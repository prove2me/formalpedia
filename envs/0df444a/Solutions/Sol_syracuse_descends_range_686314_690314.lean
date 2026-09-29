-- Prove2me | solution 1 for syracuse_descends_range_686314_690314
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:04:56.431953+00:00
-- url     : https://prove2.me/submissions/8745fdc9-728c-462d-832b-3da22bf5204f

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


theorem B2326805 : Blo 686314 2326805 := bbase (se 6 (by rfl) ⟨54534, by rfl⟩ : syracuseStep 2326805 = 109069) (by norm_num)
theorem B1769933 : Blo 686314 1769933 := bbase (se 3 (by rfl) ⟨331862, by rfl⟩ : syracuseStep 1769933 = 663725) (by norm_num)
theorem B1671637 : Blo 686314 1671637 := bbase (se 7 (by rfl) ⟨19589, by rfl⟩ : syracuseStep 1671637 = 39179) (by norm_num)
theorem B1769941 : Blo 686314 1769941 := bbase (se 7 (by rfl) ⟨20741, by rfl⟩ : syracuseStep 1769941 = 41483) (by norm_num)
theorem B3146309 : Blo 686314 3146309 := bbase (se 4 (by rfl) ⟨294966, by rfl⟩ : syracuseStep 3146309 = 589933) (by norm_num)
theorem B1737389 : Blo 686314 1737389 := bbase (se 3 (by rfl) ⟨325760, by rfl⟩ : syracuseStep 1737389 = 651521) (by norm_num)
theorem B2327237 : Blo 686314 2327237 := bbase (se 4 (by rfl) ⟨218178, by rfl⟩ : syracuseStep 2327237 = 436357) (by norm_num)
theorem B3539717 : Blo 686314 3539717 := bbase (se 4 (by rfl) ⟨331848, by rfl⟩ : syracuseStep 3539717 = 663697) (by norm_num)
theorem B1737733 : Blo 686314 1737733 := bbase (se 4 (by rfl) ⟨162912, by rfl⟩ : syracuseStep 1737733 = 325825) (by norm_num)
theorem B1180741 : Blo 686314 1180741 := bbase (se 4 (by rfl) ⟨110694, by rfl⟩ : syracuseStep 1180741 = 221389) (by norm_num)
theorem B1737845 : Blo 686314 1737845 := bbase (se 5 (by rfl) ⟨81461, by rfl⟩ : syracuseStep 1737845 = 162923) (by norm_num)
theorem B2327669 : Blo 686314 2327669 := bbase (se 5 (by rfl) ⟨109109, by rfl⟩ : syracuseStep 2327669 = 218219) (by norm_num)
theorem B1738037 : Blo 686314 1738037 := bbase (se 5 (by rfl) ⟨81470, by rfl⟩ : syracuseStep 1738037 = 162941) (by norm_num)
theorem B5866901 : Blo 686314 5866901 := bbase (se 6 (by rfl) ⟨137505, by rfl⟩ : syracuseStep 5866901 = 275011) (by norm_num)
theorem B2328101 : Blo 686314 2328101 := bbase (se 4 (by rfl) ⟨218259, by rfl⟩ : syracuseStep 2328101 = 436519) (by norm_num)
theorem B3475061 : Blo 686314 3475061 := bbase (se 5 (by rfl) ⟨162893, by rfl⟩ : syracuseStep 3475061 = 325787) (by norm_num)
theorem B1738381 : Blo 686314 1738381 := bbase (se 3 (by rfl) ⟨325946, by rfl⟩ : syracuseStep 1738381 = 651893) (by norm_num)
theorem B5310197 : Blo 686314 5310197 := bbase (se 5 (by rfl) ⟨248915, by rfl⟩ : syracuseStep 5310197 = 497831) (by norm_num)
theorem B1738493 : Blo 686314 1738493 := bbase (se 3 (by rfl) ⟨325967, by rfl⟩ : syracuseStep 1738493 = 651935) (by norm_num)
theorem B2361125 : Blo 686314 2361125 := bbase (se 4 (by rfl) ⟨221355, by rfl⟩ : syracuseStep 2361125 = 442711) (by norm_num)
theorem B1738685 : Blo 686314 1738685 := bbase (se 3 (by rfl) ⟨326003, by rfl⟩ : syracuseStep 1738685 = 652007) (by norm_num)
theorem B2328533 : Blo 686314 2328533 := bbase (se 7 (by rfl) ⟨27287, by rfl⟩ : syracuseStep 2328533 = 54575) (by norm_num)
theorem B2066485 : Blo 686314 2066485 := bbase (se 5 (by rfl) ⟨96866, by rfl⟩ : syracuseStep 2066485 = 193733) (by norm_num)
theorem B1739029 : Blo 686314 1739029 := bbase (se 6 (by rfl) ⟨40758, by rfl⟩ : syracuseStep 1739029 = 81517) (by norm_num)
theorem B1116509 : Blo 686314 1116509 := bbase (se 3 (by rfl) ⟨209345, by rfl⟩ : syracuseStep 1116509 = 418691) (by norm_num)
theorem B1673597 : Blo 686314 1673597 := bbase (se 3 (by rfl) ⟨313799, by rfl⟩ : syracuseStep 1673597 = 627599) (by norm_num)
theorem B1739141 : Blo 686314 1739141 := bbase (se 4 (by rfl) ⟨163044, by rfl⟩ : syracuseStep 1739141 = 326089) (by norm_num)
theorem B2328965 : Blo 686314 2328965 := bbase (se 4 (by rfl) ⟨218340, by rfl⟩ : syracuseStep 2328965 = 436681) (by norm_num)
theorem B1739333 : Blo 686314 1739333 := bbase (se 4 (by rfl) ⟨163062, by rfl⟩ : syracuseStep 1739333 = 326125) (by norm_num)
theorem B2329397 : Blo 686314 2329397 := bbase (se 5 (by rfl) ⟨109190, by rfl⟩ : syracuseStep 2329397 = 218381) (by norm_num)
theorem B3476357 : Blo 686314 3476357 := bbase (se 4 (by rfl) ⟨325908, by rfl⟩ : syracuseStep 3476357 = 651817) (by norm_num)
theorem B1739677 : Blo 686314 1739677 := bbase (se 3 (by rfl) ⟨326189, by rfl⟩ : syracuseStep 1739677 = 652379) (by norm_num)
theorem B1739789 : Blo 686314 1739789 := bbase (se 3 (by rfl) ⟨326210, by rfl⟩ : syracuseStep 1739789 = 652421) (by norm_num)
theorem B1739981 : Blo 686314 1739981 := bbase (se 3 (by rfl) ⟨326246, by rfl⟩ : syracuseStep 1739981 = 652493) (by norm_num)
theorem B22646101 : Blo 686314 22646101 := bbase (se 11 (by rfl) ⟨16586, by rfl⟩ : syracuseStep 22646101 = 33173) (by norm_num)
theorem B7048565 : Blo 686314 7048565 := bbase (se 5 (by rfl) ⟨330401, by rfl⟩ : syracuseStep 7048565 = 660803) (by norm_num)
theorem B1740325 : Blo 686314 1740325 := bbase (se 4 (by rfl) ⟨163155, by rfl⟩ : syracuseStep 1740325 = 326311) (by norm_num)
theorem B4722229 : Blo 686314 4722229 := bbase (se 5 (by rfl) ⟨221354, by rfl⟩ : syracuseStep 4722229 = 442709) (by norm_num)
theorem B1740437 : Blo 686314 1740437 := bbase (se 6 (by rfl) ⟨40791, by rfl⟩ : syracuseStep 1740437 = 81583) (by norm_num)
theorem B25431893 : Blo 686314 25431893 := bbase (se 9 (by rfl) ⟨74507, by rfl⟩ : syracuseStep 25431893 = 149015) (by norm_num)
theorem B1740629 : Blo 686314 1740629 := bbase (se 9 (by rfl) ⟨5099, by rfl⟩ : syracuseStep 1740629 = 10199) (by norm_num)
theorem B6688757 : Blo 686314 6688757 := bbase (se 5 (by rfl) ⟨313535, by rfl⟩ : syracuseStep 6688757 = 627071) (by norm_num)
theorem B1544237 : Blo 686314 1544237 := bbase (se 3 (by rfl) ⟨289544, by rfl⟩ : syracuseStep 1544237 = 579089) (by norm_num)
theorem B5214293 : Blo 686314 5214293 := bbase (se 8 (by rfl) ⟨30552, by rfl⟩ : syracuseStep 5214293 = 61105) (by norm_num)
theorem B1544309 : Blo 686314 1544309 := bbase (se 5 (by rfl) ⟨72389, by rfl⟩ : syracuseStep 1544309 = 144779) (by norm_num)
theorem B3477653 : Blo 686314 3477653 := bbase (se 6 (by rfl) ⟨81507, by rfl⟩ : syracuseStep 3477653 = 163015) (by norm_num)
theorem B1740973 : Blo 686314 1740973 := bbase (se 3 (by rfl) ⟨326432, by rfl⟩ : syracuseStep 1740973 = 652865) (by norm_num)
theorem B1544381 : Blo 686314 1544381 := bbase (se 3 (by rfl) ⟨289571, by rfl⟩ : syracuseStep 1544381 = 579143) (by norm_num)
theorem B1544453 : Blo 686314 1544453 := bbase (se 4 (by rfl) ⟨144792, by rfl⟩ : syracuseStep 1544453 = 289585) (by norm_num)
theorem B1741085 : Blo 686314 1741085 := bbase (se 3 (by rfl) ⟨326453, by rfl⟩ : syracuseStep 1741085 = 652907) (by norm_num)
theorem B3313973 : Blo 686314 3313973 := bbase (se 5 (by rfl) ⟨155342, by rfl⟩ : syracuseStep 3313973 = 310685) (by norm_num)
theorem B1544525 : Blo 686314 1544525 := bbase (se 3 (by rfl) ⟨289598, by rfl⟩ : syracuseStep 1544525 = 579197) (by norm_num)
theorem B1544597 : Blo 686314 1544597 := bbase (se 6 (by rfl) ⟨36201, by rfl⟩ : syracuseStep 1544597 = 72403) (by norm_num)
theorem B1544669 : Blo 686314 1544669 := bbase (se 3 (by rfl) ⟨289625, by rfl⟩ : syracuseStep 1544669 = 579251) (by norm_num)
theorem B1741277 : Blo 686314 1741277 := bbase (se 3 (by rfl) ⟨326489, by rfl⟩ : syracuseStep 1741277 = 652979) (by norm_num)
theorem B1544741 : Blo 686314 1544741 := bbase (se 4 (by rfl) ⟨144819, by rfl⟩ : syracuseStep 1544741 = 289639) (by norm_num)
theorem B1544813 : Blo 686314 1544813 := bbase (se 3 (by rfl) ⟨289652, by rfl⟩ : syracuseStep 1544813 = 579305) (by norm_num)
theorem B1544885 : Blo 686314 1544885 := bbase (se 5 (by rfl) ⟨72416, by rfl⟩ : syracuseStep 1544885 = 144833) (by norm_num)
theorem B1544957 : Blo 686314 1544957 := bbase (se 3 (by rfl) ⟨289679, by rfl⟩ : syracuseStep 1544957 = 579359) (by norm_num)
theorem B1741621 : Blo 686314 1741621 := bbase (se 5 (by rfl) ⟨81638, by rfl⟩ : syracuseStep 1741621 = 163277) (by norm_num)
theorem B2790197 : Blo 686314 2790197 := bbase (se 5 (by rfl) ⟨130790, by rfl⟩ : syracuseStep 2790197 = 261581) (by norm_num)
theorem B1545029 : Blo 686314 1545029 := bbase (se 4 (by rfl) ⟨144846, by rfl⟩ : syracuseStep 1545029 = 289693) (by norm_num)
theorem B1545101 : Blo 686314 1545101 := bbase (se 3 (by rfl) ⟨289706, by rfl⟩ : syracuseStep 1545101 = 579413) (by norm_num)
theorem B1741733 : Blo 686314 1741733 := bbase (se 4 (by rfl) ⟨163287, by rfl⟩ : syracuseStep 1741733 = 326575) (by norm_num)
theorem B1545173 : Blo 686314 1545173 := bbase (se 7 (by rfl) ⟨18107, by rfl⟩ : syracuseStep 1545173 = 36215) (by norm_num)
theorem B1545245 : Blo 686314 1545245 := bbase (se 3 (by rfl) ⟨289733, by rfl⟩ : syracuseStep 1545245 = 579467) (by norm_num)
theorem B1545317 : Blo 686314 1545317 := bbase (se 4 (by rfl) ⟨144873, by rfl⟩ : syracuseStep 1545317 = 289747) (by norm_num)
theorem B1741925 : Blo 686314 1741925 := bbase (se 4 (by rfl) ⟨163305, by rfl⟩ : syracuseStep 1741925 = 326611) (by norm_num)
theorem B1545389 : Blo 686314 1545389 := bbase (se 3 (by rfl) ⟨289760, by rfl⟩ : syracuseStep 1545389 = 579521) (by norm_num)
theorem B1545461 : Blo 686314 1545461 := bbase (se 5 (by rfl) ⟨72443, by rfl⟩ : syracuseStep 1545461 = 144887) (by norm_num)
theorem B1545533 : Blo 686314 1545533 := bbase (se 3 (by rfl) ⟨289787, by rfl⟩ : syracuseStep 1545533 = 579575) (by norm_num)
theorem B1545605 : Blo 686314 1545605 := bbase (se 4 (by rfl) ⟨144900, by rfl⟩ : syracuseStep 1545605 = 289801) (by norm_num)
theorem B3478949 : Blo 686314 3478949 := bbase (se 4 (by rfl) ⟨326151, by rfl⟩ : syracuseStep 3478949 = 652303) (by norm_num)
theorem B1742269 : Blo 686314 1742269 := bbase (se 3 (by rfl) ⟨326675, by rfl⟩ : syracuseStep 1742269 = 653351) (by norm_num)
theorem B1545677 : Blo 686314 1545677 := bbase (se 3 (by rfl) ⟨289814, by rfl⟩ : syracuseStep 1545677 = 579629) (by norm_num)
theorem B1545749 : Blo 686314 1545749 := bbase (se 6 (by rfl) ⟨36228, by rfl⟩ : syracuseStep 1545749 = 72457) (by norm_num)
theorem B1742381 : Blo 686314 1742381 := bbase (se 3 (by rfl) ⟨326696, by rfl⟩ : syracuseStep 1742381 = 653393) (by norm_num)
theorem B14161493 : Blo 686314 14161493 := bbase (se 8 (by rfl) ⟨82977, by rfl⟩ : syracuseStep 14161493 = 165955) (by norm_num)
theorem B1545821 : Blo 686314 1545821 := bbase (se 3 (by rfl) ⟨289841, by rfl⟩ : syracuseStep 1545821 = 579683) (by norm_num)
theorem B1545893 : Blo 686314 1545893 := bbase (se 4 (by rfl) ⟨144927, by rfl⟩ : syracuseStep 1545893 = 289855) (by norm_num)
theorem B1545965 : Blo 686314 1545965 := bbase (se 3 (by rfl) ⟨289868, by rfl⟩ : syracuseStep 1545965 = 579737) (by norm_num)
theorem B1742573 : Blo 686314 1742573 := bbase (se 3 (by rfl) ⟨326732, by rfl⟩ : syracuseStep 1742573 = 653465) (by norm_num)
theorem B1546037 : Blo 686314 1546037 := bbase (se 5 (by rfl) ⟨72470, by rfl⟩ : syracuseStep 1546037 = 144941) (by norm_num)
theorem B1546109 : Blo 686314 1546109 := bbase (se 3 (by rfl) ⟨289895, by rfl⟩ : syracuseStep 1546109 = 579791) (by norm_num)
theorem B1546181 : Blo 686314 1546181 := bbase (se 4 (by rfl) ⟨144954, by rfl⟩ : syracuseStep 1546181 = 289909) (by norm_num)
theorem B1546253 : Blo 686314 1546253 := bbase (se 3 (by rfl) ⟨289922, by rfl⟩ : syracuseStep 1546253 = 579845) (by norm_num)
theorem B1742917 : Blo 686314 1742917 := bbase (se 4 (by rfl) ⟨163398, by rfl⟩ : syracuseStep 1742917 = 326797) (by norm_num)
theorem B1546325 : Blo 686314 1546325 := bbase (se 8 (by rfl) ⟨9060, by rfl⟩ : syracuseStep 1546325 = 18121) (by norm_num)
theorem B825437 : Blo 686314 825437 := bbase (se 3 (by rfl) ⟨154769, by rfl⟩ : syracuseStep 825437 = 309539) (by norm_num)
theorem B2201717 : Blo 686314 2201717 := bbase (se 5 (by rfl) ⟨103205, by rfl⟩ : syracuseStep 2201717 = 206411) (by norm_num)
theorem B1546397 : Blo 686314 1546397 := bbase (se 3 (by rfl) ⟨289949, by rfl⟩ : syracuseStep 1546397 = 579899) (by norm_num)
theorem B1743029 : Blo 686314 1743029 := bbase (se 5 (by rfl) ⟨81704, by rfl⟩ : syracuseStep 1743029 = 163409) (by norm_num)
theorem B1546469 : Blo 686314 1546469 := bbase (se 4 (by rfl) ⟨144981, by rfl⟩ : syracuseStep 1546469 = 289963) (by norm_num)
theorem B1546541 : Blo 686314 1546541 := bbase (se 3 (by rfl) ⟨289976, by rfl⟩ : syracuseStep 1546541 = 579953) (by norm_num)
theorem B1546613 : Blo 686314 1546613 := bbase (se 5 (by rfl) ⟨72497, by rfl⟩ : syracuseStep 1546613 = 144995) (by norm_num)
theorem B1743221 : Blo 686314 1743221 := bbase (se 5 (by rfl) ⟨81713, by rfl⟩ : syracuseStep 1743221 = 163427) (by norm_num)
theorem B1546685 : Blo 686314 1546685 := bbase (se 3 (by rfl) ⟨290003, by rfl⟩ : syracuseStep 1546685 = 580007) (by norm_num)
theorem B1546757 : Blo 686314 1546757 := bbase (se 4 (by rfl) ⟨145008, by rfl⟩ : syracuseStep 1546757 = 290017) (by norm_num)
theorem B1546829 : Blo 686314 1546829 := bbase (se 3 (by rfl) ⟨290030, by rfl⟩ : syracuseStep 1546829 = 580061) (by norm_num)
theorem B1546901 : Blo 686314 1546901 := bbase (se 6 (by rfl) ⟨36255, by rfl⟩ : syracuseStep 1546901 = 72511) (by norm_num)
theorem B826033 : Blo 686314 826033 := bbase (se 2 (by rfl) ⟨309762, by rfl⟩ : syracuseStep 826033 = 619525) (by norm_num)
theorem B3480245 : Blo 686314 3480245 := bbase (se 5 (by rfl) ⟨163136, by rfl⟩ : syracuseStep 3480245 = 326273) (by norm_num)
theorem B1743565 : Blo 686314 1743565 := bbase (se 3 (by rfl) ⟨326918, by rfl⟩ : syracuseStep 1743565 = 653837) (by norm_num)
theorem B1546973 : Blo 686314 1546973 := bbase (se 3 (by rfl) ⟨290057, by rfl⟩ : syracuseStep 1546973 = 580115) (by norm_num)
theorem B826129 : Blo 686314 826129 := bbase (se 2 (by rfl) ⟨309798, by rfl⟩ : syracuseStep 826129 = 619597) (by norm_num)
theorem B1547045 : Blo 686314 1547045 := bbase (se 4 (by rfl) ⟨145035, by rfl⟩ : syracuseStep 1547045 = 290071) (by norm_num)
theorem B1743677 : Blo 686314 1743677 := bbase (se 3 (by rfl) ⟨326939, by rfl⟩ : syracuseStep 1743677 = 653879) (by norm_num)
theorem B1547117 : Blo 686314 1547117 := bbase (se 3 (by rfl) ⟨290084, by rfl⟩ : syracuseStep 1547117 = 580169) (by norm_num)
theorem B1547189 : Blo 686314 1547189 := bbase (se 5 (by rfl) ⟨72524, by rfl⟩ : syracuseStep 1547189 = 145049) (by norm_num)
theorem B1547261 : Blo 686314 1547261 := bbase (se 3 (by rfl) ⟨290111, by rfl⟩ : syracuseStep 1547261 = 580223) (by norm_num)
theorem B1743869 : Blo 686314 1743869 := bbase (se 3 (by rfl) ⟨326975, by rfl⟩ : syracuseStep 1743869 = 653951) (by norm_num)
theorem B1547333 : Blo 686314 1547333 := bbase (se 4 (by rfl) ⟨145062, by rfl⟩ : syracuseStep 1547333 = 290125) (by norm_num)
theorem B1547405 : Blo 686314 1547405 := bbase (se 3 (by rfl) ⟨290138, by rfl⟩ : syracuseStep 1547405 = 580277) (by norm_num)
theorem B2202805 : Blo 686314 2202805 := bbase (se 5 (by rfl) ⟨103256, by rfl⟩ : syracuseStep 2202805 = 206513) (by norm_num)
theorem B1547477 : Blo 686314 1547477 := bbase (se 7 (by rfl) ⟨18134, by rfl⟩ : syracuseStep 1547477 = 36269) (by norm_num)
theorem B1547549 : Blo 686314 1547549 := bbase (se 3 (by rfl) ⟨290165, by rfl⟩ : syracuseStep 1547549 = 580331) (by norm_num)
theorem B38083925 : Blo 686314 38083925 := bbase (se 11 (by rfl) ⟨27893, by rfl⟩ : syracuseStep 38083925 = 55787) (by norm_num)
theorem B1744213 : Blo 686314 1744213 := bbase (se 11 (by rfl) ⟨1277, by rfl⟩ : syracuseStep 1744213 = 2555) (by norm_num)
theorem B1547621 : Blo 686314 1547621 := bbase (se 4 (by rfl) ⟨145089, by rfl⟩ : syracuseStep 1547621 = 290179) (by norm_num)
theorem B3317125 : Blo 686314 3317125 := bbase (se 4 (by rfl) ⟨310980, by rfl⟩ : syracuseStep 3317125 = 621961) (by norm_num)
theorem B1547693 : Blo 686314 1547693 := bbase (se 3 (by rfl) ⟨290192, by rfl⟩ : syracuseStep 1547693 = 580385) (by norm_num)
theorem B1744325 : Blo 686314 1744325 := bbase (se 4 (by rfl) ⟨163530, by rfl⟩ : syracuseStep 1744325 = 327061) (by norm_num)
theorem B1547765 : Blo 686314 1547765 := bbase (se 5 (by rfl) ⟨72551, by rfl⟩ : syracuseStep 1547765 = 145103) (by norm_num)
theorem B1547837 : Blo 686314 1547837 := bbase (se 3 (by rfl) ⟨290219, by rfl⟩ : syracuseStep 1547837 = 580439) (by norm_num)
theorem B1547909 : Blo 686314 1547909 := bbase (se 4 (by rfl) ⟨145116, by rfl⟩ : syracuseStep 1547909 = 290233) (by norm_num)
theorem B1744517 : Blo 686314 1744517 := bbase (se 4 (by rfl) ⟨163548, by rfl⟩ : syracuseStep 1744517 = 327097) (by norm_num)
theorem B1547981 : Blo 686314 1547981 := bbase (se 3 (by rfl) ⟨290246, by rfl⟩ : syracuseStep 1547981 = 580493) (by norm_num)
theorem B1548053 : Blo 686314 1548053 := bbase (se 6 (by rfl) ⟨36282, by rfl⟩ : syracuseStep 1548053 = 72565) (by norm_num)
theorem B1548125 : Blo 686314 1548125 := bbase (se 3 (by rfl) ⟨290273, by rfl⟩ : syracuseStep 1548125 = 580547) (by norm_num)
theorem B827273 : Blo 686314 827273 := bbase (se 2 (by rfl) ⟨310227, by rfl⟩ : syracuseStep 827273 = 620455) (by norm_num)
theorem B1548197 : Blo 686314 1548197 := bbase (se 4 (by rfl) ⟨145143, by rfl⟩ : syracuseStep 1548197 = 290287) (by norm_num)
theorem B3481541 : Blo 686314 3481541 := bbase (se 4 (by rfl) ⟨326394, by rfl⟩ : syracuseStep 3481541 = 652789) (by norm_num)
theorem B1744861 : Blo 686314 1744861 := bbase (se 3 (by rfl) ⟨327161, by rfl⟩ : syracuseStep 1744861 = 654323) (by norm_num)
theorem B1548269 : Blo 686314 1548269 := bbase (se 3 (by rfl) ⟨290300, by rfl⟩ : syracuseStep 1548269 = 580601) (by norm_num)
theorem B696325 : Blo 686314 696325 := bbase (se 4 (by rfl) ⟨65280, by rfl⟩ : syracuseStep 696325 = 130561) (by norm_num)
theorem B696349 : Blo 686314 696349 := bbase (se 3 (by rfl) ⟨130565, by rfl⟩ : syracuseStep 696349 = 261131) (by norm_num)
theorem B1548341 : Blo 686314 1548341 := bbase (se 5 (by rfl) ⟨72578, by rfl⟩ : syracuseStep 1548341 = 145157) (by norm_num)
theorem B1744973 : Blo 686314 1744973 := bbase (se 3 (by rfl) ⟨327182, by rfl⟩ : syracuseStep 1744973 = 654365) (by norm_num)
theorem B1548413 : Blo 686314 1548413 := bbase (se 3 (by rfl) ⟨290327, by rfl⟩ : syracuseStep 1548413 = 580655) (by norm_num)
theorem B9412757 : Blo 686314 9412757 := bbase (se 6 (by rfl) ⟨220611, by rfl⟩ : syracuseStep 9412757 = 441223) (by norm_num)
theorem B1548485 : Blo 686314 1548485 := bbase (se 4 (by rfl) ⟨145170, by rfl⟩ : syracuseStep 1548485 = 290341) (by norm_num)
theorem B827605 : Blo 686314 827605 := bbase (se 7 (by rfl) ⟨9698, by rfl⟩ : syracuseStep 827605 = 19397) (by norm_num)
theorem B1548557 : Blo 686314 1548557 := bbase (se 3 (by rfl) ⟨290354, by rfl⟩ : syracuseStep 1548557 = 580709) (by norm_num)
theorem B1745165 : Blo 686314 1745165 := bbase (se 3 (by rfl) ⟨327218, by rfl⟩ : syracuseStep 1745165 = 654437) (by norm_num)
theorem B2203973 : Blo 686314 2203973 := bbase (se 4 (by rfl) ⟨206622, by rfl⟩ : syracuseStep 2203973 = 413245) (by norm_num)
theorem B1548629 : Blo 686314 1548629 := bbase (se 10 (by rfl) ⟨2268, by rfl⟩ : syracuseStep 1548629 = 4537) (by norm_num)
theorem B1548701 : Blo 686314 1548701 := bbase (se 3 (by rfl) ⟨290381, by rfl⟩ : syracuseStep 1548701 = 580763) (by norm_num)
theorem B1548773 : Blo 686314 1548773 := bbase (se 4 (by rfl) ⟨145197, by rfl⟩ : syracuseStep 1548773 = 290395) (by norm_num)
theorem B1548845 : Blo 686314 1548845 := bbase (se 3 (by rfl) ⟨290408, by rfl⟩ : syracuseStep 1548845 = 580817) (by norm_num)
theorem B1745509 : Blo 686314 1745509 := bbase (se 4 (by rfl) ⟨163641, by rfl⟩ : syracuseStep 1745509 = 327283) (by norm_num)
theorem B1548917 : Blo 686314 1548917 := bbase (se 5 (by rfl) ⟨72605, by rfl⟩ : syracuseStep 1548917 = 145211) (by norm_num)
theorem B1548989 : Blo 686314 1548989 := bbase (se 3 (by rfl) ⟨290435, by rfl⟩ : syracuseStep 1548989 = 580871) (by norm_num)
theorem B1745621 : Blo 686314 1745621 := bbase (se 7 (by rfl) ⟨20456, by rfl⟩ : syracuseStep 1745621 = 40913) (by norm_num)
theorem B1549061 : Blo 686314 1549061 := bbase (se 4 (by rfl) ⟨145224, by rfl⟩ : syracuseStep 1549061 = 290449) (by norm_num)
theorem B1549133 : Blo 686314 1549133 := bbase (se 3 (by rfl) ⟨290462, by rfl⟩ : syracuseStep 1549133 = 580925) (by norm_num)
theorem B828301 : Blo 686314 828301 := bbase (se 3 (by rfl) ⟨155306, by rfl⟩ : syracuseStep 828301 = 310613) (by norm_num)
theorem B1549205 : Blo 686314 1549205 := bbase (se 6 (by rfl) ⟨36309, by rfl⟩ : syracuseStep 1549205 = 72619) (by norm_num)
theorem B1745813 : Blo 686314 1745813 := bbase (se 6 (by rfl) ⟨40917, by rfl⟩ : syracuseStep 1745813 = 81835) (by norm_num)
theorem B828349 : Blo 686314 828349 := bbase (se 3 (by rfl) ⟨155315, by rfl⟩ : syracuseStep 828349 = 310631) (by norm_num)
theorem B1549277 : Blo 686314 1549277 := bbase (se 3 (by rfl) ⟨290489, by rfl⟩ : syracuseStep 1549277 = 580979) (by norm_num)
theorem B1680365 : Blo 686314 1680365 := bbase (se 3 (by rfl) ⟨315068, by rfl⟩ : syracuseStep 1680365 = 630137) (by norm_num)
theorem B1549349 : Blo 686314 1549349 := bbase (se 4 (by rfl) ⟨145251, by rfl⟩ : syracuseStep 1549349 = 290503) (by norm_num)
theorem B1549421 : Blo 686314 1549421 := bbase (se 3 (by rfl) ⟨290516, by rfl⟩ : syracuseStep 1549421 = 581033) (by norm_num)
theorem B992405 : Blo 686314 992405 := bbase (se 6 (by rfl) ⟨23259, by rfl⟩ : syracuseStep 992405 = 46519) (by norm_num)
theorem B697501 : Blo 686314 697501 := bbase (se 3 (by rfl) ⟨130781, by rfl⟩ : syracuseStep 697501 = 261563) (by norm_num)
theorem B1549493 : Blo 686314 1549493 := bbase (se 5 (by rfl) ⟨72632, by rfl⟩ : syracuseStep 1549493 = 145265) (by norm_num)
theorem B3482837 : Blo 686314 3482837 := bbase (se 7 (by rfl) ⟨40814, by rfl⟩ : syracuseStep 3482837 = 81629) (by norm_num)
theorem B1746157 : Blo 686314 1746157 := bbase (se 3 (by rfl) ⟨327404, by rfl⟩ : syracuseStep 1746157 = 654809) (by norm_num)
theorem B1549565 : Blo 686314 1549565 := bbase (se 3 (by rfl) ⟨290543, by rfl⟩ : syracuseStep 1549565 = 581087) (by norm_num)
theorem B1549637 : Blo 686314 1549637 := bbase (se 4 (by rfl) ⟨145278, by rfl⟩ : syracuseStep 1549637 = 290557) (by norm_num)
theorem B1746269 : Blo 686314 1746269 := bbase (se 3 (by rfl) ⟨327425, by rfl⟩ : syracuseStep 1746269 = 654851) (by norm_num)
theorem B1549709 : Blo 686314 1549709 := bbase (se 3 (by rfl) ⟨290570, by rfl⟩ : syracuseStep 1549709 = 581141) (by norm_num)
theorem B1549781 : Blo 686314 1549781 := bbase (se 7 (by rfl) ⟨18161, by rfl⟩ : syracuseStep 1549781 = 36323) (by norm_num)
theorem B1549853 : Blo 686314 1549853 := bbase (se 3 (by rfl) ⟨290597, by rfl⟩ : syracuseStep 1549853 = 581195) (by norm_num)
theorem B1746461 : Blo 686314 1746461 := bbase (se 3 (by rfl) ⟨327461, by rfl⟩ : syracuseStep 1746461 = 654923) (by norm_num)
theorem B1549925 : Blo 686314 1549925 := bbase (se 4 (by rfl) ⟨145305, by rfl⟩ : syracuseStep 1549925 = 290611) (by norm_num)
theorem B1549997 : Blo 686314 1549997 := bbase (se 3 (by rfl) ⟨290624, by rfl⟩ : syracuseStep 1549997 = 581249) (by norm_num)
theorem B1550069 : Blo 686314 1550069 := bbase (se 5 (by rfl) ⟨72659, by rfl⟩ : syracuseStep 1550069 = 145319) (by norm_num)
theorem B1550141 : Blo 686314 1550141 := bbase (se 3 (by rfl) ⟨290651, by rfl⟩ : syracuseStep 1550141 = 581303) (by norm_num)
theorem B1746805 : Blo 686314 1746805 := bbase (se 5 (by rfl) ⟨81881, by rfl⟩ : syracuseStep 1746805 = 163763) (by norm_num)
theorem B1550213 : Blo 686314 1550213 := bbase (se 4 (by rfl) ⟨145332, by rfl⟩ : syracuseStep 1550213 = 290665) (by norm_num)
theorem B1550285 : Blo 686314 1550285 := bbase (se 3 (by rfl) ⟨290678, by rfl⟩ : syracuseStep 1550285 = 581357) (by norm_num)
theorem B1746917 : Blo 686314 1746917 := bbase (se 4 (by rfl) ⟨163773, by rfl⟩ : syracuseStep 1746917 = 327547) (by norm_num)
theorem B1550357 : Blo 686314 1550357 := bbase (se 6 (by rfl) ⟨36336, by rfl⟩ : syracuseStep 1550357 = 72673) (by norm_num)
theorem B1550429 : Blo 686314 1550429 := bbase (se 3 (by rfl) ⟨290705, by rfl⟩ : syracuseStep 1550429 = 581411) (by norm_num)
theorem B2205829 : Blo 686314 2205829 := bbase (se 4 (by rfl) ⟨206796, by rfl⟩ : syracuseStep 2205829 = 413593) (by norm_num)
theorem B1550501 : Blo 686314 1550501 := bbase (se 4 (by rfl) ⟨145359, by rfl⟩ : syracuseStep 1550501 = 290719) (by norm_num)
theorem B1747109 : Blo 686314 1747109 := bbase (se 4 (by rfl) ⟨163791, by rfl⟩ : syracuseStep 1747109 = 327583) (by norm_num)
theorem B1550573 : Blo 686314 1550573 := bbase (se 3 (by rfl) ⟨290732, by rfl⟩ : syracuseStep 1550573 = 581465) (by norm_num)
theorem B1550645 : Blo 686314 1550645 := bbase (se 5 (by rfl) ⟨72686, by rfl⟩ : syracuseStep 1550645 = 145373) (by norm_num)
theorem B1091917 : Blo 686314 1091917 := bbase (se 3 (by rfl) ⟨204734, by rfl⟩ : syracuseStep 1091917 = 409469) (by norm_num)
theorem B698717 : Blo 686314 698717 := bbase (se 3 (by rfl) ⟨131009, by rfl⟩ : syracuseStep 698717 = 262019) (by norm_num)
theorem B1550717 : Blo 686314 1550717 := bbase (se 3 (by rfl) ⟨290759, by rfl⟩ : syracuseStep 1550717 = 581519) (by norm_num)
theorem B1550789 : Blo 686314 1550789 := bbase (se 4 (by rfl) ⟨145386, by rfl⟩ : syracuseStep 1550789 = 290773) (by norm_num)
theorem B3484133 : Blo 686314 3484133 := bbase (se 4 (by rfl) ⟨326637, by rfl⟩ : syracuseStep 3484133 = 653275) (by norm_num)
theorem B1550861 : Blo 686314 1550861 := bbase (se 3 (by rfl) ⟨290786, by rfl⟩ : syracuseStep 1550861 = 581573) (by norm_num)
theorem B797245 : Blo 686314 797245 := bbase (se 3 (by rfl) ⟨149483, by rfl⟩ : syracuseStep 797245 = 298967) (by norm_num)
theorem B1550933 : Blo 686314 1550933 := bbase (se 8 (by rfl) ⟨9087, by rfl⟩ : syracuseStep 1550933 = 18175) (by norm_num)
theorem B1551005 : Blo 686314 1551005 := bbase (se 3 (by rfl) ⟨290813, by rfl⟩ : syracuseStep 1551005 = 581627) (by norm_num)
theorem B1649317 : Blo 686314 1649317 := bbase (se 4 (by rfl) ⟨154623, by rfl⟩ : syracuseStep 1649317 = 309247) (by norm_num)
theorem B1551077 : Blo 686314 1551077 := bbase (se 4 (by rfl) ⟨145413, by rfl⟩ : syracuseStep 1551077 = 290827) (by norm_num)
theorem B7842581 : Blo 686314 7842581 := bbase (se 6 (by rfl) ⟨183810, by rfl⟩ : syracuseStep 7842581 = 367621) (by norm_num)
theorem B1551149 : Blo 686314 1551149 := bbase (se 3 (by rfl) ⟨290840, by rfl⟩ : syracuseStep 1551149 = 581681) (by norm_num)
theorem B3910517 : Blo 686314 3910517 := bbase (se 5 (by rfl) ⟨183305, by rfl⟩ : syracuseStep 3910517 = 366611) (by norm_num)
theorem B1551221 : Blo 686314 1551221 := bbase (se 5 (by rfl) ⟨72713, by rfl⟩ : syracuseStep 1551221 = 145427) (by norm_num)
theorem B6269845 : Blo 686314 6269845 := bbase (se 6 (by rfl) ⟨146949, by rfl⟩ : syracuseStep 6269845 = 293899) (by norm_num)
theorem B1551293 : Blo 686314 1551293 := bbase (se 3 (by rfl) ⟨290867, by rfl⟩ : syracuseStep 1551293 = 581735) (by norm_num)
theorem B1551365 : Blo 686314 1551365 := bbase (se 4 (by rfl) ⟨145440, by rfl⟩ : syracuseStep 1551365 = 290881) (by norm_num)
theorem B1158205 : Blo 686314 1158205 := bbase (se 3 (by rfl) ⟨217163, by rfl⟩ : syracuseStep 1158205 = 434327) (by norm_num)
theorem B1551437 : Blo 686314 1551437 := bbase (se 3 (by rfl) ⟨290894, by rfl⟩ : syracuseStep 1551437 = 581789) (by norm_num)
theorem B1158293 : Blo 686314 1158293 := bbase (se 6 (by rfl) ⟨27147, by rfl⟩ : syracuseStep 1158293 = 54295) (by norm_num)
theorem B1551509 : Blo 686314 1551509 := bbase (se 6 (by rfl) ⟨36363, by rfl⟩ : syracuseStep 1551509 = 72727) (by norm_num)
theorem B1551581 : Blo 686314 1551581 := bbase (se 3 (by rfl) ⟨290921, by rfl⟩ : syracuseStep 1551581 = 581843) (by norm_num)
theorem B1322221 : Blo 686314 1322221 := bbase (se 3 (by rfl) ⟨247916, by rfl⟩ : syracuseStep 1322221 = 495833) (by norm_num)
theorem B1649933 : Blo 686314 1649933 := bbase (se 3 (by rfl) ⟨309362, by rfl⟩ : syracuseStep 1649933 = 618725) (by norm_num)
theorem B1158421 : Blo 686314 1158421 := bbase (se 6 (by rfl) ⟨27150, by rfl⟩ : syracuseStep 1158421 = 54301) (by norm_num)
theorem B1551653 : Blo 686314 1551653 := bbase (se 4 (by rfl) ⟨145467, by rfl⟩ : syracuseStep 1551653 = 290935) (by norm_num)
theorem B1649989 : Blo 686314 1649989 := bbase (se 4 (by rfl) ⟨154686, by rfl⟩ : syracuseStep 1649989 = 309373) (by norm_num)
theorem B929125 : Blo 686314 929125 := bbase (se 4 (by rfl) ⟨87105, by rfl⟩ : syracuseStep 929125 = 174211) (by norm_num)
theorem B1158509 : Blo 686314 1158509 := bbase (se 3 (by rfl) ⟨217220, by rfl⟩ : syracuseStep 1158509 = 434441) (by norm_num)
theorem B1551725 : Blo 686314 1551725 := bbase (se 3 (by rfl) ⟨290948, by rfl⟩ : syracuseStep 1551725 = 581897) (by norm_num)
theorem B4402613 : Blo 686314 4402613 := bbase (se 5 (by rfl) ⟨206372, by rfl⟩ : syracuseStep 4402613 = 412745) (by norm_num)
theorem B1551797 : Blo 686314 1551797 := bbase (se 5 (by rfl) ⟨72740, by rfl⟩ : syracuseStep 1551797 = 145481) (by norm_num)
theorem B2207189 : Blo 686314 2207189 := bbase (se 7 (by rfl) ⟨25865, by rfl⟩ : syracuseStep 2207189 = 51731) (by norm_num)
theorem B1158637 : Blo 686314 1158637 := bbase (se 3 (by rfl) ⟨217244, by rfl⟩ : syracuseStep 1158637 = 434489) (by norm_num)
theorem B1551869 : Blo 686314 1551869 := bbase (se 3 (by rfl) ⟨290975, by rfl⟩ : syracuseStep 1551869 = 581951) (by norm_num)
theorem B4697621 : Blo 686314 4697621 := bbase (se 6 (by rfl) ⟨110100, by rfl⟩ : syracuseStep 4697621 = 220201) (by norm_num)
theorem B1158725 : Blo 686314 1158725 := bbase (se 4 (by rfl) ⟨108630, by rfl⟩ : syracuseStep 1158725 = 217261) (by norm_num)
theorem B1551941 : Blo 686314 1551941 := bbase (se 4 (by rfl) ⟨145494, by rfl⟩ : syracuseStep 1551941 = 290989) (by norm_num)
theorem B1552013 : Blo 686314 1552013 := bbase (se 3 (by rfl) ⟨291002, by rfl⟩ : syracuseStep 1552013 = 582005) (by norm_num)
theorem B5222069 : Blo 686314 5222069 := bbase (se 5 (by rfl) ⟨244784, by rfl⟩ : syracuseStep 5222069 = 489569) (by norm_num)
theorem B1158853 : Blo 686314 1158853 := bbase (se 4 (by rfl) ⟨108642, by rfl⟩ : syracuseStep 1158853 = 217285) (by norm_num)
theorem B1552085 : Blo 686314 1552085 := bbase (se 7 (by rfl) ⟨18188, by rfl⟩ : syracuseStep 1552085 = 36377) (by norm_num)
theorem B3485429 : Blo 686314 3485429 := bbase (se 5 (by rfl) ⟨163379, by rfl⟩ : syracuseStep 3485429 = 326759) (by norm_num)
theorem B1191677 : Blo 686314 1191677 := bbase (se 3 (by rfl) ⟨223439, by rfl⟩ : syracuseStep 1191677 = 446879) (by norm_num)
theorem B6598421 : Blo 686314 6598421 := bbase (se 6 (by rfl) ⟨154650, by rfl⟩ : syracuseStep 6598421 = 309301) (by norm_num)
theorem B1158941 : Blo 686314 1158941 := bbase (se 3 (by rfl) ⟨217301, by rfl⟩ : syracuseStep 1158941 = 434603) (by norm_num)
theorem B1552157 : Blo 686314 1552157 := bbase (se 3 (by rfl) ⟨291029, by rfl⟩ : syracuseStep 1552157 = 582059) (by norm_num)
theorem B1552229 : Blo 686314 1552229 := bbase (se 4 (by rfl) ⟨145521, by rfl⟩ : syracuseStep 1552229 = 291043) (by norm_num)
theorem B1159069 : Blo 686314 1159069 := bbase (se 3 (by rfl) ⟨217325, by rfl⟩ : syracuseStep 1159069 = 434651) (by norm_num)
theorem B1552301 : Blo 686314 1552301 := bbase (se 3 (by rfl) ⟨291056, by rfl⟩ : syracuseStep 1552301 = 582113) (by norm_num)
theorem B733141 : Blo 686314 733141 := bbase (se 7 (by rfl) ⟨8591, by rfl⟩ : syracuseStep 733141 = 17183) (by norm_num)
theorem B1159157 : Blo 686314 1159157 := bbase (se 5 (by rfl) ⟨54335, by rfl⟩ : syracuseStep 1159157 = 108671) (by norm_num)
theorem B1552373 : Blo 686314 1552373 := bbase (se 5 (by rfl) ⟨72767, by rfl⟩ : syracuseStep 1552373 = 145535) (by norm_num)
theorem B1552445 : Blo 686314 1552445 := bbase (se 3 (by rfl) ⟨291083, by rfl⟩ : syracuseStep 1552445 = 582167) (by norm_num)
theorem B929893 : Blo 686314 929893 := bbase (se 4 (by rfl) ⟨87177, by rfl⟩ : syracuseStep 929893 = 174355) (by norm_num)
theorem B1159285 : Blo 686314 1159285 := bbase (se 5 (by rfl) ⟨54341, by rfl⟩ : syracuseStep 1159285 = 108683) (by norm_num)
theorem B1552517 : Blo 686314 1552517 := bbase (se 4 (by rfl) ⟨145548, by rfl⟩ : syracuseStep 1552517 = 291097) (by norm_num)
theorem B1159373 : Blo 686314 1159373 := bbase (se 3 (by rfl) ⟨217382, by rfl⟩ : syracuseStep 1159373 = 434765) (by norm_num)
theorem B1552589 : Blo 686314 1552589 := bbase (se 3 (by rfl) ⟨291110, by rfl⟩ : syracuseStep 1552589 = 582221) (by norm_num)
theorem B1552661 : Blo 686314 1552661 := bbase (se 6 (by rfl) ⟨36390, by rfl⟩ : syracuseStep 1552661 = 72781) (by norm_num)
theorem B1650989 : Blo 686314 1650989 := bbase (se 3 (by rfl) ⟨309560, by rfl⟩ : syracuseStep 1650989 = 619121) (by norm_num)
theorem B1159501 : Blo 686314 1159501 := bbase (se 3 (by rfl) ⟨217406, by rfl⟩ : syracuseStep 1159501 = 434813) (by norm_num)
theorem B1552733 : Blo 686314 1552733 := bbase (se 3 (by rfl) ⟨291137, by rfl⟩ : syracuseStep 1552733 = 582275) (by norm_num)
theorem B733585 : Blo 686314 733585 := bbase (se 2 (by rfl) ⟨275094, by rfl⟩ : syracuseStep 733585 = 550189) (by norm_num)
theorem B1159589 : Blo 686314 1159589 := bbase (se 4 (by rfl) ⟨108711, by rfl⟩ : syracuseStep 1159589 = 217423) (by norm_num)
theorem B1552805 : Blo 686314 1552805 := bbase (se 4 (by rfl) ⟨145575, by rfl⟩ : syracuseStep 1552805 = 291151) (by norm_num)
theorem B733645 : Blo 686314 733645 := bbase (se 3 (by rfl) ⟨137558, by rfl⟩ : syracuseStep 733645 = 275117) (by norm_num)
theorem B1552877 : Blo 686314 1552877 := bbase (se 3 (by rfl) ⟨291164, by rfl⟩ : syracuseStep 1552877 = 582329) (by norm_num)
theorem B1159717 : Blo 686314 1159717 := bbase (se 4 (by rfl) ⟨108723, by rfl⟩ : syracuseStep 1159717 = 217447) (by norm_num)
theorem B1552949 : Blo 686314 1552949 := bbase (se 5 (by rfl) ⟨72794, by rfl⟩ : syracuseStep 1552949 = 145589) (by norm_num)
theorem B995917 : Blo 686314 995917 := bbase (se 3 (by rfl) ⟨186734, by rfl⟩ : syracuseStep 995917 = 373469) (by norm_num)
theorem B1159805 : Blo 686314 1159805 := bbase (se 3 (by rfl) ⟨217463, by rfl⟩ : syracuseStep 1159805 = 434927) (by norm_num)
theorem B1553021 : Blo 686314 1553021 := bbase (se 3 (by rfl) ⟨291191, by rfl⟩ : syracuseStep 1553021 = 582383) (by norm_num)
theorem B1553093 : Blo 686314 1553093 := bbase (se 4 (by rfl) ⟨145602, by rfl⟩ : syracuseStep 1553093 = 291205) (by norm_num)
theorem B1159933 : Blo 686314 1159933 := bbase (se 3 (by rfl) ⟨217487, by rfl⟩ : syracuseStep 1159933 = 434975) (by norm_num)
theorem B733961 : Blo 686314 733961 := bbase (se 2 (by rfl) ⟨275235, by rfl⟩ : syracuseStep 733961 = 550471) (by norm_num)
theorem B1553165 : Blo 686314 1553165 := bbase (se 3 (by rfl) ⟨291218, by rfl⟩ : syracuseStep 1553165 = 582437) (by norm_num)
theorem B1160021 : Blo 686314 1160021 := bbase (se 9 (by rfl) ⟨3398, by rfl⟩ : syracuseStep 1160021 = 6797) (by norm_num)
theorem B1258325 : Blo 686314 1258325 := bbase (se 9 (by rfl) ⟨3686, by rfl⟩ : syracuseStep 1258325 = 7373) (by norm_num)
theorem B1160149 : Blo 686314 1160149 := bbase (se 7 (by rfl) ⟨13595, by rfl⟩ : syracuseStep 1160149 = 27191) (by norm_num)
theorem B3486725 : Blo 686314 3486725 := bbase (se 4 (by rfl) ⟨326880, by rfl⟩ : syracuseStep 3486725 = 653761) (by norm_num)
theorem B3912725 : Blo 686314 3912725 := bbase (se 6 (by rfl) ⟨91704, by rfl⟩ : syracuseStep 3912725 = 183409) (by norm_num)
theorem B1160237 : Blo 686314 1160237 := bbase (se 3 (by rfl) ⟨217544, by rfl⟩ : syracuseStep 1160237 = 435089) (by norm_num)
theorem B1160365 : Blo 686314 1160365 := bbase (se 3 (by rfl) ⟨217568, by rfl⟩ : syracuseStep 1160365 = 435137) (by norm_num)
theorem B734405 : Blo 686314 734405 := bbase (se 4 (by rfl) ⟨68850, by rfl⟩ : syracuseStep 734405 = 137701) (by norm_num)
theorem B734465 : Blo 686314 734465 := bbase (se 2 (by rfl) ⟨275424, by rfl⟩ : syracuseStep 734465 = 550849) (by norm_num)
theorem B1160453 : Blo 686314 1160453 := bbase (se 4 (by rfl) ⟨108792, by rfl⟩ : syracuseStep 1160453 = 217585) (by norm_num)
theorem B1029485 : Blo 686314 1029485 := bbase (se 3 (by rfl) ⟨193028, by rfl⟩ : syracuseStep 1029485 = 386057) (by norm_num)
theorem B734593 : Blo 686314 734593 := bbase (se 2 (by rfl) ⟨275472, by rfl⟩ : syracuseStep 734593 = 550945) (by norm_num)
theorem B1029509 : Blo 686314 1029509 := bbase (se 4 (by rfl) ⟨96516, by rfl⟩ : syracuseStep 1029509 = 193033) (by norm_num)
theorem B1160581 : Blo 686314 1160581 := bbase (se 4 (by rfl) ⟨108804, by rfl⟩ : syracuseStep 1160581 = 217609) (by norm_num)
theorem B1029533 : Blo 686314 1029533 := bbase (se 3 (by rfl) ⟨193037, by rfl⟩ : syracuseStep 1029533 = 386075) (by norm_num)
theorem B1029557 : Blo 686314 1029557 := bbase (se 5 (by rfl) ⟨48260, by rfl⟩ : syracuseStep 1029557 = 96521) (by norm_num)
theorem B1029581 : Blo 686314 1029581 := bbase (se 3 (by rfl) ⟨193046, by rfl⟩ : syracuseStep 1029581 = 386093) (by norm_num)
theorem B931277 : Blo 686314 931277 := bbase (se 3 (by rfl) ⟨174614, by rfl⟩ : syracuseStep 931277 = 349229) (by norm_num)
theorem B1160669 : Blo 686314 1160669 := bbase (se 3 (by rfl) ⟨217625, by rfl⟩ : syracuseStep 1160669 = 435251) (by norm_num)
theorem B1029605 : Blo 686314 1029605 := bbase (se 4 (by rfl) ⟨96525, by rfl⟩ : syracuseStep 1029605 = 193051) (by norm_num)
theorem B1029629 : Blo 686314 1029629 := bbase (se 3 (by rfl) ⟨193055, by rfl⟩ : syracuseStep 1029629 = 386111) (by norm_num)
theorem B1029653 : Blo 686314 1029653 := bbase (se 6 (by rfl) ⟨24132, by rfl⟩ : syracuseStep 1029653 = 48265) (by norm_num)
theorem B1029677 : Blo 686314 1029677 := bbase (se 3 (by rfl) ⟨193064, by rfl⟩ : syracuseStep 1029677 = 386129) (by norm_num)
theorem B1029701 : Blo 686314 1029701 := bbase (se 4 (by rfl) ⟨96534, by rfl⟩ : syracuseStep 1029701 = 193069) (by norm_num)
theorem B1029725 : Blo 686314 1029725 := bbase (se 3 (by rfl) ⟨193073, by rfl⟩ : syracuseStep 1029725 = 386147) (by norm_num)
theorem B1160797 : Blo 686314 1160797 := bbase (se 3 (by rfl) ⟨217649, by rfl⟩ : syracuseStep 1160797 = 435299) (by norm_num)
theorem B1029749 : Blo 686314 1029749 := bbase (se 5 (by rfl) ⟨48269, by rfl⟩ : syracuseStep 1029749 = 96539) (by norm_num)
theorem B1029773 : Blo 686314 1029773 := bbase (se 3 (by rfl) ⟨193082, by rfl⟩ : syracuseStep 1029773 = 386165) (by norm_num)
theorem B1029797 : Blo 686314 1029797 := bbase (se 4 (by rfl) ⟨96543, by rfl⟩ : syracuseStep 1029797 = 193087) (by norm_num)
theorem B1160885 : Blo 686314 1160885 := bbase (se 5 (by rfl) ⟨54416, by rfl⟩ : syracuseStep 1160885 = 108833) (by norm_num)
theorem B1029821 : Blo 686314 1029821 := bbase (se 3 (by rfl) ⟨193091, by rfl⟩ : syracuseStep 1029821 = 386183) (by norm_num)
theorem B1029845 : Blo 686314 1029845 := bbase (se 7 (by rfl) ⟨12068, by rfl⟩ : syracuseStep 1029845 = 24137) (by norm_num)
theorem B1029869 : Blo 686314 1029869 := bbase (se 3 (by rfl) ⟨193100, by rfl⟩ : syracuseStep 1029869 = 386201) (by norm_num)
theorem B1029893 : Blo 686314 1029893 := bbase (se 4 (by rfl) ⟨96552, by rfl⟩ : syracuseStep 1029893 = 193105) (by norm_num)
theorem B1029917 : Blo 686314 1029917 := bbase (se 3 (by rfl) ⟨193109, by rfl⟩ : syracuseStep 1029917 = 386219) (by norm_num)
theorem B1029941 : Blo 686314 1029941 := bbase (se 5 (by rfl) ⟨48278, by rfl⟩ : syracuseStep 1029941 = 96557) (by norm_num)
theorem B1161013 : Blo 686314 1161013 := bbase (se 5 (by rfl) ⟨54422, by rfl⟩ : syracuseStep 1161013 = 108845) (by norm_num)
theorem B735037 : Blo 686314 735037 := bbase (se 3 (by rfl) ⟨137819, by rfl⟩ : syracuseStep 735037 = 275639) (by norm_num)
theorem B1029965 : Blo 686314 1029965 := bbase (se 3 (by rfl) ⟨193118, by rfl⟩ : syracuseStep 1029965 = 386237) (by norm_num)
theorem B1029989 : Blo 686314 1029989 := bbase (se 4 (by rfl) ⟨96561, by rfl⟩ : syracuseStep 1029989 = 193123) (by norm_num)
theorem B1030013 : Blo 686314 1030013 := bbase (se 3 (by rfl) ⟨193127, by rfl⟩ : syracuseStep 1030013 = 386255) (by norm_num)
theorem B1161101 : Blo 686314 1161101 := bbase (se 3 (by rfl) ⟨217706, by rfl⟩ : syracuseStep 1161101 = 435413) (by norm_num)
theorem B1030037 : Blo 686314 1030037 := bbase (se 6 (by rfl) ⟨24141, by rfl⟩ : syracuseStep 1030037 = 48283) (by norm_num)
theorem B1030061 : Blo 686314 1030061 := bbase (se 3 (by rfl) ⟨193136, by rfl⟩ : syracuseStep 1030061 = 386273) (by norm_num)
theorem B735157 : Blo 686314 735157 := bbase (se 5 (by rfl) ⟨34460, by rfl⟩ : syracuseStep 735157 = 68921) (by norm_num)
theorem B1030085 : Blo 686314 1030085 := bbase (se 4 (by rfl) ⟨96570, by rfl⟩ : syracuseStep 1030085 = 193141) (by norm_num)
theorem B1030109 : Blo 686314 1030109 := bbase (se 3 (by rfl) ⟨193145, by rfl⟩ : syracuseStep 1030109 = 386291) (by norm_num)
theorem B1030133 : Blo 686314 1030133 := bbase (se 5 (by rfl) ⟨48287, by rfl⟩ : syracuseStep 1030133 = 96575) (by norm_num)
theorem B1030157 : Blo 686314 1030157 := bbase (se 3 (by rfl) ⟨193154, by rfl⟩ : syracuseStep 1030157 = 386309) (by norm_num)
theorem B1161229 : Blo 686314 1161229 := bbase (se 3 (by rfl) ⟨217730, by rfl⟩ : syracuseStep 1161229 = 435461) (by norm_num)
theorem B1030181 : Blo 686314 1030181 := bbase (se 4 (by rfl) ⟨96579, by rfl⟩ : syracuseStep 1030181 = 193159) (by norm_num)
theorem B1030205 : Blo 686314 1030205 := bbase (se 3 (by rfl) ⟨193163, by rfl⟩ : syracuseStep 1030205 = 386327) (by norm_num)
theorem B1325117 : Blo 686314 1325117 := bbase (se 3 (by rfl) ⟨248459, by rfl⟩ : syracuseStep 1325117 = 496919) (by norm_num)
theorem B1030229 : Blo 686314 1030229 := bbase (se 8 (by rfl) ⟨6036, by rfl⟩ : syracuseStep 1030229 = 12073) (by norm_num)
theorem B1161317 : Blo 686314 1161317 := bbase (se 4 (by rfl) ⟨108873, by rfl⟩ : syracuseStep 1161317 = 217747) (by norm_num)
theorem B1030253 : Blo 686314 1030253 := bbase (se 3 (by rfl) ⟨193172, by rfl⟩ : syracuseStep 1030253 = 386345) (by norm_num)
theorem B1030277 : Blo 686314 1030277 := bbase (se 4 (by rfl) ⟨96588, by rfl⟩ : syracuseStep 1030277 = 193177) (by norm_num)
theorem B1030301 : Blo 686314 1030301 := bbase (se 3 (by rfl) ⟨193181, by rfl⟩ : syracuseStep 1030301 = 386363) (by norm_num)
theorem B735409 : Blo 686314 735409 := bbase (se 2 (by rfl) ⟨275778, by rfl⟩ : syracuseStep 735409 = 551557) (by norm_num)
theorem B1030325 : Blo 686314 1030325 := bbase (se 5 (by rfl) ⟨48296, by rfl⟩ : syracuseStep 1030325 = 96593) (by norm_num)
theorem B4962485 : Blo 686314 4962485 := bbase (se 5 (by rfl) ⟨232616, by rfl⟩ : syracuseStep 4962485 = 465233) (by norm_num)
theorem B735413 : Blo 686314 735413 := bbase (se 5 (by rfl) ⟨34472, by rfl⟩ : syracuseStep 735413 = 68945) (by norm_num)
theorem B1030349 : Blo 686314 1030349 := bbase (se 3 (by rfl) ⟨193190, by rfl⟩ : syracuseStep 1030349 = 386381) (by norm_num)
theorem B1030373 : Blo 686314 1030373 := bbase (se 4 (by rfl) ⟨96597, by rfl⟩ : syracuseStep 1030373 = 193195) (by norm_num)
theorem B1161445 : Blo 686314 1161445 := bbase (se 4 (by rfl) ⟨108885, by rfl⟩ : syracuseStep 1161445 = 217771) (by norm_num)
theorem B932077 : Blo 686314 932077 := bbase (se 3 (by rfl) ⟨174764, by rfl⟩ : syracuseStep 932077 = 349529) (by norm_num)
theorem B1030397 : Blo 686314 1030397 := bbase (se 3 (by rfl) ⟨193199, by rfl⟩ : syracuseStep 1030397 = 386399) (by norm_num)
theorem B1030421 : Blo 686314 1030421 := bbase (se 6 (by rfl) ⟨24150, by rfl⟩ : syracuseStep 1030421 = 48301) (by norm_num)
theorem B3488021 : Blo 686314 3488021 := bbase (se 6 (by rfl) ⟨81750, by rfl⟩ : syracuseStep 3488021 = 163501) (by norm_num)
theorem B1030445 : Blo 686314 1030445 := bbase (se 3 (by rfl) ⟨193208, by rfl⟩ : syracuseStep 1030445 = 386417) (by norm_num)
theorem B1161533 : Blo 686314 1161533 := bbase (se 3 (by rfl) ⟨217787, by rfl⟩ : syracuseStep 1161533 = 435575) (by norm_num)
theorem B1030469 : Blo 686314 1030469 := bbase (se 4 (by rfl) ⟨96606, by rfl⟩ : syracuseStep 1030469 = 193213) (by norm_num)
theorem B1030493 : Blo 686314 1030493 := bbase (se 3 (by rfl) ⟨193217, by rfl⟩ : syracuseStep 1030493 = 386435) (by norm_num)
theorem B1030517 : Blo 686314 1030517 := bbase (se 5 (by rfl) ⟨48305, by rfl⟩ : syracuseStep 1030517 = 96611) (by norm_num)
theorem B1030541 : Blo 686314 1030541 := bbase (se 3 (by rfl) ⟨193226, by rfl⟩ : syracuseStep 1030541 = 386453) (by norm_num)
theorem B1030565 : Blo 686314 1030565 := bbase (se 4 (by rfl) ⟨96615, by rfl⟩ : syracuseStep 1030565 = 193231) (by norm_num)
theorem B1030589 : Blo 686314 1030589 := bbase (se 3 (by rfl) ⟨193235, by rfl⟩ : syracuseStep 1030589 = 386471) (by norm_num)
theorem B1161661 : Blo 686314 1161661 := bbase (se 3 (by rfl) ⟨217811, by rfl⟩ : syracuseStep 1161661 = 435623) (by norm_num)
theorem B1030613 : Blo 686314 1030613 := bbase (se 7 (by rfl) ⟨12077, by rfl⟩ : syracuseStep 1030613 = 24155) (by norm_num)
theorem B1030637 : Blo 686314 1030637 := bbase (se 3 (by rfl) ⟨193244, by rfl⟩ : syracuseStep 1030637 = 386489) (by norm_num)
theorem B1030661 : Blo 686314 1030661 := bbase (se 4 (by rfl) ⟨96624, by rfl⟩ : syracuseStep 1030661 = 193249) (by norm_num)
theorem B1161749 : Blo 686314 1161749 := bbase (se 6 (by rfl) ⟨27228, by rfl⟩ : syracuseStep 1161749 = 54457) (by norm_num)
theorem B1030685 : Blo 686314 1030685 := bbase (se 3 (by rfl) ⟨193253, by rfl⟩ : syracuseStep 1030685 = 386507) (by norm_num)
theorem B1030709 : Blo 686314 1030709 := bbase (se 5 (by rfl) ⟨48314, by rfl⟩ : syracuseStep 1030709 = 96629) (by norm_num)
theorem B1030733 : Blo 686314 1030733 := bbase (se 3 (by rfl) ⟨193262, by rfl⟩ : syracuseStep 1030733 = 386525) (by norm_num)
theorem B1030757 : Blo 686314 1030757 := bbase (se 4 (by rfl) ⟨96633, by rfl⟩ : syracuseStep 1030757 = 193267) (by norm_num)
theorem B1653365 : Blo 686314 1653365 := bbase (se 5 (by rfl) ⟨77501, by rfl⟩ : syracuseStep 1653365 = 155003) (by norm_num)
theorem B1030781 : Blo 686314 1030781 := bbase (se 3 (by rfl) ⟨193271, by rfl⟩ : syracuseStep 1030781 = 386543) (by norm_num)
theorem B1030805 : Blo 686314 1030805 := bbase (se 6 (by rfl) ⟨24159, by rfl⟩ : syracuseStep 1030805 = 48319) (by norm_num)
theorem B1161877 : Blo 686314 1161877 := bbase (se 6 (by rfl) ⟨27231, by rfl⟩ : syracuseStep 1161877 = 54463) (by norm_num)
theorem B1030829 : Blo 686314 1030829 := bbase (se 3 (by rfl) ⟨193280, by rfl⟩ : syracuseStep 1030829 = 386561) (by norm_num)
theorem B1030853 : Blo 686314 1030853 := bbase (se 4 (by rfl) ⟨96642, by rfl⟩ : syracuseStep 1030853 = 193285) (by norm_num)
theorem B1030877 : Blo 686314 1030877 := bbase (se 3 (by rfl) ⟨193289, by rfl⟩ : syracuseStep 1030877 = 386579) (by norm_num)
theorem B735977 : Blo 686314 735977 := bbase (se 2 (by rfl) ⟨275991, by rfl⟩ : syracuseStep 735977 = 551983) (by norm_num)
theorem B1161965 : Blo 686314 1161965 := bbase (se 3 (by rfl) ⟨217868, by rfl⟩ : syracuseStep 1161965 = 435737) (by norm_num)
theorem B1030901 : Blo 686314 1030901 := bbase (se 5 (by rfl) ⟨48323, by rfl⟩ : syracuseStep 1030901 = 96647) (by norm_num)
theorem B1030925 : Blo 686314 1030925 := bbase (se 3 (by rfl) ⟨193298, by rfl⟩ : syracuseStep 1030925 = 386597) (by norm_num)
theorem B1030949 : Blo 686314 1030949 := bbase (se 4 (by rfl) ⟨96651, by rfl⟩ : syracuseStep 1030949 = 193303) (by norm_num)
theorem B2210597 : Blo 686314 2210597 := bbase (se 4 (by rfl) ⟨207243, by rfl⟩ : syracuseStep 2210597 = 414487) (by norm_num)
theorem B1030973 : Blo 686314 1030973 := bbase (se 3 (by rfl) ⟨193307, by rfl⟩ : syracuseStep 1030973 = 386615) (by norm_num)
theorem B1030997 : Blo 686314 1030997 := bbase (se 9 (by rfl) ⟨3020, by rfl⟩ : syracuseStep 1030997 = 6041) (by norm_num)
theorem B22362965 : Blo 686314 22362965 := bbase (se 9 (by rfl) ⟨65516, by rfl⟩ : syracuseStep 22362965 = 131033) (by norm_num)
theorem B1031021 : Blo 686314 1031021 := bbase (se 3 (by rfl) ⟨193316, by rfl⟩ : syracuseStep 1031021 = 386633) (by norm_num)
theorem B1162093 : Blo 686314 1162093 := bbase (se 3 (by rfl) ⟨217892, by rfl⟩ : syracuseStep 1162093 = 435785) (by norm_num)
theorem B1031045 : Blo 686314 1031045 := bbase (se 4 (by rfl) ⟨96660, by rfl⟩ : syracuseStep 1031045 = 193321) (by norm_num)
theorem B1031069 : Blo 686314 1031069 := bbase (se 3 (by rfl) ⟨193325, by rfl⟩ : syracuseStep 1031069 = 386651) (by norm_num)
theorem B736165 : Blo 686314 736165 := bbase (se 4 (by rfl) ⟨69015, by rfl⟩ : syracuseStep 736165 = 138031) (by norm_num)
theorem B1031093 : Blo 686314 1031093 := bbase (se 5 (by rfl) ⟨48332, by rfl⟩ : syracuseStep 1031093 = 96665) (by norm_num)
theorem B1162181 : Blo 686314 1162181 := bbase (se 4 (by rfl) ⟨108954, by rfl⟩ : syracuseStep 1162181 = 217909) (by norm_num)
theorem B1031117 : Blo 686314 1031117 := bbase (se 3 (by rfl) ⟨193334, by rfl⟩ : syracuseStep 1031117 = 386669) (by norm_num)
theorem B1031141 : Blo 686314 1031141 := bbase (se 4 (by rfl) ⟨96669, by rfl⟩ : syracuseStep 1031141 = 193339) (by norm_num)
theorem B1653749 : Blo 686314 1653749 := bbase (se 5 (by rfl) ⟨77519, by rfl⟩ : syracuseStep 1653749 = 155039) (by norm_num)
theorem B1031165 : Blo 686314 1031165 := bbase (se 3 (by rfl) ⟨193343, by rfl⟩ : syracuseStep 1031165 = 386687) (by norm_num)
theorem B1031189 : Blo 686314 1031189 := bbase (se 6 (by rfl) ⟨24168, by rfl⟩ : syracuseStep 1031189 = 48337) (by norm_num)
theorem B1031213 : Blo 686314 1031213 := bbase (se 3 (by rfl) ⟨193352, by rfl⟩ : syracuseStep 1031213 = 386705) (by norm_num)
theorem B1031237 : Blo 686314 1031237 := bbase (se 4 (by rfl) ⟨96678, by rfl⟩ : syracuseStep 1031237 = 193357) (by norm_num)
theorem B1162309 : Blo 686314 1162309 := bbase (se 4 (by rfl) ⟨108966, by rfl⟩ : syracuseStep 1162309 = 217933) (by norm_num)
theorem B1031261 : Blo 686314 1031261 := bbase (se 3 (by rfl) ⟨193361, by rfl⟩ : syracuseStep 1031261 = 386723) (by norm_num)
theorem B1031285 : Blo 686314 1031285 := bbase (se 5 (by rfl) ⟨48341, by rfl⟩ : syracuseStep 1031285 = 96683) (by norm_num)
theorem B1031309 : Blo 686314 1031309 := bbase (se 3 (by rfl) ⟨193370, by rfl⟩ : syracuseStep 1031309 = 386741) (by norm_num)
theorem B1162397 : Blo 686314 1162397 := bbase (se 3 (by rfl) ⟨217949, by rfl⟩ : syracuseStep 1162397 = 435899) (by norm_num)
theorem B1031333 : Blo 686314 1031333 := bbase (se 4 (by rfl) ⟨96687, by rfl⟩ : syracuseStep 1031333 = 193375) (by norm_num)
theorem B1031357 : Blo 686314 1031357 := bbase (se 3 (by rfl) ⟨193379, by rfl⟩ : syracuseStep 1031357 = 386759) (by norm_num)
theorem B1653949 : Blo 686314 1653949 := bbase (se 3 (by rfl) ⟨310115, by rfl⟩ : syracuseStep 1653949 = 620231) (by norm_num)
theorem B1031381 : Blo 686314 1031381 := bbase (se 7 (by rfl) ⟨12086, by rfl⟩ : syracuseStep 1031381 = 24173) (by norm_num)
theorem B1981669 : Blo 686314 1981669 := bbase (se 4 (by rfl) ⟨185781, by rfl⟩ : syracuseStep 1981669 = 371563) (by norm_num)
theorem B1031405 : Blo 686314 1031405 := bbase (se 3 (by rfl) ⟨193388, by rfl⟩ : syracuseStep 1031405 = 386777) (by norm_num)
theorem B1031429 : Blo 686314 1031429 := bbase (se 4 (by rfl) ⟨96696, by rfl⟩ : syracuseStep 1031429 = 193393) (by norm_num)
theorem B1031453 : Blo 686314 1031453 := bbase (se 3 (by rfl) ⟨193397, by rfl⟩ : syracuseStep 1031453 = 386795) (by norm_num)
theorem B1162525 : Blo 686314 1162525 := bbase (se 3 (by rfl) ⟨217973, by rfl⟩ : syracuseStep 1162525 = 435947) (by norm_num)
theorem B1326365 : Blo 686314 1326365 := bbase (se 3 (by rfl) ⟨248693, by rfl⟩ : syracuseStep 1326365 = 497387) (by norm_num)
theorem B1031477 : Blo 686314 1031477 := bbase (se 5 (by rfl) ⟨48350, by rfl⟩ : syracuseStep 1031477 = 96701) (by norm_num)
theorem B1031501 : Blo 686314 1031501 := bbase (se 3 (by rfl) ⟨193406, by rfl⟩ : syracuseStep 1031501 = 386813) (by norm_num)
theorem B1031525 : Blo 686314 1031525 := bbase (se 4 (by rfl) ⟨96705, by rfl⟩ : syracuseStep 1031525 = 193411) (by norm_num)
theorem B1162613 : Blo 686314 1162613 := bbase (se 5 (by rfl) ⟨54497, by rfl⟩ : syracuseStep 1162613 = 108995) (by norm_num)
theorem B1031549 : Blo 686314 1031549 := bbase (se 3 (by rfl) ⟨193415, by rfl⟩ : syracuseStep 1031549 = 386831) (by norm_num)
theorem B1031573 : Blo 686314 1031573 := bbase (se 6 (by rfl) ⟨24177, by rfl⟩ : syracuseStep 1031573 = 48355) (by norm_num)
theorem B1031597 : Blo 686314 1031597 := bbase (se 3 (by rfl) ⟨193424, by rfl⟩ : syracuseStep 1031597 = 386849) (by norm_num)
theorem B1031621 : Blo 686314 1031621 := bbase (se 4 (by rfl) ⟨96714, by rfl⟩ : syracuseStep 1031621 = 193429) (by norm_num)
theorem B1031645 : Blo 686314 1031645 := bbase (se 3 (by rfl) ⟨193433, by rfl⟩ : syracuseStep 1031645 = 386867) (by norm_num)
theorem B1031669 : Blo 686314 1031669 := bbase (se 5 (by rfl) ⟨48359, by rfl⟩ : syracuseStep 1031669 = 96719) (by norm_num)
theorem B1162741 : Blo 686314 1162741 := bbase (se 5 (by rfl) ⟨54503, by rfl⟩ : syracuseStep 1162741 = 109007) (by norm_num)
theorem B1031693 : Blo 686314 1031693 := bbase (se 3 (by rfl) ⟨193442, by rfl⟩ : syracuseStep 1031693 = 386885) (by norm_num)
theorem B1031717 : Blo 686314 1031717 := bbase (se 4 (by rfl) ⟨96723, by rfl⟩ : syracuseStep 1031717 = 193447) (by norm_num)
theorem B3489317 : Blo 686314 3489317 := bbase (se 4 (by rfl) ⟨327123, by rfl⟩ : syracuseStep 3489317 = 654247) (by norm_num)
theorem B1031741 : Blo 686314 1031741 := bbase (se 3 (by rfl) ⟨193451, by rfl⟩ : syracuseStep 1031741 = 386903) (by norm_num)
theorem B1162829 : Blo 686314 1162829 := bbase (se 3 (by rfl) ⟨218030, by rfl⟩ : syracuseStep 1162829 = 436061) (by norm_num)
theorem B1031765 : Blo 686314 1031765 := bbase (se 8 (by rfl) ⟨6045, by rfl⟩ : syracuseStep 1031765 = 12091) (by norm_num)
theorem B1031789 : Blo 686314 1031789 := bbase (se 3 (by rfl) ⟨193460, by rfl⟩ : syracuseStep 1031789 = 386921) (by norm_num)
theorem B2932357 : Blo 686314 2932357 := bbase (se 4 (by rfl) ⟨274908, by rfl⟩ : syracuseStep 2932357 = 549817) (by norm_num)
theorem B1031813 : Blo 686314 1031813 := bbase (se 4 (by rfl) ⟨96732, by rfl⟩ : syracuseStep 1031813 = 193465) (by norm_num)
theorem B1031837 : Blo 686314 1031837 := bbase (se 3 (by rfl) ⟨193469, by rfl⟩ : syracuseStep 1031837 = 386939) (by norm_num)
theorem B1031861 : Blo 686314 1031861 := bbase (se 5 (by rfl) ⟨48368, by rfl⟩ : syracuseStep 1031861 = 96737) (by norm_num)
theorem B1031885 : Blo 686314 1031885 := bbase (se 3 (by rfl) ⟨193478, by rfl⟩ : syracuseStep 1031885 = 386957) (by norm_num)
theorem B1162957 : Blo 686314 1162957 := bbase (se 3 (by rfl) ⟨218054, by rfl⟩ : syracuseStep 1162957 = 436109) (by norm_num)
theorem B736985 : Blo 686314 736985 := bbase (se 2 (by rfl) ⟨276369, by rfl⟩ : syracuseStep 736985 = 552739) (by norm_num)
theorem B1031909 : Blo 686314 1031909 := bbase (se 4 (by rfl) ⟨96741, by rfl⟩ : syracuseStep 1031909 = 193483) (by norm_num)
theorem B1031933 : Blo 686314 1031933 := bbase (se 3 (by rfl) ⟨193487, by rfl⟩ : syracuseStep 1031933 = 386975) (by norm_num)
theorem B1031957 : Blo 686314 1031957 := bbase (se 6 (by rfl) ⟨24186, by rfl⟩ : syracuseStep 1031957 = 48373) (by norm_num)
theorem B1163045 : Blo 686314 1163045 := bbase (se 4 (by rfl) ⟨109035, by rfl⟩ : syracuseStep 1163045 = 218071) (by norm_num)
theorem B1031981 : Blo 686314 1031981 := bbase (se 3 (by rfl) ⟨193496, by rfl⟩ : syracuseStep 1031981 = 386993) (by norm_num)
theorem B1032005 : Blo 686314 1032005 := bbase (se 4 (by rfl) ⟨96750, by rfl⟩ : syracuseStep 1032005 = 193501) (by norm_num)
theorem B1032029 : Blo 686314 1032029 := bbase (se 3 (by rfl) ⟨193505, by rfl⟩ : syracuseStep 1032029 = 387011) (by norm_num)
theorem B1032053 : Blo 686314 1032053 := bbase (se 5 (by rfl) ⟨48377, by rfl⟩ : syracuseStep 1032053 = 96755) (by norm_num)
theorem B1032077 : Blo 686314 1032077 := bbase (se 3 (by rfl) ⟨193514, by rfl⟩ : syracuseStep 1032077 = 387029) (by norm_num)
theorem B1032101 : Blo 686314 1032101 := bbase (se 4 (by rfl) ⟨96759, by rfl⟩ : syracuseStep 1032101 = 193519) (by norm_num)
theorem B1163173 : Blo 686314 1163173 := bbase (se 4 (by rfl) ⟨109047, by rfl⟩ : syracuseStep 1163173 = 218095) (by norm_num)
theorem B1032125 : Blo 686314 1032125 := bbase (se 3 (by rfl) ⟨193523, by rfl⟩ : syracuseStep 1032125 = 387047) (by norm_num)
theorem B1032149 : Blo 686314 1032149 := bbase (se 7 (by rfl) ⟨12095, by rfl⟩ : syracuseStep 1032149 = 24191) (by norm_num)
theorem B1032173 : Blo 686314 1032173 := bbase (se 3 (by rfl) ⟨193532, by rfl⟩ : syracuseStep 1032173 = 387065) (by norm_num)
theorem B1163261 : Blo 686314 1163261 := bbase (se 3 (by rfl) ⟨218111, by rfl⟩ : syracuseStep 1163261 = 436223) (by norm_num)
theorem B1032197 : Blo 686314 1032197 := bbase (se 4 (by rfl) ⟨96768, by rfl⟩ : syracuseStep 1032197 = 193537) (by norm_num)
theorem B1032221 : Blo 686314 1032221 := bbase (se 3 (by rfl) ⟨193541, by rfl⟩ : syracuseStep 1032221 = 387083) (by norm_num)
theorem B1032245 : Blo 686314 1032245 := bbase (se 5 (by rfl) ⟨48386, by rfl⟩ : syracuseStep 1032245 = 96773) (by norm_num)
theorem B1032269 : Blo 686314 1032269 := bbase (se 3 (by rfl) ⟨193550, by rfl⟩ : syracuseStep 1032269 = 387101) (by norm_num)
theorem B1032293 : Blo 686314 1032293 := bbase (se 4 (by rfl) ⟨96777, by rfl⟩ : syracuseStep 1032293 = 193555) (by norm_num)
theorem B1032317 : Blo 686314 1032317 := bbase (se 3 (by rfl) ⟨193559, by rfl⟩ : syracuseStep 1032317 = 387119) (by norm_num)
theorem B1163389 : Blo 686314 1163389 := bbase (se 3 (by rfl) ⟨218135, by rfl⟩ : syracuseStep 1163389 = 436271) (by norm_num)
theorem B1032341 : Blo 686314 1032341 := bbase (se 6 (by rfl) ⟨24195, by rfl⟩ : syracuseStep 1032341 = 48391) (by norm_num)
theorem B1032365 : Blo 686314 1032365 := bbase (se 3 (by rfl) ⟨193568, by rfl⟩ : syracuseStep 1032365 = 387137) (by norm_num)
theorem B2474165 : Blo 686314 2474165 := bbase (se 5 (by rfl) ⟨115976, by rfl⟩ : syracuseStep 2474165 = 231953) (by norm_num)
theorem B4538549 : Blo 686314 4538549 := bbase (se 5 (by rfl) ⟨212744, by rfl⟩ : syracuseStep 4538549 = 425489) (by norm_num)
theorem B1032389 : Blo 686314 1032389 := bbase (se 4 (by rfl) ⟨96786, by rfl⟩ : syracuseStep 1032389 = 193573) (by norm_num)
theorem B1163477 : Blo 686314 1163477 := bbase (se 7 (by rfl) ⟨13634, by rfl⟩ : syracuseStep 1163477 = 27269) (by norm_num)
theorem B1032413 : Blo 686314 1032413 := bbase (se 3 (by rfl) ⟨193577, by rfl⟩ : syracuseStep 1032413 = 387155) (by norm_num)
theorem B1032437 : Blo 686314 1032437 := bbase (se 5 (by rfl) ⟨48395, by rfl⟩ : syracuseStep 1032437 = 96791) (by norm_num)
theorem B1032461 : Blo 686314 1032461 := bbase (se 3 (by rfl) ⟨193586, by rfl⟩ : syracuseStep 1032461 = 387173) (by norm_num)
theorem B1032485 : Blo 686314 1032485 := bbase (se 4 (by rfl) ⟨96795, by rfl⟩ : syracuseStep 1032485 = 193591) (by norm_num)
theorem B1032509 : Blo 686314 1032509 := bbase (se 3 (by rfl) ⟨193595, by rfl⟩ : syracuseStep 1032509 = 387191) (by norm_num)
theorem B1032533 : Blo 686314 1032533 := bbase (se 10 (by rfl) ⟨1512, by rfl⟩ : syracuseStep 1032533 = 3025) (by norm_num)
theorem B1163605 : Blo 686314 1163605 := bbase (se 10 (by rfl) ⟨1704, by rfl⟩ : syracuseStep 1163605 = 3409) (by norm_num)
theorem B1032557 : Blo 686314 1032557 := bbase (se 3 (by rfl) ⟨193604, by rfl⟩ : syracuseStep 1032557 = 387209) (by norm_num)
theorem B1032581 : Blo 686314 1032581 := bbase (se 4 (by rfl) ⟨96804, by rfl⟩ : syracuseStep 1032581 = 193609) (by norm_num)
theorem B868745 : Blo 686314 868745 := bbase (se 2 (by rfl) ⟨325779, by rfl⟩ : syracuseStep 868745 = 651559) (by norm_num)
theorem B1032605 : Blo 686314 1032605 := bbase (se 3 (by rfl) ⟨193613, by rfl⟩ : syracuseStep 1032605 = 387227) (by norm_num)
theorem B1163693 : Blo 686314 1163693 := bbase (se 3 (by rfl) ⟨218192, by rfl⟩ : syracuseStep 1163693 = 436385) (by norm_num)
theorem B1032629 : Blo 686314 1032629 := bbase (se 5 (by rfl) ⟨48404, by rfl⟩ : syracuseStep 1032629 = 96809) (by norm_num)
theorem B868801 : Blo 686314 868801 := bbase (se 2 (by rfl) ⟨325800, by rfl⟩ : syracuseStep 868801 = 651601) (by norm_num)
theorem B1032653 : Blo 686314 1032653 := bbase (se 3 (by rfl) ⟨193622, by rfl⟩ : syracuseStep 1032653 = 387245) (by norm_num)
theorem B1032677 : Blo 686314 1032677 := bbase (se 4 (by rfl) ⟨96813, by rfl⟩ : syracuseStep 1032677 = 193627) (by norm_num)
theorem B1032701 : Blo 686314 1032701 := bbase (se 3 (by rfl) ⟨193631, by rfl⟩ : syracuseStep 1032701 = 387263) (by norm_num)
theorem B1032725 : Blo 686314 1032725 := bbase (se 6 (by rfl) ⟨24204, by rfl⟩ : syracuseStep 1032725 = 48409) (by norm_num)
theorem B868897 : Blo 686314 868897 := bbase (se 2 (by rfl) ⟨325836, by rfl⟩ : syracuseStep 868897 = 651673) (by norm_num)
theorem B1032749 : Blo 686314 1032749 := bbase (se 3 (by rfl) ⟨193640, by rfl⟩ : syracuseStep 1032749 = 387281) (by norm_num)
theorem B1163821 : Blo 686314 1163821 := bbase (se 3 (by rfl) ⟨218216, by rfl⟩ : syracuseStep 1163821 = 436433) (by norm_num)
theorem B1032773 : Blo 686314 1032773 := bbase (se 4 (by rfl) ⟨96822, by rfl⟩ : syracuseStep 1032773 = 193645) (by norm_num)
theorem B1032797 : Blo 686314 1032797 := bbase (se 3 (by rfl) ⟨193649, by rfl⟩ : syracuseStep 1032797 = 387299) (by norm_num)
theorem B1032821 : Blo 686314 1032821 := bbase (se 5 (by rfl) ⟨48413, by rfl⟩ : syracuseStep 1032821 = 96827) (by norm_num)
theorem B1163909 : Blo 686314 1163909 := bbase (se 4 (by rfl) ⟨109116, by rfl⟩ : syracuseStep 1163909 = 218233) (by norm_num)
theorem B1032845 : Blo 686314 1032845 := bbase (se 3 (by rfl) ⟨193658, by rfl⟩ : syracuseStep 1032845 = 387317) (by norm_num)
theorem B1491605 : Blo 686314 1491605 := bbase (se 6 (by rfl) ⟨34959, by rfl⟩ : syracuseStep 1491605 = 69919) (by norm_num)
theorem B1032869 : Blo 686314 1032869 := bbase (se 4 (by rfl) ⟨96831, by rfl⟩ : syracuseStep 1032869 = 193663) (by norm_num)
theorem B1032893 : Blo 686314 1032893 := bbase (se 3 (by rfl) ⟨193667, by rfl⟩ : syracuseStep 1032893 = 387335) (by norm_num)
theorem B869069 : Blo 686314 869069 := bbase (se 3 (by rfl) ⟨162950, by rfl⟩ : syracuseStep 869069 = 325901) (by norm_num)
theorem B1032917 : Blo 686314 1032917 := bbase (se 7 (by rfl) ⟨12104, by rfl⟩ : syracuseStep 1032917 = 24209) (by norm_num)
theorem B1655525 : Blo 686314 1655525 := bbase (se 4 (by rfl) ⟨155205, by rfl⟩ : syracuseStep 1655525 = 310411) (by norm_num)
theorem B1032941 : Blo 686314 1032941 := bbase (se 3 (by rfl) ⟨193676, by rfl⟩ : syracuseStep 1032941 = 387353) (by norm_num)
theorem B869125 : Blo 686314 869125 := bbase (se 4 (by rfl) ⟨81480, by rfl⟩ : syracuseStep 869125 = 162961) (by norm_num)
theorem B1032965 : Blo 686314 1032965 := bbase (se 4 (by rfl) ⟨96840, by rfl⟩ : syracuseStep 1032965 = 193681) (by norm_num)
theorem B1164037 : Blo 686314 1164037 := bbase (se 4 (by rfl) ⟨109128, by rfl⟩ : syracuseStep 1164037 = 218257) (by norm_num)
theorem B1032989 : Blo 686314 1032989 := bbase (se 3 (by rfl) ⟨193685, by rfl⟩ : syracuseStep 1032989 = 387371) (by norm_num)
theorem B1033013 : Blo 686314 1033013 := bbase (se 5 (by rfl) ⟨48422, by rfl⟩ : syracuseStep 1033013 = 96845) (by norm_num)
theorem B3490613 : Blo 686314 3490613 := bbase (se 5 (by rfl) ⟨163622, by rfl⟩ : syracuseStep 3490613 = 327245) (by norm_num)
theorem B1033037 : Blo 686314 1033037 := bbase (se 3 (by rfl) ⟨193694, by rfl⟩ : syracuseStep 1033037 = 387389) (by norm_num)
theorem B1164125 : Blo 686314 1164125 := bbase (se 3 (by rfl) ⟨218273, by rfl⟩ : syracuseStep 1164125 = 436547) (by norm_num)
theorem B869221 : Blo 686314 869221 := bbase (se 4 (by rfl) ⟨81489, by rfl⟩ : syracuseStep 869221 = 162979) (by norm_num)
theorem B1033061 : Blo 686314 1033061 := bbase (se 4 (by rfl) ⟨96849, by rfl⟩ : syracuseStep 1033061 = 193699) (by norm_num)
theorem B1033085 : Blo 686314 1033085 := bbase (se 3 (by rfl) ⟨193703, by rfl⟩ : syracuseStep 1033085 = 387407) (by norm_num)
theorem B1033109 : Blo 686314 1033109 := bbase (se 6 (by rfl) ⟨24213, by rfl⟩ : syracuseStep 1033109 = 48427) (by norm_num)
theorem B1033133 : Blo 686314 1033133 := bbase (se 3 (by rfl) ⟨193712, by rfl⟩ : syracuseStep 1033133 = 387425) (by norm_num)
theorem B1033157 : Blo 686314 1033157 := bbase (se 4 (by rfl) ⟨96858, by rfl⟩ : syracuseStep 1033157 = 193717) (by norm_num)
theorem B1033181 : Blo 686314 1033181 := bbase (se 3 (by rfl) ⟨193721, by rfl⟩ : syracuseStep 1033181 = 387443) (by norm_num)
theorem B1164253 : Blo 686314 1164253 := bbase (se 3 (by rfl) ⟨218297, by rfl⟩ : syracuseStep 1164253 = 436595) (by norm_num)
theorem B2606053 : Blo 686314 2606053 := bbase (se 4 (by rfl) ⟨244317, by rfl⟩ : syracuseStep 2606053 = 488635) (by norm_num)
theorem B1033205 : Blo 686314 1033205 := bbase (se 5 (by rfl) ⟨48431, by rfl⟩ : syracuseStep 1033205 = 96863) (by norm_num)
theorem B1033229 : Blo 686314 1033229 := bbase (se 3 (by rfl) ⟨193730, by rfl⟩ : syracuseStep 1033229 = 387461) (by norm_num)
theorem B869393 : Blo 686314 869393 := bbase (se 2 (by rfl) ⟨326022, by rfl⟩ : syracuseStep 869393 = 652045) (by norm_num)
theorem B1033253 : Blo 686314 1033253 := bbase (se 4 (by rfl) ⟨96867, by rfl⟩ : syracuseStep 1033253 = 193735) (by norm_num)
theorem B1164341 : Blo 686314 1164341 := bbase (se 5 (by rfl) ⟨54578, by rfl⟩ : syracuseStep 1164341 = 109157) (by norm_num)
theorem B1033277 : Blo 686314 1033277 := bbase (se 3 (by rfl) ⟨193739, by rfl⟩ : syracuseStep 1033277 = 387479) (by norm_num)
theorem B869449 : Blo 686314 869449 := bbase (se 2 (by rfl) ⟨326043, by rfl⟩ : syracuseStep 869449 = 652087) (by norm_num)
theorem B1033301 : Blo 686314 1033301 := bbase (se 8 (by rfl) ⟨6054, by rfl⟩ : syracuseStep 1033301 = 12109) (by norm_num)
theorem B1033325 : Blo 686314 1033325 := bbase (se 3 (by rfl) ⟨193748, by rfl⟩ : syracuseStep 1033325 = 387497) (by norm_num)
theorem B1033349 : Blo 686314 1033349 := bbase (se 4 (by rfl) ⟨96876, by rfl⟩ : syracuseStep 1033349 = 193753) (by norm_num)
theorem B1033373 : Blo 686314 1033373 := bbase (se 3 (by rfl) ⟨193757, by rfl⟩ : syracuseStep 1033373 = 387515) (by norm_num)
theorem B869545 : Blo 686314 869545 := bbase (se 2 (by rfl) ⟨326079, by rfl⟩ : syracuseStep 869545 = 652159) (by norm_num)
theorem B1033397 : Blo 686314 1033397 := bbase (se 5 (by rfl) ⟨48440, by rfl⟩ : syracuseStep 1033397 = 96881) (by norm_num)
theorem B1164469 : Blo 686314 1164469 := bbase (se 5 (by rfl) ⟨54584, by rfl⟩ : syracuseStep 1164469 = 109169) (by norm_num)
theorem B1033421 : Blo 686314 1033421 := bbase (se 3 (by rfl) ⟨193766, by rfl⟩ : syracuseStep 1033421 = 387533) (by norm_num)
theorem B1033445 : Blo 686314 1033445 := bbase (se 4 (by rfl) ⟨96885, by rfl⟩ : syracuseStep 1033445 = 193771) (by norm_num)
theorem B3720437 : Blo 686314 3720437 := bbase (se 5 (by rfl) ⟨174395, by rfl⟩ : syracuseStep 3720437 = 348791) (by norm_num)
theorem B1033469 : Blo 686314 1033469 := bbase (se 3 (by rfl) ⟨193775, by rfl⟩ : syracuseStep 1033469 = 387551) (by norm_num)
theorem B1164557 : Blo 686314 1164557 := bbase (se 3 (by rfl) ⟨218354, by rfl⟩ : syracuseStep 1164557 = 436709) (by norm_num)
theorem B2606357 : Blo 686314 2606357 := bbase (se 6 (by rfl) ⟨61086, by rfl⟩ : syracuseStep 2606357 = 122173) (by norm_num)
theorem B1033493 : Blo 686314 1033493 := bbase (se 6 (by rfl) ⟨24222, by rfl⟩ : syracuseStep 1033493 = 48445) (by norm_num)
theorem B1033517 : Blo 686314 1033517 := bbase (se 3 (by rfl) ⟨193784, by rfl⟩ : syracuseStep 1033517 = 387569) (by norm_num)
theorem B1033541 : Blo 686314 1033541 := bbase (se 4 (by rfl) ⟨96894, by rfl⟩ : syracuseStep 1033541 = 193789) (by norm_num)
theorem B869717 : Blo 686314 869717 := bbase (se 12 (by rfl) ⟨318, by rfl⟩ : syracuseStep 869717 = 637) (by norm_num)
theorem B1033565 : Blo 686314 1033565 := bbase (se 3 (by rfl) ⟨193793, by rfl⟩ : syracuseStep 1033565 = 387587) (by norm_num)
theorem B1033589 : Blo 686314 1033589 := bbase (se 5 (by rfl) ⟨48449, by rfl⟩ : syracuseStep 1033589 = 96899) (by norm_num)
theorem B869773 : Blo 686314 869773 := bbase (se 3 (by rfl) ⟨163082, by rfl⟩ : syracuseStep 869773 = 326165) (by norm_num)
theorem B1033613 : Blo 686314 1033613 := bbase (se 3 (by rfl) ⟨193802, by rfl⟩ : syracuseStep 1033613 = 387605) (by norm_num)
theorem B1164685 : Blo 686314 1164685 := bbase (se 3 (by rfl) ⟨218378, by rfl⟩ : syracuseStep 1164685 = 436757) (by norm_num)
theorem B1033637 : Blo 686314 1033637 := bbase (se 4 (by rfl) ⟨96903, by rfl⟩ : syracuseStep 1033637 = 193807) (by norm_num)
theorem B2475445 : Blo 686314 2475445 := bbase (se 5 (by rfl) ⟨116036, by rfl⟩ : syracuseStep 2475445 = 232073) (by norm_num)
theorem B1033661 : Blo 686314 1033661 := bbase (se 3 (by rfl) ⟨193811, by rfl⟩ : syracuseStep 1033661 = 387623) (by norm_num)
theorem B1033685 : Blo 686314 1033685 := bbase (se 7 (by rfl) ⟨12113, by rfl⟩ : syracuseStep 1033685 = 24227) (by norm_num)
theorem B1492453 : Blo 686314 1492453 := bbase (se 4 (by rfl) ⟨139917, by rfl⟩ : syracuseStep 1492453 = 279835) (by norm_num)
theorem B1164773 : Blo 686314 1164773 := bbase (se 4 (by rfl) ⟨109197, by rfl⟩ : syracuseStep 1164773 = 218395) (by norm_num)
theorem B869869 : Blo 686314 869869 := bbase (se 3 (by rfl) ⟨163100, by rfl⟩ : syracuseStep 869869 = 326201) (by norm_num)
theorem B1033709 : Blo 686314 1033709 := bbase (se 3 (by rfl) ⟨193820, by rfl⟩ : syracuseStep 1033709 = 387641) (by norm_num)
theorem B1033733 : Blo 686314 1033733 := bbase (se 4 (by rfl) ⟨96912, by rfl⟩ : syracuseStep 1033733 = 193825) (by norm_num)
theorem B1033757 : Blo 686314 1033757 := bbase (se 3 (by rfl) ⟨193829, by rfl⟩ : syracuseStep 1033757 = 387659) (by norm_num)
theorem B1033781 : Blo 686314 1033781 := bbase (se 5 (by rfl) ⟨48458, by rfl⟩ : syracuseStep 1033781 = 96917) (by norm_num)
theorem B1033805 : Blo 686314 1033805 := bbase (se 3 (by rfl) ⟨193838, by rfl⟩ : syracuseStep 1033805 = 387677) (by norm_num)
theorem B1033829 : Blo 686314 1033829 := bbase (se 4 (by rfl) ⟨96921, by rfl⟩ : syracuseStep 1033829 = 193843) (by norm_num)
theorem B1164901 : Blo 686314 1164901 := bbase (se 4 (by rfl) ⟨109209, by rfl⟩ : syracuseStep 1164901 = 218419) (by norm_num)
theorem B1033853 : Blo 686314 1033853 := bbase (se 3 (by rfl) ⟨193847, by rfl⟩ : syracuseStep 1033853 = 387695) (by norm_num)
theorem B1033877 : Blo 686314 1033877 := bbase (se 6 (by rfl) ⟨24231, by rfl⟩ : syracuseStep 1033877 = 48463) (by norm_num)
theorem B870041 : Blo 686314 870041 := bbase (se 2 (by rfl) ⟨326265, by rfl⟩ : syracuseStep 870041 = 652531) (by norm_num)
theorem B1033901 : Blo 686314 1033901 := bbase (se 3 (by rfl) ⟨193856, by rfl⟩ : syracuseStep 1033901 = 387713) (by norm_num)
theorem B1033925 : Blo 686314 1033925 := bbase (se 4 (by rfl) ⟨96930, by rfl⟩ : syracuseStep 1033925 = 193861) (by norm_num)
theorem B870097 : Blo 686314 870097 := bbase (se 2 (by rfl) ⟨326286, by rfl⟩ : syracuseStep 870097 = 652573) (by norm_num)
theorem B1033949 : Blo 686314 1033949 := bbase (se 3 (by rfl) ⟨193865, by rfl⟩ : syracuseStep 1033949 = 387731) (by norm_num)
theorem B1033973 : Blo 686314 1033973 := bbase (se 5 (by rfl) ⟨48467, by rfl⟩ : syracuseStep 1033973 = 96935) (by norm_num)
theorem B1033997 : Blo 686314 1033997 := bbase (se 3 (by rfl) ⟨193874, by rfl⟩ : syracuseStep 1033997 = 387749) (by norm_num)
theorem B1034021 : Blo 686314 1034021 := bbase (se 4 (by rfl) ⟨96939, by rfl⟩ : syracuseStep 1034021 = 193879) (by norm_num)
theorem B870193 : Blo 686314 870193 := bbase (se 2 (by rfl) ⟨326322, by rfl⟩ : syracuseStep 870193 = 652645) (by norm_num)
theorem B1034045 : Blo 686314 1034045 := bbase (se 3 (by rfl) ⟨193883, by rfl⟩ : syracuseStep 1034045 = 387767) (by norm_num)
theorem B1394509 : Blo 686314 1394509 := bbase (se 3 (by rfl) ⟨261470, by rfl⟩ : syracuseStep 1394509 = 522941) (by norm_num)
theorem B1034069 : Blo 686314 1034069 := bbase (se 9 (by rfl) ⟨3029, by rfl⟩ : syracuseStep 1034069 = 6059) (by norm_num)
theorem B3131237 : Blo 686314 3131237 := bbase (se 4 (by rfl) ⟨293553, by rfl⟩ : syracuseStep 3131237 = 587107) (by norm_num)
theorem B1034093 : Blo 686314 1034093 := bbase (se 3 (by rfl) ⟨193892, by rfl⟩ : syracuseStep 1034093 = 387785) (by norm_num)
theorem B1034117 : Blo 686314 1034117 := bbase (se 4 (by rfl) ⟨96948, by rfl⟩ : syracuseStep 1034117 = 193897) (by norm_num)
theorem B1034141 : Blo 686314 1034141 := bbase (se 3 (by rfl) ⟨193901, by rfl⟩ : syracuseStep 1034141 = 387803) (by norm_num)
theorem B1034165 : Blo 686314 1034165 := bbase (se 5 (by rfl) ⟨48476, by rfl⟩ : syracuseStep 1034165 = 96953) (by norm_num)
theorem B837577 : Blo 686314 837577 := bbase (se 2 (by rfl) ⟨314091, by rfl⟩ : syracuseStep 837577 = 628183) (by norm_num)
theorem B1034189 : Blo 686314 1034189 := bbase (se 3 (by rfl) ⟨193910, by rfl⟩ : syracuseStep 1034189 = 387821) (by norm_num)
theorem B870365 : Blo 686314 870365 := bbase (se 3 (by rfl) ⟨163193, by rfl⟩ : syracuseStep 870365 = 326387) (by norm_num)
theorem B1034213 : Blo 686314 1034213 := bbase (se 4 (by rfl) ⟨96957, by rfl⟩ : syracuseStep 1034213 = 193915) (by norm_num)
theorem B1034237 : Blo 686314 1034237 := bbase (se 3 (by rfl) ⟨193919, by rfl⟩ : syracuseStep 1034237 = 387839) (by norm_num)
theorem B772105 : Blo 686314 772105 := bbase (se 2 (by rfl) ⟨289539, by rfl⟩ : syracuseStep 772105 = 579079) (by norm_num)
theorem B870421 : Blo 686314 870421 := bbase (se 6 (by rfl) ⟨20400, by rfl⟩ : syracuseStep 870421 = 40801) (by norm_num)
theorem B4769813 : Blo 686314 4769813 := bbase (se 6 (by rfl) ⟨111792, by rfl⟩ : syracuseStep 4769813 = 223585) (by norm_num)
theorem B1034261 : Blo 686314 1034261 := bbase (se 6 (by rfl) ⟨24240, by rfl⟩ : syracuseStep 1034261 = 48481) (by norm_num)
theorem B772141 : Blo 686314 772141 := bbase (se 3 (by rfl) ⟨144776, by rfl⟩ : syracuseStep 772141 = 289553) (by norm_num)
theorem B1034285 : Blo 686314 1034285 := bbase (se 3 (by rfl) ⟨193928, by rfl⟩ : syracuseStep 1034285 = 387857) (by norm_num)
theorem B1034309 : Blo 686314 1034309 := bbase (se 4 (by rfl) ⟨96966, by rfl⟩ : syracuseStep 1034309 = 193933) (by norm_num)
theorem B3491909 : Blo 686314 3491909 := bbase (se 4 (by rfl) ⟨327366, by rfl⟩ : syracuseStep 3491909 = 654733) (by norm_num)
theorem B772177 : Blo 686314 772177 := bbase (se 2 (by rfl) ⟨289566, by rfl⟩ : syracuseStep 772177 = 579133) (by norm_num)
theorem B1034333 : Blo 686314 1034333 := bbase (se 3 (by rfl) ⟨193937, by rfl⟩ : syracuseStep 1034333 = 387875) (by norm_num)
theorem B772213 : Blo 686314 772213 := bbase (se 5 (by rfl) ⟨36197, by rfl⟩ : syracuseStep 772213 = 72395) (by norm_num)
theorem B870517 : Blo 686314 870517 := bbase (se 5 (by rfl) ⟨40805, by rfl⟩ : syracuseStep 870517 = 81611) (by norm_num)
theorem B1034357 : Blo 686314 1034357 := bbase (se 5 (by rfl) ⟨48485, by rfl⟩ : syracuseStep 1034357 = 96971) (by norm_num)
theorem B1656949 : Blo 686314 1656949 := bbase (se 5 (by rfl) ⟨77669, by rfl⟩ : syracuseStep 1656949 = 155339) (by norm_num)
theorem B1034381 : Blo 686314 1034381 := bbase (se 3 (by rfl) ⟨193946, by rfl⟩ : syracuseStep 1034381 = 387893) (by norm_num)
theorem B772249 : Blo 686314 772249 := bbase (se 2 (by rfl) ⟨289593, by rfl⟩ : syracuseStep 772249 = 579187) (by norm_num)
theorem B1034405 : Blo 686314 1034405 := bbase (se 4 (by rfl) ⟨96975, by rfl⟩ : syracuseStep 1034405 = 193951) (by norm_num)
theorem B772285 : Blo 686314 772285 := bbase (se 3 (by rfl) ⟨144803, by rfl⟩ : syracuseStep 772285 = 289607) (by norm_num)
theorem B1034429 : Blo 686314 1034429 := bbase (se 3 (by rfl) ⟨193955, by rfl⟩ : syracuseStep 1034429 = 387911) (by norm_num)
theorem B1034453 : Blo 686314 1034453 := bbase (se 7 (by rfl) ⟨12122, by rfl⟩ : syracuseStep 1034453 = 24245) (by norm_num)
theorem B772321 : Blo 686314 772321 := bbase (se 2 (by rfl) ⟨289620, by rfl⟩ : syracuseStep 772321 = 579241) (by norm_num)
theorem B1034477 : Blo 686314 1034477 := bbase (se 3 (by rfl) ⟨193964, by rfl⟩ : syracuseStep 1034477 = 387929) (by norm_num)
theorem B772357 : Blo 686314 772357 := bbase (se 4 (by rfl) ⟨72408, by rfl⟩ : syracuseStep 772357 = 144817) (by norm_num)
theorem B1034501 : Blo 686314 1034501 := bbase (se 4 (by rfl) ⟨96984, by rfl⟩ : syracuseStep 1034501 = 193969) (by norm_num)
theorem B1034525 : Blo 686314 1034525 := bbase (se 3 (by rfl) ⟨193973, by rfl⟩ : syracuseStep 1034525 = 387947) (by norm_num)
theorem B870689 : Blo 686314 870689 := bbase (se 2 (by rfl) ⟨326508, by rfl⟩ : syracuseStep 870689 = 653017) (by norm_num)
theorem B772393 : Blo 686314 772393 := bbase (se 2 (by rfl) ⟨289647, by rfl⟩ : syracuseStep 772393 = 579295) (by norm_num)
theorem B1034549 : Blo 686314 1034549 := bbase (se 5 (by rfl) ⟨48494, by rfl⟩ : syracuseStep 1034549 = 96989) (by norm_num)
theorem B772429 : Blo 686314 772429 := bbase (se 3 (by rfl) ⟨144830, by rfl⟩ : syracuseStep 772429 = 289661) (by norm_num)
theorem B1034573 : Blo 686314 1034573 := bbase (se 3 (by rfl) ⟨193982, by rfl⟩ : syracuseStep 1034573 = 387965) (by norm_num)
theorem B870745 : Blo 686314 870745 := bbase (se 2 (by rfl) ⟨326529, by rfl⟩ : syracuseStep 870745 = 653059) (by norm_num)
theorem B1034597 : Blo 686314 1034597 := bbase (se 4 (by rfl) ⟨96993, by rfl⟩ : syracuseStep 1034597 = 193987) (by norm_num)
theorem B772465 : Blo 686314 772465 := bbase (se 2 (by rfl) ⟨289674, by rfl⟩ : syracuseStep 772465 = 579349) (by norm_num)
theorem B1034621 : Blo 686314 1034621 := bbase (se 3 (by rfl) ⟨193991, by rfl⟩ : syracuseStep 1034621 = 387983) (by norm_num)
theorem B772501 : Blo 686314 772501 := bbase (se 6 (by rfl) ⟨18105, by rfl⟩ : syracuseStep 772501 = 36211) (by norm_num)
theorem B1034645 : Blo 686314 1034645 := bbase (se 6 (by rfl) ⟨24249, by rfl⟩ : syracuseStep 1034645 = 48499) (by norm_num)
theorem B1034669 : Blo 686314 1034669 := bbase (se 3 (by rfl) ⟨194000, by rfl⟩ : syracuseStep 1034669 = 388001) (by norm_num)
theorem B772537 : Blo 686314 772537 := bbase (se 2 (by rfl) ⟨289701, by rfl⟩ : syracuseStep 772537 = 579403) (by norm_num)
theorem B870841 : Blo 686314 870841 := bbase (se 2 (by rfl) ⟨326565, by rfl⟩ : syracuseStep 870841 = 653131) (by norm_num)
theorem B1034693 : Blo 686314 1034693 := bbase (se 4 (by rfl) ⟨97002, by rfl⟩ : syracuseStep 1034693 = 194005) (by norm_num)
theorem B707033 : Blo 686314 707033 := bbase (se 2 (by rfl) ⟨265137, by rfl⟩ : syracuseStep 707033 = 530275) (by norm_num)
theorem B772573 : Blo 686314 772573 := bbase (se 3 (by rfl) ⟨144857, by rfl⟩ : syracuseStep 772573 = 289715) (by norm_num)
theorem B1034717 : Blo 686314 1034717 := bbase (se 3 (by rfl) ⟨194009, by rfl⟩ : syracuseStep 1034717 = 388019) (by norm_num)
theorem B1395181 : Blo 686314 1395181 := bbase (se 3 (by rfl) ⟨261596, by rfl⟩ : syracuseStep 1395181 = 523193) (by norm_num)
theorem B1034741 : Blo 686314 1034741 := bbase (se 5 (by rfl) ⟨48503, by rfl⟩ : syracuseStep 1034741 = 97007) (by norm_num)
theorem B772609 : Blo 686314 772609 := bbase (se 2 (by rfl) ⟨289728, by rfl⟩ : syracuseStep 772609 = 579457) (by norm_num)
theorem B1034765 : Blo 686314 1034765 := bbase (se 3 (by rfl) ⟨194018, by rfl⟩ : syracuseStep 1034765 = 388037) (by norm_num)
theorem B772645 : Blo 686314 772645 := bbase (se 4 (by rfl) ⟨72435, by rfl⟩ : syracuseStep 772645 = 144871) (by norm_num)
theorem B1034789 : Blo 686314 1034789 := bbase (se 4 (by rfl) ⟨97011, by rfl⟩ : syracuseStep 1034789 = 194023) (by norm_num)
theorem B1395245 : Blo 686314 1395245 := bbase (se 3 (by rfl) ⟨261608, by rfl⟩ : syracuseStep 1395245 = 523217) (by norm_num)
theorem B2935349 : Blo 686314 2935349 := bbase (se 5 (by rfl) ⟨137594, by rfl⟩ : syracuseStep 2935349 = 275189) (by norm_num)
theorem B1034813 : Blo 686314 1034813 := bbase (se 3 (by rfl) ⟨194027, by rfl⟩ : syracuseStep 1034813 = 388055) (by norm_num)
theorem B772681 : Blo 686314 772681 := bbase (se 2 (by rfl) ⟨289755, by rfl⟩ : syracuseStep 772681 = 579511) (by norm_num)
theorem B1034837 : Blo 686314 1034837 := bbase (se 8 (by rfl) ⟨6063, by rfl⟩ : syracuseStep 1034837 = 12127) (by norm_num)
theorem B871013 : Blo 686314 871013 := bbase (se 4 (by rfl) ⟨81657, by rfl⟩ : syracuseStep 871013 = 163315) (by norm_num)
theorem B772717 : Blo 686314 772717 := bbase (se 3 (by rfl) ⟨144884, by rfl⟩ : syracuseStep 772717 = 289769) (by norm_num)
theorem B1034861 : Blo 686314 1034861 := bbase (se 3 (by rfl) ⟨194036, by rfl⟩ : syracuseStep 1034861 = 388073) (by norm_num)
theorem B1034885 : Blo 686314 1034885 := bbase (se 4 (by rfl) ⟨97020, by rfl⟩ : syracuseStep 1034885 = 194041) (by norm_num)
theorem B772753 : Blo 686314 772753 := bbase (se 2 (by rfl) ⟨289782, by rfl⟩ : syracuseStep 772753 = 579565) (by norm_num)
theorem B871069 : Blo 686314 871069 := bbase (se 3 (by rfl) ⟨163325, by rfl⟩ : syracuseStep 871069 = 326651) (by norm_num)
theorem B1034909 : Blo 686314 1034909 := bbase (se 3 (by rfl) ⟨194045, by rfl⟩ : syracuseStep 1034909 = 388091) (by norm_num)
theorem B772789 : Blo 686314 772789 := bbase (se 5 (by rfl) ⟨36224, by rfl⟩ : syracuseStep 772789 = 72449) (by norm_num)
theorem B1034933 : Blo 686314 1034933 := bbase (se 5 (by rfl) ⟨48512, by rfl⟩ : syracuseStep 1034933 = 97025) (by norm_num)
theorem B1034957 : Blo 686314 1034957 := bbase (se 3 (by rfl) ⟨194054, by rfl⟩ : syracuseStep 1034957 = 388109) (by norm_num)
theorem B772825 : Blo 686314 772825 := bbase (se 2 (by rfl) ⟨289809, by rfl⟩ : syracuseStep 772825 = 579619) (by norm_num)
theorem B1034981 : Blo 686314 1034981 := bbase (se 4 (by rfl) ⟨97029, by rfl⟩ : syracuseStep 1034981 = 194059) (by norm_num)
theorem B772861 : Blo 686314 772861 := bbase (se 3 (by rfl) ⟨144911, by rfl⟩ : syracuseStep 772861 = 289823) (by norm_num)
theorem B871165 : Blo 686314 871165 := bbase (se 3 (by rfl) ⟨163343, by rfl⟩ : syracuseStep 871165 = 326687) (by norm_num)
theorem B1035005 : Blo 686314 1035005 := bbase (se 3 (by rfl) ⟨194063, by rfl⟩ : syracuseStep 1035005 = 388127) (by norm_num)
theorem B1100557 : Blo 686314 1100557 := bbase (se 3 (by rfl) ⟨206354, by rfl⟩ : syracuseStep 1100557 = 412709) (by norm_num)
theorem B1657621 : Blo 686314 1657621 := bbase (se 6 (by rfl) ⟨38850, by rfl⟩ : syracuseStep 1657621 = 77701) (by norm_num)
theorem B1035029 : Blo 686314 1035029 := bbase (se 6 (by rfl) ⟨24258, by rfl⟩ : syracuseStep 1035029 = 48517) (by norm_num)
theorem B772897 : Blo 686314 772897 := bbase (se 2 (by rfl) ⟨289836, by rfl⟩ : syracuseStep 772897 = 579673) (by norm_num)
theorem B1035053 : Blo 686314 1035053 := bbase (se 3 (by rfl) ⟨194072, by rfl⟩ : syracuseStep 1035053 = 388145) (by norm_num)
theorem B772933 : Blo 686314 772933 := bbase (se 4 (by rfl) ⟨72462, by rfl⟩ : syracuseStep 772933 = 144925) (by norm_num)
theorem B1035077 : Blo 686314 1035077 := bbase (se 4 (by rfl) ⟨97038, by rfl⟩ : syracuseStep 1035077 = 194077) (by norm_num)
theorem B1035101 : Blo 686314 1035101 := bbase (se 3 (by rfl) ⟨194081, by rfl⟩ : syracuseStep 1035101 = 388163) (by norm_num)
theorem B772969 : Blo 686314 772969 := bbase (se 2 (by rfl) ⟨289863, by rfl⟩ : syracuseStep 772969 = 579727) (by norm_num)
theorem B1035125 : Blo 686314 1035125 := bbase (se 5 (by rfl) ⟨48521, by rfl⟩ : syracuseStep 1035125 = 97043) (by norm_num)
theorem B3230597 : Blo 686314 3230597 := bbase (se 4 (by rfl) ⟨302868, by rfl⟩ : syracuseStep 3230597 = 605737) (by norm_num)
theorem B773005 : Blo 686314 773005 := bbase (se 3 (by rfl) ⟨144938, by rfl⟩ : syracuseStep 773005 = 289877) (by norm_num)
theorem B1035149 : Blo 686314 1035149 := bbase (se 3 (by rfl) ⟨194090, by rfl⟩ : syracuseStep 1035149 = 388181) (by norm_num)
theorem B1035173 : Blo 686314 1035173 := bbase (se 4 (by rfl) ⟨97047, by rfl⟩ : syracuseStep 1035173 = 194095) (by norm_num)
theorem B871337 : Blo 686314 871337 := bbase (se 2 (by rfl) ⟨326751, by rfl⟩ : syracuseStep 871337 = 653503) (by norm_num)
theorem B773041 : Blo 686314 773041 := bbase (se 2 (by rfl) ⟨289890, by rfl⟩ : syracuseStep 773041 = 579781) (by norm_num)
theorem B1035197 : Blo 686314 1035197 := bbase (se 3 (by rfl) ⟨194099, by rfl⟩ : syracuseStep 1035197 = 388199) (by norm_num)
theorem B773077 : Blo 686314 773077 := bbase (se 7 (by rfl) ⟨9059, by rfl⟩ : syracuseStep 773077 = 18119) (by norm_num)
theorem B1035221 : Blo 686314 1035221 := bbase (se 7 (by rfl) ⟨12131, by rfl⟩ : syracuseStep 1035221 = 24263) (by norm_num)
theorem B871393 : Blo 686314 871393 := bbase (se 2 (by rfl) ⟨326772, by rfl⟩ : syracuseStep 871393 = 653545) (by norm_num)
theorem B1035245 : Blo 686314 1035245 := bbase (se 3 (by rfl) ⟨194108, by rfl⟩ : syracuseStep 1035245 = 388217) (by norm_num)
theorem B773113 : Blo 686314 773113 := bbase (se 2 (by rfl) ⟨289917, by rfl⟩ : syracuseStep 773113 = 579835) (by norm_num)
theorem B1657853 : Blo 686314 1657853 := bbase (se 3 (by rfl) ⟨310847, by rfl⟩ : syracuseStep 1657853 = 621695) (by norm_num)
theorem B1035269 : Blo 686314 1035269 := bbase (se 4 (by rfl) ⟨97056, by rfl⟩ : syracuseStep 1035269 = 194113) (by norm_num)
theorem B773149 : Blo 686314 773149 := bbase (se 3 (by rfl) ⟨144965, by rfl⟩ : syracuseStep 773149 = 289931) (by norm_num)
theorem B1035293 : Blo 686314 1035293 := bbase (se 3 (by rfl) ⟨194117, by rfl⟩ : syracuseStep 1035293 = 388235) (by norm_num)
theorem B1657901 : Blo 686314 1657901 := bbase (se 3 (by rfl) ⟨310856, by rfl⟩ : syracuseStep 1657901 = 621713) (by norm_num)
theorem B1035317 : Blo 686314 1035317 := bbase (se 5 (by rfl) ⟨48530, by rfl⟩ : syracuseStep 1035317 = 97061) (by norm_num)
theorem B773185 : Blo 686314 773185 := bbase (se 2 (by rfl) ⟨289944, by rfl⟩ : syracuseStep 773185 = 579889) (by norm_num)
theorem B871489 : Blo 686314 871489 := bbase (se 2 (by rfl) ⟨326808, by rfl⟩ : syracuseStep 871489 = 653617) (by norm_num)
theorem B1035341 : Blo 686314 1035341 := bbase (se 3 (by rfl) ⟨194126, by rfl⟩ : syracuseStep 1035341 = 388253) (by norm_num)
theorem B773221 : Blo 686314 773221 := bbase (se 4 (by rfl) ⟨72489, by rfl⟩ : syracuseStep 773221 = 144979) (by norm_num)
theorem B1035365 : Blo 686314 1035365 := bbase (se 4 (by rfl) ⟨97065, by rfl⟩ : syracuseStep 1035365 = 194131) (by norm_num)
theorem B3132533 : Blo 686314 3132533 := bbase (se 5 (by rfl) ⟨146837, by rfl⟩ : syracuseStep 3132533 = 293675) (by norm_num)
theorem B1035389 : Blo 686314 1035389 := bbase (se 3 (by rfl) ⟨194135, by rfl⟩ : syracuseStep 1035389 = 388271) (by norm_num)
theorem B773257 : Blo 686314 773257 := bbase (se 2 (by rfl) ⟨289971, by rfl⟩ : syracuseStep 773257 = 579943) (by norm_num)
theorem B1035413 : Blo 686314 1035413 := bbase (se 6 (by rfl) ⟨24267, by rfl⟩ : syracuseStep 1035413 = 48535) (by norm_num)
theorem B773293 : Blo 686314 773293 := bbase (se 3 (by rfl) ⟨144992, by rfl⟩ : syracuseStep 773293 = 289985) (by norm_num)
theorem B1035437 : Blo 686314 1035437 := bbase (se 3 (by rfl) ⟨194144, by rfl⟩ : syracuseStep 1035437 = 388289) (by norm_num)
theorem B1035461 : Blo 686314 1035461 := bbase (se 4 (by rfl) ⟨97074, by rfl⟩ : syracuseStep 1035461 = 194149) (by norm_num)
theorem B773329 : Blo 686314 773329 := bbase (se 2 (by rfl) ⟨289998, by rfl⟩ : syracuseStep 773329 = 579997) (by norm_num)
theorem B871661 : Blo 686314 871661 := bbase (se 3 (by rfl) ⟨163436, by rfl⟩ : syracuseStep 871661 = 326873) (by norm_num)
theorem B773365 : Blo 686314 773365 := bbase (se 5 (by rfl) ⟨36251, by rfl⟩ : syracuseStep 773365 = 72503) (by norm_num)
theorem B5229845 : Blo 686314 5229845 := bbase (se 6 (by rfl) ⟨122574, by rfl⟩ : syracuseStep 5229845 = 245149) (by norm_num)
theorem B773401 : Blo 686314 773401 := bbase (se 2 (by rfl) ⟨290025, by rfl⟩ : syracuseStep 773401 = 580051) (by norm_num)
theorem B871717 : Blo 686314 871717 := bbase (se 4 (by rfl) ⟨81723, by rfl⟩ : syracuseStep 871717 = 163447) (by norm_num)
theorem B773437 : Blo 686314 773437 := bbase (se 3 (by rfl) ⟨145019, by rfl⟩ : syracuseStep 773437 = 290039) (by norm_num)
theorem B2608469 : Blo 686314 2608469 := bbase (se 11 (by rfl) ⟨1910, by rfl⟩ : syracuseStep 2608469 = 3821) (by norm_num)
theorem B3493205 : Blo 686314 3493205 := bbase (se 11 (by rfl) ⟨2558, by rfl⟩ : syracuseStep 3493205 = 5117) (by norm_num)
theorem B773473 : Blo 686314 773473 := bbase (se 2 (by rfl) ⟨290052, by rfl⟩ : syracuseStep 773473 = 580105) (by norm_num)
theorem B773509 : Blo 686314 773509 := bbase (se 4 (by rfl) ⟨72516, by rfl⟩ : syracuseStep 773509 = 145033) (by norm_num)
theorem B871813 : Blo 686314 871813 := bbase (se 4 (by rfl) ⟨81732, by rfl⟩ : syracuseStep 871813 = 163465) (by norm_num)
theorem B773545 : Blo 686314 773545 := bbase (se 2 (by rfl) ⟨290079, by rfl⟩ : syracuseStep 773545 = 580159) (by norm_num)
theorem B773581 : Blo 686314 773581 := bbase (se 3 (by rfl) ⟨145046, by rfl⟩ : syracuseStep 773581 = 290093) (by norm_num)
theorem B1101269 : Blo 686314 1101269 := bbase (se 7 (by rfl) ⟨12905, by rfl⟩ : syracuseStep 1101269 = 25811) (by norm_num)
theorem B773617 : Blo 686314 773617 := bbase (se 2 (by rfl) ⟨290106, by rfl⟩ : syracuseStep 773617 = 580213) (by norm_num)
theorem B773653 : Blo 686314 773653 := bbase (se 6 (by rfl) ⟨18132, by rfl⟩ : syracuseStep 773653 = 36265) (by norm_num)
theorem B2936357 : Blo 686314 2936357 := bbase (se 4 (by rfl) ⟨275283, by rfl⟩ : syracuseStep 2936357 = 550567) (by norm_num)
theorem B871985 : Blo 686314 871985 := bbase (se 2 (by rfl) ⟨326994, by rfl⟩ : syracuseStep 871985 = 653989) (by norm_num)
theorem B773689 : Blo 686314 773689 := bbase (se 2 (by rfl) ⟨290133, by rfl⟩ : syracuseStep 773689 = 580267) (by norm_num)
theorem B773725 : Blo 686314 773725 := bbase (se 3 (by rfl) ⟨145073, by rfl⟩ : syracuseStep 773725 = 290147) (by norm_num)
theorem B872041 : Blo 686314 872041 := bbase (se 2 (by rfl) ⟨327015, by rfl⟩ : syracuseStep 872041 = 654031) (by norm_num)
theorem B2608757 : Blo 686314 2608757 := bbase (se 5 (by rfl) ⟨122285, by rfl⟩ : syracuseStep 2608757 = 244571) (by norm_num)
theorem B773761 : Blo 686314 773761 := bbase (se 2 (by rfl) ⟨290160, by rfl⟩ : syracuseStep 773761 = 580321) (by norm_num)
theorem B773797 : Blo 686314 773797 := bbase (se 4 (by rfl) ⟨72543, by rfl⟩ : syracuseStep 773797 = 145087) (by norm_num)
theorem B1855157 : Blo 686314 1855157 := bbase (se 5 (by rfl) ⟨86960, by rfl⟩ : syracuseStep 1855157 = 173921) (by norm_num)
theorem B773833 : Blo 686314 773833 := bbase (se 2 (by rfl) ⟨290187, by rfl⟩ : syracuseStep 773833 = 580375) (by norm_num)
theorem B872137 : Blo 686314 872137 := bbase (se 2 (by rfl) ⟨327051, by rfl⟩ : syracuseStep 872137 = 654103) (by norm_num)
theorem B773869 : Blo 686314 773869 := bbase (se 3 (by rfl) ⟨145100, by rfl⟩ : syracuseStep 773869 = 290201) (by norm_num)
theorem B773905 : Blo 686314 773905 := bbase (se 2 (by rfl) ⟨290214, by rfl⟩ : syracuseStep 773905 = 580429) (by norm_num)
theorem B773941 : Blo 686314 773941 := bbase (se 5 (by rfl) ⟨36278, by rfl⟩ : syracuseStep 773941 = 72557) (by norm_num)
theorem B839497 : Blo 686314 839497 := bbase (se 2 (by rfl) ⟨314811, by rfl⟩ : syracuseStep 839497 = 629623) (by norm_num)
theorem B773977 : Blo 686314 773977 := bbase (se 2 (by rfl) ⟨290241, by rfl⟩ : syracuseStep 773977 = 580483) (by norm_num)
theorem B872309 : Blo 686314 872309 := bbase (se 5 (by rfl) ⟨40889, by rfl⟩ : syracuseStep 872309 = 81779) (by norm_num)
theorem B774013 : Blo 686314 774013 := bbase (se 3 (by rfl) ⟨145127, by rfl⟩ : syracuseStep 774013 = 290255) (by norm_num)
theorem B774049 : Blo 686314 774049 := bbase (se 2 (by rfl) ⟨290268, by rfl⟩ : syracuseStep 774049 = 580537) (by norm_num)
theorem B872365 : Blo 686314 872365 := bbase (se 3 (by rfl) ⟨163568, by rfl⟩ : syracuseStep 872365 = 327137) (by norm_num)
theorem B774085 : Blo 686314 774085 := bbase (se 4 (by rfl) ⟨72570, by rfl⟩ : syracuseStep 774085 = 145141) (by norm_num)
theorem B774121 : Blo 686314 774121 := bbase (se 2 (by rfl) ⟨290295, by rfl⟩ : syracuseStep 774121 = 580591) (by norm_num)
theorem B970741 : Blo 686314 970741 := bbase (se 5 (by rfl) ⟨45503, by rfl⟩ : syracuseStep 970741 = 91007) (by norm_num)
theorem B774157 : Blo 686314 774157 := bbase (se 3 (by rfl) ⟨145154, by rfl⟩ : syracuseStep 774157 = 290309) (by norm_num)
theorem B872461 : Blo 686314 872461 := bbase (se 3 (by rfl) ⟨163586, by rfl⟩ : syracuseStep 872461 = 327173) (by norm_num)
theorem B774193 : Blo 686314 774193 := bbase (se 2 (by rfl) ⟨290322, by rfl⟩ : syracuseStep 774193 = 580645) (by norm_num)
theorem B774229 : Blo 686314 774229 := bbase (se 8 (by rfl) ⟨4536, by rfl⟩ : syracuseStep 774229 = 9073) (by norm_num)
theorem B1101941 : Blo 686314 1101941 := bbase (se 5 (by rfl) ⟨51653, by rfl⟩ : syracuseStep 1101941 = 103307) (by norm_num)
theorem B774265 : Blo 686314 774265 := bbase (se 2 (by rfl) ⟨290349, by rfl⟩ : syracuseStep 774265 = 580699) (by norm_num)
theorem B774301 : Blo 686314 774301 := bbase (se 3 (by rfl) ⟨145181, by rfl⟩ : syracuseStep 774301 = 290363) (by norm_num)
theorem B872633 : Blo 686314 872633 := bbase (se 2 (by rfl) ⟨327237, by rfl⟩ : syracuseStep 872633 = 654475) (by norm_num)
theorem B774337 : Blo 686314 774337 := bbase (se 2 (by rfl) ⟨290376, by rfl⟩ : syracuseStep 774337 = 580753) (by norm_num)
theorem B774373 : Blo 686314 774373 := bbase (se 4 (by rfl) ⟨72597, by rfl⟩ : syracuseStep 774373 = 145195) (by norm_num)
theorem B872689 : Blo 686314 872689 := bbase (se 2 (by rfl) ⟨327258, by rfl⟩ : syracuseStep 872689 = 654517) (by norm_num)
theorem B774409 : Blo 686314 774409 := bbase (se 2 (by rfl) ⟨290403, by rfl⟩ : syracuseStep 774409 = 580807) (by norm_num)
theorem B774445 : Blo 686314 774445 := bbase (se 3 (by rfl) ⟨145208, by rfl⟩ : syracuseStep 774445 = 290417) (by norm_num)
theorem B1397045 : Blo 686314 1397045 := bbase (se 5 (by rfl) ⟨65486, by rfl⟩ : syracuseStep 1397045 = 130973) (by norm_num)
theorem B774481 : Blo 686314 774481 := bbase (se 2 (by rfl) ⟨290430, by rfl⟩ : syracuseStep 774481 = 580861) (by norm_num)
theorem B872785 : Blo 686314 872785 := bbase (se 2 (by rfl) ⟨327294, by rfl⟩ : syracuseStep 872785 = 654589) (by norm_num)
theorem B774517 : Blo 686314 774517 := bbase (se 5 (by rfl) ⟨36305, by rfl⟩ : syracuseStep 774517 = 72611) (by norm_num)
theorem B774553 : Blo 686314 774553 := bbase (se 2 (by rfl) ⟨290457, by rfl⟩ : syracuseStep 774553 = 580915) (by norm_num)
theorem B774589 : Blo 686314 774589 := bbase (se 3 (by rfl) ⟨145235, by rfl⟩ : syracuseStep 774589 = 290471) (by norm_num)
theorem B774625 : Blo 686314 774625 := bbase (se 2 (by rfl) ⟨290484, by rfl⟩ : syracuseStep 774625 = 580969) (by norm_num)
theorem B872957 : Blo 686314 872957 := bbase (se 3 (by rfl) ⟨163679, by rfl⟩ : syracuseStep 872957 = 327359) (by norm_num)
theorem B774661 : Blo 686314 774661 := bbase (se 4 (by rfl) ⟨72624, by rfl⟩ : syracuseStep 774661 = 145249) (by norm_num)
theorem B774697 : Blo 686314 774697 := bbase (se 2 (by rfl) ⟨290511, by rfl⟩ : syracuseStep 774697 = 581023) (by norm_num)
theorem B3527221 : Blo 686314 3527221 := bbase (se 5 (by rfl) ⟨165338, by rfl⟩ : syracuseStep 3527221 = 330677) (by norm_num)
theorem B873013 : Blo 686314 873013 := bbase (se 5 (by rfl) ⟨40922, by rfl⟩ : syracuseStep 873013 = 81845) (by norm_num)
theorem B774733 : Blo 686314 774733 := bbase (se 3 (by rfl) ⟨145262, by rfl⟩ : syracuseStep 774733 = 290525) (by norm_num)
theorem B3494501 : Blo 686314 3494501 := bbase (se 4 (by rfl) ⟨327609, by rfl⟩ : syracuseStep 3494501 = 655219) (by norm_num)
theorem B774769 : Blo 686314 774769 := bbase (se 2 (by rfl) ⟨290538, by rfl⟩ : syracuseStep 774769 = 581077) (by norm_num)
theorem B1102453 : Blo 686314 1102453 := bbase (se 5 (by rfl) ⟨51677, by rfl⟩ : syracuseStep 1102453 = 103355) (by norm_num)
theorem B774805 : Blo 686314 774805 := bbase (se 6 (by rfl) ⟨18159, by rfl⟩ : syracuseStep 774805 = 36319) (by norm_num)
theorem B873109 : Blo 686314 873109 := bbase (se 6 (by rfl) ⟨20463, by rfl⟩ : syracuseStep 873109 = 40927) (by norm_num)
theorem B774841 : Blo 686314 774841 := bbase (se 2 (by rfl) ⟨290565, by rfl⟩ : syracuseStep 774841 = 581131) (by norm_num)
theorem B7951061 : Blo 686314 7951061 := bbase (se 7 (by rfl) ⟨93176, by rfl⟩ : syracuseStep 7951061 = 186353) (by norm_num)
theorem B9425621 : Blo 686314 9425621 := bbase (se 7 (by rfl) ⟨110456, by rfl⟩ : syracuseStep 9425621 = 220913) (by norm_num)
theorem B774877 : Blo 686314 774877 := bbase (se 3 (by rfl) ⟨145289, by rfl⟩ : syracuseStep 774877 = 290579) (by norm_num)
theorem B774913 : Blo 686314 774913 := bbase (se 2 (by rfl) ⟨290592, by rfl⟩ : syracuseStep 774913 = 581185) (by norm_num)
theorem B2609941 : Blo 686314 2609941 := bbase (se 6 (by rfl) ⟨61170, by rfl⟩ : syracuseStep 2609941 = 122341) (by norm_num)
theorem B774949 : Blo 686314 774949 := bbase (se 4 (by rfl) ⟨72651, by rfl⟩ : syracuseStep 774949 = 145303) (by norm_num)
theorem B873281 : Blo 686314 873281 := bbase (se 2 (by rfl) ⟨327480, by rfl⟩ : syracuseStep 873281 = 654961) (by norm_num)
theorem B3298117 : Blo 686314 3298117 := bbase (se 4 (by rfl) ⟨309198, by rfl⟩ : syracuseStep 3298117 = 618397) (by norm_num)
theorem B774985 : Blo 686314 774985 := bbase (se 2 (by rfl) ⟨290619, by rfl⟩ : syracuseStep 774985 = 581239) (by norm_num)
theorem B3298133 : Blo 686314 3298133 := bbase (se 9 (by rfl) ⟨9662, by rfl⟩ : syracuseStep 3298133 = 19325) (by norm_num)
theorem B775021 : Blo 686314 775021 := bbase (se 3 (by rfl) ⟨145316, by rfl⟩ : syracuseStep 775021 = 290633) (by norm_num)
theorem B873337 : Blo 686314 873337 := bbase (se 2 (by rfl) ⟨327501, by rfl⟩ : syracuseStep 873337 = 655003) (by norm_num)
theorem B775057 : Blo 686314 775057 := bbase (se 2 (by rfl) ⟨290646, by rfl⟩ : syracuseStep 775057 = 581293) (by norm_num)
theorem B775093 : Blo 686314 775093 := bbase (se 5 (by rfl) ⟨36332, by rfl⟩ : syracuseStep 775093 = 72665) (by norm_num)
theorem B775129 : Blo 686314 775129 := bbase (se 2 (by rfl) ⟨290673, by rfl⟩ : syracuseStep 775129 = 581347) (by norm_num)
theorem B873433 : Blo 686314 873433 := bbase (se 2 (by rfl) ⟨327537, by rfl⟩ : syracuseStep 873433 = 655075) (by norm_num)
theorem B775165 : Blo 686314 775165 := bbase (se 3 (by rfl) ⟨145343, by rfl⟩ : syracuseStep 775165 = 290687) (by norm_num)
theorem B775201 : Blo 686314 775201 := bbase (se 2 (by rfl) ⟨290700, by rfl⟩ : syracuseStep 775201 = 581401) (by norm_num)
theorem B1102909 : Blo 686314 1102909 := bbase (se 3 (by rfl) ⟨206795, by rfl⟩ : syracuseStep 1102909 = 413591) (by norm_num)
theorem B2610245 : Blo 686314 2610245 := bbase (se 4 (by rfl) ⟨244710, by rfl⟩ : syracuseStep 2610245 = 489421) (by norm_num)
theorem B775237 : Blo 686314 775237 := bbase (se 4 (by rfl) ⟨72678, by rfl⟩ : syracuseStep 775237 = 145357) (by norm_num)
theorem B775273 : Blo 686314 775273 := bbase (se 2 (by rfl) ⟨290727, by rfl⟩ : syracuseStep 775273 = 581455) (by norm_num)
theorem B873605 : Blo 686314 873605 := bbase (se 4 (by rfl) ⟨81900, by rfl⟩ : syracuseStep 873605 = 163801) (by norm_num)
theorem B775309 : Blo 686314 775309 := bbase (se 3 (by rfl) ⟨145370, by rfl⟩ : syracuseStep 775309 = 290741) (by norm_num)
theorem B3134629 : Blo 686314 3134629 := bbase (se 4 (by rfl) ⟨293871, by rfl⟩ : syracuseStep 3134629 = 587743) (by norm_num)
theorem B775345 : Blo 686314 775345 := bbase (se 2 (by rfl) ⟨290754, by rfl⟩ : syracuseStep 775345 = 581509) (by norm_num)
theorem B873661 : Blo 686314 873661 := bbase (se 3 (by rfl) ⟨163811, by rfl⟩ : syracuseStep 873661 = 327623) (by norm_num)
theorem B4183253 : Blo 686314 4183253 := bbase (se 7 (by rfl) ⟨49022, by rfl⟩ : syracuseStep 4183253 = 98045) (by norm_num)
theorem B775381 : Blo 686314 775381 := bbase (se 7 (by rfl) ⟨9086, by rfl⟩ : syracuseStep 775381 = 18173) (by norm_num)
theorem B775417 : Blo 686314 775417 := bbase (se 2 (by rfl) ⟨290781, by rfl⟩ : syracuseStep 775417 = 581563) (by norm_num)
theorem B2938133 : Blo 686314 2938133 := bbase (se 6 (by rfl) ⟨68862, by rfl⟩ : syracuseStep 2938133 = 137725) (by norm_num)
theorem B775453 : Blo 686314 775453 := bbase (se 3 (by rfl) ⟨145397, by rfl⟩ : syracuseStep 775453 = 290795) (by norm_num)
theorem B775489 : Blo 686314 775489 := bbase (se 2 (by rfl) ⟨290808, by rfl⟩ : syracuseStep 775489 = 581617) (by norm_num)
theorem B775525 : Blo 686314 775525 := bbase (se 4 (by rfl) ⟨72705, by rfl⟩ : syracuseStep 775525 = 145411) (by norm_num)
theorem B775561 : Blo 686314 775561 := bbase (se 2 (by rfl) ⟨290835, by rfl⟩ : syracuseStep 775561 = 581671) (by norm_num)
theorem B775597 : Blo 686314 775597 := bbase (se 3 (by rfl) ⟨145424, by rfl⟩ : syracuseStep 775597 = 290849) (by norm_num)
theorem B1955269 : Blo 686314 1955269 := bbase (se 4 (by rfl) ⟨183306, by rfl⟩ : syracuseStep 1955269 = 366613) (by norm_num)
theorem B775633 : Blo 686314 775633 := bbase (se 2 (by rfl) ⟨290862, by rfl⟩ : syracuseStep 775633 = 581725) (by norm_num)
theorem B775669 : Blo 686314 775669 := bbase (se 5 (by rfl) ⟨36359, by rfl⟩ : syracuseStep 775669 = 72719) (by norm_num)
theorem B775705 : Blo 686314 775705 := bbase (se 2 (by rfl) ⟨290889, by rfl⟩ : syracuseStep 775705 = 581779) (by norm_num)
theorem B775741 : Blo 686314 775741 := bbase (se 3 (by rfl) ⟨145451, by rfl⟩ : syracuseStep 775741 = 290903) (by norm_num)
theorem B775777 : Blo 686314 775777 := bbase (se 2 (by rfl) ⟨290916, by rfl⟩ : syracuseStep 775777 = 581833) (by norm_num)
theorem B775813 : Blo 686314 775813 := bbase (se 4 (by rfl) ⟨72732, by rfl⟩ : syracuseStep 775813 = 145465) (by norm_num)
theorem B775849 : Blo 686314 775849 := bbase (se 2 (by rfl) ⟨290943, by rfl⟩ : syracuseStep 775849 = 581887) (by norm_num)
theorem B775885 : Blo 686314 775885 := bbase (se 3 (by rfl) ⟨145478, by rfl⟩ : syracuseStep 775885 = 290957) (by norm_num)
theorem B1103581 : Blo 686314 1103581 := bbase (se 3 (by rfl) ⟨206921, by rfl⟩ : syracuseStep 1103581 = 413843) (by norm_num)
theorem B775921 : Blo 686314 775921 := bbase (se 2 (by rfl) ⟨290970, by rfl⟩ : syracuseStep 775921 = 581941) (by norm_num)
theorem B1857269 : Blo 686314 1857269 := bbase (se 5 (by rfl) ⟨87059, by rfl⟩ : syracuseStep 1857269 = 174119) (by norm_num)
theorem B775957 : Blo 686314 775957 := bbase (se 6 (by rfl) ⟨18186, by rfl⟩ : syracuseStep 775957 = 36373) (by norm_num)
theorem B775993 : Blo 686314 775993 := bbase (se 2 (by rfl) ⟨290997, by rfl⟩ : syracuseStep 775993 = 581995) (by norm_num)
theorem B776029 : Blo 686314 776029 := bbase (se 3 (by rfl) ⟨145505, by rfl⟩ : syracuseStep 776029 = 291011) (by norm_num)
theorem B776065 : Blo 686314 776065 := bbase (se 2 (by rfl) ⟨291024, by rfl⟩ : syracuseStep 776065 = 582049) (by norm_num)
theorem B2381717 : Blo 686314 2381717 := bbase (se 6 (by rfl) ⟨55821, by rfl⟩ : syracuseStep 2381717 = 111643) (by norm_num)
theorem B776101 : Blo 686314 776101 := bbase (se 4 (by rfl) ⟨72759, by rfl⟩ : syracuseStep 776101 = 145519) (by norm_num)
theorem B776137 : Blo 686314 776137 := bbase (se 2 (by rfl) ⟨291051, by rfl⟩ : syracuseStep 776137 = 582103) (by norm_num)
theorem B776173 : Blo 686314 776173 := bbase (se 3 (by rfl) ⟨145532, by rfl⟩ : syracuseStep 776173 = 291065) (by norm_num)
theorem B776209 : Blo 686314 776209 := bbase (se 2 (by rfl) ⟨291078, by rfl⟩ : syracuseStep 776209 = 582157) (by norm_num)
theorem B776245 : Blo 686314 776245 := bbase (se 5 (by rfl) ⟨36386, by rfl⟩ : syracuseStep 776245 = 72773) (by norm_num)
theorem B776281 : Blo 686314 776281 := bbase (se 2 (by rfl) ⟨291105, by rfl⟩ : syracuseStep 776281 = 582211) (by norm_num)
theorem B1398877 : Blo 686314 1398877 := bbase (se 3 (by rfl) ⟨262289, by rfl⟩ : syracuseStep 1398877 = 524579) (by norm_num)
theorem B776317 : Blo 686314 776317 := bbase (se 3 (by rfl) ⟨145559, by rfl⟩ : syracuseStep 776317 = 291119) (by norm_num)
theorem B1104005 : Blo 686314 1104005 := bbase (se 4 (by rfl) ⟨103500, by rfl⟩ : syracuseStep 1104005 = 207001) (by norm_num)
theorem B2316437 : Blo 686314 2316437 := bbase (se 6 (by rfl) ⟨54291, by rfl⟩ : syracuseStep 2316437 = 108583) (by norm_num)
theorem B776353 : Blo 686314 776353 := bbase (se 2 (by rfl) ⟨291132, by rfl⟩ : syracuseStep 776353 = 582265) (by norm_num)
theorem B776389 : Blo 686314 776389 := bbase (se 4 (by rfl) ⟨72786, by rfl⟩ : syracuseStep 776389 = 145573) (by norm_num)
theorem B776425 : Blo 686314 776425 := bbase (se 2 (by rfl) ⟨291159, by rfl⟩ : syracuseStep 776425 = 582319) (by norm_num)
theorem B776461 : Blo 686314 776461 := bbase (se 3 (by rfl) ⟨145586, by rfl⟩ : syracuseStep 776461 = 291173) (by norm_num)
theorem B776497 : Blo 686314 776497 := bbase (se 2 (by rfl) ⟨291186, by rfl⟩ : syracuseStep 776497 = 582373) (by norm_num)
theorem B776533 : Blo 686314 776533 := bbase (se 10 (by rfl) ⟨1137, by rfl⟩ : syracuseStep 776533 = 2275) (by norm_num)
theorem B776569 : Blo 686314 776569 := bbase (se 2 (by rfl) ⟨291213, by rfl⟩ : syracuseStep 776569 = 582427) (by norm_num)
theorem B1857925 : Blo 686314 1857925 := bbase (se 4 (by rfl) ⟨174180, by rfl⟩ : syracuseStep 1857925 = 348361) (by norm_num)
theorem B1104293 : Blo 686314 1104293 := bbase (se 4 (by rfl) ⟨103527, by rfl⟩ : syracuseStep 1104293 = 207055) (by norm_num)
theorem B2316869 : Blo 686314 2316869 := bbase (se 4 (by rfl) ⟨217206, by rfl⟩ : syracuseStep 2316869 = 434413) (by norm_num)
theorem B1399373 : Blo 686314 1399373 := bbase (se 3 (by rfl) ⟨262382, by rfl⟩ : syracuseStep 1399373 = 524765) (by norm_num)
theorem B1399445 : Blo 686314 1399445 := bbase (se 6 (by rfl) ⟨32799, by rfl⟩ : syracuseStep 1399445 = 65599) (by norm_num)
theorem B3922613 : Blo 686314 3922613 := bbase (se 5 (by rfl) ⟨183872, by rfl⟩ : syracuseStep 3922613 = 367745) (by norm_num)
theorem B1956773 : Blo 686314 1956773 := bbase (se 4 (by rfl) ⟨183447, by rfl⟩ : syracuseStep 1956773 = 366895) (by norm_num)
theorem B940997 : Blo 686314 940997 := bbase (se 4 (by rfl) ⟨88218, by rfl⟩ : syracuseStep 940997 = 176437) (by norm_num)
theorem B4709333 : Blo 686314 4709333 := bbase (se 7 (by rfl) ⟨55187, by rfl⟩ : syracuseStep 4709333 = 110375) (by norm_num)
theorem B2317301 : Blo 686314 2317301 := bbase (se 5 (by rfl) ⟨108623, by rfl⟩ : syracuseStep 2317301 = 217247) (by norm_num)
theorem B2612357 : Blo 686314 2612357 := bbase (se 4 (by rfl) ⟨244908, by rfl⟩ : syracuseStep 2612357 = 489817) (by norm_num)
theorem B3300517 : Blo 686314 3300517 := bbase (se 4 (by rfl) ⟨309423, by rfl⟩ : syracuseStep 3300517 = 618847) (by norm_num)
theorem B1105093 : Blo 686314 1105093 := bbase (se 4 (by rfl) ⟨103602, by rfl⟩ : syracuseStep 1105093 = 207205) (by norm_num)
theorem B25058645 : Blo 686314 25058645 := bbase (se 11 (by rfl) ⟨18353, by rfl⟩ : syracuseStep 25058645 = 36707) (by norm_num)
theorem B2317733 : Blo 686314 2317733 := bbase (se 4 (by rfl) ⟨217287, by rfl⟩ : syracuseStep 2317733 = 434575) (by norm_num)
theorem B2612645 : Blo 686314 2612645 := bbase (se 4 (by rfl) ⟨244935, by rfl⟩ : syracuseStep 2612645 = 489871) (by norm_num)
theorem B1859093 : Blo 686314 1859093 := bbase (se 6 (by rfl) ⟨43572, by rfl⟩ : syracuseStep 1859093 = 87145) (by norm_num)
theorem B1105645 : Blo 686314 1105645 := bbase (se 3 (by rfl) ⟨207308, by rfl⟩ : syracuseStep 1105645 = 414617) (by norm_num)
theorem B745249 : Blo 686314 745249 := bbase (se 2 (by rfl) ⟨279468, by rfl⟩ : syracuseStep 745249 = 558937) (by norm_num)
theorem B2318165 : Blo 686314 2318165 := bbase (se 9 (by rfl) ⟨6791, by rfl⟩ : syracuseStep 2318165 = 13583) (by norm_num)
theorem B1466333 : Blo 686314 1466333 := bbase (se 3 (by rfl) ⟨274937, by rfl⟩ : syracuseStep 1466333 = 549875) (by norm_num)
theorem B745513 : Blo 686314 745513 := bbase (se 2 (by rfl) ⟨279567, by rfl⟩ : syracuseStep 745513 = 559135) (by norm_num)
theorem B1466581 : Blo 686314 1466581 := bbase (se 7 (by rfl) ⟨17186, by rfl⟩ : syracuseStep 1466581 = 34373) (by norm_num)
theorem B2318597 : Blo 686314 2318597 := bbase (se 4 (by rfl) ⟨217368, by rfl⟩ : syracuseStep 2318597 = 434737) (by norm_num)
theorem B1237349 : Blo 686314 1237349 := bbase (se 4 (by rfl) ⟨116001, by rfl⟩ : syracuseStep 1237349 = 232003) (by norm_num)
theorem B1958357 : Blo 686314 1958357 := bbase (se 7 (by rfl) ⟨22949, by rfl⟩ : syracuseStep 1958357 = 45899) (by norm_num)
theorem B2482741 : Blo 686314 2482741 := bbase (se 5 (by rfl) ⟨116378, by rfl⟩ : syracuseStep 2482741 = 232757) (by norm_num)
theorem B1237565 : Blo 686314 1237565 := bbase (se 3 (by rfl) ⟨232043, by rfl⟩ : syracuseStep 1237565 = 464087) (by norm_num)
theorem B2613829 : Blo 686314 2613829 := bbase (se 4 (by rfl) ⟨245046, by rfl⟩ : syracuseStep 2613829 = 490093) (by norm_num)
theorem B1303141 : Blo 686314 1303141 := bbase (se 4 (by rfl) ⟨122169, by rfl⟩ : syracuseStep 1303141 = 244339) (by norm_num)
theorem B1237637 : Blo 686314 1237637 := bbase (se 4 (by rfl) ⟨116028, by rfl⟩ : syracuseStep 1237637 = 232057) (by norm_num)
theorem B2319029 : Blo 686314 2319029 := bbase (se 5 (by rfl) ⟨108704, by rfl⟩ : syracuseStep 2319029 = 217409) (by norm_num)
theorem B1467085 : Blo 686314 1467085 := bbase (se 3 (by rfl) ⟨275078, by rfl⟩ : syracuseStep 1467085 = 550157) (by norm_num)
theorem B1237717 : Blo 686314 1237717 := bbase (se 7 (by rfl) ⟨14504, by rfl⟩ : syracuseStep 1237717 = 29009) (by norm_num)
theorem B1303285 : Blo 686314 1303285 := bbase (se 5 (by rfl) ⟨61091, by rfl⟩ : syracuseStep 1303285 = 122183) (by norm_num)
theorem B1237781 : Blo 686314 1237781 := bbase (se 6 (by rfl) ⟨29010, by rfl⟩ : syracuseStep 1237781 = 58021) (by norm_num)
theorem B2614133 : Blo 686314 2614133 := bbase (se 5 (by rfl) ⟨122537, by rfl⟩ : syracuseStep 2614133 = 245075) (by norm_num)
theorem B4416373 : Blo 686314 4416373 := bbase (se 5 (by rfl) ⟨207017, by rfl⟩ : syracuseStep 4416373 = 414035) (by norm_num)
theorem B1303445 : Blo 686314 1303445 := bbase (se 6 (by rfl) ⟨30549, by rfl⟩ : syracuseStep 1303445 = 61099) (by norm_num)
theorem B1303589 : Blo 686314 1303589 := bbase (se 4 (by rfl) ⟨122211, by rfl⟩ : syracuseStep 1303589 = 244423) (by norm_num)
theorem B1238069 : Blo 686314 1238069 := bbase (se 5 (by rfl) ⟨58034, by rfl⟩ : syracuseStep 1238069 = 116069) (by norm_num)
theorem B2319461 : Blo 686314 2319461 := bbase (se 4 (by rfl) ⟨217449, by rfl⟩ : syracuseStep 2319461 = 434899) (by norm_num)
theorem B1959029 : Blo 686314 1959029 := bbase (se 5 (by rfl) ⟨91829, by rfl⟩ : syracuseStep 1959029 = 183659) (by norm_num)
theorem B1303877 : Blo 686314 1303877 := bbase (se 4 (by rfl) ⟨122238, by rfl⟩ : syracuseStep 1303877 = 244477) (by norm_num)
theorem B2942405 : Blo 686314 2942405 := bbase (se 4 (by rfl) ⟨275850, by rfl⟩ : syracuseStep 2942405 = 551701) (by norm_num)
theorem B1304029 : Blo 686314 1304029 := bbase (se 3 (by rfl) ⟨244505, by rfl⟩ : syracuseStep 1304029 = 489011) (by norm_num)
theorem B2319893 : Blo 686314 2319893 := bbase (se 6 (by rfl) ⟨54372, by rfl⟩ : syracuseStep 2319893 = 108745) (by norm_num)
theorem B1959461 : Blo 686314 1959461 := bbase (se 4 (by rfl) ⟨183699, by rfl⟩ : syracuseStep 1959461 = 367399) (by norm_num)
theorem B1467973 : Blo 686314 1467973 := bbase (se 4 (by rfl) ⟨137622, by rfl⟩ : syracuseStep 1467973 = 275245) (by norm_num)
theorem B1304333 : Blo 686314 1304333 := bbase (se 3 (by rfl) ⟨244562, by rfl⟩ : syracuseStep 1304333 = 489125) (by norm_num)
theorem B2320325 : Blo 686314 2320325 := bbase (se 4 (by rfl) ⟨217530, by rfl⟩ : syracuseStep 2320325 = 435061) (by norm_num)
theorem B1468469 : Blo 686314 1468469 := bbase (se 5 (by rfl) ⟨68834, by rfl⟩ : syracuseStep 1468469 = 137669) (by norm_num)
theorem B1861861 : Blo 686314 1861861 := bbase (se 4 (by rfl) ⟨174549, by rfl⟩ : syracuseStep 1861861 = 349099) (by norm_num)
theorem B1960213 : Blo 686314 1960213 := bbase (se 6 (by rfl) ⟨45942, by rfl⟩ : syracuseStep 1960213 = 91885) (by norm_num)
theorem B1239389 : Blo 686314 1239389 := bbase (se 3 (by rfl) ⟨232385, by rfl⟩ : syracuseStep 1239389 = 464771) (by norm_num)
theorem B2320757 : Blo 686314 2320757 := bbase (se 5 (by rfl) ⟨108785, by rfl⟩ : syracuseStep 2320757 = 217571) (by norm_num)
theorem B977293 : Blo 686314 977293 := bbase (se 3 (by rfl) ⟨183242, by rfl⟩ : syracuseStep 977293 = 366485) (by norm_num)
theorem B1305085 : Blo 686314 1305085 := bbase (se 3 (by rfl) ⟨244703, by rfl⟩ : syracuseStep 1305085 = 489407) (by norm_num)
theorem B1567333 : Blo 686314 1567333 := bbase (se 4 (by rfl) ⟨146937, by rfl⟩ : syracuseStep 1567333 = 293875) (by norm_num)
theorem B2976389 : Blo 686314 2976389 := bbase (se 4 (by rfl) ⟨279036, by rfl⟩ : syracuseStep 2976389 = 558073) (by norm_num)
theorem B2517637 : Blo 686314 2517637 := bbase (se 4 (by rfl) ⟨236028, by rfl⟩ : syracuseStep 2517637 = 472057) (by norm_num)
theorem B1305229 : Blo 686314 1305229 := bbase (se 3 (by rfl) ⟨244730, by rfl⟩ : syracuseStep 1305229 = 489461) (by norm_num)
theorem B2321189 : Blo 686314 2321189 := bbase (se 4 (by rfl) ⟨217611, by rfl⟩ : syracuseStep 2321189 = 435223) (by norm_num)
theorem B1305389 : Blo 686314 1305389 := bbase (se 3 (by rfl) ⟨244760, by rfl⟩ : syracuseStep 1305389 = 489521) (by norm_num)
theorem B5237621 : Blo 686314 5237621 := bbase (se 5 (by rfl) ⟨245513, by rfl⟩ : syracuseStep 5237621 = 491027) (by norm_num)
theorem B1469357 : Blo 686314 1469357 := bbase (se 3 (by rfl) ⟨275504, by rfl⟩ : syracuseStep 1469357 = 551009) (by norm_num)
theorem B2616245 : Blo 686314 2616245 := bbase (se 5 (by rfl) ⟨122636, by rfl⟩ : syracuseStep 2616245 = 245273) (by norm_num)
theorem B1305533 : Blo 686314 1305533 := bbase (se 3 (by rfl) ⟨244787, by rfl⟩ : syracuseStep 1305533 = 489575) (by norm_num)
theorem B3304421 : Blo 686314 3304421 := bbase (se 4 (by rfl) ⟨309789, by rfl⟩ : syracuseStep 3304421 = 619579) (by norm_num)
theorem B1469477 : Blo 686314 1469477 := bbase (se 4 (by rfl) ⟨137763, by rfl⟩ : syracuseStep 1469477 = 275527) (by norm_num)
theorem B978085 : Blo 686314 978085 := bbase (se 4 (by rfl) ⟨91695, by rfl⟩ : syracuseStep 978085 = 183391) (by norm_num)
theorem B2944181 : Blo 686314 2944181 := bbase (se 5 (by rfl) ⟨138008, by rfl⟩ : syracuseStep 2944181 = 276017) (by norm_num)
theorem B2321621 : Blo 686314 2321621 := bbase (se 7 (by rfl) ⟨27206, by rfl⟩ : syracuseStep 2321621 = 54413) (by norm_num)
theorem B2616533 : Blo 686314 2616533 := bbase (se 7 (by rfl) ⟨30662, by rfl⟩ : syracuseStep 2616533 = 61325) (by norm_num)
theorem B1305821 : Blo 686314 1305821 := bbase (se 3 (by rfl) ⟨244841, by rfl⟩ : syracuseStep 1305821 = 489683) (by norm_num)
theorem B3140869 : Blo 686314 3140869 := bbase (se 4 (by rfl) ⟨294456, by rfl⟩ : syracuseStep 3140869 = 588913) (by norm_num)
theorem B1305973 : Blo 686314 1305973 := bbase (se 5 (by rfl) ⟨61217, by rfl⟩ : syracuseStep 1305973 = 122435) (by norm_num)
theorem B2944421 : Blo 686314 2944421 := bbase (se 4 (by rfl) ⟨276039, by rfl⟩ : syracuseStep 2944421 = 552079) (by norm_num)
theorem B1174981 : Blo 686314 1174981 := bbase (se 4 (by rfl) ⟨110154, by rfl⟩ : syracuseStep 1174981 = 220309) (by norm_num)
theorem B945605 : Blo 686314 945605 := bbase (se 4 (by rfl) ⟨88650, by rfl⟩ : syracuseStep 945605 = 177301) (by norm_num)
theorem B978421 : Blo 686314 978421 := bbase (se 5 (by rfl) ⟨45863, by rfl⟩ : syracuseStep 978421 = 91727) (by norm_num)
theorem B2322053 : Blo 686314 2322053 := bbase (se 4 (by rfl) ⟨217692, by rfl⟩ : syracuseStep 2322053 = 435385) (by norm_num)
theorem B1470109 : Blo 686314 1470109 := bbase (se 3 (by rfl) ⟨275645, by rfl⟩ : syracuseStep 1470109 = 551291) (by norm_num)
theorem B1306277 : Blo 686314 1306277 := bbase (se 4 (by rfl) ⟨122463, by rfl⟩ : syracuseStep 1306277 = 244927) (by norm_num)
theorem B978637 : Blo 686314 978637 := bbase (se 3 (by rfl) ⟨183494, by rfl⟩ : syracuseStep 978637 = 366989) (by norm_num)
theorem B2977669 : Blo 686314 2977669 := bbase (se 4 (by rfl) ⟨279156, by rfl⟩ : syracuseStep 2977669 = 558313) (by norm_num)
theorem B1863701 : Blo 686314 1863701 := bbase (se 6 (by rfl) ⟨43680, by rfl⟩ : syracuseStep 1863701 = 87361) (by norm_num)
theorem B2322485 : Blo 686314 2322485 := bbase (se 5 (by rfl) ⟨108866, by rfl⟩ : syracuseStep 2322485 = 217733) (by norm_num)
theorem B979013 : Blo 686314 979013 := bbase (se 4 (by rfl) ⟨91782, by rfl⟩ : syracuseStep 979013 = 183565) (by norm_num)
theorem B1568893 : Blo 686314 1568893 := bbase (se 3 (by rfl) ⟨294167, by rfl⟩ : syracuseStep 1568893 = 588335) (by norm_num)
theorem B4714805 : Blo 686314 4714805 := bbase (se 5 (by rfl) ⟨221006, by rfl⟩ : syracuseStep 4714805 = 442013) (by norm_num)
theorem B1241413 : Blo 686314 1241413 := bbase (se 4 (by rfl) ⟨116382, by rfl⟩ : syracuseStep 1241413 = 232765) (by norm_num)
theorem B2617717 : Blo 686314 2617717 := bbase (se 5 (by rfl) ⟨122705, by rfl⟩ : syracuseStep 2617717 = 245411) (by norm_num)
theorem B1307029 : Blo 686314 1307029 := bbase (se 6 (by rfl) ⟨30633, by rfl⟩ : syracuseStep 1307029 = 61267) (by norm_num)
theorem B2322917 : Blo 686314 2322917 := bbase (se 4 (by rfl) ⟨217773, by rfl⟩ : syracuseStep 2322917 = 435547) (by norm_num)
theorem B1241581 : Blo 686314 1241581 := bbase (se 3 (by rfl) ⟨232796, by rfl⟩ : syracuseStep 1241581 = 465593) (by norm_num)
theorem B1470997 : Blo 686314 1470997 := bbase (se 6 (by rfl) ⟨34476, by rfl⟩ : syracuseStep 1470997 = 68953) (by norm_num)
theorem B1307173 : Blo 686314 1307173 := bbase (se 4 (by rfl) ⟨122547, by rfl⟩ : syracuseStep 1307173 = 245095) (by norm_num)
theorem B717413 : Blo 686314 717413 := bbase (se 4 (by rfl) ⟨67257, by rfl⟩ : syracuseStep 717413 = 134515) (by norm_num)
theorem B1471117 : Blo 686314 1471117 := bbase (se 3 (by rfl) ⟨275834, by rfl⟩ : syracuseStep 1471117 = 551669) (by norm_num)
theorem B2618021 : Blo 686314 2618021 := bbase (se 4 (by rfl) ⟨245439, by rfl⟩ : syracuseStep 2618021 = 490879) (by norm_num)
theorem B1045181 : Blo 686314 1045181 := bbase (se 3 (by rfl) ⟨195971, by rfl⟩ : syracuseStep 1045181 = 391943) (by norm_num)
theorem B1307333 : Blo 686314 1307333 := bbase (se 4 (by rfl) ⟨122562, by rfl⟩ : syracuseStep 1307333 = 245125) (by norm_num)
theorem B7533269 : Blo 686314 7533269 := bbase (se 7 (by rfl) ⟨88280, by rfl⟩ : syracuseStep 7533269 = 176561) (by norm_num)
theorem B1766165 : Blo 686314 1766165 := bbase (se 6 (by rfl) ⟨41394, by rfl⟩ : syracuseStep 1766165 = 82789) (by norm_num)
theorem B2356037 : Blo 686314 2356037 := bbase (se 4 (by rfl) ⟨220878, by rfl⟩ : syracuseStep 2356037 = 441757) (by norm_num)
theorem B1307477 : Blo 686314 1307477 := bbase (se 9 (by rfl) ⟨3830, by rfl⟩ : syracuseStep 1307477 = 7661) (by norm_num)
theorem B2487125 : Blo 686314 2487125 := bbase (se 9 (by rfl) ⟨7286, by rfl⟩ : syracuseStep 2487125 = 14573) (by norm_num)
theorem B1471373 : Blo 686314 1471373 := bbase (se 3 (by rfl) ⟨275882, by rfl⟩ : syracuseStep 1471373 = 551765) (by norm_num)
theorem B2323349 : Blo 686314 2323349 := bbase (se 6 (by rfl) ⟨54453, by rfl⟩ : syracuseStep 2323349 = 108907) (by norm_num)
theorem B1700765 : Blo 686314 1700765 := bbase (se 3 (by rfl) ⟨318893, by rfl⟩ : syracuseStep 1700765 = 637787) (by norm_num)
theorem B3306437 : Blo 686314 3306437 := bbase (se 4 (by rfl) ⟨309978, by rfl⟩ : syracuseStep 3306437 = 619957) (by norm_num)
theorem B1569797 : Blo 686314 1569797 := bbase (se 4 (by rfl) ⟨147168, by rfl⟩ : syracuseStep 1569797 = 294337) (by norm_num)
theorem B1242157 : Blo 686314 1242157 := bbase (se 3 (by rfl) ⟨232904, by rfl⟩ : syracuseStep 1242157 = 465809) (by norm_num)
theorem B1963061 : Blo 686314 1963061 := bbase (se 5 (by rfl) ⟨92018, by rfl⟩ : syracuseStep 1963061 = 184037) (by norm_num)
theorem B1307765 : Blo 686314 1307765 := bbase (se 5 (by rfl) ⟨61301, by rfl⟩ : syracuseStep 1307765 = 122603) (by norm_num)
theorem B1569989 : Blo 686314 1569989 := bbase (se 4 (by rfl) ⟨147186, by rfl⟩ : syracuseStep 1569989 = 294373) (by norm_num)
theorem B1570061 : Blo 686314 1570061 := bbase (se 3 (by rfl) ⟨294386, by rfl⟩ : syracuseStep 1570061 = 588773) (by norm_num)
theorem B1307917 : Blo 686314 1307917 := bbase (se 3 (by rfl) ⟨245234, by rfl⟩ : syracuseStep 1307917 = 490469) (by norm_num)
theorem B783685 : Blo 686314 783685 := bbase (se 4 (by rfl) ⟨73470, by rfl⟩ : syracuseStep 783685 = 146941) (by norm_num)
theorem B2323781 : Blo 686314 2323781 := bbase (se 4 (by rfl) ⟨217854, by rfl⟩ : syracuseStep 2323781 = 435709) (by norm_num)
theorem B783721 : Blo 686314 783721 := bbase (se 2 (by rfl) ⟨293895, by rfl⟩ : syracuseStep 783721 = 587791) (by norm_num)
theorem B5895605 : Blo 686314 5895605 := bbase (se 5 (by rfl) ⟨276356, by rfl⟩ : syracuseStep 5895605 = 552713) (by norm_num)
theorem B980437 : Blo 686314 980437 := bbase (se 7 (by rfl) ⟨11489, by rfl⟩ : syracuseStep 980437 = 22979) (by norm_num)
theorem B6616565 : Blo 686314 6616565 := bbase (se 5 (by rfl) ⟨310151, by rfl⟩ : syracuseStep 6616565 = 620303) (by norm_num)
theorem B1177109 : Blo 686314 1177109 := bbase (se 6 (by rfl) ⟨27588, by rfl⟩ : syracuseStep 1177109 = 55177) (by norm_num)
theorem B1308221 : Blo 686314 1308221 := bbase (se 3 (by rfl) ⟨245291, by rfl⟩ : syracuseStep 1308221 = 490583) (by norm_num)
theorem B783977 : Blo 686314 783977 := bbase (se 2 (by rfl) ⟨293991, by rfl⟩ : syracuseStep 783977 = 587983) (by norm_num)
theorem B784013 : Blo 686314 784013 := bbase (se 3 (by rfl) ⟨147002, by rfl⟩ : syracuseStep 784013 = 294005) (by norm_num)
theorem B2946709 : Blo 686314 2946709 := bbase (se 6 (by rfl) ⟨69063, by rfl⟩ : syracuseStep 2946709 = 138127) (by norm_num)
theorem B1242797 : Blo 686314 1242797 := bbase (se 3 (by rfl) ⟨233024, by rfl⟩ : syracuseStep 1242797 = 466049) (by norm_num)
theorem B3307189 : Blo 686314 3307189 := bbase (se 5 (by rfl) ⟨155024, by rfl⟩ : syracuseStep 3307189 = 310049) (by norm_num)
theorem B2324213 : Blo 686314 2324213 := bbase (se 5 (by rfl) ⟨108947, by rfl⟩ : syracuseStep 2324213 = 217895) (by norm_num)
theorem B1472261 : Blo 686314 1472261 := bbase (se 4 (by rfl) ⟨138024, by rfl⟩ : syracuseStep 1472261 = 276049) (by norm_num)
theorem B1242965 : Blo 686314 1242965 := bbase (se 9 (by rfl) ⟨3641, by rfl⟩ : syracuseStep 1242965 = 7283) (by norm_num)
theorem B817085 : Blo 686314 817085 := bbase (se 3 (by rfl) ⟨153203, by rfl⟩ : syracuseStep 817085 = 306407) (by norm_num)
theorem B1472501 : Blo 686314 1472501 := bbase (se 5 (by rfl) ⟨69023, by rfl⟩ : syracuseStep 1472501 = 138047) (by norm_num)
theorem B11761685 : Blo 686314 11761685 := bbase (se 6 (by rfl) ⟨275664, by rfl⟩ : syracuseStep 11761685 = 551329) (by norm_num)
theorem B981029 : Blo 686314 981029 := bbase (se 4 (by rfl) ⟨91971, by rfl⟩ : syracuseStep 981029 = 183943) (by norm_num)
theorem B981109 : Blo 686314 981109 := bbase (se 5 (by rfl) ⟨45989, by rfl⟩ : syracuseStep 981109 = 91979) (by norm_num)
theorem B2324645 : Blo 686314 2324645 := bbase (se 4 (by rfl) ⟨217935, by rfl⟩ : syracuseStep 2324645 = 435871) (by norm_num)
theorem B882857 : Blo 686314 882857 := bbase (se 2 (by rfl) ⟨331071, by rfl⟩ : syracuseStep 882857 = 662143) (by norm_num)
theorem B784561 : Blo 686314 784561 := bbase (se 2 (by rfl) ⟨294210, by rfl⟩ : syracuseStep 784561 = 588421) (by norm_num)
theorem B1964245 : Blo 686314 1964245 := bbase (se 7 (by rfl) ⟨23018, by rfl⟩ : syracuseStep 1964245 = 46037) (by norm_num)
theorem B981229 : Blo 686314 981229 := bbase (se 3 (by rfl) ⟨183980, by rfl⟩ : syracuseStep 981229 = 367961) (by norm_num)
theorem B1308973 : Blo 686314 1308973 := bbase (se 3 (by rfl) ⟨245432, by rfl⟩ : syracuseStep 1308973 = 490865) (by norm_num)
theorem B981325 : Blo 686314 981325 := bbase (se 3 (by rfl) ⟨183998, by rfl⟩ : syracuseStep 981325 = 367997) (by norm_num)
theorem B1964405 : Blo 686314 1964405 := bbase (se 5 (by rfl) ⟨92081, by rfl⟩ : syracuseStep 1964405 = 184163) (by norm_num)
theorem B1309117 : Blo 686314 1309117 := bbase (se 3 (by rfl) ⟨245459, by rfl⟩ : syracuseStep 1309117 = 490919) (by norm_num)
theorem B1473005 : Blo 686314 1473005 := bbase (se 3 (by rfl) ⟨276188, by rfl⟩ : syracuseStep 1473005 = 552377) (by norm_num)
theorem B1473013 : Blo 686314 1473013 := bbase (se 5 (by rfl) ⟨69047, by rfl⟩ : syracuseStep 1473013 = 138095) (by norm_num)
theorem B3930677 : Blo 686314 3930677 := bbase (se 5 (by rfl) ⟨184250, by rfl⟩ : syracuseStep 3930677 = 368501) (by norm_num)
theorem B2325077 : Blo 686314 2325077 := bbase (se 8 (by rfl) ⟨13623, by rfl⟩ : syracuseStep 2325077 = 27247) (by norm_num)
theorem B1309277 : Blo 686314 1309277 := bbase (se 3 (by rfl) ⟨245489, by rfl⟩ : syracuseStep 1309277 = 490979) (by norm_num)
theorem B1964645 : Blo 686314 1964645 := bbase (se 4 (by rfl) ⟨184185, by rfl⟩ : syracuseStep 1964645 = 368371) (by norm_num)
theorem B16743125 : Blo 686314 16743125 := bbase (se 7 (by rfl) ⟨196208, by rfl⟩ : syracuseStep 16743125 = 392417) (by norm_num)
theorem B2620133 : Blo 686314 2620133 := bbase (se 4 (by rfl) ⟨245637, by rfl⟩ : syracuseStep 2620133 = 491275) (by norm_num)
theorem B1309421 : Blo 686314 1309421 := bbase (se 3 (by rfl) ⟨245516, by rfl⟩ : syracuseStep 1309421 = 491033) (by norm_num)
theorem B1964837 : Blo 686314 1964837 := bbase (se 4 (by rfl) ⟨184203, by rfl⟩ : syracuseStep 1964837 = 368407) (by norm_num)
theorem B981821 : Blo 686314 981821 := bbase (se 3 (by rfl) ⟨184091, by rfl⟩ : syracuseStep 981821 = 368183) (by norm_num)
theorem B1768301 : Blo 686314 1768301 := bbase (se 3 (by rfl) ⟨331556, by rfl⟩ : syracuseStep 1768301 = 663113) (by norm_num)
theorem B1571813 : Blo 686314 1571813 := bbase (se 4 (by rfl) ⟨147357, by rfl⟩ : syracuseStep 1571813 = 294715) (by norm_num)
theorem B2325509 : Blo 686314 2325509 := bbase (se 4 (by rfl) ⟨218016, by rfl⟩ : syracuseStep 2325509 = 436033) (by norm_num)
theorem B2620421 : Blo 686314 2620421 := bbase (se 4 (by rfl) ⟨245664, by rfl⟩ : syracuseStep 2620421 = 491329) (by norm_num)
theorem B1309709 : Blo 686314 1309709 := bbase (se 3 (by rfl) ⟨245570, by rfl⟩ : syracuseStep 1309709 = 491141) (by norm_num)
theorem B2948197 : Blo 686314 2948197 := bbase (se 4 (by rfl) ⟨276393, by rfl⟩ : syracuseStep 2948197 = 552787) (by norm_num)
theorem B2948213 : Blo 686314 2948213 := bbase (se 5 (by rfl) ⟨138197, by rfl⟩ : syracuseStep 2948213 = 276395) (by norm_num)
theorem B1309861 : Blo 686314 1309861 := bbase (se 4 (by rfl) ⟨122799, by rfl⟩ : syracuseStep 1309861 = 245599) (by norm_num)
theorem B982373 : Blo 686314 982373 := bbase (se 4 (by rfl) ⟨92097, by rfl⟩ : syracuseStep 982373 = 184195) (by norm_num)
theorem B1047973 : Blo 686314 1047973 := bbase (se 4 (by rfl) ⟨98247, by rfl⟩ : syracuseStep 1047973 = 196495) (by norm_num)
theorem B2325941 : Blo 686314 2325941 := bbase (se 5 (by rfl) ⟨109028, by rfl⟩ : syracuseStep 2325941 = 218057) (by norm_num)
theorem B785857 : Blo 686314 785857 := bbase (se 2 (by rfl) ⟨294696, by rfl⟩ : syracuseStep 785857 = 589393) (by norm_num)
theorem B1310165 : Blo 686314 1310165 := bbase (se 7 (by rfl) ⟨15353, by rfl⟩ : syracuseStep 1310165 = 30707) (by norm_num)
theorem B9895445 : Blo 686314 9895445 := bbase (se 6 (by rfl) ⟨231924, by rfl⟩ : syracuseStep 9895445 = 463849) (by norm_num)
theorem B7077461 : Blo 686314 7077461 := bbase (se 8 (by rfl) ⟨41469, by rfl⟩ : syracuseStep 7077461 = 82939) (by norm_num)
theorem B1474141 : Blo 686314 1474141 := bbase (se 3 (by rfl) ⟨276401, by rfl⟩ : syracuseStep 1474141 = 552803) (by norm_num)
theorem B1769285 : Blo 686314 1769285 := bbase (se 4 (by rfl) ⟨165870, by rfl⟩ : syracuseStep 1769285 = 331741) (by norm_num)
theorem B851809 : Blo 686314 851809 := bbase (se 2 (by rfl) ⟨319428, by rfl⟩ : syracuseStep 851809 = 638857) (by norm_num)
theorem B2326373 : Blo 686314 2326373 := bbase (se 4 (by rfl) ⟨218097, by rfl⟩ : syracuseStep 2326373 = 436195) (by norm_num)
theorem B688131 : Blo 686314 688131 := bstep (se 1 (by rfl) ⟨516098, by rfl⟩ : syracuseStep 688131 = 1032197) B1032197
theorem B688147 : Blo 686314 688147 := bstep (se 1 (by rfl) ⟨516110, by rfl⟩ : syracuseStep 688147 = 1032221) B1032221
theorem B688163 : Blo 686314 688163 := bstep (se 1 (by rfl) ⟨516122, by rfl⟩ : syracuseStep 688163 = 1032245) B1032245
theorem B688179 : Blo 686314 688179 := bstep (se 1 (by rfl) ⟨516134, by rfl⟩ : syracuseStep 688179 = 1032269) B1032269
theorem B688195 : Blo 686314 688195 := bstep (se 1 (by rfl) ⟨516146, by rfl⟩ : syracuseStep 688195 = 1032293) B1032293
theorem B688211 : Blo 686314 688211 := bstep (se 1 (by rfl) ⟨516158, by rfl⟩ : syracuseStep 688211 = 1032317) B1032317
theorem B688227 : Blo 686314 688227 := bstep (se 1 (by rfl) ⟨516170, by rfl⟩ : syracuseStep 688227 = 1032341) B1032341
theorem B688243 : Blo 686314 688243 := bstep (se 1 (by rfl) ⟨516182, by rfl⟩ : syracuseStep 688243 = 1032365) B1032365
theorem B688259 : Blo 686314 688259 := bstep (se 1 (by rfl) ⟨516194, by rfl⟩ : syracuseStep 688259 = 1032389) B1032389
theorem B688275 : Blo 686314 688275 := bstep (se 1 (by rfl) ⟨516206, by rfl⟩ : syracuseStep 688275 = 1032413) B1032413
theorem B688291 : Blo 686314 688291 := bstep (se 1 (by rfl) ⟨516218, by rfl⟩ : syracuseStep 688291 = 1032437) B1032437
theorem B688307 : Blo 686314 688307 := bstep (se 1 (by rfl) ⟨516230, by rfl⟩ : syracuseStep 688307 = 1032461) B1032461
theorem B688323 : Blo 686314 688323 := bstep (se 1 (by rfl) ⟨516242, by rfl⟩ : syracuseStep 688323 = 1032485) B1032485
theorem B688339 : Blo 686314 688339 := bstep (se 1 (by rfl) ⟨516254, by rfl⟩ : syracuseStep 688339 = 1032509) B1032509
theorem B688355 : Blo 686314 688355 := bstep (se 1 (by rfl) ⟨516266, by rfl⟩ : syracuseStep 688355 = 1032533) B1032533
theorem B688371 : Blo 686314 688371 := bstep (se 1 (by rfl) ⟨516278, by rfl⟩ : syracuseStep 688371 = 1032557) B1032557
theorem B688387 : Blo 686314 688387 := bstep (se 1 (by rfl) ⟨516290, by rfl⟩ : syracuseStep 688387 = 1032581) B1032581
theorem B688403 : Blo 686314 688403 := bstep (se 1 (by rfl) ⟨516302, by rfl⟩ : syracuseStep 688403 = 1032605) B1032605
theorem B688419 : Blo 686314 688419 := bstep (se 1 (by rfl) ⟨516314, by rfl⟩ : syracuseStep 688419 = 1032629) B1032629
theorem B688435 : Blo 686314 688435 := bstep (se 1 (by rfl) ⟨516326, by rfl⟩ : syracuseStep 688435 = 1032653) B1032653
theorem B1179955 : Blo 686314 1179955 := bstep (se 1 (by rfl) ⟨884966, by rfl⟩ : syracuseStep 1179955 = 1769933) B1769933
theorem B688451 : Blo 686314 688451 := bstep (se 1 (by rfl) ⟨516338, by rfl⟩ : syracuseStep 688451 = 1032677) B1032677
theorem B688467 : Blo 686314 688467 := bstep (se 1 (by rfl) ⟨516350, by rfl⟩ : syracuseStep 688467 = 1032701) B1032701
theorem B688483 : Blo 686314 688483 := bstep (se 1 (by rfl) ⟨516362, by rfl⟩ : syracuseStep 688483 = 1032725) B1032725
theorem B688499 : Blo 686314 688499 := bstep (se 1 (by rfl) ⟨516374, by rfl⟩ : syracuseStep 688499 = 1032749) B1032749
theorem B688515 : Blo 686314 688515 := bstep (se 1 (by rfl) ⟨516386, by rfl⟩ : syracuseStep 688515 = 1032773) B1032773
theorem B2097539 : Blo 686314 2097539 := bstep (se 1 (by rfl) ⟨1573154, by rfl⟩ : syracuseStep 2097539 = 3146309) B3146309
theorem B688531 : Blo 686314 688531 := bstep (se 1 (by rfl) ⟨516398, by rfl⟩ : syracuseStep 688531 = 1032797) B1032797
theorem B688547 : Blo 686314 688547 := bstep (se 1 (by rfl) ⟨516410, by rfl⟩ : syracuseStep 688547 = 1032821) B1032821
theorem B688563 : Blo 686314 688563 := bstep (se 1 (by rfl) ⟨516422, by rfl⟩ : syracuseStep 688563 = 1032845) B1032845
theorem B688579 : Blo 686314 688579 := bstep (se 1 (by rfl) ⟨516434, by rfl⟩ : syracuseStep 688579 = 1032869) B1032869
theorem B688595 : Blo 686314 688595 := bstep (se 1 (by rfl) ⟨516446, by rfl⟩ : syracuseStep 688595 = 1032893) B1032893
theorem B688611 : Blo 686314 688611 := bstep (se 1 (by rfl) ⟨516458, by rfl⟩ : syracuseStep 688611 = 1032917) B1032917
theorem B2327021 : Blo 686314 2327021 := bstep (se 3 (by rfl) ⟨436316, by rfl⟩ : syracuseStep 2327021 = 872633) B872633
theorem B688627 : Blo 686314 688627 := bstep (se 1 (by rfl) ⟨516470, by rfl⟩ : syracuseStep 688627 = 1032941) B1032941
theorem B688643 : Blo 686314 688643 := bstep (se 1 (by rfl) ⟨516482, by rfl⟩ : syracuseStep 688643 = 1032965) B1032965
theorem B2359811 : Blo 686314 2359811 := bstep (se 1 (by rfl) ⟨1769858, by rfl⟩ : syracuseStep 2359811 = 3539717) B3539717
theorem B688659 : Blo 686314 688659 := bstep (se 1 (by rfl) ⟨516494, by rfl⟩ : syracuseStep 688659 = 1032989) B1032989
theorem B688675 : Blo 686314 688675 := bstep (se 1 (by rfl) ⟨516506, by rfl⟩ : syracuseStep 688675 = 1033013) B1033013
theorem B2327075 : Blo 686314 2327075 := bstep (se 1 (by rfl) ⟨1745306, by rfl⟩ : syracuseStep 2327075 = 3490613) B3490613
theorem B688691 : Blo 686314 688691 := bstep (se 1 (by rfl) ⟨516518, by rfl⟩ : syracuseStep 688691 = 1033037) B1033037
theorem B688707 : Blo 686314 688707 := bstep (se 1 (by rfl) ⟨516530, by rfl⟩ : syracuseStep 688707 = 1033061) B1033061
theorem B688723 : Blo 686314 688723 := bstep (se 1 (by rfl) ⟨516542, by rfl⟩ : syracuseStep 688723 = 1033085) B1033085
theorem B688739 : Blo 686314 688739 := bstep (se 1 (by rfl) ⟨516554, by rfl⟩ : syracuseStep 688739 = 1033109) B1033109
theorem B2228849 : Blo 686314 2228849 := bstep (se 2 (by rfl) ⟨835818, by rfl⟩ : syracuseStep 2228849 = 1671637) B1671637
theorem B688755 : Blo 686314 688755 := bstep (se 1 (by rfl) ⟨516566, by rfl⟩ : syracuseStep 688755 = 1033133) B1033133
theorem B688771 : Blo 686314 688771 := bstep (se 1 (by rfl) ⟨516578, by rfl⟩ : syracuseStep 688771 = 1033157) B1033157
theorem B688787 : Blo 686314 688787 := bstep (se 1 (by rfl) ⟨516590, by rfl⟩ : syracuseStep 688787 = 1033181) B1033181
theorem B688803 : Blo 686314 688803 := bstep (se 1 (by rfl) ⟨516602, by rfl⟩ : syracuseStep 688803 = 1033205) B1033205
theorem B688819 : Blo 686314 688819 := bstep (se 1 (by rfl) ⟨516614, by rfl⟩ : syracuseStep 688819 = 1033229) B1033229
theorem B688835 : Blo 686314 688835 := bstep (se 1 (by rfl) ⟨516626, by rfl⟩ : syracuseStep 688835 = 1033253) B1033253
theorem B688851 : Blo 686314 688851 := bstep (se 1 (by rfl) ⟨516638, by rfl⟩ : syracuseStep 688851 = 1033277) B1033277
theorem B688867 : Blo 686314 688867 := bstep (se 1 (by rfl) ⟨516650, by rfl⟩ : syracuseStep 688867 = 1033301) B1033301
theorem B3310321 : Blo 686314 3310321 := bstep (se 2 (by rfl) ⟨1241370, by rfl⟩ : syracuseStep 3310321 = 2482741) B2482741
theorem B688883 : Blo 686314 688883 := bstep (se 1 (by rfl) ⟨516662, by rfl⟩ : syracuseStep 688883 = 1033325) B1033325
theorem B688899 : Blo 686314 688899 := bstep (se 1 (by rfl) ⟨516674, by rfl⟩ : syracuseStep 688899 = 1033349) B1033349
theorem B688915 : Blo 686314 688915 := bstep (se 1 (by rfl) ⟨516686, by rfl⟩ : syracuseStep 688915 = 1033373) B1033373
theorem B688931 : Blo 686314 688931 := bstep (se 1 (by rfl) ⟨516698, by rfl⟩ : syracuseStep 688931 = 1033397) B1033397
theorem B1737521 : Blo 686314 1737521 := bstep (se 2 (by rfl) ⟨651570, by rfl⟩ : syracuseStep 1737521 = 1303141) B1303141
theorem B2327345 : Blo 686314 2327345 := bstep (se 2 (by rfl) ⟨872754, by rfl⟩ : syracuseStep 2327345 = 1745509) B1745509
theorem B688947 : Blo 686314 688947 := bstep (se 1 (by rfl) ⟨516710, by rfl⟩ : syracuseStep 688947 = 1033421) B1033421
theorem B688963 : Blo 686314 688963 := bstep (se 1 (by rfl) ⟨516722, by rfl⟩ : syracuseStep 688963 = 1033445) B1033445
theorem B688979 : Blo 686314 688979 := bstep (se 1 (by rfl) ⟨516734, by rfl⟩ : syracuseStep 688979 = 1033469) B1033469
theorem B1737571 : Blo 686314 1737571 := bstep (se 1 (by rfl) ⟨1303178, by rfl⟩ : syracuseStep 1737571 = 2606357) B2606357
theorem B688995 : Blo 686314 688995 := bstep (se 1 (by rfl) ⟨516746, by rfl⟩ : syracuseStep 688995 = 1033493) B1033493
theorem B689011 : Blo 686314 689011 := bstep (se 1 (by rfl) ⟨516758, by rfl⟩ : syracuseStep 689011 = 1033517) B1033517
theorem B689027 : Blo 686314 689027 := bstep (se 1 (by rfl) ⟨516770, by rfl⟩ : syracuseStep 689027 = 1033541) B1033541
theorem B689043 : Blo 686314 689043 := bstep (se 1 (by rfl) ⟨516782, by rfl⟩ : syracuseStep 689043 = 1033565) B1033565
theorem B689059 : Blo 686314 689059 := bstep (se 1 (by rfl) ⟨516794, by rfl⟩ : syracuseStep 689059 = 1033589) B1033589
theorem B689075 : Blo 686314 689075 := bstep (se 1 (by rfl) ⟨516806, by rfl⟩ : syracuseStep 689075 = 1033613) B1033613
theorem B689091 : Blo 686314 689091 := bstep (se 1 (by rfl) ⟨516818, by rfl⟩ : syracuseStep 689091 = 1033637) B1033637
theorem B689107 : Blo 686314 689107 := bstep (se 1 (by rfl) ⟨516830, by rfl⟩ : syracuseStep 689107 = 1033661) B1033661
theorem B689123 : Blo 686314 689123 := bstep (se 1 (by rfl) ⟨516842, by rfl⟩ : syracuseStep 689123 = 1033685) B1033685
theorem B1737713 : Blo 686314 1737713 := bstep (se 2 (by rfl) ⟨651642, by rfl⟩ : syracuseStep 1737713 = 1303285) B1303285
theorem B689139 : Blo 686314 689139 := bstep (se 1 (by rfl) ⟨516854, by rfl⟩ : syracuseStep 689139 = 1033709) B1033709
theorem B689155 : Blo 686314 689155 := bstep (se 1 (by rfl) ⟨516866, by rfl⟩ : syracuseStep 689155 = 1033733) B1033733
theorem B689171 : Blo 686314 689171 := bstep (se 1 (by rfl) ⟨516878, by rfl⟩ : syracuseStep 689171 = 1033757) B1033757
theorem B689187 : Blo 686314 689187 := bstep (se 1 (by rfl) ⟨516890, by rfl⟩ : syracuseStep 689187 = 1033781) B1033781
theorem B689203 : Blo 686314 689203 := bstep (se 1 (by rfl) ⟨516902, by rfl⟩ : syracuseStep 689203 = 1033805) B1033805
theorem B689219 : Blo 686314 689219 := bstep (se 1 (by rfl) ⟨516914, by rfl⟩ : syracuseStep 689219 = 1033829) B1033829
theorem B689235 : Blo 686314 689235 := bstep (se 1 (by rfl) ⟨516926, by rfl⟩ : syracuseStep 689235 = 1033853) B1033853
theorem B689251 : Blo 686314 689251 := bstep (se 1 (by rfl) ⟨516938, by rfl⟩ : syracuseStep 689251 = 1033877) B1033877
theorem B689267 : Blo 686314 689267 := bstep (se 1 (by rfl) ⟨516950, by rfl⟩ : syracuseStep 689267 = 1033901) B1033901
theorem B689283 : Blo 686314 689283 := bstep (se 1 (by rfl) ⟨516962, by rfl⟩ : syracuseStep 689283 = 1033925) B1033925
theorem B689299 : Blo 686314 689299 := bstep (se 1 (by rfl) ⟨516974, by rfl⟩ : syracuseStep 689299 = 1033949) B1033949
theorem B689315 : Blo 686314 689315 := bstep (se 1 (by rfl) ⟨516986, by rfl⟩ : syracuseStep 689315 = 1033973) B1033973
theorem B3540131 : Blo 686314 3540131 := bstep (se 1 (by rfl) ⟨2655098, by rfl⟩ : syracuseStep 3540131 = 5310197) B5310197
theorem B689331 : Blo 686314 689331 := bstep (se 1 (by rfl) ⟨516998, by rfl⟩ : syracuseStep 689331 = 1033997) B1033997
theorem B689347 : Blo 686314 689347 := bstep (se 1 (by rfl) ⟨517010, by rfl⟩ : syracuseStep 689347 = 1034021) B1034021
theorem B1574083 : Blo 686314 1574083 := bstep (se 1 (by rfl) ⟨1180562, by rfl⟩ : syracuseStep 1574083 = 2361125) B2361125
theorem B689363 : Blo 686314 689363 := bstep (se 1 (by rfl) ⟨517022, by rfl⟩ : syracuseStep 689363 = 1034045) B1034045
theorem B689379 : Blo 686314 689379 := bstep (se 1 (by rfl) ⟨517034, by rfl⟩ : syracuseStep 689379 = 1034069) B1034069
theorem B689395 : Blo 686314 689395 := bstep (se 1 (by rfl) ⟨517046, by rfl⟩ : syracuseStep 689395 = 1034093) B1034093
theorem B689411 : Blo 686314 689411 := bstep (se 1 (by rfl) ⟨517058, by rfl⟩ : syracuseStep 689411 = 1034117) B1034117
theorem B689427 : Blo 686314 689427 := bstep (se 1 (by rfl) ⟨517070, by rfl⟩ : syracuseStep 689427 = 1034141) B1034141
theorem B689443 : Blo 686314 689443 := bstep (se 1 (by rfl) ⟨517082, by rfl⟩ : syracuseStep 689443 = 1034165) B1034165
theorem B3474737 : Blo 686314 3474737 := bstep (se 2 (by rfl) ⟨1303026, by rfl⟩ : syracuseStep 3474737 = 2606053) B2606053
theorem B689459 : Blo 686314 689459 := bstep (se 1 (by rfl) ⟨517094, by rfl⟩ : syracuseStep 689459 = 1034189) B1034189
theorem B689475 : Blo 686314 689475 := bstep (se 1 (by rfl) ⟨517106, by rfl⟩ : syracuseStep 689475 = 1034213) B1034213
theorem B2327885 : Blo 686314 2327885 := bstep (se 3 (by rfl) ⟨436478, by rfl⟩ : syracuseStep 2327885 = 872957) B872957
theorem B689491 : Blo 686314 689491 := bstep (se 1 (by rfl) ⟨517118, by rfl⟩ : syracuseStep 689491 = 1034237) B1034237
theorem B689507 : Blo 686314 689507 := bstep (se 1 (by rfl) ⟨517130, by rfl⟩ : syracuseStep 689507 = 1034261) B1034261
theorem B689523 : Blo 686314 689523 := bstep (se 1 (by rfl) ⟨517142, by rfl⟩ : syracuseStep 689523 = 1034285) B1034285
theorem B689539 : Blo 686314 689539 := bstep (se 1 (by rfl) ⟨517154, by rfl⟩ : syracuseStep 689539 = 1034309) B1034309
theorem B2327939 : Blo 686314 2327939 := bstep (se 1 (by rfl) ⟨1745954, by rfl⟩ : syracuseStep 2327939 = 3491909) B3491909
theorem B689555 : Blo 686314 689555 := bstep (se 1 (by rfl) ⟨517166, by rfl⟩ : syracuseStep 689555 = 1034333) B1034333
theorem B689571 : Blo 686314 689571 := bstep (se 1 (by rfl) ⟨517178, by rfl⟩ : syracuseStep 689571 = 1034357) B1034357
theorem B1574321 : Blo 686314 1574321 := bstep (se 2 (by rfl) ⟨590370, by rfl⟩ : syracuseStep 1574321 = 1180741) B1180741
theorem B689587 : Blo 686314 689587 := bstep (se 1 (by rfl) ⟨517190, by rfl⟩ : syracuseStep 689587 = 1034381) B1034381
theorem B689603 : Blo 686314 689603 := bstep (se 1 (by rfl) ⟨517202, by rfl⟩ : syracuseStep 689603 = 1034405) B1034405
theorem B689619 : Blo 686314 689619 := bstep (se 1 (by rfl) ⟨517214, by rfl⟩ : syracuseStep 689619 = 1034429) B1034429
theorem B689635 : Blo 686314 689635 := bstep (se 1 (by rfl) ⟨517226, by rfl⟩ : syracuseStep 689635 = 1034453) B1034453
theorem B689651 : Blo 686314 689651 := bstep (se 1 (by rfl) ⟨517238, by rfl⟩ : syracuseStep 689651 = 1034477) B1034477
theorem B689667 : Blo 686314 689667 := bstep (se 1 (by rfl) ⟨517250, by rfl⟩ : syracuseStep 689667 = 1034501) B1034501
theorem B689683 : Blo 686314 689683 := bstep (se 1 (by rfl) ⟨517262, by rfl⟩ : syracuseStep 689683 = 1034525) B1034525
theorem B689699 : Blo 686314 689699 := bstep (se 1 (by rfl) ⟨517274, by rfl⟩ : syracuseStep 689699 = 1034549) B1034549
theorem B689715 : Blo 686314 689715 := bstep (se 1 (by rfl) ⟨517286, by rfl⟩ : syracuseStep 689715 = 1034573) B1034573
theorem B689731 : Blo 686314 689731 := bstep (se 1 (by rfl) ⟨517298, by rfl⟩ : syracuseStep 689731 = 1034597) B1034597
theorem B1115731 : Blo 686314 1115731 := bstep (se 1 (by rfl) ⟨836798, by rfl⟩ : syracuseStep 1115731 = 1673597) B1673597
theorem B689747 : Blo 686314 689747 := bstep (se 1 (by rfl) ⟨517310, by rfl⟩ : syracuseStep 689747 = 1034621) B1034621
theorem B689763 : Blo 686314 689763 := bstep (se 1 (by rfl) ⟨517322, by rfl⟩ : syracuseStep 689763 = 1034645) B1034645
theorem B689779 : Blo 686314 689779 := bstep (se 1 (by rfl) ⟨517334, by rfl⟩ : syracuseStep 689779 = 1034669) B1034669
theorem B689795 : Blo 686314 689795 := bstep (se 1 (by rfl) ⟨517346, by rfl⟩ : syracuseStep 689795 = 1034693) B1034693
theorem B2328209 : Blo 686314 2328209 := bstep (se 2 (by rfl) ⟨873078, by rfl⟩ : syracuseStep 2328209 = 1746157) B1746157
theorem B689811 : Blo 686314 689811 := bstep (se 1 (by rfl) ⟨517358, by rfl⟩ : syracuseStep 689811 = 1034717) B1034717
theorem B689827 : Blo 686314 689827 := bstep (se 1 (by rfl) ⟨517370, by rfl⟩ : syracuseStep 689827 = 1034741) B1034741
theorem B689843 : Blo 686314 689843 := bstep (se 1 (by rfl) ⟨517382, by rfl⟩ : syracuseStep 689843 = 1034765) B1034765
theorem B689859 : Blo 686314 689859 := bstep (se 1 (by rfl) ⟨517394, by rfl⟩ : syracuseStep 689859 = 1034789) B1034789
theorem B6620869 : Blo 686314 6620869 := bstep (se 4 (by rfl) ⟨620706, by rfl⟩ : syracuseStep 6620869 = 1241413) B1241413
theorem B689875 : Blo 686314 689875 := bstep (se 1 (by rfl) ⟨517406, by rfl⟩ : syracuseStep 689875 = 1034813) B1034813
theorem B689891 : Blo 686314 689891 := bstep (se 1 (by rfl) ⟨517418, by rfl⟩ : syracuseStep 689891 = 1034837) B1034837
theorem B689907 : Blo 686314 689907 := bstep (se 1 (by rfl) ⟨517430, by rfl⟩ : syracuseStep 689907 = 1034861) B1034861
theorem B689923 : Blo 686314 689923 := bstep (se 1 (by rfl) ⟨517442, by rfl⟩ : syracuseStep 689923 = 1034885) B1034885
theorem B689939 : Blo 686314 689939 := bstep (se 1 (by rfl) ⟨517454, by rfl⟩ : syracuseStep 689939 = 1034909) B1034909
theorem B689955 : Blo 686314 689955 := bstep (se 1 (by rfl) ⟨517466, by rfl⟩ : syracuseStep 689955 = 1034933) B1034933
theorem B689971 : Blo 686314 689971 := bstep (se 1 (by rfl) ⟨517478, by rfl⟩ : syracuseStep 689971 = 1034957) B1034957
theorem B689987 : Blo 686314 689987 := bstep (se 1 (by rfl) ⟨517490, by rfl⟩ : syracuseStep 689987 = 1034981) B1034981
theorem B2787149 : Blo 686314 2787149 := bstep (se 3 (by rfl) ⟨522590, by rfl⟩ : syracuseStep 2787149 = 1045181) B1045181
theorem B690003 : Blo 686314 690003 := bstep (se 1 (by rfl) ⟨517502, by rfl⟩ : syracuseStep 690003 = 1035005) B1035005
theorem B690019 : Blo 686314 690019 := bstep (se 1 (by rfl) ⟨517514, by rfl⟩ : syracuseStep 690019 = 1035029) B1035029
theorem B690035 : Blo 686314 690035 := bstep (se 1 (by rfl) ⟨517526, by rfl⟩ : syracuseStep 690035 = 1035053) B1035053
theorem B690051 : Blo 686314 690051 := bstep (se 1 (by rfl) ⟨517538, by rfl⟩ : syracuseStep 690051 = 1035077) B1035077
theorem B21202829 : Blo 686314 21202829 := bstep (se 3 (by rfl) ⟨3975530, by rfl⟩ : syracuseStep 21202829 = 7951061) B7951061
theorem B690067 : Blo 686314 690067 := bstep (se 1 (by rfl) ⟨517550, by rfl⟩ : syracuseStep 690067 = 1035101) B1035101
theorem B690083 : Blo 686314 690083 := bstep (se 1 (by rfl) ⟨517562, by rfl⟩ : syracuseStep 690083 = 1035125) B1035125
theorem B690099 : Blo 686314 690099 := bstep (se 1 (by rfl) ⟨517574, by rfl⟩ : syracuseStep 690099 = 1035149) B1035149
theorem B690115 : Blo 686314 690115 := bstep (se 1 (by rfl) ⟨517586, by rfl⟩ : syracuseStep 690115 = 1035173) B1035173
theorem B1738705 : Blo 686314 1738705 := bstep (se 2 (by rfl) ⟨652014, by rfl⟩ : syracuseStep 1738705 = 1304029) B1304029
theorem B690131 : Blo 686314 690131 := bstep (se 1 (by rfl) ⟨517598, by rfl⟩ : syracuseStep 690131 = 1035197) B1035197
theorem B690147 : Blo 686314 690147 := bstep (se 1 (by rfl) ⟨517610, by rfl⟩ : syracuseStep 690147 = 1035221) B1035221
theorem B690163 : Blo 686314 690163 := bstep (se 1 (by rfl) ⟨517622, by rfl⟩ : syracuseStep 690163 = 1035245) B1035245
theorem B690179 : Blo 686314 690179 := bstep (se 1 (by rfl) ⟨517634, by rfl⟩ : syracuseStep 690179 = 1035269) B1035269
theorem B690195 : Blo 686314 690195 := bstep (se 1 (by rfl) ⟨517646, by rfl⟩ : syracuseStep 690195 = 1035293) B1035293
theorem B690211 : Blo 686314 690211 := bstep (se 1 (by rfl) ⟨517658, by rfl⟩ : syracuseStep 690211 = 1035317) B1035317
theorem B690227 : Blo 686314 690227 := bstep (se 1 (by rfl) ⟨517670, by rfl⟩ : syracuseStep 690227 = 1035341) B1035341
theorem B690243 : Blo 686314 690243 := bstep (se 1 (by rfl) ⟨517682, by rfl⟩ : syracuseStep 690243 = 1035365) B1035365
theorem B690259 : Blo 686314 690259 := bstep (se 1 (by rfl) ⟨517694, by rfl⟩ : syracuseStep 690259 = 1035389) B1035389
theorem B690275 : Blo 686314 690275 := bstep (se 1 (by rfl) ⟨517706, by rfl⟩ : syracuseStep 690275 = 1035413) B1035413
theorem B690291 : Blo 686314 690291 := bstep (se 1 (by rfl) ⟨517718, by rfl⟩ : syracuseStep 690291 = 1035437) B1035437
theorem B690307 : Blo 686314 690307 := bstep (se 1 (by rfl) ⟨517730, by rfl⟩ : syracuseStep 690307 = 1035461) B1035461
theorem B2328749 : Blo 686314 2328749 := bstep (se 3 (by rfl) ⟨436640, by rfl⟩ : syracuseStep 2328749 = 873281) B873281
theorem B1738979 : Blo 686314 1738979 := bstep (se 1 (by rfl) ⟨1304234, by rfl⟩ : syracuseStep 1738979 = 2608469) B2608469
theorem B2328803 : Blo 686314 2328803 := bstep (se 1 (by rfl) ⟨1746602, by rfl⟩ : syracuseStep 2328803 = 3493205) B3493205
theorem B1739171 : Blo 686314 1739171 := bstep (se 1 (by rfl) ⟨1304378, by rfl⟩ : syracuseStep 1739171 = 2608757) B2608757
theorem B9439685 : Blo 686314 9439685 := bstep (se 4 (by rfl) ⟨884970, by rfl⟩ : syracuseStep 9439685 = 1769941) B1769941
theorem B2329073 : Blo 686314 2329073 := bstep (se 2 (by rfl) ⟨873402, by rfl⟩ : syracuseStep 2329073 = 1746805) B1746805
theorem B1116769 : Blo 686314 1116769 := bstep (se 2 (by rfl) ⟨418788, by rfl⟩ : syracuseStep 1116769 = 837577) B837577
theorem B3476195 : Blo 686314 3476195 := bstep (se 1 (by rfl) ⟨2607146, by rfl⟩ : syracuseStep 3476195 = 5214293) B5214293
theorem B2755313 : Blo 686314 2755313 := bstep (se 2 (by rfl) ⟨1033242, by rfl⟩ : syracuseStep 2755313 = 2066485) B2066485
theorem B2329613 : Blo 686314 2329613 := bstep (se 3 (by rfl) ⟨436802, by rfl⟩ : syracuseStep 2329613 = 873605) B873605
theorem B2329667 : Blo 686314 2329667 := bstep (se 1 (by rfl) ⟨1747250, by rfl⟩ : syracuseStep 2329667 = 3494501) B3494501
theorem B8359109 : Blo 686314 8359109 := bstep (se 4 (by rfl) ⟨783666, by rfl⟩ : syracuseStep 8359109 = 1567333) B1567333
theorem B2198755 : Blo 686314 2198755 := bstep (se 1 (by rfl) ⟨1649066, by rfl⟩ : syracuseStep 2198755 = 3298133) B3298133
theorem B1740113 : Blo 686314 1740113 := bstep (se 2 (by rfl) ⟨652542, by rfl⟩ : syracuseStep 1740113 = 1305085) B1305085
theorem B1740163 : Blo 686314 1740163 := bstep (se 1 (by rfl) ⟨1305122, by rfl⟩ : syracuseStep 1740163 = 2610245) B2610245
theorem B2788835 : Blo 686314 2788835 := bstep (se 1 (by rfl) ⟨2091626, by rfl⟩ : syracuseStep 2788835 = 4183253) B4183253
theorem B3477005 : Blo 686314 3477005 := bstep (se 3 (by rfl) ⟨651938, by rfl⟩ : syracuseStep 3477005 = 1303877) B1303877
theorem B1740305 : Blo 686314 1740305 := bstep (se 2 (by rfl) ⟨652614, by rfl⟩ : syracuseStep 1740305 = 1305229) B1305229
theorem B2199089 : Blo 686314 2199089 := bstep (se 2 (by rfl) ⟨824658, by rfl⟩ : syracuseStep 2199089 = 1649317) B1649317
theorem B9440995 : Blo 686314 9440995 := bstep (se 1 (by rfl) ⟨7080746, by rfl⟩ : syracuseStep 9440995 = 14161493) B14161493
theorem B8359793 : Blo 686314 8359793 := bstep (se 2 (by rfl) ⟨3134922, by rfl⟩ : syracuseStep 8359793 = 6269845) B6269845
theorem B1544273 : Blo 686314 1544273 := bstep (se 2 (by rfl) ⟨579102, by rfl⟩ : syracuseStep 1544273 = 1158205) B1158205
theorem B1544291 : Blo 686314 1544291 := bstep (se 1 (by rfl) ⟨1158218, by rfl⟩ : syracuseStep 1544291 = 2316437) B2316437
theorem B1544561 : Blo 686314 1544561 := bstep (se 2 (by rfl) ⟨579210, by rfl⟩ : syracuseStep 1544561 = 1158421) B1158421
theorem B1544579 : Blo 686314 1544579 := bstep (se 1 (by rfl) ⟨1158434, by rfl⟩ : syracuseStep 1544579 = 2316869) B2316869
theorem B3314125 : Blo 686314 3314125 := bstep (se 3 (by rfl) ⟨621398, by rfl⟩ : syracuseStep 3314125 = 1242797) B1242797
theorem B1741297 : Blo 686314 1741297 := bstep (se 2 (by rfl) ⟨652986, by rfl⟩ : syracuseStep 1741297 = 1305973) B1305973
theorem B1544849 : Blo 686314 1544849 := bstep (se 2 (by rfl) ⟨579318, by rfl⟩ : syracuseStep 1544849 = 1158637) B1158637
theorem B1544867 : Blo 686314 1544867 := bstep (se 1 (by rfl) ⟨1158650, by rfl⟩ : syracuseStep 1544867 = 2317301) B2317301
theorem B6296305 : Blo 686314 6296305 := bstep (se 2 (by rfl) ⟨2361114, by rfl⟩ : syracuseStep 6296305 = 4722229) B4722229
theorem B1741571 : Blo 686314 1741571 := bstep (se 1 (by rfl) ⟨1306178, by rfl⟩ : syracuseStep 1741571 = 2612357) B2612357
theorem B1545137 : Blo 686314 1545137 := bstep (se 2 (by rfl) ⟨579426, by rfl⟩ : syracuseStep 1545137 = 1158853) B1158853
theorem B1545155 : Blo 686314 1545155 := bstep (se 1 (by rfl) ⟨1158866, by rfl⟩ : syracuseStep 1545155 = 2317733) B2317733
theorem B1741763 : Blo 686314 1741763 := bstep (se 1 (by rfl) ⟨1306322, by rfl⟩ : syracuseStep 1741763 = 2612645) B2612645
theorem B1119329 : Blo 686314 1119329 := bstep (se 2 (by rfl) ⟨419748, by rfl⟩ : syracuseStep 1119329 = 839497) B839497
theorem B3970225 : Blo 686314 3970225 := bstep (se 2 (by rfl) ⟨1488834, by rfl⟩ : syracuseStep 3970225 = 2977669) B2977669
theorem B1545425 : Blo 686314 1545425 := bstep (se 2 (by rfl) ⟨579534, by rfl⟩ : syracuseStep 1545425 = 1159069) B1159069
theorem B1545443 : Blo 686314 1545443 := bstep (se 1 (by rfl) ⟨1159082, by rfl⟩ : syracuseStep 1545443 = 2318165) B2318165
theorem B12719501 : Blo 686314 12719501 := bstep (se 3 (by rfl) ⟨2384906, by rfl⟩ : syracuseStep 12719501 = 4769813) B4769813
theorem B1545713 : Blo 686314 1545713 := bstep (se 2 (by rfl) ⟨579642, by rfl⟩ : syracuseStep 1545713 = 1159285) B1159285
theorem B1545731 : Blo 686314 1545731 := bstep (se 1 (by rfl) ⟨1159298, by rfl⟩ : syracuseStep 1545731 = 2318597) B2318597
theorem B824899 : Blo 686314 824899 := bstep (se 1 (by rfl) ⟨618674, by rfl⟩ : syracuseStep 824899 = 1237349) B1237349
theorem B2201165 : Blo 686314 2201165 := bstep (se 3 (by rfl) ⟨412718, by rfl⟩ : syracuseStep 2201165 = 825437) B825437
theorem B1546001 : Blo 686314 1546001 := bstep (se 2 (by rfl) ⟨579750, by rfl⟩ : syracuseStep 1546001 = 1159501) B1159501
theorem B1546019 : Blo 686314 1546019 := bstep (se 1 (by rfl) ⟨1159514, by rfl⟩ : syracuseStep 1546019 = 2319029) B2319029
theorem B1742705 : Blo 686314 1742705 := bstep (se 2 (by rfl) ⟨653514, by rfl⟩ : syracuseStep 1742705 = 1307029) B1307029
theorem B1742755 : Blo 686314 1742755 := bstep (se 1 (by rfl) ⟨1307066, by rfl⟩ : syracuseStep 1742755 = 2614133) B2614133
theorem B1120243 : Blo 686314 1120243 := bstep (se 1 (by rfl) ⟨840182, by rfl⟩ : syracuseStep 1120243 = 1680365) B1680365
theorem B825379 : Blo 686314 825379 := bstep (se 1 (by rfl) ⟨619034, by rfl⟩ : syracuseStep 825379 = 1238069) B1238069
theorem B1546289 : Blo 686314 1546289 := bstep (se 2 (by rfl) ⟨579858, by rfl⟩ : syracuseStep 1546289 = 1159717) B1159717
theorem B1742897 : Blo 686314 1742897 := bstep (se 2 (by rfl) ⟨653586, by rfl⟩ : syracuseStep 1742897 = 1307173) B1307173
theorem B1546307 : Blo 686314 1546307 := bstep (se 1 (by rfl) ⟨1159730, by rfl⟩ : syracuseStep 1546307 = 2319461) B2319461
theorem B16718021 : Blo 686314 16718021 := bstep (se 4 (by rfl) ⟨1567314, by rfl⟩ : syracuseStep 16718021 = 3134629) B3134629
theorem B8821061 : Blo 686314 8821061 := bstep (se 4 (by rfl) ⟨826974, by rfl⟩ : syracuseStep 8821061 = 1653949) B1653949
theorem B1546577 : Blo 686314 1546577 := bstep (se 2 (by rfl) ⟨579966, by rfl⟩ : syracuseStep 1546577 = 1159933) B1159933
theorem B1546595 : Blo 686314 1546595 := bstep (se 1 (by rfl) ⟨1159946, by rfl⟩ : syracuseStep 1546595 = 2319893) B2319893
theorem B3479921 : Blo 686314 3479921 := bstep (se 2 (by rfl) ⟨1304970, by rfl⟩ : syracuseStep 3479921 = 2609941) B2609941
theorem B4397489 : Blo 686314 4397489 := bstep (se 2 (by rfl) ⟨1649058, by rfl⟩ : syracuseStep 4397489 = 3298117) B3298117
theorem B1546865 : Blo 686314 1546865 := bstep (se 2 (by rfl) ⟨580074, by rfl⟩ : syracuseStep 1546865 = 1160149) B1160149
theorem B1546883 : Blo 686314 1546883 := bstep (se 1 (by rfl) ⟨1160162, by rfl⟩ : syracuseStep 1546883 = 2320325) B2320325
theorem B1547153 : Blo 686314 1547153 := bstep (se 2 (by rfl) ⟨580182, by rfl⟩ : syracuseStep 1547153 = 1160365) B1160365
theorem B826259 : Blo 686314 826259 := bstep (se 1 (by rfl) ⟨619694, by rfl⟩ : syracuseStep 826259 = 1239389) B1239389
theorem B1547171 : Blo 686314 1547171 := bstep (se 1 (by rfl) ⟨1160378, by rfl⟩ : syracuseStep 1547171 = 2320757) B2320757
theorem B1743889 : Blo 686314 1743889 := bstep (se 2 (by rfl) ⟨653958, by rfl⟩ : syracuseStep 1743889 = 1307917) B1307917
theorem B1547441 : Blo 686314 1547441 := bstep (se 2 (by rfl) ⟨580290, by rfl⟩ : syracuseStep 1547441 = 1160581) B1160581
theorem B1547459 : Blo 686314 1547459 := bstep (se 1 (by rfl) ⟨1160594, by rfl⟩ : syracuseStep 1547459 = 2321189) B2321189
theorem B1744163 : Blo 686314 1744163 := bstep (se 1 (by rfl) ⟨1308122, by rfl⟩ : syracuseStep 1744163 = 2616245) B2616245
theorem B2202947 : Blo 686314 2202947 := bstep (se 1 (by rfl) ⟨1652210, by rfl⟩ : syracuseStep 2202947 = 3304421) B3304421
theorem B1547729 : Blo 686314 1547729 := bstep (se 2 (by rfl) ⟨580398, by rfl⟩ : syracuseStep 1547729 = 1160797) B1160797
theorem B1547747 : Blo 686314 1547747 := bstep (se 1 (by rfl) ⟨1160810, by rfl⟩ : syracuseStep 1547747 = 2321621) B2321621
theorem B1744355 : Blo 686314 1744355 := bstep (se 1 (by rfl) ⟨1308266, by rfl⟩ : syracuseStep 1744355 = 2616533) B2616533
theorem B1548017 : Blo 686314 1548017 := bstep (se 2 (by rfl) ⟨580506, by rfl⟩ : syracuseStep 1548017 = 1161013) B1161013
theorem B1548035 : Blo 686314 1548035 := bstep (se 1 (by rfl) ⟨1161026, by rfl⟩ : syracuseStep 1548035 = 2322053) B2322053
theorem B3481379 : Blo 686314 3481379 := bstep (se 1 (by rfl) ⟨2611034, by rfl⟩ : syracuseStep 3481379 = 5222069) B5222069
theorem B4398947 : Blo 686314 4398947 := bstep (se 1 (by rfl) ⟨3299210, by rfl⟩ : syracuseStep 4398947 = 6598421) B6598421
theorem B1548305 : Blo 686314 1548305 := bstep (se 2 (by rfl) ⟨580614, by rfl⟩ : syracuseStep 1548305 = 1161229) B1161229
theorem B1548323 : Blo 686314 1548323 := bstep (se 1 (by rfl) ⟨1161242, by rfl⟩ : syracuseStep 1548323 = 2322485) B2322485
theorem B1548593 : Blo 686314 1548593 := bstep (se 2 (by rfl) ⟨580722, by rfl⟩ : syracuseStep 1548593 = 1161445) B1161445
theorem B1548611 : Blo 686314 1548611 := bstep (se 1 (by rfl) ⟨1161458, by rfl⟩ : syracuseStep 1548611 = 2322917) B2322917
theorem B1745297 : Blo 686314 1745297 := bstep (se 2 (by rfl) ⟨654486, by rfl⟩ : syracuseStep 1745297 = 1308973) B1308973
theorem B1745347 : Blo 686314 1745347 := bstep (se 1 (by rfl) ⟨1309010, by rfl⟩ : syracuseStep 1745347 = 2618021) B2618021
theorem B5022179 : Blo 686314 5022179 := bstep (se 1 (by rfl) ⟨3766634, by rfl⟩ : syracuseStep 5022179 = 7533269) B7533269
theorem B3482189 : Blo 686314 3482189 := bstep (se 3 (by rfl) ⟨652910, by rfl⟩ : syracuseStep 3482189 = 1305821) B1305821
theorem B1745489 : Blo 686314 1745489 := bstep (se 2 (by rfl) ⟨654558, by rfl⟩ : syracuseStep 1745489 = 1309117) B1309117
theorem B1548881 : Blo 686314 1548881 := bstep (se 2 (by rfl) ⟨580830, by rfl⟩ : syracuseStep 1548881 = 1161661) B1161661
theorem B1548899 : Blo 686314 1548899 := bstep (se 1 (by rfl) ⟨1161674, by rfl⟩ : syracuseStep 1548899 = 2323349) B2323349
theorem B2204291 : Blo 686314 2204291 := bstep (se 1 (by rfl) ⟨1653218, by rfl⟩ : syracuseStep 2204291 = 3306437) B3306437
theorem B1549169 : Blo 686314 1549169 := bstep (se 2 (by rfl) ⟨580938, by rfl⟩ : syracuseStep 1549169 = 1161877) B1161877
theorem B1549187 : Blo 686314 1549187 := bstep (se 1 (by rfl) ⟨1161890, by rfl⟩ : syracuseStep 1549187 = 2323781) B2323781
theorem B1549457 : Blo 686314 1549457 := bstep (se 2 (by rfl) ⟨581046, by rfl⟩ : syracuseStep 1549457 = 1162093) B1162093
theorem B1549475 : Blo 686314 1549475 := bstep (se 1 (by rfl) ⟨1162106, by rfl⟩ : syracuseStep 1549475 = 2324213) B2324213
theorem B828643 : Blo 686314 828643 := bstep (se 1 (by rfl) ⟨621482, by rfl⟩ : syracuseStep 828643 = 1242965) B1242965
theorem B7841123 : Blo 686314 7841123 := bstep (se 1 (by rfl) ⟨5880842, by rfl⟩ : syracuseStep 7841123 = 11761685) B11761685
theorem B1549745 : Blo 686314 1549745 := bstep (se 2 (by rfl) ⟨581154, by rfl⟩ : syracuseStep 1549745 = 1162309) B1162309
theorem B1549763 : Blo 686314 1549763 := bstep (se 1 (by rfl) ⟨1162322, by rfl⟩ : syracuseStep 1549763 = 2324645) B2324645
theorem B4400689 : Blo 686314 4400689 := bstep (se 2 (by rfl) ⟨1650258, by rfl⟩ : syracuseStep 4400689 = 3300517) B3300517
theorem B1746481 : Blo 686314 1746481 := bstep (se 2 (by rfl) ⟨654930, by rfl⟩ : syracuseStep 1746481 = 1309861) B1309861
theorem B1550033 : Blo 686314 1550033 := bstep (se 2 (by rfl) ⟨581262, by rfl⟩ : syracuseStep 1550033 = 1162525) B1162525
theorem B1550051 : Blo 686314 1550051 := bstep (se 1 (by rfl) ⟨1162538, by rfl⟩ : syracuseStep 1550051 = 2325077) B2325077
theorem B1746755 : Blo 686314 1746755 := bstep (se 1 (by rfl) ⟨1310066, by rfl⟩ : syracuseStep 1746755 = 2620133) B2620133
theorem B1550321 : Blo 686314 1550321 := bstep (se 2 (by rfl) ⟨581370, by rfl⟩ : syracuseStep 1550321 = 1162741) B1162741
theorem B1550339 : Blo 686314 1550339 := bstep (se 1 (by rfl) ⟨1162754, by rfl⟩ : syracuseStep 1550339 = 2325509) B2325509
theorem B1746947 : Blo 686314 1746947 := bstep (se 1 (by rfl) ⟨1310210, by rfl⟩ : syracuseStep 1746947 = 2620421) B2620421
theorem B3909809 : Blo 686314 3909809 := bstep (se 2 (by rfl) ⟨1466178, by rfl⟩ : syracuseStep 3909809 = 2932357) B2932357
theorem B1550609 : Blo 686314 1550609 := bstep (se 2 (by rfl) ⟨581478, by rfl⟩ : syracuseStep 1550609 = 1162957) B1162957
theorem B1550627 : Blo 686314 1550627 := bstep (se 1 (by rfl) ⟨1162970, by rfl⟩ : syracuseStep 1550627 = 2325941) B2325941
theorem B6596963 : Blo 686314 6596963 := bstep (se 1 (by rfl) ⟨4947722, by rfl⟩ : syracuseStep 6596963 = 9895445) B9895445
theorem B2206061 : Blo 686314 2206061 := bstep (se 3 (by rfl) ⟨413636, by rfl⟩ : syracuseStep 2206061 = 827273) B827273
theorem B993665 : Blo 686314 993665 := bstep (se 2 (by rfl) ⟨372624, by rfl⟩ : syracuseStep 993665 = 745249) B745249
theorem B1550897 : Blo 686314 1550897 := bstep (se 2 (by rfl) ⟨581586, by rfl⟩ : syracuseStep 1550897 = 1163173) B1163173
theorem B1550915 : Blo 686314 1550915 := bstep (se 1 (by rfl) ⟨1163186, by rfl⟩ : syracuseStep 1550915 = 2326373) B2326373
theorem B17836685 : Blo 686314 17836685 := bstep (se 3 (by rfl) ⟨3344378, by rfl⟩ : syracuseStep 17836685 = 6688757) B6688757
theorem B928433 : Blo 686314 928433 := bstep (se 2 (by rfl) ⟨348162, by rfl⟩ : syracuseStep 928433 = 696325) B696325
theorem B928465 : Blo 686314 928465 := bstep (se 2 (by rfl) ⟨348174, by rfl⟩ : syracuseStep 928465 = 696349) B696349
theorem B1649443 : Blo 686314 1649443 := bstep (se 1 (by rfl) ⟨1237082, by rfl⟩ : syracuseStep 1649443 = 2474165) B2474165
theorem B1551185 : Blo 686314 1551185 := bstep (se 2 (by rfl) ⟨581694, by rfl⟩ : syracuseStep 1551185 = 1163389) B1163389
theorem B1551203 : Blo 686314 1551203 := bstep (se 1 (by rfl) ⟨1163402, by rfl⟩ : syracuseStep 1551203 = 2326805) B2326805
theorem B3976069 : Blo 686314 3976069 := bstep (se 4 (by rfl) ⟨372756, by rfl⟩ : syracuseStep 3976069 = 745513) B745513
theorem B994403 : Blo 686314 994403 := bstep (se 1 (by rfl) ⟨745802, by rfl⟩ : syracuseStep 994403 = 1491605) B1491605
theorem B1551473 : Blo 686314 1551473 := bstep (se 2 (by rfl) ⟨581802, by rfl⟩ : syracuseStep 1551473 = 1163605) B1163605
theorem B1158259 : Blo 686314 1158259 := bstep (se 1 (by rfl) ⟨868694, by rfl⟩ : syracuseStep 1158259 = 1737389) B1737389
theorem B1551491 : Blo 686314 1551491 := bstep (se 1 (by rfl) ⟨1163618, by rfl⟩ : syracuseStep 1551491 = 2327237) B2327237
theorem B12102797 : Blo 686314 12102797 := bstep (se 3 (by rfl) ⟨2269274, by rfl⟩ : syracuseStep 12102797 = 4538549) B4538549
theorem B1158401 : Blo 686314 1158401 := bstep (se 2 (by rfl) ⟨434400, by rfl⟩ : syracuseStep 1158401 = 868801) B868801
theorem B1158529 : Blo 686314 1158529 := bstep (se 2 (by rfl) ⟨434448, by rfl⟩ : syracuseStep 1158529 = 868897) B868897
theorem B1551761 : Blo 686314 1551761 := bstep (se 2 (by rfl) ⟨581910, by rfl⟩ : syracuseStep 1551761 = 1163821) B1163821
theorem B1158563 : Blo 686314 1158563 := bstep (se 1 (by rfl) ⟨868922, by rfl⟩ : syracuseStep 1158563 = 1737845) B1737845
theorem B1551779 : Blo 686314 1551779 := bstep (se 1 (by rfl) ⟨1163834, by rfl⟩ : syracuseStep 1551779 = 2327669) B2327669
theorem B3485105 : Blo 686314 3485105 := bstep (se 2 (by rfl) ⟨1306914, by rfl⟩ : syracuseStep 3485105 = 2613829) B2613829
theorem B4402637 : Blo 686314 4402637 := bstep (se 3 (by rfl) ⟨825494, by rfl⟩ : syracuseStep 4402637 = 1650989) B1650989
theorem B1158691 : Blo 686314 1158691 := bstep (se 1 (by rfl) ⟨869018, by rfl⟩ : syracuseStep 1158691 = 1738037) B1738037
theorem B3911267 : Blo 686314 3911267 := bstep (se 1 (by rfl) ⟨2933450, by rfl⟩ : syracuseStep 3911267 = 5866901) B5866901
theorem B1650289 : Blo 686314 1650289 := bstep (se 2 (by rfl) ⟨618858, by rfl⟩ : syracuseStep 1650289 = 1237717) B1237717
theorem B1158833 : Blo 686314 1158833 := bstep (se 2 (by rfl) ⟨434562, by rfl⟩ : syracuseStep 1158833 = 869125) B869125
theorem B1552049 : Blo 686314 1552049 := bstep (se 2 (by rfl) ⟨582018, by rfl⟩ : syracuseStep 1552049 = 1164037) B1164037
theorem B1552067 : Blo 686314 1552067 := bstep (se 1 (by rfl) ⟨1164050, by rfl⟩ : syracuseStep 1552067 = 2328101) B2328101
theorem B1158961 : Blo 686314 1158961 := bstep (se 2 (by rfl) ⟨434610, by rfl⟩ : syracuseStep 1158961 = 869221) B869221
theorem B1158995 : Blo 686314 1158995 := bstep (se 1 (by rfl) ⟨869246, by rfl⟩ : syracuseStep 1158995 = 1738493) B1738493
theorem B1552337 : Blo 686314 1552337 := bstep (se 2 (by rfl) ⟨582126, by rfl⟩ : syracuseStep 1552337 = 1164253) B1164253
theorem B1159123 : Blo 686314 1159123 := bstep (se 1 (by rfl) ⟨869342, by rfl⟩ : syracuseStep 1159123 = 1738685) B1738685
theorem B1552355 : Blo 686314 1552355 := bstep (se 1 (by rfl) ⟨1164266, by rfl⟩ : syracuseStep 1552355 = 2328533) B2328533
theorem B1159265 : Blo 686314 1159265 := bstep (se 2 (by rfl) ⟨434724, by rfl⟩ : syracuseStep 1159265 = 869449) B869449
theorem B1159393 : Blo 686314 1159393 := bstep (se 2 (by rfl) ⟨434772, by rfl⟩ : syracuseStep 1159393 = 869545) B869545
theorem B1552625 : Blo 686314 1552625 := bstep (se 2 (by rfl) ⟨582234, by rfl⟩ : syracuseStep 1552625 = 1164469) B1164469
theorem B1159427 : Blo 686314 1159427 := bstep (se 1 (by rfl) ⟨869570, by rfl⟩ : syracuseStep 1159427 = 1739141) B1739141
theorem B1552643 : Blo 686314 1552643 := bstep (se 1 (by rfl) ⟨1164482, by rfl⟩ : syracuseStep 1552643 = 2328965) B2328965
theorem B1913101 : Blo 686314 1913101 := bstep (se 3 (by rfl) ⟨358706, by rfl⟩ : syracuseStep 1913101 = 717413) B717413
theorem B1159555 : Blo 686314 1159555 := bstep (se 1 (by rfl) ⟨869666, by rfl⟩ : syracuseStep 1159555 = 1739333) B1739333
theorem B1159697 : Blo 686314 1159697 := bstep (se 2 (by rfl) ⟨434886, by rfl⟩ : syracuseStep 1159697 = 869773) B869773
theorem B1552913 : Blo 686314 1552913 := bstep (se 2 (by rfl) ⟨582342, by rfl⟩ : syracuseStep 1552913 = 1164685) B1164685
theorem B1552931 : Blo 686314 1552931 := bstep (se 1 (by rfl) ⟨1164698, by rfl⟩ : syracuseStep 1552931 = 2329397) B2329397
theorem B1159825 : Blo 686314 1159825 := bstep (se 2 (by rfl) ⟨434934, by rfl⟩ : syracuseStep 1159825 = 869869) B869869
theorem B1159859 : Blo 686314 1159859 := bstep (se 1 (by rfl) ⟨869894, by rfl⟩ : syracuseStep 1159859 = 1739789) B1739789
theorem B1553201 : Blo 686314 1553201 := bstep (se 2 (by rfl) ⟨582450, by rfl⟩ : syracuseStep 1553201 = 1164901) B1164901
theorem B1159987 : Blo 686314 1159987 := bstep (se 1 (by rfl) ⟨869990, by rfl⟩ : syracuseStep 1159987 = 1739981) B1739981
theorem B3486563 : Blo 686314 3486563 := bstep (se 1 (by rfl) ⟨2614922, by rfl⟩ : syracuseStep 3486563 = 5229845) B5229845
theorem B4699043 : Blo 686314 4699043 := bstep (se 1 (by rfl) ⟨3524282, by rfl⟩ : syracuseStep 4699043 = 7048565) B7048565
theorem B1160129 : Blo 686314 1160129 := bstep (se 2 (by rfl) ⟨435048, by rfl⟩ : syracuseStep 1160129 = 870097) B870097
theorem B734179 : Blo 686314 734179 := bstep (se 1 (by rfl) ⟨550634, by rfl⟩ : syracuseStep 734179 = 1101269) B1101269
theorem B1160257 : Blo 686314 1160257 := bstep (se 2 (by rfl) ⟨435096, by rfl⟩ : syracuseStep 1160257 = 870193) B870193
theorem B1160291 : Blo 686314 1160291 := bstep (se 1 (by rfl) ⟨870218, by rfl⟩ : syracuseStep 1160291 = 1740437) B1740437
theorem B16954595 : Blo 686314 16954595 := bstep (se 1 (by rfl) ⟨12715946, by rfl⟩ : syracuseStep 16954595 = 25431893) B25431893
theorem B1160419 : Blo 686314 1160419 := bstep (se 1 (by rfl) ⟨870314, by rfl⟩ : syracuseStep 1160419 = 1740629) B1740629
theorem B1029473 : Blo 686314 1029473 := bstep (se 2 (by rfl) ⟨386052, by rfl⟩ : syracuseStep 1029473 = 772105) B772105
theorem B1160561 : Blo 686314 1160561 := bstep (se 2 (by rfl) ⟨435210, by rfl⟩ : syracuseStep 1160561 = 870421) B870421
theorem B1029491 : Blo 686314 1029491 := bstep (se 1 (by rfl) ⟨772118, by rfl⟩ : syracuseStep 1029491 = 1544237) B1544237
theorem B1029521 : Blo 686314 1029521 := bstep (se 2 (by rfl) ⟨386070, by rfl⟩ : syracuseStep 1029521 = 772141) B772141
theorem B1029539 : Blo 686314 1029539 := bstep (se 1 (by rfl) ⟨772154, by rfl⟩ : syracuseStep 1029539 = 1544309) B1544309
theorem B734627 : Blo 686314 734627 := bstep (se 1 (by rfl) ⟨550970, by rfl⟩ : syracuseStep 734627 = 1101941) B1101941
theorem B1029569 : Blo 686314 1029569 := bstep (se 2 (by rfl) ⟨386088, by rfl⟩ : syracuseStep 1029569 = 772177) B772177
theorem B1029587 : Blo 686314 1029587 := bstep (se 1 (by rfl) ⟨772190, by rfl⟩ : syracuseStep 1029587 = 1544381) B1544381
theorem B1029617 : Blo 686314 1029617 := bstep (se 2 (by rfl) ⟨386106, by rfl⟩ : syracuseStep 1029617 = 772213) B772213
theorem B1160689 : Blo 686314 1160689 := bstep (se 2 (by rfl) ⟨435258, by rfl⟩ : syracuseStep 1160689 = 870517) B870517
theorem B2209265 : Blo 686314 2209265 := bstep (se 2 (by rfl) ⟨828474, by rfl⟩ : syracuseStep 2209265 = 1656949) B1656949
theorem B1029635 : Blo 686314 1029635 := bstep (se 1 (by rfl) ⟨772226, by rfl⟩ : syracuseStep 1029635 = 1544453) B1544453
theorem B1160723 : Blo 686314 1160723 := bstep (se 1 (by rfl) ⟨870542, by rfl⟩ : syracuseStep 1160723 = 1741085) B1741085
theorem B1029665 : Blo 686314 1029665 := bstep (se 2 (by rfl) ⟨386124, by rfl⟩ : syracuseStep 1029665 = 772249) B772249
theorem B2209315 : Blo 686314 2209315 := bstep (se 1 (by rfl) ⟨1656986, by rfl⟩ : syracuseStep 2209315 = 3313973) B3313973
theorem B1029683 : Blo 686314 1029683 := bstep (se 1 (by rfl) ⟨772262, by rfl⟩ : syracuseStep 1029683 = 1544525) B1544525
theorem B1029713 : Blo 686314 1029713 := bstep (se 2 (by rfl) ⟨386142, by rfl⟩ : syracuseStep 1029713 = 772285) B772285
theorem B1029731 : Blo 686314 1029731 := bstep (se 1 (by rfl) ⟨772298, by rfl⟩ : syracuseStep 1029731 = 1544597) B1544597
theorem B1029761 : Blo 686314 1029761 := bstep (se 2 (by rfl) ⟨386160, by rfl⟩ : syracuseStep 1029761 = 772321) B772321
theorem B3487373 : Blo 686314 3487373 := bstep (se 3 (by rfl) ⟨653882, by rfl⟩ : syracuseStep 3487373 = 1307765) B1307765
theorem B1029779 : Blo 686314 1029779 := bstep (se 1 (by rfl) ⟨772334, by rfl⟩ : syracuseStep 1029779 = 1544669) B1544669
theorem B1160851 : Blo 686314 1160851 := bstep (se 1 (by rfl) ⟨870638, by rfl⟩ : syracuseStep 1160851 = 1741277) B1741277
theorem B1029809 : Blo 686314 1029809 := bstep (se 2 (by rfl) ⟨386178, by rfl⟩ : syracuseStep 1029809 = 772357) B772357
theorem B1029827 : Blo 686314 1029827 := bstep (se 1 (by rfl) ⟨772370, by rfl⟩ : syracuseStep 1029827 = 1544741) B1544741
theorem B1029857 : Blo 686314 1029857 := bstep (se 2 (by rfl) ⟨386196, by rfl⟩ : syracuseStep 1029857 = 772393) B772393
theorem B1029875 : Blo 686314 1029875 := bstep (se 1 (by rfl) ⟨772406, by rfl⟩ : syracuseStep 1029875 = 1544813) B1544813
theorem B1029905 : Blo 686314 1029905 := bstep (se 2 (by rfl) ⟨386214, by rfl⟩ : syracuseStep 1029905 = 772429) B772429
theorem B1455889 : Blo 686314 1455889 := bstep (se 2 (by rfl) ⟨545958, by rfl⟩ : syracuseStep 1455889 = 1091917) B1091917
theorem B1160993 : Blo 686314 1160993 := bstep (se 2 (by rfl) ⟨435372, by rfl⟩ : syracuseStep 1160993 = 870745) B870745
theorem B1029923 : Blo 686314 1029923 := bstep (se 1 (by rfl) ⟨772442, by rfl⟩ : syracuseStep 1029923 = 1544885) B1544885
theorem B1029953 : Blo 686314 1029953 := bstep (se 2 (by rfl) ⟨386232, by rfl⟩ : syracuseStep 1029953 = 772465) B772465
theorem B1029971 : Blo 686314 1029971 := bstep (se 1 (by rfl) ⟨772478, by rfl⟩ : syracuseStep 1029971 = 1544957) B1544957
theorem B1030001 : Blo 686314 1030001 := bstep (se 2 (by rfl) ⟨386250, by rfl⟩ : syracuseStep 1030001 = 772501) B772501
theorem B1030019 : Blo 686314 1030019 := bstep (se 1 (by rfl) ⟨772514, by rfl⟩ : syracuseStep 1030019 = 1545029) B1545029
theorem B1030049 : Blo 686314 1030049 := bstep (se 2 (by rfl) ⟨386268, by rfl⟩ : syracuseStep 1030049 = 772537) B772537
theorem B1161121 : Blo 686314 1161121 := bstep (se 2 (by rfl) ⟨435420, by rfl⟩ : syracuseStep 1161121 = 870841) B870841
theorem B1030067 : Blo 686314 1030067 := bstep (se 1 (by rfl) ⟨772550, by rfl⟩ : syracuseStep 1030067 = 1545101) B1545101
theorem B1161155 : Blo 686314 1161155 := bstep (se 1 (by rfl) ⟨870866, by rfl⟩ : syracuseStep 1161155 = 1741733) B1741733
theorem B5879749 : Blo 686314 5879749 := bstep (se 4 (by rfl) ⟨551226, by rfl⟩ : syracuseStep 5879749 = 1102453) B1102453
theorem B1030097 : Blo 686314 1030097 := bstep (se 2 (by rfl) ⟨386286, by rfl⟩ : syracuseStep 1030097 = 772573) B772573
theorem B1030115 : Blo 686314 1030115 := bstep (se 1 (by rfl) ⟨772586, by rfl⟩ : syracuseStep 1030115 = 1545173) B1545173
theorem B1030145 : Blo 686314 1030145 := bstep (se 2 (by rfl) ⟨386304, by rfl⟩ : syracuseStep 1030145 = 772609) B772609
theorem B1030163 : Blo 686314 1030163 := bstep (se 1 (by rfl) ⟨772622, by rfl⟩ : syracuseStep 1030163 = 1545245) B1545245
theorem B1030193 : Blo 686314 1030193 := bstep (se 2 (by rfl) ⟨386322, by rfl⟩ : syracuseStep 1030193 = 772645) B772645
theorem B1030211 : Blo 686314 1030211 := bstep (se 1 (by rfl) ⟨772658, by rfl⟩ : syracuseStep 1030211 = 1545317) B1545317
theorem B1161283 : Blo 686314 1161283 := bstep (se 1 (by rfl) ⟨870962, by rfl⟩ : syracuseStep 1161283 = 1741925) B1741925
theorem B1030241 : Blo 686314 1030241 := bstep (se 2 (by rfl) ⟨386340, by rfl⟩ : syracuseStep 1030241 = 772681) B772681
theorem B1030259 : Blo 686314 1030259 := bstep (se 1 (by rfl) ⟨772694, by rfl⟩ : syracuseStep 1030259 = 1545389) B1545389
theorem B1030289 : Blo 686314 1030289 := bstep (se 2 (by rfl) ⟨386358, by rfl⟩ : syracuseStep 1030289 = 772717) B772717
theorem B1030307 : Blo 686314 1030307 := bstep (se 1 (by rfl) ⟨772730, by rfl⟩ : syracuseStep 1030307 = 1545461) B1545461
theorem B3356849 : Blo 686314 3356849 := bstep (se 2 (by rfl) ⟨1258818, by rfl⟩ : syracuseStep 3356849 = 2517637) B2517637
theorem B1030337 : Blo 686314 1030337 := bstep (se 2 (by rfl) ⟨386376, by rfl⟩ : syracuseStep 1030337 = 772753) B772753
theorem B1161425 : Blo 686314 1161425 := bstep (se 2 (by rfl) ⟨435534, by rfl⟩ : syracuseStep 1161425 = 871069) B871069
theorem B1030355 : Blo 686314 1030355 := bstep (se 1 (by rfl) ⟨772766, by rfl⟩ : syracuseStep 1030355 = 1545533) B1545533
theorem B1030385 : Blo 686314 1030385 := bstep (se 2 (by rfl) ⟨386394, by rfl⟩ : syracuseStep 1030385 = 772789) B772789
theorem B1030403 : Blo 686314 1030403 := bstep (se 1 (by rfl) ⟨772802, by rfl⟩ : syracuseStep 1030403 = 1545605) B1545605
theorem B1030433 : Blo 686314 1030433 := bstep (se 2 (by rfl) ⟨386412, by rfl⟩ : syracuseStep 1030433 = 772825) B772825
theorem B1030451 : Blo 686314 1030451 := bstep (se 1 (by rfl) ⟨772838, by rfl⟩ : syracuseStep 1030451 = 1545677) B1545677
theorem B1030481 : Blo 686314 1030481 := bstep (se 2 (by rfl) ⟨386430, by rfl⟩ : syracuseStep 1030481 = 772861) B772861
theorem B1161553 : Blo 686314 1161553 := bstep (se 2 (by rfl) ⟨435582, by rfl⟩ : syracuseStep 1161553 = 871165) B871165
theorem B1030499 : Blo 686314 1030499 := bstep (se 1 (by rfl) ⟨772874, by rfl⟩ : syracuseStep 1030499 = 1545749) B1545749
theorem B2210161 : Blo 686314 2210161 := bstep (se 2 (by rfl) ⟨828810, by rfl⟩ : syracuseStep 2210161 = 1657621) B1657621
theorem B1161587 : Blo 686314 1161587 := bstep (se 1 (by rfl) ⟨871190, by rfl⟩ : syracuseStep 1161587 = 1742381) B1742381
theorem B1030529 : Blo 686314 1030529 := bstep (se 2 (by rfl) ⟨386448, by rfl⟩ : syracuseStep 1030529 = 772897) B772897
theorem B1030547 : Blo 686314 1030547 := bstep (se 1 (by rfl) ⟨772910, by rfl⟩ : syracuseStep 1030547 = 1545821) B1545821
theorem B1030577 : Blo 686314 1030577 := bstep (se 2 (by rfl) ⟨386466, by rfl⟩ : syracuseStep 1030577 = 772933) B772933
theorem B1030595 : Blo 686314 1030595 := bstep (se 1 (by rfl) ⟨772946, by rfl⟩ : syracuseStep 1030595 = 1545893) B1545893
theorem B1030625 : Blo 686314 1030625 := bstep (se 2 (by rfl) ⟨386484, by rfl⟩ : syracuseStep 1030625 = 772969) B772969
theorem B1030643 : Blo 686314 1030643 := bstep (se 1 (by rfl) ⟨772982, by rfl⟩ : syracuseStep 1030643 = 1545965) B1545965
theorem B1161715 : Blo 686314 1161715 := bstep (se 1 (by rfl) ⟨871286, by rfl⟩ : syracuseStep 1161715 = 1742573) B1742573
theorem B1030673 : Blo 686314 1030673 := bstep (se 2 (by rfl) ⟨386502, by rfl⟩ : syracuseStep 1030673 = 773005) B773005
theorem B1030691 : Blo 686314 1030691 := bstep (se 1 (by rfl) ⟨773018, by rfl⟩ : syracuseStep 1030691 = 1546037) B1546037
theorem B1030721 : Blo 686314 1030721 := bstep (se 2 (by rfl) ⟨386520, by rfl⟩ : syracuseStep 1030721 = 773041) B773041
theorem B1030739 : Blo 686314 1030739 := bstep (se 1 (by rfl) ⟨773054, by rfl⟩ : syracuseStep 1030739 = 1546109) B1546109
theorem B1587811 : Blo 686314 1587811 := bstep (se 1 (by rfl) ⟨1190858, by rfl⟩ : syracuseStep 1587811 = 2381717) B2381717
theorem B1030769 : Blo 686314 1030769 := bstep (se 2 (by rfl) ⟨386538, by rfl⟩ : syracuseStep 1030769 = 773077) B773077
theorem B1161857 : Blo 686314 1161857 := bstep (se 2 (by rfl) ⟨435696, by rfl⟩ : syracuseStep 1161857 = 871393) B871393
theorem B1030787 : Blo 686314 1030787 := bstep (se 1 (by rfl) ⟨773090, by rfl⟩ : syracuseStep 1030787 = 1546181) B1546181
theorem B1030817 : Blo 686314 1030817 := bstep (se 2 (by rfl) ⟨386556, by rfl⟩ : syracuseStep 1030817 = 773113) B773113
theorem B1030835 : Blo 686314 1030835 := bstep (se 1 (by rfl) ⟨773126, by rfl⟩ : syracuseStep 1030835 = 1546253) B1546253
theorem B1030865 : Blo 686314 1030865 := bstep (se 2 (by rfl) ⟨386574, by rfl⟩ : syracuseStep 1030865 = 773149) B773149
theorem B1030883 : Blo 686314 1030883 := bstep (se 1 (by rfl) ⟨773162, by rfl⟩ : syracuseStep 1030883 = 1546325) B1546325
theorem B1030913 : Blo 686314 1030913 := bstep (se 2 (by rfl) ⟨386592, by rfl⟩ : syracuseStep 1030913 = 773185) B773185
theorem B1161985 : Blo 686314 1161985 := bstep (se 2 (by rfl) ⟨435744, by rfl⟩ : syracuseStep 1161985 = 871489) B871489
theorem B736003 : Blo 686314 736003 := bstep (se 1 (by rfl) ⟨552002, by rfl⟩ : syracuseStep 736003 = 1104005) B1104005
theorem B4406021 : Blo 686314 4406021 := bstep (se 4 (by rfl) ⟨413064, by rfl⟩ : syracuseStep 4406021 = 826129) B826129
theorem B1030931 : Blo 686314 1030931 := bstep (se 1 (by rfl) ⟨773198, by rfl⟩ : syracuseStep 1030931 = 1546397) B1546397
theorem B1162019 : Blo 686314 1162019 := bstep (se 1 (by rfl) ⟨871514, by rfl⟩ : syracuseStep 1162019 = 1743029) B1743029
theorem B1030961 : Blo 686314 1030961 := bstep (se 2 (by rfl) ⟨386610, by rfl⟩ : syracuseStep 1030961 = 773221) B773221
theorem B1030979 : Blo 686314 1030979 := bstep (se 1 (by rfl) ⟨773234, by rfl⟩ : syracuseStep 1030979 = 1546469) B1546469
theorem B1031009 : Blo 686314 1031009 := bstep (se 2 (by rfl) ⟨386628, by rfl⟩ : syracuseStep 1031009 = 773257) B773257
theorem B1031027 : Blo 686314 1031027 := bstep (se 1 (by rfl) ⟨773270, by rfl⟩ : syracuseStep 1031027 = 1546541) B1546541
theorem B1031057 : Blo 686314 1031057 := bstep (se 2 (by rfl) ⟨386646, by rfl⟩ : syracuseStep 1031057 = 773293) B773293
theorem B1031075 : Blo 686314 1031075 := bstep (se 1 (by rfl) ⟨773306, by rfl⟩ : syracuseStep 1031075 = 1546613) B1546613
theorem B1162147 : Blo 686314 1162147 := bstep (se 1 (by rfl) ⟨871610, by rfl⟩ : syracuseStep 1162147 = 1743221) B1743221
theorem B1031105 : Blo 686314 1031105 := bstep (se 2 (by rfl) ⟨386664, by rfl⟩ : syracuseStep 1031105 = 773329) B773329
theorem B1031123 : Blo 686314 1031123 := bstep (se 1 (by rfl) ⟨773342, by rfl⟩ : syracuseStep 1031123 = 1546685) B1546685
theorem B1031153 : Blo 686314 1031153 := bstep (se 2 (by rfl) ⟨386682, by rfl⟩ : syracuseStep 1031153 = 773365) B773365
theorem B1031171 : Blo 686314 1031171 := bstep (se 1 (by rfl) ⟨773378, by rfl⟩ : syracuseStep 1031171 = 1546757) B1546757
theorem B1031201 : Blo 686314 1031201 := bstep (se 2 (by rfl) ⟨386700, by rfl⟩ : syracuseStep 1031201 = 773401) B773401
theorem B1162289 : Blo 686314 1162289 := bstep (se 2 (by rfl) ⟨435858, by rfl⟩ : syracuseStep 1162289 = 871717) B871717
theorem B1031219 : Blo 686314 1031219 := bstep (se 1 (by rfl) ⟨773414, by rfl⟩ : syracuseStep 1031219 = 1546829) B1546829
theorem B932915 : Blo 686314 932915 := bstep (se 1 (by rfl) ⟨699686, by rfl⟩ : syracuseStep 932915 = 1399373) B1399373
theorem B1031249 : Blo 686314 1031249 := bstep (se 2 (by rfl) ⟨386718, by rfl⟩ : syracuseStep 1031249 = 773437) B773437
theorem B1031267 : Blo 686314 1031267 := bstep (se 1 (by rfl) ⟨773450, by rfl⟩ : syracuseStep 1031267 = 1546901) B1546901
theorem B932963 : Blo 686314 932963 := bstep (se 1 (by rfl) ⟨699722, by rfl⟩ : syracuseStep 932963 = 1399445) B1399445
theorem B30194801 : Blo 686314 30194801 := bstep (se 2 (by rfl) ⟨11323050, by rfl⟩ : syracuseStep 30194801 = 22646101) B22646101
theorem B1031297 : Blo 686314 1031297 := bstep (se 2 (by rfl) ⟨386736, by rfl⟩ : syracuseStep 1031297 = 773473) B773473
theorem B1031315 : Blo 686314 1031315 := bstep (se 1 (by rfl) ⟨773486, by rfl⟩ : syracuseStep 1031315 = 1546973) B1546973
theorem B1031345 : Blo 686314 1031345 := bstep (se 2 (by rfl) ⟨386754, by rfl⟩ : syracuseStep 1031345 = 773509) B773509
theorem B1162417 : Blo 686314 1162417 := bstep (se 2 (by rfl) ⟨435906, by rfl⟩ : syracuseStep 1162417 = 871813) B871813
theorem B1031363 : Blo 686314 1031363 := bstep (se 1 (by rfl) ⟨773522, by rfl⟩ : syracuseStep 1031363 = 1547045) B1547045
theorem B1162451 : Blo 686314 1162451 := bstep (se 1 (by rfl) ⟨871838, by rfl⟩ : syracuseStep 1162451 = 1743677) B1743677
theorem B1031393 : Blo 686314 1031393 := bstep (se 2 (by rfl) ⟨386772, by rfl⟩ : syracuseStep 1031393 = 773545) B773545
theorem B1031411 : Blo 686314 1031411 := bstep (se 1 (by rfl) ⟨773558, by rfl⟩ : syracuseStep 1031411 = 1547117) B1547117
theorem B1031441 : Blo 686314 1031441 := bstep (se 2 (by rfl) ⟨386790, by rfl⟩ : syracuseStep 1031441 = 773581) B773581
theorem B1031459 : Blo 686314 1031459 := bstep (se 1 (by rfl) ⟨773594, by rfl⟩ : syracuseStep 1031459 = 1547189) B1547189
theorem B1031489 : Blo 686314 1031489 := bstep (se 2 (by rfl) ⟨386808, by rfl⟩ : syracuseStep 1031489 = 773617) B773617
theorem B1031507 : Blo 686314 1031507 := bstep (se 1 (by rfl) ⟨773630, by rfl⟩ : syracuseStep 1031507 = 1547261) B1547261
theorem B1162579 : Blo 686314 1162579 := bstep (se 1 (by rfl) ⟨871934, by rfl⟩ : syracuseStep 1162579 = 1743869) B1743869
theorem B1031537 : Blo 686314 1031537 := bstep (se 2 (by rfl) ⟨386826, by rfl⟩ : syracuseStep 1031537 = 773653) B773653
theorem B1031555 : Blo 686314 1031555 := bstep (se 1 (by rfl) ⟨773666, by rfl⟩ : syracuseStep 1031555 = 1547333) B1547333
theorem B1031585 : Blo 686314 1031585 := bstep (se 2 (by rfl) ⟨386844, by rfl⟩ : syracuseStep 1031585 = 773689) B773689
theorem B1031603 : Blo 686314 1031603 := bstep (se 1 (by rfl) ⟨773702, by rfl⟩ : syracuseStep 1031603 = 1547405) B1547405
theorem B1031633 : Blo 686314 1031633 := bstep (se 2 (by rfl) ⟨386862, by rfl⟩ : syracuseStep 1031633 = 773725) B773725
theorem B1162721 : Blo 686314 1162721 := bstep (se 2 (by rfl) ⟨436020, by rfl⟩ : syracuseStep 1162721 = 872041) B872041
theorem B1031651 : Blo 686314 1031651 := bstep (se 1 (by rfl) ⟨773738, by rfl⟩ : syracuseStep 1031651 = 1547477) B1547477
theorem B1031681 : Blo 686314 1031681 := bstep (se 2 (by rfl) ⟨386880, by rfl⟩ : syracuseStep 1031681 = 773761) B773761
theorem B1031699 : Blo 686314 1031699 := bstep (se 1 (by rfl) ⟨773774, by rfl⟩ : syracuseStep 1031699 = 1547549) B1547549
theorem B1031729 : Blo 686314 1031729 := bstep (se 2 (by rfl) ⟨386898, by rfl⟩ : syracuseStep 1031729 = 773797) B773797
theorem B1031747 : Blo 686314 1031747 := bstep (se 1 (by rfl) ⟨773810, by rfl⟩ : syracuseStep 1031747 = 1547621) B1547621
theorem B1031777 : Blo 686314 1031777 := bstep (se 2 (by rfl) ⟨386916, by rfl⟩ : syracuseStep 1031777 = 773833) B773833
theorem B1162849 : Blo 686314 1162849 := bstep (se 2 (by rfl) ⟨436068, by rfl⟩ : syracuseStep 1162849 = 872137) B872137
theorem B1031795 : Blo 686314 1031795 := bstep (se 1 (by rfl) ⟨773846, by rfl⟩ : syracuseStep 1031795 = 1547693) B1547693
theorem B1162883 : Blo 686314 1162883 := bstep (se 1 (by rfl) ⟨872162, by rfl⟩ : syracuseStep 1162883 = 1744325) B1744325
theorem B1031825 : Blo 686314 1031825 := bstep (se 2 (by rfl) ⟨386934, by rfl⟩ : syracuseStep 1031825 = 773869) B773869
theorem B1031843 : Blo 686314 1031843 := bstep (se 1 (by rfl) ⟨773882, by rfl⟩ : syracuseStep 1031843 = 1547765) B1547765
theorem B1031873 : Blo 686314 1031873 := bstep (se 2 (by rfl) ⟨386952, by rfl⟩ : syracuseStep 1031873 = 773905) B773905
theorem B1031891 : Blo 686314 1031891 := bstep (se 1 (by rfl) ⟨773918, by rfl⟩ : syracuseStep 1031891 = 1547837) B1547837
theorem B1031921 : Blo 686314 1031921 := bstep (se 2 (by rfl) ⟨386970, by rfl⟩ : syracuseStep 1031921 = 773941) B773941
theorem B1031939 : Blo 686314 1031939 := bstep (se 1 (by rfl) ⟨773954, by rfl⟩ : syracuseStep 1031939 = 1547909) B1547909
theorem B1163011 : Blo 686314 1163011 := bstep (se 1 (by rfl) ⟨872258, by rfl⟩ : syracuseStep 1163011 = 1744517) B1744517
theorem B1031969 : Blo 686314 1031969 := bstep (se 2 (by rfl) ⟨386988, by rfl⟩ : syracuseStep 1031969 = 773977) B773977
theorem B1031987 : Blo 686314 1031987 := bstep (se 1 (by rfl) ⟨773990, by rfl⟩ : syracuseStep 1031987 = 1547981) B1547981
theorem B2178893 : Blo 686314 2178893 := bstep (se 3 (by rfl) ⟨408542, by rfl⟩ : syracuseStep 2178893 = 817085) B817085
theorem B1032017 : Blo 686314 1032017 := bstep (se 2 (by rfl) ⟨387006, by rfl⟩ : syracuseStep 1032017 = 774013) B774013
theorem B1032035 : Blo 686314 1032035 := bstep (se 1 (by rfl) ⟨774026, by rfl⟩ : syracuseStep 1032035 = 1548053) B1548053
theorem B1032065 : Blo 686314 1032065 := bstep (se 2 (by rfl) ⟨387024, by rfl⟩ : syracuseStep 1032065 = 774049) B774049
theorem B1163153 : Blo 686314 1163153 := bstep (se 2 (by rfl) ⟨436182, by rfl⟩ : syracuseStep 1163153 = 872365) B872365
theorem B1032083 : Blo 686314 1032083 := bstep (se 1 (by rfl) ⟨774062, by rfl⟩ : syracuseStep 1032083 = 1548125) B1548125
theorem B1032113 : Blo 686314 1032113 := bstep (se 2 (by rfl) ⟨387042, by rfl⟩ : syracuseStep 1032113 = 774085) B774085
theorem B1032131 : Blo 686314 1032131 := bstep (se 1 (by rfl) ⟨774098, by rfl⟩ : syracuseStep 1032131 = 1548197) B1548197
theorem B1032161 : Blo 686314 1032161 := bstep (se 2 (by rfl) ⟨387060, by rfl⟩ : syracuseStep 1032161 = 774121) B774121
theorem B1294321 : Blo 686314 1294321 := bstep (se 2 (by rfl) ⟨485370, by rfl⟩ : syracuseStep 1294321 = 970741) B970741
theorem B1032179 : Blo 686314 1032179 := bstep (se 1 (by rfl) ⟨774134, by rfl⟩ : syracuseStep 1032179 = 1548269) B1548269
theorem B1032209 : Blo 686314 1032209 := bstep (se 2 (by rfl) ⟨387078, by rfl⟩ : syracuseStep 1032209 = 774157) B774157
theorem B1163281 : Blo 686314 1163281 := bstep (se 2 (by rfl) ⟨436230, by rfl⟩ : syracuseStep 1163281 = 872461) B872461
theorem B1032227 : Blo 686314 1032227 := bstep (se 1 (by rfl) ⟨774170, by rfl⟩ : syracuseStep 1032227 = 1548341) B1548341
theorem B1163315 : Blo 686314 1163315 := bstep (se 1 (by rfl) ⟨872486, by rfl⟩ : syracuseStep 1163315 = 1744973) B1744973
theorem B1032257 : Blo 686314 1032257 := bstep (se 2 (by rfl) ⟨387096, by rfl⟩ : syracuseStep 1032257 = 774193) B774193
theorem B1032275 : Blo 686314 1032275 := bstep (se 1 (by rfl) ⟨774206, by rfl⟩ : syracuseStep 1032275 = 1548413) B1548413
theorem B6275171 : Blo 686314 6275171 := bstep (se 1 (by rfl) ⟨4706378, by rfl⟩ : syracuseStep 6275171 = 9412757) B9412757
theorem B1032305 : Blo 686314 1032305 := bstep (se 2 (by rfl) ⟨387114, by rfl⟩ : syracuseStep 1032305 = 774229) B774229
theorem B1032323 : Blo 686314 1032323 := bstep (se 1 (by rfl) ⟨774242, by rfl⟩ : syracuseStep 1032323 = 1548485) B1548485
theorem B1032353 : Blo 686314 1032353 := bstep (se 2 (by rfl) ⟨387132, by rfl⟩ : syracuseStep 1032353 = 774265) B774265
theorem B1032371 : Blo 686314 1032371 := bstep (se 1 (by rfl) ⟨774278, by rfl⟩ : syracuseStep 1032371 = 1548557) B1548557
theorem B1163443 : Blo 686314 1163443 := bstep (se 1 (by rfl) ⟨872582, by rfl⟩ : syracuseStep 1163443 = 1745165) B1745165
theorem B1032401 : Blo 686314 1032401 := bstep (se 2 (by rfl) ⟨387150, by rfl⟩ : syracuseStep 1032401 = 774301) B774301
theorem B1032419 : Blo 686314 1032419 := bstep (se 1 (by rfl) ⟨774314, by rfl⟩ : syracuseStep 1032419 = 1548629) B1548629
theorem B1032449 : Blo 686314 1032449 := bstep (se 2 (by rfl) ⟨387168, by rfl⟩ : syracuseStep 1032449 = 774337) B774337
theorem B1032467 : Blo 686314 1032467 := bstep (se 1 (by rfl) ⟨774350, by rfl⟩ : syracuseStep 1032467 = 1548701) B1548701
theorem B1032497 : Blo 686314 1032497 := bstep (se 2 (by rfl) ⟨387186, by rfl⟩ : syracuseStep 1032497 = 774373) B774373
theorem B1163585 : Blo 686314 1163585 := bstep (se 2 (by rfl) ⟨436344, by rfl⟩ : syracuseStep 1163585 = 872689) B872689
theorem B1032515 : Blo 686314 1032515 := bstep (se 1 (by rfl) ⟨774386, by rfl⟩ : syracuseStep 1032515 = 1548773) B1548773
theorem B1032545 : Blo 686314 1032545 := bstep (se 2 (by rfl) ⟨387204, by rfl⟩ : syracuseStep 1032545 = 774409) B774409
theorem B1032563 : Blo 686314 1032563 := bstep (se 1 (by rfl) ⟨774422, by rfl⟩ : syracuseStep 1032563 = 1548845) B1548845
theorem B1032593 : Blo 686314 1032593 := bstep (se 2 (by rfl) ⟨387222, by rfl⟩ : syracuseStep 1032593 = 774445) B774445
theorem B1032611 : Blo 686314 1032611 := bstep (se 1 (by rfl) ⟨774458, by rfl⟩ : syracuseStep 1032611 = 1548917) B1548917
theorem B1032641 : Blo 686314 1032641 := bstep (se 2 (by rfl) ⟨387240, by rfl⟩ : syracuseStep 1032641 = 774481) B774481
theorem B1163713 : Blo 686314 1163713 := bstep (se 2 (by rfl) ⟨436392, by rfl⟩ : syracuseStep 1163713 = 872785) B872785
theorem B1032659 : Blo 686314 1032659 := bstep (se 1 (by rfl) ⟨774494, by rfl⟩ : syracuseStep 1032659 = 1548989) B1548989
theorem B1163747 : Blo 686314 1163747 := bstep (se 1 (by rfl) ⟨872810, by rfl⟩ : syracuseStep 1163747 = 1745621) B1745621
theorem B1032689 : Blo 686314 1032689 := bstep (se 2 (by rfl) ⟨387258, by rfl⟩ : syracuseStep 1032689 = 774517) B774517
theorem B3490289 : Blo 686314 3490289 := bstep (se 2 (by rfl) ⟨1308858, by rfl⟩ : syracuseStep 3490289 = 2617717) B2617717
theorem B1032707 : Blo 686314 1032707 := bstep (se 1 (by rfl) ⟨774530, by rfl⟩ : syracuseStep 1032707 = 1549061) B1549061
theorem B1032737 : Blo 686314 1032737 := bstep (se 2 (by rfl) ⟨387276, by rfl⟩ : syracuseStep 1032737 = 774553) B774553
theorem B1032755 : Blo 686314 1032755 := bstep (se 1 (by rfl) ⟨774566, by rfl⟩ : syracuseStep 1032755 = 1549133) B1549133
theorem B1032785 : Blo 686314 1032785 := bstep (se 2 (by rfl) ⟨387294, by rfl⟩ : syracuseStep 1032785 = 774589) B774589
theorem B868963 : Blo 686314 868963 := bstep (se 1 (by rfl) ⟨651722, by rfl⟩ : syracuseStep 868963 = 1303445) B1303445
theorem B1032803 : Blo 686314 1032803 := bstep (se 1 (by rfl) ⟨774602, by rfl⟩ : syracuseStep 1032803 = 1549205) B1549205
theorem B1163875 : Blo 686314 1163875 := bstep (se 1 (by rfl) ⟨872906, by rfl⟩ : syracuseStep 1163875 = 1745813) B1745813
theorem B1032833 : Blo 686314 1032833 := bstep (se 2 (by rfl) ⟨387312, by rfl⟩ : syracuseStep 1032833 = 774625) B774625
theorem B1655441 : Blo 686314 1655441 := bstep (se 2 (by rfl) ⟨620790, by rfl⟩ : syracuseStep 1655441 = 1241581) B1241581
theorem B1032851 : Blo 686314 1032851 := bstep (se 1 (by rfl) ⟨774638, by rfl⟩ : syracuseStep 1032851 = 1549277) B1549277
theorem B1032881 : Blo 686314 1032881 := bstep (se 2 (by rfl) ⟨387330, by rfl⟩ : syracuseStep 1032881 = 774661) B774661
theorem B869059 : Blo 686314 869059 := bstep (se 1 (by rfl) ⟨651794, by rfl⟩ : syracuseStep 869059 = 1303589) B1303589
theorem B1032899 : Blo 686314 1032899 := bstep (se 1 (by rfl) ⟨774674, by rfl⟩ : syracuseStep 1032899 = 1549349) B1549349
theorem B1032929 : Blo 686314 1032929 := bstep (se 2 (by rfl) ⟨387348, by rfl⟩ : syracuseStep 1032929 = 774697) B774697
theorem B4702961 : Blo 686314 4702961 := bstep (se 2 (by rfl) ⟨1763610, by rfl⟩ : syracuseStep 4702961 = 3527221) B3527221
theorem B1164017 : Blo 686314 1164017 := bstep (se 2 (by rfl) ⟨436506, by rfl⟩ : syracuseStep 1164017 = 873013) B873013
theorem B1032947 : Blo 686314 1032947 := bstep (se 1 (by rfl) ⟨774710, by rfl⟩ : syracuseStep 1032947 = 1549421) B1549421
theorem B1032977 : Blo 686314 1032977 := bstep (se 2 (by rfl) ⟨387366, by rfl⟩ : syracuseStep 1032977 = 774733) B774733
theorem B1327889 : Blo 686314 1327889 := bstep (se 2 (by rfl) ⟨497958, by rfl⟩ : syracuseStep 1327889 = 995917) B995917
theorem B1032995 : Blo 686314 1032995 := bstep (se 1 (by rfl) ⟨774746, by rfl⟩ : syracuseStep 1032995 = 1549493) B1549493
theorem B1033025 : Blo 686314 1033025 := bstep (se 2 (by rfl) ⟨387384, by rfl⟩ : syracuseStep 1033025 = 774769) B774769
theorem B3720005 : Blo 686314 3720005 := bstep (se 4 (by rfl) ⟨348750, by rfl⟩ : syracuseStep 3720005 = 697501) B697501
theorem B1033043 : Blo 686314 1033043 := bstep (se 1 (by rfl) ⟨774782, by rfl⟩ : syracuseStep 1033043 = 1549565) B1549565
theorem B1033073 : Blo 686314 1033073 := bstep (se 2 (by rfl) ⟨387402, by rfl⟩ : syracuseStep 1033073 = 774805) B774805
theorem B1164145 : Blo 686314 1164145 := bstep (se 2 (by rfl) ⟨436554, by rfl⟩ : syracuseStep 1164145 = 873109) B873109
theorem B1033091 : Blo 686314 1033091 := bstep (se 1 (by rfl) ⟨774818, by rfl⟩ : syracuseStep 1033091 = 1549637) B1549637
theorem B1164179 : Blo 686314 1164179 := bstep (se 1 (by rfl) ⟨873134, by rfl⟩ : syracuseStep 1164179 = 1746269) B1746269
theorem B1033121 : Blo 686314 1033121 := bstep (se 2 (by rfl) ⟨387420, by rfl⟩ : syracuseStep 1033121 = 774841) B774841
theorem B1033139 : Blo 686314 1033139 := bstep (se 1 (by rfl) ⟨774854, by rfl⟩ : syracuseStep 1033139 = 1549709) B1549709
theorem B1033169 : Blo 686314 1033169 := bstep (se 2 (by rfl) ⟨387438, by rfl⟩ : syracuseStep 1033169 = 774877) B774877
theorem B1033187 : Blo 686314 1033187 := bstep (se 1 (by rfl) ⟨774890, by rfl⟩ : syracuseStep 1033187 = 1549781) B1549781
theorem B1033217 : Blo 686314 1033217 := bstep (se 2 (by rfl) ⟨387456, by rfl⟩ : syracuseStep 1033217 = 774913) B774913
theorem B1033235 : Blo 686314 1033235 := bstep (se 1 (by rfl) ⟨774926, by rfl⟩ : syracuseStep 1033235 = 1549853) B1549853
theorem B1164307 : Blo 686314 1164307 := bstep (se 1 (by rfl) ⟨873230, by rfl⟩ : syracuseStep 1164307 = 1746461) B1746461
theorem B1033265 : Blo 686314 1033265 := bstep (se 2 (by rfl) ⟨387474, by rfl⟩ : syracuseStep 1033265 = 774949) B774949
theorem B1033283 : Blo 686314 1033283 := bstep (se 1 (by rfl) ⟨774962, by rfl⟩ : syracuseStep 1033283 = 1549925) B1549925
theorem B1033313 : Blo 686314 1033313 := bstep (se 2 (by rfl) ⟨387492, by rfl⟩ : syracuseStep 1033313 = 774985) B774985
theorem B1033331 : Blo 686314 1033331 := bstep (se 1 (by rfl) ⟨774998, by rfl⟩ : syracuseStep 1033331 = 1549997) B1549997
theorem B1033361 : Blo 686314 1033361 := bstep (se 2 (by rfl) ⟨387510, by rfl⟩ : syracuseStep 1033361 = 775021) B775021
theorem B1164449 : Blo 686314 1164449 := bstep (se 2 (by rfl) ⟨436668, by rfl⟩ : syracuseStep 1164449 = 873337) B873337
theorem B1033379 : Blo 686314 1033379 := bstep (se 1 (by rfl) ⟨775034, by rfl⟩ : syracuseStep 1033379 = 1550069) B1550069
theorem B869555 : Blo 686314 869555 := bstep (se 1 (by rfl) ⟨652166, by rfl⟩ : syracuseStep 869555 = 1304333) B1304333
theorem B1033409 : Blo 686314 1033409 := bstep (se 2 (by rfl) ⟨387528, by rfl⟩ : syracuseStep 1033409 = 775057) B775057
theorem B1033427 : Blo 686314 1033427 := bstep (se 1 (by rfl) ⟨775070, by rfl⟩ : syracuseStep 1033427 = 1550141) B1550141
theorem B1885421 : Blo 686314 1885421 := bstep (se 3 (by rfl) ⟨353516, by rfl⟩ : syracuseStep 1885421 = 707033) B707033
theorem B1033457 : Blo 686314 1033457 := bstep (se 2 (by rfl) ⟨387546, by rfl⟩ : syracuseStep 1033457 = 775093) B775093
theorem B1033475 : Blo 686314 1033475 := bstep (se 1 (by rfl) ⟨775106, by rfl⟩ : syracuseStep 1033475 = 1550213) B1550213
theorem B1033505 : Blo 686314 1033505 := bstep (se 2 (by rfl) ⟨387564, by rfl⟩ : syracuseStep 1033505 = 775129) B775129
theorem B1164577 : Blo 686314 1164577 := bstep (se 2 (by rfl) ⟨436716, by rfl⟩ : syracuseStep 1164577 = 873433) B873433
theorem B1033523 : Blo 686314 1033523 := bstep (se 1 (by rfl) ⟨775142, by rfl⟩ : syracuseStep 1033523 = 1550285) B1550285
theorem B1164611 : Blo 686314 1164611 := bstep (se 1 (by rfl) ⟨873458, by rfl⟩ : syracuseStep 1164611 = 1746917) B1746917
theorem B1033553 : Blo 686314 1033553 := bstep (se 2 (by rfl) ⟨387582, by rfl⟩ : syracuseStep 1033553 = 775165) B775165
theorem B1033571 : Blo 686314 1033571 := bstep (se 1 (by rfl) ⟨775178, by rfl⟩ : syracuseStep 1033571 = 1550357) B1550357
theorem B1033601 : Blo 686314 1033601 := bstep (se 2 (by rfl) ⟨387600, by rfl⟩ : syracuseStep 1033601 = 775201) B775201
theorem B1656209 : Blo 686314 1656209 := bstep (se 2 (by rfl) ⟨621078, by rfl⟩ : syracuseStep 1656209 = 1242157) B1242157
theorem B1033619 : Blo 686314 1033619 := bstep (se 1 (by rfl) ⟨775214, by rfl⟩ : syracuseStep 1033619 = 1550429) B1550429
theorem B1033649 : Blo 686314 1033649 := bstep (se 2 (by rfl) ⟨387618, by rfl⟩ : syracuseStep 1033649 = 775237) B775237
theorem B1033667 : Blo 686314 1033667 := bstep (se 1 (by rfl) ⟨775250, by rfl⟩ : syracuseStep 1033667 = 1550501) B1550501
theorem B1164739 : Blo 686314 1164739 := bstep (se 1 (by rfl) ⟨873554, by rfl⟩ : syracuseStep 1164739 = 1747109) B1747109
theorem B3720653 : Blo 686314 3720653 := bstep (se 3 (by rfl) ⟨697622, by rfl⟩ : syracuseStep 3720653 = 1395245) B1395245
theorem B1033697 : Blo 686314 1033697 := bstep (se 2 (by rfl) ⟨387636, by rfl⟩ : syracuseStep 1033697 = 775273) B775273
theorem B1033715 : Blo 686314 1033715 := bstep (se 1 (by rfl) ⟨775286, by rfl⟩ : syracuseStep 1033715 = 1550573) B1550573
theorem B1033745 : Blo 686314 1033745 := bstep (se 2 (by rfl) ⟨387654, by rfl⟩ : syracuseStep 1033745 = 775309) B775309
theorem B1033763 : Blo 686314 1033763 := bstep (se 1 (by rfl) ⟨775322, by rfl⟩ : syracuseStep 1033763 = 1550645) B1550645
theorem B1033793 : Blo 686314 1033793 := bstep (se 2 (by rfl) ⟨387672, by rfl⟩ : syracuseStep 1033793 = 775345) B775345
theorem B1164881 : Blo 686314 1164881 := bstep (se 2 (by rfl) ⟨436830, by rfl⟩ : syracuseStep 1164881 = 873661) B873661
theorem B1033811 : Blo 686314 1033811 := bstep (se 1 (by rfl) ⟨775358, by rfl⟩ : syracuseStep 1033811 = 1550717) B1550717
theorem B1033841 : Blo 686314 1033841 := bstep (se 2 (by rfl) ⟨387690, by rfl⟩ : syracuseStep 1033841 = 775381) B775381
theorem B1033859 : Blo 686314 1033859 := bstep (se 1 (by rfl) ⟨775394, by rfl⟩ : syracuseStep 1033859 = 1550789) B1550789
theorem B1033889 : Blo 686314 1033889 := bstep (se 2 (by rfl) ⟨387708, by rfl⟩ : syracuseStep 1033889 = 775417) B775417
theorem B1033907 : Blo 686314 1033907 := bstep (se 1 (by rfl) ⟨775430, by rfl⟩ : syracuseStep 1033907 = 1550861) B1550861
theorem B8799941 : Blo 686314 8799941 := bstep (se 4 (by rfl) ⟨824994, by rfl⟩ : syracuseStep 8799941 = 1649989) B1649989
theorem B1033937 : Blo 686314 1033937 := bstep (se 2 (by rfl) ⟨387726, by rfl⟩ : syracuseStep 1033937 = 775453) B775453
theorem B1033955 : Blo 686314 1033955 := bstep (se 1 (by rfl) ⟨775466, by rfl⟩ : syracuseStep 1033955 = 1550933) B1550933
theorem B1033985 : Blo 686314 1033985 := bstep (se 2 (by rfl) ⟨387744, by rfl⟩ : syracuseStep 1033985 = 775489) B775489
theorem B1984259 : Blo 686314 1984259 := bstep (se 1 (by rfl) ⟨1488194, by rfl⟩ : syracuseStep 1984259 = 2976389) B2976389
theorem B1034003 : Blo 686314 1034003 := bstep (se 1 (by rfl) ⟨775502, by rfl⟩ : syracuseStep 1034003 = 1551005) B1551005
theorem B1034033 : Blo 686314 1034033 := bstep (se 2 (by rfl) ⟨387762, by rfl⟩ : syracuseStep 1034033 = 775525) B775525
theorem B1034051 : Blo 686314 1034051 := bstep (se 1 (by rfl) ⟨775538, by rfl⟩ : syracuseStep 1034051 = 1551077) B1551077
theorem B1034081 : Blo 686314 1034081 := bstep (se 2 (by rfl) ⟨387780, by rfl⟩ : syracuseStep 1034081 = 775561) B775561
theorem B5228387 : Blo 686314 5228387 := bstep (se 1 (by rfl) ⟨3921290, by rfl⟩ : syracuseStep 5228387 = 7842581) B7842581
theorem B870259 : Blo 686314 870259 := bstep (se 1 (by rfl) ⟨652694, by rfl⟩ : syracuseStep 870259 = 1305389) B1305389
theorem B1034099 : Blo 686314 1034099 := bstep (se 1 (by rfl) ⟨775574, by rfl⟩ : syracuseStep 1034099 = 1551149) B1551149
theorem B4179845 : Blo 686314 4179845 := bstep (se 4 (by rfl) ⟨391860, by rfl⟩ : syracuseStep 4179845 = 783721) B783721
theorem B1034129 : Blo 686314 1034129 := bstep (se 2 (by rfl) ⟨387798, by rfl⟩ : syracuseStep 1034129 = 775597) B775597
theorem B2607011 : Blo 686314 2607011 := bstep (se 1 (by rfl) ⟨1955258, by rfl⟩ : syracuseStep 2607011 = 3910517) B3910517
theorem B1034147 : Blo 686314 1034147 := bstep (se 1 (by rfl) ⟨775610, by rfl⟩ : syracuseStep 1034147 = 1551221) B1551221
theorem B3491747 : Blo 686314 3491747 := bstep (se 1 (by rfl) ⟨2618810, by rfl⟩ : syracuseStep 3491747 = 5237621) B5237621
theorem B2607025 : Blo 686314 2607025 := bstep (se 2 (by rfl) ⟨977634, by rfl⟩ : syracuseStep 2607025 = 1955269) B1955269
theorem B1034177 : Blo 686314 1034177 := bstep (se 2 (by rfl) ⟨387816, by rfl⟩ : syracuseStep 1034177 = 775633) B775633
theorem B870355 : Blo 686314 870355 := bstep (se 1 (by rfl) ⟨652766, by rfl⟩ : syracuseStep 870355 = 1305533) B1305533
theorem B1034195 : Blo 686314 1034195 := bstep (se 1 (by rfl) ⟨775646, by rfl⟩ : syracuseStep 1034195 = 1551293) B1551293
theorem B1034225 : Blo 686314 1034225 := bstep (se 2 (by rfl) ⟨387834, by rfl⟩ : syracuseStep 1034225 = 775669) B775669
theorem B1034243 : Blo 686314 1034243 := bstep (se 1 (by rfl) ⟨775682, by rfl⟩ : syracuseStep 1034243 = 1551365) B1551365
theorem B1034273 : Blo 686314 1034273 := bstep (se 2 (by rfl) ⟨387852, by rfl⟩ : syracuseStep 1034273 = 775705) B775705
theorem B1034291 : Blo 686314 1034291 := bstep (se 1 (by rfl) ⟨775718, by rfl⟩ : syracuseStep 1034291 = 1551437) B1551437
theorem B1034321 : Blo 686314 1034321 := bstep (se 2 (by rfl) ⟨387870, by rfl⟩ : syracuseStep 1034321 = 775741) B775741
theorem B772195 : Blo 686314 772195 := bstep (se 1 (by rfl) ⟨579146, by rfl⟩ : syracuseStep 772195 = 1158293) B1158293
theorem B1034339 : Blo 686314 1034339 := bstep (se 1 (by rfl) ⟨775754, by rfl⟩ : syracuseStep 1034339 = 1551509) B1551509
theorem B1034369 : Blo 686314 1034369 := bstep (se 2 (by rfl) ⟨387888, by rfl⟩ : syracuseStep 1034369 = 775777) B775777
theorem B1034387 : Blo 686314 1034387 := bstep (se 1 (by rfl) ⟨775790, by rfl⟩ : syracuseStep 1034387 = 1551581) B1551581
theorem B1034417 : Blo 686314 1034417 := bstep (se 2 (by rfl) ⟨387906, by rfl⟩ : syracuseStep 1034417 = 775813) B775813
theorem B1099955 : Blo 686314 1099955 := bstep (se 1 (by rfl) ⟨824966, by rfl⟩ : syracuseStep 1099955 = 1649933) B1649933
theorem B1034435 : Blo 686314 1034435 := bstep (se 1 (by rfl) ⟨775826, by rfl⟩ : syracuseStep 1034435 = 1551653) B1551653
theorem B1034465 : Blo 686314 1034465 := bstep (se 2 (by rfl) ⟨387924, by rfl⟩ : syracuseStep 1034465 = 775849) B775849
theorem B4409585 : Blo 686314 4409585 := bstep (se 2 (by rfl) ⟨1653594, by rfl⟩ : syracuseStep 4409585 = 3307189) B3307189
theorem B772339 : Blo 686314 772339 := bstep (se 1 (by rfl) ⟨579254, by rfl⟩ : syracuseStep 772339 = 1158509) B1158509
theorem B1034483 : Blo 686314 1034483 := bstep (se 1 (by rfl) ⟨775862, by rfl⟩ : syracuseStep 1034483 = 1551725) B1551725
theorem B1034513 : Blo 686314 1034513 := bstep (se 2 (by rfl) ⟨387942, by rfl⟩ : syracuseStep 1034513 = 775885) B775885
theorem B2935075 : Blo 686314 2935075 := bstep (se 1 (by rfl) ⟨2201306, by rfl⟩ : syracuseStep 2935075 = 4402613) B4402613
theorem B1034531 : Blo 686314 1034531 := bstep (se 1 (by rfl) ⟨775898, by rfl⟩ : syracuseStep 1034531 = 1551797) B1551797
theorem B1034561 : Blo 686314 1034561 := bstep (se 2 (by rfl) ⟨387960, by rfl⟩ : syracuseStep 1034561 = 775921) B775921
theorem B1034579 : Blo 686314 1034579 := bstep (se 1 (by rfl) ⟨775934, by rfl⟩ : syracuseStep 1034579 = 1551869) B1551869
theorem B3131747 : Blo 686314 3131747 := bstep (se 1 (by rfl) ⟨2348810, by rfl⟩ : syracuseStep 3131747 = 4697621) B4697621
theorem B1034609 : Blo 686314 1034609 := bstep (se 2 (by rfl) ⟨387978, by rfl⟩ : syracuseStep 1034609 = 775957) B775957
theorem B772483 : Blo 686314 772483 := bstep (se 1 (by rfl) ⟨579362, by rfl⟩ : syracuseStep 772483 = 1158725) B1158725
theorem B1034627 : Blo 686314 1034627 := bstep (se 1 (by rfl) ⟨775970, by rfl⟩ : syracuseStep 1034627 = 1551941) B1551941
theorem B1034657 : Blo 686314 1034657 := bstep (se 2 (by rfl) ⟨387996, by rfl⟩ : syracuseStep 1034657 = 775993) B775993
theorem B1034675 : Blo 686314 1034675 := bstep (se 1 (by rfl) ⟨776006, by rfl⟩ : syracuseStep 1034675 = 1552013) B1552013
theorem B870851 : Blo 686314 870851 := bstep (se 1 (by rfl) ⟨653138, by rfl⟩ : syracuseStep 870851 = 1306277) B1306277
theorem B1034705 : Blo 686314 1034705 := bstep (se 2 (by rfl) ⟨388014, by rfl⟩ : syracuseStep 1034705 = 776029) B776029
theorem B1034723 : Blo 686314 1034723 := bstep (se 1 (by rfl) ⟨776042, by rfl⟩ : syracuseStep 1034723 = 1552085) B1552085
theorem B1034753 : Blo 686314 1034753 := bstep (se 2 (by rfl) ⟨388032, by rfl⟩ : syracuseStep 1034753 = 776065) B776065
theorem B2509325 : Blo 686314 2509325 := bstep (se 3 (by rfl) ⟨470498, by rfl⟩ : syracuseStep 2509325 = 940997) B940997
theorem B772627 : Blo 686314 772627 := bstep (se 1 (by rfl) ⟨579470, by rfl⟩ : syracuseStep 772627 = 1158941) B1158941
theorem B1034771 : Blo 686314 1034771 := bstep (se 1 (by rfl) ⟨776078, by rfl⟩ : syracuseStep 1034771 = 1552157) B1552157
theorem B1034801 : Blo 686314 1034801 := bstep (se 2 (by rfl) ⟨388050, by rfl⟩ : syracuseStep 1034801 = 776101) B776101
theorem B1034819 : Blo 686314 1034819 := bstep (se 1 (by rfl) ⟨776114, by rfl⟩ : syracuseStep 1034819 = 1552229) B1552229
theorem B1034849 : Blo 686314 1034849 := bstep (se 2 (by rfl) ⟨388068, by rfl⟩ : syracuseStep 1034849 = 776137) B776137
theorem B1034867 : Blo 686314 1034867 := bstep (se 1 (by rfl) ⟨776150, by rfl⟩ : syracuseStep 1034867 = 1552301) B1552301
theorem B1034897 : Blo 686314 1034897 := bstep (se 2 (by rfl) ⟨388086, by rfl⟩ : syracuseStep 1034897 = 776173) B776173
theorem B772771 : Blo 686314 772771 := bstep (se 1 (by rfl) ⟨579578, by rfl⟩ : syracuseStep 772771 = 1159157) B1159157
theorem B1034915 : Blo 686314 1034915 := bstep (se 1 (by rfl) ⟨776186, by rfl⟩ : syracuseStep 1034915 = 1552373) B1552373
theorem B1034945 : Blo 686314 1034945 := bstep (se 2 (by rfl) ⟨388104, by rfl⟩ : syracuseStep 1034945 = 776209) B776209
theorem B3492557 : Blo 686314 3492557 := bstep (se 3 (by rfl) ⟨654854, by rfl⟩ : syracuseStep 3492557 = 1309709) B1309709
theorem B1034963 : Blo 686314 1034963 := bstep (se 1 (by rfl) ⟨776222, by rfl⟩ : syracuseStep 1034963 = 1552445) B1552445
theorem B1034993 : Blo 686314 1034993 := bstep (se 2 (by rfl) ⟨388122, by rfl⟩ : syracuseStep 1034993 = 776245) B776245
theorem B1035011 : Blo 686314 1035011 := bstep (se 1 (by rfl) ⟨776258, by rfl⟩ : syracuseStep 1035011 = 1552517) B1552517
theorem B1035041 : Blo 686314 1035041 := bstep (se 2 (by rfl) ⟨388140, by rfl⟩ : syracuseStep 1035041 = 776281) B776281
theorem B772915 : Blo 686314 772915 := bstep (se 1 (by rfl) ⟨579686, by rfl⟩ : syracuseStep 772915 = 1159373) B1159373
theorem B1035059 : Blo 686314 1035059 := bstep (se 1 (by rfl) ⟨776294, by rfl⟩ : syracuseStep 1035059 = 1552589) B1552589
theorem B1035089 : Blo 686314 1035089 := bstep (se 2 (by rfl) ⟨388158, by rfl⟩ : syracuseStep 1035089 = 776317) B776317
theorem B1035107 : Blo 686314 1035107 := bstep (se 1 (by rfl) ⟨776330, by rfl⟩ : syracuseStep 1035107 = 1552661) B1552661
theorem B1035137 : Blo 686314 1035137 := bstep (se 2 (by rfl) ⟨388176, by rfl⟩ : syracuseStep 1035137 = 776353) B776353
theorem B1035155 : Blo 686314 1035155 := bstep (se 1 (by rfl) ⟨776366, by rfl⟩ : syracuseStep 1035155 = 1552733) B1552733
theorem B1035185 : Blo 686314 1035185 := bstep (se 2 (by rfl) ⟨388194, by rfl⟩ : syracuseStep 1035185 = 776389) B776389
theorem B773059 : Blo 686314 773059 := bstep (se 1 (by rfl) ⟨579794, by rfl⟩ : syracuseStep 773059 = 1159589) B1159589
theorem B1035203 : Blo 686314 1035203 := bstep (se 1 (by rfl) ⟨776402, by rfl⟩ : syracuseStep 1035203 = 1552805) B1552805
theorem B1035233 : Blo 686314 1035233 := bstep (se 2 (by rfl) ⟨388212, by rfl⟩ : syracuseStep 1035233 = 776425) B776425
theorem B1035251 : Blo 686314 1035251 := bstep (se 1 (by rfl) ⟨776438, by rfl⟩ : syracuseStep 1035251 = 1552877) B1552877
theorem B1035281 : Blo 686314 1035281 := bstep (se 2 (by rfl) ⟨388230, by rfl⟩ : syracuseStep 1035281 = 776461) B776461
theorem B1035299 : Blo 686314 1035299 := bstep (se 1 (by rfl) ⟨776474, by rfl⟩ : syracuseStep 1035299 = 1552949) B1552949
theorem B1035329 : Blo 686314 1035329 := bstep (se 2 (by rfl) ⟨388248, by rfl⟩ : syracuseStep 1035329 = 776497) B776497
theorem B773203 : Blo 686314 773203 := bstep (se 1 (by rfl) ⟨579902, by rfl⟩ : syracuseStep 773203 = 1159805) B1159805
theorem B1035347 : Blo 686314 1035347 := bstep (se 1 (by rfl) ⟨776510, by rfl⟩ : syracuseStep 1035347 = 1553021) B1553021
theorem B1035377 : Blo 686314 1035377 := bstep (se 2 (by rfl) ⟨388266, by rfl⟩ : syracuseStep 1035377 = 776533) B776533
theorem B871555 : Blo 686314 871555 := bstep (se 1 (by rfl) ⟨653666, by rfl⟩ : syracuseStep 871555 = 1307333) B1307333
theorem B1035395 : Blo 686314 1035395 := bstep (se 1 (by rfl) ⟨776546, by rfl⟩ : syracuseStep 1035395 = 1553093) B1553093
theorem B1035425 : Blo 686314 1035425 := bstep (se 2 (by rfl) ⟨388284, by rfl⟩ : syracuseStep 1035425 = 776569) B776569
theorem B2477233 : Blo 686314 2477233 := bstep (se 2 (by rfl) ⟨928962, by rfl⟩ : syracuseStep 2477233 = 1857925) B1857925
theorem B1035443 : Blo 686314 1035443 := bstep (se 1 (by rfl) ⟨776582, by rfl⟩ : syracuseStep 1035443 = 1553165) B1553165
theorem B773347 : Blo 686314 773347 := bstep (se 1 (by rfl) ⟨580010, by rfl⟩ : syracuseStep 773347 = 1160021) B1160021
theorem B871651 : Blo 686314 871651 := bstep (se 1 (by rfl) ⟨653738, by rfl⟩ : syracuseStep 871651 = 1307477) B1307477
theorem B838883 : Blo 686314 838883 := bstep (se 1 (by rfl) ⟨629162, by rfl⟩ : syracuseStep 838883 = 1258325) B1258325
theorem B1658083 : Blo 686314 1658083 := bstep (se 1 (by rfl) ⟨1243562, by rfl⟩ : syracuseStep 1658083 = 2487125) B2487125
theorem B1133843 : Blo 686314 1133843 := bstep (se 1 (by rfl) ⟨850382, by rfl⟩ : syracuseStep 1133843 = 1700765) B1700765
theorem B2608483 : Blo 686314 2608483 := bstep (se 1 (by rfl) ⟨1956362, by rfl⟩ : syracuseStep 2608483 = 3912725) B3912725
theorem B773491 : Blo 686314 773491 := bstep (se 1 (by rfl) ⟨580118, by rfl⟩ : syracuseStep 773491 = 1160237) B1160237
theorem B773635 : Blo 686314 773635 := bstep (se 1 (by rfl) ⟨580226, by rfl⟩ : syracuseStep 773635 = 1160453) B1160453
theorem B1101377 : Blo 686314 1101377 := bstep (se 2 (by rfl) ⟨413016, by rfl⟩ : syracuseStep 1101377 = 826033) B826033
theorem B773779 : Blo 686314 773779 := bstep (se 1 (by rfl) ⟨580334, by rfl⟩ : syracuseStep 773779 = 1160669) B1160669
theorem B4411043 : Blo 686314 4411043 := bstep (se 1 (by rfl) ⟨3308282, by rfl⟩ : syracuseStep 4411043 = 6616565) B6616565
theorem B872147 : Blo 686314 872147 := bstep (se 1 (by rfl) ⟨654110, by rfl⟩ : syracuseStep 872147 = 1308221) B1308221
theorem B773923 : Blo 686314 773923 := bstep (se 1 (by rfl) ⟨580442, by rfl⟩ : syracuseStep 773923 = 1160885) B1160885
theorem B774067 : Blo 686314 774067 := bstep (se 1 (by rfl) ⟨580550, by rfl⟩ : syracuseStep 774067 = 1161101) B1161101
theorem B774211 : Blo 686314 774211 := bstep (se 1 (by rfl) ⟨580658, by rfl⟩ : syracuseStep 774211 = 1161317) B1161317
theorem B774355 : Blo 686314 774355 := bstep (se 1 (by rfl) ⟨580766, by rfl⟩ : syracuseStep 774355 = 1161533) B1161533
theorem B2937073 : Blo 686314 2937073 := bstep (se 2 (by rfl) ⟨1101402, by rfl⟩ : syracuseStep 2937073 = 2202805) B2202805
theorem B2642225 : Blo 686314 2642225 := bstep (se 2 (by rfl) ⟨990834, by rfl⟩ : syracuseStep 2642225 = 1981669) B1981669
theorem B3920197 : Blo 686314 3920197 := bstep (se 4 (by rfl) ⟨367518, by rfl⟩ : syracuseStep 3920197 = 735037) B735037
theorem B774499 : Blo 686314 774499 := bstep (se 1 (by rfl) ⟨580874, by rfl⟩ : syracuseStep 774499 = 1161749) B1161749
theorem B872851 : Blo 686314 872851 := bstep (se 1 (by rfl) ⟨654638, by rfl⟩ : syracuseStep 872851 = 1309277) B1309277
theorem B1102243 : Blo 686314 1102243 := bstep (se 1 (by rfl) ⟨826682, by rfl⟩ : syracuseStep 1102243 = 1653365) B1653365
theorem B11162083 : Blo 686314 11162083 := bstep (se 1 (by rfl) ⟨8371562, by rfl⟩ : syracuseStep 11162083 = 16743125) B16743125
theorem B774643 : Blo 686314 774643 := bstep (se 1 (by rfl) ⟨580982, by rfl⟩ : syracuseStep 774643 = 1161965) B1161965
theorem B872947 : Blo 686314 872947 := bstep (se 1 (by rfl) ⟨654710, by rfl⟩ : syracuseStep 872947 = 1309421) B1309421
theorem B1397297 : Blo 686314 1397297 := bstep (se 2 (by rfl) ⟨523986, by rfl⟩ : syracuseStep 1397297 = 1047973) B1047973
theorem B774787 : Blo 686314 774787 := bstep (se 1 (by rfl) ⟨581090, by rfl⟩ : syracuseStep 774787 = 1162181) B1162181
theorem B1102499 : Blo 686314 1102499 := bstep (se 1 (by rfl) ⟨826874, by rfl⟩ : syracuseStep 1102499 = 1653749) B1653749
theorem B774931 : Blo 686314 774931 := bstep (se 1 (by rfl) ⟨581198, by rfl⟩ : syracuseStep 774931 = 1162397) B1162397
theorem B775075 : Blo 686314 775075 := bstep (se 1 (by rfl) ⟨581306, by rfl⟩ : syracuseStep 775075 = 1162613) B1162613
theorem B873443 : Blo 686314 873443 := bstep (se 1 (by rfl) ⟨655082, by rfl⟩ : syracuseStep 873443 = 1310165) B1310165
theorem B775219 : Blo 686314 775219 := bstep (se 1 (by rfl) ⟨581414, by rfl⟩ : syracuseStep 775219 = 1162829) B1162829
theorem B1135745 : Blo 686314 1135745 := bstep (se 2 (by rfl) ⟨425904, by rfl⟩ : syracuseStep 1135745 = 851809) B851809
theorem B775363 : Blo 686314 775363 := bstep (se 1 (by rfl) ⟨581522, by rfl⟩ : syracuseStep 775363 = 1163045) B1163045
theorem B775507 : Blo 686314 775507 := bstep (se 1 (by rfl) ⟨581630, by rfl⟩ : syracuseStep 775507 = 1163261) B1163261
theorem B775651 : Blo 686314 775651 := bstep (se 1 (by rfl) ⟨581738, by rfl⟩ : syracuseStep 775651 = 1163477) B1163477
theorem B2610701 : Blo 686314 2610701 := bstep (se 3 (by rfl) ⟨489506, by rfl⟩ : syracuseStep 2610701 = 979013) B979013
theorem B1955441 : Blo 686314 1955441 := bstep (se 2 (by rfl) ⟨733290, by rfl⟩ : syracuseStep 1955441 = 1466581) B1466581
theorem B1103473 : Blo 686314 1103473 := bstep (se 2 (by rfl) ⟨413802, by rfl⟩ : syracuseStep 1103473 = 827605) B827605
theorem B775795 : Blo 686314 775795 := bstep (se 1 (by rfl) ⟨581846, by rfl⟩ : syracuseStep 775795 = 1163693) B1163693
theorem B775939 : Blo 686314 775939 := bstep (se 1 (by rfl) ⟨581954, by rfl⟩ : syracuseStep 775939 = 1163909) B1163909
theorem B7460677 : Blo 686314 7460677 := bstep (se 4 (by rfl) ⟨699438, by rfl⟩ : syracuseStep 7460677 = 1398877) B1398877
theorem B776083 : Blo 686314 776083 := bstep (se 1 (by rfl) ⟨582062, by rfl⟩ : syracuseStep 776083 = 1164125) B1164125
theorem B776227 : Blo 686314 776227 := bstep (se 1 (by rfl) ⟨582170, by rfl⟩ : syracuseStep 776227 = 1164341) B1164341
theorem B12572813 : Blo 686314 12572813 := bstep (se 3 (by rfl) ⟨2357402, by rfl⟩ : syracuseStep 12572813 = 4714805) B4714805
theorem B3725453 : Blo 686314 3725453 := bstep (se 3 (by rfl) ⟨698522, by rfl⟩ : syracuseStep 3725453 = 1397045) B1397045
theorem B2480291 : Blo 686314 2480291 := bstep (se 1 (by rfl) ⟨1860218, by rfl⟩ : syracuseStep 2480291 = 3720437) B3720437
theorem B776371 : Blo 686314 776371 := bstep (se 1 (by rfl) ⟨582278, by rfl⟩ : syracuseStep 776371 = 1164557) B1164557
theorem B3922181 : Blo 686314 3922181 := bstep (se 4 (by rfl) ⟨367704, by rfl⟩ : syracuseStep 3922181 = 735409) B735409
theorem B1956113 : Blo 686314 1956113 := bstep (se 2 (by rfl) ⟨733542, by rfl⟩ : syracuseStep 1956113 = 1467085) B1467085
theorem B776515 : Blo 686314 776515 := bstep (se 1 (by rfl) ⟨582386, by rfl⟩ : syracuseStep 776515 = 1164773) B1164773
theorem B2316653 : Blo 686314 2316653 := bstep (se 3 (by rfl) ⟨434372, by rfl⟩ : syracuseStep 2316653 = 868745) B868745
theorem B2316707 : Blo 686314 2316707 := bstep (se 1 (by rfl) ⟨1737530, by rfl⟩ : syracuseStep 2316707 = 3475061) B3475061
theorem B5888497 : Blo 686314 5888497 := bstep (se 2 (by rfl) ⟨2208186, by rfl⟩ : syracuseStep 5888497 = 4416373) B4416373
theorem B1104401 : Blo 686314 1104401 := bstep (se 2 (by rfl) ⟨414150, by rfl⟩ : syracuseStep 1104401 = 828301) B828301
theorem B2316977 : Blo 686314 2316977 := bstep (se 2 (by rfl) ⟨868866, by rfl⟩ : syracuseStep 2316977 = 1737733) B1737733
theorem B3300173 : Blo 686314 3300173 := bstep (se 3 (by rfl) ⟨618782, by rfl⟩ : syracuseStep 3300173 = 1237565) B1237565
theorem B3300365 : Blo 686314 3300365 := bstep (se 3 (by rfl) ⟨618818, by rfl⟩ : syracuseStep 3300365 = 1237637) B1237637
theorem B1956899 : Blo 686314 1956899 := bstep (se 1 (by rfl) ⟨1467674, by rfl⟩ : syracuseStep 1956899 = 2935349) B2935349
theorem B5233733 : Blo 686314 5233733 := bstep (se 4 (by rfl) ⟨490662, by rfl⟩ : syracuseStep 5233733 = 981325) B981325
theorem B2317517 : Blo 686314 2317517 := bstep (se 3 (by rfl) ⟨434534, by rfl⟩ : syracuseStep 2317517 = 869069) B869069
theorem B3300593 : Blo 686314 3300593 := bstep (se 2 (by rfl) ⟨1237722, by rfl⟩ : syracuseStep 3300593 = 2475445) B2475445
theorem B2317571 : Blo 686314 2317571 := bstep (se 1 (by rfl) ⟨1738178, by rfl⟩ : syracuseStep 2317571 = 3476357) B3476357
theorem B2153731 : Blo 686314 2153731 := bstep (se 1 (by rfl) ⟨1615298, by rfl⟩ : syracuseStep 2153731 = 3230597) B3230597
theorem B4414733 : Blo 686314 4414733 := bstep (se 3 (by rfl) ⟨827762, by rfl⟩ : syracuseStep 4414733 = 1655525) B1655525
theorem B1989937 : Blo 686314 1989937 := bstep (se 2 (by rfl) ⟨746226, by rfl⟩ : syracuseStep 1989937 = 1492453) B1492453
theorem B1105235 : Blo 686314 1105235 := bstep (se 1 (by rfl) ⟨828926, by rfl⟩ : syracuseStep 1105235 = 1657853) B1657853
theorem B1957229 : Blo 686314 1957229 := bstep (se 3 (by rfl) ⟨366980, by rfl⟩ : syracuseStep 1957229 = 733961) B733961
theorem B1105267 : Blo 686314 1105267 := bstep (se 1 (by rfl) ⟨828950, by rfl⟩ : syracuseStep 1105267 = 1657901) B1657901
theorem B3300749 : Blo 686314 3300749 := bstep (se 3 (by rfl) ⟨618890, by rfl⟩ : syracuseStep 3300749 = 1237781) B1237781
theorem B4709773 : Blo 686314 4709773 := bstep (se 3 (by rfl) ⟨883082, by rfl⟩ : syracuseStep 4709773 = 1766165) B1766165
theorem B2088355 : Blo 686314 2088355 := bstep (se 1 (by rfl) ⟨1566266, by rfl⟩ : syracuseStep 2088355 = 3132533) B3132533
theorem B1957297 : Blo 686314 1957297 := bstep (se 2 (by rfl) ⟨733986, by rfl⟩ : syracuseStep 1957297 = 1467973) B1467973
theorem B2317841 : Blo 686314 2317841 := bstep (se 2 (by rfl) ⟨869190, by rfl⟩ : syracuseStep 2317841 = 1738381) B1738381
theorem B1957571 : Blo 686314 1957571 := bstep (se 1 (by rfl) ⟨1468178, by rfl⟩ : syracuseStep 1957571 = 2936357) B2936357
theorem B1859345 : Blo 686314 1859345 := bstep (se 2 (by rfl) ⟨697254, by rfl⟩ : syracuseStep 1859345 = 1394509) B1394509
theorem B2318381 : Blo 686314 2318381 := bstep (se 3 (by rfl) ⟨434696, by rfl⟩ : syracuseStep 2318381 = 869393) B869393
theorem B2318435 : Blo 686314 2318435 := bstep (se 1 (by rfl) ⟨1738826, by rfl⟩ : syracuseStep 2318435 = 3477653) B3477653
theorem B2941105 : Blo 686314 2941105 := bstep (se 2 (by rfl) ⟨1102914, by rfl⟩ : syracuseStep 2941105 = 2205829) B2205829
theorem B2482481 : Blo 686314 2482481 := bstep (se 2 (by rfl) ⟨930930, by rfl⟩ : syracuseStep 2482481 = 1861861) B1861861
theorem B4251973 : Blo 686314 4251973 := bstep (se 4 (by rfl) ⟨398622, by rfl⟩ : syracuseStep 4251973 = 797245) B797245
theorem B2318705 : Blo 686314 2318705 := bstep (se 2 (by rfl) ⟨869514, by rfl⟩ : syracuseStep 2318705 = 1739029) B1739029
theorem B2613617 : Blo 686314 2613617 := bstep (se 2 (by rfl) ⟨980106, by rfl⟩ : syracuseStep 2613617 = 1960213) B1960213
theorem B2646413 : Blo 686314 2646413 := bstep (se 3 (by rfl) ⟨496202, by rfl⟩ : syracuseStep 2646413 = 992405) B992405
theorem B6283747 : Blo 686314 6283747 := bstep (se 1 (by rfl) ⟨4712810, by rfl⟩ : syracuseStep 6283747 = 9425621) B9425621
theorem B1958413 : Blo 686314 1958413 := bstep (se 3 (by rfl) ⟨367202, by rfl⟩ : syracuseStep 1958413 = 734405) B734405
theorem B4186637 : Blo 686314 4186637 := bstep (se 3 (by rfl) ⟨784994, by rfl⟩ : syracuseStep 4186637 = 1569989) B1569989
theorem B1303057 : Blo 686314 1303057 := bstep (se 2 (by rfl) ⟨488646, by rfl⟩ : syracuseStep 1303057 = 977293) B977293
theorem B1860131 : Blo 686314 1860131 := bstep (se 1 (by rfl) ⟨1395098, by rfl⟩ : syracuseStep 1860131 = 2790197) B2790197
theorem B1860241 : Blo 686314 1860241 := bstep (se 2 (by rfl) ⟨697590, by rfl⟩ : syracuseStep 1860241 = 1395181) B1395181
theorem B1958573 : Blo 686314 1958573 := bstep (se 3 (by rfl) ⟨367232, by rfl⟩ : syracuseStep 1958573 = 734465) B734465
theorem B4186829 : Blo 686314 4186829 := bstep (se 3 (by rfl) ⟨785030, by rfl⟩ : syracuseStep 4186829 = 1570061) B1570061
theorem B1958755 : Blo 686314 1958755 := bstep (se 1 (by rfl) ⟨1469066, by rfl⟩ : syracuseStep 1958755 = 2938133) B2938133
theorem B2319245 : Blo 686314 2319245 := bstep (se 3 (by rfl) ⟨434858, by rfl⟩ : syracuseStep 2319245 = 869717) B869717
theorem B2319299 : Blo 686314 2319299 := bstep (se 1 (by rfl) ⟨1739474, by rfl⟩ : syracuseStep 2319299 = 3478949) B3478949
theorem B1467409 : Blo 686314 1467409 := bstep (se 2 (by rfl) ⟨550278, by rfl⟩ : syracuseStep 1467409 = 1100557) B1100557
theorem B1238179 : Blo 686314 1238179 := bstep (se 1 (by rfl) ⟨928634, by rfl⟩ : syracuseStep 1238179 = 1857269) B1857269
theorem B2483405 : Blo 686314 2483405 := bstep (se 3 (by rfl) ⟨465638, by rfl⟩ : syracuseStep 2483405 = 931277) B931277
theorem B2319569 : Blo 686314 2319569 := bstep (se 2 (by rfl) ⟨869838, by rfl⟩ : syracuseStep 2319569 = 1739677) B1739677
theorem B1467811 : Blo 686314 1467811 := bstep (se 1 (by rfl) ⟨1100858, by rfl⟩ : syracuseStep 1467811 = 2201717) B2201717
theorem B1304113 : Blo 686314 1304113 := bstep (se 2 (by rfl) ⟨489042, by rfl⟩ : syracuseStep 1304113 = 978085) B978085
theorem B2090605 : Blo 686314 2090605 := bstep (se 3 (by rfl) ⟨391988, by rfl⟩ : syracuseStep 2090605 = 783977) B783977
theorem B1762961 : Blo 686314 1762961 := bstep (se 2 (by rfl) ⟨661110, by rfl⟩ : syracuseStep 1762961 = 1322221) B1322221
theorem B4187825 : Blo 686314 4187825 := bstep (se 2 (by rfl) ⟨1570434, by rfl⟩ : syracuseStep 4187825 = 3140869) B3140869
theorem B2090701 : Blo 686314 2090701 := bstep (se 3 (by rfl) ⟨392006, by rfl⟩ : syracuseStep 2090701 = 784013) B784013
theorem B2320109 : Blo 686314 2320109 := bstep (se 3 (by rfl) ⟨435020, by rfl⟩ : syracuseStep 2320109 = 870041) B870041
theorem B2320163 : Blo 686314 2320163 := bstep (se 1 (by rfl) ⟨1740122, by rfl⟩ : syracuseStep 2320163 = 3480245) B3480245
theorem B2615075 : Blo 686314 2615075 := bstep (se 1 (by rfl) ⟨1961306, by rfl⟩ : syracuseStep 2615075 = 3922613) B3922613
theorem B1238833 : Blo 686314 1238833 := bstep (se 2 (by rfl) ⟨464562, by rfl⟩ : syracuseStep 1238833 = 929125) B929125
theorem B1566641 : Blo 686314 1566641 := bstep (se 2 (by rfl) ⟨587490, by rfl⟩ : syracuseStep 1566641 = 1174981) B1174981
theorem B1304515 : Blo 686314 1304515 := bstep (se 1 (by rfl) ⟨978386, by rfl⟩ : syracuseStep 1304515 = 1956773) B1956773
theorem B3139555 : Blo 686314 3139555 := bstep (se 1 (by rfl) ⟨2354666, by rfl⟩ : syracuseStep 3139555 = 4709333) B4709333
theorem B1304561 : Blo 686314 1304561 := bstep (se 2 (by rfl) ⟨489210, by rfl⟩ : syracuseStep 1304561 = 978421) B978421
theorem B3926029 : Blo 686314 3926029 := bstep (se 3 (by rfl) ⟨736130, by rfl⟩ : syracuseStep 3926029 = 1472261) B1472261
theorem B2320433 : Blo 686314 2320433 := bstep (se 2 (by rfl) ⟨870162, by rfl⟩ : syracuseStep 2320433 = 1740325) B1740325
theorem B1960145 : Blo 686314 1960145 := bstep (se 2 (by rfl) ⟨735054, by rfl⟩ : syracuseStep 1960145 = 1470109) B1470109
theorem B25389283 : Blo 686314 25389283 := bstep (se 1 (by rfl) ⟨19041962, by rfl⟩ : syracuseStep 25389283 = 38083925) B38083925
theorem B16705763 : Blo 686314 16705763 := bstep (se 1 (by rfl) ⟨12529322, by rfl⟩ : syracuseStep 16705763 = 25058645) B25058645
theorem B8349965 : Blo 686314 8349965 := bstep (se 3 (by rfl) ⟨1565618, by rfl⟩ : syracuseStep 8349965 = 3131237) B3131237
theorem B1304849 : Blo 686314 1304849 := bstep (se 2 (by rfl) ⟨489318, by rfl⟩ : syracuseStep 1304849 = 978637) B978637
theorem B4417861 : Blo 686314 4417861 := bstep (se 4 (by rfl) ⟨414174, by rfl⟩ : syracuseStep 4417861 = 828349) B828349
theorem B1239395 : Blo 686314 1239395 := bstep (se 1 (by rfl) ⟨929546, by rfl⟩ : syracuseStep 1239395 = 1859093) B1859093
theorem B2320973 : Blo 686314 2320973 := bstep (se 3 (by rfl) ⟨435182, by rfl⟩ : syracuseStep 2320973 = 870365) B870365
theorem B977521 : Blo 686314 977521 := bstep (se 2 (by rfl) ⟨366570, by rfl⟩ : syracuseStep 977521 = 733141) B733141
theorem B2321027 : Blo 686314 2321027 := bstep (se 1 (by rfl) ⟨1740770, by rfl⟩ : syracuseStep 2321027 = 3481541) B3481541
theorem B977555 : Blo 686314 977555 := bstep (se 1 (by rfl) ⟨733166, by rfl⟩ : syracuseStep 977555 = 1466333) B1466333
theorem B2616077 : Blo 686314 2616077 := bstep (se 3 (by rfl) ⟨490514, by rfl⟩ : syracuseStep 2616077 = 981029) B981029
theorem B1239857 : Blo 686314 1239857 := bstep (se 2 (by rfl) ⟨464946, by rfl⟩ : syracuseStep 1239857 = 929893) B929893
theorem B3533645 : Blo 686314 3533645 := bstep (se 3 (by rfl) ⟨662558, by rfl⟩ : syracuseStep 3533645 = 1325117) B1325117
theorem B2091857 : Blo 686314 2091857 := bstep (se 2 (by rfl) ⟨784446, by rfl⟩ : syracuseStep 2091857 = 1568893) B1568893
theorem B1469315 : Blo 686314 1469315 := bstep (se 1 (by rfl) ⟨1101986, by rfl⟩ : syracuseStep 1469315 = 2203973) B2203973
theorem B2321297 : Blo 686314 2321297 := bstep (se 2 (by rfl) ⟨870486, by rfl⟩ : syracuseStep 2321297 = 1740973) B1740973
theorem B1305571 : Blo 686314 1305571 := bstep (se 1 (by rfl) ⟨979178, by rfl⟩ : syracuseStep 1305571 = 1958357) B1958357
theorem B2354285 : Blo 686314 2354285 := bstep (se 3 (by rfl) ⟨441428, by rfl⟩ : syracuseStep 2354285 = 882857) B882857
theorem B1961101 : Blo 686314 1961101 := bstep (se 3 (by rfl) ⟨367706, by rfl⟩ : syracuseStep 1961101 = 735413) B735413
theorem B978113 : Blo 686314 978113 := bstep (se 2 (by rfl) ⟨366792, by rfl⟩ : syracuseStep 978113 = 733585) B733585
theorem B978193 : Blo 686314 978193 := bstep (se 2 (by rfl) ⟨366822, by rfl⟩ : syracuseStep 978193 = 733645) B733645
theorem B1961329 : Blo 686314 1961329 := bstep (se 2 (by rfl) ⟨735498, by rfl⟩ : syracuseStep 1961329 = 1470997) B1470997
theorem B1306019 : Blo 686314 1306019 := bstep (se 1 (by rfl) ⟨979514, by rfl⟩ : syracuseStep 1306019 = 1959029) B1959029
theorem B2321837 : Blo 686314 2321837 := bstep (se 3 (by rfl) ⟨435344, by rfl⟩ : syracuseStep 2321837 = 870689) B870689
theorem B2321891 : Blo 686314 2321891 := bstep (se 1 (by rfl) ⟨1741418, by rfl⟩ : syracuseStep 2321891 = 3482837) B3482837
theorem B1961489 : Blo 686314 1961489 := bstep (se 2 (by rfl) ⟨735558, by rfl⟩ : syracuseStep 1961489 = 1471117) B1471117
theorem B75492917 : Blo 686314 75492917 := bstep (se 5 (by rfl) ⟨3538730, by rfl⟩ : syracuseStep 75492917 = 7077461) B7077461
theorem B2977357 : Blo 686314 2977357 := bstep (se 3 (by rfl) ⟨558254, by rfl⟩ : syracuseStep 2977357 = 1116509) B1116509
theorem B1863245 : Blo 686314 1863245 := bstep (se 3 (by rfl) ⟨349358, by rfl⟩ : syracuseStep 1863245 = 698717) B698717
theorem B1961603 : Blo 686314 1961603 := bstep (se 1 (by rfl) ⟨1471202, by rfl⟩ : syracuseStep 1961603 = 2942405) B2942405
theorem B1306307 : Blo 686314 1306307 := bstep (se 1 (by rfl) ⟨979730, by rfl⟩ : syracuseStep 1306307 = 1959461) B1959461
theorem B5893829 : Blo 686314 5893829 := bstep (se 4 (by rfl) ⟨552546, by rfl⟩ : syracuseStep 5893829 = 1105093) B1105093
theorem B2322161 : Blo 686314 2322161 := bstep (se 2 (by rfl) ⟨870810, by rfl⟩ : syracuseStep 2322161 = 1741621) B1741621
theorem B2944781 : Blo 686314 2944781 := bstep (se 3 (by rfl) ⟨552146, by rfl⟩ : syracuseStep 2944781 = 1104293) B1104293
theorem B3928013 : Blo 686314 3928013 := bstep (se 3 (by rfl) ⟨736502, by rfl⟩ : syracuseStep 3928013 = 1473005) B1473005
theorem B978979 : Blo 686314 978979 := bstep (se 1 (by rfl) ⟨734234, by rfl⟩ : syracuseStep 978979 = 1468469) B1468469
theorem B1470545 : Blo 686314 1470545 := bstep (se 2 (by rfl) ⟨551454, by rfl⟩ : syracuseStep 1470545 = 1102909) B1102909
theorem B2322701 : Blo 686314 2322701 := bstep (se 3 (by rfl) ⟨435506, by rfl⟩ : syracuseStep 2322701 = 871013) B871013
theorem B2322755 : Blo 686314 2322755 := bstep (se 1 (by rfl) ⟨1742066, by rfl⟩ : syracuseStep 2322755 = 3484133) B3484133
theorem B1044913 : Blo 686314 1044913 := bstep (se 2 (by rfl) ⟨391842, by rfl⟩ : syracuseStep 1044913 = 783685) B783685
theorem B979457 : Blo 686314 979457 := bstep (se 2 (by rfl) ⟨367296, by rfl⟩ : syracuseStep 979457 = 734593) B734593
theorem B2323025 : Blo 686314 2323025 := bstep (se 2 (by rfl) ⟨871134, by rfl⟩ : syracuseStep 2323025 = 1742269) B1742269
theorem B1962605 : Blo 686314 1962605 := bstep (se 3 (by rfl) ⟨367988, by rfl⟩ : syracuseStep 1962605 = 735977) B735977
theorem B1307249 : Blo 686314 1307249 := bstep (se 2 (by rfl) ⟨490218, by rfl⟩ : syracuseStep 1307249 = 980437) B980437
theorem B979571 : Blo 686314 979571 := bstep (se 1 (by rfl) ⟨734678, by rfl⟩ : syracuseStep 979571 = 1469357) B1469357
theorem B979651 : Blo 686314 979651 := bstep (se 1 (by rfl) ⟨734738, by rfl⟩ : syracuseStep 979651 = 1469477) B1469477
theorem B5239565 : Blo 686314 5239565 := bstep (se 3 (by rfl) ⟨982418, by rfl⟩ : syracuseStep 5239565 = 1964837) B1964837
theorem B1962787 : Blo 686314 1962787 := bstep (se 1 (by rfl) ⟨1472090, by rfl⟩ : syracuseStep 1962787 = 2944181) B2944181
theorem B2618189 : Blo 686314 2618189 := bstep (se 3 (by rfl) ⟨490910, by rfl⟩ : syracuseStep 2618189 = 981821) B981821
theorem B3928945 : Blo 686314 3928945 := bstep (se 2 (by rfl) ⟨1473354, by rfl⟩ : syracuseStep 3928945 = 2946709) B2946709
theorem B1962947 : Blo 686314 1962947 := bstep (se 1 (by rfl) ⟨1472210, by rfl⟩ : syracuseStep 1962947 = 2944421) B2944421
theorem B1471441 : Blo 686314 1471441 := bstep (se 2 (by rfl) ⟨551790, by rfl⟩ : syracuseStep 1471441 = 1103581) B1103581
theorem B1471459 : Blo 686314 1471459 := bstep (se 1 (by rfl) ⟨1103594, by rfl⟩ : syracuseStep 1471459 = 2207189) B2207189
theorem B2323565 : Blo 686314 2323565 := bstep (se 3 (by rfl) ⟨435668, by rfl⟩ : syracuseStep 2323565 = 871337) B871337
theorem B2323619 : Blo 686314 2323619 := bstep (se 1 (by rfl) ⟨1742714, by rfl⟩ : syracuseStep 2323619 = 3485429) B3485429
theorem B980209 : Blo 686314 980209 := bstep (se 2 (by rfl) ⟨367578, by rfl⟩ : syracuseStep 980209 = 735157) B735157
theorem B12711221 : Blo 686314 12711221 := bstep (se 5 (by rfl) ⟨595838, by rfl⟩ : syracuseStep 12711221 = 1191677) B1191677
theorem B1242467 : Blo 686314 1242467 := bstep (se 1 (by rfl) ⟨931850, by rfl⟩ : syracuseStep 1242467 = 1863701) B1863701
theorem B2323889 : Blo 686314 2323889 := bstep (se 2 (by rfl) ⟨871458, by rfl⟩ : syracuseStep 2323889 = 1742917) B1742917
theorem B1308145 : Blo 686314 1308145 := bstep (se 2 (by rfl) ⟨490554, by rfl⟩ : syracuseStep 1308145 = 981109) B981109
theorem B1046081 : Blo 686314 1046081 := bstep (se 2 (by rfl) ⟨392280, by rfl⟩ : syracuseStep 1046081 = 784561) B784561
theorem B2618993 : Blo 686314 2618993 := bstep (se 2 (by rfl) ⟨982122, by rfl⟩ : syracuseStep 2618993 = 1964245) B1964245
theorem B1308305 : Blo 686314 1308305 := bstep (se 2 (by rfl) ⟨490614, by rfl⟩ : syracuseStep 1308305 = 981229) B981229
theorem B1242769 : Blo 686314 1242769 := bstep (se 2 (by rfl) ⟨466038, by rfl⟩ : syracuseStep 1242769 = 932077) B932077
theorem B1570691 : Blo 686314 1570691 := bstep (se 1 (by rfl) ⟨1178018, by rfl⟩ : syracuseStep 1570691 = 2356037) B2356037
theorem B980915 : Blo 686314 980915 := bstep (se 1 (by rfl) ⟨735686, by rfl⟩ : syracuseStep 980915 = 1471373) B1471373
theorem B2324429 : Blo 686314 2324429 := bstep (se 3 (by rfl) ⟨435830, by rfl⟩ : syracuseStep 2324429 = 871661) B871661
theorem B1964017 : Blo 686314 1964017 := bstep (se 2 (by rfl) ⟨736506, by rfl⟩ : syracuseStep 1964017 = 1473013) B1473013
theorem B1046531 : Blo 686314 1046531 := bstep (se 1 (by rfl) ⟨784898, by rfl⟩ : syracuseStep 1046531 = 1569797) B1569797
theorem B2324483 : Blo 686314 2324483 := bstep (se 1 (by rfl) ⟨1743362, by rfl⟩ : syracuseStep 2324483 = 3486725) B3486725
theorem B1308707 : Blo 686314 1308707 := bstep (se 1 (by rfl) ⟨981530, by rfl⟩ : syracuseStep 1308707 = 1963061) B1963061
theorem B686323 : Blo 686314 686323 := bstep (se 1 (by rfl) ⟨514742, by rfl⟩ : syracuseStep 686323 = 1029485) B1029485
theorem B686339 : Blo 686314 686339 := bstep (se 1 (by rfl) ⟨514754, by rfl⟩ : syracuseStep 686339 = 1029509) B1029509
theorem B2619661 : Blo 686314 2619661 := bstep (se 3 (by rfl) ⟨491186, by rfl⟩ : syracuseStep 2619661 = 982373) B982373
theorem B2324753 : Blo 686314 2324753 := bstep (se 2 (by rfl) ⟨871782, by rfl⟩ : syracuseStep 2324753 = 1743565) B1743565
theorem B686355 : Blo 686314 686355 := bstep (se 1 (by rfl) ⟨514766, by rfl⟩ : syracuseStep 686355 = 1029533) B1029533
theorem B686371 : Blo 686314 686371 := bstep (se 1 (by rfl) ⟨514778, by rfl⟩ : syracuseStep 686371 = 1029557) B1029557
theorem B3930403 : Blo 686314 3930403 := bstep (se 1 (by rfl) ⟨2947802, by rfl⟩ : syracuseStep 3930403 = 5895605) B5895605
theorem B686387 : Blo 686314 686387 := bstep (se 1 (by rfl) ⟨514790, by rfl⟩ : syracuseStep 686387 = 1029581) B1029581
theorem B686403 : Blo 686314 686403 := bstep (se 1 (by rfl) ⟨514802, by rfl⟩ : syracuseStep 686403 = 1029605) B1029605
theorem B686419 : Blo 686314 686419 := bstep (se 1 (by rfl) ⟨514814, by rfl⟩ : syracuseStep 686419 = 1029629) B1029629
theorem B686435 : Blo 686314 686435 := bstep (se 1 (by rfl) ⟨514826, by rfl⟩ : syracuseStep 686435 = 1029653) B1029653
theorem B784739 : Blo 686314 784739 := bstep (se 1 (by rfl) ⟨588554, by rfl⟩ : syracuseStep 784739 = 1177109) B1177109
theorem B686451 : Blo 686314 686451 := bstep (se 1 (by rfl) ⟨514838, by rfl⟩ : syracuseStep 686451 = 1029677) B1029677
theorem B686467 : Blo 686314 686467 := bstep (se 1 (by rfl) ⟨514850, by rfl⟩ : syracuseStep 686467 = 1029701) B1029701
theorem B686483 : Blo 686314 686483 := bstep (se 1 (by rfl) ⟨514862, by rfl⟩ : syracuseStep 686483 = 1029725) B1029725
theorem B686499 : Blo 686314 686499 := bstep (se 1 (by rfl) ⟨514874, by rfl⟩ : syracuseStep 686499 = 1029749) B1029749
theorem B686515 : Blo 686314 686515 := bstep (se 1 (by rfl) ⟨514886, by rfl⟩ : syracuseStep 686515 = 1029773) B1029773
theorem B686531 : Blo 686314 686531 := bstep (se 1 (by rfl) ⟨514898, by rfl⟩ : syracuseStep 686531 = 1029797) B1029797
theorem B686547 : Blo 686314 686547 := bstep (se 1 (by rfl) ⟨514910, by rfl⟩ : syracuseStep 686547 = 1029821) B1029821
theorem B686563 : Blo 686314 686563 := bstep (se 1 (by rfl) ⟨514922, by rfl⟩ : syracuseStep 686563 = 1029845) B1029845
theorem B686579 : Blo 686314 686579 := bstep (se 1 (by rfl) ⟨514934, by rfl⟩ : syracuseStep 686579 = 1029869) B1029869
theorem B686595 : Blo 686314 686595 := bstep (se 1 (by rfl) ⟨514946, by rfl⟩ : syracuseStep 686595 = 1029893) B1029893
theorem B2521613 : Blo 686314 2521613 := bstep (se 3 (by rfl) ⟨472802, by rfl⟩ : syracuseStep 2521613 = 945605) B945605
theorem B686611 : Blo 686314 686611 := bstep (se 1 (by rfl) ⟨514958, by rfl⟩ : syracuseStep 686611 = 1029917) B1029917
theorem B686627 : Blo 686314 686627 := bstep (se 1 (by rfl) ⟨514970, by rfl⟩ : syracuseStep 686627 = 1029941) B1029941
theorem B981553 : Blo 686314 981553 := bstep (se 2 (by rfl) ⟨368082, by rfl⟩ : syracuseStep 981553 = 736165) B736165
theorem B686643 : Blo 686314 686643 := bstep (se 1 (by rfl) ⟨514982, by rfl⟩ : syracuseStep 686643 = 1029965) B1029965
theorem B686659 : Blo 686314 686659 := bstep (se 1 (by rfl) ⟨514994, by rfl⟩ : syracuseStep 686659 = 1029989) B1029989
theorem B686675 : Blo 686314 686675 := bstep (se 1 (by rfl) ⟨515006, by rfl⟩ : syracuseStep 686675 = 1030013) B1030013
theorem B686691 : Blo 686314 686691 := bstep (se 1 (by rfl) ⟨515018, by rfl⟩ : syracuseStep 686691 = 1030037) B1030037
theorem B686707 : Blo 686314 686707 := bstep (se 1 (by rfl) ⟨515030, by rfl⟩ : syracuseStep 686707 = 1030061) B1030061
theorem B686723 : Blo 686314 686723 := bstep (se 1 (by rfl) ⟨515042, by rfl⟩ : syracuseStep 686723 = 1030085) B1030085
theorem B686739 : Blo 686314 686739 := bstep (se 1 (by rfl) ⟨515054, by rfl⟩ : syracuseStep 686739 = 1030109) B1030109
theorem B686755 : Blo 686314 686755 := bstep (se 1 (by rfl) ⟨515066, by rfl⟩ : syracuseStep 686755 = 1030133) B1030133
theorem B981667 : Blo 686314 981667 := bstep (se 1 (by rfl) ⟨736250, by rfl⟩ : syracuseStep 981667 = 1472501) B1472501
theorem B686771 : Blo 686314 686771 := bstep (se 1 (by rfl) ⟨515078, by rfl⟩ : syracuseStep 686771 = 1030157) B1030157
theorem B686787 : Blo 686314 686787 := bstep (se 1 (by rfl) ⟨515090, by rfl⟩ : syracuseStep 686787 = 1030181) B1030181
theorem B686803 : Blo 686314 686803 := bstep (se 1 (by rfl) ⟨515102, by rfl⟩ : syracuseStep 686803 = 1030205) B1030205
theorem B686819 : Blo 686314 686819 := bstep (se 1 (by rfl) ⟨515114, by rfl⟩ : syracuseStep 686819 = 1030229) B1030229
theorem B686835 : Blo 686314 686835 := bstep (se 1 (by rfl) ⟨515126, by rfl⟩ : syracuseStep 686835 = 1030253) B1030253
theorem B686851 : Blo 686314 686851 := bstep (se 1 (by rfl) ⟨515138, by rfl⟩ : syracuseStep 686851 = 1030277) B1030277
theorem B686867 : Blo 686314 686867 := bstep (se 1 (by rfl) ⟨515150, by rfl⟩ : syracuseStep 686867 = 1030301) B1030301
theorem B686883 : Blo 686314 686883 := bstep (se 1 (by rfl) ⟨515162, by rfl⟩ : syracuseStep 686883 = 1030325) B1030325
theorem B3308323 : Blo 686314 3308323 := bstep (se 1 (by rfl) ⟨2481242, by rfl⟩ : syracuseStep 3308323 = 4962485) B4962485
theorem B2325293 : Blo 686314 2325293 := bstep (se 3 (by rfl) ⟨435992, by rfl⟩ : syracuseStep 2325293 = 871985) B871985
theorem B3930929 : Blo 686314 3930929 := bstep (se 2 (by rfl) ⟨1474098, by rfl⟩ : syracuseStep 3930929 = 2948197) B2948197
theorem B686899 : Blo 686314 686899 := bstep (se 1 (by rfl) ⟨515174, by rfl⟩ : syracuseStep 686899 = 1030349) B1030349
theorem B686915 : Blo 686314 686915 := bstep (se 1 (by rfl) ⟨515186, by rfl⟩ : syracuseStep 686915 = 1030373) B1030373
theorem B686931 : Blo 686314 686931 := bstep (se 1 (by rfl) ⟨515198, by rfl⟩ : syracuseStep 686931 = 1030397) B1030397
theorem B686947 : Blo 686314 686947 := bstep (se 1 (by rfl) ⟨515210, by rfl⟩ : syracuseStep 686947 = 1030421) B1030421
theorem B2325347 : Blo 686314 2325347 := bstep (se 1 (by rfl) ⟨1744010, by rfl⟩ : syracuseStep 2325347 = 3488021) B3488021
theorem B686963 : Blo 686314 686963 := bstep (se 1 (by rfl) ⟨515222, by rfl⟩ : syracuseStep 686963 = 1030445) B1030445
theorem B686979 : Blo 686314 686979 := bstep (se 1 (by rfl) ⟨515234, by rfl⟩ : syracuseStep 686979 = 1030469) B1030469
theorem B686995 : Blo 686314 686995 := bstep (se 1 (by rfl) ⟨515246, by rfl⟩ : syracuseStep 686995 = 1030493) B1030493
theorem B687011 : Blo 686314 687011 := bstep (se 1 (by rfl) ⟨515258, by rfl⟩ : syracuseStep 687011 = 1030517) B1030517
theorem B1309603 : Blo 686314 1309603 := bstep (se 1 (by rfl) ⟨982202, by rfl⟩ : syracuseStep 1309603 = 1964405) B1964405
theorem B687027 : Blo 686314 687027 := bstep (se 1 (by rfl) ⟨515270, by rfl⟩ : syracuseStep 687027 = 1030541) B1030541
theorem B687043 : Blo 686314 687043 := bstep (se 1 (by rfl) ⟨515282, by rfl⟩ : syracuseStep 687043 = 1030565) B1030565
theorem B687059 : Blo 686314 687059 := bstep (se 1 (by rfl) ⟨515294, by rfl⟩ : syracuseStep 687059 = 1030589) B1030589
theorem B687075 : Blo 686314 687075 := bstep (se 1 (by rfl) ⟨515306, by rfl⟩ : syracuseStep 687075 = 1030613) B1030613
theorem B687091 : Blo 686314 687091 := bstep (se 1 (by rfl) ⟨515318, by rfl⟩ : syracuseStep 687091 = 1030637) B1030637
theorem B687107 : Blo 686314 687107 := bstep (se 1 (by rfl) ⟨515330, by rfl⟩ : syracuseStep 687107 = 1030661) B1030661
theorem B687123 : Blo 686314 687123 := bstep (se 1 (by rfl) ⟨515342, by rfl⟩ : syracuseStep 687123 = 1030685) B1030685
theorem B687139 : Blo 686314 687139 := bstep (se 1 (by rfl) ⟨515354, by rfl⟩ : syracuseStep 687139 = 1030709) B1030709
theorem B2620451 : Blo 686314 2620451 := bstep (se 1 (by rfl) ⟨1965338, by rfl⟩ : syracuseStep 2620451 = 3930677) B3930677
theorem B687155 : Blo 686314 687155 := bstep (se 1 (by rfl) ⟨515366, by rfl⟩ : syracuseStep 687155 = 1030733) B1030733
theorem B687171 : Blo 686314 687171 := bstep (se 1 (by rfl) ⟨515378, by rfl⟩ : syracuseStep 687171 = 1030757) B1030757
theorem B1309763 : Blo 686314 1309763 := bstep (se 1 (by rfl) ⟨982322, by rfl⟩ : syracuseStep 1309763 = 1964645) B1964645
theorem B687187 : Blo 686314 687187 := bstep (se 1 (by rfl) ⟨515390, by rfl⟩ : syracuseStep 687187 = 1030781) B1030781
theorem B687203 : Blo 686314 687203 := bstep (se 1 (by rfl) ⟨515402, by rfl⟩ : syracuseStep 687203 = 1030805) B1030805
theorem B2325617 : Blo 686314 2325617 := bstep (se 2 (by rfl) ⟨872106, by rfl⟩ : syracuseStep 2325617 = 1744213) B1744213
theorem B687219 : Blo 686314 687219 := bstep (se 1 (by rfl) ⟨515414, by rfl⟩ : syracuseStep 687219 = 1030829) B1030829
theorem B687235 : Blo 686314 687235 := bstep (se 1 (by rfl) ⟨515426, by rfl⟩ : syracuseStep 687235 = 1030853) B1030853
theorem B4947085 : Blo 686314 4947085 := bstep (se 3 (by rfl) ⟨927578, by rfl⟩ : syracuseStep 4947085 = 1855157) B1855157
theorem B687251 : Blo 686314 687251 := bstep (se 1 (by rfl) ⟨515438, by rfl⟩ : syracuseStep 687251 = 1030877) B1030877
theorem B687267 : Blo 686314 687267 := bstep (se 1 (by rfl) ⟨515450, by rfl⟩ : syracuseStep 687267 = 1030901) B1030901
theorem B4422833 : Blo 686314 4422833 := bstep (se 2 (by rfl) ⟨1658562, by rfl⟩ : syracuseStep 4422833 = 3317125) B3317125
theorem B687283 : Blo 686314 687283 := bstep (se 1 (by rfl) ⟨515462, by rfl⟩ : syracuseStep 687283 = 1030925) B1030925
theorem B687299 : Blo 686314 687299 := bstep (se 1 (by rfl) ⟨515474, by rfl⟩ : syracuseStep 687299 = 1030949) B1030949
theorem B1473731 : Blo 686314 1473731 := bstep (se 1 (by rfl) ⟨1105298, by rfl⟩ : syracuseStep 1473731 = 2210597) B2210597
theorem B687315 : Blo 686314 687315 := bstep (se 1 (by rfl) ⟨515486, by rfl⟩ : syracuseStep 687315 = 1030973) B1030973
theorem B687331 : Blo 686314 687331 := bstep (se 1 (by rfl) ⟨515498, by rfl⟩ : syracuseStep 687331 = 1030997) B1030997
theorem B14908643 : Blo 686314 14908643 := bstep (se 1 (by rfl) ⟨11181482, by rfl⟩ : syracuseStep 14908643 = 22362965) B22362965
theorem B1965293 : Blo 686314 1965293 := bstep (se 3 (by rfl) ⟨368492, by rfl⟩ : syracuseStep 1965293 = 736985) B736985
theorem B687347 : Blo 686314 687347 := bstep (se 1 (by rfl) ⟨515510, by rfl⟩ : syracuseStep 687347 = 1031021) B1031021
theorem B1178867 : Blo 686314 1178867 := bstep (se 1 (by rfl) ⟨884150, by rfl⟩ : syracuseStep 1178867 = 1768301) B1768301
theorem B1047809 : Blo 686314 1047809 := bstep (se 2 (by rfl) ⟨392928, by rfl⟩ : syracuseStep 1047809 = 785857) B785857
theorem B687363 : Blo 686314 687363 := bstep (se 1 (by rfl) ⟨515522, by rfl⟩ : syracuseStep 687363 = 1031045) B1031045
theorem B687379 : Blo 686314 687379 := bstep (se 1 (by rfl) ⟨515534, by rfl⟩ : syracuseStep 687379 = 1031069) B1031069
theorem B687395 : Blo 686314 687395 := bstep (se 1 (by rfl) ⟨515546, by rfl⟩ : syracuseStep 687395 = 1031093) B1031093
theorem B687411 : Blo 686314 687411 := bstep (se 1 (by rfl) ⟨515558, by rfl⟩ : syracuseStep 687411 = 1031117) B1031117
theorem B687427 : Blo 686314 687427 := bstep (se 1 (by rfl) ⟨515570, by rfl⟩ : syracuseStep 687427 = 1031141) B1031141
theorem B1047875 : Blo 686314 1047875 := bstep (se 1 (by rfl) ⟨785906, by rfl⟩ : syracuseStep 1047875 = 1571813) B1571813
theorem B687443 : Blo 686314 687443 := bstep (se 1 (by rfl) ⟨515582, by rfl⟩ : syracuseStep 687443 = 1031165) B1031165
theorem B687459 : Blo 686314 687459 := bstep (se 1 (by rfl) ⟨515594, by rfl⟩ : syracuseStep 687459 = 1031189) B1031189
theorem B687475 : Blo 686314 687475 := bstep (se 1 (by rfl) ⟨515606, by rfl⟩ : syracuseStep 687475 = 1031213) B1031213
theorem B687491 : Blo 686314 687491 := bstep (se 1 (by rfl) ⟨515618, by rfl⟩ : syracuseStep 687491 = 1031237) B1031237
theorem B687507 : Blo 686314 687507 := bstep (se 1 (by rfl) ⟨515630, by rfl⟩ : syracuseStep 687507 = 1031261) B1031261
theorem B687523 : Blo 686314 687523 := bstep (se 1 (by rfl) ⟨515642, by rfl⟩ : syracuseStep 687523 = 1031285) B1031285
theorem B1965475 : Blo 686314 1965475 := bstep (se 1 (by rfl) ⟨1474106, by rfl⟩ : syracuseStep 1965475 = 2948213) B2948213
theorem B687539 : Blo 686314 687539 := bstep (se 1 (by rfl) ⟨515654, by rfl⟩ : syracuseStep 687539 = 1031309) B1031309
theorem B687555 : Blo 686314 687555 := bstep (se 1 (by rfl) ⟨515666, by rfl⟩ : syracuseStep 687555 = 1031333) B1031333
theorem B1965521 : Blo 686314 1965521 := bstep (se 2 (by rfl) ⟨737070, by rfl⟩ : syracuseStep 1965521 = 1474141) B1474141
theorem B687571 : Blo 686314 687571 := bstep (se 1 (by rfl) ⟨515678, by rfl⟩ : syracuseStep 687571 = 1031357) B1031357
theorem B687587 : Blo 686314 687587 := bstep (se 1 (by rfl) ⟨515690, by rfl⟩ : syracuseStep 687587 = 1031381) B1031381
theorem B687603 : Blo 686314 687603 := bstep (se 1 (by rfl) ⟨515702, by rfl⟩ : syracuseStep 687603 = 1031405) B1031405
theorem B687619 : Blo 686314 687619 := bstep (se 1 (by rfl) ⟨515714, by rfl⟩ : syracuseStep 687619 = 1031429) B1031429
theorem B884243 : Blo 686314 884243 := bstep (se 1 (by rfl) ⟨663182, by rfl⟩ : syracuseStep 884243 = 1326365) B1326365
theorem B687635 : Blo 686314 687635 := bstep (se 1 (by rfl) ⟨515726, by rfl⟩ : syracuseStep 687635 = 1031453) B1031453
theorem B687651 : Blo 686314 687651 := bstep (se 1 (by rfl) ⟨515738, by rfl⟩ : syracuseStep 687651 = 1031477) B1031477
theorem B687667 : Blo 686314 687667 := bstep (se 1 (by rfl) ⟨515750, by rfl⟩ : syracuseStep 687667 = 1031501) B1031501
theorem B687683 : Blo 686314 687683 := bstep (se 1 (by rfl) ⟨515762, by rfl⟩ : syracuseStep 687683 = 1031525) B1031525
theorem B687699 : Blo 686314 687699 := bstep (se 1 (by rfl) ⟨515774, by rfl⟩ : syracuseStep 687699 = 1031549) B1031549
theorem B687715 : Blo 686314 687715 := bstep (se 1 (by rfl) ⟨515786, by rfl⟩ : syracuseStep 687715 = 1031573) B1031573
theorem B687731 : Blo 686314 687731 := bstep (se 1 (by rfl) ⟨515798, by rfl⟩ : syracuseStep 687731 = 1031597) B1031597
theorem B687747 : Blo 686314 687747 := bstep (se 1 (by rfl) ⟨515810, by rfl⟩ : syracuseStep 687747 = 1031621) B1031621
theorem B2326157 : Blo 686314 2326157 := bstep (se 3 (by rfl) ⟨436154, by rfl⟩ : syracuseStep 2326157 = 872309) B872309
theorem B1474193 : Blo 686314 1474193 := bstep (se 2 (by rfl) ⟨552822, by rfl⟩ : syracuseStep 1474193 = 1105645) B1105645
theorem B687763 : Blo 686314 687763 := bstep (se 1 (by rfl) ⟨515822, by rfl⟩ : syracuseStep 687763 = 1031645) B1031645
theorem B687779 : Blo 686314 687779 := bstep (se 1 (by rfl) ⟨515834, by rfl⟩ : syracuseStep 687779 = 1031669) B1031669
theorem B687795 : Blo 686314 687795 := bstep (se 1 (by rfl) ⟨515846, by rfl⟩ : syracuseStep 687795 = 1031693) B1031693
theorem B687811 : Blo 686314 687811 := bstep (se 1 (by rfl) ⟨515858, by rfl⟩ : syracuseStep 687811 = 1031717) B1031717
theorem B2326211 : Blo 686314 2326211 := bstep (se 1 (by rfl) ⟨1744658, by rfl⟩ : syracuseStep 2326211 = 3489317) B3489317
theorem B687827 : Blo 686314 687827 := bstep (se 1 (by rfl) ⟨515870, by rfl⟩ : syracuseStep 687827 = 1031741) B1031741
theorem B687843 : Blo 686314 687843 := bstep (se 1 (by rfl) ⟨515882, by rfl⟩ : syracuseStep 687843 = 1031765) B1031765
theorem B687859 : Blo 686314 687859 := bstep (se 1 (by rfl) ⟨515894, by rfl⟩ : syracuseStep 687859 = 1031789) B1031789
theorem B687875 : Blo 686314 687875 := bstep (se 1 (by rfl) ⟨515906, by rfl⟩ : syracuseStep 687875 = 1031813) B1031813
theorem B687891 : Blo 686314 687891 := bstep (se 1 (by rfl) ⟨515918, by rfl⟩ : syracuseStep 687891 = 1031837) B1031837
theorem B687907 : Blo 686314 687907 := bstep (se 1 (by rfl) ⟨515930, by rfl⟩ : syracuseStep 687907 = 1031861) B1031861
theorem B687923 : Blo 686314 687923 := bstep (se 1 (by rfl) ⟨515942, by rfl⟩ : syracuseStep 687923 = 1031885) B1031885
theorem B687939 : Blo 686314 687939 := bstep (se 1 (by rfl) ⟨515954, by rfl⟩ : syracuseStep 687939 = 1031909) B1031909
theorem B687955 : Blo 686314 687955 := bstep (se 1 (by rfl) ⟨515966, by rfl⟩ : syracuseStep 687955 = 1031933) B1031933
theorem B687971 : Blo 686314 687971 := bstep (se 1 (by rfl) ⟨515978, by rfl⟩ : syracuseStep 687971 = 1031957) B1031957
theorem B687987 : Blo 686314 687987 := bstep (se 1 (by rfl) ⟨515990, by rfl⟩ : syracuseStep 687987 = 1031981) B1031981
theorem B1179523 : Blo 686314 1179523 := bstep (se 1 (by rfl) ⟨884642, by rfl⟩ : syracuseStep 1179523 = 1769285) B1769285
theorem B688003 : Blo 686314 688003 := bstep (se 1 (by rfl) ⟨516002, by rfl⟩ : syracuseStep 688003 = 1032005) B1032005
theorem B688019 : Blo 686314 688019 := bstep (se 1 (by rfl) ⟨516014, by rfl⟩ : syracuseStep 688019 = 1032029) B1032029
theorem B688035 : Blo 686314 688035 := bstep (se 1 (by rfl) ⟨516026, by rfl⟩ : syracuseStep 688035 = 1032053) B1032053
theorem B688051 : Blo 686314 688051 := bstep (se 1 (by rfl) ⟨516038, by rfl⟩ : syracuseStep 688051 = 1032077) B1032077
theorem B688067 : Blo 686314 688067 := bstep (se 1 (by rfl) ⟨516050, by rfl⟩ : syracuseStep 688067 = 1032101) B1032101
theorem B2326481 : Blo 686314 2326481 := bstep (se 2 (by rfl) ⟨872430, by rfl⟩ : syracuseStep 2326481 = 1744861) B1744861
theorem B688083 : Blo 686314 688083 := bstep (se 1 (by rfl) ⟨516062, by rfl⟩ : syracuseStep 688083 = 1032125) B1032125
theorem B688099 : Blo 686314 688099 := bstep (se 1 (by rfl) ⟨516074, by rfl⟩ : syracuseStep 688099 = 1032149) B1032149
theorem B688115 : Blo 686314 688115 := bstep (se 1 (by rfl) ⟨516086, by rfl⟩ : syracuseStep 688115 = 1032173) B1032173
theorem B688139 : Blo 686314 688139 := bstep (se 1 (by rfl) ⟨516104, by rfl⟩ : syracuseStep 688139 = 1032209) B1032209
theorem B688151 : Blo 686314 688151 := bstep (se 1 (by rfl) ⟨516113, by rfl⟩ : syracuseStep 688151 = 1032227) B1032227
theorem B688171 : Blo 686314 688171 := bstep (se 1 (by rfl) ⟨516128, by rfl⟩ : syracuseStep 688171 = 1032257) B1032257
theorem B688183 : Blo 686314 688183 := bstep (se 1 (by rfl) ⟨516137, by rfl⟩ : syracuseStep 688183 = 1032275) B1032275
theorem B688203 : Blo 686314 688203 := bstep (se 1 (by rfl) ⟨516152, by rfl⟩ : syracuseStep 688203 = 1032305) B1032305
theorem B688215 : Blo 686314 688215 := bstep (se 1 (by rfl) ⟨516161, by rfl⟩ : syracuseStep 688215 = 1032323) B1032323
theorem B688235 : Blo 686314 688235 := bstep (se 1 (by rfl) ⟨516176, by rfl⟩ : syracuseStep 688235 = 1032353) B1032353
theorem B688247 : Blo 686314 688247 := bstep (se 1 (by rfl) ⟨516185, by rfl⟩ : syracuseStep 688247 = 1032371) B1032371
theorem B688267 : Blo 686314 688267 := bstep (se 1 (by rfl) ⟨516200, by rfl⟩ : syracuseStep 688267 = 1032401) B1032401
theorem B688279 : Blo 686314 688279 := bstep (se 1 (by rfl) ⟨516209, by rfl⟩ : syracuseStep 688279 = 1032419) B1032419
theorem B688299 : Blo 686314 688299 := bstep (se 1 (by rfl) ⟨516224, by rfl⟩ : syracuseStep 688299 = 1032449) B1032449
theorem B688311 : Blo 686314 688311 := bstep (se 1 (by rfl) ⟨516233, by rfl⟩ : syracuseStep 688311 = 1032467) B1032467
theorem B688331 : Blo 686314 688331 := bstep (se 1 (by rfl) ⟨516248, by rfl⟩ : syracuseStep 688331 = 1032497) B1032497
theorem B688343 : Blo 686314 688343 := bstep (se 1 (by rfl) ⟨516257, by rfl⟩ : syracuseStep 688343 = 1032515) B1032515
theorem B688363 : Blo 686314 688363 := bstep (se 1 (by rfl) ⟨516272, by rfl⟩ : syracuseStep 688363 = 1032545) B1032545
theorem B688375 : Blo 686314 688375 := bstep (se 1 (by rfl) ⟨516281, by rfl⟩ : syracuseStep 688375 = 1032563) B1032563
theorem B688395 : Blo 686314 688395 := bstep (se 1 (by rfl) ⟨516296, by rfl⟩ : syracuseStep 688395 = 1032593) B1032593
theorem B688407 : Blo 686314 688407 := bstep (se 1 (by rfl) ⟨516305, by rfl⟩ : syracuseStep 688407 = 1032611) B1032611
theorem B688427 : Blo 686314 688427 := bstep (se 1 (by rfl) ⟨516320, by rfl⟩ : syracuseStep 688427 = 1032641) B1032641
theorem B688439 : Blo 686314 688439 := bstep (se 1 (by rfl) ⟨516329, by rfl⟩ : syracuseStep 688439 = 1032659) B1032659
theorem B688459 : Blo 686314 688459 := bstep (se 1 (by rfl) ⟨516344, by rfl⟩ : syracuseStep 688459 = 1032689) B1032689
theorem B2326859 : Blo 686314 2326859 := bstep (se 1 (by rfl) ⟨1745144, by rfl⟩ : syracuseStep 2326859 = 3490289) B3490289
theorem B688471 : Blo 686314 688471 := bstep (se 1 (by rfl) ⟨516353, by rfl⟩ : syracuseStep 688471 = 1032707) B1032707
theorem B688491 : Blo 686314 688491 := bstep (se 1 (by rfl) ⟨516368, by rfl⟩ : syracuseStep 688491 = 1032737) B1032737
theorem B688503 : Blo 686314 688503 := bstep (se 1 (by rfl) ⟨516377, by rfl⟩ : syracuseStep 688503 = 1032755) B1032755
theorem B688523 : Blo 686314 688523 := bstep (se 1 (by rfl) ⟨516392, by rfl⟩ : syracuseStep 688523 = 1032785) B1032785
theorem B688535 : Blo 686314 688535 := bstep (se 1 (by rfl) ⟨516401, by rfl⟩ : syracuseStep 688535 = 1032803) B1032803
theorem B1573273 : Blo 686314 1573273 := bstep (se 2 (by rfl) ⟨589977, by rfl⟩ : syracuseStep 1573273 = 1179955) B1179955
theorem B688555 : Blo 686314 688555 := bstep (se 1 (by rfl) ⟨516416, by rfl⟩ : syracuseStep 688555 = 1032833) B1032833
theorem B5669297 : Blo 686314 5669297 := bstep (se 2 (by rfl) ⟨2125986, by rfl⟩ : syracuseStep 5669297 = 4251973) B4251973
theorem B688567 : Blo 686314 688567 := bstep (se 1 (by rfl) ⟨516425, by rfl⟩ : syracuseStep 688567 = 1032851) B1032851
theorem B688587 : Blo 686314 688587 := bstep (se 1 (by rfl) ⟨516440, by rfl⟩ : syracuseStep 688587 = 1032881) B1032881
theorem B688599 : Blo 686314 688599 := bstep (se 1 (by rfl) ⟨516449, by rfl⟩ : syracuseStep 688599 = 1032899) B1032899
theorem B688619 : Blo 686314 688619 := bstep (se 1 (by rfl) ⟨516464, by rfl⟩ : syracuseStep 688619 = 1032929) B1032929
theorem B688631 : Blo 686314 688631 := bstep (se 1 (by rfl) ⟨516473, by rfl⟩ : syracuseStep 688631 = 1032947) B1032947
theorem B688651 : Blo 686314 688651 := bstep (se 1 (by rfl) ⟨516488, by rfl⟩ : syracuseStep 688651 = 1032977) B1032977
theorem B885259 : Blo 686314 885259 := bstep (se 1 (by rfl) ⟨663944, by rfl⟩ : syracuseStep 885259 = 1327889) B1327889
theorem B688663 : Blo 686314 688663 := bstep (se 1 (by rfl) ⟨516497, by rfl⟩ : syracuseStep 688663 = 1032995) B1032995
theorem B688683 : Blo 686314 688683 := bstep (se 1 (by rfl) ⟨516512, by rfl⟩ : syracuseStep 688683 = 1033025) B1033025
theorem B688695 : Blo 686314 688695 := bstep (se 1 (by rfl) ⟨516521, by rfl⟩ : syracuseStep 688695 = 1033043) B1033043
theorem B688715 : Blo 686314 688715 := bstep (se 1 (by rfl) ⟨516536, by rfl⟩ : syracuseStep 688715 = 1033073) B1033073
theorem B688727 : Blo 686314 688727 := bstep (se 1 (by rfl) ⟨516545, by rfl⟩ : syracuseStep 688727 = 1033091) B1033091
theorem B2327129 : Blo 686314 2327129 := bstep (se 2 (by rfl) ⟨872673, by rfl⟩ : syracuseStep 2327129 = 1745347) B1745347
theorem B688747 : Blo 686314 688747 := bstep (se 1 (by rfl) ⟨516560, by rfl⟩ : syracuseStep 688747 = 1033121) B1033121
theorem B688759 : Blo 686314 688759 := bstep (se 1 (by rfl) ⟨516569, by rfl⟩ : syracuseStep 688759 = 1033139) B1033139
theorem B688779 : Blo 686314 688779 := bstep (se 1 (by rfl) ⟨516584, by rfl⟩ : syracuseStep 688779 = 1033169) B1033169
theorem B688791 : Blo 686314 688791 := bstep (se 1 (by rfl) ⟨516593, by rfl⟩ : syracuseStep 688791 = 1033187) B1033187
theorem B688811 : Blo 686314 688811 := bstep (se 1 (by rfl) ⟨516608, by rfl⟩ : syracuseStep 688811 = 1033217) B1033217
theorem B688823 : Blo 686314 688823 := bstep (se 1 (by rfl) ⟨516617, by rfl⟩ : syracuseStep 688823 = 1033235) B1033235
theorem B1737409 : Blo 686314 1737409 := bstep (se 2 (by rfl) ⟨651528, by rfl⟩ : syracuseStep 1737409 = 1303057) B1303057
theorem B688843 : Blo 686314 688843 := bstep (se 1 (by rfl) ⟨516632, by rfl⟩ : syracuseStep 688843 = 1033265) B1033265
theorem B688855 : Blo 686314 688855 := bstep (se 1 (by rfl) ⟨516641, by rfl⟩ : syracuseStep 688855 = 1033283) B1033283
theorem B688875 : Blo 686314 688875 := bstep (se 1 (by rfl) ⟨516656, by rfl⟩ : syracuseStep 688875 = 1033313) B1033313
theorem B688887 : Blo 686314 688887 := bstep (se 1 (by rfl) ⟨516665, by rfl⟩ : syracuseStep 688887 = 1033331) B1033331
theorem B688907 : Blo 686314 688907 := bstep (se 1 (by rfl) ⟨516680, by rfl⟩ : syracuseStep 688907 = 1033361) B1033361
theorem B688919 : Blo 686314 688919 := bstep (se 1 (by rfl) ⟨516689, by rfl⟩ : syracuseStep 688919 = 1033379) B1033379
theorem B2360087 : Blo 686314 2360087 := bstep (se 1 (by rfl) ⟨1770065, by rfl⟩ : syracuseStep 2360087 = 3540131) B3540131
theorem B688939 : Blo 686314 688939 := bstep (se 1 (by rfl) ⟨516704, by rfl⟩ : syracuseStep 688939 = 1033409) B1033409
theorem B688951 : Blo 686314 688951 := bstep (se 1 (by rfl) ⟨516713, by rfl⟩ : syracuseStep 688951 = 1033427) B1033427
theorem B688971 : Blo 686314 688971 := bstep (se 1 (by rfl) ⟨516728, by rfl⟩ : syracuseStep 688971 = 1033457) B1033457
theorem B688983 : Blo 686314 688983 := bstep (se 1 (by rfl) ⟨516737, by rfl⟩ : syracuseStep 688983 = 1033475) B1033475
theorem B689003 : Blo 686314 689003 := bstep (se 1 (by rfl) ⟨516752, by rfl⟩ : syracuseStep 689003 = 1033505) B1033505
theorem B689015 : Blo 686314 689015 := bstep (se 1 (by rfl) ⟨516761, by rfl⟩ : syracuseStep 689015 = 1033523) B1033523
theorem B689035 : Blo 686314 689035 := bstep (se 1 (by rfl) ⟨516776, by rfl⟩ : syracuseStep 689035 = 1033553) B1033553
theorem B689047 : Blo 686314 689047 := bstep (se 1 (by rfl) ⟨516785, by rfl⟩ : syracuseStep 689047 = 1033571) B1033571
theorem B689067 : Blo 686314 689067 := bstep (se 1 (by rfl) ⟨516800, by rfl⟩ : syracuseStep 689067 = 1033601) B1033601
theorem B689079 : Blo 686314 689079 := bstep (se 1 (by rfl) ⟨516809, by rfl⟩ : syracuseStep 689079 = 1033619) B1033619
theorem B689099 : Blo 686314 689099 := bstep (se 1 (by rfl) ⟨516824, by rfl⟩ : syracuseStep 689099 = 1033649) B1033649
theorem B689111 : Blo 686314 689111 := bstep (se 1 (by rfl) ⟨516833, by rfl⟩ : syracuseStep 689111 = 1033667) B1033667
theorem B689131 : Blo 686314 689131 := bstep (se 1 (by rfl) ⟨516848, by rfl⟩ : syracuseStep 689131 = 1033697) B1033697
theorem B689143 : Blo 686314 689143 := bstep (se 1 (by rfl) ⟨516857, by rfl⟩ : syracuseStep 689143 = 1033715) B1033715
theorem B689163 : Blo 686314 689163 := bstep (se 1 (by rfl) ⟨516872, by rfl⟩ : syracuseStep 689163 = 1033745) B1033745
theorem B689175 : Blo 686314 689175 := bstep (se 1 (by rfl) ⟨516881, by rfl⟩ : syracuseStep 689175 = 1033763) B1033763
theorem B689195 : Blo 686314 689195 := bstep (se 1 (by rfl) ⟨516896, by rfl⟩ : syracuseStep 689195 = 1033793) B1033793
theorem B689207 : Blo 686314 689207 := bstep (se 1 (by rfl) ⟨516905, by rfl⟩ : syracuseStep 689207 = 1033811) B1033811
theorem B689227 : Blo 686314 689227 := bstep (se 1 (by rfl) ⟨516920, by rfl⟩ : syracuseStep 689227 = 1033841) B1033841
theorem B689239 : Blo 686314 689239 := bstep (se 1 (by rfl) ⟨516929, by rfl⟩ : syracuseStep 689239 = 1033859) B1033859
theorem B689259 : Blo 686314 689259 := bstep (se 1 (by rfl) ⟨516944, by rfl⟩ : syracuseStep 689259 = 1033889) B1033889
theorem B689271 : Blo 686314 689271 := bstep (se 1 (by rfl) ⟨516953, by rfl⟩ : syracuseStep 689271 = 1033907) B1033907
theorem B5866627 : Blo 686314 5866627 := bstep (se 1 (by rfl) ⟨4399970, by rfl⟩ : syracuseStep 5866627 = 8799941) B8799941
theorem B689291 : Blo 686314 689291 := bstep (se 1 (by rfl) ⟨516968, by rfl⟩ : syracuseStep 689291 = 1033937) B1033937
theorem B689303 : Blo 686314 689303 := bstep (se 1 (by rfl) ⟨516977, by rfl⟩ : syracuseStep 689303 = 1033955) B1033955
theorem B689323 : Blo 686314 689323 := bstep (se 1 (by rfl) ⟨516992, by rfl⟩ : syracuseStep 689323 = 1033985) B1033985
theorem B689335 : Blo 686314 689335 := bstep (se 1 (by rfl) ⟨517001, by rfl⟩ : syracuseStep 689335 = 1034003) B1034003
theorem B689355 : Blo 686314 689355 := bstep (se 1 (by rfl) ⟨517016, by rfl⟩ : syracuseStep 689355 = 1034033) B1034033
theorem B689367 : Blo 686314 689367 := bstep (se 1 (by rfl) ⟨517025, by rfl⟩ : syracuseStep 689367 = 1034051) B1034051
theorem B689387 : Blo 686314 689387 := bstep (se 1 (by rfl) ⟨517040, by rfl⟩ : syracuseStep 689387 = 1034081) B1034081
theorem B689399 : Blo 686314 689399 := bstep (se 1 (by rfl) ⟨517049, by rfl⟩ : syracuseStep 689399 = 1034099) B1034099
theorem B2786563 : Blo 686314 2786563 := bstep (se 1 (by rfl) ⟨2089922, by rfl⟩ : syracuseStep 2786563 = 4179845) B4179845
theorem B689419 : Blo 686314 689419 := bstep (se 1 (by rfl) ⟨517064, by rfl⟩ : syracuseStep 689419 = 1034129) B1034129
theorem B1738007 : Blo 686314 1738007 := bstep (se 1 (by rfl) ⟨1303505, by rfl⟩ : syracuseStep 1738007 = 2607011) B2607011
theorem B689431 : Blo 686314 689431 := bstep (se 1 (by rfl) ⟨517073, by rfl⟩ : syracuseStep 689431 = 1034147) B1034147
theorem B2327831 : Blo 686314 2327831 := bstep (se 1 (by rfl) ⟨1745873, by rfl⟩ : syracuseStep 2327831 = 3491747) B3491747
theorem B689451 : Blo 686314 689451 := bstep (se 1 (by rfl) ⟨517088, by rfl⟩ : syracuseStep 689451 = 1034177) B1034177
theorem B689463 : Blo 686314 689463 := bstep (se 1 (by rfl) ⟨517097, by rfl⟩ : syracuseStep 689463 = 1034195) B1034195
theorem B689483 : Blo 686314 689483 := bstep (se 1 (by rfl) ⟨517112, by rfl⟩ : syracuseStep 689483 = 1034225) B1034225
theorem B689495 : Blo 686314 689495 := bstep (se 1 (by rfl) ⟨517121, by rfl⟩ : syracuseStep 689495 = 1034243) B1034243
theorem B6292829 : Blo 686314 6292829 := bstep (se 3 (by rfl) ⟨1179905, by rfl⟩ : syracuseStep 6292829 = 2359811) B2359811
theorem B689515 : Blo 686314 689515 := bstep (se 1 (by rfl) ⟨517136, by rfl⟩ : syracuseStep 689515 = 1034273) B1034273
theorem B689527 : Blo 686314 689527 := bstep (se 1 (by rfl) ⟨517145, by rfl⟩ : syracuseStep 689527 = 1034291) B1034291
theorem B689547 : Blo 686314 689547 := bstep (se 1 (by rfl) ⟨517160, by rfl⟩ : syracuseStep 689547 = 1034321) B1034321
theorem B689559 : Blo 686314 689559 := bstep (se 1 (by rfl) ⟨517169, by rfl⟩ : syracuseStep 689559 = 1034339) B1034339
theorem B689579 : Blo 686314 689579 := bstep (se 1 (by rfl) ⟨517184, by rfl⟩ : syracuseStep 689579 = 1034369) B1034369
theorem B689591 : Blo 686314 689591 := bstep (se 1 (by rfl) ⟨517193, by rfl⟩ : syracuseStep 689591 = 1034387) B1034387
theorem B689611 : Blo 686314 689611 := bstep (se 1 (by rfl) ⟨517208, by rfl⟩ : syracuseStep 689611 = 1034417) B1034417
theorem B689623 : Blo 686314 689623 := bstep (se 1 (by rfl) ⟨517217, by rfl⟩ : syracuseStep 689623 = 1034435) B1034435
theorem B689643 : Blo 686314 689643 := bstep (se 1 (by rfl) ⟨517232, by rfl⟩ : syracuseStep 689643 = 1034465) B1034465
theorem B689655 : Blo 686314 689655 := bstep (se 1 (by rfl) ⟨517241, by rfl⟩ : syracuseStep 689655 = 1034483) B1034483
theorem B689675 : Blo 686314 689675 := bstep (se 1 (by rfl) ⟨517256, by rfl⟩ : syracuseStep 689675 = 1034513) B1034513
theorem B689687 : Blo 686314 689687 := bstep (se 1 (by rfl) ⟨517265, by rfl⟩ : syracuseStep 689687 = 1034531) B1034531
theorem B689707 : Blo 686314 689707 := bstep (se 1 (by rfl) ⟨517280, by rfl⟩ : syracuseStep 689707 = 1034561) B1034561
theorem B689719 : Blo 686314 689719 := bstep (se 1 (by rfl) ⟨517289, by rfl⟩ : syracuseStep 689719 = 1034579) B1034579
theorem B689739 : Blo 686314 689739 := bstep (se 1 (by rfl) ⟨517304, by rfl⟩ : syracuseStep 689739 = 1034609) B1034609
theorem B689751 : Blo 686314 689751 := bstep (se 1 (by rfl) ⟨517313, by rfl⟩ : syracuseStep 689751 = 1034627) B1034627
theorem B2098777 : Blo 686314 2098777 := bstep (se 2 (by rfl) ⟨787041, by rfl⟩ : syracuseStep 2098777 = 1574083) B1574083
theorem B689771 : Blo 686314 689771 := bstep (se 1 (by rfl) ⟨517328, by rfl⟩ : syracuseStep 689771 = 1034657) B1034657
theorem B689783 : Blo 686314 689783 := bstep (se 1 (by rfl) ⟨517337, by rfl⟩ : syracuseStep 689783 = 1034675) B1034675
theorem B6293123 : Blo 686314 6293123 := bstep (se 1 (by rfl) ⟨4719842, by rfl⟩ : syracuseStep 6293123 = 9439685) B9439685
theorem B689803 : Blo 686314 689803 := bstep (se 1 (by rfl) ⟨517352, by rfl⟩ : syracuseStep 689803 = 1034705) B1034705
theorem B689815 : Blo 686314 689815 := bstep (se 1 (by rfl) ⟨517361, by rfl⟩ : syracuseStep 689815 = 1034723) B1034723
theorem B689835 : Blo 686314 689835 := bstep (se 1 (by rfl) ⟨517376, by rfl⟩ : syracuseStep 689835 = 1034753) B1034753
theorem B1672883 : Blo 686314 1672883 := bstep (se 1 (by rfl) ⟨1254662, by rfl⟩ : syracuseStep 1672883 = 2509325) B2509325
theorem B689847 : Blo 686314 689847 := bstep (se 1 (by rfl) ⟨517385, by rfl⟩ : syracuseStep 689847 = 1034771) B1034771
theorem B689867 : Blo 686314 689867 := bstep (se 1 (by rfl) ⟨517400, by rfl⟩ : syracuseStep 689867 = 1034801) B1034801
theorem B689879 : Blo 686314 689879 := bstep (se 1 (by rfl) ⟨517409, by rfl⟩ : syracuseStep 689879 = 1034819) B1034819
theorem B689899 : Blo 686314 689899 := bstep (se 1 (by rfl) ⟨517424, by rfl⟩ : syracuseStep 689899 = 1034849) B1034849
theorem B689911 : Blo 686314 689911 := bstep (se 1 (by rfl) ⟨517433, by rfl⟩ : syracuseStep 689911 = 1034867) B1034867
theorem B689931 : Blo 686314 689931 := bstep (se 1 (by rfl) ⟨517448, by rfl⟩ : syracuseStep 689931 = 1034897) B1034897
theorem B689943 : Blo 686314 689943 := bstep (se 1 (by rfl) ⟨517457, by rfl⟩ : syracuseStep 689943 = 1034915) B1034915
theorem B689963 : Blo 686314 689963 := bstep (se 1 (by rfl) ⟨517472, by rfl⟩ : syracuseStep 689963 = 1034945) B1034945
theorem B2328371 : Blo 686314 2328371 := bstep (se 1 (by rfl) ⟨1746278, by rfl⟩ : syracuseStep 2328371 = 3492557) B3492557
theorem B689975 : Blo 686314 689975 := bstep (se 1 (by rfl) ⟨517481, by rfl⟩ : syracuseStep 689975 = 1034963) B1034963
theorem B1836875 : Blo 686314 1836875 := bstep (se 1 (by rfl) ⟨1377656, by rfl⟩ : syracuseStep 1836875 = 2755313) B2755313
theorem B689995 : Blo 686314 689995 := bstep (se 1 (by rfl) ⟨517496, by rfl⟩ : syracuseStep 689995 = 1034993) B1034993
theorem B690007 : Blo 686314 690007 := bstep (se 1 (by rfl) ⟨517505, by rfl⟩ : syracuseStep 690007 = 1035011) B1035011
theorem B690027 : Blo 686314 690027 := bstep (se 1 (by rfl) ⟨517520, by rfl⟩ : syracuseStep 690027 = 1035041) B1035041
theorem B690039 : Blo 686314 690039 := bstep (se 1 (by rfl) ⟨517529, by rfl⟩ : syracuseStep 690039 = 1035059) B1035059
theorem B690059 : Blo 686314 690059 := bstep (se 1 (by rfl) ⟨517544, by rfl⟩ : syracuseStep 690059 = 1035089) B1035089
theorem B690071 : Blo 686314 690071 := bstep (se 1 (by rfl) ⟨517553, by rfl⟩ : syracuseStep 690071 = 1035107) B1035107
theorem B690091 : Blo 686314 690091 := bstep (se 1 (by rfl) ⟨517568, by rfl⟩ : syracuseStep 690091 = 1035137) B1035137
theorem B690103 : Blo 686314 690103 := bstep (se 1 (by rfl) ⟨517577, by rfl⟩ : syracuseStep 690103 = 1035155) B1035155
theorem B690123 : Blo 686314 690123 := bstep (se 1 (by rfl) ⟨517592, by rfl⟩ : syracuseStep 690123 = 1035185) B1035185
theorem B690135 : Blo 686314 690135 := bstep (se 1 (by rfl) ⟨517601, by rfl⟩ : syracuseStep 690135 = 1035203) B1035203
theorem B690155 : Blo 686314 690155 := bstep (se 1 (by rfl) ⟨517616, by rfl⟩ : syracuseStep 690155 = 1035233) B1035233
theorem B690167 : Blo 686314 690167 := bstep (se 1 (by rfl) ⟨517625, by rfl⟩ : syracuseStep 690167 = 1035251) B1035251
theorem B690187 : Blo 686314 690187 := bstep (se 1 (by rfl) ⟨517640, by rfl⟩ : syracuseStep 690187 = 1035281) B1035281
theorem B690199 : Blo 686314 690199 := bstep (se 1 (by rfl) ⟨517649, by rfl⟩ : syracuseStep 690199 = 1035299) B1035299
theorem B690219 : Blo 686314 690219 := bstep (se 1 (by rfl) ⟨517664, by rfl⟩ : syracuseStep 690219 = 1035329) B1035329
theorem B690231 : Blo 686314 690231 := bstep (se 1 (by rfl) ⟨517673, by rfl⟩ : syracuseStep 690231 = 1035347) B1035347
theorem B5867585 : Blo 686314 5867585 := bstep (se 2 (by rfl) ⟨2200344, by rfl⟩ : syracuseStep 5867585 = 4400689) B4400689
theorem B1738817 : Blo 686314 1738817 := bstep (se 2 (by rfl) ⟨652056, by rfl⟩ : syracuseStep 1738817 = 1304113) B1304113
theorem B2328641 : Blo 686314 2328641 := bstep (se 2 (by rfl) ⟨873240, by rfl⟩ : syracuseStep 2328641 = 1746481) B1746481
theorem B690251 : Blo 686314 690251 := bstep (se 1 (by rfl) ⟨517688, by rfl⟩ : syracuseStep 690251 = 1035377) B1035377
theorem B690263 : Blo 686314 690263 := bstep (se 1 (by rfl) ⟨517697, by rfl⟩ : syracuseStep 690263 = 1035395) B1035395
theorem B690283 : Blo 686314 690283 := bstep (se 1 (by rfl) ⟨517712, by rfl⟩ : syracuseStep 690283 = 1035425) B1035425
theorem B690295 : Blo 686314 690295 := bstep (se 1 (by rfl) ⟨517721, by rfl⟩ : syracuseStep 690295 = 1035443) B1035443
theorem B5572739 : Blo 686314 5572739 := bstep (se 1 (by rfl) ⟨4179554, by rfl⟩ : syracuseStep 5572739 = 8359109) B8359109
theorem B2787473 : Blo 686314 2787473 := bstep (se 2 (by rfl) ⟨1045302, by rfl⟩ : syracuseStep 2787473 = 2090605) B2090605
theorem B920089 : Blo 686314 920089 := bstep (se 2 (by rfl) ⟨345033, by rfl⟩ : syracuseStep 920089 = 690067) B690067
theorem B3476033 : Blo 686314 3476033 := bstep (se 2 (by rfl) ⟨1303512, by rfl⟩ : syracuseStep 3476033 = 2607025) B2607025
theorem B5573195 : Blo 686314 5573195 := bstep (se 1 (by rfl) ⟨4179896, by rfl⟩ : syracuseStep 5573195 = 8359793) B8359793
theorem B1739353 : Blo 686314 1739353 := bstep (se 2 (by rfl) ⟨652257, by rfl⟩ : syracuseStep 1739353 = 1304515) B1304515
theorem B2329181 : Blo 686314 2329181 := bstep (se 3 (by rfl) ⟨436721, by rfl⟩ : syracuseStep 2329181 = 873443) B873443
theorem B33852377 : Blo 686314 33852377 := bstep (se 2 (by rfl) ⟨12694641, by rfl⟩ : syracuseStep 33852377 = 25389283) B25389283
theorem B28183733 : Blo 686314 28183733 := bstep (se 5 (by rfl) ⟨1321112, by rfl⟩ : syracuseStep 28183733 = 2642225) B2642225
theorem B1740467 : Blo 686314 1740467 := bstep (se 1 (by rfl) ⟨1305350, by rfl⟩ : syracuseStep 1740467 = 2610701) B2610701
theorem B2199257 : Blo 686314 2199257 := bstep (se 2 (by rfl) ⟨824721, by rfl⟩ : syracuseStep 2199257 = 1649443) B1649443
theorem B4951813 : Blo 686314 4951813 := bstep (se 4 (by rfl) ⟨464232, by rfl⟩ : syracuseStep 4951813 = 928465) B928465
theorem B1740761 : Blo 686314 1740761 := bstep (se 2 (by rfl) ⟨652785, by rfl⟩ : syracuseStep 1740761 = 1305571) B1305571
theorem B11145347 : Blo 686314 11145347 := bstep (se 1 (by rfl) ⟨8359010, by rfl⟩ : syracuseStep 11145347 = 16718021) B16718021
theorem B1544345 : Blo 686314 1544345 := bstep (se 2 (by rfl) ⟨579129, by rfl⟩ : syracuseStep 1544345 = 1158259) B1158259
theorem B2789549 : Blo 686314 2789549 := bstep (se 3 (by rfl) ⟨523040, by rfl⟩ : syracuseStep 2789549 = 1046081) B1046081
theorem B1544435 : Blo 686314 1544435 := bstep (se 1 (by rfl) ⟨1158326, by rfl⟩ : syracuseStep 1544435 = 2316653) B2316653
theorem B1544471 : Blo 686314 1544471 := bstep (se 1 (by rfl) ⟨1158353, by rfl⟩ : syracuseStep 1544471 = 2316707) B2316707
theorem B1544651 : Blo 686314 1544651 := bstep (se 1 (by rfl) ⟨1158488, by rfl⟩ : syracuseStep 1544651 = 2316977) B2316977
theorem B3477977 : Blo 686314 3477977 := bstep (se 2 (by rfl) ⟨1304241, by rfl⟩ : syracuseStep 3477977 = 2608483) B2608483
theorem B1544705 : Blo 686314 1544705 := bstep (se 2 (by rfl) ⟨579264, by rfl⟩ : syracuseStep 1544705 = 1158529) B1158529
theorem B2200115 : Blo 686314 2200115 := bstep (se 1 (by rfl) ⟨1650086, by rfl⟩ : syracuseStep 2200115 = 3300173) B3300173
theorem B2200243 : Blo 686314 2200243 := bstep (se 1 (by rfl) ⟨1650182, by rfl⟩ : syracuseStep 2200243 = 3300365) B3300365
theorem B1544921 : Blo 686314 1544921 := bstep (se 2 (by rfl) ⟨579345, by rfl⟩ : syracuseStep 1544921 = 1158691) B1158691
theorem B3969809 : Blo 686314 3969809 := bstep (se 2 (by rfl) ⟨1488678, by rfl⟩ : syracuseStep 3969809 = 2977357) B2977357
theorem B1545011 : Blo 686314 1545011 := bstep (se 1 (by rfl) ⟨1158758, by rfl⟩ : syracuseStep 1545011 = 2317517) B2317517
theorem B2200385 : Blo 686314 2200385 := bstep (se 2 (by rfl) ⟨825144, by rfl⟩ : syracuseStep 2200385 = 1650289) B1650289
theorem B1545047 : Blo 686314 1545047 := bstep (se 1 (by rfl) ⟨1158785, by rfl⟩ : syracuseStep 1545047 = 2317571) B2317571
theorem B2200499 : Blo 686314 2200499 := bstep (se 1 (by rfl) ⟨1650374, by rfl⟩ : syracuseStep 2200499 = 3300749) B3300749
theorem B12587993 : Blo 686314 12587993 := bstep (se 2 (by rfl) ⟨4720497, by rfl⟩ : syracuseStep 12587993 = 9440995) B9440995
theorem B1545227 : Blo 686314 1545227 := bstep (se 1 (by rfl) ⟨1158920, by rfl⟩ : syracuseStep 1545227 = 2317841) B2317841
theorem B1545281 : Blo 686314 1545281 := bstep (se 2 (by rfl) ⟨579480, by rfl⟩ : syracuseStep 1545281 = 1158961) B1158961
theorem B1545497 : Blo 686314 1545497 := bstep (se 2 (by rfl) ⟨579561, by rfl⟩ : syracuseStep 1545497 = 1159123) B1159123
theorem B2790749 : Blo 686314 2790749 := bstep (se 3 (by rfl) ⟨523265, by rfl⟩ : syracuseStep 2790749 = 1046531) B1046531
theorem B1545587 : Blo 686314 1545587 := bstep (se 1 (by rfl) ⟨1159190, by rfl⟩ : syracuseStep 1545587 = 2318381) B2318381
theorem B1545623 : Blo 686314 1545623 := bstep (se 1 (by rfl) ⟨1159217, by rfl⟩ : syracuseStep 1545623 = 2318435) B2318435
theorem B1545803 : Blo 686314 1545803 := bstep (se 1 (by rfl) ⟨1159352, by rfl⟩ : syracuseStep 1545803 = 2318705) B2318705
theorem B1742411 : Blo 686314 1742411 := bstep (se 1 (by rfl) ⟨1306808, by rfl⟩ : syracuseStep 1742411 = 2613617) B2613617
theorem B1545857 : Blo 686314 1545857 := bstep (se 2 (by rfl) ⟨579696, by rfl⟩ : syracuseStep 1545857 = 1159393) B1159393
theorem B3348119 : Blo 686314 3348119 := bstep (se 1 (by rfl) ⟨2511089, by rfl⟩ : syracuseStep 3348119 = 5022179) B5022179
theorem B2791091 : Blo 686314 2791091 := bstep (se 1 (by rfl) ⟨2093318, by rfl⟩ : syracuseStep 2791091 = 4186637) B4186637
theorem B8951597 : Blo 686314 8951597 := bstep (se 3 (by rfl) ⟨1678424, by rfl⟩ : syracuseStep 8951597 = 3356849) B3356849
theorem B1546073 : Blo 686314 1546073 := bstep (se 2 (by rfl) ⟨579777, by rfl⟩ : syracuseStep 1546073 = 1159555) B1159555
theorem B1546163 : Blo 686314 1546163 := bstep (se 1 (by rfl) ⟨1159622, by rfl⟩ : syracuseStep 1546163 = 2319245) B2319245
theorem B1546199 : Blo 686314 1546199 := bstep (se 1 (by rfl) ⟨1159649, by rfl⟩ : syracuseStep 1546199 = 2319299) B2319299
theorem B14882777 : Blo 686314 14882777 := bstep (se 2 (by rfl) ⟨5581041, by rfl⟩ : syracuseStep 14882777 = 11162083) B11162083
theorem B3479597 : Blo 686314 3479597 := bstep (se 3 (by rfl) ⟨652424, by rfl⟩ : syracuseStep 3479597 = 1304849) B1304849
theorem B1546379 : Blo 686314 1546379 := bstep (se 1 (by rfl) ⟨1159784, by rfl⟩ : syracuseStep 1546379 = 2319569) B2319569
theorem B1546433 : Blo 686314 1546433 := bstep (se 2 (by rfl) ⟨579912, by rfl⟩ : syracuseStep 1546433 = 1159825) B1159825
theorem B13211909 : Blo 686314 13211909 := bstep (se 4 (by rfl) ⟨1238616, by rfl⟩ : syracuseStep 13211909 = 2477233) B2477233
theorem B21174533 : Blo 686314 21174533 := bstep (se 4 (by rfl) ⟨1985112, by rfl⟩ : syracuseStep 21174533 = 3970225) B3970225
theorem B8395073 : Blo 686314 8395073 := bstep (se 2 (by rfl) ⟨3148152, by rfl⟩ : syracuseStep 8395073 = 6296305) B6296305
theorem B1546649 : Blo 686314 1546649 := bstep (se 2 (by rfl) ⟨579993, by rfl⟩ : syracuseStep 1546649 = 1159987) B1159987
theorem B2791883 : Blo 686314 2791883 := bstep (se 1 (by rfl) ⟨2093912, by rfl⟩ : syracuseStep 2791883 = 4187825) B4187825
theorem B1546739 : Blo 686314 1546739 := bstep (se 1 (by rfl) ⟨1160054, by rfl⟩ : syracuseStep 1546739 = 2320109) B2320109
theorem B1546775 : Blo 686314 1546775 := bstep (se 1 (by rfl) ⟨1160081, by rfl⟩ : syracuseStep 1546775 = 2320163) B2320163
theorem B1743383 : Blo 686314 1743383 := bstep (se 1 (by rfl) ⟨1307537, by rfl⟩ : syracuseStep 1743383 = 2615075) B2615075
theorem B1546955 : Blo 686314 1546955 := bstep (se 1 (by rfl) ⟨1160216, by rfl⟩ : syracuseStep 1546955 = 2320433) B2320433
theorem B1547009 : Blo 686314 1547009 := bstep (se 2 (by rfl) ⟨580128, by rfl⟩ : syracuseStep 1547009 = 1160257) B1160257
theorem B4397975 : Blo 686314 4397975 := bstep (se 1 (by rfl) ⟨3298481, by rfl⟩ : syracuseStep 4397975 = 6596963) B6596963
theorem B1547225 : Blo 686314 1547225 := bstep (se 2 (by rfl) ⟨580209, by rfl⟩ : syracuseStep 1547225 = 1160419) B1160419
theorem B1547315 : Blo 686314 1547315 := bstep (se 1 (by rfl) ⟨1160486, by rfl⟩ : syracuseStep 1547315 = 2320973) B2320973
theorem B1547351 : Blo 686314 1547351 := bstep (se 1 (by rfl) ⟨1160513, by rfl⟩ : syracuseStep 1547351 = 2321027) B2321027
theorem B1744051 : Blo 686314 1744051 := bstep (se 1 (by rfl) ⟨1308038, by rfl⟩ : syracuseStep 1744051 = 2616077) B2616077
theorem B826571 : Blo 686314 826571 := bstep (se 1 (by rfl) ⟨619928, by rfl⟩ : syracuseStep 826571 = 1239857) B1239857
theorem B1547531 : Blo 686314 1547531 := bstep (se 1 (by rfl) ⟨1160648, by rfl⟩ : syracuseStep 1547531 = 2321297) B2321297
theorem B1547585 : Blo 686314 1547585 := bstep (se 2 (by rfl) ⟨580344, by rfl⟩ : syracuseStep 1547585 = 1160689) B1160689
theorem B1744193 : Blo 686314 1744193 := bstep (se 2 (by rfl) ⟨654072, by rfl⟩ : syracuseStep 1744193 = 1308145) B1308145
theorem B8068531 : Blo 686314 8068531 := bstep (se 1 (by rfl) ⟨6051398, by rfl⟩ : syracuseStep 8068531 = 12102797) B12102797
theorem B1547801 : Blo 686314 1547801 := bstep (se 2 (by rfl) ⟨580425, by rfl⟩ : syracuseStep 1547801 = 1160851) B1160851
theorem B1547891 : Blo 686314 1547891 := bstep (se 1 (by rfl) ⟨1160918, by rfl⟩ : syracuseStep 1547891 = 2321837) B2321837
theorem B1547927 : Blo 686314 1547927 := bstep (se 1 (by rfl) ⟨1160945, by rfl⟩ : syracuseStep 1547927 = 2321891) B2321891
theorem B1941185 : Blo 686314 1941185 := bstep (se 2 (by rfl) ⟨727944, by rfl⟩ : syracuseStep 1941185 = 1455889) B1455889
theorem B2203357 : Blo 686314 2203357 := bstep (se 3 (by rfl) ⟨413129, by rfl⟩ : syracuseStep 2203357 = 826259) B826259
theorem B1548107 : Blo 686314 1548107 := bstep (se 1 (by rfl) ⟨1161080, by rfl⟩ : syracuseStep 1548107 = 2322161) B2322161
theorem B1548161 : Blo 686314 1548161 := bstep (se 2 (by rfl) ⟨580560, by rfl⟩ : syracuseStep 1548161 = 1161121) B1161121
theorem B7839665 : Blo 686314 7839665 := bstep (se 2 (by rfl) ⟨2939874, by rfl⟩ : syracuseStep 7839665 = 5879749) B5879749
theorem B1548377 : Blo 686314 1548377 := bstep (se 2 (by rfl) ⟨580641, by rfl⟩ : syracuseStep 1548377 = 1161283) B1161283
theorem B1548467 : Blo 686314 1548467 := bstep (se 1 (by rfl) ⟨1161350, by rfl⟩ : syracuseStep 1548467 = 2322701) B2322701
theorem B1548503 : Blo 686314 1548503 := bstep (se 1 (by rfl) ⟨1161377, by rfl⟩ : syracuseStep 1548503 = 2322755) B2322755
theorem B1548683 : Blo 686314 1548683 := bstep (se 1 (by rfl) ⟨1161512, by rfl⟩ : syracuseStep 1548683 = 2323025) B2323025
theorem B1548737 : Blo 686314 1548737 := bstep (se 2 (by rfl) ⟨580776, by rfl⟩ : syracuseStep 1548737 = 1161553) B1161553
theorem B1745459 : Blo 686314 1745459 := bstep (se 1 (by rfl) ⟨1309094, by rfl⟩ : syracuseStep 1745459 = 2618189) B2618189
theorem B2237021 : Blo 686314 2237021 := bstep (se 3 (by rfl) ⟨419441, by rfl⟩ : syracuseStep 2237021 = 838883) B838883
theorem B1548953 : Blo 686314 1548953 := bstep (se 2 (by rfl) ⟨580857, by rfl⟩ : syracuseStep 1548953 = 1161715) B1161715
theorem B3023581 : Blo 686314 3023581 := bstep (se 3 (by rfl) ⟨566921, by rfl⟩ : syracuseStep 3023581 = 1133843) B1133843
theorem B1549043 : Blo 686314 1549043 := bstep (se 1 (by rfl) ⟨1161782, by rfl⟩ : syracuseStep 1549043 = 2323565) B2323565
theorem B1549079 : Blo 686314 1549079 := bstep (se 1 (by rfl) ⟨1161809, by rfl⟩ : syracuseStep 1549079 = 2323619) B2323619
theorem B2794333 : Blo 686314 2794333 := bstep (se 3 (by rfl) ⟨523937, by rfl⟩ : syracuseStep 2794333 = 1047875) B1047875
theorem B828311 : Blo 686314 828311 := bstep (se 1 (by rfl) ⟨621233, by rfl⟩ : syracuseStep 828311 = 1242467) B1242467
theorem B1549259 : Blo 686314 1549259 := bstep (se 1 (by rfl) ⟨1161944, by rfl⟩ : syracuseStep 1549259 = 2323889) B2323889
theorem B1549313 : Blo 686314 1549313 := bstep (se 2 (by rfl) ⟨580992, by rfl⟩ : syracuseStep 1549313 = 1161985) B1161985
theorem B11150405 : Blo 686314 11150405 := bstep (se 4 (by rfl) ⟨1045350, by rfl⟩ : syracuseStep 11150405 = 2090701) B2090701
theorem B1745995 : Blo 686314 1745995 := bstep (se 1 (by rfl) ⟨1309496, by rfl⟩ : syracuseStep 1745995 = 2618993) B2618993
theorem B1549529 : Blo 686314 1549529 := bstep (se 2 (by rfl) ⟨581073, by rfl⟩ : syracuseStep 1549529 = 1162147) B1162147
theorem B1746137 : Blo 686314 1746137 := bstep (se 2 (by rfl) ⟨654801, by rfl⟩ : syracuseStep 1746137 = 1309603) B1309603
theorem B1549619 : Blo 686314 1549619 := bstep (se 1 (by rfl) ⟨1162214, by rfl⟩ : syracuseStep 1549619 = 2324429) B2324429
theorem B1549655 : Blo 686314 1549655 := bstep (se 1 (by rfl) ⟨1162241, by rfl⟩ : syracuseStep 1549655 = 2324483) B2324483
theorem B1549835 : Blo 686314 1549835 := bstep (se 1 (by rfl) ⟨1162376, by rfl⟩ : syracuseStep 1549835 = 2324753) B2324753
theorem B6596113 : Blo 686314 6596113 := bstep (se 2 (by rfl) ⟨2473542, by rfl⟩ : syracuseStep 6596113 = 4947085) B4947085
theorem B1549889 : Blo 686314 1549889 := bstep (se 2 (by rfl) ⟨581208, by rfl⟩ : syracuseStep 1549889 = 1162417) B1162417
theorem B1681075 : Blo 686314 1681075 := bstep (se 1 (by rfl) ⟨1260806, by rfl⟩ : syracuseStep 1681075 = 2521613) B2521613
theorem B1550105 : Blo 686314 1550105 := bstep (se 2 (by rfl) ⟨581289, by rfl⟩ : syracuseStep 1550105 = 1162579) B1162579
theorem B3483485 : Blo 686314 3483485 := bstep (se 3 (by rfl) ⟨653153, by rfl⟩ : syracuseStep 3483485 = 1306307) B1306307
theorem B1550195 : Blo 686314 1550195 := bstep (se 1 (by rfl) ⟨1162646, by rfl⟩ : syracuseStep 1550195 = 2325293) B2325293
theorem B1550231 : Blo 686314 1550231 := bstep (se 1 (by rfl) ⟨1162673, by rfl⟩ : syracuseStep 1550231 = 2325347) B2325347
theorem B1746967 : Blo 686314 1746967 := bstep (se 1 (by rfl) ⟨1310225, by rfl⟩ : syracuseStep 1746967 = 2620451) B2620451
theorem B20129867 : Blo 686314 20129867 := bstep (se 1 (by rfl) ⟨15097400, by rfl⟩ : syracuseStep 20129867 = 30194801) B30194801
theorem B1550411 : Blo 686314 1550411 := bstep (se 1 (by rfl) ⟨1162808, by rfl⟩ : syracuseStep 1550411 = 2325617) B2325617
theorem B1550465 : Blo 686314 1550465 := bstep (se 2 (by rfl) ⟨581424, by rfl⟩ : syracuseStep 1550465 = 1162849) B1162849
theorem B9939095 : Blo 686314 9939095 := bstep (se 1 (by rfl) ⟨7454321, by rfl⟩ : syracuseStep 9939095 = 14908643) B14908643
theorem B698539 : Blo 686314 698539 := bstep (se 1 (by rfl) ⟨523904, by rfl⟩ : syracuseStep 698539 = 1047809) B1047809
theorem B5810381 : Blo 686314 5810381 := bstep (se 3 (by rfl) ⟨1089446, by rfl⟩ : syracuseStep 5810381 = 2178893) B2178893
theorem B1550681 : Blo 686314 1550681 := bstep (se 2 (by rfl) ⟨581505, by rfl⟩ : syracuseStep 1550681 = 1163011) B1163011
theorem B1550771 : Blo 686314 1550771 := bstep (se 1 (by rfl) ⟨1163078, by rfl⟩ : syracuseStep 1550771 = 2326157) B2326157
theorem B1550807 : Blo 686314 1550807 := bstep (se 1 (by rfl) ⟨1163105, by rfl⟩ : syracuseStep 1550807 = 2326211) B2326211
theorem B1550987 : Blo 686314 1550987 := bstep (se 1 (by rfl) ⟨1163240, by rfl⟩ : syracuseStep 1550987 = 2326481) B2326481
theorem B1551041 : Blo 686314 1551041 := bstep (se 2 (by rfl) ⟨581640, by rfl⟩ : syracuseStep 1551041 = 1163281) B1163281
theorem B4402021 : Blo 686314 4402021 := bstep (se 4 (by rfl) ⟨412689, by rfl⟩ : syracuseStep 4402021 = 825379) B825379
theorem B1551257 : Blo 686314 1551257 := bstep (se 2 (by rfl) ⟨581721, by rfl⟩ : syracuseStep 1551257 = 1163443) B1163443
theorem B1551347 : Blo 686314 1551347 := bstep (se 1 (by rfl) ⟨1163510, by rfl⟩ : syracuseStep 1551347 = 2327021) B2327021
theorem B1551383 : Blo 686314 1551383 := bstep (se 1 (by rfl) ⟨1163537, by rfl⟩ : syracuseStep 1551383 = 2327075) B2327075
theorem B1485899 : Blo 686314 1485899 := bstep (se 1 (by rfl) ⟨1114424, by rfl⟩ : syracuseStep 1485899 = 2228849) B2228849
theorem B1158347 : Blo 686314 1158347 := bstep (se 1 (by rfl) ⟨868760, by rfl⟩ : syracuseStep 1158347 = 1737521) B1737521
theorem B1551563 : Blo 686314 1551563 := bstep (se 1 (by rfl) ⟨1163672, by rfl⟩ : syracuseStep 1551563 = 2327345) B2327345
theorem B1551617 : Blo 686314 1551617 := bstep (se 2 (by rfl) ⟨581856, by rfl⟩ : syracuseStep 1551617 = 1163713) B1163713
theorem B1158475 : Blo 686314 1158475 := bstep (se 1 (by rfl) ⟨868856, by rfl⟩ : syracuseStep 1158475 = 1737713) B1737713
theorem B1158617 : Blo 686314 1158617 := bstep (se 2 (by rfl) ⟨434481, by rfl⟩ : syracuseStep 1158617 = 868963) B868963
theorem B1551833 : Blo 686314 1551833 := bstep (se 2 (by rfl) ⟨581937, by rfl⟩ : syracuseStep 1551833 = 1163875) B1163875
theorem B1551923 : Blo 686314 1551923 := bstep (se 1 (by rfl) ⟨1163942, by rfl⟩ : syracuseStep 1551923 = 2327885) B2327885
theorem B1551959 : Blo 686314 1551959 := bstep (se 1 (by rfl) ⟨1163969, by rfl⟩ : syracuseStep 1551959 = 2327939) B2327939
theorem B1158745 : Blo 686314 1158745 := bstep (se 2 (by rfl) ⟨434529, by rfl⟩ : syracuseStep 1158745 = 869059) B869059
theorem B1552139 : Blo 686314 1552139 := bstep (se 1 (by rfl) ⟨1164104, by rfl⟩ : syracuseStep 1552139 = 2328209) B2328209
theorem B1552193 : Blo 686314 1552193 := bstep (se 2 (by rfl) ⟨582072, by rfl⟩ : syracuseStep 1552193 = 1164145) B1164145
theorem B1322839 : Blo 686314 1322839 := bstep (se 1 (by rfl) ⟨992129, by rfl⟩ : syracuseStep 1322839 = 1984259) B1984259
theorem B3485591 : Blo 686314 3485591 := bstep (se 1 (by rfl) ⟨2614193, by rfl⟩ : syracuseStep 3485591 = 5228387) B5228387
theorem B14135219 : Blo 686314 14135219 := bstep (se 1 (by rfl) ⟨10601414, by rfl⟩ : syracuseStep 14135219 = 21202829) B21202829
theorem B1552409 : Blo 686314 1552409 := bstep (se 2 (by rfl) ⟨582153, by rfl⟩ : syracuseStep 1552409 = 1164307) B1164307
theorem B10203205 : Blo 686314 10203205 := bstep (se 4 (by rfl) ⟨956550, by rfl⟩ : syracuseStep 10203205 = 1913101) B1913101
theorem B4960349 : Blo 686314 4960349 := bstep (se 3 (by rfl) ⟨930065, by rfl⟩ : syracuseStep 4960349 = 1860131) B1860131
theorem B1552499 : Blo 686314 1552499 := bstep (se 1 (by rfl) ⟨1164374, by rfl⟩ : syracuseStep 1552499 = 2328749) B2328749
theorem B733303 : Blo 686314 733303 := bstep (se 1 (by rfl) ⟨549977, by rfl⟩ : syracuseStep 733303 = 1099955) B1099955
theorem B1159319 : Blo 686314 1159319 := bstep (se 1 (by rfl) ⟨869489, by rfl⟩ : syracuseStep 1159319 = 1738979) B1738979
theorem B1552535 : Blo 686314 1552535 := bstep (se 1 (by rfl) ⟨1164401, by rfl⟩ : syracuseStep 1552535 = 2328803) B2328803
theorem B1650905 : Blo 686314 1650905 := bstep (se 2 (by rfl) ⟨619089, by rfl⟩ : syracuseStep 1650905 = 1238179) B1238179
theorem B1159447 : Blo 686314 1159447 := bstep (se 1 (by rfl) ⟨869585, by rfl⟩ : syracuseStep 1159447 = 1739171) B1739171
theorem B1552715 : Blo 686314 1552715 := bstep (se 1 (by rfl) ⟨1164536, by rfl⟩ : syracuseStep 1552715 = 2329073) B2329073
theorem B5878109 : Blo 686314 5878109 := bstep (se 3 (by rfl) ⟨1102145, by rfl⟩ : syracuseStep 5878109 = 2204291) B2204291
theorem B1552769 : Blo 686314 1552769 := bstep (se 2 (by rfl) ⟨582288, by rfl⟩ : syracuseStep 1552769 = 1164577) B1164577
theorem B1552985 : Blo 686314 1552985 := bstep (se 2 (by rfl) ⟨582369, by rfl⟩ : syracuseStep 1552985 = 1164739) B1164739
theorem B1553075 : Blo 686314 1553075 := bstep (se 1 (by rfl) ⟨1164806, by rfl⟩ : syracuseStep 1553075 = 2329613) B2329613
theorem B1553111 : Blo 686314 1553111 := bstep (se 1 (by rfl) ⟨1164833, by rfl⟩ : syracuseStep 1553111 = 2329667) B2329667
theorem B1487641 : Blo 686314 1487641 := bstep (se 2 (by rfl) ⟨557865, by rfl⟩ : syracuseStep 1487641 = 1115731) B1115731
theorem B1160075 : Blo 686314 1160075 := bstep (se 1 (by rfl) ⟨870056, by rfl⟩ : syracuseStep 1160075 = 1740113) B1740113
theorem B8827825 : Blo 686314 8827825 := bstep (se 2 (by rfl) ⟨3310434, by rfl⟩ : syracuseStep 8827825 = 6620869) B6620869
theorem B1160203 : Blo 686314 1160203 := bstep (se 1 (by rfl) ⟨870152, by rfl⟩ : syracuseStep 1160203 = 1740305) B1740305
theorem B17675333 : Blo 686314 17675333 := bstep (se 4 (by rfl) ⟨1657062, by rfl⟩ : syracuseStep 17675333 = 3314125) B3314125
theorem B1160345 : Blo 686314 1160345 := bstep (se 2 (by rfl) ⟨435129, by rfl⟩ : syracuseStep 1160345 = 870259) B870259
theorem B1160473 : Blo 686314 1160473 := bstep (se 2 (by rfl) ⟨435177, by rfl⟩ : syracuseStep 1160473 = 870355) B870355
theorem B1029515 : Blo 686314 1029515 := bstep (se 1 (by rfl) ⟨772136, by rfl⟩ : syracuseStep 1029515 = 1544273) B1544273
theorem B1029527 : Blo 686314 1029527 := bstep (se 1 (by rfl) ⟨772145, by rfl⟩ : syracuseStep 1029527 = 1544291) B1544291
theorem B1029593 : Blo 686314 1029593 := bstep (se 2 (by rfl) ⟨386097, by rfl⟩ : syracuseStep 1029593 = 772195) B772195
theorem B1029707 : Blo 686314 1029707 := bstep (se 1 (by rfl) ⟨772280, by rfl⟩ : syracuseStep 1029707 = 1544561) B1544561
theorem B1029719 : Blo 686314 1029719 := bstep (se 1 (by rfl) ⟨772289, by rfl⟩ : syracuseStep 1029719 = 1544579) B1544579
theorem B1029785 : Blo 686314 1029785 := bstep (se 2 (by rfl) ⟨386169, by rfl⟩ : syracuseStep 1029785 = 772339) B772339
theorem B3913433 : Blo 686314 3913433 := bstep (se 2 (by rfl) ⟨1467537, by rfl⟩ : syracuseStep 3913433 = 2935075) B2935075
theorem B1029899 : Blo 686314 1029899 := bstep (se 1 (by rfl) ⟨772424, by rfl⟩ : syracuseStep 1029899 = 1544849) B1544849
theorem B1029911 : Blo 686314 1029911 := bstep (se 1 (by rfl) ⟨772433, by rfl⟩ : syracuseStep 1029911 = 1544867) B1544867
theorem B734999 : Blo 686314 734999 := bstep (se 1 (by rfl) ⟨551249, by rfl⟩ : syracuseStep 734999 = 1102499) B1102499
theorem B1161047 : Blo 686314 1161047 := bstep (se 1 (by rfl) ⟨870785, by rfl⟩ : syracuseStep 1161047 = 1741571) B1741571
theorem B1029977 : Blo 686314 1029977 := bstep (se 2 (by rfl) ⟨386241, by rfl⟩ : syracuseStep 1029977 = 772483) B772483
theorem B1030091 : Blo 686314 1030091 := bstep (se 1 (by rfl) ⟨772568, by rfl⟩ : syracuseStep 1030091 = 1545137) B1545137
theorem B5027789 : Blo 686314 5027789 := bstep (se 3 (by rfl) ⟨942710, by rfl⟩ : syracuseStep 5027789 = 1885421) B1885421
theorem B1030103 : Blo 686314 1030103 := bstep (se 1 (by rfl) ⟨772577, by rfl⟩ : syracuseStep 1030103 = 1545155) B1545155
theorem B1161175 : Blo 686314 1161175 := bstep (se 1 (by rfl) ⟨870881, by rfl⟩ : syracuseStep 1161175 = 1741763) B1741763
theorem B1030169 : Blo 686314 1030169 := bstep (se 2 (by rfl) ⟨386313, by rfl⟩ : syracuseStep 1030169 = 772627) B772627
theorem B1489025 : Blo 686314 1489025 := bstep (se 2 (by rfl) ⟨558384, by rfl⟩ : syracuseStep 1489025 = 1116769) B1116769
theorem B1030283 : Blo 686314 1030283 := bstep (se 1 (by rfl) ⟨772712, by rfl⟩ : syracuseStep 1030283 = 1545425) B1545425
theorem B1030295 : Blo 686314 1030295 := bstep (se 1 (by rfl) ⟨772721, by rfl⟩ : syracuseStep 1030295 = 1545443) B1545443
theorem B1030361 : Blo 686314 1030361 := bstep (se 2 (by rfl) ⟨386385, by rfl⟩ : syracuseStep 1030361 = 772771) B772771
theorem B1030475 : Blo 686314 1030475 := bstep (se 1 (by rfl) ⟨772856, by rfl⟩ : syracuseStep 1030475 = 1545713) B1545713
theorem B1030487 : Blo 686314 1030487 := bstep (se 1 (by rfl) ⟨772865, by rfl⟩ : syracuseStep 1030487 = 1545731) B1545731
theorem B1030553 : Blo 686314 1030553 := bstep (se 2 (by rfl) ⟨386457, by rfl⟩ : syracuseStep 1030553 = 772915) B772915
theorem B1030667 : Blo 686314 1030667 := bstep (se 1 (by rfl) ⟨773000, by rfl⟩ : syracuseStep 1030667 = 1546001) B1546001
theorem B1030679 : Blo 686314 1030679 := bstep (se 1 (by rfl) ⟨773009, by rfl⟩ : syracuseStep 1030679 = 1546019) B1546019
theorem B1161803 : Blo 686314 1161803 := bstep (se 1 (by rfl) ⟨871352, by rfl⟩ : syracuseStep 1161803 = 1742705) B1742705
theorem B1030745 : Blo 686314 1030745 := bstep (se 2 (by rfl) ⟨386529, by rfl⟩ : syracuseStep 1030745 = 773059) B773059
theorem B1030859 : Blo 686314 1030859 := bstep (se 1 (by rfl) ⟨773144, by rfl⟩ : syracuseStep 1030859 = 1546289) B1546289
theorem B1161931 : Blo 686314 1161931 := bstep (se 1 (by rfl) ⟨871448, by rfl⟩ : syracuseStep 1161931 = 1742897) B1742897
theorem B1030871 : Blo 686314 1030871 := bstep (se 1 (by rfl) ⟨773153, by rfl⟩ : syracuseStep 1030871 = 1546307) B1546307
theorem B1653527 : Blo 686314 1653527 := bstep (se 1 (by rfl) ⟨1240145, by rfl⟩ : syracuseStep 1653527 = 2480291) B2480291
theorem B1030937 : Blo 686314 1030937 := bstep (se 2 (by rfl) ⟨386601, by rfl⟩ : syracuseStep 1030937 = 773203) B773203
theorem B1162073 : Blo 686314 1162073 := bstep (se 2 (by rfl) ⟨435777, by rfl⟩ : syracuseStep 1162073 = 871555) B871555
theorem B5880707 : Blo 686314 5880707 := bstep (se 1 (by rfl) ⟨4410530, by rfl⟩ : syracuseStep 5880707 = 8821061) B8821061
theorem B1031051 : Blo 686314 1031051 := bstep (se 1 (by rfl) ⟨773288, by rfl⟩ : syracuseStep 1031051 = 1546577) B1546577
theorem B1031063 : Blo 686314 1031063 := bstep (se 1 (by rfl) ⟨773297, by rfl⟩ : syracuseStep 1031063 = 1546595) B1546595
theorem B2931659 : Blo 686314 2931659 := bstep (se 1 (by rfl) ⟨2198744, by rfl⟩ : syracuseStep 2931659 = 4397489) B4397489
theorem B1031129 : Blo 686314 1031129 := bstep (se 2 (by rfl) ⟨386673, by rfl⟩ : syracuseStep 1031129 = 773347) B773347
theorem B1162201 : Blo 686314 1162201 := bstep (se 2 (by rfl) ⟨435825, by rfl⟩ : syracuseStep 1162201 = 871651) B871651
theorem B2210777 : Blo 686314 2210777 := bstep (se 2 (by rfl) ⟨829041, by rfl⟩ : syracuseStep 2210777 = 1658083) B1658083
theorem B4701229 : Blo 686314 4701229 := bstep (se 3 (by rfl) ⟨881480, by rfl⟩ : syracuseStep 4701229 = 1762961) B1762961
theorem B1031243 : Blo 686314 1031243 := bstep (se 1 (by rfl) ⟨773432, by rfl⟩ : syracuseStep 1031243 = 1546865) B1546865
theorem B1031255 : Blo 686314 1031255 := bstep (se 1 (by rfl) ⟨773441, by rfl⟩ : syracuseStep 1031255 = 1546883) B1546883
theorem B1031321 : Blo 686314 1031321 := bstep (se 2 (by rfl) ⟨386745, by rfl⟩ : syracuseStep 1031321 = 773491) B773491
theorem B16792757 : Blo 686314 16792757 := bstep (se 5 (by rfl) ⟨787160, by rfl⟩ : syracuseStep 16792757 = 1574321) B1574321
theorem B1031435 : Blo 686314 1031435 := bstep (se 1 (by rfl) ⟨773576, by rfl⟩ : syracuseStep 1031435 = 1547153) B1547153
theorem B1031447 : Blo 686314 1031447 := bstep (se 1 (by rfl) ⟨773585, by rfl⟩ : syracuseStep 1031447 = 1547171) B1547171
theorem B1031513 : Blo 686314 1031513 := bstep (se 2 (by rfl) ⟨386817, by rfl⟩ : syracuseStep 1031513 = 773635) B773635
theorem B3489155 : Blo 686314 3489155 := bstep (se 1 (by rfl) ⟨2616866, by rfl⟩ : syracuseStep 3489155 = 5233733) B5233733
theorem B1031627 : Blo 686314 1031627 := bstep (se 1 (by rfl) ⟨773720, by rfl⟩ : syracuseStep 1031627 = 1547441) B1547441
theorem B1031639 : Blo 686314 1031639 := bstep (se 1 (by rfl) ⟨773729, by rfl⟩ : syracuseStep 1031639 = 1547459) B1547459
theorem B1162775 : Blo 686314 1162775 := bstep (se 1 (by rfl) ⟨872081, by rfl⟩ : syracuseStep 1162775 = 1744163) B1744163
theorem B1031705 : Blo 686314 1031705 := bstep (se 2 (by rfl) ⟨386889, by rfl⟩ : syracuseStep 1031705 = 773779) B773779
theorem B736823 : Blo 686314 736823 := bstep (se 1 (by rfl) ⟨552617, by rfl⟩ : syracuseStep 736823 = 1105235) B1105235
theorem B1031819 : Blo 686314 1031819 := bstep (se 1 (by rfl) ⟨773864, by rfl⟩ : syracuseStep 1031819 = 1547729) B1547729
theorem B1031831 : Blo 686314 1031831 := bstep (se 1 (by rfl) ⟨773873, by rfl⟩ : syracuseStep 1031831 = 1547747) B1547747
theorem B1162903 : Blo 686314 1162903 := bstep (se 1 (by rfl) ⟨872177, by rfl⟩ : syracuseStep 1162903 = 1744355) B1744355
theorem B1031897 : Blo 686314 1031897 := bstep (se 2 (by rfl) ⟨386961, by rfl⟩ : syracuseStep 1031897 = 773923) B773923
theorem B1032011 : Blo 686314 1032011 := bstep (se 1 (by rfl) ⟨774008, by rfl⟩ : syracuseStep 1032011 = 1548017) B1548017
theorem B1032023 : Blo 686314 1032023 := bstep (se 1 (by rfl) ⟨774017, by rfl⟩ : syracuseStep 1032023 = 1548035) B1548035
theorem B2932631 : Blo 686314 2932631 := bstep (se 1 (by rfl) ⟨2199473, by rfl⟩ : syracuseStep 2932631 = 4398947) B4398947
theorem B1032089 : Blo 686314 1032089 := bstep (se 2 (by rfl) ⟨387033, by rfl⟩ : syracuseStep 1032089 = 774067) B774067
theorem B1032203 : Blo 686314 1032203 := bstep (se 1 (by rfl) ⟨774152, by rfl⟩ : syracuseStep 1032203 = 1548305) B1548305
theorem B1032215 : Blo 686314 1032215 := bstep (se 1 (by rfl) ⟨774161, by rfl⟩ : syracuseStep 1032215 = 1548323) B1548323
theorem B1032281 : Blo 686314 1032281 := bstep (se 2 (by rfl) ⟨387105, by rfl⟩ : syracuseStep 1032281 = 774211) B774211
theorem B1032395 : Blo 686314 1032395 := bstep (se 1 (by rfl) ⟨774296, by rfl⟩ : syracuseStep 1032395 = 1548593) B1548593
theorem B1654987 : Blo 686314 1654987 := bstep (se 1 (by rfl) ⟨1241240, by rfl⟩ : syracuseStep 1654987 = 2482481) B2482481
theorem B1032407 : Blo 686314 1032407 := bstep (se 1 (by rfl) ⟨774305, by rfl⟩ : syracuseStep 1032407 = 1548611) B1548611
theorem B1163531 : Blo 686314 1163531 := bstep (se 1 (by rfl) ⟨872648, by rfl⟩ : syracuseStep 1163531 = 1745297) B1745297
theorem B1032473 : Blo 686314 1032473 := bstep (se 2 (by rfl) ⟨387177, by rfl⟩ : syracuseStep 1032473 = 774355) B774355
theorem B3916097 : Blo 686314 3916097 := bstep (se 2 (by rfl) ⟨1468536, by rfl⟩ : syracuseStep 3916097 = 2937073) B2937073
theorem B1032587 : Blo 686314 1032587 := bstep (se 1 (by rfl) ⟨774440, by rfl⟩ : syracuseStep 1032587 = 1548881) B1548881
theorem B1163659 : Blo 686314 1163659 := bstep (se 1 (by rfl) ⟨872744, by rfl⟩ : syracuseStep 1163659 = 1745489) B1745489
theorem B1032599 : Blo 686314 1032599 := bstep (se 1 (by rfl) ⟨774449, by rfl⟩ : syracuseStep 1032599 = 1548899) B1548899
theorem B5226929 : Blo 686314 5226929 := bstep (se 2 (by rfl) ⟨1960098, by rfl⟩ : syracuseStep 5226929 = 3920197) B3920197
theorem B1032665 : Blo 686314 1032665 := bstep (se 2 (by rfl) ⟨387249, by rfl⟩ : syracuseStep 1032665 = 774499) B774499
theorem B1163801 : Blo 686314 1163801 := bstep (se 2 (by rfl) ⟨436425, by rfl⟩ : syracuseStep 1163801 = 872851) B872851
theorem B1393217 : Blo 686314 1393217 := bstep (se 2 (by rfl) ⟨522456, by rfl⟩ : syracuseStep 1393217 = 1044913) B1044913
theorem B1032779 : Blo 686314 1032779 := bstep (se 1 (by rfl) ⟨774584, by rfl⟩ : syracuseStep 1032779 = 1549169) B1549169
theorem B1032791 : Blo 686314 1032791 := bstep (se 1 (by rfl) ⟨774593, by rfl⟩ : syracuseStep 1032791 = 1549187) B1549187
theorem B1032857 : Blo 686314 1032857 := bstep (se 2 (by rfl) ⟨387321, by rfl⟩ : syracuseStep 1032857 = 774643) B774643
theorem B1163929 : Blo 686314 1163929 := bstep (se 2 (by rfl) ⟨436473, by rfl⟩ : syracuseStep 1163929 = 872947) B872947
theorem B1032971 : Blo 686314 1032971 := bstep (se 1 (by rfl) ⟨774728, by rfl⟩ : syracuseStep 1032971 = 1549457) B1549457
theorem B1032983 : Blo 686314 1032983 := bstep (se 1 (by rfl) ⟨774737, by rfl⟩ : syracuseStep 1032983 = 1549475) B1549475
theorem B1655603 : Blo 686314 1655603 := bstep (se 1 (by rfl) ⟨1241702, by rfl⟩ : syracuseStep 1655603 = 2483405) B2483405
theorem B1033049 : Blo 686314 1033049 := bstep (se 2 (by rfl) ⟨387393, by rfl⟩ : syracuseStep 1033049 = 774787) B774787
theorem B5227415 : Blo 686314 5227415 := bstep (se 1 (by rfl) ⟨3920561, by rfl⟩ : syracuseStep 5227415 = 7841123) B7841123
theorem B1033163 : Blo 686314 1033163 := bstep (se 1 (by rfl) ⟨774872, by rfl⟩ : syracuseStep 1033163 = 1549745) B1549745
theorem B1033175 : Blo 686314 1033175 := bstep (se 1 (by rfl) ⟨774881, by rfl⟩ : syracuseStep 1033175 = 1549763) B1549763
theorem B1033241 : Blo 686314 1033241 := bstep (se 2 (by rfl) ⟨387465, by rfl⟩ : syracuseStep 1033241 = 774931) B774931
theorem B1033355 : Blo 686314 1033355 := bstep (se 1 (by rfl) ⟨775016, by rfl⟩ : syracuseStep 1033355 = 1550033) B1550033
theorem B1033367 : Blo 686314 1033367 := bstep (se 1 (by rfl) ⟨775025, by rfl⟩ : syracuseStep 1033367 = 1550051) B1550051
theorem B1164503 : Blo 686314 1164503 := bstep (se 1 (by rfl) ⟨873377, by rfl⟩ : syracuseStep 1164503 = 1746755) B1746755
theorem B1033433 : Blo 686314 1033433 := bstep (se 2 (by rfl) ⟨387537, by rfl⟩ : syracuseStep 1033433 = 775075) B775075
theorem B869707 : Blo 686314 869707 := bstep (se 1 (by rfl) ⟨652280, by rfl⟩ : syracuseStep 869707 = 1304561) B1304561
theorem B1033547 : Blo 686314 1033547 := bstep (se 1 (by rfl) ⟨775160, by rfl⟩ : syracuseStep 1033547 = 1550321) B1550321
theorem B1033559 : Blo 686314 1033559 := bstep (se 1 (by rfl) ⟨775169, by rfl⟩ : syracuseStep 1033559 = 1550339) B1550339
theorem B1164631 : Blo 686314 1164631 := bstep (se 1 (by rfl) ⟨873473, by rfl⟩ : syracuseStep 1164631 = 1746947) B1746947
theorem B1033625 : Blo 686314 1033625 := bstep (se 2 (by rfl) ⟨387609, by rfl⟩ : syracuseStep 1033625 = 775219) B775219
theorem B2606539 : Blo 686314 2606539 := bstep (se 1 (by rfl) ⟨1954904, by rfl⟩ : syracuseStep 2606539 = 3909809) B3909809
theorem B1033739 : Blo 686314 1033739 := bstep (se 1 (by rfl) ⟨775304, by rfl⟩ : syracuseStep 1033739 = 1550609) B1550609
theorem B1033751 : Blo 686314 1033751 := bstep (se 1 (by rfl) ⟨775313, by rfl⟩ : syracuseStep 1033751 = 1550627) B1550627
theorem B1033817 : Blo 686314 1033817 := bstep (se 2 (by rfl) ⟨387681, by rfl⟩ : syracuseStep 1033817 = 775363) B775363
theorem B1033931 : Blo 686314 1033931 := bstep (se 1 (by rfl) ⟨775448, by rfl⟩ : syracuseStep 1033931 = 1550897) B1550897
theorem B1033943 : Blo 686314 1033943 := bstep (se 1 (by rfl) ⟨775457, by rfl⟩ : syracuseStep 1033943 = 1550915) B1550915
theorem B2606813 : Blo 686314 2606813 := bstep (se 3 (by rfl) ⟨488777, by rfl⟩ : syracuseStep 2606813 = 977555) B977555
theorem B1034009 : Blo 686314 1034009 := bstep (se 2 (by rfl) ⟨387753, by rfl⟩ : syracuseStep 1034009 = 775507) B775507
theorem B2475821 : Blo 686314 2475821 := bstep (se 3 (by rfl) ⟨464216, by rfl⟩ : syracuseStep 2475821 = 928433) B928433
theorem B1034123 : Blo 686314 1034123 := bstep (se 1 (by rfl) ⟨775592, by rfl⟩ : syracuseStep 1034123 = 1551185) B1551185
theorem B1034135 : Blo 686314 1034135 := bstep (se 1 (by rfl) ⟨775601, by rfl⟩ : syracuseStep 1034135 = 1551203) B1551203
theorem B1034201 : Blo 686314 1034201 := bstep (se 2 (by rfl) ⟨387825, by rfl⟩ : syracuseStep 1034201 = 775651) B775651
theorem B1034315 : Blo 686314 1034315 := bstep (se 1 (by rfl) ⟨775736, by rfl⟩ : syracuseStep 1034315 = 1551473) B1551473
theorem B1034327 : Blo 686314 1034327 := bstep (se 1 (by rfl) ⟨775745, by rfl⟩ : syracuseStep 1034327 = 1551491) B1551491
theorem B1099865 : Blo 686314 1099865 := bstep (se 2 (by rfl) ⟨412449, by rfl⟩ : syracuseStep 1099865 = 824899) B824899
theorem B1034393 : Blo 686314 1034393 := bstep (se 2 (by rfl) ⟨387897, by rfl⟩ : syracuseStep 1034393 = 775795) B775795
theorem B772267 : Blo 686314 772267 := bstep (se 1 (by rfl) ⟨579200, by rfl⟩ : syracuseStep 772267 = 1158401) B1158401
theorem B1657025 : Blo 686314 1657025 := bstep (se 2 (by rfl) ⟨621384, by rfl⟩ : syracuseStep 1657025 = 1242769) B1242769
theorem B9423053 : Blo 686314 9423053 := bstep (se 3 (by rfl) ⟨1766822, by rfl⟩ : syracuseStep 9423053 = 3533645) B3533645
theorem B1034507 : Blo 686314 1034507 := bstep (se 1 (by rfl) ⟨775880, by rfl⟩ : syracuseStep 1034507 = 1551761) B1551761
theorem B772375 : Blo 686314 772375 := bstep (se 1 (by rfl) ⟨579281, by rfl⟩ : syracuseStep 772375 = 1158563) B1158563
theorem B870679 : Blo 686314 870679 := bstep (se 1 (by rfl) ⟨653009, by rfl⟩ : syracuseStep 870679 = 1306019) B1306019
theorem B1034519 : Blo 686314 1034519 := bstep (se 1 (by rfl) ⟨775889, by rfl⟩ : syracuseStep 1034519 = 1551779) B1551779
theorem B2935091 : Blo 686314 2935091 := bstep (se 1 (by rfl) ⟨2201318, by rfl⟩ : syracuseStep 2935091 = 4402637) B4402637
theorem B1034585 : Blo 686314 1034585 := bstep (se 2 (by rfl) ⟨387969, by rfl⟩ : syracuseStep 1034585 = 775939) B775939
theorem B2607511 : Blo 686314 2607511 := bstep (se 1 (by rfl) ⟨1955633, by rfl⟩ : syracuseStep 2607511 = 3911267) B3911267
theorem B9947569 : Blo 686314 9947569 := bstep (se 2 (by rfl) ⟨3730338, by rfl⟩ : syracuseStep 9947569 = 7460677) B7460677
theorem B772555 : Blo 686314 772555 := bstep (se 1 (by rfl) ⟨579416, by rfl⟩ : syracuseStep 772555 = 1158833) B1158833
theorem B1034699 : Blo 686314 1034699 := bstep (se 1 (by rfl) ⟨776024, by rfl⟩ : syracuseStep 1034699 = 1552049) B1552049
theorem B1034711 : Blo 686314 1034711 := bstep (se 1 (by rfl) ⟨776033, by rfl⟩ : syracuseStep 1034711 = 1552067) B1552067
theorem B1034777 : Blo 686314 1034777 := bstep (se 2 (by rfl) ⟨388041, by rfl⟩ : syracuseStep 1034777 = 776083) B776083
theorem B772663 : Blo 686314 772663 := bstep (se 1 (by rfl) ⟨579497, by rfl⟩ : syracuseStep 772663 = 1158995) B1158995
theorem B1034891 : Blo 686314 1034891 := bstep (se 1 (by rfl) ⟨776168, by rfl⟩ : syracuseStep 1034891 = 1552337) B1552337
theorem B1034903 : Blo 686314 1034903 := bstep (se 1 (by rfl) ⟨776177, by rfl⟩ : syracuseStep 1034903 = 1552355) B1552355
theorem B1493657 : Blo 686314 1493657 := bstep (se 2 (by rfl) ⟨560121, by rfl⟩ : syracuseStep 1493657 = 1120243) B1120243
theorem B1034969 : Blo 686314 1034969 := bstep (se 2 (by rfl) ⟨388113, by rfl⟩ : syracuseStep 1034969 = 776227) B776227
theorem B772843 : Blo 686314 772843 := bstep (se 1 (by rfl) ⟨579632, by rfl⟩ : syracuseStep 772843 = 1159265) B1159265
theorem B1035083 : Blo 686314 1035083 := bstep (se 1 (by rfl) ⟨776312, by rfl⟩ : syracuseStep 1035083 = 1552625) B1552625
theorem B772951 : Blo 686314 772951 := bstep (se 1 (by rfl) ⟨579713, by rfl⟩ : syracuseStep 772951 = 1159427) B1159427
theorem B1035095 : Blo 686314 1035095 := bstep (se 1 (by rfl) ⟨776321, by rfl⟩ : syracuseStep 1035095 = 1552643) B1552643
theorem B1035161 : Blo 686314 1035161 := bstep (se 2 (by rfl) ⟨388185, by rfl⟩ : syracuseStep 1035161 = 776371) B776371
theorem B6278093 : Blo 686314 6278093 := bstep (se 3 (by rfl) ⟨1177142, by rfl⟩ : syracuseStep 6278093 = 2354285) B2354285
theorem B773131 : Blo 686314 773131 := bstep (se 1 (by rfl) ⟨579848, by rfl⟩ : syracuseStep 773131 = 1159697) B1159697
theorem B1035275 : Blo 686314 1035275 := bstep (se 1 (by rfl) ⟨776456, by rfl⟩ : syracuseStep 1035275 = 1552913) B1552913
theorem B3492881 : Blo 686314 3492881 := bstep (se 2 (by rfl) ⟨1309830, by rfl⟩ : syracuseStep 3492881 = 2619661) B2619661
theorem B1035287 : Blo 686314 1035287 := bstep (se 1 (by rfl) ⟨776465, by rfl⟩ : syracuseStep 1035287 = 1552931) B1552931
theorem B871499 : Blo 686314 871499 := bstep (se 1 (by rfl) ⟨653624, by rfl⟩ : syracuseStep 871499 = 1307249) B1307249
theorem B1035353 : Blo 686314 1035353 := bstep (se 2 (by rfl) ⟨388257, by rfl⟩ : syracuseStep 1035353 = 776515) B776515
theorem B773239 : Blo 686314 773239 := bstep (se 1 (by rfl) ⟨579929, by rfl⟩ : syracuseStep 773239 = 1159859) B1159859
theorem B2608301 : Blo 686314 2608301 := bstep (se 3 (by rfl) ⟨489056, by rfl⟩ : syracuseStep 2608301 = 978113) B978113
theorem B3493043 : Blo 686314 3493043 := bstep (se 1 (by rfl) ⟨2619782, by rfl⟩ : syracuseStep 3493043 = 5239565) B5239565
theorem B1035467 : Blo 686314 1035467 := bstep (se 1 (by rfl) ⟨776600, by rfl⟩ : syracuseStep 1035467 = 1553201) B1553201
theorem B3132695 : Blo 686314 3132695 := bstep (se 1 (by rfl) ⟨2349521, by rfl⟩ : syracuseStep 3132695 = 4699043) B4699043
theorem B773419 : Blo 686314 773419 := bstep (se 1 (by rfl) ⟨580064, by rfl⟩ : syracuseStep 773419 = 1160129) B1160129
theorem B8801581 : Blo 686314 8801581 := bstep (se 3 (by rfl) ⟨1650296, by rfl⟩ : syracuseStep 8801581 = 3300593) B3300593
theorem B7851329 : Blo 686314 7851329 := bstep (se 2 (by rfl) ⟨2944248, by rfl⟩ : syracuseStep 7851329 = 5888497) B5888497
theorem B773527 : Blo 686314 773527 := bstep (se 1 (by rfl) ⟨580145, by rfl⟩ : syracuseStep 773527 = 1160291) B1160291
theorem B2117081 : Blo 686314 2117081 := bstep (se 2 (by rfl) ⟨793905, by rfl⟩ : syracuseStep 2117081 = 1587811) B1587811
theorem B8474147 : Blo 686314 8474147 := bstep (se 1 (by rfl) ⟨6355610, by rfl⟩ : syracuseStep 8474147 = 12711221) B12711221
theorem B773707 : Blo 686314 773707 := bstep (se 1 (by rfl) ⟨580280, by rfl⟩ : syracuseStep 773707 = 1160561) B1160561
theorem B773815 : Blo 686314 773815 := bstep (se 1 (by rfl) ⟨580361, by rfl⟩ : syracuseStep 773815 = 1160723) B1160723
theorem B4411097 : Blo 686314 4411097 := bstep (se 2 (by rfl) ⟨1654161, by rfl⟩ : syracuseStep 4411097 = 3308323) B3308323
theorem B872203 : Blo 686314 872203 := bstep (se 1 (by rfl) ⟨654152, by rfl⟩ : syracuseStep 872203 = 1308305) B1308305
theorem B773995 : Blo 686314 773995 := bstep (se 1 (by rfl) ⟨580496, by rfl⟩ : syracuseStep 773995 = 1160993) B1160993
theorem B774103 : Blo 686314 774103 := bstep (se 1 (by rfl) ⟨580577, by rfl⟩ : syracuseStep 774103 = 1161155) B1161155
theorem B872471 : Blo 686314 872471 := bstep (se 1 (by rfl) ⟨654353, by rfl⟩ : syracuseStep 872471 = 1308707) B1308707
theorem B774283 : Blo 686314 774283 := bstep (se 1 (by rfl) ⟨580712, by rfl⟩ : syracuseStep 774283 = 1161425) B1161425
theorem B2937005 : Blo 686314 2937005 := bstep (se 3 (by rfl) ⟨550688, by rfl⟩ : syracuseStep 2937005 = 1101377) B1101377
theorem B774391 : Blo 686314 774391 := bstep (se 1 (by rfl) ⟨580793, by rfl⟩ : syracuseStep 774391 = 1161587) B1161587
theorem B6607109 : Blo 686314 6607109 := bstep (se 4 (by rfl) ⟨619416, by rfl⟩ : syracuseStep 6607109 = 1238833) B1238833
theorem B2871641 : Blo 686314 2871641 := bstep (se 2 (by rfl) ⟨1076865, by rfl⟩ : syracuseStep 2871641 = 2153731) B2153731
theorem B774571 : Blo 686314 774571 := bstep (se 1 (by rfl) ⟨580928, by rfl⟩ : syracuseStep 774571 = 1161857) B1161857
theorem B2937347 : Blo 686314 2937347 := bstep (se 1 (by rfl) ⟨2203010, by rfl⟩ : syracuseStep 2937347 = 4406021) B4406021
theorem B6279697 : Blo 686314 6279697 := bstep (se 2 (by rfl) ⟨2354886, by rfl⟩ : syracuseStep 6279697 = 4709773) B4709773
theorem B774679 : Blo 686314 774679 := bstep (se 1 (by rfl) ⟨581009, by rfl⟩ : syracuseStep 774679 = 1162019) B1162019
theorem B2609729 : Blo 686314 2609729 := bstep (se 2 (by rfl) ⟨978648, by rfl⟩ : syracuseStep 2609729 = 1957297) B1957297
theorem B774859 : Blo 686314 774859 := bstep (se 1 (by rfl) ⟨581144, by rfl⟩ : syracuseStep 774859 = 1162289) B1162289
theorem B873175 : Blo 686314 873175 := bstep (se 1 (by rfl) ⟨654881, by rfl⟩ : syracuseStep 873175 = 1309763) B1309763
theorem B774967 : Blo 686314 774967 := bstep (se 1 (by rfl) ⟨581225, by rfl⟩ : syracuseStep 774967 = 1162451) B1162451
theorem B775147 : Blo 686314 775147 := bstep (se 1 (by rfl) ⟨581360, by rfl⟩ : syracuseStep 775147 = 1162721) B1162721
theorem B775255 : Blo 686314 775255 := bstep (se 1 (by rfl) ⟨581441, by rfl⟩ : syracuseStep 775255 = 1162883) B1162883
theorem B775435 : Blo 686314 775435 := bstep (se 1 (by rfl) ⟨581576, by rfl⟩ : syracuseStep 775435 = 1163153) B1163153
theorem B1725761 : Blo 686314 1725761 := bstep (se 2 (by rfl) ⟨647160, by rfl⟩ : syracuseStep 1725761 = 1294321) B1294321
theorem B775543 : Blo 686314 775543 := bstep (se 1 (by rfl) ⟨581657, by rfl⟩ : syracuseStep 775543 = 1163315) B1163315
theorem B4183447 : Blo 686314 4183447 := bstep (se 1 (by rfl) ⟨3137585, by rfl⟩ : syracuseStep 4183447 = 6275171) B6275171
theorem B775723 : Blo 686314 775723 := bstep (se 1 (by rfl) ⟨581792, by rfl⟩ : syracuseStep 775723 = 1163585) B1163585
theorem B3921473 : Blo 686314 3921473 := bstep (se 2 (by rfl) ⟨1470552, by rfl⟩ : syracuseStep 3921473 = 2941105) B2941105
theorem B1398359 : Blo 686314 1398359 := bstep (se 1 (by rfl) ⟨1048769, by rfl⟩ : syracuseStep 1398359 = 2097539) B2097539
theorem B775831 : Blo 686314 775831 := bstep (se 1 (by rfl) ⟨581873, by rfl⟩ : syracuseStep 775831 = 1163747) B1163747
theorem B1103627 : Blo 686314 1103627 := bstep (se 1 (by rfl) ⟨827720, by rfl⟩ : syracuseStep 1103627 = 1655441) B1655441
theorem B776011 : Blo 686314 776011 := bstep (se 1 (by rfl) ⟨582008, by rfl⟩ : syracuseStep 776011 = 1164017) B1164017
theorem B2480003 : Blo 686314 2480003 := bstep (se 1 (by rfl) ⟨1860002, by rfl⟩ : syracuseStep 2480003 = 3720005) B3720005
theorem B776119 : Blo 686314 776119 := bstep (se 1 (by rfl) ⟨582089, by rfl⟩ : syracuseStep 776119 = 1164179) B1164179
theorem B8378329 : Blo 686314 8378329 := bstep (se 2 (by rfl) ⟨3141873, by rfl⟩ : syracuseStep 8378329 = 6283747) B6283747
theorem B2611217 : Blo 686314 2611217 := bstep (se 2 (by rfl) ⟨979206, by rfl⟩ : syracuseStep 2611217 = 1958413) B1958413
theorem B776299 : Blo 686314 776299 := bstep (se 1 (by rfl) ⟨582224, by rfl⟩ : syracuseStep 776299 = 1164449) B1164449
theorem B2480321 : Blo 686314 2480321 := bstep (se 2 (by rfl) ⟨930120, by rfl⟩ : syracuseStep 2480321 = 1860241) B1860241
theorem B2316491 : Blo 686314 2316491 := bstep (se 1 (by rfl) ⟨1737368, by rfl⟩ : syracuseStep 2316491 = 3474737) B3474737
theorem B776407 : Blo 686314 776407 := bstep (se 1 (by rfl) ⟨582305, by rfl⟩ : syracuseStep 776407 = 1164611) B1164611
theorem B1104139 : Blo 686314 1104139 := bstep (se 1 (by rfl) ⟨828104, by rfl⟩ : syracuseStep 1104139 = 1656209) B1656209
theorem B2480435 : Blo 686314 2480435 := bstep (se 1 (by rfl) ⟨1860326, by rfl⟩ : syracuseStep 2480435 = 3720653) B3720653
theorem B4413761 : Blo 686314 4413761 := bstep (se 2 (by rfl) ⟨1655160, by rfl⟩ : syracuseStep 4413761 = 3310321) B3310321
theorem B776587 : Blo 686314 776587 := bstep (se 1 (by rfl) ⟨582440, by rfl⟩ : syracuseStep 776587 = 1164881) B1164881
theorem B2316761 : Blo 686314 2316761 := bstep (se 2 (by rfl) ⟨868785, by rfl⟩ : syracuseStep 2316761 = 1737571) B1737571
theorem B2611673 : Blo 686314 2611673 := bstep (se 2 (by rfl) ⟨979377, by rfl⟩ : syracuseStep 2611673 = 1958755) B1958755
theorem B2611885 : Blo 686314 2611885 := bstep (se 3 (by rfl) ⟨489728, by rfl⟩ : syracuseStep 2611885 = 979457) B979457
theorem B12114613 : Blo 686314 12114613 := bstep (se 5 (by rfl) ⟨567872, by rfl⟩ : syracuseStep 12114613 = 1135745) B1135745
theorem B1956545 : Blo 686314 1956545 := bstep (se 2 (by rfl) ⟨733704, by rfl⟩ : syracuseStep 1956545 = 1467409) B1467409
theorem B3726125 : Blo 686314 3726125 := bstep (se 3 (by rfl) ⟨698648, by rfl⟩ : syracuseStep 3726125 = 1397297) B1397297
theorem B2939723 : Blo 686314 2939723 := bstep (se 1 (by rfl) ⟨2204792, by rfl⟩ : syracuseStep 2939723 = 4409585) B4409585
theorem B2087831 : Blo 686314 2087831 := bstep (se 1 (by rfl) ⟨1565873, by rfl⟩ : syracuseStep 2087831 = 3131747) B3131747
theorem B1104857 : Blo 686314 1104857 := bstep (se 2 (by rfl) ⟨414321, by rfl⟩ : syracuseStep 1104857 = 828643) B828643
theorem B2612189 : Blo 686314 2612189 := bstep (se 3 (by rfl) ⟨489785, by rfl⟩ : syracuseStep 2612189 = 979571) B979571
theorem B2317463 : Blo 686314 2317463 := bstep (se 1 (by rfl) ⟨1738097, by rfl⟩ : syracuseStep 2317463 = 3476195) B3476195
theorem B11164877 : Blo 686314 11164877 := bstep (se 3 (by rfl) ⟨2093414, by rfl⟩ : syracuseStep 11164877 = 4186829) B4186829
theorem B1957081 : Blo 686314 1957081 := bstep (se 2 (by rfl) ⟨733905, by rfl⟩ : syracuseStep 1957081 = 1467811) B1467811
theorem B12541229 : Blo 686314 12541229 := bstep (se 3 (by rfl) ⟨2351480, by rfl⟩ : syracuseStep 12541229 = 4702961) B4702961
theorem B2318003 : Blo 686314 2318003 := bstep (se 1 (by rfl) ⟨1738502, by rfl⟩ : syracuseStep 2318003 = 3477005) B3477005
theorem B2940695 : Blo 686314 2940695 := bstep (se 1 (by rfl) ⟨2205521, by rfl⟩ : syracuseStep 2940695 = 4411043) B4411043
theorem B2318273 : Blo 686314 2318273 := bstep (se 2 (by rfl) ⟨869352, by rfl⟩ : syracuseStep 2318273 = 1738705) B1738705
theorem B4186073 : Blo 686314 4186073 := bstep (se 2 (by rfl) ⟨1569777, by rfl⟩ : syracuseStep 4186073 = 3139555) B3139555
theorem B5234705 : Blo 686314 5234705 := bstep (se 2 (by rfl) ⟨1963014, by rfl⟩ : syracuseStep 5234705 = 3926029) B3926029
theorem B5890481 : Blo 686314 5890481 := bstep (se 2 (by rfl) ⟨2208930, by rfl⟩ : syracuseStep 5890481 = 4417861) B4417861
theorem B2318813 : Blo 686314 2318813 := bstep (se 3 (by rfl) ⟨434777, by rfl⟩ : syracuseStep 2318813 = 869555) B869555
theorem B746219 : Blo 686314 746219 := bstep (se 1 (by rfl) ⟨559664, by rfl⟩ : syracuseStep 746219 = 1119329) B1119329
theorem B1303361 : Blo 686314 1303361 := bstep (se 2 (by rfl) ⟨488760, by rfl⟩ : syracuseStep 1303361 = 977521) B977521
theorem B8479667 : Blo 686314 8479667 := bstep (se 1 (by rfl) ⟨6359750, by rfl⟩ : syracuseStep 8479667 = 12719501) B12719501
theorem B1467443 : Blo 686314 1467443 := bstep (se 1 (by rfl) ⟨1100582, by rfl⟩ : syracuseStep 1467443 = 2201165) B2201165
theorem B1303627 : Blo 686314 1303627 := bstep (se 1 (by rfl) ⟨977720, by rfl⟩ : syracuseStep 1303627 = 1955441) B1955441
theorem B1959005 : Blo 686314 1959005 := bstep (se 3 (by rfl) ⟨367313, by rfl⟩ : syracuseStep 1959005 = 734627) B734627
theorem B5301425 : Blo 686314 5301425 := bstep (se 2 (by rfl) ⟨1988034, by rfl⟩ : syracuseStep 5301425 = 3976069) B3976069
theorem B8381875 : Blo 686314 8381875 := bstep (se 1 (by rfl) ⟨6286406, by rfl⟩ : syracuseStep 8381875 = 12572813) B12572813
theorem B2483635 : Blo 686314 2483635 := bstep (se 1 (by rfl) ⟨1862726, by rfl⟩ : syracuseStep 2483635 = 3725453) B3725453
theorem B2614787 : Blo 686314 2614787 := bstep (se 1 (by rfl) ⟨1961090, by rfl⟩ : syracuseStep 2614787 = 3922181) B3922181
theorem B1304075 : Blo 686314 1304075 := bstep (se 1 (by rfl) ⟨978056, by rfl⟩ : syracuseStep 1304075 = 1956113) B1956113
theorem B2614801 : Blo 686314 2614801 := bstep (se 2 (by rfl) ⟨980550, by rfl⟩ : syracuseStep 2614801 = 1961101) B1961101
theorem B2319947 : Blo 686314 2319947 := bstep (se 1 (by rfl) ⟨1739960, by rfl⟩ : syracuseStep 2319947 = 3479921) B3479921
theorem B1304257 : Blo 686314 1304257 := bstep (se 2 (by rfl) ⟨489096, by rfl⟩ : syracuseStep 1304257 = 978193) B978193
theorem B2615105 : Blo 686314 2615105 := bstep (se 2 (by rfl) ⟨980664, by rfl⟩ : syracuseStep 2615105 = 1961329) B1961329
theorem B2320217 : Blo 686314 2320217 := bstep (se 2 (by rfl) ⟨870081, by rfl⟩ : syracuseStep 2320217 = 1740163) B1740163
theorem B1304599 : Blo 686314 1304599 := bstep (se 1 (by rfl) ⟨978449, by rfl⟩ : syracuseStep 1304599 = 1956899) B1956899
theorem B2943155 : Blo 686314 2943155 := bstep (se 1 (by rfl) ⟨2207366, by rfl⟩ : syracuseStep 2943155 = 4414733) B4414733
theorem B7432397 : Blo 686314 7432397 := bstep (se 3 (by rfl) ⟨1393574, by rfl⟩ : syracuseStep 7432397 = 2787149) B2787149
theorem B1468631 : Blo 686314 1468631 := bstep (se 1 (by rfl) ⟨1101473, by rfl⟩ : syracuseStep 1468631 = 2202947) B2202947
theorem B1304819 : Blo 686314 1304819 := bstep (se 1 (by rfl) ⟨978614, by rfl⟩ : syracuseStep 1304819 = 1957229) B1957229
theorem B4188509 : Blo 686314 4188509 := bstep (se 3 (by rfl) ⟨785345, by rfl⟩ : syracuseStep 4188509 = 1570691) B1570691
theorem B1305047 : Blo 686314 1305047 := bstep (se 1 (by rfl) ⟨978785, by rfl⟩ : syracuseStep 1305047 = 1957571) B1957571
theorem B2615773 : Blo 686314 2615773 := bstep (se 3 (by rfl) ⟨490457, by rfl⟩ : syracuseStep 2615773 = 980915) B980915
theorem B1239563 : Blo 686314 1239563 := bstep (se 1 (by rfl) ⟨929672, by rfl⟩ : syracuseStep 1239563 = 1859345) B1859345
theorem B2320919 : Blo 686314 2320919 := bstep (se 1 (by rfl) ⟨1740689, by rfl⟩ : syracuseStep 2320919 = 3481379) B3481379
theorem B1305305 : Blo 686314 1305305 := bstep (se 2 (by rfl) ⟨489489, by rfl⟩ : syracuseStep 1305305 = 978979) B978979
theorem B1764275 : Blo 686314 1764275 := bstep (se 1 (by rfl) ⟨1323206, by rfl⟩ : syracuseStep 1764275 = 2646413) B2646413
theorem B2321459 : Blo 686314 2321459 := bstep (se 1 (by rfl) ⟨1741094, by rfl⟩ : syracuseStep 2321459 = 3482189) B3482189
theorem B1305715 : Blo 686314 1305715 := bstep (se 1 (by rfl) ⟨979286, by rfl⟩ : syracuseStep 1305715 = 1958573) B1958573
theorem B1469657 : Blo 686314 1469657 := bstep (se 2 (by rfl) ⟨551121, by rfl⟩ : syracuseStep 1469657 = 1102243) B1102243
theorem B2321729 : Blo 686314 2321729 := bstep (se 2 (by rfl) ⟨870648, by rfl⟩ : syracuseStep 2321729 = 1741297) B1741297
theorem B1306201 : Blo 686314 1306201 := bstep (se 2 (by rfl) ⟨489825, by rfl⟩ : syracuseStep 1306201 = 979651) B979651
theorem B3305053 : Blo 686314 3305053 := bstep (se 3 (by rfl) ⟨619697, by rfl⟩ : syracuseStep 3305053 = 1239395) B1239395
theorem B2092637 : Blo 686314 2092637 := bstep (se 3 (by rfl) ⟨392369, by rfl⟩ : syracuseStep 2092637 = 784739) B784739
theorem B2649773 : Blo 686314 2649773 := bstep (se 3 (by rfl) ⟨496832, by rfl⟩ : syracuseStep 2649773 = 993665) B993665
theorem B2617049 : Blo 686314 2617049 := bstep (se 2 (by rfl) ⟨981393, by rfl⟩ : syracuseStep 2617049 = 1962787) B1962787
theorem B5238593 : Blo 686314 5238593 := bstep (se 2 (by rfl) ⟨1964472, by rfl⟩ : syracuseStep 5238593 = 3928945) B3928945
theorem B2322269 : Blo 686314 2322269 := bstep (se 3 (by rfl) ⟨435425, by rfl⟩ : syracuseStep 2322269 = 870851) B870851
theorem B11726693 : Blo 686314 11726693 := bstep (se 4 (by rfl) ⟨1099377, by rfl⟩ : syracuseStep 11726693 = 2198755) B2198755
theorem B1961921 : Blo 686314 1961921 := bstep (se 2 (by rfl) ⟨735720, by rfl⟩ : syracuseStep 1961921 = 1471441) B1471441
theorem B1044427 : Blo 686314 1044427 := bstep (se 1 (by rfl) ⟨783320, by rfl⟩ : syracuseStep 1044427 = 1566641) B1566641
theorem B978905 : Blo 686314 978905 := bstep (se 2 (by rfl) ⟨367089, by rfl⟩ : syracuseStep 978905 = 734179) B734179
theorem B1961945 : Blo 686314 1961945 := bstep (se 2 (by rfl) ⟨735729, by rfl⟩ : syracuseStep 1961945 = 1471459) B1471459
theorem B2945069 : Blo 686314 2945069 := bstep (se 3 (by rfl) ⟨552200, by rfl⟩ : syracuseStep 2945069 = 1104401) B1104401
theorem B1306763 : Blo 686314 1306763 := bstep (se 1 (by rfl) ⟨980072, by rfl⟩ : syracuseStep 1306763 = 1960145) B1960145
theorem B11137175 : Blo 686314 11137175 := bstep (se 1 (by rfl) ⟨8352881, by rfl⟩ : syracuseStep 11137175 = 16705763) B16705763
theorem B5566643 : Blo 686314 5566643 := bstep (se 1 (by rfl) ⟨4174982, by rfl⟩ : syracuseStep 5566643 = 8349965) B8349965
theorem B1470707 : Blo 686314 1470707 := bstep (se 1 (by rfl) ⟨1103030, by rfl⟩ : syracuseStep 1470707 = 2206061) B2206061
theorem B1306945 : Blo 686314 1306945 := bstep (se 2 (by rfl) ⟨490104, by rfl⟩ : syracuseStep 1306945 = 980209) B980209
theorem B11891123 : Blo 686314 11891123 := bstep (se 1 (by rfl) ⟨8918342, by rfl⟩ : syracuseStep 11891123 = 17836685) B17836685
theorem B979543 : Blo 686314 979543 := bstep (se 1 (by rfl) ⟨734657, by rfl⟩ : syracuseStep 979543 = 1469315) B1469315
theorem B2945753 : Blo 686314 2945753 := bstep (se 2 (by rfl) ⟨1104657, by rfl⟩ : syracuseStep 2945753 = 2209315) B2209315
theorem B1471297 : Blo 686314 1471297 := bstep (se 2 (by rfl) ⟨551736, by rfl⟩ : syracuseStep 1471297 = 1103473) B1103473
theorem B2323403 : Blo 686314 2323403 := bstep (se 1 (by rfl) ⟨1742552, by rfl⟩ : syracuseStep 2323403 = 3485105) B3485105
theorem B1307659 : Blo 686314 1307659 := bstep (se 1 (by rfl) ⟨980744, by rfl⟩ : syracuseStep 1307659 = 1961489) B1961489
theorem B50328611 : Blo 686314 50328611 := bstep (se 1 (by rfl) ⟨37746458, by rfl⟩ : syracuseStep 50328611 = 75492917) B75492917
theorem B1242163 : Blo 686314 1242163 := bstep (se 1 (by rfl) ⟨931622, by rfl⟩ : syracuseStep 1242163 = 1863245) B1863245
theorem B1307735 : Blo 686314 1307735 := bstep (se 1 (by rfl) ⟨980801, by rfl⟩ : syracuseStep 1307735 = 1961603) B1961603
theorem B3929219 : Blo 686314 3929219 := bstep (se 1 (by rfl) ⟨2946914, by rfl⟩ : syracuseStep 3929219 = 5893829) B5893829
theorem B1963187 : Blo 686314 1963187 := bstep (se 1 (by rfl) ⟨1472390, by rfl⟩ : syracuseStep 1963187 = 2944781) B2944781
theorem B2323673 : Blo 686314 2323673 := bstep (se 2 (by rfl) ⟨871377, by rfl⟩ : syracuseStep 2323673 = 1742755) B1742755
theorem B2618675 : Blo 686314 2618675 := bstep (se 1 (by rfl) ⟨1964006, by rfl⟩ : syracuseStep 2618675 = 3928013) B3928013
theorem B2618689 : Blo 686314 2618689 := bstep (se 2 (by rfl) ⟨982008, by rfl⟩ : syracuseStep 2618689 = 1964017) B1964017
theorem B980363 : Blo 686314 980363 := bstep (se 1 (by rfl) ⟨735272, by rfl⟩ : syracuseStep 980363 = 1470545) B1470545
theorem B2487773 : Blo 686314 2487773 := bstep (se 3 (by rfl) ⟨466457, by rfl⟩ : syracuseStep 2487773 = 932915) B932915
theorem B2651741 : Blo 686314 2651741 := bstep (se 3 (by rfl) ⟨497201, by rfl⟩ : syracuseStep 2651741 = 994403) B994403
theorem B2487901 : Blo 686314 2487901 := bstep (se 3 (by rfl) ⟨466481, by rfl⟩ : syracuseStep 2487901 = 932963) B932963
theorem B5240537 : Blo 686314 5240537 := bstep (se 2 (by rfl) ⟨1965201, by rfl⟩ : syracuseStep 5240537 = 3930403) B3930403
theorem B1308403 : Blo 686314 1308403 := bstep (se 1 (by rfl) ⟨981302, by rfl⟩ : syracuseStep 1308403 = 1962605) B1962605
theorem B2946881 : Blo 686314 2946881 := bstep (se 2 (by rfl) ⟨1105080, by rfl⟩ : syracuseStep 2946881 = 2210161) B2210161
theorem B2324375 : Blo 686314 2324375 := bstep (se 1 (by rfl) ⟨1743281, by rfl⟩ : syracuseStep 2324375 = 3486563) B3486563
theorem B1308631 : Blo 686314 1308631 := bstep (se 1 (by rfl) ⟨981473, by rfl⟩ : syracuseStep 1308631 = 1962947) B1962947
theorem B1308737 : Blo 686314 1308737 := bstep (se 2 (by rfl) ⟨490776, by rfl⟩ : syracuseStep 1308737 = 981553) B981553
theorem B11303063 : Blo 686314 11303063 := bstep (se 1 (by rfl) ⟨8477297, by rfl⟩ : syracuseStep 11303063 = 16954595) B16954595
theorem B22313141 : Blo 686314 22313141 := bstep (se 5 (by rfl) ⟨1045928, by rfl⟩ : syracuseStep 22313141 = 2091857) B2091857
theorem B1308889 : Blo 686314 1308889 := bstep (se 2 (by rfl) ⟨490833, by rfl⟩ : syracuseStep 1308889 = 981667) B981667
theorem B686315 : Blo 686314 686315 := bstep (se 1 (by rfl) ⟨514736, by rfl⟩ : syracuseStep 686315 = 1029473) B1029473
theorem B686327 : Blo 686314 686327 := bstep (se 1 (by rfl) ⟨514745, by rfl⟩ : syracuseStep 686327 = 1029491) B1029491
theorem B686347 : Blo 686314 686347 := bstep (se 1 (by rfl) ⟨514760, by rfl⟩ : syracuseStep 686347 = 1029521) B1029521
theorem B686359 : Blo 686314 686359 := bstep (se 1 (by rfl) ⟨514769, by rfl⟩ : syracuseStep 686359 = 1029539) B1029539
theorem B686379 : Blo 686314 686379 := bstep (se 1 (by rfl) ⟨514784, by rfl⟩ : syracuseStep 686379 = 1029569) B1029569
theorem B686391 : Blo 686314 686391 := bstep (se 1 (by rfl) ⟨514793, by rfl⟩ : syracuseStep 686391 = 1029587) B1029587
theorem B686411 : Blo 686314 686411 := bstep (se 1 (by rfl) ⟨514808, by rfl⟩ : syracuseStep 686411 = 1029617) B1029617
theorem B1472843 : Blo 686314 1472843 := bstep (se 1 (by rfl) ⟨1104632, by rfl⟩ : syracuseStep 1472843 = 2209265) B2209265
theorem B686423 : Blo 686314 686423 := bstep (se 1 (by rfl) ⟨514817, by rfl⟩ : syracuseStep 686423 = 1029635) B1029635
theorem B981337 : Blo 686314 981337 := bstep (se 2 (by rfl) ⟨368001, by rfl⟩ : syracuseStep 981337 = 736003) B736003
theorem B686443 : Blo 686314 686443 := bstep (se 1 (by rfl) ⟨514832, by rfl⟩ : syracuseStep 686443 = 1029665) B1029665
theorem B686455 : Blo 686314 686455 := bstep (se 1 (by rfl) ⟨514841, by rfl⟩ : syracuseStep 686455 = 1029683) B1029683
theorem B686475 : Blo 686314 686475 := bstep (se 1 (by rfl) ⟨514856, by rfl⟩ : syracuseStep 686475 = 1029713) B1029713
theorem B686487 : Blo 686314 686487 := bstep (se 1 (by rfl) ⟨514865, by rfl⟩ : syracuseStep 686487 = 1029731) B1029731
theorem B686507 : Blo 686314 686507 := bstep (se 1 (by rfl) ⟨514880, by rfl⟩ : syracuseStep 686507 = 1029761) B1029761
theorem B2324915 : Blo 686314 2324915 := bstep (se 1 (by rfl) ⟨1743686, by rfl⟩ : syracuseStep 2324915 = 3487373) B3487373
theorem B686519 : Blo 686314 686519 := bstep (se 1 (by rfl) ⟨514889, by rfl⟩ : syracuseStep 686519 = 1029779) B1029779
theorem B686539 : Blo 686314 686539 := bstep (se 1 (by rfl) ⟨514904, by rfl⟩ : syracuseStep 686539 = 1029809) B1029809
theorem B686551 : Blo 686314 686551 := bstep (se 1 (by rfl) ⟨514913, by rfl⟩ : syracuseStep 686551 = 1029827) B1029827
theorem B686571 : Blo 686314 686571 := bstep (se 1 (by rfl) ⟨514928, by rfl⟩ : syracuseStep 686571 = 1029857) B1029857
theorem B686583 : Blo 686314 686583 := bstep (se 1 (by rfl) ⟨514937, by rfl⟩ : syracuseStep 686583 = 1029875) B1029875
theorem B686603 : Blo 686314 686603 := bstep (se 1 (by rfl) ⟨514952, by rfl⟩ : syracuseStep 686603 = 1029905) B1029905
theorem B686615 : Blo 686314 686615 := bstep (se 1 (by rfl) ⟨514961, by rfl⟩ : syracuseStep 686615 = 1029923) B1029923
theorem B686635 : Blo 686314 686635 := bstep (se 1 (by rfl) ⟨514976, by rfl⟩ : syracuseStep 686635 = 1029953) B1029953
theorem B686647 : Blo 686314 686647 := bstep (se 1 (by rfl) ⟨514985, by rfl⟩ : syracuseStep 686647 = 1029971) B1029971
theorem B686667 : Blo 686314 686667 := bstep (se 1 (by rfl) ⟨515000, by rfl⟩ : syracuseStep 686667 = 1030001) B1030001
theorem B686679 : Blo 686314 686679 := bstep (se 1 (by rfl) ⟨515009, by rfl⟩ : syracuseStep 686679 = 1030019) B1030019
theorem B7436893 : Blo 686314 7436893 := bstep (se 3 (by rfl) ⟨1394417, by rfl⟩ : syracuseStep 7436893 = 2788835) B2788835
theorem B686699 : Blo 686314 686699 := bstep (se 1 (by rfl) ⟨515024, by rfl⟩ : syracuseStep 686699 = 1030049) B1030049
theorem B686711 : Blo 686314 686711 := bstep (se 1 (by rfl) ⟨515033, by rfl⟩ : syracuseStep 686711 = 1030067) B1030067
theorem B686731 : Blo 686314 686731 := bstep (se 1 (by rfl) ⟨515048, by rfl⟩ : syracuseStep 686731 = 1030097) B1030097
theorem B686743 : Blo 686314 686743 := bstep (se 1 (by rfl) ⟨515057, by rfl⟩ : syracuseStep 686743 = 1030115) B1030115
theorem B686763 : Blo 686314 686763 := bstep (se 1 (by rfl) ⟨515072, by rfl⟩ : syracuseStep 686763 = 1030145) B1030145
theorem B686775 : Blo 686314 686775 := bstep (se 1 (by rfl) ⟨515081, by rfl⟩ : syracuseStep 686775 = 1030163) B1030163
theorem B2325185 : Blo 686314 2325185 := bstep (se 2 (by rfl) ⟨871944, by rfl⟩ : syracuseStep 2325185 = 1743889) B1743889
theorem B686795 : Blo 686314 686795 := bstep (se 1 (by rfl) ⟨515096, by rfl⟩ : syracuseStep 686795 = 1030193) B1030193
theorem B686807 : Blo 686314 686807 := bstep (se 1 (by rfl) ⟨515105, by rfl⟩ : syracuseStep 686807 = 1030211) B1030211
theorem B2357981 : Blo 686314 2357981 := bstep (se 3 (by rfl) ⟨442121, by rfl⟩ : syracuseStep 2357981 = 884243) B884243
theorem B686827 : Blo 686314 686827 := bstep (se 1 (by rfl) ⟨515120, by rfl⟩ : syracuseStep 686827 = 1030241) B1030241
theorem B686839 : Blo 686314 686839 := bstep (se 1 (by rfl) ⟨515129, by rfl⟩ : syracuseStep 686839 = 1030259) B1030259
theorem B686859 : Blo 686314 686859 := bstep (se 1 (by rfl) ⟨515144, by rfl⟩ : syracuseStep 686859 = 1030289) B1030289
theorem B686871 : Blo 686314 686871 := bstep (se 1 (by rfl) ⟨515153, by rfl⟩ : syracuseStep 686871 = 1030307) B1030307
theorem B686891 : Blo 686314 686891 := bstep (se 1 (by rfl) ⟨515168, by rfl⟩ : syracuseStep 686891 = 1030337) B1030337
theorem B5864237 : Blo 686314 5864237 := bstep (se 3 (by rfl) ⟨1099544, by rfl⟩ : syracuseStep 5864237 = 2199089) B2199089
theorem B686903 : Blo 686314 686903 := bstep (se 1 (by rfl) ⟨515177, by rfl⟩ : syracuseStep 686903 = 1030355) B1030355
theorem B686923 : Blo 686314 686923 := bstep (se 1 (by rfl) ⟨515192, by rfl⟩ : syracuseStep 686923 = 1030385) B1030385
theorem B686935 : Blo 686314 686935 := bstep (se 1 (by rfl) ⟨515201, by rfl⟩ : syracuseStep 686935 = 1030403) B1030403
theorem B686955 : Blo 686314 686955 := bstep (se 1 (by rfl) ⟨515216, by rfl⟩ : syracuseStep 686955 = 1030433) B1030433
theorem B686967 : Blo 686314 686967 := bstep (se 1 (by rfl) ⟨515225, by rfl⟩ : syracuseStep 686967 = 1030451) B1030451
theorem B686987 : Blo 686314 686987 := bstep (se 1 (by rfl) ⟨515240, by rfl⟩ : syracuseStep 686987 = 1030481) B1030481
theorem B686999 : Blo 686314 686999 := bstep (se 1 (by rfl) ⟨515249, by rfl⟩ : syracuseStep 686999 = 1030499) B1030499
theorem B687019 : Blo 686314 687019 := bstep (se 1 (by rfl) ⟨515264, by rfl⟩ : syracuseStep 687019 = 1030529) B1030529
theorem B687031 : Blo 686314 687031 := bstep (se 1 (by rfl) ⟨515273, by rfl⟩ : syracuseStep 687031 = 1030547) B1030547
theorem B687051 : Blo 686314 687051 := bstep (se 1 (by rfl) ⟨515288, by rfl⟩ : syracuseStep 687051 = 1030577) B1030577
theorem B687063 : Blo 686314 687063 := bstep (se 1 (by rfl) ⟨515297, by rfl⟩ : syracuseStep 687063 = 1030595) B1030595
theorem B687083 : Blo 686314 687083 := bstep (se 1 (by rfl) ⟨515312, by rfl⟩ : syracuseStep 687083 = 1030625) B1030625
theorem B687095 : Blo 686314 687095 := bstep (se 1 (by rfl) ⟨515321, by rfl⟩ : syracuseStep 687095 = 1030643) B1030643
theorem B687115 : Blo 686314 687115 := bstep (se 1 (by rfl) ⟨515336, by rfl⟩ : syracuseStep 687115 = 1030673) B1030673
theorem B687127 : Blo 686314 687127 := bstep (se 1 (by rfl) ⟨515345, by rfl⟩ : syracuseStep 687127 = 1030691) B1030691
theorem B687147 : Blo 686314 687147 := bstep (se 1 (by rfl) ⟨515360, by rfl⟩ : syracuseStep 687147 = 1030721) B1030721
theorem B687159 : Blo 686314 687159 := bstep (se 1 (by rfl) ⟨515369, by rfl⟩ : syracuseStep 687159 = 1030739) B1030739
theorem B2653249 : Blo 686314 2653249 := bstep (se 2 (by rfl) ⟨994968, by rfl⟩ : syracuseStep 2653249 = 1989937) B1989937
theorem B687179 : Blo 686314 687179 := bstep (se 1 (by rfl) ⟨515384, by rfl⟩ : syracuseStep 687179 = 1030769) B1030769
theorem B687191 : Blo 686314 687191 := bstep (se 1 (by rfl) ⟨515393, by rfl⟩ : syracuseStep 687191 = 1030787) B1030787
theorem B687211 : Blo 686314 687211 := bstep (se 1 (by rfl) ⟨515408, by rfl⟩ : syracuseStep 687211 = 1030817) B1030817
theorem B687223 : Blo 686314 687223 := bstep (se 1 (by rfl) ⟨515417, by rfl⟩ : syracuseStep 687223 = 1030835) B1030835
theorem B687243 : Blo 686314 687243 := bstep (se 1 (by rfl) ⟨515432, by rfl⟩ : syracuseStep 687243 = 1030865) B1030865
theorem B687255 : Blo 686314 687255 := bstep (se 1 (by rfl) ⟨515441, by rfl⟩ : syracuseStep 687255 = 1030883) B1030883
theorem B1473689 : Blo 686314 1473689 := bstep (se 2 (by rfl) ⟨552633, by rfl⟩ : syracuseStep 1473689 = 1105267) B1105267
theorem B687275 : Blo 686314 687275 := bstep (se 1 (by rfl) ⟨515456, by rfl⟩ : syracuseStep 687275 = 1030913) B1030913
theorem B687287 : Blo 686314 687287 := bstep (se 1 (by rfl) ⟨515465, by rfl⟩ : syracuseStep 687287 = 1030931) B1030931
theorem B687307 : Blo 686314 687307 := bstep (se 1 (by rfl) ⟨515480, by rfl⟩ : syracuseStep 687307 = 1030961) B1030961
theorem B2620619 : Blo 686314 2620619 := bstep (se 1 (by rfl) ⟨1965464, by rfl⟩ : syracuseStep 2620619 = 3930929) B3930929
theorem B687319 : Blo 686314 687319 := bstep (se 1 (by rfl) ⟨515489, by rfl⟩ : syracuseStep 687319 = 1030979) B1030979
theorem B2784473 : Blo 686314 2784473 := bstep (se 2 (by rfl) ⟨1044177, by rfl⟩ : syracuseStep 2784473 = 2088355) B2088355
theorem B2620633 : Blo 686314 2620633 := bstep (se 2 (by rfl) ⟨982737, by rfl⟩ : syracuseStep 2620633 = 1965475) B1965475
theorem B2325725 : Blo 686314 2325725 := bstep (se 3 (by rfl) ⟨436073, by rfl⟩ : syracuseStep 2325725 = 872147) B872147
theorem B687339 : Blo 686314 687339 := bstep (se 1 (by rfl) ⟨515504, by rfl⟩ : syracuseStep 687339 = 1031009) B1031009
theorem B687351 : Blo 686314 687351 := bstep (se 1 (by rfl) ⟨515513, by rfl⟩ : syracuseStep 687351 = 1031027) B1031027
theorem B687371 : Blo 686314 687371 := bstep (se 1 (by rfl) ⟨515528, by rfl⟩ : syracuseStep 687371 = 1031057) B1031057
theorem B687383 : Blo 686314 687383 := bstep (se 1 (by rfl) ⟨515537, by rfl⟩ : syracuseStep 687383 = 1031075) B1031075
theorem B687403 : Blo 686314 687403 := bstep (se 1 (by rfl) ⟨515552, by rfl⟩ : syracuseStep 687403 = 1031105) B1031105
theorem B687415 : Blo 686314 687415 := bstep (se 1 (by rfl) ⟨515561, by rfl⟩ : syracuseStep 687415 = 1031123) B1031123
theorem B687435 : Blo 686314 687435 := bstep (se 1 (by rfl) ⟨515576, by rfl⟩ : syracuseStep 687435 = 1031153) B1031153
theorem B687447 : Blo 686314 687447 := bstep (se 1 (by rfl) ⟨515585, by rfl⟩ : syracuseStep 687447 = 1031171) B1031171
theorem B687467 : Blo 686314 687467 := bstep (se 1 (by rfl) ⟨515600, by rfl⟩ : syracuseStep 687467 = 1031201) B1031201
theorem B687479 : Blo 686314 687479 := bstep (se 1 (by rfl) ⟨515609, by rfl⟩ : syracuseStep 687479 = 1031219) B1031219
theorem B687499 : Blo 686314 687499 := bstep (se 1 (by rfl) ⟨515624, by rfl⟩ : syracuseStep 687499 = 1031249) B1031249
theorem B687511 : Blo 686314 687511 := bstep (se 1 (by rfl) ⟨515633, by rfl⟩ : syracuseStep 687511 = 1031267) B1031267
theorem B687531 : Blo 686314 687531 := bstep (se 1 (by rfl) ⟨515648, by rfl⟩ : syracuseStep 687531 = 1031297) B1031297
theorem B687543 : Blo 686314 687543 := bstep (se 1 (by rfl) ⟨515657, by rfl⟩ : syracuseStep 687543 = 1031315) B1031315
theorem B687563 : Blo 686314 687563 := bstep (se 1 (by rfl) ⟨515672, by rfl⟩ : syracuseStep 687563 = 1031345) B1031345
theorem B2948555 : Blo 686314 2948555 := bstep (se 1 (by rfl) ⟨2211416, by rfl⟩ : syracuseStep 2948555 = 4422833) B4422833
theorem B687575 : Blo 686314 687575 := bstep (se 1 (by rfl) ⟨515681, by rfl⟩ : syracuseStep 687575 = 1031363) B1031363
theorem B982487 : Blo 686314 982487 := bstep (se 1 (by rfl) ⟨736865, by rfl⟩ : syracuseStep 982487 = 1473731) B1473731
theorem B687595 : Blo 686314 687595 := bstep (se 1 (by rfl) ⟨515696, by rfl⟩ : syracuseStep 687595 = 1031393) B1031393
theorem B1310195 : Blo 686314 1310195 := bstep (se 1 (by rfl) ⟨982646, by rfl⟩ : syracuseStep 1310195 = 1965293) B1965293
theorem B687607 : Blo 686314 687607 := bstep (se 1 (by rfl) ⟨515705, by rfl⟩ : syracuseStep 687607 = 1031411) B1031411
theorem B785911 : Blo 686314 785911 := bstep (se 1 (by rfl) ⟨589433, by rfl⟩ : syracuseStep 785911 = 1178867) B1178867
theorem B687627 : Blo 686314 687627 := bstep (se 1 (by rfl) ⟨515720, by rfl⟩ : syracuseStep 687627 = 1031441) B1031441
theorem B687639 : Blo 686314 687639 := bstep (se 1 (by rfl) ⟨515729, by rfl⟩ : syracuseStep 687639 = 1031459) B1031459
theorem B687659 : Blo 686314 687659 := bstep (se 1 (by rfl) ⟨515744, by rfl⟩ : syracuseStep 687659 = 1031489) B1031489
theorem B687671 : Blo 686314 687671 := bstep (se 1 (by rfl) ⟨515753, by rfl⟩ : syracuseStep 687671 = 1031507) B1031507
theorem B687691 : Blo 686314 687691 := bstep (se 1 (by rfl) ⟨515768, by rfl⟩ : syracuseStep 687691 = 1031537) B1031537
theorem B687703 : Blo 686314 687703 := bstep (se 1 (by rfl) ⟨515777, by rfl⟩ : syracuseStep 687703 = 1031555) B1031555
theorem B687723 : Blo 686314 687723 := bstep (se 1 (by rfl) ⟨515792, by rfl⟩ : syracuseStep 687723 = 1031585) B1031585
theorem B687735 : Blo 686314 687735 := bstep (se 1 (by rfl) ⟨515801, by rfl⟩ : syracuseStep 687735 = 1031603) B1031603
theorem B687755 : Blo 686314 687755 := bstep (se 1 (by rfl) ⟨515816, by rfl⟩ : syracuseStep 687755 = 1031633) B1031633
theorem B1310347 : Blo 686314 1310347 := bstep (se 1 (by rfl) ⟨982760, by rfl⟩ : syracuseStep 1310347 = 1965521) B1965521
theorem B687767 : Blo 686314 687767 := bstep (se 1 (by rfl) ⟨515825, by rfl⟩ : syracuseStep 687767 = 1031651) B1031651
theorem B687787 : Blo 686314 687787 := bstep (se 1 (by rfl) ⟨515840, by rfl⟩ : syracuseStep 687787 = 1031681) B1031681
theorem B687799 : Blo 686314 687799 := bstep (se 1 (by rfl) ⟨515849, by rfl⟩ : syracuseStep 687799 = 1031699) B1031699
theorem B687819 : Blo 686314 687819 := bstep (se 1 (by rfl) ⟨515864, by rfl⟩ : syracuseStep 687819 = 1031729) B1031729
theorem B687831 : Blo 686314 687831 := bstep (se 1 (by rfl) ⟨515873, by rfl⟩ : syracuseStep 687831 = 1031747) B1031747
theorem B687851 : Blo 686314 687851 := bstep (se 1 (by rfl) ⟨515888, by rfl⟩ : syracuseStep 687851 = 1031777) B1031777
theorem B687863 : Blo 686314 687863 := bstep (se 1 (by rfl) ⟨515897, by rfl⟩ : syracuseStep 687863 = 1031795) B1031795
theorem B687883 : Blo 686314 687883 := bstep (se 1 (by rfl) ⟨515912, by rfl⟩ : syracuseStep 687883 = 1031825) B1031825
theorem B982795 : Blo 686314 982795 := bstep (se 1 (by rfl) ⟨737096, by rfl⟩ : syracuseStep 982795 = 1474193) B1474193
theorem B687895 : Blo 686314 687895 := bstep (se 1 (by rfl) ⟨515921, by rfl⟩ : syracuseStep 687895 = 1031843) B1031843
theorem B687915 : Blo 686314 687915 := bstep (se 1 (by rfl) ⟨515936, by rfl⟩ : syracuseStep 687915 = 1031873) B1031873
theorem B687927 : Blo 686314 687927 := bstep (se 1 (by rfl) ⟨515945, by rfl⟩ : syracuseStep 687927 = 1031891) B1031891
theorem B687947 : Blo 686314 687947 := bstep (se 1 (by rfl) ⟨515960, by rfl⟩ : syracuseStep 687947 = 1031921) B1031921
theorem B687959 : Blo 686314 687959 := bstep (se 1 (by rfl) ⟨515969, by rfl⟩ : syracuseStep 687959 = 1031939) B1031939
theorem B1572697 : Blo 686314 1572697 := bstep (se 2 (by rfl) ⟨589761, by rfl⟩ : syracuseStep 1572697 = 1179523) B1179523
theorem B687979 : Blo 686314 687979 := bstep (se 1 (by rfl) ⟨515984, by rfl⟩ : syracuseStep 687979 = 1031969) B1031969
theorem B687991 : Blo 686314 687991 := bstep (se 1 (by rfl) ⟨515993, by rfl⟩ : syracuseStep 687991 = 1031987) B1031987
theorem B688011 : Blo 686314 688011 := bstep (se 1 (by rfl) ⟨516008, by rfl⟩ : syracuseStep 688011 = 1032017) B1032017
theorem B688023 : Blo 686314 688023 := bstep (se 1 (by rfl) ⟨516017, by rfl⟩ : syracuseStep 688023 = 1032035) B1032035
theorem B688043 : Blo 686314 688043 := bstep (se 1 (by rfl) ⟨516032, by rfl⟩ : syracuseStep 688043 = 1032065) B1032065
theorem B688055 : Blo 686314 688055 := bstep (se 1 (by rfl) ⟨516041, by rfl⟩ : syracuseStep 688055 = 1032083) B1032083
theorem B688075 : Blo 686314 688075 := bstep (se 1 (by rfl) ⟨516056, by rfl⟩ : syracuseStep 688075 = 1032113) B1032113
theorem B688087 : Blo 686314 688087 := bstep (se 1 (by rfl) ⟨516065, by rfl⟩ : syracuseStep 688087 = 1032131) B1032131
theorem B688107 : Blo 686314 688107 := bstep (se 1 (by rfl) ⟨516080, by rfl⟩ : syracuseStep 688107 = 1032161) B1032161
theorem B688119 : Blo 686314 688119 := bstep (se 1 (by rfl) ⟨516089, by rfl⟩ : syracuseStep 688119 = 1032179) B1032179
theorem B688135 : Blo 686314 688135 := bstep (se 1 (by rfl) ⟨516101, by rfl⟩ : syracuseStep 688135 = 1032203) B1032203
theorem B688143 : Blo 686314 688143 := bstep (se 1 (by rfl) ⟨516107, by rfl⟩ : syracuseStep 688143 = 1032215) B1032215
theorem B688187 : Blo 686314 688187 := bstep (se 1 (by rfl) ⟨516140, by rfl⟩ : syracuseStep 688187 = 1032281) B1032281
theorem B2326589 : Blo 686314 2326589 := bstep (se 3 (by rfl) ⟨436235, by rfl⟩ : syracuseStep 2326589 = 872471) B872471
theorem B688263 : Blo 686314 688263 := bstep (se 1 (by rfl) ⟨516197, by rfl⟩ : syracuseStep 688263 = 1032395) B1032395
theorem B688271 : Blo 686314 688271 := bstep (se 1 (by rfl) ⟨516203, by rfl⟩ : syracuseStep 688271 = 1032407) B1032407
theorem B688315 : Blo 686314 688315 := bstep (se 1 (by rfl) ⟨516236, by rfl⟩ : syracuseStep 688315 = 1032473) B1032473
theorem B688391 : Blo 686314 688391 := bstep (se 1 (by rfl) ⟨516293, by rfl⟩ : syracuseStep 688391 = 1032587) B1032587
theorem B688399 : Blo 686314 688399 := bstep (se 1 (by rfl) ⟨516299, by rfl⟩ : syracuseStep 688399 = 1032599) B1032599
theorem B688443 : Blo 686314 688443 := bstep (se 1 (by rfl) ⟨516332, by rfl⟩ : syracuseStep 688443 = 1032665) B1032665
theorem B688519 : Blo 686314 688519 := bstep (se 1 (by rfl) ⟨516389, by rfl⟩ : syracuseStep 688519 = 1032779) B1032779
theorem B688527 : Blo 686314 688527 := bstep (se 1 (by rfl) ⟨516395, by rfl⟩ : syracuseStep 688527 = 1032791) B1032791
theorem B688571 : Blo 686314 688571 := bstep (se 1 (by rfl) ⟨516428, by rfl⟩ : syracuseStep 688571 = 1032857) B1032857
theorem B688647 : Blo 686314 688647 := bstep (se 1 (by rfl) ⟨516485, by rfl⟩ : syracuseStep 688647 = 1032971) B1032971
theorem B688655 : Blo 686314 688655 := bstep (se 1 (by rfl) ⟨516491, by rfl⟩ : syracuseStep 688655 = 1032983) B1032983
theorem B1573391 : Blo 686314 1573391 := bstep (se 1 (by rfl) ⟨1180043, by rfl⟩ : syracuseStep 1573391 = 2360087) B2360087
theorem B688699 : Blo 686314 688699 := bstep (se 1 (by rfl) ⟨516524, by rfl⟩ : syracuseStep 688699 = 1033049) B1033049
theorem B688775 : Blo 686314 688775 := bstep (se 1 (by rfl) ⟨516581, by rfl⟩ : syracuseStep 688775 = 1033163) B1033163
theorem B688783 : Blo 686314 688783 := bstep (se 1 (by rfl) ⟨516587, by rfl⟩ : syracuseStep 688783 = 1033175) B1033175
theorem B1180345 : Blo 686314 1180345 := bstep (se 2 (by rfl) ⟨442629, by rfl⟩ : syracuseStep 1180345 = 885259) B885259
theorem B688827 : Blo 686314 688827 := bstep (se 1 (by rfl) ⟨516620, by rfl⟩ : syracuseStep 688827 = 1033241) B1033241
theorem B688903 : Blo 686314 688903 := bstep (se 1 (by rfl) ⟨516677, by rfl⟩ : syracuseStep 688903 = 1033355) B1033355
theorem B688911 : Blo 686314 688911 := bstep (se 1 (by rfl) ⟨516683, by rfl⟩ : syracuseStep 688911 = 1033367) B1033367
theorem B688955 : Blo 686314 688955 := bstep (se 1 (by rfl) ⟨516716, by rfl⟩ : syracuseStep 688955 = 1033433) B1033433
theorem B689031 : Blo 686314 689031 := bstep (se 1 (by rfl) ⟨516773, by rfl⟩ : syracuseStep 689031 = 1033547) B1033547
theorem B689039 : Blo 686314 689039 := bstep (se 1 (by rfl) ⟨516779, by rfl⟩ : syracuseStep 689039 = 1033559) B1033559
theorem B4195219 : Blo 686314 4195219 := bstep (se 1 (by rfl) ⟨3146414, by rfl⟩ : syracuseStep 4195219 = 6292829) B6292829
theorem B689083 : Blo 686314 689083 := bstep (se 1 (by rfl) ⟨516812, by rfl⟩ : syracuseStep 689083 = 1033625) B1033625
theorem B4031441 : Blo 686314 4031441 := bstep (se 2 (by rfl) ⟨1511790, by rfl⟩ : syracuseStep 4031441 = 3023581) B3023581
theorem B689159 : Blo 686314 689159 := bstep (se 1 (by rfl) ⟨516869, by rfl⟩ : syracuseStep 689159 = 1033739) B1033739
theorem B689167 : Blo 686314 689167 := bstep (se 1 (by rfl) ⟨516875, by rfl⟩ : syracuseStep 689167 = 1033751) B1033751
theorem B689211 : Blo 686314 689211 := bstep (se 1 (by rfl) ⟨516908, by rfl⟩ : syracuseStep 689211 = 1033817) B1033817
theorem B4195415 : Blo 686314 4195415 := bstep (se 1 (by rfl) ⟨3146561, by rfl⟩ : syracuseStep 4195415 = 6293123) B6293123
theorem B1115255 : Blo 686314 1115255 := bstep (se 1 (by rfl) ⟨836441, by rfl⟩ : syracuseStep 1115255 = 1672883) B1672883
theorem B689287 : Blo 686314 689287 := bstep (se 1 (by rfl) ⟨516965, by rfl⟩ : syracuseStep 689287 = 1033931) B1033931
theorem B689295 : Blo 686314 689295 := bstep (se 1 (by rfl) ⟨516971, by rfl⟩ : syracuseStep 689295 = 1033943) B1033943
theorem B1737875 : Blo 686314 1737875 := bstep (se 1 (by rfl) ⟨1303406, by rfl⟩ : syracuseStep 1737875 = 2606813) B2606813
theorem B689339 : Blo 686314 689339 := bstep (se 1 (by rfl) ⟨517004, by rfl⟩ : syracuseStep 689339 = 1034009) B1034009
theorem B689415 : Blo 686314 689415 := bstep (se 1 (by rfl) ⟨517061, by rfl⟩ : syracuseStep 689415 = 1034123) B1034123
theorem B689423 : Blo 686314 689423 := bstep (se 1 (by rfl) ⟨517067, by rfl⟩ : syracuseStep 689423 = 1034135) B1034135
theorem B689467 : Blo 686314 689467 := bstep (se 1 (by rfl) ⟨517100, by rfl⟩ : syracuseStep 689467 = 1034201) B1034201
theorem B689543 : Blo 686314 689543 := bstep (se 1 (by rfl) ⟨517157, by rfl⟩ : syracuseStep 689543 = 1034315) B1034315
theorem B689551 : Blo 686314 689551 := bstep (se 1 (by rfl) ⟨517163, by rfl⟩ : syracuseStep 689551 = 1034327) B1034327
theorem B1738169 : Blo 686314 1738169 := bstep (se 2 (by rfl) ⟨651813, by rfl⟩ : syracuseStep 1738169 = 1303627) B1303627
theorem B2327993 : Blo 686314 2327993 := bstep (se 2 (by rfl) ⟨872997, by rfl⟩ : syracuseStep 2327993 = 1745995) B1745995
theorem B689595 : Blo 686314 689595 := bstep (se 1 (by rfl) ⟨517196, by rfl⟩ : syracuseStep 689595 = 1034393) B1034393
theorem B689671 : Blo 686314 689671 := bstep (se 1 (by rfl) ⟨517253, by rfl⟩ : syracuseStep 689671 = 1034507) B1034507
theorem B689679 : Blo 686314 689679 := bstep (se 1 (by rfl) ⟨517259, by rfl⟩ : syracuseStep 689679 = 1034519) B1034519
theorem B689723 : Blo 686314 689723 := bstep (se 1 (by rfl) ⟨517292, by rfl⟩ : syracuseStep 689723 = 1034585) B1034585
theorem B689799 : Blo 686314 689799 := bstep (se 1 (by rfl) ⟨517349, by rfl⟩ : syracuseStep 689799 = 1034699) B1034699
theorem B689807 : Blo 686314 689807 := bstep (se 1 (by rfl) ⟨517355, by rfl⟩ : syracuseStep 689807 = 1034711) B1034711
theorem B689851 : Blo 686314 689851 := bstep (se 1 (by rfl) ⟨517388, by rfl⟩ : syracuseStep 689851 = 1034777) B1034777
theorem B689927 : Blo 686314 689927 := bstep (se 1 (by rfl) ⟨517445, by rfl⟩ : syracuseStep 689927 = 1034891) B1034891
theorem B689935 : Blo 686314 689935 := bstep (se 1 (by rfl) ⟨517451, by rfl⟩ : syracuseStep 689935 = 1034903) B1034903
theorem B689979 : Blo 686314 689979 := bstep (se 1 (by rfl) ⟨517484, by rfl⟩ : syracuseStep 689979 = 1034969) B1034969
theorem B690055 : Blo 686314 690055 := bstep (se 1 (by rfl) ⟨517541, by rfl⟩ : syracuseStep 690055 = 1035083) B1035083
theorem B690063 : Blo 686314 690063 := bstep (se 1 (by rfl) ⟨517547, by rfl⟩ : syracuseStep 690063 = 1035095) B1035095
theorem B11175833 : Blo 686314 11175833 := bstep (se 2 (by rfl) ⟨4190937, by rfl⟩ : syracuseStep 11175833 = 8381875) B8381875
theorem B3311513 : Blo 686314 3311513 := bstep (se 2 (by rfl) ⟨1241817, by rfl⟩ : syracuseStep 3311513 = 2483635) B2483635
theorem B3475385 : Blo 686314 3475385 := bstep (se 2 (by rfl) ⟨1303269, by rfl⟩ : syracuseStep 3475385 = 2606539) B2606539
theorem B690107 : Blo 686314 690107 := bstep (se 1 (by rfl) ⟨517580, by rfl⟩ : syracuseStep 690107 = 1035161) B1035161
theorem B690183 : Blo 686314 690183 := bstep (se 1 (by rfl) ⟨517637, by rfl⟩ : syracuseStep 690183 = 1035275) B1035275
theorem B2328587 : Blo 686314 2328587 := bstep (se 1 (by rfl) ⟨1746440, by rfl⟩ : syracuseStep 2328587 = 3492881) B3492881
theorem B690191 : Blo 686314 690191 := bstep (se 1 (by rfl) ⟨517643, by rfl⟩ : syracuseStep 690191 = 1035287) B1035287
theorem B690235 : Blo 686314 690235 := bstep (se 1 (by rfl) ⟨517676, by rfl⟩ : syracuseStep 690235 = 1035353) B1035353
theorem B1738867 : Blo 686314 1738867 := bstep (se 1 (by rfl) ⟨1304150, by rfl⟩ : syracuseStep 1738867 = 2608301) B2608301
theorem B2328695 : Blo 686314 2328695 := bstep (se 1 (by rfl) ⟨1746521, by rfl⟩ : syracuseStep 2328695 = 3493043) B3493043
theorem B8390789 : Blo 686314 8390789 := bstep (se 4 (by rfl) ⟨786636, by rfl⟩ : syracuseStep 8390789 = 1573273) B1573273
theorem B690311 : Blo 686314 690311 := bstep (se 1 (by rfl) ⟨517733, by rfl⟩ : syracuseStep 690311 = 1035467) B1035467
theorem B1739009 : Blo 686314 1739009 := bstep (se 2 (by rfl) ⟨652128, by rfl⟩ : syracuseStep 1739009 = 1304257) B1304257
theorem B1411387 : Blo 686314 1411387 := bstep (se 1 (by rfl) ⟨1058540, by rfl⟩ : syracuseStep 1411387 = 2117081) B2117081
theorem B1739465 : Blo 686314 1739465 := bstep (se 2 (by rfl) ⟨652299, by rfl⟩ : syracuseStep 1739465 = 1304599) B1304599
theorem B2329289 : Blo 686314 2329289 := bstep (se 2 (by rfl) ⟨873483, by rfl⟩ : syracuseStep 2329289 = 1746967) B1746967
theorem B1739819 : Blo 686314 1739819 := bstep (se 1 (by rfl) ⟨1304864, by rfl⟩ : syracuseStep 1739819 = 2609729) B2609729
theorem B3476681 : Blo 686314 3476681 := bstep (se 2 (by rfl) ⟨1303755, by rfl⟩ : syracuseStep 3476681 = 2607511) B2607511
theorem B8391995 : Blo 686314 8391995 := bstep (se 1 (by rfl) ⟨6293996, by rfl⟩ : syracuseStep 8391995 = 12587993) B12587993
theorem B1150507 : Blo 686314 1150507 := bstep (se 1 (by rfl) ⟨862880, by rfl⟩ : syracuseStep 1150507 = 1725761) B1725761
theorem B5869361 : Blo 686314 5869361 := bstep (se 2 (by rfl) ⟨2201010, by rfl⟩ : syracuseStep 5869361 = 4402021) B4402021
theorem B5967731 : Blo 686314 5967731 := bstep (se 1 (by rfl) ⟨4475798, by rfl⟩ : syracuseStep 5967731 = 8951597) B8951597
theorem B1740811 : Blo 686314 1740811 := bstep (se 1 (by rfl) ⟨1305608, by rfl⟩ : syracuseStep 1740811 = 2611217) B2611217
theorem B1544327 : Blo 686314 1544327 := bstep (se 1 (by rfl) ⟨1158245, by rfl⟩ : syracuseStep 1544327 = 2316491) B2316491
theorem B1740953 : Blo 686314 1740953 := bstep (se 2 (by rfl) ⟨652857, by rfl⟩ : syracuseStep 1740953 = 1305715) B1305715
theorem B1544507 : Blo 686314 1544507 := bstep (se 1 (by rfl) ⟨1158380, by rfl⟩ : syracuseStep 1544507 = 2316761) B2316761
theorem B1741115 : Blo 686314 1741115 := bstep (se 1 (by rfl) ⟨1305836, by rfl⟩ : syracuseStep 1741115 = 2611673) B2611673
theorem B11735441 : Blo 686314 11735441 := bstep (se 2 (by rfl) ⟨4400790, by rfl⟩ : syracuseStep 11735441 = 8801581) B8801581
theorem B1544633 : Blo 686314 1544633 := bstep (se 2 (by rfl) ⟨579237, by rfl⟩ : syracuseStep 1544633 = 1158475) B1158475
theorem B1741459 : Blo 686314 1741459 := bstep (se 1 (by rfl) ⟨1306094, by rfl⟩ : syracuseStep 1741459 = 2612189) B2612189
theorem B1544975 : Blo 686314 1544975 := bstep (se 1 (by rfl) ⟨1158731, by rfl⟩ : syracuseStep 1544975 = 2317463) B2317463
theorem B1544993 : Blo 686314 1544993 := bstep (se 2 (by rfl) ⟨579372, by rfl⟩ : syracuseStep 1544993 = 1158745) B1158745
theorem B1741601 : Blo 686314 1741601 := bstep (se 2 (by rfl) ⟨653100, by rfl⟩ : syracuseStep 1741601 = 1306201) B1306201
theorem B7443251 : Blo 686314 7443251 := bstep (se 1 (by rfl) ⟨5582438, by rfl⟩ : syracuseStep 7443251 = 11164877) B11164877
theorem B8360819 : Blo 686314 8360819 := bstep (se 1 (by rfl) ⟨6270614, by rfl⟩ : syracuseStep 8360819 = 12541229) B12541229
theorem B1545335 : Blo 686314 1545335 := bstep (se 1 (by rfl) ⟨1159001, by rfl⟩ : syracuseStep 1545335 = 2318003) B2318003
theorem B13407437 : Blo 686314 13407437 := bstep (se 3 (by rfl) ⟨2513894, by rfl⟩ : syracuseStep 13407437 = 5027789) B5027789
theorem B1545515 : Blo 686314 1545515 := bstep (se 1 (by rfl) ⟨1159136, by rfl⟩ : syracuseStep 1545515 = 2318273) B2318273
theorem B2790715 : Blo 686314 2790715 := bstep (se 1 (by rfl) ⟨2093036, by rfl⟩ : syracuseStep 2790715 = 4186073) B4186073
theorem B13604273 : Blo 686314 13604273 := bstep (se 2 (by rfl) ⟨5101602, by rfl⟩ : syracuseStep 13604273 = 10203205) B10203205
theorem B25073221 : Blo 686314 25073221 := bstep (se 4 (by rfl) ⟨2350614, by rfl⟩ : syracuseStep 25073221 = 4701229) B4701229
theorem B1545875 : Blo 686314 1545875 := bstep (se 1 (by rfl) ⟨1159406, by rfl⟩ : syracuseStep 1545875 = 2318813) B2318813
theorem B1545929 : Blo 686314 1545929 := bstep (se 2 (by rfl) ⟨579723, by rfl⟩ : syracuseStep 1545929 = 1159447) B1159447
theorem B1742593 : Blo 686314 1742593 := bstep (se 2 (by rfl) ⟨653472, by rfl⟩ : syracuseStep 1742593 = 1306945) B1306945
theorem B1743191 : Blo 686314 1743191 := bstep (se 1 (by rfl) ⟨1307393, by rfl⟩ : syracuseStep 1743191 = 2614787) B2614787
theorem B1546631 : Blo 686314 1546631 := bstep (se 1 (by rfl) ⟨1159973, by rfl⟩ : syracuseStep 1546631 = 2319947) B2319947
theorem B1743403 : Blo 686314 1743403 := bstep (se 1 (by rfl) ⟨1307552, by rfl⟩ : syracuseStep 1743403 = 2615105) B2615105
theorem B1546811 : Blo 686314 1546811 := bstep (se 1 (by rfl) ⟨1160108, by rfl⟩ : syracuseStep 1546811 = 2320217) B2320217
theorem B11770433 : Blo 686314 11770433 := bstep (se 2 (by rfl) ⟨4413912, by rfl⟩ : syracuseStep 11770433 = 8827825) B8827825
theorem B1546937 : Blo 686314 1546937 := bstep (se 2 (by rfl) ⟨580101, by rfl⟩ : syracuseStep 1546937 = 1160203) B1160203
theorem B1743545 : Blo 686314 1743545 := bstep (se 2 (by rfl) ⟨653829, by rfl⟩ : syracuseStep 1743545 = 1307659) B1307659
theorem B6626063 : Blo 686314 6626063 := bstep (se 1 (by rfl) ⟨4969547, by rfl⟩ : syracuseStep 6626063 = 9939095) B9939095
theorem B4954931 : Blo 686314 4954931 := bstep (se 1 (by rfl) ⟨3716198, by rfl⟩ : syracuseStep 4954931 = 7432397) B7432397
theorem B3873587 : Blo 686314 3873587 := bstep (se 1 (by rfl) ⟨2905190, by rfl⟩ : syracuseStep 3873587 = 5810381) B5810381
theorem B2792339 : Blo 686314 2792339 := bstep (se 1 (by rfl) ⟨2094254, by rfl⟩ : syracuseStep 2792339 = 4188509) B4188509
theorem B826375 : Blo 686314 826375 := bstep (se 1 (by rfl) ⟨619781, by rfl⟩ : syracuseStep 826375 = 1239563) B1239563
theorem B1547279 : Blo 686314 1547279 := bstep (se 1 (by rfl) ⟨1160459, by rfl⟩ : syracuseStep 1547279 = 2320919) B2320919
theorem B1547297 : Blo 686314 1547297 := bstep (se 2 (by rfl) ⟨580236, by rfl⟩ : syracuseStep 1547297 = 1160473) B1160473
theorem B5577929 : Blo 686314 5577929 := bstep (se 2 (by rfl) ⟨2091723, by rfl⟩ : syracuseStep 5577929 = 4183447) B4183447
theorem B1547639 : Blo 686314 1547639 := bstep (se 1 (by rfl) ⟨1160729, by rfl⟩ : syracuseStep 1547639 = 2321459) B2321459
theorem B990599 : Blo 686314 990599 := bstep (se 1 (by rfl) ⟨742949, by rfl⟩ : syracuseStep 990599 = 1485899) B1485899
theorem B3317201 : Blo 686314 3317201 := bstep (se 2 (by rfl) ⟨1243950, by rfl⟩ : syracuseStep 3317201 = 2487901) B2487901
theorem B1547819 : Blo 686314 1547819 := bstep (se 1 (by rfl) ⟨1160864, by rfl⟩ : syracuseStep 1547819 = 2321729) B2321729
theorem B1744537 : Blo 686314 1744537 := bstep (se 2 (by rfl) ⟨654201, by rfl⟩ : syracuseStep 1744537 = 1308403) B1308403
theorem B1744699 : Blo 686314 1744699 := bstep (se 1 (by rfl) ⟨1308524, by rfl⟩ : syracuseStep 1744699 = 2617049) B2617049
theorem B1548179 : Blo 686314 1548179 := bstep (se 1 (by rfl) ⟨1161134, by rfl⟩ : syracuseStep 1548179 = 2322269) B2322269
theorem B1548233 : Blo 686314 1548233 := bstep (se 2 (by rfl) ⟨580587, by rfl⟩ : syracuseStep 1548233 = 1161175) B1161175
theorem B1744841 : Blo 686314 1744841 := bstep (se 2 (by rfl) ⟨654315, by rfl⟩ : syracuseStep 1744841 = 1308631) B1308631
theorem B3711095 : Blo 686314 3711095 := bstep (se 1 (by rfl) ⟨2783321, by rfl⟩ : syracuseStep 3711095 = 5566643) B5566643
theorem B1745185 : Blo 686314 1745185 := bstep (se 2 (by rfl) ⟨654444, by rfl⟩ : syracuseStep 1745185 = 1308889) B1308889
theorem B2204189 : Blo 686314 2204189 := bstep (se 3 (by rfl) ⟨413285, by rfl⟩ : syracuseStep 2204189 = 826571) B826571
theorem B1548935 : Blo 686314 1548935 := bstep (se 1 (by rfl) ⟨1161701, by rfl⟩ : syracuseStep 1548935 = 2323403) B2323403
theorem B1549115 : Blo 686314 1549115 := bstep (se 1 (by rfl) ⟨1161836, by rfl⟩ : syracuseStep 1549115 = 2323673) B2323673
theorem B1745783 : Blo 686314 1745783 := bstep (se 1 (by rfl) ⟨1309337, by rfl⟩ : syracuseStep 1745783 = 2618675) B2618675
theorem B3482513 : Blo 686314 3482513 := bstep (se 2 (by rfl) ⟨1305942, by rfl⟩ : syracuseStep 3482513 = 2611885) B2611885
theorem B1549241 : Blo 686314 1549241 := bstep (se 2 (by rfl) ⟨580965, by rfl⟩ : syracuseStep 1549241 = 1161931) B1161931
theorem B1549583 : Blo 686314 1549583 := bstep (se 1 (by rfl) ⟨1162187, by rfl⟩ : syracuseStep 1549583 = 2324375) B2324375
theorem B1549601 : Blo 686314 1549601 := bstep (se 2 (by rfl) ⟨581100, by rfl⟩ : syracuseStep 1549601 = 1162201) B1162201
theorem B992683 : Blo 686314 992683 := bstep (se 1 (by rfl) ⟨744512, by rfl⟩ : syracuseStep 992683 = 1489025) B1489025
theorem B1549943 : Blo 686314 1549943 := bstep (se 1 (by rfl) ⟨1162457, by rfl⟩ : syracuseStep 1549943 = 2324915) B2324915
theorem B1550123 : Blo 686314 1550123 := bstep (se 1 (by rfl) ⟨1162592, by rfl⟩ : syracuseStep 1550123 = 2325185) B2325185
theorem B3909491 : Blo 686314 3909491 := bstep (se 1 (by rfl) ⟨2932118, by rfl⟩ : syracuseStep 3909491 = 5864237) B5864237
theorem B10758041 : Blo 686314 10758041 := bstep (se 2 (by rfl) ⟨4034265, by rfl⟩ : syracuseStep 10758041 = 8068531) B8068531
theorem B1747079 : Blo 686314 1747079 := bstep (se 1 (by rfl) ⟨1310309, by rfl⟩ : syracuseStep 1747079 = 2620619) B2620619
theorem B1550483 : Blo 686314 1550483 := bstep (se 1 (by rfl) ⟨1162862, by rfl⟩ : syracuseStep 1550483 = 2325725) B2325725
theorem B1747129 : Blo 686314 1747129 := bstep (se 2 (by rfl) ⟨655173, by rfl⟩ : syracuseStep 1747129 = 1310347) B1310347
theorem B1550537 : Blo 686314 1550537 := bstep (se 2 (by rfl) ⟨581451, by rfl⟩ : syracuseStep 1550537 = 1162903) B1162903
theorem B1551239 : Blo 686314 1551239 := bstep (se 1 (by rfl) ⟨1163429, by rfl⟩ : syracuseStep 1551239 = 2326859) B2326859
theorem B2206649 : Blo 686314 2206649 := bstep (se 2 (by rfl) ⟨827493, by rfl⟩ : syracuseStep 2206649 = 1654987) B1654987
theorem B3484619 : Blo 686314 3484619 := bstep (se 1 (by rfl) ⟨2613464, by rfl⟩ : syracuseStep 3484619 = 5226929) B5226929
theorem B3779531 : Blo 686314 3779531 := bstep (se 1 (by rfl) ⟨2834648, by rfl⟩ : syracuseStep 3779531 = 5669297) B5669297
theorem B928811 : Blo 686314 928811 := bstep (se 1 (by rfl) ⟨696608, by rfl⟩ : syracuseStep 928811 = 1393217) B1393217
theorem B1551419 : Blo 686314 1551419 := bstep (se 1 (by rfl) ⟨1163564, by rfl⟩ : syracuseStep 1551419 = 2327129) B2327129
theorem B1551545 : Blo 686314 1551545 := bstep (se 2 (by rfl) ⟨581829, by rfl⟩ : syracuseStep 1551545 = 1163659) B1163659
theorem B3484943 : Blo 686314 3484943 := bstep (se 1 (by rfl) ⟨2613707, by rfl⟩ : syracuseStep 3484943 = 5227415) B5227415
theorem B3910949 : Blo 686314 3910949 := bstep (se 4 (by rfl) ⟨366651, by rfl⟩ : syracuseStep 3910949 = 733303) B733303
theorem B1158671 : Blo 686314 1158671 := bstep (se 1 (by rfl) ⟨869003, by rfl⟩ : syracuseStep 1158671 = 1738007) B1738007
theorem B1551887 : Blo 686314 1551887 := bstep (se 1 (by rfl) ⟨1163915, by rfl⟩ : syracuseStep 1551887 = 2327831) B2327831
theorem B1551905 : Blo 686314 1551905 := bstep (se 2 (by rfl) ⟨581964, by rfl⟩ : syracuseStep 1551905 = 1163929) B1163929
theorem B1650547 : Blo 686314 1650547 := bstep (se 1 (by rfl) ⟨1237910, by rfl⟩ : syracuseStep 1650547 = 2475821) B2475821
theorem B1552247 : Blo 686314 1552247 := bstep (se 1 (by rfl) ⟨1164185, by rfl⟩ : syracuseStep 1552247 = 2328371) B2328371
theorem B3911723 : Blo 686314 3911723 := bstep (se 1 (by rfl) ⟨2933792, by rfl⟩ : syracuseStep 3911723 = 5867585) B5867585
theorem B1159211 : Blo 686314 1159211 := bstep (se 1 (by rfl) ⟨869408, by rfl⟩ : syracuseStep 1159211 = 1738817) B1738817
theorem B1552427 : Blo 686314 1552427 := bstep (se 1 (by rfl) ⟨1164320, by rfl⟩ : syracuseStep 1552427 = 2328641) B2328641
theorem B3715159 : Blo 686314 3715159 := bstep (se 1 (by rfl) ⟨2786369, by rfl⟩ : syracuseStep 3715159 = 5572739) B5572739
theorem B3715417 : Blo 686314 3715417 := bstep (se 2 (by rfl) ⟨1393281, by rfl⟩ : syracuseStep 3715417 = 2786563) B2786563
theorem B3715463 : Blo 686314 3715463 := bstep (se 1 (by rfl) ⟨2786597, by rfl⟩ : syracuseStep 3715463 = 5573195) B5573195
theorem B1552787 : Blo 686314 1552787 := bstep (se 1 (by rfl) ⟨1164590, by rfl⟩ : syracuseStep 1552787 = 2329181) B2329181
theorem B1159609 : Blo 686314 1159609 := bstep (se 2 (by rfl) ⟨434853, by rfl⟩ : syracuseStep 1159609 = 869707) B869707
theorem B995771 : Blo 686314 995771 := bstep (se 1 (by rfl) ⟨746828, by rfl⟩ : syracuseStep 995771 = 1493657) B1493657
theorem B1552841 : Blo 686314 1552841 := bstep (se 2 (by rfl) ⟨582315, by rfl⟩ : syracuseStep 1552841 = 1164631) B1164631
theorem B8794817 : Blo 686314 8794817 := bstep (se 2 (by rfl) ⟨3298056, by rfl⟩ : syracuseStep 8794817 = 6596113) B6596113
theorem B3486401 : Blo 686314 3486401 := bstep (se 2 (by rfl) ⟨1307400, by rfl⟩ : syracuseStep 3486401 = 2614801) B2614801
theorem B2798369 : Blo 686314 2798369 := bstep (se 2 (by rfl) ⟨1049388, by rfl⟩ : syracuseStep 2798369 = 2098777) B2098777
theorem B18789155 : Blo 686314 18789155 := bstep (se 1 (by rfl) ⟨14091866, by rfl⟩ : syracuseStep 18789155 = 28183733) B28183733
theorem B2241433 : Blo 686314 2241433 := bstep (se 2 (by rfl) ⟨840537, by rfl⟩ : syracuseStep 2241433 = 1681075) B1681075
theorem B5649431 : Blo 686314 5649431 := bstep (se 1 (by rfl) ⟨4237073, by rfl⟩ : syracuseStep 5649431 = 8474147) B8474147
theorem B2208829 : Blo 686314 2208829 := bstep (se 3 (by rfl) ⟨414155, by rfl⟩ : syracuseStep 2208829 = 828311) B828311
theorem B1160311 : Blo 686314 1160311 := bstep (se 1 (by rfl) ⟨870233, by rfl⟩ : syracuseStep 1160311 = 1740467) B1740467
theorem B1160507 : Blo 686314 1160507 := bstep (se 1 (by rfl) ⟨870380, by rfl⟩ : syracuseStep 1160507 = 1740761) B1740761
theorem B1029563 : Blo 686314 1029563 := bstep (se 1 (by rfl) ⟨772172, by rfl⟩ : syracuseStep 1029563 = 1544345) B1544345
theorem B3913181 : Blo 686314 3913181 := bstep (se 3 (by rfl) ⟨733721, by rfl⟩ : syracuseStep 3913181 = 1467443) B1467443
theorem B1029623 : Blo 686314 1029623 := bstep (se 1 (by rfl) ⟨772217, by rfl⟩ : syracuseStep 1029623 = 1544435) B1544435
theorem B4404739 : Blo 686314 4404739 := bstep (se 1 (by rfl) ⟨3303554, by rfl⟩ : syracuseStep 4404739 = 6607109) B6607109
theorem B1029647 : Blo 686314 1029647 := bstep (se 1 (by rfl) ⟨772235, by rfl⟩ : syracuseStep 1029647 = 1544471) B1544471
theorem B1029689 : Blo 686314 1029689 := bstep (se 2 (by rfl) ⟨386133, by rfl⟩ : syracuseStep 1029689 = 772267) B772267
theorem B931385 : Blo 686314 931385 := bstep (se 2 (by rfl) ⟨349269, by rfl⟩ : syracuseStep 931385 = 698539) B698539
theorem B1914427 : Blo 686314 1914427 := bstep (se 1 (by rfl) ⟨1435820, by rfl⟩ : syracuseStep 1914427 = 2871641) B2871641
theorem B5224013 : Blo 686314 5224013 := bstep (se 3 (by rfl) ⟨979502, by rfl⟩ : syracuseStep 5224013 = 1959005) B1959005
theorem B1029767 : Blo 686314 1029767 := bstep (se 1 (by rfl) ⟨772325, by rfl⟩ : syracuseStep 1029767 = 1544651) B1544651
theorem B1029803 : Blo 686314 1029803 := bstep (se 1 (by rfl) ⟨772352, by rfl⟩ : syracuseStep 1029803 = 1544705) B1544705
theorem B1029833 : Blo 686314 1029833 := bstep (se 2 (by rfl) ⟨386187, by rfl⟩ : syracuseStep 1029833 = 772375) B772375
theorem B1160905 : Blo 686314 1160905 := bstep (se 2 (by rfl) ⟨435339, by rfl⟩ : syracuseStep 1160905 = 870679) B870679
theorem B1029947 : Blo 686314 1029947 := bstep (se 1 (by rfl) ⟨772460, by rfl⟩ : syracuseStep 1029947 = 1544921) B1544921
theorem B1030007 : Blo 686314 1030007 := bstep (se 1 (by rfl) ⟨772505, by rfl⟩ : syracuseStep 1030007 = 1545011) B1545011
theorem B1030031 : Blo 686314 1030031 := bstep (se 1 (by rfl) ⟨772523, by rfl⟩ : syracuseStep 1030031 = 1545047) B1545047
theorem B1030073 : Blo 686314 1030073 := bstep (se 2 (by rfl) ⟨386277, by rfl⟩ : syracuseStep 1030073 = 772555) B772555
theorem B3487697 : Blo 686314 3487697 := bstep (se 2 (by rfl) ⟨1307886, by rfl⟩ : syracuseStep 3487697 = 2615773) B2615773
theorem B1030151 : Blo 686314 1030151 := bstep (se 1 (by rfl) ⟨772613, by rfl⟩ : syracuseStep 1030151 = 1545227) B1545227
theorem B1030187 : Blo 686314 1030187 := bstep (se 1 (by rfl) ⟨772640, by rfl⟩ : syracuseStep 1030187 = 1545281) B1545281
theorem B1030217 : Blo 686314 1030217 := bstep (se 2 (by rfl) ⟨386331, by rfl⟩ : syracuseStep 1030217 = 772663) B772663
theorem B1030331 : Blo 686314 1030331 := bstep (se 1 (by rfl) ⟨772748, by rfl⟩ : syracuseStep 1030331 = 1545497) B1545497
theorem B1030391 : Blo 686314 1030391 := bstep (se 1 (by rfl) ⟨772793, by rfl⟩ : syracuseStep 1030391 = 1545587) B1545587
theorem B1030415 : Blo 686314 1030415 := bstep (se 1 (by rfl) ⟨772811, by rfl⟩ : syracuseStep 1030415 = 1545623) B1545623
theorem B1030457 : Blo 686314 1030457 := bstep (se 2 (by rfl) ⟨386421, by rfl⟩ : syracuseStep 1030457 = 772843) B772843
theorem B1030535 : Blo 686314 1030535 := bstep (se 1 (by rfl) ⟨772901, by rfl⟩ : syracuseStep 1030535 = 1545803) B1545803
theorem B1161607 : Blo 686314 1161607 := bstep (se 1 (by rfl) ⟨871205, by rfl⟩ : syracuseStep 1161607 = 1742411) B1742411
theorem B932239 : Blo 686314 932239 := bstep (se 1 (by rfl) ⟨699179, by rfl⟩ : syracuseStep 932239 = 1398359) B1398359
theorem B1030571 : Blo 686314 1030571 := bstep (se 1 (by rfl) ⟨772928, by rfl⟩ : syracuseStep 1030571 = 1545857) B1545857
theorem B1030601 : Blo 686314 1030601 := bstep (se 2 (by rfl) ⟨386475, by rfl⟩ : syracuseStep 1030601 = 772951) B772951
theorem B735751 : Blo 686314 735751 := bstep (se 1 (by rfl) ⟨551813, by rfl⟩ : syracuseStep 735751 = 1103627) B1103627
theorem B1030715 : Blo 686314 1030715 := bstep (se 1 (by rfl) ⟨773036, by rfl⟩ : syracuseStep 1030715 = 1546073) B1546073
theorem B6634061 : Blo 686314 6634061 := bstep (se 3 (by rfl) ⟨1243886, by rfl⟩ : syracuseStep 6634061 = 2487773) B2487773
theorem B1653335 : Blo 686314 1653335 := bstep (se 1 (by rfl) ⟨1240001, by rfl⟩ : syracuseStep 1653335 = 2480003) B2480003
theorem B1030775 : Blo 686314 1030775 := bstep (se 1 (by rfl) ⟨773081, by rfl⟩ : syracuseStep 1030775 = 1546163) B1546163
theorem B1030799 : Blo 686314 1030799 := bstep (se 1 (by rfl) ⟨773099, by rfl⟩ : syracuseStep 1030799 = 1546199) B1546199
theorem B1030841 : Blo 686314 1030841 := bstep (se 2 (by rfl) ⟨386565, by rfl⟩ : syracuseStep 1030841 = 773131) B773131
theorem B1030919 : Blo 686314 1030919 := bstep (se 1 (by rfl) ⟨773189, by rfl⟩ : syracuseStep 1030919 = 1546379) B1546379
theorem B1030955 : Blo 686314 1030955 := bstep (se 1 (by rfl) ⟨773216, by rfl⟩ : syracuseStep 1030955 = 1546433) B1546433
theorem B1653547 : Blo 686314 1653547 := bstep (se 1 (by rfl) ⟨1240160, by rfl⟩ : syracuseStep 1653547 = 2480321) B2480321
theorem B1030985 : Blo 686314 1030985 := bstep (se 2 (by rfl) ⟨386619, by rfl⟩ : syracuseStep 1030985 = 773239) B773239
theorem B1653623 : Blo 686314 1653623 := bstep (se 1 (by rfl) ⟨1240217, by rfl⟩ : syracuseStep 1653623 = 2480435) B2480435
theorem B1031099 : Blo 686314 1031099 := bstep (se 1 (by rfl) ⟨773324, by rfl⟩ : syracuseStep 1031099 = 1546649) B1546649
theorem B1031159 : Blo 686314 1031159 := bstep (se 1 (by rfl) ⟨773369, by rfl⟩ : syracuseStep 1031159 = 1546739) B1546739
theorem B1031183 : Blo 686314 1031183 := bstep (se 1 (by rfl) ⟨773387, by rfl⟩ : syracuseStep 1031183 = 1546775) B1546775
theorem B1162255 : Blo 686314 1162255 := bstep (se 1 (by rfl) ⟨871691, by rfl⟩ : syracuseStep 1162255 = 1743383) B1743383
theorem B1031225 : Blo 686314 1031225 := bstep (se 2 (by rfl) ⟨386709, by rfl⟩ : syracuseStep 1031225 = 773419) B773419
theorem B8928317 : Blo 686314 8928317 := bstep (se 3 (by rfl) ⟨1674059, by rfl⟩ : syracuseStep 8928317 = 3348119) B3348119
theorem B1031303 : Blo 686314 1031303 := bstep (se 1 (by rfl) ⟨773477, by rfl⟩ : syracuseStep 1031303 = 1546955) B1546955
theorem B1031339 : Blo 686314 1031339 := bstep (se 1 (by rfl) ⟨773504, by rfl⟩ : syracuseStep 1031339 = 1547009) B1547009
theorem B1031369 : Blo 686314 1031369 := bstep (se 2 (by rfl) ⟨386763, by rfl⟩ : syracuseStep 1031369 = 773527) B773527
theorem B2931983 : Blo 686314 2931983 := bstep (se 1 (by rfl) ⟨2198987, by rfl⟩ : syracuseStep 2931983 = 4397975) B4397975
theorem B1391887 : Blo 686314 1391887 := bstep (se 1 (by rfl) ⟨1043915, by rfl⟩ : syracuseStep 1391887 = 2087831) B2087831
theorem B1031483 : Blo 686314 1031483 := bstep (se 1 (by rfl) ⟨773612, by rfl⟩ : syracuseStep 1031483 = 1547225) B1547225
theorem B736571 : Blo 686314 736571 := bstep (se 1 (by rfl) ⟨552428, by rfl⟩ : syracuseStep 736571 = 1104857) B1104857
theorem B1031543 : Blo 686314 1031543 := bstep (se 1 (by rfl) ⟨773657, by rfl⟩ : syracuseStep 1031543 = 1547315) B1547315
theorem B1031567 : Blo 686314 1031567 := bstep (se 1 (by rfl) ⟨773675, by rfl⟩ : syracuseStep 1031567 = 1547351) B1547351
theorem B1031609 : Blo 686314 1031609 := bstep (se 2 (by rfl) ⟨386853, by rfl⟩ : syracuseStep 1031609 = 773707) B773707
theorem B4406737 : Blo 686314 4406737 := bstep (se 2 (by rfl) ⟨1652526, by rfl⟩ : syracuseStep 4406737 = 3305053) B3305053
theorem B1031687 : Blo 686314 1031687 := bstep (se 1 (by rfl) ⟨773765, by rfl⟩ : syracuseStep 1031687 = 1547531) B1547531
theorem B4898333 : Blo 686314 4898333 := bstep (se 3 (by rfl) ⟨918437, by rfl⟩ : syracuseStep 4898333 = 1836875) B1836875
theorem B1031723 : Blo 686314 1031723 := bstep (se 1 (by rfl) ⟨773792, by rfl⟩ : syracuseStep 1031723 = 1547585) B1547585
theorem B1162795 : Blo 686314 1162795 := bstep (se 1 (by rfl) ⟨872096, by rfl⟩ : syracuseStep 1162795 = 1744193) B1744193
theorem B1031753 : Blo 686314 1031753 := bstep (se 2 (by rfl) ⟨386907, by rfl⟩ : syracuseStep 1031753 = 773815) B773815
theorem B6602417 : Blo 686314 6602417 := bstep (se 2 (by rfl) ⟨2475906, by rfl⟩ : syracuseStep 6602417 = 4951813) B4951813
theorem B1162937 : Blo 686314 1162937 := bstep (se 2 (by rfl) ⟨436101, by rfl⟩ : syracuseStep 1162937 = 872203) B872203
theorem B1031867 : Blo 686314 1031867 := bstep (se 1 (by rfl) ⟨773900, by rfl⟩ : syracuseStep 1031867 = 1547801) B1547801
theorem B1031927 : Blo 686314 1031927 := bstep (se 1 (by rfl) ⟨773945, by rfl⟩ : syracuseStep 1031927 = 1547891) B1547891
theorem B1031951 : Blo 686314 1031951 := bstep (se 1 (by rfl) ⟨773963, by rfl⟩ : syracuseStep 1031951 = 1547927) B1547927
theorem B1294123 : Blo 686314 1294123 := bstep (se 1 (by rfl) ⟨970592, by rfl⟩ : syracuseStep 1294123 = 1941185) B1941185
theorem B1031993 : Blo 686314 1031993 := bstep (se 2 (by rfl) ⟨386997, by rfl⟩ : syracuseStep 1031993 = 773995) B773995
theorem B1032071 : Blo 686314 1032071 := bstep (se 1 (by rfl) ⟨774053, by rfl⟩ : syracuseStep 1032071 = 1548107) B1548107
theorem B1032107 : Blo 686314 1032107 := bstep (se 1 (by rfl) ⟨774080, by rfl⟩ : syracuseStep 1032107 = 1548161) B1548161
theorem B1392569 : Blo 686314 1392569 := bstep (se 2 (by rfl) ⟨522213, by rfl⟩ : syracuseStep 1392569 = 1044427) B1044427
theorem B1032137 : Blo 686314 1032137 := bstep (se 2 (by rfl) ⟨387051, by rfl⟩ : syracuseStep 1032137 = 774103) B774103
theorem B5226443 : Blo 686314 5226443 := bstep (se 1 (by rfl) ⟨3919832, by rfl⟩ : syracuseStep 5226443 = 7839665) B7839665
theorem B3489803 : Blo 686314 3489803 := bstep (se 1 (by rfl) ⟨2617352, by rfl⟩ : syracuseStep 3489803 = 5234705) B5234705
theorem B1032251 : Blo 686314 1032251 := bstep (se 1 (by rfl) ⟨774188, by rfl⟩ : syracuseStep 1032251 = 1548377) B1548377
theorem B1032311 : Blo 686314 1032311 := bstep (se 1 (by rfl) ⟨774233, by rfl⟩ : syracuseStep 1032311 = 1548467) B1548467
theorem B1032335 : Blo 686314 1032335 := bstep (se 1 (by rfl) ⟨774251, by rfl⟩ : syracuseStep 1032335 = 1548503) B1548503
theorem B3489965 : Blo 686314 3489965 := bstep (se 3 (by rfl) ⟨654368, by rfl⟩ : syracuseStep 3489965 = 1308737) B1308737
theorem B1032377 : Blo 686314 1032377 := bstep (se 2 (by rfl) ⟨387141, by rfl⟩ : syracuseStep 1032377 = 774283) B774283
theorem B2932973 : Blo 686314 2932973 := bstep (se 3 (by rfl) ⟨549932, by rfl⟩ : syracuseStep 2932973 = 1099865) B1099865
theorem B1032455 : Blo 686314 1032455 := bstep (se 1 (by rfl) ⟨774341, by rfl⟩ : syracuseStep 1032455 = 1548683) B1548683
theorem B1032491 : Blo 686314 1032491 := bstep (se 1 (by rfl) ⟨774368, by rfl⟩ : syracuseStep 1032491 = 1548737) B1548737
theorem B1032521 : Blo 686314 1032521 := bstep (se 2 (by rfl) ⟨387195, by rfl⟩ : syracuseStep 1032521 = 774391) B774391
theorem B1163639 : Blo 686314 1163639 := bstep (se 1 (by rfl) ⟨872729, by rfl⟩ : syracuseStep 1163639 = 1745459) B1745459
theorem B1491347 : Blo 686314 1491347 := bstep (se 1 (by rfl) ⟨1118510, by rfl⟩ : syracuseStep 1491347 = 2237021) B2237021
theorem B1032635 : Blo 686314 1032635 := bstep (se 1 (by rfl) ⟨774476, by rfl⟩ : syracuseStep 1032635 = 1548953) B1548953
theorem B7848413 : Blo 686314 7848413 := bstep (se 3 (by rfl) ⟨1471577, by rfl⟩ : syracuseStep 7848413 = 2943155) B2943155
theorem B1032695 : Blo 686314 1032695 := bstep (se 1 (by rfl) ⟨774521, by rfl⟩ : syracuseStep 1032695 = 1549043) B1549043
theorem B1032719 : Blo 686314 1032719 := bstep (se 1 (by rfl) ⟨774539, by rfl⟩ : syracuseStep 1032719 = 1549079) B1549079
theorem B868907 : Blo 686314 868907 := bstep (se 1 (by rfl) ⟨651680, by rfl⟩ : syracuseStep 868907 = 1303361) B1303361
theorem B1032761 : Blo 686314 1032761 := bstep (se 2 (by rfl) ⟨387285, by rfl⟩ : syracuseStep 1032761 = 774571) B774571
theorem B3916349 : Blo 686314 3916349 := bstep (se 3 (by rfl) ⟨734315, by rfl⟩ : syracuseStep 3916349 = 1468631) B1468631
theorem B5653111 : Blo 686314 5653111 := bstep (se 1 (by rfl) ⟨4239833, by rfl⟩ : syracuseStep 5653111 = 8479667) B8479667
theorem B1032839 : Blo 686314 1032839 := bstep (se 1 (by rfl) ⟨774629, by rfl⟩ : syracuseStep 1032839 = 1549259) B1549259
theorem B1032875 : Blo 686314 1032875 := bstep (se 1 (by rfl) ⟨774656, by rfl⟩ : syracuseStep 1032875 = 1549313) B1549313
theorem B8372929 : Blo 686314 8372929 := bstep (se 2 (by rfl) ⟨3139848, by rfl⟩ : syracuseStep 8372929 = 6279697) B6279697
theorem B1032905 : Blo 686314 1032905 := bstep (se 2 (by rfl) ⟨387339, by rfl⟩ : syracuseStep 1032905 = 774679) B774679
theorem B1033019 : Blo 686314 1033019 := bstep (se 1 (by rfl) ⟨774764, by rfl⟩ : syracuseStep 1033019 = 1549529) B1549529
theorem B1164091 : Blo 686314 1164091 := bstep (se 1 (by rfl) ⟨873068, by rfl⟩ : syracuseStep 1164091 = 1746137) B1746137
theorem B1033079 : Blo 686314 1033079 := bstep (se 1 (by rfl) ⟨774809, by rfl⟩ : syracuseStep 1033079 = 1549619) B1549619
theorem B1033103 : Blo 686314 1033103 := bstep (se 1 (by rfl) ⟨774827, by rfl⟩ : syracuseStep 1033103 = 1549655) B1549655
theorem B2933657 : Blo 686314 2933657 := bstep (se 2 (by rfl) ⟨1100121, by rfl⟩ : syracuseStep 2933657 = 2200243) B2200243
theorem B1033145 : Blo 686314 1033145 := bstep (se 2 (by rfl) ⟨387429, by rfl⟩ : syracuseStep 1033145 = 774859) B774859
theorem B1164233 : Blo 686314 1164233 := bstep (se 2 (by rfl) ⟨436587, by rfl⟩ : syracuseStep 1164233 = 873175) B873175
theorem B869383 : Blo 686314 869383 := bstep (se 1 (by rfl) ⟨652037, by rfl⟩ : syracuseStep 869383 = 1304075) B1304075
theorem B1033223 : Blo 686314 1033223 := bstep (se 1 (by rfl) ⟨774917, by rfl⟩ : syracuseStep 1033223 = 1549835) B1549835
theorem B1983521 : Blo 686314 1983521 := bstep (se 2 (by rfl) ⟨743820, by rfl⟩ : syracuseStep 1983521 = 1487641) B1487641
theorem B1033259 : Blo 686314 1033259 := bstep (se 1 (by rfl) ⟨774944, by rfl⟩ : syracuseStep 1033259 = 1549889) B1549889
theorem B1033289 : Blo 686314 1033289 := bstep (se 2 (by rfl) ⟨387483, by rfl⟩ : syracuseStep 1033289 = 774967) B774967
theorem B1033403 : Blo 686314 1033403 := bstep (se 1 (by rfl) ⟨775052, by rfl⟩ : syracuseStep 1033403 = 1550105) B1550105
theorem B1033463 : Blo 686314 1033463 := bstep (se 1 (by rfl) ⟨775097, by rfl⟩ : syracuseStep 1033463 = 1550195) B1550195
theorem B1033487 : Blo 686314 1033487 := bstep (se 1 (by rfl) ⟨775115, by rfl⟩ : syracuseStep 1033487 = 1550231) B1550231
theorem B1033529 : Blo 686314 1033529 := bstep (se 2 (by rfl) ⟨387573, by rfl⟩ : syracuseStep 1033529 = 775147) B775147
theorem B13419911 : Blo 686314 13419911 := bstep (se 1 (by rfl) ⟨10064933, by rfl⟩ : syracuseStep 13419911 = 20129867) B20129867
theorem B1033607 : Blo 686314 1033607 := bstep (se 1 (by rfl) ⟨775205, by rfl⟩ : syracuseStep 1033607 = 1550411) B1550411
theorem B1656217 : Blo 686314 1656217 := bstep (se 2 (by rfl) ⟨621081, by rfl⟩ : syracuseStep 1656217 = 1242163) B1242163
theorem B1033643 : Blo 686314 1033643 := bstep (se 1 (by rfl) ⟨775232, by rfl⟩ : syracuseStep 1033643 = 1550465) B1550465
theorem B1033673 : Blo 686314 1033673 := bstep (se 2 (by rfl) ⟨387627, by rfl⟩ : syracuseStep 1033673 = 775255) B775255
theorem B869879 : Blo 686314 869879 := bstep (se 1 (by rfl) ⟨652409, by rfl⟩ : syracuseStep 869879 = 1304819) B1304819
theorem B1033787 : Blo 686314 1033787 := bstep (se 1 (by rfl) ⟨775340, by rfl⟩ : syracuseStep 1033787 = 1550681) B1550681
theorem B1033847 : Blo 686314 1033847 := bstep (se 1 (by rfl) ⟨775385, by rfl⟩ : syracuseStep 1033847 = 1550771) B1550771
theorem B870031 : Blo 686314 870031 := bstep (se 1 (by rfl) ⟨652523, by rfl⟩ : syracuseStep 870031 = 1305047) B1305047
theorem B1033871 : Blo 686314 1033871 := bstep (se 1 (by rfl) ⟨775403, by rfl⟩ : syracuseStep 1033871 = 1550807) B1550807
theorem B1033913 : Blo 686314 1033913 := bstep (se 2 (by rfl) ⟨387717, by rfl⟩ : syracuseStep 1033913 = 775435) B775435
theorem B3491585 : Blo 686314 3491585 := bstep (se 2 (by rfl) ⟨1309344, by rfl⟩ : syracuseStep 3491585 = 2618689) B2618689
theorem B1033991 : Blo 686314 1033991 := bstep (se 1 (by rfl) ⟨775493, by rfl⟩ : syracuseStep 1033991 = 1550987) B1550987
theorem B1034027 : Blo 686314 1034027 := bstep (se 1 (by rfl) ⟨775520, by rfl⟩ : syracuseStep 1034027 = 1551041) B1551041
theorem B870203 : Blo 686314 870203 := bstep (se 1 (by rfl) ⟨652652, by rfl⟩ : syracuseStep 870203 = 1305305) B1305305
theorem B1034057 : Blo 686314 1034057 := bstep (se 2 (by rfl) ⟨387771, by rfl⟩ : syracuseStep 1034057 = 775543) B775543
theorem B1034171 : Blo 686314 1034171 := bstep (se 1 (by rfl) ⟨775628, by rfl⟩ : syracuseStep 1034171 = 1551257) B1551257
theorem B1034231 : Blo 686314 1034231 := bstep (se 1 (by rfl) ⟨775673, by rfl⟩ : syracuseStep 1034231 = 1551347) B1551347
theorem B1034255 : Blo 686314 1034255 := bstep (se 1 (by rfl) ⟨775691, by rfl⟩ : syracuseStep 1034255 = 1551383) B1551383
theorem B1034297 : Blo 686314 1034297 := bstep (se 2 (by rfl) ⟨387861, by rfl⟩ : syracuseStep 1034297 = 775723) B775723
theorem B772231 : Blo 686314 772231 := bstep (se 1 (by rfl) ⟨579173, by rfl⟩ : syracuseStep 772231 = 1158347) B1158347
theorem B1034375 : Blo 686314 1034375 := bstep (se 1 (by rfl) ⟨775781, by rfl⟩ : syracuseStep 1034375 = 1551563) B1551563
theorem B1034411 : Blo 686314 1034411 := bstep (se 1 (by rfl) ⟨775808, by rfl⟩ : syracuseStep 1034411 = 1551617) B1551617
theorem B1034441 : Blo 686314 1034441 := bstep (se 2 (by rfl) ⟨387915, by rfl⟩ : syracuseStep 1034441 = 775831) B775831
theorem B772411 : Blo 686314 772411 := bstep (se 1 (by rfl) ⟨579308, by rfl⟩ : syracuseStep 772411 = 1158617) B1158617
theorem B1034555 : Blo 686314 1034555 := bstep (se 1 (by rfl) ⟨775916, by rfl⟩ : syracuseStep 1034555 = 1551833) B1551833
theorem B1034615 : Blo 686314 1034615 := bstep (se 1 (by rfl) ⟨775961, by rfl⟩ : syracuseStep 1034615 = 1551923) B1551923
theorem B1034639 : Blo 686314 1034639 := bstep (se 1 (by rfl) ⟨775979, by rfl⟩ : syracuseStep 1034639 = 1551959) B1551959
theorem B1395091 : Blo 686314 1395091 := bstep (se 1 (by rfl) ⟨1046318, by rfl⟩ : syracuseStep 1395091 = 2092637) B2092637
theorem B1034681 : Blo 686314 1034681 := bstep (se 2 (by rfl) ⟨388005, by rfl⟩ : syracuseStep 1034681 = 776011) B776011
theorem B4704733 : Blo 686314 4704733 := bstep (se 3 (by rfl) ⟨882137, by rfl⟩ : syracuseStep 4704733 = 1764275) B1764275
theorem B1034759 : Blo 686314 1034759 := bstep (se 1 (by rfl) ⟨776069, by rfl⟩ : syracuseStep 1034759 = 1552139) B1552139
theorem B3492395 : Blo 686314 3492395 := bstep (se 1 (by rfl) ⟨2619296, by rfl⟩ : syracuseStep 3492395 = 5238593) B5238593
theorem B1034795 : Blo 686314 1034795 := bstep (se 1 (by rfl) ⟨776096, by rfl⟩ : syracuseStep 1034795 = 1552193) B1552193
theorem B7817795 : Blo 686314 7817795 := bstep (se 1 (by rfl) ⟨5863346, by rfl⟩ : syracuseStep 7817795 = 11726693) B11726693
theorem B1034825 : Blo 686314 1034825 := bstep (se 2 (by rfl) ⟨388059, by rfl⟩ : syracuseStep 1034825 = 776119) B776119
theorem B9423479 : Blo 686314 9423479 := bstep (se 1 (by rfl) ⟨7067609, by rfl⟩ : syracuseStep 9423479 = 14135219) B14135219
theorem B1034939 : Blo 686314 1034939 := bstep (se 1 (by rfl) ⟨776204, by rfl⟩ : syracuseStep 1034939 = 1552409) B1552409
theorem B1034999 : Blo 686314 1034999 := bstep (se 1 (by rfl) ⟨776249, by rfl⟩ : syracuseStep 1034999 = 1552499) B1552499
theorem B871175 : Blo 686314 871175 := bstep (se 1 (by rfl) ⟨653381, by rfl⟩ : syracuseStep 871175 = 1306763) B1306763
theorem B7424783 : Blo 686314 7424783 := bstep (se 1 (by rfl) ⟨5568587, by rfl⟩ : syracuseStep 7424783 = 11137175) B11137175
theorem B772879 : Blo 686314 772879 := bstep (se 1 (by rfl) ⟨579659, by rfl⟩ : syracuseStep 772879 = 1159319) B1159319
theorem B1035023 : Blo 686314 1035023 := bstep (se 1 (by rfl) ⟨776267, by rfl⟩ : syracuseStep 1035023 = 1552535) B1552535
theorem B1035065 : Blo 686314 1035065 := bstep (se 2 (by rfl) ⟨388149, by rfl⟩ : syracuseStep 1035065 = 776299) B776299
theorem B1100603 : Blo 686314 1100603 := bstep (se 1 (by rfl) ⟨825452, by rfl⟩ : syracuseStep 1100603 = 1650905) B1650905
theorem B1035143 : Blo 686314 1035143 := bstep (se 1 (by rfl) ⟨776357, by rfl⟩ : syracuseStep 1035143 = 1552715) B1552715
theorem B3918739 : Blo 686314 3918739 := bstep (se 1 (by rfl) ⟨2939054, by rfl⟩ : syracuseStep 3918739 = 5878109) B5878109
theorem B1035179 : Blo 686314 1035179 := bstep (se 1 (by rfl) ⟨776384, by rfl⟩ : syracuseStep 1035179 = 1552769) B1552769
theorem B1035209 : Blo 686314 1035209 := bstep (se 2 (by rfl) ⟨388203, by rfl⟩ : syracuseStep 1035209 = 776407) B776407
theorem B1035323 : Blo 686314 1035323 := bstep (se 1 (by rfl) ⟨776492, by rfl⟩ : syracuseStep 1035323 = 1552985) B1552985
theorem B1035383 : Blo 686314 1035383 := bstep (se 1 (by rfl) ⟨776537, by rfl⟩ : syracuseStep 1035383 = 1553075) B1553075
theorem B1035407 : Blo 686314 1035407 := bstep (se 1 (by rfl) ⟨776555, by rfl⟩ : syracuseStep 1035407 = 1553111) B1553111
theorem B1035449 : Blo 686314 1035449 := bstep (se 2 (by rfl) ⟨388293, by rfl⟩ : syracuseStep 1035449 = 776587) B776587
theorem B773383 : Blo 686314 773383 := bstep (se 1 (by rfl) ⟨580037, by rfl⟩ : syracuseStep 773383 = 1160075) B1160075
theorem B11783555 : Blo 686314 11783555 := bstep (se 1 (by rfl) ⟨8837666, by rfl⟩ : syracuseStep 11783555 = 17675333) B17675333
theorem B871823 : Blo 686314 871823 := bstep (se 1 (by rfl) ⟨653867, by rfl⟩ : syracuseStep 871823 = 1307735) B1307735
theorem B773563 : Blo 686314 773563 := bstep (se 1 (by rfl) ⟨580172, by rfl⟩ : syracuseStep 773563 = 1160345) B1160345
theorem B9915857 : Blo 686314 9915857 := bstep (se 2 (by rfl) ⟨3718446, by rfl⟩ : syracuseStep 9915857 = 7436893) B7436893
theorem B2608955 : Blo 686314 2608955 := bstep (se 1 (by rfl) ⟨1956716, by rfl⟩ : syracuseStep 2608955 = 3913433) B3913433
theorem B3493691 : Blo 686314 3493691 := bstep (se 1 (by rfl) ⟨2620268, by rfl⟩ : syracuseStep 3493691 = 5240537) B5240537
theorem B774031 : Blo 686314 774031 := bstep (se 1 (by rfl) ⟨580523, by rfl⟩ : syracuseStep 774031 = 1161047) B1161047
theorem B3493853 : Blo 686314 3493853 := bstep (se 3 (by rfl) ⟨655097, by rfl⟩ : syracuseStep 3493853 = 1310195) B1310195
theorem B2609441 : Blo 686314 2609441 := bstep (se 2 (by rfl) ⟨978540, by rfl⟩ : syracuseStep 2609441 = 1957081) B1957081
theorem B3494177 : Blo 686314 3494177 := bstep (se 2 (by rfl) ⟨1310316, by rfl⟩ : syracuseStep 3494177 = 2620633) B2620633
theorem B774535 : Blo 686314 774535 := bstep (se 1 (by rfl) ⟨580901, by rfl⟩ : syracuseStep 774535 = 1161803) B1161803
theorem B7066061 : Blo 686314 7066061 := bstep (se 3 (by rfl) ⟨1324886, by rfl⟩ : syracuseStep 7066061 = 2649773) B2649773
theorem B1102351 : Blo 686314 1102351 := bstep (se 1 (by rfl) ⟨826763, by rfl⟩ : syracuseStep 1102351 = 1653527) B1653527
theorem B774715 : Blo 686314 774715 := bstep (se 1 (by rfl) ⟨581036, by rfl⟩ : syracuseStep 774715 = 1162073) B1162073
theorem B3920471 : Blo 686314 3920471 := bstep (se 1 (by rfl) ⟨2940353, by rfl⟩ : syracuseStep 3920471 = 5880707) B5880707
theorem B1954439 : Blo 686314 1954439 := bstep (se 1 (by rfl) ⟨1465829, by rfl⟩ : syracuseStep 1954439 = 2931659) B2931659
theorem B11195171 : Blo 686314 11195171 := bstep (se 1 (by rfl) ⟨8396378, by rfl⟩ : syracuseStep 11195171 = 16792757) B16792757
theorem B1856315 : Blo 686314 1856315 := bstep (se 1 (by rfl) ⟨1392236, by rfl⟩ : syracuseStep 1856315 = 2784473) B2784473
theorem B2937809 : Blo 686314 2937809 := bstep (se 2 (by rfl) ⟨1101678, by rfl⟩ : syracuseStep 2937809 = 2203357) B2203357
theorem B775183 : Blo 686314 775183 := bstep (se 1 (by rfl) ⟨581387, by rfl⟩ : syracuseStep 775183 = 1162775) B1162775
theorem B5231789 : Blo 686314 5231789 := bstep (se 3 (by rfl) ⟨980960, by rfl⟩ : syracuseStep 5231789 = 1961921) B1961921
theorem B2610413 : Blo 686314 2610413 := bstep (se 3 (by rfl) ⟨489452, by rfl⟩ : syracuseStep 2610413 = 978905) B978905
theorem B1955087 : Blo 686314 1955087 := bstep (se 1 (by rfl) ⟨1466315, by rfl⟩ : syracuseStep 1955087 = 2932631) B2932631
theorem B775687 : Blo 686314 775687 := bstep (se 1 (by rfl) ⟨581765, by rfl⟩ : syracuseStep 775687 = 1163531) B1163531
theorem B2610731 : Blo 686314 2610731 := bstep (se 1 (by rfl) ⟨1958048, by rfl⟩ : syracuseStep 2610731 = 3916097) B3916097
theorem B775867 : Blo 686314 775867 := bstep (se 1 (by rfl) ⟨581900, by rfl⟩ : syracuseStep 775867 = 1163801) B1163801
theorem B1103735 : Blo 686314 1103735 := bstep (se 1 (by rfl) ⟨827801, by rfl⟩ : syracuseStep 1103735 = 1655603) B1655603
theorem B776335 : Blo 686314 776335 := bstep (se 1 (by rfl) ⟨582251, by rfl⟩ : syracuseStep 776335 = 1164503) B1164503
theorem B2316545 : Blo 686314 2316545 := bstep (se 2 (by rfl) ⟨868704, by rfl⟩ : syracuseStep 2316545 = 1737409) B1737409
theorem B3725777 : Blo 686314 3725777 := bstep (se 2 (by rfl) ⟨1397166, by rfl⟩ : syracuseStep 3725777 = 2794333) B2794333
theorem B1858315 : Blo 686314 1858315 := bstep (se 1 (by rfl) ⟨1393736, by rfl⟩ : syracuseStep 1858315 = 2787473) B2787473
theorem B1104683 : Blo 686314 1104683 := bstep (se 1 (by rfl) ⟨828512, by rfl⟩ : syracuseStep 1104683 = 1657025) B1657025
theorem B6282035 : Blo 686314 6282035 := bstep (se 1 (by rfl) ⟨4711526, by rfl⟩ : syracuseStep 6282035 = 9423053) B9423053
theorem B7822169 : Blo 686314 7822169 := bstep (se 2 (by rfl) ⟨2933313, by rfl⟩ : syracuseStep 7822169 = 5866627) B5866627
theorem B1956727 : Blo 686314 1956727 := bstep (se 1 (by rfl) ⟨1467545, by rfl⟩ : syracuseStep 1956727 = 2935091) B2935091
theorem B2317355 : Blo 686314 2317355 := bstep (se 1 (by rfl) ⟨1738016, by rfl⟩ : syracuseStep 2317355 = 3476033) B3476033
theorem B1989917 : Blo 686314 1989917 := bstep (se 3 (by rfl) ⟨373109, by rfl⟩ : syracuseStep 1989917 = 746219) B746219
theorem B4185395 : Blo 686314 4185395 := bstep (se 1 (by rfl) ⟨3139046, by rfl⟩ : syracuseStep 4185395 = 6278093) B6278093
theorem B5234219 : Blo 686314 5234219 := bstep (se 1 (by rfl) ⟨3925664, by rfl⟩ : syracuseStep 5234219 = 7851329) B7851329
theorem B1466171 : Blo 686314 1466171 := bstep (se 1 (by rfl) ⟨1099628, by rfl⟩ : syracuseStep 1466171 = 2199257) B2199257
theorem B2940731 : Blo 686314 2940731 := bstep (se 1 (by rfl) ⟨2205548, by rfl⟩ : syracuseStep 2940731 = 4411097) B4411097
theorem B7430231 : Blo 686314 7430231 := bstep (se 1 (by rfl) ⟨5572673, by rfl⟩ : syracuseStep 7430231 = 11145347) B11145347
theorem B1958003 : Blo 686314 1958003 := bstep (se 1 (by rfl) ⟨1468502, by rfl⟩ : syracuseStep 1958003 = 2937005) B2937005
theorem B1859699 : Blo 686314 1859699 := bstep (se 1 (by rfl) ⟨1394774, by rfl⟩ : syracuseStep 1859699 = 2789549) B2789549
theorem B4907141 : Blo 686314 4907141 := bstep (se 4 (by rfl) ⟨460044, by rfl⟩ : syracuseStep 4907141 = 920089) B920089
theorem B2318651 : Blo 686314 2318651 := bstep (se 1 (by rfl) ⟨1738988, by rfl⟩ : syracuseStep 2318651 = 3477977) B3477977
theorem B1958231 : Blo 686314 1958231 := bstep (se 1 (by rfl) ⟨1468673, by rfl⟩ : syracuseStep 1958231 = 2937347) B2937347
theorem B1466743 : Blo 686314 1466743 := bstep (se 1 (by rfl) ⟨1100057, by rfl⟩ : syracuseStep 1466743 = 2200115) B2200115
theorem B2646539 : Blo 686314 2646539 := bstep (se 1 (by rfl) ⟨1984904, by rfl⟩ : syracuseStep 2646539 = 3969809) B3969809
theorem B1466923 : Blo 686314 1466923 := bstep (se 1 (by rfl) ⟨1100192, by rfl⟩ : syracuseStep 1466923 = 2200385) B2200385
theorem B13263425 : Blo 686314 13263425 := bstep (se 2 (by rfl) ⟨4973784, by rfl⟩ : syracuseStep 13263425 = 9947569) B9947569
theorem B1466999 : Blo 686314 1466999 := bstep (se 1 (by rfl) ⟨1100249, by rfl⟩ : syracuseStep 1466999 = 2200499) B2200499
theorem B2319137 : Blo 686314 2319137 := bstep (se 2 (by rfl) ⟨869676, by rfl⟩ : syracuseStep 2319137 = 1739353) B1739353
theorem B1860499 : Blo 686314 1860499 := bstep (se 1 (by rfl) ⟨1395374, by rfl⟩ : syracuseStep 1860499 = 2790749) B2790749
theorem B2614301 : Blo 686314 2614301 := bstep (se 3 (by rfl) ⟨490181, by rfl⟩ : syracuseStep 2614301 = 980363) B980363
theorem B2614315 : Blo 686314 2614315 := bstep (se 1 (by rfl) ⟨1960736, by rfl⟩ : syracuseStep 2614315 = 3921473) B3921473
theorem B1860727 : Blo 686314 1860727 := bstep (se 1 (by rfl) ⟨1395545, by rfl⟩ : syracuseStep 1860727 = 2791091) B2791091
theorem B9921851 : Blo 686314 9921851 := bstep (se 1 (by rfl) ⟨7441388, by rfl⟩ : syracuseStep 9921851 = 14882777) B14882777
theorem B2319731 : Blo 686314 2319731 := bstep (se 1 (by rfl) ⟨1739798, by rfl⟩ : syracuseStep 2319731 = 3479597) B3479597
theorem B8807939 : Blo 686314 8807939 := bstep (se 1 (by rfl) ⟨6605954, by rfl⟩ : syracuseStep 8807939 = 13211909) B13211909
theorem B14116355 : Blo 686314 14116355 := bstep (se 1 (by rfl) ⟨10587266, by rfl⟩ : syracuseStep 14116355 = 21174533) B21174533
theorem B2942507 : Blo 686314 2942507 := bstep (se 1 (by rfl) ⟨2206880, by rfl⟩ : syracuseStep 2942507 = 4413761) B4413761
theorem B5596715 : Blo 686314 5596715 := bstep (se 1 (by rfl) ⟨4197536, by rfl⟩ : syracuseStep 5596715 = 8395073) B8395073
theorem B1861255 : Blo 686314 1861255 := bstep (se 1 (by rfl) ⟨1395941, by rfl⟩ : syracuseStep 1861255 = 2791883) B2791883
theorem B1304363 : Blo 686314 1304363 := bstep (se 1 (by rfl) ⟨978272, by rfl⟩ : syracuseStep 1304363 = 1956545) B1956545
theorem B2484083 : Blo 686314 2484083 := bstep (se 1 (by rfl) ⟨1863062, by rfl⟩ : syracuseStep 2484083 = 3726125) B3726125
theorem B1959815 : Blo 686314 1959815 := bstep (se 1 (by rfl) ⟨1469861, by rfl⟩ : syracuseStep 1959815 = 2939723) B2939723
theorem B1959997 : Blo 686314 1959997 := bstep (se 3 (by rfl) ⟨367499, by rfl⟩ : syracuseStep 1959997 = 734999) B734999
theorem B1763785 : Blo 686314 1763785 := bstep (se 2 (by rfl) ⟨661419, by rfl⟩ : syracuseStep 1763785 = 1322839) B1322839
theorem B1960463 : Blo 686314 1960463 := bstep (se 1 (by rfl) ⟨1470347, by rfl⟩ : syracuseStep 1960463 = 2940695) B2940695
theorem B3926987 : Blo 686314 3926987 := bstep (se 1 (by rfl) ⟨2945240, by rfl⟩ : syracuseStep 3926987 = 5890481) B5890481
theorem B7433603 : Blo 686314 7433603 := bstep (se 1 (by rfl) ⟨5575202, by rfl⟩ : syracuseStep 7433603 = 11150405) B11150405
theorem B1306057 : Blo 686314 1306057 := bstep (se 2 (by rfl) ⟨489771, by rfl⟩ : syracuseStep 1306057 = 979543) B979543
theorem B3534283 : Blo 686314 3534283 := bstep (se 1 (by rfl) ⟨2650712, by rfl⟩ : syracuseStep 3534283 = 5301425) B5301425
theorem B1961729 : Blo 686314 1961729 := bstep (se 2 (by rfl) ⟨735648, by rfl⟩ : syracuseStep 1961729 = 1471297) B1471297
theorem B2322323 : Blo 686314 2322323 := bstep (se 1 (by rfl) ⟨1741742, by rfl⟩ : syracuseStep 2322323 = 3483485) B3483485
theorem B979771 : Blo 686314 979771 := bstep (se 1 (by rfl) ⟨734828, by rfl⟩ : syracuseStep 979771 = 1469657) B1469657
theorem B90273005 : Blo 686314 90273005 := bstep (se 3 (by rfl) ⟨16926188, by rfl⟩ : syracuseStep 90273005 = 33852377) B33852377
theorem B2323727 : Blo 686314 2323727 := bstep (se 1 (by rfl) ⟨1742795, by rfl⟩ : syracuseStep 2323727 = 3485591) B3485591
theorem B11171105 : Blo 686314 11171105 := bstep (se 2 (by rfl) ⟨4189164, by rfl⟩ : syracuseStep 11171105 = 8378329) B8378329
theorem B1307963 : Blo 686314 1307963 := bstep (se 1 (by rfl) ⟨980972, by rfl⟩ : syracuseStep 1307963 = 1961945) B1961945
theorem B1963379 : Blo 686314 1963379 := bstep (se 1 (by rfl) ⟨1472534, by rfl⟩ : syracuseStep 1963379 = 2945069) B2945069
theorem B3306899 : Blo 686314 3306899 := bstep (se 1 (by rfl) ⟨2480174, by rfl⟩ : syracuseStep 3306899 = 4960349) B4960349
theorem B980471 : Blo 686314 980471 := bstep (se 1 (by rfl) ⟨735353, by rfl⟩ : syracuseStep 980471 = 1470707) B1470707
theorem B2323997 : Blo 686314 2323997 := bstep (se 3 (by rfl) ⟨435749, by rfl⟩ : syracuseStep 2323997 = 871499) B871499
theorem B7927415 : Blo 686314 7927415 := bstep (se 1 (by rfl) ⟨5945561, by rfl⟩ : syracuseStep 7927415 = 11891123) B11891123
theorem B1472185 : Blo 686314 1472185 := bstep (se 2 (by rfl) ⟨552069, by rfl⟩ : syracuseStep 1472185 = 1104139) B1104139
theorem B1308449 : Blo 686314 1308449 := bstep (se 2 (by rfl) ⟨490668, by rfl⟩ : syracuseStep 1308449 = 981337) B981337
theorem B1963835 : Blo 686314 1963835 := bstep (se 1 (by rfl) ⟨1472876, by rfl⟩ : syracuseStep 1963835 = 2945753) B2945753
theorem B33552407 : Blo 686314 33552407 := bstep (se 1 (by rfl) ⟨25164305, by rfl⟩ : syracuseStep 33552407 = 50328611) B50328611
theorem B8353853 : Blo 686314 8353853 := bstep (se 3 (by rfl) ⟨1566347, by rfl⟩ : syracuseStep 8353853 = 3132695) B3132695
theorem B2619479 : Blo 686314 2619479 := bstep (se 1 (by rfl) ⟨1964609, by rfl⟩ : syracuseStep 2619479 = 3929219) B3929219
theorem B1308791 : Blo 686314 1308791 := bstep (se 1 (by rfl) ⟨981593, by rfl⟩ : syracuseStep 1308791 = 1963187) B1963187
theorem B16152817 : Blo 686314 16152817 := bstep (se 2 (by rfl) ⟨6057306, by rfl⟩ : syracuseStep 16152817 = 12114613) B12114613
theorem B686343 : Blo 686314 686343 := bstep (se 1 (by rfl) ⟨514757, by rfl⟩ : syracuseStep 686343 = 1029515) B1029515
theorem B686351 : Blo 686314 686351 := bstep (se 1 (by rfl) ⟨514763, by rfl⟩ : syracuseStep 686351 = 1029527) B1029527
theorem B686395 : Blo 686314 686395 := bstep (se 1 (by rfl) ⟨514796, by rfl⟩ : syracuseStep 686395 = 1029593) B1029593
theorem B686471 : Blo 686314 686471 := bstep (se 1 (by rfl) ⟨514853, by rfl⟩ : syracuseStep 686471 = 1029707) B1029707
theorem B686479 : Blo 686314 686479 := bstep (se 1 (by rfl) ⟨514859, by rfl⟩ : syracuseStep 686479 = 1029719) B1029719
theorem B1767827 : Blo 686314 1767827 := bstep (se 1 (by rfl) ⟨1325870, by rfl⟩ : syracuseStep 1767827 = 2651741) B2651741
theorem B686523 : Blo 686314 686523 := bstep (se 1 (by rfl) ⟨514892, by rfl⟩ : syracuseStep 686523 = 1029785) B1029785
theorem B686599 : Blo 686314 686599 := bstep (se 1 (by rfl) ⟨514949, by rfl⟩ : syracuseStep 686599 = 1029899) B1029899
theorem B686607 : Blo 686314 686607 := bstep (se 1 (by rfl) ⟨514955, by rfl⟩ : syracuseStep 686607 = 1029911) B1029911
theorem B1964587 : Blo 686314 1964587 := bstep (se 1 (by rfl) ⟨1473440, by rfl⟩ : syracuseStep 1964587 = 2946881) B2946881
theorem B686651 : Blo 686314 686651 := bstep (se 1 (by rfl) ⟨514988, by rfl⟩ : syracuseStep 686651 = 1029977) B1029977
theorem B2619965 : Blo 686314 2619965 := bstep (se 3 (by rfl) ⟨491243, by rfl⟩ : syracuseStep 2619965 = 982487) B982487
theorem B686727 : Blo 686314 686727 := bstep (se 1 (by rfl) ⟨515045, by rfl⟩ : syracuseStep 686727 = 1030091) B1030091
theorem B686735 : Blo 686314 686735 := bstep (se 1 (by rfl) ⟨515051, by rfl⟩ : syracuseStep 686735 = 1030103) B1030103
theorem B686779 : Blo 686314 686779 := bstep (se 1 (by rfl) ⟨515084, by rfl⟩ : syracuseStep 686779 = 1030169) B1030169
theorem B3537665 : Blo 686314 3537665 := bstep (se 2 (by rfl) ⟨1326624, by rfl⟩ : syracuseStep 3537665 = 2653249) B2653249
theorem B686855 : Blo 686314 686855 := bstep (se 1 (by rfl) ⟨515141, by rfl⟩ : syracuseStep 686855 = 1030283) B1030283
theorem B686863 : Blo 686314 686863 := bstep (se 1 (by rfl) ⟨515147, by rfl⟩ : syracuseStep 686863 = 1030295) B1030295
theorem B7535375 : Blo 686314 7535375 := bstep (se 1 (by rfl) ⟨5651531, by rfl⟩ : syracuseStep 7535375 = 11303063) B11303063
theorem B14875427 : Blo 686314 14875427 := bstep (se 1 (by rfl) ⟨11156570, by rfl⟩ : syracuseStep 14875427 = 22313141) B22313141
theorem B686907 : Blo 686314 686907 := bstep (se 1 (by rfl) ⟨515180, by rfl⟩ : syracuseStep 686907 = 1030361) B1030361
theorem B1964861 : Blo 686314 1964861 := bstep (se 3 (by rfl) ⟨368411, by rfl⟩ : syracuseStep 1964861 = 736823) B736823
theorem B686983 : Blo 686314 686983 := bstep (se 1 (by rfl) ⟨515237, by rfl⟩ : syracuseStep 686983 = 1030475) B1030475
theorem B981895 : Blo 686314 981895 := bstep (se 1 (by rfl) ⟨736421, by rfl⟩ : syracuseStep 981895 = 1472843) B1472843
theorem B686991 : Blo 686314 686991 := bstep (se 1 (by rfl) ⟨515243, by rfl⟩ : syracuseStep 686991 = 1030487) B1030487
theorem B2325401 : Blo 686314 2325401 := bstep (se 2 (by rfl) ⟨872025, by rfl⟩ : syracuseStep 2325401 = 1744051) B1744051
theorem B687035 : Blo 686314 687035 := bstep (se 1 (by rfl) ⟨515276, by rfl⟩ : syracuseStep 687035 = 1030553) B1030553
theorem B687111 : Blo 686314 687111 := bstep (se 1 (by rfl) ⟨515333, by rfl⟩ : syracuseStep 687111 = 1030667) B1030667
theorem B687119 : Blo 686314 687119 := bstep (se 1 (by rfl) ⟨515339, by rfl⟩ : syracuseStep 687119 = 1030679) B1030679
theorem B687163 : Blo 686314 687163 := bstep (se 1 (by rfl) ⟨515372, by rfl⟩ : syracuseStep 687163 = 1030745) B1030745
theorem B687239 : Blo 686314 687239 := bstep (se 1 (by rfl) ⟨515429, by rfl⟩ : syracuseStep 687239 = 1030859) B1030859
theorem B687247 : Blo 686314 687247 := bstep (se 1 (by rfl) ⟨515435, by rfl⟩ : syracuseStep 687247 = 1030871) B1030871
theorem B1571987 : Blo 686314 1571987 := bstep (se 1 (by rfl) ⟨1178990, by rfl⟩ : syracuseStep 1571987 = 2357981) B2357981
theorem B687291 : Blo 686314 687291 := bstep (se 1 (by rfl) ⟨515468, by rfl⟩ : syracuseStep 687291 = 1030937) B1030937
theorem B687367 : Blo 686314 687367 := bstep (se 1 (by rfl) ⟨515525, by rfl⟩ : syracuseStep 687367 = 1031051) B1031051
theorem B687375 : Blo 686314 687375 := bstep (se 1 (by rfl) ⟨515531, by rfl⟩ : syracuseStep 687375 = 1031063) B1031063
theorem B687419 : Blo 686314 687419 := bstep (se 1 (by rfl) ⟨515564, by rfl⟩ : syracuseStep 687419 = 1031129) B1031129
theorem B1473851 : Blo 686314 1473851 := bstep (se 1 (by rfl) ⟨1105388, by rfl⟩ : syracuseStep 1473851 = 2210777) B2210777
theorem B1047881 : Blo 686314 1047881 := bstep (se 2 (by rfl) ⟨392955, by rfl⟩ : syracuseStep 1047881 = 785911) B785911
theorem B687495 : Blo 686314 687495 := bstep (se 1 (by rfl) ⟨515621, by rfl⟩ : syracuseStep 687495 = 1031243) B1031243
theorem B687503 : Blo 686314 687503 := bstep (se 1 (by rfl) ⟨515627, by rfl⟩ : syracuseStep 687503 = 1031255) B1031255
theorem B687547 : Blo 686314 687547 := bstep (se 1 (by rfl) ⟨515660, by rfl⟩ : syracuseStep 687547 = 1031321) B1031321
theorem B982459 : Blo 686314 982459 := bstep (se 1 (by rfl) ⟨736844, by rfl⟩ : syracuseStep 982459 = 1473689) B1473689
theorem B687623 : Blo 686314 687623 := bstep (se 1 (by rfl) ⟨515717, by rfl⟩ : syracuseStep 687623 = 1031435) B1031435
theorem B687631 : Blo 686314 687631 := bstep (se 1 (by rfl) ⟨515723, by rfl⟩ : syracuseStep 687631 = 1031447) B1031447
theorem B687675 : Blo 686314 687675 := bstep (se 1 (by rfl) ⟨515756, by rfl⟩ : syracuseStep 687675 = 1031513) B1031513
theorem B2326103 : Blo 686314 2326103 := bstep (se 1 (by rfl) ⟨1744577, by rfl⟩ : syracuseStep 2326103 = 3489155) B3489155
theorem B687751 : Blo 686314 687751 := bstep (se 1 (by rfl) ⟨515813, by rfl⟩ : syracuseStep 687751 = 1031627) B1031627
theorem B1965703 : Blo 686314 1965703 := bstep (se 1 (by rfl) ⟨1474277, by rfl⟩ : syracuseStep 1965703 = 2948555) B2948555
theorem B687759 : Blo 686314 687759 := bstep (se 1 (by rfl) ⟨515819, by rfl⟩ : syracuseStep 687759 = 1031639) B1031639
theorem B1310393 : Blo 686314 1310393 := bstep (se 2 (by rfl) ⟨491397, by rfl⟩ : syracuseStep 1310393 = 982795) B982795
theorem B687803 : Blo 686314 687803 := bstep (se 1 (by rfl) ⟨515852, by rfl⟩ : syracuseStep 687803 = 1031705) B1031705
theorem B687879 : Blo 686314 687879 := bstep (se 1 (by rfl) ⟨515909, by rfl⟩ : syracuseStep 687879 = 1031819) B1031819
theorem B687887 : Blo 686314 687887 := bstep (se 1 (by rfl) ⟨515915, by rfl⟩ : syracuseStep 687887 = 1031831) B1031831
theorem B2096929 : Blo 686314 2096929 := bstep (se 2 (by rfl) ⟨786348, by rfl⟩ : syracuseStep 2096929 = 1572697) B1572697
theorem B687931 : Blo 686314 687931 := bstep (se 1 (by rfl) ⟨515948, by rfl⟩ : syracuseStep 687931 = 1031897) B1031897
theorem B688007 : Blo 686314 688007 := bstep (se 1 (by rfl) ⟨516005, by rfl⟩ : syracuseStep 688007 = 1032011) B1032011
theorem B688015 : Blo 686314 688015 := bstep (se 1 (by rfl) ⟨516011, by rfl⟩ : syracuseStep 688015 = 1032023) B1032023
theorem B688059 : Blo 686314 688059 := bstep (se 1 (by rfl) ⟨516044, by rfl⟩ : syracuseStep 688059 = 1032089) B1032089
theorem B2326535 : Blo 686314 2326535 := bstep (se 1 (by rfl) ⟨1744901, by rfl⟩ : syracuseStep 2326535 = 3489803) B3489803
theorem B688167 : Blo 686314 688167 := bstep (se 1 (by rfl) ⟨516125, by rfl⟩ : syracuseStep 688167 = 1032251) B1032251
theorem B688207 : Blo 686314 688207 := bstep (se 1 (by rfl) ⟨516155, by rfl⟩ : syracuseStep 688207 = 1032311) B1032311
theorem B688223 : Blo 686314 688223 := bstep (se 1 (by rfl) ⟨516167, by rfl⟩ : syracuseStep 688223 = 1032335) B1032335
theorem B2326643 : Blo 686314 2326643 := bstep (se 1 (by rfl) ⟨1744982, by rfl⟩ : syracuseStep 2326643 = 3489965) B3489965
theorem B688251 : Blo 686314 688251 := bstep (se 1 (by rfl) ⟨516188, by rfl⟩ : syracuseStep 688251 = 1032377) B1032377
theorem B688303 : Blo 686314 688303 := bstep (se 1 (by rfl) ⟨516227, by rfl⟩ : syracuseStep 688303 = 1032455) B1032455
theorem B688327 : Blo 686314 688327 := bstep (se 1 (by rfl) ⟨516245, by rfl⟩ : syracuseStep 688327 = 1032491) B1032491
theorem B688347 : Blo 686314 688347 := bstep (se 1 (by rfl) ⟨516260, by rfl⟩ : syracuseStep 688347 = 1032521) B1032521
theorem B688423 : Blo 686314 688423 := bstep (se 1 (by rfl) ⟨516317, by rfl⟩ : syracuseStep 688423 = 1032635) B1032635
theorem B688463 : Blo 686314 688463 := bstep (se 1 (by rfl) ⟨516347, by rfl⟩ : syracuseStep 688463 = 1032695) B1032695
theorem B688479 : Blo 686314 688479 := bstep (se 1 (by rfl) ⟨516359, by rfl⟩ : syracuseStep 688479 = 1032719) B1032719
theorem B688507 : Blo 686314 688507 := bstep (se 1 (by rfl) ⟨516380, by rfl⟩ : syracuseStep 688507 = 1032761) B1032761
theorem B2326913 : Blo 686314 2326913 := bstep (se 2 (by rfl) ⟨872592, by rfl⟩ : syracuseStep 2326913 = 1745185) B1745185
theorem B688559 : Blo 686314 688559 := bstep (se 1 (by rfl) ⟨516419, by rfl⟩ : syracuseStep 688559 = 1032839) B1032839
theorem B688583 : Blo 686314 688583 := bstep (se 1 (by rfl) ⟨516437, by rfl⟩ : syracuseStep 688583 = 1032875) B1032875
theorem B688603 : Blo 686314 688603 := bstep (se 1 (by rfl) ⟨516452, by rfl⟩ : syracuseStep 688603 = 1032905) B1032905
theorem B688679 : Blo 686314 688679 := bstep (se 1 (by rfl) ⟨516509, by rfl⟩ : syracuseStep 688679 = 1033019) B1033019
theorem B688719 : Blo 686314 688719 := bstep (se 1 (by rfl) ⟨516539, by rfl⟩ : syracuseStep 688719 = 1033079) B1033079
theorem B688735 : Blo 686314 688735 := bstep (se 1 (by rfl) ⟨516551, by rfl⟩ : syracuseStep 688735 = 1033103) B1033103
theorem B688763 : Blo 686314 688763 := bstep (se 1 (by rfl) ⟨516572, by rfl⟩ : syracuseStep 688763 = 1033145) B1033145
theorem B2687627 : Blo 686314 2687627 := bstep (se 1 (by rfl) ⟨2015720, by rfl⟩ : syracuseStep 2687627 = 4031441) B4031441
theorem B688815 : Blo 686314 688815 := bstep (se 1 (by rfl) ⟨516611, by rfl⟩ : syracuseStep 688815 = 1033223) B1033223
theorem B688839 : Blo 686314 688839 := bstep (se 1 (by rfl) ⟨516629, by rfl⟩ : syracuseStep 688839 = 1033259) B1033259
theorem B688859 : Blo 686314 688859 := bstep (se 1 (by rfl) ⟨516644, by rfl⟩ : syracuseStep 688859 = 1033289) B1033289
theorem B688935 : Blo 686314 688935 := bstep (se 1 (by rfl) ⟨516701, by rfl⟩ : syracuseStep 688935 = 1033403) B1033403
theorem B7537481 : Blo 686314 7537481 := bstep (se 2 (by rfl) ⟨2826555, by rfl⟩ : syracuseStep 7537481 = 5653111) B5653111
theorem B688975 : Blo 686314 688975 := bstep (se 1 (by rfl) ⟨516731, by rfl⟩ : syracuseStep 688975 = 1033463) B1033463
theorem B688991 : Blo 686314 688991 := bstep (se 1 (by rfl) ⟨516743, by rfl⟩ : syracuseStep 688991 = 1033487) B1033487
theorem B689019 : Blo 686314 689019 := bstep (se 1 (by rfl) ⟨516764, by rfl⟩ : syracuseStep 689019 = 1033529) B1033529
theorem B1573793 : Blo 686314 1573793 := bstep (se 2 (by rfl) ⟨590172, by rfl⟩ : syracuseStep 1573793 = 1180345) B1180345
theorem B8946607 : Blo 686314 8946607 := bstep (se 1 (by rfl) ⟨6709955, by rfl⟩ : syracuseStep 8946607 = 13419911) B13419911
theorem B689071 : Blo 686314 689071 := bstep (se 1 (by rfl) ⟨516803, by rfl⟩ : syracuseStep 689071 = 1033607) B1033607
theorem B689095 : Blo 686314 689095 := bstep (se 1 (by rfl) ⟨516821, by rfl⟩ : syracuseStep 689095 = 1033643) B1033643
theorem B689115 : Blo 686314 689115 := bstep (se 1 (by rfl) ⟨516836, by rfl⟩ : syracuseStep 689115 = 1033673) B1033673
theorem B689191 : Blo 686314 689191 := bstep (se 1 (by rfl) ⟨516893, by rfl⟩ : syracuseStep 689191 = 1033787) B1033787
theorem B689231 : Blo 686314 689231 := bstep (se 1 (by rfl) ⟨516923, by rfl⟩ : syracuseStep 689231 = 1033847) B1033847
theorem B689247 : Blo 686314 689247 := bstep (se 1 (by rfl) ⟨516935, by rfl⟩ : syracuseStep 689247 = 1033871) B1033871
theorem B689275 : Blo 686314 689275 := bstep (se 1 (by rfl) ⟨516956, by rfl⟩ : syracuseStep 689275 = 1033913) B1033913
theorem B2655389 : Blo 686314 2655389 := bstep (se 3 (by rfl) ⟨497885, by rfl⟩ : syracuseStep 2655389 = 995771) B995771
theorem B2327723 : Blo 686314 2327723 := bstep (se 1 (by rfl) ⟨1745792, by rfl⟩ : syracuseStep 2327723 = 3491585) B3491585
theorem B689327 : Blo 686314 689327 := bstep (se 1 (by rfl) ⟨516995, by rfl⟩ : syracuseStep 689327 = 1033991) B1033991
theorem B689351 : Blo 686314 689351 := bstep (se 1 (by rfl) ⟨517013, by rfl⟩ : syracuseStep 689351 = 1034027) B1034027
theorem B689371 : Blo 686314 689371 := bstep (se 1 (by rfl) ⟨517028, by rfl⟩ : syracuseStep 689371 = 1034057) B1034057
theorem B689447 : Blo 686314 689447 := bstep (se 1 (by rfl) ⟨517085, by rfl⟩ : syracuseStep 689447 = 1034171) B1034171
theorem B689487 : Blo 686314 689487 := bstep (se 1 (by rfl) ⟨517115, by rfl⟩ : syracuseStep 689487 = 1034231) B1034231
theorem B689503 : Blo 686314 689503 := bstep (se 1 (by rfl) ⟨517127, by rfl⟩ : syracuseStep 689503 = 1034255) B1034255
theorem B689531 : Blo 686314 689531 := bstep (se 1 (by rfl) ⟨517148, by rfl⟩ : syracuseStep 689531 = 1034297) B1034297
theorem B4195709 : Blo 686314 4195709 := bstep (se 3 (by rfl) ⟨786695, by rfl⟩ : syracuseStep 4195709 = 1573391) B1573391
theorem B689583 : Blo 686314 689583 := bstep (se 1 (by rfl) ⟨517187, by rfl⟩ : syracuseStep 689583 = 1034375) B1034375
theorem B689607 : Blo 686314 689607 := bstep (se 1 (by rfl) ⟨517205, by rfl⟩ : syracuseStep 689607 = 1034411) B1034411
theorem B689627 : Blo 686314 689627 := bstep (se 1 (by rfl) ⟨517220, by rfl⟩ : syracuseStep 689627 = 1034441) B1034441
theorem B689703 : Blo 686314 689703 := bstep (se 1 (by rfl) ⟨517277, by rfl⟩ : syracuseStep 689703 = 1034555) B1034555
theorem B689743 : Blo 686314 689743 := bstep (se 1 (by rfl) ⟨517307, by rfl⟩ : syracuseStep 689743 = 1034615) B1034615
theorem B689759 : Blo 686314 689759 := bstep (se 1 (by rfl) ⟨517319, by rfl⟩ : syracuseStep 689759 = 1034639) B1034639
theorem B689787 : Blo 686314 689787 := bstep (se 1 (by rfl) ⟨517340, by rfl⟩ : syracuseStep 689787 = 1034681) B1034681
theorem B689839 : Blo 686314 689839 := bstep (se 1 (by rfl) ⟨517379, by rfl⟩ : syracuseStep 689839 = 1034759) B1034759
theorem B2328263 : Blo 686314 2328263 := bstep (se 1 (by rfl) ⟨1746197, by rfl⟩ : syracuseStep 2328263 = 3492395) B3492395
theorem B689863 : Blo 686314 689863 := bstep (se 1 (by rfl) ⟨517397, by rfl⟩ : syracuseStep 689863 = 1034795) B1034795
theorem B5211863 : Blo 686314 5211863 := bstep (se 1 (by rfl) ⟨3908897, by rfl⟩ : syracuseStep 5211863 = 7817795) B7817795
theorem B689883 : Blo 686314 689883 := bstep (se 1 (by rfl) ⟨517412, by rfl⟩ : syracuseStep 689883 = 1034825) B1034825
theorem B689959 : Blo 686314 689959 := bstep (se 1 (by rfl) ⟨517469, by rfl⟩ : syracuseStep 689959 = 1034939) B1034939
theorem B689999 : Blo 686314 689999 := bstep (se 1 (by rfl) ⟨517499, by rfl⟩ : syracuseStep 689999 = 1034999) B1034999
theorem B4949855 : Blo 686314 4949855 := bstep (se 1 (by rfl) ⟨3712391, by rfl⟩ : syracuseStep 4949855 = 7424783) B7424783
theorem B690015 : Blo 686314 690015 := bstep (se 1 (by rfl) ⟨517511, by rfl⟩ : syracuseStep 690015 = 1035023) B1035023
theorem B690043 : Blo 686314 690043 := bstep (se 1 (by rfl) ⟨517532, by rfl⟩ : syracuseStep 690043 = 1035065) B1035065
theorem B690095 : Blo 686314 690095 := bstep (se 1 (by rfl) ⟨517571, by rfl⟩ : syracuseStep 690095 = 1035143) B1035143
theorem B690119 : Blo 686314 690119 := bstep (se 1 (by rfl) ⟨517589, by rfl⟩ : syracuseStep 690119 = 1035179) B1035179
theorem B690139 : Blo 686314 690139 := bstep (se 1 (by rfl) ⟨517604, by rfl⟩ : syracuseStep 690139 = 1035209) B1035209
theorem B690215 : Blo 686314 690215 := bstep (se 1 (by rfl) ⟨517661, by rfl⟩ : syracuseStep 690215 = 1035323) B1035323
theorem B690255 : Blo 686314 690255 := bstep (se 1 (by rfl) ⟨517691, by rfl⟩ : syracuseStep 690255 = 1035383) B1035383
theorem B690271 : Blo 686314 690271 := bstep (se 1 (by rfl) ⟨517703, by rfl⟩ : syracuseStep 690271 = 1035407) B1035407
theorem B690299 : Blo 686314 690299 := bstep (se 1 (by rfl) ⟨517724, by rfl⟩ : syracuseStep 690299 = 1035449) B1035449
theorem B4950173 : Blo 686314 4950173 := bstep (se 3 (by rfl) ⟨928157, by rfl⟩ : syracuseStep 4950173 = 1856315) B1856315
theorem B1739303 : Blo 686314 1739303 := bstep (se 1 (by rfl) ⟨1304477, by rfl⟩ : syracuseStep 1739303 = 2608955) B2608955
theorem B2329127 : Blo 686314 2329127 := bstep (se 1 (by rfl) ⟨1746845, by rfl⟩ : syracuseStep 2329127 = 3493691) B3493691
theorem B2329235 : Blo 686314 2329235 := bstep (se 1 (by rfl) ⟨1746926, by rfl⟩ : syracuseStep 2329235 = 3493853) B3493853
theorem B1739627 : Blo 686314 1739627 := bstep (se 1 (by rfl) ⟨1304720, by rfl⟩ : syracuseStep 1739627 = 2609441) B2609441
theorem B2329451 : Blo 686314 2329451 := bstep (se 1 (by rfl) ⟨1747088, by rfl⟩ : syracuseStep 2329451 = 3494177) B3494177
theorem B2329505 : Blo 686314 2329505 := bstep (se 2 (by rfl) ⟨873564, by rfl⟩ : syracuseStep 2329505 = 1747129) B1747129
theorem B5573879 : Blo 686314 5573879 := bstep (se 1 (by rfl) ⟨4180409, by rfl⟩ : syracuseStep 5573879 = 8360819) B8360819
theorem B1740275 : Blo 686314 1740275 := bstep (se 1 (by rfl) ⟨1305206, by rfl⟩ : syracuseStep 1740275 = 2610413) B2610413
theorem B1740487 : Blo 686314 1740487 := bstep (se 1 (by rfl) ⟨1305365, by rfl⟩ : syracuseStep 1740487 = 2610731) B2610731
theorem B1544363 : Blo 686314 1544363 := bstep (se 1 (by rfl) ⟨1158272, by rfl⟩ : syracuseStep 1544363 = 2316545) B2316545
theorem B5214779 : Blo 686314 5214779 := bstep (se 1 (by rfl) ⟨3911084, by rfl⟩ : syracuseStep 5214779 = 7822169) B7822169
theorem B1741409 : Blo 686314 1741409 := bstep (se 2 (by rfl) ⟨653028, by rfl⟩ : syracuseStep 1741409 = 1306057) B1306057
theorem B1544903 : Blo 686314 1544903 := bstep (se 1 (by rfl) ⟨1158677, by rfl⟩ : syracuseStep 1544903 = 2317355) B2317355
theorem B3478301 : Blo 686314 3478301 := bstep (se 3 (by rfl) ⟨652181, by rfl⟩ : syracuseStep 3478301 = 1304363) B1304363
theorem B2790263 : Blo 686314 2790263 := bstep (se 1 (by rfl) ⟨2092697, by rfl⟩ : syracuseStep 2790263 = 4185395) B4185395
theorem B4953487 : Blo 686314 4953487 := bstep (se 1 (by rfl) ⟨3715115, by rfl⟩ : syracuseStep 4953487 = 7430231) B7430231
theorem B4953545 : Blo 686314 4953545 := bstep (se 2 (by rfl) ⟨1857579, by rfl⟩ : syracuseStep 4953545 = 3715159) B3715159
theorem B1545767 : Blo 686314 1545767 := bstep (se 1 (by rfl) ⟨1159325, by rfl⟩ : syracuseStep 1545767 = 2318651) B2318651
theorem B4953889 : Blo 686314 4953889 := bstep (se 2 (by rfl) ⟨1857708, by rfl⟩ : syracuseStep 4953889 = 3715417) B3715417
theorem B1546091 : Blo 686314 1546091 := bstep (se 1 (by rfl) ⟨1159568, by rfl⟩ : syracuseStep 1546091 = 2319137) B2319137
theorem B1546145 : Blo 686314 1546145 := bstep (se 2 (by rfl) ⟨579804, by rfl⟩ : syracuseStep 1546145 = 1159609) B1159609
theorem B1742867 : Blo 686314 1742867 := bstep (se 1 (by rfl) ⟨1307150, by rfl⟩ : syracuseStep 1742867 = 2614301) B2614301
theorem B1546487 : Blo 686314 1546487 := bstep (se 1 (by rfl) ⟨1159865, by rfl⟩ : syracuseStep 1546487 = 2319731) B2319731
theorem B5871959 : Blo 686314 5871959 := bstep (se 1 (by rfl) ⟨4403969, by rfl⟩ : syracuseStep 5871959 = 8807939) B8807939
theorem B9410903 : Blo 686314 9410903 := bstep (se 1 (by rfl) ⟨7058177, by rfl⟩ : syracuseStep 9410903 = 14116355) B14116355
theorem B9935405 : Blo 686314 9935405 := bstep (se 3 (by rfl) ⟨1862888, by rfl⟩ : syracuseStep 9935405 = 3725777) B3725777
theorem B1547081 : Blo 686314 1547081 := bstep (se 2 (by rfl) ⟨580155, by rfl⟩ : syracuseStep 1547081 = 1160311) B1160311
theorem B5872985 : Blo 686314 5872985 := bstep (se 2 (by rfl) ⟨2202369, by rfl⟩ : syracuseStep 5872985 = 4404739) B4404739
theorem B33430961 : Blo 686314 33430961 := bstep (se 2 (by rfl) ⟨12536610, by rfl⟩ : syracuseStep 33430961 = 25073221) B25073221
theorem B4955735 : Blo 686314 4955735 := bstep (se 1 (by rfl) ⟨3716801, by rfl⟩ : syracuseStep 4955735 = 7433603) B7433603
theorem B1547873 : Blo 686314 1547873 := bstep (se 2 (by rfl) ⟨580452, by rfl⟩ : syracuseStep 1547873 = 1160905) B1160905
theorem B1548215 : Blo 686314 1548215 := bstep (se 1 (by rfl) ⟨1161161, by rfl⟩ : syracuseStep 1548215 = 2322323) B2322323
theorem B21537089 : Blo 686314 21537089 := bstep (se 2 (by rfl) ⟨8076408, by rfl⟩ : syracuseStep 21537089 = 16152817) B16152817
theorem B1548809 : Blo 686314 1548809 := bstep (se 2 (by rfl) ⟨580803, by rfl⟩ : syracuseStep 1548809 = 1161607) B1161607
theorem B12526103 : Blo 686314 12526103 := bstep (se 1 (by rfl) ⟨9394577, by rfl⟩ : syracuseStep 12526103 = 18789155) B18789155
theorem B1549151 : Blo 686314 1549151 := bstep (se 1 (by rfl) ⟨1161863, by rfl⟩ : syracuseStep 1549151 = 2323727) B2323727
theorem B7447403 : Blo 686314 7447403 := bstep (se 1 (by rfl) ⟨5585552, by rfl⟩ : syracuseStep 7447403 = 11171105) B11171105
theorem B2204599 : Blo 686314 2204599 := bstep (se 1 (by rfl) ⟨1653449, by rfl⟩ : syracuseStep 2204599 = 3306899) B3306899
theorem B1549331 : Blo 686314 1549331 := bstep (se 1 (by rfl) ⟨1161998, by rfl⟩ : syracuseStep 1549331 = 2323997) B2323997
theorem B3482675 : Blo 686314 3482675 := bstep (se 1 (by rfl) ⟨2612006, by rfl⟩ : syracuseStep 3482675 = 5224013) B5224013
theorem B2204729 : Blo 686314 2204729 := bstep (se 2 (by rfl) ⟨826773, by rfl⟩ : syracuseStep 2204729 = 1653547) B1653547
theorem B5284943 : Blo 686314 5284943 := bstep (se 1 (by rfl) ⟨3963707, by rfl⟩ : syracuseStep 5284943 = 7927415) B7927415
theorem B1549673 : Blo 686314 1549673 := bstep (se 2 (by rfl) ⟨581127, by rfl⟩ : syracuseStep 1549673 = 1162255) B1162255
theorem B1746319 : Blo 686314 1746319 := bstep (se 1 (by rfl) ⟨1309739, by rfl⟩ : syracuseStep 1746319 = 2619479) B2619479
theorem B1746643 : Blo 686314 1746643 := bstep (se 1 (by rfl) ⟨1309982, by rfl⟩ : syracuseStep 1746643 = 2619965) B2619965
theorem B5023583 : Blo 686314 5023583 := bstep (se 1 (by rfl) ⟨3767687, by rfl⟩ : syracuseStep 5023583 = 7535375) B7535375
theorem B1550267 : Blo 686314 1550267 := bstep (se 1 (by rfl) ⟨1162700, by rfl⟩ : syracuseStep 1550267 = 2325401) B2325401
theorem B5875649 : Blo 686314 5875649 := bstep (se 2 (by rfl) ⟨2203368, by rfl⟩ : syracuseStep 5875649 = 4406737) B4406737
theorem B1550393 : Blo 686314 1550393 := bstep (se 2 (by rfl) ⟨581397, by rfl⟩ : syracuseStep 1550393 = 1162795) B1162795
theorem B698587 : Blo 686314 698587 := bstep (se 1 (by rfl) ⟨523940, by rfl⟩ : syracuseStep 698587 = 1047881) B1047881
theorem B2795905 : Blo 686314 2795905 := bstep (se 2 (by rfl) ⟨1048464, by rfl⟩ : syracuseStep 2795905 = 2096929) B2096929
theorem B1550735 : Blo 686314 1550735 := bstep (se 1 (by rfl) ⟨1163051, by rfl⟩ : syracuseStep 1550735 = 2326103) B2326103
theorem B4401611 : Blo 686314 4401611 := bstep (se 1 (by rfl) ⟨3301208, by rfl⟩ : syracuseStep 4401611 = 6602417) B6602417
theorem B928379 : Blo 686314 928379 := bstep (se 1 (by rfl) ⟨696284, by rfl⟩ : syracuseStep 928379 = 1392569) B1392569
theorem B3484295 : Blo 686314 3484295 := bstep (se 1 (by rfl) ⟨2613221, by rfl⟩ : syracuseStep 3484295 = 5226443) B5226443
theorem B1551059 : Blo 686314 1551059 := bstep (se 1 (by rfl) ⟨1163294, by rfl⟩ : syracuseStep 1551059 = 2326589) B2326589
theorem B994231 : Blo 686314 994231 := bstep (se 1 (by rfl) ⟨745673, by rfl⟩ : syracuseStep 994231 = 1491347) B1491347
theorem B1322347 : Blo 686314 1322347 := bstep (se 1 (by rfl) ⟨991760, by rfl⟩ : syracuseStep 1322347 = 1983521) B1983521
theorem B2796943 : Blo 686314 2796943 := bstep (se 1 (by rfl) ⟨2097707, by rfl⟩ : syracuseStep 2796943 = 4195415) B4195415
theorem B1158583 : Blo 686314 1158583 := bstep (se 1 (by rfl) ⟨868937, by rfl⟩ : syracuseStep 1158583 = 1737875) B1737875
theorem B1158779 : Blo 686314 1158779 := bstep (se 1 (by rfl) ⟨869084, by rfl⟩ : syracuseStep 1158779 = 1738169) B1738169
theorem B1551995 : Blo 686314 1551995 := bstep (se 1 (by rfl) ⟨1163996, by rfl⟩ : syracuseStep 1551995 = 2327993) B2327993
theorem B1552121 : Blo 686314 1552121 := bstep (se 2 (by rfl) ⟨582045, by rfl⟩ : syracuseStep 1552121 = 1164091) B1164091
theorem B7450555 : Blo 686314 7450555 := bstep (se 1 (by rfl) ⟨5587916, by rfl⟩ : syracuseStep 7450555 = 11175833) B11175833
theorem B2207675 : Blo 686314 2207675 := bstep (se 1 (by rfl) ⟨1655756, by rfl⟩ : syracuseStep 2207675 = 3311513) B3311513
theorem B1552391 : Blo 686314 1552391 := bstep (se 1 (by rfl) ⟨1164293, by rfl⟩ : syracuseStep 1552391 = 2328587) B2328587
theorem B1159177 : Blo 686314 1159177 := bstep (se 2 (by rfl) ⟨434691, by rfl⟩ : syracuseStep 1159177 = 869383) B869383
theorem B3485753 : Blo 686314 3485753 := bstep (se 2 (by rfl) ⟨1307157, by rfl⟩ : syracuseStep 3485753 = 2614315) B2614315
theorem B1552463 : Blo 686314 1552463 := bstep (se 1 (by rfl) ⟨1164347, by rfl⟩ : syracuseStep 1552463 = 2328695) B2328695
theorem B1159339 : Blo 686314 1159339 := bstep (se 1 (by rfl) ⟨869504, by rfl⟩ : syracuseStep 1159339 = 1739009) B1739009
theorem B1159643 : Blo 686314 1159643 := bstep (se 1 (by rfl) ⟨869732, by rfl⟩ : syracuseStep 1159643 = 1739465) B1739465
theorem B1552859 : Blo 686314 1552859 := bstep (se 1 (by rfl) ⟨1164644, by rfl⟩ : syracuseStep 1552859 = 2329289) B2329289
theorem B733735 : Blo 686314 733735 := bstep (se 1 (by rfl) ⟨550301, by rfl⟩ : syracuseStep 733735 = 1100603) B1100603
theorem B1323577 : Blo 686314 1323577 := bstep (se 2 (by rfl) ⟨496341, by rfl⟩ : syracuseStep 1323577 = 992683) B992683
theorem B1159879 : Blo 686314 1159879 := bstep (se 1 (by rfl) ⟨869909, by rfl⟩ : syracuseStep 1159879 = 1739819) B1739819
theorem B1160041 : Blo 686314 1160041 := bstep (se 2 (by rfl) ⟨435015, by rfl⟩ : syracuseStep 1160041 = 870031) B870031
theorem B3912907 : Blo 686314 3912907 := bstep (se 1 (by rfl) ⟨2934680, by rfl⟩ : syracuseStep 3912907 = 5869361) B5869361
theorem B3978487 : Blo 686314 3978487 := bstep (se 1 (by rfl) ⟨2983865, by rfl⟩ : syracuseStep 3978487 = 5967731) B5967731
theorem B1029551 : Blo 686314 1029551 := bstep (se 1 (by rfl) ⟨772163, by rfl⟩ : syracuseStep 1029551 = 1544327) B1544327
theorem B1160635 : Blo 686314 1160635 := bstep (se 1 (by rfl) ⟨870476, by rfl⟩ : syracuseStep 1160635 = 1740953) B1740953
theorem B1029641 : Blo 686314 1029641 := bstep (se 2 (by rfl) ⟨386115, by rfl⟩ : syracuseStep 1029641 = 772231) B772231
theorem B1029671 : Blo 686314 1029671 := bstep (se 1 (by rfl) ⟨772253, by rfl⟩ : syracuseStep 1029671 = 1544507) B1544507
theorem B1160743 : Blo 686314 1160743 := bstep (se 1 (by rfl) ⟨870557, by rfl⟩ : syracuseStep 1160743 = 1741115) B1741115
theorem B1029755 : Blo 686314 1029755 := bstep (se 1 (by rfl) ⟨772316, by rfl⟩ : syracuseStep 1029755 = 1544633) B1544633
theorem B1029881 : Blo 686314 1029881 := bstep (se 2 (by rfl) ⟨386205, by rfl⟩ : syracuseStep 1029881 = 772411) B772411
theorem B1029983 : Blo 686314 1029983 := bstep (se 1 (by rfl) ⟨772487, by rfl⟩ : syracuseStep 1029983 = 1544975) B1544975
theorem B1029995 : Blo 686314 1029995 := bstep (se 1 (by rfl) ⟨772496, by rfl⟩ : syracuseStep 1029995 = 1544993) B1544993
theorem B1161067 : Blo 686314 1161067 := bstep (se 1 (by rfl) ⟨870800, by rfl⟩ : syracuseStep 1161067 = 1741601) B1741601
theorem B4962167 : Blo 686314 4962167 := bstep (se 1 (by rfl) ⟨3721625, by rfl⟩ : syracuseStep 4962167 = 7443251) B7443251
theorem B6272977 : Blo 686314 6272977 := bstep (se 2 (by rfl) ⟨2352366, by rfl⟩ : syracuseStep 6272977 = 4704733) B4704733
theorem B1030223 : Blo 686314 1030223 := bstep (se 1 (by rfl) ⟨772667, by rfl⟩ : syracuseStep 1030223 = 1545335) B1545335
theorem B3487859 : Blo 686314 3487859 := bstep (se 1 (by rfl) ⟨2615894, by rfl⟩ : syracuseStep 3487859 = 5231789) B5231789
theorem B1030343 : Blo 686314 1030343 := bstep (se 1 (by rfl) ⟨772757, by rfl⟩ : syracuseStep 1030343 = 1545515) B1545515
theorem B1030505 : Blo 686314 1030505 := bstep (se 2 (by rfl) ⟨386439, by rfl⟩ : syracuseStep 1030505 = 772879) B772879
theorem B1030583 : Blo 686314 1030583 := bstep (se 1 (by rfl) ⟨772937, by rfl⟩ : syracuseStep 1030583 = 1545875) B1545875
theorem B1030619 : Blo 686314 1030619 := bstep (se 1 (by rfl) ⟨772964, by rfl⟩ : syracuseStep 1030619 = 1545929) B1545929
theorem B5224985 : Blo 686314 5224985 := bstep (se 2 (by rfl) ⟨1959369, by rfl⟩ : syracuseStep 5224985 = 3918739) B3918739
theorem B735823 : Blo 686314 735823 := bstep (se 1 (by rfl) ⟨551867, by rfl⟩ : syracuseStep 735823 = 1103735) B1103735
theorem B10566389 : Blo 686314 10566389 := bstep (se 5 (by rfl) ⟨495299, by rfl⟩ : syracuseStep 10566389 = 990599) B990599
theorem B1162127 : Blo 686314 1162127 := bstep (se 1 (by rfl) ⟨871595, by rfl⟩ : syracuseStep 1162127 = 1743191) B1743191
theorem B1031087 : Blo 686314 1031087 := bstep (se 1 (by rfl) ⟨773315, by rfl⟩ : syracuseStep 1031087 = 1546631) B1546631
theorem B1031177 : Blo 686314 1031177 := bstep (se 2 (by rfl) ⟨386691, by rfl⟩ : syracuseStep 1031177 = 773383) B773383
theorem B1031207 : Blo 686314 1031207 := bstep (se 1 (by rfl) ⟨773405, by rfl⟩ : syracuseStep 1031207 = 1546811) B1546811
theorem B7846955 : Blo 686314 7846955 := bstep (se 1 (by rfl) ⟨5885216, by rfl⟩ : syracuseStep 7846955 = 11770433) B11770433
theorem B1031291 : Blo 686314 1031291 := bstep (se 1 (by rfl) ⟨773468, by rfl⟩ : syracuseStep 1031291 = 1546937) B1546937
theorem B1162363 : Blo 686314 1162363 := bstep (se 1 (by rfl) ⟨871772, by rfl⟩ : syracuseStep 1162363 = 1743545) B1743545
theorem B1031417 : Blo 686314 1031417 := bstep (se 2 (by rfl) ⟨386781, by rfl⟩ : syracuseStep 1031417 = 773563) B773563
theorem B1031519 : Blo 686314 1031519 := bstep (se 1 (by rfl) ⟨773639, by rfl⟩ : syracuseStep 1031519 = 1547279) B1547279
theorem B1031531 : Blo 686314 1031531 := bstep (se 1 (by rfl) ⟨773648, by rfl⟩ : syracuseStep 1031531 = 1547297) B1547297
theorem B3718619 : Blo 686314 3718619 := bstep (se 1 (by rfl) ⟨2788964, by rfl⟩ : syracuseStep 3718619 = 5577929) B5577929
theorem B1326611 : Blo 686314 1326611 := bstep (se 1 (by rfl) ⟨994958, by rfl⟩ : syracuseStep 1326611 = 1989917) B1989917
theorem B1031759 : Blo 686314 1031759 := bstep (se 1 (by rfl) ⟨773819, by rfl⟩ : syracuseStep 1031759 = 1547639) B1547639
theorem B2211467 : Blo 686314 2211467 := bstep (se 1 (by rfl) ⟨1658600, by rfl⟩ : syracuseStep 2211467 = 3317201) B3317201
theorem B1031879 : Blo 686314 1031879 := bstep (se 1 (by rfl) ⟨773909, by rfl⟩ : syracuseStep 1031879 = 1547819) B1547819
theorem B3489479 : Blo 686314 3489479 := bstep (se 1 (by rfl) ⟨2617109, by rfl⟩ : syracuseStep 3489479 = 5234219) B5234219
theorem B1032041 : Blo 686314 1032041 := bstep (se 2 (by rfl) ⟨387015, by rfl⟩ : syracuseStep 1032041 = 774031) B774031
theorem B1032119 : Blo 686314 1032119 := bstep (se 1 (by rfl) ⟨774089, by rfl⟩ : syracuseStep 1032119 = 1548179) B1548179
theorem B1032155 : Blo 686314 1032155 := bstep (se 1 (by rfl) ⟨774116, by rfl⟩ : syracuseStep 1032155 = 1548233) B1548233
theorem B1163227 : Blo 686314 1163227 := bstep (se 1 (by rfl) ⟨872420, by rfl⟩ : syracuseStep 1163227 = 1744841) B1744841
theorem B2474063 : Blo 686314 2474063 := bstep (se 1 (by rfl) ⟨1855547, by rfl⟩ : syracuseStep 2474063 = 3711095) B3711095
theorem B1032623 : Blo 686314 1032623 := bstep (se 1 (by rfl) ⟨774467, by rfl⟩ : syracuseStep 1032623 = 1548935) B1548935
theorem B1032713 : Blo 686314 1032713 := bstep (se 2 (by rfl) ⟨387267, by rfl⟩ : syracuseStep 1032713 = 774535) B774535
theorem B1032743 : Blo 686314 1032743 := bstep (se 1 (by rfl) ⟨774557, by rfl⟩ : syracuseStep 1032743 = 1549115) B1549115
theorem B1163855 : Blo 686314 1163855 := bstep (se 1 (by rfl) ⟨872891, by rfl⟩ : syracuseStep 1163855 = 1745783) B1745783
theorem B1032827 : Blo 686314 1032827 := bstep (se 1 (by rfl) ⟨774620, by rfl⟩ : syracuseStep 1032827 = 1549241) B1549241
theorem B1032953 : Blo 686314 1032953 := bstep (se 2 (by rfl) ⟨387357, by rfl⟩ : syracuseStep 1032953 = 774715) B774715
theorem B1033055 : Blo 686314 1033055 := bstep (se 1 (by rfl) ⟨774791, by rfl⟩ : syracuseStep 1033055 = 1549583) B1549583
theorem B1033067 : Blo 686314 1033067 := bstep (se 1 (by rfl) ⟨774800, by rfl⟩ : syracuseStep 1033067 = 1549601) B1549601
theorem B1033295 : Blo 686314 1033295 := bstep (se 1 (by rfl) ⟨774971, by rfl⟩ : syracuseStep 1033295 = 1549943) B1549943
theorem B1033415 : Blo 686314 1033415 := bstep (se 1 (by rfl) ⟨775061, by rfl⟩ : syracuseStep 1033415 = 1550123) B1550123
theorem B2606327 : Blo 686314 2606327 := bstep (se 1 (by rfl) ⟨1954745, by rfl⟩ : syracuseStep 2606327 = 3909491) B3909491
theorem B1656055 : Blo 686314 1656055 := bstep (se 1 (by rfl) ⟨1242041, by rfl⟩ : syracuseStep 1656055 = 2484083) B2484083
theorem B1033577 : Blo 686314 1033577 := bstep (se 2 (by rfl) ⟨387591, by rfl⟩ : syracuseStep 1033577 = 775183) B775183
theorem B5227901 : Blo 686314 5227901 := bstep (se 3 (by rfl) ⟨980231, by rfl⟩ : syracuseStep 5227901 = 1960463) B1960463
theorem B7423397 : Blo 686314 7423397 := bstep (se 4 (by rfl) ⟨695943, by rfl⟩ : syracuseStep 7423397 = 1391887) B1391887
theorem B1164719 : Blo 686314 1164719 := bstep (se 1 (by rfl) ⟨873539, by rfl⟩ : syracuseStep 1164719 = 1747079) B1747079
theorem B1033655 : Blo 686314 1033655 := bstep (se 1 (by rfl) ⟨775241, by rfl⟩ : syracuseStep 1033655 = 1550483) B1550483
theorem B1033691 : Blo 686314 1033691 := bstep (se 1 (by rfl) ⟨775268, by rfl⟩ : syracuseStep 1033691 = 1550537) B1550537
theorem B3720953 : Blo 686314 3720953 := bstep (se 2 (by rfl) ⟨1395357, by rfl⟩ : syracuseStep 3720953 = 2790715) B2790715
theorem B1034159 : Blo 686314 1034159 := bstep (se 1 (by rfl) ⟨775619, by rfl⟩ : syracuseStep 1034159 = 1551239) B1551239
theorem B1034249 : Blo 686314 1034249 := bstep (se 2 (by rfl) ⟨387843, by rfl⟩ : syracuseStep 1034249 = 775687) B775687
theorem B1034279 : Blo 686314 1034279 := bstep (se 1 (by rfl) ⟨775709, by rfl⟩ : syracuseStep 1034279 = 1551419) B1551419
theorem B1034363 : Blo 686314 1034363 := bstep (se 1 (by rfl) ⟨775772, by rfl⟩ : syracuseStep 1034363 = 1551545) B1551545
theorem B8833157 : Blo 686314 8833157 := bstep (se 4 (by rfl) ⟨828108, by rfl⟩ : syracuseStep 8833157 = 1656217) B1656217
theorem B2607299 : Blo 686314 2607299 := bstep (se 1 (by rfl) ⟨1955474, by rfl⟩ : syracuseStep 2607299 = 3910949) B3910949
theorem B1034489 : Blo 686314 1034489 := bstep (se 2 (by rfl) ⟨387933, by rfl⟩ : syracuseStep 1034489 = 775867) B775867
theorem B772447 : Blo 686314 772447 := bstep (se 1 (by rfl) ⟨579335, by rfl⟩ : syracuseStep 772447 = 1158671) B1158671
theorem B1034591 : Blo 686314 1034591 := bstep (se 1 (by rfl) ⟨775943, by rfl⟩ : syracuseStep 1034591 = 1551887) B1551887
theorem B1034603 : Blo 686314 1034603 := bstep (se 1 (by rfl) ⟨775952, by rfl⟩ : syracuseStep 1034603 = 1551905) B1551905
theorem B5884397 : Blo 686314 5884397 := bstep (se 3 (by rfl) ⟨1103324, by rfl⟩ : syracuseStep 5884397 = 2206649) B2206649
theorem B1034831 : Blo 686314 1034831 := bstep (se 1 (by rfl) ⟨776123, by rfl⟩ : syracuseStep 1034831 = 1552247) B1552247
theorem B2607815 : Blo 686314 2607815 := bstep (se 1 (by rfl) ⟨1955861, by rfl⟩ : syracuseStep 2607815 = 3911723) B3911723
theorem B772807 : Blo 686314 772807 := bstep (se 1 (by rfl) ⟨579605, by rfl⟩ : syracuseStep 772807 = 1159211) B1159211
theorem B1034951 : Blo 686314 1034951 := bstep (se 1 (by rfl) ⟨776213, by rfl⟩ : syracuseStep 1034951 = 1552427) B1552427
theorem B2476829 : Blo 686314 2476829 := bstep (se 3 (by rfl) ⟨464405, by rfl⟩ : syracuseStep 2476829 = 928811) B928811
theorem B1035113 : Blo 686314 1035113 := bstep (se 2 (by rfl) ⟨388167, by rfl⟩ : syracuseStep 1035113 = 776335) B776335
theorem B2476975 : Blo 686314 2476975 := bstep (se 1 (by rfl) ⟨1857731, by rfl⟩ : syracuseStep 2476975 = 3715463) B3715463
theorem B1035191 : Blo 686314 1035191 := bstep (se 1 (by rfl) ⟨776393, by rfl⟩ : syracuseStep 1035191 = 1552787) B1552787
theorem B1035227 : Blo 686314 1035227 := bstep (se 1 (by rfl) ⟨776420, by rfl⟩ : syracuseStep 1035227 = 1552841) B1552841
theorem B10210277 : Blo 686314 10210277 := bstep (se 4 (by rfl) ⟨957213, by rfl⟩ : syracuseStep 10210277 = 1914427) B1914427
theorem B60182003 : Blo 686314 60182003 := bstep (se 1 (by rfl) ⟨45136502, by rfl⟩ : syracuseStep 60182003 = 90273005) B90273005
theorem B773671 : Blo 686314 773671 := bstep (se 1 (by rfl) ⟨580253, by rfl⟩ : syracuseStep 773671 = 1160507) B1160507
theorem B871975 : Blo 686314 871975 := bstep (se 1 (by rfl) ⟨653981, by rfl⟩ : syracuseStep 871975 = 1307963) B1307963
theorem B2608787 : Blo 686314 2608787 := bstep (se 1 (by rfl) ⟨1956590, by rfl⟩ : syracuseStep 2608787 = 3913181) B3913181
theorem B2477753 : Blo 686314 2477753 := bstep (se 2 (by rfl) ⟨929157, by rfl⟩ : syracuseStep 2477753 = 1858315) B1858315
theorem B2608969 : Blo 686314 2608969 := bstep (se 2 (by rfl) ⟨978363, by rfl⟩ : syracuseStep 2608969 = 1956727) B1956727
theorem B872299 : Blo 686314 872299 := bstep (se 1 (by rfl) ⟨654224, by rfl⟩ : syracuseStep 872299 = 1308449) B1308449
theorem B1101833 : Blo 686314 1101833 := bstep (se 2 (by rfl) ⟨413187, by rfl⟩ : syracuseStep 1101833 = 826375) B826375
theorem B22368271 : Blo 686314 22368271 := bstep (se 1 (by rfl) ⟨16776203, by rfl⟩ : syracuseStep 22368271 = 33552407) B33552407
theorem B13062221 : Blo 686314 13062221 := bstep (se 3 (by rfl) ⟨2449166, by rfl⟩ : syracuseStep 13062221 = 4898333) B4898333
theorem B872527 : Blo 686314 872527 := bstep (se 1 (by rfl) ⟨654395, by rfl⟩ : syracuseStep 872527 = 1308791) B1308791
theorem B1102223 : Blo 686314 1102223 := bstep (se 1 (by rfl) ⟨826667, by rfl⟩ : syracuseStep 1102223 = 1653335) B1653335
theorem B9916951 : Blo 686314 9916951 := bstep (se 1 (by rfl) ⟨7437713, by rfl⟩ : syracuseStep 9916951 = 14875427) B14875427
theorem B1102415 : Blo 686314 1102415 := bstep (se 1 (by rfl) ⟨826811, by rfl⟩ : syracuseStep 1102415 = 1653623) B1653623
theorem B8802917 : Blo 686314 8802917 := bstep (se 4 (by rfl) ⟨825273, by rfl⟩ : syracuseStep 8802917 = 1650547) B1650547
theorem B5952211 : Blo 686314 5952211 := bstep (se 1 (by rfl) ⟨4464158, by rfl⟩ : syracuseStep 5952211 = 8928317) B8928317
theorem B1954655 : Blo 686314 1954655 := bstep (se 1 (by rfl) ⟨1465991, by rfl⟩ : syracuseStep 1954655 = 2931983) B2931983
theorem B1725497 : Blo 686314 1725497 := bstep (se 2 (by rfl) ⟨647061, by rfl⟩ : syracuseStep 1725497 = 1294123) B1294123
theorem B775291 : Blo 686314 775291 := bstep (se 1 (by rfl) ⟨581468, by rfl⟩ : syracuseStep 775291 = 1162937) B1162937
theorem B873595 : Blo 686314 873595 := bstep (se 1 (by rfl) ⟨655196, by rfl⟩ : syracuseStep 873595 = 1310393) B1310393
theorem B1955315 : Blo 686314 1955315 := bstep (se 1 (by rfl) ⟨1466486, by rfl⟩ : syracuseStep 1955315 = 2932973) B2932973
theorem B775759 : Blo 686314 775759 := bstep (se 1 (by rfl) ⟨581819, by rfl⟩ : syracuseStep 775759 = 1163639) B1163639
theorem B5232275 : Blo 686314 5232275 := bstep (se 1 (by rfl) ⟨3924206, by rfl⟩ : syracuseStep 5232275 = 7848413) B7848413
theorem B2610899 : Blo 686314 2610899 := bstep (se 1 (by rfl) ⟨1958174, by rfl⟩ : syracuseStep 2610899 = 3916349) B3916349
theorem B1955657 : Blo 686314 1955657 := bstep (se 2 (by rfl) ⟨733371, by rfl⟩ : syracuseStep 1955657 = 1466743) B1466743
theorem B1955771 : Blo 686314 1955771 := bstep (se 1 (by rfl) ⟨1466828, by rfl⟩ : syracuseStep 1955771 = 2933657) B2933657
theorem B776155 : Blo 686314 776155 := bstep (se 1 (by rfl) ⟨582116, by rfl⟩ : syracuseStep 776155 = 1164233) B1164233
theorem B1955897 : Blo 686314 1955897 := bstep (se 2 (by rfl) ⟨733461, by rfl⟩ : syracuseStep 1955897 = 1466923) B1466923
theorem B11163905 : Blo 686314 11163905 := bstep (se 2 (by rfl) ⟨4186464, by rfl⟩ : syracuseStep 11163905 = 8372929) B8372929
theorem B5593625 : Blo 686314 5593625 := bstep (se 2 (by rfl) ⟨2097609, by rfl⟩ : syracuseStep 5593625 = 4195219) B4195219
theorem B2316923 : Blo 686314 2316923 := bstep (se 1 (by rfl) ⟨1737692, by rfl⟩ : syracuseStep 2316923 = 3475385) B3475385
theorem B5593859 : Blo 686314 5593859 := bstep (se 1 (by rfl) ⟨4195394, by rfl⟩ : syracuseStep 5593859 = 8390789) B8390789
theorem B2317085 : Blo 686314 2317085 := bstep (se 3 (by rfl) ⟨434453, by rfl⟩ : syracuseStep 2317085 = 868907) B868907
theorem B2480969 : Blo 686314 2480969 := bstep (se 2 (by rfl) ⟨930363, by rfl⟩ : syracuseStep 2480969 = 1860727) B1860727
theorem B7527397 : Blo 686314 7527397 := bstep (se 4 (by rfl) ⟨705693, by rfl⟩ : syracuseStep 7527397 = 1411387) B1411387
theorem B6282319 : Blo 686314 6282319 := bstep (se 1 (by rfl) ⟨4711739, by rfl⟩ : syracuseStep 6282319 = 9423479) B9423479
theorem B4971941 : Blo 686314 4971941 := bstep (se 4 (by rfl) ⟨466119, by rfl⟩ : syracuseStep 4971941 = 932239) B932239
theorem B2317787 : Blo 686314 2317787 := bstep (se 1 (by rfl) ⟨1738340, by rfl⟩ : syracuseStep 2317787 = 3476681) B3476681
theorem B2481673 : Blo 686314 2481673 := bstep (se 2 (by rfl) ⟨930627, by rfl⟩ : syracuseStep 2481673 = 1861255) B1861255
theorem B5594663 : Blo 686314 5594663 := bstep (se 1 (by rfl) ⟨4195997, by rfl⟩ : syracuseStep 5594663 = 8391995) B8391995
theorem B7855703 : Blo 686314 7855703 := bstep (se 1 (by rfl) ⟨5891777, by rfl⟩ : syracuseStep 7855703 = 11783555) B11783555
theorem B6610571 : Blo 686314 6610571 := bstep (se 1 (by rfl) ⟨4957928, by rfl⟩ : syracuseStep 6610571 = 9915857) B9915857
theorem B15065149 : Blo 686314 15065149 := bstep (se 3 (by rfl) ⟨2824715, by rfl⟩ : syracuseStep 15065149 = 5649431) B5649431
theorem B2613329 : Blo 686314 2613329 := bstep (se 2 (by rfl) ⟨979998, by rfl⟩ : syracuseStep 2613329 = 1959997) B1959997
theorem B2318489 : Blo 686314 2318489 := bstep (se 2 (by rfl) ⟨869433, by rfl⟩ : syracuseStep 2318489 = 1738867) B1738867
theorem B7823627 : Blo 686314 7823627 := bstep (se 1 (by rfl) ⟨5867720, by rfl⟩ : syracuseStep 7823627 = 11735441) B11735441
theorem B4710707 : Blo 686314 4710707 := bstep (se 1 (by rfl) ⟨3533030, by rfl⟩ : syracuseStep 4710707 = 7066061) B7066061
theorem B2974013 : Blo 686314 2974013 := bstep (se 3 (by rfl) ⟨557627, by rfl⟩ : syracuseStep 2974013 = 1115255) B1115255
theorem B2613647 : Blo 686314 2613647 := bstep (se 1 (by rfl) ⟨1960235, by rfl⟩ : syracuseStep 2613647 = 3920471) B3920471
theorem B1302959 : Blo 686314 1302959 := bstep (se 1 (by rfl) ⟨977219, by rfl⟩ : syracuseStep 1302959 = 1954439) B1954439
theorem B7463447 : Blo 686314 7463447 := bstep (se 1 (by rfl) ⟨5597585, by rfl⟩ : syracuseStep 7463447 = 11195171) B11195171
theorem B1860121 : Blo 686314 1860121 := bstep (se 2 (by rfl) ⟨697545, by rfl⟩ : syracuseStep 1860121 = 1395091) B1395091
theorem B2351713 : Blo 686314 2351713 := bstep (se 2 (by rfl) ⟨881892, by rfl⟩ : syracuseStep 2351713 = 1763785) B1763785
theorem B1958539 : Blo 686314 1958539 := bstep (se 1 (by rfl) ⟨1468904, by rfl⟩ : syracuseStep 1958539 = 2937809) B2937809
theorem B8938291 : Blo 686314 8938291 := bstep (se 1 (by rfl) ⟨6703718, by rfl⟩ : syracuseStep 8938291 = 13407437) B13407437
theorem B1303391 : Blo 686314 1303391 := bstep (se 1 (by rfl) ⟨977543, by rfl⟩ : syracuseStep 1303391 = 1955087) B1955087
theorem B9069515 : Blo 686314 9069515 := bstep (se 1 (by rfl) ⟨6802136, by rfl⟩ : syracuseStep 9069515 = 13604273) B13604273
theorem B5235677 : Blo 686314 5235677 := bstep (se 3 (by rfl) ⟨981689, by rfl⟩ : syracuseStep 5235677 = 1963379) B1963379
theorem B2319677 : Blo 686314 2319677 := bstep (se 3 (by rfl) ⟨434939, by rfl⟩ : syracuseStep 2319677 = 869879) B869879
theorem B2614589 : Blo 686314 2614589 := bstep (se 3 (by rfl) ⟨490235, by rfl⟩ : syracuseStep 2614589 = 980471) B980471
theorem B2483693 : Blo 686314 2483693 := bstep (se 3 (by rfl) ⟨465692, by rfl⟩ : syracuseStep 2483693 = 931385) B931385
theorem B4417375 : Blo 686314 4417375 := bstep (se 1 (by rfl) ⟨3313031, by rfl⟩ : syracuseStep 4417375 = 6626063) B6626063
theorem B3303287 : Blo 686314 3303287 := bstep (se 1 (by rfl) ⟨2477465, by rfl⟩ : syracuseStep 3303287 = 4954931) B4954931
theorem B4188023 : Blo 686314 4188023 := bstep (se 1 (by rfl) ⟨3141017, by rfl⟩ : syracuseStep 4188023 = 6282035) B6282035
theorem B1861559 : Blo 686314 1861559 := bstep (se 1 (by rfl) ⟨1396169, by rfl⟩ : syracuseStep 1861559 = 2792339) B2792339
theorem B4712377 : Blo 686314 4712377 := bstep (se 2 (by rfl) ⟨1767141, by rfl⟩ : syracuseStep 4712377 = 3534283) B3534283
theorem B1534009 : Blo 686314 1534009 := bstep (se 2 (by rfl) ⟨575253, by rfl⟩ : syracuseStep 1534009 = 1150507) B1150507
theorem B9922661 : Blo 686314 9922661 := bstep (se 4 (by rfl) ⟨930249, by rfl⟩ : syracuseStep 9922661 = 1860499) B1860499
theorem B11954309 : Blo 686314 11954309 := bstep (se 4 (by rfl) ⟨1120716, by rfl⟩ : syracuseStep 11954309 = 2241433) B2241433
theorem B2320541 : Blo 686314 2320541 := bstep (se 3 (by rfl) ⟨435101, by rfl⟩ : syracuseStep 2320541 = 870203) B870203
theorem B977447 : Blo 686314 977447 := bstep (se 1 (by rfl) ⟨733085, by rfl⟩ : syracuseStep 977447 = 1466171) B1466171
theorem B1960487 : Blo 686314 1960487 := bstep (se 1 (by rfl) ⟨1470365, by rfl⟩ : syracuseStep 1960487 = 2940731) B2940731
theorem B2321081 : Blo 686314 2321081 := bstep (se 2 (by rfl) ⟨870405, by rfl⟩ : syracuseStep 2321081 = 1740811) B1740811
theorem B1305335 : Blo 686314 1305335 := bstep (se 1 (by rfl) ⟨979001, by rfl⟩ : syracuseStep 1305335 = 1958003) B1958003
theorem B1239799 : Blo 686314 1239799 := bstep (se 1 (by rfl) ⟨929849, by rfl⟩ : syracuseStep 1239799 = 1859699) B1859699
theorem B3271427 : Blo 686314 3271427 := bstep (se 1 (by rfl) ⟨2453570, by rfl⟩ : syracuseStep 3271427 = 4907141) B4907141
theorem B1305487 : Blo 686314 1305487 := bstep (se 1 (by rfl) ⟨979115, by rfl⟩ : syracuseStep 1305487 = 1958231) B1958231
theorem B1764359 : Blo 686314 1764359 := bstep (se 1 (by rfl) ⟨1323269, by rfl⟩ : syracuseStep 1764359 = 2646539) B2646539
theorem B1469459 : Blo 686314 1469459 := bstep (se 1 (by rfl) ⟨1102094, by rfl⟩ : syracuseStep 1469459 = 2204189) B2204189
theorem B8842283 : Blo 686314 8842283 := bstep (se 1 (by rfl) ⟨6631712, by rfl⟩ : syracuseStep 8842283 = 13263425) B13263425
theorem B977999 : Blo 686314 977999 := bstep (se 1 (by rfl) ⟨733499, by rfl⟩ : syracuseStep 977999 = 1466999) B1466999
theorem B2321675 : Blo 686314 2321675 := bstep (se 1 (by rfl) ⟨1741256, by rfl⟩ : syracuseStep 2321675 = 3482513) B3482513
theorem B1469801 : Blo 686314 1469801 := bstep (se 2 (by rfl) ⟨551175, by rfl⟩ : syracuseStep 1469801 = 1102351) B1102351
theorem B2321945 : Blo 686314 2321945 := bstep (se 2 (by rfl) ⟨870729, by rfl⟩ : syracuseStep 2321945 = 1741459) B1741459
theorem B6614567 : Blo 686314 6614567 := bstep (se 1 (by rfl) ⟨4960925, by rfl⟩ : syracuseStep 6614567 = 9921851) B9921851
theorem B1961671 : Blo 686314 1961671 := bstep (se 1 (by rfl) ⟨1471253, by rfl⟩ : syracuseStep 1961671 = 2942507) B2942507
theorem B3731143 : Blo 686314 3731143 := bstep (se 1 (by rfl) ⟨2798357, by rfl⟩ : syracuseStep 3731143 = 5596715) B5596715
theorem B1306361 : Blo 686314 1306361 := bstep (se 2 (by rfl) ⟨489885, by rfl⟩ : syracuseStep 1306361 = 979771) B979771
theorem B1306543 : Blo 686314 1306543 := bstep (se 1 (by rfl) ⟨979907, by rfl⟩ : syracuseStep 1306543 = 1959815) B1959815
theorem B7172027 : Blo 686314 7172027 := bstep (se 1 (by rfl) ⟨5379020, by rfl⟩ : syracuseStep 7172027 = 10758041) B10758041
theorem B2945105 : Blo 686314 2945105 := bstep (se 2 (by rfl) ⟨1104414, by rfl⟩ : syracuseStep 2945105 = 2208829) B2208829
theorem B2323079 : Blo 686314 2323079 := bstep (se 1 (by rfl) ⟨1742309, by rfl⟩ : syracuseStep 2323079 = 3484619) B3484619
theorem B2617991 : Blo 686314 2617991 := bstep (se 1 (by rfl) ⟨1963493, by rfl⟩ : syracuseStep 2617991 = 3926987) B3926987
theorem B2519687 : Blo 686314 2519687 := bstep (se 1 (by rfl) ⟨1889765, by rfl⟩ : syracuseStep 2519687 = 3779531) B3779531
theorem B2323133 : Blo 686314 2323133 := bstep (se 3 (by rfl) ⟨435587, by rfl⟩ : syracuseStep 2323133 = 871175) B871175
theorem B2945821 : Blo 686314 2945821 := bstep (se 3 (by rfl) ⟨552341, by rfl⟩ : syracuseStep 2945821 = 1104683) B1104683
theorem B2323295 : Blo 686314 2323295 := bstep (se 1 (by rfl) ⟨1742471, by rfl⟩ : syracuseStep 2323295 = 3484943) B3484943
theorem B1962913 : Blo 686314 1962913 := bstep (se 2 (by rfl) ⟨736092, by rfl⟩ : syracuseStep 1962913 = 1472185) B1472185
theorem B2323457 : Blo 686314 2323457 := bstep (se 2 (by rfl) ⟨871296, by rfl⟩ : syracuseStep 2323457 = 1742593) B1742593
theorem B1307819 : Blo 686314 1307819 := bstep (se 1 (by rfl) ⟨980864, by rfl⟩ : syracuseStep 1307819 = 1961729) B1961729
theorem B29849269 : Blo 686314 29849269 := bstep (se 5 (by rfl) ⟨1399184, by rfl⟩ : syracuseStep 29849269 = 2798369) B2798369
theorem B5863211 : Blo 686314 5863211 := bstep (se 1 (by rfl) ⟨4397408, by rfl⟩ : syracuseStep 5863211 = 8794817) B8794817
theorem B2324267 : Blo 686314 2324267 := bstep (se 1 (by rfl) ⟨1743200, by rfl⟩ : syracuseStep 2324267 = 3486401) B3486401
theorem B41318261 : Blo 686314 41318261 := bstep (se 5 (by rfl) ⟨1936793, by rfl⟩ : syracuseStep 41318261 = 3873587) B3873587
theorem B981001 : Blo 686314 981001 := bstep (se 2 (by rfl) ⟨367875, by rfl⟩ : syracuseStep 981001 = 735751) B735751
theorem B2324537 : Blo 686314 2324537 := bstep (se 2 (by rfl) ⟨871701, by rfl⟩ : syracuseStep 2324537 = 1743403) B1743403
theorem B2619449 : Blo 686314 2619449 := bstep (se 2 (by rfl) ⟨982293, by rfl⟩ : syracuseStep 2619449 = 1964587) B1964587
theorem B1964189 : Blo 686314 1964189 := bstep (se 3 (by rfl) ⟨368285, by rfl⟩ : syracuseStep 1964189 = 736571) B736571
theorem B686375 : Blo 686314 686375 := bstep (se 1 (by rfl) ⟨514781, by rfl⟩ : syracuseStep 686375 = 1029563) B1029563
theorem B686415 : Blo 686314 686415 := bstep (se 1 (by rfl) ⟨514811, by rfl⟩ : syracuseStep 686415 = 1029623) B1029623
theorem B686431 : Blo 686314 686431 := bstep (se 1 (by rfl) ⟨514823, by rfl⟩ : syracuseStep 686431 = 1029647) B1029647
theorem B686459 : Blo 686314 686459 := bstep (se 1 (by rfl) ⟨514844, by rfl⟩ : syracuseStep 686459 = 1029689) B1029689
theorem B2324861 : Blo 686314 2324861 := bstep (se 3 (by rfl) ⟨435911, by rfl⟩ : syracuseStep 2324861 = 871823) B871823
theorem B686511 : Blo 686314 686511 := bstep (se 1 (by rfl) ⟨514883, by rfl⟩ : syracuseStep 686511 = 1029767) B1029767
theorem B686535 : Blo 686314 686535 := bstep (se 1 (by rfl) ⟨514901, by rfl⟩ : syracuseStep 686535 = 1029803) B1029803
theorem B686555 : Blo 686314 686555 := bstep (se 1 (by rfl) ⟨514916, by rfl⟩ : syracuseStep 686555 = 1029833) B1029833
theorem B1309193 : Blo 686314 1309193 := bstep (se 2 (by rfl) ⟨490947, by rfl⟩ : syracuseStep 1309193 = 981895) B981895
theorem B686631 : Blo 686314 686631 := bstep (se 1 (by rfl) ⟨514973, by rfl⟩ : syracuseStep 686631 = 1029947) B1029947
theorem B1309223 : Blo 686314 1309223 := bstep (se 1 (by rfl) ⟨981917, by rfl⟩ : syracuseStep 1309223 = 1963835) B1963835
theorem B686671 : Blo 686314 686671 := bstep (se 1 (by rfl) ⟨515003, by rfl⟩ : syracuseStep 686671 = 1030007) B1030007
theorem B686687 : Blo 686314 686687 := bstep (se 1 (by rfl) ⟨515015, by rfl⟩ : syracuseStep 686687 = 1030031) B1030031
theorem B686715 : Blo 686314 686715 := bstep (se 1 (by rfl) ⟨515036, by rfl⟩ : syracuseStep 686715 = 1030073) B1030073
theorem B2325131 : Blo 686314 2325131 := bstep (se 1 (by rfl) ⟨1743848, by rfl⟩ : syracuseStep 2325131 = 3487697) B3487697
theorem B686767 : Blo 686314 686767 := bstep (se 1 (by rfl) ⟨515075, by rfl⟩ : syracuseStep 686767 = 1030151) B1030151
theorem B686791 : Blo 686314 686791 := bstep (se 1 (by rfl) ⟨515093, by rfl⟩ : syracuseStep 686791 = 1030187) B1030187
theorem B5569235 : Blo 686314 5569235 := bstep (se 1 (by rfl) ⟨4176926, by rfl⟩ : syracuseStep 5569235 = 8353853) B8353853
theorem B686811 : Blo 686314 686811 := bstep (se 1 (by rfl) ⟨515108, by rfl⟩ : syracuseStep 686811 = 1030217) B1030217
theorem B686887 : Blo 686314 686887 := bstep (se 1 (by rfl) ⟨515165, by rfl⟩ : syracuseStep 686887 = 1030331) B1030331
theorem B686927 : Blo 686314 686927 := bstep (se 1 (by rfl) ⟨515195, by rfl⟩ : syracuseStep 686927 = 1030391) B1030391
theorem B686943 : Blo 686314 686943 := bstep (se 1 (by rfl) ⟨515207, by rfl⟩ : syracuseStep 686943 = 1030415) B1030415
theorem B686971 : Blo 686314 686971 := bstep (se 1 (by rfl) ⟨515228, by rfl⟩ : syracuseStep 686971 = 1030457) B1030457
theorem B687023 : Blo 686314 687023 := bstep (se 1 (by rfl) ⟨515267, by rfl⟩ : syracuseStep 687023 = 1030535) B1030535
theorem B1178551 : Blo 686314 1178551 := bstep (se 1 (by rfl) ⟨883913, by rfl⟩ : syracuseStep 1178551 = 1767827) B1767827
theorem B687047 : Blo 686314 687047 := bstep (se 1 (by rfl) ⟨515285, by rfl⟩ : syracuseStep 687047 = 1030571) B1030571
theorem B687067 : Blo 686314 687067 := bstep (se 1 (by rfl) ⟨515300, by rfl⟩ : syracuseStep 687067 = 1030601) B1030601
theorem B687143 : Blo 686314 687143 := bstep (se 1 (by rfl) ⟨515357, by rfl⟩ : syracuseStep 687143 = 1030715) B1030715
theorem B4422707 : Blo 686314 4422707 := bstep (se 1 (by rfl) ⟨3317030, by rfl⟩ : syracuseStep 4422707 = 6634061) B6634061
theorem B687183 : Blo 686314 687183 := bstep (se 1 (by rfl) ⟨515387, by rfl⟩ : syracuseStep 687183 = 1030775) B1030775
theorem B687199 : Blo 686314 687199 := bstep (se 1 (by rfl) ⟨515399, by rfl⟩ : syracuseStep 687199 = 1030799) B1030799
theorem B687227 : Blo 686314 687227 := bstep (se 1 (by rfl) ⟨515420, by rfl⟩ : syracuseStep 687227 = 1030841) B1030841
theorem B2358443 : Blo 686314 2358443 := bstep (se 1 (by rfl) ⟨1768832, by rfl⟩ : syracuseStep 2358443 = 3537665) B3537665
theorem B687279 : Blo 686314 687279 := bstep (se 1 (by rfl) ⟨515459, by rfl⟩ : syracuseStep 687279 = 1030919) B1030919
theorem B687303 : Blo 686314 687303 := bstep (se 1 (by rfl) ⟨515477, by rfl⟩ : syracuseStep 687303 = 1030955) B1030955
theorem B1309907 : Blo 686314 1309907 := bstep (se 1 (by rfl) ⟨982430, by rfl⟩ : syracuseStep 1309907 = 1964861) B1964861
theorem B687323 : Blo 686314 687323 := bstep (se 1 (by rfl) ⟨515492, by rfl⟩ : syracuseStep 687323 = 1030985) B1030985
theorem B1309945 : Blo 686314 1309945 := bstep (se 2 (by rfl) ⟨491229, by rfl⟩ : syracuseStep 1309945 = 982459) B982459
theorem B687399 : Blo 686314 687399 := bstep (se 1 (by rfl) ⟨515549, by rfl⟩ : syracuseStep 687399 = 1031099) B1031099
theorem B687439 : Blo 686314 687439 := bstep (se 1 (by rfl) ⟨515579, by rfl⟩ : syracuseStep 687439 = 1031159) B1031159
theorem B687455 : Blo 686314 687455 := bstep (se 1 (by rfl) ⟨515591, by rfl⟩ : syracuseStep 687455 = 1031183) B1031183
theorem B687483 : Blo 686314 687483 := bstep (se 1 (by rfl) ⟨515612, by rfl⟩ : syracuseStep 687483 = 1031225) B1031225
theorem B687535 : Blo 686314 687535 := bstep (se 1 (by rfl) ⟨515651, by rfl⟩ : syracuseStep 687535 = 1031303) B1031303
theorem B1047991 : Blo 686314 1047991 := bstep (se 1 (by rfl) ⟨785993, by rfl⟩ : syracuseStep 1047991 = 1571987) B1571987
theorem B687559 : Blo 686314 687559 := bstep (se 1 (by rfl) ⟨515669, by rfl⟩ : syracuseStep 687559 = 1031339) B1031339
theorem B687579 : Blo 686314 687579 := bstep (se 1 (by rfl) ⟨515684, by rfl⟩ : syracuseStep 687579 = 1031369) B1031369
theorem B2620937 : Blo 686314 2620937 := bstep (se 2 (by rfl) ⟨982851, by rfl⟩ : syracuseStep 2620937 = 1965703) B1965703
theorem B2326049 : Blo 686314 2326049 := bstep (se 2 (by rfl) ⟨872268, by rfl⟩ : syracuseStep 2326049 = 1744537) B1744537
theorem B687655 : Blo 686314 687655 := bstep (se 1 (by rfl) ⟨515741, by rfl⟩ : syracuseStep 687655 = 1031483) B1031483
theorem B982567 : Blo 686314 982567 := bstep (se 1 (by rfl) ⟨736925, by rfl⟩ : syracuseStep 982567 = 1473851) B1473851
theorem B687695 : Blo 686314 687695 := bstep (se 1 (by rfl) ⟨515771, by rfl⟩ : syracuseStep 687695 = 1031543) B1031543
theorem B687711 : Blo 686314 687711 := bstep (se 1 (by rfl) ⟨515783, by rfl⟩ : syracuseStep 687711 = 1031567) B1031567
theorem B687739 : Blo 686314 687739 := bstep (se 1 (by rfl) ⟨515804, by rfl⟩ : syracuseStep 687739 = 1031609) B1031609
theorem B687791 : Blo 686314 687791 := bstep (se 1 (by rfl) ⟨515843, by rfl⟩ : syracuseStep 687791 = 1031687) B1031687
theorem B687815 : Blo 686314 687815 := bstep (se 1 (by rfl) ⟨515861, by rfl⟩ : syracuseStep 687815 = 1031723) B1031723
theorem B687835 : Blo 686314 687835 := bstep (se 1 (by rfl) ⟨515876, by rfl⟩ : syracuseStep 687835 = 1031753) B1031753
theorem B2326265 : Blo 686314 2326265 := bstep (se 2 (by rfl) ⟨872349, by rfl⟩ : syracuseStep 2326265 = 1744699) B1744699
theorem B687911 : Blo 686314 687911 := bstep (se 1 (by rfl) ⟨515933, by rfl⟩ : syracuseStep 687911 = 1031867) B1031867
theorem B687951 : Blo 686314 687951 := bstep (se 1 (by rfl) ⟨515963, by rfl⟩ : syracuseStep 687951 = 1031927) B1031927
theorem B687967 : Blo 686314 687967 := bstep (se 1 (by rfl) ⟨515975, by rfl⟩ : syracuseStep 687967 = 1031951) B1031951
theorem B687995 : Blo 686314 687995 := bstep (se 1 (by rfl) ⟨515996, by rfl⟩ : syracuseStep 687995 = 1031993) B1031993
theorem B688047 : Blo 686314 688047 := bstep (se 1 (by rfl) ⟨516035, by rfl⟩ : syracuseStep 688047 = 1032071) B1032071
theorem B688071 : Blo 686314 688071 := bstep (se 1 (by rfl) ⟨516053, by rfl⟩ : syracuseStep 688071 = 1032107) B1032107
theorem B688091 : Blo 686314 688091 := bstep (se 1 (by rfl) ⟨516068, by rfl⟩ : syracuseStep 688091 = 1032137) B1032137
theorem B20086865 : Blo 686314 20086865 := bstep (se 2 (by rfl) ⟨7532574, by rfl⟩ : syracuseStep 20086865 = 15065149) B15065149
theorem B688415 : Blo 686314 688415 := bstep (se 1 (by rfl) ⟨516311, by rfl⟩ : syracuseStep 688415 = 1032623) B1032623
theorem B688475 : Blo 686314 688475 := bstep (se 1 (by rfl) ⟨516356, by rfl⟩ : syracuseStep 688475 = 1032713) B1032713
theorem B688495 : Blo 686314 688495 := bstep (se 1 (by rfl) ⟨516371, by rfl⟩ : syracuseStep 688495 = 1032743) B1032743
theorem B688551 : Blo 686314 688551 := bstep (se 1 (by rfl) ⟨516413, by rfl⟩ : syracuseStep 688551 = 1032827) B1032827
theorem B688635 : Blo 686314 688635 := bstep (se 1 (by rfl) ⟨516476, by rfl⟩ : syracuseStep 688635 = 1032953) B1032953
theorem B688703 : Blo 686314 688703 := bstep (se 1 (by rfl) ⟨516527, by rfl⟩ : syracuseStep 688703 = 1033055) B1033055
theorem B688711 : Blo 686314 688711 := bstep (se 1 (by rfl) ⟨516533, by rfl⟩ : syracuseStep 688711 = 1033067) B1033067
theorem B1049195 : Blo 686314 1049195 := bstep (se 1 (by rfl) ⟨786896, by rfl⟩ : syracuseStep 1049195 = 1573793) B1573793
theorem B688863 : Blo 686314 688863 := bstep (se 1 (by rfl) ⟨516647, by rfl⟩ : syracuseStep 688863 = 1033295) B1033295
theorem B688943 : Blo 686314 688943 := bstep (se 1 (by rfl) ⟨516707, by rfl⟩ : syracuseStep 688943 = 1033415) B1033415
theorem B1737551 : Blo 686314 1737551 := bstep (se 1 (by rfl) ⟨1303163, by rfl⟩ : syracuseStep 1737551 = 2606327) B2606327
theorem B689051 : Blo 686314 689051 := bstep (se 1 (by rfl) ⟨516788, by rfl⟩ : syracuseStep 689051 = 1033577) B1033577
theorem B4948931 : Blo 686314 4948931 := bstep (se 1 (by rfl) ⟨3711698, by rfl⟩ : syracuseStep 4948931 = 7423397) B7423397
theorem B689103 : Blo 686314 689103 := bstep (se 1 (by rfl) ⟨516827, by rfl⟩ : syracuseStep 689103 = 1033655) B1033655
theorem B689127 : Blo 686314 689127 := bstep (se 1 (by rfl) ⟨516845, by rfl⟩ : syracuseStep 689127 = 1033691) B1033691
theorem B3474575 : Blo 686314 3474575 := bstep (se 1 (by rfl) ⟨2605931, by rfl⟩ : syracuseStep 3474575 = 5211863) B5211863
theorem B11928809 : Blo 686314 11928809 := bstep (se 2 (by rfl) ⟨4473303, by rfl⟩ : syracuseStep 11928809 = 8946607) B8946607
theorem B689439 : Blo 686314 689439 := bstep (se 1 (by rfl) ⟨517079, by rfl⟩ : syracuseStep 689439 = 1034159) B1034159
theorem B689499 : Blo 686314 689499 := bstep (se 1 (by rfl) ⟨517124, by rfl⟩ : syracuseStep 689499 = 1034249) B1034249
theorem B689519 : Blo 686314 689519 := bstep (se 1 (by rfl) ⟨517139, by rfl⟩ : syracuseStep 689519 = 1034279) B1034279
theorem B689575 : Blo 686314 689575 := bstep (se 1 (by rfl) ⟨517181, by rfl⟩ : syracuseStep 689575 = 1034363) B1034363
theorem B1738199 : Blo 686314 1738199 := bstep (se 1 (by rfl) ⟨1303649, by rfl⟩ : syracuseStep 1738199 = 2607299) B2607299
theorem B689659 : Blo 686314 689659 := bstep (se 1 (by rfl) ⟨517244, by rfl⟩ : syracuseStep 689659 = 1034489) B1034489
theorem B689727 : Blo 686314 689727 := bstep (se 1 (by rfl) ⟨517295, by rfl⟩ : syracuseStep 689727 = 1034591) B1034591
theorem B689735 : Blo 686314 689735 := bstep (se 1 (by rfl) ⟨517301, by rfl⟩ : syracuseStep 689735 = 1034603) B1034603
theorem B689887 : Blo 686314 689887 := bstep (se 1 (by rfl) ⟨517415, by rfl⟩ : syracuseStep 689887 = 1034831) B1034831
theorem B1738543 : Blo 686314 1738543 := bstep (se 1 (by rfl) ⟨1303907, by rfl⟩ : syracuseStep 1738543 = 2607815) B2607815
theorem B689967 : Blo 686314 689967 := bstep (se 1 (by rfl) ⟨517475, by rfl⟩ : syracuseStep 689967 = 1034951) B1034951
theorem B2328425 : Blo 686314 2328425 := bstep (se 2 (by rfl) ⟨873159, by rfl⟩ : syracuseStep 2328425 = 1746319) B1746319
theorem B690075 : Blo 686314 690075 := bstep (se 1 (by rfl) ⟨517556, by rfl⟩ : syracuseStep 690075 = 1035113) B1035113
theorem B690127 : Blo 686314 690127 := bstep (se 1 (by rfl) ⟨517595, by rfl⟩ : syracuseStep 690127 = 1035191) B1035191
theorem B690151 : Blo 686314 690151 := bstep (se 1 (by rfl) ⟨517613, by rfl⟩ : syracuseStep 690151 = 1035227) B1035227
theorem B3475709 : Blo 686314 3475709 := bstep (se 3 (by rfl) ⟨651695, by rfl⟩ : syracuseStep 3475709 = 1303391) B1303391
theorem B2328857 : Blo 686314 2328857 := bstep (se 2 (by rfl) ⟨873321, by rfl⟩ : syracuseStep 2328857 = 1746643) B1746643
theorem B1739191 : Blo 686314 1739191 := bstep (se 1 (by rfl) ⟨1304393, by rfl⟩ : syracuseStep 1739191 = 2608787) B2608787
theorem B3476519 : Blo 686314 3476519 := bstep (se 1 (by rfl) ⟨2607389, by rfl⟩ : syracuseStep 3476519 = 5214779) B5214779
theorem B5868611 : Blo 686314 5868611 := bstep (se 1 (by rfl) ⟨4401458, by rfl⟩ : syracuseStep 5868611 = 8802917) B8802917
theorem B7081037 : Blo 686314 7081037 := bstep (se 3 (by rfl) ⟨1327694, by rfl⟩ : syracuseStep 7081037 = 2655389) B2655389
theorem B1150331 : Blo 686314 1150331 := bstep (se 1 (by rfl) ⟨862748, by rfl⟩ : syracuseStep 1150331 = 1725497) B1725497
theorem B1740599 : Blo 686314 1740599 := bstep (se 1 (by rfl) ⟨1305449, by rfl⟩ : syracuseStep 1740599 = 2610899) B2610899
theorem B1740649 : Blo 686314 1740649 := bstep (se 2 (by rfl) ⟨652743, by rfl⟩ : syracuseStep 1740649 = 1305487) B1305487
theorem B7442603 : Blo 686314 7442603 := bstep (se 1 (by rfl) ⟨5581952, by rfl⟩ : syracuseStep 7442603 = 11163905) B11163905
theorem B6623603 : Blo 686314 6623603 := bstep (se 1 (by rfl) ⟨4967702, by rfl⟩ : syracuseStep 6623603 = 9935405) B9935405
theorem B1544615 : Blo 686314 1544615 := bstep (se 1 (by rfl) ⟨1158461, by rfl⟩ : syracuseStep 1544615 = 2316923) B2316923
theorem B1544723 : Blo 686314 1544723 := bstep (se 1 (by rfl) ⟨1158542, by rfl⟩ : syracuseStep 1544723 = 2317085) B2317085
theorem B1544777 : Blo 686314 1544777 := bstep (se 2 (by rfl) ⟨579291, by rfl⟩ : syracuseStep 1544777 = 1158583) B1158583
theorem B3314627 : Blo 686314 3314627 := bstep (se 1 (by rfl) ⟨2485970, by rfl⟩ : syracuseStep 3314627 = 4971941) B4971941
theorem B22287307 : Blo 686314 22287307 := bstep (se 1 (by rfl) ⟨16715480, by rfl⟩ : syracuseStep 22287307 = 33430961) B33430961
theorem B1545191 : Blo 686314 1545191 := bstep (se 1 (by rfl) ⟨1158893, by rfl⟩ : syracuseStep 1545191 = 2317787) B2317787
theorem B3478625 : Blo 686314 3478625 := bstep (se 2 (by rfl) ⟨1304484, by rfl⟩ : syracuseStep 3478625 = 2608969) B2608969
theorem B1742057 : Blo 686314 1742057 := bstep (se 2 (by rfl) ⟨653271, by rfl⟩ : syracuseStep 1742057 = 1306543) B1306543
theorem B9934073 : Blo 686314 9934073 := bstep (se 2 (by rfl) ⟨3725277, by rfl⟩ : syracuseStep 9934073 = 7450555) B7450555
theorem B1545569 : Blo 686314 1545569 := bstep (se 2 (by rfl) ⟨579588, by rfl⟩ : syracuseStep 1545569 = 1159177) B1159177
theorem B29824361 : Blo 686314 29824361 := bstep (se 2 (by rfl) ⟨11184135, by rfl⟩ : syracuseStep 29824361 = 22368271) B22368271
theorem B1742219 : Blo 686314 1742219 := bstep (se 1 (by rfl) ⟨1306664, by rfl⟩ : syracuseStep 1742219 = 2613329) B2613329
theorem B1545659 : Blo 686314 1545659 := bstep (se 1 (by rfl) ⟨1159244, by rfl⟩ : syracuseStep 1545659 = 2318489) B2318489
theorem B5215751 : Blo 686314 5215751 := bstep (se 1 (by rfl) ⟨3911813, by rfl⟩ : syracuseStep 5215751 = 7823627) B7823627
theorem B14358059 : Blo 686314 14358059 := bstep (se 1 (by rfl) ⟨10768544, by rfl⟩ : syracuseStep 14358059 = 21537089) B21537089
theorem B1545785 : Blo 686314 1545785 := bstep (se 2 (by rfl) ⟨579669, by rfl⟩ : syracuseStep 1545785 = 1159339) B1159339
theorem B1742431 : Blo 686314 1742431 := bstep (se 1 (by rfl) ⟨1306823, by rfl⟩ : syracuseStep 1742431 = 2613647) B2613647
theorem B1546451 : Blo 686314 1546451 := bstep (se 1 (by rfl) ⟨1159838, by rfl⟩ : syracuseStep 1546451 = 2319677) B2319677
theorem B1743059 : Blo 686314 1743059 := bstep (se 1 (by rfl) ⟨1307294, by rfl⟩ : syracuseStep 1743059 = 2614589) B2614589
theorem B1546505 : Blo 686314 1546505 := bstep (se 2 (by rfl) ⟨579939, by rfl⟩ : syracuseStep 1546505 = 1159879) B1159879
theorem B1546721 : Blo 686314 1546721 := bstep (se 2 (by rfl) ⟨580020, by rfl⟩ : syracuseStep 1546721 = 1160041) B1160041
theorem B3349055 : Blo 686314 3349055 := bstep (se 1 (by rfl) ⟨2511791, by rfl⟩ : syracuseStep 3349055 = 5023583) B5023583
theorem B2202191 : Blo 686314 2202191 := bstep (se 1 (by rfl) ⟨1651643, by rfl⟩ : syracuseStep 2202191 = 3303287) B3303287
theorem B2792015 : Blo 686314 2792015 := bstep (se 1 (by rfl) ⟨2094011, by rfl⟩ : syracuseStep 2792015 = 4188023) B4188023
theorem B1547027 : Blo 686314 1547027 := bstep (se 1 (by rfl) ⟨1160270, by rfl⟩ : syracuseStep 1547027 = 2320541) B2320541
theorem B5217209 : Blo 686314 5217209 := bstep (se 2 (by rfl) ⟨1956453, by rfl⟩ : syracuseStep 5217209 = 3912907) B3912907
theorem B1547387 : Blo 686314 1547387 := bstep (se 1 (by rfl) ⟨1160540, by rfl⟩ : syracuseStep 1547387 = 2321081) B2321081
theorem B1547513 : Blo 686314 1547513 := bstep (se 2 (by rfl) ⟨580317, by rfl⟩ : syracuseStep 1547513 = 1160635) B1160635
theorem B3480893 : Blo 686314 3480893 := bstep (se 3 (by rfl) ⟨652667, by rfl⟩ : syracuseStep 3480893 = 1305335) B1305335
theorem B1547657 : Blo 686314 1547657 := bstep (se 2 (by rfl) ⟨580371, by rfl⟩ : syracuseStep 1547657 = 1160743) B1160743
theorem B1547783 : Blo 686314 1547783 := bstep (se 1 (by rfl) ⟨1160837, by rfl⟩ : syracuseStep 1547783 = 2321675) B2321675
theorem B1547963 : Blo 686314 1547963 := bstep (se 1 (by rfl) ⟨1160972, by rfl⟩ : syracuseStep 1547963 = 2321945) B2321945
theorem B1548089 : Blo 686314 1548089 := bstep (se 2 (by rfl) ⟨580533, by rfl⟩ : syracuseStep 1548089 = 1161067) B1161067
theorem B8363969 : Blo 686314 8363969 := bstep (se 2 (by rfl) ⟨3136488, by rfl⟩ : syracuseStep 8363969 = 6272977) B6272977
theorem B1548719 : Blo 686314 1548719 := bstep (se 1 (by rfl) ⟨1161539, by rfl⟩ : syracuseStep 1548719 = 2323079) B2323079
theorem B1745327 : Blo 686314 1745327 := bstep (se 1 (by rfl) ⟨1308995, by rfl⟩ : syracuseStep 1745327 = 2617991) B2617991
theorem B1679791 : Blo 686314 1679791 := bstep (se 1 (by rfl) ⟨1259843, by rfl⟩ : syracuseStep 1679791 = 2519687) B2519687
theorem B1548755 : Blo 686314 1548755 := bstep (se 1 (by rfl) ⟨1161566, by rfl⟩ : syracuseStep 1548755 = 2323133) B2323133
theorem B1548863 : Blo 686314 1548863 := bstep (se 1 (by rfl) ⟨1161647, by rfl⟩ : syracuseStep 1548863 = 2323295) B2323295
theorem B1548971 : Blo 686314 1548971 := bstep (se 1 (by rfl) ⟨1161728, by rfl⟩ : syracuseStep 1548971 = 2323457) B2323457
theorem B3908807 : Blo 686314 3908807 := bstep (se 1 (by rfl) ⟨2931605, by rfl⟩ : syracuseStep 3908807 = 5863211) B5863211
theorem B1549511 : Blo 686314 1549511 := bstep (se 1 (by rfl) ⟨1162133, by rfl⟩ : syracuseStep 1549511 = 2324267) B2324267
theorem B10036529 : Blo 686314 10036529 := bstep (se 2 (by rfl) ⟨3763698, by rfl⟩ : syracuseStep 10036529 = 7527397) B7527397
theorem B1549691 : Blo 686314 1549691 := bstep (se 1 (by rfl) ⟨1162268, by rfl⟩ : syracuseStep 1549691 = 2324537) B2324537
theorem B1746299 : Blo 686314 1746299 := bstep (se 1 (by rfl) ⟨1309724, by rfl⟩ : syracuseStep 1746299 = 2619449) B2619449
theorem B1549817 : Blo 686314 1549817 := bstep (se 2 (by rfl) ⟨581181, by rfl⟩ : syracuseStep 1549817 = 1162363) B1162363
theorem B1549907 : Blo 686314 1549907 := bstep (se 1 (by rfl) ⟨1162430, by rfl⟩ : syracuseStep 1549907 = 2324861) B2324861
theorem B1746593 : Blo 686314 1746593 := bstep (se 2 (by rfl) ⟨654972, by rfl⟩ : syracuseStep 1746593 = 1309945) B1309945
theorem B3483323 : Blo 686314 3483323 := bstep (se 1 (by rfl) ⟨2612492, by rfl⟩ : syracuseStep 3483323 = 5224985) B5224985
theorem B1550087 : Blo 686314 1550087 := bstep (se 1 (by rfl) ⟨1162565, by rfl⟩ : syracuseStep 1550087 = 2325131) B2325131
theorem B3712823 : Blo 686314 3712823 := bstep (se 1 (by rfl) ⟨2784617, by rfl⟩ : syracuseStep 3712823 = 5569235) B5569235
theorem B1747291 : Blo 686314 1747291 := bstep (se 1 (by rfl) ⟨1310468, by rfl⟩ : syracuseStep 1747291 = 2620937) B2620937
theorem B1550699 : Blo 686314 1550699 := bstep (se 1 (by rfl) ⟨1163024, by rfl⟩ : syracuseStep 1550699 = 2326049) B2326049
theorem B1550843 : Blo 686314 1550843 := bstep (se 1 (by rfl) ⟨1163132, by rfl⟩ : syracuseStep 1550843 = 2326265) B2326265
theorem B1550969 : Blo 686314 1550969 := bstep (se 2 (by rfl) ⟨581613, by rfl⟩ : syracuseStep 1550969 = 1163227) B1163227
theorem B1551023 : Blo 686314 1551023 := bstep (se 1 (by rfl) ⟨1163267, by rfl⟩ : syracuseStep 1551023 = 2326535) B2326535
theorem B1649375 : Blo 686314 1649375 := bstep (se 1 (by rfl) ⟨1237031, by rfl⟩ : syracuseStep 1649375 = 2474063) B2474063
theorem B1551095 : Blo 686314 1551095 := bstep (se 1 (by rfl) ⟨1163321, by rfl⟩ : syracuseStep 1551095 = 2326643) B2326643
theorem B1551275 : Blo 686314 1551275 := bstep (se 1 (by rfl) ⟨1163456, by rfl⟩ : syracuseStep 1551275 = 2326913) B2326913
theorem B5024987 : Blo 686314 5024987 := bstep (se 1 (by rfl) ⟨3768740, by rfl⟩ : syracuseStep 5024987 = 7537481) B7537481
theorem B1551815 : Blo 686314 1551815 := bstep (se 1 (by rfl) ⟨1163861, by rfl⟩ : syracuseStep 1551815 = 2327723) B2327723
theorem B3485267 : Blo 686314 3485267 := bstep (se 1 (by rfl) ⟨2613950, by rfl⟩ : syracuseStep 3485267 = 5227901) B5227901
theorem B2797139 : Blo 686314 2797139 := bstep (se 1 (by rfl) ⟨2097854, by rfl⟩ : syracuseStep 2797139 = 4195709) B4195709
theorem B1552175 : Blo 686314 1552175 := bstep (se 1 (by rfl) ⟨1164131, by rfl⟩ : syracuseStep 1552175 = 2328263) B2328263
theorem B33402941 : Blo 686314 33402941 := bstep (se 3 (by rfl) ⟨6263051, by rfl⟩ : syracuseStep 33402941 = 12526103) B12526103
theorem B2208073 : Blo 686314 2208073 := bstep (se 2 (by rfl) ⟨828027, by rfl⟩ : syracuseStep 2208073 = 1656055) B1656055
theorem B1159535 : Blo 686314 1159535 := bstep (se 1 (by rfl) ⟨869651, by rfl⟩ : syracuseStep 1159535 = 1739303) B1739303
theorem B1552751 : Blo 686314 1552751 := bstep (se 1 (by rfl) ⟨1164563, by rfl⟩ : syracuseStep 1552751 = 2329127) B2329127
theorem B1552823 : Blo 686314 1552823 := bstep (se 1 (by rfl) ⟨1164617, by rfl⟩ : syracuseStep 1552823 = 2329235) B2329235
theorem B1159751 : Blo 686314 1159751 := bstep (se 1 (by rfl) ⟨869813, by rfl⟩ : syracuseStep 1159751 = 1739627) B1739627
theorem B1552967 : Blo 686314 1552967 := bstep (se 1 (by rfl) ⟨1164725, by rfl⟩ : syracuseStep 1552967 = 2329451) B2329451
theorem B1553003 : Blo 686314 1553003 := bstep (se 1 (by rfl) ⟨1164752, by rfl⟩ : syracuseStep 1553003 = 2329505) B2329505
theorem B3715919 : Blo 686314 3715919 := bstep (se 1 (by rfl) ⟨2786939, by rfl⟩ : syracuseStep 3715919 = 5573879) B5573879
theorem B40121335 : Blo 686314 40121335 := bstep (se 1 (by rfl) ⟨30091001, by rfl⟩ : syracuseStep 40121335 = 60182003) B60182003
theorem B1160183 : Blo 686314 1160183 := bstep (se 1 (by rfl) ⟨870137, by rfl⟩ : syracuseStep 1160183 = 1740275) B1740275
theorem B1651835 : Blo 686314 1651835 := bstep (se 1 (by rfl) ⟨1238876, by rfl⟩ : syracuseStep 1651835 = 2477753) B2477753
theorem B734555 : Blo 686314 734555 := bstep (se 1 (by rfl) ⟨550916, by rfl⟩ : syracuseStep 734555 = 1101833) B1101833
theorem B2045345 : Blo 686314 2045345 := bstep (se 2 (by rfl) ⟨767004, by rfl⟩ : syracuseStep 2045345 = 1534009) B1534009
theorem B1029575 : Blo 686314 1029575 := bstep (se 1 (by rfl) ⟨772181, by rfl⟩ : syracuseStep 1029575 = 1544363) B1544363
theorem B734815 : Blo 686314 734815 := bstep (se 1 (by rfl) ⟨551111, by rfl⟩ : syracuseStep 734815 = 1102223) B1102223
theorem B1160939 : Blo 686314 1160939 := bstep (se 1 (by rfl) ⟨870704, by rfl⟩ : syracuseStep 1160939 = 1741409) B1741409
theorem B1029929 : Blo 686314 1029929 := bstep (se 2 (by rfl) ⟨386223, by rfl⟩ : syracuseStep 1029929 = 772447) B772447
theorem B1029935 : Blo 686314 1029935 := bstep (se 1 (by rfl) ⟨772451, by rfl⟩ : syracuseStep 1029935 = 1544903) B1544903
theorem B1030409 : Blo 686314 1030409 := bstep (se 2 (by rfl) ⟨386403, by rfl⟩ : syracuseStep 1030409 = 772807) B772807
theorem B1653065 : Blo 686314 1653065 := bstep (se 2 (by rfl) ⟨619899, by rfl⟩ : syracuseStep 1653065 = 1239799) B1239799
theorem B1030511 : Blo 686314 1030511 := bstep (se 1 (by rfl) ⟨772883, by rfl⟩ : syracuseStep 1030511 = 1545767) B1545767
theorem B3488183 : Blo 686314 3488183 := bstep (se 1 (by rfl) ⟨2616137, by rfl⟩ : syracuseStep 3488183 = 5232275) B5232275
theorem B1030727 : Blo 686314 1030727 := bstep (se 1 (by rfl) ⟨773045, by rfl⟩ : syracuseStep 1030727 = 1546091) B1546091
theorem B1325641 : Blo 686314 1325641 := bstep (se 2 (by rfl) ⟨497115, by rfl⟩ : syracuseStep 1325641 = 994231) B994231
theorem B1030763 : Blo 686314 1030763 := bstep (se 1 (by rfl) ⟨773072, by rfl⟩ : syracuseStep 1030763 = 1546145) B1546145
theorem B1161911 : Blo 686314 1161911 := bstep (se 1 (by rfl) ⟨871433, by rfl⟩ : syracuseStep 1161911 = 1742867) B1742867
theorem B1030991 : Blo 686314 1030991 := bstep (se 1 (by rfl) ⟨773243, by rfl⟩ : syracuseStep 1030991 = 1546487) B1546487
theorem B3914639 : Blo 686314 3914639 := bstep (se 1 (by rfl) ⟨2935979, by rfl⟩ : syracuseStep 3914639 = 5871959) B5871959
theorem B6273935 : Blo 686314 6273935 := bstep (se 1 (by rfl) ⟨4705451, by rfl⟩ : syracuseStep 6273935 = 9410903) B9410903
theorem B1031387 : Blo 686314 1031387 := bstep (se 1 (by rfl) ⟨773540, by rfl⟩ : syracuseStep 1031387 = 1547081) B1547081
theorem B1031561 : Blo 686314 1031561 := bstep (se 2 (by rfl) ⟨386835, by rfl⟩ : syracuseStep 1031561 = 773671) B773671
theorem B1162633 : Blo 686314 1162633 := bstep (se 2 (by rfl) ⟨435987, by rfl⟩ : syracuseStep 1162633 = 871975) B871975
theorem B3915323 : Blo 686314 3915323 := bstep (se 1 (by rfl) ⟨2936492, by rfl⟩ : syracuseStep 3915323 = 5872985) B5872985
theorem B1031915 : Blo 686314 1031915 := bstep (se 1 (by rfl) ⟨773936, by rfl⟩ : syracuseStep 1031915 = 1547873) B1547873
theorem B4407047 : Blo 686314 4407047 := bstep (se 1 (by rfl) ⟨3305285, by rfl⟩ : syracuseStep 4407047 = 6610571) B6610571
theorem B1163065 : Blo 686314 1163065 := bstep (se 2 (by rfl) ⟨436149, by rfl⟩ : syracuseStep 1163065 = 872299) B872299
theorem B1032143 : Blo 686314 1032143 := bstep (se 1 (by rfl) ⟨774107, by rfl⟩ : syracuseStep 1032143 = 1548215) B1548215
theorem B1163369 : Blo 686314 1163369 := bstep (se 2 (by rfl) ⟨436263, by rfl⟩ : syracuseStep 1163369 = 872527) B872527
theorem B1982675 : Blo 686314 1982675 := bstep (se 1 (by rfl) ⟨1487006, by rfl⟩ : syracuseStep 1982675 = 2974013) B2974013
theorem B868639 : Blo 686314 868639 := bstep (se 1 (by rfl) ⟨651479, by rfl⟩ : syracuseStep 868639 = 1302959) B1302959
theorem B1032539 : Blo 686314 1032539 := bstep (se 1 (by rfl) ⟨774404, by rfl⟩ : syracuseStep 1032539 = 1548809) B1548809
theorem B1032767 : Blo 686314 1032767 := bstep (se 1 (by rfl) ⟨774575, by rfl⟩ : syracuseStep 1032767 = 1549151) B1549151
theorem B4964935 : Blo 686314 4964935 := bstep (se 1 (by rfl) ⟨3723701, by rfl⟩ : syracuseStep 4964935 = 7447403) B7447403
theorem B6046343 : Blo 686314 6046343 := bstep (se 1 (by rfl) ⟨4534757, by rfl⟩ : syracuseStep 6046343 = 9069515) B9069515
theorem B3490451 : Blo 686314 3490451 := bstep (se 1 (by rfl) ⟨2617838, by rfl⟩ : syracuseStep 3490451 = 5235677) B5235677
theorem B1032887 : Blo 686314 1032887 := bstep (se 1 (by rfl) ⟨774665, by rfl⟩ : syracuseStep 1032887 = 1549331) B1549331
theorem B13222601 : Blo 686314 13222601 := bstep (se 2 (by rfl) ⟨4958475, by rfl⟩ : syracuseStep 13222601 = 9916951) B9916951
theorem B3523295 : Blo 686314 3523295 := bstep (se 1 (by rfl) ⟨2642471, by rfl⟩ : syracuseStep 3523295 = 5284943) B5284943
theorem B1033115 : Blo 686314 1033115 := bstep (se 1 (by rfl) ⟨774836, by rfl⟩ : syracuseStep 1033115 = 1549673) B1549673
theorem B1655795 : Blo 686314 1655795 := bstep (se 1 (by rfl) ⟨1241846, by rfl⟩ : syracuseStep 1655795 = 2483693) B2483693
theorem B1033511 : Blo 686314 1033511 := bstep (se 1 (by rfl) ⟨775133, by rfl⟩ : syracuseStep 1033511 = 1550267) B1550267
theorem B3917099 : Blo 686314 3917099 := bstep (se 1 (by rfl) ⟨2937824, by rfl⟩ : syracuseStep 3917099 = 5875649) B5875649
theorem B1033595 : Blo 686314 1033595 := bstep (se 1 (by rfl) ⟨775196, by rfl⟩ : syracuseStep 1033595 = 1550393) B1550393
theorem B2606525 : Blo 686314 2606525 := bstep (se 3 (by rfl) ⟨488723, by rfl⟩ : syracuseStep 2606525 = 977447) B977447
theorem B3491261 : Blo 686314 3491261 := bstep (se 3 (by rfl) ⟨654611, by rfl⟩ : syracuseStep 3491261 = 1309223) B1309223
theorem B1033721 : Blo 686314 1033721 := bstep (se 2 (by rfl) ⟨387645, by rfl⟩ : syracuseStep 1033721 = 775291) B775291
theorem B1164793 : Blo 686314 1164793 := bstep (se 2 (by rfl) ⟨436797, by rfl⟩ : syracuseStep 1164793 = 873595) B873595
theorem B1033823 : Blo 686314 1033823 := bstep (se 1 (by rfl) ⟨775367, by rfl⟩ : syracuseStep 1033823 = 1550735) B1550735
theorem B2934407 : Blo 686314 2934407 := bstep (se 1 (by rfl) ⟨2200805, by rfl⟩ : syracuseStep 2934407 = 4401611) B4401611
theorem B2475677 : Blo 686314 2475677 := bstep (se 3 (by rfl) ⟨464189, by rfl⟩ : syracuseStep 2475677 = 928379) B928379
theorem B1034039 : Blo 686314 1034039 := bstep (se 1 (by rfl) ⟨775529, by rfl⟩ : syracuseStep 1034039 = 1551059) B1551059
theorem B2180951 : Blo 686314 2180951 := bstep (se 1 (by rfl) ⟨1635713, by rfl⟩ : syracuseStep 2180951 = 3271427) B3271427
theorem B6604649 : Blo 686314 6604649 := bstep (se 2 (by rfl) ⟨2476743, by rfl⟩ : syracuseStep 6604649 = 4953487) B4953487
theorem B6604877 : Blo 686314 6604877 := bstep (se 3 (by rfl) ⟨1238414, by rfl⟩ : syracuseStep 6604877 = 2476829) B2476829
theorem B1034345 : Blo 686314 1034345 := bstep (se 2 (by rfl) ⟨387879, by rfl⟩ : syracuseStep 1034345 = 775759) B775759
theorem B39799025 : Blo 686314 39799025 := bstep (se 2 (by rfl) ⟨14924634, by rfl⟩ : syracuseStep 39799025 = 29849269) B29849269
theorem B4409711 : Blo 686314 4409711 := bstep (se 1 (by rfl) ⟨3307283, by rfl⟩ : syracuseStep 4409711 = 6614567) B6614567
theorem B6605185 : Blo 686314 6605185 := bstep (se 2 (by rfl) ⟨2476944, by rfl⟩ : syracuseStep 6605185 = 4953889) B4953889
theorem B772519 : Blo 686314 772519 := bstep (se 1 (by rfl) ⟨579389, by rfl⟩ : syracuseStep 772519 = 1158779) B1158779
theorem B1034663 : Blo 686314 1034663 := bstep (se 1 (by rfl) ⟨775997, by rfl⟩ : syracuseStep 1034663 = 1551995) B1551995
theorem B870907 : Blo 686314 870907 := bstep (se 1 (by rfl) ⟨653180, by rfl⟩ : syracuseStep 870907 = 1306361) B1306361
theorem B1034747 : Blo 686314 1034747 := bstep (se 1 (by rfl) ⟨776060, by rfl⟩ : syracuseStep 1034747 = 1552121) B1552121
theorem B1034873 : Blo 686314 1034873 := bstep (se 2 (by rfl) ⟨388077, by rfl⟩ : syracuseStep 1034873 = 776155) B776155
theorem B1034927 : Blo 686314 1034927 := bstep (se 1 (by rfl) ⟨776195, by rfl⟩ : syracuseStep 1034927 = 1552391) B1552391
theorem B3918557 : Blo 686314 3918557 := bstep (se 3 (by rfl) ⟨734729, by rfl⟩ : syracuseStep 3918557 = 1469459) B1469459
theorem B1034975 : Blo 686314 1034975 := bstep (se 1 (by rfl) ⟨776231, by rfl⟩ : syracuseStep 1034975 = 1552463) B1552463
theorem B2607997 : Blo 686314 2607997 := bstep (se 3 (by rfl) ⟨488999, by rfl⟩ : syracuseStep 2607997 = 977999) B977999
theorem B773095 : Blo 686314 773095 := bstep (se 1 (by rfl) ⟨579821, by rfl⟩ : syracuseStep 773095 = 1159643) B1159643
theorem B1035239 : Blo 686314 1035239 := bstep (se 1 (by rfl) ⟨776429, by rfl⟩ : syracuseStep 1035239 = 1552859) B1552859
theorem B871879 : Blo 686314 871879 := bstep (se 1 (by rfl) ⟨653909, by rfl⟩ : syracuseStep 871879 = 1307819) B1307819
theorem B27545507 : Blo 686314 27545507 := bstep (se 1 (by rfl) ⟨20659130, by rfl⟩ : syracuseStep 27545507 = 41318261) B41318261
theorem B8376425 : Blo 686314 8376425 := bstep (se 2 (by rfl) ⟨3141159, by rfl⟩ : syracuseStep 8376425 = 6282319) B6282319
theorem B872795 : Blo 686314 872795 := bstep (se 1 (by rfl) ⟨654596, by rfl⟩ : syracuseStep 872795 = 1309193) B1309193
theorem B1397321 : Blo 686314 1397321 := bstep (se 2 (by rfl) ⟨523995, by rfl⟩ : syracuseStep 1397321 = 1047991) B1047991
theorem B774751 : Blo 686314 774751 := bstep (se 1 (by rfl) ⟨581063, by rfl⟩ : syracuseStep 774751 = 1162127) B1162127
theorem B5231303 : Blo 686314 5231303 := bstep (se 1 (by rfl) ⟨3923477, by rfl⟩ : syracuseStep 5231303 = 7846955) B7846955
theorem B873271 : Blo 686314 873271 := bstep (se 1 (by rfl) ⟨654953, by rfl⟩ : syracuseStep 873271 = 1309907) B1309907
theorem B2479079 : Blo 686314 2479079 := bstep (se 1 (by rfl) ⟨1859309, by rfl⟩ : syracuseStep 2479079 = 3718619) B3718619
theorem B775903 : Blo 686314 775903 := bstep (se 1 (by rfl) ⟨581927, by rfl⟩ : syracuseStep 775903 = 1163855) B1163855
theorem B2480161 : Blo 686314 2480161 := bstep (se 2 (by rfl) ⟨930060, by rfl⟩ : syracuseStep 2480161 = 1860121) B1860121
theorem B3135617 : Blo 686314 3135617 := bstep (se 2 (by rfl) ⟨1175856, by rfl⟩ : syracuseStep 3135617 = 2351713) B2351713
theorem B2611385 : Blo 686314 2611385 := bstep (se 2 (by rfl) ⟨979269, by rfl⟩ : syracuseStep 2611385 = 1958539) B1958539
theorem B776479 : Blo 686314 776479 := bstep (se 1 (by rfl) ⟨582359, by rfl⟩ : syracuseStep 776479 = 1164719) B1164719
theorem B11917721 : Blo 686314 11917721 := bstep (se 2 (by rfl) ⟨4469145, by rfl⟩ : syracuseStep 11917721 = 8938291) B8938291
theorem B2480635 : Blo 686314 2480635 := bstep (se 1 (by rfl) ⟨1860476, by rfl⟩ : syracuseStep 2480635 = 3720953) B3720953
theorem B3299903 : Blo 686314 3299903 := bstep (se 1 (by rfl) ⟨2474927, by rfl⟩ : syracuseStep 3299903 = 4949855) B4949855
theorem B2939465 : Blo 686314 2939465 := bstep (se 2 (by rfl) ⟨1102299, by rfl⟩ : syracuseStep 2939465 = 2204599) B2204599
theorem B5888771 : Blo 686314 5888771 := bstep (se 1 (by rfl) ⟨4416578, by rfl⟩ : syracuseStep 5888771 = 8833157) B8833157
theorem B3300115 : Blo 686314 3300115 := bstep (se 1 (by rfl) ⟨2475086, by rfl⟩ : syracuseStep 3300115 = 4950173) B4950173
theorem B2939773 : Blo 686314 2939773 := bstep (se 3 (by rfl) ⟨551207, by rfl⟩ : syracuseStep 2939773 = 1102415) B1102415
theorem B3922931 : Blo 686314 3922931 := bstep (se 1 (by rfl) ⟨2942198, by rfl⟩ : syracuseStep 3922931 = 5884397) B5884397
theorem B7167005 : Blo 686314 7167005 := bstep (se 3 (by rfl) ⟨1343813, by rfl⟩ : syracuseStep 7167005 = 2687627) B2687627
theorem B6806851 : Blo 686314 6806851 := bstep (se 1 (by rfl) ⟨5105138, by rfl⟩ : syracuseStep 6806851 = 10210277) B10210277
theorem B5889833 : Blo 686314 5889833 := bstep (se 2 (by rfl) ⟨2208687, by rfl⟩ : syracuseStep 5889833 = 4417375) B4417375
theorem B6283169 : Blo 686314 6283169 := bstep (se 2 (by rfl) ⟨2356188, by rfl⟩ : syracuseStep 6283169 = 4712377) B4712377
theorem B8708147 : Blo 686314 8708147 := bstep (se 1 (by rfl) ⟨6531110, by rfl⟩ : syracuseStep 8708147 = 13062221) B13062221
theorem B3924389 : Blo 686314 3924389 := bstep (se 4 (by rfl) ⟨367911, by rfl⟩ : syracuseStep 3924389 = 735823) B735823
theorem B3727873 : Blo 686314 3727873 := bstep (se 2 (by rfl) ⟨1397952, by rfl⟩ : syracuseStep 3727873 = 2795905) B2795905
theorem B2318867 : Blo 686314 2318867 := bstep (se 1 (by rfl) ⟨1739150, by rfl⟩ : syracuseStep 2318867 = 3478301) B3478301
theorem B1303103 : Blo 686314 1303103 := bstep (se 1 (by rfl) ⟨977327, by rfl⟩ : syracuseStep 1303103 = 1954655) B1954655
theorem B1860175 : Blo 686314 1860175 := bstep (se 1 (by rfl) ⟨1395131, by rfl⟩ : syracuseStep 1860175 = 2790263) B2790263
theorem B3302363 : Blo 686314 3302363 := bstep (se 1 (by rfl) ⟨2476772, by rfl⟩ : syracuseStep 3302363 = 4953545) B4953545
theorem B1303543 : Blo 686314 1303543 := bstep (se 1 (by rfl) ⟨977657, by rfl⟩ : syracuseStep 1303543 = 1955315) B1955315
theorem B31745125 : Blo 686314 31745125 := bstep (se 4 (by rfl) ⟨2976105, by rfl⟩ : syracuseStep 31745125 = 5952211) B5952211
theorem B1303771 : Blo 686314 1303771 := bstep (se 1 (by rfl) ⟨977828, by rfl⟩ : syracuseStep 1303771 = 1955657) B1955657
theorem B3302633 : Blo 686314 3302633 := bstep (se 2 (by rfl) ⟨1238487, by rfl⟩ : syracuseStep 3302633 = 2476975) B2476975
theorem B1303847 : Blo 686314 1303847 := bstep (se 1 (by rfl) ⟨977885, by rfl⟩ : syracuseStep 1303847 = 1955771) B1955771
theorem B1303931 : Blo 686314 1303931 := bstep (se 1 (by rfl) ⟨977948, by rfl⟩ : syracuseStep 1303931 = 1955897) B1955897
theorem B3729083 : Blo 686314 3729083 := bstep (se 1 (by rfl) ⟨2796812, by rfl⟩ : syracuseStep 3729083 = 5593625) B5593625
theorem B1763129 : Blo 686314 1763129 := bstep (se 2 (by rfl) ⟨661173, by rfl⟩ : syracuseStep 1763129 = 1322347) B1322347
theorem B3729239 : Blo 686314 3729239 := bstep (se 1 (by rfl) ⟨2796929, by rfl⟩ : syracuseStep 3729239 = 5593859) B5593859
theorem B3729257 : Blo 686314 3729257 := bstep (se 2 (by rfl) ⟨1398471, by rfl⟩ : syracuseStep 3729257 = 2796943) B2796943
theorem B14903189 : Blo 686314 14903189 := bstep (se 6 (by rfl) ⟨349293, by rfl⟩ : syracuseStep 14903189 = 698587) B698587
theorem B2320649 : Blo 686314 2320649 := bstep (se 2 (by rfl) ⟨870243, by rfl⟩ : syracuseStep 2320649 = 1740487) B1740487
theorem B2615561 : Blo 686314 2615561 := bstep (se 2 (by rfl) ⟨980835, by rfl⟩ : syracuseStep 2615561 = 1961671) B1961671
theorem B4974857 : Blo 686314 4974857 := bstep (se 2 (by rfl) ⟨1865571, by rfl⟩ : syracuseStep 4974857 = 3731143) B3731143
theorem B6285605 : Blo 686314 6285605 := bstep (se 4 (by rfl) ⟨589275, by rfl⟩ : syracuseStep 6285605 = 1178551) B1178551
theorem B3729775 : Blo 686314 3729775 := bstep (se 1 (by rfl) ⟨2797331, by rfl⟩ : syracuseStep 3729775 = 5594663) B5594663
theorem B3303823 : Blo 686314 3303823 := bstep (se 1 (by rfl) ⟨2477867, by rfl⟩ : syracuseStep 3303823 = 4955735) B4955735
theorem B5237135 : Blo 686314 5237135 := bstep (se 1 (by rfl) ⟨3927851, by rfl⟩ : syracuseStep 5237135 = 7855703) B7855703
theorem B3140471 : Blo 686314 3140471 := bstep (se 1 (by rfl) ⟨2355353, by rfl⟩ : syracuseStep 3140471 = 4710707) B4710707
theorem B31878157 : Blo 686314 31878157 := bstep (se 3 (by rfl) ⟨5977154, by rfl⟩ : syracuseStep 31878157 = 11954309) B11954309
theorem B4975631 : Blo 686314 4975631 := bstep (se 1 (by rfl) ⟨3731723, by rfl⟩ : syracuseStep 4975631 = 7463447) B7463447
theorem B2321783 : Blo 686314 2321783 := bstep (se 1 (by rfl) ⟨1741337, by rfl⟩ : syracuseStep 2321783 = 3482675) B3482675
theorem B1469819 : Blo 686314 1469819 := bstep (se 1 (by rfl) ⟨1102364, by rfl⟩ : syracuseStep 1469819 = 2204729) B2204729
theorem B978313 : Blo 686314 978313 := bstep (se 2 (by rfl) ⟨366867, by rfl⟩ : syracuseStep 978313 = 733735) B733735
theorem B1764769 : Blo 686314 1764769 := bstep (se 2 (by rfl) ⟨661788, by rfl⟩ : syracuseStep 1764769 = 1323577) B1323577
theorem B3927761 : Blo 686314 3927761 := bstep (se 2 (by rfl) ⟨1472910, by rfl⟩ : syracuseStep 3927761 = 2945821) B2945821
theorem B2617217 : Blo 686314 2617217 := bstep (se 2 (by rfl) ⟨981456, by rfl⟩ : syracuseStep 2617217 = 1962913) B1962913
theorem B1241039 : Blo 686314 1241039 := bstep (se 1 (by rfl) ⟨930779, by rfl⟩ : syracuseStep 1241039 = 1861559) B1861559
theorem B6615107 : Blo 686314 6615107 := bstep (se 1 (by rfl) ⟨4961330, by rfl⟩ : syracuseStep 6615107 = 9922661) B9922661
theorem B5304649 : Blo 686314 5304649 := bstep (se 2 (by rfl) ⟨1989243, by rfl⟩ : syracuseStep 5304649 = 3978487) B3978487
theorem B1306991 : Blo 686314 1306991 := bstep (se 1 (by rfl) ⟨980243, by rfl⟩ : syracuseStep 1306991 = 1960487) B1960487
theorem B2322863 : Blo 686314 2322863 := bstep (se 1 (by rfl) ⟨1742147, by rfl⟩ : syracuseStep 2322863 = 3484295) B3484295
theorem B1176239 : Blo 686314 1176239 := bstep (se 1 (by rfl) ⟨882179, by rfl⟩ : syracuseStep 1176239 = 1764359) B1764359
theorem B5894855 : Blo 686314 5894855 := bstep (se 1 (by rfl) ⟨4421141, by rfl⟩ : syracuseStep 5894855 = 8842283) B8842283
theorem B6615917 : Blo 686314 6615917 := bstep (se 3 (by rfl) ⟨1240484, by rfl⟩ : syracuseStep 6615917 = 2480969) B2480969
theorem B979867 : Blo 686314 979867 := bstep (se 1 (by rfl) ⟨734900, by rfl⟩ : syracuseStep 979867 = 1469801) B1469801
theorem B1471783 : Blo 686314 1471783 := bstep (se 1 (by rfl) ⟨1103837, by rfl⟩ : syracuseStep 1471783 = 2207675) B2207675
theorem B4781351 : Blo 686314 4781351 := bstep (se 1 (by rfl) ⟨3586013, by rfl⟩ : syracuseStep 4781351 = 7172027) B7172027
theorem B1308001 : Blo 686314 1308001 := bstep (se 2 (by rfl) ⟨490500, by rfl⟩ : syracuseStep 1308001 = 981001) B981001
theorem B2323835 : Blo 686314 2323835 := bstep (se 1 (by rfl) ⟨1742876, by rfl⟩ : syracuseStep 2323835 = 3485753) B3485753
theorem B1963403 : Blo 686314 1963403 := bstep (se 1 (by rfl) ⟨1472552, by rfl⟩ : syracuseStep 1963403 = 2945105) B2945105
theorem B6289181 : Blo 686314 6289181 := bstep (se 3 (by rfl) ⟨1179221, by rfl⟩ : syracuseStep 6289181 = 2358443) B2358443
theorem B686367 : Blo 686314 686367 := bstep (se 1 (by rfl) ⟨514775, by rfl⟩ : syracuseStep 686367 = 1029551) B1029551
theorem B686427 : Blo 686314 686427 := bstep (se 1 (by rfl) ⟨514820, by rfl⟩ : syracuseStep 686427 = 1029641) B1029641
theorem B686447 : Blo 686314 686447 := bstep (se 1 (by rfl) ⟨514835, by rfl⟩ : syracuseStep 686447 = 1029671) B1029671
theorem B686503 : Blo 686314 686503 := bstep (se 1 (by rfl) ⟨514877, by rfl⟩ : syracuseStep 686503 = 1029755) B1029755
theorem B686587 : Blo 686314 686587 := bstep (se 1 (by rfl) ⟨514940, by rfl⟩ : syracuseStep 686587 = 1029881) B1029881
theorem B686655 : Blo 686314 686655 := bstep (se 1 (by rfl) ⟨514991, by rfl⟩ : syracuseStep 686655 = 1029983) B1029983
theorem B686663 : Blo 686314 686663 := bstep (se 1 (by rfl) ⟨514997, by rfl⟩ : syracuseStep 686663 = 1029995) B1029995
theorem B3308111 : Blo 686314 3308111 := bstep (se 1 (by rfl) ⟨2481083, by rfl⟩ : syracuseStep 3308111 = 4962167) B4962167
theorem B686815 : Blo 686314 686815 := bstep (se 1 (by rfl) ⟨515111, by rfl⟩ : syracuseStep 686815 = 1030223) B1030223
theorem B2325239 : Blo 686314 2325239 := bstep (se 1 (by rfl) ⟨1743929, by rfl⟩ : syracuseStep 2325239 = 3487859) B3487859
theorem B1309459 : Blo 686314 1309459 := bstep (se 1 (by rfl) ⟨982094, by rfl⟩ : syracuseStep 1309459 = 1964189) B1964189
theorem B686895 : Blo 686314 686895 := bstep (se 1 (by rfl) ⟨515171, by rfl⟩ : syracuseStep 686895 = 1030343) B1030343
theorem B687003 : Blo 686314 687003 := bstep (se 1 (by rfl) ⟨515252, by rfl⟩ : syracuseStep 687003 = 1030505) B1030505
theorem B687055 : Blo 686314 687055 := bstep (se 1 (by rfl) ⟨515291, by rfl⟩ : syracuseStep 687055 = 1030583) B1030583
theorem B687079 : Blo 686314 687079 := bstep (se 1 (by rfl) ⟨515309, by rfl⟩ : syracuseStep 687079 = 1030619) B1030619
theorem B5897245 : Blo 686314 5897245 := bstep (se 3 (by rfl) ⟨1105733, by rfl⟩ : syracuseStep 5897245 = 2211467) B2211467
theorem B7044259 : Blo 686314 7044259 := bstep (se 1 (by rfl) ⟨5283194, by rfl⟩ : syracuseStep 7044259 = 10566389) B10566389
theorem B687391 : Blo 686314 687391 := bstep (se 1 (by rfl) ⟨515543, by rfl⟩ : syracuseStep 687391 = 1031087) B1031087
theorem B687451 : Blo 686314 687451 := bstep (se 1 (by rfl) ⟨515588, by rfl⟩ : syracuseStep 687451 = 1031177) B1031177
theorem B3308897 : Blo 686314 3308897 := bstep (se 2 (by rfl) ⟨1240836, by rfl⟩ : syracuseStep 3308897 = 2481673) B2481673
theorem B687471 : Blo 686314 687471 := bstep (se 1 (by rfl) ⟨515603, by rfl⟩ : syracuseStep 687471 = 1031207) B1031207
theorem B2948471 : Blo 686314 2948471 := bstep (se 1 (by rfl) ⟨2211353, by rfl⟩ : syracuseStep 2948471 = 4422707) B4422707
theorem B1310089 : Blo 686314 1310089 := bstep (se 2 (by rfl) ⟨491283, by rfl⟩ : syracuseStep 1310089 = 982567) B982567
theorem B687527 : Blo 686314 687527 := bstep (se 1 (by rfl) ⟨515645, by rfl⟩ : syracuseStep 687527 = 1031291) B1031291
theorem B687611 : Blo 686314 687611 := bstep (se 1 (by rfl) ⟨515708, by rfl⟩ : syracuseStep 687611 = 1031417) B1031417
theorem B687679 : Blo 686314 687679 := bstep (se 1 (by rfl) ⟨515759, by rfl⟩ : syracuseStep 687679 = 1031519) B1031519
theorem B687687 : Blo 686314 687687 := bstep (se 1 (by rfl) ⟨515765, by rfl⟩ : syracuseStep 687687 = 1031531) B1031531
theorem B884407 : Blo 686314 884407 := bstep (se 1 (by rfl) ⟨663305, by rfl⟩ : syracuseStep 884407 = 1326611) B1326611
theorem B687839 : Blo 686314 687839 := bstep (se 1 (by rfl) ⟨515879, by rfl⟩ : syracuseStep 687839 = 1031759) B1031759
theorem B687919 : Blo 686314 687919 := bstep (se 1 (by rfl) ⟨515939, by rfl⟩ : syracuseStep 687919 = 1031879) B1031879
theorem B2326319 : Blo 686314 2326319 := bstep (se 1 (by rfl) ⟨1744739, by rfl⟩ : syracuseStep 2326319 = 3489479) B3489479
theorem B688027 : Blo 686314 688027 := bstep (se 1 (by rfl) ⟨516020, by rfl⟩ : syracuseStep 688027 = 1032041) B1032041
theorem B688079 : Blo 686314 688079 := bstep (se 1 (by rfl) ⟨516059, by rfl⟩ : syracuseStep 688079 = 1032119) B1032119
theorem B688103 : Blo 686314 688103 := bstep (se 1 (by rfl) ⟨516077, by rfl⟩ : syracuseStep 688103 = 1032155) B1032155
theorem B688359 : Blo 686314 688359 := bstep (se 1 (by rfl) ⟨516269, by rfl⟩ : syracuseStep 688359 = 1032539) B1032539
theorem B688511 : Blo 686314 688511 := bstep (se 1 (by rfl) ⟨516383, by rfl⟩ : syracuseStep 688511 = 1032767) B1032767
theorem B4030895 : Blo 686314 4030895 := bstep (se 1 (by rfl) ⟨3023171, by rfl⟩ : syracuseStep 4030895 = 6046343) B6046343
theorem B2326967 : Blo 686314 2326967 := bstep (se 1 (by rfl) ⟨1745225, by rfl⟩ : syracuseStep 2326967 = 3490451) B3490451
theorem B688591 : Blo 686314 688591 := bstep (se 1 (by rfl) ⟨516443, by rfl⟩ : syracuseStep 688591 = 1032887) B1032887
theorem B8815067 : Blo 686314 8815067 := bstep (se 1 (by rfl) ⟨6611300, by rfl⟩ : syracuseStep 8815067 = 13222601) B13222601
theorem B688743 : Blo 686314 688743 := bstep (se 1 (by rfl) ⟨516557, by rfl⟩ : syracuseStep 688743 = 1033115) B1033115
theorem B6619913 : Blo 686314 6619913 := bstep (se 2 (by rfl) ⟨2482467, by rfl⟩ : syracuseStep 6619913 = 4964935) B4964935
theorem B689007 : Blo 686314 689007 := bstep (se 1 (by rfl) ⟨516755, by rfl⟩ : syracuseStep 689007 = 1033511) B1033511
theorem B2327453 : Blo 686314 2327453 := bstep (se 3 (by rfl) ⟨436397, by rfl⟩ : syracuseStep 2327453 = 872795) B872795
theorem B689063 : Blo 686314 689063 := bstep (se 1 (by rfl) ⟨516797, by rfl⟩ : syracuseStep 689063 = 1033595) B1033595
theorem B1737683 : Blo 686314 1737683 := bstep (se 1 (by rfl) ⟨1303262, by rfl⟩ : syracuseStep 1737683 = 2606525) B2606525
theorem B2327507 : Blo 686314 2327507 := bstep (se 1 (by rfl) ⟨1745630, by rfl⟩ : syracuseStep 2327507 = 3491261) B3491261
theorem B689147 : Blo 686314 689147 := bstep (se 1 (by rfl) ⟨516860, by rfl⟩ : syracuseStep 689147 = 1033721) B1033721
theorem B689215 : Blo 686314 689215 := bstep (se 1 (by rfl) ⟨516911, by rfl⟩ : syracuseStep 689215 = 1033823) B1033823
theorem B689359 : Blo 686314 689359 := bstep (se 1 (by rfl) ⟨517019, by rfl⟩ : syracuseStep 689359 = 1034039) B1034039
theorem B1738057 : Blo 686314 1738057 := bstep (se 2 (by rfl) ⟨651771, by rfl⟩ : syracuseStep 1738057 = 1303543) B1303543
theorem B689563 : Blo 686314 689563 := bstep (se 1 (by rfl) ⟨517172, by rfl⟩ : syracuseStep 689563 = 1034345) B1034345
theorem B689775 : Blo 686314 689775 := bstep (se 1 (by rfl) ⟨517331, by rfl⟩ : syracuseStep 689775 = 1034663) B1034663
theorem B1738361 : Blo 686314 1738361 := bstep (se 2 (by rfl) ⟨651885, by rfl⟩ : syracuseStep 1738361 = 1303771) B1303771
theorem B689831 : Blo 686314 689831 := bstep (se 1 (by rfl) ⟨517373, by rfl⟩ : syracuseStep 689831 = 1034747) B1034747
theorem B689915 : Blo 686314 689915 := bstep (se 1 (by rfl) ⟨517436, by rfl⟩ : syracuseStep 689915 = 1034873) B1034873
theorem B689951 : Blo 686314 689951 := bstep (se 1 (by rfl) ⟨517463, by rfl⟩ : syracuseStep 689951 = 1034927) B1034927
theorem B689983 : Blo 686314 689983 := bstep (se 1 (by rfl) ⟨517487, by rfl⟩ : syracuseStep 689983 = 1034975) B1034975
theorem B690159 : Blo 686314 690159 := bstep (se 1 (by rfl) ⟨517619, by rfl⟩ : syracuseStep 690159 = 1035239) B1035239
theorem B4720691 : Blo 686314 4720691 := bstep (se 1 (by rfl) ⟨3540518, by rfl⟩ : syracuseStep 4720691 = 7081037) B7081037
theorem B2329721 : Blo 686314 2329721 := bstep (se 2 (by rfl) ⟨873645, by rfl⟩ : syracuseStep 2329721 = 1747291) B1747291
theorem B6622715 : Blo 686314 6622715 := bstep (se 1 (by rfl) ⟨4967036, by rfl⟩ : syracuseStep 6622715 = 9934073) B9934073
theorem B3477167 : Blo 686314 3477167 := bstep (se 1 (by rfl) ⟨2607875, by rfl⟩ : syracuseStep 3477167 = 5215751) B5215751
theorem B9572039 : Blo 686314 9572039 := bstep (se 1 (by rfl) ⟨7179029, by rfl⟩ : syracuseStep 9572039 = 14358059) B14358059
theorem B3477329 : Blo 686314 3477329 := bstep (se 2 (by rfl) ⟨1303998, by rfl⟩ : syracuseStep 3477329 = 2607997) B2607997
theorem B42504209 : Blo 686314 42504209 := bstep (se 2 (by rfl) ⟨15939078, by rfl⟩ : syracuseStep 42504209 = 31878157) B31878157
theorem B1740923 : Blo 686314 1740923 := bstep (se 1 (by rfl) ⟨1305692, by rfl⟩ : syracuseStep 1740923 = 2611385) B2611385
theorem B2199935 : Blo 686314 2199935 := bstep (se 1 (by rfl) ⟨1649951, by rfl⟩ : syracuseStep 2199935 = 3299903) B3299903
theorem B2232703 : Blo 686314 2232703 := bstep (se 1 (by rfl) ⟨1674527, by rfl⟩ : syracuseStep 2232703 = 3349055) B3349055
theorem B3478139 : Blo 686314 3478139 := bstep (se 1 (by rfl) ⟨2608604, by rfl⟩ : syracuseStep 3478139 = 5217209) B5217209
theorem B5575979 : Blo 686314 5575979 := bstep (se 1 (by rfl) ⟨4181984, by rfl⟩ : syracuseStep 5575979 = 8363969) B8363969
theorem B5805431 : Blo 686314 5805431 := bstep (se 1 (by rfl) ⟨4354073, by rfl⟩ : syracuseStep 5805431 = 8708147) B8708147
theorem B1545911 : Blo 686314 1545911 := bstep (se 1 (by rfl) ⟨1159433, by rfl⟩ : syracuseStep 1545911 = 2318867) B2318867
theorem B2201575 : Blo 686314 2201575 := bstep (se 1 (by rfl) ⟨1651181, by rfl⟩ : syracuseStep 2201575 = 3302363) B3302363
theorem B2201755 : Blo 686314 2201755 := bstep (se 1 (by rfl) ⟨1651316, by rfl⟩ : syracuseStep 2201755 = 3302633) B3302633
theorem B6691019 : Blo 686314 6691019 := bstep (se 1 (by rfl) ⟨5018264, by rfl⟩ : syracuseStep 6691019 = 10036529) B10036529
theorem B9935459 : Blo 686314 9935459 := bstep (se 1 (by rfl) ⟨7451594, by rfl⟩ : syracuseStep 9935459 = 14903189) B14903189
theorem B1547099 : Blo 686314 1547099 := bstep (se 1 (by rfl) ⟨1160324, by rfl⟩ : syracuseStep 1547099 = 2320649) B2320649
theorem B1743707 : Blo 686314 1743707 := bstep (se 1 (by rfl) ⟨1307780, by rfl⟩ : syracuseStep 1743707 = 2615561) B2615561
theorem B3316571 : Blo 686314 3316571 := bstep (se 1 (by rfl) ⟨2487428, by rfl⟩ : syracuseStep 3316571 = 4974857) B4974857
theorem B1744001 : Blo 686314 1744001 := bstep (se 2 (by rfl) ⟨654000, by rfl⟩ : syracuseStep 1744001 = 1308001) B1308001
theorem B3317087 : Blo 686314 3317087 := bstep (se 1 (by rfl) ⟨2487815, by rfl⟩ : syracuseStep 3317087 = 4975631) B4975631
theorem B3349991 : Blo 686314 3349991 := bstep (se 1 (by rfl) ⟨2512493, by rfl⟩ : syracuseStep 3349991 = 5024987) B5024987
theorem B1547855 : Blo 686314 1547855 := bstep (se 1 (by rfl) ⟨1160891, by rfl⟩ : syracuseStep 1547855 = 2321783) B2321783
theorem B1744811 : Blo 686314 1744811 := bstep (se 1 (by rfl) ⟨1308608, by rfl⟩ : syracuseStep 1744811 = 2617217) B2617217
theorem B1548575 : Blo 686314 1548575 := bstep (se 1 (by rfl) ⟨1161431, by rfl⟩ : syracuseStep 1548575 = 2322863) B2322863
theorem B3187567 : Blo 686314 3187567 := bstep (se 1 (by rfl) ⟨2390675, by rfl⟩ : syracuseStep 3187567 = 4781351) B4781351
theorem B1549223 : Blo 686314 1549223 := bstep (se 1 (by rfl) ⟨1161917, by rfl⟩ : syracuseStep 1549223 = 2323835) B2323835
theorem B8823725 : Blo 686314 8823725 := bstep (se 3 (by rfl) ⟨1654448, by rfl⟩ : syracuseStep 8823725 = 3308897) B3308897
theorem B4400153 : Blo 686314 4400153 := bstep (se 2 (by rfl) ⟨1650057, by rfl⟩ : syracuseStep 4400153 = 3300115) B3300115
theorem B1745945 : Blo 686314 1745945 := bstep (se 2 (by rfl) ⟨654729, by rfl⟩ : syracuseStep 1745945 = 1309459) B1309459
theorem B2205407 : Blo 686314 2205407 := bstep (se 1 (by rfl) ⟨1654055, by rfl⟩ : syracuseStep 2205407 = 3308111) B3308111
theorem B1550159 : Blo 686314 1550159 := bstep (se 1 (by rfl) ⟨1162619, by rfl⟩ : syracuseStep 1550159 = 2325239) B2325239
theorem B1550177 : Blo 686314 1550177 := bstep (se 2 (by rfl) ⟨581316, by rfl⟩ : syracuseStep 1550177 = 1162633) B1162633
theorem B1746785 : Blo 686314 1746785 := bstep (se 2 (by rfl) ⟨655044, by rfl⟩ : syracuseStep 1746785 = 1310089) B1310089
theorem B1550753 : Blo 686314 1550753 := bstep (se 2 (by rfl) ⟨581532, by rfl⟩ : syracuseStep 1550753 = 1163065) B1163065
theorem B1550879 : Blo 686314 1550879 := bstep (se 1 (by rfl) ⟨1163159, by rfl⟩ : syracuseStep 1550879 = 2326319) B2326319
theorem B1158185 : Blo 686314 1158185 := bstep (se 2 (by rfl) ⟨434319, by rfl⟩ : syracuseStep 1158185 = 868639) B868639
theorem B699463 : Blo 686314 699463 := bstep (se 1 (by rfl) ⟨524597, by rfl⟩ : syracuseStep 699463 = 1049195) B1049195
theorem B5287133 : Blo 686314 5287133 := bstep (se 3 (by rfl) ⟨991337, by rfl⟩ : syracuseStep 5287133 = 1982675) B1982675
theorem B1158367 : Blo 686314 1158367 := bstep (se 1 (by rfl) ⟨868775, by rfl⟩ : syracuseStep 1158367 = 1737551) B1737551
theorem B2239721 : Blo 686314 2239721 := bstep (se 2 (by rfl) ⟨839895, by rfl⟩ : syracuseStep 2239721 = 1679791) B1679791
theorem B1158799 : Blo 686314 1158799 := bstep (se 1 (by rfl) ⟨869099, by rfl⟩ : syracuseStep 1158799 = 1738199) B1738199
theorem B1650451 : Blo 686314 1650451 := bstep (se 1 (by rfl) ⟨1237838, by rfl⟩ : syracuseStep 1650451 = 2475677) B2475677
theorem B1453967 : Blo 686314 1453967 := bstep (se 1 (by rfl) ⟨1090475, by rfl⟩ : syracuseStep 1453967 = 2180951) B2180951
theorem B4403099 : Blo 686314 4403099 := bstep (se 1 (by rfl) ⟨3302324, by rfl⟩ : syracuseStep 4403099 = 6604649) B6604649
theorem B1552283 : Blo 686314 1552283 := bstep (se 1 (by rfl) ⟨1164212, by rfl⟩ : syracuseStep 1552283 = 2328425) B2328425
theorem B4403251 : Blo 686314 4403251 := bstep (se 1 (by rfl) ⟨3302438, by rfl⟩ : syracuseStep 4403251 = 6604877) B6604877
theorem B1552571 : Blo 686314 1552571 := bstep (se 1 (by rfl) ⟨1164428, by rfl⟩ : syracuseStep 1552571 = 2328857) B2328857
theorem B1553057 : Blo 686314 1553057 := bstep (se 2 (by rfl) ⟨582396, by rfl⟩ : syracuseStep 1553057 = 1164793) B1164793
theorem B3912407 : Blo 686314 3912407 := bstep (se 1 (by rfl) ⟨2934305, by rfl⟩ : syracuseStep 3912407 = 5868611) B5868611
theorem B1160399 : Blo 686314 1160399 := bstep (se 1 (by rfl) ⟨870299, by rfl⟩ : syracuseStep 1160399 = 1740599) B1740599
theorem B18363671 : Blo 686314 18363671 := bstep (se 1 (by rfl) ⟨13772753, by rfl⟩ : syracuseStep 18363671 = 27545507) B27545507
theorem B5584283 : Blo 686314 5584283 := bstep (se 1 (by rfl) ⟨4188212, by rfl⟩ : syracuseStep 5584283 = 8376425) B8376425
theorem B4961735 : Blo 686314 4961735 := bstep (se 1 (by rfl) ⟨3721301, by rfl⟩ : syracuseStep 4961735 = 7442603) B7442603
theorem B1029743 : Blo 686314 1029743 := bstep (se 1 (by rfl) ⟨772307, by rfl⟩ : syracuseStep 1029743 = 1544615) B1544615
theorem B1029815 : Blo 686314 1029815 := bstep (se 1 (by rfl) ⟨772361, by rfl⟩ : syracuseStep 1029815 = 1544723) B1544723
theorem B1029851 : Blo 686314 1029851 := bstep (se 1 (by rfl) ⟨772388, by rfl⟩ : syracuseStep 1029851 = 1544777) B1544777
theorem B931547 : Blo 686314 931547 := bstep (se 1 (by rfl) ⟨698660, by rfl⟩ : syracuseStep 931547 = 1397321) B1397321
theorem B3487535 : Blo 686314 3487535 := bstep (se 1 (by rfl) ⟨2615651, by rfl⟩ : syracuseStep 3487535 = 5231303) B5231303
theorem B4405097 : Blo 686314 4405097 := bstep (se 2 (by rfl) ⟨1651911, by rfl⟩ : syracuseStep 4405097 = 3303823) B3303823
theorem B1030025 : Blo 686314 1030025 := bstep (se 2 (by rfl) ⟨386259, by rfl⟩ : syracuseStep 1030025 = 772519) B772519
theorem B2209751 : Blo 686314 2209751 := bstep (se 1 (by rfl) ⟨1657313, by rfl⟩ : syracuseStep 2209751 = 3314627) B3314627
theorem B1030127 : Blo 686314 1030127 := bstep (se 1 (by rfl) ⟨772595, by rfl⟩ : syracuseStep 1030127 = 1545191) B1545191
theorem B1652719 : Blo 686314 1652719 := bstep (se 1 (by rfl) ⟨1239539, by rfl⟩ : syracuseStep 1652719 = 2479079) B2479079
theorem B1161209 : Blo 686314 1161209 := bstep (se 2 (by rfl) ⟨435453, by rfl⟩ : syracuseStep 1161209 = 870907) B870907
theorem B1161371 : Blo 686314 1161371 := bstep (se 1 (by rfl) ⟨871028, by rfl⟩ : syracuseStep 1161371 = 1742057) B1742057
theorem B1030379 : Blo 686314 1030379 := bstep (se 1 (by rfl) ⟨772784, by rfl⟩ : syracuseStep 1030379 = 1545569) B1545569
theorem B1161479 : Blo 686314 1161479 := bstep (se 1 (by rfl) ⟨871109, by rfl⟩ : syracuseStep 1161479 = 1742219) B1742219
theorem B1030439 : Blo 686314 1030439 := bstep (se 1 (by rfl) ⟨772829, by rfl⟩ : syracuseStep 1030439 = 1545659) B1545659
theorem B1030523 : Blo 686314 1030523 := bstep (se 1 (by rfl) ⟨772892, by rfl⟩ : syracuseStep 1030523 = 1545785) B1545785
theorem B5454253 : Blo 686314 5454253 := bstep (se 3 (by rfl) ⟨1022672, by rfl⟩ : syracuseStep 5454253 = 2045345) B2045345
theorem B12270197 : Blo 686314 12270197 := bstep (se 5 (by rfl) ⟨575165, by rfl⟩ : syracuseStep 12270197 = 1150331) B1150331
theorem B1030793 : Blo 686314 1030793 := bstep (se 2 (by rfl) ⟨386547, by rfl⟩ : syracuseStep 1030793 = 773095) B773095
theorem B1030967 : Blo 686314 1030967 := bstep (se 1 (by rfl) ⟨773225, by rfl⟩ : syracuseStep 1030967 = 1546451) B1546451
theorem B1162039 : Blo 686314 1162039 := bstep (se 1 (by rfl) ⟨871529, by rfl⟩ : syracuseStep 1162039 = 1743059) B1743059
theorem B1031003 : Blo 686314 1031003 := bstep (se 1 (by rfl) ⟨773252, by rfl⟩ : syracuseStep 1031003 = 1546505) B1546505
theorem B7945147 : Blo 686314 7945147 := bstep (se 1 (by rfl) ⟨5958860, by rfl⟩ : syracuseStep 7945147 = 11917721) B11917721
theorem B1031147 : Blo 686314 1031147 := bstep (se 1 (by rfl) ⟨773360, by rfl⟩ : syracuseStep 1031147 = 1546721) B1546721
theorem B9944221 : Blo 686314 9944221 := bstep (se 3 (by rfl) ⟨1864541, by rfl⟩ : syracuseStep 9944221 = 3729083) B3729083
theorem B1031351 : Blo 686314 1031351 := bstep (se 1 (by rfl) ⟨773513, by rfl⟩ : syracuseStep 1031351 = 1547027) B1547027
theorem B1162505 : Blo 686314 1162505 := bstep (se 2 (by rfl) ⟨435939, by rfl⟩ : syracuseStep 1162505 = 871879) B871879
theorem B1031591 : Blo 686314 1031591 := bstep (se 1 (by rfl) ⟨773693, by rfl⟩ : syracuseStep 1031591 = 1547387) B1547387
theorem B5225957 : Blo 686314 5225957 := bstep (se 4 (by rfl) ⟨489933, by rfl⟩ : syracuseStep 5225957 = 979867) B979867
theorem B1031675 : Blo 686314 1031675 := bstep (se 1 (by rfl) ⟨773756, by rfl⟩ : syracuseStep 1031675 = 1547513) B1547513
theorem B1031771 : Blo 686314 1031771 := bstep (se 1 (by rfl) ⟨773828, by rfl⟩ : syracuseStep 1031771 = 1547657) B1547657
theorem B1031855 : Blo 686314 1031855 := bstep (se 1 (by rfl) ⟨773891, by rfl⟩ : syracuseStep 1031855 = 1547783) B1547783
theorem B1031975 : Blo 686314 1031975 := bstep (se 1 (by rfl) ⟨773981, by rfl⟩ : syracuseStep 1031975 = 1547963) B1547963
theorem B1032059 : Blo 686314 1032059 := bstep (se 1 (by rfl) ⟨774044, by rfl⟩ : syracuseStep 1032059 = 1548089) B1548089
theorem B1032479 : Blo 686314 1032479 := bstep (se 1 (by rfl) ⟨774359, by rfl⟩ : syracuseStep 1032479 = 1548719) B1548719
theorem B1163551 : Blo 686314 1163551 := bstep (se 1 (by rfl) ⟨872663, by rfl⟩ : syracuseStep 1163551 = 1745327) B1745327
theorem B1032503 : Blo 686314 1032503 := bstep (se 1 (by rfl) ⟨774377, by rfl⟩ : syracuseStep 1032503 = 1548755) B1548755
theorem B868735 : Blo 686314 868735 := bstep (se 1 (by rfl) ⟨651551, by rfl⟩ : syracuseStep 868735 = 1303103) B1303103
theorem B1032575 : Blo 686314 1032575 := bstep (se 1 (by rfl) ⟨774431, by rfl⟩ : syracuseStep 1032575 = 1548863) B1548863
theorem B1032647 : Blo 686314 1032647 := bstep (se 1 (by rfl) ⟨774485, by rfl⟩ : syracuseStep 1032647 = 1548971) B1548971
theorem B16761613 : Blo 686314 16761613 := bstep (se 3 (by rfl) ⟨3142802, by rfl⟩ : syracuseStep 16761613 = 6285605) B6285605
theorem B1033001 : Blo 686314 1033001 := bstep (se 2 (by rfl) ⟨387375, by rfl⟩ : syracuseStep 1033001 = 774751) B774751
theorem B2605871 : Blo 686314 2605871 := bstep (se 1 (by rfl) ⟨1954403, by rfl⟩ : syracuseStep 2605871 = 3908807) B3908807
theorem B1033007 : Blo 686314 1033007 := bstep (se 1 (by rfl) ⟨774755, by rfl⟩ : syracuseStep 1033007 = 1549511) B1549511
theorem B869231 : Blo 686314 869231 := bstep (se 1 (by rfl) ⟨651923, by rfl⟩ : syracuseStep 869231 = 1303847) B1303847
theorem B869287 : Blo 686314 869287 := bstep (se 1 (by rfl) ⟨651965, by rfl⟩ : syracuseStep 869287 = 1303931) B1303931
theorem B1033127 : Blo 686314 1033127 := bstep (se 1 (by rfl) ⟨774845, by rfl⟩ : syracuseStep 1033127 = 1549691) B1549691
theorem B1164199 : Blo 686314 1164199 := bstep (se 1 (by rfl) ⟨873149, by rfl⟩ : syracuseStep 1164199 = 1746299) B1746299
theorem B1033211 : Blo 686314 1033211 := bstep (se 1 (by rfl) ⟨774908, by rfl⟩ : syracuseStep 1033211 = 1549817) B1549817
theorem B1033271 : Blo 686314 1033271 := bstep (se 1 (by rfl) ⟨774953, by rfl⟩ : syracuseStep 1033271 = 1549907) B1549907
theorem B1164361 : Blo 686314 1164361 := bstep (se 2 (by rfl) ⟨436635, by rfl⟩ : syracuseStep 1164361 = 873271) B873271
theorem B1164395 : Blo 686314 1164395 := bstep (se 1 (by rfl) ⟨873296, by rfl⟩ : syracuseStep 1164395 = 1746593) B1746593
theorem B1033391 : Blo 686314 1033391 := bstep (se 1 (by rfl) ⟨775043, by rfl⟩ : syracuseStep 1033391 = 1550087) B1550087
theorem B2475215 : Blo 686314 2475215 := bstep (se 1 (by rfl) ⟨1856411, by rfl⟩ : syracuseStep 2475215 = 3712823) B3712823
theorem B53495113 : Blo 686314 53495113 := bstep (se 2 (by rfl) ⟨20060667, by rfl⟩ : syracuseStep 53495113 = 40121335) B40121335
theorem B145212821 : Blo 686314 145212821 := bstep (se 6 (by rfl) ⟨3403425, by rfl⟩ : syracuseStep 145212821 = 6806851) B6806851
theorem B1033799 : Blo 686314 1033799 := bstep (se 1 (by rfl) ⟨775349, by rfl⟩ : syracuseStep 1033799 = 1550699) B1550699
theorem B3491423 : Blo 686314 3491423 := bstep (se 1 (by rfl) ⟨2618567, by rfl⟩ : syracuseStep 3491423 = 5237135) B5237135
theorem B1033895 : Blo 686314 1033895 := bstep (se 1 (by rfl) ⟨775421, by rfl⟩ : syracuseStep 1033895 = 1550843) B1550843
theorem B1033979 : Blo 686314 1033979 := bstep (se 1 (by rfl) ⟨775484, by rfl⟩ : syracuseStep 1033979 = 1550969) B1550969
theorem B1034015 : Blo 686314 1034015 := bstep (se 1 (by rfl) ⟨775511, by rfl⟩ : syracuseStep 1034015 = 1551023) B1551023
theorem B1099583 : Blo 686314 1099583 := bstep (se 1 (by rfl) ⟨824687, by rfl⟩ : syracuseStep 1099583 = 1649375) B1649375
theorem B1034063 : Blo 686314 1034063 := bstep (se 1 (by rfl) ⟨775547, by rfl⟩ : syracuseStep 1034063 = 1551095) B1551095
theorem B1034183 : Blo 686314 1034183 := bstep (se 1 (by rfl) ⟨775637, by rfl⟩ : syracuseStep 1034183 = 1551275) B1551275
theorem B1034537 : Blo 686314 1034537 := bstep (se 2 (by rfl) ⟨387951, by rfl⟩ : syracuseStep 1034537 = 775903) B775903
theorem B1034543 : Blo 686314 1034543 := bstep (se 1 (by rfl) ⟨775907, by rfl⟩ : syracuseStep 1034543 = 1551815) B1551815
theorem B1034783 : Blo 686314 1034783 := bstep (se 1 (by rfl) ⟨776087, by rfl⟩ : syracuseStep 1034783 = 1552175) B1552175
theorem B22268627 : Blo 686314 22268627 := bstep (se 1 (by rfl) ⟨16701470, by rfl⟩ : syracuseStep 22268627 = 33402941) B33402941
theorem B4410071 : Blo 686314 4410071 := bstep (se 1 (by rfl) ⟨3307553, by rfl⟩ : syracuseStep 4410071 = 6615107) B6615107
theorem B773023 : Blo 686314 773023 := bstep (se 1 (by rfl) ⟨579767, by rfl⟩ : syracuseStep 773023 = 1159535) B1159535
theorem B871327 : Blo 686314 871327 := bstep (se 1 (by rfl) ⟨653495, by rfl⟩ : syracuseStep 871327 = 1306991) B1306991
theorem B1035167 : Blo 686314 1035167 := bstep (se 1 (by rfl) ⟨776375, by rfl⟩ : syracuseStep 1035167 = 1552751) B1552751
theorem B1035215 : Blo 686314 1035215 := bstep (se 1 (by rfl) ⟨776411, by rfl⟩ : syracuseStep 1035215 = 1552823) B1552823
theorem B1035305 : Blo 686314 1035305 := bstep (se 2 (by rfl) ⟨388239, by rfl⟩ : syracuseStep 1035305 = 776479) B776479
theorem B773167 : Blo 686314 773167 := bstep (se 1 (by rfl) ⟨579875, by rfl⟩ : syracuseStep 773167 = 1159751) B1159751
theorem B1035311 : Blo 686314 1035311 := bstep (se 1 (by rfl) ⟨776483, by rfl⟩ : syracuseStep 1035311 = 1552967) B1552967
theorem B1035335 : Blo 686314 1035335 := bstep (se 1 (by rfl) ⟨776501, by rfl⟩ : syracuseStep 1035335 = 1553003) B1553003
theorem B3919013 : Blo 686314 3919013 := bstep (se 4 (by rfl) ⟨367407, by rfl⟩ : syracuseStep 3919013 = 734815) B734815
theorem B2477279 : Blo 686314 2477279 := bstep (se 1 (by rfl) ⟨1857959, by rfl⟩ : syracuseStep 2477279 = 3715919) B3715919
theorem B4410611 : Blo 686314 4410611 := bstep (se 1 (by rfl) ⟨3307958, by rfl⟩ : syracuseStep 4410611 = 6615917) B6615917
theorem B773455 : Blo 686314 773455 := bstep (se 1 (by rfl) ⟨580091, by rfl⟩ : syracuseStep 773455 = 1160183) B1160183
theorem B1101223 : Blo 686314 1101223 := bstep (se 1 (by rfl) ⟨825917, by rfl⟩ : syracuseStep 1101223 = 1651835) B1651835
theorem B773959 : Blo 686314 773959 := bstep (se 1 (by rfl) ⟨580469, by rfl⟩ : syracuseStep 773959 = 1160939) B1160939
theorem B3919697 : Blo 686314 3919697 := bstep (se 2 (by rfl) ⟨1469886, by rfl⟩ : syracuseStep 3919697 = 2939773) B2939773
theorem B9392345 : Blo 686314 9392345 := bstep (se 2 (by rfl) ⟨3522129, by rfl⟩ : syracuseStep 9392345 = 7044259) B7044259
theorem B1102043 : Blo 686314 1102043 := bstep (se 1 (by rfl) ⟨826532, by rfl⟩ : syracuseStep 1102043 = 1653065) B1653065
theorem B7459037 : Blo 686314 7459037 := bstep (se 3 (by rfl) ⟨1398569, by rfl⟩ : syracuseStep 7459037 = 2797139) B2797139
theorem B774607 : Blo 686314 774607 := bstep (se 1 (by rfl) ⟨580955, by rfl⟩ : syracuseStep 774607 = 1161911) B1161911
theorem B2609759 : Blo 686314 2609759 := bstep (se 1 (by rfl) ⟨1957319, by rfl⟩ : syracuseStep 2609759 = 3914639) B3914639
theorem B4182623 : Blo 686314 4182623 := bstep (se 1 (by rfl) ⟨3136967, by rfl⟩ : syracuseStep 4182623 = 6273935) B6273935
theorem B2610215 : Blo 686314 2610215 := bstep (se 1 (by rfl) ⟨1957661, by rfl⟩ : syracuseStep 2610215 = 3915323) B3915323
theorem B2938031 : Blo 686314 2938031 := bstep (se 1 (by rfl) ⟨2203523, by rfl⟩ : syracuseStep 2938031 = 4407047) B4407047
theorem B13391243 : Blo 686314 13391243 := bstep (se 1 (by rfl) ⟨10043432, by rfl⟩ : syracuseStep 13391243 = 20086865) B20086865
theorem B775579 : Blo 686314 775579 := bstep (se 1 (by rfl) ⟨581684, by rfl⟩ : syracuseStep 775579 = 1163369) B1163369
theorem B3299287 : Blo 686314 3299287 := bstep (se 1 (by rfl) ⟨2474465, by rfl⟩ : syracuseStep 3299287 = 4948931) B4948931
theorem B1103863 : Blo 686314 1103863 := bstep (se 1 (by rfl) ⟨827897, by rfl⟩ : syracuseStep 1103863 = 1655795) B1655795
theorem B4970497 : Blo 686314 4970497 := bstep (se 2 (by rfl) ⟨1863936, by rfl⟩ : syracuseStep 4970497 = 3727873) B3727873
theorem B2316383 : Blo 686314 2316383 := bstep (se 1 (by rfl) ⟨1737287, by rfl⟩ : syracuseStep 2316383 = 3474575) B3474575
theorem B2480233 : Blo 686314 2480233 := bstep (se 2 (by rfl) ⟨930087, by rfl⟩ : syracuseStep 2480233 = 1860175) B1860175
theorem B2611399 : Blo 686314 2611399 := bstep (se 1 (by rfl) ⟨1958549, by rfl⟩ : syracuseStep 2611399 = 3917099) B3917099
theorem B42326833 : Blo 686314 42326833 := bstep (se 2 (by rfl) ⟨15872562, by rfl⟩ : syracuseStep 42326833 = 31745125) B31745125
theorem B26532683 : Blo 686314 26532683 := bstep (se 1 (by rfl) ⟨19899512, by rfl⟩ : syracuseStep 26532683 = 39799025) B39799025
theorem B2317139 : Blo 686314 2317139 := bstep (se 1 (by rfl) ⟨1737854, by rfl⟩ : syracuseStep 2317139 = 3475709) B3475709
theorem B2939807 : Blo 686314 2939807 := bstep (se 1 (by rfl) ⟨2204855, by rfl⟩ : syracuseStep 2939807 = 4409711) B4409711
theorem B3136637 : Blo 686314 3136637 := bstep (se 3 (by rfl) ⟨588119, by rfl⟩ : syracuseStep 3136637 = 1176239) B1176239
theorem B2612371 : Blo 686314 2612371 := bstep (se 1 (by rfl) ⟨1959278, by rfl⟩ : syracuseStep 2612371 = 3918557) B3918557
theorem B9395453 : Blo 686314 9395453 := bstep (se 3 (by rfl) ⟨1761647, by rfl⟩ : syracuseStep 9395453 = 3523295) B3523295
theorem B2317679 : Blo 686314 2317679 := bstep (se 1 (by rfl) ⟨1738259, by rfl⟩ : syracuseStep 2317679 = 3476519) B3476519
theorem B2318057 : Blo 686314 2318057 := bstep (se 2 (by rfl) ⟨869271, by rfl⟩ : syracuseStep 2318057 = 1738543) B1738543
theorem B13230053 : Blo 686314 13230053 := bstep (se 4 (by rfl) ⟨1240317, by rfl⟩ : syracuseStep 13230053 = 2480635) B2480635
theorem B4415735 : Blo 686314 4415735 := bstep (se 1 (by rfl) ⟨3311801, by rfl⟩ : syracuseStep 4415735 = 6623603) B6623603
theorem B4973033 : Blo 686314 4973033 := bstep (se 2 (by rfl) ⟨1864887, by rfl⟩ : syracuseStep 4973033 = 3729775) B3729775
theorem B8806913 : Blo 686314 8806913 := bstep (se 2 (by rfl) ⟨3302592, by rfl⟩ : syracuseStep 8806913 = 6605185) B6605185
theorem B2318921 : Blo 686314 2318921 := bstep (se 2 (by rfl) ⟨869595, by rfl⟩ : syracuseStep 2318921 = 1739191) B1739191
theorem B31810157 : Blo 686314 31810157 := bstep (se 3 (by rfl) ⟨5964404, by rfl⟩ : syracuseStep 31810157 = 11928809) B11928809
theorem B2319083 : Blo 686314 2319083 := bstep (se 1 (by rfl) ⟨1739312, by rfl⟩ : syracuseStep 2319083 = 3478625) B3478625
theorem B19882907 : Blo 686314 19882907 := bstep (se 1 (by rfl) ⟨14912180, by rfl⟩ : syracuseStep 19882907 = 29824361) B29824361
theorem B1958813 : Blo 686314 1958813 := bstep (se 3 (by rfl) ⟨367277, by rfl⟩ : syracuseStep 1958813 = 734555) B734555
theorem B2090411 : Blo 686314 2090411 := bstep (se 1 (by rfl) ⟨1567808, by rfl⟩ : syracuseStep 2090411 = 3135617) B3135617
theorem B7825085 : Blo 686314 7825085 := bstep (se 3 (by rfl) ⟨1467203, by rfl⟩ : syracuseStep 7825085 = 2934407) B2934407
theorem B1959643 : Blo 686314 1959643 := bstep (se 1 (by rfl) ⟨1469732, by rfl⟩ : syracuseStep 1959643 = 2939465) B2939465
theorem B1468127 : Blo 686314 1468127 := bstep (se 1 (by rfl) ⟨1101095, by rfl⟩ : syracuseStep 1468127 = 2202191) B2202191
theorem B1861343 : Blo 686314 1861343 := bstep (se 1 (by rfl) ⟨1396007, by rfl⟩ : syracuseStep 1861343 = 2792015) B2792015
theorem B3925847 : Blo 686314 3925847 := bstep (se 1 (by rfl) ⟨2944385, by rfl⟩ : syracuseStep 3925847 = 5888771) B5888771
theorem B1304417 : Blo 686314 1304417 := bstep (se 2 (by rfl) ⟨489156, by rfl⟩ : syracuseStep 1304417 = 978313) B978313
theorem B2353025 : Blo 686314 2353025 := bstep (se 2 (by rfl) ⟨882384, by rfl⟩ : syracuseStep 2353025 = 1764769) B1764769
theorem B2615287 : Blo 686314 2615287 := bstep (se 1 (by rfl) ⟨1961465, by rfl⟩ : syracuseStep 2615287 = 3922931) B3922931
theorem B4778003 : Blo 686314 4778003 := bstep (se 1 (by rfl) ⟨3583502, by rfl⟩ : syracuseStep 4778003 = 7167005) B7167005
theorem B2320595 : Blo 686314 2320595 := bstep (se 1 (by rfl) ⟨1740446, by rfl⟩ : syracuseStep 2320595 = 3480893) B3480893
theorem B2320865 : Blo 686314 2320865 := bstep (se 2 (by rfl) ⟨870324, by rfl⟩ : syracuseStep 2320865 = 1740649) B1740649
theorem B3926555 : Blo 686314 3926555 := bstep (se 1 (by rfl) ⟨2944916, by rfl⟩ : syracuseStep 3926555 = 5889833) B5889833
theorem B4188779 : Blo 686314 4188779 := bstep (se 1 (by rfl) ⟨3141584, by rfl⟩ : syracuseStep 4188779 = 6283169) B6283169
theorem B2616259 : Blo 686314 2616259 := bstep (se 1 (by rfl) ⟨1962194, by rfl⟩ : syracuseStep 2616259 = 3924389) B3924389
theorem B7072865 : Blo 686314 7072865 := bstep (se 2 (by rfl) ⟨2652324, by rfl⟩ : syracuseStep 7072865 = 5304649) B5304649
theorem B2944097 : Blo 686314 2944097 := bstep (se 2 (by rfl) ⟨1104036, by rfl⟩ : syracuseStep 2944097 = 2208073) B2208073
theorem B2322215 : Blo 686314 2322215 := bstep (se 1 (by rfl) ⟨1741661, by rfl⟩ : syracuseStep 2322215 = 3483323) B3483323
theorem B1175419 : Blo 686314 1175419 := bstep (se 1 (by rfl) ⟨881564, by rfl⟩ : syracuseStep 1175419 = 1763129) B1763129
theorem B2486159 : Blo 686314 2486159 := bstep (se 1 (by rfl) ⟨1864619, by rfl⟩ : syracuseStep 2486159 = 3729239) B3729239
theorem B2486171 : Blo 686314 2486171 := bstep (se 1 (by rfl) ⟨1864628, by rfl⟩ : syracuseStep 2486171 = 3729257) B3729257
theorem B29716409 : Blo 686314 29716409 := bstep (se 2 (by rfl) ⟨11143653, by rfl⟩ : syracuseStep 29716409 = 22287307) B22287307
theorem B1962377 : Blo 686314 1962377 := bstep (se 2 (by rfl) ⟨735891, by rfl⟩ : syracuseStep 1962377 = 1471783) B1471783
theorem B2093647 : Blo 686314 2093647 := bstep (se 1 (by rfl) ⟨1570235, by rfl⟩ : syracuseStep 2093647 = 3140471) B3140471
theorem B2323241 : Blo 686314 2323241 := bstep (se 2 (by rfl) ⟨871215, by rfl⟩ : syracuseStep 2323241 = 1742431) B1742431
theorem B979879 : Blo 686314 979879 := bstep (se 1 (by rfl) ⟨734909, by rfl⟩ : syracuseStep 979879 = 1469819) B1469819
theorem B2323511 : Blo 686314 2323511 := bstep (se 1 (by rfl) ⟨1742633, by rfl⟩ : syracuseStep 2323511 = 3485267) B3485267
theorem B2618507 : Blo 686314 2618507 := bstep (se 1 (by rfl) ⟨1963880, by rfl⟩ : syracuseStep 2618507 = 3927761) B3927761
theorem B3306881 : Blo 686314 3306881 := bstep (se 2 (by rfl) ⟨1240080, by rfl⟩ : syracuseStep 3306881 = 2480161) B2480161
theorem B3929903 : Blo 686314 3929903 := bstep (se 1 (by rfl) ⟨2947427, by rfl⟩ : syracuseStep 3929903 = 5894855) B5894855
theorem B1767521 : Blo 686314 1767521 := bstep (se 2 (by rfl) ⟨662820, by rfl⟩ : syracuseStep 1767521 = 1325641) B1325641
theorem B1308935 : Blo 686314 1308935 := bstep (se 1 (by rfl) ⟨981701, by rfl⟩ : syracuseStep 1308935 = 1963403) B1963403
theorem B686383 : Blo 686314 686383 := bstep (se 1 (by rfl) ⟨514787, by rfl⟩ : syracuseStep 686383 = 1029575) B1029575
theorem B4192787 : Blo 686314 4192787 := bstep (se 1 (by rfl) ⟨3144590, by rfl⟩ : syracuseStep 4192787 = 6289181) B6289181
theorem B686619 : Blo 686314 686619 := bstep (se 1 (by rfl) ⟨514964, by rfl⟩ : syracuseStep 686619 = 1029929) B1029929
theorem B686623 : Blo 686314 686623 := bstep (se 1 (by rfl) ⟨514967, by rfl⟩ : syracuseStep 686623 = 1029935) B1029935
theorem B7862993 : Blo 686314 7862993 := bstep (se 2 (by rfl) ⟨2948622, by rfl⟩ : syracuseStep 7862993 = 5897245) B5897245
theorem B686939 : Blo 686314 686939 := bstep (se 1 (by rfl) ⟨515204, by rfl⟩ : syracuseStep 686939 = 1030409) B1030409
theorem B687007 : Blo 686314 687007 := bstep (se 1 (by rfl) ⟨515255, by rfl⟩ : syracuseStep 687007 = 1030511) B1030511
theorem B2325455 : Blo 686314 2325455 := bstep (se 1 (by rfl) ⟨1744091, by rfl⟩ : syracuseStep 2325455 = 3488183) B3488183
theorem B687151 : Blo 686314 687151 := bstep (se 1 (by rfl) ⟨515363, by rfl⟩ : syracuseStep 687151 = 1030727) B1030727
theorem B687175 : Blo 686314 687175 := bstep (se 1 (by rfl) ⟨515381, by rfl⟩ : syracuseStep 687175 = 1030763) B1030763
theorem B687327 : Blo 686314 687327 := bstep (se 1 (by rfl) ⟨515495, by rfl⟩ : syracuseStep 687327 = 1030991) B1030991
theorem B687591 : Blo 686314 687591 := bstep (se 1 (by rfl) ⟨515693, by rfl⟩ : syracuseStep 687591 = 1031387) B1031387
theorem B1179209 : Blo 686314 1179209 := bstep (se 2 (by rfl) ⟨442203, by rfl⟩ : syracuseStep 1179209 = 884407) B884407
theorem B1965647 : Blo 686314 1965647 := bstep (se 1 (by rfl) ⟨1474235, by rfl⟩ : syracuseStep 1965647 = 2948471) B2948471
theorem B687707 : Blo 686314 687707 := bstep (se 1 (by rfl) ⟨515780, by rfl⟩ : syracuseStep 687707 = 1031561) B1031561
theorem B687943 : Blo 686314 687943 := bstep (se 1 (by rfl) ⟨515957, by rfl⟩ : syracuseStep 687943 = 1031915) B1031915
theorem B3309437 : Blo 686314 3309437 := bstep (se 3 (by rfl) ⟨620519, by rfl⟩ : syracuseStep 3309437 = 1241039) B1241039
theorem B688095 : Blo 686314 688095 := bstep (se 1 (by rfl) ⟨516071, by rfl⟩ : syracuseStep 688095 = 1032143) B1032143
theorem B688319 : Blo 686314 688319 := bstep (se 1 (by rfl) ⟨516239, by rfl⟩ : syracuseStep 688319 = 1032479) B1032479
theorem B688335 : Blo 686314 688335 := bstep (se 1 (by rfl) ⟨516251, by rfl⟩ : syracuseStep 688335 = 1032503) B1032503
theorem B688383 : Blo 686314 688383 := bstep (se 1 (by rfl) ⟨516287, by rfl⟩ : syracuseStep 688383 = 1032575) B1032575
theorem B2687263 : Blo 686314 2687263 := bstep (se 1 (by rfl) ⟨2015447, by rfl⟩ : syracuseStep 2687263 = 4030895) B4030895
theorem B688431 : Blo 686314 688431 := bstep (se 1 (by rfl) ⟨516323, by rfl⟩ : syracuseStep 688431 = 1032647) B1032647
theorem B688667 : Blo 686314 688667 := bstep (se 1 (by rfl) ⟨516500, by rfl⟩ : syracuseStep 688667 = 1033001) B1033001
theorem B1737247 : Blo 686314 1737247 := bstep (se 1 (by rfl) ⟨1302935, by rfl⟩ : syracuseStep 1737247 = 2605871) B2605871
theorem B688671 : Blo 686314 688671 := bstep (se 1 (by rfl) ⟨516503, by rfl⟩ : syracuseStep 688671 = 1033007) B1033007
theorem B688751 : Blo 686314 688751 := bstep (se 1 (by rfl) ⟨516563, by rfl⟩ : syracuseStep 688751 = 1033127) B1033127
theorem B688807 : Blo 686314 688807 := bstep (se 1 (by rfl) ⟨516605, by rfl⟩ : syracuseStep 688807 = 1033211) B1033211
theorem B688847 : Blo 686314 688847 := bstep (se 1 (by rfl) ⟨516635, by rfl⟩ : syracuseStep 688847 = 1033271) B1033271
theorem B688927 : Blo 686314 688927 := bstep (se 1 (by rfl) ⟨516695, by rfl⟩ : syracuseStep 688927 = 1033391) B1033391
theorem B22348817 : Blo 686314 22348817 := bstep (se 2 (by rfl) ⟨8380806, by rfl⟩ : syracuseStep 22348817 = 16761613) B16761613
theorem B689199 : Blo 686314 689199 := bstep (se 1 (by rfl) ⟨516899, by rfl⟩ : syracuseStep 689199 = 1033799) B1033799
theorem B2327615 : Blo 686314 2327615 := bstep (se 1 (by rfl) ⟨1745711, by rfl⟩ : syracuseStep 2327615 = 3491423) B3491423
theorem B689263 : Blo 686314 689263 := bstep (se 1 (by rfl) ⟨516947, by rfl⟩ : syracuseStep 689263 = 1033895) B1033895
theorem B689319 : Blo 686314 689319 := bstep (se 1 (by rfl) ⟨516989, by rfl⟩ : syracuseStep 689319 = 1033979) B1033979
theorem B689343 : Blo 686314 689343 := bstep (se 1 (by rfl) ⟨517007, by rfl⟩ : syracuseStep 689343 = 1034015) B1034015
theorem B689375 : Blo 686314 689375 := bstep (se 1 (by rfl) ⟨517031, by rfl⟩ : syracuseStep 689375 = 1034063) B1034063
theorem B689455 : Blo 686314 689455 := bstep (se 1 (by rfl) ⟨517091, by rfl⟩ : syracuseStep 689455 = 1034183) B1034183
theorem B689691 : Blo 686314 689691 := bstep (se 1 (by rfl) ⟨517268, by rfl⟩ : syracuseStep 689691 = 1034537) B1034537
theorem B689695 : Blo 686314 689695 := bstep (se 1 (by rfl) ⟨517271, by rfl⟩ : syracuseStep 689695 = 1034543) B1034543
theorem B689855 : Blo 686314 689855 := bstep (se 1 (by rfl) ⟨517391, by rfl⟩ : syracuseStep 689855 = 1034783) B1034783
theorem B14845751 : Blo 686314 14845751 := bstep (se 1 (by rfl) ⟨11134313, by rfl⟩ : syracuseStep 14845751 = 22268627) B22268627
theorem B690111 : Blo 686314 690111 := bstep (se 1 (by rfl) ⟨517583, by rfl⟩ : syracuseStep 690111 = 1035167) B1035167
theorem B690143 : Blo 686314 690143 := bstep (se 1 (by rfl) ⟨517607, by rfl⟩ : syracuseStep 690143 = 1035215) B1035215
theorem B690203 : Blo 686314 690203 := bstep (se 1 (by rfl) ⟨517652, by rfl⟩ : syracuseStep 690203 = 1035305) B1035305
theorem B690207 : Blo 686314 690207 := bstep (se 1 (by rfl) ⟨517655, by rfl⟩ : syracuseStep 690207 = 1035311) B1035311
theorem B690223 : Blo 686314 690223 := bstep (se 1 (by rfl) ⟨517667, by rfl⟩ : syracuseStep 690223 = 1035335) B1035335
theorem B6261563 : Blo 686314 6261563 := bstep (se 1 (by rfl) ⟨4696172, by rfl⟩ : syracuseStep 6261563 = 9392345) B9392345
theorem B1739839 : Blo 686314 1739839 := bstep (se 1 (by rfl) ⟨1304879, by rfl⟩ : syracuseStep 1739839 = 2609759) B2609759
theorem B2788415 : Blo 686314 2788415 := bstep (se 1 (by rfl) ⟨2091311, by rfl⟩ : syracuseStep 2788415 = 4182623) B4182623
theorem B1740143 : Blo 686314 1740143 := bstep (se 1 (by rfl) ⟨1305107, by rfl⟩ : syracuseStep 1740143 = 2610215) B2610215
theorem B3870287 : Blo 686314 3870287 := bstep (se 1 (by rfl) ⟨2902715, by rfl⟩ : syracuseStep 3870287 = 5805431) B5805431
theorem B1544255 : Blo 686314 1544255 := bstep (se 1 (by rfl) ⟨1158191, by rfl⟩ : syracuseStep 1544255 = 2316383) B2316383
theorem B1544489 : Blo 686314 1544489 := bstep (se 2 (by rfl) ⟨579183, by rfl⟩ : syracuseStep 1544489 = 1158367) B1158367
theorem B6623639 : Blo 686314 6623639 := bstep (se 1 (by rfl) ⟨4967729, by rfl⟩ : syracuseStep 6623639 = 9935459) B9935459
theorem B1544759 : Blo 686314 1544759 := bstep (se 1 (by rfl) ⟨1158569, by rfl⟩ : syracuseStep 1544759 = 2317139) B2317139
theorem B6263635 : Blo 686314 6263635 := bstep (se 1 (by rfl) ⟨4697726, by rfl⟩ : syracuseStep 6263635 = 9395453) B9395453
theorem B1545065 : Blo 686314 1545065 := bstep (se 2 (by rfl) ⟨579399, by rfl⟩ : syracuseStep 1545065 = 1158799) B1158799
theorem B1545119 : Blo 686314 1545119 := bstep (se 1 (by rfl) ⟨1158839, by rfl⟩ : syracuseStep 1545119 = 2317679) B2317679
theorem B2233327 : Blo 686314 2233327 := bstep (se 1 (by rfl) ⟨1674995, by rfl⟩ : syracuseStep 2233327 = 3349991) B3349991
theorem B2200601 : Blo 686314 2200601 := bstep (se 2 (by rfl) ⟨825225, by rfl⟩ : syracuseStep 2200601 = 1650451) B1650451
theorem B1545371 : Blo 686314 1545371 := bstep (se 1 (by rfl) ⟨1159028, by rfl⟩ : syracuseStep 1545371 = 2318057) B2318057
theorem B8820035 : Blo 686314 8820035 := bstep (se 1 (by rfl) ⟨6615026, by rfl⟩ : syracuseStep 8820035 = 13230053) B13230053
theorem B5871001 : Blo 686314 5871001 := bstep (se 2 (by rfl) ⟨2201625, by rfl⟩ : syracuseStep 5871001 = 4403251) B4403251
theorem B12588509 : Blo 686314 12588509 := bstep (se 3 (by rfl) ⟨2360345, by rfl⟩ : syracuseStep 12588509 = 4720691) B4720691
theorem B5871275 : Blo 686314 5871275 := bstep (se 1 (by rfl) ⟨4403456, by rfl⟩ : syracuseStep 5871275 = 8806913) B8806913
theorem B1545947 : Blo 686314 1545947 := bstep (se 1 (by rfl) ⟨1159460, by rfl⟩ : syracuseStep 1545947 = 2318921) B2318921
theorem B21206771 : Blo 686314 21206771 := bstep (se 1 (by rfl) ⟨15905078, by rfl⟩ : syracuseStep 21206771 = 31810157) B31810157
theorem B1546055 : Blo 686314 1546055 := bstep (se 1 (by rfl) ⟨1159541, by rfl⟩ : syracuseStep 1546055 = 2319083) B2319083
theorem B2791529 : Blo 686314 2791529 := bstep (se 2 (by rfl) ⟨1046823, by rfl⟩ : syracuseStep 2791529 = 2093647) B2093647
theorem B5216723 : Blo 686314 5216723 := bstep (se 1 (by rfl) ⟨3912542, by rfl⟩ : syracuseStep 5216723 = 7825085) B7825085
theorem B3185335 : Blo 686314 3185335 := bstep (se 1 (by rfl) ⟨2389001, by rfl⟩ : syracuseStep 3185335 = 4778003) B4778003
theorem B1547063 : Blo 686314 1547063 := bstep (se 1 (by rfl) ⟨1160297, by rfl⟩ : syracuseStep 1547063 = 2320595) B2320595
theorem B1547243 : Blo 686314 1547243 := bstep (se 1 (by rfl) ⟨1160432, by rfl⟩ : syracuseStep 1547243 = 2320865) B2320865
theorem B2792519 : Blo 686314 2792519 := bstep (se 1 (by rfl) ⟨2094389, by rfl⟩ : syracuseStep 2792519 = 4188779) B4188779
theorem B1548143 : Blo 686314 1548143 := bstep (se 1 (by rfl) ⟨1161107, by rfl⟩ : syracuseStep 1548143 = 2322215) B2322215
theorem B4399049 : Blo 686314 4399049 := bstep (se 2 (by rfl) ⟨1649643, by rfl⟩ : syracuseStep 4399049 = 3299287) B3299287
theorem B2203625 : Blo 686314 2203625 := bstep (se 2 (by rfl) ⟨826359, by rfl⟩ : syracuseStep 2203625 = 1652719) B1652719
theorem B6627329 : Blo 686314 6627329 := bstep (se 2 (by rfl) ⟨2485248, by rfl⟩ : syracuseStep 6627329 = 4970497) B4970497
theorem B3481865 : Blo 686314 3481865 := bstep (se 2 (by rfl) ⟨1305699, by rfl⟩ : syracuseStep 3481865 = 2611399) B2611399
theorem B1548827 : Blo 686314 1548827 := bstep (se 1 (by rfl) ⟨1161620, by rfl⟩ : syracuseStep 1548827 = 2323241) B2323241
theorem B14099021 : Blo 686314 14099021 := bstep (se 3 (by rfl) ⟨2643566, by rfl⟩ : syracuseStep 14099021 = 5287133) B5287133
theorem B1549007 : Blo 686314 1549007 := bstep (se 1 (by rfl) ⟨1161755, by rfl⟩ : syracuseStep 1549007 = 2323511) B2323511
theorem B1745671 : Blo 686314 1745671 := bstep (se 1 (by rfl) ⟨1309253, by rfl⟩ : syracuseStep 1745671 = 2618507) B2618507
theorem B2204587 : Blo 686314 2204587 := bstep (se 1 (by rfl) ⟨1653440, by rfl⟩ : syracuseStep 2204587 = 3306881) B3306881
theorem B56435777 : Blo 686314 56435777 := bstep (se 2 (by rfl) ⟨21163416, by rfl⟩ : syracuseStep 56435777 = 42326833) B42326833
theorem B1549385 : Blo 686314 1549385 := bstep (se 2 (by rfl) ⟨581019, by rfl⟩ : syracuseStep 1549385 = 1162039) B1162039
theorem B10593529 : Blo 686314 10593529 := bstep (se 2 (by rfl) ⟨3972573, by rfl⟩ : syracuseStep 10593529 = 7945147) B7945147
theorem B3483161 : Blo 686314 3483161 := bstep (se 2 (by rfl) ⟨1306185, by rfl⟩ : syracuseStep 3483161 = 2612371) B2612371
theorem B2795191 : Blo 686314 2795191 := bstep (se 1 (by rfl) ⟨2096393, by rfl⟩ : syracuseStep 2795191 = 4192787) B4192787
theorem B1550303 : Blo 686314 1550303 := bstep (se 1 (by rfl) ⟨1162727, by rfl⟩ : syracuseStep 1550303 = 2325455) B2325455
theorem B3483971 : Blo 686314 3483971 := bstep (se 1 (by rfl) ⟨2612978, by rfl⟩ : syracuseStep 3483971 = 5225957) B5225957
theorem B6629789 : Blo 686314 6629789 := bstep (se 3 (by rfl) ⟨1243085, by rfl⟩ : syracuseStep 6629789 = 2486171) B2486171
theorem B2206291 : Blo 686314 2206291 := bstep (se 1 (by rfl) ⟨1654718, by rfl⟩ : syracuseStep 2206291 = 3309437) B3309437
theorem B1551311 : Blo 686314 1551311 := bstep (se 1 (by rfl) ⟨1163483, by rfl⟩ : syracuseStep 1551311 = 2326967) B2326967
theorem B5876711 : Blo 686314 5876711 := bstep (se 1 (by rfl) ⟨4407533, by rfl⟩ : syracuseStep 5876711 = 8815067) B8815067
theorem B1551401 : Blo 686314 1551401 := bstep (se 2 (by rfl) ⟨581775, by rfl⟩ : syracuseStep 1551401 = 1163551) B1163551
theorem B1158313 : Blo 686314 1158313 := bstep (se 2 (by rfl) ⟨434367, by rfl⟩ : syracuseStep 1158313 = 868735) B868735
theorem B1551635 : Blo 686314 1551635 := bstep (se 1 (by rfl) ⟨1163726, by rfl⟩ : syracuseStep 1551635 = 2327453) B2327453
theorem B1158455 : Blo 686314 1158455 := bstep (se 1 (by rfl) ⟨868841, by rfl⟩ : syracuseStep 1158455 = 1737683) B1737683
theorem B1551671 : Blo 686314 1551671 := bstep (se 1 (by rfl) ⟨1163753, by rfl⟩ : syracuseStep 1551671 = 2327507) B2327507
theorem B1650143 : Blo 686314 1650143 := bstep (se 1 (by rfl) ⟨1237607, by rfl⟩ : syracuseStep 1650143 = 2475215) B2475215
theorem B96808547 : Blo 686314 96808547 := bstep (se 1 (by rfl) ⟨72606410, by rfl⟩ : syracuseStep 96808547 = 145212821) B145212821
theorem B1158907 : Blo 686314 1158907 := bstep (se 1 (by rfl) ⟨869180, by rfl⟩ : syracuseStep 1158907 = 1738361) B1738361
theorem B733055 : Blo 686314 733055 := bstep (se 1 (by rfl) ⟨549791, by rfl⟩ : syracuseStep 733055 = 1099583) B1099583
theorem B1159049 : Blo 686314 1159049 := bstep (se 2 (by rfl) ⟨434643, by rfl⟩ : syracuseStep 1159049 = 869287) B869287
theorem B1552265 : Blo 686314 1552265 := bstep (se 2 (by rfl) ⟨582099, by rfl⟩ : syracuseStep 1552265 = 1164199) B1164199
theorem B1552481 : Blo 686314 1552481 := bstep (se 2 (by rfl) ⟨582180, by rfl⟩ : syracuseStep 1552481 = 1164361) B1164361
theorem B11907749 : Blo 686314 11907749 := bstep (se 4 (by rfl) ⟨1116351, by rfl⟩ : syracuseStep 11907749 = 2232703) B2232703
theorem B1553147 : Blo 686314 1553147 := bstep (se 1 (by rfl) ⟨1164860, by rfl⟩ : syracuseStep 1553147 = 2329721) B2329721
theorem B1651519 : Blo 686314 1651519 := bstep (se 1 (by rfl) ⟨1238639, by rfl⟩ : syracuseStep 1651519 = 2477279) B2477279
theorem B3487049 : Blo 686314 3487049 := bstep (se 2 (by rfl) ⟨1307643, by rfl⟩ : syracuseStep 3487049 = 2615287) B2615287
theorem B1160615 : Blo 686314 1160615 := bstep (se 1 (by rfl) ⟨870461, by rfl⟩ : syracuseStep 1160615 = 1740923) B1740923
theorem B8927495 : Blo 686314 8927495 := bstep (se 1 (by rfl) ⟨6695621, by rfl⟩ : syracuseStep 8927495 = 13391243) B13391243
theorem B1030607 : Blo 686314 1030607 := bstep (se 1 (by rfl) ⟨772955, by rfl⟩ : syracuseStep 1030607 = 1545911) B1545911
theorem B1030697 : Blo 686314 1030697 := bstep (se 2 (by rfl) ⟨386511, by rfl⟩ : syracuseStep 1030697 = 773023) B773023
theorem B1161769 : Blo 686314 1161769 := bstep (se 2 (by rfl) ⟨435663, by rfl⟩ : syracuseStep 1161769 = 871327) B871327
theorem B3488345 : Blo 686314 3488345 := bstep (se 2 (by rfl) ⟨1308129, by rfl⟩ : syracuseStep 3488345 = 2616259) B2616259
theorem B1030889 : Blo 686314 1030889 := bstep (se 2 (by rfl) ⟨386583, by rfl⟩ : syracuseStep 1030889 = 773167) B773167
theorem B932617 : Blo 686314 932617 := bstep (se 2 (by rfl) ⟨349731, by rfl⟩ : syracuseStep 932617 = 699463) B699463
theorem B1031273 : Blo 686314 1031273 := bstep (se 2 (by rfl) ⟨386727, by rfl⟩ : syracuseStep 1031273 = 773455) B773455
theorem B1031399 : Blo 686314 1031399 := bstep (se 1 (by rfl) ⟨773549, by rfl⟩ : syracuseStep 1031399 = 1547099) B1547099
theorem B1162471 : Blo 686314 1162471 := bstep (se 1 (by rfl) ⟨871853, by rfl⟩ : syracuseStep 1162471 = 1743707) B1743707
theorem B2211047 : Blo 686314 2211047 := bstep (se 1 (by rfl) ⟨1658285, by rfl⟩ : syracuseStep 2211047 = 3316571) B3316571
theorem B5881085 : Blo 686314 5881085 := bstep (se 3 (by rfl) ⟨1102703, by rfl⟩ : syracuseStep 5881085 = 2205407) B2205407
theorem B1162667 : Blo 686314 1162667 := bstep (se 1 (by rfl) ⟨872000, by rfl⟩ : syracuseStep 1162667 = 1744001) B1744001
theorem B2211391 : Blo 686314 2211391 := bstep (se 1 (by rfl) ⟨1658543, by rfl⟩ : syracuseStep 2211391 = 3317087) B3317087
theorem B1031903 : Blo 686314 1031903 := bstep (se 1 (by rfl) ⟨773927, by rfl⟩ : syracuseStep 1031903 = 1547855) B1547855
theorem B1031945 : Blo 686314 1031945 := bstep (se 2 (by rfl) ⟨386979, by rfl⟩ : syracuseStep 1031945 = 773959) B773959
theorem B1163207 : Blo 686314 1163207 := bstep (se 1 (by rfl) ⟨872405, by rfl⟩ : syracuseStep 1163207 = 1744811) B1744811
theorem B1032383 : Blo 686314 1032383 := bstep (se 1 (by rfl) ⟨774287, by rfl⟩ : syracuseStep 1032383 = 1548575) B1548575
theorem B17842717 : Blo 686314 17842717 := bstep (se 3 (by rfl) ⟨3345509, by rfl⟩ : syracuseStep 17842717 = 6691019) B6691019
theorem B13255271 : Blo 686314 13255271 := bstep (se 1 (by rfl) ⟨9941453, by rfl⟩ : syracuseStep 13255271 = 19882907) B19882907
theorem B1032809 : Blo 686314 1032809 := bstep (se 2 (by rfl) ⟨387303, by rfl⟩ : syracuseStep 1032809 = 774607) B774607
theorem B1032815 : Blo 686314 1032815 := bstep (se 1 (by rfl) ⟨774611, by rfl⟩ : syracuseStep 1032815 = 1549223) B1549223
theorem B5882483 : Blo 686314 5882483 := bstep (se 1 (by rfl) ⟨4411862, by rfl⟩ : syracuseStep 5882483 = 8823725) B8823725
theorem B2933435 : Blo 686314 2933435 := bstep (se 1 (by rfl) ⟨2200076, by rfl⟩ : syracuseStep 2933435 = 4400153) B4400153
theorem B1163963 : Blo 686314 1163963 := bstep (se 1 (by rfl) ⟨872972, by rfl⟩ : syracuseStep 1163963 = 1745945) B1745945
theorem B1393607 : Blo 686314 1393607 := bstep (se 1 (by rfl) ⟨1045205, by rfl⟩ : syracuseStep 1393607 = 2090411) B2090411
theorem B1033439 : Blo 686314 1033439 := bstep (se 1 (by rfl) ⟨775079, by rfl⟩ : syracuseStep 1033439 = 1550159) B1550159
theorem B869611 : Blo 686314 869611 := bstep (se 1 (by rfl) ⟨652208, by rfl⟩ : syracuseStep 869611 = 1304417) B1304417
theorem B1033451 : Blo 686314 1033451 := bstep (se 1 (by rfl) ⟨775088, by rfl⟩ : syracuseStep 1033451 = 1550177) B1550177
theorem B1164523 : Blo 686314 1164523 := bstep (se 1 (by rfl) ⟨873392, by rfl⟩ : syracuseStep 1164523 = 1746785) B1746785
theorem B1033835 : Blo 686314 1033835 := bstep (se 1 (by rfl) ⟨775376, by rfl⟩ : syracuseStep 1033835 = 1550753) B1550753
theorem B32720525 : Blo 686314 32720525 := bstep (se 3 (by rfl) ⟨6135098, by rfl⟩ : syracuseStep 32720525 = 12270197) B12270197
theorem B1033919 : Blo 686314 1033919 := bstep (se 1 (by rfl) ⟨775439, by rfl⟩ : syracuseStep 1033919 = 1550879) B1550879
theorem B1034105 : Blo 686314 1034105 := bstep (se 2 (by rfl) ⟨387789, by rfl⟩ : syracuseStep 1034105 = 775579) B775579
theorem B772123 : Blo 686314 772123 := bstep (se 1 (by rfl) ⟨579092, by rfl⟩ : syracuseStep 772123 = 1158185) B1158185
theorem B1493147 : Blo 686314 1493147 := bstep (se 1 (by rfl) ⟨1119860, by rfl⟩ : syracuseStep 1493147 = 2239721) B2239721
theorem B969311 : Blo 686314 969311 := bstep (se 1 (by rfl) ⟨726983, by rfl⟩ : syracuseStep 969311 = 1453967) B1453967
theorem B1657439 : Blo 686314 1657439 := bstep (se 1 (by rfl) ⟨1243079, by rfl⟩ : syracuseStep 1657439 = 2486159) B2486159
theorem B2935399 : Blo 686314 2935399 := bstep (se 1 (by rfl) ⟨2201549, by rfl⟩ : syracuseStep 2935399 = 4403099) B4403099
theorem B1034855 : Blo 686314 1034855 := bstep (se 1 (by rfl) ⟨776141, by rfl⟩ : syracuseStep 1034855 = 1552283) B1552283
theorem B19810939 : Blo 686314 19810939 := bstep (se 1 (by rfl) ⟨14858204, by rfl⟩ : syracuseStep 19810939 = 29716409) B29716409
theorem B2935433 : Blo 686314 2935433 := bstep (se 2 (by rfl) ⟨1100787, by rfl⟩ : syracuseStep 2935433 = 2201575) B2201575
theorem B1035047 : Blo 686314 1035047 := bstep (se 1 (by rfl) ⟨776285, by rfl⟩ : syracuseStep 1035047 = 1552571) B1552571
theorem B2935673 : Blo 686314 2935673 := bstep (se 2 (by rfl) ⟨1100877, by rfl⟩ : syracuseStep 2935673 = 2201755) B2201755
theorem B1035371 : Blo 686314 1035371 := bstep (se 1 (by rfl) ⟨776528, by rfl⟩ : syracuseStep 1035371 = 1553057) B1553057
theorem B2608271 : Blo 686314 2608271 := bstep (se 1 (by rfl) ⟨1956203, by rfl⟩ : syracuseStep 2608271 = 3912407) B3912407
theorem B773599 : Blo 686314 773599 := bstep (se 1 (by rfl) ⟨580199, by rfl⟩ : syracuseStep 773599 = 1160399) B1160399
theorem B12242447 : Blo 686314 12242447 := bstep (se 1 (by rfl) ⟨9181835, by rfl⟩ : syracuseStep 12242447 = 18363671) B18363671
theorem B3722855 : Blo 686314 3722855 := bstep (se 1 (by rfl) ⟨2792141, by rfl⟩ : syracuseStep 3722855 = 5584283) B5584283
theorem B2936731 : Blo 686314 2936731 := bstep (se 1 (by rfl) ⟨2202548, by rfl⟩ : syracuseStep 2936731 = 4405097) B4405097
theorem B774139 : Blo 686314 774139 := bstep (se 1 (by rfl) ⟨580604, by rfl⟩ : syracuseStep 774139 = 1161209) B1161209
theorem B774247 : Blo 686314 774247 := bstep (se 1 (by rfl) ⟨580685, by rfl⟩ : syracuseStep 774247 = 1161371) B1161371
theorem B774319 : Blo 686314 774319 := bstep (se 1 (by rfl) ⟨580739, by rfl⟩ : syracuseStep 774319 = 1161479) B1161479
theorem B872623 : Blo 686314 872623 := bstep (se 1 (by rfl) ⟨654467, by rfl⟩ : syracuseStep 872623 = 1308935) B1308935
theorem B13258961 : Blo 686314 13258961 := bstep (se 2 (by rfl) ⟨4972110, by rfl⟩ : syracuseStep 13258961 = 9944221) B9944221
theorem B775003 : Blo 686314 775003 := bstep (se 1 (by rfl) ⟨581252, by rfl⟩ : syracuseStep 775003 = 1162505) B1162505
theorem B4413275 : Blo 686314 4413275 := bstep (se 1 (by rfl) ⟨3309956, by rfl⟩ : syracuseStep 4413275 = 6619913) B6619913
theorem B2938781 : Blo 686314 2938781 := bstep (se 3 (by rfl) ⟨551021, by rfl⟩ : syracuseStep 2938781 = 1102043) B1102043
theorem B776263 : Blo 686314 776263 := bstep (se 1 (by rfl) ⟨582197, by rfl⟩ : syracuseStep 776263 = 1164395) B1164395
theorem B4250089 : Blo 686314 4250089 := bstep (se 2 (by rfl) ⟨1593783, by rfl⟩ : syracuseStep 4250089 = 3187567) B3187567
theorem B13261421 : Blo 686314 13261421 := bstep (se 3 (by rfl) ⟨2486516, by rfl⟩ : syracuseStep 13261421 = 4973033) B4973033
theorem B71326817 : Blo 686314 71326817 := bstep (se 2 (by rfl) ⟨26747556, by rfl⟩ : syracuseStep 71326817 = 53495113) B53495113
theorem B2317409 : Blo 686314 2317409 := bstep (se 2 (by rfl) ⟨869028, by rfl⟩ : syracuseStep 2317409 = 1738057) B1738057
theorem B2940047 : Blo 686314 2940047 := bstep (se 1 (by rfl) ⟨2205035, by rfl⟩ : syracuseStep 2940047 = 4410071) B4410071
theorem B2612675 : Blo 686314 2612675 := bstep (se 1 (by rfl) ⟨1959506, by rfl⟩ : syracuseStep 2612675 = 3919013) B3919013
theorem B2940407 : Blo 686314 2940407 := bstep (se 1 (by rfl) ⟨2205305, by rfl⟩ : syracuseStep 2940407 = 4410611) B4410611
theorem B2612857 : Blo 686314 2612857 := bstep (se 2 (by rfl) ⟨979821, by rfl⟩ : syracuseStep 2612857 = 1959643) B1959643
theorem B2317949 : Blo 686314 2317949 := bstep (se 3 (by rfl) ⟨434615, by rfl⟩ : syracuseStep 2317949 = 869231) B869231
theorem B4415143 : Blo 686314 4415143 := bstep (se 1 (by rfl) ⟨3311357, by rfl⟩ : syracuseStep 4415143 = 6622715) B6622715
theorem B2318111 : Blo 686314 2318111 := bstep (se 1 (by rfl) ⟨1738583, by rfl⟩ : syracuseStep 2318111 = 3477167) B3477167
theorem B6381359 : Blo 686314 6381359 := bstep (se 1 (by rfl) ⟨4786019, by rfl⟩ : syracuseStep 6381359 = 9572039) B9572039
theorem B2318219 : Blo 686314 2318219 := bstep (se 1 (by rfl) ⟨1738664, by rfl⟩ : syracuseStep 2318219 = 3477329) B3477329
theorem B2613131 : Blo 686314 2613131 := bstep (se 1 (by rfl) ⟨1959848, by rfl⟩ : syracuseStep 2613131 = 3919697) B3919697
theorem B28336139 : Blo 686314 28336139 := bstep (se 1 (by rfl) ⟨21252104, by rfl⟩ : syracuseStep 28336139 = 42504209) B42504209
theorem B4972691 : Blo 686314 4972691 := bstep (se 1 (by rfl) ⟨3729518, by rfl⟩ : syracuseStep 4972691 = 7459037) B7459037
theorem B1466623 : Blo 686314 1466623 := bstep (se 1 (by rfl) ⟨1099967, by rfl⟩ : syracuseStep 1466623 = 2199935) B2199935
theorem B2318759 : Blo 686314 2318759 := bstep (se 1 (by rfl) ⟨1739069, by rfl⟩ : syracuseStep 2318759 = 3478139) B3478139
theorem B14869277 : Blo 686314 14869277 := bstep (se 3 (by rfl) ⟨2787989, by rfl⟩ : syracuseStep 14869277 = 5575979) B5575979
theorem B1958687 : Blo 686314 1958687 := bstep (se 1 (by rfl) ⟨1469015, by rfl⟩ : syracuseStep 1958687 = 2938031) B2938031
theorem B17688455 : Blo 686314 17688455 := bstep (se 1 (by rfl) ⟨13266341, by rfl⟩ : syracuseStep 17688455 = 26532683) B26532683
theorem B1468297 : Blo 686314 1468297 := bstep (se 2 (by rfl) ⟨550611, by rfl⟩ : syracuseStep 1468297 = 1101223) B1101223
theorem B2484125 : Blo 686314 2484125 := bstep (se 3 (by rfl) ⟨465773, by rfl⟩ : syracuseStep 2484125 = 931547) B931547
theorem B1959871 : Blo 686314 1959871 := bstep (se 1 (by rfl) ⟨1469903, by rfl⟩ : syracuseStep 1959871 = 2939807) B2939807
theorem B2091091 : Blo 686314 2091091 := bstep (se 1 (by rfl) ⟨1568318, by rfl⟩ : syracuseStep 2091091 = 3136637) B3136637
theorem B1567225 : Blo 686314 1567225 := bstep (se 2 (by rfl) ⟨587709, by rfl⟩ : syracuseStep 1567225 = 1175419) B1175419
theorem B2943823 : Blo 686314 2943823 := bstep (se 1 (by rfl) ⟨2207867, by rfl⟩ : syracuseStep 2943823 = 4415735) B4415735
theorem B1305875 : Blo 686314 1305875 := bstep (se 1 (by rfl) ⟨979406, by rfl⟩ : syracuseStep 1305875 = 1958813) B1958813
theorem B978751 : Blo 686314 978751 := bstep (se 1 (by rfl) ⟨734063, by rfl⟩ : syracuseStep 978751 = 1468127) B1468127
theorem B1240895 : Blo 686314 1240895 := bstep (se 1 (by rfl) ⟨930671, by rfl⟩ : syracuseStep 1240895 = 1861343) B1861343
theorem B1306505 : Blo 686314 1306505 := bstep (se 2 (by rfl) ⟨489939, by rfl⟩ : syracuseStep 1306505 = 979879) B979879
theorem B2617231 : Blo 686314 2617231 := bstep (se 1 (by rfl) ⟨1962923, by rfl⟩ : syracuseStep 2617231 = 3925847) B3925847
theorem B1568683 : Blo 686314 1568683 := bstep (se 1 (by rfl) ⟨1176512, by rfl⟩ : syracuseStep 1568683 = 2353025) B2353025
theorem B2617703 : Blo 686314 2617703 := bstep (se 1 (by rfl) ⟨1963277, by rfl⟩ : syracuseStep 2617703 = 3926555) B3926555
theorem B4715243 : Blo 686314 4715243 := bstep (se 1 (by rfl) ⟨3536432, by rfl⟩ : syracuseStep 4715243 = 7072865) B7072865
theorem B1962731 : Blo 686314 1962731 := bstep (se 1 (by rfl) ⟨1472048, by rfl⟩ : syracuseStep 1962731 = 2944097) B2944097
theorem B1471817 : Blo 686314 1471817 := bstep (se 2 (by rfl) ⟨551931, by rfl⟩ : syracuseStep 1471817 = 1103863) B1103863
theorem B3306977 : Blo 686314 3306977 := bstep (se 2 (by rfl) ⟨1240116, by rfl⟩ : syracuseStep 3306977 = 2480233) B2480233
theorem B1308251 : Blo 686314 1308251 := bstep (se 1 (by rfl) ⟨981188, by rfl⟩ : syracuseStep 1308251 = 1962377) B1962377
theorem B7272337 : Blo 686314 7272337 := bstep (se 2 (by rfl) ⟨2727126, by rfl⟩ : syracuseStep 7272337 = 5454253) B5454253
theorem B3307823 : Blo 686314 3307823 := bstep (se 1 (by rfl) ⟨2480867, by rfl⟩ : syracuseStep 3307823 = 4961735) B4961735
theorem B686495 : Blo 686314 686495 := bstep (se 1 (by rfl) ⟨514871, by rfl⟩ : syracuseStep 686495 = 1029743) B1029743
theorem B686543 : Blo 686314 686543 := bstep (se 1 (by rfl) ⟨514907, by rfl⟩ : syracuseStep 686543 = 1029815) B1029815
theorem B686567 : Blo 686314 686567 := bstep (se 1 (by rfl) ⟨514925, by rfl⟩ : syracuseStep 686567 = 1029851) B1029851
theorem B2325023 : Blo 686314 2325023 := bstep (se 1 (by rfl) ⟨1743767, by rfl⟩ : syracuseStep 2325023 = 3487535) B3487535
theorem B2619935 : Blo 686314 2619935 := bstep (se 1 (by rfl) ⟨1964951, by rfl⟩ : syracuseStep 2619935 = 3929903) B3929903
theorem B686683 : Blo 686314 686683 := bstep (se 1 (by rfl) ⟨515012, by rfl⟩ : syracuseStep 686683 = 1030025) B1030025
theorem B1473167 : Blo 686314 1473167 := bstep (se 1 (by rfl) ⟨1104875, by rfl⟩ : syracuseStep 1473167 = 2209751) B2209751
theorem B686751 : Blo 686314 686751 := bstep (se 1 (by rfl) ⟨515063, by rfl⟩ : syracuseStep 686751 = 1030127) B1030127
theorem B1178347 : Blo 686314 1178347 := bstep (se 1 (by rfl) ⟨883760, by rfl⟩ : syracuseStep 1178347 = 1767521) B1767521
theorem B686919 : Blo 686314 686919 := bstep (se 1 (by rfl) ⟨515189, by rfl⟩ : syracuseStep 686919 = 1030379) B1030379
theorem B3144557 : Blo 686314 3144557 := bstep (se 3 (by rfl) ⟨589604, by rfl⟩ : syracuseStep 3144557 = 1179209) B1179209
theorem B686959 : Blo 686314 686959 := bstep (se 1 (by rfl) ⟨515219, by rfl⟩ : syracuseStep 686959 = 1030439) B1030439
theorem B687015 : Blo 686314 687015 := bstep (se 1 (by rfl) ⟨515261, by rfl⟩ : syracuseStep 687015 = 1030523) B1030523
theorem B687195 : Blo 686314 687195 := bstep (se 1 (by rfl) ⟨515396, by rfl⟩ : syracuseStep 687195 = 1030793) B1030793
theorem B5241995 : Blo 686314 5241995 := bstep (se 1 (by rfl) ⟨3931496, by rfl⟩ : syracuseStep 5241995 = 7862993) B7862993
theorem B687311 : Blo 686314 687311 := bstep (se 1 (by rfl) ⟨515483, by rfl⟩ : syracuseStep 687311 = 1030967) B1030967
theorem B687335 : Blo 686314 687335 := bstep (se 1 (by rfl) ⟨515501, by rfl⟩ : syracuseStep 687335 = 1031003) B1031003
theorem B687431 : Blo 686314 687431 := bstep (se 1 (by rfl) ⟨515573, by rfl⟩ : syracuseStep 687431 = 1031147) B1031147
theorem B687567 : Blo 686314 687567 := bstep (se 1 (by rfl) ⟨515675, by rfl⟩ : syracuseStep 687567 = 1031351) B1031351
theorem B687727 : Blo 686314 687727 := bstep (se 1 (by rfl) ⟨515795, by rfl⟩ : syracuseStep 687727 = 1031591) B1031591
theorem B687783 : Blo 686314 687783 := bstep (se 1 (by rfl) ⟨515837, by rfl⟩ : syracuseStep 687783 = 1031675) B1031675
theorem B1310431 : Blo 686314 1310431 := bstep (se 1 (by rfl) ⟨982823, by rfl⟩ : syracuseStep 1310431 = 1965647) B1965647
theorem B687847 : Blo 686314 687847 := bstep (se 1 (by rfl) ⟨515885, by rfl⟩ : syracuseStep 687847 = 1031771) B1031771
theorem B687903 : Blo 686314 687903 := bstep (se 1 (by rfl) ⟨515927, by rfl⟩ : syracuseStep 687903 = 1031855) B1031855
theorem B687983 : Blo 686314 687983 := bstep (se 1 (by rfl) ⟨515987, by rfl⟩ : syracuseStep 687983 = 1031975) B1031975
theorem B688039 : Blo 686314 688039 := bstep (se 1 (by rfl) ⟨516029, by rfl⟩ : syracuseStep 688039 = 1032059) B1032059
theorem B688255 : Blo 686314 688255 := bstep (se 1 (by rfl) ⟨516191, by rfl⟩ : syracuseStep 688255 = 1032383) B1032383
theorem B688539 : Blo 686314 688539 := bstep (se 1 (by rfl) ⟨516404, by rfl⟩ : syracuseStep 688539 = 1032809) B1032809
theorem B688543 : Blo 686314 688543 := bstep (se 1 (by rfl) ⟨516407, by rfl⟩ : syracuseStep 688543 = 1032815) B1032815
theorem B23790289 : Blo 686314 23790289 := bstep (se 2 (by rfl) ⟨8921358, by rfl⟩ : syracuseStep 23790289 = 17842717) B17842717
theorem B688959 : Blo 686314 688959 := bstep (se 1 (by rfl) ⟨516719, by rfl⟩ : syracuseStep 688959 = 1033439) B1033439
theorem B688967 : Blo 686314 688967 := bstep (se 1 (by rfl) ⟨516725, by rfl⟩ : syracuseStep 688967 = 1033451) B1033451
theorem B2327561 : Blo 686314 2327561 := bstep (se 2 (by rfl) ⟨872835, by rfl⟩ : syracuseStep 2327561 = 1745671) B1745671
theorem B689223 : Blo 686314 689223 := bstep (se 1 (by rfl) ⟨516917, by rfl⟩ : syracuseStep 689223 = 1033835) B1033835
theorem B689279 : Blo 686314 689279 := bstep (se 1 (by rfl) ⟨516959, by rfl⟩ : syracuseStep 689279 = 1033919) B1033919
theorem B9897167 : Blo 686314 9897167 := bstep (se 1 (by rfl) ⟨7422875, by rfl⟩ : syracuseStep 9897167 = 14845751) B14845751
theorem B689403 : Blo 686314 689403 := bstep (se 1 (by rfl) ⟨517052, by rfl⟩ : syracuseStep 689403 = 1034105) B1034105
theorem B689903 : Blo 686314 689903 := bstep (se 1 (by rfl) ⟨517427, by rfl⟩ : syracuseStep 689903 = 1034855) B1034855
theorem B690031 : Blo 686314 690031 := bstep (se 1 (by rfl) ⟨517523, by rfl⟩ : syracuseStep 690031 = 1035047) B1035047
theorem B690247 : Blo 686314 690247 := bstep (se 1 (by rfl) ⟨517685, by rfl⟩ : syracuseStep 690247 = 1035371) B1035371
theorem B1738847 : Blo 686314 1738847 := bstep (se 1 (by rfl) ⟨1304135, by rfl⟩ : syracuseStep 1738847 = 2608271) B2608271
theorem B8161631 : Blo 686314 8161631 := bstep (se 1 (by rfl) ⟨6121223, by rfl⟩ : syracuseStep 8161631 = 12242447) B12242447
theorem B2788121 : Blo 686314 2788121 := bstep (se 2 (by rfl) ⟨1045545, by rfl⟩ : syracuseStep 2788121 = 2091091) B2091091
theorem B26414585 : Blo 686314 26414585 := bstep (se 2 (by rfl) ⟨9905469, by rfl⟩ : syracuseStep 26414585 = 19810939) B19810939
theorem B8392339 : Blo 686314 8392339 := bstep (se 1 (by rfl) ⟨6294254, by rfl⟩ : syracuseStep 8392339 = 12588509) B12588509
theorem B1544417 : Blo 686314 1544417 := bstep (se 2 (by rfl) ⟨579156, by rfl⟩ : syracuseStep 1544417 = 1158313) B1158313
theorem B3477815 : Blo 686314 3477815 := bstep (se 1 (by rfl) ⟨2608361, by rfl⟩ : syracuseStep 3477815 = 5216723) B5216723
theorem B47551211 : Blo 686314 47551211 := bstep (se 1 (by rfl) ⟨35663408, by rfl⟩ : syracuseStep 47551211 = 71326817) B71326817
theorem B1544939 : Blo 686314 1544939 := bstep (se 1 (by rfl) ⟨1158704, by rfl⟩ : syracuseStep 1544939 = 2317409) B2317409
theorem B1741783 : Blo 686314 1741783 := bstep (se 1 (by rfl) ⟨1306337, by rfl⟩ : syracuseStep 1741783 = 2612675) B2612675
theorem B1545209 : Blo 686314 1545209 := bstep (se 2 (by rfl) ⟨579453, by rfl⟩ : syracuseStep 1545209 = 1158907) B1158907
theorem B7836749 : Blo 686314 7836749 := bstep (se 3 (by rfl) ⟨1469390, by rfl⟩ : syracuseStep 7836749 = 2938781) B2938781
theorem B1545299 : Blo 686314 1545299 := bstep (se 1 (by rfl) ⟨1158974, by rfl⟩ : syracuseStep 1545299 = 2317949) B2317949
theorem B1545407 : Blo 686314 1545407 := bstep (se 1 (by rfl) ⟨1159055, by rfl⟩ : syracuseStep 1545407 = 2318111) B2318111
theorem B1545479 : Blo 686314 1545479 := bstep (se 1 (by rfl) ⟨1159109, by rfl⟩ : syracuseStep 1545479 = 2318219) B2318219
theorem B1742087 : Blo 686314 1742087 := bstep (se 1 (by rfl) ⟨1306565, by rfl⟩ : syracuseStep 1742087 = 2613131) B2613131
theorem B3315127 : Blo 686314 3315127 := bstep (se 1 (by rfl) ⟨2486345, by rfl⟩ : syracuseStep 3315127 = 4972691) B4972691
theorem B1545839 : Blo 686314 1545839 := bstep (se 1 (by rfl) ⟨1159379, by rfl⟩ : syracuseStep 1545839 = 2318759) B2318759
theorem B37623851 : Blo 686314 37623851 := bstep (se 1 (by rfl) ⟨28217888, by rfl⟩ : syracuseStep 37623851 = 56435777) B56435777
theorem B2202025 : Blo 686314 2202025 := bstep (se 2 (by rfl) ⟨825759, by rfl⟩ : syracuseStep 2202025 = 1651519) B1651519
theorem B827263 : Blo 686314 827263 := bstep (se 1 (by rfl) ⟨620447, by rfl⟩ : syracuseStep 827263 = 1240895) B1240895
theorem B1745135 : Blo 686314 1745135 := bstep (se 1 (by rfl) ⟨1308851, by rfl⟩ : syracuseStep 1745135 = 2617703) B2617703
theorem B7938499 : Blo 686314 7938499 := bstep (se 1 (by rfl) ⟨5953874, by rfl⟩ : syracuseStep 7938499 = 11907749) B11907749
theorem B1549025 : Blo 686314 1549025 := bstep (se 2 (by rfl) ⟨580884, by rfl⟩ : syracuseStep 1549025 = 1161769) B1161769
theorem B2204651 : Blo 686314 2204651 := bstep (se 1 (by rfl) ⟨1653488, by rfl⟩ : syracuseStep 2204651 = 3306977) B3306977
theorem B4400381 : Blo 686314 4400381 := bstep (se 3 (by rfl) ⟨825071, by rfl⟩ : syracuseStep 4400381 = 1650143) B1650143
theorem B2205215 : Blo 686314 2205215 := bstep (se 1 (by rfl) ⟨1653911, by rfl⟩ : syracuseStep 2205215 = 3307823) B3307823
theorem B1549961 : Blo 686314 1549961 := bstep (se 2 (by rfl) ⟨581235, by rfl⟩ : syracuseStep 1549961 = 1162471) B1162471
theorem B1550015 : Blo 686314 1550015 := bstep (se 1 (by rfl) ⟨1162511, by rfl⟩ : syracuseStep 1550015 = 2325023) B2325023
theorem B1746623 : Blo 686314 1746623 := bstep (se 1 (by rfl) ⟨1309967, by rfl⟩ : syracuseStep 1746623 = 2619935) B2619935
theorem B3483809 : Blo 686314 3483809 := bstep (se 2 (by rfl) ⟨1306428, by rfl⟩ : syracuseStep 3483809 = 2612857) B2612857
theorem B1747241 : Blo 686314 1747241 := bstep (se 2 (by rfl) ⟨655215, by rfl⟩ : syracuseStep 1747241 = 1310431) B1310431
theorem B5876333 : Blo 686314 5876333 := bstep (se 3 (by rfl) ⟨1101812, by rfl⟩ : syracuseStep 5876333 = 2203625) B2203625
theorem B929071 : Blo 686314 929071 := bstep (se 1 (by rfl) ⟨696803, by rfl⟩ : syracuseStep 929071 = 1393607) B1393607
theorem B1551743 : Blo 686314 1551743 := bstep (se 1 (by rfl) ⟨1163807, by rfl⟩ : syracuseStep 1551743 = 2327615) B2327615
theorem B995431 : Blo 686314 995431 := bstep (se 1 (by rfl) ⟨746573, by rfl⟩ : syracuseStep 995431 = 1493147) B1493147
theorem B14332069 : Blo 686314 14332069 := bstep (se 4 (by rfl) ⟨1343631, by rfl⟩ : syracuseStep 14332069 = 2687263) B2687263
theorem B1159481 : Blo 686314 1159481 := bstep (se 2 (by rfl) ⟨434805, by rfl⟩ : syracuseStep 1159481 = 869611) B869611
theorem B1552697 : Blo 686314 1552697 := bstep (se 2 (by rfl) ⟨582261, by rfl⟩ : syracuseStep 1552697 = 1164523) B1164523
theorem B4174375 : Blo 686314 4174375 := bstep (se 1 (by rfl) ⟨3130781, by rfl⟩ : syracuseStep 4174375 = 6261563) B6261563
theorem B1160095 : Blo 686314 1160095 := bstep (se 1 (by rfl) ⟨870071, by rfl⟩ : syracuseStep 1160095 = 1740143) B1740143
theorem B1029497 : Blo 686314 1029497 := bstep (se 2 (by rfl) ⟨386061, by rfl⟩ : syracuseStep 1029497 = 772123) B772123
theorem B1029503 : Blo 686314 1029503 := bstep (se 1 (by rfl) ⟨772127, by rfl⟩ : syracuseStep 1029503 = 1544255) B1544255
theorem B1029659 : Blo 686314 1029659 := bstep (se 1 (by rfl) ⟨772244, by rfl⟩ : syracuseStep 1029659 = 1544489) B1544489
theorem B1029839 : Blo 686314 1029839 := bstep (se 1 (by rfl) ⟨772379, by rfl⟩ : syracuseStep 1029839 = 1544759) B1544759
theorem B1030043 : Blo 686314 1030043 := bstep (se 1 (by rfl) ⟨772532, by rfl⟩ : syracuseStep 1030043 = 1545065) B1545065
theorem B1030079 : Blo 686314 1030079 := bstep (se 1 (by rfl) ⟨772559, by rfl⟩ : syracuseStep 1030079 = 1545119) B1545119
theorem B1030247 : Blo 686314 1030247 := bstep (se 1 (by rfl) ⟨772685, by rfl⟩ : syracuseStep 1030247 = 1545371) B1545371
theorem B3913865 : Blo 686314 3913865 := bstep (se 2 (by rfl) ⟨1467699, by rfl⟩ : syracuseStep 3913865 = 2935399) B2935399
theorem B5880023 : Blo 686314 5880023 := bstep (se 1 (by rfl) ⟨4410017, by rfl⟩ : syracuseStep 5880023 = 8820035) B8820035
theorem B3914183 : Blo 686314 3914183 := bstep (se 1 (by rfl) ⟨2935637, by rfl⟩ : syracuseStep 3914183 = 5871275) B5871275
theorem B1030631 : Blo 686314 1030631 := bstep (se 1 (by rfl) ⟨772973, by rfl⟩ : syracuseStep 1030631 = 1545947) B1545947
theorem B14137847 : Blo 686314 14137847 := bstep (se 1 (by rfl) ⟨10603385, by rfl⟩ : syracuseStep 14137847 = 21206771) B21206771
theorem B1030703 : Blo 686314 1030703 := bstep (se 1 (by rfl) ⟨773027, by rfl⟩ : syracuseStep 1030703 = 1546055) B1546055
theorem B3488669 : Blo 686314 3488669 := bstep (se 3 (by rfl) ⟨654125, by rfl⟩ : syracuseStep 3488669 = 1308251) B1308251
theorem B1031375 : Blo 686314 1031375 := bstep (se 1 (by rfl) ⟨773531, by rfl⟩ : syracuseStep 1031375 = 1547063) B1547063
theorem B1031465 : Blo 686314 1031465 := bstep (se 2 (by rfl) ⟨386799, by rfl⟩ : syracuseStep 1031465 = 773599) B773599
theorem B1031495 : Blo 686314 1031495 := bstep (se 1 (by rfl) ⟨773621, by rfl⟩ : syracuseStep 1031495 = 1547243) B1547243
theorem B3489641 : Blo 686314 3489641 := bstep (se 2 (by rfl) ⟨1308615, by rfl⟩ : syracuseStep 3489641 = 2617231) B2617231
theorem B3915641 : Blo 686314 3915641 := bstep (se 2 (by rfl) ⟨1468365, by rfl⟩ : syracuseStep 3915641 = 2936731) B2936731
theorem B1032095 : Blo 686314 1032095 := bstep (se 1 (by rfl) ⟨774071, by rfl⟩ : syracuseStep 1032095 = 1548143) B1548143
theorem B2932699 : Blo 686314 2932699 := bstep (se 1 (by rfl) ⟨2199524, by rfl⟩ : syracuseStep 2932699 = 4399049) B4399049
theorem B1032185 : Blo 686314 1032185 := bstep (se 2 (by rfl) ⟨387069, by rfl⟩ : syracuseStep 1032185 = 774139) B774139
theorem B18890759 : Blo 686314 18890759 := bstep (se 1 (by rfl) ⟨14168069, by rfl⟩ : syracuseStep 18890759 = 28336139) B28336139
theorem B1032329 : Blo 686314 1032329 := bstep (se 2 (by rfl) ⟨387123, by rfl⟩ : syracuseStep 1032329 = 774247) B774247
theorem B1032425 : Blo 686314 1032425 := bstep (se 2 (by rfl) ⟨387159, by rfl⟩ : syracuseStep 1032425 = 774319) B774319
theorem B1163497 : Blo 686314 1163497 := bstep (se 2 (by rfl) ⟨436311, by rfl⟩ : syracuseStep 1163497 = 872623) B872623
theorem B1032551 : Blo 686314 1032551 := bstep (se 1 (by rfl) ⟨774413, by rfl⟩ : syracuseStep 1032551 = 1548827) B1548827
theorem B1032671 : Blo 686314 1032671 := bstep (se 1 (by rfl) ⟨774503, by rfl⟩ : syracuseStep 1032671 = 1549007) B1549007
theorem B9912851 : Blo 686314 9912851 := bstep (se 1 (by rfl) ⟨7434638, by rfl⟩ : syracuseStep 9912851 = 14869277) B14869277
theorem B1032923 : Blo 686314 1032923 := bstep (se 1 (by rfl) ⟨774692, by rfl⟩ : syracuseStep 1032923 = 1549385) B1549385
theorem B1033337 : Blo 686314 1033337 := bstep (se 2 (by rfl) ⟨387501, by rfl⟩ : syracuseStep 1033337 = 775003) B775003
theorem B1656083 : Blo 686314 1656083 := bstep (se 1 (by rfl) ⟨1242062, by rfl⟩ : syracuseStep 1656083 = 2484125) B2484125
theorem B1033535 : Blo 686314 1033535 := bstep (se 1 (by rfl) ⟨775151, by rfl⟩ : syracuseStep 1033535 = 1550303) B1550303
theorem B1034207 : Blo 686314 1034207 := bstep (se 1 (by rfl) ⟨775655, by rfl⟩ : syracuseStep 1034207 = 1551311) B1551311
theorem B3917807 : Blo 686314 3917807 := bstep (se 1 (by rfl) ⟨2938355, by rfl⟩ : syracuseStep 3917807 = 5876711) B5876711
theorem B1034267 : Blo 686314 1034267 := bstep (se 1 (by rfl) ⟨775700, by rfl⟩ : syracuseStep 1034267 = 1551401) B1551401
theorem B870583 : Blo 686314 870583 := bstep (se 1 (by rfl) ⟨652937, by rfl⟩ : syracuseStep 870583 = 1305875) B1305875
theorem B1034423 : Blo 686314 1034423 := bstep (se 1 (by rfl) ⟨775817, by rfl⟩ : syracuseStep 1034423 = 1551635) B1551635
theorem B772303 : Blo 686314 772303 := bstep (se 1 (by rfl) ⟨579227, by rfl⟩ : syracuseStep 772303 = 1158455) B1158455
theorem B1034447 : Blo 686314 1034447 := bstep (se 1 (by rfl) ⟨775835, by rfl⟩ : syracuseStep 1034447 = 1551671) B1551671
theorem B64539031 : Blo 686314 64539031 := bstep (se 1 (by rfl) ⟨48404273, by rfl⟩ : syracuseStep 64539031 = 96808547) B96808547
theorem B772699 : Blo 686314 772699 := bstep (se 1 (by rfl) ⟨579524, by rfl⟩ : syracuseStep 772699 = 1159049) B1159049
theorem B871003 : Blo 686314 871003 := bstep (se 1 (by rfl) ⟨653252, by rfl⟩ : syracuseStep 871003 = 1306505) B1306505
theorem B1034843 : Blo 686314 1034843 := bstep (se 1 (by rfl) ⟨776132, by rfl⟩ : syracuseStep 1034843 = 1552265) B1552265
theorem B1034987 : Blo 686314 1034987 := bstep (se 1 (by rfl) ⟨776240, by rfl⟩ : syracuseStep 1034987 = 1552481) B1552481
theorem B1035017 : Blo 686314 1035017 := bstep (se 2 (by rfl) ⟨388131, by rfl⟩ : syracuseStep 1035017 = 776263) B776263
theorem B1035431 : Blo 686314 1035431 := bstep (se 1 (by rfl) ⟨776573, by rfl⟩ : syracuseStep 1035431 = 1553147) B1553147
theorem B4247113 : Blo 686314 4247113 := bstep (se 2 (by rfl) ⟨1592667, by rfl⟩ : syracuseStep 4247113 = 3185335) B3185335
theorem B773743 : Blo 686314 773743 := bstep (se 1 (by rfl) ⟨580307, by rfl⟩ : syracuseStep 773743 = 1160615) B1160615
theorem B7819253 : Blo 686314 7819253 := bstep (se 5 (by rfl) ⟨366527, by rfl⟩ : syracuseStep 7819253 = 733055) B733055
theorem B5951663 : Blo 686314 5951663 := bstep (se 1 (by rfl) ⟨4463747, by rfl⟩ : syracuseStep 5951663 = 8927495) B8927495
theorem B3494663 : Blo 686314 3494663 := bstep (se 1 (by rfl) ⟨2620997, by rfl⟩ : syracuseStep 3494663 = 5241995) B5241995
theorem B3920723 : Blo 686314 3920723 := bstep (se 1 (by rfl) ⟨2940542, by rfl⟩ : syracuseStep 3920723 = 5881085) B5881085
theorem B5886857 : Blo 686314 5886857 := bstep (se 2 (by rfl) ⟨2207571, by rfl⟩ : syracuseStep 5886857 = 4415143) B4415143
theorem B775111 : Blo 686314 775111 := bstep (se 1 (by rfl) ⟨581333, by rfl⟩ : syracuseStep 775111 = 1162667) B1162667
theorem B775471 : Blo 686314 775471 := bstep (se 1 (by rfl) ⟨581603, by rfl⟩ : syracuseStep 775471 = 1163207) B1163207
theorem B1955497 : Blo 686314 1955497 := bstep (se 2 (by rfl) ⟨733311, by rfl⟩ : syracuseStep 1955497 = 1466623) B1466623
theorem B8836847 : Blo 686314 8836847 := bstep (se 1 (by rfl) ⟨6627635, by rfl⟩ : syracuseStep 8836847 = 13255271) B13255271
theorem B3921655 : Blo 686314 3921655 := bstep (se 1 (by rfl) ⟨2941241, by rfl⟩ : syracuseStep 3921655 = 5882483) B5882483
theorem B1955623 : Blo 686314 1955623 := bstep (se 1 (by rfl) ⟨1466717, by rfl⟩ : syracuseStep 1955623 = 2933435) B2933435
theorem B775975 : Blo 686314 775975 := bstep (se 1 (by rfl) ⟨581981, by rfl⟩ : syracuseStep 775975 = 1163963) B1163963
theorem B14899211 : Blo 686314 14899211 := bstep (se 1 (by rfl) ⟨11174408, by rfl⟩ : syracuseStep 14899211 = 22348817) B22348817
theorem B2316329 : Blo 686314 2316329 := bstep (se 2 (by rfl) ⟨868623, by rfl⟩ : syracuseStep 2316329 = 1737247) B1737247
theorem B21813683 : Blo 686314 21813683 := bstep (se 1 (by rfl) ⟨16360262, by rfl⟩ : syracuseStep 21813683 = 32720525) B32720525
theorem B2939449 : Blo 686314 2939449 := bstep (se 2 (by rfl) ⟨1102293, by rfl⟩ : syracuseStep 2939449 = 2204587) B2204587
theorem B1104959 : Blo 686314 1104959 := bstep (se 1 (by rfl) ⟨828719, by rfl⟩ : syracuseStep 1104959 = 1657439) B1657439
theorem B1956955 : Blo 686314 1956955 := bstep (se 1 (by rfl) ⟨1467716, by rfl⟩ : syracuseStep 1956955 = 2935433) B2935433
theorem B1957115 : Blo 686314 1957115 := bstep (se 1 (by rfl) ⟨1467836, by rfl⟩ : syracuseStep 1957115 = 2935673) B2935673
theorem B1858943 : Blo 686314 1858943 := bstep (se 1 (by rfl) ⟨1394207, by rfl⟩ : syracuseStep 1858943 = 2788415) B2788415
theorem B2580191 : Blo 686314 2580191 := bstep (se 1 (by rfl) ⟨1935143, by rfl⟩ : syracuseStep 2580191 = 3870287) B3870287
theorem B22667141 : Blo 686314 22667141 := bstep (se 4 (by rfl) ⟨2125044, by rfl⟩ : syracuseStep 22667141 = 4250089) B4250089
theorem B2613161 : Blo 686314 2613161 := bstep (se 2 (by rfl) ⟨979935, by rfl⟩ : syracuseStep 2613161 = 1959871) B1959871
theorem B8839307 : Blo 686314 8839307 := bstep (se 1 (by rfl) ⟨6629480, by rfl⟩ : syracuseStep 8839307 = 13258961) B13258961
theorem B4415759 : Blo 686314 4415759 := bstep (se 1 (by rfl) ⟨3311819, by rfl⟩ : syracuseStep 4415759 = 6623639) B6623639
theorem B2089633 : Blo 686314 2089633 := bstep (se 2 (by rfl) ⟨783612, by rfl⟩ : syracuseStep 2089633 = 1567225) B1567225
theorem B1467067 : Blo 686314 1467067 := bstep (se 1 (by rfl) ⟨1100300, by rfl⟩ : syracuseStep 1467067 = 2200601) B2200601
theorem B2941721 : Blo 686314 2941721 := bstep (se 2 (by rfl) ⟨1103145, by rfl⟩ : syracuseStep 2941721 = 2206291) B2206291
theorem B3924845 : Blo 686314 3924845 := bstep (se 3 (by rfl) ⟨735908, by rfl⟩ : syracuseStep 3924845 = 1471817) B1471817
theorem B3925097 : Blo 686314 3925097 := bstep (se 2 (by rfl) ⟨1471911, by rfl⟩ : syracuseStep 3925097 = 2943823) B2943823
theorem B2942183 : Blo 686314 2942183 := bstep (se 1 (by rfl) ⟨2206637, by rfl⟩ : syracuseStep 2942183 = 4413275) B4413275
theorem B4973957 : Blo 686314 4973957 := bstep (se 4 (by rfl) ⟨466308, by rfl⟩ : syracuseStep 4973957 = 932617) B932617
theorem B1861019 : Blo 686314 1861019 := bstep (se 1 (by rfl) ⟨1395764, by rfl⟩ : syracuseStep 1861019 = 2791529) B2791529
theorem B2319785 : Blo 686314 2319785 := bstep (se 2 (by rfl) ⟨869919, by rfl⟩ : syracuseStep 2319785 = 1739839) B1739839
theorem B8840947 : Blo 686314 8840947 := bstep (se 1 (by rfl) ⟨6630710, by rfl⟩ : syracuseStep 8840947 = 13261421) B13261421
theorem B1861679 : Blo 686314 1861679 := bstep (se 1 (by rfl) ⟨1396259, by rfl⟩ : syracuseStep 1861679 = 2792519) B2792519
theorem B1960031 : Blo 686314 1960031 := bstep (se 1 (by rfl) ⟨1470023, by rfl⟩ : syracuseStep 1960031 = 2940047) B2940047
theorem B1960271 : Blo 686314 1960271 := bstep (se 1 (by rfl) ⟨1470203, by rfl⟩ : syracuseStep 1960271 = 2940407) B2940407
theorem B1305001 : Blo 686314 1305001 := bstep (se 2 (by rfl) ⟨489375, by rfl⟩ : syracuseStep 1305001 = 978751) B978751
theorem B225995285 : Blo 686314 225995285 := bstep (se 6 (by rfl) ⟨5296764, by rfl⟩ : syracuseStep 225995285 = 10593529) B10593529
theorem B4254239 : Blo 686314 4254239 := bstep (se 1 (by rfl) ⟨3190679, by rfl⟩ : syracuseStep 4254239 = 6381359) B6381359
theorem B2091577 : Blo 686314 2091577 := bstep (se 2 (by rfl) ⟨784341, by rfl⟩ : syracuseStep 2091577 = 1568683) B1568683
theorem B4418219 : Blo 686314 4418219 := bstep (se 1 (by rfl) ⟨3313664, by rfl⟩ : syracuseStep 4418219 = 6627329) B6627329
theorem B2321243 : Blo 686314 2321243 := bstep (se 1 (by rfl) ⟨1740932, by rfl⟩ : syracuseStep 2321243 = 3481865) B3481865
theorem B9399347 : Blo 686314 9399347 := bstep (se 1 (by rfl) ⟨7049510, by rfl⟩ : syracuseStep 9399347 = 14099021) B14099021
theorem B1305791 : Blo 686314 1305791 := bstep (se 1 (by rfl) ⟨979343, by rfl⟩ : syracuseStep 1305791 = 1958687) B1958687
theorem B2322107 : Blo 686314 2322107 := bstep (se 1 (by rfl) ⟨1741580, by rfl⟩ : syracuseStep 2322107 = 3483161) B3483161
theorem B8351513 : Blo 686314 8351513 := bstep (se 2 (by rfl) ⟨3131817, by rfl⟩ : syracuseStep 8351513 = 6263635) B6263635
theorem B11792303 : Blo 686314 11792303 := bstep (se 1 (by rfl) ⟨8844227, by rfl⟩ : syracuseStep 11792303 = 17688455) B17688455
theorem B2977769 : Blo 686314 2977769 := bstep (se 2 (by rfl) ⟨1116663, by rfl⟩ : syracuseStep 2977769 = 2233327) B2233327
theorem B2322647 : Blo 686314 2322647 := bstep (se 1 (by rfl) ⟨1741985, by rfl⟩ : syracuseStep 2322647 = 3483971) B3483971
theorem B2584829 : Blo 686314 2584829 := bstep (se 3 (by rfl) ⟨484655, by rfl⟩ : syracuseStep 2584829 = 969311) B969311
theorem B4419859 : Blo 686314 4419859 := bstep (se 1 (by rfl) ⟨3314894, by rfl⟩ : syracuseStep 4419859 = 6629789) B6629789
theorem B3928445 : Blo 686314 3928445 := bstep (se 3 (by rfl) ⟨736583, by rfl⟩ : syracuseStep 3928445 = 1473167) B1473167
theorem B7828001 : Blo 686314 7828001 := bstep (se 2 (by rfl) ⟨2935500, by rfl⟩ : syracuseStep 7828001 = 5871001) B5871001
theorem B9696449 : Blo 686314 9696449 := bstep (se 2 (by rfl) ⟨3636168, by rfl⟩ : syracuseStep 9696449 = 7272337) B7272337
theorem B3143495 : Blo 686314 3143495 := bstep (se 1 (by rfl) ⟨2357621, by rfl⟩ : syracuseStep 3143495 = 4715243) B4715243
theorem B1308487 : Blo 686314 1308487 := bstep (se 1 (by rfl) ⟨981365, by rfl⟩ : syracuseStep 1308487 = 1962731) B1962731
theorem B2324699 : Blo 686314 2324699 := bstep (se 1 (by rfl) ⟨1743524, by rfl⟩ : syracuseStep 2324699 = 3487049) B3487049
theorem B14907685 : Blo 686314 14907685 := bstep (se 4 (by rfl) ⟨1397595, by rfl⟩ : syracuseStep 14907685 = 2795191) B2795191
theorem B1571129 : Blo 686314 1571129 := bstep (se 2 (by rfl) ⟨589173, by rfl⟩ : syracuseStep 1571129 = 1178347) B1178347
theorem B9927613 : Blo 686314 9927613 := bstep (se 3 (by rfl) ⟨1861427, by rfl⟩ : syracuseStep 9927613 = 3722855) B3722855
theorem B687071 : Blo 686314 687071 := bstep (se 1 (by rfl) ⟨515303, by rfl⟩ : syracuseStep 687071 = 1030607) B1030607
theorem B687131 : Blo 686314 687131 := bstep (se 1 (by rfl) ⟨515348, by rfl⟩ : syracuseStep 687131 = 1030697) B1030697
theorem B2325563 : Blo 686314 2325563 := bstep (se 1 (by rfl) ⟨1744172, by rfl⟩ : syracuseStep 2325563 = 3488345) B3488345
theorem B687259 : Blo 686314 687259 := bstep (se 1 (by rfl) ⟨515444, by rfl⟩ : syracuseStep 687259 = 1030889) B1030889
theorem B2096371 : Blo 686314 2096371 := bstep (se 1 (by rfl) ⟨1572278, by rfl⟩ : syracuseStep 2096371 = 3144557) B3144557
theorem B7830917 : Blo 686314 7830917 := bstep (se 4 (by rfl) ⟨734148, by rfl⟩ : syracuseStep 7830917 = 1468297) B1468297
theorem B687515 : Blo 686314 687515 := bstep (se 1 (by rfl) ⟨515636, by rfl⟩ : syracuseStep 687515 = 1031273) B1031273
theorem B2948521 : Blo 686314 2948521 := bstep (se 2 (by rfl) ⟨1105695, by rfl⟩ : syracuseStep 2948521 = 2211391) B2211391
theorem B687599 : Blo 686314 687599 := bstep (se 1 (by rfl) ⟨515699, by rfl⟩ : syracuseStep 687599 = 1031399) B1031399
theorem B1474031 : Blo 686314 1474031 := bstep (se 1 (by rfl) ⟨1105523, by rfl⟩ : syracuseStep 1474031 = 2211047) B2211047
theorem B687935 : Blo 686314 687935 := bstep (se 1 (by rfl) ⟨515951, by rfl⟩ : syracuseStep 687935 = 1031903) B1031903
theorem B687963 : Blo 686314 687963 := bstep (se 1 (by rfl) ⟨515972, by rfl⟩ : syracuseStep 687963 = 1031945) B1031945
theorem B688219 : Blo 686314 688219 := bstep (se 1 (by rfl) ⟨516164, by rfl⟩ : syracuseStep 688219 = 1032329) B1032329
theorem B688283 : Blo 686314 688283 := bstep (se 1 (by rfl) ⟨516212, by rfl⟩ : syracuseStep 688283 = 1032425) B1032425
theorem B688367 : Blo 686314 688367 := bstep (se 1 (by rfl) ⟨516275, by rfl⟩ : syracuseStep 688367 = 1032551) B1032551
theorem B688447 : Blo 686314 688447 := bstep (se 1 (by rfl) ⟨516335, by rfl⟩ : syracuseStep 688447 = 1032671) B1032671
theorem B688615 : Blo 686314 688615 := bstep (se 1 (by rfl) ⟨516461, by rfl⟩ : syracuseStep 688615 = 1032923) B1032923
theorem B10584665 : Blo 686314 10584665 := bstep (se 2 (by rfl) ⟨3969249, by rfl⟩ : syracuseStep 10584665 = 7938499) B7938499
theorem B688891 : Blo 686314 688891 := bstep (se 1 (by rfl) ⟨516668, by rfl⟩ : syracuseStep 688891 = 1033337) B1033337
theorem B689023 : Blo 686314 689023 := bstep (se 1 (by rfl) ⟨516767, by rfl⟩ : syracuseStep 689023 = 1033535) B1033535
theorem B2786177 : Blo 686314 2786177 := bstep (se 2 (by rfl) ⟨1044816, by rfl⟩ : syracuseStep 2786177 = 2089633) B2089633
theorem B31720385 : Blo 686314 31720385 := bstep (se 2 (by rfl) ⟨11895144, by rfl⟩ : syracuseStep 31720385 = 23790289) B23790289
theorem B689471 : Blo 686314 689471 := bstep (se 1 (by rfl) ⟨517103, by rfl⟩ : syracuseStep 689471 = 1034207) B1034207
theorem B689511 : Blo 686314 689511 := bstep (se 1 (by rfl) ⟨517133, by rfl⟩ : syracuseStep 689511 = 1034267) B1034267
theorem B689615 : Blo 686314 689615 := bstep (se 1 (by rfl) ⟨517211, by rfl⟩ : syracuseStep 689615 = 1034423) B1034423
theorem B689631 : Blo 686314 689631 := bstep (se 1 (by rfl) ⟨517223, by rfl⟩ : syracuseStep 689631 = 1034447) B1034447
theorem B5441087 : Blo 686314 5441087 := bstep (se 1 (by rfl) ⟨4080815, by rfl⟩ : syracuseStep 5441087 = 8161631) B8161631
theorem B689895 : Blo 686314 689895 := bstep (se 1 (by rfl) ⟨517421, by rfl⟩ : syracuseStep 689895 = 1034843) B1034843
theorem B689991 : Blo 686314 689991 := bstep (se 1 (by rfl) ⟨517493, by rfl⟩ : syracuseStep 689991 = 1034987) B1034987
theorem B690011 : Blo 686314 690011 := bstep (se 1 (by rfl) ⟨517508, by rfl⟩ : syracuseStep 690011 = 1035017) B1035017
theorem B690287 : Blo 686314 690287 := bstep (se 1 (by rfl) ⟨517715, by rfl⟩ : syracuseStep 690287 = 1035431) B1035431
theorem B5212835 : Blo 686314 5212835 := bstep (se 1 (by rfl) ⟨3909626, by rfl⟩ : syracuseStep 5212835 = 7819253) B7819253
theorem B3967775 : Blo 686314 3967775 := bstep (se 1 (by rfl) ⟨2975831, by rfl⟩ : syracuseStep 3967775 = 5951663) B5951663
theorem B25857197 : Blo 686314 25857197 := bstep (se 3 (by rfl) ⟨4848224, by rfl⟩ : syracuseStep 25857197 = 9696449) B9696449
theorem B2329775 : Blo 686314 2329775 := bstep (se 1 (by rfl) ⟨1747331, by rfl⟩ : syracuseStep 2329775 = 3494663) B3494663
theorem B86052041 : Blo 686314 86052041 := bstep (se 2 (by rfl) ⟨32269515, by rfl⟩ : syracuseStep 86052041 = 64539031) B64539031
theorem B1740001 : Blo 686314 1740001 := bstep (se 2 (by rfl) ⟨652500, by rfl⟩ : syracuseStep 1740001 = 1305001) B1305001
theorem B2788769 : Blo 686314 2788769 := bstep (se 2 (by rfl) ⟨1045788, by rfl⟩ : syracuseStep 2788769 = 2091577) B2091577
theorem B9932807 : Blo 686314 9932807 := bstep (se 1 (by rfl) ⟨7449605, by rfl⟩ : syracuseStep 9932807 = 14899211) B14899211
theorem B1544219 : Blo 686314 1544219 := bstep (se 1 (by rfl) ⟨1158164, by rfl⟩ : syracuseStep 1544219 = 2316329) B2316329
theorem B1742107 : Blo 686314 1742107 := bstep (se 1 (by rfl) ⟨1306580, by rfl⟩ : syracuseStep 1742107 = 2613161) B2613161
theorem B3315971 : Blo 686314 3315971 := bstep (se 1 (by rfl) ⟨2486978, by rfl⟩ : syracuseStep 3315971 = 4973957) B4973957
theorem B1546523 : Blo 686314 1546523 := bstep (se 1 (by rfl) ⟨1159892, by rfl⟩ : syracuseStep 1546523 = 2319785) B2319785
theorem B58169821 : Blo 686314 58169821 := bstep (se 3 (by rfl) ⟨10906841, by rfl⟩ : syracuseStep 58169821 = 21813683) B21813683
theorem B1546793 : Blo 686314 1546793 := bstep (se 2 (by rfl) ⟨580047, by rfl⟩ : syracuseStep 1546793 = 1160095) B1160095
theorem B11344637 : Blo 686314 11344637 := bstep (se 3 (by rfl) ⟨2127119, by rfl⟩ : syracuseStep 11344637 = 4254239) B4254239
theorem B1547495 : Blo 686314 1547495 := bstep (se 1 (by rfl) ⟨1160621, by rfl⟩ : syracuseStep 1547495 = 2321243) B2321243
theorem B6266231 : Blo 686314 6266231 := bstep (se 1 (by rfl) ⟨4699673, by rfl⟩ : syracuseStep 6266231 = 9399347) B9399347
theorem B1744649 : Blo 686314 1744649 := bstep (se 2 (by rfl) ⟨654243, by rfl⟩ : syracuseStep 1744649 = 1308487) B1308487
theorem B1548071 : Blo 686314 1548071 := bstep (se 1 (by rfl) ⟨1161053, by rfl⟩ : syracuseStep 1548071 = 2322107) B2322107
theorem B1548431 : Blo 686314 1548431 := bstep (se 1 (by rfl) ⟨1161323, by rfl⟩ : syracuseStep 1548431 = 2322647) B2322647
theorem B5218667 : Blo 686314 5218667 := bstep (se 1 (by rfl) ⟨3914000, by rfl⟩ : syracuseStep 5218667 = 7828001) B7828001
theorem B1549799 : Blo 686314 1549799 := bstep (se 1 (by rfl) ⟨1162349, by rfl⟩ : syracuseStep 1549799 = 2324699) B2324699
theorem B2795161 : Blo 686314 2795161 := bstep (se 2 (by rfl) ⟨1048185, by rfl⟩ : syracuseStep 2795161 = 2096371) B2096371
theorem B1550375 : Blo 686314 1550375 := bstep (se 1 (by rfl) ⟨1162781, by rfl⟩ : syracuseStep 1550375 = 2325563) B2325563
theorem B5220611 : Blo 686314 5220611 := bstep (se 1 (by rfl) ⟨3915458, by rfl⟩ : syracuseStep 5220611 = 7830917) B7830917
theorem B7940717 : Blo 686314 7940717 := bstep (se 3 (by rfl) ⟨1488884, by rfl⟩ : syracuseStep 7940717 = 2977769) B2977769
theorem B3910265 : Blo 686314 3910265 := bstep (se 2 (by rfl) ⟨1466349, by rfl⟩ : syracuseStep 3910265 = 2932699) B2932699
theorem B12593839 : Blo 686314 12593839 := bstep (se 1 (by rfl) ⟨9445379, by rfl⟩ : syracuseStep 12593839 = 18890759) B18890759
theorem B1551329 : Blo 686314 1551329 := bstep (se 2 (by rfl) ⟨581748, by rfl⟩ : syracuseStep 1551329 = 1163497) B1163497
theorem B6892877 : Blo 686314 6892877 := bstep (se 3 (by rfl) ⟨1292414, by rfl⟩ : syracuseStep 6892877 = 2584829) B2584829
theorem B1551707 : Blo 686314 1551707 := bstep (se 1 (by rfl) ⟨1163780, by rfl⟩ : syracuseStep 1551707 = 2327561) B2327561
theorem B6598111 : Blo 686314 6598111 := bstep (se 1 (by rfl) ⟨4948583, by rfl⟩ : syracuseStep 6598111 = 9897167) B9897167
theorem B1159231 : Blo 686314 1159231 := bstep (se 1 (by rfl) ⟨869423, by rfl⟩ : syracuseStep 1159231 = 1738847) B1738847
theorem B17609723 : Blo 686314 17609723 := bstep (se 1 (by rfl) ⟨13207292, by rfl⟩ : syracuseStep 17609723 = 26414585) B26414585
theorem B1029611 : Blo 686314 1029611 := bstep (se 1 (by rfl) ⟨772208, by rfl⟩ : syracuseStep 1029611 = 1544417) B1544417
theorem B1160777 : Blo 686314 1160777 := bstep (se 2 (by rfl) ⟨435291, by rfl⟩ : syracuseStep 1160777 = 870583) B870583
theorem B1029737 : Blo 686314 1029737 := bstep (se 2 (by rfl) ⟨386151, by rfl⟩ : syracuseStep 1029737 = 772303) B772303
theorem B31700807 : Blo 686314 31700807 := bstep (se 1 (by rfl) ⟨23775605, by rfl⟩ : syracuseStep 31700807 = 47551211) B47551211
theorem B1029959 : Blo 686314 1029959 := bstep (se 1 (by rfl) ⟨772469, by rfl⟩ : syracuseStep 1029959 = 1544939) B1544939
theorem B1030139 : Blo 686314 1030139 := bstep (se 1 (by rfl) ⟨772604, by rfl⟩ : syracuseStep 1030139 = 1545209) B1545209
theorem B5224499 : Blo 686314 5224499 := bstep (se 1 (by rfl) ⟨3918374, by rfl⟩ : syracuseStep 5224499 = 7836749) B7836749
theorem B1030199 : Blo 686314 1030199 := bstep (se 1 (by rfl) ⟨772649, by rfl⟩ : syracuseStep 1030199 = 1545299) B1545299
theorem B1030265 : Blo 686314 1030265 := bstep (se 2 (by rfl) ⟨386349, by rfl⟩ : syracuseStep 1030265 = 772699) B772699
theorem B1161337 : Blo 686314 1161337 := bstep (se 2 (by rfl) ⟨435501, by rfl⟩ : syracuseStep 1161337 = 871003) B871003
theorem B1030271 : Blo 686314 1030271 := bstep (se 1 (by rfl) ⟨772703, by rfl⟩ : syracuseStep 1030271 = 1545407) B1545407
theorem B1030319 : Blo 686314 1030319 := bstep (se 1 (by rfl) ⟨772739, by rfl⟩ : syracuseStep 1030319 = 1545479) B1545479
theorem B1161391 : Blo 686314 1161391 := bstep (se 1 (by rfl) ⟨871043, by rfl⟩ : syracuseStep 1161391 = 1742087) B1742087
theorem B1030559 : Blo 686314 1030559 := bstep (se 1 (by rfl) ⟨772919, by rfl⟩ : syracuseStep 1030559 = 1545839) B1545839
theorem B25082567 : Blo 686314 25082567 := bstep (se 1 (by rfl) ⟨18811925, by rfl⟩ : syracuseStep 25082567 = 37623851) B37623851
theorem B1031657 : Blo 686314 1031657 := bstep (se 2 (by rfl) ⟨386871, by rfl⟩ : syracuseStep 1031657 = 773743) B773743
theorem B1720127 : Blo 686314 1720127 := bstep (se 1 (by rfl) ⟨1290095, by rfl⟩ : syracuseStep 1720127 = 2580191) B2580191
theorem B1327241 : Blo 686314 1327241 := bstep (se 2 (by rfl) ⟨497715, by rfl⟩ : syracuseStep 1327241 = 995431) B995431
theorem B1163423 : Blo 686314 1163423 := bstep (se 1 (by rfl) ⟨872567, by rfl⟩ : syracuseStep 1163423 = 1745135) B1745135
theorem B1032683 : Blo 686314 1032683 := bstep (se 1 (by rfl) ⟨774512, by rfl⟩ : syracuseStep 1032683 = 1549025) B1549025
theorem B2933587 : Blo 686314 2933587 := bstep (se 1 (by rfl) ⟨2200190, by rfl⟩ : syracuseStep 2933587 = 4400381) B4400381
theorem B1033307 : Blo 686314 1033307 := bstep (se 1 (by rfl) ⟨774980, by rfl⟩ : syracuseStep 1033307 = 1549961) B1549961
theorem B1033343 : Blo 686314 1033343 := bstep (se 1 (by rfl) ⟨775007, by rfl⟩ : syracuseStep 1033343 = 1550015) B1550015
theorem B1164415 : Blo 686314 1164415 := bstep (se 1 (by rfl) ⟨873311, by rfl⟩ : syracuseStep 1164415 = 1746623) B1746623
theorem B1033481 : Blo 686314 1033481 := bstep (se 2 (by rfl) ⟨387555, by rfl⟩ : syracuseStep 1033481 = 775111) B775111
theorem B1164827 : Blo 686314 1164827 := bstep (se 1 (by rfl) ⟨873620, by rfl⟩ : syracuseStep 1164827 = 1747241) B1747241
theorem B1033961 : Blo 686314 1033961 := bstep (se 2 (by rfl) ⟨387735, by rfl⟩ : syracuseStep 1033961 = 775471) B775471
theorem B3917555 : Blo 686314 3917555 := bstep (se 1 (by rfl) ⟨2938166, by rfl⟩ : syracuseStep 3917555 = 5876333) B5876333
theorem B870527 : Blo 686314 870527 := bstep (se 1 (by rfl) ⟨652895, by rfl⟩ : syracuseStep 870527 = 1305791) B1305791
theorem B2607329 : Blo 686314 2607329 := bstep (se 2 (by rfl) ⟨977748, by rfl⟩ : syracuseStep 2607329 = 1955497) B1955497
theorem B1034495 : Blo 686314 1034495 := bstep (se 1 (by rfl) ⟨775871, by rfl⟩ : syracuseStep 1034495 = 1551743) B1551743
theorem B5228873 : Blo 686314 5228873 := bstep (se 2 (by rfl) ⟨1960827, by rfl⟩ : syracuseStep 5228873 = 3921655) B3921655
theorem B2607497 : Blo 686314 2607497 := bstep (se 2 (by rfl) ⟨977811, by rfl⟩ : syracuseStep 2607497 = 1955623) B1955623
theorem B1034633 : Blo 686314 1034633 := bstep (se 2 (by rfl) ⟨387987, by rfl⟩ : syracuseStep 1034633 = 775975) B775975
theorem B772987 : Blo 686314 772987 := bstep (se 1 (by rfl) ⟨579740, by rfl⟩ : syracuseStep 772987 = 1159481) B1159481
theorem B1035131 : Blo 686314 1035131 := bstep (se 1 (by rfl) ⟨776348, by rfl⟩ : syracuseStep 1035131 = 1552697) B1552697
theorem B19876913 : Blo 686314 19876913 := bstep (se 2 (by rfl) ⟨7453842, by rfl⟩ : syracuseStep 19876913 = 14907685) B14907685
theorem B2936033 : Blo 686314 2936033 := bstep (se 2 (by rfl) ⟨1101012, by rfl⟩ : syracuseStep 2936033 = 2202025) B2202025
theorem B3919265 : Blo 686314 3919265 := bstep (se 2 (by rfl) ⟨1469724, by rfl⟩ : syracuseStep 3919265 = 2939449) B2939449
theorem B2609243 : Blo 686314 2609243 := bstep (se 1 (by rfl) ⟨1956932, by rfl⟩ : syracuseStep 2609243 = 3913865) B3913865
theorem B2609273 : Blo 686314 2609273 := bstep (se 2 (by rfl) ⟨978477, by rfl⟩ : syracuseStep 2609273 = 1956955) B1956955
theorem B3920015 : Blo 686314 3920015 := bstep (se 1 (by rfl) ⟨2940011, by rfl⟩ : syracuseStep 3920015 = 5880023) B5880023
theorem B2609455 : Blo 686314 2609455 := bstep (se 1 (by rfl) ⟨1957091, by rfl⟩ : syracuseStep 2609455 = 3914183) B3914183
theorem B9425231 : Blo 686314 9425231 := bstep (se 1 (by rfl) ⟨7068923, by rfl⟩ : syracuseStep 9425231 = 14137847) B14137847
theorem B4412069 : Blo 686314 4412069 := bstep (se 4 (by rfl) ⟨413631, by rfl⟩ : syracuseStep 4412069 = 827263) B827263
theorem B60445709 : Blo 686314 60445709 := bstep (se 3 (by rfl) ⟨11333570, by rfl⟩ : syracuseStep 60445709 = 22667141) B22667141
theorem B2610427 : Blo 686314 2610427 := bstep (se 1 (by rfl) ⟨1957820, by rfl⟩ : syracuseStep 2610427 = 3915641) B3915641
theorem B6608567 : Blo 686314 6608567 := bstep (se 1 (by rfl) ⟨4956425, by rfl⟩ : syracuseStep 6608567 = 9912851) B9912851
theorem B76437701 : Blo 686314 76437701 := bstep (se 4 (by rfl) ⟨7166034, by rfl⟩ : syracuseStep 76437701 = 14332069) B14332069
theorem B1956089 : Blo 686314 1956089 := bstep (se 2 (by rfl) ⟨733533, by rfl⟩ : syracuseStep 1956089 = 1467067) B1467067
theorem B2611871 : Blo 686314 2611871 := bstep (se 1 (by rfl) ⟨1958903, by rfl⟩ : syracuseStep 2611871 = 3917807) B3917807
theorem B11787929 : Blo 686314 11787929 := bstep (se 2 (by rfl) ⟨4420473, by rfl⟩ : syracuseStep 11787929 = 8840947) B8840947
theorem B2318543 : Blo 686314 2318543 := bstep (se 1 (by rfl) ⟨1738907, by rfl⟩ : syracuseStep 2318543 = 3477815) B3477815
theorem B2613815 : Blo 686314 2613815 := bstep (se 1 (by rfl) ⟨1960361, by rfl⟩ : syracuseStep 2613815 = 3920723) B3920723
theorem B3924571 : Blo 686314 3924571 := bstep (se 1 (by rfl) ⟨2943428, by rfl⟩ : syracuseStep 3924571 = 5886857) B5886857
theorem B4416221 : Blo 686314 4416221 := bstep (se 3 (by rfl) ⟨828041, by rfl⟩ : syracuseStep 4416221 = 1656083) B1656083
theorem B5891231 : Blo 686314 5891231 := bstep (se 1 (by rfl) ⟨4418423, by rfl⟩ : syracuseStep 5891231 = 8836847) B8836847
theorem B1238761 : Blo 686314 1238761 := bstep (se 2 (by rfl) ⟨464535, by rfl⟩ : syracuseStep 1238761 = 929071) B929071
theorem B5662817 : Blo 686314 5662817 := bstep (se 2 (by rfl) ⟨2123556, by rfl⟩ : syracuseStep 5662817 = 4247113) B4247113
theorem B1304743 : Blo 686314 1304743 := bstep (se 1 (by rfl) ⟨978557, by rfl⟩ : syracuseStep 1304743 = 1957115) B1957115
theorem B8382653 : Blo 686314 8382653 := bstep (se 3 (by rfl) ⟨1571747, by rfl⟩ : syracuseStep 8382653 = 3143495) B3143495
theorem B1239295 : Blo 686314 1239295 := bstep (se 1 (by rfl) ⟨929471, by rfl⟩ : syracuseStep 1239295 = 1858943) B1858943
theorem B5892871 : Blo 686314 5892871 := bstep (se 1 (by rfl) ⟨4419653, by rfl⟩ : syracuseStep 5892871 = 8839307) B8839307
theorem B2943839 : Blo 686314 2943839 := bstep (se 1 (by rfl) ⟨2207879, by rfl⟩ : syracuseStep 2943839 = 4415759) B4415759
theorem B5893145 : Blo 686314 5893145 := bstep (se 2 (by rfl) ⟨2209929, by rfl⟩ : syracuseStep 5893145 = 4419859) B4419859
theorem B1961147 : Blo 686314 1961147 := bstep (se 1 (by rfl) ⟨1470860, by rfl⟩ : syracuseStep 1961147 = 2941721) B2941721
theorem B2616563 : Blo 686314 2616563 := bstep (se 1 (by rfl) ⟨1962422, by rfl⟩ : syracuseStep 2616563 = 3924845) B3924845
theorem B1469767 : Blo 686314 1469767 := bstep (se 1 (by rfl) ⟨1102325, by rfl⟩ : syracuseStep 1469767 = 2204651) B2204651
theorem B5565833 : Blo 686314 5565833 := bstep (se 2 (by rfl) ⟨2087187, by rfl⟩ : syracuseStep 5565833 = 4174375) B4174375
theorem B2616731 : Blo 686314 2616731 := bstep (se 1 (by rfl) ⟨1962548, by rfl⟩ : syracuseStep 2616731 = 3925097) B3925097
theorem B1961455 : Blo 686314 1961455 := bstep (se 1 (by rfl) ⟨1471091, by rfl⟩ : syracuseStep 1961455 = 2942183) B2942183
theorem B1240679 : Blo 686314 1240679 := bstep (se 1 (by rfl) ⟨930509, by rfl⟩ : syracuseStep 1240679 = 1861019) B1861019
theorem B1470143 : Blo 686314 1470143 := bstep (se 1 (by rfl) ⟨1102607, by rfl⟩ : syracuseStep 1470143 = 2205215) B2205215
theorem B2322377 : Blo 686314 2322377 := bstep (se 2 (by rfl) ⟨870891, by rfl⟩ : syracuseStep 2322377 = 1741783) B1741783
theorem B1241119 : Blo 686314 1241119 := bstep (se 1 (by rfl) ⟨930839, by rfl⟩ : syracuseStep 1241119 = 1861679) B1861679
theorem B1306687 : Blo 686314 1306687 := bstep (se 1 (by rfl) ⟨980015, by rfl⟩ : syracuseStep 1306687 = 1960031) B1960031
theorem B2322539 : Blo 686314 2322539 := bstep (se 1 (by rfl) ⟨1741904, by rfl⟩ : syracuseStep 2322539 = 3483809) B3483809
theorem B1306847 : Blo 686314 1306847 := bstep (se 1 (by rfl) ⟨980135, by rfl⟩ : syracuseStep 1306847 = 1960271) B1960271
theorem B150663523 : Blo 686314 150663523 := bstep (se 1 (by rfl) ⟨112997642, by rfl⟩ : syracuseStep 150663523 = 225995285) B225995285
theorem B2945479 : Blo 686314 2945479 := bstep (se 1 (by rfl) ⟨2209109, by rfl⟩ : syracuseStep 2945479 = 4418219) B4418219
theorem B4420169 : Blo 686314 4420169 := bstep (se 2 (by rfl) ⟨1657563, by rfl⟩ : syracuseStep 4420169 = 3315127) B3315127
theorem B7434989 : Blo 686314 7434989 := bstep (se 3 (by rfl) ⟨1394060, by rfl⟩ : syracuseStep 7434989 = 2788121) B2788121
theorem B5567675 : Blo 686314 5567675 := bstep (se 1 (by rfl) ⟨4175756, by rfl⟩ : syracuseStep 5567675 = 8351513) B8351513
theorem B7861535 : Blo 686314 7861535 := bstep (se 1 (by rfl) ⟨5896151, by rfl⟩ : syracuseStep 7861535 = 11792303) B11792303
theorem B2946557 : Blo 686314 2946557 := bstep (se 3 (by rfl) ⟨552479, by rfl⟩ : syracuseStep 2946557 = 1104959) B1104959
theorem B2618963 : Blo 686314 2618963 := bstep (se 1 (by rfl) ⟨1964222, by rfl⟩ : syracuseStep 2618963 = 3928445) B3928445
theorem B44759141 : Blo 686314 44759141 := bstep (se 4 (by rfl) ⟨4196169, by rfl⟩ : syracuseStep 44759141 = 8392339) B8392339
theorem B686331 : Blo 686314 686331 := bstep (se 1 (by rfl) ⟨514748, by rfl⟩ : syracuseStep 686331 = 1029497) B1029497
theorem B686335 : Blo 686314 686335 := bstep (se 1 (by rfl) ⟨514751, by rfl⟩ : syracuseStep 686335 = 1029503) B1029503
theorem B686439 : Blo 686314 686439 := bstep (se 1 (by rfl) ⟨514829, by rfl⟩ : syracuseStep 686439 = 1029659) B1029659
theorem B686559 : Blo 686314 686559 := bstep (se 1 (by rfl) ⟨514919, by rfl⟩ : syracuseStep 686559 = 1029839) B1029839
theorem B13236817 : Blo 686314 13236817 := bstep (se 2 (by rfl) ⟨4963806, by rfl⟩ : syracuseStep 13236817 = 9927613) B9927613
theorem B686695 : Blo 686314 686695 := bstep (se 1 (by rfl) ⟨515021, by rfl⟩ : syracuseStep 686695 = 1030043) B1030043
theorem B686719 : Blo 686314 686719 := bstep (se 1 (by rfl) ⟨515039, by rfl⟩ : syracuseStep 686719 = 1030079) B1030079
theorem B686831 : Blo 686314 686831 := bstep (se 1 (by rfl) ⟨515123, by rfl⟩ : syracuseStep 686831 = 1030247) B1030247
theorem B1047419 : Blo 686314 1047419 := bstep (se 1 (by rfl) ⟨785564, by rfl⟩ : syracuseStep 1047419 = 1571129) B1571129
theorem B687087 : Blo 686314 687087 := bstep (se 1 (by rfl) ⟨515315, by rfl⟩ : syracuseStep 687087 = 1030631) B1030631
theorem B687135 : Blo 686314 687135 := bstep (se 1 (by rfl) ⟨515351, by rfl⟩ : syracuseStep 687135 = 1030703) B1030703
theorem B3931361 : Blo 686314 3931361 := bstep (se 2 (by rfl) ⟨1474260, by rfl⟩ : syracuseStep 3931361 = 2948521) B2948521
theorem B2325779 : Blo 686314 2325779 := bstep (se 1 (by rfl) ⟨1744334, by rfl⟩ : syracuseStep 2325779 = 3488669) B3488669
theorem B687583 : Blo 686314 687583 := bstep (se 1 (by rfl) ⟨515687, by rfl⟩ : syracuseStep 687583 = 1031375) B1031375
theorem B687643 : Blo 686314 687643 := bstep (se 1 (by rfl) ⟨515732, by rfl⟩ : syracuseStep 687643 = 1031465) B1031465
theorem B687663 : Blo 686314 687663 := bstep (se 1 (by rfl) ⟨515747, by rfl⟩ : syracuseStep 687663 = 1031495) B1031495
theorem B982687 : Blo 686314 982687 := bstep (se 1 (by rfl) ⟨737015, by rfl⟩ : syracuseStep 982687 = 1474031) B1474031
theorem B2326427 : Blo 686314 2326427 := bstep (se 1 (by rfl) ⟨1744820, by rfl⟩ : syracuseStep 2326427 = 3489641) B3489641
theorem B688063 : Blo 686314 688063 := bstep (se 1 (by rfl) ⟨516047, by rfl⟩ : syracuseStep 688063 = 1032095) B1032095
theorem B688123 : Blo 686314 688123 := bstep (se 1 (by rfl) ⟨516092, by rfl⟩ : syracuseStep 688123 = 1032185) B1032185
theorem B884827 : Blo 686314 884827 := bstep (se 1 (by rfl) ⟨663620, by rfl⟩ : syracuseStep 884827 = 1327241) B1327241
theorem B688455 : Blo 686314 688455 := bstep (se 1 (by rfl) ⟨516341, by rfl⟩ : syracuseStep 688455 = 1032683) B1032683
theorem B688871 : Blo 686314 688871 := bstep (se 1 (by rfl) ⟨516653, by rfl⟩ : syracuseStep 688871 = 1033307) B1033307
theorem B688895 : Blo 686314 688895 := bstep (se 1 (by rfl) ⟨516671, by rfl⟩ : syracuseStep 688895 = 1033343) B1033343
theorem B688987 : Blo 686314 688987 := bstep (se 1 (by rfl) ⟨516740, by rfl⟩ : syracuseStep 688987 = 1033481) B1033481
theorem B689307 : Blo 686314 689307 := bstep (se 1 (by rfl) ⟨516980, by rfl⟩ : syracuseStep 689307 = 1033961) B1033961
theorem B1738219 : Blo 686314 1738219 := bstep (se 1 (by rfl) ⟨1303664, by rfl⟩ : syracuseStep 1738219 = 2607329) B2607329
theorem B689663 : Blo 686314 689663 := bstep (se 1 (by rfl) ⟨517247, by rfl⟩ : syracuseStep 689663 = 1034495) B1034495
theorem B1738331 : Blo 686314 1738331 := bstep (se 1 (by rfl) ⟨1303748, by rfl⟩ : syracuseStep 1738331 = 2607497) B2607497
theorem B689755 : Blo 686314 689755 := bstep (se 1 (by rfl) ⟨517316, by rfl⟩ : syracuseStep 689755 = 1034633) B1034633
theorem B3475223 : Blo 686314 3475223 := bstep (se 1 (by rfl) ⟨2606417, by rfl⟩ : syracuseStep 3475223 = 5212835) B5212835
theorem B690087 : Blo 686314 690087 := bstep (se 1 (by rfl) ⟨517565, by rfl⟩ : syracuseStep 690087 = 1035131) B1035131
theorem B17238131 : Blo 686314 17238131 := bstep (se 1 (by rfl) ⟨12928598, by rfl⟩ : syracuseStep 17238131 = 25857197) B25857197
theorem B6621871 : Blo 686314 6621871 := bstep (se 1 (by rfl) ⟨4966403, by rfl⟩ : syracuseStep 6621871 = 9932807) B9932807
theorem B1739495 : Blo 686314 1739495 := bstep (se 1 (by rfl) ⟨1304621, by rfl⟩ : syracuseStep 1739495 = 2609243) B2609243
theorem B1739515 : Blo 686314 1739515 := bstep (se 1 (by rfl) ⟨1304636, by rfl⟩ : syracuseStep 1739515 = 2609273) B2609273
theorem B1739657 : Blo 686314 1739657 := bstep (se 2 (by rfl) ⟨652371, by rfl⟩ : syracuseStep 1739657 = 1304743) B1304743
theorem B14847133 : Blo 686314 14847133 := bstep (se 3 (by rfl) ⟨2783837, by rfl⟩ : syracuseStep 14847133 = 5567675) B5567675
theorem B50958467 : Blo 686314 50958467 := bstep (se 1 (by rfl) ⟨38218850, by rfl⟩ : syracuseStep 50958467 = 76437701) B76437701
theorem B1741247 : Blo 686314 1741247 := bstep (se 1 (by rfl) ⟨1305935, by rfl⟩ : syracuseStep 1741247 = 2611871) B2611871
theorem B1545641 : Blo 686314 1545641 := bstep (se 2 (by rfl) ⟨579615, by rfl⟩ : syracuseStep 1545641 = 1159231) B1159231
theorem B1742249 : Blo 686314 1742249 := bstep (se 2 (by rfl) ⟨653343, by rfl⟩ : syracuseStep 1742249 = 1306687) B1306687
theorem B1545695 : Blo 686314 1545695 := bstep (se 1 (by rfl) ⟨1159271, by rfl⟩ : syracuseStep 1545695 = 2318543) B2318543
theorem B3479111 : Blo 686314 3479111 := bstep (se 1 (by rfl) ⟨2609333, by rfl⟩ : syracuseStep 3479111 = 5218667) B5218667
theorem B1742543 : Blo 686314 1742543 := bstep (se 1 (by rfl) ⟨1306907, by rfl⟩ : syracuseStep 1742543 = 2613815) B2613815
theorem B3479273 : Blo 686314 3479273 := bstep (se 2 (by rfl) ⟨1304727, by rfl⟩ : syracuseStep 3479273 = 2609455) B2609455
theorem B5216237 : Blo 686314 5216237 := bstep (se 3 (by rfl) ⟨978044, by rfl⟩ : syracuseStep 5216237 = 1956089) B1956089
theorem B3775211 : Blo 686314 3775211 := bstep (se 1 (by rfl) ⟨2831408, by rfl⟩ : syracuseStep 3775211 = 5662817) B5662817
theorem B3480407 : Blo 686314 3480407 := bstep (se 1 (by rfl) ⟨2610305, by rfl⟩ : syracuseStep 3480407 = 5220611) B5220611
theorem B3480569 : Blo 686314 3480569 := bstep (se 2 (by rfl) ⟨1305213, by rfl⟩ : syracuseStep 3480569 = 2610427) B2610427
theorem B1744375 : Blo 686314 1744375 := bstep (se 1 (by rfl) ⟨1308281, by rfl⟩ : syracuseStep 1744375 = 2616563) B2616563
theorem B3710555 : Blo 686314 3710555 := bstep (se 1 (by rfl) ⟨2782916, by rfl⟩ : syracuseStep 3710555 = 5565833) B5565833
theorem B1744487 : Blo 686314 1744487 := bstep (se 1 (by rfl) ⟨1308365, by rfl⟩ : syracuseStep 1744487 = 2616731) B2616731
theorem B827119 : Blo 686314 827119 := bstep (se 1 (by rfl) ⟨620339, by rfl⟩ : syracuseStep 827119 = 1240679) B1240679
theorem B1548251 : Blo 686314 1548251 := bstep (se 1 (by rfl) ⟨1161188, by rfl⟩ : syracuseStep 1548251 = 2322377) B2322377
theorem B1548359 : Blo 686314 1548359 := bstep (se 1 (by rfl) ⟨1161269, by rfl⟩ : syracuseStep 1548359 = 2322539) B2322539
theorem B1548449 : Blo 686314 1548449 := bstep (se 2 (by rfl) ⟨580668, by rfl⟩ : syracuseStep 1548449 = 1161337) B1161337
theorem B1548521 : Blo 686314 1548521 := bstep (se 2 (by rfl) ⟨580695, by rfl⟩ : syracuseStep 1548521 = 1161391) B1161391
theorem B4956659 : Blo 686314 4956659 := bstep (se 1 (by rfl) ⟨3717494, by rfl⟩ : syracuseStep 4956659 = 7434989) B7434989
theorem B11739815 : Blo 686314 11739815 := bstep (se 1 (by rfl) ⟨8804861, by rfl⟩ : syracuseStep 11739815 = 17609723) B17609723
theorem B1745975 : Blo 686314 1745975 := bstep (se 1 (by rfl) ⟨1309481, by rfl⟩ : syracuseStep 1745975 = 2618963) B2618963
theorem B3482999 : Blo 686314 3482999 := bstep (se 1 (by rfl) ⟨2612249, by rfl⟩ : syracuseStep 3482999 = 5224499) B5224499
theorem B16721711 : Blo 686314 16721711 := bstep (se 1 (by rfl) ⟨12541283, by rfl⟩ : syracuseStep 16721711 = 25082567) B25082567
theorem B698279 : Blo 686314 698279 := bstep (se 1 (by rfl) ⟨523709, by rfl⟩ : syracuseStep 698279 = 1047419) B1047419
theorem B1550519 : Blo 686314 1550519 := bstep (se 1 (by rfl) ⟨1162889, by rfl⟩ : syracuseStep 1550519 = 2325779) B2325779
theorem B1550951 : Blo 686314 1550951 := bstep (se 1 (by rfl) ⟨1163213, by rfl⟩ : syracuseStep 1550951 = 2326427) B2326427
theorem B7056443 : Blo 686314 7056443 := bstep (se 1 (by rfl) ⟨5292332, by rfl⟩ : syracuseStep 7056443 = 10584665) B10584665
theorem B21146923 : Blo 686314 21146923 := bstep (se 1 (by rfl) ⟨15860192, by rfl⟩ : syracuseStep 21146923 = 31720385) B31720385
theorem B3911449 : Blo 686314 3911449 := bstep (se 2 (by rfl) ⟨1466793, by rfl⟩ : syracuseStep 3911449 = 2933587) B2933587
theorem B1552553 : Blo 686314 1552553 := bstep (se 2 (by rfl) ⟨582207, by rfl⟩ : syracuseStep 1552553 = 1164415) B1164415
theorem B3485915 : Blo 686314 3485915 := bstep (se 1 (by rfl) ⟨2614436, by rfl⟩ : syracuseStep 3485915 = 5228873) B5228873
theorem B13251275 : Blo 686314 13251275 := bstep (se 1 (by rfl) ⟨9938456, by rfl⟩ : syracuseStep 13251275 = 19876913) B19876913
theorem B1553183 : Blo 686314 1553183 := bstep (se 1 (by rfl) ⟨1164887, by rfl⟩ : syracuseStep 1553183 = 2329775) B2329775
theorem B1651681 : Blo 686314 1651681 := bstep (se 2 (by rfl) ⟨619380, by rfl⟩ : syracuseStep 1651681 = 1238761) B1238761
theorem B1029479 : Blo 686314 1029479 := bstep (se 1 (by rfl) ⟨772109, by rfl⟩ : syracuseStep 1029479 = 1544219) B1544219
theorem B1652393 : Blo 686314 1652393 := bstep (se 2 (by rfl) ⟨619647, by rfl⟩ : syracuseStep 1652393 = 1239295) B1239295
theorem B16791785 : Blo 686314 16791785 := bstep (se 2 (by rfl) ⟨6296919, by rfl⟩ : syracuseStep 16791785 = 12593839) B12593839
theorem B1030649 : Blo 686314 1030649 := bstep (se 2 (by rfl) ⟨386493, by rfl⟩ : syracuseStep 1030649 = 772987) B772987
theorem B2210647 : Blo 686314 2210647 := bstep (se 1 (by rfl) ⟨1657985, by rfl⟩ : syracuseStep 2210647 = 3315971) B3315971
theorem B1031015 : Blo 686314 1031015 := bstep (se 1 (by rfl) ⟨773261, by rfl⟩ : syracuseStep 1031015 = 1546523) B1546523
theorem B1031195 : Blo 686314 1031195 := bstep (se 1 (by rfl) ⟨773396, by rfl⟩ : syracuseStep 1031195 = 1546793) B1546793
theorem B8797481 : Blo 686314 8797481 := bstep (se 2 (by rfl) ⟨3299055, by rfl⟩ : syracuseStep 8797481 = 6598111) B6598111
theorem B1031663 : Blo 686314 1031663 := bstep (se 1 (by rfl) ⟨773747, by rfl⟩ : syracuseStep 1031663 = 1547495) B1547495
theorem B4177487 : Blo 686314 4177487 := bstep (se 1 (by rfl) ⟨3133115, by rfl⟩ : syracuseStep 4177487 = 6266231) B6266231
theorem B1163099 : Blo 686314 1163099 := bstep (se 1 (by rfl) ⟨872324, by rfl⟩ : syracuseStep 1163099 = 1744649) B1744649
theorem B1032047 : Blo 686314 1032047 := bstep (se 1 (by rfl) ⟨774035, by rfl⟩ : syracuseStep 1032047 = 1548071) B1548071
theorem B1654825 : Blo 686314 1654825 := bstep (se 2 (by rfl) ⟨620559, by rfl⟩ : syracuseStep 1654825 = 1241119) B1241119
theorem B1032287 : Blo 686314 1032287 := bstep (se 1 (by rfl) ⟨774215, by rfl⟩ : syracuseStep 1032287 = 1548431) B1548431
theorem B200884697 : Blo 686314 200884697 := bstep (se 2 (by rfl) ⟨75331761, by rfl⟩ : syracuseStep 200884697 = 150663523) B150663523
theorem B1033199 : Blo 686314 1033199 := bstep (se 1 (by rfl) ⟨774899, by rfl⟩ : syracuseStep 1033199 = 1549799) B1549799
theorem B1033583 : Blo 686314 1033583 := bstep (se 1 (by rfl) ⟨775187, by rfl⟩ : syracuseStep 1033583 = 1550375) B1550375
theorem B5588435 : Blo 686314 5588435 := bstep (se 1 (by rfl) ⟨4191326, by rfl⟩ : syracuseStep 5588435 = 8382653) B8382653
theorem B5293811 : Blo 686314 5293811 := bstep (se 1 (by rfl) ⟨3970358, by rfl⟩ : syracuseStep 5293811 = 7940717) B7940717
theorem B2606843 : Blo 686314 2606843 := bstep (se 1 (by rfl) ⟨1955132, by rfl⟩ : syracuseStep 2606843 = 3910265) B3910265
theorem B1034219 : Blo 686314 1034219 := bstep (se 1 (by rfl) ⟨775664, by rfl⟩ : syracuseStep 1034219 = 1551329) B1551329
theorem B1034471 : Blo 686314 1034471 := bstep (se 1 (by rfl) ⟨775853, by rfl⟩ : syracuseStep 1034471 = 1551707) B1551707
theorem B871231 : Blo 686314 871231 := bstep (se 1 (by rfl) ⟨653423, by rfl⟩ : syracuseStep 871231 = 1306847) B1306847
theorem B17649089 : Blo 686314 17649089 := bstep (se 2 (by rfl) ⟨6618408, by rfl⟩ : syracuseStep 17649089 = 13236817) B13236817
theorem B773851 : Blo 686314 773851 := bstep (se 1 (by rfl) ⟨580388, by rfl⟩ : syracuseStep 773851 = 1160777) B1160777
theorem B29839427 : Blo 686314 29839427 := bstep (se 1 (by rfl) ⟨22379570, by rfl⟩ : syracuseStep 29839427 = 44759141) B44759141
theorem B775615 : Blo 686314 775615 := bstep (se 1 (by rfl) ⟨581711, by rfl⟩ : syracuseStep 775615 = 1163423) B1163423
theorem B1857451 : Blo 686314 1857451 := bstep (se 1 (by rfl) ⟨1393088, by rfl⟩ : syracuseStep 1857451 = 2786177) B2786177
theorem B5232761 : Blo 686314 5232761 := bstep (se 2 (by rfl) ⟨1962285, by rfl⟩ : syracuseStep 5232761 = 3924571) B3924571
theorem B776551 : Blo 686314 776551 := bstep (se 1 (by rfl) ⟨582413, by rfl⟩ : syracuseStep 776551 = 1164827) B1164827
theorem B3627391 : Blo 686314 3627391 := bstep (se 1 (by rfl) ⟨2720543, by rfl⟩ : syracuseStep 3627391 = 5441087) B5441087
theorem B2611703 : Blo 686314 2611703 := bstep (se 1 (by rfl) ⟨1958777, by rfl⟩ : syracuseStep 2611703 = 3917555) B3917555
theorem B2645183 : Blo 686314 2645183 := bstep (se 1 (by rfl) ⟨1983887, by rfl⟩ : syracuseStep 2645183 = 3967775) B3967775
theorem B57368027 : Blo 686314 57368027 := bstep (se 1 (by rfl) ⟨43026020, by rfl⟩ : syracuseStep 57368027 = 86052041) B86052041
theorem B1957355 : Blo 686314 1957355 := bstep (se 1 (by rfl) ⟨1468016, by rfl⟩ : syracuseStep 1957355 = 2936033) B2936033
theorem B3726881 : Blo 686314 3726881 := bstep (se 2 (by rfl) ⟨1397580, by rfl⟩ : syracuseStep 3726881 = 2795161) B2795161
theorem B2612843 : Blo 686314 2612843 := bstep (se 1 (by rfl) ⟨1959632, by rfl⟩ : syracuseStep 2612843 = 3919265) B3919265
theorem B2613343 : Blo 686314 2613343 := bstep (se 1 (by rfl) ⟨1960007, by rfl⟩ : syracuseStep 2613343 = 3920015) B3920015
theorem B6283487 : Blo 686314 6283487 := bstep (se 1 (by rfl) ⟨4712615, by rfl⟩ : syracuseStep 6283487 = 9425231) B9425231
theorem B2941379 : Blo 686314 2941379 := bstep (se 1 (by rfl) ⟨2206034, by rfl⟩ : syracuseStep 2941379 = 4412069) B4412069
theorem B40297139 : Blo 686314 40297139 := bstep (se 1 (by rfl) ⟨30222854, by rfl⟩ : syracuseStep 40297139 = 60445709) B60445709
theorem B7857161 : Blo 686314 7857161 := bstep (se 2 (by rfl) ⟨2946435, by rfl⟩ : syracuseStep 7857161 = 5892871) B5892871
theorem B2320001 : Blo 686314 2320001 := bstep (se 2 (by rfl) ⟨870000, by rfl⟩ : syracuseStep 2320001 = 1740001) B1740001
theorem B1959689 : Blo 686314 1959689 := bstep (se 2 (by rfl) ⟨734883, by rfl⟩ : syracuseStep 1959689 = 1469767) B1469767
theorem B17622845 : Blo 686314 17622845 := bstep (se 3 (by rfl) ⟨3304283, by rfl⟩ : syracuseStep 17622845 = 6608567) B6608567
theorem B7563091 : Blo 686314 7563091 := bstep (se 1 (by rfl) ⟨5672318, by rfl⟩ : syracuseStep 7563091 = 11344637) B11344637
theorem B2615273 : Blo 686314 2615273 := bstep (se 2 (by rfl) ⟨980727, by rfl⟩ : syracuseStep 2615273 = 1961455) B1961455
theorem B7858619 : Blo 686314 7858619 := bstep (se 1 (by rfl) ⟨5893964, by rfl⟩ : syracuseStep 7858619 = 11787929) B11787929
theorem B2321405 : Blo 686314 2321405 := bstep (se 3 (by rfl) ⟨435263, by rfl⟩ : syracuseStep 2321405 = 870527) B870527
theorem B2944147 : Blo 686314 2944147 := bstep (se 1 (by rfl) ⟨2208110, by rfl⟩ : syracuseStep 2944147 = 4416221) B4416221
theorem B3927305 : Blo 686314 3927305 := bstep (se 2 (by rfl) ⟨1472739, by rfl⟩ : syracuseStep 3927305 = 2945479) B2945479
theorem B3927487 : Blo 686314 3927487 := bstep (se 1 (by rfl) ⟨2945615, by rfl⟩ : syracuseStep 3927487 = 5891231) B5891231
theorem B2322809 : Blo 686314 2322809 := bstep (se 2 (by rfl) ⟨871053, by rfl⟩ : syracuseStep 2322809 = 1742107) B1742107
theorem B1962559 : Blo 686314 1962559 := bstep (se 1 (by rfl) ⟨1471919, by rfl⟩ : syracuseStep 1962559 = 2943839) B2943839
theorem B3928763 : Blo 686314 3928763 := bstep (se 1 (by rfl) ⟨2946572, by rfl⟩ : syracuseStep 3928763 = 5893145) B5893145
theorem B1307431 : Blo 686314 1307431 := bstep (se 1 (by rfl) ⟨980573, by rfl⟩ : syracuseStep 1307431 = 1961147) B1961147
theorem B980095 : Blo 686314 980095 := bstep (se 1 (by rfl) ⟨735071, by rfl⟩ : syracuseStep 980095 = 1470143) B1470143
theorem B2946779 : Blo 686314 2946779 := bstep (se 1 (by rfl) ⟨2210084, by rfl⟩ : syracuseStep 2946779 = 4420169) B4420169
theorem B77559761 : Blo 686314 77559761 := bstep (se 2 (by rfl) ⟨29084910, by rfl⟩ : syracuseStep 77559761 = 58169821) B58169821
theorem B5241023 : Blo 686314 5241023 := bstep (se 1 (by rfl) ⟨3930767, by rfl⟩ : syracuseStep 5241023 = 7861535) B7861535
theorem B18381005 : Blo 686314 18381005 := bstep (se 3 (by rfl) ⟨3446438, by rfl⟩ : syracuseStep 18381005 = 6892877) B6892877
theorem B686407 : Blo 686314 686407 := bstep (se 1 (by rfl) ⟨514805, by rfl⟩ : syracuseStep 686407 = 1029611) B1029611
theorem B1964371 : Blo 686314 1964371 := bstep (se 1 (by rfl) ⟨1473278, by rfl⟩ : syracuseStep 1964371 = 2946557) B2946557
theorem B686491 : Blo 686314 686491 := bstep (se 1 (by rfl) ⟨514868, by rfl⟩ : syracuseStep 686491 = 1029737) B1029737
theorem B7436717 : Blo 686314 7436717 := bstep (se 3 (by rfl) ⟨1394384, by rfl⟩ : syracuseStep 7436717 = 2788769) B2788769
theorem B21133871 : Blo 686314 21133871 := bstep (se 1 (by rfl) ⟨15850403, by rfl⟩ : syracuseStep 21133871 = 31700807) B31700807
theorem B686639 : Blo 686314 686639 := bstep (se 1 (by rfl) ⟨514979, by rfl⟩ : syracuseStep 686639 = 1029959) B1029959
theorem B686759 : Blo 686314 686759 := bstep (se 1 (by rfl) ⟨515069, by rfl⟩ : syracuseStep 686759 = 1030139) B1030139
theorem B686799 : Blo 686314 686799 := bstep (se 1 (by rfl) ⟨515099, by rfl⟩ : syracuseStep 686799 = 1030199) B1030199
theorem B686843 : Blo 686314 686843 := bstep (se 1 (by rfl) ⟨515132, by rfl⟩ : syracuseStep 686843 = 1030265) B1030265
theorem B686847 : Blo 686314 686847 := bstep (se 1 (by rfl) ⟨515135, by rfl⟩ : syracuseStep 686847 = 1030271) B1030271
theorem B686879 : Blo 686314 686879 := bstep (se 1 (by rfl) ⟨515159, by rfl⟩ : syracuseStep 686879 = 1030319) B1030319
theorem B687039 : Blo 686314 687039 := bstep (se 1 (by rfl) ⟨515279, by rfl⟩ : syracuseStep 687039 = 1030559) B1030559
theorem B2620907 : Blo 686314 2620907 := bstep (se 1 (by rfl) ⟨1965680, by rfl⟩ : syracuseStep 2620907 = 3931361) B3931361
theorem B4587005 : Blo 686314 4587005 := bstep (se 3 (by rfl) ⟨860063, by rfl⟩ : syracuseStep 4587005 = 1720127) B1720127
theorem B1310249 : Blo 686314 1310249 := bstep (se 2 (by rfl) ⟨491343, by rfl⟩ : syracuseStep 1310249 = 982687) B982687
theorem B687771 : Blo 686314 687771 := bstep (se 1 (by rfl) ⟨515828, by rfl⟩ : syracuseStep 687771 = 1031657) B1031657
theorem B688191 : Blo 686314 688191 := bstep (se 1 (by rfl) ⟨516143, by rfl⟩ : syracuseStep 688191 = 1032287) B1032287
theorem B133923131 : Blo 686314 133923131 := bstep (se 1 (by rfl) ⟨100442348, by rfl⟩ : syracuseStep 133923131 = 200884697) B200884697
theorem B4719077 : Blo 686314 4719077 := bstep (se 4 (by rfl) ⟨442413, by rfl⟩ : syracuseStep 4719077 = 884827) B884827
theorem B688799 : Blo 686314 688799 := bstep (se 1 (by rfl) ⟨516599, by rfl⟩ : syracuseStep 688799 = 1033199) B1033199
theorem B689055 : Blo 686314 689055 := bstep (se 1 (by rfl) ⟨516791, by rfl⟩ : syracuseStep 689055 = 1033583) B1033583
theorem B1737895 : Blo 686314 1737895 := bstep (se 1 (by rfl) ⟨1303421, by rfl⟩ : syracuseStep 1737895 = 2606843) B2606843
theorem B689479 : Blo 686314 689479 := bstep (se 1 (by rfl) ⟨517109, by rfl⟩ : syracuseStep 689479 = 1034219) B1034219
theorem B689647 : Blo 686314 689647 := bstep (se 1 (by rfl) ⟨517235, by rfl⟩ : syracuseStep 689647 = 1034471) B1034471
theorem B11766059 : Blo 686314 11766059 := bstep (se 1 (by rfl) ⟨8824544, by rfl⟩ : syracuseStep 11766059 = 17649089) B17649089
theorem B19892951 : Blo 686314 19892951 := bstep (se 1 (by rfl) ⟨14919713, by rfl⟩ : syracuseStep 19892951 = 29839427) B29839427
theorem B3477491 : Blo 686314 3477491 := bstep (se 1 (by rfl) ⟨2608118, by rfl⟩ : syracuseStep 3477491 = 5216237) B5216237
theorem B19796177 : Blo 686314 19796177 := bstep (se 2 (by rfl) ⟨7423566, by rfl⟩ : syracuseStep 19796177 = 14847133) B14847133
theorem B1741135 : Blo 686314 1741135 := bstep (se 1 (by rfl) ⟨1305851, by rfl⟩ : syracuseStep 1741135 = 2611703) B2611703
theorem B38245351 : Blo 686314 38245351 := bstep (se 1 (by rfl) ⟨28684013, by rfl⟩ : syracuseStep 38245351 = 57368027) B57368027
theorem B5215265 : Blo 686314 5215265 := bstep (se 2 (by rfl) ⟨1955724, by rfl⟩ : syracuseStep 5215265 = 3911449) B3911449
theorem B1741895 : Blo 686314 1741895 := bstep (se 1 (by rfl) ⟨1306421, by rfl⟩ : syracuseStep 1741895 = 2612843) B2612843
theorem B1743241 : Blo 686314 1743241 := bstep (se 2 (by rfl) ⟨653715, by rfl⟩ : syracuseStep 1743241 = 1307431) B1307431
theorem B1546667 : Blo 686314 1546667 := bstep (se 1 (by rfl) ⟨1160000, by rfl⟩ : syracuseStep 1546667 = 2320001) B2320001
theorem B11147807 : Blo 686314 11147807 := bstep (se 1 (by rfl) ⟨8360855, by rfl⟩ : syracuseStep 11147807 = 16721711) B16721711
theorem B2202241 : Blo 686314 2202241 := bstep (se 2 (by rfl) ⟨825840, by rfl⟩ : syracuseStep 2202241 = 1651681) B1651681
theorem B1743515 : Blo 686314 1743515 := bstep (se 1 (by rfl) ⟨1307636, by rfl⟩ : syracuseStep 1743515 = 2615273) B2615273
theorem B1547603 : Blo 686314 1547603 := bstep (se 1 (by rfl) ⟨1160702, by rfl⟩ : syracuseStep 1547603 = 2321405) B2321405
theorem B18817181 : Blo 686314 18817181 := bstep (se 3 (by rfl) ⟨3528221, by rfl⟩ : syracuseStep 18817181 = 7056443) B7056443
theorem B1548539 : Blo 686314 1548539 := bstep (se 1 (by rfl) ⟨1161404, by rfl⟩ : syracuseStep 1548539 = 2322809) B2322809
theorem B4957811 : Blo 686314 4957811 := bstep (se 1 (by rfl) ⟨3718358, by rfl⟩ : syracuseStep 4957811 = 7436717) B7436717
theorem B1747271 : Blo 686314 1747271 := bstep (se 1 (by rfl) ⟨1310453, by rfl⟩ : syracuseStep 1747271 = 2620907) B2620907
theorem B3058003 : Blo 686314 3058003 := bstep (se 1 (by rfl) ⟨2293502, by rfl⟩ : syracuseStep 3058003 = 4587005) B4587005
theorem B2206433 : Blo 686314 2206433 := bstep (se 2 (by rfl) ⟨827412, by rfl⟩ : syracuseStep 2206433 = 1654825) B1654825
theorem B3484457 : Blo 686314 3484457 := bstep (se 2 (by rfl) ⟨1306671, by rfl⟩ : syracuseStep 3484457 = 2613343) B2613343
theorem B1158887 : Blo 686314 1158887 := bstep (se 1 (by rfl) ⟨869165, by rfl⟩ : syracuseStep 1158887 = 1738331) B1738331
theorem B183873397 : Blo 686314 183873397 := bstep (se 5 (by rfl) ⟨8619065, by rfl⟩ : syracuseStep 183873397 = 17238131) B17238131
theorem B1159663 : Blo 686314 1159663 := bstep (se 1 (by rfl) ⟨869747, by rfl⟩ : syracuseStep 1159663 = 1739495) B1739495
theorem B1159771 : Blo 686314 1159771 := bstep (se 1 (by rfl) ⟨869828, by rfl⟩ : syracuseStep 1159771 = 1739657) B1739657
theorem B1160831 : Blo 686314 1160831 := bstep (se 1 (by rfl) ⟨870623, by rfl⟩ : syracuseStep 1160831 = 1741247) B1741247
theorem B8829161 : Blo 686314 8829161 := bstep (se 2 (by rfl) ⟨3310935, by rfl⟩ : syracuseStep 8829161 = 6621871) B6621871
theorem B1030427 : Blo 686314 1030427 := bstep (se 1 (by rfl) ⟨772820, by rfl⟩ : syracuseStep 1030427 = 1545641) B1545641
theorem B1161499 : Blo 686314 1161499 := bstep (se 1 (by rfl) ⟨871124, by rfl⟩ : syracuseStep 1161499 = 1742249) B1742249
theorem B1030463 : Blo 686314 1030463 := bstep (se 1 (by rfl) ⟨772847, by rfl⟩ : syracuseStep 1030463 = 1545695) B1545695
theorem B1161641 : Blo 686314 1161641 := bstep (se 2 (by rfl) ⟨435615, by rfl⟩ : syracuseStep 1161641 = 871231) B871231
theorem B1161695 : Blo 686314 1161695 := bstep (se 1 (by rfl) ⟨871271, by rfl⟩ : syracuseStep 1161695 = 1742543) B1742543
theorem B3488507 : Blo 686314 3488507 := bstep (se 1 (by rfl) ⟨2616380, by rfl⟩ : syracuseStep 3488507 = 5232761) B5232761
theorem B1031801 : Blo 686314 1031801 := bstep (se 2 (by rfl) ⟨386925, by rfl⟩ : syracuseStep 1031801 = 773851) B773851
theorem B2473703 : Blo 686314 2473703 := bstep (se 1 (by rfl) ⟨1855277, by rfl⟩ : syracuseStep 2473703 = 3710555) B3710555
theorem B1162991 : Blo 686314 1162991 := bstep (se 1 (by rfl) ⟨872243, by rfl⟩ : syracuseStep 1162991 = 1744487) B1744487
theorem B1032167 : Blo 686314 1032167 := bstep (se 1 (by rfl) ⟨774125, by rfl⟩ : syracuseStep 1032167 = 1548251) B1548251
theorem B1032239 : Blo 686314 1032239 := bstep (se 1 (by rfl) ⟨774179, by rfl⟩ : syracuseStep 1032239 = 1548359) B1548359
theorem B1032299 : Blo 686314 1032299 := bstep (se 1 (by rfl) ⟨774224, by rfl⟩ : syracuseStep 1032299 = 1548449) B1548449
theorem B1032347 : Blo 686314 1032347 := bstep (se 1 (by rfl) ⟨774260, by rfl⟩ : syracuseStep 1032347 = 1548521) B1548521
theorem B1163983 : Blo 686314 1163983 := bstep (se 1 (by rfl) ⟨872987, by rfl⟩ : syracuseStep 1163983 = 1745975) B1745975
theorem B11748563 : Blo 686314 11748563 := bstep (se 1 (by rfl) ⟨8811422, by rfl⟩ : syracuseStep 11748563 = 17622845) B17622845
theorem B1033679 : Blo 686314 1033679 := bstep (se 1 (by rfl) ⟨775259, by rfl⟩ : syracuseStep 1033679 = 1550519) B1550519
theorem B1033967 : Blo 686314 1033967 := bstep (se 1 (by rfl) ⟨775475, by rfl⟩ : syracuseStep 1033967 = 1550951) B1550951
theorem B1034153 : Blo 686314 1034153 := bstep (se 2 (by rfl) ⟨387807, by rfl⟩ : syracuseStep 1034153 = 775615) B775615
theorem B2476601 : Blo 686314 2476601 := bstep (se 2 (by rfl) ⟨928725, by rfl⟩ : syracuseStep 2476601 = 1857451) B1857451
theorem B1035035 : Blo 686314 1035035 := bstep (se 1 (by rfl) ⟨776276, by rfl⟩ : syracuseStep 1035035 = 1552553) B1552553
theorem B8834183 : Blo 686314 8834183 := bstep (se 1 (by rfl) ⟨6625637, by rfl⟩ : syracuseStep 8834183 = 13251275) B13251275
theorem B1035401 : Blo 686314 1035401 := bstep (se 2 (by rfl) ⟨388275, by rfl⟩ : syracuseStep 1035401 = 776551) B776551
theorem B4836521 : Blo 686314 4836521 := bstep (se 2 (by rfl) ⟨1813695, by rfl⟩ : syracuseStep 4836521 = 3627391) B3627391
theorem B1035455 : Blo 686314 1035455 := bstep (se 1 (by rfl) ⟨776591, by rfl⟩ : syracuseStep 1035455 = 1553183) B1553183
theorem B1101595 : Blo 686314 1101595 := bstep (se 1 (by rfl) ⟨826196, by rfl⟩ : syracuseStep 1101595 = 1652393) B1652393
theorem B3494015 : Blo 686314 3494015 := bstep (se 1 (by rfl) ⟨2620511, by rfl⟩ : syracuseStep 3494015 = 5241023) B5241023
theorem B11194523 : Blo 686314 11194523 := bstep (se 1 (by rfl) ⟨8395892, by rfl⟩ : syracuseStep 11194523 = 16791785) B16791785
theorem B1102825 : Blo 686314 1102825 := bstep (se 2 (by rfl) ⟨413559, by rfl⟩ : syracuseStep 1102825 = 827119) B827119
theorem B873499 : Blo 686314 873499 := bstep (se 1 (by rfl) ⟨655124, by rfl⟩ : syracuseStep 873499 = 1310249) B1310249
theorem B775399 : Blo 686314 775399 := bstep (se 1 (by rfl) ⟨581549, by rfl⟩ : syracuseStep 775399 = 1163099) B1163099
theorem B3725623 : Blo 686314 3725623 := bstep (se 1 (by rfl) ⟨2794217, by rfl⟩ : syracuseStep 3725623 = 5588435) B5588435
theorem B3529207 : Blo 686314 3529207 := bstep (se 1 (by rfl) ⟨2646905, by rfl⟩ : syracuseStep 3529207 = 5293811) B5293811
theorem B2316815 : Blo 686314 2316815 := bstep (se 1 (by rfl) ⟨1737611, by rfl⟩ : syracuseStep 2316815 = 3475223) B3475223
theorem B2317625 : Blo 686314 2317625 := bstep (se 2 (by rfl) ⟨869109, by rfl⟩ : syracuseStep 2317625 = 1738219) B1738219
theorem B10084121 : Blo 686314 10084121 := bstep (se 2 (by rfl) ⟨3781545, by rfl⟩ : syracuseStep 10084121 = 7563091) B7563091
theorem B33972311 : Blo 686314 33972311 := bstep (se 1 (by rfl) ⟨25479233, by rfl⟩ : syracuseStep 33972311 = 50958467) B50958467
theorem B2319353 : Blo 686314 2319353 := bstep (se 2 (by rfl) ⟨869757, by rfl⟩ : syracuseStep 2319353 = 1739515) B1739515
theorem B2319407 : Blo 686314 2319407 := bstep (se 1 (by rfl) ⟨1739555, by rfl⟩ : syracuseStep 2319407 = 3479111) B3479111
theorem B2319515 : Blo 686314 2319515 := bstep (se 1 (by rfl) ⟨1739636, by rfl⟩ : syracuseStep 2319515 = 3479273) B3479273
theorem B3925529 : Blo 686314 3925529 := bstep (se 2 (by rfl) ⟨1472073, by rfl⟩ : syracuseStep 3925529 = 2944147) B2944147
theorem B2516807 : Blo 686314 2516807 := bstep (se 1 (by rfl) ⟨1887605, by rfl⟩ : syracuseStep 2516807 = 3775211) B3775211
theorem B2320271 : Blo 686314 2320271 := bstep (se 1 (by rfl) ⟨1740203, by rfl⟩ : syracuseStep 2320271 = 3480407) B3480407
theorem B5236649 : Blo 686314 5236649 := bstep (se 2 (by rfl) ⟨1963743, by rfl⟩ : syracuseStep 5236649 = 3927487) B3927487
theorem B2320379 : Blo 686314 2320379 := bstep (se 1 (by rfl) ⟨1740284, by rfl⟩ : syracuseStep 2320379 = 3480569) B3480569
theorem B1763455 : Blo 686314 1763455 := bstep (se 1 (by rfl) ⟨1322591, by rfl⟩ : syracuseStep 1763455 = 2645183) B2645183
theorem B1304903 : Blo 686314 1304903 := bstep (se 1 (by rfl) ⟨978677, by rfl⟩ : syracuseStep 1304903 = 1957355) B1957355
theorem B2484587 : Blo 686314 2484587 := bstep (se 1 (by rfl) ⟨1863440, by rfl⟩ : syracuseStep 2484587 = 3726881) B3726881
theorem B1862077 : Blo 686314 1862077 := bstep (se 3 (by rfl) ⟨349139, by rfl⟩ : syracuseStep 1862077 = 698279) B698279
theorem B4188991 : Blo 686314 4188991 := bstep (se 1 (by rfl) ⟨3141743, by rfl⟩ : syracuseStep 4188991 = 6283487) B6283487
theorem B1960919 : Blo 686314 1960919 := bstep (se 1 (by rfl) ⟨1470689, by rfl⟩ : syracuseStep 1960919 = 2941379) B2941379
theorem B3304439 : Blo 686314 3304439 := bstep (se 1 (by rfl) ⟨2478329, by rfl⟩ : syracuseStep 3304439 = 4956659) B4956659
theorem B7826543 : Blo 686314 7826543 := bstep (se 1 (by rfl) ⟨5869907, by rfl⟩ : syracuseStep 7826543 = 11739815) B11739815
theorem B26864759 : Blo 686314 26864759 := bstep (se 1 (by rfl) ⟨20148569, by rfl⟩ : syracuseStep 26864759 = 40297139) B40297139
theorem B5238107 : Blo 686314 5238107 := bstep (se 1 (by rfl) ⟨3928580, by rfl⟩ : syracuseStep 5238107 = 7857161) B7857161
theorem B2616745 : Blo 686314 2616745 := bstep (se 2 (by rfl) ⟨981279, by rfl⟩ : syracuseStep 2616745 = 1962559) B1962559
theorem B2321999 : Blo 686314 2321999 := bstep (se 1 (by rfl) ⟨1741499, by rfl⟩ : syracuseStep 2321999 = 3482999) B3482999
theorem B1306459 : Blo 686314 1306459 := bstep (se 1 (by rfl) ⟨979844, by rfl⟩ : syracuseStep 1306459 = 1959689) B1959689
theorem B1306793 : Blo 686314 1306793 := bstep (se 2 (by rfl) ⟨490047, by rfl⟩ : syracuseStep 1306793 = 980095) B980095
theorem B112783589 : Blo 686314 112783589 := bstep (se 4 (by rfl) ⟨10573461, by rfl⟩ : syracuseStep 112783589 = 21146923) B21146923
theorem B5239079 : Blo 686314 5239079 := bstep (se 1 (by rfl) ⟨3929309, by rfl⟩ : syracuseStep 5239079 = 7858619) B7858619
theorem B2618203 : Blo 686314 2618203 := bstep (se 1 (by rfl) ⟨1963652, by rfl⟩ : syracuseStep 2618203 = 3927305) B3927305
theorem B2323943 : Blo 686314 2323943 := bstep (se 1 (by rfl) ⟨1742957, by rfl⟩ : syracuseStep 2323943 = 3485915) B3485915
theorem B2619161 : Blo 686314 2619161 := bstep (se 2 (by rfl) ⟨982185, by rfl⟩ : syracuseStep 2619161 = 1964371) B1964371
theorem B2619175 : Blo 686314 2619175 := bstep (se 1 (by rfl) ⟨1964381, by rfl⟩ : syracuseStep 2619175 = 3928763) B3928763
theorem B686319 : Blo 686314 686319 := bstep (se 1 (by rfl) ⟨514739, by rfl⟩ : syracuseStep 686319 = 1029479) B1029479
theorem B2947529 : Blo 686314 2947529 := bstep (se 2 (by rfl) ⟨1105323, by rfl⟩ : syracuseStep 2947529 = 2210647) B2210647
theorem B1964519 : Blo 686314 1964519 := bstep (se 1 (by rfl) ⟨1473389, by rfl⟩ : syracuseStep 1964519 = 2946779) B2946779
theorem B51706507 : Blo 686314 51706507 := bstep (se 1 (by rfl) ⟨38779880, by rfl⟩ : syracuseStep 51706507 = 77559761) B77559761
theorem B12254003 : Blo 686314 12254003 := bstep (se 1 (by rfl) ⟨9190502, by rfl⟩ : syracuseStep 12254003 = 18381005) B18381005
theorem B687099 : Blo 686314 687099 := bstep (se 1 (by rfl) ⟨515324, by rfl⟩ : syracuseStep 687099 = 1030649) B1030649
theorem B14089247 : Blo 686314 14089247 := bstep (se 1 (by rfl) ⟨10566935, by rfl⟩ : syracuseStep 14089247 = 21133871) B21133871
theorem B687343 : Blo 686314 687343 := bstep (se 1 (by rfl) ⟨515507, by rfl⟩ : syracuseStep 687343 = 1031015) B1031015
theorem B2325833 : Blo 686314 2325833 := bstep (se 2 (by rfl) ⟨872187, by rfl⟩ : syracuseStep 2325833 = 1744375) B1744375
theorem B687463 : Blo 686314 687463 := bstep (se 1 (by rfl) ⟨515597, by rfl⟩ : syracuseStep 687463 = 1031195) B1031195
theorem B5864987 : Blo 686314 5864987 := bstep (se 1 (by rfl) ⟨4398740, by rfl⟩ : syracuseStep 5864987 = 8797481) B8797481
theorem B687775 : Blo 686314 687775 := bstep (se 1 (by rfl) ⟨515831, by rfl⟩ : syracuseStep 687775 = 1031663) B1031663
theorem B2784991 : Blo 686314 2784991 := bstep (se 1 (by rfl) ⟨2088743, by rfl⟩ : syracuseStep 2784991 = 4177487) B4177487
theorem B688031 : Blo 686314 688031 := bstep (se 1 (by rfl) ⟨516023, by rfl⟩ : syracuseStep 688031 = 1032047) B1032047
theorem B688159 : Blo 686314 688159 := bstep (se 1 (by rfl) ⟨516119, by rfl⟩ : syracuseStep 688159 = 1032239) B1032239
theorem B688199 : Blo 686314 688199 := bstep (se 1 (by rfl) ⟨516149, by rfl⟩ : syracuseStep 688199 = 1032299) B1032299
theorem B688231 : Blo 686314 688231 := bstep (se 1 (by rfl) ⟨516173, by rfl⟩ : syracuseStep 688231 = 1032347) B1032347
theorem B3146051 : Blo 686314 3146051 := bstep (se 1 (by rfl) ⟨2359538, by rfl⟩ : syracuseStep 3146051 = 4719077) B4719077
theorem B7832375 : Blo 686314 7832375 := bstep (se 1 (by rfl) ⟨5874281, by rfl⟩ : syracuseStep 7832375 = 11748563) B11748563
theorem B689119 : Blo 686314 689119 := bstep (se 1 (by rfl) ⟨516839, by rfl⟩ : syracuseStep 689119 = 1033679) B1033679
theorem B689311 : Blo 686314 689311 := bstep (se 1 (by rfl) ⟨516983, by rfl⟩ : syracuseStep 689311 = 1033967) B1033967
theorem B689435 : Blo 686314 689435 := bstep (se 1 (by rfl) ⟨517076, by rfl⟩ : syracuseStep 689435 = 1034153) B1034153
theorem B690023 : Blo 686314 690023 := bstep (se 1 (by rfl) ⟨517517, by rfl⟩ : syracuseStep 690023 = 1035035) B1035035
theorem B690267 : Blo 686314 690267 := bstep (se 1 (by rfl) ⟨517700, by rfl⟩ : syracuseStep 690267 = 1035401) B1035401
theorem B690303 : Blo 686314 690303 := bstep (se 1 (by rfl) ⟨517727, by rfl⟩ : syracuseStep 690303 = 1035455) B1035455
theorem B2329343 : Blo 686314 2329343 := bstep (se 1 (by rfl) ⟨1747007, by rfl⟩ : syracuseStep 2329343 = 3494015) B3494015
theorem B3476843 : Blo 686314 3476843 := bstep (se 1 (by rfl) ⟨2607632, by rfl⟩ : syracuseStep 3476843 = 5215265) B5215265
theorem B1544543 : Blo 686314 1544543 := bstep (se 1 (by rfl) ⟨1158407, by rfl⟩ : syracuseStep 1544543 = 2316815) B2316815
theorem B1545083 : Blo 686314 1545083 := bstep (se 1 (by rfl) ⟨1158812, by rfl⟩ : syracuseStep 1545083 = 2317625) B2317625
theorem B1741945 : Blo 686314 1741945 := bstep (se 2 (by rfl) ⟨653229, by rfl⟩ : syracuseStep 1741945 = 1306459) B1306459
theorem B6722747 : Blo 686314 6722747 := bstep (se 1 (by rfl) ⟨5042060, by rfl⟩ : syracuseStep 6722747 = 10084121) B10084121
theorem B22648207 : Blo 686314 22648207 := bstep (se 1 (by rfl) ⟨16986155, by rfl⟩ : syracuseStep 22648207 = 33972311) B33972311
theorem B1546217 : Blo 686314 1546217 := bstep (se 2 (by rfl) ⟨579831, by rfl⟩ : syracuseStep 1546217 = 1159663) B1159663
theorem B1546235 : Blo 686314 1546235 := bstep (se 1 (by rfl) ⟨1159676, by rfl⟩ : syracuseStep 1546235 = 2319353) B2319353
theorem B1546271 : Blo 686314 1546271 := bstep (se 1 (by rfl) ⟨1159703, by rfl⟩ : syracuseStep 1546271 = 2319407) B2319407
theorem B1546343 : Blo 686314 1546343 := bstep (se 1 (by rfl) ⟨1159757, by rfl⟩ : syracuseStep 1546343 = 2319515) B2319515
theorem B1546361 : Blo 686314 1546361 := bstep (se 2 (by rfl) ⟨579885, by rfl⟩ : syracuseStep 1546361 = 1159771) B1159771
theorem B1677871 : Blo 686314 1677871 := bstep (se 1 (by rfl) ⟨1258403, by rfl⟩ : syracuseStep 1677871 = 2516807) B2516807
theorem B1546847 : Blo 686314 1546847 := bstep (se 1 (by rfl) ⟨1160135, by rfl⟩ : syracuseStep 1546847 = 2320271) B2320271
theorem B50993801 : Blo 686314 50993801 := bstep (se 2 (by rfl) ⟨19122675, by rfl⟩ : syracuseStep 50993801 = 38245351) B38245351
theorem B1546919 : Blo 686314 1546919 := bstep (se 1 (by rfl) ⟨1160189, by rfl⟩ : syracuseStep 1546919 = 2320379) B2320379
theorem B2202959 : Blo 686314 2202959 := bstep (se 1 (by rfl) ⟨1652219, by rfl⟩ : syracuseStep 2202959 = 3304439) B3304439
theorem B5217695 : Blo 686314 5217695 := bstep (se 1 (by rfl) ⟨3913271, by rfl⟩ : syracuseStep 5217695 = 7826543) B7826543
theorem B1547999 : Blo 686314 1547999 := bstep (se 1 (by rfl) ⟨1160999, by rfl⟩ : syracuseStep 1547999 = 2321999) B2321999
theorem B1548665 : Blo 686314 1548665 := bstep (se 2 (by rfl) ⟨580749, by rfl⟩ : syracuseStep 1548665 = 1161499) B1161499
theorem B1549295 : Blo 686314 1549295 := bstep (se 1 (by rfl) ⟨1161971, by rfl⟩ : syracuseStep 1549295 = 2323943) B2323943
theorem B1746107 : Blo 686314 1746107 := bstep (se 1 (by rfl) ⟨1309580, by rfl⟩ : syracuseStep 1746107 = 2619161) B2619161
theorem B8169335 : Blo 686314 8169335 := bstep (se 1 (by rfl) ⟨6127001, by rfl⟩ : syracuseStep 8169335 = 12254003) B12254003
theorem B1550555 : Blo 686314 1550555 := bstep (se 1 (by rfl) ⟨1162916, by rfl⟩ : syracuseStep 1550555 = 2325833) B2325833
theorem B3713321 : Blo 686314 3713321 := bstep (se 2 (by rfl) ⟨1392495, by rfl⟩ : syracuseStep 3713321 = 2784991) B2784991
theorem B3909991 : Blo 686314 3909991 := bstep (se 1 (by rfl) ⟨2932493, by rfl⟩ : syracuseStep 3909991 = 5864987) B5864987
theorem B1649135 : Blo 686314 1649135 := bstep (se 1 (by rfl) ⟨1236851, by rfl⟩ : syracuseStep 1649135 = 2473703) B2473703
theorem B3484781 : Blo 686314 3484781 := bstep (se 3 (by rfl) ⟨653396, by rfl⟩ : syracuseStep 3484781 = 1306793) B1306793
theorem B1551977 : Blo 686314 1551977 := bstep (se 2 (by rfl) ⟨581991, by rfl⟩ : syracuseStep 1551977 = 1163983) B1163983
theorem B7844039 : Blo 686314 7844039 := bstep (se 1 (by rfl) ⟨5883029, by rfl⟩ : syracuseStep 7844039 = 11766059) B11766059
theorem B1651067 : Blo 686314 1651067 := bstep (se 1 (by rfl) ⟨1238300, by rfl⟩ : syracuseStep 1651067 = 2476601) B2476601
theorem B1161263 : Blo 686314 1161263 := bstep (se 1 (by rfl) ⟨870947, by rfl⟩ : syracuseStep 1161263 = 1741895) B1741895
theorem B5585321 : Blo 686314 5585321 := bstep (se 2 (by rfl) ⟨2094495, by rfl⟩ : syracuseStep 5585321 = 4188991) B4188991
theorem B1031111 : Blo 686314 1031111 := bstep (se 1 (by rfl) ⟨773333, by rfl⟩ : syracuseStep 1031111 = 1546667) B1546667
theorem B1162343 : Blo 686314 1162343 := bstep (se 1 (by rfl) ⟨871757, by rfl⟩ : syracuseStep 1162343 = 1743515) B1743515
theorem B3488993 : Blo 686314 3488993 := bstep (se 2 (by rfl) ⟨1308372, by rfl⟩ : syracuseStep 3488993 = 2616745) B2616745
theorem B1031735 : Blo 686314 1031735 := bstep (se 1 (by rfl) ⟨773801, by rfl⟩ : syracuseStep 1031735 = 1547603) B1547603
theorem B5881733 : Blo 686314 5881733 := bstep (se 4 (by rfl) ⟨551412, by rfl⟩ : syracuseStep 5881733 = 1102825) B1102825
theorem B1032359 : Blo 686314 1032359 := bstep (se 1 (by rfl) ⟨774269, by rfl⟩ : syracuseStep 1032359 = 1548539) B1548539
theorem B3490937 : Blo 686314 3490937 := bstep (se 2 (by rfl) ⟨1309101, by rfl⟩ : syracuseStep 3490937 = 2618203) B2618203
theorem B3491099 : Blo 686314 3491099 := bstep (se 1 (by rfl) ⟨2618324, by rfl⟩ : syracuseStep 3491099 = 5236649) B5236649
theorem B1164665 : Blo 686314 1164665 := bstep (se 2 (by rfl) ⟨436749, by rfl⟩ : syracuseStep 1164665 = 873499) B873499
theorem B869935 : Blo 686314 869935 := bstep (se 1 (by rfl) ⟨652451, by rfl⟩ : syracuseStep 869935 = 1304903) B1304903
theorem B1164847 : Blo 686314 1164847 := bstep (se 1 (by rfl) ⟨873635, by rfl⟩ : syracuseStep 1164847 = 1747271) B1747271
theorem B1656391 : Blo 686314 1656391 := bstep (se 1 (by rfl) ⟨1242293, by rfl⟩ : syracuseStep 1656391 = 2484587) B2484587
theorem B1033865 : Blo 686314 1033865 := bstep (se 2 (by rfl) ⟨387699, by rfl⟩ : syracuseStep 1033865 = 775399) B775399
theorem B17909839 : Blo 686314 17909839 := bstep (se 1 (by rfl) ⟨13432379, by rfl⟩ : syracuseStep 17909839 = 26864759) B26864759
theorem B3492071 : Blo 686314 3492071 := bstep (se 1 (by rfl) ⟨2619053, by rfl⟩ : syracuseStep 3492071 = 5238107) B5238107
theorem B3492233 : Blo 686314 3492233 := bstep (se 2 (by rfl) ⟨1309587, by rfl⟩ : syracuseStep 3492233 = 2619175) B2619175
theorem B772591 : Blo 686314 772591 := bstep (se 1 (by rfl) ⟨579443, by rfl⟩ : syracuseStep 772591 = 1158887) B1158887
theorem B75189059 : Blo 686314 75189059 := bstep (se 1 (by rfl) ⟨56391794, by rfl⟩ : syracuseStep 75189059 = 112783589) B112783589
theorem B3492719 : Blo 686314 3492719 := bstep (se 1 (by rfl) ⟨2619539, by rfl⟩ : syracuseStep 3492719 = 5239079) B5239079
theorem B4967497 : Blo 686314 4967497 := bstep (se 2 (by rfl) ⟨1862811, by rfl⟩ : syracuseStep 4967497 = 3725623) B3725623
theorem B12897389 : Blo 686314 12897389 := bstep (se 3 (by rfl) ⟨2418260, by rfl⟩ : syracuseStep 12897389 = 4836521) B4836521
theorem B4705609 : Blo 686314 4705609 := bstep (se 2 (by rfl) ⟨1764603, by rfl⟩ : syracuseStep 4705609 = 3529207) B3529207
theorem B2936321 : Blo 686314 2936321 := bstep (se 2 (by rfl) ⟨1101120, by rfl⟩ : syracuseStep 2936321 = 2202241) B2202241
theorem B773887 : Blo 686314 773887 := bstep (se 1 (by rfl) ⟨580415, by rfl⟩ : syracuseStep 773887 = 1160831) B1160831
theorem B5886107 : Blo 686314 5886107 := bstep (se 1 (by rfl) ⟨4414580, by rfl⟩ : syracuseStep 5886107 = 8829161) B8829161
theorem B774427 : Blo 686314 774427 := bstep (se 1 (by rfl) ⟨580820, by rfl⟩ : syracuseStep 774427 = 1161641) B1161641
theorem B774463 : Blo 686314 774463 := bstep (se 1 (by rfl) ⟨580847, by rfl⟩ : syracuseStep 774463 = 1161695) B1161695
theorem B9392831 : Blo 686314 9392831 := bstep (se 1 (by rfl) ⟨7044623, by rfl⟩ : syracuseStep 9392831 = 14089247) B14089247
theorem B775327 : Blo 686314 775327 := bstep (se 1 (by rfl) ⟨581495, by rfl⟩ : syracuseStep 775327 = 1162991) B1162991
theorem B89282087 : Blo 686314 89282087 := bstep (se 1 (by rfl) ⟨66961565, by rfl⟩ : syracuseStep 89282087 = 133923131) B133923131
theorem B2317193 : Blo 686314 2317193 := bstep (se 2 (by rfl) ⟨868947, by rfl⟩ : syracuseStep 2317193 = 1737895) B1737895
theorem B16309349 : Blo 686314 16309349 := bstep (se 4 (by rfl) ⟨1529001, by rfl⟩ : syracuseStep 16309349 = 3058003) B3058003
theorem B13261967 : Blo 686314 13261967 := bstep (se 1 (by rfl) ⟨9946475, by rfl⟩ : syracuseStep 13261967 = 19892951) B19892951
theorem B5889455 : Blo 686314 5889455 := bstep (se 1 (by rfl) ⟨4417091, by rfl⟩ : syracuseStep 5889455 = 8834183) B8834183
theorem B2318327 : Blo 686314 2318327 := bstep (se 1 (by rfl) ⟨1738745, by rfl⟩ : syracuseStep 2318327 = 3477491) B3477491
theorem B7463015 : Blo 686314 7463015 := bstep (se 1 (by rfl) ⟨5597261, by rfl⟩ : syracuseStep 7463015 = 11194523) B11194523
theorem B13197451 : Blo 686314 13197451 := bstep (se 1 (by rfl) ⟨9898088, by rfl⟩ : syracuseStep 13197451 = 19796177) B19796177
theorem B2351273 : Blo 686314 2351273 := bstep (se 2 (by rfl) ⟨881727, by rfl⟩ : syracuseStep 2351273 = 1763455) B1763455
theorem B2482769 : Blo 686314 2482769 := bstep (se 2 (by rfl) ⟨931038, by rfl⟩ : syracuseStep 2482769 = 1862077) B1862077
theorem B7431871 : Blo 686314 7431871 := bstep (se 1 (by rfl) ⟨5573903, by rfl⟩ : syracuseStep 7431871 = 11147807) B11147807
theorem B1468793 : Blo 686314 1468793 := bstep (se 2 (by rfl) ⟨550797, by rfl⟩ : syracuseStep 1468793 = 1101595) B1101595
theorem B245164529 : Blo 686314 245164529 := bstep (se 2 (by rfl) ⟨91936698, by rfl⟩ : syracuseStep 245164529 = 183873397) B183873397
theorem B12544787 : Blo 686314 12544787 := bstep (se 1 (by rfl) ⟨9408590, by rfl⟩ : syracuseStep 12544787 = 18817181) B18817181
theorem B2321513 : Blo 686314 2321513 := bstep (se 2 (by rfl) ⟨870567, by rfl⟩ : syracuseStep 2321513 = 1741135) B1741135
theorem B2617019 : Blo 686314 2617019 := bstep (se 1 (by rfl) ⟨1962764, by rfl⟩ : syracuseStep 2617019 = 3925529) B3925529
theorem B3305207 : Blo 686314 3305207 := bstep (se 1 (by rfl) ⟨2478905, by rfl⟩ : syracuseStep 3305207 = 4957811) B4957811
theorem B7860077 : Blo 686314 7860077 := bstep (se 3 (by rfl) ⟨1473764, by rfl⟩ : syracuseStep 7860077 = 2947529) B2947529
theorem B1470955 : Blo 686314 1470955 := bstep (se 1 (by rfl) ⟨1103216, by rfl⟩ : syracuseStep 1470955 = 2206433) B2206433
theorem B2322971 : Blo 686314 2322971 := bstep (se 1 (by rfl) ⟨1742228, by rfl⟩ : syracuseStep 2322971 = 3484457) B3484457
theorem B1307279 : Blo 686314 1307279 := bstep (se 1 (by rfl) ⟨980459, by rfl⟩ : syracuseStep 1307279 = 1960919) B1960919
theorem B2324321 : Blo 686314 2324321 := bstep (se 2 (by rfl) ⟨871620, by rfl⟩ : syracuseStep 2324321 = 1743241) B1743241
theorem B68942009 : Blo 686314 68942009 := bstep (se 2 (by rfl) ⟨25853253, by rfl⟩ : syracuseStep 68942009 = 51706507) B51706507
theorem B686951 : Blo 686314 686951 := bstep (se 1 (by rfl) ⟨515213, by rfl⟩ : syracuseStep 686951 = 1030427) B1030427
theorem B686975 : Blo 686314 686975 := bstep (se 1 (by rfl) ⟨515231, by rfl⟩ : syracuseStep 686975 = 1030463) B1030463
theorem B1309679 : Blo 686314 1309679 := bstep (se 1 (by rfl) ⟨982259, by rfl⟩ : syracuseStep 1309679 = 1964519) B1964519
theorem B2325671 : Blo 686314 2325671 := bstep (se 1 (by rfl) ⟨1744253, by rfl⟩ : syracuseStep 2325671 = 3488507) B3488507
theorem B687867 : Blo 686314 687867 := bstep (se 1 (by rfl) ⟨515900, by rfl⟩ : syracuseStep 687867 = 1031801) B1031801
theorem B688111 : Blo 686314 688111 := bstep (se 1 (by rfl) ⟨516083, by rfl⟩ : syracuseStep 688111 = 1032167) B1032167
theorem B688239 : Blo 686314 688239 := bstep (se 1 (by rfl) ⟨516179, by rfl⟩ : syracuseStep 688239 = 1032359) B1032359
theorem B17596601 : Blo 686314 17596601 := bstep (se 2 (by rfl) ⟨6598725, by rfl⟩ : syracuseStep 17596601 = 13197451) B13197451
theorem B2327291 : Blo 686314 2327291 := bstep (se 1 (by rfl) ⟨1745468, by rfl⟩ : syracuseStep 2327291 = 3490937) B3490937
theorem B8389469 : Blo 686314 8389469 := bstep (se 3 (by rfl) ⟨1573025, by rfl⟩ : syracuseStep 8389469 = 3146051) B3146051
theorem B2327399 : Blo 686314 2327399 := bstep (se 1 (by rfl) ⟨1745549, by rfl⟩ : syracuseStep 2327399 = 3491099) B3491099
theorem B689243 : Blo 686314 689243 := bstep (se 1 (by rfl) ⟨516932, by rfl⟩ : syracuseStep 689243 = 1033865) B1033865
theorem B2328047 : Blo 686314 2328047 := bstep (se 1 (by rfl) ⟨1746035, by rfl⟩ : syracuseStep 2328047 = 3492071) B3492071
theorem B6620717 : Blo 686314 6620717 := bstep (se 3 (by rfl) ⟨1241384, by rfl⟩ : syracuseStep 6620717 = 2482769) B2482769
theorem B2328155 : Blo 686314 2328155 := bstep (se 1 (by rfl) ⟨1746116, by rfl⟩ : syracuseStep 2328155 = 3492233) B3492233
theorem B2328479 : Blo 686314 2328479 := bstep (se 1 (by rfl) ⟨1746359, by rfl⟩ : syracuseStep 2328479 = 3492719) B3492719
theorem B6261887 : Blo 686314 6261887 := bstep (se 1 (by rfl) ⟨4696415, by rfl⟩ : syracuseStep 6261887 = 9392831) B9392831
theorem B5213321 : Blo 686314 5213321 := bstep (se 2 (by rfl) ⟨1954995, by rfl⟩ : syracuseStep 5213321 = 3909991) B3909991
theorem B1544795 : Blo 686314 1544795 := bstep (se 1 (by rfl) ⟨1158596, by rfl⟩ : syracuseStep 1544795 = 2317193) B2317193
theorem B3478463 : Blo 686314 3478463 := bstep (se 1 (by rfl) ⟨2608847, by rfl⟩ : syracuseStep 3478463 = 5217695) B5217695
theorem B1545551 : Blo 686314 1545551 := bstep (se 1 (by rfl) ⟨1159163, by rfl⟩ : syracuseStep 1545551 = 2318327) B2318327
theorem B9902189 : Blo 686314 9902189 := bstep (se 3 (by rfl) ⟨1856660, by rfl⟩ : syracuseStep 9902189 = 3713321) B3713321
theorem B5446223 : Blo 686314 5446223 := bstep (se 1 (by rfl) ⟨4084667, by rfl⟩ : syracuseStep 5446223 = 8169335) B8169335
theorem B8363191 : Blo 686314 8363191 := bstep (se 1 (by rfl) ⟨6272393, by rfl⟩ : syracuseStep 8363191 = 12544787) B12544787
theorem B1547675 : Blo 686314 1547675 := bstep (se 1 (by rfl) ⟨1160756, by rfl⟩ : syracuseStep 1547675 = 2321513) B2321513
theorem B1744679 : Blo 686314 1744679 := bstep (se 1 (by rfl) ⟨1308509, by rfl⟩ : syracuseStep 1744679 = 2617019) B2617019
theorem B2203471 : Blo 686314 2203471 := bstep (se 1 (by rfl) ⟨1652603, by rfl⟩ : syracuseStep 2203471 = 3305207) B3305207
theorem B1548647 : Blo 686314 1548647 := bstep (se 1 (by rfl) ⟨1161485, by rfl⟩ : syracuseStep 1548647 = 2322971) B2322971
theorem B2237161 : Blo 686314 2237161 := bstep (se 2 (by rfl) ⟨838935, by rfl⟩ : syracuseStep 2237161 = 1677871) B1677871
theorem B1549547 : Blo 686314 1549547 := bstep (se 1 (by rfl) ⟨1162160, by rfl⟩ : syracuseStep 1549547 = 2324321) B2324321
theorem B1550447 : Blo 686314 1550447 := bstep (se 1 (by rfl) ⟨1162835, by rfl⟩ : syracuseStep 1550447 = 2325671) B2325671
theorem B6270061 : Blo 686314 6270061 := bstep (se 3 (by rfl) ⟨1175636, by rfl⟩ : syracuseStep 6270061 = 2351273) B2351273
theorem B5221583 : Blo 686314 5221583 := bstep (se 1 (by rfl) ⟨3916187, by rfl⟩ : syracuseStep 5221583 = 7832375) B7832375
theorem B3486077 : Blo 686314 3486077 := bstep (se 3 (by rfl) ⟨653639, by rfl⟩ : syracuseStep 3486077 = 1307279) B1307279
theorem B1552895 : Blo 686314 1552895 := bstep (se 1 (by rfl) ⟨1164671, by rfl⟩ : syracuseStep 1552895 = 2329343) B2329343
theorem B1159913 : Blo 686314 1159913 := bstep (se 2 (by rfl) ⟨434967, by rfl⟩ : syracuseStep 1159913 = 869935) B869935
theorem B1553129 : Blo 686314 1553129 := bstep (se 2 (by rfl) ⟨582423, by rfl⟩ : syracuseStep 1553129 = 1164847) B1164847
theorem B8598259 : Blo 686314 8598259 := bstep (se 1 (by rfl) ⟨6448694, by rfl⟩ : syracuseStep 8598259 = 12897389) B12897389
theorem B2208521 : Blo 686314 2208521 := bstep (se 2 (by rfl) ⟨828195, by rfl⟩ : syracuseStep 2208521 = 1656391) B1656391
theorem B9909161 : Blo 686314 9909161 := bstep (se 2 (by rfl) ⟨3715935, by rfl⟩ : syracuseStep 9909161 = 7431871) B7431871
theorem B1029695 : Blo 686314 1029695 := bstep (se 1 (by rfl) ⟨772271, by rfl⟩ : syracuseStep 1029695 = 1544543) B1544543
theorem B1030055 : Blo 686314 1030055 := bstep (se 1 (by rfl) ⟨772541, by rfl⟩ : syracuseStep 1030055 = 1545083) B1545083
theorem B1030121 : Blo 686314 1030121 := bstep (se 2 (by rfl) ⟨386295, by rfl⟩ : syracuseStep 1030121 = 772591) B772591
theorem B59521391 : Blo 686314 59521391 := bstep (se 1 (by rfl) ⟨44641043, by rfl⟩ : syracuseStep 59521391 = 89282087) B89282087
theorem B1030811 : Blo 686314 1030811 := bstep (se 1 (by rfl) ⟨773108, by rfl⟩ : syracuseStep 1030811 = 1546217) B1546217
theorem B1030823 : Blo 686314 1030823 := bstep (se 1 (by rfl) ⟨773117, by rfl⟩ : syracuseStep 1030823 = 1546235) B1546235
theorem B1030847 : Blo 686314 1030847 := bstep (se 1 (by rfl) ⟨773135, by rfl⟩ : syracuseStep 1030847 = 1546271) B1546271
theorem B1030895 : Blo 686314 1030895 := bstep (se 1 (by rfl) ⟨773171, by rfl⟩ : syracuseStep 1030895 = 1546343) B1546343
theorem B1030907 : Blo 686314 1030907 := bstep (se 1 (by rfl) ⟨773180, by rfl⟩ : syracuseStep 1030907 = 1546361) B1546361
theorem B1031231 : Blo 686314 1031231 := bstep (se 1 (by rfl) ⟨773423, by rfl⟩ : syracuseStep 1031231 = 1546847) B1546847
theorem B33995867 : Blo 686314 33995867 := bstep (se 1 (by rfl) ⟨25496900, by rfl⟩ : syracuseStep 33995867 = 50993801) B50993801
theorem B6274145 : Blo 686314 6274145 := bstep (se 2 (by rfl) ⟨2352804, by rfl⟩ : syracuseStep 6274145 = 4705609) B4705609
theorem B1031279 : Blo 686314 1031279 := bstep (se 1 (by rfl) ⟨773459, by rfl⟩ : syracuseStep 1031279 = 1546919) B1546919
theorem B1031849 : Blo 686314 1031849 := bstep (se 2 (by rfl) ⟨386943, by rfl⟩ : syracuseStep 1031849 = 773887) B773887
theorem B1031999 : Blo 686314 1031999 := bstep (se 1 (by rfl) ⟨773999, by rfl⟩ : syracuseStep 1031999 = 1547999) B1547999
theorem B1032443 : Blo 686314 1032443 := bstep (se 1 (by rfl) ⟨774332, by rfl⟩ : syracuseStep 1032443 = 1548665) B1548665
theorem B1032569 : Blo 686314 1032569 := bstep (se 2 (by rfl) ⟨387213, by rfl⟩ : syracuseStep 1032569 = 774427) B774427
theorem B26493317 : Blo 686314 26493317 := bstep (se 4 (by rfl) ⟨2483748, by rfl⟩ : syracuseStep 26493317 = 4967497) B4967497
theorem B1032617 : Blo 686314 1032617 := bstep (se 2 (by rfl) ⟨387231, by rfl⟩ : syracuseStep 1032617 = 774463) B774463
theorem B1032863 : Blo 686314 1032863 := bstep (se 1 (by rfl) ⟨774647, by rfl⟩ : syracuseStep 1032863 = 1549295) B1549295
theorem B1164071 : Blo 686314 1164071 := bstep (se 1 (by rfl) ⟨873053, by rfl⟩ : syracuseStep 1164071 = 1746107) B1746107
theorem B3916781 : Blo 686314 3916781 := bstep (se 3 (by rfl) ⟨734396, by rfl⟩ : syracuseStep 3916781 = 1468793) B1468793
theorem B14894189 : Blo 686314 14894189 := bstep (se 3 (by rfl) ⟨2792660, by rfl⟩ : syracuseStep 14894189 = 5585321) B5585321
theorem B1033703 : Blo 686314 1033703 := bstep (se 1 (by rfl) ⟨775277, by rfl⟩ : syracuseStep 1033703 = 1550555) B1550555
theorem B1033769 : Blo 686314 1033769 := bstep (se 2 (by rfl) ⟨387663, by rfl⟩ : syracuseStep 1033769 = 775327) B775327
theorem B1099423 : Blo 686314 1099423 := bstep (se 1 (by rfl) ⟨824567, by rfl⟩ : syracuseStep 1099423 = 1649135) B1649135
theorem B30197609 : Blo 686314 30197609 := bstep (se 2 (by rfl) ⟨11324103, by rfl⟩ : syracuseStep 30197609 = 22648207) B22648207
theorem B1034651 : Blo 686314 1034651 := bstep (se 1 (by rfl) ⟨775988, by rfl⟩ : syracuseStep 1034651 = 1551977) B1551977
theorem B5229359 : Blo 686314 5229359 := bstep (se 1 (by rfl) ⟨3922019, by rfl⟩ : syracuseStep 5229359 = 7844039) B7844039
theorem B1100711 : Blo 686314 1100711 := bstep (se 1 (by rfl) ⟨825533, by rfl⟩ : syracuseStep 1100711 = 1651067) B1651067
theorem B774175 : Blo 686314 774175 := bstep (se 1 (by rfl) ⟨580631, by rfl⟩ : syracuseStep 774175 = 1161263) B1161263
theorem B45961339 : Blo 686314 45961339 := bstep (se 1 (by rfl) ⟨34471004, by rfl⟩ : syracuseStep 45961339 = 68942009) B68942009
theorem B873119 : Blo 686314 873119 := bstep (se 1 (by rfl) ⟨654839, by rfl⟩ : syracuseStep 873119 = 1309679) B1309679
theorem B774895 : Blo 686314 774895 := bstep (se 1 (by rfl) ⟨581171, by rfl⟩ : syracuseStep 774895 = 1162343) B1162343
theorem B3921155 : Blo 686314 3921155 := bstep (se 1 (by rfl) ⟨2940866, by rfl⟩ : syracuseStep 3921155 = 5881733) B5881733
theorem B776443 : Blo 686314 776443 := bstep (se 1 (by rfl) ⟨582332, by rfl⟩ : syracuseStep 776443 = 1164665) B1164665
theorem B50126039 : Blo 686314 50126039 := bstep (se 1 (by rfl) ⟨37594529, by rfl⟩ : syracuseStep 50126039 = 75189059) B75189059
theorem B2317895 : Blo 686314 2317895 := bstep (se 1 (by rfl) ⟨1738421, by rfl⟩ : syracuseStep 2317895 = 3476843) B3476843
theorem B1957547 : Blo 686314 1957547 := bstep (se 1 (by rfl) ⟨1468160, by rfl⟩ : syracuseStep 1957547 = 2936321) B2936321
theorem B3924071 : Blo 686314 3924071 := bstep (se 1 (by rfl) ⟨2943053, by rfl⟩ : syracuseStep 3924071 = 5886107) B5886107
theorem B23879785 : Blo 686314 23879785 := bstep (se 2 (by rfl) ⟨8954919, by rfl⟩ : syracuseStep 23879785 = 17909839) B17909839
theorem B4481831 : Blo 686314 4481831 := bstep (se 1 (by rfl) ⟨3361373, by rfl⟩ : syracuseStep 4481831 = 6722747) B6722747
theorem B10872899 : Blo 686314 10872899 := bstep (se 1 (by rfl) ⟨8154674, by rfl⟩ : syracuseStep 10872899 = 16309349) B16309349
theorem B8841311 : Blo 686314 8841311 := bstep (se 1 (by rfl) ⟨6630983, by rfl⟩ : syracuseStep 8841311 = 13261967) B13261967
theorem B1468639 : Blo 686314 1468639 := bstep (se 1 (by rfl) ⟨1101479, by rfl⟩ : syracuseStep 1468639 = 2202959) B2202959
theorem B3926303 : Blo 686314 3926303 := bstep (se 1 (by rfl) ⟨2944727, by rfl⟩ : syracuseStep 3926303 = 5889455) B5889455
theorem B4975343 : Blo 686314 4975343 := bstep (se 1 (by rfl) ⟨3731507, by rfl⟩ : syracuseStep 4975343 = 7463015) B7463015
theorem B1961273 : Blo 686314 1961273 := bstep (se 2 (by rfl) ⟨735477, by rfl⟩ : syracuseStep 1961273 = 1470955) B1470955
theorem B2322593 : Blo 686314 2322593 := bstep (se 2 (by rfl) ⟨870972, by rfl⟩ : syracuseStep 2322593 = 1741945) B1741945
theorem B163443019 : Blo 686314 163443019 := bstep (se 1 (by rfl) ⟨122582264, by rfl⟩ : syracuseStep 163443019 = 245164529) B245164529
theorem B2323187 : Blo 686314 2323187 := bstep (se 1 (by rfl) ⟨1742390, by rfl⟩ : syracuseStep 2323187 = 3484781) B3484781
theorem B5240051 : Blo 686314 5240051 := bstep (se 1 (by rfl) ⟨3930038, by rfl⟩ : syracuseStep 5240051 = 7860077) B7860077
theorem B687407 : Blo 686314 687407 := bstep (se 1 (by rfl) ⟨515555, by rfl⟩ : syracuseStep 687407 = 1031111) B1031111
theorem B2325995 : Blo 686314 2325995 := bstep (se 1 (by rfl) ⟨1744496, by rfl⟩ : syracuseStep 2325995 = 3488993) B3488993
theorem B687823 : Blo 686314 687823 := bstep (se 1 (by rfl) ⟨515867, by rfl⟩ : syracuseStep 687823 = 1031735) B1031735
theorem B11731067 : Blo 686314 11731067 := bstep (se 1 (by rfl) ⟨8798300, by rfl⟩ : syracuseStep 11731067 = 17596601) B17596601
theorem B688295 : Blo 686314 688295 := bstep (se 1 (by rfl) ⟨516221, by rfl⟩ : syracuseStep 688295 = 1032443) B1032443
theorem B688379 : Blo 686314 688379 := bstep (se 1 (by rfl) ⟨516284, by rfl⟩ : syracuseStep 688379 = 1032569) B1032569
theorem B17662211 : Blo 686314 17662211 := bstep (se 1 (by rfl) ⟨13246658, by rfl⟩ : syracuseStep 17662211 = 26493317) B26493317
theorem B688411 : Blo 686314 688411 := bstep (se 1 (by rfl) ⟨516308, by rfl⟩ : syracuseStep 688411 = 1032617) B1032617
theorem B688575 : Blo 686314 688575 := bstep (se 1 (by rfl) ⟨516431, by rfl⟩ : syracuseStep 688575 = 1032863) B1032863
theorem B9929459 : Blo 686314 9929459 := bstep (se 1 (by rfl) ⟨7447094, by rfl⟩ : syracuseStep 9929459 = 14894189) B14894189
theorem B2982881 : Blo 686314 2982881 := bstep (se 2 (by rfl) ⟨1118580, by rfl⟩ : syracuseStep 2982881 = 2237161) B2237161
theorem B689135 : Blo 686314 689135 := bstep (se 1 (by rfl) ⟨516851, by rfl⟩ : syracuseStep 689135 = 1033703) B1033703
theorem B689179 : Blo 686314 689179 := bstep (se 1 (by rfl) ⟨516884, by rfl⟩ : syracuseStep 689179 = 1033769) B1033769
theorem B689767 : Blo 686314 689767 := bstep (se 1 (by rfl) ⟨517325, by rfl⟩ : syracuseStep 689767 = 1034651) B1034651
theorem B2328317 : Blo 686314 2328317 := bstep (se 3 (by rfl) ⟨436559, by rfl⟩ : syracuseStep 2328317 = 873119) B873119
theorem B3475547 : Blo 686314 3475547 := bstep (se 1 (by rfl) ⟨2606660, by rfl⟩ : syracuseStep 3475547 = 5213321) B5213321
theorem B8360081 : Blo 686314 8360081 := bstep (se 2 (by rfl) ⟨3135030, by rfl⟩ : syracuseStep 8360081 = 6270061) B6270061
theorem B1545263 : Blo 686314 1545263 := bstep (se 1 (by rfl) ⟨1158947, by rfl⟩ : syracuseStep 1545263 = 2317895) B2317895
theorem B61281785 : Blo 686314 61281785 := bstep (se 2 (by rfl) ⟨22980669, by rfl⟩ : syracuseStep 61281785 = 45961339) B45961339
theorem B2987887 : Blo 686314 2987887 := bstep (se 1 (by rfl) ⟨2240915, by rfl⟩ : syracuseStep 2987887 = 4481831) B4481831
theorem B7248599 : Blo 686314 7248599 := bstep (se 1 (by rfl) ⟨5436449, by rfl⟩ : syracuseStep 7248599 = 10872899) B10872899
theorem B3316895 : Blo 686314 3316895 := bstep (se 1 (by rfl) ⟨2487671, by rfl⟩ : syracuseStep 3316895 = 4975343) B4975343
theorem B3481055 : Blo 686314 3481055 := bstep (se 1 (by rfl) ⟨2610791, by rfl⟩ : syracuseStep 3481055 = 5221583) B5221583
theorem B1548395 : Blo 686314 1548395 := bstep (se 1 (by rfl) ⟨1161296, by rfl⟩ : syracuseStep 1548395 = 2322593) B2322593
theorem B1548791 : Blo 686314 1548791 := bstep (se 1 (by rfl) ⟨1161593, by rfl⟩ : syracuseStep 1548791 = 2323187) B2323187
theorem B11150921 : Blo 686314 11150921 := bstep (se 2 (by rfl) ⟨4181595, by rfl⟩ : syracuseStep 11150921 = 8363191) B8363191
theorem B5220125 : Blo 686314 5220125 := bstep (se 3 (by rfl) ⟨978773, by rfl⟩ : syracuseStep 5220125 = 1957547) B1957547
theorem B1550663 : Blo 686314 1550663 := bstep (se 1 (by rfl) ⟨1162997, by rfl⟩ : syracuseStep 1550663 = 2325995) B2325995
theorem B1551527 : Blo 686314 1551527 := bstep (se 1 (by rfl) ⟨1163645, by rfl⟩ : syracuseStep 1551527 = 2327291) B2327291
theorem B1551599 : Blo 686314 1551599 := bstep (se 1 (by rfl) ⟨1163699, by rfl⟩ : syracuseStep 1551599 = 2327399) B2327399
theorem B1552031 : Blo 686314 1552031 := bstep (se 1 (by rfl) ⟨1164023, by rfl⟩ : syracuseStep 1552031 = 2328047) B2328047
theorem B1552103 : Blo 686314 1552103 := bstep (se 1 (by rfl) ⟨1164077, by rfl⟩ : syracuseStep 1552103 = 2328155) B2328155
theorem B20131739 : Blo 686314 20131739 := bstep (se 1 (by rfl) ⟨15098804, by rfl⟩ : syracuseStep 20131739 = 30197609) B30197609
theorem B1552319 : Blo 686314 1552319 := bstep (se 1 (by rfl) ⟨1164239, by rfl⟩ : syracuseStep 1552319 = 2328479) B2328479
theorem B3486239 : Blo 686314 3486239 := bstep (se 1 (by rfl) ⟨2614679, by rfl⟩ : syracuseStep 3486239 = 5229359) B5229359
theorem B733807 : Blo 686314 733807 := bstep (se 1 (by rfl) ⟨550355, by rfl⟩ : syracuseStep 733807 = 1100711) B1100711
theorem B4174591 : Blo 686314 4174591 := bstep (se 1 (by rfl) ⟨3130943, by rfl⟩ : syracuseStep 4174591 = 6261887) B6261887
theorem B1029863 : Blo 686314 1029863 := bstep (se 1 (by rfl) ⟨772397, by rfl⟩ : syracuseStep 1029863 = 1544795) B1544795
theorem B1030367 : Blo 686314 1030367 := bstep (se 1 (by rfl) ⟨772775, by rfl⟩ : syracuseStep 1030367 = 1545551) B1545551
theorem B6601459 : Blo 686314 6601459 := bstep (se 1 (by rfl) ⟨4951094, by rfl⟩ : syracuseStep 6601459 = 9902189) B9902189
theorem B1031783 : Blo 686314 1031783 := bstep (se 1 (by rfl) ⟨773837, by rfl⟩ : syracuseStep 1031783 = 1547675) B1547675
theorem B1163119 : Blo 686314 1163119 := bstep (se 1 (by rfl) ⟨872339, by rfl⟩ : syracuseStep 1163119 = 1744679) B1744679
theorem B1032233 : Blo 686314 1032233 := bstep (se 2 (by rfl) ⟨387087, by rfl⟩ : syracuseStep 1032233 = 774175) B774175
theorem B1032431 : Blo 686314 1032431 := bstep (se 1 (by rfl) ⟨774323, by rfl⟩ : syracuseStep 1032431 = 1548647) B1548647
theorem B217924025 : Blo 686314 217924025 := bstep (se 2 (by rfl) ⟨81721509, by rfl⟩ : syracuseStep 217924025 = 163443019) B163443019
theorem B1033031 : Blo 686314 1033031 := bstep (se 1 (by rfl) ⟨774773, by rfl⟩ : syracuseStep 1033031 = 1549547) B1549547
theorem B1033193 : Blo 686314 1033193 := bstep (se 2 (by rfl) ⟨387447, by rfl⟩ : syracuseStep 1033193 = 774895) B774895
theorem B1033631 : Blo 686314 1033631 := bstep (se 1 (by rfl) ⟨775223, by rfl⟩ : syracuseStep 1033631 = 1550447) B1550447
theorem B90655645 : Blo 686314 90655645 := bstep (se 3 (by rfl) ⟨16997933, by rfl⟩ : syracuseStep 90655645 = 33995867) B33995867
theorem B1035257 : Blo 686314 1035257 := bstep (se 2 (by rfl) ⟨388221, by rfl⟩ : syracuseStep 1035257 = 776443) B776443
theorem B1035263 : Blo 686314 1035263 := bstep (se 1 (by rfl) ⟨776447, by rfl⟩ : syracuseStep 1035263 = 1552895) B1552895
theorem B773275 : Blo 686314 773275 := bstep (se 1 (by rfl) ⟨579956, by rfl⟩ : syracuseStep 773275 = 1159913) B1159913
theorem B1035419 : Blo 686314 1035419 := bstep (se 1 (by rfl) ⟨776564, by rfl⟩ : syracuseStep 1035419 = 1553129) B1553129
theorem B6606107 : Blo 686314 6606107 := bstep (se 1 (by rfl) ⟨4954580, by rfl⟩ : syracuseStep 6606107 = 9909161) B9909161
theorem B3493367 : Blo 686314 3493367 := bstep (se 1 (by rfl) ⟨2620025, by rfl⟩ : syracuseStep 3493367 = 5240051) B5240051
theorem B4182763 : Blo 686314 4182763 := bstep (se 1 (by rfl) ⟨3137072, by rfl⟩ : syracuseStep 4182763 = 6274145) B6274145
theorem B2937961 : Blo 686314 2937961 := bstep (se 2 (by rfl) ⟨1101735, by rfl⟩ : syracuseStep 2937961 = 2203471) B2203471
theorem B31839713 : Blo 686314 31839713 := bstep (se 2 (by rfl) ⟨11939892, by rfl⟩ : syracuseStep 31839713 = 23879785) B23879785
theorem B776047 : Blo 686314 776047 := bstep (se 1 (by rfl) ⟨582035, by rfl⟩ : syracuseStep 776047 = 1164071) B1164071
theorem B5592979 : Blo 686314 5592979 := bstep (se 1 (by rfl) ⟨4194734, by rfl⟩ : syracuseStep 5592979 = 8389469) B8389469
theorem B2611187 : Blo 686314 2611187 := bstep (se 1 (by rfl) ⟨1958390, by rfl⟩ : syracuseStep 2611187 = 3916781) B3916781
theorem B4413811 : Blo 686314 4413811 := bstep (se 1 (by rfl) ⟨3310358, by rfl⟩ : syracuseStep 4413811 = 6620717) B6620717
theorem B1958185 : Blo 686314 1958185 := bstep (se 2 (by rfl) ⟨734319, by rfl⟩ : syracuseStep 1958185 = 1468639) B1468639
theorem B2318975 : Blo 686314 2318975 := bstep (se 1 (by rfl) ⟨1739231, by rfl⟩ : syracuseStep 2318975 = 3478463) B3478463
theorem B2614103 : Blo 686314 2614103 := bstep (se 1 (by rfl) ⟨1960577, by rfl⟩ : syracuseStep 2614103 = 3921155) B3921155
theorem B3630815 : Blo 686314 3630815 := bstep (se 1 (by rfl) ⟨2723111, by rfl⟩ : syracuseStep 3630815 = 5446223) B5446223
theorem B33417359 : Blo 686314 33417359 := bstep (se 1 (by rfl) ⟨25063019, by rfl⟩ : syracuseStep 33417359 = 50126039) B50126039
theorem B2616047 : Blo 686314 2616047 := bstep (se 1 (by rfl) ⟨1962035, by rfl⟩ : syracuseStep 2616047 = 3924071) B3924071
theorem B11464345 : Blo 686314 11464345 := bstep (se 2 (by rfl) ⟨4299129, by rfl⟩ : syracuseStep 11464345 = 8598259) B8598259
theorem B5894207 : Blo 686314 5894207 := bstep (se 1 (by rfl) ⟨4420655, by rfl⟩ : syracuseStep 5894207 = 8841311) B8841311
theorem B2617535 : Blo 686314 2617535 := bstep (se 1 (by rfl) ⟨1963151, by rfl⟩ : syracuseStep 2617535 = 3926303) B3926303
theorem B1307515 : Blo 686314 1307515 := bstep (se 1 (by rfl) ⟨980636, by rfl⟩ : syracuseStep 1307515 = 1961273) B1961273
theorem B2324051 : Blo 686314 2324051 := bstep (se 1 (by rfl) ⟨1743038, by rfl⟩ : syracuseStep 2324051 = 3486077) B3486077
theorem B1472347 : Blo 686314 1472347 := bstep (se 1 (by rfl) ⟨1104260, by rfl⟩ : syracuseStep 1472347 = 2208521) B2208521
theorem B5863589 : Blo 686314 5863589 := bstep (se 4 (by rfl) ⟨549711, by rfl⟩ : syracuseStep 5863589 = 1099423) B1099423
theorem B686463 : Blo 686314 686463 := bstep (se 1 (by rfl) ⟨514847, by rfl⟩ : syracuseStep 686463 = 1029695) B1029695
theorem B686703 : Blo 686314 686703 := bstep (se 1 (by rfl) ⟨515027, by rfl⟩ : syracuseStep 686703 = 1030055) B1030055
theorem B686747 : Blo 686314 686747 := bstep (se 1 (by rfl) ⟨515060, by rfl⟩ : syracuseStep 686747 = 1030121) B1030121
theorem B39680927 : Blo 686314 39680927 := bstep (se 1 (by rfl) ⟨29760695, by rfl⟩ : syracuseStep 39680927 = 59521391) B59521391
theorem B687207 : Blo 686314 687207 := bstep (se 1 (by rfl) ⟨515405, by rfl⟩ : syracuseStep 687207 = 1030811) B1030811
theorem B687215 : Blo 686314 687215 := bstep (se 1 (by rfl) ⟨515411, by rfl⟩ : syracuseStep 687215 = 1030823) B1030823
theorem B687231 : Blo 686314 687231 := bstep (se 1 (by rfl) ⟨515423, by rfl⟩ : syracuseStep 687231 = 1030847) B1030847
theorem B687263 : Blo 686314 687263 := bstep (se 1 (by rfl) ⟨515447, by rfl⟩ : syracuseStep 687263 = 1030895) B1030895
theorem B687271 : Blo 686314 687271 := bstep (se 1 (by rfl) ⟨515453, by rfl⟩ : syracuseStep 687271 = 1030907) B1030907
theorem B687487 : Blo 686314 687487 := bstep (se 1 (by rfl) ⟨515615, by rfl⟩ : syracuseStep 687487 = 1031231) B1031231
theorem B687519 : Blo 686314 687519 := bstep (se 1 (by rfl) ⟨515639, by rfl⟩ : syracuseStep 687519 = 1031279) B1031279
theorem B687899 : Blo 686314 687899 := bstep (se 1 (by rfl) ⟨515924, by rfl⟩ : syracuseStep 687899 = 1031849) B1031849
theorem B687999 : Blo 686314 687999 := bstep (se 1 (by rfl) ⟨515999, by rfl⟩ : syracuseStep 687999 = 1031999) B1031999
theorem B688155 : Blo 686314 688155 := bstep (se 1 (by rfl) ⟨516116, by rfl⟩ : syracuseStep 688155 = 1032233) B1032233
theorem B688287 : Blo 686314 688287 := bstep (se 1 (by rfl) ⟨516215, by rfl⟩ : syracuseStep 688287 = 1032431) B1032431
theorem B6619639 : Blo 686314 6619639 := bstep (se 1 (by rfl) ⟨4964729, by rfl⟩ : syracuseStep 6619639 = 9929459) B9929459
theorem B688687 : Blo 686314 688687 := bstep (se 1 (by rfl) ⟨516515, by rfl⟩ : syracuseStep 688687 = 1033031) B1033031
theorem B688795 : Blo 686314 688795 := bstep (se 1 (by rfl) ⟨516596, by rfl⟩ : syracuseStep 688795 = 1033193) B1033193
theorem B689087 : Blo 686314 689087 := bstep (se 1 (by rfl) ⟨516815, by rfl⟩ : syracuseStep 689087 = 1033631) B1033631
theorem B690171 : Blo 686314 690171 := bstep (se 1 (by rfl) ⟨517628, by rfl⟩ : syracuseStep 690171 = 1035257) B1035257
theorem B690175 : Blo 686314 690175 := bstep (se 1 (by rfl) ⟨517631, by rfl⟩ : syracuseStep 690175 = 1035263) B1035263
theorem B690279 : Blo 686314 690279 := bstep (se 1 (by rfl) ⟨517709, by rfl⟩ : syracuseStep 690279 = 1035419) B1035419
theorem B2328911 : Blo 686314 2328911 := bstep (se 1 (by rfl) ⟨1746683, by rfl⟩ : syracuseStep 2328911 = 3493367) B3493367
theorem B5573387 : Blo 686314 5573387 := bstep (se 1 (by rfl) ⟨4180040, by rfl⟩ : syracuseStep 5573387 = 8360081) B8360081
theorem B163418093 : Blo 686314 163418093 := bstep (se 3 (by rfl) ⟨30640892, by rfl⟩ : syracuseStep 163418093 = 61281785) B61281785
theorem B1740791 : Blo 686314 1740791 := bstep (se 1 (by rfl) ⟨1305593, by rfl⟩ : syracuseStep 1740791 = 2611187) B2611187
theorem B1545983 : Blo 686314 1545983 := bstep (se 1 (by rfl) ⟨1159487, by rfl⟩ : syracuseStep 1545983 = 2318975) B2318975
theorem B1742735 : Blo 686314 1742735 := bstep (se 1 (by rfl) ⟨1307051, by rfl⟩ : syracuseStep 1742735 = 2614103) B2614103
theorem B5577017 : Blo 686314 5577017 := bstep (se 2 (by rfl) ⟨2091381, by rfl⟩ : syracuseStep 5577017 = 4182763) B4182763
theorem B1743353 : Blo 686314 1743353 := bstep (se 2 (by rfl) ⟨653757, by rfl⟩ : syracuseStep 1743353 = 1307515) B1307515
theorem B3480083 : Blo 686314 3480083 := bstep (se 1 (by rfl) ⟨2610062, by rfl⟩ : syracuseStep 3480083 = 5220125) B5220125
theorem B1744031 : Blo 686314 1744031 := bstep (se 1 (by rfl) ⟨1308023, by rfl⟩ : syracuseStep 1744031 = 2616047) B2616047
theorem B1745023 : Blo 686314 1745023 := bstep (se 1 (by rfl) ⟨1308767, by rfl⟩ : syracuseStep 1745023 = 2617535) B2617535
theorem B1549367 : Blo 686314 1549367 := bstep (se 1 (by rfl) ⟨1162025, by rfl⟩ : syracuseStep 1549367 = 2324051) B2324051
theorem B3909059 : Blo 686314 3909059 := bstep (se 1 (by rfl) ⟨2931794, by rfl⟩ : syracuseStep 3909059 = 5863589) B5863589
theorem B26453951 : Blo 686314 26453951 := bstep (se 1 (by rfl) ⟨19840463, by rfl⟩ : syracuseStep 26453951 = 39680927) B39680927
theorem B1550825 : Blo 686314 1550825 := bstep (se 2 (by rfl) ⟨581559, by rfl⟩ : syracuseStep 1550825 = 1163119) B1163119
theorem B11774807 : Blo 686314 11774807 := bstep (se 1 (by rfl) ⟨8831105, by rfl⟩ : syracuseStep 11774807 = 17662211) B17662211
theorem B1552211 : Blo 686314 1552211 := bstep (se 1 (by rfl) ⟨1164158, by rfl⟩ : syracuseStep 1552211 = 2328317) B2328317
theorem B4404071 : Blo 686314 4404071 := bstep (se 1 (by rfl) ⟨3303053, by rfl⟩ : syracuseStep 4404071 = 6606107) B6606107
theorem B1030175 : Blo 686314 1030175 := bstep (se 1 (by rfl) ⟨772631, by rfl⟩ : syracuseStep 1030175 = 1545263) B1545263
theorem B1031033 : Blo 686314 1031033 := bstep (se 2 (by rfl) ⟨386637, by rfl⟩ : syracuseStep 1031033 = 773275) B773275
theorem B4832399 : Blo 686314 4832399 := bstep (se 1 (by rfl) ⟨3624299, by rfl⟩ : syracuseStep 4832399 = 7248599) B7248599
theorem B2211263 : Blo 686314 2211263 := bstep (se 1 (by rfl) ⟨1658447, by rfl⟩ : syracuseStep 2211263 = 3316895) B3316895
theorem B15285793 : Blo 686314 15285793 := bstep (se 2 (by rfl) ⟨5732172, by rfl⟩ : syracuseStep 15285793 = 11464345) B11464345
theorem B1032263 : Blo 686314 1032263 := bstep (se 1 (by rfl) ⟨774197, by rfl⟩ : syracuseStep 1032263 = 1548395) B1548395
theorem B1032527 : Blo 686314 1032527 := bstep (se 1 (by rfl) ⟨774395, by rfl⟩ : syracuseStep 1032527 = 1548791) B1548791
theorem B3917281 : Blo 686314 3917281 := bstep (se 2 (by rfl) ⟨1468980, by rfl⟩ : syracuseStep 3917281 = 2937961) B2937961
theorem B1033775 : Blo 686314 1033775 := bstep (se 1 (by rfl) ⟨775331, by rfl⟩ : syracuseStep 1033775 = 1550663) B1550663
theorem B1034351 : Blo 686314 1034351 := bstep (se 1 (by rfl) ⟨775763, by rfl⟩ : syracuseStep 1034351 = 1551527) B1551527
theorem B1034399 : Blo 686314 1034399 := bstep (se 1 (by rfl) ⟨775799, by rfl⟩ : syracuseStep 1034399 = 1551599) B1551599
theorem B1034687 : Blo 686314 1034687 := bstep (se 1 (by rfl) ⟨776015, by rfl⟩ : syracuseStep 1034687 = 1552031) B1552031
theorem B1034729 : Blo 686314 1034729 := bstep (se 2 (by rfl) ⟨388023, by rfl⟩ : syracuseStep 1034729 = 776047) B776047
theorem B3983849 : Blo 686314 3983849 := bstep (se 2 (by rfl) ⟨1493943, by rfl⟩ : syracuseStep 3983849 = 2987887) B2987887
theorem B1034735 : Blo 686314 1034735 := bstep (se 1 (by rfl) ⟨776051, by rfl⟩ : syracuseStep 1034735 = 1552103) B1552103
theorem B7457305 : Blo 686314 7457305 := bstep (se 2 (by rfl) ⟨2796489, by rfl⟩ : syracuseStep 7457305 = 5592979) B5592979
theorem B13421159 : Blo 686314 13421159 := bstep (se 1 (by rfl) ⟨10065869, by rfl⟩ : syracuseStep 13421159 = 20131739) B20131739
theorem B1034879 : Blo 686314 1034879 := bstep (se 1 (by rfl) ⟨776159, by rfl⟩ : syracuseStep 1034879 = 1552319) B1552319
theorem B5885081 : Blo 686314 5885081 := bstep (se 2 (by rfl) ⟨2206905, by rfl⟩ : syracuseStep 5885081 = 4413811) B4413811
theorem B8801945 : Blo 686314 8801945 := bstep (se 2 (by rfl) ⟨3300729, by rfl⟩ : syracuseStep 8801945 = 6601459) B6601459
theorem B7820711 : Blo 686314 7820711 := bstep (se 1 (by rfl) ⟨5865533, by rfl⟩ : syracuseStep 7820711 = 11731067) B11731067
theorem B2610913 : Blo 686314 2610913 := bstep (se 2 (by rfl) ⟨979092, by rfl⟩ : syracuseStep 2610913 = 1958185) B1958185
theorem B1988587 : Blo 686314 1988587 := bstep (se 1 (by rfl) ⟨1491440, by rfl⟩ : syracuseStep 1988587 = 2982881) B2982881
theorem B2317031 : Blo 686314 2317031 := bstep (se 1 (by rfl) ⟨1737773, by rfl⟩ : syracuseStep 2317031 = 3475547) B3475547
theorem B21226475 : Blo 686314 21226475 := bstep (se 1 (by rfl) ⟨15919856, by rfl⟩ : syracuseStep 21226475 = 31839713) B31839713
theorem B120874193 : Blo 686314 120874193 := bstep (se 2 (by rfl) ⟨45327822, by rfl⟩ : syracuseStep 120874193 = 90655645) B90655645
theorem B2324522933 : Blo 686314 2324522933 := bstep (se 5 (by rfl) ⟨108962012, by rfl⟩ : syracuseStep 2324522933 = 217924025) B217924025
theorem B2320703 : Blo 686314 2320703 := bstep (se 1 (by rfl) ⟨1740527, by rfl⟩ : syracuseStep 2320703 = 3481055) B3481055
theorem B978409 : Blo 686314 978409 := bstep (se 2 (by rfl) ⟨366903, by rfl⟩ : syracuseStep 978409 = 733807) B733807
theorem B5566121 : Blo 686314 5566121 := bstep (se 2 (by rfl) ⟨2087295, by rfl⟩ : syracuseStep 5566121 = 4174591) B4174591
theorem B7433947 : Blo 686314 7433947 := bstep (se 1 (by rfl) ⟨5575460, by rfl⟩ : syracuseStep 7433947 = 11150921) B11150921
theorem B2420543 : Blo 686314 2420543 := bstep (se 1 (by rfl) ⟨1815407, by rfl⟩ : syracuseStep 2420543 = 3630815) B3630815
theorem B22278239 : Blo 686314 22278239 := bstep (se 1 (by rfl) ⟨16708679, by rfl⟩ : syracuseStep 22278239 = 33417359) B33417359
theorem B1963129 : Blo 686314 1963129 := bstep (se 2 (by rfl) ⟨736173, by rfl⟩ : syracuseStep 1963129 = 1472347) B1472347
theorem B3929471 : Blo 686314 3929471 := bstep (se 1 (by rfl) ⟨2947103, by rfl⟩ : syracuseStep 3929471 = 5894207) B5894207
theorem B2324159 : Blo 686314 2324159 := bstep (se 1 (by rfl) ⟨1743119, by rfl⟩ : syracuseStep 2324159 = 3486239) B3486239
theorem B686575 : Blo 686314 686575 := bstep (se 1 (by rfl) ⟨514931, by rfl⟩ : syracuseStep 686575 = 1029863) B1029863
theorem B686911 : Blo 686314 686911 := bstep (se 1 (by rfl) ⟨515183, by rfl⟩ : syracuseStep 686911 = 1030367) B1030367
theorem B687855 : Blo 686314 687855 := bstep (se 1 (by rfl) ⟨515891, by rfl⟩ : syracuseStep 687855 = 1031783) B1031783
theorem B688175 : Blo 686314 688175 := bstep (se 1 (by rfl) ⟨516131, by rfl⟩ : syracuseStep 688175 = 1032263) B1032263
theorem B2326697 : Blo 686314 2326697 := bstep (se 2 (by rfl) ⟨872511, by rfl⟩ : syracuseStep 2326697 = 1745023) B1745023
theorem B688351 : Blo 686314 688351 := bstep (se 1 (by rfl) ⟨516263, by rfl⟩ : syracuseStep 688351 = 1032527) B1032527
theorem B689183 : Blo 686314 689183 := bstep (se 1 (by rfl) ⟨516887, by rfl⟩ : syracuseStep 689183 = 1033775) B1033775
theorem B689567 : Blo 686314 689567 := bstep (se 1 (by rfl) ⟨517175, by rfl⟩ : syracuseStep 689567 = 1034351) B1034351
theorem B689599 : Blo 686314 689599 := bstep (se 1 (by rfl) ⟨517199, by rfl⟩ : syracuseStep 689599 = 1034399) B1034399
theorem B689791 : Blo 686314 689791 := bstep (se 1 (by rfl) ⟨517343, by rfl⟩ : syracuseStep 689791 = 1034687) B1034687
theorem B689819 : Blo 686314 689819 := bstep (se 1 (by rfl) ⟨517364, by rfl⟩ : syracuseStep 689819 = 1034729) B1034729
theorem B2655899 : Blo 686314 2655899 := bstep (se 1 (by rfl) ⟨1991924, by rfl⟩ : syracuseStep 2655899 = 3983849) B3983849
theorem B689823 : Blo 686314 689823 := bstep (se 1 (by rfl) ⟨517367, by rfl⟩ : syracuseStep 689823 = 1034735) B1034735
theorem B8947439 : Blo 686314 8947439 := bstep (se 1 (by rfl) ⟨6710579, by rfl⟩ : syracuseStep 8947439 = 13421159) B13421159
theorem B689919 : Blo 686314 689919 := bstep (se 1 (by rfl) ⟨517439, by rfl⟩ : syracuseStep 689919 = 1034879) B1034879
theorem B5867963 : Blo 686314 5867963 := bstep (se 1 (by rfl) ⟨4400972, by rfl⟩ : syracuseStep 5867963 = 8801945) B8801945
theorem B5213807 : Blo 686314 5213807 := bstep (se 1 (by rfl) ⟨3910355, by rfl⟩ : syracuseStep 5213807 = 7820711) B7820711
theorem B1544687 : Blo 686314 1544687 := bstep (se 1 (by rfl) ⟨1158515, by rfl⟩ : syracuseStep 1544687 = 2317031) B2317031
theorem B80582795 : Blo 686314 80582795 := bstep (se 1 (by rfl) ⟨60437096, by rfl⟩ : syracuseStep 80582795 = 120874193) B120874193
theorem B17635967 : Blo 686314 17635967 := bstep (se 1 (by rfl) ⟨13226975, by rfl⟩ : syracuseStep 17635967 = 26453951) B26453951
theorem B1547135 : Blo 686314 1547135 := bstep (se 1 (by rfl) ⟨1160351, by rfl⟩ : syracuseStep 1547135 = 2320703) B2320703
theorem B3481217 : Blo 686314 3481217 := bstep (se 2 (by rfl) ⟨1305456, by rfl⟩ : syracuseStep 3481217 = 2610913) B2610913
theorem B3710747 : Blo 686314 3710747 := bstep (se 1 (by rfl) ⟨2783060, by rfl⟩ : syracuseStep 3710747 = 5566121) B5566121
theorem B1613695 : Blo 686314 1613695 := bstep (se 1 (by rfl) ⟨1210271, by rfl⟩ : syracuseStep 1613695 = 2420543) B2420543
theorem B5218181 : Blo 686314 5218181 := bstep (se 4 (by rfl) ⟨489204, by rfl⟩ : syracuseStep 5218181 = 978409) B978409
theorem B14852159 : Blo 686314 14852159 := bstep (se 1 (by rfl) ⟨11139119, by rfl⟩ : syracuseStep 14852159 = 22278239) B22278239
theorem B12886397 : Blo 686314 12886397 := bstep (se 3 (by rfl) ⟨2416199, by rfl⟩ : syracuseStep 12886397 = 4832399) B4832399
theorem B1549439 : Blo 686314 1549439 := bstep (se 1 (by rfl) ⟨1162079, by rfl⟩ : syracuseStep 1549439 = 2324159) B2324159
theorem B8826185 : Blo 686314 8826185 := bstep (se 2 (by rfl) ⟨3309819, by rfl⟩ : syracuseStep 8826185 = 6619639) B6619639
theorem B1552607 : Blo 686314 1552607 := bstep (se 1 (by rfl) ⟨1164455, by rfl⟩ : syracuseStep 1552607 = 2328911) B2328911
theorem B3715591 : Blo 686314 3715591 := bstep (se 1 (by rfl) ⟨2786693, by rfl⟩ : syracuseStep 3715591 = 5573387) B5573387
theorem B5223041 : Blo 686314 5223041 := bstep (se 2 (by rfl) ⟨1958640, by rfl⟩ : syracuseStep 5223041 = 3917281) B3917281
theorem B11744189 : Blo 686314 11744189 := bstep (se 3 (by rfl) ⟨2202035, by rfl⟩ : syracuseStep 11744189 = 4404071) B4404071
theorem B56603933 : Blo 686314 56603933 := bstep (se 3 (by rfl) ⟨10613237, by rfl⟩ : syracuseStep 56603933 = 21226475) B21226475
theorem B1160527 : Blo 686314 1160527 := bstep (se 1 (by rfl) ⟨870395, by rfl⟩ : syracuseStep 1160527 = 1740791) B1740791
theorem B9943073 : Blo 686314 9943073 := bstep (se 2 (by rfl) ⟨3728652, by rfl⟩ : syracuseStep 9943073 = 7457305) B7457305
theorem B1030655 : Blo 686314 1030655 := bstep (se 1 (by rfl) ⟨772991, by rfl⟩ : syracuseStep 1030655 = 1545983) B1545983
theorem B1161823 : Blo 686314 1161823 := bstep (se 1 (by rfl) ⟨871367, by rfl⟩ : syracuseStep 1161823 = 1742735) B1742735
theorem B1162235 : Blo 686314 1162235 := bstep (se 1 (by rfl) ⟨871676, by rfl⟩ : syracuseStep 1162235 = 1743353) B1743353
theorem B1162687 : Blo 686314 1162687 := bstep (se 1 (by rfl) ⟨872015, by rfl⟩ : syracuseStep 1162687 = 1744031) B1744031
theorem B9911929 : Blo 686314 9911929 := bstep (se 2 (by rfl) ⟨3716973, by rfl⟩ : syracuseStep 9911929 = 7433947) B7433947
theorem B1032911 : Blo 686314 1032911 := bstep (se 1 (by rfl) ⟨774683, by rfl⟩ : syracuseStep 1032911 = 1549367) B1549367
theorem B2606039 : Blo 686314 2606039 := bstep (se 1 (by rfl) ⟨1954529, by rfl⟩ : syracuseStep 2606039 = 3909059) B3909059
theorem B1549681955 : Blo 686314 1549681955 := bstep (se 1 (by rfl) ⟨1162261466, by rfl⟩ : syracuseStep 1549681955 = 2324522933) B2324522933
theorem B1033883 : Blo 686314 1033883 := bstep (se 1 (by rfl) ⟨775412, by rfl⟩ : syracuseStep 1033883 = 1550825) B1550825
theorem B7849871 : Blo 686314 7849871 := bstep (se 1 (by rfl) ⟨5887403, by rfl⟩ : syracuseStep 7849871 = 11774807) B11774807
theorem B1034807 : Blo 686314 1034807 := bstep (se 1 (by rfl) ⟨776105, by rfl⟩ : syracuseStep 1034807 = 1552211) B1552211
theorem B3923387 : Blo 686314 3923387 := bstep (se 1 (by rfl) ⟨2942540, by rfl⟩ : syracuseStep 3923387 = 5885081) B5885081
theorem B108945395 : Blo 686314 108945395 := bstep (se 1 (by rfl) ⟨81709046, by rfl⟩ : syracuseStep 108945395 = 163418093) B163418093
theorem B2320055 : Blo 686314 2320055 := bstep (se 1 (by rfl) ⟨1740041, by rfl⟩ : syracuseStep 2320055 = 3480083) B3480083
theorem B14872045 : Blo 686314 14872045 := bstep (se 3 (by rfl) ⟨2788508, by rfl⟩ : syracuseStep 14872045 = 5577017) B5577017
theorem B2617505 : Blo 686314 2617505 := bstep (se 2 (by rfl) ⟨981564, by rfl⟩ : syracuseStep 2617505 = 1963129) B1963129
theorem B2651449 : Blo 686314 2651449 := bstep (se 2 (by rfl) ⟨994293, by rfl⟩ : syracuseStep 2651449 = 1988587) B1988587
theorem B2619647 : Blo 686314 2619647 := bstep (se 1 (by rfl) ⟨1964735, by rfl⟩ : syracuseStep 2619647 = 3929471) B3929471
theorem B686783 : Blo 686314 686783 := bstep (se 1 (by rfl) ⟨515087, by rfl⟩ : syracuseStep 686783 = 1030175) B1030175
theorem B687355 : Blo 686314 687355 := bstep (se 1 (by rfl) ⟨515516, by rfl⟩ : syracuseStep 687355 = 1031033) B1031033
theorem B20381057 : Blo 686314 20381057 := bstep (se 2 (by rfl) ⟨7642896, by rfl⟩ : syracuseStep 20381057 = 15285793) B15285793
theorem B1474175 : Blo 686314 1474175 := bstep (se 1 (by rfl) ⟨1105631, by rfl⟩ : syracuseStep 1474175 = 2211263) B2211263
theorem B688607 : Blo 686314 688607 := bstep (se 1 (by rfl) ⟨516455, by rfl⟩ : syracuseStep 688607 = 1032911) B1032911
theorem B1737359 : Blo 686314 1737359 := bstep (se 1 (by rfl) ⟨1303019, by rfl⟩ : syracuseStep 1737359 = 2606039) B2606039
theorem B689255 : Blo 686314 689255 := bstep (se 1 (by rfl) ⟨516941, by rfl⟩ : syracuseStep 689255 = 1033883) B1033883
theorem B1770599 : Blo 686314 1770599 := bstep (se 1 (by rfl) ⟨1327949, by rfl⟩ : syracuseStep 1770599 = 2655899) B2655899
theorem B5964959 : Blo 686314 5964959 := bstep (se 1 (by rfl) ⟨4473719, by rfl⟩ : syracuseStep 5964959 = 8947439) B8947439
theorem B689871 : Blo 686314 689871 := bstep (se 1 (by rfl) ⟨517403, by rfl⟩ : syracuseStep 689871 = 1034807) B1034807
theorem B3475871 : Blo 686314 3475871 := bstep (se 1 (by rfl) ⟨2606903, by rfl⟩ : syracuseStep 3475871 = 5213807) B5213807
theorem B19829393 : Blo 686314 19829393 := bstep (se 2 (by rfl) ⟨7436022, by rfl⟩ : syracuseStep 19829393 = 14872045) B14872045
theorem B3478787 : Blo 686314 3478787 := bstep (se 1 (by rfl) ⟨2609090, by rfl⟩ : syracuseStep 3478787 = 5218181) B5218181
theorem B9901439 : Blo 686314 9901439 := bstep (se 1 (by rfl) ⟨7426079, by rfl⟩ : syracuseStep 9901439 = 14852159) B14852159
theorem B8590931 : Blo 686314 8590931 := bstep (se 1 (by rfl) ⟨6443198, by rfl⟩ : syracuseStep 8590931 = 12886397) B12886397
theorem B4954121 : Blo 686314 4954121 := bstep (se 2 (by rfl) ⟨1857795, by rfl⟩ : syracuseStep 4954121 = 3715591) B3715591
theorem B1546703 : Blo 686314 1546703 := bstep (se 1 (by rfl) ⟨1160027, by rfl⟩ : syracuseStep 1546703 = 2320055) B2320055
theorem B1547369 : Blo 686314 1547369 := bstep (se 2 (by rfl) ⟨580263, by rfl⟩ : syracuseStep 1547369 = 1160527) B1160527
theorem B1745003 : Blo 686314 1745003 := bstep (se 1 (by rfl) ⟨1308752, by rfl⟩ : syracuseStep 1745003 = 2617505) B2617505
theorem B3482027 : Blo 686314 3482027 := bstep (se 1 (by rfl) ⟨2611520, by rfl⟩ : syracuseStep 3482027 = 5223041) B5223041
theorem B1549097 : Blo 686314 1549097 := bstep (se 2 (by rfl) ⟨580911, by rfl⟩ : syracuseStep 1549097 = 1161823) B1161823
theorem B6628715 : Blo 686314 6628715 := bstep (se 1 (by rfl) ⟨4971536, by rfl⟩ : syracuseStep 6628715 = 9943073) B9943073
theorem B1746431 : Blo 686314 1746431 := bstep (se 1 (by rfl) ⟨1309823, by rfl⟩ : syracuseStep 1746431 = 2619647) B2619647
theorem B1550249 : Blo 686314 1550249 := bstep (se 2 (by rfl) ⟨581343, by rfl⟩ : syracuseStep 1550249 = 1162687) B1162687
theorem B13215905 : Blo 686314 13215905 := bstep (se 2 (by rfl) ⟨4955964, by rfl⟩ : syracuseStep 13215905 = 9911929) B9911929
theorem B1551131 : Blo 686314 1551131 := bstep (se 1 (by rfl) ⟨1163348, by rfl⟩ : syracuseStep 1551131 = 2326697) B2326697
theorem B1033121303 : Blo 686314 1033121303 := bstep (se 1 (by rfl) ⟨774840977, by rfl⟩ : syracuseStep 1033121303 = 1549681955) B1549681955
theorem B3911975 : Blo 686314 3911975 := bstep (se 1 (by rfl) ⟨2933981, by rfl⟩ : syracuseStep 3911975 = 5867963) B5867963
theorem B1029791 : Blo 686314 1029791 := bstep (se 1 (by rfl) ⟨772343, by rfl⟩ : syracuseStep 1029791 = 1544687) B1544687
theorem B53721863 : Blo 686314 53721863 := bstep (se 1 (by rfl) ⟨40291397, by rfl⟩ : syracuseStep 53721863 = 80582795) B80582795
theorem B1031423 : Blo 686314 1031423 := bstep (se 1 (by rfl) ⟨773567, by rfl⟩ : syracuseStep 1031423 = 1547135) B1547135
theorem B2473831 : Blo 686314 2473831 := bstep (se 1 (by rfl) ⟨1855373, by rfl⟩ : syracuseStep 2473831 = 3710747) B3710747
theorem B72630263 : Blo 686314 72630263 := bstep (se 1 (by rfl) ⟨54472697, by rfl⟩ : syracuseStep 72630263 = 108945395) B108945395
theorem B1032959 : Blo 686314 1032959 := bstep (se 1 (by rfl) ⟨774719, by rfl⟩ : syracuseStep 1032959 = 1549439) B1549439
theorem B5884123 : Blo 686314 5884123 := bstep (se 1 (by rfl) ⟨4413092, by rfl⟩ : syracuseStep 5884123 = 8826185) B8826185
theorem B1035071 : Blo 686314 1035071 := bstep (se 1 (by rfl) ⟨776303, by rfl⟩ : syracuseStep 1035071 = 1552607) B1552607
theorem B37735955 : Blo 686314 37735955 := bstep (se 1 (by rfl) ⟨28301966, by rfl⟩ : syracuseStep 37735955 = 56603933) B56603933
theorem B774823 : Blo 686314 774823 := bstep (se 1 (by rfl) ⟨581117, by rfl⟩ : syracuseStep 774823 = 1162235) B1162235
theorem B13587371 : Blo 686314 13587371 := bstep (se 1 (by rfl) ⟨10190528, by rfl⟩ : syracuseStep 13587371 = 20381057) B20381057
theorem B2151593 : Blo 686314 2151593 := bstep (se 2 (by rfl) ⟨806847, by rfl⟩ : syracuseStep 2151593 = 1613695) B1613695
theorem B5233247 : Blo 686314 5233247 := bstep (se 1 (by rfl) ⟨3924935, by rfl⟩ : syracuseStep 5233247 = 7849871) B7849871
theorem B11757311 : Blo 686314 11757311 := bstep (se 1 (by rfl) ⟨8817983, by rfl⟩ : syracuseStep 11757311 = 17635967) B17635967
theorem B2615591 : Blo 686314 2615591 := bstep (se 1 (by rfl) ⟨1961693, by rfl⟩ : syracuseStep 2615591 = 3923387) B3923387
theorem B2320811 : Blo 686314 2320811 := bstep (se 1 (by rfl) ⟨1740608, by rfl⟩ : syracuseStep 2320811 = 3481217) B3481217
theorem B3535265 : Blo 686314 3535265 := bstep (se 2 (by rfl) ⟨1325724, by rfl⟩ : syracuseStep 3535265 = 2651449) B2651449
theorem B7829459 : Blo 686314 7829459 := bstep (se 1 (by rfl) ⟨5872094, by rfl⟩ : syracuseStep 7829459 = 11744189) B11744189
theorem B687103 : Blo 686314 687103 := bstep (se 1 (by rfl) ⟨515327, by rfl⟩ : syracuseStep 687103 = 1030655) B1030655
theorem B982783 : Blo 686314 982783 := bstep (se 1 (by rfl) ⟨737087, by rfl⟩ : syracuseStep 982783 = 1474175) B1474175
theorem B688639 : Blo 686314 688639 := bstep (se 1 (by rfl) ⟨516479, by rfl⟩ : syracuseStep 688639 = 1032959) B1032959
theorem B690047 : Blo 686314 690047 := bstep (se 1 (by rfl) ⟨517535, by rfl⟩ : syracuseStep 690047 = 1035071) B1035071
theorem B4721597 : Blo 686314 4721597 := bstep (se 3 (by rfl) ⟨885299, by rfl⟩ : syracuseStep 4721597 = 1770599) B1770599
theorem B7838207 : Blo 686314 7838207 := bstep (se 1 (by rfl) ⟨5878655, by rfl⟩ : syracuseStep 7838207 = 11757311) B11757311
theorem B1743727 : Blo 686314 1743727 := bstep (se 1 (by rfl) ⟨1307795, by rfl⟩ : syracuseStep 1743727 = 2615591) B2615591
theorem B1547207 : Blo 686314 1547207 := bstep (se 1 (by rfl) ⟨1160405, by rfl⟩ : syracuseStep 1547207 = 2320811) B2320811
theorem B5219639 : Blo 686314 5219639 := bstep (se 1 (by rfl) ⟨3914729, by rfl⟩ : syracuseStep 5219639 = 7829459) B7829459
theorem B1158239 : Blo 686314 1158239 := bstep (se 1 (by rfl) ⟨868679, by rfl⟩ : syracuseStep 1158239 = 1737359) B1737359
theorem B7845497 : Blo 686314 7845497 := bstep (se 2 (by rfl) ⟨2942061, by rfl⟩ : syracuseStep 7845497 = 5884123) B5884123
theorem B15906557 : Blo 686314 15906557 := bstep (se 3 (by rfl) ⟨2982479, by rfl⟩ : syracuseStep 15906557 = 5964959) B5964959
theorem B13219595 : Blo 686314 13219595 := bstep (se 1 (by rfl) ⟨9914696, by rfl⟩ : syracuseStep 13219595 = 19829393) B19829393
theorem B9058247 : Blo 686314 9058247 := bstep (se 1 (by rfl) ⟨6793685, by rfl⟩ : syracuseStep 9058247 = 13587371) B13587371
theorem B6600959 : Blo 686314 6600959 := bstep (se 1 (by rfl) ⟨4950719, by rfl⟩ : syracuseStep 6600959 = 9901439) B9901439
theorem B1031135 : Blo 686314 1031135 := bstep (se 1 (by rfl) ⟨773351, by rfl⟩ : syracuseStep 1031135 = 1546703) B1546703
theorem B3488831 : Blo 686314 3488831 := bstep (se 1 (by rfl) ⟨2616623, by rfl⟩ : syracuseStep 3488831 = 5233247) B5233247
theorem B1031579 : Blo 686314 1031579 := bstep (se 1 (by rfl) ⟨773684, by rfl⟩ : syracuseStep 1031579 = 1547369) B1547369
theorem B1163335 : Blo 686314 1163335 := bstep (se 1 (by rfl) ⟨872501, by rfl⟩ : syracuseStep 1163335 = 1745003) B1745003
theorem B1032731 : Blo 686314 1032731 := bstep (se 1 (by rfl) ⟨774548, by rfl⟩ : syracuseStep 1032731 = 1549097) B1549097
theorem B1033097 : Blo 686314 1033097 := bstep (se 2 (by rfl) ⟨387411, by rfl⟩ : syracuseStep 1033097 = 774823) B774823
theorem B1164287 : Blo 686314 1164287 := bstep (se 1 (by rfl) ⟨873215, by rfl⟩ : syracuseStep 1164287 = 1746431) B1746431
theorem B1033499 : Blo 686314 1033499 := bstep (se 1 (by rfl) ⟨775124, by rfl⟩ : syracuseStep 1033499 = 1550249) B1550249
theorem B1034087 : Blo 686314 1034087 := bstep (se 1 (by rfl) ⟨775565, by rfl⟩ : syracuseStep 1034087 = 1551131) B1551131
theorem B2607983 : Blo 686314 2607983 := bstep (se 1 (by rfl) ⟨1955987, by rfl⟩ : syracuseStep 2607983 = 3911975) B3911975
theorem B3298441 : Blo 686314 3298441 := bstep (se 2 (by rfl) ⟨1236915, by rfl⟩ : syracuseStep 3298441 = 2473831) B2473831
theorem B48420175 : Blo 686314 48420175 := bstep (se 1 (by rfl) ⟨36315131, by rfl⟩ : syracuseStep 48420175 = 72630263) B72630263
theorem B9427373 : Blo 686314 9427373 := bstep (se 3 (by rfl) ⟨1767632, by rfl⟩ : syracuseStep 9427373 = 3535265) B3535265
theorem B2317247 : Blo 686314 2317247 := bstep (se 1 (by rfl) ⟨1737935, by rfl⟩ : syracuseStep 2317247 = 3475871) B3475871
theorem B25157303 : Blo 686314 25157303 := bstep (se 1 (by rfl) ⟨18867977, by rfl⟩ : syracuseStep 25157303 = 37735955) B37735955
theorem B1434395 : Blo 686314 1434395 := bstep (se 1 (by rfl) ⟨1075796, by rfl⟩ : syracuseStep 1434395 = 2151593) B2151593
theorem B2319191 : Blo 686314 2319191 := bstep (se 1 (by rfl) ⟨1739393, by rfl⟩ : syracuseStep 2319191 = 3478787) B3478787
theorem B5727287 : Blo 686314 5727287 := bstep (se 1 (by rfl) ⟨4295465, by rfl⟩ : syracuseStep 5727287 = 8590931) B8590931
theorem B3302747 : Blo 686314 3302747 := bstep (se 1 (by rfl) ⟨2477060, by rfl⟩ : syracuseStep 3302747 = 4954121) B4954121
theorem B2321351 : Blo 686314 2321351 := bstep (se 1 (by rfl) ⟨1741013, by rfl⟩ : syracuseStep 2321351 = 3482027) B3482027
theorem B4419143 : Blo 686314 4419143 := bstep (se 1 (by rfl) ⟨3314357, by rfl⟩ : syracuseStep 4419143 = 6628715) B6628715
theorem B8810603 : Blo 686314 8810603 := bstep (se 1 (by rfl) ⟨6607952, by rfl⟩ : syracuseStep 8810603 = 13215905) B13215905
theorem B688747535 : Blo 686314 688747535 := bstep (se 1 (by rfl) ⟨516560651, by rfl⟩ : syracuseStep 688747535 = 1033121303) B1033121303
theorem B686527 : Blo 686314 686527 := bstep (se 1 (by rfl) ⟨514895, by rfl⟩ : syracuseStep 686527 = 1029791) B1029791
theorem B5241509 : Blo 686314 5241509 := bstep (se 4 (by rfl) ⟨491391, by rfl⟩ : syracuseStep 5241509 = 982783) B982783
theorem B35814575 : Blo 686314 35814575 := bstep (se 1 (by rfl) ⟨26860931, by rfl⟩ : syracuseStep 35814575 = 53721863) B53721863
theorem B687615 : Blo 686314 687615 := bstep (se 1 (by rfl) ⟨515711, by rfl⟩ : syracuseStep 687615 = 1031423) B1031423
theorem B688487 : Blo 686314 688487 := bstep (se 1 (by rfl) ⟨516365, by rfl⟩ : syracuseStep 688487 = 1032731) B1032731
theorem B688731 : Blo 686314 688731 := bstep (se 1 (by rfl) ⟨516548, by rfl⟩ : syracuseStep 688731 = 1033097) B1033097
theorem B688999 : Blo 686314 688999 := bstep (se 1 (by rfl) ⟨516749, by rfl⟩ : syracuseStep 688999 = 1033499) B1033499
theorem B689391 : Blo 686314 689391 := bstep (se 1 (by rfl) ⟨517043, by rfl⟩ : syracuseStep 689391 = 1034087) B1034087
theorem B1738655 : Blo 686314 1738655 := bstep (se 1 (by rfl) ⟨1303991, by rfl⟩ : syracuseStep 1738655 = 2607983) B2607983
theorem B3147731 : Blo 686314 3147731 := bstep (se 1 (by rfl) ⟨2360798, by rfl⟩ : syracuseStep 3147731 = 4721597) B4721597
theorem B1544831 : Blo 686314 1544831 := bstep (se 1 (by rfl) ⟨1158623, by rfl⟩ : syracuseStep 1544831 = 2317247) B2317247
theorem B956263 : Blo 686314 956263 := bstep (se 1 (by rfl) ⟨717197, by rfl⟩ : syracuseStep 956263 = 1434395) B1434395
theorem B1546127 : Blo 686314 1546127 := bstep (se 1 (by rfl) ⟨1159595, by rfl⟩ : syracuseStep 1546127 = 2319191) B2319191
theorem B3479759 : Blo 686314 3479759 := bstep (se 1 (by rfl) ⟨2609819, by rfl⟩ : syracuseStep 3479759 = 5219639) B5219639
theorem B2201831 : Blo 686314 2201831 := bstep (se 1 (by rfl) ⟨1651373, by rfl⟩ : syracuseStep 2201831 = 3302747) B3302747
theorem B4397921 : Blo 686314 4397921 := bstep (se 2 (by rfl) ⟨1649220, by rfl⟩ : syracuseStep 4397921 = 3298441) B3298441
theorem B64560233 : Blo 686314 64560233 := bstep (se 2 (by rfl) ⟨24210087, by rfl⟩ : syracuseStep 64560233 = 48420175) B48420175
theorem B1547567 : Blo 686314 1547567 := bstep (se 1 (by rfl) ⟨1160675, by rfl⟩ : syracuseStep 1547567 = 2321351) B2321351
theorem B5873735 : Blo 686314 5873735 := bstep (se 1 (by rfl) ⟨4405301, by rfl⟩ : syracuseStep 5873735 = 8810603) B8810603
theorem B6038831 : Blo 686314 6038831 := bstep (se 1 (by rfl) ⟨4529123, by rfl⟩ : syracuseStep 6038831 = 9058247) B9058247
theorem B4400639 : Blo 686314 4400639 := bstep (se 1 (by rfl) ⟨3300479, by rfl⟩ : syracuseStep 4400639 = 6600959) B6600959
theorem B1551113 : Blo 686314 1551113 := bstep (se 2 (by rfl) ⟨581667, by rfl⟩ : syracuseStep 1551113 = 1163335) B1163335
theorem B5225471 : Blo 686314 5225471 := bstep (se 1 (by rfl) ⟨3919103, by rfl⟩ : syracuseStep 5225471 = 7838207) B7838207
theorem B1031471 : Blo 686314 1031471 := bstep (se 1 (by rfl) ⟨773603, by rfl⟩ : syracuseStep 1031471 = 1547207) B1547207
theorem B3818191 : Blo 686314 3818191 := bstep (se 1 (by rfl) ⟨2863643, by rfl⟩ : syracuseStep 3818191 = 5727287) B5727287
theorem B772159 : Blo 686314 772159 := bstep (se 1 (by rfl) ⟨579119, by rfl⟩ : syracuseStep 772159 = 1158239) B1158239
theorem B459165023 : Blo 686314 459165023 := bstep (se 1 (by rfl) ⟨344373767, by rfl⟩ : syracuseStep 459165023 = 688747535) B688747535
theorem B5230331 : Blo 686314 5230331 := bstep (se 1 (by rfl) ⟨3922748, by rfl⟩ : syracuseStep 5230331 = 7845497) B7845497
theorem B10604371 : Blo 686314 10604371 := bstep (se 1 (by rfl) ⟨7953278, by rfl⟩ : syracuseStep 10604371 = 15906557) B15906557
theorem B3494339 : Blo 686314 3494339 := bstep (se 1 (by rfl) ⟨2620754, by rfl⟩ : syracuseStep 3494339 = 5241509) B5241509
theorem B23876383 : Blo 686314 23876383 := bstep (se 1 (by rfl) ⟨17907287, by rfl⟩ : syracuseStep 23876383 = 35814575) B35814575
theorem B776191 : Blo 686314 776191 := bstep (se 1 (by rfl) ⟨582143, by rfl⟩ : syracuseStep 776191 = 1164287) B1164287
theorem B6284915 : Blo 686314 6284915 := bstep (se 1 (by rfl) ⟨4713686, by rfl⟩ : syracuseStep 6284915 = 9427373) B9427373
theorem B16771535 : Blo 686314 16771535 := bstep (se 1 (by rfl) ⟨12578651, by rfl⟩ : syracuseStep 16771535 = 25157303) B25157303
theorem B2946095 : Blo 686314 2946095 := bstep (se 1 (by rfl) ⟨2209571, by rfl⟩ : syracuseStep 2946095 = 4419143) B4419143
theorem B2324969 : Blo 686314 2324969 := bstep (se 2 (by rfl) ⟨871863, by rfl⟩ : syracuseStep 2324969 = 1743727) B1743727
theorem B8813063 : Blo 686314 8813063 := bstep (se 1 (by rfl) ⟨6609797, by rfl⟩ : syracuseStep 8813063 = 13219595) B13219595
theorem B687423 : Blo 686314 687423 := bstep (se 1 (by rfl) ⟨515567, by rfl⟩ : syracuseStep 687423 = 1031135) B1031135
theorem B2325887 : Blo 686314 2325887 := bstep (se 1 (by rfl) ⟨1744415, by rfl⟩ : syracuseStep 2325887 = 3488831) B3488831
theorem B687719 : Blo 686314 687719 := bstep (se 1 (by rfl) ⟨515789, by rfl⟩ : syracuseStep 687719 = 1031579) B1031579
theorem B2098487 : Blo 686314 2098487 := bstep (se 1 (by rfl) ⟨1573865, by rfl⟩ : syracuseStep 2098487 = 3147731) B3147731
theorem B2329559 : Blo 686314 2329559 := bstep (se 1 (by rfl) ⟨1747169, by rfl⟩ : syracuseStep 2329559 = 3494339) B3494339
theorem B11181023 : Blo 686314 11181023 := bstep (se 1 (by rfl) ⟨8385767, by rfl⟩ : syracuseStep 11181023 = 16771535) B16771535
theorem B1549979 : Blo 686314 1549979 := bstep (se 1 (by rfl) ⟨1162484, by rfl⟩ : syracuseStep 1549979 = 2324969) B2324969
theorem B5875375 : Blo 686314 5875375 := bstep (se 1 (by rfl) ⟨4406531, by rfl⟩ : syracuseStep 5875375 = 8813063) B8813063
theorem B3483647 : Blo 686314 3483647 := bstep (se 1 (by rfl) ⟨2612735, by rfl⟩ : syracuseStep 3483647 = 5225471) B5225471
theorem B1550591 : Blo 686314 1550591 := bstep (se 1 (by rfl) ⟨1162943, by rfl⟩ : syracuseStep 1550591 = 2325887) B2325887
theorem B5090921 : Blo 686314 5090921 := bstep (se 2 (by rfl) ⟨1909095, by rfl⟩ : syracuseStep 5090921 = 3818191) B3818191
theorem B1159103 : Blo 686314 1159103 := bstep (se 1 (by rfl) ⟨869327, by rfl⟩ : syracuseStep 1159103 = 1738655) B1738655
theorem B3486887 : Blo 686314 3486887 := bstep (se 1 (by rfl) ⟨2615165, by rfl⟩ : syracuseStep 3486887 = 5230331) B5230331
theorem B1029545 : Blo 686314 1029545 := bstep (se 2 (by rfl) ⟨386079, by rfl⟩ : syracuseStep 1029545 = 772159) B772159
theorem B1029887 : Blo 686314 1029887 := bstep (se 1 (by rfl) ⟨772415, by rfl⟩ : syracuseStep 1029887 = 1544831) B1544831
theorem B16103549 : Blo 686314 16103549 := bstep (se 3 (by rfl) ⟨3019415, by rfl⟩ : syracuseStep 16103549 = 6038831) B6038831
theorem B1030751 : Blo 686314 1030751 := bstep (se 1 (by rfl) ⟨773063, by rfl⟩ : syracuseStep 1030751 = 1546127) B1546127
theorem B2931947 : Blo 686314 2931947 := bstep (se 1 (by rfl) ⟨2198960, by rfl⟩ : syracuseStep 2931947 = 4397921) B4397921
theorem B43040155 : Blo 686314 43040155 := bstep (se 1 (by rfl) ⟨32280116, by rfl⟩ : syracuseStep 43040155 = 64560233) B64560233
theorem B1031711 : Blo 686314 1031711 := bstep (se 1 (by rfl) ⟨773783, by rfl⟩ : syracuseStep 1031711 = 1547567) B1547567
theorem B14139161 : Blo 686314 14139161 := bstep (se 2 (by rfl) ⟨5302185, by rfl⟩ : syracuseStep 14139161 = 10604371) B10604371
theorem B3915823 : Blo 686314 3915823 := bstep (se 1 (by rfl) ⟨2936867, by rfl⟩ : syracuseStep 3915823 = 5873735) B5873735
theorem B2933759 : Blo 686314 2933759 := bstep (se 1 (by rfl) ⟨2200319, by rfl⟩ : syracuseStep 2933759 = 4400639) B4400639
theorem B31835177 : Blo 686314 31835177 := bstep (se 2 (by rfl) ⟨11938191, by rfl⟩ : syracuseStep 31835177 = 23876383) B23876383
theorem B1034075 : Blo 686314 1034075 := bstep (se 1 (by rfl) ⟨775556, by rfl⟩ : syracuseStep 1034075 = 1551113) B1551113
theorem B20400277 : Blo 686314 20400277 := bstep (se 6 (by rfl) ⟨478131, by rfl⟩ : syracuseStep 20400277 = 956263) B956263
theorem B1034921 : Blo 686314 1034921 := bstep (se 2 (by rfl) ⟨388095, by rfl⟩ : syracuseStep 1034921 = 776191) B776191
theorem B306110015 : Blo 686314 306110015 := bstep (se 1 (by rfl) ⟨229582511, by rfl⟩ : syracuseStep 306110015 = 459165023) B459165023
theorem B2319839 : Blo 686314 2319839 := bstep (se 1 (by rfl) ⟨1739879, by rfl⟩ : syracuseStep 2319839 = 3479759) B3479759
theorem B1467887 : Blo 686314 1467887 := bstep (se 1 (by rfl) ⟨1100915, by rfl⟩ : syracuseStep 1467887 = 2201831) B2201831
theorem B4189943 : Blo 686314 4189943 := bstep (se 1 (by rfl) ⟨3142457, by rfl⟩ : syracuseStep 4189943 = 6284915) B6284915
theorem B1964063 : Blo 686314 1964063 := bstep (se 1 (by rfl) ⟨1473047, by rfl⟩ : syracuseStep 1964063 = 2946095) B2946095
theorem B687647 : Blo 686314 687647 := bstep (se 1 (by rfl) ⟨515735, by rfl⟩ : syracuseStep 687647 = 1031471) B1031471
theorem B689383 : Blo 686314 689383 := bstep (se 1 (by rfl) ⟨517037, by rfl⟩ : syracuseStep 689383 = 1034075) B1034075
theorem B689947 : Blo 686314 689947 := bstep (se 1 (by rfl) ⟨517460, by rfl⟩ : syracuseStep 689947 = 1034921) B1034921
theorem B7833833 : Blo 686314 7833833 := bstep (se 2 (by rfl) ⟨2937687, by rfl⟩ : syracuseStep 7833833 = 5875375) B5875375
theorem B27200369 : Blo 686314 27200369 := bstep (se 2 (by rfl) ⟨10200138, by rfl⟩ : syracuseStep 27200369 = 20400277) B20400277
theorem B1546559 : Blo 686314 1546559 := bstep (se 1 (by rfl) ⟨1159919, by rfl⟩ : syracuseStep 1546559 = 2319839) B2319839
theorem B2793295 : Blo 686314 2793295 := bstep (se 1 (by rfl) ⟨2094971, by rfl⟩ : syracuseStep 2793295 = 4189943) B4189943
theorem B57386873 : Blo 686314 57386873 := bstep (se 2 (by rfl) ⟨21520077, by rfl⟩ : syracuseStep 57386873 = 43040155) B43040155
theorem B5221097 : Blo 686314 5221097 := bstep (se 2 (by rfl) ⟨1957911, by rfl⟩ : syracuseStep 5221097 = 3915823) B3915823
theorem B1553039 : Blo 686314 1553039 := bstep (se 1 (by rfl) ⟨1164779, by rfl⟩ : syracuseStep 1553039 = 2329559) B2329559
theorem B3914365 : Blo 686314 3914365 := bstep (se 3 (by rfl) ⟨733943, by rfl⟩ : syracuseStep 3914365 = 1467887) B1467887
theorem B7454015 : Blo 686314 7454015 := bstep (se 1 (by rfl) ⟨5590511, by rfl⟩ : syracuseStep 7454015 = 11181023) B11181023
theorem B1033319 : Blo 686314 1033319 := bstep (se 1 (by rfl) ⟨774989, by rfl⟩ : syracuseStep 1033319 = 1549979) B1549979
theorem B1033727 : Blo 686314 1033727 := bstep (se 1 (by rfl) ⟨775295, by rfl⟩ : syracuseStep 1033727 = 1550591) B1550591
theorem B3393947 : Blo 686314 3393947 := bstep (se 1 (by rfl) ⟨2545460, by rfl⟩ : syracuseStep 3393947 = 5090921) B5090921
theorem B772735 : Blo 686314 772735 := bstep (se 1 (by rfl) ⟨579551, by rfl⟩ : syracuseStep 772735 = 1159103) B1159103
theorem B10735699 : Blo 686314 10735699 := bstep (se 1 (by rfl) ⟨8051774, by rfl⟩ : syracuseStep 10735699 = 16103549) B16103549
theorem B1954631 : Blo 686314 1954631 := bstep (se 1 (by rfl) ⟨1465973, by rfl⟩ : syracuseStep 1954631 = 2931947) B2931947
theorem B9426107 : Blo 686314 9426107 := bstep (se 1 (by rfl) ⟨7069580, by rfl⟩ : syracuseStep 9426107 = 14139161) B14139161
theorem B1955839 : Blo 686314 1955839 := bstep (se 1 (by rfl) ⟨1466879, by rfl⟩ : syracuseStep 1955839 = 2933759) B2933759
theorem B21223451 : Blo 686314 21223451 := bstep (se 1 (by rfl) ⟨15917588, by rfl⟩ : syracuseStep 21223451 = 31835177) B31835177
theorem B5595965 : Blo 686314 5595965 := bstep (se 3 (by rfl) ⟨1049243, by rfl⟩ : syracuseStep 5595965 = 2098487) B2098487
theorem B204073343 : Blo 686314 204073343 := bstep (se 1 (by rfl) ⟨153055007, by rfl⟩ : syracuseStep 204073343 = 306110015) B306110015
theorem B2322431 : Blo 686314 2322431 := bstep (se 1 (by rfl) ⟨1741823, by rfl⟩ : syracuseStep 2322431 = 3483647) B3483647
theorem B2324591 : Blo 686314 2324591 := bstep (se 1 (by rfl) ⟨1743443, by rfl⟩ : syracuseStep 2324591 = 3486887) B3486887
theorem B686363 : Blo 686314 686363 := bstep (se 1 (by rfl) ⟨514772, by rfl⟩ : syracuseStep 686363 = 1029545) B1029545
theorem B686591 : Blo 686314 686591 := bstep (se 1 (by rfl) ⟨514943, by rfl⟩ : syracuseStep 686591 = 1029887) B1029887
theorem B1309375 : Blo 686314 1309375 := bstep (se 1 (by rfl) ⟨982031, by rfl⟩ : syracuseStep 1309375 = 1964063) B1964063
theorem B687167 : Blo 686314 687167 := bstep (se 1 (by rfl) ⟨515375, by rfl⟩ : syracuseStep 687167 = 1030751) B1030751
theorem B687807 : Blo 686314 687807 := bstep (se 1 (by rfl) ⟨515855, by rfl⟩ : syracuseStep 687807 = 1031711) B1031711
theorem B688879 : Blo 686314 688879 := bstep (se 1 (by rfl) ⟨516659, by rfl⟩ : syracuseStep 688879 = 1033319) B1033319
theorem B689151 : Blo 686314 689151 := bstep (se 1 (by rfl) ⟨516863, by rfl⟩ : syracuseStep 689151 = 1033727) B1033727
theorem B5212349 : Blo 686314 5212349 := bstep (se 3 (by rfl) ⟨977315, by rfl⟩ : syracuseStep 5212349 = 1954631) B1954631
theorem B9050525 : Blo 686314 9050525 := bstep (se 3 (by rfl) ⟨1696973, by rfl⟩ : syracuseStep 9050525 = 3393947) B3393947
theorem B3480731 : Blo 686314 3480731 := bstep (se 1 (by rfl) ⟨2610548, by rfl⟩ : syracuseStep 3480731 = 5221097) B5221097
theorem B1548287 : Blo 686314 1548287 := bstep (se 1 (by rfl) ⟨1161215, by rfl⟩ : syracuseStep 1548287 = 2322431) B2322431
theorem B5219153 : Blo 686314 5219153 := bstep (se 2 (by rfl) ⟨1957182, by rfl⟩ : syracuseStep 5219153 = 3914365) B3914365
theorem B1745833 : Blo 686314 1745833 := bstep (se 2 (by rfl) ⟨654687, by rfl⟩ : syracuseStep 1745833 = 1309375) B1309375
theorem B1549727 : Blo 686314 1549727 := bstep (se 1 (by rfl) ⟨1162295, by rfl⟩ : syracuseStep 1549727 = 2324591) B2324591
theorem B5222555 : Blo 686314 5222555 := bstep (se 1 (by rfl) ⟨3916916, by rfl⟩ : syracuseStep 5222555 = 7833833) B7833833
theorem B18133579 : Blo 686314 18133579 := bstep (se 1 (by rfl) ⟨13600184, by rfl⟩ : syracuseStep 18133579 = 27200369) B27200369
theorem B1030313 : Blo 686314 1030313 := bstep (se 2 (by rfl) ⟨386367, by rfl⟩ : syracuseStep 1030313 = 772735) B772735
theorem B1031039 : Blo 686314 1031039 := bstep (se 1 (by rfl) ⟨773279, by rfl⟩ : syracuseStep 1031039 = 1546559) B1546559
theorem B38257915 : Blo 686314 38257915 := bstep (se 1 (by rfl) ⟨28693436, by rfl⟩ : syracuseStep 38257915 = 57386873) B57386873
theorem B2607785 : Blo 686314 2607785 := bstep (se 2 (by rfl) ⟨977919, by rfl⟩ : syracuseStep 2607785 = 1955839) B1955839
theorem B1035359 : Blo 686314 1035359 := bstep (se 1 (by rfl) ⟨776519, by rfl⟩ : syracuseStep 1035359 = 1553039) B1553039
theorem B4969343 : Blo 686314 4969343 := bstep (se 1 (by rfl) ⟨3727007, by rfl⟩ : syracuseStep 4969343 = 7454015) B7454015
theorem B3724393 : Blo 686314 3724393 := bstep (se 2 (by rfl) ⟨1396647, by rfl⟩ : syracuseStep 3724393 = 2793295) B2793295
theorem B6284071 : Blo 686314 6284071 := bstep (se 1 (by rfl) ⟨4713053, by rfl⟩ : syracuseStep 6284071 = 9426107) B9426107
theorem B14148967 : Blo 686314 14148967 := bstep (se 1 (by rfl) ⟨10611725, by rfl⟩ : syracuseStep 14148967 = 21223451) B21223451
theorem B14314265 : Blo 686314 14314265 := bstep (se 2 (by rfl) ⟨5367849, by rfl⟩ : syracuseStep 14314265 = 10735699) B10735699
theorem B3730643 : Blo 686314 3730643 := bstep (se 1 (by rfl) ⟨2797982, by rfl⟩ : syracuseStep 3730643 = 5595965) B5595965
theorem B136048895 : Blo 686314 136048895 := bstep (se 1 (by rfl) ⟨102036671, by rfl⟩ : syracuseStep 136048895 = 204073343) B204073343
theorem B2327777 : Blo 686314 2327777 := bstep (se 2 (by rfl) ⟨872916, by rfl⟩ : syracuseStep 2327777 = 1745833) B1745833
theorem B3474899 : Blo 686314 3474899 := bstep (se 1 (by rfl) ⟨2606174, by rfl⟩ : syracuseStep 3474899 = 5212349) B5212349
theorem B1738523 : Blo 686314 1738523 := bstep (se 1 (by rfl) ⟨1303892, by rfl⟩ : syracuseStep 1738523 = 2607785) B2607785
theorem B690239 : Blo 686314 690239 := bstep (se 1 (by rfl) ⟨517679, by rfl⟩ : syracuseStep 690239 = 1035359) B1035359
theorem B3312895 : Blo 686314 3312895 := bstep (se 1 (by rfl) ⟨2484671, by rfl⟩ : syracuseStep 3312895 = 4969343) B4969343
theorem B6033683 : Blo 686314 6033683 := bstep (se 1 (by rfl) ⟨4525262, by rfl⟩ : syracuseStep 6033683 = 9050525) B9050525
theorem B3479435 : Blo 686314 3479435 := bstep (se 1 (by rfl) ⟨2609576, by rfl⟩ : syracuseStep 3479435 = 5219153) B5219153
theorem B9542843 : Blo 686314 9542843 := bstep (se 1 (by rfl) ⟨7157132, by rfl⟩ : syracuseStep 9542843 = 14314265) B14314265
theorem B3481703 : Blo 686314 3481703 := bstep (se 1 (by rfl) ⟨2611277, by rfl⟩ : syracuseStep 3481703 = 5222555) B5222555
theorem B1032191 : Blo 686314 1032191 := bstep (se 1 (by rfl) ⟨774143, by rfl⟩ : syracuseStep 1032191 = 1548287) B1548287
theorem B1033151 : Blo 686314 1033151 := bstep (se 1 (by rfl) ⟨774863, by rfl⟩ : syracuseStep 1033151 = 1549727) B1549727
theorem B4965857 : Blo 686314 4965857 := bstep (se 2 (by rfl) ⟨1862196, by rfl⟩ : syracuseStep 4965857 = 3724393) B3724393
theorem B51010553 : Blo 686314 51010553 := bstep (se 2 (by rfl) ⟨19128957, by rfl⟩ : syracuseStep 51010553 = 38257915) B38257915
theorem B18865289 : Blo 686314 18865289 := bstep (se 2 (by rfl) ⟨7074483, by rfl⟩ : syracuseStep 18865289 = 14148967) B14148967
theorem B33515045 : Blo 686314 33515045 := bstep (se 4 (by rfl) ⟨3142035, by rfl⟩ : syracuseStep 33515045 = 6284071) B6284071
theorem B2320487 : Blo 686314 2320487 := bstep (se 1 (by rfl) ⟨1740365, by rfl⟩ : syracuseStep 2320487 = 3480731) B3480731
theorem B24178105 : Blo 686314 24178105 := bstep (se 2 (by rfl) ⟨9066789, by rfl⟩ : syracuseStep 24178105 = 18133579) B18133579
theorem B2487095 : Blo 686314 2487095 := bstep (se 1 (by rfl) ⟨1865321, by rfl⟩ : syracuseStep 2487095 = 3730643) B3730643
theorem B90699263 : Blo 686314 90699263 := bstep (se 1 (by rfl) ⟨68024447, by rfl⟩ : syracuseStep 90699263 = 136048895) B136048895
theorem B686875 : Blo 686314 686875 := bstep (se 1 (by rfl) ⟨515156, by rfl⟩ : syracuseStep 686875 = 1030313) B1030313
theorem B687359 : Blo 686314 687359 := bstep (se 1 (by rfl) ⟨515519, by rfl⟩ : syracuseStep 687359 = 1031039) B1031039
theorem B688767 : Blo 686314 688767 := bstep (se 1 (by rfl) ⟨516575, by rfl⟩ : syracuseStep 688767 = 1033151) B1033151
theorem B3310571 : Blo 686314 3310571 := bstep (se 1 (by rfl) ⟨2482928, by rfl⟩ : syracuseStep 3310571 = 4965857) B4965857
theorem B6361895 : Blo 686314 6361895 := bstep (se 1 (by rfl) ⟨4771421, by rfl⟩ : syracuseStep 6361895 = 9542843) B9542843
theorem B1546991 : Blo 686314 1546991 := bstep (se 1 (by rfl) ⟨1160243, by rfl⟩ : syracuseStep 1546991 = 2320487) B2320487
theorem B50307437 : Blo 686314 50307437 := bstep (se 3 (by rfl) ⟨9432644, by rfl⟩ : syracuseStep 50307437 = 18865289) B18865289
theorem B60466175 : Blo 686314 60466175 := bstep (se 1 (by rfl) ⟨45349631, by rfl⟩ : syracuseStep 60466175 = 90699263) B90699263
theorem B1551851 : Blo 686314 1551851 := bstep (se 1 (by rfl) ⟨1163888, by rfl⟩ : syracuseStep 1551851 = 2327777) B2327777
theorem B1159015 : Blo 686314 1159015 := bstep (se 1 (by rfl) ⟨869261, by rfl⟩ : syracuseStep 1159015 = 1738523) B1738523
theorem B1658063 : Blo 686314 1658063 := bstep (se 1 (by rfl) ⟨1243547, by rfl⟩ : syracuseStep 1658063 = 2487095) B2487095
theorem B2316599 : Blo 686314 2316599 := bstep (se 1 (by rfl) ⟨1737449, by rfl⟩ : syracuseStep 2316599 = 3474899) B3474899
theorem B4022455 : Blo 686314 4022455 := bstep (se 1 (by rfl) ⟨3016841, by rfl⟩ : syracuseStep 4022455 = 6033683) B6033683
theorem B2319623 : Blo 686314 2319623 := bstep (se 1 (by rfl) ⟨1739717, by rfl⟩ : syracuseStep 2319623 = 3479435) B3479435
theorem B4417193 : Blo 686314 4417193 := bstep (se 2 (by rfl) ⟨1656447, by rfl⟩ : syracuseStep 4417193 = 3312895) B3312895
theorem B32237473 : Blo 686314 32237473 := bstep (se 2 (by rfl) ⟨12089052, by rfl⟩ : syracuseStep 32237473 = 24178105) B24178105
theorem B34007035 : Blo 686314 34007035 := bstep (se 1 (by rfl) ⟨25505276, by rfl⟩ : syracuseStep 34007035 = 51010553) B51010553
theorem B2321135 : Blo 686314 2321135 := bstep (se 1 (by rfl) ⟨1740851, by rfl⟩ : syracuseStep 2321135 = 3481703) B3481703
theorem B22343363 : Blo 686314 22343363 := bstep (se 1 (by rfl) ⟨16757522, by rfl⟩ : syracuseStep 22343363 = 33515045) B33515045
theorem B688127 : Blo 686314 688127 := bstep (se 1 (by rfl) ⟨516095, by rfl⟩ : syracuseStep 688127 = 1032191) B1032191
theorem B134153165 : Blo 686314 134153165 := bstep (se 3 (by rfl) ⟨25153718, by rfl⟩ : syracuseStep 134153165 = 50307437) B50307437
theorem B1544399 : Blo 686314 1544399 := bstep (se 1 (by rfl) ⟨1158299, by rfl⟩ : syracuseStep 1544399 = 2316599) B2316599
theorem B1545353 : Blo 686314 1545353 := bstep (se 2 (by rfl) ⟨579507, by rfl⟩ : syracuseStep 1545353 = 1159015) B1159015
theorem B40310783 : Blo 686314 40310783 := bstep (se 1 (by rfl) ⟨30233087, by rfl⟩ : syracuseStep 40310783 = 60466175) B60466175
theorem B1546415 : Blo 686314 1546415 := bstep (se 1 (by rfl) ⟨1159811, by rfl⟩ : syracuseStep 1546415 = 2319623) B2319623
theorem B1547423 : Blo 686314 1547423 := bstep (se 1 (by rfl) ⟨1160567, by rfl⟩ : syracuseStep 1547423 = 2321135) B2321135
theorem B8828189 : Blo 686314 8828189 := bstep (se 3 (by rfl) ⟨1655285, by rfl⟩ : syracuseStep 8828189 = 3310571) B3310571
theorem B4241263 : Blo 686314 4241263 := bstep (se 1 (by rfl) ⟨3180947, by rfl⟩ : syracuseStep 4241263 = 6361895) B6361895
theorem B11779181 : Blo 686314 11779181 := bstep (se 3 (by rfl) ⟨2208596, by rfl⟩ : syracuseStep 11779181 = 4417193) B4417193
theorem B1031327 : Blo 686314 1031327 := bstep (se 1 (by rfl) ⟨773495, by rfl⟩ : syracuseStep 1031327 = 1546991) B1546991
theorem B1034567 : Blo 686314 1034567 := bstep (se 1 (by rfl) ⟨775925, by rfl⟩ : syracuseStep 1034567 = 1551851) B1551851
theorem B14895575 : Blo 686314 14895575 := bstep (se 1 (by rfl) ⟨11171681, by rfl⟩ : syracuseStep 14895575 = 22343363) B22343363
theorem B5363273 : Blo 686314 5363273 := bstep (se 2 (by rfl) ⟨2011227, by rfl⟩ : syracuseStep 5363273 = 4022455) B4022455
theorem B1105375 : Blo 686314 1105375 := bstep (se 1 (by rfl) ⟨829031, by rfl⟩ : syracuseStep 1105375 = 1658063) B1658063
theorem B42983297 : Blo 686314 42983297 := bstep (se 2 (by rfl) ⟨16118736, by rfl⟩ : syracuseStep 42983297 = 32237473) B32237473
theorem B45342713 : Blo 686314 45342713 := bstep (se 2 (by rfl) ⟨17003517, by rfl⟩ : syracuseStep 45342713 = 34007035) B34007035
theorem B689711 : Blo 686314 689711 := bstep (se 1 (by rfl) ⟨517283, by rfl⟩ : syracuseStep 689711 = 1034567) B1034567
theorem B9930383 : Blo 686314 9930383 := bstep (se 1 (by rfl) ⟨7447787, by rfl⟩ : syracuseStep 9930383 = 14895575) B14895575
theorem B3575515 : Blo 686314 3575515 := bstep (se 1 (by rfl) ⟨2681636, by rfl⟩ : syracuseStep 3575515 = 5363273) B5363273
theorem B26873855 : Blo 686314 26873855 := bstep (se 1 (by rfl) ⟨20155391, by rfl⟩ : syracuseStep 26873855 = 40310783) B40310783
theorem B89435443 : Blo 686314 89435443 := bstep (se 1 (by rfl) ⟨67076582, by rfl⟩ : syracuseStep 89435443 = 134153165) B134153165
theorem B1029599 : Blo 686314 1029599 := bstep (se 1 (by rfl) ⟨772199, by rfl⟩ : syracuseStep 1029599 = 1544399) B1544399
theorem B1030235 : Blo 686314 1030235 := bstep (se 1 (by rfl) ⟨772676, by rfl⟩ : syracuseStep 1030235 = 1545353) B1545353
theorem B1030943 : Blo 686314 1030943 := bstep (se 1 (by rfl) ⟨773207, by rfl⟩ : syracuseStep 1030943 = 1546415) B1546415
theorem B1031615 : Blo 686314 1031615 := bstep (se 1 (by rfl) ⟨773711, by rfl⟩ : syracuseStep 1031615 = 1547423) B1547423
theorem B28655531 : Blo 686314 28655531 := bstep (se 1 (by rfl) ⟨21491648, by rfl⟩ : syracuseStep 28655531 = 42983297) B42983297
theorem B30228475 : Blo 686314 30228475 := bstep (se 1 (by rfl) ⟨22671356, by rfl⟩ : syracuseStep 30228475 = 45342713) B45342713
theorem B5655017 : Blo 686314 5655017 := bstep (se 2 (by rfl) ⟨2120631, by rfl⟩ : syracuseStep 5655017 = 4241263) B4241263
theorem B5885459 : Blo 686314 5885459 := bstep (se 1 (by rfl) ⟨4414094, by rfl⟩ : syracuseStep 5885459 = 8828189) B8828189
theorem B7852787 : Blo 686314 7852787 := bstep (se 1 (by rfl) ⟨5889590, by rfl⟩ : syracuseStep 7852787 = 11779181) B11779181
theorem B1473833 : Blo 686314 1473833 := bstep (se 2 (by rfl) ⟨552687, by rfl⟩ : syracuseStep 1473833 = 1105375) B1105375
theorem B687551 : Blo 686314 687551 := bstep (se 1 (by rfl) ⟨515663, by rfl⟩ : syracuseStep 687551 = 1031327) B1031327
theorem B6620255 : Blo 686314 6620255 := bstep (se 1 (by rfl) ⟨4965191, by rfl⟩ : syracuseStep 6620255 = 9930383) B9930383
theorem B3770011 : Blo 686314 3770011 := bstep (se 1 (by rfl) ⟨2827508, by rfl⟩ : syracuseStep 3770011 = 5655017) B5655017
theorem B119247257 : Blo 686314 119247257 := bstep (se 2 (by rfl) ⟨44717721, by rfl⟩ : syracuseStep 119247257 = 89435443) B89435443
theorem B4767353 : Blo 686314 4767353 := bstep (se 2 (by rfl) ⟨1787757, by rfl⟩ : syracuseStep 4767353 = 3575515) B3575515
theorem B3923639 : Blo 686314 3923639 := bstep (se 1 (by rfl) ⟨2942729, by rfl⟩ : syracuseStep 3923639 = 5885459) B5885459
theorem B17915903 : Blo 686314 17915903 := bstep (se 1 (by rfl) ⟨13436927, by rfl⟩ : syracuseStep 17915903 = 26873855) B26873855
theorem B5235191 : Blo 686314 5235191 := bstep (se 1 (by rfl) ⟨3926393, by rfl⟩ : syracuseStep 5235191 = 7852787) B7852787
theorem B3930221 : Blo 686314 3930221 := bstep (se 3 (by rfl) ⟨736916, by rfl⟩ : syracuseStep 3930221 = 1473833) B1473833
theorem B686399 : Blo 686314 686399 := bstep (se 1 (by rfl) ⟨514799, by rfl⟩ : syracuseStep 686399 = 1029599) B1029599
theorem B686823 : Blo 686314 686823 := bstep (se 1 (by rfl) ⟨515117, by rfl⟩ : syracuseStep 686823 = 1030235) B1030235
theorem B687295 : Blo 686314 687295 := bstep (se 1 (by rfl) ⟨515471, by rfl⟩ : syracuseStep 687295 = 1030943) B1030943
theorem B687743 : Blo 686314 687743 := bstep (se 1 (by rfl) ⟨515807, by rfl⟩ : syracuseStep 687743 = 1031615) B1031615
theorem B19103687 : Blo 686314 19103687 := bstep (se 1 (by rfl) ⟨14327765, by rfl⟩ : syracuseStep 19103687 = 28655531) B28655531
theorem B40304633 : Blo 686314 40304633 := bstep (se 2 (by rfl) ⟨15114237, by rfl⟩ : syracuseStep 40304633 = 30228475) B30228475
theorem B79498171 : Blo 686314 79498171 := bstep (se 1 (by rfl) ⟨59623628, by rfl⟩ : syracuseStep 79498171 = 119247257) B119247257
theorem B5026681 : Blo 686314 5026681 := bstep (se 2 (by rfl) ⟨1885005, by rfl⟩ : syracuseStep 5026681 = 3770011) B3770011
theorem B11943935 : Blo 686314 11943935 := bstep (se 1 (by rfl) ⟨8957951, by rfl⟩ : syracuseStep 11943935 = 17915903) B17915903
theorem B3490127 : Blo 686314 3490127 := bstep (se 1 (by rfl) ⟨2617595, by rfl⟩ : syracuseStep 3490127 = 5235191) B5235191
theorem B12735791 : Blo 686314 12735791 := bstep (se 1 (by rfl) ⟨9551843, by rfl⟩ : syracuseStep 12735791 = 19103687) B19103687
theorem B4413503 : Blo 686314 4413503 := bstep (se 1 (by rfl) ⟨3310127, by rfl⟩ : syracuseStep 4413503 = 6620255) B6620255
theorem B2615759 : Blo 686314 2615759 := bstep (se 1 (by rfl) ⟨1961819, by rfl⟩ : syracuseStep 2615759 = 3923639) B3923639
theorem B2620147 : Blo 686314 2620147 := bstep (se 1 (by rfl) ⟨1965110, by rfl⟩ : syracuseStep 2620147 = 3930221) B3930221
theorem B3178235 : Blo 686314 3178235 := bstep (se 1 (by rfl) ⟨2383676, by rfl⟩ : syracuseStep 3178235 = 4767353) B4767353
theorem B107479021 : Blo 686314 107479021 := bstep (se 3 (by rfl) ⟨20152316, by rfl⟩ : syracuseStep 107479021 = 40304633) B40304633
theorem B2326751 : Blo 686314 2326751 := bstep (se 1 (by rfl) ⟨1745063, by rfl⟩ : syracuseStep 2326751 = 3490127) B3490127
theorem B8490527 : Blo 686314 8490527 := bstep (se 1 (by rfl) ⟨6367895, by rfl⟩ : syracuseStep 8490527 = 12735791) B12735791
theorem B26808965 : Blo 686314 26808965 := bstep (se 4 (by rfl) ⟨2513340, by rfl⟩ : syracuseStep 26808965 = 5026681) B5026681
theorem B1743839 : Blo 686314 1743839 := bstep (se 1 (by rfl) ⟨1307879, by rfl⟩ : syracuseStep 1743839 = 2615759) B2615759
theorem B143305361 : Blo 686314 143305361 := bstep (se 2 (by rfl) ⟨53739510, by rfl⟩ : syracuseStep 143305361 = 107479021) B107479021
theorem B7962623 : Blo 686314 7962623 := bstep (se 1 (by rfl) ⟨5971967, by rfl⟩ : syracuseStep 7962623 = 11943935) B11943935
theorem B3493529 : Blo 686314 3493529 := bstep (se 2 (by rfl) ⟨1310073, by rfl⟩ : syracuseStep 3493529 = 2620147) B2620147
theorem B8475293 : Blo 686314 8475293 := bstep (se 3 (by rfl) ⟨1589117, by rfl⟩ : syracuseStep 8475293 = 3178235) B3178235
theorem B105997561 : Blo 686314 105997561 := bstep (se 2 (by rfl) ⟨39749085, by rfl⟩ : syracuseStep 105997561 = 79498171) B79498171
theorem B2942335 : Blo 686314 2942335 := bstep (se 1 (by rfl) ⟨2206751, by rfl⟩ : syracuseStep 2942335 = 4413503) B4413503
theorem B5308415 : Blo 686314 5308415 := bstep (se 1 (by rfl) ⟨3981311, by rfl⟩ : syracuseStep 5308415 = 7962623) B7962623
theorem B2329019 : Blo 686314 2329019 := bstep (se 1 (by rfl) ⟨1746764, by rfl⟩ : syracuseStep 2329019 = 3493529) B3493529
theorem B565320325 : Blo 686314 565320325 := bstep (se 4 (by rfl) ⟨52998780, by rfl⟩ : syracuseStep 565320325 = 105997561) B105997561
theorem B1551167 : Blo 686314 1551167 := bstep (se 1 (by rfl) ⟨1163375, by rfl⟩ : syracuseStep 1551167 = 2326751) B2326751
theorem B17872643 : Blo 686314 17872643 := bstep (se 1 (by rfl) ⟨13404482, by rfl⟩ : syracuseStep 17872643 = 26808965) B26808965
theorem B5650195 : Blo 686314 5650195 := bstep (se 1 (by rfl) ⟨4237646, by rfl⟩ : syracuseStep 5650195 = 8475293) B8475293
theorem B1162559 : Blo 686314 1162559 := bstep (se 1 (by rfl) ⟨871919, by rfl⟩ : syracuseStep 1162559 = 1743839) B1743839
theorem B95536907 : Blo 686314 95536907 := bstep (se 1 (by rfl) ⟨71652680, by rfl⟩ : syracuseStep 95536907 = 143305361) B143305361
theorem B3923113 : Blo 686314 3923113 := bstep (se 2 (by rfl) ⟨1471167, by rfl⟩ : syracuseStep 3923113 = 2942335) B2942335
theorem B5660351 : Blo 686314 5660351 := bstep (se 1 (by rfl) ⟨4245263, by rfl⟩ : syracuseStep 5660351 = 8490527) B8490527
theorem B3773567 : Blo 686314 3773567 := bstep (se 1 (by rfl) ⟨2830175, by rfl⟩ : syracuseStep 3773567 = 5660351) B5660351
theorem B3538943 : Blo 686314 3538943 := bstep (se 1 (by rfl) ⟨2654207, by rfl⟩ : syracuseStep 3538943 = 5308415) B5308415
theorem B1552679 : Blo 686314 1552679 := bstep (se 1 (by rfl) ⟨1164509, by rfl⟩ : syracuseStep 1552679 = 2329019) B2329019
theorem B1034111 : Blo 686314 1034111 := bstep (se 1 (by rfl) ⟨775583, by rfl⟩ : syracuseStep 1034111 = 1551167) B1551167
theorem B11915095 : Blo 686314 11915095 := bstep (se 1 (by rfl) ⟨8936321, by rfl⟩ : syracuseStep 11915095 = 17872643) B17872643
theorem B5230817 : Blo 686314 5230817 := bstep (se 2 (by rfl) ⟨1961556, by rfl⟩ : syracuseStep 5230817 = 3923113) B3923113
theorem B775039 : Blo 686314 775039 := bstep (se 1 (by rfl) ⟨581279, by rfl⟩ : syracuseStep 775039 = 1162559) B1162559
theorem B63691271 : Blo 686314 63691271 := bstep (se 1 (by rfl) ⟨47768453, by rfl⟩ : syracuseStep 63691271 = 95536907) B95536907
theorem B7533593 : Blo 686314 7533593 := bstep (se 2 (by rfl) ⟨2825097, by rfl⟩ : syracuseStep 7533593 = 5650195) B5650195
theorem B753760433 : Blo 686314 753760433 := bstep (se 2 (by rfl) ⟨282660162, by rfl⟩ : syracuseStep 753760433 = 565320325) B565320325
theorem B689407 : Blo 686314 689407 := bstep (se 1 (by rfl) ⟨517055, by rfl⟩ : syracuseStep 689407 = 1034111) B1034111
theorem B2359295 : Blo 686314 2359295 := bstep (se 1 (by rfl) ⟨1769471, by rfl⟩ : syracuseStep 2359295 = 3538943) B3538943
theorem B5022395 : Blo 686314 5022395 := bstep (se 1 (by rfl) ⟨3766796, by rfl⟩ : syracuseStep 5022395 = 7533593) B7533593
theorem B502506955 : Blo 686314 502506955 := bstep (se 1 (by rfl) ⟨376880216, by rfl⟩ : syracuseStep 502506955 = 753760433) B753760433
theorem B3487211 : Blo 686314 3487211 := bstep (se 1 (by rfl) ⟨2615408, by rfl⟩ : syracuseStep 3487211 = 5230817) B5230817
theorem B1033385 : Blo 686314 1033385 := bstep (se 2 (by rfl) ⟨387519, by rfl⟩ : syracuseStep 1033385 = 775039) B775039
theorem B1035119 : Blo 686314 1035119 := bstep (se 1 (by rfl) ⟨776339, by rfl⟩ : syracuseStep 1035119 = 1552679) B1552679
theorem B2515711 : Blo 686314 2515711 := bstep (se 1 (by rfl) ⟨1886783, by rfl⟩ : syracuseStep 2515711 = 3773567) B3773567
theorem B42460847 : Blo 686314 42460847 := bstep (se 1 (by rfl) ⟨31845635, by rfl⟩ : syracuseStep 42460847 = 63691271) B63691271
theorem B15886793 : Blo 686314 15886793 := bstep (se 2 (by rfl) ⟨5957547, by rfl⟩ : syracuseStep 15886793 = 11915095) B11915095
theorem B688923 : Blo 686314 688923 := bstep (se 1 (by rfl) ⟨516692, by rfl⟩ : syracuseStep 688923 = 1033385) B1033385
theorem B690079 : Blo 686314 690079 := bstep (se 1 (by rfl) ⟨517559, by rfl⟩ : syracuseStep 690079 = 1035119) B1035119
theorem B3348263 : Blo 686314 3348263 := bstep (se 1 (by rfl) ⟨2511197, by rfl⟩ : syracuseStep 3348263 = 5022395) B5022395
theorem B10591195 : Blo 686314 10591195 := bstep (se 1 (by rfl) ⟨7943396, by rfl⟩ : syracuseStep 10591195 = 15886793) B15886793
theorem B2680037093 : Blo 686314 2680037093 := bstep (se 4 (by rfl) ⟨251253477, by rfl⟩ : syracuseStep 2680037093 = 502506955) B502506955
theorem B3354281 : Blo 686314 3354281 := bstep (se 2 (by rfl) ⟨1257855, by rfl⟩ : syracuseStep 3354281 = 2515711) B2515711
theorem B1572863 : Blo 686314 1572863 := bstep (se 1 (by rfl) ⟨1179647, by rfl⟩ : syracuseStep 1572863 = 2359295) B2359295
theorem B28307231 : Blo 686314 28307231 := bstep (se 1 (by rfl) ⟨21230423, by rfl⟩ : syracuseStep 28307231 = 42460847) B42460847
theorem B2324807 : Blo 686314 2324807 := bstep (se 1 (by rfl) ⟨1743605, by rfl⟩ : syracuseStep 2324807 = 3487211) B3487211
theorem B2236187 : Blo 686314 2236187 := bstep (se 1 (by rfl) ⟨1677140, by rfl⟩ : syracuseStep 2236187 = 3354281) B3354281
theorem B1549871 : Blo 686314 1549871 := bstep (se 1 (by rfl) ⟨1162403, by rfl⟩ : syracuseStep 1549871 = 2324807) B2324807
theorem B8928701 : Blo 686314 8928701 := bstep (se 3 (by rfl) ⟨1674131, by rfl⟩ : syracuseStep 8928701 = 3348263) B3348263
theorem B1786691395 : Blo 686314 1786691395 := bstep (se 1 (by rfl) ⟨1340018546, by rfl⟩ : syracuseStep 1786691395 = 2680037093) B2680037093
theorem B18871487 : Blo 686314 18871487 := bstep (se 1 (by rfl) ⟨14153615, by rfl⟩ : syracuseStep 18871487 = 28307231) B28307231
theorem B14121593 : Blo 686314 14121593 := bstep (se 2 (by rfl) ⟨5295597, by rfl⟩ : syracuseStep 14121593 = 10591195) B10591195
theorem B4194301 : Blo 686314 4194301 := bstep (se 3 (by rfl) ⟨786431, by rfl⟩ : syracuseStep 4194301 = 1572863) B1572863
theorem B9414395 : Blo 686314 9414395 := bstep (se 1 (by rfl) ⟨7060796, by rfl⟩ : syracuseStep 9414395 = 14121593) B14121593
theorem B1033247 : Blo 686314 1033247 := bstep (se 1 (by rfl) ⟨774935, by rfl⟩ : syracuseStep 1033247 = 1549871) B1549871
theorem B5952467 : Blo 686314 5952467 := bstep (se 1 (by rfl) ⟨4464350, by rfl⟩ : syracuseStep 5952467 = 8928701) B8928701
theorem B2382255193 : Blo 686314 2382255193 := bstep (se 2 (by rfl) ⟨893345697, by rfl⟩ : syracuseStep 2382255193 = 1786691395) B1786691395
theorem B5592401 : Blo 686314 5592401 := bstep (se 2 (by rfl) ⟨2097150, by rfl⟩ : syracuseStep 5592401 = 4194301) B4194301
theorem B12580991 : Blo 686314 12580991 := bstep (se 1 (by rfl) ⟨9435743, by rfl⟩ : syracuseStep 12580991 = 18871487) B18871487
theorem B5963165 : Blo 686314 5963165 := bstep (se 3 (by rfl) ⟨1118093, by rfl⟩ : syracuseStep 5963165 = 2236187) B2236187
theorem B688831 : Blo 686314 688831 := bstep (se 1 (by rfl) ⟨516623, by rfl⟩ : syracuseStep 688831 = 1033247) B1033247
theorem B3968311 : Blo 686314 3968311 := bstep (se 1 (by rfl) ⟨2976233, by rfl⟩ : syracuseStep 3968311 = 5952467) B5952467
theorem B3176340257 : Blo 686314 3176340257 := bstep (se 2 (by rfl) ⟨1191127596, by rfl⟩ : syracuseStep 3176340257 = 2382255193) B2382255193
theorem B3975443 : Blo 686314 3975443 := bstep (se 1 (by rfl) ⟨2981582, by rfl⟩ : syracuseStep 3975443 = 5963165) B5963165
theorem B6276263 : Blo 686314 6276263 := bstep (se 1 (by rfl) ⟨4707197, by rfl⟩ : syracuseStep 6276263 = 9414395) B9414395
theorem B3728267 : Blo 686314 3728267 := bstep (se 1 (by rfl) ⟨2796200, by rfl⟩ : syracuseStep 3728267 = 5592401) B5592401
theorem B8387327 : Blo 686314 8387327 := bstep (se 1 (by rfl) ⟨6290495, by rfl⟩ : syracuseStep 8387327 = 12580991) B12580991
theorem B5291081 : Blo 686314 5291081 := bstep (se 2 (by rfl) ⟨1984155, by rfl⟩ : syracuseStep 5291081 = 3968311) B3968311
theorem B5591551 : Blo 686314 5591551 := bstep (se 1 (by rfl) ⟨4193663, by rfl⟩ : syracuseStep 5591551 = 8387327) B8387327
theorem B16736701 : Blo 686314 16736701 := bstep (se 3 (by rfl) ⟨3138131, by rfl⟩ : syracuseStep 16736701 = 6276263) B6276263
theorem B2117560171 : Blo 686314 2117560171 := bstep (se 1 (by rfl) ⟨1588170128, by rfl⟩ : syracuseStep 2117560171 = 3176340257) B3176340257
theorem B2485511 : Blo 686314 2485511 := bstep (se 1 (by rfl) ⟨1864133, by rfl⟩ : syracuseStep 2485511 = 3728267) B3728267
theorem B2650295 : Blo 686314 2650295 := bstep (se 1 (by rfl) ⟨1987721, by rfl⟩ : syracuseStep 2650295 = 3975443) B3975443
theorem B22315601 : Blo 686314 22315601 := bstep (se 2 (by rfl) ⟨8368350, by rfl⟩ : syracuseStep 22315601 = 16736701) B16736701
theorem B7455401 : Blo 686314 7455401 := bstep (se 2 (by rfl) ⟨2795775, by rfl⟩ : syracuseStep 7455401 = 5591551) B5591551
theorem B1657007 : Blo 686314 1657007 := bstep (se 1 (by rfl) ⟨1242755, by rfl⟩ : syracuseStep 1657007 = 2485511) B2485511
theorem B3527387 : Blo 686314 3527387 := bstep (se 1 (by rfl) ⟨2645540, by rfl⟩ : syracuseStep 3527387 = 5291081) B5291081
theorem B2823413561 : Blo 686314 2823413561 := bstep (se 2 (by rfl) ⟨1058780085, by rfl⟩ : syracuseStep 2823413561 = 2117560171) B2117560171
theorem B1766863 : Blo 686314 1766863 := bstep (se 1 (by rfl) ⟨1325147, by rfl⟩ : syracuseStep 1766863 = 2650295) B2650295
theorem B14877067 : Blo 686314 14877067 := bstep (se 1 (by rfl) ⟨11157800, by rfl⟩ : syracuseStep 14877067 = 22315601) B22315601
theorem B1882275707 : Blo 686314 1882275707 := bstep (se 1 (by rfl) ⟨1411706780, by rfl⟩ : syracuseStep 1882275707 = 2823413561) B2823413561
theorem B4970267 : Blo 686314 4970267 := bstep (se 1 (by rfl) ⟨3727700, by rfl⟩ : syracuseStep 4970267 = 7455401) B7455401
theorem B1104671 : Blo 686314 1104671 := bstep (se 1 (by rfl) ⟨828503, by rfl⟩ : syracuseStep 1104671 = 1657007) B1657007
theorem B2351591 : Blo 686314 2351591 := bstep (se 1 (by rfl) ⟨1763693, by rfl⟩ : syracuseStep 2351591 = 3527387) B3527387
theorem B2355817 : Blo 686314 2355817 := bstep (se 2 (by rfl) ⟨883431, by rfl⟩ : syracuseStep 2355817 = 1766863) B1766863
theorem B3313511 : Blo 686314 3313511 := bstep (se 1 (by rfl) ⟨2485133, by rfl⟩ : syracuseStep 3313511 = 4970267) B4970267
theorem B19836089 : Blo 686314 19836089 := bstep (se 2 (by rfl) ⟨7438533, by rfl⟩ : syracuseStep 19836089 = 14877067) B14877067
theorem B736447 : Blo 686314 736447 := bstep (se 1 (by rfl) ⟨552335, by rfl⟩ : syracuseStep 736447 = 1104671) B1104671
theorem B1567727 : Blo 686314 1567727 := bstep (se 1 (by rfl) ⟨1175795, by rfl⟩ : syracuseStep 1567727 = 2351591) B2351591
theorem B3141089 : Blo 686314 3141089 := bstep (se 2 (by rfl) ⟨1177908, by rfl⟩ : syracuseStep 3141089 = 2355817) B2355817
theorem B1254850471 : Blo 686314 1254850471 := bstep (se 1 (by rfl) ⟨941137853, by rfl⟩ : syracuseStep 1254850471 = 1882275707) B1882275707
theorem B2209007 : Blo 686314 2209007 := bstep (se 1 (by rfl) ⟨1656755, by rfl⟩ : syracuseStep 2209007 = 3313511) B3313511
theorem B13224059 : Blo 686314 13224059 := bstep (se 1 (by rfl) ⟨9918044, by rfl⟩ : syracuseStep 13224059 = 19836089) B19836089
theorem B1045151 : Blo 686314 1045151 := bstep (se 1 (by rfl) ⟨783863, by rfl⟩ : syracuseStep 1045151 = 1567727) B1567727
theorem B2094059 : Blo 686314 2094059 := bstep (se 1 (by rfl) ⟨1570544, by rfl⟩ : syracuseStep 2094059 = 3141089) B3141089
theorem B981929 : Blo 686314 981929 := bstep (se 2 (by rfl) ⟨368223, by rfl⟩ : syracuseStep 981929 = 736447) B736447
theorem B6692535845 : Blo 686314 6692535845 := bstep (se 4 (by rfl) ⟨627425235, by rfl⟩ : syracuseStep 6692535845 = 1254850471) B1254850471
theorem B8816039 : Blo 686314 8816039 := bstep (se 1 (by rfl) ⟨6612029, by rfl⟩ : syracuseStep 8816039 = 13224059) B13224059
theorem B696767 : Blo 686314 696767 := bstep (se 1 (by rfl) ⟨522575, by rfl⟩ : syracuseStep 696767 = 1045151) B1045151
theorem B1396039 : Blo 686314 1396039 := bstep (se 1 (by rfl) ⟨1047029, by rfl⟩ : syracuseStep 1396039 = 2094059) B2094059
theorem B2618477 : Blo 686314 2618477 := bstep (se 3 (by rfl) ⟨490964, by rfl⟩ : syracuseStep 2618477 = 981929) B981929
theorem B1472671 : Blo 686314 1472671 := bstep (se 1 (by rfl) ⟨1104503, by rfl⟩ : syracuseStep 1472671 = 2209007) B2209007
theorem B4461690563 : Blo 686314 4461690563 := bstep (se 1 (by rfl) ⟨3346267922, by rfl⟩ : syracuseStep 4461690563 = 6692535845) B6692535845
theorem B1745651 : Blo 686314 1745651 := bstep (se 1 (by rfl) ⟨1309238, by rfl⟩ : syracuseStep 1745651 = 2618477) B2618477
theorem B2974460375 : Blo 686314 2974460375 := bstep (se 1 (by rfl) ⟨2230845281, by rfl⟩ : syracuseStep 2974460375 = 4461690563) B4461690563
theorem B5877359 : Blo 686314 5877359 := bstep (se 1 (by rfl) ⟨4408019, by rfl⟩ : syracuseStep 5877359 = 8816039) B8816039
theorem B7854245 : Blo 686314 7854245 := bstep (se 4 (by rfl) ⟨736335, by rfl⟩ : syracuseStep 7854245 = 1472671) B1472671
theorem B1858045 : Blo 686314 1858045 := bstep (se 3 (by rfl) ⟨348383, by rfl⟩ : syracuseStep 1858045 = 696767) B696767
theorem B1861385 : Blo 686314 1861385 := bstep (se 2 (by rfl) ⟨698019, by rfl⟩ : syracuseStep 1861385 = 1396039) B1396039
theorem B4963693 : Blo 686314 4963693 := bstep (se 3 (by rfl) ⟨930692, by rfl⟩ : syracuseStep 4963693 = 1861385) B1861385
theorem B1163767 : Blo 686314 1163767 := bstep (se 1 (by rfl) ⟨872825, by rfl⟩ : syracuseStep 1163767 = 1745651) B1745651
theorem B1982973583 : Blo 686314 1982973583 := bstep (se 1 (by rfl) ⟨1487230187, by rfl⟩ : syracuseStep 1982973583 = 2974460375) B2974460375
theorem B3918239 : Blo 686314 3918239 := bstep (se 1 (by rfl) ⟨2938679, by rfl⟩ : syracuseStep 3918239 = 5877359) B5877359
theorem B2477393 : Blo 686314 2477393 := bstep (se 2 (by rfl) ⟨929022, by rfl⟩ : syracuseStep 2477393 = 1858045) B1858045
theorem B5236163 : Blo 686314 5236163 := bstep (se 1 (by rfl) ⟨3927122, by rfl⟩ : syracuseStep 5236163 = 7854245) B7854245
theorem B1551689 : Blo 686314 1551689 := bstep (se 2 (by rfl) ⟨581883, by rfl⟩ : syracuseStep 1551689 = 1163767) B1163767
theorem B2643964777 : Blo 686314 2643964777 := bstep (se 2 (by rfl) ⟨991486791, by rfl⟩ : syracuseStep 2643964777 = 1982973583) B1982973583
theorem B1651595 : Blo 686314 1651595 := bstep (se 1 (by rfl) ⟨1238696, by rfl⟩ : syracuseStep 1651595 = 2477393) B2477393
theorem B3490775 : Blo 686314 3490775 := bstep (se 1 (by rfl) ⟨2618081, by rfl⟩ : syracuseStep 3490775 = 5236163) B5236163
theorem B2612159 : Blo 686314 2612159 := bstep (se 1 (by rfl) ⟨1959119, by rfl⟩ : syracuseStep 2612159 = 3918239) B3918239
theorem B6618257 : Blo 686314 6618257 := bstep (se 2 (by rfl) ⟨2481846, by rfl⟩ : syracuseStep 6618257 = 4963693) B4963693
theorem B2327183 : Blo 686314 2327183 := bstep (se 1 (by rfl) ⟨1745387, by rfl⟩ : syracuseStep 2327183 = 3490775) B3490775
theorem B1741439 : Blo 686314 1741439 := bstep (se 1 (by rfl) ⟨1306079, by rfl⟩ : syracuseStep 1741439 = 2612159) B2612159
theorem B3525286369 : Blo 686314 3525286369 := bstep (se 2 (by rfl) ⟨1321982388, by rfl⟩ : syracuseStep 3525286369 = 2643964777) B2643964777
theorem B4404253 : Blo 686314 4404253 := bstep (se 3 (by rfl) ⟨825797, by rfl⟩ : syracuseStep 4404253 = 1651595) B1651595
theorem B1034459 : Blo 686314 1034459 := bstep (se 1 (by rfl) ⟨775844, by rfl⟩ : syracuseStep 1034459 = 1551689) B1551689
theorem B4412171 : Blo 686314 4412171 := bstep (se 1 (by rfl) ⟨3309128, by rfl⟩ : syracuseStep 4412171 = 6618257) B6618257
theorem B689639 : Blo 686314 689639 := bstep (se 1 (by rfl) ⟨517229, by rfl⟩ : syracuseStep 689639 = 1034459) B1034459
theorem B5872337 : Blo 686314 5872337 := bstep (se 2 (by rfl) ⟨2202126, by rfl⟩ : syracuseStep 5872337 = 4404253) B4404253
theorem B4700381825 : Blo 686314 4700381825 := bstep (se 2 (by rfl) ⟨1762643184, by rfl⟩ : syracuseStep 4700381825 = 3525286369) B3525286369
theorem B1551455 : Blo 686314 1551455 := bstep (se 1 (by rfl) ⟨1163591, by rfl⟩ : syracuseStep 1551455 = 2327183) B2327183
theorem B1160959 : Blo 686314 1160959 := bstep (se 1 (by rfl) ⟨870719, by rfl⟩ : syracuseStep 1160959 = 1741439) B1741439
theorem B2941447 : Blo 686314 2941447 := bstep (se 1 (by rfl) ⟨2206085, by rfl⟩ : syracuseStep 2941447 = 4412171) B4412171
theorem B1547945 : Blo 686314 1547945 := bstep (se 2 (by rfl) ⟨580479, by rfl⟩ : syracuseStep 1547945 = 1160959) B1160959
theorem B3914891 : Blo 686314 3914891 := bstep (se 1 (by rfl) ⟨2936168, by rfl⟩ : syracuseStep 3914891 = 5872337) B5872337
theorem B3133587883 : Blo 686314 3133587883 := bstep (se 1 (by rfl) ⟨2350190912, by rfl⟩ : syracuseStep 3133587883 = 4700381825) B4700381825
theorem B1034303 : Blo 686314 1034303 := bstep (se 1 (by rfl) ⟨775727, by rfl⟩ : syracuseStep 1034303 = 1551455) B1551455
theorem B3921929 : Blo 686314 3921929 := bstep (se 2 (by rfl) ⟨1470723, by rfl⟩ : syracuseStep 3921929 = 2941447) B2941447
theorem B4178117177 : Blo 686314 4178117177 := bstep (se 2 (by rfl) ⟨1566793941, by rfl⟩ : syracuseStep 4178117177 = 3133587883) B3133587883
theorem B689535 : Blo 686314 689535 := bstep (se 1 (by rfl) ⟨517151, by rfl⟩ : syracuseStep 689535 = 1034303) B1034303
theorem B1031963 : Blo 686314 1031963 := bstep (se 1 (by rfl) ⟨773972, by rfl⟩ : syracuseStep 1031963 = 1547945) B1547945
theorem B2609927 : Blo 686314 2609927 := bstep (se 1 (by rfl) ⟨1957445, by rfl⟩ : syracuseStep 2609927 = 3914891) B3914891
theorem B2614619 : Blo 686314 2614619 := bstep (se 1 (by rfl) ⟨1960964, by rfl⟩ : syracuseStep 2614619 = 3921929) B3921929
theorem B2785411451 : Blo 686314 2785411451 := bstep (se 1 (by rfl) ⟨2089058588, by rfl⟩ : syracuseStep 2785411451 = 4178117177) B4178117177
theorem B1739951 : Blo 686314 1739951 := bstep (se 1 (by rfl) ⟨1304963, by rfl⟩ : syracuseStep 1739951 = 2609927) B2609927
theorem B1743079 : Blo 686314 1743079 := bstep (se 1 (by rfl) ⟨1307309, by rfl⟩ : syracuseStep 1743079 = 2614619) B2614619
theorem B687975 : Blo 686314 687975 := bstep (se 1 (by rfl) ⟨515981, by rfl⟩ : syracuseStep 687975 = 1031963) B1031963
theorem B1856940967 : Blo 686314 1856940967 := bstep (se 1 (by rfl) ⟨1392705725, by rfl⟩ : syracuseStep 1856940967 = 2785411451) B2785411451
theorem B1159967 : Blo 686314 1159967 := bstep (se 1 (by rfl) ⟨869975, by rfl⟩ : syracuseStep 1159967 = 1739951) B1739951
theorem B2324105 : Blo 686314 2324105 := bstep (se 2 (by rfl) ⟨871539, by rfl⟩ : syracuseStep 2324105 = 1743079) B1743079
theorem B2475921289 : Blo 686314 2475921289 := bstep (se 2 (by rfl) ⟨928470483, by rfl⟩ : syracuseStep 2475921289 = 1856940967) B1856940967
theorem B1549403 : Blo 686314 1549403 := bstep (se 1 (by rfl) ⟨1162052, by rfl⟩ : syracuseStep 1549403 = 2324105) B2324105
theorem B773311 : Blo 686314 773311 := bstep (se 1 (by rfl) ⟨579983, by rfl⟩ : syracuseStep 773311 = 1159967) B1159967
theorem B1031081 : Blo 686314 1031081 := bstep (se 2 (by rfl) ⟨386655, by rfl⟩ : syracuseStep 1031081 = 773311) B773311
theorem B3301228385 : Blo 686314 3301228385 := bstep (se 2 (by rfl) ⟨1237960644, by rfl⟩ : syracuseStep 3301228385 = 2475921289) B2475921289
theorem B1032935 : Blo 686314 1032935 := bstep (se 1 (by rfl) ⟨774701, by rfl⟩ : syracuseStep 1032935 = 1549403) B1549403
theorem B688623 : Blo 686314 688623 := bstep (se 1 (by rfl) ⟨516467, by rfl⟩ : syracuseStep 688623 = 1032935) B1032935
theorem B2200818923 : Blo 686314 2200818923 := bstep (se 1 (by rfl) ⟨1650614192, by rfl⟩ : syracuseStep 2200818923 = 3301228385) B3301228385
theorem B687387 : Blo 686314 687387 := bstep (se 1 (by rfl) ⟨515540, by rfl⟩ : syracuseStep 687387 = 1031081) B1031081
theorem B1467212615 : Blo 686314 1467212615 := bstep (se 1 (by rfl) ⟨1100409461, by rfl⟩ : syracuseStep 1467212615 = 2200818923) B2200818923
theorem B978141743 : Blo 686314 978141743 := bstep (se 1 (by rfl) ⟨733606307, by rfl⟩ : syracuseStep 978141743 = 1467212615) B1467212615
theorem B652094495 : Blo 686314 652094495 := bstep (se 1 (by rfl) ⟨489070871, by rfl⟩ : syracuseStep 652094495 = 978141743) B978141743
theorem B434729663 : Blo 686314 434729663 := bstep (se 1 (by rfl) ⟨326047247, by rfl⟩ : syracuseStep 434729663 = 652094495) B652094495
theorem B289819775 : Blo 686314 289819775 := bstep (se 1 (by rfl) ⟨217364831, by rfl⟩ : syracuseStep 289819775 = 434729663) B434729663
theorem B193213183 : Blo 686314 193213183 := bstep (se 1 (by rfl) ⟨144909887, by rfl⟩ : syracuseStep 193213183 = 289819775) B289819775
theorem B257617577 : Blo 686314 257617577 := bstep (se 2 (by rfl) ⟨96606591, by rfl⟩ : syracuseStep 257617577 = 193213183) B193213183
theorem B171745051 : Blo 686314 171745051 := bstep (se 1 (by rfl) ⟨128808788, by rfl⟩ : syracuseStep 171745051 = 257617577) B257617577
theorem B228993401 : Blo 686314 228993401 := bstep (se 2 (by rfl) ⟨85872525, by rfl⟩ : syracuseStep 228993401 = 171745051) B171745051
theorem B152662267 : Blo 686314 152662267 := bstep (se 1 (by rfl) ⟨114496700, by rfl⟩ : syracuseStep 152662267 = 228993401) B228993401
theorem B203549689 : Blo 686314 203549689 := bstep (se 2 (by rfl) ⟨76331133, by rfl⟩ : syracuseStep 203549689 = 152662267) B152662267
theorem B271399585 : Blo 686314 271399585 := bstep (se 2 (by rfl) ⟨101774844, by rfl⟩ : syracuseStep 271399585 = 203549689) B203549689
theorem B361866113 : Blo 686314 361866113 := bstep (se 2 (by rfl) ⟨135699792, by rfl⟩ : syracuseStep 361866113 = 271399585) B271399585
theorem B241244075 : Blo 686314 241244075 := bstep (se 1 (by rfl) ⟨180933056, by rfl⟩ : syracuseStep 241244075 = 361866113) B361866113
theorem B160829383 : Blo 686314 160829383 := bstep (se 1 (by rfl) ⟨120622037, by rfl⟩ : syracuseStep 160829383 = 241244075) B241244075
theorem B214439177 : Blo 686314 214439177 := bstep (se 2 (by rfl) ⟨80414691, by rfl⟩ : syracuseStep 214439177 = 160829383) B160829383
theorem B142959451 : Blo 686314 142959451 := bstep (se 1 (by rfl) ⟨107219588, by rfl⟩ : syracuseStep 142959451 = 214439177) B214439177
theorem B190612601 : Blo 686314 190612601 := bstep (se 2 (by rfl) ⟨71479725, by rfl⟩ : syracuseStep 190612601 = 142959451) B142959451
theorem B127075067 : Blo 686314 127075067 := bstep (se 1 (by rfl) ⟨95306300, by rfl⟩ : syracuseStep 127075067 = 190612601) B190612601
theorem B84716711 : Blo 686314 84716711 := bstep (se 1 (by rfl) ⟨63537533, by rfl⟩ : syracuseStep 84716711 = 127075067) B127075067
theorem B56477807 : Blo 686314 56477807 := bstep (se 1 (by rfl) ⟨42358355, by rfl⟩ : syracuseStep 56477807 = 84716711) B84716711
theorem B37651871 : Blo 686314 37651871 := bstep (se 1 (by rfl) ⟨28238903, by rfl⟩ : syracuseStep 37651871 = 56477807) B56477807
theorem B25101247 : Blo 686314 25101247 := bstep (se 1 (by rfl) ⟨18825935, by rfl⟩ : syracuseStep 25101247 = 37651871) B37651871
theorem B33468329 : Blo 686314 33468329 := bstep (se 2 (by rfl) ⟨12550623, by rfl⟩ : syracuseStep 33468329 = 25101247) B25101247
theorem B22312219 : Blo 686314 22312219 := bstep (se 1 (by rfl) ⟨16734164, by rfl⟩ : syracuseStep 22312219 = 33468329) B33468329
theorem B29749625 : Blo 686314 29749625 := bstep (se 2 (by rfl) ⟨11156109, by rfl⟩ : syracuseStep 29749625 = 22312219) B22312219
theorem B19833083 : Blo 686314 19833083 := bstep (se 1 (by rfl) ⟨14874812, by rfl⟩ : syracuseStep 19833083 = 29749625) B29749625
theorem B13222055 : Blo 686314 13222055 := bstep (se 1 (by rfl) ⟨9916541, by rfl⟩ : syracuseStep 13222055 = 19833083) B19833083
theorem B8814703 : Blo 686314 8814703 := bstep (se 1 (by rfl) ⟨6611027, by rfl⟩ : syracuseStep 8814703 = 13222055) B13222055
theorem B11752937 : Blo 686314 11752937 := bstep (se 2 (by rfl) ⟨4407351, by rfl⟩ : syracuseStep 11752937 = 8814703) B8814703
theorem B7835291 : Blo 686314 7835291 := bstep (se 1 (by rfl) ⟨5876468, by rfl⟩ : syracuseStep 7835291 = 11752937) B11752937
theorem B5223527 : Blo 686314 5223527 := bstep (se 1 (by rfl) ⟨3917645, by rfl⟩ : syracuseStep 5223527 = 7835291) B7835291
theorem B3482351 : Blo 686314 3482351 := bstep (se 1 (by rfl) ⟨2611763, by rfl⟩ : syracuseStep 3482351 = 5223527) B5223527
theorem B2321567 : Blo 686314 2321567 := bstep (se 1 (by rfl) ⟨1741175, by rfl⟩ : syracuseStep 2321567 = 3482351) B3482351
theorem B1547711 : Blo 686314 1547711 := bstep (se 1 (by rfl) ⟨1160783, by rfl⟩ : syracuseStep 1547711 = 2321567) B2321567
theorem B1031807 : Blo 686314 1031807 := bstep (se 1 (by rfl) ⟨773855, by rfl⟩ : syracuseStep 1031807 = 1547711) B1547711
theorem B687871 : Blo 686314 687871 := bstep (se 1 (by rfl) ⟨515903, by rfl⟩ : syracuseStep 687871 = 1031807) B1031807

theorem C0 (j : ℕ) (h1 : 171578 ≤ j) (h2 : j ≤ 172277) : Blo 686314 (4 * j + 3) := by
  interval_cases j
  · exact B686315
  · exact B686319
  · exact B686323
  · exact B686327
  · exact B686331
  · exact B686335
  · exact B686339
  · exact B686343
  · exact B686347
  · exact B686351
  · exact B686355
  · exact B686359
  · exact B686363
  · exact B686367
  · exact B686371
  · exact B686375
  · exact B686379
  · exact B686383
  · exact B686387
  · exact B686391
  · exact B686395
  · exact B686399
  · exact B686403
  · exact B686407
  · exact B686411
  · exact B686415
  · exact B686419
  · exact B686423
  · exact B686427
  · exact B686431
  · exact B686435
  · exact B686439
  · exact B686443
  · exact B686447
  · exact B686451
  · exact B686455
  · exact B686459
  · exact B686463
  · exact B686467
  · exact B686471
  · exact B686475
  · exact B686479
  · exact B686483
  · exact B686487
  · exact B686491
  · exact B686495
  · exact B686499
  · exact B686503
  · exact B686507
  · exact B686511
  · exact B686515
  · exact B686519
  · exact B686523
  · exact B686527
  · exact B686531
  · exact B686535
  · exact B686539
  · exact B686543
  · exact B686547
  · exact B686551
  · exact B686555
  · exact B686559
  · exact B686563
  · exact B686567
  · exact B686571
  · exact B686575
  · exact B686579
  · exact B686583
  · exact B686587
  · exact B686591
  · exact B686595
  · exact B686599
  · exact B686603
  · exact B686607
  · exact B686611
  · exact B686615
  · exact B686619
  · exact B686623
  · exact B686627
  · exact B686631
  · exact B686635
  · exact B686639
  · exact B686643
  · exact B686647
  · exact B686651
  · exact B686655
  · exact B686659
  · exact B686663
  · exact B686667
  · exact B686671
  · exact B686675
  · exact B686679
  · exact B686683
  · exact B686687
  · exact B686691
  · exact B686695
  · exact B686699
  · exact B686703
  · exact B686707
  · exact B686711
  · exact B686715
  · exact B686719
  · exact B686723
  · exact B686727
  · exact B686731
  · exact B686735
  · exact B686739
  · exact B686743
  · exact B686747
  · exact B686751
  · exact B686755
  · exact B686759
  · exact B686763
  · exact B686767
  · exact B686771
  · exact B686775
  · exact B686779
  · exact B686783
  · exact B686787
  · exact B686791
  · exact B686795
  · exact B686799
  · exact B686803
  · exact B686807
  · exact B686811
  · exact B686815
  · exact B686819
  · exact B686823
  · exact B686827
  · exact B686831
  · exact B686835
  · exact B686839
  · exact B686843
  · exact B686847
  · exact B686851
  · exact B686855
  · exact B686859
  · exact B686863
  · exact B686867
  · exact B686871
  · exact B686875
  · exact B686879
  · exact B686883
  · exact B686887
  · exact B686891
  · exact B686895
  · exact B686899
  · exact B686903
  · exact B686907
  · exact B686911
  · exact B686915
  · exact B686919
  · exact B686923
  · exact B686927
  · exact B686931
  · exact B686935
  · exact B686939
  · exact B686943
  · exact B686947
  · exact B686951
  · exact B686955
  · exact B686959
  · exact B686963
  · exact B686967
  · exact B686971
  · exact B686975
  · exact B686979
  · exact B686983
  · exact B686987
  · exact B686991
  · exact B686995
  · exact B686999
  · exact B687003
  · exact B687007
  · exact B687011
  · exact B687015
  · exact B687019
  · exact B687023
  · exact B687027
  · exact B687031
  · exact B687035
  · exact B687039
  · exact B687043
  · exact B687047
  · exact B687051
  · exact B687055
  · exact B687059
  · exact B687063
  · exact B687067
  · exact B687071
  · exact B687075
  · exact B687079
  · exact B687083
  · exact B687087
  · exact B687091
  · exact B687095
  · exact B687099
  · exact B687103
  · exact B687107
  · exact B687111
  · exact B687115
  · exact B687119
  · exact B687123
  · exact B687127
  · exact B687131
  · exact B687135
  · exact B687139
  · exact B687143
  · exact B687147
  · exact B687151
  · exact B687155
  · exact B687159
  · exact B687163
  · exact B687167
  · exact B687171
  · exact B687175
  · exact B687179
  · exact B687183
  · exact B687187
  · exact B687191
  · exact B687195
  · exact B687199
  · exact B687203
  · exact B687207
  · exact B687211
  · exact B687215
  · exact B687219
  · exact B687223
  · exact B687227
  · exact B687231
  · exact B687235
  · exact B687239
  · exact B687243
  · exact B687247
  · exact B687251
  · exact B687255
  · exact B687259
  · exact B687263
  · exact B687267
  · exact B687271
  · exact B687275
  · exact B687279
  · exact B687283
  · exact B687287
  · exact B687291
  · exact B687295
  · exact B687299
  · exact B687303
  · exact B687307
  · exact B687311
  · exact B687315
  · exact B687319
  · exact B687323
  · exact B687327
  · exact B687331
  · exact B687335
  · exact B687339
  · exact B687343
  · exact B687347
  · exact B687351
  · exact B687355
  · exact B687359
  · exact B687363
  · exact B687367
  · exact B687371
  · exact B687375
  · exact B687379
  · exact B687383
  · exact B687387
  · exact B687391
  · exact B687395
  · exact B687399
  · exact B687403
  · exact B687407
  · exact B687411
  · exact B687415
  · exact B687419
  · exact B687423
  · exact B687427
  · exact B687431
  · exact B687435
  · exact B687439
  · exact B687443
  · exact B687447
  · exact B687451
  · exact B687455
  · exact B687459
  · exact B687463
  · exact B687467
  · exact B687471
  · exact B687475
  · exact B687479
  · exact B687483
  · exact B687487
  · exact B687491
  · exact B687495
  · exact B687499
  · exact B687503
  · exact B687507
  · exact B687511
  · exact B687515
  · exact B687519
  · exact B687523
  · exact B687527
  · exact B687531
  · exact B687535
  · exact B687539
  · exact B687543
  · exact B687547
  · exact B687551
  · exact B687555
  · exact B687559
  · exact B687563
  · exact B687567
  · exact B687571
  · exact B687575
  · exact B687579
  · exact B687583
  · exact B687587
  · exact B687591
  · exact B687595
  · exact B687599
  · exact B687603
  · exact B687607
  · exact B687611
  · exact B687615
  · exact B687619
  · exact B687623
  · exact B687627
  · exact B687631
  · exact B687635
  · exact B687639
  · exact B687643
  · exact B687647
  · exact B687651
  · exact B687655
  · exact B687659
  · exact B687663
  · exact B687667
  · exact B687671
  · exact B687675
  · exact B687679
  · exact B687683
  · exact B687687
  · exact B687691
  · exact B687695
  · exact B687699
  · exact B687703
  · exact B687707
  · exact B687711
  · exact B687715
  · exact B687719
  · exact B687723
  · exact B687727
  · exact B687731
  · exact B687735
  · exact B687739
  · exact B687743
  · exact B687747
  · exact B687751
  · exact B687755
  · exact B687759
  · exact B687763
  · exact B687767
  · exact B687771
  · exact B687775
  · exact B687779
  · exact B687783
  · exact B687787
  · exact B687791
  · exact B687795
  · exact B687799
  · exact B687803
  · exact B687807
  · exact B687811
  · exact B687815
  · exact B687819
  · exact B687823
  · exact B687827
  · exact B687831
  · exact B687835
  · exact B687839
  · exact B687843
  · exact B687847
  · exact B687851
  · exact B687855
  · exact B687859
  · exact B687863
  · exact B687867
  · exact B687871
  · exact B687875
  · exact B687879
  · exact B687883
  · exact B687887
  · exact B687891
  · exact B687895
  · exact B687899
  · exact B687903
  · exact B687907
  · exact B687911
  · exact B687915
  · exact B687919
  · exact B687923
  · exact B687927
  · exact B687931
  · exact B687935
  · exact B687939
  · exact B687943
  · exact B687947
  · exact B687951
  · exact B687955
  · exact B687959
  · exact B687963
  · exact B687967
  · exact B687971
  · exact B687975
  · exact B687979
  · exact B687983
  · exact B687987
  · exact B687991
  · exact B687995
  · exact B687999
  · exact B688003
  · exact B688007
  · exact B688011
  · exact B688015
  · exact B688019
  · exact B688023
  · exact B688027
  · exact B688031
  · exact B688035
  · exact B688039
  · exact B688043
  · exact B688047
  · exact B688051
  · exact B688055
  · exact B688059
  · exact B688063
  · exact B688067
  · exact B688071
  · exact B688075
  · exact B688079
  · exact B688083
  · exact B688087
  · exact B688091
  · exact B688095
  · exact B688099
  · exact B688103
  · exact B688107
  · exact B688111
  · exact B688115
  · exact B688119
  · exact B688123
  · exact B688127
  · exact B688131
  · exact B688135
  · exact B688139
  · exact B688143
  · exact B688147
  · exact B688151
  · exact B688155
  · exact B688159
  · exact B688163
  · exact B688167
  · exact B688171
  · exact B688175
  · exact B688179
  · exact B688183
  · exact B688187
  · exact B688191
  · exact B688195
  · exact B688199
  · exact B688203
  · exact B688207
  · exact B688211
  · exact B688215
  · exact B688219
  · exact B688223
  · exact B688227
  · exact B688231
  · exact B688235
  · exact B688239
  · exact B688243
  · exact B688247
  · exact B688251
  · exact B688255
  · exact B688259
  · exact B688263
  · exact B688267
  · exact B688271
  · exact B688275
  · exact B688279
  · exact B688283
  · exact B688287
  · exact B688291
  · exact B688295
  · exact B688299
  · exact B688303
  · exact B688307
  · exact B688311
  · exact B688315
  · exact B688319
  · exact B688323
  · exact B688327
  · exact B688331
  · exact B688335
  · exact B688339
  · exact B688343
  · exact B688347
  · exact B688351
  · exact B688355
  · exact B688359
  · exact B688363
  · exact B688367
  · exact B688371
  · exact B688375
  · exact B688379
  · exact B688383
  · exact B688387
  · exact B688391
  · exact B688395
  · exact B688399
  · exact B688403
  · exact B688407
  · exact B688411
  · exact B688415
  · exact B688419
  · exact B688423
  · exact B688427
  · exact B688431
  · exact B688435
  · exact B688439
  · exact B688443
  · exact B688447
  · exact B688451
  · exact B688455
  · exact B688459
  · exact B688463
  · exact B688467
  · exact B688471
  · exact B688475
  · exact B688479
  · exact B688483
  · exact B688487
  · exact B688491
  · exact B688495
  · exact B688499
  · exact B688503
  · exact B688507
  · exact B688511
  · exact B688515
  · exact B688519
  · exact B688523
  · exact B688527
  · exact B688531
  · exact B688535
  · exact B688539
  · exact B688543
  · exact B688547
  · exact B688551
  · exact B688555
  · exact B688559
  · exact B688563
  · exact B688567
  · exact B688571
  · exact B688575
  · exact B688579
  · exact B688583
  · exact B688587
  · exact B688591
  · exact B688595
  · exact B688599
  · exact B688603
  · exact B688607
  · exact B688611
  · exact B688615
  · exact B688619
  · exact B688623
  · exact B688627
  · exact B688631
  · exact B688635
  · exact B688639
  · exact B688643
  · exact B688647
  · exact B688651
  · exact B688655
  · exact B688659
  · exact B688663
  · exact B688667
  · exact B688671
  · exact B688675
  · exact B688679
  · exact B688683
  · exact B688687
  · exact B688691
  · exact B688695
  · exact B688699
  · exact B688703
  · exact B688707
  · exact B688711
  · exact B688715
  · exact B688719
  · exact B688723
  · exact B688727
  · exact B688731
  · exact B688735
  · exact B688739
  · exact B688743
  · exact B688747
  · exact B688751
  · exact B688755
  · exact B688759
  · exact B688763
  · exact B688767
  · exact B688771
  · exact B688775
  · exact B688779
  · exact B688783
  · exact B688787
  · exact B688791
  · exact B688795
  · exact B688799
  · exact B688803
  · exact B688807
  · exact B688811
  · exact B688815
  · exact B688819
  · exact B688823
  · exact B688827
  · exact B688831
  · exact B688835
  · exact B688839
  · exact B688843
  · exact B688847
  · exact B688851
  · exact B688855
  · exact B688859
  · exact B688863
  · exact B688867
  · exact B688871
  · exact B688875
  · exact B688879
  · exact B688883
  · exact B688887
  · exact B688891
  · exact B688895
  · exact B688899
  · exact B688903
  · exact B688907
  · exact B688911
  · exact B688915
  · exact B688919
  · exact B688923
  · exact B688927
  · exact B688931
  · exact B688935
  · exact B688939
  · exact B688943
  · exact B688947
  · exact B688951
  · exact B688955
  · exact B688959
  · exact B688963
  · exact B688967
  · exact B688971
  · exact B688975
  · exact B688979
  · exact B688983
  · exact B688987
  · exact B688991
  · exact B688995
  · exact B688999
  · exact B689003
  · exact B689007
  · exact B689011
  · exact B689015
  · exact B689019
  · exact B689023
  · exact B689027
  · exact B689031
  · exact B689035
  · exact B689039
  · exact B689043
  · exact B689047
  · exact B689051
  · exact B689055
  · exact B689059
  · exact B689063
  · exact B689067
  · exact B689071
  · exact B689075
  · exact B689079
  · exact B689083
  · exact B689087
  · exact B689091
  · exact B689095
  · exact B689099
  · exact B689103
  · exact B689107
  · exact B689111

theorem C1 (j : ℕ) (h1 : 172278 ≤ j) (h2 : j ≤ 172577) : Blo 686314 (4 * j + 3) := by
  interval_cases j
  · exact B689115
  · exact B689119
  · exact B689123
  · exact B689127
  · exact B689131
  · exact B689135
  · exact B689139
  · exact B689143
  · exact B689147
  · exact B689151
  · exact B689155
  · exact B689159
  · exact B689163
  · exact B689167
  · exact B689171
  · exact B689175
  · exact B689179
  · exact B689183
  · exact B689187
  · exact B689191
  · exact B689195
  · exact B689199
  · exact B689203
  · exact B689207
  · exact B689211
  · exact B689215
  · exact B689219
  · exact B689223
  · exact B689227
  · exact B689231
  · exact B689235
  · exact B689239
  · exact B689243
  · exact B689247
  · exact B689251
  · exact B689255
  · exact B689259
  · exact B689263
  · exact B689267
  · exact B689271
  · exact B689275
  · exact B689279
  · exact B689283
  · exact B689287
  · exact B689291
  · exact B689295
  · exact B689299
  · exact B689303
  · exact B689307
  · exact B689311
  · exact B689315
  · exact B689319
  · exact B689323
  · exact B689327
  · exact B689331
  · exact B689335
  · exact B689339
  · exact B689343
  · exact B689347
  · exact B689351
  · exact B689355
  · exact B689359
  · exact B689363
  · exact B689367
  · exact B689371
  · exact B689375
  · exact B689379
  · exact B689383
  · exact B689387
  · exact B689391
  · exact B689395
  · exact B689399
  · exact B689403
  · exact B689407
  · exact B689411
  · exact B689415
  · exact B689419
  · exact B689423
  · exact B689427
  · exact B689431
  · exact B689435
  · exact B689439
  · exact B689443
  · exact B689447
  · exact B689451
  · exact B689455
  · exact B689459
  · exact B689463
  · exact B689467
  · exact B689471
  · exact B689475
  · exact B689479
  · exact B689483
  · exact B689487
  · exact B689491
  · exact B689495
  · exact B689499
  · exact B689503
  · exact B689507
  · exact B689511
  · exact B689515
  · exact B689519
  · exact B689523
  · exact B689527
  · exact B689531
  · exact B689535
  · exact B689539
  · exact B689543
  · exact B689547
  · exact B689551
  · exact B689555
  · exact B689559
  · exact B689563
  · exact B689567
  · exact B689571
  · exact B689575
  · exact B689579
  · exact B689583
  · exact B689587
  · exact B689591
  · exact B689595
  · exact B689599
  · exact B689603
  · exact B689607
  · exact B689611
  · exact B689615
  · exact B689619
  · exact B689623
  · exact B689627
  · exact B689631
  · exact B689635
  · exact B689639
  · exact B689643
  · exact B689647
  · exact B689651
  · exact B689655
  · exact B689659
  · exact B689663
  · exact B689667
  · exact B689671
  · exact B689675
  · exact B689679
  · exact B689683
  · exact B689687
  · exact B689691
  · exact B689695
  · exact B689699
  · exact B689703
  · exact B689707
  · exact B689711
  · exact B689715
  · exact B689719
  · exact B689723
  · exact B689727
  · exact B689731
  · exact B689735
  · exact B689739
  · exact B689743
  · exact B689747
  · exact B689751
  · exact B689755
  · exact B689759
  · exact B689763
  · exact B689767
  · exact B689771
  · exact B689775
  · exact B689779
  · exact B689783
  · exact B689787
  · exact B689791
  · exact B689795
  · exact B689799
  · exact B689803
  · exact B689807
  · exact B689811
  · exact B689815
  · exact B689819
  · exact B689823
  · exact B689827
  · exact B689831
  · exact B689835
  · exact B689839
  · exact B689843
  · exact B689847
  · exact B689851
  · exact B689855
  · exact B689859
  · exact B689863
  · exact B689867
  · exact B689871
  · exact B689875
  · exact B689879
  · exact B689883
  · exact B689887
  · exact B689891
  · exact B689895
  · exact B689899
  · exact B689903
  · exact B689907
  · exact B689911
  · exact B689915
  · exact B689919
  · exact B689923
  · exact B689927
  · exact B689931
  · exact B689935
  · exact B689939
  · exact B689943
  · exact B689947
  · exact B689951
  · exact B689955
  · exact B689959
  · exact B689963
  · exact B689967
  · exact B689971
  · exact B689975
  · exact B689979
  · exact B689983
  · exact B689987
  · exact B689991
  · exact B689995
  · exact B689999
  · exact B690003
  · exact B690007
  · exact B690011
  · exact B690015
  · exact B690019
  · exact B690023
  · exact B690027
  · exact B690031
  · exact B690035
  · exact B690039
  · exact B690043
  · exact B690047
  · exact B690051
  · exact B690055
  · exact B690059
  · exact B690063
  · exact B690067
  · exact B690071
  · exact B690075
  · exact B690079
  · exact B690083
  · exact B690087
  · exact B690091
  · exact B690095
  · exact B690099
  · exact B690103
  · exact B690107
  · exact B690111
  · exact B690115
  · exact B690119
  · exact B690123
  · exact B690127
  · exact B690131
  · exact B690135
  · exact B690139
  · exact B690143
  · exact B690147
  · exact B690151
  · exact B690155
  · exact B690159
  · exact B690163
  · exact B690167
  · exact B690171
  · exact B690175
  · exact B690179
  · exact B690183
  · exact B690187
  · exact B690191
  · exact B690195
  · exact B690199
  · exact B690203
  · exact B690207
  · exact B690211
  · exact B690215
  · exact B690219
  · exact B690223
  · exact B690227
  · exact B690231
  · exact B690235
  · exact B690239
  · exact B690243
  · exact B690247
  · exact B690251
  · exact B690255
  · exact B690259
  · exact B690263
  · exact B690267
  · exact B690271
  · exact B690275
  · exact B690279
  · exact B690283
  · exact B690287
  · exact B690291
  · exact B690295
  · exact B690299
  · exact B690303
  · exact B690307
  · exact B690311

theorem solution (m : ℕ) (hlo : 686314 ≤ m) (hhi : m ≤ 690314) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 171578 ≤ j := by omega
    have hj2 : j ≤ 172577 := by omega
    have hb : Blo 686314 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 172278 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
