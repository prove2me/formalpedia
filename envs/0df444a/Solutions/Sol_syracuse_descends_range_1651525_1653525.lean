-- Prove2me | solution 1 for syracuse_descends_range_1651525_1653525
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:17:49.802347+00:00
-- url     : https://prove2.me/submissions/20dfe028-95c0-4180-8f78-80b035245945

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


theorem B1859593 : Blo 1651525 1859593 := bbase (se 2 (by rfl) ⟨697347, by rfl⟩ : syracuseStep 1859593 = 1394695) (by norm_num)
theorem B3719213 : Blo 1651525 3719213 := bbase (se 3 (by rfl) ⟨697352, by rfl⟩ : syracuseStep 3719213 = 1394705) (by norm_num)
theorem B1859629 : Blo 1651525 1859629 := bbase (se 3 (by rfl) ⟨348680, by rfl⟩ : syracuseStep 1859629 = 697361) (by norm_num)
theorem B6275141 : Blo 1651525 6275141 := bbase (se 4 (by rfl) ⟨588294, by rfl⟩ : syracuseStep 6275141 = 1176589) (by norm_num)
theorem B1859665 : Blo 1651525 1859665 := bbase (se 2 (by rfl) ⟨697374, by rfl⟩ : syracuseStep 1859665 = 1394749) (by norm_num)
theorem B3530861 : Blo 1651525 3530861 := bbase (se 3 (by rfl) ⟨662036, by rfl⟩ : syracuseStep 3530861 = 1324073) (by norm_num)
theorem B3719285 : Blo 1651525 3719285 := bbase (se 5 (by rfl) ⟨174341, by rfl⟩ : syracuseStep 3719285 = 348683) (by norm_num)
theorem B1859701 : Blo 1651525 1859701 := bbase (se 5 (by rfl) ⟨87173, by rfl⟩ : syracuseStep 1859701 = 174347) (by norm_num)
theorem B9412757 : Blo 1651525 9412757 := bbase (se 6 (by rfl) ⟨220611, by rfl⟩ : syracuseStep 9412757 = 441223) (by norm_num)
theorem B5578901 : Blo 1651525 5578901 := bbase (se 6 (by rfl) ⟨130755, by rfl⟩ : syracuseStep 5578901 = 261511) (by norm_num)
theorem B1859737 : Blo 1651525 1859737 := bbase (se 2 (by rfl) ⟨697401, by rfl⟩ : syracuseStep 1859737 = 1394803) (by norm_num)
theorem B3719357 : Blo 1651525 3719357 := bbase (se 3 (by rfl) ⟨697379, by rfl⟩ : syracuseStep 3719357 = 1394759) (by norm_num)
theorem B1859773 : Blo 1651525 1859773 := bbase (se 3 (by rfl) ⟨348707, by rfl⟩ : syracuseStep 1859773 = 697415) (by norm_num)
theorem B1884377 : Blo 1651525 1884377 := bbase (se 2 (by rfl) ⟨706641, by rfl⟩ : syracuseStep 1884377 = 1413283) (by norm_num)
theorem B1859809 : Blo 1651525 1859809 := bbase (se 2 (by rfl) ⟨697428, by rfl⟩ : syracuseStep 1859809 = 1394857) (by norm_num)
theorem B3719429 : Blo 1651525 3719429 := bbase (se 4 (by rfl) ⟨348696, by rfl⟩ : syracuseStep 3719429 = 697393) (by norm_num)
theorem B1859845 : Blo 1651525 1859845 := bbase (se 4 (by rfl) ⟨174360, by rfl⟩ : syracuseStep 1859845 = 348721) (by norm_num)
theorem B1859881 : Blo 1651525 1859881 := bbase (se 2 (by rfl) ⟨697455, by rfl⟩ : syracuseStep 1859881 = 1394911) (by norm_num)
theorem B6037829 : Blo 1651525 6037829 := bbase (se 4 (by rfl) ⟨566046, by rfl⟩ : syracuseStep 6037829 = 1132093) (by norm_num)
theorem B3719501 : Blo 1651525 3719501 := bbase (se 3 (by rfl) ⟨697406, by rfl⟩ : syracuseStep 3719501 = 1394813) (by norm_num)
theorem B1859917 : Blo 1651525 1859917 := bbase (se 3 (by rfl) ⟨348734, by rfl⟩ : syracuseStep 1859917 = 697469) (by norm_num)
theorem B3531109 : Blo 1651525 3531109 := bbase (se 4 (by rfl) ⟨331041, by rfl⟩ : syracuseStep 3531109 = 662083) (by norm_num)
theorem B1859953 : Blo 1651525 1859953 := bbase (se 2 (by rfl) ⟨697482, by rfl⟩ : syracuseStep 1859953 = 1394965) (by norm_num)
theorem B3719573 : Blo 1651525 3719573 := bbase (se 6 (by rfl) ⟨87177, by rfl⟩ : syracuseStep 3719573 = 174355) (by norm_num)
theorem B1859989 : Blo 1651525 1859989 := bbase (se 6 (by rfl) ⟨43593, by rfl⟩ : syracuseStep 1859989 = 87187) (by norm_num)
theorem B1909153 : Blo 1651525 1909153 := bbase (se 2 (by rfl) ⟨715932, by rfl⟩ : syracuseStep 1909153 = 1431865) (by norm_num)
theorem B5956021 : Blo 1651525 5956021 := bbase (se 5 (by rfl) ⟨279188, by rfl⟩ : syracuseStep 5956021 = 558377) (by norm_num)
theorem B1860025 : Blo 1651525 1860025 := bbase (se 2 (by rfl) ⟨697509, by rfl⟩ : syracuseStep 1860025 = 1395019) (by norm_num)
theorem B2351549 : Blo 1651525 2351549 := bbase (se 3 (by rfl) ⟨440915, by rfl⟩ : syracuseStep 2351549 = 881831) (by norm_num)
theorem B10584533 : Blo 1651525 10584533 := bbase (se 7 (by rfl) ⟨124037, by rfl⟩ : syracuseStep 10584533 = 248075) (by norm_num)
theorem B3719645 : Blo 1651525 3719645 := bbase (se 3 (by rfl) ⟨697433, by rfl⟩ : syracuseStep 3719645 = 1394867) (by norm_num)
theorem B1860061 : Blo 1651525 1860061 := bbase (se 3 (by rfl) ⟨348761, by rfl⟩ : syracuseStep 1860061 = 697523) (by norm_num)
theorem B1860097 : Blo 1651525 1860097 := bbase (se 2 (by rfl) ⟨697536, by rfl⟩ : syracuseStep 1860097 = 1395073) (by norm_num)
theorem B2351629 : Blo 1651525 2351629 := bbase (se 3 (by rfl) ⟨440930, by rfl⟩ : syracuseStep 2351629 = 881861) (by norm_num)
theorem B28631573 : Blo 1651525 28631573 := bbase (se 6 (by rfl) ⟨671052, by rfl⟩ : syracuseStep 28631573 = 1342105) (by norm_num)
theorem B13591061 : Blo 1651525 13591061 := bbase (se 6 (by rfl) ⟨318540, by rfl⟩ : syracuseStep 13591061 = 637081) (by norm_num)
theorem B3719717 : Blo 1651525 3719717 := bbase (se 4 (by rfl) ⟨348723, by rfl⟩ : syracuseStep 3719717 = 697447) (by norm_num)
theorem B1860133 : Blo 1651525 1860133 := bbase (se 4 (by rfl) ⟨174387, by rfl⟩ : syracuseStep 1860133 = 348775) (by norm_num)
theorem B2646589 : Blo 1651525 2646589 := bbase (se 3 (by rfl) ⟨496235, by rfl⟩ : syracuseStep 2646589 = 992471) (by norm_num)
theorem B5579333 : Blo 1651525 5579333 := bbase (se 4 (by rfl) ⟨523062, by rfl⟩ : syracuseStep 5579333 = 1046125) (by norm_num)
theorem B1860169 : Blo 1651525 1860169 := bbase (se 2 (by rfl) ⟨697563, by rfl⟩ : syracuseStep 1860169 = 1395127) (by norm_num)
theorem B31760981 : Blo 1651525 31760981 := bbase (se 8 (by rfl) ⟨186099, by rfl⟩ : syracuseStep 31760981 = 372199) (by norm_num)
theorem B3719789 : Blo 1651525 3719789 := bbase (se 3 (by rfl) ⟨697460, by rfl⟩ : syracuseStep 3719789 = 1394921) (by norm_num)
theorem B1860205 : Blo 1651525 1860205 := bbase (se 3 (by rfl) ⟨348788, by rfl⟩ : syracuseStep 1860205 = 697577) (by norm_num)
theorem B2351749 : Blo 1651525 2351749 := bbase (se 4 (by rfl) ⟨220476, by rfl⟩ : syracuseStep 2351749 = 440953) (by norm_num)
theorem B5292677 : Blo 1651525 5292677 := bbase (se 4 (by rfl) ⟨496188, by rfl⟩ : syracuseStep 5292677 = 992377) (by norm_num)
theorem B3719861 : Blo 1651525 3719861 := bbase (se 5 (by rfl) ⟨174368, by rfl⟩ : syracuseStep 3719861 = 348737) (by norm_num)
theorem B2351845 : Blo 1651525 2351845 := bbase (se 4 (by rfl) ⟨220485, by rfl⟩ : syracuseStep 2351845 = 440971) (by norm_num)
theorem B3138277 : Blo 1651525 3138277 := bbase (se 4 (by rfl) ⟨294213, by rfl⟩ : syracuseStep 3138277 = 588427) (by norm_num)
theorem B3719933 : Blo 1651525 3719933 := bbase (se 3 (by rfl) ⟨697487, by rfl⟩ : syracuseStep 3719933 = 1394975) (by norm_num)
theorem B8364869 : Blo 1651525 8364869 := bbase (se 4 (by rfl) ⟨784206, by rfl⟩ : syracuseStep 8364869 = 1568413) (by norm_num)
theorem B3720005 : Blo 1651525 3720005 := bbase (se 4 (by rfl) ⟨348750, by rfl⟩ : syracuseStep 3720005 = 697501) (by norm_num)
theorem B7938901 : Blo 1651525 7938901 := bbase (se 9 (by rfl) ⟨23258, by rfl⟩ : syracuseStep 7938901 = 46517) (by norm_num)
theorem B2040665 : Blo 1651525 2040665 := bbase (se 2 (by rfl) ⟨765249, by rfl⟩ : syracuseStep 2040665 = 1530499) (by norm_num)
theorem B3138421 : Blo 1651525 3138421 := bbase (se 5 (by rfl) ⟨147113, by rfl⟩ : syracuseStep 3138421 = 294227) (by norm_num)
theorem B3720077 : Blo 1651525 3720077 := bbase (se 3 (by rfl) ⟨697514, by rfl⟩ : syracuseStep 3720077 = 1395029) (by norm_num)
theorem B3720149 : Blo 1651525 3720149 := bbase (se 7 (by rfl) ⟨43595, by rfl⟩ : syracuseStep 3720149 = 87191) (by norm_num)
theorem B2827237 : Blo 1651525 2827237 := bbase (se 4 (by rfl) ⟨265053, by rfl⟩ : syracuseStep 2827237 = 530107) (by norm_num)
theorem B5579765 : Blo 1651525 5579765 := bbase (se 5 (by rfl) ⟨261551, by rfl⟩ : syracuseStep 5579765 = 523103) (by norm_num)
theorem B3138581 : Blo 1651525 3138581 := bbase (se 6 (by rfl) ⟨73560, by rfl⟩ : syracuseStep 3138581 = 147121) (by norm_num)
theorem B3720221 : Blo 1651525 3720221 := bbase (se 3 (by rfl) ⟨697541, by rfl⟩ : syracuseStep 3720221 = 1395083) (by norm_num)
theorem B8930357 : Blo 1651525 8930357 := bbase (se 5 (by rfl) ⟨418610, by rfl⟩ : syracuseStep 8930357 = 837221) (by norm_num)
theorem B3720293 : Blo 1651525 3720293 := bbase (se 4 (by rfl) ⟨348777, by rfl⟩ : syracuseStep 3720293 = 697555) (by norm_num)
theorem B3138725 : Blo 1651525 3138725 := bbase (se 4 (by rfl) ⟨294255, by rfl⟩ : syracuseStep 3138725 = 588511) (by norm_num)
theorem B3720365 : Blo 1651525 3720365 := bbase (se 3 (by rfl) ⟨697568, by rfl⟩ : syracuseStep 3720365 = 1395137) (by norm_num)
theorem B2352341 : Blo 1651525 2352341 := bbase (se 7 (by rfl) ⟨27566, by rfl⟩ : syracuseStep 2352341 = 55133) (by norm_num)
theorem B2647261 : Blo 1651525 2647261 := bbase (se 3 (by rfl) ⟨496361, by rfl⟩ : syracuseStep 2647261 = 992723) (by norm_num)
theorem B6276325 : Blo 1651525 6276325 := bbase (se 4 (by rfl) ⟨588405, by rfl⟩ : syracuseStep 6276325 = 1176811) (by norm_num)
theorem B2090225 : Blo 1651525 2090225 := bbase (se 2 (by rfl) ⟨783834, by rfl⟩ : syracuseStep 2090225 = 1567669) (by norm_num)
theorem B4465957 : Blo 1651525 4465957 := bbase (se 4 (by rfl) ⟨418683, by rfl⟩ : syracuseStep 4465957 = 837367) (by norm_num)
theorem B2090281 : Blo 1651525 2090281 := bbase (se 2 (by rfl) ⟨783855, by rfl⟩ : syracuseStep 2090281 = 1567711) (by norm_num)
theorem B9413941 : Blo 1651525 9413941 := bbase (se 5 (by rfl) ⟨441278, by rfl⟩ : syracuseStep 9413941 = 882557) (by norm_num)
theorem B3769685 : Blo 1651525 3769685 := bbase (se 12 (by rfl) ⟨1380, by rfl⟩ : syracuseStep 3769685 = 2761) (by norm_num)
theorem B3351925 : Blo 1651525 3351925 := bbase (se 5 (by rfl) ⟨157121, by rfl⟩ : syracuseStep 3351925 = 314243) (by norm_num)
theorem B2090377 : Blo 1651525 2090377 := bbase (se 2 (by rfl) ⟨783891, by rfl⟩ : syracuseStep 2090377 = 1567783) (by norm_num)
theorem B5580197 : Blo 1651525 5580197 := bbase (se 4 (by rfl) ⟨523143, by rfl⟩ : syracuseStep 5580197 = 1046287) (by norm_num)
theorem B3139013 : Blo 1651525 3139013 := bbase (se 4 (by rfl) ⟨294282, by rfl⟩ : syracuseStep 3139013 = 588565) (by norm_num)
theorem B4023821 : Blo 1651525 4023821 := bbase (se 3 (by rfl) ⟨754466, by rfl⟩ : syracuseStep 4023821 = 1508933) (by norm_num)
theorem B6276629 : Blo 1651525 6276629 := bbase (se 6 (by rfl) ⟨147108, by rfl⟩ : syracuseStep 6276629 = 294217) (by norm_num)
theorem B2090549 : Blo 1651525 2090549 := bbase (se 5 (by rfl) ⟨97994, by rfl⟩ : syracuseStep 2090549 = 195989) (by norm_num)
theorem B2090605 : Blo 1651525 2090605 := bbase (se 3 (by rfl) ⟨391988, by rfl⟩ : syracuseStep 2090605 = 783977) (by norm_num)
theorem B3180149 : Blo 1651525 3180149 := bbase (se 5 (by rfl) ⟨149069, by rfl⟩ : syracuseStep 3180149 = 298139) (by norm_num)
theorem B11904661 : Blo 1651525 11904661 := bbase (se 6 (by rfl) ⟨279015, by rfl⟩ : syracuseStep 11904661 = 558031) (by norm_num)
theorem B2090701 : Blo 1651525 2090701 := bbase (se 3 (by rfl) ⟨392006, by rfl⟩ : syracuseStep 2090701 = 784013) (by norm_num)
theorem B2787061 : Blo 1651525 2787061 := bbase (se 5 (by rfl) ⟨130643, by rfl⟩ : syracuseStep 2787061 = 261287) (by norm_num)
theorem B2352893 : Blo 1651525 2352893 := bbase (se 3 (by rfl) ⟨441167, by rfl⟩ : syracuseStep 2352893 = 882335) (by norm_num)
theorem B2787149 : Blo 1651525 2787149 := bbase (se 3 (by rfl) ⟨522590, by rfl⟩ : syracuseStep 2787149 = 1045181) (by norm_num)
theorem B4769621 : Blo 1651525 4769621 := bbase (se 9 (by rfl) ⟨13973, by rfl⟩ : syracuseStep 4769621 = 27947) (by norm_num)
theorem B5580629 : Blo 1651525 5580629 := bbase (se 9 (by rfl) ⟨16349, by rfl⟩ : syracuseStep 5580629 = 32699) (by norm_num)
theorem B4704101 : Blo 1651525 4704101 := bbase (se 4 (by rfl) ⟨441009, by rfl⟩ : syracuseStep 4704101 = 882019) (by norm_num)
theorem B2090873 : Blo 1651525 2090873 := bbase (se 2 (by rfl) ⟨784077, by rfl⟩ : syracuseStep 2090873 = 1568155) (by norm_num)
theorem B2090929 : Blo 1651525 2090929 := bbase (se 2 (by rfl) ⟨784098, by rfl⟩ : syracuseStep 2090929 = 1568197) (by norm_num)
theorem B2787277 : Blo 1651525 2787277 := bbase (se 3 (by rfl) ⟨522614, by rfl⟩ : syracuseStep 2787277 = 1045229) (by norm_num)
theorem B14125013 : Blo 1651525 14125013 := bbase (se 7 (by rfl) ⟨165527, by rfl⟩ : syracuseStep 14125013 = 331055) (by norm_num)
theorem B2091025 : Blo 1651525 2091025 := bbase (se 2 (by rfl) ⟨784134, by rfl⟩ : syracuseStep 2091025 = 1568269) (by norm_num)
theorem B2828317 : Blo 1651525 2828317 := bbase (se 3 (by rfl) ⟨530309, by rfl⟩ : syracuseStep 2828317 = 1060619) (by norm_num)
theorem B2787365 : Blo 1651525 2787365 := bbase (se 4 (by rfl) ⟨261315, by rfl⟩ : syracuseStep 2787365 = 522631) (by norm_num)
theorem B14116949 : Blo 1651525 14116949 := bbase (se 8 (by rfl) ⟨82716, by rfl⟩ : syracuseStep 14116949 = 165433) (by norm_num)
theorem B8366165 : Blo 1651525 8366165 := bbase (se 8 (by rfl) ⟨49020, by rfl⟩ : syracuseStep 8366165 = 98041) (by norm_num)
theorem B2787493 : Blo 1651525 2787493 := bbase (se 4 (by rfl) ⟨261327, by rfl⟩ : syracuseStep 2787493 = 522655) (by norm_num)
theorem B2091197 : Blo 1651525 2091197 := bbase (se 3 (by rfl) ⟨392099, by rfl⟩ : syracuseStep 2091197 = 784199) (by norm_num)
theorem B2648261 : Blo 1651525 2648261 := bbase (se 4 (by rfl) ⟨248274, by rfl⟩ : syracuseStep 2648261 = 496549) (by norm_num)
theorem B2091253 : Blo 1651525 2091253 := bbase (se 5 (by rfl) ⟨98027, by rfl⟩ : syracuseStep 2091253 = 196055) (by norm_num)
theorem B2787581 : Blo 1651525 2787581 := bbase (se 3 (by rfl) ⟨522671, by rfl⟩ : syracuseStep 2787581 = 1045343) (by norm_num)
theorem B1763641 : Blo 1651525 1763641 := bbase (se 2 (by rfl) ⟨661365, by rfl⟩ : syracuseStep 1763641 = 1322731) (by norm_num)
theorem B10045781 : Blo 1651525 10045781 := bbase (se 10 (by rfl) ⟨14715, by rfl⟩ : syracuseStep 10045781 = 29431) (by norm_num)
theorem B2091349 : Blo 1651525 2091349 := bbase (se 10 (by rfl) ⟨3063, by rfl⟩ : syracuseStep 2091349 = 6127) (by norm_num)
theorem B2787709 : Blo 1651525 2787709 := bbase (se 3 (by rfl) ⟨522695, by rfl⟩ : syracuseStep 2787709 = 1045391) (by norm_num)
theorem B1763713 : Blo 1651525 1763713 := bbase (se 2 (by rfl) ⟨661392, by rfl⟩ : syracuseStep 1763713 = 1322785) (by norm_num)
theorem B2787797 : Blo 1651525 2787797 := bbase (se 7 (by rfl) ⟨32669, by rfl⟩ : syracuseStep 2787797 = 65339) (by norm_num)
theorem B2353645 : Blo 1651525 2353645 := bbase (se 3 (by rfl) ⟨441308, by rfl⟩ : syracuseStep 2353645 = 882617) (by norm_num)
theorem B8931829 : Blo 1651525 8931829 := bbase (se 5 (by rfl) ⟨418679, by rfl⟩ : syracuseStep 8931829 = 837359) (by norm_num)
theorem B2091521 : Blo 1651525 2091521 := bbase (se 2 (by rfl) ⟨784320, by rfl⟩ : syracuseStep 2091521 = 1568641) (by norm_num)
theorem B1985033 : Blo 1651525 1985033 := bbase (se 2 (by rfl) ⟨744387, by rfl⟩ : syracuseStep 1985033 = 1488775) (by norm_num)
theorem B1763893 : Blo 1651525 1763893 := bbase (se 5 (by rfl) ⟨82682, by rfl⟩ : syracuseStep 1763893 = 165365) (by norm_num)
theorem B2091577 : Blo 1651525 2091577 := bbase (se 2 (by rfl) ⟨784341, by rfl⟩ : syracuseStep 2091577 = 1568683) (by norm_num)
theorem B2787925 : Blo 1651525 2787925 := bbase (se 8 (by rfl) ⟨16335, by rfl⟩ : syracuseStep 2787925 = 32671) (by norm_num)
theorem B2091673 : Blo 1651525 2091673 := bbase (se 2 (by rfl) ⟨784377, by rfl⟩ : syracuseStep 2091673 = 1568755) (by norm_num)
theorem B2788013 : Blo 1651525 2788013 := bbase (se 3 (by rfl) ⟨522752, by rfl⟩ : syracuseStep 2788013 = 1045505) (by norm_num)
theorem B4238021 : Blo 1651525 4238021 := bbase (se 4 (by rfl) ⟨397314, by rfl⟩ : syracuseStep 4238021 = 794629) (by norm_num)
theorem B4180693 : Blo 1651525 4180693 := bbase (se 7 (by rfl) ⟨48992, by rfl⟩ : syracuseStep 4180693 = 97985) (by norm_num)
theorem B8932085 : Blo 1651525 8932085 := bbase (se 5 (by rfl) ⟨418691, by rfl⟩ : syracuseStep 8932085 = 837383) (by norm_num)
theorem B2788141 : Blo 1651525 2788141 := bbase (se 3 (by rfl) ⟨522776, by rfl⟩ : syracuseStep 2788141 = 1045553) (by norm_num)
theorem B10046261 : Blo 1651525 10046261 := bbase (se 5 (by rfl) ⟨470918, by rfl⟩ : syracuseStep 10046261 = 941837) (by norm_num)
theorem B4180805 : Blo 1651525 4180805 := bbase (se 4 (by rfl) ⟨391950, by rfl⟩ : syracuseStep 4180805 = 783901) (by norm_num)
theorem B2091845 : Blo 1651525 2091845 := bbase (se 4 (by rfl) ⟨196110, by rfl⟩ : syracuseStep 2091845 = 392221) (by norm_num)
theorem B5294933 : Blo 1651525 5294933 := bbase (se 9 (by rfl) ⟨15512, by rfl⟩ : syracuseStep 5294933 = 31025) (by norm_num)
theorem B1985369 : Blo 1651525 1985369 := bbase (se 2 (by rfl) ⟨744513, by rfl⟩ : syracuseStep 1985369 = 1489027) (by norm_num)
theorem B2091901 : Blo 1651525 2091901 := bbase (se 3 (by rfl) ⟨392231, by rfl⟩ : syracuseStep 2091901 = 784463) (by norm_num)
theorem B2788229 : Blo 1651525 2788229 := bbase (se 4 (by rfl) ⟨261396, by rfl⟩ : syracuseStep 2788229 = 522793) (by norm_num)
theorem B1985485 : Blo 1651525 1985485 := bbase (se 3 (by rfl) ⟨372278, by rfl⟩ : syracuseStep 1985485 = 744557) (by norm_num)
theorem B7056341 : Blo 1651525 7056341 := bbase (se 7 (by rfl) ⟨82691, by rfl⟩ : syracuseStep 7056341 = 165383) (by norm_num)
theorem B5295061 : Blo 1651525 5295061 := bbase (se 7 (by rfl) ⟨62051, by rfl⟩ : syracuseStep 5295061 = 124103) (by norm_num)
theorem B2091997 : Blo 1651525 2091997 := bbase (se 3 (by rfl) ⟨392249, by rfl⟩ : syracuseStep 2091997 = 784499) (by norm_num)
theorem B1764337 : Blo 1651525 1764337 := bbase (se 2 (by rfl) ⟨661626, by rfl⟩ : syracuseStep 1764337 = 1323253) (by norm_num)
theorem B4180997 : Blo 1651525 4180997 := bbase (se 4 (by rfl) ⟨391968, by rfl⟩ : syracuseStep 4180997 = 783937) (by norm_num)
theorem B4705285 : Blo 1651525 4705285 := bbase (se 4 (by rfl) ⟨441120, by rfl⟩ : syracuseStep 4705285 = 882241) (by norm_num)
theorem B2788357 : Blo 1651525 2788357 := bbase (se 4 (by rfl) ⟨261408, by rfl⟩ : syracuseStep 2788357 = 522817) (by norm_num)
theorem B1985557 : Blo 1651525 1985557 := bbase (se 6 (by rfl) ⟨46536, by rfl⟩ : syracuseStep 1985557 = 93073) (by norm_num)
theorem B1985581 : Blo 1651525 1985581 := bbase (se 3 (by rfl) ⟨372296, by rfl⟩ : syracuseStep 1985581 = 744593) (by norm_num)
theorem B2788445 : Blo 1651525 2788445 := bbase (se 3 (by rfl) ⟨522833, by rfl⟩ : syracuseStep 2788445 = 1045667) (by norm_num)
theorem B1764461 : Blo 1651525 1764461 := bbase (se 3 (by rfl) ⟨330836, by rfl⟩ : syracuseStep 1764461 = 661673) (by norm_num)
theorem B1674361 : Blo 1651525 1674361 := bbase (se 2 (by rfl) ⟨627885, by rfl⟩ : syracuseStep 1674361 = 1255771) (by norm_num)
theorem B2092169 : Blo 1651525 2092169 := bbase (se 2 (by rfl) ⟨784563, by rfl⟩ : syracuseStep 2092169 = 1569127) (by norm_num)
theorem B4705445 : Blo 1651525 4705445 := bbase (se 4 (by rfl) ⟨441135, by rfl⟩ : syracuseStep 4705445 = 882271) (by norm_num)
theorem B1985725 : Blo 1651525 1985725 := bbase (se 3 (by rfl) ⟨372323, by rfl⟩ : syracuseStep 1985725 = 744647) (by norm_num)
theorem B2092225 : Blo 1651525 2092225 := bbase (se 2 (by rfl) ⟨784584, by rfl⟩ : syracuseStep 2092225 = 1569169) (by norm_num)
theorem B3181781 : Blo 1651525 3181781 := bbase (se 7 (by rfl) ⟨37286, by rfl⟩ : syracuseStep 3181781 = 74573) (by norm_num)
theorem B2788573 : Blo 1651525 2788573 := bbase (se 3 (by rfl) ⟨522857, by rfl⟩ : syracuseStep 2788573 = 1045715) (by norm_num)
theorem B7056629 : Blo 1651525 7056629 := bbase (se 5 (by rfl) ⟨330779, by rfl⟩ : syracuseStep 7056629 = 661559) (by norm_num)
theorem B9415925 : Blo 1651525 9415925 := bbase (se 5 (by rfl) ⟨441371, by rfl⟩ : syracuseStep 9415925 = 882743) (by norm_num)
theorem B2477309 : Blo 1651525 2477309 := bbase (se 3 (by rfl) ⟨464495, by rfl⟩ : syracuseStep 2477309 = 928991) (by norm_num)
theorem B2477333 : Blo 1651525 2477333 := bbase (se 6 (by rfl) ⟨58062, by rfl⟩ : syracuseStep 2477333 = 116125) (by norm_num)
theorem B2092321 : Blo 1651525 2092321 := bbase (se 2 (by rfl) ⟨784620, by rfl⟩ : syracuseStep 2092321 = 1569241) (by norm_num)
theorem B2477357 : Blo 1651525 2477357 := bbase (se 3 (by rfl) ⟨464504, by rfl⟩ : syracuseStep 2477357 = 929009) (by norm_num)
theorem B6696245 : Blo 1651525 6696245 := bbase (se 5 (by rfl) ⟨313886, by rfl⟩ : syracuseStep 6696245 = 627773) (by norm_num)
theorem B5025077 : Blo 1651525 5025077 := bbase (se 5 (by rfl) ⟨235550, by rfl⟩ : syracuseStep 5025077 = 471101) (by norm_num)
theorem B2788661 : Blo 1651525 2788661 := bbase (se 5 (by rfl) ⟨130718, by rfl⟩ : syracuseStep 2788661 = 261437) (by norm_num)
theorem B2477381 : Blo 1651525 2477381 := bbase (se 4 (by rfl) ⟨232254, by rfl⟩ : syracuseStep 2477381 = 464509) (by norm_num)
theorem B4238669 : Blo 1651525 4238669 := bbase (se 3 (by rfl) ⟨794750, by rfl⟩ : syracuseStep 4238669 = 1589501) (by norm_num)
theorem B2477405 : Blo 1651525 2477405 := bbase (se 3 (by rfl) ⟨464513, by rfl⟩ : syracuseStep 2477405 = 929027) (by norm_num)
theorem B4181341 : Blo 1651525 4181341 := bbase (se 3 (by rfl) ⟨784001, by rfl⟩ : syracuseStep 4181341 = 1568003) (by norm_num)
theorem B8367461 : Blo 1651525 8367461 := bbase (se 4 (by rfl) ⟨784449, by rfl⟩ : syracuseStep 8367461 = 1568899) (by norm_num)
theorem B1764713 : Blo 1651525 1764713 := bbase (se 2 (by rfl) ⟨661767, by rfl⟩ : syracuseStep 1764713 = 1323535) (by norm_num)
theorem B2477429 : Blo 1651525 2477429 := bbase (se 5 (by rfl) ⟨116129, by rfl⟩ : syracuseStep 2477429 = 232259) (by norm_num)
theorem B10587509 : Blo 1651525 10587509 := bbase (se 5 (by rfl) ⟨496289, by rfl⟩ : syracuseStep 10587509 = 992579) (by norm_num)
theorem B2477453 : Blo 1651525 2477453 := bbase (se 3 (by rfl) ⟨464522, by rfl⟩ : syracuseStep 2477453 = 929045) (by norm_num)
theorem B4705685 : Blo 1651525 4705685 := bbase (se 6 (by rfl) ⟨110289, by rfl⟩ : syracuseStep 4705685 = 220579) (by norm_num)
theorem B2477477 : Blo 1651525 2477477 := bbase (se 4 (by rfl) ⟨232263, by rfl⟩ : syracuseStep 2477477 = 464527) (by norm_num)
theorem B2788789 : Blo 1651525 2788789 := bbase (se 5 (by rfl) ⟨130724, by rfl⟩ : syracuseStep 2788789 = 261449) (by norm_num)
theorem B2477501 : Blo 1651525 2477501 := bbase (se 3 (by rfl) ⟨464531, by rfl⟩ : syracuseStep 2477501 = 929063) (by norm_num)
theorem B4181453 : Blo 1651525 4181453 := bbase (se 3 (by rfl) ⟨784022, by rfl⟩ : syracuseStep 4181453 = 1568045) (by norm_num)
theorem B2092493 : Blo 1651525 2092493 := bbase (se 3 (by rfl) ⟨392342, by rfl⟩ : syracuseStep 2092493 = 784685) (by norm_num)
theorem B2477525 : Blo 1651525 2477525 := bbase (se 7 (by rfl) ⟨29033, by rfl⟩ : syracuseStep 2477525 = 58067) (by norm_num)
theorem B2477549 : Blo 1651525 2477549 := bbase (se 3 (by rfl) ⟨464540, by rfl⟩ : syracuseStep 2477549 = 929081) (by norm_num)
theorem B3968509 : Blo 1651525 3968509 := bbase (se 3 (by rfl) ⟨744095, by rfl⟩ : syracuseStep 3968509 = 1488191) (by norm_num)
theorem B5574149 : Blo 1651525 5574149 := bbase (se 4 (by rfl) ⟨522576, by rfl⟩ : syracuseStep 5574149 = 1045153) (by norm_num)
theorem B2477573 : Blo 1651525 2477573 := bbase (se 4 (by rfl) ⟨232272, by rfl⟩ : syracuseStep 2477573 = 464545) (by norm_num)
theorem B2092549 : Blo 1651525 2092549 := bbase (se 4 (by rfl) ⟨196176, by rfl⟩ : syracuseStep 2092549 = 392353) (by norm_num)
theorem B2788877 : Blo 1651525 2788877 := bbase (se 3 (by rfl) ⟨522914, by rfl⟩ : syracuseStep 2788877 = 1045829) (by norm_num)
theorem B6696469 : Blo 1651525 6696469 := bbase (se 6 (by rfl) ⟨156948, by rfl⟩ : syracuseStep 6696469 = 313897) (by norm_num)
theorem B2477597 : Blo 1651525 2477597 := bbase (se 3 (by rfl) ⟨464549, by rfl⟩ : syracuseStep 2477597 = 929099) (by norm_num)
theorem B2477621 : Blo 1651525 2477621 := bbase (se 5 (by rfl) ⟨116138, by rfl⟩ : syracuseStep 2477621 = 232277) (by norm_num)
theorem B2477645 : Blo 1651525 2477645 := bbase (se 3 (by rfl) ⟨464558, by rfl⟩ : syracuseStep 2477645 = 929117) (by norm_num)
theorem B4705877 : Blo 1651525 4705877 := bbase (se 8 (by rfl) ⟨27573, by rfl⟩ : syracuseStep 4705877 = 55147) (by norm_num)
theorem B53612117 : Blo 1651525 53612117 := bbase (se 8 (by rfl) ⟨314133, by rfl⟩ : syracuseStep 53612117 = 628267) (by norm_num)
theorem B2477669 : Blo 1651525 2477669 := bbase (se 4 (by rfl) ⟨232281, by rfl⟩ : syracuseStep 2477669 = 464563) (by norm_num)
theorem B2092645 : Blo 1651525 2092645 := bbase (se 4 (by rfl) ⟨196185, by rfl⟩ : syracuseStep 2092645 = 392371) (by norm_num)
theorem B2477693 : Blo 1651525 2477693 := bbase (se 3 (by rfl) ⟨464567, by rfl⟩ : syracuseStep 2477693 = 929135) (by norm_num)
theorem B4181645 : Blo 1651525 4181645 := bbase (se 3 (by rfl) ⟨784058, by rfl⟩ : syracuseStep 4181645 = 1568117) (by norm_num)
theorem B2789005 : Blo 1651525 2789005 := bbase (se 3 (by rfl) ⟨522938, by rfl⟩ : syracuseStep 2789005 = 1045877) (by norm_num)
theorem B2477717 : Blo 1651525 2477717 := bbase (se 6 (by rfl) ⟨58071, by rfl⟩ : syracuseStep 2477717 = 116143) (by norm_num)
theorem B2477741 : Blo 1651525 2477741 := bbase (se 3 (by rfl) ⟨464576, by rfl⟩ : syracuseStep 2477741 = 929153) (by norm_num)
theorem B4296365 : Blo 1651525 4296365 := bbase (se 3 (by rfl) ⟨805568, by rfl⟩ : syracuseStep 4296365 = 1611137) (by norm_num)
theorem B2477765 : Blo 1651525 2477765 := bbase (se 4 (by rfl) ⟨232290, by rfl⟩ : syracuseStep 2477765 = 464581) (by norm_num)
theorem B5656277 : Blo 1651525 5656277 := bbase (se 7 (by rfl) ⟨66284, by rfl⟩ : syracuseStep 5656277 = 132569) (by norm_num)
theorem B2477789 : Blo 1651525 2477789 := bbase (se 3 (by rfl) ⟨464585, by rfl⟩ : syracuseStep 2477789 = 929171) (by norm_num)
theorem B2789093 : Blo 1651525 2789093 := bbase (se 4 (by rfl) ⟨261477, by rfl⟩ : syracuseStep 2789093 = 522955) (by norm_num)
theorem B2477813 : Blo 1651525 2477813 := bbase (se 5 (by rfl) ⟨116147, by rfl⟩ : syracuseStep 2477813 = 232295) (by norm_num)
theorem B2477837 : Blo 1651525 2477837 := bbase (se 3 (by rfl) ⟨464594, by rfl⟩ : syracuseStep 2477837 = 929189) (by norm_num)
theorem B2477861 : Blo 1651525 2477861 := bbase (se 4 (by rfl) ⟨232299, by rfl⟩ : syracuseStep 2477861 = 464599) (by norm_num)
theorem B1765157 : Blo 1651525 1765157 := bbase (se 4 (by rfl) ⟨165483, by rfl⟩ : syracuseStep 1765157 = 330967) (by norm_num)
theorem B2264869 : Blo 1651525 2264869 := bbase (se 4 (by rfl) ⟨212331, by rfl⟩ : syracuseStep 2264869 = 424663) (by norm_num)
theorem B2477885 : Blo 1651525 2477885 := bbase (se 3 (by rfl) ⟨464603, by rfl⟩ : syracuseStep 2477885 = 929207) (by norm_num)
theorem B2477909 : Blo 1651525 2477909 := bbase (se 9 (by rfl) ⟨7259, by rfl⟩ : syracuseStep 2477909 = 14519) (by norm_num)
theorem B2789221 : Blo 1651525 2789221 := bbase (se 4 (by rfl) ⟨261489, by rfl⟩ : syracuseStep 2789221 = 522979) (by norm_num)
theorem B2477933 : Blo 1651525 2477933 := bbase (se 3 (by rfl) ⟨464612, by rfl⟩ : syracuseStep 2477933 = 929225) (by norm_num)
theorem B2477957 : Blo 1651525 2477957 := bbase (se 4 (by rfl) ⟨232308, by rfl⟩ : syracuseStep 2477957 = 464617) (by norm_num)
theorem B2477981 : Blo 1651525 2477981 := bbase (se 3 (by rfl) ⟨464621, by rfl⟩ : syracuseStep 2477981 = 929243) (by norm_num)
theorem B5574581 : Blo 1651525 5574581 := bbase (se 5 (by rfl) ⟨261308, by rfl⟩ : syracuseStep 5574581 = 522617) (by norm_num)
theorem B2478005 : Blo 1651525 2478005 := bbase (se 5 (by rfl) ⟨116156, by rfl⟩ : syracuseStep 2478005 = 232313) (by norm_num)
theorem B2789309 : Blo 1651525 2789309 := bbase (se 3 (by rfl) ⟨522995, by rfl⟩ : syracuseStep 2789309 = 1045991) (by norm_num)
theorem B2478029 : Blo 1651525 2478029 := bbase (se 3 (by rfl) ⟨464630, by rfl⟩ : syracuseStep 2478029 = 929261) (by norm_num)
theorem B2478053 : Blo 1651525 2478053 := bbase (se 4 (by rfl) ⟨232317, by rfl⟩ : syracuseStep 2478053 = 464635) (by norm_num)
theorem B4181989 : Blo 1651525 4181989 := bbase (se 4 (by rfl) ⟨392061, by rfl⟩ : syracuseStep 4181989 = 784123) (by norm_num)
theorem B7057381 : Blo 1651525 7057381 := bbase (se 4 (by rfl) ⟨661629, by rfl⟩ : syracuseStep 7057381 = 1323259) (by norm_num)
theorem B6270965 : Blo 1651525 6270965 := bbase (se 5 (by rfl) ⟨293951, by rfl⟩ : syracuseStep 6270965 = 587903) (by norm_num)
theorem B2478077 : Blo 1651525 2478077 := bbase (se 3 (by rfl) ⟨464639, by rfl⟩ : syracuseStep 2478077 = 929279) (by norm_num)
theorem B2478101 : Blo 1651525 2478101 := bbase (se 6 (by rfl) ⟨58080, by rfl⟩ : syracuseStep 2478101 = 116161) (by norm_num)
theorem B1765405 : Blo 1651525 1765405 := bbase (se 3 (by rfl) ⟨331013, by rfl⟩ : syracuseStep 1765405 = 662027) (by norm_num)
theorem B2478125 : Blo 1651525 2478125 := bbase (se 3 (by rfl) ⟨464648, by rfl⟩ : syracuseStep 2478125 = 929297) (by norm_num)
theorem B12718133 : Blo 1651525 12718133 := bbase (se 5 (by rfl) ⟨596162, by rfl⟩ : syracuseStep 12718133 = 1192325) (by norm_num)
theorem B2789437 : Blo 1651525 2789437 := bbase (se 3 (by rfl) ⟨523019, by rfl⟩ : syracuseStep 2789437 = 1046039) (by norm_num)
theorem B2478149 : Blo 1651525 2478149 := bbase (se 4 (by rfl) ⟨232326, by rfl⟩ : syracuseStep 2478149 = 464653) (by norm_num)
theorem B4182101 : Blo 1651525 4182101 := bbase (se 8 (by rfl) ⟨24504, by rfl⟩ : syracuseStep 4182101 = 49009) (by norm_num)
theorem B2478173 : Blo 1651525 2478173 := bbase (se 3 (by rfl) ⟨464657, by rfl⟩ : syracuseStep 2478173 = 929315) (by norm_num)
theorem B3969125 : Blo 1651525 3969125 := bbase (se 4 (by rfl) ⟨372105, by rfl⟩ : syracuseStep 3969125 = 744211) (by norm_num)
theorem B2478197 : Blo 1651525 2478197 := bbase (se 5 (by rfl) ⟨116165, by rfl⟩ : syracuseStep 2478197 = 232331) (by norm_num)
theorem B2478221 : Blo 1651525 2478221 := bbase (se 3 (by rfl) ⟨464666, by rfl⟩ : syracuseStep 2478221 = 929333) (by norm_num)
theorem B2789525 : Blo 1651525 2789525 := bbase (se 6 (by rfl) ⟨65379, by rfl⟩ : syracuseStep 2789525 = 130759) (by norm_num)
theorem B2478245 : Blo 1651525 2478245 := bbase (se 4 (by rfl) ⟨232335, by rfl⟩ : syracuseStep 2478245 = 464671) (by norm_num)
theorem B8482981 : Blo 1651525 8482981 := bbase (se 4 (by rfl) ⟨795279, by rfl⟩ : syracuseStep 8482981 = 1590559) (by norm_num)
theorem B2478269 : Blo 1651525 2478269 := bbase (se 3 (by rfl) ⟨464675, by rfl⟩ : syracuseStep 2478269 = 929351) (by norm_num)
theorem B2478293 : Blo 1651525 2478293 := bbase (se 7 (by rfl) ⟨29042, by rfl⟩ : syracuseStep 2478293 = 58085) (by norm_num)
theorem B2478317 : Blo 1651525 2478317 := bbase (se 3 (by rfl) ⟨464684, by rfl⟩ : syracuseStep 2478317 = 929369) (by norm_num)
theorem B1675513 : Blo 1651525 1675513 := bbase (se 2 (by rfl) ⟨628317, by rfl⟩ : syracuseStep 1675513 = 1256635) (by norm_num)
theorem B2478341 : Blo 1651525 2478341 := bbase (se 4 (by rfl) ⟨232344, by rfl⟩ : syracuseStep 2478341 = 464689) (by norm_num)
theorem B6271253 : Blo 1651525 6271253 := bbase (se 6 (by rfl) ⟨146982, by rfl⟩ : syracuseStep 6271253 = 293965) (by norm_num)
theorem B4182293 : Blo 1651525 4182293 := bbase (se 6 (by rfl) ⟨98022, by rfl⟩ : syracuseStep 4182293 = 196045) (by norm_num)
theorem B2789653 : Blo 1651525 2789653 := bbase (se 6 (by rfl) ⟨65382, by rfl⟩ : syracuseStep 2789653 = 130765) (by norm_num)
theorem B2478365 : Blo 1651525 2478365 := bbase (se 3 (by rfl) ⟨464693, by rfl⟩ : syracuseStep 2478365 = 929387) (by norm_num)
theorem B3969317 : Blo 1651525 3969317 := bbase (se 4 (by rfl) ⟨372123, by rfl⟩ : syracuseStep 3969317 = 744247) (by norm_num)
theorem B2478389 : Blo 1651525 2478389 := bbase (se 5 (by rfl) ⟨116174, by rfl⟩ : syracuseStep 2478389 = 232349) (by norm_num)
theorem B2478413 : Blo 1651525 2478413 := bbase (se 3 (by rfl) ⟨464702, by rfl⟩ : syracuseStep 2478413 = 929405) (by norm_num)
theorem B5575013 : Blo 1651525 5575013 := bbase (se 4 (by rfl) ⟨522657, by rfl⟩ : syracuseStep 5575013 = 1045315) (by norm_num)
theorem B2478437 : Blo 1651525 2478437 := bbase (se 4 (by rfl) ⟨232353, by rfl⟩ : syracuseStep 2478437 = 464707) (by norm_num)
theorem B2789741 : Blo 1651525 2789741 := bbase (se 3 (by rfl) ⟨523076, by rfl⟩ : syracuseStep 2789741 = 1046153) (by norm_num)
theorem B2478461 : Blo 1651525 2478461 := bbase (se 3 (by rfl) ⟨464711, by rfl⟩ : syracuseStep 2478461 = 929423) (by norm_num)
theorem B2478485 : Blo 1651525 2478485 := bbase (se 6 (by rfl) ⟨58089, by rfl⟩ : syracuseStep 2478485 = 116179) (by norm_num)
theorem B2478509 : Blo 1651525 2478509 := bbase (se 3 (by rfl) ⟨464720, by rfl⟩ : syracuseStep 2478509 = 929441) (by norm_num)
theorem B2478533 : Blo 1651525 2478533 := bbase (se 4 (by rfl) ⟨232362, by rfl⟩ : syracuseStep 2478533 = 464725) (by norm_num)
theorem B2478557 : Blo 1651525 2478557 := bbase (se 3 (by rfl) ⟨464729, by rfl⟩ : syracuseStep 2478557 = 929459) (by norm_num)
theorem B2789869 : Blo 1651525 2789869 := bbase (se 3 (by rfl) ⟨523100, by rfl⟩ : syracuseStep 2789869 = 1046201) (by norm_num)
theorem B2478581 : Blo 1651525 2478581 := bbase (se 5 (by rfl) ⟨116183, by rfl⟩ : syracuseStep 2478581 = 232367) (by norm_num)
theorem B2478605 : Blo 1651525 2478605 := bbase (se 3 (by rfl) ⟨464738, by rfl⟩ : syracuseStep 2478605 = 929477) (by norm_num)
theorem B2478629 : Blo 1651525 2478629 := bbase (se 4 (by rfl) ⟨232371, by rfl⟩ : syracuseStep 2478629 = 464743) (by norm_num)
theorem B4706869 : Blo 1651525 4706869 := bbase (se 5 (by rfl) ⟨220634, by rfl⟩ : syracuseStep 4706869 = 441269) (by norm_num)
theorem B2478653 : Blo 1651525 2478653 := bbase (se 3 (by rfl) ⟨464747, by rfl⟩ : syracuseStep 2478653 = 929495) (by norm_num)
theorem B2789957 : Blo 1651525 2789957 := bbase (se 4 (by rfl) ⟨261558, by rfl⟩ : syracuseStep 2789957 = 523117) (by norm_num)
theorem B2478677 : Blo 1651525 2478677 := bbase (se 8 (by rfl) ⟨14523, by rfl⟩ : syracuseStep 2478677 = 29047) (by norm_num)
theorem B12554837 : Blo 1651525 12554837 := bbase (se 8 (by rfl) ⟨73563, by rfl⟩ : syracuseStep 12554837 = 147127) (by norm_num)
theorem B4182637 : Blo 1651525 4182637 := bbase (se 3 (by rfl) ⟨784244, by rfl⟩ : syracuseStep 4182637 = 1568489) (by norm_num)
theorem B2478701 : Blo 1651525 2478701 := bbase (se 3 (by rfl) ⟨464756, by rfl⟩ : syracuseStep 2478701 = 929513) (by norm_num)
theorem B8368757 : Blo 1651525 8368757 := bbase (se 5 (by rfl) ⟨392285, by rfl⟩ : syracuseStep 8368757 = 784571) (by norm_num)
theorem B2478725 : Blo 1651525 2478725 := bbase (se 4 (by rfl) ⟨232380, by rfl⟩ : syracuseStep 2478725 = 464761) (by norm_num)
theorem B2478749 : Blo 1651525 2478749 := bbase (se 3 (by rfl) ⟨464765, by rfl⟩ : syracuseStep 2478749 = 929531) (by norm_num)
theorem B6697637 : Blo 1651525 6697637 := bbase (se 4 (by rfl) ⟨627903, by rfl⟩ : syracuseStep 6697637 = 1255807) (by norm_num)
theorem B2478773 : Blo 1651525 2478773 := bbase (se 5 (by rfl) ⟨116192, by rfl⟩ : syracuseStep 2478773 = 232385) (by norm_num)
theorem B7058117 : Blo 1651525 7058117 := bbase (se 4 (by rfl) ⟨661698, by rfl⟩ : syracuseStep 7058117 = 1323397) (by norm_num)
theorem B2790085 : Blo 1651525 2790085 := bbase (se 4 (by rfl) ⟨261570, by rfl⟩ : syracuseStep 2790085 = 523141) (by norm_num)
theorem B2478797 : Blo 1651525 2478797 := bbase (se 3 (by rfl) ⟨464774, by rfl⟩ : syracuseStep 2478797 = 929549) (by norm_num)
theorem B4182749 : Blo 1651525 4182749 := bbase (se 3 (by rfl) ⟨784265, by rfl⟩ : syracuseStep 4182749 = 1568531) (by norm_num)
theorem B2478821 : Blo 1651525 2478821 := bbase (se 4 (by rfl) ⟨232389, by rfl⟩ : syracuseStep 2478821 = 464779) (by norm_num)
theorem B2478845 : Blo 1651525 2478845 := bbase (se 3 (by rfl) ⟨464783, by rfl⟩ : syracuseStep 2478845 = 929567) (by norm_num)
theorem B5575445 : Blo 1651525 5575445 := bbase (se 6 (by rfl) ⟨130674, by rfl⟩ : syracuseStep 5575445 = 261349) (by norm_num)
theorem B2478869 : Blo 1651525 2478869 := bbase (se 6 (by rfl) ⟨58098, by rfl⟩ : syracuseStep 2478869 = 116197) (by norm_num)
theorem B2790173 : Blo 1651525 2790173 := bbase (se 3 (by rfl) ⟨523157, by rfl⟩ : syracuseStep 2790173 = 1046315) (by norm_num)
theorem B2478893 : Blo 1651525 2478893 := bbase (se 3 (by rfl) ⟨464792, by rfl⟩ : syracuseStep 2478893 = 929585) (by norm_num)
theorem B2478917 : Blo 1651525 2478917 := bbase (se 4 (by rfl) ⟨232398, by rfl⟩ : syracuseStep 2478917 = 464797) (by norm_num)
theorem B2478941 : Blo 1651525 2478941 := bbase (se 3 (by rfl) ⟨464801, by rfl⟩ : syracuseStep 2478941 = 929603) (by norm_num)
theorem B3969893 : Blo 1651525 3969893 := bbase (se 4 (by rfl) ⟨372177, by rfl⟩ : syracuseStep 3969893 = 744355) (by norm_num)
theorem B2478965 : Blo 1651525 2478965 := bbase (se 5 (by rfl) ⟨116201, by rfl⟩ : syracuseStep 2478965 = 232403) (by norm_num)
theorem B3715973 : Blo 1651525 3715973 := bbase (se 4 (by rfl) ⟨348372, by rfl⟩ : syracuseStep 3715973 = 696745) (by norm_num)
theorem B2478989 : Blo 1651525 2478989 := bbase (se 3 (by rfl) ⟨464810, by rfl⟩ : syracuseStep 2478989 = 929621) (by norm_num)
theorem B4182941 : Blo 1651525 4182941 := bbase (se 3 (by rfl) ⟨784301, by rfl⟩ : syracuseStep 4182941 = 1568603) (by norm_num)
theorem B2790301 : Blo 1651525 2790301 := bbase (se 3 (by rfl) ⟨523181, by rfl⟩ : syracuseStep 2790301 = 1046363) (by norm_num)
theorem B2479013 : Blo 1651525 2479013 := bbase (se 4 (by rfl) ⟨232407, by rfl⟩ : syracuseStep 2479013 = 464815) (by norm_num)
theorem B3527597 : Blo 1651525 3527597 := bbase (se 3 (by rfl) ⟨661424, by rfl⟩ : syracuseStep 3527597 = 1322849) (by norm_num)
theorem B7943093 : Blo 1651525 7943093 := bbase (se 5 (by rfl) ⟨372332, by rfl⟩ : syracuseStep 7943093 = 744665) (by norm_num)
theorem B2479037 : Blo 1651525 2479037 := bbase (se 3 (by rfl) ⟨464819, by rfl⟩ : syracuseStep 2479037 = 929639) (by norm_num)
theorem B3716045 : Blo 1651525 3716045 := bbase (se 3 (by rfl) ⟨696758, by rfl⟩ : syracuseStep 3716045 = 1393517) (by norm_num)
theorem B2479061 : Blo 1651525 2479061 := bbase (se 7 (by rfl) ⟨29051, by rfl⟩ : syracuseStep 2479061 = 58103) (by norm_num)
theorem B2479085 : Blo 1651525 2479085 := bbase (se 3 (by rfl) ⟨464828, by rfl⟩ : syracuseStep 2479085 = 929657) (by norm_num)
theorem B2978797 : Blo 1651525 2978797 := bbase (se 3 (by rfl) ⟨558524, by rfl⟩ : syracuseStep 2978797 = 1117049) (by norm_num)
theorem B12547061 : Blo 1651525 12547061 := bbase (se 5 (by rfl) ⟨588143, by rfl⟩ : syracuseStep 12547061 = 1176287) (by norm_num)
theorem B2479109 : Blo 1651525 2479109 := bbase (se 4 (by rfl) ⟨232416, by rfl⟩ : syracuseStep 2479109 = 464833) (by norm_num)
theorem B8360981 : Blo 1651525 8360981 := bbase (se 6 (by rfl) ⟨195960, by rfl⟩ : syracuseStep 8360981 = 391921) (by norm_num)
theorem B3716117 : Blo 1651525 3716117 := bbase (se 6 (by rfl) ⟨87096, by rfl⟩ : syracuseStep 3716117 = 174193) (by norm_num)
theorem B2479133 : Blo 1651525 2479133 := bbase (se 3 (by rfl) ⟨464837, by rfl⟩ : syracuseStep 2479133 = 929675) (by norm_num)
theorem B2978861 : Blo 1651525 2978861 := bbase (se 3 (by rfl) ⟨558536, by rfl⟩ : syracuseStep 2978861 = 1117073) (by norm_num)
theorem B2479157 : Blo 1651525 2479157 := bbase (se 5 (by rfl) ⟨116210, by rfl⟩ : syracuseStep 2479157 = 232421) (by norm_num)
theorem B2479181 : Blo 1651525 2479181 := bbase (se 3 (by rfl) ⟨464846, by rfl⟩ : syracuseStep 2479181 = 929693) (by norm_num)
theorem B3716189 : Blo 1651525 3716189 := bbase (se 3 (by rfl) ⟨696785, by rfl⟩ : syracuseStep 3716189 = 1393571) (by norm_num)
theorem B2479205 : Blo 1651525 2479205 := bbase (se 4 (by rfl) ⟨232425, by rfl⟩ : syracuseStep 2479205 = 464851) (by norm_num)
theorem B2479229 : Blo 1651525 2479229 := bbase (se 3 (by rfl) ⟨464855, by rfl⟩ : syracuseStep 2479229 = 929711) (by norm_num)
theorem B2479253 : Blo 1651525 2479253 := bbase (se 6 (by rfl) ⟨58107, by rfl⟩ : syracuseStep 2479253 = 116215) (by norm_num)
theorem B3716261 : Blo 1651525 3716261 := bbase (se 4 (by rfl) ⟨348399, by rfl⟩ : syracuseStep 3716261 = 696799) (by norm_num)
theorem B2479277 : Blo 1651525 2479277 := bbase (se 3 (by rfl) ⟨464864, by rfl⟩ : syracuseStep 2479277 = 929729) (by norm_num)
theorem B4240565 : Blo 1651525 4240565 := bbase (se 5 (by rfl) ⟨198776, by rfl⟩ : syracuseStep 4240565 = 397553) (by norm_num)
theorem B5575877 : Blo 1651525 5575877 := bbase (se 4 (by rfl) ⟨522738, by rfl⟩ : syracuseStep 5575877 = 1045477) (by norm_num)
theorem B2479301 : Blo 1651525 2479301 := bbase (se 4 (by rfl) ⟨232434, by rfl⟩ : syracuseStep 2479301 = 464869) (by norm_num)
theorem B2479325 : Blo 1651525 2479325 := bbase (se 3 (by rfl) ⟨464873, by rfl⟩ : syracuseStep 2479325 = 929747) (by norm_num)
theorem B3970277 : Blo 1651525 3970277 := bbase (se 4 (by rfl) ⟨372213, by rfl⟩ : syracuseStep 3970277 = 744427) (by norm_num)
theorem B3716333 : Blo 1651525 3716333 := bbase (se 3 (by rfl) ⟨696812, by rfl⟩ : syracuseStep 3716333 = 1393625) (by norm_num)
theorem B4183285 : Blo 1651525 4183285 := bbase (se 5 (by rfl) ⟨196091, by rfl⟩ : syracuseStep 4183285 = 392183) (by norm_num)
theorem B2479349 : Blo 1651525 2479349 := bbase (se 5 (by rfl) ⟨116219, by rfl⟩ : syracuseStep 2479349 = 232439) (by norm_num)
theorem B7156997 : Blo 1651525 7156997 := bbase (se 4 (by rfl) ⟨670968, by rfl⟩ : syracuseStep 7156997 = 1341937) (by norm_num)
theorem B2479373 : Blo 1651525 2479373 := bbase (se 3 (by rfl) ⟨464882, by rfl⟩ : syracuseStep 2479373 = 929765) (by norm_num)
theorem B3527965 : Blo 1651525 3527965 := bbase (se 3 (by rfl) ⟨661493, by rfl⟩ : syracuseStep 3527965 = 1322987) (by norm_num)
theorem B2479397 : Blo 1651525 2479397 := bbase (se 4 (by rfl) ⟨232443, by rfl⟩ : syracuseStep 2479397 = 464887) (by norm_num)
theorem B3716405 : Blo 1651525 3716405 := bbase (se 5 (by rfl) ⟨174206, by rfl⟩ : syracuseStep 3716405 = 348413) (by norm_num)
theorem B3626293 : Blo 1651525 3626293 := bbase (se 5 (by rfl) ⟨169982, by rfl⟩ : syracuseStep 3626293 = 339965) (by norm_num)
theorem B2479421 : Blo 1651525 2479421 := bbase (se 3 (by rfl) ⟨464891, by rfl⟩ : syracuseStep 2479421 = 929783) (by norm_num)
theorem B2479445 : Blo 1651525 2479445 := bbase (se 15 (by rfl) ⟨113, by rfl⟩ : syracuseStep 2479445 = 227) (by norm_num)
theorem B45241685 : Blo 1651525 45241685 := bbase (se 16 (by rfl) ⟨1035, by rfl⟩ : syracuseStep 45241685 = 2071) (by norm_num)
theorem B4183397 : Blo 1651525 4183397 := bbase (se 4 (by rfl) ⟨392193, by rfl⟩ : syracuseStep 4183397 = 784387) (by norm_num)
theorem B2479469 : Blo 1651525 2479469 := bbase (se 3 (by rfl) ⟨464900, by rfl⟩ : syracuseStep 2479469 = 929801) (by norm_num)
theorem B3716477 : Blo 1651525 3716477 := bbase (se 3 (by rfl) ⟨696839, by rfl⟩ : syracuseStep 3716477 = 1393679) (by norm_num)
theorem B2479493 : Blo 1651525 2479493 := bbase (se 4 (by rfl) ⟨232452, by rfl⟩ : syracuseStep 2479493 = 464905) (by norm_num)
theorem B2233757 : Blo 1651525 2233757 := bbase (se 3 (by rfl) ⟨418829, by rfl⟩ : syracuseStep 2233757 = 837659) (by norm_num)
theorem B2479517 : Blo 1651525 2479517 := bbase (se 3 (by rfl) ⟨464909, by rfl⟩ : syracuseStep 2479517 = 929819) (by norm_num)
theorem B11302325 : Blo 1651525 11302325 := bbase (se 5 (by rfl) ⟨529796, by rfl⟩ : syracuseStep 11302325 = 1059593) (by norm_num)
theorem B6272437 : Blo 1651525 6272437 := bbase (se 5 (by rfl) ⟨294020, by rfl⟩ : syracuseStep 6272437 = 588041) (by norm_num)
theorem B2479541 : Blo 1651525 2479541 := bbase (se 5 (by rfl) ⟨116228, by rfl⟩ : syracuseStep 2479541 = 232457) (by norm_num)
theorem B3716549 : Blo 1651525 3716549 := bbase (se 4 (by rfl) ⟨348426, by rfl⟩ : syracuseStep 3716549 = 696853) (by norm_num)
theorem B2479565 : Blo 1651525 2479565 := bbase (se 3 (by rfl) ⟨464918, by rfl⟩ : syracuseStep 2479565 = 929837) (by norm_num)
theorem B2479589 : Blo 1651525 2479589 := bbase (se 4 (by rfl) ⟨232461, by rfl⟩ : syracuseStep 2479589 = 464923) (by norm_num)
theorem B2479613 : Blo 1651525 2479613 := bbase (se 3 (by rfl) ⟨464927, by rfl⟩ : syracuseStep 2479613 = 929855) (by norm_num)
theorem B3716621 : Blo 1651525 3716621 := bbase (se 3 (by rfl) ⟨696866, by rfl⟩ : syracuseStep 3716621 = 1393733) (by norm_num)
theorem B2479637 : Blo 1651525 2479637 := bbase (se 6 (by rfl) ⟨58116, by rfl⟩ : syracuseStep 2479637 = 116233) (by norm_num)
theorem B4183589 : Blo 1651525 4183589 := bbase (se 4 (by rfl) ⟨392211, by rfl⟩ : syracuseStep 4183589 = 784423) (by norm_num)
theorem B2479661 : Blo 1651525 2479661 := bbase (se 3 (by rfl) ⟨464936, by rfl⟩ : syracuseStep 2479661 = 929873) (by norm_num)
theorem B2479685 : Blo 1651525 2479685 := bbase (se 4 (by rfl) ⟨232470, by rfl⟩ : syracuseStep 2479685 = 464941) (by norm_num)
theorem B3716693 : Blo 1651525 3716693 := bbase (se 8 (by rfl) ⟨21777, by rfl⟩ : syracuseStep 3716693 = 43555) (by norm_num)
theorem B2479709 : Blo 1651525 2479709 := bbase (se 3 (by rfl) ⟨464945, by rfl⟩ : syracuseStep 2479709 = 929891) (by norm_num)
theorem B2119277 : Blo 1651525 2119277 := bbase (se 3 (by rfl) ⟨397364, by rfl⟩ : syracuseStep 2119277 = 794729) (by norm_num)
theorem B5576309 : Blo 1651525 5576309 := bbase (se 5 (by rfl) ⟨261389, by rfl⟩ : syracuseStep 5576309 = 522779) (by norm_num)
theorem B2479733 : Blo 1651525 2479733 := bbase (se 5 (by rfl) ⟨116237, by rfl⟩ : syracuseStep 2479733 = 232475) (by norm_num)
theorem B4707973 : Blo 1651525 4707973 := bbase (se 4 (by rfl) ⟨441372, by rfl⟩ : syracuseStep 4707973 = 882745) (by norm_num)
theorem B2479757 : Blo 1651525 2479757 := bbase (se 3 (by rfl) ⟨464954, by rfl⟩ : syracuseStep 2479757 = 929909) (by norm_num)
theorem B3716765 : Blo 1651525 3716765 := bbase (se 3 (by rfl) ⟨696893, by rfl⟩ : syracuseStep 3716765 = 1393787) (by norm_num)
theorem B2479781 : Blo 1651525 2479781 := bbase (se 4 (by rfl) ⟨232479, by rfl⟩ : syracuseStep 2479781 = 464959) (by norm_num)
theorem B2479805 : Blo 1651525 2479805 := bbase (se 3 (by rfl) ⟨464963, by rfl⟩ : syracuseStep 2479805 = 929927) (by norm_num)
theorem B2479829 : Blo 1651525 2479829 := bbase (se 7 (by rfl) ⟨29060, by rfl⟩ : syracuseStep 2479829 = 58121) (by norm_num)
theorem B3716837 : Blo 1651525 3716837 := bbase (se 4 (by rfl) ⟨348453, by rfl⟩ : syracuseStep 3716837 = 696907) (by norm_num)
theorem B6272741 : Blo 1651525 6272741 := bbase (se 4 (by rfl) ⟨588069, by rfl⟩ : syracuseStep 6272741 = 1176139) (by norm_num)
theorem B2479853 : Blo 1651525 2479853 := bbase (se 3 (by rfl) ⟨464972, by rfl⟩ : syracuseStep 2479853 = 929945) (by norm_num)
theorem B2479877 : Blo 1651525 2479877 := bbase (se 4 (by rfl) ⟨232488, by rfl⟩ : syracuseStep 2479877 = 464977) (by norm_num)
theorem B2479901 : Blo 1651525 2479901 := bbase (se 3 (by rfl) ⟨464981, by rfl⟩ : syracuseStep 2479901 = 929963) (by norm_num)
theorem B3716909 : Blo 1651525 3716909 := bbase (se 3 (by rfl) ⟨696920, by rfl⟩ : syracuseStep 3716909 = 1393841) (by norm_num)
theorem B2479925 : Blo 1651525 2479925 := bbase (se 5 (by rfl) ⟨116246, by rfl⟩ : syracuseStep 2479925 = 232493) (by norm_num)
theorem B2479949 : Blo 1651525 2479949 := bbase (se 3 (by rfl) ⟨464990, by rfl⟩ : syracuseStep 2479949 = 929981) (by norm_num)
theorem B2479973 : Blo 1651525 2479973 := bbase (se 4 (by rfl) ⟨232497, by rfl⟩ : syracuseStep 2479973 = 464995) (by norm_num)
theorem B3716981 : Blo 1651525 3716981 := bbase (se 5 (by rfl) ⟨174233, by rfl⟩ : syracuseStep 3716981 = 348467) (by norm_num)
theorem B4183933 : Blo 1651525 4183933 := bbase (se 3 (by rfl) ⟨784487, by rfl⟩ : syracuseStep 4183933 = 1568975) (by norm_num)
theorem B2479997 : Blo 1651525 2479997 := bbase (se 3 (by rfl) ⟨464999, by rfl⟩ : syracuseStep 2479997 = 929999) (by norm_num)
theorem B8370053 : Blo 1651525 8370053 := bbase (se 4 (by rfl) ⟨784692, by rfl⟩ : syracuseStep 8370053 = 1569385) (by norm_num)
theorem B2480021 : Blo 1651525 2480021 := bbase (se 6 (by rfl) ⟨58125, by rfl⟩ : syracuseStep 2480021 = 116251) (by norm_num)
theorem B2480045 : Blo 1651525 2480045 := bbase (se 3 (by rfl) ⟨465008, by rfl⟩ : syracuseStep 2480045 = 930017) (by norm_num)
theorem B3717053 : Blo 1651525 3717053 := bbase (se 3 (by rfl) ⟨696947, by rfl⟩ : syracuseStep 3717053 = 1393895) (by norm_num)
theorem B2480069 : Blo 1651525 2480069 := bbase (se 4 (by rfl) ⟨232506, by rfl⟩ : syracuseStep 2480069 = 465013) (by norm_num)
theorem B2480093 : Blo 1651525 2480093 := bbase (se 3 (by rfl) ⟨465017, by rfl⟩ : syracuseStep 2480093 = 930035) (by norm_num)
theorem B4184045 : Blo 1651525 4184045 := bbase (se 3 (by rfl) ⟨784508, by rfl⟩ : syracuseStep 4184045 = 1569017) (by norm_num)
theorem B2480117 : Blo 1651525 2480117 := bbase (se 5 (by rfl) ⟨116255, by rfl⟩ : syracuseStep 2480117 = 232511) (by norm_num)
theorem B3717125 : Blo 1651525 3717125 := bbase (se 4 (by rfl) ⟨348480, by rfl⟩ : syracuseStep 3717125 = 696961) (by norm_num)
theorem B2480141 : Blo 1651525 2480141 := bbase (se 3 (by rfl) ⟨465026, by rfl⟩ : syracuseStep 2480141 = 930053) (by norm_num)
theorem B5576741 : Blo 1651525 5576741 := bbase (se 4 (by rfl) ⟨522819, by rfl⟩ : syracuseStep 5576741 = 1045639) (by norm_num)
theorem B2480165 : Blo 1651525 2480165 := bbase (se 4 (by rfl) ⟨232515, by rfl⟩ : syracuseStep 2480165 = 465031) (by norm_num)
theorem B2480189 : Blo 1651525 2480189 := bbase (se 3 (by rfl) ⟨465035, by rfl⟩ : syracuseStep 2480189 = 930071) (by norm_num)
theorem B3717197 : Blo 1651525 3717197 := bbase (se 3 (by rfl) ⟨696974, by rfl⟩ : syracuseStep 3717197 = 1393949) (by norm_num)
theorem B4298837 : Blo 1651525 4298837 := bbase (se 8 (by rfl) ⟨25188, by rfl⟩ : syracuseStep 4298837 = 50377) (by norm_num)
theorem B2480213 : Blo 1651525 2480213 := bbase (se 8 (by rfl) ⟨14532, by rfl⟩ : syracuseStep 2480213 = 29065) (by norm_num)
theorem B3135581 : Blo 1651525 3135581 := bbase (se 3 (by rfl) ⟨587921, by rfl⟩ : syracuseStep 3135581 = 1175843) (by norm_num)
theorem B2480237 : Blo 1651525 2480237 := bbase (se 3 (by rfl) ⟨465044, by rfl⟩ : syracuseStep 2480237 = 930089) (by norm_num)
theorem B2480261 : Blo 1651525 2480261 := bbase (se 4 (by rfl) ⟨232524, by rfl⟩ : syracuseStep 2480261 = 465049) (by norm_num)
theorem B3717269 : Blo 1651525 3717269 := bbase (se 6 (by rfl) ⟨87123, by rfl⟩ : syracuseStep 3717269 = 174247) (by norm_num)
theorem B2480285 : Blo 1651525 2480285 := bbase (se 3 (by rfl) ⟨465053, by rfl⟩ : syracuseStep 2480285 = 930107) (by norm_num)
theorem B4184237 : Blo 1651525 4184237 := bbase (se 3 (by rfl) ⟨784544, by rfl⟩ : syracuseStep 4184237 = 1569089) (by norm_num)
theorem B2234557 : Blo 1651525 2234557 := bbase (se 3 (by rfl) ⟨418979, by rfl⟩ : syracuseStep 2234557 = 837959) (by norm_num)
theorem B3717341 : Blo 1651525 3717341 := bbase (se 3 (by rfl) ⟨697001, by rfl⟩ : syracuseStep 3717341 = 1394003) (by norm_num)
theorem B8362277 : Blo 1651525 8362277 := bbase (se 4 (by rfl) ⟨783963, by rfl⟩ : syracuseStep 8362277 = 1567927) (by norm_num)
theorem B3717413 : Blo 1651525 3717413 := bbase (se 4 (by rfl) ⟨348507, by rfl⟩ : syracuseStep 3717413 = 697015) (by norm_num)
theorem B3717485 : Blo 1651525 3717485 := bbase (se 3 (by rfl) ⟨697028, by rfl⟩ : syracuseStep 3717485 = 1394057) (by norm_num)
theorem B2513317 : Blo 1651525 2513317 := bbase (se 4 (by rfl) ⟨235623, by rfl⟩ : syracuseStep 2513317 = 471247) (by norm_num)
theorem B1857973 : Blo 1651525 1857973 := bbase (se 5 (by rfl) ⟨87092, by rfl⟩ : syracuseStep 1857973 = 174185) (by norm_num)
theorem B3717557 : Blo 1651525 3717557 := bbase (se 5 (by rfl) ⟨174260, by rfl⟩ : syracuseStep 3717557 = 348521) (by norm_num)
theorem B5650901 : Blo 1651525 5650901 := bbase (se 7 (by rfl) ⟨66221, by rfl⟩ : syracuseStep 5650901 = 132443) (by norm_num)
theorem B5577173 : Blo 1651525 5577173 := bbase (se 7 (by rfl) ⟨65357, by rfl⟩ : syracuseStep 5577173 = 130715) (by norm_num)
theorem B1858009 : Blo 1651525 1858009 := bbase (se 2 (by rfl) ⟨696753, by rfl⟩ : syracuseStep 1858009 = 1393507) (by norm_num)
theorem B1858045 : Blo 1651525 1858045 := bbase (se 3 (by rfl) ⟨348383, by rfl⟩ : syracuseStep 1858045 = 696767) (by norm_num)
theorem B3717629 : Blo 1651525 3717629 := bbase (se 3 (by rfl) ⟨697055, by rfl⟩ : syracuseStep 3717629 = 1394111) (by norm_num)
theorem B4184581 : Blo 1651525 4184581 := bbase (se 4 (by rfl) ⟨392304, by rfl⟩ : syracuseStep 4184581 = 784609) (by norm_num)
theorem B1858081 : Blo 1651525 1858081 := bbase (se 2 (by rfl) ⟨696780, by rfl⟩ : syracuseStep 1858081 = 1393561) (by norm_num)
theorem B15874613 : Blo 1651525 15874613 := bbase (se 5 (by rfl) ⟨744122, by rfl⟩ : syracuseStep 15874613 = 1488245) (by norm_num)
theorem B1858117 : Blo 1651525 1858117 := bbase (se 4 (by rfl) ⟨174198, by rfl⟩ : syracuseStep 1858117 = 348397) (by norm_num)
theorem B3717701 : Blo 1651525 3717701 := bbase (se 4 (by rfl) ⟨348534, by rfl⟩ : syracuseStep 3717701 = 697069) (by norm_num)
theorem B1858153 : Blo 1651525 1858153 := bbase (se 2 (by rfl) ⟨696807, by rfl⟩ : syracuseStep 1858153 = 1393615) (by norm_num)
theorem B4184693 : Blo 1651525 4184693 := bbase (se 5 (by rfl) ⟨196157, by rfl⟩ : syracuseStep 4184693 = 392315) (by norm_num)
theorem B1858189 : Blo 1651525 1858189 := bbase (se 3 (by rfl) ⟨348410, by rfl⟩ : syracuseStep 1858189 = 696821) (by norm_num)
theorem B3717773 : Blo 1651525 3717773 := bbase (se 3 (by rfl) ⟨697082, by rfl⟩ : syracuseStep 3717773 = 1394165) (by norm_num)
theorem B3676837 : Blo 1651525 3676837 := bbase (se 4 (by rfl) ⟨344703, by rfl⟩ : syracuseStep 3676837 = 689407) (by norm_num)
theorem B1858225 : Blo 1651525 1858225 := bbase (se 2 (by rfl) ⟨696834, by rfl⟩ : syracuseStep 1858225 = 1393669) (by norm_num)
theorem B1858261 : Blo 1651525 1858261 := bbase (se 7 (by rfl) ⟨21776, by rfl⟩ : syracuseStep 1858261 = 43553) (by norm_num)
theorem B3717845 : Blo 1651525 3717845 := bbase (se 7 (by rfl) ⟨43568, by rfl⟩ : syracuseStep 3717845 = 87137) (by norm_num)
theorem B4242149 : Blo 1651525 4242149 := bbase (se 4 (by rfl) ⟨397701, by rfl⟩ : syracuseStep 4242149 = 795403) (by norm_num)
theorem B1858297 : Blo 1651525 1858297 := bbase (se 2 (by rfl) ⟨696861, by rfl⟩ : syracuseStep 1858297 = 1393723) (by norm_num)
theorem B3529469 : Blo 1651525 3529469 := bbase (se 3 (by rfl) ⟨661775, by rfl⟩ : syracuseStep 3529469 = 1323551) (by norm_num)
theorem B1858333 : Blo 1651525 1858333 := bbase (se 3 (by rfl) ⟨348437, by rfl⟩ : syracuseStep 1858333 = 696875) (by norm_num)
theorem B3717917 : Blo 1651525 3717917 := bbase (se 3 (by rfl) ⟨697109, by rfl⟩ : syracuseStep 3717917 = 1394219) (by norm_num)
theorem B15276853 : Blo 1651525 15276853 := bbase (se 5 (by rfl) ⟨716102, by rfl⟩ : syracuseStep 15276853 = 1432205) (by norm_num)
theorem B4184885 : Blo 1651525 4184885 := bbase (se 5 (by rfl) ⟨196166, by rfl⟩ : syracuseStep 4184885 = 392333) (by norm_num)
theorem B1858369 : Blo 1651525 1858369 := bbase (se 2 (by rfl) ⟨696888, by rfl⟩ : syracuseStep 1858369 = 1393777) (by norm_num)
theorem B3136333 : Blo 1651525 3136333 := bbase (se 3 (by rfl) ⟨588062, by rfl⟩ : syracuseStep 3136333 = 1176125) (by norm_num)
theorem B1858405 : Blo 1651525 1858405 := bbase (se 4 (by rfl) ⟨174225, by rfl⟩ : syracuseStep 1858405 = 348451) (by norm_num)
theorem B3717989 : Blo 1651525 3717989 := bbase (se 4 (by rfl) ⟨348561, by rfl⟩ : syracuseStep 3717989 = 697123) (by norm_num)
theorem B5577605 : Blo 1651525 5577605 := bbase (se 4 (by rfl) ⟨522900, by rfl⟩ : syracuseStep 5577605 = 1045801) (by norm_num)
theorem B1858441 : Blo 1651525 1858441 := bbase (se 2 (by rfl) ⟨696915, by rfl⟩ : syracuseStep 1858441 = 1393831) (by norm_num)
theorem B3529613 : Blo 1651525 3529613 := bbase (se 3 (by rfl) ⟨661802, by rfl⟩ : syracuseStep 3529613 = 1323605) (by norm_num)
theorem B1858477 : Blo 1651525 1858477 := bbase (se 3 (by rfl) ⟨348464, by rfl⟩ : syracuseStep 1858477 = 696929) (by norm_num)
theorem B3718061 : Blo 1651525 3718061 := bbase (se 3 (by rfl) ⟨697136, by rfl⟩ : syracuseStep 3718061 = 1394273) (by norm_num)
theorem B3578813 : Blo 1651525 3578813 := bbase (se 3 (by rfl) ⟨671027, by rfl⟩ : syracuseStep 3578813 = 1342055) (by norm_num)
theorem B3972037 : Blo 1651525 3972037 := bbase (se 4 (by rfl) ⟨372378, by rfl⟩ : syracuseStep 3972037 = 744757) (by norm_num)
theorem B1858513 : Blo 1651525 1858513 := bbase (se 2 (by rfl) ⟨696942, by rfl⟩ : syracuseStep 1858513 = 1393885) (by norm_num)
theorem B3136477 : Blo 1651525 3136477 := bbase (se 3 (by rfl) ⟨588089, by rfl⟩ : syracuseStep 3136477 = 1176179) (by norm_num)
theorem B1858549 : Blo 1651525 1858549 := bbase (se 5 (by rfl) ⟨87119, by rfl⟩ : syracuseStep 1858549 = 174239) (by norm_num)
theorem B3718133 : Blo 1651525 3718133 := bbase (se 5 (by rfl) ⟨174287, by rfl⟩ : syracuseStep 3718133 = 348575) (by norm_num)
theorem B12246005 : Blo 1651525 12246005 := bbase (se 5 (by rfl) ⟨574031, by rfl⟩ : syracuseStep 12246005 = 1148063) (by norm_num)
theorem B1858585 : Blo 1651525 1858585 := bbase (se 2 (by rfl) ⟨696969, by rfl⟩ : syracuseStep 1858585 = 1393939) (by norm_num)
theorem B1858621 : Blo 1651525 1858621 := bbase (se 3 (by rfl) ⟨348491, by rfl⟩ : syracuseStep 1858621 = 696983) (by norm_num)
theorem B3718205 : Blo 1651525 3718205 := bbase (se 3 (by rfl) ⟨697163, by rfl⟩ : syracuseStep 3718205 = 1394327) (by norm_num)
theorem B2825293 : Blo 1651525 2825293 := bbase (se 3 (by rfl) ⟨529742, by rfl⟩ : syracuseStep 2825293 = 1059485) (by norm_num)
theorem B1858657 : Blo 1651525 1858657 := bbase (se 2 (by rfl) ⟨696996, by rfl⟩ : syracuseStep 1858657 = 1393993) (by norm_num)
theorem B3136637 : Blo 1651525 3136637 := bbase (se 3 (by rfl) ⟨588119, by rfl⟩ : syracuseStep 3136637 = 1176239) (by norm_num)
theorem B1858693 : Blo 1651525 1858693 := bbase (se 4 (by rfl) ⟨174252, by rfl⟩ : syracuseStep 1858693 = 348505) (by norm_num)
theorem B3718277 : Blo 1651525 3718277 := bbase (se 4 (by rfl) ⟨348588, by rfl⟩ : syracuseStep 3718277 = 697177) (by norm_num)
theorem B4185229 : Blo 1651525 4185229 := bbase (se 3 (by rfl) ⟨784730, by rfl⟩ : syracuseStep 4185229 = 1569461) (by norm_num)
theorem B2038937 : Blo 1651525 2038937 := bbase (se 2 (by rfl) ⟨764601, by rfl⟩ : syracuseStep 2038937 = 1529203) (by norm_num)
theorem B1858729 : Blo 1651525 1858729 := bbase (se 2 (by rfl) ⟨697023, by rfl⟩ : syracuseStep 1858729 = 1394047) (by norm_num)
theorem B1858765 : Blo 1651525 1858765 := bbase (se 3 (by rfl) ⟨348518, by rfl⟩ : syracuseStep 1858765 = 697037) (by norm_num)
theorem B3718349 : Blo 1651525 3718349 := bbase (se 3 (by rfl) ⟨697190, by rfl⟩ : syracuseStep 3718349 = 1394381) (by norm_num)
theorem B3579085 : Blo 1651525 3579085 := bbase (se 3 (by rfl) ⟨671078, by rfl⟩ : syracuseStep 3579085 = 1342157) (by norm_num)
theorem B20102357 : Blo 1651525 20102357 := bbase (se 7 (by rfl) ⟨235574, by rfl⟩ : syracuseStep 20102357 = 471149) (by norm_num)
theorem B1858801 : Blo 1651525 1858801 := bbase (se 2 (by rfl) ⟨697050, by rfl⟩ : syracuseStep 1858801 = 1394101) (by norm_num)
theorem B3529973 : Blo 1651525 3529973 := bbase (se 5 (by rfl) ⟨165467, by rfl⟩ : syracuseStep 3529973 = 330935) (by norm_num)
theorem B4185341 : Blo 1651525 4185341 := bbase (se 3 (by rfl) ⟨784751, by rfl⟩ : syracuseStep 4185341 = 1569503) (by norm_num)
theorem B3136781 : Blo 1651525 3136781 := bbase (se 3 (by rfl) ⟨588146, by rfl⟩ : syracuseStep 3136781 = 1176293) (by norm_num)
theorem B1858837 : Blo 1651525 1858837 := bbase (se 6 (by rfl) ⟨43566, by rfl⟩ : syracuseStep 1858837 = 87133) (by norm_num)
theorem B3718421 : Blo 1651525 3718421 := bbase (se 6 (by rfl) ⟨87150, by rfl⟩ : syracuseStep 3718421 = 174301) (by norm_num)
theorem B5578037 : Blo 1651525 5578037 := bbase (se 5 (by rfl) ⟨261470, by rfl⟩ : syracuseStep 5578037 = 522941) (by norm_num)
theorem B1858873 : Blo 1651525 1858873 := bbase (se 2 (by rfl) ⟨697077, by rfl⟩ : syracuseStep 1858873 = 1394155) (by norm_num)
theorem B1858909 : Blo 1651525 1858909 := bbase (se 3 (by rfl) ⟨348545, by rfl⟩ : syracuseStep 1858909 = 697091) (by norm_num)
theorem B3718493 : Blo 1651525 3718493 := bbase (se 3 (by rfl) ⟨697217, by rfl⟩ : syracuseStep 3718493 = 1394435) (by norm_num)
theorem B1858945 : Blo 1651525 1858945 := bbase (se 2 (by rfl) ⟨697104, by rfl⟩ : syracuseStep 1858945 = 1394209) (by norm_num)
theorem B1858981 : Blo 1651525 1858981 := bbase (se 4 (by rfl) ⟨174279, by rfl⟩ : syracuseStep 1858981 = 348559) (by norm_num)
theorem B3718565 : Blo 1651525 3718565 := bbase (se 4 (by rfl) ⟨348615, by rfl⟩ : syracuseStep 3718565 = 697231) (by norm_num)
theorem B2121157 : Blo 1651525 2121157 := bbase (se 4 (by rfl) ⟨198858, by rfl⟩ : syracuseStep 2121157 = 397717) (by norm_num)
theorem B1859017 : Blo 1651525 1859017 := bbase (se 2 (by rfl) ⟨697131, by rfl⟩ : syracuseStep 1859017 = 1394263) (by norm_num)
theorem B1859053 : Blo 1651525 1859053 := bbase (se 3 (by rfl) ⟨348572, by rfl⟩ : syracuseStep 1859053 = 697145) (by norm_num)
theorem B3718637 : Blo 1651525 3718637 := bbase (se 3 (by rfl) ⟨697244, by rfl⟩ : syracuseStep 3718637 = 1394489) (by norm_num)
theorem B1859089 : Blo 1651525 1859089 := bbase (se 2 (by rfl) ⟨697158, by rfl⟩ : syracuseStep 1859089 = 1394317) (by norm_num)
theorem B3137069 : Blo 1651525 3137069 := bbase (se 3 (by rfl) ⟨588200, by rfl⟩ : syracuseStep 3137069 = 1176401) (by norm_num)
theorem B2121265 : Blo 1651525 2121265 := bbase (se 2 (by rfl) ⟨795474, by rfl⟩ : syracuseStep 2121265 = 1590949) (by norm_num)
theorem B8363573 : Blo 1651525 8363573 := bbase (se 5 (by rfl) ⟨392042, by rfl⟩ : syracuseStep 8363573 = 784085) (by norm_num)
theorem B1859125 : Blo 1651525 1859125 := bbase (se 5 (by rfl) ⟨87146, by rfl⟩ : syracuseStep 1859125 = 174293) (by norm_num)
theorem B3718709 : Blo 1651525 3718709 := bbase (se 5 (by rfl) ⟨174314, by rfl⟩ : syracuseStep 3718709 = 348629) (by norm_num)
theorem B7945781 : Blo 1651525 7945781 := bbase (se 5 (by rfl) ⟨372458, by rfl⟩ : syracuseStep 7945781 = 744917) (by norm_num)
theorem B1859161 : Blo 1651525 1859161 := bbase (se 2 (by rfl) ⟨697185, by rfl⟩ : syracuseStep 1859161 = 1394371) (by norm_num)
theorem B1859197 : Blo 1651525 1859197 := bbase (se 3 (by rfl) ⟨348599, by rfl⟩ : syracuseStep 1859197 = 697199) (by norm_num)
theorem B3718781 : Blo 1651525 3718781 := bbase (se 3 (by rfl) ⟨697271, by rfl⟩ : syracuseStep 3718781 = 1394543) (by norm_num)
theorem B1859233 : Blo 1651525 1859233 := bbase (se 2 (by rfl) ⟨697212, by rfl⟩ : syracuseStep 1859233 = 1394425) (by norm_num)
theorem B3768005 : Blo 1651525 3768005 := bbase (se 4 (by rfl) ⟨353250, by rfl⟩ : syracuseStep 3768005 = 706501) (by norm_num)
theorem B3137221 : Blo 1651525 3137221 := bbase (se 4 (by rfl) ⟨294114, by rfl⟩ : syracuseStep 3137221 = 588229) (by norm_num)
theorem B1859269 : Blo 1651525 1859269 := bbase (se 4 (by rfl) ⟨174306, by rfl⟩ : syracuseStep 1859269 = 348613) (by norm_num)
theorem B3718853 : Blo 1651525 3718853 := bbase (se 4 (by rfl) ⟨348642, by rfl⟩ : syracuseStep 3718853 = 697285) (by norm_num)
theorem B5578469 : Blo 1651525 5578469 := bbase (se 4 (by rfl) ⟨522981, by rfl⟩ : syracuseStep 5578469 = 1045963) (by norm_num)
theorem B1859305 : Blo 1651525 1859305 := bbase (se 2 (by rfl) ⟨697239, by rfl⟩ : syracuseStep 1859305 = 1394479) (by norm_num)
theorem B1859341 : Blo 1651525 1859341 := bbase (se 3 (by rfl) ⟨348626, by rfl⟩ : syracuseStep 1859341 = 697253) (by norm_num)
theorem B3718925 : Blo 1651525 3718925 := bbase (se 3 (by rfl) ⟨697298, by rfl⟩ : syracuseStep 3718925 = 1394597) (by norm_num)
theorem B6274853 : Blo 1651525 6274853 := bbase (se 4 (by rfl) ⟨588267, by rfl⟩ : syracuseStep 6274853 = 1176535) (by norm_num)
theorem B1859377 : Blo 1651525 1859377 := bbase (se 2 (by rfl) ⟨697266, by rfl⟩ : syracuseStep 1859377 = 1394533) (by norm_num)
theorem B1859413 : Blo 1651525 1859413 := bbase (se 9 (by rfl) ⟨5447, by rfl⟩ : syracuseStep 1859413 = 10895) (by norm_num)
theorem B3718997 : Blo 1651525 3718997 := bbase (se 9 (by rfl) ⟨10895, by rfl⟩ : syracuseStep 3718997 = 21791) (by norm_num)
theorem B1859449 : Blo 1651525 1859449 := bbase (se 2 (by rfl) ⟨697293, by rfl⟩ : syracuseStep 1859449 = 1394587) (by norm_num)
theorem B1859485 : Blo 1651525 1859485 := bbase (se 3 (by rfl) ⟨348653, by rfl⟩ : syracuseStep 1859485 = 697307) (by norm_num)
theorem B3719069 : Blo 1651525 3719069 := bbase (se 3 (by rfl) ⟨697325, by rfl⟩ : syracuseStep 3719069 = 1394651) (by norm_num)
theorem B7061413 : Blo 1651525 7061413 := bbase (se 4 (by rfl) ⟨662007, by rfl⟩ : syracuseStep 7061413 = 1324015) (by norm_num)
theorem B1859521 : Blo 1651525 1859521 := bbase (se 2 (by rfl) ⟨697320, by rfl⟩ : syracuseStep 1859521 = 1394641) (by norm_num)
theorem B1859557 : Blo 1651525 1859557 := bbase (se 4 (by rfl) ⟨174333, by rfl⟩ : syracuseStep 1859557 = 348667) (by norm_num)
theorem B3719141 : Blo 1651525 3719141 := bbase (se 4 (by rfl) ⟨348669, by rfl⟩ : syracuseStep 3719141 = 697339) (by norm_num)
theorem B3137525 : Blo 1651525 3137525 := bbase (se 5 (by rfl) ⟨147071, by rfl⟩ : syracuseStep 3137525 = 294143) (by norm_num)
theorem B8478755 : Blo 1651525 8478755 := bstep (se 1 (by rfl) ⟨6359066, by rfl⟩ : syracuseStep 8478755 = 12718133) B12718133
theorem B2646083 : Blo 1651525 2646083 := bstep (se 1 (by rfl) ⟨1984562, by rfl⟩ : syracuseStep 2646083 = 3969125) B3969125
theorem B3719249 : Blo 1651525 3719249 := bstep (se 2 (by rfl) ⟨1394718, by rfl⟩ : syracuseStep 3719249 = 2789437) B2789437
theorem B6275171 : Blo 1651525 6275171 := bstep (se 1 (by rfl) ⟨4706378, by rfl⟩ : syracuseStep 6275171 = 9412757) B9412757
theorem B3719267 : Blo 1651525 3719267 := bstep (se 1 (by rfl) ⟨2789450, by rfl⟩ : syracuseStep 3719267 = 5578901) B5578901
theorem B1859683 : Blo 1651525 1859683 := bstep (se 1 (by rfl) ⟨1394762, by rfl⟩ : syracuseStep 1859683 = 2789525) B2789525
theorem B2646211 : Blo 1651525 2646211 := bstep (se 1 (by rfl) ⟨1984658, by rfl⟩ : syracuseStep 2646211 = 3969317) B3969317
theorem B1859827 : Blo 1651525 1859827 := bstep (se 1 (by rfl) ⟨1394870, by rfl⟩ : syracuseStep 1859827 = 2789741) B2789741
theorem B19087715 : Blo 1651525 19087715 := bstep (se 1 (by rfl) ⟨14315786, by rfl⟩ : syracuseStep 19087715 = 28631573) B28631573
theorem B9060707 : Blo 1651525 9060707 := bstep (se 1 (by rfl) ⟨6795530, by rfl⟩ : syracuseStep 9060707 = 13591061) B13591061
theorem B5579117 : Blo 1651525 5579117 := bstep (se 3 (by rfl) ⟨1046084, by rfl⟩ : syracuseStep 5579117 = 2092169) B2092169
theorem B3719537 : Blo 1651525 3719537 := bstep (se 2 (by rfl) ⟨1394826, by rfl⟩ : syracuseStep 3719537 = 2789653) B2789653
theorem B3719555 : Blo 1651525 3719555 := bstep (se 1 (by rfl) ⟨2789666, by rfl⟩ : syracuseStep 3719555 = 5579333) B5579333
theorem B1859971 : Blo 1651525 1859971 := bstep (se 1 (by rfl) ⟨1394978, by rfl⟩ : syracuseStep 1859971 = 2789957) B2789957
theorem B2351521 : Blo 1651525 2351521 := bstep (se 2 (by rfl) ⟨881820, by rfl⟩ : syracuseStep 2351521 = 1763641) B1763641
theorem B5579171 : Blo 1651525 5579171 := bstep (se 1 (by rfl) ⟨4184378, by rfl⟩ : syracuseStep 5579171 = 8368757) B8368757
theorem B4465091 : Blo 1651525 4465091 := bstep (se 1 (by rfl) ⟨3348818, by rfl⟩ : syracuseStep 4465091 = 6697637) B6697637
theorem B7062029 : Blo 1651525 7062029 := bstep (se 3 (by rfl) ⟨1324130, by rfl⟩ : syracuseStep 7062029 = 2648261) B2648261
theorem B1860115 : Blo 1651525 1860115 := bstep (se 1 (by rfl) ⟨1395086, by rfl⟩ : syracuseStep 1860115 = 2790173) B2790173
theorem B3351089 : Blo 1651525 3351089 := bstep (se 2 (by rfl) ⟨1256658, by rfl⟩ : syracuseStep 3351089 = 2513317) B2513317
theorem B2646595 : Blo 1651525 2646595 := bstep (se 1 (by rfl) ⟨1984946, by rfl⟩ : syracuseStep 2646595 = 3969893) B3969893
theorem B8929925 : Blo 1651525 8929925 := bstep (se 4 (by rfl) ⟨837180, by rfl⟩ : syracuseStep 8929925 = 1674361) B1674361
theorem B3138193 : Blo 1651525 3138193 := bstep (se 2 (by rfl) ⟨1176822, by rfl⟩ : syracuseStep 3138193 = 2353645) B2353645
theorem B3719825 : Blo 1651525 3719825 := bstep (se 2 (by rfl) ⟨1394934, by rfl⟩ : syracuseStep 3719825 = 2789869) B2789869
theorem B8364707 : Blo 1651525 8364707 := bstep (se 1 (by rfl) ⟨6273530, by rfl⟩ : syracuseStep 8364707 = 12547061) B12547061
theorem B3719843 : Blo 1651525 3719843 := bstep (se 1 (by rfl) ⟨2789882, by rfl⟩ : syracuseStep 3719843 = 5579765) B5579765
theorem B5579441 : Blo 1651525 5579441 := bstep (se 2 (by rfl) ⟨2092290, by rfl⟩ : syracuseStep 5579441 = 4184581) B4184581
theorem B2351857 : Blo 1651525 2351857 := bstep (se 2 (by rfl) ⟨881946, by rfl⟩ : syracuseStep 2351857 = 1763893) B1763893
theorem B6275825 : Blo 1651525 6275825 := bstep (se 2 (by rfl) ⟨2353434, by rfl⟩ : syracuseStep 6275825 = 4706869) B4706869
theorem B2827043 : Blo 1651525 2827043 := bstep (se 1 (by rfl) ⟨2120282, by rfl⟩ : syracuseStep 2827043 = 4240565) B4240565
theorem B2646851 : Blo 1651525 2646851 := bstep (se 1 (by rfl) ⟨1985138, by rfl⟩ : syracuseStep 2646851 = 3970277) B3970277
theorem B3720113 : Blo 1651525 3720113 := bstep (se 2 (by rfl) ⟨1395042, by rfl⟩ : syracuseStep 3720113 = 2790085) B2790085
theorem B21767093 : Blo 1651525 21767093 := bstep (se 5 (by rfl) ⟨1020332, by rfl⟩ : syracuseStep 21767093 = 2040665) B2040665
theorem B3720131 : Blo 1651525 3720131 := bstep (se 1 (by rfl) ⟨2790098, by rfl⟩ : syracuseStep 3720131 = 5580197) B5580197
theorem B19088453 : Blo 1651525 19088453 := bstep (se 4 (by rfl) ⟨1789542, by rfl⟩ : syracuseStep 19088453 = 3579085) B3579085
theorem B5956685 : Blo 1651525 5956685 := bstep (se 3 (by rfl) ⟨1116878, by rfl⟩ : syracuseStep 5956685 = 2233757) B2233757
theorem B10585201 : Blo 1651525 10585201 := bstep (se 2 (by rfl) ⟨3969450, by rfl⟩ : syracuseStep 10585201 = 7938901) B7938901
theorem B12543173 : Blo 1651525 12543173 := bstep (se 4 (by rfl) ⟨1175922, by rfl⟩ : syracuseStep 12543173 = 2351845) B2351845
theorem B5579981 : Blo 1651525 5579981 := bstep (se 3 (by rfl) ⟨1046246, by rfl⟩ : syracuseStep 5579981 = 2092493) B2092493
theorem B3720401 : Blo 1651525 3720401 := bstep (se 2 (by rfl) ⟨1395150, by rfl⟩ : syracuseStep 3720401 = 2790301) B2790301
theorem B3179747 : Blo 1651525 3179747 := bstep (se 1 (by rfl) ⟨2384810, by rfl⟩ : syracuseStep 3179747 = 4769621) B4769621
theorem B3720419 : Blo 1651525 3720419 := bstep (se 1 (by rfl) ⟨2790314, by rfl⟩ : syracuseStep 3720419 = 5580629) B5580629
theorem B5580035 : Blo 1651525 5580035 := bstep (se 1 (by rfl) ⟨4185026, by rfl⟩ : syracuseStep 5580035 = 8370053) B8370053
theorem B2647313 : Blo 1651525 2647313 := bstep (se 2 (by rfl) ⟨992742, by rfl⟩ : syracuseStep 2647313 = 1985485) B1985485
theorem B3769649 : Blo 1651525 3769649 := bstep (se 2 (by rfl) ⟨1413618, by rfl⟩ : syracuseStep 3769649 = 2827237) B2827237
theorem B2352449 : Blo 1651525 2352449 := bstep (se 2 (by rfl) ⟨882168, by rfl⟩ : syracuseStep 2352449 = 1764337) B1764337
theorem B5293421 : Blo 1651525 5293421 := bstep (se 3 (by rfl) ⟨992516, by rfl⟩ : syracuseStep 5293421 = 1985033) B1985033
theorem B2647409 : Blo 1651525 2647409 := bstep (se 2 (by rfl) ⟨992778, by rfl⟩ : syracuseStep 2647409 = 1985557) B1985557
theorem B2647441 : Blo 1651525 2647441 := bstep (se 2 (by rfl) ⟨992790, by rfl⟩ : syracuseStep 2647441 = 1985581) B1985581
theorem B2090387 : Blo 1651525 2090387 := bstep (se 1 (by rfl) ⟨1567790, by rfl⟩ : syracuseStep 2090387 = 3135581) B3135581
theorem B8365517 : Blo 1651525 8365517 := bstep (se 3 (by rfl) ⟨1568534, by rfl⟩ : syracuseStep 8365517 = 3137069) B3137069
theorem B5580305 : Blo 1651525 5580305 := bstep (se 2 (by rfl) ⟨2092614, by rfl⟩ : syracuseStep 5580305 = 4185229) B4185229
theorem B4703953 : Blo 1651525 4703953 := bstep (se 2 (by rfl) ⟨1763982, by rfl⟩ : syracuseStep 4703953 = 3527965) B3527965
theorem B2787041 : Blo 1651525 2787041 := bstep (se 2 (by rfl) ⟨1045140, by rfl⟩ : syracuseStep 2787041 = 2090281) B2090281
theorem B4835057 : Blo 1651525 4835057 := bstep (se 2 (by rfl) ⟨1813146, by rfl⟩ : syracuseStep 4835057 = 3626293) B3626293
theorem B12551921 : Blo 1651525 12551921 := bstep (se 2 (by rfl) ⟨4706970, by rfl⟩ : syracuseStep 12551921 = 9413941) B9413941
theorem B2828099 : Blo 1651525 2828099 := bstep (se 1 (by rfl) ⟨2121074, by rfl⟩ : syracuseStep 2828099 = 4242149) B4242149
theorem B2352979 : Blo 1651525 2352979 := bstep (se 1 (by rfl) ⟨1764734, by rfl⟩ : syracuseStep 2352979 = 3529469) B3529469
theorem B2787169 : Blo 1651525 2787169 := bstep (se 2 (by rfl) ⟨1045188, by rfl⟩ : syracuseStep 2787169 = 2090377) B2090377
theorem B2787203 : Blo 1651525 2787203 := bstep (se 1 (by rfl) ⟨2090402, by rfl⟩ : syracuseStep 2787203 = 4180805) B4180805
theorem B15083405 : Blo 1651525 15083405 := bstep (se 3 (by rfl) ⟨2828138, by rfl⟩ : syracuseStep 15083405 = 5656277) B5656277
theorem B2828209 : Blo 1651525 2828209 := bstep (se 2 (by rfl) ⟨1060578, by rfl⟩ : syracuseStep 2828209 = 2121157) B2121157
theorem B17876933 : Blo 1651525 17876933 := bstep (se 4 (by rfl) ⟨1675962, by rfl⟩ : syracuseStep 17876933 = 3351925) B3351925
theorem B2385875 : Blo 1651525 2385875 := bstep (se 1 (by rfl) ⟨1789406, by rfl⟩ : syracuseStep 2385875 = 3578813) B3578813
theorem B4704227 : Blo 1651525 4704227 := bstep (se 1 (by rfl) ⟨3528170, by rfl⟩ : syracuseStep 4704227 = 7056341) B7056341
theorem B2787331 : Blo 1651525 2787331 := bstep (se 1 (by rfl) ⟨2090498, by rfl⟩ : syracuseStep 2787331 = 4180997) B4180997
theorem B9406469 : Blo 1651525 9406469 := bstep (se 4 (by rfl) ⟨881856, by rfl⟩ : syracuseStep 9406469 = 1763713) B1763713
theorem B2828353 : Blo 1651525 2828353 := bstep (se 2 (by rfl) ⟨1060632, by rfl⟩ : syracuseStep 2828353 = 2121265) B2121265
theorem B2091091 : Blo 1651525 2091091 := bstep (se 1 (by rfl) ⟨1568318, by rfl⟩ : syracuseStep 2091091 = 3136637) B3136637
theorem B2787473 : Blo 1651525 2787473 := bstep (se 2 (by rfl) ⟨1045302, by rfl⟩ : syracuseStep 2787473 = 2090605) B2090605
theorem B4704419 : Blo 1651525 4704419 := bstep (se 1 (by rfl) ⟨3528314, by rfl⟩ : syracuseStep 4704419 = 7056629) B7056629
theorem B2353315 : Blo 1651525 2353315 := bstep (se 1 (by rfl) ⟨1764986, by rfl⟩ : syracuseStep 2353315 = 3529973) B3529973
theorem B6277283 : Blo 1651525 6277283 := bstep (se 1 (by rfl) ⟨4707962, by rfl⟩ : syracuseStep 6277283 = 9415925) B9415925
theorem B6277297 : Blo 1651525 6277297 := bstep (se 2 (by rfl) ⟨2353986, by rfl⟩ : syracuseStep 6277297 = 4707973) B4707973
theorem B2091187 : Blo 1651525 2091187 := bstep (se 1 (by rfl) ⟨1568390, by rfl⟩ : syracuseStep 2091187 = 3136781) B3136781
theorem B5294317 : Blo 1651525 5294317 := bstep (se 3 (by rfl) ⟨992684, by rfl⟩ : syracuseStep 5294317 = 1985369) B1985369
theorem B2787601 : Blo 1651525 2787601 := bstep (se 2 (by rfl) ⟨1045350, by rfl⟩ : syracuseStep 2787601 = 2090701) B2090701
theorem B2787635 : Blo 1651525 2787635 := bstep (se 1 (by rfl) ⟨2090726, by rfl⟩ : syracuseStep 2787635 = 4181453) B4181453
theorem B2787763 : Blo 1651525 2787763 := bstep (se 1 (by rfl) ⟨2090822, by rfl⟩ : syracuseStep 2787763 = 4181645) B4181645
theorem B9406925 : Blo 1651525 9406925 := bstep (se 3 (by rfl) ⟨1763798, by rfl⟩ : syracuseStep 9406925 = 3527597) B3527597
theorem B9415217 : Blo 1651525 9415217 := bstep (se 2 (by rfl) ⟨3530706, by rfl⟩ : syracuseStep 9415217 = 7061413) B7061413
theorem B2787905 : Blo 1651525 2787905 := bstep (se 2 (by rfl) ⟨1045464, by rfl⟩ : syracuseStep 2787905 = 2090929) B2090929
theorem B4180643 : Blo 1651525 4180643 := bstep (se 1 (by rfl) ⟨3135482, by rfl⟩ : syracuseStep 4180643 = 6270965) B6270965
theorem B2091683 : Blo 1651525 2091683 := bstep (se 1 (by rfl) ⟨1568762, by rfl⟩ : syracuseStep 2091683 = 3137525) B3137525
theorem B2788033 : Blo 1651525 2788033 := bstep (se 2 (by rfl) ⟨1045512, by rfl⟩ : syracuseStep 2788033 = 2091025) B2091025
theorem B2353873 : Blo 1651525 2353873 := bstep (se 2 (by rfl) ⟨882702, by rfl⟩ : syracuseStep 2353873 = 1765405) B1765405
theorem B3771089 : Blo 1651525 3771089 := bstep (se 2 (by rfl) ⟨1414158, by rfl⟩ : syracuseStep 3771089 = 2828317) B2828317
theorem B2788067 : Blo 1651525 2788067 := bstep (se 1 (by rfl) ⟨2091050, by rfl⟩ : syracuseStep 2788067 = 4182101) B4182101
theorem B2353907 : Blo 1651525 2353907 := bstep (se 1 (by rfl) ⟨1765430, by rfl⟩ : syracuseStep 2353907 = 3530861) B3530861
theorem B4180835 : Blo 1651525 4180835 := bstep (se 1 (by rfl) ⟨3135626, by rfl⟩ : syracuseStep 4180835 = 6271253) B6271253
theorem B2788195 : Blo 1651525 2788195 := bstep (se 1 (by rfl) ⟨2091146, by rfl⟩ : syracuseStep 2788195 = 4182293) B4182293
theorem B4025219 : Blo 1651525 4025219 := bstep (se 1 (by rfl) ⟨3018914, by rfl⟩ : syracuseStep 4025219 = 6037829) B6037829
theorem B4705229 : Blo 1651525 4705229 := bstep (se 3 (by rfl) ⟨882230, by rfl⟩ : syracuseStep 4705229 = 1764461) B1764461
theorem B2788337 : Blo 1651525 2788337 := bstep (se 2 (by rfl) ⟨1045626, by rfl⟩ : syracuseStep 2788337 = 2091253) B2091253
theorem B2788465 : Blo 1651525 2788465 := bstep (se 2 (by rfl) ⟨1045674, by rfl⟩ : syracuseStep 2788465 = 2091349) B2091349
theorem B4705411 : Blo 1651525 4705411 := bstep (se 1 (by rfl) ⟨3529058, by rfl⟩ : syracuseStep 4705411 = 7058117) B7058117
theorem B2788499 : Blo 1651525 2788499 := bstep (se 1 (by rfl) ⟨2091374, by rfl⟩ : syracuseStep 2788499 = 4182749) B4182749
theorem B5025005 : Blo 1651525 5025005 := bstep (se 3 (by rfl) ⟨942188, by rfl⟩ : syracuseStep 5025005 = 1884377) B1884377
theorem B2477297 : Blo 1651525 2477297 := bstep (se 2 (by rfl) ⟨928986, by rfl⟩ : syracuseStep 2477297 = 1857973) B1857973
theorem B2477315 : Blo 1651525 2477315 := bstep (se 1 (by rfl) ⟨1857986, by rfl⟩ : syracuseStep 2477315 = 3715973) B3715973
theorem B2788627 : Blo 1651525 2788627 := bstep (se 1 (by rfl) ⟨2091470, by rfl⟩ : syracuseStep 2788627 = 4182941) B4182941
theorem B2477345 : Blo 1651525 2477345 := bstep (se 2 (by rfl) ⟨929004, by rfl⟩ : syracuseStep 2477345 = 1858009) B1858009
theorem B5295395 : Blo 1651525 5295395 := bstep (se 1 (by rfl) ⟨3971546, by rfl⟩ : syracuseStep 5295395 = 7943093) B7943093
theorem B5573933 : Blo 1651525 5573933 := bstep (se 3 (by rfl) ⟨1045112, by rfl⟩ : syracuseStep 5573933 = 2090225) B2090225
theorem B2477363 : Blo 1651525 2477363 := bstep (se 1 (by rfl) ⟨1858022, by rfl⟩ : syracuseStep 2477363 = 3716045) B3716045
theorem B2477393 : Blo 1651525 2477393 := bstep (se 2 (by rfl) ⟨929022, by rfl⟩ : syracuseStep 2477393 = 1858045) B1858045
theorem B5573987 : Blo 1651525 5573987 := bstep (se 1 (by rfl) ⟨4180490, by rfl⟩ : syracuseStep 5573987 = 8360981) B8360981
theorem B2477411 : Blo 1651525 2477411 := bstep (se 1 (by rfl) ⟨1858058, by rfl⟩ : syracuseStep 2477411 = 3716117) B3716117
theorem B2092387 : Blo 1651525 2092387 := bstep (se 1 (by rfl) ⟨1569290, by rfl⟩ : syracuseStep 2092387 = 3138581) B3138581
theorem B2477441 : Blo 1651525 2477441 := bstep (se 2 (by rfl) ⟨929040, by rfl⟩ : syracuseStep 2477441 = 1858081) B1858081
theorem B2477459 : Blo 1651525 2477459 := bstep (se 1 (by rfl) ⟨1858094, by rfl⟩ : syracuseStep 2477459 = 3716189) B3716189
theorem B2788769 : Blo 1651525 2788769 := bstep (se 2 (by rfl) ⟨1045788, by rfl⟩ : syracuseStep 2788769 = 2091577) B2091577
theorem B2477489 : Blo 1651525 2477489 := bstep (se 2 (by rfl) ⟨929058, by rfl⟩ : syracuseStep 2477489 = 1858117) B1858117
theorem B2477507 : Blo 1651525 2477507 := bstep (se 1 (by rfl) ⟨1858130, by rfl⟩ : syracuseStep 2477507 = 3716261) B3716261
theorem B2092483 : Blo 1651525 2092483 := bstep (se 1 (by rfl) ⟨1569362, by rfl⟩ : syracuseStep 2092483 = 3138725) B3138725
theorem B2477537 : Blo 1651525 2477537 := bstep (se 2 (by rfl) ⟨929076, by rfl⟩ : syracuseStep 2477537 = 1858153) B1858153
theorem B2477555 : Blo 1651525 2477555 := bstep (se 1 (by rfl) ⟨1858166, by rfl⟩ : syracuseStep 2477555 = 3716333) B3716333
theorem B4771331 : Blo 1651525 4771331 := bstep (se 1 (by rfl) ⟨3578498, by rfl⟩ : syracuseStep 4771331 = 7156997) B7156997
theorem B2477585 : Blo 1651525 2477585 := bstep (se 2 (by rfl) ⟨929094, by rfl⟩ : syracuseStep 2477585 = 1858189) B1858189
theorem B2788897 : Blo 1651525 2788897 := bstep (se 2 (by rfl) ⟨1045836, by rfl⟩ : syracuseStep 2788897 = 2091673) B2091673
theorem B2477603 : Blo 1651525 2477603 := bstep (se 1 (by rfl) ⟨1858202, by rfl⟩ : syracuseStep 2477603 = 3716405) B3716405
theorem B4902449 : Blo 1651525 4902449 := bstep (se 2 (by rfl) ⟨1838418, by rfl⟩ : syracuseStep 4902449 = 3676837) B3676837
theorem B45854261 : Blo 1651525 45854261 := bstep (se 5 (by rfl) ⟨2149418, by rfl⟩ : syracuseStep 45854261 = 4298837) B4298837
theorem B2477633 : Blo 1651525 2477633 := bstep (se 2 (by rfl) ⟨929112, by rfl⟩ : syracuseStep 2477633 = 1858225) B1858225
theorem B2788931 : Blo 1651525 2788931 := bstep (se 1 (by rfl) ⟨2091698, by rfl⟩ : syracuseStep 2788931 = 4183397) B4183397
theorem B2477651 : Blo 1651525 2477651 := bstep (se 1 (by rfl) ⟨1858238, by rfl⟩ : syracuseStep 2477651 = 3716477) B3716477
theorem B4705901 : Blo 1651525 4705901 := bstep (se 3 (by rfl) ⟨882356, by rfl⟩ : syracuseStep 4705901 = 1764713) B1764713
theorem B5574257 : Blo 1651525 5574257 := bstep (se 2 (by rfl) ⟨2090346, by rfl⟩ : syracuseStep 5574257 = 4180693) B4180693
theorem B2477681 : Blo 1651525 2477681 := bstep (se 2 (by rfl) ⟨929130, by rfl⟩ : syracuseStep 2477681 = 1858261) B1858261
theorem B2477699 : Blo 1651525 2477699 := bstep (se 1 (by rfl) ⟨1858274, by rfl⟩ : syracuseStep 2477699 = 3716549) B3716549
theorem B2477729 : Blo 1651525 2477729 := bstep (se 2 (by rfl) ⟨929148, by rfl⟩ : syracuseStep 2477729 = 1858297) B1858297
theorem B2477747 : Blo 1651525 2477747 := bstep (se 1 (by rfl) ⟨1858310, by rfl⟩ : syracuseStep 2477747 = 3716621) B3716621
theorem B2789059 : Blo 1651525 2789059 := bstep (se 1 (by rfl) ⟨2091794, by rfl⟩ : syracuseStep 2789059 = 4183589) B4183589
theorem B2477777 : Blo 1651525 2477777 := bstep (se 2 (by rfl) ⟨929166, by rfl⟩ : syracuseStep 2477777 = 1858333) B1858333
theorem B2477795 : Blo 1651525 2477795 := bstep (se 1 (by rfl) ⟨1858346, by rfl⟩ : syracuseStep 2477795 = 3716693) B3716693
theorem B2477825 : Blo 1651525 2477825 := bstep (se 2 (by rfl) ⟨929184, by rfl⟩ : syracuseStep 2477825 = 1858369) B1858369
theorem B4181777 : Blo 1651525 4181777 := bstep (se 2 (by rfl) ⟨1568166, by rfl⟩ : syracuseStep 4181777 = 3136333) B3136333
theorem B2477843 : Blo 1651525 2477843 := bstep (se 1 (by rfl) ⟨1858382, by rfl⟩ : syracuseStep 2477843 = 3716765) B3716765
theorem B2477873 : Blo 1651525 2477873 := bstep (se 2 (by rfl) ⟨929202, by rfl⟩ : syracuseStep 2477873 = 1858405) B1858405
theorem B2477891 : Blo 1651525 2477891 := bstep (se 1 (by rfl) ⟨1858418, by rfl⟩ : syracuseStep 2477891 = 3716837) B3716837
theorem B4181827 : Blo 1651525 4181827 := bstep (se 1 (by rfl) ⟨3136370, by rfl⟩ : syracuseStep 4181827 = 6272741) B6272741
theorem B14118725 : Blo 1651525 14118725 := bstep (se 4 (by rfl) ⟨1323630, by rfl⟩ : syracuseStep 14118725 = 2647261) B2647261
theorem B6270797 : Blo 1651525 6270797 := bstep (se 3 (by rfl) ⟨1175774, by rfl⟩ : syracuseStep 6270797 = 2351549) B2351549
theorem B2789201 : Blo 1651525 2789201 := bstep (se 2 (by rfl) ⟨1045950, by rfl⟩ : syracuseStep 2789201 = 2091901) B2091901
theorem B2477921 : Blo 1651525 2477921 := bstep (se 2 (by rfl) ⟨929220, by rfl⟩ : syracuseStep 2477921 = 1858441) B1858441
theorem B2477939 : Blo 1651525 2477939 := bstep (se 1 (by rfl) ⟨1858454, by rfl⟩ : syracuseStep 2477939 = 3716909) B3716909
theorem B28225421 : Blo 1651525 28225421 := bstep (se 3 (by rfl) ⟨5292266, by rfl⟩ : syracuseStep 28225421 = 10584533) B10584533
theorem B2477969 : Blo 1651525 2477969 := bstep (se 2 (by rfl) ⟨929238, by rfl⟩ : syracuseStep 2477969 = 1858477) B1858477
theorem B2477987 : Blo 1651525 2477987 := bstep (se 1 (by rfl) ⟨1858490, by rfl⟩ : syracuseStep 2477987 = 3716981) B3716981
theorem B5296049 : Blo 1651525 5296049 := bstep (se 2 (by rfl) ⟨1986018, by rfl⟩ : syracuseStep 5296049 = 3972037) B3972037
theorem B2478017 : Blo 1651525 2478017 := bstep (se 2 (by rfl) ⟨929256, by rfl⟩ : syracuseStep 2478017 = 1858513) B1858513
theorem B4181969 : Blo 1651525 4181969 := bstep (se 2 (by rfl) ⟨1568238, by rfl⟩ : syracuseStep 4181969 = 3136477) B3136477
theorem B2789329 : Blo 1651525 2789329 := bstep (se 2 (by rfl) ⟨1045998, by rfl⟩ : syracuseStep 2789329 = 2091997) B2091997
theorem B2478035 : Blo 1651525 2478035 := bstep (se 1 (by rfl) ⟨1858526, by rfl⟩ : syracuseStep 2478035 = 3717053) B3717053
theorem B9416675 : Blo 1651525 9416675 := bstep (se 1 (by rfl) ⟨7062506, by rfl⟩ : syracuseStep 9416675 = 14125013) B14125013
theorem B2478065 : Blo 1651525 2478065 := bstep (se 2 (by rfl) ⟨929274, by rfl⟩ : syracuseStep 2478065 = 1858549) B1858549
theorem B2789363 : Blo 1651525 2789363 := bstep (se 1 (by rfl) ⟨2092022, by rfl⟩ : syracuseStep 2789363 = 4184045) B4184045
theorem B2478083 : Blo 1651525 2478083 := bstep (se 1 (by rfl) ⟨1858562, by rfl⟩ : syracuseStep 2478083 = 3717125) B3717125
theorem B2478113 : Blo 1651525 2478113 := bstep (se 2 (by rfl) ⟨929292, by rfl⟩ : syracuseStep 2478113 = 1858585) B1858585
theorem B2478131 : Blo 1651525 2478131 := bstep (se 1 (by rfl) ⟨1858598, by rfl⟩ : syracuseStep 2478131 = 3717197) B3717197
theorem B2478161 : Blo 1651525 2478161 := bstep (se 2 (by rfl) ⟨929310, by rfl⟩ : syracuseStep 2478161 = 1858621) B1858621
theorem B2478179 : Blo 1651525 2478179 := bstep (se 1 (by rfl) ⟨1858634, by rfl⟩ : syracuseStep 2478179 = 3717269) B3717269
theorem B2789491 : Blo 1651525 2789491 := bstep (se 1 (by rfl) ⟨2092118, by rfl⟩ : syracuseStep 2789491 = 4184237) B4184237
theorem B2478209 : Blo 1651525 2478209 := bstep (se 2 (by rfl) ⟨929328, by rfl⟩ : syracuseStep 2478209 = 1858657) B1858657
theorem B5574797 : Blo 1651525 5574797 := bstep (se 3 (by rfl) ⟨1045274, by rfl⟩ : syracuseStep 5574797 = 2090549) B2090549
theorem B21188749 : Blo 1651525 21188749 := bstep (se 3 (by rfl) ⟨3972890, by rfl⟩ : syracuseStep 21188749 = 7945781) B7945781
theorem B2478227 : Blo 1651525 2478227 := bstep (se 1 (by rfl) ⟨1858670, by rfl⟩ : syracuseStep 2478227 = 3717341) B3717341
theorem B2478257 : Blo 1651525 2478257 := bstep (se 2 (by rfl) ⟨929346, by rfl⟩ : syracuseStep 2478257 = 1858693) B1858693
theorem B5574851 : Blo 1651525 5574851 := bstep (se 1 (by rfl) ⟨4181138, by rfl⟩ : syracuseStep 5574851 = 8362277) B8362277
theorem B2478275 : Blo 1651525 2478275 := bstep (se 1 (by rfl) ⟨1858706, by rfl⟩ : syracuseStep 2478275 = 3717413) B3717413
theorem B2478305 : Blo 1651525 2478305 := bstep (se 2 (by rfl) ⟨929364, by rfl⟩ : syracuseStep 2478305 = 1858729) B1858729
theorem B6697187 : Blo 1651525 6697187 := bstep (se 1 (by rfl) ⟨5022890, by rfl⟩ : syracuseStep 6697187 = 10045781) B10045781
theorem B2478323 : Blo 1651525 2478323 := bstep (se 1 (by rfl) ⟨1858742, by rfl⟩ : syracuseStep 2478323 = 3717485) B3717485
theorem B2789633 : Blo 1651525 2789633 := bstep (se 2 (by rfl) ⟨1046112, by rfl⟩ : syracuseStep 2789633 = 2092225) B2092225
theorem B2478353 : Blo 1651525 2478353 := bstep (se 2 (by rfl) ⟨929382, by rfl⟩ : syracuseStep 2478353 = 1858765) B1858765
theorem B2478371 : Blo 1651525 2478371 := bstep (se 1 (by rfl) ⟨1858778, by rfl⟩ : syracuseStep 2478371 = 3717557) B3717557
theorem B8368433 : Blo 1651525 8368433 := bstep (se 2 (by rfl) ⟨3138162, by rfl⟩ : syracuseStep 8368433 = 6276325) B6276325
theorem B2478401 : Blo 1651525 2478401 := bstep (se 2 (by rfl) ⟨929400, by rfl⟩ : syracuseStep 2478401 = 1858801) B1858801
theorem B2478419 : Blo 1651525 2478419 := bstep (se 1 (by rfl) ⟨1858814, by rfl⟩ : syracuseStep 2478419 = 3717629) B3717629
theorem B2478449 : Blo 1651525 2478449 := bstep (se 2 (by rfl) ⟨929418, by rfl⟩ : syracuseStep 2478449 = 1858837) B1858837
theorem B2789761 : Blo 1651525 2789761 := bstep (se 2 (by rfl) ⟨1046160, by rfl⟩ : syracuseStep 2789761 = 2092321) B2092321
theorem B2478467 : Blo 1651525 2478467 := bstep (se 1 (by rfl) ⟨1858850, by rfl⟩ : syracuseStep 2478467 = 3717701) B3717701
theorem B2478497 : Blo 1651525 2478497 := bstep (se 2 (by rfl) ⟨929436, by rfl⟩ : syracuseStep 2478497 = 1858873) B1858873
theorem B2789795 : Blo 1651525 2789795 := bstep (se 1 (by rfl) ⟨2092346, by rfl⟩ : syracuseStep 2789795 = 4184693) B4184693
theorem B2478515 : Blo 1651525 2478515 := bstep (se 1 (by rfl) ⟨1858886, by rfl⟩ : syracuseStep 2478515 = 3717773) B3717773
theorem B5575121 : Blo 1651525 5575121 := bstep (se 2 (by rfl) ⟨2090670, by rfl⟩ : syracuseStep 5575121 = 4181341) B4181341
theorem B2478545 : Blo 1651525 2478545 := bstep (se 2 (by rfl) ⟨929454, by rfl⟩ : syracuseStep 2478545 = 1858909) B1858909
theorem B2478563 : Blo 1651525 2478563 := bstep (se 1 (by rfl) ⟨1858922, by rfl⟩ : syracuseStep 2478563 = 3717845) B3717845
theorem B2478593 : Blo 1651525 2478593 := bstep (se 2 (by rfl) ⟨929472, by rfl⟩ : syracuseStep 2478593 = 1858945) B1858945
theorem B11301389 : Blo 1651525 11301389 := bstep (se 3 (by rfl) ⟨2119010, by rfl⟩ : syracuseStep 11301389 = 4238021) B4238021
theorem B10048013 : Blo 1651525 10048013 := bstep (se 3 (by rfl) ⟨1884002, by rfl⟩ : syracuseStep 10048013 = 3768005) B3768005
theorem B2478611 : Blo 1651525 2478611 := bstep (se 1 (by rfl) ⟨1858958, by rfl⟩ : syracuseStep 2478611 = 3717917) B3717917
theorem B6697507 : Blo 1651525 6697507 := bstep (se 1 (by rfl) ⟨5023130, by rfl⟩ : syracuseStep 6697507 = 10046261) B10046261
theorem B2789923 : Blo 1651525 2789923 := bstep (se 1 (by rfl) ⟨2092442, by rfl⟩ : syracuseStep 2789923 = 4184885) B4184885
theorem B2478641 : Blo 1651525 2478641 := bstep (se 2 (by rfl) ⟨929490, by rfl⟩ : syracuseStep 2478641 = 1858981) B1858981
theorem B2478659 : Blo 1651525 2478659 := bstep (se 1 (by rfl) ⟨1858994, by rfl⟩ : syracuseStep 2478659 = 3717989) B3717989
theorem B2478689 : Blo 1651525 2478689 := bstep (se 2 (by rfl) ⟨929508, by rfl⟩ : syracuseStep 2478689 = 1859017) B1859017
theorem B2478707 : Blo 1651525 2478707 := bstep (se 1 (by rfl) ⟨1859030, by rfl⟩ : syracuseStep 2478707 = 3718061) B3718061
theorem B2478737 : Blo 1651525 2478737 := bstep (se 2 (by rfl) ⟨929526, by rfl⟩ : syracuseStep 2478737 = 1859053) B1859053
theorem B2478755 : Blo 1651525 2478755 := bstep (se 1 (by rfl) ⟨1859066, by rfl⟩ : syracuseStep 2478755 = 3718133) B3718133
theorem B8164003 : Blo 1651525 8164003 := bstep (se 1 (by rfl) ⟨6123002, by rfl⟩ : syracuseStep 8164003 = 12246005) B12246005
theorem B2790065 : Blo 1651525 2790065 := bstep (se 2 (by rfl) ⟨1046274, by rfl⟩ : syracuseStep 2790065 = 2092549) B2092549
theorem B2478785 : Blo 1651525 2478785 := bstep (se 2 (by rfl) ⟨929544, by rfl⟩ : syracuseStep 2478785 = 1859089) B1859089
theorem B2478803 : Blo 1651525 2478803 := bstep (se 1 (by rfl) ⟨1859102, by rfl⟩ : syracuseStep 2478803 = 3718205) B3718205
theorem B2478833 : Blo 1651525 2478833 := bstep (se 2 (by rfl) ⟨929562, by rfl⟩ : syracuseStep 2478833 = 1859125) B1859125
theorem B2478851 : Blo 1651525 2478851 := bstep (se 1 (by rfl) ⟨1859138, by rfl⟩ : syracuseStep 2478851 = 3718277) B3718277
theorem B4707085 : Blo 1651525 4707085 := bstep (se 3 (by rfl) ⟨882578, by rfl⟩ : syracuseStep 4707085 = 1765157) B1765157
theorem B2478881 : Blo 1651525 2478881 := bstep (se 2 (by rfl) ⟨929580, by rfl⟩ : syracuseStep 2478881 = 1859161) B1859161
theorem B2790193 : Blo 1651525 2790193 := bstep (se 2 (by rfl) ⟨1046322, by rfl⟩ : syracuseStep 2790193 = 2092645) B2092645
theorem B2478899 : Blo 1651525 2478899 := bstep (se 1 (by rfl) ⟨1859174, by rfl⟩ : syracuseStep 2478899 = 3718349) B3718349
theorem B2478929 : Blo 1651525 2478929 := bstep (se 2 (by rfl) ⟨929598, by rfl⟩ : syracuseStep 2478929 = 1859197) B1859197
theorem B1651539 : Blo 1651525 1651539 := bstep (se 1 (by rfl) ⟨1238654, by rfl⟩ : syracuseStep 1651539 = 2477309) B2477309
theorem B2790227 : Blo 1651525 2790227 := bstep (se 1 (by rfl) ⟨2092670, by rfl⟩ : syracuseStep 2790227 = 4185341) B4185341
theorem B1651555 : Blo 1651525 1651555 := bstep (se 1 (by rfl) ⟨1238666, by rfl⟩ : syracuseStep 1651555 = 2477333) B2477333
theorem B2478947 : Blo 1651525 2478947 := bstep (se 1 (by rfl) ⟨1859210, by rfl⟩ : syracuseStep 2478947 = 3718421) B3718421
theorem B15872881 : Blo 1651525 15872881 := bstep (se 2 (by rfl) ⟨5952330, by rfl⟩ : syracuseStep 15872881 = 11904661) B11904661
theorem B1651571 : Blo 1651525 1651571 := bstep (se 1 (by rfl) ⟨1238678, by rfl⟩ : syracuseStep 1651571 = 2477357) B2477357
theorem B1651587 : Blo 1651525 1651587 := bstep (se 1 (by rfl) ⟨1238690, by rfl⟩ : syracuseStep 1651587 = 2477381) B2477381
theorem B2478977 : Blo 1651525 2478977 := bstep (se 2 (by rfl) ⟨929616, by rfl⟩ : syracuseStep 2478977 = 1859233) B1859233
theorem B1651603 : Blo 1651525 1651603 := bstep (se 1 (by rfl) ⟨1238702, by rfl⟩ : syracuseStep 1651603 = 2477405) B2477405
theorem B2478995 : Blo 1651525 2478995 := bstep (se 1 (by rfl) ⟨1859246, by rfl⟩ : syracuseStep 2478995 = 3718493) B3718493
theorem B1651619 : Blo 1651525 1651619 := bstep (se 1 (by rfl) ⟨1238714, by rfl⟩ : syracuseStep 1651619 = 2477429) B2477429
theorem B7058339 : Blo 1651525 7058339 := bstep (se 1 (by rfl) ⟨5293754, by rfl⟩ : syracuseStep 7058339 = 10587509) B10587509
theorem B4182961 : Blo 1651525 4182961 := bstep (se 2 (by rfl) ⟨1568610, by rfl⟩ : syracuseStep 4182961 = 3137221) B3137221
theorem B2479025 : Blo 1651525 2479025 := bstep (se 2 (by rfl) ⟨929634, by rfl⟩ : syracuseStep 2479025 = 1859269) B1859269
theorem B1651635 : Blo 1651525 1651635 := bstep (se 1 (by rfl) ⟨1238726, by rfl⟩ : syracuseStep 1651635 = 2477453) B2477453
theorem B1651651 : Blo 1651525 1651651 := bstep (se 1 (by rfl) ⟨1238738, by rfl⟩ : syracuseStep 1651651 = 2477477) B2477477
theorem B2479043 : Blo 1651525 2479043 := bstep (se 1 (by rfl) ⟨1859282, by rfl⟩ : syracuseStep 2479043 = 3718565) B3718565
theorem B31765445 : Blo 1651525 31765445 := bstep (se 4 (by rfl) ⟨2978010, by rfl⟩ : syracuseStep 31765445 = 5956021) B5956021
theorem B1651667 : Blo 1651525 1651667 := bstep (se 1 (by rfl) ⟨1238750, by rfl⟩ : syracuseStep 1651667 = 2477501) B2477501
theorem B2479073 : Blo 1651525 2479073 := bstep (se 2 (by rfl) ⟨929652, by rfl⟩ : syracuseStep 2479073 = 1859305) B1859305
theorem B1651683 : Blo 1651525 1651683 := bstep (se 1 (by rfl) ⟨1238762, by rfl⟩ : syracuseStep 1651683 = 2477525) B2477525
theorem B5575661 : Blo 1651525 5575661 := bstep (se 3 (by rfl) ⟨1045436, by rfl⟩ : syracuseStep 5575661 = 2090873) B2090873
theorem B3716081 : Blo 1651525 3716081 := bstep (se 2 (by rfl) ⟨1393530, by rfl⟩ : syracuseStep 3716081 = 2787061) B2787061
theorem B1651699 : Blo 1651525 1651699 := bstep (se 1 (by rfl) ⟨1238774, by rfl⟩ : syracuseStep 1651699 = 2477549) B2477549
theorem B2479091 : Blo 1651525 2479091 := bstep (se 1 (by rfl) ⟨1859318, by rfl⟩ : syracuseStep 2479091 = 3718637) B3718637
theorem B3716099 : Blo 1651525 3716099 := bstep (se 1 (by rfl) ⟨2787074, by rfl⟩ : syracuseStep 3716099 = 5574149) B5574149
theorem B1651715 : Blo 1651525 1651715 := bstep (se 1 (by rfl) ⟨1238786, by rfl⟩ : syracuseStep 1651715 = 2477573) B2477573
theorem B2479121 : Blo 1651525 2479121 := bstep (se 2 (by rfl) ⟨929670, by rfl⟩ : syracuseStep 2479121 = 1859341) B1859341
theorem B1651731 : Blo 1651525 1651731 := bstep (se 1 (by rfl) ⟨1238798, by rfl⟩ : syracuseStep 1651731 = 2477597) B2477597
theorem B1651747 : Blo 1651525 1651747 := bstep (se 1 (by rfl) ⟨1238810, by rfl⟩ : syracuseStep 1651747 = 2477621) B2477621
theorem B5575715 : Blo 1651525 5575715 := bstep (se 1 (by rfl) ⟨4181786, by rfl⟩ : syracuseStep 5575715 = 8363573) B8363573
theorem B2479139 : Blo 1651525 2479139 := bstep (se 1 (by rfl) ⟨1859354, by rfl⟩ : syracuseStep 2479139 = 3718709) B3718709
theorem B3019825 : Blo 1651525 3019825 := bstep (se 2 (by rfl) ⟨1132434, by rfl⟩ : syracuseStep 3019825 = 2264869) B2264869
theorem B1651763 : Blo 1651525 1651763 := bstep (se 1 (by rfl) ⟨1238822, by rfl⟩ : syracuseStep 1651763 = 2477645) B2477645
theorem B2479169 : Blo 1651525 2479169 := bstep (se 2 (by rfl) ⟨929688, by rfl⟩ : syracuseStep 2479169 = 1859377) B1859377
theorem B1651779 : Blo 1651525 1651779 := bstep (se 1 (by rfl) ⟨1238834, by rfl⟩ : syracuseStep 1651779 = 2477669) B2477669
theorem B1651795 : Blo 1651525 1651795 := bstep (se 1 (by rfl) ⟨1238846, by rfl⟩ : syracuseStep 1651795 = 2477693) B2477693
theorem B2479187 : Blo 1651525 2479187 := bstep (se 1 (by rfl) ⟨1859390, by rfl⟩ : syracuseStep 2479187 = 3718781) B3718781
theorem B1651811 : Blo 1651525 1651811 := bstep (se 1 (by rfl) ⟨1238858, by rfl⟩ : syracuseStep 1651811 = 2477717) B2477717
theorem B2479217 : Blo 1651525 2479217 := bstep (se 2 (by rfl) ⟨929706, by rfl⟩ : syracuseStep 2479217 = 1859413) B1859413
theorem B1651827 : Blo 1651525 1651827 := bstep (se 1 (by rfl) ⟨1238870, by rfl⟩ : syracuseStep 1651827 = 2477741) B2477741
theorem B2864243 : Blo 1651525 2864243 := bstep (se 1 (by rfl) ⟨2148182, by rfl⟩ : syracuseStep 2864243 = 4296365) B4296365
theorem B1651843 : Blo 1651525 1651843 := bstep (se 1 (by rfl) ⟨1238882, by rfl⟩ : syracuseStep 1651843 = 2477765) B2477765
theorem B2479235 : Blo 1651525 2479235 := bstep (se 1 (by rfl) ⟨1859426, by rfl⟩ : syracuseStep 2479235 = 3718853) B3718853
theorem B1651859 : Blo 1651525 1651859 := bstep (se 1 (by rfl) ⟨1238894, by rfl⟩ : syracuseStep 1651859 = 2477789) B2477789
theorem B2479265 : Blo 1651525 2479265 := bstep (se 2 (by rfl) ⟨929724, by rfl⟩ : syracuseStep 2479265 = 1859449) B1859449
theorem B1651875 : Blo 1651525 1651875 := bstep (se 1 (by rfl) ⟨1238906, by rfl⟩ : syracuseStep 1651875 = 2477813) B2477813
theorem B1651891 : Blo 1651525 1651891 := bstep (se 1 (by rfl) ⟨1238918, by rfl⟩ : syracuseStep 1651891 = 2477837) B2477837
theorem B2479283 : Blo 1651525 2479283 := bstep (se 1 (by rfl) ⟨1859462, by rfl⟩ : syracuseStep 2479283 = 3718925) B3718925
theorem B1651907 : Blo 1651525 1651907 := bstep (se 1 (by rfl) ⟨1238930, by rfl⟩ : syracuseStep 1651907 = 2477861) B2477861
theorem B4183235 : Blo 1651525 4183235 := bstep (se 1 (by rfl) ⟨3137426, by rfl⟩ : syracuseStep 4183235 = 6274853) B6274853
theorem B2479313 : Blo 1651525 2479313 := bstep (se 2 (by rfl) ⟨929742, by rfl⟩ : syracuseStep 2479313 = 1859485) B1859485
theorem B1651923 : Blo 1651525 1651923 := bstep (se 1 (by rfl) ⟨1238942, by rfl⟩ : syracuseStep 1651923 = 2477885) B2477885
theorem B1651939 : Blo 1651525 1651939 := bstep (se 1 (by rfl) ⟨1238954, by rfl⟩ : syracuseStep 1651939 = 2477909) B2477909
theorem B2479331 : Blo 1651525 2479331 := bstep (se 1 (by rfl) ⟨1859498, by rfl⟩ : syracuseStep 2479331 = 3718997) B3718997
theorem B1651955 : Blo 1651525 1651955 := bstep (se 1 (by rfl) ⟨1238966, by rfl⟩ : syracuseStep 1651955 = 2477933) B2477933
theorem B2479361 : Blo 1651525 2479361 := bstep (se 2 (by rfl) ⟨929760, by rfl⟩ : syracuseStep 2479361 = 1859521) B1859521
theorem B1651971 : Blo 1651525 1651971 := bstep (se 1 (by rfl) ⟨1238978, by rfl⟩ : syracuseStep 1651971 = 2477957) B2477957
theorem B3716369 : Blo 1651525 3716369 := bstep (se 2 (by rfl) ⟨1393638, by rfl⟩ : syracuseStep 3716369 = 2787277) B2787277
theorem B1651987 : Blo 1651525 1651987 := bstep (se 1 (by rfl) ⟨1238990, by rfl⟩ : syracuseStep 1651987 = 2477981) B2477981
theorem B2479379 : Blo 1651525 2479379 := bstep (se 1 (by rfl) ⟨1859534, by rfl⟩ : syracuseStep 2479379 = 3719069) B3719069
theorem B3716387 : Blo 1651525 3716387 := bstep (se 1 (by rfl) ⟨2787290, by rfl⟩ : syracuseStep 3716387 = 5574581) B5574581
theorem B1652003 : Blo 1651525 1652003 := bstep (se 1 (by rfl) ⟨1239002, by rfl⟩ : syracuseStep 1652003 = 2478005) B2478005
theorem B5575985 : Blo 1651525 5575985 := bstep (se 2 (by rfl) ⟨2090994, by rfl⟩ : syracuseStep 5575985 = 4181989) B4181989
theorem B9409841 : Blo 1651525 9409841 := bstep (se 2 (by rfl) ⟨3528690, by rfl⟩ : syracuseStep 9409841 = 7057381) B7057381
theorem B1652019 : Blo 1651525 1652019 := bstep (se 1 (by rfl) ⟨1239014, by rfl⟩ : syracuseStep 1652019 = 2478029) B2478029
theorem B2479409 : Blo 1651525 2479409 := bstep (se 2 (by rfl) ⟨929778, by rfl⟩ : syracuseStep 2479409 = 1859557) B1859557
theorem B1652035 : Blo 1651525 1652035 := bstep (se 1 (by rfl) ⟨1239026, by rfl⟩ : syracuseStep 1652035 = 2478053) B2478053
theorem B2479427 : Blo 1651525 2479427 := bstep (se 1 (by rfl) ⟨1859570, by rfl⟩ : syracuseStep 2479427 = 3719141) B3719141
theorem B1652051 : Blo 1651525 1652051 := bstep (se 1 (by rfl) ⟨1239038, by rfl⟩ : syracuseStep 1652051 = 2478077) B2478077
theorem B2479457 : Blo 1651525 2479457 := bstep (se 2 (by rfl) ⟨929796, by rfl⟩ : syracuseStep 2479457 = 1859593) B1859593
theorem B1652067 : Blo 1651525 1652067 := bstep (se 1 (by rfl) ⟨1239050, by rfl⟩ : syracuseStep 1652067 = 2478101) B2478101
theorem B1652083 : Blo 1651525 1652083 := bstep (se 1 (by rfl) ⟨1239062, by rfl⟩ : syracuseStep 1652083 = 2478125) B2478125
theorem B2479475 : Blo 1651525 2479475 := bstep (se 1 (by rfl) ⟨1859606, by rfl⟩ : syracuseStep 2479475 = 3719213) B3719213
theorem B1652099 : Blo 1651525 1652099 := bstep (se 1 (by rfl) ⟨1239074, by rfl⟩ : syracuseStep 1652099 = 2478149) B2478149
theorem B4183427 : Blo 1651525 4183427 := bstep (se 1 (by rfl) ⟨3137570, by rfl⟩ : syracuseStep 4183427 = 6275141) B6275141
theorem B2479505 : Blo 1651525 2479505 := bstep (se 2 (by rfl) ⟨929814, by rfl⟩ : syracuseStep 2479505 = 1859629) B1859629
theorem B1652115 : Blo 1651525 1652115 := bstep (se 1 (by rfl) ⟨1239086, by rfl⟩ : syracuseStep 1652115 = 2478173) B2478173
theorem B1652131 : Blo 1651525 1652131 := bstep (se 1 (by rfl) ⟨1239098, by rfl⟩ : syracuseStep 1652131 = 2478197) B2478197
theorem B2479523 : Blo 1651525 2479523 := bstep (se 1 (by rfl) ⟨1859642, by rfl⟩ : syracuseStep 2479523 = 3719285) B3719285
theorem B1652147 : Blo 1651525 1652147 := bstep (se 1 (by rfl) ⟨1239110, by rfl⟩ : syracuseStep 1652147 = 2478221) B2478221
theorem B2479553 : Blo 1651525 2479553 := bstep (se 2 (by rfl) ⟨929832, by rfl⟩ : syracuseStep 2479553 = 1859665) B1859665
theorem B1652163 : Blo 1651525 1652163 := bstep (se 1 (by rfl) ⟨1239122, by rfl⟩ : syracuseStep 1652163 = 2478245) B2478245
theorem B7943629 : Blo 1651525 7943629 := bstep (se 3 (by rfl) ⟨1489430, by rfl⟩ : syracuseStep 7943629 = 2978861) B2978861
theorem B1652179 : Blo 1651525 1652179 := bstep (se 1 (by rfl) ⟨1239134, by rfl⟩ : syracuseStep 1652179 = 2478269) B2478269
theorem B2479571 : Blo 1651525 2479571 := bstep (se 1 (by rfl) ⟨1859678, by rfl⟩ : syracuseStep 2479571 = 3719357) B3719357
theorem B1652195 : Blo 1651525 1652195 := bstep (se 1 (by rfl) ⟨1239146, by rfl⟩ : syracuseStep 1652195 = 2478293) B2478293
theorem B2479601 : Blo 1651525 2479601 := bstep (se 2 (by rfl) ⟨929850, by rfl⟩ : syracuseStep 2479601 = 1859701) B1859701
theorem B1652211 : Blo 1651525 1652211 := bstep (se 1 (by rfl) ⟨1239158, by rfl⟩ : syracuseStep 1652211 = 2478317) B2478317
theorem B1652227 : Blo 1651525 1652227 := bstep (se 1 (by rfl) ⟨1239170, by rfl⟩ : syracuseStep 1652227 = 2478341) B2478341
theorem B2479619 : Blo 1651525 2479619 := bstep (se 1 (by rfl) ⟨1859714, by rfl⟩ : syracuseStep 2479619 = 3719429) B3719429
theorem B1652243 : Blo 1651525 1652243 := bstep (se 1 (by rfl) ⟨1239182, by rfl⟩ : syracuseStep 1652243 = 2478365) B2478365
theorem B2479649 : Blo 1651525 2479649 := bstep (se 2 (by rfl) ⟨929868, by rfl⟩ : syracuseStep 2479649 = 1859737) B1859737
theorem B1652259 : Blo 1651525 1652259 := bstep (se 1 (by rfl) ⟨1239194, by rfl⟩ : syracuseStep 1652259 = 2478389) B2478389
theorem B3716657 : Blo 1651525 3716657 := bstep (se 2 (by rfl) ⟨1393746, by rfl⟩ : syracuseStep 3716657 = 2787493) B2787493
theorem B11310641 : Blo 1651525 11310641 := bstep (se 2 (by rfl) ⟨4241490, by rfl⟩ : syracuseStep 11310641 = 8482981) B8482981
theorem B1652275 : Blo 1651525 1652275 := bstep (se 1 (by rfl) ⟨1239206, by rfl⟩ : syracuseStep 1652275 = 2478413) B2478413
theorem B2479667 : Blo 1651525 2479667 := bstep (se 1 (by rfl) ⟨1859750, by rfl⟩ : syracuseStep 2479667 = 3719501) B3719501
theorem B3716675 : Blo 1651525 3716675 := bstep (se 1 (by rfl) ⟨2787506, by rfl⟩ : syracuseStep 3716675 = 5575013) B5575013
theorem B1652291 : Blo 1651525 1652291 := bstep (se 1 (by rfl) ⟨1239218, by rfl⟩ : syracuseStep 1652291 = 2478437) B2478437
theorem B2479697 : Blo 1651525 2479697 := bstep (se 2 (by rfl) ⟨929886, by rfl⟩ : syracuseStep 2479697 = 1859773) B1859773
theorem B1652307 : Blo 1651525 1652307 := bstep (se 1 (by rfl) ⟨1239230, by rfl⟩ : syracuseStep 1652307 = 2478461) B2478461
theorem B1652323 : Blo 1651525 1652323 := bstep (se 1 (by rfl) ⟨1239242, by rfl⟩ : syracuseStep 1652323 = 2478485) B2478485
theorem B2479715 : Blo 1651525 2479715 := bstep (se 1 (by rfl) ⟨1859786, by rfl⟩ : syracuseStep 2479715 = 3719573) B3719573
theorem B1652339 : Blo 1651525 1652339 := bstep (se 1 (by rfl) ⟨1239254, by rfl⟩ : syracuseStep 1652339 = 2478509) B2478509
theorem B2479745 : Blo 1651525 2479745 := bstep (se 2 (by rfl) ⟨929904, by rfl⟩ : syracuseStep 2479745 = 1859809) B1859809
theorem B1652355 : Blo 1651525 1652355 := bstep (se 1 (by rfl) ⟨1239266, by rfl⟩ : syracuseStep 1652355 = 2478533) B2478533
theorem B1652371 : Blo 1651525 1652371 := bstep (se 1 (by rfl) ⟨1239278, by rfl⟩ : syracuseStep 1652371 = 2478557) B2478557
theorem B2479763 : Blo 1651525 2479763 := bstep (se 1 (by rfl) ⟨1859822, by rfl⟩ : syracuseStep 2479763 = 3719645) B3719645
theorem B2234017 : Blo 1651525 2234017 := bstep (se 2 (by rfl) ⟨837756, by rfl⟩ : syracuseStep 2234017 = 1675513) B1675513
theorem B1652387 : Blo 1651525 1652387 := bstep (se 1 (by rfl) ⟨1239290, by rfl⟩ : syracuseStep 1652387 = 2478581) B2478581
theorem B2479793 : Blo 1651525 2479793 := bstep (se 2 (by rfl) ⟨929922, by rfl⟩ : syracuseStep 2479793 = 1859845) B1859845
theorem B1652403 : Blo 1651525 1652403 := bstep (se 1 (by rfl) ⟨1239302, by rfl⟩ : syracuseStep 1652403 = 2478605) B2478605
theorem B1652419 : Blo 1651525 1652419 := bstep (se 1 (by rfl) ⟨1239314, by rfl⟩ : syracuseStep 1652419 = 2478629) B2478629
theorem B2479811 : Blo 1651525 2479811 := bstep (se 1 (by rfl) ⟨1859858, by rfl⟩ : syracuseStep 2479811 = 3719717) B3719717
theorem B1652435 : Blo 1651525 1652435 := bstep (se 1 (by rfl) ⟨1239326, by rfl⟩ : syracuseStep 1652435 = 2478653) B2478653
theorem B2479841 : Blo 1651525 2479841 := bstep (se 2 (by rfl) ⟨929940, by rfl⟩ : syracuseStep 2479841 = 1859881) B1859881
theorem B21173987 : Blo 1651525 21173987 := bstep (se 1 (by rfl) ⟨15880490, by rfl⟩ : syracuseStep 21173987 = 31760981) B31760981
theorem B1652451 : Blo 1651525 1652451 := bstep (se 1 (by rfl) ⟨1239338, by rfl⟩ : syracuseStep 1652451 = 2478677) B2478677
theorem B8369891 : Blo 1651525 8369891 := bstep (se 1 (by rfl) ⟨6277418, by rfl⟩ : syracuseStep 8369891 = 12554837) B12554837
theorem B1652467 : Blo 1651525 1652467 := bstep (se 1 (by rfl) ⟨1239350, by rfl⟩ : syracuseStep 1652467 = 2478701) B2478701
theorem B2479859 : Blo 1651525 2479859 := bstep (se 1 (by rfl) ⟨1859894, by rfl⟩ : syracuseStep 2479859 = 3719789) B3719789
theorem B3528451 : Blo 1651525 3528451 := bstep (se 1 (by rfl) ⟨2646338, by rfl⟩ : syracuseStep 3528451 = 5292677) B5292677
theorem B1652483 : Blo 1651525 1652483 := bstep (se 1 (by rfl) ⟨1239362, by rfl⟩ : syracuseStep 1652483 = 2478725) B2478725
theorem B2479889 : Blo 1651525 2479889 := bstep (se 2 (by rfl) ⟨929958, by rfl⟩ : syracuseStep 2479889 = 1859917) B1859917
theorem B1652499 : Blo 1651525 1652499 := bstep (se 1 (by rfl) ⟨1239374, by rfl⟩ : syracuseStep 1652499 = 2478749) B2478749
theorem B1652515 : Blo 1651525 1652515 := bstep (se 1 (by rfl) ⟨1239386, by rfl⟩ : syracuseStep 1652515 = 2478773) B2478773
theorem B2479907 : Blo 1651525 2479907 := bstep (se 1 (by rfl) ⟨1859930, by rfl⟩ : syracuseStep 2479907 = 3719861) B3719861
theorem B4708145 : Blo 1651525 4708145 := bstep (se 2 (by rfl) ⟨1765554, by rfl⟩ : syracuseStep 4708145 = 3531109) B3531109
theorem B1652531 : Blo 1651525 1652531 := bstep (se 1 (by rfl) ⟨1239398, by rfl⟩ : syracuseStep 1652531 = 2478797) B2478797
theorem B1652547 : Blo 1651525 1652547 := bstep (se 1 (by rfl) ⟨1239410, by rfl⟩ : syracuseStep 1652547 = 2478821) B2478821
theorem B2479937 : Blo 1651525 2479937 := bstep (se 2 (by rfl) ⟨929976, by rfl⟩ : syracuseStep 2479937 = 1859953) B1859953
theorem B5576525 : Blo 1651525 5576525 := bstep (se 3 (by rfl) ⟨1045598, by rfl⟩ : syracuseStep 5576525 = 2091197) B2091197
theorem B3716945 : Blo 1651525 3716945 := bstep (se 2 (by rfl) ⟨1393854, by rfl⟩ : syracuseStep 3716945 = 2787709) B2787709
theorem B1652563 : Blo 1651525 1652563 := bstep (se 1 (by rfl) ⟨1239422, by rfl⟩ : syracuseStep 1652563 = 2478845) B2478845
theorem B2479955 : Blo 1651525 2479955 := bstep (se 1 (by rfl) ⟨1859966, by rfl⟩ : syracuseStep 2479955 = 3719933) B3719933
theorem B3716963 : Blo 1651525 3716963 := bstep (se 1 (by rfl) ⟨2787722, by rfl⟩ : syracuseStep 3716963 = 5575445) B5575445
theorem B1652579 : Blo 1651525 1652579 := bstep (se 1 (by rfl) ⟨1239434, by rfl⟩ : syracuseStep 1652579 = 2478869) B2478869
theorem B2479985 : Blo 1651525 2479985 := bstep (se 2 (by rfl) ⟨929994, by rfl⟩ : syracuseStep 2479985 = 1859989) B1859989
theorem B1652595 : Blo 1651525 1652595 := bstep (se 1 (by rfl) ⟨1239446, by rfl⟩ : syracuseStep 1652595 = 2478893) B2478893
theorem B5576579 : Blo 1651525 5576579 := bstep (se 1 (by rfl) ⟨4182434, by rfl⟩ : syracuseStep 5576579 = 8364869) B8364869
theorem B1652611 : Blo 1651525 1652611 := bstep (se 1 (by rfl) ⟨1239458, by rfl⟩ : syracuseStep 1652611 = 2478917) B2478917
theorem B2480003 : Blo 1651525 2480003 := bstep (se 1 (by rfl) ⟨1860002, by rfl⟩ : syracuseStep 2480003 = 3720005) B3720005
theorem B6272909 : Blo 1651525 6272909 := bstep (se 3 (by rfl) ⟨1176170, by rfl⟩ : syracuseStep 6272909 = 2352341) B2352341
theorem B8484749 : Blo 1651525 8484749 := bstep (se 3 (by rfl) ⟨1590890, by rfl⟩ : syracuseStep 8484749 = 3181781) B3181781
theorem B1652627 : Blo 1651525 1652627 := bstep (se 1 (by rfl) ⟨1239470, by rfl⟩ : syracuseStep 1652627 = 2478941) B2478941
theorem B2480033 : Blo 1651525 2480033 := bstep (se 2 (by rfl) ⟨930012, by rfl⟩ : syracuseStep 2480033 = 1860025) B1860025
theorem B1652643 : Blo 1651525 1652643 := bstep (se 1 (by rfl) ⟨1239482, by rfl⟩ : syracuseStep 1652643 = 2478965) B2478965
theorem B1652659 : Blo 1651525 1652659 := bstep (se 1 (by rfl) ⟨1239494, by rfl⟩ : syracuseStep 1652659 = 2478989) B2478989
theorem B2480051 : Blo 1651525 2480051 := bstep (se 1 (by rfl) ⟨1860038, by rfl⟩ : syracuseStep 2480051 = 3720077) B3720077
theorem B1652675 : Blo 1651525 1652675 := bstep (se 1 (by rfl) ⟨1239506, by rfl⟩ : syracuseStep 1652675 = 2479013) B2479013
theorem B2480081 : Blo 1651525 2480081 := bstep (se 2 (by rfl) ⟨930030, by rfl⟩ : syracuseStep 2480081 = 1860061) B1860061
theorem B1652691 : Blo 1651525 1652691 := bstep (se 1 (by rfl) ⟨1239518, by rfl⟩ : syracuseStep 1652691 = 2479037) B2479037
theorem B1652707 : Blo 1651525 1652707 := bstep (se 1 (by rfl) ⟨1239530, by rfl⟩ : syracuseStep 1652707 = 2479061) B2479061
theorem B2480099 : Blo 1651525 2480099 := bstep (se 1 (by rfl) ⟨1860074, by rfl⟩ : syracuseStep 2480099 = 3720149) B3720149
theorem B11909105 : Blo 1651525 11909105 := bstep (se 2 (by rfl) ⟨4465914, by rfl⟩ : syracuseStep 11909105 = 8931829) B8931829
theorem B1652723 : Blo 1651525 1652723 := bstep (se 1 (by rfl) ⟨1239542, by rfl⟩ : syracuseStep 1652723 = 2479085) B2479085
theorem B2480129 : Blo 1651525 2480129 := bstep (se 2 (by rfl) ⟨930048, by rfl⟩ : syracuseStep 2480129 = 1860097) B1860097
theorem B1652739 : Blo 1651525 1652739 := bstep (se 1 (by rfl) ⟨1239554, by rfl⟩ : syracuseStep 1652739 = 2479109) B2479109
theorem B3135505 : Blo 1651525 3135505 := bstep (se 2 (by rfl) ⟨1175814, by rfl⟩ : syracuseStep 3135505 = 2351629) B2351629
theorem B1652755 : Blo 1651525 1652755 := bstep (se 1 (by rfl) ⟨1239566, by rfl⟩ : syracuseStep 1652755 = 2479133) B2479133
theorem B2480147 : Blo 1651525 2480147 := bstep (se 1 (by rfl) ⟨1860110, by rfl⟩ : syracuseStep 2480147 = 3720221) B3720221
theorem B5953571 : Blo 1651525 5953571 := bstep (se 1 (by rfl) ⟨4465178, by rfl⟩ : syracuseStep 5953571 = 8930357) B8930357
theorem B1652771 : Blo 1651525 1652771 := bstep (se 1 (by rfl) ⟨1239578, by rfl⟩ : syracuseStep 1652771 = 2479157) B2479157
theorem B2480177 : Blo 1651525 2480177 := bstep (se 2 (by rfl) ⟨930066, by rfl⟩ : syracuseStep 2480177 = 1860133) B1860133
theorem B1652787 : Blo 1651525 1652787 := bstep (se 1 (by rfl) ⟨1239590, by rfl⟩ : syracuseStep 1652787 = 2479181) B2479181
theorem B1652803 : Blo 1651525 1652803 := bstep (se 1 (by rfl) ⟨1239602, by rfl⟩ : syracuseStep 1652803 = 2479205) B2479205
theorem B2480195 : Blo 1651525 2480195 := bstep (se 1 (by rfl) ⟨1860146, by rfl⟩ : syracuseStep 2480195 = 3720293) B3720293
theorem B3528785 : Blo 1651525 3528785 := bstep (se 2 (by rfl) ⟨1323294, by rfl⟩ : syracuseStep 3528785 = 2646589) B2646589
theorem B1652819 : Blo 1651525 1652819 := bstep (se 1 (by rfl) ⟨1239614, by rfl⟩ : syracuseStep 1652819 = 2479229) B2479229
theorem B2480225 : Blo 1651525 2480225 := bstep (se 2 (by rfl) ⟨930084, by rfl⟩ : syracuseStep 2480225 = 1860169) B1860169
theorem B1652835 : Blo 1651525 1652835 := bstep (se 1 (by rfl) ⟨1239626, by rfl⟩ : syracuseStep 1652835 = 2479253) B2479253
theorem B3717233 : Blo 1651525 3717233 := bstep (se 2 (by rfl) ⟨1393962, by rfl⟩ : syracuseStep 3717233 = 2787925) B2787925
theorem B1652851 : Blo 1651525 1652851 := bstep (se 1 (by rfl) ⟨1239638, by rfl⟩ : syracuseStep 1652851 = 2479277) B2479277
theorem B2480243 : Blo 1651525 2480243 := bstep (se 1 (by rfl) ⟨1860182, by rfl⟩ : syracuseStep 2480243 = 3720365) B3720365
theorem B3717251 : Blo 1651525 3717251 := bstep (se 1 (by rfl) ⟨2787938, by rfl⟩ : syracuseStep 3717251 = 5575877) B5575877
theorem B1652867 : Blo 1651525 1652867 := bstep (se 1 (by rfl) ⟨1239650, by rfl⟩ : syracuseStep 1652867 = 2479301) B2479301
theorem B5576849 : Blo 1651525 5576849 := bstep (se 2 (by rfl) ⟨2091318, by rfl⟩ : syracuseStep 5576849 = 4182637) B4182637
theorem B1652883 : Blo 1651525 1652883 := bstep (se 1 (by rfl) ⟨1239662, by rfl⟩ : syracuseStep 1652883 = 2479325) B2479325
theorem B2480273 : Blo 1651525 2480273 := bstep (se 2 (by rfl) ⟨930102, by rfl⟩ : syracuseStep 2480273 = 1860205) B1860205
theorem B1652899 : Blo 1651525 1652899 := bstep (se 1 (by rfl) ⟨1239674, by rfl⟩ : syracuseStep 1652899 = 2479349) B2479349
theorem B3135665 : Blo 1651525 3135665 := bstep (se 2 (by rfl) ⟨1175874, by rfl⟩ : syracuseStep 3135665 = 2351749) B2351749
theorem B1652915 : Blo 1651525 1652915 := bstep (se 1 (by rfl) ⟨1239686, by rfl⟩ : syracuseStep 1652915 = 2479373) B2479373
theorem B1652931 : Blo 1651525 1652931 := bstep (se 1 (by rfl) ⟨1239698, by rfl⟩ : syracuseStep 1652931 = 2479397) B2479397
theorem B1652947 : Blo 1651525 1652947 := bstep (se 1 (by rfl) ⟨1239710, by rfl⟩ : syracuseStep 1652947 = 2479421) B2479421
theorem B2513123 : Blo 1651525 2513123 := bstep (se 1 (by rfl) ⟨1884842, by rfl⟩ : syracuseStep 2513123 = 3769685) B3769685
theorem B1652963 : Blo 1651525 1652963 := bstep (se 1 (by rfl) ⟨1239722, by rfl⟩ : syracuseStep 1652963 = 2479445) B2479445
theorem B30161123 : Blo 1651525 30161123 := bstep (se 1 (by rfl) ⟨22620842, by rfl⟩ : syracuseStep 30161123 = 45241685) B45241685
theorem B1652979 : Blo 1651525 1652979 := bstep (se 1 (by rfl) ⟨1239734, by rfl⟩ : syracuseStep 1652979 = 2479469) B2479469
theorem B1652995 : Blo 1651525 1652995 := bstep (se 1 (by rfl) ⟨1239746, by rfl⟩ : syracuseStep 1652995 = 2479493) B2479493
theorem B1653011 : Blo 1651525 1653011 := bstep (se 1 (by rfl) ⟨1239758, by rfl⟩ : syracuseStep 1653011 = 2479517) B2479517
theorem B7534883 : Blo 1651525 7534883 := bstep (se 1 (by rfl) ⟨5651162, by rfl⟩ : syracuseStep 7534883 = 11302325) B11302325
theorem B1653027 : Blo 1651525 1653027 := bstep (se 1 (by rfl) ⟨1239770, by rfl⟩ : syracuseStep 1653027 = 2479541) B2479541
theorem B4184369 : Blo 1651525 4184369 := bstep (se 2 (by rfl) ⟨1569138, by rfl⟩ : syracuseStep 4184369 = 3138277) B3138277
theorem B1653043 : Blo 1651525 1653043 := bstep (se 1 (by rfl) ⟨1239782, by rfl⟩ : syracuseStep 1653043 = 2479565) B2479565
theorem B1653059 : Blo 1651525 1653059 := bstep (se 1 (by rfl) ⟨1239794, by rfl⟩ : syracuseStep 1653059 = 2479589) B2479589
theorem B10590533 : Blo 1651525 10590533 := bstep (se 4 (by rfl) ⟨992862, by rfl⟩ : syracuseStep 10590533 = 1985725) B1985725
theorem B11917637 : Blo 1651525 11917637 := bstep (se 4 (by rfl) ⟨1117278, by rfl⟩ : syracuseStep 11917637 = 2234557) B2234557
theorem B1653075 : Blo 1651525 1653075 := bstep (se 1 (by rfl) ⟨1239806, by rfl⟩ : syracuseStep 1653075 = 2479613) B2479613
theorem B1653091 : Blo 1651525 1653091 := bstep (se 1 (by rfl) ⟨1239818, by rfl⟩ : syracuseStep 1653091 = 2479637) B2479637
theorem B4184419 : Blo 1651525 4184419 := bstep (se 1 (by rfl) ⟨3138314, by rfl⟩ : syracuseStep 4184419 = 6276629) B6276629
theorem B1653107 : Blo 1651525 1653107 := bstep (se 1 (by rfl) ⟨1239830, by rfl⟩ : syracuseStep 1653107 = 2479661) B2479661
theorem B1653123 : Blo 1651525 1653123 := bstep (se 1 (by rfl) ⟨1239842, by rfl⟩ : syracuseStep 1653123 = 2479685) B2479685
theorem B3717521 : Blo 1651525 3717521 := bstep (se 2 (by rfl) ⟨1394070, by rfl⟩ : syracuseStep 3717521 = 2788141) B2788141
theorem B1653139 : Blo 1651525 1653139 := bstep (se 1 (by rfl) ⟨1239854, by rfl⟩ : syracuseStep 1653139 = 2479709) B2479709
theorem B3717539 : Blo 1651525 3717539 := bstep (se 1 (by rfl) ⟨2788154, by rfl⟩ : syracuseStep 3717539 = 5576309) B5576309
theorem B2120099 : Blo 1651525 2120099 := bstep (se 1 (by rfl) ⟨1590074, by rfl⟩ : syracuseStep 2120099 = 3180149) B3180149
theorem B1653155 : Blo 1651525 1653155 := bstep (se 1 (by rfl) ⟨1239866, by rfl⟩ : syracuseStep 1653155 = 2479733) B2479733
theorem B1653171 : Blo 1651525 1653171 := bstep (se 1 (by rfl) ⟨1239878, by rfl⟩ : syracuseStep 1653171 = 2479757) B2479757
theorem B1653187 : Blo 1651525 1653187 := bstep (se 1 (by rfl) ⟨1239890, by rfl⟩ : syracuseStep 1653187 = 2479781) B2479781
theorem B1653203 : Blo 1651525 1653203 := bstep (se 1 (by rfl) ⟨1239902, by rfl⟩ : syracuseStep 1653203 = 2479805) B2479805
theorem B1653219 : Blo 1651525 1653219 := bstep (se 1 (by rfl) ⟨1239914, by rfl⟩ : syracuseStep 1653219 = 2479829) B2479829
theorem B4184561 : Blo 1651525 4184561 := bstep (se 2 (by rfl) ⟨1569210, by rfl⟩ : syracuseStep 4184561 = 3138421) B3138421
theorem B1653235 : Blo 1651525 1653235 := bstep (se 1 (by rfl) ⟨1239926, by rfl⟩ : syracuseStep 1653235 = 2479853) B2479853
theorem B1653251 : Blo 1651525 1653251 := bstep (se 1 (by rfl) ⟨1239938, by rfl⟩ : syracuseStep 1653251 = 2479877) B2479877
theorem B8370701 : Blo 1651525 8370701 := bstep (se 3 (by rfl) ⟨1569506, by rfl⟩ : syracuseStep 8370701 = 3139013) B3139013
theorem B1653267 : Blo 1651525 1653267 := bstep (se 1 (by rfl) ⟨1239950, by rfl⟩ : syracuseStep 1653267 = 2479901) B2479901
theorem B1653283 : Blo 1651525 1653283 := bstep (se 1 (by rfl) ⟨1239962, by rfl⟩ : syracuseStep 1653283 = 2479925) B2479925
theorem B1858099 : Blo 1651525 1858099 := bstep (se 1 (by rfl) ⟨1393574, by rfl⟩ : syracuseStep 1858099 = 2787149) B2787149
theorem B1653299 : Blo 1651525 1653299 := bstep (se 1 (by rfl) ⟨1239974, by rfl⟩ : syracuseStep 1653299 = 2479949) B2479949
theorem B3136067 : Blo 1651525 3136067 := bstep (se 1 (by rfl) ⟨2352050, by rfl⟩ : syracuseStep 3136067 = 4704101) B4704101
theorem B1653315 : Blo 1651525 1653315 := bstep (se 1 (by rfl) ⟨1239986, by rfl⟩ : syracuseStep 1653315 = 2479973) B2479973
theorem B1653331 : Blo 1651525 1653331 := bstep (se 1 (by rfl) ⟨1239998, by rfl⟩ : syracuseStep 1653331 = 2479997) B2479997
theorem B1653347 : Blo 1651525 1653347 := bstep (se 1 (by rfl) ⟨1240010, by rfl⟩ : syracuseStep 1653347 = 2480021) B2480021
theorem B7060081 : Blo 1651525 7060081 := bstep (se 2 (by rfl) ⟨2647530, by rfl⟩ : syracuseStep 7060081 = 5295061) B5295061
theorem B1653363 : Blo 1651525 1653363 := bstep (se 1 (by rfl) ⟨1240022, by rfl⟩ : syracuseStep 1653363 = 2480045) B2480045
theorem B1653379 : Blo 1651525 1653379 := bstep (se 1 (by rfl) ⟨1240034, by rfl⟩ : syracuseStep 1653379 = 2480069) B2480069
theorem B3971729 : Blo 1651525 3971729 := bstep (se 2 (by rfl) ⟨1489398, by rfl⟩ : syracuseStep 3971729 = 2978797) B2978797
theorem B1653395 : Blo 1651525 1653395 := bstep (se 1 (by rfl) ⟨1240046, by rfl⟩ : syracuseStep 1653395 = 2480093) B2480093
theorem B1653411 : Blo 1651525 1653411 := bstep (se 1 (by rfl) ⟨1240058, by rfl⟩ : syracuseStep 1653411 = 2480117) B2480117
theorem B5577389 : Blo 1651525 5577389 := bstep (se 3 (by rfl) ⟨1045760, by rfl⟩ : syracuseStep 5577389 = 2091521) B2091521
theorem B6273713 : Blo 1651525 6273713 := bstep (se 2 (by rfl) ⟨2352642, by rfl⟩ : syracuseStep 6273713 = 4705285) B4705285
theorem B3717809 : Blo 1651525 3717809 := bstep (se 2 (by rfl) ⟨1394178, by rfl⟩ : syracuseStep 3717809 = 2788357) B2788357
theorem B1653427 : Blo 1651525 1653427 := bstep (se 1 (by rfl) ⟨1240070, by rfl⟩ : syracuseStep 1653427 = 2480141) B2480141
theorem B1858243 : Blo 1651525 1858243 := bstep (se 1 (by rfl) ⟨1393682, by rfl⟩ : syracuseStep 1858243 = 2787365) B2787365
theorem B3717827 : Blo 1651525 3717827 := bstep (se 1 (by rfl) ⟨2788370, by rfl⟩ : syracuseStep 3717827 = 5576741) B5576741
theorem B1653443 : Blo 1651525 1653443 := bstep (se 1 (by rfl) ⟨1240082, by rfl⟩ : syracuseStep 1653443 = 2480165) B2480165
theorem B10730189 : Blo 1651525 10730189 := bstep (se 3 (by rfl) ⟨2011910, by rfl⟩ : syracuseStep 10730189 = 4023821) B4023821
theorem B1653459 : Blo 1651525 1653459 := bstep (se 1 (by rfl) ⟨1240094, by rfl⟩ : syracuseStep 1653459 = 2480189) B2480189
theorem B9411299 : Blo 1651525 9411299 := bstep (se 1 (by rfl) ⟨7058474, by rfl⟩ : syracuseStep 9411299 = 14116949) B14116949
theorem B5577443 : Blo 1651525 5577443 := bstep (se 1 (by rfl) ⟨4183082, by rfl⟩ : syracuseStep 5577443 = 8366165) B8366165
theorem B1653475 : Blo 1651525 1653475 := bstep (se 1 (by rfl) ⟨1240106, by rfl⟩ : syracuseStep 1653475 = 2480213) B2480213
theorem B1653491 : Blo 1651525 1653491 := bstep (se 1 (by rfl) ⟨1240118, by rfl⟩ : syracuseStep 1653491 = 2480237) B2480237
theorem B1653507 : Blo 1651525 1653507 := bstep (se 1 (by rfl) ⟨1240130, by rfl⟩ : syracuseStep 1653507 = 2480261) B2480261
theorem B3767057 : Blo 1651525 3767057 := bstep (se 2 (by rfl) ⟨1412646, by rfl⟩ : syracuseStep 3767057 = 2825293) B2825293
theorem B1653523 : Blo 1651525 1653523 := bstep (se 1 (by rfl) ⟨1240142, by rfl⟩ : syracuseStep 1653523 = 2480285) B2480285
theorem B1858387 : Blo 1651525 1858387 := bstep (se 1 (by rfl) ⟨1393790, by rfl⟩ : syracuseStep 1858387 = 2787581) B2787581
theorem B12549005 : Blo 1651525 12549005 := bstep (se 3 (by rfl) ⟨2352938, by rfl⟩ : syracuseStep 12549005 = 4705877) B4705877
theorem B21748661 : Blo 1651525 21748661 := bstep (se 5 (by rfl) ⟨1019468, by rfl⟩ : syracuseStep 21748661 = 2038937) B2038937
theorem B81476549 : Blo 1651525 81476549 := bstep (se 4 (by rfl) ⟨7638426, by rfl⟩ : syracuseStep 81476549 = 15276853) B15276853
theorem B5651405 : Blo 1651525 5651405 := bstep (se 3 (by rfl) ⟨1059638, by rfl⟩ : syracuseStep 5651405 = 2119277) B2119277
theorem B3718097 : Blo 1651525 3718097 := bstep (se 2 (by rfl) ⟨1394286, by rfl⟩ : syracuseStep 3718097 = 2788573) B2788573
theorem B3767267 : Blo 1651525 3767267 := bstep (se 1 (by rfl) ⟨2825450, by rfl⟩ : syracuseStep 3767267 = 5650901) B5650901
theorem B1858531 : Blo 1651525 1858531 := bstep (se 1 (by rfl) ⟨1393898, by rfl⟩ : syracuseStep 1858531 = 2787797) B2787797
theorem B3718115 : Blo 1651525 3718115 := bstep (se 1 (by rfl) ⟨2788586, by rfl⟩ : syracuseStep 3718115 = 5577173) B5577173
theorem B5577713 : Blo 1651525 5577713 := bstep (se 2 (by rfl) ⟨2091642, by rfl⟩ : syracuseStep 5577713 = 4183285) B4183285
theorem B10583075 : Blo 1651525 10583075 := bstep (se 1 (by rfl) ⟨7937306, by rfl⟩ : syracuseStep 10583075 = 15874613) B15874613
theorem B5954609 : Blo 1651525 5954609 := bstep (se 2 (by rfl) ⟨2232978, by rfl⟩ : syracuseStep 5954609 = 4465957) B4465957
theorem B1858675 : Blo 1651525 1858675 := bstep (se 1 (by rfl) ⟨1394006, by rfl⟩ : syracuseStep 1858675 = 2788013) B2788013
theorem B5954723 : Blo 1651525 5954723 := bstep (se 1 (by rfl) ⟨4466042, by rfl⟩ : syracuseStep 5954723 = 8932085) B8932085
theorem B3529955 : Blo 1651525 3529955 := bstep (se 1 (by rfl) ⟨2647466, by rfl⟩ : syracuseStep 3529955 = 5294933) B5294933
theorem B8363249 : Blo 1651525 8363249 := bstep (se 2 (by rfl) ⟨3136218, by rfl⟩ : syracuseStep 8363249 = 6272437) B6272437
theorem B3718385 : Blo 1651525 3718385 := bstep (se 2 (by rfl) ⟨1394394, by rfl⟩ : syracuseStep 3718385 = 2788789) B2788789
theorem B1858819 : Blo 1651525 1858819 := bstep (se 1 (by rfl) ⟨1394114, by rfl⟩ : syracuseStep 1858819 = 2788229) B2788229
theorem B3718403 : Blo 1651525 3718403 := bstep (se 1 (by rfl) ⟨2788802, by rfl⟩ : syracuseStep 3718403 = 5577605) B5577605
theorem B6274381 : Blo 1651525 6274381 := bstep (se 3 (by rfl) ⟨1176446, by rfl⟩ : syracuseStep 6274381 = 2352893) B2352893
theorem B5291345 : Blo 1651525 5291345 := bstep (se 2 (by rfl) ⟨1984254, by rfl⟩ : syracuseStep 5291345 = 3968509) B3968509
theorem B8928625 : Blo 1651525 8928625 := bstep (se 2 (by rfl) ⟨3348234, by rfl⟩ : syracuseStep 8928625 = 6696469) B6696469
theorem B1858963 : Blo 1651525 1858963 := bstep (se 1 (by rfl) ⟨1394222, by rfl⟩ : syracuseStep 1858963 = 2788445) B2788445
theorem B3136963 : Blo 1651525 3136963 := bstep (se 1 (by rfl) ⟨2352722, by rfl⟩ : syracuseStep 3136963 = 4705445) B4705445
theorem B13401571 : Blo 1651525 13401571 := bstep (se 1 (by rfl) ⟨10051178, by rfl⟩ : syracuseStep 13401571 = 20102357) B20102357
theorem B10182149 : Blo 1651525 10182149 := bstep (se 4 (by rfl) ⟨954576, by rfl⟩ : syracuseStep 10182149 = 1909153) B1909153
theorem B5578253 : Blo 1651525 5578253 := bstep (se 3 (by rfl) ⟨1045922, by rfl⟩ : syracuseStep 5578253 = 2091845) B2091845
theorem B3718673 : Blo 1651525 3718673 := bstep (se 2 (by rfl) ⟨1394502, by rfl⟩ : syracuseStep 3718673 = 2789005) B2789005
theorem B4464163 : Blo 1651525 4464163 := bstep (se 1 (by rfl) ⟨3348122, by rfl⟩ : syracuseStep 4464163 = 6696245) B6696245
theorem B3350051 : Blo 1651525 3350051 := bstep (se 1 (by rfl) ⟨2512538, by rfl⟩ : syracuseStep 3350051 = 5025077) B5025077
theorem B1859107 : Blo 1651525 1859107 := bstep (se 1 (by rfl) ⟨1394330, by rfl⟩ : syracuseStep 1859107 = 2788661) B2788661
theorem B3718691 : Blo 1651525 3718691 := bstep (se 1 (by rfl) ⟨2789018, by rfl⟩ : syracuseStep 3718691 = 5578037) B5578037
theorem B2825779 : Blo 1651525 2825779 := bstep (se 1 (by rfl) ⟨2119334, by rfl⟩ : syracuseStep 2825779 = 4238669) B4238669
theorem B5578307 : Blo 1651525 5578307 := bstep (se 1 (by rfl) ⟨4183730, by rfl⟩ : syracuseStep 5578307 = 8367461) B8367461
theorem B3137123 : Blo 1651525 3137123 := bstep (se 1 (by rfl) ⟨2352842, by rfl⟩ : syracuseStep 3137123 = 4705685) B4705685
theorem B1859251 : Blo 1651525 1859251 := bstep (se 1 (by rfl) ⟨1394438, by rfl⟩ : syracuseStep 1859251 = 2788877) B2788877
theorem B9412301 : Blo 1651525 9412301 := bstep (se 3 (by rfl) ⟨1764806, by rfl⟩ : syracuseStep 9412301 = 3529613) B3529613
theorem B35741411 : Blo 1651525 35741411 := bstep (se 1 (by rfl) ⟨26806058, by rfl⟩ : syracuseStep 35741411 = 53612117) B53612117
theorem B3718961 : Blo 1651525 3718961 := bstep (se 2 (by rfl) ⟨1394610, by rfl⟩ : syracuseStep 3718961 = 2789221) B2789221
theorem B1859395 : Blo 1651525 1859395 := bstep (se 1 (by rfl) ⟨1394546, by rfl⟩ : syracuseStep 1859395 = 2789093) B2789093
theorem B3718979 : Blo 1651525 3718979 := bstep (se 1 (by rfl) ⟨2789234, by rfl⟩ : syracuseStep 3718979 = 5578469) B5578469
theorem B5578577 : Blo 1651525 5578577 := bstep (se 2 (by rfl) ⟨2091966, by rfl⟩ : syracuseStep 5578577 = 4183933) B4183933
theorem B1859539 : Blo 1651525 1859539 := bstep (se 1 (by rfl) ⟨1394654, by rfl⟩ : syracuseStep 1859539 = 2789309) B2789309
theorem B5652503 : Blo 1651525 5652503 := bstep (se 1 (by rfl) ⟨4239377, by rfl⟩ : syracuseStep 5652503 = 8478755) B8478755
theorem B4464791 : Blo 1651525 4464791 := bstep (se 1 (by rfl) ⟨3348593, by rfl⟩ : syracuseStep 4464791 = 6697187) B6697187
theorem B3719321 : Blo 1651525 3719321 := bstep (se 2 (by rfl) ⟨1394745, by rfl⟩ : syracuseStep 3719321 = 2789491) B2789491
theorem B1859755 : Blo 1651525 1859755 := bstep (se 1 (by rfl) ⟨1394816, by rfl⟩ : syracuseStep 1859755 = 2789633) B2789633
theorem B5578955 : Blo 1651525 5578955 := bstep (se 1 (by rfl) ⟨4184216, by rfl⟩ : syracuseStep 5578955 = 8368433) B8368433
theorem B3137753 : Blo 1651525 3137753 := bstep (se 2 (by rfl) ⟨1176657, by rfl⟩ : syracuseStep 3137753 = 2353315) B2353315
theorem B3719411 : Blo 1651525 3719411 := bstep (se 1 (by rfl) ⟨2789558, by rfl⟩ : syracuseStep 3719411 = 5579117) B5579117
theorem B3719447 : Blo 1651525 3719447 := bstep (se 1 (by rfl) ⟨2789585, by rfl⟩ : syracuseStep 3719447 = 5579171) B5579171
theorem B1859863 : Blo 1651525 1859863 := bstep (se 1 (by rfl) ⟨1394897, by rfl⟩ : syracuseStep 1859863 = 2789795) B2789795
theorem B3719627 : Blo 1651525 3719627 := bstep (se 1 (by rfl) ⟨2789720, by rfl⟩ : syracuseStep 3719627 = 5579441) B5579441
theorem B1860043 : Blo 1651525 1860043 := bstep (se 1 (by rfl) ⟨1395032, by rfl⟩ : syracuseStep 1860043 = 2790065) B2790065
theorem B5579225 : Blo 1651525 5579225 := bstep (se 2 (by rfl) ⟨2092209, by rfl⟩ : syracuseStep 5579225 = 4184419) B4184419
theorem B3719681 : Blo 1651525 3719681 := bstep (se 2 (by rfl) ⟨1394880, by rfl⟩ : syracuseStep 3719681 = 2789761) B2789761
theorem B1860151 : Blo 1651525 1860151 := bstep (se 1 (by rfl) ⟨1395113, by rfl⟩ : syracuseStep 1860151 = 2790227) B2790227
theorem B21176963 : Blo 1651525 21176963 := bstep (se 1 (by rfl) ⟨15882722, by rfl⟩ : syracuseStep 21176963 = 31765445) B31765445
theorem B8930009 : Blo 1651525 8930009 := bstep (se 2 (by rfl) ⟨3348753, by rfl⟩ : syracuseStep 8930009 = 6697507) B6697507
theorem B3719897 : Blo 1651525 3719897 := bstep (se 2 (by rfl) ⟨1394961, by rfl⟩ : syracuseStep 3719897 = 2789923) B2789923
theorem B1909495 : Blo 1651525 1909495 := bstep (se 1 (by rfl) ⟨1432121, by rfl⟩ : syracuseStep 1909495 = 2864243) B2864243
theorem B3719987 : Blo 1651525 3719987 := bstep (se 1 (by rfl) ⟨2789990, by rfl⟩ : syracuseStep 3719987 = 5579981) B5579981
theorem B9413441 : Blo 1651525 9413441 := bstep (se 2 (by rfl) ⟨3530040, by rfl⟩ : syracuseStep 9413441 = 7060081) B7060081
theorem B3720023 : Blo 1651525 3720023 := bstep (se 1 (by rfl) ⟨2790017, by rfl⟩ : syracuseStep 3720023 = 5580035) B5580035
theorem B3138497 : Blo 1651525 3138497 := bstep (se 2 (by rfl) ⟨1176936, by rfl⟩ : syracuseStep 3138497 = 2353873) B2353873
theorem B3720203 : Blo 1651525 3720203 := bstep (se 1 (by rfl) ⟨2790152, by rfl⟩ : syracuseStep 3720203 = 5580305) B5580305
theorem B6276113 : Blo 1651525 6276113 := bstep (se 2 (by rfl) ⟨2353542, by rfl⟩ : syracuseStep 6276113 = 4707085) B4707085
theorem B3720257 : Blo 1651525 3720257 := bstep (se 2 (by rfl) ⟨1395096, by rfl⟩ : syracuseStep 3720257 = 2790193) B2790193
theorem B5653597 : Blo 1651525 5653597 := bstep (se 3 (by rfl) ⟨1060049, by rfl⟩ : syracuseStep 5653597 = 2120099) B2120099
theorem B14115991 : Blo 1651525 14115991 := bstep (se 1 (by rfl) ⟨10586993, by rfl⟩ : syracuseStep 14115991 = 21173987) B21173987
theorem B5579927 : Blo 1651525 5579927 := bstep (se 1 (by rfl) ⟨4184945, by rfl⟩ : syracuseStep 5579927 = 8369891) B8369891
theorem B3138763 : Blo 1651525 3138763 := bstep (se 1 (by rfl) ⟨2354072, by rfl⟩ : syracuseStep 3138763 = 4708145) B4708145
theorem B1885399 : Blo 1651525 1885399 := bstep (se 1 (by rfl) ⟨1414049, by rfl⟩ : syracuseStep 1885399 = 2828099) B2828099
theorem B7939403 : Blo 1651525 7939403 := bstep (se 1 (by rfl) ⟨5954552, by rfl⟩ : syracuseStep 7939403 = 11909105) B11909105
theorem B18818405 : Blo 1651525 18818405 := bstep (se 4 (by rfl) ⟨1764225, by rfl⟩ : syracuseStep 18818405 = 3528451) B3528451
theorem B2090443 : Blo 1651525 2090443 := bstep (se 1 (by rfl) ⟨1567832, by rfl⟩ : syracuseStep 2090443 = 3135665) B3135665
theorem B120620501 : Blo 1651525 120620501 := bstep (se 7 (by rfl) ⟨1413521, by rfl⟩ : syracuseStep 120620501 = 2827043) B2827043
theorem B5023255 : Blo 1651525 5023255 := bstep (se 1 (by rfl) ⟨3767441, by rfl⟩ : syracuseStep 5023255 = 7534883) B7534883
theorem B5580467 : Blo 1651525 5580467 := bstep (se 1 (by rfl) ⟨4185350, by rfl⟩ : syracuseStep 5580467 = 8370701) B8370701
theorem B6276811 : Blo 1651525 6276811 := bstep (se 1 (by rfl) ⟨4707608, by rfl⟩ : syracuseStep 6276811 = 9415217) B9415217
theorem B2090711 : Blo 1651525 2090711 := bstep (se 1 (by rfl) ⟨1568033, by rfl⟩ : syracuseStep 2090711 = 3136067) B3136067
theorem B2647819 : Blo 1651525 2647819 := bstep (se 1 (by rfl) ⟨1985864, by rfl⟩ : syracuseStep 2647819 = 3971729) B3971729
theorem B8365841 : Blo 1651525 8365841 := bstep (se 2 (by rfl) ⟨3137190, by rfl⟩ : syracuseStep 8365841 = 6274381) B6274381
theorem B2787095 : Blo 1651525 2787095 := bstep (se 1 (by rfl) ⟨2090321, by rfl⟩ : syracuseStep 2787095 = 4180643) B4180643
theorem B11904833 : Blo 1651525 11904833 := bstep (se 2 (by rfl) ⟨4464312, by rfl⟩ : syracuseStep 11904833 = 8928625) B8928625
theorem B2787223 : Blo 1651525 2787223 := bstep (se 1 (by rfl) ⟨2090417, by rfl⟩ : syracuseStep 2787223 = 4180835) B4180835
theorem B8366003 : Blo 1651525 8366003 := bstep (se 1 (by rfl) ⟨6274502, by rfl⟩ : syracuseStep 8366003 = 12549005) B12549005
theorem B17868761 : Blo 1651525 17868761 := bstep (se 2 (by rfl) ⟨6700785, by rfl⟩ : syracuseStep 17868761 = 13401571) B13401571
theorem B6277085 : Blo 1651525 6277085 := bstep (se 3 (by rfl) ⟨1176953, by rfl⟩ : syracuseStep 6277085 = 2353907) B2353907
theorem B7055383 : Blo 1651525 7055383 := bstep (se 1 (by rfl) ⟨5291537, by rfl⟩ : syracuseStep 7055383 = 10583075) B10583075
theorem B2353303 : Blo 1651525 2353303 := bstep (se 1 (by rfl) ⟨1764977, by rfl⟩ : syracuseStep 2353303 = 3529955) B3529955
theorem B3180887 : Blo 1651525 3180887 := bstep (se 1 (by rfl) ⟨2385665, by rfl⟩ : syracuseStep 3180887 = 4771331) B4771331
theorem B10733917 : Blo 1651525 10733917 := bstep (se 3 (by rfl) ⟨2012609, by rfl⟩ : syracuseStep 10733917 = 4025219) B4025219
theorem B2091415 : Blo 1651525 2091415 := bstep (se 1 (by rfl) ⟨1568561, by rfl⟩ : syracuseStep 2091415 = 3137123) B3137123
theorem B2787851 : Blo 1651525 2787851 := bstep (se 1 (by rfl) ⟨2090888, by rfl⟩ : syracuseStep 2787851 = 4181777) B4181777
theorem B4180531 : Blo 1651525 4180531 := bstep (se 1 (by rfl) ⟨3135398, by rfl⟩ : syracuseStep 4180531 = 6270797) B6270797
theorem B3770945 : Blo 1651525 3770945 := bstep (se 2 (by rfl) ⟨1414104, by rfl⟩ : syracuseStep 3770945 = 2828209) B2828209
theorem B10046045 : Blo 1651525 10046045 := bstep (se 3 (by rfl) ⟨1883633, by rfl⟩ : syracuseStep 10046045 = 3767267) B3767267
theorem B2787979 : Blo 1651525 2787979 := bstep (se 1 (by rfl) ⟨2090984, by rfl⟩ : syracuseStep 2787979 = 4181969) B4181969
theorem B6277783 : Blo 1651525 6277783 := bstep (se 1 (by rfl) ⟨4708337, by rfl⟩ : syracuseStep 6277783 = 9416675) B9416675
theorem B4180673 : Blo 1651525 4180673 := bstep (se 2 (by rfl) ⟨1567752, by rfl⟩ : syracuseStep 4180673 = 3135505) B3135505
theorem B1764055 : Blo 1651525 1764055 := bstep (se 1 (by rfl) ⟨1323041, by rfl⟩ : syracuseStep 1764055 = 2646083) B2646083
theorem B3771137 : Blo 1651525 3771137 := bstep (se 2 (by rfl) ⟨1414176, by rfl⟩ : syracuseStep 3771137 = 2828353) B2828353
theorem B2788121 : Blo 1651525 2788121 := bstep (se 2 (by rfl) ⟨1045545, by rfl⟩ : syracuseStep 2788121 = 2091091) B2091091
theorem B12725143 : Blo 1651525 12725143 := bstep (se 1 (by rfl) ⟨9543857, by rfl⟩ : syracuseStep 12725143 = 19087715) B19087715
theorem B2788249 : Blo 1651525 2788249 := bstep (se 2 (by rfl) ⟨1045593, by rfl⟩ : syracuseStep 2788249 = 2091187) B2091187
theorem B12545117 : Blo 1651525 12545117 := bstep (se 3 (by rfl) ⟨2352209, by rfl⟩ : syracuseStep 12545117 = 4704419) B4704419
theorem B52292789 : Blo 1651525 52292789 := bstep (se 5 (by rfl) ⟨2451224, by rfl⟩ : syracuseStep 52292789 = 4902449) B4902449
theorem B4705559 : Blo 1651525 4705559 := bstep (se 1 (by rfl) ⟨3529169, by rfl⟩ : syracuseStep 4705559 = 7058339) B7058339
theorem B14511395 : Blo 1651525 14511395 := bstep (se 1 (by rfl) ⟨10883546, by rfl⟩ : syracuseStep 14511395 = 21767093) B21767093
theorem B2477387 : Blo 1651525 2477387 := bstep (se 1 (by rfl) ⟨1858040, by rfl⟩ : syracuseStep 2477387 = 3716081) B3716081
theorem B2477399 : Blo 1651525 2477399 := bstep (se 1 (by rfl) ⟨1858049, by rfl⟩ : syracuseStep 2477399 = 3716099) B3716099
theorem B12725635 : Blo 1651525 12725635 := bstep (se 1 (by rfl) ⟨9544226, by rfl⟩ : syracuseStep 12725635 = 19088453) B19088453
theorem B2477465 : Blo 1651525 2477465 := bstep (se 2 (by rfl) ⟨929049, by rfl⟩ : syracuseStep 2477465 = 1858099) B1858099
theorem B2788823 : Blo 1651525 2788823 := bstep (se 1 (by rfl) ⟨2091617, by rfl⟩ : syracuseStep 2788823 = 4183235) B4183235
theorem B2477579 : Blo 1651525 2477579 := bstep (se 1 (by rfl) ⟨1858184, by rfl⟩ : syracuseStep 2477579 = 3716369) B3716369
theorem B1764875 : Blo 1651525 1764875 := bstep (se 1 (by rfl) ⟨1323656, by rfl⟩ : syracuseStep 1764875 = 2647313) B2647313
theorem B2477591 : Blo 1651525 2477591 := bstep (se 1 (by rfl) ⟨1858193, by rfl⟩ : syracuseStep 2477591 = 3716387) B3716387
theorem B2788951 : Blo 1651525 2788951 := bstep (se 1 (by rfl) ⟨2091713, by rfl⟩ : syracuseStep 2788951 = 4183427) B4183427
theorem B2477657 : Blo 1651525 2477657 := bstep (se 2 (by rfl) ⟨929121, by rfl⟩ : syracuseStep 2477657 = 1858243) B1858243
theorem B24161885 : Blo 1651525 24161885 := bstep (se 3 (by rfl) ⟨4530353, by rfl⟩ : syracuseStep 24161885 = 9060707) B9060707
theorem B2477771 : Blo 1651525 2477771 := bstep (se 1 (by rfl) ⟨1858328, by rfl⟩ : syracuseStep 2477771 = 3716657) B3716657
theorem B7540427 : Blo 1651525 7540427 := bstep (se 1 (by rfl) ⟨5655320, by rfl⟩ : syracuseStep 7540427 = 11310641) B11310641
theorem B2477783 : Blo 1651525 2477783 := bstep (se 1 (by rfl) ⟨1858337, by rfl⟩ : syracuseStep 2477783 = 3716675) B3716675
theorem B5574365 : Blo 1651525 5574365 := bstep (se 3 (by rfl) ⟨1045193, by rfl⟩ : syracuseStep 5574365 = 2090387) B2090387
theorem B2477849 : Blo 1651525 2477849 := bstep (se 2 (by rfl) ⟨929193, by rfl⟩ : syracuseStep 2477849 = 1858387) B1858387
theorem B21163841 : Blo 1651525 21163841 := bstep (se 2 (by rfl) ⟨7936440, by rfl⟩ : syracuseStep 21163841 = 15872881) B15872881
theorem B8367947 : Blo 1651525 8367947 := bstep (se 1 (by rfl) ⟨6275960, by rfl⟩ : syracuseStep 8367947 = 12551921) B12551921
theorem B11906909 : Blo 1651525 11906909 := bstep (se 3 (by rfl) ⟨2232545, by rfl⟩ : syracuseStep 11906909 = 4465091) B4465091
theorem B2477963 : Blo 1651525 2477963 := bstep (se 1 (by rfl) ⟨1858472, by rfl⟩ : syracuseStep 2477963 = 3716945) B3716945
theorem B2477975 : Blo 1651525 2477975 := bstep (se 1 (by rfl) ⟨1858481, by rfl⟩ : syracuseStep 2477975 = 3716963) B3716963
theorem B4181939 : Blo 1651525 4181939 := bstep (se 1 (by rfl) ⟨3136454, by rfl⟩ : syracuseStep 4181939 = 6272909) B6272909
theorem B10055603 : Blo 1651525 10055603 := bstep (se 1 (by rfl) ⟨7541702, by rfl⟩ : syracuseStep 10055603 = 15083405) B15083405
theorem B5656499 : Blo 1651525 5656499 := bstep (se 1 (by rfl) ⟨4242374, by rfl⟩ : syracuseStep 5656499 = 8484749) B8484749
theorem B2478041 : Blo 1651525 2478041 := bstep (se 2 (by rfl) ⟨929265, by rfl⟩ : syracuseStep 2478041 = 1858531) B1858531
theorem B6270979 : Blo 1651525 6270979 := bstep (se 1 (by rfl) ⟨4703234, by rfl⟩ : syracuseStep 6270979 = 9406469) B9406469
theorem B3969047 : Blo 1651525 3969047 := bstep (se 1 (by rfl) ⟨2976785, by rfl⟩ : syracuseStep 3969047 = 5953571) B5953571
theorem B4026433 : Blo 1651525 4026433 := bstep (se 2 (by rfl) ⟨1509912, by rfl⟩ : syracuseStep 4026433 = 3019825) B3019825
theorem B2478155 : Blo 1651525 2478155 := bstep (se 1 (by rfl) ⟨1858616, by rfl⟩ : syracuseStep 2478155 = 3717233) B3717233
theorem B2478167 : Blo 1651525 2478167 := bstep (se 1 (by rfl) ⟨1858625, by rfl⟩ : syracuseStep 2478167 = 3717251) B3717251
theorem B1675415 : Blo 1651525 1675415 := bstep (se 1 (by rfl) ⟨1256561, by rfl⟩ : syracuseStep 1675415 = 2513123) B2513123
theorem B20107415 : Blo 1651525 20107415 := bstep (se 1 (by rfl) ⟨15080561, by rfl⟩ : syracuseStep 20107415 = 30161123) B30161123
theorem B2478233 : Blo 1651525 2478233 := bstep (se 2 (by rfl) ⟨929337, by rfl⟩ : syracuseStep 2478233 = 1858675) B1858675
theorem B2789579 : Blo 1651525 2789579 := bstep (se 1 (by rfl) ⟨2092184, by rfl⟩ : syracuseStep 2789579 = 4184369) B4184369
theorem B2478347 : Blo 1651525 2478347 := bstep (se 1 (by rfl) ⟨1858760, by rfl⟩ : syracuseStep 2478347 = 3717521) B3717521
theorem B2478359 : Blo 1651525 2478359 := bstep (se 1 (by rfl) ⟨1858769, by rfl⟩ : syracuseStep 2478359 = 3717539) B3717539
theorem B6271283 : Blo 1651525 6271283 := bstep (se 1 (by rfl) ⟨4703462, by rfl⟩ : syracuseStep 6271283 = 9406925) B9406925
theorem B2789707 : Blo 1651525 2789707 := bstep (se 1 (by rfl) ⟨2092280, by rfl⟩ : syracuseStep 2789707 = 4184561) B4184561
theorem B2478425 : Blo 1651525 2478425 := bstep (se 2 (by rfl) ⟨929409, by rfl⟩ : syracuseStep 2478425 = 1858819) B1858819
theorem B4182475 : Blo 1651525 4182475 := bstep (se 1 (by rfl) ⟨3136856, by rfl⟩ : syracuseStep 4182475 = 6273713) B6273713
theorem B2478539 : Blo 1651525 2478539 := bstep (se 1 (by rfl) ⟨1858904, by rfl⟩ : syracuseStep 2478539 = 3717809) B3717809
theorem B2478551 : Blo 1651525 2478551 := bstep (se 1 (by rfl) ⟨1858913, by rfl⟩ : syracuseStep 2478551 = 3717827) B3717827
theorem B2789849 : Blo 1651525 2789849 := bstep (se 2 (by rfl) ⟨1046193, by rfl⟩ : syracuseStep 2789849 = 2092387) B2092387
theorem B2511371 : Blo 1651525 2511371 := bstep (se 1 (by rfl) ⟨1883528, by rfl⟩ : syracuseStep 2511371 = 3767057) B3767057
theorem B2478617 : Blo 1651525 2478617 := bstep (se 2 (by rfl) ⟨929481, by rfl⟩ : syracuseStep 2478617 = 1858963) B1858963
theorem B4182617 : Blo 1651525 4182617 := bstep (se 2 (by rfl) ⟨1568481, by rfl⟩ : syracuseStep 4182617 = 3136963) B3136963
theorem B2789977 : Blo 1651525 2789977 := bstep (se 2 (by rfl) ⟨1046241, by rfl⟩ : syracuseStep 2789977 = 2092483) B2092483
theorem B54317699 : Blo 1651525 54317699 := bstep (se 1 (by rfl) ⟨40738274, by rfl⟩ : syracuseStep 54317699 = 81476549) B81476549
theorem B2478731 : Blo 1651525 2478731 := bstep (se 1 (by rfl) ⟨1859048, by rfl⟩ : syracuseStep 2478731 = 3718097) B3718097
theorem B2478743 : Blo 1651525 2478743 := bstep (se 1 (by rfl) ⟨1859057, by rfl⟩ : syracuseStep 2478743 = 3718115) B3718115
theorem B3969739 : Blo 1651525 3969739 := bstep (se 1 (by rfl) ⟨2977304, by rfl⟩ : syracuseStep 3969739 = 5954609) B5954609
theorem B5952217 : Blo 1651525 5952217 := bstep (se 2 (by rfl) ⟨2232081, by rfl⟩ : syracuseStep 5952217 = 4464163) B4464163
theorem B2478809 : Blo 1651525 2478809 := bstep (se 2 (by rfl) ⟨929553, by rfl⟩ : syracuseStep 2478809 = 1859107) B1859107
theorem B3969815 : Blo 1651525 3969815 := bstep (se 1 (by rfl) ⟨2977361, by rfl⟩ : syracuseStep 3969815 = 5954723) B5954723
theorem B1651531 : Blo 1651525 1651531 := bstep (se 1 (by rfl) ⟨1238648, by rfl⟩ : syracuseStep 1651531 = 2477297) B2477297
theorem B5575499 : Blo 1651525 5575499 := bstep (se 1 (by rfl) ⟨4181624, by rfl⟩ : syracuseStep 5575499 = 8363249) B8363249
theorem B2478923 : Blo 1651525 2478923 := bstep (se 1 (by rfl) ⟨1859192, by rfl⟩ : syracuseStep 2478923 = 3718385) B3718385
theorem B1651543 : Blo 1651525 1651543 := bstep (se 1 (by rfl) ⟨1238657, by rfl⟩ : syracuseStep 1651543 = 2477315) B2477315
theorem B2478935 : Blo 1651525 2478935 := bstep (se 1 (by rfl) ⟨1859201, by rfl⟩ : syracuseStep 2478935 = 3718403) B3718403
theorem B7058269 : Blo 1651525 7058269 := bstep (se 3 (by rfl) ⟨1323425, by rfl⟩ : syracuseStep 7058269 = 2646851) B2646851
theorem B1651563 : Blo 1651525 1651563 := bstep (se 1 (by rfl) ⟨1238672, by rfl⟩ : syracuseStep 1651563 = 2477345) B2477345
theorem B3715955 : Blo 1651525 3715955 := bstep (se 1 (by rfl) ⟨2786966, by rfl⟩ : syracuseStep 3715955 = 5573933) B5573933
theorem B1651575 : Blo 1651525 1651575 := bstep (se 1 (by rfl) ⟨1238681, by rfl⟩ : syracuseStep 1651575 = 2477363) B2477363
theorem B2978689 : Blo 1651525 2978689 := bstep (se 2 (by rfl) ⟨1117008, by rfl⟩ : syracuseStep 2978689 = 2234017) B2234017
theorem B1651595 : Blo 1651525 1651595 := bstep (se 1 (by rfl) ⟨1238696, by rfl⟩ : syracuseStep 1651595 = 2477393) B2477393
theorem B3527563 : Blo 1651525 3527563 := bstep (se 1 (by rfl) ⟨2645672, by rfl⟩ : syracuseStep 3527563 = 5291345) B5291345
theorem B3715991 : Blo 1651525 3715991 := bstep (se 1 (by rfl) ⟨2786993, by rfl⟩ : syracuseStep 3715991 = 5573987) B5573987
theorem B1651607 : Blo 1651525 1651607 := bstep (se 1 (by rfl) ⟨1238705, by rfl⟩ : syracuseStep 1651607 = 2477411) B2477411
theorem B2479001 : Blo 1651525 2479001 := bstep (se 2 (by rfl) ⟨929625, by rfl⟩ : syracuseStep 2479001 = 1859251) B1859251
theorem B1651627 : Blo 1651525 1651627 := bstep (se 1 (by rfl) ⟨1238720, by rfl⟩ : syracuseStep 1651627 = 2477441) B2477441
theorem B1651639 : Blo 1651525 1651639 := bstep (se 1 (by rfl) ⟨1238729, by rfl⟩ : syracuseStep 1651639 = 2477459) B2477459
theorem B6271937 : Blo 1651525 6271937 := bstep (se 2 (by rfl) ⟨2351976, by rfl⟩ : syracuseStep 6271937 = 4703953) B4703953
theorem B1651659 : Blo 1651525 1651659 := bstep (se 1 (by rfl) ⟨1238744, by rfl⟩ : syracuseStep 1651659 = 2477489) B2477489
theorem B1651671 : Blo 1651525 1651671 := bstep (se 1 (by rfl) ⟨1238753, by rfl⟩ : syracuseStep 1651671 = 2477507) B2477507
theorem B1651691 : Blo 1651525 1651691 := bstep (se 1 (by rfl) ⟨1238768, by rfl⟩ : syracuseStep 1651691 = 2477537) B2477537
theorem B1651703 : Blo 1651525 1651703 := bstep (se 1 (by rfl) ⟨1238777, by rfl⟩ : syracuseStep 1651703 = 2477555) B2477555
theorem B6788099 : Blo 1651525 6788099 := bstep (se 1 (by rfl) ⟨5091074, by rfl⟩ : syracuseStep 6788099 = 10182149) B10182149
theorem B1651723 : Blo 1651525 1651723 := bstep (se 1 (by rfl) ⟨1238792, by rfl⟩ : syracuseStep 1651723 = 2477585) B2477585
theorem B2479115 : Blo 1651525 2479115 := bstep (se 1 (by rfl) ⟨1859336, by rfl⟩ : syracuseStep 2479115 = 3718673) B3718673
theorem B1651735 : Blo 1651525 1651735 := bstep (se 1 (by rfl) ⟨1238801, by rfl⟩ : syracuseStep 1651735 = 2477603) B2477603
theorem B2233367 : Blo 1651525 2233367 := bstep (se 1 (by rfl) ⟨1675025, by rfl⟩ : syracuseStep 2233367 = 3350051) B3350051
theorem B2479127 : Blo 1651525 2479127 := bstep (se 1 (by rfl) ⟨1859345, by rfl⟩ : syracuseStep 2479127 = 3718691) B3718691
theorem B30569507 : Blo 1651525 30569507 := bstep (se 1 (by rfl) ⟨22927130, by rfl⟩ : syracuseStep 30569507 = 45854261) B45854261
theorem B1651755 : Blo 1651525 1651755 := bstep (se 1 (by rfl) ⟨1238816, by rfl⟩ : syracuseStep 1651755 = 2477633) B2477633
theorem B1651767 : Blo 1651525 1651767 := bstep (se 1 (by rfl) ⟨1238825, by rfl⟩ : syracuseStep 1651767 = 2477651) B2477651
theorem B3716171 : Blo 1651525 3716171 := bstep (se 1 (by rfl) ⟨2787128, by rfl⟩ : syracuseStep 3716171 = 5574257) B5574257
theorem B1651787 : Blo 1651525 1651787 := bstep (se 1 (by rfl) ⟨1238840, by rfl⟩ : syracuseStep 1651787 = 2477681) B2477681
theorem B1651799 : Blo 1651525 1651799 := bstep (se 1 (by rfl) ⟨1238849, by rfl⟩ : syracuseStep 1651799 = 2477699) B2477699
theorem B5575769 : Blo 1651525 5575769 := bstep (se 2 (by rfl) ⟨2090913, by rfl⟩ : syracuseStep 5575769 = 4181827) B4181827
theorem B2479193 : Blo 1651525 2479193 := bstep (se 2 (by rfl) ⟨929697, by rfl⟩ : syracuseStep 2479193 = 1859395) B1859395
theorem B1651819 : Blo 1651525 1651819 := bstep (se 1 (by rfl) ⟨1238864, by rfl⟩ : syracuseStep 1651819 = 2477729) B2477729
theorem B1651831 : Blo 1651525 1651831 := bstep (se 1 (by rfl) ⟨1238873, by rfl⟩ : syracuseStep 1651831 = 2477747) B2477747
theorem B3716225 : Blo 1651525 3716225 := bstep (se 2 (by rfl) ⟨1393584, by rfl⟩ : syracuseStep 3716225 = 2787169) B2787169
theorem B1651851 : Blo 1651525 1651851 := bstep (se 1 (by rfl) ⟨1238888, by rfl⟩ : syracuseStep 1651851 = 2477777) B2477777
theorem B1651863 : Blo 1651525 1651863 := bstep (se 1 (by rfl) ⟨1238897, by rfl⟩ : syracuseStep 1651863 = 2477795) B2477795
theorem B23827607 : Blo 1651525 23827607 := bstep (se 1 (by rfl) ⟨17870705, by rfl⟩ : syracuseStep 23827607 = 35741411) B35741411
theorem B1651883 : Blo 1651525 1651883 := bstep (se 1 (by rfl) ⟨1238912, by rfl⟩ : syracuseStep 1651883 = 2477825) B2477825
theorem B51573941 : Blo 1651525 51573941 := bstep (se 5 (by rfl) ⟨2417528, by rfl⟩ : syracuseStep 51573941 = 4835057) B4835057
theorem B1651895 : Blo 1651525 1651895 := bstep (se 1 (by rfl) ⟨1238921, by rfl⟩ : syracuseStep 1651895 = 2477843) B2477843
theorem B1651915 : Blo 1651525 1651915 := bstep (se 1 (by rfl) ⟨1238936, by rfl⟩ : syracuseStep 1651915 = 2477873) B2477873
theorem B2479307 : Blo 1651525 2479307 := bstep (se 1 (by rfl) ⟨1859480, by rfl⟩ : syracuseStep 2479307 = 3718961) B3718961
theorem B1651927 : Blo 1651525 1651927 := bstep (se 1 (by rfl) ⟨1238945, by rfl⟩ : syracuseStep 1651927 = 2477891) B2477891
theorem B2479319 : Blo 1651525 2479319 := bstep (se 1 (by rfl) ⟨1859489, by rfl⟩ : syracuseStep 2479319 = 3718979) B3718979
theorem B6362333 : Blo 1651525 6362333 := bstep (se 3 (by rfl) ⟨1192937, by rfl⟩ : syracuseStep 6362333 = 2385875) B2385875
theorem B1651947 : Blo 1651525 1651947 := bstep (se 1 (by rfl) ⟨1238960, by rfl⟩ : syracuseStep 1651947 = 2477921) B2477921
theorem B1651959 : Blo 1651525 1651959 := bstep (se 1 (by rfl) ⟨1238969, by rfl⟩ : syracuseStep 1651959 = 2477939) B2477939
theorem B1651979 : Blo 1651525 1651979 := bstep (se 1 (by rfl) ⟨1238984, by rfl⟩ : syracuseStep 1651979 = 2477969) B2477969
theorem B1651991 : Blo 1651525 1651991 := bstep (se 1 (by rfl) ⟨1238993, by rfl⟩ : syracuseStep 1651991 = 2477987) B2477987
theorem B2479385 : Blo 1651525 2479385 := bstep (se 2 (by rfl) ⟨929769, by rfl⟩ : syracuseStep 2479385 = 1859539) B1859539
theorem B1652011 : Blo 1651525 1652011 := bstep (se 1 (by rfl) ⟨1239008, by rfl⟩ : syracuseStep 1652011 = 2478017) B2478017
theorem B1652023 : Blo 1651525 1652023 := bstep (se 1 (by rfl) ⟨1239017, by rfl⟩ : syracuseStep 1652023 = 2478035) B2478035
theorem B1652043 : Blo 1651525 1652043 := bstep (se 1 (by rfl) ⟨1239032, by rfl⟩ : syracuseStep 1652043 = 2478065) B2478065
theorem B1652055 : Blo 1651525 1652055 := bstep (se 1 (by rfl) ⟨1239041, by rfl⟩ : syracuseStep 1652055 = 2478083) B2478083
theorem B3716441 : Blo 1651525 3716441 := bstep (se 2 (by rfl) ⟨1393665, by rfl⟩ : syracuseStep 3716441 = 2787331) B2787331
theorem B1652075 : Blo 1651525 1652075 := bstep (se 1 (by rfl) ⟨1239056, by rfl⟩ : syracuseStep 1652075 = 2478113) B2478113
theorem B1652087 : Blo 1651525 1652087 := bstep (se 1 (by rfl) ⟨1239065, by rfl⟩ : syracuseStep 1652087 = 2478131) B2478131
theorem B1652107 : Blo 1651525 1652107 := bstep (se 1 (by rfl) ⟨1239080, by rfl⟩ : syracuseStep 1652107 = 2478161) B2478161
theorem B2479499 : Blo 1651525 2479499 := bstep (se 1 (by rfl) ⟨1859624, by rfl⟩ : syracuseStep 2479499 = 3719249) B3719249
theorem B1652119 : Blo 1651525 1652119 := bstep (se 1 (by rfl) ⟨1239089, by rfl⟩ : syracuseStep 1652119 = 2478179) B2478179
theorem B4183447 : Blo 1651525 4183447 := bstep (se 1 (by rfl) ⟨3137585, by rfl⟩ : syracuseStep 4183447 = 6275171) B6275171
theorem B2479511 : Blo 1651525 2479511 := bstep (se 1 (by rfl) ⟨1859633, by rfl⟩ : syracuseStep 2479511 = 3719267) B3719267
theorem B1652139 : Blo 1651525 1652139 := bstep (se 1 (by rfl) ⟨1239104, by rfl⟩ : syracuseStep 1652139 = 2478209) B2478209
theorem B3716531 : Blo 1651525 3716531 := bstep (se 1 (by rfl) ⟨2787398, by rfl⟩ : syracuseStep 3716531 = 5574797) B5574797
theorem B1652151 : Blo 1651525 1652151 := bstep (se 1 (by rfl) ⟨1239113, by rfl⟩ : syracuseStep 1652151 = 2478227) B2478227
theorem B1652171 : Blo 1651525 1652171 := bstep (se 1 (by rfl) ⟨1239128, by rfl⟩ : syracuseStep 1652171 = 2478257) B2478257
theorem B3716567 : Blo 1651525 3716567 := bstep (se 1 (by rfl) ⟨2787425, by rfl⟩ : syracuseStep 3716567 = 5574851) B5574851
theorem B1652183 : Blo 1651525 1652183 := bstep (se 1 (by rfl) ⟨1239137, by rfl⟩ : syracuseStep 1652183 = 2478275) B2478275
theorem B2479577 : Blo 1651525 2479577 := bstep (se 2 (by rfl) ⟨929841, by rfl⟩ : syracuseStep 2479577 = 1859683) B1859683
theorem B1652203 : Blo 1651525 1652203 := bstep (se 1 (by rfl) ⟨1239152, by rfl⟩ : syracuseStep 1652203 = 2478305) B2478305
theorem B1652215 : Blo 1651525 1652215 := bstep (se 1 (by rfl) ⟨1239161, by rfl⟩ : syracuseStep 1652215 = 2478323) B2478323
theorem B1652235 : Blo 1651525 1652235 := bstep (se 1 (by rfl) ⟨1239176, by rfl⟩ : syracuseStep 1652235 = 2478353) B2478353
theorem B28251665 : Blo 1651525 28251665 := bstep (se 2 (by rfl) ⟨10594374, by rfl⟩ : syracuseStep 28251665 = 21188749) B21188749
theorem B1652247 : Blo 1651525 1652247 := bstep (se 1 (by rfl) ⟨1239185, by rfl⟩ : syracuseStep 1652247 = 2478371) B2478371
theorem B1652267 : Blo 1651525 1652267 := bstep (se 1 (by rfl) ⟨1239200, by rfl⟩ : syracuseStep 1652267 = 2478401) B2478401
theorem B9410093 : Blo 1651525 9410093 := bstep (se 3 (by rfl) ⟨1764392, by rfl⟩ : syracuseStep 9410093 = 3528785) B3528785
theorem B1652279 : Blo 1651525 1652279 := bstep (se 1 (by rfl) ⟨1239209, by rfl⟩ : syracuseStep 1652279 = 2478419) B2478419
theorem B8369729 : Blo 1651525 8369729 := bstep (se 2 (by rfl) ⟨3138648, by rfl⟩ : syracuseStep 8369729 = 6277297) B6277297
theorem B1652299 : Blo 1651525 1652299 := bstep (se 1 (by rfl) ⟨1239224, by rfl⟩ : syracuseStep 1652299 = 2478449) B2478449
theorem B2479691 : Blo 1651525 2479691 := bstep (se 1 (by rfl) ⟨1859768, by rfl⟩ : syracuseStep 2479691 = 3719537) B3719537
theorem B1652311 : Blo 1651525 1652311 := bstep (se 1 (by rfl) ⟨1239233, by rfl⟩ : syracuseStep 1652311 = 2478467) B2478467
theorem B2479703 : Blo 1651525 2479703 := bstep (se 1 (by rfl) ⟨1859777, by rfl⟩ : syracuseStep 2479703 = 3719555) B3719555
theorem B3528281 : Blo 1651525 3528281 := bstep (se 2 (by rfl) ⟨1323105, by rfl⟩ : syracuseStep 3528281 = 2646211) B2646211
theorem B1652331 : Blo 1651525 1652331 := bstep (se 1 (by rfl) ⟨1239248, by rfl⟩ : syracuseStep 1652331 = 2478497) B2478497
theorem B1652343 : Blo 1651525 1652343 := bstep (se 1 (by rfl) ⟨1239257, by rfl⟩ : syracuseStep 1652343 = 2478515) B2478515
theorem B3716747 : Blo 1651525 3716747 := bstep (se 1 (by rfl) ⟨2787560, by rfl⟩ : syracuseStep 3716747 = 5575121) B5575121
theorem B1652363 : Blo 1651525 1652363 := bstep (se 1 (by rfl) ⟨1239272, by rfl⟩ : syracuseStep 1652363 = 2478545) B2478545
theorem B7059089 : Blo 1651525 7059089 := bstep (se 2 (by rfl) ⟨2647158, by rfl⟩ : syracuseStep 7059089 = 5294317) B5294317
theorem B1652375 : Blo 1651525 1652375 := bstep (se 1 (by rfl) ⟨1239281, by rfl⟩ : syracuseStep 1652375 = 2478563) B2478563
theorem B2479769 : Blo 1651525 2479769 := bstep (se 2 (by rfl) ⟨929913, by rfl⟩ : syracuseStep 2479769 = 1859827) B1859827
theorem B1652395 : Blo 1651525 1652395 := bstep (se 1 (by rfl) ⟨1239296, by rfl⟩ : syracuseStep 1652395 = 2478593) B2478593
theorem B7534259 : Blo 1651525 7534259 := bstep (se 1 (by rfl) ⟨5650694, by rfl⟩ : syracuseStep 7534259 = 11301389) B11301389
theorem B6698675 : Blo 1651525 6698675 := bstep (se 1 (by rfl) ⟨5024006, by rfl⟩ : syracuseStep 6698675 = 10048013) B10048013
theorem B4708019 : Blo 1651525 4708019 := bstep (se 1 (by rfl) ⟨3531014, by rfl⟩ : syracuseStep 4708019 = 7062029) B7062029
theorem B1652407 : Blo 1651525 1652407 := bstep (se 1 (by rfl) ⟨1239305, by rfl⟩ : syracuseStep 1652407 = 2478611) B2478611
theorem B3716801 : Blo 1651525 3716801 := bstep (se 2 (by rfl) ⟨1393800, by rfl⟩ : syracuseStep 3716801 = 2787601) B2787601
theorem B1652427 : Blo 1651525 1652427 := bstep (se 1 (by rfl) ⟨1239320, by rfl⟩ : syracuseStep 1652427 = 2478641) B2478641
theorem B1652439 : Blo 1651525 1652439 := bstep (se 1 (by rfl) ⟨1239329, by rfl⟩ : syracuseStep 1652439 = 2478659) B2478659
theorem B1652459 : Blo 1651525 1652459 := bstep (se 1 (by rfl) ⟨1239344, by rfl⟩ : syracuseStep 1652459 = 2478689) B2478689
theorem B1652471 : Blo 1651525 1652471 := bstep (se 1 (by rfl) ⟨1239353, by rfl⟩ : syracuseStep 1652471 = 2478707) B2478707
theorem B5953283 : Blo 1651525 5953283 := bstep (se 1 (by rfl) ⟨4464962, by rfl⟩ : syracuseStep 5953283 = 8929925) B8929925
theorem B1652491 : Blo 1651525 1652491 := bstep (se 1 (by rfl) ⟨1239368, by rfl⟩ : syracuseStep 1652491 = 2478737) B2478737
theorem B2479883 : Blo 1651525 2479883 := bstep (se 1 (by rfl) ⟨1859912, by rfl⟩ : syracuseStep 2479883 = 3719825) B3719825
theorem B5576471 : Blo 1651525 5576471 := bstep (se 1 (by rfl) ⟨4182353, by rfl⟩ : syracuseStep 5576471 = 8364707) B8364707
theorem B1652503 : Blo 1651525 1652503 := bstep (se 1 (by rfl) ⟨1239377, by rfl⟩ : syracuseStep 1652503 = 2478755) B2478755
theorem B2479895 : Blo 1651525 2479895 := bstep (se 1 (by rfl) ⟨1859921, by rfl⟩ : syracuseStep 2479895 = 3719843) B3719843
theorem B1652523 : Blo 1651525 1652523 := bstep (se 1 (by rfl) ⟨1239392, by rfl⟩ : syracuseStep 1652523 = 2478785) B2478785
theorem B1652535 : Blo 1651525 1652535 := bstep (se 1 (by rfl) ⟨1239401, by rfl⟩ : syracuseStep 1652535 = 2478803) B2478803
theorem B1652555 : Blo 1651525 1652555 := bstep (se 1 (by rfl) ⟨1239416, by rfl⟩ : syracuseStep 1652555 = 2478833) B2478833
theorem B4183883 : Blo 1651525 4183883 := bstep (se 1 (by rfl) ⟨3137912, by rfl⟩ : syracuseStep 4183883 = 6275825) B6275825
theorem B1652567 : Blo 1651525 1652567 := bstep (se 1 (by rfl) ⟨1239425, by rfl⟩ : syracuseStep 1652567 = 2478851) B2478851
theorem B2479961 : Blo 1651525 2479961 := bstep (se 2 (by rfl) ⟨929985, by rfl⟩ : syracuseStep 2479961 = 1859971) B1859971
theorem B1652587 : Blo 1651525 1652587 := bstep (se 1 (by rfl) ⟨1239440, by rfl⟩ : syracuseStep 1652587 = 2478881) B2478881
theorem B1652599 : Blo 1651525 1652599 := bstep (se 1 (by rfl) ⟨1239449, by rfl⟩ : syracuseStep 1652599 = 2478899) B2478899
theorem B3135361 : Blo 1651525 3135361 := bstep (se 2 (by rfl) ⟨1175760, by rfl⟩ : syracuseStep 3135361 = 2351521) B2351521
theorem B1652619 : Blo 1651525 1652619 := bstep (se 1 (by rfl) ⟨1239464, by rfl⟩ : syracuseStep 1652619 = 2478929) B2478929
theorem B1652631 : Blo 1651525 1652631 := bstep (se 1 (by rfl) ⟨1239473, by rfl⟩ : syracuseStep 1652631 = 2478947) B2478947
theorem B3717017 : Blo 1651525 3717017 := bstep (se 2 (by rfl) ⟨1393881, by rfl⟩ : syracuseStep 3717017 = 2787763) B2787763
theorem B1652651 : Blo 1651525 1652651 := bstep (se 1 (by rfl) ⟨1239488, by rfl⟩ : syracuseStep 1652651 = 2478977) B2478977
theorem B1652663 : Blo 1651525 1652663 := bstep (se 1 (by rfl) ⟨1239497, by rfl⟩ : syracuseStep 1652663 = 2478995) B2478995
theorem B1652683 : Blo 1651525 1652683 := bstep (se 1 (by rfl) ⟨1239512, by rfl⟩ : syracuseStep 1652683 = 2479025) B2479025
theorem B2480075 : Blo 1651525 2480075 := bstep (se 1 (by rfl) ⟨1860056, by rfl⟩ : syracuseStep 2480075 = 3720113) B3720113
theorem B1652695 : Blo 1651525 1652695 := bstep (se 1 (by rfl) ⟨1239521, by rfl⟩ : syracuseStep 1652695 = 2479043) B2479043
theorem B2480087 : Blo 1651525 2480087 := bstep (se 1 (by rfl) ⟨1860065, by rfl⟩ : syracuseStep 2480087 = 3720131) B3720131
theorem B1652715 : Blo 1651525 1652715 := bstep (se 1 (by rfl) ⟨1239536, by rfl⟩ : syracuseStep 1652715 = 2479073) B2479073
theorem B3717107 : Blo 1651525 3717107 := bstep (se 1 (by rfl) ⟨2787830, by rfl⟩ : syracuseStep 3717107 = 5575661) B5575661
theorem B1652727 : Blo 1651525 1652727 := bstep (se 1 (by rfl) ⟨1239545, by rfl⟩ : syracuseStep 1652727 = 2479091) B2479091
theorem B1652747 : Blo 1651525 1652747 := bstep (se 1 (by rfl) ⟨1239560, by rfl⟩ : syracuseStep 1652747 = 2479121) B2479121
theorem B3717143 : Blo 1651525 3717143 := bstep (se 1 (by rfl) ⟨2787857, by rfl⟩ : syracuseStep 3717143 = 5575715) B5575715
theorem B1652759 : Blo 1651525 1652759 := bstep (se 1 (by rfl) ⟨1239569, by rfl⟩ : syracuseStep 1652759 = 2479139) B2479139
theorem B2480153 : Blo 1651525 2480153 := bstep (se 2 (by rfl) ⟨930057, by rfl⟩ : syracuseStep 2480153 = 1860115) B1860115
theorem B1652779 : Blo 1651525 1652779 := bstep (se 1 (by rfl) ⟨1239584, by rfl⟩ : syracuseStep 1652779 = 2479169) B2479169
theorem B3971123 : Blo 1651525 3971123 := bstep (se 1 (by rfl) ⟨2978342, by rfl⟩ : syracuseStep 3971123 = 5956685) B5956685
theorem B1652791 : Blo 1651525 1652791 := bstep (se 1 (by rfl) ⟨1239593, by rfl⟩ : syracuseStep 1652791 = 2479187) B2479187
theorem B1652811 : Blo 1651525 1652811 := bstep (se 1 (by rfl) ⟨1239608, by rfl⟩ : syracuseStep 1652811 = 2479217) B2479217
theorem B1652823 : Blo 1651525 1652823 := bstep (se 1 (by rfl) ⟨1239617, by rfl⟩ : syracuseStep 1652823 = 2479235) B2479235
theorem B3528793 : Blo 1651525 3528793 := bstep (se 2 (by rfl) ⟨1323297, by rfl⟩ : syracuseStep 3528793 = 2646595) B2646595
theorem B1652843 : Blo 1651525 1652843 := bstep (se 1 (by rfl) ⟨1239632, by rfl⟩ : syracuseStep 1652843 = 2479265) B2479265
theorem B1652855 : Blo 1651525 1652855 := bstep (se 1 (by rfl) ⟨1239641, by rfl⟩ : syracuseStep 1652855 = 2479283) B2479283
theorem B8362115 : Blo 1651525 8362115 := bstep (se 1 (by rfl) ⟨6271586, by rfl⟩ : syracuseStep 8362115 = 12543173) B12543173
theorem B1652875 : Blo 1651525 1652875 := bstep (se 1 (by rfl) ⟨1239656, by rfl⟩ : syracuseStep 1652875 = 2479313) B2479313
theorem B2480267 : Blo 1651525 2480267 := bstep (se 1 (by rfl) ⟨1860200, by rfl⟩ : syracuseStep 2480267 = 3720401) B3720401
theorem B2119831 : Blo 1651525 2119831 := bstep (se 1 (by rfl) ⟨1589873, by rfl⟩ : syracuseStep 2119831 = 3179747) B3179747
theorem B1652887 : Blo 1651525 1652887 := bstep (se 1 (by rfl) ⟨1239665, by rfl⟩ : syracuseStep 1652887 = 2479331) B2479331
theorem B2480279 : Blo 1651525 2480279 := bstep (se 1 (by rfl) ⟨1860209, by rfl⟩ : syracuseStep 2480279 = 3720419) B3720419
theorem B1652907 : Blo 1651525 1652907 := bstep (se 1 (by rfl) ⟨1239680, by rfl⟩ : syracuseStep 1652907 = 2479361) B2479361
theorem B6273197 : Blo 1651525 6273197 := bstep (se 3 (by rfl) ⟨1176224, by rfl⟩ : syracuseStep 6273197 = 2352449) B2352449
theorem B1652919 : Blo 1651525 1652919 := bstep (se 1 (by rfl) ⟨1239689, by rfl⟩ : syracuseStep 1652919 = 2479379) B2479379
theorem B4184257 : Blo 1651525 4184257 := bstep (se 2 (by rfl) ⟨1569096, by rfl⟩ : syracuseStep 4184257 = 3138193) B3138193
theorem B3717323 : Blo 1651525 3717323 := bstep (se 1 (by rfl) ⟨2787992, by rfl⟩ : syracuseStep 3717323 = 5575985) B5575985
theorem B6273227 : Blo 1651525 6273227 := bstep (se 1 (by rfl) ⟨4704920, by rfl⟩ : syracuseStep 6273227 = 9409841) B9409841
theorem B2513099 : Blo 1651525 2513099 := bstep (se 1 (by rfl) ⟨1884824, by rfl⟩ : syracuseStep 2513099 = 3769649) B3769649
theorem B1652939 : Blo 1651525 1652939 := bstep (se 1 (by rfl) ⟨1239704, by rfl⟩ : syracuseStep 1652939 = 2479409) B2479409
theorem B1652951 : Blo 1651525 1652951 := bstep (se 1 (by rfl) ⟨1239713, by rfl⟩ : syracuseStep 1652951 = 2479427) B2479427
theorem B10885337 : Blo 1651525 10885337 := bstep (se 2 (by rfl) ⟨4082001, by rfl⟩ : syracuseStep 10885337 = 8164003) B8164003
theorem B1652971 : Blo 1651525 1652971 := bstep (se 1 (by rfl) ⟨1239728, by rfl⟩ : syracuseStep 1652971 = 2479457) B2479457
theorem B3528947 : Blo 1651525 3528947 := bstep (se 1 (by rfl) ⟨2646710, by rfl⟩ : syracuseStep 3528947 = 5293421) B5293421
theorem B1652983 : Blo 1651525 1652983 := bstep (se 1 (by rfl) ⟨1239737, by rfl⟩ : syracuseStep 1652983 = 2479475) B2479475
theorem B3717377 : Blo 1651525 3717377 := bstep (se 2 (by rfl) ⟨1394016, by rfl⟩ : syracuseStep 3717377 = 2788033) B2788033
theorem B1653003 : Blo 1651525 1653003 := bstep (se 1 (by rfl) ⟨1239752, by rfl⟩ : syracuseStep 1653003 = 2479505) B2479505
theorem B1653015 : Blo 1651525 1653015 := bstep (se 1 (by rfl) ⟨1239761, by rfl⟩ : syracuseStep 1653015 = 2479523) B2479523
theorem B1653035 : Blo 1651525 1653035 := bstep (se 1 (by rfl) ⟨1239776, by rfl⟩ : syracuseStep 1653035 = 2479553) B2479553
theorem B7059757 : Blo 1651525 7059757 := bstep (se 3 (by rfl) ⟨1323704, by rfl⟩ : syracuseStep 7059757 = 2647409) B2647409
theorem B5577011 : Blo 1651525 5577011 := bstep (se 1 (by rfl) ⟨4182758, by rfl⟩ : syracuseStep 5577011 = 8365517) B8365517
theorem B1653047 : Blo 1651525 1653047 := bstep (se 1 (by rfl) ⟨1239785, by rfl⟩ : syracuseStep 1653047 = 2479571) B2479571
theorem B3135809 : Blo 1651525 3135809 := bstep (se 2 (by rfl) ⟨1175928, by rfl⟩ : syracuseStep 3135809 = 2351857) B2351857
theorem B1653067 : Blo 1651525 1653067 := bstep (se 1 (by rfl) ⟨1239800, by rfl⟩ : syracuseStep 1653067 = 2479601) B2479601
theorem B1653079 : Blo 1651525 1653079 := bstep (se 1 (by rfl) ⟨1239809, by rfl⟩ : syracuseStep 1653079 = 2479619) B2479619
theorem B1653099 : Blo 1651525 1653099 := bstep (se 1 (by rfl) ⟨1239824, by rfl⟩ : syracuseStep 1653099 = 2479649) B2479649
theorem B1653111 : Blo 1651525 1653111 := bstep (se 1 (by rfl) ⟨1239833, by rfl⟩ : syracuseStep 1653111 = 2479667) B2479667
theorem B1653131 : Blo 1651525 1653131 := bstep (se 1 (by rfl) ⟨1239848, by rfl⟩ : syracuseStep 1653131 = 2479697) B2479697
theorem B1653143 : Blo 1651525 1653143 := bstep (se 1 (by rfl) ⟨1239857, by rfl⟩ : syracuseStep 1653143 = 2479715) B2479715
theorem B1653163 : Blo 1651525 1653163 := bstep (se 1 (by rfl) ⟨1239872, by rfl⟩ : syracuseStep 1653163 = 2479745) B2479745
theorem B1653175 : Blo 1651525 1653175 := bstep (se 1 (by rfl) ⟨1239881, by rfl⟩ : syracuseStep 1653175 = 2479763) B2479763
theorem B1653195 : Blo 1651525 1653195 := bstep (se 1 (by rfl) ⟨1239896, by rfl⟩ : syracuseStep 1653195 = 2479793) B2479793
theorem B1653207 : Blo 1651525 1653207 := bstep (se 1 (by rfl) ⟨1239905, by rfl⟩ : syracuseStep 1653207 = 2479811) B2479811
theorem B3717593 : Blo 1651525 3717593 := bstep (se 2 (by rfl) ⟨1394097, by rfl⟩ : syracuseStep 3717593 = 2788195) B2788195
theorem B1858027 : Blo 1651525 1858027 := bstep (se 1 (by rfl) ⟨1393520, by rfl⟩ : syracuseStep 1858027 = 2787041) B2787041
theorem B1653227 : Blo 1651525 1653227 := bstep (se 1 (by rfl) ⟨1239920, by rfl⟩ : syracuseStep 1653227 = 2479841) B2479841
theorem B1653239 : Blo 1651525 1653239 := bstep (se 1 (by rfl) ⟨1239929, by rfl⟩ : syracuseStep 1653239 = 2479859) B2479859
theorem B1653259 : Blo 1651525 1653259 := bstep (se 1 (by rfl) ⟨1239944, by rfl⟩ : syracuseStep 1653259 = 2479889) B2479889
theorem B1653271 : Blo 1651525 1653271 := bstep (se 1 (by rfl) ⟨1239953, by rfl⟩ : syracuseStep 1653271 = 2479907) B2479907
theorem B1653291 : Blo 1651525 1653291 := bstep (se 1 (by rfl) ⟨1239968, by rfl⟩ : syracuseStep 1653291 = 2479937) B2479937
theorem B3717683 : Blo 1651525 3717683 := bstep (se 1 (by rfl) ⟨2788262, by rfl⟩ : syracuseStep 3717683 = 5576525) B5576525
theorem B1653303 : Blo 1651525 1653303 := bstep (se 1 (by rfl) ⟨1239977, by rfl⟩ : syracuseStep 1653303 = 2479955) B2479955
theorem B5577281 : Blo 1651525 5577281 := bstep (se 2 (by rfl) ⟨2091480, by rfl⟩ : syracuseStep 5577281 = 4182961) B4182961
theorem B1653323 : Blo 1651525 1653323 := bstep (se 1 (by rfl) ⟨1239992, by rfl⟩ : syracuseStep 1653323 = 2479985) B2479985
theorem B1858135 : Blo 1651525 1858135 := bstep (se 1 (by rfl) ⟨1393601, by rfl⟩ : syracuseStep 1858135 = 2787203) B2787203
theorem B3717719 : Blo 1651525 3717719 := bstep (se 1 (by rfl) ⟨2788289, by rfl⟩ : syracuseStep 3717719 = 5576579) B5576579
theorem B1653335 : Blo 1651525 1653335 := bstep (se 1 (by rfl) ⟨1240001, by rfl⟩ : syracuseStep 1653335 = 2480003) B2480003
theorem B1653355 : Blo 1651525 1653355 := bstep (se 1 (by rfl) ⟨1240016, by rfl⟩ : syracuseStep 1653355 = 2480033) B2480033
theorem B1653367 : Blo 1651525 1653367 := bstep (se 1 (by rfl) ⟨1240025, by rfl⟩ : syracuseStep 1653367 = 2480051) B2480051
theorem B11917955 : Blo 1651525 11917955 := bstep (se 1 (by rfl) ⟨8938466, by rfl⟩ : syracuseStep 11917955 = 17876933) B17876933
theorem B1653387 : Blo 1651525 1653387 := bstep (se 1 (by rfl) ⟨1240040, by rfl⟩ : syracuseStep 1653387 = 2480081) B2480081
theorem B3136151 : Blo 1651525 3136151 := bstep (se 1 (by rfl) ⟨2352113, by rfl⟩ : syracuseStep 3136151 = 4704227) B4704227
theorem B1653399 : Blo 1651525 1653399 := bstep (se 1 (by rfl) ⟨1240049, by rfl⟩ : syracuseStep 1653399 = 2480099) B2480099
theorem B1653419 : Blo 1651525 1653419 := bstep (se 1 (by rfl) ⟨1240064, by rfl⟩ : syracuseStep 1653419 = 2480129) B2480129
theorem B1653431 : Blo 1651525 1653431 := bstep (se 1 (by rfl) ⟨1240073, by rfl⟩ : syracuseStep 1653431 = 2480147) B2480147
theorem B1653451 : Blo 1651525 1653451 := bstep (se 1 (by rfl) ⟨1240088, by rfl⟩ : syracuseStep 1653451 = 2480177) B2480177
theorem B1653463 : Blo 1651525 1653463 := bstep (se 1 (by rfl) ⟨1240097, by rfl⟩ : syracuseStep 1653463 = 2480195) B2480195
theorem B1653483 : Blo 1651525 1653483 := bstep (se 1 (by rfl) ⟨1240112, by rfl⟩ : syracuseStep 1653483 = 2480225) B2480225
theorem B1653495 : Blo 1651525 1653495 := bstep (se 1 (by rfl) ⟨1240121, by rfl⟩ : syracuseStep 1653495 = 2480243) B2480243
theorem B1858315 : Blo 1651525 1858315 := bstep (se 1 (by rfl) ⟨1393736, by rfl⟩ : syracuseStep 1858315 = 2787473) B2787473
theorem B3717899 : Blo 1651525 3717899 := bstep (se 1 (by rfl) ⟨2788424, by rfl⟩ : syracuseStep 3717899 = 5576849) B5576849
theorem B1653515 : Blo 1651525 1653515 := bstep (se 1 (by rfl) ⟨1240136, by rfl⟩ : syracuseStep 1653515 = 2480273) B2480273
theorem B4184855 : Blo 1651525 4184855 := bstep (se 1 (by rfl) ⟨3138641, by rfl⟩ : syracuseStep 4184855 = 6277283) B6277283
theorem B8936237 : Blo 1651525 8936237 := bstep (se 3 (by rfl) ⟨1675544, by rfl⟩ : syracuseStep 8936237 = 3351089) B3351089
theorem B14113601 : Blo 1651525 14113601 := bstep (se 2 (by rfl) ⟨5292600, by rfl⟩ : syracuseStep 14113601 = 10585201) B10585201
theorem B3717953 : Blo 1651525 3717953 := bstep (se 2 (by rfl) ⟨1394232, by rfl⟩ : syracuseStep 3717953 = 2788465) B2788465
theorem B6273881 : Blo 1651525 6273881 := bstep (se 2 (by rfl) ⟨2352705, by rfl⟩ : syracuseStep 6273881 = 4705411) B4705411
theorem B1858423 : Blo 1651525 1858423 := bstep (se 1 (by rfl) ⟨1393817, by rfl⟩ : syracuseStep 1858423 = 2787635) B2787635
theorem B7060355 : Blo 1651525 7060355 := bstep (se 1 (by rfl) ⟨5295266, by rfl⟩ : syracuseStep 7060355 = 10590533) B10590533
theorem B7945091 : Blo 1651525 7945091 := bstep (se 1 (by rfl) ⟨5958818, by rfl⟩ : syracuseStep 7945091 = 11917637) B11917637
theorem B3718169 : Blo 1651525 3718169 := bstep (se 2 (by rfl) ⟨1394313, by rfl⟩ : syracuseStep 3718169 = 2788627) B2788627
theorem B1858603 : Blo 1651525 1858603 := bstep (se 1 (by rfl) ⟨1393952, by rfl⟩ : syracuseStep 1858603 = 2787905) B2787905
theorem B5577821 : Blo 1651525 5577821 := bstep (se 3 (by rfl) ⟨1045841, by rfl⟩ : syracuseStep 5577821 = 2091683) B2091683
theorem B3718259 : Blo 1651525 3718259 := bstep (se 1 (by rfl) ⟨2788694, by rfl⟩ : syracuseStep 3718259 = 5577389) B5577389
theorem B2514059 : Blo 1651525 2514059 := bstep (se 1 (by rfl) ⟨1885544, by rfl⟩ : syracuseStep 2514059 = 3771089) B3771089
theorem B1858711 : Blo 1651525 1858711 := bstep (se 1 (by rfl) ⟨1394033, by rfl⟩ : syracuseStep 1858711 = 2788067) B2788067
theorem B6274199 : Blo 1651525 6274199 := bstep (se 1 (by rfl) ⟨4705649, by rfl⟩ : syracuseStep 6274199 = 9411299) B9411299
theorem B3718295 : Blo 1651525 3718295 := bstep (se 1 (by rfl) ⟨2788721, by rfl⟩ : syracuseStep 3718295 = 5577443) B5577443
theorem B3529921 : Blo 1651525 3529921 := bstep (se 2 (by rfl) ⟨1323720, by rfl⟩ : syracuseStep 3529921 = 2647441) B2647441
theorem B28613837 : Blo 1651525 28613837 := bstep (se 3 (by rfl) ⟨5365094, by rfl⟩ : syracuseStep 28613837 = 10730189) B10730189
theorem B10591505 : Blo 1651525 10591505 := bstep (se 2 (by rfl) ⟨3971814, by rfl⟩ : syracuseStep 10591505 = 7943629) B7943629
theorem B14499107 : Blo 1651525 14499107 := bstep (se 1 (by rfl) ⟨10874330, by rfl⟩ : syracuseStep 14499107 = 21748661) B21748661
theorem B3767603 : Blo 1651525 3767603 := bstep (se 1 (by rfl) ⟨2825702, by rfl⟩ : syracuseStep 3767603 = 5651405) B5651405
theorem B3136819 : Blo 1651525 3136819 := bstep (se 1 (by rfl) ⟨2352614, by rfl⟩ : syracuseStep 3136819 = 4705229) B4705229
theorem B1858891 : Blo 1651525 1858891 := bstep (se 1 (by rfl) ⟨1394168, by rfl⟩ : syracuseStep 1858891 = 2788337) B2788337
theorem B3718475 : Blo 1651525 3718475 := bstep (se 1 (by rfl) ⟨2788856, by rfl⟩ : syracuseStep 3718475 = 5577713) B5577713
theorem B3718529 : Blo 1651525 3718529 := bstep (se 2 (by rfl) ⟨1394448, by rfl⟩ : syracuseStep 3718529 = 2788897) B2788897
theorem B3767705 : Blo 1651525 3767705 := bstep (se 2 (by rfl) ⟨1412889, by rfl⟩ : syracuseStep 3767705 = 2825779) B2825779
theorem B1858999 : Blo 1651525 1858999 := bstep (se 1 (by rfl) ⟨1394249, by rfl⟩ : syracuseStep 1858999 = 2788499) B2788499
theorem B3350003 : Blo 1651525 3350003 := bstep (se 1 (by rfl) ⟨2512502, by rfl⟩ : syracuseStep 3350003 = 5025005) B5025005
theorem B3530263 : Blo 1651525 3530263 := bstep (se 1 (by rfl) ⟨2647697, by rfl⟩ : syracuseStep 3530263 = 5295395) B5295395
theorem B3718745 : Blo 1651525 3718745 := bstep (se 2 (by rfl) ⟨1394529, by rfl⟩ : syracuseStep 3718745 = 2789059) B2789059
theorem B1859179 : Blo 1651525 1859179 := bstep (se 1 (by rfl) ⟨1394384, by rfl⟩ : syracuseStep 1859179 = 2788769) B2788769
theorem B3718835 : Blo 1651525 3718835 := bstep (se 1 (by rfl) ⟨2789126, by rfl⟩ : syracuseStep 3718835 = 5578253) B5578253
theorem B1859287 : Blo 1651525 1859287 := bstep (se 1 (by rfl) ⟨1394465, by rfl⟩ : syracuseStep 1859287 = 2788931) B2788931
theorem B3718871 : Blo 1651525 3718871 := bstep (se 1 (by rfl) ⟨2789153, by rfl⟩ : syracuseStep 3718871 = 5578307) B5578307
theorem B3137267 : Blo 1651525 3137267 := bstep (se 1 (by rfl) ⟨2352950, by rfl⟩ : syracuseStep 3137267 = 4705901) B4705901
theorem B3137305 : Blo 1651525 3137305 := bstep (se 2 (by rfl) ⟨1176489, by rfl⟩ : syracuseStep 3137305 = 2352979) B2352979
theorem B6274867 : Blo 1651525 6274867 := bstep (se 1 (by rfl) ⟨4706150, by rfl⟩ : syracuseStep 6274867 = 9412301) B9412301
theorem B9412483 : Blo 1651525 9412483 := bstep (se 1 (by rfl) ⟨7059362, by rfl⟩ : syracuseStep 9412483 = 14118725) B14118725
theorem B1859467 : Blo 1651525 1859467 := bstep (se 1 (by rfl) ⟨1394600, by rfl⟩ : syracuseStep 1859467 = 2789201) B2789201
theorem B3719051 : Blo 1651525 3719051 := bstep (se 1 (by rfl) ⟨2789288, by rfl⟩ : syracuseStep 3719051 = 5578577) B5578577
theorem B18816947 : Blo 1651525 18816947 := bstep (se 1 (by rfl) ⟨14112710, by rfl⟩ : syracuseStep 18816947 = 28225421) B28225421
theorem B3719105 : Blo 1651525 3719105 := bstep (se 2 (by rfl) ⟨1394664, by rfl⟩ : syracuseStep 3719105 = 2789329) B2789329
theorem B3530699 : Blo 1651525 3530699 := bstep (se 1 (by rfl) ⟨2648024, by rfl⟩ : syracuseStep 3530699 = 5296049) B5296049
theorem B1859575 : Blo 1651525 1859575 := bstep (se 1 (by rfl) ⟨1394681, by rfl⟩ : syracuseStep 1859575 = 2789363) B2789363
theorem B2646031 : Blo 1651525 2646031 := bstep (se 1 (by rfl) ⟨1984523, by rfl⟩ : syracuseStep 2646031 = 3969047) B3969047
theorem B3768335 : Blo 1651525 3768335 := bstep (se 1 (by rfl) ⟨2826251, by rfl⟩ : syracuseStep 3768335 = 5652503) B5652503
theorem B3719303 : Blo 1651525 3719303 := bstep (se 1 (by rfl) ⟨2789477, by rfl⟩ : syracuseStep 3719303 = 5578955) B5578955
theorem B1859719 : Blo 1651525 1859719 := bstep (se 1 (by rfl) ⟨1394789, by rfl⟩ : syracuseStep 1859719 = 2789579) B2789579
theorem B42344693 : Blo 1651525 42344693 := bstep (se 5 (by rfl) ⟨1984907, by rfl⟩ : syracuseStep 42344693 = 3969815) B3969815
theorem B23822581 : Blo 1651525 23822581 := bstep (se 5 (by rfl) ⟨1116683, by rfl⟩ : syracuseStep 23822581 = 2233367) B2233367
theorem B5579009 : Blo 1651525 5579009 := bstep (se 2 (by rfl) ⟨2092128, by rfl⟩ : syracuseStep 5579009 = 4184257) B4184257
theorem B3719483 : Blo 1651525 3719483 := bstep (se 1 (by rfl) ⟨2789612, by rfl⟩ : syracuseStep 3719483 = 5579225) B5579225
theorem B1859899 : Blo 1651525 1859899 := bstep (se 1 (by rfl) ⟨1394924, by rfl⟩ : syracuseStep 1859899 = 2789849) B2789849
theorem B9413009 : Blo 1651525 9413009 := bstep (se 2 (by rfl) ⟨3529878, by rfl⟩ : syracuseStep 9413009 = 7059757) B7059757
theorem B3719609 : Blo 1651525 3719609 := bstep (se 2 (by rfl) ⟨1394853, by rfl⟩ : syracuseStep 3719609 = 2789707) B2789707
theorem B14311889 : Blo 1651525 14311889 := bstep (se 2 (by rfl) ⟨5366958, by rfl⟩ : syracuseStep 14311889 = 10733917) B10733917
theorem B6275627 : Blo 1651525 6275627 := bstep (se 1 (by rfl) ⟨4706720, by rfl⟩ : syracuseStep 6275627 = 9413441) B9413441
theorem B15885071 : Blo 1651525 15885071 := bstep (se 1 (by rfl) ⟨11913803, by rfl⟩ : syracuseStep 15885071 = 23827607) B23827607
theorem B3719951 : Blo 1651525 3719951 := bstep (se 1 (by rfl) ⟨2789963, by rfl⟩ : syracuseStep 3719951 = 5579927) B5579927
theorem B3719969 : Blo 1651525 3719969 := bstep (se 2 (by rfl) ⟨1394988, by rfl⟩ : syracuseStep 3719969 = 2789977) B2789977
theorem B34382627 : Blo 1651525 34382627 := bstep (se 1 (by rfl) ⟨25786970, by rfl⟩ : syracuseStep 34382627 = 51573941) B51573941
theorem B11305765 : Blo 1651525 11305765 := bstep (se 4 (by rfl) ⟨1059915, by rfl⟩ : syracuseStep 11305765 = 2119831) B2119831
theorem B12550949 : Blo 1651525 12550949 := bstep (se 4 (by rfl) ⟨1176651, by rfl⟩ : syracuseStep 12550949 = 2353303) B2353303
theorem B5292935 : Blo 1651525 5292935 := bstep (se 1 (by rfl) ⟨3969701, by rfl⟩ : syracuseStep 5292935 = 7939403) B7939403
theorem B5292985 : Blo 1651525 5292985 := bstep (se 2 (by rfl) ⟨1984869, by rfl⟩ : syracuseStep 5292985 = 3969739) B3969739
theorem B2352073 : Blo 1651525 2352073 := bstep (se 2 (by rfl) ⟨882027, by rfl⟩ : syracuseStep 2352073 = 1764055) B1764055
theorem B80413667 : Blo 1651525 80413667 := bstep (se 1 (by rfl) ⟨60310250, by rfl⟩ : syracuseStep 80413667 = 120620501) B120620501
theorem B18834443 : Blo 1651525 18834443 := bstep (se 1 (by rfl) ⟨14125832, by rfl⟩ : syracuseStep 18834443 = 28251665) B28251665
theorem B5579819 : Blo 1651525 5579819 := bstep (se 1 (by rfl) ⟨4184864, by rfl⟩ : syracuseStep 5579819 = 8369729) B8369729
theorem B2352187 : Blo 1651525 2352187 := bstep (se 1 (by rfl) ⟨1764140, by rfl⟩ : syracuseStep 2352187 = 3528281) B3528281
theorem B5022839 : Blo 1651525 5022839 := bstep (se 1 (by rfl) ⟨3767129, by rfl⟩ : syracuseStep 5022839 = 7534259) B7534259
theorem B4465783 : Blo 1651525 4465783 := bstep (se 1 (by rfl) ⟨3349337, by rfl⟩ : syracuseStep 4465783 = 6698675) B6698675
theorem B3138679 : Blo 1651525 3138679 := bstep (se 1 (by rfl) ⟨2354009, by rfl⟩ : syracuseStep 3138679 = 4708019) B4708019
theorem B3720311 : Blo 1651525 3720311 := bstep (se 1 (by rfl) ⟨2790233, by rfl⟩ : syracuseStep 3720311 = 5580467) B5580467
theorem B4703417 : Blo 1651525 4703417 := bstep (se 2 (by rfl) ⟨1763781, by rfl⟩ : syracuseStep 4703417 = 3527563) B3527563
theorem B11912507 : Blo 1651525 11912507 := bstep (se 1 (by rfl) ⟨8934380, by rfl⟩ : syracuseStep 11912507 = 17868761) B17868761
theorem B2647415 : Blo 1651525 2647415 := bstep (se 1 (by rfl) ⟨1985561, by rfl⟩ : syracuseStep 2647415 = 3971123) B3971123
theorem B7538129 : Blo 1651525 7538129 := bstep (se 2 (by rfl) ⟨2826798, by rfl⟩ : syracuseStep 7538129 = 5653597) B5653597
theorem B2090539 : Blo 1651525 2090539 := bstep (se 1 (by rfl) ⟨1567904, by rfl⟩ : syracuseStep 2090539 = 3135809) B3135809
theorem B26789453 : Blo 1651525 26789453 := bstep (se 3 (by rfl) ⟨5023022, by rfl⟩ : syracuseStep 26789453 = 10046045) B10046045
theorem B2090767 : Blo 1651525 2090767 := bstep (se 1 (by rfl) ⟨1568075, by rfl⟩ : syracuseStep 2090767 = 3136151) B3136151
theorem B2787115 : Blo 1651525 2787115 := bstep (se 1 (by rfl) ⟨2090336, by rfl⟩ : syracuseStep 2787115 = 4180673) B4180673
theorem B16967513 : Blo 1651525 16967513 := bstep (se 2 (by rfl) ⟨6362817, by rfl⟩ : syracuseStep 16967513 = 12725635) B12725635
theorem B5957491 : Blo 1651525 5957491 := bstep (se 1 (by rfl) ⟨4468118, by rfl⟩ : syracuseStep 5957491 = 8936237) B8936237
theorem B2787257 : Blo 1651525 2787257 := bstep (se 2 (by rfl) ⟨1045221, by rfl⟩ : syracuseStep 2787257 = 2090443) B2090443
theorem B16107923 : Blo 1651525 16107923 := bstep (se 1 (by rfl) ⟨12080942, by rfl⟩ : syracuseStep 16107923 = 24161885) B24161885
theorem B8366489 : Blo 1651525 8366489 := bstep (se 2 (by rfl) ⟨3137433, by rfl⟩ : syracuseStep 8366489 = 6274867) B6274867
theorem B2091511 : Blo 1651525 2091511 := bstep (se 1 (by rfl) ⟨1568633, by rfl⟩ : syracuseStep 2091511 = 3137267) B3137267
theorem B4180481 : Blo 1651525 4180481 := bstep (se 2 (by rfl) ⟨1567680, by rfl⟩ : syracuseStep 4180481 = 3135361) B3135361
theorem B14109227 : Blo 1651525 14109227 := bstep (se 1 (by rfl) ⟨10581920, by rfl⟩ : syracuseStep 14109227 = 21163841) B21163841
theorem B12544631 : Blo 1651525 12544631 := bstep (se 1 (by rfl) ⟨9408473, by rfl⟩ : syracuseStep 12544631 = 18816947) B18816947
theorem B2787959 : Blo 1651525 2787959 := bstep (se 1 (by rfl) ⟨2090969, by rfl⟩ : syracuseStep 2787959 = 4181939) B4181939
theorem B6703735 : Blo 1651525 6703735 := bstep (se 1 (by rfl) ⟨5027801, by rfl⟩ : syracuseStep 6703735 = 10055603) B10055603
theorem B3770999 : Blo 1651525 3770999 := bstep (se 1 (by rfl) ⟨2828249, by rfl⟩ : syracuseStep 3770999 = 5656499) B5656499
theorem B2353799 : Blo 1651525 2353799 := bstep (se 1 (by rfl) ⟨1765349, by rfl⟩ : syracuseStep 2353799 = 3530699) B3530699
theorem B9407177 : Blo 1651525 9407177 := bstep (se 2 (by rfl) ⟨3527691, by rfl⟩ : syracuseStep 9407177 = 7055383) B7055383
theorem B5368577 : Blo 1651525 5368577 := bstep (se 2 (by rfl) ⟨2013216, by rfl⟩ : syracuseStep 5368577 = 4026433) B4026433
theorem B2976527 : Blo 1651525 2976527 := bstep (se 1 (by rfl) ⟨2232395, by rfl⟩ : syracuseStep 2976527 = 4464791) B4464791
theorem B13404943 : Blo 1651525 13404943 := bstep (se 1 (by rfl) ⟨10053707, by rfl⟩ : syracuseStep 13404943 = 20107415) B20107415
theorem B4705057 : Blo 1651525 4705057 := bstep (se 2 (by rfl) ⟨1764396, by rfl⟩ : syracuseStep 4705057 = 3528793) B3528793
theorem B2091835 : Blo 1651525 2091835 := bstep (se 1 (by rfl) ⟨1568876, by rfl⟩ : syracuseStep 2091835 = 3137753) B3137753
theorem B4180855 : Blo 1651525 4180855 := bstep (se 1 (by rfl) ⟨3135641, by rfl⟩ : syracuseStep 4180855 = 6271283) B6271283
theorem B1674247 : Blo 1651525 1674247 := bstep (se 1 (by rfl) ⟨1255685, by rfl⟩ : syracuseStep 1674247 = 2511371) B2511371
theorem B2788411 : Blo 1651525 2788411 := bstep (se 1 (by rfl) ⟨2091308, by rfl⟩ : syracuseStep 2788411 = 4182617) B4182617
theorem B4467773 : Blo 1651525 4467773 := bstep (se 3 (by rfl) ⟨837707, by rfl⟩ : syracuseStep 4467773 = 1675415) B1675415
theorem B36211799 : Blo 1651525 36211799 := bstep (se 1 (by rfl) ⟨27158849, by rfl⟩ : syracuseStep 36211799 = 54317699) B54317699
theorem B14117975 : Blo 1651525 14117975 := bstep (se 1 (by rfl) ⟨10588481, by rfl⟩ : syracuseStep 14117975 = 21176963) B21176963
theorem B2788553 : Blo 1651525 2788553 := bstep (se 2 (by rfl) ⟨1045707, by rfl⟩ : syracuseStep 2788553 = 2091415) B2091415
theorem B76303565 : Blo 1651525 76303565 := bstep (se 3 (by rfl) ⟨14306918, by rfl⟩ : syracuseStep 76303565 = 28613837) B28613837
theorem B2477303 : Blo 1651525 2477303 := bstep (se 1 (by rfl) ⟨1857977, by rfl⟩ : syracuseStep 2477303 = 3715955) B3715955
theorem B2477327 : Blo 1651525 2477327 := bstep (se 1 (by rfl) ⟨1857995, by rfl⟩ : syracuseStep 2477327 = 3715991) B3715991
theorem B4181291 : Blo 1651525 4181291 := bstep (se 1 (by rfl) ⟨3135968, by rfl⟩ : syracuseStep 4181291 = 6271937) B6271937
theorem B2092331 : Blo 1651525 2092331 := bstep (se 1 (by rfl) ⟨1569248, by rfl⟩ : syracuseStep 2092331 = 3138497) B3138497
theorem B2477369 : Blo 1651525 2477369 := bstep (se 2 (by rfl) ⟨929013, by rfl⟩ : syracuseStep 2477369 = 1858027) B1858027
theorem B4525399 : Blo 1651525 4525399 := bstep (se 1 (by rfl) ⟨3394049, by rfl⟩ : syracuseStep 4525399 = 6788099) B6788099
theorem B2477447 : Blo 1651525 2477447 := bstep (se 1 (by rfl) ⟨1858085, by rfl⟩ : syracuseStep 2477447 = 3716171) B3716171
theorem B5574041 : Blo 1651525 5574041 := bstep (se 2 (by rfl) ⟨2090265, by rfl⟩ : syracuseStep 5574041 = 4180531) B4180531
theorem B2477483 : Blo 1651525 2477483 := bstep (se 1 (by rfl) ⟨1858112, by rfl⟩ : syracuseStep 2477483 = 3716225) B3716225
theorem B2477513 : Blo 1651525 2477513 := bstep (se 2 (by rfl) ⟨929067, by rfl⟩ : syracuseStep 2477513 = 1858135) B1858135
theorem B2477627 : Blo 1651525 2477627 := bstep (se 1 (by rfl) ⟨1858220, by rfl⟩ : syracuseStep 2477627 = 3716441) B3716441
theorem B12545603 : Blo 1651525 12545603 := bstep (se 1 (by rfl) ⟨9409202, by rfl⟩ : syracuseStep 12545603 = 18818405) B18818405
theorem B2477687 : Blo 1651525 2477687 := bstep (se 1 (by rfl) ⟨1858265, by rfl⟩ : syracuseStep 2477687 = 3716531) B3716531
theorem B2477711 : Blo 1651525 2477711 := bstep (se 1 (by rfl) ⟨1858283, by rfl⟩ : syracuseStep 2477711 = 3716567) B3716567
theorem B2477753 : Blo 1651525 2477753 := bstep (se 2 (by rfl) ⟨929157, by rfl⟩ : syracuseStep 2477753 = 1858315) B1858315
theorem B2477831 : Blo 1651525 2477831 := bstep (se 1 (by rfl) ⟨1858373, by rfl⟩ : syracuseStep 2477831 = 3716747) B3716747
theorem B10055461 : Blo 1651525 10055461 := bstep (se 4 (by rfl) ⟨942699, by rfl⟩ : syracuseStep 10055461 = 1885399) B1885399
theorem B2477867 : Blo 1651525 2477867 := bstep (se 1 (by rfl) ⟨1858400, by rfl⟩ : syracuseStep 2477867 = 3716801) B3716801
theorem B2477897 : Blo 1651525 2477897 := bstep (se 2 (by rfl) ⟨929211, by rfl⟩ : syracuseStep 2477897 = 1858423) B1858423
theorem B3968855 : Blo 1651525 3968855 := bstep (se 1 (by rfl) ⟨2976641, by rfl⟩ : syracuseStep 3968855 = 5953283) B5953283
theorem B2789255 : Blo 1651525 2789255 := bstep (se 1 (by rfl) ⟨2091941, by rfl⟩ : syracuseStep 2789255 = 4183883) B4183883
theorem B2478011 : Blo 1651525 2478011 := bstep (se 1 (by rfl) ⟨1858508, by rfl⟩ : syracuseStep 2478011 = 3717017) B3717017
theorem B8933341 : Blo 1651525 8933341 := bstep (se 3 (by rfl) ⟨1675001, by rfl⟩ : syracuseStep 8933341 = 3350003) B3350003
theorem B2478071 : Blo 1651525 2478071 := bstep (se 1 (by rfl) ⟨1858553, by rfl⟩ : syracuseStep 2478071 = 3717107) B3717107
theorem B2478095 : Blo 1651525 2478095 := bstep (se 1 (by rfl) ⟨1858571, by rfl⟩ : syracuseStep 2478095 = 3717143) B3717143
theorem B4706333 : Blo 1651525 4706333 := bstep (se 3 (by rfl) ⟨882437, by rfl⟩ : syracuseStep 4706333 = 1764875) B1764875
theorem B2478137 : Blo 1651525 2478137 := bstep (se 2 (by rfl) ⟨929301, by rfl⟩ : syracuseStep 2478137 = 1858603) B1858603
theorem B5574743 : Blo 1651525 5574743 := bstep (se 1 (by rfl) ⟨4181057, by rfl⟩ : syracuseStep 5574743 = 8362115) B8362115
theorem B4182131 : Blo 1651525 4182131 := bstep (se 1 (by rfl) ⟨3136598, by rfl⟩ : syracuseStep 4182131 = 6273197) B6273197
theorem B26816629 : Blo 1651525 26816629 := bstep (se 5 (by rfl) ⟨1257029, by rfl⟩ : syracuseStep 26816629 = 2514059) B2514059
theorem B2478215 : Blo 1651525 2478215 := bstep (se 1 (by rfl) ⟨1858661, by rfl⟩ : syracuseStep 2478215 = 3717323) B3717323
theorem B4182151 : Blo 1651525 4182151 := bstep (se 1 (by rfl) ⟨3136613, by rfl⟩ : syracuseStep 4182151 = 6273227) B6273227
theorem B1675399 : Blo 1651525 1675399 := bstep (se 1 (by rfl) ⟨1256549, by rfl⟩ : syracuseStep 1675399 = 2513099) B2513099
theorem B2478251 : Blo 1651525 2478251 := bstep (se 1 (by rfl) ⟨1858688, by rfl⟩ : syracuseStep 2478251 = 3717377) B3717377
theorem B2478281 : Blo 1651525 2478281 := bstep (se 2 (by rfl) ⟨929355, by rfl⟩ : syracuseStep 2478281 = 1858711) B1858711
theorem B18821321 : Blo 1651525 18821321 := bstep (se 2 (by rfl) ⟨7057995, by rfl⟩ : syracuseStep 18821321 = 14115991) B14115991
theorem B4706561 : Blo 1651525 4706561 := bstep (se 2 (by rfl) ⟨1764960, by rfl⟩ : syracuseStep 4706561 = 3529921) B3529921
theorem B2478395 : Blo 1651525 2478395 := bstep (se 1 (by rfl) ⟨1858796, by rfl⟩ : syracuseStep 2478395 = 3717593) B3717593
theorem B2478455 : Blo 1651525 2478455 := bstep (se 1 (by rfl) ⟨1858841, by rfl⟩ : syracuseStep 2478455 = 3717683) B3717683
theorem B2478479 : Blo 1651525 2478479 := bstep (se 1 (by rfl) ⟨1858859, by rfl⟩ : syracuseStep 2478479 = 3717719) B3717719
theorem B4182425 : Blo 1651525 4182425 := bstep (se 2 (by rfl) ⟨1568409, by rfl⟩ : syracuseStep 4182425 = 3136819) B3136819
theorem B2478521 : Blo 1651525 2478521 := bstep (se 2 (by rfl) ⟨929445, by rfl⟩ : syracuseStep 2478521 = 1858891) B1858891
theorem B2478599 : Blo 1651525 2478599 := bstep (se 1 (by rfl) ⟨1858949, by rfl⟩ : syracuseStep 2478599 = 3717899) B3717899
theorem B2789903 : Blo 1651525 2789903 := bstep (se 1 (by rfl) ⟨2092427, by rfl⟩ : syracuseStep 2789903 = 4184855) B4184855
theorem B9409067 : Blo 1651525 9409067 := bstep (se 1 (by rfl) ⟨7056800, by rfl⟩ : syracuseStep 9409067 = 14113601) B14113601
theorem B2478635 : Blo 1651525 2478635 := bstep (se 1 (by rfl) ⟨1858976, by rfl⟩ : syracuseStep 2478635 = 3717953) B3717953
theorem B4182587 : Blo 1651525 4182587 := bstep (se 1 (by rfl) ⟨3136940, by rfl⟩ : syracuseStep 4182587 = 6273881) B6273881
theorem B5575229 : Blo 1651525 5575229 := bstep (se 3 (by rfl) ⟨1045355, by rfl⟩ : syracuseStep 5575229 = 2090711) B2090711
theorem B2478665 : Blo 1651525 2478665 := bstep (se 2 (by rfl) ⟨929499, by rfl⟩ : syracuseStep 2478665 = 1858999) B1858999
theorem B4706903 : Blo 1651525 4706903 := bstep (se 1 (by rfl) ⟨3530177, by rfl⟩ : syracuseStep 4706903 = 7060355) B7060355
theorem B5296727 : Blo 1651525 5296727 := bstep (se 1 (by rfl) ⟨3972545, by rfl⟩ : syracuseStep 5296727 = 7945091) B7945091
theorem B2478779 : Blo 1651525 2478779 := bstep (se 1 (by rfl) ⟨1859084, by rfl⟩ : syracuseStep 2478779 = 3718169) B3718169
theorem B6697673 : Blo 1651525 6697673 := bstep (se 2 (by rfl) ⟨2511627, by rfl⟩ : syracuseStep 6697673 = 5023255) B5023255
theorem B4707017 : Blo 1651525 4707017 := bstep (se 2 (by rfl) ⟨1765131, by rfl⟩ : syracuseStep 4707017 = 3530263) B3530263
theorem B2478839 : Blo 1651525 2478839 := bstep (se 1 (by rfl) ⟨1859129, by rfl⟩ : syracuseStep 2478839 = 3718259) B3718259
theorem B4182799 : Blo 1651525 4182799 := bstep (se 1 (by rfl) ⟨3137099, by rfl⟩ : syracuseStep 4182799 = 6274199) B6274199
theorem B2478863 : Blo 1651525 2478863 := bstep (se 1 (by rfl) ⟨1859147, by rfl⟩ : syracuseStep 2478863 = 3718295) B3718295
theorem B34861859 : Blo 1651525 34861859 := bstep (se 1 (by rfl) ⟨26146394, by rfl⟩ : syracuseStep 34861859 = 52292789) B52292789
theorem B67867429 : Blo 1651525 67867429 := bstep (se 4 (by rfl) ⟨6362571, by rfl⟩ : syracuseStep 67867429 = 12725143) B12725143
theorem B2478905 : Blo 1651525 2478905 := bstep (se 2 (by rfl) ⟨929589, by rfl⟩ : syracuseStep 2478905 = 1859179) B1859179
theorem B1651591 : Blo 1651525 1651591 := bstep (se 1 (by rfl) ⟨1238693, by rfl⟩ : syracuseStep 1651591 = 2477387) B2477387
theorem B2478983 : Blo 1651525 2478983 := bstep (se 1 (by rfl) ⟨1859237, by rfl⟩ : syracuseStep 2478983 = 3718475) B3718475
theorem B1651599 : Blo 1651525 1651599 := bstep (se 1 (by rfl) ⟨1238699, by rfl⟩ : syracuseStep 1651599 = 2477399) B2477399
theorem B2479019 : Blo 1651525 2479019 := bstep (se 1 (by rfl) ⟨1859264, by rfl⟩ : syracuseStep 2479019 = 3718529) B3718529
theorem B8369081 : Blo 1651525 8369081 := bstep (se 2 (by rfl) ⟨3138405, by rfl⟩ : syracuseStep 8369081 = 6276811) B6276811
theorem B1651643 : Blo 1651525 1651643 := bstep (se 1 (by rfl) ⟨1238732, by rfl⟩ : syracuseStep 1651643 = 2477465) B2477465
theorem B2511803 : Blo 1651525 2511803 := bstep (se 1 (by rfl) ⟨1883852, by rfl⟩ : syracuseStep 2511803 = 3767705) B3767705
theorem B2479049 : Blo 1651525 2479049 := bstep (se 2 (by rfl) ⟨929643, by rfl⟩ : syracuseStep 2479049 = 1859287) B1859287
theorem B1651719 : Blo 1651525 1651719 := bstep (se 1 (by rfl) ⟨1238789, by rfl⟩ : syracuseStep 1651719 = 2477579) B2477579
theorem B1651727 : Blo 1651525 1651727 := bstep (se 1 (by rfl) ⟨1238795, by rfl⟩ : syracuseStep 1651727 = 2477591) B2477591
theorem B4183073 : Blo 1651525 4183073 := bstep (se 2 (by rfl) ⟨1568652, by rfl⟩ : syracuseStep 4183073 = 3137305) B3137305
theorem B1651771 : Blo 1651525 1651771 := bstep (se 1 (by rfl) ⟨1238828, by rfl⟩ : syracuseStep 1651771 = 2477657) B2477657
theorem B2479163 : Blo 1651525 2479163 := bstep (se 1 (by rfl) ⟨1859372, by rfl⟩ : syracuseStep 2479163 = 3718745) B3718745
theorem B2479223 : Blo 1651525 2479223 := bstep (se 1 (by rfl) ⟨1859417, by rfl⟩ : syracuseStep 2479223 = 3718835) B3718835
theorem B1651847 : Blo 1651525 1651847 := bstep (se 1 (by rfl) ⟨1238885, by rfl⟩ : syracuseStep 1651847 = 2477771) B2477771
theorem B5026951 : Blo 1651525 5026951 := bstep (se 1 (by rfl) ⟨3770213, by rfl⟩ : syracuseStep 5026951 = 7540427) B7540427
theorem B1651855 : Blo 1651525 1651855 := bstep (se 1 (by rfl) ⟨1238891, by rfl⟩ : syracuseStep 1651855 = 2477783) B2477783
theorem B2479247 : Blo 1651525 2479247 := bstep (se 1 (by rfl) ⟨1859435, by rfl⟩ : syracuseStep 2479247 = 3718871) B3718871
theorem B3716243 : Blo 1651525 3716243 := bstep (se 1 (by rfl) ⟨2787182, by rfl⟩ : syracuseStep 3716243 = 5574365) B5574365
theorem B2479289 : Blo 1651525 2479289 := bstep (se 2 (by rfl) ⟨929733, by rfl⟩ : syracuseStep 2479289 = 1859467) B1859467
theorem B1651899 : Blo 1651525 1651899 := bstep (se 1 (by rfl) ⟨1238924, by rfl⟩ : syracuseStep 1651899 = 2477849) B2477849
theorem B3716297 : Blo 1651525 3716297 := bstep (se 2 (by rfl) ⟨1393611, by rfl⟩ : syracuseStep 3716297 = 2787223) B2787223
theorem B1651975 : Blo 1651525 1651975 := bstep (se 1 (by rfl) ⟨1238981, by rfl⟩ : syracuseStep 1651975 = 2477963) B2477963
theorem B2479367 : Blo 1651525 2479367 := bstep (se 1 (by rfl) ⟨1859525, by rfl⟩ : syracuseStep 2479367 = 3719051) B3719051
theorem B1651983 : Blo 1651525 1651983 := bstep (se 1 (by rfl) ⟨1238987, by rfl⟩ : syracuseStep 1651983 = 2477975) B2477975
theorem B2479403 : Blo 1651525 2479403 := bstep (se 1 (by rfl) ⟨1859552, by rfl⟩ : syracuseStep 2479403 = 3719105) B3719105
theorem B1652027 : Blo 1651525 1652027 := bstep (se 1 (by rfl) ⟨1239020, by rfl⟩ : syracuseStep 1652027 = 2478041) B2478041
theorem B2479433 : Blo 1651525 2479433 := bstep (se 2 (by rfl) ⟨929787, by rfl⟩ : syracuseStep 2479433 = 1859575) B1859575
theorem B8361305 : Blo 1651525 8361305 := bstep (se 2 (by rfl) ⟨3135489, by rfl⟩ : syracuseStep 8361305 = 6270979) B6270979
theorem B1652103 : Blo 1651525 1652103 := bstep (se 1 (by rfl) ⟨1239077, by rfl⟩ : syracuseStep 1652103 = 2478155) B2478155
theorem B1652111 : Blo 1651525 1652111 := bstep (se 1 (by rfl) ⟨1239083, by rfl⟩ : syracuseStep 1652111 = 2478167) B2478167
theorem B1652155 : Blo 1651525 1652155 := bstep (se 1 (by rfl) ⟨1239116, by rfl⟩ : syracuseStep 1652155 = 2478233) B2478233
theorem B2479547 : Blo 1651525 2479547 := bstep (se 1 (by rfl) ⟨1859660, by rfl⟩ : syracuseStep 2479547 = 3719321) B3719321
theorem B2479607 : Blo 1651525 2479607 := bstep (se 1 (by rfl) ⟨1859705, by rfl⟩ : syracuseStep 2479607 = 3719411) B3719411
theorem B1652231 : Blo 1651525 1652231 := bstep (se 1 (by rfl) ⟨1239173, by rfl⟩ : syracuseStep 1652231 = 2478347) B2478347
theorem B1652239 : Blo 1651525 1652239 := bstep (se 1 (by rfl) ⟨1239179, by rfl⟩ : syracuseStep 1652239 = 2478359) B2478359
theorem B2479631 : Blo 1651525 2479631 := bstep (se 1 (by rfl) ⟨1859723, by rfl⟩ : syracuseStep 2479631 = 3719447) B3719447
theorem B2479673 : Blo 1651525 2479673 := bstep (se 2 (by rfl) ⟨929877, by rfl⟩ : syracuseStep 2479673 = 1859755) B1859755
theorem B1652283 : Blo 1651525 1652283 := bstep (se 1 (by rfl) ⟨1239212, by rfl⟩ : syracuseStep 1652283 = 2478425) B2478425
theorem B1652359 : Blo 1651525 1652359 := bstep (se 1 (by rfl) ⟨1239269, by rfl⟩ : syracuseStep 1652359 = 2478539) B2478539
theorem B2479751 : Blo 1651525 2479751 := bstep (se 1 (by rfl) ⟨1859813, by rfl⟩ : syracuseStep 2479751 = 3719627) B3719627
theorem B1652367 : Blo 1651525 1652367 := bstep (se 1 (by rfl) ⟨1239275, by rfl⟩ : syracuseStep 1652367 = 2478551) B2478551
theorem B2479787 : Blo 1651525 2479787 := bstep (se 1 (by rfl) ⟨1859840, by rfl⟩ : syracuseStep 2479787 = 3719681) B3719681
theorem B1652411 : Blo 1651525 1652411 := bstep (se 1 (by rfl) ⟨1239308, by rfl⟩ : syracuseStep 1652411 = 2478617) B2478617
theorem B2479817 : Blo 1651525 2479817 := bstep (se 2 (by rfl) ⟨929931, by rfl⟩ : syracuseStep 2479817 = 1859863) B1859863
theorem B1652487 : Blo 1651525 1652487 := bstep (se 1 (by rfl) ⟨1239365, by rfl⟩ : syracuseStep 1652487 = 2478731) B2478731
theorem B1652495 : Blo 1651525 1652495 := bstep (se 1 (by rfl) ⟨1239371, by rfl⟩ : syracuseStep 1652495 = 2478743) B2478743
theorem B5953339 : Blo 1651525 5953339 := bstep (se 1 (by rfl) ⟨4465004, by rfl⟩ : syracuseStep 5953339 = 8930009) B8930009
theorem B1652539 : Blo 1651525 1652539 := bstep (se 1 (by rfl) ⟨1239404, by rfl⟩ : syracuseStep 1652539 = 2478809) B2478809
theorem B2479931 : Blo 1651525 2479931 := bstep (se 1 (by rfl) ⟨1859948, by rfl⟩ : syracuseStep 2479931 = 3719897) B3719897
theorem B40187765 : Blo 1651525 40187765 := bstep (se 5 (by rfl) ⟨1883801, by rfl⟩ : syracuseStep 40187765 = 3767603) B3767603
theorem B2479991 : Blo 1651525 2479991 := bstep (se 1 (by rfl) ⟨1859993, by rfl⟩ : syracuseStep 2479991 = 3719987) B3719987
theorem B3716999 : Blo 1651525 3716999 := bstep (se 1 (by rfl) ⟨2787749, by rfl⟩ : syracuseStep 3716999 = 5575499) B5575499
theorem B1652615 : Blo 1651525 1652615 := bstep (se 1 (by rfl) ⟨1239461, by rfl⟩ : syracuseStep 1652615 = 2478923) B2478923
theorem B1652623 : Blo 1651525 1652623 := bstep (se 1 (by rfl) ⟨1239467, by rfl⟩ : syracuseStep 1652623 = 2478935) B2478935
theorem B2480015 : Blo 1651525 2480015 := bstep (se 1 (by rfl) ⟨1860011, by rfl⟩ : syracuseStep 2480015 = 3720023) B3720023
theorem B5576633 : Blo 1651525 5576633 := bstep (se 2 (by rfl) ⟨2091237, by rfl⟩ : syracuseStep 5576633 = 4182475) B4182475
theorem B2480057 : Blo 1651525 2480057 := bstep (se 2 (by rfl) ⟨930021, by rfl⟩ : syracuseStep 2480057 = 1860043) B1860043
theorem B1652667 : Blo 1651525 1652667 := bstep (se 1 (by rfl) ⟨1239500, by rfl⟩ : syracuseStep 1652667 = 2479001) B2479001
theorem B9410525 : Blo 1651525 9410525 := bstep (se 3 (by rfl) ⟨1764473, by rfl⟩ : syracuseStep 9410525 = 3528947) B3528947
theorem B1652743 : Blo 1651525 1652743 := bstep (se 1 (by rfl) ⟨1239557, by rfl⟩ : syracuseStep 1652743 = 2479115) B2479115
theorem B2480135 : Blo 1651525 2480135 := bstep (se 1 (by rfl) ⟨1860101, by rfl⟩ : syracuseStep 2480135 = 3720203) B3720203
theorem B4184075 : Blo 1651525 4184075 := bstep (se 1 (by rfl) ⟨3138056, by rfl⟩ : syracuseStep 4184075 = 6276113) B6276113
theorem B1652751 : Blo 1651525 1652751 := bstep (se 1 (by rfl) ⟨1239563, by rfl⟩ : syracuseStep 1652751 = 2479127) B2479127
theorem B20379671 : Blo 1651525 20379671 := bstep (se 1 (by rfl) ⟨15284753, by rfl⟩ : syracuseStep 20379671 = 30569507) B30569507
theorem B2480171 : Blo 1651525 2480171 := bstep (se 1 (by rfl) ⟨1860128, by rfl⟩ : syracuseStep 2480171 = 3720257) B3720257
theorem B3717179 : Blo 1651525 3717179 := bstep (se 1 (by rfl) ⟨2787884, by rfl⟩ : syracuseStep 3717179 = 5575769) B5575769
theorem B1652795 : Blo 1651525 1652795 := bstep (se 1 (by rfl) ⟨1239596, by rfl⟩ : syracuseStep 1652795 = 2479193) B2479193
theorem B2480201 : Blo 1651525 2480201 := bstep (se 2 (by rfl) ⟨930075, by rfl⟩ : syracuseStep 2480201 = 1860151) B1860151
theorem B1652871 : Blo 1651525 1652871 := bstep (se 1 (by rfl) ⟨1239653, by rfl⟩ : syracuseStep 1652871 = 2479307) B2479307
theorem B1652879 : Blo 1651525 1652879 := bstep (se 1 (by rfl) ⟨1239659, by rfl⟩ : syracuseStep 1652879 = 2479319) B2479319
theorem B4241555 : Blo 1651525 4241555 := bstep (se 1 (by rfl) ⟨3181166, by rfl⟩ : syracuseStep 4241555 = 6362333) B6362333
theorem B3717305 : Blo 1651525 3717305 := bstep (se 2 (by rfl) ⟨1393989, by rfl⟩ : syracuseStep 3717305 = 2787979) B2787979
theorem B1652923 : Blo 1651525 1652923 := bstep (se 1 (by rfl) ⟨1239692, by rfl⟩ : syracuseStep 1652923 = 2479385) B2479385
theorem B8370377 : Blo 1651525 8370377 := bstep (se 2 (by rfl) ⟨3138891, by rfl⟩ : syracuseStep 8370377 = 6277783) B6277783
theorem B1652999 : Blo 1651525 1652999 := bstep (se 1 (by rfl) ⟨1239749, by rfl⟩ : syracuseStep 1652999 = 2479499) B2479499
theorem B1653007 : Blo 1651525 1653007 := bstep (se 1 (by rfl) ⟨1239755, by rfl⟩ : syracuseStep 1653007 = 2479511) B2479511
theorem B7936289 : Blo 1651525 7936289 := bstep (se 2 (by rfl) ⟨2976108, by rfl⟩ : syracuseStep 7936289 = 5952217) B5952217
theorem B1653051 : Blo 1651525 1653051 := bstep (se 1 (by rfl) ⟨1239788, by rfl⟩ : syracuseStep 1653051 = 2479577) B2479577
theorem B2545993 : Blo 1651525 2545993 := bstep (se 2 (by rfl) ⟨954747, by rfl⟩ : syracuseStep 2545993 = 1909495) B1909495
theorem B6273395 : Blo 1651525 6273395 := bstep (se 1 (by rfl) ⟨4705046, by rfl⟩ : syracuseStep 6273395 = 9410093) B9410093
theorem B1653127 : Blo 1651525 1653127 := bstep (se 1 (by rfl) ⟨1239845, by rfl⟩ : syracuseStep 1653127 = 2479691) B2479691
theorem B1653135 : Blo 1651525 1653135 := bstep (se 1 (by rfl) ⟨1239851, by rfl⟩ : syracuseStep 1653135 = 2479703) B2479703
theorem B1653179 : Blo 1651525 1653179 := bstep (se 1 (by rfl) ⟨1239884, by rfl⟩ : syracuseStep 1653179 = 2479769) B2479769
theorem B9411025 : Blo 1651525 9411025 := bstep (se 2 (by rfl) ⟨3529134, by rfl⟩ : syracuseStep 9411025 = 7058269) B7058269
theorem B3971585 : Blo 1651525 3971585 := bstep (se 2 (by rfl) ⟨1489344, by rfl⟩ : syracuseStep 3971585 = 2978689) B2978689
theorem B1653255 : Blo 1651525 1653255 := bstep (se 1 (by rfl) ⟨1239941, by rfl⟩ : syracuseStep 1653255 = 2479883) B2479883
theorem B5577227 : Blo 1651525 5577227 := bstep (se 1 (by rfl) ⟨4182920, by rfl⟩ : syracuseStep 5577227 = 8365841) B8365841
theorem B1858063 : Blo 1651525 1858063 := bstep (se 1 (by rfl) ⟨1393547, by rfl⟩ : syracuseStep 1858063 = 2787095) B2787095
theorem B3717647 : Blo 1651525 3717647 := bstep (se 1 (by rfl) ⟨2788235, by rfl⟩ : syracuseStep 3717647 = 5576471) B5576471
theorem B1653263 : Blo 1651525 1653263 := bstep (se 1 (by rfl) ⟨1239947, by rfl⟩ : syracuseStep 1653263 = 2479895) B2479895
theorem B3717665 : Blo 1651525 3717665 := bstep (se 2 (by rfl) ⟨1394124, by rfl⟩ : syracuseStep 3717665 = 2788249) B2788249
theorem B7936555 : Blo 1651525 7936555 := bstep (se 1 (by rfl) ⟨5952416, by rfl⟩ : syracuseStep 7936555 = 11904833) B11904833
theorem B1653307 : Blo 1651525 1653307 := bstep (se 1 (by rfl) ⟨1239980, by rfl⟩ : syracuseStep 1653307 = 2479961) B2479961
theorem B5577335 : Blo 1651525 5577335 := bstep (se 1 (by rfl) ⟨4183001, by rfl⟩ : syracuseStep 5577335 = 8366003) B8366003
theorem B1653383 : Blo 1651525 1653383 := bstep (se 1 (by rfl) ⟨1240037, by rfl⟩ : syracuseStep 1653383 = 2480075) B2480075
theorem B1653391 : Blo 1651525 1653391 := bstep (se 1 (by rfl) ⟨1240043, by rfl⟩ : syracuseStep 1653391 = 2480087) B2480087
theorem B4184723 : Blo 1651525 4184723 := bstep (se 1 (by rfl) ⟨3138542, by rfl⟩ : syracuseStep 4184723 = 6277085) B6277085
theorem B1653435 : Blo 1651525 1653435 := bstep (se 1 (by rfl) ⟨1240076, by rfl⟩ : syracuseStep 1653435 = 2480153) B2480153
theorem B14121701 : Blo 1651525 14121701 := bstep (se 4 (by rfl) ⟨1323909, by rfl⟩ : syracuseStep 14121701 = 2647819) B2647819
theorem B1653511 : Blo 1651525 1653511 := bstep (se 1 (by rfl) ⟨1240133, by rfl⟩ : syracuseStep 1653511 = 2480267) B2480267
theorem B1653519 : Blo 1651525 1653519 := bstep (se 1 (by rfl) ⟨1240139, by rfl⟩ : syracuseStep 1653519 = 2480279) B2480279
theorem B7256891 : Blo 1651525 7256891 := bstep (se 1 (by rfl) ⟨5442668, by rfl⟩ : syracuseStep 7256891 = 10885337) B10885337
theorem B3718007 : Blo 1651525 3718007 := bstep (se 1 (by rfl) ⟨2788505, by rfl⟩ : syracuseStep 3718007 = 5577011) B5577011
theorem B2120591 : Blo 1651525 2120591 := bstep (se 1 (by rfl) ⟨1590443, by rfl⟩ : syracuseStep 2120591 = 3180887) B3180887
theorem B4185017 : Blo 1651525 4185017 := bstep (se 2 (by rfl) ⟨1569381, by rfl⟩ : syracuseStep 4185017 = 3138763) B3138763
theorem B1858567 : Blo 1651525 1858567 := bstep (se 1 (by rfl) ⟨1393925, by rfl⟩ : syracuseStep 1858567 = 2787851) B2787851
theorem B3718187 : Blo 1651525 3718187 := bstep (se 1 (by rfl) ⟨2788640, by rfl⟩ : syracuseStep 3718187 = 5577281) B5577281
theorem B18824237 : Blo 1651525 18824237 := bstep (se 3 (by rfl) ⟨3529544, by rfl⟩ : syracuseStep 18824237 = 7059089) B7059089
theorem B2513963 : Blo 1651525 2513963 := bstep (se 1 (by rfl) ⟨1885472, by rfl⟩ : syracuseStep 2513963 = 3770945) B3770945
theorem B7945303 : Blo 1651525 7945303 := bstep (se 1 (by rfl) ⟨5958977, by rfl⟩ : syracuseStep 7945303 = 11917955) B11917955
theorem B2514091 : Blo 1651525 2514091 := bstep (se 1 (by rfl) ⟨1885568, by rfl⟩ : syracuseStep 2514091 = 3771137) B3771137
theorem B1858747 : Blo 1651525 1858747 := bstep (se 1 (by rfl) ⟨1394060, by rfl⟩ : syracuseStep 1858747 = 2788121) B2788121
theorem B5577929 : Blo 1651525 5577929 := bstep (se 2 (by rfl) ⟨2091723, by rfl⟩ : syracuseStep 5577929 = 4183447) B4183447
theorem B8363411 : Blo 1651525 8363411 := bstep (se 1 (by rfl) ⟨6272558, by rfl⟩ : syracuseStep 8363411 = 12545117) B12545117
theorem B3718547 : Blo 1651525 3718547 := bstep (se 1 (by rfl) ⟨2788910, by rfl⟩ : syracuseStep 3718547 = 5577821) B5577821
theorem B3718601 : Blo 1651525 3718601 := bstep (se 2 (by rfl) ⟨1394475, by rfl⟩ : syracuseStep 3718601 = 2788951) B2788951
theorem B7061003 : Blo 1651525 7061003 := bstep (se 1 (by rfl) ⟨5295752, by rfl⟩ : syracuseStep 7061003 = 10591505) B10591505
theorem B3137039 : Blo 1651525 3137039 := bstep (se 1 (by rfl) ⟨2352779, by rfl⟩ : syracuseStep 3137039 = 4705559) B4705559
theorem B9666071 : Blo 1651525 9666071 := bstep (se 1 (by rfl) ⟨7249553, by rfl⟩ : syracuseStep 9666071 = 14499107) B14499107
theorem B9674263 : Blo 1651525 9674263 := bstep (se 1 (by rfl) ⟨7255697, by rfl⟩ : syracuseStep 9674263 = 14511395) B14511395
theorem B1859215 : Blo 1651525 1859215 := bstep (se 1 (by rfl) ⟨1394411, by rfl⟩ : syracuseStep 1859215 = 2788823) B2788823
theorem B12549977 : Blo 1651525 12549977 := bstep (se 2 (by rfl) ⟨4706241, by rfl⟩ : syracuseStep 12549977 = 9412483) B9412483
theorem B5578631 : Blo 1651525 5578631 := bstep (se 1 (by rfl) ⟨4183973, by rfl⟩ : syracuseStep 5578631 = 8367947) B8367947
theorem B7937939 : Blo 1651525 7937939 := bstep (se 1 (by rfl) ⟨5953454, by rfl⟩ : syracuseStep 7937939 = 11906909) B11906909
theorem B3137555 : Blo 1651525 3137555 := bstep (se 1 (by rfl) ⟨2353166, by rfl⟩ : syracuseStep 3137555 = 4706333) B4706333
theorem B28229795 : Blo 1651525 28229795 := bstep (se 1 (by rfl) ⟨21172346, by rfl⟩ : syracuseStep 28229795 = 42344693) B42344693
theorem B3137707 : Blo 1651525 3137707 := bstep (se 1 (by rfl) ⟨2353280, by rfl⟩ : syracuseStep 3137707 = 4706561) B4706561
theorem B3719339 : Blo 1651525 3719339 := bstep (se 1 (by rfl) ⟨2789504, by rfl⟩ : syracuseStep 3719339 = 5579009) B5579009
theorem B6275339 : Blo 1651525 6275339 := bstep (se 1 (by rfl) ⟨4706504, by rfl⟩ : syracuseStep 6275339 = 9413009) B9413009
theorem B1859935 : Blo 1651525 1859935 := bstep (se 1 (by rfl) ⟨1394951, by rfl⟩ : syracuseStep 1859935 = 2789903) B2789903
theorem B3137935 : Blo 1651525 3137935 := bstep (se 1 (by rfl) ⟨2353451, by rfl⟩ : syracuseStep 3137935 = 4706903) B4706903
theorem B3531151 : Blo 1651525 3531151 := bstep (se 1 (by rfl) ⟨2648363, by rfl⟩ : syracuseStep 3531151 = 5296727) B5296727
theorem B4465115 : Blo 1651525 4465115 := bstep (se 1 (by rfl) ⟨3348836, by rfl⟩ : syracuseStep 4465115 = 6697673) B6697673
theorem B3138011 : Blo 1651525 3138011 := bstep (se 1 (by rfl) ⟨2353508, by rfl⟩ : syracuseStep 3138011 = 4707017) B4707017
theorem B22921751 : Blo 1651525 22921751 := bstep (se 1 (by rfl) ⟨17191313, by rfl⟩ : syracuseStep 22921751 = 34382627) B34382627
theorem B23241239 : Blo 1651525 23241239 := bstep (se 1 (by rfl) ⟨17430929, by rfl⟩ : syracuseStep 23241239 = 34861859) B34861859
theorem B5579387 : Blo 1651525 5579387 := bstep (se 1 (by rfl) ⟨4184540, by rfl⟩ : syracuseStep 5579387 = 8369081) B8369081
theorem B53609111 : Blo 1651525 53609111 := bstep (se 1 (by rfl) ⟨40206833, by rfl⟩ : syracuseStep 53609111 = 80413667) B80413667
theorem B3719879 : Blo 1651525 3719879 := bstep (se 1 (by rfl) ⟨2789909, by rfl⟩ : syracuseStep 3719879 = 5579819) B5579819
theorem B5579549 : Blo 1651525 5579549 := bstep (se 3 (by rfl) ⟨1046165, by rfl⟩ : syracuseStep 5579549 = 2092331) B2092331
theorem B8938313 : Blo 1651525 8938313 := bstep (se 2 (by rfl) ⟨3351867, by rfl⟩ : syracuseStep 8938313 = 6703735) B6703735
theorem B15074353 : Blo 1651525 15074353 := bstep (se 2 (by rfl) ⟨5652882, by rfl⟩ : syracuseStep 15074353 = 11305765) B11305765
theorem B90489905 : Blo 1651525 90489905 := bstep (se 2 (by rfl) ⟨33933714, by rfl⟩ : syracuseStep 90489905 = 67867429) B67867429
theorem B17859635 : Blo 1651525 17859635 := bstep (se 1 (by rfl) ⟨13394726, by rfl⟩ : syracuseStep 17859635 = 26789453) B26789453
theorem B2827703 : Blo 1651525 2827703 := bstep (se 1 (by rfl) ⟨2120777, by rfl⟩ : syracuseStep 2827703 = 4241555) B4241555
theorem B10593737 : Blo 1651525 10593737 := bstep (se 2 (by rfl) ⟨3972651, by rfl⟩ : syracuseStep 10593737 = 7945303) B7945303
theorem B5580251 : Blo 1651525 5580251 := bstep (se 1 (by rfl) ⟨4185188, by rfl⟩ : syracuseStep 5580251 = 8370377) B8370377
theorem B6702601 : Blo 1651525 6702601 := bstep (se 2 (by rfl) ⟨2513475, by rfl⟩ : syracuseStep 6702601 = 5026951) B5026951
theorem B3352121 : Blo 1651525 3352121 := bstep (se 2 (by rfl) ⟨1257045, by rfl⟩ : syracuseStep 3352121 = 2514091) B2514091
theorem B2786987 : Blo 1651525 2786987 := bstep (se 1 (by rfl) ⟨2090240, by rfl⟩ : syracuseStep 2786987 = 4180481) B4180481
theorem B2647723 : Blo 1651525 2647723 := bstep (se 1 (by rfl) ⟨1985792, by rfl⟩ : syracuseStep 2647723 = 3971585) B3971585
theorem B6276797 : Blo 1651525 6276797 := bstep (se 3 (by rfl) ⟨1176899, by rfl⟩ : syracuseStep 6276797 = 2353799) B2353799
theorem B9406151 : Blo 1651525 9406151 := bstep (se 1 (by rfl) ⟨7054613, by rfl⟩ : syracuseStep 9406151 = 14109227) B14109227
theorem B9414467 : Blo 1651525 9414467 := bstep (se 1 (by rfl) ⟨7060850, by rfl⟩ : syracuseStep 9414467 = 14121701) B14121701
theorem B1984351 : Blo 1651525 1984351 := bstep (se 1 (by rfl) ⟨1488263, by rfl⟩ : syracuseStep 1984351 = 2976527) B2976527
theorem B2787385 : Blo 1651525 2787385 := bstep (se 2 (by rfl) ⟨1045269, by rfl⟩ : syracuseStep 2787385 = 2090539) B2090539
theorem B2787527 : Blo 1651525 2787527 := bstep (se 1 (by rfl) ⟨2090645, by rfl⟩ : syracuseStep 2787527 = 4181291) B4181291
theorem B45246701 : Blo 1651525 45246701 := bstep (se 3 (by rfl) ⟨8483756, by rfl⟩ : syracuseStep 45246701 = 16967513) B16967513
theorem B2091359 : Blo 1651525 2091359 := bstep (se 1 (by rfl) ⟨1568519, by rfl⟩ : syracuseStep 2091359 = 3137039) B3137039
theorem B2787689 : Blo 1651525 2787689 := bstep (se 2 (by rfl) ⟨1045383, by rfl⟩ : syracuseStep 2787689 = 2090767) B2090767
theorem B5654909 : Blo 1651525 5654909 := bstep (se 3 (by rfl) ⟨1060295, by rfl⟩ : syracuseStep 5654909 = 2120591) B2120591
theorem B8366651 : Blo 1651525 8366651 := bstep (se 1 (by rfl) ⟨6274988, by rfl⟩ : syracuseStep 8366651 = 12549977) B12549977
theorem B2788087 : Blo 1651525 2788087 := bstep (se 1 (by rfl) ⟨2091065, by rfl⟩ : syracuseStep 2788087 = 4182131) B4182131
theorem B2788283 : Blo 1651525 2788283 := bstep (se 1 (by rfl) ⟨2091212, by rfl⟩ : syracuseStep 2788283 = 4182425) B4182425
theorem B31763441 : Blo 1651525 31763441 := bstep (se 2 (by rfl) ⟨11911290, by rfl⟩ : syracuseStep 31763441 = 23822581) B23822581
theorem B2788391 : Blo 1651525 2788391 := bstep (se 1 (by rfl) ⟨2091293, by rfl⟩ : syracuseStep 2788391 = 4182587) B4182587
theorem B3394657 : Blo 1651525 3394657 := bstep (se 2 (by rfl) ⟨1272996, by rfl⟩ : syracuseStep 3394657 = 2545993) B2545993
theorem B8367299 : Blo 1651525 8367299 := bstep (se 1 (by rfl) ⟨6275474, by rfl⟩ : syracuseStep 8367299 = 12550949) B12550949
theorem B23817509 : Blo 1651525 23817509 := bstep (se 4 (by rfl) ⟨2232891, by rfl⟩ : syracuseStep 23817509 = 4465783) B4465783
theorem B2788681 : Blo 1651525 2788681 := bstep (se 2 (by rfl) ⟨1045755, by rfl⟩ : syracuseStep 2788681 = 2091511) B2091511
theorem B2477417 : Blo 1651525 2477417 := bstep (se 2 (by rfl) ⟨929031, by rfl⟩ : syracuseStep 2477417 = 1858063) B1858063
theorem B2788715 : Blo 1651525 2788715 := bstep (se 1 (by rfl) ⟨2091536, by rfl⟩ : syracuseStep 2788715 = 4183073) B4183073
theorem B2477495 : Blo 1651525 2477495 := bstep (se 1 (by rfl) ⟨1858121, by rfl⟩ : syracuseStep 2477495 = 3716243) B3716243
theorem B2477531 : Blo 1651525 2477531 := bstep (se 1 (by rfl) ⟨1858148, by rfl⟩ : syracuseStep 2477531 = 3716297) B3716297
theorem B7941671 : Blo 1651525 7941671 := bstep (se 1 (by rfl) ⟨5956253, by rfl⟩ : syracuseStep 7941671 = 11912507) B11912507
theorem B5574203 : Blo 1651525 5574203 := bstep (se 1 (by rfl) ⟨4180652, by rfl⟩ : syracuseStep 5574203 = 8361305) B8361305
theorem B5025419 : Blo 1651525 5025419 := bstep (se 1 (by rfl) ⟨3769064, by rfl⟩ : syracuseStep 5025419 = 7538129) B7538129
theorem B2789113 : Blo 1651525 2789113 := bstep (se 2 (by rfl) ⟨1045917, by rfl⟩ : syracuseStep 2789113 = 2091835) B2091835
theorem B5574473 : Blo 1651525 5574473 := bstep (se 2 (by rfl) ⟨2090427, by rfl⟩ : syracuseStep 5574473 = 4180855) B4180855
theorem B7057313 : Blo 1651525 7057313 := bstep (se 2 (by rfl) ⟨2646492, by rfl⟩ : syracuseStep 7057313 = 5292985) B5292985
theorem B2477999 : Blo 1651525 2477999 := bstep (se 1 (by rfl) ⟨1858499, by rfl⟩ : syracuseStep 2477999 = 3716999) B3716999
theorem B2789383 : Blo 1651525 2789383 := bstep (se 1 (by rfl) ⟨2092037, by rfl⟩ : syracuseStep 2789383 = 4184075) B4184075
theorem B2232329 : Blo 1651525 2232329 := bstep (se 2 (by rfl) ⟨837123, by rfl⟩ : syracuseStep 2232329 = 1674247) B1674247
theorem B2478089 : Blo 1651525 2478089 := bstep (se 2 (by rfl) ⟨929283, by rfl⟩ : syracuseStep 2478089 = 1858567) B1858567
theorem B13586447 : Blo 1651525 13586447 := bstep (se 1 (by rfl) ⟨10189835, by rfl⟩ : syracuseStep 13586447 = 20379671) B20379671
theorem B2478119 : Blo 1651525 2478119 := bstep (se 1 (by rfl) ⟨1858589, by rfl⟩ : syracuseStep 2478119 = 3717179) B3717179
theorem B2478203 : Blo 1651525 2478203 := bstep (se 1 (by rfl) ⟨1858652, by rfl⟩ : syracuseStep 2478203 = 3717305) B3717305
theorem B4182263 : Blo 1651525 4182263 := bstep (se 1 (by rfl) ⟨3136697, by rfl⟩ : syracuseStep 4182263 = 6273395) B6273395
theorem B2478329 : Blo 1651525 2478329 := bstep (se 2 (by rfl) ⟨929373, by rfl⟩ : syracuseStep 2478329 = 1858747) B1858747
theorem B2478431 : Blo 1651525 2478431 := bstep (se 1 (by rfl) ⟨1858823, by rfl⟩ : syracuseStep 2478431 = 3717647) B3717647
theorem B2478443 : Blo 1651525 2478443 := bstep (se 1 (by rfl) ⟨1858832, by rfl⟩ : syracuseStep 2478443 = 3717665) B3717665
theorem B2789815 : Blo 1651525 2789815 := bstep (se 1 (by rfl) ⟨2092361, by rfl⟩ : syracuseStep 2789815 = 4184723) B4184723
theorem B6033865 : Blo 1651525 6033865 := bstep (se 2 (by rfl) ⟨2262699, by rfl⟩ : syracuseStep 6033865 = 4525399) B4525399
theorem B6271451 : Blo 1651525 6271451 := bstep (se 1 (by rfl) ⟨4703588, by rfl⟩ : syracuseStep 6271451 = 9407177) B9407177
theorem B4837927 : Blo 1651525 4837927 := bstep (se 1 (by rfl) ⟨3628445, by rfl⟩ : syracuseStep 4837927 = 7256891) B7256891
theorem B2478671 : Blo 1651525 2478671 := bstep (se 1 (by rfl) ⟨1859003, by rfl⟩ : syracuseStep 2478671 = 3718007) B3718007
theorem B2790011 : Blo 1651525 2790011 := bstep (se 1 (by rfl) ⟨2092508, by rfl⟩ : syracuseStep 2790011 = 4185017) B4185017
theorem B14316205 : Blo 1651525 14316205 := bstep (se 3 (by rfl) ⟨2684288, by rfl⟩ : syracuseStep 14316205 = 5368577) B5368577
theorem B2478791 : Blo 1651525 2478791 := bstep (se 1 (by rfl) ⟨1859093, by rfl⟩ : syracuseStep 2478791 = 3718187) B3718187
theorem B1675975 : Blo 1651525 1675975 := bstep (se 1 (by rfl) ⟨1256981, by rfl⟩ : syracuseStep 1675975 = 2513963) B2513963
theorem B12899017 : Blo 1651525 12899017 := bstep (se 2 (by rfl) ⟨4837131, by rfl⟩ : syracuseStep 12899017 = 9674263) B9674263
theorem B2978515 : Blo 1651525 2978515 := bstep (se 1 (by rfl) ⟨2233886, by rfl⟩ : syracuseStep 2978515 = 4467773) B4467773
theorem B50869043 : Blo 1651525 50869043 := bstep (se 1 (by rfl) ⟨38151782, by rfl⟩ : syracuseStep 50869043 = 76303565) B76303565
theorem B1651535 : Blo 1651525 1651535 := bstep (se 1 (by rfl) ⟨1238651, by rfl⟩ : syracuseStep 1651535 = 2477303) B2477303
theorem B1651551 : Blo 1651525 1651551 := bstep (se 1 (by rfl) ⟨1238663, by rfl⟩ : syracuseStep 1651551 = 2477327) B2477327
theorem B2478953 : Blo 1651525 2478953 := bstep (se 2 (by rfl) ⟨929607, by rfl⟩ : syracuseStep 2478953 = 1859215) B1859215
theorem B1651579 : Blo 1651525 1651579 := bstep (se 1 (by rfl) ⟨1238684, by rfl⟩ : syracuseStep 1651579 = 2477369) B2477369
theorem B1651631 : Blo 1651525 1651631 := bstep (se 1 (by rfl) ⟨1238723, by rfl⟩ : syracuseStep 1651631 = 2477447) B2477447
theorem B5575607 : Blo 1651525 5575607 := bstep (se 1 (by rfl) ⟨4181705, by rfl⟩ : syracuseStep 5575607 = 8363411) B8363411
theorem B2479031 : Blo 1651525 2479031 := bstep (se 1 (by rfl) ⟨1859273, by rfl⟩ : syracuseStep 2479031 = 3718547) B3718547
theorem B3716027 : Blo 1651525 3716027 := bstep (se 1 (by rfl) ⟨2787020, by rfl⟩ : syracuseStep 3716027 = 5574041) B5574041
theorem B1651655 : Blo 1651525 1651655 := bstep (se 1 (by rfl) ⟨1238741, by rfl⟩ : syracuseStep 1651655 = 2477483) B2477483
theorem B1651675 : Blo 1651525 1651675 := bstep (se 1 (by rfl) ⟨1238756, by rfl⟩ : syracuseStep 1651675 = 2477513) B2477513
theorem B2479067 : Blo 1651525 2479067 := bstep (se 1 (by rfl) ⟨1859300, by rfl⟩ : syracuseStep 2479067 = 3718601) B3718601
theorem B4707335 : Blo 1651525 4707335 := bstep (se 1 (by rfl) ⟨3530501, by rfl⟩ : syracuseStep 4707335 = 7061003) B7061003
theorem B6444047 : Blo 1651525 6444047 := bstep (se 1 (by rfl) ⟨4833035, by rfl⟩ : syracuseStep 6444047 = 9666071) B9666071
theorem B1651751 : Blo 1651525 1651751 := bstep (se 1 (by rfl) ⟨1238813, by rfl⟩ : syracuseStep 1651751 = 2477627) B2477627
theorem B13407281 : Blo 1651525 13407281 := bstep (se 2 (by rfl) ⟨5027730, by rfl⟩ : syracuseStep 13407281 = 10055461) B10055461
theorem B3716153 : Blo 1651525 3716153 := bstep (se 2 (by rfl) ⟨1393557, by rfl⟩ : syracuseStep 3716153 = 2787115) B2787115
theorem B1651791 : Blo 1651525 1651791 := bstep (se 1 (by rfl) ⟨1238843, by rfl⟩ : syracuseStep 1651791 = 2477687) B2477687
theorem B1651807 : Blo 1651525 1651807 := bstep (se 1 (by rfl) ⟨1238855, by rfl⟩ : syracuseStep 1651807 = 2477711) B2477711
theorem B1651835 : Blo 1651525 1651835 := bstep (se 1 (by rfl) ⟨1238876, by rfl⟩ : syracuseStep 1651835 = 2477753) B2477753
theorem B7943321 : Blo 1651525 7943321 := bstep (se 2 (by rfl) ⟨2978745, by rfl⟩ : syracuseStep 7943321 = 5957491) B5957491
theorem B6698141 : Blo 1651525 6698141 := bstep (se 3 (by rfl) ⟨1255901, by rfl⟩ : syracuseStep 6698141 = 2511803) B2511803
theorem B1651887 : Blo 1651525 1651887 := bstep (se 1 (by rfl) ⟨1238915, by rfl⟩ : syracuseStep 1651887 = 2477831) B2477831
theorem B1651911 : Blo 1651525 1651911 := bstep (se 1 (by rfl) ⟨1238933, by rfl⟩ : syracuseStep 1651911 = 2477867) B2477867
theorem B1651931 : Blo 1651525 1651931 := bstep (se 1 (by rfl) ⟨1238948, by rfl⟩ : syracuseStep 1651931 = 2477897) B2477897
theorem B1652007 : Blo 1651525 1652007 := bstep (se 1 (by rfl) ⟨1239005, by rfl⟩ : syracuseStep 1652007 = 2478011) B2478011
theorem B1652047 : Blo 1651525 1652047 := bstep (se 1 (by rfl) ⟨1239035, by rfl⟩ : syracuseStep 1652047 = 2478071) B2478071
theorem B1652063 : Blo 1651525 1652063 := bstep (se 1 (by rfl) ⟨1239047, by rfl⟩ : syracuseStep 1652063 = 2478095) B2478095
theorem B2512223 : Blo 1651525 2512223 := bstep (se 1 (by rfl) ⟨1884167, by rfl⟩ : syracuseStep 2512223 = 3768335) B3768335
theorem B3528041 : Blo 1651525 3528041 := bstep (se 2 (by rfl) ⟨1323015, by rfl⟩ : syracuseStep 3528041 = 2646031) B2646031
theorem B1652091 : Blo 1651525 1652091 := bstep (se 1 (by rfl) ⟨1239068, by rfl⟩ : syracuseStep 1652091 = 2478137) B2478137
theorem B3716495 : Blo 1651525 3716495 := bstep (se 1 (by rfl) ⟨2787371, by rfl⟩ : syracuseStep 3716495 = 5574743) B5574743
theorem B1652143 : Blo 1651525 1652143 := bstep (se 1 (by rfl) ⟨1239107, by rfl⟩ : syracuseStep 1652143 = 2478215) B2478215
theorem B2479535 : Blo 1651525 2479535 := bstep (se 1 (by rfl) ⟨1859651, by rfl⟩ : syracuseStep 2479535 = 3719303) B3719303
theorem B1652167 : Blo 1651525 1652167 := bstep (se 1 (by rfl) ⟨1239125, by rfl⟩ : syracuseStep 1652167 = 2478251) B2478251
theorem B1652187 : Blo 1651525 1652187 := bstep (se 1 (by rfl) ⟨1239140, by rfl⟩ : syracuseStep 1652187 = 2478281) B2478281
theorem B12547547 : Blo 1651525 12547547 := bstep (se 1 (by rfl) ⟨9410660, by rfl⟩ : syracuseStep 12547547 = 18821321) B18821321
theorem B35755505 : Blo 1651525 35755505 := bstep (se 2 (by rfl) ⟨13408314, by rfl⟩ : syracuseStep 35755505 = 26816629) B26816629
theorem B5576201 : Blo 1651525 5576201 := bstep (se 2 (by rfl) ⟨2091075, by rfl⟩ : syracuseStep 5576201 = 4182151) B4182151
theorem B2233865 : Blo 1651525 2233865 := bstep (se 2 (by rfl) ⟨837699, by rfl⟩ : syracuseStep 2233865 = 1675399) B1675399
theorem B2479625 : Blo 1651525 2479625 := bstep (se 2 (by rfl) ⟨929859, by rfl⟩ : syracuseStep 2479625 = 1859719) B1859719
theorem B1652263 : Blo 1651525 1652263 := bstep (se 1 (by rfl) ⟨1239197, by rfl⟩ : syracuseStep 1652263 = 2478395) B2478395
theorem B2479655 : Blo 1651525 2479655 := bstep (se 1 (by rfl) ⟨1859741, by rfl⟩ : syracuseStep 2479655 = 3719483) B3719483
theorem B1652303 : Blo 1651525 1652303 := bstep (se 1 (by rfl) ⟨1239227, by rfl⟩ : syracuseStep 1652303 = 2478455) B2478455
theorem B1652319 : Blo 1651525 1652319 := bstep (se 1 (by rfl) ⟨1239239, by rfl⟩ : syracuseStep 1652319 = 2478479) B2478479
theorem B1652347 : Blo 1651525 1652347 := bstep (se 1 (by rfl) ⟨1239260, by rfl⟩ : syracuseStep 1652347 = 2478521) B2478521
theorem B2479739 : Blo 1651525 2479739 := bstep (se 1 (by rfl) ⟨1859804, by rfl⟩ : syracuseStep 2479739 = 3719609) B3719609
theorem B9541259 : Blo 1651525 9541259 := bstep (se 1 (by rfl) ⟨7155944, by rfl⟩ : syracuseStep 9541259 = 14311889) B14311889
theorem B1652399 : Blo 1651525 1652399 := bstep (se 1 (by rfl) ⟨1239299, by rfl⟩ : syracuseStep 1652399 = 2478599) B2478599
theorem B6272711 : Blo 1651525 6272711 := bstep (se 1 (by rfl) ⟨4704533, by rfl⟩ : syracuseStep 6272711 = 9409067) B9409067
theorem B1652423 : Blo 1651525 1652423 := bstep (se 1 (by rfl) ⟨1239317, by rfl⟩ : syracuseStep 1652423 = 2478635) B2478635
theorem B4183751 : Blo 1651525 4183751 := bstep (se 1 (by rfl) ⟨3137813, by rfl⟩ : syracuseStep 4183751 = 6275627) B6275627
theorem B3716819 : Blo 1651525 3716819 := bstep (se 1 (by rfl) ⟨2787614, by rfl⟩ : syracuseStep 3716819 = 5575229) B5575229
theorem B1652443 : Blo 1651525 1652443 := bstep (se 1 (by rfl) ⟨1239332, by rfl⟩ : syracuseStep 1652443 = 2478665) B2478665
theorem B2479865 : Blo 1651525 2479865 := bstep (se 2 (by rfl) ⟨929949, by rfl⟩ : syracuseStep 2479865 = 1859899) B1859899
theorem B1652519 : Blo 1651525 1652519 := bstep (se 1 (by rfl) ⟨1239389, by rfl⟩ : syracuseStep 1652519 = 2478779) B2478779
theorem B1652559 : Blo 1651525 1652559 := bstep (se 1 (by rfl) ⟨1239419, by rfl⟩ : syracuseStep 1652559 = 2478839) B2478839
theorem B1652575 : Blo 1651525 1652575 := bstep (se 1 (by rfl) ⟨1239431, by rfl⟩ : syracuseStep 1652575 = 2478863) B2478863
theorem B10590047 : Blo 1651525 10590047 := bstep (se 1 (by rfl) ⟨7942535, by rfl⟩ : syracuseStep 10590047 = 15885071) B15885071
theorem B2479967 : Blo 1651525 2479967 := bstep (se 1 (by rfl) ⟨1859975, by rfl⟩ : syracuseStep 2479967 = 3719951) B3719951
theorem B2479979 : Blo 1651525 2479979 := bstep (se 1 (by rfl) ⟨1859984, by rfl⟩ : syracuseStep 2479979 = 3719969) B3719969
theorem B1652603 : Blo 1651525 1652603 := bstep (se 1 (by rfl) ⟨1239452, by rfl⟩ : syracuseStep 1652603 = 2478905) B2478905
theorem B3528623 : Blo 1651525 3528623 := bstep (se 1 (by rfl) ⟨2646467, by rfl⟩ : syracuseStep 3528623 = 5292935) B5292935
theorem B1652655 : Blo 1651525 1652655 := bstep (se 1 (by rfl) ⟨1239491, by rfl⟩ : syracuseStep 1652655 = 2478983) B2478983
theorem B12548033 : Blo 1651525 12548033 := bstep (se 2 (by rfl) ⟨4705512, by rfl⟩ : syracuseStep 12548033 = 9411025) B9411025
theorem B1652679 : Blo 1651525 1652679 := bstep (se 1 (by rfl) ⟨1239509, by rfl⟩ : syracuseStep 1652679 = 2479019) B2479019
theorem B1652699 : Blo 1651525 1652699 := bstep (se 1 (by rfl) ⟨1239524, by rfl⟩ : syracuseStep 1652699 = 2479049) B2479049
theorem B12556295 : Blo 1651525 12556295 := bstep (se 1 (by rfl) ⟨9417221, by rfl⟩ : syracuseStep 12556295 = 18834443) B18834443
theorem B1652775 : Blo 1651525 1652775 := bstep (se 1 (by rfl) ⟨1239581, by rfl⟩ : syracuseStep 1652775 = 2479163) B2479163
theorem B10582073 : Blo 1651525 10582073 := bstep (se 2 (by rfl) ⟨3968277, by rfl⟩ : syracuseStep 10582073 = 7936555) B7936555
theorem B3348559 : Blo 1651525 3348559 := bstep (se 1 (by rfl) ⟨2511419, by rfl⟩ : syracuseStep 3348559 = 5022839) B5022839
theorem B1652815 : Blo 1651525 1652815 := bstep (se 1 (by rfl) ⟨1239611, by rfl⟩ : syracuseStep 1652815 = 2479223) B2479223
theorem B2480207 : Blo 1651525 2480207 := bstep (se 1 (by rfl) ⟨1860155, by rfl⟩ : syracuseStep 2480207 = 3720311) B3720311
theorem B1652831 : Blo 1651525 1652831 := bstep (se 1 (by rfl) ⟨1239623, by rfl⟩ : syracuseStep 1652831 = 2479247) B2479247
theorem B3135611 : Blo 1651525 3135611 := bstep (se 1 (by rfl) ⟨2351708, by rfl⟩ : syracuseStep 3135611 = 4703417) B4703417
theorem B1652859 : Blo 1651525 1652859 := bstep (se 1 (by rfl) ⟨1239644, by rfl⟩ : syracuseStep 1652859 = 2479289) B2479289
theorem B1652911 : Blo 1651525 1652911 := bstep (se 1 (by rfl) ⟨1239683, by rfl⟩ : syracuseStep 1652911 = 2479367) B2479367
theorem B1652935 : Blo 1651525 1652935 := bstep (se 1 (by rfl) ⟨1239701, by rfl⟩ : syracuseStep 1652935 = 2479403) B2479403
theorem B1652955 : Blo 1651525 1652955 := bstep (se 1 (by rfl) ⟨1239716, by rfl⟩ : syracuseStep 1652955 = 2479433) B2479433
theorem B1653031 : Blo 1651525 1653031 := bstep (se 1 (by rfl) ⟨1239773, by rfl⟩ : syracuseStep 1653031 = 2479547) B2479547
theorem B7059773 : Blo 1651525 7059773 := bstep (se 3 (by rfl) ⟨1323707, by rfl⟩ : syracuseStep 7059773 = 2647415) B2647415
theorem B1653071 : Blo 1651525 1653071 := bstep (se 1 (by rfl) ⟨1239803, by rfl⟩ : syracuseStep 1653071 = 2479607) B2479607
theorem B1653087 : Blo 1651525 1653087 := bstep (se 1 (by rfl) ⟨1239815, by rfl⟩ : syracuseStep 1653087 = 2479631) B2479631
theorem B5577065 : Blo 1651525 5577065 := bstep (se 2 (by rfl) ⟨2091399, by rfl⟩ : syracuseStep 5577065 = 4182799) B4182799
theorem B17873257 : Blo 1651525 17873257 := bstep (se 2 (by rfl) ⟨6702471, by rfl⟩ : syracuseStep 17873257 = 13404943) B13404943
theorem B1653115 : Blo 1651525 1653115 := bstep (se 1 (by rfl) ⟨1239836, by rfl⟩ : syracuseStep 1653115 = 2479673) B2479673
theorem B6273409 : Blo 1651525 6273409 := bstep (se 2 (by rfl) ⟨2352528, by rfl⟩ : syracuseStep 6273409 = 4705057) B4705057
theorem B1653167 : Blo 1651525 1653167 := bstep (se 1 (by rfl) ⟨1239875, by rfl⟩ : syracuseStep 1653167 = 2479751) B2479751
theorem B1653191 : Blo 1651525 1653191 := bstep (se 1 (by rfl) ⟨1239893, by rfl⟩ : syracuseStep 1653191 = 2479787) B2479787
theorem B1653211 : Blo 1651525 1653211 := bstep (se 1 (by rfl) ⟨1239908, by rfl⟩ : syracuseStep 1653211 = 2479817) B2479817
theorem B1653287 : Blo 1651525 1653287 := bstep (se 1 (by rfl) ⟨1239965, by rfl⟩ : syracuseStep 1653287 = 2479931) B2479931
theorem B1653327 : Blo 1651525 1653327 := bstep (se 1 (by rfl) ⟨1239995, by rfl⟩ : syracuseStep 1653327 = 2479991) B2479991
theorem B1653343 : Blo 1651525 1653343 := bstep (se 1 (by rfl) ⟨1240007, by rfl⟩ : syracuseStep 1653343 = 2480015) B2480015
theorem B3136097 : Blo 1651525 3136097 := bstep (se 2 (by rfl) ⟨1176036, by rfl⟩ : syracuseStep 3136097 = 2352073) B2352073
theorem B1858171 : Blo 1651525 1858171 := bstep (se 1 (by rfl) ⟨1393628, by rfl⟩ : syracuseStep 1858171 = 2787257) B2787257
theorem B3717755 : Blo 1651525 3717755 := bstep (se 1 (by rfl) ⟨2788316, by rfl⟩ : syracuseStep 3717755 = 5576633) B5576633
theorem B1653371 : Blo 1651525 1653371 := bstep (se 1 (by rfl) ⟨1240028, by rfl⟩ : syracuseStep 1653371 = 2480057) B2480057
theorem B6273683 : Blo 1651525 6273683 := bstep (se 1 (by rfl) ⟨4705262, by rfl⟩ : syracuseStep 6273683 = 9410525) B9410525
theorem B1653423 : Blo 1651525 1653423 := bstep (se 1 (by rfl) ⟨1240067, by rfl⟩ : syracuseStep 1653423 = 2480135) B2480135
theorem B1653447 : Blo 1651525 1653447 := bstep (se 1 (by rfl) ⟨1240085, by rfl⟩ : syracuseStep 1653447 = 2480171) B2480171
theorem B1653467 : Blo 1651525 1653467 := bstep (se 1 (by rfl) ⟨1240100, by rfl⟩ : syracuseStep 1653467 = 2480201) B2480201
theorem B3136249 : Blo 1651525 3136249 := bstep (se 2 (by rfl) ⟨1176093, by rfl⟩ : syracuseStep 3136249 = 2352187) B2352187
theorem B3717881 : Blo 1651525 3717881 := bstep (se 2 (by rfl) ⟨1394205, by rfl⟩ : syracuseStep 3717881 = 2788411) B2788411
theorem B4184905 : Blo 1651525 4184905 := bstep (se 2 (by rfl) ⟨1569339, by rfl⟩ : syracuseStep 4184905 = 3138679) B3138679
theorem B5290859 : Blo 1651525 5290859 := bstep (se 1 (by rfl) ⟨3968144, by rfl⟩ : syracuseStep 5290859 = 7936289) B7936289
theorem B10738615 : Blo 1651525 10738615 := bstep (se 1 (by rfl) ⟨8053961, by rfl⟩ : syracuseStep 10738615 = 16107923) B16107923
theorem B5577659 : Blo 1651525 5577659 := bstep (se 1 (by rfl) ⟨4183244, by rfl⟩ : syracuseStep 5577659 = 8366489) B8366489
theorem B3718151 : Blo 1651525 3718151 := bstep (se 1 (by rfl) ⟨2788613, by rfl⟩ : syracuseStep 3718151 = 5577227) B5577227
theorem B8363087 : Blo 1651525 8363087 := bstep (se 1 (by rfl) ⟨6272315, by rfl⟩ : syracuseStep 8363087 = 12544631) B12544631
theorem B1858639 : Blo 1651525 1858639 := bstep (se 1 (by rfl) ⟨1393979, by rfl⟩ : syracuseStep 1858639 = 2787959) B2787959
theorem B3718223 : Blo 1651525 3718223 := bstep (se 1 (by rfl) ⟨2788667, by rfl⟩ : syracuseStep 3718223 = 5577335) B5577335
theorem B2513999 : Blo 1651525 2513999 := bstep (se 1 (by rfl) ⟨1885499, by rfl⟩ : syracuseStep 2513999 = 3770999) B3770999
theorem B12549491 : Blo 1651525 12549491 := bstep (se 1 (by rfl) ⟨9412118, by rfl⟩ : syracuseStep 12549491 = 18824237) B18824237
theorem B24141199 : Blo 1651525 24141199 := bstep (se 1 (by rfl) ⟨18105899, by rfl⟩ : syracuseStep 24141199 = 36211799) B36211799
theorem B9411983 : Blo 1651525 9411983 := bstep (se 1 (by rfl) ⟨7058987, by rfl⟩ : syracuseStep 9411983 = 14117975) B14117975
theorem B1859035 : Blo 1651525 1859035 := bstep (se 1 (by rfl) ⟨1394276, by rfl⟩ : syracuseStep 1859035 = 2788553) B2788553
theorem B3718619 : Blo 1651525 3718619 := bstep (se 1 (by rfl) ⟨2788964, by rfl⟩ : syracuseStep 3718619 = 5577929) B5577929
theorem B107167373 : Blo 1651525 107167373 := bstep (se 3 (by rfl) ⟨20093882, by rfl⟩ : syracuseStep 107167373 = 40187765) B40187765
theorem B8363735 : Blo 1651525 8363735 := bstep (se 1 (by rfl) ⟨6272801, by rfl⟩ : syracuseStep 8363735 = 12545603) B12545603
theorem B21167837 : Blo 1651525 21167837 := bstep (se 3 (by rfl) ⟨3968969, by rfl⟩ : syracuseStep 21167837 = 7937939) B7937939
theorem B7937785 : Blo 1651525 7937785 := bstep (se 2 (by rfl) ⟨2976669, by rfl⟩ : syracuseStep 7937785 = 5953339) B5953339
theorem B2645903 : Blo 1651525 2645903 := bstep (se 1 (by rfl) ⟨1984427, by rfl⟩ : syracuseStep 2645903 = 3968855) B3968855
theorem B1859503 : Blo 1651525 1859503 := bstep (se 1 (by rfl) ⟨1394627, by rfl⟩ : syracuseStep 1859503 = 2789255) B2789255
theorem B3719087 : Blo 1651525 3719087 := bstep (se 1 (by rfl) ⟨2789315, by rfl⟩ : syracuseStep 3719087 = 5578631) B5578631
theorem B11911121 : Blo 1651525 11911121 := bstep (se 2 (by rfl) ⟨4466670, by rfl⟩ : syracuseStep 11911121 = 8933341) B8933341
theorem B3719177 : Blo 1651525 3719177 := bstep (se 2 (by rfl) ⟨1394691, by rfl⟩ : syracuseStep 3719177 = 2789383) B2789383
theorem B80396549 : Blo 1651525 80396549 := bstep (se 4 (by rfl) ⟨7537176, by rfl⟩ : syracuseStep 80396549 = 15074353) B15074353
theorem B17858981 : Blo 1651525 17858981 := bstep (se 4 (by rfl) ⟨1674279, by rfl⟩ : syracuseStep 17858981 = 3348559) B3348559
theorem B3719591 : Blo 1651525 3719591 := bstep (se 1 (by rfl) ⟨2789693, by rfl⟩ : syracuseStep 3719591 = 5579387) B5579387
theorem B1860007 : Blo 1651525 1860007 := bstep (se 1 (by rfl) ⟨1395005, by rfl⟩ : syracuseStep 1860007 = 2790011) B2790011
theorem B23831009 : Blo 1651525 23831009 := bstep (se 2 (by rfl) ⟨8936628, by rfl⟩ : syracuseStep 23831009 = 17873257) B17873257
theorem B8364545 : Blo 1651525 8364545 := bstep (se 2 (by rfl) ⟨3136704, by rfl⟩ : syracuseStep 8364545 = 6273409) B6273409
theorem B3719699 : Blo 1651525 3719699 := bstep (se 1 (by rfl) ⟨2789774, by rfl⟩ : syracuseStep 3719699 = 5579549) B5579549
theorem B3719753 : Blo 1651525 3719753 := bstep (se 2 (by rfl) ⟨1394907, by rfl⟩ : syracuseStep 3719753 = 2789815) B2789815
theorem B8045153 : Blo 1651525 8045153 := bstep (se 2 (by rfl) ⟨3016932, by rfl⟩ : syracuseStep 8045153 = 6033865) B6033865
theorem B60326603 : Blo 1651525 60326603 := bstep (se 1 (by rfl) ⟨45244952, by rfl⟩ : syracuseStep 60326603 = 90489905) B90489905
theorem B8938187 : Blo 1651525 8938187 := bstep (se 1 (by rfl) ⟨6703640, by rfl⟩ : syracuseStep 8938187 = 13407281) B13407281
theorem B4465427 : Blo 1651525 4465427 := bstep (se 1 (by rfl) ⟨3349070, by rfl⟩ : syracuseStep 4465427 = 6698141) B6698141
theorem B19088273 : Blo 1651525 19088273 := bstep (se 2 (by rfl) ⟨7158102, by rfl⟩ : syracuseStep 19088273 = 14316205) B14316205
theorem B1885135 : Blo 1651525 1885135 := bstep (se 1 (by rfl) ⟨1413851, by rfl⟩ : syracuseStep 1885135 = 2827703) B2827703
theorem B7062491 : Blo 1651525 7062491 := bstep (se 1 (by rfl) ⟨5296868, by rfl⟩ : syracuseStep 7062491 = 10593737) B10593737
theorem B8365031 : Blo 1651525 8365031 := bstep (se 1 (by rfl) ⟨6273773, by rfl⟩ : syracuseStep 8365031 = 12547547) B12547547
theorem B3720167 : Blo 1651525 3720167 := bstep (se 1 (by rfl) ⟨2790125, by rfl⟩ : syracuseStep 3720167 = 5580251) B5580251
theorem B5579873 : Blo 1651525 5579873 := bstep (se 2 (by rfl) ⟨2092452, by rfl⟩ : syracuseStep 5579873 = 4184905) B4184905
theorem B6276311 : Blo 1651525 6276311 := bstep (se 1 (by rfl) ⟨4707233, by rfl⟩ : syracuseStep 6276311 = 9414467) B9414467
theorem B2352415 : Blo 1651525 2352415 := bstep (se 1 (by rfl) ⟨1764311, by rfl⟩ : syracuseStep 2352415 = 3528623) B3528623
theorem B8365355 : Blo 1651525 8365355 := bstep (se 1 (by rfl) ⟨6274016, by rfl⟩ : syracuseStep 8365355 = 12548033) B12548033
theorem B5956973 : Blo 1651525 5956973 := bstep (se 3 (by rfl) ⟨1116932, by rfl⟩ : syracuseStep 5956973 = 2233865) B2233865
theorem B7054715 : Blo 1651525 7054715 := bstep (se 1 (by rfl) ⟨5291036, by rfl⟩ : syracuseStep 7054715 = 10582073) B10582073
theorem B3769939 : Blo 1651525 3769939 := bstep (se 1 (by rfl) ⟨2827454, by rfl⟩ : syracuseStep 3769939 = 5654909) B5654909
theorem B32188265 : Blo 1651525 32188265 := bstep (se 2 (by rfl) ⟨12070599, by rfl⟩ : syracuseStep 32188265 = 24141199) B24141199
theorem B15878339 : Blo 1651525 15878339 := bstep (se 1 (by rfl) ⟨11908754, by rfl⟩ : syracuseStep 15878339 = 23817509) B23817509
theorem B8366327 : Blo 1651525 8366327 := bstep (se 1 (by rfl) ⟨6274745, by rfl⟩ : syracuseStep 8366327 = 12549491) B12549491
theorem B5294447 : Blo 1651525 5294447 := bstep (se 1 (by rfl) ⟨3970835, by rfl⟩ : syracuseStep 5294447 = 7941671) B7941671
theorem B7055741 : Blo 1651525 7055741 := bstep (se 3 (by rfl) ⟨1322951, by rfl⟩ : syracuseStep 7055741 = 2645903) B2645903
theorem B71444915 : Blo 1651525 71444915 := bstep (se 1 (by rfl) ⟨53583686, by rfl⟩ : syracuseStep 71444915 = 107167373) B107167373
theorem B4704875 : Blo 1651525 4704875 := bstep (se 1 (by rfl) ⟨3528656, by rfl⟩ : syracuseStep 4704875 = 7057313) B7057313
theorem B7940747 : Blo 1651525 7940747 := bstep (se 1 (by rfl) ⟨5955560, by rfl⟩ : syracuseStep 7940747 = 11911121) B11911121
theorem B12552893 : Blo 1651525 12552893 := bstep (se 3 (by rfl) ⟨2353667, by rfl⟩ : syracuseStep 12552893 = 4707335) B4707335
theorem B8366813 : Blo 1651525 8366813 := bstep (se 3 (by rfl) ⟨1568777, by rfl⟩ : syracuseStep 8366813 = 3137555) B3137555
theorem B18819863 : Blo 1651525 18819863 := bstep (se 1 (by rfl) ⟨14114897, by rfl⟩ : syracuseStep 18819863 = 28229795) B28229795
theorem B2788175 : Blo 1651525 2788175 := bstep (se 1 (by rfl) ⟨2091131, by rfl⟩ : syracuseStep 2788175 = 4182263) B4182263
theorem B4180967 : Blo 1651525 4180967 := bstep (se 1 (by rfl) ⟨3135725, by rfl⟩ : syracuseStep 4180967 = 6271451) B6271451
theorem B2976743 : Blo 1651525 2976743 := bstep (se 1 (by rfl) ⟨2232557, by rfl⟩ : syracuseStep 2976743 = 4465115) B4465115
theorem B2092007 : Blo 1651525 2092007 := bstep (se 1 (by rfl) ⟨1569005, by rfl⟩ : syracuseStep 2092007 = 3138011) B3138011
theorem B15281167 : Blo 1651525 15281167 := bstep (se 1 (by rfl) ⟨11460875, by rfl⟩ : syracuseStep 15281167 = 22921751) B22921751
theorem B15494159 : Blo 1651525 15494159 := bstep (se 1 (by rfl) ⟨11620619, by rfl⟩ : syracuseStep 15494159 = 23241239) B23241239
theorem B5958875 : Blo 1651525 5958875 := bstep (se 1 (by rfl) ⟨4469156, by rfl⟩ : syracuseStep 5958875 = 8938313) B8938313
theorem B2477351 : Blo 1651525 2477351 := bstep (se 1 (by rfl) ⟨1858013, by rfl⟩ : syracuseStep 2477351 = 3716027) B3716027
theorem B11906423 : Blo 1651525 11906423 := bstep (se 1 (by rfl) ⟨8929817, by rfl⟩ : syracuseStep 11906423 = 17859635) B17859635
theorem B2477435 : Blo 1651525 2477435 := bstep (se 1 (by rfl) ⟨1858076, by rfl⟩ : syracuseStep 2477435 = 3716153) B3716153
theorem B6450569 : Blo 1651525 6450569 := bstep (se 2 (by rfl) ⟨2418963, by rfl⟩ : syracuseStep 6450569 = 4837927) B4837927
theorem B5295547 : Blo 1651525 5295547 := bstep (se 1 (by rfl) ⟨3971660, by rfl⟩ : syracuseStep 5295547 = 7943321) B7943321
theorem B2477561 : Blo 1651525 2477561 := bstep (se 2 (by rfl) ⟨929085, by rfl⟩ : syracuseStep 2477561 = 1858171) B1858171
theorem B1674815 : Blo 1651525 1674815 := bstep (se 1 (by rfl) ⟨1256111, by rfl⟩ : syracuseStep 1674815 = 2512223) B2512223
theorem B2477663 : Blo 1651525 2477663 := bstep (se 1 (by rfl) ⟨1858247, by rfl⟩ : syracuseStep 2477663 = 3716495) B3716495
theorem B17198689 : Blo 1651525 17198689 := bstep (se 2 (by rfl) ⟨6449508, by rfl⟩ : syracuseStep 17198689 = 12899017) B12899017
theorem B9408109 : Blo 1651525 9408109 := bstep (se 3 (by rfl) ⟨1764020, by rfl⟩ : syracuseStep 9408109 = 3528041) B3528041
theorem B4181665 : Blo 1651525 4181665 := bstep (se 2 (by rfl) ⟨1568124, by rfl⟩ : syracuseStep 4181665 = 3136249) B3136249
theorem B6360839 : Blo 1651525 6360839 := bstep (se 1 (by rfl) ⟨4770629, by rfl⟩ : syracuseStep 6360839 = 9541259) B9541259
theorem B6270767 : Blo 1651525 6270767 := bstep (se 1 (by rfl) ⟨4703075, by rfl⟩ : syracuseStep 6270767 = 9406151) B9406151
theorem B4181807 : Blo 1651525 4181807 := bstep (se 1 (by rfl) ⟨3136355, by rfl⟩ : syracuseStep 4181807 = 6272711) B6272711
theorem B2789167 : Blo 1651525 2789167 := bstep (se 1 (by rfl) ⟨2091875, by rfl⟩ : syracuseStep 2789167 = 4183751) B4183751
theorem B2477879 : Blo 1651525 2477879 := bstep (se 1 (by rfl) ⟨1858409, by rfl⟩ : syracuseStep 2477879 = 3716819) B3716819
theorem B2478185 : Blo 1651525 2478185 := bstep (se 2 (by rfl) ⟨929319, by rfl⟩ : syracuseStep 2478185 = 1858639) B1858639
theorem B4526209 : Blo 1651525 4526209 := bstep (se 2 (by rfl) ⟨1697328, by rfl⟩ : syracuseStep 4526209 = 3394657) B3394657
theorem B4706515 : Blo 1651525 4706515 := bstep (se 1 (by rfl) ⟨3529886, by rfl⟩ : syracuseStep 4706515 = 7059773) B7059773
theorem B2478503 : Blo 1651525 2478503 := bstep (se 1 (by rfl) ⟨1858877, by rfl⟩ : syracuseStep 2478503 = 3717755) B3717755
theorem B4182455 : Blo 1651525 4182455 := bstep (se 1 (by rfl) ⟨3136841, by rfl⟩ : syracuseStep 4182455 = 6273683) B6273683
theorem B2478587 : Blo 1651525 2478587 := bstep (se 1 (by rfl) ⟨1858940, by rfl⟩ : syracuseStep 2478587 = 3717881) B3717881
theorem B3527239 : Blo 1651525 3527239 := bstep (se 1 (by rfl) ⟨2645429, by rfl⟩ : syracuseStep 3527239 = 5290859) B5290859
theorem B2478713 : Blo 1651525 2478713 := bstep (se 2 (by rfl) ⟨929517, by rfl⟩ : syracuseStep 2478713 = 1859035) B1859035
theorem B2478767 : Blo 1651525 2478767 := bstep (se 1 (by rfl) ⟨1859075, by rfl⟩ : syracuseStep 2478767 = 3718151) B3718151
theorem B5575391 : Blo 1651525 5575391 := bstep (se 1 (by rfl) ⟨4181543, by rfl⟩ : syracuseStep 5575391 = 8363087) B8363087
theorem B2478815 : Blo 1651525 2478815 := bstep (se 1 (by rfl) ⟨1859111, by rfl⟩ : syracuseStep 2478815 = 3718223) B3718223
theorem B1675999 : Blo 1651525 1675999 := bstep (se 1 (by rfl) ⟨1256999, by rfl⟩ : syracuseStep 1675999 = 2513999) B2513999
theorem B1651611 : Blo 1651525 1651611 := bstep (se 1 (by rfl) ⟨1238708, by rfl⟩ : syracuseStep 1651611 = 2477417) B2477417
theorem B1651663 : Blo 1651525 1651663 := bstep (se 1 (by rfl) ⟨1238747, by rfl⟩ : syracuseStep 1651663 = 2477495) B2477495
theorem B1651687 : Blo 1651525 1651687 := bstep (se 1 (by rfl) ⟨1238765, by rfl⟩ : syracuseStep 1651687 = 2477531) B2477531
theorem B2479079 : Blo 1651525 2479079 := bstep (se 1 (by rfl) ⟨1859309, by rfl⟩ : syracuseStep 2479079 = 3718619) B3718619
theorem B3716135 : Blo 1651525 3716135 := bstep (se 1 (by rfl) ⟨2787101, by rfl⟩ : syracuseStep 3716135 = 5574203) B5574203
theorem B5575823 : Blo 1651525 5575823 := bstep (se 1 (by rfl) ⟨4181867, by rfl⟩ : syracuseStep 5575823 = 8363735) B8363735
theorem B14111891 : Blo 1651525 14111891 := bstep (se 1 (by rfl) ⟨10583918, by rfl⟩ : syracuseStep 14111891 = 21167837) B21167837
theorem B3716315 : Blo 1651525 3716315 := bstep (se 1 (by rfl) ⟨2787236, by rfl⟩ : syracuseStep 3716315 = 5574473) B5574473
theorem B2479337 : Blo 1651525 2479337 := bstep (se 2 (by rfl) ⟨929751, by rfl⟩ : syracuseStep 2479337 = 1859503) B1859503
theorem B1651999 : Blo 1651525 1651999 := bstep (se 1 (by rfl) ⟨1238999, by rfl⟩ : syracuseStep 1651999 = 2477999) B2477999
theorem B2479391 : Blo 1651525 2479391 := bstep (se 1 (by rfl) ⟨1859543, by rfl⟩ : syracuseStep 2479391 = 3719087) B3719087
theorem B1652059 : Blo 1651525 1652059 := bstep (se 1 (by rfl) ⟨1239044, by rfl⟩ : syracuseStep 1652059 = 2478089) B2478089
theorem B9057631 : Blo 1651525 9057631 := bstep (se 1 (by rfl) ⟨6793223, by rfl⟩ : syracuseStep 9057631 = 13586447) B13586447
theorem B1652079 : Blo 1651525 1652079 := bstep (se 1 (by rfl) ⟨1239059, by rfl⟩ : syracuseStep 1652079 = 2478119) B2478119
theorem B17184125 : Blo 1651525 17184125 := bstep (se 3 (by rfl) ⟨3222023, by rfl⟩ : syracuseStep 17184125 = 6444047) B6444047
theorem B3716513 : Blo 1651525 3716513 := bstep (se 2 (by rfl) ⟨1393692, by rfl⟩ : syracuseStep 3716513 = 2787385) B2787385
theorem B1652135 : Blo 1651525 1652135 := bstep (se 1 (by rfl) ⟨1239101, by rfl⟩ : syracuseStep 1652135 = 2478203) B2478203
theorem B23811509 : Blo 1651525 23811509 := bstep (se 5 (by rfl) ⟨1116164, by rfl⟩ : syracuseStep 23811509 = 2232329) B2232329
theorem B2479559 : Blo 1651525 2479559 := bstep (se 1 (by rfl) ⟨1859669, by rfl⟩ : syracuseStep 2479559 = 3719339) B3719339
theorem B1652219 : Blo 1651525 1652219 := bstep (se 1 (by rfl) ⟨1239164, by rfl⟩ : syracuseStep 1652219 = 2478329) B2478329
theorem B4183559 : Blo 1651525 4183559 := bstep (se 1 (by rfl) ⟨3137669, by rfl⟩ : syracuseStep 4183559 = 6275339) B6275339
theorem B4183609 : Blo 1651525 4183609 := bstep (se 2 (by rfl) ⟨1568853, by rfl⟩ : syracuseStep 4183609 = 3137707) B3137707
theorem B1652287 : Blo 1651525 1652287 := bstep (se 1 (by rfl) ⟨1239215, by rfl⟩ : syracuseStep 1652287 = 2478431) B2478431
theorem B1652295 : Blo 1651525 1652295 := bstep (se 1 (by rfl) ⟨1239221, by rfl⟩ : syracuseStep 1652295 = 2478443) B2478443
theorem B8361629 : Blo 1651525 8361629 := bstep (se 3 (by rfl) ⟨1567805, by rfl⟩ : syracuseStep 8361629 = 3135611) B3135611
theorem B1652447 : Blo 1651525 1652447 := bstep (se 1 (by rfl) ⟨1239335, by rfl⟩ : syracuseStep 1652447 = 2478671) B2478671
theorem B35739407 : Blo 1651525 35739407 := bstep (se 1 (by rfl) ⟨26804555, by rfl⟩ : syracuseStep 35739407 = 53609111) B53609111
theorem B2479913 : Blo 1651525 2479913 := bstep (se 2 (by rfl) ⟨929967, by rfl⟩ : syracuseStep 2479913 = 1859935) B1859935
theorem B1652527 : Blo 1651525 1652527 := bstep (se 1 (by rfl) ⟨1239395, by rfl⟩ : syracuseStep 1652527 = 2478791) B2478791
theorem B2479919 : Blo 1651525 2479919 := bstep (se 1 (by rfl) ⟨1859939, by rfl⟩ : syracuseStep 2479919 = 3719879) B3719879
theorem B4183913 : Blo 1651525 4183913 := bstep (se 2 (by rfl) ⟨1568967, by rfl⟩ : syracuseStep 4183913 = 3137935) B3137935
theorem B4708201 : Blo 1651525 4708201 := bstep (se 2 (by rfl) ⟨1765575, by rfl⟩ : syracuseStep 4708201 = 3531151) B3531151
theorem B33912695 : Blo 1651525 33912695 := bstep (se 1 (by rfl) ⟨25434521, by rfl⟩ : syracuseStep 33912695 = 50869043) B50869043
theorem B1652635 : Blo 1651525 1652635 := bstep (se 1 (by rfl) ⟨1239476, by rfl⟩ : syracuseStep 1652635 = 2478953) B2478953
theorem B120657869 : Blo 1651525 120657869 := bstep (se 3 (by rfl) ⟨22623350, by rfl⟩ : syracuseStep 120657869 = 45246701) B45246701
theorem B3717071 : Blo 1651525 3717071 := bstep (se 1 (by rfl) ⟨2787803, by rfl⟩ : syracuseStep 3717071 = 5575607) B5575607
theorem B1652687 : Blo 1651525 1652687 := bstep (se 1 (by rfl) ⟨1239515, by rfl⟩ : syracuseStep 1652687 = 2479031) B2479031
theorem B1652711 : Blo 1651525 1652711 := bstep (se 1 (by rfl) ⟨1239533, by rfl⟩ : syracuseStep 1652711 = 2479067) B2479067
theorem B5576957 : Blo 1651525 5576957 := bstep (se 3 (by rfl) ⟨1045679, by rfl⟩ : syracuseStep 5576957 = 2091359) B2091359
theorem B2234633 : Blo 1651525 2234633 := bstep (se 2 (by rfl) ⟨837987, by rfl⟩ : syracuseStep 2234633 = 1675975) B1675975
theorem B3971353 : Blo 1651525 3971353 := bstep (se 2 (by rfl) ⟨1489257, by rfl⟩ : syracuseStep 3971353 = 2978515) B2978515
theorem B1653023 : Blo 1651525 1653023 := bstep (se 1 (by rfl) ⟨1239767, by rfl⟩ : syracuseStep 1653023 = 2479535) B2479535
theorem B3717449 : Blo 1651525 3717449 := bstep (se 2 (by rfl) ⟨1394043, by rfl⟩ : syracuseStep 3717449 = 2788087) B2788087
theorem B23837003 : Blo 1651525 23837003 := bstep (se 1 (by rfl) ⟨17877752, by rfl⟩ : syracuseStep 23837003 = 35755505) B35755505
theorem B3717467 : Blo 1651525 3717467 := bstep (se 1 (by rfl) ⟨2788100, by rfl⟩ : syracuseStep 3717467 = 5576201) B5576201
theorem B1653083 : Blo 1651525 1653083 := bstep (se 1 (by rfl) ⟨1239812, by rfl⟩ : syracuseStep 1653083 = 2479625) B2479625
theorem B1653103 : Blo 1651525 1653103 := bstep (se 1 (by rfl) ⟨1239827, by rfl⟩ : syracuseStep 1653103 = 2479655) B2479655
theorem B2234747 : Blo 1651525 2234747 := bstep (se 1 (by rfl) ⟨1676060, by rfl⟩ : syracuseStep 2234747 = 3352121) B3352121
theorem B1653159 : Blo 1651525 1653159 := bstep (se 1 (by rfl) ⟨1239869, by rfl⟩ : syracuseStep 1653159 = 2479739) B2479739
theorem B1857991 : Blo 1651525 1857991 := bstep (se 1 (by rfl) ⟨1393493, by rfl⟩ : syracuseStep 1857991 = 2786987) B2786987
theorem B4184531 : Blo 1651525 4184531 := bstep (se 1 (by rfl) ⟨3138398, by rfl⟩ : syracuseStep 4184531 = 6276797) B6276797
theorem B1653243 : Blo 1651525 1653243 := bstep (se 1 (by rfl) ⟨1239932, by rfl⟩ : syracuseStep 1653243 = 2479865) B2479865
theorem B7060031 : Blo 1651525 7060031 := bstep (se 1 (by rfl) ⟨5295023, by rfl⟩ : syracuseStep 7060031 = 10590047) B10590047
theorem B1653311 : Blo 1651525 1653311 := bstep (se 1 (by rfl) ⟨1239983, by rfl⟩ : syracuseStep 1653311 = 2479967) B2479967
theorem B1653319 : Blo 1651525 1653319 := bstep (se 1 (by rfl) ⟨1239989, by rfl⟩ : syracuseStep 1653319 = 2479979) B2479979
theorem B14318153 : Blo 1651525 14318153 := bstep (se 2 (by rfl) ⟨5369307, by rfl⟩ : syracuseStep 14318153 = 10738615) B10738615
theorem B8370863 : Blo 1651525 8370863 := bstep (se 1 (by rfl) ⟨6278147, by rfl⟩ : syracuseStep 8370863 = 12556295) B12556295
theorem B1653471 : Blo 1651525 1653471 := bstep (se 1 (by rfl) ⟨1240103, by rfl⟩ : syracuseStep 1653471 = 2480207) B2480207
theorem B1858351 : Blo 1651525 1858351 := bstep (se 1 (by rfl) ⟨1393763, by rfl⟩ : syracuseStep 1858351 = 2787527) B2787527
theorem B1858459 : Blo 1651525 1858459 := bstep (se 1 (by rfl) ⟨1393844, by rfl⟩ : syracuseStep 1858459 = 2787689) B2787689
theorem B3718043 : Blo 1651525 3718043 := bstep (se 1 (by rfl) ⟨2788532, by rfl⟩ : syracuseStep 3718043 = 5577065) B5577065
theorem B8362925 : Blo 1651525 8362925 := bstep (se 3 (by rfl) ⟨1568048, by rfl⟩ : syracuseStep 8362925 = 3136097) B3136097
theorem B5577767 : Blo 1651525 5577767 := bstep (se 1 (by rfl) ⟨4183325, by rfl⟩ : syracuseStep 5577767 = 8366651) B8366651
theorem B3718241 : Blo 1651525 3718241 := bstep (se 2 (by rfl) ⟨1394340, by rfl⟩ : syracuseStep 3718241 = 2788681) B2788681
theorem B1858855 : Blo 1651525 1858855 := bstep (se 1 (by rfl) ⟨1394141, by rfl⟩ : syracuseStep 1858855 = 2788283) B2788283
theorem B3718439 : Blo 1651525 3718439 := bstep (se 1 (by rfl) ⟨2788829, by rfl⟩ : syracuseStep 3718439 = 5577659) B5577659
theorem B21175627 : Blo 1651525 21175627 := bstep (se 1 (by rfl) ⟨15881720, by rfl⟩ : syracuseStep 21175627 = 31763441) B31763441
theorem B8936801 : Blo 1651525 8936801 := bstep (se 2 (by rfl) ⟨3351300, by rfl⟩ : syracuseStep 8936801 = 6702601) B6702601
theorem B1858927 : Blo 1651525 1858927 := bstep (se 1 (by rfl) ⟨1394195, by rfl⟩ : syracuseStep 1858927 = 2788391) B2788391
theorem B5578199 : Blo 1651525 5578199 := bstep (se 1 (by rfl) ⟨4183649, by rfl⟩ : syracuseStep 5578199 = 8367299) B8367299
theorem B3530297 : Blo 1651525 3530297 := bstep (se 2 (by rfl) ⟨1323861, by rfl⟩ : syracuseStep 3530297 = 2647723) B2647723
theorem B1859143 : Blo 1651525 1859143 := bstep (se 1 (by rfl) ⟨1394357, by rfl⟩ : syracuseStep 1859143 = 2788715) B2788715
theorem B6274655 : Blo 1651525 6274655 := bstep (se 1 (by rfl) ⟨4705991, by rfl⟩ : syracuseStep 6274655 = 9411983) B9411983
theorem B10583713 : Blo 1651525 10583713 := bstep (se 2 (by rfl) ⟨3968892, by rfl⟩ : syracuseStep 10583713 = 7937785) B7937785
theorem B3718817 : Blo 1651525 3718817 := bstep (se 2 (by rfl) ⟨1394556, by rfl⟩ : syracuseStep 3718817 = 2789113) B2789113
theorem B3350279 : Blo 1651525 3350279 := bstep (se 1 (by rfl) ⟨2512709, by rfl⟩ : syracuseStep 3350279 = 5025419) B5025419
theorem B2645801 : Blo 1651525 2645801 := bstep (se 2 (by rfl) ⟨992175, by rfl⟩ : syracuseStep 2645801 = 1984351) B1984351
theorem B6275353 : Blo 1651525 6275353 := bstep (se 2 (by rfl) ⟨2353257, by rfl⟩ : syracuseStep 6275353 = 4706515) B4706515
theorem B3719915 : Blo 1651525 3719915 := bstep (se 1 (by rfl) ⟨2789936, by rfl⟩ : syracuseStep 3719915 = 5579873) B5579873
theorem B4702985 : Blo 1651525 4702985 := bstep (se 2 (by rfl) ⟨1763619, by rfl⟩ : syracuseStep 4702985 = 3527239) B3527239
theorem B63497357 : Blo 1651525 63497357 := bstep (se 3 (by rfl) ⟨11905754, by rfl⟩ : syracuseStep 63497357 = 23811509) B23811509
theorem B80438579 : Blo 1651525 80438579 := bstep (se 1 (by rfl) ⟨60328934, by rfl⟩ : syracuseStep 80438579 = 120657869) B120657869
theorem B10585559 : Blo 1651525 10585559 := bstep (se 1 (by rfl) ⟨7939169, by rfl⟩ : syracuseStep 10585559 = 15878339) B15878339
theorem B4466173 : Blo 1651525 4466173 := bstep (se 3 (by rfl) ⟨837407, by rfl⟩ : syracuseStep 4466173 = 1674815) B1674815
theorem B4703827 : Blo 1651525 4703827 := bstep (se 1 (by rfl) ⟨3527870, by rfl⟩ : syracuseStep 4703827 = 7055741) B7055741
theorem B47629943 : Blo 1651525 47629943 := bstep (se 1 (by rfl) ⟨35722457, by rfl⟩ : syracuseStep 47629943 = 71444915) B71444915
theorem B9545435 : Blo 1651525 9545435 := bstep (se 1 (by rfl) ⟨7159076, by rfl⟩ : syracuseStep 9545435 = 14318153) B14318153
theorem B5293831 : Blo 1651525 5293831 := bstep (se 1 (by rfl) ⟨3970373, by rfl⟩ : syracuseStep 5293831 = 7940747) B7940747
theorem B5580575 : Blo 1651525 5580575 := bstep (se 1 (by rfl) ⟨4185431, by rfl⟩ : syracuseStep 5580575 = 8370863) B8370863
theorem B12076841 : Blo 1651525 12076841 := bstep (se 2 (by rfl) ⟨4528815, by rfl⟩ : syracuseStep 12076841 = 9057631) B9057631
theorem B2787311 : Blo 1651525 2787311 := bstep (se 1 (by rfl) ⟨2090483, by rfl⟩ : syracuseStep 2787311 = 4180967) B4180967
theorem B1984495 : Blo 1651525 1984495 := bstep (se 1 (by rfl) ⟨1488371, by rfl⟩ : syracuseStep 1984495 = 2976743) B2976743
theorem B22931585 : Blo 1651525 22931585 := bstep (se 2 (by rfl) ⟨8599344, by rfl⟩ : syracuseStep 22931585 = 17198689) B17198689
theorem B12544145 : Blo 1651525 12544145 := bstep (se 2 (by rfl) ⟨4704054, by rfl⟩ : syracuseStep 12544145 = 9408109) B9408109
theorem B5957867 : Blo 1651525 5957867 := bstep (se 1 (by rfl) ⟨4468400, by rfl⟩ : syracuseStep 5957867 = 8936801) B8936801
theorem B90433853 : Blo 1651525 90433853 := bstep (se 3 (by rfl) ⟨16956347, by rfl⟩ : syracuseStep 90433853 = 33912695) B33912695
theorem B2353531 : Blo 1651525 2353531 := bstep (se 1 (by rfl) ⟨1765148, by rfl⟩ : syracuseStep 2353531 = 3530297) B3530297
theorem B6277601 : Blo 1651525 6277601 := bstep (se 2 (by rfl) ⟨2354100, by rfl⟩ : syracuseStep 6277601 = 4708201) B4708201
theorem B1763867 : Blo 1651525 1763867 := bstep (se 1 (by rfl) ⟨1322900, by rfl⟩ : syracuseStep 1763867 = 2645801) B2645801
theorem B4180511 : Blo 1651525 4180511 := bstep (se 1 (by rfl) ⟨3135383, by rfl⟩ : syracuseStep 4180511 = 6270767) B6270767
theorem B2787871 : Blo 1651525 2787871 := bstep (se 1 (by rfl) ⟨2090903, by rfl⟩ : syracuseStep 2787871 = 4181807) B4181807
theorem B11905987 : Blo 1651525 11905987 := bstep (se 1 (by rfl) ⟨8929490, by rfl⟩ : syracuseStep 11905987 = 17858981) B17858981
theorem B2788303 : Blo 1651525 2788303 := bstep (se 1 (by rfl) ⟨2091227, by rfl⟩ : syracuseStep 2788303 = 4182455) B4182455
theorem B15887339 : Blo 1651525 15887339 := bstep (se 1 (by rfl) ⟨11915504, by rfl⟩ : syracuseStep 15887339 = 23831009) B23831009
theorem B5295137 : Blo 1651525 5295137 := bstep (se 2 (by rfl) ⟨1985676, by rfl⟩ : syracuseStep 5295137 = 3971353) B3971353
theorem B40217735 : Blo 1651525 40217735 := bstep (se 1 (by rfl) ⟨30163301, by rfl⟩ : syracuseStep 40217735 = 60326603) B60326603
theorem B5958791 : Blo 1651525 5958791 := bstep (se 1 (by rfl) ⟨4469093, by rfl⟩ : syracuseStep 5958791 = 8938187) B8938187
theorem B2477321 : Blo 1651525 2477321 := bstep (se 2 (by rfl) ⟨928995, by rfl⟩ : syracuseStep 2477321 = 1857991) B1857991
theorem B12725515 : Blo 1651525 12725515 := bstep (se 1 (by rfl) ⟨9544136, by rfl⟩ : syracuseStep 12725515 = 19088273) B19088273
theorem B5959021 : Blo 1651525 5959021 := bstep (se 3 (by rfl) ⟨1117316, by rfl⟩ : syracuseStep 5959021 = 2234633) B2234633
theorem B2477423 : Blo 1651525 2477423 := bstep (se 1 (by rfl) ⟨1858067, by rfl⟩ : syracuseStep 2477423 = 3716135) B3716135
theorem B9407927 : Blo 1651525 9407927 := bstep (se 1 (by rfl) ⟨7055945, by rfl⟩ : syracuseStep 9407927 = 14111891) B14111891
theorem B2477543 : Blo 1651525 2477543 := bstep (se 1 (by rfl) ⟨1858157, by rfl⟩ : syracuseStep 2477543 = 3716315) B3716315
theorem B11456083 : Blo 1651525 11456083 := bstep (se 1 (by rfl) ⟨8592062, by rfl⟩ : syracuseStep 11456083 = 17184125) B17184125
theorem B2477675 : Blo 1651525 2477675 := bstep (se 1 (by rfl) ⟨1858256, by rfl⟩ : syracuseStep 2477675 = 3716513) B3716513
theorem B18812573 : Blo 1651525 18812573 := bstep (se 3 (by rfl) ⟨3527357, by rfl⟩ : syracuseStep 18812573 = 7054715) B7054715
theorem B5959325 : Blo 1651525 5959325 := bstep (se 3 (by rfl) ⟨1117373, by rfl⟩ : syracuseStep 5959325 = 2234747) B2234747
theorem B2789039 : Blo 1651525 2789039 := bstep (se 1 (by rfl) ⟨2091779, by rfl⟩ : syracuseStep 2789039 = 4183559) B4183559
theorem B2477801 : Blo 1651525 2477801 := bstep (se 2 (by rfl) ⟨929175, by rfl⟩ : syracuseStep 2477801 = 1858351) B1858351
theorem B5574419 : Blo 1651525 5574419 := bstep (se 1 (by rfl) ⟨4180814, by rfl⟩ : syracuseStep 5574419 = 8361629) B8361629
theorem B2477945 : Blo 1651525 2477945 := bstep (se 2 (by rfl) ⟨929229, by rfl⟩ : syracuseStep 2477945 = 1858459) B1858459
theorem B21458843 : Blo 1651525 21458843 := bstep (se 1 (by rfl) ⟨16094132, by rfl⟩ : syracuseStep 21458843 = 32188265) B32188265
theorem B2789275 : Blo 1651525 2789275 := bstep (se 1 (by rfl) ⟨2091956, by rfl⟩ : syracuseStep 2789275 = 4183913) B4183913
theorem B2478047 : Blo 1651525 2478047 := bstep (se 1 (by rfl) ⟨1858535, by rfl⟩ : syracuseStep 2478047 = 3717071) B3717071
theorem B2478299 : Blo 1651525 2478299 := bstep (se 1 (by rfl) ⟨1858724, by rfl⟩ : syracuseStep 2478299 = 3717449) B3717449
theorem B2478311 : Blo 1651525 2478311 := bstep (se 1 (by rfl) ⟨1858733, by rfl⟩ : syracuseStep 2478311 = 3717467) B3717467
theorem B2789687 : Blo 1651525 2789687 := bstep (se 1 (by rfl) ⟨2092265, by rfl⟩ : syracuseStep 2789687 = 4184531) B4184531
theorem B4706687 : Blo 1651525 4706687 := bstep (se 1 (by rfl) ⟨3530015, by rfl⟩ : syracuseStep 4706687 = 7060031) B7060031
theorem B2478473 : Blo 1651525 2478473 := bstep (se 2 (by rfl) ⟨929427, by rfl⟩ : syracuseStep 2478473 = 1858855) B1858855
theorem B28234169 : Blo 1651525 28234169 := bstep (se 2 (by rfl) ⟨10587813, by rfl⟩ : syracuseStep 28234169 = 21175627) B21175627
theorem B8368595 : Blo 1651525 8368595 := bstep (se 1 (by rfl) ⟨6276446, by rfl⟩ : syracuseStep 8368595 = 12552893) B12552893
theorem B2478569 : Blo 1651525 2478569 := bstep (se 2 (by rfl) ⟨929463, by rfl⟩ : syracuseStep 2478569 = 1858927) B1858927
theorem B12546575 : Blo 1651525 12546575 := bstep (se 1 (by rfl) ⟨9409931, by rfl⟩ : syracuseStep 12546575 = 18819863) B18819863
theorem B2478695 : Blo 1651525 2478695 := bstep (se 1 (by rfl) ⟨1859021, by rfl⟩ : syracuseStep 2478695 = 3718043) B3718043
theorem B5575283 : Blo 1651525 5575283 := bstep (se 1 (by rfl) ⟨4181462, by rfl⟩ : syracuseStep 5575283 = 8362925) B8362925
theorem B8934077 : Blo 1651525 8934077 := bstep (se 3 (by rfl) ⟨1675139, by rfl⟩ : syracuseStep 8934077 = 3350279) B3350279
theorem B11907805 : Blo 1651525 11907805 := bstep (se 3 (by rfl) ⟨2232713, by rfl⟩ : syracuseStep 11907805 = 4465427) B4465427
theorem B2478827 : Blo 1651525 2478827 := bstep (se 1 (by rfl) ⟨1859120, by rfl⟩ : syracuseStep 2478827 = 3718241) B3718241
theorem B2478857 : Blo 1651525 2478857 := bstep (se 2 (by rfl) ⟨929571, by rfl⟩ : syracuseStep 2478857 = 1859143) B1859143
theorem B5026585 : Blo 1651525 5026585 := bstep (se 2 (by rfl) ⟨1884969, by rfl⟩ : syracuseStep 5026585 = 3769939) B3769939
theorem B1651567 : Blo 1651525 1651567 := bstep (se 1 (by rfl) ⟨1238675, by rfl⟩ : syracuseStep 1651567 = 2477351) B2477351
theorem B2478959 : Blo 1651525 2478959 := bstep (se 1 (by rfl) ⟨1859219, by rfl⟩ : syracuseStep 2478959 = 3718439) B3718439
theorem B14111617 : Blo 1651525 14111617 := bstep (se 2 (by rfl) ⟨5291856, by rfl⟩ : syracuseStep 14111617 = 10583713) B10583713
theorem B5575553 : Blo 1651525 5575553 := bstep (se 2 (by rfl) ⟨2090832, by rfl⟩ : syracuseStep 5575553 = 4181665) B4181665
theorem B1651623 : Blo 1651525 1651623 := bstep (se 1 (by rfl) ⟨1238717, by rfl⟩ : syracuseStep 1651623 = 2477435) B2477435
theorem B28242917 : Blo 1651525 28242917 := bstep (se 4 (by rfl) ⟨2647773, by rfl⟩ : syracuseStep 28242917 = 5295547) B5295547
theorem B1651707 : Blo 1651525 1651707 := bstep (se 1 (by rfl) ⟨1238780, by rfl⟩ : syracuseStep 1651707 = 2477561) B2477561
theorem B1651775 : Blo 1651525 1651775 := bstep (se 1 (by rfl) ⟨1238831, by rfl⟩ : syracuseStep 1651775 = 2477663) B2477663
theorem B4183103 : Blo 1651525 4183103 := bstep (se 1 (by rfl) ⟨3137327, by rfl⟩ : syracuseStep 4183103 = 6274655) B6274655
theorem B2479211 : Blo 1651525 2479211 := bstep (se 1 (by rfl) ⟨1859408, by rfl⟩ : syracuseStep 2479211 = 3718817) B3718817
theorem B4240559 : Blo 1651525 4240559 := bstep (se 1 (by rfl) ⟨3180419, by rfl⟩ : syracuseStep 4240559 = 6360839) B6360839
theorem B1651919 : Blo 1651525 1651919 := bstep (se 1 (by rfl) ⟨1238939, by rfl⟩ : syracuseStep 1651919 = 2477879) B2477879
theorem B2479451 : Blo 1651525 2479451 := bstep (se 1 (by rfl) ⟨1859588, by rfl⟩ : syracuseStep 2479451 = 3719177) B3719177
theorem B1652123 : Blo 1651525 1652123 := bstep (se 1 (by rfl) ⟨1239092, by rfl⟩ : syracuseStep 1652123 = 2478185) B2478185
theorem B53597699 : Blo 1651525 53597699 := bstep (se 1 (by rfl) ⟨40198274, by rfl⟩ : syracuseStep 53597699 = 80396549) B80396549
theorem B1652335 : Blo 1651525 1652335 := bstep (se 1 (by rfl) ⟨1239251, by rfl⟩ : syracuseStep 1652335 = 2478503) B2478503
theorem B2479727 : Blo 1651525 2479727 := bstep (se 1 (by rfl) ⟨1859795, by rfl⟩ : syracuseStep 2479727 = 3719591) B3719591
theorem B325998229 : Blo 1651525 325998229 := bstep (se 6 (by rfl) ⟨7640583, by rfl⟩ : syracuseStep 325998229 = 15281167) B15281167
theorem B1652391 : Blo 1651525 1652391 := bstep (se 1 (by rfl) ⟨1239293, by rfl⟩ : syracuseStep 1652391 = 2478587) B2478587
theorem B5576363 : Blo 1651525 5576363 := bstep (se 1 (by rfl) ⟨4182272, by rfl⟩ : syracuseStep 5576363 = 8364545) B8364545
theorem B2479799 : Blo 1651525 2479799 := bstep (se 1 (by rfl) ⟨1859849, by rfl⟩ : syracuseStep 2479799 = 3719699) B3719699
theorem B2479835 : Blo 1651525 2479835 := bstep (se 1 (by rfl) ⟨1859876, by rfl⟩ : syracuseStep 2479835 = 3719753) B3719753
theorem B5363435 : Blo 1651525 5363435 := bstep (se 1 (by rfl) ⟨4022576, by rfl⟩ : syracuseStep 5363435 = 8045153) B8045153
theorem B1652475 : Blo 1651525 1652475 := bstep (se 1 (by rfl) ⟨1239356, by rfl⟩ : syracuseStep 1652475 = 2478713) B2478713
theorem B1652511 : Blo 1651525 1652511 := bstep (se 1 (by rfl) ⟨1239383, by rfl⟩ : syracuseStep 1652511 = 2478767) B2478767
theorem B3716927 : Blo 1651525 3716927 := bstep (se 1 (by rfl) ⟨2787695, by rfl⟩ : syracuseStep 3716927 = 5575391) B5575391
theorem B1652543 : Blo 1651525 1652543 := bstep (se 1 (by rfl) ⟨1239407, by rfl⟩ : syracuseStep 1652543 = 2478815) B2478815
theorem B2480009 : Blo 1651525 2480009 := bstep (se 2 (by rfl) ⟨930003, by rfl⟩ : syracuseStep 2480009 = 1860007) B1860007
theorem B4708327 : Blo 1651525 4708327 := bstep (se 1 (by rfl) ⟨3531245, by rfl⟩ : syracuseStep 4708327 = 7062491) B7062491
theorem B5576687 : Blo 1651525 5576687 := bstep (se 1 (by rfl) ⟨4182515, by rfl⟩ : syracuseStep 5576687 = 8365031) B8365031
theorem B1652719 : Blo 1651525 1652719 := bstep (se 1 (by rfl) ⟨1239539, by rfl⟩ : syracuseStep 1652719 = 2479079) B2479079
theorem B2480111 : Blo 1651525 2480111 := bstep (se 1 (by rfl) ⟨1860083, by rfl⟩ : syracuseStep 2480111 = 3720167) B3720167
theorem B24139781 : Blo 1651525 24139781 := bstep (se 4 (by rfl) ⟨2263104, by rfl⟩ : syracuseStep 24139781 = 4526209) B4526209
theorem B3717215 : Blo 1651525 3717215 := bstep (se 1 (by rfl) ⟨2787911, by rfl⟩ : syracuseStep 3717215 = 5575823) B5575823
theorem B4184207 : Blo 1651525 4184207 := bstep (se 1 (by rfl) ⟨3138155, by rfl⟩ : syracuseStep 4184207 = 6276311) B6276311
theorem B1652891 : Blo 1651525 1652891 := bstep (se 1 (by rfl) ⟨1239668, by rfl⟩ : syracuseStep 1652891 = 2479337) B2479337
theorem B1652927 : Blo 1651525 1652927 := bstep (se 1 (by rfl) ⟨1239695, by rfl⟩ : syracuseStep 1652927 = 2479391) B2479391
theorem B5576903 : Blo 1651525 5576903 := bstep (se 1 (by rfl) ⟨4182677, by rfl⟩ : syracuseStep 5576903 = 8365355) B8365355
theorem B3971315 : Blo 1651525 3971315 := bstep (se 1 (by rfl) ⟨2978486, by rfl⟩ : syracuseStep 3971315 = 5956973) B5956973
theorem B2234665 : Blo 1651525 2234665 := bstep (se 2 (by rfl) ⟨837999, by rfl⟩ : syracuseStep 2234665 = 1675999) B1675999
theorem B1653039 : Blo 1651525 1653039 := bstep (se 1 (by rfl) ⟨1239779, by rfl⟩ : syracuseStep 1653039 = 2479559) B2479559
theorem B1653275 : Blo 1651525 1653275 := bstep (se 1 (by rfl) ⟨1239956, by rfl⟩ : syracuseStep 1653275 = 2479913) B2479913
theorem B1653279 : Blo 1651525 1653279 := bstep (se 1 (by rfl) ⟨1239959, by rfl⟩ : syracuseStep 1653279 = 2479919) B2479919
theorem B2513513 : Blo 1651525 2513513 := bstep (se 2 (by rfl) ⟨942567, by rfl⟩ : syracuseStep 2513513 = 1885135) B1885135
theorem B5577551 : Blo 1651525 5577551 := bstep (se 1 (by rfl) ⟨4183163, by rfl⟩ : syracuseStep 5577551 = 8366327) B8366327
theorem B3717971 : Blo 1651525 3717971 := bstep (se 1 (by rfl) ⟨2788478, by rfl⟩ : syracuseStep 3717971 = 5576957) B5576957
theorem B15891335 : Blo 1651525 15891335 := bstep (se 1 (by rfl) ⟨11918501, by rfl⟩ : syracuseStep 15891335 = 23837003) B23837003
theorem B3529631 : Blo 1651525 3529631 := bstep (se 1 (by rfl) ⟨2647223, by rfl⟩ : syracuseStep 3529631 = 5294447) B5294447
theorem B3136553 : Blo 1651525 3136553 := bstep (se 2 (by rfl) ⟨1176207, by rfl⟩ : syracuseStep 3136553 = 2352415) B2352415
theorem B3136583 : Blo 1651525 3136583 := bstep (se 1 (by rfl) ⟨2352437, by rfl⟩ : syracuseStep 3136583 = 4704875) B4704875
theorem B5577875 : Blo 1651525 5577875 := bstep (se 1 (by rfl) ⟨4183406, by rfl⟩ : syracuseStep 5577875 = 8366813) B8366813
theorem B1858783 : Blo 1651525 1858783 := bstep (se 1 (by rfl) ⟨1394087, by rfl⟩ : syracuseStep 1858783 = 2788175) B2788175
theorem B10329439 : Blo 1651525 10329439 := bstep (se 1 (by rfl) ⟨7747079, by rfl⟩ : syracuseStep 10329439 = 15494159) B15494159
theorem B3718511 : Blo 1651525 3718511 := bstep (se 1 (by rfl) ⟨2788883, by rfl⟩ : syracuseStep 3718511 = 5577767) B5577767
theorem B95305085 : Blo 1651525 95305085 := bstep (se 3 (by rfl) ⟨17869703, by rfl⟩ : syracuseStep 95305085 = 35739407) B35739407
theorem B5578145 : Blo 1651525 5578145 := bstep (se 2 (by rfl) ⟨2091804, by rfl⟩ : syracuseStep 5578145 = 4183609) B4183609
theorem B3972583 : Blo 1651525 3972583 := bstep (se 1 (by rfl) ⟨2979437, by rfl⟩ : syracuseStep 3972583 = 5958875) B5958875
theorem B7937615 : Blo 1651525 7937615 := bstep (se 1 (by rfl) ⟨5953211, by rfl⟩ : syracuseStep 7937615 = 11906423) B11906423
theorem B4300379 : Blo 1651525 4300379 := bstep (se 1 (by rfl) ⟨3225284, by rfl⟩ : syracuseStep 4300379 = 6450569) B6450569
theorem B3718799 : Blo 1651525 3718799 := bstep (se 1 (by rfl) ⟨2789099, by rfl⟩ : syracuseStep 3718799 = 5578199) B5578199
theorem B3718889 : Blo 1651525 3718889 := bstep (se 2 (by rfl) ⟨1394583, by rfl⟩ : syracuseStep 3718889 = 2789167) B2789167
theorem B5578685 : Blo 1651525 5578685 := bstep (se 3 (by rfl) ⟨1046003, by rfl⟩ : syracuseStep 5578685 = 2092007) B2092007
theorem B8364221 : Blo 1651525 8364221 := bstep (se 3 (by rfl) ⟨1568291, by rfl⟩ : syracuseStep 8364221 = 3136583) B3136583
theorem B1859791 : Blo 1651525 1859791 := bstep (se 1 (by rfl) ⟨1394843, by rfl⟩ : syracuseStep 1859791 = 2789687) B2789687
theorem B3137791 : Blo 1651525 3137791 := bstep (se 1 (by rfl) ⟨2353343, by rfl⟩ : syracuseStep 3137791 = 4706687) B4706687
theorem B5579063 : Blo 1651525 5579063 := bstep (se 1 (by rfl) ⟨4184297, by rfl⟩ : syracuseStep 5579063 = 8368595) B8368595
theorem B8364383 : Blo 1651525 8364383 := bstep (se 1 (by rfl) ⟨6273287, by rfl⟩ : syracuseStep 8364383 = 12546575) B12546575
theorem B5956051 : Blo 1651525 5956051 := bstep (se 1 (by rfl) ⟨4467038, by rfl⟩ : syracuseStep 5956051 = 8934077) B8934077
theorem B3138041 : Blo 1651525 3138041 := bstep (se 2 (by rfl) ⟨1176765, by rfl⟩ : syracuseStep 3138041 = 2353531) B2353531
theorem B53625719 : Blo 1651525 53625719 := bstep (se 1 (by rfl) ⟨40219289, by rfl⟩ : syracuseStep 53625719 = 80438579) B80438579
theorem B15877073 : Blo 1651525 15877073 := bstep (se 2 (by rfl) ⟨5953902, by rfl⟩ : syracuseStep 15877073 = 11907805) B11907805
theorem B6702113 : Blo 1651525 6702113 := bstep (se 2 (by rfl) ⟨2513292, by rfl⟩ : syracuseStep 6702113 = 5026585) B5026585
theorem B31753295 : Blo 1651525 31753295 := bstep (se 1 (by rfl) ⟨23814971, by rfl⟩ : syracuseStep 31753295 = 47629943) B47629943
theorem B3720383 : Blo 1651525 3720383 := bstep (se 1 (by rfl) ⟨2790287, by rfl⟩ : syracuseStep 3720383 = 5580575) B5580575
theorem B4703645 : Blo 1651525 4703645 := bstep (se 3 (by rfl) ⟨881933, by rfl⟩ : syracuseStep 4703645 = 1763867) B1763867
theorem B15287723 : Blo 1651525 15287723 := bstep (se 1 (by rfl) ⟨11465792, by rfl⟩ : syracuseStep 15287723 = 22931585) B22931585
theorem B2787007 : Blo 1651525 2787007 := bstep (se 1 (by rfl) ⟨2090255, by rfl⟩ : syracuseStep 2787007 = 4180511) B4180511
theorem B13772585 : Blo 1651525 13772585 := bstep (se 2 (by rfl) ⟨5164719, by rfl⟩ : syracuseStep 13772585 = 10329439) B10329439
theorem B10594223 : Blo 1651525 10594223 := bstep (se 1 (by rfl) ⟨7945667, by rfl⟩ : syracuseStep 10594223 = 15891335) B15891335
theorem B2353087 : Blo 1651525 2353087 := bstep (se 1 (by rfl) ⟨1764815, by rfl⟩ : syracuseStep 2353087 = 3529631) B3529631
theorem B2091035 : Blo 1651525 2091035 := bstep (se 1 (by rfl) ⟨1568276, by rfl⟩ : syracuseStep 2091035 = 3136553) B3136553
theorem B21187109 : Blo 1651525 21187109 := bstep (se 4 (by rfl) ⟨1986291, by rfl⟩ : syracuseStep 21187109 = 3972583) B3972583
theorem B14305895 : Blo 1651525 14305895 := bstep (se 1 (by rfl) ⟨10729421, by rfl⟩ : syracuseStep 14305895 = 21458843) B21458843
theorem B6277769 : Blo 1651525 6277769 := bstep (se 2 (by rfl) ⟨2354163, by rfl⟩ : syracuseStep 6277769 = 4708327) B4708327
theorem B8367137 : Blo 1651525 8367137 := bstep (se 2 (by rfl) ⟨3137676, by rfl⟩ : syracuseStep 8367137 = 6275353) B6275353
theorem B61099109 : Blo 1651525 61099109 := bstep (se 4 (by rfl) ⟨5728041, by rfl⟩ : syracuseStep 61099109 = 11456083) B11456083
theorem B11308157 : Blo 1651525 11308157 := bstep (se 3 (by rfl) ⟨2120279, by rfl⟩ : syracuseStep 11308157 = 4240559) B4240559
theorem B18828611 : Blo 1651525 18828611 := bstep (se 1 (by rfl) ⟨14121458, by rfl⟩ : syracuseStep 18828611 = 28242917) B28242917
theorem B2788735 : Blo 1651525 2788735 := bstep (se 1 (by rfl) ⟨2091551, by rfl⟩ : syracuseStep 2788735 = 4183103) B4183103
theorem B42331571 : Blo 1651525 42331571 := bstep (se 1 (by rfl) ⟨31748678, by rfl⟩ : syracuseStep 42331571 = 63497357) B63497357
theorem B7057039 : Blo 1651525 7057039 := bstep (se 1 (by rfl) ⟨5292779, by rfl⟩ : syracuseStep 7057039 = 10585559) B10585559
theorem B2477951 : Blo 1651525 2477951 := bstep (se 1 (by rfl) ⟨1858463, by rfl⟩ : syracuseStep 2477951 = 3716927) B3716927
theorem B16093187 : Blo 1651525 16093187 := bstep (se 1 (by rfl) ⟨12069890, by rfl⟩ : syracuseStep 16093187 = 24139781) B24139781
theorem B2478143 : Blo 1651525 2478143 := bstep (se 1 (by rfl) ⟨1858607, by rfl⟩ : syracuseStep 2478143 = 3717215) B3717215
theorem B2789471 : Blo 1651525 2789471 := bstep (se 1 (by rfl) ⟨2092103, by rfl⟩ : syracuseStep 2789471 = 4184207) B4184207
theorem B60289235 : Blo 1651525 60289235 := bstep (se 1 (by rfl) ⟨45216926, by rfl⟩ : syracuseStep 60289235 = 90433853) B90433853
theorem B2478377 : Blo 1651525 2478377 := bstep (se 2 (by rfl) ⟨929391, by rfl⟩ : syracuseStep 2478377 = 1858783) B1858783
theorem B1675675 : Blo 1651525 1675675 := bstep (se 1 (by rfl) ⟨1256756, by rfl⟩ : syracuseStep 1675675 = 2513513) B2513513
theorem B2478647 : Blo 1651525 2478647 := bstep (se 1 (by rfl) ⟨1858985, by rfl⟩ : syracuseStep 2478647 = 3717971) B3717971
theorem B6271769 : Blo 1651525 6271769 := bstep (se 2 (by rfl) ⟨2351913, by rfl⟩ : syracuseStep 6271769 = 4703827) B4703827
theorem B1651547 : Blo 1651525 1651547 := bstep (se 1 (by rfl) ⟨1238660, by rfl⟩ : syracuseStep 1651547 = 2477321) B2477321
theorem B434664305 : Blo 1651525 434664305 := bstep (se 2 (by rfl) ⟨162999114, by rfl⟩ : syracuseStep 434664305 = 325998229) B325998229
theorem B1651615 : Blo 1651525 1651615 := bstep (se 1 (by rfl) ⟨1238711, by rfl⟩ : syracuseStep 1651615 = 2477423) B2477423
theorem B2479007 : Blo 1651525 2479007 := bstep (se 1 (by rfl) ⟨1859255, by rfl⟩ : syracuseStep 2479007 = 3718511) B3718511
theorem B6271951 : Blo 1651525 6271951 := bstep (se 1 (by rfl) ⟨4703963, by rfl⟩ : syracuseStep 6271951 = 9407927) B9407927
theorem B1651695 : Blo 1651525 1651695 := bstep (se 1 (by rfl) ⟨1238771, by rfl⟩ : syracuseStep 1651695 = 2477543) B2477543
theorem B7058441 : Blo 1651525 7058441 := bstep (se 2 (by rfl) ⟨2646915, by rfl⟩ : syracuseStep 7058441 = 5293831) B5293831
theorem B1651783 : Blo 1651525 1651783 := bstep (se 1 (by rfl) ⟨1238837, by rfl⟩ : syracuseStep 1651783 = 2477675) B2477675
theorem B2479199 : Blo 1651525 2479199 := bstep (se 1 (by rfl) ⟨1859399, by rfl⟩ : syracuseStep 2479199 = 3718799) B3718799
theorem B1651867 : Blo 1651525 1651867 := bstep (se 1 (by rfl) ⟨1238900, by rfl⟩ : syracuseStep 1651867 = 2477801) B2477801
theorem B2479259 : Blo 1651525 2479259 := bstep (se 1 (by rfl) ⟨1859444, by rfl⟩ : syracuseStep 2479259 = 3718889) B3718889
theorem B3716279 : Blo 1651525 3716279 := bstep (se 1 (by rfl) ⟨2787209, by rfl⟩ : syracuseStep 3716279 = 5574419) B5574419
theorem B1651963 : Blo 1651525 1651963 := bstep (se 1 (by rfl) ⟨1238972, by rfl⟩ : syracuseStep 1651963 = 2477945) B2477945
theorem B1652031 : Blo 1651525 1652031 := bstep (se 1 (by rfl) ⟨1239023, by rfl⟩ : syracuseStep 1652031 = 2478047) B2478047
theorem B14120365 : Blo 1651525 14120365 := bstep (se 3 (by rfl) ⟨2647568, by rfl⟩ : syracuseStep 14120365 = 5295137) B5295137
theorem B1652199 : Blo 1651525 1652199 := bstep (se 1 (by rfl) ⟨1239149, by rfl⟩ : syracuseStep 1652199 = 2478299) B2478299
theorem B1652207 : Blo 1651525 1652207 := bstep (se 1 (by rfl) ⟨1239155, by rfl⟩ : syracuseStep 1652207 = 2478311) B2478311
theorem B1652315 : Blo 1651525 1652315 := bstep (se 1 (by rfl) ⟨1239236, by rfl⟩ : syracuseStep 1652315 = 2478473) B2478473
theorem B18822779 : Blo 1651525 18822779 := bstep (se 1 (by rfl) ⟨14117084, by rfl⟩ : syracuseStep 18822779 = 28234169) B28234169
theorem B1652379 : Blo 1651525 1652379 := bstep (se 1 (by rfl) ⟨1239284, by rfl⟩ : syracuseStep 1652379 = 2478569) B2478569
theorem B1652463 : Blo 1651525 1652463 := bstep (se 1 (by rfl) ⟨1239347, by rfl⟩ : syracuseStep 1652463 = 2478695) B2478695
theorem B3716855 : Blo 1651525 3716855 := bstep (se 1 (by rfl) ⟨2787641, by rfl⟩ : syracuseStep 3716855 = 5575283) B5575283
theorem B1652551 : Blo 1651525 1652551 := bstep (se 1 (by rfl) ⟨1239413, by rfl⟩ : syracuseStep 1652551 = 2478827) B2478827
theorem B2479943 : Blo 1651525 2479943 := bstep (se 1 (by rfl) ⟨1859957, by rfl⟩ : syracuseStep 2479943 = 3719915) B3719915
theorem B3135323 : Blo 1651525 3135323 := bstep (se 1 (by rfl) ⟨2351492, by rfl⟩ : syracuseStep 3135323 = 4702985) B4702985
theorem B1652571 : Blo 1651525 1652571 := bstep (se 1 (by rfl) ⟨1239428, by rfl⟩ : syracuseStep 1652571 = 2478857) B2478857
theorem B1652639 : Blo 1651525 1652639 := bstep (se 1 (by rfl) ⟨1239479, by rfl⟩ : syracuseStep 1652639 = 2478959) B2478959
theorem B3717035 : Blo 1651525 3717035 := bstep (se 1 (by rfl) ⟨2787776, by rfl⟩ : syracuseStep 3717035 = 5575553) B5575553
theorem B10590173 : Blo 1651525 10590173 := bstep (se 3 (by rfl) ⟨1985657, by rfl⟩ : syracuseStep 10590173 = 3971315) B3971315
theorem B3717161 : Blo 1651525 3717161 := bstep (se 2 (by rfl) ⟨1393935, by rfl⟩ : syracuseStep 3717161 = 2787871) B2787871
theorem B1652807 : Blo 1651525 1652807 := bstep (se 1 (by rfl) ⟨1239605, by rfl⟩ : syracuseStep 1652807 = 2479211) B2479211
theorem B1652967 : Blo 1651525 1652967 := bstep (se 1 (by rfl) ⟨1239725, by rfl⟩ : syracuseStep 1652967 = 2479451) B2479451
theorem B35731799 : Blo 1651525 35731799 := bstep (se 1 (by rfl) ⟨26798849, by rfl⟩ : syracuseStep 35731799 = 53597699) B53597699
theorem B1653151 : Blo 1651525 1653151 := bstep (se 1 (by rfl) ⟨1239863, by rfl⟩ : syracuseStep 1653151 = 2479727) B2479727
theorem B3717575 : Blo 1651525 3717575 := bstep (se 1 (by rfl) ⟨2788181, by rfl⟩ : syracuseStep 3717575 = 5576363) B5576363
theorem B1653199 : Blo 1651525 1653199 := bstep (se 1 (by rfl) ⟨1239899, by rfl⟩ : syracuseStep 1653199 = 2479799) B2479799
theorem B1653223 : Blo 1651525 1653223 := bstep (se 1 (by rfl) ⟨1239917, by rfl⟩ : syracuseStep 1653223 = 2479835) B2479835
theorem B6363623 : Blo 1651525 6363623 := bstep (se 1 (by rfl) ⟨4772717, by rfl⟩ : syracuseStep 6363623 = 9545435) B9545435
theorem B18815489 : Blo 1651525 18815489 := bstep (se 2 (by rfl) ⟨7055808, by rfl⟩ : syracuseStep 18815489 = 14111617) B14111617
theorem B8051227 : Blo 1651525 8051227 := bstep (se 1 (by rfl) ⟨6038420, by rfl⟩ : syracuseStep 8051227 = 12076841) B12076841
theorem B15874649 : Blo 1651525 15874649 := bstep (se 2 (by rfl) ⟨5952993, by rfl⟩ : syracuseStep 15874649 = 11905987) B11905987
theorem B1653339 : Blo 1651525 1653339 := bstep (se 1 (by rfl) ⟨1240004, by rfl⟩ : syracuseStep 1653339 = 2480009) B2480009
theorem B3717737 : Blo 1651525 3717737 := bstep (se 2 (by rfl) ⟨1394151, by rfl⟩ : syracuseStep 3717737 = 2788303) B2788303
theorem B1858207 : Blo 1651525 1858207 := bstep (se 1 (by rfl) ⟨1393655, by rfl⟩ : syracuseStep 1858207 = 2787311) B2787311
theorem B3717791 : Blo 1651525 3717791 := bstep (se 1 (by rfl) ⟨2788343, by rfl⟩ : syracuseStep 3717791 = 5576687) B5576687
theorem B1653407 : Blo 1651525 1653407 := bstep (se 1 (by rfl) ⟨1240055, by rfl⟩ : syracuseStep 1653407 = 2480111) B2480111
theorem B67869413 : Blo 1651525 67869413 := bstep (se 4 (by rfl) ⟨6362757, by rfl⟩ : syracuseStep 67869413 = 12725515) B12725515
theorem B8362763 : Blo 1651525 8362763 := bstep (se 1 (by rfl) ⟨6272072, by rfl⟩ : syracuseStep 8362763 = 12544145) B12544145
theorem B3717935 : Blo 1651525 3717935 := bstep (se 1 (by rfl) ⟨2788451, by rfl⟩ : syracuseStep 3717935 = 5576903) B5576903
theorem B3971911 : Blo 1651525 3971911 := bstep (se 1 (by rfl) ⟨2978933, by rfl⟩ : syracuseStep 3971911 = 5957867) B5957867
theorem B4185067 : Blo 1651525 4185067 := bstep (se 1 (by rfl) ⟨3138800, by rfl⟩ : syracuseStep 4185067 = 6277601) B6277601
theorem B7945361 : Blo 1651525 7945361 := bstep (se 2 (by rfl) ⟨2979510, by rfl⟩ : syracuseStep 7945361 = 5959021) B5959021
theorem B3718367 : Blo 1651525 3718367 := bstep (se 1 (by rfl) ⟨2788775, by rfl⟩ : syracuseStep 3718367 = 5577551) B5577551
theorem B14302493 : Blo 1651525 14302493 := bstep (se 3 (by rfl) ⟨2681717, by rfl⟩ : syracuseStep 14302493 = 5363435) B5363435
theorem B10591559 : Blo 1651525 10591559 := bstep (se 1 (by rfl) ⟨7943669, by rfl⟩ : syracuseStep 10591559 = 15887339) B15887339
theorem B5954897 : Blo 1651525 5954897 := bstep (se 2 (by rfl) ⟨2233086, by rfl⟩ : syracuseStep 5954897 = 4466173) B4466173
theorem B26811823 : Blo 1651525 26811823 := bstep (se 1 (by rfl) ⟨20108867, by rfl⟩ : syracuseStep 26811823 = 40217735) B40217735
theorem B3972527 : Blo 1651525 3972527 := bstep (se 1 (by rfl) ⟨2979395, by rfl⟩ : syracuseStep 3972527 = 5958791) B5958791
theorem B3718583 : Blo 1651525 3718583 := bstep (se 1 (by rfl) ⟨2788937, by rfl⟩ : syracuseStep 3718583 = 5577875) B5577875
theorem B2979553 : Blo 1651525 2979553 := bstep (se 2 (by rfl) ⟨1117332, by rfl⟩ : syracuseStep 2979553 = 2234665) B2234665
theorem B63536723 : Blo 1651525 63536723 := bstep (se 1 (by rfl) ⟨47652542, by rfl⟩ : syracuseStep 63536723 = 95305085) B95305085
theorem B3718763 : Blo 1651525 3718763 := bstep (se 1 (by rfl) ⟨2789072, by rfl⟩ : syracuseStep 3718763 = 5578145) B5578145
theorem B5291743 : Blo 1651525 5291743 := bstep (se 1 (by rfl) ⟨3968807, by rfl⟩ : syracuseStep 5291743 = 7937615) B7937615
theorem B2866919 : Blo 1651525 2866919 := bstep (se 1 (by rfl) ⟨2150189, by rfl⟩ : syracuseStep 2866919 = 4300379) B4300379
theorem B12541715 : Blo 1651525 12541715 := bstep (se 1 (by rfl) ⟨9406286, by rfl⟩ : syracuseStep 12541715 = 18812573) B18812573
theorem B3972883 : Blo 1651525 3972883 := bstep (se 1 (by rfl) ⟨2979662, by rfl⟩ : syracuseStep 3972883 = 5959325) B5959325
theorem B1859359 : Blo 1651525 1859359 := bstep (se 1 (by rfl) ⟨1394519, by rfl⟩ : syracuseStep 1859359 = 2789039) B2789039
theorem B3719033 : Blo 1651525 3719033 := bstep (se 2 (by rfl) ⟨1394637, by rfl⟩ : syracuseStep 3719033 = 2789275) B2789275
theorem B3719123 : Blo 1651525 3719123 := bstep (se 1 (by rfl) ⟨2789342, by rfl⟩ : syracuseStep 3719123 = 5578685) B5578685
theorem B2645993 : Blo 1651525 2645993 := bstep (se 2 (by rfl) ⟨992247, by rfl⟩ : syracuseStep 2645993 = 1984495) B1984495
theorem B1859647 : Blo 1651525 1859647 := bstep (se 1 (by rfl) ⟨1394735, by rfl⟩ : syracuseStep 1859647 = 2789471) B2789471
theorem B3719375 : Blo 1651525 3719375 := bstep (se 1 (by rfl) ⟨2789531, by rfl⟩ : syracuseStep 3719375 = 5579063) B5579063
theorem B289776203 : Blo 1651525 289776203 := bstep (se 1 (by rfl) ⟨217332152, by rfl⟩ : syracuseStep 289776203 = 434664305) B434664305
theorem B35750479 : Blo 1651525 35750479 := bstep (se 1 (by rfl) ⟨26812859, by rfl⟩ : syracuseStep 35750479 = 53625719) B53625719
theorem B10584715 : Blo 1651525 10584715 := bstep (se 1 (by rfl) ⟨7938536, by rfl⟩ : syracuseStep 10584715 = 15877073) B15877073
theorem B21168863 : Blo 1651525 21168863 := bstep (se 1 (by rfl) ⟨15876647, by rfl⟩ : syracuseStep 21168863 = 31753295) B31753295
theorem B10191815 : Blo 1651525 10191815 := bstep (se 1 (by rfl) ⟨7643861, by rfl⟩ : syracuseStep 10191815 = 15287723) B15287723
theorem B2090215 : Blo 1651525 2090215 := bstep (se 1 (by rfl) ⟨1567661, by rfl⟩ : syracuseStep 2090215 = 3135323) B3135323
theorem B7062815 : Blo 1651525 7062815 := bstep (se 1 (by rfl) ⟨5297111, by rfl⟩ : syracuseStep 7062815 = 10594223) B10594223
theorem B5580089 : Blo 1651525 5580089 := bstep (se 2 (by rfl) ⟨2092533, by rfl⟩ : syracuseStep 5580089 = 4185067) B4185067
theorem B12543659 : Blo 1651525 12543659 := bstep (se 1 (by rfl) ⟨9407744, by rfl⟩ : syracuseStep 12543659 = 18815489) B18815489
theorem B14124739 : Blo 1651525 14124739 := bstep (se 1 (by rfl) ⟨10593554, by rfl⟩ : syracuseStep 14124739 = 21187109) B21187109
theorem B9537263 : Blo 1651525 9537263 := bstep (se 1 (by rfl) ⟨7152947, by rfl⟩ : syracuseStep 9537263 = 14305895) B14305895
theorem B45246275 : Blo 1651525 45246275 := bstep (se 1 (by rfl) ⟨33934706, by rfl⟩ : syracuseStep 45246275 = 67869413) B67869413
theorem B18827153 : Blo 1651525 18827153 := bstep (se 2 (by rfl) ⟨7060182, by rfl⟩ : syracuseStep 18827153 = 14120365) B14120365
theorem B7645117 : Blo 1651525 7645117 := bstep (se 3 (by rfl) ⟨1433459, by rfl⟩ : syracuseStep 7645117 = 2866919) B2866919
theorem B40732739 : Blo 1651525 40732739 := bstep (se 1 (by rfl) ⟨30549554, by rfl⟩ : syracuseStep 40732739 = 61099109) B61099109
theorem B7538771 : Blo 1651525 7538771 := bstep (se 1 (by rfl) ⟨5654078, by rfl⟩ : syracuseStep 7538771 = 11308157) B11308157
theorem B12552407 : Blo 1651525 12552407 := bstep (se 1 (by rfl) ⟨9414305, by rfl⟩ : syracuseStep 12552407 = 18828611) B18828611
theorem B2648351 : Blo 1651525 2648351 := bstep (se 1 (by rfl) ⟨1986263, by rfl⟩ : syracuseStep 2648351 = 3972527) B3972527
theorem B7055657 : Blo 1651525 7055657 := bstep (se 2 (by rfl) ⟨2645871, by rfl⟩ : syracuseStep 7055657 = 5291743) B5291743
theorem B7055981 : Blo 1651525 7055981 := bstep (se 3 (by rfl) ⟨1322996, by rfl⟩ : syracuseStep 7055981 = 2645993) B2645993
theorem B40192823 : Blo 1651525 40192823 := bstep (se 1 (by rfl) ⟨30144617, by rfl⟩ : syracuseStep 40192823 = 60289235) B60289235
theorem B4181179 : Blo 1651525 4181179 := bstep (se 1 (by rfl) ⟨3135884, by rfl⟩ : syracuseStep 4181179 = 6271769) B6271769
theorem B7941401 : Blo 1651525 7941401 := bstep (se 2 (by rfl) ⟨2978025, by rfl⟩ : syracuseStep 7941401 = 5956051) B5956051
theorem B4705627 : Blo 1651525 4705627 := bstep (se 1 (by rfl) ⟨3529220, by rfl⟩ : syracuseStep 4705627 = 7058441) B7058441
theorem B2477519 : Blo 1651525 2477519 := bstep (se 1 (by rfl) ⟨1858139, by rfl⟩ : syracuseStep 2477519 = 3716279) B3716279
theorem B2477609 : Blo 1651525 2477609 := bstep (se 2 (by rfl) ⟨929103, by rfl⟩ : syracuseStep 2477609 = 1858207) B1858207
theorem B15879725 : Blo 1651525 15879725 := bstep (se 3 (by rfl) ⟨2977448, by rfl⟩ : syracuseStep 15879725 = 5954897) B5954897
theorem B5295881 : Blo 1651525 5295881 := bstep (se 2 (by rfl) ⟨1985955, by rfl⟩ : syracuseStep 5295881 = 3971911) B3971911
theorem B2477903 : Blo 1651525 2477903 := bstep (se 1 (by rfl) ⟨1858427, by rfl⟩ : syracuseStep 2477903 = 3716855) B3716855
theorem B16969661 : Blo 1651525 16969661 := bstep (se 3 (by rfl) ⟨3181811, by rfl⟩ : syracuseStep 16969661 = 6363623) B6363623
theorem B2478023 : Blo 1651525 2478023 := bstep (se 1 (by rfl) ⟨1858517, by rfl⟩ : syracuseStep 2478023 = 3717035) B3717035
theorem B8368109 : Blo 1651525 8368109 := bstep (se 3 (by rfl) ⟨1569020, by rfl⟩ : syracuseStep 8368109 = 3138041) B3138041
theorem B2478107 : Blo 1651525 2478107 := bstep (se 1 (by rfl) ⟨1858580, by rfl⟩ : syracuseStep 2478107 = 3717161) B3717161
theorem B2478383 : Blo 1651525 2478383 := bstep (se 1 (by rfl) ⟨1858787, by rfl⟩ : syracuseStep 2478383 = 3717575) B3717575
theorem B2478491 : Blo 1651525 2478491 := bstep (se 1 (by rfl) ⟨1858868, by rfl⟩ : syracuseStep 2478491 = 3717737) B3717737
theorem B2478527 : Blo 1651525 2478527 := bstep (se 1 (by rfl) ⟨1858895, by rfl⟩ : syracuseStep 2478527 = 3717791) B3717791
theorem B5575175 : Blo 1651525 5575175 := bstep (se 1 (by rfl) ⟨4181381, by rfl⟩ : syracuseStep 5575175 = 8362763) B8362763
theorem B2478623 : Blo 1651525 2478623 := bstep (se 1 (by rfl) ⟨1858967, by rfl⟩ : syracuseStep 2478623 = 3717935) B3717935
theorem B5296907 : Blo 1651525 5296907 := bstep (se 1 (by rfl) ⟨3972680, by rfl⟩ : syracuseStep 5296907 = 7945361) B7945361
theorem B2478911 : Blo 1651525 2478911 := bstep (se 1 (by rfl) ⟨1859183, by rfl⟩ : syracuseStep 2478911 = 3718367) B3718367
theorem B9409385 : Blo 1651525 9409385 := bstep (se 2 (by rfl) ⟨3528519, by rfl⟩ : syracuseStep 9409385 = 7057039) B7057039
theorem B3716009 : Blo 1651525 3716009 := bstep (se 2 (by rfl) ⟨1393503, by rfl⟩ : syracuseStep 3716009 = 2787007) B2787007
theorem B2479055 : Blo 1651525 2479055 := bstep (se 1 (by rfl) ⟨1859291, by rfl⟩ : syracuseStep 2479055 = 3718583) B3718583
theorem B5297177 : Blo 1651525 5297177 := bstep (se 2 (by rfl) ⟨1986441, by rfl⟩ : syracuseStep 5297177 = 3972883) B3972883
theorem B2479145 : Blo 1651525 2479145 := bstep (se 2 (by rfl) ⟨929679, by rfl⟩ : syracuseStep 2479145 = 1859359) B1859359
theorem B42357815 : Blo 1651525 42357815 := bstep (se 1 (by rfl) ⟨31768361, by rfl⟩ : syracuseStep 42357815 = 63536723) B63536723
theorem B2479175 : Blo 1651525 2479175 := bstep (se 1 (by rfl) ⟨1859381, by rfl⟩ : syracuseStep 2479175 = 3718763) B3718763
theorem B8361143 : Blo 1651525 8361143 := bstep (se 1 (by rfl) ⟨6270857, by rfl⟩ : syracuseStep 8361143 = 12541715) B12541715
theorem B2479355 : Blo 1651525 2479355 := bstep (se 1 (by rfl) ⟨1859516, by rfl⟩ : syracuseStep 2479355 = 3719033) B3719033
theorem B1651967 : Blo 1651525 1651967 := bstep (se 1 (by rfl) ⟨1238975, by rfl⟩ : syracuseStep 1651967 = 2477951) B2477951
theorem B2479415 : Blo 1651525 2479415 := bstep (se 1 (by rfl) ⟨1859561, by rfl⟩ : syracuseStep 2479415 = 3719123) B3719123
theorem B10728791 : Blo 1651525 10728791 := bstep (se 1 (by rfl) ⟨8046593, by rfl⟩ : syracuseStep 10728791 = 16093187) B16093187
theorem B1652095 : Blo 1651525 1652095 := bstep (se 1 (by rfl) ⟨1239071, by rfl⟩ : syracuseStep 1652095 = 2478143) B2478143
theorem B5576093 : Blo 1651525 5576093 := bstep (se 3 (by rfl) ⟨1045517, by rfl⟩ : syracuseStep 5576093 = 2091035) B2091035
theorem B17872301 : Blo 1651525 17872301 := bstep (se 3 (by rfl) ⟨3351056, by rfl⟩ : syracuseStep 17872301 = 6702113) B6702113
theorem B5576147 : Blo 1651525 5576147 := bstep (se 1 (by rfl) ⟨4182110, by rfl⟩ : syracuseStep 5576147 = 8364221) B8364221
theorem B42939877 : Blo 1651525 42939877 := bstep (se 4 (by rfl) ⟨4025613, by rfl⟩ : syracuseStep 42939877 = 8051227) B8051227
theorem B1652251 : Blo 1651525 1652251 := bstep (se 1 (by rfl) ⟨1239188, by rfl⟩ : syracuseStep 1652251 = 2478377) B2478377
theorem B5576255 : Blo 1651525 5576255 := bstep (se 1 (by rfl) ⟨4182191, by rfl⟩ : syracuseStep 5576255 = 8364383) B8364383
theorem B2479721 : Blo 1651525 2479721 := bstep (se 2 (by rfl) ⟨929895, by rfl⟩ : syracuseStep 2479721 = 1859791) B1859791
theorem B4183721 : Blo 1651525 4183721 := bstep (se 2 (by rfl) ⟨1568895, by rfl⟩ : syracuseStep 4183721 = 3137791) B3137791
theorem B1652431 : Blo 1651525 1652431 := bstep (se 1 (by rfl) ⟨1239323, by rfl⟩ : syracuseStep 1652431 = 2478647) B2478647
theorem B2234233 : Blo 1651525 2234233 := bstep (se 2 (by rfl) ⟨837837, by rfl⟩ : syracuseStep 2234233 = 1675675) B1675675
theorem B1652671 : Blo 1651525 1652671 := bstep (se 1 (by rfl) ⟨1239503, by rfl⟩ : syracuseStep 1652671 = 2479007) B2479007
theorem B1652799 : Blo 1651525 1652799 := bstep (se 1 (by rfl) ⟨1239599, by rfl⟩ : syracuseStep 1652799 = 2479199) B2479199
theorem B1652839 : Blo 1651525 1652839 := bstep (se 1 (by rfl) ⟨1239629, by rfl⟩ : syracuseStep 1652839 = 2479259) B2479259
theorem B2480255 : Blo 1651525 2480255 := bstep (se 1 (by rfl) ⟨1860191, by rfl⟩ : syracuseStep 2480255 = 3720383) B3720383
theorem B3135763 : Blo 1651525 3135763 := bstep (se 1 (by rfl) ⟨2351822, by rfl⟩ : syracuseStep 3135763 = 4703645) B4703645
theorem B12548519 : Blo 1651525 12548519 := bstep (se 1 (by rfl) ⟨9411389, by rfl⟩ : syracuseStep 12548519 = 18822779) B18822779
theorem B9181723 : Blo 1651525 9181723 := bstep (se 1 (by rfl) ⟨6886292, by rfl⟩ : syracuseStep 9181723 = 13772585) B13772585
theorem B1653295 : Blo 1651525 1653295 := bstep (se 1 (by rfl) ⟨1239971, by rfl⟩ : syracuseStep 1653295 = 2479943) B2479943
theorem B8362601 : Blo 1651525 8362601 := bstep (se 2 (by rfl) ⟨3135975, by rfl⟩ : syracuseStep 8362601 = 6271951) B6271951
theorem B7060115 : Blo 1651525 7060115 := bstep (se 1 (by rfl) ⟨5295086, by rfl⟩ : syracuseStep 7060115 = 10590173) B10590173
theorem B23821199 : Blo 1651525 23821199 := bstep (se 1 (by rfl) ⟨17865899, by rfl⟩ : syracuseStep 23821199 = 35731799) B35731799
theorem B10583099 : Blo 1651525 10583099 := bstep (se 1 (by rfl) ⟨7937324, by rfl⟩ : syracuseStep 10583099 = 15874649) B15874649
theorem B4185179 : Blo 1651525 4185179 := bstep (se 1 (by rfl) ⟨3138884, by rfl⟩ : syracuseStep 4185179 = 6277769) B6277769
theorem B3718313 : Blo 1651525 3718313 := bstep (se 2 (by rfl) ⟨1394367, by rfl⟩ : syracuseStep 3718313 = 2788735) B2788735
theorem B35749097 : Blo 1651525 35749097 := bstep (se 2 (by rfl) ⟨13405911, by rfl⟩ : syracuseStep 35749097 = 26811823) B26811823
theorem B5578091 : Blo 1651525 5578091 := bstep (se 1 (by rfl) ⟨4183568, by rfl⟩ : syracuseStep 5578091 = 8367137) B8367137
theorem B9534995 : Blo 1651525 9534995 := bstep (se 1 (by rfl) ⟨7151246, by rfl⟩ : syracuseStep 9534995 = 14302493) B14302493
theorem B7061039 : Blo 1651525 7061039 := bstep (se 1 (by rfl) ⟨5295779, by rfl⟩ : syracuseStep 7061039 = 10591559) B10591559
theorem B28221047 : Blo 1651525 28221047 := bstep (se 1 (by rfl) ⟨21165785, by rfl⟩ : syracuseStep 28221047 = 42331571) B42331571
theorem B3972737 : Blo 1651525 3972737 := bstep (se 2 (by rfl) ⟨1489776, by rfl⟩ : syracuseStep 3972737 = 2979553) B2979553
theorem B3137449 : Blo 1651525 3137449 := bstep (se 2 (by rfl) ⟨1176543, by rfl⟩ : syracuseStep 3137449 = 2353087) B2353087
theorem B193184135 : Blo 1651525 193184135 := bstep (se 1 (by rfl) ⟨144888101, by rfl⟩ : syracuseStep 193184135 = 289776203) B289776203
theorem B3531271 : Blo 1651525 3531271 := bstep (se 1 (by rfl) ⟨2648453, by rfl⟩ : syracuseStep 3531271 = 5296907) B5296907
theorem B3531451 : Blo 1651525 3531451 := bstep (se 1 (by rfl) ⟨2648588, by rfl⟩ : syracuseStep 3531451 = 5297177) B5297177
theorem B28238543 : Blo 1651525 28238543 := bstep (se 1 (by rfl) ⟨21178907, by rfl⟩ : syracuseStep 28238543 = 42357815) B42357815
theorem B3720059 : Blo 1651525 3720059 := bstep (se 1 (by rfl) ⟨2790044, by rfl⟩ : syracuseStep 3720059 = 5580089) B5580089
theorem B7152527 : Blo 1651525 7152527 := bstep (se 1 (by rfl) ⟨5364395, by rfl⟩ : syracuseStep 7152527 = 10728791) B10728791
theorem B6358175 : Blo 1651525 6358175 := bstep (se 1 (by rfl) ⟨4768631, by rfl⟩ : syracuseStep 6358175 = 9537263) B9537263
theorem B30164183 : Blo 1651525 30164183 := bstep (se 1 (by rfl) ⟨22623137, by rfl⟩ : syracuseStep 30164183 = 45246275) B45246275
theorem B12551435 : Blo 1651525 12551435 := bstep (se 1 (by rfl) ⟨9413576, by rfl⟩ : syracuseStep 12551435 = 18827153) B18827153
theorem B4703771 : Blo 1651525 4703771 := bstep (se 1 (by rfl) ⟨3527828, by rfl⟩ : syracuseStep 4703771 = 7055657) B7055657
theorem B8365679 : Blo 1651525 8365679 := bstep (se 1 (by rfl) ⟨6274259, by rfl⟩ : syracuseStep 8365679 = 12548519) B12548519
theorem B2786953 : Blo 1651525 2786953 := bstep (se 2 (by rfl) ⟨1045107, by rfl⟩ : syracuseStep 2786953 = 2090215) B2090215
theorem B10593965 : Blo 1651525 10593965 := bstep (se 3 (by rfl) ⟨1986368, by rfl⟩ : syracuseStep 10593965 = 3972737) B3972737
theorem B4703987 : Blo 1651525 4703987 := bstep (se 1 (by rfl) ⟨3527990, by rfl⟩ : syracuseStep 4703987 = 7055981) B7055981
theorem B7055399 : Blo 1651525 7055399 := bstep (se 1 (by rfl) ⟨5291549, by rfl⟩ : syracuseStep 7055399 = 10583099) B10583099
theorem B23832731 : Blo 1651525 23832731 := bstep (se 1 (by rfl) ⟨17874548, by rfl⟩ : syracuseStep 23832731 = 35749097) B35749097
theorem B5294267 : Blo 1651525 5294267 := bstep (se 1 (by rfl) ⟨3970700, by rfl⟩ : syracuseStep 5294267 = 7941401) B7941401
theorem B10586483 : Blo 1651525 10586483 := bstep (se 1 (by rfl) ⟨7939862, by rfl⟩ : syracuseStep 10586483 = 15879725) B15879725
theorem B10193489 : Blo 1651525 10193489 := bstep (se 2 (by rfl) ⟨3822558, by rfl⟩ : syracuseStep 10193489 = 7645117) B7645117
theorem B4181017 : Blo 1651525 4181017 := bstep (se 2 (by rfl) ⟨1567881, by rfl⟩ : syracuseStep 4181017 = 3135763) B3135763
theorem B2477339 : Blo 1651525 2477339 := bstep (se 1 (by rfl) ⟨1858004, by rfl⟩ : syracuseStep 2477339 = 3716009) B3716009
theorem B6794543 : Blo 1651525 6794543 := bstep (se 1 (by rfl) ⟨5095907, by rfl⟩ : syracuseStep 6794543 = 10191815) B10191815
theorem B12242297 : Blo 1651525 12242297 := bstep (se 2 (by rfl) ⟨4590861, by rfl⟩ : syracuseStep 12242297 = 9181723) B9181723
theorem B5574095 : Blo 1651525 5574095 := bstep (se 1 (by rfl) ⟨4180571, by rfl⟩ : syracuseStep 5574095 = 8361143) B8361143
theorem B11914867 : Blo 1651525 11914867 := bstep (se 1 (by rfl) ⟨8936150, by rfl⟩ : syracuseStep 11914867 = 17872301) B17872301
theorem B2789147 : Blo 1651525 2789147 := bstep (se 1 (by rfl) ⟨2091860, by rfl⟩ : syracuseStep 2789147 = 4183721) B4183721
theorem B5025847 : Blo 1651525 5025847 := bstep (se 1 (by rfl) ⟨3769385, by rfl⟩ : syracuseStep 5025847 = 7538771) B7538771
theorem B8368271 : Blo 1651525 8368271 := bstep (se 1 (by rfl) ⟨6276203, by rfl⟩ : syracuseStep 8368271 = 12552407) B12552407
theorem B1765567 : Blo 1651525 1765567 := bstep (se 1 (by rfl) ⟨1324175, by rfl⟩ : syracuseStep 1765567 = 2648351) B2648351
theorem B5574905 : Blo 1651525 5574905 := bstep (se 2 (by rfl) ⟨2090589, by rfl⟩ : syracuseStep 5574905 = 4181179) B4181179
theorem B5575067 : Blo 1651525 5575067 := bstep (se 1 (by rfl) ⟨4181300, by rfl⟩ : syracuseStep 5575067 = 8362601) B8362601
theorem B4706743 : Blo 1651525 4706743 := bstep (se 1 (by rfl) ⟨3530057, by rfl⟩ : syracuseStep 4706743 = 7060115) B7060115
theorem B15880799 : Blo 1651525 15880799 := bstep (se 1 (by rfl) ⟨11910599, by rfl⟩ : syracuseStep 15880799 = 23821199) B23821199
theorem B2790119 : Blo 1651525 2790119 := bstep (se 1 (by rfl) ⟨2092589, by rfl⟩ : syracuseStep 2790119 = 4185179) B4185179
theorem B2478875 : Blo 1651525 2478875 := bstep (se 1 (by rfl) ⟨1859156, by rfl⟩ : syracuseStep 2478875 = 3718313) B3718313
theorem B1651679 : Blo 1651525 1651679 := bstep (se 1 (by rfl) ⟨1238759, by rfl⟩ : syracuseStep 1651679 = 2477519) B2477519
theorem B1651739 : Blo 1651525 1651739 := bstep (se 1 (by rfl) ⟨1238804, by rfl⟩ : syracuseStep 1651739 = 2477609) B2477609
theorem B4707359 : Blo 1651525 4707359 := bstep (se 1 (by rfl) ⟨3530519, by rfl⟩ : syracuseStep 4707359 = 7061039) B7061039
theorem B18814031 : Blo 1651525 18814031 := bstep (se 1 (by rfl) ⟨14110523, by rfl⟩ : syracuseStep 18814031 = 28221047) B28221047
theorem B2978977 : Blo 1651525 2978977 := bstep (se 2 (by rfl) ⟨1117116, by rfl⟩ : syracuseStep 2978977 = 2234233) B2234233
theorem B1651935 : Blo 1651525 1651935 := bstep (se 1 (by rfl) ⟨1238951, by rfl⟩ : syracuseStep 1651935 = 2477903) B2477903
theorem B4183265 : Blo 1651525 4183265 := bstep (se 2 (by rfl) ⟨1568724, by rfl⟩ : syracuseStep 4183265 = 3137449) B3137449
theorem B1652015 : Blo 1651525 1652015 := bstep (se 1 (by rfl) ⟨1239011, by rfl⟩ : syracuseStep 1652015 = 2478023) B2478023
theorem B1652071 : Blo 1651525 1652071 := bstep (se 1 (by rfl) ⟨1239053, by rfl⟩ : syracuseStep 1652071 = 2478107) B2478107
theorem B2479529 : Blo 1651525 2479529 := bstep (se 2 (by rfl) ⟨929823, by rfl⟩ : syracuseStep 2479529 = 1859647) B1859647
theorem B2479583 : Blo 1651525 2479583 := bstep (se 1 (by rfl) ⟨1859687, by rfl⟩ : syracuseStep 2479583 = 3719375) B3719375
theorem B1652255 : Blo 1651525 1652255 := bstep (se 1 (by rfl) ⟨1239191, by rfl⟩ : syracuseStep 1652255 = 2478383) B2478383
theorem B1652327 : Blo 1651525 1652327 := bstep (se 1 (by rfl) ⟨1239245, by rfl⟩ : syracuseStep 1652327 = 2478491) B2478491
theorem B1652351 : Blo 1651525 1652351 := bstep (se 1 (by rfl) ⟨1239263, by rfl⟩ : syracuseStep 1652351 = 2478527) B2478527
theorem B3716783 : Blo 1651525 3716783 := bstep (se 1 (by rfl) ⟨2787587, by rfl⟩ : syracuseStep 3716783 = 5575175) B5575175
theorem B1652415 : Blo 1651525 1652415 := bstep (se 1 (by rfl) ⟨1239311, by rfl⟩ : syracuseStep 1652415 = 2478623) B2478623
theorem B14112575 : Blo 1651525 14112575 := bstep (se 1 (by rfl) ⟨10584431, by rfl⟩ : syracuseStep 14112575 = 21168863) B21168863
theorem B1652607 : Blo 1651525 1652607 := bstep (se 1 (by rfl) ⟨1239455, by rfl⟩ : syracuseStep 1652607 = 2478911) B2478911
theorem B6272923 : Blo 1651525 6272923 := bstep (se 1 (by rfl) ⟨4704692, by rfl⟩ : syracuseStep 6272923 = 9409385) B9409385
theorem B1652703 : Blo 1651525 1652703 := bstep (se 1 (by rfl) ⟨1239527, by rfl⟩ : syracuseStep 1652703 = 2479055) B2479055
theorem B1652763 : Blo 1651525 1652763 := bstep (se 1 (by rfl) ⟨1239572, by rfl⟩ : syracuseStep 1652763 = 2479145) B2479145
theorem B1652783 : Blo 1651525 1652783 := bstep (se 1 (by rfl) ⟨1239587, by rfl⟩ : syracuseStep 1652783 = 2479175) B2479175
theorem B47667305 : Blo 1651525 47667305 := bstep (se 2 (by rfl) ⟨17875239, by rfl⟩ : syracuseStep 47667305 = 35750479) B35750479
theorem B1652903 : Blo 1651525 1652903 := bstep (se 1 (by rfl) ⟨1239677, by rfl⟩ : syracuseStep 1652903 = 2479355) B2479355
theorem B14112953 : Blo 1651525 14112953 := bstep (se 2 (by rfl) ⟨5292357, by rfl⟩ : syracuseStep 14112953 = 10584715) B10584715
theorem B4708543 : Blo 1651525 4708543 := bstep (se 1 (by rfl) ⟨3531407, by rfl⟩ : syracuseStep 4708543 = 7062815) B7062815
theorem B1652943 : Blo 1651525 1652943 := bstep (se 1 (by rfl) ⟨1239707, by rfl⟩ : syracuseStep 1652943 = 2479415) B2479415
theorem B3717395 : Blo 1651525 3717395 := bstep (se 1 (by rfl) ⟨2788046, by rfl⟩ : syracuseStep 3717395 = 5576093) B5576093
theorem B3717431 : Blo 1651525 3717431 := bstep (se 1 (by rfl) ⟨2788073, by rfl⟩ : syracuseStep 3717431 = 5576147) B5576147
theorem B3717503 : Blo 1651525 3717503 := bstep (se 1 (by rfl) ⟨2788127, by rfl⟩ : syracuseStep 3717503 = 5576255) B5576255
theorem B1653147 : Blo 1651525 1653147 := bstep (se 1 (by rfl) ⟨1239860, by rfl⟩ : syracuseStep 1653147 = 2479721) B2479721
theorem B8362439 : Blo 1651525 8362439 := bstep (se 1 (by rfl) ⟨6271829, by rfl⟩ : syracuseStep 8362439 = 12543659) B12543659
theorem B27155159 : Blo 1651525 27155159 := bstep (se 1 (by rfl) ⟨20366369, by rfl⟩ : syracuseStep 27155159 = 40732739) B40732739
theorem B1653503 : Blo 1651525 1653503 := bstep (se 1 (by rfl) ⟨1240127, by rfl⟩ : syracuseStep 1653503 = 2480255) B2480255
theorem B6274169 : Blo 1651525 6274169 := bstep (se 2 (by rfl) ⟨2352813, by rfl⟩ : syracuseStep 6274169 = 4705627) B4705627
theorem B26795215 : Blo 1651525 26795215 := bstep (se 1 (by rfl) ⟨20096411, by rfl⟩ : syracuseStep 26795215 = 40192823) B40192823
theorem B57253169 : Blo 1651525 57253169 := bstep (se 2 (by rfl) ⟨21469938, by rfl⟩ : syracuseStep 57253169 = 42939877) B42939877
theorem B14122349 : Blo 1651525 14122349 := bstep (se 3 (by rfl) ⟨2647940, by rfl⟩ : syracuseStep 14122349 = 5295881) B5295881
theorem B3718727 : Blo 1651525 3718727 := bstep (se 1 (by rfl) ⟨2789045, by rfl⟩ : syracuseStep 3718727 = 5578091) B5578091
theorem B18832985 : Blo 1651525 18832985 := bstep (se 2 (by rfl) ⟨7062369, by rfl⟩ : syracuseStep 18832985 = 14124739) B14124739
theorem B6356663 : Blo 1651525 6356663 := bstep (se 1 (by rfl) ⟨4767497, by rfl⟩ : syracuseStep 6356663 = 9534995) B9534995
theorem B11313107 : Blo 1651525 11313107 := bstep (se 1 (by rfl) ⟨8484830, by rfl⟩ : syracuseStep 11313107 = 16969661) B16969661
theorem B5578739 : Blo 1651525 5578739 := bstep (se 1 (by rfl) ⟨4184054, by rfl⟩ : syracuseStep 5578739 = 8368109) B8368109
theorem B6701129 : Blo 1651525 6701129 := bstep (se 2 (by rfl) ⟨2512923, by rfl⟩ : syracuseStep 6701129 = 5025847) B5025847
theorem B5578847 : Blo 1651525 5578847 := bstep (se 1 (by rfl) ⟨4184135, by rfl⟩ : syracuseStep 5578847 = 8368271) B8368271
theorem B18825695 : Blo 1651525 18825695 := bstep (se 1 (by rfl) ⟨14119271, by rfl⟩ : syracuseStep 18825695 = 28238543) B28238543
theorem B1860079 : Blo 1651525 1860079 := bstep (se 1 (by rfl) ⟨1395059, by rfl⟩ : syracuseStep 1860079 = 2790119) B2790119
theorem B6275657 : Blo 1651525 6275657 := bstep (se 2 (by rfl) ⟨2353371, by rfl⟩ : syracuseStep 6275657 = 4706743) B4706743
theorem B4768351 : Blo 1651525 4768351 := bstep (se 1 (by rfl) ⟨3576263, by rfl⟩ : syracuseStep 4768351 = 7152527) B7152527
theorem B3138239 : Blo 1651525 3138239 := bstep (se 1 (by rfl) ⟨2353679, by rfl⟩ : syracuseStep 3138239 = 4707359) B4707359
theorem B12542687 : Blo 1651525 12542687 := bstep (se 1 (by rfl) ⟨9407015, by rfl⟩ : syracuseStep 12542687 = 18814031) B18814031
theorem B32646125 : Blo 1651525 32646125 := bstep (se 3 (by rfl) ⟨6121148, by rfl⟩ : syracuseStep 32646125 = 12242297) B12242297
theorem B7062643 : Blo 1651525 7062643 := bstep (se 1 (by rfl) ⟨5296982, by rfl⟩ : syracuseStep 7062643 = 10593965) B10593965
theorem B4703599 : Blo 1651525 4703599 := bstep (se 1 (by rfl) ⟨3527699, by rfl⟩ : syracuseStep 4703599 = 7055399) B7055399
theorem B31778203 : Blo 1651525 31778203 := bstep (se 1 (by rfl) ⟨23833652, by rfl⟩ : syracuseStep 31778203 = 47667305) B47667305
theorem B3719159 : Blo 1651525 3719159 := bstep (se 1 (by rfl) ⟨2789369, by rfl⟩ : syracuseStep 3719159 = 5578739) B5578739
theorem B35726953 : Blo 1651525 35726953 := bstep (se 2 (by rfl) ⟨13397607, by rfl⟩ : syracuseStep 35726953 = 26795215) B26795215
theorem B15886489 : Blo 1651525 15886489 := bstep (se 2 (by rfl) ⟨5957433, by rfl⟩ : syracuseStep 15886489 = 11914867) B11914867
theorem B38168779 : Blo 1651525 38168779 := bstep (se 1 (by rfl) ⟨28626584, by rfl⟩ : syracuseStep 38168779 = 57253169) B57253169
theorem B9414899 : Blo 1651525 9414899 := bstep (se 1 (by rfl) ⟨7061174, by rfl⟩ : syracuseStep 9414899 = 14122349) B14122349
theorem B4237775 : Blo 1651525 4237775 := bstep (se 1 (by rfl) ⟨3178331, by rfl⟩ : syracuseStep 4237775 = 6356663) B6356663
theorem B6278057 : Blo 1651525 6278057 := bstep (se 2 (by rfl) ⟨2354271, by rfl⟩ : syracuseStep 6278057 = 4708543) B4708543
theorem B128789423 : Blo 1651525 128789423 := bstep (se 1 (by rfl) ⟨96592067, by rfl⟩ : syracuseStep 128789423 = 193184135) B193184135
theorem B10587199 : Blo 1651525 10587199 := bstep (se 1 (by rfl) ⟨7940399, by rfl⟩ : syracuseStep 10587199 = 15880799) B15880799
theorem B4238783 : Blo 1651525 4238783 := bstep (se 1 (by rfl) ⟨3179087, by rfl⟩ : syracuseStep 4238783 = 6358175) B6358175
theorem B2788843 : Blo 1651525 2788843 := bstep (se 1 (by rfl) ⟨2091632, by rfl⟩ : syracuseStep 2788843 = 4183265) B4183265
theorem B8367623 : Blo 1651525 8367623 := bstep (se 1 (by rfl) ⟨6275717, by rfl⟩ : syracuseStep 8367623 = 12551435) B12551435
theorem B9416357 : Blo 1651525 9416357 := bstep (se 4 (by rfl) ⟨882783, by rfl⟩ : syracuseStep 9416357 = 1765567) B1765567
theorem B2477855 : Blo 1651525 2477855 := bstep (se 1 (by rfl) ⟨1858391, by rfl⟩ : syracuseStep 2477855 = 3716783) B3716783
theorem B9408383 : Blo 1651525 9408383 := bstep (se 1 (by rfl) ⟨7056287, by rfl⟩ : syracuseStep 9408383 = 14112575) B14112575
theorem B5574689 : Blo 1651525 5574689 := bstep (se 2 (by rfl) ⟨2090508, by rfl⟩ : syracuseStep 5574689 = 4181017) B4181017
theorem B15888487 : Blo 1651525 15888487 := bstep (se 1 (by rfl) ⟨11916365, by rfl⟩ : syracuseStep 15888487 = 23832731) B23832731
theorem B9408635 : Blo 1651525 9408635 := bstep (se 1 (by rfl) ⟨7056476, by rfl⟩ : syracuseStep 9408635 = 14112953) B14112953
theorem B2478263 : Blo 1651525 2478263 := bstep (se 1 (by rfl) ⟨1858697, by rfl⟩ : syracuseStep 2478263 = 3717395) B3717395
theorem B2478287 : Blo 1651525 2478287 := bstep (se 1 (by rfl) ⟨1858715, by rfl⟩ : syracuseStep 2478287 = 3717431) B3717431
theorem B7057655 : Blo 1651525 7057655 := bstep (se 1 (by rfl) ⟨5293241, by rfl⟩ : syracuseStep 7057655 = 10586483) B10586483
theorem B2478335 : Blo 1651525 2478335 := bstep (se 1 (by rfl) ⟨1858751, by rfl⟩ : syracuseStep 2478335 = 3717503) B3717503
theorem B5574959 : Blo 1651525 5574959 := bstep (se 1 (by rfl) ⟨4181219, by rfl⟩ : syracuseStep 5574959 = 8362439) B8362439
theorem B6795659 : Blo 1651525 6795659 := bstep (se 1 (by rfl) ⟨5096744, by rfl⟩ : syracuseStep 6795659 = 10193489) B10193489
theorem B4182779 : Blo 1651525 4182779 := bstep (se 1 (by rfl) ⟨3137084, by rfl⟩ : syracuseStep 4182779 = 6274169) B6274169
theorem B3715937 : Blo 1651525 3715937 := bstep (se 2 (by rfl) ⟨1393476, by rfl⟩ : syracuseStep 3715937 = 2786953) B2786953
theorem B1651559 : Blo 1651525 1651559 := bstep (se 1 (by rfl) ⟨1238669, by rfl⟩ : syracuseStep 1651559 = 2477339) B2477339
theorem B3716063 : Blo 1651525 3716063 := bstep (se 1 (by rfl) ⟨2787047, by rfl⟩ : syracuseStep 3716063 = 5574095) B5574095
theorem B2479151 : Blo 1651525 2479151 := bstep (se 1 (by rfl) ⟨1859363, by rfl⟩ : syracuseStep 2479151 = 3718727) B3718727
theorem B12555323 : Blo 1651525 12555323 := bstep (se 1 (by rfl) ⟨9416492, by rfl⟩ : syracuseStep 12555323 = 18832985) B18832985
theorem B7542071 : Blo 1651525 7542071 := bstep (se 1 (by rfl) ⟨5656553, by rfl⟩ : syracuseStep 7542071 = 11313107) B11313107
theorem B3716603 : Blo 1651525 3716603 := bstep (se 1 (by rfl) ⟨2787452, by rfl⟩ : syracuseStep 3716603 = 5574905) B5574905
theorem B3716711 : Blo 1651525 3716711 := bstep (se 1 (by rfl) ⟨2787533, by rfl⟩ : syracuseStep 3716711 = 5575067) B5575067
theorem B1652583 : Blo 1651525 1652583 := bstep (se 1 (by rfl) ⟨1239437, by rfl⟩ : syracuseStep 1652583 = 2478875) B2478875
theorem B2480039 : Blo 1651525 2480039 := bstep (se 1 (by rfl) ⟨1860029, by rfl⟩ : syracuseStep 2480039 = 3720059) B3720059
theorem B4708361 : Blo 1651525 4708361 := bstep (se 2 (by rfl) ⟨1765635, by rfl⟩ : syracuseStep 4708361 = 3531271) B3531271
theorem B20109455 : Blo 1651525 20109455 := bstep (se 1 (by rfl) ⟨15082091, by rfl⟩ : syracuseStep 20109455 = 30164183) B30164183
theorem B4708601 : Blo 1651525 4708601 := bstep (se 2 (by rfl) ⟨1765725, by rfl⟩ : syracuseStep 4708601 = 3531451) B3531451
theorem B1653019 : Blo 1651525 1653019 := bstep (se 1 (by rfl) ⟨1239764, by rfl⟩ : syracuseStep 1653019 = 2479529) B2479529
theorem B1653055 : Blo 1651525 1653055 := bstep (se 1 (by rfl) ⟨1239791, by rfl⟩ : syracuseStep 1653055 = 2479583) B2479583
theorem B3135847 : Blo 1651525 3135847 := bstep (se 1 (by rfl) ⟨2351885, by rfl⟩ : syracuseStep 3135847 = 4703771) B4703771
theorem B5577119 : Blo 1651525 5577119 := bstep (se 1 (by rfl) ⟨4182839, by rfl⟩ : syracuseStep 5577119 = 8365679) B8365679
theorem B3135991 : Blo 1651525 3135991 := bstep (se 1 (by rfl) ⟨2351993, by rfl⟩ : syracuseStep 3135991 = 4703987) B4703987
theorem B3529511 : Blo 1651525 3529511 := bstep (se 1 (by rfl) ⟨2647133, by rfl⟩ : syracuseStep 3529511 = 5294267) B5294267
theorem B3971969 : Blo 1651525 3971969 := bstep (se 2 (by rfl) ⟨1489488, by rfl⟩ : syracuseStep 3971969 = 2978977) B2978977
theorem B18103439 : Blo 1651525 18103439 := bstep (se 1 (by rfl) ⟨13577579, by rfl⟩ : syracuseStep 18103439 = 27155159) B27155159
theorem B4529695 : Blo 1651525 4529695 := bstep (se 1 (by rfl) ⟨3397271, by rfl⟩ : syracuseStep 4529695 = 6794543) B6794543
theorem B1859431 : Blo 1651525 1859431 := bstep (se 1 (by rfl) ⟨1394573, by rfl⟩ : syracuseStep 1859431 = 2789147) B2789147
theorem B8363897 : Blo 1651525 8363897 := bstep (se 2 (by rfl) ⟨3136461, by rfl⟩ : syracuseStep 8363897 = 6272923) B6272923
theorem B3719231 : Blo 1651525 3719231 := bstep (se 1 (by rfl) ⟨2789423, by rfl⟩ : syracuseStep 3719231 = 5578847) B5578847
theorem B21184649 : Blo 1651525 21184649 := bstep (se 2 (by rfl) ⟨7944243, by rfl⟩ : syracuseStep 21184649 = 15888487) B15888487
theorem B4530439 : Blo 1651525 4530439 := bstep (se 1 (by rfl) ⟨3397829, by rfl⟩ : syracuseStep 4530439 = 6795659) B6795659
theorem B12550463 : Blo 1651525 12550463 := bstep (se 1 (by rfl) ⟨9412847, by rfl⟩ : syracuseStep 12550463 = 18825695) B18825695
theorem B48275837 : Blo 1651525 48275837 := bstep (se 3 (by rfl) ⟨9051719, by rfl⟩ : syracuseStep 48275837 = 18103439) B18103439
theorem B3138907 : Blo 1651525 3138907 := bstep (se 1 (by rfl) ⟨2354180, by rfl⟩ : syracuseStep 3138907 = 4708361) B4708361
theorem B14116265 : Blo 1651525 14116265 := bstep (se 2 (by rfl) ⟨5293599, by rfl⟩ : syracuseStep 14116265 = 10587199) B10587199
theorem B6276599 : Blo 1651525 6276599 := bstep (se 1 (by rfl) ⟨4707449, by rfl⟩ : syracuseStep 6276599 = 9414899) B9414899
theorem B3139067 : Blo 1651525 3139067 := bstep (se 1 (by rfl) ⟨2354300, by rfl⟩ : syracuseStep 3139067 = 4708601) B4708601
theorem B2353007 : Blo 1651525 2353007 := bstep (se 1 (by rfl) ⟨1764755, by rfl⟩ : syracuseStep 2353007 = 3529511) B3529511
theorem B42370937 : Blo 1651525 42370937 := bstep (se 2 (by rfl) ⟨15889101, by rfl⟩ : syracuseStep 42370937 = 31778203) B31778203
theorem B2647979 : Blo 1651525 2647979 := bstep (se 1 (by rfl) ⟨1985984, by rfl⟩ : syracuseStep 2647979 = 3971969) B3971969
theorem B6039593 : Blo 1651525 6039593 := bstep (se 2 (by rfl) ⟨2264847, by rfl⟩ : syracuseStep 6039593 = 4529695) B4529695
theorem B6277571 : Blo 1651525 6277571 := bstep (se 1 (by rfl) ⟨4708178, by rfl⟩ : syracuseStep 6277571 = 9416357) B9416357
theorem B4467419 : Blo 1651525 4467419 := bstep (se 1 (by rfl) ⟨3350564, by rfl⟩ : syracuseStep 4467419 = 6701129) B6701129
theorem B4705103 : Blo 1651525 4705103 := bstep (se 1 (by rfl) ⟨3528827, by rfl⟩ : syracuseStep 4705103 = 7057655) B7057655
theorem B50891705 : Blo 1651525 50891705 := bstep (se 2 (by rfl) ⟨19084389, by rfl⟩ : syracuseStep 50891705 = 38168779) B38168779
theorem B2092159 : Blo 1651525 2092159 := bstep (se 1 (by rfl) ⟨1569119, by rfl⟩ : syracuseStep 2092159 = 3138239) B3138239
theorem B4181129 : Blo 1651525 4181129 := bstep (se 2 (by rfl) ⟨1567923, by rfl⟩ : syracuseStep 4181129 = 3135847) B3135847
theorem B2788519 : Blo 1651525 2788519 := bstep (se 1 (by rfl) ⟨2091389, by rfl⟩ : syracuseStep 2788519 = 4182779) B4182779
theorem B2477291 : Blo 1651525 2477291 := bstep (se 1 (by rfl) ⟨1857968, by rfl⟩ : syracuseStep 2477291 = 3715937) B3715937
theorem B2477375 : Blo 1651525 2477375 := bstep (se 1 (by rfl) ⟨1858031, by rfl⟩ : syracuseStep 2477375 = 3716063) B3716063
theorem B4181321 : Blo 1651525 4181321 := bstep (se 2 (by rfl) ⟨1567995, by rfl⟩ : syracuseStep 4181321 = 3135991) B3135991
theorem B2477735 : Blo 1651525 2477735 := bstep (se 1 (by rfl) ⟨1858301, by rfl⟩ : syracuseStep 2477735 = 3716603) B3716603
theorem B2477807 : Blo 1651525 2477807 := bstep (se 1 (by rfl) ⟨1858355, by rfl⟩ : syracuseStep 2477807 = 3716711) B3716711
theorem B13406303 : Blo 1651525 13406303 := bstep (se 1 (by rfl) ⟨10054727, by rfl⟩ : syracuseStep 13406303 = 20109455) B20109455
theorem B9416857 : Blo 1651525 9416857 := bstep (se 2 (by rfl) ⟨3531321, by rfl⟩ : syracuseStep 9416857 = 7062643) B7062643
theorem B6271465 : Blo 1651525 6271465 := bstep (se 2 (by rfl) ⟨2351799, by rfl⟩ : syracuseStep 6271465 = 4703599) B4703599
theorem B101724821 : Blo 1651525 101724821 := bstep (se 6 (by rfl) ⟨2384175, by rfl⟩ : syracuseStep 101724821 = 4768351) B4768351
theorem B2479241 : Blo 1651525 2479241 := bstep (se 2 (by rfl) ⟨929715, by rfl⟩ : syracuseStep 2479241 = 1859431) B1859431
theorem B1651903 : Blo 1651525 1651903 := bstep (se 1 (by rfl) ⟨1238927, by rfl⟩ : syracuseStep 1651903 = 2477855) B2477855
theorem B5575931 : Blo 1651525 5575931 := bstep (se 1 (by rfl) ⟨4181948, by rfl⟩ : syracuseStep 5575931 = 8363897) B8363897
theorem B6272255 : Blo 1651525 6272255 := bstep (se 1 (by rfl) ⟨4704191, by rfl⟩ : syracuseStep 6272255 = 9408383) B9408383
theorem B2479439 : Blo 1651525 2479439 := bstep (se 1 (by rfl) ⟨1859579, by rfl⟩ : syracuseStep 2479439 = 3719159) B3719159
theorem B3716459 : Blo 1651525 3716459 := bstep (se 1 (by rfl) ⟨2787344, by rfl⟩ : syracuseStep 3716459 = 5574689) B5574689
theorem B6272423 : Blo 1651525 6272423 := bstep (se 1 (by rfl) ⟨4704317, by rfl⟩ : syracuseStep 6272423 = 9408635) B9408635
theorem B1652175 : Blo 1651525 1652175 := bstep (se 1 (by rfl) ⟨1239131, by rfl⟩ : syracuseStep 1652175 = 2478263) B2478263
theorem B1652191 : Blo 1651525 1652191 := bstep (se 1 (by rfl) ⟨1239143, by rfl⟩ : syracuseStep 1652191 = 2478287) B2478287
theorem B1652223 : Blo 1651525 1652223 := bstep (se 1 (by rfl) ⟨1239167, by rfl⟩ : syracuseStep 1652223 = 2478335) B2478335
theorem B3716639 : Blo 1651525 3716639 := bstep (se 1 (by rfl) ⟨2787479, by rfl⟩ : syracuseStep 3716639 = 5574959) B5574959
theorem B21181985 : Blo 1651525 21181985 := bstep (se 2 (by rfl) ⟨7943244, by rfl⟩ : syracuseStep 21181985 = 15886489) B15886489
theorem B4183771 : Blo 1651525 4183771 := bstep (se 1 (by rfl) ⟨3137828, by rfl⟩ : syracuseStep 4183771 = 6275657) B6275657
theorem B8361791 : Blo 1651525 8361791 := bstep (se 1 (by rfl) ⟨6271343, by rfl⟩ : syracuseStep 8361791 = 12542687) B12542687
theorem B2480105 : Blo 1651525 2480105 := bstep (se 2 (by rfl) ⟨930039, by rfl⟩ : syracuseStep 2480105 = 1860079) B1860079
theorem B1652767 : Blo 1651525 1652767 := bstep (se 1 (by rfl) ⟨1239575, by rfl⟩ : syracuseStep 1652767 = 2479151) B2479151
theorem B8370215 : Blo 1651525 8370215 := bstep (se 1 (by rfl) ⟨6277661, by rfl⟩ : syracuseStep 8370215 = 12555323) B12555323
theorem B5028047 : Blo 1651525 5028047 := bstep (se 1 (by rfl) ⟨3771035, by rfl⟩ : syracuseStep 5028047 = 7542071) B7542071
theorem B1653359 : Blo 1651525 1653359 := bstep (se 1 (by rfl) ⟨1240019, by rfl⟩ : syracuseStep 1653359 = 2480039) B2480039
theorem B3718079 : Blo 1651525 3718079 := bstep (se 1 (by rfl) ⟨2788559, by rfl⟩ : syracuseStep 3718079 = 5577119) B5577119
theorem B2825183 : Blo 1651525 2825183 := bstep (se 1 (by rfl) ⟨2118887, by rfl⟩ : syracuseStep 2825183 = 4237775) B4237775
theorem B4185371 : Blo 1651525 4185371 := bstep (se 1 (by rfl) ⟨3139028, by rfl⟩ : syracuseStep 4185371 = 6278057) B6278057
theorem B85859615 : Blo 1651525 85859615 := bstep (se 1 (by rfl) ⟨64394711, by rfl⟩ : syracuseStep 85859615 = 128789423) B128789423
theorem B3718457 : Blo 1651525 3718457 := bstep (se 2 (by rfl) ⟨1394421, by rfl⟩ : syracuseStep 3718457 = 2788843) B2788843
theorem B47635937 : Blo 1651525 47635937 := bstep (se 2 (by rfl) ⟨17863476, by rfl⟩ : syracuseStep 47635937 = 35726953) B35726953
theorem B2825855 : Blo 1651525 2825855 := bstep (se 1 (by rfl) ⟨2119391, by rfl⟩ : syracuseStep 2825855 = 4238783) B4238783
theorem B5578415 : Blo 1651525 5578415 := bstep (se 1 (by rfl) ⟨4183811, by rfl⟩ : syracuseStep 5578415 = 8367623) B8367623
theorem B87056333 : Blo 1651525 87056333 := bstep (se 3 (by rfl) ⟨16323062, by rfl⟩ : syracuseStep 87056333 = 32646125) B32646125
theorem B8937535 : Blo 1651525 8937535 := bstep (se 1 (by rfl) ⟨6703151, by rfl⟩ : syracuseStep 8937535 = 13406303) B13406303
theorem B14123099 : Blo 1651525 14123099 := bstep (se 1 (by rfl) ⟨10592324, by rfl⟩ : syracuseStep 14123099 = 21184649) B21184649
theorem B28247291 : Blo 1651525 28247291 := bstep (se 1 (by rfl) ⟨21185468, by rfl⟩ : syracuseStep 28247291 = 42370937) B42370937
theorem B5580143 : Blo 1651525 5580143 := bstep (se 1 (by rfl) ⟨4185107, by rfl⟩ : syracuseStep 5580143 = 8370215) B8370215
theorem B3352031 : Blo 1651525 3352031 := bstep (se 1 (by rfl) ⟨2514023, by rfl⟩ : syracuseStep 3352031 = 5028047) B5028047
theorem B2787419 : Blo 1651525 2787419 := bstep (se 1 (by rfl) ⟨2090564, by rfl⟩ : syracuseStep 2787419 = 4181129) B4181129
theorem B57239743 : Blo 1651525 57239743 := bstep (se 1 (by rfl) ⟨42929807, by rfl⟩ : syracuseStep 57239743 = 85859615) B85859615
theorem B2787547 : Blo 1651525 2787547 := bstep (se 1 (by rfl) ⟨2090660, by rfl⟩ : syracuseStep 2787547 = 4181321) B4181321
theorem B8366975 : Blo 1651525 8366975 := bstep (se 1 (by rfl) ⟨6275231, by rfl⟩ : syracuseStep 8366975 = 12550463) B12550463
theorem B6040585 : Blo 1651525 6040585 := bstep (se 2 (by rfl) ⟨2265219, by rfl⟩ : syracuseStep 6040585 = 4530439) B4530439
theorem B67816547 : Blo 1651525 67816547 := bstep (se 1 (by rfl) ⟨50862410, by rfl⟩ : syracuseStep 67816547 = 101724821) B101724821
theorem B4181503 : Blo 1651525 4181503 := bstep (se 1 (by rfl) ⟨3136127, by rfl⟩ : syracuseStep 4181503 = 6272255) B6272255
theorem B2477639 : Blo 1651525 2477639 := bstep (se 1 (by rfl) ⟨1858229, by rfl⟩ : syracuseStep 2477639 = 3716459) B3716459
theorem B4181615 : Blo 1651525 4181615 := bstep (se 1 (by rfl) ⟨3136211, by rfl⟩ : syracuseStep 4181615 = 6272423) B6272423
theorem B2092711 : Blo 1651525 2092711 := bstep (se 1 (by rfl) ⟨1569533, by rfl⟩ : syracuseStep 2092711 = 3139067) B3139067
theorem B2477759 : Blo 1651525 2477759 := bstep (se 1 (by rfl) ⟨1858319, by rfl⟩ : syracuseStep 2477759 = 3716639) B3716639
theorem B5574527 : Blo 1651525 5574527 := bstep (se 1 (by rfl) ⟨4180895, by rfl⟩ : syracuseStep 5574527 = 8361791) B8361791
theorem B1765319 : Blo 1651525 1765319 := bstep (se 1 (by rfl) ⟨1323989, by rfl⟩ : syracuseStep 1765319 = 2647979) B2647979
theorem B4026395 : Blo 1651525 4026395 := bstep (se 1 (by rfl) ⟨3019796, by rfl⟩ : syracuseStep 4026395 = 6039593) B6039593
theorem B2789545 : Blo 1651525 2789545 := bstep (se 2 (by rfl) ⟨1046079, by rfl⟩ : syracuseStep 2789545 = 2092159) B2092159
theorem B2978279 : Blo 1651525 2978279 := bstep (se 1 (by rfl) ⟨2233709, by rfl⟩ : syracuseStep 2978279 = 4467419) B4467419
theorem B33927803 : Blo 1651525 33927803 := bstep (se 1 (by rfl) ⟨25445852, by rfl⟩ : syracuseStep 33927803 = 50891705) B50891705
theorem B2478719 : Blo 1651525 2478719 := bstep (se 1 (by rfl) ⟨1859039, by rfl⟩ : syracuseStep 2478719 = 3718079) B3718079
theorem B1651527 : Blo 1651525 1651527 := bstep (se 1 (by rfl) ⟨1238645, by rfl⟩ : syracuseStep 1651527 = 2477291) B2477291
theorem B2790247 : Blo 1651525 2790247 := bstep (se 1 (by rfl) ⟨2092685, by rfl⟩ : syracuseStep 2790247 = 4185371) B4185371
theorem B2478971 : Blo 1651525 2478971 := bstep (se 1 (by rfl) ⟨1859228, by rfl⟩ : syracuseStep 2478971 = 3718457) B3718457
theorem B1651583 : Blo 1651525 1651583 := bstep (se 1 (by rfl) ⟨1238687, by rfl⟩ : syracuseStep 1651583 = 2477375) B2477375
theorem B31757291 : Blo 1651525 31757291 := bstep (se 1 (by rfl) ⟨23817968, by rfl⟩ : syracuseStep 31757291 = 47635937) B47635937
theorem B1651823 : Blo 1651525 1651823 := bstep (se 1 (by rfl) ⟨1238867, by rfl⟩ : syracuseStep 1651823 = 2477735) B2477735
theorem B1651871 : Blo 1651525 1651871 := bstep (se 1 (by rfl) ⟨1238903, by rfl⟩ : syracuseStep 1651871 = 2477807) B2477807
theorem B58037555 : Blo 1651525 58037555 := bstep (se 1 (by rfl) ⟨43528166, by rfl⟩ : syracuseStep 58037555 = 87056333) B87056333
theorem B2479487 : Blo 1651525 2479487 := bstep (se 1 (by rfl) ⟨1859615, by rfl⟩ : syracuseStep 2479487 = 3719231) B3719231
theorem B12555809 : Blo 1651525 12555809 := bstep (se 2 (by rfl) ⟨4708428, by rfl⟩ : syracuseStep 12555809 = 9416857) B9416857
theorem B32183891 : Blo 1651525 32183891 := bstep (se 1 (by rfl) ⟨24137918, by rfl⟩ : syracuseStep 32183891 = 48275837) B48275837
theorem B8361953 : Blo 1651525 8361953 := bstep (se 2 (by rfl) ⟨3135732, by rfl⟩ : syracuseStep 8361953 = 6271465) B6271465
theorem B1652827 : Blo 1651525 1652827 := bstep (se 1 (by rfl) ⟨1239620, by rfl⟩ : syracuseStep 1652827 = 2479241) B2479241
theorem B3717287 : Blo 1651525 3717287 := bstep (se 1 (by rfl) ⟨2787965, by rfl⟩ : syracuseStep 3717287 = 5575931) B5575931
theorem B1652959 : Blo 1651525 1652959 := bstep (se 1 (by rfl) ⟨1239719, by rfl⟩ : syracuseStep 1652959 = 2479439) B2479439
theorem B9410843 : Blo 1651525 9410843 := bstep (se 1 (by rfl) ⟨7058132, by rfl⟩ : syracuseStep 9410843 = 14116265) B14116265
theorem B4184399 : Blo 1651525 4184399 := bstep (se 1 (by rfl) ⟨3138299, by rfl⟩ : syracuseStep 4184399 = 6276599) B6276599
theorem B14121323 : Blo 1651525 14121323 := bstep (se 1 (by rfl) ⟨10590992, by rfl⟩ : syracuseStep 14121323 = 21181985) B21181985
theorem B1653403 : Blo 1651525 1653403 := bstep (se 1 (by rfl) ⟨1240052, by rfl⟩ : syracuseStep 1653403 = 2480105) B2480105
theorem B3718025 : Blo 1651525 3718025 := bstep (se 2 (by rfl) ⟨1394259, by rfl⟩ : syracuseStep 3718025 = 2788519) B2788519
theorem B4185047 : Blo 1651525 4185047 := bstep (se 1 (by rfl) ⟨3138785, by rfl⟩ : syracuseStep 4185047 = 6277571) B6277571
theorem B4185209 : Blo 1651525 4185209 := bstep (se 2 (by rfl) ⟨1569453, by rfl⟩ : syracuseStep 4185209 = 3138907) B3138907
theorem B3136735 : Blo 1651525 3136735 := bstep (se 1 (by rfl) ⟨2352551, by rfl⟩ : syracuseStep 3136735 = 4705103) B4705103
theorem B1883455 : Blo 1651525 1883455 := bstep (se 1 (by rfl) ⟨1412591, by rfl⟩ : syracuseStep 1883455 = 2825183) B2825183
theorem B5578361 : Blo 1651525 5578361 := bstep (se 2 (by rfl) ⟨2091885, by rfl⟩ : syracuseStep 5578361 = 4183771) B4183771
theorem B6274685 : Blo 1651525 6274685 := bstep (se 3 (by rfl) ⟨1176503, by rfl⟩ : syracuseStep 6274685 = 2353007) B2353007
theorem B1883903 : Blo 1651525 1883903 := bstep (se 1 (by rfl) ⟨1412927, by rfl⟩ : syracuseStep 1883903 = 2825855) B2825855
theorem B3718943 : Blo 1651525 3718943 := bstep (se 1 (by rfl) ⟨2789207, by rfl⟩ : syracuseStep 3718943 = 5578415) B5578415
theorem B3719393 : Blo 1651525 3719393 := bstep (se 2 (by rfl) ⟨1394772, by rfl⟩ : syracuseStep 3719393 = 2789545) B2789545
theorem B22618535 : Blo 1651525 22618535 := bstep (se 1 (by rfl) ⟨16963901, by rfl⟩ : syracuseStep 22618535 = 33927803) B33927803
theorem B38691703 : Blo 1651525 38691703 := bstep (se 1 (by rfl) ⟨29018777, by rfl⟩ : syracuseStep 38691703 = 58037555) B58037555
theorem B3720095 : Blo 1651525 3720095 := bstep (se 1 (by rfl) ⟨2790071, by rfl⟩ : syracuseStep 3720095 = 5580143) B5580143
theorem B21455927 : Blo 1651525 21455927 := bstep (se 1 (by rfl) ⟨16091945, by rfl⟩ : syracuseStep 21455927 = 32183891) B32183891
theorem B3720329 : Blo 1651525 3720329 := bstep (se 2 (by rfl) ⟨1395123, by rfl⟩ : syracuseStep 3720329 = 2790247) B2790247
theorem B9414215 : Blo 1651525 9414215 := bstep (se 1 (by rfl) ⟨7060661, by rfl⟩ : syracuseStep 9414215 = 14121323) B14121323
theorem B10045093 : Blo 1651525 10045093 := bstep (se 4 (by rfl) ⟨941727, by rfl⟩ : syracuseStep 10045093 = 1883455) B1883455
theorem B5023741 : Blo 1651525 5023741 := bstep (se 3 (by rfl) ⟨941951, by rfl⟩ : syracuseStep 5023741 = 1883903) B1883903
theorem B2787743 : Blo 1651525 2787743 := bstep (se 1 (by rfl) ⟨2090807, by rfl⟩ : syracuseStep 2787743 = 4181615) B4181615
theorem B9415399 : Blo 1651525 9415399 := bstep (se 1 (by rfl) ⟨7061549, by rfl⟩ : syracuseStep 9415399 = 14123099) B14123099
theorem B76319657 : Blo 1651525 76319657 := bstep (se 2 (by rfl) ⟨28619871, by rfl⟩ : syracuseStep 76319657 = 57239743) B57239743
theorem B1985519 : Blo 1651525 1985519 := bstep (se 1 (by rfl) ⟨1489139, by rfl⟩ : syracuseStep 1985519 = 2978279) B2978279
theorem B21171527 : Blo 1651525 21171527 := bstep (se 1 (by rfl) ⟨15878645, by rfl⟩ : syracuseStep 21171527 = 31757291) B31757291
theorem B5574635 : Blo 1651525 5574635 := bstep (se 1 (by rfl) ⟨4180976, by rfl⟩ : syracuseStep 5574635 = 8361953) B8361953
theorem B2478191 : Blo 1651525 2478191 := bstep (se 1 (by rfl) ⟨1858643, by rfl⟩ : syracuseStep 2478191 = 3717287) B3717287
theorem B2789599 : Blo 1651525 2789599 := bstep (se 1 (by rfl) ⟨2092199, by rfl⟩ : syracuseStep 2789599 = 4184399) B4184399
theorem B4182313 : Blo 1651525 4182313 := bstep (se 2 (by rfl) ⟨1568367, by rfl⟩ : syracuseStep 4182313 = 3136735) B3136735
theorem B2478683 : Blo 1651525 2478683 := bstep (se 1 (by rfl) ⟨1859012, by rfl⟩ : syracuseStep 2478683 = 3718025) B3718025
theorem B2790031 : Blo 1651525 2790031 := bstep (se 1 (by rfl) ⟨2092523, by rfl⟩ : syracuseStep 2790031 = 4185047) B4185047
theorem B5575337 : Blo 1651525 5575337 := bstep (se 2 (by rfl) ⟨2090751, by rfl⟩ : syracuseStep 5575337 = 4181503) B4181503
theorem B18830069 : Blo 1651525 18830069 := bstep (se 5 (by rfl) ⟨882659, by rfl⟩ : syracuseStep 18830069 = 1765319) B1765319
theorem B2790139 : Blo 1651525 2790139 := bstep (se 1 (by rfl) ⟨2092604, by rfl⟩ : syracuseStep 2790139 = 4185209) B4185209
theorem B2790281 : Blo 1651525 2790281 := bstep (se 2 (by rfl) ⟨1046355, by rfl⟩ : syracuseStep 2790281 = 2092711) B2092711
theorem B1651759 : Blo 1651525 1651759 := bstep (se 1 (by rfl) ⟨1238819, by rfl⟩ : syracuseStep 1651759 = 2477639) B2477639
theorem B4183123 : Blo 1651525 4183123 := bstep (se 1 (by rfl) ⟨3137342, by rfl⟩ : syracuseStep 4183123 = 6274685) B6274685
theorem B1651839 : Blo 1651525 1651839 := bstep (se 1 (by rfl) ⟨1238879, by rfl⟩ : syracuseStep 1651839 = 2477759) B2477759
theorem B2479295 : Blo 1651525 2479295 := bstep (se 1 (by rfl) ⟨1859471, by rfl⟩ : syracuseStep 2479295 = 3718943) B3718943
theorem B3716351 : Blo 1651525 3716351 := bstep (se 1 (by rfl) ⟨2787263, by rfl⟩ : syracuseStep 3716351 = 5574527) B5574527
theorem B2684263 : Blo 1651525 2684263 := bstep (se 1 (by rfl) ⟨2013197, by rfl⟩ : syracuseStep 2684263 = 4026395) B4026395
theorem B32216453 : Blo 1651525 32216453 := bstep (se 4 (by rfl) ⟨3020292, by rfl⟩ : syracuseStep 32216453 = 6040585) B6040585
theorem B11916713 : Blo 1651525 11916713 := bstep (se 2 (by rfl) ⟨4468767, by rfl⟩ : syracuseStep 11916713 = 8937535) B8937535
theorem B3716729 : Blo 1651525 3716729 := bstep (se 2 (by rfl) ⟨1393773, by rfl⟩ : syracuseStep 3716729 = 2787547) B2787547
theorem B1652479 : Blo 1651525 1652479 := bstep (se 1 (by rfl) ⟨1239359, by rfl⟩ : syracuseStep 1652479 = 2478719) B2478719
theorem B1652647 : Blo 1651525 1652647 := bstep (se 1 (by rfl) ⟨1239485, by rfl⟩ : syracuseStep 1652647 = 2478971) B2478971
theorem B18831527 : Blo 1651525 18831527 := bstep (se 1 (by rfl) ⟨14123645, by rfl⟩ : syracuseStep 18831527 = 28247291) B28247291
theorem B1652991 : Blo 1651525 1652991 := bstep (se 1 (by rfl) ⟨1239743, by rfl⟩ : syracuseStep 1652991 = 2479487) B2479487
theorem B2234687 : Blo 1651525 2234687 := bstep (se 1 (by rfl) ⟨1676015, by rfl⟩ : syracuseStep 2234687 = 3352031) B3352031
theorem B8370539 : Blo 1651525 8370539 := bstep (se 1 (by rfl) ⟨6277904, by rfl⟩ : syracuseStep 8370539 = 12555809) B12555809
theorem B1858279 : Blo 1651525 1858279 := bstep (se 1 (by rfl) ⟨1393709, by rfl⟩ : syracuseStep 1858279 = 2787419) B2787419
theorem B6273895 : Blo 1651525 6273895 := bstep (se 1 (by rfl) ⟨4705421, by rfl⟩ : syracuseStep 6273895 = 9410843) B9410843
theorem B5577983 : Blo 1651525 5577983 := bstep (se 1 (by rfl) ⟨4183487, by rfl⟩ : syracuseStep 5577983 = 8366975) B8366975
theorem B45211031 : Blo 1651525 45211031 := bstep (se 1 (by rfl) ⟨33908273, by rfl⟩ : syracuseStep 45211031 = 67816547) B67816547
theorem B3718907 : Blo 1651525 3718907 := bstep (se 1 (by rfl) ⟨2789180, by rfl⟩ : syracuseStep 3718907 = 5578361) B5578361
theorem B3719465 : Blo 1651525 3719465 := bstep (se 2 (by rfl) ⟨1394799, by rfl⟩ : syracuseStep 3719465 = 2789599) B2789599
theorem B1860187 : Blo 1651525 1860187 := bstep (se 1 (by rfl) ⟨1395140, by rfl⟩ : syracuseStep 1860187 = 2790281) B2790281
theorem B14303951 : Blo 1651525 14303951 := bstep (se 1 (by rfl) ⟨10727963, by rfl⟩ : syracuseStep 14303951 = 21455927) B21455927
theorem B3720041 : Blo 1651525 3720041 := bstep (se 2 (by rfl) ⟨1395015, by rfl⟩ : syracuseStep 3720041 = 2790031) B2790031
theorem B3720185 : Blo 1651525 3720185 := bstep (se 2 (by rfl) ⟨1395069, by rfl⟩ : syracuseStep 3720185 = 2790139) B2790139
theorem B6276143 : Blo 1651525 6276143 := bstep (se 1 (by rfl) ⟨4707107, by rfl⟩ : syracuseStep 6276143 = 9414215) B9414215
theorem B8365193 : Blo 1651525 8365193 := bstep (se 2 (by rfl) ⟨3136947, by rfl⟩ : syracuseStep 8365193 = 6273895) B6273895
theorem B5580359 : Blo 1651525 5580359 := bstep (se 1 (by rfl) ⟨4185269, by rfl⟩ : syracuseStep 5580359 = 8370539) B8370539
theorem B30140687 : Blo 1651525 30140687 := bstep (se 1 (by rfl) ⟨22605515, by rfl⟩ : syracuseStep 30140687 = 45211031) B45211031
theorem B5294717 : Blo 1651525 5294717 := bstep (se 3 (by rfl) ⟨992759, by rfl⟩ : syracuseStep 5294717 = 1985519) B1985519
theorem B12553379 : Blo 1651525 12553379 := bstep (se 1 (by rfl) ⟨9415034, by rfl⟩ : syracuseStep 12553379 = 18830069) B18830069
theorem B5959165 : Blo 1651525 5959165 := bstep (se 3 (by rfl) ⟨1117343, by rfl⟩ : syracuseStep 5959165 = 2234687) B2234687
theorem B2477567 : Blo 1651525 2477567 := bstep (se 1 (by rfl) ⟨1858175, by rfl⟩ : syracuseStep 2477567 = 3716351) B3716351
theorem B2477705 : Blo 1651525 2477705 := bstep (se 2 (by rfl) ⟨929139, by rfl⟩ : syracuseStep 2477705 = 1858279) B1858279
theorem B12553865 : Blo 1651525 12553865 := bstep (se 2 (by rfl) ⟨4707699, by rfl⟩ : syracuseStep 12553865 = 9415399) B9415399
theorem B2477819 : Blo 1651525 2477819 := bstep (se 1 (by rfl) ⟨1858364, by rfl⟩ : syracuseStep 2477819 = 3716729) B3716729
theorem B51588937 : Blo 1651525 51588937 := bstep (se 2 (by rfl) ⟨19345851, by rfl⟩ : syracuseStep 51588937 = 38691703) B38691703
theorem B12554351 : Blo 1651525 12554351 := bstep (se 1 (by rfl) ⟨9415763, by rfl⟩ : syracuseStep 12554351 = 18831527) B18831527
theorem B2479271 : Blo 1651525 2479271 := bstep (se 1 (by rfl) ⟨1859453, by rfl⟩ : syracuseStep 2479271 = 3718907) B3718907
theorem B3716423 : Blo 1651525 3716423 := bstep (se 1 (by rfl) ⟨2787317, by rfl⟩ : syracuseStep 3716423 = 5574635) B5574635
theorem B6698321 : Blo 1651525 6698321 := bstep (se 2 (by rfl) ⟨2511870, by rfl⟩ : syracuseStep 6698321 = 5023741) B5023741
theorem B1652127 : Blo 1651525 1652127 := bstep (se 1 (by rfl) ⟨1239095, by rfl⟩ : syracuseStep 1652127 = 2478191) B2478191
theorem B2479595 : Blo 1651525 2479595 := bstep (se 1 (by rfl) ⟨1859696, by rfl⟩ : syracuseStep 2479595 = 3719393) B3719393
theorem B5576417 : Blo 1651525 5576417 := bstep (se 2 (by rfl) ⟨2091156, by rfl⟩ : syracuseStep 5576417 = 4182313) B4182313
theorem B1652455 : Blo 1651525 1652455 := bstep (se 1 (by rfl) ⟨1239341, by rfl⟩ : syracuseStep 1652455 = 2478683) B2478683
theorem B3716891 : Blo 1651525 3716891 := bstep (se 1 (by rfl) ⟨2787668, by rfl⟩ : syracuseStep 3716891 = 5575337) B5575337
theorem B2480063 : Blo 1651525 2480063 := bstep (se 1 (by rfl) ⟨1860047, by rfl⟩ : syracuseStep 2480063 = 3720095) B3720095
theorem B2480219 : Blo 1651525 2480219 := bstep (se 1 (by rfl) ⟨1860164, by rfl⟩ : syracuseStep 2480219 = 3720329) B3720329
theorem B1652863 : Blo 1651525 1652863 := bstep (se 1 (by rfl) ⟨1239647, by rfl⟩ : syracuseStep 1652863 = 2479295) B2479295
theorem B21477635 : Blo 1651525 21477635 := bstep (se 1 (by rfl) ⟨16108226, by rfl⟩ : syracuseStep 21477635 = 32216453) B32216453
theorem B7944475 : Blo 1651525 7944475 := bstep (se 1 (by rfl) ⟨5958356, by rfl⟩ : syracuseStep 7944475 = 11916713) B11916713
theorem B60316093 : Blo 1651525 60316093 := bstep (se 3 (by rfl) ⟨11309267, by rfl⟩ : syracuseStep 60316093 = 22618535) B22618535
theorem B5577497 : Blo 1651525 5577497 := bstep (se 2 (by rfl) ⟨2091561, by rfl⟩ : syracuseStep 5577497 = 4183123) B4183123
theorem B1858495 : Blo 1651525 1858495 := bstep (se 1 (by rfl) ⟨1393871, by rfl⟩ : syracuseStep 1858495 = 2787743) B2787743
theorem B3579017 : Blo 1651525 3579017 := bstep (se 2 (by rfl) ⟨1342131, by rfl⟩ : syracuseStep 3579017 = 2684263) B2684263
theorem B50879771 : Blo 1651525 50879771 := bstep (se 1 (by rfl) ⟨38159828, by rfl⟩ : syracuseStep 50879771 = 76319657) B76319657
theorem B3718655 : Blo 1651525 3718655 := bstep (se 1 (by rfl) ⟨2788991, by rfl⟩ : syracuseStep 3718655 = 5577983) B5577983
theorem B14114351 : Blo 1651525 14114351 := bstep (se 1 (by rfl) ⟨10585763, by rfl⟩ : syracuseStep 14114351 = 21171527) B21171527
theorem B13393457 : Blo 1651525 13393457 := bstep (se 2 (by rfl) ⟨5022546, by rfl⟩ : syracuseStep 13393457 = 10045093) B10045093
theorem B10592633 : Blo 1651525 10592633 := bstep (se 2 (by rfl) ⟨3972237, by rfl⟩ : syracuseStep 10592633 = 7944475) B7944475
theorem B9535967 : Blo 1651525 9535967 := bstep (se 1 (by rfl) ⟨7151975, by rfl⟩ : syracuseStep 9535967 = 14303951) B14303951
theorem B80421457 : Blo 1651525 80421457 := bstep (se 2 (by rfl) ⟨30158046, by rfl⟩ : syracuseStep 80421457 = 60316093) B60316093
theorem B4465547 : Blo 1651525 4465547 := bstep (se 1 (by rfl) ⟨3349160, by rfl⟩ : syracuseStep 4465547 = 6698321) B6698321
theorem B3720239 : Blo 1651525 3720239 := bstep (se 1 (by rfl) ⟨2790179, by rfl⟩ : syracuseStep 3720239 = 5580359) B5580359
theorem B38176181 : Blo 1651525 38176181 := bstep (se 5 (by rfl) ⟨1789508, by rfl⟩ : syracuseStep 38176181 = 3579017) B3579017
theorem B2477615 : Blo 1651525 2477615 := bstep (se 1 (by rfl) ⟨1858211, by rfl⟩ : syracuseStep 2477615 = 3716423) B3716423
theorem B2477927 : Blo 1651525 2477927 := bstep (se 1 (by rfl) ⟨1858445, by rfl⟩ : syracuseStep 2477927 = 3716891) B3716891
theorem B2477993 : Blo 1651525 2477993 := bstep (se 2 (by rfl) ⟨929247, by rfl⟩ : syracuseStep 2477993 = 1858495) B1858495
theorem B8368919 : Blo 1651525 8368919 := bstep (se 1 (by rfl) ⟨6276689, by rfl⟩ : syracuseStep 8368919 = 12553379) B12553379
theorem B33919847 : Blo 1651525 33919847 := bstep (se 1 (by rfl) ⟨25439885, by rfl⟩ : syracuseStep 33919847 = 50879771) B50879771
theorem B1651711 : Blo 1651525 1651711 := bstep (se 1 (by rfl) ⟨1238783, by rfl⟩ : syracuseStep 1651711 = 2477567) B2477567
theorem B2479103 : Blo 1651525 2479103 := bstep (se 1 (by rfl) ⟨1859327, by rfl⟩ : syracuseStep 2479103 = 3718655) B3718655
theorem B9409567 : Blo 1651525 9409567 := bstep (se 1 (by rfl) ⟨7057175, by rfl⟩ : syracuseStep 9409567 = 14114351) B14114351
theorem B1651803 : Blo 1651525 1651803 := bstep (se 1 (by rfl) ⟨1238852, by rfl⟩ : syracuseStep 1651803 = 2477705) B2477705
theorem B8369243 : Blo 1651525 8369243 := bstep (se 1 (by rfl) ⟨6276932, by rfl⟩ : syracuseStep 8369243 = 12553865) B12553865
theorem B68785249 : Blo 1651525 68785249 := bstep (se 2 (by rfl) ⟨25794468, by rfl⟩ : syracuseStep 68785249 = 51588937) B51588937
theorem B1651879 : Blo 1651525 1651879 := bstep (se 1 (by rfl) ⟨1238909, by rfl⟩ : syracuseStep 1651879 = 2477819) B2477819
theorem B8369567 : Blo 1651525 8369567 := bstep (se 1 (by rfl) ⟨6277175, by rfl⟩ : syracuseStep 8369567 = 12554351) B12554351
theorem B2479643 : Blo 1651525 2479643 := bstep (se 1 (by rfl) ⟨1859732, by rfl⟩ : syracuseStep 2479643 = 3719465) B3719465
theorem B2480027 : Blo 1651525 2480027 := bstep (se 1 (by rfl) ⟨1860020, by rfl⟩ : syracuseStep 2480027 = 3720041) B3720041
theorem B2480123 : Blo 1651525 2480123 := bstep (se 1 (by rfl) ⟨1860092, by rfl⟩ : syracuseStep 2480123 = 3720185) B3720185
theorem B4184095 : Blo 1651525 4184095 := bstep (se 1 (by rfl) ⟨3138071, by rfl⟩ : syracuseStep 4184095 = 6276143) B6276143
theorem B5576795 : Blo 1651525 5576795 := bstep (se 1 (by rfl) ⟨4182596, by rfl⟩ : syracuseStep 5576795 = 8365193) B8365193
theorem B1652847 : Blo 1651525 1652847 := bstep (se 1 (by rfl) ⟨1239635, by rfl⟩ : syracuseStep 1652847 = 2479271) B2479271
theorem B2480249 : Blo 1651525 2480249 := bstep (se 2 (by rfl) ⟨930093, by rfl⟩ : syracuseStep 2480249 = 1860187) B1860187
theorem B1653063 : Blo 1651525 1653063 := bstep (se 1 (by rfl) ⟨1239797, by rfl⟩ : syracuseStep 1653063 = 2479595) B2479595
theorem B3717611 : Blo 1651525 3717611 := bstep (se 1 (by rfl) ⟨2788208, by rfl⟩ : syracuseStep 3717611 = 5576417) B5576417
theorem B1653375 : Blo 1651525 1653375 := bstep (se 1 (by rfl) ⟨1240031, by rfl⟩ : syracuseStep 1653375 = 2480063) B2480063
theorem B1653479 : Blo 1651525 1653479 := bstep (se 1 (by rfl) ⟨1240109, by rfl⟩ : syracuseStep 1653479 = 2480219) B2480219
theorem B14318423 : Blo 1651525 14318423 := bstep (se 1 (by rfl) ⟨10738817, by rfl⟩ : syracuseStep 14318423 = 21477635) B21477635
theorem B20093791 : Blo 1651525 20093791 := bstep (se 1 (by rfl) ⟨15070343, by rfl⟩ : syracuseStep 20093791 = 30140687) B30140687
theorem B3529811 : Blo 1651525 3529811 := bstep (se 1 (by rfl) ⟨2647358, by rfl⟩ : syracuseStep 3529811 = 5294717) B5294717
theorem B3718331 : Blo 1651525 3718331 := bstep (se 1 (by rfl) ⟨2788748, by rfl⟩ : syracuseStep 3718331 = 5577497) B5577497
theorem B7945553 : Blo 1651525 7945553 := bstep (se 2 (by rfl) ⟨2979582, by rfl⟩ : syracuseStep 7945553 = 5959165) B5959165
theorem B8928971 : Blo 1651525 8928971 := bstep (se 1 (by rfl) ⟨6696728, by rfl⟩ : syracuseStep 8928971 = 13393457) B13393457
theorem B5578793 : Blo 1651525 5578793 := bstep (se 2 (by rfl) ⟨2092047, by rfl⟩ : syracuseStep 5578793 = 4184095) B4184095
theorem B7061755 : Blo 1651525 7061755 := bstep (se 1 (by rfl) ⟨5296316, by rfl⟩ : syracuseStep 7061755 = 10592633) B10592633
theorem B6357311 : Blo 1651525 6357311 := bstep (se 1 (by rfl) ⟨4767983, by rfl⟩ : syracuseStep 6357311 = 9535967) B9535967
theorem B5579279 : Blo 1651525 5579279 := bstep (se 1 (by rfl) ⟨4184459, by rfl⟩ : syracuseStep 5579279 = 8368919) B8368919
theorem B5579495 : Blo 1651525 5579495 := bstep (se 1 (by rfl) ⟨4184621, by rfl⟩ : syracuseStep 5579495 = 8369243) B8369243
theorem B5579711 : Blo 1651525 5579711 := bstep (se 1 (by rfl) ⟨4184783, by rfl⟩ : syracuseStep 5579711 = 8369567) B8369567
theorem B9545615 : Blo 1651525 9545615 := bstep (se 1 (by rfl) ⟨7159211, by rfl⟩ : syracuseStep 9545615 = 14318423) B14318423
theorem B2353207 : Blo 1651525 2353207 := bstep (se 1 (by rfl) ⟨1764905, by rfl⟩ : syracuseStep 2353207 = 3529811) B3529811
theorem B22613231 : Blo 1651525 22613231 := bstep (se 1 (by rfl) ⟨16959923, by rfl⟩ : syracuseStep 22613231 = 33919847) B33919847
theorem B2977031 : Blo 1651525 2977031 := bstep (se 1 (by rfl) ⟨2232773, by rfl⟩ : syracuseStep 2977031 = 4465547) B4465547
theorem B107228609 : Blo 1651525 107228609 := bstep (se 2 (by rfl) ⟨40210728, by rfl⟩ : syracuseStep 107228609 = 80421457) B80421457
theorem B26791721 : Blo 1651525 26791721 := bstep (se 2 (by rfl) ⟨10046895, by rfl⟩ : syracuseStep 26791721 = 20093791) B20093791
theorem B12546089 : Blo 1651525 12546089 := bstep (se 2 (by rfl) ⟨4704783, by rfl⟩ : syracuseStep 12546089 = 9409567) B9409567
theorem B91713665 : Blo 1651525 91713665 := bstep (se 2 (by rfl) ⟨34392624, by rfl⟩ : syracuseStep 91713665 = 68785249) B68785249
theorem B2478407 : Blo 1651525 2478407 := bstep (se 1 (by rfl) ⟨1858805, by rfl⟩ : syracuseStep 2478407 = 3717611) B3717611
theorem B2478887 : Blo 1651525 2478887 := bstep (se 1 (by rfl) ⟨1859165, by rfl⟩ : syracuseStep 2478887 = 3718331) B3718331
theorem B5297035 : Blo 1651525 5297035 := bstep (se 1 (by rfl) ⟨3972776, by rfl⟩ : syracuseStep 5297035 = 7945553) B7945553
theorem B1651743 : Blo 1651525 1651743 := bstep (se 1 (by rfl) ⟨1238807, by rfl⟩ : syracuseStep 1651743 = 2477615) B2477615
theorem B5952647 : Blo 1651525 5952647 := bstep (se 1 (by rfl) ⟨4464485, by rfl⟩ : syracuseStep 5952647 = 8928971) B8928971
theorem B1651951 : Blo 1651525 1651951 := bstep (se 1 (by rfl) ⟨1238963, by rfl⟩ : syracuseStep 1651951 = 2477927) B2477927
theorem B1651995 : Blo 1651525 1651995 := bstep (se 1 (by rfl) ⟨1238996, by rfl⟩ : syracuseStep 1651995 = 2477993) B2477993
theorem B1652735 : Blo 1651525 1652735 := bstep (se 1 (by rfl) ⟨1239551, by rfl⟩ : syracuseStep 1652735 = 2479103) B2479103
theorem B2480159 : Blo 1651525 2480159 := bstep (se 1 (by rfl) ⟨1860119, by rfl⟩ : syracuseStep 2480159 = 3720239) B3720239
theorem B25450787 : Blo 1651525 25450787 := bstep (se 1 (by rfl) ⟨19088090, by rfl⟩ : syracuseStep 25450787 = 38176181) B38176181
theorem B1653095 : Blo 1651525 1653095 := bstep (se 1 (by rfl) ⟨1239821, by rfl⟩ : syracuseStep 1653095 = 2479643) B2479643
theorem B1653351 : Blo 1651525 1653351 := bstep (se 1 (by rfl) ⟨1240013, by rfl⟩ : syracuseStep 1653351 = 2480027) B2480027
theorem B1653415 : Blo 1651525 1653415 := bstep (se 1 (by rfl) ⟨1240061, by rfl⟩ : syracuseStep 1653415 = 2480123) B2480123
theorem B3717863 : Blo 1651525 3717863 := bstep (se 1 (by rfl) ⟨2788397, by rfl⟩ : syracuseStep 3717863 = 5576795) B5576795
theorem B1653499 : Blo 1651525 1653499 := bstep (se 1 (by rfl) ⟨1240124, by rfl⟩ : syracuseStep 1653499 = 2480249) B2480249
theorem B8364059 : Blo 1651525 8364059 := bstep (se 1 (by rfl) ⟨6273044, by rfl⟩ : syracuseStep 8364059 = 12546089) B12546089
theorem B3719195 : Blo 1651525 3719195 := bstep (se 1 (by rfl) ⟨2789396, by rfl⟩ : syracuseStep 3719195 = 5578793) B5578793
theorem B3137609 : Blo 1651525 3137609 := bstep (se 2 (by rfl) ⟨1176603, by rfl⟩ : syracuseStep 3137609 = 2353207) B2353207
theorem B3719519 : Blo 1651525 3719519 := bstep (se 1 (by rfl) ⟨2789639, by rfl⟩ : syracuseStep 3719519 = 5579279) B5579279
theorem B3719663 : Blo 1651525 3719663 := bstep (se 1 (by rfl) ⟨2789747, by rfl⟩ : syracuseStep 3719663 = 5579495) B5579495
theorem B3719807 : Blo 1651525 3719807 := bstep (se 1 (by rfl) ⟨2789855, by rfl⟩ : syracuseStep 3719807 = 5579711) B5579711
theorem B7938749 : Blo 1651525 7938749 := bstep (se 3 (by rfl) ⟨1488515, by rfl⟩ : syracuseStep 7938749 = 2977031) B2977031
theorem B7062713 : Blo 1651525 7062713 := bstep (se 2 (by rfl) ⟨2648517, by rfl⟩ : syracuseStep 7062713 = 5297035) B5297035
theorem B16967191 : Blo 1651525 16967191 := bstep (se 1 (by rfl) ⟨12725393, by rfl⟩ : syracuseStep 16967191 = 25450787) B25450787
theorem B15075487 : Blo 1651525 15075487 := bstep (se 1 (by rfl) ⟨11306615, by rfl⟩ : syracuseStep 15075487 = 22613231) B22613231
theorem B71485739 : Blo 1651525 71485739 := bstep (se 1 (by rfl) ⟨53614304, by rfl⟩ : syracuseStep 71485739 = 107228609) B107228609
theorem B17861147 : Blo 1651525 17861147 := bstep (se 1 (by rfl) ⟨13395860, by rfl⟩ : syracuseStep 17861147 = 26791721) B26791721
theorem B4238207 : Blo 1651525 4238207 := bstep (se 1 (by rfl) ⟨3178655, by rfl⟩ : syracuseStep 4238207 = 6357311) B6357311
theorem B9415673 : Blo 1651525 9415673 := bstep (se 2 (by rfl) ⟨3530877, by rfl⟩ : syracuseStep 9415673 = 7061755) B7061755
theorem B2478575 : Blo 1651525 2478575 := bstep (se 1 (by rfl) ⟨1858931, by rfl⟩ : syracuseStep 2478575 = 3717863) B3717863
theorem B1652271 : Blo 1651525 1652271 := bstep (se 1 (by rfl) ⟨1239203, by rfl⟩ : syracuseStep 1652271 = 2478407) B2478407
theorem B244569773 : Blo 1651525 244569773 := bstep (se 3 (by rfl) ⟨45856832, by rfl⟩ : syracuseStep 244569773 = 91713665) B91713665
theorem B15873725 : Blo 1651525 15873725 := bstep (se 3 (by rfl) ⟨2976323, by rfl⟩ : syracuseStep 15873725 = 5952647) B5952647
theorem B1652591 : Blo 1651525 1652591 := bstep (se 1 (by rfl) ⟨1239443, by rfl⟩ : syracuseStep 1652591 = 2478887) B2478887
theorem B6363743 : Blo 1651525 6363743 := bstep (se 1 (by rfl) ⟨4772807, by rfl⟩ : syracuseStep 6363743 = 9545615) B9545615
theorem B1653439 : Blo 1651525 1653439 := bstep (se 1 (by rfl) ⟨1240079, by rfl⟩ : syracuseStep 1653439 = 2480159) B2480159
theorem B5292499 : Blo 1651525 5292499 := bstep (se 1 (by rfl) ⟨3969374, by rfl⟩ : syracuseStep 5292499 = 7938749) B7938749
theorem B163046515 : Blo 1651525 163046515 := bstep (se 1 (by rfl) ⟨122284886, by rfl⟩ : syracuseStep 163046515 = 244569773) B244569773
theorem B6277115 : Blo 1651525 6277115 := bstep (se 1 (by rfl) ⟨4707836, by rfl⟩ : syracuseStep 6277115 = 9415673) B9415673
theorem B2091739 : Blo 1651525 2091739 := bstep (se 1 (by rfl) ⟨1568804, by rfl⟩ : syracuseStep 2091739 = 3137609) B3137609
theorem B47657159 : Blo 1651525 47657159 := bstep (se 1 (by rfl) ⟨35742869, by rfl⟩ : syracuseStep 47657159 = 71485739) B71485739
theorem B16969981 : Blo 1651525 16969981 := bstep (se 3 (by rfl) ⟨3181871, by rfl⟩ : syracuseStep 16969981 = 6363743) B6363743
theorem B11907431 : Blo 1651525 11907431 := bstep (se 1 (by rfl) ⟨8930573, by rfl⟩ : syracuseStep 11907431 = 17861147) B17861147
theorem B22622921 : Blo 1651525 22622921 := bstep (se 2 (by rfl) ⟨8483595, by rfl⟩ : syracuseStep 22622921 = 16967191) B16967191
theorem B5576039 : Blo 1651525 5576039 := bstep (se 1 (by rfl) ⟨4182029, by rfl⟩ : syracuseStep 5576039 = 8364059) B8364059
theorem B2479463 : Blo 1651525 2479463 := bstep (se 1 (by rfl) ⟨1859597, by rfl⟩ : syracuseStep 2479463 = 3719195) B3719195
theorem B20100649 : Blo 1651525 20100649 := bstep (se 2 (by rfl) ⟨7537743, by rfl⟩ : syracuseStep 20100649 = 15075487) B15075487
theorem B2479679 : Blo 1651525 2479679 := bstep (se 1 (by rfl) ⟨1859759, by rfl⟩ : syracuseStep 2479679 = 3719519) B3719519
theorem B1652383 : Blo 1651525 1652383 := bstep (se 1 (by rfl) ⟨1239287, by rfl⟩ : syracuseStep 1652383 = 2478575) B2478575
theorem B2479775 : Blo 1651525 2479775 := bstep (se 1 (by rfl) ⟨1859831, by rfl⟩ : syracuseStep 2479775 = 3719663) B3719663
theorem B2479871 : Blo 1651525 2479871 := bstep (se 1 (by rfl) ⟨1859903, by rfl⟩ : syracuseStep 2479871 = 3719807) B3719807
theorem B4708475 : Blo 1651525 4708475 := bstep (se 1 (by rfl) ⟨3531356, by rfl⟩ : syracuseStep 4708475 = 7062713) B7062713
theorem B10582483 : Blo 1651525 10582483 := bstep (se 1 (by rfl) ⟨7936862, by rfl⟩ : syracuseStep 10582483 = 15873725) B15873725
theorem B2825471 : Blo 1651525 2825471 := bstep (se 1 (by rfl) ⟨2119103, by rfl⟩ : syracuseStep 2825471 = 4238207) B4238207
theorem B7938287 : Blo 1651525 7938287 := bstep (se 1 (by rfl) ⟨5953715, by rfl⟩ : syracuseStep 7938287 = 11907431) B11907431
theorem B22626641 : Blo 1651525 22626641 := bstep (se 2 (by rfl) ⟨8484990, by rfl⟩ : syracuseStep 22626641 = 16969981) B16969981
theorem B15081947 : Blo 1651525 15081947 := bstep (se 1 (by rfl) ⟨11311460, by rfl⟩ : syracuseStep 15081947 = 22622921) B22622921
theorem B3138983 : Blo 1651525 3138983 := bstep (se 1 (by rfl) ⟨2354237, by rfl⟩ : syracuseStep 3138983 = 4708475) B4708475
theorem B31771439 : Blo 1651525 31771439 := bstep (se 1 (by rfl) ⟨23828579, by rfl⟩ : syracuseStep 31771439 = 47657159) B47657159
theorem B14109977 : Blo 1651525 14109977 := bstep (se 2 (by rfl) ⟨5291241, by rfl⟩ : syracuseStep 14109977 = 10582483) B10582483
theorem B7056665 : Blo 1651525 7056665 := bstep (se 2 (by rfl) ⟨2646249, by rfl⟩ : syracuseStep 7056665 = 5292499) B5292499
theorem B2788985 : Blo 1651525 2788985 := bstep (se 2 (by rfl) ⟨1045869, by rfl⟩ : syracuseStep 2788985 = 2091739) B2091739
theorem B217395353 : Blo 1651525 217395353 := bstep (se 2 (by rfl) ⟨81523257, by rfl⟩ : syracuseStep 217395353 = 163046515) B163046515
theorem B26800865 : Blo 1651525 26800865 := bstep (se 2 (by rfl) ⟨10050324, by rfl⟩ : syracuseStep 26800865 = 20100649) B20100649
theorem B3717359 : Blo 1651525 3717359 := bstep (se 1 (by rfl) ⟨2788019, by rfl⟩ : syracuseStep 3717359 = 5576039) B5576039
theorem B1652975 : Blo 1651525 1652975 := bstep (se 1 (by rfl) ⟨1239731, by rfl⟩ : syracuseStep 1652975 = 2479463) B2479463
theorem B1653119 : Blo 1651525 1653119 := bstep (se 1 (by rfl) ⟨1239839, by rfl⟩ : syracuseStep 1653119 = 2479679) B2479679
theorem B1653183 : Blo 1651525 1653183 := bstep (se 1 (by rfl) ⟨1239887, by rfl⟩ : syracuseStep 1653183 = 2479775) B2479775
theorem B1653247 : Blo 1651525 1653247 := bstep (se 1 (by rfl) ⟨1239935, by rfl⟩ : syracuseStep 1653247 = 2479871) B2479871
theorem B4184743 : Blo 1651525 4184743 := bstep (se 1 (by rfl) ⟨3138557, by rfl⟩ : syracuseStep 4184743 = 6277115) B6277115
theorem B1883647 : Blo 1651525 1883647 := bstep (se 1 (by rfl) ⟨1412735, by rfl⟩ : syracuseStep 1883647 = 2825471) B2825471
theorem B5292191 : Blo 1651525 5292191 := bstep (se 1 (by rfl) ⟨3969143, by rfl⟩ : syracuseStep 5292191 = 7938287) B7938287
theorem B17867243 : Blo 1651525 17867243 := bstep (se 1 (by rfl) ⟨13400432, by rfl⟩ : syracuseStep 17867243 = 26800865) B26800865
theorem B5579657 : Blo 1651525 5579657 := bstep (se 2 (by rfl) ⟨2092371, by rfl⟩ : syracuseStep 5579657 = 4184743) B4184743
theorem B9406651 : Blo 1651525 9406651 := bstep (se 1 (by rfl) ⟨7054988, by rfl⟩ : syracuseStep 9406651 = 14109977) B14109977
theorem B4704443 : Blo 1651525 4704443 := bstep (se 1 (by rfl) ⟨3528332, by rfl⟩ : syracuseStep 4704443 = 7056665) B7056665
theorem B15084427 : Blo 1651525 15084427 := bstep (se 1 (by rfl) ⟨11313320, by rfl⟩ : syracuseStep 15084427 = 22626641) B22626641
theorem B10054631 : Blo 1651525 10054631 := bstep (se 1 (by rfl) ⟨7540973, by rfl⟩ : syracuseStep 10054631 = 15081947) B15081947
theorem B2092655 : Blo 1651525 2092655 := bstep (se 1 (by rfl) ⟨1569491, by rfl⟩ : syracuseStep 2092655 = 3138983) B3138983
theorem B2478239 : Blo 1651525 2478239 := bstep (se 1 (by rfl) ⟨1858679, by rfl⟩ : syracuseStep 2478239 = 3717359) B3717359
theorem B21180959 : Blo 1651525 21180959 := bstep (se 1 (by rfl) ⟨15885719, by rfl⟩ : syracuseStep 21180959 = 31771439) B31771439
theorem B2511529 : Blo 1651525 2511529 := bstep (se 2 (by rfl) ⟨941823, by rfl⟩ : syracuseStep 2511529 = 1883647) B1883647
theorem B144930235 : Blo 1651525 144930235 := bstep (se 1 (by rfl) ⟨108697676, by rfl⟩ : syracuseStep 144930235 = 217395353) B217395353
theorem B1859323 : Blo 1651525 1859323 := bstep (se 1 (by rfl) ⟨1394492, by rfl⟩ : syracuseStep 1859323 = 2788985) B2788985
theorem B12542201 : Blo 1651525 12542201 := bstep (se 2 (by rfl) ⟨4703325, by rfl⟩ : syracuseStep 12542201 = 9406651) B9406651
theorem B3719771 : Blo 1651525 3719771 := bstep (se 1 (by rfl) ⟨2789828, by rfl⟩ : syracuseStep 3719771 = 5579657) B5579657
theorem B13394821 : Blo 1651525 13394821 := bstep (se 4 (by rfl) ⟨1255764, by rfl⟩ : syracuseStep 13394821 = 2511529) B2511529
theorem B20112569 : Blo 1651525 20112569 := bstep (se 2 (by rfl) ⟨7542213, by rfl⟩ : syracuseStep 20112569 = 15084427) B15084427
theorem B47645981 : Blo 1651525 47645981 := bstep (se 3 (by rfl) ⟨8933621, by rfl⟩ : syracuseStep 47645981 = 17867243) B17867243
theorem B5580413 : Blo 1651525 5580413 := bstep (se 3 (by rfl) ⟨1046327, by rfl⟩ : syracuseStep 5580413 = 2092655) B2092655
theorem B6703087 : Blo 1651525 6703087 := bstep (se 1 (by rfl) ⟨5027315, by rfl⟩ : syracuseStep 6703087 = 10054631) B10054631
theorem B2479097 : Blo 1651525 2479097 := bstep (se 2 (by rfl) ⟨929661, by rfl⟩ : syracuseStep 2479097 = 1859323) B1859323
theorem B3528127 : Blo 1651525 3528127 := bstep (se 1 (by rfl) ⟨2646095, by rfl⟩ : syracuseStep 3528127 = 5292191) B5292191
theorem B1652159 : Blo 1651525 1652159 := bstep (se 1 (by rfl) ⟨1239119, by rfl⟩ : syracuseStep 1652159 = 2478239) B2478239
theorem B14120639 : Blo 1651525 14120639 := bstep (se 1 (by rfl) ⟨10590479, by rfl⟩ : syracuseStep 14120639 = 21180959) B21180959
theorem B3136295 : Blo 1651525 3136295 := bstep (se 1 (by rfl) ⟨2352221, by rfl⟩ : syracuseStep 3136295 = 4704443) B4704443
theorem B193240313 : Blo 1651525 193240313 := bstep (se 2 (by rfl) ⟨72465117, by rfl⟩ : syracuseStep 193240313 = 144930235) B144930235
theorem B3720275 : Blo 1651525 3720275 := bstep (se 1 (by rfl) ⟨2790206, by rfl⟩ : syracuseStep 3720275 = 5580413) B5580413
theorem B9413759 : Blo 1651525 9413759 := bstep (se 1 (by rfl) ⟨7060319, by rfl⟩ : syracuseStep 9413759 = 14120639) B14120639
theorem B17859761 : Blo 1651525 17859761 := bstep (se 2 (by rfl) ⟨6697410, by rfl⟩ : syracuseStep 17859761 = 13394821) B13394821
theorem B2090863 : Blo 1651525 2090863 := bstep (se 1 (by rfl) ⟨1568147, by rfl⟩ : syracuseStep 2090863 = 3136295) B3136295
theorem B4704169 : Blo 1651525 4704169 := bstep (se 2 (by rfl) ⟨1764063, by rfl⟩ : syracuseStep 4704169 = 3528127) B3528127
theorem B31763987 : Blo 1651525 31763987 := bstep (se 1 (by rfl) ⟨23822990, by rfl⟩ : syracuseStep 31763987 = 47645981) B47645981
theorem B8361467 : Blo 1651525 8361467 := bstep (se 1 (by rfl) ⟨6271100, by rfl⟩ : syracuseStep 8361467 = 12542201) B12542201
theorem B2479847 : Blo 1651525 2479847 := bstep (se 1 (by rfl) ⟨1859885, by rfl⟩ : syracuseStep 2479847 = 3719771) B3719771
theorem B1652731 : Blo 1651525 1652731 := bstep (se 1 (by rfl) ⟨1239548, by rfl⟩ : syracuseStep 1652731 = 2479097) B2479097
theorem B13408379 : Blo 1651525 13408379 := bstep (se 1 (by rfl) ⟨10056284, by rfl⟩ : syracuseStep 13408379 = 20112569) B20112569
theorem B128826875 : Blo 1651525 128826875 := bstep (se 1 (by rfl) ⟨96620156, by rfl⟩ : syracuseStep 128826875 = 193240313) B193240313
theorem B8937449 : Blo 1651525 8937449 := bstep (se 2 (by rfl) ⟨3351543, by rfl⟩ : syracuseStep 8937449 = 6703087) B6703087
theorem B6275839 : Blo 1651525 6275839 := bstep (se 1 (by rfl) ⟨4706879, by rfl⟩ : syracuseStep 6275839 = 9413759) B9413759
theorem B8938919 : Blo 1651525 8938919 := bstep (se 1 (by rfl) ⟨6704189, by rfl⟩ : syracuseStep 8938919 = 13408379) B13408379
theorem B2787817 : Blo 1651525 2787817 := bstep (se 2 (by rfl) ⟨1045431, by rfl⟩ : syracuseStep 2787817 = 2090863) B2090863
theorem B5958299 : Blo 1651525 5958299 := bstep (se 1 (by rfl) ⟨4468724, by rfl⟩ : syracuseStep 5958299 = 8937449) B8937449
theorem B11906507 : Blo 1651525 11906507 := bstep (se 1 (by rfl) ⟨8929880, by rfl⟩ : syracuseStep 11906507 = 17859761) B17859761
theorem B5574311 : Blo 1651525 5574311 := bstep (se 1 (by rfl) ⟨4180733, by rfl⟩ : syracuseStep 5574311 = 8361467) B8361467
theorem B6272225 : Blo 1651525 6272225 := bstep (se 2 (by rfl) ⟨2352084, by rfl⟩ : syracuseStep 6272225 = 4704169) B4704169
theorem B2480183 : Blo 1651525 2480183 := bstep (se 1 (by rfl) ⟨1860137, by rfl⟩ : syracuseStep 2480183 = 3720275) B3720275
theorem B1653231 : Blo 1651525 1653231 := bstep (se 1 (by rfl) ⟨1239923, by rfl⟩ : syracuseStep 1653231 = 2479847) B2479847
theorem B85884583 : Blo 1651525 85884583 := bstep (se 1 (by rfl) ⟨64413437, by rfl⟩ : syracuseStep 85884583 = 128826875) B128826875
theorem B21175991 : Blo 1651525 21175991 := bstep (se 1 (by rfl) ⟨15881993, by rfl⟩ : syracuseStep 21175991 = 31763987) B31763987
theorem B14117327 : Blo 1651525 14117327 := bstep (se 1 (by rfl) ⟨10587995, by rfl⟩ : syracuseStep 14117327 = 21175991) B21175991
theorem B4181483 : Blo 1651525 4181483 := bstep (se 1 (by rfl) ⟨3136112, by rfl⟩ : syracuseStep 4181483 = 6272225) B6272225
theorem B5959279 : Blo 1651525 5959279 := bstep (se 1 (by rfl) ⟨4469459, by rfl⟩ : syracuseStep 5959279 = 8938919) B8938919
theorem B8367785 : Blo 1651525 8367785 := bstep (se 2 (by rfl) ⟨3137919, by rfl⟩ : syracuseStep 8367785 = 6275839) B6275839
theorem B15888797 : Blo 1651525 15888797 := bstep (se 3 (by rfl) ⟨2979149, by rfl⟩ : syracuseStep 15888797 = 5958299) B5958299
theorem B114512777 : Blo 1651525 114512777 := bstep (se 2 (by rfl) ⟨42942291, by rfl⟩ : syracuseStep 114512777 = 85884583) B85884583
theorem B3716207 : Blo 1651525 3716207 := bstep (se 1 (by rfl) ⟨2787155, by rfl⟩ : syracuseStep 3716207 = 5574311) B5574311
theorem B3717089 : Blo 1651525 3717089 := bstep (se 2 (by rfl) ⟨1393908, by rfl⟩ : syracuseStep 3717089 = 2787817) B2787817
theorem B1653455 : Blo 1651525 1653455 := bstep (se 1 (by rfl) ⟨1240091, by rfl⟩ : syracuseStep 1653455 = 2480183) B2480183
theorem B7937671 : Blo 1651525 7937671 := bstep (se 1 (by rfl) ⟨5953253, by rfl⟩ : syracuseStep 7937671 = 11906507) B11906507
theorem B10592531 : Blo 1651525 10592531 := bstep (se 1 (by rfl) ⟨7944398, by rfl⟩ : syracuseStep 10592531 = 15888797) B15888797
theorem B76341851 : Blo 1651525 76341851 := bstep (se 1 (by rfl) ⟨57256388, by rfl⟩ : syracuseStep 76341851 = 114512777) B114512777
theorem B2787655 : Blo 1651525 2787655 := bstep (se 1 (by rfl) ⟨2090741, by rfl⟩ : syracuseStep 2787655 = 4181483) B4181483
theorem B2477471 : Blo 1651525 2477471 := bstep (se 1 (by rfl) ⟨1858103, by rfl⟩ : syracuseStep 2477471 = 3716207) B3716207
theorem B2478059 : Blo 1651525 2478059 := bstep (se 1 (by rfl) ⟨1858544, by rfl⟩ : syracuseStep 2478059 = 3717089) B3717089
theorem B9411551 : Blo 1651525 9411551 := bstep (se 1 (by rfl) ⟨7058663, by rfl⟩ : syracuseStep 9411551 = 14117327) B14117327
theorem B7945705 : Blo 1651525 7945705 := bstep (se 2 (by rfl) ⟨2979639, by rfl⟩ : syracuseStep 7945705 = 5959279) B5959279
theorem B10583561 : Blo 1651525 10583561 := bstep (se 2 (by rfl) ⟨3968835, by rfl⟩ : syracuseStep 10583561 = 7937671) B7937671
theorem B5578523 : Blo 1651525 5578523 := bstep (se 1 (by rfl) ⟨4183892, by rfl⟩ : syracuseStep 5578523 = 8367785) B8367785
theorem B7061687 : Blo 1651525 7061687 := bstep (se 1 (by rfl) ⟨5296265, by rfl⟩ : syracuseStep 7061687 = 10592531) B10592531
theorem B10594273 : Blo 1651525 10594273 := bstep (se 2 (by rfl) ⟨3972852, by rfl⟩ : syracuseStep 10594273 = 7945705) B7945705
theorem B7055707 : Blo 1651525 7055707 := bstep (se 1 (by rfl) ⟨5291780, by rfl⟩ : syracuseStep 7055707 = 10583561) B10583561
theorem B1651647 : Blo 1651525 1651647 := bstep (se 1 (by rfl) ⟨1238735, by rfl⟩ : syracuseStep 1651647 = 2477471) B2477471
theorem B1652039 : Blo 1651525 1652039 := bstep (se 1 (by rfl) ⟨1239029, by rfl⟩ : syracuseStep 1652039 = 2478059) B2478059
theorem B50894567 : Blo 1651525 50894567 := bstep (se 1 (by rfl) ⟨38170925, by rfl⟩ : syracuseStep 50894567 = 76341851) B76341851
theorem B3716873 : Blo 1651525 3716873 := bstep (se 2 (by rfl) ⟨1393827, by rfl⟩ : syracuseStep 3716873 = 2787655) B2787655
theorem B6274367 : Blo 1651525 6274367 := bstep (se 1 (by rfl) ⟨4705775, by rfl⟩ : syracuseStep 6274367 = 9411551) B9411551
theorem B3719015 : Blo 1651525 3719015 := bstep (se 1 (by rfl) ⟨2789261, by rfl⟩ : syracuseStep 3719015 = 5578523) B5578523
theorem B14125697 : Blo 1651525 14125697 := bstep (se 2 (by rfl) ⟨5297136, by rfl⟩ : syracuseStep 14125697 = 10594273) B10594273
theorem B9407609 : Blo 1651525 9407609 := bstep (se 2 (by rfl) ⟨3527853, by rfl⟩ : syracuseStep 9407609 = 7055707) B7055707
theorem B2477915 : Blo 1651525 2477915 := bstep (se 1 (by rfl) ⟨1858436, by rfl⟩ : syracuseStep 2477915 = 3716873) B3716873
theorem B4182911 : Blo 1651525 4182911 := bstep (se 1 (by rfl) ⟨3137183, by rfl⟩ : syracuseStep 4182911 = 6274367) B6274367
theorem B2479343 : Blo 1651525 2479343 := bstep (se 1 (by rfl) ⟨1859507, by rfl⟩ : syracuseStep 2479343 = 3719015) B3719015
theorem B4707791 : Blo 1651525 4707791 := bstep (se 1 (by rfl) ⟨3530843, by rfl⟩ : syracuseStep 4707791 = 7061687) B7061687
theorem B33929711 : Blo 1651525 33929711 := bstep (se 1 (by rfl) ⟨25447283, by rfl⟩ : syracuseStep 33929711 = 50894567) B50894567
theorem B3138527 : Blo 1651525 3138527 := bstep (se 1 (by rfl) ⟨2353895, by rfl⟩ : syracuseStep 3138527 = 4707791) B4707791
theorem B22619807 : Blo 1651525 22619807 := bstep (se 1 (by rfl) ⟨16964855, by rfl⟩ : syracuseStep 22619807 = 33929711) B33929711
theorem B2788607 : Blo 1651525 2788607 := bstep (se 1 (by rfl) ⟨2091455, by rfl⟩ : syracuseStep 2788607 = 4182911) B4182911
theorem B9417131 : Blo 1651525 9417131 := bstep (se 1 (by rfl) ⟨7062848, by rfl⟩ : syracuseStep 9417131 = 14125697) B14125697
theorem B6271739 : Blo 1651525 6271739 := bstep (se 1 (by rfl) ⟨4703804, by rfl⟩ : syracuseStep 6271739 = 9407609) B9407609
theorem B1651943 : Blo 1651525 1651943 := bstep (se 1 (by rfl) ⟨1238957, by rfl⟩ : syracuseStep 1651943 = 2477915) B2477915
theorem B1652895 : Blo 1651525 1652895 := bstep (se 1 (by rfl) ⟨1239671, by rfl⟩ : syracuseStep 1652895 = 2479343) B2479343
theorem B6278087 : Blo 1651525 6278087 := bstep (se 1 (by rfl) ⟨4708565, by rfl⟩ : syracuseStep 6278087 = 9417131) B9417131
theorem B4181159 : Blo 1651525 4181159 := bstep (se 1 (by rfl) ⟨3135869, by rfl⟩ : syracuseStep 4181159 = 6271739) B6271739
theorem B8369405 : Blo 1651525 8369405 := bstep (se 3 (by rfl) ⟨1569263, by rfl⟩ : syracuseStep 8369405 = 3138527) B3138527
theorem B15079871 : Blo 1651525 15079871 := bstep (se 1 (by rfl) ⟨11309903, by rfl⟩ : syracuseStep 15079871 = 22619807) B22619807
theorem B1859071 : Blo 1651525 1859071 := bstep (se 1 (by rfl) ⟨1394303, by rfl⟩ : syracuseStep 1859071 = 2788607) B2788607
theorem B5579603 : Blo 1651525 5579603 := bstep (se 1 (by rfl) ⟨4184702, by rfl⟩ : syracuseStep 5579603 = 8369405) B8369405
theorem B10053247 : Blo 1651525 10053247 := bstep (se 1 (by rfl) ⟨7539935, by rfl⟩ : syracuseStep 10053247 = 15079871) B15079871
theorem B2787439 : Blo 1651525 2787439 := bstep (se 1 (by rfl) ⟨2090579, by rfl⟩ : syracuseStep 2787439 = 4181159) B4181159
theorem B2478761 : Blo 1651525 2478761 := bstep (se 2 (by rfl) ⟨929535, by rfl⟩ : syracuseStep 2478761 = 1859071) B1859071
theorem B4185391 : Blo 1651525 4185391 := bstep (se 1 (by rfl) ⟨3139043, by rfl⟩ : syracuseStep 4185391 = 6278087) B6278087
theorem B3719735 : Blo 1651525 3719735 := bstep (se 1 (by rfl) ⟨2789801, by rfl⟩ : syracuseStep 3719735 = 5579603) B5579603
theorem B5580521 : Blo 1651525 5580521 := bstep (se 2 (by rfl) ⟨2092695, by rfl⟩ : syracuseStep 5580521 = 4185391) B4185391
theorem B13404329 : Blo 1651525 13404329 := bstep (se 2 (by rfl) ⟨5026623, by rfl⟩ : syracuseStep 13404329 = 10053247) B10053247
theorem B3716585 : Blo 1651525 3716585 := bstep (se 2 (by rfl) ⟨1393719, by rfl⟩ : syracuseStep 3716585 = 2787439) B2787439
theorem B1652507 : Blo 1651525 1652507 := bstep (se 1 (by rfl) ⟨1239380, by rfl⟩ : syracuseStep 1652507 = 2478761) B2478761
theorem B3720347 : Blo 1651525 3720347 := bstep (se 1 (by rfl) ⟨2790260, by rfl⟩ : syracuseStep 3720347 = 5580521) B5580521
theorem B2477723 : Blo 1651525 2477723 := bstep (se 1 (by rfl) ⟨1858292, by rfl⟩ : syracuseStep 2477723 = 3716585) B3716585
theorem B2479823 : Blo 1651525 2479823 := bstep (se 1 (by rfl) ⟨1859867, by rfl⟩ : syracuseStep 2479823 = 3719735) B3719735
theorem B8936219 : Blo 1651525 8936219 := bstep (se 1 (by rfl) ⟨6702164, by rfl⟩ : syracuseStep 8936219 = 13404329) B13404329
theorem B5957479 : Blo 1651525 5957479 := bstep (se 1 (by rfl) ⟨4468109, by rfl⟩ : syracuseStep 5957479 = 8936219) B8936219
theorem B1651815 : Blo 1651525 1651815 := bstep (se 1 (by rfl) ⟨1238861, by rfl⟩ : syracuseStep 1651815 = 2477723) B2477723
theorem B2480231 : Blo 1651525 2480231 := bstep (se 1 (by rfl) ⟨1860173, by rfl⟩ : syracuseStep 2480231 = 3720347) B3720347
theorem B1653215 : Blo 1651525 1653215 := bstep (se 1 (by rfl) ⟨1239911, by rfl⟩ : syracuseStep 1653215 = 2479823) B2479823
theorem B7943305 : Blo 1651525 7943305 := bstep (se 2 (by rfl) ⟨2978739, by rfl⟩ : syracuseStep 7943305 = 5957479) B5957479
theorem B1653487 : Blo 1651525 1653487 := bstep (se 1 (by rfl) ⟨1240115, by rfl⟩ : syracuseStep 1653487 = 2480231) B2480231
theorem B10591073 : Blo 1651525 10591073 := bstep (se 2 (by rfl) ⟨3971652, by rfl⟩ : syracuseStep 10591073 = 7943305) B7943305
theorem B7060715 : Blo 1651525 7060715 := bstep (se 1 (by rfl) ⟨5295536, by rfl⟩ : syracuseStep 7060715 = 10591073) B10591073
theorem B4707143 : Blo 1651525 4707143 := bstep (se 1 (by rfl) ⟨3530357, by rfl⟩ : syracuseStep 4707143 = 7060715) B7060715
theorem B3138095 : Blo 1651525 3138095 := bstep (se 1 (by rfl) ⟨2353571, by rfl⟩ : syracuseStep 3138095 = 4707143) B4707143
theorem B2092063 : Blo 1651525 2092063 := bstep (se 1 (by rfl) ⟨1569047, by rfl⟩ : syracuseStep 2092063 = 3138095) B3138095
theorem B2789417 : Blo 1651525 2789417 := bstep (se 2 (by rfl) ⟨1046031, by rfl⟩ : syracuseStep 2789417 = 2092063) B2092063
theorem B1859611 : Blo 1651525 1859611 := bstep (se 1 (by rfl) ⟨1394708, by rfl⟩ : syracuseStep 1859611 = 2789417) B2789417
theorem B2479481 : Blo 1651525 2479481 := bstep (se 2 (by rfl) ⟨929805, by rfl⟩ : syracuseStep 2479481 = 1859611) B1859611
theorem B1652987 : Blo 1651525 1652987 := bstep (se 1 (by rfl) ⟨1239740, by rfl⟩ : syracuseStep 1652987 = 2479481) B2479481

theorem C0 (j : ℕ) (h1 : 412881 ≤ j) (h2 : j ≤ 413380) : Blo 1651525 (4 * j + 3) := by
  interval_cases j
  · exact B1651527
  · exact B1651531
  · exact B1651535
  · exact B1651539
  · exact B1651543
  · exact B1651547
  · exact B1651551
  · exact B1651555
  · exact B1651559
  · exact B1651563
  · exact B1651567
  · exact B1651571
  · exact B1651575
  · exact B1651579
  · exact B1651583
  · exact B1651587
  · exact B1651591
  · exact B1651595
  · exact B1651599
  · exact B1651603
  · exact B1651607
  · exact B1651611
  · exact B1651615
  · exact B1651619
  · exact B1651623
  · exact B1651627
  · exact B1651631
  · exact B1651635
  · exact B1651639
  · exact B1651643
  · exact B1651647
  · exact B1651651
  · exact B1651655
  · exact B1651659
  · exact B1651663
  · exact B1651667
  · exact B1651671
  · exact B1651675
  · exact B1651679
  · exact B1651683
  · exact B1651687
  · exact B1651691
  · exact B1651695
  · exact B1651699
  · exact B1651703
  · exact B1651707
  · exact B1651711
  · exact B1651715
  · exact B1651719
  · exact B1651723
  · exact B1651727
  · exact B1651731
  · exact B1651735
  · exact B1651739
  · exact B1651743
  · exact B1651747
  · exact B1651751
  · exact B1651755
  · exact B1651759
  · exact B1651763
  · exact B1651767
  · exact B1651771
  · exact B1651775
  · exact B1651779
  · exact B1651783
  · exact B1651787
  · exact B1651791
  · exact B1651795
  · exact B1651799
  · exact B1651803
  · exact B1651807
  · exact B1651811
  · exact B1651815
  · exact B1651819
  · exact B1651823
  · exact B1651827
  · exact B1651831
  · exact B1651835
  · exact B1651839
  · exact B1651843
  · exact B1651847
  · exact B1651851
  · exact B1651855
  · exact B1651859
  · exact B1651863
  · exact B1651867
  · exact B1651871
  · exact B1651875
  · exact B1651879
  · exact B1651883
  · exact B1651887
  · exact B1651891
  · exact B1651895
  · exact B1651899
  · exact B1651903
  · exact B1651907
  · exact B1651911
  · exact B1651915
  · exact B1651919
  · exact B1651923
  · exact B1651927
  · exact B1651931
  · exact B1651935
  · exact B1651939
  · exact B1651943
  · exact B1651947
  · exact B1651951
  · exact B1651955
  · exact B1651959
  · exact B1651963
  · exact B1651967
  · exact B1651971
  · exact B1651975
  · exact B1651979
  · exact B1651983
  · exact B1651987
  · exact B1651991
  · exact B1651995
  · exact B1651999
  · exact B1652003
  · exact B1652007
  · exact B1652011
  · exact B1652015
  · exact B1652019
  · exact B1652023
  · exact B1652027
  · exact B1652031
  · exact B1652035
  · exact B1652039
  · exact B1652043
  · exact B1652047
  · exact B1652051
  · exact B1652055
  · exact B1652059
  · exact B1652063
  · exact B1652067
  · exact B1652071
  · exact B1652075
  · exact B1652079
  · exact B1652083
  · exact B1652087
  · exact B1652091
  · exact B1652095
  · exact B1652099
  · exact B1652103
  · exact B1652107
  · exact B1652111
  · exact B1652115
  · exact B1652119
  · exact B1652123
  · exact B1652127
  · exact B1652131
  · exact B1652135
  · exact B1652139
  · exact B1652143
  · exact B1652147
  · exact B1652151
  · exact B1652155
  · exact B1652159
  · exact B1652163
  · exact B1652167
  · exact B1652171
  · exact B1652175
  · exact B1652179
  · exact B1652183
  · exact B1652187
  · exact B1652191
  · exact B1652195
  · exact B1652199
  · exact B1652203
  · exact B1652207
  · exact B1652211
  · exact B1652215
  · exact B1652219
  · exact B1652223
  · exact B1652227
  · exact B1652231
  · exact B1652235
  · exact B1652239
  · exact B1652243
  · exact B1652247
  · exact B1652251
  · exact B1652255
  · exact B1652259
  · exact B1652263
  · exact B1652267
  · exact B1652271
  · exact B1652275
  · exact B1652279
  · exact B1652283
  · exact B1652287
  · exact B1652291
  · exact B1652295
  · exact B1652299
  · exact B1652303
  · exact B1652307
  · exact B1652311
  · exact B1652315
  · exact B1652319
  · exact B1652323
  · exact B1652327
  · exact B1652331
  · exact B1652335
  · exact B1652339
  · exact B1652343
  · exact B1652347
  · exact B1652351
  · exact B1652355
  · exact B1652359
  · exact B1652363
  · exact B1652367
  · exact B1652371
  · exact B1652375
  · exact B1652379
  · exact B1652383
  · exact B1652387
  · exact B1652391
  · exact B1652395
  · exact B1652399
  · exact B1652403
  · exact B1652407
  · exact B1652411
  · exact B1652415
  · exact B1652419
  · exact B1652423
  · exact B1652427
  · exact B1652431
  · exact B1652435
  · exact B1652439
  · exact B1652443
  · exact B1652447
  · exact B1652451
  · exact B1652455
  · exact B1652459
  · exact B1652463
  · exact B1652467
  · exact B1652471
  · exact B1652475
  · exact B1652479
  · exact B1652483
  · exact B1652487
  · exact B1652491
  · exact B1652495
  · exact B1652499
  · exact B1652503
  · exact B1652507
  · exact B1652511
  · exact B1652515
  · exact B1652519
  · exact B1652523
  · exact B1652527
  · exact B1652531
  · exact B1652535
  · exact B1652539
  · exact B1652543
  · exact B1652547
  · exact B1652551
  · exact B1652555
  · exact B1652559
  · exact B1652563
  · exact B1652567
  · exact B1652571
  · exact B1652575
  · exact B1652579
  · exact B1652583
  · exact B1652587
  · exact B1652591
  · exact B1652595
  · exact B1652599
  · exact B1652603
  · exact B1652607
  · exact B1652611
  · exact B1652615
  · exact B1652619
  · exact B1652623
  · exact B1652627
  · exact B1652631
  · exact B1652635
  · exact B1652639
  · exact B1652643
  · exact B1652647
  · exact B1652651
  · exact B1652655
  · exact B1652659
  · exact B1652663
  · exact B1652667
  · exact B1652671
  · exact B1652675
  · exact B1652679
  · exact B1652683
  · exact B1652687
  · exact B1652691
  · exact B1652695
  · exact B1652699
  · exact B1652703
  · exact B1652707
  · exact B1652711
  · exact B1652715
  · exact B1652719
  · exact B1652723
  · exact B1652727
  · exact B1652731
  · exact B1652735
  · exact B1652739
  · exact B1652743
  · exact B1652747
  · exact B1652751
  · exact B1652755
  · exact B1652759
  · exact B1652763
  · exact B1652767
  · exact B1652771
  · exact B1652775
  · exact B1652779
  · exact B1652783
  · exact B1652787
  · exact B1652791
  · exact B1652795
  · exact B1652799
  · exact B1652803
  · exact B1652807
  · exact B1652811
  · exact B1652815
  · exact B1652819
  · exact B1652823
  · exact B1652827
  · exact B1652831
  · exact B1652835
  · exact B1652839
  · exact B1652843
  · exact B1652847
  · exact B1652851
  · exact B1652855
  · exact B1652859
  · exact B1652863
  · exact B1652867
  · exact B1652871
  · exact B1652875
  · exact B1652879
  · exact B1652883
  · exact B1652887
  · exact B1652891
  · exact B1652895
  · exact B1652899
  · exact B1652903
  · exact B1652907
  · exact B1652911
  · exact B1652915
  · exact B1652919
  · exact B1652923
  · exact B1652927
  · exact B1652931
  · exact B1652935
  · exact B1652939
  · exact B1652943
  · exact B1652947
  · exact B1652951
  · exact B1652955
  · exact B1652959
  · exact B1652963
  · exact B1652967
  · exact B1652971
  · exact B1652975
  · exact B1652979
  · exact B1652983
  · exact B1652987
  · exact B1652991
  · exact B1652995
  · exact B1652999
  · exact B1653003
  · exact B1653007
  · exact B1653011
  · exact B1653015
  · exact B1653019
  · exact B1653023
  · exact B1653027
  · exact B1653031
  · exact B1653035
  · exact B1653039
  · exact B1653043
  · exact B1653047
  · exact B1653051
  · exact B1653055
  · exact B1653059
  · exact B1653063
  · exact B1653067
  · exact B1653071
  · exact B1653075
  · exact B1653079
  · exact B1653083
  · exact B1653087
  · exact B1653091
  · exact B1653095
  · exact B1653099
  · exact B1653103
  · exact B1653107
  · exact B1653111
  · exact B1653115
  · exact B1653119
  · exact B1653123
  · exact B1653127
  · exact B1653131
  · exact B1653135
  · exact B1653139
  · exact B1653143
  · exact B1653147
  · exact B1653151
  · exact B1653155
  · exact B1653159
  · exact B1653163
  · exact B1653167
  · exact B1653171
  · exact B1653175
  · exact B1653179
  · exact B1653183
  · exact B1653187
  · exact B1653191
  · exact B1653195
  · exact B1653199
  · exact B1653203
  · exact B1653207
  · exact B1653211
  · exact B1653215
  · exact B1653219
  · exact B1653223
  · exact B1653227
  · exact B1653231
  · exact B1653235
  · exact B1653239
  · exact B1653243
  · exact B1653247
  · exact B1653251
  · exact B1653255
  · exact B1653259
  · exact B1653263
  · exact B1653267
  · exact B1653271
  · exact B1653275
  · exact B1653279
  · exact B1653283
  · exact B1653287
  · exact B1653291
  · exact B1653295
  · exact B1653299
  · exact B1653303
  · exact B1653307
  · exact B1653311
  · exact B1653315
  · exact B1653319
  · exact B1653323
  · exact B1653327
  · exact B1653331
  · exact B1653335
  · exact B1653339
  · exact B1653343
  · exact B1653347
  · exact B1653351
  · exact B1653355
  · exact B1653359
  · exact B1653363
  · exact B1653367
  · exact B1653371
  · exact B1653375
  · exact B1653379
  · exact B1653383
  · exact B1653387
  · exact B1653391
  · exact B1653395
  · exact B1653399
  · exact B1653403
  · exact B1653407
  · exact B1653411
  · exact B1653415
  · exact B1653419
  · exact B1653423
  · exact B1653427
  · exact B1653431
  · exact B1653435
  · exact B1653439
  · exact B1653443
  · exact B1653447
  · exact B1653451
  · exact B1653455
  · exact B1653459
  · exact B1653463
  · exact B1653467
  · exact B1653471
  · exact B1653475
  · exact B1653479
  · exact B1653483
  · exact B1653487
  · exact B1653491
  · exact B1653495
  · exact B1653499
  · exact B1653503
  · exact B1653507
  · exact B1653511
  · exact B1653515
  · exact B1653519
  · exact B1653523

theorem solution (m : ℕ) (hlo : 1651525 ≤ m) (hhi : m ≤ 1653525) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 412881 ≤ j := by omega
    have hj2 : j ≤ 413380 := by omega
    have hb : Blo 1651525 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
