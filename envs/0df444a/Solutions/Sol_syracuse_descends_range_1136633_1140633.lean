-- Prove2me | solution 1 for syracuse_descends_range_1136633_1140633
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:22:45.094044+00:00
-- url     : https://prove2.me/submissions/8663cc02-b97e-4164-9f02-cb35ddc15910

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


theorem B2162693 : Blo 1136633 2162693 := bbase (se 4 (by rfl) ⟨202752, by rfl⟩ : syracuseStep 2162693 = 405505) (by norm_num)
theorem B1441901 : Blo 1136633 1441901 := bbase (se 3 (by rfl) ⟨270356, by rfl⟩ : syracuseStep 1441901 = 540713) (by norm_num)
theorem B2883701 : Blo 1136633 2883701 := bbase (se 5 (by rfl) ⟨135173, by rfl⟩ : syracuseStep 2883701 = 270347) (by norm_num)
theorem B2162837 : Blo 1136633 2162837 := bbase (se 6 (by rfl) ⟨50691, by rfl⟩ : syracuseStep 2162837 = 101383) (by norm_num)
theorem B21921941 : Blo 1136633 21921941 := bbase (se 6 (by rfl) ⟨513795, by rfl⟩ : syracuseStep 21921941 = 1027591) (by norm_num)
theorem B1441957 : Blo 1136633 1441957 := bbase (se 4 (by rfl) ⟨135183, by rfl⟩ : syracuseStep 1441957 = 270367) (by norm_num)
theorem B1442053 : Blo 1136633 1442053 := bbase (se 4 (by rfl) ⟨135192, by rfl⟩ : syracuseStep 1442053 = 270385) (by norm_num)
theorem B1442225 : Blo 1136633 1442225 := bbase (se 2 (by rfl) ⟨540834, by rfl⟩ : syracuseStep 1442225 = 1081669) (by norm_num)
theorem B2163125 : Blo 1136633 2163125 := bbase (se 5 (by rfl) ⟨101396, by rfl⟩ : syracuseStep 2163125 = 202793) (by norm_num)
theorem B2884045 : Blo 1136633 2884045 := bbase (se 3 (by rfl) ⟨540758, by rfl⟩ : syracuseStep 2884045 = 1081517) (by norm_num)
theorem B1442281 : Blo 1136633 1442281 := bbase (se 2 (by rfl) ⟨540855, by rfl⟩ : syracuseStep 1442281 = 1081711) (by norm_num)
theorem B5767685 : Blo 1136633 5767685 := bbase (se 4 (by rfl) ⟨540720, by rfl⟩ : syracuseStep 5767685 = 1081441) (by norm_num)
theorem B8651285 : Blo 1136633 8651285 := bbase (se 6 (by rfl) ⟨202764, by rfl⟩ : syracuseStep 8651285 = 405529) (by norm_num)
theorem B2884157 : Blo 1136633 2884157 := bbase (se 3 (by rfl) ⟨540779, by rfl⟩ : syracuseStep 2884157 = 1081559) (by norm_num)
theorem B1442377 : Blo 1136633 1442377 := bbase (se 2 (by rfl) ⟨540891, by rfl⟩ : syracuseStep 1442377 = 1081783) (by norm_num)
theorem B2163277 : Blo 1136633 2163277 := bbase (se 3 (by rfl) ⟨405614, by rfl⟩ : syracuseStep 2163277 = 811229) (by norm_num)
theorem B6488693 : Blo 1136633 6488693 := bbase (se 5 (by rfl) ⟨304157, by rfl⟩ : syracuseStep 6488693 = 608315) (by norm_num)
theorem B1540733 : Blo 1136633 1540733 := bbase (se 3 (by rfl) ⟨288887, by rfl⟩ : syracuseStep 1540733 = 577775) (by norm_num)
theorem B4096757 : Blo 1136633 4096757 := bbase (se 5 (by rfl) ⟨192035, by rfl⟩ : syracuseStep 4096757 = 384071) (by norm_num)
theorem B1442549 : Blo 1136633 1442549 := bbase (se 5 (by rfl) ⟨67619, by rfl⟩ : syracuseStep 1442549 = 135239) (by norm_num)
theorem B2884349 : Blo 1136633 2884349 := bbase (se 3 (by rfl) ⟨540815, by rfl⟩ : syracuseStep 2884349 = 1081631) (by norm_num)
theorem B1278733 : Blo 1136633 1278733 := bbase (se 3 (by rfl) ⟨239762, by rfl⟩ : syracuseStep 1278733 = 479525) (by norm_num)
theorem B1442605 : Blo 1136633 1442605 := bbase (se 3 (by rfl) ⟨270488, by rfl⟩ : syracuseStep 1442605 = 540977) (by norm_num)
theorem B1278769 : Blo 1136633 1278769 := bbase (se 2 (by rfl) ⟨479538, by rfl⟩ : syracuseStep 1278769 = 959077) (by norm_num)
theorem B1278805 : Blo 1136633 1278805 := bbase (se 9 (by rfl) ⟨3746, by rfl⟩ : syracuseStep 1278805 = 7493) (by norm_num)
theorem B1278841 : Blo 1136633 1278841 := bbase (se 2 (by rfl) ⟨479565, by rfl⟩ : syracuseStep 1278841 = 959131) (by norm_num)
theorem B2163581 : Blo 1136633 2163581 := bbase (se 3 (by rfl) ⟨405671, by rfl⟩ : syracuseStep 2163581 = 811343) (by norm_num)
theorem B4096901 : Blo 1136633 4096901 := bbase (se 4 (by rfl) ⟨384084, by rfl⟩ : syracuseStep 4096901 = 768169) (by norm_num)
theorem B1442701 : Blo 1136633 1442701 := bbase (se 3 (by rfl) ⟨270506, by rfl⟩ : syracuseStep 1442701 = 541013) (by norm_num)
theorem B1278877 : Blo 1136633 1278877 := bbase (se 3 (by rfl) ⟨239789, by rfl⟩ : syracuseStep 1278877 = 479579) (by norm_num)
theorem B1278913 : Blo 1136633 1278913 := bbase (se 2 (by rfl) ⟨479592, by rfl⟩ : syracuseStep 1278913 = 959185) (by norm_num)
theorem B1278949 : Blo 1136633 1278949 := bbase (se 4 (by rfl) ⟨119901, by rfl⟩ : syracuseStep 1278949 = 239803) (by norm_num)
theorem B1704965 : Blo 1136633 1704965 := bbase (se 4 (by rfl) ⟨159840, by rfl⟩ : syracuseStep 1704965 = 319681) (by norm_num)
theorem B1278985 : Blo 1136633 1278985 := bbase (se 2 (by rfl) ⟨479619, by rfl⟩ : syracuseStep 1278985 = 959239) (by norm_num)
theorem B1704989 : Blo 1136633 1704989 := bbase (se 3 (by rfl) ⟨319685, by rfl⟩ : syracuseStep 1704989 = 639371) (by norm_num)
theorem B1279021 : Blo 1136633 1279021 := bbase (se 3 (by rfl) ⟨239816, by rfl⟩ : syracuseStep 1279021 = 479633) (by norm_num)
theorem B1705013 : Blo 1136633 1705013 := bbase (se 5 (by rfl) ⟨79922, by rfl⟩ : syracuseStep 1705013 = 159845) (by norm_num)
theorem B1442873 : Blo 1136633 1442873 := bbase (se 2 (by rfl) ⟨541077, by rfl⟩ : syracuseStep 1442873 = 1082155) (by norm_num)
theorem B1705037 : Blo 1136633 1705037 := bbase (se 3 (by rfl) ⟨319694, by rfl⟩ : syracuseStep 1705037 = 639389) (by norm_num)
theorem B1279057 : Blo 1136633 1279057 := bbase (se 2 (by rfl) ⟨479646, by rfl⟩ : syracuseStep 1279057 = 959293) (by norm_num)
theorem B2884693 : Blo 1136633 2884693 := bbase (se 8 (by rfl) ⟨16902, by rfl⟩ : syracuseStep 2884693 = 33805) (by norm_num)
theorem B1705061 : Blo 1136633 1705061 := bbase (se 4 (by rfl) ⟨159849, by rfl⟩ : syracuseStep 1705061 = 319699) (by norm_num)
theorem B1442929 : Blo 1136633 1442929 := bbase (se 2 (by rfl) ⟨541098, by rfl⟩ : syracuseStep 1442929 = 1082197) (by norm_num)
theorem B1279093 : Blo 1136633 1279093 := bbase (se 5 (by rfl) ⟨59957, by rfl⟩ : syracuseStep 1279093 = 119915) (by norm_num)
theorem B1705085 : Blo 1136633 1705085 := bbase (se 3 (by rfl) ⟨319703, by rfl⟩ : syracuseStep 1705085 = 639407) (by norm_num)
theorem B1705109 : Blo 1136633 1705109 := bbase (se 6 (by rfl) ⟨39963, by rfl⟩ : syracuseStep 1705109 = 79927) (by norm_num)
theorem B1279129 : Blo 1136633 1279129 := bbase (se 2 (by rfl) ⟨479673, by rfl⟩ : syracuseStep 1279129 = 959347) (by norm_num)
theorem B1705133 : Blo 1136633 1705133 := bbase (se 3 (by rfl) ⟨319712, by rfl⟩ : syracuseStep 1705133 = 639425) (by norm_num)
theorem B1279165 : Blo 1136633 1279165 := bbase (se 3 (by rfl) ⟨239843, by rfl⟩ : syracuseStep 1279165 = 479687) (by norm_num)
theorem B1705157 : Blo 1136633 1705157 := bbase (se 4 (by rfl) ⟨159858, by rfl⟩ : syracuseStep 1705157 = 319717) (by norm_num)
theorem B2884805 : Blo 1136633 2884805 := bbase (se 4 (by rfl) ⟨270450, by rfl⟩ : syracuseStep 2884805 = 540901) (by norm_num)
theorem B1443025 : Blo 1136633 1443025 := bbase (se 2 (by rfl) ⟨541134, by rfl⟩ : syracuseStep 1443025 = 1082269) (by norm_num)
theorem B1705181 : Blo 1136633 1705181 := bbase (se 3 (by rfl) ⟨319721, by rfl⟩ : syracuseStep 1705181 = 639443) (by norm_num)
theorem B1279201 : Blo 1136633 1279201 := bbase (se 2 (by rfl) ⟨479700, by rfl⟩ : syracuseStep 1279201 = 959401) (by norm_num)
theorem B1705205 : Blo 1136633 1705205 := bbase (se 5 (by rfl) ⟨79931, by rfl⟩ : syracuseStep 1705205 = 159863) (by norm_num)
theorem B1279237 : Blo 1136633 1279237 := bbase (se 4 (by rfl) ⟨119928, by rfl⟩ : syracuseStep 1279237 = 239857) (by norm_num)
theorem B1705229 : Blo 1136633 1705229 := bbase (se 3 (by rfl) ⟨319730, by rfl⟩ : syracuseStep 1705229 = 639461) (by norm_num)
theorem B1705253 : Blo 1136633 1705253 := bbase (se 4 (by rfl) ⟨159867, by rfl⟩ : syracuseStep 1705253 = 319735) (by norm_num)
theorem B1279273 : Blo 1136633 1279273 := bbase (se 2 (by rfl) ⟨479727, by rfl⟩ : syracuseStep 1279273 = 959455) (by norm_num)
theorem B1705277 : Blo 1136633 1705277 := bbase (se 3 (by rfl) ⟨319739, by rfl⟩ : syracuseStep 1705277 = 639479) (by norm_num)
theorem B1279309 : Blo 1136633 1279309 := bbase (se 3 (by rfl) ⟨239870, by rfl⟩ : syracuseStep 1279309 = 479741) (by norm_num)
theorem B1705301 : Blo 1136633 1705301 := bbase (se 12 (by rfl) ⟨624, by rfl⟩ : syracuseStep 1705301 = 1249) (by norm_num)
theorem B1705325 : Blo 1136633 1705325 := bbase (se 3 (by rfl) ⟨319748, by rfl⟩ : syracuseStep 1705325 = 639497) (by norm_num)
theorem B1279345 : Blo 1136633 1279345 := bbase (se 2 (by rfl) ⟨479754, by rfl⟩ : syracuseStep 1279345 = 959509) (by norm_num)
theorem B1443197 : Blo 1136633 1443197 := bbase (se 3 (by rfl) ⟨270599, by rfl⟩ : syracuseStep 1443197 = 541199) (by norm_num)
theorem B1705349 : Blo 1136633 1705349 := bbase (se 4 (by rfl) ⟨159876, by rfl⟩ : syracuseStep 1705349 = 319753) (by norm_num)
theorem B2884997 : Blo 1136633 2884997 := bbase (se 4 (by rfl) ⟨270468, by rfl⟩ : syracuseStep 2884997 = 540937) (by norm_num)
theorem B1279381 : Blo 1136633 1279381 := bbase (se 6 (by rfl) ⟨29985, by rfl⟩ : syracuseStep 1279381 = 59971) (by norm_num)
theorem B1705373 : Blo 1136633 1705373 := bbase (se 3 (by rfl) ⟨319757, by rfl⟩ : syracuseStep 1705373 = 639515) (by norm_num)
theorem B1705397 : Blo 1136633 1705397 := bbase (se 5 (by rfl) ⟨79940, by rfl⟩ : syracuseStep 1705397 = 159881) (by norm_num)
theorem B1443253 : Blo 1136633 1443253 := bbase (se 5 (by rfl) ⟨67652, by rfl⟩ : syracuseStep 1443253 = 135305) (by norm_num)
theorem B1279417 : Blo 1136633 1279417 := bbase (se 2 (by rfl) ⟨479781, by rfl⟩ : syracuseStep 1279417 = 959563) (by norm_num)
theorem B1705421 : Blo 1136633 1705421 := bbase (se 3 (by rfl) ⟨319766, by rfl⟩ : syracuseStep 1705421 = 639533) (by norm_num)
theorem B1279453 : Blo 1136633 1279453 := bbase (se 3 (by rfl) ⟨239897, by rfl⟩ : syracuseStep 1279453 = 479795) (by norm_num)
theorem B1705445 : Blo 1136633 1705445 := bbase (se 4 (by rfl) ⟨159885, by rfl⟩ : syracuseStep 1705445 = 319771) (by norm_num)
theorem B1705469 : Blo 1136633 1705469 := bbase (se 3 (by rfl) ⟨319775, by rfl⟩ : syracuseStep 1705469 = 639551) (by norm_num)
theorem B1279489 : Blo 1136633 1279489 := bbase (se 2 (by rfl) ⟨479808, by rfl⟩ : syracuseStep 1279489 = 959617) (by norm_num)
theorem B1705493 : Blo 1136633 1705493 := bbase (se 6 (by rfl) ⟨39972, by rfl⟩ : syracuseStep 1705493 = 79945) (by norm_num)
theorem B1443349 : Blo 1136633 1443349 := bbase (se 6 (by rfl) ⟨33828, by rfl⟩ : syracuseStep 1443349 = 67657) (by norm_num)
theorem B20809237 : Blo 1136633 20809237 := bbase (se 6 (by rfl) ⟨487716, by rfl⟩ : syracuseStep 20809237 = 975433) (by norm_num)
theorem B1279525 : Blo 1136633 1279525 := bbase (se 4 (by rfl) ⟨119955, by rfl⟩ : syracuseStep 1279525 = 239911) (by norm_num)
theorem B1705517 : Blo 1136633 1705517 := bbase (se 3 (by rfl) ⟨319784, by rfl⟩ : syracuseStep 1705517 = 639569) (by norm_num)
theorem B2557493 : Blo 1136633 2557493 := bbase (se 5 (by rfl) ⟨119882, by rfl⟩ : syracuseStep 2557493 = 239765) (by norm_num)
theorem B4326965 : Blo 1136633 4326965 := bbase (se 5 (by rfl) ⟨202826, by rfl⟩ : syracuseStep 4326965 = 405653) (by norm_num)
theorem B1705541 : Blo 1136633 1705541 := bbase (se 4 (by rfl) ⟨159894, by rfl⟩ : syracuseStep 1705541 = 319789) (by norm_num)
theorem B1279561 : Blo 1136633 1279561 := bbase (se 2 (by rfl) ⟨479835, by rfl⟩ : syracuseStep 1279561 = 959671) (by norm_num)
theorem B1214033 : Blo 1136633 1214033 := bbase (se 2 (by rfl) ⟨455262, by rfl⟩ : syracuseStep 1214033 = 910525) (by norm_num)
theorem B1705565 : Blo 1136633 1705565 := bbase (se 3 (by rfl) ⟨319793, by rfl⟩ : syracuseStep 1705565 = 639587) (by norm_num)
theorem B1279597 : Blo 1136633 1279597 := bbase (se 3 (by rfl) ⟨239924, by rfl⟩ : syracuseStep 1279597 = 479849) (by norm_num)
theorem B2164333 : Blo 1136633 2164333 := bbase (se 3 (by rfl) ⟨405812, by rfl⟩ : syracuseStep 2164333 = 811625) (by norm_num)
theorem B1705589 : Blo 1136633 1705589 := bbase (se 5 (by rfl) ⟨79949, by rfl⟩ : syracuseStep 1705589 = 159899) (by norm_num)
theorem B2557565 : Blo 1136633 2557565 := bbase (se 3 (by rfl) ⟨479543, by rfl⟩ : syracuseStep 2557565 = 959087) (by norm_num)
theorem B1705613 : Blo 1136633 1705613 := bbase (se 3 (by rfl) ⟨319802, by rfl⟩ : syracuseStep 1705613 = 639605) (by norm_num)
theorem B1279633 : Blo 1136633 1279633 := bbase (se 2 (by rfl) ⟨479862, by rfl⟩ : syracuseStep 1279633 = 959725) (by norm_num)
theorem B1705637 : Blo 1136633 1705637 := bbase (se 4 (by rfl) ⟨159903, by rfl⟩ : syracuseStep 1705637 = 319807) (by norm_num)
theorem B1279669 : Blo 1136633 1279669 := bbase (se 5 (by rfl) ⟨59984, by rfl⟩ : syracuseStep 1279669 = 119969) (by norm_num)
theorem B1705661 : Blo 1136633 1705661 := bbase (se 3 (by rfl) ⟨319811, by rfl⟩ : syracuseStep 1705661 = 639623) (by norm_num)
theorem B1443521 : Blo 1136633 1443521 := bbase (se 2 (by rfl) ⟨541320, by rfl⟩ : syracuseStep 1443521 = 1082641) (by norm_num)
theorem B2557637 : Blo 1136633 2557637 := bbase (se 4 (by rfl) ⟨239778, by rfl⟩ : syracuseStep 2557637 = 479557) (by norm_num)
theorem B1705685 : Blo 1136633 1705685 := bbase (se 7 (by rfl) ⟨19988, by rfl⟩ : syracuseStep 1705685 = 39977) (by norm_num)
theorem B15599317 : Blo 1136633 15599317 := bbase (se 7 (by rfl) ⟨182804, by rfl⟩ : syracuseStep 15599317 = 365609) (by norm_num)
theorem B1279705 : Blo 1136633 1279705 := bbase (se 2 (by rfl) ⟨479889, by rfl⟩ : syracuseStep 1279705 = 959779) (by norm_num)
theorem B2885341 : Blo 1136633 2885341 := bbase (se 3 (by rfl) ⟨541001, by rfl⟩ : syracuseStep 2885341 = 1082003) (by norm_num)
theorem B1705709 : Blo 1136633 1705709 := bbase (se 3 (by rfl) ⟨319820, by rfl⟩ : syracuseStep 1705709 = 639641) (by norm_num)
theorem B1443577 : Blo 1136633 1443577 := bbase (se 2 (by rfl) ⟨541341, by rfl⟩ : syracuseStep 1443577 = 1082683) (by norm_num)
theorem B1279741 : Blo 1136633 1279741 := bbase (se 3 (by rfl) ⟨239951, by rfl⟩ : syracuseStep 1279741 = 479903) (by norm_num)
theorem B2164477 : Blo 1136633 2164477 := bbase (se 3 (by rfl) ⟨405839, by rfl⟩ : syracuseStep 2164477 = 811679) (by norm_num)
theorem B1705733 : Blo 1136633 1705733 := bbase (se 4 (by rfl) ⟨159912, by rfl⟩ : syracuseStep 1705733 = 319825) (by norm_num)
theorem B2557709 : Blo 1136633 2557709 := bbase (se 3 (by rfl) ⟨479570, by rfl⟩ : syracuseStep 2557709 = 959141) (by norm_num)
theorem B5768981 : Blo 1136633 5768981 := bbase (se 6 (by rfl) ⟨135210, by rfl⟩ : syracuseStep 5768981 = 270421) (by norm_num)
theorem B1705757 : Blo 1136633 1705757 := bbase (se 3 (by rfl) ⟨319829, by rfl⟩ : syracuseStep 1705757 = 639659) (by norm_num)
theorem B1279777 : Blo 1136633 1279777 := bbase (se 2 (by rfl) ⟨479916, by rfl⟩ : syracuseStep 1279777 = 959833) (by norm_num)
theorem B1705781 : Blo 1136633 1705781 := bbase (se 5 (by rfl) ⟨79958, by rfl⟩ : syracuseStep 1705781 = 159917) (by norm_num)
theorem B1279813 : Blo 1136633 1279813 := bbase (se 4 (by rfl) ⟨119982, by rfl⟩ : syracuseStep 1279813 = 239965) (by norm_num)
theorem B1214281 : Blo 1136633 1214281 := bbase (se 2 (by rfl) ⟨455355, by rfl⟩ : syracuseStep 1214281 = 910711) (by norm_num)
theorem B1705805 : Blo 1136633 1705805 := bbase (se 3 (by rfl) ⟨319838, by rfl⟩ : syracuseStep 1705805 = 639677) (by norm_num)
theorem B2885453 : Blo 1136633 2885453 := bbase (se 3 (by rfl) ⟨541022, by rfl⟩ : syracuseStep 2885453 = 1082045) (by norm_num)
theorem B2557781 : Blo 1136633 2557781 := bbase (se 9 (by rfl) ⟨7493, by rfl⟩ : syracuseStep 2557781 = 14987) (by norm_num)
theorem B4327253 : Blo 1136633 4327253 := bbase (se 9 (by rfl) ⟨12677, by rfl⟩ : syracuseStep 4327253 = 25355) (by norm_num)
theorem B1705829 : Blo 1136633 1705829 := bbase (se 4 (by rfl) ⟨159921, by rfl⟩ : syracuseStep 1705829 = 319843) (by norm_num)
theorem B1279849 : Blo 1136633 1279849 := bbase (se 2 (by rfl) ⟨479943, by rfl⟩ : syracuseStep 1279849 = 959887) (by norm_num)
theorem B1705853 : Blo 1136633 1705853 := bbase (se 3 (by rfl) ⟨319847, by rfl⟩ : syracuseStep 1705853 = 639695) (by norm_num)
theorem B2918285 : Blo 1136633 2918285 := bbase (se 3 (by rfl) ⟨547178, by rfl⟩ : syracuseStep 2918285 = 1094357) (by norm_num)
theorem B1279885 : Blo 1136633 1279885 := bbase (se 3 (by rfl) ⟨239978, by rfl⟩ : syracuseStep 1279885 = 479957) (by norm_num)
theorem B1705877 : Blo 1136633 1705877 := bbase (se 6 (by rfl) ⟨39981, by rfl⟩ : syracuseStep 1705877 = 79963) (by norm_num)
theorem B2557853 : Blo 1136633 2557853 := bbase (se 3 (by rfl) ⟨479597, by rfl⟩ : syracuseStep 2557853 = 959195) (by norm_num)
theorem B2164637 : Blo 1136633 2164637 := bbase (se 3 (by rfl) ⟨405869, by rfl⟩ : syracuseStep 2164637 = 811739) (by norm_num)
theorem B1705901 : Blo 1136633 1705901 := bbase (se 3 (by rfl) ⟨319856, by rfl⟩ : syracuseStep 1705901 = 639713) (by norm_num)
theorem B1279921 : Blo 1136633 1279921 := bbase (se 2 (by rfl) ⟨479970, by rfl⟩ : syracuseStep 1279921 = 959941) (by norm_num)
theorem B1705925 : Blo 1136633 1705925 := bbase (se 4 (by rfl) ⟨159930, by rfl⟩ : syracuseStep 1705925 = 319861) (by norm_num)
theorem B5998549 : Blo 1136633 5998549 := bbase (se 7 (by rfl) ⟨70295, by rfl⟩ : syracuseStep 5998549 = 140591) (by norm_num)
theorem B1279957 : Blo 1136633 1279957 := bbase (se 7 (by rfl) ⟨14999, by rfl⟩ : syracuseStep 1279957 = 29999) (by norm_num)
theorem B1705949 : Blo 1136633 1705949 := bbase (se 3 (by rfl) ⟨319865, by rfl⟩ : syracuseStep 1705949 = 639731) (by norm_num)
theorem B2557925 : Blo 1136633 2557925 := bbase (se 4 (by rfl) ⟨239805, by rfl⟩ : syracuseStep 2557925 = 479611) (by norm_num)
theorem B1705973 : Blo 1136633 1705973 := bbase (se 5 (by rfl) ⟨79967, by rfl⟩ : syracuseStep 1705973 = 159935) (by norm_num)
theorem B1279993 : Blo 1136633 1279993 := bbase (se 2 (by rfl) ⟨479997, by rfl⟩ : syracuseStep 1279993 = 959995) (by norm_num)
theorem B1640461 : Blo 1136633 1640461 := bbase (se 3 (by rfl) ⟨307586, by rfl⟩ : syracuseStep 1640461 = 615173) (by norm_num)
theorem B1705997 : Blo 1136633 1705997 := bbase (se 3 (by rfl) ⟨319874, by rfl⟩ : syracuseStep 1705997 = 639749) (by norm_num)
theorem B2885645 : Blo 1136633 2885645 := bbase (se 3 (by rfl) ⟨541058, by rfl⟩ : syracuseStep 2885645 = 1082117) (by norm_num)
theorem B3246101 : Blo 1136633 3246101 := bbase (se 6 (by rfl) ⟨76080, by rfl⟩ : syracuseStep 3246101 = 152161) (by norm_num)
theorem B1280029 : Blo 1136633 1280029 := bbase (se 3 (by rfl) ⟨240005, by rfl⟩ : syracuseStep 1280029 = 480011) (by norm_num)
theorem B1706021 : Blo 1136633 1706021 := bbase (se 4 (by rfl) ⟨159939, by rfl⟩ : syracuseStep 1706021 = 319879) (by norm_num)
theorem B2557997 : Blo 1136633 2557997 := bbase (se 3 (by rfl) ⟨479624, by rfl⟩ : syracuseStep 2557997 = 959249) (by norm_num)
theorem B2164781 : Blo 1136633 2164781 := bbase (se 3 (by rfl) ⟨405896, by rfl⟩ : syracuseStep 2164781 = 811793) (by norm_num)
theorem B1706045 : Blo 1136633 1706045 := bbase (se 3 (by rfl) ⟨319883, by rfl⟩ : syracuseStep 1706045 = 639767) (by norm_num)
theorem B1280065 : Blo 1136633 1280065 := bbase (se 2 (by rfl) ⟨480024, by rfl⟩ : syracuseStep 1280065 = 960049) (by norm_num)
theorem B1706069 : Blo 1136633 1706069 := bbase (se 8 (by rfl) ⟨9996, by rfl⟩ : syracuseStep 1706069 = 19993) (by norm_num)
theorem B1280101 : Blo 1136633 1280101 := bbase (se 4 (by rfl) ⟨120009, by rfl⟩ : syracuseStep 1280101 = 240019) (by norm_num)
theorem B1706093 : Blo 1136633 1706093 := bbase (se 3 (by rfl) ⟨319892, by rfl⟩ : syracuseStep 1706093 = 639785) (by norm_num)
theorem B2558069 : Blo 1136633 2558069 := bbase (se 5 (by rfl) ⟨119909, by rfl⟩ : syracuseStep 2558069 = 239819) (by norm_num)
theorem B1706117 : Blo 1136633 1706117 := bbase (se 4 (by rfl) ⟨159948, by rfl⟩ : syracuseStep 1706117 = 319897) (by norm_num)
theorem B1280137 : Blo 1136633 1280137 := bbase (se 2 (by rfl) ⟨480051, by rfl⟩ : syracuseStep 1280137 = 960103) (by norm_num)
theorem B1706141 : Blo 1136633 1706141 := bbase (se 3 (by rfl) ⟨319901, by rfl⟩ : syracuseStep 1706141 = 639803) (by norm_num)
theorem B1280173 : Blo 1136633 1280173 := bbase (se 3 (by rfl) ⟨240032, by rfl⟩ : syracuseStep 1280173 = 480065) (by norm_num)
theorem B1706165 : Blo 1136633 1706165 := bbase (se 5 (by rfl) ⟨79976, by rfl⟩ : syracuseStep 1706165 = 159953) (by norm_num)
theorem B2558141 : Blo 1136633 2558141 := bbase (se 3 (by rfl) ⟨479651, by rfl⟩ : syracuseStep 2558141 = 959303) (by norm_num)
theorem B1706189 : Blo 1136633 1706189 := bbase (se 3 (by rfl) ⟨319910, by rfl⟩ : syracuseStep 1706189 = 639821) (by norm_num)
theorem B1280209 : Blo 1136633 1280209 := bbase (se 2 (by rfl) ⟨480078, by rfl⟩ : syracuseStep 1280209 = 960157) (by norm_num)
theorem B1706213 : Blo 1136633 1706213 := bbase (se 4 (by rfl) ⟨159957, by rfl⟩ : syracuseStep 1706213 = 319915) (by norm_num)
theorem B1280245 : Blo 1136633 1280245 := bbase (se 5 (by rfl) ⟨60011, by rfl⟩ : syracuseStep 1280245 = 120023) (by norm_num)
theorem B1706237 : Blo 1136633 1706237 := bbase (se 3 (by rfl) ⟨319919, by rfl⟩ : syracuseStep 1706237 = 639839) (by norm_num)
theorem B2558213 : Blo 1136633 2558213 := bbase (se 4 (by rfl) ⟨239832, by rfl⟩ : syracuseStep 2558213 = 479665) (by norm_num)
theorem B1214725 : Blo 1136633 1214725 := bbase (se 4 (by rfl) ⟨113880, by rfl⟩ : syracuseStep 1214725 = 227761) (by norm_num)
theorem B1706261 : Blo 1136633 1706261 := bbase (se 6 (by rfl) ⟨39990, by rfl⟩ : syracuseStep 1706261 = 79981) (by norm_num)
theorem B1280281 : Blo 1136633 1280281 := bbase (se 2 (by rfl) ⟨480105, by rfl⟩ : syracuseStep 1280281 = 960211) (by norm_num)
theorem B1706285 : Blo 1136633 1706285 := bbase (se 3 (by rfl) ⟨319928, by rfl⟩ : syracuseStep 1706285 = 639857) (by norm_num)
theorem B3836213 : Blo 1136633 3836213 := bbase (se 5 (by rfl) ⟨179822, by rfl⟩ : syracuseStep 3836213 = 359645) (by norm_num)
theorem B1280317 : Blo 1136633 1280317 := bbase (se 3 (by rfl) ⟨240059, by rfl⟩ : syracuseStep 1280317 = 480119) (by norm_num)
theorem B1214785 : Blo 1136633 1214785 := bbase (se 2 (by rfl) ⟨455544, by rfl⟩ : syracuseStep 1214785 = 911089) (by norm_num)
theorem B1706309 : Blo 1136633 1706309 := bbase (se 4 (by rfl) ⟨159966, by rfl⟩ : syracuseStep 1706309 = 319933) (by norm_num)
theorem B2558285 : Blo 1136633 2558285 := bbase (se 3 (by rfl) ⟨479678, by rfl⟩ : syracuseStep 2558285 = 959357) (by norm_num)
theorem B2165069 : Blo 1136633 2165069 := bbase (se 3 (by rfl) ⟨405950, by rfl⟩ : syracuseStep 2165069 = 811901) (by norm_num)
theorem B1706333 : Blo 1136633 1706333 := bbase (se 3 (by rfl) ⟨319937, by rfl⟩ : syracuseStep 1706333 = 639875) (by norm_num)
theorem B1280353 : Blo 1136633 1280353 := bbase (se 2 (by rfl) ⟨480132, by rfl⟩ : syracuseStep 1280353 = 960265) (by norm_num)
theorem B2885989 : Blo 1136633 2885989 := bbase (se 4 (by rfl) ⟨270561, by rfl⟩ : syracuseStep 2885989 = 541123) (by norm_num)
theorem B1706357 : Blo 1136633 1706357 := bbase (se 5 (by rfl) ⟨79985, by rfl⟩ : syracuseStep 1706357 = 159971) (by norm_num)
theorem B1280389 : Blo 1136633 1280389 := bbase (se 4 (by rfl) ⟨120036, by rfl⟩ : syracuseStep 1280389 = 240073) (by norm_num)
theorem B1706381 : Blo 1136633 1706381 := bbase (se 3 (by rfl) ⟨319946, by rfl⟩ : syracuseStep 1706381 = 639893) (by norm_num)
theorem B2558357 : Blo 1136633 2558357 := bbase (se 6 (by rfl) ⟨59961, by rfl⟩ : syracuseStep 2558357 = 119923) (by norm_num)
theorem B3082645 : Blo 1136633 3082645 := bbase (se 6 (by rfl) ⟨72249, by rfl⟩ : syracuseStep 3082645 = 144499) (by norm_num)
theorem B1706405 : Blo 1136633 1706405 := bbase (se 4 (by rfl) ⟨159975, by rfl⟩ : syracuseStep 1706405 = 319951) (by norm_num)
theorem B1280425 : Blo 1136633 1280425 := bbase (se 2 (by rfl) ⟨480159, by rfl⟩ : syracuseStep 1280425 = 960319) (by norm_num)
theorem B1706429 : Blo 1136633 1706429 := bbase (se 3 (by rfl) ⟨319955, by rfl⟩ : syracuseStep 1706429 = 639911) (by norm_num)
theorem B1280461 : Blo 1136633 1280461 := bbase (se 3 (by rfl) ⟨240086, by rfl⟩ : syracuseStep 1280461 = 480173) (by norm_num)
theorem B1706453 : Blo 1136633 1706453 := bbase (se 7 (by rfl) ⟨19997, by rfl⟩ : syracuseStep 1706453 = 39995) (by norm_num)
theorem B2886101 : Blo 1136633 2886101 := bbase (se 7 (by rfl) ⟨33821, by rfl⟩ : syracuseStep 2886101 = 67643) (by norm_num)
theorem B2558429 : Blo 1136633 2558429 := bbase (se 3 (by rfl) ⟨479705, by rfl⟩ : syracuseStep 2558429 = 959411) (by norm_num)
theorem B2165221 : Blo 1136633 2165221 := bbase (se 4 (by rfl) ⟨202989, by rfl⟩ : syracuseStep 2165221 = 405979) (by norm_num)
theorem B1706477 : Blo 1136633 1706477 := bbase (se 3 (by rfl) ⟨319964, by rfl⟩ : syracuseStep 1706477 = 639929) (by norm_num)
theorem B1280497 : Blo 1136633 1280497 := bbase (se 2 (by rfl) ⟨480186, by rfl⟩ : syracuseStep 1280497 = 960373) (by norm_num)
theorem B1706501 : Blo 1136633 1706501 := bbase (se 4 (by rfl) ⟨159984, by rfl⟩ : syracuseStep 1706501 = 319969) (by norm_num)
theorem B1280533 : Blo 1136633 1280533 := bbase (se 6 (by rfl) ⟨30012, by rfl⟩ : syracuseStep 1280533 = 60025) (by norm_num)
theorem B1706525 : Blo 1136633 1706525 := bbase (se 3 (by rfl) ⟨319973, by rfl⟩ : syracuseStep 1706525 = 639947) (by norm_num)
theorem B2558501 : Blo 1136633 2558501 := bbase (se 4 (by rfl) ⟨239859, by rfl⟩ : syracuseStep 2558501 = 479719) (by norm_num)
theorem B1706549 : Blo 1136633 1706549 := bbase (se 5 (by rfl) ⟨79994, by rfl⟩ : syracuseStep 1706549 = 159989) (by norm_num)
theorem B1280569 : Blo 1136633 1280569 := bbase (se 2 (by rfl) ⟨480213, by rfl⟩ : syracuseStep 1280569 = 960427) (by norm_num)
theorem B1706573 : Blo 1136633 1706573 := bbase (se 3 (by rfl) ⟨319982, by rfl⟩ : syracuseStep 1706573 = 639965) (by norm_num)
theorem B1280605 : Blo 1136633 1280605 := bbase (se 3 (by rfl) ⟨240113, by rfl⟩ : syracuseStep 1280605 = 480227) (by norm_num)
theorem B1706597 : Blo 1136633 1706597 := bbase (se 4 (by rfl) ⟨159993, by rfl⟩ : syracuseStep 1706597 = 319987) (by norm_num)
theorem B2558573 : Blo 1136633 2558573 := bbase (se 3 (by rfl) ⟨479732, by rfl⟩ : syracuseStep 2558573 = 959465) (by norm_num)
theorem B1706621 : Blo 1136633 1706621 := bbase (se 3 (by rfl) ⟨319991, by rfl⟩ : syracuseStep 1706621 = 639983) (by norm_num)
theorem B1215101 : Blo 1136633 1215101 := bbase (se 3 (by rfl) ⟨227831, by rfl⟩ : syracuseStep 1215101 = 455663) (by norm_num)
theorem B1280641 : Blo 1136633 1280641 := bbase (se 2 (by rfl) ⟨480240, by rfl⟩ : syracuseStep 1280641 = 960481) (by norm_num)
theorem B1706645 : Blo 1136633 1706645 := bbase (se 6 (by rfl) ⟨39999, by rfl⟩ : syracuseStep 1706645 = 79999) (by norm_num)
theorem B2886293 : Blo 1136633 2886293 := bbase (se 6 (by rfl) ⟨67647, by rfl⟩ : syracuseStep 2886293 = 135295) (by norm_num)
theorem B1280677 : Blo 1136633 1280677 := bbase (se 4 (by rfl) ⟨120063, by rfl⟩ : syracuseStep 1280677 = 240127) (by norm_num)
theorem B1706669 : Blo 1136633 1706669 := bbase (se 3 (by rfl) ⟨320000, by rfl⟩ : syracuseStep 1706669 = 640001) (by norm_num)
theorem B2558645 : Blo 1136633 2558645 := bbase (se 5 (by rfl) ⟨119936, by rfl⟩ : syracuseStep 2558645 = 239873) (by norm_num)
theorem B1706693 : Blo 1136633 1706693 := bbase (se 4 (by rfl) ⟨160002, by rfl⟩ : syracuseStep 1706693 = 320005) (by norm_num)
theorem B1280713 : Blo 1136633 1280713 := bbase (se 2 (by rfl) ⟨480267, by rfl⟩ : syracuseStep 1280713 = 960535) (by norm_num)
theorem B1706717 : Blo 1136633 1706717 := bbase (se 3 (by rfl) ⟨320009, by rfl⟩ : syracuseStep 1706717 = 640019) (by norm_num)
theorem B3836645 : Blo 1136633 3836645 := bbase (se 4 (by rfl) ⟨359685, by rfl⟩ : syracuseStep 3836645 = 719371) (by norm_num)
theorem B1280749 : Blo 1136633 1280749 := bbase (se 3 (by rfl) ⟨240140, by rfl⟩ : syracuseStep 1280749 = 480281) (by norm_num)
theorem B1706741 : Blo 1136633 1706741 := bbase (se 5 (by rfl) ⟨80003, by rfl⟩ : syracuseStep 1706741 = 160007) (by norm_num)
theorem B2558717 : Blo 1136633 2558717 := bbase (se 3 (by rfl) ⟨479759, by rfl⟩ : syracuseStep 2558717 = 959519) (by norm_num)
theorem B1706765 : Blo 1136633 1706765 := bbase (se 3 (by rfl) ⟨320018, by rfl⟩ : syracuseStep 1706765 = 640037) (by norm_num)
theorem B1280785 : Blo 1136633 1280785 := bbase (se 2 (by rfl) ⟨480294, by rfl⟩ : syracuseStep 1280785 = 960589) (by norm_num)
theorem B1706789 : Blo 1136633 1706789 := bbase (se 4 (by rfl) ⟨160011, by rfl⟩ : syracuseStep 1706789 = 320023) (by norm_num)
theorem B1280821 : Blo 1136633 1280821 := bbase (se 5 (by rfl) ⟨60038, by rfl⟩ : syracuseStep 1280821 = 120077) (by norm_num)
theorem B1706813 : Blo 1136633 1706813 := bbase (se 3 (by rfl) ⟨320027, by rfl⟩ : syracuseStep 1706813 = 640055) (by norm_num)
theorem B2558789 : Blo 1136633 2558789 := bbase (se 4 (by rfl) ⟨239886, by rfl⟩ : syracuseStep 2558789 = 479773) (by norm_num)
theorem B2427725 : Blo 1136633 2427725 := bbase (se 3 (by rfl) ⟨455198, by rfl⟩ : syracuseStep 2427725 = 910397) (by norm_num)
theorem B1706837 : Blo 1136633 1706837 := bbase (se 9 (by rfl) ⟨5000, by rfl⟩ : syracuseStep 1706837 = 10001) (by norm_num)
theorem B1280857 : Blo 1136633 1280857 := bbase (se 2 (by rfl) ⟨480321, by rfl⟩ : syracuseStep 1280857 = 960643) (by norm_num)
theorem B1706861 : Blo 1136633 1706861 := bbase (se 3 (by rfl) ⟨320036, by rfl⟩ : syracuseStep 1706861 = 640073) (by norm_num)
theorem B1280893 : Blo 1136633 1280893 := bbase (se 3 (by rfl) ⟨240167, by rfl⟩ : syracuseStep 1280893 = 480335) (by norm_num)
theorem B1706885 : Blo 1136633 1706885 := bbase (se 4 (by rfl) ⟨160020, by rfl⟩ : syracuseStep 1706885 = 320041) (by norm_num)
theorem B2558861 : Blo 1136633 2558861 := bbase (se 3 (by rfl) ⟨479786, by rfl⟩ : syracuseStep 2558861 = 959573) (by norm_num)
theorem B1706909 : Blo 1136633 1706909 := bbase (se 3 (by rfl) ⟨320045, by rfl⟩ : syracuseStep 1706909 = 640091) (by norm_num)
theorem B1280929 : Blo 1136633 1280929 := bbase (se 2 (by rfl) ⟨480348, by rfl⟩ : syracuseStep 1280929 = 960697) (by norm_num)
theorem B1706933 : Blo 1136633 1706933 := bbase (se 5 (by rfl) ⟨80012, by rfl⟩ : syracuseStep 1706933 = 160025) (by norm_num)
theorem B1280965 : Blo 1136633 1280965 := bbase (se 4 (by rfl) ⟨120090, by rfl⟩ : syracuseStep 1280965 = 240181) (by norm_num)
theorem B1706957 : Blo 1136633 1706957 := bbase (se 3 (by rfl) ⟨320054, by rfl⟩ : syracuseStep 1706957 = 640109) (by norm_num)
theorem B2558933 : Blo 1136633 2558933 := bbase (se 7 (by rfl) ⟨29987, by rfl⟩ : syracuseStep 2558933 = 59975) (by norm_num)
theorem B1706981 : Blo 1136633 1706981 := bbase (se 4 (by rfl) ⟨160029, by rfl⟩ : syracuseStep 1706981 = 320059) (by norm_num)
theorem B1281001 : Blo 1136633 1281001 := bbase (se 2 (by rfl) ⟨480375, by rfl⟩ : syracuseStep 1281001 = 960751) (by norm_num)
theorem B2886637 : Blo 1136633 2886637 := bbase (se 3 (by rfl) ⟨541244, by rfl⟩ : syracuseStep 2886637 = 1082489) (by norm_num)
theorem B4328437 : Blo 1136633 4328437 := bbase (se 5 (by rfl) ⟨202895, by rfl⟩ : syracuseStep 4328437 = 405791) (by norm_num)
theorem B1707005 : Blo 1136633 1707005 := bbase (se 3 (by rfl) ⟨320063, by rfl⟩ : syracuseStep 1707005 = 640127) (by norm_num)
theorem B1281037 : Blo 1136633 1281037 := bbase (se 3 (by rfl) ⟨240194, by rfl⟩ : syracuseStep 1281037 = 480389) (by norm_num)
theorem B1707029 : Blo 1136633 1707029 := bbase (se 6 (by rfl) ⟨40008, by rfl⟩ : syracuseStep 1707029 = 80017) (by norm_num)
theorem B2559005 : Blo 1136633 2559005 := bbase (se 3 (by rfl) ⟨479813, by rfl⟩ : syracuseStep 2559005 = 959627) (by norm_num)
theorem B5770277 : Blo 1136633 5770277 := bbase (se 4 (by rfl) ⟨540963, by rfl⟩ : syracuseStep 5770277 = 1081927) (by norm_num)
theorem B1707053 : Blo 1136633 1707053 := bbase (se 3 (by rfl) ⟨320072, by rfl⟩ : syracuseStep 1707053 = 640145) (by norm_num)
theorem B1281073 : Blo 1136633 1281073 := bbase (se 2 (by rfl) ⟨480402, by rfl⟩ : syracuseStep 1281073 = 960805) (by norm_num)
theorem B1215545 : Blo 1136633 1215545 := bbase (se 2 (by rfl) ⟨455829, by rfl⟩ : syracuseStep 1215545 = 911659) (by norm_num)
theorem B1707077 : Blo 1136633 1707077 := bbase (se 4 (by rfl) ⟨160038, by rfl⟩ : syracuseStep 1707077 = 320077) (by norm_num)
theorem B1281109 : Blo 1136633 1281109 := bbase (se 8 (by rfl) ⟨7506, by rfl⟩ : syracuseStep 1281109 = 15013) (by norm_num)
theorem B1707101 : Blo 1136633 1707101 := bbase (se 3 (by rfl) ⟨320081, by rfl⟩ : syracuseStep 1707101 = 640163) (by norm_num)
theorem B2886749 : Blo 1136633 2886749 := bbase (se 3 (by rfl) ⟨541265, by rfl⟩ : syracuseStep 2886749 = 1082531) (by norm_num)
theorem B2559077 : Blo 1136633 2559077 := bbase (se 4 (by rfl) ⟨239913, by rfl⟩ : syracuseStep 2559077 = 479827) (by norm_num)
theorem B1707125 : Blo 1136633 1707125 := bbase (se 5 (by rfl) ⟨80021, by rfl⟩ : syracuseStep 1707125 = 160043) (by norm_num)
theorem B1215605 : Blo 1136633 1215605 := bbase (se 5 (by rfl) ⟨56981, by rfl⟩ : syracuseStep 1215605 = 113963) (by norm_num)
theorem B1281145 : Blo 1136633 1281145 := bbase (se 2 (by rfl) ⟨480429, by rfl⟩ : syracuseStep 1281145 = 960859) (by norm_num)
theorem B1707149 : Blo 1136633 1707149 := bbase (se 3 (by rfl) ⟨320090, by rfl⟩ : syracuseStep 1707149 = 640181) (by norm_num)
theorem B3837077 : Blo 1136633 3837077 := bbase (se 6 (by rfl) ⟨89931, by rfl⟩ : syracuseStep 3837077 = 179863) (by norm_num)
theorem B1281181 : Blo 1136633 1281181 := bbase (se 3 (by rfl) ⟨240221, by rfl⟩ : syracuseStep 1281181 = 480443) (by norm_num)
theorem B1707173 : Blo 1136633 1707173 := bbase (se 4 (by rfl) ⟨160047, by rfl⟩ : syracuseStep 1707173 = 320095) (by norm_num)
theorem B2559149 : Blo 1136633 2559149 := bbase (se 3 (by rfl) ⟨479840, by rfl⟩ : syracuseStep 2559149 = 959681) (by norm_num)
theorem B3247285 : Blo 1136633 3247285 := bbase (se 5 (by rfl) ⟨152216, by rfl⟩ : syracuseStep 3247285 = 304433) (by norm_num)
theorem B1707197 : Blo 1136633 1707197 := bbase (se 3 (by rfl) ⟨320099, by rfl⟩ : syracuseStep 1707197 = 640199) (by norm_num)
theorem B1281217 : Blo 1136633 1281217 := bbase (se 2 (by rfl) ⟨480456, by rfl⟩ : syracuseStep 1281217 = 960913) (by norm_num)
theorem B1707221 : Blo 1136633 1707221 := bbase (se 7 (by rfl) ⟨20006, by rfl⟩ : syracuseStep 1707221 = 40013) (by norm_num)
theorem B1281253 : Blo 1136633 1281253 := bbase (se 4 (by rfl) ⟨120117, by rfl⟩ : syracuseStep 1281253 = 240235) (by norm_num)
theorem B1707245 : Blo 1136633 1707245 := bbase (se 3 (by rfl) ⟨320108, by rfl⟩ : syracuseStep 1707245 = 640217) (by norm_num)
theorem B2559221 : Blo 1136633 2559221 := bbase (se 5 (by rfl) ⟨119963, by rfl⟩ : syracuseStep 2559221 = 239927) (by norm_num)
theorem B1215733 : Blo 1136633 1215733 := bbase (se 5 (by rfl) ⟨56987, by rfl⟩ : syracuseStep 1215733 = 113975) (by norm_num)
theorem B1707269 : Blo 1136633 1707269 := bbase (se 4 (by rfl) ⟨160056, by rfl⟩ : syracuseStep 1707269 = 320113) (by norm_num)
theorem B1281289 : Blo 1136633 1281289 := bbase (se 2 (by rfl) ⟨480483, by rfl⟩ : syracuseStep 1281289 = 960967) (by norm_num)
theorem B1707293 : Blo 1136633 1707293 := bbase (se 3 (by rfl) ⟨320117, by rfl⟩ : syracuseStep 1707293 = 640235) (by norm_num)
theorem B2886941 : Blo 1136633 2886941 := bbase (se 3 (by rfl) ⟨541301, by rfl⟩ : syracuseStep 2886941 = 1082603) (by norm_num)
theorem B4328741 : Blo 1136633 4328741 := bbase (se 4 (by rfl) ⟨405819, by rfl⟩ : syracuseStep 4328741 = 811639) (by norm_num)
theorem B1281325 : Blo 1136633 1281325 := bbase (se 3 (by rfl) ⟨240248, by rfl⟩ : syracuseStep 1281325 = 480497) (by norm_num)
theorem B1707317 : Blo 1136633 1707317 := bbase (se 5 (by rfl) ⟨80030, by rfl⟩ : syracuseStep 1707317 = 160061) (by norm_num)
theorem B2559293 : Blo 1136633 2559293 := bbase (se 3 (by rfl) ⟨479867, by rfl⟩ : syracuseStep 2559293 = 959735) (by norm_num)
theorem B1707341 : Blo 1136633 1707341 := bbase (se 3 (by rfl) ⟨320126, by rfl⟩ : syracuseStep 1707341 = 640253) (by norm_num)
theorem B1281361 : Blo 1136633 1281361 := bbase (se 2 (by rfl) ⟨480510, by rfl⟩ : syracuseStep 1281361 = 961021) (by norm_num)
theorem B3247445 : Blo 1136633 3247445 := bbase (se 11 (by rfl) ⟨2378, by rfl⟩ : syracuseStep 3247445 = 4757) (by norm_num)
theorem B1707365 : Blo 1136633 1707365 := bbase (se 4 (by rfl) ⟨160065, by rfl⟩ : syracuseStep 1707365 = 320131) (by norm_num)
theorem B2461037 : Blo 1136633 2461037 := bbase (se 3 (by rfl) ⟨461444, by rfl⟩ : syracuseStep 2461037 = 922889) (by norm_num)
theorem B1281397 : Blo 1136633 1281397 := bbase (se 5 (by rfl) ⟨60065, by rfl⟩ : syracuseStep 1281397 = 120131) (by norm_num)
theorem B5475701 : Blo 1136633 5475701 := bbase (se 5 (by rfl) ⟨256673, by rfl⟩ : syracuseStep 5475701 = 513347) (by norm_num)
theorem B11701621 : Blo 1136633 11701621 := bbase (se 5 (by rfl) ⟨548513, by rfl⟩ : syracuseStep 11701621 = 1097027) (by norm_num)
theorem B1707389 : Blo 1136633 1707389 := bbase (se 3 (by rfl) ⟨320135, by rfl⟩ : syracuseStep 1707389 = 640271) (by norm_num)
theorem B2559365 : Blo 1136633 2559365 := bbase (se 4 (by rfl) ⟨239940, by rfl⟩ : syracuseStep 2559365 = 479881) (by norm_num)
theorem B1707413 : Blo 1136633 1707413 := bbase (se 6 (by rfl) ⟨40017, by rfl⟩ : syracuseStep 1707413 = 80035) (by norm_num)
theorem B10390933 : Blo 1136633 10390933 := bbase (se 6 (by rfl) ⟨243537, by rfl⟩ : syracuseStep 10390933 = 487075) (by norm_num)
theorem B1281433 : Blo 1136633 1281433 := bbase (se 2 (by rfl) ⟨480537, by rfl⟩ : syracuseStep 1281433 = 961075) (by norm_num)
theorem B1707437 : Blo 1136633 1707437 := bbase (se 3 (by rfl) ⟨320144, by rfl⟩ : syracuseStep 1707437 = 640289) (by norm_num)
theorem B6917557 : Blo 1136633 6917557 := bbase (se 5 (by rfl) ⟨324260, by rfl⟩ : syracuseStep 6917557 = 648521) (by norm_num)
theorem B1281469 : Blo 1136633 1281469 := bbase (se 3 (by rfl) ⟨240275, by rfl⟩ : syracuseStep 1281469 = 480551) (by norm_num)
theorem B1707461 : Blo 1136633 1707461 := bbase (se 4 (by rfl) ⟨160074, by rfl⟩ : syracuseStep 1707461 = 320149) (by norm_num)
theorem B2559437 : Blo 1136633 2559437 := bbase (se 3 (by rfl) ⟨479894, by rfl⟩ : syracuseStep 2559437 = 959789) (by norm_num)
theorem B43814357 : Blo 1136633 43814357 := bbase (se 7 (by rfl) ⟨513449, by rfl⟩ : syracuseStep 43814357 = 1026899) (by norm_num)
theorem B1707485 : Blo 1136633 1707485 := bbase (se 3 (by rfl) ⟨320153, by rfl⟩ : syracuseStep 1707485 = 640307) (by norm_num)
theorem B1281505 : Blo 1136633 1281505 := bbase (se 2 (by rfl) ⟨480564, by rfl⟩ : syracuseStep 1281505 = 961129) (by norm_num)
theorem B1707509 : Blo 1136633 1707509 := bbase (se 5 (by rfl) ⟨80039, by rfl⟩ : syracuseStep 1707509 = 160079) (by norm_num)
theorem B1281541 : Blo 1136633 1281541 := bbase (se 4 (by rfl) ⟨120144, by rfl⟩ : syracuseStep 1281541 = 240289) (by norm_num)
theorem B1707533 : Blo 1136633 1707533 := bbase (se 3 (by rfl) ⟨320162, by rfl⟩ : syracuseStep 1707533 = 640325) (by norm_num)
theorem B2559509 : Blo 1136633 2559509 := bbase (se 6 (by rfl) ⟨59988, by rfl⟩ : syracuseStep 2559509 = 119977) (by norm_num)
theorem B1707557 : Blo 1136633 1707557 := bbase (se 4 (by rfl) ⟨160083, by rfl⟩ : syracuseStep 1707557 = 320167) (by norm_num)
theorem B1281577 : Blo 1136633 1281577 := bbase (se 2 (by rfl) ⟨480591, by rfl⟩ : syracuseStep 1281577 = 961183) (by norm_num)
theorem B1707581 : Blo 1136633 1707581 := bbase (se 3 (by rfl) ⟨320171, by rfl⟩ : syracuseStep 1707581 = 640343) (by norm_num)
theorem B3837509 : Blo 1136633 3837509 := bbase (se 4 (by rfl) ⟨359766, by rfl⟩ : syracuseStep 3837509 = 719533) (by norm_num)
theorem B3247685 : Blo 1136633 3247685 := bbase (se 4 (by rfl) ⟨304470, by rfl⟩ : syracuseStep 3247685 = 608941) (by norm_num)
theorem B1281613 : Blo 1136633 1281613 := bbase (se 3 (by rfl) ⟨240302, by rfl⟩ : syracuseStep 1281613 = 480605) (by norm_num)
theorem B1707605 : Blo 1136633 1707605 := bbase (se 8 (by rfl) ⟨10005, by rfl⟩ : syracuseStep 1707605 = 20011) (by norm_num)
theorem B2559581 : Blo 1136633 2559581 := bbase (se 3 (by rfl) ⟨479921, by rfl⟩ : syracuseStep 2559581 = 959843) (by norm_num)
theorem B1707629 : Blo 1136633 1707629 := bbase (se 3 (by rfl) ⟨320180, by rfl⟩ : syracuseStep 1707629 = 640361) (by norm_num)
theorem B1281649 : Blo 1136633 1281649 := bbase (se 2 (by rfl) ⟨480618, by rfl⟩ : syracuseStep 1281649 = 961237) (by norm_num)
theorem B1707653 : Blo 1136633 1707653 := bbase (se 4 (by rfl) ⟨160092, by rfl⟩ : syracuseStep 1707653 = 320185) (by norm_num)
theorem B1281685 : Blo 1136633 1281685 := bbase (se 6 (by rfl) ⟨30039, by rfl⟩ : syracuseStep 1281685 = 60079) (by norm_num)
theorem B1707677 : Blo 1136633 1707677 := bbase (se 3 (by rfl) ⟨320189, by rfl⟩ : syracuseStep 1707677 = 640379) (by norm_num)
theorem B2559653 : Blo 1136633 2559653 := bbase (se 4 (by rfl) ⟨239967, by rfl⟩ : syracuseStep 2559653 = 479935) (by norm_num)
theorem B1216177 : Blo 1136633 1216177 := bbase (se 2 (by rfl) ⟨456066, by rfl⟩ : syracuseStep 1216177 = 912133) (by norm_num)
theorem B1707701 : Blo 1136633 1707701 := bbase (se 5 (by rfl) ⟨80048, by rfl⟩ : syracuseStep 1707701 = 160097) (by norm_num)
theorem B1281721 : Blo 1136633 1281721 := bbase (se 2 (by rfl) ⟨480645, by rfl⟩ : syracuseStep 1281721 = 961291) (by norm_num)
theorem B2428613 : Blo 1136633 2428613 := bbase (se 4 (by rfl) ⟨227682, by rfl⟩ : syracuseStep 2428613 = 455365) (by norm_num)
theorem B1707725 : Blo 1136633 1707725 := bbase (se 3 (by rfl) ⟨320198, by rfl⟩ : syracuseStep 1707725 = 640397) (by norm_num)
theorem B1281757 : Blo 1136633 1281757 := bbase (se 3 (by rfl) ⟨240329, by rfl⟩ : syracuseStep 1281757 = 480659) (by norm_num)
theorem B1707749 : Blo 1136633 1707749 := bbase (se 4 (by rfl) ⟨160101, by rfl⟩ : syracuseStep 1707749 = 320203) (by norm_num)
theorem B2559725 : Blo 1136633 2559725 := bbase (se 3 (by rfl) ⟨479948, by rfl⟩ : syracuseStep 2559725 = 959897) (by norm_num)
theorem B1707773 : Blo 1136633 1707773 := bbase (se 3 (by rfl) ⟨320207, by rfl⟩ : syracuseStep 1707773 = 640415) (by norm_num)
theorem B1281793 : Blo 1136633 1281793 := bbase (se 2 (by rfl) ⟨480672, by rfl⟩ : syracuseStep 1281793 = 961345) (by norm_num)
theorem B3247877 : Blo 1136633 3247877 := bbase (se 4 (by rfl) ⟨304488, by rfl⟩ : syracuseStep 3247877 = 608977) (by norm_num)
theorem B1707797 : Blo 1136633 1707797 := bbase (se 6 (by rfl) ⟨40026, by rfl⟩ : syracuseStep 1707797 = 80053) (by norm_num)
theorem B1281829 : Blo 1136633 1281829 := bbase (se 4 (by rfl) ⟨120171, by rfl⟩ : syracuseStep 1281829 = 240343) (by norm_num)
theorem B1216297 : Blo 1136633 1216297 := bbase (se 2 (by rfl) ⟨456111, by rfl⟩ : syracuseStep 1216297 = 912223) (by norm_num)
theorem B1707821 : Blo 1136633 1707821 := bbase (se 3 (by rfl) ⟨320216, by rfl⟩ : syracuseStep 1707821 = 640433) (by norm_num)
theorem B2559797 : Blo 1136633 2559797 := bbase (se 5 (by rfl) ⟨119990, by rfl⟩ : syracuseStep 2559797 = 239981) (by norm_num)
theorem B1707845 : Blo 1136633 1707845 := bbase (se 4 (by rfl) ⟨160110, by rfl⟩ : syracuseStep 1707845 = 320221) (by norm_num)
theorem B1281865 : Blo 1136633 1281865 := bbase (se 2 (by rfl) ⟨480699, by rfl⟩ : syracuseStep 1281865 = 961399) (by norm_num)
theorem B1707869 : Blo 1136633 1707869 := bbase (se 3 (by rfl) ⟨320225, by rfl⟩ : syracuseStep 1707869 = 640451) (by norm_num)
theorem B1281901 : Blo 1136633 1281901 := bbase (se 3 (by rfl) ⟨240356, by rfl⟩ : syracuseStep 1281901 = 480713) (by norm_num)
theorem B1707893 : Blo 1136633 1707893 := bbase (se 5 (by rfl) ⟨80057, by rfl⟩ : syracuseStep 1707893 = 160115) (by norm_num)
theorem B2559869 : Blo 1136633 2559869 := bbase (se 3 (by rfl) ⟨479975, by rfl⟩ : syracuseStep 2559869 = 959951) (by norm_num)
theorem B1707917 : Blo 1136633 1707917 := bbase (se 3 (by rfl) ⟨320234, by rfl⟩ : syracuseStep 1707917 = 640469) (by norm_num)
theorem B1281937 : Blo 1136633 1281937 := bbase (se 2 (by rfl) ⟨480726, by rfl⟩ : syracuseStep 1281937 = 961453) (by norm_num)
theorem B1707941 : Blo 1136633 1707941 := bbase (se 4 (by rfl) ⟨160119, by rfl⟩ : syracuseStep 1707941 = 320239) (by norm_num)
theorem B1281973 : Blo 1136633 1281973 := bbase (se 5 (by rfl) ⟨60092, by rfl⟩ : syracuseStep 1281973 = 120185) (by norm_num)
theorem B2428861 : Blo 1136633 2428861 := bbase (se 3 (by rfl) ⟨455411, by rfl⟩ : syracuseStep 2428861 = 910823) (by norm_num)
theorem B1707965 : Blo 1136633 1707965 := bbase (se 3 (by rfl) ⟨320243, by rfl⟩ : syracuseStep 1707965 = 640487) (by norm_num)
theorem B2559941 : Blo 1136633 2559941 := bbase (se 4 (by rfl) ⟨239994, by rfl⟩ : syracuseStep 2559941 = 479989) (by norm_num)
theorem B1707989 : Blo 1136633 1707989 := bbase (se 7 (by rfl) ⟨20015, by rfl⟩ : syracuseStep 1707989 = 40031) (by norm_num)
theorem B1282009 : Blo 1136633 1282009 := bbase (se 2 (by rfl) ⟨480753, by rfl⟩ : syracuseStep 1282009 = 961507) (by norm_num)
theorem B1708013 : Blo 1136633 1708013 := bbase (se 3 (by rfl) ⟨320252, by rfl⟩ : syracuseStep 1708013 = 640505) (by norm_num)
theorem B3837941 : Blo 1136633 3837941 := bbase (se 5 (by rfl) ⟨179903, by rfl⟩ : syracuseStep 3837941 = 359807) (by norm_num)
theorem B1282045 : Blo 1136633 1282045 := bbase (se 3 (by rfl) ⟨240383, by rfl⟩ : syracuseStep 1282045 = 480767) (by norm_num)
theorem B1708037 : Blo 1136633 1708037 := bbase (se 4 (by rfl) ⟨160128, by rfl⟩ : syracuseStep 1708037 = 320257) (by norm_num)
theorem B2560013 : Blo 1136633 2560013 := bbase (se 3 (by rfl) ⟨480002, by rfl⟩ : syracuseStep 2560013 = 960005) (by norm_num)
theorem B1708061 : Blo 1136633 1708061 := bbase (se 3 (by rfl) ⟨320261, by rfl⟩ : syracuseStep 1708061 = 640523) (by norm_num)
theorem B1282081 : Blo 1136633 1282081 := bbase (se 2 (by rfl) ⟨480780, by rfl⟩ : syracuseStep 1282081 = 961561) (by norm_num)
theorem B1216549 : Blo 1136633 1216549 := bbase (se 4 (by rfl) ⟨114051, by rfl⟩ : syracuseStep 1216549 = 228103) (by norm_num)
theorem B1216553 : Blo 1136633 1216553 := bbase (se 2 (by rfl) ⟨456207, by rfl⟩ : syracuseStep 1216553 = 912415) (by norm_num)
theorem B1708085 : Blo 1136633 1708085 := bbase (se 5 (by rfl) ⟨80066, by rfl⟩ : syracuseStep 1708085 = 160133) (by norm_num)
theorem B1282117 : Blo 1136633 1282117 := bbase (se 4 (by rfl) ⟨120198, by rfl⟩ : syracuseStep 1282117 = 240397) (by norm_num)
theorem B1708109 : Blo 1136633 1708109 := bbase (se 3 (by rfl) ⟨320270, by rfl⟩ : syracuseStep 1708109 = 640541) (by norm_num)
theorem B2560085 : Blo 1136633 2560085 := bbase (se 8 (by rfl) ⟨15000, by rfl⟩ : syracuseStep 2560085 = 30001) (by norm_num)
theorem B1708133 : Blo 1136633 1708133 := bbase (se 4 (by rfl) ⟨160137, by rfl⟩ : syracuseStep 1708133 = 320275) (by norm_num)
theorem B1282153 : Blo 1136633 1282153 := bbase (se 2 (by rfl) ⟨480807, by rfl⟩ : syracuseStep 1282153 = 961615) (by norm_num)
theorem B1708157 : Blo 1136633 1708157 := bbase (se 3 (by rfl) ⟨320279, by rfl⟩ : syracuseStep 1708157 = 640559) (by norm_num)
theorem B1282189 : Blo 1136633 1282189 := bbase (se 3 (by rfl) ⟨240410, by rfl⟩ : syracuseStep 1282189 = 480821) (by norm_num)
theorem B1708181 : Blo 1136633 1708181 := bbase (se 6 (by rfl) ⟨40035, by rfl⟩ : syracuseStep 1708181 = 80071) (by norm_num)
theorem B2560157 : Blo 1136633 2560157 := bbase (se 3 (by rfl) ⟨480029, by rfl⟩ : syracuseStep 2560157 = 960059) (by norm_num)
theorem B1708205 : Blo 1136633 1708205 := bbase (se 3 (by rfl) ⟨320288, by rfl⟩ : syracuseStep 1708205 = 640577) (by norm_num)
theorem B1282225 : Blo 1136633 1282225 := bbase (se 2 (by rfl) ⟨480834, by rfl⟩ : syracuseStep 1282225 = 961669) (by norm_num)
theorem B1708229 : Blo 1136633 1708229 := bbase (se 4 (by rfl) ⟨160146, by rfl⟩ : syracuseStep 1708229 = 320293) (by norm_num)
theorem B1282261 : Blo 1136633 1282261 := bbase (se 7 (by rfl) ⟨15026, by rfl⟩ : syracuseStep 1282261 = 30053) (by norm_num)
theorem B1708253 : Blo 1136633 1708253 := bbase (se 3 (by rfl) ⟨320297, by rfl⟩ : syracuseStep 1708253 = 640595) (by norm_num)
theorem B2560229 : Blo 1136633 2560229 := bbase (se 4 (by rfl) ⟨240021, by rfl⟩ : syracuseStep 2560229 = 480043) (by norm_num)
theorem B1708277 : Blo 1136633 1708277 := bbase (se 5 (by rfl) ⟨80075, by rfl⟩ : syracuseStep 1708277 = 160151) (by norm_num)
theorem B1282297 : Blo 1136633 1282297 := bbase (se 2 (by rfl) ⟨480861, by rfl⟩ : syracuseStep 1282297 = 961723) (by norm_num)
theorem B1708301 : Blo 1136633 1708301 := bbase (se 3 (by rfl) ⟨320306, by rfl⟩ : syracuseStep 1708301 = 640613) (by norm_num)
theorem B1282333 : Blo 1136633 1282333 := bbase (se 3 (by rfl) ⟨240437, by rfl⟩ : syracuseStep 1282333 = 480875) (by norm_num)
theorem B1708325 : Blo 1136633 1708325 := bbase (se 4 (by rfl) ⟨160155, by rfl⟩ : syracuseStep 1708325 = 320311) (by norm_num)
theorem B2560301 : Blo 1136633 2560301 := bbase (se 3 (by rfl) ⟨480056, by rfl⟩ : syracuseStep 2560301 = 960113) (by norm_num)
theorem B5771573 : Blo 1136633 5771573 := bbase (se 5 (by rfl) ⟨270542, by rfl⟩ : syracuseStep 5771573 = 541085) (by norm_num)
theorem B1708349 : Blo 1136633 1708349 := bbase (se 3 (by rfl) ⟨320315, by rfl⟩ : syracuseStep 1708349 = 640631) (by norm_num)
theorem B1282369 : Blo 1136633 1282369 := bbase (se 2 (by rfl) ⟨480888, by rfl⟩ : syracuseStep 1282369 = 961777) (by norm_num)
theorem B1708373 : Blo 1136633 1708373 := bbase (se 10 (by rfl) ⟨2502, by rfl⟩ : syracuseStep 1708373 = 5005) (by norm_num)
theorem B1282405 : Blo 1136633 1282405 := bbase (se 4 (by rfl) ⟨120225, by rfl⟩ : syracuseStep 1282405 = 240451) (by norm_num)
theorem B1708397 : Blo 1136633 1708397 := bbase (se 3 (by rfl) ⟨320324, by rfl⟩ : syracuseStep 1708397 = 640649) (by norm_num)
theorem B2560373 : Blo 1136633 2560373 := bbase (se 5 (by rfl) ⟨120017, by rfl⟩ : syracuseStep 2560373 = 240035) (by norm_num)
theorem B1708421 : Blo 1136633 1708421 := bbase (se 4 (by rfl) ⟨160164, by rfl⟩ : syracuseStep 1708421 = 320329) (by norm_num)
theorem B1282441 : Blo 1136633 1282441 := bbase (se 2 (by rfl) ⟨480915, by rfl⟩ : syracuseStep 1282441 = 961831) (by norm_num)
theorem B1708445 : Blo 1136633 1708445 := bbase (se 3 (by rfl) ⟨320333, by rfl⟩ : syracuseStep 1708445 = 640667) (by norm_num)
theorem B1642909 : Blo 1136633 1642909 := bbase (se 3 (by rfl) ⟨308045, by rfl⟩ : syracuseStep 1642909 = 616091) (by norm_num)
theorem B3641765 : Blo 1136633 3641765 := bbase (se 4 (by rfl) ⟨341415, by rfl⟩ : syracuseStep 3641765 = 682831) (by norm_num)
theorem B3838373 : Blo 1136633 3838373 := bbase (se 4 (by rfl) ⟨359847, by rfl⟩ : syracuseStep 3838373 = 719695) (by norm_num)
theorem B1282477 : Blo 1136633 1282477 := bbase (se 3 (by rfl) ⟨240464, by rfl⟩ : syracuseStep 1282477 = 480929) (by norm_num)
theorem B2429365 : Blo 1136633 2429365 := bbase (se 5 (by rfl) ⟨113876, by rfl⟩ : syracuseStep 2429365 = 227753) (by norm_num)
theorem B1708469 : Blo 1136633 1708469 := bbase (se 5 (by rfl) ⟨80084, by rfl⟩ : syracuseStep 1708469 = 160169) (by norm_num)
theorem B2560445 : Blo 1136633 2560445 := bbase (se 3 (by rfl) ⟨480083, by rfl⟩ : syracuseStep 2560445 = 960167) (by norm_num)
theorem B1708493 : Blo 1136633 1708493 := bbase (se 3 (by rfl) ⟨320342, by rfl⟩ : syracuseStep 1708493 = 640685) (by norm_num)
theorem B1282513 : Blo 1136633 1282513 := bbase (se 2 (by rfl) ⟨480942, by rfl⟩ : syracuseStep 1282513 = 961885) (by norm_num)
theorem B1708517 : Blo 1136633 1708517 := bbase (se 4 (by rfl) ⟨160173, by rfl⟩ : syracuseStep 1708517 = 320347) (by norm_num)
theorem B1282549 : Blo 1136633 1282549 := bbase (se 5 (by rfl) ⟨60119, by rfl⟩ : syracuseStep 1282549 = 120239) (by norm_num)
theorem B1708541 : Blo 1136633 1708541 := bbase (se 3 (by rfl) ⟨320351, by rfl⟩ : syracuseStep 1708541 = 640703) (by norm_num)
theorem B2560517 : Blo 1136633 2560517 := bbase (se 4 (by rfl) ⟨240048, by rfl⟩ : syracuseStep 2560517 = 480097) (by norm_num)
theorem B1708565 : Blo 1136633 1708565 := bbase (se 6 (by rfl) ⟨40044, by rfl⟩ : syracuseStep 1708565 = 80089) (by norm_num)
theorem B1282585 : Blo 1136633 1282585 := bbase (se 2 (by rfl) ⟨480969, by rfl⟩ : syracuseStep 1282585 = 961939) (by norm_num)
theorem B1708589 : Blo 1136633 1708589 := bbase (se 3 (by rfl) ⟨320360, by rfl⟩ : syracuseStep 1708589 = 640721) (by norm_num)
theorem B1282621 : Blo 1136633 1282621 := bbase (se 3 (by rfl) ⟨240491, by rfl⟩ : syracuseStep 1282621 = 480983) (by norm_num)
theorem B1708613 : Blo 1136633 1708613 := bbase (se 4 (by rfl) ⟨160182, by rfl⟩ : syracuseStep 1708613 = 320365) (by norm_num)
theorem B2560589 : Blo 1136633 2560589 := bbase (se 3 (by rfl) ⟨480110, by rfl⟩ : syracuseStep 2560589 = 960221) (by norm_num)
theorem B1708637 : Blo 1136633 1708637 := bbase (se 3 (by rfl) ⟨320369, by rfl⟩ : syracuseStep 1708637 = 640739) (by norm_num)
theorem B1217117 : Blo 1136633 1217117 := bbase (se 3 (by rfl) ⟨228209, by rfl⟩ : syracuseStep 1217117 = 456419) (by norm_num)
theorem B1282657 : Blo 1136633 1282657 := bbase (se 2 (by rfl) ⟨480996, by rfl⟩ : syracuseStep 1282657 = 961993) (by norm_num)
theorem B1708661 : Blo 1136633 1708661 := bbase (se 5 (by rfl) ⟨80093, by rfl⟩ : syracuseStep 1708661 = 160187) (by norm_num)
theorem B1282693 : Blo 1136633 1282693 := bbase (se 4 (by rfl) ⟨120252, by rfl⟩ : syracuseStep 1282693 = 240505) (by norm_num)
theorem B1708685 : Blo 1136633 1708685 := bbase (se 3 (by rfl) ⟨320378, by rfl⟩ : syracuseStep 1708685 = 640757) (by norm_num)
theorem B2560661 : Blo 1136633 2560661 := bbase (se 6 (by rfl) ⟨60015, by rfl⟩ : syracuseStep 2560661 = 120031) (by norm_num)
theorem B1708709 : Blo 1136633 1708709 := bbase (se 4 (by rfl) ⟨160191, by rfl⟩ : syracuseStep 1708709 = 320383) (by norm_num)
theorem B1282729 : Blo 1136633 1282729 := bbase (se 2 (by rfl) ⟨481023, by rfl⟩ : syracuseStep 1282729 = 962047) (by norm_num)
theorem B1708733 : Blo 1136633 1708733 := bbase (se 3 (by rfl) ⟨320387, by rfl⟩ : syracuseStep 1708733 = 640775) (by norm_num)
theorem B1282765 : Blo 1136633 1282765 := bbase (se 3 (by rfl) ⟨240518, by rfl⟩ : syracuseStep 1282765 = 481037) (by norm_num)
theorem B1708757 : Blo 1136633 1708757 := bbase (se 7 (by rfl) ⟨20024, by rfl⟩ : syracuseStep 1708757 = 40049) (by norm_num)
theorem B2560733 : Blo 1136633 2560733 := bbase (se 3 (by rfl) ⟨480137, by rfl⟩ : syracuseStep 2560733 = 960275) (by norm_num)
theorem B1708781 : Blo 1136633 1708781 := bbase (se 3 (by rfl) ⟨320396, by rfl⟩ : syracuseStep 1708781 = 640793) (by norm_num)
theorem B1282801 : Blo 1136633 1282801 := bbase (se 2 (by rfl) ⟨481050, by rfl⟩ : syracuseStep 1282801 = 962101) (by norm_num)
theorem B1708805 : Blo 1136633 1708805 := bbase (se 4 (by rfl) ⟨160200, by rfl⟩ : syracuseStep 1708805 = 320401) (by norm_num)
theorem B1282837 : Blo 1136633 1282837 := bbase (se 6 (by rfl) ⟨30066, by rfl⟩ : syracuseStep 1282837 = 60133) (by norm_num)
theorem B1217305 : Blo 1136633 1217305 := bbase (se 2 (by rfl) ⟨456489, by rfl⟩ : syracuseStep 1217305 = 912979) (by norm_num)
theorem B1708829 : Blo 1136633 1708829 := bbase (se 3 (by rfl) ⟨320405, by rfl⟩ : syracuseStep 1708829 = 640811) (by norm_num)
theorem B2560805 : Blo 1136633 2560805 := bbase (se 4 (by rfl) ⟨240075, by rfl⟩ : syracuseStep 2560805 = 480151) (by norm_num)
theorem B1708853 : Blo 1136633 1708853 := bbase (se 5 (by rfl) ⟨80102, by rfl⟩ : syracuseStep 1708853 = 160205) (by norm_num)
theorem B1282873 : Blo 1136633 1282873 := bbase (se 2 (by rfl) ⟨481077, by rfl⟩ : syracuseStep 1282873 = 962155) (by norm_num)
theorem B1708877 : Blo 1136633 1708877 := bbase (se 3 (by rfl) ⟨320414, by rfl⟩ : syracuseStep 1708877 = 640829) (by norm_num)
theorem B3838805 : Blo 1136633 3838805 := bbase (se 9 (by rfl) ⟨11246, by rfl⟩ : syracuseStep 3838805 = 22493) (by norm_num)
theorem B1282909 : Blo 1136633 1282909 := bbase (se 3 (by rfl) ⟨240545, by rfl⟩ : syracuseStep 1282909 = 481091) (by norm_num)
theorem B1708901 : Blo 1136633 1708901 := bbase (se 4 (by rfl) ⟨160209, by rfl⟩ : syracuseStep 1708901 = 320419) (by norm_num)
theorem B2560877 : Blo 1136633 2560877 := bbase (se 3 (by rfl) ⟨480164, by rfl⟩ : syracuseStep 2560877 = 960329) (by norm_num)
theorem B1708925 : Blo 1136633 1708925 := bbase (se 3 (by rfl) ⟨320423, by rfl⟩ : syracuseStep 1708925 = 640847) (by norm_num)
theorem B1282945 : Blo 1136633 1282945 := bbase (se 2 (by rfl) ⟨481104, by rfl⟩ : syracuseStep 1282945 = 962209) (by norm_num)
theorem B1708949 : Blo 1136633 1708949 := bbase (se 6 (by rfl) ⟨40053, by rfl⟩ : syracuseStep 1708949 = 80107) (by norm_num)
theorem B1282981 : Blo 1136633 1282981 := bbase (se 4 (by rfl) ⟨120279, by rfl⟩ : syracuseStep 1282981 = 240559) (by norm_num)
theorem B1708973 : Blo 1136633 1708973 := bbase (se 3 (by rfl) ⟨320432, by rfl⟩ : syracuseStep 1708973 = 640865) (by norm_num)
theorem B2560949 : Blo 1136633 2560949 := bbase (se 5 (by rfl) ⟨120044, by rfl⟩ : syracuseStep 2560949 = 240089) (by norm_num)
theorem B1708997 : Blo 1136633 1708997 := bbase (se 4 (by rfl) ⟨160218, by rfl⟩ : syracuseStep 1708997 = 320437) (by norm_num)
theorem B1283017 : Blo 1136633 1283017 := bbase (se 2 (by rfl) ⟨481131, by rfl⟩ : syracuseStep 1283017 = 962263) (by norm_num)
theorem B2593757 : Blo 1136633 2593757 := bbase (se 3 (by rfl) ⟨486329, by rfl⟩ : syracuseStep 2593757 = 972659) (by norm_num)
theorem B1709021 : Blo 1136633 1709021 := bbase (se 3 (by rfl) ⟨320441, by rfl⟩ : syracuseStep 1709021 = 640883) (by norm_num)
theorem B1283053 : Blo 1136633 1283053 := bbase (se 3 (by rfl) ⟨240572, by rfl⟩ : syracuseStep 1283053 = 481145) (by norm_num)
theorem B1709045 : Blo 1136633 1709045 := bbase (se 5 (by rfl) ⟨80111, by rfl⟩ : syracuseStep 1709045 = 160223) (by norm_num)
theorem B2561021 : Blo 1136633 2561021 := bbase (se 3 (by rfl) ⟨480191, by rfl⟩ : syracuseStep 2561021 = 960383) (by norm_num)
theorem B1709069 : Blo 1136633 1709069 := bbase (se 3 (by rfl) ⟨320450, by rfl⟩ : syracuseStep 1709069 = 640901) (by norm_num)
theorem B1283089 : Blo 1136633 1283089 := bbase (se 2 (by rfl) ⟨481158, by rfl⟩ : syracuseStep 1283089 = 962317) (by norm_num)
theorem B1709093 : Blo 1136633 1709093 := bbase (se 4 (by rfl) ⟨160227, by rfl⟩ : syracuseStep 1709093 = 320455) (by norm_num)
theorem B1283125 : Blo 1136633 1283125 := bbase (se 5 (by rfl) ⟨60146, by rfl⟩ : syracuseStep 1283125 = 120293) (by norm_num)
theorem B1709117 : Blo 1136633 1709117 := bbase (se 3 (by rfl) ⟨320459, by rfl⟩ : syracuseStep 1709117 = 640919) (by norm_num)
theorem B2561093 : Blo 1136633 2561093 := bbase (se 4 (by rfl) ⟨240102, by rfl⟩ : syracuseStep 2561093 = 480205) (by norm_num)
theorem B1315921 : Blo 1136633 1315921 := bbase (se 2 (by rfl) ⟨493470, by rfl⟩ : syracuseStep 1315921 = 986941) (by norm_num)
theorem B1709141 : Blo 1136633 1709141 := bbase (se 8 (by rfl) ⟨10014, by rfl⟩ : syracuseStep 1709141 = 20029) (by norm_num)
theorem B1283161 : Blo 1136633 1283161 := bbase (se 2 (by rfl) ⟨481185, by rfl⟩ : syracuseStep 1283161 = 962371) (by norm_num)
theorem B2593885 : Blo 1136633 2593885 := bbase (se 3 (by rfl) ⟨486353, by rfl⟩ : syracuseStep 2593885 = 972707) (by norm_num)
theorem B1709165 : Blo 1136633 1709165 := bbase (se 3 (by rfl) ⟨320468, by rfl⟩ : syracuseStep 1709165 = 640937) (by norm_num)
theorem B1283197 : Blo 1136633 1283197 := bbase (se 3 (by rfl) ⟨240599, by rfl⟩ : syracuseStep 1283197 = 481199) (by norm_num)
theorem B1709189 : Blo 1136633 1709189 := bbase (se 4 (by rfl) ⟨160236, by rfl⟩ : syracuseStep 1709189 = 320473) (by norm_num)
theorem B2561165 : Blo 1136633 2561165 := bbase (se 3 (by rfl) ⟨480218, by rfl⟩ : syracuseStep 2561165 = 960437) (by norm_num)
theorem B1152145 : Blo 1136633 1152145 := bbase (se 2 (by rfl) ⟨432054, by rfl⟩ : syracuseStep 1152145 = 864109) (by norm_num)
theorem B1709213 : Blo 1136633 1709213 := bbase (se 3 (by rfl) ⟨320477, by rfl⟩ : syracuseStep 1709213 = 640955) (by norm_num)
theorem B1152181 : Blo 1136633 1152181 := bbase (se 5 (by rfl) ⟨54008, by rfl⟩ : syracuseStep 1152181 = 108017) (by norm_num)
theorem B1709237 : Blo 1136633 1709237 := bbase (se 5 (by rfl) ⟨80120, by rfl⟩ : syracuseStep 1709237 = 160241) (by norm_num)
theorem B1709261 : Blo 1136633 1709261 := bbase (se 3 (by rfl) ⟨320486, by rfl⟩ : syracuseStep 1709261 = 640973) (by norm_num)
theorem B2561237 : Blo 1136633 2561237 := bbase (se 7 (by rfl) ⟨30014, by rfl⟩ : syracuseStep 2561237 = 60029) (by norm_num)
theorem B1709285 : Blo 1136633 1709285 := bbase (se 4 (by rfl) ⟨160245, by rfl⟩ : syracuseStep 1709285 = 320491) (by norm_num)
theorem B1709309 : Blo 1136633 1709309 := bbase (se 3 (by rfl) ⟨320495, by rfl⟩ : syracuseStep 1709309 = 640991) (by norm_num)
theorem B3839237 : Blo 1136633 3839237 := bbase (se 4 (by rfl) ⟨359928, by rfl⟩ : syracuseStep 3839237 = 719857) (by norm_num)
theorem B1709333 : Blo 1136633 1709333 := bbase (se 6 (by rfl) ⟨40062, by rfl⟩ : syracuseStep 1709333 = 80125) (by norm_num)
theorem B2561309 : Blo 1136633 2561309 := bbase (se 3 (by rfl) ⟨480245, by rfl⟩ : syracuseStep 2561309 = 960491) (by norm_num)
theorem B2430253 : Blo 1136633 2430253 := bbase (se 3 (by rfl) ⟨455672, by rfl⟩ : syracuseStep 2430253 = 911345) (by norm_num)
theorem B1709357 : Blo 1136633 1709357 := bbase (se 3 (by rfl) ⟨320504, by rfl⟩ : syracuseStep 1709357 = 641009) (by norm_num)
theorem B3642677 : Blo 1136633 3642677 := bbase (se 5 (by rfl) ⟨170750, by rfl⟩ : syracuseStep 3642677 = 341501) (by norm_num)
theorem B1709381 : Blo 1136633 1709381 := bbase (se 4 (by rfl) ⟨160254, by rfl⟩ : syracuseStep 1709381 = 320509) (by norm_num)
theorem B1709405 : Blo 1136633 1709405 := bbase (se 3 (by rfl) ⟨320513, by rfl⟩ : syracuseStep 1709405 = 641027) (by norm_num)
theorem B2561381 : Blo 1136633 2561381 := bbase (se 4 (by rfl) ⟨240129, by rfl⟩ : syracuseStep 2561381 = 480259) (by norm_num)
theorem B1709429 : Blo 1136633 1709429 := bbase (se 5 (by rfl) ⟨80129, by rfl⟩ : syracuseStep 1709429 = 160259) (by norm_num)
theorem B1709453 : Blo 1136633 1709453 := bbase (se 3 (by rfl) ⟨320522, by rfl⟩ : syracuseStep 1709453 = 641045) (by norm_num)
theorem B1709477 : Blo 1136633 1709477 := bbase (se 4 (by rfl) ⟨160263, by rfl⟩ : syracuseStep 1709477 = 320527) (by norm_num)
theorem B2561453 : Blo 1136633 2561453 := bbase (se 3 (by rfl) ⟨480272, by rfl⟩ : syracuseStep 2561453 = 960545) (by norm_num)
theorem B1480117 : Blo 1136633 1480117 := bbase (se 5 (by rfl) ⟨69380, by rfl⟩ : syracuseStep 1480117 = 138761) (by norm_num)
theorem B1709501 : Blo 1136633 1709501 := bbase (se 3 (by rfl) ⟨320531, by rfl⟩ : syracuseStep 1709501 = 641063) (by norm_num)
theorem B1709525 : Blo 1136633 1709525 := bbase (se 7 (by rfl) ⟨20033, by rfl⟩ : syracuseStep 1709525 = 40067) (by norm_num)
theorem B1709549 : Blo 1136633 1709549 := bbase (se 3 (by rfl) ⟨320540, by rfl⟩ : syracuseStep 1709549 = 641081) (by norm_num)
theorem B2561525 : Blo 1136633 2561525 := bbase (se 5 (by rfl) ⟨120071, by rfl⟩ : syracuseStep 2561525 = 240143) (by norm_num)
theorem B1709573 : Blo 1136633 1709573 := bbase (se 4 (by rfl) ⟨160272, by rfl⟩ : syracuseStep 1709573 = 320545) (by norm_num)
theorem B1709597 : Blo 1136633 1709597 := bbase (se 3 (by rfl) ⟨320549, by rfl⟩ : syracuseStep 1709597 = 641099) (by norm_num)
theorem B1709621 : Blo 1136633 1709621 := bbase (se 5 (by rfl) ⟨80138, by rfl⟩ : syracuseStep 1709621 = 160277) (by norm_num)
theorem B2561597 : Blo 1136633 2561597 := bbase (se 3 (by rfl) ⟨480299, by rfl⟩ : syracuseStep 2561597 = 960599) (by norm_num)
theorem B5772869 : Blo 1136633 5772869 := bbase (se 4 (by rfl) ⟨541206, by rfl⟩ : syracuseStep 5772869 = 1082413) (by norm_num)
theorem B1709645 : Blo 1136633 1709645 := bbase (se 3 (by rfl) ⟨320558, by rfl⟩ : syracuseStep 1709645 = 641117) (by norm_num)
theorem B1709669 : Blo 1136633 1709669 := bbase (se 4 (by rfl) ⟨160281, by rfl⟩ : syracuseStep 1709669 = 320563) (by norm_num)
theorem B1709693 : Blo 1136633 1709693 := bbase (se 3 (by rfl) ⟨320567, by rfl⟩ : syracuseStep 1709693 = 641135) (by norm_num)
theorem B2561669 : Blo 1136633 2561669 := bbase (se 4 (by rfl) ⟨240156, by rfl⟩ : syracuseStep 2561669 = 480313) (by norm_num)
theorem B1709717 : Blo 1136633 1709717 := bbase (se 6 (by rfl) ⟨40071, by rfl⟩ : syracuseStep 1709717 = 80143) (by norm_num)
theorem B1709741 : Blo 1136633 1709741 := bbase (se 3 (by rfl) ⟨320576, by rfl⟩ : syracuseStep 1709741 = 641153) (by norm_num)
theorem B3839669 : Blo 1136633 3839669 := bbase (se 5 (by rfl) ⟨179984, by rfl⟩ : syracuseStep 3839669 = 359969) (by norm_num)
theorem B1709765 : Blo 1136633 1709765 := bbase (se 4 (by rfl) ⟨160290, by rfl⟩ : syracuseStep 1709765 = 320581) (by norm_num)
theorem B2561741 : Blo 1136633 2561741 := bbase (se 3 (by rfl) ⟨480326, by rfl⟩ : syracuseStep 2561741 = 960653) (by norm_num)
theorem B1709789 : Blo 1136633 1709789 := bbase (se 3 (by rfl) ⟨320585, by rfl⟩ : syracuseStep 1709789 = 641171) (by norm_num)
theorem B1709813 : Blo 1136633 1709813 := bbase (se 5 (by rfl) ⟨80147, by rfl⟩ : syracuseStep 1709813 = 160295) (by norm_num)
theorem B1709837 : Blo 1136633 1709837 := bbase (se 3 (by rfl) ⟨320594, by rfl⟩ : syracuseStep 1709837 = 641189) (by norm_num)
theorem B2561813 : Blo 1136633 2561813 := bbase (se 6 (by rfl) ⟨60042, by rfl⟩ : syracuseStep 2561813 = 120085) (by norm_num)
theorem B2430749 : Blo 1136633 2430749 := bbase (se 3 (by rfl) ⟨455765, by rfl⟩ : syracuseStep 2430749 = 911531) (by norm_num)
theorem B1709861 : Blo 1136633 1709861 := bbase (se 4 (by rfl) ⟨160299, by rfl⟩ : syracuseStep 1709861 = 320599) (by norm_num)
theorem B1709885 : Blo 1136633 1709885 := bbase (se 3 (by rfl) ⟨320603, by rfl⟩ : syracuseStep 1709885 = 641207) (by norm_num)
theorem B1709909 : Blo 1136633 1709909 := bbase (se 9 (by rfl) ⟨5009, by rfl⟩ : syracuseStep 1709909 = 10019) (by norm_num)
theorem B2561885 : Blo 1136633 2561885 := bbase (se 3 (by rfl) ⟨480353, by rfl⟩ : syracuseStep 2561885 = 960707) (by norm_num)
theorem B1709933 : Blo 1136633 1709933 := bbase (se 3 (by rfl) ⟨320612, by rfl⟩ : syracuseStep 1709933 = 641225) (by norm_num)
theorem B1709957 : Blo 1136633 1709957 := bbase (se 4 (by rfl) ⟨160308, by rfl⟩ : syracuseStep 1709957 = 320617) (by norm_num)
theorem B1709981 : Blo 1136633 1709981 := bbase (se 3 (by rfl) ⟨320621, by rfl⟩ : syracuseStep 1709981 = 641243) (by norm_num)
theorem B2561957 : Blo 1136633 2561957 := bbase (se 4 (by rfl) ⟨240183, by rfl⟩ : syracuseStep 2561957 = 480367) (by norm_num)
theorem B1710005 : Blo 1136633 1710005 := bbase (se 5 (by rfl) ⟨80156, by rfl⟩ : syracuseStep 1710005 = 160313) (by norm_num)
theorem B1710029 : Blo 1136633 1710029 := bbase (se 3 (by rfl) ⟨320630, by rfl⟩ : syracuseStep 1710029 = 641261) (by norm_num)
theorem B1710053 : Blo 1136633 1710053 := bbase (se 4 (by rfl) ⟨160317, by rfl⟩ : syracuseStep 1710053 = 320635) (by norm_num)
theorem B2562029 : Blo 1136633 2562029 := bbase (se 3 (by rfl) ⟨480380, by rfl⟩ : syracuseStep 2562029 = 960761) (by norm_num)
theorem B1710077 : Blo 1136633 1710077 := bbase (se 3 (by rfl) ⟨320639, by rfl⟩ : syracuseStep 1710077 = 641279) (by norm_num)
theorem B1710101 : Blo 1136633 1710101 := bbase (se 6 (by rfl) ⟨40080, by rfl⟩ : syracuseStep 1710101 = 80161) (by norm_num)
theorem B1710125 : Blo 1136633 1710125 := bbase (se 3 (by rfl) ⟨320648, by rfl⟩ : syracuseStep 1710125 = 641297) (by norm_num)
theorem B8755253 : Blo 1136633 8755253 := bbase (se 5 (by rfl) ⟨410402, by rfl⟩ : syracuseStep 8755253 = 820805) (by norm_num)
theorem B2562101 : Blo 1136633 2562101 := bbase (se 5 (by rfl) ⟨120098, by rfl⟩ : syracuseStep 2562101 = 240197) (by norm_num)
theorem B1710149 : Blo 1136633 1710149 := bbase (se 4 (by rfl) ⟨160326, by rfl⟩ : syracuseStep 1710149 = 320653) (by norm_num)
theorem B1710173 : Blo 1136633 1710173 := bbase (se 3 (by rfl) ⟨320657, by rfl⟩ : syracuseStep 1710173 = 641315) (by norm_num)
theorem B1153121 : Blo 1136633 1153121 := bbase (se 2 (by rfl) ⟨432420, by rfl⟩ : syracuseStep 1153121 = 864841) (by norm_num)
theorem B3840101 : Blo 1136633 3840101 := bbase (se 4 (by rfl) ⟨360009, by rfl⟩ : syracuseStep 3840101 = 720019) (by norm_num)
theorem B3119221 : Blo 1136633 3119221 := bbase (se 5 (by rfl) ⟨146213, by rfl⟩ : syracuseStep 3119221 = 292427) (by norm_num)
theorem B1710197 : Blo 1136633 1710197 := bbase (se 5 (by rfl) ⟨80165, by rfl⟩ : syracuseStep 1710197 = 160331) (by norm_num)
theorem B2562173 : Blo 1136633 2562173 := bbase (se 3 (by rfl) ⟨480407, by rfl⟩ : syracuseStep 2562173 = 960815) (by norm_num)
theorem B1710221 : Blo 1136633 1710221 := bbase (se 3 (by rfl) ⟨320666, by rfl⟩ : syracuseStep 1710221 = 641333) (by norm_num)
theorem B1710245 : Blo 1136633 1710245 := bbase (se 4 (by rfl) ⟨160335, by rfl⟩ : syracuseStep 1710245 = 320671) (by norm_num)
theorem B1710269 : Blo 1136633 1710269 := bbase (se 3 (by rfl) ⟨320675, by rfl⟩ : syracuseStep 1710269 = 641351) (by norm_num)
theorem B2562245 : Blo 1136633 2562245 := bbase (se 4 (by rfl) ⟨240210, by rfl⟩ : syracuseStep 2562245 = 480421) (by norm_num)
theorem B1710293 : Blo 1136633 1710293 := bbase (se 7 (by rfl) ⟨20042, by rfl⟩ : syracuseStep 1710293 = 40085) (by norm_num)
theorem B2595053 : Blo 1136633 2595053 := bbase (se 3 (by rfl) ⟨486572, by rfl⟩ : syracuseStep 2595053 = 973145) (by norm_num)
theorem B1710317 : Blo 1136633 1710317 := bbase (se 3 (by rfl) ⟨320684, by rfl⟩ : syracuseStep 1710317 = 641369) (by norm_num)
theorem B1710341 : Blo 1136633 1710341 := bbase (se 4 (by rfl) ⟨160344, by rfl⟩ : syracuseStep 1710341 = 320689) (by norm_num)
theorem B2562317 : Blo 1136633 2562317 := bbase (se 3 (by rfl) ⟨480434, by rfl⟩ : syracuseStep 2562317 = 960869) (by norm_num)
theorem B1710365 : Blo 1136633 1710365 := bbase (se 3 (by rfl) ⟨320693, by rfl⟩ : syracuseStep 1710365 = 641387) (by norm_num)
theorem B1710389 : Blo 1136633 1710389 := bbase (se 5 (by rfl) ⟨80174, by rfl⟩ : syracuseStep 1710389 = 160349) (by norm_num)
theorem B1710413 : Blo 1136633 1710413 := bbase (se 3 (by rfl) ⟨320702, by rfl⟩ : syracuseStep 1710413 = 641405) (by norm_num)
theorem B2562389 : Blo 1136633 2562389 := bbase (se 10 (by rfl) ⟨3753, by rfl⟩ : syracuseStep 2562389 = 7507) (by norm_num)
theorem B1710437 : Blo 1136633 1710437 := bbase (se 4 (by rfl) ⟨160353, by rfl⟩ : syracuseStep 1710437 = 320707) (by norm_num)
theorem B1710461 : Blo 1136633 1710461 := bbase (se 3 (by rfl) ⟨320711, by rfl⟩ : syracuseStep 1710461 = 641423) (by norm_num)
theorem B1153429 : Blo 1136633 1153429 := bbase (se 6 (by rfl) ⟨27033, by rfl⟩ : syracuseStep 1153429 = 54067) (by norm_num)
theorem B1710485 : Blo 1136633 1710485 := bbase (se 6 (by rfl) ⟨40089, by rfl⟩ : syracuseStep 1710485 = 80179) (by norm_num)
theorem B2562461 : Blo 1136633 2562461 := bbase (se 3 (by rfl) ⟨480461, by rfl⟩ : syracuseStep 2562461 = 960923) (by norm_num)
theorem B1710509 : Blo 1136633 1710509 := bbase (se 3 (by rfl) ⟨320720, by rfl⟩ : syracuseStep 1710509 = 641441) (by norm_num)
theorem B1710533 : Blo 1136633 1710533 := bbase (se 4 (by rfl) ⟨160362, by rfl⟩ : syracuseStep 1710533 = 320725) (by norm_num)
theorem B1710557 : Blo 1136633 1710557 := bbase (se 3 (by rfl) ⟨320729, by rfl⟩ : syracuseStep 1710557 = 641459) (by norm_num)
theorem B2562533 : Blo 1136633 2562533 := bbase (se 4 (by rfl) ⟨240237, by rfl⟩ : syracuseStep 2562533 = 480475) (by norm_num)
theorem B1710581 : Blo 1136633 1710581 := bbase (se 5 (by rfl) ⟨80183, by rfl⟩ : syracuseStep 1710581 = 160367) (by norm_num)
theorem B1710605 : Blo 1136633 1710605 := bbase (se 3 (by rfl) ⟨320738, by rfl⟩ : syracuseStep 1710605 = 641477) (by norm_num)
theorem B3840533 : Blo 1136633 3840533 := bbase (se 6 (by rfl) ⟨90012, by rfl⟩ : syracuseStep 3840533 = 180025) (by norm_num)
theorem B1710629 : Blo 1136633 1710629 := bbase (se 4 (by rfl) ⟨160371, by rfl⟩ : syracuseStep 1710629 = 320743) (by norm_num)
theorem B2562605 : Blo 1136633 2562605 := bbase (se 3 (by rfl) ⟨480488, by rfl⟩ : syracuseStep 2562605 = 960977) (by norm_num)
theorem B1710653 : Blo 1136633 1710653 := bbase (se 3 (by rfl) ⟨320747, by rfl⟩ : syracuseStep 1710653 = 641495) (by norm_num)
theorem B1710677 : Blo 1136633 1710677 := bbase (se 8 (by rfl) ⟨10023, by rfl⟩ : syracuseStep 1710677 = 20047) (by norm_num)
theorem B2464357 : Blo 1136633 2464357 := bbase (se 4 (by rfl) ⟨231033, by rfl⟩ : syracuseStep 2464357 = 462067) (by norm_num)
theorem B1710701 : Blo 1136633 1710701 := bbase (se 3 (by rfl) ⟨320756, by rfl⟩ : syracuseStep 1710701 = 641513) (by norm_num)
theorem B1481329 : Blo 1136633 1481329 := bbase (se 2 (by rfl) ⟨555498, by rfl⟩ : syracuseStep 1481329 = 1110997) (by norm_num)
theorem B3644021 : Blo 1136633 3644021 := bbase (se 5 (by rfl) ⟨170813, by rfl⟩ : syracuseStep 3644021 = 341627) (by norm_num)
theorem B2562677 : Blo 1136633 2562677 := bbase (se 5 (by rfl) ⟨120125, by rfl⟩ : syracuseStep 2562677 = 240251) (by norm_num)
theorem B1710725 : Blo 1136633 1710725 := bbase (se 4 (by rfl) ⟨160380, by rfl⟩ : syracuseStep 1710725 = 320761) (by norm_num)
theorem B2431637 : Blo 1136633 2431637 := bbase (se 6 (by rfl) ⟨56991, by rfl⟩ : syracuseStep 2431637 = 113983) (by norm_num)
theorem B1710749 : Blo 1136633 1710749 := bbase (se 3 (by rfl) ⟨320765, by rfl⟩ : syracuseStep 1710749 = 641531) (by norm_num)
theorem B1710773 : Blo 1136633 1710773 := bbase (se 5 (by rfl) ⟨80192, by rfl⟩ : syracuseStep 1710773 = 160385) (by norm_num)
theorem B2562749 : Blo 1136633 2562749 := bbase (se 3 (by rfl) ⟨480515, by rfl⟩ : syracuseStep 2562749 = 961031) (by norm_num)
theorem B1710797 : Blo 1136633 1710797 := bbase (se 3 (by rfl) ⟨320774, by rfl⟩ : syracuseStep 1710797 = 641549) (by norm_num)
theorem B1710821 : Blo 1136633 1710821 := bbase (se 4 (by rfl) ⟨160389, by rfl⟩ : syracuseStep 1710821 = 320779) (by norm_num)
theorem B1710845 : Blo 1136633 1710845 := bbase (se 3 (by rfl) ⟨320783, by rfl⟩ : syracuseStep 1710845 = 641567) (by norm_num)
theorem B2562821 : Blo 1136633 2562821 := bbase (se 4 (by rfl) ⟨240264, by rfl⟩ : syracuseStep 2562821 = 480529) (by norm_num)
theorem B2431757 : Blo 1136633 2431757 := bbase (se 3 (by rfl) ⟨455954, by rfl⟩ : syracuseStep 2431757 = 911909) (by norm_num)
theorem B1710869 : Blo 1136633 1710869 := bbase (se 6 (by rfl) ⟨40098, by rfl⟩ : syracuseStep 1710869 = 80197) (by norm_num)
theorem B1645357 : Blo 1136633 1645357 := bbase (se 3 (by rfl) ⟨308504, by rfl⟩ : syracuseStep 1645357 = 617009) (by norm_num)
theorem B1710893 : Blo 1136633 1710893 := bbase (se 3 (by rfl) ⟨320792, by rfl⟩ : syracuseStep 1710893 = 641585) (by norm_num)
theorem B1710917 : Blo 1136633 1710917 := bbase (se 4 (by rfl) ⟨160398, by rfl⟩ : syracuseStep 1710917 = 320797) (by norm_num)
theorem B2562893 : Blo 1136633 2562893 := bbase (se 3 (by rfl) ⟨480542, by rfl⟩ : syracuseStep 2562893 = 961085) (by norm_num)
theorem B5774165 : Blo 1136633 5774165 := bbase (se 9 (by rfl) ⟨16916, by rfl⟩ : syracuseStep 5774165 = 33833) (by norm_num)
theorem B1710941 : Blo 1136633 1710941 := bbase (se 3 (by rfl) ⟨320801, by rfl⟩ : syracuseStep 1710941 = 641603) (by norm_num)
theorem B2562965 : Blo 1136633 2562965 := bbase (se 6 (by rfl) ⟨60069, by rfl⟩ : syracuseStep 2562965 = 120139) (by norm_num)
theorem B3283877 : Blo 1136633 3283877 := bbase (se 4 (by rfl) ⟨307863, by rfl⟩ : syracuseStep 3283877 = 615727) (by norm_num)
theorem B3840965 : Blo 1136633 3840965 := bbase (se 4 (by rfl) ⟨360090, by rfl⟩ : syracuseStep 3840965 = 720181) (by norm_num)
theorem B1153993 : Blo 1136633 1153993 := bbase (se 2 (by rfl) ⟨432747, by rfl⟩ : syracuseStep 1153993 = 865495) (by norm_num)
theorem B2563037 : Blo 1136633 2563037 := bbase (se 3 (by rfl) ⟨480569, by rfl⟩ : syracuseStep 2563037 = 961139) (by norm_num)
theorem B2563109 : Blo 1136633 2563109 := bbase (se 4 (by rfl) ⟨240291, by rfl⟩ : syracuseStep 2563109 = 480583) (by norm_num)
theorem B4856917 : Blo 1136633 4856917 := bbase (se 8 (by rfl) ⟨28458, by rfl⟩ : syracuseStep 4856917 = 56917) (by norm_num)
theorem B2563181 : Blo 1136633 2563181 := bbase (se 3 (by rfl) ⟨480596, by rfl⟩ : syracuseStep 2563181 = 961193) (by norm_num)
theorem B1481881 : Blo 1136633 1481881 := bbase (se 2 (by rfl) ⟨555705, by rfl⟩ : syracuseStep 1481881 = 1111411) (by norm_num)
theorem B2563253 : Blo 1136633 2563253 := bbase (se 5 (by rfl) ⟨120152, by rfl⟩ : syracuseStep 2563253 = 240305) (by norm_num)
theorem B2563325 : Blo 1136633 2563325 := bbase (se 3 (by rfl) ⟨480623, by rfl⟩ : syracuseStep 2563325 = 961247) (by norm_num)
theorem B2563397 : Blo 1136633 2563397 := bbase (se 4 (by rfl) ⟨240318, by rfl⟩ : syracuseStep 2563397 = 480637) (by norm_num)
theorem B3841397 : Blo 1136633 3841397 := bbase (se 5 (by rfl) ⟨180065, by rfl⟩ : syracuseStep 3841397 = 360131) (by norm_num)
theorem B2432389 : Blo 1136633 2432389 := bbase (se 4 (by rfl) ⟨228036, by rfl⟩ : syracuseStep 2432389 = 456073) (by norm_num)
theorem B2563469 : Blo 1136633 2563469 := bbase (se 3 (by rfl) ⟨480650, by rfl⟩ : syracuseStep 2563469 = 961301) (by norm_num)
theorem B2563541 : Blo 1136633 2563541 := bbase (se 7 (by rfl) ⟨30041, by rfl⟩ : syracuseStep 2563541 = 60083) (by norm_num)
theorem B1154557 : Blo 1136633 1154557 := bbase (se 3 (by rfl) ⟨216479, by rfl⟩ : syracuseStep 1154557 = 432959) (by norm_num)
theorem B2563613 : Blo 1136633 2563613 := bbase (se 3 (by rfl) ⟨480677, by rfl⟩ : syracuseStep 2563613 = 961355) (by norm_num)
theorem B2924093 : Blo 1136633 2924093 := bbase (se 3 (by rfl) ⟨548267, by rfl⟩ : syracuseStep 2924093 = 1096535) (by norm_num)
theorem B2563685 : Blo 1136633 2563685 := bbase (se 4 (by rfl) ⟨240345, by rfl⟩ : syracuseStep 2563685 = 480691) (by norm_num)
theorem B8756885 : Blo 1136633 8756885 := bbase (se 6 (by rfl) ⟨205239, by rfl⟩ : syracuseStep 8756885 = 410479) (by norm_num)
theorem B2563757 : Blo 1136633 2563757 := bbase (se 3 (by rfl) ⟨480704, by rfl⟩ : syracuseStep 2563757 = 961409) (by norm_num)
theorem B2563829 : Blo 1136633 2563829 := bbase (se 5 (by rfl) ⟨120179, by rfl⟩ : syracuseStep 2563829 = 240359) (by norm_num)
theorem B1154837 : Blo 1136633 1154837 := bbase (se 6 (by rfl) ⟨27066, by rfl⟩ : syracuseStep 1154837 = 54133) (by norm_num)
theorem B3841829 : Blo 1136633 3841829 := bbase (se 4 (by rfl) ⟨360171, by rfl⟩ : syracuseStep 3841829 = 720343) (by norm_num)
theorem B6922037 : Blo 1136633 6922037 := bbase (se 5 (by rfl) ⟨324470, by rfl⟩ : syracuseStep 6922037 = 648941) (by norm_num)
theorem B2563901 : Blo 1136633 2563901 := bbase (se 3 (by rfl) ⟨480731, by rfl⟩ : syracuseStep 2563901 = 961463) (by norm_num)
theorem B2563973 : Blo 1136633 2563973 := bbase (se 4 (by rfl) ⟨240372, by rfl⟩ : syracuseStep 2563973 = 480745) (by norm_num)
theorem B2564045 : Blo 1136633 2564045 := bbase (se 3 (by rfl) ⟨480758, by rfl⟩ : syracuseStep 2564045 = 961517) (by norm_num)
theorem B3645445 : Blo 1136633 3645445 := bbase (se 4 (by rfl) ⟨341760, by rfl⟩ : syracuseStep 3645445 = 683521) (by norm_num)
theorem B2564117 : Blo 1136633 2564117 := bbase (se 6 (by rfl) ⟨60096, by rfl⟩ : syracuseStep 2564117 = 120193) (by norm_num)
theorem B1155097 : Blo 1136633 1155097 := bbase (se 2 (by rfl) ⟨433161, by rfl⟩ : syracuseStep 1155097 = 866323) (by norm_num)
theorem B1482805 : Blo 1136633 1482805 := bbase (se 5 (by rfl) ⟨69506, by rfl⟩ : syracuseStep 1482805 = 139013) (by norm_num)
theorem B2564189 : Blo 1136633 2564189 := bbase (se 3 (by rfl) ⟨480785, by rfl⟩ : syracuseStep 2564189 = 961571) (by norm_num)
theorem B8659061 : Blo 1136633 8659061 := bbase (se 5 (by rfl) ⟨405893, by rfl⟩ : syracuseStep 8659061 = 811787) (by norm_num)
theorem B2924669 : Blo 1136633 2924669 := bbase (se 3 (by rfl) ⟨548375, by rfl⟩ : syracuseStep 2924669 = 1096751) (by norm_num)
theorem B2564261 : Blo 1136633 2564261 := bbase (se 4 (by rfl) ⟨240399, by rfl⟩ : syracuseStep 2564261 = 480799) (by norm_num)
theorem B2597069 : Blo 1136633 2597069 := bbase (se 3 (by rfl) ⟨486950, by rfl⟩ : syracuseStep 2597069 = 973901) (by norm_num)
theorem B3842261 : Blo 1136633 3842261 := bbase (se 7 (by rfl) ⟨45026, by rfl⟩ : syracuseStep 3842261 = 90053) (by norm_num)
theorem B2564333 : Blo 1136633 2564333 := bbase (se 3 (by rfl) ⟨480812, by rfl⟩ : syracuseStep 2564333 = 961625) (by norm_num)
theorem B2433277 : Blo 1136633 2433277 := bbase (se 3 (by rfl) ⟨456239, by rfl⟩ : syracuseStep 2433277 = 912479) (by norm_num)
theorem B2564405 : Blo 1136633 2564405 := bbase (se 5 (by rfl) ⟨120206, by rfl⟩ : syracuseStep 2564405 = 240413) (by norm_num)
theorem B1155421 : Blo 1136633 1155421 := bbase (se 3 (by rfl) ⟨216641, by rfl⟩ : syracuseStep 1155421 = 433283) (by norm_num)
theorem B2433397 : Blo 1136633 2433397 := bbase (se 5 (by rfl) ⟨114065, by rfl⟩ : syracuseStep 2433397 = 228131) (by norm_num)
theorem B2564477 : Blo 1136633 2564477 := bbase (se 3 (by rfl) ⟨480839, by rfl⟩ : syracuseStep 2564477 = 961679) (by norm_num)
theorem B2564549 : Blo 1136633 2564549 := bbase (se 4 (by rfl) ⟨240426, by rfl⟩ : syracuseStep 2564549 = 480853) (by norm_num)
theorem B2564621 : Blo 1136633 2564621 := bbase (se 3 (by rfl) ⟨480866, by rfl⟩ : syracuseStep 2564621 = 961733) (by norm_num)
theorem B39428693 : Blo 1136633 39428693 := bbase (se 8 (by rfl) ⟨231027, by rfl⟩ : syracuseStep 39428693 = 462055) (by norm_num)
theorem B2564693 : Blo 1136633 2564693 := bbase (se 8 (by rfl) ⟨15027, by rfl⟩ : syracuseStep 2564693 = 30055) (by norm_num)
theorem B2433653 : Blo 1136633 2433653 := bbase (se 5 (by rfl) ⟨114077, by rfl⟩ : syracuseStep 2433653 = 228155) (by norm_num)
theorem B2925181 : Blo 1136633 2925181 := bbase (se 3 (by rfl) ⟨548471, by rfl⟩ : syracuseStep 2925181 = 1096943) (by norm_num)
theorem B3842693 : Blo 1136633 3842693 := bbase (se 4 (by rfl) ⟨360252, by rfl⟩ : syracuseStep 3842693 = 720505) (by norm_num)
theorem B2564765 : Blo 1136633 2564765 := bbase (se 3 (by rfl) ⟨480893, by rfl⟩ : syracuseStep 2564765 = 961787) (by norm_num)
theorem B2564837 : Blo 1136633 2564837 := bbase (se 4 (by rfl) ⟨240453, by rfl⟩ : syracuseStep 2564837 = 480907) (by norm_num)
theorem B2564909 : Blo 1136633 2564909 := bbase (se 3 (by rfl) ⟨480920, by rfl⟩ : syracuseStep 2564909 = 961841) (by norm_num)
theorem B2564981 : Blo 1136633 2564981 := bbase (se 5 (by rfl) ⟨120233, by rfl⟩ : syracuseStep 2564981 = 240467) (by norm_num)
theorem B2565053 : Blo 1136633 2565053 := bbase (se 3 (by rfl) ⟨480947, by rfl⟩ : syracuseStep 2565053 = 961895) (by norm_num)
theorem B4105205 : Blo 1136633 4105205 := bbase (se 5 (by rfl) ⟨192431, by rfl⟩ : syracuseStep 4105205 = 384863) (by norm_num)
theorem B2565125 : Blo 1136633 2565125 := bbase (se 4 (by rfl) ⟨240480, by rfl⟩ : syracuseStep 2565125 = 480961) (by norm_num)
theorem B3843125 : Blo 1136633 3843125 := bbase (se 5 (by rfl) ⟨180146, by rfl⟩ : syracuseStep 3843125 = 360293) (by norm_num)
theorem B2565197 : Blo 1136633 2565197 := bbase (se 3 (by rfl) ⟨480974, by rfl⟩ : syracuseStep 2565197 = 961949) (by norm_num)
theorem B12297365 : Blo 1136633 12297365 := bbase (se 6 (by rfl) ⟨288219, by rfl⟩ : syracuseStep 12297365 = 576439) (by norm_num)
theorem B2565269 : Blo 1136633 2565269 := bbase (se 6 (by rfl) ⟨60123, by rfl⟩ : syracuseStep 2565269 = 120247) (by norm_num)
theorem B2335925 : Blo 1136633 2335925 := bbase (se 5 (by rfl) ⟨109496, by rfl⟩ : syracuseStep 2335925 = 218993) (by norm_num)
theorem B2401493 : Blo 1136633 2401493 := bbase (se 7 (by rfl) ⟨28142, by rfl⟩ : syracuseStep 2401493 = 56285) (by norm_num)
theorem B2565341 : Blo 1136633 2565341 := bbase (se 3 (by rfl) ⟨481001, by rfl⟩ : syracuseStep 2565341 = 962003) (by norm_num)
theorem B2565413 : Blo 1136633 2565413 := bbase (se 4 (by rfl) ⟨240507, by rfl⟩ : syracuseStep 2565413 = 481015) (by norm_num)
theorem B2565485 : Blo 1136633 2565485 := bbase (se 3 (by rfl) ⟨481028, by rfl⟩ : syracuseStep 2565485 = 962057) (by norm_num)
theorem B4105637 : Blo 1136633 4105637 := bbase (se 4 (by rfl) ⟨384903, by rfl⟩ : syracuseStep 4105637 = 769807) (by norm_num)
theorem B2565557 : Blo 1136633 2565557 := bbase (se 5 (by rfl) ⟨120260, by rfl⟩ : syracuseStep 2565557 = 240521) (by norm_num)
theorem B3843557 : Blo 1136633 3843557 := bbase (se 4 (by rfl) ⟨360333, by rfl⟩ : syracuseStep 3843557 = 720667) (by norm_num)
theorem B2434541 : Blo 1136633 2434541 := bbase (se 3 (by rfl) ⟨456476, by rfl⟩ : syracuseStep 2434541 = 912953) (by norm_num)
theorem B6235637 : Blo 1136633 6235637 := bbase (se 5 (by rfl) ⟨292295, by rfl⟩ : syracuseStep 6235637 = 584591) (by norm_num)
theorem B2565629 : Blo 1136633 2565629 := bbase (se 3 (by rfl) ⟨481055, by rfl⟩ : syracuseStep 2565629 = 962111) (by norm_num)
theorem B2336261 : Blo 1136633 2336261 := bbase (se 4 (by rfl) ⟨219024, by rfl⟩ : syracuseStep 2336261 = 438049) (by norm_num)
theorem B3647045 : Blo 1136633 3647045 := bbase (se 4 (by rfl) ⟨341910, by rfl⟩ : syracuseStep 3647045 = 683821) (by norm_num)
theorem B2565701 : Blo 1136633 2565701 := bbase (se 4 (by rfl) ⟨240534, by rfl⟩ : syracuseStep 2565701 = 481069) (by norm_num)
theorem B2565773 : Blo 1136633 2565773 := bbase (se 3 (by rfl) ⟨481082, by rfl⟩ : syracuseStep 2565773 = 962165) (by norm_num)
theorem B2565845 : Blo 1136633 2565845 := bbase (se 7 (by rfl) ⟨30068, by rfl⟩ : syracuseStep 2565845 = 60137) (by norm_num)
theorem B2434781 : Blo 1136633 2434781 := bbase (se 3 (by rfl) ⟨456521, by rfl⟩ : syracuseStep 2434781 = 913043) (by norm_num)
theorem B2565917 : Blo 1136633 2565917 := bbase (se 3 (by rfl) ⟨481109, by rfl⟩ : syracuseStep 2565917 = 962219) (by norm_num)
theorem B2598701 : Blo 1136633 2598701 := bbase (se 3 (by rfl) ⟨487256, by rfl⟩ : syracuseStep 2598701 = 974513) (by norm_num)
theorem B2565989 : Blo 1136633 2565989 := bbase (se 4 (by rfl) ⟨240561, by rfl⟩ : syracuseStep 2565989 = 481123) (by norm_num)
theorem B3843989 : Blo 1136633 3843989 := bbase (se 6 (by rfl) ⟨90093, by rfl⟩ : syracuseStep 3843989 = 180187) (by norm_num)
theorem B2566061 : Blo 1136633 2566061 := bbase (se 3 (by rfl) ⟨481136, by rfl⟩ : syracuseStep 2566061 = 962273) (by norm_num)
theorem B2566133 : Blo 1136633 2566133 := bbase (se 5 (by rfl) ⟨120287, by rfl⟩ : syracuseStep 2566133 = 240575) (by norm_num)
theorem B4859909 : Blo 1136633 4859909 := bbase (se 4 (by rfl) ⟨455616, by rfl⟩ : syracuseStep 4859909 = 911233) (by norm_num)
theorem B2566205 : Blo 1136633 2566205 := bbase (se 3 (by rfl) ⟨481163, by rfl⟩ : syracuseStep 2566205 = 962327) (by norm_num)
theorem B2566277 : Blo 1136633 2566277 := bbase (se 4 (by rfl) ⟨240588, by rfl⟩ : syracuseStep 2566277 = 481177) (by norm_num)
theorem B2566349 : Blo 1136633 2566349 := bbase (se 3 (by rfl) ⟨481190, by rfl⟩ : syracuseStep 2566349 = 962381) (by norm_num)
theorem B2435285 : Blo 1136633 2435285 := bbase (se 7 (by rfl) ⟨28538, by rfl⟩ : syracuseStep 2435285 = 57077) (by norm_num)
theorem B2435293 : Blo 1136633 2435293 := bbase (se 3 (by rfl) ⟨456617, by rfl⟩ : syracuseStep 2435293 = 913235) (by norm_num)
theorem B2566421 : Blo 1136633 2566421 := bbase (se 6 (by rfl) ⟨60150, by rfl⟩ : syracuseStep 2566421 = 120301) (by norm_num)
theorem B3844421 : Blo 1136633 3844421 := bbase (se 4 (by rfl) ⟨360414, by rfl⟩ : syracuseStep 3844421 = 720829) (by norm_num)
theorem B2468381 : Blo 1136633 2468381 := bbase (se 3 (by rfl) ⟨462821, by rfl⟩ : syracuseStep 2468381 = 925643) (by norm_num)
theorem B3648149 : Blo 1136633 3648149 := bbase (se 6 (by rfl) ⟨85503, by rfl⟩ : syracuseStep 3648149 = 171007) (by norm_num)
theorem B3844853 : Blo 1136633 3844853 := bbase (se 5 (by rfl) ⟨180227, by rfl⟩ : syracuseStep 3844853 = 360455) (by norm_num)
theorem B2960285 : Blo 1136633 2960285 := bbase (se 3 (by rfl) ⟨555053, by rfl⟩ : syracuseStep 2960285 = 1110107) (by norm_num)
theorem B4860917 : Blo 1136633 4860917 := bbase (se 5 (by rfl) ⟨227855, by rfl⟩ : syracuseStep 4860917 = 455711) (by norm_num)
theorem B2731085 : Blo 1136633 2731085 := bbase (se 3 (by rfl) ⟨512078, by rfl⟩ : syracuseStep 2731085 = 1024157) (by norm_num)
theorem B1944661 : Blo 1136633 1944661 := bbase (se 8 (by rfl) ⟨11394, by rfl⟩ : syracuseStep 1944661 = 22789) (by norm_num)
theorem B2731133 : Blo 1136633 2731133 := bbase (se 3 (by rfl) ⟨512087, by rfl⟩ : syracuseStep 2731133 = 1024175) (by norm_num)
theorem B3845285 : Blo 1136633 3845285 := bbase (se 4 (by rfl) ⟨360495, by rfl⟩ : syracuseStep 3845285 = 720991) (by norm_num)
theorem B2305333 : Blo 1136633 2305333 := bbase (se 5 (by rfl) ⟨108062, by rfl⟩ : syracuseStep 2305333 = 216125) (by norm_num)
theorem B2731421 : Blo 1136633 2731421 := bbase (se 3 (by rfl) ⟨512141, by rfl⟩ : syracuseStep 2731421 = 1024283) (by norm_num)
theorem B3845717 : Blo 1136633 3845717 := bbase (se 8 (by rfl) ⟨22533, by rfl⟩ : syracuseStep 3845717 = 45067) (by norm_num)
theorem B3846149 : Blo 1136633 3846149 := bbase (se 4 (by rfl) ⟨360576, by rfl⟩ : syracuseStep 3846149 = 721153) (by norm_num)
theorem B2077085 : Blo 1136633 2077085 := bbase (se 3 (by rfl) ⟨389453, by rfl⟩ : syracuseStep 2077085 = 778907) (by norm_num)
theorem B7287221 : Blo 1136633 7287221 := bbase (se 5 (by rfl) ⟨341588, by rfl⟩ : syracuseStep 7287221 = 683177) (by norm_num)
theorem B3846581 : Blo 1136633 3846581 := bbase (se 5 (by rfl) ⟨180308, by rfl⟩ : syracuseStep 3846581 = 360617) (by norm_num)
theorem B3650069 : Blo 1136633 3650069 := bbase (se 6 (by rfl) ⟨85548, by rfl⟩ : syracuseStep 3650069 = 171097) (by norm_num)
theorem B4993589 : Blo 1136633 4993589 := bbase (se 5 (by rfl) ⟨234074, by rfl⟩ : syracuseStep 4993589 = 468149) (by norm_num)
theorem B1847909 : Blo 1136633 1847909 := bbase (se 4 (by rfl) ⟨173241, by rfl⟩ : syracuseStep 1847909 = 346483) (by norm_num)
theorem B4108981 : Blo 1136633 4108981 := bbase (se 5 (by rfl) ⟨192608, by rfl⟩ : syracuseStep 4108981 = 385217) (by norm_num)
theorem B4862693 : Blo 1136633 4862693 := bbase (se 4 (by rfl) ⟨455877, by rfl⟩ : syracuseStep 4862693 = 911755) (by norm_num)
theorem B10957589 : Blo 1136633 10957589 := bbase (se 6 (by rfl) ⟨256818, by rfl⟩ : syracuseStep 10957589 = 513637) (by norm_num)
theorem B3847013 : Blo 1136633 3847013 := bbase (se 4 (by rfl) ⟨360657, by rfl⟩ : syracuseStep 3847013 = 721315) (by norm_num)
theorem B1618813 : Blo 1136633 1618813 := bbase (se 3 (by rfl) ⟨303527, by rfl⟩ : syracuseStep 1618813 = 607055) (by norm_num)
theorem B2306989 : Blo 1136633 2306989 := bbase (se 3 (by rfl) ⟨432560, by rfl⟩ : syracuseStep 2306989 = 865121) (by norm_num)
theorem B2339813 : Blo 1136633 2339813 := bbase (se 4 (by rfl) ⟨219357, by rfl⟩ : syracuseStep 2339813 = 438715) (by norm_num)
theorem B3847445 : Blo 1136633 3847445 := bbase (se 6 (by rfl) ⟨90174, by rfl⟩ : syracuseStep 3847445 = 180349) (by norm_num)
theorem B1946933 : Blo 1136633 1946933 := bbase (se 5 (by rfl) ⟨91262, by rfl⟩ : syracuseStep 1946933 = 182525) (by norm_num)
theorem B9876917 : Blo 1136633 9876917 := bbase (se 5 (by rfl) ⟨462980, by rfl⟩ : syracuseStep 9876917 = 925961) (by norm_num)
theorem B1619605 : Blo 1136633 1619605 := bbase (se 6 (by rfl) ⟨37959, by rfl⟩ : syracuseStep 1619605 = 75919) (by norm_num)
theorem B3847877 : Blo 1136633 3847877 := bbase (se 4 (by rfl) ⟨360738, by rfl⟩ : syracuseStep 3847877 = 721477) (by norm_num)
theorem B2733853 : Blo 1136633 2733853 := bbase (se 3 (by rfl) ⟨512597, by rfl⟩ : syracuseStep 2733853 = 1025195) (by norm_num)
theorem B1947493 : Blo 1136633 1947493 := bbase (se 4 (by rfl) ⟨182577, by rfl⟩ : syracuseStep 1947493 = 365155) (by norm_num)
theorem B3651493 : Blo 1136633 3651493 := bbase (se 4 (by rfl) ⟨342327, by rfl⟩ : syracuseStep 3651493 = 684655) (by norm_num)
theorem B1619941 : Blo 1136633 1619941 := bbase (se 4 (by rfl) ⟨151869, by rfl⟩ : syracuseStep 1619941 = 303739) (by norm_num)
theorem B2308117 : Blo 1136633 2308117 := bbase (se 6 (by rfl) ⟨54096, by rfl⟩ : syracuseStep 2308117 = 108193) (by norm_num)
theorem B2340949 : Blo 1136633 2340949 := bbase (se 8 (by rfl) ⟨13716, by rfl⟩ : syracuseStep 2340949 = 27433) (by norm_num)
theorem B2308189 : Blo 1136633 2308189 := bbase (se 3 (by rfl) ⟨432785, by rfl⟩ : syracuseStep 2308189 = 865571) (by norm_num)
theorem B3848309 : Blo 1136633 3848309 := bbase (se 5 (by rfl) ⟨180389, by rfl⟩ : syracuseStep 3848309 = 360779) (by norm_num)
theorem B17315989 : Blo 1136633 17315989 := bbase (se 6 (by rfl) ⟨405843, by rfl⟩ : syracuseStep 17315989 = 811687) (by norm_num)
theorem B1620157 : Blo 1136633 1620157 := bbase (se 3 (by rfl) ⟨303779, by rfl⟩ : syracuseStep 1620157 = 607559) (by norm_num)
theorem B3651941 : Blo 1136633 3651941 := bbase (se 4 (by rfl) ⟨342369, by rfl⟩ : syracuseStep 3651941 = 684739) (by norm_num)
theorem B2734469 : Blo 1136633 2734469 := bbase (se 4 (by rfl) ⟨256356, by rfl⟩ : syracuseStep 2734469 = 512713) (by norm_num)
theorem B3291637 : Blo 1136633 3291637 := bbase (se 5 (by rfl) ⟨154295, by rfl⟩ : syracuseStep 3291637 = 308591) (by norm_num)
theorem B3848741 : Blo 1136633 3848741 := bbase (se 4 (by rfl) ⟨360819, by rfl⟩ : syracuseStep 3848741 = 721639) (by norm_num)
theorem B1620533 : Blo 1136633 1620533 := bbase (se 5 (by rfl) ⟨75962, by rfl⟩ : syracuseStep 1620533 = 151925) (by norm_num)
theorem B2734669 : Blo 1136633 2734669 := bbase (se 3 (by rfl) ⟨512750, by rfl⟩ : syracuseStep 2734669 = 1025501) (by norm_num)
theorem B5192549 : Blo 1136633 5192549 := bbase (se 4 (by rfl) ⟨486801, by rfl⟩ : syracuseStep 5192549 = 973603) (by norm_num)
theorem B3849173 : Blo 1136633 3849173 := bbase (se 7 (by rfl) ⟨45107, by rfl⟩ : syracuseStep 3849173 = 90215) (by norm_num)
theorem B2309285 : Blo 1136633 2309285 := bbase (se 4 (by rfl) ⟨216495, by rfl⟩ : syracuseStep 2309285 = 432991) (by norm_num)
theorem B2735477 : Blo 1136633 2735477 := bbase (se 5 (by rfl) ⟨128225, by rfl⟩ : syracuseStep 2735477 = 256451) (by norm_num)
theorem B3849605 : Blo 1136633 3849605 := bbase (se 4 (by rfl) ⟨360900, by rfl⟩ : syracuseStep 3849605 = 721801) (by norm_num)
theorem B8764885 : Blo 1136633 8764885 := bbase (se 7 (by rfl) ⟨102713, by rfl⟩ : syracuseStep 8764885 = 205427) (by norm_num)
theorem B1621957 : Blo 1136633 1621957 := bbase (se 4 (by rfl) ⟨152058, by rfl⟩ : syracuseStep 1621957 = 304117) (by norm_num)
theorem B2736245 : Blo 1136633 2736245 := bbase (se 5 (by rfl) ⟨128261, by rfl⟩ : syracuseStep 2736245 = 256523) (by norm_num)
theorem B7291093 : Blo 1136633 7291093 := bbase (se 7 (by rfl) ⟨85442, by rfl⟩ : syracuseStep 7291093 = 170885) (by norm_num)
theorem B9716021 : Blo 1136633 9716021 := bbase (se 5 (by rfl) ⟨455438, by rfl⟩ : syracuseStep 9716021 = 910877) (by norm_num)
theorem B1622549 : Blo 1136633 1622549 := bbase (se 6 (by rfl) ⟨38028, by rfl⟩ : syracuseStep 1622549 = 76057) (by norm_num)
theorem B1622629 : Blo 1136633 1622629 := bbase (se 4 (by rfl) ⟨152121, by rfl⟩ : syracuseStep 1622629 = 304243) (by norm_num)
theorem B1622749 : Blo 1136633 1622749 := bbase (se 3 (by rfl) ⟨304265, by rfl⟩ : syracuseStep 1622749 = 608531) (by norm_num)
theorem B10535669 : Blo 1136633 10535669 := bbase (se 5 (by rfl) ⟨493859, by rfl⟩ : syracuseStep 10535669 = 987719) (by norm_num)
theorem B1622845 : Blo 1136633 1622845 := bbase (se 3 (by rfl) ⟨304283, by rfl⟩ : syracuseStep 1622845 = 608567) (by norm_num)
theorem B4866965 : Blo 1136633 4866965 := bbase (se 6 (by rfl) ⟨114069, by rfl⟩ : syracuseStep 4866965 = 228139) (by norm_num)
theorem B4932677 : Blo 1136633 4932677 := bbase (se 4 (by rfl) ⟨462438, by rfl⟩ : syracuseStep 4932677 = 924877) (by norm_num)
theorem B1918093 : Blo 1136633 1918093 := bbase (se 3 (by rfl) ⟨359642, by rfl⟩ : syracuseStep 1918093 = 719285) (by norm_num)
theorem B1918181 : Blo 1136633 1918181 := bbase (se 4 (by rfl) ⟨179829, by rfl⟩ : syracuseStep 1918181 = 359659) (by norm_num)
theorem B1623341 : Blo 1136633 1623341 := bbase (se 3 (by rfl) ⟨304376, by rfl⟩ : syracuseStep 1623341 = 608753) (by norm_num)
theorem B2770229 : Blo 1136633 2770229 := bbase (se 5 (by rfl) ⟨129854, by rfl⟩ : syracuseStep 2770229 = 259709) (by norm_num)
theorem B6931765 : Blo 1136633 6931765 := bbase (se 5 (by rfl) ⟨324926, by rfl⟩ : syracuseStep 6931765 = 649853) (by norm_num)
theorem B8635733 : Blo 1136633 8635733 := bbase (se 12 (by rfl) ⟨3162, by rfl⟩ : syracuseStep 8635733 = 6325) (by norm_num)
theorem B1918309 : Blo 1136633 1918309 := bbase (se 4 (by rfl) ⟨179841, by rfl⟩ : syracuseStep 1918309 = 359683) (by norm_num)
theorem B1918397 : Blo 1136633 1918397 := bbase (se 3 (by rfl) ⟨359699, by rfl⟩ : syracuseStep 1918397 = 719399) (by norm_num)
theorem B1918525 : Blo 1136633 1918525 := bbase (se 3 (by rfl) ⟨359723, by rfl⟩ : syracuseStep 1918525 = 719447) (by norm_num)
theorem B1918613 : Blo 1136633 1918613 := bbase (se 6 (by rfl) ⟨44967, by rfl⟩ : syracuseStep 1918613 = 89935) (by norm_num)
theorem B1918741 : Blo 1136633 1918741 := bbase (se 6 (by rfl) ⟨44970, by rfl⟩ : syracuseStep 1918741 = 89941) (by norm_num)
theorem B2737957 : Blo 1136633 2737957 := bbase (se 4 (by rfl) ⟨256683, by rfl⟩ : syracuseStep 2737957 = 513367) (by norm_num)
theorem B2049877 : Blo 1136633 2049877 := bbase (se 9 (by rfl) ⟨6005, by rfl⟩ : syracuseStep 2049877 = 12011) (by norm_num)
theorem B1623893 : Blo 1136633 1623893 := bbase (se 9 (by rfl) ⟨4757, by rfl⟩ : syracuseStep 1623893 = 9515) (by norm_num)
theorem B1918829 : Blo 1136633 1918829 := bbase (se 3 (by rfl) ⟨359780, by rfl⟩ : syracuseStep 1918829 = 719561) (by norm_num)
theorem B1918957 : Blo 1136633 1918957 := bbase (se 3 (by rfl) ⟨359804, by rfl⟩ : syracuseStep 1918957 = 719609) (by norm_num)
theorem B1919045 : Blo 1136633 1919045 := bbase (se 4 (by rfl) ⟨179910, by rfl⟩ : syracuseStep 1919045 = 359821) (by norm_num)
theorem B2312309 : Blo 1136633 2312309 := bbase (se 5 (by rfl) ⟨108389, by rfl⟩ : syracuseStep 2312309 = 216779) (by norm_num)
theorem B1296541 : Blo 1136633 1296541 := bbase (se 3 (by rfl) ⟨243101, by rfl⟩ : syracuseStep 1296541 = 486203) (by norm_num)
theorem B1919173 : Blo 1136633 1919173 := bbase (se 4 (by rfl) ⟨179922, by rfl⟩ : syracuseStep 1919173 = 359845) (by norm_num)
theorem B1919261 : Blo 1136633 1919261 := bbase (se 3 (by rfl) ⟨359861, by rfl⟩ : syracuseStep 1919261 = 719723) (by norm_num)
theorem B1821037 : Blo 1136633 1821037 := bbase (se 3 (by rfl) ⟨341444, by rfl⟩ : syracuseStep 1821037 = 682889) (by norm_num)
theorem B2738573 : Blo 1136633 2738573 := bbase (se 3 (by rfl) ⟨513482, by rfl⟩ : syracuseStep 2738573 = 1026965) (by norm_num)
theorem B1919389 : Blo 1136633 1919389 := bbase (se 3 (by rfl) ⟨359885, by rfl⟩ : syracuseStep 1919389 = 719771) (by norm_num)
theorem B1821133 : Blo 1136633 1821133 := bbase (se 3 (by rfl) ⟨341462, by rfl⟩ : syracuseStep 1821133 = 682925) (by norm_num)
theorem B4442597 : Blo 1136633 4442597 := bbase (se 4 (by rfl) ⟨416493, by rfl⟩ : syracuseStep 4442597 = 832987) (by norm_num)
theorem B1919477 : Blo 1136633 1919477 := bbase (se 5 (by rfl) ⟨89975, by rfl⟩ : syracuseStep 1919477 = 179951) (by norm_num)
theorem B1296929 : Blo 1136633 1296929 := bbase (se 2 (by rfl) ⟨486348, by rfl⟩ : syracuseStep 1296929 = 972697) (by norm_num)
theorem B1821293 : Blo 1136633 1821293 := bbase (se 3 (by rfl) ⟨341492, by rfl⟩ : syracuseStep 1821293 = 682985) (by norm_num)
theorem B1919605 : Blo 1136633 1919605 := bbase (se 5 (by rfl) ⟨89981, by rfl⟩ : syracuseStep 1919605 = 179963) (by norm_num)
theorem B1460857 : Blo 1136633 1460857 := bbase (se 2 (by rfl) ⟨547821, by rfl⟩ : syracuseStep 1460857 = 1095643) (by norm_num)
theorem B2050685 : Blo 1136633 2050685 := bbase (se 3 (by rfl) ⟨384503, by rfl⟩ : syracuseStep 2050685 = 769007) (by norm_num)
theorem B4868741 : Blo 1136633 4868741 := bbase (se 4 (by rfl) ⟨456444, by rfl⟩ : syracuseStep 4868741 = 912889) (by norm_num)
theorem B1919693 : Blo 1136633 1919693 := bbase (se 3 (by rfl) ⟨359942, by rfl⟩ : syracuseStep 1919693 = 719885) (by norm_num)
theorem B2739005 : Blo 1136633 2739005 := bbase (se 3 (by rfl) ⟨513563, by rfl⟩ : syracuseStep 2739005 = 1027127) (by norm_num)
theorem B1919821 : Blo 1136633 1919821 := bbase (se 3 (by rfl) ⟨359966, by rfl⟩ : syracuseStep 1919821 = 719933) (by norm_num)
theorem B6474613 : Blo 1136633 6474613 := bbase (se 5 (by rfl) ⟨303497, by rfl⟩ : syracuseStep 6474613 = 606995) (by norm_num)
theorem B4868981 : Blo 1136633 4868981 := bbase (se 5 (by rfl) ⟨228233, by rfl⟩ : syracuseStep 4868981 = 456467) (by norm_num)
theorem B4377509 : Blo 1136633 4377509 := bbase (se 4 (by rfl) ⟨410391, by rfl⟩ : syracuseStep 4377509 = 820783) (by norm_num)
theorem B1919909 : Blo 1136633 1919909 := bbase (se 4 (by rfl) ⟨179991, by rfl⟩ : syracuseStep 1919909 = 359983) (by norm_num)
theorem B1920037 : Blo 1136633 1920037 := bbase (se 4 (by rfl) ⟨180003, by rfl⟩ : syracuseStep 1920037 = 360007) (by norm_num)
theorem B1461349 : Blo 1136633 1461349 := bbase (se 4 (by rfl) ⟨137001, by rfl⟩ : syracuseStep 1461349 = 274003) (by norm_num)
theorem B1920125 : Blo 1136633 1920125 := bbase (se 3 (by rfl) ⟨360023, by rfl⟩ : syracuseStep 1920125 = 720047) (by norm_num)
theorem B1920253 : Blo 1136633 1920253 := bbase (se 3 (by rfl) ⟨360047, by rfl⟩ : syracuseStep 1920253 = 720095) (by norm_num)
theorem B1920341 : Blo 1136633 1920341 := bbase (se 11 (by rfl) ⟨1406, by rfl⟩ : syracuseStep 1920341 = 2813) (by norm_num)
theorem B5328293 : Blo 1136633 5328293 := bbase (se 4 (by rfl) ⟨499527, by rfl⟩ : syracuseStep 5328293 = 999055) (by norm_num)
theorem B1920469 : Blo 1136633 1920469 := bbase (se 7 (by rfl) ⟨22505, by rfl⟩ : syracuseStep 1920469 = 45011) (by norm_num)
theorem B1920557 : Blo 1136633 1920557 := bbase (se 3 (by rfl) ⟨360104, by rfl⟩ : syracuseStep 1920557 = 720209) (by norm_num)
theorem B1920685 : Blo 1136633 1920685 := bbase (se 3 (by rfl) ⟨360128, by rfl⟩ : syracuseStep 1920685 = 720257) (by norm_num)
theorem B1822421 : Blo 1136633 1822421 := bbase (se 7 (by rfl) ⟨21356, by rfl⟩ : syracuseStep 1822421 = 42713) (by norm_num)
theorem B1920773 : Blo 1136633 1920773 := bbase (se 4 (by rfl) ⟨180072, by rfl⟩ : syracuseStep 1920773 = 360145) (by norm_num)
theorem B5754725 : Blo 1136633 5754725 := bbase (se 4 (by rfl) ⟨539505, by rfl⟩ : syracuseStep 5754725 = 1079011) (by norm_num)
theorem B1920901 : Blo 1136633 1920901 := bbase (se 4 (by rfl) ⟨180084, by rfl⟩ : syracuseStep 1920901 = 360169) (by norm_num)
theorem B1920989 : Blo 1136633 1920989 := bbase (se 3 (by rfl) ⟨360185, by rfl⟩ : syracuseStep 1920989 = 720371) (by norm_num)
theorem B2740205 : Blo 1136633 2740205 := bbase (se 3 (by rfl) ⟨513788, by rfl⟩ : syracuseStep 2740205 = 1027577) (by norm_num)
theorem B1921117 : Blo 1136633 1921117 := bbase (se 3 (by rfl) ⟨360209, by rfl⟩ : syracuseStep 1921117 = 720419) (by norm_num)
theorem B1298557 : Blo 1136633 1298557 := bbase (se 3 (by rfl) ⟨243479, by rfl⟩ : syracuseStep 1298557 = 486959) (by norm_num)
theorem B1921205 : Blo 1136633 1921205 := bbase (se 5 (by rfl) ⟨90056, by rfl⟩ : syracuseStep 1921205 = 180113) (by norm_num)
theorem B1822933 : Blo 1136633 1822933 := bbase (se 7 (by rfl) ⟨21362, by rfl⟩ : syracuseStep 1822933 = 42725) (by norm_num)
theorem B1921333 : Blo 1136633 1921333 := bbase (se 5 (by rfl) ⟨90062, by rfl⟩ : syracuseStep 1921333 = 180125) (by norm_num)
theorem B1921421 : Blo 1136633 1921421 := bbase (se 3 (by rfl) ⟨360266, by rfl⟩ : syracuseStep 1921421 = 720533) (by norm_num)
theorem B1921549 : Blo 1136633 1921549 := bbase (se 3 (by rfl) ⟨360290, by rfl⟩ : syracuseStep 1921549 = 720581) (by norm_num)
theorem B18469397 : Blo 1136633 18469397 := bbase (se 6 (by rfl) ⟨432876, by rfl⟩ : syracuseStep 18469397 = 865753) (by norm_num)
theorem B1921637 : Blo 1136633 1921637 := bbase (se 4 (by rfl) ⟨180153, by rfl⟩ : syracuseStep 1921637 = 360307) (by norm_num)
theorem B1921765 : Blo 1136633 1921765 := bbase (se 4 (by rfl) ⟨180165, by rfl⟩ : syracuseStep 1921765 = 360331) (by norm_num)
theorem B6476597 : Blo 1136633 6476597 := bbase (se 5 (by rfl) ⟨303590, by rfl⟩ : syracuseStep 6476597 = 607181) (by norm_num)
theorem B1921853 : Blo 1136633 1921853 := bbase (se 3 (by rfl) ⟨360347, by rfl⟩ : syracuseStep 1921853 = 720695) (by norm_num)
theorem B1921981 : Blo 1136633 1921981 := bbase (se 3 (by rfl) ⟨360371, by rfl⟩ : syracuseStep 1921981 = 720743) (by norm_num)
theorem B1922069 : Blo 1136633 1922069 := bbase (se 6 (by rfl) ⟨45048, by rfl⟩ : syracuseStep 1922069 = 90097) (by norm_num)
theorem B4871269 : Blo 1136633 4871269 := bbase (se 4 (by rfl) ⟨456681, by rfl⟩ : syracuseStep 4871269 = 913363) (by norm_num)
theorem B5756021 : Blo 1136633 5756021 := bbase (se 5 (by rfl) ⟨269813, by rfl⟩ : syracuseStep 5756021 = 539627) (by norm_num)
theorem B1922197 : Blo 1136633 1922197 := bbase (se 6 (by rfl) ⟨45051, by rfl⟩ : syracuseStep 1922197 = 90103) (by norm_num)
theorem B1823933 : Blo 1136633 1823933 := bbase (se 3 (by rfl) ⟨341987, by rfl⟩ : syracuseStep 1823933 = 683975) (by norm_num)
theorem B1922285 : Blo 1136633 1922285 := bbase (se 3 (by rfl) ⟨360428, by rfl⟩ : syracuseStep 1922285 = 720857) (by norm_num)
theorem B1824061 : Blo 1136633 1824061 := bbase (se 3 (by rfl) ⟨342011, by rfl⟩ : syracuseStep 1824061 = 684023) (by norm_num)
theorem B2053453 : Blo 1136633 2053453 := bbase (se 3 (by rfl) ⟨385022, by rfl⟩ : syracuseStep 2053453 = 770045) (by norm_num)
theorem B1922413 : Blo 1136633 1922413 := bbase (se 3 (by rfl) ⟨360452, by rfl⟩ : syracuseStep 1922413 = 720905) (by norm_num)
theorem B1824125 : Blo 1136633 1824125 := bbase (se 3 (by rfl) ⟨342023, by rfl⟩ : syracuseStep 1824125 = 684047) (by norm_num)
theorem B1922501 : Blo 1136633 1922501 := bbase (se 4 (by rfl) ⟨180234, by rfl⟩ : syracuseStep 1922501 = 360469) (by norm_num)
theorem B1922629 : Blo 1136633 1922629 := bbase (se 4 (by rfl) ⟨180246, by rfl⟩ : syracuseStep 1922629 = 360493) (by norm_num)
theorem B1300045 : Blo 1136633 1300045 := bbase (se 3 (by rfl) ⟨243758, by rfl⟩ : syracuseStep 1300045 = 487517) (by norm_num)
theorem B1922717 : Blo 1136633 1922717 := bbase (se 3 (by rfl) ⟨360509, by rfl⟩ : syracuseStep 1922717 = 721019) (by norm_num)
theorem B1922845 : Blo 1136633 1922845 := bbase (se 3 (by rfl) ⟨360533, by rfl⟩ : syracuseStep 1922845 = 721067) (by norm_num)
theorem B1922933 : Blo 1136633 1922933 := bbase (se 5 (by rfl) ⟨90137, by rfl⟩ : syracuseStep 1922933 = 180275) (by norm_num)
theorem B2054029 : Blo 1136633 2054029 := bbase (se 3 (by rfl) ⟨385130, by rfl⟩ : syracuseStep 2054029 = 770261) (by norm_num)
theorem B1365941 : Blo 1136633 1365941 := bbase (se 5 (by rfl) ⟨64028, by rfl⟩ : syracuseStep 1365941 = 128057) (by norm_num)
theorem B1923061 : Blo 1136633 1923061 := bbase (se 5 (by rfl) ⟨90143, by rfl⟩ : syracuseStep 1923061 = 180287) (by norm_num)
theorem B1923149 : Blo 1136633 1923149 := bbase (se 3 (by rfl) ⟨360590, by rfl⟩ : syracuseStep 1923149 = 721181) (by norm_num)
theorem B1923277 : Blo 1136633 1923277 := bbase (se 3 (by rfl) ⟨360614, by rfl⟩ : syracuseStep 1923277 = 721229) (by norm_num)
theorem B1366249 : Blo 1136633 1366249 := bbase (se 2 (by rfl) ⟨512343, by rfl⟩ : syracuseStep 1366249 = 1024687) (by norm_num)
theorem B1366277 : Blo 1136633 1366277 := bbase (se 4 (by rfl) ⟨128088, by rfl⟩ : syracuseStep 1366277 = 256177) (by norm_num)
theorem B1923365 : Blo 1136633 1923365 := bbase (se 4 (by rfl) ⟨180315, by rfl⟩ : syracuseStep 1923365 = 360631) (by norm_num)
theorem B11688245 : Blo 1136633 11688245 := bbase (se 5 (by rfl) ⟨547886, by rfl⟩ : syracuseStep 11688245 = 1095773) (by norm_num)
theorem B5757317 : Blo 1136633 5757317 := bbase (se 4 (by rfl) ⟨539748, by rfl⟩ : syracuseStep 5757317 = 1079497) (by norm_num)
theorem B1923493 : Blo 1136633 1923493 := bbase (se 4 (by rfl) ⟨180327, by rfl⟩ : syracuseStep 1923493 = 360655) (by norm_num)
theorem B8214965 : Blo 1136633 8214965 := bbase (se 5 (by rfl) ⟨385076, by rfl⟩ : syracuseStep 8214965 = 770153) (by norm_num)
theorem B1923581 : Blo 1136633 1923581 := bbase (se 3 (by rfl) ⟨360671, by rfl⟩ : syracuseStep 1923581 = 721343) (by norm_num)
theorem B2054693 : Blo 1136633 2054693 := bbase (se 4 (by rfl) ⟨192627, by rfl⟩ : syracuseStep 2054693 = 385255) (by norm_num)
theorem B1923709 : Blo 1136633 1923709 := bbase (se 3 (by rfl) ⟨360695, by rfl⟩ : syracuseStep 1923709 = 721391) (by norm_num)
theorem B1825445 : Blo 1136633 1825445 := bbase (se 4 (by rfl) ⟨171135, by rfl⟩ : syracuseStep 1825445 = 342271) (by norm_num)
theorem B1923797 : Blo 1136633 1923797 := bbase (se 7 (by rfl) ⟨22544, by rfl⟩ : syracuseStep 1923797 = 45089) (by norm_num)
theorem B1366777 : Blo 1136633 1366777 := bbase (se 2 (by rfl) ⟨512541, by rfl⟩ : syracuseStep 1366777 = 1025083) (by norm_num)
theorem B2054909 : Blo 1136633 2054909 := bbase (se 3 (by rfl) ⟨385295, by rfl⟩ : syracuseStep 2054909 = 770591) (by norm_num)
theorem B1825573 : Blo 1136633 1825573 := bbase (se 4 (by rfl) ⟨171147, by rfl⟩ : syracuseStep 1825573 = 342295) (by norm_num)
theorem B1923925 : Blo 1136633 1923925 := bbase (se 9 (by rfl) ⟨5636, by rfl⟩ : syracuseStep 1923925 = 11273) (by norm_num)
theorem B1924013 : Blo 1136633 1924013 := bbase (se 3 (by rfl) ⟨360752, by rfl⟩ : syracuseStep 1924013 = 721505) (by norm_num)
theorem B6478805 : Blo 1136633 6478805 := bbase (se 7 (by rfl) ⟨75923, by rfl⟩ : syracuseStep 6478805 = 151847) (by norm_num)
theorem B3890197 : Blo 1136633 3890197 := bbase (se 6 (by rfl) ⟨91176, by rfl⟩ : syracuseStep 3890197 = 182353) (by norm_num)
theorem B1924141 : Blo 1136633 1924141 := bbase (se 3 (by rfl) ⟨360776, by rfl⟩ : syracuseStep 1924141 = 721553) (by norm_num)
theorem B1924229 : Blo 1136633 1924229 := bbase (se 4 (by rfl) ⟨180396, by rfl⟩ : syracuseStep 1924229 = 360793) (by norm_num)
theorem B10935445 : Blo 1136633 10935445 := bbase (se 6 (by rfl) ⟨256299, by rfl⟩ : syracuseStep 10935445 = 512599) (by norm_num)
theorem B2055413 : Blo 1136633 2055413 := bbase (se 5 (by rfl) ⟨96347, by rfl⟩ : syracuseStep 2055413 = 192695) (by norm_num)
theorem B1924357 : Blo 1136633 1924357 := bbase (se 4 (by rfl) ⟨180408, by rfl⟩ : syracuseStep 1924357 = 360817) (by norm_num)
theorem B1924445 : Blo 1136633 1924445 := bbase (se 3 (by rfl) ⟨360833, by rfl⟩ : syracuseStep 1924445 = 721667) (by norm_num)
theorem B1924573 : Blo 1136633 1924573 := bbase (se 3 (by rfl) ⟨360857, by rfl⟩ : syracuseStep 1924573 = 721715) (by norm_num)
theorem B1924661 : Blo 1136633 1924661 := bbase (se 5 (by rfl) ⟨90218, by rfl⟩ : syracuseStep 1924661 = 180437) (by norm_num)
theorem B1826381 : Blo 1136633 1826381 := bbase (se 3 (by rfl) ⟨342446, by rfl⟩ : syracuseStep 1826381 = 684893) (by norm_num)
theorem B4316773 : Blo 1136633 4316773 := bbase (se 4 (by rfl) ⟨404697, by rfl⟩ : syracuseStep 4316773 = 809395) (by norm_num)
theorem B2252405 : Blo 1136633 2252405 := bbase (se 5 (by rfl) ⟨105581, by rfl⟩ : syracuseStep 2252405 = 211163) (by norm_num)
theorem B5758613 : Blo 1136633 5758613 := bbase (se 6 (by rfl) ⟨134967, by rfl⟩ : syracuseStep 5758613 = 269935) (by norm_num)
theorem B5004965 : Blo 1136633 5004965 := bbase (se 4 (by rfl) ⟨469215, by rfl⟩ : syracuseStep 5004965 = 938431) (by norm_num)
theorem B1924789 : Blo 1136633 1924789 := bbase (se 5 (by rfl) ⟨90224, by rfl⟩ : syracuseStep 1924789 = 180449) (by norm_num)
theorem B7790357 : Blo 1136633 7790357 := bbase (se 6 (by rfl) ⟨182586, by rfl⟩ : syracuseStep 7790357 = 365173) (by norm_num)
theorem B1826669 : Blo 1136633 1826669 := bbase (se 3 (by rfl) ⟨342500, by rfl⟩ : syracuseStep 1826669 = 685001) (by norm_num)
theorem B4317077 : Blo 1136633 4317077 := bbase (se 6 (by rfl) ⟨101181, by rfl⟩ : syracuseStep 4317077 = 202363) (by norm_num)
theorem B1367965 : Blo 1136633 1367965 := bbase (se 3 (by rfl) ⟨256493, by rfl⟩ : syracuseStep 1367965 = 512987) (by norm_num)
theorem B1368157 : Blo 1136633 1368157 := bbase (se 3 (by rfl) ⟨256529, by rfl⟩ : syracuseStep 1368157 = 513059) (by norm_num)
theorem B1368257 : Blo 1136633 1368257 := bbase (se 2 (by rfl) ⟨513096, by rfl⟩ : syracuseStep 1368257 = 1026193) (by norm_num)
theorem B4153589 : Blo 1136633 4153589 := bbase (se 5 (by rfl) ⟨194699, by rfl⟩ : syracuseStep 4153589 = 389399) (by norm_num)
theorem B18702677 : Blo 1136633 18702677 := bbase (se 10 (by rfl) ⟨27396, by rfl⟩ : syracuseStep 18702677 = 54793) (by norm_num)
theorem B4154053 : Blo 1136633 4154053 := bbase (se 4 (by rfl) ⟨389442, by rfl⟩ : syracuseStep 4154053 = 778885) (by norm_num)
theorem B44360405 : Blo 1136633 44360405 := bbase (se 7 (by rfl) ⟨519848, by rfl⟩ : syracuseStep 44360405 = 1039697) (by norm_num)
theorem B5759909 : Blo 1136633 5759909 := bbase (se 4 (by rfl) ⟨539991, by rfl⟩ : syracuseStep 5759909 = 1079983) (by norm_num)
theorem B8643509 : Blo 1136633 8643509 := bbase (se 5 (by rfl) ⟨405164, by rfl⟩ : syracuseStep 8643509 = 810329) (by norm_num)
theorem B1369045 : Blo 1136633 1369045 := bbase (se 7 (by rfl) ⟨16043, by rfl⟩ : syracuseStep 1369045 = 32087) (by norm_num)
theorem B3237205 : Blo 1136633 3237205 := bbase (se 12 (by rfl) ⟨1185, by rfl⟩ : syracuseStep 3237205 = 2371) (by norm_num)
theorem B1369757 : Blo 1136633 1369757 := bbase (se 3 (by rfl) ⟨256829, by rfl⟩ : syracuseStep 1369757 = 513659) (by norm_num)
theorem B2877221 : Blo 1136633 2877221 := bbase (se 4 (by rfl) ⟨269739, by rfl⟩ : syracuseStep 2877221 = 539479) (by norm_num)
theorem B3073909 : Blo 1136633 3073909 := bbase (se 5 (by rfl) ⟨144089, by rfl⟩ : syracuseStep 3073909 = 288179) (by norm_num)
theorem B4319189 : Blo 1136633 4319189 := bbase (se 7 (by rfl) ⟨50615, by rfl⟩ : syracuseStep 4319189 = 101231) (by norm_num)
theorem B1370093 : Blo 1136633 1370093 := bbase (se 3 (by rfl) ⟨256892, by rfl⟩ : syracuseStep 1370093 = 513785) (by norm_num)
theorem B1730557 : Blo 1136633 1730557 := bbase (se 3 (by rfl) ⟨324479, by rfl⟩ : syracuseStep 1730557 = 648959) (by norm_num)
theorem B1370209 : Blo 1136633 1370209 := bbase (se 2 (by rfl) ⟨513828, by rfl⟩ : syracuseStep 1370209 = 1027657) (by norm_num)
theorem B1370233 : Blo 1136633 1370233 := bbase (se 2 (by rfl) ⟨513837, by rfl⟩ : syracuseStep 1370233 = 1027675) (by norm_num)
theorem B2877565 : Blo 1136633 2877565 := bbase (se 3 (by rfl) ⟨539543, by rfl⟩ : syracuseStep 2877565 = 1079087) (by norm_num)
theorem B1730717 : Blo 1136633 1730717 := bbase (se 3 (by rfl) ⟨324509, by rfl⟩ : syracuseStep 1730717 = 649019) (by norm_num)
theorem B5761205 : Blo 1136633 5761205 := bbase (se 5 (by rfl) ⟨270056, by rfl⟩ : syracuseStep 5761205 = 540113) (by norm_num)
theorem B2877677 : Blo 1136633 2877677 := bbase (se 3 (by rfl) ⟨539564, by rfl⟩ : syracuseStep 2877677 = 1079129) (by norm_num)
theorem B4319477 : Blo 1136633 4319477 := bbase (se 5 (by rfl) ⟨202475, by rfl⟩ : syracuseStep 4319477 = 404951) (by norm_num)
theorem B1403281 : Blo 1136633 1403281 := bbase (se 2 (by rfl) ⟨526230, by rfl⟩ : syracuseStep 1403281 = 1052461) (by norm_num)
theorem B3238309 : Blo 1136633 3238309 := bbase (se 4 (by rfl) ⟨303591, by rfl⟩ : syracuseStep 3238309 = 607183) (by norm_num)
theorem B2877869 : Blo 1136633 2877869 := bbase (se 3 (by rfl) ⟨539600, by rfl⟩ : syracuseStep 2877869 = 1079201) (by norm_num)
theorem B2190053 : Blo 1136633 2190053 := bbase (se 4 (by rfl) ⟨205317, by rfl⟩ : syracuseStep 2190053 = 410635) (by norm_num)
theorem B2878213 : Blo 1136633 2878213 := bbase (se 4 (by rfl) ⟨269832, by rfl⟩ : syracuseStep 2878213 = 539665) (by norm_num)
theorem B2878325 : Blo 1136633 2878325 := bbase (se 5 (by rfl) ⟨134921, by rfl⟩ : syracuseStep 2878325 = 269843) (by norm_num)
theorem B14576597 : Blo 1136633 14576597 := bbase (se 7 (by rfl) ⟨170819, by rfl⟩ : syracuseStep 14576597 = 341639) (by norm_num)
theorem B3075077 : Blo 1136633 3075077 := bbase (se 4 (by rfl) ⟨288288, by rfl⟩ : syracuseStep 3075077 = 576577) (by norm_num)
theorem B2878517 : Blo 1136633 2878517 := bbase (se 5 (by rfl) ⟨134930, by rfl⟩ : syracuseStep 2878517 = 269861) (by norm_num)
theorem B11103317 : Blo 1136633 11103317 := bbase (se 8 (by rfl) ⟨65058, by rfl⟩ : syracuseStep 11103317 = 130117) (by norm_num)
theorem B1731677 : Blo 1136633 1731677 := bbase (se 3 (by rfl) ⟨324689, by rfl⟩ : syracuseStep 1731677 = 649379) (by norm_num)
theorem B5467493 : Blo 1136633 5467493 := bbase (se 4 (by rfl) ⟨512577, by rfl⟩ : syracuseStep 5467493 = 1025155) (by norm_num)
theorem B2878861 : Blo 1136633 2878861 := bbase (se 3 (by rfl) ⟨539786, by rfl⟩ : syracuseStep 2878861 = 1079573) (by norm_num)
theorem B4320661 : Blo 1136633 4320661 := bbase (se 6 (by rfl) ⟨101265, by rfl⟩ : syracuseStep 4320661 = 202531) (by norm_num)
theorem B5762501 : Blo 1136633 5762501 := bbase (se 4 (by rfl) ⟨540234, by rfl⟩ : syracuseStep 5762501 = 1080469) (by norm_num)
theorem B2878973 : Blo 1136633 2878973 := bbase (se 3 (by rfl) ⟨539807, by rfl⟩ : syracuseStep 2878973 = 1079615) (by norm_num)
theorem B2879165 : Blo 1136633 2879165 := bbase (se 3 (by rfl) ⟨539843, by rfl⟩ : syracuseStep 2879165 = 1079687) (by norm_num)
theorem B4320965 : Blo 1136633 4320965 := bbase (se 4 (by rfl) ⟨405090, by rfl⟩ : syracuseStep 4320965 = 810181) (by norm_num)
theorem B5467877 : Blo 1136633 5467877 := bbase (se 4 (by rfl) ⟨512613, by rfl⟩ : syracuseStep 5467877 = 1025227) (by norm_num)
theorem B19459925 : Blo 1136633 19459925 := bbase (se 9 (by rfl) ⟨57011, by rfl⟩ : syracuseStep 19459925 = 114023) (by norm_num)
theorem B3239813 : Blo 1136633 3239813 := bbase (se 4 (by rfl) ⟨303732, by rfl⟩ : syracuseStep 3239813 = 607465) (by norm_num)
theorem B7303061 : Blo 1136633 7303061 := bbase (se 6 (by rfl) ⟨171165, by rfl⟩ : syracuseStep 7303061 = 342331) (by norm_num)
theorem B2158501 : Blo 1136633 2158501 := bbase (se 4 (by rfl) ⟨202359, by rfl⟩ : syracuseStep 2158501 = 404719) (by norm_num)
theorem B2879509 : Blo 1136633 2879509 := bbase (se 6 (by rfl) ⟨67488, by rfl⟩ : syracuseStep 2879509 = 134977) (by norm_num)
theorem B4157477 : Blo 1136633 4157477 := bbase (se 4 (by rfl) ⟨389763, by rfl⟩ : syracuseStep 4157477 = 779527) (by norm_num)
theorem B2158645 : Blo 1136633 2158645 := bbase (se 5 (by rfl) ⟨101186, by rfl⟩ : syracuseStep 2158645 = 202373) (by norm_num)
theorem B2879621 : Blo 1136633 2879621 := bbase (se 4 (by rfl) ⟨269964, by rfl⟩ : syracuseStep 2879621 = 539929) (by norm_num)
theorem B2158805 : Blo 1136633 2158805 := bbase (se 7 (by rfl) ⟨25298, by rfl⟩ : syracuseStep 2158805 = 50597) (by norm_num)
theorem B2879813 : Blo 1136633 2879813 := bbase (se 4 (by rfl) ⟨269982, by rfl⟩ : syracuseStep 2879813 = 539965) (by norm_num)
theorem B1536349 : Blo 1136633 1536349 := bbase (se 3 (by rfl) ⟨288065, by rfl⟩ : syracuseStep 1536349 = 576131) (by norm_num)
theorem B2158949 : Blo 1136633 2158949 := bbase (se 4 (by rfl) ⟨202401, by rfl⟩ : syracuseStep 2158949 = 404803) (by norm_num)
theorem B2159237 : Blo 1136633 2159237 := bbase (se 4 (by rfl) ⟨202428, by rfl⟩ : syracuseStep 2159237 = 404857) (by norm_num)
theorem B2880157 : Blo 1136633 2880157 := bbase (se 3 (by rfl) ⟨540029, by rfl⟩ : syracuseStep 2880157 = 1080059) (by norm_num)
theorem B5763797 : Blo 1136633 5763797 := bbase (se 7 (by rfl) ⟨67544, by rfl⟩ : syracuseStep 5763797 = 135089) (by norm_num)
theorem B2880269 : Blo 1136633 2880269 := bbase (se 3 (by rfl) ⟨540050, by rfl⟩ : syracuseStep 2880269 = 1080101) (by norm_num)
theorem B2159389 : Blo 1136633 2159389 := bbase (se 3 (by rfl) ⟨404885, by rfl⟩ : syracuseStep 2159389 = 809771) (by norm_num)
theorem B1438661 : Blo 1136633 1438661 := bbase (se 4 (by rfl) ⟨134874, by rfl⟩ : syracuseStep 1438661 = 269749) (by norm_num)
theorem B2880461 : Blo 1136633 2880461 := bbase (se 3 (by rfl) ⟨540086, by rfl⟩ : syracuseStep 2880461 = 1080173) (by norm_num)
theorem B1438717 : Blo 1136633 1438717 := bbase (se 3 (by rfl) ⟨269759, by rfl⟩ : syracuseStep 1438717 = 539519) (by norm_num)
theorem B2159693 : Blo 1136633 2159693 := bbase (se 3 (by rfl) ⟨404942, by rfl⟩ : syracuseStep 2159693 = 809885) (by norm_num)
theorem B6157397 : Blo 1136633 6157397 := bbase (se 8 (by rfl) ⟨36078, by rfl⟩ : syracuseStep 6157397 = 72157) (by norm_num)
theorem B1438813 : Blo 1136633 1438813 := bbase (se 3 (by rfl) ⟨269777, by rfl⟩ : syracuseStep 1438813 = 539555) (by norm_num)
theorem B1733813 : Blo 1136633 1733813 := bbase (se 5 (by rfl) ⟨81272, by rfl⟩ : syracuseStep 1733813 = 162545) (by norm_num)
theorem B16643285 : Blo 1136633 16643285 := bbase (se 7 (by rfl) ⟨195038, by rfl⟩ : syracuseStep 16643285 = 390077) (by norm_num)
theorem B1438985 : Blo 1136633 1438985 := bbase (se 2 (by rfl) ⟨539619, by rfl⟩ : syracuseStep 1438985 = 1079239) (by norm_num)
theorem B2880805 : Blo 1136633 2880805 := bbase (se 4 (by rfl) ⟨270075, by rfl⟩ : syracuseStep 2880805 = 540151) (by norm_num)
theorem B1439041 : Blo 1136633 1439041 := bbase (se 2 (by rfl) ⟨539640, by rfl⟩ : syracuseStep 1439041 = 1079281) (by norm_num)
theorem B2880917 : Blo 1136633 2880917 := bbase (se 6 (by rfl) ⟨67521, by rfl⟩ : syracuseStep 2880917 = 135043) (by norm_num)
theorem B1439137 : Blo 1136633 1439137 := bbase (se 2 (by rfl) ⟨539676, by rfl⟩ : syracuseStep 1439137 = 1079353) (by norm_num)
theorem B3241397 : Blo 1136633 3241397 := bbase (se 5 (by rfl) ⟨151940, by rfl⟩ : syracuseStep 3241397 = 303881) (by norm_num)
theorem B4388357 : Blo 1136633 4388357 := bbase (se 4 (by rfl) ⟨411408, by rfl⟩ : syracuseStep 4388357 = 822817) (by norm_num)
theorem B7796245 : Blo 1136633 7796245 := bbase (se 6 (by rfl) ⟨182724, by rfl⟩ : syracuseStep 7796245 = 365449) (by norm_num)
theorem B1439309 : Blo 1136633 1439309 := bbase (se 3 (by rfl) ⟨269870, by rfl⟩ : syracuseStep 1439309 = 539741) (by norm_num)
theorem B2881109 : Blo 1136633 2881109 := bbase (se 8 (by rfl) ⟨16881, by rfl⟩ : syracuseStep 2881109 = 33763) (by norm_num)
theorem B1439365 : Blo 1136633 1439365 := bbase (se 4 (by rfl) ⟨134940, by rfl⟩ : syracuseStep 1439365 = 269881) (by norm_num)
theorem B1439461 : Blo 1136633 1439461 := bbase (se 4 (by rfl) ⟨134949, by rfl⟩ : syracuseStep 1439461 = 269899) (by norm_num)
theorem B4323077 : Blo 1136633 4323077 := bbase (se 4 (by rfl) ⟨405288, by rfl⟩ : syracuseStep 4323077 = 810577) (by norm_num)
theorem B2160445 : Blo 1136633 2160445 := bbase (se 3 (by rfl) ⟨405083, by rfl⟩ : syracuseStep 2160445 = 810167) (by norm_num)
theorem B1439633 : Blo 1136633 1439633 := bbase (se 2 (by rfl) ⟨539862, by rfl⟩ : syracuseStep 1439633 = 1079725) (by norm_num)
theorem B2881453 : Blo 1136633 2881453 := bbase (se 3 (by rfl) ⟨540272, by rfl⟩ : syracuseStep 2881453 = 1080545) (by norm_num)
theorem B1439689 : Blo 1136633 1439689 := bbase (se 2 (by rfl) ⟨539883, by rfl⟩ : syracuseStep 1439689 = 1079767) (by norm_num)
theorem B2160589 : Blo 1136633 2160589 := bbase (se 3 (by rfl) ⟨405110, by rfl⟩ : syracuseStep 2160589 = 810221) (by norm_num)
theorem B5765093 : Blo 1136633 5765093 := bbase (se 4 (by rfl) ⟨540477, by rfl⟩ : syracuseStep 5765093 = 1080955) (by norm_num)
theorem B2881565 : Blo 1136633 2881565 := bbase (se 3 (by rfl) ⟨540293, by rfl⟩ : syracuseStep 2881565 = 1080587) (by norm_num)
theorem B4323365 : Blo 1136633 4323365 := bbase (se 4 (by rfl) ⟨405315, by rfl⟩ : syracuseStep 4323365 = 810631) (by norm_num)
theorem B1439785 : Blo 1136633 1439785 := bbase (se 2 (by rfl) ⟨539919, by rfl⟩ : syracuseStep 1439785 = 1079839) (by norm_num)
theorem B3242069 : Blo 1136633 3242069 := bbase (se 8 (by rfl) ⟨18996, by rfl⟩ : syracuseStep 3242069 = 37993) (by norm_num)
theorem B2160749 : Blo 1136633 2160749 := bbase (se 3 (by rfl) ⟨405140, by rfl⟩ : syracuseStep 2160749 = 810281) (by norm_num)
theorem B1439957 : Blo 1136633 1439957 := bbase (se 7 (by rfl) ⟨16874, by rfl⟩ : syracuseStep 1439957 = 33749) (by norm_num)
theorem B2881757 : Blo 1136633 2881757 := bbase (se 3 (by rfl) ⟨540329, by rfl⟩ : syracuseStep 2881757 = 1080659) (by norm_num)
theorem B2160893 : Blo 1136633 2160893 := bbase (se 3 (by rfl) ⟨405167, by rfl⟩ : syracuseStep 2160893 = 810335) (by norm_num)
theorem B1440013 : Blo 1136633 1440013 := bbase (se 3 (by rfl) ⟨270002, by rfl⟩ : syracuseStep 1440013 = 540005) (by norm_num)
theorem B2193685 : Blo 1136633 2193685 := bbase (se 6 (by rfl) ⟨51414, by rfl⟩ : syracuseStep 2193685 = 102829) (by norm_num)
theorem B1440109 : Blo 1136633 1440109 := bbase (se 3 (by rfl) ⟨270020, by rfl⟩ : syracuseStep 1440109 = 540041) (by norm_num)
theorem B3242501 : Blo 1136633 3242501 := bbase (se 4 (by rfl) ⟨303984, by rfl⟩ : syracuseStep 3242501 = 607969) (by norm_num)
theorem B1440281 : Blo 1136633 1440281 := bbase (se 2 (by rfl) ⟨540105, by rfl⟩ : syracuseStep 1440281 = 1080211) (by norm_num)
theorem B2161181 : Blo 1136633 2161181 := bbase (se 3 (by rfl) ⟨405221, by rfl⟩ : syracuseStep 2161181 = 810443) (by norm_num)
theorem B2882101 : Blo 1136633 2882101 := bbase (se 5 (by rfl) ⟨135098, by rfl⟩ : syracuseStep 2882101 = 270197) (by norm_num)
theorem B1440337 : Blo 1136633 1440337 := bbase (se 2 (by rfl) ⟨540126, by rfl⟩ : syracuseStep 1440337 = 1080253) (by norm_num)
theorem B12974741 : Blo 1136633 12974741 := bbase (se 6 (by rfl) ⟨304095, by rfl⟩ : syracuseStep 12974741 = 608191) (by norm_num)
theorem B2882213 : Blo 1136633 2882213 := bbase (se 4 (by rfl) ⟨270207, by rfl⟩ : syracuseStep 2882213 = 540415) (by norm_num)
theorem B1440433 : Blo 1136633 1440433 := bbase (se 2 (by rfl) ⟨540162, by rfl⟩ : syracuseStep 1440433 = 1080325) (by norm_num)
theorem B2161333 : Blo 1136633 2161333 := bbase (se 5 (by rfl) ⟨101312, by rfl⟩ : syracuseStep 2161333 = 202625) (by norm_num)
theorem B1440605 : Blo 1136633 1440605 := bbase (se 3 (by rfl) ⟨270113, by rfl⟩ : syracuseStep 1440605 = 540227) (by norm_num)
theorem B2882405 : Blo 1136633 2882405 := bbase (se 4 (by rfl) ⟨270225, by rfl⟩ : syracuseStep 2882405 = 540451) (by norm_num)
theorem B1440661 : Blo 1136633 1440661 := bbase (se 6 (by rfl) ⟨33765, by rfl⟩ : syracuseStep 1440661 = 67531) (by norm_num)
theorem B2161637 : Blo 1136633 2161637 := bbase (se 4 (by rfl) ⟨202653, by rfl⟩ : syracuseStep 2161637 = 405307) (by norm_num)
theorem B1440757 : Blo 1136633 1440757 := bbase (se 5 (by rfl) ⟨67535, by rfl⟩ : syracuseStep 1440757 = 135071) (by norm_num)
theorem B1539181 : Blo 1136633 1539181 := bbase (se 3 (by rfl) ⟨288596, by rfl⟩ : syracuseStep 1539181 = 577193) (by norm_num)
theorem B1440929 : Blo 1136633 1440929 := bbase (se 2 (by rfl) ⟨540348, by rfl⟩ : syracuseStep 1440929 = 1080697) (by norm_num)
theorem B2882749 : Blo 1136633 2882749 := bbase (se 3 (by rfl) ⟨540515, by rfl⟩ : syracuseStep 2882749 = 1081031) (by norm_num)
theorem B4324549 : Blo 1136633 4324549 := bbase (se 4 (by rfl) ⟨405426, by rfl⟩ : syracuseStep 4324549 = 810853) (by norm_num)
theorem B1440985 : Blo 1136633 1440985 := bbase (se 2 (by rfl) ⟨540369, by rfl⟩ : syracuseStep 1440985 = 1080739) (by norm_num)
theorem B3243253 : Blo 1136633 3243253 := bbase (se 5 (by rfl) ⟨152027, by rfl⟩ : syracuseStep 3243253 = 304055) (by norm_num)
theorem B5766389 : Blo 1136633 5766389 := bbase (se 5 (by rfl) ⟨270299, by rfl⟩ : syracuseStep 5766389 = 540599) (by norm_num)
theorem B12320021 : Blo 1136633 12320021 := bbase (se 6 (by rfl) ⟨288750, by rfl⟩ : syracuseStep 12320021 = 577501) (by norm_num)
theorem B2882861 : Blo 1136633 2882861 := bbase (se 3 (by rfl) ⟨540536, by rfl⟩ : syracuseStep 2882861 = 1081073) (by norm_num)
theorem B1441081 : Blo 1136633 1441081 := bbase (se 2 (by rfl) ⟨540405, by rfl⟩ : syracuseStep 1441081 = 1080811) (by norm_num)
theorem B4619605 : Blo 1136633 4619605 := bbase (se 11 (by rfl) ⟨3383, by rfl⟩ : syracuseStep 4619605 = 6767) (by norm_num)
theorem B1441253 : Blo 1136633 1441253 := bbase (se 4 (by rfl) ⟨135117, by rfl⟩ : syracuseStep 1441253 = 270235) (by norm_num)
theorem B4619749 : Blo 1136633 4619749 := bbase (se 4 (by rfl) ⟨433101, by rfl⟩ : syracuseStep 4619749 = 866203) (by norm_num)
theorem B2883053 : Blo 1136633 2883053 := bbase (se 3 (by rfl) ⟨540572, by rfl⟩ : syracuseStep 2883053 = 1081145) (by norm_num)
theorem B4324853 : Blo 1136633 4324853 := bbase (se 5 (by rfl) ⟨202727, by rfl⟩ : syracuseStep 4324853 = 405455) (by norm_num)
theorem B1441309 : Blo 1136633 1441309 := bbase (se 3 (by rfl) ⟨270245, by rfl⟩ : syracuseStep 1441309 = 540491) (by norm_num)
theorem B6159925 : Blo 1136633 6159925 := bbase (se 5 (by rfl) ⟨288746, by rfl⟩ : syracuseStep 6159925 = 577493) (by norm_num)
theorem B1441405 : Blo 1136633 1441405 := bbase (se 3 (by rfl) ⟨270263, by rfl⟩ : syracuseStep 1441405 = 540527) (by norm_num)
theorem B2162389 : Blo 1136633 2162389 := bbase (se 7 (by rfl) ⟨25340, by rfl⟩ : syracuseStep 2162389 = 50681) (by norm_num)
theorem B1441577 : Blo 1136633 1441577 := bbase (se 2 (by rfl) ⟨540591, by rfl⟩ : syracuseStep 1441577 = 1081183) (by norm_num)
theorem B2883397 : Blo 1136633 2883397 := bbase (se 4 (by rfl) ⟨270318, by rfl⟩ : syracuseStep 2883397 = 540637) (by norm_num)
theorem B1441633 : Blo 1136633 1441633 := bbase (se 2 (by rfl) ⟨540612, by rfl⟩ : syracuseStep 1441633 = 1081225) (by norm_num)
theorem B2162533 : Blo 1136633 2162533 := bbase (se 4 (by rfl) ⟨202737, by rfl⟩ : syracuseStep 2162533 = 405475) (by norm_num)
theorem B3800981 : Blo 1136633 3800981 := bbase (se 6 (by rfl) ⟨89085, by rfl⟩ : syracuseStep 3800981 = 178171) (by norm_num)
theorem B2883509 : Blo 1136633 2883509 := bbase (se 5 (by rfl) ⟨135164, by rfl⟩ : syracuseStep 2883509 = 270329) (by norm_num)
theorem B1441729 : Blo 1136633 1441729 := bbase (se 2 (by rfl) ⟨540648, by rfl⟩ : syracuseStep 1441729 = 1081297) (by norm_num)
theorem B1441795 : Blo 1136633 1441795 := bstep (se 1 (by rfl) ⟨1081346, by rfl⟩ : syracuseStep 1441795 = 2162693) B2162693
theorem B1540129 : Blo 1136633 1540129 := bstep (se 2 (by rfl) ⟨577548, by rfl⟩ : syracuseStep 1540129 = 1155097) B1155097
theorem B1441891 : Blo 1136633 1441891 := bstep (se 1 (by rfl) ⟨1081418, by rfl⟩ : syracuseStep 1441891 = 2162837) B2162837
theorem B14614627 : Blo 1136633 14614627 := bstep (se 1 (by rfl) ⟨10960970, by rfl⟩ : syracuseStep 14614627 = 21921941) B21921941
theorem B3244141 : Blo 1136633 3244141 := bstep (se 3 (by rfl) ⟨608276, by rfl⟩ : syracuseStep 3244141 = 1216553) B1216553
theorem B6488261 : Blo 1136633 6488261 := bstep (se 4 (by rfl) ⟨608274, by rfl⟩ : syracuseStep 6488261 = 1216549) B1216549
theorem B3244369 : Blo 1136633 3244369 := bstep (se 2 (by rfl) ⟨1216638, by rfl⟩ : syracuseStep 3244369 = 2433277) B2433277
theorem B5767523 : Blo 1136633 5767523 := bstep (se 1 (by rfl) ⟨4325642, by rfl⟩ : syracuseStep 5767523 = 8651285) B8651285
theorem B4325795 : Blo 1136633 4325795 := bstep (se 1 (by rfl) ⟨3244346, by rfl⟩ : syracuseStep 4325795 = 6488693) B6488693
theorem B1540561 : Blo 1136633 1540561 := bstep (se 2 (by rfl) ⟨577710, by rfl⟩ : syracuseStep 1540561 = 1155421) B1155421
theorem B3244529 : Blo 1136633 3244529 := bstep (se 2 (by rfl) ⟨1216698, by rfl⟩ : syracuseStep 3244529 = 2433397) B2433397
theorem B1442387 : Blo 1136633 1442387 := bstep (se 1 (by rfl) ⟨1081790, by rfl⟩ : syracuseStep 1442387 = 2163581) B2163581
theorem B3244643 : Blo 1136633 3244643 := bstep (se 1 (by rfl) ⟨2433482, by rfl⟩ : syracuseStep 3244643 = 4866965) B4866965
theorem B2884369 : Blo 1136633 2884369 := bstep (se 2 (by rfl) ⟨1081638, by rfl⟩ : syracuseStep 2884369 = 2163277) B2163277
theorem B2163505 : Blo 1136633 2163505 := bstep (se 2 (by rfl) ⟨811314, by rfl⟩ : syracuseStep 2163505 = 1622629) B1622629
theorem B1278787 : Blo 1136633 1278787 := bstep (se 1 (by rfl) ⟨959090, by rfl⟩ : syracuseStep 1278787 = 1918181) B1918181
theorem B3900241 : Blo 1136633 3900241 := bstep (se 2 (by rfl) ⟨1462590, by rfl⟩ : syracuseStep 3900241 = 2925181) B2925181
theorem B49873805 : Blo 1136633 49873805 := bstep (se 3 (by rfl) ⟨9351338, by rfl⟩ : syracuseStep 49873805 = 18702677) B18702677
theorem B5538737 : Blo 1136633 5538737 := bstep (se 2 (by rfl) ⟨2077026, by rfl⟩ : syracuseStep 5538737 = 4154053) B4154053
theorem B2163665 : Blo 1136633 2163665 := bstep (se 2 (by rfl) ⟨811374, by rfl⟩ : syracuseStep 2163665 = 1622749) B1622749
theorem B1278931 : Blo 1136633 1278931 := bstep (se 1 (by rfl) ⟨959198, by rfl⟩ : syracuseStep 1278931 = 1918397) B1918397
theorem B1704977 : Blo 1136633 1704977 := bstep (se 2 (by rfl) ⟨639366, by rfl⟩ : syracuseStep 1704977 = 1278733) B1278733
theorem B1704995 : Blo 1136633 1704995 := bstep (se 1 (by rfl) ⟨1278746, by rfl⟩ : syracuseStep 1704995 = 2557493) B2557493
theorem B2884643 : Blo 1136633 2884643 := bstep (se 1 (by rfl) ⟨2163482, by rfl⟩ : syracuseStep 2884643 = 4326965) B4326965
theorem B1705025 : Blo 1136633 1705025 := bstep (se 2 (by rfl) ⟨639384, by rfl⟩ : syracuseStep 1705025 = 1278769) B1278769
theorem B5538893 : Blo 1136633 5538893 := bstep (se 3 (by rfl) ⟨1038542, by rfl⟩ : syracuseStep 5538893 = 2077085) B2077085
theorem B1705043 : Blo 1136633 1705043 := bstep (se 1 (by rfl) ⟨1278782, by rfl⟩ : syracuseStep 1705043 = 2557565) B2557565
theorem B1279075 : Blo 1136633 1279075 := bstep (se 1 (by rfl) ⟨959306, by rfl⟩ : syracuseStep 1279075 = 1918613) B1918613
theorem B1705073 : Blo 1136633 1705073 := bstep (se 2 (by rfl) ⟨639402, by rfl⟩ : syracuseStep 1705073 = 1278805) B1278805
theorem B1705091 : Blo 1136633 1705091 := bstep (se 1 (by rfl) ⟨1278818, by rfl⟩ : syracuseStep 1705091 = 2557637) B2557637
theorem B5768333 : Blo 1136633 5768333 := bstep (se 3 (by rfl) ⟨1081562, by rfl⟩ : syracuseStep 5768333 = 2163125) B2163125
theorem B1705121 : Blo 1136633 1705121 := bstep (se 2 (by rfl) ⟨639420, by rfl⟩ : syracuseStep 1705121 = 1278841) B1278841
theorem B1705139 : Blo 1136633 1705139 := bstep (se 1 (by rfl) ⟨1278854, by rfl⟩ : syracuseStep 1705139 = 2557709) B2557709
theorem B1705169 : Blo 1136633 1705169 := bstep (se 2 (by rfl) ⟨639438, by rfl⟩ : syracuseStep 1705169 = 1278877) B1278877
theorem B1705187 : Blo 1136633 1705187 := bstep (se 1 (by rfl) ⟨1278890, by rfl⟩ : syracuseStep 1705187 = 2557781) B2557781
theorem B2884835 : Blo 1136633 2884835 := bstep (se 1 (by rfl) ⟨2163626, by rfl⟩ : syracuseStep 2884835 = 4327253) B4327253
theorem B1279219 : Blo 1136633 1279219 := bstep (se 1 (by rfl) ⟨959414, by rfl⟩ : syracuseStep 1279219 = 1918829) B1918829
theorem B1705217 : Blo 1136633 1705217 := bstep (se 2 (by rfl) ⟨639456, by rfl⟩ : syracuseStep 1705217 = 1278913) B1278913
theorem B1705235 : Blo 1136633 1705235 := bstep (se 1 (by rfl) ⟨1278926, by rfl⟩ : syracuseStep 1705235 = 2557853) B2557853
theorem B1443091 : Blo 1136633 1443091 := bstep (se 1 (by rfl) ⟨1082318, by rfl⟩ : syracuseStep 1443091 = 2164637) B2164637
theorem B1705265 : Blo 1136633 1705265 := bstep (se 2 (by rfl) ⟨639474, by rfl⟩ : syracuseStep 1705265 = 1278949) B1278949
theorem B1705283 : Blo 1136633 1705283 := bstep (se 1 (by rfl) ⟨1278962, by rfl⟩ : syracuseStep 1705283 = 2557925) B2557925
theorem B1705313 : Blo 1136633 1705313 := bstep (se 2 (by rfl) ⟨639492, by rfl⟩ : syracuseStep 1705313 = 1278985) B1278985
theorem B2164067 : Blo 1136633 2164067 := bstep (se 1 (by rfl) ⟨1623050, by rfl⟩ : syracuseStep 2164067 = 3246101) B3246101
theorem B1705331 : Blo 1136633 1705331 := bstep (se 1 (by rfl) ⟨1278998, by rfl⟩ : syracuseStep 1705331 = 2557997) B2557997
theorem B1443187 : Blo 1136633 1443187 := bstep (se 1 (by rfl) ⟨1082390, by rfl⟩ : syracuseStep 1443187 = 2164781) B2164781
theorem B1279363 : Blo 1136633 1279363 := bstep (se 1 (by rfl) ⟨959522, by rfl⟩ : syracuseStep 1279363 = 1919045) B1919045
theorem B9733517 : Blo 1136633 9733517 := bstep (se 3 (by rfl) ⟨1825034, by rfl⟩ : syracuseStep 9733517 = 3650069) B3650069
theorem B4326797 : Blo 1136633 4326797 := bstep (se 3 (by rfl) ⟨811274, by rfl⟩ : syracuseStep 4326797 = 1622549) B1622549
theorem B1705361 : Blo 1136633 1705361 := bstep (se 2 (by rfl) ⟨639510, by rfl⟩ : syracuseStep 1705361 = 1279021) B1279021
theorem B1705379 : Blo 1136633 1705379 := bstep (se 1 (by rfl) ⟨1279034, by rfl⟩ : syracuseStep 1705379 = 2558069) B2558069
theorem B1541539 : Blo 1136633 1541539 := bstep (se 1 (by rfl) ⟨1156154, by rfl⟩ : syracuseStep 1541539 = 2312309) B2312309
theorem B1705409 : Blo 1136633 1705409 := bstep (se 2 (by rfl) ⟨639528, by rfl⟩ : syracuseStep 1705409 = 1279057) B1279057
theorem B11699653 : Blo 1136633 11699653 := bstep (se 4 (by rfl) ⟨1096842, by rfl⟩ : syracuseStep 11699653 = 2193685) B2193685
theorem B1705427 : Blo 1136633 1705427 := bstep (se 1 (by rfl) ⟨1279070, by rfl⟩ : syracuseStep 1705427 = 2558141) B2558141
theorem B1705457 : Blo 1136633 1705457 := bstep (se 2 (by rfl) ⟨639546, by rfl⟩ : syracuseStep 1705457 = 1279093) B1279093
theorem B1705475 : Blo 1136633 1705475 := bstep (se 1 (by rfl) ⟨1279106, by rfl⟩ : syracuseStep 1705475 = 2558213) B2558213
theorem B2557457 : Blo 1136633 2557457 := bstep (se 2 (by rfl) ⟨959046, by rfl⟩ : syracuseStep 2557457 = 1918093) B1918093
theorem B1279507 : Blo 1136633 1279507 := bstep (se 1 (by rfl) ⟨959630, by rfl⟩ : syracuseStep 1279507 = 1919261) B1919261
theorem B1705505 : Blo 1136633 1705505 := bstep (se 2 (by rfl) ⟨639564, by rfl⟩ : syracuseStep 1705505 = 1279129) B1279129
theorem B2557475 : Blo 1136633 2557475 := bstep (se 1 (by rfl) ⟨1918106, by rfl⟩ : syracuseStep 2557475 = 3836213) B3836213
theorem B1705523 : Blo 1136633 1705523 := bstep (se 1 (by rfl) ⟨1279142, by rfl⟩ : syracuseStep 1705523 = 2558285) B2558285
theorem B3245645 : Blo 1136633 3245645 := bstep (se 3 (by rfl) ⟨608558, by rfl⟩ : syracuseStep 3245645 = 1217117) B1217117
theorem B1705553 : Blo 1136633 1705553 := bstep (se 2 (by rfl) ⟨639582, by rfl⟩ : syracuseStep 1705553 = 1279165) B1279165
theorem B1705571 : Blo 1136633 1705571 := bstep (se 1 (by rfl) ⟨1279178, by rfl⟩ : syracuseStep 1705571 = 2558357) B2558357
theorem B1705601 : Blo 1136633 1705601 := bstep (se 2 (by rfl) ⟨639600, by rfl⟩ : syracuseStep 1705601 = 1279201) B1279201
theorem B1705619 : Blo 1136633 1705619 := bstep (se 1 (by rfl) ⟨1279214, by rfl⟩ : syracuseStep 1705619 = 2558429) B2558429
theorem B1279651 : Blo 1136633 1279651 := bstep (se 1 (by rfl) ⟨959738, by rfl⟩ : syracuseStep 1279651 = 1919477) B1919477
theorem B1705649 : Blo 1136633 1705649 := bstep (se 2 (by rfl) ⟨639618, by rfl⟩ : syracuseStep 1705649 = 1279237) B1279237
theorem B1705667 : Blo 1136633 1705667 := bstep (se 1 (by rfl) ⟨1279250, by rfl⟩ : syracuseStep 1705667 = 2558501) B2558501
theorem B1705697 : Blo 1136633 1705697 := bstep (se 2 (by rfl) ⟨639636, by rfl⟩ : syracuseStep 1705697 = 1279273) B1279273
theorem B9242353 : Blo 1136633 9242353 := bstep (se 2 (by rfl) ⟨3465882, by rfl⟩ : syracuseStep 9242353 = 6931765) B6931765
theorem B1214195 : Blo 1136633 1214195 := bstep (se 1 (by rfl) ⟨910646, by rfl⟩ : syracuseStep 1214195 = 1821293) B1821293
theorem B1705715 : Blo 1136633 1705715 := bstep (se 1 (by rfl) ⟨1279286, by rfl⟩ : syracuseStep 1705715 = 2558573) B2558573
theorem B3245827 : Blo 1136633 3245827 := bstep (se 1 (by rfl) ⟨2434370, by rfl⟩ : syracuseStep 3245827 = 4868741) B4868741
theorem B1705745 : Blo 1136633 1705745 := bstep (se 2 (by rfl) ⟨639654, by rfl⟩ : syracuseStep 1705745 = 1279309) B1279309
theorem B1705763 : Blo 1136633 1705763 := bstep (se 1 (by rfl) ⟨1279322, by rfl⟩ : syracuseStep 1705763 = 2558645) B2558645
theorem B2557745 : Blo 1136633 2557745 := bstep (se 2 (by rfl) ⟨959154, by rfl⟩ : syracuseStep 2557745 = 1918309) B1918309
theorem B1279795 : Blo 1136633 1279795 := bstep (se 1 (by rfl) ⟨959846, by rfl⟩ : syracuseStep 1279795 = 1919693) B1919693
theorem B1705793 : Blo 1136633 1705793 := bstep (se 2 (by rfl) ⟨639672, by rfl⟩ : syracuseStep 1705793 = 1279345) B1279345
theorem B2557763 : Blo 1136633 2557763 := bstep (se 1 (by rfl) ⟨1918322, by rfl⟩ : syracuseStep 2557763 = 3836645) B3836645
theorem B1705811 : Blo 1136633 1705811 := bstep (se 1 (by rfl) ⟨1279358, by rfl⟩ : syracuseStep 1705811 = 2558717) B2558717
theorem B1705841 : Blo 1136633 1705841 := bstep (se 2 (by rfl) ⟨639690, by rfl⟩ : syracuseStep 1705841 = 1279381) B1279381
theorem B1705859 : Blo 1136633 1705859 := bstep (se 1 (by rfl) ⟨1279394, by rfl⟩ : syracuseStep 1705859 = 2558789) B2558789
theorem B1705889 : Blo 1136633 1705889 := bstep (se 2 (by rfl) ⟨639708, by rfl⟩ : syracuseStep 1705889 = 1279417) B1279417
theorem B3245987 : Blo 1136633 3245987 := bstep (se 1 (by rfl) ⟨2434490, by rfl⟩ : syracuseStep 3245987 = 4868981) B4868981
theorem B1705907 : Blo 1136633 1705907 := bstep (se 1 (by rfl) ⟨1279430, by rfl⟩ : syracuseStep 1705907 = 2558861) B2558861
theorem B2918339 : Blo 1136633 2918339 := bstep (se 1 (by rfl) ⟨2188754, by rfl⟩ : syracuseStep 2918339 = 4377509) B4377509
theorem B1279939 : Blo 1136633 1279939 := bstep (se 1 (by rfl) ⟨959954, by rfl⟩ : syracuseStep 1279939 = 1919909) B1919909
theorem B1705937 : Blo 1136633 1705937 := bstep (se 2 (by rfl) ⟨639726, by rfl⟩ : syracuseStep 1705937 = 1279453) B1279453
theorem B1705955 : Blo 1136633 1705955 := bstep (se 1 (by rfl) ⟨1279466, by rfl⟩ : syracuseStep 1705955 = 2558933) B2558933
theorem B1705985 : Blo 1136633 1705985 := bstep (se 2 (by rfl) ⟨639744, by rfl⟩ : syracuseStep 1705985 = 1279489) B1279489
theorem B1706003 : Blo 1136633 1706003 := bstep (se 1 (by rfl) ⟨1279502, by rfl⟩ : syracuseStep 1706003 = 2559005) B2559005
theorem B1706033 : Blo 1136633 1706033 := bstep (se 2 (by rfl) ⟨639762, by rfl⟩ : syracuseStep 1706033 = 1279525) B1279525
theorem B1706051 : Blo 1136633 1706051 := bstep (se 1 (by rfl) ⟨1279538, by rfl⟩ : syracuseStep 1706051 = 2559077) B2559077
theorem B2558033 : Blo 1136633 2558033 := bstep (se 2 (by rfl) ⟨959262, by rfl⟩ : syracuseStep 2558033 = 1918525) B1918525
theorem B1280083 : Blo 1136633 1280083 := bstep (se 1 (by rfl) ⟨960062, by rfl⟩ : syracuseStep 1280083 = 1920125) B1920125
theorem B1706081 : Blo 1136633 1706081 := bstep (se 2 (by rfl) ⟨639780, by rfl⟩ : syracuseStep 1706081 = 1279561) B1279561
theorem B2558051 : Blo 1136633 2558051 := bstep (se 1 (by rfl) ⟨1918538, by rfl⟩ : syracuseStep 2558051 = 3837077) B3837077
theorem B1706099 : Blo 1136633 1706099 := bstep (se 1 (by rfl) ⟨1279574, by rfl⟩ : syracuseStep 1706099 = 2559149) B2559149
theorem B1706129 : Blo 1136633 1706129 := bstep (se 2 (by rfl) ⟨639798, by rfl⟩ : syracuseStep 1706129 = 1279597) B1279597
theorem B2885777 : Blo 1136633 2885777 := bstep (se 2 (by rfl) ⟨1082166, by rfl⟩ : syracuseStep 2885777 = 2164333) B2164333
theorem B1706147 : Blo 1136633 1706147 := bstep (se 1 (by rfl) ⟨1279610, by rfl⟩ : syracuseStep 1706147 = 2559221) B2559221
theorem B1706177 : Blo 1136633 1706177 := bstep (se 2 (by rfl) ⟨639816, by rfl⟩ : syracuseStep 1706177 = 1279633) B1279633
theorem B2885827 : Blo 1136633 2885827 := bstep (se 1 (by rfl) ⟨2164370, by rfl⟩ : syracuseStep 2885827 = 4328741) B4328741
theorem B1706195 : Blo 1136633 1706195 := bstep (se 1 (by rfl) ⟨1279646, by rfl⟩ : syracuseStep 1706195 = 2559293) B2559293
theorem B1280227 : Blo 1136633 1280227 := bstep (se 1 (by rfl) ⟨960170, by rfl⟩ : syracuseStep 1280227 = 1920341) B1920341
theorem B2164963 : Blo 1136633 2164963 := bstep (se 1 (by rfl) ⟨1623722, by rfl⟩ : syracuseStep 2164963 = 3247445) B3247445
theorem B1706225 : Blo 1136633 1706225 := bstep (se 2 (by rfl) ⟨639834, by rfl⟩ : syracuseStep 1706225 = 1279669) B1279669
theorem B1706243 : Blo 1136633 1706243 := bstep (se 1 (by rfl) ⟨1279682, by rfl⟩ : syracuseStep 1706243 = 2559365) B2559365
theorem B1706273 : Blo 1136633 1706273 := bstep (se 2 (by rfl) ⟨639852, by rfl⟩ : syracuseStep 1706273 = 1279705) B1279705
theorem B1706291 : Blo 1136633 1706291 := bstep (se 1 (by rfl) ⟨1279718, by rfl⟩ : syracuseStep 1706291 = 2559437) B2559437
theorem B1706321 : Blo 1136633 1706321 := bstep (se 2 (by rfl) ⟨639870, by rfl⟩ : syracuseStep 1706321 = 1279741) B1279741
theorem B2885969 : Blo 1136633 2885969 := bstep (se 2 (by rfl) ⟨1082238, by rfl⟩ : syracuseStep 2885969 = 2164477) B2164477
theorem B1706339 : Blo 1136633 1706339 := bstep (se 1 (by rfl) ⟨1279754, by rfl⟩ : syracuseStep 1706339 = 2559509) B2559509
theorem B2558321 : Blo 1136633 2558321 := bstep (se 2 (by rfl) ⟨959370, by rfl⟩ : syracuseStep 2558321 = 1918741) B1918741
theorem B1280371 : Blo 1136633 1280371 := bstep (se 1 (by rfl) ⟨960278, by rfl⟩ : syracuseStep 1280371 = 1920557) B1920557
theorem B1706369 : Blo 1136633 1706369 := bstep (se 2 (by rfl) ⟨639888, by rfl⟩ : syracuseStep 1706369 = 1279777) B1279777
theorem B2558339 : Blo 1136633 2558339 := bstep (se 1 (by rfl) ⟨1918754, by rfl⟩ : syracuseStep 2558339 = 3837509) B3837509
theorem B2165123 : Blo 1136633 2165123 := bstep (se 1 (by rfl) ⟨1623842, by rfl⟩ : syracuseStep 2165123 = 3247685) B3247685
theorem B1706387 : Blo 1136633 1706387 := bstep (se 1 (by rfl) ⟨1279790, by rfl⟩ : syracuseStep 1706387 = 2559581) B2559581
theorem B1706417 : Blo 1136633 1706417 := bstep (se 2 (by rfl) ⟨639906, by rfl⟩ : syracuseStep 1706417 = 1279813) B1279813
theorem B1706435 : Blo 1136633 1706435 := bstep (se 1 (by rfl) ⟨1279826, by rfl⟩ : syracuseStep 1706435 = 2559653) B2559653
theorem B1706465 : Blo 1136633 1706465 := bstep (se 2 (by rfl) ⟨639924, by rfl⟩ : syracuseStep 1706465 = 1279849) B1279849
theorem B1214947 : Blo 1136633 1214947 := bstep (se 1 (by rfl) ⟨911210, by rfl⟩ : syracuseStep 1214947 = 1822421) B1822421
theorem B4098545 : Blo 1136633 4098545 := bstep (se 2 (by rfl) ⟨1536954, by rfl⟩ : syracuseStep 4098545 = 3073909) B3073909
theorem B1706483 : Blo 1136633 1706483 := bstep (se 1 (by rfl) ⟨1279862, by rfl⟩ : syracuseStep 1706483 = 2559725) B2559725
theorem B1280515 : Blo 1136633 1280515 := bstep (se 1 (by rfl) ⟨960386, by rfl⟩ : syracuseStep 1280515 = 1920773) B1920773
theorem B3836429 : Blo 1136633 3836429 := bstep (se 3 (by rfl) ⟨719330, by rfl⟩ : syracuseStep 3836429 = 1438661) B1438661
theorem B1706513 : Blo 1136633 1706513 := bstep (se 2 (by rfl) ⟨639942, by rfl⟩ : syracuseStep 1706513 = 1279885) B1279885
theorem B1706531 : Blo 1136633 1706531 := bstep (se 1 (by rfl) ⟨1279898, by rfl⟩ : syracuseStep 1706531 = 2559797) B2559797
theorem B1706561 : Blo 1136633 1706561 := bstep (se 2 (by rfl) ⟨639960, by rfl⟩ : syracuseStep 1706561 = 1279921) B1279921
theorem B3836483 : Blo 1136633 3836483 := bstep (se 1 (by rfl) ⟨2877362, by rfl⟩ : syracuseStep 3836483 = 5754725) B5754725
theorem B1706579 : Blo 1136633 1706579 := bstep (se 1 (by rfl) ⟨1279934, by rfl⟩ : syracuseStep 1706579 = 2559869) B2559869
theorem B7998065 : Blo 1136633 7998065 := bstep (se 2 (by rfl) ⟨2999274, by rfl⟩ : syracuseStep 7998065 = 5998549) B5998549
theorem B1706609 : Blo 1136633 1706609 := bstep (se 2 (by rfl) ⟨639978, by rfl⟩ : syracuseStep 1706609 = 1279957) B1279957
theorem B1706627 : Blo 1136633 1706627 := bstep (se 1 (by rfl) ⟨1279970, by rfl⟩ : syracuseStep 1706627 = 2559941) B2559941
theorem B2558609 : Blo 1136633 2558609 := bstep (se 2 (by rfl) ⟨959478, by rfl⟩ : syracuseStep 2558609 = 1918957) B1918957
theorem B1280659 : Blo 1136633 1280659 := bstep (se 1 (by rfl) ⟨960494, by rfl⟩ : syracuseStep 1280659 = 1920989) B1920989
theorem B1706657 : Blo 1136633 1706657 := bstep (se 2 (by rfl) ⟨639996, by rfl⟩ : syracuseStep 1706657 = 1279993) B1279993
theorem B2558627 : Blo 1136633 2558627 := bstep (se 1 (by rfl) ⟨1918970, by rfl⟩ : syracuseStep 2558627 = 3837941) B3837941
theorem B1706675 : Blo 1136633 1706675 := bstep (se 1 (by rfl) ⟨1280006, by rfl⟩ : syracuseStep 1706675 = 2560013) B2560013
theorem B1706705 : Blo 1136633 1706705 := bstep (se 2 (by rfl) ⟨640014, by rfl⟩ : syracuseStep 1706705 = 1280029) B1280029
theorem B1706723 : Blo 1136633 1706723 := bstep (se 1 (by rfl) ⟨1280042, by rfl⟩ : syracuseStep 1706723 = 2560085) B2560085
theorem B1706753 : Blo 1136633 1706753 := bstep (se 2 (by rfl) ⟨640032, by rfl⟩ : syracuseStep 1706753 = 1280065) B1280065
theorem B1706771 : Blo 1136633 1706771 := bstep (se 1 (by rfl) ⟨1280078, by rfl⟩ : syracuseStep 1706771 = 2560157) B2560157
theorem B1280803 : Blo 1136633 1280803 := bstep (se 1 (by rfl) ⟨960602, by rfl⟩ : syracuseStep 1280803 = 1921205) B1921205
theorem B1706801 : Blo 1136633 1706801 := bstep (se 2 (by rfl) ⟨640050, by rfl⟩ : syracuseStep 1706801 = 1280101) B1280101
theorem B1706819 : Blo 1136633 1706819 := bstep (se 1 (by rfl) ⟨1280114, by rfl⟩ : syracuseStep 1706819 = 2560229) B2560229
theorem B3836753 : Blo 1136633 3836753 := bstep (se 2 (by rfl) ⟨1438782, by rfl⟩ : syracuseStep 3836753 = 2877565) B2877565
theorem B1706849 : Blo 1136633 1706849 := bstep (se 2 (by rfl) ⟨640068, by rfl⟩ : syracuseStep 1706849 = 1280137) B1280137
theorem B1706867 : Blo 1136633 1706867 := bstep (se 1 (by rfl) ⟨1280150, by rfl⟩ : syracuseStep 1706867 = 2560301) B2560301
theorem B1706897 : Blo 1136633 1706897 := bstep (se 2 (by rfl) ⟨640086, by rfl⟩ : syracuseStep 1706897 = 1280173) B1280173
theorem B1706915 : Blo 1136633 1706915 := bstep (se 1 (by rfl) ⟨1280186, by rfl⟩ : syracuseStep 1706915 = 2560373) B2560373
theorem B2558897 : Blo 1136633 2558897 := bstep (se 2 (by rfl) ⟨959586, by rfl⟩ : syracuseStep 2558897 = 1919173) B1919173
theorem B1280947 : Blo 1136633 1280947 := bstep (se 1 (by rfl) ⟨960710, by rfl⟩ : syracuseStep 1280947 = 1921421) B1921421
theorem B1706945 : Blo 1136633 1706945 := bstep (se 2 (by rfl) ⟨640104, by rfl⟩ : syracuseStep 1706945 = 1280209) B1280209
theorem B2558915 : Blo 1136633 2558915 := bstep (se 1 (by rfl) ⟨1919186, by rfl⟩ : syracuseStep 2558915 = 3838373) B3838373
theorem B3247057 : Blo 1136633 3247057 := bstep (se 2 (by rfl) ⟨1217646, by rfl⟩ : syracuseStep 3247057 = 2435293) B2435293
theorem B1706963 : Blo 1136633 1706963 := bstep (se 1 (by rfl) ⟨1280222, by rfl⟩ : syracuseStep 1706963 = 2560445) B2560445
theorem B1706993 : Blo 1136633 1706993 := bstep (se 2 (by rfl) ⟨640122, by rfl⟩ : syracuseStep 1706993 = 1280245) B1280245
theorem B1707011 : Blo 1136633 1707011 := bstep (se 1 (by rfl) ⟨1280258, by rfl⟩ : syracuseStep 1707011 = 2560517) B2560517
theorem B1707041 : Blo 1136633 1707041 := bstep (se 2 (by rfl) ⟨640140, by rfl⟩ : syracuseStep 1707041 = 1280281) B1280281
theorem B1707059 : Blo 1136633 1707059 := bstep (se 1 (by rfl) ⟨1280294, by rfl⟩ : syracuseStep 1707059 = 2560589) B2560589
theorem B1281091 : Blo 1136633 1281091 := bstep (se 1 (by rfl) ⟨960818, by rfl⟩ : syracuseStep 1281091 = 1921637) B1921637
theorem B1707089 : Blo 1136633 1707089 := bstep (se 2 (by rfl) ⟨640158, by rfl⟩ : syracuseStep 1707089 = 1280317) B1280317
theorem B1707107 : Blo 1136633 1707107 := bstep (se 1 (by rfl) ⟨1280330, by rfl⟩ : syracuseStep 1707107 = 2560661) B2560661
theorem B1707137 : Blo 1136633 1707137 := bstep (se 2 (by rfl) ⟨640176, by rfl⟩ : syracuseStep 1707137 = 1280353) B1280353
theorem B6229133 : Blo 1136633 6229133 := bstep (se 3 (by rfl) ⟨1167962, by rfl⟩ : syracuseStep 6229133 = 2335925) B2335925
theorem B2428049 : Blo 1136633 2428049 := bstep (se 2 (by rfl) ⟨910518, by rfl⟩ : syracuseStep 2428049 = 1821037) B1821037
theorem B1707155 : Blo 1136633 1707155 := bstep (se 1 (by rfl) ⟨1280366, by rfl⟩ : syracuseStep 1707155 = 2560733) B2560733
theorem B1707185 : Blo 1136633 1707185 := bstep (se 2 (by rfl) ⟨640194, by rfl⟩ : syracuseStep 1707185 = 1280389) B1280389
theorem B1707203 : Blo 1136633 1707203 := bstep (se 1 (by rfl) ⟨1280402, by rfl⟩ : syracuseStep 1707203 = 2560805) B2560805
theorem B2559185 : Blo 1136633 2559185 := bstep (se 2 (by rfl) ⟨959694, by rfl⟩ : syracuseStep 2559185 = 1919389) B1919389
theorem B1281235 : Blo 1136633 1281235 := bstep (se 1 (by rfl) ⟨960926, by rfl⟩ : syracuseStep 1281235 = 1921853) B1921853
theorem B1707233 : Blo 1136633 1707233 := bstep (se 2 (by rfl) ⟨640212, by rfl⟩ : syracuseStep 1707233 = 1280425) B1280425
theorem B2559203 : Blo 1136633 2559203 := bstep (se 1 (by rfl) ⟨1919402, by rfl⟩ : syracuseStep 2559203 = 3838805) B3838805
theorem B1707251 : Blo 1136633 1707251 := bstep (se 1 (by rfl) ⟨1280438, by rfl⟩ : syracuseStep 1707251 = 2560877) B2560877
theorem B1707281 : Blo 1136633 1707281 := bstep (se 2 (by rfl) ⟨640230, by rfl⟩ : syracuseStep 1707281 = 1280461) B1280461
theorem B1707299 : Blo 1136633 1707299 := bstep (se 1 (by rfl) ⟨1280474, by rfl⟩ : syracuseStep 1707299 = 2560949) B2560949
theorem B2886961 : Blo 1136633 2886961 := bstep (se 2 (by rfl) ⟨1082610, by rfl⟩ : syracuseStep 2886961 = 2165221) B2165221
theorem B1707329 : Blo 1136633 1707329 := bstep (se 2 (by rfl) ⟨640248, by rfl⟩ : syracuseStep 1707329 = 1280497) B1280497
theorem B1707347 : Blo 1136633 1707347 := bstep (se 1 (by rfl) ⟨1280510, by rfl⟩ : syracuseStep 1707347 = 2561021) B2561021
theorem B1281379 : Blo 1136633 1281379 := bstep (se 1 (by rfl) ⟨961034, by rfl⟩ : syracuseStep 1281379 = 1922069) B1922069
theorem B3837293 : Blo 1136633 3837293 := bstep (se 3 (by rfl) ⟨719492, by rfl⟩ : syracuseStep 3837293 = 1438985) B1438985
theorem B1707377 : Blo 1136633 1707377 := bstep (se 2 (by rfl) ⟨640266, by rfl⟩ : syracuseStep 1707377 = 1280533) B1280533
theorem B1707395 : Blo 1136633 1707395 := bstep (se 1 (by rfl) ⟨1280546, by rfl⟩ : syracuseStep 1707395 = 2561093) B2561093
theorem B1707425 : Blo 1136633 1707425 := bstep (se 2 (by rfl) ⟨640284, by rfl⟩ : syracuseStep 1707425 = 1280569) B1280569
theorem B3837347 : Blo 1136633 3837347 := bstep (se 1 (by rfl) ⟨2878010, by rfl⟩ : syracuseStep 3837347 = 5756021) B5756021
theorem B1707443 : Blo 1136633 1707443 := bstep (se 1 (by rfl) ⟨1280582, by rfl⟩ : syracuseStep 1707443 = 2561165) B2561165
theorem B4328909 : Blo 1136633 4328909 := bstep (se 3 (by rfl) ⟨811670, by rfl⟩ : syracuseStep 4328909 = 1623341) B1623341
theorem B1707473 : Blo 1136633 1707473 := bstep (se 2 (by rfl) ⟨640302, by rfl⟩ : syracuseStep 1707473 = 1280605) B1280605
theorem B1215955 : Blo 1136633 1215955 := bstep (se 1 (by rfl) ⟨911966, by rfl⟩ : syracuseStep 1215955 = 1823933) B1823933
theorem B1707491 : Blo 1136633 1707491 := bstep (se 1 (by rfl) ⟨1280618, by rfl⟩ : syracuseStep 1707491 = 2561237) B2561237
theorem B2559473 : Blo 1136633 2559473 := bstep (se 2 (by rfl) ⟨959802, by rfl⟩ : syracuseStep 2559473 = 1919605) B1919605
theorem B1281523 : Blo 1136633 1281523 := bstep (se 1 (by rfl) ⟨961142, by rfl⟩ : syracuseStep 1281523 = 1922285) B1922285
theorem B1707521 : Blo 1136633 1707521 := bstep (se 2 (by rfl) ⟨640320, by rfl⟩ : syracuseStep 1707521 = 1280641) B1280641
theorem B2559491 : Blo 1136633 2559491 := bstep (se 1 (by rfl) ⟨1919618, by rfl⟩ : syracuseStep 2559491 = 3839237) B3839237
theorem B1707539 : Blo 1136633 1707539 := bstep (se 1 (by rfl) ⟨1280654, by rfl⟩ : syracuseStep 1707539 = 2561309) B2561309
theorem B2428451 : Blo 1136633 2428451 := bstep (se 1 (by rfl) ⟨1821338, by rfl⟩ : syracuseStep 2428451 = 3642677) B3642677
theorem B1707569 : Blo 1136633 1707569 := bstep (se 2 (by rfl) ⟨640338, by rfl⟩ : syracuseStep 1707569 = 1280677) B1280677
theorem B1707587 : Blo 1136633 1707587 := bstep (se 1 (by rfl) ⟨1280690, by rfl⟩ : syracuseStep 1707587 = 2561381) B2561381
theorem B1707617 : Blo 1136633 1707617 := bstep (se 2 (by rfl) ⟨640356, by rfl⟩ : syracuseStep 1707617 = 1280713) B1280713
theorem B1707635 : Blo 1136633 1707635 := bstep (se 1 (by rfl) ⟨1280726, by rfl⟩ : syracuseStep 1707635 = 2561453) B2561453
theorem B1281667 : Blo 1136633 1281667 := bstep (se 1 (by rfl) ⟨961250, by rfl⟩ : syracuseStep 1281667 = 1922501) B1922501
theorem B1707665 : Blo 1136633 1707665 := bstep (se 2 (by rfl) ⟨640374, by rfl⟩ : syracuseStep 1707665 = 1280749) B1280749
theorem B1707683 : Blo 1136633 1707683 := bstep (se 1 (by rfl) ⟨1280762, by rfl⟩ : syracuseStep 1707683 = 2561525) B2561525
theorem B3837617 : Blo 1136633 3837617 := bstep (se 2 (by rfl) ⟨1439106, by rfl⟩ : syracuseStep 3837617 = 2878213) B2878213
theorem B1707713 : Blo 1136633 1707713 := bstep (se 2 (by rfl) ⟨640392, by rfl⟩ : syracuseStep 1707713 = 1280785) B1280785
theorem B1707731 : Blo 1136633 1707731 := bstep (se 1 (by rfl) ⟨1280798, by rfl⟩ : syracuseStep 1707731 = 2561597) B2561597
theorem B1707761 : Blo 1136633 1707761 := bstep (se 2 (by rfl) ⟨640410, by rfl⟩ : syracuseStep 1707761 = 1280821) B1280821
theorem B1707779 : Blo 1136633 1707779 := bstep (se 1 (by rfl) ⟨1280834, by rfl⟩ : syracuseStep 1707779 = 2561669) B2561669
theorem B2559761 : Blo 1136633 2559761 := bstep (se 2 (by rfl) ⟨959910, by rfl⟩ : syracuseStep 2559761 = 1919821) B1919821
theorem B1281811 : Blo 1136633 1281811 := bstep (se 1 (by rfl) ⟨961358, by rfl⟩ : syracuseStep 1281811 = 1922717) B1922717
theorem B1707809 : Blo 1136633 1707809 := bstep (se 2 (by rfl) ⟨640428, by rfl⟩ : syracuseStep 1707809 = 1280857) B1280857
theorem B2559779 : Blo 1136633 2559779 := bstep (se 1 (by rfl) ⟨1919834, by rfl⟩ : syracuseStep 2559779 = 3839669) B3839669
theorem B1707827 : Blo 1136633 1707827 := bstep (se 1 (by rfl) ⟨1280870, by rfl⟩ : syracuseStep 1707827 = 2561741) B2561741
theorem B1707857 : Blo 1136633 1707857 := bstep (se 2 (by rfl) ⟨640446, by rfl⟩ : syracuseStep 1707857 = 1280893) B1280893
theorem B1707875 : Blo 1136633 1707875 := bstep (se 1 (by rfl) ⟨1280906, by rfl⟩ : syracuseStep 1707875 = 2561813) B2561813
theorem B1707905 : Blo 1136633 1707905 := bstep (se 2 (by rfl) ⟨640464, by rfl⟩ : syracuseStep 1707905 = 1280929) B1280929
theorem B1707923 : Blo 1136633 1707923 := bstep (se 1 (by rfl) ⟨1280942, by rfl⟩ : syracuseStep 1707923 = 2561885) B2561885
theorem B1281955 : Blo 1136633 1281955 := bstep (se 1 (by rfl) ⟨961466, by rfl⟩ : syracuseStep 1281955 = 1922933) B1922933
theorem B1707953 : Blo 1136633 1707953 := bstep (se 2 (by rfl) ⟨640482, by rfl⟩ : syracuseStep 1707953 = 1280965) B1280965
theorem B1707971 : Blo 1136633 1707971 := bstep (se 1 (by rfl) ⟨1280978, by rfl⟩ : syracuseStep 1707971 = 2561957) B2561957
theorem B6492109 : Blo 1136633 6492109 := bstep (se 3 (by rfl) ⟨1217270, by rfl⟩ : syracuseStep 6492109 = 2434541) B2434541
theorem B1708001 : Blo 1136633 1708001 := bstep (se 2 (by rfl) ⟨640500, by rfl⟩ : syracuseStep 1708001 = 1281001) B1281001
theorem B5771249 : Blo 1136633 5771249 := bstep (se 2 (by rfl) ⟨2164218, by rfl⟩ : syracuseStep 5771249 = 4328437) B4328437
theorem B1708019 : Blo 1136633 1708019 := bstep (se 1 (by rfl) ⟨1281014, by rfl⟩ : syracuseStep 1708019 = 2562029) B2562029
theorem B6230029 : Blo 1136633 6230029 := bstep (se 3 (by rfl) ⟨1168130, by rfl⟩ : syracuseStep 6230029 = 2336261) B2336261
theorem B1708049 : Blo 1136633 1708049 := bstep (se 2 (by rfl) ⟨640518, by rfl⟩ : syracuseStep 1708049 = 1281037) B1281037
theorem B5836835 : Blo 1136633 5836835 := bstep (se 1 (by rfl) ⟨4377626, by rfl⟩ : syracuseStep 5836835 = 8755253) B8755253
theorem B1708067 : Blo 1136633 1708067 := bstep (se 1 (by rfl) ⟨1281050, by rfl⟩ : syracuseStep 1708067 = 2562101) B2562101
theorem B2560049 : Blo 1136633 2560049 := bstep (se 2 (by rfl) ⟨960018, by rfl⟩ : syracuseStep 2560049 = 1920037) B1920037
theorem B1282099 : Blo 1136633 1282099 := bstep (se 1 (by rfl) ⟨961574, by rfl⟩ : syracuseStep 1282099 = 1923149) B1923149
theorem B1708097 : Blo 1136633 1708097 := bstep (se 2 (by rfl) ⟨640536, by rfl⟩ : syracuseStep 1708097 = 1281073) B1281073
theorem B2560067 : Blo 1136633 2560067 := bstep (se 1 (by rfl) ⟨1920050, by rfl⟩ : syracuseStep 2560067 = 3840101) B3840101
theorem B1708115 : Blo 1136633 1708115 := bstep (se 1 (by rfl) ⟨1281086, by rfl⟩ : syracuseStep 1708115 = 2562173) B2562173
theorem B2592881 : Blo 1136633 2592881 := bstep (se 2 (by rfl) ⟨972330, by rfl⟩ : syracuseStep 2592881 = 1944661) B1944661
theorem B1708145 : Blo 1136633 1708145 := bstep (se 2 (by rfl) ⟨640554, by rfl⟩ : syracuseStep 1708145 = 1281109) B1281109
theorem B1708163 : Blo 1136633 1708163 := bstep (se 1 (by rfl) ⟨1281122, by rfl⟩ : syracuseStep 1708163 = 2562245) B2562245
theorem B1708193 : Blo 1136633 1708193 := bstep (se 2 (by rfl) ⟨640572, by rfl⟩ : syracuseStep 1708193 = 1281145) B1281145
theorem B1708211 : Blo 1136633 1708211 := bstep (se 1 (by rfl) ⟨1281158, by rfl⟩ : syracuseStep 1708211 = 2562317) B2562317
theorem B1282243 : Blo 1136633 1282243 := bstep (se 1 (by rfl) ⟨961682, by rfl⟩ : syracuseStep 1282243 = 1923365) B1923365
theorem B3838157 : Blo 1136633 3838157 := bstep (se 3 (by rfl) ⟨719654, by rfl⟩ : syracuseStep 3838157 = 1439309) B1439309
theorem B1708241 : Blo 1136633 1708241 := bstep (se 2 (by rfl) ⟨640590, by rfl⟩ : syracuseStep 1708241 = 1281181) B1281181
theorem B1708259 : Blo 1136633 1708259 := bstep (se 1 (by rfl) ⟨1281194, by rfl⟩ : syracuseStep 1708259 = 2562389) B2562389
theorem B4329713 : Blo 1136633 4329713 := bstep (se 2 (by rfl) ⟨1623642, by rfl⟩ : syracuseStep 4329713 = 3247285) B3247285
theorem B1708289 : Blo 1136633 1708289 := bstep (se 2 (by rfl) ⟨640608, by rfl⟩ : syracuseStep 1708289 = 1281217) B1281217
theorem B3838211 : Blo 1136633 3838211 := bstep (se 1 (by rfl) ⟨2878658, by rfl⟩ : syracuseStep 3838211 = 5757317) B5757317
theorem B1708307 : Blo 1136633 1708307 := bstep (se 1 (by rfl) ⟨1281230, by rfl⟩ : syracuseStep 1708307 = 2562461) B2562461
theorem B5476643 : Blo 1136633 5476643 := bstep (se 1 (by rfl) ⟨4107482, by rfl⟩ : syracuseStep 5476643 = 8214965) B8214965
theorem B1708337 : Blo 1136633 1708337 := bstep (se 2 (by rfl) ⟨640626, by rfl⟩ : syracuseStep 1708337 = 1281253) B1281253
theorem B1708355 : Blo 1136633 1708355 := bstep (se 1 (by rfl) ⟨1281266, by rfl⟩ : syracuseStep 1708355 = 2562533) B2562533
theorem B8655173 : Blo 1136633 8655173 := bstep (se 4 (by rfl) ⟨811422, by rfl⟩ : syracuseStep 8655173 = 1622845) B1622845
theorem B2560337 : Blo 1136633 2560337 := bstep (se 2 (by rfl) ⟨960126, by rfl⟩ : syracuseStep 2560337 = 1920253) B1920253
theorem B1282387 : Blo 1136633 1282387 := bstep (se 1 (by rfl) ⟨961790, by rfl⟩ : syracuseStep 1282387 = 1923581) B1923581
theorem B1708385 : Blo 1136633 1708385 := bstep (se 2 (by rfl) ⟨640644, by rfl⟩ : syracuseStep 1708385 = 1281289) B1281289
theorem B2560355 : Blo 1136633 2560355 := bstep (se 1 (by rfl) ⟨1920266, by rfl⟩ : syracuseStep 2560355 = 3840533) B3840533
theorem B1708403 : Blo 1136633 1708403 := bstep (se 1 (by rfl) ⟨1281302, by rfl⟩ : syracuseStep 1708403 = 2562605) B2562605
theorem B1708433 : Blo 1136633 1708433 := bstep (se 2 (by rfl) ⟨640662, by rfl⟩ : syracuseStep 1708433 = 1281325) B1281325
theorem B2429347 : Blo 1136633 2429347 := bstep (se 1 (by rfl) ⟨1822010, by rfl⟩ : syracuseStep 2429347 = 3644021) B3644021
theorem B1708451 : Blo 1136633 1708451 := bstep (se 1 (by rfl) ⟨1281338, by rfl⟩ : syracuseStep 1708451 = 2562677) B2562677
theorem B1708481 : Blo 1136633 1708481 := bstep (se 2 (by rfl) ⟨640680, by rfl⟩ : syracuseStep 1708481 = 1281361) B1281361
theorem B1216963 : Blo 1136633 1216963 := bstep (se 1 (by rfl) ⟨912722, by rfl⟩ : syracuseStep 1216963 = 1825445) B1825445
theorem B1708499 : Blo 1136633 1708499 := bstep (se 1 (by rfl) ⟨1281374, by rfl⟩ : syracuseStep 1708499 = 2562749) B2562749
theorem B1282531 : Blo 1136633 1282531 := bstep (se 1 (by rfl) ⟨961898, by rfl⟩ : syracuseStep 1282531 = 1923797) B1923797
theorem B1708529 : Blo 1136633 1708529 := bstep (se 2 (by rfl) ⟨640698, by rfl⟩ : syracuseStep 1708529 = 1281397) B1281397
theorem B15602161 : Blo 1136633 15602161 := bstep (se 2 (by rfl) ⟨5850810, by rfl⟩ : syracuseStep 15602161 = 11701621) B11701621
theorem B1708547 : Blo 1136633 1708547 := bstep (se 1 (by rfl) ⟨1281410, by rfl⟩ : syracuseStep 1708547 = 2562821) B2562821
theorem B3838481 : Blo 1136633 3838481 := bstep (se 2 (by rfl) ⟨1439430, by rfl⟩ : syracuseStep 3838481 = 2878861) B2878861
theorem B1708577 : Blo 1136633 1708577 := bstep (se 2 (by rfl) ⟨640716, by rfl⟩ : syracuseStep 1708577 = 1281433) B1281433
theorem B1708595 : Blo 1136633 1708595 := bstep (se 1 (by rfl) ⟨1281446, by rfl⟩ : syracuseStep 1708595 = 2562893) B2562893
theorem B1708625 : Blo 1136633 1708625 := bstep (se 2 (by rfl) ⟨640734, by rfl⟩ : syracuseStep 1708625 = 1281469) B1281469
theorem B1708643 : Blo 1136633 1708643 := bstep (se 1 (by rfl) ⟨1281482, by rfl⟩ : syracuseStep 1708643 = 2562965) B2562965
theorem B2560625 : Blo 1136633 2560625 := bstep (se 2 (by rfl) ⟨960234, by rfl⟩ : syracuseStep 2560625 = 1920469) B1920469
theorem B1282675 : Blo 1136633 1282675 := bstep (se 1 (by rfl) ⟨962006, by rfl⟩ : syracuseStep 1282675 = 1924013) B1924013
theorem B1708673 : Blo 1136633 1708673 := bstep (se 2 (by rfl) ⟨640752, by rfl⟩ : syracuseStep 1708673 = 1281505) B1281505
theorem B2560643 : Blo 1136633 2560643 := bstep (se 1 (by rfl) ⟨1920482, by rfl⟩ : syracuseStep 2560643 = 3840965) B3840965
theorem B1708691 : Blo 1136633 1708691 := bstep (se 1 (by rfl) ⟨1281518, by rfl⟩ : syracuseStep 1708691 = 2563037) B2563037
theorem B1708721 : Blo 1136633 1708721 := bstep (se 2 (by rfl) ⟨640770, by rfl⟩ : syracuseStep 1708721 = 1281541) B1281541
theorem B1708739 : Blo 1136633 1708739 := bstep (se 1 (by rfl) ⟨1281554, by rfl⟩ : syracuseStep 1708739 = 2563109) B2563109
theorem B1708769 : Blo 1136633 1708769 := bstep (se 2 (by rfl) ⟨640788, by rfl⟩ : syracuseStep 1708769 = 1281577) B1281577
theorem B1708787 : Blo 1136633 1708787 := bstep (se 1 (by rfl) ⟨1281590, by rfl⟩ : syracuseStep 1708787 = 2563181) B2563181
theorem B1282819 : Blo 1136633 1282819 := bstep (se 1 (by rfl) ⟨962114, by rfl⟩ : syracuseStep 1282819 = 1924229) B1924229
theorem B1708817 : Blo 1136633 1708817 := bstep (se 2 (by rfl) ⟨640806, by rfl⟩ : syracuseStep 1708817 = 1281613) B1281613
theorem B1708835 : Blo 1136633 1708835 := bstep (se 1 (by rfl) ⟨1281626, by rfl⟩ : syracuseStep 1708835 = 2563253) B2563253
theorem B1708865 : Blo 1136633 1708865 := bstep (se 2 (by rfl) ⟨640824, by rfl⟩ : syracuseStep 1708865 = 1281649) B1281649
theorem B1708883 : Blo 1136633 1708883 := bstep (se 1 (by rfl) ⟨1281662, by rfl⟩ : syracuseStep 1708883 = 2563325) B2563325
theorem B1708913 : Blo 1136633 1708913 := bstep (se 2 (by rfl) ⟨640842, by rfl⟩ : syracuseStep 1708913 = 1281685) B1281685
theorem B1708931 : Blo 1136633 1708931 := bstep (se 1 (by rfl) ⟨1281698, by rfl⟩ : syracuseStep 1708931 = 2563397) B2563397
theorem B4330381 : Blo 1136633 4330381 := bstep (se 3 (by rfl) ⟨811946, by rfl⟩ : syracuseStep 4330381 = 1623893) B1623893
theorem B2560913 : Blo 1136633 2560913 := bstep (se 2 (by rfl) ⟨960342, by rfl⟩ : syracuseStep 2560913 = 1920685) B1920685
theorem B1282963 : Blo 1136633 1282963 := bstep (se 1 (by rfl) ⟨962222, by rfl⟩ : syracuseStep 1282963 = 1924445) B1924445
theorem B1708961 : Blo 1136633 1708961 := bstep (se 2 (by rfl) ⟨640860, by rfl⟩ : syracuseStep 1708961 = 1281721) B1281721
theorem B2560931 : Blo 1136633 2560931 := bstep (se 1 (by rfl) ⟨1920698, by rfl⟩ : syracuseStep 2560931 = 3841397) B3841397
theorem B1708979 : Blo 1136633 1708979 := bstep (se 1 (by rfl) ⟨1281734, by rfl⟩ : syracuseStep 1708979 = 2563469) B2563469
theorem B1709009 : Blo 1136633 1709009 := bstep (se 2 (by rfl) ⟨640878, by rfl⟩ : syracuseStep 1709009 = 1281757) B1281757
theorem B1709027 : Blo 1136633 1709027 := bstep (se 1 (by rfl) ⟨1281770, by rfl⟩ : syracuseStep 1709027 = 2563541) B2563541
theorem B1709057 : Blo 1136633 1709057 := bstep (se 2 (by rfl) ⟨640896, by rfl⟩ : syracuseStep 1709057 = 1281793) B1281793
theorem B1709075 : Blo 1136633 1709075 := bstep (se 1 (by rfl) ⟨1281806, by rfl⟩ : syracuseStep 1709075 = 2563613) B2563613
theorem B1283107 : Blo 1136633 1283107 := bstep (se 1 (by rfl) ⟨962330, by rfl⟩ : syracuseStep 1283107 = 1924661) B1924661
theorem B3839021 : Blo 1136633 3839021 := bstep (se 3 (by rfl) ⟨719816, by rfl⟩ : syracuseStep 3839021 = 1439633) B1439633
theorem B1709105 : Blo 1136633 1709105 := bstep (se 2 (by rfl) ⟨640914, by rfl⟩ : syracuseStep 1709105 = 1281829) B1281829
theorem B1217587 : Blo 1136633 1217587 := bstep (se 1 (by rfl) ⟨913190, by rfl⟩ : syracuseStep 1217587 = 1826381) B1826381
theorem B1709123 : Blo 1136633 1709123 := bstep (se 1 (by rfl) ⟨1281842, by rfl⟩ : syracuseStep 1709123 = 2563685) B2563685
theorem B1709153 : Blo 1136633 1709153 := bstep (se 2 (by rfl) ⟨640932, by rfl⟩ : syracuseStep 1709153 = 1281865) B1281865
theorem B3839075 : Blo 1136633 3839075 := bstep (se 1 (by rfl) ⟨2879306, by rfl⟩ : syracuseStep 3839075 = 5758613) B5758613
theorem B5837923 : Blo 1136633 5837923 := bstep (se 1 (by rfl) ⟨4378442, by rfl⟩ : syracuseStep 5837923 = 8756885) B8756885
theorem B1709171 : Blo 1136633 1709171 := bstep (se 1 (by rfl) ⟨1281878, by rfl⟩ : syracuseStep 1709171 = 2563757) B2563757
theorem B3642509 : Blo 1136633 3642509 := bstep (se 3 (by rfl) ⟨682970, by rfl⟩ : syracuseStep 3642509 = 1365941) B1365941
theorem B1709201 : Blo 1136633 1709201 := bstep (se 2 (by rfl) ⟨640950, by rfl⟩ : syracuseStep 1709201 = 1281901) B1281901
theorem B1709219 : Blo 1136633 1709219 := bstep (se 1 (by rfl) ⟨1281914, by rfl⟩ : syracuseStep 1709219 = 2563829) B2563829
theorem B2561201 : Blo 1136633 2561201 := bstep (se 2 (by rfl) ⟨960450, by rfl⟩ : syracuseStep 2561201 = 1920901) B1920901
theorem B1709249 : Blo 1136633 1709249 := bstep (se 2 (by rfl) ⟨640968, by rfl⟩ : syracuseStep 1709249 = 1281937) B1281937
theorem B2561219 : Blo 1136633 2561219 := bstep (se 1 (by rfl) ⟨1920914, by rfl⟩ : syracuseStep 2561219 = 3841829) B3841829
theorem B1709267 : Blo 1136633 1709267 := bstep (se 1 (by rfl) ⟨1281950, by rfl⟩ : syracuseStep 1709267 = 2563901) B2563901
theorem B1709297 : Blo 1136633 1709297 := bstep (se 2 (by rfl) ⟨640986, by rfl⟩ : syracuseStep 1709297 = 1281973) B1281973
theorem B1709315 : Blo 1136633 1709315 := bstep (se 1 (by rfl) ⟨1281986, by rfl⟩ : syracuseStep 1709315 = 2563973) B2563973
theorem B1709345 : Blo 1136633 1709345 := bstep (se 2 (by rfl) ⟨641004, by rfl⟩ : syracuseStep 1709345 = 1282009) B1282009
theorem B1709363 : Blo 1136633 1709363 := bstep (se 1 (by rfl) ⟨1282022, by rfl⟩ : syracuseStep 1709363 = 2564045) B2564045
theorem B1709393 : Blo 1136633 1709393 := bstep (se 2 (by rfl) ⟨641022, by rfl⟩ : syracuseStep 1709393 = 1282045) B1282045
theorem B1709411 : Blo 1136633 1709411 := bstep (se 1 (by rfl) ⟨1282058, by rfl⟩ : syracuseStep 1709411 = 2564117) B2564117
theorem B3839345 : Blo 1136633 3839345 := bstep (se 2 (by rfl) ⟨1439754, by rfl⟩ : syracuseStep 3839345 = 2879509) B2879509
theorem B1709441 : Blo 1136633 1709441 := bstep (se 2 (by rfl) ⟨641040, by rfl⟩ : syracuseStep 1709441 = 1282081) B1282081
theorem B1709459 : Blo 1136633 1709459 := bstep (se 1 (by rfl) ⟨1282094, by rfl⟩ : syracuseStep 1709459 = 2564189) B2564189
theorem B5772707 : Blo 1136633 5772707 := bstep (se 1 (by rfl) ⟨4329530, by rfl⟩ : syracuseStep 5772707 = 8659061) B8659061
theorem B1709489 : Blo 1136633 1709489 := bstep (se 2 (by rfl) ⟨641058, by rfl⟩ : syracuseStep 1709489 = 1282117) B1282117
theorem B1709507 : Blo 1136633 1709507 := bstep (se 1 (by rfl) ⟨1282130, by rfl⟩ : syracuseStep 1709507 = 2564261) B2564261
theorem B2561489 : Blo 1136633 2561489 := bstep (se 2 (by rfl) ⟨960558, by rfl⟩ : syracuseStep 2561489 = 1921117) B1921117
theorem B1709537 : Blo 1136633 1709537 := bstep (se 2 (by rfl) ⟨641076, by rfl⟩ : syracuseStep 1709537 = 1282153) B1282153
theorem B2561507 : Blo 1136633 2561507 := bstep (se 1 (by rfl) ⟨1921130, by rfl⟩ : syracuseStep 2561507 = 3842261) B3842261
theorem B1709555 : Blo 1136633 1709555 := bstep (se 1 (by rfl) ⟨1282166, by rfl⟩ : syracuseStep 1709555 = 2564333) B2564333
theorem B1709585 : Blo 1136633 1709585 := bstep (se 2 (by rfl) ⟨641094, by rfl⟩ : syracuseStep 1709585 = 1282189) B1282189
theorem B1709603 : Blo 1136633 1709603 := bstep (se 1 (by rfl) ⟨1282202, by rfl⟩ : syracuseStep 1709603 = 2564405) B2564405
theorem B1709633 : Blo 1136633 1709633 := bstep (se 2 (by rfl) ⟨641112, by rfl⟩ : syracuseStep 1709633 = 1282225) B1282225
theorem B1709651 : Blo 1136633 1709651 := bstep (se 1 (by rfl) ⟨1282238, by rfl⟩ : syracuseStep 1709651 = 2564477) B2564477
theorem B2430577 : Blo 1136633 2430577 := bstep (se 2 (by rfl) ⟨911466, by rfl⟩ : syracuseStep 2430577 = 1822933) B1822933
theorem B1709681 : Blo 1136633 1709681 := bstep (se 2 (by rfl) ⟨641130, by rfl⟩ : syracuseStep 1709681 = 1282261) B1282261
theorem B1709699 : Blo 1136633 1709699 := bstep (se 1 (by rfl) ⟨1282274, by rfl⟩ : syracuseStep 1709699 = 2564549) B2564549
theorem B1709729 : Blo 1136633 1709729 := bstep (se 2 (by rfl) ⟨641148, by rfl⟩ : syracuseStep 1709729 = 1282297) B1282297
theorem B1709747 : Blo 1136633 1709747 := bstep (se 1 (by rfl) ⟨1282310, by rfl⟩ : syracuseStep 1709747 = 2564621) B2564621
theorem B1709777 : Blo 1136633 1709777 := bstep (se 2 (by rfl) ⟨641166, by rfl⟩ : syracuseStep 1709777 = 1282333) B1282333
theorem B26285795 : Blo 1136633 26285795 := bstep (se 1 (by rfl) ⟨19714346, by rfl⟩ : syracuseStep 26285795 = 39428693) B39428693
theorem B1709795 : Blo 1136633 1709795 := bstep (se 1 (by rfl) ⟨1282346, by rfl⟩ : syracuseStep 1709795 = 2564693) B2564693
theorem B2561777 : Blo 1136633 2561777 := bstep (se 2 (by rfl) ⟨960666, by rfl⟩ : syracuseStep 2561777 = 1921333) B1921333
theorem B1709825 : Blo 1136633 1709825 := bstep (se 2 (by rfl) ⟨641184, by rfl⟩ : syracuseStep 1709825 = 1282369) B1282369
theorem B2561795 : Blo 1136633 2561795 := bstep (se 1 (by rfl) ⟨1921346, by rfl⟩ : syracuseStep 2561795 = 3842693) B3842693
theorem B1709843 : Blo 1136633 1709843 := bstep (se 1 (by rfl) ⟨1282382, by rfl⟩ : syracuseStep 1709843 = 2564765) B2564765
theorem B1709873 : Blo 1136633 1709873 := bstep (se 2 (by rfl) ⟨641202, by rfl⟩ : syracuseStep 1709873 = 1282405) B1282405
theorem B1709891 : Blo 1136633 1709891 := bstep (se 1 (by rfl) ⟨1282418, by rfl⟩ : syracuseStep 1709891 = 2564837) B2564837
theorem B1709921 : Blo 1136633 1709921 := bstep (se 2 (by rfl) ⟨641220, by rfl⟩ : syracuseStep 1709921 = 1282441) B1282441
theorem B1709939 : Blo 1136633 1709939 := bstep (se 1 (by rfl) ⟨1282454, by rfl⟩ : syracuseStep 1709939 = 2564909) B2564909
theorem B3839885 : Blo 1136633 3839885 := bstep (se 3 (by rfl) ⟨719978, by rfl⟩ : syracuseStep 3839885 = 1439957) B1439957
theorem B6494093 : Blo 1136633 6494093 := bstep (se 3 (by rfl) ⟨1217642, by rfl⟩ : syracuseStep 6494093 = 2435285) B2435285
theorem B1709969 : Blo 1136633 1709969 := bstep (se 2 (by rfl) ⟨641238, by rfl⟩ : syracuseStep 1709969 = 1282477) B1282477
theorem B1709987 : Blo 1136633 1709987 := bstep (se 1 (by rfl) ⟨1282490, by rfl⟩ : syracuseStep 1709987 = 2564981) B2564981
theorem B1710017 : Blo 1136633 1710017 := bstep (se 2 (by rfl) ⟨641256, by rfl⟩ : syracuseStep 1710017 = 1282513) B1282513
theorem B3839939 : Blo 1136633 3839939 := bstep (se 1 (by rfl) ⟨2879954, by rfl⟩ : syracuseStep 3839939 = 5759909) B5759909
theorem B1710035 : Blo 1136633 1710035 := bstep (se 1 (by rfl) ⟨1282526, by rfl⟩ : syracuseStep 1710035 = 2565053) B2565053
theorem B1710065 : Blo 1136633 1710065 := bstep (se 2 (by rfl) ⟨641274, by rfl⟩ : syracuseStep 1710065 = 1282549) B1282549
theorem B1710083 : Blo 1136633 1710083 := bstep (se 1 (by rfl) ⟨1282562, by rfl⟩ : syracuseStep 1710083 = 2565125) B2565125
theorem B2562065 : Blo 1136633 2562065 := bstep (se 2 (by rfl) ⟨960774, by rfl⟩ : syracuseStep 2562065 = 1921549) B1921549
theorem B1710113 : Blo 1136633 1710113 := bstep (se 2 (by rfl) ⟨641292, by rfl⟩ : syracuseStep 1710113 = 1282585) B1282585
theorem B2562083 : Blo 1136633 2562083 := bstep (se 1 (by rfl) ⟨1921562, by rfl⟩ : syracuseStep 2562083 = 3843125) B3843125
theorem B1710131 : Blo 1136633 1710131 := bstep (se 1 (by rfl) ⟨1282598, by rfl⟩ : syracuseStep 1710131 = 2565197) B2565197
theorem B1710161 : Blo 1136633 1710161 := bstep (se 2 (by rfl) ⟨641310, by rfl⟩ : syracuseStep 1710161 = 1282621) B1282621
theorem B8198243 : Blo 1136633 8198243 := bstep (se 1 (by rfl) ⟨6148682, by rfl⟩ : syracuseStep 8198243 = 12297365) B12297365
theorem B1710179 : Blo 1136633 1710179 := bstep (se 1 (by rfl) ⟨1282634, by rfl⟩ : syracuseStep 1710179 = 2565269) B2565269
theorem B1710209 : Blo 1136633 1710209 := bstep (se 2 (by rfl) ⟨641328, by rfl⟩ : syracuseStep 1710209 = 1282657) B1282657
theorem B1710227 : Blo 1136633 1710227 := bstep (se 1 (by rfl) ⟨1282670, by rfl⟩ : syracuseStep 1710227 = 2565341) B2565341
theorem B1710257 : Blo 1136633 1710257 := bstep (se 2 (by rfl) ⟨641346, by rfl⟩ : syracuseStep 1710257 = 1282693) B1282693
theorem B1710275 : Blo 1136633 1710275 := bstep (se 1 (by rfl) ⟨1282706, by rfl⟩ : syracuseStep 1710275 = 2565413) B2565413
theorem B5773517 : Blo 1136633 5773517 := bstep (se 3 (by rfl) ⟨1082534, by rfl⟩ : syracuseStep 5773517 = 2165069) B2165069
theorem B3840209 : Blo 1136633 3840209 := bstep (se 2 (by rfl) ⟨1440078, by rfl⟩ : syracuseStep 3840209 = 2880157) B2880157
theorem B1710305 : Blo 1136633 1710305 := bstep (se 2 (by rfl) ⟨641364, by rfl⟩ : syracuseStep 1710305 = 1282729) B1282729
theorem B5478641 : Blo 1136633 5478641 := bstep (se 2 (by rfl) ⟨2054490, by rfl⟩ : syracuseStep 5478641 = 4108981) B4108981
theorem B1710323 : Blo 1136633 1710323 := bstep (se 1 (by rfl) ⟨1282742, by rfl⟩ : syracuseStep 1710323 = 2565485) B2565485
theorem B1710353 : Blo 1136633 1710353 := bstep (se 2 (by rfl) ⟨641382, by rfl⟩ : syracuseStep 1710353 = 1282765) B1282765
theorem B1710371 : Blo 1136633 1710371 := bstep (se 1 (by rfl) ⟨1282778, by rfl⟩ : syracuseStep 1710371 = 2565557) B2565557
theorem B2562353 : Blo 1136633 2562353 := bstep (se 2 (by rfl) ⟨960882, by rfl⟩ : syracuseStep 2562353 = 1921765) B1921765
theorem B1710401 : Blo 1136633 1710401 := bstep (se 2 (by rfl) ⟨641400, by rfl⟩ : syracuseStep 1710401 = 1282801) B1282801
theorem B2562371 : Blo 1136633 2562371 := bstep (se 1 (by rfl) ⟨1921778, by rfl⟩ : syracuseStep 2562371 = 3843557) B3843557
theorem B1710419 : Blo 1136633 1710419 := bstep (se 1 (by rfl) ⟨1282814, by rfl⟩ : syracuseStep 1710419 = 2565629) B2565629
theorem B1710449 : Blo 1136633 1710449 := bstep (se 2 (by rfl) ⟨641418, by rfl⟩ : syracuseStep 1710449 = 1282837) B1282837
theorem B1710467 : Blo 1136633 1710467 := bstep (se 1 (by rfl) ⟨1282850, by rfl⟩ : syracuseStep 1710467 = 2565701) B2565701
theorem B1710497 : Blo 1136633 1710497 := bstep (se 2 (by rfl) ⟨641436, by rfl⟩ : syracuseStep 1710497 = 1282873) B1282873
theorem B1710515 : Blo 1136633 1710515 := bstep (se 1 (by rfl) ⟨1282886, by rfl⟩ : syracuseStep 1710515 = 2565773) B2565773
theorem B1710545 : Blo 1136633 1710545 := bstep (se 2 (by rfl) ⟨641454, by rfl⟩ : syracuseStep 1710545 = 1282909) B1282909
theorem B1710563 : Blo 1136633 1710563 := bstep (se 1 (by rfl) ⟨1282922, by rfl⟩ : syracuseStep 1710563 = 2565845) B2565845
theorem B1710593 : Blo 1136633 1710593 := bstep (se 2 (by rfl) ⟨641472, by rfl⟩ : syracuseStep 1710593 = 1282945) B1282945
theorem B1710611 : Blo 1136633 1710611 := bstep (se 1 (by rfl) ⟨1282958, by rfl⟩ : syracuseStep 1710611 = 2565917) B2565917
theorem B1710641 : Blo 1136633 1710641 := bstep (se 2 (by rfl) ⟨641490, by rfl⟩ : syracuseStep 1710641 = 1282981) B1282981
theorem B1710659 : Blo 1136633 1710659 := bstep (se 1 (by rfl) ⟨1282994, by rfl⟩ : syracuseStep 1710659 = 2565989) B2565989
theorem B2562641 : Blo 1136633 2562641 := bstep (se 2 (by rfl) ⟨960990, by rfl⟩ : syracuseStep 2562641 = 1921981) B1921981
theorem B1710689 : Blo 1136633 1710689 := bstep (se 2 (by rfl) ⟨641508, by rfl⟩ : syracuseStep 1710689 = 1283017) B1283017
theorem B2562659 : Blo 1136633 2562659 := bstep (se 1 (by rfl) ⟨1921994, by rfl⟩ : syracuseStep 2562659 = 3843989) B3843989
theorem B1710707 : Blo 1136633 1710707 := bstep (se 1 (by rfl) ⟨1283030, by rfl⟩ : syracuseStep 1710707 = 2566061) B2566061
theorem B1710737 : Blo 1136633 1710737 := bstep (se 2 (by rfl) ⟨641526, by rfl⟩ : syracuseStep 1710737 = 1283053) B1283053
theorem B1710755 : Blo 1136633 1710755 := bstep (se 1 (by rfl) ⟨1283066, by rfl⟩ : syracuseStep 1710755 = 2566133) B2566133
theorem B1710785 : Blo 1136633 1710785 := bstep (se 2 (by rfl) ⟨641544, by rfl⟩ : syracuseStep 1710785 = 1283089) B1283089
theorem B1710803 : Blo 1136633 1710803 := bstep (se 1 (by rfl) ⟨1283102, by rfl⟩ : syracuseStep 1710803 = 2566205) B2566205
theorem B3840749 : Blo 1136633 3840749 := bstep (se 3 (by rfl) ⟨720140, by rfl⟩ : syracuseStep 3840749 = 1440281) B1440281
theorem B1710833 : Blo 1136633 1710833 := bstep (se 2 (by rfl) ⟨641562, by rfl⟩ : syracuseStep 1710833 = 1283125) B1283125
theorem B1710851 : Blo 1136633 1710851 := bstep (se 1 (by rfl) ⟨1283138, by rfl⟩ : syracuseStep 1710851 = 2566277) B2566277
theorem B1153811 : Blo 1136633 1153811 := bstep (se 1 (by rfl) ⟨865358, by rfl⟩ : syracuseStep 1153811 = 1730717) B1730717
theorem B1710881 : Blo 1136633 1710881 := bstep (se 2 (by rfl) ⟨641580, by rfl⟩ : syracuseStep 1710881 = 1283161) B1283161
theorem B3840803 : Blo 1136633 3840803 := bstep (se 1 (by rfl) ⟨2880602, by rfl⟩ : syracuseStep 3840803 = 5761205) B5761205
theorem B6495025 : Blo 1136633 6495025 := bstep (se 2 (by rfl) ⟨2435634, by rfl⟩ : syracuseStep 6495025 = 4871269) B4871269
theorem B1710899 : Blo 1136633 1710899 := bstep (se 1 (by rfl) ⟨1283174, by rfl⟩ : syracuseStep 1710899 = 2566349) B2566349
theorem B1710929 : Blo 1136633 1710929 := bstep (se 2 (by rfl) ⟨641598, by rfl⟩ : syracuseStep 1710929 = 1283197) B1283197
theorem B1710947 : Blo 1136633 1710947 := bstep (se 1 (by rfl) ⟨1283210, by rfl⟩ : syracuseStep 1710947 = 2566421) B2566421
theorem B2562929 : Blo 1136633 2562929 := bstep (se 2 (by rfl) ⟨961098, by rfl⟩ : syracuseStep 2562929 = 1922197) B1922197
theorem B2562947 : Blo 1136633 2562947 := bstep (se 1 (by rfl) ⟨1922210, by rfl⟩ : syracuseStep 2562947 = 3844421) B3844421
theorem B12295109 : Blo 1136633 12295109 := bstep (se 4 (by rfl) ⟨1152666, by rfl⟩ : syracuseStep 12295109 = 2305333) B2305333
theorem B3841073 : Blo 1136633 3841073 := bstep (se 2 (by rfl) ⟨1440402, by rfl⟩ : syracuseStep 3841073 = 2880805) B2880805
theorem B2432081 : Blo 1136633 2432081 := bstep (se 2 (by rfl) ⟨912030, by rfl⟩ : syracuseStep 2432081 = 1824061) B1824061
theorem B2432099 : Blo 1136633 2432099 := bstep (se 1 (by rfl) ⟨1824074, by rfl⟩ : syracuseStep 2432099 = 3648149) B3648149
theorem B2563217 : Blo 1136633 2563217 := bstep (se 2 (by rfl) ⟨961206, by rfl⟩ : syracuseStep 2563217 = 1922413) B1922413
theorem B2563235 : Blo 1136633 2563235 := bstep (se 1 (by rfl) ⟨1922426, by rfl⟩ : syracuseStep 2563235 = 3844853) B3844853
theorem B1973489 : Blo 1136633 1973489 := bstep (se 2 (by rfl) ⟨740058, by rfl⟩ : syracuseStep 1973489 = 1480117) B1480117
theorem B5479757 : Blo 1136633 5479757 := bstep (se 3 (by rfl) ⟨1027454, by rfl⟩ : syracuseStep 5479757 = 2054909) B2054909
theorem B10394993 : Blo 1136633 10394993 := bstep (se 2 (by rfl) ⟨3898122, by rfl⟩ : syracuseStep 10394993 = 7796245) B7796245
theorem B2563505 : Blo 1136633 2563505 := bstep (se 2 (by rfl) ⟨961314, by rfl⟩ : syracuseStep 2563505 = 1922629) B1922629
theorem B2563523 : Blo 1136633 2563523 := bstep (se 1 (by rfl) ⟨1922642, by rfl⟩ : syracuseStep 2563523 = 3845285) B3845285
theorem B3644995 : Blo 1136633 3644995 := bstep (se 1 (by rfl) ⟨2733746, by rfl⟩ : syracuseStep 3644995 = 5467493) B5467493
theorem B3841613 : Blo 1136633 3841613 := bstep (se 3 (by rfl) ⟨720302, by rfl⟩ : syracuseStep 3841613 = 1440605) B1440605
theorem B3841667 : Blo 1136633 3841667 := bstep (se 1 (by rfl) ⟨2881250, by rfl⟩ : syracuseStep 3841667 = 5762501) B5762501
theorem B3645137 : Blo 1136633 3645137 := bstep (se 2 (by rfl) ⟨1366926, by rfl⟩ : syracuseStep 3645137 = 2733853) B2733853
theorem B2563793 : Blo 1136633 2563793 := bstep (se 2 (by rfl) ⟨961422, by rfl⟩ : syracuseStep 2563793 = 1922845) B1922845
theorem B2563811 : Blo 1136633 2563811 := bstep (se 1 (by rfl) ⟨1922858, by rfl⟩ : syracuseStep 2563811 = 3845717) B3845717
theorem B3645251 : Blo 1136633 3645251 := bstep (se 1 (by rfl) ⟨2733938, by rfl⟩ : syracuseStep 3645251 = 5467877) B5467877
theorem B3841937 : Blo 1136633 3841937 := bstep (se 2 (by rfl) ⟨1440726, by rfl⟩ : syracuseStep 3841937 = 2881453) B2881453
theorem B2564081 : Blo 1136633 2564081 := bstep (se 2 (by rfl) ⟨961530, by rfl⟩ : syracuseStep 2564081 = 1923061) B1923061
theorem B2564099 : Blo 1136633 2564099 := bstep (se 1 (by rfl) ⟨1923074, by rfl⟩ : syracuseStep 2564099 = 3846149) B3846149
theorem B3121265 : Blo 1136633 3121265 := bstep (se 2 (by rfl) ⟨1170474, by rfl⟩ : syracuseStep 3121265 = 2340949) B2340949
theorem B2564369 : Blo 1136633 2564369 := bstep (se 2 (by rfl) ⟨961638, by rfl⟩ : syracuseStep 2564369 = 1923277) B1923277
theorem B4858147 : Blo 1136633 4858147 := bstep (se 1 (by rfl) ⟨3643610, by rfl⟩ : syracuseStep 4858147 = 7287221) B7287221
theorem B2564387 : Blo 1136633 2564387 := bstep (se 1 (by rfl) ⟨1923290, by rfl⟩ : syracuseStep 2564387 = 3846581) B3846581
theorem B3842477 : Blo 1136633 3842477 := bstep (se 3 (by rfl) ⟨720464, by rfl⟩ : syracuseStep 3842477 = 1440929) B1440929
theorem B3842531 : Blo 1136633 3842531 := bstep (se 1 (by rfl) ⟨2881898, by rfl⟩ : syracuseStep 3842531 = 5763797) B5763797
theorem B2564657 : Blo 1136633 2564657 := bstep (se 2 (by rfl) ⟨961746, by rfl⟩ : syracuseStep 2564657 = 1923493) B1923493
theorem B2564675 : Blo 1136633 2564675 := bstep (se 1 (by rfl) ⟨1923506, by rfl⟩ : syracuseStep 2564675 = 3847013) B3847013
theorem B5481101 : Blo 1136633 5481101 := bstep (se 3 (by rfl) ⟨1027706, by rfl⟩ : syracuseStep 5481101 = 2055413) B2055413
theorem B4104931 : Blo 1136633 4104931 := bstep (se 1 (by rfl) ⟨3078698, by rfl⟩ : syracuseStep 4104931 = 6157397) B6157397
theorem B3842801 : Blo 1136633 3842801 := bstep (se 2 (by rfl) ⟨1441050, by rfl⟩ : syracuseStep 3842801 = 2882101) B2882101
theorem B3646225 : Blo 1136633 3646225 := bstep (se 2 (by rfl) ⟨1367334, by rfl⟩ : syracuseStep 3646225 = 2734669) B2734669
theorem B1155875 : Blo 1136633 1155875 := bstep (se 1 (by rfl) ⟨866906, by rfl⟩ : syracuseStep 1155875 = 1733813) B1733813
theorem B3285809 : Blo 1136633 3285809 := bstep (se 2 (by rfl) ⟨1232178, by rfl⟩ : syracuseStep 3285809 = 2464357) B2464357
theorem B1975105 : Blo 1136633 1975105 := bstep (se 2 (by rfl) ⟨740664, by rfl⟩ : syracuseStep 1975105 = 1481329) B1481329
theorem B2564945 : Blo 1136633 2564945 := bstep (se 2 (by rfl) ⟨961854, by rfl⟩ : syracuseStep 2564945 = 1923709) B1923709
theorem B2564963 : Blo 1136633 2564963 := bstep (se 1 (by rfl) ⟨1923722, by rfl⟩ : syracuseStep 2564963 = 3847445) B3847445
theorem B6562765 : Blo 1136633 6562765 := bstep (se 3 (by rfl) ⟨1230518, by rfl⟩ : syracuseStep 6562765 = 2461037) B2461037
theorem B2925571 : Blo 1136633 2925571 := bstep (se 1 (by rfl) ⟨2194178, by rfl⟩ : syracuseStep 2925571 = 4388357) B4388357
theorem B2434097 : Blo 1136633 2434097 := bstep (se 2 (by rfl) ⟨912786, by rfl⟩ : syracuseStep 2434097 = 1825573) B1825573
theorem B7283789 : Blo 1136633 7283789 := bstep (se 3 (by rfl) ⟨1365710, by rfl⟩ : syracuseStep 7283789 = 2731421) B2731421
theorem B2565233 : Blo 1136633 2565233 := bstep (se 2 (by rfl) ⟨961962, by rfl⟩ : syracuseStep 2565233 = 1923925) B1923925
theorem B2565251 : Blo 1136633 2565251 := bstep (se 1 (by rfl) ⟨1923938, by rfl⟩ : syracuseStep 2565251 = 3847877) B3847877
theorem B3843341 : Blo 1136633 3843341 := bstep (se 3 (by rfl) ⟨720626, by rfl⟩ : syracuseStep 3843341 = 1441253) B1441253
theorem B3843395 : Blo 1136633 3843395 := bstep (se 1 (by rfl) ⟨2882546, by rfl⟩ : syracuseStep 3843395 = 5765093) B5765093
theorem B5186929 : Blo 1136633 5186929 := bstep (se 2 (by rfl) ⟨1945098, by rfl⟩ : syracuseStep 5186929 = 3890197) B3890197
theorem B2565521 : Blo 1136633 2565521 := bstep (se 2 (by rfl) ⟨962070, by rfl⟩ : syracuseStep 2565521 = 1924141) B1924141
theorem B2565539 : Blo 1136633 2565539 := bstep (se 1 (by rfl) ⟨1924154, by rfl⟩ : syracuseStep 2565539 = 3848309) B3848309
theorem B1975841 : Blo 1136633 1975841 := bstep (se 2 (by rfl) ⟨740940, by rfl⟩ : syracuseStep 1975841 = 1481881) B1481881
theorem B2434627 : Blo 1136633 2434627 := bstep (se 1 (by rfl) ⟨1825970, by rfl⟩ : syracuseStep 2434627 = 3651941) B3651941
theorem B3843665 : Blo 1136633 3843665 := bstep (se 2 (by rfl) ⟨1441374, by rfl⟩ : syracuseStep 3843665 = 2882749) B2882749
theorem B6006413 : Blo 1136633 6006413 := bstep (se 3 (by rfl) ⟨1126202, by rfl⟩ : syracuseStep 6006413 = 2252405) B2252405
theorem B2565809 : Blo 1136633 2565809 := bstep (se 2 (by rfl) ⟨962178, by rfl⟩ : syracuseStep 2565809 = 1924357) B1924357
theorem B2565827 : Blo 1136633 2565827 := bstep (se 1 (by rfl) ⟨1924370, by rfl⟩ : syracuseStep 2565827 = 3848741) B3848741
theorem B2566097 : Blo 1136633 2566097 := bstep (se 2 (by rfl) ⟨962286, by rfl⟩ : syracuseStep 2566097 = 1924573) B1924573
theorem B2566115 : Blo 1136633 2566115 := bstep (se 1 (by rfl) ⟨1924586, by rfl⟩ : syracuseStep 2566115 = 3849173) B3849173
theorem B8661005 : Blo 1136633 8661005 := bstep (se 3 (by rfl) ⟨1623938, by rfl⟩ : syracuseStep 8661005 = 3247877) B3247877
theorem B3844205 : Blo 1136633 3844205 := bstep (se 3 (by rfl) ⟨720788, by rfl⟩ : syracuseStep 3844205 = 1441577) B1441577
theorem B3844259 : Blo 1136633 3844259 := bstep (se 1 (by rfl) ⟨2883194, by rfl⟩ : syracuseStep 3844259 = 5766389) B5766389
theorem B2566385 : Blo 1136633 2566385 := bstep (se 2 (by rfl) ⟨962394, by rfl⟩ : syracuseStep 2566385 = 1924789) B1924789
theorem B2566403 : Blo 1136633 2566403 := bstep (se 1 (by rfl) ⟨1924802, by rfl⟩ : syracuseStep 2566403 = 3849605) B3849605
theorem B3844529 : Blo 1136633 3844529 := bstep (se 2 (by rfl) ⟨1441698, by rfl⟩ : syracuseStep 3844529 = 2883397) B2883397
theorem B2533987 : Blo 1136633 2533987 := bstep (se 1 (by rfl) ⟨1900490, by rfl⟩ : syracuseStep 2533987 = 3800981) B3800981
theorem B4860593 : Blo 1136633 4860593 := bstep (se 2 (by rfl) ⟨1822722, by rfl⟩ : syracuseStep 4860593 = 3645445) B3645445
theorem B7908293 : Blo 1136633 7908293 := bstep (se 4 (by rfl) ⟨741402, by rfl⟩ : syracuseStep 7908293 = 1482805) B1482805
theorem B3845069 : Blo 1136633 3845069 := bstep (se 3 (by rfl) ⟨720950, by rfl⟩ : syracuseStep 3845069 = 1441901) B1441901
theorem B3845123 : Blo 1136633 3845123 := bstep (se 1 (by rfl) ⟨2883842, by rfl⟩ : syracuseStep 3845123 = 5767685) B5767685
theorem B2731171 : Blo 1136633 2731171 := bstep (se 1 (by rfl) ⟨2048378, by rfl⟩ : syracuseStep 2731171 = 4096757) B4096757
theorem B7023779 : Blo 1136633 7023779 := bstep (se 1 (by rfl) ⟨5267834, by rfl⟩ : syracuseStep 7023779 = 10535669) B10535669
theorem B2731267 : Blo 1136633 2731267 := bstep (se 1 (by rfl) ⟨2048450, by rfl⟩ : syracuseStep 2731267 = 4096901) B4096901
theorem B3845393 : Blo 1136633 3845393 := bstep (se 2 (by rfl) ⟨1442022, by rfl⟩ : syracuseStep 3845393 = 2884045) B2884045
theorem B6925637 : Blo 1136633 6925637 := bstep (se 4 (by rfl) ⟨649278, by rfl⟩ : syracuseStep 6925637 = 1298557) B1298557
theorem B3288451 : Blo 1136633 3288451 := bstep (se 1 (by rfl) ⟨2466338, by rfl⟩ : syracuseStep 3288451 = 4932677) B4932677
theorem B1846819 : Blo 1136633 1846819 := bstep (se 1 (by rfl) ⟨1385114, by rfl⟩ : syracuseStep 1846819 = 2770229) B2770229
theorem B9711373 : Blo 1136633 9711373 := bstep (se 3 (by rfl) ⟨1820882, by rfl⟩ : syracuseStep 9711373 = 3641765) B3641765
theorem B3845933 : Blo 1136633 3845933 := bstep (se 3 (by rfl) ⟨721112, by rfl⟩ : syracuseStep 3845933 = 1442225) B1442225
theorem B3845987 : Blo 1136633 3845987 := bstep (se 1 (by rfl) ⟨2884490, by rfl⟩ : syracuseStep 3845987 = 5768981) B5768981
theorem B1945523 : Blo 1136633 1945523 := bstep (se 1 (by rfl) ⟨1459142, by rfl⟩ : syracuseStep 1945523 = 2918285) B2918285
theorem B3846257 : Blo 1136633 3846257 := bstep (se 2 (by rfl) ⟨1442346, by rfl⟩ : syracuseStep 3846257 = 2884693) B2884693
theorem B2961731 : Blo 1136633 2961731 := bstep (se 1 (by rfl) ⟨2221298, by rfl⟩ : syracuseStep 2961731 = 4442597) B4442597
theorem B1618483 : Blo 1136633 1618483 := bstep (se 1 (by rfl) ⟨1213862, by rfl⟩ : syracuseStep 1618483 = 2427725) B2427725
theorem B3846797 : Blo 1136633 3846797 := bstep (se 3 (by rfl) ⟨721274, by rfl⟩ : syracuseStep 3846797 = 1442549) B1442549
theorem B14594741 : Blo 1136633 14594741 := bstep (se 5 (by rfl) ⟨684128, by rfl⟩ : syracuseStep 14594741 = 1368257) B1368257
theorem B3846851 : Blo 1136633 3846851 := bstep (se 1 (by rfl) ⟨2885138, by rfl⟩ : syracuseStep 3846851 = 5770277) B5770277
theorem B7484165 : Blo 1136633 7484165 := bstep (se 4 (by rfl) ⟨701640, by rfl⟩ : syracuseStep 7484165 = 1403281) B1403281
theorem B3847121 : Blo 1136633 3847121 := bstep (se 2 (by rfl) ⟨1442670, by rfl⟩ : syracuseStep 3847121 = 2885341) B2885341
theorem B29209571 : Blo 1136633 29209571 := bstep (se 1 (by rfl) ⟨21907178, by rfl⟩ : syracuseStep 29209571 = 43814357) B43814357
theorem B3650609 : Blo 1136633 3650609 := bstep (se 2 (by rfl) ⟨1368978, by rfl⟩ : syracuseStep 3650609 = 2737957) B2737957
theorem B9712709 : Blo 1136633 9712709 := bstep (se 4 (by rfl) ⟨910566, by rfl⟩ : syracuseStep 9712709 = 1821133) B1821133
theorem B1619041 : Blo 1136633 1619041 := bstep (se 2 (by rfl) ⟨607140, by rfl⟩ : syracuseStep 1619041 = 1214281) B1214281
theorem B1619075 : Blo 1136633 1619075 := bstep (se 1 (by rfl) ⟨1214306, by rfl⟩ : syracuseStep 1619075 = 2428613) B2428613
theorem B6239501 : Blo 1136633 6239501 := bstep (se 3 (by rfl) ⟨1169906, by rfl⟩ : syracuseStep 6239501 = 2339813) B2339813
theorem B2307409 : Blo 1136633 2307409 := bstep (se 2 (by rfl) ⟨865278, by rfl⟩ : syracuseStep 2307409 = 1730557) B1730557
theorem B3847661 : Blo 1136633 3847661 := bstep (se 3 (by rfl) ⟨721436, by rfl⟩ : syracuseStep 3847661 = 1442873) B1442873
theorem B3847715 : Blo 1136633 3847715 := bstep (se 1 (by rfl) ⟨2885786, by rfl⟩ : syracuseStep 3847715 = 5771573) B5771573
theorem B1619633 : Blo 1136633 1619633 := bstep (se 2 (by rfl) ⟨607362, by rfl⟩ : syracuseStep 1619633 = 1214725) B1214725
theorem B1619713 : Blo 1136633 1619713 := bstep (se 2 (by rfl) ⟨607392, by rfl⟩ : syracuseStep 1619713 = 1214785) B1214785
theorem B369407765 : Blo 1136633 369407765 := bstep (se 6 (by rfl) ⟨8657994, by rfl⟩ : syracuseStep 369407765 = 17315989) B17315989
theorem B3847985 : Blo 1136633 3847985 := bstep (se 2 (by rfl) ⟨1442994, by rfl⟩ : syracuseStep 3847985 = 2885989) B2885989
theorem B4110193 : Blo 1136633 4110193 := bstep (se 2 (by rfl) ⟨1541322, by rfl⟩ : syracuseStep 4110193 = 3082645) B3082645
theorem B6403981 : Blo 1136633 6403981 := bstep (se 3 (by rfl) ⟨1200746, by rfl⟩ : syracuseStep 6403981 = 2401493) B2401493
theorem B1947809 : Blo 1136633 1947809 := bstep (se 2 (by rfl) ⟨730428, by rfl⟩ : syracuseStep 1947809 = 1460857) B1460857
theorem B4864333 : Blo 1136633 4864333 := bstep (se 3 (by rfl) ⟨912062, by rfl⟩ : syracuseStep 4864333 = 1824125) B1824125
theorem B3848525 : Blo 1136633 3848525 := bstep (se 3 (by rfl) ⟨721598, by rfl⟩ : syracuseStep 3848525 = 1443197) B1443197
theorem B3848579 : Blo 1136633 3848579 := bstep (se 1 (by rfl) ⟨2886434, by rfl⟩ : syracuseStep 3848579 = 5772869) B5772869
theorem B8632817 : Blo 1136633 8632817 := bstep (se 2 (by rfl) ⟨3237306, by rfl⟩ : syracuseStep 8632817 = 6474613) B6474613
theorem B1620499 : Blo 1136633 1620499 := bstep (se 1 (by rfl) ⟨1215374, by rfl⟩ : syracuseStep 1620499 = 2430749) B2430749
theorem B7289477 : Blo 1136633 7289477 := bstep (se 4 (by rfl) ⟨683388, by rfl⟩ : syracuseStep 7289477 = 1366777) B1366777
theorem B16628365 : Blo 1136633 16628365 := bstep (se 3 (by rfl) ⟨3117818, by rfl⟩ : syracuseStep 16628365 = 6235637) B6235637
theorem B3848849 : Blo 1136633 3848849 := bstep (se 2 (by rfl) ⟨1443318, by rfl⟩ : syracuseStep 3848849 = 2886637) B2886637
theorem B1948465 : Blo 1136633 1948465 := bstep (se 2 (by rfl) ⟨730674, by rfl⟩ : syracuseStep 1948465 = 1461349) B1461349
theorem B1620977 : Blo 1136633 1620977 := bstep (se 2 (by rfl) ⟨607866, by rfl⟩ : syracuseStep 1620977 = 1215733) B1215733
theorem B56835125 : Blo 1136633 56835125 := bstep (se 5 (by rfl) ⟨2664146, by rfl⟩ : syracuseStep 56835125 = 5328293) B5328293
theorem B3652685 : Blo 1136633 3652685 := bstep (se 3 (by rfl) ⟨684878, by rfl⟩ : syracuseStep 3652685 = 1369757) B1369757
theorem B1621091 : Blo 1136633 1621091 := bstep (se 1 (by rfl) ⟨1215818, by rfl⟩ : syracuseStep 1621091 = 2431637) B2431637
theorem B3849389 : Blo 1136633 3849389 := bstep (se 3 (by rfl) ⟨721760, by rfl⟩ : syracuseStep 3849389 = 1443521) B1443521
theorem B1621171 : Blo 1136633 1621171 := bstep (se 1 (by rfl) ⟨1215878, by rfl⟩ : syracuseStep 1621171 = 2431757) B2431757
theorem B3849443 : Blo 1136633 3849443 := bstep (se 1 (by rfl) ⟨2887082, by rfl⟩ : syracuseStep 3849443 = 5774165) B5774165
theorem B9223409 : Blo 1136633 9223409 := bstep (se 2 (by rfl) ⟨3458778, by rfl⟩ : syracuseStep 9223409 = 6917557) B6917557
theorem B6929869 : Blo 1136633 6929869 := bstep (se 3 (by rfl) ⟨1299350, by rfl⟩ : syracuseStep 6929869 = 2598701) B2598701
theorem B1949395 : Blo 1136633 1949395 := bstep (se 1 (by rfl) ⟨1462046, by rfl⟩ : syracuseStep 1949395 = 2924093) B2924093
theorem B1621729 : Blo 1136633 1621729 := bstep (se 2 (by rfl) ⟨608148, by rfl⟩ : syracuseStep 1621729 = 1216297) B1216297
theorem B5193571 : Blo 1136633 5193571 := bstep (se 1 (by rfl) ⟨3895178, by rfl⟩ : syracuseStep 5193571 = 7790357) B7790357
theorem B3653581 : Blo 1136633 3653581 := bstep (se 3 (by rfl) ⟨685046, by rfl⟩ : syracuseStep 3653581 = 1370093) B1370093
theorem B1949779 : Blo 1136633 1949779 := bstep (se 1 (by rfl) ⟨1462334, by rfl⟩ : syracuseStep 1949779 = 2924669) B2924669
theorem B2769059 : Blo 1136633 2769059 := bstep (se 1 (by rfl) ⟨2076794, by rfl⟩ : syracuseStep 2769059 = 4153589) B4153589
theorem B1622435 : Blo 1136633 1622435 := bstep (se 1 (by rfl) ⟨1216826, by rfl⟩ : syracuseStep 1622435 = 2433653) B2433653
theorem B2048465 : Blo 1136633 2048465 := bstep (se 2 (by rfl) ⟨768174, by rfl⟩ : syracuseStep 2048465 = 1536349) B1536349
theorem B29573603 : Blo 1136633 29573603 := bstep (se 1 (by rfl) ⟨22180202, by rfl⟩ : syracuseStep 29573603 = 44360405) B44360405
theorem B8208965 : Blo 1136633 8208965 := bstep (se 4 (by rfl) ⟨769590, by rfl⟩ : syracuseStep 8208965 = 1539181) B1539181
theorem B2736803 : Blo 1136633 2736803 := bstep (se 1 (by rfl) ⟨2052602, by rfl⟩ : syracuseStep 2736803 = 4105205) B4105205
theorem B2737091 : Blo 1136633 2737091 := bstep (se 1 (by rfl) ⟨2052818, by rfl⟩ : syracuseStep 2737091 = 4105637) B4105637
theorem B1623073 : Blo 1136633 1623073 := bstep (se 2 (by rfl) ⟨608652, by rfl⟩ : syracuseStep 1623073 = 1217305) B1217305
theorem B1623187 : Blo 1136633 1623187 := bstep (se 1 (by rfl) ⟨1217390, by rfl⟩ : syracuseStep 1623187 = 2434781) B2434781
theorem B1918147 : Blo 1136633 1918147 := bstep (se 1 (by rfl) ⟨1438610, by rfl⟩ : syracuseStep 1918147 = 2877221) B2877221
theorem B16434485 : Blo 1136633 16434485 := bstep (se 5 (by rfl) ⟨770366, by rfl⟩ : syracuseStep 16434485 = 1540733) B1540733
theorem B1918289 : Blo 1136633 1918289 := bstep (se 2 (by rfl) ⟨719358, by rfl⟩ : syracuseStep 1918289 = 1438717) B1438717
theorem B3458477 : Blo 1136633 3458477 := bstep (se 3 (by rfl) ⟨648464, by rfl⟩ : syracuseStep 3458477 = 1296929) B1296929
theorem B1754561 : Blo 1136633 1754561 := bstep (se 2 (by rfl) ⟨657960, by rfl⟩ : syracuseStep 1754561 = 1315921) B1315921
theorem B1918417 : Blo 1136633 1918417 := bstep (se 2 (by rfl) ⟨719406, by rfl⟩ : syracuseStep 1918417 = 1438813) B1438813
theorem B3458513 : Blo 1136633 3458513 := bstep (se 2 (by rfl) ⟨1296942, by rfl⟩ : syracuseStep 3458513 = 2593885) B2593885
theorem B1918451 : Blo 1136633 1918451 := bstep (se 1 (by rfl) ⟨1438838, by rfl⟩ : syracuseStep 1918451 = 2877677) B2877677
theorem B1918579 : Blo 1136633 1918579 := bstep (se 1 (by rfl) ⟨1438934, by rfl⟩ : syracuseStep 1918579 = 2877869) B2877869
theorem B1918721 : Blo 1136633 1918721 := bstep (se 2 (by rfl) ⟨719520, by rfl⟩ : syracuseStep 1918721 = 1439041) B1439041
theorem B2737937 : Blo 1136633 2737937 := bstep (se 2 (by rfl) ⟨1026726, by rfl⟩ : syracuseStep 2737937 = 2053453) B2053453
theorem B1460035 : Blo 1136633 1460035 := bstep (se 1 (by rfl) ⟨1095026, by rfl⟩ : syracuseStep 1460035 = 2190053) B2190053
theorem B1918849 : Blo 1136633 1918849 := bstep (se 2 (by rfl) ⟨719568, by rfl⟩ : syracuseStep 1918849 = 1439137) B1439137
theorem B1918883 : Blo 1136633 1918883 := bstep (se 1 (by rfl) ⟨1439162, by rfl⟩ : syracuseStep 1918883 = 2878325) B2878325
theorem B9717731 : Blo 1136633 9717731 := bstep (se 1 (by rfl) ⟨7288298, by rfl⟩ : syracuseStep 9717731 = 14576597) B14576597
theorem B2050051 : Blo 1136633 2050051 := bstep (se 1 (by rfl) ⟨1537538, by rfl⟩ : syracuseStep 2050051 = 3075077) B3075077
theorem B1919011 : Blo 1136633 1919011 := bstep (se 1 (by rfl) ⟨1439258, by rfl⟩ : syracuseStep 1919011 = 2878517) B2878517
theorem B1820723 : Blo 1136633 1820723 := bstep (se 1 (by rfl) ⟨1365542, by rfl⟩ : syracuseStep 1820723 = 2731085) B2731085
theorem B1820755 : Blo 1136633 1820755 := bstep (se 1 (by rfl) ⟨1365566, by rfl⟩ : syracuseStep 1820755 = 2731133) B2731133
theorem B1919153 : Blo 1136633 1919153 := bstep (se 2 (by rfl) ⟨719682, by rfl⟩ : syracuseStep 1919153 = 1439365) B1439365
theorem B1919281 : Blo 1136633 1919281 := bstep (se 2 (by rfl) ⟨719730, by rfl⟩ : syracuseStep 1919281 = 1439461) B1439461
theorem B1919315 : Blo 1136633 1919315 := bstep (se 1 (by rfl) ⟨1439486, by rfl⟩ : syracuseStep 1919315 = 2878973) B2878973
theorem B1919443 : Blo 1136633 1919443 := bstep (se 1 (by rfl) ⟨1439582, by rfl⟩ : syracuseStep 1919443 = 2879165) B2879165
theorem B2738705 : Blo 1136633 2738705 := bstep (se 2 (by rfl) ⟨1027014, by rfl⟩ : syracuseStep 2738705 = 2054029) B2054029
theorem B4868657 : Blo 1136633 4868657 := bstep (se 2 (by rfl) ⟨1825746, by rfl⟩ : syracuseStep 4868657 = 3651493) B3651493
theorem B1919585 : Blo 1136633 1919585 := bstep (se 2 (by rfl) ⟨719844, by rfl⟩ : syracuseStep 1919585 = 1439689) B1439689
theorem B4868707 : Blo 1136633 4868707 := bstep (se 1 (by rfl) ⟨3651530, by rfl⟩ : syracuseStep 4868707 = 7303061) B7303061
theorem B2771651 : Blo 1136633 2771651 := bstep (se 1 (by rfl) ⟨2078738, by rfl⟩ : syracuseStep 2771651 = 4157477) B4157477
theorem B1919713 : Blo 1136633 1919713 := bstep (se 2 (by rfl) ⟨719892, by rfl⟩ : syracuseStep 1919713 = 1439785) B1439785
theorem B1919747 : Blo 1136633 1919747 := bstep (se 1 (by rfl) ⟨1439810, by rfl⟩ : syracuseStep 1919747 = 2879621) B2879621
theorem B1919875 : Blo 1136633 1919875 := bstep (se 1 (by rfl) ⟨1439906, by rfl⟩ : syracuseStep 1919875 = 2879813) B2879813
theorem B1821665 : Blo 1136633 1821665 := bstep (se 2 (by rfl) ⟨683124, by rfl⟩ : syracuseStep 1821665 = 1366249) B1366249
theorem B1920017 : Blo 1136633 1920017 := bstep (se 2 (by rfl) ⟨720006, by rfl⟩ : syracuseStep 1920017 = 1440013) B1440013
theorem B3329059 : Blo 1136633 3329059 := bstep (se 1 (by rfl) ⟨2496794, by rfl⟩ : syracuseStep 3329059 = 4993589) B4993589
theorem B1231939 : Blo 1136633 1231939 := bstep (se 1 (by rfl) ⟨923954, by rfl⟩ : syracuseStep 1231939 = 1847909) B1847909
theorem B1920145 : Blo 1136633 1920145 := bstep (se 2 (by rfl) ⟨720054, by rfl⟩ : syracuseStep 1920145 = 1440109) B1440109
theorem B1920179 : Blo 1136633 1920179 := bstep (se 1 (by rfl) ⟨1440134, by rfl⟩ : syracuseStep 1920179 = 2880269) B2880269
theorem B1920307 : Blo 1136633 1920307 := bstep (se 1 (by rfl) ⟨1440230, by rfl⟩ : syracuseStep 1920307 = 2880461) B2880461
theorem B1920449 : Blo 1136633 1920449 := bstep (se 2 (by rfl) ⟨720168, by rfl⟩ : syracuseStep 1920449 = 1440337) B1440337
theorem B11095523 : Blo 1136633 11095523 := bstep (se 1 (by rfl) ⟨8321642, by rfl⟩ : syracuseStep 11095523 = 16643285) B16643285
theorem B1297955 : Blo 1136633 1297955 := bstep (se 1 (by rfl) ⟨973466, by rfl⟩ : syracuseStep 1297955 = 1946933) B1946933
theorem B1920577 : Blo 1136633 1920577 := bstep (se 2 (by rfl) ⟨720216, by rfl⟩ : syracuseStep 1920577 = 1440433) B1440433
theorem B1920611 : Blo 1136633 1920611 := bstep (se 1 (by rfl) ⟨1440458, by rfl⟩ : syracuseStep 1920611 = 2880917) B2880917
theorem B14601869 : Blo 1136633 14601869 := bstep (se 3 (by rfl) ⟨2737850, by rfl⟩ : syracuseStep 14601869 = 5475701) B5475701
theorem B1920739 : Blo 1136633 1920739 := bstep (se 1 (by rfl) ⟨1440554, by rfl⟩ : syracuseStep 1920739 = 2881109) B2881109
theorem B1920881 : Blo 1136633 1920881 := bstep (se 2 (by rfl) ⟨720330, by rfl⟩ : syracuseStep 1920881 = 1440661) B1440661
theorem B1921009 : Blo 1136633 1921009 := bstep (se 2 (by rfl) ⟨720378, by rfl⟩ : syracuseStep 1921009 = 1440757) B1440757
theorem B1921043 : Blo 1136633 1921043 := bstep (se 1 (by rfl) ⟨1440782, by rfl⟩ : syracuseStep 1921043 = 2881565) B2881565
theorem B6475889 : Blo 1136633 6475889 := bstep (se 2 (by rfl) ⟨2428458, by rfl⟩ : syracuseStep 6475889 = 4856917) B4856917
theorem B1921171 : Blo 1136633 1921171 := bstep (se 1 (by rfl) ⟨1440878, by rfl⟩ : syracuseStep 1921171 = 2881757) B2881757
theorem B1822979 : Blo 1136633 1822979 := bstep (se 1 (by rfl) ⟨1367234, by rfl⟩ : syracuseStep 1822979 = 2734469) B2734469
theorem B1921313 : Blo 1136633 1921313 := bstep (se 2 (by rfl) ⟨720492, by rfl⟩ : syracuseStep 1921313 = 1440985) B1440985
theorem B1921441 : Blo 1136633 1921441 := bstep (se 2 (by rfl) ⟨720540, by rfl⟩ : syracuseStep 1921441 = 1441081) B1441081
theorem B1921475 : Blo 1136633 1921475 := bstep (se 1 (by rfl) ⟨1441106, by rfl⟩ : syracuseStep 1921475 = 2882213) B2882213
theorem B10932677 : Blo 1136633 10932677 := bstep (se 4 (by rfl) ⟨1024938, by rfl⟩ : syracuseStep 10932677 = 2049877) B2049877
theorem B3461699 : Blo 1136633 3461699 := bstep (se 1 (by rfl) ⟨2596274, by rfl⟩ : syracuseStep 3461699 = 5192549) B5192549
theorem B1921603 : Blo 1136633 1921603 := bstep (se 1 (by rfl) ⟨1441202, by rfl⟩ : syracuseStep 1921603 = 2882405) B2882405
theorem B11686513 : Blo 1136633 11686513 := bstep (se 2 (by rfl) ⟨4382442, by rfl⟩ : syracuseStep 11686513 = 8764885) B8764885
theorem B1921745 : Blo 1136633 1921745 := bstep (se 2 (by rfl) ⟨720654, by rfl⟩ : syracuseStep 1921745 = 1441309) B1441309
theorem B8213233 : Blo 1136633 8213233 := bstep (se 2 (by rfl) ⟨3079962, by rfl⟩ : syracuseStep 8213233 = 6159925) B6159925
theorem B5755697 : Blo 1136633 5755697 := bstep (se 2 (by rfl) ⟨2158386, by rfl⟩ : syracuseStep 5755697 = 4316773) B4316773
theorem B1921873 : Blo 1136633 1921873 := bstep (se 2 (by rfl) ⟨720702, by rfl⟩ : syracuseStep 1921873 = 1441405) B1441405
theorem B8213347 : Blo 1136633 8213347 := bstep (se 1 (by rfl) ⟨6160010, by rfl⟩ : syracuseStep 8213347 = 12320021) B12320021
theorem B1921907 : Blo 1136633 1921907 := bstep (se 1 (by rfl) ⟨1441430, by rfl⟩ : syracuseStep 1921907 = 2882861) B2882861
theorem B1823651 : Blo 1136633 1823651 := bstep (se 1 (by rfl) ⟨1367738, by rfl⟩ : syracuseStep 1823651 = 2735477) B2735477
theorem B4871117 : Blo 1136633 4871117 := bstep (se 3 (by rfl) ⟨913334, by rfl⟩ : syracuseStep 4871117 = 1826669) B1826669
theorem B1922035 : Blo 1136633 1922035 := bstep (se 1 (by rfl) ⟨1441526, by rfl⟩ : syracuseStep 1922035 = 2883053) B2883053
theorem B1922177 : Blo 1136633 1922177 := bstep (se 2 (by rfl) ⟨720816, by rfl⟩ : syracuseStep 1922177 = 1441633) B1441633
theorem B1823953 : Blo 1136633 1823953 := bstep (se 2 (by rfl) ⟨683982, by rfl⟩ : syracuseStep 1823953 = 1367965) B1367965
theorem B1922305 : Blo 1136633 1922305 := bstep (se 2 (by rfl) ⟨720864, by rfl⟩ : syracuseStep 1922305 = 1441729) B1441729
theorem B1922339 : Blo 1136633 1922339 := bstep (se 1 (by rfl) ⟨1441754, by rfl⟩ : syracuseStep 1922339 = 2883509) B2883509
theorem B1824163 : Blo 1136633 1824163 := bstep (se 1 (by rfl) ⟨1368122, by rfl⟩ : syracuseStep 1824163 = 2736245) B2736245
theorem B1922467 : Blo 1136633 1922467 := bstep (se 1 (by rfl) ⟨1441850, by rfl⟩ : syracuseStep 1922467 = 2883701) B2883701
theorem B1824209 : Blo 1136633 1824209 := bstep (se 2 (by rfl) ⟨684078, by rfl⟩ : syracuseStep 1824209 = 1368157) B1368157
theorem B6477347 : Blo 1136633 6477347 := bstep (se 1 (by rfl) ⟨4858010, by rfl⟩ : syracuseStep 6477347 = 9716021) B9716021
theorem B1922609 : Blo 1136633 1922609 := bstep (se 2 (by rfl) ⟨720978, by rfl⟩ : syracuseStep 1922609 = 1441957) B1441957
theorem B9721457 : Blo 1136633 9721457 := bstep (se 2 (by rfl) ⟨3645546, by rfl⟩ : syracuseStep 9721457 = 7291093) B7291093
theorem B1922737 : Blo 1136633 1922737 := bstep (se 2 (by rfl) ⟨721026, by rfl⟩ : syracuseStep 1922737 = 1442053) B1442053
theorem B1922771 : Blo 1136633 1922771 := bstep (se 1 (by rfl) ⟨1442078, by rfl⟩ : syracuseStep 1922771 = 2884157) B2884157
theorem B1922899 : Blo 1136633 1922899 := bstep (se 1 (by rfl) ⟨1442174, by rfl⟩ : syracuseStep 1922899 = 2884349) B2884349
theorem B16635845 : Blo 1136633 16635845 := bstep (se 4 (by rfl) ⟨1559610, by rfl⟩ : syracuseStep 16635845 = 3119221) B3119221
theorem B1923041 : Blo 1136633 1923041 := bstep (se 2 (by rfl) ⟨721140, by rfl⟩ : syracuseStep 1923041 = 1442281) B1442281
theorem B1136643 : Blo 1136633 1136643 := bstep (se 1 (by rfl) ⟨852482, by rfl⟩ : syracuseStep 1136643 = 1704965) B1704965
theorem B1136659 : Blo 1136633 1136659 := bstep (se 1 (by rfl) ⟨852494, by rfl⟩ : syracuseStep 1136659 = 1704989) B1704989
theorem B1136675 : Blo 1136633 1136675 := bstep (se 1 (by rfl) ⟨852506, by rfl⟩ : syracuseStep 1136675 = 1705013) B1705013
theorem B1136691 : Blo 1136633 1136691 := bstep (se 1 (by rfl) ⟨852518, by rfl⟩ : syracuseStep 1136691 = 1705037) B1705037
theorem B1136707 : Blo 1136633 1136707 := bstep (se 1 (by rfl) ⟨852530, by rfl⟩ : syracuseStep 1136707 = 1705061) B1705061
theorem B1136723 : Blo 1136633 1136723 := bstep (se 1 (by rfl) ⟨852542, by rfl⟩ : syracuseStep 1136723 = 1705085) B1705085
theorem B1923169 : Blo 1136633 1923169 := bstep (se 2 (by rfl) ⟨721188, by rfl⟩ : syracuseStep 1923169 = 1442377) B1442377
theorem B1136739 : Blo 1136633 1136739 := bstep (se 1 (by rfl) ⟨852554, by rfl⟩ : syracuseStep 1136739 = 1705109) B1705109
theorem B1136755 : Blo 1136633 1136755 := bstep (se 1 (by rfl) ⟨852566, by rfl⟩ : syracuseStep 1136755 = 1705133) B1705133
theorem B1136771 : Blo 1136633 1136771 := bstep (se 1 (by rfl) ⟨852578, by rfl⟩ : syracuseStep 1136771 = 1705157) B1705157
theorem B1923203 : Blo 1136633 1923203 := bstep (se 1 (by rfl) ⟨1442402, by rfl⟩ : syracuseStep 1923203 = 2884805) B2884805
theorem B1136787 : Blo 1136633 1136787 := bstep (se 1 (by rfl) ⟨852590, by rfl⟩ : syracuseStep 1136787 = 1705181) B1705181
theorem B1136803 : Blo 1136633 1136803 := bstep (se 1 (by rfl) ⟨852602, by rfl⟩ : syracuseStep 1136803 = 1705205) B1705205
theorem B1136819 : Blo 1136633 1136819 := bstep (se 1 (by rfl) ⟨852614, by rfl⟩ : syracuseStep 1136819 = 1705229) B1705229
theorem B1136835 : Blo 1136633 1136835 := bstep (se 1 (by rfl) ⟨852626, by rfl⟩ : syracuseStep 1136835 = 1705253) B1705253
theorem B1136851 : Blo 1136633 1136851 := bstep (se 1 (by rfl) ⟨852638, by rfl⟩ : syracuseStep 1136851 = 1705277) B1705277
theorem B1136867 : Blo 1136633 1136867 := bstep (se 1 (by rfl) ⟨852650, by rfl⟩ : syracuseStep 1136867 = 1705301) B1705301
theorem B5757155 : Blo 1136633 5757155 := bstep (se 1 (by rfl) ⟨4317866, by rfl⟩ : syracuseStep 5757155 = 8635733) B8635733
theorem B1136883 : Blo 1136633 1136883 := bstep (se 1 (by rfl) ⟨852662, by rfl⟩ : syracuseStep 1136883 = 1705325) B1705325
theorem B1136899 : Blo 1136633 1136899 := bstep (se 1 (by rfl) ⟨852674, by rfl⟩ : syracuseStep 1136899 = 1705349) B1705349
theorem B1923331 : Blo 1136633 1923331 := bstep (se 1 (by rfl) ⟨1442498, by rfl⟩ : syracuseStep 1923331 = 2884997) B2884997
theorem B1136915 : Blo 1136633 1136915 := bstep (se 1 (by rfl) ⟨852686, by rfl⟩ : syracuseStep 1136915 = 1705373) B1705373
theorem B1136931 : Blo 1136633 1136931 := bstep (se 1 (by rfl) ⟨852698, by rfl⟩ : syracuseStep 1136931 = 1705397) B1705397
theorem B1136947 : Blo 1136633 1136947 := bstep (se 1 (by rfl) ⟨852710, by rfl⟩ : syracuseStep 1136947 = 1705421) B1705421
theorem B1136963 : Blo 1136633 1136963 := bstep (se 1 (by rfl) ⟨852722, by rfl⟩ : syracuseStep 1136963 = 1705445) B1705445
theorem B1136979 : Blo 1136633 1136979 := bstep (se 1 (by rfl) ⟨852734, by rfl⟩ : syracuseStep 1136979 = 1705469) B1705469
theorem B1136995 : Blo 1136633 1136995 := bstep (se 1 (by rfl) ⟨852746, by rfl⟩ : syracuseStep 1136995 = 1705493) B1705493
theorem B1137011 : Blo 1136633 1137011 := bstep (se 1 (by rfl) ⟨852758, by rfl⟩ : syracuseStep 1137011 = 1705517) B1705517
theorem B1137027 : Blo 1136633 1137027 := bstep (se 1 (by rfl) ⟨852770, by rfl⟩ : syracuseStep 1137027 = 1705541) B1705541
theorem B1923473 : Blo 1136633 1923473 := bstep (se 2 (by rfl) ⟨721302, by rfl⟩ : syracuseStep 1923473 = 1442605) B1442605
theorem B1137043 : Blo 1136633 1137043 := bstep (se 1 (by rfl) ⟨852782, by rfl⟩ : syracuseStep 1137043 = 1705565) B1705565
theorem B1137059 : Blo 1136633 1137059 := bstep (se 1 (by rfl) ⟨852794, by rfl⟩ : syracuseStep 1137059 = 1705589) B1705589
theorem B1137075 : Blo 1136633 1137075 := bstep (se 1 (by rfl) ⟨852806, by rfl⟩ : syracuseStep 1137075 = 1705613) B1705613
theorem B1137091 : Blo 1136633 1137091 := bstep (se 1 (by rfl) ⟨852818, by rfl⟩ : syracuseStep 1137091 = 1705637) B1705637
theorem B1137107 : Blo 1136633 1137107 := bstep (se 1 (by rfl) ⟨852830, by rfl⟩ : syracuseStep 1137107 = 1705661) B1705661
theorem B1137123 : Blo 1136633 1137123 := bstep (se 1 (by rfl) ⟨852842, by rfl⟩ : syracuseStep 1137123 = 1705685) B1705685
theorem B1137139 : Blo 1136633 1137139 := bstep (se 1 (by rfl) ⟨852854, by rfl⟩ : syracuseStep 1137139 = 1705709) B1705709
theorem B1137155 : Blo 1136633 1137155 := bstep (se 1 (by rfl) ⟨852866, by rfl⟩ : syracuseStep 1137155 = 1705733) B1705733
theorem B1923601 : Blo 1136633 1923601 := bstep (se 2 (by rfl) ⟨721350, by rfl⟩ : syracuseStep 1923601 = 1442701) B1442701
theorem B1137171 : Blo 1136633 1137171 := bstep (se 1 (by rfl) ⟨852878, by rfl⟩ : syracuseStep 1137171 = 1705757) B1705757
theorem B1137187 : Blo 1136633 1137187 := bstep (se 1 (by rfl) ⟨852890, by rfl⟩ : syracuseStep 1137187 = 1705781) B1705781
theorem B1137203 : Blo 1136633 1137203 := bstep (se 1 (by rfl) ⟨852902, by rfl⟩ : syracuseStep 1137203 = 1705805) B1705805
theorem B1923635 : Blo 1136633 1923635 := bstep (se 1 (by rfl) ⟨1442726, by rfl⟩ : syracuseStep 1923635 = 2885453) B2885453
theorem B1137219 : Blo 1136633 1137219 := bstep (se 1 (by rfl) ⟨852914, by rfl⟩ : syracuseStep 1137219 = 1705829) B1705829
theorem B1137235 : Blo 1136633 1137235 := bstep (se 1 (by rfl) ⟨852926, by rfl⟩ : syracuseStep 1137235 = 1705853) B1705853
theorem B1137251 : Blo 1136633 1137251 := bstep (se 1 (by rfl) ⟨852938, by rfl⟩ : syracuseStep 1137251 = 1705877) B1705877
theorem B1137267 : Blo 1136633 1137267 := bstep (se 1 (by rfl) ⟨852950, by rfl⟩ : syracuseStep 1137267 = 1705901) B1705901
theorem B1137283 : Blo 1136633 1137283 := bstep (se 1 (by rfl) ⟨852962, by rfl⟩ : syracuseStep 1137283 = 1705925) B1705925
theorem B1137299 : Blo 1136633 1137299 := bstep (se 1 (by rfl) ⟨852974, by rfl⟩ : syracuseStep 1137299 = 1705949) B1705949
theorem B1137315 : Blo 1136633 1137315 := bstep (se 1 (by rfl) ⟨852986, by rfl⟩ : syracuseStep 1137315 = 1705973) B1705973
theorem B1137331 : Blo 1136633 1137331 := bstep (se 1 (by rfl) ⟨852998, by rfl⟩ : syracuseStep 1137331 = 1705997) B1705997
theorem B1923763 : Blo 1136633 1923763 := bstep (se 1 (by rfl) ⟨1442822, by rfl⟩ : syracuseStep 1923763 = 2885645) B2885645
theorem B1137347 : Blo 1136633 1137347 := bstep (se 1 (by rfl) ⟨853010, by rfl⟩ : syracuseStep 1137347 = 1706021) B1706021
theorem B1137363 : Blo 1136633 1137363 := bstep (se 1 (by rfl) ⟨853022, by rfl⟩ : syracuseStep 1137363 = 1706045) B1706045
theorem B1137379 : Blo 1136633 1137379 := bstep (se 1 (by rfl) ⟨853034, by rfl⟩ : syracuseStep 1137379 = 1706069) B1706069
theorem B1137395 : Blo 1136633 1137395 := bstep (se 1 (by rfl) ⟨853046, by rfl⟩ : syracuseStep 1137395 = 1706093) B1706093
theorem B1137411 : Blo 1136633 1137411 := bstep (se 1 (by rfl) ⟨853058, by rfl⟩ : syracuseStep 1137411 = 1706117) B1706117
theorem B1137427 : Blo 1136633 1137427 := bstep (se 1 (by rfl) ⟨853070, by rfl⟩ : syracuseStep 1137427 = 1706141) B1706141
theorem B1137443 : Blo 1136633 1137443 := bstep (se 1 (by rfl) ⟨853082, by rfl⟩ : syracuseStep 1137443 = 1706165) B1706165
theorem B1137459 : Blo 1136633 1137459 := bstep (se 1 (by rfl) ⟨853094, by rfl⟩ : syracuseStep 1137459 = 1706189) B1706189
theorem B1923905 : Blo 1136633 1923905 := bstep (se 2 (by rfl) ⟨721464, by rfl⟩ : syracuseStep 1923905 = 1442929) B1442929
theorem B1137475 : Blo 1136633 1137475 := bstep (se 1 (by rfl) ⟨853106, by rfl⟩ : syracuseStep 1137475 = 1706213) B1706213
theorem B1137491 : Blo 1136633 1137491 := bstep (se 1 (by rfl) ⟨853118, by rfl⟩ : syracuseStep 1137491 = 1706237) B1706237
theorem B1137507 : Blo 1136633 1137507 := bstep (se 1 (by rfl) ⟨853130, by rfl⟩ : syracuseStep 1137507 = 1706261) B1706261
theorem B1137523 : Blo 1136633 1137523 := bstep (se 1 (by rfl) ⟨853142, by rfl⟩ : syracuseStep 1137523 = 1706285) B1706285
theorem B1137539 : Blo 1136633 1137539 := bstep (se 1 (by rfl) ⟨853154, by rfl⟩ : syracuseStep 1137539 = 1706309) B1706309
theorem B1137555 : Blo 1136633 1137555 := bstep (se 1 (by rfl) ⟨853166, by rfl⟩ : syracuseStep 1137555 = 1706333) B1706333
theorem B1137571 : Blo 1136633 1137571 := bstep (se 1 (by rfl) ⟨853178, by rfl⟩ : syracuseStep 1137571 = 1706357) B1706357
theorem B1137587 : Blo 1136633 1137587 := bstep (se 1 (by rfl) ⟨853190, by rfl⟩ : syracuseStep 1137587 = 1706381) B1706381
theorem B1825715 : Blo 1136633 1825715 := bstep (se 1 (by rfl) ⟨1369286, by rfl⟩ : syracuseStep 1825715 = 2738573) B2738573
theorem B1924033 : Blo 1136633 1924033 := bstep (se 2 (by rfl) ⟨721512, by rfl⟩ : syracuseStep 1924033 = 1443025) B1443025
theorem B1137603 : Blo 1136633 1137603 := bstep (se 1 (by rfl) ⟨853202, by rfl⟩ : syracuseStep 1137603 = 1706405) B1706405
theorem B1137619 : Blo 1136633 1137619 := bstep (se 1 (by rfl) ⟨853214, by rfl⟩ : syracuseStep 1137619 = 1706429) B1706429
theorem B1137635 : Blo 1136633 1137635 := bstep (se 1 (by rfl) ⟨853226, by rfl⟩ : syracuseStep 1137635 = 1706453) B1706453
theorem B1924067 : Blo 1136633 1924067 := bstep (se 1 (by rfl) ⟨1443050, by rfl⟩ : syracuseStep 1924067 = 2886101) B2886101
theorem B1137651 : Blo 1136633 1137651 := bstep (se 1 (by rfl) ⟨853238, by rfl⟩ : syracuseStep 1137651 = 1706477) B1706477
theorem B1137667 : Blo 1136633 1137667 := bstep (se 1 (by rfl) ⟨853250, by rfl⟩ : syracuseStep 1137667 = 1706501) B1706501
theorem B5757965 : Blo 1136633 5757965 := bstep (se 3 (by rfl) ⟨1079618, by rfl⟩ : syracuseStep 5757965 = 2159237) B2159237
theorem B1137683 : Blo 1136633 1137683 := bstep (se 1 (by rfl) ⟨853262, by rfl⟩ : syracuseStep 1137683 = 1706525) B1706525
theorem B1137699 : Blo 1136633 1137699 := bstep (se 1 (by rfl) ⟨853274, by rfl⟩ : syracuseStep 1137699 = 1706549) B1706549
theorem B1137715 : Blo 1136633 1137715 := bstep (se 1 (by rfl) ⟨853286, by rfl⟩ : syracuseStep 1137715 = 1706573) B1706573
theorem B1137731 : Blo 1136633 1137731 := bstep (se 1 (by rfl) ⟨853298, by rfl⟩ : syracuseStep 1137731 = 1706597) B1706597
theorem B1137747 : Blo 1136633 1137747 := bstep (se 1 (by rfl) ⟨853310, by rfl⟩ : syracuseStep 1137747 = 1706621) B1706621
theorem B1367123 : Blo 1136633 1367123 := bstep (se 1 (by rfl) ⟨1025342, by rfl⟩ : syracuseStep 1367123 = 2050685) B2050685
theorem B1137763 : Blo 1136633 1137763 := bstep (se 1 (by rfl) ⟨853322, by rfl⟩ : syracuseStep 1137763 = 1706645) B1706645
theorem B1924195 : Blo 1136633 1924195 := bstep (se 1 (by rfl) ⟨1443146, by rfl⟩ : syracuseStep 1924195 = 2886293) B2886293
theorem B4316273 : Blo 1136633 4316273 := bstep (se 2 (by rfl) ⟨1618602, by rfl⟩ : syracuseStep 4316273 = 3237205) B3237205
theorem B1137779 : Blo 1136633 1137779 := bstep (se 1 (by rfl) ⟨853334, by rfl⟩ : syracuseStep 1137779 = 1706669) B1706669
theorem B1137795 : Blo 1136633 1137795 := bstep (se 1 (by rfl) ⟨853346, by rfl⟩ : syracuseStep 1137795 = 1706693) B1706693
theorem B1137811 : Blo 1136633 1137811 := bstep (se 1 (by rfl) ⟨853358, by rfl⟩ : syracuseStep 1137811 = 1706717) B1706717
theorem B1137827 : Blo 1136633 1137827 := bstep (se 1 (by rfl) ⟨853370, by rfl⟩ : syracuseStep 1137827 = 1706741) B1706741
theorem B1137843 : Blo 1136633 1137843 := bstep (se 1 (by rfl) ⟨853382, by rfl⟩ : syracuseStep 1137843 = 1706765) B1706765
theorem B1137859 : Blo 1136633 1137859 := bstep (se 1 (by rfl) ⟨853394, by rfl⟩ : syracuseStep 1137859 = 1706789) B1706789
theorem B1137875 : Blo 1136633 1137875 := bstep (se 1 (by rfl) ⟨853406, by rfl⟩ : syracuseStep 1137875 = 1706813) B1706813
theorem B1826003 : Blo 1136633 1826003 := bstep (se 1 (by rfl) ⟨1369502, by rfl⟩ : syracuseStep 1826003 = 2739005) B2739005
theorem B1137891 : Blo 1136633 1137891 := bstep (se 1 (by rfl) ⟨853418, by rfl⟩ : syracuseStep 1137891 = 1706837) B1706837
theorem B1924337 : Blo 1136633 1924337 := bstep (se 2 (by rfl) ⟨721626, by rfl⟩ : syracuseStep 1924337 = 1443253) B1443253
theorem B1137907 : Blo 1136633 1137907 := bstep (se 1 (by rfl) ⟨853430, by rfl⟩ : syracuseStep 1137907 = 1706861) B1706861
theorem B1137923 : Blo 1136633 1137923 := bstep (se 1 (by rfl) ⟨853442, by rfl⟩ : syracuseStep 1137923 = 1706885) B1706885
theorem B1137939 : Blo 1136633 1137939 := bstep (se 1 (by rfl) ⟨853454, by rfl⟩ : syracuseStep 1137939 = 1706909) B1706909
theorem B1137955 : Blo 1136633 1137955 := bstep (se 1 (by rfl) ⟨853466, by rfl⟩ : syracuseStep 1137955 = 1706933) B1706933
theorem B1137971 : Blo 1136633 1137971 := bstep (se 1 (by rfl) ⟨853478, by rfl⟩ : syracuseStep 1137971 = 1706957) B1706957
theorem B1137987 : Blo 1136633 1137987 := bstep (se 1 (by rfl) ⟨853490, by rfl⟩ : syracuseStep 1137987 = 1706981) B1706981
theorem B1138003 : Blo 1136633 1138003 := bstep (se 1 (by rfl) ⟨853502, by rfl⟩ : syracuseStep 1138003 = 1707005) B1707005
theorem B1138019 : Blo 1136633 1138019 := bstep (se 1 (by rfl) ⟨853514, by rfl⟩ : syracuseStep 1138019 = 1707029) B1707029
theorem B1924465 : Blo 1136633 1924465 := bstep (se 2 (by rfl) ⟨721674, by rfl⟩ : syracuseStep 1924465 = 1443349) B1443349
theorem B27745649 : Blo 1136633 27745649 := bstep (se 2 (by rfl) ⟨10404618, by rfl⟩ : syracuseStep 27745649 = 20809237) B20809237
theorem B1138035 : Blo 1136633 1138035 := bstep (se 1 (by rfl) ⟨853526, by rfl⟩ : syracuseStep 1138035 = 1707053) B1707053
theorem B1138051 : Blo 1136633 1138051 := bstep (se 1 (by rfl) ⟨853538, by rfl⟩ : syracuseStep 1138051 = 1707077) B1707077
theorem B1138067 : Blo 1136633 1138067 := bstep (se 1 (by rfl) ⟨853550, by rfl⟩ : syracuseStep 1138067 = 1707101) B1707101
theorem B1924499 : Blo 1136633 1924499 := bstep (se 1 (by rfl) ⟨1443374, by rfl⟩ : syracuseStep 1924499 = 2886749) B2886749
theorem B1138083 : Blo 1136633 1138083 := bstep (se 1 (by rfl) ⟨853562, by rfl⟩ : syracuseStep 1138083 = 1707125) B1707125
theorem B1138099 : Blo 1136633 1138099 := bstep (se 1 (by rfl) ⟨853574, by rfl⟩ : syracuseStep 1138099 = 1707149) B1707149
theorem B1138115 : Blo 1136633 1138115 := bstep (se 1 (by rfl) ⟨853586, by rfl⟩ : syracuseStep 1138115 = 1707173) B1707173
theorem B6151621 : Blo 1136633 6151621 := bstep (se 4 (by rfl) ⟨576714, by rfl⟩ : syracuseStep 6151621 = 1153429) B1153429
theorem B1138131 : Blo 1136633 1138131 := bstep (se 1 (by rfl) ⟨853598, by rfl⟩ : syracuseStep 1138131 = 1707197) B1707197
theorem B1138147 : Blo 1136633 1138147 := bstep (se 1 (by rfl) ⟨853610, by rfl⟩ : syracuseStep 1138147 = 1707221) B1707221
theorem B1138163 : Blo 1136633 1138163 := bstep (se 1 (by rfl) ⟨853622, by rfl⟩ : syracuseStep 1138163 = 1707245) B1707245
theorem B1138179 : Blo 1136633 1138179 := bstep (se 1 (by rfl) ⟨853634, by rfl⟩ : syracuseStep 1138179 = 1707269) B1707269
theorem B1138195 : Blo 1136633 1138195 := bstep (se 1 (by rfl) ⟨853646, by rfl⟩ : syracuseStep 1138195 = 1707293) B1707293
theorem B1924627 : Blo 1136633 1924627 := bstep (se 1 (by rfl) ⟨1443470, by rfl⟩ : syracuseStep 1924627 = 2886941) B2886941
theorem B1138211 : Blo 1136633 1138211 := bstep (se 1 (by rfl) ⟨853658, by rfl⟩ : syracuseStep 1138211 = 1707317) B1707317
theorem B1138227 : Blo 1136633 1138227 := bstep (se 1 (by rfl) ⟨853670, by rfl⟩ : syracuseStep 1138227 = 1707341) B1707341
theorem B1138243 : Blo 1136633 1138243 := bstep (se 1 (by rfl) ⟨853682, by rfl⟩ : syracuseStep 1138243 = 1707365) B1707365
theorem B1138259 : Blo 1136633 1138259 := bstep (se 1 (by rfl) ⟨853694, by rfl⟩ : syracuseStep 1138259 = 1707389) B1707389
theorem B1138275 : Blo 1136633 1138275 := bstep (se 1 (by rfl) ⟨853706, by rfl⟩ : syracuseStep 1138275 = 1707413) B1707413
theorem B20799089 : Blo 1136633 20799089 := bstep (se 2 (by rfl) ⟨7799658, by rfl⟩ : syracuseStep 20799089 = 15599317) B15599317
theorem B1138291 : Blo 1136633 1138291 := bstep (se 1 (by rfl) ⟨853718, by rfl⟩ : syracuseStep 1138291 = 1707437) B1707437
theorem B1138307 : Blo 1136633 1138307 := bstep (se 1 (by rfl) ⟨853730, by rfl⟩ : syracuseStep 1138307 = 1707461) B1707461
theorem B1138323 : Blo 1136633 1138323 := bstep (se 1 (by rfl) ⟨853742, by rfl⟩ : syracuseStep 1138323 = 1707485) B1707485
theorem B1924769 : Blo 1136633 1924769 := bstep (se 2 (by rfl) ⟨721788, by rfl⟩ : syracuseStep 1924769 = 1443577) B1443577
theorem B1138339 : Blo 1136633 1138339 := bstep (se 1 (by rfl) ⟨853754, by rfl⟩ : syracuseStep 1138339 = 1707509) B1707509
theorem B1138355 : Blo 1136633 1138355 := bstep (se 1 (by rfl) ⟨853766, by rfl⟩ : syracuseStep 1138355 = 1707533) B1707533
theorem B1138371 : Blo 1136633 1138371 := bstep (se 1 (by rfl) ⟨853778, by rfl⟩ : syracuseStep 1138371 = 1707557) B1707557
theorem B1138387 : Blo 1136633 1138387 := bstep (se 1 (by rfl) ⟨853790, by rfl⟩ : syracuseStep 1138387 = 1707581) B1707581
theorem B1138403 : Blo 1136633 1138403 := bstep (se 1 (by rfl) ⟨853802, by rfl⟩ : syracuseStep 1138403 = 1707605) B1707605
theorem B1138419 : Blo 1136633 1138419 := bstep (se 1 (by rfl) ⟨853814, by rfl⟩ : syracuseStep 1138419 = 1707629) B1707629
theorem B1138435 : Blo 1136633 1138435 := bstep (se 1 (by rfl) ⟨853826, by rfl⟩ : syracuseStep 1138435 = 1707653) B1707653
theorem B1138451 : Blo 1136633 1138451 := bstep (se 1 (by rfl) ⟨853838, by rfl⟩ : syracuseStep 1138451 = 1707677) B1707677
theorem B1138467 : Blo 1136633 1138467 := bstep (se 1 (by rfl) ⟨853850, by rfl⟩ : syracuseStep 1138467 = 1707701) B1707701
theorem B1138483 : Blo 1136633 1138483 := bstep (se 1 (by rfl) ⟨853862, by rfl⟩ : syracuseStep 1138483 = 1707725) B1707725
theorem B1138499 : Blo 1136633 1138499 := bstep (se 1 (by rfl) ⟨853874, by rfl⟩ : syracuseStep 1138499 = 1707749) B1707749
theorem B1138515 : Blo 1136633 1138515 := bstep (se 1 (by rfl) ⟨853886, by rfl⟩ : syracuseStep 1138515 = 1707773) B1707773
theorem B1138531 : Blo 1136633 1138531 := bstep (se 1 (by rfl) ⟨853898, by rfl⟩ : syracuseStep 1138531 = 1707797) B1707797
theorem B1138547 : Blo 1136633 1138547 := bstep (se 1 (by rfl) ⟨853910, by rfl⟩ : syracuseStep 1138547 = 1707821) B1707821
theorem B1138563 : Blo 1136633 1138563 := bstep (se 1 (by rfl) ⟨853922, by rfl⟩ : syracuseStep 1138563 = 1707845) B1707845
theorem B1138579 : Blo 1136633 1138579 := bstep (se 1 (by rfl) ⟨853934, by rfl⟩ : syracuseStep 1138579 = 1707869) B1707869
theorem B1138595 : Blo 1136633 1138595 := bstep (se 1 (by rfl) ⟨853946, by rfl⟩ : syracuseStep 1138595 = 1707893) B1707893
theorem B1138611 : Blo 1136633 1138611 := bstep (se 1 (by rfl) ⟨853958, by rfl⟩ : syracuseStep 1138611 = 1707917) B1707917
theorem B1138627 : Blo 1136633 1138627 := bstep (se 1 (by rfl) ⟨853970, by rfl⟩ : syracuseStep 1138627 = 1707941) B1707941
theorem B1138643 : Blo 1136633 1138643 := bstep (se 1 (by rfl) ⟨853982, by rfl⟩ : syracuseStep 1138643 = 1707965) B1707965
theorem B1138659 : Blo 1136633 1138659 := bstep (se 1 (by rfl) ⟨853994, by rfl⟩ : syracuseStep 1138659 = 1707989) B1707989
theorem B1138675 : Blo 1136633 1138675 := bstep (se 1 (by rfl) ⟨854006, by rfl⟩ : syracuseStep 1138675 = 1708013) B1708013
theorem B1826803 : Blo 1136633 1826803 := bstep (se 1 (by rfl) ⟨1370102, by rfl⟩ : syracuseStep 1826803 = 2740205) B2740205
theorem B1138691 : Blo 1136633 1138691 := bstep (se 1 (by rfl) ⟨854018, by rfl⟩ : syracuseStep 1138691 = 1708037) B1708037
theorem B2187281 : Blo 1136633 2187281 := bstep (se 2 (by rfl) ⟨820230, by rfl⟩ : syracuseStep 2187281 = 1640461) B1640461
theorem B1138707 : Blo 1136633 1138707 := bstep (se 1 (by rfl) ⟨854030, by rfl⟩ : syracuseStep 1138707 = 1708061) B1708061
theorem B1138723 : Blo 1136633 1138723 := bstep (se 1 (by rfl) ⟨854042, by rfl⟩ : syracuseStep 1138723 = 1708085) B1708085
theorem B1138739 : Blo 1136633 1138739 := bstep (se 1 (by rfl) ⟨854054, by rfl⟩ : syracuseStep 1138739 = 1708109) B1708109
theorem B14573621 : Blo 1136633 14573621 := bstep (se 5 (by rfl) ⟨683138, by rfl⟩ : syracuseStep 14573621 = 1366277) B1366277
theorem B1138755 : Blo 1136633 1138755 := bstep (se 1 (by rfl) ⟨854066, by rfl⟩ : syracuseStep 1138755 = 1708133) B1708133
theorem B1138771 : Blo 1136633 1138771 := bstep (se 1 (by rfl) ⟨854078, by rfl⟩ : syracuseStep 1138771 = 1708157) B1708157
theorem B1138787 : Blo 1136633 1138787 := bstep (se 1 (by rfl) ⟨854090, by rfl⟩ : syracuseStep 1138787 = 1708181) B1708181
theorem B1138803 : Blo 1136633 1138803 := bstep (se 1 (by rfl) ⟨854102, by rfl⟩ : syracuseStep 1138803 = 1708205) B1708205
theorem B1826945 : Blo 1136633 1826945 := bstep (se 2 (by rfl) ⟨685104, by rfl⟩ : syracuseStep 1826945 = 1370209) B1370209
theorem B1138819 : Blo 1136633 1138819 := bstep (se 1 (by rfl) ⟨854114, by rfl⟩ : syracuseStep 1138819 = 1708229) B1708229
theorem B1138835 : Blo 1136633 1138835 := bstep (se 1 (by rfl) ⟨854126, by rfl⟩ : syracuseStep 1138835 = 1708253) B1708253
theorem B1826977 : Blo 1136633 1826977 := bstep (se 2 (by rfl) ⟨685116, by rfl⟩ : syracuseStep 1826977 = 1370233) B1370233
theorem B1138851 : Blo 1136633 1138851 := bstep (se 1 (by rfl) ⟨854138, by rfl⟩ : syracuseStep 1138851 = 1708277) B1708277
theorem B1138867 : Blo 1136633 1138867 := bstep (se 1 (by rfl) ⟨854150, by rfl⟩ : syracuseStep 1138867 = 1708301) B1708301
theorem B1138883 : Blo 1136633 1138883 := bstep (se 1 (by rfl) ⟨854162, by rfl⟩ : syracuseStep 1138883 = 1708325) B1708325
theorem B1728721 : Blo 1136633 1728721 := bstep (se 2 (by rfl) ⟨648270, by rfl⟩ : syracuseStep 1728721 = 1296541) B1296541
theorem B1138899 : Blo 1136633 1138899 := bstep (se 1 (by rfl) ⟨854174, by rfl⟩ : syracuseStep 1138899 = 1708349) B1708349
theorem B1138915 : Blo 1136633 1138915 := bstep (se 1 (by rfl) ⟨854186, by rfl⟩ : syracuseStep 1138915 = 1708373) B1708373
theorem B1138931 : Blo 1136633 1138931 := bstep (se 1 (by rfl) ⟨854198, by rfl⟩ : syracuseStep 1138931 = 1708397) B1708397
theorem B1138947 : Blo 1136633 1138947 := bstep (se 1 (by rfl) ⟨854210, by rfl⟩ : syracuseStep 1138947 = 1708421) B1708421
theorem B1138963 : Blo 1136633 1138963 := bstep (se 1 (by rfl) ⟨854222, by rfl⟩ : syracuseStep 1138963 = 1708445) B1708445
theorem B1138979 : Blo 1136633 1138979 := bstep (se 1 (by rfl) ⟨854234, by rfl⟩ : syracuseStep 1138979 = 1708469) B1708469
theorem B1138995 : Blo 1136633 1138995 := bstep (se 1 (by rfl) ⟨854246, by rfl⟩ : syracuseStep 1138995 = 1708493) B1708493
theorem B1139011 : Blo 1136633 1139011 := bstep (se 1 (by rfl) ⟨854258, by rfl⟩ : syracuseStep 1139011 = 1708517) B1708517
theorem B1139027 : Blo 1136633 1139027 := bstep (se 1 (by rfl) ⟨854270, by rfl⟩ : syracuseStep 1139027 = 1708541) B1708541
theorem B12312931 : Blo 1136633 12312931 := bstep (se 1 (by rfl) ⟨9234698, by rfl⟩ : syracuseStep 12312931 = 18469397) B18469397
theorem B1139043 : Blo 1136633 1139043 := bstep (se 1 (by rfl) ⟨854282, by rfl⟩ : syracuseStep 1139043 = 1708565) B1708565
theorem B1139059 : Blo 1136633 1139059 := bstep (se 1 (by rfl) ⟨854294, by rfl⟩ : syracuseStep 1139059 = 1708589) B1708589
theorem B1139075 : Blo 1136633 1139075 := bstep (se 1 (by rfl) ⟨854306, by rfl⟩ : syracuseStep 1139075 = 1708613) B1708613
theorem B1139091 : Blo 1136633 1139091 := bstep (se 1 (by rfl) ⟨854318, by rfl⟩ : syracuseStep 1139091 = 1708637) B1708637
theorem B1139107 : Blo 1136633 1139107 := bstep (se 1 (by rfl) ⟨854330, by rfl⟩ : syracuseStep 1139107 = 1708661) B1708661
theorem B1139123 : Blo 1136633 1139123 := bstep (se 1 (by rfl) ⟨854342, by rfl⟩ : syracuseStep 1139123 = 1708685) B1708685
theorem B1139139 : Blo 1136633 1139139 := bstep (se 1 (by rfl) ⟨854354, by rfl⟩ : syracuseStep 1139139 = 1708709) B1708709
theorem B1139155 : Blo 1136633 1139155 := bstep (se 1 (by rfl) ⟨854366, by rfl⟩ : syracuseStep 1139155 = 1708733) B1708733
theorem B1139171 : Blo 1136633 1139171 := bstep (se 1 (by rfl) ⟨854378, by rfl⟩ : syracuseStep 1139171 = 1708757) B1708757
theorem B1139187 : Blo 1136633 1139187 := bstep (se 1 (by rfl) ⟨854390, by rfl⟩ : syracuseStep 1139187 = 1708781) B1708781
theorem B1139203 : Blo 1136633 1139203 := bstep (se 1 (by rfl) ⟨854402, by rfl⟩ : syracuseStep 1139203 = 1708805) B1708805
theorem B1139219 : Blo 1136633 1139219 := bstep (se 1 (by rfl) ⟨854414, by rfl⟩ : syracuseStep 1139219 = 1708829) B1708829
theorem B4317731 : Blo 1136633 4317731 := bstep (se 1 (by rfl) ⟨3238298, by rfl⟩ : syracuseStep 4317731 = 6476597) B6476597
theorem B1139235 : Blo 1136633 1139235 := bstep (se 1 (by rfl) ⟨854426, by rfl⟩ : syracuseStep 1139235 = 1708853) B1708853
theorem B4317745 : Blo 1136633 4317745 := bstep (se 2 (by rfl) ⟨1619154, by rfl⟩ : syracuseStep 4317745 = 3238309) B3238309
theorem B1139251 : Blo 1136633 1139251 := bstep (se 1 (by rfl) ⟨854438, by rfl⟩ : syracuseStep 1139251 = 1708877) B1708877
theorem B1139267 : Blo 1136633 1139267 := bstep (se 1 (by rfl) ⟨854450, by rfl⟩ : syracuseStep 1139267 = 1708901) B1708901
theorem B1139283 : Blo 1136633 1139283 := bstep (se 1 (by rfl) ⟨854462, by rfl⟩ : syracuseStep 1139283 = 1708925) B1708925
theorem B1139299 : Blo 1136633 1139299 := bstep (se 1 (by rfl) ⟨854474, by rfl⟩ : syracuseStep 1139299 = 1708949) B1708949
theorem B1139315 : Blo 1136633 1139315 := bstep (se 1 (by rfl) ⟨854486, by rfl⟩ : syracuseStep 1139315 = 1708973) B1708973
theorem B1139331 : Blo 1136633 1139331 := bstep (se 1 (by rfl) ⟨854498, by rfl⟩ : syracuseStep 1139331 = 1708997) B1708997
theorem B1729171 : Blo 1136633 1729171 := bstep (se 1 (by rfl) ⟨1296878, by rfl⟩ : syracuseStep 1729171 = 2593757) B2593757
theorem B1139347 : Blo 1136633 1139347 := bstep (se 1 (by rfl) ⟨854510, by rfl⟩ : syracuseStep 1139347 = 1709021) B1709021
theorem B1139363 : Blo 1136633 1139363 := bstep (se 1 (by rfl) ⟨854522, by rfl⟩ : syracuseStep 1139363 = 1709045) B1709045
theorem B1139379 : Blo 1136633 1139379 := bstep (se 1 (by rfl) ⟨854534, by rfl⟩ : syracuseStep 1139379 = 1709069) B1709069
theorem B1139395 : Blo 1136633 1139395 := bstep (se 1 (by rfl) ⟨854546, by rfl⟩ : syracuseStep 1139395 = 1709093) B1709093
theorem B1139411 : Blo 1136633 1139411 := bstep (se 1 (by rfl) ⟨854558, by rfl⟩ : syracuseStep 1139411 = 1709117) B1709117
theorem B1139427 : Blo 1136633 1139427 := bstep (se 1 (by rfl) ⟨854570, by rfl⟩ : syracuseStep 1139427 = 1709141) B1709141
theorem B1139443 : Blo 1136633 1139443 := bstep (se 1 (by rfl) ⟨854582, by rfl⟩ : syracuseStep 1139443 = 1709165) B1709165
theorem B1139459 : Blo 1136633 1139459 := bstep (se 1 (by rfl) ⟨854594, by rfl⟩ : syracuseStep 1139459 = 1709189) B1709189
theorem B1139475 : Blo 1136633 1139475 := bstep (se 1 (by rfl) ⟨854606, by rfl⟩ : syracuseStep 1139475 = 1709213) B1709213
theorem B1139491 : Blo 1136633 1139491 := bstep (se 1 (by rfl) ⟨854618, by rfl⟩ : syracuseStep 1139491 = 1709237) B1709237
theorem B1139507 : Blo 1136633 1139507 := bstep (se 1 (by rfl) ⟨854630, by rfl⟩ : syracuseStep 1139507 = 1709261) B1709261
theorem B1139523 : Blo 1136633 1139523 := bstep (se 1 (by rfl) ⟨854642, by rfl⟩ : syracuseStep 1139523 = 1709285) B1709285
theorem B1139539 : Blo 1136633 1139539 := bstep (se 1 (by rfl) ⟨854654, by rfl⟩ : syracuseStep 1139539 = 1709309) B1709309
theorem B1139555 : Blo 1136633 1139555 := bstep (se 1 (by rfl) ⟨854666, by rfl⟩ : syracuseStep 1139555 = 1709333) B1709333
theorem B1139571 : Blo 1136633 1139571 := bstep (se 1 (by rfl) ⟨854678, by rfl⟩ : syracuseStep 1139571 = 1709357) B1709357
theorem B1139587 : Blo 1136633 1139587 := bstep (se 1 (by rfl) ⟨854690, by rfl⟩ : syracuseStep 1139587 = 1709381) B1709381
theorem B1139603 : Blo 1136633 1139603 := bstep (se 1 (by rfl) ⟨854702, by rfl⟩ : syracuseStep 1139603 = 1709405) B1709405
theorem B1139619 : Blo 1136633 1139619 := bstep (se 1 (by rfl) ⟨854714, by rfl⟩ : syracuseStep 1139619 = 1709429) B1709429
theorem B1139635 : Blo 1136633 1139635 := bstep (se 1 (by rfl) ⟨854726, by rfl⟩ : syracuseStep 1139635 = 1709453) B1709453
theorem B1139651 : Blo 1136633 1139651 := bstep (se 1 (by rfl) ⟨854738, by rfl⟩ : syracuseStep 1139651 = 1709477) B1709477
theorem B1139667 : Blo 1136633 1139667 := bstep (se 1 (by rfl) ⟨854750, by rfl⟩ : syracuseStep 1139667 = 1709501) B1709501
theorem B1139683 : Blo 1136633 1139683 := bstep (se 1 (by rfl) ⟨854762, by rfl⟩ : syracuseStep 1139683 = 1709525) B1709525
theorem B1139699 : Blo 1136633 1139699 := bstep (se 1 (by rfl) ⟨854774, by rfl⟩ : syracuseStep 1139699 = 1709549) B1709549
theorem B1139715 : Blo 1136633 1139715 := bstep (se 1 (by rfl) ⟨854786, by rfl⟩ : syracuseStep 1139715 = 1709573) B1709573
theorem B1139731 : Blo 1136633 1139731 := bstep (se 1 (by rfl) ⟨854798, by rfl⟩ : syracuseStep 1139731 = 1709597) B1709597
theorem B1139747 : Blo 1136633 1139747 := bstep (se 1 (by rfl) ⟨854810, by rfl⟩ : syracuseStep 1139747 = 1709621) B1709621
theorem B1139763 : Blo 1136633 1139763 := bstep (se 1 (by rfl) ⟨854822, by rfl⟩ : syracuseStep 1139763 = 1709645) B1709645
theorem B1139779 : Blo 1136633 1139779 := bstep (se 1 (by rfl) ⟨854834, by rfl⟩ : syracuseStep 1139779 = 1709669) B1709669
theorem B1139795 : Blo 1136633 1139795 := bstep (se 1 (by rfl) ⟨854846, by rfl⟩ : syracuseStep 1139795 = 1709693) B1709693
theorem B1139811 : Blo 1136633 1139811 := bstep (se 1 (by rfl) ⟨854858, by rfl⟩ : syracuseStep 1139811 = 1709717) B1709717
theorem B1139827 : Blo 1136633 1139827 := bstep (se 1 (by rfl) ⟨854870, by rfl⟩ : syracuseStep 1139827 = 1709741) B1709741
theorem B1139843 : Blo 1136633 1139843 := bstep (se 1 (by rfl) ⟨854882, by rfl⟩ : syracuseStep 1139843 = 1709765) B1709765
theorem B26338445 : Blo 1136633 26338445 := bstep (se 3 (by rfl) ⟨4938458, by rfl⟩ : syracuseStep 26338445 = 9876917) B9876917
theorem B1139859 : Blo 1136633 1139859 := bstep (se 1 (by rfl) ⟨854894, by rfl⟩ : syracuseStep 1139859 = 1709789) B1709789
theorem B1139875 : Blo 1136633 1139875 := bstep (se 1 (by rfl) ⟨854906, by rfl⟩ : syracuseStep 1139875 = 1709813) B1709813
theorem B1139891 : Blo 1136633 1139891 := bstep (se 1 (by rfl) ⟨854918, by rfl⟩ : syracuseStep 1139891 = 1709837) B1709837
theorem B1139907 : Blo 1136633 1139907 := bstep (se 1 (by rfl) ⟨854930, by rfl⟩ : syracuseStep 1139907 = 1709861) B1709861
theorem B1139923 : Blo 1136633 1139923 := bstep (se 1 (by rfl) ⟨854942, by rfl⟩ : syracuseStep 1139923 = 1709885) B1709885
theorem B1139939 : Blo 1136633 1139939 := bstep (se 1 (by rfl) ⟨854954, by rfl⟩ : syracuseStep 1139939 = 1709909) B1709909
theorem B1139955 : Blo 1136633 1139955 := bstep (se 1 (by rfl) ⟨854966, by rfl⟩ : syracuseStep 1139955 = 1709933) B1709933
theorem B1139971 : Blo 1136633 1139971 := bstep (se 1 (by rfl) ⟨854978, by rfl⟩ : syracuseStep 1139971 = 1709957) B1709957
theorem B1139987 : Blo 1136633 1139987 := bstep (se 1 (by rfl) ⟨854990, by rfl⟩ : syracuseStep 1139987 = 1709981) B1709981
theorem B1140003 : Blo 1136633 1140003 := bstep (se 1 (by rfl) ⟨855002, by rfl⟩ : syracuseStep 1140003 = 1710005) B1710005
theorem B1140019 : Blo 1136633 1140019 := bstep (se 1 (by rfl) ⟨855014, by rfl⟩ : syracuseStep 1140019 = 1710029) B1710029
theorem B1140035 : Blo 1136633 1140035 := bstep (se 1 (by rfl) ⟨855026, by rfl⟩ : syracuseStep 1140035 = 1710053) B1710053
theorem B1140051 : Blo 1136633 1140051 := bstep (se 1 (by rfl) ⟨855038, by rfl⟩ : syracuseStep 1140051 = 1710077) B1710077
theorem B1140067 : Blo 1136633 1140067 := bstep (se 1 (by rfl) ⟨855050, by rfl⟩ : syracuseStep 1140067 = 1710101) B1710101
theorem B1140083 : Blo 1136633 1140083 := bstep (se 1 (by rfl) ⟨855062, by rfl⟩ : syracuseStep 1140083 = 1710125) B1710125
theorem B1140099 : Blo 1136633 1140099 := bstep (se 1 (by rfl) ⟨855074, by rfl⟩ : syracuseStep 1140099 = 1710149) B1710149
theorem B1140115 : Blo 1136633 1140115 := bstep (se 1 (by rfl) ⟨855086, by rfl⟩ : syracuseStep 1140115 = 1710173) B1710173
theorem B1140131 : Blo 1136633 1140131 := bstep (se 1 (by rfl) ⟨855098, by rfl⟩ : syracuseStep 1140131 = 1710197) B1710197
theorem B1140147 : Blo 1136633 1140147 := bstep (se 1 (by rfl) ⟨855110, by rfl⟩ : syracuseStep 1140147 = 1710221) B1710221
theorem B1140163 : Blo 1136633 1140163 := bstep (se 1 (by rfl) ⟨855122, by rfl⟩ : syracuseStep 1140163 = 1710245) B1710245
theorem B1140179 : Blo 1136633 1140179 := bstep (se 1 (by rfl) ⟨855134, by rfl⟩ : syracuseStep 1140179 = 1710269) B1710269
theorem B1140195 : Blo 1136633 1140195 := bstep (se 1 (by rfl) ⟨855146, by rfl⟩ : syracuseStep 1140195 = 1710293) B1710293
theorem B1730035 : Blo 1136633 1730035 := bstep (se 1 (by rfl) ⟨1297526, by rfl⟩ : syracuseStep 1730035 = 2595053) B2595053
theorem B1140211 : Blo 1136633 1140211 := bstep (se 1 (by rfl) ⟨855158, by rfl⟩ : syracuseStep 1140211 = 1710317) B1710317
theorem B1140227 : Blo 1136633 1140227 := bstep (se 1 (by rfl) ⟨855170, by rfl⟩ : syracuseStep 1140227 = 1710341) B1710341
theorem B9725453 : Blo 1136633 9725453 := bstep (se 3 (by rfl) ⟨1823522, by rfl⟩ : syracuseStep 9725453 = 3647045) B3647045
theorem B1140243 : Blo 1136633 1140243 := bstep (se 1 (by rfl) ⟨855182, by rfl⟩ : syracuseStep 1140243 = 1710365) B1710365
theorem B7792163 : Blo 1136633 7792163 := bstep (se 1 (by rfl) ⟨5844122, by rfl⟩ : syracuseStep 7792163 = 11688245) B11688245
theorem B1140259 : Blo 1136633 1140259 := bstep (se 1 (by rfl) ⟨855194, by rfl⟩ : syracuseStep 1140259 = 1710389) B1710389
theorem B3237421 : Blo 1136633 3237421 := bstep (se 3 (by rfl) ⟨607016, by rfl⟩ : syracuseStep 3237421 = 1214033) B1214033
theorem B1140275 : Blo 1136633 1140275 := bstep (se 1 (by rfl) ⟨855206, by rfl⟩ : syracuseStep 1140275 = 1710413) B1710413
theorem B1140291 : Blo 1136633 1140291 := bstep (se 1 (by rfl) ⟨855218, by rfl⟩ : syracuseStep 1140291 = 1710437) B1710437
theorem B1140307 : Blo 1136633 1140307 := bstep (se 1 (by rfl) ⟨855230, by rfl⟩ : syracuseStep 1140307 = 1710461) B1710461
theorem B1140323 : Blo 1136633 1140323 := bstep (se 1 (by rfl) ⟨855242, by rfl⟩ : syracuseStep 1140323 = 1710485) B1710485
theorem B1140339 : Blo 1136633 1140339 := bstep (se 1 (by rfl) ⟨855254, by rfl⟩ : syracuseStep 1140339 = 1710509) B1710509
theorem B1140355 : Blo 1136633 1140355 := bstep (se 1 (by rfl) ⟨855266, by rfl⟩ : syracuseStep 1140355 = 1710533) B1710533
theorem B1140371 : Blo 1136633 1140371 := bstep (se 1 (by rfl) ⟨855278, by rfl⟩ : syracuseStep 1140371 = 1710557) B1710557
theorem B1140387 : Blo 1136633 1140387 := bstep (se 1 (by rfl) ⟨855290, by rfl⟩ : syracuseStep 1140387 = 1710581) B1710581
theorem B1140403 : Blo 1136633 1140403 := bstep (se 1 (by rfl) ⟨855302, by rfl⟩ : syracuseStep 1140403 = 1710605) B1710605
theorem B1369795 : Blo 1136633 1369795 := bstep (se 1 (by rfl) ⟨1027346, by rfl⟩ : syracuseStep 1369795 = 2054693) B2054693
theorem B1140419 : Blo 1136633 1140419 := bstep (se 1 (by rfl) ⟨855314, by rfl⟩ : syracuseStep 1140419 = 1710629) B1710629
theorem B1140435 : Blo 1136633 1140435 := bstep (se 1 (by rfl) ⟨855326, by rfl⟩ : syracuseStep 1140435 = 1710653) B1710653
theorem B1140451 : Blo 1136633 1140451 := bstep (se 1 (by rfl) ⟨855338, by rfl⟩ : syracuseStep 1140451 = 1710677) B1710677
theorem B1140467 : Blo 1136633 1140467 := bstep (se 1 (by rfl) ⟨855350, by rfl⟩ : syracuseStep 1140467 = 1710701) B1710701
theorem B1140483 : Blo 1136633 1140483 := bstep (se 1 (by rfl) ⟨855362, by rfl⟩ : syracuseStep 1140483 = 1710725) B1710725
theorem B1140499 : Blo 1136633 1140499 := bstep (se 1 (by rfl) ⟨855374, by rfl⟩ : syracuseStep 1140499 = 1710749) B1710749
theorem B1140515 : Blo 1136633 1140515 := bstep (se 1 (by rfl) ⟨855386, by rfl⟩ : syracuseStep 1140515 = 1710773) B1710773
theorem B1140531 : Blo 1136633 1140531 := bstep (se 1 (by rfl) ⟨855398, by rfl⟩ : syracuseStep 1140531 = 1710797) B1710797
theorem B1140547 : Blo 1136633 1140547 := bstep (se 1 (by rfl) ⟨855410, by rfl⟩ : syracuseStep 1140547 = 1710821) B1710821
theorem B1140563 : Blo 1136633 1140563 := bstep (se 1 (by rfl) ⟨855422, by rfl⟩ : syracuseStep 1140563 = 1710845) B1710845
theorem B1140579 : Blo 1136633 1140579 := bstep (se 1 (by rfl) ⟨855434, by rfl⟩ : syracuseStep 1140579 = 1710869) B1710869
theorem B5760881 : Blo 1136633 5760881 := bstep (se 2 (by rfl) ⟨2160330, by rfl⟩ : syracuseStep 5760881 = 4320661) B4320661
theorem B13854577 : Blo 1136633 13854577 := bstep (se 2 (by rfl) ⟨5195466, by rfl⟩ : syracuseStep 13854577 = 10390933) B10390933
theorem B1140595 : Blo 1136633 1140595 := bstep (se 1 (by rfl) ⟨855446, by rfl⟩ : syracuseStep 1140595 = 1710893) B1710893
theorem B1140611 : Blo 1136633 1140611 := bstep (se 1 (by rfl) ⟨855458, by rfl⟩ : syracuseStep 1140611 = 1710917) B1710917
theorem B1140627 : Blo 1136633 1140627 := bstep (se 1 (by rfl) ⟨855470, by rfl⟩ : syracuseStep 1140627 = 1710941) B1710941
theorem B2189251 : Blo 1136633 2189251 := bstep (se 1 (by rfl) ⟨1641938, by rfl⟩ : syracuseStep 2189251 = 3283877) B3283877
theorem B4319203 : Blo 1136633 4319203 := bstep (se 1 (by rfl) ⟨3239402, by rfl⟩ : syracuseStep 4319203 = 6478805) B6478805
theorem B3336643 : Blo 1136633 3336643 := bstep (se 1 (by rfl) ⟨2502482, by rfl⟩ : syracuseStep 3336643 = 5004965) B5004965
theorem B7301573 : Blo 1136633 7301573 := bstep (se 4 (by rfl) ⟨684522, by rfl⟩ : syracuseStep 7301573 = 1369045) B1369045
theorem B4614691 : Blo 1136633 4614691 := bstep (se 1 (by rfl) ⟨3461018, by rfl⟩ : syracuseStep 4614691 = 6922037) B6922037
theorem B2878001 : Blo 1136633 2878001 := bstep (se 2 (by rfl) ⟨1079250, by rfl⟩ : syracuseStep 2878001 = 2158501) B2158501
theorem B3238481 : Blo 1136633 3238481 := bstep (se 2 (by rfl) ⟨1214430, by rfl⟩ : syracuseStep 3238481 = 2428861) B2428861
theorem B2878051 : Blo 1136633 2878051 := bstep (se 1 (by rfl) ⟨2158538, by rfl⟩ : syracuseStep 2878051 = 4317077) B4317077
theorem B2878193 : Blo 1136633 2878193 := bstep (se 2 (by rfl) ⟨1079322, by rfl⟩ : syracuseStep 2878193 = 2158645) B2158645
theorem B1731379 : Blo 1136633 1731379 := bstep (se 1 (by rfl) ⟨1298534, by rfl⟩ : syracuseStep 1731379 = 2597069) B2597069
theorem B3074989 : Blo 1136633 3074989 := bstep (se 3 (by rfl) ⟨576560, by rfl⟩ : syracuseStep 3074989 = 1153121) B1153121
theorem B2190545 : Blo 1136633 2190545 := bstep (se 2 (by rfl) ⟨821454, by rfl⟩ : syracuseStep 2190545 = 1642909) B1642909
theorem B3239153 : Blo 1136633 3239153 := bstep (se 2 (by rfl) ⟨1214682, by rfl⟩ : syracuseStep 3239153 = 2429365) B2429365
theorem B5762339 : Blo 1136633 5762339 := bstep (se 1 (by rfl) ⟨4321754, by rfl⟩ : syracuseStep 5762339 = 8643509) B8643509
theorem B2879185 : Blo 1136633 2879185 := bstep (se 2 (by rfl) ⟨1079694, by rfl⟩ : syracuseStep 2879185 = 2159389) B2159389
theorem B2158417 : Blo 1136633 2158417 := bstep (se 2 (by rfl) ⟨809406, by rfl⟩ : syracuseStep 2158417 = 1618813) B1618813
theorem B3075985 : Blo 1136633 3075985 := bstep (se 2 (by rfl) ⟨1153494, by rfl⟩ : syracuseStep 3075985 = 2306989) B2306989
theorem B2879459 : Blo 1136633 2879459 := bstep (se 1 (by rfl) ⟨2159594, by rfl⟩ : syracuseStep 2879459 = 4319189) B4319189
theorem B3239939 : Blo 1136633 3239939 := bstep (se 1 (by rfl) ⟨2429954, by rfl⟩ : syracuseStep 3239939 = 4859909) B4859909
theorem B5763149 : Blo 1136633 5763149 := bstep (se 3 (by rfl) ⟨1080590, by rfl⟩ : syracuseStep 5763149 = 2161181) B2161181
theorem B6582349 : Blo 1136633 6582349 := bstep (se 3 (by rfl) ⟨1234190, by rfl⟩ : syracuseStep 6582349 = 2468381) B2468381
theorem B4321421 : Blo 1136633 4321421 := bstep (se 3 (by rfl) ⟨810266, by rfl⟩ : syracuseStep 4321421 = 1620533) B1620533
theorem B2879651 : Blo 1136633 2879651 := bstep (se 1 (by rfl) ⟨2159738, by rfl⟩ : syracuseStep 2879651 = 4319477) B4319477
theorem B1536193 : Blo 1136633 1536193 := bstep (se 2 (by rfl) ⟨576072, by rfl⟩ : syracuseStep 1536193 = 1152145) B1152145
theorem B1536241 : Blo 1136633 1536241 := bstep (se 2 (by rfl) ⟨576090, by rfl⟩ : syracuseStep 1536241 = 1152181) B1152181
theorem B3240269 : Blo 1136633 3240269 := bstep (se 3 (by rfl) ⟨607550, by rfl⟩ : syracuseStep 3240269 = 1215101) B1215101
theorem B3240337 : Blo 1136633 3240337 := bstep (se 2 (by rfl) ⟨1215126, by rfl⟩ : syracuseStep 3240337 = 2430253) B2430253
theorem B3240611 : Blo 1136633 3240611 := bstep (se 1 (by rfl) ⟨2430458, by rfl⟩ : syracuseStep 3240611 = 4860917) B4860917
theorem B7402211 : Blo 1136633 7402211 := bstep (se 1 (by rfl) ⟨5551658, by rfl⟩ : syracuseStep 7402211 = 11103317) B11103317
theorem B1733393 : Blo 1136633 1733393 := bstep (se 2 (by rfl) ⟨650022, by rfl⟩ : syracuseStep 1733393 = 1300045) B1300045
theorem B2159473 : Blo 1136633 2159473 := bstep (se 2 (by rfl) ⟨809802, by rfl⟩ : syracuseStep 2159473 = 1619605) B1619605
theorem B7894093 : Blo 1136633 7894093 := bstep (se 3 (by rfl) ⟨1480142, by rfl⟩ : syracuseStep 7894093 = 2960285) B2960285
theorem B2880593 : Blo 1136633 2880593 := bstep (se 2 (by rfl) ⟨1080222, by rfl⟩ : syracuseStep 2880593 = 2160445) B2160445
theorem B2880643 : Blo 1136633 2880643 := bstep (se 1 (by rfl) ⟨2160482, by rfl⟩ : syracuseStep 2880643 = 4320965) B4320965
theorem B12973283 : Blo 1136633 12973283 := bstep (se 1 (by rfl) ⟨9729962, by rfl⟩ : syracuseStep 12973283 = 19459925) B19459925
theorem B2159875 : Blo 1136633 2159875 := bstep (se 1 (by rfl) ⟨1619906, by rfl⟩ : syracuseStep 2159875 = 3239813) B3239813
theorem B2880785 : Blo 1136633 2880785 := bstep (se 2 (by rfl) ⟨1080294, by rfl⟩ : syracuseStep 2880785 = 2160589) B2160589
theorem B2159921 : Blo 1136633 2159921 := bstep (se 2 (by rfl) ⟨809970, by rfl⟩ : syracuseStep 2159921 = 1619941) B1619941
theorem B3077489 : Blo 1136633 3077489 := bstep (se 2 (by rfl) ⟨1154058, by rfl⟩ : syracuseStep 3077489 = 2308117) B2308117
theorem B3077585 : Blo 1136633 3077585 := bstep (se 2 (by rfl) ⟨1154094, by rfl⟩ : syracuseStep 3077585 = 2308189) B2308189
theorem B1439203 : Blo 1136633 1439203 := bstep (se 1 (by rfl) ⟨1079402, by rfl⟩ : syracuseStep 1439203 = 2158805) B2158805
theorem B3241453 : Blo 1136633 3241453 := bstep (se 3 (by rfl) ⟨607772, by rfl⟩ : syracuseStep 3241453 = 1215545) B1215545
theorem B1439299 : Blo 1136633 1439299 := bstep (se 1 (by rfl) ⟨1079474, by rfl⟩ : syracuseStep 1439299 = 2158949) B2158949
theorem B4617805 : Blo 1136633 4617805 := bstep (se 3 (by rfl) ⟨865838, by rfl⟩ : syracuseStep 4617805 = 1731677) B1731677
theorem B2160209 : Blo 1136633 2160209 := bstep (se 2 (by rfl) ⟨810078, by rfl⟩ : syracuseStep 2160209 = 1620157) B1620157
theorem B3241613 : Blo 1136633 3241613 := bstep (se 3 (by rfl) ⟨607802, by rfl⟩ : syracuseStep 3241613 = 1215605) B1215605
theorem B3241795 : Blo 1136633 3241795 := bstep (se 1 (by rfl) ⟨2431346, by rfl⟩ : syracuseStep 3241795 = 4862693) B4862693
theorem B7305059 : Blo 1136633 7305059 := bstep (se 1 (by rfl) ⟨5478794, by rfl⟩ : syracuseStep 7305059 = 10957589) B10957589
theorem B4388849 : Blo 1136633 4388849 := bstep (se 2 (by rfl) ⟨1645818, by rfl⟩ : syracuseStep 4388849 = 3291637) B3291637
theorem B1439795 : Blo 1136633 1439795 := bstep (se 1 (by rfl) ⟨1079846, by rfl⟩ : syracuseStep 1439795 = 2159693) B2159693
theorem B2881777 : Blo 1136633 2881777 := bstep (se 2 (by rfl) ⟨1080666, by rfl⟩ : syracuseStep 2881777 = 2161333) B2161333
theorem B6486277 : Blo 1136633 6486277 := bstep (se 4 (by rfl) ⟨608088, by rfl⟩ : syracuseStep 6486277 = 1216177) B1216177
theorem B2160931 : Blo 1136633 2160931 := bstep (se 1 (by rfl) ⟨1620698, by rfl⟩ : syracuseStep 2160931 = 3241397) B3241397
theorem B2193809 : Blo 1136633 2193809 := bstep (se 2 (by rfl) ⟨822678, by rfl⟩ : syracuseStep 2193809 = 1645357) B1645357
theorem B2882051 : Blo 1136633 2882051 := bstep (se 1 (by rfl) ⟨2161538, by rfl⟩ : syracuseStep 2882051 = 4323077) B4323077
theorem B1538657 : Blo 1136633 1538657 := bstep (se 2 (by rfl) ⟨576996, by rfl⟩ : syracuseStep 1538657 = 1153993) B1153993
theorem B2882243 : Blo 1136633 2882243 := bstep (se 1 (by rfl) ⟨2161682, by rfl⟩ : syracuseStep 2882243 = 4323365) B4323365
theorem B2161379 : Blo 1136633 2161379 := bstep (se 1 (by rfl) ⟨1621034, by rfl⟩ : syracuseStep 2161379 = 3242069) B3242069
theorem B1440499 : Blo 1136633 1440499 := bstep (se 1 (by rfl) ⟨1080374, by rfl⟩ : syracuseStep 1440499 = 2160749) B2160749
theorem B1440595 : Blo 1136633 1440595 := bstep (se 1 (by rfl) ⟨1080446, by rfl⟩ : syracuseStep 1440595 = 2160893) B2160893
theorem B14580593 : Blo 1136633 14580593 := bstep (se 2 (by rfl) ⟨5467722, by rfl⟩ : syracuseStep 14580593 = 10935445) B10935445
theorem B5766065 : Blo 1136633 5766065 := bstep (se 2 (by rfl) ⟨2162274, by rfl⟩ : syracuseStep 5766065 = 4324549) B4324549
theorem B4324337 : Blo 1136633 4324337 := bstep (se 2 (by rfl) ⟨1621626, by rfl⟩ : syracuseStep 4324337 = 3243253) B3243253
theorem B2161667 : Blo 1136633 2161667 := bstep (se 1 (by rfl) ⟨1621250, by rfl⟩ : syracuseStep 2161667 = 3242501) B3242501
theorem B8649827 : Blo 1136633 8649827 := bstep (se 1 (by rfl) ⟨6487370, by rfl⟩ : syracuseStep 8649827 = 12974741) B12974741
theorem B6159473 : Blo 1136633 6159473 := bstep (se 2 (by rfl) ⟨2309802, by rfl⟩ : syracuseStep 6159473 = 4619605) B4619605
theorem B3243185 : Blo 1136633 3243185 := bstep (se 2 (by rfl) ⟨1216194, by rfl⟩ : syracuseStep 3243185 = 2432389) B2432389
theorem B10386629 : Blo 1136633 10386629 := bstep (se 4 (by rfl) ⟨973746, by rfl⟩ : syracuseStep 10386629 = 1947493) B1947493
theorem B6159665 : Blo 1136633 6159665 := bstep (se 2 (by rfl) ⟨2309874, by rfl⟩ : syracuseStep 6159665 = 4619749) B4619749
theorem B1441091 : Blo 1136633 1441091 := bstep (se 1 (by rfl) ⟨1080818, by rfl⟩ : syracuseStep 1441091 = 2161637) B2161637
theorem B1539409 : Blo 1136633 1539409 := bstep (se 2 (by rfl) ⟨577278, by rfl⟩ : syracuseStep 1539409 = 1154557) B1154557
theorem B3079565 : Blo 1136633 3079565 := bstep (se 3 (by rfl) ⟨577418, by rfl⟩ : syracuseStep 3079565 = 1154837) B1154837
theorem B1539523 : Blo 1136633 1539523 := bstep (se 1 (by rfl) ⟨1154642, by rfl⟩ : syracuseStep 1539523 = 2309285) B2309285
theorem B2883185 : Blo 1136633 2883185 := bstep (se 2 (by rfl) ⟨1081194, by rfl⟩ : syracuseStep 2883185 = 2162389) B2162389
theorem B2883235 : Blo 1136633 2883235 := bstep (se 1 (by rfl) ⟨2162426, by rfl⟩ : syracuseStep 2883235 = 4324853) B4324853
theorem B2883377 : Blo 1136633 2883377 := bstep (se 2 (by rfl) ⟨1081266, by rfl⟩ : syracuseStep 2883377 = 2162533) B2162533
theorem B2162609 : Blo 1136633 2162609 := bstep (se 2 (by rfl) ⟨810978, by rfl⟩ : syracuseStep 2162609 = 1621957) B1621957
theorem B5832749 : Blo 1136633 5832749 := bstep (se 3 (by rfl) ⟨1093640, by rfl⟩ : syracuseStep 5832749 = 2187281) B2187281
theorem B4325507 : Blo 1136633 4325507 := bstep (se 1 (by rfl) ⟨3244130, by rfl⟩ : syracuseStep 4325507 = 6488261) B6488261
theorem B4325521 : Blo 1136633 4325521 := bstep (se 2 (by rfl) ⟨1622070, by rfl⟩ : syracuseStep 4325521 = 3244141) B3244141
theorem B2883863 : Blo 1136633 2883863 := bstep (se 1 (by rfl) ⟨2162897, by rfl⟩ : syracuseStep 2883863 = 4325795) B4325795
theorem B8323373 : Blo 1136633 8323373 := bstep (se 3 (by rfl) ⟨1560632, by rfl⟩ : syracuseStep 8323373 = 3121265) B3121265
theorem B2163019 : Blo 1136633 2163019 := bstep (se 1 (by rfl) ⟨1622264, by rfl⟩ : syracuseStep 2163019 = 3244529) B3244529
theorem B2163095 : Blo 1136633 2163095 := bstep (se 1 (by rfl) ⟨1622321, by rfl⟩ : syracuseStep 2163095 = 3244643) B3244643
theorem B4325825 : Blo 1136633 4325825 := bstep (se 2 (by rfl) ⟨1622184, by rfl⟩ : syracuseStep 4325825 = 3244369) B3244369
theorem B16417241 : Blo 1136633 16417241 := bstep (se 2 (by rfl) ⟨6156465, by rfl⟩ : syracuseStep 16417241 = 12312931) B12312931
theorem B1442443 : Blo 1136633 1442443 := bstep (se 1 (by rfl) ⟨1081832, by rfl⟩ : syracuseStep 1442443 = 2163665) B2163665
theorem B59081525 : Blo 1136633 59081525 := bstep (se 5 (by rfl) ⟨2769446, by rfl⟩ : syracuseStep 59081525 = 5538893) B5538893
theorem B1278859 : Blo 1136633 1278859 := bstep (se 1 (by rfl) ⟨959144, by rfl⟩ : syracuseStep 1278859 = 1918289) B1918289
theorem B1442711 : Blo 1136633 1442711 := bstep (se 1 (by rfl) ⟨1082033, by rfl⟩ : syracuseStep 1442711 = 2164067) B2164067
theorem B6489011 : Blo 1136633 6489011 := bstep (se 1 (by rfl) ⟨4866758, by rfl⟩ : syracuseStep 6489011 = 9733517) B9733517
theorem B2884531 : Blo 1136633 2884531 := bstep (se 1 (by rfl) ⟨2163398, by rfl⟩ : syracuseStep 2884531 = 4326797) B4326797
theorem B5473241 : Blo 1136633 5473241 := bstep (se 2 (by rfl) ⟨2052465, by rfl⟩ : syracuseStep 5473241 = 4104931) B4104931
theorem B1278967 : Blo 1136633 1278967 := bstep (se 1 (by rfl) ⟨959225, by rfl⟩ : syracuseStep 1278967 = 1918451) B1918451
theorem B1704971 : Blo 1136633 1704971 := bstep (se 1 (by rfl) ⟨1278728, by rfl⟩ : syracuseStep 1704971 = 2557457) B2557457
theorem B1704983 : Blo 1136633 1704983 := bstep (se 1 (by rfl) ⟨1278737, by rfl⟩ : syracuseStep 1704983 = 2557475) B2557475
theorem B2163763 : Blo 1136633 2163763 := bstep (se 1 (by rfl) ⟨1622822, by rfl⟩ : syracuseStep 2163763 = 3245645) B3245645
theorem B2884673 : Blo 1136633 2884673 := bstep (se 2 (by rfl) ⟨1081752, by rfl⟩ : syracuseStep 2884673 = 2163505) B2163505
theorem B1705049 : Blo 1136633 1705049 := bstep (se 2 (by rfl) ⟨639393, by rfl⟩ : syracuseStep 1705049 = 1278787) B1278787
theorem B4326493 : Blo 1136633 4326493 := bstep (se 3 (by rfl) ⟨811217, by rfl⟩ : syracuseStep 4326493 = 1622435) B1622435
theorem B1279147 : Blo 1136633 1279147 := bstep (se 1 (by rfl) ⟨959360, by rfl⟩ : syracuseStep 1279147 = 1918721) B1918721
theorem B1705163 : Blo 1136633 1705163 := bstep (se 1 (by rfl) ⟨1278872, by rfl⟩ : syracuseStep 1705163 = 2557745) B2557745
theorem B1705175 : Blo 1136633 1705175 := bstep (se 1 (by rfl) ⟨1278881, by rfl⟩ : syracuseStep 1705175 = 2557763) B2557763
theorem B8750353 : Blo 1136633 8750353 := bstep (se 2 (by rfl) ⟨3281382, by rfl⟩ : syracuseStep 8750353 = 6562765) B6562765
theorem B1279255 : Blo 1136633 1279255 := bstep (se 1 (by rfl) ⟨959441, by rfl⟩ : syracuseStep 1279255 = 1918883) B1918883
theorem B2163991 : Blo 1136633 2163991 := bstep (se 1 (by rfl) ⟨1622993, by rfl⟩ : syracuseStep 2163991 = 3245987) B3245987
theorem B1705241 : Blo 1136633 1705241 := bstep (se 2 (by rfl) ⟨639465, by rfl⟩ : syracuseStep 1705241 = 1278931) B1278931
theorem B3900761 : Blo 1136633 3900761 := bstep (se 2 (by rfl) ⟨1462785, by rfl⟩ : syracuseStep 3900761 = 2925571) B2925571
theorem B2164097 : Blo 1136633 2164097 := bstep (se 2 (by rfl) ⟨811536, by rfl⟩ : syracuseStep 2164097 = 1623073) B1623073
theorem B1705355 : Blo 1136633 1705355 := bstep (se 1 (by rfl) ⟨1279016, by rfl⟩ : syracuseStep 1705355 = 2558033) B2558033
theorem B1705367 : Blo 1136633 1705367 := bstep (se 1 (by rfl) ⟨1279025, by rfl⟩ : syracuseStep 1705367 = 2558051) B2558051
theorem B1279435 : Blo 1136633 1279435 := bstep (se 1 (by rfl) ⟨959576, by rfl⟩ : syracuseStep 1279435 = 1919153) B1919153
theorem B1705433 : Blo 1136633 1705433 := bstep (se 2 (by rfl) ⟨639537, by rfl⟩ : syracuseStep 1705433 = 1279075) B1279075
theorem B21890573 : Blo 1136633 21890573 := bstep (se 3 (by rfl) ⟨4104482, by rfl⟩ : syracuseStep 21890573 = 8208965) B8208965
theorem B2164249 : Blo 1136633 2164249 := bstep (se 2 (by rfl) ⟨811593, by rfl⟩ : syracuseStep 2164249 = 1623187) B1623187
theorem B1279543 : Blo 1136633 1279543 := bstep (se 1 (by rfl) ⟨959657, by rfl⟩ : syracuseStep 1279543 = 1919315) B1919315
theorem B1705547 : Blo 1136633 1705547 := bstep (se 1 (by rfl) ⟨1279160, by rfl⟩ : syracuseStep 1705547 = 2558321) B2558321
theorem B1705559 : Blo 1136633 1705559 := bstep (se 1 (by rfl) ⟨1279169, by rfl⟩ : syracuseStep 1705559 = 2558339) B2558339
theorem B1443415 : Blo 1136633 1443415 := bstep (se 1 (by rfl) ⟨1082561, by rfl⟩ : syracuseStep 1443415 = 2165123) B2165123
theorem B2557529 : Blo 1136633 2557529 := bstep (se 2 (by rfl) ⟨959073, by rfl⟩ : syracuseStep 2557529 = 1918147) B1918147
theorem B1705625 : Blo 1136633 1705625 := bstep (se 2 (by rfl) ⟨639609, by rfl⟩ : syracuseStep 1705625 = 1279219) B1279219
theorem B2557619 : Blo 1136633 2557619 := bstep (se 1 (by rfl) ⟨1918214, by rfl⟩ : syracuseStep 2557619 = 3836429) B3836429
theorem B3245771 : Blo 1136633 3245771 := bstep (se 1 (by rfl) ⟨2434328, by rfl⟩ : syracuseStep 3245771 = 4868657) B4868657
theorem B2557655 : Blo 1136633 2557655 := bstep (se 1 (by rfl) ⟨1918241, by rfl⟩ : syracuseStep 2557655 = 3836483) B3836483
theorem B1279723 : Blo 1136633 1279723 := bstep (se 1 (by rfl) ⟨959792, by rfl⟩ : syracuseStep 1279723 = 1919585) B1919585
theorem B1705739 : Blo 1136633 1705739 := bstep (se 1 (by rfl) ⟨1279304, by rfl⟩ : syracuseStep 1705739 = 2558609) B2558609
theorem B1705751 : Blo 1136633 1705751 := bstep (se 1 (by rfl) ⟨1279313, by rfl⟩ : syracuseStep 1705751 = 2558627) B2558627
theorem B6915905 : Blo 1136633 6915905 := bstep (se 2 (by rfl) ⟨2593464, by rfl⟩ : syracuseStep 6915905 = 5186929) B5186929
theorem B1279831 : Blo 1136633 1279831 := bstep (se 1 (by rfl) ⟨959873, by rfl⟩ : syracuseStep 1279831 = 1919747) B1919747
theorem B1705817 : Blo 1136633 1705817 := bstep (se 2 (by rfl) ⟨639681, by rfl⟩ : syracuseStep 1705817 = 1279363) B1279363
theorem B2557835 : Blo 1136633 2557835 := bstep (se 1 (by rfl) ⟨1918376, by rfl⟩ : syracuseStep 2557835 = 3836753) B3836753
theorem B15599537 : Blo 1136633 15599537 := bstep (se 2 (by rfl) ⟨5849826, by rfl⟩ : syracuseStep 15599537 = 11699653) B11699653
theorem B2557889 : Blo 1136633 2557889 := bstep (se 2 (by rfl) ⟨959208, by rfl⟩ : syracuseStep 2557889 = 1918417) B1918417
theorem B1705931 : Blo 1136633 1705931 := bstep (se 1 (by rfl) ⟨1279448, by rfl⟩ : syracuseStep 1705931 = 2558897) B2558897
theorem B1705943 : Blo 1136633 1705943 := bstep (se 1 (by rfl) ⟨1279457, by rfl⟩ : syracuseStep 1705943 = 2558915) B2558915
theorem B1214443 : Blo 1136633 1214443 := bstep (se 1 (by rfl) ⟨910832, by rfl⟩ : syracuseStep 1214443 = 1821665) B1821665
theorem B1280011 : Blo 1136633 1280011 := bstep (se 1 (by rfl) ⟨960008, by rfl⟩ : syracuseStep 1280011 = 1920017) B1920017
theorem B1706009 : Blo 1136633 1706009 := bstep (se 2 (by rfl) ⟨639753, by rfl⟩ : syracuseStep 1706009 = 1279507) B1279507
theorem B3246169 : Blo 1136633 3246169 := bstep (se 2 (by rfl) ⟨1217313, by rfl⟩ : syracuseStep 3246169 = 2434627) B2434627
theorem B3082333 : Blo 1136633 3082333 := bstep (se 3 (by rfl) ⟨577937, by rfl⟩ : syracuseStep 3082333 = 1155875) B1155875
theorem B1280119 : Blo 1136633 1280119 := bstep (se 1 (by rfl) ⟨960089, by rfl⟩ : syracuseStep 1280119 = 1920179) B1920179
theorem B1706123 : Blo 1136633 1706123 := bstep (se 1 (by rfl) ⟨1279592, by rfl⟩ : syracuseStep 1706123 = 2559185) B2559185
theorem B1706135 : Blo 1136633 1706135 := bstep (se 1 (by rfl) ⟨1279601, by rfl⟩ : syracuseStep 1706135 = 2559203) B2559203
theorem B2558105 : Blo 1136633 2558105 := bstep (se 2 (by rfl) ⟨959289, by rfl⟩ : syracuseStep 2558105 = 1918579) B1918579
theorem B1706201 : Blo 1136633 1706201 := bstep (se 2 (by rfl) ⟨639825, by rfl⟩ : syracuseStep 1706201 = 1279651) B1279651
theorem B2558195 : Blo 1136633 2558195 := bstep (se 1 (by rfl) ⟨1918646, by rfl⟩ : syracuseStep 2558195 = 3837293) B3837293
theorem B2558231 : Blo 1136633 2558231 := bstep (se 1 (by rfl) ⟨1918673, by rfl⟩ : syracuseStep 2558231 = 3837347) B3837347
theorem B1280299 : Blo 1136633 1280299 := bstep (se 1 (by rfl) ⟨960224, by rfl⟩ : syracuseStep 1280299 = 1920449) B1920449
theorem B2885939 : Blo 1136633 2885939 := bstep (se 1 (by rfl) ⟨2164454, by rfl⟩ : syracuseStep 2885939 = 4328909) B4328909
theorem B12323137 : Blo 1136633 12323137 := bstep (se 2 (by rfl) ⟨4621176, by rfl⟩ : syracuseStep 12323137 = 9242353) B9242353
theorem B1706315 : Blo 1136633 1706315 := bstep (se 1 (by rfl) ⟨1279736, by rfl⟩ : syracuseStep 1706315 = 2559473) B2559473
theorem B1706327 : Blo 1136633 1706327 := bstep (se 1 (by rfl) ⟨1279745, by rfl⟩ : syracuseStep 1706327 = 2559491) B2559491
theorem B4327769 : Blo 1136633 4327769 := bstep (se 2 (by rfl) ⟨1622913, by rfl⟩ : syracuseStep 4327769 = 3245827) B3245827
theorem B6490469 : Blo 1136633 6490469 := bstep (se 4 (by rfl) ⟨608481, by rfl⟩ : syracuseStep 6490469 = 1216963) B1216963
theorem B1280407 : Blo 1136633 1280407 := bstep (se 1 (by rfl) ⟨960305, by rfl⟩ : syracuseStep 1280407 = 1920611) B1920611
theorem B1706393 : Blo 1136633 1706393 := bstep (se 2 (by rfl) ⟨639897, by rfl⟩ : syracuseStep 1706393 = 1279795) B1279795
theorem B9734579 : Blo 1136633 9734579 := bstep (se 1 (by rfl) ⟨7300934, by rfl⟩ : syracuseStep 9734579 = 14601869) B14601869
theorem B2558411 : Blo 1136633 2558411 := bstep (se 1 (by rfl) ⟨1918808, by rfl⟩ : syracuseStep 2558411 = 3837617) B3837617
theorem B2558465 : Blo 1136633 2558465 := bstep (se 2 (by rfl) ⟨959424, by rfl⟩ : syracuseStep 2558465 = 1918849) B1918849
theorem B1706507 : Blo 1136633 1706507 := bstep (se 1 (by rfl) ⟨1279880, by rfl⟩ : syracuseStep 1706507 = 2559761) B2559761
theorem B1706519 : Blo 1136633 1706519 := bstep (se 1 (by rfl) ⟨1279889, by rfl⟩ : syracuseStep 1706519 = 2559779) B2559779
theorem B1280587 : Blo 1136633 1280587 := bstep (se 1 (by rfl) ⟨960440, by rfl⟩ : syracuseStep 1280587 = 1920881) B1920881
theorem B2919001 : Blo 1136633 2919001 := bstep (se 2 (by rfl) ⟨1094625, by rfl⟩ : syracuseStep 2919001 = 2189251) B2189251
theorem B1706585 : Blo 1136633 1706585 := bstep (se 2 (by rfl) ⟨639969, by rfl⟩ : syracuseStep 1706585 = 1279939) B1279939
theorem B1280695 : Blo 1136633 1280695 := bstep (se 1 (by rfl) ⟨960521, by rfl⟩ : syracuseStep 1280695 = 1921043) B1921043
theorem B1706699 : Blo 1136633 1706699 := bstep (se 1 (by rfl) ⟨1280024, by rfl⟩ : syracuseStep 1706699 = 2560049) B2560049
theorem B1706711 : Blo 1136633 1706711 := bstep (se 1 (by rfl) ⟨1280033, by rfl⟩ : syracuseStep 1706711 = 2560067) B2560067
theorem B2558681 : Blo 1136633 2558681 := bstep (se 2 (by rfl) ⟨959505, by rfl⟩ : syracuseStep 2558681 = 1919011) B1919011
theorem B2427673 : Blo 1136633 2427673 := bstep (se 2 (by rfl) ⟨910377, by rfl⟩ : syracuseStep 2427673 = 1820755) B1820755
theorem B1706777 : Blo 1136633 1706777 := bstep (se 2 (by rfl) ⟨640041, by rfl⟩ : syracuseStep 1706777 = 1280083) B1280083
theorem B6490925 : Blo 1136633 6490925 := bstep (se 3 (by rfl) ⟨1217048, by rfl⟩ : syracuseStep 6490925 = 2434097) B2434097
theorem B2558771 : Blo 1136633 2558771 := bstep (se 1 (by rfl) ⟨1919078, by rfl⟩ : syracuseStep 2558771 = 3838157) B3838157
theorem B2886475 : Blo 1136633 2886475 := bstep (se 1 (by rfl) ⟨2164856, by rfl⟩ : syracuseStep 2886475 = 4329713) B4329713
theorem B2558807 : Blo 1136633 2558807 := bstep (se 1 (by rfl) ⟨1919105, by rfl⟩ : syracuseStep 2558807 = 3838211) B3838211
theorem B1215319 : Blo 1136633 1215319 := bstep (se 1 (by rfl) ⟨911489, by rfl⟩ : syracuseStep 1215319 = 1822979) B1822979
theorem B1280875 : Blo 1136633 1280875 := bstep (se 1 (by rfl) ⟨960656, by rfl⟩ : syracuseStep 1280875 = 1921313) B1921313
theorem B5770115 : Blo 1136633 5770115 := bstep (se 1 (by rfl) ⟨4327586, by rfl⟩ : syracuseStep 5770115 = 8655173) B8655173
theorem B1706891 : Blo 1136633 1706891 := bstep (se 1 (by rfl) ⟨1280168, by rfl⟩ : syracuseStep 1706891 = 2560337) B2560337
theorem B1706903 : Blo 1136633 1706903 := bstep (se 1 (by rfl) ⟨1280177, by rfl⟩ : syracuseStep 1706903 = 2560355) B2560355
theorem B1280983 : Blo 1136633 1280983 := bstep (se 1 (by rfl) ⟨960737, by rfl⟩ : syracuseStep 1280983 = 1921475) B1921475
theorem B1706969 : Blo 1136633 1706969 := bstep (se 2 (by rfl) ⟨640113, by rfl⟩ : syracuseStep 1706969 = 1280227) B1280227
theorem B2886617 : Blo 1136633 2886617 := bstep (se 2 (by rfl) ⟨1082481, by rfl⟩ : syracuseStep 2886617 = 2164963) B2164963
theorem B2558987 : Blo 1136633 2558987 := bstep (se 1 (by rfl) ⟨1919240, by rfl⟩ : syracuseStep 2558987 = 3838481) B3838481
theorem B2559041 : Blo 1136633 2559041 := bstep (se 2 (by rfl) ⟨959640, by rfl⟩ : syracuseStep 2559041 = 1919281) B1919281
theorem B1707083 : Blo 1136633 1707083 := bstep (se 1 (by rfl) ⟨1280312, by rfl⟩ : syracuseStep 1707083 = 2560625) B2560625
theorem B1707095 : Blo 1136633 1707095 := bstep (se 1 (by rfl) ⟨1280321, by rfl⟩ : syracuseStep 1707095 = 2560643) B2560643
theorem B1281163 : Blo 1136633 1281163 := bstep (se 1 (by rfl) ⟨960872, by rfl⟩ : syracuseStep 1281163 = 1921745) B1921745
theorem B1707161 : Blo 1136633 1707161 := bstep (se 2 (by rfl) ⟨640185, by rfl⟩ : syracuseStep 1707161 = 1280371) B1280371
theorem B3837131 : Blo 1136633 3837131 := bstep (se 1 (by rfl) ⟨2877848, by rfl⟩ : syracuseStep 3837131 = 5755697) B5755697
theorem B1281271 : Blo 1136633 1281271 := bstep (se 1 (by rfl) ⟨960953, by rfl⟩ : syracuseStep 1281271 = 1921907) B1921907
theorem B1707275 : Blo 1136633 1707275 := bstep (se 1 (by rfl) ⟨1280456, by rfl⟩ : syracuseStep 1707275 = 2560913) B2560913
theorem B1707287 : Blo 1136633 1707287 := bstep (se 1 (by rfl) ⟨1280465, by rfl⟩ : syracuseStep 1707287 = 2560931) B2560931
theorem B1215767 : Blo 1136633 1215767 := bstep (se 1 (by rfl) ⟨911825, by rfl⟩ : syracuseStep 1215767 = 1823651) B1823651
theorem B2559257 : Blo 1136633 2559257 := bstep (se 2 (by rfl) ⟨959721, by rfl⟩ : syracuseStep 2559257 = 1919443) B1919443
theorem B3247411 : Blo 1136633 3247411 := bstep (se 1 (by rfl) ⟨2435558, by rfl⟩ : syracuseStep 3247411 = 4871117) B4871117
theorem B1707353 : Blo 1136633 1707353 := bstep (se 2 (by rfl) ⟨640257, by rfl⟩ : syracuseStep 1707353 = 1280515) B1280515
theorem B2559347 : Blo 1136633 2559347 := bstep (se 1 (by rfl) ⟨1919510, by rfl⟩ : syracuseStep 2559347 = 3839021) B3839021
theorem B2559383 : Blo 1136633 2559383 := bstep (se 1 (by rfl) ⟨1919537, by rfl⟩ : syracuseStep 2559383 = 3839075) B3839075
theorem B1281451 : Blo 1136633 1281451 := bstep (se 1 (by rfl) ⟨961088, by rfl⟩ : syracuseStep 1281451 = 1922177) B1922177
theorem B1707467 : Blo 1136633 1707467 := bstep (se 1 (by rfl) ⟨1280600, by rfl⟩ : syracuseStep 1707467 = 2561201) B2561201
theorem B1707479 : Blo 1136633 1707479 := bstep (se 1 (by rfl) ⟨1280609, by rfl⟩ : syracuseStep 1707479 = 2561219) B2561219
theorem B3837401 : Blo 1136633 3837401 := bstep (se 2 (by rfl) ⟨1439025, by rfl⟩ : syracuseStep 3837401 = 2878051) B2878051
theorem B3378649 : Blo 1136633 3378649 := bstep (se 2 (by rfl) ⟨1266993, by rfl⟩ : syracuseStep 3378649 = 2533987) B2533987
theorem B6491609 : Blo 1136633 6491609 := bstep (se 2 (by rfl) ⟨2434353, by rfl⟩ : syracuseStep 6491609 = 4868707) B4868707
theorem B1281559 : Blo 1136633 1281559 := bstep (se 1 (by rfl) ⟨961169, by rfl⟩ : syracuseStep 1281559 = 1922339) B1922339
theorem B1707545 : Blo 1136633 1707545 := bstep (se 2 (by rfl) ⟨640329, by rfl⟩ : syracuseStep 1707545 = 1280659) B1280659
theorem B2559563 : Blo 1136633 2559563 := bstep (se 1 (by rfl) ⟨1919672, by rfl⟩ : syracuseStep 2559563 = 3839345) B3839345
theorem B2559617 : Blo 1136633 2559617 := bstep (se 2 (by rfl) ⟨959856, by rfl⟩ : syracuseStep 2559617 = 1919713) B1919713
theorem B1707659 : Blo 1136633 1707659 := bstep (se 1 (by rfl) ⟨1280744, by rfl⟩ : syracuseStep 1707659 = 2561489) B2561489
theorem B1216139 : Blo 1136633 1216139 := bstep (se 1 (by rfl) ⟨912104, by rfl⟩ : syracuseStep 1216139 = 1824209) B1824209
theorem B1707671 : Blo 1136633 1707671 := bstep (se 1 (by rfl) ⟨1280753, by rfl⟩ : syracuseStep 1707671 = 2561507) B2561507
theorem B1281739 : Blo 1136633 1281739 := bstep (se 1 (by rfl) ⟨961304, by rfl⟩ : syracuseStep 1281739 = 1922609) B1922609
theorem B1707737 : Blo 1136633 1707737 := bstep (se 2 (by rfl) ⟨640401, by rfl⟩ : syracuseStep 1707737 = 1280803) B1280803
theorem B1281847 : Blo 1136633 1281847 := bstep (se 1 (by rfl) ⟨961385, by rfl⟩ : syracuseStep 1281847 = 1922771) B1922771
theorem B1707851 : Blo 1136633 1707851 := bstep (se 1 (by rfl) ⟨1280888, by rfl⟩ : syracuseStep 1707851 = 2561777) B2561777
theorem B1707863 : Blo 1136633 1707863 := bstep (se 1 (by rfl) ⟨1280897, by rfl⟩ : syracuseStep 1707863 = 2561795) B2561795
theorem B2559833 : Blo 1136633 2559833 := bstep (se 2 (by rfl) ⟨959937, by rfl⟩ : syracuseStep 2559833 = 1919875) B1919875
theorem B4099985 : Blo 1136633 4099985 := bstep (se 2 (by rfl) ⟨1537494, by rfl⟩ : syracuseStep 4099985 = 3074989) B3074989
theorem B1707929 : Blo 1136633 1707929 := bstep (se 2 (by rfl) ⟨640473, by rfl⟩ : syracuseStep 1707929 = 1280947) B1280947
theorem B2559923 : Blo 1136633 2559923 := bstep (se 1 (by rfl) ⟨1919942, by rfl⟩ : syracuseStep 2559923 = 3839885) B3839885
theorem B4329395 : Blo 1136633 4329395 := bstep (se 1 (by rfl) ⟨3247046, by rfl⟩ : syracuseStep 4329395 = 6494093) B6494093
theorem B4329409 : Blo 1136633 4329409 := bstep (se 2 (by rfl) ⟨1623528, by rfl⟩ : syracuseStep 4329409 = 3247057) B3247057
theorem B2559959 : Blo 1136633 2559959 := bstep (se 1 (by rfl) ⟨1919969, by rfl⟩ : syracuseStep 2559959 = 3839939) B3839939
theorem B1282027 : Blo 1136633 1282027 := bstep (se 1 (by rfl) ⟨961520, by rfl⟩ : syracuseStep 1282027 = 1923041) B1923041
theorem B1708043 : Blo 1136633 1708043 := bstep (se 1 (by rfl) ⟨1281032, by rfl⟩ : syracuseStep 1708043 = 2562065) B2562065
theorem B1708055 : Blo 1136633 1708055 := bstep (se 1 (by rfl) ⟨1281041, by rfl⟩ : syracuseStep 1708055 = 2562083) B2562083
theorem B1282135 : Blo 1136633 1282135 := bstep (se 1 (by rfl) ⟨961601, by rfl⟩ : syracuseStep 1282135 = 1923203) B1923203
theorem B1708121 : Blo 1136633 1708121 := bstep (se 2 (by rfl) ⟨640545, by rfl⟩ : syracuseStep 1708121 = 1281091) B1281091
theorem B2560139 : Blo 1136633 2560139 := bstep (se 1 (by rfl) ⟨1920104, by rfl⟩ : syracuseStep 2560139 = 3840209) B3840209
theorem B3838103 : Blo 1136633 3838103 := bstep (se 1 (by rfl) ⟨2878577, by rfl⟩ : syracuseStep 3838103 = 5757155) B5757155
theorem B2560193 : Blo 1136633 2560193 := bstep (se 2 (by rfl) ⟨960072, by rfl⟩ : syracuseStep 2560193 = 1920145) B1920145
theorem B1708235 : Blo 1136633 1708235 := bstep (se 1 (by rfl) ⟨1281176, by rfl⟩ : syracuseStep 1708235 = 2562353) B2562353
theorem B1708247 : Blo 1136633 1708247 := bstep (se 1 (by rfl) ⟨1281185, by rfl⟩ : syracuseStep 1708247 = 2562371) B2562371
theorem B3641561 : Blo 1136633 3641561 := bstep (se 2 (by rfl) ⟨1365585, by rfl⟩ : syracuseStep 3641561 = 2731171) B2731171
theorem B10391813 : Blo 1136633 10391813 := bstep (se 4 (by rfl) ⟨974232, by rfl⟩ : syracuseStep 10391813 = 1948465) B1948465
theorem B1282315 : Blo 1136633 1282315 := bstep (se 1 (by rfl) ⟨961736, by rfl⟩ : syracuseStep 1282315 = 1923473) B1923473
theorem B1708313 : Blo 1136633 1708313 := bstep (se 2 (by rfl) ⟨640617, by rfl⟩ : syracuseStep 1708313 = 1281235) B1281235
theorem B3641689 : Blo 1136633 3641689 := bstep (se 2 (by rfl) ⟨1365633, by rfl⟩ : syracuseStep 3641689 = 2731267) B2731267
theorem B1282423 : Blo 1136633 1282423 := bstep (se 1 (by rfl) ⟨961817, by rfl⟩ : syracuseStep 1282423 = 1923635) B1923635
theorem B1708427 : Blo 1136633 1708427 := bstep (se 1 (by rfl) ⟨1281320, by rfl⟩ : syracuseStep 1708427 = 2562641) B2562641
theorem B1708439 : Blo 1136633 1708439 := bstep (se 1 (by rfl) ⟨1281329, by rfl⟩ : syracuseStep 1708439 = 2562659) B2562659
theorem B2560409 : Blo 1136633 2560409 := bstep (se 2 (by rfl) ⟨960153, by rfl⟩ : syracuseStep 2560409 = 1920307) B1920307
theorem B1708505 : Blo 1136633 1708505 := bstep (se 2 (by rfl) ⟨640689, by rfl⟩ : syracuseStep 1708505 = 1281379) B1281379
theorem B2560499 : Blo 1136633 2560499 := bstep (se 1 (by rfl) ⟨1920374, by rfl⟩ : syracuseStep 2560499 = 3840749) B3840749
theorem B2560535 : Blo 1136633 2560535 := bstep (se 1 (by rfl) ⟨1920401, by rfl⟩ : syracuseStep 2560535 = 3840803) B3840803
theorem B1282603 : Blo 1136633 1282603 := bstep (se 1 (by rfl) ⟨961952, by rfl⟩ : syracuseStep 1282603 = 1923905) B1923905
theorem B1708619 : Blo 1136633 1708619 := bstep (se 1 (by rfl) ⟨1281464, by rfl⟩ : syracuseStep 1708619 = 2562929) B2562929
theorem B1708631 : Blo 1136633 1708631 := bstep (se 1 (by rfl) ⟨1281473, by rfl⟩ : syracuseStep 1708631 = 2562947) B2562947
theorem B1217143 : Blo 1136633 1217143 := bstep (se 1 (by rfl) ⟨912857, by rfl⟩ : syracuseStep 1217143 = 1825715) B1825715
theorem B1282711 : Blo 1136633 1282711 := bstep (se 1 (by rfl) ⟨962033, by rfl⟩ : syracuseStep 1282711 = 1924067) B1924067
theorem B1708697 : Blo 1136633 1708697 := bstep (se 2 (by rfl) ⟨640761, by rfl⟩ : syracuseStep 1708697 = 1281523) B1281523
theorem B3838643 : Blo 1136633 3838643 := bstep (se 1 (by rfl) ⟨2878982, by rfl⟩ : syracuseStep 3838643 = 5757965) B5757965
theorem B2560715 : Blo 1136633 2560715 := bstep (se 1 (by rfl) ⟨1920536, by rfl⟩ : syracuseStep 2560715 = 3841073) B3841073
theorem B2560769 : Blo 1136633 2560769 := bstep (se 2 (by rfl) ⟨960288, by rfl⟩ : syracuseStep 2560769 = 1920577) B1920577
theorem B1708811 : Blo 1136633 1708811 := bstep (se 1 (by rfl) ⟨1281608, by rfl⟩ : syracuseStep 1708811 = 2563217) B2563217
theorem B1708823 : Blo 1136633 1708823 := bstep (se 1 (by rfl) ⟨1281617, by rfl⟩ : syracuseStep 1708823 = 2563235) B2563235
theorem B1282891 : Blo 1136633 1282891 := bstep (se 1 (by rfl) ⟨962168, by rfl⟩ : syracuseStep 1282891 = 1924337) B1924337
theorem B1708889 : Blo 1136633 1708889 := bstep (se 2 (by rfl) ⟨640833, by rfl⟩ : syracuseStep 1708889 = 1281667) B1281667
theorem B1282999 : Blo 1136633 1282999 := bstep (se 1 (by rfl) ⟨962249, by rfl⟩ : syracuseStep 1282999 = 1924499) B1924499
theorem B3838913 : Blo 1136633 3838913 := bstep (se 2 (by rfl) ⟨1439592, by rfl⟩ : syracuseStep 3838913 = 2879185) B2879185
theorem B1709003 : Blo 1136633 1709003 := bstep (se 1 (by rfl) ⟨1281752, by rfl⟩ : syracuseStep 1709003 = 2563505) B2563505
theorem B1709015 : Blo 1136633 1709015 := bstep (se 1 (by rfl) ⟨1281761, by rfl⟩ : syracuseStep 1709015 = 2563523) B2563523
theorem B2560985 : Blo 1136633 2560985 := bstep (se 2 (by rfl) ⟨960369, by rfl⟩ : syracuseStep 2560985 = 1920739) B1920739
theorem B12948497 : Blo 1136633 12948497 := bstep (se 2 (by rfl) ⟨4855686, by rfl⟩ : syracuseStep 12948497 = 9711373) B9711373
theorem B1709081 : Blo 1136633 1709081 := bstep (se 2 (by rfl) ⟨640905, by rfl⟩ : syracuseStep 1709081 = 1281811) B1281811
theorem B2561075 : Blo 1136633 2561075 := bstep (se 1 (by rfl) ⟨1920806, by rfl⟩ : syracuseStep 2561075 = 3841613) B3841613
theorem B13866059 : Blo 1136633 13866059 := bstep (se 1 (by rfl) ⟨10399544, by rfl⟩ : syracuseStep 13866059 = 20799089) B20799089
theorem B2561111 : Blo 1136633 2561111 := bstep (se 1 (by rfl) ⟨1920833, by rfl⟩ : syracuseStep 2561111 = 3841667) B3841667
theorem B1283179 : Blo 1136633 1283179 := bstep (se 1 (by rfl) ⟨962384, by rfl⟩ : syracuseStep 1283179 = 1924769) B1924769
theorem B2430091 : Blo 1136633 2430091 := bstep (se 1 (by rfl) ⟨1822568, by rfl⟩ : syracuseStep 2430091 = 3645137) B3645137
theorem B1709195 : Blo 1136633 1709195 := bstep (se 1 (by rfl) ⟨1281896, by rfl⟩ : syracuseStep 1709195 = 2563793) B2563793
theorem B1709207 : Blo 1136633 1709207 := bstep (se 1 (by rfl) ⟨1281905, by rfl⟩ : syracuseStep 1709207 = 2563811) B2563811
theorem B4101313 : Blo 1136633 4101313 := bstep (se 2 (by rfl) ⟨1537992, by rfl⟩ : syracuseStep 4101313 = 3075985) B3075985
theorem B2430167 : Blo 1136633 2430167 := bstep (se 1 (by rfl) ⟨1822625, by rfl⟩ : syracuseStep 2430167 = 3645251) B3645251
theorem B1709273 : Blo 1136633 1709273 := bstep (se 2 (by rfl) ⟨640977, by rfl⟩ : syracuseStep 1709273 = 1281955) B1281955
theorem B2561291 : Blo 1136633 2561291 := bstep (se 1 (by rfl) ⟨1920968, by rfl⟩ : syracuseStep 2561291 = 3841937) B3841937
theorem B8656145 : Blo 1136633 8656145 := bstep (se 2 (by rfl) ⟨3246054, by rfl⟩ : syracuseStep 8656145 = 6492109) B6492109
theorem B2561345 : Blo 1136633 2561345 := bstep (se 2 (by rfl) ⟨960504, by rfl⟩ : syracuseStep 2561345 = 1921009) B1921009
theorem B1709387 : Blo 1136633 1709387 := bstep (se 1 (by rfl) ⟨1282040, by rfl⟩ : syracuseStep 1709387 = 2564081) B2564081
theorem B1709399 : Blo 1136633 1709399 := bstep (se 1 (by rfl) ⟨1282049, by rfl⟩ : syracuseStep 1709399 = 2564099) B2564099
theorem B1709465 : Blo 1136633 1709465 := bstep (se 2 (by rfl) ⟨641049, by rfl⟩ : syracuseStep 1709465 = 1282099) B1282099
theorem B1217963 : Blo 1136633 1217963 := bstep (se 1 (by rfl) ⟨913472, by rfl⟩ : syracuseStep 1217963 = 1826945) B1826945
theorem B4855261 : Blo 1136633 4855261 := bstep (se 3 (by rfl) ⟨910361, by rfl⟩ : syracuseStep 4855261 = 1820723) B1820723
theorem B3839453 : Blo 1136633 3839453 := bstep (se 3 (by rfl) ⟨719897, by rfl⟩ : syracuseStep 3839453 = 1439795) B1439795
theorem B1709579 : Blo 1136633 1709579 := bstep (se 1 (by rfl) ⟨1282184, by rfl⟩ : syracuseStep 1709579 = 2564369) B2564369
theorem B1709591 : Blo 1136633 1709591 := bstep (se 1 (by rfl) ⟨1282193, by rfl⟩ : syracuseStep 1709591 = 2564387) B2564387
theorem B2561561 : Blo 1136633 2561561 := bstep (se 2 (by rfl) ⟨960585, by rfl⟩ : syracuseStep 2561561 = 1921171) B1921171
theorem B1709657 : Blo 1136633 1709657 := bstep (se 2 (by rfl) ⟨641121, by rfl⟩ : syracuseStep 1709657 = 1282243) B1282243
theorem B2561651 : Blo 1136633 2561651 := bstep (se 1 (by rfl) ⟨1921238, by rfl⟩ : syracuseStep 2561651 = 3842477) B3842477
theorem B2561687 : Blo 1136633 2561687 := bstep (se 1 (by rfl) ⟨1921265, by rfl⟩ : syracuseStep 2561687 = 3842531) B3842531
theorem B1709771 : Blo 1136633 1709771 := bstep (se 1 (by rfl) ⟨1282328, by rfl⟩ : syracuseStep 1709771 = 2564657) B2564657
theorem B1709783 : Blo 1136633 1709783 := bstep (se 1 (by rfl) ⟨1282337, by rfl⟩ : syracuseStep 1709783 = 2564675) B2564675
theorem B1709849 : Blo 1136633 1709849 := bstep (se 2 (by rfl) ⟨641193, by rfl⟩ : syracuseStep 1709849 = 1282387) B1282387
theorem B2561867 : Blo 1136633 2561867 := bstep (se 1 (by rfl) ⟨1921400, by rfl⟩ : syracuseStep 2561867 = 3842801) B3842801
theorem B31135589 : Blo 1136633 31135589 := bstep (se 4 (by rfl) ⟨2918961, by rfl⟩ : syracuseStep 31135589 = 5837923) B5837923
theorem B2561921 : Blo 1136633 2561921 := bstep (se 2 (by rfl) ⟨960720, by rfl⟩ : syracuseStep 2561921 = 1921441) B1921441
theorem B1709963 : Blo 1136633 1709963 := bstep (se 1 (by rfl) ⟨1282472, by rfl⟩ : syracuseStep 1709963 = 2564945) B2564945
theorem B1709975 : Blo 1136633 1709975 := bstep (se 1 (by rfl) ⟨1282481, by rfl⟩ : syracuseStep 1709975 = 2564963) B2564963
theorem B1710041 : Blo 1136633 1710041 := bstep (se 2 (by rfl) ⟨641265, by rfl⟩ : syracuseStep 1710041 = 1282531) B1282531
theorem B4855859 : Blo 1136633 4855859 := bstep (se 1 (by rfl) ⟨3641894, by rfl⟩ : syracuseStep 4855859 = 7283789) B7283789
theorem B1710155 : Blo 1136633 1710155 := bstep (se 1 (by rfl) ⟨1282616, by rfl⟩ : syracuseStep 1710155 = 2565233) B2565233
theorem B1710167 : Blo 1136633 1710167 := bstep (se 1 (by rfl) ⟨1282625, by rfl⟩ : syracuseStep 1710167 = 2565251) B2565251
theorem B2562137 : Blo 1136633 2562137 := bstep (se 2 (by rfl) ⟨960801, by rfl⟩ : syracuseStep 2562137 = 1921603) B1921603
theorem B1710233 : Blo 1136633 1710233 := bstep (se 2 (by rfl) ⟨641337, by rfl⟩ : syracuseStep 1710233 = 1282675) B1282675
theorem B2562227 : Blo 1136633 2562227 := bstep (se 1 (by rfl) ⟨1921670, by rfl⟩ : syracuseStep 2562227 = 3843341) B3843341
theorem B2562263 : Blo 1136633 2562263 := bstep (se 1 (by rfl) ⟨1921697, by rfl⟩ : syracuseStep 2562263 = 3843395) B3843395
theorem B1710347 : Blo 1136633 1710347 := bstep (se 1 (by rfl) ⟨1282760, by rfl⟩ : syracuseStep 1710347 = 2565521) B2565521
theorem B1710359 : Blo 1136633 1710359 := bstep (se 1 (by rfl) ⟨1282769, by rfl⟩ : syracuseStep 1710359 = 2565539) B2565539
theorem B10950977 : Blo 1136633 10950977 := bstep (se 2 (by rfl) ⟨4106616, by rfl⟩ : syracuseStep 10950977 = 8213233) B8213233
theorem B1710425 : Blo 1136633 1710425 := bstep (se 2 (by rfl) ⟨641409, by rfl⟩ : syracuseStep 1710425 = 1282819) B1282819
theorem B1317227 : Blo 1136633 1317227 := bstep (se 1 (by rfl) ⟨987920, by rfl⟩ : syracuseStep 1317227 = 1975841) B1975841
theorem B2562443 : Blo 1136633 2562443 := bstep (se 1 (by rfl) ⟨1921832, by rfl⟩ : syracuseStep 2562443 = 3843665) B3843665
theorem B4004275 : Blo 1136633 4004275 := bstep (se 1 (by rfl) ⟨3003206, by rfl⟩ : syracuseStep 4004275 = 6006413) B6006413
theorem B2562497 : Blo 1136633 2562497 := bstep (se 2 (by rfl) ⟨960936, by rfl⟩ : syracuseStep 2562497 = 1921873) B1921873
theorem B1710539 : Blo 1136633 1710539 := bstep (se 1 (by rfl) ⟨1282904, by rfl⟩ : syracuseStep 1710539 = 2565809) B2565809
theorem B1710551 : Blo 1136633 1710551 := bstep (se 1 (by rfl) ⟨1282913, by rfl⟩ : syracuseStep 1710551 = 2565827) B2565827
theorem B10951129 : Blo 1136633 10951129 := bstep (se 2 (by rfl) ⟨4106673, by rfl⟩ : syracuseStep 10951129 = 8213347) B8213347
theorem B5773841 : Blo 1136633 5773841 := bstep (se 2 (by rfl) ⟨2165190, by rfl⟩ : syracuseStep 5773841 = 4330381) B4330381
theorem B1710617 : Blo 1136633 1710617 := bstep (se 2 (by rfl) ⟨641481, by rfl⟩ : syracuseStep 1710617 = 1282963) B1282963
theorem B3840587 : Blo 1136633 3840587 := bstep (se 1 (by rfl) ⟨2880440, by rfl⟩ : syracuseStep 3840587 = 5760881) B5760881
theorem B1710731 : Blo 1136633 1710731 := bstep (se 1 (by rfl) ⟨1283048, by rfl⟩ : syracuseStep 1710731 = 2566097) B2566097
theorem B1710743 : Blo 1136633 1710743 := bstep (se 1 (by rfl) ⟨1283057, by rfl⟩ : syracuseStep 1710743 = 2566115) B2566115
theorem B2562713 : Blo 1136633 2562713 := bstep (se 2 (by rfl) ⟨961017, by rfl⟩ : syracuseStep 2562713 = 1922035) B1922035
theorem B5774003 : Blo 1136633 5774003 := bstep (se 1 (by rfl) ⟨4330502, by rfl⟩ : syracuseStep 5774003 = 8661005) B8661005
theorem B1710809 : Blo 1136633 1710809 := bstep (se 2 (by rfl) ⟨641553, by rfl⟩ : syracuseStep 1710809 = 1283107) B1283107
theorem B2562803 : Blo 1136633 2562803 := bstep (se 1 (by rfl) ⟨1922102, by rfl⟩ : syracuseStep 2562803 = 3844205) B3844205
theorem B10525457 : Blo 1136633 10525457 := bstep (se 2 (by rfl) ⟨3947046, by rfl⟩ : syracuseStep 10525457 = 7894093) B7894093
theorem B2562839 : Blo 1136633 2562839 := bstep (se 1 (by rfl) ⟨1922129, by rfl⟩ : syracuseStep 2562839 = 3844259) B3844259
theorem B1710923 : Blo 1136633 1710923 := bstep (se 1 (by rfl) ⟨1283192, by rfl⟩ : syracuseStep 1710923 = 2566385) B2566385
theorem B1710935 : Blo 1136633 1710935 := bstep (se 1 (by rfl) ⟨1283201, by rfl⟩ : syracuseStep 1710935 = 2566403) B2566403
theorem B3840857 : Blo 1136633 3840857 := bstep (se 2 (by rfl) ⟨1440321, by rfl⟩ : syracuseStep 3840857 = 2880643) B2880643
theorem B2431937 : Blo 1136633 2431937 := bstep (se 2 (by rfl) ⟨911976, by rfl⟩ : syracuseStep 2431937 = 1823953) B1823953
theorem B2563019 : Blo 1136633 2563019 := bstep (se 1 (by rfl) ⟨1922264, by rfl⟩ : syracuseStep 2563019 = 3844529) B3844529
theorem B2563073 : Blo 1136633 2563073 := bstep (se 2 (by rfl) ⟨961152, by rfl⟩ : syracuseStep 2563073 = 1922305) B1922305
theorem B2563289 : Blo 1136633 2563289 := bstep (se 2 (by rfl) ⟨961233, by rfl⟩ : syracuseStep 2563289 = 1922467) B1922467
theorem B2563379 : Blo 1136633 2563379 := bstep (se 1 (by rfl) ⟨1922534, by rfl⟩ : syracuseStep 2563379 = 3845069) B3845069
theorem B2563415 : Blo 1136633 2563415 := bstep (se 1 (by rfl) ⟨1922561, by rfl⟩ : syracuseStep 2563415 = 3845123) B3845123
theorem B2563595 : Blo 1136633 2563595 := bstep (se 1 (by rfl) ⟨1922696, by rfl⟩ : syracuseStep 2563595 = 3845393) B3845393
theorem B3841559 : Blo 1136633 3841559 := bstep (se 1 (by rfl) ⟨2881169, by rfl⟩ : syracuseStep 3841559 = 5762339) B5762339
theorem B2563649 : Blo 1136633 2563649 := bstep (se 2 (by rfl) ⟨961368, by rfl⟩ : syracuseStep 2563649 = 1922737) B1922737
theorem B2563865 : Blo 1136633 2563865 := bstep (se 2 (by rfl) ⟨961449, by rfl⟩ : syracuseStep 2563865 = 1922899) B1922899
theorem B5480257 : Blo 1136633 5480257 := bstep (se 2 (by rfl) ⟨2055096, by rfl⟩ : syracuseStep 5480257 = 4110193) B4110193
theorem B2563955 : Blo 1136633 2563955 := bstep (se 1 (by rfl) ⟨1922966, by rfl⟩ : syracuseStep 2563955 = 3845933) B3845933
theorem B12951413 : Blo 1136633 12951413 := bstep (se 5 (by rfl) ⟨607097, by rfl⟩ : syracuseStep 12951413 = 1214195) B1214195
theorem B2563991 : Blo 1136633 2563991 := bstep (se 1 (by rfl) ⟨1922993, by rfl⟩ : syracuseStep 2563991 = 3845987) B3845987
theorem B3842099 : Blo 1136633 3842099 := bstep (se 1 (by rfl) ⟨2881574, by rfl⟩ : syracuseStep 3842099 = 5763149) B5763149
theorem B2564171 : Blo 1136633 2564171 := bstep (se 1 (by rfl) ⟨1923128, by rfl⟩ : syracuseStep 2564171 = 3846257) B3846257
theorem B2564225 : Blo 1136633 2564225 := bstep (se 2 (by rfl) ⟨961584, by rfl⟩ : syracuseStep 2564225 = 1923169) B1923169
theorem B1974487 : Blo 1136633 1974487 := bstep (se 1 (by rfl) ⟨1480865, by rfl⟩ : syracuseStep 1974487 = 2961731) B2961731
theorem B3645661 : Blo 1136633 3645661 := bstep (se 3 (by rfl) ⟨683561, by rfl⟩ : syracuseStep 3645661 = 1367123) B1367123
theorem B3842369 : Blo 1136633 3842369 := bstep (se 2 (by rfl) ⟨1440888, by rfl⟩ : syracuseStep 3842369 = 2881777) B2881777
theorem B2564441 : Blo 1136633 2564441 := bstep (se 2 (by rfl) ⟨961665, by rfl⟩ : syracuseStep 2564441 = 1923331) B1923331
theorem B2564531 : Blo 1136633 2564531 := bstep (se 1 (by rfl) ⟨1923398, by rfl⟩ : syracuseStep 2564531 = 3846797) B3846797
theorem B2564567 : Blo 1136633 2564567 := bstep (se 1 (by rfl) ⟨1923425, by rfl⟩ : syracuseStep 2564567 = 3846851) B3846851
theorem B4989443 : Blo 1136633 4989443 := bstep (se 1 (by rfl) ⟨3742082, by rfl⟩ : syracuseStep 4989443 = 7484165) B7484165
theorem B1155595 : Blo 1136633 1155595 := bstep (se 1 (by rfl) ⟨866696, by rfl⟩ : syracuseStep 1155595 = 1733393) B1733393
theorem B2564747 : Blo 1136633 2564747 := bstep (se 1 (by rfl) ⟨1923560, by rfl⟩ : syracuseStep 2564747 = 3847121) B3847121
theorem B19473047 : Blo 1136633 19473047 := bstep (se 1 (by rfl) ⟨14604785, by rfl⟩ : syracuseStep 19473047 = 29209571) B29209571
theorem B2564801 : Blo 1136633 2564801 := bstep (se 2 (by rfl) ⟨961800, by rfl⟩ : syracuseStep 2564801 = 1923601) B1923601
theorem B2433739 : Blo 1136633 2433739 := bstep (se 1 (by rfl) ⟨1825304, by rfl⟩ : syracuseStep 2433739 = 3650609) B3650609
theorem B16425773 : Blo 1136633 16425773 := bstep (se 3 (by rfl) ⟨3079832, by rfl⟩ : syracuseStep 16425773 = 6159665) B6159665
theorem B3842909 : Blo 1136633 3842909 := bstep (se 3 (by rfl) ⟨720545, by rfl⟩ : syracuseStep 3842909 = 1441091) B1441091
theorem B2565017 : Blo 1136633 2565017 := bstep (se 2 (by rfl) ⟨961881, by rfl⟩ : syracuseStep 2565017 = 1923763) B1923763
theorem B2565107 : Blo 1136633 2565107 := bstep (se 1 (by rfl) ⟨1923830, by rfl⟩ : syracuseStep 2565107 = 3847661) B3847661
theorem B2565143 : Blo 1136633 2565143 := bstep (se 1 (by rfl) ⟨1923857, by rfl⟩ : syracuseStep 2565143 = 3847715) B3847715
theorem B8660033 : Blo 1136633 8660033 := bstep (se 2 (by rfl) ⟨3247512, by rfl⟩ : syracuseStep 8660033 = 6495025) B6495025
theorem B2565323 : Blo 1136633 2565323 := bstep (se 1 (by rfl) ⟨1923992, by rfl⟩ : syracuseStep 2565323 = 3847985) B3847985
theorem B2565377 : Blo 1136633 2565377 := bstep (se 2 (by rfl) ⟨962016, by rfl⟩ : syracuseStep 2565377 = 1924033) B1924033
theorem B2925899 : Blo 1136633 2925899 := bstep (se 1 (by rfl) ⟨2194424, by rfl⟩ : syracuseStep 2925899 = 4388849) B4388849
theorem B2565593 : Blo 1136633 2565593 := bstep (se 2 (by rfl) ⟨962097, by rfl⟩ : syracuseStep 2565593 = 1924195) B1924195
theorem B2565683 : Blo 1136633 2565683 := bstep (se 1 (by rfl) ⟨1924262, by rfl⟩ : syracuseStep 2565683 = 3848525) B3848525
theorem B2565719 : Blo 1136633 2565719 := bstep (se 1 (by rfl) ⟨1924289, by rfl⟩ : syracuseStep 2565719 = 3848579) B3848579
theorem B4859651 : Blo 1136633 4859651 := bstep (se 1 (by rfl) ⟨3644738, by rfl⟩ : syracuseStep 4859651 = 7289477) B7289477
theorem B2565899 : Blo 1136633 2565899 := bstep (se 1 (by rfl) ⟨1924424, by rfl⟩ : syracuseStep 2565899 = 3848849) B3848849
theorem B2565953 : Blo 1136633 2565953 := bstep (se 2 (by rfl) ⟨962232, by rfl⟩ : syracuseStep 2565953 = 1924465) B1924465
theorem B8202161 : Blo 1136633 8202161 := bstep (se 2 (by rfl) ⟨3075810, by rfl⟩ : syracuseStep 8202161 = 6151621) B6151621
theorem B3844043 : Blo 1136633 3844043 := bstep (se 1 (by rfl) ⟨2883032, by rfl⟩ : syracuseStep 3844043 = 5766065) B5766065
theorem B2566169 : Blo 1136633 2566169 := bstep (se 2 (by rfl) ⟨962313, by rfl⟩ : syracuseStep 2566169 = 1924627) B1924627
theorem B37890083 : Blo 1136633 37890083 := bstep (se 1 (by rfl) ⟨28417562, by rfl⟩ : syracuseStep 37890083 = 56835125) B56835125
theorem B2435123 : Blo 1136633 2435123 := bstep (se 1 (by rfl) ⟨1826342, by rfl⟩ : syracuseStep 2435123 = 3652685) B3652685
theorem B4106315 : Blo 1136633 4106315 := bstep (se 1 (by rfl) ⟨3079736, by rfl⟩ : syracuseStep 4106315 = 6159473) B6159473
theorem B4859993 : Blo 1136633 4859993 := bstep (se 2 (by rfl) ⟨1822497, by rfl⟩ : syracuseStep 4859993 = 3644995) B3644995
theorem B2566259 : Blo 1136633 2566259 := bstep (se 1 (by rfl) ⟨1924694, by rfl⟩ : syracuseStep 2566259 = 3849389) B3849389
theorem B6924419 : Blo 1136633 6924419 := bstep (se 1 (by rfl) ⟨5193314, by rfl⟩ : syracuseStep 6924419 = 10386629) B10386629
theorem B2566295 : Blo 1136633 2566295 := bstep (se 1 (by rfl) ⟨1924721, by rfl⟩ : syracuseStep 2566295 = 3849443) B3849443
theorem B3844313 : Blo 1136633 3844313 := bstep (se 2 (by rfl) ⟨1441617, by rfl⟩ : syracuseStep 3844313 = 2883235) B2883235
theorem B2599193 : Blo 1136633 2599193 := bstep (se 2 (by rfl) ⟨974697, by rfl⟩ : syracuseStep 2599193 = 1949395) B1949395
theorem B6924761 : Blo 1136633 6924761 := bstep (se 2 (by rfl) ⟨2596785, by rfl⟩ : syracuseStep 6924761 = 5193571) B5193571
theorem B9742949 : Blo 1136633 9742949 := bstep (se 4 (by rfl) ⟨913401, by rfl⟩ : syracuseStep 9742949 = 1826803) B1826803
theorem B1846039 : Blo 1136633 1846039 := bstep (se 1 (by rfl) ⟨1384529, by rfl⟩ : syracuseStep 1846039 = 2769059) B2769059
theorem B2599705 : Blo 1136633 2599705 := bstep (se 2 (by rfl) ⟨974889, by rfl⟩ : syracuseStep 2599705 = 1949779) B1949779
theorem B2435969 : Blo 1136633 2435969 := bstep (se 2 (by rfl) ⟨913488, by rfl⟩ : syracuseStep 2435969 = 1826977) B1826977
theorem B3845015 : Blo 1136633 3845015 := bstep (se 1 (by rfl) ⟨2883761, by rfl⟩ : syracuseStep 3845015 = 5767523) B5767523
theorem B35105861 : Blo 1136633 35105861 := bstep (se 4 (by rfl) ⟨3291174, by rfl⟩ : syracuseStep 35105861 = 6582349) B6582349
theorem B3845555 : Blo 1136633 3845555 := bstep (se 1 (by rfl) ⟨2884166, by rfl⟩ : syracuseStep 3845555 = 5768333) B5768333
theorem B10956323 : Blo 1136633 10956323 := bstep (se 1 (by rfl) ⟨8217242, by rfl⟩ : syracuseStep 10956323 = 16434485) B16434485
theorem B2305651 : Blo 1136633 2305651 := bstep (se 1 (by rfl) ⟨1729238, by rfl⟩ : syracuseStep 2305651 = 3458477) B3458477
theorem B2305675 : Blo 1136633 2305675 := bstep (se 1 (by rfl) ⟨1729256, by rfl⟩ : syracuseStep 2305675 = 3458513) B3458513
theorem B4861633 : Blo 1136633 4861633 := bstep (se 2 (by rfl) ⟨1823112, by rfl⟩ : syracuseStep 4861633 = 3646225) B3646225
theorem B3845825 : Blo 1136633 3845825 := bstep (se 2 (by rfl) ⟨1442184, by rfl⟩ : syracuseStep 3845825 = 2884369) B2884369
theorem B2633473 : Blo 1136633 2633473 := bstep (se 2 (by rfl) ⟨987552, by rfl⟩ : syracuseStep 2633473 = 1975105) B1975105
theorem B9219845 : Blo 1136633 9219845 := bstep (se 4 (by rfl) ⟨864360, by rfl⟩ : syracuseStep 9219845 = 1728721) B1728721
theorem B1945559 : Blo 1136633 1945559 := bstep (se 1 (by rfl) ⟨1459169, by rfl⟩ : syracuseStep 1945559 = 2918339) B2918339
theorem B3846365 : Blo 1136633 3846365 := bstep (se 3 (by rfl) ⟨721193, by rfl⟩ : syracuseStep 3846365 = 1442387) B1442387
theorem B2732363 : Blo 1136633 2732363 := bstep (se 1 (by rfl) ⟨2049272, by rfl⟩ : syracuseStep 2732363 = 4098545) B4098545
theorem B1847767 : Blo 1136633 1847767 := bstep (se 1 (by rfl) ⟨1385825, by rfl⟩ : syracuseStep 1847767 = 2771651) B2771651
theorem B2306713 : Blo 1136633 2306713 := bstep (se 2 (by rfl) ⟨865017, by rfl⟩ : syracuseStep 2306713 = 1730035) B1730035
theorem B1618699 : Blo 1136633 1618699 := bstep (se 1 (by rfl) ⟨1214024, by rfl⟩ : syracuseStep 1618699 = 2428049) B2428049
theorem B1618967 : Blo 1136633 1618967 := bstep (se 1 (by rfl) ⟨1214225, by rfl⟩ : syracuseStep 1618967 = 2428451) B2428451
theorem B21050549 : Blo 1136633 21050549 := bstep (se 5 (by rfl) ⟨986744, by rfl⟩ : syracuseStep 21050549 = 1973489) B1973489
theorem B3847499 : Blo 1136633 3847499 := bstep (se 1 (by rfl) ⟨2885624, by rfl⟩ : syracuseStep 3847499 = 5771249) B5771249
theorem B2733401 : Blo 1136633 2733401 := bstep (se 2 (by rfl) ⟨1025025, by rfl⟩ : syracuseStep 2733401 = 2050051) B2050051
theorem B3651095 : Blo 1136633 3651095 := bstep (se 1 (by rfl) ⟨2738321, by rfl⟩ : syracuseStep 3651095 = 5476643) B5476643
theorem B3847769 : Blo 1136633 3847769 := bstep (se 2 (by rfl) ⟨1442913, by rfl⟩ : syracuseStep 3847769 = 2885827) B2885827
theorem B7288451 : Blo 1136633 7288451 := bstep (se 1 (by rfl) ⟨5466338, by rfl⟩ : syracuseStep 7288451 = 10932677) B10932677
theorem B9713357 : Blo 1136633 9713357 := bstep (se 3 (by rfl) ⟨1821254, by rfl⟩ : syracuseStep 9713357 = 3642509) B3642509
theorem B2307799 : Blo 1136633 2307799 := bstep (se 1 (by rfl) ⟨1730849, by rfl⟩ : syracuseStep 2307799 = 3461699) B3461699
theorem B1619929 : Blo 1136633 1619929 := bstep (se 2 (by rfl) ⟨607473, by rfl⟩ : syracuseStep 1619929 = 1214947) B1214947
theorem B9222245 : Blo 1136633 9222245 := bstep (se 4 (by rfl) ⟨864585, by rfl⟩ : syracuseStep 9222245 = 1729171) B1729171
theorem B3848471 : Blo 1136633 3848471 := bstep (se 1 (by rfl) ⟨2886353, by rfl⟩ : syracuseStep 3848471 = 5772707) B5772707
theorem B2308505 : Blo 1136633 2308505 := bstep (se 2 (by rfl) ⟨865689, by rfl⟩ : syracuseStep 2308505 = 1731379) B1731379
theorem B4438745 : Blo 1136633 4438745 := bstep (se 2 (by rfl) ⟨1664529, by rfl⟩ : syracuseStep 4438745 = 3329059) B3329059
theorem B3849011 : Blo 1136633 3849011 := bstep (se 1 (by rfl) ⟨2886758, by rfl⟩ : syracuseStep 3849011 = 5773517) B5773517
theorem B3652427 : Blo 1136633 3652427 := bstep (se 1 (by rfl) ⟨2739320, by rfl⟩ : syracuseStep 3652427 = 5478641) B5478641
theorem B3849281 : Blo 1136633 3849281 := bstep (se 2 (by rfl) ⟨1443480, by rfl⟩ : syracuseStep 3849281 = 2886961) B2886961
theorem B1621387 : Blo 1136633 1621387 := bstep (se 1 (by rfl) ⟨1216040, by rfl⟩ : syracuseStep 1621387 = 2432081) B2432081
theorem B1621399 : Blo 1136633 1621399 := bstep (se 1 (by rfl) ⟨1216049, by rfl⟩ : syracuseStep 1621399 = 2432099) B2432099
theorem B3653171 : Blo 1136633 3653171 := bstep (se 1 (by rfl) ⟨2739878, by rfl⟩ : syracuseStep 3653171 = 5479757) B5479757
theorem B6929995 : Blo 1136633 6929995 := bstep (se 1 (by rfl) ⟨5197496, by rfl⟩ : syracuseStep 6929995 = 10394993) B10394993
theorem B18497099 : Blo 1136633 18497099 := bstep (se 1 (by rfl) ⟨13872824, by rfl⟩ : syracuseStep 18497099 = 27745649) B27745649
theorem B8306705 : Blo 1136633 8306705 := bstep (se 2 (by rfl) ⟨3115014, by rfl⟩ : syracuseStep 8306705 = 6230029) B6230029
theorem B9715747 : Blo 1136633 9715747 := bstep (se 1 (by rfl) ⟨7286810, by rfl⟩ : syracuseStep 9715747 = 14573621) B14573621
theorem B2048257 : Blo 1136633 2048257 := bstep (se 2 (by rfl) ⟨768096, by rfl⟩ : syracuseStep 2048257 = 1536193) B1536193
theorem B2048321 : Blo 1136633 2048321 := bstep (se 2 (by rfl) ⟨768120, by rfl⟩ : syracuseStep 2048321 = 1536241) B1536241
theorem B6570341 : Blo 1136633 6570341 := bstep (se 4 (by rfl) ⟨615969, by rfl⟩ : syracuseStep 6570341 = 1231939) B1231939
theorem B3654067 : Blo 1136633 3654067 := bstep (se 1 (by rfl) ⟨2740550, by rfl⟩ : syracuseStep 3654067 = 5481101) B5481101
theorem B15582017 : Blo 1136633 15582017 := bstep (se 2 (by rfl) ⟨5843256, by rfl⟩ : syracuseStep 15582017 = 11686513) B11686513
theorem B5194775 : Blo 1136633 5194775 := bstep (se 1 (by rfl) ⟨3896081, by rfl⟩ : syracuseStep 5194775 = 7792163) B7792163
theorem B5850157 : Blo 1136633 5850157 := bstep (se 3 (by rfl) ⟨1096904, by rfl⟩ : syracuseStep 5850157 = 2193809) B2193809
theorem B1623449 : Blo 1136633 1623449 := bstep (se 2 (by rfl) ⟨608793, by rfl⟩ : syracuseStep 1623449 = 1217587) B1217587
theorem B4867715 : Blo 1136633 4867715 := bstep (se 1 (by rfl) ⟨3650786, by rfl⟩ : syracuseStep 4867715 = 7301573) B7301573
theorem B1918667 : Blo 1136633 1918667 := bstep (se 1 (by rfl) ⟨1439000, by rfl⟩ : syracuseStep 1918667 = 2878001) B2878001
theorem B12306181 : Blo 1136633 12306181 := bstep (se 4 (by rfl) ⟨1153704, by rfl⟩ : syracuseStep 12306181 = 2307409) B2307409
theorem B1918795 : Blo 1136633 1918795 := bstep (se 1 (by rfl) ⟨1439096, by rfl⟩ : syracuseStep 1918795 = 2878193) B2878193
theorem B1918937 : Blo 1136633 1918937 := bstep (se 2 (by rfl) ⟨719601, by rfl⟩ : syracuseStep 1918937 = 1439203) B1439203
theorem B1919065 : Blo 1136633 1919065 := bstep (se 2 (by rfl) ⟨719649, by rfl⟩ : syracuseStep 1919065 = 1439299) B1439299
theorem B1460363 : Blo 1136633 1460363 := bstep (se 1 (by rfl) ⟨1095272, by rfl⟩ : syracuseStep 1460363 = 2190545) B2190545
theorem B32786957 : Blo 1136633 32786957 := bstep (se 3 (by rfl) ⟨6147554, by rfl⟩ : syracuseStep 32786957 = 12295109) B12295109
theorem B21088781 : Blo 1136633 21088781 := bstep (se 3 (by rfl) ⟨3954146, by rfl⟩ : syracuseStep 21088781 = 7908293) B7908293
theorem B8538641 : Blo 1136633 8538641 := bstep (se 2 (by rfl) ⟨3201990, by rfl⟩ : syracuseStep 8538641 = 6403981) B6403981
theorem B1297015 : Blo 1136633 1297015 := bstep (se 1 (by rfl) ⟨972761, by rfl⟩ : syracuseStep 1297015 = 1945523) B1945523
theorem B1919639 : Blo 1136633 1919639 := bstep (se 1 (by rfl) ⟨1439729, by rfl⟩ : syracuseStep 1919639 = 2879459) B2879459
theorem B1919767 : Blo 1136633 1919767 := bstep (se 1 (by rfl) ⟨1439825, by rfl⟩ : syracuseStep 1919767 = 2879651) B2879651
theorem B9849701 : Blo 1136633 9849701 := bstep (se 4 (by rfl) ⟨923409, by rfl⟩ : syracuseStep 9849701 = 1846819) B1846819
theorem B4934807 : Blo 1136633 4934807 := bstep (se 1 (by rfl) ⟨3701105, by rfl⟩ : syracuseStep 4934807 = 7402211) B7402211
theorem B4869341 : Blo 1136633 4869341 := bstep (se 3 (by rfl) ⟨913001, by rfl⟩ : syracuseStep 4869341 = 1826003) B1826003
theorem B12963077 : Blo 1136633 12963077 := bstep (se 4 (by rfl) ⟨1215288, by rfl⟩ : syracuseStep 12963077 = 2430577) B2430577
theorem B6475139 : Blo 1136633 6475139 := bstep (se 1 (by rfl) ⟨4856354, by rfl⟩ : syracuseStep 6475139 = 9712709) B9712709
theorem B1920395 : Blo 1136633 1920395 := bstep (se 1 (by rfl) ⟨1440296, by rfl⟩ : syracuseStep 1920395 = 2880593) B2880593
theorem B1920523 : Blo 1136633 1920523 := bstep (se 1 (by rfl) ⟨1440392, by rfl⟩ : syracuseStep 1920523 = 2880785) B2880785
theorem B22171153 : Blo 1136633 22171153 := bstep (se 2 (by rfl) ⟨8314182, by rfl⟩ : syracuseStep 22171153 = 16628365) B16628365
theorem B2051659 : Blo 1136633 2051659 := bstep (se 1 (by rfl) ⟨1538744, by rfl⟩ : syracuseStep 2051659 = 3077489) B3077489
theorem B2051723 : Blo 1136633 2051723 := bstep (se 1 (by rfl) ⟨1538792, by rfl⟩ : syracuseStep 2051723 = 3077585) B3077585
theorem B1920665 : Blo 1136633 1920665 := bstep (se 2 (by rfl) ⟨720249, by rfl⟩ : syracuseStep 1920665 = 1440499) B1440499
theorem B1920793 : Blo 1136633 1920793 := bstep (se 2 (by rfl) ⟨720297, by rfl⟩ : syracuseStep 1920793 = 1440595) B1440595
theorem B246271843 : Blo 1136633 246271843 := bstep (se 1 (by rfl) ⟨184703882, by rfl⟩ : syracuseStep 246271843 = 369407765) B369407765
theorem B4870039 : Blo 1136633 4870039 := bstep (se 1 (by rfl) ⟨3652529, by rfl⟩ : syracuseStep 4870039 = 7305059) B7305059
theorem B3461213 : Blo 1136633 3461213 := bstep (se 3 (by rfl) ⟨648977, by rfl⟩ : syracuseStep 3461213 = 1297955) B1297955
theorem B1298539 : Blo 1136633 1298539 := bstep (se 1 (by rfl) ⟨973904, by rfl⟩ : syracuseStep 1298539 = 1947809) B1947809
theorem B5755211 : Blo 1136633 5755211 := bstep (se 1 (by rfl) ⟨4316408, by rfl⟩ : syracuseStep 5755211 = 8632817) B8632817
theorem B1921367 : Blo 1136633 1921367 := bstep (se 1 (by rfl) ⟨1441025, by rfl⟩ : syracuseStep 1921367 = 2882051) B2882051
theorem B7786853 : Blo 1136633 7786853 := bstep (se 4 (by rfl) ⟨730017, by rfl⟩ : syracuseStep 7786853 = 1460035) B1460035
theorem B2052545 : Blo 1136633 2052545 := bstep (se 2 (by rfl) ⟨769704, by rfl⟩ : syracuseStep 2052545 = 1539409) B1539409
theorem B1921495 : Blo 1136633 1921495 := bstep (se 1 (by rfl) ⟨1441121, by rfl⟩ : syracuseStep 1921495 = 2882243) B2882243
theorem B9720395 : Blo 1136633 9720395 := bstep (se 1 (by rfl) ⟨7290296, by rfl⟩ : syracuseStep 9720395 = 14580593) B14580593
theorem B2052697 : Blo 1136633 2052697 := bstep (se 2 (by rfl) ⟨769761, by rfl⟩ : syracuseStep 2052697 = 1539523) B1539523
theorem B6148939 : Blo 1136633 6148939 := bstep (se 1 (by rfl) ⟨4611704, by rfl⟩ : syracuseStep 6148939 = 9223409) B9223409
theorem B2053043 : Blo 1136633 2053043 := bstep (se 1 (by rfl) ⟨1539782, by rfl⟩ : syracuseStep 2053043 = 3079565) B3079565
theorem B1922123 : Blo 1136633 1922123 := bstep (se 1 (by rfl) ⟨1441592, by rfl⟩ : syracuseStep 1922123 = 2883185) B2883185
theorem B1922251 : Blo 1136633 1922251 := bstep (se 1 (by rfl) ⟨1441688, by rfl⟩ : syracuseStep 1922251 = 2883377) B2883377
theorem B4871441 : Blo 1136633 4871441 := bstep (se 2 (by rfl) ⟨1826790, by rfl⟩ : syracuseStep 4871441 = 3653581) B3653581
theorem B1922393 : Blo 1136633 1922393 := bstep (se 2 (by rfl) ⟨720897, by rfl⟩ : syracuseStep 1922393 = 1441795) B1441795
theorem B2053505 : Blo 1136633 2053505 := bstep (se 2 (by rfl) ⟨770064, by rfl⟩ : syracuseStep 2053505 = 1540129) B1540129
theorem B1922521 : Blo 1136633 1922521 := bstep (se 2 (by rfl) ⟨720945, by rfl⟩ : syracuseStep 1922521 = 1441891) B1441891
theorem B19486169 : Blo 1136633 19486169 := bstep (se 2 (by rfl) ⟨7307313, by rfl⟩ : syracuseStep 19486169 = 14614627) B14614627
theorem B1365643 : Blo 1136633 1365643 := bstep (se 1 (by rfl) ⟨1024232, by rfl⟩ : syracuseStep 1365643 = 2048465) B2048465
theorem B19715735 : Blo 1136633 19715735 := bstep (se 1 (by rfl) ⟨14786801, by rfl⟩ : syracuseStep 19715735 = 29573603) B29573603
theorem B6477529 : Blo 1136633 6477529 := bstep (se 2 (by rfl) ⟨2429073, by rfl⟩ : syracuseStep 6477529 = 4858147) B4858147
theorem B1824535 : Blo 1136633 1824535 := bstep (se 1 (by rfl) ⟨1368401, by rfl⟩ : syracuseStep 1824535 = 2736803) B2736803
theorem B33249203 : Blo 1136633 33249203 := bstep (se 1 (by rfl) ⟨24936902, by rfl⟩ : syracuseStep 33249203 = 49873805) B49873805
theorem B2054081 : Blo 1136633 2054081 := bstep (se 2 (by rfl) ⟨770280, by rfl⟩ : syracuseStep 2054081 = 1540561) B1540561
theorem B1136651 : Blo 1136633 1136651 := bstep (se 1 (by rfl) ⟨852488, by rfl⟩ : syracuseStep 1136651 = 1704977) B1704977
theorem B1136663 : Blo 1136633 1136663 := bstep (se 1 (by rfl) ⟨852497, by rfl⟩ : syracuseStep 1136663 = 1704995) B1704995
theorem B1923095 : Blo 1136633 1923095 := bstep (se 1 (by rfl) ⟨1442321, by rfl⟩ : syracuseStep 1923095 = 2884643) B2884643
theorem B1136683 : Blo 1136633 1136683 := bstep (se 1 (by rfl) ⟨852512, by rfl⟩ : syracuseStep 1136683 = 1705025) B1705025
theorem B1136695 : Blo 1136633 1136695 := bstep (se 1 (by rfl) ⟨852521, by rfl⟩ : syracuseStep 1136695 = 1705043) B1705043
theorem B5756993 : Blo 1136633 5756993 := bstep (se 2 (by rfl) ⟨2158872, by rfl⟩ : syracuseStep 5756993 = 4317745) B4317745
theorem B1136715 : Blo 1136633 1136715 := bstep (se 1 (by rfl) ⟨852536, by rfl⟩ : syracuseStep 1136715 = 1705073) B1705073
theorem B1136727 : Blo 1136633 1136727 := bstep (se 1 (by rfl) ⟨852545, by rfl⟩ : syracuseStep 1136727 = 1705091) B1705091
theorem B1136747 : Blo 1136633 1136747 := bstep (se 1 (by rfl) ⟨852560, by rfl⟩ : syracuseStep 1136747 = 1705121) B1705121
theorem B1136759 : Blo 1136633 1136759 := bstep (se 1 (by rfl) ⟨852569, by rfl⟩ : syracuseStep 1136759 = 1705139) B1705139
theorem B1136779 : Blo 1136633 1136779 := bstep (se 1 (by rfl) ⟨852584, by rfl⟩ : syracuseStep 1136779 = 1705169) B1705169
theorem B1136791 : Blo 1136633 1136791 := bstep (se 1 (by rfl) ⟨852593, by rfl⟩ : syracuseStep 1136791 = 1705187) B1705187
theorem B1923223 : Blo 1136633 1923223 := bstep (se 1 (by rfl) ⟨1442417, by rfl⟩ : syracuseStep 1923223 = 2884835) B2884835
theorem B1136811 : Blo 1136633 1136811 := bstep (se 1 (by rfl) ⟨852608, by rfl⟩ : syracuseStep 1136811 = 1705217) B1705217
theorem B1136823 : Blo 1136633 1136823 := bstep (se 1 (by rfl) ⟨852617, by rfl⟩ : syracuseStep 1136823 = 1705235) B1705235
theorem B1136843 : Blo 1136633 1136843 := bstep (se 1 (by rfl) ⟨852632, by rfl⟩ : syracuseStep 1136843 = 1705265) B1705265
theorem B1136855 : Blo 1136633 1136855 := bstep (se 1 (by rfl) ⟨852641, by rfl⟩ : syracuseStep 1136855 = 1705283) B1705283
theorem B1136875 : Blo 1136633 1136875 := bstep (se 1 (by rfl) ⟨852656, by rfl⟩ : syracuseStep 1136875 = 1705313) B1705313
theorem B1136887 : Blo 1136633 1136887 := bstep (se 1 (by rfl) ⟨852665, by rfl⟩ : syracuseStep 1136887 = 1705331) B1705331
theorem B1136907 : Blo 1136633 1136907 := bstep (se 1 (by rfl) ⟨852680, by rfl⟩ : syracuseStep 1136907 = 1705361) B1705361
theorem B1136919 : Blo 1136633 1136919 := bstep (se 1 (by rfl) ⟨852689, by rfl⟩ : syracuseStep 1136919 = 1705379) B1705379
theorem B1136939 : Blo 1136633 1136939 := bstep (se 1 (by rfl) ⟨852704, by rfl⟩ : syracuseStep 1136939 = 1705409) B1705409
theorem B1136951 : Blo 1136633 1136951 := bstep (se 1 (by rfl) ⟨852713, by rfl⟩ : syracuseStep 1136951 = 1705427) B1705427
theorem B1136971 : Blo 1136633 1136971 := bstep (se 1 (by rfl) ⟨852728, by rfl⟩ : syracuseStep 1136971 = 1705457) B1705457
theorem B1136983 : Blo 1136633 1136983 := bstep (se 1 (by rfl) ⟨852737, by rfl⟩ : syracuseStep 1136983 = 1705475) B1705475
theorem B1137003 : Blo 1136633 1137003 := bstep (se 1 (by rfl) ⟨852752, by rfl⟩ : syracuseStep 1137003 = 1705505) B1705505
theorem B1137015 : Blo 1136633 1137015 := bstep (se 1 (by rfl) ⟨852761, by rfl⟩ : syracuseStep 1137015 = 1705523) B1705523
theorem B1137035 : Blo 1136633 1137035 := bstep (se 1 (by rfl) ⟨852776, by rfl⟩ : syracuseStep 1137035 = 1705553) B1705553
theorem B1137047 : Blo 1136633 1137047 := bstep (se 1 (by rfl) ⟨852785, by rfl⟩ : syracuseStep 1137047 = 1705571) B1705571
theorem B1137067 : Blo 1136633 1137067 := bstep (se 1 (by rfl) ⟨852800, by rfl⟩ : syracuseStep 1137067 = 1705601) B1705601
theorem B1137079 : Blo 1136633 1137079 := bstep (se 1 (by rfl) ⟨852809, by rfl⟩ : syracuseStep 1137079 = 1705619) B1705619
theorem B1137099 : Blo 1136633 1137099 := bstep (se 1 (by rfl) ⟨852824, by rfl⟩ : syracuseStep 1137099 = 1705649) B1705649
theorem B1137111 : Blo 1136633 1137111 := bstep (se 1 (by rfl) ⟨852833, by rfl⟩ : syracuseStep 1137111 = 1705667) B1705667
theorem B1137131 : Blo 1136633 1137131 := bstep (se 1 (by rfl) ⟨852848, by rfl⟩ : syracuseStep 1137131 = 1705697) B1705697
theorem B1137143 : Blo 1136633 1137143 := bstep (se 1 (by rfl) ⟨852857, by rfl⟩ : syracuseStep 1137143 = 1705715) B1705715
theorem B1137163 : Blo 1136633 1137163 := bstep (se 1 (by rfl) ⟨852872, by rfl⟩ : syracuseStep 1137163 = 1705745) B1705745
theorem B1825291 : Blo 1136633 1825291 := bstep (se 1 (by rfl) ⟨1368968, by rfl⟩ : syracuseStep 1825291 = 2737937) B2737937
theorem B1137175 : Blo 1136633 1137175 := bstep (se 1 (by rfl) ⟨852881, by rfl⟩ : syracuseStep 1137175 = 1705763) B1705763
theorem B1137195 : Blo 1136633 1137195 := bstep (se 1 (by rfl) ⟨852896, by rfl⟩ : syracuseStep 1137195 = 1705793) B1705793
theorem B1137207 : Blo 1136633 1137207 := bstep (se 1 (by rfl) ⟨852905, by rfl⟩ : syracuseStep 1137207 = 1705811) B1705811
theorem B1137227 : Blo 1136633 1137227 := bstep (se 1 (by rfl) ⟨852920, by rfl⟩ : syracuseStep 1137227 = 1705841) B1705841
theorem B1137239 : Blo 1136633 1137239 := bstep (se 1 (by rfl) ⟨852929, by rfl⟩ : syracuseStep 1137239 = 1705859) B1705859
theorem B1137259 : Blo 1136633 1137259 := bstep (se 1 (by rfl) ⟨852944, by rfl⟩ : syracuseStep 1137259 = 1705889) B1705889
theorem B1137271 : Blo 1136633 1137271 := bstep (se 1 (by rfl) ⟨852953, by rfl⟩ : syracuseStep 1137271 = 1705907) B1705907
theorem B1137291 : Blo 1136633 1137291 := bstep (se 1 (by rfl) ⟨852968, by rfl⟩ : syracuseStep 1137291 = 1705937) B1705937
theorem B1137303 : Blo 1136633 1137303 := bstep (se 1 (by rfl) ⟨852977, by rfl⟩ : syracuseStep 1137303 = 1705955) B1705955
theorem B6478487 : Blo 1136633 6478487 := bstep (se 1 (by rfl) ⟨4858865, by rfl⟩ : syracuseStep 6478487 = 9717731) B9717731
theorem B1137323 : Blo 1136633 1137323 := bstep (se 1 (by rfl) ⟨852992, by rfl⟩ : syracuseStep 1137323 = 1705985) B1705985
theorem B1137335 : Blo 1136633 1137335 := bstep (se 1 (by rfl) ⟨853001, by rfl⟩ : syracuseStep 1137335 = 1706003) B1706003
theorem B1137355 : Blo 1136633 1137355 := bstep (se 1 (by rfl) ⟨853016, by rfl⟩ : syracuseStep 1137355 = 1706033) B1706033
theorem B1137367 : Blo 1136633 1137367 := bstep (se 1 (by rfl) ⟨853025, by rfl⟩ : syracuseStep 1137367 = 1706051) B1706051
theorem B1137387 : Blo 1136633 1137387 := bstep (se 1 (by rfl) ⟨853040, by rfl⟩ : syracuseStep 1137387 = 1706081) B1706081
theorem B1137399 : Blo 1136633 1137399 := bstep (se 1 (by rfl) ⟨853049, by rfl⟩ : syracuseStep 1137399 = 1706099) B1706099
theorem B1137419 : Blo 1136633 1137419 := bstep (se 1 (by rfl) ⟨853064, by rfl⟩ : syracuseStep 1137419 = 1706129) B1706129
theorem B1923851 : Blo 1136633 1923851 := bstep (se 1 (by rfl) ⟨1442888, by rfl⟩ : syracuseStep 1923851 = 2885777) B2885777
theorem B1137431 : Blo 1136633 1137431 := bstep (se 1 (by rfl) ⟨853073, by rfl⟩ : syracuseStep 1137431 = 1706147) B1706147
theorem B1137451 : Blo 1136633 1137451 := bstep (se 1 (by rfl) ⟨853088, by rfl⟩ : syracuseStep 1137451 = 1706177) B1706177
theorem B1137463 : Blo 1136633 1137463 := bstep (se 1 (by rfl) ⟨853097, by rfl⟩ : syracuseStep 1137463 = 1706195) B1706195
theorem B1137483 : Blo 1136633 1137483 := bstep (se 1 (by rfl) ⟨853112, by rfl⟩ : syracuseStep 1137483 = 1706225) B1706225
theorem B1137495 : Blo 1136633 1137495 := bstep (se 1 (by rfl) ⟨853121, by rfl⟩ : syracuseStep 1137495 = 1706243) B1706243
theorem B1137515 : Blo 1136633 1137515 := bstep (se 1 (by rfl) ⟨853136, by rfl⟩ : syracuseStep 1137515 = 1706273) B1706273
theorem B1137527 : Blo 1136633 1137527 := bstep (se 1 (by rfl) ⟨853145, by rfl⟩ : syracuseStep 1137527 = 1706291) B1706291
theorem B1137547 : Blo 1136633 1137547 := bstep (se 1 (by rfl) ⟨853160, by rfl⟩ : syracuseStep 1137547 = 1706321) B1706321
theorem B1923979 : Blo 1136633 1923979 := bstep (se 1 (by rfl) ⟨1442984, by rfl⟩ : syracuseStep 1923979 = 2885969) B2885969
theorem B1137559 : Blo 1136633 1137559 := bstep (se 1 (by rfl) ⟨853169, by rfl⟩ : syracuseStep 1137559 = 1706339) B1706339
theorem B1137579 : Blo 1136633 1137579 := bstep (se 1 (by rfl) ⟨853184, by rfl⟩ : syracuseStep 1137579 = 1706369) B1706369
theorem B1137591 : Blo 1136633 1137591 := bstep (se 1 (by rfl) ⟨853193, by rfl⟩ : syracuseStep 1137591 = 1706387) B1706387
theorem B1137611 : Blo 1136633 1137611 := bstep (se 1 (by rfl) ⟨853208, by rfl⟩ : syracuseStep 1137611 = 1706417) B1706417
theorem B1137623 : Blo 1136633 1137623 := bstep (se 1 (by rfl) ⟨853217, by rfl⟩ : syracuseStep 1137623 = 1706435) B1706435
theorem B1137643 : Blo 1136633 1137643 := bstep (se 1 (by rfl) ⟨853232, by rfl⟩ : syracuseStep 1137643 = 1706465) B1706465
theorem B1137655 : Blo 1136633 1137655 := bstep (se 1 (by rfl) ⟨853241, by rfl⟩ : syracuseStep 1137655 = 1706483) B1706483
theorem B1137675 : Blo 1136633 1137675 := bstep (se 1 (by rfl) ⟨853256, by rfl⟩ : syracuseStep 1137675 = 1706513) B1706513
theorem B1137687 : Blo 1136633 1137687 := bstep (se 1 (by rfl) ⟨853265, by rfl⟩ : syracuseStep 1137687 = 1706531) B1706531
theorem B1924121 : Blo 1136633 1924121 := bstep (se 2 (by rfl) ⟨721545, by rfl⟩ : syracuseStep 1924121 = 1443091) B1443091
theorem B1137707 : Blo 1136633 1137707 := bstep (se 1 (by rfl) ⟨853280, by rfl⟩ : syracuseStep 1137707 = 1706561) B1706561
theorem B1137719 : Blo 1136633 1137719 := bstep (se 1 (by rfl) ⟨853289, by rfl⟩ : syracuseStep 1137719 = 1706579) B1706579
theorem B5332043 : Blo 1136633 5332043 := bstep (se 1 (by rfl) ⟨3999032, by rfl⟩ : syracuseStep 5332043 = 7998065) B7998065
theorem B1137739 : Blo 1136633 1137739 := bstep (se 1 (by rfl) ⟨853304, by rfl⟩ : syracuseStep 1137739 = 1706609) B1706609
theorem B1137751 : Blo 1136633 1137751 := bstep (se 1 (by rfl) ⟨853313, by rfl⟩ : syracuseStep 1137751 = 1706627) B1706627
theorem B1137771 : Blo 1136633 1137771 := bstep (se 1 (by rfl) ⟨853328, by rfl⟩ : syracuseStep 1137771 = 1706657) B1706657
theorem B1137783 : Blo 1136633 1137783 := bstep (se 1 (by rfl) ⟨853337, by rfl⟩ : syracuseStep 1137783 = 1706675) B1706675
theorem B1137803 : Blo 1136633 1137803 := bstep (se 1 (by rfl) ⟨853352, by rfl⟩ : syracuseStep 1137803 = 1706705) B1706705
theorem B1137815 : Blo 1136633 1137815 := bstep (se 1 (by rfl) ⟨853361, by rfl⟩ : syracuseStep 1137815 = 1706723) B1706723
theorem B1924249 : Blo 1136633 1924249 := bstep (se 2 (by rfl) ⟨721593, by rfl⟩ : syracuseStep 1924249 = 1443187) B1443187
theorem B1137835 : Blo 1136633 1137835 := bstep (se 1 (by rfl) ⟨853376, by rfl⟩ : syracuseStep 1137835 = 1706753) B1706753
theorem B1137847 : Blo 1136633 1137847 := bstep (se 1 (by rfl) ⟨853385, by rfl⟩ : syracuseStep 1137847 = 1706771) B1706771
theorem B1137867 : Blo 1136633 1137867 := bstep (se 1 (by rfl) ⟨853400, by rfl⟩ : syracuseStep 1137867 = 1706801) B1706801
theorem B1137879 : Blo 1136633 1137879 := bstep (se 1 (by rfl) ⟨853409, by rfl⟩ : syracuseStep 1137879 = 1706819) B1706819
theorem B2055385 : Blo 1136633 2055385 := bstep (se 2 (by rfl) ⟨770769, by rfl⟩ : syracuseStep 2055385 = 1541539) B1541539
theorem B1137899 : Blo 1136633 1137899 := bstep (se 1 (by rfl) ⟨853424, by rfl⟩ : syracuseStep 1137899 = 1706849) B1706849
theorem B1137911 : Blo 1136633 1137911 := bstep (se 1 (by rfl) ⟨853433, by rfl⟩ : syracuseStep 1137911 = 1706867) B1706867
theorem B1137931 : Blo 1136633 1137931 := bstep (se 1 (by rfl) ⟨853448, by rfl⟩ : syracuseStep 1137931 = 1706897) B1706897
theorem B1137943 : Blo 1136633 1137943 := bstep (se 1 (by rfl) ⟨853457, by rfl⟩ : syracuseStep 1137943 = 1706915) B1706915
theorem B1137963 : Blo 1136633 1137963 := bstep (se 1 (by rfl) ⟨853472, by rfl⟩ : syracuseStep 1137963 = 1706945) B1706945
theorem B1137975 : Blo 1136633 1137975 := bstep (se 1 (by rfl) ⟨853481, by rfl⟩ : syracuseStep 1137975 = 1706963) B1706963
theorem B1137995 : Blo 1136633 1137995 := bstep (se 1 (by rfl) ⟨853496, by rfl⟩ : syracuseStep 1137995 = 1706993) B1706993
theorem B1138007 : Blo 1136633 1138007 := bstep (se 1 (by rfl) ⟨853505, by rfl⟩ : syracuseStep 1138007 = 1707011) B1707011
theorem B1138027 : Blo 1136633 1138027 := bstep (se 1 (by rfl) ⟨853520, by rfl⟩ : syracuseStep 1138027 = 1707041) B1707041
theorem B1138039 : Blo 1136633 1138039 := bstep (se 1 (by rfl) ⟨853529, by rfl⟩ : syracuseStep 1138039 = 1707059) B1707059
theorem B1138059 : Blo 1136633 1138059 := bstep (se 1 (by rfl) ⟨853544, by rfl⟩ : syracuseStep 1138059 = 1707089) B1707089
theorem B4316561 : Blo 1136633 4316561 := bstep (se 2 (by rfl) ⟨1618710, by rfl⟩ : syracuseStep 4316561 = 3237421) B3237421
theorem B1138071 : Blo 1136633 1138071 := bstep (se 1 (by rfl) ⟨853553, by rfl⟩ : syracuseStep 1138071 = 1707107) B1707107
theorem B1138091 : Blo 1136633 1138091 := bstep (se 1 (by rfl) ⟨853568, by rfl⟩ : syracuseStep 1138091 = 1707137) B1707137
theorem B4152755 : Blo 1136633 4152755 := bstep (se 1 (by rfl) ⟨3114566, by rfl⟩ : syracuseStep 4152755 = 6229133) B6229133
theorem B1138103 : Blo 1136633 1138103 := bstep (se 1 (by rfl) ⟨853577, by rfl⟩ : syracuseStep 1138103 = 1707155) B1707155
theorem B1138123 : Blo 1136633 1138123 := bstep (se 1 (by rfl) ⟨853592, by rfl⟩ : syracuseStep 1138123 = 1707185) B1707185
theorem B1138135 : Blo 1136633 1138135 := bstep (se 1 (by rfl) ⟨853601, by rfl⟩ : syracuseStep 1138135 = 1707203) B1707203
theorem B1138155 : Blo 1136633 1138155 := bstep (se 1 (by rfl) ⟨853616, by rfl⟩ : syracuseStep 1138155 = 1707233) B1707233
theorem B1138167 : Blo 1136633 1138167 := bstep (se 1 (by rfl) ⟨853625, by rfl⟩ : syracuseStep 1138167 = 1707251) B1707251
theorem B1138187 : Blo 1136633 1138187 := bstep (se 1 (by rfl) ⟨853640, by rfl⟩ : syracuseStep 1138187 = 1707281) B1707281
theorem B1138199 : Blo 1136633 1138199 := bstep (se 1 (by rfl) ⟨853649, by rfl⟩ : syracuseStep 1138199 = 1707299) B1707299
theorem B1138219 : Blo 1136633 1138219 := bstep (se 1 (by rfl) ⟨853664, by rfl⟩ : syracuseStep 1138219 = 1707329) B1707329
theorem B1138231 : Blo 1136633 1138231 := bstep (se 1 (by rfl) ⟨853673, by rfl⟩ : syracuseStep 1138231 = 1707347) B1707347
theorem B1138251 : Blo 1136633 1138251 := bstep (se 1 (by rfl) ⟨853688, by rfl⟩ : syracuseStep 1138251 = 1707377) B1707377
theorem B1138263 : Blo 1136633 1138263 := bstep (se 1 (by rfl) ⟨853697, by rfl⟩ : syracuseStep 1138263 = 1707395) B1707395
theorem B1826393 : Blo 1136633 1826393 := bstep (se 2 (by rfl) ⟨684897, by rfl⟩ : syracuseStep 1826393 = 1369795) B1369795
theorem B1138283 : Blo 1136633 1138283 := bstep (se 1 (by rfl) ⟨853712, by rfl⟩ : syracuseStep 1138283 = 1707425) B1707425
theorem B1138295 : Blo 1136633 1138295 := bstep (se 1 (by rfl) ⟨853721, by rfl⟩ : syracuseStep 1138295 = 1707443) B1707443
theorem B1138315 : Blo 1136633 1138315 := bstep (se 1 (by rfl) ⟨853736, by rfl⟩ : syracuseStep 1138315 = 1707473) B1707473
theorem B1138327 : Blo 1136633 1138327 := bstep (se 1 (by rfl) ⟨853745, by rfl⟩ : syracuseStep 1138327 = 1707491) B1707491
theorem B7397015 : Blo 1136633 7397015 := bstep (se 1 (by rfl) ⟨5547761, by rfl⟩ : syracuseStep 7397015 = 11095523) B11095523
theorem B1138347 : Blo 1136633 1138347 := bstep (se 1 (by rfl) ⟨853760, by rfl⟩ : syracuseStep 1138347 = 1707521) B1707521
theorem B1138359 : Blo 1136633 1138359 := bstep (se 1 (by rfl) ⟨853769, by rfl⟩ : syracuseStep 1138359 = 1707539) B1707539
theorem B1138379 : Blo 1136633 1138379 := bstep (se 1 (by rfl) ⟨853784, by rfl⟩ : syracuseStep 1138379 = 1707569) B1707569
theorem B1138391 : Blo 1136633 1138391 := bstep (se 1 (by rfl) ⟨853793, by rfl⟩ : syracuseStep 1138391 = 1707587) B1707587
theorem B1138411 : Blo 1136633 1138411 := bstep (se 1 (by rfl) ⟨853808, by rfl⟩ : syracuseStep 1138411 = 1707617) B1707617
theorem B1138423 : Blo 1136633 1138423 := bstep (se 1 (by rfl) ⟨853817, by rfl⟩ : syracuseStep 1138423 = 1707635) B1707635
theorem B1138443 : Blo 1136633 1138443 := bstep (se 1 (by rfl) ⟨853832, by rfl⟩ : syracuseStep 1138443 = 1707665) B1707665
theorem B1138455 : Blo 1136633 1138455 := bstep (se 1 (by rfl) ⟨853841, by rfl⟩ : syracuseStep 1138455 = 1707683) B1707683
theorem B1138475 : Blo 1136633 1138475 := bstep (se 1 (by rfl) ⟨853856, by rfl⟩ : syracuseStep 1138475 = 1707713) B1707713
theorem B14769965 : Blo 1136633 14769965 := bstep (se 3 (by rfl) ⟨2769368, by rfl⟩ : syracuseStep 14769965 = 5538737) B5538737
theorem B1138487 : Blo 1136633 1138487 := bstep (se 1 (by rfl) ⟨853865, by rfl⟩ : syracuseStep 1138487 = 1707731) B1707731
theorem B18472769 : Blo 1136633 18472769 := bstep (se 2 (by rfl) ⟨6927288, by rfl⟩ : syracuseStep 18472769 = 13854577) B13854577
theorem B1138507 : Blo 1136633 1138507 := bstep (se 1 (by rfl) ⟨853880, by rfl⟩ : syracuseStep 1138507 = 1707761) B1707761
theorem B1138519 : Blo 1136633 1138519 := bstep (se 1 (by rfl) ⟨853889, by rfl⟩ : syracuseStep 1138519 = 1707779) B1707779
theorem B7298909 : Blo 1136633 7298909 := bstep (se 3 (by rfl) ⟨1368545, by rfl⟩ : syracuseStep 7298909 = 2737091) B2737091
theorem B1138539 : Blo 1136633 1138539 := bstep (se 1 (by rfl) ⟨853904, by rfl⟩ : syracuseStep 1138539 = 1707809) B1707809
theorem B1138551 : Blo 1136633 1138551 := bstep (se 1 (by rfl) ⟨853913, by rfl⟩ : syracuseStep 1138551 = 1707827) B1707827
theorem B1138571 : Blo 1136633 1138571 := bstep (se 1 (by rfl) ⟨853928, by rfl⟩ : syracuseStep 1138571 = 1707857) B1707857
theorem B1138583 : Blo 1136633 1138583 := bstep (se 1 (by rfl) ⟨853937, by rfl⟩ : syracuseStep 1138583 = 1707875) B1707875
theorem B1138603 : Blo 1136633 1138603 := bstep (se 1 (by rfl) ⟨853952, by rfl⟩ : syracuseStep 1138603 = 1707905) B1707905
theorem B1138615 : Blo 1136633 1138615 := bstep (se 1 (by rfl) ⟨853961, by rfl⟩ : syracuseStep 1138615 = 1707923) B1707923
theorem B1138635 : Blo 1136633 1138635 := bstep (se 1 (by rfl) ⟨853976, by rfl⟩ : syracuseStep 1138635 = 1707953) B1707953
theorem B1138647 : Blo 1136633 1138647 := bstep (se 1 (by rfl) ⟨853985, by rfl⟩ : syracuseStep 1138647 = 1707971) B1707971
theorem B5758937 : Blo 1136633 5758937 := bstep (se 2 (by rfl) ⟨2159601, by rfl⟩ : syracuseStep 5758937 = 4319203) B4319203
theorem B1138667 : Blo 1136633 1138667 := bstep (se 1 (by rfl) ⟨854000, by rfl⟩ : syracuseStep 1138667 = 1708001) B1708001
theorem B1138679 : Blo 1136633 1138679 := bstep (se 1 (by rfl) ⟨854009, by rfl⟩ : syracuseStep 1138679 = 1708019) B1708019
theorem B1138699 : Blo 1136633 1138699 := bstep (se 1 (by rfl) ⟨854024, by rfl⟩ : syracuseStep 1138699 = 1708049) B1708049
theorem B3891223 : Blo 1136633 3891223 := bstep (se 1 (by rfl) ⟨2918417, by rfl⟩ : syracuseStep 3891223 = 5836835) B5836835
theorem B1138711 : Blo 1136633 1138711 := bstep (se 1 (by rfl) ⟨854033, by rfl⟩ : syracuseStep 1138711 = 1708067) B1708067
theorem B1138731 : Blo 1136633 1138731 := bstep (se 1 (by rfl) ⟨854048, by rfl⟩ : syracuseStep 1138731 = 1708097) B1708097
theorem B1138743 : Blo 1136633 1138743 := bstep (se 1 (by rfl) ⟨854057, by rfl⟩ : syracuseStep 1138743 = 1708115) B1708115
theorem B1728587 : Blo 1136633 1728587 := bstep (se 1 (by rfl) ⟨1296440, by rfl⟩ : syracuseStep 1728587 = 2592881) B2592881
theorem B4317259 : Blo 1136633 4317259 := bstep (se 1 (by rfl) ⟨3237944, by rfl⟩ : syracuseStep 4317259 = 6475889) B6475889
theorem B1138763 : Blo 1136633 1138763 := bstep (se 1 (by rfl) ⟨854072, by rfl⟩ : syracuseStep 1138763 = 1708145) B1708145
theorem B1138775 : Blo 1136633 1138775 := bstep (se 1 (by rfl) ⟨854081, by rfl⟩ : syracuseStep 1138775 = 1708163) B1708163
theorem B1138795 : Blo 1136633 1138795 := bstep (se 1 (by rfl) ⟨854096, by rfl⟩ : syracuseStep 1138795 = 1708193) B1708193
theorem B1138807 : Blo 1136633 1138807 := bstep (se 1 (by rfl) ⟨854105, by rfl⟩ : syracuseStep 1138807 = 1708211) B1708211
theorem B1138827 : Blo 1136633 1138827 := bstep (se 1 (by rfl) ⟨854120, by rfl⟩ : syracuseStep 1138827 = 1708241) B1708241
theorem B1138839 : Blo 1136633 1138839 := bstep (se 1 (by rfl) ⟨854129, by rfl⟩ : syracuseStep 1138839 = 1708259) B1708259
theorem B1138859 : Blo 1136633 1138859 := bstep (se 1 (by rfl) ⟨854144, by rfl⟩ : syracuseStep 1138859 = 1708289) B1708289
theorem B1138871 : Blo 1136633 1138871 := bstep (se 1 (by rfl) ⟨854153, by rfl⟩ : syracuseStep 1138871 = 1708307) B1708307
theorem B1138891 : Blo 1136633 1138891 := bstep (se 1 (by rfl) ⟨854168, by rfl⟩ : syracuseStep 1138891 = 1708337) B1708337
theorem B1138903 : Blo 1136633 1138903 := bstep (se 1 (by rfl) ⟨854177, by rfl⟩ : syracuseStep 1138903 = 1708355) B1708355
theorem B1138923 : Blo 1136633 1138923 := bstep (se 1 (by rfl) ⟨854192, by rfl⟩ : syracuseStep 1138923 = 1708385) B1708385
theorem B1138935 : Blo 1136633 1138935 := bstep (se 1 (by rfl) ⟨854201, by rfl⟩ : syracuseStep 1138935 = 1708403) B1708403
theorem B1138955 : Blo 1136633 1138955 := bstep (se 1 (by rfl) ⟨854216, by rfl⟩ : syracuseStep 1138955 = 1708433) B1708433
theorem B1138967 : Blo 1136633 1138967 := bstep (se 1 (by rfl) ⟨854225, by rfl⟩ : syracuseStep 1138967 = 1708451) B1708451
theorem B1138987 : Blo 1136633 1138987 := bstep (se 1 (by rfl) ⟨854240, by rfl⟩ : syracuseStep 1138987 = 1708481) B1708481
theorem B1138999 : Blo 1136633 1138999 := bstep (se 1 (by rfl) ⟨854249, by rfl⟩ : syracuseStep 1138999 = 1708499) B1708499
theorem B1139019 : Blo 1136633 1139019 := bstep (se 1 (by rfl) ⟨854264, by rfl⟩ : syracuseStep 1139019 = 1708529) B1708529
theorem B1139031 : Blo 1136633 1139031 := bstep (se 1 (by rfl) ⟨854273, by rfl⟩ : syracuseStep 1139031 = 1708547) B1708547
theorem B4317533 : Blo 1136633 4317533 := bstep (se 3 (by rfl) ⟨809537, by rfl⟩ : syracuseStep 4317533 = 1619075) B1619075
theorem B1139051 : Blo 1136633 1139051 := bstep (se 1 (by rfl) ⟨854288, by rfl⟩ : syracuseStep 1139051 = 1708577) B1708577
theorem B1139063 : Blo 1136633 1139063 := bstep (se 1 (by rfl) ⟨854297, by rfl⟩ : syracuseStep 1139063 = 1708595) B1708595
theorem B1139083 : Blo 1136633 1139083 := bstep (se 1 (by rfl) ⟨854312, by rfl⟩ : syracuseStep 1139083 = 1708625) B1708625
theorem B1139095 : Blo 1136633 1139095 := bstep (se 1 (by rfl) ⟨854321, by rfl⟩ : syracuseStep 1139095 = 1708643) B1708643
theorem B1139115 : Blo 1136633 1139115 := bstep (se 1 (by rfl) ⟨854336, by rfl⟩ : syracuseStep 1139115 = 1708673) B1708673
theorem B1139127 : Blo 1136633 1139127 := bstep (se 1 (by rfl) ⟨854345, by rfl⟩ : syracuseStep 1139127 = 1708691) B1708691
theorem B1139147 : Blo 1136633 1139147 := bstep (se 1 (by rfl) ⟨854360, by rfl⟩ : syracuseStep 1139147 = 1708721) B1708721
theorem B1139159 : Blo 1136633 1139159 := bstep (se 1 (by rfl) ⟨854369, by rfl⟩ : syracuseStep 1139159 = 1708739) B1708739
theorem B1139179 : Blo 1136633 1139179 := bstep (se 1 (by rfl) ⟨854384, by rfl⟩ : syracuseStep 1139179 = 1708769) B1708769
theorem B1139191 : Blo 1136633 1139191 := bstep (se 1 (by rfl) ⟨854393, by rfl⟩ : syracuseStep 1139191 = 1708787) B1708787
theorem B1139211 : Blo 1136633 1139211 := bstep (se 1 (by rfl) ⟨854408, by rfl⟩ : syracuseStep 1139211 = 1708817) B1708817
theorem B1139223 : Blo 1136633 1139223 := bstep (se 1 (by rfl) ⟨854417, by rfl⟩ : syracuseStep 1139223 = 1708835) B1708835
theorem B1139243 : Blo 1136633 1139243 := bstep (se 1 (by rfl) ⟨854432, by rfl⟩ : syracuseStep 1139243 = 1708865) B1708865
theorem B1139255 : Blo 1136633 1139255 := bstep (se 1 (by rfl) ⟨854441, by rfl⟩ : syracuseStep 1139255 = 1708883) B1708883
theorem B1139275 : Blo 1136633 1139275 := bstep (se 1 (by rfl) ⟨854456, by rfl⟩ : syracuseStep 1139275 = 1708913) B1708913
theorem B1139287 : Blo 1136633 1139287 := bstep (se 1 (by rfl) ⟨854465, by rfl⟩ : syracuseStep 1139287 = 1708931) B1708931
theorem B4448857 : Blo 1136633 4448857 := bstep (se 2 (by rfl) ⟨1668321, by rfl⟩ : syracuseStep 4448857 = 3336643) B3336643
theorem B1139307 : Blo 1136633 1139307 := bstep (se 1 (by rfl) ⟨854480, by rfl⟩ : syracuseStep 1139307 = 1708961) B1708961
theorem B1139319 : Blo 1136633 1139319 := bstep (se 1 (by rfl) ⟨854489, by rfl⟩ : syracuseStep 1139319 = 1708979) B1708979
theorem B1139339 : Blo 1136633 1139339 := bstep (se 1 (by rfl) ⟨854504, by rfl⟩ : syracuseStep 1139339 = 1709009) B1709009
theorem B1139351 : Blo 1136633 1139351 := bstep (se 1 (by rfl) ⟨854513, by rfl⟩ : syracuseStep 1139351 = 1709027) B1709027
theorem B1139371 : Blo 1136633 1139371 := bstep (se 1 (by rfl) ⟨854528, by rfl⟩ : syracuseStep 1139371 = 1709057) B1709057
theorem B1139383 : Blo 1136633 1139383 := bstep (se 1 (by rfl) ⟨854537, by rfl⟩ : syracuseStep 1139383 = 1709075) B1709075
theorem B1139403 : Blo 1136633 1139403 := bstep (se 1 (by rfl) ⟨854552, by rfl⟩ : syracuseStep 1139403 = 1709105) B1709105
theorem B1139415 : Blo 1136633 1139415 := bstep (se 1 (by rfl) ⟨854561, by rfl⟩ : syracuseStep 1139415 = 1709123) B1709123
theorem B6152921 : Blo 1136633 6152921 := bstep (se 2 (by rfl) ⟨2307345, by rfl⟩ : syracuseStep 6152921 = 4614691) B4614691
theorem B1139435 : Blo 1136633 1139435 := bstep (se 1 (by rfl) ⟨854576, by rfl⟩ : syracuseStep 1139435 = 1709153) B1709153
theorem B1139447 : Blo 1136633 1139447 := bstep (se 1 (by rfl) ⟨854585, by rfl⟩ : syracuseStep 1139447 = 1709171) B1709171
theorem B1139467 : Blo 1136633 1139467 := bstep (se 1 (by rfl) ⟨854600, by rfl⟩ : syracuseStep 1139467 = 1709201) B1709201
theorem B1139479 : Blo 1136633 1139479 := bstep (se 1 (by rfl) ⟨854609, by rfl⟩ : syracuseStep 1139479 = 1709219) B1709219
theorem B1139499 : Blo 1136633 1139499 := bstep (se 1 (by rfl) ⟨854624, by rfl⟩ : syracuseStep 1139499 = 1709249) B1709249
theorem B1139511 : Blo 1136633 1139511 := bstep (se 1 (by rfl) ⟨854633, by rfl⟩ : syracuseStep 1139511 = 1709267) B1709267
theorem B1139531 : Blo 1136633 1139531 := bstep (se 1 (by rfl) ⟨854648, by rfl⟩ : syracuseStep 1139531 = 1709297) B1709297
theorem B1139543 : Blo 1136633 1139543 := bstep (se 1 (by rfl) ⟨854657, by rfl⟩ : syracuseStep 1139543 = 1709315) B1709315
theorem B1139563 : Blo 1136633 1139563 := bstep (se 1 (by rfl) ⟨854672, by rfl⟩ : syracuseStep 1139563 = 1709345) B1709345
theorem B1139575 : Blo 1136633 1139575 := bstep (se 1 (by rfl) ⟨854681, by rfl⟩ : syracuseStep 1139575 = 1709363) B1709363
theorem B1139595 : Blo 1136633 1139595 := bstep (se 1 (by rfl) ⟨854696, by rfl⟩ : syracuseStep 1139595 = 1709393) B1709393
theorem B1139607 : Blo 1136633 1139607 := bstep (se 1 (by rfl) ⟨854705, by rfl⟩ : syracuseStep 1139607 = 1709411) B1709411
theorem B1139627 : Blo 1136633 1139627 := bstep (se 1 (by rfl) ⟨854720, by rfl⟩ : syracuseStep 1139627 = 1709441) B1709441
theorem B1139639 : Blo 1136633 1139639 := bstep (se 1 (by rfl) ⟨854729, by rfl⟩ : syracuseStep 1139639 = 1709459) B1709459
theorem B1139659 : Blo 1136633 1139659 := bstep (se 1 (by rfl) ⟨854744, by rfl⟩ : syracuseStep 1139659 = 1709489) B1709489
theorem B1139671 : Blo 1136633 1139671 := bstep (se 1 (by rfl) ⟨854753, by rfl⟩ : syracuseStep 1139671 = 1709507) B1709507
theorem B1139691 : Blo 1136633 1139691 := bstep (se 1 (by rfl) ⟨854768, by rfl⟩ : syracuseStep 1139691 = 1709537) B1709537
theorem B1139703 : Blo 1136633 1139703 := bstep (se 1 (by rfl) ⟨854777, by rfl⟩ : syracuseStep 1139703 = 1709555) B1709555
theorem B1139723 : Blo 1136633 1139723 := bstep (se 1 (by rfl) ⟨854792, by rfl⟩ : syracuseStep 1139723 = 1709585) B1709585
theorem B4318231 : Blo 1136633 4318231 := bstep (se 1 (by rfl) ⟨3238673, by rfl⟩ : syracuseStep 4318231 = 6477347) B6477347
theorem B1139735 : Blo 1136633 1139735 := bstep (se 1 (by rfl) ⟨854801, by rfl⟩ : syracuseStep 1139735 = 1709603) B1709603
theorem B1139755 : Blo 1136633 1139755 := bstep (se 1 (by rfl) ⟨854816, by rfl⟩ : syracuseStep 1139755 = 1709633) B1709633
theorem B1139767 : Blo 1136633 1139767 := bstep (se 1 (by rfl) ⟨854825, by rfl⟩ : syracuseStep 1139767 = 1709651) B1709651
theorem B6480971 : Blo 1136633 6480971 := bstep (se 1 (by rfl) ⟨4860728, by rfl⟩ : syracuseStep 6480971 = 9721457) B9721457
theorem B1139787 : Blo 1136633 1139787 := bstep (se 1 (by rfl) ⟨854840, by rfl⟩ : syracuseStep 1139787 = 1709681) B1709681
theorem B1139799 : Blo 1136633 1139799 := bstep (se 1 (by rfl) ⟨854849, by rfl⟩ : syracuseStep 1139799 = 1709699) B1709699
theorem B1139819 : Blo 1136633 1139819 := bstep (se 1 (by rfl) ⟨854864, by rfl⟩ : syracuseStep 1139819 = 1709729) B1709729
theorem B1139831 : Blo 1136633 1139831 := bstep (se 1 (by rfl) ⟨854873, by rfl⟩ : syracuseStep 1139831 = 1709747) B1709747
theorem B1139851 : Blo 1136633 1139851 := bstep (se 1 (by rfl) ⟨854888, by rfl⟩ : syracuseStep 1139851 = 1709777) B1709777
theorem B17523863 : Blo 1136633 17523863 := bstep (se 1 (by rfl) ⟨13142897, by rfl⟩ : syracuseStep 17523863 = 26285795) B26285795
theorem B1139863 : Blo 1136633 1139863 := bstep (se 1 (by rfl) ⟨854897, by rfl⟩ : syracuseStep 1139863 = 1709795) B1709795
theorem B1139883 : Blo 1136633 1139883 := bstep (se 1 (by rfl) ⟨854912, by rfl⟩ : syracuseStep 1139883 = 1709825) B1709825
theorem B4678829 : Blo 1136633 4678829 := bstep (se 3 (by rfl) ⟨877280, by rfl⟩ : syracuseStep 4678829 = 1754561) B1754561
theorem B1139895 : Blo 1136633 1139895 := bstep (se 1 (by rfl) ⟨854921, by rfl⟩ : syracuseStep 1139895 = 1709843) B1709843
theorem B1139915 : Blo 1136633 1139915 := bstep (se 1 (by rfl) ⟨854936, by rfl⟩ : syracuseStep 1139915 = 1709873) B1709873
theorem B1139927 : Blo 1136633 1139927 := bstep (se 1 (by rfl) ⟨854945, by rfl⟩ : syracuseStep 1139927 = 1709891) B1709891
theorem B1139947 : Blo 1136633 1139947 := bstep (se 1 (by rfl) ⟨854960, by rfl⟩ : syracuseStep 1139947 = 1709921) B1709921
theorem B1139959 : Blo 1136633 1139959 := bstep (se 1 (by rfl) ⟨854969, by rfl⟩ : syracuseStep 1139959 = 1709939) B1709939
theorem B1139979 : Blo 1136633 1139979 := bstep (se 1 (by rfl) ⟨854984, by rfl⟩ : syracuseStep 1139979 = 1709969) B1709969
theorem B1139991 : Blo 1136633 1139991 := bstep (se 1 (by rfl) ⟨854993, by rfl⟩ : syracuseStep 1139991 = 1709987) B1709987
theorem B1140011 : Blo 1136633 1140011 := bstep (se 1 (by rfl) ⟨855008, by rfl⟩ : syracuseStep 1140011 = 1710017) B1710017
theorem B1140023 : Blo 1136633 1140023 := bstep (se 1 (by rfl) ⟨855017, by rfl⟩ : syracuseStep 1140023 = 1710035) B1710035
theorem B1140043 : Blo 1136633 1140043 := bstep (se 1 (by rfl) ⟨855032, by rfl⟩ : syracuseStep 1140043 = 1710065) B1710065
theorem B1140055 : Blo 1136633 1140055 := bstep (se 1 (by rfl) ⟨855041, by rfl⟩ : syracuseStep 1140055 = 1710083) B1710083
theorem B1140075 : Blo 1136633 1140075 := bstep (se 1 (by rfl) ⟨855056, by rfl⟩ : syracuseStep 1140075 = 1710113) B1710113
theorem B1140087 : Blo 1136633 1140087 := bstep (se 1 (by rfl) ⟨855065, by rfl⟩ : syracuseStep 1140087 = 1710131) B1710131
theorem B1140107 : Blo 1136633 1140107 := bstep (se 1 (by rfl) ⟨855080, by rfl⟩ : syracuseStep 1140107 = 1710161) B1710161
theorem B5465495 : Blo 1136633 5465495 := bstep (se 1 (by rfl) ⟨4099121, by rfl⟩ : syracuseStep 5465495 = 8198243) B8198243
theorem B1140119 : Blo 1136633 1140119 := bstep (se 1 (by rfl) ⟨855089, by rfl⟩ : syracuseStep 1140119 = 1710179) B1710179
theorem B1140139 : Blo 1136633 1140139 := bstep (se 1 (by rfl) ⟨855104, by rfl⟩ : syracuseStep 1140139 = 1710209) B1710209
theorem B1140151 : Blo 1136633 1140151 := bstep (se 1 (by rfl) ⟨855113, by rfl⟩ : syracuseStep 1140151 = 1710227) B1710227
theorem B1140171 : Blo 1136633 1140171 := bstep (se 1 (by rfl) ⟨855128, by rfl⟩ : syracuseStep 1140171 = 1710257) B1710257
theorem B1140183 : Blo 1136633 1140183 := bstep (se 1 (by rfl) ⟨855137, by rfl⟩ : syracuseStep 1140183 = 1710275) B1710275
theorem B1140203 : Blo 1136633 1140203 := bstep (se 1 (by rfl) ⟨855152, by rfl⟩ : syracuseStep 1140203 = 1710305) B1710305
theorem B1140215 : Blo 1136633 1140215 := bstep (se 1 (by rfl) ⟨855161, by rfl⟩ : syracuseStep 1140215 = 1710323) B1710323
theorem B1140235 : Blo 1136633 1140235 := bstep (se 1 (by rfl) ⟨855176, by rfl⟩ : syracuseStep 1140235 = 1710353) B1710353
theorem B1140247 : Blo 1136633 1140247 := bstep (se 1 (by rfl) ⟨855185, by rfl⟩ : syracuseStep 1140247 = 1710371) B1710371
theorem B1140267 : Blo 1136633 1140267 := bstep (se 1 (by rfl) ⟨855200, by rfl⟩ : syracuseStep 1140267 = 1710401) B1710401
theorem B5760557 : Blo 1136633 5760557 := bstep (se 3 (by rfl) ⟨1080104, by rfl⟩ : syracuseStep 5760557 = 2160209) B2160209
theorem B1140279 : Blo 1136633 1140279 := bstep (se 1 (by rfl) ⟨855209, by rfl⟩ : syracuseStep 1140279 = 1710419) B1710419
theorem B1140299 : Blo 1136633 1140299 := bstep (se 1 (by rfl) ⟨855224, by rfl⟩ : syracuseStep 1140299 = 1710449) B1710449
theorem B1140311 : Blo 1136633 1140311 := bstep (se 1 (by rfl) ⟨855233, by rfl⟩ : syracuseStep 1140311 = 1710467) B1710467
theorem B1140331 : Blo 1136633 1140331 := bstep (se 1 (by rfl) ⟨855248, by rfl⟩ : syracuseStep 1140331 = 1710497) B1710497
theorem B1140343 : Blo 1136633 1140343 := bstep (se 1 (by rfl) ⟨855257, by rfl⟩ : syracuseStep 1140343 = 1710515) B1710515
theorem B1140363 : Blo 1136633 1140363 := bstep (se 1 (by rfl) ⟨855272, by rfl⟩ : syracuseStep 1140363 = 1710545) B1710545
theorem B1140375 : Blo 1136633 1140375 := bstep (se 1 (by rfl) ⟨855281, by rfl⟩ : syracuseStep 1140375 = 1710563) B1710563
theorem B1140395 : Blo 1136633 1140395 := bstep (se 1 (by rfl) ⟨855296, by rfl⟩ : syracuseStep 1140395 = 1710593) B1710593
theorem B1140407 : Blo 1136633 1140407 := bstep (se 1 (by rfl) ⟨855305, by rfl⟩ : syracuseStep 1140407 = 1710611) B1710611
theorem B1140427 : Blo 1136633 1140427 := bstep (se 1 (by rfl) ⟨855320, by rfl⟩ : syracuseStep 1140427 = 1710641) B1710641
theorem B1140439 : Blo 1136633 1140439 := bstep (se 1 (by rfl) ⟨855329, by rfl⟩ : syracuseStep 1140439 = 1710659) B1710659
theorem B1140459 : Blo 1136633 1140459 := bstep (se 1 (by rfl) ⟨855344, by rfl⟩ : syracuseStep 1140459 = 1710689) B1710689
theorem B1140471 : Blo 1136633 1140471 := bstep (se 1 (by rfl) ⟨855353, by rfl⟩ : syracuseStep 1140471 = 1710707) B1710707
theorem B20801285 : Blo 1136633 20801285 := bstep (se 4 (by rfl) ⟨1950120, by rfl⟩ : syracuseStep 20801285 = 3900241) B3900241
theorem B1140491 : Blo 1136633 1140491 := bstep (se 1 (by rfl) ⟨855368, by rfl⟩ : syracuseStep 1140491 = 1710737) B1710737
theorem B1140503 : Blo 1136633 1140503 := bstep (se 1 (by rfl) ⟨855377, by rfl⟩ : syracuseStep 1140503 = 1710755) B1710755
theorem B1140523 : Blo 1136633 1140523 := bstep (se 1 (by rfl) ⟨855392, by rfl⟩ : syracuseStep 1140523 = 1710785) B1710785
theorem B4319021 : Blo 1136633 4319021 := bstep (se 3 (by rfl) ⟨809816, by rfl⟩ : syracuseStep 4319021 = 1619633) B1619633
theorem B1140535 : Blo 1136633 1140535 := bstep (se 1 (by rfl) ⟨855401, by rfl⟩ : syracuseStep 1140535 = 1710803) B1710803
theorem B1140555 : Blo 1136633 1140555 := bstep (se 1 (by rfl) ⟨855416, by rfl⟩ : syracuseStep 1140555 = 1710833) B1710833
theorem B1140567 : Blo 1136633 1140567 := bstep (se 1 (by rfl) ⟨855425, by rfl⟩ : syracuseStep 1140567 = 1710851) B1710851
theorem B4384601 : Blo 1136633 4384601 := bstep (se 2 (by rfl) ⟨1644225, by rfl⟩ : syracuseStep 4384601 = 3288451) B3288451
theorem B1140587 : Blo 1136633 1140587 := bstep (se 1 (by rfl) ⟨855440, by rfl⟩ : syracuseStep 1140587 = 1710881) B1710881
theorem B1140599 : Blo 1136633 1140599 := bstep (se 1 (by rfl) ⟨855449, by rfl⟩ : syracuseStep 1140599 = 1710899) B1710899
theorem B1140619 : Blo 1136633 1140619 := bstep (se 1 (by rfl) ⟨855464, by rfl⟩ : syracuseStep 1140619 = 1710929) B1710929
theorem B1140631 : Blo 1136633 1140631 := bstep (se 1 (by rfl) ⟨855473, by rfl⟩ : syracuseStep 1140631 = 1710947) B1710947
theorem B2877515 : Blo 1136633 2877515 := bstep (se 1 (by rfl) ⟨2158136, by rfl⟩ : syracuseStep 2877515 = 4316273) B4316273
theorem B2877889 : Blo 1136633 2877889 := bstep (se 2 (by rfl) ⟨1079208, by rfl⟩ : syracuseStep 2877889 = 2158417) B2158417
theorem B44362253 : Blo 1136633 44362253 := bstep (se 3 (by rfl) ⟨8317922, by rfl⟩ : syracuseStep 44362253 = 16635845) B16635845
theorem B2878487 : Blo 1136633 2878487 := bstep (se 1 (by rfl) ⟨2158865, by rfl⟩ : syracuseStep 2878487 = 4317731) B4317731
theorem B4320449 : Blo 1136633 4320449 := bstep (se 2 (by rfl) ⟨1620168, by rfl⟩ : syracuseStep 4320449 = 3240337) B3240337
theorem B2190539 : Blo 1136633 2190539 := bstep (se 1 (by rfl) ⟨1642904, by rfl⟩ : syracuseStep 2190539 = 3285809) B3285809
theorem B3239129 : Blo 1136633 3239129 := bstep (se 2 (by rfl) ⟨1214673, by rfl⟩ : syracuseStep 3239129 = 2429347) B2429347
theorem B20802881 : Blo 1136633 20802881 := bstep (se 2 (by rfl) ⟨7801080, by rfl⟩ : syracuseStep 20802881 = 15602161) B15602161
theorem B2157977 : Blo 1136633 2157977 := bstep (se 2 (by rfl) ⟨809241, by rfl⟩ : syracuseStep 2157977 = 1618483) B1618483
theorem B17558963 : Blo 1136633 17558963 := bstep (se 1 (by rfl) ⟨13169222, by rfl⟩ : syracuseStep 17558963 = 26338445) B26338445
theorem B6483635 : Blo 1136633 6483635 := bstep (se 1 (by rfl) ⟨4862726, by rfl⟩ : syracuseStep 6483635 = 9725453) B9725453
theorem B16412341 : Blo 1136633 16412341 := bstep (se 5 (by rfl) ⟨769328, by rfl⟩ : syracuseStep 16412341 = 1538657) B1538657
theorem B2879297 : Blo 1136633 2879297 := bstep (se 2 (by rfl) ⟨1079736, by rfl⟩ : syracuseStep 2879297 = 2159473) B2159473
theorem B7303213 : Blo 1136633 7303213 := bstep (se 3 (by rfl) ⟨1369352, by rfl⟩ : syracuseStep 7303213 = 2738705) B2738705
theorem B2158721 : Blo 1136633 2158721 := bstep (se 2 (by rfl) ⟨809520, by rfl⟩ : syracuseStep 2158721 = 1619041) B1619041
theorem B2879833 : Blo 1136633 2879833 := bstep (se 2 (by rfl) ⟨1079937, by rfl⟩ : syracuseStep 2879833 = 2159875) B2159875
theorem B2158987 : Blo 1136633 2158987 := bstep (se 1 (by rfl) ⟨1619240, by rfl⟩ : syracuseStep 2158987 = 3238481) B3238481
theorem B3240395 : Blo 1136633 3240395 := bstep (se 1 (by rfl) ⟨2430296, by rfl⟩ : syracuseStep 3240395 = 4860593) B4860593
theorem B4321937 : Blo 1136633 4321937 := bstep (se 2 (by rfl) ⟨1620726, by rfl⟩ : syracuseStep 4321937 = 3241453) B3241453
theorem B3076829 : Blo 1136633 3076829 := bstep (se 3 (by rfl) ⟨576905, by rfl⟩ : syracuseStep 3076829 = 1153811) B1153811
theorem B6157073 : Blo 1136633 6157073 := bstep (se 2 (by rfl) ⟨2308902, by rfl⟩ : syracuseStep 6157073 = 4617805) B4617805
theorem B4682519 : Blo 1136633 4682519 := bstep (se 1 (by rfl) ⟨3511889, by rfl⟩ : syracuseStep 4682519 = 7023779) B7023779
theorem B2159435 : Blo 1136633 2159435 := bstep (se 1 (by rfl) ⟨1619576, by rfl⟩ : syracuseStep 2159435 = 3239153) B3239153
theorem B9728869 : Blo 1136633 9728869 := bstep (se 4 (by rfl) ⟨912081, by rfl⟩ : syracuseStep 9728869 = 1824163) B1824163
theorem B4617091 : Blo 1136633 4617091 := bstep (se 1 (by rfl) ⟨3462818, by rfl⟩ : syracuseStep 4617091 = 6925637) B6925637
theorem B2159617 : Blo 1136633 2159617 := bstep (se 2 (by rfl) ⟨809856, by rfl⟩ : syracuseStep 2159617 = 1619713) B1619713
theorem B4322393 : Blo 1136633 4322393 := bstep (se 2 (by rfl) ⟨1620897, by rfl⟩ : syracuseStep 4322393 = 3241795) B3241795
theorem B6485093 : Blo 1136633 6485093 := bstep (se 4 (by rfl) ⟨607977, by rfl⟩ : syracuseStep 6485093 = 1215955) B1215955
theorem B4322605 : Blo 1136633 4322605 := bstep (se 3 (by rfl) ⟨810488, by rfl⟩ : syracuseStep 4322605 = 1620977) B1620977
theorem B2159959 : Blo 1136633 2159959 := bstep (se 1 (by rfl) ⟨1619969, by rfl⟩ : syracuseStep 2159959 = 3239939) B3239939
theorem B5764445 : Blo 1136633 5764445 := bstep (se 3 (by rfl) ⟨1080833, by rfl⟩ : syracuseStep 5764445 = 2161667) B2161667
theorem B2880947 : Blo 1136633 2880947 := bstep (se 1 (by rfl) ⟨2160710, by rfl⟩ : syracuseStep 2880947 = 4321421) B4321421
theorem B2160179 : Blo 1136633 2160179 := bstep (se 1 (by rfl) ⟨1620134, by rfl⟩ : syracuseStep 2160179 = 3240269) B3240269
theorem B4322909 : Blo 1136633 4322909 := bstep (se 3 (by rfl) ⟨810545, by rfl⟩ : syracuseStep 4322909 = 1621091) B1621091
theorem B8648369 : Blo 1136633 8648369 := bstep (se 2 (by rfl) ⟨3243138, by rfl⟩ : syracuseStep 8648369 = 6486277) B6486277
theorem B2881241 : Blo 1136633 2881241 := bstep (se 2 (by rfl) ⟨1080465, by rfl⟩ : syracuseStep 2881241 = 2160931) B2160931
theorem B6485777 : Blo 1136633 6485777 := bstep (se 2 (by rfl) ⟨2432166, by rfl⟩ : syracuseStep 6485777 = 4864333) B4864333
theorem B2160407 : Blo 1136633 2160407 := bstep (se 1 (by rfl) ⟨1620305, by rfl⟩ : syracuseStep 2160407 = 3240611) B3240611
theorem B9729827 : Blo 1136633 9729827 := bstep (se 1 (by rfl) ⟨7297370, by rfl⟩ : syracuseStep 9729827 = 14594741) B14594741
theorem B2160665 : Blo 1136633 2160665 := bstep (se 2 (by rfl) ⟨810249, by rfl⟩ : syracuseStep 2160665 = 1620499) B1620499
theorem B8648855 : Blo 1136633 8648855 := bstep (se 1 (by rfl) ⟨6486641, by rfl⟩ : syracuseStep 8648855 = 12973283) B12973283
theorem B4159667 : Blo 1136633 4159667 := bstep (se 1 (by rfl) ⟨3119750, by rfl⟩ : syracuseStep 4159667 = 6239501) B6239501
theorem B1439947 : Blo 1136633 1439947 := bstep (se 1 (by rfl) ⟨1079960, by rfl⟩ : syracuseStep 1439947 = 2159921) B2159921
theorem B2161075 : Blo 1136633 2161075 := bstep (se 1 (by rfl) ⟨1620806, by rfl⟩ : syracuseStep 2161075 = 3241613) B3241613
theorem B2161561 : Blo 1136633 2161561 := bstep (se 2 (by rfl) ⟨810585, by rfl⟩ : syracuseStep 2161561 = 1621171) B1621171
theorem B1440919 : Blo 1136633 1440919 := bstep (se 1 (by rfl) ⟨1080689, by rfl⟩ : syracuseStep 1440919 = 2161379) B2161379
theorem B9239825 : Blo 1136633 9239825 := bstep (se 2 (by rfl) ⟨3464934, by rfl⟩ : syracuseStep 9239825 = 6929869) B6929869
theorem B2882891 : Blo 1136633 2882891 := bstep (se 1 (by rfl) ⟨2162168, by rfl⟩ : syracuseStep 2882891 = 4324337) B4324337
theorem B5766551 : Blo 1136633 5766551 := bstep (se 1 (by rfl) ⟨4324913, by rfl⟩ : syracuseStep 5766551 = 8649827) B8649827
theorem B2162123 : Blo 1136633 2162123 := bstep (se 1 (by rfl) ⟨1621592, by rfl⟩ : syracuseStep 2162123 = 3243185) B3243185
theorem B2162305 : Blo 1136633 2162305 := bstep (se 2 (by rfl) ⟨810864, by rfl⟩ : syracuseStep 2162305 = 1621729) B1621729
theorem B1441739 : Blo 1136633 1441739 := bstep (se 1 (by rfl) ⟨1081304, by rfl⟩ : syracuseStep 1441739 = 2162609) B2162609
theorem B5537803 : Blo 1136633 5537803 := bstep (se 1 (by rfl) ⟨4153352, by rfl⟩ : syracuseStep 5537803 = 8306705) B8306705
theorem B2883671 : Blo 1136633 2883671 := bstep (se 1 (by rfl) ⟨2162753, by rfl⟩ : syracuseStep 2883671 = 4325507) B4325507
theorem B5767361 : Blo 1136633 5767361 := bstep (se 2 (by rfl) ⟨2162760, by rfl⟩ : syracuseStep 5767361 = 4325521) B4325521
theorem B1442063 : Blo 1136633 1442063 := bstep (se 1 (by rfl) ⟨1081547, by rfl⟩ : syracuseStep 1442063 = 2163095) B2163095
theorem B2883883 : Blo 1136633 2883883 := bstep (se 1 (by rfl) ⟨2162912, by rfl⟩ : syracuseStep 2883883 = 4325825) B4325825
theorem B10944827 : Blo 1136633 10944827 := bstep (se 1 (by rfl) ⟨8208620, by rfl⟩ : syracuseStep 10944827 = 16417241) B16417241
theorem B2884025 : Blo 1136633 2884025 := bstep (se 2 (by rfl) ⟨1081509, by rfl⟩ : syracuseStep 2884025 = 2163019) B2163019
theorem B39387683 : Blo 1136633 39387683 := bstep (se 1 (by rfl) ⟨29540762, by rfl⟩ : syracuseStep 39387683 = 59081525) B59081525
theorem B10388011 : Blo 1136633 10388011 := bstep (se 1 (by rfl) ⟨7791008, by rfl⟩ : syracuseStep 10388011 = 15582017) B15582017
theorem B4326007 : Blo 1136633 4326007 := bstep (se 1 (by rfl) ⟨3244505, by rfl⟩ : syracuseStep 4326007 = 6489011) B6489011
theorem B1540793 : Blo 1136633 1540793 := bstep (se 2 (by rfl) ⟨577797, by rfl⟩ : syracuseStep 1540793 = 1155595) B1155595
theorem B5931809 : Blo 1136633 5931809 := bstep (se 2 (by rfl) ⟨2224428, by rfl⟩ : syracuseStep 5931809 = 4448857) B4448857
theorem B3244985 : Blo 1136633 3244985 := bstep (se 2 (by rfl) ⟨1216869, by rfl⟩ : syracuseStep 3244985 = 2433739) B2433739
theorem B1705019 : Blo 1136633 1705019 := bstep (se 1 (by rfl) ⟨1278764, by rfl⟩ : syracuseStep 1705019 = 2557529) B2557529
theorem B1705079 : Blo 1136633 1705079 := bstep (se 1 (by rfl) ⟨1278809, by rfl⟩ : syracuseStep 1705079 = 2557619) B2557619
theorem B1279111 : Blo 1136633 1279111 := bstep (se 1 (by rfl) ⟨959333, by rfl⟩ : syracuseStep 1279111 = 1918667) B1918667
theorem B2163847 : Blo 1136633 2163847 := bstep (se 1 (by rfl) ⟨1622885, by rfl⟩ : syracuseStep 2163847 = 3245771) B3245771
theorem B1705103 : Blo 1136633 1705103 := bstep (se 1 (by rfl) ⟨1278827, by rfl⟩ : syracuseStep 1705103 = 2557655) B2557655
theorem B5473453 : Blo 1136633 5473453 := bstep (se 3 (by rfl) ⟨1026272, by rfl⟩ : syracuseStep 5473453 = 2052545) B2052545
theorem B1705145 : Blo 1136633 1705145 := bstep (se 2 (by rfl) ⟨639429, by rfl⟩ : syracuseStep 1705145 = 1278859) B1278859
theorem B1705223 : Blo 1136633 1705223 := bstep (se 1 (by rfl) ⟨1278917, by rfl⟩ : syracuseStep 1705223 = 2557835) B2557835
theorem B1705259 : Blo 1136633 1705259 := bstep (se 1 (by rfl) ⟨1278944, by rfl⟩ : syracuseStep 1705259 = 2557889) B2557889
theorem B1279291 : Blo 1136633 1279291 := bstep (se 1 (by rfl) ⟨959468, by rfl⟩ : syracuseStep 1279291 = 1918937) B1918937
theorem B1705289 : Blo 1136633 1705289 := bstep (se 2 (by rfl) ⟨639483, by rfl⟩ : syracuseStep 1705289 = 1278967) B1278967
theorem B13305181 : Blo 1136633 13305181 := bstep (se 3 (by rfl) ⟨2494721, by rfl⟩ : syracuseStep 13305181 = 4989443) B4989443
theorem B7800209 : Blo 1136633 7800209 := bstep (se 2 (by rfl) ⟨2925078, by rfl⟩ : syracuseStep 7800209 = 5850157) B5850157
theorem B2885017 : Blo 1136633 2885017 := bstep (se 2 (by rfl) ⟨1081881, by rfl⟩ : syracuseStep 2885017 = 2163763) B2163763
theorem B1705403 : Blo 1136633 1705403 := bstep (se 1 (by rfl) ⟨1279052, by rfl⟩ : syracuseStep 1705403 = 2558105) B2558105
theorem B5768657 : Blo 1136633 5768657 := bstep (se 2 (by rfl) ⟨2163246, by rfl⟩ : syracuseStep 5768657 = 4326493) B4326493
theorem B1705463 : Blo 1136633 1705463 := bstep (se 1 (by rfl) ⟨1279097, by rfl⟩ : syracuseStep 1705463 = 2558195) B2558195
theorem B1705487 : Blo 1136633 1705487 := bstep (se 1 (by rfl) ⟨1279115, by rfl⟩ : syracuseStep 1705487 = 2558231) B2558231
theorem B1705529 : Blo 1136633 1705529 := bstep (se 2 (by rfl) ⟨639573, by rfl⟩ : syracuseStep 1705529 = 1279147) B1279147
theorem B2885179 : Blo 1136633 2885179 := bstep (se 1 (by rfl) ⟨2163884, by rfl⟩ : syracuseStep 2885179 = 4327769) B4327769
theorem B4326979 : Blo 1136633 4326979 := bstep (se 1 (by rfl) ⟨3245234, by rfl⟩ : syracuseStep 4326979 = 6490469) B6490469
theorem B6489719 : Blo 1136633 6489719 := bstep (se 1 (by rfl) ⟨4867289, by rfl⟩ : syracuseStep 6489719 = 9734579) B9734579
theorem B1705607 : Blo 1136633 1705607 := bstep (se 1 (by rfl) ⟨1279205, by rfl⟩ : syracuseStep 1705607 = 2558411) B2558411
theorem B1705643 : Blo 1136633 1705643 := bstep (se 1 (by rfl) ⟨1279232, by rfl⟩ : syracuseStep 1705643 = 2558465) B2558465
theorem B21857971 : Blo 1136633 21857971 := bstep (se 1 (by rfl) ⟨16393478, by rfl⟩ : syracuseStep 21857971 = 32786957) B32786957
theorem B14059187 : Blo 1136633 14059187 := bstep (se 1 (by rfl) ⟨10544390, by rfl⟩ : syracuseStep 14059187 = 21088781) B21088781
theorem B11667137 : Blo 1136633 11667137 := bstep (se 2 (by rfl) ⟨4375176, by rfl⟩ : syracuseStep 11667137 = 8750353) B8750353
theorem B1705673 : Blo 1136633 1705673 := bstep (se 2 (by rfl) ⟨639627, by rfl⟩ : syracuseStep 1705673 = 1279255) B1279255
theorem B2885321 : Blo 1136633 2885321 := bstep (se 2 (by rfl) ⟨1081995, by rfl⟩ : syracuseStep 2885321 = 2163991) B2163991
theorem B1279759 : Blo 1136633 1279759 := bstep (se 1 (by rfl) ⟨959819, by rfl⟩ : syracuseStep 1279759 = 1919639) B1919639
theorem B1705787 : Blo 1136633 1705787 := bstep (se 1 (by rfl) ⟨1279340, by rfl⟩ : syracuseStep 1705787 = 2558681) B2558681
theorem B4327283 : Blo 1136633 4327283 := bstep (se 1 (by rfl) ⟨3245462, by rfl⟩ : syracuseStep 4327283 = 6490925) B6490925
theorem B1705847 : Blo 1136633 1705847 := bstep (se 1 (by rfl) ⟨1279385, by rfl⟩ : syracuseStep 1705847 = 2558771) B2558771
theorem B1705871 : Blo 1136633 1705871 := bstep (se 1 (by rfl) ⟨1279403, by rfl⟩ : syracuseStep 1705871 = 2558807) B2558807
theorem B1705913 : Blo 1136633 1705913 := bstep (se 2 (by rfl) ⟨639717, by rfl⟩ : syracuseStep 1705913 = 1279435) B1279435
theorem B1705991 : Blo 1136633 1705991 := bstep (se 1 (by rfl) ⟨1279493, by rfl⟩ : syracuseStep 1705991 = 2558987) B2558987
theorem B2885665 : Blo 1136633 2885665 := bstep (se 2 (by rfl) ⟨1082124, by rfl⟩ : syracuseStep 2885665 = 2164249) B2164249
theorem B1706027 : Blo 1136633 1706027 := bstep (se 1 (by rfl) ⟨1279520, by rfl⟩ : syracuseStep 1706027 = 2559041) B2559041
theorem B1706057 : Blo 1136633 1706057 := bstep (se 2 (by rfl) ⟨639771, by rfl⟩ : syracuseStep 1706057 = 1279543) B1279543
theorem B2558087 : Blo 1136633 2558087 := bstep (se 1 (by rfl) ⟨1918565, by rfl⟩ : syracuseStep 2558087 = 3837131) B3837131
theorem B3246227 : Blo 1136633 3246227 := bstep (se 1 (by rfl) ⟨2434670, by rfl⟩ : syracuseStep 3246227 = 4869341) B4869341
theorem B1706171 : Blo 1136633 1706171 := bstep (se 1 (by rfl) ⟨1279628, by rfl⟩ : syracuseStep 1706171 = 2559257) B2559257
theorem B1706231 : Blo 1136633 1706231 := bstep (se 1 (by rfl) ⟨1279673, by rfl⟩ : syracuseStep 1706231 = 2559347) B2559347
theorem B1280263 : Blo 1136633 1280263 := bstep (se 1 (by rfl) ⟨960197, by rfl⟩ : syracuseStep 1280263 = 1920395) B1920395
theorem B1706255 : Blo 1136633 1706255 := bstep (se 1 (by rfl) ⟨1279691, by rfl⟩ : syracuseStep 1706255 = 2559383) B2559383
theorem B1706297 : Blo 1136633 1706297 := bstep (se 2 (by rfl) ⟨639861, by rfl⟩ : syracuseStep 1706297 = 1279723) B1279723
theorem B2558267 : Blo 1136633 2558267 := bstep (se 1 (by rfl) ⟨1918700, by rfl⟩ : syracuseStep 2558267 = 3837401) B3837401
theorem B4327739 : Blo 1136633 4327739 := bstep (se 1 (by rfl) ⟨3245804, by rfl⟩ : syracuseStep 4327739 = 6491609) B6491609
theorem B1706375 : Blo 1136633 1706375 := bstep (se 1 (by rfl) ⟨1279781, by rfl⟩ : syracuseStep 1706375 = 2559563) B2559563
theorem B1706411 : Blo 1136633 1706411 := bstep (se 1 (by rfl) ⟨1279808, by rfl⟩ : syracuseStep 1706411 = 2559617) B2559617
theorem B2558393 : Blo 1136633 2558393 := bstep (se 2 (by rfl) ⟨959397, by rfl⟩ : syracuseStep 2558393 = 1918795) B1918795
theorem B1280443 : Blo 1136633 1280443 := bstep (se 1 (by rfl) ⟨960332, by rfl⟩ : syracuseStep 1280443 = 1920665) B1920665
theorem B1706441 : Blo 1136633 1706441 := bstep (se 2 (by rfl) ⟨639915, by rfl⟩ : syracuseStep 1706441 = 1279831) B1279831
theorem B1706555 : Blo 1136633 1706555 := bstep (se 1 (by rfl) ⟨1279916, by rfl⟩ : syracuseStep 1706555 = 2559833) B2559833
theorem B1706615 : Blo 1136633 1706615 := bstep (se 1 (by rfl) ⟨1279961, by rfl⟩ : syracuseStep 1706615 = 2559923) B2559923
theorem B2886263 : Blo 1136633 2886263 := bstep (se 1 (by rfl) ⟨2164697, by rfl⟩ : syracuseStep 2886263 = 4329395) B4329395
theorem B1706639 : Blo 1136633 1706639 := bstep (se 1 (by rfl) ⟨1279979, by rfl⟩ : syracuseStep 1706639 = 2559959) B2559959
theorem B1706681 : Blo 1136633 1706681 := bstep (se 2 (by rfl) ⟨640005, by rfl⟩ : syracuseStep 1706681 = 1280011) B1280011
theorem B1706759 : Blo 1136633 1706759 := bstep (se 1 (by rfl) ⟨1280069, by rfl⟩ : syracuseStep 1706759 = 2560139) B2560139
theorem B2558735 : Blo 1136633 2558735 := bstep (se 1 (by rfl) ⟨1919051, by rfl⟩ : syracuseStep 2558735 = 3838103) B3838103
theorem B2558753 : Blo 1136633 2558753 := bstep (se 2 (by rfl) ⟨959532, by rfl⟩ : syracuseStep 2558753 = 1919065) B1919065
theorem B4328225 : Blo 1136633 4328225 := bstep (se 2 (by rfl) ⟨1623084, by rfl⟩ : syracuseStep 4328225 = 3246169) B3246169
theorem B1706795 : Blo 1136633 1706795 := bstep (se 1 (by rfl) ⟨1280096, by rfl⟩ : syracuseStep 1706795 = 2560193) B2560193
theorem B2427707 : Blo 1136633 2427707 := bstep (se 1 (by rfl) ⟨1820780, by rfl⟩ : syracuseStep 2427707 = 3641561) B3641561
theorem B1706825 : Blo 1136633 1706825 := bstep (se 2 (by rfl) ⟨640059, by rfl⟩ : syracuseStep 1706825 = 1280119) B1280119
theorem B3836807 : Blo 1136633 3836807 := bstep (se 1 (by rfl) ⟨2877605, by rfl⟩ : syracuseStep 3836807 = 5755211) B5755211
theorem B1280911 : Blo 1136633 1280911 := bstep (se 1 (by rfl) ⟨960683, by rfl⟩ : syracuseStep 1280911 = 1921367) B1921367
theorem B1706939 : Blo 1136633 1706939 := bstep (se 1 (by rfl) ⟨1280204, by rfl⟩ : syracuseStep 1706939 = 2560409) B2560409
theorem B1706999 : Blo 1136633 1706999 := bstep (se 1 (by rfl) ⟨1280249, by rfl⟩ : syracuseStep 1706999 = 2560499) B2560499
theorem B1707023 : Blo 1136633 1707023 := bstep (se 1 (by rfl) ⟨1280267, by rfl⟩ : syracuseStep 1707023 = 2560535) B2560535
theorem B1707065 : Blo 1136633 1707065 := bstep (se 2 (by rfl) ⟨640149, by rfl⟩ : syracuseStep 1707065 = 1280299) B1280299
theorem B2559095 : Blo 1136633 2559095 := bstep (se 1 (by rfl) ⟨1919321, by rfl⟩ : syracuseStep 2559095 = 3838643) B3838643
theorem B1707143 : Blo 1136633 1707143 := bstep (se 1 (by rfl) ⟨1280357, by rfl⟩ : syracuseStep 1707143 = 2560715) B2560715
theorem B1707179 : Blo 1136633 1707179 := bstep (se 1 (by rfl) ⟨1280384, by rfl⟩ : syracuseStep 1707179 = 2560769) B2560769
theorem B1707209 : Blo 1136633 1707209 := bstep (se 2 (by rfl) ⟨640203, by rfl⟩ : syracuseStep 1707209 = 1280407) B1280407
theorem B3837185 : Blo 1136633 3837185 := bstep (se 2 (by rfl) ⟨1438944, by rfl⟩ : syracuseStep 3837185 = 2877889) B2877889
theorem B6917413 : Blo 1136633 6917413 := bstep (se 4 (by rfl) ⟨648507, by rfl⟩ : syracuseStep 6917413 = 1297015) B1297015
theorem B2559275 : Blo 1136633 2559275 := bstep (se 1 (by rfl) ⟨1919456, by rfl⟩ : syracuseStep 2559275 = 3838913) B3838913
theorem B1707323 : Blo 1136633 1707323 := bstep (se 1 (by rfl) ⟨1280492, by rfl⟩ : syracuseStep 1707323 = 2560985) B2560985
theorem B1707383 : Blo 1136633 1707383 := bstep (se 1 (by rfl) ⟨1280537, by rfl⟩ : syracuseStep 1707383 = 2561075) B2561075
theorem B1281415 : Blo 1136633 1281415 := bstep (se 1 (by rfl) ⟨961061, by rfl⟩ : syracuseStep 1281415 = 1922123) B1922123
theorem B9244039 : Blo 1136633 9244039 := bstep (se 1 (by rfl) ⟨6933029, by rfl⟩ : syracuseStep 9244039 = 13866059) B13866059
theorem B1707407 : Blo 1136633 1707407 := bstep (se 1 (by rfl) ⟨1280555, by rfl⟩ : syracuseStep 1707407 = 2561111) B2561111
theorem B1707449 : Blo 1136633 1707449 := bstep (se 2 (by rfl) ⟨640293, by rfl⟩ : syracuseStep 1707449 = 1280587) B1280587
theorem B1707527 : Blo 1136633 1707527 := bstep (se 1 (by rfl) ⟨1280645, by rfl⟩ : syracuseStep 1707527 = 2561291) B2561291
theorem B5770763 : Blo 1136633 5770763 := bstep (se 1 (by rfl) ⟨4328072, by rfl⟩ : syracuseStep 5770763 = 8656145) B8656145
theorem B3247627 : Blo 1136633 3247627 := bstep (se 1 (by rfl) ⟨2435720, by rfl⟩ : syracuseStep 3247627 = 4871441) B4871441
theorem B1707563 : Blo 1136633 1707563 := bstep (se 1 (by rfl) ⟨1280672, by rfl⟩ : syracuseStep 1707563 = 2561345) B2561345
theorem B1281595 : Blo 1136633 1281595 := bstep (se 1 (by rfl) ⟨961196, by rfl⟩ : syracuseStep 1281595 = 1922393) B1922393
theorem B1707593 : Blo 1136633 1707593 := bstep (se 2 (by rfl) ⟨640347, by rfl⟩ : syracuseStep 1707593 = 1280695) B1280695
theorem B2559635 : Blo 1136633 2559635 := bstep (se 1 (by rfl) ⟨1919726, by rfl⟩ : syracuseStep 2559635 = 3839453) B3839453
theorem B5770925 : Blo 1136633 5770925 := bstep (se 3 (by rfl) ⟨1082048, by rfl⟩ : syracuseStep 5770925 = 2164097) B2164097
theorem B1707707 : Blo 1136633 1707707 := bstep (se 1 (by rfl) ⟨1280780, by rfl⟩ : syracuseStep 1707707 = 2561561) B2561561
theorem B2461385 : Blo 1136633 2461385 := bstep (se 2 (by rfl) ⟨923019, by rfl⟩ : syracuseStep 2461385 = 1846039) B1846039
theorem B2559689 : Blo 1136633 2559689 := bstep (se 2 (by rfl) ⟨959883, by rfl⟩ : syracuseStep 2559689 = 1919767) B1919767
theorem B4329197 : Blo 1136633 4329197 := bstep (se 3 (by rfl) ⟨811724, by rfl⟩ : syracuseStep 4329197 = 1623449) B1623449
theorem B1707767 : Blo 1136633 1707767 := bstep (se 1 (by rfl) ⟨1280825, by rfl⟩ : syracuseStep 1707767 = 2561651) B2561651
theorem B1707791 : Blo 1136633 1707791 := bstep (se 1 (by rfl) ⟨1280843, by rfl⟩ : syracuseStep 1707791 = 2561687) B2561687
theorem B3247901 : Blo 1136633 3247901 := bstep (se 3 (by rfl) ⟨608981, by rfl⟩ : syracuseStep 3247901 = 1217963) B1217963
theorem B1707833 : Blo 1136633 1707833 := bstep (se 2 (by rfl) ⟨640437, by rfl⟩ : syracuseStep 1707833 = 1280875) B1280875
theorem B1707911 : Blo 1136633 1707911 := bstep (se 1 (by rfl) ⟨1280933, by rfl⟩ : syracuseStep 1707911 = 2561867) B2561867
theorem B1707947 : Blo 1136633 1707947 := bstep (se 1 (by rfl) ⟨1280960, by rfl⟩ : syracuseStep 1707947 = 2561921) B2561921
theorem B1707977 : Blo 1136633 1707977 := bstep (se 2 (by rfl) ⟨640491, by rfl⟩ : syracuseStep 1707977 = 1280983) B1280983
theorem B1282063 : Blo 1136633 1282063 := bstep (se 1 (by rfl) ⟨961547, by rfl⟩ : syracuseStep 1282063 = 1923095) B1923095
theorem B3837995 : Blo 1136633 3837995 := bstep (se 1 (by rfl) ⟨2878496, by rfl⟩ : syracuseStep 3837995 = 5756993) B5756993
theorem B1708091 : Blo 1136633 1708091 := bstep (se 1 (by rfl) ⟨1281068, by rfl⟩ : syracuseStep 1708091 = 2562137) B2562137
theorem B1708151 : Blo 1136633 1708151 := bstep (se 1 (by rfl) ⟨1281113, by rfl⟩ : syracuseStep 1708151 = 2562227) B2562227
theorem B1708175 : Blo 1136633 1708175 := bstep (se 1 (by rfl) ⟨1281131, by rfl⟩ : syracuseStep 1708175 = 2562263) B2562263
theorem B1708217 : Blo 1136633 1708217 := bstep (se 2 (by rfl) ⟨640581, by rfl⟩ : syracuseStep 1708217 = 1281163) B1281163
theorem B1708295 : Blo 1136633 1708295 := bstep (se 1 (by rfl) ⟨1281221, by rfl⟩ : syracuseStep 1708295 = 2562443) B2562443
theorem B1708331 : Blo 1136633 1708331 := bstep (se 1 (by rfl) ⟨1281248, by rfl⟩ : syracuseStep 1708331 = 2562497) B2562497
theorem B1708361 : Blo 1136633 1708361 := bstep (se 2 (by rfl) ⟨640635, by rfl⟩ : syracuseStep 1708361 = 1281271) B1281271
theorem B12980573 : Blo 1136633 12980573 := bstep (se 3 (by rfl) ⟨2433857, by rfl⟩ : syracuseStep 12980573 = 4867715) B4867715
theorem B2560391 : Blo 1136633 2560391 := bstep (se 1 (by rfl) ⟨1920293, by rfl⟩ : syracuseStep 2560391 = 3840587) B3840587
theorem B4329881 : Blo 1136633 4329881 := bstep (se 2 (by rfl) ⟨1623705, by rfl⟩ : syracuseStep 4329881 = 3247411) B3247411
theorem B1708475 : Blo 1136633 1708475 := bstep (se 1 (by rfl) ⟨1281356, by rfl⟩ : syracuseStep 1708475 = 2562713) B2562713
theorem B1708535 : Blo 1136633 1708535 := bstep (se 1 (by rfl) ⟨1281401, by rfl⟩ : syracuseStep 1708535 = 2562803) B2562803
theorem B1282567 : Blo 1136633 1282567 := bstep (se 1 (by rfl) ⟨961925, by rfl⟩ : syracuseStep 1282567 = 1923851) B1923851
theorem B7016971 : Blo 1136633 7016971 := bstep (se 1 (by rfl) ⟨5262728, by rfl⟩ : syracuseStep 7016971 = 10525457) B10525457
theorem B1708559 : Blo 1136633 1708559 := bstep (se 1 (by rfl) ⟨1281419, by rfl⟩ : syracuseStep 1708559 = 2562839) B2562839
theorem B1708601 : Blo 1136633 1708601 := bstep (se 2 (by rfl) ⟨640725, by rfl⟩ : syracuseStep 1708601 = 1281451) B1281451
theorem B2560571 : Blo 1136633 2560571 := bstep (se 1 (by rfl) ⟨1920428, by rfl⟩ : syracuseStep 2560571 = 3840857) B3840857
theorem B1708679 : Blo 1136633 1708679 := bstep (se 1 (by rfl) ⟨1281509, by rfl⟩ : syracuseStep 1708679 = 2563019) B2563019
theorem B1708715 : Blo 1136633 1708715 := bstep (se 1 (by rfl) ⟨1281536, by rfl⟩ : syracuseStep 1708715 = 2563073) B2563073
theorem B2560697 : Blo 1136633 2560697 := bstep (se 2 (by rfl) ⟨960261, by rfl⟩ : syracuseStep 2560697 = 1920523) B1920523
theorem B1282747 : Blo 1136633 1282747 := bstep (se 1 (by rfl) ⟨962060, by rfl⟩ : syracuseStep 1282747 = 1924121) B1924121
theorem B29561537 : Blo 1136633 29561537 := bstep (se 2 (by rfl) ⟨11085576, by rfl⟩ : syracuseStep 29561537 = 22171153) B22171153
theorem B1708745 : Blo 1136633 1708745 := bstep (se 2 (by rfl) ⟨640779, by rfl⟩ : syracuseStep 1708745 = 1281559) B1281559
theorem B1708859 : Blo 1136633 1708859 := bstep (se 1 (by rfl) ⟨1281644, by rfl⟩ : syracuseStep 1708859 = 2563289) B2563289
theorem B1708919 : Blo 1136633 1708919 := bstep (se 1 (by rfl) ⟨1281689, by rfl⟩ : syracuseStep 1708919 = 2563379) B2563379
theorem B1708943 : Blo 1136633 1708943 := bstep (se 1 (by rfl) ⟨1281707, by rfl⟩ : syracuseStep 1708943 = 2563415) B2563415
theorem B1708985 : Blo 1136633 1708985 := bstep (se 2 (by rfl) ⟨640869, by rfl⟩ : syracuseStep 1708985 = 1281739) B1281739
theorem B3511297 : Blo 1136633 3511297 := bstep (se 2 (by rfl) ⟨1316736, by rfl⟩ : syracuseStep 3511297 = 2633473) B2633473
theorem B1709063 : Blo 1136633 1709063 := bstep (se 1 (by rfl) ⟨1281797, by rfl⟩ : syracuseStep 1709063 = 2563595) B2563595
theorem B2561039 : Blo 1136633 2561039 := bstep (se 1 (by rfl) ⟨1920779, by rfl⟩ : syracuseStep 2561039 = 3841559) B3841559
theorem B2561057 : Blo 1136633 2561057 := bstep (se 2 (by rfl) ⟨960396, by rfl⟩ : syracuseStep 2561057 = 1920793) B1920793
theorem B1709099 : Blo 1136633 1709099 := bstep (se 1 (by rfl) ⟨1281824, by rfl⟩ : syracuseStep 1709099 = 2563649) B2563649
theorem B1709129 : Blo 1136633 1709129 := bstep (se 2 (by rfl) ⟨640923, by rfl⟩ : syracuseStep 1709129 = 1281847) B1281847
theorem B1709243 : Blo 1136633 1709243 := bstep (se 1 (by rfl) ⟨1281932, by rfl⟩ : syracuseStep 1709243 = 2563865) B2563865
theorem B6493385 : Blo 1136633 6493385 := bstep (se 2 (by rfl) ⟨2435019, by rfl⟩ : syracuseStep 6493385 = 4870039) B4870039
theorem B1709303 : Blo 1136633 1709303 := bstep (se 1 (by rfl) ⟨1281977, by rfl⟩ : syracuseStep 1709303 = 2563955) B2563955
theorem B5772545 : Blo 1136633 5772545 := bstep (se 2 (by rfl) ⟨2164704, by rfl⟩ : syracuseStep 5772545 = 4329409) B4329409
theorem B1709327 : Blo 1136633 1709327 := bstep (se 1 (by rfl) ⟨1281995, by rfl⟩ : syracuseStep 1709327 = 2563991) B2563991
theorem B1709369 : Blo 1136633 1709369 := bstep (se 2 (by rfl) ⟨641013, by rfl⟩ : syracuseStep 1709369 = 1282027) B1282027
theorem B3839291 : Blo 1136633 3839291 := bstep (se 1 (by rfl) ⟨2879468, by rfl⟩ : syracuseStep 3839291 = 5758937) B5758937
theorem B2561399 : Blo 1136633 2561399 := bstep (se 1 (by rfl) ⟨1921049, by rfl⟩ : syracuseStep 2561399 = 3842099) B3842099
theorem B1709447 : Blo 1136633 1709447 := bstep (se 1 (by rfl) ⟨1282085, by rfl⟩ : syracuseStep 1709447 = 2564171) B2564171
theorem B9737617 : Blo 1136633 9737617 := bstep (se 2 (by rfl) ⟨3651606, by rfl⟩ : syracuseStep 9737617 = 7303213) B7303213
theorem B1709483 : Blo 1136633 1709483 := bstep (se 1 (by rfl) ⟨1282112, by rfl⟩ : syracuseStep 1709483 = 2564225) B2564225
theorem B1709513 : Blo 1136633 1709513 := bstep (se 2 (by rfl) ⟨641067, by rfl⟩ : syracuseStep 1709513 = 1282135) B1282135
theorem B10950173 : Blo 1136633 10950173 := bstep (se 3 (by rfl) ⟨2053157, by rfl⟩ : syracuseStep 10950173 = 4106315) B4106315
theorem B2561579 : Blo 1136633 2561579 := bstep (se 1 (by rfl) ⟨1921184, by rfl⟩ : syracuseStep 2561579 = 3842369) B3842369
theorem B1709627 : Blo 1136633 1709627 := bstep (se 1 (by rfl) ⟨1282220, by rfl⟩ : syracuseStep 1709627 = 2564441) B2564441
theorem B1709687 : Blo 1136633 1709687 := bstep (se 1 (by rfl) ⟨1282265, by rfl⟩ : syracuseStep 1709687 = 2564531) B2564531
theorem B1709711 : Blo 1136633 1709711 := bstep (se 1 (by rfl) ⟨1282283, by rfl⟩ : syracuseStep 1709711 = 2564567) B2564567
theorem B1709753 : Blo 1136633 1709753 := bstep (se 2 (by rfl) ⟨641157, by rfl⟩ : syracuseStep 1709753 = 1282315) B1282315
theorem B1709831 : Blo 1136633 1709831 := bstep (se 1 (by rfl) ⟨1282373, by rfl⟩ : syracuseStep 1709831 = 2564747) B2564747
theorem B12982031 : Blo 1136633 12982031 := bstep (se 1 (by rfl) ⟨9736523, by rfl⟩ : syracuseStep 12982031 = 19473047) B19473047
theorem B4855585 : Blo 1136633 4855585 := bstep (se 2 (by rfl) ⟨1820844, by rfl⟩ : syracuseStep 4855585 = 3641689) B3641689
theorem B3839777 : Blo 1136633 3839777 := bstep (se 2 (by rfl) ⟨1439916, by rfl⟩ : syracuseStep 3839777 = 2879833) B2879833
theorem B1709867 : Blo 1136633 1709867 := bstep (se 1 (by rfl) ⟨1282400, by rfl⟩ : syracuseStep 1709867 = 2564801) B2564801
theorem B4101947 : Blo 1136633 4101947 := bstep (se 1 (by rfl) ⟨3076460, by rfl⟩ : syracuseStep 4101947 = 6152921) B6152921
theorem B1709897 : Blo 1136633 1709897 := bstep (se 2 (by rfl) ⟨641211, by rfl⟩ : syracuseStep 1709897 = 1282423) B1282423
theorem B10950515 : Blo 1136633 10950515 := bstep (se 1 (by rfl) ⟨8212886, by rfl⟩ : syracuseStep 10950515 = 16425773) B16425773
theorem B2561939 : Blo 1136633 2561939 := bstep (se 1 (by rfl) ⟨1921454, by rfl⟩ : syracuseStep 2561939 = 3842909) B3842909
theorem B1710011 : Blo 1136633 1710011 := bstep (se 1 (by rfl) ⟨1282508, by rfl⟩ : syracuseStep 1710011 = 2565017) B2565017
theorem B2463689 : Blo 1136633 2463689 := bstep (se 2 (by rfl) ⟨923883, by rfl⟩ : syracuseStep 2463689 = 1847767) B1847767
theorem B2561993 : Blo 1136633 2561993 := bstep (se 2 (by rfl) ⟨960747, by rfl⟩ : syracuseStep 2561993 = 1921495) B1921495
theorem B1710071 : Blo 1136633 1710071 := bstep (se 1 (by rfl) ⟨1282553, by rfl⟩ : syracuseStep 1710071 = 2565107) B2565107
theorem B1710095 : Blo 1136633 1710095 := bstep (se 1 (by rfl) ⟨1282571, by rfl⟩ : syracuseStep 1710095 = 2565143) B2565143
theorem B5773355 : Blo 1136633 5773355 := bstep (se 1 (by rfl) ⟨4330016, by rfl⟩ : syracuseStep 5773355 = 8660033) B8660033
theorem B1710137 : Blo 1136633 1710137 := bstep (se 2 (by rfl) ⟨641301, by rfl⟩ : syracuseStep 1710137 = 1282603) B1282603
theorem B3119219 : Blo 1136633 3119219 := bstep (se 1 (by rfl) ⟨2339414, by rfl⟩ : syracuseStep 3119219 = 4678829) B4678829
theorem B1710215 : Blo 1136633 1710215 := bstep (se 1 (by rfl) ⟨1282661, by rfl⟩ : syracuseStep 1710215 = 2565323) B2565323
theorem B1710251 : Blo 1136633 1710251 := bstep (se 1 (by rfl) ⟨1282688, by rfl⟩ : syracuseStep 1710251 = 2565377) B2565377
theorem B1710281 : Blo 1136633 1710281 := bstep (se 2 (by rfl) ⟨641355, by rfl⟩ : syracuseStep 1710281 = 1282711) B1282711
theorem B3643663 : Blo 1136633 3643663 := bstep (se 1 (by rfl) ⟨2732747, by rfl⟩ : syracuseStep 3643663 = 5465495) B5465495
theorem B3512605 : Blo 1136633 3512605 := bstep (se 3 (by rfl) ⟨658613, by rfl⟩ : syracuseStep 3512605 = 1317227) B1317227
theorem B1710395 : Blo 1136633 1710395 := bstep (se 1 (by rfl) ⟨1282796, by rfl⟩ : syracuseStep 1710395 = 2565593) B2565593
theorem B3840371 : Blo 1136633 3840371 := bstep (se 1 (by rfl) ⟨2880278, by rfl⟩ : syracuseStep 3840371 = 5760557) B5760557
theorem B1710455 : Blo 1136633 1710455 := bstep (se 1 (by rfl) ⟨1282841, by rfl⟩ : syracuseStep 1710455 = 2565683) B2565683
theorem B1710479 : Blo 1136633 1710479 := bstep (se 1 (by rfl) ⟨1282859, by rfl⟩ : syracuseStep 1710479 = 2565719) B2565719
theorem B8198585 : Blo 1136633 8198585 := bstep (se 2 (by rfl) ⟨3074469, by rfl⟩ : syracuseStep 8198585 = 6148939) B6148939
theorem B1710521 : Blo 1136633 1710521 := bstep (se 2 (by rfl) ⟨641445, by rfl⟩ : syracuseStep 1710521 = 1282891) B1282891
theorem B13867523 : Blo 1136633 13867523 := bstep (se 1 (by rfl) ⟨10400642, by rfl⟩ : syracuseStep 13867523 = 20801285) B20801285
theorem B1710599 : Blo 1136633 1710599 := bstep (se 1 (by rfl) ⟨1282949, by rfl⟩ : syracuseStep 1710599 = 2565899) B2565899
theorem B1710635 : Blo 1136633 1710635 := bstep (se 1 (by rfl) ⟨1282976, by rfl⟩ : syracuseStep 1710635 = 2565953) B2565953
theorem B2923067 : Blo 1136633 2923067 := bstep (se 1 (by rfl) ⟨2192300, by rfl⟩ : syracuseStep 2923067 = 4384601) B4384601
theorem B1710665 : Blo 1136633 1710665 := bstep (se 2 (by rfl) ⟨641499, by rfl⟩ : syracuseStep 1710665 = 1282999) B1282999
theorem B2562695 : Blo 1136633 2562695 := bstep (se 1 (by rfl) ⟨1922021, by rfl⟩ : syracuseStep 2562695 = 3844043) B3844043
theorem B1710779 : Blo 1136633 1710779 := bstep (se 1 (by rfl) ⟨1283084, by rfl⟩ : syracuseStep 1710779 = 2566169) B2566169
theorem B118299341 : Blo 1136633 118299341 := bstep (se 3 (by rfl) ⟨22181126, by rfl⟩ : syracuseStep 118299341 = 44362253) B44362253
theorem B1710839 : Blo 1136633 1710839 := bstep (se 1 (by rfl) ⟨1283129, by rfl⟩ : syracuseStep 1710839 = 2566259) B2566259
theorem B1710863 : Blo 1136633 1710863 := bstep (se 1 (by rfl) ⟨1283147, by rfl⟩ : syracuseStep 1710863 = 2566295) B2566295
theorem B1710905 : Blo 1136633 1710905 := bstep (se 2 (by rfl) ⟨641589, by rfl⟩ : syracuseStep 1710905 = 1283179) B1283179
theorem B2562875 : Blo 1136633 2562875 := bstep (se 1 (by rfl) ⟨1922156, by rfl⟩ : syracuseStep 2562875 = 3844313) B3844313
theorem B2563001 : Blo 1136633 2563001 := bstep (se 2 (by rfl) ⟨961125, by rfl⟩ : syracuseStep 2563001 = 1922251) B1922251
theorem B6495299 : Blo 1136633 6495299 := bstep (se 1 (by rfl) ⟨4871474, by rfl⟩ : syracuseStep 6495299 = 9742949) B9742949
theorem B2563343 : Blo 1136633 2563343 := bstep (se 1 (by rfl) ⟨1922507, by rfl⟩ : syracuseStep 2563343 = 3845015) B3845015
theorem B2563361 : Blo 1136633 2563361 := bstep (se 2 (by rfl) ⟨961260, by rfl⟩ : syracuseStep 2563361 = 1922521) B1922521
theorem B23403907 : Blo 1136633 23403907 := bstep (se 1 (by rfl) ⟨17552930, by rfl⟩ : syracuseStep 23403907 = 35105861) B35105861
theorem B13868587 : Blo 1136633 13868587 := bstep (se 1 (by rfl) ⟨10401440, by rfl⟩ : syracuseStep 13868587 = 20802881) B20802881
theorem B2563703 : Blo 1136633 2563703 := bstep (se 1 (by rfl) ⟨1922777, by rfl⟩ : syracuseStep 2563703 = 3845555) B3845555
theorem B11705975 : Blo 1136633 11705975 := bstep (se 1 (by rfl) ⟨8779481, by rfl⟩ : syracuseStep 11705975 = 17558963) B17558963
theorem B2563883 : Blo 1136633 2563883 := bstep (se 1 (by rfl) ⟨1922912, by rfl⟩ : syracuseStep 2563883 = 3845825) B3845825
theorem B2564243 : Blo 1136633 2564243 := bstep (se 1 (by rfl) ⟨1923182, by rfl⟩ : syracuseStep 2564243 = 3846365) B3846365
theorem B2564297 : Blo 1136633 2564297 := bstep (se 2 (by rfl) ⟨961611, by rfl⟩ : syracuseStep 2564297 = 1923223) B1923223
theorem B4104715 : Blo 1136633 4104715 := bstep (se 1 (by rfl) ⟨3078536, by rfl⟩ : syracuseStep 4104715 = 6157073) B6157073
theorem B3121679 : Blo 1136633 3121679 := bstep (se 1 (by rfl) ⟨2341259, by rfl⟩ : syracuseStep 3121679 = 4682519) B4682519
theorem B2433721 : Blo 1136633 2433721 := bstep (se 2 (by rfl) ⟨912645, by rfl⟩ : syracuseStep 2433721 = 1825291) B1825291
theorem B7283429 : Blo 1136633 7283429 := bstep (se 4 (by rfl) ⟨682821, by rfl⟩ : syracuseStep 7283429 = 1365643) B1365643
theorem B12296933 : Blo 1136633 12296933 := bstep (se 4 (by rfl) ⟨1152837, by rfl⟩ : syracuseStep 12296933 = 2305675) B2305675
theorem B14033699 : Blo 1136633 14033699 := bstep (se 1 (by rfl) ⟨10525274, by rfl⟩ : syracuseStep 14033699 = 21050549) B21050549
theorem B2564999 : Blo 1136633 2564999 := bstep (se 1 (by rfl) ⟨1923749, by rfl⟩ : syracuseStep 2564999 = 3847499) B3847499
theorem B3842963 : Blo 1136633 3842963 := bstep (se 1 (by rfl) ⟨2882222, by rfl⟩ : syracuseStep 3842963 = 5764445) B5764445
theorem B2434063 : Blo 1136633 2434063 := bstep (se 1 (by rfl) ⟨1825547, by rfl⟩ : syracuseStep 2434063 = 3651095) B3651095
theorem B2565179 : Blo 1136633 2565179 := bstep (se 1 (by rfl) ⟨1923884, by rfl⟩ : syracuseStep 2565179 = 3847769) B3847769
theorem B4858967 : Blo 1136633 4858967 := bstep (se 1 (by rfl) ⟨3644225, by rfl⟩ : syracuseStep 4858967 = 7288451) B7288451
theorem B2565305 : Blo 1136633 2565305 := bstep (se 2 (by rfl) ⟨961989, by rfl⟩ : syracuseStep 2565305 = 1923979) B1923979
theorem B2565647 : Blo 1136633 2565647 := bstep (se 1 (by rfl) ⟨1924235, by rfl⟩ : syracuseStep 2565647 = 3848471) B3848471
theorem B49325597 : Blo 1136633 49325597 := bstep (se 3 (by rfl) ⟨9248549, by rfl⟩ : syracuseStep 49325597 = 18497099) B18497099
theorem B2565665 : Blo 1136633 2565665 := bstep (se 2 (by rfl) ⟨962124, by rfl⟩ : syracuseStep 2565665 = 1924249) B1924249
theorem B2959163 : Blo 1136633 2959163 := bstep (se 1 (by rfl) ⟨2219372, by rfl⟩ : syracuseStep 2959163 = 4438745) B4438745
theorem B2566007 : Blo 1136633 2566007 := bstep (se 1 (by rfl) ⟨1924505, by rfl⟩ : syracuseStep 2566007 = 3849011) B3849011
theorem B2434951 : Blo 1136633 2434951 := bstep (se 1 (by rfl) ⟨1826213, by rfl⟩ : syracuseStep 2434951 = 3652427) B3652427
theorem B24586253 : Blo 1136633 24586253 := bstep (se 3 (by rfl) ⟨4609922, by rfl⟩ : syracuseStep 24586253 = 9219845) B9219845
theorem B2566187 : Blo 1136633 2566187 := bstep (se 1 (by rfl) ⟨1924640, by rfl⟩ : syracuseStep 2566187 = 3849281) B3849281
theorem B3844367 : Blo 1136633 3844367 := bstep (se 1 (by rfl) ⟨2883275, by rfl⟩ : syracuseStep 3844367 = 5766551) B5766551
theorem B2435447 : Blo 1136633 2435447 := bstep (se 1 (by rfl) ⟨1826585, by rfl⟩ : syracuseStep 2435447 = 3653171) B3653171
theorem B3844637 : Blo 1136633 3844637 := bstep (se 3 (by rfl) ⟨720869, by rfl⟩ : syracuseStep 3844637 = 1441739) B1441739
theorem B5188157 : Blo 1136633 5188157 := bstep (se 3 (by rfl) ⟨972779, by rfl⟩ : syracuseStep 5188157 = 1945559) B1945559
theorem B5188297 : Blo 1136633 5188297 := bstep (se 2 (by rfl) ⟨1945611, by rfl⟩ : syracuseStep 5188297 = 3891223) B3891223
theorem B12954329 : Blo 1136633 12954329 := bstep (se 2 (by rfl) ⟨4857873, by rfl⟩ : syracuseStep 12954329 = 9715747) B9715747
theorem B5548915 : Blo 1136633 5548915 := bstep (se 1 (by rfl) ⟨4161686, by rfl⟩ : syracuseStep 5548915 = 8323373) B8323373
theorem B4860881 : Blo 1136633 4860881 := bstep (se 2 (by rfl) ⟨1822830, by rfl⟩ : syracuseStep 4860881 = 3645661) B3645661
theorem B2731009 : Blo 1136633 2731009 := bstep (se 2 (by rfl) ⟨1024128, by rfl⟩ : syracuseStep 2731009 = 2048257) B2048257
theorem B3648827 : Blo 1136633 3648827 := bstep (se 1 (by rfl) ⟨2736620, by rfl⟩ : syracuseStep 3648827 = 5473241) B5473241
theorem B2600507 : Blo 1136633 2600507 := bstep (se 1 (by rfl) ⟨1950380, by rfl⟩ : syracuseStep 2600507 = 3900761) B3900761
theorem B14593715 : Blo 1136633 14593715 := bstep (se 1 (by rfl) ⟨10945286, by rfl⟩ : syracuseStep 14593715 = 21890573) B21890573
theorem B3846041 : Blo 1136633 3846041 := bstep (se 2 (by rfl) ⟨1442265, by rfl⟩ : syracuseStep 3846041 = 2884531) B2884531
theorem B10399691 : Blo 1136633 10399691 := bstep (se 1 (by rfl) ⟨7799768, by rfl⟩ : syracuseStep 10399691 = 15599537) B15599537
theorem B6566467 : Blo 1136633 6566467 := bstep (se 1 (by rfl) ⟨4924850, by rfl⟩ : syracuseStep 6566467 = 9849701) B9849701
theorem B3846743 : Blo 1136633 3846743 := bstep (se 1 (by rfl) ⟨2885057, by rfl⟩ : syracuseStep 3846743 = 5770115) B5770115
theorem B3289871 : Blo 1136633 3289871 := bstep (se 1 (by rfl) ⟨2467403, by rfl⟩ : syracuseStep 3289871 = 4934807) B4934807
theorem B3847229 : Blo 1136633 3847229 := bstep (se 3 (by rfl) ⟨721355, by rfl⟩ : syracuseStep 3847229 = 1442711) B1442711
theorem B2733323 : Blo 1136633 2733323 := bstep (se 1 (by rfl) ⟨2049992, by rfl⟩ : syracuseStep 2733323 = 4099985) B4099985
theorem B2307475 : Blo 1136633 2307475 := bstep (se 1 (by rfl) ⟨1730606, by rfl⟩ : syracuseStep 2307475 = 3461213) B3461213
theorem B4109777 : Blo 1136633 4109777 := bstep (se 2 (by rfl) ⟨1541166, by rfl⟩ : syracuseStep 4109777 = 3082333) B3082333
theorem B6927875 : Blo 1136633 6927875 := bstep (se 1 (by rfl) ⟨5195906, by rfl⟩ : syracuseStep 6927875 = 10391813) B10391813
theorem B5191235 : Blo 1136633 5191235 := bstep (se 1 (by rfl) ⟨3893426, by rfl⟩ : syracuseStep 5191235 = 7786853) B7786853
theorem B16430849 : Blo 1136633 16430849 := bstep (se 2 (by rfl) ⟨6161568, by rfl⟩ : syracuseStep 16430849 = 12323137) B12323137
theorem B8632331 : Blo 1136633 8632331 := bstep (se 1 (by rfl) ⟨6474248, by rfl⟩ : syracuseStep 8632331 = 12948497) B12948497
theorem B12990779 : Blo 1136633 12990779 := bstep (se 1 (by rfl) ⟨9743084, by rfl⟩ : syracuseStep 12990779 = 19486169) B19486169
theorem B3848633 : Blo 1136633 3848633 := bstep (se 2 (by rfl) ⟨1443237, by rfl⟩ : syracuseStep 3848633 = 2886475) B2886475
theorem B1620425 : Blo 1136633 1620425 := bstep (se 2 (by rfl) ⟨607659, by rfl⟩ : syracuseStep 1620425 = 1215319) B1215319
theorem B20757059 : Blo 1136633 20757059 := bstep (se 1 (by rfl) ⟨15567794, by rfl⟩ : syracuseStep 20757059 = 31135589) B31135589
theorem B22166135 : Blo 1136633 22166135 := bstep (se 1 (by rfl) ⟨16624601, by rfl⟩ : syracuseStep 22166135 = 33249203) B33249203
theorem B3849227 : Blo 1136633 3849227 := bstep (se 1 (by rfl) ⟨2886920, by rfl⟩ : syracuseStep 3849227 = 5773841) B5773841
theorem B52575293 : Blo 1136633 52575293 := bstep (se 3 (by rfl) ⟨9857867, by rfl⟩ : syracuseStep 52575293 = 19715735) B19715735
theorem B3849335 : Blo 1136633 3849335 := bstep (se 1 (by rfl) ⟨2887001, by rfl⟩ : syracuseStep 3849335 = 5774003) B5774003
theorem B4504865 : Blo 1136633 4504865 := bstep (se 2 (by rfl) ⟨1689324, by rfl⟩ : syracuseStep 4504865 = 3378649) B3378649
theorem B1621291 : Blo 1136633 1621291 := bstep (se 1 (by rfl) ⟨1215968, by rfl⟩ : syracuseStep 1621291 = 2431937) B2431937
theorem B3554695 : Blo 1136633 3554695 := bstep (se 1 (by rfl) ⟨2666021, by rfl⟩ : syracuseStep 3554695 = 5332043) B5332043
theorem B2735545 : Blo 1136633 2735545 := bstep (se 2 (by rfl) ⟨1025829, by rfl⟩ : syracuseStep 2735545 = 2051659) B2051659
theorem B2768503 : Blo 1136633 2768503 := bstep (se 1 (by rfl) ⟨2076377, by rfl⟩ : syracuseStep 2768503 = 4152755) B4152755
theorem B21872429 : Blo 1136633 21872429 := bstep (se 3 (by rfl) ⟨4101080, by rfl⟩ : syracuseStep 21872429 = 8202161) B8202161
theorem B4865939 : Blo 1136633 4865939 := bstep (se 1 (by rfl) ⟨3649454, by rfl⟩ : syracuseStep 4865939 = 7298909) B7298909
theorem B8634275 : Blo 1136633 8634275 := bstep (se 1 (by rfl) ⟨6475706, by rfl⟩ : syracuseStep 8634275 = 12951413) B12951413
theorem B11682575 : Blo 1136633 11682575 := bstep (se 1 (by rfl) ⟨8761931, by rfl⟩ : syracuseStep 11682575 = 17523863) B17523863
theorem B2736929 : Blo 1136633 2736929 := bstep (se 2 (by rfl) ⟨1026348, by rfl⟩ : syracuseStep 2736929 = 2052697) B2052697
theorem B1622857 : Blo 1136633 1622857 := bstep (se 2 (by rfl) ⟨608571, by rfl⟩ : syracuseStep 1622857 = 1217143) B1217143
theorem B1950599 : Blo 1136633 1950599 := bstep (se 1 (by rfl) ⟨1462949, by rfl⟩ : syracuseStep 1950599 = 2925899) B2925899
theorem B1623415 : Blo 1136633 1623415 := bstep (se 1 (by rfl) ⟨1217561, by rfl⟩ : syracuseStep 1623415 = 2435123) B2435123
theorem B1918343 : Blo 1136633 1918343 := bstep (se 1 (by rfl) ⟨1438757, by rfl⟩ : syracuseStep 1918343 = 2877515) B2877515
theorem B1623979 : Blo 1136633 1623979 := bstep (se 1 (by rfl) ⟨1217984, by rfl⟩ : syracuseStep 1623979 = 2435969) B2435969
theorem B6473681 : Blo 1136633 6473681 := bstep (se 2 (by rfl) ⟨2427630, by rfl⟩ : syracuseStep 6473681 = 4855261) B4855261
theorem B1918991 : Blo 1136633 1918991 := bstep (se 1 (by rfl) ⟨1439243, by rfl⟩ : syracuseStep 1918991 = 2878487) B2878487
theorem B1460359 : Blo 1136633 1460359 := bstep (se 1 (by rfl) ⟨1095269, by rfl⟩ : syracuseStep 1460359 = 2190539) B2190539
theorem B8636705 : Blo 1136633 8636705 := bstep (se 2 (by rfl) ⟨3238764, by rfl⟩ : syracuseStep 8636705 = 6477529) B6477529
theorem B1919531 : Blo 1136633 1919531 := bstep (se 1 (by rfl) ⟨1439648, by rfl⟩ : syracuseStep 1919531 = 2879297) B2879297
theorem B1821575 : Blo 1136633 1821575 := bstep (se 1 (by rfl) ⟨1366181, by rfl⟩ : syracuseStep 1821575 = 2732363) B2732363
theorem B1919929 : Blo 1136633 1919929 := bstep (se 2 (by rfl) ⟨719973, by rfl⟩ : syracuseStep 1919929 = 1439947) B1439947
theorem B2051219 : Blo 1136633 2051219 := bstep (se 1 (by rfl) ⟨1538414, by rfl⟩ : syracuseStep 2051219 = 3076829) B3076829
theorem B8637677 : Blo 1136633 8637677 := bstep (se 3 (by rfl) ⟨1619564, by rfl⟩ : syracuseStep 8637677 = 3239129) B3239129
theorem B14601505 : Blo 1136633 14601505 := bstep (se 2 (by rfl) ⟨5475564, by rfl⟩ : syracuseStep 14601505 = 10951129) B10951129
theorem B1822267 : Blo 1136633 1822267 := bstep (se 1 (by rfl) ⟨1366700, by rfl⟩ : syracuseStep 1822267 = 2733401) B2733401
theorem B1920631 : Blo 1136633 1920631 := bstep (se 1 (by rfl) ⟨1440473, by rfl⟩ : syracuseStep 1920631 = 2880947) B2880947
theorem B6475571 : Blo 1136633 6475571 := bstep (se 1 (by rfl) ⟨4856678, by rfl⟩ : syracuseStep 6475571 = 9713357) B9713357
theorem B1920827 : Blo 1136633 1920827 := bstep (se 1 (by rfl) ⟨1440620, by rfl⟩ : syracuseStep 1920827 = 2881241) B2881241
theorem B6148163 : Blo 1136633 6148163 := bstep (se 1 (by rfl) ⟨4611122, by rfl⟩ : syracuseStep 6148163 = 9222245) B9222245
theorem B2773111 : Blo 1136633 2773111 := bstep (se 1 (by rfl) ⟨2079833, by rfl⟩ : syracuseStep 2773111 = 4159667) B4159667
theorem B1921225 : Blo 1136633 1921225 := bstep (se 2 (by rfl) ⟨720459, by rfl⟩ : syracuseStep 1921225 = 1440919) B1440919
theorem B4870381 : Blo 1136633 4870381 := bstep (se 3 (by rfl) ⟨913196, by rfl⟩ : syracuseStep 4870381 = 1826393) B1826393
theorem B2740513 : Blo 1136633 2740513 := bstep (se 2 (by rfl) ⟨1027692, by rfl⟩ : syracuseStep 2740513 = 2055385) B2055385
theorem B1921927 : Blo 1136633 1921927 := bstep (se 1 (by rfl) ⟨1441445, by rfl⟩ : syracuseStep 1921927 = 2882891) B2882891
theorem B8639621 : Blo 1136633 8639621 := bstep (se 4 (by rfl) ⟨809964, by rfl⟩ : syracuseStep 8639621 = 1619929) B1619929
theorem B6477029 : Blo 1136633 6477029 := bstep (se 4 (by rfl) ⟨607221, by rfl⟩ : syracuseStep 6477029 = 1214443) B1214443
theorem B3888499 : Blo 1136633 3888499 := bstep (se 1 (by rfl) ⟨2916374, by rfl⟩ : syracuseStep 3888499 = 5832749) B5832749
theorem B5756345 : Blo 1136633 5756345 := bstep (se 2 (by rfl) ⟨2158629, by rfl⟩ : syracuseStep 5756345 = 4317259) B4317259
theorem B1922575 : Blo 1136633 1922575 := bstep (se 1 (by rfl) ⟨1441931, by rfl⟩ : syracuseStep 1922575 = 2883863) B2883863
theorem B4609565 : Blo 1136633 4609565 := bstep (se 3 (by rfl) ⟨864293, by rfl⟩ : syracuseStep 4609565 = 1728587) B1728587
theorem B1365547 : Blo 1136633 1365547 := bstep (se 1 (by rfl) ⟨1024160, by rfl⟩ : syracuseStep 1365547 = 2048321) B2048321
theorem B4380227 : Blo 1136633 4380227 := bstep (se 1 (by rfl) ⟨3285170, by rfl⟩ : syracuseStep 4380227 = 6570341) B6570341
theorem B4872089 : Blo 1136633 4872089 := bstep (se 2 (by rfl) ⟨1827033, by rfl⟩ : syracuseStep 4872089 = 3654067) B3654067
theorem B1136647 : Blo 1136633 1136647 := bstep (se 1 (by rfl) ⟨852485, by rfl⟩ : syracuseStep 1136647 = 1704971) B1704971
theorem B1136655 : Blo 1136633 1136655 := bstep (se 1 (by rfl) ⟨852491, by rfl⟩ : syracuseStep 1136655 = 1704983) B1704983
theorem B3463183 : Blo 1136633 3463183 := bstep (se 1 (by rfl) ⟨2597387, by rfl⟩ : syracuseStep 3463183 = 5194775) B5194775
theorem B1923115 : Blo 1136633 1923115 := bstep (se 1 (by rfl) ⟨1442336, by rfl⟩ : syracuseStep 1923115 = 2884673) B2884673
theorem B1136699 : Blo 1136633 1136699 := bstep (se 1 (by rfl) ⟨852524, by rfl⟩ : syracuseStep 1136699 = 1705049) B1705049
theorem B1136775 : Blo 1136633 1136775 := bstep (se 1 (by rfl) ⟨852581, by rfl⟩ : syracuseStep 1136775 = 1705163) B1705163
theorem B1136783 : Blo 1136633 1136783 := bstep (se 1 (by rfl) ⟨852587, by rfl⟩ : syracuseStep 1136783 = 1705175) B1705175
theorem B1923257 : Blo 1136633 1923257 := bstep (se 2 (by rfl) ⟨721221, by rfl⟩ : syracuseStep 1923257 = 1442443) B1442443
theorem B1136827 : Blo 1136633 1136827 := bstep (se 1 (by rfl) ⟨852620, by rfl⟩ : syracuseStep 1136827 = 1705241) B1705241
theorem B1136903 : Blo 1136633 1136903 := bstep (se 1 (by rfl) ⟨852677, by rfl⟩ : syracuseStep 1136903 = 1705355) B1705355
theorem B1136911 : Blo 1136633 1136911 := bstep (se 1 (by rfl) ⟨852683, by rfl⟩ : syracuseStep 1136911 = 1705367) B1705367
theorem B1136955 : Blo 1136633 1136955 := bstep (se 1 (by rfl) ⟨852716, by rfl⟩ : syracuseStep 1136955 = 1705433) B1705433
theorem B1137031 : Blo 1136633 1137031 := bstep (se 1 (by rfl) ⟨852773, by rfl⟩ : syracuseStep 1137031 = 1705547) B1705547
theorem B1137039 : Blo 1136633 1137039 := bstep (se 1 (by rfl) ⟨852779, by rfl⟩ : syracuseStep 1137039 = 1705559) B1705559
theorem B1137083 : Blo 1136633 1137083 := bstep (se 1 (by rfl) ⟨852812, by rfl⟩ : syracuseStep 1137083 = 1705625) B1705625
theorem B1137159 : Blo 1136633 1137159 := bstep (se 1 (by rfl) ⟨852869, by rfl⟩ : syracuseStep 1137159 = 1705739) B1705739
theorem B1137167 : Blo 1136633 1137167 := bstep (se 1 (by rfl) ⟨852875, by rfl⟩ : syracuseStep 1137167 = 1705751) B1705751
theorem B4610603 : Blo 1136633 4610603 := bstep (se 1 (by rfl) ⟨3457952, by rfl⟩ : syracuseStep 4610603 = 6915905) B6915905
theorem B1137211 : Blo 1136633 1137211 := bstep (se 1 (by rfl) ⟨852908, by rfl⟩ : syracuseStep 1137211 = 1705817) B1705817
theorem B1137287 : Blo 1136633 1137287 := bstep (se 1 (by rfl) ⟨852965, by rfl⟩ : syracuseStep 1137287 = 1705931) B1705931
theorem B1137295 : Blo 1136633 1137295 := bstep (se 1 (by rfl) ⟨852971, by rfl⟩ : syracuseStep 1137295 = 1705943) B1705943
theorem B1137339 : Blo 1136633 1137339 := bstep (se 1 (by rfl) ⟨853004, by rfl⟩ : syracuseStep 1137339 = 1706009) B1706009
theorem B5757641 : Blo 1136633 5757641 := bstep (se 2 (by rfl) ⟨2159115, by rfl⟩ : syracuseStep 5757641 = 4318231) B4318231
theorem B1137415 : Blo 1136633 1137415 := bstep (se 1 (by rfl) ⟨853061, by rfl⟩ : syracuseStep 1137415 = 1706123) B1706123
theorem B1137423 : Blo 1136633 1137423 := bstep (se 1 (by rfl) ⟨853067, by rfl⟩ : syracuseStep 1137423 = 1706135) B1706135
theorem B1137467 : Blo 1136633 1137467 := bstep (se 1 (by rfl) ⟨853100, by rfl⟩ : syracuseStep 1137467 = 1706201) B1706201
theorem B1923959 : Blo 1136633 1923959 := bstep (se 1 (by rfl) ⟨1442969, by rfl⟩ : syracuseStep 1923959 = 2885939) B2885939
theorem B1137543 : Blo 1136633 1137543 := bstep (se 1 (by rfl) ⟨853157, by rfl⟩ : syracuseStep 1137543 = 1706315) B1706315
theorem B1137551 : Blo 1136633 1137551 := bstep (se 1 (by rfl) ⟨853163, by rfl⟩ : syracuseStep 1137551 = 1706327) B1706327
theorem B1137595 : Blo 1136633 1137595 := bstep (se 1 (by rfl) ⟨853196, by rfl⟩ : syracuseStep 1137595 = 1706393) B1706393
theorem B1137671 : Blo 1136633 1137671 := bstep (se 1 (by rfl) ⟨853253, by rfl⟩ : syracuseStep 1137671 = 1706507) B1706507
theorem B5692427 : Blo 1136633 5692427 := bstep (se 1 (by rfl) ⟨4269320, by rfl⟩ : syracuseStep 5692427 = 8538641) B8538641
theorem B1137679 : Blo 1136633 1137679 := bstep (se 1 (by rfl) ⟨853259, by rfl⟩ : syracuseStep 1137679 = 1706519) B1706519
theorem B1137723 : Blo 1136633 1137723 := bstep (se 1 (by rfl) ⟨853292, by rfl⟩ : syracuseStep 1137723 = 1706585) B1706585
theorem B1137799 : Blo 1136633 1137799 := bstep (se 1 (by rfl) ⟨853349, by rfl⟩ : syracuseStep 1137799 = 1706699) B1706699
theorem B1137807 : Blo 1136633 1137807 := bstep (se 1 (by rfl) ⟨853355, by rfl⟩ : syracuseStep 1137807 = 1706711) B1706711
theorem B1137851 : Blo 1136633 1137851 := bstep (se 1 (by rfl) ⟨853388, by rfl⟩ : syracuseStep 1137851 = 1706777) B1706777
theorem B1137927 : Blo 1136633 1137927 := bstep (se 1 (by rfl) ⟨853445, by rfl⟩ : syracuseStep 1137927 = 1706891) B1706891
theorem B1137935 : Blo 1136633 1137935 := bstep (se 1 (by rfl) ⟨853451, by rfl⟩ : syracuseStep 1137935 = 1706903) B1706903
theorem B1137979 : Blo 1136633 1137979 := bstep (se 1 (by rfl) ⟨853484, by rfl⟩ : syracuseStep 1137979 = 1706969) B1706969
theorem B1924411 : Blo 1136633 1924411 := bstep (se 1 (by rfl) ⟨1443308, by rfl⟩ : syracuseStep 1924411 = 2886617) B2886617
theorem B1138055 : Blo 1136633 1138055 := bstep (se 1 (by rfl) ⟨853541, by rfl⟩ : syracuseStep 1138055 = 1707083) B1707083
theorem B1138063 : Blo 1136633 1138063 := bstep (se 1 (by rfl) ⟨853547, by rfl⟩ : syracuseStep 1138063 = 1707095) B1707095
theorem B1138107 : Blo 1136633 1138107 := bstep (se 1 (by rfl) ⟨853580, by rfl⟩ : syracuseStep 1138107 = 1707161) B1707161
theorem B1924553 : Blo 1136633 1924553 := bstep (se 2 (by rfl) ⟨721707, by rfl⟩ : syracuseStep 1924553 = 1443415) B1443415
theorem B8642051 : Blo 1136633 8642051 := bstep (se 1 (by rfl) ⟨6481538, by rfl⟩ : syracuseStep 8642051 = 12963077) B12963077
theorem B1138183 : Blo 1136633 1138183 := bstep (se 1 (by rfl) ⟨853637, by rfl⟩ : syracuseStep 1138183 = 1707275) B1707275
theorem B1138191 : Blo 1136633 1138191 := bstep (se 1 (by rfl) ⟨853643, by rfl⟩ : syracuseStep 1138191 = 1707287) B1707287
theorem B1138235 : Blo 1136633 1138235 := bstep (se 1 (by rfl) ⟨853676, by rfl⟩ : syracuseStep 1138235 = 1707353) B1707353
theorem B4316759 : Blo 1136633 4316759 := bstep (se 1 (by rfl) ⟨3237569, by rfl⟩ : syracuseStep 4316759 = 6475139) B6475139
theorem B1138311 : Blo 1136633 1138311 := bstep (se 1 (by rfl) ⟨853733, by rfl⟩ : syracuseStep 1138311 = 1707467) B1707467
theorem B1138319 : Blo 1136633 1138319 := bstep (se 1 (by rfl) ⟨853739, by rfl⟩ : syracuseStep 1138319 = 1707479) B1707479
theorem B16408241 : Blo 1136633 16408241 := bstep (se 2 (by rfl) ⟨6153090, by rfl⟩ : syracuseStep 16408241 = 12306181) B12306181
theorem B1138363 : Blo 1136633 1138363 := bstep (se 1 (by rfl) ⟨853772, by rfl⟩ : syracuseStep 1138363 = 1707545) B1707545
theorem B1138439 : Blo 1136633 1138439 := bstep (se 1 (by rfl) ⟨853829, by rfl⟩ : syracuseStep 1138439 = 1707659) B1707659
theorem B1367815 : Blo 1136633 1367815 := bstep (se 1 (by rfl) ⟨1025861, by rfl⟩ : syracuseStep 1367815 = 2051723) B2051723
theorem B1138447 : Blo 1136633 1138447 := bstep (se 1 (by rfl) ⟨853835, by rfl⟩ : syracuseStep 1138447 = 1707671) B1707671
theorem B1138491 : Blo 1136633 1138491 := bstep (se 1 (by rfl) ⟨853868, by rfl⟩ : syracuseStep 1138491 = 1707737) B1707737
theorem B1138567 : Blo 1136633 1138567 := bstep (se 1 (by rfl) ⟨853925, by rfl⟩ : syracuseStep 1138567 = 1707851) B1707851
theorem B1138575 : Blo 1136633 1138575 := bstep (se 1 (by rfl) ⟨853931, by rfl⟩ : syracuseStep 1138575 = 1707863) B1707863
theorem B1138619 : Blo 1136633 1138619 := bstep (se 1 (by rfl) ⟨853964, by rfl⟩ : syracuseStep 1138619 = 1707929) B1707929
theorem B1138695 : Blo 1136633 1138695 := bstep (se 1 (by rfl) ⟨854021, by rfl⟩ : syracuseStep 1138695 = 1708043) B1708043
theorem B1138703 : Blo 1136633 1138703 := bstep (se 1 (by rfl) ⟨854027, by rfl⟩ : syracuseStep 1138703 = 1708055) B1708055
theorem B1138747 : Blo 1136633 1138747 := bstep (se 1 (by rfl) ⟨854060, by rfl⟩ : syracuseStep 1138747 = 1708121) B1708121
theorem B4317245 : Blo 1136633 4317245 := bstep (se 3 (by rfl) ⟨809483, by rfl⟩ : syracuseStep 4317245 = 1618967) B1618967
theorem B1138823 : Blo 1136633 1138823 := bstep (se 1 (by rfl) ⟨854117, by rfl⟩ : syracuseStep 1138823 = 1708235) B1708235
theorem B1138831 : Blo 1136633 1138831 := bstep (se 1 (by rfl) ⟨854123, by rfl⟩ : syracuseStep 1138831 = 1708247) B1708247
theorem B1138875 : Blo 1136633 1138875 := bstep (se 1 (by rfl) ⟨854156, by rfl⟩ : syracuseStep 1138875 = 1708313) B1708313
theorem B1138951 : Blo 1136633 1138951 := bstep (se 1 (by rfl) ⟨854213, by rfl⟩ : syracuseStep 1138951 = 1708427) B1708427
theorem B1138959 : Blo 1136633 1138959 := bstep (se 1 (by rfl) ⟨854219, by rfl⟩ : syracuseStep 1138959 = 1708439) B1708439
theorem B1139003 : Blo 1136633 1139003 := bstep (se 1 (by rfl) ⟨854252, by rfl⟩ : syracuseStep 1139003 = 1708505) B1708505
theorem B6480263 : Blo 1136633 6480263 := bstep (se 1 (by rfl) ⟨4860197, by rfl⟩ : syracuseStep 6480263 = 9720395) B9720395
theorem B1139079 : Blo 1136633 1139079 := bstep (se 1 (by rfl) ⟨854309, by rfl⟩ : syracuseStep 1139079 = 1708619) B1708619
theorem B1139087 : Blo 1136633 1139087 := bstep (se 1 (by rfl) ⟨854315, by rfl⟩ : syracuseStep 1139087 = 1708631) B1708631
theorem B1139131 : Blo 1136633 1139131 := bstep (se 1 (by rfl) ⟨854348, by rfl⟩ : syracuseStep 1139131 = 1708697) B1708697
theorem B1139207 : Blo 1136633 1139207 := bstep (se 1 (by rfl) ⟨854405, by rfl⟩ : syracuseStep 1139207 = 1708811) B1708811
theorem B1139215 : Blo 1136633 1139215 := bstep (se 1 (by rfl) ⟨854411, by rfl⟩ : syracuseStep 1139215 = 1708823) B1708823
theorem B1139259 : Blo 1136633 1139259 := bstep (se 1 (by rfl) ⟨854444, by rfl⟩ : syracuseStep 1139259 = 1708889) B1708889
theorem B6480445 : Blo 1136633 6480445 := bstep (se 3 (by rfl) ⟨1215083, by rfl⟩ : syracuseStep 6480445 = 2430167) B2430167
theorem B1368695 : Blo 1136633 1368695 := bstep (se 1 (by rfl) ⟨1026521, by rfl⟩ : syracuseStep 1368695 = 2053043) B2053043
theorem B1139335 : Blo 1136633 1139335 := bstep (se 1 (by rfl) ⟨854501, by rfl⟩ : syracuseStep 1139335 = 1709003) B1709003
theorem B1139343 : Blo 1136633 1139343 := bstep (se 1 (by rfl) ⟨854507, by rfl⟩ : syracuseStep 1139343 = 1709015) B1709015
theorem B1139387 : Blo 1136633 1139387 := bstep (se 1 (by rfl) ⟨854540, by rfl⟩ : syracuseStep 1139387 = 1709081) B1709081
theorem B1139463 : Blo 1136633 1139463 := bstep (se 1 (by rfl) ⟨854597, by rfl⟩ : syracuseStep 1139463 = 1709195) B1709195
theorem B1139471 : Blo 1136633 1139471 := bstep (se 1 (by rfl) ⟨854603, by rfl⟩ : syracuseStep 1139471 = 1709207) B1709207
theorem B3892001 : Blo 1136633 3892001 := bstep (se 2 (by rfl) ⟨1459500, by rfl⟩ : syracuseStep 3892001 = 2919001) B2919001
theorem B1139515 : Blo 1136633 1139515 := bstep (se 1 (by rfl) ⟨854636, by rfl⟩ : syracuseStep 1139515 = 1709273) B1709273
theorem B1139591 : Blo 1136633 1139591 := bstep (se 1 (by rfl) ⟨854693, by rfl⟩ : syracuseStep 1139591 = 1709387) B1709387
theorem B1139599 : Blo 1136633 1139599 := bstep (se 1 (by rfl) ⟨854699, by rfl⟩ : syracuseStep 1139599 = 1709399) B1709399
theorem B1369003 : Blo 1136633 1369003 := bstep (se 1 (by rfl) ⟨1026752, by rfl⟩ : syracuseStep 1369003 = 2053505) B2053505
theorem B1139643 : Blo 1136633 1139643 := bstep (se 1 (by rfl) ⟨854732, by rfl⟩ : syracuseStep 1139643 = 1709465) B1709465
theorem B1139719 : Blo 1136633 1139719 := bstep (se 1 (by rfl) ⟨854789, by rfl⟩ : syracuseStep 1139719 = 1709579) B1709579
theorem B1139727 : Blo 1136633 1139727 := bstep (se 1 (by rfl) ⟨854795, by rfl⟩ : syracuseStep 1139727 = 1709591) B1709591
theorem B3236897 : Blo 1136633 3236897 := bstep (se 2 (by rfl) ⟨1213836, by rfl⟩ : syracuseStep 3236897 = 2427673) B2427673
theorem B3466273 : Blo 1136633 3466273 := bstep (se 2 (by rfl) ⟨1299852, by rfl⟩ : syracuseStep 3466273 = 2599705) B2599705
theorem B1139771 : Blo 1136633 1139771 := bstep (se 1 (by rfl) ⟨854828, by rfl⟩ : syracuseStep 1139771 = 1709657) B1709657
theorem B1139847 : Blo 1136633 1139847 := bstep (se 1 (by rfl) ⟨854885, by rfl⟩ : syracuseStep 1139847 = 1709771) B1709771
theorem B1139855 : Blo 1136633 1139855 := bstep (se 1 (by rfl) ⟨854891, by rfl⟩ : syracuseStep 1139855 = 1709783) B1709783
theorem B1139899 : Blo 1136633 1139899 := bstep (se 1 (by rfl) ⟨854924, by rfl⟩ : syracuseStep 1139899 = 1709849) B1709849
theorem B1139975 : Blo 1136633 1139975 := bstep (se 1 (by rfl) ⟨854981, by rfl⟩ : syracuseStep 1139975 = 1709963) B1709963
theorem B1139983 : Blo 1136633 1139983 := bstep (se 1 (by rfl) ⟨854987, by rfl⟩ : syracuseStep 1139983 = 1709975) B1709975
theorem B1369387 : Blo 1136633 1369387 := bstep (se 1 (by rfl) ⟨1027040, by rfl⟩ : syracuseStep 1369387 = 2054081) B2054081
theorem B1140027 : Blo 1136633 1140027 := bstep (se 1 (by rfl) ⟨855020, by rfl⟩ : syracuseStep 1140027 = 1710041) B1710041
theorem B3237239 : Blo 1136633 3237239 := bstep (se 1 (by rfl) ⟨2427929, by rfl⟩ : syracuseStep 3237239 = 4855859) B4855859
theorem B1140103 : Blo 1136633 1140103 := bstep (se 1 (by rfl) ⟨855077, by rfl⟩ : syracuseStep 1140103 = 1710155) B1710155
theorem B1140111 : Blo 1136633 1140111 := bstep (se 1 (by rfl) ⟨855083, by rfl⟩ : syracuseStep 1140111 = 1710167) B1710167
theorem B1140155 : Blo 1136633 1140155 := bstep (se 1 (by rfl) ⟨855116, by rfl⟩ : syracuseStep 1140155 = 1710233) B1710233
theorem B1140231 : Blo 1136633 1140231 := bstep (se 1 (by rfl) ⟨855173, by rfl⟩ : syracuseStep 1140231 = 1710347) B1710347
theorem B1140239 : Blo 1136633 1140239 := bstep (se 1 (by rfl) ⟨855179, by rfl⟩ : syracuseStep 1140239 = 1710359) B1710359
theorem B7300651 : Blo 1136633 7300651 := bstep (se 1 (by rfl) ⟨5475488, by rfl⟩ : syracuseStep 7300651 = 10950977) B10950977
theorem B1140283 : Blo 1136633 1140283 := bstep (se 1 (by rfl) ⟨855212, by rfl⟩ : syracuseStep 1140283 = 1710425) B1710425
theorem B1140359 : Blo 1136633 1140359 := bstep (se 1 (by rfl) ⟨855269, by rfl⟩ : syracuseStep 1140359 = 1710539) B1710539
theorem B1140367 : Blo 1136633 1140367 := bstep (se 1 (by rfl) ⟨855275, by rfl⟩ : syracuseStep 1140367 = 1710551) B1710551
theorem B1140411 : Blo 1136633 1140411 := bstep (se 1 (by rfl) ⟨855308, by rfl⟩ : syracuseStep 1140411 = 1710617) B1710617
theorem B1140487 : Blo 1136633 1140487 := bstep (se 1 (by rfl) ⟨855365, by rfl⟩ : syracuseStep 1140487 = 1710731) B1710731
theorem B4318991 : Blo 1136633 4318991 := bstep (se 1 (by rfl) ⟨3239243, by rfl⟩ : syracuseStep 4318991 = 6478487) B6478487
theorem B1140495 : Blo 1136633 1140495 := bstep (se 1 (by rfl) ⟨855371, by rfl⟩ : syracuseStep 1140495 = 1710743) B1710743
theorem B1140539 : Blo 1136633 1140539 := bstep (se 1 (by rfl) ⟨855404, by rfl⟩ : syracuseStep 1140539 = 1710809) B1710809
theorem B1140615 : Blo 1136633 1140615 := bstep (se 1 (by rfl) ⟨855461, by rfl⟩ : syracuseStep 1140615 = 1710923) B1710923
theorem B1140623 : Blo 1136633 1140623 := bstep (se 1 (by rfl) ⟨855467, by rfl⟩ : syracuseStep 1140623 = 1710935) B1710935
theorem B3074201 : Blo 1136633 3074201 := bstep (se 2 (by rfl) ⟨1152825, by rfl⟩ : syracuseStep 3074201 = 2305651) B2305651
theorem B21883121 : Blo 1136633 21883121 := bstep (se 2 (by rfl) ⟨8206170, by rfl⟩ : syracuseStep 21883121 = 16412341) B16412341
theorem B6482177 : Blo 1136633 6482177 := bstep (se 2 (by rfl) ⟨2430816, by rfl⟩ : syracuseStep 6482177 = 4861633) B4861633
theorem B2877707 : Blo 1136633 2877707 := bstep (se 1 (by rfl) ⟨2158280, by rfl⟩ : syracuseStep 2877707 = 4316561) B4316561
theorem B328362457 : Blo 1136633 328362457 := bstep (se 2 (by rfl) ⟨123135921, by rfl⟩ : syracuseStep 328362457 = 246271843) B246271843
theorem B12315179 : Blo 1136633 12315179 := bstep (se 1 (by rfl) ⟨9236384, by rfl⟩ : syracuseStep 12315179 = 18472769) B18472769
theorem B1731385 : Blo 1136633 1731385 := bstep (se 2 (by rfl) ⟨649269, by rfl⟩ : syracuseStep 1731385 = 1298539) B1298539
theorem B2878355 : Blo 1136633 2878355 := bstep (se 1 (by rfl) ⟨2158766, by rfl⟩ : syracuseStep 2878355 = 4317533) B4317533
theorem B3894301 : Blo 1136633 3894301 := bstep (se 3 (by rfl) ⟨730181, by rfl⟩ : syracuseStep 3894301 = 1460363) B1460363
theorem B2878649 : Blo 1136633 2878649 := bstep (se 2 (by rfl) ⟨1079493, by rfl⟩ : syracuseStep 2878649 = 2158987) B2158987
theorem B4320647 : Blo 1136633 4320647 := bstep (se 1 (by rfl) ⟨3240485, by rfl⟩ : syracuseStep 4320647 = 6480971) B6480971
theorem B3075617 : Blo 1136633 3075617 := bstep (se 2 (by rfl) ⟨1153356, by rfl⟩ : syracuseStep 3075617 = 2306713) B2306713
theorem B2158265 : Blo 1136633 2158265 := bstep (se 2 (by rfl) ⟨809349, by rfl⟩ : syracuseStep 2158265 = 1618699) B1618699
theorem B6156013 : Blo 1136633 6156013 := bstep (se 3 (by rfl) ⟨1154252, by rfl⟩ : syracuseStep 6156013 = 2308505) B2308505
theorem B12971825 : Blo 1136633 12971825 := bstep (se 2 (by rfl) ⟨4864434, by rfl⟩ : syracuseStep 12971825 = 9728869) B9728869
theorem B3239767 : Blo 1136633 3239767 := bstep (se 1 (by rfl) ⟨2429825, by rfl⟩ : syracuseStep 3239767 = 4859651) B4859651
theorem B6156121 : Blo 1136633 6156121 := bstep (se 2 (by rfl) ⟨2308545, by rfl⟩ : syracuseStep 6156121 = 4617091) B4617091
theorem B2879347 : Blo 1136633 2879347 := bstep (se 1 (by rfl) ⟨2159510, by rfl⟩ : syracuseStep 2879347 = 4319021) B4319021
theorem B2879489 : Blo 1136633 2879489 := bstep (se 2 (by rfl) ⟨1079808, by rfl⟩ : syracuseStep 2879489 = 2159617) B2159617
theorem B25260055 : Blo 1136633 25260055 := bstep (se 1 (by rfl) ⟨18945041, by rfl⟩ : syracuseStep 25260055 = 37890083) B37890083
theorem B3239995 : Blo 1136633 3239995 := bstep (se 1 (by rfl) ⟨2429996, by rfl⟩ : syracuseStep 3239995 = 4859993) B4859993
theorem B4616279 : Blo 1136633 4616279 := bstep (se 1 (by rfl) ⟨3462209, by rfl⟩ : syracuseStep 4616279 = 6924419) B6924419
theorem B3240121 : Blo 1136633 3240121 := bstep (se 2 (by rfl) ⟨1215045, by rfl⟩ : syracuseStep 3240121 = 2430091) B2430091
theorem B1732795 : Blo 1136633 1732795 := bstep (se 1 (by rfl) ⟨1299596, by rfl⟩ : syracuseStep 1732795 = 2599193) B2599193
theorem B5468417 : Blo 1136633 5468417 := bstep (se 2 (by rfl) ⟨2050656, by rfl⟩ : syracuseStep 5468417 = 4101313) B4101313
theorem B4616507 : Blo 1136633 4616507 := bstep (se 1 (by rfl) ⟨3462380, by rfl⟩ : syracuseStep 4616507 = 6924761) B6924761
theorem B5763473 : Blo 1136633 5763473 := bstep (se 2 (by rfl) ⟨2161302, by rfl⟩ : syracuseStep 5763473 = 4322605) B4322605
theorem B2879945 : Blo 1136633 2879945 := bstep (se 2 (by rfl) ⟨1079979, by rfl⟩ : syracuseStep 2879945 = 2159959) B2159959
theorem B168489557 : Blo 1136633 168489557 := bstep (se 8 (by rfl) ⟨987243, by rfl⟩ : syracuseStep 168489557 = 1974487) B1974487
theorem B8647397 : Blo 1136633 8647397 := bstep (se 4 (by rfl) ⟨810693, by rfl⟩ : syracuseStep 8647397 = 1621387) B1621387
theorem B2880299 : Blo 1136633 2880299 := bstep (se 1 (by rfl) ⟨2160224, by rfl⟩ : syracuseStep 2880299 = 4320449) B4320449
theorem B1438651 : Blo 1136633 1438651 := bstep (se 1 (by rfl) ⟨1078988, by rfl⟩ : syracuseStep 1438651 = 2157977) B2157977
theorem B3077065 : Blo 1136633 3077065 := bstep (se 2 (by rfl) ⟨1153899, by rfl⟩ : syracuseStep 3077065 = 2307799) B2307799
theorem B7304215 : Blo 1136633 7304215 := bstep (se 1 (by rfl) ⟨5478161, by rfl⟩ : syracuseStep 7304215 = 10956323) B10956323
theorem B4322423 : Blo 1136633 4322423 := bstep (se 1 (by rfl) ⟨3241817, by rfl⟩ : syracuseStep 4322423 = 6483635) B6483635
theorem B1439147 : Blo 1136633 1439147 := bstep (se 1 (by rfl) ⟨1079360, by rfl⟩ : syracuseStep 1439147 = 2158721) B2158721
theorem B2160263 : Blo 1136633 2160263 := bstep (se 1 (by rfl) ⟨1620197, by rfl⟩ : syracuseStep 2160263 = 3240395) B3240395
theorem B2881291 : Blo 1136633 2881291 := bstep (se 1 (by rfl) ⟨2160968, by rfl⟩ : syracuseStep 2881291 = 4321937) B4321937
theorem B1439623 : Blo 1136633 1439623 := bstep (se 1 (by rfl) ⟨1079717, by rfl⟩ : syracuseStep 1439623 = 2159435) B2159435
theorem B2881433 : Blo 1136633 2881433 := bstep (se 2 (by rfl) ⟨1080537, by rfl⟩ : syracuseStep 2881433 = 2161075) B2161075
theorem B5339033 : Blo 1136633 5339033 := bstep (se 2 (by rfl) ⟨2002137, by rfl⟩ : syracuseStep 5339033 = 4004275) B4004275
theorem B2881595 : Blo 1136633 2881595 := bstep (se 1 (by rfl) ⟨2161196, by rfl⟩ : syracuseStep 2881595 = 4322393) B4322393
theorem B3242045 : Blo 1136633 3242045 := bstep (se 3 (by rfl) ⟨607883, by rfl⟩ : syracuseStep 3242045 = 1215767) B1215767
theorem B4323395 : Blo 1136633 4323395 := bstep (se 1 (by rfl) ⟨3242546, by rfl⟩ : syracuseStep 4323395 = 6485093) B6485093
theorem B1440119 : Blo 1136633 1440119 := bstep (se 1 (by rfl) ⟨1080089, by rfl⟩ : syracuseStep 1440119 = 2160179) B2160179
theorem B2881939 : Blo 1136633 2881939 := bstep (se 1 (by rfl) ⟨2161454, by rfl⟩ : syracuseStep 2881939 = 4322909) B4322909
theorem B5765579 : Blo 1136633 5765579 := bstep (se 1 (by rfl) ⟨4324184, by rfl⟩ : syracuseStep 5765579 = 8648369) B8648369
theorem B4323851 : Blo 1136633 4323851 := bstep (se 1 (by rfl) ⟨3242888, by rfl⟩ : syracuseStep 4323851 = 6485777) B6485777
theorem B1440271 : Blo 1136633 1440271 := bstep (se 1 (by rfl) ⟨1080203, by rfl⟩ : syracuseStep 1440271 = 2160407) B2160407
theorem B6486551 : Blo 1136633 6486551 := bstep (se 1 (by rfl) ⟨4864913, by rfl⟩ : syracuseStep 6486551 = 9729827) B9729827
theorem B2882081 : Blo 1136633 2882081 := bstep (se 2 (by rfl) ⟨1080780, by rfl⟩ : syracuseStep 2882081 = 2161561) B2161561
theorem B1440443 : Blo 1136633 1440443 := bstep (se 1 (by rfl) ⟨1080332, by rfl⟩ : syracuseStep 1440443 = 2160665) B2160665
theorem B5765903 : Blo 1136633 5765903 := bstep (se 1 (by rfl) ⟨4324427, by rfl⟩ : syracuseStep 5765903 = 8648855) B8648855
theorem B9730853 : Blo 1136633 9730853 := bstep (se 4 (by rfl) ⟨912267, by rfl⟩ : syracuseStep 9730853 = 1824535) B1824535
theorem B3243037 : Blo 1136633 3243037 := bstep (se 3 (by rfl) ⟨608069, by rfl⟩ : syracuseStep 3243037 = 1216139) B1216139
theorem B19725373 : Blo 1136633 19725373 := bstep (se 3 (by rfl) ⟨3698507, by rfl⟩ : syracuseStep 19725373 = 7397015) B7397015
theorem B2161865 : Blo 1136633 2161865 := bstep (se 2 (by rfl) ⟨810699, by rfl⟩ : syracuseStep 2161865 = 1621399) B1621399
theorem B9239993 : Blo 1136633 9239993 := bstep (se 2 (by rfl) ⟨3464997, by rfl⟩ : syracuseStep 9239993 = 6929995) B6929995
theorem B39386573 : Blo 1136633 39386573 := bstep (se 3 (by rfl) ⟨7384982, by rfl⟩ : syracuseStep 39386573 = 14769965) B14769965
theorem B2883073 : Blo 1136633 2883073 := bstep (se 2 (by rfl) ⟨1081152, by rfl⟩ : syracuseStep 2883073 = 2162305) B2162305
theorem B6159883 : Blo 1136633 6159883 := bstep (se 1 (by rfl) ⟨4619912, by rfl⟩ : syracuseStep 6159883 = 9239825) B9239825
theorem B1441415 : Blo 1136633 1441415 := bstep (se 1 (by rfl) ⟨1081061, by rfl⟩ : syracuseStep 1441415 = 2162123) B2162123
theorem B7307009 : Blo 1136633 7307009 := bstep (se 2 (by rfl) ⟨2740128, by rfl⟩ : syracuseStep 7307009 = 5480257) B5480257
theorem B2163323 : Blo 1136633 2163323 := bstep (se 1 (by rfl) ⟨1622492, by rfl⟩ : syracuseStep 2163323 = 3244985) B3244985
theorem B5472953 : Blo 1136633 5472953 := bstep (se 2 (by rfl) ⟨2052357, by rfl⟩ : syracuseStep 5472953 = 4104715) B4104715
theorem B5768009 : Blo 1136633 5768009 := bstep (se 2 (by rfl) ⟨2163003, by rfl⟩ : syracuseStep 5768009 = 4326007) B4326007
theorem B3244961 : Blo 1136633 3244961 := bstep (se 2 (by rfl) ⟨1216860, by rfl⟩ : syracuseStep 3244961 = 2433721) B2433721
theorem B1278895 : Blo 1136633 1278895 := bstep (se 1 (by rfl) ⟨959171, by rfl⟩ : syracuseStep 1278895 = 1918343) B1918343
theorem B4326479 : Blo 1136633 4326479 := bstep (se 1 (by rfl) ⟨3244859, by rfl⟩ : syracuseStep 4326479 = 6489719) B6489719
theorem B2163809 : Blo 1136633 2163809 := bstep (se 2 (by rfl) ⟨811428, by rfl⟩ : syracuseStep 2163809 = 1622857) B1622857
theorem B9372791 : Blo 1136633 9372791 := bstep (se 1 (by rfl) ⟨7029593, by rfl⟩ : syracuseStep 9372791 = 14059187) B14059187
theorem B2884855 : Blo 1136633 2884855 := bstep (se 1 (by rfl) ⟨2163641, by rfl⟩ : syracuseStep 2884855 = 4327283) B4327283
theorem B1279327 : Blo 1136633 1279327 := bstep (se 1 (by rfl) ⟨959495, by rfl⟩ : syracuseStep 1279327 = 1918991) B1918991
theorem B3245417 : Blo 1136633 3245417 := bstep (se 2 (by rfl) ⟨1217031, by rfl⟩ : syracuseStep 3245417 = 2434063) B2434063
theorem B4621697 : Blo 1136633 4621697 := bstep (se 2 (by rfl) ⟨1733136, by rfl⟩ : syracuseStep 4621697 = 3466273) B3466273
theorem B1705391 : Blo 1136633 1705391 := bstep (se 1 (by rfl) ⟨1279043, by rfl⟩ : syracuseStep 1705391 = 2558087) B2558087
theorem B2164151 : Blo 1136633 2164151 := bstep (se 1 (by rfl) ⟨1623113, by rfl⟩ : syracuseStep 2164151 = 3246227) B3246227
theorem B1705481 : Blo 1136633 1705481 := bstep (se 2 (by rfl) ⟨639555, by rfl⟩ : syracuseStep 1705481 = 1279111) B1279111
theorem B2885129 : Blo 1136633 2885129 := bstep (se 2 (by rfl) ⟨1081923, by rfl⟩ : syracuseStep 2885129 = 2163847) B2163847
theorem B1705511 : Blo 1136633 1705511 := bstep (se 1 (by rfl) ⟨1279133, by rfl⟩ : syracuseStep 1705511 = 2558267) B2558267
theorem B2885159 : Blo 1136633 2885159 := bstep (se 1 (by rfl) ⟨2163869, by rfl⟩ : syracuseStep 2885159 = 4327739) B4327739
theorem B1705595 : Blo 1136633 1705595 := bstep (se 1 (by rfl) ⟨1279196, by rfl⟩ : syracuseStep 1705595 = 2558393) B2558393
theorem B1279687 : Blo 1136633 1279687 := bstep (se 1 (by rfl) ⟨959765, by rfl⟩ : syracuseStep 1279687 = 1919531) B1919531
theorem B1705721 : Blo 1136633 1705721 := bstep (se 2 (by rfl) ⟨639645, by rfl⟩ : syracuseStep 1705721 = 1279291) B1279291
theorem B2164553 : Blo 1136633 2164553 := bstep (se 2 (by rfl) ⟨811707, by rfl⟩ : syracuseStep 2164553 = 1623415) B1623415
theorem B1705823 : Blo 1136633 1705823 := bstep (se 1 (by rfl) ⟨1279367, by rfl⟩ : syracuseStep 1705823 = 2558735) B2558735
theorem B1705835 : Blo 1136633 1705835 := bstep (se 1 (by rfl) ⟨1279376, by rfl⟩ : syracuseStep 1705835 = 2558753) B2558753
theorem B2885483 : Blo 1136633 2885483 := bstep (se 1 (by rfl) ⟨2164112, by rfl⟩ : syracuseStep 2885483 = 4328225) B4328225
theorem B2557871 : Blo 1136633 2557871 := bstep (se 1 (by rfl) ⟨1918403, by rfl⟩ : syracuseStep 2557871 = 3836807) B3836807
theorem B9734201 : Blo 1136633 9734201 := bstep (se 2 (by rfl) ⟨3650325, by rfl⟩ : syracuseStep 9734201 = 7300651) B7300651
theorem B1706063 : Blo 1136633 1706063 := bstep (se 1 (by rfl) ⟨1279547, by rfl⟩ : syracuseStep 1706063 = 2559095) B2559095
theorem B5769305 : Blo 1136633 5769305 := bstep (se 2 (by rfl) ⟨2163489, by rfl⟩ : syracuseStep 5769305 = 4326979) B4326979
theorem B2558123 : Blo 1136633 2558123 := bstep (se 1 (by rfl) ⟨1918592, by rfl⟩ : syracuseStep 2558123 = 3837185) B3837185
theorem B1706183 : Blo 1136633 1706183 := bstep (se 1 (by rfl) ⟨1279637, by rfl⟩ : syracuseStep 1706183 = 2559275) B2559275
theorem B1706345 : Blo 1136633 1706345 := bstep (se 2 (by rfl) ⟨639879, by rfl⟩ : syracuseStep 1706345 = 1279759) B1279759
theorem B1706423 : Blo 1136633 1706423 := bstep (se 1 (by rfl) ⟨1279817, by rfl⟩ : syracuseStep 1706423 = 2559635) B2559635
theorem B1706459 : Blo 1136633 1706459 := bstep (se 1 (by rfl) ⟨1279844, by rfl⟩ : syracuseStep 1706459 = 2559689) B2559689
theorem B2886131 : Blo 1136633 2886131 := bstep (se 1 (by rfl) ⟨2164598, by rfl⟩ : syracuseStep 2886131 = 4329197) B4329197
theorem B2165267 : Blo 1136633 2165267 := bstep (se 1 (by rfl) ⟨1623950, by rfl⟩ : syracuseStep 2165267 = 3247901) B3247901
theorem B1280551 : Blo 1136633 1280551 := bstep (se 1 (by rfl) ⟨960413, by rfl⟩ : syracuseStep 1280551 = 1920827) B1920827
theorem B2165305 : Blo 1136633 2165305 := bstep (se 2 (by rfl) ⟨811989, by rfl⟩ : syracuseStep 2165305 = 1623979) B1623979
theorem B2558663 : Blo 1136633 2558663 := bstep (se 1 (by rfl) ⟨1918997, by rfl⟩ : syracuseStep 2558663 = 3837995) B3837995
theorem B4098775 : Blo 1136633 4098775 := bstep (se 1 (by rfl) ⟨3074081, by rfl⟩ : syracuseStep 4098775 = 6148163) B6148163
theorem B8653715 : Blo 1136633 8653715 := bstep (se 1 (by rfl) ⟨6490286, by rfl⟩ : syracuseStep 8653715 = 12980573) B12980573
theorem B1706927 : Blo 1136633 1706927 := bstep (se 1 (by rfl) ⟨1280195, by rfl⟩ : syracuseStep 1706927 = 2560391) B2560391
theorem B2886587 : Blo 1136633 2886587 := bstep (se 1 (by rfl) ⟨2164940, by rfl⟩ : syracuseStep 2886587 = 4329881) B4329881
theorem B1707017 : Blo 1136633 1707017 := bstep (se 2 (by rfl) ⟨640131, by rfl⟩ : syracuseStep 1707017 = 1280263) B1280263
theorem B1707047 : Blo 1136633 1707047 := bstep (se 1 (by rfl) ⟨1280285, by rfl⟩ : syracuseStep 1707047 = 2560571) B2560571
theorem B1707131 : Blo 1136633 1707131 := bstep (se 1 (by rfl) ⟨1280348, by rfl⟩ : syracuseStep 1707131 = 2560697) B2560697
theorem B1707257 : Blo 1136633 1707257 := bstep (se 2 (by rfl) ⟨640221, by rfl⟩ : syracuseStep 1707257 = 1280443) B1280443
theorem B437816609 : Blo 1136633 437816609 := bstep (se 2 (by rfl) ⟨164181228, by rfl⟩ : syracuseStep 437816609 = 328362457) B328362457
theorem B1707359 : Blo 1136633 1707359 := bstep (se 1 (by rfl) ⟨1280519, by rfl⟩ : syracuseStep 1707359 = 2561039) B2561039
theorem B1707371 : Blo 1136633 1707371 := bstep (se 1 (by rfl) ⟨1280528, by rfl⟩ : syracuseStep 1707371 = 2561057) B2561057
theorem B4328923 : Blo 1136633 4328923 := bstep (se 1 (by rfl) ⟨3246692, by rfl⟩ : syracuseStep 4328923 = 6493385) B6493385
theorem B2559527 : Blo 1136633 2559527 := bstep (se 1 (by rfl) ⟨1919645, by rfl⟩ : syracuseStep 2559527 = 3839291) B3839291
theorem B1707599 : Blo 1136633 1707599 := bstep (se 1 (by rfl) ⟨1280699, by rfl⟩ : syracuseStep 1707599 = 2561399) B2561399
theorem B6917729 : Blo 1136633 6917729 := bstep (se 2 (by rfl) ⟨2594148, by rfl⟩ : syracuseStep 6917729 = 5188297) B5188297
theorem B3837563 : Blo 1136633 3837563 := bstep (se 1 (by rfl) ⟨2878172, by rfl⟩ : syracuseStep 3837563 = 5756345) B5756345
theorem B1707719 : Blo 1136633 1707719 := bstep (se 1 (by rfl) ⟨1280789, by rfl⟩ : syracuseStep 1707719 = 2561579) B2561579
theorem B2920151 : Blo 1136633 2920151 := bstep (se 1 (by rfl) ⟨2190113, by rfl⟩ : syracuseStep 2920151 = 4380227) B4380227
theorem B3837725 : Blo 1136633 3837725 := bstep (se 3 (by rfl) ⟨719573, by rfl⟩ : syracuseStep 3837725 = 1439147) B1439147
theorem B8654687 : Blo 1136633 8654687 := bstep (se 1 (by rfl) ⟨6491015, by rfl⟩ : syracuseStep 8654687 = 12982031) B12982031
theorem B1707881 : Blo 1136633 1707881 := bstep (se 2 (by rfl) ⟨640455, by rfl⟩ : syracuseStep 1707881 = 1280911) B1280911
theorem B2559851 : Blo 1136633 2559851 := bstep (se 1 (by rfl) ⟨1919888, by rfl⟩ : syracuseStep 2559851 = 3839777) B3839777
theorem B36966293 : Blo 1136633 36966293 := bstep (se 6 (by rfl) ⟨866397, by rfl⟩ : syracuseStep 36966293 = 1732795) B1732795
theorem B2559905 : Blo 1136633 2559905 := bstep (se 2 (by rfl) ⟨959964, by rfl⟩ : syracuseStep 2559905 = 1919929) B1919929
theorem B1707959 : Blo 1136633 1707959 := bstep (se 1 (by rfl) ⟨1280969, by rfl⟩ : syracuseStep 1707959 = 2561939) B2561939
theorem B1642459 : Blo 1136633 1642459 := bstep (se 1 (by rfl) ⟨1231844, by rfl⟩ : syracuseStep 1642459 = 2463689) B2463689
theorem B1707995 : Blo 1136633 1707995 := bstep (se 1 (by rfl) ⟨1280996, by rfl⟩ : syracuseStep 1707995 = 2561993) B2561993
theorem B3641345 : Blo 1136633 3641345 := bstep (se 2 (by rfl) ⟨1365504, by rfl⟩ : syracuseStep 3641345 = 2731009) B2731009
theorem B1282171 : Blo 1136633 1282171 := bstep (se 1 (by rfl) ⟨961628, by rfl⟩ : syracuseStep 1282171 = 1923257) B1923257
theorem B2560247 : Blo 1136633 2560247 := bstep (se 1 (by rfl) ⟨1920185, by rfl⟩ : syracuseStep 2560247 = 3840371) B3840371
theorem B9245015 : Blo 1136633 9245015 := bstep (se 1 (by rfl) ⟨6933761, by rfl⟩ : syracuseStep 9245015 = 13867523) B13867523
theorem B19468673 : Blo 1136633 19468673 := bstep (se 2 (by rfl) ⟨7300752, by rfl⟩ : syracuseStep 19468673 = 14601505) B14601505
theorem B1708463 : Blo 1136633 1708463 := bstep (se 1 (by rfl) ⟨1281347, by rfl⟩ : syracuseStep 1708463 = 2562695) B2562695
theorem B3838427 : Blo 1136633 3838427 := bstep (se 1 (by rfl) ⟨2878820, by rfl⟩ : syracuseStep 3838427 = 5757641) B5757641
theorem B1708553 : Blo 1136633 1708553 := bstep (se 2 (by rfl) ⟨640707, by rfl⟩ : syracuseStep 1708553 = 1281415) B1281415
theorem B12325385 : Blo 1136633 12325385 := bstep (se 2 (by rfl) ⟨4622019, by rfl⟩ : syracuseStep 12325385 = 9244039) B9244039
theorem B1708583 : Blo 1136633 1708583 := bstep (se 1 (by rfl) ⟨1281437, by rfl⟩ : syracuseStep 1708583 = 2562875) B2562875
theorem B1282639 : Blo 1136633 1282639 := bstep (se 1 (by rfl) ⟨961979, by rfl⟩ : syracuseStep 1282639 = 1923959) B1923959
theorem B1708667 : Blo 1136633 1708667 := bstep (se 1 (by rfl) ⟨1281500, by rfl⟩ : syracuseStep 1708667 = 2563001) B2563001
theorem B4330169 : Blo 1136633 4330169 := bstep (se 2 (by rfl) ⟨1623813, by rfl⟩ : syracuseStep 4330169 = 3247627) B3247627
theorem B4330199 : Blo 1136633 4330199 := bstep (se 1 (by rfl) ⟨3247649, by rfl⟩ : syracuseStep 4330199 = 6495299) B6495299
theorem B2429689 : Blo 1136633 2429689 := bstep (se 2 (by rfl) ⟨911133, by rfl⟩ : syracuseStep 2429689 = 1822267) B1822267
theorem B1708793 : Blo 1136633 1708793 := bstep (se 2 (by rfl) ⟨640797, by rfl⟩ : syracuseStep 1708793 = 1281595) B1281595
theorem B2560841 : Blo 1136633 2560841 := bstep (se 2 (by rfl) ⟨960315, by rfl⟩ : syracuseStep 2560841 = 1920631) B1920631
theorem B1708895 : Blo 1136633 1708895 := bstep (se 1 (by rfl) ⟨1281671, by rfl⟩ : syracuseStep 1708895 = 2563343) B2563343
theorem B1708907 : Blo 1136633 1708907 := bstep (se 1 (by rfl) ⟨1281680, by rfl⟩ : syracuseStep 1708907 = 2563361) B2563361
theorem B1283035 : Blo 1136633 1283035 := bstep (se 1 (by rfl) ⟨962276, by rfl⟩ : syracuseStep 1283035 = 1924553) B1924553
theorem B1709135 : Blo 1136633 1709135 := bstep (se 1 (by rfl) ⟨1281851, by rfl⟩ : syracuseStep 1709135 = 2563703) B2563703
theorem B7803983 : Blo 1136633 7803983 := bstep (se 1 (by rfl) ⟨5852987, by rfl⟩ : syracuseStep 7803983 = 11705975) B11705975
theorem B3839129 : Blo 1136633 3839129 := bstep (se 2 (by rfl) ⟨1439673, by rfl⟩ : syracuseStep 3839129 = 2879347) B2879347
theorem B1709255 : Blo 1136633 1709255 := bstep (se 1 (by rfl) ⟨1281941, by rfl⟩ : syracuseStep 1709255 = 2563883) B2563883
theorem B1709417 : Blo 1136633 1709417 := bstep (se 2 (by rfl) ⟨641031, by rfl⟩ : syracuseStep 1709417 = 1282063) B1282063
theorem B1709495 : Blo 1136633 1709495 := bstep (se 1 (by rfl) ⟨1282121, by rfl⟩ : syracuseStep 1709495 = 2564243) B2564243
theorem B1709531 : Blo 1136633 1709531 := bstep (se 1 (by rfl) ⟨1282148, by rfl⟩ : syracuseStep 1709531 = 2564297) B2564297
theorem B2561633 : Blo 1136633 2561633 := bstep (se 2 (by rfl) ⟨960612, by rfl⟩ : syracuseStep 2561633 = 1921225) B1921225
theorem B6493841 : Blo 1136633 6493841 := bstep (se 2 (by rfl) ⟨2435190, by rfl⟩ : syracuseStep 6493841 = 4870381) B4870381
theorem B4855619 : Blo 1136633 4855619 := bstep (se 1 (by rfl) ⟨3641714, by rfl⟩ : syracuseStep 4855619 = 7283429) B7283429
theorem B8197955 : Blo 1136633 8197955 := bstep (se 1 (by rfl) ⟨6148466, by rfl⟩ : syracuseStep 8197955 = 12296933) B12296933
theorem B1709999 : Blo 1136633 1709999 := bstep (se 1 (by rfl) ⟨1282499, by rfl⟩ : syracuseStep 1709999 = 2564999) B2564999
theorem B2561975 : Blo 1136633 2561975 := bstep (se 1 (by rfl) ⟨1921481, by rfl⟩ : syracuseStep 2561975 = 3842963) B3842963
theorem B1710089 : Blo 1136633 1710089 := bstep (se 2 (by rfl) ⟨641283, by rfl⟩ : syracuseStep 1710089 = 1282567) B1282567
theorem B1710119 : Blo 1136633 1710119 := bstep (se 1 (by rfl) ⟨1282589, by rfl⟩ : syracuseStep 1710119 = 2565179) B2565179
theorem B8755289 : Blo 1136633 8755289 := bstep (se 2 (by rfl) ⟨3283233, by rfl⟩ : syracuseStep 8755289 = 6566467) B6566467
theorem B1710203 : Blo 1136633 1710203 := bstep (se 1 (by rfl) ⟨1282652, by rfl⟩ : syracuseStep 1710203 = 2565305) B2565305
theorem B1710329 : Blo 1136633 1710329 := bstep (se 2 (by rfl) ⟨641373, by rfl⟩ : syracuseStep 1710329 = 1282747) B1282747
theorem B3840317 : Blo 1136633 3840317 := bstep (se 3 (by rfl) ⟨720059, by rfl⟩ : syracuseStep 3840317 = 1440119) B1440119
theorem B6494525 : Blo 1136633 6494525 := bstep (se 3 (by rfl) ⟨1217723, by rfl⟩ : syracuseStep 6494525 = 2435447) B2435447
theorem B1710431 : Blo 1136633 1710431 := bstep (se 1 (by rfl) ⟨1282823, by rfl⟩ : syracuseStep 1710431 = 2565647) B2565647
theorem B1710443 : Blo 1136633 1710443 := bstep (se 1 (by rfl) ⟨1282832, by rfl⟩ : syracuseStep 1710443 = 2565665) B2565665
theorem B2562569 : Blo 1136633 2562569 := bstep (se 2 (by rfl) ⟨960963, by rfl⟩ : syracuseStep 2562569 = 1921927) B1921927
theorem B1972775 : Blo 1136633 1972775 := bstep (se 1 (by rfl) ⟨1479581, by rfl⟩ : syracuseStep 1972775 = 2959163) B2959163
theorem B1710671 : Blo 1136633 1710671 := bstep (se 1 (by rfl) ⟨1283003, by rfl⟩ : syracuseStep 1710671 = 2566007) B2566007
theorem B4102753 : Blo 1136633 4102753 := bstep (se 2 (by rfl) ⟨1538532, by rfl⟩ : syracuseStep 4102753 = 3077065) B3077065
theorem B16390835 : Blo 1136633 16390835 := bstep (se 1 (by rfl) ⟨12293126, by rfl⟩ : syracuseStep 16390835 = 24586253) B24586253
theorem B1710791 : Blo 1136633 1710791 := bstep (se 1 (by rfl) ⟨1283093, by rfl⟩ : syracuseStep 1710791 = 2566187) B2566187
theorem B9738953 : Blo 1136633 9738953 := bstep (se 2 (by rfl) ⟨3652107, by rfl⟩ : syracuseStep 9738953 = 7304215) B7304215
theorem B14588747 : Blo 1136633 14588747 := bstep (se 1 (by rfl) ⟨10941560, by rfl⟩ : syracuseStep 14588747 = 21883121) B21883121
theorem B2562911 : Blo 1136633 2562911 := bstep (se 1 (by rfl) ⟨1922183, by rfl⟩ : syracuseStep 2562911 = 3844367) B3844367
theorem B2563091 : Blo 1136633 2563091 := bstep (se 1 (by rfl) ⟨1922318, by rfl⟩ : syracuseStep 2563091 = 3844637) B3844637
theorem B5184665 : Blo 1136633 5184665 := bstep (se 2 (by rfl) ⟨1944249, by rfl⟩ : syracuseStep 5184665 = 3888499) B3888499
theorem B3841181 : Blo 1136633 3841181 := bstep (se 3 (by rfl) ⟨720221, by rfl⟩ : syracuseStep 3841181 = 1440443) B1440443
theorem B12983489 : Blo 1136633 12983489 := bstep (se 2 (by rfl) ⟨4868808, by rfl⟩ : syracuseStep 12983489 = 9737617) B9737617
theorem B2563433 : Blo 1136633 2563433 := bstep (se 2 (by rfl) ⟨961287, by rfl⟩ : syracuseStep 2563433 = 1922575) B1922575
theorem B3841721 : Blo 1136633 3841721 := bstep (se 2 (by rfl) ⟨1440645, by rfl⟩ : syracuseStep 3841721 = 2881291) B2881291
theorem B4857533 : Blo 1136633 4857533 := bstep (se 3 (by rfl) ⟨910787, by rfl⟩ : syracuseStep 4857533 = 1821575) B1821575
theorem B2564027 : Blo 1136633 2564027 := bstep (se 1 (by rfl) ⟨1923020, by rfl⟩ : syracuseStep 2564027 = 3846041) B3846041
theorem B2564153 : Blo 1136633 2564153 := bstep (se 2 (by rfl) ⟨961557, by rfl⟩ : syracuseStep 2564153 = 1923115) B1923115
theorem B3645611 : Blo 1136633 3645611 := bstep (se 1 (by rfl) ⟨2734208, by rfl⟩ : syracuseStep 3645611 = 5468417) B5468417
theorem B73965797 : Blo 1136633 73965797 := bstep (se 4 (by rfl) ⟨6934293, by rfl⟩ : syracuseStep 73965797 = 13868587) B13868587
theorem B3842315 : Blo 1136633 3842315 := bstep (se 1 (by rfl) ⟨2881736, by rfl⟩ : syracuseStep 3842315 = 5763473) B5763473
theorem B4858217 : Blo 1136633 4858217 := bstep (se 2 (by rfl) ⟨1821831, by rfl⟩ : syracuseStep 4858217 = 3643663) B3643663
theorem B2564495 : Blo 1136633 2564495 := bstep (se 1 (by rfl) ⟨1923371, by rfl⟩ : syracuseStep 2564495 = 3846743) B3846743
theorem B3842585 : Blo 1136633 3842585 := bstep (se 2 (by rfl) ⟨1440969, by rfl⟩ : syracuseStep 3842585 = 2881939) B2881939
theorem B2564819 : Blo 1136633 2564819 := bstep (se 1 (by rfl) ⟨1923614, by rfl⟩ : syracuseStep 2564819 = 3847229) B3847229
theorem B10953899 : Blo 1136633 10953899 := bstep (se 1 (by rfl) ⟨8215424, by rfl⟩ : syracuseStep 10953899 = 16430849) B16430849
theorem B8201645 : Blo 1136633 8201645 := bstep (se 3 (by rfl) ⟨1537808, by rfl⟩ : syracuseStep 8201645 = 3075617) B3075617
theorem B8660519 : Blo 1136633 8660519 := bstep (se 1 (by rfl) ⟨6495389, by rfl⟩ : syracuseStep 8660519 = 12990779) B12990779
theorem B2565755 : Blo 1136633 2565755 := bstep (se 1 (by rfl) ⟨1924316, by rfl⟩ : syracuseStep 2565755 = 3848633) B3848633
theorem B3843719 : Blo 1136633 3843719 := bstep (se 1 (by rfl) ⟨2882789, by rfl⟩ : syracuseStep 3843719 = 5765579) B5765579
theorem B3843773 : Blo 1136633 3843773 := bstep (se 3 (by rfl) ⟨720707, by rfl⟩ : syracuseStep 3843773 = 1441415) B1441415
theorem B13838039 : Blo 1136633 13838039 := bstep (se 1 (by rfl) ⟨10378529, by rfl⟩ : syracuseStep 13838039 = 20757059) B20757059
theorem B2565881 : Blo 1136633 2565881 := bstep (se 2 (by rfl) ⟨962205, by rfl⟩ : syracuseStep 2565881 = 1924411) B1924411
theorem B31205209 : Blo 1136633 31205209 := bstep (se 2 (by rfl) ⟨11701953, by rfl⟩ : syracuseStep 31205209 = 23403907) B23403907
theorem B3843935 : Blo 1136633 3843935 := bstep (se 1 (by rfl) ⟨2882951, by rfl⟩ : syracuseStep 3843935 = 5765903) B5765903
theorem B6563693 : Blo 1136633 6563693 := bstep (se 3 (by rfl) ⟨1230692, by rfl⟩ : syracuseStep 6563693 = 2461385) B2461385
theorem B3647393 : Blo 1136633 3647393 := bstep (se 2 (by rfl) ⟨1367772, by rfl⟩ : syracuseStep 3647393 = 2735545) B2735545
theorem B3844097 : Blo 1136633 3844097 := bstep (se 2 (by rfl) ⟨1441536, by rfl⟩ : syracuseStep 3844097 = 2883073) B2883073
theorem B2566151 : Blo 1136633 2566151 := bstep (se 1 (by rfl) ⟨1924613, by rfl⟩ : syracuseStep 2566151 = 3849227) B3849227
theorem B12986405 : Blo 1136633 12986405 := bstep (se 4 (by rfl) ⟨1217475, by rfl⟩ : syracuseStep 12986405 = 2434951) B2434951
theorem B2566223 : Blo 1136633 2566223 := bstep (se 1 (by rfl) ⟨1924667, by rfl⟩ : syracuseStep 2566223 = 3849335) B3849335
theorem B26257715 : Blo 1136633 26257715 := bstep (se 1 (by rfl) ⟨19693286, by rfl⟩ : syracuseStep 26257715 = 39386573) B39386573
theorem B7383737 : Blo 1136633 7383737 := bstep (se 2 (by rfl) ⟨2768901, by rfl⟩ : syracuseStep 7383737 = 5537803) B5537803
theorem B134720293 : Blo 1136633 134720293 := bstep (se 4 (by rfl) ⟨12630027, by rfl⟩ : syracuseStep 134720293 = 25260055) B25260055
theorem B3844907 : Blo 1136633 3844907 := bstep (se 1 (by rfl) ⟨2883680, by rfl⟩ : syracuseStep 3844907 = 5767361) B5767361
theorem B26258455 : Blo 1136633 26258455 := bstep (se 1 (by rfl) ⟨19693841, by rfl⟩ : syracuseStep 26258455 = 39387683) B39387683
theorem B3845177 : Blo 1136633 3845177 := bstep (se 2 (by rfl) ⟨1441941, by rfl⟩ : syracuseStep 3845177 = 2883883) B2883883
theorem B3845501 : Blo 1136633 3845501 := bstep (se 3 (by rfl) ⟨721031, by rfl⟩ : syracuseStep 3845501 = 1442063) B1442063
theorem B3845771 : Blo 1136633 3845771 := bstep (se 1 (by rfl) ⟨2884328, by rfl⟩ : syracuseStep 3845771 = 5768657) B5768657
theorem B3649853 : Blo 1136633 3649853 := bstep (se 3 (by rfl) ⟨684347, by rfl⟩ : syracuseStep 3649853 = 1368695) B1368695
theorem B17740241 : Blo 1136633 17740241 := bstep (se 2 (by rfl) ⟨6652590, by rfl⟩ : syracuseStep 17740241 = 13305181) B13305181
theorem B4108781 : Blo 1136633 4108781 := bstep (se 3 (by rfl) ⟨770396, by rfl⟩ : syracuseStep 4108781 = 1540793) B1540793
theorem B3846689 : Blo 1136633 3846689 := bstep (se 2 (by rfl) ⟨1442508, by rfl⟩ : syracuseStep 3846689 = 2885017) B2885017
theorem B1618471 : Blo 1136633 1618471 := bstep (se 1 (by rfl) ⟨1213853, by rfl⟩ : syracuseStep 1618471 = 2427707) B2427707
theorem B3846905 : Blo 1136633 3846905 := bstep (se 2 (by rfl) ⟨1442589, by rfl⟩ : syracuseStep 3846905 = 2885179) B2885179
theorem B29143961 : Blo 1136633 29143961 := bstep (se 2 (by rfl) ⟨10928985, by rfl⟩ : syracuseStep 29143961 = 21857971) B21857971
theorem B3847175 : Blo 1136633 3847175 := bstep (se 1 (by rfl) ⟨2885381, by rfl⟩ : syracuseStep 3847175 = 5770763) B5770763
theorem B3847283 : Blo 1136633 3847283 := bstep (se 1 (by rfl) ⟨2885462, by rfl⟩ : syracuseStep 3847283 = 5770925) B5770925
theorem B3847553 : Blo 1136633 3847553 := bstep (se 2 (by rfl) ⟨1442832, by rfl⟩ : syracuseStep 3847553 = 2885665) B2885665
theorem B12957245 : Blo 1136633 12957245 := bstep (se 3 (by rfl) ⟨2429483, by rfl⟩ : syracuseStep 12957245 = 4858967) B4858967
theorem B48051893 : Blo 1136633 48051893 := bstep (se 5 (by rfl) ⟨2252432, by rfl⟩ : syracuseStep 48051893 = 4504865) B4504865
theorem B7288861 : Blo 1136633 7288861 := bstep (se 3 (by rfl) ⟨1366661, by rfl⟩ : syracuseStep 7288861 = 2733323) B2733323
theorem B3848363 : Blo 1136633 3848363 := bstep (se 1 (by rfl) ⟨2886272, by rfl⟩ : syracuseStep 3848363 = 5772545) B5772545
theorem B2308513 : Blo 1136633 2308513 := bstep (se 2 (by rfl) ⟨865692, by rfl⟩ : syracuseStep 2308513 = 1731385) B1731385
theorem B2734631 : Blo 1136633 2734631 := bstep (se 1 (by rfl) ⟨2050973, by rfl⟩ : syracuseStep 2734631 = 4101947) B4101947
theorem B3848903 : Blo 1136633 3848903 := bstep (se 1 (by rfl) ⟨2886677, by rfl⟩ : syracuseStep 3848903 = 5773355) B5773355
theorem B2079479 : Blo 1136633 2079479 := bstep (se 1 (by rfl) ⟨1559609, by rfl⟩ : syracuseStep 2079479 = 3119219) B3119219
theorem B9223217 : Blo 1136633 9223217 := bstep (se 2 (by rfl) ⟨3458706, by rfl⟩ : syracuseStep 9223217 = 6917413) B6917413
theorem B31112365 : Blo 1136633 31112365 := bstep (se 3 (by rfl) ⟨5833568, by rfl⟩ : syracuseStep 31112365 = 11667137) B11667137
theorem B8208017 : Blo 1136633 8208017 := bstep (se 2 (by rfl) ⟨3078006, by rfl⟩ : syracuseStep 8208017 = 6156013) B6156013
theorem B12992237 : Blo 1136633 12992237 := bstep (se 3 (by rfl) ⟨2436044, by rfl⟩ : syracuseStep 12992237 = 4872089) B4872089
theorem B8208161 : Blo 1136633 8208161 := bstep (se 2 (by rfl) ⟨3078060, by rfl⟩ : syracuseStep 8208161 = 6156121) B6156121
theorem B2081119 : Blo 1136633 2081119 := bstep (se 1 (by rfl) ⟨1560839, by rfl⟩ : syracuseStep 2081119 = 3121679) B3121679
theorem B3654017 : Blo 1136633 3654017 := bstep (se 2 (by rfl) ⟨1370256, by rfl⟩ : syracuseStep 3654017 = 2740513) B2740513
theorem B9355799 : Blo 1136633 9355799 := bstep (se 1 (by rfl) ⟨7016849, by rfl⟩ : syracuseStep 9355799 = 14033699) B14033699
theorem B9355961 : Blo 1136633 9355961 := bstep (se 2 (by rfl) ⟨3508485, by rfl⟩ : syracuseStep 9355961 = 7016971) B7016971
theorem B32883731 : Blo 1136633 32883731 := bstep (se 1 (by rfl) ⟨24662798, by rfl⟩ : syracuseStep 32883731 = 49325597) B49325597
theorem B1918201 : Blo 1136633 1918201 := bstep (se 2 (by rfl) ⟨719325, by rfl⟩ : syracuseStep 1918201 = 1438651) B1438651
theorem B2049467 : Blo 1136633 2049467 := bstep (se 1 (by rfl) ⟨1537100, by rfl⟩ : syracuseStep 2049467 = 3074201) B3074201
theorem B1918471 : Blo 1136633 1918471 := bstep (se 1 (by rfl) ⟨1438853, by rfl⟩ : syracuseStep 1918471 = 2877707) B2877707
theorem B8210119 : Blo 1136633 8210119 := bstep (se 1 (by rfl) ⟨6157589, by rfl⟩ : syracuseStep 8210119 = 12315179) B12315179
theorem B3458771 : Blo 1136633 3458771 := bstep (se 1 (by rfl) ⟨2594078, by rfl⟩ : syracuseStep 3458771 = 5188157) B5188157
theorem B8636219 : Blo 1136633 8636219 := bstep (se 1 (by rfl) ⟨6477164, by rfl⟩ : syracuseStep 8636219 = 12954329) B12954329
theorem B1918903 : Blo 1136633 1918903 := bstep (se 1 (by rfl) ⟨1439177, by rfl⟩ : syracuseStep 1918903 = 2878355) B2878355
theorem B1820729 : Blo 1136633 1820729 := bstep (se 2 (by rfl) ⟨682773, by rfl⟩ : syracuseStep 1820729 = 1365547) B1365547
theorem B1919099 : Blo 1136633 1919099 := bstep (se 1 (by rfl) ⟨1439324, by rfl⟩ : syracuseStep 1919099 = 2878649) B2878649
theorem B6474113 : Blo 1136633 6474113 := bstep (se 2 (by rfl) ⟨2427792, by rfl⟩ : syracuseStep 6474113 = 4855585) B4855585
theorem B1919497 : Blo 1136633 1919497 := bstep (se 2 (by rfl) ⟨719811, by rfl⟩ : syracuseStep 1919497 = 1439623) B1439623
theorem B6933127 : Blo 1136633 6933127 := bstep (se 1 (by rfl) ⟨5199845, by rfl⟩ : syracuseStep 6933127 = 10399691) B10399691
theorem B1919659 : Blo 1136633 1919659 := bstep (se 1 (by rfl) ⟨1439744, by rfl⟩ : syracuseStep 1919659 = 2879489) B2879489
theorem B1919963 : Blo 1136633 1919963 := bstep (se 1 (by rfl) ⟨1439972, by rfl⟩ : syracuseStep 1919963 = 2879945) B2879945
theorem B1920199 : Blo 1136633 1920199 := bstep (se 1 (by rfl) ⟨1440149, by rfl⟩ : syracuseStep 1920199 = 2880299) B2880299
theorem B1920361 : Blo 1136633 1920361 := bstep (se 2 (by rfl) ⟨720135, by rfl⟩ : syracuseStep 1920361 = 1440271) B1440271
theorem B2739851 : Blo 1136633 2739851 := bstep (se 1 (by rfl) ⟨2054888, by rfl⟩ : syracuseStep 2739851 = 4109777) B4109777
theorem B3460823 : Blo 1136633 3460823 := bstep (se 1 (by rfl) ⟨2595617, by rfl⟩ : syracuseStep 3460823 = 5191235) B5191235
theorem B1920955 : Blo 1136633 1920955 := bstep (se 1 (by rfl) ⟨1440716, by rfl⟩ : syracuseStep 1920955 = 2881433) B2881433
theorem B3559355 : Blo 1136633 3559355 := bstep (se 1 (by rfl) ⟨2669516, by rfl⟩ : syracuseStep 3559355 = 5339033) B5339033
theorem B5754887 : Blo 1136633 5754887 := bstep (se 1 (by rfl) ⟨4316165, by rfl⟩ : syracuseStep 5754887 = 8632331) B8632331
theorem B1921063 : Blo 1136633 1921063 := bstep (se 1 (by rfl) ⟨1440797, by rfl⟩ : syracuseStep 1921063 = 2881595) B2881595
theorem B26300497 : Blo 1136633 26300497 := bstep (se 2 (by rfl) ⟨9862686, by rfl⟩ : syracuseStep 26300497 = 19725373) B19725373
theorem B1921387 : Blo 1136633 1921387 := bstep (se 1 (by rfl) ⟨1441040, by rfl⟩ : syracuseStep 1921387 = 2882081) B2882081
theorem B5755373 : Blo 1136633 5755373 := bstep (se 3 (by rfl) ⟨1079132, by rfl⟩ : syracuseStep 5755373 = 2158265) B2158265
theorem B4739593 : Blo 1136633 4739593 := bstep (se 2 (by rfl) ⟨1777347, by rfl⟩ : syracuseStep 4739593 = 3554695) B3554695
theorem B8213177 : Blo 1136633 8213177 := bstep (se 2 (by rfl) ⟨3079941, by rfl⟩ : syracuseStep 8213177 = 6159883) B6159883
theorem B35050195 : Blo 1136633 35050195 := bstep (se 1 (by rfl) ⟨26287646, by rfl⟩ : syracuseStep 35050195 = 52575293) B52575293
theorem B3691337 : Blo 1136633 3691337 := bstep (se 2 (by rfl) ⟨1384251, by rfl⟩ : syracuseStep 3691337 = 2768503) B2768503
theorem B1823753 : Blo 1136633 1823753 := bstep (se 2 (by rfl) ⟨683907, by rfl⟩ : syracuseStep 1823753 = 1367815) B1367815
theorem B4871339 : Blo 1136633 4871339 := bstep (se 1 (by rfl) ⟨3653504, by rfl⟩ : syracuseStep 4871339 = 7307009) B7307009
theorem B5756183 : Blo 1136633 5756183 := bstep (se 1 (by rfl) ⟨4317137, by rfl⟩ : syracuseStep 5756183 = 8634275) B8634275
theorem B1922447 : Blo 1136633 1922447 := bstep (se 1 (by rfl) ⟨1441835, by rfl⟩ : syracuseStep 1922447 = 2883671) B2883671
theorem B7296551 : Blo 1136633 7296551 := bstep (se 1 (by rfl) ⟨5472413, by rfl⟩ : syracuseStep 7296551 = 10944827) B10944827
theorem B1922683 : Blo 1136633 1922683 := bstep (se 1 (by rfl) ⟨1442012, by rfl⟩ : syracuseStep 1922683 = 2884025) B2884025
theorem B7788383 : Blo 1136633 7788383 := bstep (se 1 (by rfl) ⟨5841287, by rfl⟩ : syracuseStep 7788383 = 11682575) B11682575
theorem B1824619 : Blo 1136633 1824619 := bstep (se 1 (by rfl) ⟨1368464, by rfl⟩ : syracuseStep 1824619 = 2736929) B2736929
theorem B3954539 : Blo 1136633 3954539 := bstep (se 1 (by rfl) ⟨2965904, by rfl⟩ : syracuseStep 3954539 = 5931809) B5931809
theorem B1300399 : Blo 1136633 1300399 := bstep (se 1 (by rfl) ⟨975299, by rfl⟩ : syracuseStep 1300399 = 1950599) B1950599
theorem B7788581 : Blo 1136633 7788581 := bstep (se 4 (by rfl) ⟨730179, by rfl⟩ : syracuseStep 7788581 = 1460359) B1460359
theorem B1136679 : Blo 1136633 1136679 := bstep (se 1 (by rfl) ⟨852509, by rfl⟩ : syracuseStep 1136679 = 1705019) B1705019
theorem B13850681 : Blo 1136633 13850681 := bstep (se 2 (by rfl) ⟨5194005, by rfl⟩ : syracuseStep 13850681 = 10388011) B10388011
theorem B1136719 : Blo 1136633 1136719 := bstep (se 1 (by rfl) ⟨852539, by rfl⟩ : syracuseStep 1136719 = 1705079) B1705079
theorem B8640593 : Blo 1136633 8640593 := bstep (se 2 (by rfl) ⟨3240222, by rfl⟩ : syracuseStep 8640593 = 6480445) B6480445
theorem B1136735 : Blo 1136633 1136735 := bstep (se 1 (by rfl) ⟨852551, by rfl⟩ : syracuseStep 1136735 = 1705103) B1705103
theorem B1136763 : Blo 1136633 1136763 := bstep (se 1 (by rfl) ⟨852572, by rfl⟩ : syracuseStep 1136763 = 1705145) B1705145
theorem B1136815 : Blo 1136633 1136815 := bstep (se 1 (by rfl) ⟨852611, by rfl⟩ : syracuseStep 1136815 = 1705223) B1705223
theorem B1136839 : Blo 1136633 1136839 := bstep (se 1 (by rfl) ⟨852629, by rfl⟩ : syracuseStep 1136839 = 1705259) B1705259
theorem B1136859 : Blo 1136633 1136859 := bstep (se 1 (by rfl) ⟨852644, by rfl⟩ : syracuseStep 1136859 = 1705289) B1705289
theorem B5200139 : Blo 1136633 5200139 := bstep (se 1 (by rfl) ⟨3900104, by rfl⟩ : syracuseStep 5200139 = 7800209) B7800209
theorem B1136935 : Blo 1136633 1136935 := bstep (se 1 (by rfl) ⟨852701, by rfl⟩ : syracuseStep 1136935 = 1705403) B1705403
theorem B1136975 : Blo 1136633 1136975 := bstep (se 1 (by rfl) ⟨852731, by rfl⟩ : syracuseStep 1136975 = 1705463) B1705463
theorem B1136991 : Blo 1136633 1136991 := bstep (se 1 (by rfl) ⟨852743, by rfl⟩ : syracuseStep 1136991 = 1705487) B1705487
theorem B1137019 : Blo 1136633 1137019 := bstep (se 1 (by rfl) ⟨852764, by rfl⟩ : syracuseStep 1137019 = 1705529) B1705529
theorem B1137071 : Blo 1136633 1137071 := bstep (se 1 (by rfl) ⟨852803, by rfl⟩ : syracuseStep 1137071 = 1705607) B1705607
theorem B1137095 : Blo 1136633 1137095 := bstep (se 1 (by rfl) ⟨852821, by rfl⟩ : syracuseStep 1137095 = 1705643) B1705643
theorem B1137115 : Blo 1136633 1137115 := bstep (se 1 (by rfl) ⟨852836, by rfl⟩ : syracuseStep 1137115 = 1705673) B1705673
theorem B1923547 : Blo 1136633 1923547 := bstep (se 1 (by rfl) ⟨1442660, by rfl⟩ : syracuseStep 1923547 = 2885321) B2885321
theorem B1137191 : Blo 1136633 1137191 := bstep (se 1 (by rfl) ⟨852893, by rfl⟩ : syracuseStep 1137191 = 1705787) B1705787
theorem B1825337 : Blo 1136633 1825337 := bstep (se 2 (by rfl) ⟨684501, by rfl⟩ : syracuseStep 1825337 = 1369003) B1369003
theorem B1137231 : Blo 1136633 1137231 := bstep (se 1 (by rfl) ⟨852923, by rfl⟩ : syracuseStep 1137231 = 1705847) B1705847
theorem B1137247 : Blo 1136633 1137247 := bstep (se 1 (by rfl) ⟨852935, by rfl⟩ : syracuseStep 1137247 = 1705871) B1705871
theorem B1137275 : Blo 1136633 1137275 := bstep (se 1 (by rfl) ⟨852956, by rfl⟩ : syracuseStep 1137275 = 1705913) B1705913
theorem B4315787 : Blo 1136633 4315787 := bstep (se 1 (by rfl) ⟨3236840, by rfl⟩ : syracuseStep 4315787 = 6473681) B6473681
theorem B1137327 : Blo 1136633 1137327 := bstep (se 1 (by rfl) ⟨852995, by rfl⟩ : syracuseStep 1137327 = 1705991) B1705991
theorem B1137351 : Blo 1136633 1137351 := bstep (se 1 (by rfl) ⟨853013, by rfl⟩ : syracuseStep 1137351 = 1706027) B1706027
theorem B1137371 : Blo 1136633 1137371 := bstep (se 1 (by rfl) ⟨853028, by rfl⟩ : syracuseStep 1137371 = 1706057) B1706057
theorem B1137447 : Blo 1136633 1137447 := bstep (se 1 (by rfl) ⟨853085, by rfl⟩ : syracuseStep 1137447 = 1706171) B1706171
theorem B1137487 : Blo 1136633 1137487 := bstep (se 1 (by rfl) ⟨853115, by rfl⟩ : syracuseStep 1137487 = 1706231) B1706231
theorem B1137503 : Blo 1136633 1137503 := bstep (se 1 (by rfl) ⟨853127, by rfl⟩ : syracuseStep 1137503 = 1706255) B1706255
theorem B5757803 : Blo 1136633 5757803 := bstep (se 1 (by rfl) ⟨4318352, by rfl⟩ : syracuseStep 5757803 = 8636705) B8636705
theorem B1137531 : Blo 1136633 1137531 := bstep (se 1 (by rfl) ⟨853148, by rfl⟩ : syracuseStep 1137531 = 1706297) B1706297
theorem B7297937 : Blo 1136633 7297937 := bstep (se 2 (by rfl) ⟨2736726, by rfl⟩ : syracuseStep 7297937 = 5473453) B5473453
theorem B1137583 : Blo 1136633 1137583 := bstep (se 1 (by rfl) ⟨853187, by rfl⟩ : syracuseStep 1137583 = 1706375) B1706375
theorem B1137607 : Blo 1136633 1137607 := bstep (se 1 (by rfl) ⟨853205, by rfl⟩ : syracuseStep 1137607 = 1706411) B1706411
theorem B1137627 : Blo 1136633 1137627 := bstep (se 1 (by rfl) ⟨853220, by rfl⟩ : syracuseStep 1137627 = 1706441) B1706441
theorem B1137703 : Blo 1136633 1137703 := bstep (se 1 (by rfl) ⟨853277, by rfl⟩ : syracuseStep 1137703 = 1706555) B1706555
theorem B1825849 : Blo 1136633 1825849 := bstep (se 2 (by rfl) ⟨684693, by rfl⟩ : syracuseStep 1825849 = 1369387) B1369387
theorem B1137743 : Blo 1136633 1137743 := bstep (se 1 (by rfl) ⟨853307, by rfl⟩ : syracuseStep 1137743 = 1706615) B1706615
theorem B1924175 : Blo 1136633 1924175 := bstep (se 1 (by rfl) ⟨1443131, by rfl⟩ : syracuseStep 1924175 = 2886263) B2886263
theorem B1137759 : Blo 1136633 1137759 := bstep (se 1 (by rfl) ⟨853319, by rfl⟩ : syracuseStep 1137759 = 1706639) B1706639
theorem B1137787 : Blo 1136633 1137787 := bstep (se 1 (by rfl) ⟨853340, by rfl⟩ : syracuseStep 1137787 = 1706681) B1706681
theorem B78830765 : Blo 1136633 78830765 := bstep (se 3 (by rfl) ⟨14780768, by rfl⟩ : syracuseStep 78830765 = 29561537) B29561537
theorem B1137839 : Blo 1136633 1137839 := bstep (se 1 (by rfl) ⟨853379, by rfl⟩ : syracuseStep 1137839 = 1706759) B1706759
theorem B1137863 : Blo 1136633 1137863 := bstep (se 1 (by rfl) ⟨853397, by rfl⟩ : syracuseStep 1137863 = 1706795) B1706795
theorem B1137883 : Blo 1136633 1137883 := bstep (se 1 (by rfl) ⟨853412, by rfl⟩ : syracuseStep 1137883 = 1706825) B1706825
theorem B1137959 : Blo 1136633 1137959 := bstep (se 1 (by rfl) ⟨853469, by rfl⟩ : syracuseStep 1137959 = 1706939) B1706939
theorem B1137999 : Blo 1136633 1137999 := bstep (se 1 (by rfl) ⟨853499, by rfl⟩ : syracuseStep 1137999 = 1706999) B1706999
theorem B1138015 : Blo 1136633 1138015 := bstep (se 1 (by rfl) ⟨853511, by rfl⟩ : syracuseStep 1138015 = 1707023) B1707023
theorem B1138043 : Blo 1136633 1138043 := bstep (se 1 (by rfl) ⟨853532, by rfl⟩ : syracuseStep 1138043 = 1707065) B1707065
theorem B1138095 : Blo 1136633 1138095 := bstep (se 1 (by rfl) ⟨853571, by rfl⟩ : syracuseStep 1138095 = 1707143) B1707143
theorem B1367479 : Blo 1136633 1367479 := bstep (se 1 (by rfl) ⟨1025609, by rfl⟩ : syracuseStep 1367479 = 2051219) B2051219
theorem B1138119 : Blo 1136633 1138119 := bstep (se 1 (by rfl) ⟨853589, by rfl⟩ : syracuseStep 1138119 = 1707179) B1707179
theorem B1138139 : Blo 1136633 1138139 := bstep (se 1 (by rfl) ⟨853604, by rfl⟩ : syracuseStep 1138139 = 1707209) B1707209
theorem B5758451 : Blo 1136633 5758451 := bstep (se 1 (by rfl) ⟨4318838, by rfl⟩ : syracuseStep 5758451 = 8637677) B8637677
theorem B1138215 : Blo 1136633 1138215 := bstep (se 1 (by rfl) ⟨853661, by rfl⟩ : syracuseStep 1138215 = 1707323) B1707323
theorem B1138255 : Blo 1136633 1138255 := bstep (se 1 (by rfl) ⟨853691, by rfl⟩ : syracuseStep 1138255 = 1707383) B1707383
theorem B1138271 : Blo 1136633 1138271 := bstep (se 1 (by rfl) ⟨853703, by rfl⟩ : syracuseStep 1138271 = 1707407) B1707407
theorem B1138299 : Blo 1136633 1138299 := bstep (se 1 (by rfl) ⟨853724, by rfl⟩ : syracuseStep 1138299 = 1707449) B1707449
theorem B1138351 : Blo 1136633 1138351 := bstep (se 1 (by rfl) ⟨853763, by rfl⟩ : syracuseStep 1138351 = 1707527) B1707527
theorem B1138375 : Blo 1136633 1138375 := bstep (se 1 (by rfl) ⟨853781, by rfl⟩ : syracuseStep 1138375 = 1707563) B1707563
theorem B1138395 : Blo 1136633 1138395 := bstep (se 1 (by rfl) ⟨853796, by rfl⟩ : syracuseStep 1138395 = 1707593) B1707593
theorem B1138471 : Blo 1136633 1138471 := bstep (se 1 (by rfl) ⟨853853, by rfl⟩ : syracuseStep 1138471 = 1707707) B1707707
theorem B1138511 : Blo 1136633 1138511 := bstep (se 1 (by rfl) ⟨853883, by rfl⟩ : syracuseStep 1138511 = 1707767) B1707767
theorem B1138527 : Blo 1136633 1138527 := bstep (se 1 (by rfl) ⟨853895, by rfl⟩ : syracuseStep 1138527 = 1707791) B1707791
theorem B4317047 : Blo 1136633 4317047 := bstep (se 1 (by rfl) ⟨3237785, by rfl⟩ : syracuseStep 4317047 = 6475571) B6475571
theorem B1138555 : Blo 1136633 1138555 := bstep (se 1 (by rfl) ⟨853916, by rfl⟩ : syracuseStep 1138555 = 1707833) B1707833
theorem B1138607 : Blo 1136633 1138607 := bstep (se 1 (by rfl) ⟨853955, by rfl⟩ : syracuseStep 1138607 = 1707911) B1707911
theorem B1138631 : Blo 1136633 1138631 := bstep (se 1 (by rfl) ⟨853973, by rfl⟩ : syracuseStep 1138631 = 1707947) B1707947
theorem B1138651 : Blo 1136633 1138651 := bstep (se 1 (by rfl) ⟨853988, by rfl⟩ : syracuseStep 1138651 = 1707977) B1707977
theorem B1138727 : Blo 1136633 1138727 := bstep (se 1 (by rfl) ⟨854045, by rfl⟩ : syracuseStep 1138727 = 1708091) B1708091
theorem B1138767 : Blo 1136633 1138767 := bstep (se 1 (by rfl) ⟨854075, by rfl⟩ : syracuseStep 1138767 = 1708151) B1708151
theorem B1138783 : Blo 1136633 1138783 := bstep (se 1 (by rfl) ⟨854087, by rfl⟩ : syracuseStep 1138783 = 1708175) B1708175
theorem B1138811 : Blo 1136633 1138811 := bstep (se 1 (by rfl) ⟨854108, by rfl⟩ : syracuseStep 1138811 = 1708217) B1708217
theorem B1138863 : Blo 1136633 1138863 := bstep (se 1 (by rfl) ⟨854147, by rfl⟩ : syracuseStep 1138863 = 1708295) B1708295
theorem B1138887 : Blo 1136633 1138887 := bstep (se 1 (by rfl) ⟨854165, by rfl⟩ : syracuseStep 1138887 = 1708331) B1708331
theorem B1138907 : Blo 1136633 1138907 := bstep (se 1 (by rfl) ⟨854180, by rfl⟩ : syracuseStep 1138907 = 1708361) B1708361
theorem B1138983 : Blo 1136633 1138983 := bstep (se 1 (by rfl) ⟨854237, by rfl⟩ : syracuseStep 1138983 = 1708475) B1708475
theorem B1139023 : Blo 1136633 1139023 := bstep (se 1 (by rfl) ⟨854267, by rfl⟩ : syracuseStep 1139023 = 1708535) B1708535
theorem B1139039 : Blo 1136633 1139039 := bstep (se 1 (by rfl) ⟨854279, by rfl⟩ : syracuseStep 1139039 = 1708559) B1708559
theorem B1139067 : Blo 1136633 1139067 := bstep (se 1 (by rfl) ⟨854300, by rfl⟩ : syracuseStep 1139067 = 1708601) B1708601
theorem B1139119 : Blo 1136633 1139119 := bstep (se 1 (by rfl) ⟨854339, by rfl⟩ : syracuseStep 1139119 = 1708679) B1708679
theorem B1139143 : Blo 1136633 1139143 := bstep (se 1 (by rfl) ⟨854357, by rfl⟩ : syracuseStep 1139143 = 1708715) B1708715
theorem B1139163 : Blo 1136633 1139163 := bstep (se 1 (by rfl) ⟨854372, by rfl⟩ : syracuseStep 1139163 = 1708745) B1708745
theorem B1139239 : Blo 1136633 1139239 := bstep (se 1 (by rfl) ⟨854429, by rfl⟩ : syracuseStep 1139239 = 1708859) B1708859
theorem B1139279 : Blo 1136633 1139279 := bstep (se 1 (by rfl) ⟨854459, by rfl⟩ : syracuseStep 1139279 = 1708919) B1708919
theorem B1139295 : Blo 1136633 1139295 := bstep (se 1 (by rfl) ⟨854471, by rfl⟩ : syracuseStep 1139295 = 1708943) B1708943
theorem B1139323 : Blo 1136633 1139323 := bstep (se 1 (by rfl) ⟨854492, by rfl⟩ : syracuseStep 1139323 = 1708985) B1708985
theorem B1139375 : Blo 1136633 1139375 := bstep (se 1 (by rfl) ⟨854531, by rfl⟩ : syracuseStep 1139375 = 1709063) B1709063
theorem B1139399 : Blo 1136633 1139399 := bstep (se 1 (by rfl) ⟨854549, by rfl⟩ : syracuseStep 1139399 = 1709099) B1709099
theorem B1139419 : Blo 1136633 1139419 := bstep (se 1 (by rfl) ⟨854564, by rfl⟩ : syracuseStep 1139419 = 1709129) B1709129
theorem B5759747 : Blo 1136633 5759747 := bstep (se 1 (by rfl) ⟨4319810, by rfl⟩ : syracuseStep 5759747 = 8639621) B8639621
theorem B1139495 : Blo 1136633 1139495 := bstep (se 1 (by rfl) ⟨854621, by rfl⟩ : syracuseStep 1139495 = 1709243) B1709243
theorem B4318019 : Blo 1136633 4318019 := bstep (se 1 (by rfl) ⟨3238514, by rfl⟩ : syracuseStep 4318019 = 6477029) B6477029
theorem B1139535 : Blo 1136633 1139535 := bstep (se 1 (by rfl) ⟨854651, by rfl⟩ : syracuseStep 1139535 = 1709303) B1709303
theorem B1139551 : Blo 1136633 1139551 := bstep (se 1 (by rfl) ⟨854663, by rfl⟩ : syracuseStep 1139551 = 1709327) B1709327
theorem B1139579 : Blo 1136633 1139579 := bstep (se 1 (by rfl) ⟨854684, by rfl⟩ : syracuseStep 1139579 = 1709369) B1709369
theorem B1139631 : Blo 1136633 1139631 := bstep (se 1 (by rfl) ⟨854723, by rfl⟩ : syracuseStep 1139631 = 1709447) B1709447
theorem B1139655 : Blo 1136633 1139655 := bstep (se 1 (by rfl) ⟨854741, by rfl⟩ : syracuseStep 1139655 = 1709483) B1709483
theorem B1139675 : Blo 1136633 1139675 := bstep (se 1 (by rfl) ⟨854756, by rfl⟩ : syracuseStep 1139675 = 1709513) B1709513
theorem B3073043 : Blo 1136633 3073043 := bstep (se 1 (by rfl) ⟨2304782, by rfl⟩ : syracuseStep 3073043 = 4609565) B4609565
theorem B7300115 : Blo 1136633 7300115 := bstep (se 1 (by rfl) ⟨5475086, by rfl⟩ : syracuseStep 7300115 = 10950173) B10950173
theorem B1139751 : Blo 1136633 1139751 := bstep (se 1 (by rfl) ⟨854813, by rfl⟩ : syracuseStep 1139751 = 1709627) B1709627
theorem B1139791 : Blo 1136633 1139791 := bstep (se 1 (by rfl) ⟨854843, by rfl⟩ : syracuseStep 1139791 = 1709687) B1709687
theorem B1139807 : Blo 1136633 1139807 := bstep (se 1 (by rfl) ⟨854855, by rfl⟩ : syracuseStep 1139807 = 1709711) B1709711
theorem B1139835 : Blo 1136633 1139835 := bstep (se 1 (by rfl) ⟨854876, by rfl⟩ : syracuseStep 1139835 = 1709753) B1709753
theorem B7398553 : Blo 1136633 7398553 := bstep (se 2 (by rfl) ⟨2774457, by rfl⟩ : syracuseStep 7398553 = 5548915) B5548915
theorem B1139887 : Blo 1136633 1139887 := bstep (se 1 (by rfl) ⟨854915, by rfl⟩ : syracuseStep 1139887 = 1709831) B1709831
theorem B1139911 : Blo 1136633 1139911 := bstep (se 1 (by rfl) ⟨854933, by rfl⟩ : syracuseStep 1139911 = 1709867) B1709867
theorem B1139931 : Blo 1136633 1139931 := bstep (se 1 (by rfl) ⟨854948, by rfl⟩ : syracuseStep 1139931 = 1709897) B1709897
theorem B7300343 : Blo 1136633 7300343 := bstep (se 1 (by rfl) ⟨5475257, by rfl⟩ : syracuseStep 7300343 = 10950515) B10950515
theorem B1140007 : Blo 1136633 1140007 := bstep (se 1 (by rfl) ⟨855005, by rfl⟩ : syracuseStep 1140007 = 1710011) B1710011
theorem B1140047 : Blo 1136633 1140047 := bstep (se 1 (by rfl) ⟨855035, by rfl⟩ : syracuseStep 1140047 = 1710071) B1710071
theorem B1140063 : Blo 1136633 1140063 := bstep (se 1 (by rfl) ⟨855047, by rfl⟩ : syracuseStep 1140063 = 1710095) B1710095
theorem B1140091 : Blo 1136633 1140091 := bstep (se 1 (by rfl) ⟨855068, by rfl⟩ : syracuseStep 1140091 = 1710137) B1710137
theorem B1140143 : Blo 1136633 1140143 := bstep (se 1 (by rfl) ⟨855107, by rfl⟩ : syracuseStep 1140143 = 1710215) B1710215
theorem B1140167 : Blo 1136633 1140167 := bstep (se 1 (by rfl) ⟨855125, by rfl⟩ : syracuseStep 1140167 = 1710251) B1710251
theorem B1140187 : Blo 1136633 1140187 := bstep (se 1 (by rfl) ⟨855140, by rfl⟩ : syracuseStep 1140187 = 1710281) B1710281
theorem B1140263 : Blo 1136633 1140263 := bstep (se 1 (by rfl) ⟨855197, by rfl⟩ : syracuseStep 1140263 = 1710395) B1710395
theorem B1140303 : Blo 1136633 1140303 := bstep (se 1 (by rfl) ⟨855227, by rfl⟩ : syracuseStep 1140303 = 1710455) B1710455
theorem B1140319 : Blo 1136633 1140319 := bstep (se 1 (by rfl) ⟨855239, by rfl⟩ : syracuseStep 1140319 = 1710479) B1710479
theorem B5465723 : Blo 1136633 5465723 := bstep (se 1 (by rfl) ⟨4099292, by rfl⟩ : syracuseStep 5465723 = 8198585) B8198585
theorem B1140347 : Blo 1136633 1140347 := bstep (se 1 (by rfl) ⟨855260, by rfl⟩ : syracuseStep 1140347 = 1710521) B1710521
theorem B1140399 : Blo 1136633 1140399 := bstep (se 1 (by rfl) ⟨855299, by rfl⟩ : syracuseStep 1140399 = 1710599) B1710599
theorem B3073735 : Blo 1136633 3073735 := bstep (se 1 (by rfl) ⟨2305301, by rfl⟩ : syracuseStep 3073735 = 4610603) B4610603
theorem B1140423 : Blo 1136633 1140423 := bstep (se 1 (by rfl) ⟨855317, by rfl⟩ : syracuseStep 1140423 = 1710635) B1710635
theorem B1140443 : Blo 1136633 1140443 := bstep (se 1 (by rfl) ⟨855332, by rfl⟩ : syracuseStep 1140443 = 1710665) B1710665
theorem B1140519 : Blo 1136633 1140519 := bstep (se 1 (by rfl) ⟨855389, by rfl⟩ : syracuseStep 1140519 = 1710779) B1710779
theorem B78866227 : Blo 1136633 78866227 := bstep (se 1 (by rfl) ⟨59149670, by rfl⟩ : syracuseStep 78866227 = 118299341) B118299341
theorem B1140559 : Blo 1136633 1140559 := bstep (se 1 (by rfl) ⟨855419, by rfl⟩ : syracuseStep 1140559 = 1710839) B1710839
theorem B1140575 : Blo 1136633 1140575 := bstep (se 1 (by rfl) ⟨855431, by rfl⟩ : syracuseStep 1140575 = 1710863) B1710863
theorem B1140603 : Blo 1136633 1140603 := bstep (se 1 (by rfl) ⟨855452, by rfl⟩ : syracuseStep 1140603 = 1710905) B1710905
theorem B3794951 : Blo 1136633 3794951 := bstep (se 1 (by rfl) ⟨2846213, by rfl⟩ : syracuseStep 3794951 = 5692427) B5692427
theorem B5761367 : Blo 1136633 5761367 := bstep (se 1 (by rfl) ⟨4321025, by rfl⟩ : syracuseStep 5761367 = 8642051) B8642051
theorem B2877839 : Blo 1136633 2877839 := bstep (se 1 (by rfl) ⟨2158379, by rfl⟩ : syracuseStep 2877839 = 4316759) B4316759
theorem B4319689 : Blo 1136633 4319689 := bstep (se 2 (by rfl) ⟨1619883, by rfl⟩ : syracuseStep 4319689 = 3239767) B3239767
theorem B10938827 : Blo 1136633 10938827 := bstep (se 1 (by rfl) ⟨8204120, by rfl⟩ : syracuseStep 10938827 = 16408241) B16408241
theorem B2878163 : Blo 1136633 2878163 := bstep (se 1 (by rfl) ⟨2158622, by rfl⟩ : syracuseStep 2878163 = 4317245) B4317245
theorem B4319993 : Blo 1136633 4319993 := bstep (se 2 (by rfl) ⟨1619997, by rfl⟩ : syracuseStep 4319993 = 3239995) B3239995
theorem B20769605 : Blo 1136633 20769605 := bstep (se 4 (by rfl) ⟨1947150, by rfl⟩ : syracuseStep 20769605 = 3894301) B3894301
theorem B3697481 : Blo 1136633 3697481 := bstep (se 2 (by rfl) ⟨1386555, by rfl⟩ : syracuseStep 3697481 = 2773111) B2773111
theorem B8645453 : Blo 1136633 8645453 := bstep (se 3 (by rfl) ⟨1621022, by rfl⟩ : syracuseStep 8645453 = 3242045) B3242045
theorem B4320161 : Blo 1136633 4320161 := bstep (se 2 (by rfl) ⟨1620060, by rfl⟩ : syracuseStep 4320161 = 3240121) B3240121
theorem B4320175 : Blo 1136633 4320175 := bstep (se 1 (by rfl) ⟨3240131, by rfl⟩ : syracuseStep 4320175 = 6480263) B6480263
theorem B2157931 : Blo 1136633 2157931 := bstep (se 1 (by rfl) ⟨1618448, by rfl⟩ : syracuseStep 2157931 = 3236897) B3236897
theorem B2158159 : Blo 1136633 2158159 := bstep (se 1 (by rfl) ⟨1618619, by rfl⟩ : syracuseStep 2158159 = 3237239) B3237239
theorem B2879327 : Blo 1136633 2879327 := bstep (se 1 (by rfl) ⟨2159495, by rfl⟩ : syracuseStep 2879327 = 4318991) B4318991
theorem B4321133 : Blo 1136633 4321133 := bstep (se 3 (by rfl) ⟨810212, by rfl⟩ : syracuseStep 4321133 = 1620425) B1620425
theorem B4681729 : Blo 1136633 4681729 := bstep (se 2 (by rfl) ⟨1755648, by rfl⟩ : syracuseStep 4681729 = 3511297) B3511297
theorem B7794845 : Blo 1136633 7794845 := bstep (se 3 (by rfl) ⟨1461533, by rfl⟩ : syracuseStep 7794845 = 2923067) B2923067
theorem B4321451 : Blo 1136633 4321451 := bstep (se 1 (by rfl) ⟨3241088, by rfl⟩ : syracuseStep 4321451 = 6482177) B6482177
theorem B3076633 : Blo 1136633 3076633 := bstep (se 2 (by rfl) ⟨1153737, by rfl⟩ : syracuseStep 3076633 = 2307475) B2307475
theorem B3240587 : Blo 1136633 3240587 := bstep (se 1 (by rfl) ⟨2430440, by rfl⟩ : syracuseStep 3240587 = 4860881) B4860881
theorem B2880431 : Blo 1136633 2880431 := bstep (se 1 (by rfl) ⟨2160323, by rfl⟩ : syracuseStep 2880431 = 4320647) B4320647
theorem B1733671 : Blo 1136633 1733671 := bstep (se 1 (by rfl) ⟨1300253, by rfl⟩ : syracuseStep 1733671 = 2600507) B2600507
theorem B9729143 : Blo 1136633 9729143 := bstep (se 1 (by rfl) ⟨7296857, by rfl⟩ : syracuseStep 9729143 = 14593715) B14593715
theorem B8647883 : Blo 1136633 8647883 := bstep (se 1 (by rfl) ⟨6485912, by rfl⟩ : syracuseStep 8647883 = 12971825) B12971825
theorem B4617577 : Blo 1136633 4617577 := bstep (se 2 (by rfl) ⟨1731591, by rfl⟩ : syracuseStep 4617577 = 3463183) B3463183
theorem B3077519 : Blo 1136633 3077519 := bstep (se 1 (by rfl) ⟨2308139, by rfl⟩ : syracuseStep 3077519 = 4616279) B4616279
theorem B3077671 : Blo 1136633 3077671 := bstep (se 1 (by rfl) ⟨2308253, by rfl⟩ : syracuseStep 3077671 = 4616507) B4616507
theorem B41514677 : Blo 1136633 41514677 := bstep (se 5 (by rfl) ⟨1946000, by rfl⟩ : syracuseStep 41514677 = 3892001) B3892001
theorem B4683473 : Blo 1136633 4683473 := bstep (se 2 (by rfl) ⟨1756302, by rfl⟩ : syracuseStep 4683473 = 3512605) B3512605
theorem B112326371 : Blo 1136633 112326371 := bstep (se 1 (by rfl) ⟨84244778, by rfl⟩ : syracuseStep 112326371 = 168489557) B168489557
theorem B5764931 : Blo 1136633 5764931 := bstep (se 1 (by rfl) ⟨4323698, by rfl⟩ : syracuseStep 5764931 = 8647397) B8647397
theorem B2193247 : Blo 1136633 2193247 := bstep (se 1 (by rfl) ⟨1644935, by rfl⟩ : syracuseStep 2193247 = 3289871) B3289871
theorem B2881615 : Blo 1136633 2881615 := bstep (se 1 (by rfl) ⟨2161211, by rfl⟩ : syracuseStep 2881615 = 4322423) B4322423
theorem B9730205 : Blo 1136633 9730205 := bstep (se 3 (by rfl) ⟨1824413, by rfl⟩ : syracuseStep 9730205 = 3648827) B3648827
theorem B4618583 : Blo 1136633 4618583 := bstep (se 1 (by rfl) ⟨3463937, by rfl⟩ : syracuseStep 4618583 = 6927875) B6927875
theorem B1440175 : Blo 1136633 1440175 := bstep (se 1 (by rfl) ⟨1080131, by rfl⟩ : syracuseStep 1440175 = 2160263) B2160263
theorem B4324049 : Blo 1136633 4324049 := bstep (se 2 (by rfl) ⟨1621518, by rfl⟩ : syracuseStep 4324049 = 3243037) B3243037
theorem B2882263 : Blo 1136633 2882263 := bstep (se 1 (by rfl) ⟨2161697, by rfl⟩ : syracuseStep 2882263 = 4323395) B4323395
theorem B2882567 : Blo 1136633 2882567 := bstep (se 1 (by rfl) ⟨2161925, by rfl⟩ : syracuseStep 2882567 = 4323851) B4323851
theorem B4324367 : Blo 1136633 4324367 := bstep (se 1 (by rfl) ⟨3243275, by rfl⟩ : syracuseStep 4324367 = 6486551) B6486551
theorem B2161721 : Blo 1136633 2161721 := bstep (se 2 (by rfl) ⟨810645, by rfl⟩ : syracuseStep 2161721 = 1621291) B1621291
theorem B14777423 : Blo 1136633 14777423 := bstep (se 1 (by rfl) ⟨11083067, by rfl⟩ : syracuseStep 14777423 = 22166135) B22166135
theorem B6487235 : Blo 1136633 6487235 := bstep (se 1 (by rfl) ⟨4865426, by rfl⟩ : syracuseStep 6487235 = 9730853) B9730853
theorem B1441243 : Blo 1136633 1441243 := bstep (se 1 (by rfl) ⟨1080932, by rfl⟩ : syracuseStep 1441243 = 2161865) B2161865
theorem B6159995 : Blo 1136633 6159995 := bstep (se 1 (by rfl) ⟨4619996, by rfl⟩ : syracuseStep 6159995 = 9239993) B9239993
theorem B14581619 : Blo 1136633 14581619 := bstep (se 1 (by rfl) ⟨10936214, by rfl⟩ : syracuseStep 14581619 = 21872429) B21872429
theorem B3243959 : Blo 1136633 3243959 := bstep (se 1 (by rfl) ⟨2432969, by rfl⟩ : syracuseStep 3243959 = 4865939) B4865939
theorem B24969221 : Blo 1136633 24969221 := bstep (se 4 (by rfl) ⟨2340864, by rfl⟩ : syracuseStep 24969221 = 4681729) B4681729
theorem B1442215 : Blo 1136633 1442215 := bstep (se 1 (by rfl) ⟨1081661, by rfl⟩ : syracuseStep 1442215 = 2163323) B2163323
theorem B21922487 : Blo 1136633 21922487 := bstep (se 1 (by rfl) ⟨16441865, by rfl⟩ : syracuseStep 21922487 = 32883731) B32883731
theorem B2884319 : Blo 1136633 2884319 := bstep (se 1 (by rfl) ⟨2163239, by rfl⟩ : syracuseStep 2884319 = 4326479) B4326479
theorem B1442539 : Blo 1136633 1442539 := bstep (se 1 (by rfl) ⟨1081904, by rfl⟩ : syracuseStep 1442539 = 2163809) B2163809
theorem B2163611 : Blo 1136633 2163611 := bstep (se 1 (by rfl) ⟨1622708, by rfl⟩ : syracuseStep 2163611 = 3245417) B3245417
theorem B3081131 : Blo 1136633 3081131 := bstep (se 1 (by rfl) ⟨2310848, by rfl⟩ : syracuseStep 3081131 = 4621697) B4621697
theorem B1442767 : Blo 1136633 1442767 := bstep (se 1 (by rfl) ⟨1082075, by rfl⟩ : syracuseStep 1442767 = 2164151) B2164151
theorem B1443035 : Blo 1136633 1443035 := bstep (se 1 (by rfl) ⟨1082276, by rfl⟩ : syracuseStep 1443035 = 2164553) B2164553
theorem B1705193 : Blo 1136633 1705193 := bstep (se 2 (by rfl) ⟨639447, by rfl⟩ : syracuseStep 1705193 = 1278895) B1278895
theorem B1705247 : Blo 1136633 1705247 := bstep (se 1 (by rfl) ⟨1278935, by rfl⟩ : syracuseStep 1705247 = 2557871) B2557871
theorem B32867693 : Blo 1136633 32867693 := bstep (se 3 (by rfl) ⟨6162692, by rfl⟩ : syracuseStep 32867693 = 12325385) B12325385
theorem B6489467 : Blo 1136633 6489467 := bstep (se 1 (by rfl) ⟨4867100, by rfl⟩ : syracuseStep 6489467 = 9734201) B9734201
theorem B1279399 : Blo 1136633 1279399 := bstep (se 1 (by rfl) ⟨959549, by rfl⟩ : syracuseStep 1279399 = 1919099) B1919099
theorem B1705415 : Blo 1136633 1705415 := bstep (se 1 (by rfl) ⟨1279061, by rfl⟩ : syracuseStep 1705415 = 2558123) B2558123
theorem B9864737 : Blo 1136633 9864737 := bstep (se 2 (by rfl) ⟨3699276, by rfl⟩ : syracuseStep 9864737 = 7398553) B7398553
theorem B2557601 : Blo 1136633 2557601 := bstep (se 2 (by rfl) ⟨959100, by rfl⟩ : syracuseStep 2557601 = 1918201) B1918201
theorem B1443511 : Blo 1136633 1443511 := bstep (se 1 (by rfl) ⟨1082633, by rfl⟩ : syracuseStep 1443511 = 2165267) B2165267
theorem B1705769 : Blo 1136633 1705769 := bstep (se 2 (by rfl) ⟨639663, by rfl⟩ : syracuseStep 1705769 = 1279327) B1279327
theorem B1705775 : Blo 1136633 1705775 := bstep (se 1 (by rfl) ⟨1279331, by rfl⟩ : syracuseStep 1705775 = 2558663) B2558663
theorem B5769143 : Blo 1136633 5769143 := bstep (se 1 (by rfl) ⟨4326857, by rfl⟩ : syracuseStep 5769143 = 8653715) B8653715
theorem B1279975 : Blo 1136633 1279975 := bstep (se 1 (by rfl) ⟨959981, by rfl⟩ : syracuseStep 1279975 = 1919963) B1919963
theorem B2557961 : Blo 1136633 2557961 := bstep (se 2 (by rfl) ⟨959235, by rfl⟩ : syracuseStep 2557961 = 1918471) B1918471
theorem B4098313 : Blo 1136633 4098313 := bstep (se 2 (by rfl) ⟨1536867, by rfl⟩ : syracuseStep 4098313 = 3073735) B3073735
theorem B1706249 : Blo 1136633 1706249 := bstep (se 2 (by rfl) ⟨639843, by rfl⟩ : syracuseStep 1706249 = 1279687) B1279687
theorem B10946825 : Blo 1136633 10946825 := bstep (se 2 (by rfl) ⟨4105059, by rfl⟩ : syracuseStep 10946825 = 8210119) B8210119
theorem B1706351 : Blo 1136633 1706351 := bstep (se 1 (by rfl) ⟨1279763, by rfl⟩ : syracuseStep 1706351 = 2559527) B2559527
theorem B105154969 : Blo 1136633 105154969 := bstep (se 2 (by rfl) ⟨39433113, by rfl⟩ : syracuseStep 105154969 = 78866227) B78866227
theorem B2558375 : Blo 1136633 2558375 := bstep (se 1 (by rfl) ⟨1918781, by rfl⟩ : syracuseStep 2558375 = 3837563) B3837563
theorem B8653229 : Blo 1136633 8653229 := bstep (se 3 (by rfl) ⟨1622480, by rfl⟩ : syracuseStep 8653229 = 3244961) B3244961
theorem B2558483 : Blo 1136633 2558483 := bstep (se 1 (by rfl) ⟨1918862, by rfl⟩ : syracuseStep 2558483 = 3837725) B3837725
theorem B5769791 : Blo 1136633 5769791 := bstep (se 1 (by rfl) ⟨4327343, by rfl⟩ : syracuseStep 5769791 = 8654687) B8654687
theorem B1706567 : Blo 1136633 1706567 := bstep (se 1 (by rfl) ⟨1279925, by rfl⟩ : syracuseStep 1706567 = 2559851) B2559851
theorem B2558537 : Blo 1136633 2558537 := bstep (se 2 (by rfl) ⟨959451, by rfl⟩ : syracuseStep 2558537 = 1918903) B1918903
theorem B24644195 : Blo 1136633 24644195 := bstep (se 1 (by rfl) ⟨18483146, by rfl⟩ : syracuseStep 24644195 = 36966293) B36966293
theorem B1706603 : Blo 1136633 1706603 := bstep (se 1 (by rfl) ⟨1279952, by rfl⟩ : syracuseStep 1706603 = 2559905) B2559905
theorem B2427563 : Blo 1136633 2427563 := bstep (se 1 (by rfl) ⟨1820672, by rfl⟩ : syracuseStep 2427563 = 3641345) B3641345
theorem B3836591 : Blo 1136633 3836591 := bstep (se 1 (by rfl) ⟨2877443, by rfl⟩ : syracuseStep 3836591 = 5754887) B5754887
theorem B1706831 : Blo 1136633 1706831 := bstep (se 1 (by rfl) ⟨1280123, by rfl⟩ : syracuseStep 1706831 = 2560247) B2560247
theorem B20810621 : Blo 1136633 20810621 := bstep (se 3 (by rfl) ⟨3901991, by rfl⟩ : syracuseStep 20810621 = 7803983) B7803983
theorem B6163343 : Blo 1136633 6163343 := bstep (se 1 (by rfl) ⟨4622507, by rfl⟩ : syracuseStep 6163343 = 9245015) B9245015
theorem B12979115 : Blo 1136633 12979115 := bstep (se 1 (by rfl) ⟨9734336, by rfl⟩ : syracuseStep 12979115 = 19468673) B19468673
theorem B2558951 : Blo 1136633 2558951 := bstep (se 1 (by rfl) ⟨1919213, by rfl⟩ : syracuseStep 2558951 = 3838427) B3838427
theorem B3836915 : Blo 1136633 3836915 := bstep (se 1 (by rfl) ⟨2877686, by rfl⟩ : syracuseStep 3836915 = 5755373) B5755373
theorem B5475451 : Blo 1136633 5475451 := bstep (se 1 (by rfl) ⟨4106588, by rfl⟩ : syracuseStep 5475451 = 8213177) B8213177
theorem B2886779 : Blo 1136633 2886779 := bstep (se 1 (by rfl) ⟨2165084, by rfl⟩ : syracuseStep 2886779 = 4330169) B4330169
theorem B2886799 : Blo 1136633 2886799 := bstep (se 1 (by rfl) ⟨2165099, by rfl⟩ : syracuseStep 2886799 = 4330199) B4330199
theorem B1707227 : Blo 1136633 1707227 := bstep (se 1 (by rfl) ⟨1280420, by rfl⟩ : syracuseStep 1707227 = 2560841) B2560841
theorem B2559329 : Blo 1136633 2559329 := bstep (se 2 (by rfl) ⟨959748, by rfl⟩ : syracuseStep 2559329 = 1919497) B1919497
theorem B1707401 : Blo 1136633 1707401 := bstep (se 2 (by rfl) ⟨640275, by rfl⟩ : syracuseStep 1707401 = 1280551) B1280551
theorem B2887073 : Blo 1136633 2887073 := bstep (se 2 (by rfl) ⟨1082652, by rfl⟩ : syracuseStep 2887073 = 2165305) B2165305
theorem B2559419 : Blo 1136633 2559419 := bstep (se 1 (by rfl) ⟨1919564, by rfl⟩ : syracuseStep 2559419 = 3839129) B3839129
theorem B3247559 : Blo 1136633 3247559 := bstep (se 1 (by rfl) ⟨2435669, by rfl⟩ : syracuseStep 3247559 = 4871339) B4871339
theorem B9244169 : Blo 1136633 9244169 := bstep (se 2 (by rfl) ⟨3466563, by rfl⟩ : syracuseStep 9244169 = 6933127) B6933127
theorem B3837455 : Blo 1136633 3837455 := bstep (se 1 (by rfl) ⟨2878091, by rfl⟩ : syracuseStep 3837455 = 5756183) B5756183
theorem B2559545 : Blo 1136633 2559545 := bstep (se 2 (by rfl) ⟨959829, by rfl⟩ : syracuseStep 2559545 = 1919659) B1919659
theorem B1281631 : Blo 1136633 1281631 := bstep (se 1 (by rfl) ⟨961223, by rfl⟩ : syracuseStep 1281631 = 1922447) B1922447
theorem B1707755 : Blo 1136633 1707755 := bstep (se 1 (by rfl) ⟨1280816, by rfl⟩ : syracuseStep 1707755 = 2561633) B2561633
theorem B4329227 : Blo 1136633 4329227 := bstep (se 1 (by rfl) ⟨3246920, by rfl⟩ : syracuseStep 4329227 = 6493841) B6493841
theorem B1707983 : Blo 1136633 1707983 := bstep (se 1 (by rfl) ⟨1280987, by rfl⟩ : syracuseStep 1707983 = 2561975) B2561975
theorem B5836859 : Blo 1136633 5836859 := bstep (se 1 (by rfl) ⟨4377644, by rfl⟩ : syracuseStep 5836859 = 8755289) B8755289
theorem B2560211 : Blo 1136633 2560211 := bstep (se 1 (by rfl) ⟨1920158, by rfl⟩ : syracuseStep 2560211 = 3840317) B3840317
theorem B4329683 : Blo 1136633 4329683 := bstep (se 1 (by rfl) ⟨3247262, by rfl⟩ : syracuseStep 4329683 = 6494525) B6494525
theorem B2560265 : Blo 1136633 2560265 := bstep (se 2 (by rfl) ⟨960099, by rfl⟩ : syracuseStep 2560265 = 1920199) B1920199
theorem B1708379 : Blo 1136633 1708379 := bstep (se 1 (by rfl) ⟨1281284, by rfl⟩ : syracuseStep 1708379 = 2562569) B2562569
theorem B1315183 : Blo 1136633 1315183 := bstep (se 1 (by rfl) ⟨986387, by rfl⟩ : syracuseStep 1315183 = 1972775) B1972775
theorem B1216891 : Blo 1136633 1216891 := bstep (se 1 (by rfl) ⟨912668, by rfl⟩ : syracuseStep 1216891 = 1825337) B1825337
theorem B6492635 : Blo 1136633 6492635 := bstep (se 1 (by rfl) ⟨4869476, by rfl⟩ : syracuseStep 6492635 = 9738953) B9738953
theorem B2560481 : Blo 1136633 2560481 := bstep (se 2 (by rfl) ⟨960180, by rfl⟩ : syracuseStep 2560481 = 1920361) B1920361
theorem B1708607 : Blo 1136633 1708607 := bstep (se 1 (by rfl) ⟨1281455, by rfl⟩ : syracuseStep 1708607 = 2562911) B2562911
theorem B3838535 : Blo 1136633 3838535 := bstep (se 1 (by rfl) ⟨2878901, by rfl⟩ : syracuseStep 3838535 = 5757803) B5757803
theorem B5771897 : Blo 1136633 5771897 := bstep (se 2 (by rfl) ⟨2164461, by rfl⟩ : syracuseStep 5771897 = 4328923) B4328923
theorem B1708727 : Blo 1136633 1708727 := bstep (se 1 (by rfl) ⟨1281545, by rfl⟩ : syracuseStep 1708727 = 2563091) B2563091
theorem B1282783 : Blo 1136633 1282783 := bstep (se 1 (by rfl) ⟨962087, by rfl⟩ : syracuseStep 1282783 = 1924175) B1924175
theorem B2560787 : Blo 1136633 2560787 := bstep (se 1 (by rfl) ⟨1920590, by rfl⟩ : syracuseStep 2560787 = 3841181) B3841181
theorem B8655659 : Blo 1136633 8655659 := bstep (se 1 (by rfl) ⟨6491744, by rfl⟩ : syracuseStep 8655659 = 12983489) B12983489
theorem B1708955 : Blo 1136633 1708955 := bstep (se 1 (by rfl) ⟨1281716, by rfl⟩ : syracuseStep 1708955 = 2563433) B2563433
theorem B3838967 : Blo 1136633 3838967 := bstep (se 1 (by rfl) ⟨2879225, by rfl⟩ : syracuseStep 3838967 = 5758451) B5758451
theorem B2561147 : Blo 1136633 2561147 := bstep (se 1 (by rfl) ⟨1920860, by rfl⟩ : syracuseStep 2561147 = 3841721) B3841721
theorem B2561273 : Blo 1136633 2561273 := bstep (se 2 (by rfl) ⟨960477, by rfl⟩ : syracuseStep 2561273 = 1920955) B1920955
theorem B1709351 : Blo 1136633 1709351 := bstep (se 1 (by rfl) ⟨1282013, by rfl⟩ : syracuseStep 1709351 = 2564027) B2564027
theorem B1709435 : Blo 1136633 1709435 := bstep (se 1 (by rfl) ⟨1282076, by rfl⟩ : syracuseStep 1709435 = 2564153) B2564153
theorem B2561417 : Blo 1136633 2561417 := bstep (se 2 (by rfl) ⟨960531, by rfl⟩ : syracuseStep 2561417 = 1921063) B1921063
theorem B35067329 : Blo 1136633 35067329 := bstep (se 2 (by rfl) ⟨13150248, by rfl⟩ : syracuseStep 35067329 = 26300497) B26300497
theorem B2430407 : Blo 1136633 2430407 := bstep (se 1 (by rfl) ⟨1822805, by rfl⟩ : syracuseStep 2430407 = 3645611) B3645611
theorem B4855277 : Blo 1136633 4855277 := bstep (se 3 (by rfl) ⟨910364, by rfl⟩ : syracuseStep 4855277 = 1820729) B1820729
theorem B1709561 : Blo 1136633 1709561 := bstep (se 2 (by rfl) ⟨641085, by rfl⟩ : syracuseStep 1709561 = 1282171) B1282171
theorem B2561543 : Blo 1136633 2561543 := bstep (se 1 (by rfl) ⟨1921157, by rfl⟩ : syracuseStep 2561543 = 3842315) B3842315
theorem B1709663 : Blo 1136633 1709663 := bstep (se 1 (by rfl) ⟨1282247, by rfl⟩ : syracuseStep 1709663 = 2564495) B2564495
theorem B2561723 : Blo 1136633 2561723 := bstep (se 1 (by rfl) ⟨1921292, by rfl⟩ : syracuseStep 2561723 = 3842585) B3842585
theorem B1709879 : Blo 1136633 1709879 := bstep (se 1 (by rfl) ⟨1282409, by rfl⟩ : syracuseStep 1709879 = 2564819) B2564819
theorem B2561849 : Blo 1136633 2561849 := bstep (se 2 (by rfl) ⟨960693, by rfl⟩ : syracuseStep 2561849 = 1921387) B1921387
theorem B3839831 : Blo 1136633 3839831 := bstep (se 1 (by rfl) ⟨2879873, by rfl⟩ : syracuseStep 3839831 = 5759747) B5759747
theorem B13867037 : Blo 1136633 13867037 := bstep (se 3 (by rfl) ⟨2600069, by rfl⟩ : syracuseStep 13867037 = 5200139) B5200139
theorem B4102177 : Blo 1136633 4102177 := bstep (se 2 (by rfl) ⟨1538316, by rfl⟩ : syracuseStep 4102177 = 3076633) B3076633
theorem B1710185 : Blo 1136633 1710185 := bstep (se 2 (by rfl) ⟨641319, by rfl⟩ : syracuseStep 1710185 = 1282639) B1282639
theorem B46733593 : Blo 1136633 46733593 := bstep (se 2 (by rfl) ⟨17525097, by rfl⟩ : syracuseStep 46733593 = 35050195) B35050195
theorem B5773679 : Blo 1136633 5773679 := bstep (se 1 (by rfl) ⟨4330259, by rfl⟩ : syracuseStep 5773679 = 8660519) B8660519
theorem B1710503 : Blo 1136633 1710503 := bstep (se 1 (by rfl) ⟨1282877, by rfl⟩ : syracuseStep 1710503 = 2565755) B2565755
theorem B2562479 : Blo 1136633 2562479 := bstep (se 1 (by rfl) ⟨1921859, by rfl⟩ : syracuseStep 2562479 = 3843719) B3843719
theorem B2562515 : Blo 1136633 2562515 := bstep (se 1 (by rfl) ⟨1921886, by rfl⟩ : syracuseStep 2562515 = 3843773) B3843773
theorem B1710587 : Blo 1136633 1710587 := bstep (se 1 (by rfl) ⟨1282940, by rfl⟩ : syracuseStep 1710587 = 2565881) B2565881
theorem B29170205 : Blo 1136633 29170205 := bstep (se 3 (by rfl) ⟨5469413, by rfl⟩ : syracuseStep 29170205 = 10938827) B10938827
theorem B2562623 : Blo 1136633 2562623 := bstep (se 1 (by rfl) ⟨1921967, by rfl⟩ : syracuseStep 2562623 = 3843935) B3843935
theorem B2431595 : Blo 1136633 2431595 := bstep (se 1 (by rfl) ⟨1823696, by rfl⟩ : syracuseStep 2431595 = 3647393) B3647393
theorem B1710713 : Blo 1136633 1710713 := bstep (se 2 (by rfl) ⟨641517, by rfl⟩ : syracuseStep 1710713 = 1283035) B1283035
theorem B2562731 : Blo 1136633 2562731 := bstep (se 1 (by rfl) ⟨1922048, by rfl⟩ : syracuseStep 2562731 = 3844097) B3844097
theorem B2529967 : Blo 1136633 2529967 := bstep (se 1 (by rfl) ⟨1897475, by rfl⟩ : syracuseStep 2529967 = 3794951) B3794951
theorem B1710767 : Blo 1136633 1710767 := bstep (se 1 (by rfl) ⟨1283075, by rfl⟩ : syracuseStep 1710767 = 2566151) B2566151
theorem B8657603 : Blo 1136633 8657603 := bstep (se 1 (by rfl) ⟨6493202, by rfl⟩ : syracuseStep 8657603 = 12986405) B12986405
theorem B1710815 : Blo 1136633 1710815 := bstep (se 1 (by rfl) ⟨1283111, by rfl⟩ : syracuseStep 1710815 = 2566223) B2566223
theorem B17505143 : Blo 1136633 17505143 := bstep (se 1 (by rfl) ⟨13128857, by rfl⟩ : syracuseStep 17505143 = 26257715) B26257715
theorem B3840911 : Blo 1136633 3840911 := bstep (se 1 (by rfl) ⟨2880683, by rfl⟩ : syracuseStep 3840911 = 5761367) B5761367
theorem B4922491 : Blo 1136633 4922491 := bstep (se 1 (by rfl) ⟨3691868, by rfl⟩ : syracuseStep 4922491 = 7383737) B7383737
theorem B2563271 : Blo 1136633 2563271 := bstep (se 1 (by rfl) ⟨1922453, by rfl⟩ : syracuseStep 2563271 = 3844907) B3844907
theorem B2464987 : Blo 1136633 2464987 := bstep (se 1 (by rfl) ⟨1848740, by rfl⟩ : syracuseStep 2464987 = 3697481) B3697481
theorem B2563451 : Blo 1136633 2563451 := bstep (se 1 (by rfl) ⟨1922588, by rfl⟩ : syracuseStep 2563451 = 3845177) B3845177
theorem B4103561 : Blo 1136633 4103561 := bstep (se 2 (by rfl) ⟨1538835, by rfl⟩ : syracuseStep 4103561 = 3077671) B3077671
theorem B2563577 : Blo 1136633 2563577 := bstep (se 2 (by rfl) ⟨961341, by rfl⟩ : syracuseStep 2563577 = 1922683) B1922683
theorem B2563667 : Blo 1136633 2563667 := bstep (se 1 (by rfl) ⟨1922750, by rfl⟩ : syracuseStep 2563667 = 3845501) B3845501
theorem B2563847 : Blo 1136633 2563847 := bstep (se 1 (by rfl) ⟨1922885, by rfl⟩ : syracuseStep 2563847 = 3845771) B3845771
theorem B2432825 : Blo 1136633 2432825 := bstep (se 2 (by rfl) ⟨912309, by rfl⟩ : syracuseStep 2432825 = 1824619) B1824619
theorem B3842153 : Blo 1136633 3842153 := bstep (se 2 (by rfl) ⟨1440807, by rfl⟩ : syracuseStep 3842153 = 2881615) B2881615
theorem B2433235 : Blo 1136633 2433235 := bstep (se 1 (by rfl) ⟨1824926, by rfl⟩ : syracuseStep 2433235 = 3649853) B3649853
theorem B2564459 : Blo 1136633 2564459 := bstep (se 1 (by rfl) ⟨1923344, by rfl⟩ : syracuseStep 2564459 = 3846689) B3846689
theorem B2564603 : Blo 1136633 2564603 := bstep (se 1 (by rfl) ⟨1923452, by rfl⟩ : syracuseStep 2564603 = 3846905) B3846905
theorem B2564729 : Blo 1136633 2564729 := bstep (se 2 (by rfl) ⟨961773, by rfl⟩ : syracuseStep 2564729 = 1923547) B1923547
theorem B2564783 : Blo 1136633 2564783 := bstep (se 1 (by rfl) ⟨1923587, by rfl⟩ : syracuseStep 2564783 = 3847175) B3847175
theorem B2564855 : Blo 1136633 2564855 := bstep (se 1 (by rfl) ⟨1923641, by rfl⟩ : syracuseStep 2564855 = 3847283) B3847283
theorem B2565035 : Blo 1136633 2565035 := bstep (se 1 (by rfl) ⟨1923776, by rfl⟩ : syracuseStep 2565035 = 3847553) B3847553
theorem B3843017 : Blo 1136633 3843017 := bstep (se 2 (by rfl) ⟨1441131, by rfl⟩ : syracuseStep 3843017 = 2882263) B2882263
theorem B3122315 : Blo 1136633 3122315 := bstep (se 1 (by rfl) ⟨2341736, by rfl⟩ : syracuseStep 3122315 = 4683473) B4683473
theorem B74884247 : Blo 1136633 74884247 := bstep (se 1 (by rfl) ⟨56163185, by rfl⟩ : syracuseStep 74884247 = 112326371) B112326371
theorem B3843287 : Blo 1136633 3843287 := bstep (se 1 (by rfl) ⟨2882465, by rfl⟩ : syracuseStep 3843287 = 5764931) B5764931
theorem B2434465 : Blo 1136633 2434465 := bstep (se 2 (by rfl) ⟨912924, by rfl⟩ : syracuseStep 2434465 = 1825849) B1825849
theorem B2565575 : Blo 1136633 2565575 := bstep (se 1 (by rfl) ⟨1924181, by rfl⟩ : syracuseStep 2565575 = 3848363) B3848363
theorem B2565935 : Blo 1136633 2565935 := bstep (se 1 (by rfl) ⟨1924451, by rfl⟩ : syracuseStep 2565935 = 3848903) B3848903
theorem B1386319 : Blo 1136633 1386319 := bstep (se 1 (by rfl) ⟨1039739, by rfl⟩ : syracuseStep 1386319 = 2079479) B2079479
theorem B4106663 : Blo 1136633 4106663 := bstep (se 1 (by rfl) ⟨3079997, by rfl⟩ : syracuseStep 4106663 = 6159995) B6159995
theorem B8661491 : Blo 1136633 8661491 := bstep (se 1 (by rfl) ⟨6496118, by rfl⟩ : syracuseStep 8661491 = 12992237) B12992237
theorem B2436011 : Blo 1136633 2436011 := bstep (se 1 (by rfl) ⟨1827008, by rfl⟩ : syracuseStep 2436011 = 3654017) B3654017
theorem B6237199 : Blo 1136633 6237199 := bstep (se 1 (by rfl) ⟨4677899, by rfl⟩ : syracuseStep 6237199 = 9355799) B9355799
theorem B6237307 : Blo 1136633 6237307 := bstep (se 1 (by rfl) ⟨4677980, by rfl⟩ : syracuseStep 6237307 = 9355961) B9355961
theorem B3648635 : Blo 1136633 3648635 := bstep (se 1 (by rfl) ⟨2736476, by rfl⟩ : syracuseStep 3648635 = 5472953) B5472953
theorem B3845339 : Blo 1136633 3845339 := bstep (se 1 (by rfl) ⟨2884004, by rfl⟩ : syracuseStep 3845339 = 5768009) B5768009
theorem B2305847 : Blo 1136633 2305847 := bstep (se 1 (by rfl) ⟨1729385, by rfl⟩ : syracuseStep 2305847 = 3458771) B3458771
theorem B3846203 : Blo 1136633 3846203 := bstep (se 1 (by rfl) ⟨2884652, by rfl⟩ : syracuseStep 3846203 = 5769305) B5769305
theorem B3846473 : Blo 1136633 3846473 := bstep (se 2 (by rfl) ⟨1442427, by rfl⟩ : syracuseStep 3846473 = 2884855) B2884855
theorem B291877739 : Blo 1136633 291877739 := bstep (se 1 (by rfl) ⟨218908304, by rfl⟩ : syracuseStep 291877739 = 437816609) B437816609
theorem B9843565 : Blo 1136633 9843565 := bstep (se 3 (by rfl) ⟨1845668, by rfl⟩ : syracuseStep 9843565 = 3691337) B3691337
theorem B2307215 : Blo 1136633 2307215 := bstep (se 1 (by rfl) ⟨1730411, by rfl⟩ : syracuseStep 2307215 = 3460823) B3460823
theorem B2372903 : Blo 1136633 2372903 := bstep (se 1 (by rfl) ⟨1779677, by rfl⟩ : syracuseStep 2372903 = 3559355) B3559355
theorem B4863341 : Blo 1136633 4863341 := bstep (se 3 (by rfl) ⟨911876, by rfl⟩ : syracuseStep 4863341 = 1823753) B1823753
theorem B8631845 : Blo 1136633 8631845 := bstep (se 4 (by rfl) ⟨809235, by rfl⟩ : syracuseStep 8631845 = 1618471) B1618471
theorem B4864367 : Blo 1136633 4864367 := bstep (se 1 (by rfl) ⟨3648275, by rfl⟩ : syracuseStep 4864367 = 7296551) B7296551
theorem B5192255 : Blo 1136633 5192255 := bstep (se 1 (by rfl) ⟨3894191, by rfl⟩ : syracuseStep 5192255 = 7788383) B7788383
theorem B5192387 : Blo 1136633 5192387 := bstep (se 1 (by rfl) ⟨3894290, by rfl⟩ : syracuseStep 5192387 = 7788581) B7788581
theorem B35011273 : Blo 1136633 35011273 := bstep (se 2 (by rfl) ⟨13129227, by rfl⟩ : syracuseStep 35011273 = 26258455) B26258455
theorem B10927223 : Blo 1136633 10927223 := bstep (se 1 (by rfl) ⟨8195417, by rfl⟩ : syracuseStep 10927223 = 16390835) B16390835
theorem B128138381 : Blo 1136633 128138381 := bstep (se 3 (by rfl) ⟨24025946, by rfl⟩ : syracuseStep 128138381 = 48051893) B48051893
theorem B4865291 : Blo 1136633 4865291 := bstep (se 1 (by rfl) ⟨3648968, by rfl⟩ : syracuseStep 4865291 = 7297937) B7297937
theorem B3456443 : Blo 1136633 3456443 := bstep (se 1 (by rfl) ⟨2592332, by rfl⟩ : syracuseStep 3456443 = 5184665) B5184665
theorem B2048695 : Blo 1136633 2048695 := bstep (se 1 (by rfl) ⟨1536521, by rfl⟩ : syracuseStep 2048695 = 3073043) B3073043
theorem B4866743 : Blo 1136633 4866743 := bstep (se 1 (by rfl) ⟨3650057, by rfl⟩ : syracuseStep 4866743 = 7300115) B7300115
theorem B4866895 : Blo 1136633 4866895 := bstep (se 1 (by rfl) ⟨3650171, by rfl⟩ : syracuseStep 4866895 = 7300343) B7300343
theorem B9225359 : Blo 1136633 9225359 := bstep (se 1 (by rfl) ⟨6919019, by rfl⟩ : syracuseStep 9225359 = 13838039) B13838039
theorem B4375795 : Blo 1136633 4375795 := bstep (se 1 (by rfl) ⟨3281846, by rfl⟩ : syracuseStep 4375795 = 6563693) B6563693
theorem B2311561 : Blo 1136633 2311561 := bstep (se 2 (by rfl) ⟨866835, by rfl⟩ : syracuseStep 2311561 = 1733671) B1733671
theorem B1918559 : Blo 1136633 1918559 := bstep (se 1 (by rfl) ⟨1438919, by rfl⟩ : syracuseStep 1918559 = 2877839) B2877839
theorem B1918775 : Blo 1136633 1918775 := bstep (se 1 (by rfl) ⟨1439081, by rfl⟩ : syracuseStep 1918775 = 2878163) B2878163
theorem B13846403 : Blo 1136633 13846403 := bstep (se 1 (by rfl) ⟨10384802, by rfl⟩ : syracuseStep 13846403 = 20769605) B20769605
theorem B24627077 : Blo 1136633 24627077 := bstep (se 4 (by rfl) ⟨2308788, by rfl⟩ : syracuseStep 24627077 = 4617577) B4617577
theorem B1919551 : Blo 1136633 1919551 := bstep (se 1 (by rfl) ⟨1439663, by rfl⟩ : syracuseStep 1919551 = 2879327) B2879327
theorem B9718481 : Blo 1136633 9718481 := bstep (se 2 (by rfl) ⟨3644430, by rfl⟩ : syracuseStep 9718481 = 7288861) B7288861
theorem B5196563 : Blo 1136633 5196563 := bstep (se 1 (by rfl) ⟨3897422, by rfl⟩ : syracuseStep 5196563 = 7794845) B7794845
theorem B2739187 : Blo 1136633 2739187 := bstep (se 1 (by rfl) ⟨2054390, by rfl⟩ : syracuseStep 2739187 = 4108781) B4108781
theorem B1920233 : Blo 1136633 1920233 := bstep (se 2 (by rfl) ⟨720087, by rfl⟩ : syracuseStep 1920233 = 1440175) B1440175
theorem B1920287 : Blo 1136633 1920287 := bstep (se 1 (by rfl) ⟨1440215, by rfl⟩ : syracuseStep 1920287 = 2880431) B2880431
theorem B27741845 : Blo 1136633 27741845 := bstep (se 6 (by rfl) ⟨650199, by rfl⟩ : syracuseStep 27741845 = 1300399) B1300399
theorem B8638163 : Blo 1136633 8638163 := bstep (se 1 (by rfl) ⟨6478622, by rfl⟩ : syracuseStep 8638163 = 12957245) B12957245
theorem B27676451 : Blo 1136633 27676451 := bstep (se 1 (by rfl) ⟨20757338, by rfl⟩ : syracuseStep 27676451 = 41514677) B41514677
theorem B1823087 : Blo 1136633 1823087 := bstep (se 1 (by rfl) ⟨1367315, by rfl⟩ : syracuseStep 1823087 = 2734631) B2734631
theorem B7787069 : Blo 1136633 7787069 := bstep (se 3 (by rfl) ⟨1460075, by rfl⟩ : syracuseStep 7787069 = 2920151) B2920151
theorem B1823305 : Blo 1136633 1823305 := bstep (se 2 (by rfl) ⟨683739, by rfl⟩ : syracuseStep 1823305 = 1367479) B1367479
theorem B1921657 : Blo 1136633 1921657 := bstep (se 2 (by rfl) ⟨720621, by rfl⟩ : syracuseStep 1921657 = 1441243) B1441243
theorem B1921711 : Blo 1136633 1921711 := bstep (se 1 (by rfl) ⟨1441283, by rfl⟩ : syracuseStep 1921711 = 2882567) B2882567
theorem B6148811 : Blo 1136633 6148811 := bstep (se 1 (by rfl) ⟨4611608, by rfl⟩ : syracuseStep 6148811 = 9223217) B9223217
theorem B9851615 : Blo 1136633 9851615 := bstep (se 1 (by rfl) ⟨7388711, by rfl⟩ : syracuseStep 9851615 = 14777423) B14777423
theorem B9721079 : Blo 1136633 9721079 := bstep (se 1 (by rfl) ⟨7290809, by rfl⟩ : syracuseStep 9721079 = 14581619) B14581619
theorem B2774825 : Blo 1136633 2774825 := bstep (se 2 (by rfl) ⟨1040559, by rfl⟩ : syracuseStep 2774825 = 2081119) B2081119
theorem B147740597 : Blo 1136633 147740597 := bstep (se 5 (by rfl) ⟨6925340, by rfl⟩ : syracuseStep 147740597 = 13850681) B13850681
theorem B1136927 : Blo 1136633 1136927 := bstep (se 1 (by rfl) ⟨852695, by rfl⟩ : syracuseStep 1136927 = 1705391) B1705391
theorem B1136987 : Blo 1136633 1136987 := bstep (se 1 (by rfl) ⟨852740, by rfl⟩ : syracuseStep 1136987 = 1705481) B1705481
theorem B1923419 : Blo 1136633 1923419 := bstep (se 1 (by rfl) ⟨1442564, by rfl⟩ : syracuseStep 1923419 = 2885129) B2885129
theorem B1137007 : Blo 1136633 1137007 := bstep (se 1 (by rfl) ⟨852755, by rfl⟩ : syracuseStep 1137007 = 1705511) B1705511
theorem B1923439 : Blo 1136633 1923439 := bstep (se 1 (by rfl) ⟨1442579, by rfl⟩ : syracuseStep 1923439 = 2885159) B2885159
theorem B1137063 : Blo 1136633 1137063 := bstep (se 1 (by rfl) ⟨852797, by rfl⟩ : syracuseStep 1137063 = 1705595) B1705595
theorem B1137147 : Blo 1136633 1137147 := bstep (se 1 (by rfl) ⟨852860, by rfl⟩ : syracuseStep 1137147 = 1705721) B1705721
theorem B5757479 : Blo 1136633 5757479 := bstep (se 1 (by rfl) ⟨4318109, by rfl⟩ : syracuseStep 5757479 = 8636219) B8636219
theorem B1137215 : Blo 1136633 1137215 := bstep (se 1 (by rfl) ⟨852911, by rfl⟩ : syracuseStep 1137215 = 1705823) B1705823
theorem B1137223 : Blo 1136633 1137223 := bstep (se 1 (by rfl) ⟨852917, by rfl⟩ : syracuseStep 1137223 = 1705835) B1705835
theorem B1923655 : Blo 1136633 1923655 := bstep (se 1 (by rfl) ⟨1442741, by rfl⟩ : syracuseStep 1923655 = 2885483) B2885483
theorem B1137375 : Blo 1136633 1137375 := bstep (se 1 (by rfl) ⟨853031, by rfl⟩ : syracuseStep 1137375 = 1706063) B1706063
theorem B1137455 : Blo 1136633 1137455 := bstep (se 1 (by rfl) ⟨853091, by rfl⟩ : syracuseStep 1137455 = 1706183) B1706183
theorem B1137563 : Blo 1136633 1137563 := bstep (se 1 (by rfl) ⟨853172, by rfl⟩ : syracuseStep 1137563 = 1706345) B1706345
theorem B4316075 : Blo 1136633 4316075 := bstep (se 1 (by rfl) ⟨3237056, by rfl⟩ : syracuseStep 4316075 = 6474113) B6474113
theorem B1137615 : Blo 1136633 1137615 := bstep (se 1 (by rfl) ⟨853211, by rfl⟩ : syracuseStep 1137615 = 1706423) B1706423
theorem B1137639 : Blo 1136633 1137639 := bstep (se 1 (by rfl) ⟨853229, by rfl⟩ : syracuseStep 1137639 = 1706459) B1706459
theorem B1924087 : Blo 1136633 1924087 := bstep (se 1 (by rfl) ⟨1443065, by rfl⟩ : syracuseStep 1924087 = 2886131) B2886131
theorem B8641565 : Blo 1136633 8641565 := bstep (se 3 (by rfl) ⟨1620293, by rfl⟩ : syracuseStep 8641565 = 3240587) B3240587
theorem B1137951 : Blo 1136633 1137951 := bstep (se 1 (by rfl) ⟨853463, by rfl⟩ : syracuseStep 1137951 = 1706927) B1706927
theorem B1924391 : Blo 1136633 1924391 := bstep (se 1 (by rfl) ⟨1443293, by rfl⟩ : syracuseStep 1924391 = 2886587) B2886587
theorem B1138011 : Blo 1136633 1138011 := bstep (se 1 (by rfl) ⟨853508, by rfl⟩ : syracuseStep 1138011 = 1707017) B1707017
theorem B1138031 : Blo 1136633 1138031 := bstep (se 1 (by rfl) ⟨853523, by rfl⟩ : syracuseStep 1138031 = 1707047) B1707047
theorem B1138087 : Blo 1136633 1138087 := bstep (se 1 (by rfl) ⟨853565, by rfl⟩ : syracuseStep 1138087 = 1707131) B1707131
theorem B1138171 : Blo 1136633 1138171 := bstep (se 1 (by rfl) ⟨853628, by rfl⟩ : syracuseStep 1138171 = 1707257) B1707257
theorem B1138239 : Blo 1136633 1138239 := bstep (se 1 (by rfl) ⟨853679, by rfl⟩ : syracuseStep 1138239 = 1707359) B1707359
theorem B1138247 : Blo 1136633 1138247 := bstep (se 1 (by rfl) ⟨853685, by rfl⟩ : syracuseStep 1138247 = 1707371) B1707371
theorem B1138399 : Blo 1136633 1138399 := bstep (se 1 (by rfl) ⟨853799, by rfl⟩ : syracuseStep 1138399 = 1707599) B1707599
theorem B1826567 : Blo 1136633 1826567 := bstep (se 1 (by rfl) ⟨1369925, by rfl⟩ : syracuseStep 1826567 = 2739851) B2739851
theorem B41606945 : Blo 1136633 41606945 := bstep (se 2 (by rfl) ⟨15602604, by rfl⟩ : syracuseStep 41606945 = 31205209) B31205209
theorem B1138479 : Blo 1136633 1138479 := bstep (se 1 (by rfl) ⟨853859, by rfl⟩ : syracuseStep 1138479 = 1707719) B1707719
theorem B1138587 : Blo 1136633 1138587 := bstep (se 1 (by rfl) ⟨853940, by rfl⟩ : syracuseStep 1138587 = 1707881) B1707881
theorem B1138639 : Blo 1136633 1138639 := bstep (se 1 (by rfl) ⟨853979, by rfl⟩ : syracuseStep 1138639 = 1707959) B1707959
theorem B1138663 : Blo 1136633 1138663 := bstep (se 1 (by rfl) ⟨853997, by rfl⟩ : syracuseStep 1138663 = 1707995) B1707995
theorem B1138975 : Blo 1136633 1138975 := bstep (se 1 (by rfl) ⟨854231, by rfl⟩ : syracuseStep 1138975 = 1708463) B1708463
theorem B24994109 : Blo 1136633 24994109 := bstep (se 3 (by rfl) ⟨4686395, by rfl⟩ : syracuseStep 24994109 = 9372791) B9372791
theorem B1139035 : Blo 1136633 1139035 := bstep (se 1 (by rfl) ⟨854276, by rfl⟩ : syracuseStep 1139035 = 1708553) B1708553
theorem B1139055 : Blo 1136633 1139055 := bstep (se 1 (by rfl) ⟨854291, by rfl⟩ : syracuseStep 1139055 = 1708583) B1708583
theorem B1139111 : Blo 1136633 1139111 := bstep (se 1 (by rfl) ⟨854333, by rfl⟩ : syracuseStep 1139111 = 1708667) B1708667
theorem B1139195 : Blo 1136633 1139195 := bstep (se 1 (by rfl) ⟨854396, by rfl⟩ : syracuseStep 1139195 = 1708793) B1708793
theorem B1139263 : Blo 1136633 1139263 := bstep (se 1 (by rfl) ⟨854447, by rfl⟩ : syracuseStep 1139263 = 1708895) B1708895
theorem B1139271 : Blo 1136633 1139271 := bstep (se 1 (by rfl) ⟨854453, by rfl⟩ : syracuseStep 1139271 = 1708907) B1708907
theorem B5759585 : Blo 1136633 5759585 := bstep (se 2 (by rfl) ⟨2159844, by rfl⟩ : syracuseStep 5759585 = 4319689) B4319689
theorem B1139423 : Blo 1136633 1139423 := bstep (se 1 (by rfl) ⟨854567, by rfl⟩ : syracuseStep 1139423 = 1709135) B1709135
theorem B1139503 : Blo 1136633 1139503 := bstep (se 1 (by rfl) ⟨854627, by rfl⟩ : syracuseStep 1139503 = 1709255) B1709255
theorem B1139611 : Blo 1136633 1139611 := bstep (se 1 (by rfl) ⟨854708, by rfl⟩ : syracuseStep 1139611 = 1709417) B1709417
theorem B5465033 : Blo 1136633 5465033 := bstep (se 2 (by rfl) ⟨2049387, by rfl⟩ : syracuseStep 5465033 = 4098775) B4098775
theorem B1139663 : Blo 1136633 1139663 := bstep (se 1 (by rfl) ⟨854747, by rfl⟩ : syracuseStep 1139663 = 1709495) B1709495
theorem B1139687 : Blo 1136633 1139687 := bstep (se 1 (by rfl) ⟨854765, by rfl⟩ : syracuseStep 1139687 = 1709531) B1709531
theorem B179627057 : Blo 1136633 179627057 := bstep (se 2 (by rfl) ⟨67360146, by rfl⟩ : syracuseStep 179627057 = 134720293) B134720293
theorem B5465245 : Blo 1136633 5465245 := bstep (se 3 (by rfl) ⟨1024733, by rfl⟩ : syracuseStep 5465245 = 2049467) B2049467
theorem B3237079 : Blo 1136633 3237079 := bstep (se 1 (by rfl) ⟨2427809, by rfl⟩ : syracuseStep 3237079 = 4855619) B4855619
theorem B5465303 : Blo 1136633 5465303 := bstep (se 1 (by rfl) ⟨4098977, by rfl⟩ : syracuseStep 5465303 = 8197955) B8197955
theorem B5760233 : Blo 1136633 5760233 := bstep (se 2 (by rfl) ⟨2160087, by rfl⟩ : syracuseStep 5760233 = 4320175) B4320175
theorem B1139999 : Blo 1136633 1139999 := bstep (se 1 (by rfl) ⟨854999, by rfl⟩ : syracuseStep 1139999 = 1709999) B1709999
theorem B1140059 : Blo 1136633 1140059 := bstep (se 1 (by rfl) ⟨855044, by rfl⟩ : syracuseStep 1140059 = 1710089) B1710089
theorem B1140079 : Blo 1136633 1140079 := bstep (se 1 (by rfl) ⟨855059, by rfl⟩ : syracuseStep 1140079 = 1710119) B1710119
theorem B5760395 : Blo 1136633 5760395 := bstep (se 1 (by rfl) ⟨4320296, by rfl⟩ : syracuseStep 5760395 = 8640593) B8640593
theorem B1140135 : Blo 1136633 1140135 := bstep (se 1 (by rfl) ⟨855101, by rfl⟩ : syracuseStep 1140135 = 1710203) B1710203
theorem B32826869 : Blo 1136633 32826869 := bstep (se 5 (by rfl) ⟨1538759, by rfl⟩ : syracuseStep 32826869 = 3077519) B3077519
theorem B1140219 : Blo 1136633 1140219 := bstep (se 1 (by rfl) ⟨855164, by rfl⟩ : syracuseStep 1140219 = 1710329) B1710329
theorem B1140287 : Blo 1136633 1140287 := bstep (se 1 (by rfl) ⟨855215, by rfl⟩ : syracuseStep 1140287 = 1710431) B1710431
theorem B1140295 : Blo 1136633 1140295 := bstep (se 1 (by rfl) ⟨855221, by rfl⟩ : syracuseStep 1140295 = 1710443) B1710443
theorem B14575261 : Blo 1136633 14575261 := bstep (se 3 (by rfl) ⟨2732861, by rfl⟩ : syracuseStep 14575261 = 5465723) B5465723
theorem B1140447 : Blo 1136633 1140447 := bstep (se 1 (by rfl) ⟨855335, by rfl⟩ : syracuseStep 1140447 = 1710671) B1710671
theorem B2877191 : Blo 1136633 2877191 := bstep (se 1 (by rfl) ⟨2157893, by rfl⟩ : syracuseStep 2877191 = 4315787) B4315787
theorem B1140527 : Blo 1136633 1140527 := bstep (se 1 (by rfl) ⟨855395, by rfl⟩ : syracuseStep 1140527 = 1710791) B1710791
theorem B2877241 : Blo 1136633 2877241 := bstep (se 2 (by rfl) ⟨1078965, by rfl⟩ : syracuseStep 2877241 = 2157931) B2157931
theorem B9725831 : Blo 1136633 9725831 := bstep (se 1 (by rfl) ⟨7294373, by rfl⟩ : syracuseStep 9725831 = 14588747) B14588747
theorem B2877545 : Blo 1136633 2877545 := bstep (se 2 (by rfl) ⟨1079079, by rfl⟩ : syracuseStep 2877545 = 2158159) B2158159
theorem B52553843 : Blo 1136633 52553843 := bstep (se 1 (by rfl) ⟨39415382, by rfl⟩ : syracuseStep 52553843 = 78830765) B78830765
theorem B10545437 : Blo 1136633 10545437 := bstep (se 3 (by rfl) ⟨1977269, by rfl⟩ : syracuseStep 10545437 = 3954539) B3954539
theorem B3238355 : Blo 1136633 3238355 := bstep (se 1 (by rfl) ⟨2428766, by rfl⟩ : syracuseStep 3238355 = 4857533) B4857533
theorem B2878031 : Blo 1136633 2878031 := bstep (se 1 (by rfl) ⟨2158523, by rfl⟩ : syracuseStep 2878031 = 4317047) B4317047
theorem B2189945 : Blo 1136633 2189945 := bstep (se 2 (by rfl) ⟨821229, by rfl⟩ : syracuseStep 2189945 = 1642459) B1642459
theorem B49310531 : Blo 1136633 49310531 := bstep (se 1 (by rfl) ⟨36982898, by rfl⟩ : syracuseStep 49310531 = 73965797) B73965797
theorem B3238811 : Blo 1136633 3238811 := bstep (se 1 (by rfl) ⟨2429108, by rfl⟩ : syracuseStep 3238811 = 4858217) B4858217
theorem B2878679 : Blo 1136633 2878679 := bstep (se 1 (by rfl) ⟨2159009, by rfl⟩ : syracuseStep 2878679 = 4318019) B4318019
theorem B6319457 : Blo 1136633 6319457 := bstep (se 2 (by rfl) ⟨2369796, by rfl⟩ : syracuseStep 6319457 = 4739593) B4739593
theorem B7302599 : Blo 1136633 7302599 := bstep (se 1 (by rfl) ⟨5476949, by rfl⟩ : syracuseStep 7302599 = 10953899) B10953899
theorem B5467763 : Blo 1136633 5467763 := bstep (se 1 (by rfl) ⟨4100822, by rfl⟩ : syracuseStep 5467763 = 8201645) B8201645
theorem B3239585 : Blo 1136633 3239585 := bstep (se 2 (by rfl) ⟨1214844, by rfl⟩ : syracuseStep 3239585 = 2429689) B2429689
theorem B2879995 : Blo 1136633 2879995 := bstep (se 1 (by rfl) ⟨2159996, by rfl⟩ : syracuseStep 2879995 = 4319993) B4319993
theorem B5763635 : Blo 1136633 5763635 := bstep (se 1 (by rfl) ⟨4322726, by rfl⟩ : syracuseStep 5763635 = 8645453) B8645453
theorem B2880107 : Blo 1136633 2880107 := bstep (se 1 (by rfl) ⟨2160080, by rfl⟩ : syracuseStep 2880107 = 4320161) B4320161
theorem B2880755 : Blo 1136633 2880755 := bstep (se 1 (by rfl) ⟨2160566, by rfl⟩ : syracuseStep 2880755 = 4321133) B4321133
theorem B2880967 : Blo 1136633 2880967 := bstep (se 1 (by rfl) ⟨2160725, by rfl⟩ : syracuseStep 2880967 = 4321451) B4321451
theorem B11826827 : Blo 1136633 11826827 := bstep (se 1 (by rfl) ⟨8870120, by rfl⟩ : syracuseStep 11826827 = 17740241) B17740241
theorem B3078017 : Blo 1136633 3078017 := bstep (se 2 (by rfl) ⟨1154256, by rfl⟩ : syracuseStep 3078017 = 2308513) B2308513
theorem B19429307 : Blo 1136633 19429307 := bstep (se 1 (by rfl) ⟨14571980, by rfl⟩ : syracuseStep 19429307 = 29143961) B29143961
theorem B6486095 : Blo 1136633 6486095 := bstep (se 1 (by rfl) ⟨4864571, by rfl⟩ : syracuseStep 6486095 = 9729143) B9729143
theorem B5470337 : Blo 1136633 5470337 := bstep (se 2 (by rfl) ⟨2051376, by rfl⟩ : syracuseStep 5470337 = 4102753) B4102753
theorem B5765255 : Blo 1136633 5765255 := bstep (se 1 (by rfl) ⟨4323941, by rfl⟩ : syracuseStep 5765255 = 8647883) B8647883
theorem B6486803 : Blo 1136633 6486803 := bstep (se 1 (by rfl) ⟨4865102, by rfl⟩ : syracuseStep 6486803 = 9730205) B9730205
theorem B3079055 : Blo 1136633 3079055 := bstep (se 1 (by rfl) ⟨2309291, by rfl⟩ : syracuseStep 3079055 = 4618583) B4618583
theorem B41483153 : Blo 1136633 41483153 := bstep (se 2 (by rfl) ⟨15556182, by rfl⟩ : syracuseStep 41483153 = 31112365) B31112365
theorem B18447277 : Blo 1136633 18447277 := bstep (se 3 (by rfl) ⟨3458864, by rfl⟩ : syracuseStep 18447277 = 6917729) B6917729
theorem B2882699 : Blo 1136633 2882699 := bstep (se 1 (by rfl) ⟨2162024, by rfl⟩ : syracuseStep 2882699 = 4324049) B4324049
theorem B11697317 : Blo 1136633 11697317 := bstep (se 4 (by rfl) ⟨1096623, by rfl⟩ : syracuseStep 11697317 = 2193247) B2193247
theorem B2882911 : Blo 1136633 2882911 := bstep (se 1 (by rfl) ⟨2162183, by rfl⟩ : syracuseStep 2882911 = 4324367) B4324367
theorem B1441147 : Blo 1136633 1441147 := bstep (se 1 (by rfl) ⟨1080860, by rfl⟩ : syracuseStep 1441147 = 2161721) B2161721
theorem B4324823 : Blo 1136633 4324823 := bstep (se 1 (by rfl) ⟨3243617, by rfl⟩ : syracuseStep 4324823 = 6487235) B6487235
theorem B5472011 : Blo 1136633 5472011 := bstep (se 1 (by rfl) ⟨4104008, by rfl⟩ : syracuseStep 5472011 = 8208017) B8208017
theorem B5472107 : Blo 1136633 5472107 := bstep (se 1 (by rfl) ⟨4104080, by rfl⟩ : syracuseStep 5472107 = 8208161) B8208161
theorem B2162639 : Blo 1136633 2162639 := bstep (se 1 (by rfl) ⟨1621979, by rfl⟩ : syracuseStep 2162639 = 3243959) B3243959
theorem B16646147 : Blo 1136633 16646147 := bstep (se 1 (by rfl) ⟨12484610, by rfl⟩ : syracuseStep 16646147 = 24969221) B24969221
theorem B3244313 : Blo 1136633 3244313 := bstep (se 2 (by rfl) ⟨1216617, by rfl⟩ : syracuseStep 3244313 = 2433235) B2433235
theorem B3244495 : Blo 1136633 3244495 := bstep (se 1 (by rfl) ⟨2433371, by rfl⟩ : syracuseStep 3244495 = 4866743) B4866743
theorem B14614991 : Blo 1136633 14614991 := bstep (se 1 (by rfl) ⟨10961243, by rfl⟩ : syracuseStep 14614991 = 21922487) B21922487
theorem B66650957 : Blo 1136633 66650957 := bstep (se 3 (by rfl) ⟨12497054, by rfl⟩ : syracuseStep 66650957 = 24994109) B24994109
theorem B4326311 : Blo 1136633 4326311 := bstep (se 1 (by rfl) ⟨3244733, by rfl⟩ : syracuseStep 4326311 = 6489467) B6489467
theorem B1279039 : Blo 1136633 1279039 := bstep (se 1 (by rfl) ⟨959279, by rfl⟩ : syracuseStep 1279039 = 1918559) B1918559
theorem B6489193 : Blo 1136633 6489193 := bstep (se 2 (by rfl) ⟨2433447, by rfl⟩ : syracuseStep 6489193 = 4866895) B4866895
theorem B1705067 : Blo 1136633 1705067 := bstep (se 1 (by rfl) ⟨1278800, by rfl⟩ : syracuseStep 1705067 = 2557601) B2557601
theorem B1279183 : Blo 1136633 1279183 := bstep (se 1 (by rfl) ⟨959387, by rfl⟩ : syracuseStep 1279183 = 1918775) B1918775
theorem B16418051 : Blo 1136633 16418051 := bstep (se 1 (by rfl) ⟨12313538, by rfl⟩ : syracuseStep 16418051 = 24627077) B24627077
theorem B1705307 : Blo 1136633 1705307 := bstep (se 1 (by rfl) ⟨1278980, by rfl⟩ : syracuseStep 1705307 = 2557961) B2557961
theorem B1705583 : Blo 1136633 1705583 := bstep (se 1 (by rfl) ⟨1279187, by rfl⟩ : syracuseStep 1705583 = 2558375) B2558375
theorem B5768819 : Blo 1136633 5768819 := bstep (se 1 (by rfl) ⟨4326614, by rfl⟩ : syracuseStep 5768819 = 8653229) B8653229
theorem B5834393 : Blo 1136633 5834393 := bstep (se 2 (by rfl) ⟨2187897, by rfl⟩ : syracuseStep 5834393 = 4375795) B4375795
theorem B1705655 : Blo 1136633 1705655 := bstep (se 1 (by rfl) ⟨1279241, by rfl⟩ : syracuseStep 1705655 = 2558483) B2558483
theorem B1705691 : Blo 1136633 1705691 := bstep (se 1 (by rfl) ⟨1279268, by rfl⟩ : syracuseStep 1705691 = 2558537) B2558537
theorem B2557727 : Blo 1136633 2557727 := bstep (se 1 (by rfl) ⟨1918295, by rfl⟩ : syracuseStep 2557727 = 3836591) B3836591
theorem B3245953 : Blo 1136633 3245953 := bstep (se 2 (by rfl) ⟨1217232, by rfl⟩ : syracuseStep 3245953 = 2434465) B2434465
theorem B1705865 : Blo 1136633 1705865 := bstep (se 2 (by rfl) ⟨639699, by rfl⟩ : syracuseStep 1705865 = 1279399) B1279399
theorem B8652743 : Blo 1136633 8652743 := bstep (se 1 (by rfl) ⟨6489557, by rfl⟩ : syracuseStep 8652743 = 12979115) B12979115
theorem B1705967 : Blo 1136633 1705967 := bstep (se 1 (by rfl) ⟨1279475, by rfl⟩ : syracuseStep 1705967 = 2558951) B2558951
theorem B2557943 : Blo 1136633 2557943 := bstep (se 1 (by rfl) ⟨1918457, by rfl⟩ : syracuseStep 2557943 = 3836915) B3836915
theorem B1280155 : Blo 1136633 1280155 := bstep (se 1 (by rfl) ⟨960116, by rfl⟩ : syracuseStep 1280155 = 1920233) B1920233
theorem B1280191 : Blo 1136633 1280191 := bstep (se 1 (by rfl) ⟨960143, by rfl⟩ : syracuseStep 1280191 = 1920287) B1920287
theorem B19433681 : Blo 1136633 19433681 := bstep (se 2 (by rfl) ⟨7287630, by rfl⟩ : syracuseStep 19433681 = 14575261) B14575261
theorem B1706219 : Blo 1136633 1706219 := bstep (se 1 (by rfl) ⟨1279664, by rfl⟩ : syracuseStep 1706219 = 2559329) B2559329
theorem B1706279 : Blo 1136633 1706279 := bstep (se 1 (by rfl) ⟨1279709, by rfl⟩ : syracuseStep 1706279 = 2559419) B2559419
theorem B2165039 : Blo 1136633 2165039 := bstep (se 1 (by rfl) ⟨1623779, by rfl⟩ : syracuseStep 2165039 = 3247559) B3247559
theorem B6162779 : Blo 1136633 6162779 := bstep (se 1 (by rfl) ⟨4622084, by rfl⟩ : syracuseStep 6162779 = 9244169) B9244169
theorem B2558303 : Blo 1136633 2558303 := bstep (se 1 (by rfl) ⟨1918727, by rfl⟩ : syracuseStep 2558303 = 3837455) B3837455
theorem B1706363 : Blo 1136633 1706363 := bstep (se 1 (by rfl) ⟨1279772, by rfl⟩ : syracuseStep 1706363 = 2559545) B2559545
theorem B5769629 : Blo 1136633 5769629 := bstep (se 3 (by rfl) ⟨1081805, by rfl⟩ : syracuseStep 5769629 = 2163611) B2163611
theorem B3836321 : Blo 1136633 3836321 := bstep (se 2 (by rfl) ⟨1438620, by rfl⟩ : syracuseStep 3836321 = 2877241) B2877241
theorem B2886151 : Blo 1136633 2886151 := bstep (se 1 (by rfl) ⟨2164613, by rfl⟩ : syracuseStep 2886151 = 4329227) B4329227
theorem B1706633 : Blo 1136633 1706633 := bstep (se 2 (by rfl) ⟨639987, by rfl⟩ : syracuseStep 1706633 = 1279975) B1279975
theorem B1706807 : Blo 1136633 1706807 := bstep (se 1 (by rfl) ⟨1280105, by rfl⟩ : syracuseStep 1706807 = 2560211) B2560211
theorem B2886455 : Blo 1136633 2886455 := bstep (se 1 (by rfl) ⟨2164841, by rfl⟩ : syracuseStep 2886455 = 4329683) B4329683
theorem B1706843 : Blo 1136633 1706843 := bstep (se 1 (by rfl) ⟨1280132, by rfl⟩ : syracuseStep 1706843 = 2560265) B2560265
theorem B4328423 : Blo 1136633 4328423 := bstep (se 1 (by rfl) ⟨3246317, by rfl⟩ : syracuseStep 4328423 = 6492635) B6492635
theorem B1706987 : Blo 1136633 1706987 := bstep (se 1 (by rfl) ⟨1280240, by rfl⟩ : syracuseStep 1706987 = 2560481) B2560481
theorem B2559023 : Blo 1136633 2559023 := bstep (se 1 (by rfl) ⟨1919267, by rfl⟩ : syracuseStep 2559023 = 3838535) B3838535
theorem B1707191 : Blo 1136633 1707191 := bstep (se 1 (by rfl) ⟨1280393, by rfl⟩ : syracuseStep 1707191 = 2560787) B2560787
theorem B5770439 : Blo 1136633 5770439 := bstep (se 1 (by rfl) ⟨4327829, by rfl⟩ : syracuseStep 5770439 = 8655659) B8655659
theorem B2559311 : Blo 1136633 2559311 := bstep (se 1 (by rfl) ⟨1919483, by rfl⟩ : syracuseStep 2559311 = 3838967) B3838967
theorem B1707431 : Blo 1136633 1707431 := bstep (se 1 (by rfl) ⟨1280573, by rfl⟩ : syracuseStep 1707431 = 2561147) B2561147
theorem B2559401 : Blo 1136633 2559401 := bstep (se 2 (by rfl) ⟨959775, by rfl⟩ : syracuseStep 2559401 = 1919551) B1919551
theorem B1707515 : Blo 1136633 1707515 := bstep (se 1 (by rfl) ⟨1280636, by rfl⟩ : syracuseStep 1707515 = 2561273) B2561273
theorem B1707611 : Blo 1136633 1707611 := bstep (se 1 (by rfl) ⟨1280708, by rfl⟩ : syracuseStep 1707611 = 2561417) B2561417
theorem B1707695 : Blo 1136633 1707695 := bstep (se 1 (by rfl) ⟨1280771, by rfl⟩ : syracuseStep 1707695 = 2561543) B2561543
theorem B1707815 : Blo 1136633 1707815 := bstep (se 1 (by rfl) ⟨1280861, by rfl⟩ : syracuseStep 1707815 = 2561723) B2561723
theorem B1707899 : Blo 1136633 1707899 := bstep (se 1 (by rfl) ⟨1280924, by rfl⟩ : syracuseStep 1707899 = 2561849) B2561849
theorem B2559887 : Blo 1136633 2559887 := bstep (se 1 (by rfl) ⟨1919915, by rfl⟩ : syracuseStep 2559887 = 3839831) B3839831
theorem B9244691 : Blo 1136633 9244691 := bstep (se 1 (by rfl) ⟨6933518, by rfl⟩ : syracuseStep 9244691 = 13867037) B13867037
theorem B1282279 : Blo 1136633 1282279 := bstep (se 1 (by rfl) ⟨961709, by rfl⟩ : syracuseStep 1282279 = 1923419) B1923419
theorem B1708319 : Blo 1136633 1708319 := bstep (se 1 (by rfl) ⟨1281239, by rfl⟩ : syracuseStep 1708319 = 2562479) B2562479
theorem B1708343 : Blo 1136633 1708343 := bstep (se 1 (by rfl) ⟨1281257, by rfl⟩ : syracuseStep 1708343 = 2562515) B2562515
theorem B3838319 : Blo 1136633 3838319 := bstep (se 1 (by rfl) ⟨2878739, by rfl⟩ : syracuseStep 3838319 = 5757479) B5757479
theorem B1708415 : Blo 1136633 1708415 := bstep (se 1 (by rfl) ⟨1281311, by rfl⟩ : syracuseStep 1708415 = 2562623) B2562623
theorem B1708487 : Blo 1136633 1708487 := bstep (se 1 (by rfl) ⟨1281365, by rfl⟩ : syracuseStep 1708487 = 2562731) B2562731
theorem B5771735 : Blo 1136633 5771735 := bstep (se 1 (by rfl) ⟨4328801, by rfl⟩ : syracuseStep 5771735 = 8657603) B8657603
theorem B11670095 : Blo 1136633 11670095 := bstep (se 1 (by rfl) ⟨8752571, by rfl⟩ : syracuseStep 11670095 = 17505143) B17505143
theorem B2560607 : Blo 1136633 2560607 := bstep (se 1 (by rfl) ⟨1920455, by rfl⟩ : syracuseStep 2560607 = 3840911) B3840911
theorem B1708841 : Blo 1136633 1708841 := bstep (se 2 (by rfl) ⟨640815, by rfl⟩ : syracuseStep 1708841 = 1281631) B1281631
theorem B1708847 : Blo 1136633 1708847 := bstep (se 1 (by rfl) ⟨1281635, by rfl⟩ : syracuseStep 1708847 = 2563271) B2563271
theorem B1282927 : Blo 1136633 1282927 := bstep (se 1 (by rfl) ⟨962195, by rfl⟩ : syracuseStep 1282927 = 1924391) B1924391
theorem B1708967 : Blo 1136633 1708967 := bstep (se 1 (by rfl) ⟨1281725, by rfl⟩ : syracuseStep 1708967 = 2563451) B2563451
theorem B1709051 : Blo 1136633 1709051 := bstep (se 1 (by rfl) ⟨1281788, by rfl⟩ : syracuseStep 1709051 = 2563577) B2563577
theorem B1709111 : Blo 1136633 1709111 := bstep (se 1 (by rfl) ⟨1281833, by rfl⟩ : syracuseStep 1709111 = 2563667) B2563667
theorem B1709231 : Blo 1136633 1709231 := bstep (se 1 (by rfl) ⟨1281923, by rfl⟩ : syracuseStep 1709231 = 2563847) B2563847
theorem B1217711 : Blo 1136633 1217711 := bstep (se 1 (by rfl) ⟨913283, by rfl⟩ : syracuseStep 1217711 = 1826567) B1826567
theorem B2561435 : Blo 1136633 2561435 := bstep (se 1 (by rfl) ⟨1921076, by rfl⟩ : syracuseStep 2561435 = 3842153) B3842153
theorem B1709639 : Blo 1136633 1709639 := bstep (se 1 (by rfl) ⟨1282229, by rfl⟩ : syracuseStep 1709639 = 2564459) B2564459
theorem B1709735 : Blo 1136633 1709735 := bstep (se 1 (by rfl) ⟨1282301, by rfl⟩ : syracuseStep 1709735 = 2564603) B2564603
theorem B3839723 : Blo 1136633 3839723 := bstep (se 1 (by rfl) ⟨2879792, by rfl⟩ : syracuseStep 3839723 = 5759585) B5759585
theorem B1709819 : Blo 1136633 1709819 := bstep (se 1 (by rfl) ⟨1282364, by rfl⟩ : syracuseStep 1709819 = 2564729) B2564729
theorem B1709855 : Blo 1136633 1709855 := bstep (se 1 (by rfl) ⟨1282391, by rfl⟩ : syracuseStep 1709855 = 2564783) B2564783
theorem B1709903 : Blo 1136633 1709903 := bstep (se 1 (by rfl) ⟨1282427, by rfl⟩ : syracuseStep 1709903 = 2564855) B2564855
theorem B1710023 : Blo 1136633 1710023 := bstep (se 1 (by rfl) ⟨1282517, by rfl⟩ : syracuseStep 1710023 = 2565035) B2565035
theorem B3643355 : Blo 1136633 3643355 := bstep (se 1 (by rfl) ⟨2732516, by rfl⟩ : syracuseStep 3643355 = 5465033) B5465033
theorem B2562011 : Blo 1136633 2562011 := bstep (se 1 (by rfl) ⟨1921508, by rfl⟩ : syracuseStep 2562011 = 3843017) B3843017
theorem B33265637 : Blo 1136633 33265637 := bstep (se 4 (by rfl) ⟨3118653, by rfl⟩ : syracuseStep 33265637 = 6237307) B6237307
theorem B3839993 : Blo 1136633 3839993 := bstep (se 2 (by rfl) ⟨1439997, by rfl⟩ : syracuseStep 3839993 = 2879995) B2879995
theorem B28121165 : Blo 1136633 28121165 := bstep (se 3 (by rfl) ⟨5272718, by rfl⟩ : syracuseStep 28121165 = 10545437) B10545437
theorem B2431073 : Blo 1136633 2431073 := bstep (se 2 (by rfl) ⟨911652, by rfl⟩ : syracuseStep 2431073 = 1823305) B1823305
theorem B3643535 : Blo 1136633 3643535 := bstep (se 1 (by rfl) ⟨2732651, by rfl⟩ : syracuseStep 3643535 = 5465303) B5465303
theorem B2562191 : Blo 1136633 2562191 := bstep (se 1 (by rfl) ⟨1921643, by rfl⟩ : syracuseStep 2562191 = 3843287) B3843287
theorem B3840155 : Blo 1136633 3840155 := bstep (se 1 (by rfl) ⟨2880116, by rfl⟩ : syracuseStep 3840155 = 5760233) B5760233
theorem B2562209 : Blo 1136633 2562209 := bstep (se 2 (by rfl) ⟨960828, by rfl⟩ : syracuseStep 2562209 = 1921657) B1921657
theorem B2562281 : Blo 1136633 2562281 := bstep (se 2 (by rfl) ⟨960855, by rfl⟩ : syracuseStep 2562281 = 1921711) B1921711
theorem B3840263 : Blo 1136633 3840263 := bstep (se 1 (by rfl) ⟨2880197, by rfl⟩ : syracuseStep 3840263 = 5760395) B5760395
theorem B1710377 : Blo 1136633 1710377 := bstep (se 2 (by rfl) ⟨641391, by rfl⟩ : syracuseStep 1710377 = 1282783) B1282783
theorem B1710383 : Blo 1136633 1710383 := bstep (se 1 (by rfl) ⟨1282787, by rfl⟩ : syracuseStep 1710383 = 2565575) B2565575
theorem B1710623 : Blo 1136633 1710623 := bstep (se 1 (by rfl) ⟨1282967, by rfl⟩ : syracuseStep 1710623 = 2565935) B2565935
theorem B35035895 : Blo 1136633 35035895 := bstep (se 1 (by rfl) ⟨26276921, by rfl⟩ : syracuseStep 35035895 = 52553843) B52553843
theorem B5774327 : Blo 1136633 5774327 := bstep (se 1 (by rfl) ⟨4330745, by rfl⟩ : syracuseStep 5774327 = 8661491) B8661491
theorem B32873687 : Blo 1136633 32873687 := bstep (se 1 (by rfl) ⟨24655265, by rfl⟩ : syracuseStep 32873687 = 49310531) B49310531
theorem B3841289 : Blo 1136633 3841289 := bstep (se 2 (by rfl) ⟨1440483, by rfl⟩ : syracuseStep 3841289 = 2880967) B2880967
theorem B12328325 : Blo 1136633 12328325 := bstep (se 4 (by rfl) ⟨1155780, by rfl⟩ : syracuseStep 12328325 = 2311561) B2311561
theorem B2432423 : Blo 1136633 2432423 := bstep (se 1 (by rfl) ⟨1824317, by rfl⟩ : syracuseStep 2432423 = 3648635) B3648635
theorem B2563559 : Blo 1136633 2563559 := bstep (se 1 (by rfl) ⟨1922669, by rfl⟩ : syracuseStep 2563559 = 3845339) B3845339
theorem B3645175 : Blo 1136633 3645175 := bstep (se 1 (by rfl) ⟨2733881, by rfl⟩ : syracuseStep 3645175 = 5467763) B5467763
theorem B2564135 : Blo 1136633 2564135 := bstep (se 1 (by rfl) ⟨1923101, by rfl⟩ : syracuseStep 2564135 = 3846203) B3846203
theorem B2564315 : Blo 1136633 2564315 := bstep (se 1 (by rfl) ⟨1923236, by rfl⟩ : syracuseStep 2564315 = 3846473) B3846473
theorem B3842423 : Blo 1136633 3842423 := bstep (se 1 (by rfl) ⟨2881817, by rfl⟩ : syracuseStep 3842423 = 5763635) B5763635
theorem B2564585 : Blo 1136633 2564585 := bstep (se 2 (by rfl) ⟨961719, by rfl⟩ : syracuseStep 2564585 = 1923439) B1923439
theorem B194585159 : Blo 1136633 194585159 := bstep (se 1 (by rfl) ⟨145938869, by rfl⟩ : syracuseStep 194585159 = 291877739) B291877739
theorem B2564873 : Blo 1136633 2564873 := bstep (se 2 (by rfl) ⟨961827, by rfl⟩ : syracuseStep 2564873 = 1923655) B1923655
theorem B1581935 : Blo 1136633 1581935 := bstep (se 1 (by rfl) ⟨1186451, by rfl⟩ : syracuseStep 1581935 = 2372903) B2372903
theorem B12952871 : Blo 1136633 12952871 := bstep (se 1 (by rfl) ⟨9714653, by rfl⟩ : syracuseStep 12952871 = 19429307) B19429307
theorem B2565449 : Blo 1136633 2565449 := bstep (se 2 (by rfl) ⟨962043, by rfl⟩ : syracuseStep 2565449 = 1924087) B1924087
theorem B3646891 : Blo 1136633 3646891 := bstep (se 1 (by rfl) ⟨2735168, by rfl⟩ : syracuseStep 3646891 = 5470337) B5470337
theorem B3843503 : Blo 1136633 3843503 := bstep (se 1 (by rfl) ⟨2882627, by rfl⟩ : syracuseStep 3843503 = 5765255) B5765255
theorem B6563321 : Blo 1136633 6563321 := bstep (se 2 (by rfl) ⟨2461245, by rfl⟩ : syracuseStep 6563321 = 4922491) B4922491
theorem B3286649 : Blo 1136633 3286649 := bstep (se 2 (by rfl) ⟨1232493, by rfl⟩ : syracuseStep 3286649 = 2464987) B2464987
theorem B3843881 : Blo 1136633 3843881 := bstep (se 2 (by rfl) ⟨1441455, by rfl⟩ : syracuseStep 3843881 = 2882911) B2882911
theorem B7284815 : Blo 1136633 7284815 := bstep (se 1 (by rfl) ⟨5463611, by rfl⟩ : syracuseStep 7284815 = 10927223) B10927223
theorem B73803869 : Blo 1136633 73803869 := bstep (se 3 (by rfl) ⟨13838225, by rfl⟩ : syracuseStep 73803869 = 27676451) B27676451
theorem B2304295 : Blo 1136633 2304295 := bstep (se 1 (by rfl) ⟨1728221, by rfl⟩ : syracuseStep 2304295 = 3456443) B3456443
theorem B3648007 : Blo 1136633 3648007 := bstep (se 1 (by rfl) ⟨2736005, by rfl⟩ : syracuseStep 3648007 = 5472011) B5472011
theorem B3648071 : Blo 1136633 3648071 := bstep (se 1 (by rfl) ⟨2736053, by rfl⟩ : syracuseStep 3648071 = 5472107) B5472107
theorem B4861565 : Blo 1136633 4861565 := bstep (se 3 (by rfl) ⟨911543, by rfl⟩ : syracuseStep 4861565 = 1823087) B1823087
theorem B3846095 : Blo 1136633 3846095 := bstep (se 1 (by rfl) ⟨2884571, by rfl⟩ : syracuseStep 3846095 = 5769143) B5769143
theorem B7286993 : Blo 1136633 7286993 := bstep (se 2 (by rfl) ⟨2732622, by rfl⟩ : syracuseStep 7286993 = 5465245) B5465245
theorem B3846527 : Blo 1136633 3846527 := bstep (se 1 (by rfl) ⟨2884895, by rfl⟩ : syracuseStep 3846527 = 5769791) B5769791
theorem B16429463 : Blo 1136633 16429463 := bstep (se 1 (by rfl) ⟨12322097, by rfl⟩ : syracuseStep 16429463 = 24644195) B24644195
theorem B1618375 : Blo 1136633 1618375 := bstep (se 1 (by rfl) ⟨1213781, by rfl⟩ : syracuseStep 1618375 = 2427563) B2427563
theorem B16396829 : Blo 1136633 16396829 := bstep (se 3 (by rfl) ⟨3074405, by rfl⟩ : syracuseStep 16396829 = 6148811) B6148811
theorem B4108895 : Blo 1136633 4108895 := bstep (se 1 (by rfl) ⟨3081671, by rfl⟩ : syracuseStep 4108895 = 6163343) B6163343
theorem B18494563 : Blo 1136633 18494563 := bstep (se 1 (by rfl) ⟨13870922, by rfl⟩ : syracuseStep 18494563 = 27741845) B27741845
theorem B1848425 : Blo 1136633 1848425 := bstep (se 2 (by rfl) ⟨693159, by rfl⟩ : syracuseStep 1848425 = 1386319) B1386319
theorem B5191379 : Blo 1136633 5191379 := bstep (se 1 (by rfl) ⟨3893534, by rfl⟩ : syracuseStep 5191379 = 7787069) B7787069
theorem B3847931 : Blo 1136633 3847931 := bstep (se 1 (by rfl) ⟨2885948, by rfl⟩ : syracuseStep 3847931 = 5771897) B5771897
theorem B6567743 : Blo 1136633 6567743 := bstep (se 1 (by rfl) ⟨4925807, by rfl⟩ : syracuseStep 6567743 = 9851615) B9851615
theorem B3848093 : Blo 1136633 3848093 := bstep (se 3 (by rfl) ⟨721517, by rfl⟩ : syracuseStep 3848093 = 1443035) B1443035
theorem B10926373 : Blo 1136633 10926373 := bstep (se 4 (by rfl) ⟨1024347, by rfl⟩ : syracuseStep 10926373 = 2048695) B2048695
theorem B23378219 : Blo 1136633 23378219 := bstep (se 1 (by rfl) ⟨17533664, by rfl⟩ : syracuseStep 23378219 = 35067329) B35067329
theorem B1620271 : Blo 1136633 1620271 := bstep (se 1 (by rfl) ⟨1215203, by rfl⟩ : syracuseStep 1620271 = 2430407) B2430407
theorem B1849883 : Blo 1136633 1849883 := bstep (se 1 (by rfl) ⟨1387412, by rfl⟩ : syracuseStep 1849883 = 2774825) B2774825
theorem B3652249 : Blo 1136633 3652249 := bstep (se 2 (by rfl) ⟨1369593, by rfl⟩ : syracuseStep 3652249 = 2739187) B2739187
theorem B3849065 : Blo 1136633 3849065 := bstep (se 2 (by rfl) ⟨1443399, by rfl⟩ : syracuseStep 3849065 = 2886799) B2886799
theorem B3849119 : Blo 1136633 3849119 := bstep (se 1 (by rfl) ⟨2886839, by rfl⟩ : syracuseStep 3849119 = 5773679) B5773679
theorem B19446803 : Blo 1136633 19446803 := bstep (se 1 (by rfl) ⟨14585102, by rfl⟩ : syracuseStep 19446803 = 29170205) B29170205
theorem B1621063 : Blo 1136633 1621063 := bstep (se 1 (by rfl) ⟨1215797, by rfl⟩ : syracuseStep 1621063 = 2431595) B2431595
theorem B2735707 : Blo 1136633 2735707 := bstep (se 1 (by rfl) ⟨2051780, by rfl⟩ : syracuseStep 2735707 = 4103561) B4103561
theorem B27737963 : Blo 1136633 27737963 := bstep (se 1 (by rfl) ⟨20803472, by rfl⟩ : syracuseStep 27737963 = 41606945) B41606945
theorem B1621883 : Blo 1136633 1621883 := bstep (se 1 (by rfl) ⟨1216412, by rfl⟩ : syracuseStep 1621883 = 2432825) B2432825
theorem B1753577 : Blo 1136633 1753577 := bstep (se 2 (by rfl) ⟨657591, by rfl⟩ : syracuseStep 1753577 = 1315183) B1315183
theorem B1622521 : Blo 1136633 1622521 := bstep (se 2 (by rfl) ⟨608445, by rfl⟩ : syracuseStep 1622521 = 1216891) B1216891
theorem B119751371 : Blo 1136633 119751371 := bstep (se 1 (by rfl) ⟨89813528, by rfl⟩ : syracuseStep 119751371 = 179627057) B179627057
theorem B2081543 : Blo 1136633 2081543 := bstep (se 1 (by rfl) ⟨1561157, by rfl⟩ : syracuseStep 2081543 = 3122315) B3122315
theorem B49922831 : Blo 1136633 49922831 := bstep (se 1 (by rfl) ⟨37442123, by rfl⟩ : syracuseStep 49922831 = 74884247) B74884247
theorem B13124753 : Blo 1136633 13124753 := bstep (se 2 (by rfl) ⟨4921782, by rfl⟩ : syracuseStep 13124753 = 9843565) B9843565
theorem B1918127 : Blo 1136633 1918127 := bstep (se 1 (by rfl) ⟨1438595, by rfl⟩ : syracuseStep 1918127 = 2877191) B2877191
theorem B1918363 : Blo 1136633 1918363 := bstep (se 1 (by rfl) ⟨1438772, by rfl⟩ : syracuseStep 1918363 = 2877545) B2877545
theorem B2737775 : Blo 1136633 2737775 := bstep (se 1 (by rfl) ⟨2053331, by rfl⟩ : syracuseStep 2737775 = 4106663) B4106663
theorem B1918687 : Blo 1136633 1918687 := bstep (se 1 (by rfl) ⟨1439015, by rfl⟩ : syracuseStep 1918687 = 2878031) B2878031
theorem B1459963 : Blo 1136633 1459963 := bstep (se 1 (by rfl) ⟨1094972, by rfl⟩ : syracuseStep 1459963 = 2189945) B2189945
theorem B1624007 : Blo 1136633 1624007 := bstep (se 1 (by rfl) ⟨1218005, by rfl⟩ : syracuseStep 1624007 = 2436011) B2436011
theorem B1919119 : Blo 1136633 1919119 := bstep (se 1 (by rfl) ⟨1439339, by rfl⟩ : syracuseStep 1919119 = 2878679) B2878679
theorem B4212971 : Blo 1136633 4212971 := bstep (se 1 (by rfl) ⟨3159728, by rfl⟩ : syracuseStep 4212971 = 6319457) B6319457
theorem B4868399 : Blo 1136633 4868399 := bstep (se 1 (by rfl) ⟨3651299, by rfl⟩ : syracuseStep 4868399 = 7302599) B7302599
theorem B55494989 : Blo 1136633 55494989 := bstep (se 3 (by rfl) ⟨10405310, by rfl⟩ : syracuseStep 55494989 = 20810621) B20810621
theorem B62311457 : Blo 1136633 62311457 := bstep (se 2 (by rfl) ⟨23366796, by rfl⟩ : syracuseStep 62311457 = 46733593) B46733593
theorem B1920071 : Blo 1136633 1920071 := bstep (se 1 (by rfl) ⟨1440053, by rfl⟩ : syracuseStep 1920071 = 2880107) B2880107
theorem B1920503 : Blo 1136633 1920503 := bstep (se 1 (by rfl) ⟨1440377, by rfl⟩ : syracuseStep 1920503 = 2880755) B2880755
theorem B46681697 : Blo 1136633 46681697 := bstep (se 2 (by rfl) ⟨17505636, by rfl⟩ : syracuseStep 46681697 = 35011273) B35011273
theorem B5754563 : Blo 1136633 5754563 := bstep (se 1 (by rfl) ⟨4315922, by rfl⟩ : syracuseStep 5754563 = 8631845) B8631845
theorem B7884551 : Blo 1136633 7884551 := bstep (se 1 (by rfl) ⟨5913413, by rfl⟩ : syracuseStep 7884551 = 11826827) B11826827
theorem B24596369 : Blo 1136633 24596369 := bstep (se 2 (by rfl) ⟨9223638, by rfl⟩ : syracuseStep 24596369 = 18447277) B18447277
theorem B2052011 : Blo 1136633 2052011 := bstep (se 1 (by rfl) ⟨1539008, by rfl⟩ : syracuseStep 2052011 = 3078017) B3078017
theorem B3461503 : Blo 1136633 3461503 := bstep (se 1 (by rfl) ⟨2596127, by rfl⟩ : syracuseStep 3461503 = 5192255) B5192255
theorem B3461591 : Blo 1136633 3461591 := bstep (se 1 (by rfl) ⟨2596193, by rfl⟩ : syracuseStep 3461591 = 5192387) B5192387
theorem B1921529 : Blo 1136633 1921529 := bstep (se 2 (by rfl) ⟨720573, by rfl⟩ : syracuseStep 1921529 = 1441147) B1441147
theorem B2052703 : Blo 1136633 2052703 := bstep (se 1 (by rfl) ⟨1539527, by rfl⟩ : syracuseStep 2052703 = 3079055) B3079055
theorem B1921799 : Blo 1136633 1921799 := bstep (se 1 (by rfl) ⟨1441349, by rfl⟩ : syracuseStep 1921799 = 2882699) B2882699
theorem B1922879 : Blo 1136633 1922879 := bstep (se 1 (by rfl) ⟨1442159, by rfl⟩ : syracuseStep 1922879 = 2884319) B2884319
theorem B1922953 : Blo 1136633 1922953 := bstep (se 2 (by rfl) ⟨721107, by rfl⟩ : syracuseStep 1922953 = 1442215) B1442215
theorem B2054087 : Blo 1136633 2054087 := bstep (se 1 (by rfl) ⟨1540565, by rfl⟩ : syracuseStep 2054087 = 3081131) B3081131
theorem B6150239 : Blo 1136633 6150239 := bstep (se 1 (by rfl) ⟨4612679, by rfl⟩ : syracuseStep 6150239 = 9225359) B9225359
theorem B1136795 : Blo 1136633 1136795 := bstep (se 1 (by rfl) ⟨852596, by rfl⟩ : syracuseStep 1136795 = 1705193) B1705193
theorem B1136831 : Blo 1136633 1136831 := bstep (se 1 (by rfl) ⟨852623, by rfl⟩ : syracuseStep 1136831 = 1705247) B1705247
theorem B21911795 : Blo 1136633 21911795 := bstep (se 1 (by rfl) ⟨16433846, by rfl⟩ : syracuseStep 21911795 = 32867693) B32867693
theorem B1136943 : Blo 1136633 1136943 := bstep (se 1 (by rfl) ⟨852707, by rfl⟩ : syracuseStep 1136943 = 1705415) B1705415
theorem B1923385 : Blo 1136633 1923385 := bstep (se 2 (by rfl) ⟨721269, by rfl⟩ : syracuseStep 1923385 = 1442539) B1442539
theorem B6576491 : Blo 1136633 6576491 := bstep (se 1 (by rfl) ⟨4932368, by rfl⟩ : syracuseStep 6576491 = 9864737) B9864737
theorem B1137179 : Blo 1136633 1137179 := bstep (se 1 (by rfl) ⟨852884, by rfl⟩ : syracuseStep 1137179 = 1705769) B1705769
theorem B1137183 : Blo 1136633 1137183 := bstep (se 1 (by rfl) ⟨852887, by rfl⟩ : syracuseStep 1137183 = 1705775) B1705775
theorem B9230935 : Blo 1136633 9230935 := bstep (se 1 (by rfl) ⟨6923201, by rfl⟩ : syracuseStep 9230935 = 13846403) B13846403
theorem B1923689 : Blo 1136633 1923689 := bstep (se 2 (by rfl) ⟨721383, by rfl⟩ : syracuseStep 1923689 = 1442767) B1442767
theorem B1137499 : Blo 1136633 1137499 := bstep (se 1 (by rfl) ⟨853124, by rfl⟩ : syracuseStep 1137499 = 1706249) B1706249
theorem B7297883 : Blo 1136633 7297883 := bstep (se 1 (by rfl) ⟨5473412, by rfl⟩ : syracuseStep 7297883 = 10946825) B10946825
theorem B1137567 : Blo 1136633 1137567 := bstep (se 1 (by rfl) ⟨853175, by rfl⟩ : syracuseStep 1137567 = 1706351) B1706351
theorem B4316105 : Blo 1136633 4316105 := bstep (se 2 (by rfl) ⟨1618539, by rfl⟩ : syracuseStep 4316105 = 3237079) B3237079
theorem B1137711 : Blo 1136633 1137711 := bstep (se 1 (by rfl) ⟨853283, by rfl⟩ : syracuseStep 1137711 = 1706567) B1706567
theorem B1137735 : Blo 1136633 1137735 := bstep (se 1 (by rfl) ⟨853301, by rfl⟩ : syracuseStep 1137735 = 1706603) B1706603
theorem B6478987 : Blo 1136633 6478987 := bstep (se 1 (by rfl) ⟨4859240, by rfl⟩ : syracuseStep 6478987 = 9718481) B9718481
theorem B3464375 : Blo 1136633 3464375 := bstep (se 1 (by rfl) ⟨2598281, by rfl⟩ : syracuseStep 3464375 = 5196563) B5196563
theorem B1137887 : Blo 1136633 1137887 := bstep (se 1 (by rfl) ⟨853415, by rfl⟩ : syracuseStep 1137887 = 1706831) B1706831
theorem B1924519 : Blo 1136633 1924519 := bstep (se 1 (by rfl) ⟨1443389, by rfl⟩ : syracuseStep 1924519 = 2886779) B2886779
theorem B1138151 : Blo 1136633 1138151 := bstep (se 1 (by rfl) ⟨853613, by rfl⟩ : syracuseStep 1138151 = 1707227) B1707227
theorem B1924681 : Blo 1136633 1924681 := bstep (se 2 (by rfl) ⟨721755, by rfl⟩ : syracuseStep 1924681 = 1443511) B1443511
theorem B1138267 : Blo 1136633 1138267 := bstep (se 1 (by rfl) ⟨853700, by rfl⟩ : syracuseStep 1138267 = 1707401) B1707401
theorem B1924715 : Blo 1136633 1924715 := bstep (se 1 (by rfl) ⟨1443536, by rfl⟩ : syracuseStep 1924715 = 2887073) B2887073
theorem B5758775 : Blo 1136633 5758775 := bstep (se 1 (by rfl) ⟨4319081, by rfl⟩ : syracuseStep 5758775 = 8638163) B8638163
theorem B1138503 : Blo 1136633 1138503 := bstep (se 1 (by rfl) ⟨853877, by rfl⟩ : syracuseStep 1138503 = 1707755) B1707755
theorem B1138655 : Blo 1136633 1138655 := bstep (se 1 (by rfl) ⟨853991, by rfl⟩ : syracuseStep 1138655 = 1707983) B1707983
theorem B3891239 : Blo 1136633 3891239 := bstep (se 1 (by rfl) ⟨2918429, by rfl⟩ : syracuseStep 3891239 = 5836859) B5836859
theorem B1138919 : Blo 1136633 1138919 := bstep (se 1 (by rfl) ⟨854189, by rfl⟩ : syracuseStep 1138919 = 1708379) B1708379
theorem B5464417 : Blo 1136633 5464417 := bstep (se 2 (by rfl) ⟨2049156, by rfl⟩ : syracuseStep 5464417 = 4098313) B4098313
theorem B6152573 : Blo 1136633 6152573 := bstep (se 3 (by rfl) ⟨1153607, by rfl⟩ : syracuseStep 6152573 = 2307215) B2307215
theorem B1139071 : Blo 1136633 1139071 := bstep (se 1 (by rfl) ⟨854303, by rfl⟩ : syracuseStep 1139071 = 1708607) B1708607
theorem B1139151 : Blo 1136633 1139151 := bstep (se 1 (by rfl) ⟨854363, by rfl⟩ : syracuseStep 1139151 = 1708727) B1708727
theorem B140206625 : Blo 1136633 140206625 := bstep (se 2 (by rfl) ⟨52577484, by rfl⟩ : syracuseStep 140206625 = 105154969) B105154969
theorem B1139303 : Blo 1136633 1139303 := bstep (se 1 (by rfl) ⟨854477, by rfl⟩ : syracuseStep 1139303 = 1708955) B1708955
theorem B6480719 : Blo 1136633 6480719 := bstep (se 1 (by rfl) ⟨4860539, by rfl⟩ : syracuseStep 6480719 = 9721079) B9721079
theorem B1139567 : Blo 1136633 1139567 := bstep (se 1 (by rfl) ⟨854675, by rfl⟩ : syracuseStep 1139567 = 1709351) B1709351
theorem B1139623 : Blo 1136633 1139623 := bstep (se 1 (by rfl) ⟨854717, by rfl⟩ : syracuseStep 1139623 = 1709435) B1709435
theorem B12968909 : Blo 1136633 12968909 := bstep (se 3 (by rfl) ⟨2431670, by rfl⟩ : syracuseStep 12968909 = 4863341) B4863341
theorem B3236851 : Blo 1136633 3236851 := bstep (se 1 (by rfl) ⟨2427638, by rfl⟩ : syracuseStep 3236851 = 4855277) B4855277
theorem B1139707 : Blo 1136633 1139707 := bstep (se 1 (by rfl) ⟨854780, by rfl⟩ : syracuseStep 1139707 = 1709561) B1709561
theorem B1139775 : Blo 1136633 1139775 := bstep (se 1 (by rfl) ⟨854831, by rfl⟩ : syracuseStep 1139775 = 1709663) B1709663
theorem B1139919 : Blo 1136633 1139919 := bstep (se 1 (by rfl) ⟨854939, by rfl⟩ : syracuseStep 1139919 = 1709879) B1709879
theorem B98493731 : Blo 1136633 98493731 := bstep (se 1 (by rfl) ⟨73870298, by rfl⟩ : syracuseStep 98493731 = 147740597) B147740597
theorem B8316265 : Blo 1136633 8316265 := bstep (se 2 (by rfl) ⟨3118599, by rfl⟩ : syracuseStep 8316265 = 6237199) B6237199
theorem B1140123 : Blo 1136633 1140123 := bstep (se 1 (by rfl) ⟨855092, by rfl⟩ : syracuseStep 1140123 = 1710185) B1710185
theorem B7300601 : Blo 1136633 7300601 := bstep (se 2 (by rfl) ⟨2737725, by rfl⟩ : syracuseStep 7300601 = 5475451) B5475451
theorem B1140335 : Blo 1136633 1140335 := bstep (se 1 (by rfl) ⟨855251, by rfl⟩ : syracuseStep 1140335 = 1710503) B1710503
theorem B1140391 : Blo 1136633 1140391 := bstep (se 1 (by rfl) ⟨855293, by rfl⟩ : syracuseStep 1140391 = 1710587) B1710587
theorem B1140475 : Blo 1136633 1140475 := bstep (se 1 (by rfl) ⟨855356, by rfl⟩ : syracuseStep 1140475 = 1710713) B1710713
theorem B1140511 : Blo 1136633 1140511 := bstep (se 1 (by rfl) ⟨855383, by rfl⟩ : syracuseStep 1140511 = 1710767) B1710767
theorem B1140543 : Blo 1136633 1140543 := bstep (se 1 (by rfl) ⟨855407, by rfl⟩ : syracuseStep 1140543 = 1710815) B1710815
theorem B2877383 : Blo 1136633 2877383 := bstep (se 1 (by rfl) ⟨2158037, by rfl⟩ : syracuseStep 2877383 = 4316075) B4316075
theorem B5761043 : Blo 1136633 5761043 := bstep (se 1 (by rfl) ⟨4320782, by rfl⟩ : syracuseStep 5761043 = 8641565) B8641565
theorem B21884579 : Blo 1136633 21884579 := bstep (se 1 (by rfl) ⟨16413434, by rfl⟩ : syracuseStep 21884579 = 32826869) B32826869
theorem B6483887 : Blo 1136633 6483887 := bstep (se 1 (by rfl) ⟨4862915, by rfl⟩ : syracuseStep 6483887 = 9725831) B9725831
theorem B2158903 : Blo 1136633 2158903 := bstep (se 1 (by rfl) ⟨1619177, by rfl⟩ : syracuseStep 2158903 = 3238355) B3238355
theorem B2159207 : Blo 1136633 2159207 := bstep (se 1 (by rfl) ⟨1619405, by rfl⟩ : syracuseStep 2159207 = 3238811) B3238811
theorem B2159723 : Blo 1136633 2159723 := bstep (se 1 (by rfl) ⟨1619792, by rfl⟩ : syracuseStep 2159723 = 3239585) B3239585
theorem B1537231 : Blo 1136633 1537231 := bstep (se 1 (by rfl) ⟨1152923, by rfl⟩ : syracuseStep 1537231 = 2305847) B2305847
theorem B5469569 : Blo 1136633 5469569 := bstep (se 2 (by rfl) ⟨2051088, by rfl⟩ : syracuseStep 5469569 = 4102177) B4102177
theorem B3373289 : Blo 1136633 3373289 := bstep (se 2 (by rfl) ⟨1264983, by rfl⟩ : syracuseStep 3373289 = 2529967) B2529967
theorem B4324063 : Blo 1136633 4324063 := bstep (se 1 (by rfl) ⟨3243047, by rfl⟩ : syracuseStep 4324063 = 6486095) B6486095
theorem B3242911 : Blo 1136633 3242911 := bstep (se 1 (by rfl) ⟨2432183, by rfl⟩ : syracuseStep 3242911 = 4864367) B4864367
theorem B4324535 : Blo 1136633 4324535 := bstep (se 1 (by rfl) ⟨3243401, by rfl⟩ : syracuseStep 4324535 = 6486803) B6486803
theorem B27655435 : Blo 1136633 27655435 := bstep (se 1 (by rfl) ⟨20741576, by rfl⟩ : syracuseStep 27655435 = 41483153) B41483153
theorem B85425587 : Blo 1136633 85425587 := bstep (se 1 (by rfl) ⟨64069190, by rfl⟩ : syracuseStep 85425587 = 128138381) B128138381
theorem B7798211 : Blo 1136633 7798211 := bstep (se 1 (by rfl) ⟨5848658, by rfl⟩ : syracuseStep 7798211 = 11697317) B11697317
theorem B3243527 : Blo 1136633 3243527 := bstep (se 1 (by rfl) ⟨2432645, by rfl⟩ : syracuseStep 3243527 = 4865291) B4865291
theorem B2883215 : Blo 1136633 2883215 := bstep (se 1 (by rfl) ⟨2162411, by rfl⟩ : syracuseStep 2883215 = 4324823) B4324823
theorem B5767037 : Blo 1136633 5767037 := bstep (se 3 (by rfl) ⟨1081319, by rfl⟩ : syracuseStep 5767037 = 2162639) B2162639
theorem B2162875 : Blo 1136633 2162875 := bstep (se 1 (by rfl) ⟨1622156, by rfl⟩ : syracuseStep 2162875 = 3244313) B3244313
theorem B44433971 : Blo 1136633 44433971 := bstep (se 1 (by rfl) ⟨33325478, by rfl⟩ : syracuseStep 44433971 = 66650957) B66650957
theorem B4325993 : Blo 1136633 4325993 := bstep (se 2 (by rfl) ⟨1622247, by rfl⟩ : syracuseStep 4325993 = 3244495) B3244495
theorem B2884207 : Blo 1136633 2884207 := bstep (se 1 (by rfl) ⟨2163155, by rfl⟩ : syracuseStep 2884207 = 4326311) B4326311
theorem B2163361 : Blo 1136633 2163361 := bstep (se 2 (by rfl) ⟨811260, by rfl⟩ : syracuseStep 2163361 = 1622521) B1622521
theorem B8749835 : Blo 1136633 8749835 := bstep (se 1 (by rfl) ⟨6562376, by rfl⟩ : syracuseStep 8749835 = 13124753) B13124753
theorem B1278751 : Blo 1136633 1278751 := bstep (se 1 (by rfl) ⟨959063, by rfl⟩ : syracuseStep 1278751 = 1918127) B1918127
theorem B10945367 : Blo 1136633 10945367 := bstep (se 1 (by rfl) ⟨8209025, by rfl⟩ : syracuseStep 10945367 = 16418051) B16418051
theorem B1705151 : Blo 1136633 1705151 := bstep (se 1 (by rfl) ⟨1278863, by rfl⟩ : syracuseStep 1705151 = 2557727) B2557727
theorem B5768495 : Blo 1136633 5768495 := bstep (se 1 (by rfl) ⟨4326371, by rfl⟩ : syracuseStep 5768495 = 8652743) B8652743
theorem B1705295 : Blo 1136633 1705295 := bstep (se 1 (by rfl) ⟨1278971, by rfl⟩ : syracuseStep 1705295 = 2557943) B2557943
theorem B1705385 : Blo 1136633 1705385 := bstep (se 2 (by rfl) ⟨639519, by rfl⟩ : syracuseStep 1705385 = 1279039) B1279039
theorem B8652257 : Blo 1136633 8652257 := bstep (se 2 (by rfl) ⟨3244596, by rfl⟩ : syracuseStep 8652257 = 6489193) B6489193
theorem B3245599 : Blo 1136633 3245599 := bstep (se 1 (by rfl) ⟨2434199, by rfl⟩ : syracuseStep 3245599 = 4868399) B4868399
theorem B1443359 : Blo 1136633 1443359 := bstep (se 1 (by rfl) ⟨1082519, by rfl⟩ : syracuseStep 1443359 = 2165039) B2165039
theorem B12289573 : Blo 1136633 12289573 := bstep (se 4 (by rfl) ⟨1152147, by rfl⟩ : syracuseStep 12289573 = 2304295) B2304295
theorem B36996659 : Blo 1136633 36996659 := bstep (se 1 (by rfl) ⟨27747494, by rfl⟩ : syracuseStep 36996659 = 55494989) B55494989
theorem B1705535 : Blo 1136633 1705535 := bstep (se 1 (by rfl) ⟨1279151, by rfl⟩ : syracuseStep 1705535 = 2558303) B2558303
theorem B1705577 : Blo 1136633 1705577 := bstep (se 2 (by rfl) ⟨639591, by rfl⟩ : syracuseStep 1705577 = 1279183) B1279183
theorem B2557547 : Blo 1136633 2557547 := bstep (se 1 (by rfl) ⟨1918160, by rfl⟩ : syracuseStep 2557547 = 3836321) B3836321
theorem B2557817 : Blo 1136633 2557817 := bstep (se 2 (by rfl) ⟨959181, by rfl⟩ : syracuseStep 2557817 = 1918363) B1918363
theorem B2885615 : Blo 1136633 2885615 := bstep (se 1 (by rfl) ⟨2164211, by rfl⟩ : syracuseStep 2885615 = 4328423) B4328423
theorem B1706015 : Blo 1136633 1706015 := bstep (se 1 (by rfl) ⟨1279511, by rfl⟩ : syracuseStep 1706015 = 2559023) B2559023
theorem B1280047 : Blo 1136633 1280047 := bstep (se 1 (by rfl) ⟨960035, by rfl⟩ : syracuseStep 1280047 = 1920071) B1920071
theorem B1706207 : Blo 1136633 1706207 := bstep (se 1 (by rfl) ⟨1279655, by rfl⟩ : syracuseStep 1706207 = 2559311) B2559311
theorem B1706267 : Blo 1136633 1706267 := bstep (se 1 (by rfl) ⟨1279700, by rfl⟩ : syracuseStep 1706267 = 2559401) B2559401
theorem B2558249 : Blo 1136633 2558249 := bstep (se 2 (by rfl) ⟨959343, by rfl⟩ : syracuseStep 2558249 = 1918687) B1918687
theorem B1280335 : Blo 1136633 1280335 := bstep (se 1 (by rfl) ⟨960251, by rfl⟩ : syracuseStep 1280335 = 1920503) B1920503
theorem B3836375 : Blo 1136633 3836375 := bstep (se 1 (by rfl) ⟨2877281, by rfl⟩ : syracuseStep 3836375 = 5754563) B5754563
theorem B4327937 : Blo 1136633 4327937 := bstep (se 2 (by rfl) ⟨1622976, by rfl⟩ : syracuseStep 4327937 = 3245953) B3245953
theorem B1706591 : Blo 1136633 1706591 := bstep (se 1 (by rfl) ⟨1279943, by rfl⟩ : syracuseStep 1706591 = 2559887) B2559887
theorem B6163127 : Blo 1136633 6163127 := bstep (se 1 (by rfl) ⟨4622345, by rfl⟩ : syracuseStep 6163127 = 9244691) B9244691
theorem B2558825 : Blo 1136633 2558825 := bstep (se 2 (by rfl) ⟨959559, by rfl⟩ : syracuseStep 2558825 = 1919119) B1919119
theorem B1706873 : Blo 1136633 1706873 := bstep (se 2 (by rfl) ⟨640077, by rfl⟩ : syracuseStep 1706873 = 1280155) B1280155
theorem B2558879 : Blo 1136633 2558879 := bstep (se 1 (by rfl) ⟨1919159, by rfl⟩ : syracuseStep 2558879 = 3838319) B3838319
theorem B1706921 : Blo 1136633 1706921 := bstep (se 2 (by rfl) ⟨640095, by rfl⟩ : syracuseStep 1706921 = 1280191) B1280191
theorem B1281019 : Blo 1136633 1281019 := bstep (se 1 (by rfl) ⟨960764, by rfl⟩ : syracuseStep 1281019 = 1921529) B1921529
theorem B1707071 : Blo 1136633 1707071 := bstep (se 1 (by rfl) ⟨1280303, by rfl⟩ : syracuseStep 1707071 = 2560607) B2560607
theorem B3247229 : Blo 1136633 3247229 := bstep (se 3 (by rfl) ⟨608855, by rfl⟩ : syracuseStep 3247229 = 1217711) B1217711
theorem B1281199 : Blo 1136633 1281199 := bstep (se 1 (by rfl) ⟨960899, by rfl⟩ : syracuseStep 1281199 = 1921799) B1921799
theorem B1707623 : Blo 1136633 1707623 := bstep (se 1 (by rfl) ⟨1280717, by rfl⟩ : syracuseStep 1707623 = 2561435) B2561435
theorem B2559815 : Blo 1136633 2559815 := bstep (se 1 (by rfl) ⟨1919861, by rfl⟩ : syracuseStep 2559815 = 3839723) B3839723
theorem B1281919 : Blo 1136633 1281919 := bstep (se 1 (by rfl) ⟨961439, by rfl⟩ : syracuseStep 1281919 = 1922879) B1922879
theorem B2428903 : Blo 1136633 2428903 := bstep (se 1 (by rfl) ⟨1821677, by rfl⟩ : syracuseStep 2428903 = 3643355) B3643355
theorem B1708007 : Blo 1136633 1708007 := bstep (se 1 (by rfl) ⟨1281005, by rfl⟩ : syracuseStep 1708007 = 2562011) B2562011
theorem B2559995 : Blo 1136633 2559995 := bstep (se 1 (by rfl) ⟨1919996, by rfl⟩ : syracuseStep 2559995 = 3839993) B3839993
theorem B18747443 : Blo 1136633 18747443 := bstep (se 1 (by rfl) ⟨14060582, by rfl⟩ : syracuseStep 18747443 = 28121165) B28121165
theorem B4100159 : Blo 1136633 4100159 := bstep (se 1 (by rfl) ⟨3075119, by rfl⟩ : syracuseStep 4100159 = 6150239) B6150239
theorem B2429023 : Blo 1136633 2429023 := bstep (se 1 (by rfl) ⟨1821767, by rfl⟩ : syracuseStep 2429023 = 3643535) B3643535
theorem B1708127 : Blo 1136633 1708127 := bstep (se 1 (by rfl) ⟨1281095, by rfl⟩ : syracuseStep 1708127 = 2562191) B2562191
theorem B2560103 : Blo 1136633 2560103 := bstep (se 1 (by rfl) ⟨1920077, by rfl⟩ : syracuseStep 2560103 = 3840155) B3840155
theorem B1708139 : Blo 1136633 1708139 := bstep (se 1 (by rfl) ⟨1281104, by rfl⟩ : syracuseStep 1708139 = 2562209) B2562209
theorem B1708187 : Blo 1136633 1708187 := bstep (se 1 (by rfl) ⟨1281140, by rfl⟩ : syracuseStep 1708187 = 2562281) B2562281
theorem B2560175 : Blo 1136633 2560175 := bstep (se 1 (by rfl) ⟨1920131, by rfl⟩ : syracuseStep 2560175 = 3840263) B3840263
theorem B1282459 : Blo 1136633 1282459 := bstep (se 1 (by rfl) ⟨961844, by rfl⟩ : syracuseStep 1282459 = 1923689) B1923689
theorem B2560859 : Blo 1136633 2560859 := bstep (se 1 (by rfl) ⟨1920644, by rfl⟩ : syracuseStep 2560859 = 3841289) B3841289
theorem B1709039 : Blo 1136633 1709039 := bstep (se 1 (by rfl) ⟨1281779, by rfl⟩ : syracuseStep 1709039 = 2563559) B2563559
theorem B1283143 : Blo 1136633 1283143 := bstep (se 1 (by rfl) ⟨962357, by rfl⟩ : syracuseStep 1283143 = 1924715) B1924715
theorem B4330685 : Blo 1136633 4330685 := bstep (se 3 (by rfl) ⟨812003, by rfl⟩ : syracuseStep 4330685 = 1624007) B1624007
theorem B3839183 : Blo 1136633 3839183 := bstep (se 1 (by rfl) ⟨2879387, by rfl⟩ : syracuseStep 3839183 = 5758775) B5758775
theorem B2594159 : Blo 1136633 2594159 := bstep (se 1 (by rfl) ⟨1945619, by rfl⟩ : syracuseStep 2594159 = 3891239) B3891239
theorem B1709423 : Blo 1136633 1709423 := bstep (se 1 (by rfl) ⟨1282067, by rfl⟩ : syracuseStep 1709423 = 2564135) B2564135
theorem B1709543 : Blo 1136633 1709543 := bstep (se 1 (by rfl) ⟨1282157, by rfl⟩ : syracuseStep 1709543 = 2564315) B2564315
theorem B2561615 : Blo 1136633 2561615 := bstep (se 1 (by rfl) ⟨1921211, by rfl⟩ : syracuseStep 2561615 = 3842423) B3842423
theorem B4101715 : Blo 1136633 4101715 := bstep (se 1 (by rfl) ⟨3076286, by rfl⟩ : syracuseStep 4101715 = 6152573) B6152573
theorem B19732085 : Blo 1136633 19732085 := bstep (se 5 (by rfl) ⟨924941, by rfl⟩ : syracuseStep 19732085 = 1849883) B1849883
theorem B1709705 : Blo 1136633 1709705 := bstep (se 2 (by rfl) ⟨641139, by rfl⟩ : syracuseStep 1709705 = 1282279) B1282279
theorem B1709723 : Blo 1136633 1709723 := bstep (se 1 (by rfl) ⟨1282292, by rfl⟩ : syracuseStep 1709723 = 2564585) B2564585
theorem B1709915 : Blo 1136633 1709915 := bstep (se 1 (by rfl) ⟨1282436, by rfl⟩ : syracuseStep 1709915 = 2564873) B2564873
theorem B1710299 : Blo 1136633 1710299 := bstep (se 1 (by rfl) ⟨1282724, by rfl⟩ : syracuseStep 1710299 = 2565449) B2565449
theorem B2562335 : Blo 1136633 2562335 := bstep (se 1 (by rfl) ⟨1921751, by rfl⟩ : syracuseStep 2562335 = 3843503) B3843503
theorem B1710569 : Blo 1136633 1710569 := bstep (se 2 (by rfl) ⟨641463, by rfl⟩ : syracuseStep 1710569 = 1282927) B1282927
theorem B2562587 : Blo 1136633 2562587 := bstep (se 1 (by rfl) ⟨1921940, by rfl⟩ : syracuseStep 2562587 = 3843881) B3843881
theorem B3840695 : Blo 1136633 3840695 := bstep (se 1 (by rfl) ⟨2880521, by rfl⟩ : syracuseStep 3840695 = 5761043) B5761043
theorem B4856543 : Blo 1136633 4856543 := bstep (se 1 (by rfl) ⟨3642407, by rfl⟩ : syracuseStep 4856543 = 7284815) B7284815
theorem B2432047 : Blo 1136633 2432047 := bstep (se 1 (by rfl) ⟨1824035, by rfl⟩ : syracuseStep 2432047 = 3648071) B3648071
theorem B14589719 : Blo 1136633 14589719 := bstep (se 1 (by rfl) ⟨10942289, by rfl⟩ : syracuseStep 14589719 = 21884579) B21884579
theorem B2563937 : Blo 1136633 2563937 := bstep (se 2 (by rfl) ⟨961476, by rfl⟩ : syracuseStep 2563937 = 1922953) B1922953
theorem B2564063 : Blo 1136633 2564063 := bstep (se 1 (by rfl) ⟨1923047, by rfl⟩ : syracuseStep 2564063 = 3846095) B3846095
theorem B4857995 : Blo 1136633 4857995 := bstep (se 1 (by rfl) ⟨3643496, by rfl⟩ : syracuseStep 4857995 = 7286993) B7286993
theorem B2564351 : Blo 1136633 2564351 := bstep (se 1 (by rfl) ⟨1923263, by rfl⟩ : syracuseStep 2564351 = 3846527) B3846527
theorem B10952975 : Blo 1136633 10952975 := bstep (se 1 (by rfl) ⟨8214731, by rfl⟩ : syracuseStep 10952975 = 16429463) B16429463
theorem B2564513 : Blo 1136633 2564513 := bstep (se 2 (by rfl) ⟨961692, by rfl⟩ : syracuseStep 2564513 = 1923385) B1923385
theorem B3646379 : Blo 1136633 3646379 := bstep (se 1 (by rfl) ⟨2734784, by rfl⟩ : syracuseStep 3646379 = 5469569) B5469569
theorem B2565287 : Blo 1136633 2565287 := bstep (se 1 (by rfl) ⟨1923965, by rfl⟩ : syracuseStep 2565287 = 3847931) B3847931
theorem B2565395 : Blo 1136633 2565395 := bstep (se 1 (by rfl) ⟨1924046, by rfl⟩ : syracuseStep 2565395 = 3848093) B3848093
theorem B36873913 : Blo 1136633 36873913 := bstep (se 2 (by rfl) ⟨13827717, by rfl⟩ : syracuseStep 36873913 = 27655435) B27655435
theorem B2566025 : Blo 1136633 2566025 := bstep (se 2 (by rfl) ⟨962259, by rfl⟩ : syracuseStep 2566025 = 1924519) B1924519
theorem B2566043 : Blo 1136633 2566043 := bstep (se 1 (by rfl) ⟨1924532, by rfl⟩ : syracuseStep 2566043 = 3849065) B3849065
theorem B2566079 : Blo 1136633 2566079 := bstep (se 1 (by rfl) ⟨1924559, by rfl⟩ : syracuseStep 2566079 = 3849119) B3849119
theorem B2566241 : Blo 1136633 2566241 := bstep (se 2 (by rfl) ⟨962340, by rfl⟩ : syracuseStep 2566241 = 1924681) B1924681
theorem B3647609 : Blo 1136633 3647609 := bstep (se 2 (by rfl) ⟨1367853, by rfl⟩ : syracuseStep 3647609 = 2735707) B2735707
theorem B4860233 : Blo 1136633 4860233 := bstep (se 2 (by rfl) ⟨1822587, by rfl⟩ : syracuseStep 4860233 = 3645175) B3645175
theorem B18491975 : Blo 1136633 18491975 := bstep (se 1 (by rfl) ⟨13868981, by rfl⟩ : syracuseStep 18491975 = 27737963) B27737963
theorem B3844691 : Blo 1136633 3844691 := bstep (se 1 (by rfl) ⟨2883518, by rfl⟩ : syracuseStep 3844691 = 5767037) B5767037
theorem B9743327 : Blo 1136633 9743327 := bstep (se 1 (by rfl) ⟨7307495, by rfl⟩ : syracuseStep 9743327 = 14614991) B14614991
theorem B7285889 : Blo 1136633 7285889 := bstep (se 2 (by rfl) ⟨2732208, by rfl⟩ : syracuseStep 7285889 = 5464417) B5464417
theorem B79834247 : Blo 1136633 79834247 := bstep (se 1 (by rfl) ⟨59875685, by rfl⟩ : syracuseStep 79834247 = 119751371) B119751371
theorem B3845879 : Blo 1136633 3845879 := bstep (se 1 (by rfl) ⟨2884409, by rfl⟩ : syracuseStep 3845879 = 5768819) B5768819
theorem B12955787 : Blo 1136633 12955787 := bstep (se 1 (by rfl) ⟨9716840, by rfl⟩ : syracuseStep 12955787 = 19433681) B19433681
theorem B4108519 : Blo 1136633 4108519 := bstep (se 1 (by rfl) ⟨3081389, by rfl⟩ : syracuseStep 4108519 = 6162779) B6162779
theorem B3846419 : Blo 1136633 3846419 := bstep (se 1 (by rfl) ⟨2884814, by rfl⟩ : syracuseStep 3846419 = 5769629) B5769629
theorem B11088353 : Blo 1136633 11088353 := bstep (se 2 (by rfl) ⟨4158132, by rfl⟩ : syracuseStep 11088353 = 8316265) B8316265
theorem B4862521 : Blo 1136633 4862521 := bstep (se 2 (by rfl) ⟨1823445, by rfl⟩ : syracuseStep 4862521 = 3646891) B3646891
theorem B5550781 : Blo 1136633 5550781 := bstep (se 3 (by rfl) ⟨1040771, by rfl⟩ : syracuseStep 5550781 = 2081543) B2081543
theorem B3846959 : Blo 1136633 3846959 := bstep (se 1 (by rfl) ⟨2885219, by rfl⟩ : syracuseStep 3846959 = 5770439) B5770439
theorem B16397579 : Blo 1136633 16397579 := bstep (se 1 (by rfl) ⟨12298184, by rfl⟩ : syracuseStep 16397579 = 24596369) B24596369
theorem B4929133 : Blo 1136633 4929133 := bstep (se 3 (by rfl) ⟨924212, by rfl⟩ : syracuseStep 4929133 = 1848425) B1848425
theorem B2307727 : Blo 1136633 2307727 := bstep (se 1 (by rfl) ⟨1730795, by rfl⟩ : syracuseStep 2307727 = 3461591) B3461591
theorem B3847823 : Blo 1136633 3847823 := bstep (se 1 (by rfl) ⟨2885867, by rfl⟩ : syracuseStep 3847823 = 5771735) B5771735
theorem B7780063 : Blo 1136633 7780063 := bstep (se 1 (by rfl) ⟨5835047, by rfl⟩ : syracuseStep 7780063 = 11670095) B11670095
theorem B4864009 : Blo 1136633 4864009 := bstep (se 2 (by rfl) ⟨1824003, by rfl⟩ : syracuseStep 4864009 = 3648007) B3648007
theorem B3848201 : Blo 1136633 3848201 := bstep (se 2 (by rfl) ⟨1443075, by rfl⟩ : syracuseStep 3848201 = 2886151) B2886151
theorem B4865255 : Blo 1136633 4865255 := bstep (se 1 (by rfl) ⟨3648941, by rfl⟩ : syracuseStep 4865255 = 7297883) B7297883
theorem B3849551 : Blo 1136633 3849551 := bstep (se 1 (by rfl) ⟨2887163, by rfl⟩ : syracuseStep 3849551 = 5774327) B5774327
theorem B1621615 : Blo 1136633 1621615 := bstep (se 1 (by rfl) ⟨1216211, by rfl⟩ : syracuseStep 1621615 = 2432423) B2432423
theorem B93471083 : Blo 1136633 93471083 := bstep (se 1 (by rfl) ⟨70103312, by rfl⟩ : syracuseStep 93471083 = 140206625) B140206625
theorem B2736937 : Blo 1136633 2736937 := bstep (se 2 (by rfl) ⟨1026351, by rfl⟩ : syracuseStep 2736937 = 2052703) B2052703
theorem B8635247 : Blo 1136633 8635247 := bstep (se 1 (by rfl) ⟨6476435, by rfl⟩ : syracuseStep 8635247 = 12952871) B12952871
theorem B4375547 : Blo 1136633 4375547 := bstep (se 1 (by rfl) ⟨3281660, by rfl⟩ : syracuseStep 4375547 = 6563321) B6563321
theorem B4867067 : Blo 1136633 4867067 := bstep (se 1 (by rfl) ⟨3650300, by rfl⟩ : syracuseStep 4867067 = 7300601) B7300601
theorem B1918255 : Blo 1136633 1918255 := bstep (se 1 (by rfl) ⟨1438691, by rfl⟩ : syracuseStep 1918255 = 2877383) B2877383
theorem B49202579 : Blo 1136633 49202579 := bstep (se 1 (by rfl) ⟨36901934, by rfl⟩ : syracuseStep 49202579 = 73803869) B73803869
theorem B24659417 : Blo 1136633 24659417 := bstep (se 2 (by rfl) ⟨9247281, by rfl⟩ : syracuseStep 24659417 = 18494563) B18494563
theorem B2049641 : Blo 1136633 2049641 := bstep (se 2 (by rfl) ⟨768615, by rfl⟩ : syracuseStep 2049641 = 1537231) B1537231
theorem B10931219 : Blo 1136633 10931219 := bstep (se 1 (by rfl) ⟨8198414, by rfl⟩ : syracuseStep 10931219 = 16396829) B16396829
theorem B14568497 : Blo 1136633 14568497 := bstep (se 2 (by rfl) ⟨5463186, by rfl⟩ : syracuseStep 14568497 = 10926373) B10926373
theorem B2739263 : Blo 1136633 2739263 := bstep (se 1 (by rfl) ⟨2054447, by rfl⟩ : syracuseStep 2739263 = 4108895) B4108895
theorem B12307913 : Blo 1136633 12307913 := bstep (se 2 (by rfl) ⟨4615467, by rfl⟩ : syracuseStep 12307913 = 9230935) B9230935
theorem B4869665 : Blo 1136633 4869665 := bstep (se 2 (by rfl) ⟨1826124, by rfl⟩ : syracuseStep 4869665 = 3652249) B3652249
theorem B3460919 : Blo 1136633 3460919 := bstep (se 1 (by rfl) ⟨2595689, by rfl⟩ : syracuseStep 3460919 = 5191379) B5191379
theorem B4378495 : Blo 1136633 4378495 := bstep (se 1 (by rfl) ⟨3283871, by rfl⟩ : syracuseStep 4378495 = 6567743) B6567743
theorem B7786469 : Blo 1136633 7786469 := bstep (se 4 (by rfl) ⟨729981, by rfl⟩ : syracuseStep 7786469 = 1459963) B1459963
theorem B2248859 : Blo 1136633 2248859 := bstep (se 1 (by rfl) ⟨1686644, by rfl⟩ : syracuseStep 2248859 = 3373289) B3373289
theorem B8638649 : Blo 1136633 8638649 := bstep (se 2 (by rfl) ⟨3239493, by rfl⟩ : syracuseStep 8638649 = 6478987) B6478987
theorem B15585479 : Blo 1136633 15585479 := bstep (se 1 (by rfl) ⟨11689109, by rfl⟩ : syracuseStep 15585479 = 23378219) B23378219
theorem B12964535 : Blo 1136633 12964535 := bstep (se 1 (by rfl) ⟨9723401, by rfl⟩ : syracuseStep 12964535 = 19446803) B19446803
theorem B21025469 : Blo 1136633 21025469 := bstep (se 3 (by rfl) ⟨3942275, by rfl⟩ : syracuseStep 21025469 = 7884551) B7884551
theorem B5198807 : Blo 1136633 5198807 := bstep (se 1 (by rfl) ⟨3899105, by rfl⟩ : syracuseStep 5198807 = 7798211) B7798211
theorem B1922143 : Blo 1136633 1922143 := bstep (se 1 (by rfl) ⟨1441607, by rfl⟩ : syracuseStep 1922143 = 2883215) B2883215
theorem B11097431 : Blo 1136633 11097431 := bstep (se 1 (by rfl) ⟨8323073, by rfl⟩ : syracuseStep 11097431 = 16646147) B16646147
theorem B1169051 : Blo 1136633 1169051 := bstep (se 1 (by rfl) ⟨876788, by rfl⟩ : syracuseStep 1169051 = 1753577) B1753577
theorem B33281887 : Blo 1136633 33281887 := bstep (se 1 (by rfl) ⟨24961415, by rfl⟩ : syracuseStep 33281887 = 49922831) B49922831
theorem B1136711 : Blo 1136633 1136711 := bstep (se 1 (by rfl) ⟨852533, by rfl⟩ : syracuseStep 1136711 = 1705067) B1705067
theorem B1136871 : Blo 1136633 1136871 := bstep (se 1 (by rfl) ⟨852653, by rfl⟩ : syracuseStep 1136871 = 1705307) B1705307
theorem B1137055 : Blo 1136633 1137055 := bstep (se 1 (by rfl) ⟨852791, by rfl⟩ : syracuseStep 1137055 = 1705583) B1705583
theorem B1825183 : Blo 1136633 1825183 := bstep (se 1 (by rfl) ⟨1368887, by rfl⟩ : syracuseStep 1825183 = 2737775) B2737775
theorem B3889595 : Blo 1136633 3889595 := bstep (se 1 (by rfl) ⟨2917196, by rfl⟩ : syracuseStep 3889595 = 5834393) B5834393
theorem B1137103 : Blo 1136633 1137103 := bstep (se 1 (by rfl) ⟨852827, by rfl⟩ : syracuseStep 1137103 = 1705655) B1705655
theorem B1137127 : Blo 1136633 1137127 := bstep (se 1 (by rfl) ⟨852845, by rfl⟩ : syracuseStep 1137127 = 1705691) B1705691
theorem B1137243 : Blo 1136633 1137243 := bstep (se 1 (by rfl) ⟨852932, by rfl⟩ : syracuseStep 1137243 = 1705865) B1705865
theorem B4315801 : Blo 1136633 4315801 := bstep (se 2 (by rfl) ⟨1618425, by rfl⟩ : syracuseStep 4315801 = 3236851) B3236851
theorem B1137311 : Blo 1136633 1137311 := bstep (se 1 (by rfl) ⟨852983, by rfl⟩ : syracuseStep 1137311 = 1705967) B1705967
theorem B1137479 : Blo 1136633 1137479 := bstep (se 1 (by rfl) ⟨853109, by rfl⟩ : syracuseStep 1137479 = 1706219) B1706219
theorem B2808647 : Blo 1136633 2808647 := bstep (se 1 (by rfl) ⟨2106485, by rfl⟩ : syracuseStep 2808647 = 4212971) B4212971
theorem B1137519 : Blo 1136633 1137519 := bstep (se 1 (by rfl) ⟨853139, by rfl⟩ : syracuseStep 1137519 = 1706279) B1706279
theorem B1137575 : Blo 1136633 1137575 := bstep (se 1 (by rfl) ⟨853181, by rfl⟩ : syracuseStep 1137575 = 1706363) B1706363
theorem B1137755 : Blo 1136633 1137755 := bstep (se 1 (by rfl) ⟨853316, by rfl⟩ : syracuseStep 1137755 = 1706633) B1706633
theorem B1137871 : Blo 1136633 1137871 := bstep (se 1 (by rfl) ⟨853403, by rfl⟩ : syracuseStep 1137871 = 1706807) B1706807
theorem B1924303 : Blo 1136633 1924303 := bstep (se 1 (by rfl) ⟨1443227, by rfl⟩ : syracuseStep 1924303 = 2886455) B2886455
theorem B1137895 : Blo 1136633 1137895 := bstep (se 1 (by rfl) ⟨853421, by rfl⟩ : syracuseStep 1137895 = 1706843) B1706843
theorem B1137991 : Blo 1136633 1137991 := bstep (se 1 (by rfl) ⟨853493, by rfl⟩ : syracuseStep 1137991 = 1706987) B1706987
theorem B41540971 : Blo 1136633 41540971 := bstep (se 1 (by rfl) ⟨31155728, by rfl⟩ : syracuseStep 41540971 = 62311457) B62311457
theorem B1138127 : Blo 1136633 1138127 := bstep (se 1 (by rfl) ⟨853595, by rfl⟩ : syracuseStep 1138127 = 1707191) B1707191
theorem B1138287 : Blo 1136633 1138287 := bstep (se 1 (by rfl) ⟨853715, by rfl⟩ : syracuseStep 1138287 = 1707431) B1707431
theorem B4218493 : Blo 1136633 4218493 := bstep (se 3 (by rfl) ⟨790967, by rfl⟩ : syracuseStep 4218493 = 1581935) B1581935
theorem B1138343 : Blo 1136633 1138343 := bstep (se 1 (by rfl) ⟨853757, by rfl⟩ : syracuseStep 1138343 = 1707515) B1707515
theorem B1138407 : Blo 1136633 1138407 := bstep (se 1 (by rfl) ⟨853805, by rfl⟩ : syracuseStep 1138407 = 1707611) B1707611
theorem B31121131 : Blo 1136633 31121131 := bstep (se 1 (by rfl) ⟨23340848, by rfl⟩ : syracuseStep 31121131 = 46681697) B46681697
theorem B1138463 : Blo 1136633 1138463 := bstep (se 1 (by rfl) ⟨853847, by rfl⟩ : syracuseStep 1138463 = 1707695) B1707695
theorem B1138543 : Blo 1136633 1138543 := bstep (se 1 (by rfl) ⟨853907, by rfl⟩ : syracuseStep 1138543 = 1707815) B1707815
theorem B1138599 : Blo 1136633 1138599 := bstep (se 1 (by rfl) ⟨853949, by rfl⟩ : syracuseStep 1138599 = 1707899) B1707899
theorem B1138879 : Blo 1136633 1138879 := bstep (se 1 (by rfl) ⟨854159, by rfl⟩ : syracuseStep 1138879 = 1708319) B1708319
theorem B1138895 : Blo 1136633 1138895 := bstep (se 1 (by rfl) ⟨854171, by rfl⟩ : syracuseStep 1138895 = 1708343) B1708343
theorem B1138943 : Blo 1136633 1138943 := bstep (se 1 (by rfl) ⟨854207, by rfl⟩ : syracuseStep 1138943 = 1708415) B1708415
theorem B5759261 : Blo 1136633 5759261 := bstep (se 3 (by rfl) ⟨1079861, by rfl⟩ : syracuseStep 5759261 = 2159723) B2159723
theorem B1138991 : Blo 1136633 1138991 := bstep (se 1 (by rfl) ⟨854243, by rfl⟩ : syracuseStep 1138991 = 1708487) B1708487
theorem B1139227 : Blo 1136633 1139227 := bstep (se 1 (by rfl) ⟨854420, by rfl⟩ : syracuseStep 1139227 = 1708841) B1708841
theorem B1139231 : Blo 1136633 1139231 := bstep (se 1 (by rfl) ⟨854423, by rfl⟩ : syracuseStep 1139231 = 1708847) B1708847
theorem B1139311 : Blo 1136633 1139311 := bstep (se 1 (by rfl) ⟨854483, by rfl⟩ : syracuseStep 1139311 = 1708967) B1708967
theorem B1139367 : Blo 1136633 1139367 := bstep (se 1 (by rfl) ⟨854525, by rfl⟩ : syracuseStep 1139367 = 1709051) B1709051
theorem B1139407 : Blo 1136633 1139407 := bstep (se 1 (by rfl) ⟨854555, by rfl⟩ : syracuseStep 1139407 = 1709111) B1709111
theorem B1139487 : Blo 1136633 1139487 := bstep (se 1 (by rfl) ⟨854615, by rfl⟩ : syracuseStep 1139487 = 1709231) B1709231
theorem B1139759 : Blo 1136633 1139759 := bstep (se 1 (by rfl) ⟨854819, by rfl⟩ : syracuseStep 1139759 = 1709639) B1709639
theorem B1139823 : Blo 1136633 1139823 := bstep (se 1 (by rfl) ⟨854867, by rfl⟩ : syracuseStep 1139823 = 1709735) B1709735
theorem B1139879 : Blo 1136633 1139879 := bstep (se 1 (by rfl) ⟨854909, by rfl⟩ : syracuseStep 1139879 = 1709819) B1709819
theorem B1139903 : Blo 1136633 1139903 := bstep (se 1 (by rfl) ⟨854927, by rfl⟩ : syracuseStep 1139903 = 1709855) B1709855
theorem B1139935 : Blo 1136633 1139935 := bstep (se 1 (by rfl) ⟨854951, by rfl⟩ : syracuseStep 1139935 = 1709903) B1709903
theorem B1369391 : Blo 1136633 1369391 := bstep (se 1 (by rfl) ⟨1027043, by rfl⟩ : syracuseStep 1369391 = 2054087) B2054087
theorem B1140015 : Blo 1136633 1140015 := bstep (se 1 (by rfl) ⟨855011, by rfl⟩ : syracuseStep 1140015 = 1710023) B1710023
theorem B22177091 : Blo 1136633 22177091 := bstep (se 1 (by rfl) ⟨16632818, by rfl⟩ : syracuseStep 22177091 = 33265637) B33265637
theorem B14607863 : Blo 1136633 14607863 := bstep (se 1 (by rfl) ⟨10955897, by rfl⟩ : syracuseStep 14607863 = 21911795) B21911795
theorem B1140251 : Blo 1136633 1140251 := bstep (se 1 (by rfl) ⟨855188, by rfl⟩ : syracuseStep 1140251 = 1710377) B1710377
theorem B1140255 : Blo 1136633 1140255 := bstep (se 1 (by rfl) ⟨855191, by rfl⟩ : syracuseStep 1140255 = 1710383) B1710383
theorem B4384327 : Blo 1136633 4384327 := bstep (se 1 (by rfl) ⟨3288245, by rfl⟩ : syracuseStep 4384327 = 6576491) B6576491
theorem B1140415 : Blo 1136633 1140415 := bstep (se 1 (by rfl) ⟨855311, by rfl⟩ : syracuseStep 1140415 = 1710623) B1710623
theorem B23357263 : Blo 1136633 23357263 := bstep (se 1 (by rfl) ⟨17517947, by rfl⟩ : syracuseStep 23357263 = 35035895) B35035895
theorem B2877403 : Blo 1136633 2877403 := bstep (se 1 (by rfl) ⟨2158052, by rfl⟩ : syracuseStep 2877403 = 4316105) B4316105
theorem B21915791 : Blo 1136633 21915791 := bstep (se 1 (by rfl) ⟨16436843, by rfl⟩ : syracuseStep 21915791 = 32873687) B32873687
theorem B8218883 : Blo 1136633 8218883 := bstep (se 1 (by rfl) ⟨6164162, by rfl⟩ : syracuseStep 8218883 = 12328325) B12328325
theorem B6482861 : Blo 1136633 6482861 := bstep (se 3 (by rfl) ⟨1215536, by rfl⟩ : syracuseStep 6482861 = 2431073) B2431073
theorem B129723439 : Blo 1136633 129723439 := bstep (se 1 (by rfl) ⟨97292579, by rfl⟩ : syracuseStep 129723439 = 194585159) B194585159
theorem B2878537 : Blo 1136633 2878537 := bstep (se 2 (by rfl) ⟨1079451, by rfl⟩ : syracuseStep 2878537 = 2158903) B2158903
theorem B4615337 : Blo 1136633 4615337 := bstep (se 2 (by rfl) ⟨1730751, by rfl⟩ : syracuseStep 4615337 = 3461503) B3461503
theorem B4320479 : Blo 1136633 4320479 := bstep (se 1 (by rfl) ⟨3240359, by rfl⟩ : syracuseStep 4320479 = 6480719) B6480719
theorem B2157833 : Blo 1136633 2157833 := bstep (se 2 (by rfl) ⟨809187, by rfl⟩ : syracuseStep 2157833 = 1618375) B1618375
theorem B8645939 : Blo 1136633 8645939 := bstep (se 1 (by rfl) ⟨6484454, by rfl⟩ : syracuseStep 8645939 = 12968909) B12968909
theorem B65662487 : Blo 1136633 65662487 := bstep (se 1 (by rfl) ⟨49246865, by rfl⟩ : syracuseStep 65662487 = 98493731) B98493731
theorem B2191099 : Blo 1136633 2191099 := bstep (se 1 (by rfl) ⟨1643324, by rfl⟩ : syracuseStep 2191099 = 3286649) B3286649
theorem B3241043 : Blo 1136633 3241043 := bstep (se 1 (by rfl) ⟨2430782, by rfl⟩ : syracuseStep 3241043 = 4861565) B4861565
theorem B4322591 : Blo 1136633 4322591 := bstep (se 1 (by rfl) ⟨3241943, by rfl⟩ : syracuseStep 4322591 = 6483887) B6483887
theorem B2160361 : Blo 1136633 2160361 := bstep (se 2 (by rfl) ⟨810135, by rfl⟩ : syracuseStep 2160361 = 1620271) B1620271
theorem B1439471 : Blo 1136633 1439471 := bstep (se 1 (by rfl) ⟨1079603, by rfl⟩ : syracuseStep 1439471 = 2159207) B2159207
theorem B9238333 : Blo 1136633 9238333 := bstep (se 3 (by rfl) ⟨1732187, by rfl⟩ : syracuseStep 9238333 = 3464375) B3464375
theorem B5765417 : Blo 1136633 5765417 := bstep (se 2 (by rfl) ⟨2162031, by rfl⟩ : syracuseStep 5765417 = 4324063) B4324063
theorem B4323881 : Blo 1136633 4323881 := bstep (se 2 (by rfl) ⟨1621455, by rfl⟩ : syracuseStep 4323881 = 3242911) B3242911
theorem B2161417 : Blo 1136633 2161417 := bstep (se 2 (by rfl) ⟨810531, by rfl⟩ : syracuseStep 2161417 = 1621063) B1621063
theorem B2883023 : Blo 1136633 2883023 := bstep (se 1 (by rfl) ⟨2162267, by rfl⟩ : syracuseStep 2883023 = 4324535) B4324535
theorem B56950391 : Blo 1136633 56950391 := bstep (se 1 (by rfl) ⟨42712793, by rfl⟩ : syracuseStep 56950391 = 85425587) B85425587
theorem B4325021 : Blo 1136633 4325021 := bstep (se 3 (by rfl) ⟨810941, by rfl⟩ : syracuseStep 4325021 = 1621883) B1621883
theorem B2162351 : Blo 1136633 2162351 := bstep (se 1 (by rfl) ⟨1621763, by rfl⟩ : syracuseStep 2162351 = 3243527) B3243527
theorem B5472029 : Blo 1136633 5472029 := bstep (se 3 (by rfl) ⟨1026005, by rfl⟩ : syracuseStep 5472029 = 2052011) B2052011
theorem B2883833 : Blo 1136633 2883833 := bstep (se 2 (by rfl) ⟨1081437, by rfl⟩ : syracuseStep 2883833 = 2162875) B2162875
theorem B29622647 : Blo 1136633 29622647 := bstep (se 1 (by rfl) ⟨22216985, by rfl⟩ : syracuseStep 29622647 = 44433971) B44433971
theorem B2883995 : Blo 1136633 2883995 := bstep (se 1 (by rfl) ⟨2162996, by rfl⟩ : syracuseStep 2883995 = 4325993) B4325993
theorem B5833223 : Blo 1136633 5833223 := bstep (se 1 (by rfl) ⟨4374917, by rfl⟩ : syracuseStep 5833223 = 8749835) B8749835
theorem B2917031 : Blo 1136633 2917031 := bstep (se 1 (by rfl) ⟨2187773, by rfl⟩ : syracuseStep 2917031 = 4375547) B4375547
theorem B3244711 : Blo 1136633 3244711 := bstep (se 1 (by rfl) ⟨2433533, by rfl⟩ : syracuseStep 3244711 = 4867067) B4867067
theorem B2884481 : Blo 1136633 2884481 := bstep (se 2 (by rfl) ⟨1081680, by rfl⟩ : syracuseStep 2884481 = 2163361) B2163361
theorem B32801719 : Blo 1136633 32801719 := bstep (se 1 (by rfl) ⟨24601289, by rfl⟩ : syracuseStep 32801719 = 49202579) B49202579
theorem B5768171 : Blo 1136633 5768171 := bstep (se 1 (by rfl) ⟨4326128, by rfl⟩ : syracuseStep 5768171 = 8652257) B8652257
theorem B1705001 : Blo 1136633 1705001 := bstep (se 2 (by rfl) ⟨639375, by rfl⟩ : syracuseStep 1705001 = 1278751) B1278751
theorem B1705031 : Blo 1136633 1705031 := bstep (se 1 (by rfl) ⟨1278773, by rfl⟩ : syracuseStep 1705031 = 2557547) B2557547
theorem B1705211 : Blo 1136633 1705211 := bstep (se 1 (by rfl) ⟨1278908, by rfl⟩ : syracuseStep 1705211 = 2557817) B2557817
theorem B1705499 : Blo 1136633 1705499 := bstep (se 1 (by rfl) ⟨1279124, by rfl⟩ : syracuseStep 1705499 = 2558249) B2558249
theorem B2557583 : Blo 1136633 2557583 := bstep (se 1 (by rfl) ⟨1918187, by rfl⟩ : syracuseStep 2557583 = 3836375) B3836375
theorem B2885291 : Blo 1136633 2885291 := bstep (se 1 (by rfl) ⟨2163968, by rfl⟩ : syracuseStep 2885291 = 4327937) B4327937
theorem B2557673 : Blo 1136633 2557673 := bstep (se 2 (by rfl) ⟨959127, by rfl⟩ : syracuseStep 2557673 = 1918255) B1918255
theorem B1705883 : Blo 1136633 1705883 := bstep (se 1 (by rfl) ⟨1279412, by rfl⟩ : syracuseStep 1705883 = 2558825) B2558825
theorem B1705919 : Blo 1136633 1705919 := bstep (se 1 (by rfl) ⟨1279439, by rfl⟩ : syracuseStep 1705919 = 2558879) B2558879
theorem B4327465 : Blo 1136633 4327465 := bstep (se 2 (by rfl) ⟨1622799, by rfl⟩ : syracuseStep 4327465 = 3245599) B3245599
theorem B2164819 : Blo 1136633 2164819 := bstep (se 1 (by rfl) ⟨1623614, by rfl⟩ : syracuseStep 2164819 = 3247229) B3247229
theorem B3246443 : Blo 1136633 3246443 := bstep (se 1 (by rfl) ⟨2434832, by rfl⟩ : syracuseStep 3246443 = 4869665) B4869665
theorem B1706543 : Blo 1136633 1706543 := bstep (se 1 (by rfl) ⟨1279907, by rfl⟩ : syracuseStep 1706543 = 2559815) B2559815
theorem B3836537 : Blo 1136633 3836537 := bstep (se 2 (by rfl) ⟨1438701, by rfl⟩ : syracuseStep 3836537 = 2877403) B2877403
theorem B1706663 : Blo 1136633 1706663 := bstep (se 1 (by rfl) ⟨1279997, by rfl⟩ : syracuseStep 1706663 = 2559995) B2559995
theorem B1706729 : Blo 1136633 1706729 := bstep (se 2 (by rfl) ⟨640023, by rfl⟩ : syracuseStep 1706729 = 1280047) B1280047
theorem B1706735 : Blo 1136633 1706735 := bstep (se 1 (by rfl) ⟨1280051, by rfl⟩ : syracuseStep 1706735 = 2560103) B2560103
theorem B1706783 : Blo 1136633 1706783 := bstep (se 1 (by rfl) ⟨1280087, by rfl⟩ : syracuseStep 1706783 = 2560175) B2560175
theorem B10390319 : Blo 1136633 10390319 := bstep (se 1 (by rfl) ⟨7792739, by rfl⟩ : syracuseStep 10390319 = 15585479) B15585479
theorem B1707113 : Blo 1136633 1707113 := bstep (se 2 (by rfl) ⟨640167, by rfl⟩ : syracuseStep 1707113 = 1280335) B1280335
theorem B1707239 : Blo 1136633 1707239 := bstep (se 1 (by rfl) ⟨1280429, by rfl⟩ : syracuseStep 1707239 = 2560859) B2560859
theorem B2887123 : Blo 1136633 2887123 := bstep (se 1 (by rfl) ⟨2165342, by rfl⟩ : syracuseStep 2887123 = 4330685) B4330685
theorem B2559455 : Blo 1136633 2559455 := bstep (se 1 (by rfl) ⟨1919591, by rfl⟩ : syracuseStep 2559455 = 3839183) B3839183
theorem B1707743 : Blo 1136633 1707743 := bstep (se 1 (by rfl) ⟨1280807, by rfl⟩ : syracuseStep 1707743 = 2561615) B2561615
theorem B1708025 : Blo 1136633 1708025 := bstep (se 2 (by rfl) ⟨640509, by rfl⟩ : syracuseStep 1708025 = 1281019) B1281019
theorem B3838049 : Blo 1136633 3838049 := bstep (se 2 (by rfl) ⟨1439268, by rfl⟩ : syracuseStep 3838049 = 2878537) B2878537
theorem B1708223 : Blo 1136633 1708223 := bstep (se 1 (by rfl) ⟨1281167, by rfl⟩ : syracuseStep 1708223 = 2562335) B2562335
theorem B1708265 : Blo 1136633 1708265 := bstep (se 2 (by rfl) ⟨640599, by rfl⟩ : syracuseStep 1708265 = 1281199) B1281199
theorem B2593063 : Blo 1136633 2593063 := bstep (se 1 (by rfl) ⟨1944797, by rfl⟩ : syracuseStep 2593063 = 3889595) B3889595
theorem B1708391 : Blo 1136633 1708391 := bstep (se 1 (by rfl) ⟨1281293, by rfl⟩ : syracuseStep 1708391 = 2562587) B2562587
theorem B3117469 : Blo 1136633 3117469 := bstep (se 3 (by rfl) ⟨584525, by rfl⟩ : syracuseStep 3117469 = 1169051) B1169051
theorem B2560463 : Blo 1136633 2560463 := bstep (se 1 (by rfl) ⟨1920347, by rfl⟩ : syracuseStep 2560463 = 3840695) B3840695
theorem B1872431 : Blo 1136633 1872431 := bstep (se 1 (by rfl) ⟨1404323, by rfl⟩ : syracuseStep 1872431 = 2808647) B2808647
theorem B3838589 : Blo 1136633 3838589 := bstep (se 3 (by rfl) ⟨719735, by rfl⟩ : syracuseStep 3838589 = 1439471) B1439471
theorem B2921465 : Blo 1136633 2921465 := bstep (se 2 (by rfl) ⟨1095549, by rfl⟩ : syracuseStep 2921465 = 2191099) B2191099
theorem B5837993 : Blo 1136633 5837993 := bstep (se 2 (by rfl) ⟨2189247, by rfl⟩ : syracuseStep 5837993 = 4378495) B4378495
theorem B1709225 : Blo 1136633 1709225 := bstep (se 2 (by rfl) ⟨640959, by rfl⟩ : syracuseStep 1709225 = 1281919) B1281919
theorem B1709291 : Blo 1136633 1709291 := bstep (se 1 (by rfl) ⟨1281968, by rfl⟩ : syracuseStep 1709291 = 2563937) B2563937
theorem B1709375 : Blo 1136633 1709375 := bstep (se 1 (by rfl) ⟨1282031, by rfl⟩ : syracuseStep 1709375 = 2564063) B2564063
theorem B1709567 : Blo 1136633 1709567 := bstep (se 1 (by rfl) ⟨1282175, by rfl⟩ : syracuseStep 1709567 = 2564351) B2564351
theorem B3839507 : Blo 1136633 3839507 := bstep (se 1 (by rfl) ⟨2879630, by rfl⟩ : syracuseStep 3839507 = 5759261) B5759261
theorem B1709675 : Blo 1136633 1709675 := bstep (se 1 (by rfl) ⟨1282256, by rfl⟩ : syracuseStep 1709675 = 2564513) B2564513
theorem B5478025 : Blo 1136633 5478025 := bstep (se 2 (by rfl) ⟨2054259, by rfl⟩ : syracuseStep 5478025 = 4108519) B4108519
theorem B1709945 : Blo 1136633 1709945 := bstep (se 2 (by rfl) ⟨641229, by rfl⟩ : syracuseStep 1709945 = 1282459) B1282459
theorem B2430919 : Blo 1136633 2430919 := bstep (se 1 (by rfl) ⟨1823189, by rfl⟩ : syracuseStep 2430919 = 3646379) B3646379
theorem B1710191 : Blo 1136633 1710191 := bstep (se 1 (by rfl) ⟨1282643, by rfl⟩ : syracuseStep 1710191 = 2565287) B2565287
theorem B1710263 : Blo 1136633 1710263 := bstep (se 1 (by rfl) ⟨1282697, by rfl⟩ : syracuseStep 1710263 = 2565395) B2565395
theorem B9738575 : Blo 1136633 9738575 := bstep (se 1 (by rfl) ⟨7303931, by rfl⟩ : syracuseStep 9738575 = 14607863) B14607863
theorem B1710683 : Blo 1136633 1710683 := bstep (se 1 (by rfl) ⟨1283012, by rfl⟩ : syracuseStep 1710683 = 2566025) B2566025
theorem B1710695 : Blo 1136633 1710695 := bstep (se 1 (by rfl) ⟨1283021, by rfl⟩ : syracuseStep 1710695 = 2566043) B2566043
theorem B1710719 : Blo 1136633 1710719 := bstep (se 1 (by rfl) ⟨1283039, by rfl⟩ : syracuseStep 1710719 = 2566079) B2566079
theorem B1710827 : Blo 1136633 1710827 := bstep (se 1 (by rfl) ⟨1283120, by rfl⟩ : syracuseStep 1710827 = 2566241) B2566241
theorem B2431739 : Blo 1136633 2431739 := bstep (se 1 (by rfl) ⟨1823804, by rfl⟩ : syracuseStep 2431739 = 3647609) B3647609
theorem B1710857 : Blo 1136633 1710857 := bstep (se 2 (by rfl) ⟨641571, by rfl⟩ : syracuseStep 1710857 = 1283143) B1283143
theorem B2562857 : Blo 1136633 2562857 := bstep (se 2 (by rfl) ⟨961071, by rfl⟩ : syracuseStep 2562857 = 1922143) B1922143
theorem B5479255 : Blo 1136633 5479255 := bstep (se 1 (by rfl) ⟨4109441, by rfl⟩ : syracuseStep 5479255 = 8218883) B8218883
theorem B12327983 : Blo 1136633 12327983 := bstep (se 1 (by rfl) ⟨9245987, by rfl⟩ : syracuseStep 12327983 = 18491975) B18491975
theorem B2563127 : Blo 1136633 2563127 := bstep (se 1 (by rfl) ⟨1922345, by rfl⟩ : syracuseStep 2563127 = 3844691) B3844691
theorem B6495551 : Blo 1136633 6495551 := bstep (se 1 (by rfl) ⟨4871663, by rfl⟩ : syracuseStep 6495551 = 9743327) B9743327
theorem B4857259 : Blo 1136633 4857259 := bstep (se 1 (by rfl) ⟨3642944, by rfl⟩ : syracuseStep 4857259 = 7285889) B7285889
theorem B53222831 : Blo 1136633 53222831 := bstep (se 1 (by rfl) ⟨39917123, by rfl⟩ : syracuseStep 53222831 = 79834247) B79834247
theorem B44375849 : Blo 1136633 44375849 := bstep (se 2 (by rfl) ⟨16640943, by rfl⟩ : syracuseStep 44375849 = 33281887) B33281887
theorem B2563919 : Blo 1136633 2563919 := bstep (se 1 (by rfl) ⟨1922939, by rfl⟩ : syracuseStep 2563919 = 3845879) B3845879
theorem B2564279 : Blo 1136633 2564279 := bstep (se 1 (by rfl) ⟨1923209, by rfl⟩ : syracuseStep 2564279 = 3846419) B3846419
theorem B65544389 : Blo 1136633 65544389 := bstep (se 4 (by rfl) ⟨6144786, by rfl⟩ : syracuseStep 65544389 = 12289573) B12289573
theorem B2564639 : Blo 1136633 2564639 := bstep (se 1 (by rfl) ⟨1923479, by rfl⟩ : syracuseStep 2564639 = 3846959) B3846959
theorem B2433577 : Blo 1136633 2433577 := bstep (se 2 (by rfl) ⟨912591, by rfl⟩ : syracuseStep 2433577 = 1825183) B1825183
theorem B2565215 : Blo 1136633 2565215 := bstep (se 1 (by rfl) ⟨1923911, by rfl⟩ : syracuseStep 2565215 = 3847823) B3847823
theorem B2565467 : Blo 1136633 2565467 := bstep (se 1 (by rfl) ⟨1924100, by rfl⟩ : syracuseStep 2565467 = 3848201) B3848201
theorem B3843611 : Blo 1136633 3843611 := bstep (se 1 (by rfl) ⟨2882708, by rfl⟩ : syracuseStep 3843611 = 5765417) B5765417
theorem B2565737 : Blo 1136633 2565737 := bstep (se 2 (by rfl) ⟨962151, by rfl⟩ : syracuseStep 2565737 = 1924303) B1924303
theorem B55387961 : Blo 1136633 55387961 := bstep (se 2 (by rfl) ⟨20770485, by rfl⟩ : syracuseStep 55387961 = 41540971) B41540971
theorem B2566367 : Blo 1136633 2566367 := bstep (se 1 (by rfl) ⟨1924775, by rfl⟩ : syracuseStep 2566367 = 3849551) B3849551
theorem B41494841 : Blo 1136633 41494841 := bstep (se 2 (by rfl) ⟨15560565, by rfl⟩ : syracuseStep 41494841 = 31121131) B31121131
theorem B3648019 : Blo 1136633 3648019 := bstep (se 1 (by rfl) ⟨2736014, by rfl⟩ : syracuseStep 3648019 = 5472029) B5472029
theorem B3845609 : Blo 1136633 3845609 := bstep (se 2 (by rfl) ⟨1442103, by rfl⟩ : syracuseStep 3845609 = 2884207) B2884207
theorem B3845663 : Blo 1136633 3845663 := bstep (se 1 (by rfl) ⟨2884247, by rfl⟩ : syracuseStep 3845663 = 5768495) B5768495
theorem B3649249 : Blo 1136633 3649249 := bstep (se 2 (by rfl) ⟨1368468, by rfl⟩ : syracuseStep 3649249 = 2736937) B2736937
theorem B4108751 : Blo 1136633 4108751 := bstep (se 1 (by rfl) ⟨3081563, by rfl⟩ : syracuseStep 4108751 = 6163127) B6163127
theorem B7287479 : Blo 1136633 7287479 := bstep (se 1 (by rfl) ⟨5465609, by rfl⟩ : syracuseStep 7287479 = 10931219) B10931219
theorem B9712331 : Blo 1136633 9712331 := bstep (se 1 (by rfl) ⟨7284248, by rfl⟩ : syracuseStep 9712331 = 14568497) B14568497
theorem B5845769 : Blo 1136633 5845769 := bstep (se 2 (by rfl) ⟨2192163, by rfl⟩ : syracuseStep 5845769 = 4384327) B4384327
theorem B49165217 : Blo 1136633 49165217 := bstep (se 2 (by rfl) ⟨18436956, by rfl⟩ : syracuseStep 49165217 = 36873913) B36873913
theorem B8205275 : Blo 1136633 8205275 := bstep (se 1 (by rfl) ⟨6153956, by rfl⟩ : syracuseStep 8205275 = 12307913) B12307913
theorem B31143017 : Blo 1136633 31143017 := bstep (se 2 (by rfl) ⟨11678631, by rfl⟩ : syracuseStep 31143017 = 23357263) B23357263
theorem B5190979 : Blo 1136633 5190979 := bstep (se 1 (by rfl) ⟨3893234, by rfl⟩ : syracuseStep 5190979 = 7786469) B7786469
theorem B12498295 : Blo 1136633 12498295 := bstep (se 1 (by rfl) ⟨9373721, by rfl⟩ : syracuseStep 12498295 = 18747443) B18747443
theorem B2733439 : Blo 1136633 2733439 := bstep (se 1 (by rfl) ⟨2050079, by rfl⟩ : syracuseStep 2733439 = 4100159) B4100159
theorem B13154723 : Blo 1136633 13154723 := bstep (se 1 (by rfl) ⟨9866042, by rfl⟩ : syracuseStep 13154723 = 19732085) B19732085
theorem B172964585 : Blo 1136633 172964585 := bstep (se 2 (by rfl) ⟨64861719, by rfl⟩ : syracuseStep 172964585 = 129723439) B129723439
theorem B3848957 : Blo 1136633 3848957 := bstep (se 3 (by rfl) ⟨721679, by rfl⟩ : syracuseStep 3848957 = 1443359) B1443359
theorem B6572177 : Blo 1136633 6572177 := bstep (se 2 (by rfl) ⟨2464566, by rfl⟩ : syracuseStep 6572177 = 4929133) B4929133
theorem B10373417 : Blo 1136633 10373417 := bstep (se 2 (by rfl) ⟨3890031, by rfl⟩ : syracuseStep 10373417 = 7780063) B7780063
theorem B8637191 : Blo 1136633 8637191 := bstep (se 1 (by rfl) ⟨6477893, by rfl⟩ : syracuseStep 8637191 = 12955787) B12955787
theorem B7392235 : Blo 1136633 7392235 := bstep (se 1 (by rfl) ⟨5544176, by rfl⟩ : syracuseStep 7392235 = 11088353) B11088353
theorem B12307565 : Blo 1136633 12307565 := bstep (se 3 (by rfl) ⟨2307668, by rfl⟩ : syracuseStep 12307565 = 4615337) B4615337
theorem B36916469 : Blo 1136633 36916469 := bstep (se 5 (by rfl) ⟨1730459, by rfl⟩ : syracuseStep 36916469 = 3460919) B3460919
theorem B10931719 : Blo 1136633 10931719 := bstep (se 1 (by rfl) ⟨8198789, by rfl⟩ : syracuseStep 10931719 = 16397579) B16397579
theorem B5754401 : Blo 1136633 5754401 := bstep (se 2 (by rfl) ⟨2157900, by rfl⟩ : syracuseStep 5754401 = 4315801) B4315801
theorem B5624657 : Blo 1136633 5624657 := bstep (se 2 (by rfl) ⟨2109246, by rfl⟩ : syracuseStep 5624657 = 4218493) B4218493
theorem B1922015 : Blo 1136633 1922015 := bstep (se 1 (by rfl) ⟨1441511, by rfl⟩ : syracuseStep 1922015 = 2883023) B2883023
theorem B37966927 : Blo 1136633 37966927 := bstep (se 1 (by rfl) ⟨28475195, by rfl⟩ : syracuseStep 37966927 = 56950391) B56950391
theorem B62314055 : Blo 1136633 62314055 := bstep (se 1 (by rfl) ⟨46735541, by rfl⟩ : syracuseStep 62314055 = 93471083) B93471083
theorem B7296911 : Blo 1136633 7296911 := bstep (se 1 (by rfl) ⟨5472683, by rfl⟩ : syracuseStep 7296911 = 10945367) B10945367
theorem B5756831 : Blo 1136633 5756831 := bstep (se 1 (by rfl) ⟨4317623, by rfl⟩ : syracuseStep 5756831 = 8635247) B8635247
theorem B1136767 : Blo 1136633 1136767 := bstep (se 1 (by rfl) ⟨852575, by rfl⟩ : syracuseStep 1136767 = 1705151) B1705151
theorem B1136863 : Blo 1136633 1136863 := bstep (se 1 (by rfl) ⟨852647, by rfl⟩ : syracuseStep 1136863 = 1705295) B1705295
theorem B1136923 : Blo 1136633 1136923 := bstep (se 1 (by rfl) ⟨852692, by rfl⟩ : syracuseStep 1136923 = 1705385) B1705385
theorem B16439611 : Blo 1136633 16439611 := bstep (se 1 (by rfl) ⟨12329708, by rfl⟩ : syracuseStep 16439611 = 24659417) B24659417
theorem B24664439 : Blo 1136633 24664439 := bstep (se 1 (by rfl) ⟨18498329, by rfl⟩ : syracuseStep 24664439 = 36996659) B36996659
theorem B1137023 : Blo 1136633 1137023 := bstep (se 1 (by rfl) ⟨852767, by rfl⟩ : syracuseStep 1137023 = 1705535) B1705535
theorem B1137051 : Blo 1136633 1137051 := bstep (se 1 (by rfl) ⟨852788, by rfl⟩ : syracuseStep 1137051 = 1705577) B1705577
theorem B1366427 : Blo 1136633 1366427 := bstep (se 1 (by rfl) ⟨1024820, by rfl⟩ : syracuseStep 1366427 = 2049641) B2049641
theorem B1923743 : Blo 1136633 1923743 := bstep (se 1 (by rfl) ⟨1442807, by rfl⟩ : syracuseStep 1923743 = 2885615) B2885615
theorem B1137343 : Blo 1136633 1137343 := bstep (se 1 (by rfl) ⟨853007, by rfl⟩ : syracuseStep 1137343 = 1706015) B1706015
theorem B1137471 : Blo 1136633 1137471 := bstep (se 1 (by rfl) ⟨853103, by rfl⟩ : syracuseStep 1137471 = 1706207) B1706207
theorem B1137511 : Blo 1136633 1137511 := bstep (se 1 (by rfl) ⟨853133, by rfl⟩ : syracuseStep 1137511 = 1706267) B1706267
theorem B1137727 : Blo 1136633 1137727 := bstep (se 1 (by rfl) ⟨853295, by rfl⟩ : syracuseStep 1137727 = 1706591) B1706591
theorem B1137915 : Blo 1136633 1137915 := bstep (se 1 (by rfl) ⟨853436, by rfl⟩ : syracuseStep 1137915 = 1706873) B1706873
theorem B1137947 : Blo 1136633 1137947 := bstep (se 1 (by rfl) ⟨853460, by rfl⟩ : syracuseStep 1137947 = 1706921) B1706921
theorem B1138047 : Blo 1136633 1138047 := bstep (se 1 (by rfl) ⟨853535, by rfl⟩ : syracuseStep 1138047 = 1707071) B1707071
theorem B1138415 : Blo 1136633 1138415 := bstep (se 1 (by rfl) ⟨853811, by rfl⟩ : syracuseStep 1138415 = 1707623) B1707623
theorem B1138671 : Blo 1136633 1138671 := bstep (se 1 (by rfl) ⟨854003, by rfl⟩ : syracuseStep 1138671 = 1708007) B1708007
theorem B1138751 : Blo 1136633 1138751 := bstep (se 1 (by rfl) ⟨854063, by rfl⟩ : syracuseStep 1138751 = 1708127) B1708127
theorem B1138759 : Blo 1136633 1138759 := bstep (se 1 (by rfl) ⟨854069, by rfl⟩ : syracuseStep 1138759 = 1708139) B1708139
theorem B1499239 : Blo 1136633 1499239 := bstep (se 1 (by rfl) ⟨1124429, by rfl⟩ : syracuseStep 1499239 = 2248859) B2248859
theorem B1138791 : Blo 1136633 1138791 := bstep (se 1 (by rfl) ⟨854093, by rfl⟩ : syracuseStep 1138791 = 1708187) B1708187
theorem B5759099 : Blo 1136633 5759099 := bstep (se 1 (by rfl) ⟨4319324, by rfl⟩ : syracuseStep 5759099 = 8638649) B8638649
theorem B8643023 : Blo 1136633 8643023 := bstep (se 1 (by rfl) ⟨6482267, by rfl⟩ : syracuseStep 8643023 = 12964535) B12964535
theorem B14016979 : Blo 1136633 14016979 := bstep (se 1 (by rfl) ⟨10512734, by rfl⟩ : syracuseStep 14016979 = 21025469) B21025469
theorem B14606837 : Blo 1136633 14606837 := bstep (se 5 (by rfl) ⟨684695, by rfl⟩ : syracuseStep 14606837 = 1369391) B1369391
theorem B3465871 : Blo 1136633 3465871 := bstep (se 1 (by rfl) ⟨2599403, by rfl⟩ : syracuseStep 3465871 = 5198807) B5198807
theorem B1139359 : Blo 1136633 1139359 := bstep (se 1 (by rfl) ⟨854519, by rfl⟩ : syracuseStep 1139359 = 1709039) B1709039
theorem B59138909 : Blo 1136633 59138909 := bstep (se 3 (by rfl) ⟨11088545, by rfl⟩ : syracuseStep 59138909 = 22177091) B22177091
theorem B7398287 : Blo 1136633 7398287 := bstep (se 1 (by rfl) ⟨5548715, by rfl⟩ : syracuseStep 7398287 = 11097431) B11097431
theorem B1729439 : Blo 1136633 1729439 := bstep (se 1 (by rfl) ⟨1297079, by rfl⟩ : syracuseStep 1729439 = 2594159) B2594159
theorem B1139615 : Blo 1136633 1139615 := bstep (se 1 (by rfl) ⟨854711, by rfl⟩ : syracuseStep 1139615 = 1709423) B1709423
theorem B1139695 : Blo 1136633 1139695 := bstep (se 1 (by rfl) ⟨854771, by rfl⟩ : syracuseStep 1139695 = 1709543) B1709543
theorem B1139803 : Blo 1136633 1139803 := bstep (se 1 (by rfl) ⟨854852, by rfl⟩ : syracuseStep 1139803 = 1709705) B1709705
theorem B1139815 : Blo 1136633 1139815 := bstep (se 1 (by rfl) ⟨854861, by rfl⟩ : syracuseStep 1139815 = 1709723) B1709723
theorem B1139943 : Blo 1136633 1139943 := bstep (se 1 (by rfl) ⟨854957, by rfl⟩ : syracuseStep 1139943 = 1709915) B1709915
theorem B1140199 : Blo 1136633 1140199 := bstep (se 1 (by rfl) ⟨855149, by rfl⟩ : syracuseStep 1140199 = 1710299) B1710299
theorem B1140379 : Blo 1136633 1140379 := bstep (se 1 (by rfl) ⟨855284, by rfl⟩ : syracuseStep 1140379 = 1710569) B1710569
theorem B3237695 : Blo 1136633 3237695 := bstep (se 1 (by rfl) ⟨2428271, by rfl⟩ : syracuseStep 3237695 = 4856543) B4856543
theorem B9726479 : Blo 1136633 9726479 := bstep (se 1 (by rfl) ⟨7294859, by rfl⟩ : syracuseStep 9726479 = 14589719) B14589719
theorem B3238537 : Blo 1136633 3238537 := bstep (se 2 (by rfl) ⟨1214451, by rfl⟩ : syracuseStep 3238537 = 2428903) B2428903
theorem B3238663 : Blo 1136633 3238663 := bstep (se 1 (by rfl) ⟨2428997, by rfl⟩ : syracuseStep 3238663 = 4857995) B4857995
theorem B3238697 : Blo 1136633 3238697 := bstep (se 2 (by rfl) ⟨1214511, by rfl⟩ : syracuseStep 3238697 = 2429023) B2429023
theorem B7301983 : Blo 1136633 7301983 := bstep (se 1 (by rfl) ⟨5476487, by rfl⟩ : syracuseStep 7301983 = 10952975) B10952975
theorem B6483361 : Blo 1136633 6483361 := bstep (se 2 (by rfl) ⟨2431260, by rfl⟩ : syracuseStep 6483361 = 4862521) B4862521
theorem B7401041 : Blo 1136633 7401041 := bstep (se 2 (by rfl) ⟨2775390, by rfl⟩ : syracuseStep 7401041 = 5550781) B5550781
theorem B14610527 : Blo 1136633 14610527 := bstep (se 1 (by rfl) ⟨10957895, by rfl⟩ : syracuseStep 14610527 = 21915791) B21915791
theorem B3240155 : Blo 1136633 3240155 := bstep (se 1 (by rfl) ⟨2430116, by rfl⟩ : syracuseStep 3240155 = 4860233) B4860233
theorem B4321907 : Blo 1136633 4321907 := bstep (se 1 (by rfl) ⟨3241430, by rfl⟩ : syracuseStep 4321907 = 6482861) B6482861
theorem B5468953 : Blo 1136633 5468953 := bstep (se 2 (by rfl) ⟨2050857, by rfl⟩ : syracuseStep 5468953 = 4101715) B4101715
theorem B2880319 : Blo 1136633 2880319 := bstep (se 1 (by rfl) ⟨2160239, by rfl⟩ : syracuseStep 2880319 = 4320479) B4320479
theorem B1438555 : Blo 1136633 1438555 := bstep (se 1 (by rfl) ⟨1078916, by rfl⟩ : syracuseStep 1438555 = 2157833) B2157833
theorem B3076969 : Blo 1136633 3076969 := bstep (se 2 (by rfl) ⟨1153863, by rfl⟩ : syracuseStep 3076969 = 2307727) B2307727
theorem B5763959 : Blo 1136633 5763959 := bstep (se 1 (by rfl) ⟨4322969, by rfl⟩ : syracuseStep 5763959 = 8645939) B8645939
theorem B2880481 : Blo 1136633 2880481 := bstep (se 2 (by rfl) ⟨1080180, by rfl⟩ : syracuseStep 2880481 = 2160361) B2160361
theorem B43774991 : Blo 1136633 43774991 := bstep (se 1 (by rfl) ⟨32831243, by rfl⟩ : syracuseStep 43774991 = 65662487) B65662487
theorem B12317777 : Blo 1136633 12317777 := bstep (se 2 (by rfl) ⟨4619166, by rfl⟩ : syracuseStep 12317777 = 9238333) B9238333
theorem B6485345 : Blo 1136633 6485345 := bstep (se 2 (by rfl) ⟨2432004, by rfl⟩ : syracuseStep 6485345 = 4864009) B4864009
theorem B7304701 : Blo 1136633 7304701 := bstep (se 3 (by rfl) ⟨1369631, by rfl⟩ : syracuseStep 7304701 = 2739263) B2739263
theorem B2160695 : Blo 1136633 2160695 := bstep (se 1 (by rfl) ⟨1620521, by rfl⟩ : syracuseStep 2160695 = 3241043) B3241043
theorem B2881727 : Blo 1136633 2881727 := bstep (se 1 (by rfl) ⟨2161295, by rfl⟩ : syracuseStep 2881727 = 4322591) B4322591
theorem B2881889 : Blo 1136633 2881889 := bstep (se 2 (by rfl) ⟨1080708, by rfl⟩ : syracuseStep 2881889 = 2161417) B2161417
theorem B3242729 : Blo 1136633 3242729 := bstep (se 2 (by rfl) ⟨1216023, by rfl⟩ : syracuseStep 3242729 = 2432047) B2432047
theorem B2882587 : Blo 1136633 2882587 := bstep (se 1 (by rfl) ⟨2161940, by rfl⟩ : syracuseStep 2882587 = 4323881) B4323881
theorem B2162153 : Blo 1136633 2162153 := bstep (se 2 (by rfl) ⟨810807, by rfl⟩ : syracuseStep 2162153 = 1621615) B1621615
theorem B3243503 : Blo 1136633 3243503 := bstep (se 1 (by rfl) ⟨2432627, by rfl⟩ : syracuseStep 3243503 = 4865255) B4865255
theorem B2883347 : Blo 1136633 2883347 := bstep (se 1 (by rfl) ⟨2162510, by rfl⟩ : syracuseStep 2883347 = 4325021) B4325021
theorem B1441567 : Blo 1136633 1441567 := bstep (se 1 (by rfl) ⟨1081175, by rfl⟩ : syracuseStep 1441567 = 2162351) B2162351
theorem B7995941 : Blo 1136633 7995941 := bstep (se 4 (by rfl) ⟨749619, by rfl⟩ : syracuseStep 7995941 = 1499239) B1499239
theorem B3244769 : Blo 1136633 3244769 := bstep (se 2 (by rfl) ⟨1216788, by rfl⟩ : syracuseStep 3244769 = 2433577) B2433577
theorem B4326281 : Blo 1136633 4326281 := bstep (se 2 (by rfl) ⟨1622355, by rfl⟩ : syracuseStep 4326281 = 3244711) B3244711
theorem B1705055 : Blo 1136633 1705055 := bstep (se 1 (by rfl) ⟨1278791, by rfl⟩ : syracuseStep 1705055 = 2557583) B2557583
theorem B1705115 : Blo 1136633 1705115 := bstep (se 1 (by rfl) ⟨1278836, by rfl⟩ : syracuseStep 1705115 = 2557673) B2557673
theorem B6915611 : Blo 1136633 6915611 := bstep (se 1 (by rfl) ⟨5186708, by rfl⟩ : syracuseStep 6915611 = 10373417) B10373417
theorem B2164295 : Blo 1136633 2164295 := bstep (se 1 (by rfl) ⟨1623221, by rfl⟩ : syracuseStep 2164295 = 3246443) B3246443
theorem B2557691 : Blo 1136633 2557691 := bstep (se 1 (by rfl) ⟨1918268, by rfl⟩ : syracuseStep 2557691 = 3836537) B3836537
theorem B24610979 : Blo 1136633 24610979 := bstep (se 1 (by rfl) ⟨18458234, by rfl⟩ : syracuseStep 24610979 = 36916469) B36916469
theorem B1706303 : Blo 1136633 1706303 := bstep (se 1 (by rfl) ⟨1279727, by rfl⟩ : syracuseStep 1706303 = 2559455) B2559455
theorem B3836267 : Blo 1136633 3836267 := bstep (se 1 (by rfl) ⟨2877200, by rfl⟩ : syracuseStep 3836267 = 5754401) B5754401
theorem B5769953 : Blo 1136633 5769953 := bstep (se 2 (by rfl) ⟨2163732, by rfl⟩ : syracuseStep 5769953 = 4327465) B4327465
theorem B2558699 : Blo 1136633 2558699 := bstep (se 1 (by rfl) ⟨1919024, by rfl⟩ : syracuseStep 2558699 = 3838049) B3838049
theorem B2886425 : Blo 1136633 2886425 := bstep (se 2 (by rfl) ⟨1082409, by rfl⟩ : syracuseStep 2886425 = 2164819) B2164819
theorem B1706975 : Blo 1136633 1706975 := bstep (se 1 (by rfl) ⟨1280231, by rfl⟩ : syracuseStep 1706975 = 2560463) B2560463
theorem B1248287 : Blo 1136633 1248287 := bstep (se 1 (by rfl) ⟨936215, by rfl⟩ : syracuseStep 1248287 = 1872431) B1872431
theorem B2559059 : Blo 1136633 2559059 := bstep (se 1 (by rfl) ⟨1919294, by rfl⟩ : syracuseStep 2559059 = 3838589) B3838589
theorem B1281343 : Blo 1136633 1281343 := bstep (se 1 (by rfl) ⟨961007, by rfl⟩ : syracuseStep 1281343 = 1922015) B1922015
theorem B18484645 : Blo 1136633 18484645 := bstep (se 4 (by rfl) ⟨1732935, by rfl⟩ : syracuseStep 18484645 = 3465871) B3465871
theorem B2559671 : Blo 1136633 2559671 := bstep (se 1 (by rfl) ⟨1919753, by rfl⟩ : syracuseStep 2559671 = 3839507) B3839507
theorem B9735977 : Blo 1136633 9735977 := bstep (se 2 (by rfl) ⟨3650991, by rfl⟩ : syracuseStep 9735977 = 7301983) B7301983
theorem B3837887 : Blo 1136633 3837887 := bstep (se 1 (by rfl) ⟨2878415, by rfl⟩ : syracuseStep 3837887 = 5756831) B5756831
theorem B6492383 : Blo 1136633 6492383 := bstep (se 1 (by rfl) ⟨4869287, by rfl⟩ : syracuseStep 6492383 = 9738575) B9738575
theorem B1282495 : Blo 1136633 1282495 := bstep (se 1 (by rfl) ⟨961871, by rfl⟩ : syracuseStep 1282495 = 1923743) B1923743
theorem B1708571 : Blo 1136633 1708571 := bstep (se 1 (by rfl) ⟨1281428, by rfl⟩ : syracuseStep 1708571 = 2562857) B2562857
theorem B1708751 : Blo 1136633 1708751 := bstep (se 1 (by rfl) ⟨1281563, by rfl⟩ : syracuseStep 1708751 = 2563127) B2563127
theorem B4330367 : Blo 1136633 4330367 := bstep (se 1 (by rfl) ⟨3247775, by rfl⟩ : syracuseStep 4330367 = 6495551) B6495551
theorem B1709279 : Blo 1136633 1709279 := bstep (se 1 (by rfl) ⟨1281959, by rfl⟩ : syracuseStep 1709279 = 2563919) B2563919
theorem B3839399 : Blo 1136633 3839399 := bstep (se 1 (by rfl) ⟨2879549, by rfl⟩ : syracuseStep 3839399 = 5759099) B5759099
theorem B1709519 : Blo 1136633 1709519 := bstep (se 1 (by rfl) ⟨1282139, by rfl⟩ : syracuseStep 1709519 = 2564279) B2564279
theorem B9737891 : Blo 1136633 9737891 := bstep (se 1 (by rfl) ⟨7303418, by rfl⟩ : syracuseStep 9737891 = 14606837) B14606837
theorem B1709759 : Blo 1136633 1709759 := bstep (se 1 (by rfl) ⟨1282319, by rfl⟩ : syracuseStep 1709759 = 2564639) B2564639
theorem B39425939 : Blo 1136633 39425939 := bstep (se 1 (by rfl) ⟨29569454, by rfl⟩ : syracuseStep 39425939 = 59138909) B59138909
theorem B1152959 : Blo 1136633 1152959 := bstep (se 1 (by rfl) ⟨864719, by rfl⟩ : syracuseStep 1152959 = 1729439) B1729439
theorem B1710143 : Blo 1136633 1710143 := bstep (se 1 (by rfl) ⟨1282607, by rfl⟩ : syracuseStep 1710143 = 2565215) B2565215
theorem B1710311 : Blo 1136633 1710311 := bstep (se 1 (by rfl) ⟨1282733, by rfl⟩ : syracuseStep 1710311 = 2565467) B2565467
theorem B2562407 : Blo 1136633 2562407 := bstep (se 1 (by rfl) ⟨1921805, by rfl⟩ : syracuseStep 2562407 = 3843611) B3843611
theorem B1710491 : Blo 1136633 1710491 := bstep (se 1 (by rfl) ⟨1282868, by rfl⟩ : syracuseStep 1710491 = 2565737) B2565737
theorem B3643805 : Blo 1136633 3643805 := bstep (se 3 (by rfl) ⟨683213, by rfl⟩ : syracuseStep 3643805 = 1366427) B1366427
theorem B3840425 : Blo 1136633 3840425 := bstep (se 2 (by rfl) ⟨1440159, by rfl⟩ : syracuseStep 3840425 = 2880319) B2880319
theorem B4102625 : Blo 1136633 4102625 := bstep (se 2 (by rfl) ⟨1538484, by rfl⟩ : syracuseStep 4102625 = 3076969) B3076969
theorem B3840641 : Blo 1136633 3840641 := bstep (se 2 (by rfl) ⟨1440240, by rfl⟩ : syracuseStep 3840641 = 2880481) B2880481
theorem B1710911 : Blo 1136633 1710911 := bstep (se 1 (by rfl) ⟨1283183, by rfl⟩ : syracuseStep 1710911 = 2566367) B2566367
theorem B27663227 : Blo 1136633 27663227 := bstep (se 1 (by rfl) ⟨20747420, by rfl⟩ : syracuseStep 27663227 = 41494841) B41494841
theorem B6921305 : Blo 1136633 6921305 := bstep (se 2 (by rfl) ⟨2595489, by rfl⟩ : syracuseStep 6921305 = 5190979) B5190979
theorem B3644585 : Blo 1136633 3644585 := bstep (se 2 (by rfl) ⟨1366719, by rfl⟩ : syracuseStep 3644585 = 2733439) B2733439
theorem B9739601 : Blo 1136633 9739601 := bstep (se 2 (by rfl) ⟨3652350, by rfl⟩ : syracuseStep 9739601 = 7304701) B7304701
theorem B2563739 : Blo 1136633 2563739 := bstep (se 1 (by rfl) ⟨1922804, by rfl⟩ : syracuseStep 2563739 = 3845609) B3845609
theorem B2563775 : Blo 1136633 2563775 := bstep (se 1 (by rfl) ⟨1922831, by rfl⟩ : syracuseStep 2563775 = 3845663) B3845663
theorem B9740351 : Blo 1136633 9740351 := bstep (se 1 (by rfl) ⟨7305263, by rfl⟩ : syracuseStep 9740351 = 14610527) B14610527
theorem B4858319 : Blo 1136633 4858319 := bstep (se 1 (by rfl) ⟨3643739, by rfl⟩ : syracuseStep 4858319 = 7287479) B7287479
theorem B3842639 : Blo 1136633 3842639 := bstep (se 1 (by rfl) ⟨2881979, by rfl⟩ : syracuseStep 3842639 = 5763959) B5763959
theorem B32776811 : Blo 1136633 32776811 := bstep (se 1 (by rfl) ⟨24582608, by rfl⟩ : syracuseStep 32776811 = 49165217) B49165217
theorem B3843449 : Blo 1136633 3843449 := bstep (se 2 (by rfl) ⟨1441293, by rfl⟩ : syracuseStep 3843449 = 2882587) B2882587
theorem B2565971 : Blo 1136633 2565971 := bstep (se 1 (by rfl) ⟨1924478, by rfl⟩ : syracuseStep 2565971 = 3848957) B3848957
theorem B18689305 : Blo 1136633 18689305 := bstep (se 2 (by rfl) ⟨7008489, by rfl⟩ : syracuseStep 18689305 = 14016979) B14016979
theorem B3845447 : Blo 1136633 3845447 := bstep (se 1 (by rfl) ⟨2884085, by rfl⟩ : syracuseStep 3845447 = 5768171) B5768171
theorem B7778749 : Blo 1136633 7778749 := bstep (se 3 (by rfl) ⟨1458515, by rfl⟩ : syracuseStep 7778749 = 2917031) B2917031
theorem B6926879 : Blo 1136633 6926879 := bstep (se 1 (by rfl) ⟨5195159, by rfl⟩ : syracuseStep 6926879 = 10390319) B10390319
theorem B3749771 : Blo 1136633 3749771 := bstep (se 1 (by rfl) ⟨2812328, by rfl⟩ : syracuseStep 3749771 = 5624657) B5624657
theorem B4864025 : Blo 1136633 4864025 := bstep (se 2 (by rfl) ⟨1824009, by rfl⟩ : syracuseStep 4864025 = 3648019) B3648019
theorem B4864607 : Blo 1136633 4864607 := bstep (se 1 (by rfl) ⟨3648455, by rfl⟩ : syracuseStep 4864607 = 7296911) B7296911
theorem B3849497 : Blo 1136633 3849497 := bstep (se 2 (by rfl) ⟨1443561, by rfl⟩ : syracuseStep 3849497 = 2887123) B2887123
theorem B4865665 : Blo 1136633 4865665 := bstep (se 2 (by rfl) ⟨1824624, by rfl⟩ : syracuseStep 4865665 = 3649249) B3649249
theorem B43696259 : Blo 1136633 43696259 := bstep (se 1 (by rfl) ⟨32772194, by rfl⟩ : syracuseStep 43696259 = 65544389) B65544389
theorem B3457417 : Blo 1136633 3457417 := bstep (se 2 (by rfl) ⟨1296531, by rfl⟩ : syracuseStep 3457417 = 2593063) B2593063
theorem B4932191 : Blo 1136633 4932191 := bstep (se 1 (by rfl) ⟨3699143, by rfl⟩ : syracuseStep 4932191 = 7398287) B7398287
theorem B7291937 : Blo 1136633 7291937 := bstep (se 2 (by rfl) ⟨2734476, by rfl⟩ : syracuseStep 7291937 = 5468953) B5468953
theorem B1918073 : Blo 1136633 1918073 := bstep (se 2 (by rfl) ⟨719277, by rfl⟩ : syracuseStep 1918073 = 1438555) B1438555
theorem B16664393 : Blo 1136633 16664393 := bstep (se 2 (by rfl) ⟨6249147, by rfl⟩ : syracuseStep 16664393 = 12498295) B12498295
theorem B4934027 : Blo 1136633 4934027 := bstep (se 1 (by rfl) ⟨3700520, by rfl⟩ : syracuseStep 4934027 = 7401041) B7401041
theorem B32820173 : Blo 1136633 32820173 := bstep (se 3 (by rfl) ⟨6153782, by rfl⟩ : syracuseStep 32820173 = 12307565) B12307565
theorem B2739167 : Blo 1136633 2739167 := bstep (se 1 (by rfl) ⟨2054375, by rfl⟩ : syracuseStep 2739167 = 4108751) B4108751
theorem B6474887 : Blo 1136633 6474887 := bstep (se 1 (by rfl) ⟨4856165, by rfl⟩ : syracuseStep 6474887 = 9712331) B9712331
theorem B29183327 : Blo 1136633 29183327 := bstep (se 1 (by rfl) ⟨21887495, by rfl⟩ : syracuseStep 29183327 = 43774991) B43774991
theorem B8211851 : Blo 1136633 8211851 := bstep (se 1 (by rfl) ⟨6158888, by rfl⟩ : syracuseStep 8211851 = 12317777) B12317777
theorem B20762011 : Blo 1136633 20762011 := bstep (se 1 (by rfl) ⟨15571508, by rfl⟩ : syracuseStep 20762011 = 31143017) B31143017
theorem B1921151 : Blo 1136633 1921151 := bstep (se 1 (by rfl) ⟨1440863, by rfl⟩ : syracuseStep 1921151 = 2881727) B2881727
theorem B1921259 : Blo 1136633 1921259 := bstep (se 1 (by rfl) ⟨1440944, by rfl⟩ : syracuseStep 1921259 = 2881889) B2881889
theorem B8769815 : Blo 1136633 8769815 := bstep (se 1 (by rfl) ⟨6577361, by rfl⟩ : syracuseStep 8769815 = 13154723) B13154723
theorem B6476345 : Blo 1136633 6476345 := bstep (se 2 (by rfl) ⟨2428629, by rfl⟩ : syracuseStep 6476345 = 4857259) B4857259
theorem B1922089 : Blo 1136633 1922089 := bstep (se 2 (by rfl) ⟨720783, by rfl⟩ : syracuseStep 1922089 = 1441567) B1441567
theorem B1922231 : Blo 1136633 1922231 := bstep (se 1 (by rfl) ⟨1441673, by rfl⟩ : syracuseStep 1922231 = 2883347) B2883347
theorem B1922555 : Blo 1136633 1922555 := bstep (se 1 (by rfl) ⟨1441916, by rfl⟩ : syracuseStep 1922555 = 2883833) B2883833
theorem B19748431 : Blo 1136633 19748431 := bstep (se 1 (by rfl) ⟨14811323, by rfl⟩ : syracuseStep 19748431 = 29622647) B29622647
theorem B1922663 : Blo 1136633 1922663 := bstep (se 1 (by rfl) ⟨1441997, by rfl⟩ : syracuseStep 1922663 = 2883995) B2883995
theorem B3888815 : Blo 1136633 3888815 := bstep (se 1 (by rfl) ⟨2916611, by rfl⟩ : syracuseStep 3888815 = 5833223) B5833223
theorem B1922987 : Blo 1136633 1922987 := bstep (se 1 (by rfl) ⟨1442240, by rfl⟩ : syracuseStep 1922987 = 2884481) B2884481
theorem B1136667 : Blo 1136633 1136667 := bstep (se 1 (by rfl) ⟨852500, by rfl⟩ : syracuseStep 1136667 = 1705001) B1705001
theorem B1136687 : Blo 1136633 1136687 := bstep (se 1 (by rfl) ⟨852515, by rfl⟩ : syracuseStep 1136687 = 1705031) B1705031
theorem B1136807 : Blo 1136633 1136807 := bstep (se 1 (by rfl) ⟨852605, by rfl⟩ : syracuseStep 1136807 = 1705211) B1705211
theorem B1136999 : Blo 1136633 1136999 := bstep (se 1 (by rfl) ⟨852749, by rfl⟩ : syracuseStep 1136999 = 1705499) B1705499
theorem B1923527 : Blo 1136633 1923527 := bstep (se 1 (by rfl) ⟨1442645, by rfl⟩ : syracuseStep 1923527 = 2885291) B2885291
theorem B43735625 : Blo 1136633 43735625 := bstep (se 2 (by rfl) ⟨16400859, by rfl⟩ : syracuseStep 43735625 = 32801719) B32801719
theorem B1137255 : Blo 1136633 1137255 := bstep (se 1 (by rfl) ⟨852941, by rfl⟩ : syracuseStep 1137255 = 1705883) B1705883
theorem B1137279 : Blo 1136633 1137279 := bstep (se 1 (by rfl) ⟨852959, by rfl⟩ : syracuseStep 1137279 = 1705919) B1705919
theorem B4381451 : Blo 1136633 4381451 := bstep (se 1 (by rfl) ⟨3286088, by rfl⟩ : syracuseStep 4381451 = 6572177) B6572177
theorem B1137695 : Blo 1136633 1137695 := bstep (se 1 (by rfl) ⟨853271, by rfl⟩ : syracuseStep 1137695 = 1706543) B1706543
theorem B1137775 : Blo 1136633 1137775 := bstep (se 1 (by rfl) ⟨853331, by rfl⟩ : syracuseStep 1137775 = 1706663) B1706663
theorem B1137819 : Blo 1136633 1137819 := bstep (se 1 (by rfl) ⟨853364, by rfl⟩ : syracuseStep 1137819 = 1706729) B1706729
theorem B1137823 : Blo 1136633 1137823 := bstep (se 1 (by rfl) ⟨853367, by rfl⟩ : syracuseStep 1137823 = 1706735) B1706735
theorem B5758127 : Blo 1136633 5758127 := bstep (se 1 (by rfl) ⟨4318595, by rfl⟩ : syracuseStep 5758127 = 8637191) B8637191
theorem B1137855 : Blo 1136633 1137855 := bstep (se 1 (by rfl) ⟨853391, by rfl⟩ : syracuseStep 1137855 = 1706783) B1706783
theorem B1138075 : Blo 1136633 1138075 := bstep (se 1 (by rfl) ⟨853556, by rfl⟩ : syracuseStep 1138075 = 1707113) B1707113
theorem B1138159 : Blo 1136633 1138159 := bstep (se 1 (by rfl) ⟨853619, by rfl⟩ : syracuseStep 1138159 = 1707239) B1707239
theorem B1138495 : Blo 1136633 1138495 := bstep (se 1 (by rfl) ⟨853871, by rfl⟩ : syracuseStep 1138495 = 1707743) B1707743
theorem B7790573 : Blo 1136633 7790573 := bstep (se 3 (by rfl) ⟨1460732, by rfl⟩ : syracuseStep 7790573 = 2921465) B2921465
theorem B1138683 : Blo 1136633 1138683 := bstep (se 1 (by rfl) ⟨854012, by rfl⟩ : syracuseStep 1138683 = 1708025) B1708025
theorem B1138815 : Blo 1136633 1138815 := bstep (se 1 (by rfl) ⟨854111, by rfl⟩ : syracuseStep 1138815 = 1708223) B1708223
theorem B1138843 : Blo 1136633 1138843 := bstep (se 1 (by rfl) ⟨854132, by rfl⟩ : syracuseStep 1138843 = 1708265) B1708265
theorem B1138927 : Blo 1136633 1138927 := bstep (se 1 (by rfl) ⟨854195, by rfl⟩ : syracuseStep 1138927 = 1708391) B1708391
theorem B3891995 : Blo 1136633 3891995 := bstep (se 1 (by rfl) ⟨2918996, by rfl⟩ : syracuseStep 3891995 = 5837993) B5837993
theorem B1139483 : Blo 1136633 1139483 := bstep (se 1 (by rfl) ⟨854612, by rfl⟩ : syracuseStep 1139483 = 1709225) B1709225
theorem B1139527 : Blo 1136633 1139527 := bstep (se 1 (by rfl) ⟨854645, by rfl⟩ : syracuseStep 1139527 = 1709291) B1709291
theorem B4318049 : Blo 1136633 4318049 := bstep (se 2 (by rfl) ⟨1619268, by rfl⟩ : syracuseStep 4318049 = 3238537) B3238537
theorem B1139583 : Blo 1136633 1139583 := bstep (se 1 (by rfl) ⟨854687, by rfl⟩ : syracuseStep 1139583 = 1709375) B1709375
theorem B1139711 : Blo 1136633 1139711 := bstep (se 1 (by rfl) ⟨854783, by rfl⟩ : syracuseStep 1139711 = 1709567) B1709567
theorem B4318217 : Blo 1136633 4318217 := bstep (se 2 (by rfl) ⟨1619331, by rfl⟩ : syracuseStep 4318217 = 3238663) B3238663
theorem B41542703 : Blo 1136633 41542703 := bstep (se 1 (by rfl) ⟨31157027, by rfl⟩ : syracuseStep 41542703 = 62314055) B62314055
theorem B1139783 : Blo 1136633 1139783 := bstep (se 1 (by rfl) ⟨854837, by rfl⟩ : syracuseStep 1139783 = 1709675) B1709675
theorem B1139963 : Blo 1136633 1139963 := bstep (se 1 (by rfl) ⟨854972, by rfl⟩ : syracuseStep 1139963 = 1709945) B1709945
theorem B9856313 : Blo 1136633 9856313 := bstep (se 2 (by rfl) ⟨3696117, by rfl⟩ : syracuseStep 9856313 = 7392235) B7392235
theorem B1140127 : Blo 1136633 1140127 := bstep (se 1 (by rfl) ⟨855095, by rfl⟩ : syracuseStep 1140127 = 1710191) B1710191
theorem B1140175 : Blo 1136633 1140175 := bstep (se 1 (by rfl) ⟨855131, by rfl⟩ : syracuseStep 1140175 = 1710263) B1710263
theorem B16442959 : Blo 1136633 16442959 := bstep (se 1 (by rfl) ⟨12332219, by rfl⟩ : syracuseStep 16442959 = 24664439) B24664439
theorem B1140455 : Blo 1136633 1140455 := bstep (se 1 (by rfl) ⟨855341, by rfl⟩ : syracuseStep 1140455 = 1710683) B1710683
theorem B1140463 : Blo 1136633 1140463 := bstep (se 1 (by rfl) ⟨855347, by rfl⟩ : syracuseStep 1140463 = 1710695) B1710695
theorem B1140479 : Blo 1136633 1140479 := bstep (se 1 (by rfl) ⟨855359, by rfl⟩ : syracuseStep 1140479 = 1710719) B1710719
theorem B29222693 : Blo 1136633 29222693 := bstep (se 4 (by rfl) ⟨2739627, by rfl⟩ : syracuseStep 29222693 = 5479255) B5479255
theorem B1140551 : Blo 1136633 1140551 := bstep (se 1 (by rfl) ⟨855413, by rfl⟩ : syracuseStep 1140551 = 1710827) B1710827
theorem B1140571 : Blo 1136633 1140571 := bstep (se 1 (by rfl) ⟨855428, by rfl⟩ : syracuseStep 1140571 = 1710857) B1710857
theorem B8644481 : Blo 1136633 8644481 := bstep (se 2 (by rfl) ⟨3241680, by rfl⟩ : syracuseStep 8644481 = 6483361) B6483361
theorem B14575625 : Blo 1136633 14575625 := bstep (se 2 (by rfl) ⟨5465859, by rfl⟩ : syracuseStep 14575625 = 10931719) B10931719
theorem B8218655 : Blo 1136633 8218655 := bstep (se 1 (by rfl) ⟨6163991, by rfl⟩ : syracuseStep 8218655 = 12327983) B12327983
theorem B35481887 : Blo 1136633 35481887 := bstep (se 1 (by rfl) ⟨26611415, by rfl⟩ : syracuseStep 35481887 = 53222831) B53222831
theorem B29583899 : Blo 1136633 29583899 := bstep (se 1 (by rfl) ⟨22187924, by rfl⟩ : syracuseStep 29583899 = 44375849) B44375849
theorem B5761853 : Blo 1136633 5761853 := bstep (se 3 (by rfl) ⟨1080347, by rfl⟩ : syracuseStep 5761853 = 2160695) B2160695
theorem B5762015 : Blo 1136633 5762015 := bstep (se 1 (by rfl) ⟨4321511, by rfl⟩ : syracuseStep 5762015 = 8643023) B8643023
theorem B4156625 : Blo 1136633 4156625 := bstep (se 2 (by rfl) ⟨1558734, by rfl⟩ : syracuseStep 4156625 = 3117469) B3117469
theorem B36925307 : Blo 1136633 36925307 := bstep (se 1 (by rfl) ⟨27693980, by rfl⟩ : syracuseStep 36925307 = 55387961) B55387961
theorem B2158463 : Blo 1136633 2158463 := bstep (se 1 (by rfl) ⟨1618847, by rfl⟩ : syracuseStep 2158463 = 3237695) B3237695
theorem B50622569 : Blo 1136633 50622569 := bstep (se 2 (by rfl) ⟨18983463, by rfl⟩ : syracuseStep 50622569 = 37966927) B37966927
theorem B6484319 : Blo 1136633 6484319 := bstep (se 1 (by rfl) ⟨4863239, by rfl⟩ : syracuseStep 6484319 = 9726479) B9726479
theorem B2159131 : Blo 1136633 2159131 := bstep (se 1 (by rfl) ⟨1619348, by rfl⟩ : syracuseStep 2159131 = 3238697) B3238697
theorem B461238893 : Blo 1136633 461238893 := bstep (se 3 (by rfl) ⟨86482292, by rfl⟩ : syracuseStep 461238893 = 172964585) B172964585
theorem B6484637 : Blo 1136633 6484637 := bstep (se 3 (by rfl) ⟨1215869, by rfl⟩ : syracuseStep 6484637 = 2431739) B2431739
theorem B7304033 : Blo 1136633 7304033 := bstep (se 2 (by rfl) ⟨2739012, by rfl⟩ : syracuseStep 7304033 = 5478025) B5478025
theorem B3241225 : Blo 1136633 3241225 := bstep (se 2 (by rfl) ⟨1215459, by rfl⟩ : syracuseStep 3241225 = 2430919) B2430919
theorem B2160103 : Blo 1136633 2160103 := bstep (se 1 (by rfl) ⟨1620077, by rfl⟩ : syracuseStep 2160103 = 3240155) B3240155
theorem B2881271 : Blo 1136633 2881271 := bstep (se 1 (by rfl) ⟨2160953, by rfl⟩ : syracuseStep 2881271 = 4321907) B4321907
theorem B21919481 : Blo 1136633 21919481 := bstep (se 2 (by rfl) ⟨8219805, by rfl⟩ : syracuseStep 21919481 = 16439611) B16439611
theorem B3897179 : Blo 1136633 3897179 := bstep (se 1 (by rfl) ⟨2922884, by rfl⟩ : syracuseStep 3897179 = 5845769) B5845769
theorem B5470183 : Blo 1136633 5470183 := bstep (se 1 (by rfl) ⟨4102637, by rfl⟩ : syracuseStep 5470183 = 8205275) B8205275
theorem B4323563 : Blo 1136633 4323563 := bstep (se 1 (by rfl) ⟨3242672, by rfl⟩ : syracuseStep 4323563 = 6485345) B6485345
theorem B5765741 : Blo 1136633 5765741 := bstep (se 3 (by rfl) ⟨1081076, by rfl⟩ : syracuseStep 5765741 = 2162153) B2162153
theorem B8649341 : Blo 1136633 8649341 := bstep (se 3 (by rfl) ⟨1621751, by rfl⟩ : syracuseStep 8649341 = 3243503) B3243503
theorem B2161819 : Blo 1136633 2161819 := bstep (se 1 (by rfl) ⟨1621364, by rfl⟩ : syracuseStep 2161819 = 3242729) B3242729
theorem B29130839 : Blo 1136633 29130839 := bstep (se 1 (by rfl) ⟨21848129, by rfl⟩ : syracuseStep 29130839 = 43696259) B43696259
theorem B2163179 : Blo 1136633 2163179 := bstep (se 1 (by rfl) ⟨1622384, by rfl⟩ : syracuseStep 2163179 = 3244769) B3244769
theorem B2884187 : Blo 1136633 2884187 := bstep (se 1 (by rfl) ⟨2163140, by rfl⟩ : syracuseStep 2884187 = 4326281) B4326281
theorem B1278715 : Blo 1136633 1278715 := bstep (se 1 (by rfl) ⟨959036, by rfl⟩ : syracuseStep 1278715 = 1918073) B1918073
theorem B1442863 : Blo 1136633 1442863 := bstep (se 1 (by rfl) ⟨1082147, by rfl⟩ : syracuseStep 1442863 = 2164295) B2164295
theorem B1705127 : Blo 1136633 1705127 := bstep (se 1 (by rfl) ⟨1278845, by rfl⟩ : syracuseStep 1705127 = 2557691) B2557691
theorem B11109595 : Blo 1136633 11109595 := bstep (se 1 (by rfl) ⟨8332196, by rfl⟩ : syracuseStep 11109595 = 16664393) B16664393
theorem B2557511 : Blo 1136633 2557511 := bstep (se 1 (by rfl) ⟨1918133, by rfl⟩ : syracuseStep 2557511 = 3836267) B3836267
theorem B1705799 : Blo 1136633 1705799 := bstep (se 1 (by rfl) ⟨1279349, by rfl⟩ : syracuseStep 1705799 = 2558699) B2558699
theorem B1706039 : Blo 1136633 1706039 := bstep (se 1 (by rfl) ⟨1279529, by rfl⟩ : syracuseStep 1706039 = 2559059) B2559059
theorem B21923945 : Blo 1136633 21923945 := bstep (se 2 (by rfl) ⟨8221479, by rfl⟩ : syracuseStep 21923945 = 16442959) B16442959
theorem B5474567 : Blo 1136633 5474567 := bstep (se 1 (by rfl) ⟨4105925, by rfl⟩ : syracuseStep 5474567 = 8211851) B8211851
theorem B1706447 : Blo 1136633 1706447 := bstep (se 1 (by rfl) ⟨1279835, by rfl⟩ : syracuseStep 1706447 = 2559671) B2559671
theorem B6490651 : Blo 1136633 6490651 := bstep (se 1 (by rfl) ⟨4867988, by rfl⟩ : syracuseStep 6490651 = 9735977) B9735977
theorem B2558591 : Blo 1136633 2558591 := bstep (se 1 (by rfl) ⟨1918943, by rfl⟩ : syracuseStep 2558591 = 3837887) B3837887
theorem B1280767 : Blo 1136633 1280767 := bstep (se 1 (by rfl) ⟨960575, by rfl⟩ : syracuseStep 1280767 = 1921151) B1921151
theorem B4328255 : Blo 1136633 4328255 := bstep (se 1 (by rfl) ⟨3246191, by rfl⟩ : syracuseStep 4328255 = 6492383) B6492383
theorem B1280839 : Blo 1136633 1280839 := bstep (se 1 (by rfl) ⟨960629, by rfl⟩ : syracuseStep 1280839 = 1921259) B1921259
theorem B2886911 : Blo 1136633 2886911 := bstep (se 1 (by rfl) ⟨2165183, by rfl⟩ : syracuseStep 2886911 = 4330367) B4330367
theorem B1281487 : Blo 1136633 1281487 := bstep (se 1 (by rfl) ⟨961115, by rfl⟩ : syracuseStep 1281487 = 1922231) B1922231
theorem B2559599 : Blo 1136633 2559599 := bstep (se 1 (by rfl) ⟨1919699, by rfl⟩ : syracuseStep 2559599 = 3839399) B3839399
theorem B1281703 : Blo 1136633 1281703 := bstep (se 1 (by rfl) ⟨961277, by rfl⟩ : syracuseStep 1281703 = 1922555) B1922555
theorem B1281775 : Blo 1136633 1281775 := bstep (se 1 (by rfl) ⟨961331, by rfl⟩ : syracuseStep 1281775 = 1922663) B1922663
theorem B6491927 : Blo 1136633 6491927 := bstep (se 1 (by rfl) ⟨4868945, by rfl⟩ : syracuseStep 6491927 = 9737891) B9737891
theorem B26283959 : Blo 1136633 26283959 := bstep (se 1 (by rfl) ⟨19712969, by rfl⟩ : syracuseStep 26283959 = 39425939) B39425939
theorem B1281991 : Blo 1136633 1281991 := bstep (se 1 (by rfl) ⟨961493, by rfl⟩ : syracuseStep 1281991 = 1922987) B1922987
theorem B1708271 : Blo 1136633 1708271 := bstep (se 1 (by rfl) ⟨1281203, by rfl⟩ : syracuseStep 1708271 = 2562407) B2562407
theorem B2429203 : Blo 1136633 2429203 := bstep (se 1 (by rfl) ⟨1821902, by rfl⟩ : syracuseStep 2429203 = 3643805) B3643805
theorem B2560283 : Blo 1136633 2560283 := bstep (se 1 (by rfl) ⟨1920212, by rfl⟩ : syracuseStep 2560283 = 3840425) B3840425
theorem B1282351 : Blo 1136633 1282351 := bstep (se 1 (by rfl) ⟨961763, by rfl⟩ : syracuseStep 1282351 = 1923527) B1923527
theorem B1708457 : Blo 1136633 1708457 := bstep (se 2 (by rfl) ⟨640671, by rfl⟩ : syracuseStep 1708457 = 1281343) B1281343
theorem B2560427 : Blo 1136633 2560427 := bstep (se 1 (by rfl) ⟨1920320, by rfl⟩ : syracuseStep 2560427 = 3840641) B3840641
theorem B2920967 : Blo 1136633 2920967 := bstep (se 1 (by rfl) ⟨2190725, by rfl⟩ : syracuseStep 2920967 = 4381451) B4381451
theorem B24646193 : Blo 1136633 24646193 := bstep (se 2 (by rfl) ⟨9242322, by rfl⟩ : syracuseStep 24646193 = 18484645) B18484645
theorem B2429723 : Blo 1136633 2429723 := bstep (se 1 (by rfl) ⟨1822292, by rfl⟩ : syracuseStep 2429723 = 3644585) B3644585
theorem B3838751 : Blo 1136633 3838751 := bstep (se 1 (by rfl) ⟨2879063, by rfl⟩ : syracuseStep 3838751 = 5758127) B5758127
theorem B6493067 : Blo 1136633 6493067 := bstep (se 1 (by rfl) ⟨4869800, by rfl⟩ : syracuseStep 6493067 = 9739601) B9739601
theorem B9999389 : Blo 1136633 9999389 := bstep (se 3 (by rfl) ⟨1874885, by rfl⟩ : syracuseStep 9999389 = 3749771) B3749771
theorem B1709159 : Blo 1136633 1709159 := bstep (se 1 (by rfl) ⟨1281869, by rfl⟩ : syracuseStep 1709159 = 2563739) B2563739
theorem B1709183 : Blo 1136633 1709183 := bstep (se 1 (by rfl) ⟨1281887, by rfl⟩ : syracuseStep 1709183 = 2563775) B2563775
theorem B6493567 : Blo 1136633 6493567 := bstep (se 1 (by rfl) ⟨4870175, by rfl⟩ : syracuseStep 6493567 = 9740351) B9740351
theorem B2561759 : Blo 1136633 2561759 := bstep (se 1 (by rfl) ⟨1921319, by rfl⟩ : syracuseStep 2561759 = 3842639) B3842639
theorem B2594663 : Blo 1136633 2594663 := bstep (se 1 (by rfl) ⟨1945997, by rfl⟩ : syracuseStep 2594663 = 3891995) B3891995
theorem B1709993 : Blo 1136633 1709993 := bstep (se 2 (by rfl) ⟨641247, by rfl⟩ : syracuseStep 1709993 = 1282495) B1282495
theorem B27695135 : Blo 1136633 27695135 := bstep (se 1 (by rfl) ⟨20771351, by rfl⟩ : syracuseStep 27695135 = 41542703) B41542703
theorem B2562299 : Blo 1136633 2562299 := bstep (se 1 (by rfl) ⟨1921724, by rfl⟩ : syracuseStep 2562299 = 3843449) B3843449
theorem B1710647 : Blo 1136633 1710647 := bstep (se 1 (by rfl) ⟨1282985, by rfl⟩ : syracuseStep 1710647 = 2565971) B2565971
theorem B5479103 : Blo 1136633 5479103 := bstep (se 1 (by rfl) ⟨4109327, by rfl⟩ : syracuseStep 5479103 = 8218655) B8218655
theorem B2562785 : Blo 1136633 2562785 := bstep (se 2 (by rfl) ⟨961044, by rfl⟩ : syracuseStep 2562785 = 1922089) B1922089
theorem B3841235 : Blo 1136633 3841235 := bstep (se 1 (by rfl) ⟨2880926, by rfl⟩ : syracuseStep 3841235 = 5761853) B5761853
theorem B3841343 : Blo 1136633 3841343 := bstep (se 1 (by rfl) ⟨2881007, by rfl⟩ : syracuseStep 3841343 = 5762015) B5762015
theorem B2563631 : Blo 1136633 2563631 := bstep (se 1 (by rfl) ⟨1922723, by rfl⟩ : syracuseStep 2563631 = 3845447) B3845447
theorem B24616871 : Blo 1136633 24616871 := bstep (se 1 (by rfl) ⟨18462653, by rfl⟩ : syracuseStep 24616871 = 36925307) B36925307
theorem B2598119 : Blo 1136633 2598119 := bstep (se 1 (by rfl) ⟨1948589, by rfl⟩ : syracuseStep 2598119 = 3897179) B3897179
theorem B3843827 : Blo 1136633 3843827 := bstep (se 1 (by rfl) ⟨2882870, by rfl⟩ : syracuseStep 3843827 = 5765741) B5765741
theorem B12298229 : Blo 1136633 12298229 := bstep (se 5 (by rfl) ⟨576479, by rfl⟩ : syracuseStep 12298229 = 1152959) B1152959
theorem B2566331 : Blo 1136633 2566331 := bstep (se 1 (by rfl) ⟨1924748, by rfl⟩ : syracuseStep 2566331 = 3849497) B3849497
theorem B3288127 : Blo 1136633 3288127 := bstep (se 1 (by rfl) ⟨2466095, by rfl⟩ : syracuseStep 3288127 = 4932191) B4932191
theorem B4861291 : Blo 1136633 4861291 := bstep (se 1 (by rfl) ⟨3645968, by rfl⟩ : syracuseStep 4861291 = 7291937) B7291937
theorem B3289351 : Blo 1136633 3289351 := bstep (se 1 (by rfl) ⟨2467013, by rfl⟩ : syracuseStep 3289351 = 4934027) B4934027
theorem B3846635 : Blo 1136633 3846635 := bstep (se 1 (by rfl) ⟨2884976, by rfl⟩ : syracuseStep 3846635 = 5769953) B5769953
theorem B19477421 : Blo 1136633 19477421 := bstep (se 3 (by rfl) ⟨3652016, by rfl⟩ : syracuseStep 19477421 = 7304033) B7304033
theorem B5846543 : Blo 1136633 5846543 := bstep (se 1 (by rfl) ⟨4384907, by rfl⟩ : syracuseStep 5846543 = 8769815) B8769815
theorem B2735083 : Blo 1136633 2735083 := bstep (se 1 (by rfl) ⟨2051312, by rfl⟩ : syracuseStep 2735083 = 4102625) B4102625
theorem B24919073 : Blo 1136633 24919073 := bstep (se 2 (by rfl) ⟨9344652, by rfl⟩ : syracuseStep 24919073 = 18689305) B18689305
theorem B5193715 : Blo 1136633 5193715 := bstep (se 1 (by rfl) ⟨3895286, by rfl⟩ : syracuseStep 5193715 = 7790573) B7790573
theorem B10371665 : Blo 1136633 10371665 := bstep (se 2 (by rfl) ⟨3889374, by rfl⟩ : syracuseStep 10371665 = 7778749) B7778749
theorem B6570875 : Blo 1136633 6570875 := bstep (se 1 (by rfl) ⟨4928156, by rfl⟩ : syracuseStep 6570875 = 9856313) B9856313
theorem B19481795 : Blo 1136633 19481795 := bstep (se 1 (by rfl) ⟨14611346, by rfl⟩ : syracuseStep 19481795 = 29222693) B29222693
theorem B9717083 : Blo 1136633 9717083 := bstep (se 1 (by rfl) ⟨7287812, by rfl⟩ : syracuseStep 9717083 = 14575625) B14575625
theorem B26331241 : Blo 1136633 26331241 := bstep (se 2 (by rfl) ⟨9874215, by rfl⟩ : syracuseStep 26331241 = 19748431) B19748431
theorem B2771083 : Blo 1136633 2771083 := bstep (se 1 (by rfl) ⟨2078312, by rfl⟩ : syracuseStep 2771083 = 4156625) B4156625
theorem B7293577 : Blo 1136633 7293577 := bstep (se 2 (by rfl) ⟨2735091, by rfl⟩ : syracuseStep 7293577 = 5470183) B5470183
theorem B3328765 : Blo 1136633 3328765 := bstep (se 3 (by rfl) ⟨624143, by rfl⟩ : syracuseStep 3328765 = 1248287) B1248287
theorem B1920847 : Blo 1136633 1920847 := bstep (se 1 (by rfl) ⟨1440635, by rfl⟩ : syracuseStep 1920847 = 2881271) B2881271
theorem B5330627 : Blo 1136633 5330627 := bstep (se 1 (by rfl) ⟨3997970, by rfl⟩ : syracuseStep 5330627 = 7995941) B7995941
theorem B4609889 : Blo 1136633 4609889 := bstep (se 2 (by rfl) ⟨1728708, by rfl⟩ : syracuseStep 4609889 = 3457417) B3457417
theorem B1136703 : Blo 1136633 1136703 := bstep (se 1 (by rfl) ⟨852527, by rfl⟩ : syracuseStep 1136703 = 1705055) B1705055
theorem B1136743 : Blo 1136633 1136743 := bstep (se 1 (by rfl) ⟨852557, by rfl⟩ : syracuseStep 1136743 = 1705115) B1705115
theorem B4610407 : Blo 1136633 4610407 := bstep (se 1 (by rfl) ⟨3457805, by rfl⟩ : syracuseStep 4610407 = 6915611) B6915611
theorem B16407319 : Blo 1136633 16407319 := bstep (se 1 (by rfl) ⟨12305489, by rfl⟩ : syracuseStep 16407319 = 24610979) B24610979
theorem B1137535 : Blo 1136633 1137535 := bstep (se 1 (by rfl) ⟨853151, by rfl⟩ : syracuseStep 1137535 = 1706303) B1706303
theorem B1924283 : Blo 1136633 1924283 := bstep (se 1 (by rfl) ⟨1443212, by rfl⟩ : syracuseStep 1924283 = 2886425) B2886425
theorem B21880115 : Blo 1136633 21880115 := bstep (se 1 (by rfl) ⟨16410086, by rfl⟩ : syracuseStep 21880115 = 32820173) B32820173
theorem B1137983 : Blo 1136633 1137983 := bstep (se 1 (by rfl) ⟨853487, by rfl⟩ : syracuseStep 1137983 = 1706975) B1706975
theorem B1826111 : Blo 1136633 1826111 := bstep (se 1 (by rfl) ⟨1369583, by rfl⟩ : syracuseStep 1826111 = 2739167) B2739167
theorem B4316591 : Blo 1136633 4316591 := bstep (se 1 (by rfl) ⟨3237443, by rfl⟩ : syracuseStep 4316591 = 6474887) B6474887
theorem B19455551 : Blo 1136633 19455551 := bstep (se 1 (by rfl) ⟨14591663, by rfl⟩ : syracuseStep 19455551 = 29183327) B29183327
theorem B1139047 : Blo 1136633 1139047 := bstep (se 1 (by rfl) ⟨854285, by rfl⟩ : syracuseStep 1139047 = 1708571) B1708571
theorem B4317563 : Blo 1136633 4317563 := bstep (se 1 (by rfl) ⟨3238172, by rfl⟩ : syracuseStep 4317563 = 6476345) B6476345
theorem B1139167 : Blo 1136633 1139167 := bstep (se 1 (by rfl) ⟨854375, by rfl⟩ : syracuseStep 1139167 = 1708751) B1708751
theorem B1139519 : Blo 1136633 1139519 := bstep (se 1 (by rfl) ⟨854639, by rfl⟩ : syracuseStep 1139519 = 1709279) B1709279
theorem B1139679 : Blo 1136633 1139679 := bstep (se 1 (by rfl) ⟨854759, by rfl⟩ : syracuseStep 1139679 = 1709519) B1709519
theorem B1139839 : Blo 1136633 1139839 := bstep (se 1 (by rfl) ⟨854879, by rfl⟩ : syracuseStep 1139839 = 1709759) B1709759
theorem B1140095 : Blo 1136633 1140095 := bstep (se 1 (by rfl) ⟨855071, by rfl⟩ : syracuseStep 1140095 = 1710143) B1710143
theorem B1140207 : Blo 1136633 1140207 := bstep (se 1 (by rfl) ⟨855155, by rfl⟩ : syracuseStep 1140207 = 1710311) B1710311
theorem B1140327 : Blo 1136633 1140327 := bstep (se 1 (by rfl) ⟨855245, by rfl⟩ : syracuseStep 1140327 = 1710491) B1710491
theorem B29157083 : Blo 1136633 29157083 := bstep (se 1 (by rfl) ⟨21867812, by rfl⟩ : syracuseStep 29157083 = 43735625) B43735625
theorem B27682681 : Blo 1136633 27682681 := bstep (se 2 (by rfl) ⟨10381005, by rfl⟩ : syracuseStep 27682681 = 20762011) B20762011
theorem B1140607 : Blo 1136633 1140607 := bstep (se 1 (by rfl) ⟨855455, by rfl⟩ : syracuseStep 1140607 = 1710911) B1710911
theorem B18442151 : Blo 1136633 18442151 := bstep (se 1 (by rfl) ⟨13831613, by rfl⟩ : syracuseStep 18442151 = 27663227) B27663227
theorem B4614203 : Blo 1136633 4614203 := bstep (se 1 (by rfl) ⟨3460652, by rfl⟩ : syracuseStep 4614203 = 6921305) B6921305
theorem B3238879 : Blo 1136633 3238879 := bstep (se 1 (by rfl) ⟨2429159, by rfl⟩ : syracuseStep 3238879 = 4858319) B4858319
theorem B21851207 : Blo 1136633 21851207 := bstep (se 1 (by rfl) ⟨16388405, by rfl⟩ : syracuseStep 21851207 = 32776811) B32776811
theorem B2878699 : Blo 1136633 2878699 := bstep (se 1 (by rfl) ⟨2159024, by rfl⟩ : syracuseStep 2878699 = 4318049) B4318049
theorem B2878811 : Blo 1136633 2878811 := bstep (se 1 (by rfl) ⟨2159108, by rfl⟩ : syracuseStep 2878811 = 4318217) B4318217
theorem B2878841 : Blo 1136633 2878841 := bstep (se 2 (by rfl) ⟨1079565, by rfl⟩ : syracuseStep 2878841 = 2159131) B2159131
theorem B5762987 : Blo 1136633 5762987 := bstep (se 1 (by rfl) ⟨4322240, by rfl⟩ : syracuseStep 5762987 = 8644481) B8644481
theorem B23654591 : Blo 1136633 23654591 := bstep (se 1 (by rfl) ⟨17740943, by rfl⟩ : syracuseStep 23654591 = 35481887) B35481887
theorem B4321633 : Blo 1136633 4321633 := bstep (se 2 (by rfl) ⟨1620612, by rfl⟩ : syracuseStep 4321633 = 3241225) B3241225
theorem B19722599 : Blo 1136633 19722599 := bstep (se 1 (by rfl) ⟨14791949, by rfl⟩ : syracuseStep 19722599 = 29583899) B29583899
theorem B41480693 : Blo 1136633 41480693 := bstep (se 5 (by rfl) ⟨1944407, by rfl⟩ : syracuseStep 41480693 = 3888815) B3888815
theorem B2880137 : Blo 1136633 2880137 := bstep (se 2 (by rfl) ⟨1080051, by rfl⟩ : syracuseStep 2880137 = 2160103) B2160103
theorem B1438975 : Blo 1136633 1438975 := bstep (se 1 (by rfl) ⟨1079231, by rfl⟩ : syracuseStep 1438975 = 2158463) B2158463
theorem B33748379 : Blo 1136633 33748379 := bstep (se 1 (by rfl) ⟨25311284, by rfl⟩ : syracuseStep 33748379 = 50622569) B50622569
theorem B4322879 : Blo 1136633 4322879 := bstep (se 1 (by rfl) ⟨3242159, by rfl⟩ : syracuseStep 4322879 = 6484319) B6484319
theorem B4617919 : Blo 1136633 4617919 := bstep (se 1 (by rfl) ⟨3463439, by rfl⟩ : syracuseStep 4617919 = 6926879) B6926879
theorem B307492595 : Blo 1136633 307492595 := bstep (se 1 (by rfl) ⟨230619446, by rfl⟩ : syracuseStep 307492595 = 461238893) B461238893
theorem B4323091 : Blo 1136633 4323091 := bstep (se 1 (by rfl) ⟨3242318, by rfl⟩ : syracuseStep 4323091 = 6484637) B6484637
theorem B14612987 : Blo 1136633 14612987 := bstep (se 1 (by rfl) ⟨10959740, by rfl⟩ : syracuseStep 14612987 = 21919481) B21919481
theorem B3242683 : Blo 1136633 3242683 := bstep (se 1 (by rfl) ⟨2432012, by rfl⟩ : syracuseStep 3242683 = 4864025) B4864025
theorem B2882375 : Blo 1136633 2882375 := bstep (se 1 (by rfl) ⟨2161781, by rfl⟩ : syracuseStep 2882375 = 4323563) B4323563
theorem B2882425 : Blo 1136633 2882425 := bstep (se 2 (by rfl) ⟨1080909, by rfl⟩ : syracuseStep 2882425 = 2161819) B2161819
theorem B3243071 : Blo 1136633 3243071 := bstep (se 1 (by rfl) ⟨2432303, by rfl⟩ : syracuseStep 3243071 = 4864607) B4864607
theorem B5766227 : Blo 1136633 5766227 := bstep (se 1 (by rfl) ⟨4324670, by rfl⟩ : syracuseStep 5766227 = 8649341) B8649341
theorem B6487553 : Blo 1136633 6487553 := bstep (se 2 (by rfl) ⟨2432832, by rfl⟩ : syracuseStep 6487553 = 4865665) B4865665
theorem B1442119 : Blo 1136633 1442119 := bstep (se 1 (by rfl) ⟨1081589, by rfl⟩ : syracuseStep 1442119 = 2163179) B2163179
theorem B1704953 : Blo 1136633 1704953 := bstep (se 2 (by rfl) ⟨639357, by rfl⟩ : syracuseStep 1704953 = 1278715) B1278715
theorem B1705007 : Blo 1136633 1705007 := bstep (se 1 (by rfl) ⟨1278755, by rfl⟩ : syracuseStep 1705007 = 2557511) B2557511
theorem B14615963 : Blo 1136633 14615963 := bstep (se 1 (by rfl) ⟨10961972, by rfl⟩ : syracuseStep 14615963 = 21923945) B21923945
theorem B27657773 : Blo 1136633 27657773 := bstep (se 3 (by rfl) ⟨5185832, by rfl⟩ : syracuseStep 27657773 = 10371665) B10371665
theorem B14812793 : Blo 1136633 14812793 := bstep (se 2 (by rfl) ⟨5554797, by rfl⟩ : syracuseStep 14812793 = 11109595) B11109595
theorem B1705727 : Blo 1136633 1705727 := bstep (se 1 (by rfl) ⟨1279295, by rfl⟩ : syracuseStep 1705727 = 2558591) B2558591
theorem B2885503 : Blo 1136633 2885503 := bstep (se 1 (by rfl) ⟨2164127, by rfl⟩ : syracuseStep 2885503 = 4328255) B4328255
theorem B1706399 : Blo 1136633 1706399 := bstep (se 1 (by rfl) ⟨1279799, by rfl⟩ : syracuseStep 1706399 = 2559599) B2559599
theorem B4327951 : Blo 1136633 4327951 := bstep (se 1 (by rfl) ⟨3245963, by rfl⟩ : syracuseStep 4327951 = 6491927) B6491927
theorem B1706855 : Blo 1136633 1706855 := bstep (se 1 (by rfl) ⟨1280141, by rfl⟩ : syracuseStep 1706855 = 2560283) B2560283
theorem B1706951 : Blo 1136633 1706951 := bstep (se 1 (by rfl) ⟨1280213, by rfl⟩ : syracuseStep 1706951 = 2560427) B2560427
theorem B2559167 : Blo 1136633 2559167 := bstep (se 1 (by rfl) ⟨1919375, by rfl⟩ : syracuseStep 2559167 = 3838751) B3838751
theorem B4328711 : Blo 1136633 4328711 := bstep (se 1 (by rfl) ⟨3246533, by rfl⟩ : syracuseStep 4328711 = 6493067) B6493067
theorem B8654201 : Blo 1136633 8654201 := bstep (se 2 (by rfl) ⟨3245325, by rfl⟩ : syracuseStep 8654201 = 6490651) B6490651
theorem B1707689 : Blo 1136633 1707689 := bstep (se 2 (by rfl) ⟨640383, by rfl⟩ : syracuseStep 1707689 = 1280767) B1280767
theorem B1707785 : Blo 1136633 1707785 := bstep (se 2 (by rfl) ⟨640419, by rfl⟩ : syracuseStep 1707785 = 1280839) B1280839
theorem B1707839 : Blo 1136633 1707839 := bstep (se 1 (by rfl) ⟨1280879, by rfl⟩ : syracuseStep 1707839 = 2561759) B2561759
theorem B1708199 : Blo 1136633 1708199 := bstep (se 1 (by rfl) ⟨1281149, by rfl⟩ : syracuseStep 1708199 = 2562299) B2562299
theorem B3838265 : Blo 1136633 3838265 := bstep (se 2 (by rfl) ⟨1439349, by rfl⟩ : syracuseStep 3838265 = 2878699) B2878699
theorem B1708523 : Blo 1136633 1708523 := bstep (se 1 (by rfl) ⟨1281392, by rfl⟩ : syracuseStep 1708523 = 2562785) B2562785
theorem B1708649 : Blo 1136633 1708649 := bstep (se 2 (by rfl) ⟨640743, by rfl⟩ : syracuseStep 1708649 = 1281487) B1281487
theorem B1282855 : Blo 1136633 1282855 := bstep (se 1 (by rfl) ⟨962141, by rfl⟩ : syracuseStep 1282855 = 1924283) B1924283
theorem B2560823 : Blo 1136633 2560823 := bstep (se 1 (by rfl) ⟨1920617, by rfl⟩ : syracuseStep 2560823 = 3841235) B3841235
theorem B14586743 : Blo 1136633 14586743 := bstep (se 1 (by rfl) ⟨10940057, by rfl⟩ : syracuseStep 14586743 = 21880115) B21880115
theorem B2560895 : Blo 1136633 2560895 := bstep (se 1 (by rfl) ⟨1920671, by rfl⟩ : syracuseStep 2560895 = 3841343) B3841343
theorem B1708937 : Blo 1136633 1708937 := bstep (se 2 (by rfl) ⟨640851, by rfl⟩ : syracuseStep 1708937 = 1281703) B1281703
theorem B1709033 : Blo 1136633 1709033 := bstep (se 2 (by rfl) ⟨640887, by rfl⟩ : syracuseStep 1709033 = 1281775) B1281775
theorem B1709087 : Blo 1136633 1709087 := bstep (se 1 (by rfl) ⟨1281815, by rfl⟩ : syracuseStep 1709087 = 2563631) B2563631
theorem B2561129 : Blo 1136633 2561129 := bstep (se 2 (by rfl) ⟨960423, by rfl⟩ : syracuseStep 2561129 = 1920847) B1920847
theorem B1709321 : Blo 1136633 1709321 := bstep (se 2 (by rfl) ⟨640995, by rfl⟩ : syracuseStep 1709321 = 1281991) B1281991
theorem B1709801 : Blo 1136633 1709801 := bstep (se 2 (by rfl) ⟨641175, by rfl⟩ : syracuseStep 1709801 = 1282351) B1282351
theorem B19438055 : Blo 1136633 19438055 := bstep (se 1 (by rfl) ⟨14578541, by rfl⟩ : syracuseStep 19438055 = 29157083) B29157083
theorem B2562551 : Blo 1136633 2562551 := bstep (se 1 (by rfl) ⟨1921913, by rfl⟩ : syracuseStep 2562551 = 3843827) B3843827
theorem B12294767 : Blo 1136633 12294767 := bstep (se 1 (by rfl) ⟨9221075, by rfl⟩ : syracuseStep 12294767 = 18442151) B18442151
theorem B8198819 : Blo 1136633 8198819 := bstep (se 1 (by rfl) ⟨6149114, by rfl⟩ : syracuseStep 8198819 = 12298229) B12298229
theorem B1710887 : Blo 1136633 1710887 := bstep (se 1 (by rfl) ⟨1283165, by rfl⟩ : syracuseStep 1710887 = 2566331) B2566331
theorem B8658089 : Blo 1136633 8658089 := bstep (se 2 (by rfl) ⟨3246783, by rfl⟩ : syracuseStep 8658089 = 6493567) B6493567
theorem B56860021 : Blo 1136633 56860021 := bstep (se 5 (by rfl) ⟨2665313, by rfl⟩ : syracuseStep 56860021 = 5330627) B5330627
theorem B3841991 : Blo 1136633 3841991 := bstep (se 1 (by rfl) ⟨2881493, by rfl⟩ : syracuseStep 3841991 = 5762987) B5762987
theorem B15769727 : Blo 1136633 15769727 := bstep (se 1 (by rfl) ⟨11827295, by rfl⟩ : syracuseStep 15769727 = 23654591) B23654591
theorem B13148399 : Blo 1136633 13148399 := bstep (se 1 (by rfl) ⟨9861299, by rfl⟩ : syracuseStep 13148399 = 19722599) B19722599
theorem B2564423 : Blo 1136633 2564423 := bstep (se 1 (by rfl) ⟨1923317, by rfl⟩ : syracuseStep 2564423 = 3846635) B3846635
theorem B12984947 : Blo 1136633 12984947 := bstep (se 1 (by rfl) ⟨9738710, by rfl⟩ : syracuseStep 12984947 = 19477421) B19477421
theorem B3843233 : Blo 1136633 3843233 := bstep (se 2 (by rfl) ⟨1441212, by rfl⟩ : syracuseStep 3843233 = 2882425) B2882425
theorem B3646777 : Blo 1136633 3646777 := bstep (se 2 (by rfl) ⟨1367541, by rfl⟩ : syracuseStep 3646777 = 2735083) B2735083
theorem B9741991 : Blo 1136633 9741991 := bstep (se 1 (by rfl) ⟨7306493, by rfl⟩ : syracuseStep 9741991 = 14612987) B14612987
theorem B3844151 : Blo 1136633 3844151 := bstep (se 1 (by rfl) ⟨2883113, by rfl⟩ : syracuseStep 3844151 = 5766227) B5766227
theorem B6924953 : Blo 1136633 6924953 := bstep (se 2 (by rfl) ⟨2596857, by rfl⟩ : syracuseStep 6924953 = 5193715) B5193715
theorem B12987863 : Blo 1136633 12987863 := bstep (se 1 (by rfl) ⟨9740897, by rfl⟩ : syracuseStep 12987863 = 19481795) B19481795
theorem B3649711 : Blo 1136633 3649711 := bstep (se 1 (by rfl) ⟨2737283, by rfl⟩ : syracuseStep 3649711 = 5474567) B5474567
theorem B36910241 : Blo 1136633 36910241 := bstep (se 2 (by rfl) ⟨13841340, by rfl⟩ : syracuseStep 36910241 = 27682681) B27682681
theorem B35108321 : Blo 1136633 35108321 := bstep (se 2 (by rfl) ⟨13165620, by rfl⟩ : syracuseStep 35108321 = 26331241) B26331241
theorem B1947311 : Blo 1136633 1947311 := bstep (se 1 (by rfl) ⟨1460483, by rfl⟩ : syracuseStep 1947311 = 2920967) B2920967
theorem B16430795 : Blo 1136633 16430795 := bstep (se 1 (by rfl) ⟨12323096, by rfl⟩ : syracuseStep 16430795 = 24646193) B24646193
theorem B6666259 : Blo 1136633 6666259 := bstep (se 1 (by rfl) ⟨4999694, by rfl⟩ : syracuseStep 6666259 = 9999389) B9999389
theorem B3652735 : Blo 1136633 3652735 := bstep (se 1 (by rfl) ⟨2739551, by rfl⟩ : syracuseStep 3652735 = 5479103) B5479103
theorem B12304541 : Blo 1136633 12304541 := bstep (se 3 (by rfl) ⟨2307101, by rfl⟩ : syracuseStep 12304541 = 4614203) B4614203
theorem B1918633 : Blo 1136633 1918633 := bstep (se 2 (by rfl) ⟨719487, by rfl⟩ : syracuseStep 1918633 = 1438975) B1438975
theorem B14567471 : Blo 1136633 14567471 := bstep (se 1 (by rfl) ⟨10925603, by rfl⟩ : syracuseStep 14567471 = 21851207) B21851207
theorem B1919207 : Blo 1136633 1919207 := bstep (se 1 (by rfl) ⟨1439405, by rfl⟩ : syracuseStep 1919207 = 2878811) B2878811
theorem B1919227 : Blo 1136633 1919227 := bstep (se 1 (by rfl) ⟨1439420, by rfl⟩ : syracuseStep 1919227 = 2878841) B2878841
theorem B1920091 : Blo 1136633 1920091 := bstep (se 1 (by rfl) ⟨1440068, by rfl⟩ : syracuseStep 1920091 = 2880137) B2880137
theorem B6147209 : Blo 1136633 6147209 := bstep (se 2 (by rfl) ⟨2305203, by rfl⟩ : syracuseStep 6147209 = 4610407) B4610407
theorem B4869629 : Blo 1136633 4869629 := bstep (se 3 (by rfl) ⟨913055, by rfl⟩ : syracuseStep 4869629 = 1826111) B1826111
theorem B22498919 : Blo 1136633 22498919 := bstep (se 1 (by rfl) ⟨16874189, by rfl⟩ : syracuseStep 22498919 = 33748379) B33748379
theorem B21876425 : Blo 1136633 21876425 := bstep (se 2 (by rfl) ⟨8203659, by rfl⟩ : syracuseStep 21876425 = 16407319) B16407319
theorem B1921583 : Blo 1136633 1921583 := bstep (se 1 (by rfl) ⟨1441187, by rfl⟩ : syracuseStep 1921583 = 2882375) B2882375
theorem B19420559 : Blo 1136633 19420559 := bstep (se 1 (by rfl) ⟨14565419, by rfl⟩ : syracuseStep 19420559 = 29130839) B29130839
theorem B1922791 : Blo 1136633 1922791 := bstep (se 1 (by rfl) ⟨1442093, by rfl⟩ : syracuseStep 1922791 = 2884187) B2884187
theorem B4380583 : Blo 1136633 4380583 := bstep (se 1 (by rfl) ⟨3285437, by rfl⟩ : syracuseStep 4380583 = 6570875) B6570875
theorem B1136751 : Blo 1136633 1136751 := bstep (se 1 (by rfl) ⟨852563, by rfl⟩ : syracuseStep 1136751 = 1705127) B1705127
theorem B6478055 : Blo 1136633 6478055 := bstep (se 1 (by rfl) ⟨4858541, by rfl⟩ : syracuseStep 6478055 = 9717083) B9717083
theorem B1137199 : Blo 1136633 1137199 := bstep (se 1 (by rfl) ⟨852899, by rfl⟩ : syracuseStep 1137199 = 1705799) B1705799
theorem B1137359 : Blo 1136633 1137359 := bstep (se 1 (by rfl) ⟨853019, by rfl⟩ : syracuseStep 1137359 = 1706039) B1706039
theorem B1923817 : Blo 1136633 1923817 := bstep (se 2 (by rfl) ⟨721431, by rfl⟩ : syracuseStep 1923817 = 1442863) B1442863
theorem B1137631 : Blo 1136633 1137631 := bstep (se 1 (by rfl) ⟨853223, by rfl⟩ : syracuseStep 1137631 = 1706447) B1706447
theorem B6479261 : Blo 1136633 6479261 := bstep (se 3 (by rfl) ⟨1214861, by rfl⟩ : syracuseStep 6479261 = 2429723) B2429723
theorem B1924607 : Blo 1136633 1924607 := bstep (se 1 (by rfl) ⟨1443455, by rfl⟩ : syracuseStep 1924607 = 2886911) B2886911
theorem B17522639 : Blo 1136633 17522639 := bstep (se 1 (by rfl) ⟨13141979, by rfl⟩ : syracuseStep 17522639 = 26283959) B26283959
theorem B1138847 : Blo 1136633 1138847 := bstep (se 1 (by rfl) ⟨854135, by rfl⟩ : syracuseStep 1138847 = 1708271) B1708271
theorem B3694777 : Blo 1136633 3694777 := bstep (se 2 (by rfl) ⟨1385541, by rfl⟩ : syracuseStep 3694777 = 2771083) B2771083
theorem B1138971 : Blo 1136633 1138971 := bstep (se 1 (by rfl) ⟨854228, by rfl⟩ : syracuseStep 1138971 = 1708457) B1708457
theorem B1139439 : Blo 1136633 1139439 := bstep (se 1 (by rfl) ⟨854579, by rfl⟩ : syracuseStep 1139439 = 1709159) B1709159
theorem B1139455 : Blo 1136633 1139455 := bstep (se 1 (by rfl) ⟨854591, by rfl⟩ : syracuseStep 1139455 = 1709183) B1709183
theorem B9724769 : Blo 1136633 9724769 := bstep (se 2 (by rfl) ⟨3646788, by rfl⟩ : syracuseStep 9724769 = 7293577) B7293577
theorem B3073259 : Blo 1136633 3073259 := bstep (se 1 (by rfl) ⟨2304944, by rfl⟩ : syracuseStep 3073259 = 4609889) B4609889
theorem B1729775 : Blo 1136633 1729775 := bstep (se 1 (by rfl) ⟨1297331, by rfl⟩ : syracuseStep 1729775 = 2594663) B2594663
theorem B1139995 : Blo 1136633 1139995 := bstep (se 1 (by rfl) ⟨854996, by rfl⟩ : syracuseStep 1139995 = 1709993) B1709993
theorem B4318505 : Blo 1136633 4318505 := bstep (se 2 (by rfl) ⟨1619439, by rfl⟩ : syracuseStep 4318505 = 3238879) B3238879
theorem B17753413 : Blo 1136633 17753413 := bstep (se 4 (by rfl) ⟨1664382, by rfl⟩ : syracuseStep 17753413 = 3328765) B3328765
theorem B4384169 : Blo 1136633 4384169 := bstep (se 2 (by rfl) ⟨1644063, by rfl⟩ : syracuseStep 4384169 = 3288127) B3288127
theorem B1140431 : Blo 1136633 1140431 := bstep (se 1 (by rfl) ⟨855323, by rfl⟩ : syracuseStep 1140431 = 1710647) B1710647
theorem B6481721 : Blo 1136633 6481721 := bstep (se 2 (by rfl) ⟨2430645, by rfl⟩ : syracuseStep 6481721 = 4861291) B4861291
theorem B2877727 : Blo 1136633 2877727 := bstep (se 1 (by rfl) ⟨2158295, by rfl⟩ : syracuseStep 2877727 = 4316591) B4316591
theorem B12970367 : Blo 1136633 12970367 := bstep (se 1 (by rfl) ⟨9727775, by rfl⟩ : syracuseStep 12970367 = 19455551) B19455551
theorem B16411247 : Blo 1136633 16411247 := bstep (se 1 (by rfl) ⟨12308435, by rfl⟩ : syracuseStep 16411247 = 24616871) B24616871
theorem B73853693 : Blo 1136633 73853693 := bstep (se 3 (by rfl) ⟨13847567, by rfl⟩ : syracuseStep 73853693 = 27695135) B27695135
theorem B2878375 : Blo 1136633 2878375 := bstep (se 1 (by rfl) ⟨2158781, by rfl⟩ : syracuseStep 2878375 = 4317563) B4317563
theorem B4385801 : Blo 1136633 4385801 := bstep (se 2 (by rfl) ⟨1644675, by rfl⟩ : syracuseStep 4385801 = 3289351) B3289351
theorem B3238937 : Blo 1136633 3238937 := bstep (se 2 (by rfl) ⟨1214601, by rfl⟩ : syracuseStep 3238937 = 2429203) B2429203
theorem B5762177 : Blo 1136633 5762177 := bstep (se 2 (by rfl) ⟨2160816, by rfl⟩ : syracuseStep 5762177 = 4321633) B4321633
theorem B1732079 : Blo 1136633 1732079 := bstep (se 1 (by rfl) ⟨1299059, by rfl⟩ : syracuseStep 1732079 = 2598119) B2598119
theorem B6157225 : Blo 1136633 6157225 := bstep (se 2 (by rfl) ⟨2308959, by rfl⟩ : syracuseStep 6157225 = 4617919) B4617919
theorem B5764121 : Blo 1136633 5764121 := bstep (se 2 (by rfl) ⟨2161545, by rfl⟩ : syracuseStep 5764121 = 4323091) B4323091
theorem B27653795 : Blo 1136633 27653795 := bstep (se 1 (by rfl) ⟨20740346, by rfl⟩ : syracuseStep 27653795 = 41480693) B41480693
theorem B4323577 : Blo 1136633 4323577 := bstep (se 2 (by rfl) ⟨1621341, by rfl⟩ : syracuseStep 4323577 = 3242683) B3242683
theorem B3897695 : Blo 1136633 3897695 := bstep (se 1 (by rfl) ⟨2923271, by rfl⟩ : syracuseStep 3897695 = 5846543) B5846543
theorem B2881919 : Blo 1136633 2881919 := bstep (se 1 (by rfl) ⟨2161439, by rfl⟩ : syracuseStep 2881919 = 4322879) B4322879
theorem B204995063 : Blo 1136633 204995063 := bstep (se 1 (by rfl) ⟨153746297, by rfl⟩ : syracuseStep 204995063 = 307492595) B307492595
theorem B16612715 : Blo 1136633 16612715 := bstep (se 1 (by rfl) ⟨12459536, by rfl⟩ : syracuseStep 16612715 = 24919073) B24919073
theorem B2162047 : Blo 1136633 2162047 := bstep (se 1 (by rfl) ⟨1621535, by rfl⟩ : syracuseStep 2162047 = 3243071) B3243071
theorem B4325035 : Blo 1136633 4325035 := bstep (se 1 (by rfl) ⟨3243776, by rfl⟩ : syracuseStep 4325035 = 6487553) B6487553
theorem B1279471 : Blo 1136633 1279471 := bstep (se 1 (by rfl) ⟨959603, by rfl⟩ : syracuseStep 1279471 = 1919207) B1919207
theorem B1706111 : Blo 1136633 1706111 := bstep (se 1 (by rfl) ⟨1279583, by rfl⟩ : syracuseStep 1706111 = 2559167) B2559167
theorem B2885807 : Blo 1136633 2885807 := bstep (se 1 (by rfl) ⟨2164355, by rfl⟩ : syracuseStep 2885807 = 4328711) B4328711
theorem B2558177 : Blo 1136633 2558177 := bstep (se 2 (by rfl) ⟨959316, by rfl⟩ : syracuseStep 2558177 = 1918633) B1918633
theorem B5769467 : Blo 1136633 5769467 := bstep (se 1 (by rfl) ⟨4327100, by rfl⟩ : syracuseStep 5769467 = 8654201) B8654201
theorem B3246419 : Blo 1136633 3246419 := bstep (se 1 (by rfl) ⟨2434814, by rfl⟩ : syracuseStep 3246419 = 4869629) B4869629
theorem B14584283 : Blo 1136633 14584283 := bstep (se 1 (by rfl) ⟨10938212, by rfl⟩ : syracuseStep 14584283 = 21876425) B21876425
theorem B2558843 : Blo 1136633 2558843 := bstep (se 1 (by rfl) ⟨1919132, by rfl⟩ : syracuseStep 2558843 = 3838265) B3838265
theorem B2558969 : Blo 1136633 2558969 := bstep (se 2 (by rfl) ⟨959613, by rfl⟩ : syracuseStep 2558969 = 1919227) B1919227
theorem B1281055 : Blo 1136633 1281055 := bstep (se 1 (by rfl) ⟨960791, by rfl⟩ : syracuseStep 1281055 = 1921583) B1921583
theorem B3836969 : Blo 1136633 3836969 := bstep (se 2 (by rfl) ⟨1438863, by rfl⟩ : syracuseStep 3836969 = 2877727) B2877727
theorem B1707215 : Blo 1136633 1707215 := bstep (se 1 (by rfl) ⟨1280411, by rfl⟩ : syracuseStep 1707215 = 2560823) B2560823
theorem B1707263 : Blo 1136633 1707263 := bstep (se 1 (by rfl) ⟨1280447, by rfl⟩ : syracuseStep 1707263 = 2560895) B2560895
theorem B8195357 : Blo 1136633 8195357 := bstep (se 3 (by rfl) ⟨1536629, by rfl⟩ : syracuseStep 8195357 = 3073259) B3073259
theorem B5770601 : Blo 1136633 5770601 := bstep (se 2 (by rfl) ⟨2163975, by rfl⟩ : syracuseStep 5770601 = 4327951) B4327951
theorem B1707419 : Blo 1136633 1707419 := bstep (se 1 (by rfl) ⟨1280564, by rfl⟩ : syracuseStep 1707419 = 2561129) B2561129
theorem B12947039 : Blo 1136633 12947039 := bstep (se 1 (by rfl) ⟨9710279, by rfl⟩ : syracuseStep 12947039 = 19420559) B19420559
theorem B3837833 : Blo 1136633 3837833 := bstep (se 2 (by rfl) ⟨1439187, by rfl⟩ : syracuseStep 3837833 = 2878375) B2878375
theorem B93622189 : Blo 1136633 93622189 := bstep (se 3 (by rfl) ⟨17554160, by rfl⟩ : syracuseStep 93622189 = 35108321) B35108321
theorem B2560121 : Blo 1136633 2560121 := bstep (se 2 (by rfl) ⟨960045, by rfl⟩ : syracuseStep 2560121 = 1920091) B1920091
theorem B1708367 : Blo 1136633 1708367 := bstep (se 1 (by rfl) ⟨1281275, by rfl⟩ : syracuseStep 1708367 = 2562551) B2562551
theorem B8196511 : Blo 1136633 8196511 := bstep (se 1 (by rfl) ⟨6147383, by rfl⟩ : syracuseStep 8196511 = 12294767) B12294767
theorem B5772059 : Blo 1136633 5772059 := bstep (se 1 (by rfl) ⟨4329044, by rfl⟩ : syracuseStep 5772059 = 8658089) B8658089
theorem B1283071 : Blo 1136633 1283071 := bstep (se 1 (by rfl) ⟨962303, by rfl⟩ : syracuseStep 1283071 = 1924607) B1924607
theorem B2561327 : Blo 1136633 2561327 := bstep (se 1 (by rfl) ⟨1920995, by rfl⟩ : syracuseStep 2561327 = 3841991) B3841991
theorem B1709615 : Blo 1136633 1709615 := bstep (se 1 (by rfl) ⟨1282211, by rfl⟩ : syracuseStep 1709615 = 2564423) B2564423
theorem B8656631 : Blo 1136633 8656631 := bstep (se 1 (by rfl) ⟨6492473, by rfl⟩ : syracuseStep 8656631 = 12984947) B12984947
theorem B2562155 : Blo 1136633 2562155 := bstep (se 1 (by rfl) ⟨1921616, by rfl⟩ : syracuseStep 2562155 = 3843233) B3843233
theorem B2922779 : Blo 1136633 2922779 := bstep (se 1 (by rfl) ⟨2192084, by rfl⟩ : syracuseStep 2922779 = 4384169) B4384169
theorem B1710473 : Blo 1136633 1710473 := bstep (se 2 (by rfl) ⟨641427, by rfl⟩ : syracuseStep 1710473 = 1282855) B1282855
theorem B2562767 : Blo 1136633 2562767 := bstep (se 1 (by rfl) ⟨1922075, by rfl⟩ : syracuseStep 2562767 = 3844151) B3844151
theorem B2923867 : Blo 1136633 2923867 := bstep (se 1 (by rfl) ⟨2192900, by rfl⟩ : syracuseStep 2923867 = 4385801) B4385801
theorem B3841451 : Blo 1136633 3841451 := bstep (se 1 (by rfl) ⟨2881088, by rfl⟩ : syracuseStep 3841451 = 5762177) B5762177
theorem B2563721 : Blo 1136633 2563721 := bstep (se 2 (by rfl) ⟨961395, by rfl⟩ : syracuseStep 2563721 = 1922791) B1922791
theorem B8658575 : Blo 1136633 8658575 := bstep (se 1 (by rfl) ⟨6493931, by rfl⟩ : syracuseStep 8658575 = 12987863) B12987863
theorem B1154719 : Blo 1136633 1154719 := bstep (se 1 (by rfl) ⟨866039, by rfl⟩ : syracuseStep 1154719 = 1732079) B1732079
theorem B5840777 : Blo 1136633 5840777 := bstep (se 2 (by rfl) ⟨2190291, by rfl⟩ : syracuseStep 5840777 = 4380583) B4380583
theorem B8888345 : Blo 1136633 8888345 := bstep (se 2 (by rfl) ⟨3333129, by rfl⟩ : syracuseStep 8888345 = 6666259) B6666259
theorem B16392557 : Blo 1136633 16392557 := bstep (se 3 (by rfl) ⟨3073604, by rfl⟩ : syracuseStep 16392557 = 6147209) B6147209
theorem B3842747 : Blo 1136633 3842747 := bstep (se 1 (by rfl) ⟨2882060, by rfl⟩ : syracuseStep 3842747 = 5764121) B5764121
theorem B2565089 : Blo 1136633 2565089 := bstep (se 2 (by rfl) ⟨961908, by rfl⟩ : syracuseStep 2565089 = 1923817) B1923817
theorem B10953863 : Blo 1136633 10953863 := bstep (se 1 (by rfl) ⟨8215397, by rfl⟩ : syracuseStep 10953863 = 16430795) B16430795
theorem B2598463 : Blo 1136633 2598463 := bstep (se 1 (by rfl) ⟨1948847, by rfl⟩ : syracuseStep 2598463 = 3897695) B3897695
theorem B8203027 : Blo 1136633 8203027 := bstep (se 1 (by rfl) ⟨6152270, by rfl⟩ : syracuseStep 8203027 = 12304541) B12304541
theorem B9743975 : Blo 1136633 9743975 := bstep (se 1 (by rfl) ⟨7307981, by rfl⟩ : syracuseStep 9743975 = 14615963) B14615963
theorem B9875195 : Blo 1136633 9875195 := bstep (se 1 (by rfl) ⟨7406396, by rfl⟩ : syracuseStep 9875195 = 14812793) B14812793
theorem B9711647 : Blo 1136633 9711647 := bstep (se 1 (by rfl) ⟨7283735, by rfl⟩ : syracuseStep 9711647 = 14567471) B14567471
theorem B4862369 : Blo 1136633 4862369 := bstep (se 2 (by rfl) ⟨1823388, by rfl⟩ : syracuseStep 4862369 = 3646777) B3646777
theorem B23671217 : Blo 1136633 23671217 := bstep (se 2 (by rfl) ⟨8876706, by rfl⟩ : syracuseStep 23671217 = 17753413) B17753413
theorem B12989321 : Blo 1136633 12989321 := bstep (se 2 (by rfl) ⟨4870995, by rfl⟩ : syracuseStep 12989321 = 9741991) B9741991
theorem B3847337 : Blo 1136633 3847337 := bstep (se 2 (by rfl) ⟨1442751, by rfl⟩ : syracuseStep 3847337 = 2885503) B2885503
theorem B78821909 : Blo 1136633 78821909 := bstep (se 6 (by rfl) ⟨1847388, by rfl⟩ : syracuseStep 78821909 = 3694777) B3694777
theorem B12958703 : Blo 1136633 12958703 := bstep (se 1 (by rfl) ⟨9719027, by rfl⟩ : syracuseStep 12958703 = 19438055) B19438055
theorem B11681759 : Blo 1136633 11681759 := bstep (se 1 (by rfl) ⟨8761319, by rfl⟩ : syracuseStep 11681759 = 17522639) B17522639
theorem B8765599 : Blo 1136633 8765599 := bstep (se 1 (by rfl) ⟨6574199, by rfl⟩ : syracuseStep 8765599 = 13148399) B13148399
theorem B4866281 : Blo 1136633 4866281 := bstep (se 2 (by rfl) ⟨1824855, by rfl⟩ : syracuseStep 4866281 = 3649711) B3649711
theorem B8209633 : Blo 1136633 8209633 := bstep (se 2 (by rfl) ⟨3078612, by rfl⟩ : syracuseStep 8209633 = 6157225) B6157225
theorem B18466541 : Blo 1136633 18466541 := bstep (se 3 (by rfl) ⟨3462476, by rfl⟩ : syracuseStep 18466541 = 6924953) B6924953
theorem B49235795 : Blo 1136633 49235795 := bstep (se 1 (by rfl) ⟨36926846, by rfl⟩ : syracuseStep 49235795 = 73853693) B73853693
theorem B303253445 : Blo 1136633 303253445 := bstep (se 4 (by rfl) ⟨28430010, by rfl⟩ : syracuseStep 303253445 = 56860021) B56860021
theorem B18435863 : Blo 1136633 18435863 := bstep (se 1 (by rfl) ⟨13826897, by rfl⟩ : syracuseStep 18435863 = 27653795) B27653795
theorem B1298207 : Blo 1136633 1298207 := bstep (se 1 (by rfl) ⟨973655, by rfl⟩ : syracuseStep 1298207 = 1947311) B1947311
theorem B4870313 : Blo 1136633 4870313 := bstep (se 2 (by rfl) ⟨1826367, by rfl⟩ : syracuseStep 4870313 = 3652735) B3652735
theorem B1921279 : Blo 1136633 1921279 := bstep (se 1 (by rfl) ⟨1440959, by rfl⟩ : syracuseStep 1921279 = 2881919) B2881919
theorem B136663375 : Blo 1136633 136663375 := bstep (se 1 (by rfl) ⟨102497531, by rfl⟩ : syracuseStep 136663375 = 204995063) B204995063
theorem B1922825 : Blo 1136633 1922825 := bstep (se 2 (by rfl) ⟨721059, by rfl⟩ : syracuseStep 1922825 = 1442119) B1442119
theorem B1136635 : Blo 1136633 1136635 := bstep (se 1 (by rfl) ⟨852476, by rfl⟩ : syracuseStep 1136635 = 1704953) B1704953
theorem B1136671 : Blo 1136633 1136671 := bstep (se 1 (by rfl) ⟨852503, by rfl⟩ : syracuseStep 1136671 = 1705007) B1705007
theorem B18438515 : Blo 1136633 18438515 := bstep (se 1 (by rfl) ⟨13828886, by rfl⟩ : syracuseStep 18438515 = 27657773) B27657773
theorem B1137151 : Blo 1136633 1137151 := bstep (se 1 (by rfl) ⟨852863, by rfl⟩ : syracuseStep 1137151 = 1705727) B1705727
theorem B1137599 : Blo 1136633 1137599 := bstep (se 1 (by rfl) ⟨853199, by rfl⟩ : syracuseStep 1137599 = 1706399) B1706399
theorem B1137903 : Blo 1136633 1137903 := bstep (se 1 (by rfl) ⟨853427, by rfl⟩ : syracuseStep 1137903 = 1706855) B1706855
theorem B1137967 : Blo 1136633 1137967 := bstep (se 1 (by rfl) ⟨853475, by rfl⟩ : syracuseStep 1137967 = 1706951) B1706951
theorem B14999279 : Blo 1136633 14999279 := bstep (se 1 (by rfl) ⟨11249459, by rfl⟩ : syracuseStep 14999279 = 22498919) B22498919
theorem B1138459 : Blo 1136633 1138459 := bstep (se 1 (by rfl) ⟨853844, by rfl⟩ : syracuseStep 1138459 = 1707689) B1707689
theorem B1138523 : Blo 1136633 1138523 := bstep (se 1 (by rfl) ⟨853892, by rfl⟩ : syracuseStep 1138523 = 1707785) B1707785
theorem B1138559 : Blo 1136633 1138559 := bstep (se 1 (by rfl) ⟨853919, by rfl⟩ : syracuseStep 1138559 = 1707839) B1707839
theorem B1138799 : Blo 1136633 1138799 := bstep (se 1 (by rfl) ⟨854099, by rfl⟩ : syracuseStep 1138799 = 1708199) B1708199
theorem B1139015 : Blo 1136633 1139015 := bstep (se 1 (by rfl) ⟨854261, by rfl⟩ : syracuseStep 1139015 = 1708523) B1708523
theorem B1139099 : Blo 1136633 1139099 := bstep (se 1 (by rfl) ⟨854324, by rfl⟩ : syracuseStep 1139099 = 1708649) B1708649
theorem B9724495 : Blo 1136633 9724495 := bstep (se 1 (by rfl) ⟨7293371, by rfl⟩ : syracuseStep 9724495 = 14586743) B14586743
theorem B1139291 : Blo 1136633 1139291 := bstep (se 1 (by rfl) ⟨854468, by rfl⟩ : syracuseStep 1139291 = 1708937) B1708937
theorem B4612733 : Blo 1136633 4612733 := bstep (se 3 (by rfl) ⟨864887, by rfl⟩ : syracuseStep 4612733 = 1729775) B1729775
theorem B1139355 : Blo 1136633 1139355 := bstep (se 1 (by rfl) ⟨854516, by rfl⟩ : syracuseStep 1139355 = 1709033) B1709033
theorem B1139391 : Blo 1136633 1139391 := bstep (se 1 (by rfl) ⟨854543, by rfl⟩ : syracuseStep 1139391 = 1709087) B1709087
theorem B1139547 : Blo 1136633 1139547 := bstep (se 1 (by rfl) ⟨854660, by rfl⟩ : syracuseStep 1139547 = 1709321) B1709321
theorem B1139867 : Blo 1136633 1139867 := bstep (se 1 (by rfl) ⟨854900, by rfl⟩ : syracuseStep 1139867 = 1709801) B1709801
theorem B4318703 : Blo 1136633 4318703 := bstep (se 1 (by rfl) ⟨3239027, by rfl⟩ : syracuseStep 4318703 = 6478055) B6478055
theorem B5465879 : Blo 1136633 5465879 := bstep (se 1 (by rfl) ⟨4099409, by rfl⟩ : syracuseStep 5465879 = 8198819) B8198819
theorem B1140591 : Blo 1136633 1140591 := bstep (se 1 (by rfl) ⟨855443, by rfl⟩ : syracuseStep 1140591 = 1710887) B1710887
theorem B4319507 : Blo 1136633 4319507 := bstep (se 1 (by rfl) ⟨3239630, by rfl⟩ : syracuseStep 4319507 = 6479261) B6479261
theorem B10513151 : Blo 1136633 10513151 := bstep (se 1 (by rfl) ⟨7884863, by rfl⟩ : syracuseStep 10513151 = 15769727) B15769727
theorem B6483179 : Blo 1136633 6483179 := bstep (se 1 (by rfl) ⟨4862384, by rfl⟩ : syracuseStep 6483179 = 9724769) B9724769
theorem B2879003 : Blo 1136633 2879003 := bstep (se 1 (by rfl) ⟨2159252, by rfl⟩ : syracuseStep 2879003 = 4318505) B4318505
theorem B4321147 : Blo 1136633 4321147 := bstep (se 1 (by rfl) ⟨3240860, by rfl⟩ : syracuseStep 4321147 = 6481721) B6481721
theorem B8646911 : Blo 1136633 8646911 := bstep (se 1 (by rfl) ⟨6485183, by rfl⟩ : syracuseStep 8646911 = 12970367) B12970367
theorem B10940831 : Blo 1136633 10940831 := bstep (se 1 (by rfl) ⟨8205623, by rfl⟩ : syracuseStep 10940831 = 16411247) B16411247
theorem B2159291 : Blo 1136633 2159291 := bstep (se 1 (by rfl) ⟨1619468, by rfl⟩ : syracuseStep 2159291 = 3238937) B3238937
theorem B5764769 : Blo 1136633 5764769 := bstep (se 2 (by rfl) ⟨2161788, by rfl⟩ : syracuseStep 5764769 = 4323577) B4323577
theorem B24606827 : Blo 1136633 24606827 := bstep (se 1 (by rfl) ⟨18455120, by rfl⟩ : syracuseStep 24606827 = 36910241) B36910241
theorem B2882729 : Blo 1136633 2882729 := bstep (se 2 (by rfl) ⟨1081023, by rfl⟩ : syracuseStep 2882729 = 2162047) B2162047
theorem B5766713 : Blo 1136633 5766713 := bstep (se 2 (by rfl) ⟨2162517, by rfl⟩ : syracuseStep 5766713 = 4325035) B4325035
theorem B11075143 : Blo 1136633 11075143 := bstep (se 1 (by rfl) ⟨8306357, by rfl⟩ : syracuseStep 11075143 = 16612715) B16612715
theorem B3244187 : Blo 1136633 3244187 := bstep (se 1 (by rfl) ⟨2433140, by rfl⟩ : syracuseStep 3244187 = 4866281) B4866281
theorem B1705451 : Blo 1136633 1705451 := bstep (se 1 (by rfl) ⟨1279088, by rfl⟩ : syracuseStep 1705451 = 2558177) B2558177
theorem B10946177 : Blo 1136633 10946177 := bstep (se 2 (by rfl) ⟨4104816, by rfl⟩ : syracuseStep 10946177 = 8209633) B8209633
theorem B1705895 : Blo 1136633 1705895 := bstep (se 1 (by rfl) ⟨1279421, by rfl⟩ : syracuseStep 1705895 = 2558843) B2558843
theorem B1705961 : Blo 1136633 1705961 := bstep (se 2 (by rfl) ⟨639735, by rfl⟩ : syracuseStep 1705961 = 1279471) B1279471
theorem B1705979 : Blo 1136633 1705979 := bstep (se 1 (by rfl) ⟨1279484, by rfl⟩ : syracuseStep 1705979 = 2558969) B2558969
theorem B2557979 : Blo 1136633 2557979 := bstep (se 1 (by rfl) ⟨1918484, by rfl⟩ : syracuseStep 2557979 = 3836969) B3836969
theorem B12290575 : Blo 1136633 12290575 := bstep (se 1 (by rfl) ⟨9217931, by rfl⟩ : syracuseStep 12290575 = 18435863) B18435863
theorem B2558555 : Blo 1136633 2558555 := bstep (se 1 (by rfl) ⟨1918916, by rfl⟩ : syracuseStep 2558555 = 3837833) B3837833
theorem B1706747 : Blo 1136633 1706747 := bstep (se 1 (by rfl) ⟨1280060, by rfl⟩ : syracuseStep 1706747 = 2560121) B2560121
theorem B3246875 : Blo 1136633 3246875 := bstep (se 1 (by rfl) ⟨2435156, by rfl⟩ : syracuseStep 3246875 = 4870313) B4870313
theorem B1707551 : Blo 1136633 1707551 := bstep (se 1 (by rfl) ⟨1280663, by rfl⟩ : syracuseStep 1707551 = 2561327) B2561327
theorem B5771087 : Blo 1136633 5771087 := bstep (se 1 (by rfl) ⟨4328315, by rfl⟩ : syracuseStep 5771087 = 8656631) B8656631
theorem B1281883 : Blo 1136633 1281883 := bstep (se 1 (by rfl) ⟨961412, by rfl⟩ : syracuseStep 1281883 = 1922825) B1922825
theorem B1708073 : Blo 1136633 1708073 := bstep (se 2 (by rfl) ⟨640527, by rfl⟩ : syracuseStep 1708073 = 1281055) B1281055
theorem B1708103 : Blo 1136633 1708103 := bstep (se 1 (by rfl) ⟨1281077, by rfl⟩ : syracuseStep 1708103 = 2562155) B2562155
theorem B12292343 : Blo 1136633 12292343 := bstep (se 1 (by rfl) ⟨9219257, by rfl⟩ : syracuseStep 12292343 = 18438515) B18438515
theorem B1708511 : Blo 1136633 1708511 := bstep (se 1 (by rfl) ⟨1281383, by rfl⟩ : syracuseStep 1708511 = 2562767) B2562767
theorem B2560967 : Blo 1136633 2560967 := bstep (se 1 (by rfl) ⟨1920725, by rfl⟩ : syracuseStep 2560967 = 3841451) B3841451
theorem B1709147 : Blo 1136633 1709147 := bstep (se 1 (by rfl) ⟨1281860, by rfl⟩ : syracuseStep 1709147 = 2563721) B2563721
theorem B5772383 : Blo 1136633 5772383 := bstep (se 1 (by rfl) ⟨4329287, by rfl⟩ : syracuseStep 5772383 = 8658575) B8658575
theorem B2561705 : Blo 1136633 2561705 := bstep (se 2 (by rfl) ⟨960639, by rfl⟩ : syracuseStep 2561705 = 1921279) B1921279
theorem B2561831 : Blo 1136633 2561831 := bstep (se 1 (by rfl) ⟨1921373, by rfl⟩ : syracuseStep 2561831 = 3842747) B3842747
theorem B1710059 : Blo 1136633 1710059 := bstep (se 1 (by rfl) ⟨1282544, by rfl⟩ : syracuseStep 1710059 = 2565089) B2565089
theorem B8657117 : Blo 1136633 8657117 := bstep (se 3 (by rfl) ⟨1623209, by rfl⟩ : syracuseStep 8657117 = 3246419) B3246419
theorem B3643919 : Blo 1136633 3643919 := bstep (se 1 (by rfl) ⟨2732939, by rfl⟩ : syracuseStep 3643919 = 5465879) B5465879
theorem B1710761 : Blo 1136633 1710761 := bstep (se 2 (by rfl) ⟨641535, by rfl⟩ : syracuseStep 1710761 = 1283071) B1283071
theorem B6495983 : Blo 1136633 6495983 := bstep (se 1 (by rfl) ⟨4871987, by rfl⟩ : syracuseStep 6495983 = 9743975) B9743975
theorem B8659547 : Blo 1136633 8659547 := bstep (se 1 (by rfl) ⟨6494660, by rfl⟩ : syracuseStep 8659547 = 12989321) B12989321
theorem B2564891 : Blo 1136633 2564891 := bstep (se 1 (by rfl) ⟨1923668, by rfl⟩ : syracuseStep 2564891 = 3847337) B3847337
theorem B3843179 : Blo 1136633 3843179 := bstep (se 1 (by rfl) ⟨2882384, by rfl⟩ : syracuseStep 3843179 = 5764769) B5764769
theorem B3844475 : Blo 1136633 3844475 := bstep (se 1 (by rfl) ⟨2883356, by rfl⟩ : syracuseStep 3844475 = 5766713) B5766713
theorem B63123245 : Blo 1136633 63123245 := bstep (se 3 (by rfl) ⟨11835608, by rfl⟩ : syracuseStep 63123245 = 23671217) B23671217
theorem B3846311 : Blo 1136633 3846311 := bstep (se 1 (by rfl) ⟨2884733, by rfl⟩ : syracuseStep 3846311 = 5769467) B5769467
theorem B3847067 : Blo 1136633 3847067 := bstep (se 1 (by rfl) ⟨2885300, by rfl⟩ : syracuseStep 3847067 = 5770601) B5770601
theorem B8631359 : Blo 1136633 8631359 := bstep (se 1 (by rfl) ⟨6473519, by rfl⟩ : syracuseStep 8631359 = 12947039) B12947039
theorem B3848039 : Blo 1136633 3848039 := bstep (se 1 (by rfl) ⟨2886029, by rfl⟩ : syracuseStep 3848039 = 5772059) B5772059
theorem B1948519 : Blo 1136633 1948519 := bstep (se 1 (by rfl) ⟨1461389, by rfl⟩ : syracuseStep 1948519 = 2922779) B2922779
theorem B124829585 : Blo 1136633 124829585 := bstep (se 2 (by rfl) ⟨46811094, by rfl⟩ : syracuseStep 124829585 = 93622189) B93622189
theorem B10928371 : Blo 1136633 10928371 := bstep (se 1 (by rfl) ⟨8196278, by rfl⟩ : syracuseStep 10928371 = 16392557) B16392557
theorem B10928681 : Blo 1136633 10928681 := bstep (se 2 (by rfl) ⟨4098255, by rfl⟩ : syracuseStep 10928681 = 8196511) B8196511
theorem B1919335 : Blo 1136633 1919335 := bstep (se 1 (by rfl) ⟨1439501, by rfl⟩ : syracuseStep 1919335 = 2879003) B2879003
theorem B159992309 : Blo 1136633 159992309 := bstep (se 5 (by rfl) ⟨7499639, by rfl⟩ : syracuseStep 159992309 = 14999279) B14999279
theorem B6474431 : Blo 1136633 6474431 := bstep (se 1 (by rfl) ⟨4855823, by rfl⟩ : syracuseStep 6474431 = 9711647) B9711647
theorem B7293887 : Blo 1136633 7293887 := bstep (se 1 (by rfl) ⟨5470415, by rfl⟩ : syracuseStep 7293887 = 10940831) B10940831
theorem B16404551 : Blo 1136633 16404551 := bstep (se 1 (by rfl) ⟨12303413, by rfl⟩ : syracuseStep 16404551 = 24606827) B24606827
theorem B52547939 : Blo 1136633 52547939 := bstep (se 1 (by rfl) ⟨39410954, by rfl⟩ : syracuseStep 52547939 = 78821909) B78821909
theorem B8639135 : Blo 1136633 8639135 := bstep (se 1 (by rfl) ⟨6479351, by rfl⟩ : syracuseStep 8639135 = 12958703) B12958703
theorem B3461885 : Blo 1136633 3461885 := bstep (se 3 (by rfl) ⟨649103, by rfl⟩ : syracuseStep 3461885 = 1298207) B1298207
theorem B14766857 : Blo 1136633 14766857 := bstep (se 2 (by rfl) ⟨5537571, by rfl⟩ : syracuseStep 14766857 = 11075143) B11075143
theorem B1921819 : Blo 1136633 1921819 := bstep (se 1 (by rfl) ⟨1441364, by rfl⟩ : syracuseStep 1921819 = 2882729) B2882729
theorem B7787839 : Blo 1136633 7787839 := bstep (se 1 (by rfl) ⟨5840879, by rfl⟩ : syracuseStep 7787839 = 11681759) B11681759
theorem B11687465 : Blo 1136633 11687465 := bstep (se 2 (by rfl) ⟨4382799, by rfl⟩ : syracuseStep 11687465 = 8765599) B8765599
theorem B12965993 : Blo 1136633 12965993 := bstep (se 2 (by rfl) ⟨4862247, by rfl⟩ : syracuseStep 12965993 = 9724495) B9724495
theorem B12311027 : Blo 1136633 12311027 := bstep (se 1 (by rfl) ⟨9233270, by rfl⟩ : syracuseStep 12311027 = 18466541) B18466541
theorem B32823863 : Blo 1136633 32823863 := bstep (se 1 (by rfl) ⟨24617897, by rfl⟩ : syracuseStep 32823863 = 49235795) B49235795
theorem B202168963 : Blo 1136633 202168963 := bstep (se 1 (by rfl) ⟨151626722, by rfl⟩ : syracuseStep 202168963 = 303253445) B303253445
theorem B1137407 : Blo 1136633 1137407 := bstep (se 1 (by rfl) ⟨853055, by rfl⟩ : syracuseStep 1137407 = 1706111) B1706111
theorem B1923871 : Blo 1136633 1923871 := bstep (se 1 (by rfl) ⟨1442903, by rfl⟩ : syracuseStep 1923871 = 2885807) B2885807
theorem B9722855 : Blo 1136633 9722855 := bstep (se 1 (by rfl) ⟨7292141, by rfl⟩ : syracuseStep 9722855 = 14584283) B14584283
theorem B3464617 : Blo 1136633 3464617 := bstep (se 2 (by rfl) ⟨1299231, by rfl⟩ : syracuseStep 3464617 = 2598463) B2598463
theorem B1138143 : Blo 1136633 1138143 := bstep (se 1 (by rfl) ⟨853607, by rfl⟩ : syracuseStep 1138143 = 1707215) B1707215
theorem B1138175 : Blo 1136633 1138175 := bstep (se 1 (by rfl) ⟨853631, by rfl⟩ : syracuseStep 1138175 = 1707263) B1707263
theorem B5463571 : Blo 1136633 5463571 := bstep (se 1 (by rfl) ⟨4097678, by rfl⟩ : syracuseStep 5463571 = 8195357) B8195357
theorem B1138279 : Blo 1136633 1138279 := bstep (se 1 (by rfl) ⟨853709, by rfl⟩ : syracuseStep 1138279 = 1707419) B1707419
theorem B1138911 : Blo 1136633 1138911 := bstep (se 1 (by rfl) ⟨854183, by rfl⟩ : syracuseStep 1138911 = 1708367) B1708367
theorem B10937369 : Blo 1136633 10937369 := bstep (se 2 (by rfl) ⟨4101513, by rfl⟩ : syracuseStep 10937369 = 8203027) B8203027
theorem B1139743 : Blo 1136633 1139743 := bstep (se 1 (by rfl) ⟨854807, by rfl⟩ : syracuseStep 1139743 = 1709615) B1709615
theorem B1140315 : Blo 1136633 1140315 := bstep (se 1 (by rfl) ⟨855236, by rfl⟩ : syracuseStep 1140315 = 1710473) B1710473
theorem B5761529 : Blo 1136633 5761529 := bstep (se 2 (by rfl) ⟨2160573, by rfl⟩ : syracuseStep 5761529 = 4321147) B4321147
theorem B3893851 : Blo 1136633 3893851 := bstep (se 1 (by rfl) ⟨2920388, by rfl⟩ : syracuseStep 3893851 = 5840777) B5840777
theorem B5925563 : Blo 1136633 5925563 := bstep (se 1 (by rfl) ⟨4444172, by rfl⟩ : syracuseStep 5925563 = 8888345) B8888345
theorem B3075155 : Blo 1136633 3075155 := bstep (se 1 (by rfl) ⟨2306366, by rfl⟩ : syracuseStep 3075155 = 4612733) B4612733
theorem B182217833 : Blo 1136633 182217833 := bstep (se 2 (by rfl) ⟨68331687, by rfl⟩ : syracuseStep 182217833 = 136663375) B136663375
theorem B7302575 : Blo 1136633 7302575 := bstep (se 1 (by rfl) ⟨5476931, by rfl⟩ : syracuseStep 7302575 = 10953863) B10953863
theorem B2879135 : Blo 1136633 2879135 := bstep (se 1 (by rfl) ⟨2159351, by rfl⟩ : syracuseStep 2879135 = 4318703) B4318703
theorem B2879671 : Blo 1136633 2879671 := bstep (se 1 (by rfl) ⟨2159753, by rfl⟩ : syracuseStep 2879671 = 4319507) B4319507
theorem B15593957 : Blo 1136633 15593957 := bstep (se 4 (by rfl) ⟨1461933, by rfl⟩ : syracuseStep 15593957 = 2923867) B2923867
theorem B7008767 : Blo 1136633 7008767 := bstep (se 1 (by rfl) ⟨5256575, by rfl⟩ : syracuseStep 7008767 = 10513151) B10513151
theorem B4322119 : Blo 1136633 4322119 := bstep (se 1 (by rfl) ⟨3241589, by rfl⟩ : syracuseStep 4322119 = 6483179) B6483179
theorem B6583463 : Blo 1136633 6583463 := bstep (se 1 (by rfl) ⟨4937597, by rfl⟩ : syracuseStep 6583463 = 9875195) B9875195
theorem B5764607 : Blo 1136633 5764607 := bstep (se 1 (by rfl) ⟨4323455, by rfl⟩ : syracuseStep 5764607 = 8646911) B8646911
theorem B3241579 : Blo 1136633 3241579 := bstep (se 1 (by rfl) ⟨2431184, by rfl⟩ : syracuseStep 3241579 = 4862369) B4862369
theorem B1439527 : Blo 1136633 1439527 := bstep (se 1 (by rfl) ⟨1079645, by rfl⟩ : syracuseStep 1439527 = 2159291) B2159291
theorem B6158501 : Blo 1136633 6158501 := bstep (se 4 (by rfl) ⟨577359, by rfl⟩ : syracuseStep 6158501 = 1154719) B1154719
theorem B2162791 : Blo 1136633 2162791 := bstep (se 1 (by rfl) ⟨1622093, by rfl⟩ : syracuseStep 2162791 = 3244187) B3244187
theorem B1705319 : Blo 1136633 1705319 := bstep (se 1 (by rfl) ⟨1278989, by rfl⟩ : syracuseStep 1705319 = 2557979) B2557979
theorem B106661539 : Blo 1136633 106661539 := bstep (se 1 (by rfl) ⟨79996154, by rfl⟩ : syracuseStep 106661539 = 159992309) B159992309
theorem B1705703 : Blo 1136633 1705703 := bstep (se 1 (by rfl) ⟨1279277, by rfl⟩ : syracuseStep 1705703 = 2558555) B2558555
theorem B2164583 : Blo 1136633 2164583 := bstep (se 1 (by rfl) ⟨1623437, by rfl⟩ : syracuseStep 2164583 = 3246875) B3246875
theorem B8194895 : Blo 1136633 8194895 := bstep (se 1 (by rfl) ⟨6146171, by rfl⟩ : syracuseStep 8194895 = 12292343) B12292343
theorem B35031959 : Blo 1136633 35031959 := bstep (se 1 (by rfl) ⟨26273969, by rfl⟩ : syracuseStep 35031959 = 52547939) B52547939
theorem B2559113 : Blo 1136633 2559113 := bstep (se 2 (by rfl) ⟨959667, by rfl⟩ : syracuseStep 2559113 = 1919335) B1919335
theorem B1707311 : Blo 1136633 1707311 := bstep (se 1 (by rfl) ⟨1280483, by rfl⟩ : syracuseStep 1707311 = 2560967) B2560967
theorem B16387433 : Blo 1136633 16387433 := bstep (se 2 (by rfl) ⟨6145287, by rfl⟩ : syracuseStep 16387433 = 12290575) B12290575
theorem B1707803 : Blo 1136633 1707803 := bstep (se 1 (by rfl) ⟨1280852, by rfl⟩ : syracuseStep 1707803 = 2561705) B2561705
theorem B1707887 : Blo 1136633 1707887 := bstep (se 1 (by rfl) ⟨1280915, by rfl⟩ : syracuseStep 1707887 = 2561831) B2561831
theorem B5771411 : Blo 1136633 5771411 := bstep (se 1 (by rfl) ⟨4328558, by rfl⟩ : syracuseStep 5771411 = 8657117) B8657117
theorem B2429279 : Blo 1136633 2429279 := bstep (se 1 (by rfl) ⟨1821959, by rfl⟩ : syracuseStep 2429279 = 3643919) B3643919
theorem B10392101 : Blo 1136633 10392101 := bstep (se 4 (by rfl) ⟨974259, by rfl⟩ : syracuseStep 10392101 = 1948519) B1948519
theorem B1709177 : Blo 1136633 1709177 := bstep (se 2 (by rfl) ⟨640941, by rfl⟩ : syracuseStep 1709177 = 1281883) B1281883
theorem B4330655 : Blo 1136633 4330655 := bstep (se 1 (by rfl) ⟨3247991, by rfl⟩ : syracuseStep 4330655 = 6495983) B6495983
theorem B3839561 : Blo 1136633 3839561 := bstep (se 2 (by rfl) ⟨1439835, by rfl⟩ : syracuseStep 3839561 = 2879671) B2879671
theorem B5773031 : Blo 1136633 5773031 := bstep (se 1 (by rfl) ⟨4329773, by rfl⟩ : syracuseStep 5773031 = 8659547) B8659547
theorem B1709927 : Blo 1136633 1709927 := bstep (se 1 (by rfl) ⟨1282445, by rfl⟩ : syracuseStep 1709927 = 2564891) B2564891
theorem B2562119 : Blo 1136633 2562119 := bstep (se 1 (by rfl) ⟨1921589, by rfl⟩ : syracuseStep 2562119 = 3843179) B3843179
theorem B2562425 : Blo 1136633 2562425 := bstep (se 2 (by rfl) ⟨960909, by rfl⟩ : syracuseStep 2562425 = 1921819) B1921819
theorem B2562983 : Blo 1136633 2562983 := bstep (se 1 (by rfl) ⟨1922237, by rfl⟩ : syracuseStep 2562983 = 3844475) B3844475
theorem B3841019 : Blo 1136633 3841019 := bstep (se 1 (by rfl) ⟨2880764, by rfl⟩ : syracuseStep 3841019 = 5761529) B5761529
theorem B121478555 : Blo 1136633 121478555 := bstep (se 1 (by rfl) ⟨91108916, by rfl⟩ : syracuseStep 121478555 = 182217833) B182217833
theorem B42082163 : Blo 1136633 42082163 := bstep (se 1 (by rfl) ⟨31561622, by rfl⟩ : syracuseStep 42082163 = 63123245) B63123245
theorem B2564207 : Blo 1136633 2564207 := bstep (se 1 (by rfl) ⟨1923155, by rfl⟩ : syracuseStep 2564207 = 3846311) B3846311
theorem B10395971 : Blo 1136633 10395971 := bstep (se 1 (by rfl) ⟨7796978, by rfl⟩ : syracuseStep 10395971 = 15593957) B15593957
theorem B2564711 : Blo 1136633 2564711 := bstep (se 1 (by rfl) ⟨1923533, by rfl⟩ : syracuseStep 2564711 = 3847067) B3847067
theorem B269558617 : Blo 1136633 269558617 := bstep (se 2 (by rfl) ⟨101084481, by rfl⟩ : syracuseStep 269558617 = 202168963) B202168963
theorem B3843071 : Blo 1136633 3843071 := bstep (se 1 (by rfl) ⟨2882303, by rfl⟩ : syracuseStep 3843071 = 5764607) B5764607
theorem B2565161 : Blo 1136633 2565161 := bstep (se 2 (by rfl) ⟨961935, by rfl⟩ : syracuseStep 2565161 = 1923871) B1923871
theorem B2565359 : Blo 1136633 2565359 := bstep (se 1 (by rfl) ⟨1924019, by rfl⟩ : syracuseStep 2565359 = 3848039) B3848039
theorem B4105667 : Blo 1136633 4105667 := bstep (se 1 (by rfl) ⟨3079250, by rfl⟩ : syracuseStep 4105667 = 6158501) B6158501
theorem B7284761 : Blo 1136633 7284761 := bstep (se 2 (by rfl) ⟨2731785, by rfl⟩ : syracuseStep 7284761 = 5463571) B5463571
theorem B7285787 : Blo 1136633 7285787 := bstep (se 1 (by rfl) ⟨5464340, by rfl⟩ : syracuseStep 7285787 = 10928681) B10928681
theorem B4862591 : Blo 1136633 4862591 := bstep (se 1 (by rfl) ⟨3646943, by rfl⟩ : syracuseStep 4862591 = 7293887) B7293887
theorem B3847391 : Blo 1136633 3847391 := bstep (se 1 (by rfl) ⟨2885543, by rfl⟩ : syracuseStep 3847391 = 5771087) B5771087
theorem B2307923 : Blo 1136633 2307923 := bstep (se 1 (by rfl) ⟨1730942, by rfl⟩ : syracuseStep 2307923 = 3461885) B3461885
theorem B9844571 : Blo 1136633 9844571 := bstep (se 1 (by rfl) ⟨7383428, by rfl⟩ : syracuseStep 9844571 = 14766857) B14766857
theorem B3848255 : Blo 1136633 3848255 := bstep (se 1 (by rfl) ⟨2886191, by rfl⟩ : syracuseStep 3848255 = 5772383) B5772383
theorem B8207351 : Blo 1136633 8207351 := bstep (se 1 (by rfl) ⟨6155513, by rfl⟩ : syracuseStep 8207351 = 12311027) B12311027
theorem B7291579 : Blo 1136633 7291579 := bstep (se 1 (by rfl) ⟨5468684, by rfl⟩ : syracuseStep 7291579 = 10937369) B10937369
theorem B3950375 : Blo 1136633 3950375 := bstep (se 1 (by rfl) ⟨2962781, by rfl⟩ : syracuseStep 3950375 = 5925563) B5925563
theorem B2050103 : Blo 1136633 2050103 := bstep (se 1 (by rfl) ⟨1537577, by rfl⟩ : syracuseStep 2050103 = 3075155) B3075155
theorem B4868383 : Blo 1136633 4868383 := bstep (se 1 (by rfl) ⟨3651287, by rfl⟩ : syracuseStep 4868383 = 7302575) B7302575
theorem B1919369 : Blo 1136633 1919369 := bstep (se 2 (by rfl) ⟨719763, by rfl⟩ : syracuseStep 1919369 = 1439527) B1439527
theorem B1919423 : Blo 1136633 1919423 := bstep (se 1 (by rfl) ⟨1439567, by rfl⟩ : syracuseStep 1919423 = 2879135) B2879135
theorem B4672511 : Blo 1136633 4672511 := bstep (se 1 (by rfl) ⟨3504383, by rfl⟩ : syracuseStep 4672511 = 7008767) B7008767
theorem B5754239 : Blo 1136633 5754239 := bstep (se 1 (by rfl) ⟨4315679, by rfl⟩ : syracuseStep 5754239 = 8631359) B8631359
theorem B83219723 : Blo 1136633 83219723 := bstep (se 1 (by rfl) ⟨62414792, by rfl⟩ : syracuseStep 83219723 = 124829585) B124829585
theorem B14571161 : Blo 1136633 14571161 := bstep (se 2 (by rfl) ⟨5464185, by rfl⟩ : syracuseStep 14571161 = 10928371) B10928371
theorem B1136967 : Blo 1136633 1136967 := bstep (se 1 (by rfl) ⟨852725, by rfl⟩ : syracuseStep 1136967 = 1705451) B1705451
theorem B7297451 : Blo 1136633 7297451 := bstep (se 1 (by rfl) ⟨5473088, by rfl⟩ : syracuseStep 7297451 = 10946177) B10946177
theorem B1137263 : Blo 1136633 1137263 := bstep (se 1 (by rfl) ⟨852947, by rfl⟩ : syracuseStep 1137263 = 1705895) B1705895
theorem B1137307 : Blo 1136633 1137307 := bstep (se 1 (by rfl) ⟨852980, by rfl⟩ : syracuseStep 1137307 = 1705961) B1705961
theorem B1137319 : Blo 1136633 1137319 := bstep (se 1 (by rfl) ⟨852989, by rfl⟩ : syracuseStep 1137319 = 1705979) B1705979
theorem B4316287 : Blo 1136633 4316287 := bstep (se 1 (by rfl) ⟨3237215, by rfl⟩ : syracuseStep 4316287 = 6474431) B6474431
theorem B1137831 : Blo 1136633 1137831 := bstep (se 1 (by rfl) ⟨853373, by rfl⟩ : syracuseStep 1137831 = 1706747) B1706747
theorem B1138367 : Blo 1136633 1138367 := bstep (se 1 (by rfl) ⟨853775, by rfl⟩ : syracuseStep 1138367 = 1707551) B1707551
theorem B1138715 : Blo 1136633 1138715 := bstep (se 1 (by rfl) ⟨854036, by rfl⟩ : syracuseStep 1138715 = 1708073) B1708073
theorem B10936367 : Blo 1136633 10936367 := bstep (se 1 (by rfl) ⟨8202275, by rfl⟩ : syracuseStep 10936367 = 16404551) B16404551
theorem B1138735 : Blo 1136633 1138735 := bstep (se 1 (by rfl) ⟨854051, by rfl⟩ : syracuseStep 1138735 = 1708103) B1708103
theorem B1139007 : Blo 1136633 1139007 := bstep (se 1 (by rfl) ⟨854255, by rfl⟩ : syracuseStep 1139007 = 1708511) B1708511
theorem B5759423 : Blo 1136633 5759423 := bstep (se 1 (by rfl) ⟨4319567, by rfl⟩ : syracuseStep 5759423 = 8639135) B8639135
theorem B20767205 : Blo 1136633 20767205 := bstep (se 4 (by rfl) ⟨1946925, by rfl⟩ : syracuseStep 20767205 = 3893851) B3893851
theorem B1139431 : Blo 1136633 1139431 := bstep (se 1 (by rfl) ⟨854573, by rfl⟩ : syracuseStep 1139431 = 1709147) B1709147
theorem B7791643 : Blo 1136633 7791643 := bstep (se 1 (by rfl) ⟨5843732, by rfl⟩ : syracuseStep 7791643 = 11687465) B11687465
theorem B1140039 : Blo 1136633 1140039 := bstep (se 1 (by rfl) ⟨855029, by rfl⟩ : syracuseStep 1140039 = 1710059) B1710059
theorem B8643995 : Blo 1136633 8643995 := bstep (se 1 (by rfl) ⟨6482996, by rfl⟩ : syracuseStep 8643995 = 12965993) B12965993
theorem B21882575 : Blo 1136633 21882575 := bstep (se 1 (by rfl) ⟨16411931, by rfl⟩ : syracuseStep 21882575 = 32823863) B32823863
theorem B1140507 : Blo 1136633 1140507 := bstep (se 1 (by rfl) ⟨855380, by rfl⟩ : syracuseStep 1140507 = 1710761) B1710761
theorem B6481903 : Blo 1136633 6481903 := bstep (se 1 (by rfl) ⟨4861427, by rfl⟩ : syracuseStep 6481903 = 9722855) B9722855
theorem B5762825 : Blo 1136633 5762825 := bstep (se 2 (by rfl) ⟨2161059, by rfl⟩ : syracuseStep 5762825 = 4322119) B4322119
theorem B10383785 : Blo 1136633 10383785 := bstep (se 2 (by rfl) ⟨3893919, by rfl⟩ : syracuseStep 10383785 = 7787839) B7787839
theorem B4322105 : Blo 1136633 4322105 := bstep (se 2 (by rfl) ⟨1620789, by rfl⟩ : syracuseStep 4322105 = 3241579) B3241579
theorem B4388975 : Blo 1136633 4388975 := bstep (se 1 (by rfl) ⟨3291731, by rfl⟩ : syracuseStep 4388975 = 6583463) B6583463
theorem B4619489 : Blo 1136633 4619489 := bstep (se 2 (by rfl) ⟨1732308, by rfl⟩ : syracuseStep 4619489 = 3464617) B3464617
theorem B2883721 : Blo 1136633 2883721 := bstep (se 2 (by rfl) ⟨1081395, by rfl⟩ : syracuseStep 2883721 = 2162791) B2162791
theorem B1279579 : Blo 1136633 1279579 := bstep (se 1 (by rfl) ⟨959684, by rfl⟩ : syracuseStep 1279579 = 1919369) B1919369
theorem B1279615 : Blo 1136633 1279615 := bstep (se 1 (by rfl) ⟨959711, by rfl⟩ : syracuseStep 1279615 = 1919423) B1919423
theorem B3115007 : Blo 1136633 3115007 := bstep (se 1 (by rfl) ⟨2336255, by rfl⟩ : syracuseStep 3115007 = 4672511) B4672511
theorem B1706075 : Blo 1136633 1706075 := bstep (se 1 (by rfl) ⟨1279556, by rfl⟩ : syracuseStep 1706075 = 2559113) B2559113
theorem B3836159 : Blo 1136633 3836159 := bstep (se 1 (by rfl) ⟨2877119, by rfl⟩ : syracuseStep 3836159 = 5754239) B5754239
theorem B6491177 : Blo 1136633 6491177 := bstep (se 2 (by rfl) ⟨2434191, by rfl⟩ : syracuseStep 6491177 = 4868383) B4868383
theorem B2887103 : Blo 1136633 2887103 := bstep (se 1 (by rfl) ⟨2165327, by rfl⟩ : syracuseStep 2887103 = 4330655) B4330655
theorem B55479815 : Blo 1136633 55479815 := bstep (se 1 (by rfl) ⟨41609861, by rfl⟩ : syracuseStep 55479815 = 83219723) B83219723
theorem B2559707 : Blo 1136633 2559707 := bstep (se 1 (by rfl) ⟨1919780, by rfl⟩ : syracuseStep 2559707 = 3839561) B3839561
theorem B1708079 : Blo 1136633 1708079 := bstep (se 1 (by rfl) ⟨1281059, by rfl⟩ : syracuseStep 1708079 = 2562119) B2562119
theorem B1708283 : Blo 1136633 1708283 := bstep (se 1 (by rfl) ⟨1281212, by rfl⟩ : syracuseStep 1708283 = 2562425) B2562425
theorem B1708655 : Blo 1136633 1708655 := bstep (se 1 (by rfl) ⟨1281491, by rfl⟩ : syracuseStep 1708655 = 2562983) B2562983
theorem B2560679 : Blo 1136633 2560679 := bstep (se 1 (by rfl) ⟨1920509, by rfl⟩ : syracuseStep 2560679 = 3841019) B3841019
theorem B5772221 : Blo 1136633 5772221 := bstep (se 3 (by rfl) ⟨1082291, by rfl⟩ : syracuseStep 5772221 = 2164583) B2164583
theorem B28054775 : Blo 1136633 28054775 := bstep (se 1 (by rfl) ⟨21041081, by rfl⟩ : syracuseStep 28054775 = 42082163) B42082163
theorem B1709471 : Blo 1136633 1709471 := bstep (se 1 (by rfl) ⟨1282103, by rfl⟩ : syracuseStep 1709471 = 2564207) B2564207
theorem B41555429 : Blo 1136633 41555429 := bstep (se 4 (by rfl) ⟨3895821, by rfl⟩ : syracuseStep 41555429 = 7791643) B7791643
theorem B3839615 : Blo 1136633 3839615 := bstep (se 1 (by rfl) ⟨2879711, by rfl⟩ : syracuseStep 3839615 = 5759423) B5759423
theorem B1709807 : Blo 1136633 1709807 := bstep (se 1 (by rfl) ⟨1282355, by rfl⟩ : syracuseStep 1709807 = 2564711) B2564711
theorem B2562047 : Blo 1136633 2562047 := bstep (se 1 (by rfl) ⟨1921535, by rfl⟩ : syracuseStep 2562047 = 3843071) B3843071
theorem B1710107 : Blo 1136633 1710107 := bstep (se 1 (by rfl) ⟨1282580, by rfl⟩ : syracuseStep 1710107 = 2565161) B2565161
theorem B1710239 : Blo 1136633 1710239 := bstep (se 1 (by rfl) ⟨1282679, by rfl⟩ : syracuseStep 1710239 = 2565359) B2565359
theorem B14588383 : Blo 1136633 14588383 := bstep (se 1 (by rfl) ⟨10941287, by rfl⟩ : syracuseStep 14588383 = 21882575) B21882575
theorem B4856507 : Blo 1136633 4856507 := bstep (se 1 (by rfl) ⟨3642380, by rfl⟩ : syracuseStep 4856507 = 7284761) B7284761
theorem B4857191 : Blo 1136633 4857191 := bstep (se 1 (by rfl) ⟨3642893, by rfl⟩ : syracuseStep 4857191 = 7285787) B7285787
theorem B3841883 : Blo 1136633 3841883 := bstep (se 1 (by rfl) ⟨2881412, by rfl⟩ : syracuseStep 3841883 = 5762825) B5762825
theorem B6922523 : Blo 1136633 6922523 := bstep (se 1 (by rfl) ⟨5191892, by rfl⟩ : syracuseStep 6922523 = 10383785) B10383785
theorem B2564927 : Blo 1136633 2564927 := bstep (se 1 (by rfl) ⟨1923695, by rfl⟩ : syracuseStep 2564927 = 3847391) B3847391
theorem B568861541 : Blo 1136633 568861541 := bstep (se 4 (by rfl) ⟨53330769, by rfl⟩ : syracuseStep 568861541 = 106661539) B106661539
theorem B6563047 : Blo 1136633 6563047 := bstep (se 1 (by rfl) ⟨4922285, by rfl⟩ : syracuseStep 6563047 = 9844571) B9844571
theorem B2565503 : Blo 1136633 2565503 := bstep (se 1 (by rfl) ⟨1924127, by rfl⟩ : syracuseStep 2565503 = 3848255) B3848255
theorem B2925983 : Blo 1136633 2925983 := bstep (se 1 (by rfl) ⟨2194487, by rfl⟩ : syracuseStep 2925983 = 4388975) B4388975
theorem B359411489 : Blo 1136633 359411489 := bstep (se 2 (by rfl) ⟨134779308, by rfl⟩ : syracuseStep 359411489 = 269558617) B269558617
theorem B10924955 : Blo 1136633 10924955 := bstep (se 1 (by rfl) ⟨8193716, by rfl⟩ : syracuseStep 10924955 = 16387433) B16387433
theorem B3847607 : Blo 1136633 3847607 := bstep (se 1 (by rfl) ⟨2885705, by rfl⟩ : syracuseStep 3847607 = 5771411) B5771411
theorem B1619519 : Blo 1136633 1619519 := bstep (se 1 (by rfl) ⟨1214639, by rfl⟩ : syracuseStep 1619519 = 2429279) B2429279
theorem B6928067 : Blo 1136633 6928067 := bstep (se 1 (by rfl) ⟨5196050, by rfl⟩ : syracuseStep 6928067 = 10392101) B10392101
theorem B9714107 : Blo 1136633 9714107 := bstep (se 1 (by rfl) ⟨7285580, by rfl⟩ : syracuseStep 9714107 = 14571161) B14571161
theorem B3848687 : Blo 1136633 3848687 := bstep (se 1 (by rfl) ⟨2886515, by rfl⟩ : syracuseStep 3848687 = 5773031) B5773031
theorem B4864967 : Blo 1136633 4864967 := bstep (se 1 (by rfl) ⟨3648725, by rfl⟩ : syracuseStep 4864967 = 7297451) B7297451
theorem B80985703 : Blo 1136633 80985703 := bstep (se 1 (by rfl) ⟨60739277, by rfl⟩ : syracuseStep 80985703 = 121478555) B121478555
theorem B7290911 : Blo 1136633 7290911 := bstep (se 1 (by rfl) ⟨5468183, by rfl⟩ : syracuseStep 7290911 = 10936367) B10936367
theorem B6930647 : Blo 1136633 6930647 := bstep (se 1 (by rfl) ⟨5197985, by rfl⟩ : syracuseStep 6930647 = 10395971) B10395971
theorem B13844803 : Blo 1136633 13844803 := bstep (se 1 (by rfl) ⟨10383602, by rfl⟩ : syracuseStep 13844803 = 20767205) B20767205
theorem B2737111 : Blo 1136633 2737111 := bstep (se 1 (by rfl) ⟨2052833, by rfl⟩ : syracuseStep 2737111 = 4105667) B4105667
theorem B5755049 : Blo 1136633 5755049 := bstep (se 2 (by rfl) ⟨2158143, by rfl⟩ : syracuseStep 5755049 = 4316287) B4316287
theorem B1136879 : Blo 1136633 1136879 := bstep (se 1 (by rfl) ⟨852659, by rfl⟩ : syracuseStep 1136879 = 1705319) B1705319
theorem B9722105 : Blo 1136633 9722105 := bstep (se 2 (by rfl) ⟨3645789, by rfl⟩ : syracuseStep 9722105 = 7291579) B7291579
theorem B1137135 : Blo 1136633 1137135 := bstep (se 1 (by rfl) ⟨852851, by rfl⟩ : syracuseStep 1137135 = 1705703) B1705703
theorem B1366735 : Blo 1136633 1366735 := bstep (se 1 (by rfl) ⟨1025051, by rfl⟩ : syracuseStep 1366735 = 2050103) B2050103
theorem B5463263 : Blo 1136633 5463263 := bstep (se 1 (by rfl) ⟨4097447, by rfl⟩ : syracuseStep 5463263 = 8194895) B8194895
theorem B23354639 : Blo 1136633 23354639 := bstep (se 1 (by rfl) ⟨17515979, by rfl⟩ : syracuseStep 23354639 = 35031959) B35031959
theorem B1138207 : Blo 1136633 1138207 := bstep (se 1 (by rfl) ⟨853655, by rfl⟩ : syracuseStep 1138207 = 1707311) B1707311
theorem B1138535 : Blo 1136633 1138535 := bstep (se 1 (by rfl) ⟨853901, by rfl⟩ : syracuseStep 1138535 = 1707803) B1707803
theorem B1138591 : Blo 1136633 1138591 := bstep (se 1 (by rfl) ⟨853943, by rfl⟩ : syracuseStep 1138591 = 1707887) B1707887
theorem B8642537 : Blo 1136633 8642537 := bstep (se 2 (by rfl) ⟨3240951, by rfl⟩ : syracuseStep 8642537 = 6481903) B6481903
theorem B1139451 : Blo 1136633 1139451 := bstep (se 1 (by rfl) ⟨854588, by rfl⟩ : syracuseStep 1139451 = 1709177) B1709177
theorem B1139951 : Blo 1136633 1139951 := bstep (se 1 (by rfl) ⟨854963, by rfl⟩ : syracuseStep 1139951 = 1709927) B1709927
theorem B5762663 : Blo 1136633 5762663 := bstep (se 1 (by rfl) ⟨4321997, by rfl⟩ : syracuseStep 5762663 = 8643995) B8643995
theorem B42137333 : Blo 1136633 42137333 := bstep (se 5 (by rfl) ⟨1975187, by rfl⟩ : syracuseStep 42137333 = 3950375) B3950375
theorem B3241727 : Blo 1136633 3241727 := bstep (se 1 (by rfl) ⟨2431295, by rfl⟩ : syracuseStep 3241727 = 4862591) B4862591
theorem B2881403 : Blo 1136633 2881403 := bstep (se 1 (by rfl) ⟨2161052, by rfl⟩ : syracuseStep 2881403 = 4322105) B4322105
theorem B12318637 : Blo 1136633 12318637 := bstep (se 3 (by rfl) ⟨2309744, by rfl⟩ : syracuseStep 12318637 = 4619489) B4619489
theorem B1538615 : Blo 1136633 1538615 := bstep (se 1 (by rfl) ⟨1153961, by rfl⟩ : syracuseStep 1538615 = 2307923) B2307923
theorem B5471567 : Blo 1136633 5471567 := bstep (se 1 (by rfl) ⟨4103675, by rfl⟩ : syracuseStep 5471567 = 8207351) B8207351
theorem B4620431 : Blo 1136633 4620431 := bstep (se 1 (by rfl) ⟨3465323, by rfl⟩ : syracuseStep 4620431 = 6930647) B6930647
theorem B2557439 : Blo 1136633 2557439 := bstep (se 1 (by rfl) ⟨1918079, by rfl⟩ : syracuseStep 2557439 = 3836159) B3836159
theorem B8750729 : Blo 1136633 8750729 := bstep (se 2 (by rfl) ⟨3281523, by rfl⟩ : syracuseStep 8750729 = 6563047) B6563047
theorem B4327451 : Blo 1136633 4327451 := bstep (se 1 (by rfl) ⟨3245588, by rfl⟩ : syracuseStep 4327451 = 6491177) B6491177
theorem B1706105 : Blo 1136633 1706105 := bstep (se 2 (by rfl) ⟨639789, by rfl⟩ : syracuseStep 1706105 = 1279579) B1279579
theorem B1706153 : Blo 1136633 1706153 := bstep (se 2 (by rfl) ⟨639807, by rfl⟩ : syracuseStep 1706153 = 1279615) B1279615
theorem B1706471 : Blo 1136633 1706471 := bstep (se 1 (by rfl) ⟨1279853, by rfl⟩ : syracuseStep 1706471 = 2559707) B2559707
theorem B3836699 : Blo 1136633 3836699 := bstep (se 1 (by rfl) ⟨2877524, by rfl⟩ : syracuseStep 3836699 = 5755049) B5755049
theorem B1707119 : Blo 1136633 1707119 := bstep (se 1 (by rfl) ⟨1280339, by rfl⟩ : syracuseStep 1707119 = 2560679) B2560679
theorem B2559743 : Blo 1136633 2559743 := bstep (se 1 (by rfl) ⟨1919807, by rfl⟩ : syracuseStep 2559743 = 3839615) B3839615
theorem B1708031 : Blo 1136633 1708031 := bstep (se 1 (by rfl) ⟨1281023, by rfl⟩ : syracuseStep 1708031 = 2562047) B2562047
theorem B3642175 : Blo 1136633 3642175 := bstep (se 1 (by rfl) ⟨2731631, by rfl⟩ : syracuseStep 3642175 = 5463263) B5463263
theorem B15569759 : Blo 1136633 15569759 := bstep (se 1 (by rfl) ⟨11677319, by rfl⟩ : syracuseStep 15569759 = 23354639) B23354639
theorem B2561255 : Blo 1136633 2561255 := bstep (se 1 (by rfl) ⟨1920941, by rfl⟩ : syracuseStep 2561255 = 3841883) B3841883
theorem B1709951 : Blo 1136633 1709951 := bstep (se 1 (by rfl) ⟨1282463, by rfl⟩ : syracuseStep 1709951 = 2564927) B2564927
theorem B1710335 : Blo 1136633 1710335 := bstep (se 1 (by rfl) ⟨1282751, by rfl⟩ : syracuseStep 1710335 = 2565503) B2565503
theorem B4102973 : Blo 1136633 4102973 := bstep (se 3 (by rfl) ⟨769307, by rfl⟩ : syracuseStep 4102973 = 1538615) B1538615
theorem B3841775 : Blo 1136633 3841775 := bstep (se 1 (by rfl) ⟨2881331, by rfl⟩ : syracuseStep 3841775 = 5762663) B5762663
theorem B239607659 : Blo 1136633 239607659 := bstep (se 1 (by rfl) ⟨179705744, by rfl⟩ : syracuseStep 239607659 = 359411489) B359411489
theorem B16424849 : Blo 1136633 16424849 := bstep (se 2 (by rfl) ⟨6159318, by rfl⟩ : syracuseStep 16424849 = 12318637) B12318637
theorem B7283303 : Blo 1136633 7283303 := bstep (se 1 (by rfl) ⟨5462477, by rfl⟩ : syracuseStep 7283303 = 10924955) B10924955
theorem B2565071 : Blo 1136633 2565071 := bstep (se 1 (by rfl) ⟨1923803, by rfl⟩ : syracuseStep 2565071 = 3847607) B3847607
theorem B28091555 : Blo 1136633 28091555 := bstep (se 1 (by rfl) ⟨21068666, by rfl⟩ : syracuseStep 28091555 = 42137333) B42137333
theorem B2565791 : Blo 1136633 2565791 := bstep (se 1 (by rfl) ⟨1924343, by rfl⟩ : syracuseStep 2565791 = 3848687) B3848687
theorem B107980937 : Blo 1136633 107980937 := bstep (se 2 (by rfl) ⟨40492851, by rfl⟩ : syracuseStep 107980937 = 80985703) B80985703
theorem B3647711 : Blo 1136633 3647711 := bstep (se 1 (by rfl) ⟨2735783, by rfl⟩ : syracuseStep 3647711 = 5471567) B5471567
theorem B19442429 : Blo 1136633 19442429 := bstep (se 3 (by rfl) ⟨3645455, by rfl⟩ : syracuseStep 19442429 = 7290911) B7290911
theorem B3844961 : Blo 1136633 3844961 := bstep (se 2 (by rfl) ⟨1441860, by rfl⟩ : syracuseStep 3844961 = 2883721) B2883721
theorem B18459737 : Blo 1136633 18459737 := bstep (se 2 (by rfl) ⟨6922401, by rfl⟩ : syracuseStep 18459737 = 13844803) B13844803
theorem B3649481 : Blo 1136633 3649481 := bstep (se 2 (by rfl) ⟨1368555, by rfl⟩ : syracuseStep 3649481 = 2737111) B2737111
theorem B2076671 : Blo 1136633 2076671 := bstep (se 1 (by rfl) ⟨1557503, by rfl⟩ : syracuseStep 2076671 = 3115007) B3115007
theorem B3848147 : Blo 1136633 3848147 := bstep (se 1 (by rfl) ⟨2886110, by rfl⟩ : syracuseStep 3848147 = 5772221) B5772221
theorem B27703619 : Blo 1136633 27703619 := bstep (se 1 (by rfl) ⟨20777714, by rfl⟩ : syracuseStep 27703619 = 41555429) B41555429
theorem B379241027 : Blo 1136633 379241027 := bstep (se 1 (by rfl) ⟨284430770, by rfl⟩ : syracuseStep 379241027 = 568861541) B568861541
theorem B1950655 : Blo 1136633 1950655 := bstep (se 1 (by rfl) ⟨1462991, by rfl⟩ : syracuseStep 1950655 = 2925983) B2925983
theorem B19451177 : Blo 1136633 19451177 := bstep (se 2 (by rfl) ⟨7294191, by rfl⟩ : syracuseStep 19451177 = 14588383) B14588383
theorem B1822313 : Blo 1136633 1822313 := bstep (se 2 (by rfl) ⟨683367, by rfl⟩ : syracuseStep 1822313 = 1366735) B1366735
theorem B1920935 : Blo 1136633 1920935 := bstep (se 1 (by rfl) ⟨1440701, by rfl⟩ : syracuseStep 1920935 = 2881403) B2881403
theorem B6476071 : Blo 1136633 6476071 := bstep (se 1 (by rfl) ⟨4857053, by rfl⟩ : syracuseStep 6476071 = 9714107) B9714107
theorem B1137383 : Blo 1136633 1137383 := bstep (se 1 (by rfl) ⟨853037, by rfl⟩ : syracuseStep 1137383 = 1706075) B1706075
theorem B1924735 : Blo 1136633 1924735 := bstep (se 1 (by rfl) ⟨1443551, by rfl⟩ : syracuseStep 1924735 = 2887103) B2887103
theorem B36986543 : Blo 1136633 36986543 := bstep (se 1 (by rfl) ⟨27739907, by rfl⟩ : syracuseStep 36986543 = 55479815) B55479815
theorem B1138719 : Blo 1136633 1138719 := bstep (se 1 (by rfl) ⟨854039, by rfl⟩ : syracuseStep 1138719 = 1708079) B1708079
theorem B1138855 : Blo 1136633 1138855 := bstep (se 1 (by rfl) ⟨854141, by rfl⟩ : syracuseStep 1138855 = 1708283) B1708283
theorem B1139103 : Blo 1136633 1139103 := bstep (se 1 (by rfl) ⟨854327, by rfl⟩ : syracuseStep 1139103 = 1708655) B1708655
theorem B18703183 : Blo 1136633 18703183 := bstep (se 1 (by rfl) ⟨14027387, by rfl⟩ : syracuseStep 18703183 = 28054775) B28054775
theorem B1139647 : Blo 1136633 1139647 := bstep (se 1 (by rfl) ⟨854735, by rfl⟩ : syracuseStep 1139647 = 1709471) B1709471
theorem B1139871 : Blo 1136633 1139871 := bstep (se 1 (by rfl) ⟨854903, by rfl⟩ : syracuseStep 1139871 = 1709807) B1709807
theorem B1140071 : Blo 1136633 1140071 := bstep (se 1 (by rfl) ⟨855053, by rfl⟩ : syracuseStep 1140071 = 1710107) B1710107
theorem B1140159 : Blo 1136633 1140159 := bstep (se 1 (by rfl) ⟨855119, by rfl⟩ : syracuseStep 1140159 = 1710239) B1710239
theorem B6481403 : Blo 1136633 6481403 := bstep (se 1 (by rfl) ⟨4861052, by rfl⟩ : syracuseStep 6481403 = 9722105) B9722105
theorem B4318717 : Blo 1136633 4318717 := bstep (se 3 (by rfl) ⟨809759, by rfl⟩ : syracuseStep 4318717 = 1619519) B1619519
theorem B3237671 : Blo 1136633 3237671 := bstep (se 1 (by rfl) ⟨2428253, by rfl⟩ : syracuseStep 3237671 = 4856507) B4856507
theorem B3238127 : Blo 1136633 3238127 := bstep (se 1 (by rfl) ⟨2428595, by rfl⟩ : syracuseStep 3238127 = 4857191) B4857191
theorem B5761691 : Blo 1136633 5761691 := bstep (se 1 (by rfl) ⟨4321268, by rfl⟩ : syracuseStep 5761691 = 8642537) B8642537
theorem B4615015 : Blo 1136633 4615015 := bstep (se 1 (by rfl) ⟨3461261, by rfl⟩ : syracuseStep 4615015 = 6922523) B6922523
theorem B4618711 : Blo 1136633 4618711 := bstep (se 1 (by rfl) ⟨3464033, by rfl⟩ : syracuseStep 4618711 = 6928067) B6928067
theorem B2161151 : Blo 1136633 2161151 := bstep (se 1 (by rfl) ⟨1620863, by rfl⟩ : syracuseStep 2161151 = 3241727) B3241727
theorem B3243311 : Blo 1136633 3243311 := bstep (se 1 (by rfl) ⟨2432483, by rfl⟩ : syracuseStep 3243311 = 4864967) B4864967
theorem B3080287 : Blo 1136633 3080287 := bstep (se 1 (by rfl) ⟨2310215, by rfl⟩ : syracuseStep 3080287 = 4620431) B4620431
theorem B1704959 : Blo 1136633 1704959 := bstep (se 1 (by rfl) ⟨1278719, by rfl⟩ : syracuseStep 1704959 = 2557439) B2557439
theorem B5833819 : Blo 1136633 5833819 := bstep (se 1 (by rfl) ⟨4375364, by rfl⟩ : syracuseStep 5833819 = 8750729) B8750729
theorem B24937577 : Blo 1136633 24937577 := bstep (se 2 (by rfl) ⟨9351591, by rfl⟩ : syracuseStep 24937577 = 18703183) B18703183
theorem B2884967 : Blo 1136633 2884967 := bstep (se 1 (by rfl) ⟨2163725, by rfl⟩ : syracuseStep 2884967 = 4327451) B4327451
theorem B2557799 : Blo 1136633 2557799 := bstep (se 1 (by rfl) ⟨1918349, by rfl⟩ : syracuseStep 2557799 = 3836699) B3836699
theorem B1214875 : Blo 1136633 1214875 := bstep (se 1 (by rfl) ⟨911156, by rfl⟩ : syracuseStep 1214875 = 1822313) B1822313
theorem B1706495 : Blo 1136633 1706495 := bstep (se 1 (by rfl) ⟨1279871, by rfl⟩ : syracuseStep 1706495 = 2559743) B2559743
theorem B1280623 : Blo 1136633 1280623 := bstep (se 1 (by rfl) ⟨960467, by rfl⟩ : syracuseStep 1280623 = 1920935) B1920935
theorem B1707503 : Blo 1136633 1707503 := bstep (se 1 (by rfl) ⟨1280627, by rfl⟩ : syracuseStep 1707503 = 2561255) B2561255
theorem B2561183 : Blo 1136633 2561183 := bstep (se 1 (by rfl) ⟨1920887, by rfl⟩ : syracuseStep 2561183 = 3841775) B3841775
theorem B10949899 : Blo 1136633 10949899 := bstep (se 1 (by rfl) ⟨8212424, by rfl⟩ : syracuseStep 10949899 = 16424849) B16424849
theorem B4855535 : Blo 1136633 4855535 := bstep (se 1 (by rfl) ⟨3641651, by rfl⟩ : syracuseStep 4855535 = 7283303) B7283303
theorem B1710047 : Blo 1136633 1710047 := bstep (se 1 (by rfl) ⟨1282535, by rfl⟩ : syracuseStep 1710047 = 2565071) B2565071
theorem B1710527 : Blo 1136633 1710527 := bstep (se 1 (by rfl) ⟨1282895, by rfl⟩ : syracuseStep 1710527 = 2565791) B2565791
theorem B3841127 : Blo 1136633 3841127 := bstep (se 1 (by rfl) ⟨2880845, by rfl⟩ : syracuseStep 3841127 = 5761691) B5761691
theorem B2563307 : Blo 1136633 2563307 := bstep (se 1 (by rfl) ⟨1922480, by rfl⟩ : syracuseStep 2563307 = 3844961) B3844961
theorem B2432987 : Blo 1136633 2432987 := bstep (se 1 (by rfl) ⟨1824740, by rfl⟩ : syracuseStep 2432987 = 3649481) B3649481
theorem B1384447 : Blo 1136633 1384447 := bstep (se 1 (by rfl) ⟨1038335, by rfl⟩ : syracuseStep 1384447 = 2076671) B2076671
theorem B2565431 : Blo 1136633 2565431 := bstep (se 1 (by rfl) ⟨1924073, by rfl⟩ : syracuseStep 2565431 = 3848147) B3848147
theorem B2566313 : Blo 1136633 2566313 := bstep (se 2 (by rfl) ⟨962367, by rfl⟩ : syracuseStep 2566313 = 1924735) B1924735
theorem B2600873 : Blo 1136633 2600873 := bstep (se 2 (by rfl) ⟨975327, by rfl⟩ : syracuseStep 2600873 = 1950655) B1950655
theorem B2735315 : Blo 1136633 2735315 := bstep (se 1 (by rfl) ⟨2051486, by rfl⟩ : syracuseStep 2735315 = 4102973) B4102973
theorem B8633789 : Blo 1136633 8633789 := bstep (se 3 (by rfl) ⟨1618835, by rfl⟩ : syracuseStep 8633789 = 3237671) B3237671
theorem B24657695 : Blo 1136633 24657695 := bstep (se 1 (by rfl) ⟨18493271, by rfl⟩ : syracuseStep 24657695 = 36986543) B36986543
theorem B8634761 : Blo 1136633 8634761 := bstep (se 2 (by rfl) ⟨3238035, by rfl⟩ : syracuseStep 8634761 = 6476071) B6476071
theorem B18727703 : Blo 1136633 18727703 := bstep (se 1 (by rfl) ⟨14045777, by rfl⟩ : syracuseStep 18727703 = 28091555) B28091555
theorem B12961619 : Blo 1136633 12961619 := bstep (se 1 (by rfl) ⟨9721214, by rfl⟩ : syracuseStep 12961619 = 19442429) B19442429
theorem B12306491 : Blo 1136633 12306491 := bstep (se 1 (by rfl) ⟨9229868, by rfl⟩ : syracuseStep 12306491 = 18459737) B18459737
theorem B18469079 : Blo 1136633 18469079 := bstep (se 1 (by rfl) ⟨13851809, by rfl⟩ : syracuseStep 18469079 = 27703619) B27703619
theorem B252827351 : Blo 1136633 252827351 := bstep (se 1 (by rfl) ⟨189620513, by rfl⟩ : syracuseStep 252827351 = 379241027) B379241027
theorem B1137403 : Blo 1136633 1137403 := bstep (se 1 (by rfl) ⟨853052, by rfl⟩ : syracuseStep 1137403 = 1706105) B1706105
theorem B1137435 : Blo 1136633 1137435 := bstep (se 1 (by rfl) ⟨853076, by rfl⟩ : syracuseStep 1137435 = 1706153) B1706153
theorem B1137647 : Blo 1136633 1137647 := bstep (se 1 (by rfl) ⟨853235, by rfl⟩ : syracuseStep 1137647 = 1706471) B1706471
theorem B5758289 : Blo 1136633 5758289 := bstep (se 2 (by rfl) ⟨2159358, by rfl⟩ : syracuseStep 5758289 = 4318717) B4318717
theorem B1138079 : Blo 1136633 1138079 := bstep (se 1 (by rfl) ⟨853559, by rfl⟩ : syracuseStep 1138079 = 1707119) B1707119
theorem B12967451 : Blo 1136633 12967451 := bstep (se 1 (by rfl) ⟨9725588, by rfl⟩ : syracuseStep 12967451 = 19451177) B19451177
theorem B1138687 : Blo 1136633 1138687 := bstep (se 1 (by rfl) ⟨854015, by rfl⟩ : syracuseStep 1138687 = 1708031) B1708031
theorem B10379839 : Blo 1136633 10379839 := bstep (se 1 (by rfl) ⟨7784879, by rfl⟩ : syracuseStep 10379839 = 15569759) B15569759
theorem B6153353 : Blo 1136633 6153353 := bstep (se 2 (by rfl) ⟨2307507, by rfl⟩ : syracuseStep 6153353 = 4615015) B4615015
theorem B1139967 : Blo 1136633 1139967 := bstep (se 1 (by rfl) ⟨854975, by rfl⟩ : syracuseStep 1139967 = 1709951) B1709951
theorem B1140223 : Blo 1136633 1140223 := bstep (se 1 (by rfl) ⟨855167, by rfl⟩ : syracuseStep 1140223 = 1710335) B1710335
theorem B19424933 : Blo 1136633 19424933 := bstep (se 4 (by rfl) ⟨1821087, by rfl⟩ : syracuseStep 19424933 = 3642175) B3642175
theorem B159738439 : Blo 1136633 159738439 := bstep (se 1 (by rfl) ⟨119803829, by rfl⟩ : syracuseStep 159738439 = 239607659) B239607659
theorem B9727229 : Blo 1136633 9727229 := bstep (se 3 (by rfl) ⟨1823855, by rfl⟩ : syracuseStep 9727229 = 3647711) B3647711
theorem B4320935 : Blo 1136633 4320935 := bstep (se 1 (by rfl) ⟨3240701, by rfl⟩ : syracuseStep 4320935 = 6481403) B6481403
theorem B71987291 : Blo 1136633 71987291 := bstep (se 1 (by rfl) ⟨53990468, by rfl⟩ : syracuseStep 71987291 = 107980937) B107980937
theorem B2158751 : Blo 1136633 2158751 := bstep (se 1 (by rfl) ⟨1619063, by rfl⟩ : syracuseStep 2158751 = 3238127) B3238127
theorem B6158281 : Blo 1136633 6158281 := bstep (se 2 (by rfl) ⟨2309355, by rfl⟩ : syracuseStep 6158281 = 4618711) B4618711
theorem B1440767 : Blo 1136633 1440767 := bstep (se 1 (by rfl) ⟨1080575, by rfl⟩ : syracuseStep 1440767 = 2161151) B2161151
theorem B2162207 : Blo 1136633 2162207 := bstep (se 1 (by rfl) ⟨1621655, by rfl⟩ : syracuseStep 2162207 = 3243311) B3243311
theorem B12485135 : Blo 1136633 12485135 := bstep (se 1 (by rfl) ⟨9363851, by rfl⟩ : syracuseStep 12485135 = 18727703) B18727703
theorem B1705199 : Blo 1136633 1705199 := bstep (se 1 (by rfl) ⟨1278899, by rfl⟩ : syracuseStep 1705199 = 2557799) B2557799
theorem B1707455 : Blo 1136633 1707455 := bstep (se 1 (by rfl) ⟨1280591, by rfl⟩ : syracuseStep 1707455 = 2561183) B2561183
theorem B1707497 : Blo 1136633 1707497 := bstep (se 2 (by rfl) ⟨640311, by rfl⟩ : syracuseStep 1707497 = 1280623) B1280623
theorem B2560751 : Blo 1136633 2560751 := bstep (se 1 (by rfl) ⟨1920563, by rfl⟩ : syracuseStep 2560751 = 3841127) B3841127
theorem B1708871 : Blo 1136633 1708871 := bstep (se 1 (by rfl) ⟨1281653, by rfl⟩ : syracuseStep 1708871 = 2563307) B2563307
theorem B3838859 : Blo 1136633 3838859 := bstep (se 1 (by rfl) ⟨2879144, by rfl⟩ : syracuseStep 3838859 = 5758289) B5758289
theorem B4102235 : Blo 1136633 4102235 := bstep (se 1 (by rfl) ⟨3076676, by rfl⟩ : syracuseStep 4102235 = 6153353) B6153353
theorem B1710287 : Blo 1136633 1710287 := bstep (se 1 (by rfl) ⟨1282715, by rfl⟩ : syracuseStep 1710287 = 2565431) B2565431
theorem B12949955 : Blo 1136633 12949955 := bstep (se 1 (by rfl) ⟨9712466, by rfl⟩ : syracuseStep 12949955 = 19424933) B19424933
theorem B1710875 : Blo 1136633 1710875 := bstep (se 1 (by rfl) ⟨1283156, by rfl⟩ : syracuseStep 1710875 = 2566313) B2566313
theorem B3842045 : Blo 1136633 3842045 := bstep (se 3 (by rfl) ⟨720383, by rfl⟩ : syracuseStep 3842045 = 1440767) B1440767
theorem B1845929 : Blo 1136633 1845929 := bstep (se 2 (by rfl) ⟨692223, by rfl⟩ : syracuseStep 1845929 = 1384447) B1384447
theorem B16428197 : Blo 1136633 16428197 := bstep (se 4 (by rfl) ⟨1540143, by rfl⟩ : syracuseStep 16428197 = 3080287) B3080287
theorem B16625051 : Blo 1136633 16625051 := bstep (se 1 (by rfl) ⟨12468788, by rfl⟩ : syracuseStep 16625051 = 24937577) B24937577
theorem B13839785 : Blo 1136633 13839785 := bstep (se 2 (by rfl) ⟨5189919, by rfl⟩ : syracuseStep 13839785 = 10379839) B10379839
theorem B8204327 : Blo 1136633 8204327 := bstep (se 1 (by rfl) ⟨6153245, by rfl⟩ : syracuseStep 8204327 = 12306491) B12306491
theorem B7778425 : Blo 1136633 7778425 := bstep (se 2 (by rfl) ⟨2916909, by rfl⟩ : syracuseStep 7778425 = 5833819) B5833819
theorem B1619833 : Blo 1136633 1619833 := bstep (se 2 (by rfl) ⟨607437, by rfl⟩ : syracuseStep 1619833 = 1214875) B1214875
theorem B1621991 : Blo 1136633 1621991 := bstep (se 1 (by rfl) ⟨1216493, by rfl⟩ : syracuseStep 1621991 = 2432987) B2432987
theorem B14599865 : Blo 1136633 14599865 := bstep (se 2 (by rfl) ⟨5474949, by rfl⟩ : syracuseStep 14599865 = 10949899) B10949899
theorem B8211041 : Blo 1136633 8211041 := bstep (se 2 (by rfl) ⟨3079140, by rfl⟩ : syracuseStep 8211041 = 6158281) B6158281
theorem B47991527 : Blo 1136633 47991527 := bstep (se 1 (by rfl) ⟨35993645, by rfl⟩ : syracuseStep 47991527 = 71987291) B71987291
theorem B1823543 : Blo 1136633 1823543 := bstep (se 1 (by rfl) ⟨1367657, by rfl⟩ : syracuseStep 1823543 = 2735315) B2735315
theorem B5755859 : Blo 1136633 5755859 := bstep (se 1 (by rfl) ⟨4316894, by rfl⟩ : syracuseStep 5755859 = 8633789) B8633789
theorem B16438463 : Blo 1136633 16438463 := bstep (se 1 (by rfl) ⟨12328847, by rfl⟩ : syracuseStep 16438463 = 24657695) B24657695
theorem B5756507 : Blo 1136633 5756507 := bstep (se 1 (by rfl) ⟨4317380, by rfl⟩ : syracuseStep 5756507 = 8634761) B8634761
theorem B5756669 : Blo 1136633 5756669 := bstep (se 3 (by rfl) ⟨1079375, by rfl⟩ : syracuseStep 5756669 = 2158751) B2158751
theorem B1136639 : Blo 1136633 1136639 := bstep (se 1 (by rfl) ⟨852479, by rfl⟩ : syracuseStep 1136639 = 1704959) B1704959
theorem B1923311 : Blo 1136633 1923311 := bstep (se 1 (by rfl) ⟨1442483, by rfl⟩ : syracuseStep 1923311 = 2884967) B2884967
theorem B8641079 : Blo 1136633 8641079 := bstep (se 1 (by rfl) ⟨6480809, by rfl⟩ : syracuseStep 8641079 = 12961619) B12961619
theorem B1137663 : Blo 1136633 1137663 := bstep (se 1 (by rfl) ⟨853247, by rfl⟩ : syracuseStep 1137663 = 1706495) B1706495
theorem B1138335 : Blo 1136633 1138335 := bstep (se 1 (by rfl) ⟨853751, by rfl⟩ : syracuseStep 1138335 = 1707503) B1707503
theorem B12312719 : Blo 1136633 12312719 := bstep (se 1 (by rfl) ⟨9234539, by rfl⟩ : syracuseStep 12312719 = 18469079) B18469079
theorem B212984585 : Blo 1136633 212984585 := bstep (se 2 (by rfl) ⟨79869219, by rfl⟩ : syracuseStep 212984585 = 159738439) B159738439
theorem B168551567 : Blo 1136633 168551567 := bstep (se 1 (by rfl) ⟨126413675, by rfl⟩ : syracuseStep 168551567 = 252827351) B252827351
theorem B3237023 : Blo 1136633 3237023 := bstep (se 1 (by rfl) ⟨2427767, by rfl⟩ : syracuseStep 3237023 = 4855535) B4855535
theorem B1140031 : Blo 1136633 1140031 := bstep (se 1 (by rfl) ⟨855023, by rfl⟩ : syracuseStep 1140031 = 1710047) B1710047
theorem B1140351 : Blo 1136633 1140351 := bstep (se 1 (by rfl) ⟨855263, by rfl⟩ : syracuseStep 1140351 = 1710527) B1710527
theorem B8644967 : Blo 1136633 8644967 := bstep (se 1 (by rfl) ⟨6483725, by rfl⟩ : syracuseStep 8644967 = 12967451) B12967451
theorem B6484819 : Blo 1136633 6484819 := bstep (se 1 (by rfl) ⟨4863614, by rfl⟩ : syracuseStep 6484819 = 9727229) B9727229
theorem B2880623 : Blo 1136633 2880623 := bstep (se 1 (by rfl) ⟨2160467, by rfl⟩ : syracuseStep 2880623 = 4320935) B4320935
theorem B1733915 : Blo 1136633 1733915 := bstep (se 1 (by rfl) ⟨1300436, by rfl⟩ : syracuseStep 1733915 = 2600873) B2600873
theorem B1441471 : Blo 1136633 1441471 := bstep (se 1 (by rfl) ⟨1081103, by rfl⟩ : syracuseStep 1441471 = 2162207) B2162207
theorem B9733243 : Blo 1136633 9733243 := bstep (se 1 (by rfl) ⟨7299932, by rfl⟩ : syracuseStep 9733243 = 14599865) B14599865
theorem B33293693 : Blo 1136633 33293693 := bstep (se 3 (by rfl) ⟨6242567, by rfl⟩ : syracuseStep 33293693 = 12485135) B12485135
theorem B5474027 : Blo 1136633 5474027 := bstep (se 1 (by rfl) ⟨4105520, by rfl⟩ : syracuseStep 5474027 = 8211041) B8211041
theorem B1707167 : Blo 1136633 1707167 := bstep (se 1 (by rfl) ⟨1280375, by rfl⟩ : syracuseStep 1707167 = 2560751) B2560751
theorem B1215695 : Blo 1136633 1215695 := bstep (se 1 (by rfl) ⟨911771, by rfl⟩ : syracuseStep 1215695 = 1823543) B1823543
theorem B2559239 : Blo 1136633 2559239 := bstep (se 1 (by rfl) ⟨1919429, by rfl⟩ : syracuseStep 2559239 = 3838859) B3838859
theorem B3837239 : Blo 1136633 3837239 := bstep (se 1 (by rfl) ⟨2877929, by rfl⟩ : syracuseStep 3837239 = 5755859) B5755859
theorem B3837671 : Blo 1136633 3837671 := bstep (se 1 (by rfl) ⟨2878253, by rfl⟩ : syracuseStep 3837671 = 5756507) B5756507
theorem B3837779 : Blo 1136633 3837779 := bstep (se 1 (by rfl) ⟨2878334, by rfl⟩ : syracuseStep 3837779 = 5756669) B5756669
theorem B1282207 : Blo 1136633 1282207 := bstep (se 1 (by rfl) ⟨961655, by rfl⟩ : syracuseStep 1282207 = 1923311) B1923311
theorem B2561363 : Blo 1136633 2561363 := bstep (se 1 (by rfl) ⟨1921022, by rfl⟩ : syracuseStep 2561363 = 3842045) B3842045
theorem B141989723 : Blo 1136633 141989723 := bstep (se 1 (by rfl) ⟨106492292, by rfl⟩ : syracuseStep 141989723 = 212984585) B212984585
theorem B112367711 : Blo 1136633 112367711 := bstep (se 1 (by rfl) ⟨84275783, by rfl⟩ : syracuseStep 112367711 = 168551567) B168551567
theorem B4922477 : Blo 1136633 4922477 := bstep (se 3 (by rfl) ⟨922964, by rfl⟩ : syracuseStep 4922477 = 1845929) B1845929
theorem B10952131 : Blo 1136633 10952131 := bstep (se 1 (by rfl) ⟨8214098, by rfl⟩ : syracuseStep 10952131 = 16428197) B16428197
theorem B11083367 : Blo 1136633 11083367 := bstep (se 1 (by rfl) ⟨8312525, by rfl⟩ : syracuseStep 11083367 = 16625051) B16625051
theorem B1155943 : Blo 1136633 1155943 := bstep (se 1 (by rfl) ⟨866957, by rfl⟩ : syracuseStep 1155943 = 1733915) B1733915
theorem B31994351 : Blo 1136633 31994351 := bstep (se 1 (by rfl) ⟨23995763, by rfl⟩ : syracuseStep 31994351 = 47991527) B47991527
theorem B10958975 : Blo 1136633 10958975 := bstep (se 1 (by rfl) ⟨8219231, by rfl⟩ : syracuseStep 10958975 = 16438463) B16438463
theorem B2734823 : Blo 1136633 2734823 := bstep (se 1 (by rfl) ⟨2051117, by rfl⟩ : syracuseStep 2734823 = 4102235) B4102235
theorem B8633303 : Blo 1136633 8633303 := bstep (se 1 (by rfl) ⟨6474977, by rfl⟩ : syracuseStep 8633303 = 12949955) B12949955
theorem B8208479 : Blo 1136633 8208479 := bstep (se 1 (by rfl) ⟨6156359, by rfl⟩ : syracuseStep 8208479 = 12312719) B12312719
theorem B10371233 : Blo 1136633 10371233 := bstep (se 2 (by rfl) ⟨3889212, by rfl⟩ : syracuseStep 10371233 = 7778425) B7778425
theorem B9226523 : Blo 1136633 9226523 := bstep (se 1 (by rfl) ⟨6919892, by rfl⟩ : syracuseStep 9226523 = 13839785) B13839785
theorem B1920415 : Blo 1136633 1920415 := bstep (se 1 (by rfl) ⟨1440311, by rfl⟩ : syracuseStep 1920415 = 2880623) B2880623
theorem B1921961 : Blo 1136633 1921961 := bstep (se 2 (by rfl) ⟨720735, by rfl⟩ : syracuseStep 1921961 = 1441471) B1441471
theorem B1136799 : Blo 1136633 1136799 := bstep (se 1 (by rfl) ⟨852599, by rfl⟩ : syracuseStep 1136799 = 1705199) B1705199
theorem B1138303 : Blo 1136633 1138303 := bstep (se 1 (by rfl) ⟨853727, by rfl⟩ : syracuseStep 1138303 = 1707455) B1707455
theorem B1138331 : Blo 1136633 1138331 := bstep (se 1 (by rfl) ⟨853748, by rfl⟩ : syracuseStep 1138331 = 1707497) B1707497
theorem B1139247 : Blo 1136633 1139247 := bstep (se 1 (by rfl) ⟨854435, by rfl⟩ : syracuseStep 1139247 = 1708871) B1708871
theorem B1140191 : Blo 1136633 1140191 := bstep (se 1 (by rfl) ⟨855143, by rfl⟩ : syracuseStep 1140191 = 1710287) B1710287
theorem B5760719 : Blo 1136633 5760719 := bstep (se 1 (by rfl) ⟨4320539, by rfl⟩ : syracuseStep 5760719 = 8641079) B8641079
theorem B1140583 : Blo 1136633 1140583 := bstep (se 1 (by rfl) ⟨855437, by rfl⟩ : syracuseStep 1140583 = 1710875) B1710875
theorem B2158015 : Blo 1136633 2158015 := bstep (se 1 (by rfl) ⟨1618511, by rfl⟩ : syracuseStep 2158015 = 3237023) B3237023
theorem B8646425 : Blo 1136633 8646425 := bstep (se 2 (by rfl) ⟨3242409, by rfl⟩ : syracuseStep 8646425 = 6484819) B6484819
theorem B5763311 : Blo 1136633 5763311 := bstep (se 1 (by rfl) ⟨4322483, by rfl⟩ : syracuseStep 5763311 = 8644967) B8644967
theorem B2159777 : Blo 1136633 2159777 := bstep (se 2 (by rfl) ⟨809916, by rfl⟩ : syracuseStep 2159777 = 1619833) B1619833
theorem B5469551 : Blo 1136633 5469551 := bstep (se 1 (by rfl) ⟨4102163, by rfl⟩ : syracuseStep 5469551 = 8204327) B8204327
theorem B4325309 : Blo 1136633 4325309 := bstep (se 3 (by rfl) ⟨810995, by rfl⟩ : syracuseStep 4325309 = 1621991) B1621991
theorem B5472319 : Blo 1136633 5472319 := bstep (se 1 (by rfl) ⟨4104239, by rfl⟩ : syracuseStep 5472319 = 8208479) B8208479
theorem B6914155 : Blo 1136633 6914155 := bstep (se 1 (by rfl) ⟨5185616, by rfl⟩ : syracuseStep 6914155 = 10371233) B10371233
theorem B1541257 : Blo 1136633 1541257 := bstep (se 2 (by rfl) ⟨577971, by rfl⟩ : syracuseStep 1541257 = 1155943) B1155943
theorem B12977657 : Blo 1136633 12977657 := bstep (se 2 (by rfl) ⟨4866621, by rfl⟩ : syracuseStep 12977657 = 9733243) B9733243
theorem B1706159 : Blo 1136633 1706159 := bstep (se 1 (by rfl) ⟨1279619, by rfl⟩ : syracuseStep 1706159 = 2559239) B2559239
theorem B2558159 : Blo 1136633 2558159 := bstep (se 1 (by rfl) ⟨1918619, by rfl⟩ : syracuseStep 2558159 = 3837239) B3837239
theorem B2558447 : Blo 1136633 2558447 := bstep (se 1 (by rfl) ⟨1918835, by rfl⟩ : syracuseStep 2558447 = 3837671) B3837671
theorem B2558519 : Blo 1136633 2558519 := bstep (se 1 (by rfl) ⟨1918889, by rfl⟩ : syracuseStep 2558519 = 3837779) B3837779
theorem B1281307 : Blo 1136633 1281307 := bstep (se 1 (by rfl) ⟨960980, by rfl⟩ : syracuseStep 1281307 = 1921961) B1921961
theorem B1707575 : Blo 1136633 1707575 := bstep (se 1 (by rfl) ⟨1280681, by rfl⟩ : syracuseStep 1707575 = 2561363) B2561363
theorem B74911807 : Blo 1136633 74911807 := bstep (se 1 (by rfl) ⟨56183855, by rfl⟩ : syracuseStep 74911807 = 112367711) B112367711
theorem B2560553 : Blo 1136633 2560553 := bstep (se 2 (by rfl) ⟨960207, by rfl⟩ : syracuseStep 2560553 = 1920415) B1920415
theorem B3281651 : Blo 1136633 3281651 := bstep (se 1 (by rfl) ⟨2461238, by rfl⟩ : syracuseStep 3281651 = 4922477) B4922477
theorem B1709609 : Blo 1136633 1709609 := bstep (se 2 (by rfl) ⟨641103, by rfl⟩ : syracuseStep 1709609 = 1282207) B1282207
theorem B3840479 : Blo 1136633 3840479 := bstep (se 1 (by rfl) ⟨2880359, by rfl⟩ : syracuseStep 3840479 = 5760719) B5760719
theorem B3842207 : Blo 1136633 3842207 := bstep (se 1 (by rfl) ⟨2881655, by rfl⟩ : syracuseStep 3842207 = 5763311) B5763311
theorem B3646367 : Blo 1136633 3646367 := bstep (se 1 (by rfl) ⟨2734775, by rfl⟩ : syracuseStep 3646367 = 5469551) B5469551
theorem B22195795 : Blo 1136633 22195795 := bstep (se 1 (by rfl) ⟨16646846, by rfl⟩ : syracuseStep 22195795 = 33293693) B33293693
theorem B14597405 : Blo 1136633 14597405 := bstep (se 3 (by rfl) ⟨2737013, by rfl⟩ : syracuseStep 14597405 = 5474027) B5474027
theorem B7388911 : Blo 1136633 7388911 := bstep (se 1 (by rfl) ⟨5541683, by rfl⟩ : syracuseStep 7388911 = 11083367) B11083367
theorem B7292861 : Blo 1136633 7292861 := bstep (se 3 (by rfl) ⟨1367411, by rfl⟩ : syracuseStep 7292861 = 2734823) B2734823
theorem B14602841 : Blo 1136633 14602841 := bstep (se 2 (by rfl) ⟨5476065, by rfl⟩ : syracuseStep 14602841 = 10952131) B10952131
theorem B5755535 : Blo 1136633 5755535 := bstep (se 1 (by rfl) ⟨4316651, by rfl⟩ : syracuseStep 5755535 = 8633303) B8633303
theorem B6151015 : Blo 1136633 6151015 := bstep (se 1 (by rfl) ⟨4613261, by rfl⟩ : syracuseStep 6151015 = 9226523) B9226523
theorem B1138111 : Blo 1136633 1138111 := bstep (se 1 (by rfl) ⟨853583, by rfl⟩ : syracuseStep 1138111 = 1707167) B1707167
theorem B94659815 : Blo 1136633 94659815 := bstep (se 1 (by rfl) ⟨70994861, by rfl⟩ : syracuseStep 94659815 = 141989723) B141989723
theorem B2877353 : Blo 1136633 2877353 := bstep (se 2 (by rfl) ⟨1079007, by rfl⟩ : syracuseStep 2877353 = 2158015) B2158015
theorem B5764283 : Blo 1136633 5764283 := bstep (se 1 (by rfl) ⟨4323212, by rfl⟩ : syracuseStep 5764283 = 8646425) B8646425
theorem B21329567 : Blo 1136633 21329567 := bstep (se 1 (by rfl) ⟨15997175, by rfl⟩ : syracuseStep 21329567 = 31994351) B31994351
theorem B3241853 : Blo 1136633 3241853 := bstep (se 3 (by rfl) ⟨607847, by rfl⟩ : syracuseStep 3241853 = 1215695) B1215695
theorem B1439851 : Blo 1136633 1439851 := bstep (se 1 (by rfl) ⟨1079888, by rfl⟩ : syracuseStep 1439851 = 2159777) B2159777
theorem B7305983 : Blo 1136633 7305983 := bstep (se 1 (by rfl) ⟨5479487, by rfl⟩ : syracuseStep 7305983 = 10958975) B10958975
theorem B2883539 : Blo 1136633 2883539 := bstep (se 1 (by rfl) ⟨2162654, by rfl⟩ : syracuseStep 2883539 = 4325309) B4325309
theorem B8651771 : Blo 1136633 8651771 := bstep (se 1 (by rfl) ⟨6488828, by rfl⟩ : syracuseStep 8651771 = 12977657) B12977657
theorem B1705439 : Blo 1136633 1705439 := bstep (se 1 (by rfl) ⟨1279079, by rfl⟩ : syracuseStep 1705439 = 2558159) B2558159
theorem B1705631 : Blo 1136633 1705631 := bstep (se 1 (by rfl) ⟨1279223, by rfl⟩ : syracuseStep 1705631 = 2558447) B2558447
theorem B1705679 : Blo 1136633 1705679 := bstep (se 1 (by rfl) ⟨1279259, by rfl⟩ : syracuseStep 1705679 = 2558519) B2558519
theorem B1707035 : Blo 1136633 1707035 := bstep (se 1 (by rfl) ⟨1280276, by rfl⟩ : syracuseStep 1707035 = 2560553) B2560553
theorem B9735227 : Blo 1136633 9735227 := bstep (se 1 (by rfl) ⟨7301420, by rfl⟩ : syracuseStep 9735227 = 14602841) B14602841
theorem B3837023 : Blo 1136633 3837023 := bstep (se 1 (by rfl) ⟨2877767, by rfl⟩ : syracuseStep 3837023 = 5755535) B5755535
theorem B2560319 : Blo 1136633 2560319 := bstep (se 1 (by rfl) ⟨1920239, by rfl⟩ : syracuseStep 2560319 = 3840479) B3840479
theorem B1708409 : Blo 1136633 1708409 := bstep (se 2 (by rfl) ⟨640653, by rfl⟩ : syracuseStep 1708409 = 1281307) B1281307
theorem B29594393 : Blo 1136633 29594393 := bstep (se 2 (by rfl) ⟨11097897, by rfl⟩ : syracuseStep 29594393 = 22195795) B22195795
theorem B99882409 : Blo 1136633 99882409 := bstep (se 2 (by rfl) ⟨37455903, by rfl⟩ : syracuseStep 99882409 = 74911807) B74911807
theorem B2561471 : Blo 1136633 2561471 := bstep (se 1 (by rfl) ⟨1921103, by rfl⟩ : syracuseStep 2561471 = 3842207) B3842207
theorem B2430911 : Blo 1136633 2430911 := bstep (se 1 (by rfl) ⟨1823183, by rfl⟩ : syracuseStep 2430911 = 3646367) B3646367
theorem B3842855 : Blo 1136633 3842855 := bstep (se 1 (by rfl) ⟨2882141, by rfl⟩ : syracuseStep 3842855 = 5764283) B5764283
theorem B8201353 : Blo 1136633 8201353 := bstep (se 2 (by rfl) ⟨3075507, by rfl⟩ : syracuseStep 8201353 = 6151015) B6151015
theorem B9218873 : Blo 1136633 9218873 := bstep (se 2 (by rfl) ⟨3457077, by rfl⟩ : syracuseStep 9218873 = 6914155) B6914155
theorem B4861907 : Blo 1136633 4861907 := bstep (se 1 (by rfl) ⟨3646430, by rfl⟩ : syracuseStep 4861907 = 7292861) B7292861
theorem B1918235 : Blo 1136633 1918235 := bstep (se 1 (by rfl) ⟨1438676, by rfl⟩ : syracuseStep 1918235 = 2877353) B2877353
theorem B1919801 : Blo 1136633 1919801 := bstep (se 2 (by rfl) ⟨719925, by rfl⟩ : syracuseStep 1919801 = 1439851) B1439851
theorem B4870655 : Blo 1136633 4870655 := bstep (se 1 (by rfl) ⟨3652991, by rfl⟩ : syracuseStep 4870655 = 7305983) B7305983
theorem B9851881 : Blo 1136633 9851881 := bstep (se 2 (by rfl) ⟨3694455, by rfl⟩ : syracuseStep 9851881 = 7388911) B7388911
theorem B1922359 : Blo 1136633 1922359 := bstep (se 1 (by rfl) ⟨1441769, by rfl⟩ : syracuseStep 1922359 = 2883539) B2883539
theorem B7296425 : Blo 1136633 7296425 := bstep (se 2 (by rfl) ⟨2736159, by rfl⟩ : syracuseStep 7296425 = 5472319) B5472319
theorem B1137439 : Blo 1136633 1137439 := bstep (se 1 (by rfl) ⟨853079, by rfl⟩ : syracuseStep 1137439 = 1706159) B1706159
theorem B1138383 : Blo 1136633 1138383 := bstep (se 1 (by rfl) ⟨853787, by rfl⟩ : syracuseStep 1138383 = 1707575) B1707575
theorem B2187767 : Blo 1136633 2187767 := bstep (se 1 (by rfl) ⟨1640825, by rfl⟩ : syracuseStep 2187767 = 3281651) B3281651
theorem B1139739 : Blo 1136633 1139739 := bstep (se 1 (by rfl) ⟨854804, by rfl⟩ : syracuseStep 1139739 = 1709609) B1709609
theorem B8220037 : Blo 1136633 8220037 := bstep (se 4 (by rfl) ⟨770628, by rfl⟩ : syracuseStep 8220037 = 1541257) B1541257
theorem B63106543 : Blo 1136633 63106543 := bstep (se 1 (by rfl) ⟨47329907, by rfl⟩ : syracuseStep 63106543 = 94659815) B94659815
theorem B14219711 : Blo 1136633 14219711 := bstep (se 1 (by rfl) ⟨10664783, by rfl⟩ : syracuseStep 14219711 = 21329567) B21329567
theorem B2161235 : Blo 1136633 2161235 := bstep (se 1 (by rfl) ⟨1620926, by rfl⟩ : syracuseStep 2161235 = 3241853) B3241853
theorem B9731603 : Blo 1136633 9731603 := bstep (se 1 (by rfl) ⟨7298702, by rfl⟩ : syracuseStep 9731603 = 14597405) B14597405
theorem B5767847 : Blo 1136633 5767847 := bstep (se 1 (by rfl) ⟨4325885, by rfl⟩ : syracuseStep 5767847 = 8651771) B8651771
theorem B1278823 : Blo 1136633 1278823 := bstep (se 1 (by rfl) ⟨959117, by rfl⟩ : syracuseStep 1278823 = 1918235) B1918235
theorem B5834045 : Blo 1136633 5834045 := bstep (se 3 (by rfl) ⟨1093883, by rfl⟩ : syracuseStep 5834045 = 2187767) B2187767
theorem B1279867 : Blo 1136633 1279867 := bstep (se 1 (by rfl) ⟨959900, by rfl⟩ : syracuseStep 1279867 = 1919801) B1919801
theorem B6490151 : Blo 1136633 6490151 := bstep (se 1 (by rfl) ⟨4867613, by rfl⟩ : syracuseStep 6490151 = 9735227) B9735227
theorem B2558015 : Blo 1136633 2558015 := bstep (se 1 (by rfl) ⟨1918511, by rfl⟩ : syracuseStep 2558015 = 3837023) B3837023
theorem B1706879 : Blo 1136633 1706879 := bstep (se 1 (by rfl) ⟨1280159, by rfl⟩ : syracuseStep 1706879 = 2560319) B2560319
theorem B3247103 : Blo 1136633 3247103 := bstep (se 1 (by rfl) ⟨2435327, by rfl⟩ : syracuseStep 3247103 = 4870655) B4870655
theorem B19729595 : Blo 1136633 19729595 := bstep (se 1 (by rfl) ⟨14797196, by rfl⟩ : syracuseStep 19729595 = 29594393) B29594393
theorem B1707647 : Blo 1136633 1707647 := bstep (se 1 (by rfl) ⟨1280735, by rfl⟩ : syracuseStep 1707647 = 2561471) B2561471
theorem B2561903 : Blo 1136633 2561903 := bstep (se 1 (by rfl) ⟨1921427, by rfl⟩ : syracuseStep 2561903 = 3842855) B3842855
theorem B2563145 : Blo 1136633 2563145 := bstep (se 2 (by rfl) ⟨961179, by rfl⟩ : syracuseStep 2563145 = 1922359) B1922359
theorem B133176545 : Blo 1136633 133176545 := bstep (se 2 (by rfl) ⟨49941204, by rfl⟩ : syracuseStep 133176545 = 99882409) B99882409
theorem B336568229 : Blo 1136633 336568229 := bstep (se 4 (by rfl) ⟨31553271, by rfl⟩ : syracuseStep 336568229 = 63106543) B63106543
theorem B9479807 : Blo 1136633 9479807 := bstep (se 1 (by rfl) ⟨7109855, by rfl⟩ : syracuseStep 9479807 = 14219711) B14219711
theorem B4864283 : Blo 1136633 4864283 := bstep (se 1 (by rfl) ⟨3648212, by rfl⟩ : syracuseStep 4864283 = 7296425) B7296425
theorem B10960049 : Blo 1136633 10960049 := bstep (se 2 (by rfl) ⟨4110018, by rfl⟩ : syracuseStep 10960049 = 8220037) B8220037
theorem B6145915 : Blo 1136633 6145915 := bstep (se 1 (by rfl) ⟨4609436, by rfl⟩ : syracuseStep 6145915 = 9218873) B9218873
theorem B1136959 : Blo 1136633 1136959 := bstep (se 1 (by rfl) ⟨852719, by rfl⟩ : syracuseStep 1136959 = 1705439) B1705439
theorem B1137087 : Blo 1136633 1137087 := bstep (se 1 (by rfl) ⟨852815, by rfl⟩ : syracuseStep 1137087 = 1705631) B1705631
theorem B1137119 : Blo 1136633 1137119 := bstep (se 1 (by rfl) ⟨852839, by rfl⟩ : syracuseStep 1137119 = 1705679) B1705679
theorem B10935137 : Blo 1136633 10935137 := bstep (se 2 (by rfl) ⟨4100676, by rfl⟩ : syracuseStep 10935137 = 8201353) B8201353
theorem B1138023 : Blo 1136633 1138023 := bstep (se 1 (by rfl) ⟨853517, by rfl⟩ : syracuseStep 1138023 = 1707035) B1707035
theorem B1138939 : Blo 1136633 1138939 := bstep (se 1 (by rfl) ⟨854204, by rfl⟩ : syracuseStep 1138939 = 1708409) B1708409
theorem B6482429 : Blo 1136633 6482429 := bstep (se 3 (by rfl) ⟨1215455, by rfl⟩ : syracuseStep 6482429 = 2430911) B2430911
theorem B13135841 : Blo 1136633 13135841 := bstep (se 2 (by rfl) ⟨4925940, by rfl⟩ : syracuseStep 13135841 = 9851881) B9851881
theorem B3241271 : Blo 1136633 3241271 := bstep (se 1 (by rfl) ⟨2430953, by rfl⟩ : syracuseStep 3241271 = 4861907) B4861907
theorem B1440823 : Blo 1136633 1440823 := bstep (se 1 (by rfl) ⟨1080617, by rfl⟩ : syracuseStep 1440823 = 2161235) B2161235
theorem B6487735 : Blo 1136633 6487735 := bstep (se 1 (by rfl) ⟨4865801, by rfl⟩ : syracuseStep 6487735 = 9731603) B9731603
theorem B1705097 : Blo 1136633 1705097 := bstep (se 2 (by rfl) ⟨639411, by rfl⟩ : syracuseStep 1705097 = 1278823) B1278823
theorem B4326767 : Blo 1136633 4326767 := bstep (se 1 (by rfl) ⟨3245075, by rfl⟩ : syracuseStep 4326767 = 6490151) B6490151
theorem B1705343 : Blo 1136633 1705343 := bstep (se 1 (by rfl) ⟨1279007, by rfl⟩ : syracuseStep 1705343 = 2558015) B2558015
theorem B2164735 : Blo 1136633 2164735 := bstep (se 1 (by rfl) ⟨1623551, by rfl⟩ : syracuseStep 2164735 = 3247103) B3247103
theorem B8194553 : Blo 1136633 8194553 := bstep (se 2 (by rfl) ⟨3072957, by rfl⟩ : syracuseStep 8194553 = 6145915) B6145915
theorem B1706489 : Blo 1136633 1706489 := bstep (se 2 (by rfl) ⟨639933, by rfl⟩ : syracuseStep 1706489 = 1279867) B1279867
theorem B1707935 : Blo 1136633 1707935 := bstep (se 1 (by rfl) ⟨1280951, by rfl⟩ : syracuseStep 1707935 = 2561903) B2561903
theorem B1708763 : Blo 1136633 1708763 := bstep (se 1 (by rfl) ⟨1281572, by rfl⟩ : syracuseStep 1708763 = 2563145) B2563145
theorem B8757227 : Blo 1136633 8757227 := bstep (se 1 (by rfl) ⟨6567920, by rfl⟩ : syracuseStep 8757227 = 13135841) B13135841
theorem B3845231 : Blo 1136633 3845231 := bstep (se 1 (by rfl) ⟨2883923, by rfl⟩ : syracuseStep 3845231 = 5767847) B5767847
theorem B13153063 : Blo 1136633 13153063 := bstep (se 1 (by rfl) ⟨9864797, by rfl⟩ : syracuseStep 13153063 = 19729595) B19729595
theorem B7290091 : Blo 1136633 7290091 := bstep (se 1 (by rfl) ⟨5467568, by rfl⟩ : syracuseStep 7290091 = 10935137) B10935137
theorem B88784363 : Blo 1136633 88784363 := bstep (se 1 (by rfl) ⟨66588272, by rfl⟩ : syracuseStep 88784363 = 133176545) B133176545
theorem B224378819 : Blo 1136633 224378819 := bstep (se 1 (by rfl) ⟨168284114, by rfl⟩ : syracuseStep 224378819 = 336568229) B336568229
theorem B1921097 : Blo 1136633 1921097 := bstep (se 2 (by rfl) ⟨720411, by rfl⟩ : syracuseStep 1921097 = 1440823) B1440823
theorem B1137919 : Blo 1136633 1137919 := bstep (se 1 (by rfl) ⟨853439, by rfl⟩ : syracuseStep 1137919 = 1706879) B1706879
theorem B1138431 : Blo 1136633 1138431 := bstep (se 1 (by rfl) ⟨853823, by rfl⟩ : syracuseStep 1138431 = 1707647) B1707647
theorem B15557453 : Blo 1136633 15557453 := bstep (se 3 (by rfl) ⟨2917022, by rfl⟩ : syracuseStep 15557453 = 5834045) B5834045
theorem B6319871 : Blo 1136633 6319871 := bstep (se 1 (by rfl) ⟨4739903, by rfl⟩ : syracuseStep 6319871 = 9479807) B9479807
theorem B4321619 : Blo 1136633 4321619 := bstep (se 1 (by rfl) ⟨3241214, by rfl⟩ : syracuseStep 4321619 = 6482429) B6482429
theorem B2160847 : Blo 1136633 2160847 := bstep (se 1 (by rfl) ⟨1620635, by rfl⟩ : syracuseStep 2160847 = 3241271) B3241271
theorem B3242855 : Blo 1136633 3242855 := bstep (se 1 (by rfl) ⟨2432141, by rfl⟩ : syracuseStep 3242855 = 4864283) B4864283
theorem B7306699 : Blo 1136633 7306699 := bstep (se 1 (by rfl) ⟨5480024, by rfl⟩ : syracuseStep 7306699 = 10960049) B10960049
theorem B8650313 : Blo 1136633 8650313 := bstep (se 2 (by rfl) ⟨3243867, by rfl⟩ : syracuseStep 8650313 = 6487735) B6487735
theorem B2884511 : Blo 1136633 2884511 := bstep (se 1 (by rfl) ⟨2163383, by rfl⟩ : syracuseStep 2884511 = 4326767) B4326767
theorem B2886313 : Blo 1136633 2886313 := bstep (se 2 (by rfl) ⟨1082367, by rfl⟩ : syracuseStep 2886313 = 2164735) B2164735
theorem B1280731 : Blo 1136633 1280731 := bstep (se 1 (by rfl) ⟨960548, by rfl⟩ : syracuseStep 1280731 = 1921097) B1921097
theorem B5838151 : Blo 1136633 5838151 := bstep (se 1 (by rfl) ⟨4378613, by rfl⟩ : syracuseStep 5838151 = 8757227) B8757227
theorem B17537417 : Blo 1136633 17537417 := bstep (se 2 (by rfl) ⟨6576531, by rfl⟩ : syracuseStep 17537417 = 13153063) B13153063
theorem B2563487 : Blo 1136633 2563487 := bstep (se 1 (by rfl) ⟨1922615, by rfl⟩ : syracuseStep 2563487 = 3845231) B3845231
theorem B236758301 : Blo 1136633 236758301 := bstep (se 3 (by rfl) ⟨44392181, by rfl⟩ : syracuseStep 236758301 = 88784363) B88784363
theorem B9742265 : Blo 1136633 9742265 := bstep (se 2 (by rfl) ⟨3653349, by rfl⟩ : syracuseStep 9742265 = 7306699) B7306699
theorem B10371635 : Blo 1136633 10371635 := bstep (se 1 (by rfl) ⟨7778726, by rfl⟩ : syracuseStep 10371635 = 15557453) B15557453
theorem B4213247 : Blo 1136633 4213247 := bstep (se 1 (by rfl) ⟨3159935, by rfl⟩ : syracuseStep 4213247 = 6319871) B6319871
theorem B9720121 : Blo 1136633 9720121 := bstep (se 2 (by rfl) ⟨3645045, by rfl⟩ : syracuseStep 9720121 = 7290091) B7290091
theorem B1136731 : Blo 1136633 1136731 := bstep (se 1 (by rfl) ⟨852548, by rfl⟩ : syracuseStep 1136731 = 1705097) B1705097
theorem B1136895 : Blo 1136633 1136895 := bstep (se 1 (by rfl) ⟨852671, by rfl⟩ : syracuseStep 1136895 = 1705343) B1705343
theorem B5463035 : Blo 1136633 5463035 := bstep (se 1 (by rfl) ⟨4097276, by rfl⟩ : syracuseStep 5463035 = 8194553) B8194553
theorem B1137659 : Blo 1136633 1137659 := bstep (se 1 (by rfl) ⟨853244, by rfl⟩ : syracuseStep 1137659 = 1706489) B1706489
theorem B1138623 : Blo 1136633 1138623 := bstep (se 1 (by rfl) ⟨853967, by rfl⟩ : syracuseStep 1138623 = 1707935) B1707935
theorem B1139175 : Blo 1136633 1139175 := bstep (se 1 (by rfl) ⟨854381, by rfl⟩ : syracuseStep 1139175 = 1708763) B1708763
theorem B2881079 : Blo 1136633 2881079 := bstep (se 1 (by rfl) ⟨2160809, by rfl⟩ : syracuseStep 2881079 = 4321619) B4321619
theorem B2881129 : Blo 1136633 2881129 := bstep (se 2 (by rfl) ⟨1080423, by rfl⟩ : syracuseStep 2881129 = 2160847) B2160847
theorem B2161903 : Blo 1136633 2161903 := bstep (se 1 (by rfl) ⟨1621427, by rfl⟩ : syracuseStep 2161903 = 3242855) B3242855
theorem B5766875 : Blo 1136633 5766875 := bstep (se 1 (by rfl) ⟨4325156, by rfl⟩ : syracuseStep 5766875 = 8650313) B8650313
theorem B149585879 : Blo 1136633 149585879 := bstep (se 1 (by rfl) ⟨112189409, by rfl⟩ : syracuseStep 149585879 = 224378819) B224378819
theorem B6914423 : Blo 1136633 6914423 := bstep (se 1 (by rfl) ⟨5185817, by rfl⟩ : syracuseStep 6914423 = 10371635) B10371635
theorem B1707641 : Blo 1136633 1707641 := bstep (se 2 (by rfl) ⟨640365, by rfl⟩ : syracuseStep 1707641 = 1280731) B1280731
theorem B3642023 : Blo 1136633 3642023 := bstep (se 1 (by rfl) ⟨2731517, by rfl⟩ : syracuseStep 3642023 = 5463035) B5463035
theorem B1708991 : Blo 1136633 1708991 := bstep (se 1 (by rfl) ⟨1281743, by rfl⟩ : syracuseStep 1708991 = 2563487) B2563487
theorem B6494843 : Blo 1136633 6494843 := bstep (se 1 (by rfl) ⟨4871132, by rfl⟩ : syracuseStep 6494843 = 9742265) B9742265
theorem B3841505 : Blo 1136633 3841505 := bstep (se 2 (by rfl) ⟨1440564, by rfl⟩ : syracuseStep 3841505 = 2881129) B2881129
theorem B3844583 : Blo 1136633 3844583 := bstep (se 1 (by rfl) ⟨2883437, by rfl⟩ : syracuseStep 3844583 = 5766875) B5766875
theorem B398895677 : Blo 1136633 398895677 := bstep (se 3 (by rfl) ⟨74792939, by rfl⟩ : syracuseStep 398895677 = 149585879) B149585879
theorem B3848417 : Blo 1136633 3848417 := bstep (se 2 (by rfl) ⟨1443156, by rfl⟩ : syracuseStep 3848417 = 2886313) B2886313
theorem B44941301 : Blo 1136633 44941301 := bstep (se 5 (by rfl) ⟨2106623, by rfl⟩ : syracuseStep 44941301 = 4213247) B4213247
theorem B12960161 : Blo 1136633 12960161 := bstep (se 2 (by rfl) ⟨4860060, by rfl⟩ : syracuseStep 12960161 = 9720121) B9720121
theorem B7784201 : Blo 1136633 7784201 := bstep (se 2 (by rfl) ⟨2919075, by rfl⟩ : syracuseStep 7784201 = 5838151) B5838151
theorem B1920719 : Blo 1136633 1920719 := bstep (se 1 (by rfl) ⟨1440539, by rfl⟩ : syracuseStep 1920719 = 2881079) B2881079
theorem B1923007 : Blo 1136633 1923007 := bstep (se 1 (by rfl) ⟨1442255, by rfl⟩ : syracuseStep 1923007 = 2884511) B2884511
theorem B11691611 : Blo 1136633 11691611 := bstep (se 1 (by rfl) ⟨8768708, by rfl⟩ : syracuseStep 11691611 = 17537417) B17537417
theorem B157838867 : Blo 1136633 157838867 := bstep (se 1 (by rfl) ⟨118379150, by rfl⟩ : syracuseStep 157838867 = 236758301) B236758301
theorem B2882537 : Blo 1136633 2882537 := bstep (se 2 (by rfl) ⟨1080951, by rfl⟩ : syracuseStep 2882537 = 2161903) B2161903
theorem B1280479 : Blo 1136633 1280479 := bstep (se 1 (by rfl) ⟨960359, by rfl⟩ : syracuseStep 1280479 = 1920719) B1920719
theorem B2428015 : Blo 1136633 2428015 := bstep (se 1 (by rfl) ⟨1821011, by rfl⟩ : syracuseStep 2428015 = 3642023) B3642023
theorem B4329895 : Blo 1136633 4329895 := bstep (se 1 (by rfl) ⟨3247421, by rfl⟩ : syracuseStep 4329895 = 6494843) B6494843
theorem B2561003 : Blo 1136633 2561003 := bstep (se 1 (by rfl) ⟨1920752, by rfl⟩ : syracuseStep 2561003 = 3841505) B3841505
theorem B2563055 : Blo 1136633 2563055 := bstep (se 1 (by rfl) ⟨1922291, by rfl⟩ : syracuseStep 2563055 = 3844583) B3844583
theorem B105225911 : Blo 1136633 105225911 := bstep (se 1 (by rfl) ⟨78919433, by rfl⟩ : syracuseStep 105225911 = 157838867) B157838867
theorem B2564009 : Blo 1136633 2564009 := bstep (se 2 (by rfl) ⟨961503, by rfl⟩ : syracuseStep 2564009 = 1923007) B1923007
theorem B2565611 : Blo 1136633 2565611 := bstep (se 1 (by rfl) ⟨1924208, by rfl⟩ : syracuseStep 2565611 = 3848417) B3848417
theorem B29960867 : Blo 1136633 29960867 := bstep (se 1 (by rfl) ⟨22470650, by rfl⟩ : syracuseStep 29960867 = 44941301) B44941301
theorem B5189467 : Blo 1136633 5189467 := bstep (se 1 (by rfl) ⟨3892100, by rfl⟩ : syracuseStep 5189467 = 7784201) B7784201
theorem B265930451 : Blo 1136633 265930451 := bstep (se 1 (by rfl) ⟨199447838, by rfl⟩ : syracuseStep 265930451 = 398895677) B398895677
theorem B1921691 : Blo 1136633 1921691 := bstep (se 1 (by rfl) ⟨1441268, by rfl⟩ : syracuseStep 1921691 = 2882537) B2882537
theorem B8640107 : Blo 1136633 8640107 := bstep (se 1 (by rfl) ⟨6480080, by rfl⟩ : syracuseStep 8640107 = 12960161) B12960161
theorem B18438461 : Blo 1136633 18438461 := bstep (se 3 (by rfl) ⟨3457211, by rfl⟩ : syracuseStep 18438461 = 6914423) B6914423
theorem B1138427 : Blo 1136633 1138427 := bstep (se 1 (by rfl) ⟨853820, by rfl⟩ : syracuseStep 1138427 = 1707641) B1707641
theorem B1139327 : Blo 1136633 1139327 := bstep (se 1 (by rfl) ⟨854495, by rfl⟩ : syracuseStep 1139327 = 1708991) B1708991
theorem B7794407 : Blo 1136633 7794407 := bstep (se 1 (by rfl) ⟨5845805, by rfl⟩ : syracuseStep 7794407 = 11691611) B11691611
theorem B1281127 : Blo 1136633 1281127 := bstep (se 1 (by rfl) ⟨960845, by rfl⟩ : syracuseStep 1281127 = 1921691) B1921691
theorem B1707305 : Blo 1136633 1707305 := bstep (se 2 (by rfl) ⟨640239, by rfl⟩ : syracuseStep 1707305 = 1280479) B1280479
theorem B1707335 : Blo 1136633 1707335 := bstep (se 1 (by rfl) ⟨1280501, by rfl⟩ : syracuseStep 1707335 = 2561003) B2561003
theorem B12292307 : Blo 1136633 12292307 := bstep (se 1 (by rfl) ⟨9219230, by rfl⟩ : syracuseStep 12292307 = 18438461) B18438461
theorem B1708703 : Blo 1136633 1708703 := bstep (se 1 (by rfl) ⟨1281527, by rfl⟩ : syracuseStep 1708703 = 2563055) B2563055
theorem B6919289 : Blo 1136633 6919289 := bstep (se 2 (by rfl) ⟨2594733, by rfl⟩ : syracuseStep 6919289 = 5189467) B5189467
theorem B1709339 : Blo 1136633 1709339 := bstep (se 1 (by rfl) ⟨1282004, by rfl⟩ : syracuseStep 1709339 = 2564009) B2564009
theorem B5773193 : Blo 1136633 5773193 := bstep (se 2 (by rfl) ⟨2164947, by rfl⟩ : syracuseStep 5773193 = 4329895) B4329895
theorem B1710407 : Blo 1136633 1710407 := bstep (se 1 (by rfl) ⟨1282805, by rfl⟩ : syracuseStep 1710407 = 2565611) B2565611
theorem B79895645 : Blo 1136633 79895645 := bstep (se 3 (by rfl) ⟨14980433, by rfl⟩ : syracuseStep 79895645 = 29960867) B29960867
theorem B177286967 : Blo 1136633 177286967 := bstep (se 1 (by rfl) ⟨132965225, by rfl⟩ : syracuseStep 177286967 = 265930451) B265930451
theorem B5196271 : Blo 1136633 5196271 := bstep (se 1 (by rfl) ⟨3897203, by rfl⟩ : syracuseStep 5196271 = 7794407) B7794407
theorem B5760071 : Blo 1136633 5760071 := bstep (se 1 (by rfl) ⟨4320053, by rfl⟩ : syracuseStep 5760071 = 8640107) B8640107
theorem B3237353 : Blo 1136633 3237353 := bstep (se 2 (by rfl) ⟨1214007, by rfl⟩ : syracuseStep 3237353 = 2428015) B2428015
theorem B70150607 : Blo 1136633 70150607 := bstep (se 1 (by rfl) ⟨52612955, by rfl⟩ : syracuseStep 70150607 = 105225911) B105225911
theorem B8194871 : Blo 1136633 8194871 := bstep (se 1 (by rfl) ⟨6146153, by rfl⟩ : syracuseStep 8194871 = 12292307) B12292307
theorem B1708169 : Blo 1136633 1708169 := bstep (se 2 (by rfl) ⟨640563, by rfl⟩ : syracuseStep 1708169 = 1281127) B1281127
theorem B3840047 : Blo 1136633 3840047 := bstep (se 1 (by rfl) ⟨2880035, by rfl⟩ : syracuseStep 3840047 = 5760071) B5760071
theorem B46767071 : Blo 1136633 46767071 := bstep (se 1 (by rfl) ⟨35075303, by rfl⟩ : syracuseStep 46767071 = 70150607) B70150607
theorem B6928361 : Blo 1136633 6928361 := bstep (se 2 (by rfl) ⟨2598135, by rfl⟩ : syracuseStep 6928361 = 5196271) B5196271
theorem B3848795 : Blo 1136633 3848795 := bstep (se 1 (by rfl) ⟨2886596, by rfl⟩ : syracuseStep 3848795 = 5773193) B5773193
theorem B53263763 : Blo 1136633 53263763 := bstep (se 1 (by rfl) ⟨39947822, by rfl⟩ : syracuseStep 53263763 = 79895645) B79895645
theorem B1138203 : Blo 1136633 1138203 := bstep (se 1 (by rfl) ⟨853652, by rfl⟩ : syracuseStep 1138203 = 1707305) B1707305
theorem B1138223 : Blo 1136633 1138223 := bstep (se 1 (by rfl) ⟨853667, by rfl⟩ : syracuseStep 1138223 = 1707335) B1707335
theorem B1139135 : Blo 1136633 1139135 := bstep (se 1 (by rfl) ⟨854351, by rfl⟩ : syracuseStep 1139135 = 1708703) B1708703
theorem B4612859 : Blo 1136633 4612859 := bstep (se 1 (by rfl) ⟨3459644, by rfl⟩ : syracuseStep 4612859 = 6919289) B6919289
theorem B1139559 : Blo 1136633 1139559 := bstep (se 1 (by rfl) ⟨854669, by rfl⟩ : syracuseStep 1139559 = 1709339) B1709339
theorem B1140271 : Blo 1136633 1140271 := bstep (se 1 (by rfl) ⟨855203, by rfl⟩ : syracuseStep 1140271 = 1710407) B1710407
theorem B2158235 : Blo 1136633 2158235 := bstep (se 1 (by rfl) ⟨1618676, by rfl⟩ : syracuseStep 2158235 = 3237353) B3237353
theorem B118191311 : Blo 1136633 118191311 := bstep (se 1 (by rfl) ⟨88643483, by rfl⟩ : syracuseStep 118191311 = 177286967) B177286967
theorem B2560031 : Blo 1136633 2560031 := bstep (se 1 (by rfl) ⟨1920023, by rfl⟩ : syracuseStep 2560031 = 3840047) B3840047
theorem B2565863 : Blo 1136633 2565863 := bstep (se 1 (by rfl) ⟨1924397, by rfl⟩ : syracuseStep 2565863 = 3848795) B3848795
theorem B31178047 : Blo 1136633 31178047 := bstep (se 1 (by rfl) ⟨23383535, by rfl⟩ : syracuseStep 31178047 = 46767071) B46767071
theorem B78794207 : Blo 1136633 78794207 := bstep (se 1 (by rfl) ⟨59095655, by rfl⟩ : syracuseStep 78794207 = 118191311) B118191311
theorem B35509175 : Blo 1136633 35509175 := bstep (se 1 (by rfl) ⟨26631881, by rfl⟩ : syracuseStep 35509175 = 53263763) B53263763
theorem B5463247 : Blo 1136633 5463247 := bstep (se 1 (by rfl) ⟨4097435, by rfl⟩ : syracuseStep 5463247 = 8194871) B8194871
theorem B1138779 : Blo 1136633 1138779 := bstep (se 1 (by rfl) ⟨854084, by rfl⟩ : syracuseStep 1138779 = 1708169) B1708169
theorem B3075239 : Blo 1136633 3075239 := bstep (se 1 (by rfl) ⟨2306429, by rfl⟩ : syracuseStep 3075239 = 4612859) B4612859
theorem B1438823 : Blo 1136633 1438823 := bstep (se 1 (by rfl) ⟨1079117, by rfl⟩ : syracuseStep 1438823 = 2158235) B2158235
theorem B4618907 : Blo 1136633 4618907 := bstep (se 1 (by rfl) ⟨3464180, by rfl⟩ : syracuseStep 4618907 = 6928361) B6928361
theorem B52529471 : Blo 1136633 52529471 := bstep (se 1 (by rfl) ⟨39397103, by rfl⟩ : syracuseStep 52529471 = 78794207) B78794207
theorem B1706687 : Blo 1136633 1706687 := bstep (se 1 (by rfl) ⟨1280015, by rfl⟩ : syracuseStep 1706687 = 2560031) B2560031
theorem B3836861 : Blo 1136633 3836861 := bstep (se 3 (by rfl) ⟨719411, by rfl⟩ : syracuseStep 3836861 = 1438823) B1438823
theorem B1710575 : Blo 1136633 1710575 := bstep (se 1 (by rfl) ⟨1282931, by rfl⟩ : syracuseStep 1710575 = 2565863) B2565863
theorem B7284329 : Blo 1136633 7284329 := bstep (se 2 (by rfl) ⟨2731623, by rfl⟩ : syracuseStep 7284329 = 5463247) B5463247
theorem B23672783 : Blo 1136633 23672783 := bstep (se 1 (by rfl) ⟨17754587, by rfl⟩ : syracuseStep 23672783 = 35509175) B35509175
theorem B2050159 : Blo 1136633 2050159 := bstep (se 1 (by rfl) ⟨1537619, by rfl⟩ : syracuseStep 2050159 = 3075239) B3075239
theorem B41570729 : Blo 1136633 41570729 := bstep (se 2 (by rfl) ⟨15589023, by rfl⟩ : syracuseStep 41570729 = 31178047) B31178047
theorem B3079271 : Blo 1136633 3079271 := bstep (se 1 (by rfl) ⟨2309453, by rfl⟩ : syracuseStep 3079271 = 4618907) B4618907
theorem B2557907 : Blo 1136633 2557907 := bstep (se 1 (by rfl) ⟨1918430, by rfl⟩ : syracuseStep 2557907 = 3836861) B3836861
theorem B4856219 : Blo 1136633 4856219 := bstep (se 1 (by rfl) ⟨3642164, by rfl⟩ : syracuseStep 4856219 = 7284329) B7284329
theorem B2733545 : Blo 1136633 2733545 := bstep (se 2 (by rfl) ⟨1025079, by rfl⟩ : syracuseStep 2733545 = 2050159) B2050159
theorem B63127421 : Blo 1136633 63127421 := bstep (se 3 (by rfl) ⟨11836391, by rfl⟩ : syracuseStep 63127421 = 23672783) B23672783
theorem B2052847 : Blo 1136633 2052847 := bstep (se 1 (by rfl) ⟨1539635, by rfl⟩ : syracuseStep 2052847 = 3079271) B3079271
theorem B35019647 : Blo 1136633 35019647 := bstep (se 1 (by rfl) ⟨26264735, by rfl⟩ : syracuseStep 35019647 = 52529471) B52529471
theorem B1137791 : Blo 1136633 1137791 := bstep (se 1 (by rfl) ⟨853343, by rfl⟩ : syracuseStep 1137791 = 1706687) B1706687
theorem B27713819 : Blo 1136633 27713819 := bstep (se 1 (by rfl) ⟨20785364, by rfl⟩ : syracuseStep 27713819 = 41570729) B41570729
theorem B1140383 : Blo 1136633 1140383 := bstep (se 1 (by rfl) ⟨855287, by rfl⟩ : syracuseStep 1140383 = 1710575) B1710575
theorem B1705271 : Blo 1136633 1705271 := bstep (se 1 (by rfl) ⟨1278953, by rfl⟩ : syracuseStep 1705271 = 2557907) B2557907
theorem B10948517 : Blo 1136633 10948517 := bstep (se 4 (by rfl) ⟨1026423, by rfl⟩ : syracuseStep 10948517 = 2052847) B2052847
theorem B42084947 : Blo 1136633 42084947 := bstep (se 1 (by rfl) ⟨31563710, by rfl⟩ : syracuseStep 42084947 = 63127421) B63127421
theorem B7289453 : Blo 1136633 7289453 := bstep (se 3 (by rfl) ⟨1366772, by rfl⟩ : syracuseStep 7289453 = 2733545) B2733545
theorem B23346431 : Blo 1136633 23346431 := bstep (se 1 (by rfl) ⟨17509823, by rfl⟩ : syracuseStep 23346431 = 35019647) B35019647
theorem B3237479 : Blo 1136633 3237479 := bstep (se 1 (by rfl) ⟨2428109, by rfl⟩ : syracuseStep 3237479 = 4856219) B4856219
theorem B18475879 : Blo 1136633 18475879 := bstep (se 1 (by rfl) ⟨13856909, by rfl⟩ : syracuseStep 18475879 = 27713819) B27713819
theorem B28056631 : Blo 1136633 28056631 := bstep (se 1 (by rfl) ⟨21042473, by rfl⟩ : syracuseStep 28056631 = 42084947) B42084947
theorem B4859635 : Blo 1136633 4859635 := bstep (se 1 (by rfl) ⟨3644726, by rfl⟩ : syracuseStep 4859635 = 7289453) B7289453
theorem B1136847 : Blo 1136633 1136847 := bstep (se 1 (by rfl) ⟨852635, by rfl⟩ : syracuseStep 1136847 = 1705271) B1705271
theorem B7299011 : Blo 1136633 7299011 := bstep (se 1 (by rfl) ⟨5474258, by rfl⟩ : syracuseStep 7299011 = 10948517) B10948517
theorem B24634505 : Blo 1136633 24634505 := bstep (se 2 (by rfl) ⟨9237939, by rfl⟩ : syracuseStep 24634505 = 18475879) B18475879
theorem B2158319 : Blo 1136633 2158319 := bstep (se 1 (by rfl) ⟨1618739, by rfl⟩ : syracuseStep 2158319 = 3237479) B3237479
theorem B15564287 : Blo 1136633 15564287 := bstep (se 1 (by rfl) ⟨11673215, by rfl⟩ : syracuseStep 15564287 = 23346431) B23346431
theorem B16423003 : Blo 1136633 16423003 := bstep (se 1 (by rfl) ⟨12317252, by rfl⟩ : syracuseStep 16423003 = 24634505) B24634505
theorem B4866007 : Blo 1136633 4866007 := bstep (se 1 (by rfl) ⟨3649505, by rfl⟩ : syracuseStep 4866007 = 7299011) B7299011
theorem B37408841 : Blo 1136633 37408841 := bstep (se 2 (by rfl) ⟨14028315, by rfl⟩ : syracuseStep 37408841 = 28056631) B28056631
theorem B10376191 : Blo 1136633 10376191 := bstep (se 1 (by rfl) ⟨7782143, by rfl⟩ : syracuseStep 10376191 = 15564287) B15564287
theorem B6479513 : Blo 1136633 6479513 := bstep (se 2 (by rfl) ⟨2429817, by rfl⟩ : syracuseStep 6479513 = 4859635) B4859635
theorem B1438879 : Blo 1136633 1438879 := bstep (se 1 (by rfl) ⟨1079159, by rfl⟩ : syracuseStep 1438879 = 2158319) B2158319
theorem B24939227 : Blo 1136633 24939227 := bstep (se 1 (by rfl) ⟨18704420, by rfl⟩ : syracuseStep 24939227 = 37408841) B37408841
theorem B13834921 : Blo 1136633 13834921 := bstep (se 2 (by rfl) ⟨5188095, by rfl⟩ : syracuseStep 13834921 = 10376191) B10376191
theorem B21897337 : Blo 1136633 21897337 := bstep (se 2 (by rfl) ⟨8211501, by rfl⟩ : syracuseStep 21897337 = 16423003) B16423003
theorem B1918505 : Blo 1136633 1918505 := bstep (se 2 (by rfl) ⟨719439, by rfl⟩ : syracuseStep 1918505 = 1438879) B1438879
theorem B4319675 : Blo 1136633 4319675 := bstep (se 1 (by rfl) ⟨3239756, by rfl⟩ : syracuseStep 4319675 = 6479513) B6479513
theorem B6488009 : Blo 1136633 6488009 := bstep (se 2 (by rfl) ⟨2433003, by rfl⟩ : syracuseStep 6488009 = 4866007) B4866007
theorem B29196449 : Blo 1136633 29196449 := bstep (se 2 (by rfl) ⟨10948668, by rfl⟩ : syracuseStep 29196449 = 21897337) B21897337
theorem B1279003 : Blo 1136633 1279003 := bstep (se 1 (by rfl) ⟨959252, by rfl⟩ : syracuseStep 1279003 = 1918505) B1918505
theorem B16626151 : Blo 1136633 16626151 := bstep (se 1 (by rfl) ⟨12469613, by rfl⟩ : syracuseStep 16626151 = 24939227) B24939227
theorem B2879783 : Blo 1136633 2879783 := bstep (se 1 (by rfl) ⟨2159837, by rfl⟩ : syracuseStep 2879783 = 4319675) B4319675
theorem B18446561 : Blo 1136633 18446561 := bstep (se 2 (by rfl) ⟨6917460, by rfl⟩ : syracuseStep 18446561 = 13834921) B13834921
theorem B4325339 : Blo 1136633 4325339 := bstep (se 1 (by rfl) ⟨3244004, by rfl⟩ : syracuseStep 4325339 = 6488009) B6488009
theorem B19464299 : Blo 1136633 19464299 := bstep (se 1 (by rfl) ⟨14598224, by rfl⟩ : syracuseStep 19464299 = 29196449) B29196449
theorem B1705337 : Blo 1136633 1705337 := bstep (se 2 (by rfl) ⟨639501, by rfl⟩ : syracuseStep 1705337 = 1279003) B1279003
theorem B88672805 : Blo 1136633 88672805 := bstep (se 4 (by rfl) ⟨8313075, by rfl⟩ : syracuseStep 88672805 = 16626151) B16626151
theorem B12297707 : Blo 1136633 12297707 := bstep (se 1 (by rfl) ⟨9223280, by rfl⟩ : syracuseStep 12297707 = 18446561) B18446561
theorem B1919855 : Blo 1136633 1919855 := bstep (se 1 (by rfl) ⟨1439891, by rfl⟩ : syracuseStep 1919855 = 2879783) B2879783
theorem B2883559 : Blo 1136633 2883559 := bstep (se 1 (by rfl) ⟨2162669, by rfl⟩ : syracuseStep 2883559 = 4325339) B4325339
theorem B12976199 : Blo 1136633 12976199 := bstep (se 1 (by rfl) ⟨9732149, by rfl⟩ : syracuseStep 12976199 = 19464299) B19464299
theorem B59115203 : Blo 1136633 59115203 := bstep (se 1 (by rfl) ⟨44336402, by rfl⟩ : syracuseStep 59115203 = 88672805) B88672805
theorem B1279903 : Blo 1136633 1279903 := bstep (se 1 (by rfl) ⟨959927, by rfl⟩ : syracuseStep 1279903 = 1919855) B1919855
theorem B8198471 : Blo 1136633 8198471 := bstep (se 1 (by rfl) ⟨6148853, by rfl⟩ : syracuseStep 8198471 = 12297707) B12297707
theorem B3844745 : Blo 1136633 3844745 := bstep (se 2 (by rfl) ⟨1441779, by rfl⟩ : syracuseStep 3844745 = 2883559) B2883559
theorem B1136891 : Blo 1136633 1136891 := bstep (se 1 (by rfl) ⟨852668, by rfl⟩ : syracuseStep 1136891 = 1705337) B1705337
theorem B8650799 : Blo 1136633 8650799 := bstep (se 1 (by rfl) ⟨6488099, by rfl⟩ : syracuseStep 8650799 = 12976199) B12976199
theorem B1706537 : Blo 1136633 1706537 := bstep (se 2 (by rfl) ⟨639951, by rfl⟩ : syracuseStep 1706537 = 1279903) B1279903
theorem B2563163 : Blo 1136633 2563163 := bstep (se 1 (by rfl) ⟨1922372, by rfl⟩ : syracuseStep 2563163 = 3844745) B3844745
theorem B39410135 : Blo 1136633 39410135 := bstep (se 1 (by rfl) ⟨29557601, by rfl⟩ : syracuseStep 39410135 = 59115203) B59115203
theorem B5465647 : Blo 1136633 5465647 := bstep (se 1 (by rfl) ⟨4099235, by rfl⟩ : syracuseStep 5465647 = 8198471) B8198471
theorem B5767199 : Blo 1136633 5767199 := bstep (se 1 (by rfl) ⟨4325399, by rfl⟩ : syracuseStep 5767199 = 8650799) B8650799
theorem B1708775 : Blo 1136633 1708775 := bstep (se 1 (by rfl) ⟨1281581, by rfl⟩ : syracuseStep 1708775 = 2563163) B2563163
theorem B7287529 : Blo 1136633 7287529 := bstep (se 2 (by rfl) ⟨2732823, by rfl⟩ : syracuseStep 7287529 = 5465647) B5465647
theorem B1137691 : Blo 1136633 1137691 := bstep (se 1 (by rfl) ⟨853268, by rfl⟩ : syracuseStep 1137691 = 1706537) B1706537
theorem B26273423 : Blo 1136633 26273423 := bstep (se 1 (by rfl) ⟨19705067, by rfl⟩ : syracuseStep 26273423 = 39410135) B39410135
theorem B3844799 : Blo 1136633 3844799 := bstep (se 1 (by rfl) ⟨2883599, by rfl⟩ : syracuseStep 3844799 = 5767199) B5767199
theorem B9716705 : Blo 1136633 9716705 := bstep (se 2 (by rfl) ⟨3643764, by rfl⟩ : syracuseStep 9716705 = 7287529) B7287529
theorem B17515615 : Blo 1136633 17515615 := bstep (se 1 (by rfl) ⟨13136711, by rfl⟩ : syracuseStep 17515615 = 26273423) B26273423
theorem B1139183 : Blo 1136633 1139183 := bstep (se 1 (by rfl) ⟨854387, by rfl⟩ : syracuseStep 1139183 = 1708775) B1708775
theorem B2563199 : Blo 1136633 2563199 := bstep (se 1 (by rfl) ⟨1922399, by rfl⟩ : syracuseStep 2563199 = 3844799) B3844799
theorem B6477803 : Blo 1136633 6477803 := bstep (se 1 (by rfl) ⟨4858352, by rfl⟩ : syracuseStep 6477803 = 9716705) B9716705
theorem B23354153 : Blo 1136633 23354153 := bstep (se 2 (by rfl) ⟨8757807, by rfl⟩ : syracuseStep 23354153 = 17515615) B17515615
theorem B15569435 : Blo 1136633 15569435 := bstep (se 1 (by rfl) ⟨11677076, by rfl⟩ : syracuseStep 15569435 = 23354153) B23354153
theorem B1708799 : Blo 1136633 1708799 := bstep (se 1 (by rfl) ⟨1281599, by rfl⟩ : syracuseStep 1708799 = 2563199) B2563199
theorem B4318535 : Blo 1136633 4318535 := bstep (se 1 (by rfl) ⟨3238901, by rfl⟩ : syracuseStep 4318535 = 6477803) B6477803
theorem B10379623 : Blo 1136633 10379623 := bstep (se 1 (by rfl) ⟨7784717, by rfl⟩ : syracuseStep 10379623 = 15569435) B15569435
theorem B1139199 : Blo 1136633 1139199 := bstep (se 1 (by rfl) ⟨854399, by rfl⟩ : syracuseStep 1139199 = 1708799) B1708799
theorem B2879023 : Blo 1136633 2879023 := bstep (se 1 (by rfl) ⟨2159267, by rfl⟩ : syracuseStep 2879023 = 4318535) B4318535
theorem B3838697 : Blo 1136633 3838697 := bstep (se 2 (by rfl) ⟨1439511, by rfl⟩ : syracuseStep 3838697 = 2879023) B2879023
theorem B13839497 : Blo 1136633 13839497 := bstep (se 2 (by rfl) ⟨5189811, by rfl⟩ : syracuseStep 13839497 = 10379623) B10379623
theorem B2559131 : Blo 1136633 2559131 := bstep (se 1 (by rfl) ⟨1919348, by rfl⟩ : syracuseStep 2559131 = 3838697) B3838697
theorem B9226331 : Blo 1136633 9226331 := bstep (se 1 (by rfl) ⟨6919748, by rfl⟩ : syracuseStep 9226331 = 13839497) B13839497
theorem B1706087 : Blo 1136633 1706087 := bstep (se 1 (by rfl) ⟨1279565, by rfl⟩ : syracuseStep 1706087 = 2559131) B2559131
theorem B6150887 : Blo 1136633 6150887 := bstep (se 1 (by rfl) ⟨4613165, by rfl⟩ : syracuseStep 6150887 = 9226331) B9226331
theorem B4100591 : Blo 1136633 4100591 := bstep (se 1 (by rfl) ⟨3075443, by rfl⟩ : syracuseStep 4100591 = 6150887) B6150887
theorem B1137391 : Blo 1136633 1137391 := bstep (se 1 (by rfl) ⟨853043, by rfl⟩ : syracuseStep 1137391 = 1706087) B1706087
theorem B10934909 : Blo 1136633 10934909 := bstep (se 3 (by rfl) ⟨2050295, by rfl⟩ : syracuseStep 10934909 = 4100591) B4100591
theorem B7289939 : Blo 1136633 7289939 := bstep (se 1 (by rfl) ⟨5467454, by rfl⟩ : syracuseStep 7289939 = 10934909) B10934909
theorem B4859959 : Blo 1136633 4859959 := bstep (se 1 (by rfl) ⟨3644969, by rfl⟩ : syracuseStep 4859959 = 7289939) B7289939
theorem B6479945 : Blo 1136633 6479945 := bstep (se 2 (by rfl) ⟨2429979, by rfl⟩ : syracuseStep 6479945 = 4859959) B4859959
theorem B4319963 : Blo 1136633 4319963 := bstep (se 1 (by rfl) ⟨3239972, by rfl⟩ : syracuseStep 4319963 = 6479945) B6479945
theorem B2879975 : Blo 1136633 2879975 := bstep (se 1 (by rfl) ⟨2159981, by rfl⟩ : syracuseStep 2879975 = 4319963) B4319963
theorem B1919983 : Blo 1136633 1919983 := bstep (se 1 (by rfl) ⟨1439987, by rfl⟩ : syracuseStep 1919983 = 2879975) B2879975
theorem B2559977 : Blo 1136633 2559977 := bstep (se 2 (by rfl) ⟨959991, by rfl⟩ : syracuseStep 2559977 = 1919983) B1919983
theorem B1706651 : Blo 1136633 1706651 := bstep (se 1 (by rfl) ⟨1279988, by rfl⟩ : syracuseStep 1706651 = 2559977) B2559977
theorem B1137767 : Blo 1136633 1137767 := bstep (se 1 (by rfl) ⟨853325, by rfl⟩ : syracuseStep 1137767 = 1706651) B1706651

theorem C0 (j : ℕ) (h1 : 284158 ≤ j) (h2 : j ≤ 284857) : Blo 1136633 (4 * j + 3) := by
  interval_cases j
  · exact B1136635
  · exact B1136639
  · exact B1136643
  · exact B1136647
  · exact B1136651
  · exact B1136655
  · exact B1136659
  · exact B1136663
  · exact B1136667
  · exact B1136671
  · exact B1136675
  · exact B1136679
  · exact B1136683
  · exact B1136687
  · exact B1136691
  · exact B1136695
  · exact B1136699
  · exact B1136703
  · exact B1136707
  · exact B1136711
  · exact B1136715
  · exact B1136719
  · exact B1136723
  · exact B1136727
  · exact B1136731
  · exact B1136735
  · exact B1136739
  · exact B1136743
  · exact B1136747
  · exact B1136751
  · exact B1136755
  · exact B1136759
  · exact B1136763
  · exact B1136767
  · exact B1136771
  · exact B1136775
  · exact B1136779
  · exact B1136783
  · exact B1136787
  · exact B1136791
  · exact B1136795
  · exact B1136799
  · exact B1136803
  · exact B1136807
  · exact B1136811
  · exact B1136815
  · exact B1136819
  · exact B1136823
  · exact B1136827
  · exact B1136831
  · exact B1136835
  · exact B1136839
  · exact B1136843
  · exact B1136847
  · exact B1136851
  · exact B1136855
  · exact B1136859
  · exact B1136863
  · exact B1136867
  · exact B1136871
  · exact B1136875
  · exact B1136879
  · exact B1136883
  · exact B1136887
  · exact B1136891
  · exact B1136895
  · exact B1136899
  · exact B1136903
  · exact B1136907
  · exact B1136911
  · exact B1136915
  · exact B1136919
  · exact B1136923
  · exact B1136927
  · exact B1136931
  · exact B1136935
  · exact B1136939
  · exact B1136943
  · exact B1136947
  · exact B1136951
  · exact B1136955
  · exact B1136959
  · exact B1136963
  · exact B1136967
  · exact B1136971
  · exact B1136975
  · exact B1136979
  · exact B1136983
  · exact B1136987
  · exact B1136991
  · exact B1136995
  · exact B1136999
  · exact B1137003
  · exact B1137007
  · exact B1137011
  · exact B1137015
  · exact B1137019
  · exact B1137023
  · exact B1137027
  · exact B1137031
  · exact B1137035
  · exact B1137039
  · exact B1137043
  · exact B1137047
  · exact B1137051
  · exact B1137055
  · exact B1137059
  · exact B1137063
  · exact B1137067
  · exact B1137071
  · exact B1137075
  · exact B1137079
  · exact B1137083
  · exact B1137087
  · exact B1137091
  · exact B1137095
  · exact B1137099
  · exact B1137103
  · exact B1137107
  · exact B1137111
  · exact B1137115
  · exact B1137119
  · exact B1137123
  · exact B1137127
  · exact B1137131
  · exact B1137135
  · exact B1137139
  · exact B1137143
  · exact B1137147
  · exact B1137151
  · exact B1137155
  · exact B1137159
  · exact B1137163
  · exact B1137167
  · exact B1137171
  · exact B1137175
  · exact B1137179
  · exact B1137183
  · exact B1137187
  · exact B1137191
  · exact B1137195
  · exact B1137199
  · exact B1137203
  · exact B1137207
  · exact B1137211
  · exact B1137215
  · exact B1137219
  · exact B1137223
  · exact B1137227
  · exact B1137231
  · exact B1137235
  · exact B1137239
  · exact B1137243
  · exact B1137247
  · exact B1137251
  · exact B1137255
  · exact B1137259
  · exact B1137263
  · exact B1137267
  · exact B1137271
  · exact B1137275
  · exact B1137279
  · exact B1137283
  · exact B1137287
  · exact B1137291
  · exact B1137295
  · exact B1137299
  · exact B1137303
  · exact B1137307
  · exact B1137311
  · exact B1137315
  · exact B1137319
  · exact B1137323
  · exact B1137327
  · exact B1137331
  · exact B1137335
  · exact B1137339
  · exact B1137343
  · exact B1137347
  · exact B1137351
  · exact B1137355
  · exact B1137359
  · exact B1137363
  · exact B1137367
  · exact B1137371
  · exact B1137375
  · exact B1137379
  · exact B1137383
  · exact B1137387
  · exact B1137391
  · exact B1137395
  · exact B1137399
  · exact B1137403
  · exact B1137407
  · exact B1137411
  · exact B1137415
  · exact B1137419
  · exact B1137423
  · exact B1137427
  · exact B1137431
  · exact B1137435
  · exact B1137439
  · exact B1137443
  · exact B1137447
  · exact B1137451
  · exact B1137455
  · exact B1137459
  · exact B1137463
  · exact B1137467
  · exact B1137471
  · exact B1137475
  · exact B1137479
  · exact B1137483
  · exact B1137487
  · exact B1137491
  · exact B1137495
  · exact B1137499
  · exact B1137503
  · exact B1137507
  · exact B1137511
  · exact B1137515
  · exact B1137519
  · exact B1137523
  · exact B1137527
  · exact B1137531
  · exact B1137535
  · exact B1137539
  · exact B1137543
  · exact B1137547
  · exact B1137551
  · exact B1137555
  · exact B1137559
  · exact B1137563
  · exact B1137567
  · exact B1137571
  · exact B1137575
  · exact B1137579
  · exact B1137583
  · exact B1137587
  · exact B1137591
  · exact B1137595
  · exact B1137599
  · exact B1137603
  · exact B1137607
  · exact B1137611
  · exact B1137615
  · exact B1137619
  · exact B1137623
  · exact B1137627
  · exact B1137631
  · exact B1137635
  · exact B1137639
  · exact B1137643
  · exact B1137647
  · exact B1137651
  · exact B1137655
  · exact B1137659
  · exact B1137663
  · exact B1137667
  · exact B1137671
  · exact B1137675
  · exact B1137679
  · exact B1137683
  · exact B1137687
  · exact B1137691
  · exact B1137695
  · exact B1137699
  · exact B1137703
  · exact B1137707
  · exact B1137711
  · exact B1137715
  · exact B1137719
  · exact B1137723
  · exact B1137727
  · exact B1137731
  · exact B1137735
  · exact B1137739
  · exact B1137743
  · exact B1137747
  · exact B1137751
  · exact B1137755
  · exact B1137759
  · exact B1137763
  · exact B1137767
  · exact B1137771
  · exact B1137775
  · exact B1137779
  · exact B1137783
  · exact B1137787
  · exact B1137791
  · exact B1137795
  · exact B1137799
  · exact B1137803
  · exact B1137807
  · exact B1137811
  · exact B1137815
  · exact B1137819
  · exact B1137823
  · exact B1137827
  · exact B1137831
  · exact B1137835
  · exact B1137839
  · exact B1137843
  · exact B1137847
  · exact B1137851
  · exact B1137855
  · exact B1137859
  · exact B1137863
  · exact B1137867
  · exact B1137871
  · exact B1137875
  · exact B1137879
  · exact B1137883
  · exact B1137887
  · exact B1137891
  · exact B1137895
  · exact B1137899
  · exact B1137903
  · exact B1137907
  · exact B1137911
  · exact B1137915
  · exact B1137919
  · exact B1137923
  · exact B1137927
  · exact B1137931
  · exact B1137935
  · exact B1137939
  · exact B1137943
  · exact B1137947
  · exact B1137951
  · exact B1137955
  · exact B1137959
  · exact B1137963
  · exact B1137967
  · exact B1137971
  · exact B1137975
  · exact B1137979
  · exact B1137983
  · exact B1137987
  · exact B1137991
  · exact B1137995
  · exact B1137999
  · exact B1138003
  · exact B1138007
  · exact B1138011
  · exact B1138015
  · exact B1138019
  · exact B1138023
  · exact B1138027
  · exact B1138031
  · exact B1138035
  · exact B1138039
  · exact B1138043
  · exact B1138047
  · exact B1138051
  · exact B1138055
  · exact B1138059
  · exact B1138063
  · exact B1138067
  · exact B1138071
  · exact B1138075
  · exact B1138079
  · exact B1138083
  · exact B1138087
  · exact B1138091
  · exact B1138095
  · exact B1138099
  · exact B1138103
  · exact B1138107
  · exact B1138111
  · exact B1138115
  · exact B1138119
  · exact B1138123
  · exact B1138127
  · exact B1138131
  · exact B1138135
  · exact B1138139
  · exact B1138143
  · exact B1138147
  · exact B1138151
  · exact B1138155
  · exact B1138159
  · exact B1138163
  · exact B1138167
  · exact B1138171
  · exact B1138175
  · exact B1138179
  · exact B1138183
  · exact B1138187
  · exact B1138191
  · exact B1138195
  · exact B1138199
  · exact B1138203
  · exact B1138207
  · exact B1138211
  · exact B1138215
  · exact B1138219
  · exact B1138223
  · exact B1138227
  · exact B1138231
  · exact B1138235
  · exact B1138239
  · exact B1138243
  · exact B1138247
  · exact B1138251
  · exact B1138255
  · exact B1138259
  · exact B1138263
  · exact B1138267
  · exact B1138271
  · exact B1138275
  · exact B1138279
  · exact B1138283
  · exact B1138287
  · exact B1138291
  · exact B1138295
  · exact B1138299
  · exact B1138303
  · exact B1138307
  · exact B1138311
  · exact B1138315
  · exact B1138319
  · exact B1138323
  · exact B1138327
  · exact B1138331
  · exact B1138335
  · exact B1138339
  · exact B1138343
  · exact B1138347
  · exact B1138351
  · exact B1138355
  · exact B1138359
  · exact B1138363
  · exact B1138367
  · exact B1138371
  · exact B1138375
  · exact B1138379
  · exact B1138383
  · exact B1138387
  · exact B1138391
  · exact B1138395
  · exact B1138399
  · exact B1138403
  · exact B1138407
  · exact B1138411
  · exact B1138415
  · exact B1138419
  · exact B1138423
  · exact B1138427
  · exact B1138431
  · exact B1138435
  · exact B1138439
  · exact B1138443
  · exact B1138447
  · exact B1138451
  · exact B1138455
  · exact B1138459
  · exact B1138463
  · exact B1138467
  · exact B1138471
  · exact B1138475
  · exact B1138479
  · exact B1138483
  · exact B1138487
  · exact B1138491
  · exact B1138495
  · exact B1138499
  · exact B1138503
  · exact B1138507
  · exact B1138511
  · exact B1138515
  · exact B1138519
  · exact B1138523
  · exact B1138527
  · exact B1138531
  · exact B1138535
  · exact B1138539
  · exact B1138543
  · exact B1138547
  · exact B1138551
  · exact B1138555
  · exact B1138559
  · exact B1138563
  · exact B1138567
  · exact B1138571
  · exact B1138575
  · exact B1138579
  · exact B1138583
  · exact B1138587
  · exact B1138591
  · exact B1138595
  · exact B1138599
  · exact B1138603
  · exact B1138607
  · exact B1138611
  · exact B1138615
  · exact B1138619
  · exact B1138623
  · exact B1138627
  · exact B1138631
  · exact B1138635
  · exact B1138639
  · exact B1138643
  · exact B1138647
  · exact B1138651
  · exact B1138655
  · exact B1138659
  · exact B1138663
  · exact B1138667
  · exact B1138671
  · exact B1138675
  · exact B1138679
  · exact B1138683
  · exact B1138687
  · exact B1138691
  · exact B1138695
  · exact B1138699
  · exact B1138703
  · exact B1138707
  · exact B1138711
  · exact B1138715
  · exact B1138719
  · exact B1138723
  · exact B1138727
  · exact B1138731
  · exact B1138735
  · exact B1138739
  · exact B1138743
  · exact B1138747
  · exact B1138751
  · exact B1138755
  · exact B1138759
  · exact B1138763
  · exact B1138767
  · exact B1138771
  · exact B1138775
  · exact B1138779
  · exact B1138783
  · exact B1138787
  · exact B1138791
  · exact B1138795
  · exact B1138799
  · exact B1138803
  · exact B1138807
  · exact B1138811
  · exact B1138815
  · exact B1138819
  · exact B1138823
  · exact B1138827
  · exact B1138831
  · exact B1138835
  · exact B1138839
  · exact B1138843
  · exact B1138847
  · exact B1138851
  · exact B1138855
  · exact B1138859
  · exact B1138863
  · exact B1138867
  · exact B1138871
  · exact B1138875
  · exact B1138879
  · exact B1138883
  · exact B1138887
  · exact B1138891
  · exact B1138895
  · exact B1138899
  · exact B1138903
  · exact B1138907
  · exact B1138911
  · exact B1138915
  · exact B1138919
  · exact B1138923
  · exact B1138927
  · exact B1138931
  · exact B1138935
  · exact B1138939
  · exact B1138943
  · exact B1138947
  · exact B1138951
  · exact B1138955
  · exact B1138959
  · exact B1138963
  · exact B1138967
  · exact B1138971
  · exact B1138975
  · exact B1138979
  · exact B1138983
  · exact B1138987
  · exact B1138991
  · exact B1138995
  · exact B1138999
  · exact B1139003
  · exact B1139007
  · exact B1139011
  · exact B1139015
  · exact B1139019
  · exact B1139023
  · exact B1139027
  · exact B1139031
  · exact B1139035
  · exact B1139039
  · exact B1139043
  · exact B1139047
  · exact B1139051
  · exact B1139055
  · exact B1139059
  · exact B1139063
  · exact B1139067
  · exact B1139071
  · exact B1139075
  · exact B1139079
  · exact B1139083
  · exact B1139087
  · exact B1139091
  · exact B1139095
  · exact B1139099
  · exact B1139103
  · exact B1139107
  · exact B1139111
  · exact B1139115
  · exact B1139119
  · exact B1139123
  · exact B1139127
  · exact B1139131
  · exact B1139135
  · exact B1139139
  · exact B1139143
  · exact B1139147
  · exact B1139151
  · exact B1139155
  · exact B1139159
  · exact B1139163
  · exact B1139167
  · exact B1139171
  · exact B1139175
  · exact B1139179
  · exact B1139183
  · exact B1139187
  · exact B1139191
  · exact B1139195
  · exact B1139199
  · exact B1139203
  · exact B1139207
  · exact B1139211
  · exact B1139215
  · exact B1139219
  · exact B1139223
  · exact B1139227
  · exact B1139231
  · exact B1139235
  · exact B1139239
  · exact B1139243
  · exact B1139247
  · exact B1139251
  · exact B1139255
  · exact B1139259
  · exact B1139263
  · exact B1139267
  · exact B1139271
  · exact B1139275
  · exact B1139279
  · exact B1139283
  · exact B1139287
  · exact B1139291
  · exact B1139295
  · exact B1139299
  · exact B1139303
  · exact B1139307
  · exact B1139311
  · exact B1139315
  · exact B1139319
  · exact B1139323
  · exact B1139327
  · exact B1139331
  · exact B1139335
  · exact B1139339
  · exact B1139343
  · exact B1139347
  · exact B1139351
  · exact B1139355
  · exact B1139359
  · exact B1139363
  · exact B1139367
  · exact B1139371
  · exact B1139375
  · exact B1139379
  · exact B1139383
  · exact B1139387
  · exact B1139391
  · exact B1139395
  · exact B1139399
  · exact B1139403
  · exact B1139407
  · exact B1139411
  · exact B1139415
  · exact B1139419
  · exact B1139423
  · exact B1139427
  · exact B1139431

theorem C1 (j : ℕ) (h1 : 284858 ≤ j) (h2 : j ≤ 285157) : Blo 1136633 (4 * j + 3) := by
  interval_cases j
  · exact B1139435
  · exact B1139439
  · exact B1139443
  · exact B1139447
  · exact B1139451
  · exact B1139455
  · exact B1139459
  · exact B1139463
  · exact B1139467
  · exact B1139471
  · exact B1139475
  · exact B1139479
  · exact B1139483
  · exact B1139487
  · exact B1139491
  · exact B1139495
  · exact B1139499
  · exact B1139503
  · exact B1139507
  · exact B1139511
  · exact B1139515
  · exact B1139519
  · exact B1139523
  · exact B1139527
  · exact B1139531
  · exact B1139535
  · exact B1139539
  · exact B1139543
  · exact B1139547
  · exact B1139551
  · exact B1139555
  · exact B1139559
  · exact B1139563
  · exact B1139567
  · exact B1139571
  · exact B1139575
  · exact B1139579
  · exact B1139583
  · exact B1139587
  · exact B1139591
  · exact B1139595
  · exact B1139599
  · exact B1139603
  · exact B1139607
  · exact B1139611
  · exact B1139615
  · exact B1139619
  · exact B1139623
  · exact B1139627
  · exact B1139631
  · exact B1139635
  · exact B1139639
  · exact B1139643
  · exact B1139647
  · exact B1139651
  · exact B1139655
  · exact B1139659
  · exact B1139663
  · exact B1139667
  · exact B1139671
  · exact B1139675
  · exact B1139679
  · exact B1139683
  · exact B1139687
  · exact B1139691
  · exact B1139695
  · exact B1139699
  · exact B1139703
  · exact B1139707
  · exact B1139711
  · exact B1139715
  · exact B1139719
  · exact B1139723
  · exact B1139727
  · exact B1139731
  · exact B1139735
  · exact B1139739
  · exact B1139743
  · exact B1139747
  · exact B1139751
  · exact B1139755
  · exact B1139759
  · exact B1139763
  · exact B1139767
  · exact B1139771
  · exact B1139775
  · exact B1139779
  · exact B1139783
  · exact B1139787
  · exact B1139791
  · exact B1139795
  · exact B1139799
  · exact B1139803
  · exact B1139807
  · exact B1139811
  · exact B1139815
  · exact B1139819
  · exact B1139823
  · exact B1139827
  · exact B1139831
  · exact B1139835
  · exact B1139839
  · exact B1139843
  · exact B1139847
  · exact B1139851
  · exact B1139855
  · exact B1139859
  · exact B1139863
  · exact B1139867
  · exact B1139871
  · exact B1139875
  · exact B1139879
  · exact B1139883
  · exact B1139887
  · exact B1139891
  · exact B1139895
  · exact B1139899
  · exact B1139903
  · exact B1139907
  · exact B1139911
  · exact B1139915
  · exact B1139919
  · exact B1139923
  · exact B1139927
  · exact B1139931
  · exact B1139935
  · exact B1139939
  · exact B1139943
  · exact B1139947
  · exact B1139951
  · exact B1139955
  · exact B1139959
  · exact B1139963
  · exact B1139967
  · exact B1139971
  · exact B1139975
  · exact B1139979
  · exact B1139983
  · exact B1139987
  · exact B1139991
  · exact B1139995
  · exact B1139999
  · exact B1140003
  · exact B1140007
  · exact B1140011
  · exact B1140015
  · exact B1140019
  · exact B1140023
  · exact B1140027
  · exact B1140031
  · exact B1140035
  · exact B1140039
  · exact B1140043
  · exact B1140047
  · exact B1140051
  · exact B1140055
  · exact B1140059
  · exact B1140063
  · exact B1140067
  · exact B1140071
  · exact B1140075
  · exact B1140079
  · exact B1140083
  · exact B1140087
  · exact B1140091
  · exact B1140095
  · exact B1140099
  · exact B1140103
  · exact B1140107
  · exact B1140111
  · exact B1140115
  · exact B1140119
  · exact B1140123
  · exact B1140127
  · exact B1140131
  · exact B1140135
  · exact B1140139
  · exact B1140143
  · exact B1140147
  · exact B1140151
  · exact B1140155
  · exact B1140159
  · exact B1140163
  · exact B1140167
  · exact B1140171
  · exact B1140175
  · exact B1140179
  · exact B1140183
  · exact B1140187
  · exact B1140191
  · exact B1140195
  · exact B1140199
  · exact B1140203
  · exact B1140207
  · exact B1140211
  · exact B1140215
  · exact B1140219
  · exact B1140223
  · exact B1140227
  · exact B1140231
  · exact B1140235
  · exact B1140239
  · exact B1140243
  · exact B1140247
  · exact B1140251
  · exact B1140255
  · exact B1140259
  · exact B1140263
  · exact B1140267
  · exact B1140271
  · exact B1140275
  · exact B1140279
  · exact B1140283
  · exact B1140287
  · exact B1140291
  · exact B1140295
  · exact B1140299
  · exact B1140303
  · exact B1140307
  · exact B1140311
  · exact B1140315
  · exact B1140319
  · exact B1140323
  · exact B1140327
  · exact B1140331
  · exact B1140335
  · exact B1140339
  · exact B1140343
  · exact B1140347
  · exact B1140351
  · exact B1140355
  · exact B1140359
  · exact B1140363
  · exact B1140367
  · exact B1140371
  · exact B1140375
  · exact B1140379
  · exact B1140383
  · exact B1140387
  · exact B1140391
  · exact B1140395
  · exact B1140399
  · exact B1140403
  · exact B1140407
  · exact B1140411
  · exact B1140415
  · exact B1140419
  · exact B1140423
  · exact B1140427
  · exact B1140431
  · exact B1140435
  · exact B1140439
  · exact B1140443
  · exact B1140447
  · exact B1140451
  · exact B1140455
  · exact B1140459
  · exact B1140463
  · exact B1140467
  · exact B1140471
  · exact B1140475
  · exact B1140479
  · exact B1140483
  · exact B1140487
  · exact B1140491
  · exact B1140495
  · exact B1140499
  · exact B1140503
  · exact B1140507
  · exact B1140511
  · exact B1140515
  · exact B1140519
  · exact B1140523
  · exact B1140527
  · exact B1140531
  · exact B1140535
  · exact B1140539
  · exact B1140543
  · exact B1140547
  · exact B1140551
  · exact B1140555
  · exact B1140559
  · exact B1140563
  · exact B1140567
  · exact B1140571
  · exact B1140575
  · exact B1140579
  · exact B1140583
  · exact B1140587
  · exact B1140591
  · exact B1140595
  · exact B1140599
  · exact B1140603
  · exact B1140607
  · exact B1140611
  · exact B1140615
  · exact B1140619
  · exact B1140623
  · exact B1140627
  · exact B1140631

theorem solution (m : ℕ) (hlo : 1136633 ≤ m) (hhi : m ≤ 1140633) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 284158 ≤ j := by omega
    have hj2 : j ≤ 285157 := by omega
    have hb : Blo 1136633 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 284858 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
