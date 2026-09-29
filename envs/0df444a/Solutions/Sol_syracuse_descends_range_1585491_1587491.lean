-- Prove2me | solution 1 for syracuse_descends_range_1585491_1587491
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:08:17.878877+00:00
-- url     : https://prove2.me/submissions/407ce7eb-2ee9-44f5-89ef-429377af3ddc

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


theorem B1785865 : Blo 1585491 1785865 := bbase (se 2 (by rfl) ⟨669699, by rfl⟩ : syracuseStep 1785865 = 1339399) (by norm_num)
theorem B3571757 : Blo 1585491 3571757 := bbase (se 3 (by rfl) ⟨669704, by rfl⟩ : syracuseStep 3571757 = 1339409) (by norm_num)
theorem B1785901 : Blo 1585491 1785901 := bbase (se 3 (by rfl) ⟨334856, by rfl⟩ : syracuseStep 1785901 = 669713) (by norm_num)
theorem B2678845 : Blo 1585491 2678845 := bbase (se 3 (by rfl) ⟨502283, by rfl⟩ : syracuseStep 2678845 = 1004567) (by norm_num)
theorem B2007109 : Blo 1585491 2007109 := bbase (se 4 (by rfl) ⟨188166, by rfl⟩ : syracuseStep 2007109 = 376333) (by norm_num)
theorem B4014157 : Blo 1585491 4014157 := bbase (se 3 (by rfl) ⟨752654, by rfl⟩ : syracuseStep 4014157 = 1505309) (by norm_num)
theorem B3571829 : Blo 1585491 3571829 := bbase (se 5 (by rfl) ⟨167429, by rfl⟩ : syracuseStep 3571829 = 334859) (by norm_num)
theorem B5357717 : Blo 1585491 5357717 := bbase (se 6 (by rfl) ⟨125571, by rfl⟩ : syracuseStep 5357717 = 251143) (by norm_num)
theorem B4014269 : Blo 1585491 4014269 := bbase (se 3 (by rfl) ⟨752675, by rfl⟩ : syracuseStep 4014269 = 1505351) (by norm_num)
theorem B2007281 : Blo 1585491 2007281 := bbase (se 2 (by rfl) ⟨752730, by rfl⟩ : syracuseStep 2007281 = 1505461) (by norm_num)
theorem B2007337 : Blo 1585491 2007337 := bbase (se 2 (by rfl) ⟨752751, by rfl⟩ : syracuseStep 2007337 = 1505503) (by norm_num)
theorem B4014461 : Blo 1585491 4014461 := bbase (se 3 (by rfl) ⟨752711, by rfl⟩ : syracuseStep 4014461 = 1505423) (by norm_num)
theorem B2007433 : Blo 1585491 2007433 := bbase (se 2 (by rfl) ⟨752787, by rfl⟩ : syracuseStep 2007433 = 1505575) (by norm_num)
theorem B2539973 : Blo 1585491 2539973 := bbase (se 4 (by rfl) ⟨238122, by rfl⟩ : syracuseStep 2539973 = 476245) (by norm_num)
theorem B2007605 : Blo 1585491 2007605 := bbase (se 5 (by rfl) ⟨94106, by rfl⟩ : syracuseStep 2007605 = 188213) (by norm_num)
theorem B2007661 : Blo 1585491 2007661 := bbase (se 3 (by rfl) ⟨376436, by rfl⟩ : syracuseStep 2007661 = 752873) (by norm_num)
theorem B7832213 : Blo 1585491 7832213 := bbase (se 6 (by rfl) ⟨183567, by rfl⟩ : syracuseStep 7832213 = 367135) (by norm_num)
theorem B22872725 : Blo 1585491 22872725 := bbase (se 6 (by rfl) ⟨536079, by rfl⟩ : syracuseStep 22872725 = 1072159) (by norm_num)
theorem B2540197 : Blo 1585491 2540197 := bbase (se 4 (by rfl) ⟨238143, by rfl⟩ : syracuseStep 2540197 = 476287) (by norm_num)
theorem B2007757 : Blo 1585491 2007757 := bbase (se 3 (by rfl) ⟨376454, by rfl⟩ : syracuseStep 2007757 = 752909) (by norm_num)
theorem B4014805 : Blo 1585491 4014805 := bbase (se 7 (by rfl) ⟨47048, by rfl⟩ : syracuseStep 4014805 = 94097) (by norm_num)
theorem B2540261 : Blo 1585491 2540261 := bbase (se 4 (by rfl) ⟨238149, by rfl⟩ : syracuseStep 2540261 = 476299) (by norm_num)
theorem B4014917 : Blo 1585491 4014917 := bbase (se 4 (by rfl) ⟨376398, by rfl⟩ : syracuseStep 4014917 = 752797) (by norm_num)
theorem B23192405 : Blo 1585491 23192405 := bbase (se 9 (by rfl) ⟨67946, by rfl⟩ : syracuseStep 23192405 = 135893) (by norm_num)
theorem B2540389 : Blo 1585491 2540389 := bbase (se 4 (by rfl) ⟨238161, by rfl⟩ : syracuseStep 2540389 = 476323) (by norm_num)
theorem B2007929 : Blo 1585491 2007929 := bbase (se 2 (by rfl) ⟨752973, by rfl⟩ : syracuseStep 2007929 = 1505947) (by norm_num)
theorem B2007985 : Blo 1585491 2007985 := bbase (se 2 (by rfl) ⟨752994, by rfl⟩ : syracuseStep 2007985 = 1505989) (by norm_num)
theorem B6022133 : Blo 1585491 6022133 := bbase (se 5 (by rfl) ⟨282287, by rfl⟩ : syracuseStep 6022133 = 564575) (by norm_num)
theorem B4015109 : Blo 1585491 4015109 := bbase (se 4 (by rfl) ⟨376416, by rfl⟩ : syracuseStep 4015109 = 752833) (by norm_num)
theorem B2008081 : Blo 1585491 2008081 := bbase (se 2 (by rfl) ⟨753030, by rfl⟩ : syracuseStep 2008081 = 1506061) (by norm_num)
theorem B8029205 : Blo 1585491 8029205 := bbase (se 6 (by rfl) ⟨188184, by rfl⟩ : syracuseStep 8029205 = 376369) (by norm_num)
theorem B7619669 : Blo 1585491 7619669 := bbase (se 8 (by rfl) ⟨44646, by rfl⟩ : syracuseStep 7619669 = 89293) (by norm_num)
theorem B2860181 : Blo 1585491 2860181 := bbase (se 6 (by rfl) ⟨67035, by rfl⟩ : syracuseStep 2860181 = 134071) (by norm_num)
theorem B2008253 : Blo 1585491 2008253 := bbase (se 3 (by rfl) ⟨376547, by rfl⟩ : syracuseStep 2008253 = 753095) (by norm_num)
theorem B2008309 : Blo 1585491 2008309 := bbase (se 5 (by rfl) ⟨94139, by rfl⟩ : syracuseStep 2008309 = 188279) (by norm_num)
theorem B6022421 : Blo 1585491 6022421 := bbase (se 6 (by rfl) ⟨141150, by rfl⟩ : syracuseStep 6022421 = 282301) (by norm_num)
theorem B10167605 : Blo 1585491 10167605 := bbase (se 5 (by rfl) ⟨476606, by rfl⟩ : syracuseStep 10167605 = 953213) (by norm_num)
theorem B2008405 : Blo 1585491 2008405 := bbase (se 12 (by rfl) ⟨735, by rfl⟩ : syracuseStep 2008405 = 1471) (by norm_num)
theorem B4015453 : Blo 1585491 4015453 := bbase (se 3 (by rfl) ⟨752897, by rfl⟩ : syracuseStep 4015453 = 1505795) (by norm_num)
theorem B7628165 : Blo 1585491 7628165 := bbase (se 4 (by rfl) ⟨715140, by rfl⟩ : syracuseStep 7628165 = 1430281) (by norm_num)
theorem B10855829 : Blo 1585491 10855829 := bbase (se 6 (by rfl) ⟨254433, by rfl⟩ : syracuseStep 10855829 = 508867) (by norm_num)
theorem B4015565 : Blo 1585491 4015565 := bbase (se 3 (by rfl) ⟨752918, by rfl⟩ : syracuseStep 4015565 = 1505837) (by norm_num)
theorem B2008577 : Blo 1585491 2008577 := bbase (se 2 (by rfl) ⟨753216, by rfl⟩ : syracuseStep 2008577 = 1506433) (by norm_num)
theorem B2008633 : Blo 1585491 2008633 := bbase (se 2 (by rfl) ⟨753237, by rfl⟩ : syracuseStep 2008633 = 1506475) (by norm_num)
theorem B6776405 : Blo 1585491 6776405 := bbase (se 8 (by rfl) ⟨39705, by rfl⟩ : syracuseStep 6776405 = 79411) (by norm_num)
theorem B4015757 : Blo 1585491 4015757 := bbase (se 3 (by rfl) ⟨752954, by rfl⟩ : syracuseStep 4015757 = 1505909) (by norm_num)
theorem B2008729 : Blo 1585491 2008729 := bbase (se 2 (by rfl) ⟨753273, by rfl⟩ : syracuseStep 2008729 = 1506547) (by norm_num)
theorem B3811045 : Blo 1585491 3811045 := bbase (se 4 (by rfl) ⟨357285, by rfl⟩ : syracuseStep 3811045 = 714571) (by norm_num)
theorem B5351237 : Blo 1585491 5351237 := bbase (se 4 (by rfl) ⟨501678, by rfl⟩ : syracuseStep 5351237 = 1003357) (by norm_num)
theorem B2008901 : Blo 1585491 2008901 := bbase (se 4 (by rfl) ⟨188334, by rfl⟩ : syracuseStep 2008901 = 376669) (by norm_num)
theorem B6776693 : Blo 1585491 6776693 := bbase (se 5 (by rfl) ⟨317657, by rfl⟩ : syracuseStep 6776693 = 635315) (by norm_num)
theorem B2008957 : Blo 1585491 2008957 := bbase (se 3 (by rfl) ⟨376679, by rfl⟩ : syracuseStep 2008957 = 753359) (by norm_num)
theorem B2009053 : Blo 1585491 2009053 := bbase (se 3 (by rfl) ⟨376697, by rfl⟩ : syracuseStep 2009053 = 753395) (by norm_num)
theorem B4016101 : Blo 1585491 4016101 := bbase (se 4 (by rfl) ⟨376509, by rfl⟩ : syracuseStep 4016101 = 753019) (by norm_num)
theorem B2541613 : Blo 1585491 2541613 := bbase (se 3 (by rfl) ⟨476552, by rfl⟩ : syracuseStep 2541613 = 953105) (by norm_num)
theorem B12863573 : Blo 1585491 12863573 := bbase (se 8 (by rfl) ⟨75372, by rfl⟩ : syracuseStep 12863573 = 150745) (by norm_num)
theorem B4016213 : Blo 1585491 4016213 := bbase (se 8 (by rfl) ⟨23532, by rfl⟩ : syracuseStep 4016213 = 47065) (by norm_num)
theorem B5351669 : Blo 1585491 5351669 := bbase (se 5 (by rfl) ⟨250859, by rfl⟩ : syracuseStep 5351669 = 501719) (by norm_num)
theorem B4016405 : Blo 1585491 4016405 := bbase (se 6 (by rfl) ⟨94134, by rfl⟩ : syracuseStep 4016405 = 188269) (by norm_num)
theorem B8030501 : Blo 1585491 8030501 := bbase (se 4 (by rfl) ⟨752859, by rfl⟩ : syracuseStep 8030501 = 1505719) (by norm_num)
theorem B3811661 : Blo 1585491 3811661 := bbase (se 3 (by rfl) ⟨714686, by rfl⟩ : syracuseStep 3811661 = 1429373) (by norm_num)
theorem B4581733 : Blo 1585491 4581733 := bbase (se 4 (by rfl) ⟨429537, by rfl⟩ : syracuseStep 4581733 = 859075) (by norm_num)
theorem B30501269 : Blo 1585491 30501269 := bbase (se 6 (by rfl) ⟨714873, by rfl⟩ : syracuseStep 30501269 = 1429747) (by norm_num)
theorem B6023605 : Blo 1585491 6023605 := bbase (se 5 (by rfl) ⟨282356, by rfl⟩ : syracuseStep 6023605 = 564713) (by norm_num)
theorem B2378237 : Blo 1585491 2378237 := bbase (se 3 (by rfl) ⟨445919, by rfl⟩ : syracuseStep 2378237 = 891839) (by norm_num)
theorem B2411021 : Blo 1585491 2411021 := bbase (se 3 (by rfl) ⟨452066, by rfl⟩ : syracuseStep 2411021 = 904133) (by norm_num)
theorem B3811853 : Blo 1585491 3811853 := bbase (se 3 (by rfl) ⟨714722, by rfl⟩ : syracuseStep 3811853 = 1429445) (by norm_num)
theorem B2378261 : Blo 1585491 2378261 := bbase (se 6 (by rfl) ⟨55740, by rfl⟩ : syracuseStep 2378261 = 111481) (by norm_num)
theorem B2378285 : Blo 1585491 2378285 := bbase (se 3 (by rfl) ⟨445928, by rfl⟩ : syracuseStep 2378285 = 891857) (by norm_num)
theorem B2378309 : Blo 1585491 2378309 := bbase (se 4 (by rfl) ⟨222966, by rfl⟩ : syracuseStep 2378309 = 445933) (by norm_num)
theorem B2378333 : Blo 1585491 2378333 := bbase (se 3 (by rfl) ⟨445937, by rfl⟩ : syracuseStep 2378333 = 891875) (by norm_num)
theorem B6777445 : Blo 1585491 6777445 := bbase (se 4 (by rfl) ⟨635385, by rfl⟩ : syracuseStep 6777445 = 1270771) (by norm_num)
theorem B4016749 : Blo 1585491 4016749 := bbase (se 3 (by rfl) ⟨753140, by rfl⟩ : syracuseStep 4016749 = 1506281) (by norm_num)
theorem B2378357 : Blo 1585491 2378357 := bbase (se 5 (by rfl) ⟨111485, by rfl⟩ : syracuseStep 2378357 = 222971) (by norm_num)
theorem B2378381 : Blo 1585491 2378381 := bbase (se 3 (by rfl) ⟨445946, by rfl⟩ : syracuseStep 2378381 = 891893) (by norm_num)
theorem B2378405 : Blo 1585491 2378405 := bbase (se 4 (by rfl) ⟨222975, by rfl⟩ : syracuseStep 2378405 = 445951) (by norm_num)
theorem B5352101 : Blo 1585491 5352101 := bbase (se 4 (by rfl) ⟨501759, by rfl⟩ : syracuseStep 5352101 = 1003519) (by norm_num)
theorem B2378429 : Blo 1585491 2378429 := bbase (se 3 (by rfl) ⟨445955, by rfl⟩ : syracuseStep 2378429 = 891911) (by norm_num)
theorem B1608385 : Blo 1585491 1608385 := bbase (se 2 (by rfl) ⟨603144, by rfl⟩ : syracuseStep 1608385 = 1206289) (by norm_num)
theorem B2542285 : Blo 1585491 2542285 := bbase (se 3 (by rfl) ⟨476678, by rfl⟩ : syracuseStep 2542285 = 953357) (by norm_num)
theorem B2378453 : Blo 1585491 2378453 := bbase (se 7 (by rfl) ⟨27872, by rfl⟩ : syracuseStep 2378453 = 55745) (by norm_num)
theorem B4016861 : Blo 1585491 4016861 := bbase (se 3 (by rfl) ⟨753161, by rfl⟩ : syracuseStep 4016861 = 1506323) (by norm_num)
theorem B2034401 : Blo 1585491 2034401 := bbase (se 2 (by rfl) ⟨762900, by rfl⟩ : syracuseStep 2034401 = 1525801) (by norm_num)
theorem B6023909 : Blo 1585491 6023909 := bbase (se 4 (by rfl) ⟨564741, by rfl⟩ : syracuseStep 6023909 = 1129483) (by norm_num)
theorem B2378477 : Blo 1585491 2378477 := bbase (se 3 (by rfl) ⟨445964, by rfl⟩ : syracuseStep 2378477 = 891929) (by norm_num)
theorem B2378501 : Blo 1585491 2378501 := bbase (se 4 (by rfl) ⟨222984, by rfl⟩ : syracuseStep 2378501 = 445969) (by norm_num)
theorem B2378525 : Blo 1585491 2378525 := bbase (se 3 (by rfl) ⟨445973, by rfl⟩ : syracuseStep 2378525 = 891947) (by norm_num)
theorem B2378549 : Blo 1585491 2378549 := bbase (se 5 (by rfl) ⟨111494, by rfl⟩ : syracuseStep 2378549 = 222989) (by norm_num)
theorem B2378573 : Blo 1585491 2378573 := bbase (se 3 (by rfl) ⟨445982, by rfl⟩ : syracuseStep 2378573 = 891965) (by norm_num)
theorem B2378597 : Blo 1585491 2378597 := bbase (se 4 (by rfl) ⟨222993, by rfl⟩ : syracuseStep 2378597 = 445987) (by norm_num)
theorem B2378621 : Blo 1585491 2378621 := bbase (se 3 (by rfl) ⟨445991, by rfl⟩ : syracuseStep 2378621 = 891983) (by norm_num)
theorem B2378645 : Blo 1585491 2378645 := bbase (se 6 (by rfl) ⟨55749, by rfl⟩ : syracuseStep 2378645 = 111499) (by norm_num)
theorem B4017053 : Blo 1585491 4017053 := bbase (se 3 (by rfl) ⟨753197, by rfl⟩ : syracuseStep 4017053 = 1506395) (by norm_num)
theorem B2378669 : Blo 1585491 2378669 := bbase (se 3 (by rfl) ⟨446000, by rfl⟩ : syracuseStep 2378669 = 892001) (by norm_num)
theorem B2378693 : Blo 1585491 2378693 := bbase (se 4 (by rfl) ⟨223002, by rfl⟩ : syracuseStep 2378693 = 446005) (by norm_num)
theorem B2378717 : Blo 1585491 2378717 := bbase (se 3 (by rfl) ⟨446009, by rfl⟩ : syracuseStep 2378717 = 892019) (by norm_num)
theorem B3386357 : Blo 1585491 3386357 := bbase (se 5 (by rfl) ⟨158735, by rfl⟩ : syracuseStep 3386357 = 317471) (by norm_num)
theorem B2378741 : Blo 1585491 2378741 := bbase (se 5 (by rfl) ⟨111503, by rfl⟩ : syracuseStep 2378741 = 223007) (by norm_num)
theorem B1608701 : Blo 1585491 1608701 := bbase (se 3 (by rfl) ⟨301631, by rfl⟩ : syracuseStep 1608701 = 603263) (by norm_num)
theorem B2378765 : Blo 1585491 2378765 := bbase (se 3 (by rfl) ⟨446018, by rfl⟩ : syracuseStep 2378765 = 892037) (by norm_num)
theorem B2378789 : Blo 1585491 2378789 := bbase (se 4 (by rfl) ⟨223011, by rfl⟩ : syracuseStep 2378789 = 446023) (by norm_num)
theorem B2378813 : Blo 1585491 2378813 := bbase (se 3 (by rfl) ⟨446027, by rfl⟩ : syracuseStep 2378813 = 892055) (by norm_num)
theorem B3812429 : Blo 1585491 3812429 := bbase (se 3 (by rfl) ⟨714830, by rfl⟩ : syracuseStep 3812429 = 1429661) (by norm_num)
theorem B2378837 : Blo 1585491 2378837 := bbase (se 8 (by rfl) ⟨13938, by rfl⟩ : syracuseStep 2378837 = 27877) (by norm_num)
theorem B5352533 : Blo 1585491 5352533 := bbase (se 8 (by rfl) ⟨31362, by rfl⟩ : syracuseStep 5352533 = 62725) (by norm_num)
theorem B2378861 : Blo 1585491 2378861 := bbase (se 3 (by rfl) ⟨446036, by rfl⟩ : syracuseStep 2378861 = 892073) (by norm_num)
theorem B2378885 : Blo 1585491 2378885 := bbase (se 4 (by rfl) ⟨223020, by rfl⟩ : syracuseStep 2378885 = 446041) (by norm_num)
theorem B12217493 : Blo 1585491 12217493 := bbase (se 6 (by rfl) ⟨286347, by rfl⟩ : syracuseStep 12217493 = 572695) (by norm_num)
theorem B2378909 : Blo 1585491 2378909 := bbase (se 3 (by rfl) ⟨446045, by rfl⟩ : syracuseStep 2378909 = 892091) (by norm_num)
theorem B2378933 : Blo 1585491 2378933 := bbase (se 5 (by rfl) ⟨111512, by rfl⟩ : syracuseStep 2378933 = 223025) (by norm_num)
theorem B2378957 : Blo 1585491 2378957 := bbase (se 3 (by rfl) ⟨446054, by rfl⟩ : syracuseStep 2378957 = 892109) (by norm_num)
theorem B2378981 : Blo 1585491 2378981 := bbase (se 4 (by rfl) ⟨223029, by rfl⟩ : syracuseStep 2378981 = 446059) (by norm_num)
theorem B4017397 : Blo 1585491 4017397 := bbase (se 5 (by rfl) ⟨188315, by rfl⟩ : syracuseStep 4017397 = 376631) (by norm_num)
theorem B2379005 : Blo 1585491 2379005 := bbase (se 3 (by rfl) ⟨446063, by rfl⟩ : syracuseStep 2379005 = 892127) (by norm_num)
theorem B2379029 : Blo 1585491 2379029 := bbase (se 6 (by rfl) ⟨55758, by rfl⟩ : syracuseStep 2379029 = 111517) (by norm_num)
theorem B1608985 : Blo 1585491 1608985 := bbase (se 2 (by rfl) ⟨603369, by rfl⟩ : syracuseStep 1608985 = 1206739) (by norm_num)
theorem B2379053 : Blo 1585491 2379053 := bbase (se 3 (by rfl) ⟨446072, by rfl⟩ : syracuseStep 2379053 = 892145) (by norm_num)
theorem B2379077 : Blo 1585491 2379077 := bbase (se 4 (by rfl) ⟨223038, by rfl⟩ : syracuseStep 2379077 = 446077) (by norm_num)
theorem B6778181 : Blo 1585491 6778181 := bbase (se 4 (by rfl) ⟨635454, by rfl⟩ : syracuseStep 6778181 = 1270909) (by norm_num)
theorem B2379101 : Blo 1585491 2379101 := bbase (se 3 (by rfl) ⟨446081, by rfl⟩ : syracuseStep 2379101 = 892163) (by norm_num)
theorem B4017509 : Blo 1585491 4017509 := bbase (se 4 (by rfl) ⟨376641, by rfl⟩ : syracuseStep 4017509 = 753283) (by norm_num)
theorem B2379125 : Blo 1585491 2379125 := bbase (se 5 (by rfl) ⟨111521, by rfl⟩ : syracuseStep 2379125 = 223043) (by norm_num)
theorem B2379149 : Blo 1585491 2379149 := bbase (se 3 (by rfl) ⟨446090, by rfl⟩ : syracuseStep 2379149 = 892181) (by norm_num)
theorem B2379173 : Blo 1585491 2379173 := bbase (se 4 (by rfl) ⟨223047, by rfl⟩ : syracuseStep 2379173 = 446095) (by norm_num)
theorem B3009973 : Blo 1585491 3009973 := bbase (se 5 (by rfl) ⟨141092, by rfl⟩ : syracuseStep 3009973 = 282185) (by norm_num)
theorem B2379197 : Blo 1585491 2379197 := bbase (se 3 (by rfl) ⟨446099, by rfl⟩ : syracuseStep 2379197 = 892199) (by norm_num)
theorem B3812813 : Blo 1585491 3812813 := bbase (se 3 (by rfl) ⟨714902, by rfl⟩ : syracuseStep 3812813 = 1429805) (by norm_num)
theorem B2379221 : Blo 1585491 2379221 := bbase (se 7 (by rfl) ⟨27881, by rfl⟩ : syracuseStep 2379221 = 55763) (by norm_num)
theorem B2379245 : Blo 1585491 2379245 := bbase (se 3 (by rfl) ⟨446108, by rfl⟩ : syracuseStep 2379245 = 892217) (by norm_num)
theorem B14470645 : Blo 1585491 14470645 := bbase (se 5 (by rfl) ⟨678311, by rfl⟩ : syracuseStep 14470645 = 1356623) (by norm_num)
theorem B5352965 : Blo 1585491 5352965 := bbase (se 4 (by rfl) ⟨501840, by rfl⟩ : syracuseStep 5352965 = 1003681) (by norm_num)
theorem B2379269 : Blo 1585491 2379269 := bbase (se 4 (by rfl) ⟨223056, by rfl⟩ : syracuseStep 2379269 = 446113) (by norm_num)
theorem B13544981 : Blo 1585491 13544981 := bbase (se 6 (by rfl) ⟨317460, by rfl⟩ : syracuseStep 13544981 = 634921) (by norm_num)
theorem B2379293 : Blo 1585491 2379293 := bbase (se 3 (by rfl) ⟨446117, by rfl⟩ : syracuseStep 2379293 = 892235) (by norm_num)
theorem B4017701 : Blo 1585491 4017701 := bbase (se 4 (by rfl) ⟨376659, by rfl⟩ : syracuseStep 4017701 = 753319) (by norm_num)
theorem B2379317 : Blo 1585491 2379317 := bbase (se 5 (by rfl) ⟨111530, by rfl⟩ : syracuseStep 2379317 = 223061) (by norm_num)
theorem B5795381 : Blo 1585491 5795381 := bbase (se 5 (by rfl) ⟨271658, by rfl⟩ : syracuseStep 5795381 = 543317) (by norm_num)
theorem B8031797 : Blo 1585491 8031797 := bbase (se 5 (by rfl) ⟨376490, by rfl⟩ : syracuseStep 8031797 = 752981) (by norm_num)
theorem B9653813 : Blo 1585491 9653813 := bbase (se 5 (by rfl) ⟨452522, by rfl⟩ : syracuseStep 9653813 = 905045) (by norm_num)
theorem B3010117 : Blo 1585491 3010117 := bbase (se 4 (by rfl) ⟨282198, by rfl⟩ : syracuseStep 3010117 = 564397) (by norm_num)
theorem B2379341 : Blo 1585491 2379341 := bbase (se 3 (by rfl) ⟨446126, by rfl⟩ : syracuseStep 2379341 = 892253) (by norm_num)
theorem B2379365 : Blo 1585491 2379365 := bbase (se 4 (by rfl) ⟨223065, by rfl⟩ : syracuseStep 2379365 = 446131) (by norm_num)
theorem B4517477 : Blo 1585491 4517477 := bbase (se 4 (by rfl) ⟨423513, by rfl⟩ : syracuseStep 4517477 = 847027) (by norm_num)
theorem B5082725 : Blo 1585491 5082725 := bbase (se 4 (by rfl) ⟨476505, by rfl⟩ : syracuseStep 5082725 = 953011) (by norm_num)
theorem B2379389 : Blo 1585491 2379389 := bbase (se 3 (by rfl) ⟨446135, by rfl⟩ : syracuseStep 2379389 = 892271) (by norm_num)
theorem B2379413 : Blo 1585491 2379413 := bbase (se 6 (by rfl) ⟨55767, by rfl⟩ : syracuseStep 2379413 = 111535) (by norm_num)
theorem B9039509 : Blo 1585491 9039509 := bbase (se 6 (by rfl) ⟨211863, by rfl⟩ : syracuseStep 9039509 = 423727) (by norm_num)
theorem B2379437 : Blo 1585491 2379437 := bbase (se 3 (by rfl) ⟨446144, by rfl⟩ : syracuseStep 2379437 = 892289) (by norm_num)
theorem B2379461 : Blo 1585491 2379461 := bbase (se 4 (by rfl) ⟨223074, by rfl⟩ : syracuseStep 2379461 = 446149) (by norm_num)
theorem B2379485 : Blo 1585491 2379485 := bbase (se 3 (by rfl) ⟨446153, by rfl⟩ : syracuseStep 2379485 = 892307) (by norm_num)
theorem B3010277 : Blo 1585491 3010277 := bbase (se 4 (by rfl) ⟨282213, by rfl⟩ : syracuseStep 3010277 = 564427) (by norm_num)
theorem B3387109 : Blo 1585491 3387109 := bbase (se 4 (by rfl) ⟨317541, by rfl⟩ : syracuseStep 3387109 = 635083) (by norm_num)
theorem B2379509 : Blo 1585491 2379509 := bbase (se 5 (by rfl) ⟨111539, by rfl⟩ : syracuseStep 2379509 = 223079) (by norm_num)
theorem B3567365 : Blo 1585491 3567365 := bbase (se 4 (by rfl) ⟨334440, by rfl⟩ : syracuseStep 3567365 = 668881) (by norm_num)
theorem B2379533 : Blo 1585491 2379533 := bbase (se 3 (by rfl) ⟨446162, by rfl⟩ : syracuseStep 2379533 = 892325) (by norm_num)
theorem B9031445 : Blo 1585491 9031445 := bbase (se 6 (by rfl) ⟨211674, by rfl⟩ : syracuseStep 9031445 = 423349) (by norm_num)
theorem B2379557 : Blo 1585491 2379557 := bbase (se 4 (by rfl) ⟨223083, by rfl⟩ : syracuseStep 2379557 = 446167) (by norm_num)
theorem B2379581 : Blo 1585491 2379581 := bbase (se 3 (by rfl) ⟨446171, by rfl⟩ : syracuseStep 2379581 = 892343) (by norm_num)
theorem B3215173 : Blo 1585491 3215173 := bbase (se 4 (by rfl) ⟨301422, by rfl⟩ : syracuseStep 3215173 = 602845) (by norm_num)
theorem B3567437 : Blo 1585491 3567437 := bbase (se 3 (by rfl) ⟨668894, by rfl⟩ : syracuseStep 3567437 = 1337789) (by norm_num)
theorem B36622165 : Blo 1585491 36622165 := bbase (se 9 (by rfl) ⟨107291, by rfl⟩ : syracuseStep 36622165 = 214583) (by norm_num)
theorem B2379605 : Blo 1585491 2379605 := bbase (se 9 (by rfl) ⟨6971, by rfl⟩ : syracuseStep 2379605 = 13943) (by norm_num)
theorem B2379629 : Blo 1585491 2379629 := bbase (se 3 (by rfl) ⟨446180, by rfl⟩ : syracuseStep 2379629 = 892361) (by norm_num)
theorem B3010421 : Blo 1585491 3010421 := bbase (se 5 (by rfl) ⟨141113, by rfl⟩ : syracuseStep 3010421 = 282227) (by norm_num)
theorem B3387253 : Blo 1585491 3387253 := bbase (se 5 (by rfl) ⟨158777, by rfl⟩ : syracuseStep 3387253 = 317555) (by norm_num)
theorem B4018045 : Blo 1585491 4018045 := bbase (se 3 (by rfl) ⟨753383, by rfl⟩ : syracuseStep 4018045 = 1506767) (by norm_num)
theorem B2379653 : Blo 1585491 2379653 := bbase (se 4 (by rfl) ⟨223092, by rfl⟩ : syracuseStep 2379653 = 446185) (by norm_num)
theorem B2322317 : Blo 1585491 2322317 := bbase (se 3 (by rfl) ⟨435434, by rfl⟩ : syracuseStep 2322317 = 870869) (by norm_num)
theorem B3567509 : Blo 1585491 3567509 := bbase (se 6 (by rfl) ⟨83613, by rfl⟩ : syracuseStep 3567509 = 167227) (by norm_num)
theorem B2379677 : Blo 1585491 2379677 := bbase (se 3 (by rfl) ⟨446189, by rfl⟩ : syracuseStep 2379677 = 892379) (by norm_num)
theorem B5353397 : Blo 1585491 5353397 := bbase (se 5 (by rfl) ⟨250940, by rfl⟩ : syracuseStep 5353397 = 501881) (by norm_num)
theorem B2379701 : Blo 1585491 2379701 := bbase (se 5 (by rfl) ⟨111548, by rfl⟩ : syracuseStep 2379701 = 223097) (by norm_num)
theorem B2379725 : Blo 1585491 2379725 := bbase (se 3 (by rfl) ⟨446198, by rfl⟩ : syracuseStep 2379725 = 892397) (by norm_num)
theorem B3567581 : Blo 1585491 3567581 := bbase (se 3 (by rfl) ⟨668921, by rfl⟩ : syracuseStep 3567581 = 1337843) (by norm_num)
theorem B2379749 : Blo 1585491 2379749 := bbase (se 4 (by rfl) ⟨223101, by rfl⟩ : syracuseStep 2379749 = 446203) (by norm_num)
theorem B4018157 : Blo 1585491 4018157 := bbase (se 3 (by rfl) ⟨753404, by rfl⟩ : syracuseStep 4018157 = 1506809) (by norm_num)
theorem B2379773 : Blo 1585491 2379773 := bbase (se 3 (by rfl) ⟨446207, by rfl⟩ : syracuseStep 2379773 = 892415) (by norm_num)
theorem B2379797 : Blo 1585491 2379797 := bbase (se 6 (by rfl) ⟨55776, by rfl⟩ : syracuseStep 2379797 = 111553) (by norm_num)
theorem B3567653 : Blo 1585491 3567653 := bbase (se 4 (by rfl) ⟨334467, by rfl⟩ : syracuseStep 3567653 = 668935) (by norm_num)
theorem B2379821 : Blo 1585491 2379821 := bbase (se 3 (by rfl) ⟨446216, by rfl⟩ : syracuseStep 2379821 = 892433) (by norm_num)
theorem B10850357 : Blo 1585491 10850357 := bbase (se 5 (by rfl) ⟨508610, by rfl⟩ : syracuseStep 10850357 = 1017221) (by norm_num)
theorem B2379845 : Blo 1585491 2379845 := bbase (se 4 (by rfl) ⟨223110, by rfl⟩ : syracuseStep 2379845 = 446221) (by norm_num)
theorem B2379869 : Blo 1585491 2379869 := bbase (se 3 (by rfl) ⟨446225, by rfl⟩ : syracuseStep 2379869 = 892451) (by norm_num)
theorem B7336037 : Blo 1585491 7336037 := bbase (se 4 (by rfl) ⟨687753, by rfl⟩ : syracuseStep 7336037 = 1375507) (by norm_num)
theorem B3567725 : Blo 1585491 3567725 := bbase (se 3 (by rfl) ⟨668948, by rfl⟩ : syracuseStep 3567725 = 1337897) (by norm_num)
theorem B2379893 : Blo 1585491 2379893 := bbase (se 5 (by rfl) ⟨111557, by rfl⟩ : syracuseStep 2379893 = 223115) (by norm_num)
theorem B2379917 : Blo 1585491 2379917 := bbase (se 3 (by rfl) ⟨446234, by rfl⟩ : syracuseStep 2379917 = 892469) (by norm_num)
theorem B3010709 : Blo 1585491 3010709 := bbase (se 6 (by rfl) ⟨70563, by rfl⟩ : syracuseStep 3010709 = 141127) (by norm_num)
theorem B8138917 : Blo 1585491 8138917 := bbase (se 4 (by rfl) ⟨763023, by rfl⟩ : syracuseStep 8138917 = 1526047) (by norm_num)
theorem B2379941 : Blo 1585491 2379941 := bbase (se 4 (by rfl) ⟨223119, by rfl⟩ : syracuseStep 2379941 = 446239) (by norm_num)
theorem B3436717 : Blo 1585491 3436717 := bbase (se 3 (by rfl) ⟨644384, by rfl⟩ : syracuseStep 3436717 = 1288769) (by norm_num)
theorem B3567797 : Blo 1585491 3567797 := bbase (se 5 (by rfl) ⟨167240, by rfl⟩ : syracuseStep 3567797 = 334481) (by norm_num)
theorem B2379965 : Blo 1585491 2379965 := bbase (se 3 (by rfl) ⟨446243, by rfl⟩ : syracuseStep 2379965 = 892487) (by norm_num)
theorem B2379989 : Blo 1585491 2379989 := bbase (se 7 (by rfl) ⟨27890, by rfl⟩ : syracuseStep 2379989 = 55781) (by norm_num)
theorem B3387629 : Blo 1585491 3387629 := bbase (se 3 (by rfl) ⟨635180, by rfl⟩ : syracuseStep 3387629 = 1270361) (by norm_num)
theorem B2380013 : Blo 1585491 2380013 := bbase (se 3 (by rfl) ⟨446252, by rfl⟩ : syracuseStep 2380013 = 892505) (by norm_num)
theorem B2576621 : Blo 1585491 2576621 := bbase (se 3 (by rfl) ⟨483116, by rfl⟩ : syracuseStep 2576621 = 966233) (by norm_num)
theorem B3567869 : Blo 1585491 3567869 := bbase (se 3 (by rfl) ⟨668975, by rfl⟩ : syracuseStep 3567869 = 1337951) (by norm_num)
theorem B2380037 : Blo 1585491 2380037 := bbase (se 4 (by rfl) ⟨223128, by rfl⟩ : syracuseStep 2380037 = 446257) (by norm_num)
theorem B2380061 : Blo 1585491 2380061 := bbase (se 3 (by rfl) ⟨446261, by rfl⟩ : syracuseStep 2380061 = 892523) (by norm_num)
theorem B3010861 : Blo 1585491 3010861 := bbase (se 3 (by rfl) ⟨564536, by rfl⟩ : syracuseStep 3010861 = 1129073) (by norm_num)
theorem B2380085 : Blo 1585491 2380085 := bbase (se 5 (by rfl) ⟨111566, by rfl⟩ : syracuseStep 2380085 = 223133) (by norm_num)
theorem B3567941 : Blo 1585491 3567941 := bbase (se 4 (by rfl) ⟨334494, by rfl⟩ : syracuseStep 3567941 = 668989) (by norm_num)
theorem B1716557 : Blo 1585491 1716557 := bbase (se 3 (by rfl) ⟨321854, by rfl⟩ : syracuseStep 1716557 = 643709) (by norm_num)
theorem B2380109 : Blo 1585491 2380109 := bbase (se 3 (by rfl) ⟨446270, by rfl⟩ : syracuseStep 2380109 = 892541) (by norm_num)
theorem B2412893 : Blo 1585491 2412893 := bbase (se 3 (by rfl) ⟨452417, by rfl⟩ : syracuseStep 2412893 = 904835) (by norm_num)
theorem B5353829 : Blo 1585491 5353829 := bbase (se 4 (by rfl) ⟨501921, by rfl⟩ : syracuseStep 5353829 = 1003843) (by norm_num)
theorem B2380133 : Blo 1585491 2380133 := bbase (se 4 (by rfl) ⟨223137, by rfl⟩ : syracuseStep 2380133 = 446275) (by norm_num)
theorem B2380157 : Blo 1585491 2380157 := bbase (se 3 (by rfl) ⟨446279, by rfl⟩ : syracuseStep 2380157 = 892559) (by norm_num)
theorem B3568013 : Blo 1585491 3568013 := bbase (se 3 (by rfl) ⟨669002, by rfl⟩ : syracuseStep 3568013 = 1338005) (by norm_num)
theorem B2380181 : Blo 1585491 2380181 := bbase (se 6 (by rfl) ⟨55785, by rfl⟩ : syracuseStep 2380181 = 111571) (by norm_num)
theorem B2380205 : Blo 1585491 2380205 := bbase (se 3 (by rfl) ⟨446288, by rfl⟩ : syracuseStep 2380205 = 892577) (by norm_num)
theorem B2380229 : Blo 1585491 2380229 := bbase (se 4 (by rfl) ⟨223146, by rfl⟩ : syracuseStep 2380229 = 446293) (by norm_num)
theorem B3568085 : Blo 1585491 3568085 := bbase (se 7 (by rfl) ⟨41813, by rfl⟩ : syracuseStep 3568085 = 83627) (by norm_num)
theorem B2380253 : Blo 1585491 2380253 := bbase (se 3 (by rfl) ⟨446297, by rfl⟩ : syracuseStep 2380253 = 892595) (by norm_num)
theorem B3215845 : Blo 1585491 3215845 := bbase (se 4 (by rfl) ⟨301485, by rfl⟩ : syracuseStep 3215845 = 602971) (by norm_num)
theorem B2380277 : Blo 1585491 2380277 := bbase (se 5 (by rfl) ⟨111575, by rfl⟩ : syracuseStep 2380277 = 223151) (by norm_num)
theorem B2380301 : Blo 1585491 2380301 := bbase (se 3 (by rfl) ⟨446306, by rfl⟩ : syracuseStep 2380301 = 892613) (by norm_num)
theorem B3568157 : Blo 1585491 3568157 := bbase (se 3 (by rfl) ⟨669029, by rfl⟩ : syracuseStep 3568157 = 1338059) (by norm_num)
theorem B2380325 : Blo 1585491 2380325 := bbase (se 4 (by rfl) ⟨223155, by rfl⟩ : syracuseStep 2380325 = 446311) (by norm_num)
theorem B2380349 : Blo 1585491 2380349 := bbase (se 3 (by rfl) ⟨446315, by rfl⟩ : syracuseStep 2380349 = 892631) (by norm_num)
theorem B2380373 : Blo 1585491 2380373 := bbase (se 8 (by rfl) ⟨13947, by rfl⟩ : syracuseStep 2380373 = 27895) (by norm_num)
theorem B3011165 : Blo 1585491 3011165 := bbase (se 3 (by rfl) ⟨564593, by rfl⟩ : syracuseStep 3011165 = 1129187) (by norm_num)
theorem B3387997 : Blo 1585491 3387997 := bbase (se 3 (by rfl) ⟨635249, by rfl⟩ : syracuseStep 3387997 = 1270499) (by norm_num)
theorem B3568229 : Blo 1585491 3568229 := bbase (se 4 (by rfl) ⟨334521, by rfl⟩ : syracuseStep 3568229 = 669043) (by norm_num)
theorem B2380397 : Blo 1585491 2380397 := bbase (se 3 (by rfl) ⟨446324, by rfl⟩ : syracuseStep 2380397 = 892649) (by norm_num)
theorem B2380421 : Blo 1585491 2380421 := bbase (se 4 (by rfl) ⟨223164, by rfl⟩ : syracuseStep 2380421 = 446329) (by norm_num)
theorem B2380445 : Blo 1585491 2380445 := bbase (se 3 (by rfl) ⟨446333, by rfl⟩ : syracuseStep 2380445 = 892667) (by norm_num)
theorem B3568301 : Blo 1585491 3568301 := bbase (se 3 (by rfl) ⟨669056, by rfl⟩ : syracuseStep 3568301 = 1338113) (by norm_num)
theorem B2380469 : Blo 1585491 2380469 := bbase (se 5 (by rfl) ⟨111584, by rfl⟩ : syracuseStep 2380469 = 223169) (by norm_num)
theorem B2380493 : Blo 1585491 2380493 := bbase (se 3 (by rfl) ⟨446342, by rfl⟩ : syracuseStep 2380493 = 892685) (by norm_num)
theorem B2380517 : Blo 1585491 2380517 := bbase (se 4 (by rfl) ⟨223173, by rfl⟩ : syracuseStep 2380517 = 446347) (by norm_num)
theorem B2257645 : Blo 1585491 2257645 := bbase (se 3 (by rfl) ⟨423308, by rfl⟩ : syracuseStep 2257645 = 846617) (by norm_num)
theorem B3568373 : Blo 1585491 3568373 := bbase (se 5 (by rfl) ⟨167267, by rfl⟩ : syracuseStep 3568373 = 334535) (by norm_num)
theorem B2380541 : Blo 1585491 2380541 := bbase (se 3 (by rfl) ⟨446351, by rfl⟩ : syracuseStep 2380541 = 892703) (by norm_num)
theorem B4518661 : Blo 1585491 4518661 := bbase (se 4 (by rfl) ⟨423624, by rfl⟩ : syracuseStep 4518661 = 847249) (by norm_num)
theorem B30479125 : Blo 1585491 30479125 := bbase (se 6 (by rfl) ⟨714354, by rfl⟩ : syracuseStep 30479125 = 1428709) (by norm_num)
theorem B5354261 : Blo 1585491 5354261 := bbase (se 6 (by rfl) ⟨125490, by rfl⟩ : syracuseStep 5354261 = 250981) (by norm_num)
theorem B2380565 : Blo 1585491 2380565 := bbase (se 6 (by rfl) ⟨55794, by rfl⟩ : syracuseStep 2380565 = 111589) (by norm_num)
theorem B6026021 : Blo 1585491 6026021 := bbase (se 4 (by rfl) ⟨564939, by rfl⟩ : syracuseStep 6026021 = 1129879) (by norm_num)
theorem B2143021 : Blo 1585491 2143021 := bbase (se 3 (by rfl) ⟨401816, by rfl⟩ : syracuseStep 2143021 = 803633) (by norm_num)
theorem B2380589 : Blo 1585491 2380589 := bbase (se 3 (by rfl) ⟨446360, by rfl⟩ : syracuseStep 2380589 = 892721) (by norm_num)
theorem B9646901 : Blo 1585491 9646901 := bbase (se 5 (by rfl) ⟨452198, by rfl⟩ : syracuseStep 9646901 = 904397) (by norm_num)
theorem B9040693 : Blo 1585491 9040693 := bbase (se 5 (by rfl) ⟨423782, by rfl⟩ : syracuseStep 9040693 = 847565) (by norm_num)
theorem B3568445 : Blo 1585491 3568445 := bbase (se 3 (by rfl) ⟨669083, by rfl⟩ : syracuseStep 3568445 = 1338167) (by norm_num)
theorem B8033093 : Blo 1585491 8033093 := bbase (se 4 (by rfl) ⟨753102, by rfl⟩ : syracuseStep 8033093 = 1506205) (by norm_num)
theorem B2380613 : Blo 1585491 2380613 := bbase (se 4 (by rfl) ⟨223182, by rfl⟩ : syracuseStep 2380613 = 446365) (by norm_num)
theorem B2380637 : Blo 1585491 2380637 := bbase (se 3 (by rfl) ⟨446369, by rfl⟩ : syracuseStep 2380637 = 892739) (by norm_num)
theorem B2380661 : Blo 1585491 2380661 := bbase (se 5 (by rfl) ⟨111593, by rfl⟩ : syracuseStep 2380661 = 223187) (by norm_num)
theorem B3568517 : Blo 1585491 3568517 := bbase (se 4 (by rfl) ⟨334548, by rfl⟩ : syracuseStep 3568517 = 669097) (by norm_num)
theorem B2380685 : Blo 1585491 2380685 := bbase (se 3 (by rfl) ⟨446378, by rfl⟩ : syracuseStep 2380685 = 892757) (by norm_num)
theorem B2675605 : Blo 1585491 2675605 := bbase (se 6 (by rfl) ⟨62709, by rfl⟩ : syracuseStep 2675605 = 125419) (by norm_num)
theorem B4518821 : Blo 1585491 4518821 := bbase (se 4 (by rfl) ⟨423639, by rfl⟩ : syracuseStep 4518821 = 847279) (by norm_num)
theorem B2380709 : Blo 1585491 2380709 := bbase (se 4 (by rfl) ⟨223191, by rfl⟩ : syracuseStep 2380709 = 446383) (by norm_num)
theorem B2380733 : Blo 1585491 2380733 := bbase (se 3 (by rfl) ⟨446387, by rfl⟩ : syracuseStep 2380733 = 892775) (by norm_num)
theorem B3568589 : Blo 1585491 3568589 := bbase (se 3 (by rfl) ⟨669110, by rfl⟩ : syracuseStep 3568589 = 1338221) (by norm_num)
theorem B18060245 : Blo 1585491 18060245 := bbase (se 7 (by rfl) ⟨211643, by rfl⟩ : syracuseStep 18060245 = 423287) (by norm_num)
theorem B2143189 : Blo 1585491 2143189 := bbase (se 7 (by rfl) ⟨25115, by rfl⟩ : syracuseStep 2143189 = 50231) (by norm_num)
theorem B9286613 : Blo 1585491 9286613 := bbase (se 7 (by rfl) ⟨108827, by rfl⟩ : syracuseStep 9286613 = 217655) (by norm_num)
theorem B2380757 : Blo 1585491 2380757 := bbase (se 7 (by rfl) ⟨27899, by rfl⟩ : syracuseStep 2380757 = 55799) (by norm_num)
theorem B2675693 : Blo 1585491 2675693 := bbase (se 3 (by rfl) ⟨501692, by rfl⟩ : syracuseStep 2675693 = 1003385) (by norm_num)
theorem B2380781 : Blo 1585491 2380781 := bbase (se 3 (by rfl) ⟨446396, by rfl⟩ : syracuseStep 2380781 = 892793) (by norm_num)
theorem B2380805 : Blo 1585491 2380805 := bbase (se 4 (by rfl) ⟨223200, by rfl⟩ : syracuseStep 2380805 = 446401) (by norm_num)
theorem B3568661 : Blo 1585491 3568661 := bbase (se 6 (by rfl) ⟨83640, by rfl⟩ : syracuseStep 3568661 = 167281) (by norm_num)
theorem B2380829 : Blo 1585491 2380829 := bbase (se 3 (by rfl) ⟨446405, by rfl⟩ : syracuseStep 2380829 = 892811) (by norm_num)
theorem B2380853 : Blo 1585491 2380853 := bbase (se 5 (by rfl) ⟨111602, by rfl⟩ : syracuseStep 2380853 = 223205) (by norm_num)
theorem B6026309 : Blo 1585491 6026309 := bbase (se 4 (by rfl) ⟨564966, by rfl⟩ : syracuseStep 6026309 = 1129933) (by norm_num)
theorem B2380877 : Blo 1585491 2380877 := bbase (se 3 (by rfl) ⟨446414, by rfl⟩ : syracuseStep 2380877 = 892829) (by norm_num)
theorem B3568733 : Blo 1585491 3568733 := bbase (se 3 (by rfl) ⟨669137, by rfl⟩ : syracuseStep 3568733 = 1338275) (by norm_num)
theorem B2380901 : Blo 1585491 2380901 := bbase (se 4 (by rfl) ⟨223209, by rfl⟩ : syracuseStep 2380901 = 446419) (by norm_num)
theorem B2675821 : Blo 1585491 2675821 := bbase (se 3 (by rfl) ⟨501716, by rfl⟩ : syracuseStep 2675821 = 1003433) (by norm_num)
theorem B2380925 : Blo 1585491 2380925 := bbase (se 3 (by rfl) ⟨446423, by rfl⟩ : syracuseStep 2380925 = 892847) (by norm_num)
theorem B4519061 : Blo 1585491 4519061 := bbase (se 6 (by rfl) ⟨105915, by rfl⟩ : syracuseStep 4519061 = 211831) (by norm_num)
theorem B2380949 : Blo 1585491 2380949 := bbase (se 6 (by rfl) ⟨55803, by rfl⟩ : syracuseStep 2380949 = 111607) (by norm_num)
theorem B3568805 : Blo 1585491 3568805 := bbase (se 4 (by rfl) ⟨334575, by rfl⟩ : syracuseStep 3568805 = 669151) (by norm_num)
theorem B2380973 : Blo 1585491 2380973 := bbase (se 3 (by rfl) ⟨446432, by rfl⟩ : syracuseStep 2380973 = 892865) (by norm_num)
theorem B2675909 : Blo 1585491 2675909 := bbase (se 4 (by rfl) ⟨250866, by rfl⟩ : syracuseStep 2675909 = 501733) (by norm_num)
theorem B5354693 : Blo 1585491 5354693 := bbase (se 4 (by rfl) ⟨502002, by rfl⟩ : syracuseStep 5354693 = 1004005) (by norm_num)
theorem B2380997 : Blo 1585491 2380997 := bbase (se 4 (by rfl) ⟨223218, by rfl⟩ : syracuseStep 2380997 = 446437) (by norm_num)
theorem B2381021 : Blo 1585491 2381021 := bbase (se 3 (by rfl) ⟨446441, by rfl⟩ : syracuseStep 2381021 = 892883) (by norm_num)
theorem B3568877 : Blo 1585491 3568877 := bbase (se 3 (by rfl) ⟨669164, by rfl⟩ : syracuseStep 3568877 = 1338329) (by norm_num)
theorem B2381045 : Blo 1585491 2381045 := bbase (se 5 (by rfl) ⟨111611, by rfl⟩ : syracuseStep 2381045 = 223223) (by norm_num)
theorem B2381069 : Blo 1585491 2381069 := bbase (se 3 (by rfl) ⟨446450, by rfl⟩ : syracuseStep 2381069 = 892901) (by norm_num)
theorem B7623973 : Blo 1585491 7623973 := bbase (se 4 (by rfl) ⟨714747, by rfl⟩ : syracuseStep 7623973 = 1429495) (by norm_num)
theorem B2381093 : Blo 1585491 2381093 := bbase (se 4 (by rfl) ⟨223227, by rfl⟩ : syracuseStep 2381093 = 446455) (by norm_num)
theorem B3568949 : Blo 1585491 3568949 := bbase (se 5 (by rfl) ⟨167294, by rfl⟩ : syracuseStep 3568949 = 334589) (by norm_num)
theorem B2258237 : Blo 1585491 2258237 := bbase (se 3 (by rfl) ⟨423419, by rfl⟩ : syracuseStep 2258237 = 846839) (by norm_num)
theorem B2381117 : Blo 1585491 2381117 := bbase (se 3 (by rfl) ⟨446459, by rfl⟩ : syracuseStep 2381117 = 892919) (by norm_num)
theorem B2676037 : Blo 1585491 2676037 := bbase (se 4 (by rfl) ⟨250878, by rfl⟩ : syracuseStep 2676037 = 501757) (by norm_num)
theorem B3011917 : Blo 1585491 3011917 := bbase (se 3 (by rfl) ⟨564734, by rfl⟩ : syracuseStep 3011917 = 1129469) (by norm_num)
theorem B4519253 : Blo 1585491 4519253 := bbase (se 13 (by rfl) ⟨827, by rfl⟩ : syracuseStep 4519253 = 1655) (by norm_num)
theorem B2381141 : Blo 1585491 2381141 := bbase (se 16 (by rfl) ⟨54, by rfl⟩ : syracuseStep 2381141 = 109) (by norm_num)
theorem B2381165 : Blo 1585491 2381165 := bbase (se 3 (by rfl) ⟨446468, by rfl⟩ : syracuseStep 2381165 = 892937) (by norm_num)
theorem B3569021 : Blo 1585491 3569021 := bbase (se 3 (by rfl) ⟨669191, by rfl⟩ : syracuseStep 3569021 = 1338383) (by norm_num)
theorem B2381189 : Blo 1585491 2381189 := bbase (se 4 (by rfl) ⟨223236, by rfl⟩ : syracuseStep 2381189 = 446473) (by norm_num)
theorem B2258317 : Blo 1585491 2258317 := bbase (se 3 (by rfl) ⟨423434, by rfl⟩ : syracuseStep 2258317 = 846869) (by norm_num)
theorem B2676125 : Blo 1585491 2676125 := bbase (se 3 (by rfl) ⟨501773, by rfl⟩ : syracuseStep 2676125 = 1003547) (by norm_num)
theorem B2381213 : Blo 1585491 2381213 := bbase (se 3 (by rfl) ⟨446477, by rfl⟩ : syracuseStep 2381213 = 892955) (by norm_num)
theorem B2381237 : Blo 1585491 2381237 := bbase (se 5 (by rfl) ⟨111620, by rfl⟩ : syracuseStep 2381237 = 223241) (by norm_num)
theorem B3569093 : Blo 1585491 3569093 := bbase (se 4 (by rfl) ⟨334602, by rfl⟩ : syracuseStep 3569093 = 669205) (by norm_num)
theorem B3012061 : Blo 1585491 3012061 := bbase (se 3 (by rfl) ⟨564761, by rfl⟩ : syracuseStep 3012061 = 1129523) (by norm_num)
theorem B2258437 : Blo 1585491 2258437 := bbase (se 4 (by rfl) ⟨211728, by rfl⟩ : syracuseStep 2258437 = 423457) (by norm_num)
theorem B3569165 : Blo 1585491 3569165 := bbase (se 3 (by rfl) ⟨669218, by rfl⟩ : syracuseStep 3569165 = 1338437) (by norm_num)
theorem B2676253 : Blo 1585491 2676253 := bbase (se 3 (by rfl) ⟨501797, by rfl⟩ : syracuseStep 2676253 = 1003595) (by norm_num)
theorem B9156149 : Blo 1585491 9156149 := bbase (se 5 (by rfl) ⟨429194, by rfl⟩ : syracuseStep 9156149 = 858389) (by norm_num)
theorem B3569237 : Blo 1585491 3569237 := bbase (se 8 (by rfl) ⟨20913, by rfl⟩ : syracuseStep 3569237 = 41827) (by norm_num)
theorem B2258533 : Blo 1585491 2258533 := bbase (se 4 (by rfl) ⟨211737, by rfl⟩ : syracuseStep 2258533 = 423475) (by norm_num)
theorem B2676341 : Blo 1585491 2676341 := bbase (se 5 (by rfl) ⟨125453, by rfl⟩ : syracuseStep 2676341 = 250907) (by norm_num)
theorem B5355125 : Blo 1585491 5355125 := bbase (se 5 (by rfl) ⟨251021, by rfl⟩ : syracuseStep 5355125 = 502043) (by norm_num)
theorem B3012221 : Blo 1585491 3012221 := bbase (se 3 (by rfl) ⟨564791, by rfl⟩ : syracuseStep 3012221 = 1129583) (by norm_num)
theorem B1906301 : Blo 1585491 1906301 := bbase (se 3 (by rfl) ⟨357431, by rfl⟩ : syracuseStep 1906301 = 714863) (by norm_num)
theorem B3569309 : Blo 1585491 3569309 := bbase (se 3 (by rfl) ⟨669245, by rfl⟩ : syracuseStep 3569309 = 1338491) (by norm_num)
theorem B10303157 : Blo 1585491 10303157 := bbase (se 5 (by rfl) ⟨482960, by rfl⟩ : syracuseStep 10303157 = 965921) (by norm_num)
theorem B8574677 : Blo 1585491 8574677 := bbase (se 7 (by rfl) ⟨100484, by rfl⟩ : syracuseStep 8574677 = 200969) (by norm_num)
theorem B1808101 : Blo 1585491 1808101 := bbase (se 4 (by rfl) ⟨169509, by rfl⟩ : syracuseStep 1808101 = 339019) (by norm_num)
theorem B3569381 : Blo 1585491 3569381 := bbase (se 4 (by rfl) ⟨334629, by rfl⟩ : syracuseStep 3569381 = 669259) (by norm_num)
theorem B2676469 : Blo 1585491 2676469 := bbase (se 5 (by rfl) ⟨125459, by rfl⟩ : syracuseStep 2676469 = 250919) (by norm_num)
theorem B3012365 : Blo 1585491 3012365 := bbase (se 3 (by rfl) ⟨564818, by rfl⟩ : syracuseStep 3012365 = 1129637) (by norm_num)
theorem B3569453 : Blo 1585491 3569453 := bbase (se 3 (by rfl) ⟨669272, by rfl⟩ : syracuseStep 3569453 = 1338545) (by norm_num)
theorem B5084981 : Blo 1585491 5084981 := bbase (se 5 (by rfl) ⟨238358, by rfl⟩ : syracuseStep 5084981 = 476717) (by norm_num)
theorem B2676557 : Blo 1585491 2676557 := bbase (se 3 (by rfl) ⟨501854, by rfl⟩ : syracuseStep 2676557 = 1003709) (by norm_num)
theorem B3569525 : Blo 1585491 3569525 := bbase (se 5 (by rfl) ⟨167321, by rfl⟩ : syracuseStep 3569525 = 334643) (by norm_num)
theorem B1783705 : Blo 1585491 1783705 := bbase (se 2 (by rfl) ⟨668889, by rfl⟩ : syracuseStep 1783705 = 1337779) (by norm_num)
theorem B5085109 : Blo 1585491 5085109 := bbase (se 5 (by rfl) ⟨238364, by rfl⟩ : syracuseStep 5085109 = 476729) (by norm_num)
theorem B1783741 : Blo 1585491 1783741 := bbase (se 3 (by rfl) ⟨334451, by rfl⟩ : syracuseStep 1783741 = 668903) (by norm_num)
theorem B3569597 : Blo 1585491 3569597 := bbase (se 3 (by rfl) ⟨669299, by rfl⟩ : syracuseStep 3569597 = 1338599) (by norm_num)
theorem B2676685 : Blo 1585491 2676685 := bbase (se 3 (by rfl) ⟨501878, by rfl⟩ : syracuseStep 2676685 = 1003757) (by norm_num)
theorem B1906637 : Blo 1585491 1906637 := bbase (se 3 (by rfl) ⟨357494, by rfl⟩ : syracuseStep 1906637 = 714989) (by norm_num)
theorem B1693657 : Blo 1585491 1693657 := bbase (se 2 (by rfl) ⟨635121, by rfl⟩ : syracuseStep 1693657 = 1270243) (by norm_num)
theorem B1783777 : Blo 1585491 1783777 := bbase (se 2 (by rfl) ⟨668916, by rfl⟩ : syracuseStep 1783777 = 1337833) (by norm_num)
theorem B1783813 : Blo 1585491 1783813 := bbase (se 4 (by rfl) ⟨167232, by rfl⟩ : syracuseStep 1783813 = 334465) (by norm_num)
theorem B8140805 : Blo 1585491 8140805 := bbase (se 4 (by rfl) ⟨763200, by rfl⟩ : syracuseStep 8140805 = 1526401) (by norm_num)
theorem B3569669 : Blo 1585491 3569669 := bbase (se 4 (by rfl) ⟨334656, by rfl⟩ : syracuseStep 3569669 = 669313) (by norm_num)
theorem B1693729 : Blo 1585491 1693729 := bbase (se 2 (by rfl) ⟨635148, by rfl⟩ : syracuseStep 1693729 = 1270297) (by norm_num)
theorem B2676773 : Blo 1585491 2676773 := bbase (se 4 (by rfl) ⟨250947, by rfl⟩ : syracuseStep 2676773 = 501895) (by norm_num)
theorem B5355557 : Blo 1585491 5355557 := bbase (se 4 (by rfl) ⟨502083, by rfl⟩ : syracuseStep 5355557 = 1004167) (by norm_num)
theorem B1783849 : Blo 1585491 1783849 := bbase (se 2 (by rfl) ⟨668943, by rfl⟩ : syracuseStep 1783849 = 1337887) (by norm_num)
theorem B3012653 : Blo 1585491 3012653 := bbase (se 3 (by rfl) ⟨564872, by rfl⟩ : syracuseStep 3012653 = 1129745) (by norm_num)
theorem B5716021 : Blo 1585491 5716021 := bbase (se 5 (by rfl) ⟨267938, by rfl⟩ : syracuseStep 5716021 = 535877) (by norm_num)
theorem B3389501 : Blo 1585491 3389501 := bbase (se 3 (by rfl) ⟨635531, by rfl⟩ : syracuseStep 3389501 = 1271063) (by norm_num)
theorem B1906753 : Blo 1585491 1906753 := bbase (se 2 (by rfl) ⟨715032, by rfl⟩ : syracuseStep 1906753 = 1430065) (by norm_num)
theorem B1783885 : Blo 1585491 1783885 := bbase (se 3 (by rfl) ⟨334478, by rfl⟩ : syracuseStep 1783885 = 668957) (by norm_num)
theorem B3569741 : Blo 1585491 3569741 := bbase (se 3 (by rfl) ⟨669326, by rfl⟩ : syracuseStep 3569741 = 1338653) (by norm_num)
theorem B2259029 : Blo 1585491 2259029 := bbase (se 8 (by rfl) ⟨13236, by rfl⟩ : syracuseStep 2259029 = 26473) (by norm_num)
theorem B8034389 : Blo 1585491 8034389 := bbase (se 8 (by rfl) ⟨47076, by rfl⟩ : syracuseStep 8034389 = 94153) (by norm_num)
theorem B1783921 : Blo 1585491 1783921 := bbase (se 2 (by rfl) ⟨668970, by rfl⟩ : syracuseStep 1783921 = 1337941) (by norm_num)
theorem B1906825 : Blo 1585491 1906825 := bbase (se 2 (by rfl) ⟨715059, by rfl⟩ : syracuseStep 1906825 = 1430119) (by norm_num)
theorem B1783957 : Blo 1585491 1783957 := bbase (se 6 (by rfl) ⟨41811, by rfl⟩ : syracuseStep 1783957 = 83623) (by norm_num)
theorem B3569813 : Blo 1585491 3569813 := bbase (se 6 (by rfl) ⟨83667, by rfl⟩ : syracuseStep 3569813 = 167335) (by norm_num)
theorem B2144405 : Blo 1585491 2144405 := bbase (se 6 (by rfl) ⟨50259, by rfl⟩ : syracuseStep 2144405 = 100519) (by norm_num)
theorem B1906849 : Blo 1585491 1906849 := bbase (se 2 (by rfl) ⟨715068, by rfl⟩ : syracuseStep 1906849 = 1430137) (by norm_num)
theorem B2676901 : Blo 1585491 2676901 := bbase (se 4 (by rfl) ⟨250959, by rfl⟩ : syracuseStep 2676901 = 501919) (by norm_num)
theorem B1783993 : Blo 1585491 1783993 := bbase (se 2 (by rfl) ⟨668997, by rfl⟩ : syracuseStep 1783993 = 1337995) (by norm_num)
theorem B3012805 : Blo 1585491 3012805 := bbase (se 4 (by rfl) ⟨282450, by rfl⟩ : syracuseStep 3012805 = 564901) (by norm_num)
theorem B3389645 : Blo 1585491 3389645 := bbase (se 3 (by rfl) ⟨635558, by rfl⟩ : syracuseStep 3389645 = 1271117) (by norm_num)
theorem B1693909 : Blo 1585491 1693909 := bbase (se 7 (by rfl) ⟨19850, by rfl⟩ : syracuseStep 1693909 = 39701) (by norm_num)
theorem B1784029 : Blo 1585491 1784029 := bbase (se 3 (by rfl) ⟨334505, by rfl⟩ : syracuseStep 1784029 = 669011) (by norm_num)
theorem B3569885 : Blo 1585491 3569885 := bbase (se 3 (by rfl) ⟨669353, by rfl⟩ : syracuseStep 3569885 = 1338707) (by norm_num)
theorem B6027493 : Blo 1585491 6027493 := bbase (se 4 (by rfl) ⟨565077, by rfl⟩ : syracuseStep 6027493 = 1130155) (by norm_num)
theorem B2676989 : Blo 1585491 2676989 := bbase (se 3 (by rfl) ⟨501935, by rfl⟩ : syracuseStep 2676989 = 1003871) (by norm_num)
theorem B1784065 : Blo 1585491 1784065 := bbase (se 2 (by rfl) ⟨669024, by rfl⟩ : syracuseStep 1784065 = 1338049) (by norm_num)
theorem B6428933 : Blo 1585491 6428933 := bbase (se 4 (by rfl) ⟨602712, by rfl⟩ : syracuseStep 6428933 = 1205425) (by norm_num)
theorem B1784101 : Blo 1585491 1784101 := bbase (se 4 (by rfl) ⟨167259, by rfl⟩ : syracuseStep 1784101 = 334519) (by norm_num)
theorem B3569957 : Blo 1585491 3569957 := bbase (se 4 (by rfl) ⟨334683, by rfl⟩ : syracuseStep 3569957 = 669367) (by norm_num)
theorem B1906993 : Blo 1585491 1906993 := bbase (se 2 (by rfl) ⟨715122, by rfl⟩ : syracuseStep 1906993 = 1430245) (by norm_num)
theorem B4520245 : Blo 1585491 4520245 := bbase (se 5 (by rfl) ⟨211886, by rfl⟩ : syracuseStep 4520245 = 423773) (by norm_num)
theorem B1784137 : Blo 1585491 1784137 := bbase (se 2 (by rfl) ⟨669051, by rfl⟩ : syracuseStep 1784137 = 1338103) (by norm_num)
theorem B198162773 : Blo 1585491 198162773 := bbase (se 10 (by rfl) ⟨290277, by rfl⟩ : syracuseStep 198162773 = 580555) (by norm_num)
theorem B1784173 : Blo 1585491 1784173 := bbase (se 3 (by rfl) ⟨334532, by rfl⟩ : syracuseStep 1784173 = 669065) (by norm_num)
theorem B3570029 : Blo 1585491 3570029 := bbase (se 3 (by rfl) ⟨669380, by rfl⟩ : syracuseStep 3570029 = 1338761) (by norm_num)
theorem B2677117 : Blo 1585491 2677117 := bbase (se 3 (by rfl) ⟨501959, by rfl⟩ : syracuseStep 2677117 = 1003919) (by norm_num)
theorem B1784209 : Blo 1585491 1784209 := bbase (se 2 (by rfl) ⟨669078, by rfl⟩ : syracuseStep 1784209 = 1338157) (by norm_num)
theorem B5151125 : Blo 1585491 5151125 := bbase (se 6 (by rfl) ⟨120729, by rfl⟩ : syracuseStep 5151125 = 241459) (by norm_num)
theorem B10164629 : Blo 1585491 10164629 := bbase (se 6 (by rfl) ⟨238233, by rfl⟩ : syracuseStep 10164629 = 476467) (by norm_num)
theorem B1784245 : Blo 1585491 1784245 := bbase (se 5 (by rfl) ⟨83636, by rfl⟩ : syracuseStep 1784245 = 167273) (by norm_num)
theorem B3570101 : Blo 1585491 3570101 := bbase (se 5 (by rfl) ⟨167348, by rfl⟩ : syracuseStep 3570101 = 334697) (by norm_num)
theorem B2677205 : Blo 1585491 2677205 := bbase (se 7 (by rfl) ⟨31373, by rfl⟩ : syracuseStep 2677205 = 62747) (by norm_num)
theorem B5355989 : Blo 1585491 5355989 := bbase (se 7 (by rfl) ⟨62765, by rfl⟩ : syracuseStep 5355989 = 125531) (by norm_num)
theorem B1784281 : Blo 1585491 1784281 := bbase (se 2 (by rfl) ⟨669105, by rfl⟩ : syracuseStep 1784281 = 1338211) (by norm_num)
theorem B8026613 : Blo 1585491 8026613 := bbase (se 5 (by rfl) ⟨376247, by rfl⟩ : syracuseStep 8026613 = 752495) (by norm_num)
theorem B3013109 : Blo 1585491 3013109 := bbase (se 5 (by rfl) ⟨141239, by rfl⟩ : syracuseStep 3013109 = 282479) (by norm_num)
theorem B1784317 : Blo 1585491 1784317 := bbase (se 3 (by rfl) ⟨334559, by rfl⟩ : syracuseStep 1784317 = 669119) (by norm_num)
theorem B3570173 : Blo 1585491 3570173 := bbase (se 3 (by rfl) ⟨669407, by rfl⟩ : syracuseStep 3570173 = 1338815) (by norm_num)
theorem B2857477 : Blo 1585491 2857477 := bbase (se 4 (by rfl) ⟨267888, by rfl⟩ : syracuseStep 2857477 = 535777) (by norm_num)
theorem B11434517 : Blo 1585491 11434517 := bbase (se 6 (by rfl) ⟨267996, by rfl⟩ : syracuseStep 11434517 = 535993) (by norm_num)
theorem B1784353 : Blo 1585491 1784353 := bbase (se 2 (by rfl) ⟨669132, by rfl⟩ : syracuseStep 1784353 = 1338265) (by norm_num)
theorem B3390005 : Blo 1585491 3390005 := bbase (se 5 (by rfl) ⟨158906, by rfl⟩ : syracuseStep 3390005 = 317813) (by norm_num)
theorem B1784389 : Blo 1585491 1784389 := bbase (se 4 (by rfl) ⟨167286, by rfl⟩ : syracuseStep 1784389 = 334573) (by norm_num)
theorem B3570245 : Blo 1585491 3570245 := bbase (se 4 (by rfl) ⟨334710, by rfl⟩ : syracuseStep 3570245 = 669421) (by norm_num)
theorem B2677333 : Blo 1585491 2677333 := bbase (se 8 (by rfl) ⟨15687, by rfl⟩ : syracuseStep 2677333 = 31375) (by norm_num)
theorem B1784425 : Blo 1585491 1784425 := bbase (se 2 (by rfl) ⟨669159, by rfl⟩ : syracuseStep 1784425 = 1338319) (by norm_num)
theorem B2259581 : Blo 1585491 2259581 := bbase (se 3 (by rfl) ⟨423671, by rfl⟩ : syracuseStep 2259581 = 847343) (by norm_num)
theorem B1784461 : Blo 1585491 1784461 := bbase (se 3 (by rfl) ⟨334586, by rfl⟩ : syracuseStep 1784461 = 669173) (by norm_num)
theorem B3570317 : Blo 1585491 3570317 := bbase (se 3 (by rfl) ⟨669434, by rfl⟩ : syracuseStep 3570317 = 1338869) (by norm_num)
theorem B1694353 : Blo 1585491 1694353 := bbase (se 2 (by rfl) ⟨635382, by rfl⟩ : syracuseStep 1694353 = 1270765) (by norm_num)
theorem B2857621 : Blo 1585491 2857621 := bbase (se 6 (by rfl) ⟨66975, by rfl⟩ : syracuseStep 2857621 = 133951) (by norm_num)
theorem B2677421 : Blo 1585491 2677421 := bbase (se 3 (by rfl) ⟨502016, by rfl⟩ : syracuseStep 2677421 = 1004033) (by norm_num)
theorem B1784497 : Blo 1585491 1784497 := bbase (se 2 (by rfl) ⟨669186, by rfl⟩ : syracuseStep 1784497 = 1338373) (by norm_num)
theorem B1784533 : Blo 1585491 1784533 := bbase (se 7 (by rfl) ⟨20912, by rfl⟩ : syracuseStep 1784533 = 41825) (by norm_num)
theorem B3570389 : Blo 1585491 3570389 := bbase (se 7 (by rfl) ⟨41840, by rfl⟩ : syracuseStep 3570389 = 83681) (by norm_num)
theorem B1784569 : Blo 1585491 1784569 := bbase (se 2 (by rfl) ⟨669213, by rfl⟩ : syracuseStep 1784569 = 1338427) (by norm_num)
theorem B1694477 : Blo 1585491 1694477 := bbase (se 3 (by rfl) ⟨317714, by rfl⟩ : syracuseStep 1694477 = 635429) (by norm_num)
theorem B3914525 : Blo 1585491 3914525 := bbase (se 3 (by rfl) ⟨733973, by rfl⟩ : syracuseStep 3914525 = 1467947) (by norm_num)
theorem B1784605 : Blo 1585491 1784605 := bbase (se 3 (by rfl) ⟨334613, by rfl⟩ : syracuseStep 1784605 = 669227) (by norm_num)
theorem B3570461 : Blo 1585491 3570461 := bbase (se 3 (by rfl) ⟨669461, by rfl⟩ : syracuseStep 3570461 = 1338923) (by norm_num)
theorem B2677549 : Blo 1585491 2677549 := bbase (se 3 (by rfl) ⟨502040, by rfl⟩ : syracuseStep 2677549 = 1004081) (by norm_num)
theorem B1784641 : Blo 1585491 1784641 := bbase (se 2 (by rfl) ⟨669240, by rfl⟩ : syracuseStep 1784641 = 1338481) (by norm_num)
theorem B1784677 : Blo 1585491 1784677 := bbase (se 4 (by rfl) ⟨167313, by rfl⟩ : syracuseStep 1784677 = 334627) (by norm_num)
theorem B3570533 : Blo 1585491 3570533 := bbase (se 4 (by rfl) ⟨334737, by rfl⟩ : syracuseStep 3570533 = 669475) (by norm_num)
theorem B2857837 : Blo 1585491 2857837 := bbase (se 3 (by rfl) ⟨535844, by rfl⟩ : syracuseStep 2857837 = 1071689) (by norm_num)
theorem B11598709 : Blo 1585491 11598709 := bbase (se 5 (by rfl) ⟨543689, by rfl⟩ : syracuseStep 11598709 = 1087379) (by norm_num)
theorem B2677637 : Blo 1585491 2677637 := bbase (se 4 (by rfl) ⟨251028, by rfl⟩ : syracuseStep 2677637 = 502057) (by norm_num)
theorem B5356421 : Blo 1585491 5356421 := bbase (se 4 (by rfl) ⟨502164, by rfl⟩ : syracuseStep 5356421 = 1004329) (by norm_num)
theorem B1784713 : Blo 1585491 1784713 := bbase (se 2 (by rfl) ⟨669267, by rfl⟩ : syracuseStep 1784713 = 1338535) (by norm_num)
theorem B1784749 : Blo 1585491 1784749 := bbase (se 3 (by rfl) ⟨334640, by rfl⟩ : syracuseStep 1784749 = 669281) (by norm_num)
theorem B3570605 : Blo 1585491 3570605 := bbase (se 3 (by rfl) ⟨669488, by rfl⟩ : syracuseStep 3570605 = 1338977) (by norm_num)
theorem B6020021 : Blo 1585491 6020021 := bbase (se 5 (by rfl) ⟨282188, by rfl⟩ : syracuseStep 6020021 = 564377) (by norm_num)
theorem B1784785 : Blo 1585491 1784785 := bbase (se 2 (by rfl) ⟨669294, by rfl⟩ : syracuseStep 1784785 = 1338589) (by norm_num)
theorem B1784821 : Blo 1585491 1784821 := bbase (se 5 (by rfl) ⟨83663, by rfl⟩ : syracuseStep 1784821 = 167327) (by norm_num)
theorem B12049397 : Blo 1585491 12049397 := bbase (se 5 (by rfl) ⟨564815, by rfl⟩ : syracuseStep 12049397 = 1129631) (by norm_num)
theorem B3570677 : Blo 1585491 3570677 := bbase (se 5 (by rfl) ⟨167375, by rfl⟩ : syracuseStep 3570677 = 334751) (by norm_num)
theorem B2677765 : Blo 1585491 2677765 := bbase (se 4 (by rfl) ⟨251040, by rfl⟩ : syracuseStep 2677765 = 502081) (by norm_num)
theorem B2898949 : Blo 1585491 2898949 := bbase (se 4 (by rfl) ⟨271776, by rfl⟩ : syracuseStep 2898949 = 543553) (by norm_num)
theorem B1694729 : Blo 1585491 1694729 := bbase (se 2 (by rfl) ⟨635523, by rfl⟩ : syracuseStep 1694729 = 1271047) (by norm_num)
theorem B1784857 : Blo 1585491 1784857 := bbase (se 2 (by rfl) ⟨669321, by rfl⟩ : syracuseStep 1784857 = 1338643) (by norm_num)
theorem B1784893 : Blo 1585491 1784893 := bbase (se 3 (by rfl) ⟨334667, by rfl⟩ : syracuseStep 1784893 = 669335) (by norm_num)
theorem B3570749 : Blo 1585491 3570749 := bbase (se 3 (by rfl) ⟨669515, by rfl⟩ : syracuseStep 3570749 = 1339031) (by norm_num)
theorem B2677853 : Blo 1585491 2677853 := bbase (se 3 (by rfl) ⟨502097, by rfl⟩ : syracuseStep 2677853 = 1004195) (by norm_num)
theorem B1784929 : Blo 1585491 1784929 := bbase (se 2 (by rfl) ⟨669348, by rfl⟩ : syracuseStep 1784929 = 1338697) (by norm_num)
theorem B1784965 : Blo 1585491 1784965 := bbase (se 4 (by rfl) ⟨167340, by rfl⟩ : syracuseStep 1784965 = 334681) (by norm_num)
theorem B3570821 : Blo 1585491 3570821 := bbase (se 4 (by rfl) ⟨334764, by rfl⟩ : syracuseStep 3570821 = 669529) (by norm_num)
theorem B1785001 : Blo 1585491 1785001 := bbase (se 2 (by rfl) ⟨669375, by rfl⟩ : syracuseStep 1785001 = 1338751) (by norm_num)
theorem B3054773 : Blo 1585491 3054773 := bbase (se 5 (by rfl) ⟨143192, by rfl⟩ : syracuseStep 3054773 = 286385) (by norm_num)
theorem B1785037 : Blo 1585491 1785037 := bbase (se 3 (by rfl) ⟨334694, by rfl⟩ : syracuseStep 1785037 = 669389) (by norm_num)
theorem B3570893 : Blo 1585491 3570893 := bbase (se 3 (by rfl) ⟨669542, by rfl⟩ : syracuseStep 3570893 = 1339085) (by norm_num)
theorem B2677981 : Blo 1585491 2677981 := bbase (se 3 (by rfl) ⟨502121, by rfl⟩ : syracuseStep 2677981 = 1004243) (by norm_num)
theorem B1785073 : Blo 1585491 1785073 := bbase (se 2 (by rfl) ⟨669402, by rfl⟩ : syracuseStep 1785073 = 1338805) (by norm_num)
theorem B1834249 : Blo 1585491 1834249 := bbase (se 2 (by rfl) ⟨687843, by rfl⟩ : syracuseStep 1834249 = 1375687) (by norm_num)
theorem B1785109 : Blo 1585491 1785109 := bbase (se 6 (by rfl) ⟨41838, by rfl⟩ : syracuseStep 1785109 = 83677) (by norm_num)
theorem B3570965 : Blo 1585491 3570965 := bbase (se 6 (by rfl) ⟨83694, by rfl⟩ : syracuseStep 3570965 = 167389) (by norm_num)
theorem B3915037 : Blo 1585491 3915037 := bbase (se 3 (by rfl) ⟨734069, by rfl⟩ : syracuseStep 3915037 = 1468139) (by norm_num)
theorem B2678069 : Blo 1585491 2678069 := bbase (se 5 (by rfl) ⟨125534, by rfl⟩ : syracuseStep 2678069 = 251069) (by norm_num)
theorem B5356853 : Blo 1585491 5356853 := bbase (se 5 (by rfl) ⟨251102, by rfl⟩ : syracuseStep 5356853 = 502205) (by norm_num)
theorem B1785145 : Blo 1585491 1785145 := bbase (se 2 (by rfl) ⟨669429, by rfl⟩ : syracuseStep 1785145 = 1338859) (by norm_num)
theorem B13557077 : Blo 1585491 13557077 := bbase (se 11 (by rfl) ⟨9929, by rfl⟩ : syracuseStep 13557077 = 19859) (by norm_num)
theorem B1785181 : Blo 1585491 1785181 := bbase (se 3 (by rfl) ⟨334721, by rfl⟩ : syracuseStep 1785181 = 669443) (by norm_num)
theorem B3571037 : Blo 1585491 3571037 := bbase (se 3 (by rfl) ⟨669569, by rfl⟩ : syracuseStep 3571037 = 1339139) (by norm_num)
theorem B8035685 : Blo 1585491 8035685 := bbase (se 4 (by rfl) ⟨753345, by rfl⟩ : syracuseStep 8035685 = 1506691) (by norm_num)
theorem B1785217 : Blo 1585491 1785217 := bbase (se 2 (by rfl) ⟨669456, by rfl⟩ : syracuseStep 1785217 = 1338913) (by norm_num)
theorem B12041621 : Blo 1585491 12041621 := bbase (se 6 (by rfl) ⟨282225, by rfl⟩ : syracuseStep 12041621 = 564451) (by norm_num)
theorem B11435413 : Blo 1585491 11435413 := bbase (se 6 (by rfl) ⟨268017, by rfl⟩ : syracuseStep 11435413 = 536035) (by norm_num)
theorem B1785253 : Blo 1585491 1785253 := bbase (se 4 (by rfl) ⟨167367, by rfl⟩ : syracuseStep 1785253 = 334735) (by norm_num)
theorem B3571109 : Blo 1585491 3571109 := bbase (se 4 (by rfl) ⟨334791, by rfl⟩ : syracuseStep 3571109 = 669583) (by norm_num)
theorem B2678197 : Blo 1585491 2678197 := bbase (se 5 (by rfl) ⟨125540, by rfl⟩ : syracuseStep 2678197 = 251081) (by norm_num)
theorem B2858429 : Blo 1585491 2858429 := bbase (se 3 (by rfl) ⟨535955, by rfl⟩ : syracuseStep 2858429 = 1071911) (by norm_num)
theorem B4013509 : Blo 1585491 4013509 := bbase (se 4 (by rfl) ⟨376266, by rfl⟩ : syracuseStep 4013509 = 752533) (by norm_num)
theorem B1695173 : Blo 1585491 1695173 := bbase (se 4 (by rfl) ⟨158922, by rfl⟩ : syracuseStep 1695173 = 317845) (by norm_num)
theorem B1785289 : Blo 1585491 1785289 := bbase (se 2 (by rfl) ⟨669483, by rfl⟩ : syracuseStep 1785289 = 1338967) (by norm_num)
theorem B15244757 : Blo 1585491 15244757 := bbase (se 7 (by rfl) ⟨178649, by rfl⟩ : syracuseStep 15244757 = 357299) (by norm_num)
theorem B65158613 : Blo 1585491 65158613 := bbase (se 7 (by rfl) ⟨763577, by rfl⟩ : syracuseStep 65158613 = 1527155) (by norm_num)
theorem B1785325 : Blo 1585491 1785325 := bbase (se 3 (by rfl) ⟨334748, by rfl⟩ : syracuseStep 1785325 = 669497) (by norm_num)
theorem B3571181 : Blo 1585491 3571181 := bbase (se 3 (by rfl) ⟨669596, by rfl⟩ : syracuseStep 3571181 = 1339193) (by norm_num)
theorem B2678285 : Blo 1585491 2678285 := bbase (se 3 (by rfl) ⟨502178, by rfl⟩ : syracuseStep 2678285 = 1004357) (by norm_num)
theorem B1785361 : Blo 1585491 1785361 := bbase (se 2 (by rfl) ⟨669510, by rfl⟩ : syracuseStep 1785361 = 1339021) (by norm_num)
theorem B4013621 : Blo 1585491 4013621 := bbase (se 5 (by rfl) ⟨188138, by rfl⟩ : syracuseStep 4013621 = 376277) (by norm_num)
theorem B1785397 : Blo 1585491 1785397 := bbase (se 5 (by rfl) ⟨83690, by rfl⟩ : syracuseStep 1785397 = 167381) (by norm_num)
theorem B3571253 : Blo 1585491 3571253 := bbase (se 5 (by rfl) ⟨167402, by rfl⟩ : syracuseStep 3571253 = 334805) (by norm_num)
theorem B1785433 : Blo 1585491 1785433 := bbase (se 2 (by rfl) ⟨669537, by rfl⟩ : syracuseStep 1785433 = 1339075) (by norm_num)
theorem B1785469 : Blo 1585491 1785469 := bbase (se 3 (by rfl) ⟨334775, by rfl⟩ : syracuseStep 1785469 = 669551) (by norm_num)
theorem B3571325 : Blo 1585491 3571325 := bbase (se 3 (by rfl) ⟨669623, by rfl⟩ : syracuseStep 3571325 = 1339247) (by norm_num)
theorem B2678413 : Blo 1585491 2678413 := bbase (se 3 (by rfl) ⟨502202, by rfl⟩ : syracuseStep 2678413 = 1004405) (by norm_num)
theorem B2858645 : Blo 1585491 2858645 := bbase (se 6 (by rfl) ⟨66999, by rfl⟩ : syracuseStep 2858645 = 133999) (by norm_num)
theorem B3620501 : Blo 1585491 3620501 := bbase (se 6 (by rfl) ⟨84855, by rfl⟩ : syracuseStep 3620501 = 169711) (by norm_num)
theorem B2006689 : Blo 1585491 2006689 := bbase (se 2 (by rfl) ⟨752508, by rfl⟩ : syracuseStep 2006689 = 1505017) (by norm_num)
theorem B1785505 : Blo 1585491 1785505 := bbase (se 2 (by rfl) ⟨669564, by rfl⟩ : syracuseStep 1785505 = 1339129) (by norm_num)
theorem B1785541 : Blo 1585491 1785541 := bbase (se 4 (by rfl) ⟨167394, by rfl⟩ : syracuseStep 1785541 = 334789) (by norm_num)
theorem B3571397 : Blo 1585491 3571397 := bbase (se 4 (by rfl) ⟨334818, by rfl⟩ : syracuseStep 3571397 = 669637) (by norm_num)
theorem B2678501 : Blo 1585491 2678501 := bbase (se 4 (by rfl) ⟨251109, by rfl⟩ : syracuseStep 2678501 = 502219) (by norm_num)
theorem B5357285 : Blo 1585491 5357285 := bbase (se 4 (by rfl) ⟨502245, by rfl⟩ : syracuseStep 5357285 = 1004491) (by norm_num)
theorem B1785577 : Blo 1585491 1785577 := bbase (se 2 (by rfl) ⟨669591, by rfl⟩ : syracuseStep 1785577 = 1339183) (by norm_num)
theorem B4013813 : Blo 1585491 4013813 := bbase (se 5 (by rfl) ⟨188147, by rfl⟩ : syracuseStep 4013813 = 376295) (by norm_num)
theorem B16498421 : Blo 1585491 16498421 := bbase (se 5 (by rfl) ⟨773363, by rfl⟩ : syracuseStep 16498421 = 1546727) (by norm_num)
theorem B2006785 : Blo 1585491 2006785 := bbase (se 2 (by rfl) ⟨752544, by rfl⟩ : syracuseStep 2006785 = 1505089) (by norm_num)
theorem B8027909 : Blo 1585491 8027909 := bbase (se 4 (by rfl) ⟨752616, by rfl⟩ : syracuseStep 8027909 = 1505233) (by norm_num)
theorem B1785613 : Blo 1585491 1785613 := bbase (se 3 (by rfl) ⟨334802, by rfl⟩ : syracuseStep 1785613 = 669605) (by norm_num)
theorem B3571469 : Blo 1585491 3571469 := bbase (se 3 (by rfl) ⟨669650, by rfl⟩ : syracuseStep 3571469 = 1339301) (by norm_num)
theorem B1785649 : Blo 1585491 1785649 := bbase (se 2 (by rfl) ⟨669618, by rfl⟩ : syracuseStep 1785649 = 1339237) (by norm_num)
theorem B1785685 : Blo 1585491 1785685 := bbase (se 9 (by rfl) ⟨5231, by rfl⟩ : syracuseStep 1785685 = 10463) (by norm_num)
theorem B3571541 : Blo 1585491 3571541 := bbase (se 9 (by rfl) ⟨10463, by rfl⟩ : syracuseStep 3571541 = 20927) (by norm_num)
theorem B2678629 : Blo 1585491 2678629 := bbase (se 4 (by rfl) ⟨251121, by rfl⟩ : syracuseStep 2678629 = 502243) (by norm_num)
theorem B1785721 : Blo 1585491 1785721 := bbase (se 2 (by rfl) ⟨669645, by rfl⟩ : syracuseStep 1785721 = 1339291) (by norm_num)
theorem B1785757 : Blo 1585491 1785757 := bbase (se 3 (by rfl) ⟨334829, by rfl⟩ : syracuseStep 1785757 = 669659) (by norm_num)
theorem B3571613 : Blo 1585491 3571613 := bbase (se 3 (by rfl) ⟨669677, by rfl⟩ : syracuseStep 3571613 = 1339355) (by norm_num)
theorem B2006957 : Blo 1585491 2006957 := bbase (se 3 (by rfl) ⟨376304, by rfl⟩ : syracuseStep 2006957 = 752609) (by norm_num)
theorem B2858933 : Blo 1585491 2858933 := bbase (se 5 (by rfl) ⟨134012, by rfl⟩ : syracuseStep 2858933 = 268025) (by norm_num)
theorem B2678717 : Blo 1585491 2678717 := bbase (se 3 (by rfl) ⟨502259, by rfl⟩ : syracuseStep 2678717 = 1004519) (by norm_num)
theorem B1785793 : Blo 1585491 1785793 := bbase (se 2 (by rfl) ⟨669672, by rfl⟩ : syracuseStep 1785793 = 1339345) (by norm_num)
theorem B2007013 : Blo 1585491 2007013 := bbase (se 4 (by rfl) ⟨188157, by rfl⟩ : syracuseStep 2007013 = 376315) (by norm_num)
theorem B1785829 : Blo 1585491 1785829 := bbase (se 4 (by rfl) ⟨167421, by rfl⟩ : syracuseStep 1785829 = 334843) (by norm_num)
theorem B3571685 : Blo 1585491 3571685 := bbase (se 4 (by rfl) ⟨334845, by rfl⟩ : syracuseStep 3571685 = 669691) (by norm_num)
theorem B10878965 : Blo 1585491 10878965 := bbase (se 5 (by rfl) ⟨509951, by rfl⟩ : syracuseStep 10878965 = 1019903) (by norm_num)
theorem B7233571 : Blo 1585491 7233571 := bstep (se 1 (by rfl) ⟨5425178, by rfl⟩ : syracuseStep 7233571 = 10850357) B10850357
theorem B4890691 : Blo 1585491 4890691 := bstep (se 1 (by rfl) ⟨3668018, by rfl⟩ : syracuseStep 4890691 = 7336037) B7336037
theorem B3571793 : Blo 1585491 3571793 := bstep (se 2 (by rfl) ⟨1339422, by rfl⟩ : syracuseStep 3571793 = 2678845) B2678845
theorem B3571811 : Blo 1585491 3571811 := bstep (se 1 (by rfl) ⟨2678858, by rfl⟩ : syracuseStep 3571811 = 5357717) B5357717
theorem B8036657 : Blo 1585491 8036657 := bstep (se 2 (by rfl) ⟨3013746, by rfl⟩ : syracuseStep 8036657 = 6027493) B6027493
theorem B8028557 : Blo 1585491 8028557 := bstep (se 3 (by rfl) ⟨1505354, by rfl⟩ : syracuseStep 8028557 = 3010709) B3010709
theorem B5718413 : Blo 1585491 5718413 := bstep (se 3 (by rfl) ⟨1072202, by rfl⟩ : syracuseStep 5718413 = 2144405) B2144405
theorem B32579981 : Blo 1585491 32579981 := bstep (se 3 (by rfl) ⟨6108746, by rfl⟩ : syracuseStep 32579981 = 12217493) B12217493
theorem B4014481 : Blo 1585491 4014481 := bstep (se 2 (by rfl) ⟨1505430, by rfl⟩ : syracuseStep 4014481 = 3010861) B3010861
theorem B2007443 : Blo 1585491 2007443 := bstep (se 1 (by rfl) ⟨1505582, by rfl⟩ : syracuseStep 2007443 = 3011165) B3011165
theorem B6431267 : Blo 1585491 6431267 := bstep (se 1 (by rfl) ⟨4823450, by rfl⟩ : syracuseStep 6431267 = 9646901) B9646901
theorem B4014755 : Blo 1585491 4014755 := bstep (se 1 (by rfl) ⟨3011066, by rfl⟩ : syracuseStep 4014755 = 6022133) B6022133
theorem B3809969 : Blo 1585491 3809969 := bstep (se 2 (by rfl) ⟨1428738, by rfl⟩ : syracuseStep 3809969 = 2857477) B2857477
theorem B5079779 : Blo 1585491 5079779 := bstep (se 1 (by rfl) ⟨3809834, by rfl⟩ : syracuseStep 5079779 = 7619669) B7619669
theorem B9036593 : Blo 1585491 9036593 := bstep (se 2 (by rfl) ⟨3388722, by rfl⟩ : syracuseStep 9036593 = 6777445) B6777445
theorem B6021965 : Blo 1585491 6021965 := bstep (se 3 (by rfl) ⟨1129118, by rfl⟩ : syracuseStep 6021965 = 2258237) B2258237
theorem B4014947 : Blo 1585491 4014947 := bstep (se 1 (by rfl) ⟨3011210, by rfl⟩ : syracuseStep 4014947 = 6022421) B6022421
theorem B3810161 : Blo 1585491 3810161 := bstep (se 2 (by rfl) ⟨1428810, by rfl⟩ : syracuseStep 3810161 = 2857621) B2857621
theorem B12051341 : Blo 1585491 12051341 := bstep (se 3 (by rfl) ⟨2259626, by rfl⟩ : syracuseStep 12051341 = 4519253) B4519253
theorem B6104099 : Blo 1585491 6104099 := bstep (se 1 (by rfl) ⟨4578074, by rfl⟩ : syracuseStep 6104099 = 9156149) B9156149
theorem B13558853 : Blo 1585491 13558853 := bstep (se 4 (by rfl) ⟨1271142, by rfl⟩ : syracuseStep 13558853 = 2542285) B2542285
theorem B2008147 : Blo 1585491 2008147 := bstep (se 1 (by rfl) ⟨1506110, by rfl⟩ : syracuseStep 2008147 = 3012221) B3012221
theorem B3810449 : Blo 1585491 3810449 := bstep (se 2 (by rfl) ⟨1428918, by rfl⟩ : syracuseStep 3810449 = 2857837) B2857837
theorem B2008243 : Blo 1585491 2008243 := bstep (se 1 (by rfl) ⟨1506182, by rfl⟩ : syracuseStep 2008243 = 3012365) B3012365
theorem B9643205 : Blo 1585491 9643205 := bstep (se 4 (by rfl) ⟨904050, by rfl⟩ : syracuseStep 9643205 = 1808101) B1808101
theorem B4285955 : Blo 1585491 4285955 := bstep (se 1 (by rfl) ⟨3214466, by rfl⟩ : syracuseStep 4285955 = 6428933) B6428933
theorem B2541107 : Blo 1585491 2541107 := bstep (se 1 (by rfl) ⟨1905830, by rfl⟩ : syracuseStep 2541107 = 3811661) B3811661
theorem B3434083 : Blo 1585491 3434083 := bstep (se 1 (by rfl) ⟨2575562, by rfl⟩ : syracuseStep 3434083 = 5151125) B5151125
theorem B20334179 : Blo 1585491 20334179 := bstep (se 1 (by rfl) ⟨15250634, by rfl⟩ : syracuseStep 20334179 = 30501269) B30501269
theorem B5351075 : Blo 1585491 5351075 := bstep (se 1 (by rfl) ⟨4013306, by rfl⟩ : syracuseStep 5351075 = 8026613) B8026613
theorem B2008739 : Blo 1585491 2008739 := bstep (se 1 (by rfl) ⟨1506554, by rfl⟩ : syracuseStep 2008739 = 3013109) B3013109
theorem B1607347 : Blo 1585491 1607347 := bstep (se 1 (by rfl) ⟨1205510, by rfl⟩ : syracuseStep 1607347 = 2411021) B2411021
theorem B2541235 : Blo 1585491 2541235 := bstep (se 1 (by rfl) ⟨1905926, by rfl⟩ : syracuseStep 2541235 = 3811853) B3811853
theorem B5220049 : Blo 1585491 5220049 := bstep (se 2 (by rfl) ⟨1957518, by rfl⟩ : syracuseStep 5220049 = 3915037) B3915037
theorem B4015889 : Blo 1585491 4015889 := bstep (se 2 (by rfl) ⟨1505958, by rfl⟩ : syracuseStep 4015889 = 3011917) B3011917
theorem B4015939 : Blo 1585491 4015939 := bstep (se 1 (by rfl) ⟨3011954, by rfl⟩ : syracuseStep 4015939 = 6023909) B6023909
theorem B15247217 : Blo 1585491 15247217 := bstep (se 2 (by rfl) ⟨5717706, by rfl⟩ : syracuseStep 15247217 = 11435413) B11435413
theorem B5425069 : Blo 1585491 5425069 := bstep (se 3 (by rfl) ⟨1017200, by rfl⟩ : syracuseStep 5425069 = 2034401) B2034401
theorem B5351345 : Blo 1585491 5351345 := bstep (se 2 (by rfl) ⟨2006754, by rfl⟩ : syracuseStep 5351345 = 4013509) B4013509
theorem B4016081 : Blo 1585491 4016081 := bstep (se 2 (by rfl) ⟨1506030, by rfl⟩ : syracuseStep 4016081 = 3012061) B3012061
theorem B19294193 : Blo 1585491 19294193 := bstep (se 2 (by rfl) ⟨7235322, by rfl⟩ : syracuseStep 19294193 = 14470645) B14470645
theorem B2541619 : Blo 1585491 2541619 := bstep (se 1 (by rfl) ⟨1906214, by rfl⟩ : syracuseStep 2541619 = 3812429) B3812429
theorem B10438733 : Blo 1585491 10438733 := bstep (se 3 (by rfl) ⟨1957262, by rfl⟩ : syracuseStep 10438733 = 3914525) B3914525
theorem B9038051 : Blo 1585491 9038051 := bstep (se 1 (by rfl) ⟨6778538, by rfl⟩ : syracuseStep 9038051 = 13557077) B13557077
theorem B4516145 : Blo 1585491 4516145 := bstep (se 2 (by rfl) ⟨1693554, by rfl⟩ : syracuseStep 4516145 = 3387109) B3387109
theorem B5081393 : Blo 1585491 5081393 := bstep (se 2 (by rfl) ⟨1905522, by rfl⟩ : syracuseStep 5081393 = 3811045) B3811045
theorem B2541875 : Blo 1585491 2541875 := bstep (se 1 (by rfl) ⟨1906406, by rfl⟩ : syracuseStep 2541875 = 3812813) B3812813
theorem B9029987 : Blo 1585491 9029987 := bstep (se 1 (by rfl) ⟨6772490, by rfl⟩ : syracuseStep 9029987 = 13544981) B13544981
theorem B4286897 : Blo 1585491 4286897 := bstep (se 2 (by rfl) ⟨1607586, by rfl⟩ : syracuseStep 4286897 = 3215173) B3215173
theorem B11430341 : Blo 1585491 11430341 := bstep (se 4 (by rfl) ⟨1071594, by rfl⟩ : syracuseStep 11430341 = 2143189) B2143189
theorem B5351885 : Blo 1585491 5351885 := bstep (se 3 (by rfl) ⟨1003478, by rfl⟩ : syracuseStep 5351885 = 2006957) B2006957
theorem B4516337 : Blo 1585491 4516337 := bstep (se 2 (by rfl) ⟨1693626, by rfl⟩ : syracuseStep 4516337 = 3387253) B3387253
theorem B2378243 : Blo 1585491 2378243 := bstep (se 1 (by rfl) ⟨1783682, by rfl⟩ : syracuseStep 2378243 = 3567365) B3567365
theorem B5351939 : Blo 1585491 5351939 := bstep (se 1 (by rfl) ⟨4013954, by rfl⟩ : syracuseStep 5351939 = 8027909) B8027909
theorem B2378273 : Blo 1585491 2378273 := bstep (se 2 (by rfl) ⟨891852, by rfl⟩ : syracuseStep 2378273 = 1783705) B1783705
theorem B2378291 : Blo 1585491 2378291 := bstep (se 1 (by rfl) ⟨1783718, by rfl⟩ : syracuseStep 2378291 = 3567437) B3567437
theorem B2378321 : Blo 1585491 2378321 := bstep (se 2 (by rfl) ⟨891870, by rfl⟩ : syracuseStep 2378321 = 1783741) B1783741
theorem B2378339 : Blo 1585491 2378339 := bstep (se 1 (by rfl) ⟨1783754, by rfl⟩ : syracuseStep 2378339 = 3567509) B3567509
theorem B2378369 : Blo 1585491 2378369 := bstep (se 2 (by rfl) ⟨891888, by rfl⟩ : syracuseStep 2378369 = 1783777) B1783777
theorem B2378387 : Blo 1585491 2378387 := bstep (se 1 (by rfl) ⟨1783790, by rfl⟩ : syracuseStep 2378387 = 3567581) B3567581
theorem B7252643 : Blo 1585491 7252643 := bstep (se 1 (by rfl) ⟨5439482, by rfl⟩ : syracuseStep 7252643 = 10878965) B10878965
theorem B2378417 : Blo 1585491 2378417 := bstep (se 2 (by rfl) ⟨891906, by rfl⟩ : syracuseStep 2378417 = 1783813) B1783813
theorem B2378435 : Blo 1585491 2378435 := bstep (se 1 (by rfl) ⟨1783826, by rfl⟩ : syracuseStep 2378435 = 3567653) B3567653
theorem B2378465 : Blo 1585491 2378465 := bstep (se 2 (by rfl) ⟨891924, by rfl⟩ : syracuseStep 2378465 = 1783849) B1783849
theorem B7621361 : Blo 1585491 7621361 := bstep (se 2 (by rfl) ⟨2858010, by rfl⟩ : syracuseStep 7621361 = 5716021) B5716021
theorem B2378483 : Blo 1585491 2378483 := bstep (se 1 (by rfl) ⟨1783862, by rfl⟩ : syracuseStep 2378483 = 3567725) B3567725
theorem B2542337 : Blo 1585491 2542337 := bstep (se 2 (by rfl) ⟨953376, by rfl⟩ : syracuseStep 2542337 = 1906753) B1906753
theorem B2378513 : Blo 1585491 2378513 := bstep (se 2 (by rfl) ⟨891942, by rfl⟩ : syracuseStep 2378513 = 1783885) B1783885
theorem B5352209 : Blo 1585491 5352209 := bstep (se 2 (by rfl) ⟨2007078, by rfl⟩ : syracuseStep 5352209 = 4014157) B4014157
theorem B2378531 : Blo 1585491 2378531 := bstep (se 1 (by rfl) ⟨1783898, by rfl⟩ : syracuseStep 2378531 = 3567797) B3567797
theorem B2378561 : Blo 1585491 2378561 := bstep (se 2 (by rfl) ⟨891960, by rfl⟩ : syracuseStep 2378561 = 1783921) B1783921
theorem B2378579 : Blo 1585491 2378579 := bstep (se 1 (by rfl) ⟨1783934, by rfl⟩ : syracuseStep 2378579 = 3567869) B3567869
theorem B2542433 : Blo 1585491 2542433 := bstep (se 2 (by rfl) ⟨953412, by rfl⟩ : syracuseStep 2542433 = 1906825) B1906825
theorem B2378609 : Blo 1585491 2378609 := bstep (se 2 (by rfl) ⟨891978, by rfl⟩ : syracuseStep 2378609 = 1783957) B1783957
theorem B2542465 : Blo 1585491 2542465 := bstep (se 2 (by rfl) ⟨953424, by rfl⟩ : syracuseStep 2542465 = 1906849) B1906849
theorem B2378627 : Blo 1585491 2378627 := bstep (se 1 (by rfl) ⟨1783970, by rfl⟩ : syracuseStep 2378627 = 3567941) B3567941
theorem B6024077 : Blo 1585491 6024077 := bstep (se 3 (by rfl) ⟨1129514, by rfl⟩ : syracuseStep 6024077 = 2259029) B2259029
theorem B4582289 : Blo 1585491 4582289 := bstep (se 2 (by rfl) ⟨1718358, by rfl⟩ : syracuseStep 4582289 = 3436717) B3436717
theorem B2378657 : Blo 1585491 2378657 := bstep (se 2 (by rfl) ⟨891996, by rfl⟩ : syracuseStep 2378657 = 1783993) B1783993
theorem B4017073 : Blo 1585491 4017073 := bstep (se 2 (by rfl) ⟨1506402, by rfl⟩ : syracuseStep 4017073 = 3012805) B3012805
theorem B2378675 : Blo 1585491 2378675 := bstep (se 1 (by rfl) ⟨1784006, by rfl⟩ : syracuseStep 2378675 = 3568013) B3568013
theorem B2378705 : Blo 1585491 2378705 := bstep (se 2 (by rfl) ⟨892014, by rfl⟩ : syracuseStep 2378705 = 1784029) B1784029
theorem B2378723 : Blo 1585491 2378723 := bstep (se 1 (by rfl) ⟨1784042, by rfl⟩ : syracuseStep 2378723 = 3568085) B3568085
theorem B2378753 : Blo 1585491 2378753 := bstep (se 2 (by rfl) ⟨892032, by rfl⟩ : syracuseStep 2378753 = 1784065) B1784065
theorem B2378771 : Blo 1585491 2378771 := bstep (se 1 (by rfl) ⟨1784078, by rfl⟩ : syracuseStep 2378771 = 3568157) B3568157
theorem B2378801 : Blo 1585491 2378801 := bstep (se 2 (by rfl) ⟨892050, by rfl⟩ : syracuseStep 2378801 = 1784101) B1784101
theorem B2378819 : Blo 1585491 2378819 := bstep (se 1 (by rfl) ⟨1784114, by rfl⟩ : syracuseStep 2378819 = 3568229) B3568229
theorem B2378849 : Blo 1585491 2378849 := bstep (se 2 (by rfl) ⟨892068, by rfl⟩ : syracuseStep 2378849 = 1784137) B1784137
theorem B5221475 : Blo 1585491 5221475 := bstep (se 1 (by rfl) ⟨3916106, by rfl⟩ : syracuseStep 5221475 = 7832213) B7832213
theorem B15248483 : Blo 1585491 15248483 := bstep (se 1 (by rfl) ⟨11436362, by rfl⟩ : syracuseStep 15248483 = 22872725) B22872725
theorem B2378867 : Blo 1585491 2378867 := bstep (se 1 (by rfl) ⟨1784150, by rfl⟩ : syracuseStep 2378867 = 3568301) B3568301
theorem B8146061 : Blo 1585491 8146061 := bstep (se 3 (by rfl) ⟨1527386, by rfl⟩ : syracuseStep 8146061 = 3054773) B3054773
theorem B2378897 : Blo 1585491 2378897 := bstep (se 2 (by rfl) ⟨892086, by rfl⟩ : syracuseStep 2378897 = 1784173) B1784173
theorem B2378915 : Blo 1585491 2378915 := bstep (se 1 (by rfl) ⟨1784186, by rfl⟩ : syracuseStep 2378915 = 3568373) B3568373
theorem B2378945 : Blo 1585491 2378945 := bstep (se 2 (by rfl) ⟨892104, by rfl⟩ : syracuseStep 2378945 = 1784209) B1784209
theorem B4017347 : Blo 1585491 4017347 := bstep (se 1 (by rfl) ⟨3013010, by rfl⟩ : syracuseStep 4017347 = 6026021) B6026021
theorem B12045509 : Blo 1585491 12045509 := bstep (se 4 (by rfl) ⟨1129266, by rfl⟩ : syracuseStep 12045509 = 2258533) B2258533
theorem B9039053 : Blo 1585491 9039053 := bstep (se 3 (by rfl) ⟨1694822, by rfl⟩ : syracuseStep 9039053 = 3389645) B3389645
theorem B2378963 : Blo 1585491 2378963 := bstep (se 1 (by rfl) ⟨1784222, by rfl⟩ : syracuseStep 2378963 = 3568445) B3568445
theorem B15461603 : Blo 1585491 15461603 := bstep (se 1 (by rfl) ⟨11596202, by rfl⟩ : syracuseStep 15461603 = 23192405) B23192405
theorem B2378993 : Blo 1585491 2378993 := bstep (se 2 (by rfl) ⟨892122, by rfl⟩ : syracuseStep 2378993 = 1784245) B1784245
theorem B8031473 : Blo 1585491 8031473 := bstep (se 2 (by rfl) ⟨3011802, by rfl⟩ : syracuseStep 8031473 = 6023605) B6023605
theorem B2379011 : Blo 1585491 2379011 := bstep (se 1 (by rfl) ⟨1784258, by rfl⟩ : syracuseStep 2379011 = 3568517) B3568517
theorem B2379041 : Blo 1585491 2379041 := bstep (se 2 (by rfl) ⟨892140, by rfl⟩ : syracuseStep 2379041 = 1784281) B1784281
theorem B5352749 : Blo 1585491 5352749 := bstep (se 3 (by rfl) ⟨1003640, by rfl⟩ : syracuseStep 5352749 = 2007281) B2007281
theorem B2379059 : Blo 1585491 2379059 := bstep (se 1 (by rfl) ⟨1784294, by rfl⟩ : syracuseStep 2379059 = 3568589) B3568589
theorem B2379089 : Blo 1585491 2379089 := bstep (se 2 (by rfl) ⟨892158, by rfl⟩ : syracuseStep 2379089 = 1784317) B1784317
theorem B5352803 : Blo 1585491 5352803 := bstep (se 1 (by rfl) ⟨4014602, by rfl⟩ : syracuseStep 5352803 = 8029205) B8029205
theorem B2379107 : Blo 1585491 2379107 := bstep (se 1 (by rfl) ⟨1784330, by rfl⟩ : syracuseStep 2379107 = 3568661) B3568661
theorem B2379137 : Blo 1585491 2379137 := bstep (se 2 (by rfl) ⟨892176, by rfl⟩ : syracuseStep 2379137 = 1784353) B1784353
theorem B4017539 : Blo 1585491 4017539 := bstep (se 1 (by rfl) ⟨3013154, by rfl⟩ : syracuseStep 4017539 = 6026309) B6026309
theorem B2379155 : Blo 1585491 2379155 := bstep (se 1 (by rfl) ⟨1784366, by rfl⟩ : syracuseStep 2379155 = 3568733) B3568733
theorem B2379185 : Blo 1585491 2379185 := bstep (se 2 (by rfl) ⟨892194, by rfl⟩ : syracuseStep 2379185 = 1784389) B1784389
theorem B2379203 : Blo 1585491 2379203 := bstep (se 1 (by rfl) ⟨1784402, by rfl⟩ : syracuseStep 2379203 = 3568805) B3568805
theorem B4517329 : Blo 1585491 4517329 := bstep (se 2 (by rfl) ⟨1693998, by rfl⟩ : syracuseStep 4517329 = 3387997) B3387997
theorem B2379233 : Blo 1585491 2379233 := bstep (se 2 (by rfl) ⟨892212, by rfl⟩ : syracuseStep 2379233 = 1784425) B1784425
theorem B2379251 : Blo 1585491 2379251 := bstep (se 1 (by rfl) ⟨1784438, by rfl⟩ : syracuseStep 2379251 = 3568877) B3568877
theorem B2379281 : Blo 1585491 2379281 := bstep (se 2 (by rfl) ⟨892230, by rfl⟩ : syracuseStep 2379281 = 1784461) B1784461
theorem B2379299 : Blo 1585491 2379299 := bstep (se 1 (by rfl) ⟨1784474, by rfl⟩ : syracuseStep 2379299 = 3568949) B3568949
theorem B6778403 : Blo 1585491 6778403 := bstep (se 1 (by rfl) ⟨5083802, by rfl⟩ : syracuseStep 6778403 = 10167605) B10167605
theorem B3386929 : Blo 1585491 3386929 := bstep (se 2 (by rfl) ⟨1270098, by rfl⟩ : syracuseStep 3386929 = 2540197) B2540197
theorem B2379329 : Blo 1585491 2379329 := bstep (se 2 (by rfl) ⟨892248, by rfl⟩ : syracuseStep 2379329 = 1784497) B1784497
theorem B6434381 : Blo 1585491 6434381 := bstep (se 3 (by rfl) ⟨1206446, by rfl⟩ : syracuseStep 6434381 = 2412893) B2412893
theorem B2379347 : Blo 1585491 2379347 := bstep (se 1 (by rfl) ⟨1784510, by rfl⟩ : syracuseStep 2379347 = 3569021) B3569021
theorem B7237219 : Blo 1585491 7237219 := bstep (se 1 (by rfl) ⟨5427914, by rfl⟩ : syracuseStep 7237219 = 10855829) B10855829
theorem B5353073 : Blo 1585491 5353073 := bstep (se 2 (by rfl) ⟨2007402, by rfl⟩ : syracuseStep 5353073 = 4014805) B4014805
theorem B2379377 : Blo 1585491 2379377 := bstep (se 2 (by rfl) ⟨892266, by rfl⟩ : syracuseStep 2379377 = 1784533) B1784533
theorem B2379395 : Blo 1585491 2379395 := bstep (se 1 (by rfl) ⟨1784546, by rfl⟩ : syracuseStep 2379395 = 3569093) B3569093
theorem B3010193 : Blo 1585491 3010193 := bstep (se 2 (by rfl) ⟨1128822, by rfl⟩ : syracuseStep 3010193 = 2257645) B2257645
theorem B2379425 : Blo 1585491 2379425 := bstep (se 2 (by rfl) ⟨892284, by rfl⟩ : syracuseStep 2379425 = 1784569) B1784569
theorem B6024881 : Blo 1585491 6024881 := bstep (se 2 (by rfl) ⟨2259330, by rfl⟩ : syracuseStep 6024881 = 4518661) B4518661
theorem B2379443 : Blo 1585491 2379443 := bstep (se 1 (by rfl) ⟨1784582, by rfl⟩ : syracuseStep 2379443 = 3569165) B3569165
theorem B2379473 : Blo 1585491 2379473 := bstep (se 2 (by rfl) ⟨892302, by rfl⟩ : syracuseStep 2379473 = 1784605) B1784605
theorem B2379491 : Blo 1585491 2379491 := bstep (se 1 (by rfl) ⟨1784618, by rfl⟩ : syracuseStep 2379491 = 3569237) B3569237
theorem B4517603 : Blo 1585491 4517603 := bstep (se 1 (by rfl) ⟨3388202, by rfl⟩ : syracuseStep 4517603 = 6776405) B6776405
theorem B12054257 : Blo 1585491 12054257 := bstep (se 2 (by rfl) ⟨4520346, by rfl⟩ : syracuseStep 12054257 = 9040693) B9040693
theorem B2379521 : Blo 1585491 2379521 := bstep (se 2 (by rfl) ⟨892320, by rfl⟩ : syracuseStep 2379521 = 1784641) B1784641
theorem B2379539 : Blo 1585491 2379539 := bstep (se 1 (by rfl) ⟨1784654, by rfl⟩ : syracuseStep 2379539 = 3569309) B3569309
theorem B3387185 : Blo 1585491 3387185 := bstep (se 2 (by rfl) ⟨1270194, by rfl⟩ : syracuseStep 3387185 = 2540389) B2540389
theorem B2379569 : Blo 1585491 2379569 := bstep (se 2 (by rfl) ⟨892338, by rfl⟩ : syracuseStep 2379569 = 1784677) B1784677
theorem B2379587 : Blo 1585491 2379587 := bstep (se 1 (by rfl) ⟨1784690, by rfl⟩ : syracuseStep 2379587 = 3569381) B3569381
theorem B2379617 : Blo 1585491 2379617 := bstep (se 2 (by rfl) ⟨892356, by rfl⟩ : syracuseStep 2379617 = 1784713) B1784713
theorem B3567473 : Blo 1585491 3567473 := bstep (se 2 (by rfl) ⟨1337802, by rfl⟩ : syracuseStep 3567473 = 2675605) B2675605
theorem B2379635 : Blo 1585491 2379635 := bstep (se 1 (by rfl) ⟨1784726, by rfl⟩ : syracuseStep 2379635 = 3569453) B3569453
theorem B3567491 : Blo 1585491 3567491 := bstep (se 1 (by rfl) ⟨2675618, by rfl⟩ : syracuseStep 3567491 = 5351237) B5351237
theorem B2379665 : Blo 1585491 2379665 := bstep (se 2 (by rfl) ⟨892374, by rfl⟩ : syracuseStep 2379665 = 1784749) B1784749
theorem B2379683 : Blo 1585491 2379683 := bstep (se 1 (by rfl) ⟨1784762, by rfl⟩ : syracuseStep 2379683 = 3569525) B3569525
theorem B4517795 : Blo 1585491 4517795 := bstep (se 1 (by rfl) ⟨3388346, by rfl⟩ : syracuseStep 4517795 = 6776693) B6776693
theorem B2379713 : Blo 1585491 2379713 := bstep (se 2 (by rfl) ⟨892392, by rfl⟩ : syracuseStep 2379713 = 1784785) B1784785
theorem B2379731 : Blo 1585491 2379731 := bstep (se 1 (by rfl) ⟨1784798, by rfl⟩ : syracuseStep 2379731 = 3569597) B3569597
theorem B2379761 : Blo 1585491 2379761 := bstep (se 2 (by rfl) ⟨892410, by rfl⟩ : syracuseStep 2379761 = 1784821) B1784821
theorem B5427203 : Blo 1585491 5427203 := bstep (se 1 (by rfl) ⟨4070402, by rfl⟩ : syracuseStep 5427203 = 8140805) B8140805
theorem B2379779 : Blo 1585491 2379779 := bstep (se 1 (by rfl) ⟨1784834, by rfl⟩ : syracuseStep 2379779 = 3569669) B3569669
theorem B2379809 : Blo 1585491 2379809 := bstep (se 2 (by rfl) ⟨892428, by rfl⟩ : syracuseStep 2379809 = 1784857) B1784857
theorem B2379827 : Blo 1585491 2379827 := bstep (se 1 (by rfl) ⟨1784870, by rfl⟩ : syracuseStep 2379827 = 3569741) B3569741
theorem B2379857 : Blo 1585491 2379857 := bstep (se 2 (by rfl) ⟨892446, by rfl⟩ : syracuseStep 2379857 = 1784893) B1784893
theorem B2379875 : Blo 1585491 2379875 := bstep (se 1 (by rfl) ⟨1784906, by rfl⟩ : syracuseStep 2379875 = 3569813) B3569813
theorem B2379905 : Blo 1585491 2379905 := bstep (se 2 (by rfl) ⟨892464, by rfl⟩ : syracuseStep 2379905 = 1784929) B1784929
theorem B5353613 : Blo 1585491 5353613 := bstep (se 3 (by rfl) ⟨1003802, by rfl⟩ : syracuseStep 5353613 = 2007605) B2007605
theorem B3567761 : Blo 1585491 3567761 := bstep (se 2 (by rfl) ⟨1337910, by rfl⟩ : syracuseStep 3567761 = 2675821) B2675821
theorem B2379923 : Blo 1585491 2379923 := bstep (se 1 (by rfl) ⟨1784942, by rfl⟩ : syracuseStep 2379923 = 3569885) B3569885
theorem B3567779 : Blo 1585491 3567779 := bstep (se 1 (by rfl) ⟨2675834, by rfl⟩ : syracuseStep 3567779 = 5351669) B5351669
theorem B2379953 : Blo 1585491 2379953 := bstep (se 2 (by rfl) ⟨892482, by rfl⟩ : syracuseStep 2379953 = 1784965) B1784965
theorem B5353667 : Blo 1585491 5353667 := bstep (se 1 (by rfl) ⟨4015250, by rfl⟩ : syracuseStep 5353667 = 8030501) B8030501
theorem B2379971 : Blo 1585491 2379971 := bstep (se 1 (by rfl) ⟨1784978, by rfl⟩ : syracuseStep 2379971 = 3569957) B3569957
theorem B2380001 : Blo 1585491 2380001 := bstep (se 2 (by rfl) ⟨892500, by rfl⟩ : syracuseStep 2380001 = 1785001) B1785001
theorem B132108515 : Blo 1585491 132108515 := bstep (se 1 (by rfl) ⟨99081386, by rfl⟩ : syracuseStep 132108515 = 198162773) B198162773
theorem B2380019 : Blo 1585491 2380019 := bstep (se 1 (by rfl) ⟨1785014, by rfl⟩ : syracuseStep 2380019 = 3570029) B3570029
theorem B10170629 : Blo 1585491 10170629 := bstep (se 4 (by rfl) ⟨953496, by rfl⟩ : syracuseStep 10170629 = 1906993) B1906993
theorem B2380049 : Blo 1585491 2380049 := bstep (se 2 (by rfl) ⟨892518, by rfl⟩ : syracuseStep 2380049 = 1785037) B1785037
theorem B2380067 : Blo 1585491 2380067 := bstep (se 1 (by rfl) ⟨1785050, by rfl⟩ : syracuseStep 2380067 = 3570101) B3570101
theorem B2380097 : Blo 1585491 2380097 := bstep (se 2 (by rfl) ⟨892536, by rfl⟩ : syracuseStep 2380097 = 1785073) B1785073
theorem B5083469 : Blo 1585491 5083469 := bstep (se 3 (by rfl) ⟨953150, by rfl⟩ : syracuseStep 5083469 = 1906301) B1906301
theorem B6025549 : Blo 1585491 6025549 := bstep (se 3 (by rfl) ⟨1129790, by rfl⟩ : syracuseStep 6025549 = 2259581) B2259581
theorem B1585491 : Blo 1585491 1585491 := bstep (se 1 (by rfl) ⟨1189118, by rfl⟩ : syracuseStep 1585491 = 2378237) B2378237
theorem B2380115 : Blo 1585491 2380115 := bstep (se 1 (by rfl) ⟨1785086, by rfl⟩ : syracuseStep 2380115 = 3570173) B3570173
theorem B1585507 : Blo 1585491 1585507 := bstep (se 1 (by rfl) ⟨1189130, by rfl⟩ : syracuseStep 1585507 = 2378261) B2378261
theorem B7623011 : Blo 1585491 7623011 := bstep (se 1 (by rfl) ⟨5717258, by rfl⟩ : syracuseStep 7623011 = 11434517) B11434517
theorem B2445665 : Blo 1585491 2445665 := bstep (se 2 (by rfl) ⟨917124, by rfl⟩ : syracuseStep 2445665 = 1834249) B1834249
theorem B2380145 : Blo 1585491 2380145 := bstep (se 2 (by rfl) ⟨892554, by rfl⟩ : syracuseStep 2380145 = 1785109) B1785109
theorem B1585523 : Blo 1585491 1585523 := bstep (se 1 (by rfl) ⟨1189142, by rfl⟩ : syracuseStep 1585523 = 2378285) B2378285
theorem B1585539 : Blo 1585491 1585539 := bstep (se 1 (by rfl) ⟨1189154, by rfl⟩ : syracuseStep 1585539 = 2378309) B2378309
theorem B2380163 : Blo 1585491 2380163 := bstep (se 1 (by rfl) ⟨1785122, by rfl⟩ : syracuseStep 2380163 = 3570245) B3570245
theorem B1585555 : Blo 1585491 1585555 := bstep (se 1 (by rfl) ⟨1189166, by rfl⟩ : syracuseStep 1585555 = 2378333) B2378333
theorem B2380193 : Blo 1585491 2380193 := bstep (se 2 (by rfl) ⟨892572, by rfl⟩ : syracuseStep 2380193 = 1785145) B1785145
theorem B1585571 : Blo 1585491 1585571 := bstep (se 1 (by rfl) ⟨1189178, by rfl⟩ : syracuseStep 1585571 = 2378357) B2378357
theorem B3568049 : Blo 1585491 3568049 := bstep (se 2 (by rfl) ⟨1338018, by rfl⟩ : syracuseStep 3568049 = 2676037) B2676037
theorem B1585587 : Blo 1585491 1585587 := bstep (se 1 (by rfl) ⟨1189190, by rfl⟩ : syracuseStep 1585587 = 2378381) B2378381
theorem B2380211 : Blo 1585491 2380211 := bstep (se 1 (by rfl) ⟨1785158, by rfl⟩ : syracuseStep 2380211 = 3570317) B3570317
theorem B1585603 : Blo 1585491 1585603 := bstep (se 1 (by rfl) ⟨1189202, by rfl⟩ : syracuseStep 1585603 = 2378405) B2378405
theorem B3568067 : Blo 1585491 3568067 := bstep (se 1 (by rfl) ⟨2676050, by rfl⟩ : syracuseStep 3568067 = 5352101) B5352101
theorem B5353937 : Blo 1585491 5353937 := bstep (se 2 (by rfl) ⟨2007726, by rfl⟩ : syracuseStep 5353937 = 4015453) B4015453
theorem B1585619 : Blo 1585491 1585619 := bstep (se 1 (by rfl) ⟨1189214, by rfl⟩ : syracuseStep 1585619 = 2378429) B2378429
theorem B2380241 : Blo 1585491 2380241 := bstep (se 2 (by rfl) ⟨892590, by rfl⟩ : syracuseStep 2380241 = 1785181) B1785181
theorem B1585635 : Blo 1585491 1585635 := bstep (se 1 (by rfl) ⟨1189226, by rfl⟩ : syracuseStep 1585635 = 2378453) B2378453
theorem B2380259 : Blo 1585491 2380259 := bstep (se 1 (by rfl) ⟨1785194, by rfl⟩ : syracuseStep 2380259 = 3570389) B3570389
theorem B1585651 : Blo 1585491 1585651 := bstep (se 1 (by rfl) ⟨1189238, by rfl⟩ : syracuseStep 1585651 = 2378477) B2378477
theorem B2380289 : Blo 1585491 2380289 := bstep (se 2 (by rfl) ⟨892608, by rfl⟩ : syracuseStep 2380289 = 1785217) B1785217
theorem B1585667 : Blo 1585491 1585667 := bstep (se 1 (by rfl) ⟨1189250, by rfl⟩ : syracuseStep 1585667 = 2378501) B2378501
theorem B3011089 : Blo 1585491 3011089 := bstep (se 2 (by rfl) ⟨1129158, by rfl⟩ : syracuseStep 3011089 = 2258317) B2258317
theorem B1585683 : Blo 1585491 1585683 := bstep (se 1 (by rfl) ⟨1189262, by rfl⟩ : syracuseStep 1585683 = 2378525) B2378525
theorem B2380307 : Blo 1585491 2380307 := bstep (se 1 (by rfl) ⟨1785230, by rfl⟩ : syracuseStep 2380307 = 3570461) B3570461
theorem B1585699 : Blo 1585491 1585699 := bstep (se 1 (by rfl) ⟨1189274, by rfl⟩ : syracuseStep 1585699 = 2378549) B2378549
theorem B2380337 : Blo 1585491 2380337 := bstep (se 2 (by rfl) ⟨892626, by rfl⟩ : syracuseStep 2380337 = 1785253) B1785253
theorem B1585715 : Blo 1585491 1585715 := bstep (se 1 (by rfl) ⟨1189286, by rfl⟩ : syracuseStep 1585715 = 2378573) B2378573
theorem B1585731 : Blo 1585491 1585731 := bstep (se 1 (by rfl) ⟨1189298, by rfl⟩ : syracuseStep 1585731 = 2378597) B2378597
theorem B2380355 : Blo 1585491 2380355 := bstep (se 1 (by rfl) ⟨1785266, by rfl⟩ : syracuseStep 2380355 = 3570533) B3570533
theorem B1585747 : Blo 1585491 1585747 := bstep (se 1 (by rfl) ⟨1189310, by rfl⟩ : syracuseStep 1585747 = 2378621) B2378621
theorem B2380385 : Blo 1585491 2380385 := bstep (se 2 (by rfl) ⟨892644, by rfl⟩ : syracuseStep 2380385 = 1785289) B1785289
theorem B1585763 : Blo 1585491 1585763 := bstep (se 1 (by rfl) ⟨1189322, by rfl⟩ : syracuseStep 1585763 = 2378645) B2378645
theorem B1585779 : Blo 1585491 1585779 := bstep (se 1 (by rfl) ⟨1189334, by rfl⟩ : syracuseStep 1585779 = 2378669) B2378669
theorem B2380403 : Blo 1585491 2380403 := bstep (se 1 (by rfl) ⟨1785302, by rfl⟩ : syracuseStep 2380403 = 3570605) B3570605
theorem B1585795 : Blo 1585491 1585795 := bstep (se 1 (by rfl) ⟨1189346, by rfl⟩ : syracuseStep 1585795 = 2378693) B2378693
theorem B2380433 : Blo 1585491 2380433 := bstep (se 2 (by rfl) ⟨892662, by rfl⟩ : syracuseStep 2380433 = 1785325) B1785325
theorem B1585811 : Blo 1585491 1585811 := bstep (se 1 (by rfl) ⟨1189358, by rfl⟩ : syracuseStep 1585811 = 2378717) B2378717
theorem B2257571 : Blo 1585491 2257571 := bstep (se 1 (by rfl) ⟨1693178, by rfl⟩ : syracuseStep 2257571 = 3386357) B3386357
theorem B1585827 : Blo 1585491 1585827 := bstep (se 1 (by rfl) ⟨1189370, by rfl⟩ : syracuseStep 1585827 = 2378741) B2378741
theorem B8032931 : Blo 1585491 8032931 := bstep (se 1 (by rfl) ⟨6024698, by rfl⟩ : syracuseStep 8032931 = 12049397) B12049397
theorem B2380451 : Blo 1585491 2380451 := bstep (se 1 (by rfl) ⟨1785338, by rfl⟩ : syracuseStep 2380451 = 3570677) B3570677
theorem B3011249 : Blo 1585491 3011249 := bstep (se 2 (by rfl) ⟨1129218, by rfl⟩ : syracuseStep 3011249 = 2258437) B2258437
theorem B1585843 : Blo 1585491 1585843 := bstep (se 1 (by rfl) ⟨1189382, by rfl⟩ : syracuseStep 1585843 = 2378765) B2378765
theorem B2380481 : Blo 1585491 2380481 := bstep (se 2 (by rfl) ⟨892680, by rfl⟩ : syracuseStep 2380481 = 1785361) B1785361
theorem B1585859 : Blo 1585491 1585859 := bstep (se 1 (by rfl) ⟨1189394, by rfl⟩ : syracuseStep 1585859 = 2378789) B2378789
theorem B4518605 : Blo 1585491 4518605 := bstep (se 3 (by rfl) ⟨847238, by rfl⟩ : syracuseStep 4518605 = 1694477) B1694477
theorem B3568337 : Blo 1585491 3568337 := bstep (se 2 (by rfl) ⟨1338126, by rfl⟩ : syracuseStep 3568337 = 2676253) B2676253
theorem B1585875 : Blo 1585491 1585875 := bstep (se 1 (by rfl) ⟨1189406, by rfl⟩ : syracuseStep 1585875 = 2378813) B2378813
theorem B2380499 : Blo 1585491 2380499 := bstep (se 1 (by rfl) ⟨1785374, by rfl⟩ : syracuseStep 2380499 = 3570749) B3570749
theorem B1585891 : Blo 1585491 1585891 := bstep (se 1 (by rfl) ⟨1189418, by rfl⟩ : syracuseStep 1585891 = 2378837) B2378837
theorem B3568355 : Blo 1585491 3568355 := bstep (se 1 (by rfl) ⟨2676266, by rfl⟩ : syracuseStep 3568355 = 5352533) B5352533
theorem B2380529 : Blo 1585491 2380529 := bstep (se 2 (by rfl) ⟨892698, by rfl⟩ : syracuseStep 2380529 = 1785397) B1785397
theorem B1585907 : Blo 1585491 1585907 := bstep (se 1 (by rfl) ⟨1189430, by rfl⟩ : syracuseStep 1585907 = 2378861) B2378861
theorem B1585923 : Blo 1585491 1585923 := bstep (se 1 (by rfl) ⟨1189442, by rfl⟩ : syracuseStep 1585923 = 2378885) B2378885
theorem B2380547 : Blo 1585491 2380547 := bstep (se 1 (by rfl) ⟨1785410, by rfl⟩ : syracuseStep 2380547 = 3570821) B3570821
theorem B1585939 : Blo 1585491 1585939 := bstep (se 1 (by rfl) ⟨1189454, by rfl⟩ : syracuseStep 1585939 = 2378909) B2378909
theorem B2380577 : Blo 1585491 2380577 := bstep (se 2 (by rfl) ⟨892716, by rfl⟩ : syracuseStep 2380577 = 1785433) B1785433
theorem B1585955 : Blo 1585491 1585955 := bstep (se 1 (by rfl) ⟨1189466, by rfl⟩ : syracuseStep 1585955 = 2378933) B2378933
theorem B1585971 : Blo 1585491 1585971 := bstep (se 1 (by rfl) ⟨1189478, by rfl⟩ : syracuseStep 1585971 = 2378957) B2378957
theorem B2380595 : Blo 1585491 2380595 := bstep (se 1 (by rfl) ⟨1785446, by rfl⟩ : syracuseStep 2380595 = 3570893) B3570893
theorem B1585987 : Blo 1585491 1585987 := bstep (se 1 (by rfl) ⟨1189490, by rfl⟩ : syracuseStep 1585987 = 2378981) B2378981
theorem B2380625 : Blo 1585491 2380625 := bstep (se 2 (by rfl) ⟨892734, by rfl⟩ : syracuseStep 2380625 = 1785469) B1785469
theorem B1586003 : Blo 1585491 1586003 := bstep (se 1 (by rfl) ⟨1189502, by rfl⟩ : syracuseStep 1586003 = 2379005) B2379005
theorem B1586019 : Blo 1585491 1586019 := bstep (se 1 (by rfl) ⟨1189514, by rfl⟩ : syracuseStep 1586019 = 2379029) B2379029
theorem B2380643 : Blo 1585491 2380643 := bstep (se 1 (by rfl) ⟨1785482, by rfl⟩ : syracuseStep 2380643 = 3570965) B3570965
theorem B1586035 : Blo 1585491 1586035 := bstep (se 1 (by rfl) ⟨1189526, by rfl⟩ : syracuseStep 1586035 = 2379053) B2379053
theorem B2675585 : Blo 1585491 2675585 := bstep (se 2 (by rfl) ⟨1003344, by rfl⟩ : syracuseStep 2675585 = 2006689) B2006689
theorem B1586051 : Blo 1585491 1586051 := bstep (se 1 (by rfl) ⟨1189538, by rfl⟩ : syracuseStep 1586051 = 2379077) B2379077
theorem B4518787 : Blo 1585491 4518787 := bstep (se 1 (by rfl) ⟨3389090, by rfl⟩ : syracuseStep 4518787 = 6778181) B6778181
theorem B2380673 : Blo 1585491 2380673 := bstep (se 2 (by rfl) ⟨892752, by rfl⟩ : syracuseStep 2380673 = 1785505) B1785505
theorem B1586067 : Blo 1585491 1586067 := bstep (se 1 (by rfl) ⟨1189550, by rfl⟩ : syracuseStep 1586067 = 2379101) B2379101
theorem B2380691 : Blo 1585491 2380691 := bstep (se 1 (by rfl) ⟨1785518, by rfl⟩ : syracuseStep 2380691 = 3571037) B3571037
theorem B1586083 : Blo 1585491 1586083 := bstep (se 1 (by rfl) ⟨1189562, by rfl⟩ : syracuseStep 1586083 = 2379125) B2379125
theorem B2380721 : Blo 1585491 2380721 := bstep (se 2 (by rfl) ⟨892770, by rfl⟩ : syracuseStep 2380721 = 1785541) B1785541
theorem B1586099 : Blo 1585491 1586099 := bstep (se 1 (by rfl) ⟨1189574, by rfl⟩ : syracuseStep 1586099 = 2379149) B2379149
theorem B1586115 : Blo 1585491 1586115 := bstep (se 1 (by rfl) ⟨1189586, by rfl⟩ : syracuseStep 1586115 = 2379173) B2379173
theorem B2380739 : Blo 1585491 2380739 := bstep (se 1 (by rfl) ⟨1785554, by rfl⟩ : syracuseStep 2380739 = 3571109) B3571109
theorem B1586131 : Blo 1585491 1586131 := bstep (se 1 (by rfl) ⟨1189598, by rfl⟩ : syracuseStep 1586131 = 2379197) B2379197
theorem B1905619 : Blo 1585491 1905619 := bstep (se 1 (by rfl) ⟨1429214, by rfl⟩ : syracuseStep 1905619 = 2858429) B2858429
theorem B2380769 : Blo 1585491 2380769 := bstep (se 2 (by rfl) ⟨892788, by rfl⟩ : syracuseStep 2380769 = 1785577) B1785577
theorem B1586147 : Blo 1585491 1586147 := bstep (se 1 (by rfl) ⟨1189610, by rfl⟩ : syracuseStep 1586147 = 2379221) B2379221
theorem B10163171 : Blo 1585491 10163171 := bstep (se 1 (by rfl) ⟨7622378, by rfl⟩ : syracuseStep 10163171 = 15244757) B15244757
theorem B43439075 : Blo 1585491 43439075 := bstep (se 1 (by rfl) ⟨32579306, by rfl⟩ : syracuseStep 43439075 = 65158613) B65158613
theorem B5354477 : Blo 1585491 5354477 := bstep (se 3 (by rfl) ⟨1003964, by rfl⟩ : syracuseStep 5354477 = 2007929) B2007929
theorem B3568625 : Blo 1585491 3568625 := bstep (se 2 (by rfl) ⟨1338234, by rfl⟩ : syracuseStep 3568625 = 2676469) B2676469
theorem B1586163 : Blo 1585491 1586163 := bstep (se 1 (by rfl) ⟨1189622, by rfl⟩ : syracuseStep 1586163 = 2379245) B2379245
theorem B2380787 : Blo 1585491 2380787 := bstep (se 1 (by rfl) ⟨1785590, by rfl⟩ : syracuseStep 2380787 = 3571181) B3571181
theorem B2675713 : Blo 1585491 2675713 := bstep (se 2 (by rfl) ⟨1003392, by rfl⟩ : syracuseStep 2675713 = 2006785) B2006785
theorem B3568643 : Blo 1585491 3568643 := bstep (se 1 (by rfl) ⟨2676482, by rfl⟩ : syracuseStep 3568643 = 5352965) B5352965
theorem B1586179 : Blo 1585491 1586179 := bstep (se 1 (by rfl) ⟨1189634, by rfl⟩ : syracuseStep 1586179 = 2379269) B2379269
theorem B2380817 : Blo 1585491 2380817 := bstep (se 2 (by rfl) ⟨892806, by rfl⟩ : syracuseStep 2380817 = 1785613) B1785613
theorem B1586195 : Blo 1585491 1586195 := bstep (se 1 (by rfl) ⟨1189646, by rfl⟩ : syracuseStep 1586195 = 2379293) B2379293
theorem B2675747 : Blo 1585491 2675747 := bstep (se 1 (by rfl) ⟨2006810, by rfl⟩ : syracuseStep 2675747 = 4013621) B4013621
theorem B1586211 : Blo 1585491 1586211 := bstep (se 1 (by rfl) ⟨1189658, by rfl⟩ : syracuseStep 1586211 = 2379317) B2379317
theorem B3863587 : Blo 1585491 3863587 := bstep (se 1 (by rfl) ⟨2897690, by rfl⟩ : syracuseStep 3863587 = 5795381) B5795381
theorem B5354531 : Blo 1585491 5354531 := bstep (se 1 (by rfl) ⟨4015898, by rfl⟩ : syracuseStep 5354531 = 8031797) B8031797
theorem B2380835 : Blo 1585491 2380835 := bstep (se 1 (by rfl) ⟨1785626, by rfl⟩ : syracuseStep 2380835 = 3571253) B3571253
theorem B6435875 : Blo 1585491 6435875 := bstep (se 1 (by rfl) ⟨4826906, by rfl⟩ : syracuseStep 6435875 = 9653813) B9653813
theorem B1586227 : Blo 1585491 1586227 := bstep (se 1 (by rfl) ⟨1189670, by rfl⟩ : syracuseStep 1586227 = 2379341) B2379341
theorem B2380865 : Blo 1585491 2380865 := bstep (se 2 (by rfl) ⟨892824, by rfl⟩ : syracuseStep 2380865 = 1785649) B1785649
theorem B1586243 : Blo 1585491 1586243 := bstep (se 1 (by rfl) ⟨1189682, by rfl⟩ : syracuseStep 1586243 = 2379365) B2379365
theorem B3011651 : Blo 1585491 3011651 := bstep (se 1 (by rfl) ⟨2258738, by rfl⟩ : syracuseStep 3011651 = 4517477) B4517477
theorem B3388483 : Blo 1585491 3388483 := bstep (se 1 (by rfl) ⟨2541362, by rfl⟩ : syracuseStep 3388483 = 5082725) B5082725
theorem B1586259 : Blo 1585491 1586259 := bstep (se 1 (by rfl) ⟨1189694, by rfl⟩ : syracuseStep 1586259 = 2379389) B2379389
theorem B2380883 : Blo 1585491 2380883 := bstep (se 1 (by rfl) ⟨1785662, by rfl⟩ : syracuseStep 2380883 = 3571325) B3571325
theorem B1586275 : Blo 1585491 1586275 := bstep (se 1 (by rfl) ⟨1189706, by rfl⟩ : syracuseStep 1586275 = 2379413) B2379413
theorem B1905763 : Blo 1585491 1905763 := bstep (se 1 (by rfl) ⟨1429322, by rfl⟩ : syracuseStep 1905763 = 2858645) B2858645
theorem B6026339 : Blo 1585491 6026339 := bstep (se 1 (by rfl) ⟨4519754, by rfl⟩ : syracuseStep 6026339 = 9039509) B9039509
theorem B2413667 : Blo 1585491 2413667 := bstep (se 1 (by rfl) ⟨1810250, by rfl⟩ : syracuseStep 2413667 = 3620501) B3620501
theorem B48829553 : Blo 1585491 48829553 := bstep (se 2 (by rfl) ⟨18311082, by rfl⟩ : syracuseStep 48829553 = 36622165) B36622165
theorem B2380913 : Blo 1585491 2380913 := bstep (se 2 (by rfl) ⟨892842, by rfl⟩ : syracuseStep 2380913 = 1785685) B1785685
theorem B1586291 : Blo 1585491 1586291 := bstep (se 1 (by rfl) ⟨1189718, by rfl⟩ : syracuseStep 1586291 = 2379437) B2379437
theorem B1586307 : Blo 1585491 1586307 := bstep (se 1 (by rfl) ⟨1189730, by rfl⟩ : syracuseStep 1586307 = 2379461) B2379461
theorem B2380931 : Blo 1585491 2380931 := bstep (se 1 (by rfl) ⟨1785698, by rfl⟩ : syracuseStep 2380931 = 3571397) B3571397
theorem B7623821 : Blo 1585491 7623821 := bstep (se 3 (by rfl) ⟨1429466, by rfl⟩ : syracuseStep 7623821 = 2858933) B2858933
theorem B1586323 : Blo 1585491 1586323 := bstep (se 1 (by rfl) ⟨1189742, by rfl⟩ : syracuseStep 1586323 = 2379485) B2379485
theorem B2380961 : Blo 1585491 2380961 := bstep (se 2 (by rfl) ⟨892860, by rfl⟩ : syracuseStep 2380961 = 1785721) B1785721
theorem B2675875 : Blo 1585491 2675875 := bstep (se 1 (by rfl) ⟨2006906, by rfl⟩ : syracuseStep 2675875 = 4013813) B4013813
theorem B10998947 : Blo 1585491 10998947 := bstep (se 1 (by rfl) ⟨8249210, by rfl⟩ : syracuseStep 10998947 = 16498421) B16498421
theorem B1586339 : Blo 1585491 1586339 := bstep (se 1 (by rfl) ⟨1189754, by rfl⟩ : syracuseStep 1586339 = 2379509) B2379509
theorem B1586355 : Blo 1585491 1586355 := bstep (se 1 (by rfl) ⟨1189766, by rfl⟩ : syracuseStep 1586355 = 2379533) B2379533
theorem B2380979 : Blo 1585491 2380979 := bstep (se 1 (by rfl) ⟨1785734, by rfl⟩ : syracuseStep 2380979 = 3571469) B3571469
theorem B1586371 : Blo 1585491 1586371 := bstep (se 1 (by rfl) ⟨1189778, by rfl⟩ : syracuseStep 1586371 = 2379557) B2379557
theorem B17151173 : Blo 1585491 17151173 := bstep (se 4 (by rfl) ⟨1607922, by rfl⟩ : syracuseStep 17151173 = 3215845) B3215845
theorem B5084365 : Blo 1585491 5084365 := bstep (se 3 (by rfl) ⟨953318, by rfl⟩ : syracuseStep 5084365 = 1906637) B1906637
theorem B2381009 : Blo 1585491 2381009 := bstep (se 2 (by rfl) ⟨892878, by rfl⟩ : syracuseStep 2381009 = 1785757) B1785757
theorem B1586387 : Blo 1585491 1586387 := bstep (se 1 (by rfl) ⟨1189790, by rfl⟩ : syracuseStep 1586387 = 2379581) B2379581
theorem B1586403 : Blo 1585491 1586403 := bstep (se 1 (by rfl) ⟨1189802, by rfl⟩ : syracuseStep 1586403 = 2379605) B2379605
theorem B2381027 : Blo 1585491 2381027 := bstep (se 1 (by rfl) ⟨1785770, by rfl⟩ : syracuseStep 2381027 = 3571541) B3571541
theorem B6780145 : Blo 1585491 6780145 := bstep (se 2 (by rfl) ⟨2542554, by rfl⟩ : syracuseStep 6780145 = 5085109) B5085109
theorem B1586419 : Blo 1585491 1586419 := bstep (se 1 (by rfl) ⟨1189814, by rfl⟩ : syracuseStep 1586419 = 2379629) B2379629
theorem B2381057 : Blo 1585491 2381057 := bstep (se 2 (by rfl) ⟨892896, by rfl⟩ : syracuseStep 2381057 = 1785793) B1785793
theorem B1586435 : Blo 1585491 1586435 := bstep (se 1 (by rfl) ⟨1189826, by rfl⟩ : syracuseStep 1586435 = 2379653) B2379653
theorem B3568913 : Blo 1585491 3568913 := bstep (se 2 (by rfl) ⟨1338342, by rfl⟩ : syracuseStep 3568913 = 2676685) B2676685
theorem B1586451 : Blo 1585491 1586451 := bstep (se 1 (by rfl) ⟨1189838, by rfl⟩ : syracuseStep 1586451 = 2379677) B2379677
theorem B2381075 : Blo 1585491 2381075 := bstep (se 1 (by rfl) ⟨1785806, by rfl⟩ : syracuseStep 2381075 = 3571613) B3571613
theorem B2258209 : Blo 1585491 2258209 := bstep (se 2 (by rfl) ⟨846828, by rfl⟩ : syracuseStep 2258209 = 1693657) B1693657
theorem B3568931 : Blo 1585491 3568931 := bstep (se 1 (by rfl) ⟨2676698, by rfl⟩ : syracuseStep 3568931 = 5353397) B5353397
theorem B1586467 : Blo 1585491 1586467 := bstep (se 1 (by rfl) ⟨1189850, by rfl⟩ : syracuseStep 1586467 = 2379701) B2379701
theorem B2676017 : Blo 1585491 2676017 := bstep (se 2 (by rfl) ⟨1003506, by rfl⟩ : syracuseStep 2676017 = 2007013) B2007013
theorem B5354801 : Blo 1585491 5354801 := bstep (se 2 (by rfl) ⟨2008050, by rfl⟩ : syracuseStep 5354801 = 4016101) B4016101
theorem B1586483 : Blo 1585491 1586483 := bstep (se 1 (by rfl) ⟨1189862, by rfl⟩ : syracuseStep 1586483 = 2379725) B2379725
theorem B2381105 : Blo 1585491 2381105 := bstep (se 2 (by rfl) ⟨892914, by rfl⟩ : syracuseStep 2381105 = 1785829) B1785829
theorem B1586499 : Blo 1585491 1586499 := bstep (se 1 (by rfl) ⟨1189874, by rfl⟩ : syracuseStep 1586499 = 2379749) B2379749
theorem B2381123 : Blo 1585491 2381123 := bstep (se 1 (by rfl) ⟨1785842, by rfl⟩ : syracuseStep 2381123 = 3571685) B3571685
theorem B4289869 : Blo 1585491 4289869 := bstep (se 3 (by rfl) ⟨804350, by rfl⟩ : syracuseStep 4289869 = 1608701) B1608701
theorem B1586515 : Blo 1585491 1586515 := bstep (se 1 (by rfl) ⟨1189886, by rfl⟩ : syracuseStep 1586515 = 2379773) B2379773
theorem B2381153 : Blo 1585491 2381153 := bstep (se 2 (by rfl) ⟨892932, by rfl⟩ : syracuseStep 2381153 = 1785865) B1785865
theorem B1586531 : Blo 1585491 1586531 := bstep (se 1 (by rfl) ⟨1189898, by rfl⟩ : syracuseStep 1586531 = 2379797) B2379797
theorem B4519277 : Blo 1585491 4519277 := bstep (se 3 (by rfl) ⟨847364, by rfl⟩ : syracuseStep 4519277 = 1694729) B1694729
theorem B1586547 : Blo 1585491 1586547 := bstep (se 1 (by rfl) ⟨1189910, by rfl⟩ : syracuseStep 1586547 = 2379821) B2379821
theorem B2381171 : Blo 1585491 2381171 := bstep (se 1 (by rfl) ⟨1785878, by rfl⟩ : syracuseStep 2381171 = 3571757) B3571757
theorem B1586563 : Blo 1585491 1586563 := bstep (se 1 (by rfl) ⟨1189922, by rfl⟩ : syracuseStep 1586563 = 2379845) B2379845
theorem B3388817 : Blo 1585491 3388817 := bstep (se 2 (by rfl) ⟨1270806, by rfl⟩ : syracuseStep 3388817 = 2541613) B2541613
theorem B2381201 : Blo 1585491 2381201 := bstep (se 2 (by rfl) ⟨892950, by rfl⟩ : syracuseStep 2381201 = 1785901) B1785901
theorem B1586579 : Blo 1585491 1586579 := bstep (se 1 (by rfl) ⟨1189934, by rfl⟩ : syracuseStep 1586579 = 2379869) B2379869
theorem B1586595 : Blo 1585491 1586595 := bstep (se 1 (by rfl) ⟨1189946, by rfl⟩ : syracuseStep 1586595 = 2379893) B2379893
theorem B2381219 : Blo 1585491 2381219 := bstep (se 1 (by rfl) ⟨1785914, by rfl⟩ : syracuseStep 2381219 = 3571829) B3571829
theorem B2676145 : Blo 1585491 2676145 := bstep (se 2 (by rfl) ⟨1003554, by rfl⟩ : syracuseStep 2676145 = 2007109) B2007109
theorem B1586611 : Blo 1585491 1586611 := bstep (se 1 (by rfl) ⟨1189958, by rfl⟩ : syracuseStep 1586611 = 2379917) B2379917
theorem B1586627 : Blo 1585491 1586627 := bstep (se 1 (by rfl) ⟨1189970, by rfl⟩ : syracuseStep 1586627 = 2379941) B2379941
theorem B8033741 : Blo 1585491 8033741 := bstep (se 3 (by rfl) ⟨1506326, by rfl⟩ : syracuseStep 8033741 = 3012653) B3012653
theorem B2676179 : Blo 1585491 2676179 := bstep (se 1 (by rfl) ⟨2007134, by rfl⟩ : syracuseStep 2676179 = 4014269) B4014269
theorem B1586643 : Blo 1585491 1586643 := bstep (se 1 (by rfl) ⟨1189982, by rfl⟩ : syracuseStep 1586643 = 2379965) B2379965
theorem B1586659 : Blo 1585491 1586659 := bstep (se 1 (by rfl) ⟨1189994, by rfl⟩ : syracuseStep 1586659 = 2379989) B2379989
theorem B1586675 : Blo 1585491 1586675 := bstep (se 1 (by rfl) ⟨1190006, by rfl⟩ : syracuseStep 1586675 = 2380013) B2380013
theorem B1586691 : Blo 1585491 1586691 := bstep (se 1 (by rfl) ⟨1190018, by rfl⟩ : syracuseStep 1586691 = 2380037) B2380037
theorem B9033221 : Blo 1585491 9033221 := bstep (se 4 (by rfl) ⟨846864, by rfl⟩ : syracuseStep 9033221 = 1693729) B1693729
theorem B1586707 : Blo 1585491 1586707 := bstep (se 1 (by rfl) ⟨1190030, by rfl⟩ : syracuseStep 1586707 = 2380061) B2380061
theorem B1586723 : Blo 1585491 1586723 := bstep (se 1 (by rfl) ⟨1190042, by rfl⟩ : syracuseStep 1586723 = 2380085) B2380085
theorem B10851889 : Blo 1585491 10851889 := bstep (se 2 (by rfl) ⟨4069458, by rfl⟩ : syracuseStep 10851889 = 8138917) B8138917
theorem B3569201 : Blo 1585491 3569201 := bstep (se 2 (by rfl) ⟨1338450, by rfl⟩ : syracuseStep 3569201 = 2676901) B2676901
theorem B1586739 : Blo 1585491 1586739 := bstep (se 1 (by rfl) ⟨1190054, by rfl⟩ : syracuseStep 1586739 = 2380109) B2380109
theorem B3569219 : Blo 1585491 3569219 := bstep (se 1 (by rfl) ⟨2676914, by rfl⟩ : syracuseStep 3569219 = 5353829) B5353829
theorem B1586755 : Blo 1585491 1586755 := bstep (se 1 (by rfl) ⟨1190066, by rfl⟩ : syracuseStep 1586755 = 2380133) B2380133
theorem B2676307 : Blo 1585491 2676307 := bstep (se 1 (by rfl) ⟨2007230, by rfl⟩ : syracuseStep 2676307 = 4014461) B4014461
theorem B1586771 : Blo 1585491 1586771 := bstep (se 1 (by rfl) ⟨1190078, by rfl⟩ : syracuseStep 1586771 = 2380157) B2380157
theorem B1586787 : Blo 1585491 1586787 := bstep (se 1 (by rfl) ⟨1190090, by rfl⟩ : syracuseStep 1586787 = 2380181) B2380181
theorem B2258545 : Blo 1585491 2258545 := bstep (se 2 (by rfl) ⟨846954, by rfl⟩ : syracuseStep 2258545 = 1693909) B1693909
theorem B1586803 : Blo 1585491 1586803 := bstep (se 1 (by rfl) ⟨1190102, by rfl⟩ : syracuseStep 1586803 = 2380205) B2380205
theorem B1693315 : Blo 1585491 1693315 := bstep (se 1 (by rfl) ⟨1269986, by rfl⟩ : syracuseStep 1693315 = 2539973) B2539973
theorem B1586819 : Blo 1585491 1586819 := bstep (se 1 (by rfl) ⟨1190114, by rfl⟩ : syracuseStep 1586819 = 2380229) B2380229
theorem B1586835 : Blo 1585491 1586835 := bstep (se 1 (by rfl) ⟨1190126, by rfl⟩ : syracuseStep 1586835 = 2380253) B2380253
theorem B1586851 : Blo 1585491 1586851 := bstep (se 1 (by rfl) ⟨1190138, by rfl⟩ : syracuseStep 1586851 = 2380277) B2380277
theorem B1586867 : Blo 1585491 1586867 := bstep (se 1 (by rfl) ⟨1190150, by rfl⟩ : syracuseStep 1586867 = 2380301) B2380301
theorem B1586883 : Blo 1585491 1586883 := bstep (se 1 (by rfl) ⟨1190162, by rfl⟩ : syracuseStep 1586883 = 2380325) B2380325
theorem B1586899 : Blo 1585491 1586899 := bstep (se 1 (by rfl) ⟨1190174, by rfl⟩ : syracuseStep 1586899 = 2380349) B2380349
theorem B2676449 : Blo 1585491 2676449 := bstep (se 2 (by rfl) ⟨1003668, by rfl⟩ : syracuseStep 2676449 = 2007337) B2007337
theorem B1586915 : Blo 1585491 1586915 := bstep (se 1 (by rfl) ⟨1190186, by rfl⟩ : syracuseStep 1586915 = 2380373) B2380373
theorem B6026993 : Blo 1585491 6026993 := bstep (se 2 (by rfl) ⟨2260122, by rfl⟩ : syracuseStep 6026993 = 4520245) B4520245
theorem B1586931 : Blo 1585491 1586931 := bstep (se 1 (by rfl) ⟨1190198, by rfl⟩ : syracuseStep 1586931 = 2380397) B2380397
theorem B1586947 : Blo 1585491 1586947 := bstep (se 1 (by rfl) ⟨1190210, by rfl⟩ : syracuseStep 1586947 = 2380421) B2380421
theorem B1586963 : Blo 1585491 1586963 := bstep (se 1 (by rfl) ⟨1190222, by rfl⟩ : syracuseStep 1586963 = 2380445) B2380445
theorem B1586979 : Blo 1585491 1586979 := bstep (se 1 (by rfl) ⟨1190234, by rfl⟩ : syracuseStep 1586979 = 2380469) B2380469
theorem B6108977 : Blo 1585491 6108977 := bstep (se 2 (by rfl) ⟨2290866, by rfl⟩ : syracuseStep 6108977 = 4581733) B4581733
theorem B1586995 : Blo 1585491 1586995 := bstep (se 1 (by rfl) ⟨1190246, by rfl⟩ : syracuseStep 1586995 = 2380493) B2380493
theorem B1587011 : Blo 1585491 1587011 := bstep (se 1 (by rfl) ⟨1190258, by rfl⟩ : syracuseStep 1587011 = 2380517) B2380517
theorem B5355341 : Blo 1585491 5355341 := bstep (se 3 (by rfl) ⟨1004126, by rfl⟩ : syracuseStep 5355341 = 2008253) B2008253
theorem B3569489 : Blo 1585491 3569489 := bstep (se 2 (by rfl) ⟨1338558, by rfl⟩ : syracuseStep 3569489 = 2677117) B2677117
theorem B1587027 : Blo 1585491 1587027 := bstep (se 1 (by rfl) ⟨1190270, by rfl⟩ : syracuseStep 1587027 = 2380541) B2380541
theorem B2676577 : Blo 1585491 2676577 := bstep (se 2 (by rfl) ⟨1003716, by rfl⟩ : syracuseStep 2676577 = 2007433) B2007433
theorem B3569507 : Blo 1585491 3569507 := bstep (se 1 (by rfl) ⟨2677130, by rfl⟩ : syracuseStep 3569507 = 5354261) B5354261
theorem B1587043 : Blo 1585491 1587043 := bstep (se 1 (by rfl) ⟨1190282, by rfl⟩ : syracuseStep 1587043 = 2380565) B2380565
theorem B1587059 : Blo 1585491 1587059 := bstep (se 1 (by rfl) ⟨1190294, by rfl⟩ : syracuseStep 1587059 = 2380589) B2380589
theorem B2676611 : Blo 1585491 2676611 := bstep (se 1 (by rfl) ⟨2007458, by rfl⟩ : syracuseStep 2676611 = 4014917) B4014917
theorem B5355395 : Blo 1585491 5355395 := bstep (se 1 (by rfl) ⟨4016546, by rfl⟩ : syracuseStep 5355395 = 8033093) B8033093
theorem B1587075 : Blo 1585491 1587075 := bstep (se 1 (by rfl) ⟨1190306, by rfl⟩ : syracuseStep 1587075 = 2380613) B2380613
theorem B1587091 : Blo 1585491 1587091 := bstep (se 1 (by rfl) ⟨1190318, by rfl⟩ : syracuseStep 1587091 = 2380637) B2380637
theorem B1587107 : Blo 1585491 1587107 := bstep (se 1 (by rfl) ⟨1190330, by rfl⟩ : syracuseStep 1587107 = 2380661) B2380661
theorem B1587123 : Blo 1585491 1587123 := bstep (se 1 (by rfl) ⟨1190342, by rfl⟩ : syracuseStep 1587123 = 2380685) B2380685
theorem B3012547 : Blo 1585491 3012547 := bstep (se 1 (by rfl) ⟨2259410, by rfl⟩ : syracuseStep 3012547 = 4518821) B4518821
theorem B1587139 : Blo 1585491 1587139 := bstep (se 1 (by rfl) ⟨1190354, by rfl⟩ : syracuseStep 1587139 = 2380709) B2380709
theorem B9033677 : Blo 1585491 9033677 := bstep (se 3 (by rfl) ⟨1693814, by rfl⟩ : syracuseStep 9033677 = 3387629) B3387629
theorem B6870989 : Blo 1585491 6870989 := bstep (se 3 (by rfl) ⟨1288310, by rfl⟩ : syracuseStep 6870989 = 2576621) B2576621
theorem B1587155 : Blo 1585491 1587155 := bstep (se 1 (by rfl) ⟨1190366, by rfl⟩ : syracuseStep 1587155 = 2380733) B2380733
theorem B12040163 : Blo 1585491 12040163 := bstep (se 1 (by rfl) ⟨9030122, by rfl⟩ : syracuseStep 12040163 = 18060245) B18060245
theorem B6191075 : Blo 1585491 6191075 := bstep (se 1 (by rfl) ⟨4643306, by rfl⟩ : syracuseStep 6191075 = 9286613) B9286613
theorem B1587171 : Blo 1585491 1587171 := bstep (se 1 (by rfl) ⟨1190378, by rfl⟩ : syracuseStep 1587171 = 2380757) B2380757
theorem B1783795 : Blo 1585491 1783795 := bstep (se 1 (by rfl) ⟨1337846, by rfl⟩ : syracuseStep 1783795 = 2675693) B2675693
theorem B1587187 : Blo 1585491 1587187 := bstep (se 1 (by rfl) ⟨1190390, by rfl⟩ : syracuseStep 1587187 = 2380781) B2380781
theorem B2676739 : Blo 1585491 2676739 := bstep (se 1 (by rfl) ⟨2007554, by rfl⟩ : syracuseStep 2676739 = 4015109) B4015109
theorem B1587203 : Blo 1585491 1587203 := bstep (se 1 (by rfl) ⟨1190402, by rfl⟩ : syracuseStep 1587203 = 2380805) B2380805
theorem B1587219 : Blo 1585491 1587219 := bstep (se 1 (by rfl) ⟨1190414, by rfl⟩ : syracuseStep 1587219 = 2380829) B2380829
theorem B1587235 : Blo 1585491 1587235 := bstep (se 1 (by rfl) ⟨1190426, by rfl⟩ : syracuseStep 1587235 = 2380853) B2380853
theorem B1587251 : Blo 1585491 1587251 := bstep (se 1 (by rfl) ⟨1190438, by rfl⟩ : syracuseStep 1587251 = 2380877) B2380877
theorem B1587267 : Blo 1585491 1587267 := bstep (se 1 (by rfl) ⟨1190450, by rfl⟩ : syracuseStep 1587267 = 2380901) B2380901
theorem B1587283 : Blo 1585491 1587283 := bstep (se 1 (by rfl) ⟨1190462, by rfl⟩ : syracuseStep 1587283 = 2380925) B2380925
theorem B3012707 : Blo 1585491 3012707 := bstep (se 1 (by rfl) ⟨2259530, by rfl⟩ : syracuseStep 3012707 = 4519061) B4519061
theorem B1906787 : Blo 1585491 1906787 := bstep (se 1 (by rfl) ⟨1430090, by rfl⟩ : syracuseStep 1906787 = 2860181) B2860181
theorem B1587299 : Blo 1585491 1587299 := bstep (se 1 (by rfl) ⟨1190474, by rfl⟩ : syracuseStep 1587299 = 2380949) B2380949
theorem B3569777 : Blo 1585491 3569777 := bstep (se 2 (by rfl) ⟨1338666, by rfl⟩ : syracuseStep 3569777 = 2677333) B2677333
theorem B1587315 : Blo 1585491 1587315 := bstep (se 1 (by rfl) ⟨1190486, by rfl⟩ : syracuseStep 1587315 = 2380973) B2380973
theorem B1783939 : Blo 1585491 1783939 := bstep (se 1 (by rfl) ⟨1337954, by rfl⟩ : syracuseStep 1783939 = 2675909) B2675909
theorem B3569795 : Blo 1585491 3569795 := bstep (se 1 (by rfl) ⟨2677346, by rfl⟩ : syracuseStep 3569795 = 5354693) B5354693
theorem B1587331 : Blo 1585491 1587331 := bstep (se 1 (by rfl) ⟨1190498, by rfl⟩ : syracuseStep 1587331 = 2380997) B2380997
theorem B2676881 : Blo 1585491 2676881 := bstep (se 2 (by rfl) ⟨1003830, by rfl⟩ : syracuseStep 2676881 = 2007661) B2007661
theorem B5355665 : Blo 1585491 5355665 := bstep (se 2 (by rfl) ⟨2008374, by rfl⟩ : syracuseStep 5355665 = 4016749) B4016749
theorem B1587347 : Blo 1585491 1587347 := bstep (se 1 (by rfl) ⟨1190510, by rfl⟩ : syracuseStep 1587347 = 2381021) B2381021
theorem B1587363 : Blo 1585491 1587363 := bstep (se 1 (by rfl) ⟨1190522, by rfl⟩ : syracuseStep 1587363 = 2381045) B2381045
theorem B1587379 : Blo 1585491 1587379 := bstep (se 1 (by rfl) ⟨1190534, by rfl⟩ : syracuseStep 1587379 = 2381069) B2381069
theorem B2259137 : Blo 1585491 2259137 := bstep (se 2 (by rfl) ⟨847176, by rfl⟩ : syracuseStep 2259137 = 1694353) B1694353
theorem B1587395 : Blo 1585491 1587395 := bstep (se 1 (by rfl) ⟨1190546, by rfl⟩ : syracuseStep 1587395 = 2381093) B2381093
theorem B4577485 : Blo 1585491 4577485 := bstep (se 3 (by rfl) ⟨858278, by rfl⟩ : syracuseStep 4577485 = 1716557) B1716557
theorem B1587411 : Blo 1585491 1587411 := bstep (se 1 (by rfl) ⟨1190558, by rfl⟩ : syracuseStep 1587411 = 2381117) B2381117
theorem B1587427 : Blo 1585491 1587427 := bstep (se 1 (by rfl) ⟨1190570, by rfl⟩ : syracuseStep 1587427 = 2381141) B2381141
theorem B1587443 : Blo 1585491 1587443 := bstep (se 1 (by rfl) ⟨1190582, by rfl⟩ : syracuseStep 1587443 = 2381165) B2381165
theorem B2144513 : Blo 1585491 2144513 := bstep (se 2 (by rfl) ⟨804192, by rfl⟩ : syracuseStep 2144513 = 1608385) B1608385
theorem B5085443 : Blo 1585491 5085443 := bstep (se 1 (by rfl) ⟨3814082, by rfl⟩ : syracuseStep 5085443 = 7628165) B7628165
theorem B1587459 : Blo 1585491 1587459 := bstep (se 1 (by rfl) ⟨1190594, by rfl⟩ : syracuseStep 1587459 = 2381189) B2381189
theorem B2677009 : Blo 1585491 2677009 := bstep (se 2 (by rfl) ⟨1003878, by rfl⟩ : syracuseStep 2677009 = 2007757) B2007757
theorem B1784083 : Blo 1585491 1784083 := bstep (se 1 (by rfl) ⟨1338062, by rfl⟩ : syracuseStep 1784083 = 2676125) B2676125
theorem B1587475 : Blo 1585491 1587475 := bstep (se 1 (by rfl) ⟨1190606, by rfl⟩ : syracuseStep 1587475 = 2381213) B2381213
theorem B1587491 : Blo 1585491 1587491 := bstep (se 1 (by rfl) ⟨1190618, by rfl⟩ : syracuseStep 1587491 = 2381237) B2381237
theorem B2677043 : Blo 1585491 2677043 := bstep (se 1 (by rfl) ⟨2007782, by rfl⟩ : syracuseStep 2677043 = 4015565) B4015565
theorem B40638833 : Blo 1585491 40638833 := bstep (se 2 (by rfl) ⟨15239562, by rfl⟩ : syracuseStep 40638833 = 30479125) B30479125
theorem B27105677 : Blo 1585491 27105677 := bstep (se 3 (by rfl) ⟨5082314, by rfl⟩ : syracuseStep 27105677 = 10164629) B10164629
theorem B2857361 : Blo 1585491 2857361 := bstep (se 2 (by rfl) ⟨1071510, by rfl⟩ : syracuseStep 2857361 = 2143021) B2143021
theorem B3570065 : Blo 1585491 3570065 := bstep (se 2 (by rfl) ⟨1338774, by rfl⟩ : syracuseStep 3570065 = 2677549) B2677549
theorem B1784227 : Blo 1585491 1784227 := bstep (se 1 (by rfl) ⟨1338170, by rfl⟩ : syracuseStep 1784227 = 2676341) B2676341
theorem B3570083 : Blo 1585491 3570083 := bstep (se 1 (by rfl) ⟨2677562, by rfl⟩ : syracuseStep 3570083 = 5355125) B5355125
theorem B2677171 : Blo 1585491 2677171 := bstep (se 1 (by rfl) ⟨2007878, by rfl⟩ : syracuseStep 2677171 = 4015757) B4015757
theorem B5716451 : Blo 1585491 5716451 := bstep (se 1 (by rfl) ⟨4287338, by rfl⟩ : syracuseStep 5716451 = 8574677) B8574677
theorem B15464945 : Blo 1585491 15464945 := bstep (se 2 (by rfl) ⟨5799354, by rfl⟩ : syracuseStep 15464945 = 11598709) B11598709
theorem B4520461 : Blo 1585491 4520461 := bstep (se 3 (by rfl) ⟨847586, by rfl⟩ : syracuseStep 4520461 = 1695173) B1695173
theorem B3389987 : Blo 1585491 3389987 := bstep (se 1 (by rfl) ⟨2542490, by rfl⟩ : syracuseStep 3389987 = 5084981) B5084981
theorem B1784371 : Blo 1585491 1784371 := bstep (se 1 (by rfl) ⟨1338278, by rfl⟩ : syracuseStep 1784371 = 2676557) B2676557
theorem B2677313 : Blo 1585491 2677313 := bstep (se 2 (by rfl) ⟨1003992, by rfl⟩ : syracuseStep 2677313 = 2007985) B2007985
theorem B5356205 : Blo 1585491 5356205 := bstep (se 3 (by rfl) ⟨1004288, by rfl⟩ : syracuseStep 5356205 = 2008577) B2008577
theorem B3570353 : Blo 1585491 3570353 := bstep (se 2 (by rfl) ⟨1338882, by rfl⟩ : syracuseStep 3570353 = 2677765) B2677765
theorem B3865265 : Blo 1585491 3865265 := bstep (se 2 (by rfl) ⟨1449474, by rfl⟩ : syracuseStep 3865265 = 2898949) B2898949
theorem B2677441 : Blo 1585491 2677441 := bstep (se 2 (by rfl) ⟨1004040, by rfl⟩ : syracuseStep 2677441 = 2008081) B2008081
theorem B1784515 : Blo 1585491 1784515 := bstep (se 1 (by rfl) ⟨1338386, by rfl⟩ : syracuseStep 1784515 = 2676773) B2676773
theorem B3570371 : Blo 1585491 3570371 := bstep (se 1 (by rfl) ⟨2677778, by rfl⟩ : syracuseStep 3570371 = 5355557) B5355557
theorem B2259667 : Blo 1585491 2259667 := bstep (se 1 (by rfl) ⟨1694750, by rfl⟩ : syracuseStep 2259667 = 3389501) B3389501
theorem B8575715 : Blo 1585491 8575715 := bstep (se 1 (by rfl) ⟨6431786, by rfl⟩ : syracuseStep 8575715 = 12863573) B12863573
theorem B2677475 : Blo 1585491 2677475 := bstep (se 1 (by rfl) ⟨2008106, by rfl⟩ : syracuseStep 2677475 = 4016213) B4016213
theorem B5356259 : Blo 1585491 5356259 := bstep (se 1 (by rfl) ⟨4017194, by rfl⟩ : syracuseStep 5356259 = 8034389) B8034389
theorem B1784659 : Blo 1585491 1784659 := bstep (se 1 (by rfl) ⟨1338494, by rfl⟩ : syracuseStep 1784659 = 2676989) B2676989
theorem B2677603 : Blo 1585491 2677603 := bstep (se 1 (by rfl) ⟨2008202, by rfl⟩ : syracuseStep 2677603 = 4016405) B4016405
theorem B3570641 : Blo 1585491 3570641 := bstep (se 2 (by rfl) ⟨1338990, by rfl⟩ : syracuseStep 3570641 = 2677981) B2677981
theorem B1784803 : Blo 1585491 1784803 := bstep (se 1 (by rfl) ⟨1338602, by rfl⟩ : syracuseStep 1784803 = 2677205) B2677205
theorem B3570659 : Blo 1585491 3570659 := bstep (se 1 (by rfl) ⟨2677994, by rfl⟩ : syracuseStep 3570659 = 5355989) B5355989
theorem B2677745 : Blo 1585491 2677745 := bstep (se 2 (by rfl) ⟨1004154, by rfl⟩ : syracuseStep 2677745 = 2008309) B2008309
theorem B5356529 : Blo 1585491 5356529 := bstep (se 2 (by rfl) ⟨2008698, by rfl⟩ : syracuseStep 5356529 = 4017397) B4017397
theorem B2145313 : Blo 1585491 2145313 := bstep (se 2 (by rfl) ⟨804492, by rfl⟩ : syracuseStep 2145313 = 1608985) B1608985
theorem B2260003 : Blo 1585491 2260003 := bstep (se 1 (by rfl) ⟨1695002, by rfl⟩ : syracuseStep 2260003 = 3390005) B3390005
theorem B10165297 : Blo 1585491 10165297 := bstep (se 2 (by rfl) ⟨3811986, by rfl⟩ : syracuseStep 10165297 = 7623973) B7623973
theorem B2677873 : Blo 1585491 2677873 := bstep (se 2 (by rfl) ⟨1004202, by rfl⟩ : syracuseStep 2677873 = 2008405) B2008405
theorem B1784947 : Blo 1585491 1784947 := bstep (se 1 (by rfl) ⟨1338710, by rfl⟩ : syracuseStep 1784947 = 2677421) B2677421
theorem B27475085 : Blo 1585491 27475085 := bstep (se 3 (by rfl) ⟨5151578, by rfl⟩ : syracuseStep 27475085 = 10303157) B10303157
theorem B2677907 : Blo 1585491 2677907 := bstep (se 1 (by rfl) ⟨2008430, by rfl⟩ : syracuseStep 2677907 = 4016861) B4016861
theorem B4013297 : Blo 1585491 4013297 := bstep (se 2 (by rfl) ⟨1504986, by rfl⟩ : syracuseStep 4013297 = 3009973) B3009973
theorem B3570929 : Blo 1585491 3570929 := bstep (se 2 (by rfl) ⟨1339098, by rfl⟩ : syracuseStep 3570929 = 2678197) B2678197
theorem B1785091 : Blo 1585491 1785091 := bstep (se 1 (by rfl) ⟨1338818, by rfl⟩ : syracuseStep 1785091 = 2677637) B2677637
theorem B3570947 : Blo 1585491 3570947 := bstep (se 1 (by rfl) ⟨2678210, by rfl⟩ : syracuseStep 3570947 = 5356421) B5356421
theorem B6774029 : Blo 1585491 6774029 := bstep (se 3 (by rfl) ⟨1270130, by rfl⟩ : syracuseStep 6774029 = 2540261) B2540261
theorem B2678035 : Blo 1585491 2678035 := bstep (se 1 (by rfl) ⟨2008526, by rfl⟩ : syracuseStep 2678035 = 4017053) B4017053
theorem B4013347 : Blo 1585491 4013347 := bstep (se 1 (by rfl) ⟨3010010, by rfl⟩ : syracuseStep 4013347 = 6020021) B6020021
theorem B1785235 : Blo 1585491 1785235 := bstep (se 1 (by rfl) ⟨1338926, by rfl⟩ : syracuseStep 1785235 = 2677853) B2677853
theorem B2678177 : Blo 1585491 2678177 := bstep (se 2 (by rfl) ⟨1004316, by rfl⟩ : syracuseStep 2678177 = 2008633) B2008633
theorem B4013489 : Blo 1585491 4013489 := bstep (se 2 (by rfl) ⟨1505058, by rfl⟩ : syracuseStep 4013489 = 3010117) B3010117
theorem B5357069 : Blo 1585491 5357069 := bstep (se 3 (by rfl) ⟨1004450, by rfl⟩ : syracuseStep 5357069 = 2008901) B2008901
theorem B3571217 : Blo 1585491 3571217 := bstep (se 2 (by rfl) ⟨1339206, by rfl⟩ : syracuseStep 3571217 = 2678413) B2678413
theorem B2678305 : Blo 1585491 2678305 := bstep (se 2 (by rfl) ⟨1004364, by rfl⟩ : syracuseStep 2678305 = 2008729) B2008729
theorem B1785379 : Blo 1585491 1785379 := bstep (se 1 (by rfl) ⟨1339034, by rfl⟩ : syracuseStep 1785379 = 2678069) B2678069
theorem B3571235 : Blo 1585491 3571235 := bstep (se 1 (by rfl) ⟨2678426, by rfl⟩ : syracuseStep 3571235 = 5356853) B5356853
theorem B2678339 : Blo 1585491 2678339 := bstep (se 1 (by rfl) ⟨2008754, by rfl⟩ : syracuseStep 2678339 = 4017509) B4017509
theorem B5357123 : Blo 1585491 5357123 := bstep (se 1 (by rfl) ⟨4017842, by rfl⟩ : syracuseStep 5357123 = 8035685) B8035685
theorem B8027747 : Blo 1585491 8027747 := bstep (se 1 (by rfl) ⟨6020810, by rfl⟩ : syracuseStep 8027747 = 12041621) B12041621
theorem B1785523 : Blo 1585491 1785523 := bstep (se 1 (by rfl) ⟨1339142, by rfl⟩ : syracuseStep 1785523 = 2678285) B2678285
theorem B2678467 : Blo 1585491 2678467 := bstep (se 1 (by rfl) ⟨2008850, by rfl⟩ : syracuseStep 2678467 = 4017701) B4017701
theorem B6192845 : Blo 1585491 6192845 := bstep (se 3 (by rfl) ⟨1161158, by rfl⟩ : syracuseStep 6192845 = 2322317) B2322317
theorem B3571505 : Blo 1585491 3571505 := bstep (se 2 (by rfl) ⟨1339314, by rfl⟩ : syracuseStep 3571505 = 2678629) B2678629
theorem B2006851 : Blo 1585491 2006851 := bstep (se 1 (by rfl) ⟨1505138, by rfl⟩ : syracuseStep 2006851 = 3010277) B3010277
theorem B1785667 : Blo 1585491 1785667 := bstep (se 1 (by rfl) ⟨1339250, by rfl⟩ : syracuseStep 1785667 = 2678501) B2678501
theorem B3571523 : Blo 1585491 3571523 := bstep (se 1 (by rfl) ⟨2678642, by rfl⟩ : syracuseStep 3571523 = 5357285) B5357285
theorem B2678609 : Blo 1585491 2678609 := bstep (se 2 (by rfl) ⟨1004478, by rfl⟩ : syracuseStep 2678609 = 2008957) B2008957
theorem B5357393 : Blo 1585491 5357393 := bstep (se 2 (by rfl) ⟨2009022, by rfl⟩ : syracuseStep 5357393 = 4018045) B4018045
theorem B6020963 : Blo 1585491 6020963 := bstep (se 1 (by rfl) ⟨4515722, by rfl⟩ : syracuseStep 6020963 = 9031445) B9031445
theorem B2006947 : Blo 1585491 2006947 := bstep (se 1 (by rfl) ⟨1505210, by rfl⟩ : syracuseStep 2006947 = 3010421) B3010421
theorem B2678737 : Blo 1585491 2678737 := bstep (se 2 (by rfl) ⟨1004526, by rfl⟩ : syracuseStep 2678737 = 2009053) B2009053
theorem B1785811 : Blo 1585491 1785811 := bstep (se 1 (by rfl) ⟨1339358, by rfl⟩ : syracuseStep 1785811 = 2678717) B2678717
theorem B2678771 : Blo 1585491 2678771 := bstep (se 1 (by rfl) ⟨2009078, by rfl⟩ : syracuseStep 2678771 = 4018157) B4018157
theorem B88072343 : Blo 1585491 88072343 := bstep (se 1 (by rfl) ⟨66054257, by rfl⟩ : syracuseStep 88072343 = 132108515) B132108515
theorem B5357771 : Blo 1585491 5357771 := bstep (se 1 (by rfl) ⟨4018328, by rfl⟩ : syracuseStep 5357771 = 8036657) B8036657
theorem B6103313 : Blo 1585491 6103313 := bstep (se 2 (by rfl) ⟨2288742, by rfl⟩ : syracuseStep 6103313 = 4577485) B4577485
theorem B18071909 : Blo 1585491 18071909 := bstep (se 4 (by rfl) ⟨1694241, by rfl⟩ : syracuseStep 18071909 = 3388483) B3388483
theorem B26083685 : Blo 1585491 26083685 := bstep (se 4 (by rfl) ⟨2445345, by rfl⟩ : syracuseStep 26083685 = 4890691) B4890691
theorem B2539979 : Blo 1585491 2539979 := bstep (se 1 (by rfl) ⟨1904984, by rfl⟩ : syracuseStep 2539979 = 3809969) B3809969
theorem B2007499 : Blo 1585491 2007499 := bstep (se 1 (by rfl) ⟨1505624, by rfl⟩ : syracuseStep 2007499 = 3011249) B3011249
theorem B4014643 : Blo 1585491 4014643 := bstep (se 1 (by rfl) ⟨3010982, by rfl⟩ : syracuseStep 4014643 = 6021965) B6021965
theorem B2540107 : Blo 1585491 2540107 := bstep (se 1 (by rfl) ⟨1905080, by rfl⟩ : syracuseStep 2540107 = 3810161) B3810161
theorem B6775447 : Blo 1585491 6775447 := bstep (se 1 (by rfl) ⟨5081585, by rfl⟩ : syracuseStep 6775447 = 10163171) B10163171
theorem B28959383 : Blo 1585491 28959383 := bstep (se 1 (by rfl) ⟨21719537, by rfl⟩ : syracuseStep 28959383 = 43439075) B43439075
theorem B5718701 : Blo 1585491 5718701 := bstep (se 3 (by rfl) ⟨1072256, by rfl⟩ : syracuseStep 5718701 = 2144513) B2144513
theorem B4014785 : Blo 1585491 4014785 := bstep (se 2 (by rfl) ⟨1505544, by rfl⟩ : syracuseStep 4014785 = 3011089) B3011089
theorem B2007767 : Blo 1585491 2007767 := bstep (se 1 (by rfl) ⟨1505825, by rfl⟩ : syracuseStep 2007767 = 3011651) B3011651
theorem B6022147 : Blo 1585491 6022147 := bstep (se 1 (by rfl) ⟨4516610, by rfl⟩ : syracuseStep 6022147 = 9033221) B9033221
theorem B7619629 : Blo 1585491 7619629 := bstep (se 3 (by rfl) ⟨1428680, by rfl⟩ : syracuseStep 7619629 = 2857361) B2857361
theorem B9036845 : Blo 1585491 9036845 := bstep (se 3 (by rfl) ⟨1694408, by rfl⟩ : syracuseStep 9036845 = 3388817) B3388817
theorem B2540825 : Blo 1585491 2540825 := bstep (se 2 (by rfl) ⟨952809, by rfl⟩ : syracuseStep 2540825 = 1905619) B1905619
theorem B12043565 : Blo 1585491 12043565 := bstep (se 3 (by rfl) ⟨2258168, by rfl⟩ : syracuseStep 12043565 = 4516337) B4516337
theorem B6022451 : Blo 1585491 6022451 := bstep (se 1 (by rfl) ⟨4516838, by rfl⟩ : syracuseStep 6022451 = 9033677) B9033677
theorem B4580659 : Blo 1585491 4580659 := bstep (se 1 (by rfl) ⟨3435494, by rfl⟩ : syracuseStep 4580659 = 6870989) B6870989
theorem B12862795 : Blo 1585491 12862795 := bstep (se 1 (by rfl) ⟨9647096, by rfl⟩ : syracuseStep 12862795 = 19294193) B19294193
theorem B2860417 : Blo 1585491 2860417 := bstep (se 2 (by rfl) ⟨1072656, by rfl⟩ : syracuseStep 2860417 = 2145313) B2145313
theorem B2008471 : Blo 1585491 2008471 := bstep (se 1 (by rfl) ⟨1506353, by rfl⟩ : syracuseStep 2008471 = 3012707) B3012707
theorem B2541017 : Blo 1585491 2541017 := bstep (se 2 (by rfl) ⟨952881, by rfl⟩ : syracuseStep 2541017 = 1905763) B1905763
theorem B27092555 : Blo 1585491 27092555 := bstep (se 1 (by rfl) ⟨20319416, by rfl⟩ : syracuseStep 27092555 = 40638833) B40638833
theorem B7620227 : Blo 1585491 7620227 := bstep (se 1 (by rfl) ⟨5715170, by rfl⟩ : syracuseStep 7620227 = 11430341) B11430341
theorem B5351129 : Blo 1585491 5351129 := bstep (se 2 (by rfl) ⟨2006673, by rfl⟩ : syracuseStep 5351129 = 4013347) B4013347
theorem B5719825 : Blo 1585491 5719825 := bstep (se 2 (by rfl) ⟨2144934, by rfl⟩ : syracuseStep 5719825 = 4289869) B4289869
theorem B4835095 : Blo 1585491 4835095 := bstep (se 1 (by rfl) ⟨3626321, by rfl⟩ : syracuseStep 4835095 = 7252643) B7252643
theorem B5080907 : Blo 1585491 5080907 := bstep (se 1 (by rfl) ⟨3810680, by rfl⟩ : syracuseStep 5080907 = 7621361) B7621361
theorem B4016051 : Blo 1585491 4016051 := bstep (se 1 (by rfl) ⟨3012038, by rfl⟩ : syracuseStep 4016051 = 6024077) B6024077
theorem B6023105 : Blo 1585491 6023105 := bstep (se 2 (by rfl) ⟨2258664, by rfl⟩ : syracuseStep 6023105 = 4517329) B4517329
theorem B4515905 : Blo 1585491 4515905 := bstep (se 2 (by rfl) ⟨1693464, by rfl⟩ : syracuseStep 4515905 = 3386929) B3386929
theorem B14469185 : Blo 1585491 14469185 := bstep (se 2 (by rfl) ⟨5425944, by rfl⟩ : syracuseStep 14469185 = 10851889) B10851889
theorem B8030339 : Blo 1585491 8030339 := bstep (se 1 (by rfl) ⟨6022754, by rfl⟩ : syracuseStep 8030339 = 12045509) B12045509
theorem B10307735 : Blo 1585491 10307735 := bstep (se 1 (by rfl) ⟨7730801, by rfl⟩ : syracuseStep 10307735 = 15461603) B15461603
theorem B4516019 : Blo 1585491 4516019 := bstep (se 1 (by rfl) ⟨3387014, by rfl⟩ : syracuseStep 4516019 = 6774029) B6774029
theorem B5351831 : Blo 1585491 5351831 := bstep (se 1 (by rfl) ⟨4013873, by rfl⟩ : syracuseStep 5351831 = 8027747) B8027747
theorem B4016587 : Blo 1585491 4016587 := bstep (se 1 (by rfl) ⟨3012440, by rfl⟩ : syracuseStep 4016587 = 6024881) B6024881
theorem B2378315 : Blo 1585491 2378315 := bstep (se 1 (by rfl) ⟨1783736, by rfl⟩ : syracuseStep 2378315 = 3567473) B3567473
theorem B2378327 : Blo 1585491 2378327 := bstep (se 1 (by rfl) ⟨1783745, by rfl⟩ : syracuseStep 2378327 = 3567491) B3567491
theorem B4016729 : Blo 1585491 4016729 := bstep (se 2 (by rfl) ⟨1506273, by rfl⟩ : syracuseStep 4016729 = 3012547) B3012547
theorem B2378393 : Blo 1585491 2378393 := bstep (se 2 (by rfl) ⟨891897, by rfl⟩ : syracuseStep 2378393 = 1783795) B1783795
theorem B9644761 : Blo 1585491 9644761 := bstep (se 2 (by rfl) ⟨3616785, by rfl⟩ : syracuseStep 9644761 = 7233571) B7233571
theorem B2378507 : Blo 1585491 2378507 := bstep (se 1 (by rfl) ⟨1783880, by rfl⟩ : syracuseStep 2378507 = 3567761) B3567761
theorem B2378519 : Blo 1585491 2378519 := bstep (se 1 (by rfl) ⟨1783889, by rfl⟩ : syracuseStep 2378519 = 3567779) B3567779
theorem B2378585 : Blo 1585491 2378585 := bstep (se 2 (by rfl) ⟨891969, by rfl⟩ : syracuseStep 2378585 = 1783939) B1783939
theorem B5352371 : Blo 1585491 5352371 := bstep (se 1 (by rfl) ⟨4014278, by rfl⟩ : syracuseStep 5352371 = 8028557) B8028557
theorem B3812275 : Blo 1585491 3812275 := bstep (se 1 (by rfl) ⟨2859206, by rfl⟩ : syracuseStep 3812275 = 5718413) B5718413
theorem B21719987 : Blo 1585491 21719987 := bstep (se 1 (by rfl) ⟨16289990, by rfl⟩ : syracuseStep 21719987 = 32579981) B32579981
theorem B2378699 : Blo 1585491 2378699 := bstep (se 1 (by rfl) ⟨1784024, by rfl⟩ : syracuseStep 2378699 = 3568049) B3568049
theorem B2378711 : Blo 1585491 2378711 := bstep (se 1 (by rfl) ⟨1784033, by rfl⟩ : syracuseStep 2378711 = 3568067) B3568067
theorem B4287511 : Blo 1585491 4287511 := bstep (se 1 (by rfl) ⟨3215633, by rfl⟩ : syracuseStep 4287511 = 6431267) B6431267
theorem B2378777 : Blo 1585491 2378777 := bstep (se 2 (by rfl) ⟨892041, by rfl⟩ : syracuseStep 2378777 = 1784083) B1784083
theorem B10161197 : Blo 1585491 10161197 := bstep (se 3 (by rfl) ⟨1905224, by rfl⟩ : syracuseStep 10161197 = 3810449) B3810449
theorem B29330525 : Blo 1585491 29330525 := bstep (se 3 (by rfl) ⟨5499473, by rfl⟩ : syracuseStep 29330525 = 10998947) B10998947
theorem B2378891 : Blo 1585491 2378891 := bstep (se 1 (by rfl) ⟨1784168, by rfl⟩ : syracuseStep 2378891 = 3568337) B3568337
theorem B3386519 : Blo 1585491 3386519 := bstep (se 1 (by rfl) ⟨2539889, by rfl⟩ : syracuseStep 3386519 = 5079779) B5079779
theorem B2378903 : Blo 1585491 2378903 := bstep (se 1 (by rfl) ⟨1784177, by rfl⟩ : syracuseStep 2378903 = 3568355) B3568355
theorem B6024365 : Blo 1585491 6024365 := bstep (se 3 (by rfl) ⟨1129568, by rfl⟩ : syracuseStep 6024365 = 2259137) B2259137
theorem B5352641 : Blo 1585491 5352641 := bstep (se 2 (by rfl) ⟨2007240, by rfl⟩ : syracuseStep 5352641 = 4014481) B4014481
theorem B6024395 : Blo 1585491 6024395 := bstep (se 1 (by rfl) ⟨4518296, by rfl⟩ : syracuseStep 6024395 = 9036593) B9036593
theorem B2378969 : Blo 1585491 2378969 := bstep (se 2 (by rfl) ⟨892113, by rfl⟩ : syracuseStep 2378969 = 1784227) B1784227
theorem B2379083 : Blo 1585491 2379083 := bstep (se 1 (by rfl) ⟨1784312, by rfl⟩ : syracuseStep 2379083 = 3568625) B3568625
theorem B2379095 : Blo 1585491 2379095 := bstep (se 1 (by rfl) ⟨1784321, by rfl⟩ : syracuseStep 2379095 = 3568643) B3568643
theorem B9031013 : Blo 1585491 9031013 := bstep (se 4 (by rfl) ⟨846657, by rfl⟩ : syracuseStep 9031013 = 1693315) B1693315
theorem B9039235 : Blo 1585491 9039235 := bstep (se 1 (by rfl) ⟨6779426, by rfl⟩ : syracuseStep 9039235 = 13558853) B13558853
theorem B4017559 : Blo 1585491 4017559 := bstep (se 1 (by rfl) ⟨3013169, by rfl⟩ : syracuseStep 4017559 = 6026339) B6026339
theorem B1609111 : Blo 1585491 1609111 := bstep (se 1 (by rfl) ⟨1206833, by rfl⟩ : syracuseStep 1609111 = 2413667) B2413667
theorem B2379161 : Blo 1585491 2379161 := bstep (se 2 (by rfl) ⟨892185, by rfl⟩ : syracuseStep 2379161 = 1784371) B1784371
theorem B5082547 : Blo 1585491 5082547 := bstep (se 1 (by rfl) ⟨3811910, by rfl⟩ : syracuseStep 5082547 = 7623821) B7623821
theorem B6778333 : Blo 1585491 6778333 := bstep (se 3 (by rfl) ⟨1270937, by rfl⟩ : syracuseStep 6778333 = 2541875) B2541875
theorem B2379275 : Blo 1585491 2379275 := bstep (se 1 (by rfl) ⟨1784456, by rfl⟩ : syracuseStep 2379275 = 3568913) B3568913
theorem B2379287 : Blo 1585491 2379287 := bstep (se 1 (by rfl) ⟨1784465, by rfl⟩ : syracuseStep 2379287 = 3568931) B3568931
theorem B2379353 : Blo 1585491 2379353 := bstep (se 2 (by rfl) ⟨892257, by rfl⟩ : syracuseStep 2379353 = 1784515) B1784515
theorem B20328029 : Blo 1585491 20328029 := bstep (se 3 (by rfl) ⟨3811505, by rfl⟩ : syracuseStep 20328029 = 7623011) B7623011
theorem B8572517 : Blo 1585491 8572517 := bstep (se 4 (by rfl) ⟨803673, by rfl⟩ : syracuseStep 8572517 = 1607347) B1607347
theorem B26087093 : Blo 1585491 26087093 := bstep (se 5 (by rfl) ⟨1222832, by rfl⟩ : syracuseStep 26087093 = 2445665) B2445665
theorem B2379467 : Blo 1585491 2379467 := bstep (se 1 (by rfl) ⟨1784600, by rfl⟩ : syracuseStep 2379467 = 3569201) B3569201
theorem B2379479 : Blo 1585491 2379479 := bstep (se 1 (by rfl) ⟨1784609, by rfl⟩ : syracuseStep 2379479 = 3569219) B3569219
theorem B5353181 : Blo 1585491 5353181 := bstep (se 3 (by rfl) ⟨1003721, by rfl⟩ : syracuseStep 5353181 = 2007443) B2007443
theorem B3567383 : Blo 1585491 3567383 := bstep (se 1 (by rfl) ⟨2675537, by rfl⟩ : syracuseStep 3567383 = 5351075) B5351075
theorem B2379545 : Blo 1585491 2379545 := bstep (se 2 (by rfl) ⟨892329, by rfl⟩ : syracuseStep 2379545 = 1784659) B1784659
theorem B4017995 : Blo 1585491 4017995 := bstep (se 1 (by rfl) ⟨3013496, by rfl⟩ : syracuseStep 4017995 = 6026993) B6026993
theorem B6025049 : Blo 1585491 6025049 := bstep (se 2 (by rfl) ⟨2259393, by rfl⟩ : syracuseStep 6025049 = 4518787) B4518787
theorem B2379659 : Blo 1585491 2379659 := bstep (se 1 (by rfl) ⟨1784744, by rfl⟩ : syracuseStep 2379659 = 3569489) B3569489
theorem B2379671 : Blo 1585491 2379671 := bstep (se 1 (by rfl) ⟨1784753, by rfl⟩ : syracuseStep 2379671 = 3569507) B3569507
theorem B3567563 : Blo 1585491 3567563 := bstep (se 1 (by rfl) ⟨2675672, by rfl⟩ : syracuseStep 3567563 = 5351345) B5351345
theorem B2379737 : Blo 1585491 2379737 := bstep (se 2 (by rfl) ⟨892401, by rfl⟩ : syracuseStep 2379737 = 1784803) B1784803
theorem B3567617 : Blo 1585491 3567617 := bstep (se 2 (by rfl) ⟨1337856, by rfl⟩ : syracuseStep 3567617 = 2675713) B2675713
theorem B6959155 : Blo 1585491 6959155 := bstep (se 1 (by rfl) ⟨5219366, by rfl⟩ : syracuseStep 6959155 = 10438733) B10438733
theorem B13553729 : Blo 1585491 13553729 := bstep (se 2 (by rfl) ⟨5082648, by rfl⟩ : syracuseStep 13553729 = 10165297) B10165297
theorem B2379851 : Blo 1585491 2379851 := bstep (se 1 (by rfl) ⟨1784888, by rfl⟩ : syracuseStep 2379851 = 3569777) B3569777
theorem B2379863 : Blo 1585491 2379863 := bstep (se 1 (by rfl) ⟨1784897, by rfl⟩ : syracuseStep 2379863 = 3569795) B3569795
theorem B6025367 : Blo 1585491 6025367 := bstep (se 1 (by rfl) ⟨4519025, by rfl⟩ : syracuseStep 6025367 = 9038051) B9038051
theorem B2379929 : Blo 1585491 2379929 := bstep (se 2 (by rfl) ⟨892473, by rfl⟩ : syracuseStep 2379929 = 1784947) B1784947
theorem B3010763 : Blo 1585491 3010763 := bstep (se 1 (by rfl) ⟨2258072, by rfl⟩ : syracuseStep 3010763 = 4516145) B4516145
theorem B3387595 : Blo 1585491 3387595 := bstep (se 1 (by rfl) ⟨2540696, by rfl⟩ : syracuseStep 3387595 = 5081393) B5081393
theorem B3567833 : Blo 1585491 3567833 := bstep (se 2 (by rfl) ⟨1337937, by rfl⟩ : syracuseStep 3567833 = 2675875) B2675875
theorem B2380043 : Blo 1585491 2380043 := bstep (se 1 (by rfl) ⟨1785032, by rfl⟩ : syracuseStep 2380043 = 3570065) B3570065
theorem B6779153 : Blo 1585491 6779153 := bstep (se 2 (by rfl) ⟨2542182, by rfl⟩ : syracuseStep 6779153 = 5084365) B5084365
theorem B2380055 : Blo 1585491 2380055 := bstep (se 1 (by rfl) ⟨1785041, by rfl⟩ : syracuseStep 2380055 = 3570083) B3570083
theorem B3567923 : Blo 1585491 3567923 := bstep (se 1 (by rfl) ⟨2675942, by rfl⟩ : syracuseStep 3567923 = 5351885) B5351885
theorem B9040193 : Blo 1585491 9040193 := bstep (se 2 (by rfl) ⟨3390072, by rfl⟩ : syracuseStep 9040193 = 6780145) B6780145
theorem B10309963 : Blo 1585491 10309963 := bstep (se 1 (by rfl) ⟨7732472, by rfl⟩ : syracuseStep 10309963 = 15464945) B15464945
theorem B1585495 : Blo 1585491 1585495 := bstep (se 1 (by rfl) ⟨1189121, by rfl⟩ : syracuseStep 1585495 = 2378243) B2378243
theorem B3567959 : Blo 1585491 3567959 := bstep (se 1 (by rfl) ⟨2675969, by rfl⟩ : syracuseStep 3567959 = 5351939) B5351939
theorem B2380121 : Blo 1585491 2380121 := bstep (se 2 (by rfl) ⟨892545, by rfl⟩ : syracuseStep 2380121 = 1785091) B1785091
theorem B1585515 : Blo 1585491 1585515 := bstep (se 1 (by rfl) ⟨1189136, by rfl⟩ : syracuseStep 1585515 = 2378273) B2378273
theorem B1585527 : Blo 1585491 1585527 := bstep (se 1 (by rfl) ⟨1189145, by rfl⟩ : syracuseStep 1585527 = 2378291) B2378291
theorem B3010945 : Blo 1585491 3010945 := bstep (se 2 (by rfl) ⟨1129104, by rfl⟩ : syracuseStep 3010945 = 2258209) B2258209
theorem B1585547 : Blo 1585491 1585547 := bstep (se 1 (by rfl) ⟨1189160, by rfl⟩ : syracuseStep 1585547 = 2378321) B2378321
theorem B1585559 : Blo 1585491 1585559 := bstep (se 1 (by rfl) ⟨1189169, by rfl⟩ : syracuseStep 1585559 = 2378339) B2378339
theorem B1585579 : Blo 1585491 1585579 := bstep (se 1 (by rfl) ⟨1189184, by rfl⟩ : syracuseStep 1585579 = 2378369) B2378369
theorem B1585591 : Blo 1585491 1585591 := bstep (se 1 (by rfl) ⟨1189193, by rfl⟩ : syracuseStep 1585591 = 2378387) B2378387
theorem B1585611 : Blo 1585491 1585611 := bstep (se 1 (by rfl) ⟨1189208, by rfl⟩ : syracuseStep 1585611 = 2378417) B2378417
theorem B2380235 : Blo 1585491 2380235 := bstep (se 1 (by rfl) ⟨1785176, by rfl⟩ : syracuseStep 2380235 = 3570353) B3570353
theorem B2576843 : Blo 1585491 2576843 := bstep (se 1 (by rfl) ⟨1932632, by rfl⟩ : syracuseStep 2576843 = 3865265) B3865265
theorem B1585623 : Blo 1585491 1585623 := bstep (se 1 (by rfl) ⟨1189217, by rfl⟩ : syracuseStep 1585623 = 2378435) B2378435
theorem B2380247 : Blo 1585491 2380247 := bstep (se 1 (by rfl) ⟨1785185, by rfl⟩ : syracuseStep 2380247 = 3570371) B3570371
theorem B1585643 : Blo 1585491 1585643 := bstep (se 1 (by rfl) ⟨1189232, by rfl⟩ : syracuseStep 1585643 = 2378465) B2378465
theorem B1585655 : Blo 1585491 1585655 := bstep (se 1 (by rfl) ⟨1189241, by rfl⟩ : syracuseStep 1585655 = 2378483) B2378483
theorem B1585675 : Blo 1585491 1585675 := bstep (se 1 (by rfl) ⟨1189256, by rfl⟩ : syracuseStep 1585675 = 2378513) B2378513
theorem B3568139 : Blo 1585491 3568139 := bstep (se 1 (by rfl) ⟨2676104, by rfl⟩ : syracuseStep 3568139 = 5352209) B5352209
theorem B1585687 : Blo 1585491 1585687 := bstep (se 1 (by rfl) ⟨1189265, by rfl⟩ : syracuseStep 1585687 = 2378531) B2378531
theorem B2380313 : Blo 1585491 2380313 := bstep (se 2 (by rfl) ⟨892617, by rfl⟩ : syracuseStep 2380313 = 1785235) B1785235
theorem B1585707 : Blo 1585491 1585707 := bstep (se 1 (by rfl) ⟨1189280, by rfl⟩ : syracuseStep 1585707 = 2378561) B2378561
theorem B1585719 : Blo 1585491 1585719 := bstep (se 1 (by rfl) ⟨1189289, by rfl⟩ : syracuseStep 1585719 = 2378579) B2378579
theorem B3568193 : Blo 1585491 3568193 := bstep (se 2 (by rfl) ⟨1338072, by rfl⟩ : syracuseStep 3568193 = 2676145) B2676145
theorem B1585739 : Blo 1585491 1585739 := bstep (se 1 (by rfl) ⟨1189304, by rfl⟩ : syracuseStep 1585739 = 2378609) B2378609
theorem B1585751 : Blo 1585491 1585751 := bstep (se 1 (by rfl) ⟨1189313, by rfl⟩ : syracuseStep 1585751 = 2378627) B2378627
theorem B1585771 : Blo 1585491 1585771 := bstep (se 1 (by rfl) ⟨1189328, by rfl⟩ : syracuseStep 1585771 = 2378657) B2378657
theorem B1585783 : Blo 1585491 1585783 := bstep (se 1 (by rfl) ⟨1189337, by rfl⟩ : syracuseStep 1585783 = 2378675) B2378675
theorem B1585803 : Blo 1585491 1585803 := bstep (se 1 (by rfl) ⟨1189352, by rfl⟩ : syracuseStep 1585803 = 2378705) B2378705
theorem B2380427 : Blo 1585491 2380427 := bstep (se 1 (by rfl) ⟨1785320, by rfl⟩ : syracuseStep 2380427 = 3570641) B3570641
theorem B1585815 : Blo 1585491 1585815 := bstep (se 1 (by rfl) ⟨1189361, by rfl⟩ : syracuseStep 1585815 = 2378723) B2378723
theorem B2380439 : Blo 1585491 2380439 := bstep (se 1 (by rfl) ⟨1785329, by rfl⟩ : syracuseStep 2380439 = 3570659) B3570659
theorem B1585835 : Blo 1585491 1585835 := bstep (se 1 (by rfl) ⟨1189376, by rfl⟩ : syracuseStep 1585835 = 2378753) B2378753
theorem B1585847 : Blo 1585491 1585847 := bstep (se 1 (by rfl) ⟨1189385, by rfl⟩ : syracuseStep 1585847 = 2378771) B2378771
theorem B1585867 : Blo 1585491 1585867 := bstep (se 1 (by rfl) ⟨1189400, by rfl⟩ : syracuseStep 1585867 = 2378801) B2378801
theorem B1585879 : Blo 1585491 1585879 := bstep (se 1 (by rfl) ⟨1189409, by rfl⟩ : syracuseStep 1585879 = 2378819) B2378819
theorem B2380505 : Blo 1585491 2380505 := bstep (se 2 (by rfl) ⟨892689, by rfl⟩ : syracuseStep 2380505 = 1785379) B1785379
theorem B1585899 : Blo 1585491 1585899 := bstep (se 1 (by rfl) ⟨1189424, by rfl⟩ : syracuseStep 1585899 = 2378849) B2378849
theorem B1585911 : Blo 1585491 1585911 := bstep (se 1 (by rfl) ⟨1189433, by rfl⟩ : syracuseStep 1585911 = 2378867) B2378867
theorem B1585931 : Blo 1585491 1585931 := bstep (se 1 (by rfl) ⟨1189448, by rfl⟩ : syracuseStep 1585931 = 2378897) B2378897
theorem B1585943 : Blo 1585491 1585943 := bstep (se 1 (by rfl) ⟨1189457, by rfl⟩ : syracuseStep 1585943 = 2378915) B2378915
theorem B3568409 : Blo 1585491 3568409 := bstep (se 2 (by rfl) ⟨1338153, by rfl⟩ : syracuseStep 3568409 = 2676307) B2676307
theorem B1585963 : Blo 1585491 1585963 := bstep (se 1 (by rfl) ⟨1189472, by rfl⟩ : syracuseStep 1585963 = 2378945) B2378945
theorem B16290605 : Blo 1585491 16290605 := bstep (se 3 (by rfl) ⟨3054488, by rfl⟩ : syracuseStep 16290605 = 6108977) B6108977
theorem B6026035 : Blo 1585491 6026035 := bstep (se 1 (by rfl) ⟨4519526, by rfl⟩ : syracuseStep 6026035 = 9039053) B9039053
theorem B1585975 : Blo 1585491 1585975 := bstep (se 1 (by rfl) ⟨1189481, by rfl⟩ : syracuseStep 1585975 = 2378963) B2378963
theorem B3011393 : Blo 1585491 3011393 := bstep (se 2 (by rfl) ⟨1129272, by rfl⟩ : syracuseStep 3011393 = 2258545) B2258545
theorem B2675531 : Blo 1585491 2675531 := bstep (se 1 (by rfl) ⟨2006648, by rfl⟩ : syracuseStep 2675531 = 4013297) B4013297
theorem B1585995 : Blo 1585491 1585995 := bstep (se 1 (by rfl) ⟨1189496, by rfl⟩ : syracuseStep 1585995 = 2378993) B2378993
theorem B5354315 : Blo 1585491 5354315 := bstep (se 1 (by rfl) ⟨4015736, by rfl⟩ : syracuseStep 5354315 = 8031473) B8031473
theorem B2380619 : Blo 1585491 2380619 := bstep (se 1 (by rfl) ⟨1785464, by rfl⟩ : syracuseStep 2380619 = 3570929) B3570929
theorem B1586007 : Blo 1585491 1586007 := bstep (se 1 (by rfl) ⟨1189505, by rfl⟩ : syracuseStep 1586007 = 2379011) B2379011
theorem B2380631 : Blo 1585491 2380631 := bstep (se 1 (by rfl) ⟨1785473, by rfl⟩ : syracuseStep 2380631 = 3570947) B3570947
theorem B1586027 : Blo 1585491 1586027 := bstep (se 1 (by rfl) ⟨1189520, by rfl⟩ : syracuseStep 1586027 = 2379041) B2379041
theorem B3568499 : Blo 1585491 3568499 := bstep (se 1 (by rfl) ⟨2676374, by rfl⟩ : syracuseStep 3568499 = 5352749) B5352749
theorem B1586039 : Blo 1585491 1586039 := bstep (se 1 (by rfl) ⟨1189529, by rfl⟩ : syracuseStep 1586039 = 2379059) B2379059
theorem B1586059 : Blo 1585491 1586059 := bstep (se 1 (by rfl) ⟨1189544, by rfl⟩ : syracuseStep 1586059 = 2379089) B2379089
theorem B3568535 : Blo 1585491 3568535 := bstep (se 1 (by rfl) ⟨2676401, by rfl⟩ : syracuseStep 3568535 = 5352803) B5352803
theorem B1586071 : Blo 1585491 1586071 := bstep (se 1 (by rfl) ⟨1189553, by rfl⟩ : syracuseStep 1586071 = 2379107) B2379107
theorem B3388313 : Blo 1585491 3388313 := bstep (se 2 (by rfl) ⟨1270617, by rfl⟩ : syracuseStep 3388313 = 2541235) B2541235
theorem B2380697 : Blo 1585491 2380697 := bstep (se 2 (by rfl) ⟨892761, by rfl⟩ : syracuseStep 2380697 = 1785523) B1785523
theorem B1586091 : Blo 1585491 1586091 := bstep (se 1 (by rfl) ⟨1189568, by rfl⟩ : syracuseStep 1586091 = 2379137) B2379137
theorem B6779821 : Blo 1585491 6779821 := bstep (se 3 (by rfl) ⟨1271216, by rfl⟩ : syracuseStep 6779821 = 2542433) B2542433
theorem B1586103 : Blo 1585491 1586103 := bstep (se 1 (by rfl) ⟨1189577, by rfl⟩ : syracuseStep 1586103 = 2379155) B2379155
theorem B6960065 : Blo 1585491 6960065 := bstep (se 2 (by rfl) ⟨2610024, by rfl⟩ : syracuseStep 6960065 = 5220049) B5220049
theorem B2675659 : Blo 1585491 2675659 := bstep (se 1 (by rfl) ⟨2006744, by rfl⟩ : syracuseStep 2675659 = 4013489) B4013489
theorem B1586123 : Blo 1585491 1586123 := bstep (se 1 (by rfl) ⟨1189592, by rfl⟩ : syracuseStep 1586123 = 2379185) B2379185
theorem B1586135 : Blo 1585491 1586135 := bstep (se 1 (by rfl) ⟨1189601, by rfl⟩ : syracuseStep 1586135 = 2379203) B2379203
theorem B1586155 : Blo 1585491 1586155 := bstep (se 1 (by rfl) ⟨1189616, by rfl⟩ : syracuseStep 1586155 = 2379233) B2379233
theorem B1586167 : Blo 1585491 1586167 := bstep (se 1 (by rfl) ⟨1189625, by rfl⟩ : syracuseStep 1586167 = 2379251) B2379251
theorem B1586187 : Blo 1585491 1586187 := bstep (se 1 (by rfl) ⟨1189640, by rfl⟩ : syracuseStep 1586187 = 2379281) B2379281
theorem B2380811 : Blo 1585491 2380811 := bstep (se 1 (by rfl) ⟨1785608, by rfl⟩ : syracuseStep 2380811 = 3571217) B3571217
theorem B1586199 : Blo 1585491 1586199 := bstep (se 1 (by rfl) ⟨1189649, by rfl⟩ : syracuseStep 1586199 = 2379299) B2379299
theorem B4518935 : Blo 1585491 4518935 := bstep (se 1 (by rfl) ⟨3389201, by rfl⟩ : syracuseStep 4518935 = 6778403) B6778403
theorem B2380823 : Blo 1585491 2380823 := bstep (se 1 (by rfl) ⟨1785617, by rfl⟩ : syracuseStep 2380823 = 3571235) B3571235
theorem B1586219 : Blo 1585491 1586219 := bstep (se 1 (by rfl) ⟨1189664, by rfl⟩ : syracuseStep 1586219 = 2379329) B2379329
theorem B12219437 : Blo 1585491 12219437 := bstep (se 3 (by rfl) ⟨2291144, by rfl⟩ : syracuseStep 12219437 = 4582289) B4582289
theorem B4289587 : Blo 1585491 4289587 := bstep (se 1 (by rfl) ⟨3217190, by rfl⟩ : syracuseStep 4289587 = 6434381) B6434381
theorem B1586231 : Blo 1585491 1586231 := bstep (se 1 (by rfl) ⟨1189673, by rfl⟩ : syracuseStep 1586231 = 2379347) B2379347
theorem B3568715 : Blo 1585491 3568715 := bstep (se 1 (by rfl) ⟨2676536, by rfl⟩ : syracuseStep 3568715 = 5353073) B5353073
theorem B1586251 : Blo 1585491 1586251 := bstep (se 1 (by rfl) ⟨1189688, by rfl⟩ : syracuseStep 1586251 = 2379377) B2379377
theorem B1586263 : Blo 1585491 1586263 := bstep (se 1 (by rfl) ⟨1189697, by rfl⟩ : syracuseStep 1586263 = 2379395) B2379395
theorem B2675801 : Blo 1585491 2675801 := bstep (se 2 (by rfl) ⟨1003425, by rfl⟩ : syracuseStep 2675801 = 2006851) B2006851
theorem B5354585 : Blo 1585491 5354585 := bstep (se 2 (by rfl) ⟨2007969, by rfl⟩ : syracuseStep 5354585 = 4015939) B4015939
theorem B12047453 : Blo 1585491 12047453 := bstep (se 3 (by rfl) ⟨2258897, by rfl⟩ : syracuseStep 12047453 = 4517795) B4517795
theorem B2380889 : Blo 1585491 2380889 := bstep (se 2 (by rfl) ⟨892833, by rfl⟩ : syracuseStep 2380889 = 1785667) B1785667
theorem B1586283 : Blo 1585491 1586283 := bstep (se 1 (by rfl) ⟨1189712, by rfl⟩ : syracuseStep 1586283 = 2379425) B2379425
theorem B1586295 : Blo 1585491 1586295 := bstep (se 1 (by rfl) ⟨1189721, by rfl⟩ : syracuseStep 1586295 = 2379443) B2379443
theorem B3568769 : Blo 1585491 3568769 := bstep (se 2 (by rfl) ⟨1338288, by rfl⟩ : syracuseStep 3568769 = 2676577) B2676577
theorem B1586315 : Blo 1585491 1586315 := bstep (se 1 (by rfl) ⟨1189736, by rfl⟩ : syracuseStep 1586315 = 2379473) B2379473
theorem B1586327 : Blo 1585491 1586327 := bstep (se 1 (by rfl) ⟨1189745, by rfl⟩ : syracuseStep 1586327 = 2379491) B2379491
theorem B3011735 : Blo 1585491 3011735 := bstep (se 1 (by rfl) ⟨2258801, by rfl⟩ : syracuseStep 3011735 = 4517603) B4517603
theorem B1586347 : Blo 1585491 1586347 := bstep (se 1 (by rfl) ⟨1189760, by rfl⟩ : syracuseStep 1586347 = 2379521) B2379521
theorem B1586359 : Blo 1585491 1586359 := bstep (se 1 (by rfl) ⟨1189769, by rfl⟩ : syracuseStep 1586359 = 2379539) B2379539
theorem B2258123 : Blo 1585491 2258123 := bstep (se 1 (by rfl) ⟨1693592, by rfl⟩ : syracuseStep 2258123 = 3387185) B3387185
theorem B1586379 : Blo 1585491 1586379 := bstep (se 1 (by rfl) ⟨1189784, by rfl⟩ : syracuseStep 1586379 = 2379569) B2379569
theorem B2381003 : Blo 1585491 2381003 := bstep (se 1 (by rfl) ⟨1785752, by rfl⟩ : syracuseStep 2381003 = 3571505) B3571505
theorem B1586391 : Blo 1585491 1586391 := bstep (se 1 (by rfl) ⟨1189793, by rfl⟩ : syracuseStep 1586391 = 2379587) B2379587
theorem B2381015 : Blo 1585491 2381015 := bstep (se 1 (by rfl) ⟨1785761, by rfl⟩ : syracuseStep 2381015 = 3571523) B3571523
theorem B2675929 : Blo 1585491 2675929 := bstep (se 2 (by rfl) ⟨1003473, by rfl⟩ : syracuseStep 2675929 = 2006947) B2006947
theorem B1586411 : Blo 1585491 1586411 := bstep (se 1 (by rfl) ⟨1189808, by rfl⟩ : syracuseStep 1586411 = 2379617) B2379617
theorem B1586423 : Blo 1585491 1586423 := bstep (se 1 (by rfl) ⟨1189817, by rfl⟩ : syracuseStep 1586423 = 2379635) B2379635
theorem B1586443 : Blo 1585491 1586443 := bstep (se 1 (by rfl) ⟨1189832, by rfl⟩ : syracuseStep 1586443 = 2379665) B2379665
theorem B1586455 : Blo 1585491 1586455 := bstep (se 1 (by rfl) ⟨1189841, by rfl⟩ : syracuseStep 1586455 = 2379683) B2379683
theorem B2381081 : Blo 1585491 2381081 := bstep (se 2 (by rfl) ⟨892905, by rfl⟩ : syracuseStep 2381081 = 1785811) B1785811
theorem B1586475 : Blo 1585491 1586475 := bstep (se 1 (by rfl) ⟨1189856, by rfl⟩ : syracuseStep 1586475 = 2379713) B2379713
theorem B1586487 : Blo 1585491 1586487 := bstep (se 1 (by rfl) ⟨1189865, by rfl⟩ : syracuseStep 1586487 = 2379731) B2379731
theorem B1586507 : Blo 1585491 1586507 := bstep (se 1 (by rfl) ⟨1189880, by rfl⟩ : syracuseStep 1586507 = 2379761) B2379761
theorem B1586519 : Blo 1585491 1586519 := bstep (se 1 (by rfl) ⟨1189889, by rfl⟩ : syracuseStep 1586519 = 2379779) B2379779
theorem B3568985 : Blo 1585491 3568985 := bstep (se 2 (by rfl) ⟨1338369, by rfl⟩ : syracuseStep 3568985 = 2676739) B2676739
theorem B14472541 : Blo 1585491 14472541 := bstep (se 3 (by rfl) ⟨2713601, by rfl⟩ : syracuseStep 14472541 = 5427203) B5427203
theorem B1586539 : Blo 1585491 1586539 := bstep (se 1 (by rfl) ⟨1189904, by rfl⟩ : syracuseStep 1586539 = 2379809) B2379809
theorem B1586551 : Blo 1585491 1586551 := bstep (se 1 (by rfl) ⟨1189913, by rfl⟩ : syracuseStep 1586551 = 2379827) B2379827
theorem B1586571 : Blo 1585491 1586571 := bstep (se 1 (by rfl) ⟨1189928, by rfl⟩ : syracuseStep 1586571 = 2379857) B2379857
theorem B2381195 : Blo 1585491 2381195 := bstep (se 1 (by rfl) ⟨1785896, by rfl⟩ : syracuseStep 2381195 = 3571793) B3571793
theorem B1586583 : Blo 1585491 1586583 := bstep (se 1 (by rfl) ⟨1189937, by rfl⟩ : syracuseStep 1586583 = 2379875) B2379875
theorem B2381207 : Blo 1585491 2381207 := bstep (se 1 (by rfl) ⟨1785905, by rfl⟩ : syracuseStep 2381207 = 3571811) B3571811
theorem B3388825 : Blo 1585491 3388825 := bstep (se 2 (by rfl) ⟨1270809, by rfl⟩ : syracuseStep 3388825 = 2541619) B2541619
theorem B1586603 : Blo 1585491 1586603 := bstep (se 1 (by rfl) ⟨1189952, by rfl⟩ : syracuseStep 1586603 = 2379905) B2379905
theorem B3569075 : Blo 1585491 3569075 := bstep (se 1 (by rfl) ⟨2676806, by rfl⟩ : syracuseStep 3569075 = 5353613) B5353613
theorem B1586615 : Blo 1585491 1586615 := bstep (se 1 (by rfl) ⟨1189961, by rfl⟩ : syracuseStep 1586615 = 2379923) B2379923
theorem B1586635 : Blo 1585491 1586635 := bstep (se 1 (by rfl) ⟨1189976, by rfl⟩ : syracuseStep 1586635 = 2379953) B2379953
theorem B3569111 : Blo 1585491 3569111 := bstep (se 1 (by rfl) ⟨2676833, by rfl⟩ : syracuseStep 3569111 = 5353667) B5353667
theorem B1586647 : Blo 1585491 1586647 := bstep (se 1 (by rfl) ⟨1189985, by rfl⟩ : syracuseStep 1586647 = 2379971) B2379971
theorem B1586667 : Blo 1585491 1586667 := bstep (se 1 (by rfl) ⟨1190000, by rfl⟩ : syracuseStep 1586667 = 2380001) B2380001
theorem B1586679 : Blo 1585491 1586679 := bstep (se 1 (by rfl) ⟨1190009, by rfl⟩ : syracuseStep 1586679 = 2380019) B2380019
theorem B6780419 : Blo 1585491 6780419 := bstep (se 1 (by rfl) ⟨5085314, by rfl⟩ : syracuseStep 6780419 = 10170629) B10170629
theorem B1586699 : Blo 1585491 1586699 := bstep (se 1 (by rfl) ⟨1190024, by rfl⟩ : syracuseStep 1586699 = 2380049) B2380049
theorem B1586711 : Blo 1585491 1586711 := bstep (se 1 (by rfl) ⟨1190033, by rfl⟩ : syracuseStep 1586711 = 2380067) B2380067
theorem B1586731 : Blo 1585491 1586731 := bstep (se 1 (by rfl) ⟨1190048, by rfl⟩ : syracuseStep 1586731 = 2380097) B2380097
theorem B3388979 : Blo 1585491 3388979 := bstep (se 1 (by rfl) ⟨2541734, by rfl⟩ : syracuseStep 3388979 = 5083469) B5083469
theorem B1586743 : Blo 1585491 1586743 := bstep (se 1 (by rfl) ⟨1190057, by rfl⟩ : syracuseStep 1586743 = 2380115) B2380115
theorem B1586763 : Blo 1585491 1586763 := bstep (se 1 (by rfl) ⟨1190072, by rfl⟩ : syracuseStep 1586763 = 2380145) B2380145
theorem B1586775 : Blo 1585491 1586775 := bstep (se 1 (by rfl) ⟨1190081, by rfl⟩ : syracuseStep 1586775 = 2380163) B2380163
theorem B5084765 : Blo 1585491 5084765 := bstep (se 3 (by rfl) ⟨953393, by rfl⟩ : syracuseStep 5084765 = 1906787) B1906787
theorem B1586795 : Blo 1585491 1586795 := bstep (se 1 (by rfl) ⟨1190096, by rfl⟩ : syracuseStep 1586795 = 2380193) B2380193
theorem B1586807 : Blo 1585491 1586807 := bstep (se 1 (by rfl) ⟨1190105, by rfl⟩ : syracuseStep 1586807 = 2380211) B2380211
theorem B3569291 : Blo 1585491 3569291 := bstep (se 1 (by rfl) ⟨2676968, by rfl⟩ : syracuseStep 3569291 = 5353937) B5353937
theorem B1586827 : Blo 1585491 1586827 := bstep (se 1 (by rfl) ⟨1190120, by rfl⟩ : syracuseStep 1586827 = 2380241) B2380241
theorem B1586839 : Blo 1585491 1586839 := bstep (se 1 (by rfl) ⟨1190129, by rfl⟩ : syracuseStep 1586839 = 2380259) B2380259
theorem B1586859 : Blo 1585491 1586859 := bstep (se 1 (by rfl) ⟨1190144, by rfl⟩ : syracuseStep 1586859 = 2380289) B2380289
theorem B1586871 : Blo 1585491 1586871 := bstep (se 1 (by rfl) ⟨1190153, by rfl⟩ : syracuseStep 1586871 = 2380307) B2380307
theorem B3569345 : Blo 1585491 3569345 := bstep (se 2 (by rfl) ⟨1338504, by rfl⟩ : syracuseStep 3569345 = 2677009) B2677009
theorem B1586891 : Blo 1585491 1586891 := bstep (se 1 (by rfl) ⟨1190168, by rfl⟩ : syracuseStep 1586891 = 2380337) B2380337
theorem B73266893 : Blo 1585491 73266893 := bstep (se 3 (by rfl) ⟨13737542, by rfl⟩ : syracuseStep 73266893 = 27475085) B27475085
theorem B1586903 : Blo 1585491 1586903 := bstep (se 1 (by rfl) ⟨1190177, by rfl⟩ : syracuseStep 1586903 = 2380355) B2380355
theorem B1586923 : Blo 1585491 1586923 := bstep (se 1 (by rfl) ⟨1190192, by rfl⟩ : syracuseStep 1586923 = 2380385) B2380385
theorem B1586935 : Blo 1585491 1586935 := bstep (se 1 (by rfl) ⟨1190201, by rfl⟩ : syracuseStep 1586935 = 2380403) B2380403
theorem B1586955 : Blo 1585491 1586955 := bstep (se 1 (by rfl) ⟨1190216, by rfl⟩ : syracuseStep 1586955 = 2380433) B2380433
theorem B8034065 : Blo 1585491 8034065 := bstep (se 2 (by rfl) ⟨3012774, by rfl⟩ : syracuseStep 8034065 = 6025549) B6025549
theorem B2676503 : Blo 1585491 2676503 := bstep (se 1 (by rfl) ⟨2007377, by rfl⟩ : syracuseStep 2676503 = 4014755) B4014755
theorem B5355287 : Blo 1585491 5355287 := bstep (se 1 (by rfl) ⟨4016465, by rfl⟩ : syracuseStep 5355287 = 8032931) B8032931
theorem B1586967 : Blo 1585491 1586967 := bstep (se 1 (by rfl) ⟨1190225, by rfl⟩ : syracuseStep 1586967 = 2380451) B2380451
theorem B1586987 : Blo 1585491 1586987 := bstep (se 1 (by rfl) ⟨1190240, by rfl⟩ : syracuseStep 1586987 = 2380481) B2380481
theorem B3012403 : Blo 1585491 3012403 := bstep (se 1 (by rfl) ⟨2259302, by rfl⟩ : syracuseStep 3012403 = 4518605) B4518605
theorem B1586999 : Blo 1585491 1586999 := bstep (se 1 (by rfl) ⟨1190249, by rfl⟩ : syracuseStep 1586999 = 2380499) B2380499
theorem B1587019 : Blo 1585491 1587019 := bstep (se 1 (by rfl) ⟨1190264, by rfl⟩ : syracuseStep 1587019 = 2380529) B2380529
theorem B1587031 : Blo 1585491 1587031 := bstep (se 1 (by rfl) ⟨1190273, by rfl⟩ : syracuseStep 1587031 = 2380547) B2380547
theorem B18315109 : Blo 1585491 18315109 := bstep (se 4 (by rfl) ⟨1717041, by rfl⟩ : syracuseStep 18315109 = 3434083) B3434083
theorem B1587051 : Blo 1585491 1587051 := bstep (se 1 (by rfl) ⟨1190288, by rfl⟩ : syracuseStep 1587051 = 2380577) B2380577
theorem B1587063 : Blo 1585491 1587063 := bstep (se 1 (by rfl) ⟨1190297, by rfl⟩ : syracuseStep 1587063 = 2380595) B2380595
theorem B1587083 : Blo 1585491 1587083 := bstep (se 1 (by rfl) ⟨1190312, by rfl⟩ : syracuseStep 1587083 = 2380625) B2380625
theorem B2676631 : Blo 1585491 2676631 := bstep (se 1 (by rfl) ⟨2007473, by rfl⟩ : syracuseStep 2676631 = 4014947) B4014947
theorem B1587095 : Blo 1585491 1587095 := bstep (se 1 (by rfl) ⟨1190321, by rfl⟩ : syracuseStep 1587095 = 2380643) B2380643
theorem B3569561 : Blo 1585491 3569561 := bstep (se 2 (by rfl) ⟨1338585, by rfl⟩ : syracuseStep 3569561 = 2677171) B2677171
theorem B1783723 : Blo 1585491 1783723 := bstep (se 1 (by rfl) ⟨1337792, by rfl⟩ : syracuseStep 1783723 = 2675585) B2675585
theorem B1587115 : Blo 1585491 1587115 := bstep (se 1 (by rfl) ⟨1190336, by rfl⟩ : syracuseStep 1587115 = 2380673) B2380673
theorem B8034227 : Blo 1585491 8034227 := bstep (se 1 (by rfl) ⟨6025670, by rfl⟩ : syracuseStep 8034227 = 12051341) B12051341
theorem B1587127 : Blo 1585491 1587127 := bstep (se 1 (by rfl) ⟨1190345, by rfl⟩ : syracuseStep 1587127 = 2380691) B2380691
theorem B1587147 : Blo 1585491 1587147 := bstep (se 1 (by rfl) ⟨1190360, by rfl⟩ : syracuseStep 1587147 = 2380721) B2380721
theorem B1587159 : Blo 1585491 1587159 := bstep (se 1 (by rfl) ⟨1190369, by rfl⟩ : syracuseStep 1587159 = 2380739) B2380739
theorem B1587179 : Blo 1585491 1587179 := bstep (se 1 (by rfl) ⟨1190384, by rfl⟩ : syracuseStep 1587179 = 2380769) B2380769
theorem B3569651 : Blo 1585491 3569651 := bstep (se 1 (by rfl) ⟨2677238, by rfl⟩ : syracuseStep 3569651 = 5354477) B5354477
theorem B1587191 : Blo 1585491 1587191 := bstep (se 1 (by rfl) ⟨1190393, by rfl⟩ : syracuseStep 1587191 = 2380787) B2380787
theorem B1587211 : Blo 1585491 1587211 := bstep (se 1 (by rfl) ⟨1190408, by rfl⟩ : syracuseStep 1587211 = 2380817) B2380817
theorem B6027281 : Blo 1585491 6027281 := bstep (se 2 (by rfl) ⟨2260230, by rfl⟩ : syracuseStep 6027281 = 4520461) B4520461
theorem B1783831 : Blo 1585491 1783831 := bstep (se 1 (by rfl) ⟨1337873, by rfl⟩ : syracuseStep 1783831 = 2675747) B2675747
theorem B4069399 : Blo 1585491 4069399 := bstep (se 1 (by rfl) ⟨3052049, by rfl⟩ : syracuseStep 4069399 = 6104099) B6104099
theorem B3569687 : Blo 1585491 3569687 := bstep (se 1 (by rfl) ⟨2677265, by rfl⟩ : syracuseStep 3569687 = 5354531) B5354531
theorem B1587223 : Blo 1585491 1587223 := bstep (se 1 (by rfl) ⟨1190417, by rfl⟩ : syracuseStep 1587223 = 2380835) B2380835
theorem B4290583 : Blo 1585491 4290583 := bstep (se 1 (by rfl) ⟨3217937, by rfl⟩ : syracuseStep 4290583 = 6435875) B6435875
theorem B1587243 : Blo 1585491 1587243 := bstep (se 1 (by rfl) ⟨1190432, by rfl⟩ : syracuseStep 1587243 = 2380865) B2380865
theorem B1587255 : Blo 1585491 1587255 := bstep (se 1 (by rfl) ⟨1190441, by rfl⟩ : syracuseStep 1587255 = 2380883) B2380883
theorem B32553035 : Blo 1585491 32553035 := bstep (se 1 (by rfl) ⟨24414776, by rfl⟩ : syracuseStep 32553035 = 48829553) B48829553
theorem B1587275 : Blo 1585491 1587275 := bstep (se 1 (by rfl) ⟨1190456, by rfl⟩ : syracuseStep 1587275 = 2380913) B2380913
theorem B1587287 : Blo 1585491 1587287 := bstep (se 1 (by rfl) ⟨1190465, by rfl⟩ : syracuseStep 1587287 = 2380931) B2380931
theorem B1587307 : Blo 1585491 1587307 := bstep (se 1 (by rfl) ⟨1190480, by rfl⟩ : syracuseStep 1587307 = 2380961) B2380961
theorem B1587319 : Blo 1585491 1587319 := bstep (se 1 (by rfl) ⟨1190489, by rfl⟩ : syracuseStep 1587319 = 2380979) B2380979
theorem B6428803 : Blo 1585491 6428803 := bstep (se 1 (by rfl) ⟨4821602, by rfl⟩ : syracuseStep 6428803 = 9643205) B9643205
theorem B11434115 : Blo 1585491 11434115 := bstep (se 1 (by rfl) ⟨8575586, by rfl⟩ : syracuseStep 11434115 = 17151173) B17151173
theorem B1587339 : Blo 1585491 1587339 := bstep (se 1 (by rfl) ⟨1190504, by rfl⟩ : syracuseStep 1587339 = 2381009) B2381009
theorem B1587351 : Blo 1585491 1587351 := bstep (se 1 (by rfl) ⟨1190513, by rfl⟩ : syracuseStep 1587351 = 2381027) B2381027
theorem B1587371 : Blo 1585491 1587371 := bstep (se 1 (by rfl) ⟨1190528, by rfl⟩ : syracuseStep 1587371 = 2381057) B2381057
theorem B1587383 : Blo 1585491 1587383 := bstep (se 1 (by rfl) ⟨1190537, by rfl⟩ : syracuseStep 1587383 = 2381075) B2381075
theorem B1784011 : Blo 1585491 1784011 := bstep (se 1 (by rfl) ⟨1338008, by rfl⟩ : syracuseStep 1784011 = 2676017) B2676017
theorem B3569867 : Blo 1585491 3569867 := bstep (se 1 (by rfl) ⟨2677400, by rfl⟩ : syracuseStep 3569867 = 5354801) B5354801
theorem B1587403 : Blo 1585491 1587403 := bstep (se 1 (by rfl) ⟨1190552, by rfl⟩ : syracuseStep 1587403 = 2381105) B2381105
theorem B1587415 : Blo 1585491 1587415 := bstep (se 1 (by rfl) ⟨1190561, by rfl⟩ : syracuseStep 1587415 = 2381123) B2381123
theorem B1587435 : Blo 1585491 1587435 := bstep (se 1 (by rfl) ⟨1190576, by rfl⟩ : syracuseStep 1587435 = 2381153) B2381153
theorem B3012851 : Blo 1585491 3012851 := bstep (se 1 (by rfl) ⟨2259638, by rfl⟩ : syracuseStep 3012851 = 4519277) B4519277
theorem B1587447 : Blo 1585491 1587447 := bstep (se 1 (by rfl) ⟨1190585, by rfl⟩ : syracuseStep 1587447 = 2381171) B2381171
theorem B3569921 : Blo 1585491 3569921 := bstep (se 2 (by rfl) ⟨1338720, by rfl⟩ : syracuseStep 3569921 = 2677441) B2677441
theorem B1587467 : Blo 1585491 1587467 := bstep (se 1 (by rfl) ⟨1190600, by rfl⟩ : syracuseStep 1587467 = 2381201) B2381201
theorem B1587479 : Blo 1585491 1587479 := bstep (se 1 (by rfl) ⟨1190609, by rfl⟩ : syracuseStep 1587479 = 2381219) B2381219
theorem B3012889 : Blo 1585491 3012889 := bstep (se 2 (by rfl) ⟨1129833, by rfl⟩ : syracuseStep 3012889 = 2259667) B2259667
theorem B5355827 : Blo 1585491 5355827 := bstep (se 1 (by rfl) ⟨4016870, by rfl⟩ : syracuseStep 5355827 = 8033741) B8033741
theorem B1784119 : Blo 1585491 1784119 := bstep (se 1 (by rfl) ⟨1338089, by rfl⟩ : syracuseStep 1784119 = 2676179) B2676179
theorem B2857303 : Blo 1585491 2857303 := bstep (se 1 (by rfl) ⟨2142977, by rfl⟩ : syracuseStep 2857303 = 4285955) B4285955
theorem B1694071 : Blo 1585491 1694071 := bstep (se 1 (by rfl) ⟨1270553, by rfl⟩ : syracuseStep 1694071 = 2541107) B2541107
theorem B13556119 : Blo 1585491 13556119 := bstep (se 1 (by rfl) ⟨10167089, by rfl⟩ : syracuseStep 13556119 = 20334179) B20334179
theorem B1785847 : Blo 1585491 1785847 := bstep (se 1 (by rfl) ⟨1339385, by rfl⟩ : syracuseStep 1785847 = 2678771) B2678771
theorem B3570137 : Blo 1585491 3570137 := bstep (se 2 (by rfl) ⟨1338801, by rfl⟩ : syracuseStep 3570137 = 2677603) B2677603
theorem B1784299 : Blo 1585491 1784299 := bstep (se 1 (by rfl) ⟨1338224, by rfl⟩ : syracuseStep 1784299 = 2676449) B2676449
theorem B3389953 : Blo 1585491 3389953 := bstep (se 2 (by rfl) ⟨1271232, by rfl⟩ : syracuseStep 3389953 = 2542465) B2542465
theorem B2677259 : Blo 1585491 2677259 := bstep (se 1 (by rfl) ⟨2007944, by rfl⟩ : syracuseStep 2677259 = 4015889) B4015889
theorem B3570227 : Blo 1585491 3570227 := bstep (se 1 (by rfl) ⟨2677670, by rfl⟩ : syracuseStep 3570227 = 5355341) B5355341
theorem B5356097 : Blo 1585491 5356097 := bstep (se 2 (by rfl) ⟨2008536, by rfl⟩ : syracuseStep 5356097 = 4017073) B4017073
theorem B10164811 : Blo 1585491 10164811 := bstep (se 1 (by rfl) ⟨7623608, by rfl⟩ : syracuseStep 10164811 = 15247217) B15247217
theorem B1784407 : Blo 1585491 1784407 := bstep (se 1 (by rfl) ⟨1338305, by rfl⟩ : syracuseStep 1784407 = 2676611) B2676611
theorem B3570263 : Blo 1585491 3570263 := bstep (se 1 (by rfl) ⟨2677697, by rfl⟩ : syracuseStep 3570263 = 5355395) B5355395
theorem B15243869 : Blo 1585491 15243869 := bstep (se 3 (by rfl) ⟨2858225, by rfl⟩ : syracuseStep 15243869 = 5716451) B5716451
theorem B2677387 : Blo 1585491 2677387 := bstep (se 1 (by rfl) ⟨2008040, by rfl⟩ : syracuseStep 2677387 = 4016081) B4016081
theorem B8026775 : Blo 1585491 8026775 := bstep (se 1 (by rfl) ⟨6020081, by rfl⟩ : syracuseStep 8026775 = 12040163) B12040163
theorem B4127383 : Blo 1585491 4127383 := bstep (se 1 (by rfl) ⟨3095537, by rfl⟩ : syracuseStep 4127383 = 6191075) B6191075
theorem B5151449 : Blo 1585491 5151449 := bstep (se 2 (by rfl) ⟨1931793, by rfl⟩ : syracuseStep 5151449 = 3863587) B3863587
theorem B3013337 : Blo 1585491 3013337 := bstep (se 2 (by rfl) ⟨1130001, by rfl⟩ : syracuseStep 3013337 = 2260003) B2260003
theorem B1784587 : Blo 1585491 1784587 := bstep (se 1 (by rfl) ⟨1338440, by rfl⟩ : syracuseStep 1784587 = 2676881) B2676881
theorem B3570443 : Blo 1585491 3570443 := bstep (se 1 (by rfl) ⟨2677832, by rfl⟩ : syracuseStep 3570443 = 5355665) B5355665
theorem B2677529 : Blo 1585491 2677529 := bstep (se 2 (by rfl) ⟨1004073, by rfl⟩ : syracuseStep 2677529 = 2008147) B2008147
theorem B3570497 : Blo 1585491 3570497 := bstep (se 2 (by rfl) ⟨1338936, by rfl⟩ : syracuseStep 3570497 = 2677873) B2677873
theorem B3390295 : Blo 1585491 3390295 := bstep (se 1 (by rfl) ⟨2542721, by rfl⟩ : syracuseStep 3390295 = 5085443) B5085443
theorem B1784695 : Blo 1585491 1784695 := bstep (se 1 (by rfl) ⟨1338521, by rfl⟩ : syracuseStep 1784695 = 2677043) B2677043
theorem B6019991 : Blo 1585491 6019991 := bstep (se 1 (by rfl) ⟨4514993, by rfl⟩ : syracuseStep 6019991 = 9029987) B9029987
theorem B2677657 : Blo 1585491 2677657 := bstep (se 2 (by rfl) ⟨1004121, by rfl⟩ : syracuseStep 2677657 = 2008243) B2008243
theorem B18070451 : Blo 1585491 18070451 := bstep (se 1 (by rfl) ⟨13552838, by rfl⟩ : syracuseStep 18070451 = 27105677) B27105677
theorem B2857931 : Blo 1585491 2857931 := bstep (se 1 (by rfl) ⟨2143448, by rfl⟩ : syracuseStep 2857931 = 4286897) B4286897
theorem B2259991 : Blo 1585491 2259991 := bstep (se 1 (by rfl) ⟨1694993, by rfl⟩ : syracuseStep 2259991 = 3389987) B3389987
theorem B3570713 : Blo 1585491 3570713 := bstep (se 2 (by rfl) ⟨1339017, by rfl⟩ : syracuseStep 3570713 = 2678035) B2678035
theorem B1784875 : Blo 1585491 1784875 := bstep (se 1 (by rfl) ⟨1338656, by rfl⟩ : syracuseStep 1784875 = 2677313) B2677313
theorem B6020189 : Blo 1585491 6020189 := bstep (se 3 (by rfl) ⟨1128785, by rfl⟩ : syracuseStep 6020189 = 2257571) B2257571
theorem B5356637 : Blo 1585491 5356637 := bstep (se 3 (by rfl) ⟨1004369, by rfl⟩ : syracuseStep 5356637 = 2008739) B2008739
theorem B3570803 : Blo 1585491 3570803 := bstep (se 1 (by rfl) ⟨2678102, by rfl⟩ : syracuseStep 3570803 = 5356205) B5356205
theorem B5717143 : Blo 1585491 5717143 := bstep (se 1 (by rfl) ⟨4287857, by rfl⟩ : syracuseStep 5717143 = 8575715) B8575715
theorem B1784983 : Blo 1585491 1784983 := bstep (se 1 (by rfl) ⟨1338737, by rfl⟩ : syracuseStep 1784983 = 2677475) B2677475
theorem B3570839 : Blo 1585491 3570839 := bstep (se 1 (by rfl) ⟨2678129, by rfl⟩ : syracuseStep 3570839 = 5356259) B5356259
theorem B1694891 : Blo 1585491 1694891 := bstep (se 1 (by rfl) ⟨1271168, by rfl⟩ : syracuseStep 1694891 = 2542337) B2542337
theorem B1785163 : Blo 1585491 1785163 := bstep (se 1 (by rfl) ⟨1338872, by rfl⟩ : syracuseStep 1785163 = 2677745) B2677745
theorem B3571019 : Blo 1585491 3571019 := bstep (se 1 (by rfl) ⟨2678264, by rfl⟩ : syracuseStep 3571019 = 5356529) B5356529
theorem B3571073 : Blo 1585491 3571073 := bstep (se 2 (by rfl) ⟨1339152, by rfl⟩ : syracuseStep 3571073 = 2678305) B2678305
theorem B3480983 : Blo 1585491 3480983 := bstep (se 1 (by rfl) ⟨2610737, by rfl⟩ : syracuseStep 3480983 = 5221475) B5221475
theorem B10165655 : Blo 1585491 10165655 := bstep (se 1 (by rfl) ⟨7624241, by rfl⟩ : syracuseStep 10165655 = 15248483) B15248483
theorem B5430707 : Blo 1585491 5430707 := bstep (se 1 (by rfl) ⟨4073030, by rfl⟩ : syracuseStep 5430707 = 8146061) B8146061
theorem B1785271 : Blo 1585491 1785271 := bstep (se 1 (by rfl) ⟨1338953, by rfl⟩ : syracuseStep 1785271 = 2677907) B2677907
theorem B2678231 : Blo 1585491 2678231 := bstep (se 1 (by rfl) ⟨2008673, by rfl⟩ : syracuseStep 2678231 = 4017347) B4017347
theorem B9649625 : Blo 1585491 9649625 := bstep (se 2 (by rfl) ⟨3618609, by rfl⟩ : syracuseStep 9649625 = 7237219) B7237219
theorem B2678359 : Blo 1585491 2678359 := bstep (se 1 (by rfl) ⟨2008769, by rfl⟩ : syracuseStep 2678359 = 4017539) B4017539
theorem B3571289 : Blo 1585491 3571289 := bstep (se 2 (by rfl) ⟨1339233, by rfl⟩ : syracuseStep 3571289 = 2678467) B2678467
theorem B1785451 : Blo 1585491 1785451 := bstep (se 1 (by rfl) ⟨1339088, by rfl⟩ : syracuseStep 1785451 = 2678177) B2678177
theorem B3571379 : Blo 1585491 3571379 := bstep (se 1 (by rfl) ⟨2678534, by rfl⟩ : syracuseStep 3571379 = 5357069) B5357069
theorem B1785559 : Blo 1585491 1785559 := bstep (se 1 (by rfl) ⟨1339169, by rfl⟩ : syracuseStep 1785559 = 2678339) B2678339
theorem B3571415 : Blo 1585491 3571415 := bstep (se 1 (by rfl) ⟨2678561, by rfl⟩ : syracuseStep 3571415 = 5357123) B5357123
theorem B2006795 : Blo 1585491 2006795 := bstep (se 1 (by rfl) ⟨1505096, by rfl⟩ : syracuseStep 2006795 = 3010193) B3010193
theorem B4128563 : Blo 1585491 4128563 := bstep (se 1 (by rfl) ⟨3096422, by rfl⟩ : syracuseStep 4128563 = 6192845) B6192845
theorem B8036171 : Blo 1585491 8036171 := bstep (se 1 (by rfl) ⟨6027128, by rfl⟩ : syracuseStep 8036171 = 12054257) B12054257
theorem B1785739 : Blo 1585491 1785739 := bstep (se 1 (by rfl) ⟨1339304, by rfl⟩ : syracuseStep 1785739 = 2678609) B2678609
theorem B3571595 : Blo 1585491 3571595 := bstep (se 1 (by rfl) ⟨2678696, by rfl⟩ : syracuseStep 3571595 = 5357393) B5357393
theorem B7233425 : Blo 1585491 7233425 := bstep (se 2 (by rfl) ⟨2712534, by rfl⟩ : syracuseStep 7233425 = 5425069) B5425069
theorem B4013975 : Blo 1585491 4013975 := bstep (se 1 (by rfl) ⟨3010481, by rfl⟩ : syracuseStep 4013975 = 6020963) B6020963
theorem B3571649 : Blo 1585491 3571649 := bstep (se 2 (by rfl) ⟨1339368, by rfl⟩ : syracuseStep 3571649 = 2678737) B2678737
theorem B9035819 : Blo 1585491 9035819 := bstep (se 1 (by rfl) ⟨6776864, by rfl⟩ : syracuseStep 9035819 = 13553729) B13553729
theorem B2007175 : Blo 1585491 2007175 := bstep (se 1 (by rfl) ⟨1505381, by rfl⟩ : syracuseStep 2007175 = 3010763) B3010763
theorem B3571847 : Blo 1585491 3571847 := bstep (se 1 (by rfl) ⟨2678885, by rfl⟩ : syracuseStep 3571847 = 5357771) B5357771
theorem B13746617 : Blo 1585491 13746617 := bstep (se 2 (by rfl) ⟨5154981, by rfl⟩ : syracuseStep 13746617 = 10309963) B10309963
theorem B3809737 : Blo 1585491 3809737 := bstep (se 2 (by rfl) ⟨1428651, by rfl⟩ : syracuseStep 3809737 = 2857303) B2857303
theorem B4014593 : Blo 1585491 4014593 := bstep (se 2 (by rfl) ⟨1505472, by rfl⟩ : syracuseStep 4014593 = 3010945) B3010945
theorem B6021661 : Blo 1585491 6021661 := bstep (se 3 (by rfl) ⟨1129061, by rfl⟩ : syracuseStep 6021661 = 2258123) B2258123
theorem B2007595 : Blo 1585491 2007595 := bstep (se 1 (by rfl) ⟨1505696, by rfl⟩ : syracuseStep 2007595 = 3011393) B3011393
theorem B2007823 : Blo 1585491 2007823 := bstep (se 1 (by rfl) ⟨1505867, by rfl⟩ : syracuseStep 2007823 = 3011735) B3011735
theorem B8029043 : Blo 1585491 8029043 := bstep (se 1 (by rfl) ⟨6021782, by rfl⟩ : syracuseStep 8029043 = 12043565) B12043565
theorem B4014967 : Blo 1585491 4014967 := bstep (se 1 (by rfl) ⟨3011225, by rfl⟩ : syracuseStep 4014967 = 6022451) B6022451
theorem B14479991 : Blo 1585491 14479991 := bstep (se 1 (by rfl) ⟨10859993, by rfl⟩ : syracuseStep 14479991 = 21719987) B21719987
theorem B5080151 : Blo 1585491 5080151 := bstep (se 1 (by rfl) ⟨3810113, by rfl⟩ : syracuseStep 5080151 = 7620227) B7620227
theorem B6776045 : Blo 1585491 6776045 := bstep (se 3 (by rfl) ⟨1270508, by rfl⟩ : syracuseStep 6776045 = 2541017) B2541017
theorem B25732333 : Blo 1585491 25732333 := bstep (se 3 (by rfl) ⟨4824812, by rfl⟩ : syracuseStep 25732333 = 9649625) B9649625
theorem B4015403 : Blo 1585491 4015403 := bstep (se 1 (by rfl) ⟨3011552, by rfl⟩ : syracuseStep 4015403 = 6023105) B6023105
theorem B8029529 : Blo 1585491 8029529 := bstep (se 2 (by rfl) ⟨3011073, by rfl⟩ : syracuseStep 8029529 = 6022147) B6022147
theorem B21702023 : Blo 1585491 21702023 := bstep (se 1 (by rfl) ⟨16276517, by rfl⟩ : syracuseStep 21702023 = 32553035) B32553035
theorem B10159505 : Blo 1585491 10159505 := bstep (se 2 (by rfl) ⟨3809814, by rfl⟩ : syracuseStep 10159505 = 7619629) B7619629
theorem B9037277 : Blo 1585491 9037277 := bstep (se 3 (by rfl) ⟨1694489, by rfl⟩ : syracuseStep 9037277 = 3388979) B3388979
theorem B2008567 : Blo 1585491 2008567 := bstep (se 1 (by rfl) ⟨1506425, by rfl⟩ : syracuseStep 2008567 = 3012851) B3012851
theorem B5351183 : Blo 1585491 5351183 := bstep (se 1 (by rfl) ⟨4013387, by rfl⟩ : syracuseStep 5351183 = 8026775) B8026775
theorem B2008891 : Blo 1585491 2008891 := bstep (se 1 (by rfl) ⟨1506668, by rfl⟩ : syracuseStep 2008891 = 3013337) B3013337
theorem B12052313 : Blo 1585491 12052313 := bstep (se 2 (by rfl) ⟨4519617, by rfl⟩ : syracuseStep 12052313 = 9039235) B9039235
theorem B6776729 : Blo 1585491 6776729 := bstep (se 2 (by rfl) ⟨2541273, by rfl⟩ : syracuseStep 6776729 = 5082547) B5082547
theorem B9037777 : Blo 1585491 9037777 := bstep (se 2 (by rfl) ⟨3389166, by rfl⟩ : syracuseStep 9037777 = 6778333) B6778333
theorem B5351453 : Blo 1585491 5351453 := bstep (se 3 (by rfl) ⟨1003397, by rfl⟩ : syracuseStep 5351453 = 2006795) B2006795
theorem B4016243 : Blo 1585491 4016243 := bstep (se 1 (by rfl) ⟨3012182, by rfl⟩ : syracuseStep 4016243 = 6024365) B6024365
theorem B4016263 : Blo 1585491 4016263 := bstep (se 1 (by rfl) ⟨3012197, by rfl⟩ : syracuseStep 4016263 = 6024395) B6024395
theorem B2320655 : Blo 1585491 2320655 := bstep (se 1 (by rfl) ⟨1740491, by rfl⟩ : syracuseStep 2320655 = 3480983) B3480983
theorem B6777103 : Blo 1585491 6777103 := bstep (se 1 (by rfl) ⟨5082827, by rfl⟩ : syracuseStep 6777103 = 10165655) B10165655
theorem B13552019 : Blo 1585491 13552019 := bstep (se 1 (by rfl) ⟨10164014, by rfl⟩ : syracuseStep 13552019 = 20328029) B20328029
theorem B4016537 : Blo 1585491 4016537 := bstep (se 2 (by rfl) ⟨1506201, by rfl⟩ : syracuseStep 4016537 = 3012403) B3012403
theorem B2378255 : Blo 1585491 2378255 := bstep (se 1 (by rfl) ⟨1783691, by rfl⟩ : syracuseStep 2378255 = 3567383) B3567383
theorem B2378297 : Blo 1585491 2378297 := bstep (se 2 (by rfl) ⟨891861, by rfl⟩ : syracuseStep 2378297 = 1783723) B1783723
theorem B4016699 : Blo 1585491 4016699 := bstep (se 1 (by rfl) ⟨3012524, by rfl⟩ : syracuseStep 4016699 = 6025049) B6025049
theorem B2378375 : Blo 1585491 2378375 := bstep (se 1 (by rfl) ⟨1783781, by rfl⟩ : syracuseStep 2378375 = 3567563) B3567563
theorem B2378411 : Blo 1585491 2378411 := bstep (se 1 (by rfl) ⟨1783808, by rfl⟩ : syracuseStep 2378411 = 3567617) B3567617
theorem B2378441 : Blo 1585491 2378441 := bstep (se 2 (by rfl) ⟨891915, by rfl⟩ : syracuseStep 2378441 = 1783831) B1783831
theorem B5425865 : Blo 1585491 5425865 := bstep (se 2 (by rfl) ⟨2034699, by rfl⟩ : syracuseStep 5425865 = 4069399) B4069399
theorem B5720777 : Blo 1585491 5720777 := bstep (se 2 (by rfl) ⟨2145291, by rfl⟩ : syracuseStep 5720777 = 4290583) B4290583
theorem B4016911 : Blo 1585491 4016911 := bstep (se 1 (by rfl) ⟨3012683, by rfl⟩ : syracuseStep 4016911 = 6025367) B6025367
theorem B58714895 : Blo 1585491 58714895 := bstep (se 1 (by rfl) ⟨44036171, by rfl⟩ : syracuseStep 58714895 = 88072343) B88072343
theorem B22866725 : Blo 1585491 22866725 := bstep (se 4 (by rfl) ⟨2143755, by rfl⟩ : syracuseStep 22866725 = 4287511) B4287511
theorem B12053285 : Blo 1585491 12053285 := bstep (se 4 (by rfl) ⟨1129995, by rfl⟩ : syracuseStep 12053285 = 2259991) B2259991
theorem B2378555 : Blo 1585491 2378555 := bstep (se 1 (by rfl) ⟨1783916, by rfl⟩ : syracuseStep 2378555 = 3567833) B3567833
theorem B8571737 : Blo 1585491 8571737 := bstep (se 2 (by rfl) ⟨3214401, by rfl⟩ : syracuseStep 8571737 = 6428803) B6428803
theorem B2378615 : Blo 1585491 2378615 := bstep (se 1 (by rfl) ⟨1783961, by rfl⟩ : syracuseStep 2378615 = 3567923) B3567923
theorem B2378639 : Blo 1585491 2378639 := bstep (se 1 (by rfl) ⟨1783979, by rfl⟩ : syracuseStep 2378639 = 3567959) B3567959
theorem B2378681 : Blo 1585491 2378681 := bstep (se 2 (by rfl) ⟨892005, by rfl⟩ : syracuseStep 2378681 = 1784011) B1784011
theorem B4516793 : Blo 1585491 4516793 := bstep (se 2 (by rfl) ⟨1693797, by rfl⟩ : syracuseStep 4516793 = 3387595) B3387595
theorem B2378759 : Blo 1585491 2378759 := bstep (se 1 (by rfl) ⟨1784069, by rfl⟩ : syracuseStep 2378759 = 3568139) B3568139
theorem B4017185 : Blo 1585491 4017185 := bstep (se 2 (by rfl) ⟨1506444, by rfl⟩ : syracuseStep 4017185 = 3012889) B3012889
theorem B2378795 : Blo 1585491 2378795 := bstep (se 1 (by rfl) ⟨1784096, by rfl⟩ : syracuseStep 2378795 = 3568193) B3568193
theorem B2378825 : Blo 1585491 2378825 := bstep (se 2 (by rfl) ⟨892059, by rfl⟩ : syracuseStep 2378825 = 1784119) B1784119
theorem B2378939 : Blo 1585491 2378939 := bstep (se 1 (by rfl) ⟨1784204, by rfl⟩ : syracuseStep 2378939 = 3568409) B3568409
theorem B18074825 : Blo 1585491 18074825 := bstep (se 2 (by rfl) ⟨6778059, by rfl⟩ : syracuseStep 18074825 = 13556119) B13556119
theorem B2378999 : Blo 1585491 2378999 := bstep (se 1 (by rfl) ⟨1784249, by rfl⟩ : syracuseStep 2378999 = 3568499) B3568499
theorem B2379023 : Blo 1585491 2379023 := bstep (se 1 (by rfl) ⟨1784267, by rfl⟩ : syracuseStep 2379023 = 3568535) B3568535
theorem B2379065 : Blo 1585491 2379065 := bstep (se 2 (by rfl) ⟨892149, by rfl⟩ : syracuseStep 2379065 = 1784299) B1784299
theorem B6024563 : Blo 1585491 6024563 := bstep (se 1 (by rfl) ⟨4518422, by rfl⟩ : syracuseStep 6024563 = 9036845) B9036845
theorem B8146291 : Blo 1585491 8146291 := bstep (se 1 (by rfl) ⟨6109718, by rfl⟩ : syracuseStep 8146291 = 12219437) B12219437
theorem B2379143 : Blo 1585491 2379143 := bstep (se 1 (by rfl) ⟨1784357, by rfl⟩ : syracuseStep 2379143 = 3568715) B3568715
theorem B8031635 : Blo 1585491 8031635 := bstep (se 1 (by rfl) ⟨6023726, by rfl⟩ : syracuseStep 8031635 = 12047453) B12047453
theorem B5352857 : Blo 1585491 5352857 := bstep (se 2 (by rfl) ⟨2007321, by rfl⟩ : syracuseStep 5352857 = 4014643) B4014643
theorem B2379179 : Blo 1585491 2379179 := bstep (se 1 (by rfl) ⟨1784384, by rfl⟩ : syracuseStep 2379179 = 3568769) B3568769
theorem B3386809 : Blo 1585491 3386809 := bstep (se 2 (by rfl) ⟨1270053, by rfl⟩ : syracuseStep 3386809 = 2540107) B2540107
theorem B13553081 : Blo 1585491 13553081 := bstep (se 2 (by rfl) ⟨5082405, by rfl⟩ : syracuseStep 13553081 = 10164811) B10164811
theorem B2379209 : Blo 1585491 2379209 := bstep (se 2 (by rfl) ⟨892203, by rfl⟩ : syracuseStep 2379209 = 1784407) B1784407
theorem B2379323 : Blo 1585491 2379323 := bstep (se 1 (by rfl) ⟨1784492, by rfl⟩ : syracuseStep 2379323 = 3568985) B3568985
theorem B2379383 : Blo 1585491 2379383 := bstep (se 1 (by rfl) ⟨1784537, by rfl⟩ : syracuseStep 2379383 = 3569075) B3569075
theorem B2379407 : Blo 1585491 2379407 := bstep (se 1 (by rfl) ⟨1784555, by rfl⟩ : syracuseStep 2379407 = 3569111) B3569111
theorem B2379449 : Blo 1585491 2379449 := bstep (se 2 (by rfl) ⟨892293, by rfl⟩ : syracuseStep 2379449 = 1784587) B1784587
theorem B2379527 : Blo 1585491 2379527 := bstep (se 1 (by rfl) ⟨1784645, by rfl⟩ : syracuseStep 2379527 = 3569291) B3569291
theorem B2379563 : Blo 1585491 2379563 := bstep (se 1 (by rfl) ⟨1784672, by rfl⟩ : syracuseStep 2379563 = 3569345) B3569345
theorem B48844595 : Blo 1585491 48844595 := bstep (se 1 (by rfl) ⟨36633446, by rfl⟩ : syracuseStep 48844595 = 73266893) B73266893
theorem B3567419 : Blo 1585491 3567419 := bstep (se 1 (by rfl) ⟨2675564, by rfl⟩ : syracuseStep 3567419 = 5351129) B5351129
theorem B2379593 : Blo 1585491 2379593 := bstep (se 2 (by rfl) ⟨892347, by rfl⟩ : syracuseStep 2379593 = 1784695) B1784695
theorem B3387271 : Blo 1585491 3387271 := bstep (se 1 (by rfl) ⟨2540453, by rfl⟩ : syracuseStep 3387271 = 5080907) B5080907
theorem B9039761 : Blo 1585491 9039761 := bstep (se 2 (by rfl) ⟨3389910, by rfl⟩ : syracuseStep 9039761 = 6779821) B6779821
theorem B5083033 : Blo 1585491 5083033 := bstep (se 2 (by rfl) ⟨1906137, by rfl⟩ : syracuseStep 5083033 = 3812275) B3812275
theorem B3567545 : Blo 1585491 3567545 := bstep (se 2 (by rfl) ⟨1337829, by rfl⟩ : syracuseStep 3567545 = 2675659) B2675659
theorem B2379707 : Blo 1585491 2379707 := bstep (se 1 (by rfl) ⟨1784780, by rfl⟩ : syracuseStep 2379707 = 3569561) B3569561
theorem B2379767 : Blo 1585491 2379767 := bstep (se 1 (by rfl) ⟨1784825, by rfl⟩ : syracuseStep 2379767 = 3569651) B3569651
theorem B4018187 : Blo 1585491 4018187 := bstep (se 1 (by rfl) ⟨3013640, by rfl⟩ : syracuseStep 4018187 = 6027281) B6027281
theorem B2379791 : Blo 1585491 2379791 := bstep (se 1 (by rfl) ⟨1784843, by rfl⟩ : syracuseStep 2379791 = 3569687) B3569687
theorem B3010603 : Blo 1585491 3010603 := bstep (se 1 (by rfl) ⟨2257952, by rfl⟩ : syracuseStep 3010603 = 4515905) B4515905
theorem B9646123 : Blo 1585491 9646123 := bstep (se 1 (by rfl) ⟨7234592, by rfl⟩ : syracuseStep 9646123 = 14469185) B14469185
theorem B2379833 : Blo 1585491 2379833 := bstep (se 2 (by rfl) ⟨892437, by rfl⟩ : syracuseStep 2379833 = 1784875) B1784875
theorem B5353559 : Blo 1585491 5353559 := bstep (se 1 (by rfl) ⟨4015169, by rfl⟩ : syracuseStep 5353559 = 8030339) B8030339
theorem B7622743 : Blo 1585491 7622743 := bstep (se 1 (by rfl) ⟨5717057, by rfl⟩ : syracuseStep 7622743 = 11434115) B11434115
theorem B3010679 : Blo 1585491 3010679 := bstep (se 1 (by rfl) ⟨2258009, by rfl⟩ : syracuseStep 3010679 = 4516019) B4516019
theorem B2379911 : Blo 1585491 2379911 := bstep (se 1 (by rfl) ⟨1784933, by rfl⟩ : syracuseStep 2379911 = 3569867) B3569867
theorem B2379947 : Blo 1585491 2379947 := bstep (se 1 (by rfl) ⟨1784960, by rfl⟩ : syracuseStep 2379947 = 3569921) B3569921
theorem B7622857 : Blo 1585491 7622857 := bstep (se 2 (by rfl) ⟨2858571, by rfl⟩ : syracuseStep 7622857 = 5717143) B5717143
theorem B2379977 : Blo 1585491 2379977 := bstep (se 2 (by rfl) ⟨892491, by rfl⟩ : syracuseStep 2379977 = 1784983) B1784983
theorem B3567887 : Blo 1585491 3567887 := bstep (se 1 (by rfl) ⟨2675915, by rfl⟩ : syracuseStep 3567887 = 5351831) B5351831
theorem B3567905 : Blo 1585491 3567905 := bstep (se 2 (by rfl) ⟨1337964, by rfl⟩ : syracuseStep 3567905 = 2675929) B2675929
theorem B2380091 : Blo 1585491 2380091 := bstep (se 1 (by rfl) ⟨1785068, by rfl⟩ : syracuseStep 2380091 = 3570137) B3570137
theorem B2380151 : Blo 1585491 2380151 := bstep (se 1 (by rfl) ⟨1785113, by rfl⟩ : syracuseStep 2380151 = 3570227) B3570227
theorem B1585543 : Blo 1585491 1585543 := bstep (se 1 (by rfl) ⟨1189157, by rfl⟩ : syracuseStep 1585543 = 2378315) B2378315
theorem B1585551 : Blo 1585491 1585551 := bstep (se 1 (by rfl) ⟨1189163, by rfl⟩ : syracuseStep 1585551 = 2378327) B2378327
theorem B2380175 : Blo 1585491 2380175 := bstep (se 1 (by rfl) ⟨1785131, by rfl⟩ : syracuseStep 2380175 = 3570263) B3570263
theorem B10162579 : Blo 1585491 10162579 := bstep (se 1 (by rfl) ⟨7621934, by rfl⟩ : syracuseStep 10162579 = 15243869) B15243869
theorem B6107545 : Blo 1585491 6107545 := bstep (se 2 (by rfl) ⟨2290329, by rfl⟩ : syracuseStep 6107545 = 4580659) B4580659
theorem B17150393 : Blo 1585491 17150393 := bstep (se 2 (by rfl) ⟨6431397, by rfl⟩ : syracuseStep 17150393 = 12862795) B12862795
theorem B2380217 : Blo 1585491 2380217 := bstep (se 2 (by rfl) ⟨892581, by rfl⟩ : syracuseStep 2380217 = 1785163) B1785163
theorem B1585595 : Blo 1585491 1585595 := bstep (se 1 (by rfl) ⟨1189196, by rfl⟩ : syracuseStep 1585595 = 2378393) B2378393
theorem B15249869 : Blo 1585491 15249869 := bstep (se 3 (by rfl) ⟨2859350, by rfl⟩ : syracuseStep 15249869 = 5718701) B5718701
theorem B19296721 : Blo 1585491 19296721 := bstep (se 2 (by rfl) ⟨7236270, by rfl⟩ : syracuseStep 19296721 = 14472541) B14472541
theorem B3813889 : Blo 1585491 3813889 := bstep (se 2 (by rfl) ⟨1430208, by rfl⟩ : syracuseStep 3813889 = 2860417) B2860417
theorem B1585671 : Blo 1585491 1585671 := bstep (se 1 (by rfl) ⟨1189253, by rfl⟩ : syracuseStep 1585671 = 2378507) B2378507
theorem B2380295 : Blo 1585491 2380295 := bstep (se 1 (by rfl) ⟨1785221, by rfl⟩ : syracuseStep 2380295 = 3570443) B3570443
theorem B1585679 : Blo 1585491 1585679 := bstep (se 1 (by rfl) ⟨1189259, by rfl⟩ : syracuseStep 1585679 = 2378519) B2378519
theorem B4518433 : Blo 1585491 4518433 := bstep (se 2 (by rfl) ⟨1694412, by rfl⟩ : syracuseStep 4518433 = 3388825) B3388825
theorem B2380331 : Blo 1585491 2380331 := bstep (se 1 (by rfl) ⟨1785248, by rfl⟩ : syracuseStep 2380331 = 3570497) B3570497
theorem B1585723 : Blo 1585491 1585723 := bstep (se 1 (by rfl) ⟨1189292, by rfl⟩ : syracuseStep 1585723 = 2378585) B2378585
theorem B5354045 : Blo 1585491 5354045 := bstep (se 3 (by rfl) ⟨1003883, by rfl⟩ : syracuseStep 5354045 = 2007767) B2007767
theorem B2380361 : Blo 1585491 2380361 := bstep (se 2 (by rfl) ⟨892635, by rfl⟩ : syracuseStep 2380361 = 1785271) B1785271
theorem B3568247 : Blo 1585491 3568247 := bstep (se 1 (by rfl) ⟨2676185, by rfl⟩ : syracuseStep 3568247 = 5352371) B5352371
theorem B12046967 : Blo 1585491 12046967 := bstep (se 1 (by rfl) ⟨9035225, by rfl⟩ : syracuseStep 12046967 = 18070451) B18070451
theorem B1585799 : Blo 1585491 1585799 := bstep (se 1 (by rfl) ⟨1189349, by rfl⟩ : syracuseStep 1585799 = 2378699) B2378699
theorem B1905287 : Blo 1585491 1905287 := bstep (se 1 (by rfl) ⟨1428965, by rfl⟩ : syracuseStep 1905287 = 2857931) B2857931
theorem B1585807 : Blo 1585491 1585807 := bstep (se 1 (by rfl) ⟨1189355, by rfl⟩ : syracuseStep 1585807 = 2378711) B2378711
theorem B1585851 : Blo 1585491 1585851 := bstep (se 1 (by rfl) ⟨1189388, by rfl⟩ : syracuseStep 1585851 = 2378777) B2378777
theorem B2380475 : Blo 1585491 2380475 := bstep (se 1 (by rfl) ⟨1785356, by rfl⟩ : syracuseStep 2380475 = 3570713) B3570713
theorem B2380535 : Blo 1585491 2380535 := bstep (se 1 (by rfl) ⟨1785401, by rfl⟩ : syracuseStep 2380535 = 3570803) B3570803
theorem B1585927 : Blo 1585491 1585927 := bstep (se 1 (by rfl) ⟨1189445, by rfl⟩ : syracuseStep 1585927 = 2378891) B2378891
theorem B2257679 : Blo 1585491 2257679 := bstep (se 1 (by rfl) ⟨1693259, by rfl⟩ : syracuseStep 2257679 = 3386519) B3386519
theorem B1585935 : Blo 1585491 1585935 := bstep (se 1 (by rfl) ⟨1189451, by rfl⟩ : syracuseStep 1585935 = 2378903) B2378903
theorem B2380559 : Blo 1585491 2380559 := bstep (se 1 (by rfl) ⟨1785419, by rfl⟩ : syracuseStep 2380559 = 3570839) B3570839
theorem B8581925 : Blo 1585491 8581925 := bstep (se 4 (by rfl) ⟨804555, by rfl⟩ : syracuseStep 8581925 = 1609111) B1609111
theorem B3568427 : Blo 1585491 3568427 := bstep (se 1 (by rfl) ⟨2676320, by rfl⟩ : syracuseStep 3568427 = 5352641) B5352641
theorem B2380601 : Blo 1585491 2380601 := bstep (se 2 (by rfl) ⟨892725, by rfl⟩ : syracuseStep 2380601 = 1785451) B1785451
theorem B1585979 : Blo 1585491 1585979 := bstep (se 1 (by rfl) ⟨1189484, by rfl⟩ : syracuseStep 1585979 = 2378969) B2378969
theorem B1586055 : Blo 1585491 1586055 := bstep (se 1 (by rfl) ⟨1189541, by rfl⟩ : syracuseStep 1586055 = 2379083) B2379083
theorem B2380679 : Blo 1585491 2380679 := bstep (se 1 (by rfl) ⟨1785509, by rfl⟩ : syracuseStep 2380679 = 3571019) B3571019
theorem B1586063 : Blo 1585491 1586063 := bstep (se 1 (by rfl) ⟨1189547, by rfl⟩ : syracuseStep 1586063 = 2379095) B2379095
theorem B2380715 : Blo 1585491 2380715 := bstep (se 1 (by rfl) ⟨1785536, by rfl⟩ : syracuseStep 2380715 = 3571073) B3571073
theorem B1586107 : Blo 1585491 1586107 := bstep (se 1 (by rfl) ⟨1189580, by rfl⟩ : syracuseStep 1586107 = 2379161) B2379161
theorem B2380745 : Blo 1585491 2380745 := bstep (se 2 (by rfl) ⟨892779, by rfl⟩ : syracuseStep 2380745 = 1785559) B1785559
theorem B1586183 : Blo 1585491 1586183 := bstep (se 1 (by rfl) ⟨1189637, by rfl⟩ : syracuseStep 1586183 = 2379275) B2379275
theorem B1586191 : Blo 1585491 1586191 := bstep (se 1 (by rfl) ⟨1189643, by rfl⟩ : syracuseStep 1586191 = 2379287) B2379287
theorem B1586235 : Blo 1585491 1586235 := bstep (se 1 (by rfl) ⟨1189676, by rfl⟩ : syracuseStep 1586235 = 2379353) B2379353
theorem B2380859 : Blo 1585491 2380859 := bstep (se 1 (by rfl) ⟨1785644, by rfl⟩ : syracuseStep 2380859 = 3571289) B3571289
theorem B5715011 : Blo 1585491 5715011 := bstep (se 1 (by rfl) ⟨4286258, by rfl⟩ : syracuseStep 5715011 = 8572517) B8572517
theorem B2380919 : Blo 1585491 2380919 := bstep (se 1 (by rfl) ⟨1785689, by rfl⟩ : syracuseStep 2380919 = 3571379) B3571379
theorem B1586311 : Blo 1585491 1586311 := bstep (se 1 (by rfl) ⟨1189733, by rfl⟩ : syracuseStep 1586311 = 2379467) B2379467
theorem B1586319 : Blo 1585491 1586319 := bstep (se 1 (by rfl) ⟨1189739, by rfl⟩ : syracuseStep 1586319 = 2379479) B2379479
theorem B3568787 : Blo 1585491 3568787 := bstep (se 1 (by rfl) ⟨2676590, by rfl⟩ : syracuseStep 3568787 = 5353181) B5353181
theorem B2380943 : Blo 1585491 2380943 := bstep (se 1 (by rfl) ⟨1785707, by rfl⟩ : syracuseStep 2380943 = 3571415) B3571415
theorem B18560173 : Blo 1585491 18560173 := bstep (se 3 (by rfl) ⟨3480032, by rfl⟩ : syracuseStep 18560173 = 6960065) B6960065
theorem B2380985 : Blo 1585491 2380985 := bstep (se 2 (by rfl) ⟨892869, by rfl⟩ : syracuseStep 2380985 = 1785739) B1785739
theorem B1586363 : Blo 1585491 1586363 := bstep (se 1 (by rfl) ⟨1189772, by rfl⟩ : syracuseStep 1586363 = 2379545) B2379545
theorem B3568841 : Blo 1585491 3568841 := bstep (se 2 (by rfl) ⟨1338315, by rfl⟩ : syracuseStep 3568841 = 2676631) B2676631
theorem B1586439 : Blo 1585491 1586439 := bstep (se 1 (by rfl) ⟨1189829, by rfl⟩ : syracuseStep 1586439 = 2379659) B2379659
theorem B2381063 : Blo 1585491 2381063 := bstep (se 1 (by rfl) ⟨1785797, by rfl⟩ : syracuseStep 2381063 = 3571595) B3571595
theorem B4822283 : Blo 1585491 4822283 := bstep (se 1 (by rfl) ⟨3616712, by rfl⟩ : syracuseStep 4822283 = 7233425) B7233425
theorem B2675983 : Blo 1585491 2675983 := bstep (se 1 (by rfl) ⟨2006987, by rfl⟩ : syracuseStep 2675983 = 4013975) B4013975
theorem B1586447 : Blo 1585491 1586447 := bstep (se 1 (by rfl) ⟨1189835, by rfl⟩ : syracuseStep 1586447 = 2379671) B2379671
theorem B2381099 : Blo 1585491 2381099 := bstep (se 1 (by rfl) ⟨1785824, by rfl⟩ : syracuseStep 2381099 = 3571649) B3571649
theorem B1586491 : Blo 1585491 1586491 := bstep (se 1 (by rfl) ⟨1189868, by rfl⟩ : syracuseStep 1586491 = 2379737) B2379737
theorem B2381129 : Blo 1585491 2381129 := bstep (se 2 (by rfl) ⟨892923, by rfl⟩ : syracuseStep 2381129 = 1785847) B1785847
theorem B1586567 : Blo 1585491 1586567 := bstep (se 1 (by rfl) ⟨1189925, by rfl⟩ : syracuseStep 1586567 = 2379851) B2379851
theorem B1586575 : Blo 1585491 1586575 := bstep (se 1 (by rfl) ⟨1189931, by rfl⟩ : syracuseStep 1586575 = 2379863) B2379863
theorem B9278873 : Blo 1585491 9278873 := bstep (se 2 (by rfl) ⟨3479577, by rfl⟩ : syracuseStep 9278873 = 6959155) B6959155
theorem B1586619 : Blo 1585491 1586619 := bstep (se 1 (by rfl) ⟨1189964, by rfl⟩ : syracuseStep 1586619 = 2379929) B2379929
theorem B1586695 : Blo 1585491 1586695 := bstep (se 1 (by rfl) ⟨1190021, by rfl⟩ : syracuseStep 1586695 = 2380043) B2380043
theorem B4068875 : Blo 1585491 4068875 := bstep (se 1 (by rfl) ⟨3051656, by rfl⟩ : syracuseStep 4068875 = 6103313) B6103313
theorem B1586703 : Blo 1585491 1586703 := bstep (se 1 (by rfl) ⟨1190027, by rfl⟩ : syracuseStep 1586703 = 2380055) B2380055
theorem B6026795 : Blo 1585491 6026795 := bstep (se 1 (by rfl) ⟨4520096, by rfl⟩ : syracuseStep 6026795 = 9040193) B9040193
theorem B1586747 : Blo 1585491 1586747 := bstep (se 1 (by rfl) ⟨1190060, by rfl⟩ : syracuseStep 1586747 = 2380121) B2380121
theorem B12047939 : Blo 1585491 12047939 := bstep (se 1 (by rfl) ⟨9035954, by rfl⟩ : syracuseStep 12047939 = 18071909) B18071909
theorem B22877797 : Blo 1585491 22877797 := bstep (se 4 (by rfl) ⟨2144793, by rfl⟩ : syracuseStep 22877797 = 4289587) B4289587
theorem B1693319 : Blo 1585491 1693319 := bstep (se 1 (by rfl) ⟨1269989, by rfl⟩ : syracuseStep 1693319 = 2539979) B2539979
theorem B1586823 : Blo 1585491 1586823 := bstep (se 1 (by rfl) ⟨1190117, by rfl⟩ : syracuseStep 1586823 = 2380235) B2380235
theorem B1717895 : Blo 1585491 1717895 := bstep (se 1 (by rfl) ⟨1288421, by rfl⟩ : syracuseStep 1717895 = 2576843) B2576843
theorem B1586831 : Blo 1585491 1586831 := bstep (se 1 (by rfl) ⟨1190123, by rfl⟩ : syracuseStep 1586831 = 2380247) B2380247
theorem B1586875 : Blo 1585491 1586875 := bstep (se 1 (by rfl) ⟨1190156, by rfl⟩ : syracuseStep 1586875 = 2380313) B2380313
theorem B1586951 : Blo 1585491 1586951 := bstep (se 1 (by rfl) ⟨1190213, by rfl⟩ : syracuseStep 1586951 = 2380427) B2380427
theorem B1586959 : Blo 1585491 1586959 := bstep (se 1 (by rfl) ⟨1190219, by rfl⟩ : syracuseStep 1586959 = 2380439) B2380439
theorem B4519709 : Blo 1585491 4519709 := bstep (se 3 (by rfl) ⟨847445, by rfl⟩ : syracuseStep 4519709 = 1694891) B1694891
theorem B2676523 : Blo 1585491 2676523 := bstep (se 1 (by rfl) ⟨2007392, by rfl⟩ : syracuseStep 2676523 = 4014785) B4014785
theorem B1587003 : Blo 1585491 1587003 := bstep (se 1 (by rfl) ⟨1190252, by rfl⟩ : syracuseStep 1587003 = 2380505) B2380505
theorem B2258761 : Blo 1585491 2258761 := bstep (se 2 (by rfl) ⟨847035, by rfl⟩ : syracuseStep 2258761 = 1694071) B1694071
theorem B10860403 : Blo 1585491 10860403 := bstep (se 1 (by rfl) ⟨8145302, by rfl⟩ : syracuseStep 10860403 = 16290605) B16290605
theorem B1783687 : Blo 1585491 1783687 := bstep (se 1 (by rfl) ⟨1337765, by rfl⟩ : syracuseStep 1783687 = 2675531) B2675531
theorem B3569543 : Blo 1585491 3569543 := bstep (se 1 (by rfl) ⟨2677157, by rfl⟩ : syracuseStep 3569543 = 5354315) B5354315
theorem B1587079 : Blo 1585491 1587079 := bstep (se 1 (by rfl) ⟨1190309, by rfl⟩ : syracuseStep 1587079 = 2380619) B2380619
theorem B1587087 : Blo 1585491 1587087 := bstep (se 1 (by rfl) ⟨1190315, by rfl⟩ : syracuseStep 1587087 = 2380631) B2380631
theorem B2676665 : Blo 1585491 2676665 := bstep (se 2 (by rfl) ⟨1003749, by rfl⟩ : syracuseStep 2676665 = 2007499) B2007499
theorem B5355449 : Blo 1585491 5355449 := bstep (se 2 (by rfl) ⟨2008293, by rfl⟩ : syracuseStep 5355449 = 4016587) B4016587
theorem B2258875 : Blo 1585491 2258875 := bstep (se 1 (by rfl) ⟨1694156, by rfl⟩ : syracuseStep 2258875 = 3388313) B3388313
theorem B1587131 : Blo 1585491 1587131 := bstep (se 1 (by rfl) ⟨1190348, by rfl⟩ : syracuseStep 1587131 = 2380697) B2380697
theorem B4519937 : Blo 1585491 4519937 := bstep (se 2 (by rfl) ⟨1694976, by rfl⟩ : syracuseStep 4519937 = 3389953) B3389953
theorem B1587207 : Blo 1585491 1587207 := bstep (se 1 (by rfl) ⟨1190405, by rfl⟩ : syracuseStep 1587207 = 2380811) B2380811
theorem B3012623 : Blo 1585491 3012623 := bstep (se 1 (by rfl) ⟨2259467, by rfl⟩ : syracuseStep 3012623 = 4518935) B4518935
theorem B1587215 : Blo 1585491 1587215 := bstep (se 1 (by rfl) ⟨1190411, by rfl⟩ : syracuseStep 1587215 = 2380823) B2380823
theorem B18077741 : Blo 1585491 18077741 := bstep (se 3 (by rfl) ⟨3389576, by rfl⟩ : syracuseStep 18077741 = 6779153) B6779153
theorem B1783867 : Blo 1585491 1783867 := bstep (se 1 (by rfl) ⟨1337900, by rfl⟩ : syracuseStep 1783867 = 2675801) B2675801
theorem B3569723 : Blo 1585491 3569723 := bstep (se 1 (by rfl) ⟨2677292, by rfl⟩ : syracuseStep 3569723 = 5354585) B5354585
theorem B1587259 : Blo 1585491 1587259 := bstep (se 1 (by rfl) ⟨1190444, by rfl⟩ : syracuseStep 1587259 = 2380889) B2380889
theorem B1587335 : Blo 1585491 1587335 := bstep (se 1 (by rfl) ⟨1190501, by rfl⟩ : syracuseStep 1587335 = 2381003) B2381003
theorem B1587343 : Blo 1585491 1587343 := bstep (se 1 (by rfl) ⟨1190507, by rfl⟩ : syracuseStep 1587343 = 2381015) B2381015
theorem B3569849 : Blo 1585491 3569849 := bstep (se 2 (by rfl) ⟨1338693, by rfl⟩ : syracuseStep 3569849 = 2677387) B2677387
theorem B1693883 : Blo 1585491 1693883 := bstep (se 1 (by rfl) ⟨1270412, by rfl⟩ : syracuseStep 1693883 = 2540825) B2540825
theorem B1587387 : Blo 1585491 1587387 := bstep (se 1 (by rfl) ⟨1190540, by rfl⟩ : syracuseStep 1587387 = 2381081) B2381081
theorem B9033929 : Blo 1585491 9033929 := bstep (se 2 (by rfl) ⟨3387723, by rfl⟩ : syracuseStep 9033929 = 6775447) B6775447
theorem B5503177 : Blo 1585491 5503177 := bstep (se 2 (by rfl) ⟨2063691, by rfl⟩ : syracuseStep 5503177 = 4127383) B4127383
theorem B1587463 : Blo 1585491 1587463 := bstep (se 1 (by rfl) ⟨1190597, by rfl⟩ : syracuseStep 1587463 = 2381195) B2381195
theorem B69556493 : Blo 1585491 69556493 := bstep (se 3 (by rfl) ⟨13041842, by rfl⟩ : syracuseStep 69556493 = 26083685) B26083685
theorem B1587471 : Blo 1585491 1587471 := bstep (se 1 (by rfl) ⟨1190603, by rfl⟩ : syracuseStep 1587471 = 2381207) B2381207
theorem B12859681 : Blo 1585491 12859681 := bstep (se 2 (by rfl) ⟨4822380, by rfl⟩ : syracuseStep 12859681 = 9644761) B9644761
theorem B4520279 : Blo 1585491 4520279 := bstep (se 1 (by rfl) ⟨3390209, by rfl⟩ : syracuseStep 4520279 = 6780419) B6780419
theorem B18061703 : Blo 1585491 18061703 := bstep (se 1 (by rfl) ⟨13546277, by rfl⟩ : syracuseStep 18061703 = 27092555) B27092555
theorem B3389843 : Blo 1585491 3389843 := bstep (se 1 (by rfl) ⟨2542382, by rfl⟩ : syracuseStep 3389843 = 5084765) B5084765
theorem B8034713 : Blo 1585491 8034713 := bstep (se 2 (by rfl) ⟨3013017, by rfl⟩ : syracuseStep 8034713 = 6026035) B6026035
theorem B4520393 : Blo 1585491 4520393 := bstep (se 2 (by rfl) ⟨1695147, by rfl⟩ : syracuseStep 4520393 = 3390295) B3390295
theorem B5356043 : Blo 1585491 5356043 := bstep (se 1 (by rfl) ⟨4017032, by rfl⟩ : syracuseStep 5356043 = 8034065) B8034065
theorem B1784335 : Blo 1585491 1784335 := bstep (se 1 (by rfl) ⟨1338251, by rfl⟩ : syracuseStep 1784335 = 2676503) B2676503
theorem B3570191 : Blo 1585491 3570191 := bstep (se 1 (by rfl) ⟨2677643, by rfl⟩ : syracuseStep 3570191 = 5355287) B5355287
theorem B3570209 : Blo 1585491 3570209 := bstep (se 2 (by rfl) ⟨1338828, by rfl⟩ : syracuseStep 3570209 = 2677657) B2677657
theorem B2677367 : Blo 1585491 2677367 := bstep (se 1 (by rfl) ⟨2008025, by rfl⟩ : syracuseStep 2677367 = 4016051) B4016051
theorem B5356151 : Blo 1585491 5356151 := bstep (se 1 (by rfl) ⟨4017113, by rfl⟩ : syracuseStep 5356151 = 8034227) B8034227
theorem B30505733 : Blo 1585491 30505733 := bstep (se 4 (by rfl) ⟨2859912, by rfl⟩ : syracuseStep 30505733 = 5719825) B5719825
theorem B6871823 : Blo 1585491 6871823 := bstep (se 1 (by rfl) ⟨5153867, by rfl⟩ : syracuseStep 6871823 = 10307735) B10307735
theorem B25787173 : Blo 1585491 25787173 := bstep (se 4 (by rfl) ⟨2417547, by rfl⟩ : syracuseStep 25787173 = 4835095) B4835095
theorem B3570551 : Blo 1585491 3570551 := bstep (se 1 (by rfl) ⟨2677913, by rfl⟩ : syracuseStep 3570551 = 5355827) B5355827
theorem B1784839 : Blo 1585491 1784839 := bstep (se 1 (by rfl) ⟨1338629, by rfl⟩ : syracuseStep 1784839 = 2677259) B2677259
theorem B3570731 : Blo 1585491 3570731 := bstep (se 1 (by rfl) ⟨2678048, by rfl⟩ : syracuseStep 3570731 = 5356097) B5356097
theorem B2677819 : Blo 1585491 2677819 := bstep (se 1 (by rfl) ⟨2008364, by rfl⟩ : syracuseStep 2677819 = 4016729) B4016729
theorem B77225021 : Blo 1585491 77225021 := bstep (se 3 (by rfl) ⟨14479691, by rfl⟩ : syracuseStep 77225021 = 28959383) B28959383
theorem B1785019 : Blo 1585491 1785019 := bstep (se 1 (by rfl) ⟨1338764, by rfl⟩ : syracuseStep 1785019 = 2677529) B2677529
theorem B2677961 : Blo 1585491 2677961 := bstep (se 2 (by rfl) ⟨1004235, by rfl⟩ : syracuseStep 2677961 = 2008471) B2008471
theorem B5356745 : Blo 1585491 5356745 := bstep (se 2 (by rfl) ⟨2008779, by rfl⟩ : syracuseStep 5356745 = 4017559) B4017559
theorem B13737197 : Blo 1585491 13737197 := bstep (se 3 (by rfl) ⟨2575724, by rfl⟩ : syracuseStep 13737197 = 5151449) B5151449
theorem B4013327 : Blo 1585491 4013327 := bstep (se 1 (by rfl) ⟨3009995, by rfl⟩ : syracuseStep 4013327 = 6019991) B6019991
theorem B6774131 : Blo 1585491 6774131 := bstep (se 1 (by rfl) ⟨5080598, by rfl⟩ : syracuseStep 6774131 = 10161197) B10161197
theorem B4013459 : Blo 1585491 4013459 := bstep (se 1 (by rfl) ⟨3010094, by rfl⟩ : syracuseStep 4013459 = 6020189) B6020189
theorem B19553683 : Blo 1585491 19553683 := bstep (se 1 (by rfl) ⟨14665262, by rfl⟩ : syracuseStep 19553683 = 29330525) B29330525
theorem B3571091 : Blo 1585491 3571091 := bstep (se 1 (by rfl) ⟨2678318, by rfl⟩ : syracuseStep 3571091 = 5356637) B5356637
theorem B3571145 : Blo 1585491 3571145 := bstep (se 2 (by rfl) ⟨1339179, by rfl⟩ : syracuseStep 3571145 = 2678359) B2678359
theorem B6020675 : Blo 1585491 6020675 := bstep (se 1 (by rfl) ⟨4515506, by rfl⟩ : syracuseStep 6020675 = 9031013) B9031013
theorem B3620471 : Blo 1585491 3620471 := bstep (se 1 (by rfl) ⟨2715353, by rfl⟩ : syracuseStep 3620471 = 5430707) B5430707
theorem B1785487 : Blo 1585491 1785487 := bstep (se 1 (by rfl) ⟨1339115, by rfl⟩ : syracuseStep 1785487 = 2678231) B2678231
theorem B17391395 : Blo 1585491 17391395 := bstep (se 1 (by rfl) ⟨13043546, by rfl⟩ : syracuseStep 17391395 = 26087093) B26087093
theorem B24420145 : Blo 1585491 24420145 := bstep (se 2 (by rfl) ⟨9157554, by rfl⟩ : syracuseStep 24420145 = 18315109) B18315109
theorem B2752375 : Blo 1585491 2752375 := bstep (se 1 (by rfl) ⟨2064281, by rfl⟩ : syracuseStep 2752375 = 4128563) B4128563
theorem B2678663 : Blo 1585491 2678663 := bstep (se 1 (by rfl) ⟨2008997, by rfl⟩ : syracuseStep 2678663 = 4017995) B4017995
theorem B5357447 : Blo 1585491 5357447 := bstep (se 1 (by rfl) ⟨4018085, by rfl⟩ : syracuseStep 5357447 = 8036171) B8036171
theorem B2678791 : Blo 1585491 2678791 := bstep (se 1 (by rfl) ⟨2009093, by rfl⟩ : syracuseStep 2678791 = 4018187) B4018187
theorem B4014137 : Blo 1585491 4014137 := bstep (se 2 (by rfl) ⟨1505301, by rfl⟩ : syracuseStep 4014137 = 3010603) B3010603
theorem B12861497 : Blo 1585491 12861497 := bstep (se 2 (by rfl) ⟨4823061, by rfl⟩ : syracuseStep 12861497 = 9646123) B9646123
theorem B2007119 : Blo 1585491 2007119 := bstep (se 1 (by rfl) ⟨1505339, by rfl⟩ : syracuseStep 2007119 = 3010679) B3010679
theorem B10166579 : Blo 1585491 10166579 := bstep (se 1 (by rfl) ⟨7624934, by rfl⟩ : syracuseStep 10166579 = 15249869) B15249869
theorem B9036137 : Blo 1585491 9036137 := bstep (se 2 (by rfl) ⟨3388551, by rfl⟩ : syracuseStep 9036137 = 6777103) B6777103
theorem B17146241 : Blo 1585491 17146241 := bstep (se 2 (by rfl) ⟨6429840, by rfl⟩ : syracuseStep 17146241 = 12859681) B12859681
theorem B13550105 : Blo 1585491 13550105 := bstep (se 2 (by rfl) ⟨5081289, by rfl⟩ : syracuseStep 13550105 = 10162579) B10162579
theorem B185483981 : Blo 1585491 185483981 := bstep (se 3 (by rfl) ⟨34778246, by rfl⟩ : syracuseStep 185483981 = 69556493) B69556493
theorem B8028881 : Blo 1585491 8028881 := bstep (se 2 (by rfl) ⟨3010830, by rfl⟩ : syracuseStep 8028881 = 6021661) B6021661
theorem B3810007 : Blo 1585491 3810007 := bstep (se 1 (by rfl) ⟨2857505, by rfl⟩ : syracuseStep 3810007 = 5715011) B5715011
theorem B14468015 : Blo 1585491 14468015 := bstep (se 1 (by rfl) ⟨10851011, by rfl⟩ : syracuseStep 14468015 = 21702023) B21702023
theorem B6185915 : Blo 1585491 6185915 := bstep (se 1 (by rfl) ⟨4639436, by rfl⟩ : syracuseStep 6185915 = 9278873) B9278873
theorem B2712583 : Blo 1585491 2712583 := bstep (se 1 (by rfl) ⟨2034437, by rfl⟩ : syracuseStep 2712583 = 4068875) B4068875
theorem B34382897 : Blo 1585491 34382897 := bstep (se 2 (by rfl) ⟨12893586, by rfl⟩ : syracuseStep 34382897 = 25787173) B25787173
theorem B2008415 : Blo 1585491 2008415 := bstep (se 1 (by rfl) ⟨1506311, by rfl⟩ : syracuseStep 2008415 = 3012623) B3012623
theorem B12051827 : Blo 1585491 12051827 := bstep (se 1 (by rfl) ⟨9038870, by rfl⟩ : syracuseStep 12051827 = 18077741) B18077741
theorem B6022619 : Blo 1585491 6022619 := bstep (se 1 (by rfl) ⟨4516964, by rfl⟩ : syracuseStep 6022619 = 9033929) B9033929
theorem B34309777 : Blo 1585491 34309777 := bstep (se 2 (by rfl) ⟨12866166, by rfl⟩ : syracuseStep 34309777 = 25732333) B25732333
theorem B4515517 : Blo 1585491 4515517 := bstep (se 3 (by rfl) ⟨846659, by rfl⟩ : syracuseStep 4515517 = 1693319) B1693319
theorem B4581053 : Blo 1585491 4581053 := bstep (se 3 (by rfl) ⟨858947, by rfl⟩ : syracuseStep 4581053 = 1717895) B1717895
theorem B4581215 : Blo 1585491 4581215 := bstep (se 1 (by rfl) ⟨3435911, by rfl⟩ : syracuseStep 4581215 = 6871823) B6871823
theorem B39143263 : Blo 1585491 39143263 := bstep (se 1 (by rfl) ⟨29357447, by rfl⟩ : syracuseStep 39143263 = 58714895) B58714895
theorem B4515745 : Blo 1585491 4515745 := bstep (se 2 (by rfl) ⟨1693404, by rfl⟩ : syracuseStep 4515745 = 3386809) B3386809
theorem B32573573 : Blo 1585491 32573573 := bstep (se 4 (by rfl) ⟨3053772, by rfl⟩ : syracuseStep 32573573 = 6107545) B6107545
theorem B4516087 : Blo 1585491 4516087 := bstep (se 1 (by rfl) ⟨3387065, by rfl⟩ : syracuseStep 4516087 = 6774131) B6774131
theorem B4016375 : Blo 1585491 4016375 := bstep (se 1 (by rfl) ⟨3012281, by rfl⟩ : syracuseStep 4016375 = 6024563) B6024563
theorem B20318597 : Blo 1585491 20318597 := bstep (se 4 (by rfl) ⟨1904868, by rfl⟩ : syracuseStep 20318597 = 3809737) B3809737
theorem B2378249 : Blo 1585491 2378249 := bstep (se 2 (by rfl) ⟨891843, by rfl⟩ : syracuseStep 2378249 = 1783687) B1783687
theorem B4516361 : Blo 1585491 4516361 := bstep (se 2 (by rfl) ⟨1693635, by rfl⟩ : syracuseStep 4516361 = 3387271) B3387271
theorem B11594263 : Blo 1585491 11594263 := bstep (se 1 (by rfl) ⟨8695697, by rfl⟩ : syracuseStep 11594263 = 17391395) B17391395
theorem B6777377 : Blo 1585491 6777377 := bstep (se 2 (by rfl) ⟨2541516, by rfl⟩ : syracuseStep 6777377 = 5083033) B5083033
theorem B2378279 : Blo 1585491 2378279 := bstep (se 1 (by rfl) ⟨1783709, by rfl⟩ : syracuseStep 2378279 = 3567419) B3567419
theorem B2378363 : Blo 1585491 2378363 := bstep (se 1 (by rfl) ⟨1783772, by rfl⟩ : syracuseStep 2378363 = 3567545) B3567545
theorem B6023879 : Blo 1585491 6023879 := bstep (se 1 (by rfl) ⟨4517909, by rfl⟩ : syracuseStep 6023879 = 9035819) B9035819
theorem B2378489 : Blo 1585491 2378489 := bstep (se 2 (by rfl) ⟨891933, by rfl⟩ : syracuseStep 2378489 = 1783867) B1783867
theorem B2378591 : Blo 1585491 2378591 := bstep (se 1 (by rfl) ⟨1783943, by rfl⟩ : syracuseStep 2378591 = 3567887) B3567887
theorem B2378603 : Blo 1585491 2378603 := bstep (se 1 (by rfl) ⟨1783952, by rfl⟩ : syracuseStep 2378603 = 3567905) B3567905
theorem B2378831 : Blo 1585491 2378831 := bstep (se 1 (by rfl) ⟨1784123, by rfl⟩ : syracuseStep 2378831 = 3568247) B3568247
theorem B8031311 : Blo 1585491 8031311 := bstep (se 1 (by rfl) ⟨6023483, by rfl⟩ : syracuseStep 8031311 = 12046967) B12046967
theorem B9653327 : Blo 1585491 9653327 := bstep (se 1 (by rfl) ⟨7239995, by rfl⟩ : syracuseStep 9653327 = 14479991) B14479991
theorem B4517021 : Blo 1585491 4517021 := bstep (se 3 (by rfl) ⟨846941, by rfl⟩ : syracuseStep 4517021 = 1693883) B1693883
theorem B5721283 : Blo 1585491 5721283 := bstep (se 1 (by rfl) ⟨4290962, by rfl⟩ : syracuseStep 5721283 = 8581925) B8581925
theorem B2378951 : Blo 1585491 2378951 := bstep (se 1 (by rfl) ⟨1784213, by rfl⟩ : syracuseStep 2378951 = 3568427) B3568427
theorem B5352695 : Blo 1585491 5352695 := bstep (se 1 (by rfl) ⟨4014521, by rfl⟩ : syracuseStep 5352695 = 8029043) B8029043
theorem B2379113 : Blo 1585491 2379113 := bstep (se 2 (by rfl) ⟨892167, by rfl⟩ : syracuseStep 2379113 = 1784335) B1784335
theorem B6188413 : Blo 1585491 6188413 := bstep (se 3 (by rfl) ⟨1160327, by rfl⟩ : syracuseStep 6188413 = 2320655) B2320655
theorem B6024577 : Blo 1585491 6024577 := bstep (se 2 (by rfl) ⟨2259216, by rfl⟩ : syracuseStep 6024577 = 4518433) B4518433
theorem B3386767 : Blo 1585491 3386767 := bstep (se 1 (by rfl) ⟨2540075, by rfl⟩ : syracuseStep 3386767 = 5080151) B5080151
theorem B2379191 : Blo 1585491 2379191 := bstep (se 1 (by rfl) ⟨1784393, by rfl⟩ : syracuseStep 2379191 = 3568787) B3568787
theorem B2379227 : Blo 1585491 2379227 := bstep (se 1 (by rfl) ⟨1784420, by rfl⟩ : syracuseStep 2379227 = 3568841) B3568841
theorem B4517363 : Blo 1585491 4517363 := bstep (se 1 (by rfl) ⟨3388022, by rfl⟩ : syracuseStep 4517363 = 6776045) B6776045
theorem B3214855 : Blo 1585491 3214855 := bstep (se 1 (by rfl) ⟨2411141, by rfl⟩ : syracuseStep 3214855 = 4822283) B4822283
theorem B5353019 : Blo 1585491 5353019 := bstep (se 1 (by rfl) ⟨4014764, by rfl⟩ : syracuseStep 5353019 = 8029529) B8029529
theorem B6024851 : Blo 1585491 6024851 := bstep (se 1 (by rfl) ⟨4518638, by rfl⟩ : syracuseStep 6024851 = 9037277) B9037277
theorem B4017863 : Blo 1585491 4017863 := bstep (se 1 (by rfl) ⟨3013397, by rfl⟩ : syracuseStep 4017863 = 6026795) B6026795
theorem B8031959 : Blo 1585491 8031959 := bstep (se 1 (by rfl) ⟨6023969, by rfl⟩ : syracuseStep 8031959 = 12047939) B12047939
theorem B5353289 : Blo 1585491 5353289 := bstep (se 2 (by rfl) ⟨2007483, by rfl⟩ : syracuseStep 5353289 = 4014967) B4014967
theorem B3567455 : Blo 1585491 3567455 := bstep (se 1 (by rfl) ⟨2675591, by rfl⟩ : syracuseStep 3567455 = 5351183) B5351183
theorem B2379695 : Blo 1585491 2379695 := bstep (se 1 (by rfl) ⟨1784771, by rfl⟩ : syracuseStep 2379695 = 3569543) B3569543
theorem B4517819 : Blo 1585491 4517819 := bstep (se 1 (by rfl) ⟨3388364, by rfl⟩ : syracuseStep 4517819 = 6776729) B6776729
theorem B2379785 : Blo 1585491 2379785 := bstep (se 2 (by rfl) ⟨892419, by rfl⟩ : syracuseStep 2379785 = 1784839) B1784839
theorem B3567635 : Blo 1585491 3567635 := bstep (se 1 (by rfl) ⟨2675726, by rfl⟩ : syracuseStep 3567635 = 5351453) B5351453
theorem B2379815 : Blo 1585491 2379815 := bstep (se 1 (by rfl) ⟨1784861, by rfl⟩ : syracuseStep 2379815 = 3569723) B3569723
theorem B2379899 : Blo 1585491 2379899 := bstep (se 1 (by rfl) ⟨1784924, by rfl⟩ : syracuseStep 2379899 = 3569849) B3569849
theorem B2380025 : Blo 1585491 2380025 := bstep (se 2 (by rfl) ⟨892509, by rfl⟩ : syracuseStep 2380025 = 1785019) B1785019
theorem B9654589 : Blo 1585491 9654589 := bstep (se 3 (by rfl) ⟨1810235, by rfl⟩ : syracuseStep 9654589 = 3620471) B3620471
theorem B1585503 : Blo 1585491 1585503 := bstep (se 1 (by rfl) ⟨1189127, by rfl⟩ : syracuseStep 1585503 = 2378255) B2378255
theorem B2380127 : Blo 1585491 2380127 := bstep (se 1 (by rfl) ⟨1785095, by rfl⟩ : syracuseStep 2380127 = 3570191) B3570191
theorem B3567977 : Blo 1585491 3567977 := bstep (se 2 (by rfl) ⟨1337991, by rfl⟩ : syracuseStep 3567977 = 2675983) B2675983
theorem B2380139 : Blo 1585491 2380139 := bstep (se 1 (by rfl) ⟨1785104, by rfl⟩ : syracuseStep 2380139 = 3570209) B3570209
theorem B1585531 : Blo 1585491 1585531 := bstep (se 1 (by rfl) ⟨1189148, by rfl⟩ : syracuseStep 1585531 = 2378297) B2378297
theorem B1585583 : Blo 1585491 1585583 := bstep (se 1 (by rfl) ⟨1189187, by rfl⟩ : syracuseStep 1585583 = 2378375) B2378375
theorem B1585607 : Blo 1585491 1585607 := bstep (se 1 (by rfl) ⟨1189205, by rfl⟩ : syracuseStep 1585607 = 2378411) B2378411
theorem B1585627 : Blo 1585491 1585627 := bstep (se 1 (by rfl) ⟨1189220, by rfl⟩ : syracuseStep 1585627 = 2378441) B2378441
theorem B3617243 : Blo 1585491 3617243 := bstep (se 1 (by rfl) ⟨2712932, by rfl⟩ : syracuseStep 3617243 = 5425865) B5425865
theorem B3813851 : Blo 1585491 3813851 := bstep (se 1 (by rfl) ⟨2860388, by rfl⟩ : syracuseStep 3813851 = 5720777) B5720777
theorem B20337155 : Blo 1585491 20337155 := bstep (se 1 (by rfl) ⟨15252866, by rfl⟩ : syracuseStep 20337155 = 30505733) B30505733
theorem B26071577 : Blo 1585491 26071577 := bstep (se 2 (by rfl) ⟨9776841, by rfl⟩ : syracuseStep 26071577 = 19553683) B19553683
theorem B1585703 : Blo 1585491 1585703 := bstep (se 1 (by rfl) ⟨1189277, by rfl⟩ : syracuseStep 1585703 = 2378555) B2378555
theorem B5714491 : Blo 1585491 5714491 := bstep (se 1 (by rfl) ⟨4285868, by rfl⟩ : syracuseStep 5714491 = 8571737) B8571737
theorem B1585743 : Blo 1585491 1585743 := bstep (se 1 (by rfl) ⟨1189307, by rfl⟩ : syracuseStep 1585743 = 2378615) B2378615
theorem B2380367 : Blo 1585491 2380367 := bstep (se 1 (by rfl) ⟨1785275, by rfl⟩ : syracuseStep 2380367 = 3570551) B3570551
theorem B1585759 : Blo 1585491 1585759 := bstep (se 1 (by rfl) ⟨1189319, by rfl⟩ : syracuseStep 1585759 = 2378639) B2378639
theorem B1585787 : Blo 1585491 1585787 := bstep (se 1 (by rfl) ⟨1189340, by rfl⟩ : syracuseStep 1585787 = 2378681) B2378681
theorem B3011195 : Blo 1585491 3011195 := bstep (se 1 (by rfl) ⟨2258396, by rfl⟩ : syracuseStep 3011195 = 4516793) B4516793
theorem B1585839 : Blo 1585491 1585839 := bstep (se 1 (by rfl) ⟨1189379, by rfl⟩ : syracuseStep 1585839 = 2378759) B2378759
theorem B1585863 : Blo 1585491 1585863 := bstep (se 1 (by rfl) ⟨1189397, by rfl⟩ : syracuseStep 1585863 = 2378795) B2378795
theorem B2380487 : Blo 1585491 2380487 := bstep (se 1 (by rfl) ⟨1785365, by rfl⟩ : syracuseStep 2380487 = 3570731) B3570731
theorem B51483347 : Blo 1585491 51483347 := bstep (se 1 (by rfl) ⟨38612510, by rfl⟩ : syracuseStep 51483347 = 77225021) B77225021
theorem B1585883 : Blo 1585491 1585883 := bstep (se 1 (by rfl) ⟨1189412, by rfl⟩ : syracuseStep 1585883 = 2378825) B2378825
theorem B60977933 : Blo 1585491 60977933 := bstep (se 3 (by rfl) ⟨11433362, by rfl⟩ : syracuseStep 60977933 = 22866725) B22866725
theorem B1585959 : Blo 1585491 1585959 := bstep (se 1 (by rfl) ⟨1189469, by rfl⟩ : syracuseStep 1585959 = 2378939) B2378939
theorem B30503729 : Blo 1585491 30503729 := bstep (se 2 (by rfl) ⟨11438898, by rfl⟩ : syracuseStep 30503729 = 22877797) B22877797
theorem B1585999 : Blo 1585491 1585999 := bstep (se 1 (by rfl) ⟨1189499, by rfl⟩ : syracuseStep 1585999 = 2378999) B2378999
theorem B2675551 : Blo 1585491 2675551 := bstep (se 1 (by rfl) ⟨2006663, by rfl⟩ : syracuseStep 2675551 = 4013327) B4013327
theorem B1586015 : Blo 1585491 1586015 := bstep (se 1 (by rfl) ⟨1189511, by rfl⟩ : syracuseStep 1586015 = 2379023) B2379023
theorem B2380649 : Blo 1585491 2380649 := bstep (se 2 (by rfl) ⟨892743, by rfl⟩ : syracuseStep 2380649 = 1785487) B1785487
theorem B1586043 : Blo 1585491 1586043 := bstep (se 1 (by rfl) ⟨1189532, by rfl⟩ : syracuseStep 1586043 = 2379065) B2379065
theorem B1586095 : Blo 1585491 1586095 := bstep (se 1 (by rfl) ⟨1189571, by rfl⟩ : syracuseStep 1586095 = 2379143) B2379143
theorem B2675639 : Blo 1585491 2675639 := bstep (se 1 (by rfl) ⟨2006729, by rfl⟩ : syracuseStep 2675639 = 4013459) B4013459
theorem B5354423 : Blo 1585491 5354423 := bstep (se 1 (by rfl) ⟨4015817, by rfl⟩ : syracuseStep 5354423 = 8031635) B8031635
theorem B2380727 : Blo 1585491 2380727 := bstep (se 1 (by rfl) ⟨1785545, by rfl⟩ : syracuseStep 2380727 = 3571091) B3571091
theorem B3568571 : Blo 1585491 3568571 := bstep (se 1 (by rfl) ⟨2676428, by rfl⟩ : syracuseStep 3568571 = 5352857) B5352857
theorem B1586119 : Blo 1585491 1586119 := bstep (se 1 (by rfl) ⟨1189589, by rfl⟩ : syracuseStep 1586119 = 2379179) B2379179
theorem B1586139 : Blo 1585491 1586139 := bstep (se 1 (by rfl) ⟨1189604, by rfl⟩ : syracuseStep 1586139 = 2379209) B2379209
theorem B2380763 : Blo 1585491 2380763 := bstep (se 1 (by rfl) ⟨1785572, by rfl⟩ : syracuseStep 2380763 = 3571145) B3571145
theorem B1586215 : Blo 1585491 1586215 := bstep (se 1 (by rfl) ⟨1189661, by rfl⟩ : syracuseStep 1586215 = 2379323) B2379323
theorem B3568697 : Blo 1585491 3568697 := bstep (se 2 (by rfl) ⟨1338261, by rfl⟩ : syracuseStep 3568697 = 2676523) B2676523
theorem B32560193 : Blo 1585491 32560193 := bstep (se 2 (by rfl) ⟨12210072, by rfl⟩ : syracuseStep 32560193 = 24420145) B24420145
theorem B1586255 : Blo 1585491 1586255 := bstep (se 1 (by rfl) ⟨1189691, by rfl⟩ : syracuseStep 1586255 = 2379383) B2379383
theorem B1586271 : Blo 1585491 1586271 := bstep (se 1 (by rfl) ⟨1189703, by rfl⟩ : syracuseStep 1586271 = 2379407) B2379407
theorem B3011681 : Blo 1585491 3011681 := bstep (se 2 (by rfl) ⟨1129380, by rfl⟩ : syracuseStep 3011681 = 2258761) B2258761
theorem B1586299 : Blo 1585491 1586299 := bstep (se 1 (by rfl) ⟨1189724, by rfl⟩ : syracuseStep 1586299 = 2379449) B2379449
theorem B14480537 : Blo 1585491 14480537 := bstep (se 2 (by rfl) ⟨5430201, by rfl⟩ : syracuseStep 14480537 = 10860403) B10860403
theorem B1586351 : Blo 1585491 1586351 := bstep (se 1 (by rfl) ⟨1189763, by rfl⟩ : syracuseStep 1586351 = 2379527) B2379527
theorem B1586375 : Blo 1585491 1586375 := bstep (se 1 (by rfl) ⟨1189781, by rfl⟩ : syracuseStep 1586375 = 2379563) B2379563
theorem B1586395 : Blo 1585491 1586395 := bstep (se 1 (by rfl) ⟨1189796, by rfl⟩ : syracuseStep 1586395 = 2379593) B2379593
theorem B3011833 : Blo 1585491 3011833 := bstep (se 2 (by rfl) ⟨1129437, by rfl⟩ : syracuseStep 3011833 = 2258875) B2258875
theorem B6026507 : Blo 1585491 6026507 := bstep (se 1 (by rfl) ⟨4519880, by rfl⟩ : syracuseStep 6026507 = 9039761) B9039761
theorem B1586471 : Blo 1585491 1586471 := bstep (se 1 (by rfl) ⟨1189853, by rfl⟩ : syracuseStep 1586471 = 2379707) B2379707
theorem B1586511 : Blo 1585491 1586511 := bstep (se 1 (by rfl) ⟨1189883, by rfl⟩ : syracuseStep 1586511 = 2379767) B2379767
theorem B1586527 : Blo 1585491 1586527 := bstep (se 1 (by rfl) ⟨1189895, by rfl⟩ : syracuseStep 1586527 = 2379791) B2379791
theorem B1586555 : Blo 1585491 1586555 := bstep (se 1 (by rfl) ⟨1189916, by rfl⟩ : syracuseStep 1586555 = 2379833) B2379833
theorem B3569039 : Blo 1585491 3569039 := bstep (se 1 (by rfl) ⟨2676779, by rfl⟩ : syracuseStep 3569039 = 5353559) B5353559
theorem B1586607 : Blo 1585491 1586607 := bstep (se 1 (by rfl) ⟨1189955, by rfl⟩ : syracuseStep 1586607 = 2379911) B2379911
theorem B2381231 : Blo 1585491 2381231 := bstep (se 1 (by rfl) ⟨1785923, by rfl⟩ : syracuseStep 2381231 = 3571847) B3571847
theorem B1586631 : Blo 1585491 1586631 := bstep (se 1 (by rfl) ⟨1189973, by rfl⟩ : syracuseStep 1586631 = 2379947) B2379947
theorem B10163657 : Blo 1585491 10163657 := bstep (se 2 (by rfl) ⟨3811371, by rfl⟩ : syracuseStep 10163657 = 7622743) B7622743
theorem B1586651 : Blo 1585491 1586651 := bstep (se 1 (by rfl) ⟨1189988, by rfl⟩ : syracuseStep 1586651 = 2379977) B2379977
theorem B2676233 : Blo 1585491 2676233 := bstep (se 2 (by rfl) ⟨1003587, by rfl⟩ : syracuseStep 2676233 = 2007175) B2007175
theorem B5355017 : Blo 1585491 5355017 := bstep (se 2 (by rfl) ⟨2008131, by rfl⟩ : syracuseStep 5355017 = 4016263) B4016263
theorem B1586727 : Blo 1585491 1586727 := bstep (se 1 (by rfl) ⟨1190045, by rfl⟩ : syracuseStep 1586727 = 2380091) B2380091
theorem B1586767 : Blo 1585491 1586767 := bstep (se 1 (by rfl) ⟨1190075, by rfl⟩ : syracuseStep 1586767 = 2380151) B2380151
theorem B1586783 : Blo 1585491 1586783 := bstep (se 1 (by rfl) ⟨1190087, by rfl⟩ : syracuseStep 1586783 = 2380175) B2380175
theorem B10163809 : Blo 1585491 10163809 := bstep (se 2 (by rfl) ⟨3811428, by rfl⟩ : syracuseStep 10163809 = 7622857) B7622857
theorem B11433595 : Blo 1585491 11433595 := bstep (se 1 (by rfl) ⟨8575196, by rfl⟩ : syracuseStep 11433595 = 17150393) B17150393
theorem B1586811 : Blo 1585491 1586811 := bstep (se 1 (by rfl) ⟨1190108, by rfl⟩ : syracuseStep 1586811 = 2380217) B2380217
theorem B9164411 : Blo 1585491 9164411 := bstep (se 1 (by rfl) ⟨6873308, by rfl⟩ : syracuseStep 9164411 = 13746617) B13746617
theorem B2676395 : Blo 1585491 2676395 := bstep (se 1 (by rfl) ⟨2007296, by rfl⟩ : syracuseStep 2676395 = 4014593) B4014593
theorem B1586863 : Blo 1585491 1586863 := bstep (se 1 (by rfl) ⟨1190147, by rfl⟩ : syracuseStep 1586863 = 2380295) B2380295
theorem B1586887 : Blo 1585491 1586887 := bstep (se 1 (by rfl) ⟨1190165, by rfl⟩ : syracuseStep 1586887 = 2380331) B2380331
theorem B3569363 : Blo 1585491 3569363 := bstep (se 1 (by rfl) ⟨2677022, by rfl⟩ : syracuseStep 3569363 = 5354045) B5354045
theorem B1586907 : Blo 1585491 1586907 := bstep (se 1 (by rfl) ⟨1190180, by rfl⟩ : syracuseStep 1586907 = 2380361) B2380361
theorem B1586983 : Blo 1585491 1586983 := bstep (se 1 (by rfl) ⟨1190237, by rfl⟩ : syracuseStep 1586983 = 2380475) B2380475
theorem B1587023 : Blo 1585491 1587023 := bstep (se 1 (by rfl) ⟨1190267, by rfl⟩ : syracuseStep 1587023 = 2380535) B2380535
theorem B1587039 : Blo 1585491 1587039 := bstep (se 1 (by rfl) ⟨1190279, by rfl⟩ : syracuseStep 1587039 = 2380559) B2380559
theorem B1587067 : Blo 1585491 1587067 := bstep (se 1 (by rfl) ⟨1190300, by rfl⟩ : syracuseStep 1587067 = 2380601) B2380601
theorem B1587119 : Blo 1585491 1587119 := bstep (se 1 (by rfl) ⟨1190339, by rfl⟩ : syracuseStep 1587119 = 2380679) B2380679
theorem B1587143 : Blo 1585491 1587143 := bstep (se 1 (by rfl) ⟨1190357, by rfl⟩ : syracuseStep 1587143 = 2380715) B2380715
theorem B1587163 : Blo 1585491 1587163 := bstep (se 1 (by rfl) ⟨1190372, by rfl⟩ : syracuseStep 1587163 = 2380745) B2380745
theorem B5085185 : Blo 1585491 5085185 := bstep (se 2 (by rfl) ⟨1906944, by rfl⟩ : syracuseStep 5085185 = 3813889) B3813889
theorem B1587239 : Blo 1585491 1587239 := bstep (se 1 (by rfl) ⟨1190429, by rfl⟩ : syracuseStep 1587239 = 2380859) B2380859
theorem B2676793 : Blo 1585491 2676793 := bstep (se 2 (by rfl) ⟨1003797, by rfl⟩ : syracuseStep 2676793 = 2007595) B2007595
theorem B1587279 : Blo 1585491 1587279 := bstep (se 1 (by rfl) ⟨1190459, by rfl⟩ : syracuseStep 1587279 = 2380919) B2380919
theorem B1587295 : Blo 1585491 1587295 := bstep (se 1 (by rfl) ⟨1190471, by rfl⟩ : syracuseStep 1587295 = 2380943) B2380943
theorem B1587323 : Blo 1585491 1587323 := bstep (se 1 (by rfl) ⟨1190492, by rfl⟩ : syracuseStep 1587323 = 2380985) B2380985
theorem B1587375 : Blo 1585491 1587375 := bstep (se 1 (by rfl) ⟨1190531, by rfl⟩ : syracuseStep 1587375 = 2381063) B2381063
theorem B2676935 : Blo 1585491 2676935 := bstep (se 1 (by rfl) ⟨2007701, by rfl⟩ : syracuseStep 2676935 = 4015403) B4015403
theorem B1587399 : Blo 1585491 1587399 := bstep (se 1 (by rfl) ⟨1190549, by rfl⟩ : syracuseStep 1587399 = 2381099) B2381099
theorem B1587419 : Blo 1585491 1587419 := bstep (se 1 (by rfl) ⟨1190564, by rfl⟩ : syracuseStep 1587419 = 2381129) B2381129
theorem B6773003 : Blo 1585491 6773003 := bstep (se 1 (by rfl) ⟨5079752, by rfl⟩ : syracuseStep 6773003 = 10159505) B10159505
theorem B2677097 : Blo 1585491 2677097 := bstep (se 2 (by rfl) ⟨1003911, by rfl⟩ : syracuseStep 2677097 = 2007823) B2007823
theorem B5355881 : Blo 1585491 5355881 := bstep (se 2 (by rfl) ⟨2008455, by rfl⟩ : syracuseStep 5355881 = 4016911) B4016911
theorem B29350277 : Blo 1585491 29350277 := bstep (se 4 (by rfl) ⟨2751588, by rfl⟩ : syracuseStep 29350277 = 5503177) B5503177
theorem B3013139 : Blo 1585491 3013139 := bstep (se 1 (by rfl) ⟨2259854, by rfl⟩ : syracuseStep 3013139 = 4519709) B4519709
theorem B8034875 : Blo 1585491 8034875 := bstep (se 1 (by rfl) ⟨6026156, by rfl⟩ : syracuseStep 8034875 = 12052313) B12052313
theorem B1784443 : Blo 1585491 1784443 := bstep (se 1 (by rfl) ⟨1338332, by rfl⟩ : syracuseStep 1784443 = 2676665) B2676665
theorem B3570299 : Blo 1585491 3570299 := bstep (se 1 (by rfl) ⟨2677724, by rfl⟩ : syracuseStep 3570299 = 5355449) B5355449
theorem B3013291 : Blo 1585491 3013291 := bstep (se 1 (by rfl) ⟨2259968, by rfl⟩ : syracuseStep 3013291 = 4519937) B4519937
theorem B20323061 : Blo 1585491 20323061 := bstep (se 5 (by rfl) ⟨952643, by rfl⟩ : syracuseStep 20323061 = 1905287) B1905287
theorem B2677495 : Blo 1585491 2677495 := bstep (se 1 (by rfl) ⟨2008121, by rfl⟩ : syracuseStep 2677495 = 4016243) B4016243
theorem B3570425 : Blo 1585491 3570425 := bstep (se 2 (by rfl) ⟨1338909, by rfl⟩ : syracuseStep 3570425 = 2677819) B2677819
theorem B3013519 : Blo 1585491 3013519 := bstep (se 1 (by rfl) ⟨2260139, by rfl⟩ : syracuseStep 3013519 = 4520279) B4520279
theorem B24746897 : Blo 1585491 24746897 := bstep (se 2 (by rfl) ⟨9280086, by rfl⟩ : syracuseStep 24746897 = 18560173) B18560173
theorem B12041135 : Blo 1585491 12041135 := bstep (se 1 (by rfl) ⟨9030851, by rfl⟩ : syracuseStep 12041135 = 18061703) B18061703
theorem B9034679 : Blo 1585491 9034679 := bstep (se 1 (by rfl) ⟨6776009, by rfl⟩ : syracuseStep 9034679 = 13552019) B13552019
theorem B2259895 : Blo 1585491 2259895 := bstep (se 1 (by rfl) ⟨1694921, by rfl⟩ : syracuseStep 2259895 = 3389843) B3389843
theorem B2677691 : Blo 1585491 2677691 := bstep (se 1 (by rfl) ⟨2008268, by rfl⟩ : syracuseStep 2677691 = 4016537) B4016537
theorem B5356475 : Blo 1585491 5356475 := bstep (se 1 (by rfl) ⟨4017356, by rfl⟩ : syracuseStep 5356475 = 8034713) B8034713
theorem B3013595 : Blo 1585491 3013595 := bstep (se 1 (by rfl) ⟨2260196, by rfl⟩ : syracuseStep 3013595 = 4520393) B4520393
theorem B3570695 : Blo 1585491 3570695 := bstep (se 1 (by rfl) ⟨2678021, by rfl⟩ : syracuseStep 3570695 = 5356043) B5356043
theorem B2677799 : Blo 1585491 2677799 := bstep (se 1 (by rfl) ⟨2008349, by rfl⟩ : syracuseStep 2677799 = 4016699) B4016699
theorem B1784911 : Blo 1585491 1784911 := bstep (se 1 (by rfl) ⟨1338683, by rfl⟩ : syracuseStep 1784911 = 2677367) B2677367
theorem B3570767 : Blo 1585491 3570767 := bstep (se 1 (by rfl) ⟨2678075, by rfl⟩ : syracuseStep 3570767 = 5356151) B5356151
theorem B10861721 : Blo 1585491 10861721 := bstep (se 2 (by rfl) ⟨4073145, by rfl⟩ : syracuseStep 10861721 = 8146291) B8146291
theorem B8035523 : Blo 1585491 8035523 := bstep (se 1 (by rfl) ⟨6026642, by rfl⟩ : syracuseStep 8035523 = 12053285) B12053285
theorem B2678089 : Blo 1585491 2678089 := bstep (se 2 (by rfl) ⟨1004283, by rfl⟩ : syracuseStep 2678089 = 2008567) B2008567
theorem B2678123 : Blo 1585491 2678123 := bstep (se 1 (by rfl) ⟨2008592, by rfl⟩ : syracuseStep 2678123 = 4017185) B4017185
theorem B6020477 : Blo 1585491 6020477 := bstep (se 3 (by rfl) ⟨1128839, by rfl⟩ : syracuseStep 6020477 = 2257679) B2257679
theorem B12049883 : Blo 1585491 12049883 := bstep (se 1 (by rfl) ⟨9037412, by rfl⟩ : syracuseStep 12049883 = 18074825) B18074825
theorem B1785307 : Blo 1585491 1785307 := bstep (se 1 (by rfl) ⟨1338980, by rfl⟩ : syracuseStep 1785307 = 2677961) B2677961
theorem B3571163 : Blo 1585491 3571163 := bstep (se 1 (by rfl) ⟨2678372, by rfl⟩ : syracuseStep 3571163 = 5356745) B5356745
theorem B9158131 : Blo 1585491 9158131 := bstep (se 1 (by rfl) ⟨6868598, by rfl⟩ : syracuseStep 9158131 = 13737197) B13737197
theorem B9035387 : Blo 1585491 9035387 := bstep (se 1 (by rfl) ⟨6776540, by rfl⟩ : syracuseStep 9035387 = 13553081) B13553081
theorem B4013783 : Blo 1585491 4013783 := bstep (se 1 (by rfl) ⟨3010337, by rfl⟩ : syracuseStep 4013783 = 6020675) B6020675
theorem B2678521 : Blo 1585491 2678521 := bstep (se 2 (by rfl) ⟨1004445, by rfl⟩ : syracuseStep 2678521 = 2008891) B2008891
theorem B102915845 : Blo 1585491 102915845 := bstep (se 4 (by rfl) ⟨9648360, by rfl⟩ : syracuseStep 102915845 = 19296721) B19296721
theorem B3669833 : Blo 1585491 3669833 := bstep (se 2 (by rfl) ⟨1376187, by rfl⟩ : syracuseStep 3669833 = 2752375) B2752375
theorem B32563063 : Blo 1585491 32563063 := bstep (se 1 (by rfl) ⟨24422297, by rfl⟩ : syracuseStep 32563063 = 48844595) B48844595
theorem B1785775 : Blo 1585491 1785775 := bstep (se 1 (by rfl) ⟨1339331, by rfl⟩ : syracuseStep 1785775 = 2678663) B2678663
theorem B3571631 : Blo 1585491 3571631 := bstep (se 1 (by rfl) ⟨2678723, by rfl⟩ : syracuseStep 3571631 = 5357447) B5357447
theorem B12050369 : Blo 1585491 12050369 := bstep (se 2 (by rfl) ⟨4518888, by rfl⟩ : syracuseStep 12050369 = 9037777) B9037777
theorem B3571721 : Blo 1585491 3571721 := bstep (se 2 (by rfl) ⟨1339395, by rfl⟩ : syracuseStep 3571721 = 2678791) B2678791
theorem B17145893 : Blo 1585491 17145893 := bstep (se 4 (by rfl) ⟨1607427, by rfl⟩ : syracuseStep 17145893 = 3214855) B3214855
theorem B6021449 : Blo 1585491 6021449 := bstep (se 2 (by rfl) ⟨2258043, by rfl⟩ : syracuseStep 6021449 = 4516087) B4516087
theorem B13558103 : Blo 1585491 13558103 := bstep (se 1 (by rfl) ⟨10168577, by rfl⟩ : syracuseStep 13558103 = 20337155) B20337155
theorem B15459017 : Blo 1585491 15459017 := bstep (se 2 (by rfl) ⟨5797131, by rfl⟩ : syracuseStep 15459017 = 11594263) B11594263
theorem B22921931 : Blo 1585491 22921931 := bstep (se 1 (by rfl) ⟨17191448, by rfl⟩ : syracuseStep 22921931 = 34382897) B34382897
theorem B7619321 : Blo 1585491 7619321 := bstep (se 2 (by rfl) ⟨2857245, by rfl⟩ : syracuseStep 7619321 = 5714491) B5714491
theorem B5080009 : Blo 1585491 5080009 := bstep (se 2 (by rfl) ⟨1905003, by rfl⟩ : syracuseStep 5080009 = 3810007) B3810007
theorem B6775771 : Blo 1585491 6775771 := bstep (se 1 (by rfl) ⟨5081828, by rfl⟩ : syracuseStep 6775771 = 10163657) B10163657
theorem B4015079 : Blo 1585491 4015079 := bstep (se 1 (by rfl) ⟨3011309, by rfl⟩ : syracuseStep 4015079 = 6022619) B6022619
theorem B4515335 : Blo 1585491 4515335 := bstep (se 1 (by rfl) ⟨3386501, by rfl⟩ : syracuseStep 4515335 = 6773003) B6773003
theorem B7628377 : Blo 1585491 7628377 := bstep (se 2 (by rfl) ⟨2860641, by rfl⟩ : syracuseStep 7628377 = 5721283) B5721283
theorem B8029853 : Blo 1585491 8029853 := bstep (se 3 (by rfl) ⟨1505597, by rfl⟩ : syracuseStep 8029853 = 3011195) B3011195
theorem B4015777 : Blo 1585491 4015777 := bstep (se 2 (by rfl) ⟨1505916, by rfl⟩ : syracuseStep 4015777 = 3011833) B3011833
theorem B4015919 : Blo 1585491 4015919 := bstep (se 1 (by rfl) ⟨3011939, by rfl⟩ : syracuseStep 4015919 = 6023879) B6023879
theorem B8251217 : Blo 1585491 8251217 := bstep (se 2 (by rfl) ⟨3094206, by rfl⟩ : syracuseStep 8251217 = 6188413) B6188413
theorem B4515689 : Blo 1585491 4515689 := bstep (se 2 (by rfl) ⟨1693383, by rfl⟩ : syracuseStep 4515689 = 3386767) B3386767
theorem B6023119 : Blo 1585491 6023119 := bstep (se 1 (by rfl) ⟨4517339, by rfl⟩ : syracuseStep 6023119 = 9034679) B9034679
theorem B2009063 : Blo 1585491 2009063 := bstep (se 1 (by rfl) ⟨1506797, by rfl⟩ : syracuseStep 2009063 = 3013595) B3013595
theorem B13551745 : Blo 1585491 13551745 := bstep (se 2 (by rfl) ⟨5081904, by rfl⟩ : syracuseStep 13551745 = 10163809) B10163809
theorem B45746369 : Blo 1585491 45746369 := bstep (se 2 (by rfl) ⟨17154888, by rfl⟩ : syracuseStep 45746369 = 34309777) B34309777
theorem B6023591 : Blo 1585491 6023591 := bstep (se 1 (by rfl) ⟨4517693, by rfl⟩ : syracuseStep 6023591 = 9035387) B9035387
theorem B4016567 : Blo 1585491 4016567 := bstep (se 1 (by rfl) ⟨3012425, by rfl⟩ : syracuseStep 4016567 = 6024851) B6024851
theorem B68610563 : Blo 1585491 68610563 := bstep (se 1 (by rfl) ⟨51457922, by rfl⟩ : syracuseStep 68610563 = 102915845) B102915845
theorem B2378303 : Blo 1585491 2378303 := bstep (se 1 (by rfl) ⟨1783727, by rfl⟩ : syracuseStep 2378303 = 3567455) B3567455
theorem B13560493 : Blo 1585491 13560493 := bstep (se 3 (by rfl) ⟨2542592, by rfl⟩ : syracuseStep 13560493 = 5085185) B5085185
theorem B2378423 : Blo 1585491 2378423 := bstep (se 1 (by rfl) ⟨1783817, by rfl⟩ : syracuseStep 2378423 = 3567635) B3567635
theorem B6777719 : Blo 1585491 6777719 := bstep (se 1 (by rfl) ⟨5083289, by rfl⟩ : syracuseStep 6777719 = 10166579) B10166579
theorem B5352317 : Blo 1585491 5352317 := bstep (se 3 (by rfl) ⟨1003559, by rfl⟩ : syracuseStep 5352317 = 2007119) B2007119
theorem B2378651 : Blo 1585491 2378651 := bstep (se 1 (by rfl) ⟨1783988, by rfl⟩ : syracuseStep 2378651 = 3567977) B3567977
theorem B6024091 : Blo 1585491 6024091 := bstep (se 1 (by rfl) ⟨4518068, by rfl⟩ : syracuseStep 6024091 = 9036137) B9036137
theorem B11430827 : Blo 1585491 11430827 := bstep (se 1 (by rfl) ⟨8573120, by rfl⟩ : syracuseStep 11430827 = 17146241) B17146241
theorem B8031149 : Blo 1585491 8031149 := bstep (se 3 (by rfl) ⟨1505840, by rfl⟩ : syracuseStep 8031149 = 3011681) B3011681
theorem B2411495 : Blo 1585491 2411495 := bstep (se 1 (by rfl) ⟨1808621, by rfl⟩ : syracuseStep 2411495 = 3617243) B3617243
theorem B12872785 : Blo 1585491 12872785 := bstep (se 2 (by rfl) ⟨4827294, by rfl⟩ : syracuseStep 12872785 = 9654589) B9654589
theorem B5352587 : Blo 1585491 5352587 := bstep (se 1 (by rfl) ⟨4014440, by rfl⟩ : syracuseStep 5352587 = 8028881) B8028881
theorem B40651955 : Blo 1585491 40651955 := bstep (se 1 (by rfl) ⟨30488966, by rfl⟩ : syracuseStep 40651955 = 60977933) B60977933
theorem B20335819 : Blo 1585491 20335819 := bstep (se 1 (by rfl) ⟨15251864, by rfl⟩ : syracuseStep 20335819 = 30503729) B30503729
theorem B4123943 : Blo 1585491 4123943 := bstep (se 1 (by rfl) ⟨3092957, by rfl⟩ : syracuseStep 4123943 = 6185915) B6185915
theorem B2379047 : Blo 1585491 2379047 := bstep (se 1 (by rfl) ⟨1784285, by rfl⟩ : syracuseStep 2379047 = 3568571) B3568571
theorem B2379131 : Blo 1585491 2379131 := bstep (se 1 (by rfl) ⟨1784348, by rfl⟩ : syracuseStep 2379131 = 3568697) B3568697
theorem B2379257 : Blo 1585491 2379257 := bstep (se 2 (by rfl) ⟨892221, by rfl⟩ : syracuseStep 2379257 = 1784443) B1784443
theorem B4017671 : Blo 1585491 4017671 := bstep (se 1 (by rfl) ⟨3013253, by rfl⟩ : syracuseStep 4017671 = 6026507) B6026507
theorem B4017721 : Blo 1585491 4017721 := bstep (se 2 (by rfl) ⟨1506645, by rfl⟩ : syracuseStep 4017721 = 3013291) B3013291
theorem B2379359 : Blo 1585491 2379359 := bstep (se 1 (by rfl) ⟨1784519, by rfl⟩ : syracuseStep 2379359 = 3569039) B3569039
theorem B3567401 : Blo 1585491 3567401 := bstep (se 2 (by rfl) ⟨1337775, by rfl⟩ : syracuseStep 3567401 = 2675551) B2675551
theorem B2379575 : Blo 1585491 2379575 := bstep (se 1 (by rfl) ⟨1784681, by rfl⟩ : syracuseStep 2379575 = 3569363) B3569363
theorem B4018025 : Blo 1585491 4018025 := bstep (se 2 (by rfl) ⟨1506759, by rfl⟩ : syracuseStep 4018025 = 3013519) B3013519
theorem B10170269 : Blo 1585491 10170269 := bstep (se 3 (by rfl) ⟨1906925, by rfl⟩ : syracuseStep 10170269 = 3813851) B3813851
theorem B3616777 : Blo 1585491 3616777 := bstep (se 2 (by rfl) ⟨1356291, by rfl⟩ : syracuseStep 3616777 = 2712583) B2712583
theorem B2379881 : Blo 1585491 2379881 := bstep (se 2 (by rfl) ⟨892455, by rfl⟩ : syracuseStep 2379881 = 1784911) B1784911
theorem B13545731 : Blo 1585491 13545731 := bstep (se 1 (by rfl) ⟨10159298, by rfl⟩ : syracuseStep 13545731 = 20318597) B20318597
theorem B19566851 : Blo 1585491 19566851 := bstep (se 1 (by rfl) ⟨14675138, by rfl⟩ : syracuseStep 19566851 = 29350277) B29350277
theorem B1585499 : Blo 1585491 1585499 := bstep (se 1 (by rfl) ⟨1189124, by rfl⟩ : syracuseStep 1585499 = 2378249) B2378249
theorem B3010907 : Blo 1585491 3010907 := bstep (se 1 (by rfl) ⟨2258180, by rfl⟩ : syracuseStep 3010907 = 4516361) B4516361
theorem B4518251 : Blo 1585491 4518251 := bstep (se 1 (by rfl) ⟨3388688, by rfl⟩ : syracuseStep 4518251 = 6777377) B6777377
theorem B1585519 : Blo 1585491 1585519 := bstep (se 1 (by rfl) ⟨1189139, by rfl⟩ : syracuseStep 1585519 = 2378279) B2378279
theorem B1585575 : Blo 1585491 1585575 := bstep (se 1 (by rfl) ⟨1189181, by rfl⟩ : syracuseStep 1585575 = 2378363) B2378363
theorem B2380199 : Blo 1585491 2380199 := bstep (se 1 (by rfl) ⟨1785149, by rfl⟩ : syracuseStep 2380199 = 3570299) B3570299
theorem B1585659 : Blo 1585491 1585659 := bstep (se 1 (by rfl) ⟨1189244, by rfl⟩ : syracuseStep 1585659 = 2378489) B2378489
theorem B2380283 : Blo 1585491 2380283 := bstep (se 1 (by rfl) ⟨1785212, by rfl⟩ : syracuseStep 2380283 = 3570425) B3570425
theorem B8032769 : Blo 1585491 8032769 := bstep (se 2 (by rfl) ⟨3012288, by rfl⟩ : syracuseStep 8032769 = 6024577) B6024577
theorem B1585727 : Blo 1585491 1585727 := bstep (se 1 (by rfl) ⟨1189295, by rfl⟩ : syracuseStep 1585727 = 2378591) B2378591
theorem B1585735 : Blo 1585491 1585735 := bstep (se 1 (by rfl) ⟨1189301, by rfl⟩ : syracuseStep 1585735 = 2378603) B2378603
theorem B2380409 : Blo 1585491 2380409 := bstep (se 2 (by rfl) ⟨892653, by rfl⟩ : syracuseStep 2380409 = 1785307) B1785307
theorem B12210841 : Blo 1585491 12210841 := bstep (se 2 (by rfl) ⟨4579065, by rfl⟩ : syracuseStep 12210841 = 9158131) B9158131
theorem B2380463 : Blo 1585491 2380463 := bstep (se 1 (by rfl) ⟨1785347, by rfl⟩ : syracuseStep 2380463 = 3570695) B3570695
theorem B1585887 : Blo 1585491 1585887 := bstep (se 1 (by rfl) ⟨1189415, by rfl⟩ : syracuseStep 1585887 = 2378831) B2378831
theorem B5354207 : Blo 1585491 5354207 := bstep (se 1 (by rfl) ⟨4015655, by rfl⟩ : syracuseStep 5354207 = 8031311) B8031311
theorem B2380511 : Blo 1585491 2380511 := bstep (se 1 (by rfl) ⟨1785383, by rfl⟩ : syracuseStep 2380511 = 3570767) B3570767
theorem B6435551 : Blo 1585491 6435551 := bstep (se 1 (by rfl) ⟨4826663, by rfl⟩ : syracuseStep 6435551 = 9653327) B9653327
theorem B3011347 : Blo 1585491 3011347 := bstep (se 1 (by rfl) ⟨2258510, by rfl⟩ : syracuseStep 3011347 = 4517021) B4517021
theorem B1585967 : Blo 1585491 1585967 := bstep (se 1 (by rfl) ⟨1189475, by rfl⟩ : syracuseStep 1585967 = 2378951) B2378951
theorem B3568463 : Blo 1585491 3568463 := bstep (se 1 (by rfl) ⟨2676347, by rfl⟩ : syracuseStep 3568463 = 5352695) B5352695
theorem B1586075 : Blo 1585491 1586075 := bstep (se 1 (by rfl) ⟨1189556, by rfl⟩ : syracuseStep 1586075 = 2379113) B2379113
theorem B1586127 : Blo 1585491 1586127 := bstep (se 1 (by rfl) ⟨1189595, by rfl⟩ : syracuseStep 1586127 = 2379191) B2379191
theorem B1586151 : Blo 1585491 1586151 := bstep (se 1 (by rfl) ⟨1189613, by rfl⟩ : syracuseStep 1586151 = 2379227) B2379227
theorem B8033255 : Blo 1585491 8033255 := bstep (se 1 (by rfl) ⟨6024941, by rfl⟩ : syracuseStep 8033255 = 12049883) B12049883
theorem B2380775 : Blo 1585491 2380775 := bstep (se 1 (by rfl) ⟨1785581, by rfl⟩ : syracuseStep 2380775 = 3571163) B3571163
theorem B3011575 : Blo 1585491 3011575 := bstep (se 1 (by rfl) ⟨2258681, by rfl⟩ : syracuseStep 3011575 = 4517363) B4517363
theorem B3568679 : Blo 1585491 3568679 := bstep (se 1 (by rfl) ⟨2676509, by rfl⟩ : syracuseStep 3568679 = 5353019) B5353019
theorem B38581373 : Blo 1585491 38581373 := bstep (se 3 (by rfl) ⟨7234007, by rfl⟩ : syracuseStep 38581373 = 14468015) B14468015
theorem B2675855 : Blo 1585491 2675855 := bstep (se 1 (by rfl) ⟨2006891, by rfl⟩ : syracuseStep 2675855 = 4013783) B4013783
theorem B5354639 : Blo 1585491 5354639 := bstep (se 1 (by rfl) ⟨4015979, by rfl⟩ : syracuseStep 5354639 = 8031959) B8031959
theorem B3568859 : Blo 1585491 3568859 := bstep (se 1 (by rfl) ⟨2676644, by rfl⟩ : syracuseStep 3568859 = 5353289) B5353289
theorem B2446555 : Blo 1585491 2446555 := bstep (se 1 (by rfl) ⟨1834916, by rfl⟩ : syracuseStep 2446555 = 3669833) B3669833
theorem B2381033 : Blo 1585491 2381033 := bstep (se 2 (by rfl) ⟨892887, by rfl⟩ : syracuseStep 2381033 = 1785775) B1785775
theorem B1586463 : Blo 1585491 1586463 := bstep (se 1 (by rfl) ⟨1189847, by rfl⟩ : syracuseStep 1586463 = 2379695) B2379695
theorem B2381087 : Blo 1585491 2381087 := bstep (se 1 (by rfl) ⟨1785815, by rfl⟩ : syracuseStep 2381087 = 3571631) B3571631
theorem B3011879 : Blo 1585491 3011879 := bstep (se 1 (by rfl) ⟨2258909, by rfl⟩ : syracuseStep 3011879 = 4517819) B4517819
theorem B8033579 : Blo 1585491 8033579 := bstep (se 1 (by rfl) ⟨6025184, by rfl⟩ : syracuseStep 8033579 = 12050369) B12050369
theorem B1586523 : Blo 1585491 1586523 := bstep (se 1 (by rfl) ⟨1189892, by rfl⟩ : syracuseStep 1586523 = 2379785) B2379785
theorem B1586543 : Blo 1585491 1586543 := bstep (se 1 (by rfl) ⟨1189907, by rfl⟩ : syracuseStep 1586543 = 2379815) B2379815
theorem B2676091 : Blo 1585491 2676091 := bstep (se 1 (by rfl) ⟨2007068, by rfl⟩ : syracuseStep 2676091 = 4014137) B4014137
theorem B8574331 : Blo 1585491 8574331 := bstep (se 1 (by rfl) ⟨6430748, by rfl⟩ : syracuseStep 8574331 = 12861497) B12861497
theorem B3569057 : Blo 1585491 3569057 := bstep (se 2 (by rfl) ⟨1338396, by rfl⟩ : syracuseStep 3569057 = 2676793) B2676793
theorem B1586599 : Blo 1585491 1586599 := bstep (se 1 (by rfl) ⟨1189949, by rfl⟩ : syracuseStep 1586599 = 2379899) B2379899
theorem B1586683 : Blo 1585491 1586683 := bstep (se 1 (by rfl) ⟨1190012, by rfl⟩ : syracuseStep 1586683 = 2380025) B2380025
theorem B1586751 : Blo 1585491 1586751 := bstep (se 1 (by rfl) ⟨1190063, by rfl⟩ : syracuseStep 1586751 = 2380127) B2380127
theorem B1586759 : Blo 1585491 1586759 := bstep (se 1 (by rfl) ⟨1190069, by rfl⟩ : syracuseStep 1586759 = 2380139) B2380139
theorem B17381051 : Blo 1585491 17381051 := bstep (se 1 (by rfl) ⟨13035788, by rfl⟩ : syracuseStep 17381051 = 26071577) B26071577
theorem B9033403 : Blo 1585491 9033403 := bstep (se 1 (by rfl) ⟨6775052, by rfl⟩ : syracuseStep 9033403 = 13550105) B13550105
theorem B1586911 : Blo 1585491 1586911 := bstep (se 1 (by rfl) ⟨1190183, by rfl⟩ : syracuseStep 1586911 = 2380367) B2380367
theorem B38614765 : Blo 1585491 38614765 := bstep (se 3 (by rfl) ⟨7240268, by rfl⟩ : syracuseStep 38614765 = 14480537) B14480537
theorem B1586991 : Blo 1585491 1586991 := bstep (se 1 (by rfl) ⟨1190243, by rfl⟩ : syracuseStep 1586991 = 2380487) B2380487
theorem B123655987 : Blo 1585491 123655987 := bstep (se 1 (by rfl) ⟨92741990, by rfl⟩ : syracuseStep 123655987 = 185483981) B185483981
theorem B34322231 : Blo 1585491 34322231 := bstep (se 1 (by rfl) ⟨25741673, by rfl⟩ : syracuseStep 34322231 = 51483347) B51483347
theorem B1587099 : Blo 1585491 1587099 := bstep (se 1 (by rfl) ⟨1190324, by rfl⟩ : syracuseStep 1587099 = 2380649) B2380649
theorem B1783759 : Blo 1585491 1783759 := bstep (se 1 (by rfl) ⟨1337819, by rfl⟩ : syracuseStep 1783759 = 2675639) B2675639
theorem B3569615 : Blo 1585491 3569615 := bstep (se 1 (by rfl) ⟨2677211, by rfl⟩ : syracuseStep 3569615 = 5354423) B5354423
theorem B1587151 : Blo 1585491 1587151 := bstep (se 1 (by rfl) ⟨1190363, by rfl⟩ : syracuseStep 1587151 = 2380727) B2380727
theorem B1587175 : Blo 1585491 1587175 := bstep (se 1 (by rfl) ⟨1190381, by rfl⟩ : syracuseStep 1587175 = 2380763) B2380763
theorem B21706795 : Blo 1585491 21706795 := bstep (se 1 (by rfl) ⟨16280096, by rfl⟩ : syracuseStep 21706795 = 32560193) B32560193
theorem B8034551 : Blo 1585491 8034551 := bstep (se 1 (by rfl) ⟨6025913, by rfl⟩ : syracuseStep 8034551 = 12051827) B12051827
theorem B5355773 : Blo 1585491 5355773 := bstep (se 3 (by rfl) ⟨1004207, by rfl⟩ : syracuseStep 5355773 = 2008415) B2008415
theorem B1587487 : Blo 1585491 1587487 := bstep (se 1 (by rfl) ⟨1190615, by rfl⟩ : syracuseStep 1587487 = 2381231) B2381231
theorem B3569993 : Blo 1585491 3569993 := bstep (se 2 (by rfl) ⟨1338747, by rfl⟩ : syracuseStep 3569993 = 2677495) B2677495
theorem B1784155 : Blo 1585491 1784155 := bstep (se 1 (by rfl) ⟨1338116, by rfl⟩ : syracuseStep 1784155 = 2676233) B2676233
theorem B3570011 : Blo 1585491 3570011 := bstep (se 1 (by rfl) ⟨2677508, by rfl⟩ : syracuseStep 3570011 = 5355017) B5355017
theorem B6109607 : Blo 1585491 6109607 := bstep (se 1 (by rfl) ⟨4582205, by rfl⟩ : syracuseStep 6109607 = 9164411) B9164411
theorem B1784263 : Blo 1585491 1784263 := bstep (se 1 (by rfl) ⟨1338197, by rfl⟩ : syracuseStep 1784263 = 2676395) B2676395
theorem B3054035 : Blo 1585491 3054035 := bstep (se 1 (by rfl) ⟨2290526, by rfl⟩ : syracuseStep 3054035 = 4581053) B4581053
theorem B3054143 : Blo 1585491 3054143 := bstep (se 1 (by rfl) ⟨2290607, by rfl⟩ : syracuseStep 3054143 = 4581215) B4581215
theorem B3013193 : Blo 1585491 3013193 := bstep (se 2 (by rfl) ⟨1129947, by rfl⟩ : syracuseStep 3013193 = 2259895) B2259895
theorem B8035037 : Blo 1585491 8035037 := bstep (se 3 (by rfl) ⟨1506569, by rfl⟩ : syracuseStep 8035037 = 3013139) B3013139
theorem B21715715 : Blo 1585491 21715715 := bstep (se 1 (by rfl) ⟨16286786, by rfl⟩ : syracuseStep 21715715 = 32573573) B32573573
theorem B1784623 : Blo 1585491 1784623 := bstep (se 1 (by rfl) ⟨1338467, by rfl⟩ : syracuseStep 1784623 = 2676935) B2676935
theorem B2677583 : Blo 1585491 2677583 := bstep (se 1 (by rfl) ⟨2008187, by rfl⟩ : syracuseStep 2677583 = 4016375) B4016375
theorem B1784731 : Blo 1585491 1784731 := bstep (se 1 (by rfl) ⟨1338548, by rfl⟩ : syracuseStep 1784731 = 2677097) B2677097
theorem B3570587 : Blo 1585491 3570587 := bstep (se 1 (by rfl) ⟨2677940, by rfl⟩ : syracuseStep 3570587 = 5355881) B5355881
theorem B5356583 : Blo 1585491 5356583 := bstep (se 1 (by rfl) ⟨4017437, by rfl⟩ : syracuseStep 5356583 = 8034875) B8034875
theorem B3570785 : Blo 1585491 3570785 := bstep (se 2 (by rfl) ⟨1339044, by rfl⟩ : syracuseStep 3570785 = 2678089) B2678089
theorem B13548707 : Blo 1585491 13548707 := bstep (se 1 (by rfl) ⟨10161530, by rfl⟩ : syracuseStep 13548707 = 20323061) B20323061
theorem B16497931 : Blo 1585491 16497931 := bstep (se 1 (by rfl) ⟨12373448, by rfl⟩ : syracuseStep 16497931 = 24746897) B24746897
theorem B8027423 : Blo 1585491 8027423 := bstep (se 1 (by rfl) ⟨6020567, by rfl⟩ : syracuseStep 8027423 = 12041135) B12041135
theorem B1785127 : Blo 1585491 1785127 := bstep (se 1 (by rfl) ⟨1338845, by rfl⟩ : syracuseStep 1785127 = 2677691) B2677691
theorem B3570983 : Blo 1585491 3570983 := bstep (se 1 (by rfl) ⟨2678237, by rfl⟩ : syracuseStep 3570983 = 5356475) B5356475
theorem B1785199 : Blo 1585491 1785199 := bstep (se 1 (by rfl) ⟨1338899, by rfl⟩ : syracuseStep 1785199 = 2677799) B2677799
theorem B7241147 : Blo 1585491 7241147 := bstep (se 1 (by rfl) ⟨5430860, by rfl⟩ : syracuseStep 7241147 = 10861721) B10861721
theorem B5357015 : Blo 1585491 5357015 := bstep (se 1 (by rfl) ⟨4017761, by rfl⟩ : syracuseStep 5357015 = 8035523) B8035523
theorem B15244793 : Blo 1585491 15244793 := bstep (se 2 (by rfl) ⟨5716797, by rfl⟩ : syracuseStep 15244793 = 11433595) B11433595
theorem B1785415 : Blo 1585491 1785415 := bstep (se 1 (by rfl) ⟨1339061, by rfl⟩ : syracuseStep 1785415 = 2678123) B2678123
theorem B6020689 : Blo 1585491 6020689 := bstep (se 2 (by rfl) ⟨2257758, by rfl⟩ : syracuseStep 6020689 = 4515517) B4515517
theorem B4013651 : Blo 1585491 4013651 := bstep (se 1 (by rfl) ⟨3010238, by rfl⟩ : syracuseStep 4013651 = 6020477) B6020477
theorem B3571361 : Blo 1585491 3571361 := bstep (se 2 (by rfl) ⟨1339260, by rfl⟩ : syracuseStep 3571361 = 2678521) B2678521
theorem B52191017 : Blo 1585491 52191017 := bstep (se 2 (by rfl) ⟨19571631, by rfl⟩ : syracuseStep 52191017 = 39143263) B39143263
theorem B2678575 : Blo 1585491 2678575 := bstep (se 1 (by rfl) ⟨2008931, by rfl⟩ : syracuseStep 2678575 = 4017863) B4017863
theorem B43417417 : Blo 1585491 43417417 := bstep (se 2 (by rfl) ⟨16281531, by rfl⟩ : syracuseStep 43417417 = 32563063) B32563063
theorem B6020993 : Blo 1585491 6020993 := bstep (se 2 (by rfl) ⟨2257872, by rfl⟩ : syracuseStep 6020993 = 4515745) B4515745
theorem B28942393 : Blo 1585491 28942393 := bstep (se 2 (by rfl) ⟨10853397, by rfl⟩ : syracuseStep 28942393 = 21706795) B21706795
theorem B4014299 : Blo 1585491 4014299 := bstep (se 1 (by rfl) ⟨3010724, by rfl⟩ : syracuseStep 4014299 = 6021449) B6021449
theorem B2007271 : Blo 1585491 2007271 := bstep (se 1 (by rfl) ⟨1505453, by rfl⟩ : syracuseStep 2007271 = 3010907) B3010907
theorem B5079547 : Blo 1585491 5079547 := bstep (se 1 (by rfl) ⟨3809660, by rfl⟩ : syracuseStep 5079547 = 7619321) B7619321
theorem B2007919 : Blo 1585491 2007919 := bstep (se 1 (by rfl) ⟨1505939, by rfl⟩ : syracuseStep 2007919 = 3011879) B3011879
theorem B18080657 : Blo 1585491 18080657 := bstep (se 2 (by rfl) ⟨6780246, by rfl⟩ : syracuseStep 18080657 = 13560493) B13560493
theorem B4015129 : Blo 1585491 4015129 := bstep (se 2 (by rfl) ⟨1505673, by rfl⟩ : syracuseStep 4015129 = 3011347) B3011347
theorem B4015433 : Blo 1585491 4015433 := bstep (se 2 (by rfl) ⟨1505787, by rfl⟩ : syracuseStep 4015433 = 3011575) B3011575
theorem B17163713 : Blo 1585491 17163713 := bstep (se 2 (by rfl) ⟨6436392, by rfl⟩ : syracuseStep 17163713 = 12872785) B12872785
theorem B8144381 : Blo 1585491 8144381 := bstep (se 3 (by rfl) ⟨1527071, by rfl⟩ : syracuseStep 8144381 = 3054143) B3054143
theorem B4015727 : Blo 1585491 4015727 := bstep (se 1 (by rfl) ⟨3011795, by rfl⟩ : syracuseStep 4015727 = 6023591) B6023591
theorem B3262073 : Blo 1585491 3262073 := bstep (se 2 (by rfl) ⟨1223277, by rfl⟩ : syracuseStep 3262073 = 2446555) B2446555
theorem B21997241 : Blo 1585491 21997241 := bstep (se 2 (by rfl) ⟨8248965, by rfl⟩ : syracuseStep 21997241 = 16497931) B16497931
theorem B2008795 : Blo 1585491 2008795 := bstep (se 1 (by rfl) ⟨1506596, by rfl⟩ : syracuseStep 2008795 = 3013193) B3013193
theorem B14477143 : Blo 1585491 14477143 := bstep (se 1 (by rfl) ⟨10857857, by rfl⟩ : syracuseStep 14477143 = 21715715) B21715715
theorem B41224045 : Blo 1585491 41224045 := bstep (se 3 (by rfl) ⟨7729508, by rfl⟩ : syracuseStep 41224045 = 15459017) B15459017
theorem B7620551 : Blo 1585491 7620551 := bstep (se 1 (by rfl) ⟨5715413, by rfl⟩ : syracuseStep 7620551 = 11430827) B11430827
theorem B1607663 : Blo 1585491 1607663 := bstep (se 1 (by rfl) ⟨1205747, by rfl⟩ : syracuseStep 1607663 = 2411495) B2411495
theorem B27101303 : Blo 1585491 27101303 := bstep (se 1 (by rfl) ⟨20325977, by rfl⟩ : syracuseStep 27101303 = 40651955) B40651955
theorem B5351615 : Blo 1585491 5351615 := bstep (se 1 (by rfl) ⟨4013711, by rfl⟩ : syracuseStep 5351615 = 8027423) B8027423
theorem B12044537 : Blo 1585491 12044537 := bstep (se 2 (by rfl) ⟨4516701, by rfl⟩ : syracuseStep 12044537 = 9033403) B9033403
theorem B4827431 : Blo 1585491 4827431 := bstep (se 1 (by rfl) ⟨3620573, by rfl⟩ : syracuseStep 4827431 = 7241147) B7241147
theorem B164874649 : Blo 1585491 164874649 := bstep (se 2 (by rfl) ⟨61827993, by rfl⟩ : syracuseStep 164874649 = 123655987) B123655987
theorem B2378267 : Blo 1585491 2378267 := bstep (se 1 (by rfl) ⟨1783700, by rfl⟩ : syracuseStep 2378267 = 3567401) B3567401
theorem B34794011 : Blo 1585491 34794011 := bstep (se 1 (by rfl) ⟨26095508, by rfl⟩ : syracuseStep 34794011 = 52191017) B52191017
theorem B2378345 : Blo 1585491 2378345 := bstep (se 2 (by rfl) ⟨891879, by rfl⟩ : syracuseStep 2378345 = 1783759) B1783759
theorem B8030825 : Blo 1585491 8030825 := bstep (se 2 (by rfl) ⟨3011559, by rfl⟩ : syracuseStep 8030825 = 6023119) B6023119
theorem B11430595 : Blo 1585491 11430595 := bstep (se 1 (by rfl) ⟨8572946, by rfl⟩ : syracuseStep 11430595 = 17145893) B17145893
theorem B9030487 : Blo 1585491 9030487 := bstep (se 1 (by rfl) ⟨6772865, by rfl⟩ : syracuseStep 9030487 = 13545731) B13545731
theorem B9038735 : Blo 1585491 9038735 := bstep (se 1 (by rfl) ⟨6779051, by rfl⟩ : syracuseStep 9038735 = 13558103) B13558103
theorem B2378873 : Blo 1585491 2378873 := bstep (se 2 (by rfl) ⟨892077, by rfl⟩ : syracuseStep 2378873 = 1784155) B1784155
theorem B15281287 : Blo 1585491 15281287 := bstep (se 1 (by rfl) ⟨11460965, by rfl⟩ : syracuseStep 15281287 = 22921931) B22921931
theorem B2378975 : Blo 1585491 2378975 := bstep (se 1 (by rfl) ⟨1784231, by rfl⟩ : syracuseStep 2378975 = 3568463) B3568463
theorem B2379017 : Blo 1585491 2379017 := bstep (se 2 (by rfl) ⟨892131, by rfl⟩ : syracuseStep 2379017 = 1784263) B1784263
theorem B52178269 : Blo 1585491 52178269 := bstep (se 3 (by rfl) ⟨9783425, by rfl⟩ : syracuseStep 52178269 = 19566851) B19566851
theorem B2379119 : Blo 1585491 2379119 := bstep (se 1 (by rfl) ⟨1784339, by rfl⟩ : syracuseStep 2379119 = 3568679) B3568679
theorem B2379239 : Blo 1585491 2379239 := bstep (se 1 (by rfl) ⟨1784429, by rfl⟩ : syracuseStep 2379239 = 3568859) B3568859
theorem B2379371 : Blo 1585491 2379371 := bstep (se 1 (by rfl) ⟨1784528, by rfl⟩ : syracuseStep 2379371 = 3569057) B3569057
theorem B3010223 : Blo 1585491 3010223 := bstep (se 1 (by rfl) ⟨2257667, by rfl⟩ : syracuseStep 3010223 = 4515335) B4515335
theorem B2379497 : Blo 1585491 2379497 := bstep (se 2 (by rfl) ⟨892311, by rfl⟩ : syracuseStep 2379497 = 1784623) B1784623
theorem B5353235 : Blo 1585491 5353235 := bstep (se 1 (by rfl) ⟨4014926, by rfl⟩ : syracuseStep 5353235 = 8029853) B8029853
theorem B11587367 : Blo 1585491 11587367 := bstep (se 1 (by rfl) ⟨8690525, by rfl⟩ : syracuseStep 11587367 = 17381051) B17381051
theorem B2379641 : Blo 1585491 2379641 := bstep (se 2 (by rfl) ⟨892365, by rfl⟩ : syracuseStep 2379641 = 1784731) B1784731
theorem B8032121 : Blo 1585491 8032121 := bstep (se 2 (by rfl) ⟨3012045, by rfl⟩ : syracuseStep 8032121 = 6024091) B6024091
theorem B5500811 : Blo 1585491 5500811 := bstep (se 1 (by rfl) ⟨4125608, by rfl⟩ : syracuseStep 5500811 = 8251217) B8251217
theorem B3010459 : Blo 1585491 3010459 := bstep (se 1 (by rfl) ⟨2257844, by rfl⟩ : syracuseStep 3010459 = 4515689) B4515689
theorem B2379743 : Blo 1585491 2379743 := bstep (se 1 (by rfl) ⟨1784807, by rfl⟩ : syracuseStep 2379743 = 3569615) B3569615
theorem B2379995 : Blo 1585491 2379995 := bstep (se 1 (by rfl) ⟨1784996, by rfl⟩ : syracuseStep 2379995 = 3569993) B3569993
theorem B2380007 : Blo 1585491 2380007 := bstep (se 1 (by rfl) ⟨1785005, by rfl⟩ : syracuseStep 2380007 = 3570011) B3570011
theorem B2036023 : Blo 1585491 2036023 := bstep (se 1 (by rfl) ⟨1527017, by rfl⟩ : syracuseStep 2036023 = 3054035) B3054035
theorem B45740375 : Blo 1585491 45740375 := bstep (se 1 (by rfl) ⟨34305281, by rfl⟩ : syracuseStep 45740375 = 68610563) B68610563
theorem B1585535 : Blo 1585491 1585535 := bstep (se 1 (by rfl) ⟨1189151, by rfl⟩ : syracuseStep 1585535 = 2378303) B2378303
theorem B2380169 : Blo 1585491 2380169 := bstep (se 2 (by rfl) ⟨892563, by rfl⟩ : syracuseStep 2380169 = 1785127) B1785127
theorem B1585615 : Blo 1585491 1585615 := bstep (se 1 (by rfl) ⟨1189211, by rfl⟩ : syracuseStep 1585615 = 2378423) B2378423
theorem B2380265 : Blo 1585491 2380265 := bstep (se 2 (by rfl) ⟨892599, by rfl⟩ : syracuseStep 2380265 = 1785199) B1785199
theorem B3568121 : Blo 1585491 3568121 := bstep (se 2 (by rfl) ⟨1338045, by rfl⟩ : syracuseStep 3568121 = 2676091) B2676091
theorem B11432441 : Blo 1585491 11432441 := bstep (se 2 (by rfl) ⟨4287165, by rfl⟩ : syracuseStep 11432441 = 8574331) B8574331
theorem B4518479 : Blo 1585491 4518479 := bstep (se 1 (by rfl) ⟨3388859, by rfl⟩ : syracuseStep 4518479 = 6777719) B6777719
theorem B3568211 : Blo 1585491 3568211 := bstep (se 1 (by rfl) ⟨2676158, by rfl⟩ : syracuseStep 3568211 = 5352317) B5352317
theorem B1585767 : Blo 1585491 1585767 := bstep (se 1 (by rfl) ⟨1189325, by rfl⟩ : syracuseStep 1585767 = 2378651) B2378651
theorem B2380391 : Blo 1585491 2380391 := bstep (se 1 (by rfl) ⟨1785293, by rfl⟩ : syracuseStep 2380391 = 3570587) B3570587
theorem B5354099 : Blo 1585491 5354099 := bstep (se 1 (by rfl) ⟨4015574, by rfl⟩ : syracuseStep 5354099 = 8031149) B8031149
theorem B2380523 : Blo 1585491 2380523 := bstep (se 1 (by rfl) ⟨1785392, by rfl⟩ : syracuseStep 2380523 = 3570785) B3570785
theorem B3568391 : Blo 1585491 3568391 := bstep (se 1 (by rfl) ⟨2676293, by rfl⟩ : syracuseStep 3568391 = 5352587) B5352587
theorem B2380553 : Blo 1585491 2380553 := bstep (se 2 (by rfl) ⟨892707, by rfl⟩ : syracuseStep 2380553 = 1785415) B1785415
theorem B9032471 : Blo 1585491 9032471 := bstep (se 1 (by rfl) ⟨6774353, by rfl⟩ : syracuseStep 9032471 = 13548707) B13548707
theorem B10171169 : Blo 1585491 10171169 := bstep (se 2 (by rfl) ⟨3814188, by rfl⟩ : syracuseStep 10171169 = 7628377) B7628377
theorem B91525949 : Blo 1585491 91525949 := bstep (se 3 (by rfl) ⟨17161115, by rfl⟩ : syracuseStep 91525949 = 34322231) B34322231
theorem B2749295 : Blo 1585491 2749295 := bstep (se 1 (by rfl) ⟨2061971, by rfl⟩ : syracuseStep 2749295 = 4123943) B4123943
theorem B1586031 : Blo 1585491 1586031 := bstep (se 1 (by rfl) ⟨1189523, by rfl⟩ : syracuseStep 1586031 = 2379047) B2379047
theorem B2380655 : Blo 1585491 2380655 := bstep (se 1 (by rfl) ⟨1785491, by rfl⟩ : syracuseStep 2380655 = 3570983) B3570983
theorem B5354369 : Blo 1585491 5354369 := bstep (se 2 (by rfl) ⟨2007888, by rfl⟩ : syracuseStep 5354369 = 4015777) B4015777
theorem B1586087 : Blo 1585491 1586087 := bstep (se 1 (by rfl) ⟨1189565, by rfl⟩ : syracuseStep 1586087 = 2379131) B2379131
theorem B1586171 : Blo 1585491 1586171 := bstep (se 1 (by rfl) ⟨1189628, by rfl⟩ : syracuseStep 1586171 = 2379257) B2379257
theorem B10163195 : Blo 1585491 10163195 := bstep (se 1 (by rfl) ⟨7622396, by rfl⟩ : syracuseStep 10163195 = 15244793) B15244793
theorem B2675767 : Blo 1585491 2675767 := bstep (se 1 (by rfl) ⟨2006825, by rfl⟩ : syracuseStep 2675767 = 4013651) B4013651
theorem B1586239 : Blo 1585491 1586239 := bstep (se 1 (by rfl) ⟨1189679, by rfl⟩ : syracuseStep 1586239 = 2379359) B2379359
theorem B57889889 : Blo 1585491 57889889 := bstep (se 2 (by rfl) ⟨21708708, by rfl⟩ : syracuseStep 57889889 = 43417417) B43417417
theorem B2380907 : Blo 1585491 2380907 := bstep (se 1 (by rfl) ⟨1785680, by rfl⟩ : syracuseStep 2380907 = 3571361) B3571361
theorem B1586383 : Blo 1585491 1586383 := bstep (se 1 (by rfl) ⟨1189787, by rfl⟩ : syracuseStep 1586383 = 2379575) B2379575
theorem B6780179 : Blo 1585491 6780179 := bstep (se 1 (by rfl) ⟨5085134, by rfl⟩ : syracuseStep 6780179 = 10170269) B10170269
theorem B2381147 : Blo 1585491 2381147 := bstep (se 1 (by rfl) ⟨1785860, by rfl⟩ : syracuseStep 2381147 = 3571721) B3571721
theorem B19289477 : Blo 1585491 19289477 := bstep (se 4 (by rfl) ⟨1808388, by rfl⟩ : syracuseStep 19289477 = 3616777) B3616777
theorem B1586587 : Blo 1585491 1586587 := bstep (se 1 (by rfl) ⟨1189940, by rfl⟩ : syracuseStep 1586587 = 2379881) B2379881
theorem B18068993 : Blo 1585491 18068993 := bstep (se 2 (by rfl) ⟨6775872, by rfl⟩ : syracuseStep 18068993 = 13551745) B13551745
theorem B3012167 : Blo 1585491 3012167 := bstep (se 1 (by rfl) ⟨2259125, by rfl⟩ : syracuseStep 3012167 = 4518251) B4518251
theorem B1586799 : Blo 1585491 1586799 := bstep (se 1 (by rfl) ⟨1190099, by rfl⟩ : syracuseStep 1586799 = 2380199) B2380199
theorem B1586855 : Blo 1585491 1586855 := bstep (se 1 (by rfl) ⟨1190141, by rfl⟩ : syracuseStep 1586855 = 2380283) B2380283
theorem B5355179 : Blo 1585491 5355179 := bstep (se 1 (by rfl) ⟨4016384, by rfl⟩ : syracuseStep 5355179 = 8032769) B8032769
theorem B1586939 : Blo 1585491 1586939 := bstep (se 1 (by rfl) ⟨1190204, by rfl⟩ : syracuseStep 1586939 = 2380409) B2380409
theorem B1586975 : Blo 1585491 1586975 := bstep (se 1 (by rfl) ⟨1190231, by rfl⟩ : syracuseStep 1586975 = 2380463) B2380463
theorem B3569471 : Blo 1585491 3569471 := bstep (se 1 (by rfl) ⟨2677103, by rfl⟩ : syracuseStep 3569471 = 5354207) B5354207
theorem B1587007 : Blo 1585491 1587007 := bstep (se 1 (by rfl) ⟨1190255, by rfl⟩ : syracuseStep 1587007 = 2380511) B2380511
theorem B4290367 : Blo 1585491 4290367 := bstep (se 1 (by rfl) ⟨3217775, by rfl⟩ : syracuseStep 4290367 = 6435551) B6435551
theorem B2676719 : Blo 1585491 2676719 := bstep (se 1 (by rfl) ⟨2007539, by rfl⟩ : syracuseStep 2676719 = 4015079) B4015079
theorem B5355503 : Blo 1585491 5355503 := bstep (se 1 (by rfl) ⟨4016627, by rfl⟩ : syracuseStep 5355503 = 8033255) B8033255
theorem B1587183 : Blo 1585491 1587183 := bstep (se 1 (by rfl) ⟨1190387, by rfl⟩ : syracuseStep 1587183 = 2380775) B2380775
theorem B25720915 : Blo 1585491 25720915 := bstep (se 1 (by rfl) ⟨19290686, by rfl⟩ : syracuseStep 25720915 = 38581373) B38581373
theorem B1783903 : Blo 1585491 1783903 := bstep (se 1 (by rfl) ⟨1337927, by rfl⟩ : syracuseStep 1783903 = 2675855) B2675855
theorem B3569759 : Blo 1585491 3569759 := bstep (se 1 (by rfl) ⟨2677319, by rfl⟩ : syracuseStep 3569759 = 5354639) B5354639
theorem B65124485 : Blo 1585491 65124485 := bstep (se 4 (by rfl) ⟨6105420, by rfl⟩ : syracuseStep 65124485 = 12210841) B12210841
theorem B1587355 : Blo 1585491 1587355 := bstep (se 1 (by rfl) ⟨1190516, by rfl⟩ : syracuseStep 1587355 = 2381033) B2381033
theorem B1587391 : Blo 1585491 1587391 := bstep (se 1 (by rfl) ⟨1190543, by rfl⟩ : syracuseStep 1587391 = 2381087) B2381087
theorem B5355719 : Blo 1585491 5355719 := bstep (se 1 (by rfl) ⟨4016789, by rfl⟩ : syracuseStep 5355719 = 8033579) B8033579
theorem B16292285 : Blo 1585491 16292285 := bstep (se 3 (by rfl) ⟨3054803, by rfl⟩ : syracuseStep 16292285 = 6109607) B6109607
theorem B2677279 : Blo 1585491 2677279 := bstep (se 1 (by rfl) ⟨2007959, by rfl⟩ : syracuseStep 2677279 = 4015919) B4015919
theorem B6773345 : Blo 1585491 6773345 := bstep (se 2 (by rfl) ⟨2540004, by rfl⟩ : syracuseStep 6773345 = 5080009) B5080009
theorem B9034361 : Blo 1585491 9034361 := bstep (se 2 (by rfl) ⟨3387885, by rfl⟩ : syracuseStep 9034361 = 6775771) B6775771
theorem B30497579 : Blo 1585491 30497579 := bstep (se 1 (by rfl) ⟨22873184, by rfl⟩ : syracuseStep 30497579 = 45746369) B45746369
theorem B5356367 : Blo 1585491 5356367 := bstep (se 1 (by rfl) ⟨4017275, by rfl⟩ : syracuseStep 5356367 = 8034551) B8034551
theorem B3570515 : Blo 1585491 3570515 := bstep (se 1 (by rfl) ⟨2677886, by rfl⟩ : syracuseStep 3570515 = 5355773) B5355773
theorem B27114425 : Blo 1585491 27114425 := bstep (se 2 (by rfl) ⟨10167909, by rfl⟩ : syracuseStep 27114425 = 20335819) B20335819
theorem B2677711 : Blo 1585491 2677711 := bstep (se 1 (by rfl) ⟨2008283, by rfl⟩ : syracuseStep 2677711 = 4016567) B4016567
theorem B5356691 : Blo 1585491 5356691 := bstep (se 1 (by rfl) ⟨4017518, by rfl⟩ : syracuseStep 5356691 = 8035037) B8035037
theorem B1785055 : Blo 1585491 1785055 := bstep (se 1 (by rfl) ⟨1338791, by rfl⟩ : syracuseStep 1785055 = 2677583) B2677583
theorem B3571055 : Blo 1585491 3571055 := bstep (se 1 (by rfl) ⟨2678291, by rfl⟩ : syracuseStep 3571055 = 5356583) B5356583
theorem B5356961 : Blo 1585491 5356961 := bstep (se 2 (by rfl) ⟨2008860, by rfl⟩ : syracuseStep 5356961 = 4017721) B4017721
theorem B8027585 : Blo 1585491 8027585 := bstep (se 2 (by rfl) ⟨3010344, by rfl⟩ : syracuseStep 8027585 = 6020689) B6020689
theorem B3571343 : Blo 1585491 3571343 := bstep (se 1 (by rfl) ⟨2678507, by rfl⟩ : syracuseStep 3571343 = 5357015) B5357015
theorem B51486353 : Blo 1585491 51486353 := bstep (se 2 (by rfl) ⟨19307382, by rfl⟩ : syracuseStep 51486353 = 38614765) B38614765
theorem B2678447 : Blo 1585491 2678447 := bstep (se 1 (by rfl) ⟨2008835, by rfl⟩ : syracuseStep 2678447 = 4017671) B4017671
theorem B3571433 : Blo 1585491 3571433 := bstep (se 2 (by rfl) ⟨1339287, by rfl⟩ : syracuseStep 3571433 = 2678575) B2678575
theorem B2678683 : Blo 1585491 2678683 := bstep (se 1 (by rfl) ⟨2009012, by rfl⟩ : syracuseStep 2678683 = 4018025) B4018025
theorem B4013995 : Blo 1585491 4013995 := bstep (se 1 (by rfl) ⟨3010496, by rfl⟩ : syracuseStep 4013995 = 6020993) B6020993
theorem B5357501 : Blo 1585491 5357501 := bstep (se 3 (by rfl) ⟨1004531, by rfl⟩ : syracuseStep 5357501 = 2009063) B2009063
theorem B6021647 : Blo 1585491 6021647 := bstep (se 1 (by rfl) ⟨4516235, by rfl⟩ : syracuseStep 6021647 = 9032471) B9032471
theorem B219832865 : Blo 1585491 219832865 := bstep (se 2 (by rfl) ⟨82437324, by rfl⟩ : syracuseStep 219832865 = 164874649) B164874649
theorem B6775463 : Blo 1585491 6775463 := bstep (se 1 (by rfl) ⟨5081597, by rfl⟩ : syracuseStep 6775463 = 10163195) B10163195
theorem B38593259 : Blo 1585491 38593259 := bstep (se 1 (by rfl) ⟨28944944, by rfl⟩ : syracuseStep 38593259 = 57889889) B57889889
theorem B14664827 : Blo 1585491 14664827 := bstep (se 1 (by rfl) ⟨10998620, by rfl⟩ : syracuseStep 14664827 = 21997241) B21997241
theorem B5080367 : Blo 1585491 5080367 := bstep (se 1 (by rfl) ⟨3810275, by rfl⟩ : syracuseStep 5080367 = 7620551) B7620551
theorem B8029691 : Blo 1585491 8029691 := bstep (se 1 (by rfl) ⟨6022268, by rfl⟩ : syracuseStep 8029691 = 12044537) B12044537
theorem B4515563 : Blo 1585491 4515563 := bstep (se 1 (by rfl) ⟨3386672, by rfl⟩ : syracuseStep 4515563 = 6773345) B6773345
theorem B6022907 : Blo 1585491 6022907 := bstep (se 1 (by rfl) ⟨4517180, by rfl⟩ : syracuseStep 6022907 = 9034361) B9034361
theorem B5351723 : Blo 1585491 5351723 := bstep (se 1 (by rfl) ⟨4013792, by rfl⟩ : syracuseStep 5351723 = 8027585) B8027585
theorem B5720489 : Blo 1585491 5720489 := bstep (se 2 (by rfl) ⟨2145183, by rfl⟩ : syracuseStep 5720489 = 4290367) B4290367
theorem B19302857 : Blo 1585491 19302857 := bstep (se 2 (by rfl) ⟨7238571, by rfl⟩ : syracuseStep 19302857 = 14477143) B14477143
theorem B5351993 : Blo 1585491 5351993 := bstep (se 2 (by rfl) ⟨2006997, by rfl⟩ : syracuseStep 5351993 = 4013995) B4013995
theorem B4287101 : Blo 1585491 4287101 := bstep (se 3 (by rfl) ⟨803831, by rfl⟩ : syracuseStep 4287101 = 1607663) B1607663
theorem B34294553 : Blo 1585491 34294553 := bstep (se 2 (by rfl) ⟨12860457, by rfl⟩ : syracuseStep 34294553 = 25720915) B25720915
theorem B2378537 : Blo 1585491 2378537 := bstep (se 2 (by rfl) ⟨891951, by rfl⟩ : syracuseStep 2378537 = 1783903) B1783903
theorem B30493583 : Blo 1585491 30493583 := bstep (se 1 (by rfl) ⟨22870187, by rfl⟩ : syracuseStep 30493583 = 45740375) B45740375
theorem B2378747 : Blo 1585491 2378747 := bstep (se 1 (by rfl) ⟨1784060, by rfl⟩ : syracuseStep 2378747 = 3568121) B3568121
theorem B7621627 : Blo 1585491 7621627 := bstep (se 1 (by rfl) ⟨5716220, by rfl⟩ : syracuseStep 7621627 = 11432441) B11432441
theorem B2378807 : Blo 1585491 2378807 := bstep (se 1 (by rfl) ⟨1784105, by rfl⟩ : syracuseStep 2378807 = 3568211) B3568211
theorem B2378927 : Blo 1585491 2378927 := bstep (se 1 (by rfl) ⟨1784195, by rfl⟩ : syracuseStep 2378927 = 3568391) B3568391
theorem B61017299 : Blo 1585491 61017299 := bstep (se 1 (by rfl) ⟨45762974, by rfl⟩ : syracuseStep 61017299 = 91525949) B91525949
theorem B12053771 : Blo 1585491 12053771 := bstep (se 1 (by rfl) ⟨9040328, by rfl⟩ : syracuseStep 12053771 = 18080657) B18080657
theorem B15240793 : Blo 1585491 15240793 := bstep (se 2 (by rfl) ⟨5715297, by rfl⟩ : syracuseStep 15240793 = 11430595) B11430595
theorem B12045995 : Blo 1585491 12045995 := bstep (se 1 (by rfl) ⟨9034496, by rfl⟩ : syracuseStep 12045995 = 18068993) B18068993
theorem B2379647 : Blo 1585491 2379647 := bstep (se 1 (by rfl) ⟨1784735, by rfl⟩ : syracuseStep 2379647 = 3569471) B3569471
theorem B5353505 : Blo 1585491 5353505 := bstep (se 2 (by rfl) ⟨2007564, by rfl⟩ : syracuseStep 5353505 = 4015129) B4015129
theorem B2379839 : Blo 1585491 2379839 := bstep (se 1 (by rfl) ⟨1784879, by rfl⟩ : syracuseStep 2379839 = 3569759) B3569759
theorem B3567689 : Blo 1585491 3567689 := bstep (se 2 (by rfl) ⟨1337883, by rfl⟩ : syracuseStep 3567689 = 2675767) B2675767
theorem B18067535 : Blo 1585491 18067535 := bstep (se 1 (by rfl) ⟨13550651, by rfl⟩ : syracuseStep 18067535 = 27101303) B27101303
theorem B3567743 : Blo 1585491 3567743 := bstep (se 1 (by rfl) ⟨2675807, by rfl⟩ : syracuseStep 3567743 = 5351615) B5351615
theorem B8032445 : Blo 1585491 8032445 := bstep (se 3 (by rfl) ⟨1506083, by rfl⟩ : syracuseStep 8032445 = 3012167) B3012167
theorem B10858789 : Blo 1585491 10858789 := bstep (se 4 (by rfl) ⟨1018011, by rfl⟩ : syracuseStep 10858789 = 2036023) B2036023
theorem B2380073 : Blo 1585491 2380073 := bstep (se 2 (by rfl) ⟨892527, by rfl⟩ : syracuseStep 2380073 = 1785055) B1785055
theorem B1585511 : Blo 1585491 1585511 := bstep (se 1 (by rfl) ⟨1189133, by rfl⟩ : syracuseStep 1585511 = 2378267) B2378267
theorem B23196007 : Blo 1585491 23196007 := bstep (se 1 (by rfl) ⟨17397005, by rfl⟩ : syracuseStep 23196007 = 34794011) B34794011
theorem B1585563 : Blo 1585491 1585563 := bstep (se 1 (by rfl) ⟨1189172, by rfl⟩ : syracuseStep 1585563 = 2378345) B2378345
theorem B5353883 : Blo 1585491 5353883 := bstep (se 1 (by rfl) ⟨4015412, by rfl⟩ : syracuseStep 5353883 = 8030825) B8030825
theorem B69571025 : Blo 1585491 69571025 := bstep (se 2 (by rfl) ⟨26089134, by rfl⟩ : syracuseStep 69571025 = 52178269) B52178269
theorem B2380343 : Blo 1585491 2380343 := bstep (se 1 (by rfl) ⟨1785257, by rfl⟩ : syracuseStep 2380343 = 3570515) B3570515
theorem B6025823 : Blo 1585491 6025823 := bstep (se 1 (by rfl) ⟨4519367, by rfl⟩ : syracuseStep 6025823 = 9038735) B9038735
theorem B18076283 : Blo 1585491 18076283 := bstep (se 1 (by rfl) ⟨13557212, by rfl⟩ : syracuseStep 18076283 = 27114425) B27114425
theorem B1585915 : Blo 1585491 1585915 := bstep (se 1 (by rfl) ⟨1189436, by rfl⟩ : syracuseStep 1585915 = 2378873) B2378873
theorem B1585983 : Blo 1585491 1585983 := bstep (se 1 (by rfl) ⟨1189487, by rfl⟩ : syracuseStep 1585983 = 2378975) B2378975
theorem B1586011 : Blo 1585491 1586011 := bstep (se 1 (by rfl) ⟨1189508, by rfl⟩ : syracuseStep 1586011 = 2379017) B2379017
theorem B1586079 : Blo 1585491 1586079 := bstep (se 1 (by rfl) ⟨1189559, by rfl⟩ : syracuseStep 1586079 = 2379119) B2379119
theorem B2380703 : Blo 1585491 2380703 := bstep (se 1 (by rfl) ⟨1785527, by rfl⟩ : syracuseStep 2380703 = 3571055) B3571055
theorem B1586159 : Blo 1585491 1586159 := bstep (se 1 (by rfl) ⟨1189619, by rfl⟩ : syracuseStep 1586159 = 2379239) B2379239
theorem B1586247 : Blo 1585491 1586247 := bstep (se 1 (by rfl) ⟨1189685, by rfl⟩ : syracuseStep 1586247 = 2379371) B2379371
theorem B2380895 : Blo 1585491 2380895 := bstep (se 1 (by rfl) ⟨1785671, by rfl⟩ : syracuseStep 2380895 = 3571343) B3571343
theorem B54965393 : Blo 1585491 54965393 := bstep (se 2 (by rfl) ⟨20612022, by rfl⟩ : syracuseStep 54965393 = 41224045) B41224045
theorem B1586331 : Blo 1585491 1586331 := bstep (se 1 (by rfl) ⟨1189748, by rfl⟩ : syracuseStep 1586331 = 2379497) B2379497
theorem B2380955 : Blo 1585491 2380955 := bstep (se 1 (by rfl) ⟨1785716, by rfl⟩ : syracuseStep 2380955 = 3571433) B3571433
theorem B3568823 : Blo 1585491 3568823 := bstep (se 1 (by rfl) ⟨2676617, by rfl⟩ : syracuseStep 3568823 = 5353235) B5353235
theorem B1586427 : Blo 1585491 1586427 := bstep (se 1 (by rfl) ⟨1189820, by rfl⟩ : syracuseStep 1586427 = 2379641) B2379641
theorem B5354747 : Blo 1585491 5354747 := bstep (se 1 (by rfl) ⟨4016060, by rfl⟩ : syracuseStep 5354747 = 8032121) B8032121
theorem B3667207 : Blo 1585491 3667207 := bstep (se 1 (by rfl) ⟨2750405, by rfl⟩ : syracuseStep 3667207 = 5500811) B5500811
theorem B1586495 : Blo 1585491 1586495 := bstep (se 1 (by rfl) ⟨1189871, by rfl⟩ : syracuseStep 1586495 = 2379743) B2379743
theorem B38589857 : Blo 1585491 38589857 := bstep (se 2 (by rfl) ⟨14471196, by rfl⟩ : syracuseStep 38589857 = 28942393) B28942393
theorem B2676199 : Blo 1585491 2676199 := bstep (se 1 (by rfl) ⟨2007149, by rfl⟩ : syracuseStep 2676199 = 4014299) B4014299
theorem B1586663 : Blo 1585491 1586663 := bstep (se 1 (by rfl) ⟨1189997, by rfl⟩ : syracuseStep 1586663 = 2379995) B2379995
theorem B1586671 : Blo 1585491 1586671 := bstep (se 1 (by rfl) ⟨1190003, by rfl⟩ : syracuseStep 1586671 = 2380007) B2380007
theorem B1586779 : Blo 1585491 1586779 := bstep (se 1 (by rfl) ⟨1190084, by rfl⟩ : syracuseStep 1586779 = 2380169) B2380169
theorem B2676361 : Blo 1585491 2676361 := bstep (se 2 (by rfl) ⟨1003635, by rfl⟩ : syracuseStep 2676361 = 2007271) B2007271
theorem B1586843 : Blo 1585491 1586843 := bstep (se 1 (by rfl) ⟨1190132, by rfl⟩ : syracuseStep 1586843 = 2380265) B2380265
theorem B3012319 : Blo 1585491 3012319 := bstep (se 1 (by rfl) ⟨2259239, by rfl⟩ : syracuseStep 3012319 = 4518479) B4518479
theorem B1586927 : Blo 1585491 1586927 := bstep (se 1 (by rfl) ⟨1190195, by rfl⟩ : syracuseStep 1586927 = 2380391) B2380391
theorem B3569399 : Blo 1585491 3569399 := bstep (se 1 (by rfl) ⟨2677049, by rfl⟩ : syracuseStep 3569399 = 5354099) B5354099
theorem B1587015 : Blo 1585491 1587015 := bstep (se 1 (by rfl) ⟨1190261, by rfl⟩ : syracuseStep 1587015 = 2380523) B2380523
theorem B1587035 : Blo 1585491 1587035 := bstep (se 1 (by rfl) ⟨1190276, by rfl⟩ : syracuseStep 1587035 = 2380553) B2380553
theorem B6780779 : Blo 1585491 6780779 := bstep (se 1 (by rfl) ⟨5085584, by rfl⟩ : syracuseStep 6780779 = 10171169) B10171169
theorem B1832863 : Blo 1585491 1832863 := bstep (se 1 (by rfl) ⟨1374647, by rfl⟩ : syracuseStep 1832863 = 2749295) B2749295
theorem B1587103 : Blo 1585491 1587103 := bstep (se 1 (by rfl) ⟨1190327, by rfl⟩ : syracuseStep 1587103 = 2380655) B2380655
theorem B3569579 : Blo 1585491 3569579 := bstep (se 1 (by rfl) ⟨2677184, by rfl⟩ : syracuseStep 3569579 = 5354369) B5354369
theorem B6772729 : Blo 1585491 6772729 := bstep (se 2 (by rfl) ⟨2539773, by rfl⟩ : syracuseStep 6772729 = 5079547) B5079547
theorem B81500197 : Blo 1585491 81500197 := bstep (se 4 (by rfl) ⟨7640643, by rfl⟩ : syracuseStep 81500197 = 15281287) B15281287
theorem B3569705 : Blo 1585491 3569705 := bstep (se 2 (by rfl) ⟨1338639, by rfl⟩ : syracuseStep 3569705 = 2677279) B2677279
theorem B1587271 : Blo 1585491 1587271 := bstep (se 1 (by rfl) ⟨1190453, by rfl⟩ : syracuseStep 1587271 = 2380907) B2380907
theorem B4520119 : Blo 1585491 4520119 := bstep (se 1 (by rfl) ⟨3390089, by rfl⟩ : syracuseStep 4520119 = 6780179) B6780179
theorem B2676955 : Blo 1585491 2676955 := bstep (se 1 (by rfl) ⟨2007716, by rfl⟩ : syracuseStep 2676955 = 4015433) B4015433
theorem B1587431 : Blo 1585491 1587431 := bstep (se 1 (by rfl) ⟨1190573, by rfl⟩ : syracuseStep 1587431 = 2381147) B2381147
theorem B12859651 : Blo 1585491 12859651 := bstep (se 1 (by rfl) ⟨9644738, by rfl⟩ : syracuseStep 12859651 = 19289477) B19289477
theorem B11442475 : Blo 1585491 11442475 := bstep (se 1 (by rfl) ⟨8581856, by rfl⟩ : syracuseStep 11442475 = 17163713) B17163713
theorem B5429587 : Blo 1585491 5429587 := bstep (se 1 (by rfl) ⟨4072190, by rfl⟩ : syracuseStep 5429587 = 8144381) B8144381
theorem B2677151 : Blo 1585491 2677151 := bstep (se 1 (by rfl) ⟨2007863, by rfl⟩ : syracuseStep 2677151 = 4015727) B4015727
theorem B12040649 : Blo 1585491 12040649 := bstep (se 2 (by rfl) ⟨4515243, by rfl⟩ : syracuseStep 12040649 = 9030487) B9030487
theorem B3570119 : Blo 1585491 3570119 := bstep (se 1 (by rfl) ⟨2677589, by rfl⟩ : syracuseStep 3570119 = 5355179) B5355179
theorem B2677225 : Blo 1585491 2677225 := bstep (se 2 (by rfl) ⟨1003959, by rfl⟩ : syracuseStep 2677225 = 2007919) B2007919
theorem B3570281 : Blo 1585491 3570281 := bstep (se 2 (by rfl) ⟨1338855, by rfl⟩ : syracuseStep 3570281 = 2677711) B2677711
theorem B1784479 : Blo 1585491 1784479 := bstep (se 1 (by rfl) ⟨1338359, by rfl⟩ : syracuseStep 1784479 = 2676719) B2676719
theorem B3570335 : Blo 1585491 3570335 := bstep (se 1 (by rfl) ⟨2677751, by rfl⟩ : syracuseStep 3570335 = 5355503) B5355503
theorem B43416323 : Blo 1585491 43416323 := bstep (se 1 (by rfl) ⟨32562242, by rfl⟩ : syracuseStep 43416323 = 65124485) B65124485
theorem B3570479 : Blo 1585491 3570479 := bstep (se 1 (by rfl) ⟨2677859, by rfl⟩ : syracuseStep 3570479 = 5355719) B5355719
theorem B3218287 : Blo 1585491 3218287 := bstep (se 1 (by rfl) ⟨2413715, by rfl⟩ : syracuseStep 3218287 = 4827431) B4827431
theorem B10861523 : Blo 1585491 10861523 := bstep (se 1 (by rfl) ⟨8146142, by rfl⟩ : syracuseStep 10861523 = 16292285) B16292285
theorem B8698861 : Blo 1585491 8698861 := bstep (se 3 (by rfl) ⟨1631036, by rfl⟩ : syracuseStep 8698861 = 3262073) B3262073
theorem B8027261 : Blo 1585491 8027261 := bstep (se 3 (by rfl) ⟨1505111, by rfl⟩ : syracuseStep 8027261 = 3010223) B3010223
theorem B20331719 : Blo 1585491 20331719 := bstep (se 1 (by rfl) ⟨15248789, by rfl⟩ : syracuseStep 20331719 = 30497579) B30497579
theorem B3570911 : Blo 1585491 3570911 := bstep (se 1 (by rfl) ⟨2678183, by rfl⟩ : syracuseStep 3570911 = 5356367) B5356367
theorem B3571127 : Blo 1585491 3571127 := bstep (se 1 (by rfl) ⟨2678345, by rfl⟩ : syracuseStep 3571127 = 5356691) B5356691
theorem B30899645 : Blo 1585491 30899645 := bstep (se 3 (by rfl) ⟨5793683, by rfl⟩ : syracuseStep 30899645 = 11587367) B11587367
theorem B3571307 : Blo 1585491 3571307 := bstep (se 1 (by rfl) ⟨2678480, by rfl⟩ : syracuseStep 3571307 = 5356961) B5356961
theorem B2678393 : Blo 1585491 2678393 := bstep (se 2 (by rfl) ⟨1004397, by rfl⟩ : syracuseStep 2678393 = 2008795) B2008795
theorem B34324235 : Blo 1585491 34324235 := bstep (se 1 (by rfl) ⟨25743176, by rfl⟩ : syracuseStep 34324235 = 51486353) B51486353
theorem B1785631 : Blo 1585491 1785631 := bstep (se 1 (by rfl) ⟨1339223, by rfl⟩ : syracuseStep 1785631 = 2678447) B2678447
theorem B4013945 : Blo 1585491 4013945 := bstep (se 2 (by rfl) ⟨1505229, by rfl⟩ : syracuseStep 4013945 = 3010459) B3010459
theorem B3571577 : Blo 1585491 3571577 := bstep (se 2 (by rfl) ⟨1339341, by rfl⟩ : syracuseStep 3571577 = 2678683) B2678683
theorem B3571667 : Blo 1585491 3571667 := bstep (se 1 (by rfl) ⟨2678750, by rfl⟩ : syracuseStep 3571667 = 5357501) B5357501
theorem B108666929 : Blo 1585491 108666929 := bstep (se 2 (by rfl) ⟨40750098, by rfl⟩ : syracuseStep 108666929 = 81500197) B81500197
theorem B17146201 : Blo 1585491 17146201 := bstep (se 2 (by rfl) ⟨6429825, by rfl⟩ : syracuseStep 17146201 = 12859651) B12859651
theorem B4014431 : Blo 1585491 4014431 := bstep (se 1 (by rfl) ⟨3010823, by rfl⟩ : syracuseStep 4014431 = 6021647) B6021647
theorem B146555243 : Blo 1585491 146555243 := bstep (se 1 (by rfl) ⟨109916432, by rfl⟩ : syracuseStep 146555243 = 219832865) B219832865
theorem B12050855 : Blo 1585491 12050855 := bstep (se 1 (by rfl) ⟨9038141, by rfl⟩ : syracuseStep 12050855 = 18076283) B18076283
theorem B36643595 : Blo 1585491 36643595 := bstep (se 1 (by rfl) ⟨27482696, by rfl⟩ : syracuseStep 36643595 = 54965393) B54965393
theorem B4015271 : Blo 1585491 4015271 := bstep (se 1 (by rfl) ⟨3011453, by rfl⟩ : syracuseStep 4015271 = 6022907) B6022907
theorem B28944215 : Blo 1585491 28944215 := bstep (se 1 (by rfl) ⟨21708161, by rfl⟩ : syracuseStep 28944215 = 43416323) B43416323
theorem B5351507 : Blo 1585491 5351507 := bstep (se 1 (by rfl) ⟨4013630, by rfl⟩ : syracuseStep 5351507 = 8027261) B8027261
theorem B4016425 : Blo 1585491 4016425 := bstep (se 2 (by rfl) ⟨1506159, by rfl⟩ : syracuseStep 4016425 = 3012319) B3012319
theorem B8030663 : Blo 1585491 8030663 := bstep (se 1 (by rfl) ⟨6022997, by rfl⟩ : syracuseStep 8030663 = 12045995) B12045995
theorem B22882823 : Blo 1585491 22882823 := bstep (se 1 (by rfl) ⟨17162117, by rfl⟩ : syracuseStep 22882823 = 34324235) B34324235
theorem B2443817 : Blo 1585491 2443817 := bstep (se 2 (by rfl) ⟨916431, by rfl⟩ : syracuseStep 2443817 = 1832863) B1832863
theorem B9030305 : Blo 1585491 9030305 := bstep (se 2 (by rfl) ⟨3386364, by rfl⟩ : syracuseStep 9030305 = 6772729) B6772729
theorem B2378459 : Blo 1585491 2378459 := bstep (se 1 (by rfl) ⟨1783844, by rfl⟩ : syracuseStep 2378459 = 3567689) B3567689
theorem B12045023 : Blo 1585491 12045023 := bstep (se 1 (by rfl) ⟨9033767, by rfl⟩ : syracuseStep 12045023 = 18067535) B18067535
theorem B2378495 : Blo 1585491 2378495 := bstep (se 1 (by rfl) ⟨1783871, by rfl⟩ : syracuseStep 2378495 = 3567743) B3567743
theorem B14478385 : Blo 1585491 14478385 := bstep (se 2 (by rfl) ⟨5429394, by rfl⟩ : syracuseStep 14478385 = 10858789) B10858789
theorem B15256633 : Blo 1585491 15256633 := bstep (se 2 (by rfl) ⟨5721237, by rfl⟩ : syracuseStep 15256633 = 11442475) B11442475
theorem B4017215 : Blo 1585491 4017215 := bstep (se 1 (by rfl) ⟨3012911, by rfl⟩ : syracuseStep 4017215 = 6025823) B6025823
theorem B4516975 : Blo 1585491 4516975 := bstep (se 1 (by rfl) ⟨3387731, by rfl⟩ : syracuseStep 4516975 = 6775463) B6775463
theorem B30928009 : Blo 1585491 30928009 := bstep (se 2 (by rfl) ⟨11598003, by rfl⟩ : syracuseStep 30928009 = 23196007) B23196007
theorem B9776551 : Blo 1585491 9776551 := bstep (se 1 (by rfl) ⟨7332413, by rfl⟩ : syracuseStep 9776551 = 14664827) B14664827
theorem B2379215 : Blo 1585491 2379215 := bstep (se 1 (by rfl) ⟨1784411, by rfl⟩ : syracuseStep 2379215 = 3568823) B3568823
theorem B2379305 : Blo 1585491 2379305 := bstep (se 2 (by rfl) ⟨892239, by rfl⟩ : syracuseStep 2379305 = 1784479) B1784479
theorem B25726571 : Blo 1585491 25726571 := bstep (se 1 (by rfl) ⟨19294928, by rfl⟩ : syracuseStep 25726571 = 38589857) B38589857
theorem B5353127 : Blo 1585491 5353127 := bstep (se 1 (by rfl) ⟨4014845, by rfl⟩ : syracuseStep 5353127 = 8029691) B8029691
theorem B3010375 : Blo 1585491 3010375 := bstep (se 1 (by rfl) ⟨2257781, by rfl⟩ : syracuseStep 3010375 = 4515563) B4515563
theorem B2379599 : Blo 1585491 2379599 := bstep (se 1 (by rfl) ⟨1784699, by rfl⟩ : syracuseStep 2379599 = 3569399) B3569399
theorem B2379719 : Blo 1585491 2379719 := bstep (se 1 (by rfl) ⟨1784789, by rfl⟩ : syracuseStep 2379719 = 3569579) B3569579
theorem B10162169 : Blo 1585491 10162169 := bstep (se 2 (by rfl) ⟨3810813, by rfl⟩ : syracuseStep 10162169 = 7621627) B7621627
theorem B2379803 : Blo 1585491 2379803 := bstep (se 1 (by rfl) ⟨1784852, by rfl⟩ : syracuseStep 2379803 = 3569705) B3569705
theorem B3567815 : Blo 1585491 3567815 := bstep (se 1 (by rfl) ⟨2675861, by rfl⟩ : syracuseStep 3567815 = 5351723) B5351723
theorem B3813659 : Blo 1585491 3813659 := bstep (se 1 (by rfl) ⟨2860244, by rfl⟩ : syracuseStep 3813659 = 5720489) B5720489
theorem B2380079 : Blo 1585491 2380079 := bstep (se 1 (by rfl) ⟨1785059, by rfl⟩ : syracuseStep 2380079 = 3570119) B3570119
theorem B11432269 : Blo 1585491 11432269 := bstep (se 3 (by rfl) ⟨2143550, by rfl⟩ : syracuseStep 11432269 = 4287101) B4287101
theorem B3567995 : Blo 1585491 3567995 := bstep (se 1 (by rfl) ⟨2675996, by rfl⟩ : syracuseStep 3567995 = 5351993) B5351993
theorem B2380187 : Blo 1585491 2380187 := bstep (se 1 (by rfl) ⟨1785140, by rfl⟩ : syracuseStep 2380187 = 3570281) B3570281
theorem B2380223 : Blo 1585491 2380223 := bstep (se 1 (by rfl) ⟨1785167, by rfl⟩ : syracuseStep 2380223 = 3570335) B3570335
theorem B1585691 : Blo 1585491 1585691 := bstep (se 1 (by rfl) ⟨1189268, by rfl⟩ : syracuseStep 1585691 = 2378537) B2378537
theorem B2380319 : Blo 1585491 2380319 := bstep (se 1 (by rfl) ⟨1785239, by rfl⟩ : syracuseStep 2380319 = 3570479) B3570479
theorem B20329055 : Blo 1585491 20329055 := bstep (se 1 (by rfl) ⟨15246791, by rfl⟩ : syracuseStep 20329055 = 30493583) B30493583
theorem B3568265 : Blo 1585491 3568265 := bstep (se 2 (by rfl) ⟨1338099, by rfl⟩ : syracuseStep 3568265 = 2676199) B2676199
theorem B1585831 : Blo 1585491 1585831 := bstep (se 1 (by rfl) ⟨1189373, by rfl⟩ : syracuseStep 1585831 = 2378747) B2378747
theorem B1585871 : Blo 1585491 1585871 := bstep (se 1 (by rfl) ⟨1189403, by rfl⟩ : syracuseStep 1585871 = 2378807) B2378807
theorem B1585951 : Blo 1585491 1585951 := bstep (se 1 (by rfl) ⟨1189463, by rfl⟩ : syracuseStep 1585951 = 2378927) B2378927
theorem B20321057 : Blo 1585491 20321057 := bstep (se 2 (by rfl) ⟨7620396, by rfl⟩ : syracuseStep 20321057 = 15240793) B15240793
theorem B13554479 : Blo 1585491 13554479 := bstep (se 1 (by rfl) ⟨10165859, by rfl⟩ : syracuseStep 13554479 = 20331719) B20331719
theorem B40678199 : Blo 1585491 40678199 := bstep (se 1 (by rfl) ⟨30508649, by rfl⟩ : syracuseStep 40678199 = 61017299) B61017299
theorem B2380607 : Blo 1585491 2380607 := bstep (se 1 (by rfl) ⟨1785455, by rfl⟩ : syracuseStep 2380607 = 3570911) B3570911
theorem B3568481 : Blo 1585491 3568481 := bstep (se 2 (by rfl) ⟨1338180, by rfl⟩ : syracuseStep 3568481 = 2676361) B2676361
theorem B2380751 : Blo 1585491 2380751 := bstep (se 1 (by rfl) ⟨1785563, by rfl⟩ : syracuseStep 2380751 = 3571127) B3571127
theorem B20599763 : Blo 1585491 20599763 := bstep (se 1 (by rfl) ⟨15449822, by rfl⟩ : syracuseStep 20599763 = 30899645) B30899645
theorem B2380841 : Blo 1585491 2380841 := bstep (se 2 (by rfl) ⟨892815, by rfl⟩ : syracuseStep 2380841 = 1785631) B1785631
theorem B2380871 : Blo 1585491 2380871 := bstep (se 1 (by rfl) ⟨1785653, by rfl⟩ : syracuseStep 2380871 = 3571307) B3571307
theorem B2675963 : Blo 1585491 2675963 := bstep (se 1 (by rfl) ⟨2006972, by rfl⟩ : syracuseStep 2675963 = 4013945) B4013945
theorem B2381051 : Blo 1585491 2381051 := bstep (se 1 (by rfl) ⟨1785788, by rfl⟩ : syracuseStep 2381051 = 3571577) B3571577
theorem B1586431 : Blo 1585491 1586431 := bstep (se 1 (by rfl) ⟨1189823, by rfl⟩ : syracuseStep 1586431 = 2379647) B2379647
theorem B2381111 : Blo 1585491 2381111 := bstep (se 1 (by rfl) ⟨1785833, by rfl⟩ : syracuseStep 2381111 = 3571667) B3571667
theorem B3569003 : Blo 1585491 3569003 := bstep (se 1 (by rfl) ⟨2676752, by rfl⟩ : syracuseStep 3569003 = 5353505) B5353505
theorem B1586559 : Blo 1585491 1586559 := bstep (se 1 (by rfl) ⟨1189919, by rfl⟩ : syracuseStep 1586559 = 2379839) B2379839
theorem B5354963 : Blo 1585491 5354963 := bstep (se 1 (by rfl) ⟨4016222, by rfl⟩ : syracuseStep 5354963 = 8032445) B8032445
theorem B1586715 : Blo 1585491 1586715 := bstep (se 1 (by rfl) ⟨1190036, by rfl⟩ : syracuseStep 1586715 = 2380073) B2380073
theorem B6026825 : Blo 1585491 6026825 := bstep (se 2 (by rfl) ⟨2260059, by rfl⟩ : syracuseStep 6026825 = 4520119) B4520119
theorem B3569255 : Blo 1585491 3569255 := bstep (se 1 (by rfl) ⟨2676941, by rfl⟩ : syracuseStep 3569255 = 5353883) B5353883
theorem B3569273 : Blo 1585491 3569273 := bstep (se 2 (by rfl) ⟨1338477, by rfl⟩ : syracuseStep 3569273 = 2676955) B2676955
theorem B46380683 : Blo 1585491 46380683 := bstep (se 1 (by rfl) ⟨34785512, by rfl⟩ : syracuseStep 46380683 = 69571025) B69571025
theorem B1586895 : Blo 1585491 1586895 := bstep (se 1 (by rfl) ⟨1190171, by rfl⟩ : syracuseStep 1586895 = 2380343) B2380343
theorem B7239449 : Blo 1585491 7239449 := bstep (se 2 (by rfl) ⟨2714793, by rfl⟩ : syracuseStep 7239449 = 5429587) B5429587
theorem B25728839 : Blo 1585491 25728839 := bstep (se 1 (by rfl) ⟨19296629, by rfl⟩ : syracuseStep 25728839 = 38593259) B38593259
theorem B1587135 : Blo 1585491 1587135 := bstep (se 1 (by rfl) ⟨1190351, by rfl⟩ : syracuseStep 1587135 = 2380703) B2380703
theorem B3569633 : Blo 1585491 3569633 := bstep (se 2 (by rfl) ⟨1338612, by rfl⟩ : syracuseStep 3569633 = 2677225) B2677225
theorem B1587263 : Blo 1585491 1587263 := bstep (se 1 (by rfl) ⟨1190447, by rfl⟩ : syracuseStep 1587263 = 2380895) B2380895
theorem B1587303 : Blo 1585491 1587303 := bstep (se 1 (by rfl) ⟨1190477, by rfl⟩ : syracuseStep 1587303 = 2380955) B2380955
theorem B13547645 : Blo 1585491 13547645 := bstep (se 3 (by rfl) ⟨2540183, by rfl⟩ : syracuseStep 13547645 = 5080367) B5080367
theorem B3569831 : Blo 1585491 3569831 := bstep (se 1 (by rfl) ⟨2677373, by rfl⟩ : syracuseStep 3569831 = 5354747) B5354747
theorem B4291049 : Blo 1585491 4291049 := bstep (se 2 (by rfl) ⟨1609143, by rfl⟩ : syracuseStep 4291049 = 3218287) B3218287
theorem B4520519 : Blo 1585491 4520519 := bstep (se 1 (by rfl) ⟨3390389, by rfl⟩ : syracuseStep 4520519 = 6780779) B6780779
theorem B11598481 : Blo 1585491 11598481 := bstep (se 2 (by rfl) ⟨4349430, by rfl⟩ : syracuseStep 11598481 = 8698861) B8698861
theorem B1784767 : Blo 1585491 1784767 := bstep (se 1 (by rfl) ⟨1338575, by rfl⟩ : syracuseStep 1784767 = 2677151) B2677151
theorem B8027099 : Blo 1585491 8027099 := bstep (se 1 (by rfl) ⟨6020324, by rfl⟩ : syracuseStep 8027099 = 12040649) B12040649
theorem B12868571 : Blo 1585491 12868571 := bstep (se 1 (by rfl) ⟨9651428, by rfl⟩ : syracuseStep 12868571 = 19302857) B19302857
theorem B4889609 : Blo 1585491 4889609 := bstep (se 2 (by rfl) ⟨1833603, by rfl⟩ : syracuseStep 4889609 = 3667207) B3667207
theorem B22863035 : Blo 1585491 22863035 := bstep (se 1 (by rfl) ⟨17147276, by rfl⟩ : syracuseStep 22863035 = 34294553) B34294553
theorem B7241015 : Blo 1585491 7241015 := bstep (se 1 (by rfl) ⟨5430761, by rfl⟩ : syracuseStep 7241015 = 10861523) B10861523
theorem B8035847 : Blo 1585491 8035847 := bstep (se 1 (by rfl) ⟨6026885, by rfl⟩ : syracuseStep 8035847 = 12053771) B12053771
theorem B1785595 : Blo 1585491 1785595 := bstep (se 1 (by rfl) ⟨1339196, by rfl⟩ : syracuseStep 1785595 = 2678393) B2678393
theorem B390865013 : Blo 1585491 390865013 := bstep (se 5 (by rfl) ⟨18321797, by rfl⟩ : syracuseStep 390865013 = 36643595) B36643595
theorem B9036319 : Blo 1585491 9036319 := bstep (se 1 (by rfl) ⟨6777239, by rfl⟩ : syracuseStep 9036319 = 13554479) B13554479
theorem B61858565 : Blo 1585491 61858565 := bstep (se 4 (by rfl) ⟨5799240, by rfl⟩ : syracuseStep 61858565 = 11598481) B11598481
theorem B19309373 : Blo 1585491 19309373 := bstep (se 3 (by rfl) ⟨3620507, by rfl⟩ : syracuseStep 19309373 = 7241015) B7241015
theorem B4826299 : Blo 1585491 4826299 := bstep (se 1 (by rfl) ⟨3619724, by rfl⟩ : syracuseStep 4826299 = 7239449) B7239449
theorem B20342177 : Blo 1585491 20342177 := bstep (se 2 (by rfl) ⟨7628316, by rfl⟩ : syracuseStep 20342177 = 15256633) B15256633
theorem B6022633 : Blo 1585491 6022633 := bstep (se 2 (by rfl) ⟨2258487, by rfl⟩ : syracuseStep 6022633 = 4516975) B4516975
theorem B2860699 : Blo 1585491 2860699 := bstep (se 1 (by rfl) ⟨2145524, by rfl⟩ : syracuseStep 2860699 = 4291049) B4291049
theorem B15255215 : Blo 1585491 15255215 := bstep (se 1 (by rfl) ⟨11441411, by rfl⟩ : syracuseStep 15255215 = 22882823) B22882823
theorem B8030015 : Blo 1585491 8030015 := bstep (se 1 (by rfl) ⟨6022511, by rfl⟩ : syracuseStep 8030015 = 12045023) B12045023
theorem B13035401 : Blo 1585491 13035401 := bstep (se 2 (by rfl) ⟨4888275, by rfl⟩ : syracuseStep 13035401 = 9776551) B9776551
theorem B5351399 : Blo 1585491 5351399 := bstep (se 1 (by rfl) ⟨4013549, by rfl⟩ : syracuseStep 5351399 = 8027099) B8027099
theorem B8579047 : Blo 1585491 8579047 := bstep (se 1 (by rfl) ⟨6434285, by rfl⟩ : syracuseStep 8579047 = 12868571) B12868571
theorem B72444619 : Blo 1585491 72444619 := bstep (se 1 (by rfl) ⟨54333464, by rfl⟩ : syracuseStep 72444619 = 108666929) B108666929
theorem B2378543 : Blo 1585491 2378543 := bstep (se 1 (by rfl) ⟨1783907, by rfl⟩ : syracuseStep 2378543 = 3567815) B3567815
theorem B2542439 : Blo 1585491 2542439 := bstep (se 1 (by rfl) ⟨1906829, by rfl⟩ : syracuseStep 2542439 = 3813659) B3813659
theorem B2378663 : Blo 1585491 2378663 := bstep (se 1 (by rfl) ⟨1783997, by rfl⟩ : syracuseStep 2378663 = 3567995) B3567995
theorem B13552703 : Blo 1585491 13552703 := bstep (se 1 (by rfl) ⟨10164527, by rfl⟩ : syracuseStep 13552703 = 20329055) B20329055
theorem B2378843 : Blo 1585491 2378843 := bstep (se 1 (by rfl) ⟨1784132, by rfl⟩ : syracuseStep 2378843 = 3568265) B3568265
theorem B27118799 : Blo 1585491 27118799 := bstep (se 1 (by rfl) ⟨20339099, by rfl⟩ : syracuseStep 27118799 = 40678199) B40678199
theorem B2378987 : Blo 1585491 2378987 := bstep (se 1 (by rfl) ⟨1784240, by rfl⟩ : syracuseStep 2378987 = 3568481) B3568481
theorem B2379335 : Blo 1585491 2379335 := bstep (se 1 (by rfl) ⟨1784501, by rfl⟩ : syracuseStep 2379335 = 3569003) B3569003
theorem B4017883 : Blo 1585491 4017883 := bstep (se 1 (by rfl) ⟨3013412, by rfl⟩ : syracuseStep 4017883 = 6026825) B6026825
theorem B2379503 : Blo 1585491 2379503 := bstep (se 1 (by rfl) ⟨1784627, by rfl⟩ : syracuseStep 2379503 = 3569255) B3569255
theorem B2379515 : Blo 1585491 2379515 := bstep (se 1 (by rfl) ⟨1784636, by rfl⟩ : syracuseStep 2379515 = 3569273) B3569273
theorem B19296143 : Blo 1585491 19296143 := bstep (se 1 (by rfl) ⟨14472107, by rfl⟩ : syracuseStep 19296143 = 28944215) B28944215
theorem B2379689 : Blo 1585491 2379689 := bstep (se 2 (by rfl) ⟨892383, by rfl⟩ : syracuseStep 2379689 = 1784767) B1784767
theorem B2379755 : Blo 1585491 2379755 := bstep (se 1 (by rfl) ⟨1784816, by rfl⟩ : syracuseStep 2379755 = 3569633) B3569633
theorem B3567671 : Blo 1585491 3567671 := bstep (se 1 (by rfl) ⟨2675753, by rfl⟩ : syracuseStep 3567671 = 5351507) B5351507
theorem B19304513 : Blo 1585491 19304513 := bstep (se 2 (by rfl) ⟨7239192, by rfl⟩ : syracuseStep 19304513 = 14478385) B14478385
theorem B9031763 : Blo 1585491 9031763 := bstep (se 1 (by rfl) ⟨6773822, by rfl⟩ : syracuseStep 9031763 = 13547645) B13547645
theorem B6516845 : Blo 1585491 6516845 := bstep (se 3 (by rfl) ⟨1221908, by rfl⟩ : syracuseStep 6516845 = 2443817) B2443817
theorem B2379887 : Blo 1585491 2379887 := bstep (se 1 (by rfl) ⟨1784915, by rfl⟩ : syracuseStep 2379887 = 3569831) B3569831
theorem B5353775 : Blo 1585491 5353775 := bstep (se 1 (by rfl) ⟨4015331, by rfl⟩ : syracuseStep 5353775 = 8030663) B8030663
theorem B1585639 : Blo 1585491 1585639 := bstep (se 1 (by rfl) ⟨1189229, by rfl⟩ : syracuseStep 1585639 = 2378459) B2378459
theorem B1585663 : Blo 1585491 1585663 := bstep (se 1 (by rfl) ⟨1189247, by rfl⟩ : syracuseStep 1585663 = 2378495) B2378495
theorem B15242023 : Blo 1585491 15242023 := bstep (se 1 (by rfl) ⟨11431517, by rfl⟩ : syracuseStep 15242023 = 22863035) B22863035
theorem B1586143 : Blo 1585491 1586143 := bstep (se 1 (by rfl) ⟨1189607, by rfl⟩ : syracuseStep 1586143 = 2379215) B2379215
theorem B2380793 : Blo 1585491 2380793 := bstep (se 2 (by rfl) ⟨892797, by rfl⟩ : syracuseStep 2380793 = 1785595) B1785595
theorem B1586203 : Blo 1585491 1586203 := bstep (se 1 (by rfl) ⟨1189652, by rfl⟩ : syracuseStep 1586203 = 2379305) B2379305
theorem B17151047 : Blo 1585491 17151047 := bstep (se 1 (by rfl) ⟨12863285, by rfl⟩ : syracuseStep 17151047 = 25726571) B25726571
theorem B3568751 : Blo 1585491 3568751 := bstep (se 1 (by rfl) ⟨2676563, by rfl⟩ : syracuseStep 3568751 = 5353127) B5353127
theorem B54932701 : Blo 1585491 54932701 := bstep (se 3 (by rfl) ⟨10299881, by rfl⟩ : syracuseStep 54932701 = 20599763) B20599763
theorem B1586399 : Blo 1585491 1586399 := bstep (se 1 (by rfl) ⟨1189799, by rfl⟩ : syracuseStep 1586399 = 2379599) B2379599
theorem B1586479 : Blo 1585491 1586479 := bstep (se 1 (by rfl) ⟨1189859, by rfl⟩ : syracuseStep 1586479 = 2379719) B2379719
theorem B1586535 : Blo 1585491 1586535 := bstep (se 1 (by rfl) ⟨1189901, by rfl⟩ : syracuseStep 1586535 = 2379803) B2379803
theorem B1586719 : Blo 1585491 1586719 := bstep (se 1 (by rfl) ⟨1190039, by rfl⟩ : syracuseStep 1586719 = 2380079) B2380079
theorem B2676287 : Blo 1585491 2676287 := bstep (se 1 (by rfl) ⟨2007215, by rfl⟩ : syracuseStep 2676287 = 4014431) B4014431
theorem B97703495 : Blo 1585491 97703495 := bstep (se 1 (by rfl) ⟨73277621, by rfl⟩ : syracuseStep 97703495 = 146555243) B146555243
theorem B1586791 : Blo 1585491 1586791 := bstep (se 1 (by rfl) ⟨1190093, by rfl⟩ : syracuseStep 1586791 = 2380187) B2380187
theorem B8033903 : Blo 1585491 8033903 := bstep (se 1 (by rfl) ⟨6025427, by rfl⟩ : syracuseStep 8033903 = 12050855) B12050855
theorem B1586815 : Blo 1585491 1586815 := bstep (se 1 (by rfl) ⟨1190111, by rfl⟩ : syracuseStep 1586815 = 2380223) B2380223
theorem B1586879 : Blo 1585491 1586879 := bstep (se 1 (by rfl) ⟨1190159, by rfl⟩ : syracuseStep 1586879 = 2380319) B2380319
theorem B5355233 : Blo 1585491 5355233 := bstep (se 2 (by rfl) ⟨2008212, by rfl⟩ : syracuseStep 5355233 = 4016425) B4016425
theorem B15243025 : Blo 1585491 15243025 := bstep (se 2 (by rfl) ⟨5716134, by rfl⟩ : syracuseStep 15243025 = 11432269) B11432269
theorem B22861601 : Blo 1585491 22861601 := bstep (se 2 (by rfl) ⟨8573100, by rfl⟩ : syracuseStep 22861601 = 17146201) B17146201
theorem B13547371 : Blo 1585491 13547371 := bstep (se 1 (by rfl) ⟨10160528, by rfl⟩ : syracuseStep 13547371 = 20321057) B20321057
theorem B1587071 : Blo 1585491 1587071 := bstep (se 1 (by rfl) ⟨1190303, by rfl⟩ : syracuseStep 1587071 = 2380607) B2380607
theorem B1587167 : Blo 1585491 1587167 := bstep (se 1 (by rfl) ⟨1190375, by rfl⟩ : syracuseStep 1587167 = 2380751) B2380751
theorem B1587227 : Blo 1585491 1587227 := bstep (se 1 (by rfl) ⟨1190420, by rfl⟩ : syracuseStep 1587227 = 2380841) B2380841
theorem B1587247 : Blo 1585491 1587247 := bstep (se 1 (by rfl) ⟨1190435, by rfl⟩ : syracuseStep 1587247 = 2380871) B2380871
theorem B2676847 : Blo 1585491 2676847 := bstep (se 1 (by rfl) ⟨2007635, by rfl⟩ : syracuseStep 2676847 = 4015271) B4015271
theorem B1783975 : Blo 1585491 1783975 := bstep (se 1 (by rfl) ⟨1337981, by rfl⟩ : syracuseStep 1783975 = 2675963) B2675963
theorem B1587367 : Blo 1585491 1587367 := bstep (se 1 (by rfl) ⟨1190525, by rfl⟩ : syracuseStep 1587367 = 2381051) B2381051
theorem B1587407 : Blo 1585491 1587407 := bstep (se 1 (by rfl) ⟨1190555, by rfl⟩ : syracuseStep 1587407 = 2381111) B2381111
theorem B3569975 : Blo 1585491 3569975 := bstep (se 1 (by rfl) ⟨2677481, by rfl⟩ : syracuseStep 3569975 = 5354963) B5354963
theorem B17152559 : Blo 1585491 17152559 := bstep (se 1 (by rfl) ⟨12864419, by rfl⟩ : syracuseStep 17152559 = 25728839) B25728839
theorem B41237345 : Blo 1585491 41237345 := bstep (se 2 (by rfl) ⟨15464004, by rfl⟩ : syracuseStep 41237345 = 30928009) B30928009
theorem B123681821 : Blo 1585491 123681821 := bstep (se 3 (by rfl) ⟨23190341, by rfl⟩ : syracuseStep 123681821 = 46380683) B46380683
theorem B3013679 : Blo 1585491 3013679 := bstep (se 1 (by rfl) ⟨2260259, by rfl⟩ : syracuseStep 3013679 = 4520519) B4520519
theorem B6020203 : Blo 1585491 6020203 := bstep (se 1 (by rfl) ⟨4515152, by rfl⟩ : syracuseStep 6020203 = 9030305) B9030305
theorem B3259739 : Blo 1585491 3259739 := bstep (se 1 (by rfl) ⟨2444804, by rfl⟩ : syracuseStep 3259739 = 4889609) B4889609
theorem B2678143 : Blo 1585491 2678143 := bstep (se 1 (by rfl) ⟨2008607, by rfl⟩ : syracuseStep 2678143 = 4017215) B4017215
theorem B5357231 : Blo 1585491 5357231 := bstep (se 1 (by rfl) ⟨4017923, by rfl⟩ : syracuseStep 5357231 = 8035847) B8035847
theorem B4013833 : Blo 1585491 4013833 := bstep (se 2 (by rfl) ⟨1505187, by rfl⟩ : syracuseStep 4013833 = 3010375) B3010375
theorem B6774779 : Blo 1585491 6774779 := bstep (se 1 (by rfl) ⟨5081084, by rfl⟩ : syracuseStep 6774779 = 10162169) B10162169
theorem B12869675 : Blo 1585491 12869675 := bstep (se 1 (by rfl) ⟨9652256, by rfl⟩ : syracuseStep 12869675 = 19304513) B19304513
theorem B6021175 : Blo 1585491 6021175 := bstep (se 1 (by rfl) ⟨4515881, by rfl⟩ : syracuseStep 6021175 = 9031763) B9031763
theorem B329818189 : Blo 1585491 329818189 := bstep (se 3 (by rfl) ⟨61840910, by rfl⟩ : syracuseStep 329818189 = 123681821) B123681821
theorem B41239043 : Blo 1585491 41239043 := bstep (se 1 (by rfl) ⟨30929282, by rfl⟩ : syracuseStep 41239043 = 61858565) B61858565
theorem B96592825 : Blo 1585491 96592825 := bstep (se 2 (by rfl) ⟨36222309, by rfl⟩ : syracuseStep 96592825 = 72444619) B72444619
theorem B65135663 : Blo 1585491 65135663 := bstep (se 1 (by rfl) ⟨48851747, by rfl⟩ : syracuseStep 65135663 = 97703495) B97703495
theorem B8030177 : Blo 1585491 8030177 := bstep (se 2 (by rfl) ⟨3011316, by rfl⟩ : syracuseStep 8030177 = 6022633) B6022633
theorem B2009119 : Blo 1585491 2009119 := bstep (se 1 (by rfl) ⟨1506839, by rfl⟩ : syracuseStep 2009119 = 3013679) B3013679
theorem B2173159 : Blo 1585491 2173159 := bstep (se 1 (by rfl) ⟨1629869, by rfl⟩ : syracuseStep 2173159 = 3259739) B3259739
theorem B5351777 : Blo 1585491 5351777 := bstep (se 2 (by rfl) ⟨2006916, by rfl⟩ : syracuseStep 5351777 = 4013833) B4013833
theorem B12864095 : Blo 1585491 12864095 := bstep (se 1 (by rfl) ⟨9648071, by rfl⟩ : syracuseStep 12864095 = 19296143) B19296143
theorem B11438729 : Blo 1585491 11438729 := bstep (se 2 (by rfl) ⟨4289523, by rfl⟩ : syracuseStep 11438729 = 8579047) B8579047
theorem B18066077 : Blo 1585491 18066077 := bstep (se 3 (by rfl) ⟨3387389, by rfl⟩ : syracuseStep 18066077 = 6774779) B6774779
theorem B2378447 : Blo 1585491 2378447 := bstep (se 1 (by rfl) ⟨1783835, by rfl⟩ : syracuseStep 2378447 = 3567671) B3567671
theorem B4344563 : Blo 1585491 4344563 := bstep (se 1 (by rfl) ⟨3258422, by rfl⟩ : syracuseStep 4344563 = 6516845) B6516845
theorem B2378633 : Blo 1585491 2378633 := bstep (se 2 (by rfl) ⟨891987, by rfl⟩ : syracuseStep 2378633 = 1783975) B1783975
theorem B12872915 : Blo 1585491 12872915 := bstep (se 1 (by rfl) ⟨9654686, by rfl⟩ : syracuseStep 12872915 = 19309373) B19309373
theorem B2379167 : Blo 1585491 2379167 := bstep (se 1 (by rfl) ⟨1784375, by rfl⟩ : syracuseStep 2379167 = 3568751) B3568751
theorem B13561451 : Blo 1585491 13561451 := bstep (se 1 (by rfl) ⟨10171088, by rfl⟩ : syracuseStep 13561451 = 20342177) B20342177
theorem B10170143 : Blo 1585491 10170143 := bstep (se 1 (by rfl) ⟨7627607, by rfl⟩ : syracuseStep 10170143 = 15255215) B15255215
theorem B15241067 : Blo 1585491 15241067 := bstep (se 1 (by rfl) ⟨11430800, by rfl⟩ : syracuseStep 15241067 = 22861601) B22861601
theorem B5353343 : Blo 1585491 5353343 := bstep (se 1 (by rfl) ⟨4015007, by rfl⟩ : syracuseStep 5353343 = 8030015) B8030015
theorem B3567599 : Blo 1585491 3567599 := bstep (se 1 (by rfl) ⟨2675699, by rfl⟩ : syracuseStep 3567599 = 5351399) B5351399
theorem B2379983 : Blo 1585491 2379983 := bstep (se 1 (by rfl) ⟨1784987, by rfl⟩ : syracuseStep 2379983 = 3569975) B3569975
theorem B6435065 : Blo 1585491 6435065 := bstep (se 2 (by rfl) ⟨2413149, by rfl⟩ : syracuseStep 6435065 = 4826299) B4826299
theorem B1585695 : Blo 1585491 1585695 := bstep (se 1 (by rfl) ⟨1189271, by rfl⟩ : syracuseStep 1585695 = 2378543) B2378543
theorem B1585775 : Blo 1585491 1585775 := bstep (se 1 (by rfl) ⟨1189331, by rfl⟩ : syracuseStep 1585775 = 2378663) B2378663
theorem B1585895 : Blo 1585491 1585895 := bstep (se 1 (by rfl) ⟨1189421, by rfl⟩ : syracuseStep 1585895 = 2378843) B2378843
theorem B1585991 : Blo 1585491 1585991 := bstep (se 1 (by rfl) ⟨1189493, by rfl⟩ : syracuseStep 1585991 = 2378987) B2378987
theorem B3814265 : Blo 1585491 3814265 := bstep (se 2 (by rfl) ⟨1430349, by rfl⟩ : syracuseStep 3814265 = 2860699) B2860699
theorem B6779837 : Blo 1585491 6779837 := bstep (se 3 (by rfl) ⟨1271219, by rfl⟩ : syracuseStep 6779837 = 2542439) B2542439
theorem B1586223 : Blo 1585491 1586223 := bstep (se 1 (by rfl) ⟨1189667, by rfl⟩ : syracuseStep 1586223 = 2379335) B2379335
theorem B1586335 : Blo 1585491 1586335 := bstep (se 1 (by rfl) ⟨1189751, by rfl⟩ : syracuseStep 1586335 = 2379503) B2379503
theorem B1586343 : Blo 1585491 1586343 := bstep (se 1 (by rfl) ⟨1189757, by rfl⟩ : syracuseStep 1586343 = 2379515) B2379515
theorem B1586459 : Blo 1585491 1586459 := bstep (se 1 (by rfl) ⟨1189844, by rfl⟩ : syracuseStep 1586459 = 2379689) B2379689
theorem B1586503 : Blo 1585491 1586503 := bstep (se 1 (by rfl) ⟨1189877, by rfl⟩ : syracuseStep 1586503 = 2379755) B2379755
theorem B1586591 : Blo 1585491 1586591 := bstep (se 1 (by rfl) ⟨1189943, by rfl⟩ : syracuseStep 1586591 = 2379887) B2379887
theorem B260576675 : Blo 1585491 260576675 := bstep (se 1 (by rfl) ⟨195432506, by rfl⟩ : syracuseStep 260576675 = 390865013) B390865013
theorem B3569129 : Blo 1585491 3569129 := bstep (se 2 (by rfl) ⟨1338423, by rfl⟩ : syracuseStep 3569129 = 2676847) B2676847
theorem B3569183 : Blo 1585491 3569183 := bstep (se 1 (by rfl) ⟨2676887, by rfl⟩ : syracuseStep 3569183 = 5353775) B5353775
theorem B1587195 : Blo 1585491 1587195 := bstep (se 1 (by rfl) ⟨1190396, by rfl⟩ : syracuseStep 1587195 = 2380793) B2380793
theorem B12048425 : Blo 1585491 12048425 := bstep (se 2 (by rfl) ⟨4518159, by rfl⟩ : syracuseStep 12048425 = 9036319) B9036319
theorem B11434031 : Blo 1585491 11434031 := bstep (se 1 (by rfl) ⟨8575523, by rfl⟩ : syracuseStep 11434031 = 17151047) B17151047
theorem B1784191 : Blo 1585491 1784191 := bstep (se 1 (by rfl) ⟨1338143, by rfl⟩ : syracuseStep 1784191 = 2676287) B2676287
theorem B20322697 : Blo 1585491 20322697 := bstep (se 2 (by rfl) ⟨7621011, by rfl⟩ : syracuseStep 20322697 = 15242023) B15242023
theorem B5355935 : Blo 1585491 5355935 := bstep (se 1 (by rfl) ⟨4016951, by rfl⟩ : syracuseStep 5355935 = 8033903) B8033903
theorem B3570155 : Blo 1585491 3570155 := bstep (se 1 (by rfl) ⟨2677616, by rfl⟩ : syracuseStep 3570155 = 5355233) B5355233
theorem B8690267 : Blo 1585491 8690267 := bstep (se 1 (by rfl) ⟨6517700, by rfl⟩ : syracuseStep 8690267 = 13035401) B13035401
theorem B8026937 : Blo 1585491 8026937 := bstep (se 2 (by rfl) ⟨3010101, by rfl⟩ : syracuseStep 8026937 = 6020203) B6020203
theorem B73243601 : Blo 1585491 73243601 := bstep (se 2 (by rfl) ⟨27466350, by rfl⟩ : syracuseStep 73243601 = 54932701) B54932701
theorem B11435039 : Blo 1585491 11435039 := bstep (se 1 (by rfl) ⟨8576279, by rfl⟩ : syracuseStep 11435039 = 17152559) B17152559
theorem B3570857 : Blo 1585491 3570857 := bstep (se 2 (by rfl) ⟨1339071, by rfl⟩ : syracuseStep 3570857 = 2678143) B2678143
theorem B27491563 : Blo 1585491 27491563 := bstep (se 1 (by rfl) ⟨20618672, by rfl⟩ : syracuseStep 27491563 = 41237345) B41237345
theorem B9035135 : Blo 1585491 9035135 := bstep (se 1 (by rfl) ⟨6776351, by rfl⟩ : syracuseStep 9035135 = 13552703) B13552703
theorem B18079199 : Blo 1585491 18079199 := bstep (se 1 (by rfl) ⟨13559399, by rfl⟩ : syracuseStep 18079199 = 27118799) B27118799
theorem B5357177 : Blo 1585491 5357177 := bstep (se 2 (by rfl) ⟨2008941, by rfl⟩ : syracuseStep 5357177 = 4017883) B4017883
theorem B20324033 : Blo 1585491 20324033 := bstep (se 2 (by rfl) ⟨7621512, by rfl⟩ : syracuseStep 20324033 = 15243025) B15243025
theorem B3571487 : Blo 1585491 3571487 := bstep (se 1 (by rfl) ⟨2678615, by rfl⟩ : syracuseStep 3571487 = 5357231) B5357231
theorem B18063161 : Blo 1585491 18063161 := bstep (se 2 (by rfl) ⟨6773685, by rfl⟩ : syracuseStep 18063161 = 13547371) B13547371
theorem B2678825 : Blo 1585491 2678825 := bstep (se 2 (by rfl) ⟨1004559, by rfl⟩ : syracuseStep 2678825 = 2009119) B2009119
theorem B8028233 : Blo 1585491 8028233 := bstep (se 2 (by rfl) ⟨3010587, by rfl⟩ : syracuseStep 8028233 = 6021175) B6021175
theorem B27492695 : Blo 1585491 27492695 := bstep (se 1 (by rfl) ⟨20619521, by rfl⟩ : syracuseStep 27492695 = 41239043) B41239043
theorem B12044051 : Blo 1585491 12044051 := bstep (se 1 (by rfl) ⟨9033038, by rfl⟩ : syracuseStep 12044051 = 18066077) B18066077
theorem B5351291 : Blo 1585491 5351291 := bstep (se 1 (by rfl) ⟨4013468, by rfl⟩ : syracuseStep 5351291 = 8026937) B8026937
theorem B11585501 : Blo 1585491 11585501 := bstep (se 3 (by rfl) ⟨2172281, by rfl⟩ : syracuseStep 11585501 = 4344563) B4344563
theorem B6023423 : Blo 1585491 6023423 := bstep (se 1 (by rfl) ⟨4517567, by rfl⟩ : syracuseStep 6023423 = 9035135) B9035135
theorem B12052799 : Blo 1585491 12052799 := bstep (se 1 (by rfl) ⟨9039599, by rfl⟩ : syracuseStep 12052799 = 18079199) B18079199
theorem B10160711 : Blo 1585491 10160711 := bstep (se 1 (by rfl) ⟨7620533, by rfl⟩ : syracuseStep 10160711 = 15241067) B15241067
theorem B2378399 : Blo 1585491 2378399 := bstep (se 1 (by rfl) ⟨1783799, by rfl⟩ : syracuseStep 2378399 = 3567599) B3567599
theorem B8579783 : Blo 1585491 8579783 := bstep (se 1 (by rfl) ⟨6434837, by rfl⟩ : syracuseStep 8579783 = 12869675) B12869675
theorem B439757585 : Blo 1585491 439757585 := bstep (se 2 (by rfl) ⟨164909094, by rfl⟩ : syracuseStep 439757585 = 329818189) B329818189
theorem B2378921 : Blo 1585491 2378921 := bstep (se 2 (by rfl) ⟨892095, by rfl⟩ : syracuseStep 2378921 = 1784191) B1784191
theorem B2542843 : Blo 1585491 2542843 := bstep (se 1 (by rfl) ⟨1907132, by rfl⟩ : syracuseStep 2542843 = 3814265) B3814265
theorem B2379419 : Blo 1585491 2379419 := bstep (se 1 (by rfl) ⟨1784564, by rfl⟩ : syracuseStep 2379419 = 3569129) B3569129
theorem B2379455 : Blo 1585491 2379455 := bstep (se 1 (by rfl) ⟨1784591, by rfl⟩ : syracuseStep 2379455 = 3569183) B3569183
theorem B128790433 : Blo 1585491 128790433 := bstep (se 2 (by rfl) ⟨48296412, by rfl⟩ : syracuseStep 128790433 = 96592825) B96592825
theorem B5353451 : Blo 1585491 5353451 := bstep (se 1 (by rfl) ⟨4015088, by rfl⟩ : syracuseStep 5353451 = 8030177) B8030177
theorem B8032283 : Blo 1585491 8032283 := bstep (se 1 (by rfl) ⟨6024212, by rfl⟩ : syracuseStep 8032283 = 12048425) B12048425
theorem B7622687 : Blo 1585491 7622687 := bstep (se 1 (by rfl) ⟨5717015, by rfl⟩ : syracuseStep 7622687 = 11434031) B11434031
theorem B3567851 : Blo 1585491 3567851 := bstep (se 1 (by rfl) ⟨2675888, by rfl⟩ : syracuseStep 3567851 = 5351777) B5351777
theorem B36655417 : Blo 1585491 36655417 := bstep (se 2 (by rfl) ⟨13745781, by rfl⟩ : syracuseStep 36655417 = 27491563) B27491563
theorem B2380103 : Blo 1585491 2380103 := bstep (se 1 (by rfl) ⟨1785077, by rfl⟩ : syracuseStep 2380103 = 3570155) B3570155
theorem B1585631 : Blo 1585491 1585631 := bstep (se 1 (by rfl) ⟨1189223, by rfl⟩ : syracuseStep 1585631 = 2378447) B2378447
theorem B1585755 : Blo 1585491 1585755 := bstep (se 1 (by rfl) ⟨1189316, by rfl⟩ : syracuseStep 1585755 = 2378633) B2378633
theorem B48829067 : Blo 1585491 48829067 := bstep (se 1 (by rfl) ⟨36621800, by rfl⟩ : syracuseStep 48829067 = 73243601) B73243601
theorem B7623359 : Blo 1585491 7623359 := bstep (se 1 (by rfl) ⟨5717519, by rfl⟩ : syracuseStep 7623359 = 11435039) B11435039
theorem B2380571 : Blo 1585491 2380571 := bstep (se 1 (by rfl) ⟨1785428, by rfl⟩ : syracuseStep 2380571 = 3570857) B3570857
theorem B8581943 : Blo 1585491 8581943 := bstep (se 1 (by rfl) ⟨6436457, by rfl⟩ : syracuseStep 8581943 = 12872915) B12872915
theorem B1586111 : Blo 1585491 1586111 := bstep (se 1 (by rfl) ⟨1189583, by rfl⟩ : syracuseStep 1586111 = 2379167) B2379167
theorem B9040967 : Blo 1585491 9040967 := bstep (se 1 (by rfl) ⟨6780725, by rfl⟩ : syracuseStep 9040967 = 13561451) B13561451
theorem B6780095 : Blo 1585491 6780095 := bstep (se 1 (by rfl) ⟨5085071, by rfl⟩ : syracuseStep 6780095 = 10170143) B10170143
theorem B2380991 : Blo 1585491 2380991 := bstep (se 1 (by rfl) ⟨1785743, by rfl⟩ : syracuseStep 2380991 = 3571487) B3571487
theorem B3568895 : Blo 1585491 3568895 := bstep (se 1 (by rfl) ⟨2676671, by rfl⟩ : syracuseStep 3568895 = 5353343) B5353343
theorem B1586655 : Blo 1585491 1586655 := bstep (se 1 (by rfl) ⟨1189991, by rfl⟩ : syracuseStep 1586655 = 2379983) B2379983
theorem B2897545 : Blo 1585491 2897545 := bstep (se 2 (by rfl) ⟨1086579, by rfl⟩ : syracuseStep 2897545 = 2173159) B2173159
theorem B27096929 : Blo 1585491 27096929 := bstep (se 2 (by rfl) ⟨10161348, by rfl⟩ : syracuseStep 27096929 = 20322697) B20322697
theorem B4519891 : Blo 1585491 4519891 := bstep (se 1 (by rfl) ⟨3389918, by rfl⟩ : syracuseStep 4519891 = 6779837) B6779837
theorem B17160173 : Blo 1585491 17160173 := bstep (se 3 (by rfl) ⟨3217532, by rfl⟩ : syracuseStep 17160173 = 6435065) B6435065
theorem B43423775 : Blo 1585491 43423775 := bstep (se 1 (by rfl) ⟨32567831, by rfl⟩ : syracuseStep 43423775 = 65135663) B65135663
theorem B173717783 : Blo 1585491 173717783 := bstep (se 1 (by rfl) ⟨130288337, by rfl⟩ : syracuseStep 173717783 = 260576675) B260576675
theorem B23174045 : Blo 1585491 23174045 := bstep (se 3 (by rfl) ⟨4345133, by rfl⟩ : syracuseStep 23174045 = 8690267) B8690267
theorem B3570623 : Blo 1585491 3570623 := bstep (se 1 (by rfl) ⟨2677967, by rfl⟩ : syracuseStep 3570623 = 5355935) B5355935
theorem B8576063 : Blo 1585491 8576063 := bstep (se 1 (by rfl) ⟨6432047, by rfl⟩ : syracuseStep 8576063 = 12864095) B12864095
theorem B7625819 : Blo 1585491 7625819 := bstep (se 1 (by rfl) ⟨5719364, by rfl⟩ : syracuseStep 7625819 = 11438729) B11438729
theorem B3571451 : Blo 1585491 3571451 := bstep (se 1 (by rfl) ⟨2678588, by rfl⟩ : syracuseStep 3571451 = 5357177) B5357177
theorem B13549355 : Blo 1585491 13549355 := bstep (se 1 (by rfl) ⟨10162016, by rfl⟩ : syracuseStep 13549355 = 20324033) B20324033
theorem B12042107 : Blo 1585491 12042107 := bstep (se 1 (by rfl) ⟨9031580, by rfl⟩ : syracuseStep 12042107 = 18063161) B18063161
theorem B1785883 : Blo 1585491 1785883 := bstep (se 1 (by rfl) ⟨1339412, by rfl⟩ : syracuseStep 1785883 = 2678825) B2678825
theorem B48873889 : Blo 1585491 48873889 := bstep (se 2 (by rfl) ⟨18327708, by rfl⟩ : syracuseStep 48873889 = 36655417) B36655417
theorem B8029367 : Blo 1585491 8029367 := bstep (se 1 (by rfl) ⟨6022025, by rfl⟩ : syracuseStep 8029367 = 12044051) B12044051
theorem B18064619 : Blo 1585491 18064619 := bstep (se 1 (by rfl) ⟨13548464, by rfl⟩ : syracuseStep 18064619 = 27096929) B27096929
theorem B4015615 : Blo 1585491 4015615 := bstep (se 1 (by rfl) ⟨3011711, by rfl⟩ : syracuseStep 4015615 = 6023423) B6023423
theorem B115811855 : Blo 1585491 115811855 := bstep (se 1 (by rfl) ⟨86858891, by rfl⟩ : syracuseStep 115811855 = 173717783) B173717783
theorem B5719855 : Blo 1585491 5719855 := bstep (se 1 (by rfl) ⟨4289891, by rfl⟩ : syracuseStep 5719855 = 8579783) B8579783
theorem B5081791 : Blo 1585491 5081791 := bstep (se 1 (by rfl) ⟨3811343, by rfl⟩ : syracuseStep 5081791 = 7622687) B7622687
theorem B5352155 : Blo 1585491 5352155 := bstep (se 1 (by rfl) ⟨4014116, by rfl⟩ : syracuseStep 5352155 = 8028233) B8028233
theorem B2378567 : Blo 1585491 2378567 := bstep (se 1 (by rfl) ⟨1783925, by rfl⟩ : syracuseStep 2378567 = 3567851) B3567851
theorem B18328463 : Blo 1585491 18328463 := bstep (se 1 (by rfl) ⟨13746347, by rfl⟩ : syracuseStep 18328463 = 27492695) B27492695
theorem B5082239 : Blo 1585491 5082239 := bstep (se 1 (by rfl) ⟨3811679, by rfl⟩ : syracuseStep 5082239 = 7623359) B7623359
theorem B5721295 : Blo 1585491 5721295 := bstep (se 1 (by rfl) ⟨4290971, by rfl⟩ : syracuseStep 5721295 = 8581943) B8581943
theorem B2379263 : Blo 1585491 2379263 := bstep (se 1 (by rfl) ⟨1784447, by rfl⟩ : syracuseStep 2379263 = 3568895) B3568895
theorem B3567527 : Blo 1585491 3567527 := bstep (se 1 (by rfl) ⟨2675645, by rfl⟩ : syracuseStep 3567527 = 5351291) B5351291
theorem B13561829 : Blo 1585491 13561829 := bstep (se 4 (by rfl) ⟨1271421, by rfl⟩ : syracuseStep 13561829 = 2542843) B2542843
theorem B11440115 : Blo 1585491 11440115 := bstep (se 1 (by rfl) ⟨8580086, by rfl⟩ : syracuseStep 11440115 = 17160173) B17160173
theorem B1585599 : Blo 1585491 1585599 := bstep (se 1 (by rfl) ⟨1189199, by rfl⟩ : syracuseStep 1585599 = 2378399) B2378399
theorem B293171723 : Blo 1585491 293171723 := bstep (se 1 (by rfl) ⟨219878792, by rfl⟩ : syracuseStep 293171723 = 439757585) B439757585
theorem B2380415 : Blo 1585491 2380415 := bstep (se 1 (by rfl) ⟨1785311, by rfl⟩ : syracuseStep 2380415 = 3570623) B3570623
theorem B5083879 : Blo 1585491 5083879 := bstep (se 1 (by rfl) ⟨3812909, by rfl⟩ : syracuseStep 5083879 = 7625819) B7625819
theorem B1585947 : Blo 1585491 1585947 := bstep (se 1 (by rfl) ⟨1189460, by rfl⟩ : syracuseStep 1585947 = 2378921) B2378921
theorem B3863393 : Blo 1585491 3863393 := bstep (se 2 (by rfl) ⟨1448772, by rfl⟩ : syracuseStep 3863393 = 2897545) B2897545
theorem B1586279 : Blo 1585491 1586279 := bstep (se 1 (by rfl) ⟨1189709, by rfl⟩ : syracuseStep 1586279 = 2379419) B2379419
theorem B1586303 : Blo 1585491 1586303 := bstep (se 1 (by rfl) ⟨1189727, by rfl⟩ : syracuseStep 1586303 = 2379455) B2379455
theorem B2380967 : Blo 1585491 2380967 := bstep (se 1 (by rfl) ⟨1785725, by rfl⟩ : syracuseStep 2380967 = 3571451) B3571451
theorem B9032903 : Blo 1585491 9032903 := bstep (se 1 (by rfl) ⟨6774677, by rfl⟩ : syracuseStep 9032903 = 13549355) B13549355
theorem B6026521 : Blo 1585491 6026521 := bstep (se 2 (by rfl) ⟨2259945, by rfl⟩ : syracuseStep 6026521 = 4519891) B4519891
theorem B3568967 : Blo 1585491 3568967 := bstep (se 1 (by rfl) ⟨2676725, by rfl⟩ : syracuseStep 3568967 = 5353451) B5353451
theorem B5354855 : Blo 1585491 5354855 := bstep (se 1 (by rfl) ⟨4016141, by rfl⟩ : syracuseStep 5354855 = 8032283) B8032283
theorem B1586735 : Blo 1585491 1586735 := bstep (se 1 (by rfl) ⟨1190051, by rfl⟩ : syracuseStep 1586735 = 2380103) B2380103
theorem B32552711 : Blo 1585491 32552711 := bstep (se 1 (by rfl) ⟨24414533, by rfl⟩ : syracuseStep 32552711 = 48829067) B48829067
theorem B1587047 : Blo 1585491 1587047 := bstep (se 1 (by rfl) ⟨1190285, by rfl⟩ : syracuseStep 1587047 = 2380571) B2380571
theorem B6027311 : Blo 1585491 6027311 := bstep (se 1 (by rfl) ⟨4520483, by rfl⟩ : syracuseStep 6027311 = 9040967) B9040967
theorem B4520063 : Blo 1585491 4520063 := bstep (se 1 (by rfl) ⟨3390047, by rfl⟩ : syracuseStep 4520063 = 6780095) B6780095
theorem B1587327 : Blo 1585491 1587327 := bstep (se 1 (by rfl) ⟨1190495, by rfl⟩ : syracuseStep 1587327 = 2380991) B2380991
theorem B7723667 : Blo 1585491 7723667 := bstep (se 1 (by rfl) ⟨5792750, by rfl⟩ : syracuseStep 7723667 = 11585501) B11585501
theorem B28949183 : Blo 1585491 28949183 := bstep (se 1 (by rfl) ⟨21711887, by rfl⟩ : syracuseStep 28949183 = 43423775) B43423775
theorem B8035199 : Blo 1585491 8035199 := bstep (se 1 (by rfl) ⟨6026399, by rfl⟩ : syracuseStep 8035199 = 12052799) B12052799
theorem B6773807 : Blo 1585491 6773807 := bstep (se 1 (by rfl) ⟨5080355, by rfl⟩ : syracuseStep 6773807 = 10160711) B10160711
theorem B15449363 : Blo 1585491 15449363 := bstep (se 1 (by rfl) ⟨11587022, by rfl⟩ : syracuseStep 15449363 = 23174045) B23174045
theorem B5717375 : Blo 1585491 5717375 := bstep (se 1 (by rfl) ⟨4288031, by rfl⟩ : syracuseStep 5717375 = 8576063) B8576063
theorem B171720577 : Blo 1585491 171720577 := bstep (se 2 (by rfl) ⟨64395216, by rfl⟩ : syracuseStep 171720577 = 128790433) B128790433
theorem B8028071 : Blo 1585491 8028071 := bstep (se 1 (by rfl) ⟨6021053, by rfl⟩ : syracuseStep 8028071 = 12042107) B12042107
theorem B7626743 : Blo 1585491 7626743 := bstep (se 1 (by rfl) ⟨5720057, by rfl⟩ : syracuseStep 7626743 = 11440115) B11440115
theorem B6021935 : Blo 1585491 6021935 := bstep (se 1 (by rfl) ⟨4516451, by rfl⟩ : syracuseStep 6021935 = 9032903) B9032903
theorem B12043079 : Blo 1585491 12043079 := bstep (se 1 (by rfl) ⟨9032309, by rfl⟩ : syracuseStep 12043079 = 18064619) B18064619
theorem B6775721 : Blo 1585491 6775721 := bstep (se 2 (by rfl) ⟨2540895, by rfl⟩ : syracuseStep 6775721 = 5081791) B5081791
theorem B21701807 : Blo 1585491 21701807 := bstep (se 1 (by rfl) ⟨16276355, by rfl⟩ : syracuseStep 21701807 = 32552711) B32552711
theorem B7628393 : Blo 1585491 7628393 := bstep (se 2 (by rfl) ⟨2860647, by rfl⟩ : syracuseStep 7628393 = 5721295) B5721295
theorem B4515871 : Blo 1585491 4515871 := bstep (se 1 (by rfl) ⟨3386903, by rfl⟩ : syracuseStep 4515871 = 6773807) B6773807
theorem B10299575 : Blo 1585491 10299575 := bstep (se 1 (by rfl) ⟨7724681, by rfl⟩ : syracuseStep 10299575 = 15449363) B15449363
theorem B3811583 : Blo 1585491 3811583 := bstep (se 1 (by rfl) ⟨2858687, by rfl⟩ : syracuseStep 3811583 = 5717375) B5717375
theorem B228960769 : Blo 1585491 228960769 := bstep (se 2 (by rfl) ⟨85860288, by rfl⟩ : syracuseStep 228960769 = 171720577) B171720577
theorem B2378351 : Blo 1585491 2378351 := bstep (se 1 (by rfl) ⟨1783763, by rfl⟩ : syracuseStep 2378351 = 3567527) B3567527
theorem B5352047 : Blo 1585491 5352047 := bstep (se 1 (by rfl) ⟨4014035, by rfl⟩ : syracuseStep 5352047 = 8028071) B8028071
theorem B195447815 : Blo 1585491 195447815 := bstep (se 1 (by rfl) ⟨146585861, by rfl⟩ : syracuseStep 195447815 = 293171723) B293171723
theorem B2575595 : Blo 1585491 2575595 := bstep (se 1 (by rfl) ⟨1931696, by rfl⟩ : syracuseStep 2575595 = 3863393) B3863393
theorem B5352911 : Blo 1585491 5352911 := bstep (se 1 (by rfl) ⟨4014683, by rfl⟩ : syracuseStep 5352911 = 8029367) B8029367
theorem B2379311 : Blo 1585491 2379311 := bstep (se 1 (by rfl) ⟨1784483, by rfl⟩ : syracuseStep 2379311 = 3568967) B3568967
theorem B6778505 : Blo 1585491 6778505 := bstep (se 2 (by rfl) ⟨2541939, by rfl⟩ : syracuseStep 6778505 = 5083879) B5083879
theorem B4018207 : Blo 1585491 4018207 := bstep (se 1 (by rfl) ⟨3013655, by rfl⟩ : syracuseStep 4018207 = 6027311) B6027311
theorem B5149111 : Blo 1585491 5149111 := bstep (se 1 (by rfl) ⟨3861833, by rfl⟩ : syracuseStep 5149111 = 7723667) B7723667
theorem B3568103 : Blo 1585491 3568103 := bstep (se 1 (by rfl) ⟨2676077, by rfl⟩ : syracuseStep 3568103 = 5352155) B5352155
theorem B1585711 : Blo 1585491 1585711 := bstep (se 1 (by rfl) ⟨1189283, by rfl⟩ : syracuseStep 1585711 = 2378567) B2378567
theorem B12218975 : Blo 1585491 12218975 := bstep (se 1 (by rfl) ⟨9164231, by rfl⟩ : syracuseStep 12218975 = 18328463) B18328463
theorem B5354153 : Blo 1585491 5354153 := bstep (se 2 (by rfl) ⟨2007807, by rfl⟩ : syracuseStep 5354153 = 4015615) B4015615
theorem B3388159 : Blo 1585491 3388159 := bstep (se 1 (by rfl) ⟨2541119, by rfl⟩ : syracuseStep 3388159 = 5082239) B5082239
theorem B1586175 : Blo 1585491 1586175 := bstep (se 1 (by rfl) ⟨1189631, by rfl⟩ : syracuseStep 1586175 = 2379263) B2379263
theorem B9041219 : Blo 1585491 9041219 := bstep (se 1 (by rfl) ⟨6780914, by rfl⟩ : syracuseStep 9041219 = 13561829) B13561829
theorem B2381177 : Blo 1585491 2381177 := bstep (se 2 (by rfl) ⟨892941, by rfl⟩ : syracuseStep 2381177 = 1785883) B1785883
theorem B1586943 : Blo 1585491 1586943 := bstep (se 1 (by rfl) ⟨1190207, by rfl⟩ : syracuseStep 1586943 = 2380415) B2380415
theorem B65165185 : Blo 1585491 65165185 := bstep (se 2 (by rfl) ⟨24436944, by rfl⟩ : syracuseStep 65165185 = 48873889) B48873889
theorem B1587311 : Blo 1585491 1587311 := bstep (se 1 (by rfl) ⟨1190483, by rfl⟩ : syracuseStep 1587311 = 2380967) B2380967
theorem B3569903 : Blo 1585491 3569903 := bstep (se 1 (by rfl) ⟨2677427, by rfl⟩ : syracuseStep 3569903 = 5354855) B5354855
theorem B77207903 : Blo 1585491 77207903 := bstep (se 1 (by rfl) ⟨57905927, by rfl⟩ : syracuseStep 77207903 = 115811855) B115811855
theorem B3013375 : Blo 1585491 3013375 := bstep (se 1 (by rfl) ⟨2260031, by rfl⟩ : syracuseStep 3013375 = 4520063) B4520063
theorem B8035361 : Blo 1585491 8035361 := bstep (se 2 (by rfl) ⟨3013260, by rfl⟩ : syracuseStep 8035361 = 6026521) B6026521
theorem B19299455 : Blo 1585491 19299455 := bstep (se 1 (by rfl) ⟨14474591, by rfl⟩ : syracuseStep 19299455 = 28949183) B28949183
theorem B5356799 : Blo 1585491 5356799 := bstep (se 1 (by rfl) ⟨4017599, by rfl⟩ : syracuseStep 5356799 = 8035199) B8035199
theorem B7626473 : Blo 1585491 7626473 := bstep (se 2 (by rfl) ⟨2859927, by rfl⟩ : syracuseStep 7626473 = 5719855) B5719855
theorem B6021161 : Blo 1585491 6021161 := bstep (se 2 (by rfl) ⟨2257935, by rfl⟩ : syracuseStep 6021161 = 4515871) B4515871
theorem B5357609 : Blo 1585491 5357609 := bstep (se 2 (by rfl) ⟨2009103, by rfl⟩ : syracuseStep 5357609 = 4018207) B4018207
theorem B4014623 : Blo 1585491 4014623 := bstep (se 1 (by rfl) ⟨3010967, by rfl⟩ : syracuseStep 4014623 = 6021935) B6021935
theorem B8028719 : Blo 1585491 8028719 := bstep (se 1 (by rfl) ⟨6021539, by rfl⟩ : syracuseStep 8028719 = 12043079) B12043079
theorem B6865481 : Blo 1585491 6865481 := bstep (se 2 (by rfl) ⟨2574555, by rfl⟩ : syracuseStep 6865481 = 5149111) B5149111
theorem B14467871 : Blo 1585491 14467871 := bstep (se 1 (by rfl) ⟨10850903, by rfl⟩ : syracuseStep 14467871 = 21701807) B21701807
theorem B6866383 : Blo 1585491 6866383 := bstep (se 1 (by rfl) ⟨5149787, by rfl⟩ : syracuseStep 6866383 = 10299575) B10299575
theorem B2541055 : Blo 1585491 2541055 := bstep (se 1 (by rfl) ⟨1905791, by rfl⟩ : syracuseStep 2541055 = 3811583) B3811583
theorem B51471935 : Blo 1585491 51471935 := bstep (se 1 (by rfl) ⟨38603951, by rfl⟩ : syracuseStep 51471935 = 77207903) B77207903
theorem B86886913 : Blo 1585491 86886913 := bstep (se 2 (by rfl) ⟨32582592, by rfl⟩ : syracuseStep 86886913 = 65165185) B65165185
theorem B2378735 : Blo 1585491 2378735 := bstep (se 1 (by rfl) ⟨1784051, by rfl⟩ : syracuseStep 2378735 = 3568103) B3568103
theorem B8145983 : Blo 1585491 8145983 := bstep (se 1 (by rfl) ⟨6109487, by rfl⟩ : syracuseStep 8145983 = 12218975) B12218975
theorem B4517147 : Blo 1585491 4517147 := bstep (se 1 (by rfl) ⟨3387860, by rfl⟩ : syracuseStep 4517147 = 6775721) B6775721
theorem B6868253 : Blo 1585491 6868253 := bstep (se 3 (by rfl) ⟨1287797, by rfl⟩ : syracuseStep 6868253 = 2575595) B2575595
theorem B4517545 : Blo 1585491 4517545 := bstep (se 2 (by rfl) ⟨1694079, by rfl⟩ : syracuseStep 4517545 = 3388159) B3388159
theorem B4017833 : Blo 1585491 4017833 := bstep (se 2 (by rfl) ⟨1506687, by rfl⟩ : syracuseStep 4017833 = 3013375) B3013375
theorem B2379935 : Blo 1585491 2379935 := bstep (se 1 (by rfl) ⟨1784951, by rfl⟩ : syracuseStep 2379935 = 3569903) B3569903
theorem B1585567 : Blo 1585491 1585567 := bstep (se 1 (by rfl) ⟨1189175, by rfl⟩ : syracuseStep 1585567 = 2378351) B2378351
theorem B3568031 : Blo 1585491 3568031 := bstep (se 1 (by rfl) ⟨2676023, by rfl⟩ : syracuseStep 3568031 = 5352047) B5352047
theorem B130298543 : Blo 1585491 130298543 := bstep (se 1 (by rfl) ⟨97723907, by rfl⟩ : syracuseStep 130298543 = 195447815) B195447815
theorem B12866303 : Blo 1585491 12866303 := bstep (se 1 (by rfl) ⟨9649727, by rfl⟩ : syracuseStep 12866303 = 19299455) B19299455
theorem B3568607 : Blo 1585491 3568607 := bstep (se 1 (by rfl) ⟨2676455, by rfl⟩ : syracuseStep 3568607 = 5352911) B5352911
theorem B1586207 : Blo 1585491 1586207 := bstep (se 1 (by rfl) ⟨1189655, by rfl⟩ : syracuseStep 1586207 = 2379311) B2379311
theorem B4519003 : Blo 1585491 4519003 := bstep (se 1 (by rfl) ⟨3389252, by rfl⟩ : syracuseStep 4519003 = 6778505) B6778505
theorem B5084315 : Blo 1585491 5084315 := bstep (se 1 (by rfl) ⟨3813236, by rfl⟩ : syracuseStep 5084315 = 7626473) B7626473
theorem B5084495 : Blo 1585491 5084495 := bstep (se 1 (by rfl) ⟨3813371, by rfl⟩ : syracuseStep 5084495 = 7626743) B7626743
theorem B3569435 : Blo 1585491 3569435 := bstep (se 1 (by rfl) ⟨2677076, by rfl⟩ : syracuseStep 3569435 = 5354153) B5354153
theorem B305281025 : Blo 1585491 305281025 := bstep (se 2 (by rfl) ⟨114480384, by rfl⟩ : syracuseStep 305281025 = 228960769) B228960769
theorem B6027479 : Blo 1585491 6027479 := bstep (se 1 (by rfl) ⟨4520609, by rfl⟩ : syracuseStep 6027479 = 9041219) B9041219
theorem B1587451 : Blo 1585491 1587451 := bstep (se 1 (by rfl) ⟨1190588, by rfl⟩ : syracuseStep 1587451 = 2381177) B2381177
theorem B5085595 : Blo 1585491 5085595 := bstep (se 1 (by rfl) ⟨3814196, by rfl⟩ : syracuseStep 5085595 = 7628393) B7628393
theorem B5356907 : Blo 1585491 5356907 := bstep (se 1 (by rfl) ⟨4017680, by rfl⟩ : syracuseStep 5356907 = 8035361) B8035361
theorem B3571199 : Blo 1585491 3571199 := bstep (se 1 (by rfl) ⟨2678399, by rfl⟩ : syracuseStep 3571199 = 5356799) B5356799
theorem B4014107 : Blo 1585491 4014107 := bstep (se 1 (by rfl) ⟨3010580, by rfl⟩ : syracuseStep 4014107 = 6021161) B6021161
theorem B3571739 : Blo 1585491 3571739 := bstep (se 1 (by rfl) ⟨2678804, by rfl⟩ : syracuseStep 3571739 = 5357609) B5357609
theorem B8577535 : Blo 1585491 8577535 := bstep (se 1 (by rfl) ⟨6433151, by rfl⟩ : syracuseStep 8577535 = 12866303) B12866303
theorem B6023393 : Blo 1585491 6023393 := bstep (se 2 (by rfl) ⟨2258772, by rfl⟩ : syracuseStep 6023393 = 4517545) B4517545
theorem B2378687 : Blo 1585491 2378687 := bstep (se 1 (by rfl) ⟨1784015, by rfl⟩ : syracuseStep 2378687 = 3568031) B3568031
theorem B5352479 : Blo 1585491 5352479 := bstep (se 1 (by rfl) ⟨4014359, by rfl⟩ : syracuseStep 5352479 = 8028719) B8028719
theorem B9645247 : Blo 1585491 9645247 := bstep (se 1 (by rfl) ⟨7233935, by rfl⟩ : syracuseStep 9645247 = 14467871) B14467871
theorem B2379071 : Blo 1585491 2379071 := bstep (se 1 (by rfl) ⟨1784303, by rfl⟩ : syracuseStep 2379071 = 3568607) B3568607
theorem B2379623 : Blo 1585491 2379623 := bstep (se 1 (by rfl) ⟨1784717, by rfl⟩ : syracuseStep 2379623 = 3569435) B3569435
theorem B6025337 : Blo 1585491 6025337 := bstep (se 2 (by rfl) ⟨2259501, by rfl⟩ : syracuseStep 6025337 = 4519003) B4519003
theorem B4018319 : Blo 1585491 4018319 := bstep (se 1 (by rfl) ⟨3013739, by rfl⟩ : syracuseStep 4018319 = 6027479) B6027479
theorem B9155177 : Blo 1585491 9155177 := bstep (se 2 (by rfl) ⟨3433191, by rfl⟩ : syracuseStep 9155177 = 6866383) B6866383
theorem B1585823 : Blo 1585491 1585823 := bstep (se 1 (by rfl) ⟨1189367, by rfl⟩ : syracuseStep 1585823 = 2378735) B2378735
theorem B3388073 : Blo 1585491 3388073 := bstep (se 2 (by rfl) ⟨1270527, by rfl⟩ : syracuseStep 3388073 = 2541055) B2541055
theorem B3011431 : Blo 1585491 3011431 := bstep (se 1 (by rfl) ⟨2258573, by rfl⟩ : syracuseStep 3011431 = 4517147) B4517147
theorem B2380799 : Blo 1585491 2380799 := bstep (se 1 (by rfl) ⟨1785599, by rfl⟩ : syracuseStep 2380799 = 3571199) B3571199
theorem B1586623 : Blo 1585491 1586623 := bstep (se 1 (by rfl) ⟨1189967, by rfl⟩ : syracuseStep 1586623 = 2379935) B2379935
theorem B2676415 : Blo 1585491 2676415 := bstep (se 1 (by rfl) ⟨2007311, by rfl⟩ : syracuseStep 2676415 = 4014623) B4014623
theorem B4576987 : Blo 1585491 4576987 := bstep (se 1 (by rfl) ⟨3432740, by rfl⟩ : syracuseStep 4576987 = 6865481) B6865481
theorem B86865695 : Blo 1585491 86865695 := bstep (se 1 (by rfl) ⟨65149271, by rfl⟩ : syracuseStep 86865695 = 130298543) B130298543
theorem B115849217 : Blo 1585491 115849217 := bstep (se 2 (by rfl) ⟨43443456, by rfl⟩ : syracuseStep 115849217 = 86886913) B86886913
theorem B18315341 : Blo 1585491 18315341 := bstep (se 3 (by rfl) ⟨3434126, by rfl⟩ : syracuseStep 18315341 = 6868253) B6868253
theorem B3389543 : Blo 1585491 3389543 := bstep (se 1 (by rfl) ⟨2542157, by rfl⟩ : syracuseStep 3389543 = 5084315) B5084315
theorem B3389663 : Blo 1585491 3389663 := bstep (se 1 (by rfl) ⟨2542247, by rfl⟩ : syracuseStep 3389663 = 5084495) B5084495
theorem B34314623 : Blo 1585491 34314623 := bstep (se 1 (by rfl) ⟨25735967, by rfl⟩ : syracuseStep 34314623 = 51471935) B51471935
theorem B203520683 : Blo 1585491 203520683 := bstep (se 1 (by rfl) ⟨152640512, by rfl⟩ : syracuseStep 203520683 = 305281025) B305281025
theorem B5430655 : Blo 1585491 5430655 := bstep (se 1 (by rfl) ⟨4072991, by rfl⟩ : syracuseStep 5430655 = 8145983) B8145983
theorem B27123173 : Blo 1585491 27123173 := bstep (se 4 (by rfl) ⟨2542797, by rfl⟩ : syracuseStep 27123173 = 5085595) B5085595
theorem B3571271 : Blo 1585491 3571271 := bstep (se 1 (by rfl) ⟨2678453, by rfl⟩ : syracuseStep 3571271 = 5356907) B5356907
theorem B2678555 : Blo 1585491 2678555 := bstep (se 1 (by rfl) ⟨2008916, by rfl⟩ : syracuseStep 2678555 = 4017833) B4017833
theorem B2678879 : Blo 1585491 2678879 := bstep (se 1 (by rfl) ⟨2009159, by rfl⟩ : syracuseStep 2678879 = 4018319) B4018319
theorem B6103451 : Blo 1585491 6103451 := bstep (se 1 (by rfl) ⟨4577588, by rfl⟩ : syracuseStep 6103451 = 9155177) B9155177
theorem B11436713 : Blo 1585491 11436713 := bstep (se 2 (by rfl) ⟨4288767, by rfl⟩ : syracuseStep 11436713 = 8577535) B8577535
theorem B4015241 : Blo 1585491 4015241 := bstep (se 2 (by rfl) ⟨1505715, by rfl⟩ : syracuseStep 4015241 = 3011431) B3011431
theorem B57910463 : Blo 1585491 57910463 := bstep (se 1 (by rfl) ⟨43432847, by rfl⟩ : syracuseStep 57910463 = 86865695) B86865695
theorem B4015595 : Blo 1585491 4015595 := bstep (se 1 (by rfl) ⟨3011696, by rfl⟩ : syracuseStep 4015595 = 6023393) B6023393
theorem B18082115 : Blo 1585491 18082115 := bstep (se 1 (by rfl) ⟨13561586, by rfl⟩ : syracuseStep 18082115 = 27123173) B27123173
theorem B4016891 : Blo 1585491 4016891 := bstep (se 1 (by rfl) ⟨3012668, by rfl⟩ : syracuseStep 4016891 = 6025337) B6025337
theorem B51441317 : Blo 1585491 51441317 := bstep (se 4 (by rfl) ⟨4822623, by rfl⟩ : syracuseStep 51441317 = 9645247) B9645247
theorem B12210227 : Blo 1585491 12210227 := bstep (se 1 (by rfl) ⟨9157670, by rfl⟩ : syracuseStep 12210227 = 18315341) B18315341
theorem B22876415 : Blo 1585491 22876415 := bstep (se 1 (by rfl) ⟨17157311, by rfl⟩ : syracuseStep 22876415 = 34314623) B34314623
theorem B135680455 : Blo 1585491 135680455 := bstep (se 1 (by rfl) ⟨101760341, by rfl⟩ : syracuseStep 135680455 = 203520683) B203520683
theorem B1585791 : Blo 1585491 1585791 := bstep (se 1 (by rfl) ⟨1189343, by rfl⟩ : syracuseStep 1585791 = 2378687) B2378687
theorem B3568319 : Blo 1585491 3568319 := bstep (se 1 (by rfl) ⟨2676239, by rfl⟩ : syracuseStep 3568319 = 5352479) B5352479
theorem B1586047 : Blo 1585491 1586047 := bstep (se 1 (by rfl) ⟨1189535, by rfl⟩ : syracuseStep 1586047 = 2379071) B2379071
theorem B3568553 : Blo 1585491 3568553 := bstep (se 2 (by rfl) ⟨1338207, by rfl⟩ : syracuseStep 3568553 = 2676415) B2676415
theorem B2380847 : Blo 1585491 2380847 := bstep (se 1 (by rfl) ⟨1785635, by rfl⟩ : syracuseStep 2380847 = 3571271) B3571271
theorem B1586415 : Blo 1585491 1586415 := bstep (se 1 (by rfl) ⟨1189811, by rfl⟩ : syracuseStep 1586415 = 2379623) B2379623
theorem B2676071 : Blo 1585491 2676071 := bstep (se 1 (by rfl) ⟨2007053, by rfl⟩ : syracuseStep 2676071 = 4014107) B4014107
theorem B2381159 : Blo 1585491 2381159 := bstep (se 1 (by rfl) ⟨1785869, by rfl⟩ : syracuseStep 2381159 = 3571739) B3571739
theorem B1587199 : Blo 1585491 1587199 := bstep (se 1 (by rfl) ⟨1190399, by rfl⟩ : syracuseStep 1587199 = 2380799) B2380799
theorem B77232811 : Blo 1585491 77232811 := bstep (se 1 (by rfl) ⟨57924608, by rfl⟩ : syracuseStep 77232811 = 115849217) B115849217
theorem B2259695 : Blo 1585491 2259695 := bstep (se 1 (by rfl) ⟨1694771, by rfl⟩ : syracuseStep 2259695 = 3389543) B3389543
theorem B2259775 : Blo 1585491 2259775 := bstep (se 1 (by rfl) ⟨1694831, by rfl⟩ : syracuseStep 2259775 = 3389663) B3389663
theorem B9034861 : Blo 1585491 9034861 := bstep (se 3 (by rfl) ⟨1694036, by rfl⟩ : syracuseStep 9034861 = 3388073) B3388073
theorem B7240873 : Blo 1585491 7240873 := bstep (se 2 (by rfl) ⟨2715327, by rfl⟩ : syracuseStep 7240873 = 5430655) B5430655
theorem B6102649 : Blo 1585491 6102649 := bstep (se 2 (by rfl) ⟨2288493, by rfl⟩ : syracuseStep 6102649 = 4576987) B4576987
theorem B1785703 : Blo 1585491 1785703 := bstep (se 1 (by rfl) ⟨1339277, by rfl⟩ : syracuseStep 1785703 = 2678555) B2678555
theorem B1785919 : Blo 1585491 1785919 := bstep (se 1 (by rfl) ⟨1339439, by rfl⟩ : syracuseStep 1785919 = 2678879) B2678879
theorem B8136865 : Blo 1585491 8136865 := bstep (se 2 (by rfl) ⟨3051324, by rfl⟩ : syracuseStep 8136865 = 6102649) B6102649
theorem B34294211 : Blo 1585491 34294211 := bstep (se 1 (by rfl) ⟨25720658, by rfl⟩ : syracuseStep 34294211 = 51441317) B51441317
theorem B2378879 : Blo 1585491 2378879 := bstep (se 1 (by rfl) ⟨1784159, by rfl⟩ : syracuseStep 2378879 = 3568319) B3568319
theorem B180907273 : Blo 1585491 180907273 := bstep (se 2 (by rfl) ⟨67840227, by rfl⟩ : syracuseStep 180907273 = 135680455) B135680455
theorem B2379035 : Blo 1585491 2379035 := bstep (se 1 (by rfl) ⟨1784276, by rfl⟩ : syracuseStep 2379035 = 3568553) B3568553
theorem B102977081 : Blo 1585491 102977081 := bstep (se 2 (by rfl) ⟨38616405, by rfl⟩ : syracuseStep 102977081 = 77232811) B77232811
theorem B12046481 : Blo 1585491 12046481 := bstep (se 2 (by rfl) ⟨4517430, by rfl⟩ : syracuseStep 12046481 = 9034861) B9034861
theorem B12054743 : Blo 1585491 12054743 := bstep (se 1 (by rfl) ⟨9041057, by rfl⟩ : syracuseStep 12054743 = 18082115) B18082115
theorem B9654497 : Blo 1585491 9654497 := bstep (se 2 (by rfl) ⟨3620436, by rfl⟩ : syracuseStep 9654497 = 7240873) B7240873
theorem B6025853 : Blo 1585491 6025853 := bstep (se 3 (by rfl) ⟨1129847, by rfl⟩ : syracuseStep 6025853 = 2259695) B2259695
theorem B2380937 : Blo 1585491 2380937 := bstep (se 2 (by rfl) ⟨892851, by rfl⟩ : syracuseStep 2380937 = 1785703) B1785703
theorem B8140151 : Blo 1585491 8140151 := bstep (se 1 (by rfl) ⟨6105113, by rfl⟩ : syracuseStep 8140151 = 12210227) B12210227
theorem B15250943 : Blo 1585491 15250943 := bstep (se 1 (by rfl) ⟨11438207, by rfl⟩ : syracuseStep 15250943 = 22876415) B22876415
theorem B4068967 : Blo 1585491 4068967 := bstep (se 1 (by rfl) ⟨3051725, by rfl⟩ : syracuseStep 4068967 = 6103451) B6103451
theorem B7624475 : Blo 1585491 7624475 := bstep (se 1 (by rfl) ⟨5718356, by rfl⟩ : syracuseStep 7624475 = 11436713) B11436713
theorem B1587231 : Blo 1585491 1587231 := bstep (se 1 (by rfl) ⟨1190423, by rfl⟩ : syracuseStep 1587231 = 2380847) B2380847
theorem B2676827 : Blo 1585491 2676827 := bstep (se 1 (by rfl) ⟨2007620, by rfl⟩ : syracuseStep 2676827 = 4015241) B4015241
theorem B38606975 : Blo 1585491 38606975 := bstep (se 1 (by rfl) ⟨28955231, by rfl⟩ : syracuseStep 38606975 = 57910463) B57910463
theorem B1784047 : Blo 1585491 1784047 := bstep (se 1 (by rfl) ⟨1338035, by rfl⟩ : syracuseStep 1784047 = 2676071) B2676071
theorem B1587439 : Blo 1585491 1587439 := bstep (se 1 (by rfl) ⟨1190579, by rfl⟩ : syracuseStep 1587439 = 2381159) B2381159
theorem B2677063 : Blo 1585491 2677063 := bstep (se 1 (by rfl) ⟨2007797, by rfl⟩ : syracuseStep 2677063 = 4015595) B4015595
theorem B3013033 : Blo 1585491 3013033 := bstep (se 2 (by rfl) ⟨1129887, by rfl⟩ : syracuseStep 3013033 = 2259775) B2259775
theorem B2677927 : Blo 1585491 2677927 := bstep (se 1 (by rfl) ⟨2008445, by rfl⟩ : syracuseStep 2677927 = 4016891) B4016891
theorem B8036495 : Blo 1585491 8036495 := bstep (se 1 (by rfl) ⟨6027371, by rfl⟩ : syracuseStep 8036495 = 12054743) B12054743
theorem B10167295 : Blo 1585491 10167295 := bstep (se 1 (by rfl) ⟨7625471, by rfl⟩ : syracuseStep 10167295 = 15250943) B15250943
theorem B5425289 : Blo 1585491 5425289 := bstep (se 2 (by rfl) ⟨2034483, by rfl⟩ : syracuseStep 5425289 = 4068967) B4068967
theorem B68651387 : Blo 1585491 68651387 := bstep (se 1 (by rfl) ⟨51488540, by rfl⟩ : syracuseStep 68651387 = 102977081) B102977081
theorem B8030987 : Blo 1585491 8030987 := bstep (se 1 (by rfl) ⟨6023240, by rfl⟩ : syracuseStep 8030987 = 12046481) B12046481
theorem B10849153 : Blo 1585491 10849153 := bstep (se 2 (by rfl) ⟨4068432, by rfl⟩ : syracuseStep 10849153 = 8136865) B8136865
theorem B2378729 : Blo 1585491 2378729 := bstep (se 2 (by rfl) ⟨892023, by rfl⟩ : syracuseStep 2378729 = 1784047) B1784047
theorem B4017235 : Blo 1585491 4017235 := bstep (se 1 (by rfl) ⟨3012926, by rfl⟩ : syracuseStep 4017235 = 6025853) B6025853
theorem B4017377 : Blo 1585491 4017377 := bstep (se 2 (by rfl) ⟨1506516, by rfl⟩ : syracuseStep 4017377 = 3013033) B3013033
theorem B5426767 : Blo 1585491 5426767 := bstep (se 1 (by rfl) ⟨4070075, by rfl⟩ : syracuseStep 5426767 = 8140151) B8140151
theorem B5082983 : Blo 1585491 5082983 := bstep (se 1 (by rfl) ⟨3812237, by rfl⟩ : syracuseStep 5082983 = 7624475) B7624475
theorem B241209697 : Blo 1585491 241209697 := bstep (se 2 (by rfl) ⟨90453636, by rfl⟩ : syracuseStep 241209697 = 180907273) B180907273
theorem B1585919 : Blo 1585491 1585919 := bstep (se 1 (by rfl) ⟨1189439, by rfl⟩ : syracuseStep 1585919 = 2378879) B2378879
theorem B1586023 : Blo 1585491 1586023 := bstep (se 1 (by rfl) ⟨1189517, by rfl⟩ : syracuseStep 1586023 = 2379035) B2379035
theorem B2381225 : Blo 1585491 2381225 := bstep (se 2 (by rfl) ⟨892959, by rfl⟩ : syracuseStep 2381225 = 1785919) B1785919
theorem B6436331 : Blo 1585491 6436331 := bstep (se 1 (by rfl) ⟨4827248, by rfl⟩ : syracuseStep 6436331 = 9654497) B9654497
theorem B3569417 : Blo 1585491 3569417 := bstep (se 2 (by rfl) ⟨1338531, by rfl⟩ : syracuseStep 3569417 = 2677063) B2677063
theorem B1587291 : Blo 1585491 1587291 := bstep (se 1 (by rfl) ⟨1190468, by rfl⟩ : syracuseStep 1587291 = 2380937) B2380937
theorem B1784551 : Blo 1585491 1784551 := bstep (se 1 (by rfl) ⟨1338413, by rfl⟩ : syracuseStep 1784551 = 2676827) B2676827
theorem B25737983 : Blo 1585491 25737983 := bstep (se 1 (by rfl) ⟨19303487, by rfl⟩ : syracuseStep 25737983 = 38606975) B38606975
theorem B3570569 : Blo 1585491 3570569 := bstep (se 2 (by rfl) ⟨1338963, by rfl⟩ : syracuseStep 3570569 = 2677927) B2677927
theorem B22862807 : Blo 1585491 22862807 := bstep (se 1 (by rfl) ⟨17147105, by rfl⟩ : syracuseStep 22862807 = 34294211) B34294211
theorem B5357663 : Blo 1585491 5357663 := bstep (se 1 (by rfl) ⟨4018247, by rfl⟩ : syracuseStep 5357663 = 8036495) B8036495
theorem B28942757 : Blo 1585491 28942757 := bstep (se 4 (by rfl) ⟨2713383, by rfl⟩ : syracuseStep 28942757 = 5426767) B5426767
theorem B321612929 : Blo 1585491 321612929 := bstep (se 2 (by rfl) ⟨120604848, by rfl⟩ : syracuseStep 321612929 = 241209697) B241209697
theorem B2379401 : Blo 1585491 2379401 := bstep (se 2 (by rfl) ⟨892275, by rfl⟩ : syracuseStep 2379401 = 1784551) B1784551
theorem B2379611 : Blo 1585491 2379611 := bstep (se 1 (by rfl) ⟨1784708, by rfl⟩ : syracuseStep 2379611 = 3569417) B3569417
theorem B3616859 : Blo 1585491 3616859 := bstep (se 1 (by rfl) ⟨2712644, by rfl⟩ : syracuseStep 3616859 = 5425289) B5425289
theorem B17158655 : Blo 1585491 17158655 := bstep (se 1 (by rfl) ⟨12868991, by rfl⟩ : syracuseStep 17158655 = 25737983) B25737983
theorem B5353991 : Blo 1585491 5353991 := bstep (se 1 (by rfl) ⟨4015493, by rfl⟩ : syracuseStep 5353991 = 8030987) B8030987
theorem B2380379 : Blo 1585491 2380379 := bstep (se 1 (by rfl) ⟨1785284, by rfl⟩ : syracuseStep 2380379 = 3570569) B3570569
theorem B15241871 : Blo 1585491 15241871 := bstep (se 1 (by rfl) ⟨11431403, by rfl⟩ : syracuseStep 15241871 = 22862807) B22862807
theorem B1585819 : Blo 1585491 1585819 := bstep (se 1 (by rfl) ⟨1189364, by rfl⟩ : syracuseStep 1585819 = 2378729) B2378729
theorem B3388655 : Blo 1585491 3388655 := bstep (se 1 (by rfl) ⟨2541491, by rfl⟩ : syracuseStep 3388655 = 5082983) B5082983
theorem B1587483 : Blo 1585491 1587483 := bstep (se 1 (by rfl) ⟨1190612, by rfl⟩ : syracuseStep 1587483 = 2381225) B2381225
theorem B4290887 : Blo 1585491 4290887 := bstep (se 1 (by rfl) ⟨3218165, by rfl⟩ : syracuseStep 4290887 = 6436331) B6436331
theorem B14465537 : Blo 1585491 14465537 := bstep (se 2 (by rfl) ⟨5424576, by rfl⟩ : syracuseStep 14465537 = 10849153) B10849153
theorem B13556393 : Blo 1585491 13556393 := bstep (se 2 (by rfl) ⟨5083647, by rfl⟩ : syracuseStep 13556393 = 10167295) B10167295
theorem B5356313 : Blo 1585491 5356313 := bstep (se 2 (by rfl) ⟨2008617, by rfl⟩ : syracuseStep 5356313 = 4017235) B4017235
theorem B45767591 : Blo 1585491 45767591 := bstep (se 1 (by rfl) ⟨34325693, by rfl⟩ : syracuseStep 45767591 = 68651387) B68651387
theorem B2678251 : Blo 1585491 2678251 := bstep (se 1 (by rfl) ⟨2008688, by rfl⟩ : syracuseStep 2678251 = 4017377) B4017377
theorem B3571775 : Blo 1585491 3571775 := bstep (se 1 (by rfl) ⟨2678831, by rfl⟩ : syracuseStep 3571775 = 5357663) B5357663
theorem B2860591 : Blo 1585491 2860591 := bstep (se 1 (by rfl) ⟨2145443, by rfl⟩ : syracuseStep 2860591 = 4290887) B4290887
theorem B9643691 : Blo 1585491 9643691 := bstep (se 1 (by rfl) ⟨7232768, by rfl⟩ : syracuseStep 9643691 = 14465537) B14465537
theorem B9037595 : Blo 1585491 9037595 := bstep (se 1 (by rfl) ⟨6778196, by rfl⟩ : syracuseStep 9037595 = 13556393) B13556393
theorem B2411239 : Blo 1585491 2411239 := bstep (se 1 (by rfl) ⟨1808429, by rfl⟩ : syracuseStep 2411239 = 3616859) B3616859
theorem B19295171 : Blo 1585491 19295171 := bstep (se 1 (by rfl) ⟨14471378, by rfl⟩ : syracuseStep 19295171 = 28942757) B28942757
theorem B10161247 : Blo 1585491 10161247 := bstep (se 1 (by rfl) ⟨7620935, by rfl⟩ : syracuseStep 10161247 = 15241871) B15241871
theorem B45756413 : Blo 1585491 45756413 := bstep (se 3 (by rfl) ⟨8579327, by rfl⟩ : syracuseStep 45756413 = 17158655) B17158655
theorem B30511727 : Blo 1585491 30511727 := bstep (se 1 (by rfl) ⟨22883795, by rfl⟩ : syracuseStep 30511727 = 45767591) B45767591
theorem B1586267 : Blo 1585491 1586267 := bstep (se 1 (by rfl) ⟨1189700, by rfl⟩ : syracuseStep 1586267 = 2379401) B2379401
theorem B1586407 : Blo 1585491 1586407 := bstep (se 1 (by rfl) ⟨1189805, by rfl⟩ : syracuseStep 1586407 = 2379611) B2379611
theorem B3569327 : Blo 1585491 3569327 := bstep (se 1 (by rfl) ⟨2676995, by rfl⟩ : syracuseStep 3569327 = 5353991) B5353991
theorem B1586919 : Blo 1585491 1586919 := bstep (se 1 (by rfl) ⟨1190189, by rfl⟩ : syracuseStep 1586919 = 2380379) B2380379
theorem B2259103 : Blo 1585491 2259103 := bstep (se 1 (by rfl) ⟨1694327, by rfl⟩ : syracuseStep 2259103 = 3388655) B3388655
theorem B3570875 : Blo 1585491 3570875 := bstep (se 1 (by rfl) ⟨2678156, by rfl⟩ : syracuseStep 3570875 = 5356313) B5356313
theorem B3571001 : Blo 1585491 3571001 := bstep (se 2 (by rfl) ⟨1339125, by rfl⟩ : syracuseStep 3571001 = 2678251) B2678251
theorem B214408619 : Blo 1585491 214408619 := bstep (se 1 (by rfl) ⟨160806464, by rfl⟩ : syracuseStep 214408619 = 321612929) B321612929
theorem B20341151 : Blo 1585491 20341151 := bstep (se 1 (by rfl) ⟨15255863, by rfl⟩ : syracuseStep 20341151 = 30511727) B30511727
theorem B12863447 : Blo 1585491 12863447 := bstep (se 1 (by rfl) ⟨9647585, by rfl⟩ : syracuseStep 12863447 = 19295171) B19295171
theorem B3214985 : Blo 1585491 3214985 := bstep (se 2 (by rfl) ⟨1205619, by rfl⟩ : syracuseStep 3214985 = 2411239) B2411239
theorem B2379551 : Blo 1585491 2379551 := bstep (se 1 (by rfl) ⟨1784663, by rfl⟩ : syracuseStep 2379551 = 3569327) B3569327
theorem B6025063 : Blo 1585491 6025063 := bstep (se 1 (by rfl) ⟨4518797, by rfl⟩ : syracuseStep 6025063 = 9037595) B9037595
theorem B3814121 : Blo 1585491 3814121 := bstep (se 2 (by rfl) ⟨1430295, by rfl⟩ : syracuseStep 3814121 = 2860591) B2860591
theorem B2380583 : Blo 1585491 2380583 := bstep (se 1 (by rfl) ⟨1785437, by rfl⟩ : syracuseStep 2380583 = 3570875) B3570875
theorem B2380667 : Blo 1585491 2380667 := bstep (se 1 (by rfl) ⟨1785500, by rfl⟩ : syracuseStep 2380667 = 3571001) B3571001
theorem B142939079 : Blo 1585491 142939079 := bstep (se 1 (by rfl) ⟨107204309, by rfl⟩ : syracuseStep 142939079 = 214408619) B214408619
theorem B30504275 : Blo 1585491 30504275 := bstep (se 1 (by rfl) ⟨22878206, by rfl⟩ : syracuseStep 30504275 = 45756413) B45756413
theorem B2381183 : Blo 1585491 2381183 := bstep (se 1 (by rfl) ⟨1785887, by rfl⟩ : syracuseStep 2381183 = 3571775) B3571775
theorem B3012137 : Blo 1585491 3012137 := bstep (se 2 (by rfl) ⟨1129551, by rfl⟩ : syracuseStep 3012137 = 2259103) B2259103
theorem B6429127 : Blo 1585491 6429127 := bstep (se 1 (by rfl) ⟨4821845, by rfl⟩ : syracuseStep 6429127 = 9643691) B9643691
theorem B13548329 : Blo 1585491 13548329 := bstep (se 2 (by rfl) ⟨5080623, by rfl⟩ : syracuseStep 13548329 = 10161247) B10161247
theorem B2008091 : Blo 1585491 2008091 := bstep (se 1 (by rfl) ⟨1506068, by rfl⟩ : syracuseStep 2008091 = 3012137) B3012137
theorem B13560767 : Blo 1585491 13560767 := bstep (se 1 (by rfl) ⟨10170575, by rfl⟩ : syracuseStep 13560767 = 20341151) B20341151
theorem B2542747 : Blo 1585491 2542747 := bstep (se 1 (by rfl) ⟨1907060, by rfl⟩ : syracuseStep 2542747 = 3814121) B3814121
theorem B8572169 : Blo 1585491 8572169 := bstep (se 2 (by rfl) ⟨3214563, by rfl⟩ : syracuseStep 8572169 = 6429127) B6429127
theorem B95292719 : Blo 1585491 95292719 := bstep (se 1 (by rfl) ⟨71469539, by rfl⟩ : syracuseStep 95292719 = 142939079) B142939079
theorem B20336183 : Blo 1585491 20336183 := bstep (se 1 (by rfl) ⟨15252137, by rfl⟩ : syracuseStep 20336183 = 30504275) B30504275
theorem B8573293 : Blo 1585491 8573293 := bstep (se 3 (by rfl) ⟨1607492, by rfl⟩ : syracuseStep 8573293 = 3214985) B3214985
theorem B9032219 : Blo 1585491 9032219 := bstep (se 1 (by rfl) ⟨6774164, by rfl⟩ : syracuseStep 9032219 = 13548329) B13548329
theorem B8033417 : Blo 1585491 8033417 := bstep (se 2 (by rfl) ⟨3012531, by rfl⟩ : syracuseStep 8033417 = 6025063) B6025063
theorem B1586367 : Blo 1585491 1586367 := bstep (se 1 (by rfl) ⟨1189775, by rfl⟩ : syracuseStep 1586367 = 2379551) B2379551
theorem B1587055 : Blo 1585491 1587055 := bstep (se 1 (by rfl) ⟨1190291, by rfl⟩ : syracuseStep 1587055 = 2380583) B2380583
theorem B1587111 : Blo 1585491 1587111 := bstep (se 1 (by rfl) ⟨1190333, by rfl⟩ : syracuseStep 1587111 = 2380667) B2380667
theorem B1587455 : Blo 1585491 1587455 := bstep (se 1 (by rfl) ⟨1190591, by rfl⟩ : syracuseStep 1587455 = 2381183) B2381183
theorem B8575631 : Blo 1585491 8575631 := bstep (se 1 (by rfl) ⟨6431723, by rfl⟩ : syracuseStep 8575631 = 12863447) B12863447
theorem B6021479 : Blo 1585491 6021479 := bstep (se 1 (by rfl) ⟨4516109, by rfl⟩ : syracuseStep 6021479 = 9032219) B9032219
theorem B11431057 : Blo 1585491 11431057 := bstep (se 2 (by rfl) ⟨4286646, by rfl⟩ : syracuseStep 11431057 = 8573293) B8573293
theorem B22859117 : Blo 1585491 22859117 := bstep (se 3 (by rfl) ⟨4286084, by rfl⟩ : syracuseStep 22859117 = 8572169) B8572169
theorem B9040511 : Blo 1585491 9040511 := bstep (se 1 (by rfl) ⟨6780383, by rfl⟩ : syracuseStep 9040511 = 13560767) B13560767
theorem B5354909 : Blo 1585491 5354909 := bstep (se 3 (by rfl) ⟨1004045, by rfl⟩ : syracuseStep 5354909 = 2008091) B2008091
theorem B5355611 : Blo 1585491 5355611 := bstep (se 1 (by rfl) ⟨4016708, by rfl⟩ : syracuseStep 5355611 = 8033417) B8033417
theorem B3390329 : Blo 1585491 3390329 := bstep (se 2 (by rfl) ⟨1271373, by rfl⟩ : syracuseStep 3390329 = 2542747) B2542747
theorem B5717087 : Blo 1585491 5717087 := bstep (se 1 (by rfl) ⟨4287815, by rfl⟩ : syracuseStep 5717087 = 8575631) B8575631
theorem B63528479 : Blo 1585491 63528479 := bstep (se 1 (by rfl) ⟨47646359, by rfl⟩ : syracuseStep 63528479 = 95292719) B95292719
theorem B13557455 : Blo 1585491 13557455 := bstep (se 1 (by rfl) ⟨10168091, by rfl⟩ : syracuseStep 13557455 = 20336183) B20336183
theorem B4014319 : Blo 1585491 4014319 := bstep (se 1 (by rfl) ⟨3010739, by rfl⟩ : syracuseStep 4014319 = 6021479) B6021479
theorem B3811391 : Blo 1585491 3811391 := bstep (se 1 (by rfl) ⟨2858543, by rfl⟩ : syracuseStep 3811391 = 5717087) B5717087
theorem B15239411 : Blo 1585491 15239411 := bstep (se 1 (by rfl) ⟨11429558, by rfl⟩ : syracuseStep 15239411 = 22859117) B22859117
theorem B9038303 : Blo 1585491 9038303 := bstep (se 1 (by rfl) ⟨6778727, by rfl⟩ : syracuseStep 9038303 = 13557455) B13557455
theorem B15241409 : Blo 1585491 15241409 := bstep (se 2 (by rfl) ⟨5715528, by rfl⟩ : syracuseStep 15241409 = 11431057) B11431057
theorem B6027007 : Blo 1585491 6027007 := bstep (se 1 (by rfl) ⟨4520255, by rfl⟩ : syracuseStep 6027007 = 9040511) B9040511
theorem B3569939 : Blo 1585491 3569939 := bstep (se 1 (by rfl) ⟨2677454, by rfl⟩ : syracuseStep 3569939 = 5354909) B5354909
theorem B3570407 : Blo 1585491 3570407 := bstep (se 1 (by rfl) ⟨2677805, by rfl⟩ : syracuseStep 3570407 = 5355611) B5355611
theorem B2260219 : Blo 1585491 2260219 := bstep (se 1 (by rfl) ⟨1695164, by rfl⟩ : syracuseStep 2260219 = 3390329) B3390329
theorem B42352319 : Blo 1585491 42352319 := bstep (se 1 (by rfl) ⟨31764239, by rfl⟩ : syracuseStep 42352319 = 63528479) B63528479
theorem B2540927 : Blo 1585491 2540927 := bstep (se 1 (by rfl) ⟨1905695, by rfl⟩ : syracuseStep 2540927 = 3811391) B3811391
theorem B10159607 : Blo 1585491 10159607 := bstep (se 1 (by rfl) ⟨7619705, by rfl⟩ : syracuseStep 10159607 = 15239411) B15239411
theorem B10160939 : Blo 1585491 10160939 := bstep (se 1 (by rfl) ⟨7620704, by rfl⟩ : syracuseStep 10160939 = 15241409) B15241409
theorem B5352425 : Blo 1585491 5352425 := bstep (se 2 (by rfl) ⟨2007159, by rfl⟩ : syracuseStep 5352425 = 4014319) B4014319
theorem B2379959 : Blo 1585491 2379959 := bstep (se 1 (by rfl) ⟨1784969, by rfl⟩ : syracuseStep 2379959 = 3569939) B3569939
theorem B6025535 : Blo 1585491 6025535 := bstep (se 1 (by rfl) ⟨4519151, by rfl⟩ : syracuseStep 6025535 = 9038303) B9038303
theorem B2380271 : Blo 1585491 2380271 := bstep (se 1 (by rfl) ⟨1785203, by rfl⟩ : syracuseStep 2380271 = 3570407) B3570407
theorem B112939517 : Blo 1585491 112939517 := bstep (se 3 (by rfl) ⟨21176159, by rfl⟩ : syracuseStep 112939517 = 42352319) B42352319
theorem B3013625 : Blo 1585491 3013625 := bstep (se 2 (by rfl) ⟨1130109, by rfl⟩ : syracuseStep 3013625 = 2260219) B2260219
theorem B8036009 : Blo 1585491 8036009 := bstep (se 2 (by rfl) ⟨3013503, by rfl⟩ : syracuseStep 8036009 = 6027007) B6027007
theorem B75293011 : Blo 1585491 75293011 := bstep (se 1 (by rfl) ⟨56469758, by rfl⟩ : syracuseStep 75293011 = 112939517) B112939517
theorem B6775805 : Blo 1585491 6775805 := bstep (se 3 (by rfl) ⟨1270463, by rfl⟩ : syracuseStep 6775805 = 2540927) B2540927
theorem B4017023 : Blo 1585491 4017023 := bstep (se 1 (by rfl) ⟨3012767, by rfl⟩ : syracuseStep 4017023 = 6025535) B6025535
theorem B3568283 : Blo 1585491 3568283 := bstep (se 1 (by rfl) ⟨2676212, by rfl⟩ : syracuseStep 3568283 = 5352425) B5352425
theorem B1586639 : Blo 1585491 1586639 := bstep (se 1 (by rfl) ⟨1189979, by rfl⟩ : syracuseStep 1586639 = 2379959) B2379959
theorem B1586847 : Blo 1585491 1586847 := bstep (se 1 (by rfl) ⟨1190135, by rfl⟩ : syracuseStep 1586847 = 2380271) B2380271
theorem B6773071 : Blo 1585491 6773071 := bstep (se 1 (by rfl) ⟨5079803, by rfl⟩ : syracuseStep 6773071 = 10159607) B10159607
theorem B6773959 : Blo 1585491 6773959 := bstep (se 1 (by rfl) ⟨5080469, by rfl⟩ : syracuseStep 6773959 = 10160939) B10160939
theorem B5357339 : Blo 1585491 5357339 := bstep (se 1 (by rfl) ⟨4018004, by rfl⟩ : syracuseStep 5357339 = 8036009) B8036009
theorem B8036333 : Blo 1585491 8036333 := bstep (se 3 (by rfl) ⟨1506812, by rfl⟩ : syracuseStep 8036333 = 3013625) B3013625
theorem B2378855 : Blo 1585491 2378855 := bstep (se 1 (by rfl) ⟨1784141, by rfl⟩ : syracuseStep 2378855 = 3568283) B3568283
theorem B9030761 : Blo 1585491 9030761 := bstep (se 2 (by rfl) ⟨3386535, by rfl⟩ : syracuseStep 9030761 = 6773071) B6773071
theorem B4517203 : Blo 1585491 4517203 := bstep (se 1 (by rfl) ⟨3387902, by rfl⟩ : syracuseStep 4517203 = 6775805) B6775805
theorem B9031945 : Blo 1585491 9031945 := bstep (se 2 (by rfl) ⟨3386979, by rfl⟩ : syracuseStep 9031945 = 6773959) B6773959
theorem B100390681 : Blo 1585491 100390681 := bstep (se 2 (by rfl) ⟨37646505, by rfl⟩ : syracuseStep 100390681 = 75293011) B75293011
theorem B2678015 : Blo 1585491 2678015 := bstep (se 1 (by rfl) ⟨2008511, by rfl⟩ : syracuseStep 2678015 = 4017023) B4017023
theorem B3571559 : Blo 1585491 3571559 := bstep (se 1 (by rfl) ⟨2678669, by rfl⟩ : syracuseStep 3571559 = 5357339) B5357339
theorem B5357555 : Blo 1585491 5357555 := bstep (se 1 (by rfl) ⟨4018166, by rfl⟩ : syracuseStep 5357555 = 8036333) B8036333
theorem B12042593 : Blo 1585491 12042593 := bstep (se 2 (by rfl) ⟨4515972, by rfl⟩ : syracuseStep 12042593 = 9031945) B9031945
theorem B6022937 : Blo 1585491 6022937 := bstep (se 2 (by rfl) ⟨2258601, by rfl⟩ : syracuseStep 6022937 = 4517203) B4517203
theorem B3571703 : Blo 1585491 3571703 := bstep (se 1 (by rfl) ⟨2678777, by rfl⟩ : syracuseStep 3571703 = 5357555) B5357555
theorem B1585903 : Blo 1585491 1585903 := bstep (se 1 (by rfl) ⟨1189427, by rfl⟩ : syracuseStep 1585903 = 2378855) B2378855
theorem B133854241 : Blo 1585491 133854241 := bstep (se 2 (by rfl) ⟨50195340, by rfl⟩ : syracuseStep 133854241 = 100390681) B100390681
theorem B2381039 : Blo 1585491 2381039 := bstep (se 1 (by rfl) ⟨1785779, by rfl⟩ : syracuseStep 2381039 = 3571559) B3571559
theorem B6020507 : Blo 1585491 6020507 := bstep (se 1 (by rfl) ⟨4515380, by rfl⟩ : syracuseStep 6020507 = 9030761) B9030761
theorem B1785343 : Blo 1585491 1785343 := bstep (se 1 (by rfl) ⟨1339007, by rfl⟩ : syracuseStep 1785343 = 2678015) B2678015
theorem B8028395 : Blo 1585491 8028395 := bstep (se 1 (by rfl) ⟨6021296, by rfl⟩ : syracuseStep 8028395 = 12042593) B12042593
theorem B4015291 : Blo 1585491 4015291 := bstep (se 1 (by rfl) ⟨3011468, by rfl⟩ : syracuseStep 4015291 = 6022937) B6022937
theorem B178472321 : Blo 1585491 178472321 := bstep (se 2 (by rfl) ⟨66927120, by rfl⟩ : syracuseStep 178472321 = 133854241) B133854241
theorem B2380457 : Blo 1585491 2380457 := bstep (se 2 (by rfl) ⟨892671, by rfl⟩ : syracuseStep 2380457 = 1785343) B1785343
theorem B2381135 : Blo 1585491 2381135 := bstep (se 1 (by rfl) ⟨1785851, by rfl⟩ : syracuseStep 2381135 = 3571703) B3571703
theorem B1587359 : Blo 1585491 1587359 := bstep (se 1 (by rfl) ⟨1190519, by rfl⟩ : syracuseStep 1587359 = 2381039) B2381039
theorem B4013671 : Blo 1585491 4013671 := bstep (se 1 (by rfl) ⟨3010253, by rfl⟩ : syracuseStep 4013671 = 6020507) B6020507
theorem B118981547 : Blo 1585491 118981547 := bstep (se 1 (by rfl) ⟨89236160, by rfl⟩ : syracuseStep 118981547 = 178472321) B178472321
theorem B5351561 : Blo 1585491 5351561 := bstep (se 2 (by rfl) ⟨2006835, by rfl⟩ : syracuseStep 5351561 = 4013671) B4013671
theorem B5352263 : Blo 1585491 5352263 := bstep (se 1 (by rfl) ⟨4014197, by rfl⟩ : syracuseStep 5352263 = 8028395) B8028395
theorem B5353721 : Blo 1585491 5353721 := bstep (se 2 (by rfl) ⟨2007645, by rfl⟩ : syracuseStep 5353721 = 4015291) B4015291
theorem B1586971 : Blo 1585491 1586971 := bstep (se 1 (by rfl) ⟨1190228, by rfl⟩ : syracuseStep 1586971 = 2380457) B2380457
theorem B1587423 : Blo 1585491 1587423 := bstep (se 1 (by rfl) ⟨1190567, by rfl⟩ : syracuseStep 1587423 = 2381135) B2381135
theorem B3567707 : Blo 1585491 3567707 := bstep (se 1 (by rfl) ⟨2675780, by rfl⟩ : syracuseStep 3567707 = 5351561) B5351561
theorem B3568175 : Blo 1585491 3568175 := bstep (se 1 (by rfl) ⟨2676131, by rfl⟩ : syracuseStep 3568175 = 5352263) B5352263
theorem B3569147 : Blo 1585491 3569147 := bstep (se 1 (by rfl) ⟨2676860, by rfl⟩ : syracuseStep 3569147 = 5353721) B5353721
theorem B79321031 : Blo 1585491 79321031 := bstep (se 1 (by rfl) ⟨59490773, by rfl⟩ : syracuseStep 79321031 = 118981547) B118981547
theorem B52880687 : Blo 1585491 52880687 := bstep (se 1 (by rfl) ⟨39660515, by rfl⟩ : syracuseStep 52880687 = 79321031) B79321031
theorem B2378471 : Blo 1585491 2378471 := bstep (se 1 (by rfl) ⟨1783853, by rfl⟩ : syracuseStep 2378471 = 3567707) B3567707
theorem B2378783 : Blo 1585491 2378783 := bstep (se 1 (by rfl) ⟨1784087, by rfl⟩ : syracuseStep 2378783 = 3568175) B3568175
theorem B2379431 : Blo 1585491 2379431 := bstep (se 1 (by rfl) ⟨1784573, by rfl⟩ : syracuseStep 2379431 = 3569147) B3569147
theorem B35253791 : Blo 1585491 35253791 := bstep (se 1 (by rfl) ⟨26440343, by rfl⟩ : syracuseStep 35253791 = 52880687) B52880687
theorem B1585647 : Blo 1585491 1585647 := bstep (se 1 (by rfl) ⟨1189235, by rfl⟩ : syracuseStep 1585647 = 2378471) B2378471
theorem B1585855 : Blo 1585491 1585855 := bstep (se 1 (by rfl) ⟨1189391, by rfl⟩ : syracuseStep 1585855 = 2378783) B2378783
theorem B1586287 : Blo 1585491 1586287 := bstep (se 1 (by rfl) ⟨1189715, by rfl⟩ : syracuseStep 1586287 = 2379431) B2379431
theorem B23502527 : Blo 1585491 23502527 := bstep (se 1 (by rfl) ⟨17626895, by rfl⟩ : syracuseStep 23502527 = 35253791) B35253791
theorem B15668351 : Blo 1585491 15668351 := bstep (se 1 (by rfl) ⟨11751263, by rfl⟩ : syracuseStep 15668351 = 23502527) B23502527
theorem B10445567 : Blo 1585491 10445567 := bstep (se 1 (by rfl) ⟨7834175, by rfl⟩ : syracuseStep 10445567 = 15668351) B15668351
theorem B111419381 : Blo 1585491 111419381 := bstep (se 5 (by rfl) ⟨5222783, by rfl⟩ : syracuseStep 111419381 = 10445567) B10445567
theorem B74279587 : Blo 1585491 74279587 := bstep (se 1 (by rfl) ⟨55709690, by rfl⟩ : syracuseStep 74279587 = 111419381) B111419381
theorem B99039449 : Blo 1585491 99039449 := bstep (se 2 (by rfl) ⟨37139793, by rfl⟩ : syracuseStep 99039449 = 74279587) B74279587
theorem B264105197 : Blo 1585491 264105197 := bstep (se 3 (by rfl) ⟨49519724, by rfl⟩ : syracuseStep 264105197 = 99039449) B99039449
theorem B176070131 : Blo 1585491 176070131 := bstep (se 1 (by rfl) ⟨132052598, by rfl⟩ : syracuseStep 176070131 = 264105197) B264105197
theorem B117380087 : Blo 1585491 117380087 := bstep (se 1 (by rfl) ⟨88035065, by rfl⟩ : syracuseStep 117380087 = 176070131) B176070131
theorem B78253391 : Blo 1585491 78253391 := bstep (se 1 (by rfl) ⟨58690043, by rfl⟩ : syracuseStep 78253391 = 117380087) B117380087
theorem B208675709 : Blo 1585491 208675709 := bstep (se 3 (by rfl) ⟨39126695, by rfl⟩ : syracuseStep 208675709 = 78253391) B78253391
theorem B139117139 : Blo 1585491 139117139 := bstep (se 1 (by rfl) ⟨104337854, by rfl⟩ : syracuseStep 139117139 = 208675709) B208675709
theorem B92744759 : Blo 1585491 92744759 := bstep (se 1 (by rfl) ⟨69558569, by rfl⟩ : syracuseStep 92744759 = 139117139) B139117139
theorem B61829839 : Blo 1585491 61829839 := bstep (se 1 (by rfl) ⟨46372379, by rfl⟩ : syracuseStep 61829839 = 92744759) B92744759
theorem B82439785 : Blo 1585491 82439785 := bstep (se 2 (by rfl) ⟨30914919, by rfl⟩ : syracuseStep 82439785 = 61829839) B61829839
theorem B109919713 : Blo 1585491 109919713 := bstep (se 2 (by rfl) ⟨41219892, by rfl⟩ : syracuseStep 109919713 = 82439785) B82439785
theorem B146559617 : Blo 1585491 146559617 := bstep (se 2 (by rfl) ⟨54959856, by rfl⟩ : syracuseStep 146559617 = 109919713) B109919713
theorem B97706411 : Blo 1585491 97706411 := bstep (se 1 (by rfl) ⟨73279808, by rfl⟩ : syracuseStep 97706411 = 146559617) B146559617
theorem B65137607 : Blo 1585491 65137607 := bstep (se 1 (by rfl) ⟨48853205, by rfl⟩ : syracuseStep 65137607 = 97706411) B97706411
theorem B43425071 : Blo 1585491 43425071 := bstep (se 1 (by rfl) ⟨32568803, by rfl⟩ : syracuseStep 43425071 = 65137607) B65137607
theorem B28950047 : Blo 1585491 28950047 := bstep (se 1 (by rfl) ⟨21712535, by rfl⟩ : syracuseStep 28950047 = 43425071) B43425071
theorem B19300031 : Blo 1585491 19300031 := bstep (se 1 (by rfl) ⟨14475023, by rfl⟩ : syracuseStep 19300031 = 28950047) B28950047
theorem B12866687 : Blo 1585491 12866687 := bstep (se 1 (by rfl) ⟨9650015, by rfl⟩ : syracuseStep 12866687 = 19300031) B19300031
theorem B8577791 : Blo 1585491 8577791 := bstep (se 1 (by rfl) ⟨6433343, by rfl⟩ : syracuseStep 8577791 = 12866687) B12866687
theorem B5718527 : Blo 1585491 5718527 := bstep (se 1 (by rfl) ⟨4288895, by rfl⟩ : syracuseStep 5718527 = 8577791) B8577791
theorem B3812351 : Blo 1585491 3812351 := bstep (se 1 (by rfl) ⟨2859263, by rfl⟩ : syracuseStep 3812351 = 5718527) B5718527
theorem B40665077 : Blo 1585491 40665077 := bstep (se 5 (by rfl) ⟨1906175, by rfl⟩ : syracuseStep 40665077 = 3812351) B3812351
theorem B27110051 : Blo 1585491 27110051 := bstep (se 1 (by rfl) ⟨20332538, by rfl⟩ : syracuseStep 27110051 = 40665077) B40665077
theorem B18073367 : Blo 1585491 18073367 := bstep (se 1 (by rfl) ⟨13555025, by rfl⟩ : syracuseStep 18073367 = 27110051) B27110051
theorem B12048911 : Blo 1585491 12048911 := bstep (se 1 (by rfl) ⟨9036683, by rfl⟩ : syracuseStep 12048911 = 18073367) B18073367
theorem B8032607 : Blo 1585491 8032607 := bstep (se 1 (by rfl) ⟨6024455, by rfl⟩ : syracuseStep 8032607 = 12048911) B12048911
theorem B5355071 : Blo 1585491 5355071 := bstep (se 1 (by rfl) ⟨4016303, by rfl⟩ : syracuseStep 5355071 = 8032607) B8032607
theorem B3570047 : Blo 1585491 3570047 := bstep (se 1 (by rfl) ⟨2677535, by rfl⟩ : syracuseStep 3570047 = 5355071) B5355071
theorem B2380031 : Blo 1585491 2380031 := bstep (se 1 (by rfl) ⟨1785023, by rfl⟩ : syracuseStep 2380031 = 3570047) B3570047
theorem B1586687 : Blo 1585491 1586687 := bstep (se 1 (by rfl) ⟨1190015, by rfl⟩ : syracuseStep 1586687 = 2380031) B2380031

theorem C0 (j : ℕ) (h1 : 396372 ≤ j) (h2 : j ≤ 396872) : Blo 1585491 (4 * j + 3) := by
  interval_cases j
  · exact B1585491
  · exact B1585495
  · exact B1585499
  · exact B1585503
  · exact B1585507
  · exact B1585511
  · exact B1585515
  · exact B1585519
  · exact B1585523
  · exact B1585527
  · exact B1585531
  · exact B1585535
  · exact B1585539
  · exact B1585543
  · exact B1585547
  · exact B1585551
  · exact B1585555
  · exact B1585559
  · exact B1585563
  · exact B1585567
  · exact B1585571
  · exact B1585575
  · exact B1585579
  · exact B1585583
  · exact B1585587
  · exact B1585591
  · exact B1585595
  · exact B1585599
  · exact B1585603
  · exact B1585607
  · exact B1585611
  · exact B1585615
  · exact B1585619
  · exact B1585623
  · exact B1585627
  · exact B1585631
  · exact B1585635
  · exact B1585639
  · exact B1585643
  · exact B1585647
  · exact B1585651
  · exact B1585655
  · exact B1585659
  · exact B1585663
  · exact B1585667
  · exact B1585671
  · exact B1585675
  · exact B1585679
  · exact B1585683
  · exact B1585687
  · exact B1585691
  · exact B1585695
  · exact B1585699
  · exact B1585703
  · exact B1585707
  · exact B1585711
  · exact B1585715
  · exact B1585719
  · exact B1585723
  · exact B1585727
  · exact B1585731
  · exact B1585735
  · exact B1585739
  · exact B1585743
  · exact B1585747
  · exact B1585751
  · exact B1585755
  · exact B1585759
  · exact B1585763
  · exact B1585767
  · exact B1585771
  · exact B1585775
  · exact B1585779
  · exact B1585783
  · exact B1585787
  · exact B1585791
  · exact B1585795
  · exact B1585799
  · exact B1585803
  · exact B1585807
  · exact B1585811
  · exact B1585815
  · exact B1585819
  · exact B1585823
  · exact B1585827
  · exact B1585831
  · exact B1585835
  · exact B1585839
  · exact B1585843
  · exact B1585847
  · exact B1585851
  · exact B1585855
  · exact B1585859
  · exact B1585863
  · exact B1585867
  · exact B1585871
  · exact B1585875
  · exact B1585879
  · exact B1585883
  · exact B1585887
  · exact B1585891
  · exact B1585895
  · exact B1585899
  · exact B1585903
  · exact B1585907
  · exact B1585911
  · exact B1585915
  · exact B1585919
  · exact B1585923
  · exact B1585927
  · exact B1585931
  · exact B1585935
  · exact B1585939
  · exact B1585943
  · exact B1585947
  · exact B1585951
  · exact B1585955
  · exact B1585959
  · exact B1585963
  · exact B1585967
  · exact B1585971
  · exact B1585975
  · exact B1585979
  · exact B1585983
  · exact B1585987
  · exact B1585991
  · exact B1585995
  · exact B1585999
  · exact B1586003
  · exact B1586007
  · exact B1586011
  · exact B1586015
  · exact B1586019
  · exact B1586023
  · exact B1586027
  · exact B1586031
  · exact B1586035
  · exact B1586039
  · exact B1586043
  · exact B1586047
  · exact B1586051
  · exact B1586055
  · exact B1586059
  · exact B1586063
  · exact B1586067
  · exact B1586071
  · exact B1586075
  · exact B1586079
  · exact B1586083
  · exact B1586087
  · exact B1586091
  · exact B1586095
  · exact B1586099
  · exact B1586103
  · exact B1586107
  · exact B1586111
  · exact B1586115
  · exact B1586119
  · exact B1586123
  · exact B1586127
  · exact B1586131
  · exact B1586135
  · exact B1586139
  · exact B1586143
  · exact B1586147
  · exact B1586151
  · exact B1586155
  · exact B1586159
  · exact B1586163
  · exact B1586167
  · exact B1586171
  · exact B1586175
  · exact B1586179
  · exact B1586183
  · exact B1586187
  · exact B1586191
  · exact B1586195
  · exact B1586199
  · exact B1586203
  · exact B1586207
  · exact B1586211
  · exact B1586215
  · exact B1586219
  · exact B1586223
  · exact B1586227
  · exact B1586231
  · exact B1586235
  · exact B1586239
  · exact B1586243
  · exact B1586247
  · exact B1586251
  · exact B1586255
  · exact B1586259
  · exact B1586263
  · exact B1586267
  · exact B1586271
  · exact B1586275
  · exact B1586279
  · exact B1586283
  · exact B1586287
  · exact B1586291
  · exact B1586295
  · exact B1586299
  · exact B1586303
  · exact B1586307
  · exact B1586311
  · exact B1586315
  · exact B1586319
  · exact B1586323
  · exact B1586327
  · exact B1586331
  · exact B1586335
  · exact B1586339
  · exact B1586343
  · exact B1586347
  · exact B1586351
  · exact B1586355
  · exact B1586359
  · exact B1586363
  · exact B1586367
  · exact B1586371
  · exact B1586375
  · exact B1586379
  · exact B1586383
  · exact B1586387
  · exact B1586391
  · exact B1586395
  · exact B1586399
  · exact B1586403
  · exact B1586407
  · exact B1586411
  · exact B1586415
  · exact B1586419
  · exact B1586423
  · exact B1586427
  · exact B1586431
  · exact B1586435
  · exact B1586439
  · exact B1586443
  · exact B1586447
  · exact B1586451
  · exact B1586455
  · exact B1586459
  · exact B1586463
  · exact B1586467
  · exact B1586471
  · exact B1586475
  · exact B1586479
  · exact B1586483
  · exact B1586487
  · exact B1586491
  · exact B1586495
  · exact B1586499
  · exact B1586503
  · exact B1586507
  · exact B1586511
  · exact B1586515
  · exact B1586519
  · exact B1586523
  · exact B1586527
  · exact B1586531
  · exact B1586535
  · exact B1586539
  · exact B1586543
  · exact B1586547
  · exact B1586551
  · exact B1586555
  · exact B1586559
  · exact B1586563
  · exact B1586567
  · exact B1586571
  · exact B1586575
  · exact B1586579
  · exact B1586583
  · exact B1586587
  · exact B1586591
  · exact B1586595
  · exact B1586599
  · exact B1586603
  · exact B1586607
  · exact B1586611
  · exact B1586615
  · exact B1586619
  · exact B1586623
  · exact B1586627
  · exact B1586631
  · exact B1586635
  · exact B1586639
  · exact B1586643
  · exact B1586647
  · exact B1586651
  · exact B1586655
  · exact B1586659
  · exact B1586663
  · exact B1586667
  · exact B1586671
  · exact B1586675
  · exact B1586679
  · exact B1586683
  · exact B1586687
  · exact B1586691
  · exact B1586695
  · exact B1586699
  · exact B1586703
  · exact B1586707
  · exact B1586711
  · exact B1586715
  · exact B1586719
  · exact B1586723
  · exact B1586727
  · exact B1586731
  · exact B1586735
  · exact B1586739
  · exact B1586743
  · exact B1586747
  · exact B1586751
  · exact B1586755
  · exact B1586759
  · exact B1586763
  · exact B1586767
  · exact B1586771
  · exact B1586775
  · exact B1586779
  · exact B1586783
  · exact B1586787
  · exact B1586791
  · exact B1586795
  · exact B1586799
  · exact B1586803
  · exact B1586807
  · exact B1586811
  · exact B1586815
  · exact B1586819
  · exact B1586823
  · exact B1586827
  · exact B1586831
  · exact B1586835
  · exact B1586839
  · exact B1586843
  · exact B1586847
  · exact B1586851
  · exact B1586855
  · exact B1586859
  · exact B1586863
  · exact B1586867
  · exact B1586871
  · exact B1586875
  · exact B1586879
  · exact B1586883
  · exact B1586887
  · exact B1586891
  · exact B1586895
  · exact B1586899
  · exact B1586903
  · exact B1586907
  · exact B1586911
  · exact B1586915
  · exact B1586919
  · exact B1586923
  · exact B1586927
  · exact B1586931
  · exact B1586935
  · exact B1586939
  · exact B1586943
  · exact B1586947
  · exact B1586951
  · exact B1586955
  · exact B1586959
  · exact B1586963
  · exact B1586967
  · exact B1586971
  · exact B1586975
  · exact B1586979
  · exact B1586983
  · exact B1586987
  · exact B1586991
  · exact B1586995
  · exact B1586999
  · exact B1587003
  · exact B1587007
  · exact B1587011
  · exact B1587015
  · exact B1587019
  · exact B1587023
  · exact B1587027
  · exact B1587031
  · exact B1587035
  · exact B1587039
  · exact B1587043
  · exact B1587047
  · exact B1587051
  · exact B1587055
  · exact B1587059
  · exact B1587063
  · exact B1587067
  · exact B1587071
  · exact B1587075
  · exact B1587079
  · exact B1587083
  · exact B1587087
  · exact B1587091
  · exact B1587095
  · exact B1587099
  · exact B1587103
  · exact B1587107
  · exact B1587111
  · exact B1587115
  · exact B1587119
  · exact B1587123
  · exact B1587127
  · exact B1587131
  · exact B1587135
  · exact B1587139
  · exact B1587143
  · exact B1587147
  · exact B1587151
  · exact B1587155
  · exact B1587159
  · exact B1587163
  · exact B1587167
  · exact B1587171
  · exact B1587175
  · exact B1587179
  · exact B1587183
  · exact B1587187
  · exact B1587191
  · exact B1587195
  · exact B1587199
  · exact B1587203
  · exact B1587207
  · exact B1587211
  · exact B1587215
  · exact B1587219
  · exact B1587223
  · exact B1587227
  · exact B1587231
  · exact B1587235
  · exact B1587239
  · exact B1587243
  · exact B1587247
  · exact B1587251
  · exact B1587255
  · exact B1587259
  · exact B1587263
  · exact B1587267
  · exact B1587271
  · exact B1587275
  · exact B1587279
  · exact B1587283
  · exact B1587287
  · exact B1587291
  · exact B1587295
  · exact B1587299
  · exact B1587303
  · exact B1587307
  · exact B1587311
  · exact B1587315
  · exact B1587319
  · exact B1587323
  · exact B1587327
  · exact B1587331
  · exact B1587335
  · exact B1587339
  · exact B1587343
  · exact B1587347
  · exact B1587351
  · exact B1587355
  · exact B1587359
  · exact B1587363
  · exact B1587367
  · exact B1587371
  · exact B1587375
  · exact B1587379
  · exact B1587383
  · exact B1587387
  · exact B1587391
  · exact B1587395
  · exact B1587399
  · exact B1587403
  · exact B1587407
  · exact B1587411
  · exact B1587415
  · exact B1587419
  · exact B1587423
  · exact B1587427
  · exact B1587431
  · exact B1587435
  · exact B1587439
  · exact B1587443
  · exact B1587447
  · exact B1587451
  · exact B1587455
  · exact B1587459
  · exact B1587463
  · exact B1587467
  · exact B1587471
  · exact B1587475
  · exact B1587479
  · exact B1587483
  · exact B1587487
  · exact B1587491

theorem solution (m : ℕ) (hlo : 1585491 ≤ m) (hhi : m ≤ 1587491) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 396372 ≤ j := by omega
    have hj2 : j ≤ 396872 := by omega
    have hb : Blo 1585491 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
