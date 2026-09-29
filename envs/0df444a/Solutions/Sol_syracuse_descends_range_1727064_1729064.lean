-- Prove2me | solution 1 for syracuse_descends_range_1727064_1729064
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:31:15.724376+00:00
-- url     : https://prove2.me/submissions/aa6283f3-036a-40f3-8e25-31fc88100b0c

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


theorem B2768909 : Blo 1727064 2768909 := bbase (se 3 (by rfl) ⟨519170, by rfl⟩ : syracuseStep 2768909 = 1038341) (by norm_num)
theorem B4374557 : Blo 1727064 4374557 := bbase (se 3 (by rfl) ⟨820229, by rfl⟩ : syracuseStep 4374557 = 1640459) (by norm_num)
theorem B2334781 : Blo 1727064 2334781 := bbase (se 3 (by rfl) ⟨437771, by rfl⟩ : syracuseStep 2334781 = 875543) (by norm_num)
theorem B4153421 : Blo 1727064 4153421 := bbase (se 3 (by rfl) ⟨778766, by rfl⟩ : syracuseStep 4153421 = 1557533) (by norm_num)
theorem B22134869 : Blo 1727064 22134869 := bbase (se 8 (by rfl) ⟨129696, by rfl⟩ : syracuseStep 22134869 = 259393) (by norm_num)
theorem B2916445 : Blo 1727064 2916445 := bbase (se 3 (by rfl) ⟨546833, by rfl⟩ : syracuseStep 2916445 = 1093667) (by norm_num)
theorem B2187425 : Blo 1727064 2187425 := bbase (se 2 (by rfl) ⟨820284, by rfl⟩ : syracuseStep 2187425 = 1640569) (by norm_num)
theorem B2916533 : Blo 1727064 2916533 := bbase (se 5 (by rfl) ⟨136712, by rfl⟩ : syracuseStep 2916533 = 273425) (by norm_num)
theorem B5832917 : Blo 1727064 5832917 := bbase (se 7 (by rfl) ⟨68354, by rfl⟩ : syracuseStep 5832917 = 136709) (by norm_num)
theorem B2187481 : Blo 1727064 2187481 := bbase (se 2 (by rfl) ⟨820305, by rfl⟩ : syracuseStep 2187481 = 1640611) (by norm_num)
theorem B4374749 : Blo 1727064 4374749 := bbase (se 3 (by rfl) ⟨820265, by rfl⟩ : syracuseStep 4374749 = 1640531) (by norm_num)
theorem B2916661 : Blo 1727064 2916661 := bbase (se 5 (by rfl) ⟨136718, by rfl⟩ : syracuseStep 2916661 = 273437) (by norm_num)
theorem B2187577 : Blo 1727064 2187577 := bbase (se 2 (by rfl) ⟨820341, by rfl⟩ : syracuseStep 2187577 = 1640683) (by norm_num)
theorem B2916749 : Blo 1727064 2916749 := bbase (se 3 (by rfl) ⟨546890, by rfl⟩ : syracuseStep 2916749 = 1093781) (by norm_num)
theorem B2187749 : Blo 1727064 2187749 := bbase (se 4 (by rfl) ⟨205101, by rfl⟩ : syracuseStep 2187749 = 410203) (by norm_num)
theorem B2916877 : Blo 1727064 2916877 := bbase (se 3 (by rfl) ⟨546914, by rfl⟩ : syracuseStep 2916877 = 1093829) (by norm_num)
theorem B2187805 : Blo 1727064 2187805 := bbase (se 3 (by rfl) ⟨410213, by rfl⟩ : syracuseStep 2187805 = 820427) (by norm_num)
theorem B4375093 : Blo 1727064 4375093 := bbase (se 5 (by rfl) ⟨205082, by rfl⟩ : syracuseStep 4375093 = 410165) (by norm_num)
theorem B2916965 : Blo 1727064 2916965 := bbase (se 4 (by rfl) ⟨273465, by rfl⟩ : syracuseStep 2916965 = 546931) (by norm_num)
theorem B2187901 : Blo 1727064 2187901 := bbase (se 3 (by rfl) ⟨410231, by rfl⟩ : syracuseStep 2187901 = 820463) (by norm_num)
theorem B5833349 : Blo 1727064 5833349 := bbase (se 4 (by rfl) ⟨546876, by rfl⟩ : syracuseStep 5833349 = 1093753) (by norm_num)
theorem B4375205 : Blo 1727064 4375205 := bbase (se 4 (by rfl) ⟨410175, by rfl⟩ : syracuseStep 4375205 = 820351) (by norm_num)
theorem B8749781 : Blo 1727064 8749781 := bbase (se 7 (by rfl) ⟨102536, by rfl⟩ : syracuseStep 8749781 = 205073) (by norm_num)
theorem B2917093 : Blo 1727064 2917093 := bbase (se 4 (by rfl) ⟨273477, by rfl⟩ : syracuseStep 2917093 = 546955) (by norm_num)
theorem B6562565 : Blo 1727064 6562565 := bbase (se 4 (by rfl) ⟨615240, by rfl⟩ : syracuseStep 6562565 = 1230481) (by norm_num)
theorem B15770389 : Blo 1727064 15770389 := bbase (se 6 (by rfl) ⟨369618, by rfl⟩ : syracuseStep 15770389 = 739237) (by norm_num)
theorem B2188073 : Blo 1727064 2188073 := bbase (se 2 (by rfl) ⟨820527, by rfl⟩ : syracuseStep 2188073 = 1641055) (by norm_num)
theorem B2917181 : Blo 1727064 2917181 := bbase (se 3 (by rfl) ⟨546971, by rfl⟩ : syracuseStep 2917181 = 1093943) (by norm_num)
theorem B2188129 : Blo 1727064 2188129 := bbase (se 2 (by rfl) ⟨820548, by rfl⟩ : syracuseStep 2188129 = 1641097) (by norm_num)
theorem B4375397 : Blo 1727064 4375397 := bbase (se 4 (by rfl) ⟨410193, by rfl⟩ : syracuseStep 4375397 = 820387) (by norm_num)
theorem B2917309 : Blo 1727064 2917309 := bbase (se 3 (by rfl) ⟨546995, by rfl⟩ : syracuseStep 2917309 = 1093991) (by norm_num)
theorem B2188225 : Blo 1727064 2188225 := bbase (se 2 (by rfl) ⟨820584, by rfl⟩ : syracuseStep 2188225 = 1641169) (by norm_num)
theorem B2917397 : Blo 1727064 2917397 := bbase (se 6 (by rfl) ⟨68376, by rfl⟩ : syracuseStep 2917397 = 136753) (by norm_num)
theorem B6562853 : Blo 1727064 6562853 := bbase (se 4 (by rfl) ⟨615267, by rfl⟩ : syracuseStep 6562853 = 1230535) (by norm_num)
theorem B14754869 : Blo 1727064 14754869 := bbase (se 5 (by rfl) ⟨691634, by rfl⟩ : syracuseStep 14754869 = 1383269) (by norm_num)
theorem B5833781 : Blo 1727064 5833781 := bbase (se 5 (by rfl) ⟨273458, by rfl⟩ : syracuseStep 5833781 = 546917) (by norm_num)
theorem B7382117 : Blo 1727064 7382117 := bbase (se 4 (by rfl) ⟨692073, by rfl⟩ : syracuseStep 7382117 = 1384147) (by norm_num)
theorem B3114101 : Blo 1727064 3114101 := bbase (se 5 (by rfl) ⟨145973, by rfl⟩ : syracuseStep 3114101 = 291947) (by norm_num)
theorem B6227077 : Blo 1727064 6227077 := bbase (se 4 (by rfl) ⟨583788, by rfl⟩ : syracuseStep 6227077 = 1167577) (by norm_num)
theorem B2917525 : Blo 1727064 2917525 := bbase (se 6 (by rfl) ⟨68379, by rfl⟩ : syracuseStep 2917525 = 136759) (by norm_num)
theorem B4375741 : Blo 1727064 4375741 := bbase (se 3 (by rfl) ⟨820451, by rfl⟩ : syracuseStep 4375741 = 1640903) (by norm_num)
theorem B2917613 : Blo 1727064 2917613 := bbase (se 3 (by rfl) ⟨547052, by rfl⟩ : syracuseStep 2917613 = 1094105) (by norm_num)
theorem B3941629 : Blo 1727064 3941629 := bbase (se 3 (by rfl) ⟨739055, by rfl⟩ : syracuseStep 3941629 = 1478111) (by norm_num)
theorem B2335997 : Blo 1727064 2335997 := bbase (se 3 (by rfl) ⟨437999, by rfl⟩ : syracuseStep 2335997 = 875999) (by norm_num)
theorem B4375853 : Blo 1727064 4375853 := bbase (se 3 (by rfl) ⟨820472, by rfl⟩ : syracuseStep 4375853 = 1640945) (by norm_num)
theorem B12453173 : Blo 1727064 12453173 := bbase (se 5 (by rfl) ⟨583742, by rfl⟩ : syracuseStep 12453173 = 1167485) (by norm_num)
theorem B1844581 : Blo 1727064 1844581 := bbase (se 4 (by rfl) ⟨172929, by rfl⟩ : syracuseStep 1844581 = 345859) (by norm_num)
theorem B2917741 : Blo 1727064 2917741 := bbase (se 3 (by rfl) ⟨547076, by rfl⟩ : syracuseStep 2917741 = 1094153) (by norm_num)
theorem B1844641 : Blo 1727064 1844641 := bbase (se 2 (by rfl) ⟨691740, by rfl⟩ : syracuseStep 1844641 = 1383481) (by norm_num)
theorem B1942969 : Blo 1727064 1942969 := bbase (se 2 (by rfl) ⟨728613, by rfl⟩ : syracuseStep 1942969 = 1457227) (by norm_num)
theorem B1943005 : Blo 1727064 1943005 := bbase (se 3 (by rfl) ⟨364313, by rfl⟩ : syracuseStep 1943005 = 728627) (by norm_num)
theorem B5834213 : Blo 1727064 5834213 := bbase (se 4 (by rfl) ⟨546957, by rfl⟩ : syracuseStep 5834213 = 1093915) (by norm_num)
theorem B4376045 : Blo 1727064 4376045 := bbase (se 3 (by rfl) ⟨820508, by rfl⟩ : syracuseStep 4376045 = 1641017) (by norm_num)
theorem B1943041 : Blo 1727064 1943041 := bbase (se 2 (by rfl) ⟨728640, by rfl⟩ : syracuseStep 1943041 = 1457281) (by norm_num)
theorem B1943077 : Blo 1727064 1943077 := bbase (se 4 (by rfl) ⟨182163, by rfl⟩ : syracuseStep 1943077 = 364327) (by norm_num)
theorem B3114541 : Blo 1727064 3114541 := bbase (se 3 (by rfl) ⟨583976, by rfl⟩ : syracuseStep 3114541 = 1167953) (by norm_num)
theorem B1943113 : Blo 1727064 1943113 := bbase (se 2 (by rfl) ⟨728667, by rfl⟩ : syracuseStep 1943113 = 1457335) (by norm_num)
theorem B1943149 : Blo 1727064 1943149 := bbase (se 3 (by rfl) ⟨364340, by rfl⟩ : syracuseStep 1943149 = 728681) (by norm_num)
theorem B3114605 : Blo 1727064 3114605 := bbase (se 3 (by rfl) ⟨583988, by rfl⟩ : syracuseStep 3114605 = 1167977) (by norm_num)
theorem B1943185 : Blo 1727064 1943185 := bbase (se 2 (by rfl) ⟨728694, by rfl⟩ : syracuseStep 1943185 = 1457389) (by norm_num)
theorem B1943221 : Blo 1727064 1943221 := bbase (se 5 (by rfl) ⟨91088, by rfl⟩ : syracuseStep 1943221 = 182177) (by norm_num)
theorem B4736693 : Blo 1727064 4736693 := bbase (se 5 (by rfl) ⟨222032, by rfl⟩ : syracuseStep 4736693 = 444065) (by norm_num)
theorem B1943257 : Blo 1727064 1943257 := bbase (se 2 (by rfl) ⟨728721, by rfl⟩ : syracuseStep 1943257 = 1457443) (by norm_num)
theorem B1844957 : Blo 1727064 1844957 := bbase (se 3 (by rfl) ⟨345929, by rfl⟩ : syracuseStep 1844957 = 691859) (by norm_num)
theorem B1943293 : Blo 1727064 1943293 := bbase (se 3 (by rfl) ⟨364367, by rfl⟩ : syracuseStep 1943293 = 728735) (by norm_num)
theorem B2459413 : Blo 1727064 2459413 := bbase (se 6 (by rfl) ⟨57642, by rfl⟩ : syracuseStep 2459413 = 115285) (by norm_num)
theorem B1943329 : Blo 1727064 1943329 := bbase (se 2 (by rfl) ⟨728748, by rfl⟩ : syracuseStep 1943329 = 1457497) (by norm_num)
theorem B1943365 : Blo 1727064 1943365 := bbase (se 4 (by rfl) ⟨182190, by rfl⟩ : syracuseStep 1943365 = 364381) (by norm_num)
theorem B4376389 : Blo 1727064 4376389 := bbase (se 4 (by rfl) ⟨410286, by rfl⟩ : syracuseStep 4376389 = 820573) (by norm_num)
theorem B1943401 : Blo 1727064 1943401 := bbase (se 2 (by rfl) ⟨728775, by rfl⟩ : syracuseStep 1943401 = 1457551) (by norm_num)
theorem B2131849 : Blo 1727064 2131849 := bbase (se 2 (by rfl) ⟨799443, by rfl⟩ : syracuseStep 2131849 = 1598887) (by norm_num)
theorem B1943437 : Blo 1727064 1943437 := bbase (se 3 (by rfl) ⟨364394, by rfl⟩ : syracuseStep 1943437 = 728789) (by norm_num)
theorem B3114893 : Blo 1727064 3114893 := bbase (se 3 (by rfl) ⟨584042, by rfl⟩ : syracuseStep 3114893 = 1168085) (by norm_num)
theorem B2590613 : Blo 1727064 2590613 := bbase (se 6 (by rfl) ⟨60717, by rfl⟩ : syracuseStep 2590613 = 121435) (by norm_num)
theorem B5834645 : Blo 1727064 5834645 := bbase (se 6 (by rfl) ⟨136749, by rfl⟩ : syracuseStep 5834645 = 273499) (by norm_num)
theorem B2590637 : Blo 1727064 2590637 := bbase (se 3 (by rfl) ⟨485744, by rfl⟩ : syracuseStep 2590637 = 971489) (by norm_num)
theorem B1943473 : Blo 1727064 1943473 := bbase (se 2 (by rfl) ⟨728802, by rfl⟩ : syracuseStep 1943473 = 1457605) (by norm_num)
theorem B4376501 : Blo 1727064 4376501 := bbase (se 5 (by rfl) ⟨205148, by rfl⟩ : syracuseStep 4376501 = 410297) (by norm_num)
theorem B2590661 : Blo 1727064 2590661 := bbase (se 4 (by rfl) ⟨242874, by rfl⟩ : syracuseStep 2590661 = 485749) (by norm_num)
theorem B1943509 : Blo 1727064 1943509 := bbase (se 7 (by rfl) ⟨22775, by rfl⟩ : syracuseStep 1943509 = 45551) (by norm_num)
theorem B2590685 : Blo 1727064 2590685 := bbase (se 3 (by rfl) ⟨485753, by rfl⟩ : syracuseStep 2590685 = 971507) (by norm_num)
theorem B6227941 : Blo 1727064 6227941 := bbase (se 4 (by rfl) ⟨583869, by rfl⟩ : syracuseStep 6227941 = 1167739) (by norm_num)
theorem B8751077 : Blo 1727064 8751077 := bbase (se 4 (by rfl) ⟨820413, by rfl⟩ : syracuseStep 8751077 = 1640827) (by norm_num)
theorem B2590709 : Blo 1727064 2590709 := bbase (se 5 (by rfl) ⟨121439, by rfl⟩ : syracuseStep 2590709 = 242879) (by norm_num)
theorem B1943545 : Blo 1727064 1943545 := bbase (se 2 (by rfl) ⟨728829, by rfl⟩ : syracuseStep 1943545 = 1457659) (by norm_num)
theorem B2590733 : Blo 1727064 2590733 := bbase (se 3 (by rfl) ⟨485762, by rfl⟩ : syracuseStep 2590733 = 971525) (by norm_num)
theorem B1943581 : Blo 1727064 1943581 := bbase (se 3 (by rfl) ⟨364421, by rfl⟩ : syracuseStep 1943581 = 728843) (by norm_num)
theorem B2336797 : Blo 1727064 2336797 := bbase (se 3 (by rfl) ⟨438149, by rfl⟩ : syracuseStep 2336797 = 876299) (by norm_num)
theorem B2590757 : Blo 1727064 2590757 := bbase (se 4 (by rfl) ⟨242883, by rfl⟩ : syracuseStep 2590757 = 485767) (by norm_num)
theorem B2590781 : Blo 1727064 2590781 := bbase (se 3 (by rfl) ⟨485771, by rfl⟩ : syracuseStep 2590781 = 971543) (by norm_num)
theorem B1943617 : Blo 1727064 1943617 := bbase (se 2 (by rfl) ⟨728856, by rfl⟩ : syracuseStep 1943617 = 1457713) (by norm_num)
theorem B2590805 : Blo 1727064 2590805 := bbase (se 8 (by rfl) ⟨15180, by rfl⟩ : syracuseStep 2590805 = 30361) (by norm_num)
theorem B4434005 : Blo 1727064 4434005 := bbase (se 8 (by rfl) ⟨25980, by rfl⟩ : syracuseStep 4434005 = 51961) (by norm_num)
theorem B136554581 : Blo 1727064 136554581 := bbase (se 8 (by rfl) ⟨800124, by rfl⟩ : syracuseStep 136554581 = 1600249) (by norm_num)
theorem B2459749 : Blo 1727064 2459749 := bbase (se 4 (by rfl) ⟨230601, by rfl⟩ : syracuseStep 2459749 = 461203) (by norm_num)
theorem B1943653 : Blo 1727064 1943653 := bbase (se 4 (by rfl) ⟨182217, by rfl⟩ : syracuseStep 1943653 = 364435) (by norm_num)
theorem B2590829 : Blo 1727064 2590829 := bbase (se 3 (by rfl) ⟨485780, by rfl⟩ : syracuseStep 2590829 = 971561) (by norm_num)
theorem B4376693 : Blo 1727064 4376693 := bbase (se 5 (by rfl) ⟨205157, by rfl⟩ : syracuseStep 4376693 = 410315) (by norm_num)
theorem B3688573 : Blo 1727064 3688573 := bbase (se 3 (by rfl) ⟨691607, by rfl⟩ : syracuseStep 3688573 = 1383215) (by norm_num)
theorem B3278981 : Blo 1727064 3278981 := bbase (se 4 (by rfl) ⟨307404, by rfl⟩ : syracuseStep 3278981 = 614809) (by norm_num)
theorem B2590853 : Blo 1727064 2590853 := bbase (se 4 (by rfl) ⟨242892, by rfl⟩ : syracuseStep 2590853 = 485785) (by norm_num)
theorem B1943689 : Blo 1727064 1943689 := bbase (se 2 (by rfl) ⟨728883, by rfl⟩ : syracuseStep 1943689 = 1457767) (by norm_num)
theorem B4671637 : Blo 1727064 4671637 := bbase (se 6 (by rfl) ⟨109491, by rfl⟩ : syracuseStep 4671637 = 218983) (by norm_num)
theorem B1845401 : Blo 1727064 1845401 := bbase (se 2 (by rfl) ⟨692025, by rfl⟩ : syracuseStep 1845401 = 1384051) (by norm_num)
theorem B2590877 : Blo 1727064 2590877 := bbase (se 3 (by rfl) ⟨485789, by rfl⟩ : syracuseStep 2590877 = 971579) (by norm_num)
theorem B1943725 : Blo 1727064 1943725 := bbase (se 3 (by rfl) ⟨364448, by rfl⟩ : syracuseStep 1943725 = 728897) (by norm_num)
theorem B2590901 : Blo 1727064 2590901 := bbase (se 5 (by rfl) ⟨121448, by rfl⟩ : syracuseStep 2590901 = 242897) (by norm_num)
theorem B6564037 : Blo 1727064 6564037 := bbase (se 4 (by rfl) ⟨615378, by rfl⟩ : syracuseStep 6564037 = 1230757) (by norm_num)
theorem B2590925 : Blo 1727064 2590925 := bbase (se 3 (by rfl) ⟨485798, by rfl⟩ : syracuseStep 2590925 = 971597) (by norm_num)
theorem B1943761 : Blo 1727064 1943761 := bbase (se 2 (by rfl) ⟨728910, by rfl⟩ : syracuseStep 1943761 = 1457821) (by norm_num)
theorem B2074837 : Blo 1727064 2074837 := bbase (se 7 (by rfl) ⟨24314, by rfl⟩ : syracuseStep 2074837 = 48629) (by norm_num)
theorem B1845461 : Blo 1727064 1845461 := bbase (se 7 (by rfl) ⟨21626, by rfl⟩ : syracuseStep 1845461 = 43253) (by norm_num)
theorem B44902613 : Blo 1727064 44902613 := bbase (se 7 (by rfl) ⟨526202, by rfl⟩ : syracuseStep 44902613 = 1052405) (by norm_num)
theorem B2590949 : Blo 1727064 2590949 := bbase (se 4 (by rfl) ⟨242901, by rfl⟩ : syracuseStep 2590949 = 485803) (by norm_num)
theorem B2074865 : Blo 1727064 2074865 := bbase (se 2 (by rfl) ⟨778074, by rfl⟩ : syracuseStep 2074865 = 1556149) (by norm_num)
theorem B1943797 : Blo 1727064 1943797 := bbase (se 5 (by rfl) ⟨91115, by rfl⟩ : syracuseStep 1943797 = 182231) (by norm_num)
theorem B2590973 : Blo 1727064 2590973 := bbase (se 3 (by rfl) ⟨485807, by rfl⟩ : syracuseStep 2590973 = 971615) (by norm_num)
theorem B2590997 : Blo 1727064 2590997 := bbase (se 6 (by rfl) ⟨60726, by rfl⟩ : syracuseStep 2590997 = 121453) (by norm_num)
theorem B1943833 : Blo 1727064 1943833 := bbase (se 2 (by rfl) ⟨728937, by rfl⟩ : syracuseStep 1943833 = 1457875) (by norm_num)
theorem B3279133 : Blo 1727064 3279133 := bbase (se 3 (by rfl) ⟨614837, by rfl⟩ : syracuseStep 3279133 = 1229675) (by norm_num)
theorem B2591021 : Blo 1727064 2591021 := bbase (se 3 (by rfl) ⟨485816, by rfl⟩ : syracuseStep 2591021 = 971633) (by norm_num)
theorem B2459965 : Blo 1727064 2459965 := bbase (se 3 (by rfl) ⟨461243, by rfl⟩ : syracuseStep 2459965 = 922487) (by norm_num)
theorem B1943869 : Blo 1727064 1943869 := bbase (se 3 (by rfl) ⟨364475, by rfl⟩ : syracuseStep 1943869 = 728951) (by norm_num)
theorem B2591045 : Blo 1727064 2591045 := bbase (se 4 (by rfl) ⟨242910, by rfl⟩ : syracuseStep 2591045 = 485821) (by norm_num)
theorem B5835077 : Blo 1727064 5835077 := bbase (se 4 (by rfl) ⟨547038, by rfl⟩ : syracuseStep 5835077 = 1094077) (by norm_num)
theorem B1845589 : Blo 1727064 1845589 := bbase (se 10 (by rfl) ⟨2703, by rfl⟩ : syracuseStep 1845589 = 5407) (by norm_num)
theorem B2591069 : Blo 1727064 2591069 := bbase (se 3 (by rfl) ⟨485825, by rfl⟩ : syracuseStep 2591069 = 971651) (by norm_num)
theorem B1943905 : Blo 1727064 1943905 := bbase (se 2 (by rfl) ⟨728964, by rfl⟩ : syracuseStep 1943905 = 1457929) (by norm_num)
theorem B2591093 : Blo 1727064 2591093 := bbase (se 5 (by rfl) ⟨121457, by rfl⟩ : syracuseStep 2591093 = 242915) (by norm_num)
theorem B8743301 : Blo 1727064 8743301 := bbase (se 4 (by rfl) ⟨819684, by rfl⟩ : syracuseStep 8743301 = 1639369) (by norm_num)
theorem B1943941 : Blo 1727064 1943941 := bbase (se 4 (by rfl) ⟨182244, by rfl⟩ : syracuseStep 1943941 = 364489) (by norm_num)
theorem B2591117 : Blo 1727064 2591117 := bbase (se 3 (by rfl) ⟨485834, by rfl⟩ : syracuseStep 2591117 = 971669) (by norm_num)
theorem B2591141 : Blo 1727064 2591141 := bbase (se 4 (by rfl) ⟨242919, by rfl⟩ : syracuseStep 2591141 = 485839) (by norm_num)
theorem B6228389 : Blo 1727064 6228389 := bbase (se 4 (by rfl) ⟨583911, by rfl⟩ : syracuseStep 6228389 = 1167823) (by norm_num)
theorem B1943977 : Blo 1727064 1943977 := bbase (se 2 (by rfl) ⟨728991, by rfl⟩ : syracuseStep 1943977 = 1457983) (by norm_num)
theorem B2591165 : Blo 1727064 2591165 := bbase (se 3 (by rfl) ⟨485843, by rfl⟩ : syracuseStep 2591165 = 971687) (by norm_num)
theorem B1944013 : Blo 1727064 1944013 := bbase (se 3 (by rfl) ⟨364502, by rfl⟩ : syracuseStep 1944013 = 729005) (by norm_num)
theorem B2591189 : Blo 1727064 2591189 := bbase (se 7 (by rfl) ⟨30365, by rfl⟩ : syracuseStep 2591189 = 60731) (by norm_num)
theorem B2591213 : Blo 1727064 2591213 := bbase (se 3 (by rfl) ⟨485852, by rfl⟩ : syracuseStep 2591213 = 971705) (by norm_num)
theorem B1944049 : Blo 1727064 1944049 := bbase (se 2 (by rfl) ⟨729018, by rfl⟩ : syracuseStep 1944049 = 1458037) (by norm_num)
theorem B6564341 : Blo 1727064 6564341 := bbase (se 5 (by rfl) ⟨307703, by rfl⟩ : syracuseStep 6564341 = 615407) (by norm_num)
theorem B2591237 : Blo 1727064 2591237 := bbase (se 4 (by rfl) ⟨242928, by rfl⟩ : syracuseStep 2591237 = 485857) (by norm_num)
theorem B1944085 : Blo 1727064 1944085 := bbase (se 6 (by rfl) ⟨45564, by rfl⟩ : syracuseStep 1944085 = 91129) (by norm_num)
theorem B2591261 : Blo 1727064 2591261 := bbase (se 3 (by rfl) ⟨485861, by rfl⟩ : syracuseStep 2591261 = 971723) (by norm_num)
theorem B6228517 : Blo 1727064 6228517 := bbase (se 4 (by rfl) ⟨583923, by rfl⟩ : syracuseStep 6228517 = 1167847) (by norm_num)
theorem B2591285 : Blo 1727064 2591285 := bbase (se 5 (by rfl) ⟨121466, by rfl⟩ : syracuseStep 2591285 = 242933) (by norm_num)
theorem B1944121 : Blo 1727064 1944121 := bbase (se 2 (by rfl) ⟨729045, by rfl⟩ : syracuseStep 1944121 = 1458091) (by norm_num)
theorem B3279437 : Blo 1727064 3279437 := bbase (se 3 (by rfl) ⟨614894, by rfl⟩ : syracuseStep 3279437 = 1229789) (by norm_num)
theorem B2591309 : Blo 1727064 2591309 := bbase (se 3 (by rfl) ⟨485870, by rfl⟩ : syracuseStep 2591309 = 971741) (by norm_num)
theorem B1944157 : Blo 1727064 1944157 := bbase (se 3 (by rfl) ⟨364529, by rfl⟩ : syracuseStep 1944157 = 729059) (by norm_num)
theorem B2591333 : Blo 1727064 2591333 := bbase (se 4 (by rfl) ⟨242937, by rfl⟩ : syracuseStep 2591333 = 485875) (by norm_num)
theorem B3689077 : Blo 1727064 3689077 := bbase (se 5 (by rfl) ⟨172925, by rfl⟩ : syracuseStep 3689077 = 345851) (by norm_num)
theorem B2591357 : Blo 1727064 2591357 := bbase (se 3 (by rfl) ⟨485879, by rfl⟩ : syracuseStep 2591357 = 971759) (by norm_num)
theorem B1944193 : Blo 1727064 1944193 := bbase (se 2 (by rfl) ⟨729072, by rfl⟩ : syracuseStep 1944193 = 1458145) (by norm_num)
theorem B2591381 : Blo 1727064 2591381 := bbase (se 6 (by rfl) ⟨60735, by rfl⟩ : syracuseStep 2591381 = 121471) (by norm_num)
theorem B1870489 : Blo 1727064 1870489 := bbase (se 2 (by rfl) ⟨701433, by rfl⟩ : syracuseStep 1870489 = 1402867) (by norm_num)
theorem B1944229 : Blo 1727064 1944229 := bbase (se 4 (by rfl) ⟨182271, by rfl⟩ : syracuseStep 1944229 = 364543) (by norm_num)
theorem B2591405 : Blo 1727064 2591405 := bbase (se 3 (by rfl) ⟨485888, by rfl⟩ : syracuseStep 2591405 = 971777) (by norm_num)
theorem B2460341 : Blo 1727064 2460341 := bbase (se 5 (by rfl) ⟨115328, by rfl⟩ : syracuseStep 2460341 = 230657) (by norm_num)
theorem B2591429 : Blo 1727064 2591429 := bbase (se 4 (by rfl) ⟨242946, by rfl⟩ : syracuseStep 2591429 = 485893) (by norm_num)
theorem B1944265 : Blo 1727064 1944265 := bbase (se 2 (by rfl) ⟨729099, by rfl⟩ : syracuseStep 1944265 = 1458199) (by norm_num)
theorem B2591453 : Blo 1727064 2591453 := bbase (se 3 (by rfl) ⟨485897, by rfl⟩ : syracuseStep 2591453 = 971795) (by norm_num)
theorem B2075365 : Blo 1727064 2075365 := bbase (se 4 (by rfl) ⟨194565, by rfl⟩ : syracuseStep 2075365 = 389131) (by norm_num)
theorem B1944301 : Blo 1727064 1944301 := bbase (se 3 (by rfl) ⟨364556, by rfl⟩ : syracuseStep 1944301 = 729113) (by norm_num)
theorem B2591477 : Blo 1727064 2591477 := bbase (se 5 (by rfl) ⟨121475, by rfl⟩ : syracuseStep 2591477 = 242951) (by norm_num)
theorem B5835509 : Blo 1727064 5835509 := bbase (se 5 (by rfl) ⟨273539, by rfl⟩ : syracuseStep 5835509 = 547079) (by norm_num)
theorem B2591501 : Blo 1727064 2591501 := bbase (se 3 (by rfl) ⟨485906, by rfl⟩ : syracuseStep 2591501 = 971813) (by norm_num)
theorem B1944337 : Blo 1727064 1944337 := bbase (se 2 (by rfl) ⟨729126, by rfl⟩ : syracuseStep 1944337 = 1458253) (by norm_num)
theorem B1846033 : Blo 1727064 1846033 := bbase (se 2 (by rfl) ⟨692262, by rfl⟩ : syracuseStep 1846033 = 1384525) (by norm_num)
theorem B10504981 : Blo 1727064 10504981 := bbase (se 6 (by rfl) ⟨246210, by rfl⟩ : syracuseStep 10504981 = 492421) (by norm_num)
theorem B11070229 : Blo 1727064 11070229 := bbase (se 6 (by rfl) ⟨259458, by rfl⟩ : syracuseStep 11070229 = 518917) (by norm_num)
theorem B2591525 : Blo 1727064 2591525 := bbase (se 4 (by rfl) ⟨242955, by rfl⟩ : syracuseStep 2591525 = 485911) (by norm_num)
theorem B1944373 : Blo 1727064 1944373 := bbase (se 5 (by rfl) ⟨91142, by rfl⟩ : syracuseStep 1944373 = 182285) (by norm_num)
theorem B2591549 : Blo 1727064 2591549 := bbase (se 3 (by rfl) ⟨485915, by rfl⟩ : syracuseStep 2591549 = 971831) (by norm_num)
theorem B2591573 : Blo 1727064 2591573 := bbase (se 9 (by rfl) ⟨7592, by rfl⟩ : syracuseStep 2591573 = 15185) (by norm_num)
theorem B1944409 : Blo 1727064 1944409 := bbase (se 2 (by rfl) ⟨729153, by rfl⟩ : syracuseStep 1944409 = 1458307) (by norm_num)
theorem B2591597 : Blo 1727064 2591597 := bbase (se 3 (by rfl) ⟨485924, by rfl⟩ : syracuseStep 2591597 = 971849) (by norm_num)
theorem B1944445 : Blo 1727064 1944445 := bbase (se 3 (by rfl) ⟨364583, by rfl⟩ : syracuseStep 1944445 = 729167) (by norm_num)
theorem B5909381 : Blo 1727064 5909381 := bbase (se 4 (by rfl) ⟨554004, by rfl⟩ : syracuseStep 5909381 = 1108009) (by norm_num)
theorem B2591621 : Blo 1727064 2591621 := bbase (se 4 (by rfl) ⟨242964, by rfl⟩ : syracuseStep 2591621 = 485929) (by norm_num)
theorem B1846153 : Blo 1727064 1846153 := bbase (se 2 (by rfl) ⟨692307, by rfl⟩ : syracuseStep 1846153 = 1384615) (by norm_num)
theorem B3885965 : Blo 1727064 3885965 := bbase (se 3 (by rfl) ⟨728618, by rfl⟩ : syracuseStep 3885965 = 1457237) (by norm_num)
theorem B14396309 : Blo 1727064 14396309 := bbase (se 6 (by rfl) ⟨337413, by rfl⟩ : syracuseStep 14396309 = 674827) (by norm_num)
theorem B2591645 : Blo 1727064 2591645 := bbase (se 3 (by rfl) ⟨485933, by rfl⟩ : syracuseStep 2591645 = 971867) (by norm_num)
theorem B1944481 : Blo 1727064 1944481 := bbase (se 2 (by rfl) ⟨729180, by rfl⟩ : syracuseStep 1944481 = 1458361) (by norm_num)
theorem B2591669 : Blo 1727064 2591669 := bbase (se 5 (by rfl) ⟨121484, by rfl⟩ : syracuseStep 2591669 = 242969) (by norm_num)
theorem B1944517 : Blo 1727064 1944517 := bbase (se 4 (by rfl) ⟨182298, by rfl⟩ : syracuseStep 1944517 = 364597) (by norm_num)
theorem B2591693 : Blo 1727064 2591693 := bbase (se 3 (by rfl) ⟨485942, by rfl⟩ : syracuseStep 2591693 = 971885) (by norm_num)
theorem B3886037 : Blo 1727064 3886037 := bbase (se 7 (by rfl) ⟨45539, by rfl⟩ : syracuseStep 3886037 = 91079) (by norm_num)
theorem B2591717 : Blo 1727064 2591717 := bbase (se 4 (by rfl) ⟨242973, by rfl⟩ : syracuseStep 2591717 = 485947) (by norm_num)
theorem B1944553 : Blo 1727064 1944553 := bbase (se 2 (by rfl) ⟨729207, by rfl⟩ : syracuseStep 1944553 = 1458415) (by norm_num)
theorem B2591741 : Blo 1727064 2591741 := bbase (se 3 (by rfl) ⟨485951, by rfl⟩ : syracuseStep 2591741 = 971903) (by norm_num)
theorem B1944589 : Blo 1727064 1944589 := bbase (se 3 (by rfl) ⟨364610, by rfl⟩ : syracuseStep 1944589 = 729221) (by norm_num)
theorem B2591765 : Blo 1727064 2591765 := bbase (se 6 (by rfl) ⟨60744, by rfl⟩ : syracuseStep 2591765 = 121489) (by norm_num)
theorem B3886109 : Blo 1727064 3886109 := bbase (se 3 (by rfl) ⟨728645, by rfl⟩ : syracuseStep 3886109 = 1457291) (by norm_num)
theorem B2591789 : Blo 1727064 2591789 := bbase (se 3 (by rfl) ⟨485960, by rfl⟩ : syracuseStep 2591789 = 971921) (by norm_num)
theorem B1944625 : Blo 1727064 1944625 := bbase (se 2 (by rfl) ⟨729234, by rfl⟩ : syracuseStep 1944625 = 1458469) (by norm_num)
theorem B2591813 : Blo 1727064 2591813 := bbase (se 4 (by rfl) ⟨242982, by rfl⟩ : syracuseStep 2591813 = 485965) (by norm_num)
theorem B1944661 : Blo 1727064 1944661 := bbase (se 8 (by rfl) ⟨11394, by rfl⟩ : syracuseStep 1944661 = 22789) (by norm_num)
theorem B2591837 : Blo 1727064 2591837 := bbase (se 3 (by rfl) ⟨485969, by rfl⟩ : syracuseStep 2591837 = 971939) (by norm_num)
theorem B3886181 : Blo 1727064 3886181 := bbase (se 4 (by rfl) ⟨364329, by rfl⟩ : syracuseStep 3886181 = 728659) (by norm_num)
theorem B2591861 : Blo 1727064 2591861 := bbase (se 5 (by rfl) ⟨121493, by rfl⟩ : syracuseStep 2591861 = 242987) (by norm_num)
theorem B1944697 : Blo 1727064 1944697 := bbase (se 2 (by rfl) ⟨729261, by rfl⟩ : syracuseStep 1944697 = 1458523) (by norm_num)
theorem B1846405 : Blo 1727064 1846405 := bbase (se 4 (by rfl) ⟨173100, by rfl⟩ : syracuseStep 1846405 = 346201) (by norm_num)
theorem B1846409 : Blo 1727064 1846409 := bbase (se 2 (by rfl) ⟨692403, by rfl⟩ : syracuseStep 1846409 = 1384807) (by norm_num)
theorem B2591885 : Blo 1727064 2591885 := bbase (se 3 (by rfl) ⟨485978, by rfl⟩ : syracuseStep 2591885 = 971957) (by norm_num)
theorem B1944733 : Blo 1727064 1944733 := bbase (se 3 (by rfl) ⟨364637, by rfl⟩ : syracuseStep 1944733 = 729275) (by norm_num)
theorem B2591909 : Blo 1727064 2591909 := bbase (se 4 (by rfl) ⟨242991, by rfl⟩ : syracuseStep 2591909 = 485983) (by norm_num)
theorem B3886253 : Blo 1727064 3886253 := bbase (se 3 (by rfl) ⟨728672, by rfl⟩ : syracuseStep 3886253 = 1457345) (by norm_num)
theorem B2591933 : Blo 1727064 2591933 := bbase (se 3 (by rfl) ⟨485987, by rfl⟩ : syracuseStep 2591933 = 971975) (by norm_num)
theorem B1944769 : Blo 1727064 1944769 := bbase (se 2 (by rfl) ⟨729288, by rfl⟩ : syracuseStep 1944769 = 1458577) (by norm_num)
theorem B2591957 : Blo 1727064 2591957 := bbase (se 7 (by rfl) ⟨30374, by rfl⟩ : syracuseStep 2591957 = 60749) (by norm_num)
theorem B1944805 : Blo 1727064 1944805 := bbase (se 4 (by rfl) ⟨182325, by rfl⟩ : syracuseStep 1944805 = 364651) (by norm_num)
theorem B2591981 : Blo 1727064 2591981 := bbase (se 3 (by rfl) ⟨485996, by rfl⟩ : syracuseStep 2591981 = 971993) (by norm_num)
theorem B3886325 : Blo 1727064 3886325 := bbase (se 5 (by rfl) ⟨182171, by rfl⟩ : syracuseStep 3886325 = 364343) (by norm_num)
theorem B8752373 : Blo 1727064 8752373 := bbase (se 5 (by rfl) ⟨410267, by rfl⟩ : syracuseStep 8752373 = 820535) (by norm_num)
theorem B2592005 : Blo 1727064 2592005 := bbase (se 4 (by rfl) ⟨243000, by rfl⟩ : syracuseStep 2592005 = 486001) (by norm_num)
theorem B1944841 : Blo 1727064 1944841 := bbase (se 2 (by rfl) ⟨729315, by rfl⟩ : syracuseStep 1944841 = 1458631) (by norm_num)
theorem B8301845 : Blo 1727064 8301845 := bbase (se 6 (by rfl) ⟨194574, by rfl⟩ : syracuseStep 8301845 = 389149) (by norm_num)
theorem B2592029 : Blo 1727064 2592029 := bbase (se 3 (by rfl) ⟨486005, by rfl⟩ : syracuseStep 2592029 = 972011) (by norm_num)
theorem B1944877 : Blo 1727064 1944877 := bbase (se 3 (by rfl) ⟨364664, by rfl⟩ : syracuseStep 1944877 = 729329) (by norm_num)
theorem B2592053 : Blo 1727064 2592053 := bbase (se 5 (by rfl) ⟨121502, by rfl⟩ : syracuseStep 2592053 = 243005) (by norm_num)
theorem B3886397 : Blo 1727064 3886397 := bbase (se 3 (by rfl) ⟨728699, by rfl⟩ : syracuseStep 3886397 = 1457399) (by norm_num)
theorem B3280189 : Blo 1727064 3280189 := bbase (se 3 (by rfl) ⟨615035, by rfl⟩ : syracuseStep 3280189 = 1230071) (by norm_num)
theorem B2592077 : Blo 1727064 2592077 := bbase (se 3 (by rfl) ⟨486014, by rfl⟩ : syracuseStep 2592077 = 972029) (by norm_num)
theorem B1944913 : Blo 1727064 1944913 := bbase (se 2 (by rfl) ⟨729342, by rfl⟩ : syracuseStep 1944913 = 1458685) (by norm_num)
theorem B2592101 : Blo 1727064 2592101 := bbase (se 4 (by rfl) ⟨243009, by rfl⟩ : syracuseStep 2592101 = 486019) (by norm_num)
theorem B1944949 : Blo 1727064 1944949 := bbase (se 5 (by rfl) ⟨91169, by rfl⟩ : syracuseStep 1944949 = 182339) (by norm_num)
theorem B2592125 : Blo 1727064 2592125 := bbase (se 3 (by rfl) ⟨486023, by rfl⟩ : syracuseStep 2592125 = 972047) (by norm_num)
theorem B3886469 : Blo 1727064 3886469 := bbase (se 4 (by rfl) ⟨364356, by rfl⟩ : syracuseStep 3886469 = 728713) (by norm_num)
theorem B2592149 : Blo 1727064 2592149 := bbase (se 6 (by rfl) ⟨60753, by rfl⟩ : syracuseStep 2592149 = 121507) (by norm_num)
theorem B1944985 : Blo 1727064 1944985 := bbase (se 2 (by rfl) ⟨729369, by rfl⟩ : syracuseStep 1944985 = 1458739) (by norm_num)
theorem B2592173 : Blo 1727064 2592173 := bbase (se 3 (by rfl) ⟨486032, by rfl⟩ : syracuseStep 2592173 = 972065) (by norm_num)
theorem B14011829 : Blo 1727064 14011829 := bbase (se 5 (by rfl) ⟨656804, by rfl⟩ : syracuseStep 14011829 = 1313609) (by norm_num)
theorem B1945021 : Blo 1727064 1945021 := bbase (se 3 (by rfl) ⟨364691, by rfl⟩ : syracuseStep 1945021 = 729383) (by norm_num)
theorem B2592197 : Blo 1727064 2592197 := bbase (se 4 (by rfl) ⟨243018, by rfl⟩ : syracuseStep 2592197 = 486037) (by norm_num)
theorem B3886541 : Blo 1727064 3886541 := bbase (se 3 (by rfl) ⟨728726, by rfl⟩ : syracuseStep 3886541 = 1457453) (by norm_num)
theorem B3280333 : Blo 1727064 3280333 := bbase (se 3 (by rfl) ⟨615062, by rfl⟩ : syracuseStep 3280333 = 1230125) (by norm_num)
theorem B2592221 : Blo 1727064 2592221 := bbase (se 3 (by rfl) ⟨486041, by rfl⟩ : syracuseStep 2592221 = 972083) (by norm_num)
theorem B1945057 : Blo 1727064 1945057 := bbase (se 2 (by rfl) ⟨729396, by rfl⟩ : syracuseStep 1945057 = 1458793) (by norm_num)
theorem B3689965 : Blo 1727064 3689965 := bbase (se 3 (by rfl) ⟨691868, by rfl⟩ : syracuseStep 3689965 = 1383737) (by norm_num)
theorem B2592245 : Blo 1727064 2592245 := bbase (se 5 (by rfl) ⟨121511, by rfl⟩ : syracuseStep 2592245 = 243023) (by norm_num)
theorem B1945093 : Blo 1727064 1945093 := bbase (se 4 (by rfl) ⟨182352, by rfl⟩ : syracuseStep 1945093 = 364705) (by norm_num)
theorem B2592269 : Blo 1727064 2592269 := bbase (se 3 (by rfl) ⟨486050, by rfl⟩ : syracuseStep 2592269 = 972101) (by norm_num)
theorem B3501589 : Blo 1727064 3501589 := bbase (se 6 (by rfl) ⟨82068, by rfl⟩ : syracuseStep 3501589 = 164137) (by norm_num)
theorem B3886613 : Blo 1727064 3886613 := bbase (se 6 (by rfl) ⟨91092, by rfl⟩ : syracuseStep 3886613 = 182185) (by norm_num)
theorem B9473557 : Blo 1727064 9473557 := bbase (se 6 (by rfl) ⟨222036, by rfl⟩ : syracuseStep 9473557 = 444073) (by norm_num)
theorem B2592293 : Blo 1727064 2592293 := bbase (se 4 (by rfl) ⟨243027, by rfl⟩ : syracuseStep 2592293 = 486055) (by norm_num)
theorem B1945129 : Blo 1727064 1945129 := bbase (se 2 (by rfl) ⟨729423, by rfl⟩ : syracuseStep 1945129 = 1458847) (by norm_num)
theorem B15773237 : Blo 1727064 15773237 := bbase (se 5 (by rfl) ⟨739370, by rfl⟩ : syracuseStep 15773237 = 1478741) (by norm_num)
theorem B2494013 : Blo 1727064 2494013 := bbase (se 3 (by rfl) ⟨467627, by rfl⟩ : syracuseStep 2494013 = 935255) (by norm_num)
theorem B2592317 : Blo 1727064 2592317 := bbase (se 3 (by rfl) ⟨486059, by rfl⟩ : syracuseStep 2592317 = 972119) (by norm_num)
theorem B1945165 : Blo 1727064 1945165 := bbase (se 3 (by rfl) ⟨364718, by rfl⟩ : syracuseStep 1945165 = 729437) (by norm_num)
theorem B2592341 : Blo 1727064 2592341 := bbase (se 8 (by rfl) ⟨15189, by rfl⟩ : syracuseStep 2592341 = 30379) (by norm_num)
theorem B3886685 : Blo 1727064 3886685 := bbase (se 3 (by rfl) ⟨728753, by rfl⟩ : syracuseStep 3886685 = 1457507) (by norm_num)
theorem B3280493 : Blo 1727064 3280493 := bbase (se 3 (by rfl) ⟨615092, by rfl⟩ : syracuseStep 3280493 = 1230185) (by norm_num)
theorem B2592365 : Blo 1727064 2592365 := bbase (se 3 (by rfl) ⟨486068, by rfl⟩ : syracuseStep 2592365 = 972137) (by norm_num)
theorem B4673141 : Blo 1727064 4673141 := bbase (se 5 (by rfl) ⟨219053, by rfl⟩ : syracuseStep 4673141 = 438107) (by norm_num)
theorem B2592389 : Blo 1727064 2592389 := bbase (se 4 (by rfl) ⟨243036, by rfl⟩ : syracuseStep 2592389 = 486073) (by norm_num)
theorem B8744597 : Blo 1727064 8744597 := bbase (se 6 (by rfl) ⟨204951, by rfl⟩ : syracuseStep 8744597 = 409903) (by norm_num)
theorem B8302229 : Blo 1727064 8302229 := bbase (se 6 (by rfl) ⟨194583, by rfl⟩ : syracuseStep 8302229 = 389167) (by norm_num)
theorem B2592413 : Blo 1727064 2592413 := bbase (se 3 (by rfl) ⟨486077, by rfl⟩ : syracuseStep 2592413 = 972155) (by norm_num)
theorem B3886757 : Blo 1727064 3886757 := bbase (se 4 (by rfl) ⟨364383, by rfl⟩ : syracuseStep 3886757 = 728767) (by norm_num)
theorem B2592437 : Blo 1727064 2592437 := bbase (se 5 (by rfl) ⟨121520, by rfl⟩ : syracuseStep 2592437 = 243041) (by norm_num)
theorem B2592461 : Blo 1727064 2592461 := bbase (se 3 (by rfl) ⟨486086, by rfl⟩ : syracuseStep 2592461 = 972173) (by norm_num)
theorem B2592485 : Blo 1727064 2592485 := bbase (se 4 (by rfl) ⟨243045, by rfl⟩ : syracuseStep 2592485 = 486091) (by norm_num)
theorem B3886829 : Blo 1727064 3886829 := bbase (se 3 (by rfl) ⟨728780, by rfl⟩ : syracuseStep 3886829 = 1457561) (by norm_num)
theorem B3280637 : Blo 1727064 3280637 := bbase (se 3 (by rfl) ⟨615119, by rfl⟩ : syracuseStep 3280637 = 1230239) (by norm_num)
theorem B2592509 : Blo 1727064 2592509 := bbase (se 3 (by rfl) ⟨486095, by rfl⟩ : syracuseStep 2592509 = 972191) (by norm_num)
theorem B2592533 : Blo 1727064 2592533 := bbase (se 6 (by rfl) ⟨60762, by rfl⟩ : syracuseStep 2592533 = 121525) (by norm_num)
theorem B2592557 : Blo 1727064 2592557 := bbase (se 3 (by rfl) ⟨486104, by rfl⟩ : syracuseStep 2592557 = 972209) (by norm_num)
theorem B3886901 : Blo 1727064 3886901 := bbase (se 5 (by rfl) ⟨182198, by rfl⟩ : syracuseStep 3886901 = 364397) (by norm_num)
theorem B2592581 : Blo 1727064 2592581 := bbase (se 4 (by rfl) ⟨243054, by rfl⟩ : syracuseStep 2592581 = 486109) (by norm_num)
theorem B2592605 : Blo 1727064 2592605 := bbase (se 3 (by rfl) ⟨486113, by rfl⟩ : syracuseStep 2592605 = 972227) (by norm_num)
theorem B5762917 : Blo 1727064 5762917 := bbase (se 4 (by rfl) ⟨540273, by rfl⟩ : syracuseStep 5762917 = 1080547) (by norm_num)
theorem B2592629 : Blo 1727064 2592629 := bbase (se 5 (by rfl) ⟨121529, by rfl⟩ : syracuseStep 2592629 = 243059) (by norm_num)
theorem B3886973 : Blo 1727064 3886973 := bbase (se 3 (by rfl) ⟨728807, by rfl⟩ : syracuseStep 3886973 = 1457615) (by norm_num)
theorem B2076553 : Blo 1727064 2076553 := bbase (se 2 (by rfl) ⟨778707, by rfl⟩ : syracuseStep 2076553 = 1557415) (by norm_num)
theorem B2592653 : Blo 1727064 2592653 := bbase (se 3 (by rfl) ⟨486122, by rfl⟩ : syracuseStep 2592653 = 972245) (by norm_num)
theorem B5533589 : Blo 1727064 5533589 := bbase (se 6 (by rfl) ⟨129693, by rfl⟩ : syracuseStep 5533589 = 259387) (by norm_num)
theorem B2592677 : Blo 1727064 2592677 := bbase (se 4 (by rfl) ⟨243063, by rfl⟩ : syracuseStep 2592677 = 486127) (by norm_num)
theorem B2592701 : Blo 1727064 2592701 := bbase (se 3 (by rfl) ⟨486131, by rfl⟩ : syracuseStep 2592701 = 972263) (by norm_num)
theorem B3887045 : Blo 1727064 3887045 := bbase (se 4 (by rfl) ⟨364410, by rfl⟩ : syracuseStep 3887045 = 728821) (by norm_num)
theorem B2592725 : Blo 1727064 2592725 := bbase (se 7 (by rfl) ⟨30383, by rfl⟩ : syracuseStep 2592725 = 60767) (by norm_num)
theorem B3690461 : Blo 1727064 3690461 := bbase (se 3 (by rfl) ⟨691961, by rfl⟩ : syracuseStep 3690461 = 1383923) (by norm_num)
theorem B2592749 : Blo 1727064 2592749 := bbase (se 3 (by rfl) ⟨486140, by rfl⟩ : syracuseStep 2592749 = 972281) (by norm_num)
theorem B2592773 : Blo 1727064 2592773 := bbase (se 4 (by rfl) ⟨243072, by rfl⟩ : syracuseStep 2592773 = 486145) (by norm_num)
theorem B3887117 : Blo 1727064 3887117 := bbase (se 3 (by rfl) ⟨728834, by rfl⟩ : syracuseStep 3887117 = 1457669) (by norm_num)
theorem B3502109 : Blo 1727064 3502109 := bbase (se 3 (by rfl) ⟨656645, by rfl⟩ : syracuseStep 3502109 = 1313291) (by norm_num)
theorem B3280925 : Blo 1727064 3280925 := bbase (se 3 (by rfl) ⟨615173, by rfl⟩ : syracuseStep 3280925 = 1230347) (by norm_num)
theorem B2592797 : Blo 1727064 2592797 := bbase (se 3 (by rfl) ⟨486149, by rfl⟩ : syracuseStep 2592797 = 972299) (by norm_num)
theorem B2592821 : Blo 1727064 2592821 := bbase (se 5 (by rfl) ⟨121538, by rfl⟩ : syracuseStep 2592821 = 243077) (by norm_num)
theorem B2461765 : Blo 1727064 2461765 := bbase (se 4 (by rfl) ⟨230790, by rfl⟩ : syracuseStep 2461765 = 461581) (by norm_num)
theorem B2076745 : Blo 1727064 2076745 := bbase (se 2 (by rfl) ⟨778779, by rfl⟩ : syracuseStep 2076745 = 1557559) (by norm_num)
theorem B2592845 : Blo 1727064 2592845 := bbase (se 3 (by rfl) ⟨486158, by rfl⟩ : syracuseStep 2592845 = 972317) (by norm_num)
theorem B3887189 : Blo 1727064 3887189 := bbase (se 8 (by rfl) ⟨22776, by rfl⟩ : syracuseStep 3887189 = 45553) (by norm_num)
theorem B2592869 : Blo 1727064 2592869 := bbase (se 4 (by rfl) ⟨243081, by rfl⟩ : syracuseStep 2592869 = 486163) (by norm_num)
theorem B2592893 : Blo 1727064 2592893 := bbase (se 3 (by rfl) ⟨486167, by rfl⟩ : syracuseStep 2592893 = 972335) (by norm_num)
theorem B4919429 : Blo 1727064 4919429 := bbase (se 4 (by rfl) ⟨461196, by rfl⟩ : syracuseStep 4919429 = 922393) (by norm_num)
theorem B2592917 : Blo 1727064 2592917 := bbase (se 6 (by rfl) ⟨60771, by rfl⟩ : syracuseStep 2592917 = 121543) (by norm_num)
theorem B3887261 : Blo 1727064 3887261 := bbase (se 3 (by rfl) ⟨728861, by rfl⟩ : syracuseStep 3887261 = 1457723) (by norm_num)
theorem B2592941 : Blo 1727064 2592941 := bbase (se 3 (by rfl) ⟨486176, by rfl⟩ : syracuseStep 2592941 = 972353) (by norm_num)
theorem B2076845 : Blo 1727064 2076845 := bbase (se 3 (by rfl) ⟨389408, by rfl⟩ : syracuseStep 2076845 = 778817) (by norm_num)
theorem B3281077 : Blo 1727064 3281077 := bbase (se 5 (by rfl) ⟨153800, by rfl⟩ : syracuseStep 3281077 = 307601) (by norm_num)
theorem B2592965 : Blo 1727064 2592965 := bbase (se 4 (by rfl) ⟨243090, by rfl⟩ : syracuseStep 2592965 = 486181) (by norm_num)
theorem B2592989 : Blo 1727064 2592989 := bbase (se 3 (by rfl) ⟨486185, by rfl⟩ : syracuseStep 2592989 = 972371) (by norm_num)
theorem B3887333 : Blo 1727064 3887333 := bbase (se 4 (by rfl) ⟨364437, by rfl⟩ : syracuseStep 3887333 = 728875) (by norm_num)
theorem B3502325 : Blo 1727064 3502325 := bbase (se 5 (by rfl) ⟨164171, by rfl⟩ : syracuseStep 3502325 = 328343) (by norm_num)
theorem B2593013 : Blo 1727064 2593013 := bbase (se 5 (by rfl) ⟨121547, by rfl⟩ : syracuseStep 2593013 = 243095) (by norm_num)
theorem B2593037 : Blo 1727064 2593037 := bbase (se 3 (by rfl) ⟨486194, by rfl⟩ : syracuseStep 2593037 = 972389) (by norm_num)
theorem B3502373 : Blo 1727064 3502373 := bbase (se 4 (by rfl) ⟨328347, by rfl⟩ : syracuseStep 3502373 = 656695) (by norm_num)
theorem B2593061 : Blo 1727064 2593061 := bbase (se 4 (by rfl) ⟨243099, by rfl⟩ : syracuseStep 2593061 = 486199) (by norm_num)
theorem B3887405 : Blo 1727064 3887405 := bbase (se 3 (by rfl) ⟨728888, by rfl⟩ : syracuseStep 3887405 = 1457777) (by norm_num)
theorem B2593085 : Blo 1727064 2593085 := bbase (se 3 (by rfl) ⟨486203, by rfl⟩ : syracuseStep 2593085 = 972407) (by norm_num)
theorem B2527573 : Blo 1727064 2527573 := bbase (se 10 (by rfl) ⟨3702, by rfl⟩ : syracuseStep 2527573 = 7405) (by norm_num)
theorem B2593109 : Blo 1727064 2593109 := bbase (se 10 (by rfl) ⟨3798, by rfl⟩ : syracuseStep 2593109 = 7597) (by norm_num)
theorem B2593133 : Blo 1727064 2593133 := bbase (se 3 (by rfl) ⟨486212, by rfl⟩ : syracuseStep 2593133 = 972425) (by norm_num)
theorem B3887477 : Blo 1727064 3887477 := bbase (se 5 (by rfl) ⟨182225, by rfl⟩ : syracuseStep 3887477 = 364451) (by norm_num)
theorem B2593157 : Blo 1727064 2593157 := bbase (se 4 (by rfl) ⟨243108, by rfl⟩ : syracuseStep 2593157 = 486217) (by norm_num)
theorem B2593181 : Blo 1727064 2593181 := bbase (se 3 (by rfl) ⟨486221, by rfl⟩ : syracuseStep 2593181 = 972443) (by norm_num)
theorem B5829029 : Blo 1727064 5829029 := bbase (se 4 (by rfl) ⟨546471, by rfl⟩ : syracuseStep 5829029 = 1092943) (by norm_num)
theorem B2593205 : Blo 1727064 2593205 := bbase (se 5 (by rfl) ⟨121556, by rfl⟩ : syracuseStep 2593205 = 243113) (by norm_num)
theorem B3887549 : Blo 1727064 3887549 := bbase (se 3 (by rfl) ⟨728915, by rfl⟩ : syracuseStep 3887549 = 1457831) (by norm_num)
theorem B2593229 : Blo 1727064 2593229 := bbase (se 3 (by rfl) ⟨486230, by rfl⟩ : syracuseStep 2593229 = 972461) (by norm_num)
theorem B3281381 : Blo 1727064 3281381 := bbase (se 4 (by rfl) ⟨307629, by rfl⟩ : syracuseStep 3281381 = 615259) (by norm_num)
theorem B2593253 : Blo 1727064 2593253 := bbase (se 4 (by rfl) ⟨243117, by rfl⟩ : syracuseStep 2593253 = 486235) (by norm_num)
theorem B2593277 : Blo 1727064 2593277 := bbase (se 3 (by rfl) ⟨486239, by rfl⟩ : syracuseStep 2593277 = 972479) (by norm_num)
theorem B3887621 : Blo 1727064 3887621 := bbase (se 4 (by rfl) ⟨364464, by rfl⟩ : syracuseStep 3887621 = 728929) (by norm_num)
theorem B2593301 : Blo 1727064 2593301 := bbase (se 6 (by rfl) ⟨60780, by rfl⟩ : syracuseStep 2593301 = 121561) (by norm_num)
theorem B2593325 : Blo 1727064 2593325 := bbase (se 3 (by rfl) ⟨486248, by rfl⟩ : syracuseStep 2593325 = 972497) (by norm_num)
theorem B2593349 : Blo 1727064 2593349 := bbase (se 4 (by rfl) ⟨243126, by rfl⟩ : syracuseStep 2593349 = 486253) (by norm_num)
theorem B3887693 : Blo 1727064 3887693 := bbase (se 3 (by rfl) ⟨728942, by rfl⟩ : syracuseStep 3887693 = 1457885) (by norm_num)
theorem B2593373 : Blo 1727064 2593373 := bbase (se 3 (by rfl) ⟨486257, by rfl⟩ : syracuseStep 2593373 = 972515) (by norm_num)
theorem B2593397 : Blo 1727064 2593397 := bbase (se 5 (by rfl) ⟨121565, by rfl⟩ : syracuseStep 2593397 = 243131) (by norm_num)
theorem B2593421 : Blo 1727064 2593421 := bbase (se 3 (by rfl) ⟨486266, by rfl⟩ : syracuseStep 2593421 = 972533) (by norm_num)
theorem B2216593 : Blo 1727064 2216593 := bbase (se 2 (by rfl) ⟨831222, by rfl⟩ : syracuseStep 2216593 = 1662445) (by norm_num)
theorem B3887765 : Blo 1727064 3887765 := bbase (se 6 (by rfl) ⟨91119, by rfl⟩ : syracuseStep 3887765 = 182239) (by norm_num)
theorem B2593445 : Blo 1727064 2593445 := bbase (se 4 (by rfl) ⟨243135, by rfl⟩ : syracuseStep 2593445 = 486271) (by norm_num)
theorem B2593469 : Blo 1727064 2593469 := bbase (se 3 (by rfl) ⟨486275, by rfl⟩ : syracuseStep 2593469 = 972551) (by norm_num)
theorem B2593493 : Blo 1727064 2593493 := bbase (se 7 (by rfl) ⟨30392, by rfl⟩ : syracuseStep 2593493 = 60785) (by norm_num)
theorem B3887837 : Blo 1727064 3887837 := bbase (se 3 (by rfl) ⟨728969, by rfl⟩ : syracuseStep 3887837 = 1457939) (by norm_num)
theorem B2593517 : Blo 1727064 2593517 := bbase (se 3 (by rfl) ⟨486284, by rfl⟩ : syracuseStep 2593517 = 972569) (by norm_num)
theorem B2593541 : Blo 1727064 2593541 := bbase (se 4 (by rfl) ⟨243144, by rfl⟩ : syracuseStep 2593541 = 486289) (by norm_num)
theorem B2593565 : Blo 1727064 2593565 := bbase (se 3 (by rfl) ⟨486293, by rfl⟩ : syracuseStep 2593565 = 972587) (by norm_num)
theorem B3887909 : Blo 1727064 3887909 := bbase (se 4 (by rfl) ⟨364491, by rfl⟩ : syracuseStep 3887909 = 728983) (by norm_num)
theorem B5911349 : Blo 1727064 5911349 := bbase (se 5 (by rfl) ⟨277094, by rfl⟩ : syracuseStep 5911349 = 554189) (by norm_num)
theorem B2593589 : Blo 1727064 2593589 := bbase (se 5 (by rfl) ⟨121574, by rfl⟩ : syracuseStep 2593589 = 243149) (by norm_num)
theorem B5829461 : Blo 1727064 5829461 := bbase (se 9 (by rfl) ⟨17078, by rfl⟩ : syracuseStep 5829461 = 34157) (by norm_num)
theorem B3691349 : Blo 1727064 3691349 := bbase (se 9 (by rfl) ⟨10814, by rfl⟩ : syracuseStep 3691349 = 21629) (by norm_num)
theorem B3887981 : Blo 1727064 3887981 := bbase (se 3 (by rfl) ⟨728996, by rfl⟩ : syracuseStep 3887981 = 1457993) (by norm_num)
theorem B8745893 : Blo 1727064 8745893 := bbase (se 4 (by rfl) ⟨819927, by rfl⟩ : syracuseStep 8745893 = 1639855) (by norm_num)
theorem B3888053 : Blo 1727064 3888053 := bbase (se 5 (by rfl) ⟨182252, by rfl⟩ : syracuseStep 3888053 = 364505) (by norm_num)
theorem B3691469 : Blo 1727064 3691469 := bbase (se 3 (by rfl) ⟨692150, by rfl⟩ : syracuseStep 3691469 = 1384301) (by norm_num)
theorem B6558677 : Blo 1727064 6558677 := bbase (se 7 (by rfl) ⟨76859, by rfl⟩ : syracuseStep 6558677 = 153719) (by norm_num)
theorem B11228149 : Blo 1727064 11228149 := bbase (se 5 (by rfl) ⟨526319, by rfl⟩ : syracuseStep 11228149 = 1052639) (by norm_num)
theorem B3888125 : Blo 1727064 3888125 := bbase (se 3 (by rfl) ⟨729023, by rfl⟩ : syracuseStep 3888125 = 1458047) (by norm_num)
theorem B3888197 : Blo 1727064 3888197 := bbase (se 4 (by rfl) ⟨364518, by rfl⟩ : syracuseStep 3888197 = 729037) (by norm_num)
theorem B10515541 : Blo 1727064 10515541 := bbase (se 8 (by rfl) ⟨61614, by rfl⟩ : syracuseStep 10515541 = 123229) (by norm_num)
theorem B3888269 : Blo 1727064 3888269 := bbase (se 3 (by rfl) ⟨729050, by rfl⟩ : syracuseStep 3888269 = 1458101) (by norm_num)
theorem B3888341 : Blo 1727064 3888341 := bbase (se 7 (by rfl) ⟨45566, by rfl⟩ : syracuseStep 3888341 = 91133) (by norm_num)
theorem B3282133 : Blo 1727064 3282133 := bbase (se 7 (by rfl) ⟨38462, by rfl⟩ : syracuseStep 3282133 = 76925) (by norm_num)
theorem B6558965 : Blo 1727064 6558965 := bbase (se 5 (by rfl) ⟨307451, by rfl⟩ : syracuseStep 6558965 = 614903) (by norm_num)
theorem B5829893 : Blo 1727064 5829893 := bbase (se 4 (by rfl) ⟨546552, by rfl⟩ : syracuseStep 5829893 = 1093105) (by norm_num)
theorem B3888413 : Blo 1727064 3888413 := bbase (se 3 (by rfl) ⟨729077, by rfl⟩ : syracuseStep 3888413 = 1458155) (by norm_num)
theorem B5535013 : Blo 1727064 5535013 := bbase (se 4 (by rfl) ⟨518907, by rfl⟩ : syracuseStep 5535013 = 1037815) (by norm_num)
theorem B29537621 : Blo 1727064 29537621 := bbase (se 13 (by rfl) ⟨5408, by rfl⟩ : syracuseStep 29537621 = 10817) (by norm_num)
theorem B3888485 : Blo 1727064 3888485 := bbase (se 4 (by rfl) ⟨364545, by rfl⟩ : syracuseStep 3888485 = 729091) (by norm_num)
theorem B3282277 : Blo 1727064 3282277 := bbase (se 4 (by rfl) ⟨307713, by rfl⟩ : syracuseStep 3282277 = 615427) (by norm_num)
theorem B4371853 : Blo 1727064 4371853 := bbase (se 3 (by rfl) ⟨819722, by rfl⟩ : syracuseStep 4371853 = 1639445) (by norm_num)
theorem B3888557 : Blo 1727064 3888557 := bbase (se 3 (by rfl) ⟨729104, by rfl⟩ : syracuseStep 3888557 = 1458209) (by norm_num)
theorem B2807245 : Blo 1727064 2807245 := bbase (se 3 (by rfl) ⟨526358, by rfl⟩ : syracuseStep 2807245 = 1052717) (by norm_num)
theorem B3888629 : Blo 1727064 3888629 := bbase (se 5 (by rfl) ⟨182279, by rfl⟩ : syracuseStep 3888629 = 364559) (by norm_num)
theorem B4371965 : Blo 1727064 4371965 := bbase (se 3 (by rfl) ⟨819743, by rfl⟩ : syracuseStep 4371965 = 1639487) (by norm_num)
theorem B3282437 : Blo 1727064 3282437 := bbase (se 4 (by rfl) ⟨307728, by rfl⟩ : syracuseStep 3282437 = 615457) (by norm_num)
theorem B3888701 : Blo 1727064 3888701 := bbase (se 3 (by rfl) ⟨729131, by rfl⟩ : syracuseStep 3888701 = 1458263) (by norm_num)
theorem B3692101 : Blo 1727064 3692101 := bbase (se 4 (by rfl) ⟨346134, by rfl⟩ : syracuseStep 3692101 = 692269) (by norm_num)
theorem B3888773 : Blo 1727064 3888773 := bbase (se 4 (by rfl) ⟨364572, by rfl⟩ : syracuseStep 3888773 = 729145) (by norm_num)
theorem B5830325 : Blo 1727064 5830325 := bbase (se 5 (by rfl) ⟨273296, by rfl⟩ : syracuseStep 5830325 = 546593) (by norm_num)
theorem B4921013 : Blo 1727064 4921013 := bbase (se 5 (by rfl) ⟨230672, by rfl⟩ : syracuseStep 4921013 = 461345) (by norm_num)
theorem B4372157 : Blo 1727064 4372157 := bbase (se 3 (by rfl) ⟨819779, by rfl⟩ : syracuseStep 4372157 = 1639559) (by norm_num)
theorem B3888845 : Blo 1727064 3888845 := bbase (se 3 (by rfl) ⟨729158, by rfl⟩ : syracuseStep 3888845 = 1458317) (by norm_num)
theorem B4151029 : Blo 1727064 4151029 := bbase (se 5 (by rfl) ⟨194579, by rfl⟩ : syracuseStep 4151029 = 389159) (by norm_num)
theorem B3888917 : Blo 1727064 3888917 := bbase (se 6 (by rfl) ⟨91146, by rfl⟩ : syracuseStep 3888917 = 182293) (by norm_num)
theorem B1775441 : Blo 1727064 1775441 := bbase (se 2 (by rfl) ⟨665790, by rfl⟩ : syracuseStep 1775441 = 1331581) (by norm_num)
theorem B7690069 : Blo 1727064 7690069 := bbase (se 9 (by rfl) ⟨22529, by rfl⟩ : syracuseStep 7690069 = 45059) (by norm_num)
theorem B3888989 : Blo 1727064 3888989 := bbase (se 3 (by rfl) ⟨729185, by rfl⟩ : syracuseStep 3888989 = 1458371) (by norm_num)
theorem B3889061 : Blo 1727064 3889061 := bbase (se 4 (by rfl) ⟨364599, by rfl⟩ : syracuseStep 3889061 = 729199) (by norm_num)
theorem B3889133 : Blo 1727064 3889133 := bbase (se 3 (by rfl) ⟨729212, by rfl⟩ : syracuseStep 3889133 = 1458425) (by norm_num)
theorem B1751041 : Blo 1727064 1751041 := bbase (se 2 (by rfl) ⟨656640, by rfl⟩ : syracuseStep 1751041 = 1313281) (by norm_num)
theorem B4372501 : Blo 1727064 4372501 := bbase (se 6 (by rfl) ⟨102480, by rfl⟩ : syracuseStep 4372501 = 204961) (by norm_num)
theorem B12621845 : Blo 1727064 12621845 := bbase (se 6 (by rfl) ⟨295824, by rfl⟩ : syracuseStep 12621845 = 591649) (by norm_num)
theorem B14956597 : Blo 1727064 14956597 := bbase (se 5 (by rfl) ⟨701090, by rfl⟩ : syracuseStep 14956597 = 1402181) (by norm_num)
theorem B3889205 : Blo 1727064 3889205 := bbase (se 5 (by rfl) ⟨182306, by rfl⟩ : syracuseStep 3889205 = 364613) (by norm_num)
theorem B5830757 : Blo 1727064 5830757 := bbase (se 4 (by rfl) ⟨546633, by rfl⟩ : syracuseStep 5830757 = 1093267) (by norm_num)
theorem B3889277 : Blo 1727064 3889277 := bbase (se 3 (by rfl) ⟨729239, by rfl⟩ : syracuseStep 3889277 = 1458479) (by norm_num)
theorem B4372613 : Blo 1727064 4372613 := bbase (se 4 (by rfl) ⟨409932, by rfl⟩ : syracuseStep 4372613 = 819865) (by norm_num)
theorem B2627749 : Blo 1727064 2627749 := bbase (se 4 (by rfl) ⟨246351, by rfl⟩ : syracuseStep 2627749 = 492703) (by norm_num)
theorem B5257381 : Blo 1727064 5257381 := bbase (se 4 (by rfl) ⟨492879, by rfl⟩ : syracuseStep 5257381 = 985759) (by norm_num)
theorem B8747189 : Blo 1727064 8747189 := bbase (se 5 (by rfl) ⟨410024, by rfl⟩ : syracuseStep 8747189 = 820049) (by norm_num)
theorem B2914501 : Blo 1727064 2914501 := bbase (se 4 (by rfl) ⟨273234, by rfl⟩ : syracuseStep 2914501 = 546469) (by norm_num)
theorem B3889349 : Blo 1727064 3889349 := bbase (se 4 (by rfl) ⟨364626, by rfl⟩ : syracuseStep 3889349 = 729253) (by norm_num)
theorem B28424405 : Blo 1727064 28424405 := bbase (se 7 (by rfl) ⟨333098, by rfl⟩ : syracuseStep 28424405 = 666197) (by norm_num)
theorem B3889421 : Blo 1727064 3889421 := bbase (se 3 (by rfl) ⟨729266, by rfl⟩ : syracuseStep 3889421 = 1458533) (by norm_num)
theorem B2914589 : Blo 1727064 2914589 := bbase (se 3 (by rfl) ⟨546485, by rfl⟩ : syracuseStep 2914589 = 1092971) (by norm_num)
theorem B4372805 : Blo 1727064 4372805 := bbase (se 4 (by rfl) ⟨409950, by rfl⟩ : syracuseStep 4372805 = 819901) (by norm_num)
theorem B5257541 : Blo 1727064 5257541 := bbase (se 4 (by rfl) ⟨492894, by rfl⟩ : syracuseStep 5257541 = 985789) (by norm_num)
theorem B201922901 : Blo 1727064 201922901 := bbase (se 10 (by rfl) ⟨295785, by rfl⟩ : syracuseStep 201922901 = 591571) (by norm_num)
theorem B4921685 : Blo 1727064 4921685 := bbase (se 10 (by rfl) ⟨7209, by rfl⟩ : syracuseStep 4921685 = 14419) (by norm_num)
theorem B16202069 : Blo 1727064 16202069 := bbase (se 10 (by rfl) ⟨23733, by rfl⟩ : syracuseStep 16202069 = 47467) (by norm_num)
theorem B3889493 : Blo 1727064 3889493 := bbase (se 10 (by rfl) ⟨5697, by rfl⟩ : syracuseStep 3889493 = 11395) (by norm_num)
theorem B4151645 : Blo 1727064 4151645 := bbase (se 3 (by rfl) ⟨778433, by rfl⟩ : syracuseStep 4151645 = 1556867) (by norm_num)
theorem B2767205 : Blo 1727064 2767205 := bbase (se 4 (by rfl) ⟨259425, by rfl⟩ : syracuseStep 2767205 = 518851) (by norm_num)
theorem B7379333 : Blo 1727064 7379333 := bbase (se 4 (by rfl) ⟨691812, by rfl⟩ : syracuseStep 7379333 = 1383625) (by norm_num)
theorem B6560149 : Blo 1727064 6560149 := bbase (se 6 (by rfl) ⟨153753, by rfl⟩ : syracuseStep 6560149 = 307507) (by norm_num)
theorem B2914717 : Blo 1727064 2914717 := bbase (se 3 (by rfl) ⟨546509, by rfl⟩ : syracuseStep 2914717 = 1093019) (by norm_num)
theorem B3889565 : Blo 1727064 3889565 := bbase (se 3 (by rfl) ⟨729293, by rfl⟩ : syracuseStep 3889565 = 1458587) (by norm_num)
theorem B3889637 : Blo 1727064 3889637 := bbase (se 4 (by rfl) ⟨364653, by rfl⟩ : syracuseStep 3889637 = 729307) (by norm_num)
theorem B2914805 : Blo 1727064 2914805 := bbase (se 5 (by rfl) ⟨136631, by rfl⟩ : syracuseStep 2914805 = 273263) (by norm_num)
theorem B5831189 : Blo 1727064 5831189 := bbase (se 6 (by rfl) ⟨136668, by rfl⟩ : syracuseStep 5831189 = 273337) (by norm_num)
theorem B26974741 : Blo 1727064 26974741 := bbase (se 6 (by rfl) ⟨632220, by rfl⟩ : syracuseStep 26974741 = 1264441) (by norm_num)
theorem B4151845 : Blo 1727064 4151845 := bbase (se 4 (by rfl) ⟨389235, by rfl⟩ : syracuseStep 4151845 = 778471) (by norm_num)
theorem B3889709 : Blo 1727064 3889709 := bbase (se 3 (by rfl) ⟨729320, by rfl⟩ : syracuseStep 3889709 = 1458641) (by norm_num)
theorem B2914933 : Blo 1727064 2914933 := bbase (se 5 (by rfl) ⟨136637, by rfl⟩ : syracuseStep 2914933 = 273275) (by norm_num)
theorem B3889781 : Blo 1727064 3889781 := bbase (se 5 (by rfl) ⟨182333, by rfl⟩ : syracuseStep 3889781 = 364667) (by norm_num)
theorem B2185861 : Blo 1727064 2185861 := bbase (se 4 (by rfl) ⟨204924, by rfl⟩ : syracuseStep 2185861 = 409849) (by norm_num)
theorem B2103953 : Blo 1727064 2103953 := bbase (se 2 (by rfl) ⟨788982, by rfl⟩ : syracuseStep 2103953 = 1577965) (by norm_num)
theorem B4373149 : Blo 1727064 4373149 := bbase (se 3 (by rfl) ⟨819965, by rfl⟩ : syracuseStep 4373149 = 1639931) (by norm_num)
theorem B3889853 : Blo 1727064 3889853 := bbase (se 3 (by rfl) ⟨729347, by rfl⟩ : syracuseStep 3889853 = 1458695) (by norm_num)
theorem B6560453 : Blo 1727064 6560453 := bbase (se 4 (by rfl) ⟨615042, by rfl⟩ : syracuseStep 6560453 = 1230085) (by norm_num)
theorem B2915021 : Blo 1727064 2915021 := bbase (se 3 (by rfl) ⟨546566, by rfl⟩ : syracuseStep 2915021 = 1093133) (by norm_num)
theorem B2185957 : Blo 1727064 2185957 := bbase (se 4 (by rfl) ⟨204933, by rfl⟩ : syracuseStep 2185957 = 409867) (by norm_num)
theorem B4922117 : Blo 1727064 4922117 := bbase (se 4 (by rfl) ⟨461448, by rfl⟩ : syracuseStep 4922117 = 922897) (by norm_num)
theorem B3889925 : Blo 1727064 3889925 := bbase (se 4 (by rfl) ⟨364680, by rfl⟩ : syracuseStep 3889925 = 729361) (by norm_num)
theorem B4373261 : Blo 1727064 4373261 := bbase (se 3 (by rfl) ⟨819986, by rfl⟩ : syracuseStep 4373261 = 1639973) (by norm_num)
theorem B2915149 : Blo 1727064 2915149 := bbase (se 3 (by rfl) ⟨546590, by rfl⟩ : syracuseStep 2915149 = 1093181) (by norm_num)
theorem B3889997 : Blo 1727064 3889997 := bbase (se 3 (by rfl) ⟨729374, by rfl⟩ : syracuseStep 3889997 = 1458749) (by norm_num)
theorem B2767717 : Blo 1727064 2767717 := bbase (se 4 (by rfl) ⟨259473, by rfl⟩ : syracuseStep 2767717 = 518947) (by norm_num)
theorem B5536613 : Blo 1727064 5536613 := bbase (se 4 (by rfl) ⟨519057, by rfl⟩ : syracuseStep 5536613 = 1038115) (by norm_num)
theorem B1751941 : Blo 1727064 1751941 := bbase (se 4 (by rfl) ⟨164244, by rfl⟩ : syracuseStep 1751941 = 328489) (by norm_num)
theorem B2186129 : Blo 1727064 2186129 := bbase (se 2 (by rfl) ⟨819798, by rfl⟩ : syracuseStep 2186129 = 1639597) (by norm_num)
theorem B3890069 : Blo 1727064 3890069 := bbase (se 6 (by rfl) ⟨91173, by rfl⟩ : syracuseStep 3890069 = 182347) (by norm_num)
theorem B2915237 : Blo 1727064 2915237 := bbase (se 4 (by rfl) ⟨273303, by rfl⟩ : syracuseStep 2915237 = 546607) (by norm_num)
theorem B13122485 : Blo 1727064 13122485 := bbase (se 5 (by rfl) ⟨615116, by rfl⟩ : syracuseStep 13122485 = 1230233) (by norm_num)
theorem B5831621 : Blo 1727064 5831621 := bbase (se 4 (by rfl) ⟨546714, by rfl⟩ : syracuseStep 5831621 = 1093429) (by norm_num)
theorem B2186185 : Blo 1727064 2186185 := bbase (se 2 (by rfl) ⟨819819, by rfl⟩ : syracuseStep 2186185 = 1639639) (by norm_num)
theorem B2104265 : Blo 1727064 2104265 := bbase (se 2 (by rfl) ⟨789099, by rfl⟩ : syracuseStep 2104265 = 1578199) (by norm_num)
theorem B4373453 : Blo 1727064 4373453 := bbase (se 3 (by rfl) ⟨820022, by rfl⟩ : syracuseStep 4373453 = 1640045) (by norm_num)
theorem B7003093 : Blo 1727064 7003093 := bbase (se 7 (by rfl) ⟨82067, by rfl⟩ : syracuseStep 7003093 = 164135) (by norm_num)
theorem B3890141 : Blo 1727064 3890141 := bbase (se 3 (by rfl) ⟨729401, by rfl⟩ : syracuseStep 3890141 = 1458803) (by norm_num)
theorem B11066357 : Blo 1727064 11066357 := bbase (se 5 (by rfl) ⟨518735, by rfl⟩ : syracuseStep 11066357 = 1037471) (by norm_num)
theorem B16604149 : Blo 1727064 16604149 := bbase (se 5 (by rfl) ⟨778319, by rfl⟩ : syracuseStep 16604149 = 1556639) (by norm_num)
theorem B2915365 : Blo 1727064 2915365 := bbase (se 4 (by rfl) ⟨273315, by rfl⟩ : syracuseStep 2915365 = 546631) (by norm_num)
theorem B3890213 : Blo 1727064 3890213 := bbase (se 4 (by rfl) ⟨364707, by rfl⟩ : syracuseStep 3890213 = 729415) (by norm_num)
theorem B2186281 : Blo 1727064 2186281 := bbase (se 2 (by rfl) ⟨819855, by rfl⟩ : syracuseStep 2186281 = 1639711) (by norm_num)
theorem B7003189 : Blo 1727064 7003189 := bbase (se 5 (by rfl) ⟨328274, by rfl⟩ : syracuseStep 7003189 = 656549) (by norm_num)
theorem B3890285 : Blo 1727064 3890285 := bbase (se 3 (by rfl) ⟨729428, by rfl⟩ : syracuseStep 3890285 = 1458857) (by norm_num)
theorem B2915453 : Blo 1727064 2915453 := bbase (se 3 (by rfl) ⟨546647, by rfl⟩ : syracuseStep 2915453 = 1093295) (by norm_num)
theorem B3890357 : Blo 1727064 3890357 := bbase (se 5 (by rfl) ⟨182360, by rfl⟩ : syracuseStep 3890357 = 364721) (by norm_num)
theorem B1752257 : Blo 1727064 1752257 := bbase (se 2 (by rfl) ⟨657096, by rfl⟩ : syracuseStep 1752257 = 1314193) (by norm_num)
theorem B2186453 : Blo 1727064 2186453 := bbase (se 7 (by rfl) ⟨25622, by rfl⟩ : syracuseStep 2186453 = 51245) (by norm_num)
theorem B8862965 : Blo 1727064 8862965 := bbase (se 5 (by rfl) ⟨415451, by rfl⟩ : syracuseStep 8862965 = 830903) (by norm_num)
theorem B2915581 : Blo 1727064 2915581 := bbase (se 3 (by rfl) ⟨546671, by rfl⟩ : syracuseStep 2915581 = 1093343) (by norm_num)
theorem B2186509 : Blo 1727064 2186509 := bbase (se 3 (by rfl) ⟨409970, by rfl⟩ : syracuseStep 2186509 = 819941) (by norm_num)
theorem B18685205 : Blo 1727064 18685205 := bbase (se 6 (by rfl) ⟨437934, by rfl⟩ : syracuseStep 18685205 = 875869) (by norm_num)
theorem B4373797 : Blo 1727064 4373797 := bbase (se 4 (by rfl) ⟨410043, by rfl⟩ : syracuseStep 4373797 = 820087) (by norm_num)
theorem B4152653 : Blo 1727064 4152653 := bbase (se 3 (by rfl) ⟨778622, by rfl⟩ : syracuseStep 4152653 = 1557245) (by norm_num)
theorem B2915669 : Blo 1727064 2915669 := bbase (se 11 (by rfl) ⟨2135, by rfl⟩ : syracuseStep 2915669 = 4271) (by norm_num)
theorem B2186605 : Blo 1727064 2186605 := bbase (se 3 (by rfl) ⟨409988, by rfl⟩ : syracuseStep 2186605 = 819977) (by norm_num)
theorem B7380341 : Blo 1727064 7380341 := bbase (se 5 (by rfl) ⟨345953, by rfl⟩ : syracuseStep 7380341 = 691907) (by norm_num)
theorem B5832053 : Blo 1727064 5832053 := bbase (se 5 (by rfl) ⟨273377, by rfl⟩ : syracuseStep 5832053 = 546755) (by norm_num)
theorem B4373909 : Blo 1727064 4373909 := bbase (se 6 (by rfl) ⟨102513, by rfl⟩ : syracuseStep 4373909 = 205027) (by norm_num)
theorem B3112349 : Blo 1727064 3112349 := bbase (se 3 (by rfl) ⟨583565, by rfl⟩ : syracuseStep 3112349 = 1167131) (by norm_num)
theorem B2956709 : Blo 1727064 2956709 := bbase (se 4 (by rfl) ⟨277191, by rfl⟩ : syracuseStep 2956709 = 554383) (by norm_num)
theorem B8748485 : Blo 1727064 8748485 := bbase (se 4 (by rfl) ⟨820170, by rfl⟩ : syracuseStep 8748485 = 1640341) (by norm_num)
theorem B1752517 : Blo 1727064 1752517 := bbase (se 4 (by rfl) ⟨164298, by rfl⟩ : syracuseStep 1752517 = 328597) (by norm_num)
theorem B9838037 : Blo 1727064 9838037 := bbase (se 7 (by rfl) ⟨115289, by rfl⟩ : syracuseStep 9838037 = 230579) (by norm_num)
theorem B2915797 : Blo 1727064 2915797 := bbase (se 7 (by rfl) ⟨34169, by rfl⟩ : syracuseStep 2915797 = 68339) (by norm_num)
theorem B4922869 : Blo 1727064 4922869 := bbase (se 5 (by rfl) ⟨230759, by rfl⟩ : syracuseStep 4922869 = 461519) (by norm_num)
theorem B2186777 : Blo 1727064 2186777 := bbase (se 2 (by rfl) ⟨820041, by rfl⟩ : syracuseStep 2186777 = 1640083) (by norm_num)
theorem B3792413 : Blo 1727064 3792413 := bbase (se 3 (by rfl) ⟨711077, by rfl⟩ : syracuseStep 3792413 = 1422155) (by norm_num)
theorem B2915885 : Blo 1727064 2915885 := bbase (se 3 (by rfl) ⟨546728, by rfl⟩ : syracuseStep 2915885 = 1093457) (by norm_num)
theorem B2186833 : Blo 1727064 2186833 := bbase (se 2 (by rfl) ⟨820062, by rfl⟩ : syracuseStep 2186833 = 1640125) (by norm_num)
theorem B4374101 : Blo 1727064 4374101 := bbase (se 8 (by rfl) ⟨25629, by rfl⟩ : syracuseStep 4374101 = 51259) (by norm_num)
theorem B4210325 : Blo 1727064 4210325 := bbase (se 6 (by rfl) ⟨98679, by rfl⟩ : syracuseStep 4210325 = 197359) (by norm_num)
theorem B19693205 : Blo 1727064 19693205 := bbase (se 6 (by rfl) ⟨461559, by rfl⟩ : syracuseStep 19693205 = 923119) (by norm_num)
theorem B2916013 : Blo 1727064 2916013 := bbase (se 3 (by rfl) ⟨546752, by rfl⟩ : syracuseStep 2916013 = 1093505) (by norm_num)
theorem B2186929 : Blo 1727064 2186929 := bbase (se 2 (by rfl) ⟨820098, by rfl⟩ : syracuseStep 2186929 = 1640197) (by norm_num)
theorem B2916101 : Blo 1727064 2916101 := bbase (se 4 (by rfl) ⟨273384, by rfl⟩ : syracuseStep 2916101 = 546769) (by norm_num)
theorem B5832485 : Blo 1727064 5832485 := bbase (se 4 (by rfl) ⟨546795, by rfl⟩ : syracuseStep 5832485 = 1093591) (by norm_num)
theorem B2768717 : Blo 1727064 2768717 := bbase (se 3 (by rfl) ⟨519134, by rfl⟩ : syracuseStep 2768717 = 1038269) (by norm_num)
theorem B6225749 : Blo 1727064 6225749 := bbase (se 9 (by rfl) ⟨18239, by rfl⟩ : syracuseStep 6225749 = 36479) (by norm_num)
theorem B2187101 : Blo 1727064 2187101 := bbase (se 3 (by rfl) ⟨410081, by rfl⟩ : syracuseStep 2187101 = 820163) (by norm_num)
theorem B2916229 : Blo 1727064 2916229 := bbase (se 4 (by rfl) ⟨273396, by rfl⟩ : syracuseStep 2916229 = 546793) (by norm_num)
theorem B2187157 : Blo 1727064 2187157 := bbase (se 6 (by rfl) ⟨51261, by rfl⟩ : syracuseStep 2187157 = 102523) (by norm_num)
theorem B4374445 : Blo 1727064 4374445 := bbase (se 3 (by rfl) ⟨820208, by rfl⟩ : syracuseStep 4374445 = 1640417) (by norm_num)
theorem B5537717 : Blo 1727064 5537717 := bbase (se 5 (by rfl) ⟨259580, by rfl⟩ : syracuseStep 5537717 = 519161) (by norm_num)
theorem B2768845 : Blo 1727064 2768845 := bbase (se 3 (by rfl) ⟨519158, by rfl⟩ : syracuseStep 2768845 = 1038317) (by norm_num)
theorem B2916317 : Blo 1727064 2916317 := bbase (se 3 (by rfl) ⟨546809, by rfl⟩ : syracuseStep 2916317 = 1093619) (by norm_num)
theorem B3112933 : Blo 1727064 3112933 := bbase (se 4 (by rfl) ⟨291837, by rfl⟩ : syracuseStep 3112933 = 583675) (by norm_num)
theorem B2187253 : Blo 1727064 2187253 := bbase (se 5 (by rfl) ⟨102527, by rfl⟩ : syracuseStep 2187253 = 205055) (by norm_num)
theorem B1728515 : Blo 1727064 1728515 := bstep (se 1 (by rfl) ⟨1296386, by rfl⟩ : syracuseStep 1728515 = 2592773) B2592773
theorem B9338885 : Blo 1727064 9338885 := bstep (se 4 (by rfl) ⟨875520, by rfl⟩ : syracuseStep 9338885 = 1751041) B1751041
theorem B2334739 : Blo 1727064 2334739 := bstep (se 1 (by rfl) ⟨1751054, by rfl⟩ : syracuseStep 2334739 = 3502109) B3502109
theorem B2916371 : Blo 1727064 2916371 := bstep (se 1 (by rfl) ⟨2187278, by rfl⟩ : syracuseStep 2916371 = 4374557) B4374557
theorem B1728531 : Blo 1727064 1728531 := bstep (se 1 (by rfl) ⟨1296398, by rfl⟩ : syracuseStep 1728531 = 2592797) B2592797
theorem B1728547 : Blo 1727064 1728547 := bstep (se 1 (by rfl) ⟨1296410, by rfl⟩ : syracuseStep 1728547 = 2592821) B2592821
theorem B1728563 : Blo 1727064 1728563 := bstep (se 1 (by rfl) ⟨1296422, by rfl⟩ : syracuseStep 1728563 = 2592845) B2592845
theorem B2768947 : Blo 1727064 2768947 := bstep (se 1 (by rfl) ⟨2076710, by rfl⟩ : syracuseStep 2768947 = 4153421) B4153421
theorem B1728579 : Blo 1727064 1728579 := bstep (se 1 (by rfl) ⟨1296434, by rfl⟩ : syracuseStep 1728579 = 2592869) B2592869
theorem B8749133 : Blo 1727064 8749133 := bstep (se 3 (by rfl) ⟨1640462, by rfl⟩ : syracuseStep 8749133 = 3280925) B3280925
theorem B3113041 : Blo 1727064 3113041 := bstep (se 2 (by rfl) ⟨1167390, by rfl⟩ : syracuseStep 3113041 = 2334781) B2334781
theorem B1728595 : Blo 1727064 1728595 := bstep (se 1 (by rfl) ⟨1296446, by rfl⟩ : syracuseStep 1728595 = 2592893) B2592893
theorem B2768993 : Blo 1727064 2768993 := bstep (se 2 (by rfl) ⟨1038372, by rfl⟩ : syracuseStep 2768993 = 2076745) B2076745
theorem B1728611 : Blo 1727064 1728611 := bstep (se 1 (by rfl) ⟨1296458, by rfl⟩ : syracuseStep 1728611 = 2592917) B2592917
theorem B1728627 : Blo 1727064 1728627 := bstep (se 1 (by rfl) ⟨1296470, by rfl⟩ : syracuseStep 1728627 = 2592941) B2592941
theorem B1728643 : Blo 1727064 1728643 := bstep (se 1 (by rfl) ⟨1296482, by rfl⟩ : syracuseStep 1728643 = 2592965) B2592965
theorem B2916499 : Blo 1727064 2916499 := bstep (se 1 (by rfl) ⟨2187374, by rfl⟩ : syracuseStep 2916499 = 4374749) B4374749
theorem B1728659 : Blo 1727064 1728659 := bstep (se 1 (by rfl) ⟨1296494, by rfl⟩ : syracuseStep 1728659 = 2592989) B2592989
theorem B1728675 : Blo 1727064 1728675 := bstep (se 1 (by rfl) ⟨1296506, by rfl⟩ : syracuseStep 1728675 = 2593013) B2593013
theorem B1728691 : Blo 1727064 1728691 := bstep (se 1 (by rfl) ⟨1296518, by rfl⟩ : syracuseStep 1728691 = 2593037) B2593037
theorem B1728707 : Blo 1727064 1728707 := bstep (se 1 (by rfl) ⟨1296530, by rfl⟩ : syracuseStep 1728707 = 2593061) B2593061
theorem B1728723 : Blo 1727064 1728723 := bstep (se 1 (by rfl) ⟨1296542, by rfl⟩ : syracuseStep 1728723 = 2593085) B2593085
theorem B1728739 : Blo 1727064 1728739 := bstep (se 1 (by rfl) ⟨1296554, by rfl⟩ : syracuseStep 1728739 = 2593109) B2593109
theorem B4374769 : Blo 1727064 4374769 := bstep (se 2 (by rfl) ⟨1640538, by rfl⟩ : syracuseStep 4374769 = 3281077) B3281077
theorem B1728755 : Blo 1727064 1728755 := bstep (se 1 (by rfl) ⟨1296566, by rfl⟩ : syracuseStep 1728755 = 2593133) B2593133
theorem B1728771 : Blo 1727064 1728771 := bstep (se 1 (by rfl) ⟨1296578, by rfl⟩ : syracuseStep 1728771 = 2593157) B2593157
theorem B1728787 : Blo 1727064 1728787 := bstep (se 1 (by rfl) ⟨1296590, by rfl⟩ : syracuseStep 1728787 = 2593181) B2593181
theorem B2916641 : Blo 1727064 2916641 := bstep (se 2 (by rfl) ⟨1093740, by rfl⟩ : syracuseStep 2916641 = 2187481) B2187481
theorem B1728803 : Blo 1727064 1728803 := bstep (se 1 (by rfl) ⟨1296602, by rfl⟩ : syracuseStep 1728803 = 2593205) B2593205
theorem B1728819 : Blo 1727064 1728819 := bstep (se 1 (by rfl) ⟨1296614, by rfl⟩ : syracuseStep 1728819 = 2593229) B2593229
theorem B2187587 : Blo 1727064 2187587 := bstep (se 1 (by rfl) ⟨1640690, by rfl⟩ : syracuseStep 2187587 = 3281381) B3281381
theorem B1728835 : Blo 1727064 1728835 := bstep (se 1 (by rfl) ⟨1296626, by rfl⟩ : syracuseStep 1728835 = 2593253) B2593253
theorem B1728851 : Blo 1727064 1728851 := bstep (se 1 (by rfl) ⟨1296638, by rfl⟩ : syracuseStep 1728851 = 2593277) B2593277
theorem B1728867 : Blo 1727064 1728867 := bstep (se 1 (by rfl) ⟨1296650, by rfl⟩ : syracuseStep 1728867 = 2593301) B2593301
theorem B4923757 : Blo 1727064 4923757 := bstep (se 3 (by rfl) ⟨923204, by rfl⟩ : syracuseStep 4923757 = 1846409) B1846409
theorem B1728883 : Blo 1727064 1728883 := bstep (se 1 (by rfl) ⟨1296662, by rfl⟩ : syracuseStep 1728883 = 2593325) B2593325
theorem B1728899 : Blo 1727064 1728899 := bstep (se 1 (by rfl) ⟨1296674, by rfl⟩ : syracuseStep 1728899 = 2593349) B2593349
theorem B1728915 : Blo 1727064 1728915 := bstep (se 1 (by rfl) ⟨1296686, by rfl⟩ : syracuseStep 1728915 = 2593373) B2593373
theorem B2916769 : Blo 1727064 2916769 := bstep (se 2 (by rfl) ⟨1093788, by rfl⟩ : syracuseStep 2916769 = 2187577) B2187577
theorem B1728931 : Blo 1727064 1728931 := bstep (se 1 (by rfl) ⟨1296698, by rfl⟩ : syracuseStep 1728931 = 2593397) B2593397
theorem B5833133 : Blo 1727064 5833133 := bstep (se 3 (by rfl) ⟨1093712, by rfl⟩ : syracuseStep 5833133 = 2187425) B2187425
theorem B1728947 : Blo 1727064 1728947 := bstep (se 1 (by rfl) ⟨1296710, by rfl⟩ : syracuseStep 1728947 = 2593421) B2593421
theorem B2916803 : Blo 1727064 2916803 := bstep (se 1 (by rfl) ⟨2187602, by rfl⟩ : syracuseStep 2916803 = 4375205) B4375205
theorem B1728963 : Blo 1727064 1728963 := bstep (se 1 (by rfl) ⟨1296722, by rfl⟩ : syracuseStep 1728963 = 2593445) B2593445
theorem B1728979 : Blo 1727064 1728979 := bstep (se 1 (by rfl) ⟨1296734, by rfl⟩ : syracuseStep 1728979 = 2593469) B2593469
theorem B5833187 : Blo 1727064 5833187 := bstep (se 1 (by rfl) ⟨4374890, by rfl⟩ : syracuseStep 5833187 = 8749781) B8749781
theorem B1728995 : Blo 1727064 1728995 := bstep (se 1 (by rfl) ⟨1296746, by rfl⟩ : syracuseStep 1728995 = 2593493) B2593493
theorem B1729011 : Blo 1727064 1729011 := bstep (se 1 (by rfl) ⟨1296758, by rfl⟩ : syracuseStep 1729011 = 2593517) B2593517
theorem B4375043 : Blo 1727064 4375043 := bstep (se 1 (by rfl) ⟨3281282, by rfl⟩ : syracuseStep 4375043 = 6562565) B6562565
theorem B1729027 : Blo 1727064 1729027 := bstep (se 1 (by rfl) ⟨1296770, by rfl⟩ : syracuseStep 1729027 = 2593541) B2593541
theorem B1729043 : Blo 1727064 1729043 := bstep (se 1 (by rfl) ⟨1296782, by rfl⟩ : syracuseStep 1729043 = 2593565) B2593565
theorem B1729059 : Blo 1727064 1729059 := bstep (se 1 (by rfl) ⟨1296794, by rfl⟩ : syracuseStep 1729059 = 2593589) B2593589
theorem B63054389 : Blo 1727064 63054389 := bstep (se 5 (by rfl) ⟨2955674, by rfl⟩ : syracuseStep 63054389 = 5911349) B5911349
theorem B2916931 : Blo 1727064 2916931 := bstep (se 1 (by rfl) ⟨2187698, by rfl⟩ : syracuseStep 2916931 = 4375397) B4375397
theorem B9339533 : Blo 1727064 9339533 := bstep (se 3 (by rfl) ⟨1751162, by rfl⟩ : syracuseStep 9339533 = 3502325) B3502325
theorem B4375235 : Blo 1727064 4375235 := bstep (se 1 (by rfl) ⟨3281426, by rfl⟩ : syracuseStep 4375235 = 6562853) B6562853
theorem B9847493 : Blo 1727064 9847493 := bstep (se 4 (by rfl) ⟨923202, by rfl⟩ : syracuseStep 9847493 = 1846405) B1846405
theorem B2917073 : Blo 1727064 2917073 := bstep (se 2 (by rfl) ⟨1093902, by rfl⟩ : syracuseStep 2917073 = 2187805) B2187805
theorem B5833457 : Blo 1727064 5833457 := bstep (se 2 (by rfl) ⟨2187546, by rfl⟩ : syracuseStep 5833457 = 4375093) B4375093
theorem B9339661 : Blo 1727064 9339661 := bstep (se 3 (by rfl) ⟨1751186, by rfl⟩ : syracuseStep 9339661 = 3502373) B3502373
theorem B2917201 : Blo 1727064 2917201 := bstep (se 2 (by rfl) ⟨1093950, by rfl⟩ : syracuseStep 2917201 = 2187901) B2187901
theorem B2917235 : Blo 1727064 2917235 := bstep (se 1 (by rfl) ⟨2187926, by rfl⟩ : syracuseStep 2917235 = 4375853) B4375853
theorem B2917363 : Blo 1727064 2917363 := bstep (se 1 (by rfl) ⟨2188022, by rfl⟩ : syracuseStep 2917363 = 4376045) B4376045
theorem B2188291 : Blo 1727064 2188291 := bstep (se 1 (by rfl) ⟨1641218, by rfl⟩ : syracuseStep 2188291 = 3282437) B3282437
theorem B8299597 : Blo 1727064 8299597 := bstep (se 3 (by rfl) ⟨1556174, by rfl⟩ : syracuseStep 8299597 = 3112349) B3112349
theorem B2917505 : Blo 1727064 2917505 := bstep (se 2 (by rfl) ⟨1094064, by rfl⟩ : syracuseStep 2917505 = 2188129) B2188129
theorem B2335921 : Blo 1727064 2335921 := bstep (se 2 (by rfl) ⟨875970, by rfl⟩ : syracuseStep 2335921 = 1751941) B1751941
theorem B11068613 : Blo 1727064 11068613 := bstep (se 4 (by rfl) ⟨1037682, by rfl⟩ : syracuseStep 11068613 = 2075365) B2075365
theorem B2917633 : Blo 1727064 2917633 := bstep (se 2 (by rfl) ⟨1094112, by rfl⟩ : syracuseStep 2917633 = 2188225) B2188225
theorem B5833997 : Blo 1727064 5833997 := bstep (se 3 (by rfl) ⟨1093874, by rfl⟩ : syracuseStep 5833997 = 2187749) B2187749
theorem B2917667 : Blo 1727064 2917667 := bstep (se 1 (by rfl) ⟨2188250, by rfl⟩ : syracuseStep 2917667 = 4376501) B4376501
theorem B5834051 : Blo 1727064 5834051 := bstep (se 1 (by rfl) ⟨4375538, by rfl⟩ : syracuseStep 5834051 = 8751077) B8751077
theorem B21022021 : Blo 1727064 21022021 := bstep (se 4 (by rfl) ⟨1970814, by rfl⟩ : syracuseStep 21022021 = 3941629) B3941629
theorem B2917795 : Blo 1727064 2917795 := bstep (se 1 (by rfl) ⟨2188346, by rfl⟩ : syracuseStep 2917795 = 4376693) B4376693
theorem B1943059 : Blo 1727064 1943059 := bstep (se 1 (by rfl) ⟨1457294, by rfl⟩ : syracuseStep 1943059 = 2914589) B2914589
theorem B1844803 : Blo 1727064 1844803 := bstep (se 1 (by rfl) ⟨1383602, by rfl⟩ : syracuseStep 1844803 = 2767205) B2767205
theorem B5834321 : Blo 1727064 5834321 := bstep (se 2 (by rfl) ⟨2187870, by rfl⟩ : syracuseStep 5834321 = 4375741) B4375741
theorem B4376177 : Blo 1727064 4376177 := bstep (se 2 (by rfl) ⟨1641066, by rfl⟩ : syracuseStep 4376177 = 3282133) B3282133
theorem B1943203 : Blo 1727064 1943203 := bstep (se 1 (by rfl) ⟨1457402, by rfl⟩ : syracuseStep 1943203 = 2914805) B2914805
theorem B4376227 : Blo 1727064 4376227 := bstep (se 1 (by rfl) ⟨3282170, by rfl⟩ : syracuseStep 4376227 = 6564341) B6564341
theorem B2459441 : Blo 1727064 2459441 := bstep (se 2 (by rfl) ⟨922290, by rfl⟩ : syracuseStep 2459441 = 1844581) B1844581
theorem B4376369 : Blo 1727064 4376369 := bstep (se 2 (by rfl) ⟨1641138, by rfl⟩ : syracuseStep 4376369 = 3282277) B3282277
theorem B1943347 : Blo 1727064 1943347 := bstep (se 1 (by rfl) ⟨1457510, by rfl⟩ : syracuseStep 1943347 = 2915021) B2915021
theorem B22153013 : Blo 1727064 22153013 := bstep (se 5 (by rfl) ⟨1038422, by rfl⟩ : syracuseStep 22153013 = 2076845) B2076845
theorem B2459521 : Blo 1727064 2459521 := bstep (se 2 (by rfl) ⟨922320, by rfl⟩ : syracuseStep 2459521 = 1844641) B1844641
theorem B2590625 : Blo 1727064 2590625 := bstep (se 2 (by rfl) ⟨971484, by rfl⟩ : syracuseStep 2590625 = 1942969) B1942969
theorem B2590643 : Blo 1727064 2590643 := bstep (se 1 (by rfl) ⟨1942982, by rfl⟩ : syracuseStep 2590643 = 3885965) B3885965
theorem B2336689 : Blo 1727064 2336689 := bstep (se 2 (by rfl) ⟨876258, by rfl⟩ : syracuseStep 2336689 = 1752517) B1752517
theorem B1943491 : Blo 1727064 1943491 := bstep (se 1 (by rfl) ⟨1457618, by rfl⟩ : syracuseStep 1943491 = 2915237) B2915237
theorem B2590673 : Blo 1727064 2590673 := bstep (se 2 (by rfl) ⟨971502, by rfl⟩ : syracuseStep 2590673 = 1943005) B1943005
theorem B2590691 : Blo 1727064 2590691 := bstep (se 1 (by rfl) ⟨1943018, by rfl⟩ : syracuseStep 2590691 = 3886037) B3886037
theorem B6563825 : Blo 1727064 6563825 := bstep (se 2 (by rfl) ⟨2461434, by rfl⟩ : syracuseStep 6563825 = 4922869) B4922869
theorem B2590721 : Blo 1727064 2590721 := bstep (se 2 (by rfl) ⟨971520, by rfl⟩ : syracuseStep 2590721 = 1943041) B1943041
theorem B2590739 : Blo 1727064 2590739 := bstep (se 1 (by rfl) ⟨1943054, by rfl⟩ : syracuseStep 2590739 = 3886109) B3886109
theorem B2590769 : Blo 1727064 2590769 := bstep (se 2 (by rfl) ⟨971538, by rfl⟩ : syracuseStep 2590769 = 1943077) B1943077
theorem B2590787 : Blo 1727064 2590787 := bstep (se 1 (by rfl) ⟨1943090, by rfl⟩ : syracuseStep 2590787 = 3886181) B3886181
theorem B1943635 : Blo 1727064 1943635 := bstep (se 1 (by rfl) ⟨1457726, by rfl⟩ : syracuseStep 1943635 = 2915453) B2915453
theorem B2590817 : Blo 1727064 2590817 := bstep (se 2 (by rfl) ⟨971556, by rfl⟩ : syracuseStep 2590817 = 1943113) B1943113
theorem B5834861 : Blo 1727064 5834861 := bstep (se 3 (by rfl) ⟨1094036, by rfl⟩ : syracuseStep 5834861 = 2188073) B2188073
theorem B2590835 : Blo 1727064 2590835 := bstep (se 1 (by rfl) ⟨1943126, by rfl⟩ : syracuseStep 2590835 = 3886253) B3886253
theorem B2590865 : Blo 1727064 2590865 := bstep (se 2 (by rfl) ⟨971574, by rfl⟩ : syracuseStep 2590865 = 1943149) B1943149
theorem B5908643 : Blo 1727064 5908643 := bstep (se 1 (by rfl) ⟨4431482, by rfl⟩ : syracuseStep 5908643 = 8862965) B8862965
theorem B2590883 : Blo 1727064 2590883 := bstep (se 1 (by rfl) ⟨1943162, by rfl⟩ : syracuseStep 2590883 = 3886325) B3886325
theorem B5834915 : Blo 1727064 5834915 := bstep (se 1 (by rfl) ⟨4376186, by rfl⟩ : syracuseStep 5834915 = 8752373) B8752373
theorem B2590913 : Blo 1727064 2590913 := bstep (se 2 (by rfl) ⟨971592, by rfl⟩ : syracuseStep 2590913 = 1943185) B1943185
theorem B2590931 : Blo 1727064 2590931 := bstep (se 1 (by rfl) ⟨1943198, by rfl⟩ : syracuseStep 2590931 = 3886397) B3886397
theorem B1943779 : Blo 1727064 1943779 := bstep (se 1 (by rfl) ⟨1457834, by rfl⟩ : syracuseStep 1943779 = 2915669) B2915669
theorem B2590961 : Blo 1727064 2590961 := bstep (se 2 (by rfl) ⟨971610, by rfl⟩ : syracuseStep 2590961 = 1943221) B1943221
theorem B2590979 : Blo 1727064 2590979 := bstep (se 1 (by rfl) ⟨1943234, by rfl⟩ : syracuseStep 2590979 = 3886469) B3886469
theorem B14764301 : Blo 1727064 14764301 := bstep (se 3 (by rfl) ⟨2768306, by rfl⟩ : syracuseStep 14764301 = 5536613) B5536613
theorem B2591009 : Blo 1727064 2591009 := bstep (se 2 (by rfl) ⟨971628, by rfl⟩ : syracuseStep 2591009 = 1943257) B1943257
theorem B9341219 : Blo 1727064 9341219 := bstep (se 1 (by rfl) ⟨7005914, by rfl⟩ : syracuseStep 9341219 = 14011829) B14011829
theorem B2591027 : Blo 1727064 2591027 := bstep (se 1 (by rfl) ⟨1943270, by rfl⟩ : syracuseStep 2591027 = 3886541) B3886541
theorem B2591057 : Blo 1727064 2591057 := bstep (se 2 (by rfl) ⟨971646, by rfl⟩ : syracuseStep 2591057 = 1943293) B1943293
theorem B2591075 : Blo 1727064 2591075 := bstep (se 1 (by rfl) ⟨1943306, by rfl⟩ : syracuseStep 2591075 = 3886613) B3886613
theorem B3279217 : Blo 1727064 3279217 := bstep (se 2 (by rfl) ⟨1229706, by rfl⟩ : syracuseStep 3279217 = 2459413) B2459413
theorem B1943923 : Blo 1727064 1943923 := bstep (se 1 (by rfl) ⟨1457942, by rfl⟩ : syracuseStep 1943923 = 2915885) B2915885
theorem B2591105 : Blo 1727064 2591105 := bstep (se 2 (by rfl) ⟨971664, by rfl⟩ : syracuseStep 2591105 = 1943329) B1943329
theorem B2591123 : Blo 1727064 2591123 := bstep (se 1 (by rfl) ⟨1943342, by rfl⟩ : syracuseStep 2591123 = 3886685) B3886685
theorem B3115427 : Blo 1727064 3115427 := bstep (se 1 (by rfl) ⟨2336570, by rfl⟩ : syracuseStep 3115427 = 4673141) B4673141
theorem B2591153 : Blo 1727064 2591153 := bstep (se 2 (by rfl) ⟨971682, by rfl⟩ : syracuseStep 2591153 = 1943365) B1943365
theorem B5835185 : Blo 1727064 5835185 := bstep (se 2 (by rfl) ⟨2188194, by rfl⟩ : syracuseStep 5835185 = 4376389) B4376389
theorem B2591171 : Blo 1727064 2591171 := bstep (se 1 (by rfl) ⟨1943378, by rfl⟩ : syracuseStep 2591171 = 3886757) B3886757
theorem B2591201 : Blo 1727064 2591201 := bstep (se 2 (by rfl) ⟨971700, by rfl⟩ : syracuseStep 2591201 = 1943401) B1943401
theorem B2591219 : Blo 1727064 2591219 := bstep (se 1 (by rfl) ⟨1943414, by rfl⟩ : syracuseStep 2591219 = 3886829) B3886829
theorem B1944067 : Blo 1727064 1944067 := bstep (se 1 (by rfl) ⟨1458050, by rfl⟩ : syracuseStep 1944067 = 2916101) B2916101
theorem B2591249 : Blo 1727064 2591249 := bstep (se 2 (by rfl) ⟨971718, by rfl⟩ : syracuseStep 2591249 = 1943437) B1943437
theorem B2591267 : Blo 1727064 2591267 := bstep (se 1 (by rfl) ⟨1943450, by rfl⟩ : syracuseStep 2591267 = 3886901) B3886901
theorem B1845811 : Blo 1727064 1845811 := bstep (se 1 (by rfl) ⟨1384358, by rfl⟩ : syracuseStep 1845811 = 2768717) B2768717
theorem B2591297 : Blo 1727064 2591297 := bstep (se 2 (by rfl) ⟨971736, by rfl⟩ : syracuseStep 2591297 = 1943473) B1943473
theorem B2591315 : Blo 1727064 2591315 := bstep (se 1 (by rfl) ⟨1943486, by rfl⟩ : syracuseStep 2591315 = 3886973) B3886973
theorem B3689059 : Blo 1727064 3689059 := bstep (se 1 (by rfl) ⟨2766794, by rfl⟩ : syracuseStep 3689059 = 5533589) B5533589
theorem B2591345 : Blo 1727064 2591345 := bstep (se 2 (by rfl) ⟨971754, by rfl⟩ : syracuseStep 2591345 = 1943509) B1943509
theorem B2591363 : Blo 1727064 2591363 := bstep (se 1 (by rfl) ⟨1943522, by rfl⟩ : syracuseStep 2591363 = 3887045) B3887045
theorem B2460307 : Blo 1727064 2460307 := bstep (se 1 (by rfl) ⟨1845230, by rfl⟩ : syracuseStep 2460307 = 3690461) B3690461
theorem B1944211 : Blo 1727064 1944211 := bstep (se 1 (by rfl) ⟨1458158, by rfl⟩ : syracuseStep 1944211 = 2916317) B2916317
theorem B2591393 : Blo 1727064 2591393 := bstep (se 2 (by rfl) ⟨971772, by rfl⟩ : syracuseStep 2591393 = 1943545) B1943545
theorem B2591411 : Blo 1727064 2591411 := bstep (se 1 (by rfl) ⟨1943558, by rfl⟩ : syracuseStep 2591411 = 3887117) B3887117
theorem B7383757 : Blo 1727064 7383757 := bstep (se 3 (by rfl) ⟨1384454, by rfl⟩ : syracuseStep 7383757 = 2768909) B2768909
theorem B2591441 : Blo 1727064 2591441 := bstep (se 2 (by rfl) ⟨971790, by rfl⟩ : syracuseStep 2591441 = 1943581) B1943581
theorem B3115729 : Blo 1727064 3115729 := bstep (se 2 (by rfl) ⟨1168398, by rfl⟩ : syracuseStep 3115729 = 2336797) B2336797
theorem B14756579 : Blo 1727064 14756579 := bstep (se 1 (by rfl) ⟨11067434, by rfl⟩ : syracuseStep 14756579 = 22134869) B22134869
theorem B2591459 : Blo 1727064 2591459 := bstep (se 1 (by rfl) ⟨1943594, by rfl⟩ : syracuseStep 2591459 = 3887189) B3887189
theorem B19942129 : Blo 1727064 19942129 := bstep (se 2 (by rfl) ⟨7478298, by rfl⟩ : syracuseStep 19942129 = 14956597) B14956597
theorem B2591489 : Blo 1727064 2591489 := bstep (se 2 (by rfl) ⟨971808, by rfl⟩ : syracuseStep 2591489 = 1943617) B1943617
theorem B3279619 : Blo 1727064 3279619 := bstep (se 1 (by rfl) ⟨2459714, by rfl⟩ : syracuseStep 3279619 = 4919429) B4919429
theorem B2591507 : Blo 1727064 2591507 := bstep (se 1 (by rfl) ⟨1943630, by rfl⟩ : syracuseStep 2591507 = 3887261) B3887261
theorem B1944355 : Blo 1727064 1944355 := bstep (se 1 (by rfl) ⟨1458266, by rfl⟩ : syracuseStep 1944355 = 2916533) B2916533
theorem B3279665 : Blo 1727064 3279665 := bstep (se 2 (by rfl) ⟨1229874, by rfl⟩ : syracuseStep 3279665 = 2459749) B2459749
theorem B2591537 : Blo 1727064 2591537 := bstep (se 2 (by rfl) ⟨971826, by rfl⟩ : syracuseStep 2591537 = 1943653) B1943653
theorem B2591555 : Blo 1727064 2591555 := bstep (se 1 (by rfl) ⟨1943666, by rfl⟩ : syracuseStep 2591555 = 3887333) B3887333
theorem B4918097 : Blo 1727064 4918097 := bstep (se 2 (by rfl) ⟨1844286, by rfl⟩ : syracuseStep 4918097 = 3688573) B3688573
theorem B2591585 : Blo 1727064 2591585 := bstep (se 2 (by rfl) ⟨971844, by rfl⟩ : syracuseStep 2591585 = 1943689) B1943689
theorem B2591603 : Blo 1727064 2591603 := bstep (se 1 (by rfl) ⟨1943702, by rfl⟩ : syracuseStep 2591603 = 3887405) B3887405
theorem B2591633 : Blo 1727064 2591633 := bstep (se 2 (by rfl) ⟨971862, by rfl⟩ : syracuseStep 2591633 = 1943725) B1943725
theorem B2591651 : Blo 1727064 2591651 := bstep (se 1 (by rfl) ⟨1943738, by rfl⟩ : syracuseStep 2591651 = 3887477) B3887477
theorem B3886001 : Blo 1727064 3886001 := bstep (se 2 (by rfl) ⟨1457250, by rfl⟩ : syracuseStep 3886001 = 2914501) B2914501
theorem B8752049 : Blo 1727064 8752049 := bstep (se 2 (by rfl) ⟨3282018, by rfl⟩ : syracuseStep 8752049 = 6564037) B6564037
theorem B1944499 : Blo 1727064 1944499 := bstep (se 1 (by rfl) ⟨1458374, by rfl⟩ : syracuseStep 1944499 = 2916749) B2916749
theorem B2591681 : Blo 1727064 2591681 := bstep (se 2 (by rfl) ⟨971880, by rfl⟩ : syracuseStep 2591681 = 1943761) B1943761
theorem B3886019 : Blo 1727064 3886019 := bstep (se 1 (by rfl) ⟨2914514, by rfl⟩ : syracuseStep 3886019 = 5829029) B5829029
theorem B2591699 : Blo 1727064 2591699 := bstep (se 1 (by rfl) ⟨1943774, by rfl⟩ : syracuseStep 2591699 = 3887549) B3887549
theorem B2591729 : Blo 1727064 2591729 := bstep (se 2 (by rfl) ⟨971898, by rfl⟩ : syracuseStep 2591729 = 1943797) B1943797
theorem B2591747 : Blo 1727064 2591747 := bstep (se 1 (by rfl) ⟨1943810, by rfl⟩ : syracuseStep 2591747 = 3887621) B3887621
theorem B8743949 : Blo 1727064 8743949 := bstep (se 3 (by rfl) ⟨1639490, by rfl⟩ : syracuseStep 8743949 = 3278981) B3278981
theorem B2591777 : Blo 1727064 2591777 := bstep (se 2 (by rfl) ⟨971916, by rfl⟩ : syracuseStep 2591777 = 1943833) B1943833
theorem B2591795 : Blo 1727064 2591795 := bstep (se 1 (by rfl) ⟨1943846, by rfl⟩ : syracuseStep 2591795 = 3887693) B3887693
theorem B1944643 : Blo 1727064 1944643 := bstep (se 1 (by rfl) ⟨1458482, by rfl⟩ : syracuseStep 1944643 = 2916965) B2916965
theorem B3279953 : Blo 1727064 3279953 := bstep (se 2 (by rfl) ⟨1229982, by rfl⟩ : syracuseStep 3279953 = 2459965) B2459965
theorem B2591825 : Blo 1727064 2591825 := bstep (se 2 (by rfl) ⟨971934, by rfl⟩ : syracuseStep 2591825 = 1943869) B1943869
theorem B2591843 : Blo 1727064 2591843 := bstep (se 1 (by rfl) ⟨1943882, by rfl⟩ : syracuseStep 2591843 = 3887765) B3887765
theorem B3370097 : Blo 1727064 3370097 := bstep (se 2 (by rfl) ⟨1263786, by rfl⟩ : syracuseStep 3370097 = 2527573) B2527573
theorem B2460785 : Blo 1727064 2460785 := bstep (se 2 (by rfl) ⟨922794, by rfl⟩ : syracuseStep 2460785 = 1845589) B1845589
theorem B2591873 : Blo 1727064 2591873 := bstep (se 2 (by rfl) ⟨971952, by rfl⟩ : syracuseStep 2591873 = 1943905) B1943905
theorem B2591891 : Blo 1727064 2591891 := bstep (se 1 (by rfl) ⟨1943918, by rfl⟩ : syracuseStep 2591891 = 3887837) B3887837
theorem B4672685 : Blo 1727064 4672685 := bstep (se 3 (by rfl) ⟨876128, by rfl⟩ : syracuseStep 4672685 = 1752257) B1752257
theorem B2591921 : Blo 1727064 2591921 := bstep (se 2 (by rfl) ⟨971970, by rfl⟩ : syracuseStep 2591921 = 1943941) B1943941
theorem B2591939 : Blo 1727064 2591939 := bstep (se 1 (by rfl) ⟨1943954, by rfl⟩ : syracuseStep 2591939 = 3887909) B3887909
theorem B3886289 : Blo 1727064 3886289 := bstep (se 2 (by rfl) ⟨1457358, by rfl⟩ : syracuseStep 3886289 = 2914717) B2914717
theorem B1944787 : Blo 1727064 1944787 := bstep (se 1 (by rfl) ⟨1458590, by rfl⟩ : syracuseStep 1944787 = 2917181) B2917181
theorem B2591969 : Blo 1727064 2591969 := bstep (se 2 (by rfl) ⟨971988, by rfl⟩ : syracuseStep 2591969 = 1943977) B1943977
theorem B3886307 : Blo 1727064 3886307 := bstep (se 1 (by rfl) ⟨2914730, by rfl⟩ : syracuseStep 3886307 = 5829461) B5829461
theorem B2460899 : Blo 1727064 2460899 := bstep (se 1 (by rfl) ⟨1845674, by rfl⟩ : syracuseStep 2460899 = 3691349) B3691349
theorem B2591987 : Blo 1727064 2591987 := bstep (se 1 (by rfl) ⟨1943990, by rfl⟩ : syracuseStep 2591987 = 3887981) B3887981
theorem B2592017 : Blo 1727064 2592017 := bstep (se 2 (by rfl) ⟨972006, by rfl⟩ : syracuseStep 2592017 = 1944013) B1944013
theorem B2592035 : Blo 1727064 2592035 := bstep (se 1 (by rfl) ⟨1944026, by rfl⟩ : syracuseStep 2592035 = 3888053) B3888053
theorem B2460979 : Blo 1727064 2460979 := bstep (se 1 (by rfl) ⟨1845734, by rfl⟩ : syracuseStep 2460979 = 3691469) B3691469
theorem B26602805 : Blo 1727064 26602805 := bstep (se 5 (by rfl) ⟨1247006, by rfl⟩ : syracuseStep 26602805 = 2494013) B2494013
theorem B2592065 : Blo 1727064 2592065 := bstep (se 2 (by rfl) ⟨972024, by rfl⟩ : syracuseStep 2592065 = 1944049) B1944049
theorem B6229325 : Blo 1727064 6229325 := bstep (se 3 (by rfl) ⟨1167998, by rfl⟩ : syracuseStep 6229325 = 2335997) B2335997
theorem B2592083 : Blo 1727064 2592083 := bstep (se 1 (by rfl) ⟨1944062, by rfl⟩ : syracuseStep 2592083 = 3888125) B3888125
theorem B1944931 : Blo 1727064 1944931 := bstep (se 1 (by rfl) ⟨1458698, by rfl⟩ : syracuseStep 1944931 = 2917397) B2917397
theorem B2592113 : Blo 1727064 2592113 := bstep (se 2 (by rfl) ⟨972042, by rfl⟩ : syracuseStep 2592113 = 1944085) B1944085
theorem B35966321 : Blo 1727064 35966321 := bstep (se 2 (by rfl) ⟨13487370, by rfl⟩ : syracuseStep 35966321 = 26974741) B26974741
theorem B2592131 : Blo 1727064 2592131 := bstep (se 1 (by rfl) ⟨1944098, by rfl⟩ : syracuseStep 2592131 = 3888197) B3888197
theorem B2592161 : Blo 1727064 2592161 := bstep (se 2 (by rfl) ⟨972060, by rfl⟩ : syracuseStep 2592161 = 1944121) B1944121
theorem B2076067 : Blo 1727064 2076067 := bstep (se 1 (by rfl) ⟨1557050, by rfl⟩ : syracuseStep 2076067 = 3114101) B3114101
theorem B2592179 : Blo 1727064 2592179 := bstep (se 1 (by rfl) ⟨1944134, by rfl⟩ : syracuseStep 2592179 = 3888269) B3888269
theorem B24915397 : Blo 1727064 24915397 := bstep (se 4 (by rfl) ⟨2335818, by rfl⟩ : syracuseStep 24915397 = 4671637) B4671637
theorem B2592209 : Blo 1727064 2592209 := bstep (se 2 (by rfl) ⟨972078, by rfl⟩ : syracuseStep 2592209 = 1944157) B1944157
theorem B2592227 : Blo 1727064 2592227 := bstep (se 1 (by rfl) ⟨1944170, by rfl⟩ : syracuseStep 2592227 = 3888341) B3888341
theorem B4918769 : Blo 1727064 4918769 := bstep (se 2 (by rfl) ⟨1844538, by rfl⟩ : syracuseStep 4918769 = 3689077) B3689077
theorem B3886577 : Blo 1727064 3886577 := bstep (se 2 (by rfl) ⟨1457466, by rfl⟩ : syracuseStep 3886577 = 2914933) B2914933
theorem B1945075 : Blo 1727064 1945075 := bstep (se 1 (by rfl) ⟨1458806, by rfl⟩ : syracuseStep 1945075 = 2917613) B2917613
theorem B2592257 : Blo 1727064 2592257 := bstep (se 2 (by rfl) ⟨972096, by rfl⟩ : syracuseStep 2592257 = 1944193) B1944193
theorem B3886595 : Blo 1727064 3886595 := bstep (se 1 (by rfl) ⟨2914946, by rfl⟩ : syracuseStep 3886595 = 5829893) B5829893
theorem B2592275 : Blo 1727064 2592275 := bstep (se 1 (by rfl) ⟨1944206, by rfl⟩ : syracuseStep 2592275 = 3888413) B3888413
theorem B2493985 : Blo 1727064 2493985 := bstep (se 2 (by rfl) ⟨935244, by rfl⟩ : syracuseStep 2493985 = 1870489) B1870489
theorem B8302115 : Blo 1727064 8302115 := bstep (se 1 (by rfl) ⟨6226586, by rfl⟩ : syracuseStep 8302115 = 12453173) B12453173
theorem B2592305 : Blo 1727064 2592305 := bstep (se 2 (by rfl) ⟨972114, by rfl⟩ : syracuseStep 2592305 = 1944229) B1944229
theorem B2592323 : Blo 1727064 2592323 := bstep (se 1 (by rfl) ⟨1944242, by rfl⟩ : syracuseStep 2592323 = 3888485) B3888485
theorem B2592353 : Blo 1727064 2592353 := bstep (se 2 (by rfl) ⟨972132, by rfl⟩ : syracuseStep 2592353 = 1944265) B1944265
theorem B2592371 : Blo 1727064 2592371 := bstep (se 1 (by rfl) ⟨1944278, by rfl⟩ : syracuseStep 2592371 = 3888557) B3888557
theorem B2592401 : Blo 1727064 2592401 := bstep (se 2 (by rfl) ⟨972150, by rfl⟩ : syracuseStep 2592401 = 1944301) B1944301
theorem B2592419 : Blo 1727064 2592419 := bstep (se 1 (by rfl) ⟨1944314, by rfl⟩ : syracuseStep 2592419 = 3888629) B3888629
theorem B2592449 : Blo 1727064 2592449 := bstep (se 2 (by rfl) ⟨972168, by rfl⟩ : syracuseStep 2592449 = 1944337) B1944337
theorem B2592467 : Blo 1727064 2592467 := bstep (se 1 (by rfl) ⟨1944350, by rfl⟩ : syracuseStep 2592467 = 3888701) B3888701
theorem B2592497 : Blo 1727064 2592497 := bstep (se 2 (by rfl) ⟨972186, by rfl⟩ : syracuseStep 2592497 = 1944373) B1944373
theorem B2076403 : Blo 1727064 2076403 := bstep (se 1 (by rfl) ⟨1557302, by rfl⟩ : syracuseStep 2076403 = 3114605) B3114605
theorem B2592515 : Blo 1727064 2592515 := bstep (se 1 (by rfl) ⟨1944386, by rfl⟩ : syracuseStep 2592515 = 3888773) B3888773
theorem B7884557 : Blo 1727064 7884557 := bstep (se 3 (by rfl) ⟨1478354, by rfl⟩ : syracuseStep 7884557 = 2956709) B2956709
theorem B3886865 : Blo 1727064 3886865 := bstep (se 2 (by rfl) ⟨1457574, by rfl⟩ : syracuseStep 3886865 = 2915149) B2915149
theorem B2592545 : Blo 1727064 2592545 := bstep (se 2 (by rfl) ⟨972204, by rfl⟩ : syracuseStep 2592545 = 1944409) B1944409
theorem B3886883 : Blo 1727064 3886883 := bstep (se 1 (by rfl) ⟨2915162, by rfl⟩ : syracuseStep 3886883 = 5830325) B5830325
theorem B3280675 : Blo 1727064 3280675 := bstep (se 1 (by rfl) ⟨2460506, by rfl⟩ : syracuseStep 3280675 = 4921013) B4921013
theorem B3157795 : Blo 1727064 3157795 := bstep (se 1 (by rfl) ⟨2368346, by rfl⟩ : syracuseStep 3157795 = 4736693) B4736693
theorem B3690289 : Blo 1727064 3690289 := bstep (se 2 (by rfl) ⟨1383858, by rfl⟩ : syracuseStep 3690289 = 2767717) B2767717
theorem B2592563 : Blo 1727064 2592563 := bstep (se 1 (by rfl) ⟨1944422, by rfl⟩ : syracuseStep 2592563 = 3888845) B3888845
theorem B2592593 : Blo 1727064 2592593 := bstep (se 2 (by rfl) ⟨972222, by rfl⟩ : syracuseStep 2592593 = 1944445) B1944445
theorem B2461537 : Blo 1727064 2461537 := bstep (se 2 (by rfl) ⟨923076, by rfl⟩ : syracuseStep 2461537 = 1846153) B1846153
theorem B2592611 : Blo 1727064 2592611 := bstep (se 1 (by rfl) ⟨1944458, by rfl⟩ : syracuseStep 2592611 = 3888917) B3888917
theorem B2592641 : Blo 1727064 2592641 := bstep (se 2 (by rfl) ⟨972240, by rfl⟩ : syracuseStep 2592641 = 1944481) B1944481
theorem B2592659 : Blo 1727064 2592659 := bstep (se 1 (by rfl) ⟨1944494, by rfl⟩ : syracuseStep 2592659 = 3888989) B3888989
theorem B2592689 : Blo 1727064 2592689 := bstep (se 2 (by rfl) ⟨972258, by rfl⟩ : syracuseStep 2592689 = 1944517) B1944517
theorem B2592707 : Blo 1727064 2592707 := bstep (se 1 (by rfl) ⟨1944530, by rfl⟩ : syracuseStep 2592707 = 3889061) B3889061
theorem B2592737 : Blo 1727064 2592737 := bstep (se 2 (by rfl) ⟨972276, by rfl⟩ : syracuseStep 2592737 = 1944553) B1944553
theorem B22138865 : Blo 1727064 22138865 := bstep (se 2 (by rfl) ⟨8302074, by rfl⟩ : syracuseStep 22138865 = 16604149) B16604149
theorem B14970865 : Blo 1727064 14970865 := bstep (se 2 (by rfl) ⟨5614074, by rfl⟩ : syracuseStep 14970865 = 11228149) B11228149
theorem B2592755 : Blo 1727064 2592755 := bstep (se 1 (by rfl) ⟨1944566, by rfl⟩ : syracuseStep 2592755 = 3889133) B3889133
theorem B2592785 : Blo 1727064 2592785 := bstep (se 2 (by rfl) ⟨972294, by rfl⟩ : syracuseStep 2592785 = 1944589) B1944589
theorem B2592803 : Blo 1727064 2592803 := bstep (se 1 (by rfl) ⟨1944602, by rfl⟩ : syracuseStep 2592803 = 3889205) B3889205
theorem B3887153 : Blo 1727064 3887153 := bstep (se 2 (by rfl) ⟨1457682, by rfl⟩ : syracuseStep 3887153 = 2915365) B2915365
theorem B2592833 : Blo 1727064 2592833 := bstep (se 2 (by rfl) ⟨972312, by rfl⟩ : syracuseStep 2592833 = 1944625) B1944625
theorem B3887171 : Blo 1727064 3887171 := bstep (se 1 (by rfl) ⟨2915378, by rfl⟩ : syracuseStep 3887171 = 5830757) B5830757
theorem B2592851 : Blo 1727064 2592851 := bstep (se 1 (by rfl) ⟨1944638, by rfl⟩ : syracuseStep 2592851 = 3889277) B3889277
theorem B2592881 : Blo 1727064 2592881 := bstep (se 2 (by rfl) ⟨972330, by rfl⟩ : syracuseStep 2592881 = 1944661) B1944661
theorem B14020721 : Blo 1727064 14020721 := bstep (se 2 (by rfl) ⟨5257770, by rfl⟩ : syracuseStep 14020721 = 10515541) B10515541
theorem B2592899 : Blo 1727064 2592899 := bstep (se 1 (by rfl) ⟨1944674, by rfl⟩ : syracuseStep 2592899 = 3889349) B3889349
theorem B2592929 : Blo 1727064 2592929 := bstep (se 2 (by rfl) ⟨972348, by rfl⟩ : syracuseStep 2592929 = 1944697) B1944697
theorem B8302769 : Blo 1727064 8302769 := bstep (se 2 (by rfl) ⟨3113538, by rfl⟩ : syracuseStep 8302769 = 6227077) B6227077
theorem B2592947 : Blo 1727064 2592947 := bstep (se 1 (by rfl) ⟨1944710, by rfl⟩ : syracuseStep 2592947 = 3889421) B3889421
theorem B2592977 : Blo 1727064 2592977 := bstep (se 2 (by rfl) ⟨972366, by rfl⟩ : syracuseStep 2592977 = 1944733) B1944733
theorem B134615267 : Blo 1727064 134615267 := bstep (se 1 (by rfl) ⟨100961450, by rfl⟩ : syracuseStep 134615267 = 201922901) B201922901
theorem B3281123 : Blo 1727064 3281123 := bstep (se 1 (by rfl) ⟨2460842, by rfl⟩ : syracuseStep 3281123 = 4921685) B4921685
theorem B10801379 : Blo 1727064 10801379 := bstep (se 1 (by rfl) ⟨8101034, by rfl⟩ : syracuseStep 10801379 = 16202069) B16202069
theorem B2592995 : Blo 1727064 2592995 := bstep (se 1 (by rfl) ⟨1944746, by rfl⟩ : syracuseStep 2592995 = 3889493) B3889493
theorem B2593025 : Blo 1727064 2593025 := bstep (se 2 (by rfl) ⟨972384, by rfl⟩ : syracuseStep 2593025 = 1944769) B1944769
theorem B5828867 : Blo 1727064 5828867 := bstep (se 1 (by rfl) ⟨4371650, by rfl⟩ : syracuseStep 5828867 = 8743301) B8743301
theorem B4919555 : Blo 1727064 4919555 := bstep (se 1 (by rfl) ⟨3689666, by rfl⟩ : syracuseStep 4919555 = 7379333) B7379333
theorem B2593043 : Blo 1727064 2593043 := bstep (se 1 (by rfl) ⟨1944782, by rfl⟩ : syracuseStep 2593043 = 3889565) B3889565
theorem B2593073 : Blo 1727064 2593073 := bstep (se 2 (by rfl) ⟨972402, by rfl⟩ : syracuseStep 2593073 = 1944805) B1944805
theorem B2593091 : Blo 1727064 2593091 := bstep (se 1 (by rfl) ⟨1944818, by rfl⟩ : syracuseStep 2593091 = 3889637) B3889637
theorem B3887441 : Blo 1727064 3887441 := bstep (se 2 (by rfl) ⟨1457790, by rfl⟩ : syracuseStep 3887441 = 2915581) B2915581
theorem B2593121 : Blo 1727064 2593121 := bstep (se 2 (by rfl) ⟨972420, by rfl⟩ : syracuseStep 2593121 = 1944841) B1944841
theorem B3887459 : Blo 1727064 3887459 := bstep (se 1 (by rfl) ⟨2915594, by rfl⟩ : syracuseStep 3887459 = 5831189) B5831189
theorem B2593139 : Blo 1727064 2593139 := bstep (se 1 (by rfl) ⟨1944854, by rfl⟩ : syracuseStep 2593139 = 3889709) B3889709
theorem B2593169 : Blo 1727064 2593169 := bstep (se 2 (by rfl) ⟨972438, by rfl⟩ : syracuseStep 2593169 = 1944877) B1944877
theorem B2593187 : Blo 1727064 2593187 := bstep (se 1 (by rfl) ⟨1944890, by rfl⟩ : syracuseStep 2593187 = 3889781) B3889781
theorem B2593217 : Blo 1727064 2593217 := bstep (se 2 (by rfl) ⟨972456, by rfl⟩ : syracuseStep 2593217 = 1944913) B1944913
theorem B41013701 : Blo 1727064 41013701 := bstep (se 4 (by rfl) ⟨3845034, by rfl⟩ : syracuseStep 41013701 = 7690069) B7690069
theorem B2593235 : Blo 1727064 2593235 := bstep (se 1 (by rfl) ⟨1944926, by rfl⟩ : syracuseStep 2593235 = 3889853) B3889853
theorem B2593265 : Blo 1727064 2593265 := bstep (se 2 (by rfl) ⟨972474, by rfl⟩ : syracuseStep 2593265 = 1944949) B1944949
theorem B3281411 : Blo 1727064 3281411 := bstep (se 1 (by rfl) ⟨2461058, by rfl⟩ : syracuseStep 3281411 = 4922117) B4922117
theorem B2593283 : Blo 1727064 2593283 := bstep (se 1 (by rfl) ⟨1944962, by rfl⟩ : syracuseStep 2593283 = 3889925) B3889925
theorem B5829137 : Blo 1727064 5829137 := bstep (se 2 (by rfl) ⟨2185926, by rfl⟩ : syracuseStep 5829137 = 4371853) B4371853
theorem B2593313 : Blo 1727064 2593313 := bstep (se 2 (by rfl) ⟨972492, by rfl⟩ : syracuseStep 2593313 = 1944985) B1944985
theorem B2593331 : Blo 1727064 2593331 := bstep (se 1 (by rfl) ⟨1944998, by rfl⟩ : syracuseStep 2593331 = 3889997) B3889997
theorem B4919885 : Blo 1727064 4919885 := bstep (se 3 (by rfl) ⟨922478, by rfl⟩ : syracuseStep 4919885 = 1844957) B1844957
theorem B2593361 : Blo 1727064 2593361 := bstep (se 2 (by rfl) ⟨972510, by rfl⟩ : syracuseStep 2593361 = 1945021) B1945021
theorem B9597539 : Blo 1727064 9597539 := bstep (se 1 (by rfl) ⟨7198154, by rfl⟩ : syracuseStep 9597539 = 14396309) B14396309
theorem B2593379 : Blo 1727064 2593379 := bstep (se 1 (by rfl) ⟨1945034, by rfl⟩ : syracuseStep 2593379 = 3890069) B3890069
theorem B3887729 : Blo 1727064 3887729 := bstep (se 2 (by rfl) ⟨1457898, by rfl⟩ : syracuseStep 3887729 = 2915797) B2915797
theorem B2593409 : Blo 1727064 2593409 := bstep (se 2 (by rfl) ⟨972528, by rfl⟩ : syracuseStep 2593409 = 1945057) B1945057
theorem B3887747 : Blo 1727064 3887747 := bstep (se 1 (by rfl) ⟨2915810, by rfl⟩ : syracuseStep 3887747 = 5831621) B5831621
theorem B4919953 : Blo 1727064 4919953 := bstep (se 2 (by rfl) ⟨1844982, by rfl⟩ : syracuseStep 4919953 = 3689965) B3689965
theorem B2593427 : Blo 1727064 2593427 := bstep (se 1 (by rfl) ⟨1945070, by rfl⟩ : syracuseStep 2593427 = 3890141) B3890141
theorem B7377571 : Blo 1727064 7377571 := bstep (se 1 (by rfl) ⟨5533178, by rfl⟩ : syracuseStep 7377571 = 11066357) B11066357
theorem B2593457 : Blo 1727064 2593457 := bstep (se 2 (by rfl) ⟨972546, by rfl⟩ : syracuseStep 2593457 = 1945093) B1945093
theorem B2593475 : Blo 1727064 2593475 := bstep (se 1 (by rfl) ⟨1945106, by rfl⟩ : syracuseStep 2593475 = 3890213) B3890213
theorem B2593505 : Blo 1727064 2593505 := bstep (se 2 (by rfl) ⟨972564, by rfl⟩ : syracuseStep 2593505 = 1945129) B1945129
theorem B2593523 : Blo 1727064 2593523 := bstep (se 1 (by rfl) ⟨1945142, by rfl⟩ : syracuseStep 2593523 = 3890285) B3890285
theorem B2593553 : Blo 1727064 2593553 := bstep (se 2 (by rfl) ⟨972582, by rfl⟩ : syracuseStep 2593553 = 1945165) B1945165
theorem B2593571 : Blo 1727064 2593571 := bstep (se 1 (by rfl) ⟨1945178, by rfl⟩ : syracuseStep 2593571 = 3890357) B3890357
theorem B5534563 : Blo 1727064 5534563 := bstep (se 1 (by rfl) ⟨4150922, by rfl⟩ : syracuseStep 5534563 = 8301845) B8301845
theorem B12456803 : Blo 1727064 12456803 := bstep (se 1 (by rfl) ⟨9342602, by rfl⟩ : syracuseStep 12456803 = 18685205) B18685205
theorem B3888017 : Blo 1727064 3888017 := bstep (se 2 (by rfl) ⟨1458006, by rfl⟩ : syracuseStep 3888017 = 2916013) B2916013
theorem B4920227 : Blo 1727064 4920227 := bstep (se 1 (by rfl) ⟨3690170, by rfl⟩ : syracuseStep 4920227 = 7380341) B7380341
theorem B3888035 : Blo 1727064 3888035 := bstep (se 1 (by rfl) ⟨2916026, by rfl⟩ : syracuseStep 3888035 = 5832053) B5832053
theorem B6558691 : Blo 1727064 6558691 := bstep (se 1 (by rfl) ⟨4919018, by rfl⟩ : syracuseStep 6558691 = 9838037) B9838037
theorem B5534705 : Blo 1727064 5534705 := bstep (se 2 (by rfl) ⟨2075514, by rfl⟩ : syracuseStep 5534705 = 4151029) B4151029
theorem B2528275 : Blo 1727064 2528275 := bstep (se 1 (by rfl) ⟨1896206, by rfl⟩ : syracuseStep 2528275 = 3792413) B3792413
theorem B10515491 : Blo 1727064 10515491 := bstep (se 1 (by rfl) ⟨7886618, by rfl⟩ : syracuseStep 10515491 = 15773237) B15773237
theorem B5829677 : Blo 1727064 5829677 := bstep (se 3 (by rfl) ⟨1093064, by rfl⟩ : syracuseStep 5829677 = 2186129) B2186129
theorem B5829731 : Blo 1727064 5829731 := bstep (se 1 (by rfl) ⟨4372298, by rfl⟩ : syracuseStep 5829731 = 8744597) B8744597
theorem B5534819 : Blo 1727064 5534819 := bstep (se 1 (by rfl) ⟨4151114, by rfl⟩ : syracuseStep 5534819 = 8302229) B8302229
theorem B2806883 : Blo 1727064 2806883 := bstep (se 1 (by rfl) ⟨2105162, by rfl⟩ : syracuseStep 2806883 = 4210325) B4210325
theorem B13128803 : Blo 1727064 13128803 := bstep (se 1 (by rfl) ⟨9846602, by rfl⟩ : syracuseStep 13128803 = 19693205) B19693205
theorem B3888305 : Blo 1727064 3888305 := bstep (se 2 (by rfl) ⟨1458114, by rfl⟩ : syracuseStep 3888305 = 2916229) B2916229
theorem B22131893 : Blo 1727064 22131893 := bstep (se 5 (by rfl) ⟨1037432, by rfl⟩ : syracuseStep 22131893 = 2074865) B2074865
theorem B3888323 : Blo 1727064 3888323 := bstep (se 1 (by rfl) ⟨2916242, by rfl⟩ : syracuseStep 3888323 = 5832485) B5832485
theorem B4150499 : Blo 1727064 4150499 := bstep (se 1 (by rfl) ⟨3112874, by rfl⟩ : syracuseStep 4150499 = 6225749) B6225749
theorem B3691793 : Blo 1727064 3691793 := bstep (se 2 (by rfl) ⟨1384422, by rfl⟩ : syracuseStep 3691793 = 2768845) B2768845
theorem B3691811 : Blo 1727064 3691811 := bstep (se 1 (by rfl) ⟨2768858, by rfl⟩ : syracuseStep 3691811 = 5537717) B5537717
theorem B4150577 : Blo 1727064 4150577 := bstep (se 2 (by rfl) ⟨1556466, by rfl⟩ : syracuseStep 4150577 = 3112933) B3112933
theorem B8303921 : Blo 1727064 8303921 := bstep (se 2 (by rfl) ⟨3113970, by rfl⟩ : syracuseStep 8303921 = 6227941) B6227941
theorem B5830001 : Blo 1727064 5830001 := bstep (se 2 (by rfl) ⟨2186250, by rfl⟩ : syracuseStep 5830001 = 4372501) B4372501
theorem B33658253 : Blo 1727064 33658253 := bstep (se 3 (by rfl) ⟨6310922, by rfl⟩ : syracuseStep 33658253 = 12621845) B12621845
theorem B3282353 : Blo 1727064 3282353 := bstep (se 2 (by rfl) ⟨1230882, by rfl⟩ : syracuseStep 3282353 = 2461765) B2461765
theorem B3888593 : Blo 1727064 3888593 := bstep (se 2 (by rfl) ⟨1458222, by rfl⟩ : syracuseStep 3888593 = 2916445) B2916445
theorem B3888611 : Blo 1727064 3888611 := bstep (se 1 (by rfl) ⟨2916458, by rfl⟩ : syracuseStep 3888611 = 5832917) B5832917
theorem B3503665 : Blo 1727064 3503665 := bstep (se 2 (by rfl) ⟨1313874, by rfl⟩ : syracuseStep 3503665 = 2627749) B2627749
theorem B7009841 : Blo 1727064 7009841 := bstep (se 2 (by rfl) ⟨2628690, by rfl⟩ : syracuseStep 7009841 = 5257381) B5257381
theorem B2766449 : Blo 1727064 2766449 := bstep (se 2 (by rfl) ⟨1037418, by rfl⟩ : syracuseStep 2766449 = 2074837) B2074837
theorem B4372177 : Blo 1727064 4372177 := bstep (se 2 (by rfl) ⟨1639566, by rfl⟩ : syracuseStep 4372177 = 3279133) B3279133
theorem B4921069 : Blo 1727064 4921069 := bstep (se 3 (by rfl) ⟨922700, by rfl⟩ : syracuseStep 4921069 = 1845401) B1845401
theorem B3888881 : Blo 1727064 3888881 := bstep (se 2 (by rfl) ⟨1458330, by rfl⟩ : syracuseStep 3888881 = 2916661) B2916661
theorem B3888899 : Blo 1727064 3888899 := bstep (se 1 (by rfl) ⟨2916674, by rfl⟩ : syracuseStep 3888899 = 5833349) B5833349
theorem B8746865 : Blo 1727064 8746865 := bstep (se 2 (by rfl) ⟨3280074, by rfl⟩ : syracuseStep 8746865 = 6560149) B6560149
theorem B5830541 : Blo 1727064 5830541 := bstep (se 3 (by rfl) ⟨1093226, by rfl⟩ : syracuseStep 5830541 = 2186453) B2186453
theorem B4921229 : Blo 1727064 4921229 := bstep (se 3 (by rfl) ⟨922730, by rfl⟩ : syracuseStep 4921229 = 1845461) B1845461
theorem B119740301 : Blo 1727064 119740301 := bstep (se 3 (by rfl) ⟨22451306, by rfl⟩ : syracuseStep 119740301 = 44902613) B44902613
theorem B75798413 : Blo 1727064 75798413 := bstep (se 3 (by rfl) ⟨14212202, by rfl⟩ : syracuseStep 75798413 = 28424405) B28424405
theorem B5830595 : Blo 1727064 5830595 := bstep (se 1 (by rfl) ⟨4372946, by rfl⟩ : syracuseStep 5830595 = 8745893) B8745893
theorem B4372451 : Blo 1727064 4372451 := bstep (se 1 (by rfl) ⟨3279338, by rfl⟩ : syracuseStep 4372451 = 6558677) B6558677
theorem B3889169 : Blo 1727064 3889169 := bstep (se 2 (by rfl) ⟨1458438, by rfl⟩ : syracuseStep 3889169 = 2916877) B2916877
theorem B9836579 : Blo 1727064 9836579 := bstep (se 1 (by rfl) ⟨7377434, by rfl⟩ : syracuseStep 9836579 = 14754869) B14754869
theorem B3889187 : Blo 1727064 3889187 := bstep (se 1 (by rfl) ⟨2916890, by rfl⟩ : syracuseStep 3889187 = 5833781) B5833781
theorem B5535793 : Blo 1727064 5535793 := bstep (se 2 (by rfl) ⟨2075922, by rfl⟩ : syracuseStep 5535793 = 4151845) B4151845
theorem B8304689 : Blo 1727064 8304689 := bstep (se 2 (by rfl) ⟨3114258, by rfl⟩ : syracuseStep 8304689 = 6228517) B6228517
theorem B4921411 : Blo 1727064 4921411 := bstep (se 1 (by rfl) ⟨3691058, by rfl⟩ : syracuseStep 4921411 = 7382117) B7382117
theorem B4372643 : Blo 1727064 4372643 := bstep (se 1 (by rfl) ⟨3279482, by rfl⟩ : syracuseStep 4372643 = 6558965) B6558965
theorem B2914481 : Blo 1727064 2914481 := bstep (se 2 (by rfl) ⟨1092930, by rfl⟩ : syracuseStep 2914481 = 2185861) B2185861
theorem B2955457 : Blo 1727064 2955457 := bstep (se 2 (by rfl) ⟨1108296, by rfl⟩ : syracuseStep 2955457 = 2216593) B2216593
theorem B5830865 : Blo 1727064 5830865 := bstep (se 2 (by rfl) ⟨2186574, by rfl⟩ : syracuseStep 5830865 = 4373149) B4373149
theorem B19691747 : Blo 1727064 19691747 := bstep (se 1 (by rfl) ⟨14768810, by rfl⟩ : syracuseStep 19691747 = 29537621) B29537621
theorem B2914609 : Blo 1727064 2914609 := bstep (se 2 (by rfl) ⟨1092978, by rfl⟩ : syracuseStep 2914609 = 2185957) B2185957
theorem B3889457 : Blo 1727064 3889457 := bstep (se 2 (by rfl) ⟨1458546, by rfl⟩ : syracuseStep 3889457 = 2917093) B2917093
theorem B3889475 : Blo 1727064 3889475 := bstep (se 1 (by rfl) ⟨2917106, by rfl⟩ : syracuseStep 3889475 = 5834213) B5834213
theorem B2914643 : Blo 1727064 2914643 := bstep (se 1 (by rfl) ⟨2185982, by rfl⟩ : syracuseStep 2914643 = 4371965) B4371965
theorem B14006641 : Blo 1727064 14006641 := bstep (se 2 (by rfl) ⟨5252490, by rfl⟩ : syracuseStep 14006641 = 10504981) B10504981
theorem B14760305 : Blo 1727064 14760305 := bstep (se 2 (by rfl) ⟨5535114, by rfl⟩ : syracuseStep 14760305 = 11070229) B11070229
theorem B21027185 : Blo 1727064 21027185 := bstep (se 2 (by rfl) ⟨7885194, by rfl⟩ : syracuseStep 21027185 = 15770389) B15770389
theorem B2914771 : Blo 1727064 2914771 := bstep (se 1 (by rfl) ⟨2186078, by rfl⟩ : syracuseStep 2914771 = 4372157) B4372157
theorem B3889745 : Blo 1727064 3889745 := bstep (se 2 (by rfl) ⟨1458654, by rfl⟩ : syracuseStep 3889745 = 2917309) B2917309
theorem B2914913 : Blo 1727064 2914913 := bstep (se 2 (by rfl) ⟨1093092, by rfl⟩ : syracuseStep 2914913 = 2186185) B2186185
theorem B1727075 : Blo 1727064 1727075 := bstep (se 1 (by rfl) ⟨1295306, by rfl⟩ : syracuseStep 1727075 = 2590613) B2590613
theorem B3889763 : Blo 1727064 3889763 := bstep (se 1 (by rfl) ⟨2917322, by rfl⟩ : syracuseStep 3889763 = 5834645) B5834645
theorem B9337457 : Blo 1727064 9337457 := bstep (se 2 (by rfl) ⟨3501546, by rfl⟩ : syracuseStep 9337457 = 7003093) B7003093
theorem B1727091 : Blo 1727064 1727091 := bstep (se 1 (by rfl) ⟨1295318, by rfl⟩ : syracuseStep 1727091 = 2590637) B2590637
theorem B1727107 : Blo 1727064 1727107 := bstep (se 1 (by rfl) ⟨1295330, by rfl⟩ : syracuseStep 1727107 = 2590661) B2590661
theorem B1727123 : Blo 1727064 1727123 := bstep (se 1 (by rfl) ⟨1295342, by rfl⟩ : syracuseStep 1727123 = 2590685) B2590685
theorem B1727139 : Blo 1727064 1727139 := bstep (se 1 (by rfl) ⟨1295354, by rfl⟩ : syracuseStep 1727139 = 2590709) B2590709
theorem B1727155 : Blo 1727064 1727155 := bstep (se 1 (by rfl) ⟨1295366, by rfl⟩ : syracuseStep 1727155 = 2590733) B2590733
theorem B1727171 : Blo 1727064 1727171 := bstep (se 1 (by rfl) ⟨1295378, by rfl⟩ : syracuseStep 1727171 = 2590757) B2590757
theorem B1727187 : Blo 1727064 1727187 := bstep (se 1 (by rfl) ⟨1295390, by rfl⟩ : syracuseStep 1727187 = 2590781) B2590781
theorem B2915041 : Blo 1727064 2915041 := bstep (se 2 (by rfl) ⟨1093140, by rfl⟩ : syracuseStep 2915041 = 2186281) B2186281
theorem B1727203 : Blo 1727064 1727203 := bstep (se 1 (by rfl) ⟨1295402, by rfl⟩ : syracuseStep 1727203 = 2590805) B2590805
theorem B2956003 : Blo 1727064 2956003 := bstep (se 1 (by rfl) ⟨2217002, by rfl⟩ : syracuseStep 2956003 = 4434005) B4434005
theorem B91036387 : Blo 1727064 91036387 := bstep (se 1 (by rfl) ⟨68277290, by rfl⟩ : syracuseStep 91036387 = 136554581) B136554581
theorem B5831405 : Blo 1727064 5831405 := bstep (se 3 (by rfl) ⟨1093388, by rfl⟩ : syracuseStep 5831405 = 2186777) B2186777
theorem B9337585 : Blo 1727064 9337585 := bstep (se 2 (by rfl) ⟨3501594, by rfl⟩ : syracuseStep 9337585 = 7003189) B7003189
theorem B1727219 : Blo 1727064 1727219 := bstep (se 1 (by rfl) ⟨1295414, by rfl⟩ : syracuseStep 1727219 = 2590829) B2590829
theorem B1727235 : Blo 1727064 1727235 := bstep (se 1 (by rfl) ⟨1295426, by rfl⟩ : syracuseStep 1727235 = 2590853) B2590853
theorem B2915075 : Blo 1727064 2915075 := bstep (se 1 (by rfl) ⟨2186306, by rfl⟩ : syracuseStep 2915075 = 4372613) B4372613
theorem B9845509 : Blo 1727064 9845509 := bstep (se 4 (by rfl) ⟨923016, by rfl⟩ : syracuseStep 9845509 = 1846033) B1846033
theorem B1727251 : Blo 1727064 1727251 := bstep (se 1 (by rfl) ⟨1295438, by rfl⟩ : syracuseStep 1727251 = 2590877) B2590877
theorem B1727267 : Blo 1727064 1727267 := bstep (se 1 (by rfl) ⟨1295450, by rfl⟩ : syracuseStep 1727267 = 2590901) B2590901
theorem B5831459 : Blo 1727064 5831459 := bstep (se 1 (by rfl) ⟨4373594, by rfl⟩ : syracuseStep 5831459 = 8747189) B8747189
theorem B1727283 : Blo 1727064 1727283 := bstep (se 1 (by rfl) ⟨1295462, by rfl⟩ : syracuseStep 1727283 = 2590925) B2590925
theorem B1727299 : Blo 1727064 1727299 := bstep (se 1 (by rfl) ⟨1295474, by rfl⟩ : syracuseStep 1727299 = 2590949) B2590949
theorem B1727315 : Blo 1727064 1727315 := bstep (se 1 (by rfl) ⟨1295486, by rfl⟩ : syracuseStep 1727315 = 2590973) B2590973
theorem B1727331 : Blo 1727064 1727331 := bstep (se 1 (by rfl) ⟨1295498, by rfl⟩ : syracuseStep 1727331 = 2590997) B2590997
theorem B3890033 : Blo 1727064 3890033 := bstep (se 2 (by rfl) ⟨1458762, by rfl⟩ : syracuseStep 3890033 = 2917525) B2917525
theorem B1727347 : Blo 1727064 1727347 := bstep (se 1 (by rfl) ⟨1295510, by rfl⟩ : syracuseStep 1727347 = 2591021) B2591021
theorem B1727363 : Blo 1727064 1727363 := bstep (se 1 (by rfl) ⟨1295522, by rfl⟩ : syracuseStep 1727363 = 2591045) B2591045
theorem B2915203 : Blo 1727064 2915203 := bstep (se 1 (by rfl) ⟨2186402, by rfl⟩ : syracuseStep 2915203 = 4372805) B4372805
theorem B3890051 : Blo 1727064 3890051 := bstep (se 1 (by rfl) ⟨2917538, by rfl⟩ : syracuseStep 3890051 = 5835077) B5835077
theorem B3505027 : Blo 1727064 3505027 := bstep (se 1 (by rfl) ⟨2628770, by rfl⟩ : syracuseStep 3505027 = 5257541) B5257541
theorem B1727379 : Blo 1727064 1727379 := bstep (se 1 (by rfl) ⟨1295534, by rfl⟩ : syracuseStep 1727379 = 2591069) B2591069
theorem B2767763 : Blo 1727064 2767763 := bstep (se 1 (by rfl) ⟨2075822, by rfl⟩ : syracuseStep 2767763 = 4151645) B4151645
theorem B1727395 : Blo 1727064 1727395 := bstep (se 1 (by rfl) ⟨1295546, by rfl⟩ : syracuseStep 1727395 = 2591093) B2591093
theorem B1727411 : Blo 1727064 1727411 := bstep (se 1 (by rfl) ⟨1295558, by rfl⟩ : syracuseStep 1727411 = 2591117) B2591117
theorem B1727427 : Blo 1727064 1727427 := bstep (se 1 (by rfl) ⟨1295570, by rfl⟩ : syracuseStep 1727427 = 2591141) B2591141
theorem B4152259 : Blo 1727064 4152259 := bstep (se 1 (by rfl) ⟨3114194, by rfl⟩ : syracuseStep 4152259 = 6228389) B6228389
theorem B1727443 : Blo 1727064 1727443 := bstep (se 1 (by rfl) ⟨1295582, by rfl⟩ : syracuseStep 1727443 = 2591165) B2591165
theorem B1727459 : Blo 1727064 1727459 := bstep (se 1 (by rfl) ⟨1295594, by rfl⟩ : syracuseStep 1727459 = 2591189) B2591189
theorem B1727475 : Blo 1727064 1727475 := bstep (se 1 (by rfl) ⟨1295606, by rfl⟩ : syracuseStep 1727475 = 2591213) B2591213
theorem B1727491 : Blo 1727064 1727491 := bstep (se 1 (by rfl) ⟨1295618, by rfl⟩ : syracuseStep 1727491 = 2591237) B2591237
theorem B2915345 : Blo 1727064 2915345 := bstep (se 2 (by rfl) ⟨1093254, by rfl⟩ : syracuseStep 2915345 = 2186509) B2186509
theorem B1727507 : Blo 1727064 1727507 := bstep (se 1 (by rfl) ⟨1295630, by rfl⟩ : syracuseStep 1727507 = 2591261) B2591261
theorem B1727523 : Blo 1727064 1727523 := bstep (se 1 (by rfl) ⟨1295642, by rfl⟩ : syracuseStep 1727523 = 2591285) B2591285
theorem B5610541 : Blo 1727064 5610541 := bstep (se 3 (by rfl) ⟨1051976, by rfl⟩ : syracuseStep 5610541 = 2103953) B2103953
theorem B7380017 : Blo 1727064 7380017 := bstep (se 2 (by rfl) ⟨2767506, by rfl⟩ : syracuseStep 7380017 = 5535013) B5535013
theorem B5831729 : Blo 1727064 5831729 := bstep (se 2 (by rfl) ⟨2186898, by rfl⟩ : syracuseStep 5831729 = 4373797) B4373797
theorem B2186291 : Blo 1727064 2186291 := bstep (se 1 (by rfl) ⟨1639718, by rfl⟩ : syracuseStep 2186291 = 3279437) B3279437
theorem B1727539 : Blo 1727064 1727539 := bstep (se 1 (by rfl) ⟨1295654, by rfl⟩ : syracuseStep 1727539 = 2591309) B2591309
theorem B1727555 : Blo 1727064 1727555 := bstep (se 1 (by rfl) ⟨1295666, by rfl⟩ : syracuseStep 1727555 = 2591333) B2591333
theorem B4373585 : Blo 1727064 4373585 := bstep (se 2 (by rfl) ⟨1640094, by rfl⟩ : syracuseStep 4373585 = 3280189) B3280189
theorem B1727571 : Blo 1727064 1727571 := bstep (se 1 (by rfl) ⟨1295678, by rfl⟩ : syracuseStep 1727571 = 2591357) B2591357
theorem B1727587 : Blo 1727064 1727587 := bstep (se 1 (by rfl) ⟨1295690, by rfl⟩ : syracuseStep 1727587 = 2591381) B2591381
theorem B1727603 : Blo 1727064 1727603 := bstep (se 1 (by rfl) ⟨1295702, by rfl⟩ : syracuseStep 1727603 = 2591405) B2591405
theorem B1727619 : Blo 1727064 1727619 := bstep (se 1 (by rfl) ⟨1295714, by rfl⟩ : syracuseStep 1727619 = 2591429) B2591429
theorem B4373635 : Blo 1727064 4373635 := bstep (se 1 (by rfl) ⟨3280226, by rfl⟩ : syracuseStep 4373635 = 6560453) B6560453
theorem B6560909 : Blo 1727064 6560909 := bstep (se 3 (by rfl) ⟨1230170, by rfl⟩ : syracuseStep 6560909 = 2460341) B2460341
theorem B2915473 : Blo 1727064 2915473 := bstep (se 2 (by rfl) ⟨1093302, by rfl⟩ : syracuseStep 2915473 = 2186605) B2186605
theorem B1727635 : Blo 1727064 1727635 := bstep (se 1 (by rfl) ⟨1295726, by rfl⟩ : syracuseStep 1727635 = 2591453) B2591453
theorem B3890321 : Blo 1727064 3890321 := bstep (se 2 (by rfl) ⟨1458870, by rfl⟩ : syracuseStep 3890321 = 2917741) B2917741
theorem B1727651 : Blo 1727064 1727651 := bstep (se 1 (by rfl) ⟨1295738, by rfl⟩ : syracuseStep 1727651 = 2591477) B2591477
theorem B3890339 : Blo 1727064 3890339 := bstep (se 1 (by rfl) ⟨2917754, by rfl⟩ : syracuseStep 3890339 = 5835509) B5835509
theorem B1727667 : Blo 1727064 1727667 := bstep (se 1 (by rfl) ⟨1295750, by rfl⟩ : syracuseStep 1727667 = 2591501) B2591501
theorem B2915507 : Blo 1727064 2915507 := bstep (se 1 (by rfl) ⟨2186630, by rfl⟩ : syracuseStep 2915507 = 4373261) B4373261
theorem B1727683 : Blo 1727064 1727683 := bstep (se 1 (by rfl) ⟨1295762, by rfl⟩ : syracuseStep 1727683 = 2591525) B2591525
theorem B1727699 : Blo 1727064 1727699 := bstep (se 1 (by rfl) ⟨1295774, by rfl⟩ : syracuseStep 1727699 = 2591549) B2591549
theorem B1727715 : Blo 1727064 1727715 := bstep (se 1 (by rfl) ⟨1295786, by rfl⟩ : syracuseStep 1727715 = 2591573) B2591573
theorem B1727731 : Blo 1727064 1727731 := bstep (se 1 (by rfl) ⟨1295798, by rfl⟩ : syracuseStep 1727731 = 2591597) B2591597
theorem B3939587 : Blo 1727064 3939587 := bstep (se 1 (by rfl) ⟨2954690, by rfl⟩ : syracuseStep 3939587 = 5909381) B5909381
theorem B1727747 : Blo 1727064 1727747 := bstep (se 1 (by rfl) ⟨1295810, by rfl⟩ : syracuseStep 1727747 = 2591621) B2591621
theorem B4373777 : Blo 1727064 4373777 := bstep (se 2 (by rfl) ⟨1640166, by rfl⟩ : syracuseStep 4373777 = 3280333) B3280333
theorem B1727763 : Blo 1727064 1727763 := bstep (se 1 (by rfl) ⟨1295822, by rfl⟩ : syracuseStep 1727763 = 2591645) B2591645
theorem B3742993 : Blo 1727064 3742993 := bstep (se 2 (by rfl) ⟨1403622, by rfl⟩ : syracuseStep 3742993 = 2807245) B2807245
theorem B1727779 : Blo 1727064 1727779 := bstep (se 1 (by rfl) ⟨1295834, by rfl⟩ : syracuseStep 1727779 = 2591669) B2591669
theorem B8748323 : Blo 1727064 8748323 := bstep (se 1 (by rfl) ⟨6561242, by rfl⟩ : syracuseStep 8748323 = 13122485) B13122485
theorem B2915635 : Blo 1727064 2915635 := bstep (se 1 (by rfl) ⟨2186726, by rfl⟩ : syracuseStep 2915635 = 4373453) B4373453
theorem B1727795 : Blo 1727064 1727795 := bstep (se 1 (by rfl) ⟨1295846, by rfl⟩ : syracuseStep 1727795 = 2591693) B2591693
theorem B1727811 : Blo 1727064 1727811 := bstep (se 1 (by rfl) ⟨1295858, by rfl⟩ : syracuseStep 1727811 = 2591717) B2591717
theorem B1727827 : Blo 1727064 1727827 := bstep (se 1 (by rfl) ⟨1295870, by rfl⟩ : syracuseStep 1727827 = 2591741) B2591741
theorem B1727843 : Blo 1727064 1727843 := bstep (se 1 (by rfl) ⟨1295882, by rfl⟩ : syracuseStep 1727843 = 2591765) B2591765
theorem B4668785 : Blo 1727064 4668785 := bstep (se 2 (by rfl) ⟨1750794, by rfl⟩ : syracuseStep 4668785 = 3501589) B3501589
theorem B12631409 : Blo 1727064 12631409 := bstep (se 2 (by rfl) ⟨4736778, by rfl⟩ : syracuseStep 12631409 = 9473557) B9473557
theorem B1727859 : Blo 1727064 1727859 := bstep (se 1 (by rfl) ⟨1295894, by rfl⟩ : syracuseStep 1727859 = 2591789) B2591789
theorem B1727875 : Blo 1727064 1727875 := bstep (se 1 (by rfl) ⟨1295906, by rfl⟩ : syracuseStep 1727875 = 2591813) B2591813
theorem B11369861 : Blo 1727064 11369861 := bstep (se 4 (by rfl) ⟨1065924, by rfl⟩ : syracuseStep 11369861 = 2131849) B2131849
theorem B4152721 : Blo 1727064 4152721 := bstep (se 2 (by rfl) ⟨1557270, by rfl⟩ : syracuseStep 4152721 = 3114541) B3114541
theorem B1727891 : Blo 1727064 1727891 := bstep (se 1 (by rfl) ⟨1295918, by rfl⟩ : syracuseStep 1727891 = 2591837) B2591837
theorem B1727907 : Blo 1727064 1727907 := bstep (se 1 (by rfl) ⟨1295930, by rfl⟩ : syracuseStep 1727907 = 2591861) B2591861
theorem B4922801 : Blo 1727064 4922801 := bstep (se 2 (by rfl) ⟨1846050, by rfl⟩ : syracuseStep 4922801 = 3692101) B3692101
theorem B1727923 : Blo 1727064 1727923 := bstep (se 1 (by rfl) ⟨1295942, by rfl⟩ : syracuseStep 1727923 = 2591885) B2591885
theorem B2915777 : Blo 1727064 2915777 := bstep (se 2 (by rfl) ⟨1093416, by rfl⟩ : syracuseStep 2915777 = 2186833) B2186833
theorem B1727939 : Blo 1727064 1727939 := bstep (se 1 (by rfl) ⟨1295954, by rfl⟩ : syracuseStep 1727939 = 2591909) B2591909
theorem B1727955 : Blo 1727064 1727955 := bstep (se 1 (by rfl) ⟨1295966, by rfl⟩ : syracuseStep 1727955 = 2591933) B2591933
theorem B1727971 : Blo 1727064 1727971 := bstep (se 1 (by rfl) ⟨1295978, by rfl⟩ : syracuseStep 1727971 = 2591957) B2591957
theorem B1727987 : Blo 1727064 1727987 := bstep (se 1 (by rfl) ⟨1295990, by rfl⟩ : syracuseStep 1727987 = 2591981) B2591981
theorem B1728003 : Blo 1727064 1728003 := bstep (se 1 (by rfl) ⟨1296002, by rfl⟩ : syracuseStep 1728003 = 2592005) B2592005
theorem B1728019 : Blo 1727064 1728019 := bstep (se 1 (by rfl) ⟨1296014, by rfl⟩ : syracuseStep 1728019 = 2592029) B2592029
theorem B1728035 : Blo 1727064 1728035 := bstep (se 1 (by rfl) ⟨1296026, by rfl⟩ : syracuseStep 1728035 = 2592053) B2592053
theorem B4734509 : Blo 1727064 4734509 := bstep (se 3 (by rfl) ⟨887720, by rfl⟩ : syracuseStep 4734509 = 1775441) B1775441
theorem B1728051 : Blo 1727064 1728051 := bstep (se 1 (by rfl) ⟨1296038, by rfl⟩ : syracuseStep 1728051 = 2592077) B2592077
theorem B2768435 : Blo 1727064 2768435 := bstep (se 1 (by rfl) ⟨2076326, by rfl⟩ : syracuseStep 2768435 = 4152653) B4152653
theorem B2915905 : Blo 1727064 2915905 := bstep (se 2 (by rfl) ⟨1093464, by rfl⟩ : syracuseStep 2915905 = 2186929) B2186929
theorem B1728067 : Blo 1727064 1728067 := bstep (se 1 (by rfl) ⟨1296050, by rfl⟩ : syracuseStep 1728067 = 2592101) B2592101
theorem B5832269 : Blo 1727064 5832269 := bstep (se 3 (by rfl) ⟨1093550, by rfl⟩ : syracuseStep 5832269 = 2187101) B2187101
theorem B1728083 : Blo 1727064 1728083 := bstep (se 1 (by rfl) ⟨1296062, by rfl⟩ : syracuseStep 1728083 = 2592125) B2592125
theorem B2915939 : Blo 1727064 2915939 := bstep (se 1 (by rfl) ⟨2186954, by rfl⟩ : syracuseStep 2915939 = 4373909) B4373909
theorem B1728099 : Blo 1727064 1728099 := bstep (se 1 (by rfl) ⟨1296074, by rfl⟩ : syracuseStep 1728099 = 2592149) B2592149
theorem B1728115 : Blo 1727064 1728115 := bstep (se 1 (by rfl) ⟨1296086, by rfl⟩ : syracuseStep 1728115 = 2592173) B2592173
theorem B5832323 : Blo 1727064 5832323 := bstep (se 1 (by rfl) ⟨4374242, by rfl⟩ : syracuseStep 5832323 = 8748485) B8748485
theorem B1728131 : Blo 1727064 1728131 := bstep (se 1 (by rfl) ⟨1296098, by rfl⟩ : syracuseStep 1728131 = 2592197) B2592197
theorem B1728147 : Blo 1727064 1728147 := bstep (se 1 (by rfl) ⟨1296110, by rfl⟩ : syracuseStep 1728147 = 2592221) B2592221
theorem B1728163 : Blo 1727064 1728163 := bstep (se 1 (by rfl) ⟨1296122, by rfl⟩ : syracuseStep 1728163 = 2592245) B2592245
theorem B1728179 : Blo 1727064 1728179 := bstep (se 1 (by rfl) ⟨1296134, by rfl⟩ : syracuseStep 1728179 = 2592269) B2592269
theorem B1728195 : Blo 1727064 1728195 := bstep (se 1 (by rfl) ⟨1296146, by rfl⟩ : syracuseStep 1728195 = 2592293) B2592293
theorem B8306381 : Blo 1727064 8306381 := bstep (se 3 (by rfl) ⟨1557446, by rfl⟩ : syracuseStep 8306381 = 3114893) B3114893
theorem B1728211 : Blo 1727064 1728211 := bstep (se 1 (by rfl) ⟨1296158, by rfl⟩ : syracuseStep 1728211 = 2592317) B2592317
theorem B2916067 : Blo 1727064 2916067 := bstep (se 1 (by rfl) ⟨2187050, by rfl⟩ : syracuseStep 2916067 = 4374101) B4374101
theorem B1728227 : Blo 1727064 1728227 := bstep (se 1 (by rfl) ⟨1296170, by rfl⟩ : syracuseStep 1728227 = 2592341) B2592341
theorem B2186995 : Blo 1727064 2186995 := bstep (se 1 (by rfl) ⟨1640246, by rfl⟩ : syracuseStep 2186995 = 3280493) B3280493
theorem B1728243 : Blo 1727064 1728243 := bstep (se 1 (by rfl) ⟨1296182, by rfl⟩ : syracuseStep 1728243 = 2592365) B2592365
theorem B1728259 : Blo 1727064 1728259 := bstep (se 1 (by rfl) ⟨1296194, by rfl⟩ : syracuseStep 1728259 = 2592389) B2592389
theorem B1728275 : Blo 1727064 1728275 := bstep (se 1 (by rfl) ⟨1296206, by rfl⟩ : syracuseStep 1728275 = 2592413) B2592413
theorem B1728291 : Blo 1727064 1728291 := bstep (se 1 (by rfl) ⟨1296218, by rfl⟩ : syracuseStep 1728291 = 2592437) B2592437
theorem B7683889 : Blo 1727064 7683889 := bstep (se 2 (by rfl) ⟨2881458, by rfl⟩ : syracuseStep 7683889 = 5762917) B5762917
theorem B1728307 : Blo 1727064 1728307 := bstep (se 1 (by rfl) ⟨1296230, by rfl⟩ : syracuseStep 1728307 = 2592461) B2592461
theorem B1728323 : Blo 1727064 1728323 := bstep (se 1 (by rfl) ⟨1296242, by rfl⟩ : syracuseStep 1728323 = 2592485) B2592485
theorem B2187091 : Blo 1727064 2187091 := bstep (se 1 (by rfl) ⟨1640318, by rfl⟩ : syracuseStep 2187091 = 3280637) B3280637
theorem B1728339 : Blo 1727064 1728339 := bstep (se 1 (by rfl) ⟨1296254, by rfl⟩ : syracuseStep 1728339 = 2592509) B2592509
theorem B2768737 : Blo 1727064 2768737 := bstep (se 2 (by rfl) ⟨1038276, by rfl⟩ : syracuseStep 2768737 = 2076553) B2076553
theorem B1728355 : Blo 1727064 1728355 := bstep (se 1 (by rfl) ⟨1296266, by rfl⟩ : syracuseStep 1728355 = 2592533) B2592533
theorem B5611373 : Blo 1727064 5611373 := bstep (se 3 (by rfl) ⟨1052132, by rfl⟩ : syracuseStep 5611373 = 2104265) B2104265
theorem B2916209 : Blo 1727064 2916209 := bstep (se 2 (by rfl) ⟨1093578, by rfl⟩ : syracuseStep 2916209 = 2187157) B2187157
theorem B1728371 : Blo 1727064 1728371 := bstep (se 1 (by rfl) ⟨1296278, by rfl⟩ : syracuseStep 1728371 = 2592557) B2592557
theorem B1728387 : Blo 1727064 1728387 := bstep (se 1 (by rfl) ⟨1296290, by rfl⟩ : syracuseStep 1728387 = 2592581) B2592581
theorem B5832593 : Blo 1727064 5832593 := bstep (se 2 (by rfl) ⟨2187222, by rfl⟩ : syracuseStep 5832593 = 4374445) B4374445
theorem B1728403 : Blo 1727064 1728403 := bstep (se 1 (by rfl) ⟨1296302, by rfl⟩ : syracuseStep 1728403 = 2592605) B2592605
theorem B1728419 : Blo 1727064 1728419 := bstep (se 1 (by rfl) ⟨1296314, by rfl⟩ : syracuseStep 1728419 = 2592629) B2592629
theorem B1728435 : Blo 1727064 1728435 := bstep (se 1 (by rfl) ⟨1296326, by rfl⟩ : syracuseStep 1728435 = 2592653) B2592653
theorem B1728451 : Blo 1727064 1728451 := bstep (se 1 (by rfl) ⟨1296338, by rfl⟩ : syracuseStep 1728451 = 2592677) B2592677
theorem B1728467 : Blo 1727064 1728467 := bstep (se 1 (by rfl) ⟨1296350, by rfl⟩ : syracuseStep 1728467 = 2592701) B2592701
theorem B1728483 : Blo 1727064 1728483 := bstep (se 1 (by rfl) ⟨1296362, by rfl⟩ : syracuseStep 1728483 = 2592725) B2592725
theorem B2916337 : Blo 1727064 2916337 := bstep (se 2 (by rfl) ⟨1093626, by rfl⟩ : syracuseStep 2916337 = 2187253) B2187253
theorem B1728499 : Blo 1727064 1728499 := bstep (se 1 (by rfl) ⟨1296374, by rfl⟩ : syracuseStep 1728499 = 2592749) B2592749
theorem B6225923 : Blo 1727064 6225923 := bstep (se 1 (by rfl) ⟨4669442, by rfl⟩ : syracuseStep 6225923 = 9338885) B9338885
theorem B1728523 : Blo 1727064 1728523 := bstep (se 1 (by rfl) ⟨1296392, by rfl⟩ : syracuseStep 1728523 = 2592785) B2592785
theorem B1728535 : Blo 1727064 1728535 := bstep (se 1 (by rfl) ⟨1296401, by rfl⟩ : syracuseStep 1728535 = 2592803) B2592803
theorem B3112985 : Blo 1727064 3112985 := bstep (se 2 (by rfl) ⟨1167369, by rfl⟩ : syracuseStep 3112985 = 2334739) B2334739
theorem B1728555 : Blo 1727064 1728555 := bstep (se 1 (by rfl) ⟨1296416, by rfl⟩ : syracuseStep 1728555 = 2592833) B2592833
theorem B5832755 : Blo 1727064 5832755 := bstep (se 1 (by rfl) ⟨4374566, by rfl⟩ : syracuseStep 5832755 = 8749133) B8749133
theorem B1728567 : Blo 1727064 1728567 := bstep (se 1 (by rfl) ⟨1296425, by rfl⟩ : syracuseStep 1728567 = 2592851) B2592851
theorem B7381057 : Blo 1727064 7381057 := bstep (se 2 (by rfl) ⟨2767896, by rfl⟩ : syracuseStep 7381057 = 5535793) B5535793
theorem B1728587 : Blo 1727064 1728587 := bstep (se 1 (by rfl) ⟨1296440, by rfl⟩ : syracuseStep 1728587 = 2592881) B2592881
theorem B9347147 : Blo 1727064 9347147 := bstep (se 1 (by rfl) ⟨7010360, by rfl⟩ : syracuseStep 9347147 = 14020721) B14020721
theorem B1728599 : Blo 1727064 1728599 := bstep (se 1 (by rfl) ⟨1296449, by rfl⟩ : syracuseStep 1728599 = 2592899) B2592899
theorem B6561881 : Blo 1727064 6561881 := bstep (se 2 (by rfl) ⟨2460705, by rfl⟩ : syracuseStep 6561881 = 4921411) B4921411
theorem B1728619 : Blo 1727064 1728619 := bstep (se 1 (by rfl) ⟨1296464, by rfl⟩ : syracuseStep 1728619 = 2592929) B2592929
theorem B1728631 : Blo 1727064 1728631 := bstep (se 1 (by rfl) ⟨1296473, by rfl⟩ : syracuseStep 1728631 = 2592947) B2592947
theorem B1728651 : Blo 1727064 1728651 := bstep (se 1 (by rfl) ⟨1296488, by rfl⟩ : syracuseStep 1728651 = 2592977) B2592977
theorem B89743511 : Blo 1727064 89743511 := bstep (se 1 (by rfl) ⟨67307633, by rfl⟩ : syracuseStep 89743511 = 134615267) B134615267
theorem B2187415 : Blo 1727064 2187415 := bstep (se 1 (by rfl) ⟨1640561, by rfl⟩ : syracuseStep 2187415 = 3281123) B3281123
theorem B7200919 : Blo 1727064 7200919 := bstep (se 1 (by rfl) ⟨5400689, by rfl⟩ : syracuseStep 7200919 = 10801379) B10801379
theorem B1728663 : Blo 1727064 1728663 := bstep (se 1 (by rfl) ⟨1296497, by rfl⟩ : syracuseStep 1728663 = 2592995) B2592995
theorem B1728683 : Blo 1727064 1728683 := bstep (se 1 (by rfl) ⟨1296512, by rfl⟩ : syracuseStep 1728683 = 2593025) B2593025
theorem B1728695 : Blo 1727064 1728695 := bstep (se 1 (by rfl) ⟨1296521, by rfl⟩ : syracuseStep 1728695 = 2593043) B2593043
theorem B1728715 : Blo 1727064 1728715 := bstep (se 1 (by rfl) ⟨1296536, by rfl⟩ : syracuseStep 1728715 = 2593073) B2593073
theorem B1728727 : Blo 1727064 1728727 := bstep (se 1 (by rfl) ⟨1296545, by rfl⟩ : syracuseStep 1728727 = 2593091) B2593091
theorem B1728747 : Blo 1727064 1728747 := bstep (se 1 (by rfl) ⟨1296560, by rfl⟩ : syracuseStep 1728747 = 2593121) B2593121
theorem B1728759 : Blo 1727064 1728759 := bstep (se 1 (by rfl) ⟨1296569, by rfl⟩ : syracuseStep 1728759 = 2593139) B2593139
theorem B1728779 : Blo 1727064 1728779 := bstep (se 1 (by rfl) ⟨1296584, by rfl⟩ : syracuseStep 1728779 = 2593169) B2593169
theorem B1728791 : Blo 1727064 1728791 := bstep (se 1 (by rfl) ⟨1296593, by rfl⟩ : syracuseStep 1728791 = 2593187) B2593187
theorem B1728811 : Blo 1727064 1728811 := bstep (se 1 (by rfl) ⟨1296608, by rfl⟩ : syracuseStep 1728811 = 2593217) B2593217
theorem B8986925 : Blo 1727064 8986925 := bstep (se 3 (by rfl) ⟨1685048, by rfl⟩ : syracuseStep 8986925 = 3370097) B3370097
theorem B6562093 : Blo 1727064 6562093 := bstep (se 3 (by rfl) ⟨1230392, by rfl⟩ : syracuseStep 6562093 = 2460785) B2460785
theorem B1728823 : Blo 1727064 1728823 := bstep (se 1 (by rfl) ⟨1296617, by rfl⟩ : syracuseStep 1728823 = 2593235) B2593235
theorem B5833025 : Blo 1727064 5833025 := bstep (se 2 (by rfl) ⟨2187384, by rfl⟩ : syracuseStep 5833025 = 4374769) B4374769
theorem B1728843 : Blo 1727064 1728843 := bstep (se 1 (by rfl) ⟨1296632, by rfl⟩ : syracuseStep 1728843 = 2593265) B2593265
theorem B2916695 : Blo 1727064 2916695 := bstep (se 1 (by rfl) ⟨2187521, by rfl⟩ : syracuseStep 2916695 = 4375043) B4375043
theorem B1728855 : Blo 1727064 1728855 := bstep (se 1 (by rfl) ⟨1296641, by rfl⟩ : syracuseStep 1728855 = 2593283) B2593283
theorem B1728875 : Blo 1727064 1728875 := bstep (se 1 (by rfl) ⟨1296656, by rfl⟩ : syracuseStep 1728875 = 2593313) B2593313
theorem B1728887 : Blo 1727064 1728887 := bstep (se 1 (by rfl) ⟨1296665, by rfl⟩ : syracuseStep 1728887 = 2593331) B2593331
theorem B1728907 : Blo 1727064 1728907 := bstep (se 1 (by rfl) ⟨1296680, by rfl⟩ : syracuseStep 1728907 = 2593361) B2593361
theorem B6398359 : Blo 1727064 6398359 := bstep (se 1 (by rfl) ⟨4798769, by rfl⟩ : syracuseStep 6398359 = 9597539) B9597539
theorem B1728919 : Blo 1727064 1728919 := bstep (se 1 (by rfl) ⟨1296689, by rfl⟩ : syracuseStep 1728919 = 2593379) B2593379
theorem B1728939 : Blo 1727064 1728939 := bstep (se 1 (by rfl) ⟨1296704, by rfl⟩ : syracuseStep 1728939 = 2593409) B2593409
theorem B6226355 : Blo 1727064 6226355 := bstep (se 1 (by rfl) ⟨4669766, by rfl⟩ : syracuseStep 6226355 = 9339533) B9339533
theorem B1728951 : Blo 1727064 1728951 := bstep (se 1 (by rfl) ⟨1296713, by rfl⟩ : syracuseStep 1728951 = 2593427) B2593427
theorem B1728971 : Blo 1727064 1728971 := bstep (se 1 (by rfl) ⟨1296728, by rfl⟩ : syracuseStep 1728971 = 2593457) B2593457
theorem B12460493 : Blo 1727064 12460493 := bstep (se 3 (by rfl) ⟨2336342, by rfl⟩ : syracuseStep 12460493 = 4672685) B4672685
theorem B2916823 : Blo 1727064 2916823 := bstep (se 1 (by rfl) ⟨2187617, by rfl⟩ : syracuseStep 2916823 = 4375235) B4375235
theorem B1728983 : Blo 1727064 1728983 := bstep (se 1 (by rfl) ⟨1296737, by rfl⟩ : syracuseStep 1728983 = 2593475) B2593475
theorem B1729003 : Blo 1727064 1729003 := bstep (se 1 (by rfl) ⟨1296752, by rfl⟩ : syracuseStep 1729003 = 2593505) B2593505
theorem B1729015 : Blo 1727064 1729015 := bstep (se 1 (by rfl) ⟨1296761, by rfl⟩ : syracuseStep 1729015 = 2593523) B2593523
theorem B1729035 : Blo 1727064 1729035 := bstep (se 1 (by rfl) ⟨1296776, by rfl⟩ : syracuseStep 1729035 = 2593553) B2593553
theorem B1729047 : Blo 1727064 1729047 := bstep (se 1 (by rfl) ⟨1296785, by rfl⟩ : syracuseStep 1729047 = 2593571) B2593571
theorem B11067997 : Blo 1727064 11067997 := bstep (se 3 (by rfl) ⟨2075249, by rfl⟩ : syracuseStep 11067997 = 4150499) B4150499
theorem B6562397 : Blo 1727064 6562397 := bstep (se 3 (by rfl) ⟨1230449, by rfl⟩ : syracuseStep 6562397 = 2460899) B2460899
theorem B14754595 : Blo 1727064 14754595 := bstep (se 1 (by rfl) ⟨11065946, by rfl⟩ : syracuseStep 14754595 = 22131893) B22131893
theorem B5833565 : Blo 1727064 5833565 := bstep (se 3 (by rfl) ⟨1093793, by rfl⟩ : syracuseStep 5833565 = 2187587) B2187587
theorem B22438835 : Blo 1727064 22438835 := bstep (se 1 (by rfl) ⟨16829126, by rfl⟩ : syracuseStep 22438835 = 33658253) B33658253
theorem B2188235 : Blo 1727064 2188235 := bstep (se 1 (by rfl) ⟨1641176, by rfl⟩ : syracuseStep 2188235 = 3282353) B3282353
theorem B121381849 : Blo 1727064 121381849 := bstep (se 2 (by rfl) ⟨45518193, by rfl⟩ : syracuseStep 121381849 = 91036387) B91036387
theorem B15762437 : Blo 1727064 15762437 := bstep (se 4 (by rfl) ⟨1477728, by rfl⟩ : syracuseStep 15762437 = 2955457) B2955457
theorem B12452881 : Blo 1727064 12452881 := bstep (se 2 (by rfl) ⟨4669830, by rfl⟩ : syracuseStep 12452881 = 9339661) B9339661
theorem B49832981 : Blo 1727064 49832981 := bstep (se 6 (by rfl) ⟨1167960, by rfl⟩ : syracuseStep 49832981 = 2335921) B2335921
theorem B1844299 : Blo 1727064 1844299 := bstep (se 1 (by rfl) ⟨1383224, by rfl⟩ : syracuseStep 1844299 = 2766449) B2766449
theorem B2917451 : Blo 1727064 2917451 := bstep (se 1 (by rfl) ⟨2188088, by rfl⟩ : syracuseStep 2917451 = 4376177) B4376177
theorem B8307805 : Blo 1727064 8307805 := bstep (se 3 (by rfl) ⟨1557713, by rfl⟩ : syracuseStep 8307805 = 3115427) B3115427
theorem B2917579 : Blo 1727064 2917579 := bstep (se 1 (by rfl) ⟨2188184, by rfl⟩ : syracuseStep 2917579 = 4376369) B4376369
theorem B4375883 : Blo 1727064 4375883 := bstep (se 1 (by rfl) ⟨3281912, by rfl⟩ : syracuseStep 4375883 = 6563825) B6563825
theorem B2917721 : Blo 1727064 2917721 := bstep (se 2 (by rfl) ⟨1094145, by rfl⟩ : syracuseStep 2917721 = 2188291) B2188291
theorem B8750429 : Blo 1727064 8750429 := bstep (se 3 (by rfl) ⟨1640705, by rfl⟩ : syracuseStep 8750429 = 3281411) B3281411
theorem B7480721 : Blo 1727064 7480721 := bstep (se 2 (by rfl) ⟨2805270, by rfl⟩ : syracuseStep 7480721 = 5610541) B5610541
theorem B1942987 : Blo 1727064 1942987 := bstep (se 1 (by rfl) ⟨1457240, by rfl⟩ : syracuseStep 1942987 = 2914481) B2914481
theorem B12625357 : Blo 1727064 12625357 := bstep (se 3 (by rfl) ⟨2367254, by rfl⟩ : syracuseStep 12625357 = 4734509) B4734509
theorem B6227479 : Blo 1727064 6227479 := bstep (se 1 (by rfl) ⟨4670609, by rfl⟩ : syracuseStep 6227479 = 9341219) B9341219
theorem B1943095 : Blo 1727064 1943095 := bstep (se 1 (by rfl) ⟨1457321, by rfl⟩ : syracuseStep 1943095 = 2914643) B2914643
theorem B9840203 : Blo 1727064 9840203 := bstep (se 1 (by rfl) ⟨7380152, by rfl⟩ : syracuseStep 9840203 = 14760305) B14760305
theorem B14018123 : Blo 1727064 14018123 := bstep (se 1 (by rfl) ⟨10513592, by rfl⟩ : syracuseStep 14018123 = 21027185) B21027185
theorem B112117445 : Blo 1727064 112117445 := bstep (se 4 (by rfl) ⟨10511010, by rfl⟩ : syracuseStep 112117445 = 21022021) B21022021
theorem B1943275 : Blo 1727064 1943275 := bstep (se 1 (by rfl) ⟨1457456, by rfl⟩ : syracuseStep 1943275 = 2914913) B2914913
theorem B1943383 : Blo 1727064 1943383 := bstep (se 1 (by rfl) ⟨1457537, by rfl⟩ : syracuseStep 1943383 = 2915075) B2915075
theorem B3278731 : Blo 1727064 3278731 := bstep (se 1 (by rfl) ⟨2459048, by rfl⟩ : syracuseStep 3278731 = 4918097) B4918097
theorem B33220529 : Blo 1727064 33220529 := bstep (se 2 (by rfl) ⟨12457698, by rfl⟩ : syracuseStep 33220529 = 24915397) B24915397
theorem B1845175 : Blo 1727064 1845175 := bstep (se 1 (by rfl) ⟨1383881, by rfl⟩ : syracuseStep 1845175 = 2767763) B2767763
theorem B2590667 : Blo 1727064 2590667 := bstep (se 1 (by rfl) ⟨1943000, by rfl⟩ : syracuseStep 2590667 = 3886001) B3886001
theorem B5834699 : Blo 1727064 5834699 := bstep (se 1 (by rfl) ⟨4376024, by rfl⟩ : syracuseStep 5834699 = 8752049) B8752049
theorem B2590679 : Blo 1727064 2590679 := bstep (se 1 (by rfl) ⟨1943009, by rfl⟩ : syracuseStep 2590679 = 3886019) B3886019
theorem B1943563 : Blo 1727064 1943563 := bstep (se 1 (by rfl) ⟨1457672, by rfl⟩ : syracuseStep 1943563 = 2915345) B2915345
theorem B2590745 : Blo 1727064 2590745 := bstep (se 2 (by rfl) ⟨971529, by rfl⟩ : syracuseStep 2590745 = 1943059) B1943059
theorem B4671553 : Blo 1727064 4671553 := bstep (se 2 (by rfl) ⟨1751832, by rfl⟩ : syracuseStep 4671553 = 3503665) B3503665
theorem B2459737 : Blo 1727064 2459737 := bstep (se 2 (by rfl) ⟨922401, by rfl⟩ : syracuseStep 2459737 = 1844803) B1844803
theorem B1943671 : Blo 1727064 1943671 := bstep (se 1 (by rfl) ⟨1457753, by rfl⟩ : syracuseStep 1943671 = 2915507) B2915507
theorem B2590859 : Blo 1727064 2590859 := bstep (se 1 (by rfl) ⟨1943144, by rfl⟩ : syracuseStep 2590859 = 3886289) B3886289
theorem B2590871 : Blo 1727064 2590871 := bstep (se 1 (by rfl) ⟨1943153, by rfl⟩ : syracuseStep 2590871 = 3886307) B3886307
theorem B2590937 : Blo 1727064 2590937 := bstep (se 2 (by rfl) ⟨971601, by rfl⟩ : syracuseStep 2590937 = 1943203) B1943203
theorem B5834969 : Blo 1727064 5834969 := bstep (se 2 (by rfl) ⟨2188113, by rfl⟩ : syracuseStep 5834969 = 4376227) B4376227
theorem B7579907 : Blo 1727064 7579907 := bstep (se 1 (by rfl) ⟨5684930, by rfl⟩ : syracuseStep 7579907 = 11369861) B11369861
theorem B1943851 : Blo 1727064 1943851 := bstep (se 1 (by rfl) ⟨1457888, by rfl⟩ : syracuseStep 1943851 = 2915777) B2915777
theorem B3279179 : Blo 1727064 3279179 := bstep (se 1 (by rfl) ⟨2459384, by rfl⟩ : syracuseStep 3279179 = 4918769) B4918769
theorem B2591051 : Blo 1727064 2591051 := bstep (se 1 (by rfl) ⟨1943288, by rfl⟩ : syracuseStep 2591051 = 3886577) B3886577
theorem B2591063 : Blo 1727064 2591063 := bstep (se 1 (by rfl) ⟨1943297, by rfl⟩ : syracuseStep 2591063 = 3886595) B3886595
theorem B1845623 : Blo 1727064 1845623 := bstep (se 1 (by rfl) ⟨1384217, by rfl⟩ : syracuseStep 1845623 = 2768435) B2768435
theorem B1943959 : Blo 1727064 1943959 := bstep (se 1 (by rfl) ⟨1457969, by rfl⟩ : syracuseStep 1943959 = 2915939) B2915939
theorem B2591129 : Blo 1727064 2591129 := bstep (se 2 (by rfl) ⟨971673, by rfl⟩ : syracuseStep 2591129 = 1943347) B1943347
theorem B3279361 : Blo 1727064 3279361 := bstep (se 2 (by rfl) ⟨1229760, by rfl⟩ : syracuseStep 3279361 = 2459521) B2459521
theorem B2591243 : Blo 1727064 2591243 := bstep (se 1 (by rfl) ⟨1943432, by rfl⟩ : syracuseStep 2591243 = 3886865) B3886865
theorem B2591255 : Blo 1727064 2591255 := bstep (se 1 (by rfl) ⟨1943441, by rfl⟩ : syracuseStep 2591255 = 3886883) B3886883
theorem B3115585 : Blo 1727064 3115585 := bstep (se 2 (by rfl) ⟨1168344, by rfl⟩ : syracuseStep 3115585 = 2336689) B2336689
theorem B1944139 : Blo 1727064 1944139 := bstep (se 1 (by rfl) ⟨1458104, by rfl⟩ : syracuseStep 1944139 = 2916209) B2916209
theorem B2591321 : Blo 1727064 2591321 := bstep (se 2 (by rfl) ⟨971745, by rfl⟩ : syracuseStep 2591321 = 1943491) B1943491
theorem B1944247 : Blo 1727064 1944247 := bstep (se 1 (by rfl) ⟨1458185, by rfl⟩ : syracuseStep 1944247 = 2916371) B2916371
theorem B2591435 : Blo 1727064 2591435 := bstep (se 1 (by rfl) ⟨1943576, by rfl⟩ : syracuseStep 2591435 = 3887153) B3887153
theorem B2591447 : Blo 1727064 2591447 := bstep (se 1 (by rfl) ⟨1943585, by rfl⟩ : syracuseStep 2591447 = 3887171) B3887171
theorem B1845995 : Blo 1727064 1845995 := bstep (se 1 (by rfl) ⟨1384496, by rfl⟩ : syracuseStep 1845995 = 2768993) B2768993
theorem B2591513 : Blo 1727064 2591513 := bstep (se 2 (by rfl) ⟨971817, by rfl⟩ : syracuseStep 2591513 = 1943635) B1943635
theorem B3885911 : Blo 1727064 3885911 := bstep (se 1 (by rfl) ⟨2914433, by rfl⟩ : syracuseStep 3885911 = 5828867) B5828867
theorem B3279703 : Blo 1727064 3279703 := bstep (se 1 (by rfl) ⟨2459777, by rfl⟩ : syracuseStep 3279703 = 4919555) B4919555
theorem B1944427 : Blo 1727064 1944427 := bstep (se 1 (by rfl) ⟨1458320, by rfl⟩ : syracuseStep 1944427 = 2916641) B2916641
theorem B2591627 : Blo 1727064 2591627 := bstep (se 1 (by rfl) ⟨1943720, by rfl⟩ : syracuseStep 2591627 = 3887441) B3887441
theorem B2591639 : Blo 1727064 2591639 := bstep (se 1 (by rfl) ⟨1943729, by rfl⟩ : syracuseStep 2591639 = 3887459) B3887459
theorem B1944535 : Blo 1727064 1944535 := bstep (se 1 (by rfl) ⟨1458401, by rfl⟩ : syracuseStep 1944535 = 2916803) B2916803
theorem B2591705 : Blo 1727064 2591705 := bstep (se 2 (by rfl) ⟨971889, by rfl⟩ : syracuseStep 2591705 = 1943779) B1943779
theorem B3886091 : Blo 1727064 3886091 := bstep (se 1 (by rfl) ⟨2914568, by rfl⟩ : syracuseStep 3886091 = 5829137) B5829137
theorem B42036259 : Blo 1727064 42036259 := bstep (se 1 (by rfl) ⟨31527194, by rfl⟩ : syracuseStep 42036259 = 63054389) B63054389
theorem B3279923 : Blo 1727064 3279923 := bstep (se 1 (by rfl) ⟨2459942, by rfl⟩ : syracuseStep 3279923 = 4919885) B4919885
theorem B3886145 : Blo 1727064 3886145 := bstep (se 2 (by rfl) ⟨1457304, by rfl⟩ : syracuseStep 3886145 = 2914609) B2914609
theorem B2591819 : Blo 1727064 2591819 := bstep (se 1 (by rfl) ⟨1943864, by rfl⟩ : syracuseStep 2591819 = 3887729) B3887729
theorem B2591831 : Blo 1727064 2591831 := bstep (se 1 (by rfl) ⟨1943873, by rfl⟩ : syracuseStep 2591831 = 3887747) B3887747
theorem B6564995 : Blo 1727064 6564995 := bstep (se 1 (by rfl) ⟨4923746, by rfl⟩ : syracuseStep 6564995 = 9847493) B9847493
theorem B1944715 : Blo 1727064 1944715 := bstep (se 1 (by rfl) ⟨1458536, by rfl⟩ : syracuseStep 1944715 = 2917073) B2917073
theorem B6565009 : Blo 1727064 6565009 := bstep (se 2 (by rfl) ⟨2461878, by rfl⟩ : syracuseStep 6565009 = 4923757) B4923757
theorem B2591897 : Blo 1727064 2591897 := bstep (se 2 (by rfl) ⟨971961, by rfl⟩ : syracuseStep 2591897 = 1943923) B1943923
theorem B1944823 : Blo 1727064 1944823 := bstep (se 1 (by rfl) ⟨1458617, by rfl⟩ : syracuseStep 1944823 = 2917235) B2917235
theorem B2592011 : Blo 1727064 2592011 := bstep (se 1 (by rfl) ⟨1944008, by rfl⟩ : syracuseStep 2592011 = 3888017) B3888017
theorem B3280151 : Blo 1727064 3280151 := bstep (se 1 (by rfl) ⟨2460113, by rfl⟩ : syracuseStep 3280151 = 4920227) B4920227
theorem B2592023 : Blo 1727064 2592023 := bstep (se 1 (by rfl) ⟨1944017, by rfl⟩ : syracuseStep 2592023 = 3888035) B3888035
theorem B3886361 : Blo 1727064 3886361 := bstep (se 2 (by rfl) ⟨1457385, by rfl⟩ : syracuseStep 3886361 = 2914771) B2914771
theorem B3689803 : Blo 1727064 3689803 := bstep (se 1 (by rfl) ⟨2767352, by rfl⟩ : syracuseStep 3689803 = 5534705) B5534705
theorem B2592089 : Blo 1727064 2592089 := bstep (se 2 (by rfl) ⟨972033, by rfl⟩ : syracuseStep 2592089 = 1944067) B1944067
theorem B3886451 : Blo 1727064 3886451 := bstep (se 1 (by rfl) ⟨2914838, by rfl⟩ : syracuseStep 3886451 = 5829677) B5829677
theorem B3886487 : Blo 1727064 3886487 := bstep (se 1 (by rfl) ⟨2914865, by rfl⟩ : syracuseStep 3886487 = 5829731) B5829731
theorem B3689879 : Blo 1727064 3689879 := bstep (se 1 (by rfl) ⟨2767409, by rfl⟩ : syracuseStep 3689879 = 5534819) B5534819
theorem B1871255 : Blo 1727064 1871255 := bstep (se 1 (by rfl) ⟨1403441, by rfl⟩ : syracuseStep 1871255 = 2806883) B2806883
theorem B8752535 : Blo 1727064 8752535 := bstep (se 1 (by rfl) ⟨6564401, by rfl⟩ : syracuseStep 8752535 = 13128803) B13128803
theorem B1945003 : Blo 1727064 1945003 := bstep (se 1 (by rfl) ⟨1458752, by rfl⟩ : syracuseStep 1945003 = 2917505) B2917505
theorem B2592203 : Blo 1727064 2592203 := bstep (se 1 (by rfl) ⟨1944152, by rfl⟩ : syracuseStep 2592203 = 3888305) B3888305
theorem B2592215 : Blo 1727064 2592215 := bstep (se 1 (by rfl) ⟨1944161, by rfl⟩ : syracuseStep 2592215 = 3888323) B3888323
theorem B4918745 : Blo 1727064 4918745 := bstep (se 2 (by rfl) ⟨1844529, by rfl⟩ : syracuseStep 4918745 = 3689059) B3689059
theorem B2461195 : Blo 1727064 2461195 := bstep (se 1 (by rfl) ⟨1845896, by rfl⟩ : syracuseStep 2461195 = 3691793) B3691793
theorem B2461207 : Blo 1727064 2461207 := bstep (se 1 (by rfl) ⟨1845905, by rfl⟩ : syracuseStep 2461207 = 3691811) B3691811
theorem B3280409 : Blo 1727064 3280409 := bstep (se 2 (by rfl) ⟨1230153, by rfl⟩ : syracuseStep 3280409 = 2460307) B2460307
theorem B2592281 : Blo 1727064 2592281 := bstep (se 2 (by rfl) ⟨972105, by rfl⟩ : syracuseStep 2592281 = 1944211) B1944211
theorem B1945111 : Blo 1727064 1945111 := bstep (se 1 (by rfl) ⟨1458833, by rfl⟩ : syracuseStep 1945111 = 2917667) B2917667
theorem B3886667 : Blo 1727064 3886667 := bstep (se 1 (by rfl) ⟨2915000, by rfl⟩ : syracuseStep 3886667 = 5830001) B5830001
theorem B3886721 : Blo 1727064 3886721 := bstep (se 2 (by rfl) ⟨1457520, by rfl⟩ : syracuseStep 3886721 = 2915041) B2915041
theorem B2592395 : Blo 1727064 2592395 := bstep (se 1 (by rfl) ⟨1944296, by rfl⟩ : syracuseStep 2592395 = 3888593) B3888593
theorem B2592407 : Blo 1727064 2592407 := bstep (se 1 (by rfl) ⟨1944305, by rfl⟩ : syracuseStep 2592407 = 3888611) B3888611
theorem B13127345 : Blo 1727064 13127345 := bstep (se 2 (by rfl) ⟨4922754, by rfl⟩ : syracuseStep 13127345 = 9845509) B9845509
theorem B4673227 : Blo 1727064 4673227 := bstep (se 1 (by rfl) ⟨3504920, by rfl⟩ : syracuseStep 4673227 = 7009841) B7009841
theorem B2592473 : Blo 1727064 2592473 := bstep (se 2 (by rfl) ⟨972177, by rfl⟩ : syracuseStep 2592473 = 1944355) B1944355
theorem B16617221 : Blo 1727064 16617221 := bstep (se 4 (by rfl) ⟨1557864, by rfl⟩ : syracuseStep 16617221 = 3115729) B3115729
theorem B2592587 : Blo 1727064 2592587 := bstep (se 1 (by rfl) ⟨1944440, by rfl⟩ : syracuseStep 2592587 = 3888881) B3888881
theorem B2592599 : Blo 1727064 2592599 := bstep (se 1 (by rfl) ⟨1944449, by rfl⟩ : syracuseStep 2592599 = 3888899) B3888899
theorem B3886937 : Blo 1727064 3886937 := bstep (se 2 (by rfl) ⟨1457601, by rfl⟩ : syracuseStep 3886937 = 2915203) B2915203
theorem B4673369 : Blo 1727064 4673369 := bstep (se 2 (by rfl) ⟨1752513, by rfl⟩ : syracuseStep 4673369 = 3505027) B3505027
theorem B15765349 : Blo 1727064 15765349 := bstep (se 4 (by rfl) ⟨1478001, by rfl⟩ : syracuseStep 15765349 = 2956003) B2956003
theorem B2592665 : Blo 1727064 2592665 := bstep (se 2 (by rfl) ⟨972249, by rfl⟩ : syracuseStep 2592665 = 1944499) B1944499
theorem B3887027 : Blo 1727064 3887027 := bstep (se 1 (by rfl) ⟨2915270, by rfl⟩ : syracuseStep 3887027 = 5830541) B5830541
theorem B3280819 : Blo 1727064 3280819 := bstep (se 1 (by rfl) ⟨2460614, by rfl⟩ : syracuseStep 3280819 = 4921229) B4921229
theorem B79826867 : Blo 1727064 79826867 := bstep (se 1 (by rfl) ⟨59870150, by rfl⟩ : syracuseStep 79826867 = 119740301) B119740301
theorem B50532275 : Blo 1727064 50532275 := bstep (se 1 (by rfl) ⟨37899206, by rfl⟩ : syracuseStep 50532275 = 75798413) B75798413
theorem B3887063 : Blo 1727064 3887063 := bstep (se 1 (by rfl) ⟨2915297, by rfl⟩ : syracuseStep 3887063 = 5830595) B5830595
theorem B8744921 : Blo 1727064 8744921 := bstep (se 2 (by rfl) ⟨3279345, by rfl⟩ : syracuseStep 8744921 = 6558691) B6558691
theorem B2592779 : Blo 1727064 2592779 := bstep (se 1 (by rfl) ⟨1944584, by rfl⟩ : syracuseStep 2592779 = 3889169) B3889169
theorem B6557719 : Blo 1727064 6557719 := bstep (se 1 (by rfl) ⟨4918289, by rfl⟩ : syracuseStep 6557719 = 9836579) B9836579
theorem B2592791 : Blo 1727064 2592791 := bstep (se 1 (by rfl) ⟨1944593, by rfl⟩ : syracuseStep 2592791 = 3889187) B3889187
theorem B3371033 : Blo 1727064 3371033 := bstep (se 2 (by rfl) ⟨1264137, by rfl⟩ : syracuseStep 3371033 = 2528275) B2528275
theorem B2592857 : Blo 1727064 2592857 := bstep (se 2 (by rfl) ⟨972321, by rfl⟩ : syracuseStep 2592857 = 1944643) B1944643
theorem B3887243 : Blo 1727064 3887243 := bstep (se 1 (by rfl) ⟨2915432, by rfl⟩ : syracuseStep 3887243 = 5830865) B5830865
theorem B13127831 : Blo 1727064 13127831 := bstep (se 1 (by rfl) ⟨9845873, by rfl⟩ : syracuseStep 13127831 = 19691747) B19691747
theorem B9842867 : Blo 1727064 9842867 := bstep (se 1 (by rfl) ⟨7382150, by rfl⟩ : syracuseStep 9842867 = 14764301) B14764301
theorem B3887297 : Blo 1727064 3887297 := bstep (se 2 (by rfl) ⟨1457736, by rfl⟩ : syracuseStep 3887297 = 2915473) B2915473
theorem B2592971 : Blo 1727064 2592971 := bstep (se 1 (by rfl) ⟨1944728, by rfl⟩ : syracuseStep 2592971 = 3889457) B3889457
theorem B2592983 : Blo 1727064 2592983 := bstep (se 1 (by rfl) ⟨1944737, by rfl⟩ : syracuseStep 2592983 = 3889475) B3889475
theorem B19681541 : Blo 1727064 19681541 := bstep (se 4 (by rfl) ⟨1845144, by rfl⟩ : syracuseStep 19681541 = 3690289) B3690289
theorem B2593049 : Blo 1727064 2593049 := bstep (se 2 (by rfl) ⟨972393, by rfl⟩ : syracuseStep 2593049 = 1944787) B1944787
theorem B24899885 : Blo 1727064 24899885 := bstep (se 3 (by rfl) ⟨4668728, by rfl⟩ : syracuseStep 24899885 = 9337457) B9337457
theorem B2593163 : Blo 1727064 2593163 := bstep (se 1 (by rfl) ⟨1944872, by rfl⟩ : syracuseStep 2593163 = 3889745) B3889745
theorem B2593175 : Blo 1727064 2593175 := bstep (se 1 (by rfl) ⟨1944881, by rfl⟩ : syracuseStep 2593175 = 3889763) B3889763
theorem B3887513 : Blo 1727064 3887513 := bstep (se 2 (by rfl) ⟨1457817, by rfl⟩ : syracuseStep 3887513 = 2915635) B2915635
theorem B3281305 : Blo 1727064 3281305 := bstep (se 2 (by rfl) ⟨1230489, by rfl⟩ : syracuseStep 3281305 = 2460979) B2460979
theorem B2593241 : Blo 1727064 2593241 := bstep (se 2 (by rfl) ⟨972465, by rfl⟩ : syracuseStep 2593241 = 1944931) B1944931
theorem B3887603 : Blo 1727064 3887603 := bstep (se 1 (by rfl) ⟨2915702, by rfl⟩ : syracuseStep 3887603 = 5831405) B5831405
theorem B3887639 : Blo 1727064 3887639 := bstep (se 1 (by rfl) ⟨2915729, by rfl⟩ : syracuseStep 3887639 = 5831459) B5831459
theorem B2593355 : Blo 1727064 2593355 := bstep (se 1 (by rfl) ⟨1945016, by rfl⟩ : syracuseStep 2593355 = 3890033) B3890033
theorem B2593367 : Blo 1727064 2593367 := bstep (se 1 (by rfl) ⟨1945025, by rfl⟩ : syracuseStep 2593367 = 3890051) B3890051
theorem B2593433 : Blo 1727064 2593433 := bstep (se 2 (by rfl) ⟨972537, by rfl⟩ : syracuseStep 2593433 = 1945075) B1945075
theorem B5829299 : Blo 1727064 5829299 := bstep (se 1 (by rfl) ⟨4371974, by rfl⟩ : syracuseStep 5829299 = 8743949) B8743949
theorem B4920011 : Blo 1727064 4920011 := bstep (se 1 (by rfl) ⟨3690008, by rfl⟩ : syracuseStep 4920011 = 7380017) B7380017
theorem B3887819 : Blo 1727064 3887819 := bstep (se 1 (by rfl) ⟨2915864, by rfl⟩ : syracuseStep 3887819 = 5831729) B5831729
theorem B3887873 : Blo 1727064 3887873 := bstep (se 2 (by rfl) ⟨1457952, by rfl⟩ : syracuseStep 3887873 = 2915905) B2915905
theorem B2593547 : Blo 1727064 2593547 := bstep (se 1 (by rfl) ⟨1945160, by rfl⟩ : syracuseStep 2593547 = 3890321) B3890321
theorem B2593559 : Blo 1727064 2593559 := bstep (se 1 (by rfl) ⟨1945169, by rfl⟩ : syracuseStep 2593559 = 3890339) B3890339
theorem B6558509 : Blo 1727064 6558509 := bstep (se 3 (by rfl) ⟨1229720, by rfl⟩ : syracuseStep 6558509 = 2459441) B2459441
theorem B2626391 : Blo 1727064 2626391 := bstep (se 1 (by rfl) ⟨1969793, by rfl⟩ : syracuseStep 2626391 = 3939587) B3939587
theorem B5829569 : Blo 1727064 5829569 := bstep (se 2 (by rfl) ⟨2186088, by rfl⟩ : syracuseStep 5829569 = 4372177) B4372177
theorem B3281867 : Blo 1727064 3281867 := bstep (se 1 (by rfl) ⟨2461400, by rfl⟩ : syracuseStep 3281867 = 4922801) B4922801
theorem B3888089 : Blo 1727064 3888089 := bstep (se 2 (by rfl) ⟨1458033, by rfl⟩ : syracuseStep 3888089 = 2916067) B2916067
theorem B5534743 : Blo 1727064 5534743 := bstep (se 1 (by rfl) ⟨4151057, by rfl⟩ : syracuseStep 5534743 = 8302115) B8302115
theorem B3888179 : Blo 1727064 3888179 := bstep (se 1 (by rfl) ⟨2916134, by rfl⟩ : syracuseStep 3888179 = 5832269) B5832269
theorem B10245185 : Blo 1727064 10245185 := bstep (se 2 (by rfl) ⟨3841944, by rfl⟩ : syracuseStep 10245185 = 7683889) B7683889
theorem B3888215 : Blo 1727064 3888215 := bstep (se 1 (by rfl) ⟨2916161, by rfl⟩ : syracuseStep 3888215 = 5832323) B5832323
theorem B3691649 : Blo 1727064 3691649 := bstep (se 2 (by rfl) ⟨1384368, by rfl⟩ : syracuseStep 3691649 = 2768737) B2768737
theorem B3282049 : Blo 1727064 3282049 := bstep (se 2 (by rfl) ⟨1230768, by rfl⟩ : syracuseStep 3282049 = 2461537) B2461537
theorem B5256371 : Blo 1727064 5256371 := bstep (se 1 (by rfl) ⟨3942278, by rfl⟩ : syracuseStep 5256371 = 7884557) B7884557
theorem B3740915 : Blo 1727064 3740915 := bstep (se 1 (by rfl) ⟨2805686, by rfl⟩ : syracuseStep 3740915 = 5611373) B5611373
theorem B3888395 : Blo 1727064 3888395 := bstep (se 1 (by rfl) ⟨2916296, by rfl⟩ : syracuseStep 3888395 = 5832593) B5832593
theorem B3888449 : Blo 1727064 3888449 := bstep (se 2 (by rfl) ⟨1458168, by rfl⟩ : syracuseStep 3888449 = 2916337) B2916337
theorem B19961153 : Blo 1727064 19961153 := bstep (se 2 (by rfl) ⟨7485432, by rfl⟩ : syracuseStep 19961153 = 14970865) B14970865
theorem B14759243 : Blo 1727064 14759243 := bstep (se 1 (by rfl) ⟨11069432, by rfl⟩ : syracuseStep 14759243 = 22138865) B22138865
theorem B4150721 : Blo 1727064 4150721 := bstep (se 2 (by rfl) ⟨1556520, by rfl⟩ : syracuseStep 4150721 = 3113041) B3113041
theorem B5535179 : Blo 1727064 5535179 := bstep (se 1 (by rfl) ⟨4151384, by rfl⟩ : syracuseStep 5535179 = 8302769) B8302769
theorem B5830109 : Blo 1727064 5830109 := bstep (se 3 (by rfl) ⟨1093145, by rfl⟩ : syracuseStep 5830109 = 2186291) B2186291
theorem B3888665 : Blo 1727064 3888665 := bstep (se 2 (by rfl) ⟨1458249, by rfl⟩ : syracuseStep 3888665 = 2916499) B2916499
theorem B8746541 : Blo 1727064 8746541 := bstep (se 3 (by rfl) ⟨1639976, by rfl⟩ : syracuseStep 8746541 = 3279953) B3279953
theorem B9844325 : Blo 1727064 9844325 := bstep (se 4 (by rfl) ⟨922905, by rfl⟩ : syracuseStep 9844325 = 1845811) B1845811
theorem B14767717 : Blo 1727064 14767717 := bstep (se 4 (by rfl) ⟨1384473, by rfl⟩ : syracuseStep 14767717 = 2768947) B2768947
theorem B3888755 : Blo 1727064 3888755 := bstep (se 1 (by rfl) ⟨2916566, by rfl⟩ : syracuseStep 3888755 = 5833133) B5833133
theorem B27342467 : Blo 1727064 27342467 := bstep (se 1 (by rfl) ⟨20506850, by rfl⟩ : syracuseStep 27342467 = 41013701) B41013701
theorem B3888791 : Blo 1727064 3888791 := bstep (se 1 (by rfl) ⟨2916593, by rfl⟩ : syracuseStep 3888791 = 5833187) B5833187
theorem B18675521 : Blo 1727064 18675521 := bstep (se 2 (by rfl) ⟨7003320, by rfl⟩ : syracuseStep 18675521 = 14006641) B14006641
theorem B4372289 : Blo 1727064 4372289 := bstep (se 2 (by rfl) ⟨1639608, by rfl⟩ : syracuseStep 4372289 = 3279217) B3279217
theorem B3888971 : Blo 1727064 3888971 := bstep (se 1 (by rfl) ⟨2916728, by rfl⟩ : syracuseStep 3888971 = 5833457) B5833457
theorem B3889025 : Blo 1727064 3889025 := bstep (se 2 (by rfl) ⟨1458384, by rfl⟩ : syracuseStep 3889025 = 2916769) B2916769
theorem B8304535 : Blo 1727064 8304535 := bstep (se 1 (by rfl) ⟨6228401, by rfl⟩ : syracuseStep 8304535 = 12456803) B12456803
theorem B7010327 : Blo 1727064 7010327 := bstep (se 1 (by rfl) ⟨5257745, by rfl⟩ : syracuseStep 7010327 = 10515491) B10515491
theorem B3889241 : Blo 1727064 3889241 := bstep (se 2 (by rfl) ⟨1458465, by rfl⟩ : syracuseStep 3889241 = 2916931) B2916931
theorem B7379075 : Blo 1727064 7379075 := bstep (se 1 (by rfl) ⟨5534306, by rfl⟩ : syracuseStep 7379075 = 11068613) B11068613
theorem B3889331 : Blo 1727064 3889331 := bstep (se 1 (by rfl) ⟨2916998, by rfl⟩ : syracuseStep 3889331 = 5833997) B5833997
theorem B6559937 : Blo 1727064 6559937 := bstep (se 2 (by rfl) ⟨2459976, by rfl⟩ : syracuseStep 6559937 = 4919953) B4919953
theorem B2767051 : Blo 1727064 2767051 := bstep (se 1 (by rfl) ⟨2075288, by rfl⟩ : syracuseStep 2767051 = 4150577) B4150577
theorem B5535947 : Blo 1727064 5535947 := bstep (se 1 (by rfl) ⟨4151960, by rfl⟩ : syracuseStep 5535947 = 8303921) B8303921
theorem B3889367 : Blo 1727064 3889367 := bstep (se 1 (by rfl) ⟨2917025, by rfl⟩ : syracuseStep 3889367 = 5834051) B5834051
theorem B9836761 : Blo 1727064 9836761 := bstep (se 2 (by rfl) ⟨3688785, by rfl⟩ : syracuseStep 9836761 = 7377571) B7377571
theorem B9845009 : Blo 1727064 9845009 := bstep (se 2 (by rfl) ⟨3691878, by rfl⟩ : syracuseStep 9845009 = 7383757) B7383757
theorem B26589505 : Blo 1727064 26589505 := bstep (se 2 (by rfl) ⟨9971064, by rfl⟩ : syracuseStep 26589505 = 19942129) B19942129
theorem B12450113 : Blo 1727064 12450113 := bstep (se 2 (by rfl) ⟨4668792, by rfl⟩ : syracuseStep 12450113 = 9337585) B9337585
theorem B4372825 : Blo 1727064 4372825 := bstep (se 2 (by rfl) ⟨1639809, by rfl⟩ : syracuseStep 4372825 = 3279619) B3279619
theorem B3889547 : Blo 1727064 3889547 := bstep (se 1 (by rfl) ⟨2917160, by rfl⟩ : syracuseStep 3889547 = 5834321) B5834321
theorem B3889601 : Blo 1727064 3889601 := bstep (se 2 (by rfl) ⟨1458600, by rfl⟩ : syracuseStep 3889601 = 2917201) B2917201
theorem B7379417 : Blo 1727064 7379417 := bstep (se 2 (by rfl) ⟨2767281, by rfl⟩ : syracuseStep 7379417 = 5534563) B5534563
theorem B14768675 : Blo 1727064 14768675 := bstep (se 1 (by rfl) ⟨11076506, by rfl⟩ : syracuseStep 14768675 = 22153013) B22153013
theorem B5831243 : Blo 1727064 5831243 := bstep (se 1 (by rfl) ⟨4373432, by rfl⟩ : syracuseStep 5831243 = 8746865) B8746865
theorem B5536345 : Blo 1727064 5536345 := bstep (se 2 (by rfl) ⟨2076129, by rfl⟩ : syracuseStep 5536345 = 4152259) B4152259
theorem B1727083 : Blo 1727064 1727083 := bstep (se 1 (by rfl) ⟨1295312, by rfl⟩ : syracuseStep 1727083 = 2590625) B2590625
theorem B1727095 : Blo 1727064 1727095 := bstep (se 1 (by rfl) ⟨1295321, by rfl⟩ : syracuseStep 1727095 = 2590643) B2590643
theorem B1727115 : Blo 1727064 1727115 := bstep (se 1 (by rfl) ⟨1295336, by rfl⟩ : syracuseStep 1727115 = 2590673) B2590673
theorem B1727127 : Blo 1727064 1727127 := bstep (se 1 (by rfl) ⟨1295345, by rfl⟩ : syracuseStep 1727127 = 2590691) B2590691
theorem B2914967 : Blo 1727064 2914967 := bstep (se 1 (by rfl) ⟨2186225, by rfl⟩ : syracuseStep 2914967 = 4372451) B4372451
theorem B3889817 : Blo 1727064 3889817 := bstep (se 2 (by rfl) ⟨1458681, by rfl⟩ : syracuseStep 3889817 = 2917363) B2917363
theorem B1727147 : Blo 1727064 1727147 := bstep (se 1 (by rfl) ⟨1295360, by rfl⟩ : syracuseStep 1727147 = 2590721) B2590721
theorem B1727159 : Blo 1727064 1727159 := bstep (se 1 (by rfl) ⟨1295369, by rfl⟩ : syracuseStep 1727159 = 2590739) B2590739
theorem B1727179 : Blo 1727064 1727179 := bstep (se 1 (by rfl) ⟨1295384, by rfl⟩ : syracuseStep 1727179 = 2590769) B2590769
theorem B5536459 : Blo 1727064 5536459 := bstep (se 1 (by rfl) ⟨4152344, by rfl⟩ : syracuseStep 5536459 = 8304689) B8304689
theorem B1727191 : Blo 1727064 1727191 := bstep (se 1 (by rfl) ⟨1295393, by rfl⟩ : syracuseStep 1727191 = 2590787) B2590787
theorem B1727211 : Blo 1727064 1727211 := bstep (se 1 (by rfl) ⟨1295408, by rfl⟩ : syracuseStep 1727211 = 2590817) B2590817
theorem B3889907 : Blo 1727064 3889907 := bstep (se 1 (by rfl) ⟨2917430, by rfl⟩ : syracuseStep 3889907 = 5834861) B5834861
theorem B1727223 : Blo 1727064 1727223 := bstep (se 1 (by rfl) ⟨1295417, by rfl⟩ : syracuseStep 1727223 = 2590835) B2590835
theorem B19962629 : Blo 1727064 19962629 := bstep (se 4 (by rfl) ⟨1871496, by rfl⟩ : syracuseStep 19962629 = 3742993) B3742993
theorem B1727243 : Blo 1727064 1727243 := bstep (se 1 (by rfl) ⟨1295432, by rfl⟩ : syracuseStep 1727243 = 2590865) B2590865
theorem B11066129 : Blo 1727064 11066129 := bstep (se 2 (by rfl) ⟨4149798, by rfl⟩ : syracuseStep 11066129 = 8299597) B8299597
theorem B3939095 : Blo 1727064 3939095 := bstep (se 1 (by rfl) ⟨2954321, by rfl⟩ : syracuseStep 3939095 = 5908643) B5908643
theorem B1727255 : Blo 1727064 1727255 := bstep (se 1 (by rfl) ⟨1295441, by rfl⟩ : syracuseStep 1727255 = 2590883) B2590883
theorem B2915095 : Blo 1727064 2915095 := bstep (se 1 (by rfl) ⟨2186321, by rfl⟩ : syracuseStep 2915095 = 4372643) B4372643
theorem B3889943 : Blo 1727064 3889943 := bstep (se 1 (by rfl) ⟨2917457, by rfl⟩ : syracuseStep 3889943 = 5834915) B5834915
theorem B1727275 : Blo 1727064 1727275 := bstep (se 1 (by rfl) ⟨1295456, by rfl⟩ : syracuseStep 1727275 = 2590913) B2590913
theorem B1727287 : Blo 1727064 1727287 := bstep (se 1 (by rfl) ⟨1295465, by rfl⟩ : syracuseStep 1727287 = 2590931) B2590931
theorem B1727307 : Blo 1727064 1727307 := bstep (se 1 (by rfl) ⟨1295480, by rfl⟩ : syracuseStep 1727307 = 2590961) B2590961
theorem B1727319 : Blo 1727064 1727319 := bstep (se 1 (by rfl) ⟨1295489, by rfl⟩ : syracuseStep 1727319 = 2590979) B2590979
theorem B5831513 : Blo 1727064 5831513 := bstep (se 2 (by rfl) ⟨2186817, by rfl⟩ : syracuseStep 5831513 = 4373635) B4373635
theorem B1727339 : Blo 1727064 1727339 := bstep (se 1 (by rfl) ⟨1295504, by rfl⟩ : syracuseStep 1727339 = 2591009) B2591009
theorem B1727351 : Blo 1727064 1727351 := bstep (se 1 (by rfl) ⟨1295513, by rfl⟩ : syracuseStep 1727351 = 2591027) B2591027
theorem B1727371 : Blo 1727064 1727371 := bstep (se 1 (by rfl) ⟨1295528, by rfl⟩ : syracuseStep 1727371 = 2591057) B2591057
theorem B1727383 : Blo 1727064 1727383 := bstep (se 1 (by rfl) ⟨1295537, by rfl⟩ : syracuseStep 1727383 = 2591075) B2591075
theorem B1727403 : Blo 1727064 1727403 := bstep (se 1 (by rfl) ⟨1295552, by rfl⟩ : syracuseStep 1727403 = 2591105) B2591105
theorem B1727415 : Blo 1727064 1727415 := bstep (se 1 (by rfl) ⟨1295561, by rfl⟩ : syracuseStep 1727415 = 2591123) B2591123
theorem B1727435 : Blo 1727064 1727435 := bstep (se 1 (by rfl) ⟨1295576, by rfl⟩ : syracuseStep 1727435 = 2591153) B2591153
theorem B3890123 : Blo 1727064 3890123 := bstep (se 1 (by rfl) ⟨2917592, by rfl⟩ : syracuseStep 3890123 = 5835185) B5835185
theorem B1727447 : Blo 1727064 1727447 := bstep (se 1 (by rfl) ⟨1295585, by rfl⟩ : syracuseStep 1727447 = 2591171) B2591171
theorem B1727467 : Blo 1727064 1727467 := bstep (se 1 (by rfl) ⟨1295600, by rfl⟩ : syracuseStep 1727467 = 2591201) B2591201
theorem B1727479 : Blo 1727064 1727479 := bstep (se 1 (by rfl) ⟨1295609, by rfl⟩ : syracuseStep 1727479 = 2591219) B2591219
theorem B3890177 : Blo 1727064 3890177 := bstep (se 2 (by rfl) ⟨1458816, by rfl⟩ : syracuseStep 3890177 = 2917633) B2917633
theorem B1727499 : Blo 1727064 1727499 := bstep (se 1 (by rfl) ⟨1295624, by rfl⟩ : syracuseStep 1727499 = 2591249) B2591249
theorem B1727511 : Blo 1727064 1727511 := bstep (se 1 (by rfl) ⟨1295633, by rfl⟩ : syracuseStep 1727511 = 2591267) B2591267
theorem B1727531 : Blo 1727064 1727531 := bstep (se 1 (by rfl) ⟨1295648, by rfl⟩ : syracuseStep 1727531 = 2591297) B2591297
theorem B1727543 : Blo 1727064 1727543 := bstep (se 1 (by rfl) ⟨1295657, by rfl⟩ : syracuseStep 1727543 = 2591315) B2591315
theorem B1727563 : Blo 1727064 1727563 := bstep (se 1 (by rfl) ⟨1295672, by rfl⟩ : syracuseStep 1727563 = 2591345) B2591345
theorem B1727575 : Blo 1727064 1727575 := bstep (se 1 (by rfl) ⟨1295681, by rfl⟩ : syracuseStep 1727575 = 2591363) B2591363
theorem B1727595 : Blo 1727064 1727595 := bstep (se 1 (by rfl) ⟨1295696, by rfl⟩ : syracuseStep 1727595 = 2591393) B2591393
theorem B1727607 : Blo 1727064 1727607 := bstep (se 1 (by rfl) ⟨1295705, by rfl⟩ : syracuseStep 1727607 = 2591411) B2591411
theorem B1727627 : Blo 1727064 1727627 := bstep (se 1 (by rfl) ⟨1295720, by rfl⟩ : syracuseStep 1727627 = 2591441) B2591441
theorem B9837719 : Blo 1727064 9837719 := bstep (se 1 (by rfl) ⟨7378289, by rfl⟩ : syracuseStep 9837719 = 14756579) B14756579
theorem B1727639 : Blo 1727064 1727639 := bstep (se 1 (by rfl) ⟨1295729, by rfl⟩ : syracuseStep 1727639 = 2591459) B2591459
theorem B1727659 : Blo 1727064 1727659 := bstep (se 1 (by rfl) ⟨1295744, by rfl⟩ : syracuseStep 1727659 = 2591489) B2591489
theorem B1727671 : Blo 1727064 1727671 := bstep (se 1 (by rfl) ⟨1295753, by rfl⟩ : syracuseStep 1727671 = 2591507) B2591507
theorem B5536961 : Blo 1727064 5536961 := bstep (se 2 (by rfl) ⟨2076360, by rfl⟩ : syracuseStep 5536961 = 4152721) B4152721
theorem B2186443 : Blo 1727064 2186443 := bstep (se 1 (by rfl) ⟨1639832, by rfl⟩ : syracuseStep 2186443 = 3279665) B3279665
theorem B1727691 : Blo 1727064 1727691 := bstep (se 1 (by rfl) ⟨1295768, by rfl⟩ : syracuseStep 1727691 = 2591537) B2591537
theorem B1727703 : Blo 1727064 1727703 := bstep (se 1 (by rfl) ⟨1295777, by rfl⟩ : syracuseStep 1727703 = 2591555) B2591555
theorem B2768089 : Blo 1727064 2768089 := bstep (se 2 (by rfl) ⟨1038033, by rfl⟩ : syracuseStep 2768089 = 2076067) B2076067
theorem B3890393 : Blo 1727064 3890393 := bstep (se 2 (by rfl) ⟨1458897, by rfl⟩ : syracuseStep 3890393 = 2917795) B2917795
theorem B1727723 : Blo 1727064 1727723 := bstep (se 1 (by rfl) ⟨1295792, by rfl⟩ : syracuseStep 1727723 = 2591585) B2591585
theorem B1727735 : Blo 1727064 1727735 := bstep (se 1 (by rfl) ⟨1295801, by rfl⟩ : syracuseStep 1727735 = 2591603) B2591603
theorem B1727755 : Blo 1727064 1727755 := bstep (se 1 (by rfl) ⟨1295816, by rfl⟩ : syracuseStep 1727755 = 2591633) B2591633
theorem B1727767 : Blo 1727064 1727767 := bstep (se 1 (by rfl) ⟨1295825, by rfl⟩ : syracuseStep 1727767 = 2591651) B2591651
theorem B1727787 : Blo 1727064 1727787 := bstep (se 1 (by rfl) ⟨1295840, by rfl⟩ : syracuseStep 1727787 = 2591681) B2591681
theorem B1727799 : Blo 1727064 1727799 := bstep (se 1 (by rfl) ⟨1295849, by rfl⟩ : syracuseStep 1727799 = 2591699) B2591699
theorem B1727819 : Blo 1727064 1727819 := bstep (se 1 (by rfl) ⟨1295864, by rfl⟩ : syracuseStep 1727819 = 2591729) B2591729
theorem B1727831 : Blo 1727064 1727831 := bstep (se 1 (by rfl) ⟨1295873, by rfl⟩ : syracuseStep 1727831 = 2591747) B2591747
theorem B1727851 : Blo 1727064 1727851 := bstep (se 1 (by rfl) ⟨1295888, by rfl⟩ : syracuseStep 1727851 = 2591777) B2591777
theorem B1727863 : Blo 1727064 1727863 := bstep (se 1 (by rfl) ⟨1295897, by rfl⟩ : syracuseStep 1727863 = 2591795) B2591795
theorem B3325313 : Blo 1727064 3325313 := bstep (se 2 (by rfl) ⟨1246992, by rfl⟩ : syracuseStep 3325313 = 2493985) B2493985
theorem B2915723 : Blo 1727064 2915723 := bstep (se 1 (by rfl) ⟨2186792, by rfl⟩ : syracuseStep 2915723 = 4373585) B4373585
theorem B1727883 : Blo 1727064 1727883 := bstep (se 1 (by rfl) ⟨1295912, by rfl⟩ : syracuseStep 1727883 = 2591825) B2591825
theorem B1727895 : Blo 1727064 1727895 := bstep (se 1 (by rfl) ⟨1295921, by rfl⟩ : syracuseStep 1727895 = 2591843) B2591843
theorem B1727915 : Blo 1727064 1727915 := bstep (se 1 (by rfl) ⟨1295936, by rfl⟩ : syracuseStep 1727915 = 2591873) B2591873
theorem B4373939 : Blo 1727064 4373939 := bstep (se 1 (by rfl) ⟨3280454, by rfl⟩ : syracuseStep 4373939 = 6560909) B6560909
theorem B1727927 : Blo 1727064 1727927 := bstep (se 1 (by rfl) ⟨1295945, by rfl⟩ : syracuseStep 1727927 = 2591891) B2591891
theorem B1727947 : Blo 1727064 1727947 := bstep (se 1 (by rfl) ⟨1295960, by rfl⟩ : syracuseStep 1727947 = 2591921) B2591921
theorem B1727959 : Blo 1727064 1727959 := bstep (se 1 (by rfl) ⟨1295969, by rfl⟩ : syracuseStep 1727959 = 2591939) B2591939
theorem B1727979 : Blo 1727064 1727979 := bstep (se 1 (by rfl) ⟨1295984, by rfl⟩ : syracuseStep 1727979 = 2591969) B2591969
theorem B1727991 : Blo 1727064 1727991 := bstep (se 1 (by rfl) ⟨1295993, by rfl⟩ : syracuseStep 1727991 = 2591987) B2591987
theorem B2915851 : Blo 1727064 2915851 := bstep (se 1 (by rfl) ⟨2186888, by rfl⟩ : syracuseStep 2915851 = 4373777) B4373777
theorem B1728011 : Blo 1727064 1728011 := bstep (se 1 (by rfl) ⟨1296008, by rfl⟩ : syracuseStep 1728011 = 2592017) B2592017
theorem B1728023 : Blo 1727064 1728023 := bstep (se 1 (by rfl) ⟨1296017, by rfl⟩ : syracuseStep 1728023 = 2592035) B2592035
theorem B5832215 : Blo 1727064 5832215 := bstep (se 1 (by rfl) ⟨4374161, by rfl⟩ : syracuseStep 5832215 = 8748323) B8748323
theorem B17735203 : Blo 1727064 17735203 := bstep (se 1 (by rfl) ⟨13301402, by rfl⟩ : syracuseStep 17735203 = 26602805) B26602805
theorem B1728043 : Blo 1727064 1728043 := bstep (se 1 (by rfl) ⟨1296032, by rfl⟩ : syracuseStep 1728043 = 2592065) B2592065
theorem B4152883 : Blo 1727064 4152883 := bstep (se 1 (by rfl) ⟨3114662, by rfl⟩ : syracuseStep 4152883 = 6229325) B6229325
theorem B1728055 : Blo 1727064 1728055 := bstep (se 1 (by rfl) ⟨1296041, by rfl⟩ : syracuseStep 1728055 = 2592083) B2592083
theorem B3112523 : Blo 1727064 3112523 := bstep (se 1 (by rfl) ⟨2334392, by rfl⟩ : syracuseStep 3112523 = 4668785) B4668785
theorem B1728075 : Blo 1727064 1728075 := bstep (se 1 (by rfl) ⟨1296056, by rfl⟩ : syracuseStep 1728075 = 2592113) B2592113
theorem B23977547 : Blo 1727064 23977547 := bstep (se 1 (by rfl) ⟨17983160, by rfl⟩ : syracuseStep 23977547 = 35966321) B35966321
theorem B8420939 : Blo 1727064 8420939 := bstep (se 1 (by rfl) ⟨6315704, by rfl⟩ : syracuseStep 8420939 = 12631409) B12631409
theorem B1728087 : Blo 1727064 1728087 := bstep (se 1 (by rfl) ⟨1296065, by rfl⟩ : syracuseStep 1728087 = 2592131) B2592131
theorem B1728107 : Blo 1727064 1728107 := bstep (se 1 (by rfl) ⟨1296080, by rfl⟩ : syracuseStep 1728107 = 2592161) B2592161
theorem B1728119 : Blo 1727064 1728119 := bstep (se 1 (by rfl) ⟨1296089, by rfl⟩ : syracuseStep 1728119 = 2592179) B2592179
theorem B1728139 : Blo 1727064 1728139 := bstep (se 1 (by rfl) ⟨1296104, by rfl⟩ : syracuseStep 1728139 = 2592209) B2592209
theorem B6561425 : Blo 1727064 6561425 := bstep (se 2 (by rfl) ⟨2460534, by rfl⟩ : syracuseStep 6561425 = 4921069) B4921069
theorem B1728151 : Blo 1727064 1728151 := bstep (se 1 (by rfl) ⟨1296113, by rfl⟩ : syracuseStep 1728151 = 2592227) B2592227
theorem B2915993 : Blo 1727064 2915993 := bstep (se 2 (by rfl) ⟨1093497, by rfl⟩ : syracuseStep 2915993 = 2186995) B2186995
theorem B2768537 : Blo 1727064 2768537 := bstep (se 2 (by rfl) ⟨1038201, by rfl⟩ : syracuseStep 2768537 = 2076403) B2076403
theorem B1728171 : Blo 1727064 1728171 := bstep (se 1 (by rfl) ⟨1296128, by rfl⟩ : syracuseStep 1728171 = 2592257) B2592257
theorem B1728183 : Blo 1727064 1728183 := bstep (se 1 (by rfl) ⟨1296137, by rfl⟩ : syracuseStep 1728183 = 2592275) B2592275
theorem B1728203 : Blo 1727064 1728203 := bstep (se 1 (by rfl) ⟨1296152, by rfl⟩ : syracuseStep 1728203 = 2592305) B2592305
theorem B1728215 : Blo 1727064 1728215 := bstep (se 1 (by rfl) ⟨1296161, by rfl⟩ : syracuseStep 1728215 = 2592323) B2592323
theorem B4374233 : Blo 1727064 4374233 := bstep (se 2 (by rfl) ⟨1640337, by rfl⟩ : syracuseStep 4374233 = 3280675) B3280675
theorem B4210393 : Blo 1727064 4210393 := bstep (se 2 (by rfl) ⟨1578897, by rfl⟩ : syracuseStep 4210393 = 3157795) B3157795
theorem B1728235 : Blo 1727064 1728235 := bstep (se 1 (by rfl) ⟨1296176, by rfl⟩ : syracuseStep 1728235 = 2592353) B2592353
theorem B1728247 : Blo 1727064 1728247 := bstep (se 1 (by rfl) ⟨1296185, by rfl⟩ : syracuseStep 1728247 = 2592371) B2592371
theorem B1728267 : Blo 1727064 1728267 := bstep (se 1 (by rfl) ⟨1296200, by rfl⟩ : syracuseStep 1728267 = 2592401) B2592401
theorem B1728279 : Blo 1727064 1728279 := bstep (se 1 (by rfl) ⟨1296209, by rfl⟩ : syracuseStep 1728279 = 2592419) B2592419
theorem B2916121 : Blo 1727064 2916121 := bstep (se 2 (by rfl) ⟨1093545, by rfl⟩ : syracuseStep 2916121 = 2187091) B2187091
theorem B1728299 : Blo 1727064 1728299 := bstep (se 1 (by rfl) ⟨1296224, by rfl⟩ : syracuseStep 1728299 = 2592449) B2592449
theorem B5537587 : Blo 1727064 5537587 := bstep (se 1 (by rfl) ⟨4153190, by rfl⟩ : syracuseStep 5537587 = 8306381) B8306381
theorem B1728311 : Blo 1727064 1728311 := bstep (se 1 (by rfl) ⟨1296233, by rfl⟩ : syracuseStep 1728311 = 2592467) B2592467
theorem B1728331 : Blo 1727064 1728331 := bstep (se 1 (by rfl) ⟨1296248, by rfl⟩ : syracuseStep 1728331 = 2592497) B2592497
theorem B1728343 : Blo 1727064 1728343 := bstep (se 1 (by rfl) ⟨1296257, by rfl⟩ : syracuseStep 1728343 = 2592515) B2592515
theorem B1728363 : Blo 1727064 1728363 := bstep (se 1 (by rfl) ⟨1296272, by rfl⟩ : syracuseStep 1728363 = 2592545) B2592545
theorem B1728375 : Blo 1727064 1728375 := bstep (se 1 (by rfl) ⟨1296281, by rfl⟩ : syracuseStep 1728375 = 2592563) B2592563
theorem B1728395 : Blo 1727064 1728395 := bstep (se 1 (by rfl) ⟨1296296, by rfl⟩ : syracuseStep 1728395 = 2592593) B2592593
theorem B1728407 : Blo 1727064 1728407 := bstep (se 1 (by rfl) ⟨1296305, by rfl⟩ : syracuseStep 1728407 = 2592611) B2592611
theorem B1728427 : Blo 1727064 1728427 := bstep (se 1 (by rfl) ⟨1296320, by rfl⟩ : syracuseStep 1728427 = 2592641) B2592641
theorem B1728439 : Blo 1727064 1728439 := bstep (se 1 (by rfl) ⟨1296329, by rfl⟩ : syracuseStep 1728439 = 2592659) B2592659
theorem B1728459 : Blo 1727064 1728459 := bstep (se 1 (by rfl) ⟨1296344, by rfl⟩ : syracuseStep 1728459 = 2592689) B2592689
theorem B1728471 : Blo 1727064 1728471 := bstep (se 1 (by rfl) ⟨1296353, by rfl⟩ : syracuseStep 1728471 = 2592707) B2592707
theorem B1728491 : Blo 1727064 1728491 := bstep (se 1 (by rfl) ⟨1296368, by rfl⟩ : syracuseStep 1728491 = 2592737) B2592737
theorem B1728503 : Blo 1727064 1728503 := bstep (se 1 (by rfl) ⟨1296377, by rfl⟩ : syracuseStep 1728503 = 2592755) B2592755
theorem B1728519 : Blo 1727064 1728519 := bstep (se 1 (by rfl) ⟨1296389, by rfl⟩ : syracuseStep 1728519 = 2592779) B2592779
theorem B1728527 : Blo 1727064 1728527 := bstep (se 1 (by rfl) ⟨1296395, by rfl⟩ : syracuseStep 1728527 = 2592791) B2592791
theorem B4374587 : Blo 1727064 4374587 := bstep (se 1 (by rfl) ⟨3280940, by rfl⟩ : syracuseStep 4374587 = 6561881) B6561881
theorem B1728571 : Blo 1727064 1728571 := bstep (se 1 (by rfl) ⟨1296428, by rfl⟩ : syracuseStep 1728571 = 2592857) B2592857
theorem B6561911 : Blo 1727064 6561911 := bstep (se 1 (by rfl) ⟨4921433, by rfl⟩ : syracuseStep 6561911 = 9842867) B9842867
theorem B1728647 : Blo 1727064 1728647 := bstep (se 1 (by rfl) ⟨1296485, by rfl⟩ : syracuseStep 1728647 = 2592971) B2592971
theorem B1728655 : Blo 1727064 1728655 := bstep (se 1 (by rfl) ⟨1296491, by rfl⟩ : syracuseStep 1728655 = 2592983) B2592983
theorem B1728699 : Blo 1727064 1728699 := bstep (se 1 (by rfl) ⟨1296524, by rfl⟩ : syracuseStep 1728699 = 2593049) B2593049
theorem B2916553 : Blo 1727064 2916553 := bstep (se 2 (by rfl) ⟨1093707, by rfl⟩ : syracuseStep 2916553 = 2187415) B2187415
theorem B1728775 : Blo 1727064 1728775 := bstep (se 1 (by rfl) ⟨1296581, by rfl⟩ : syracuseStep 1728775 = 2593163) B2593163
theorem B1728783 : Blo 1727064 1728783 := bstep (se 1 (by rfl) ⟨1296587, by rfl⟩ : syracuseStep 1728783 = 2593175) B2593175
theorem B13115681 : Blo 1727064 13115681 := bstep (se 2 (by rfl) ⟨4918380, by rfl⟩ : syracuseStep 13115681 = 9836761) B9836761
theorem B1728827 : Blo 1727064 1728827 := bstep (se 1 (by rfl) ⟨1296620, by rfl⟩ : syracuseStep 1728827 = 2593241) B2593241
theorem B1728903 : Blo 1727064 1728903 := bstep (se 1 (by rfl) ⟨1296677, by rfl⟩ : syracuseStep 1728903 = 2593355) B2593355
theorem B1728911 : Blo 1727064 1728911 := bstep (se 1 (by rfl) ⟨1296683, by rfl⟩ : syracuseStep 1728911 = 2593367) B2593367
theorem B8749457 : Blo 1727064 8749457 := bstep (se 2 (by rfl) ⟨3281046, by rfl⟩ : syracuseStep 8749457 = 6562093) B6562093
theorem B4374931 : Blo 1727064 4374931 := bstep (se 1 (by rfl) ⟨3281198, by rfl⟩ : syracuseStep 4374931 = 6562397) B6562397
theorem B1728955 : Blo 1727064 1728955 := bstep (se 1 (by rfl) ⟨1296716, by rfl⟩ : syracuseStep 1728955 = 2593433) B2593433
theorem B14016989 : Blo 1727064 14016989 := bstep (se 3 (by rfl) ⟨2628185, by rfl⟩ : syracuseStep 14016989 = 5256371) B5256371
theorem B1729031 : Blo 1727064 1729031 := bstep (se 1 (by rfl) ⟨1296773, by rfl⟩ : syracuseStep 1729031 = 2593547) B2593547
theorem B1729039 : Blo 1727064 1729039 := bstep (se 1 (by rfl) ⟨1296779, by rfl⟩ : syracuseStep 1729039 = 2593559) B2593559
theorem B4375073 : Blo 1727064 4375073 := bstep (se 2 (by rfl) ⟨1640652, by rfl⟩ : syracuseStep 4375073 = 3281305) B3281305
theorem B14959223 : Blo 1727064 14959223 := bstep (se 1 (by rfl) ⟨11219417, by rfl⟩ : syracuseStep 14959223 = 22438835) B22438835
theorem B2187911 : Blo 1727064 2187911 := bstep (se 1 (by rfl) ⟨1640933, by rfl⟩ : syracuseStep 2187911 = 3281867) B3281867
theorem B4154113 : Blo 1727064 4154113 := bstep (se 2 (by rfl) ⟨1557792, by rfl⟩ : syracuseStep 4154113 = 3115585) B3115585
theorem B7381793 : Blo 1727064 7381793 := bstep (se 2 (by rfl) ⟨2768172, by rfl⟩ : syracuseStep 7381793 = 5536345) B5536345
theorem B38404901 : Blo 1727064 38404901 := bstep (se 4 (by rfl) ⟨3600459, by rfl⟩ : syracuseStep 38404901 = 7200919) B7200919
theorem B9839495 : Blo 1727064 9839495 := bstep (se 1 (by rfl) ⟨7379621, by rfl⟩ : syracuseStep 9839495 = 14759243) B14759243
theorem B2917255 : Blo 1727064 2917255 := bstep (se 1 (by rfl) ⟨2187941, by rfl⟩ : syracuseStep 2917255 = 4375883) B4375883
theorem B5833619 : Blo 1727064 5833619 := bstep (se 1 (by rfl) ⟨4375214, by rfl⟩ : syracuseStep 5833619 = 8750429) B8750429
theorem B7381945 : Blo 1727064 7381945 := bstep (se 2 (by rfl) ⟨2768229, by rfl⟩ : syracuseStep 7381945 = 5536459) B5536459
theorem B19948589 : Blo 1727064 19948589 := bstep (se 3 (by rfl) ⟨3740360, by rfl⟩ : syracuseStep 19948589 = 7480721) B7480721
theorem B9839677 : Blo 1727064 9839677 := bstep (se 3 (by rfl) ⟨1844939, by rfl⟩ : syracuseStep 9839677 = 3689879) B3689879
theorem B4990013 : Blo 1727064 4990013 := bstep (se 3 (by rfl) ⟨935627, by rfl⟩ : syracuseStep 4990013 = 1871255) B1871255
theorem B6562883 : Blo 1727064 6562883 := bstep (se 1 (by rfl) ⟨4922162, by rfl⟩ : syracuseStep 6562883 = 9844325) B9844325
theorem B18228311 : Blo 1727064 18228311 := bstep (se 1 (by rfl) ⟨13671233, by rfl⟩ : syracuseStep 18228311 = 27342467) B27342467
theorem B74744963 : Blo 1727064 74744963 := bstep (se 1 (by rfl) ⟨56058722, by rfl⟩ : syracuseStep 74744963 = 112117445) B112117445
theorem B11068589 : Blo 1727064 11068589 := bstep (se 3 (by rfl) ⟨2075360, by rfl⟩ : syracuseStep 11068589 = 4150721) B4150721
theorem B33227981 : Blo 1727064 33227981 := bstep (se 3 (by rfl) ⟨6230246, by rfl⟩ : syracuseStep 33227981 = 12460493) B12460493
theorem B13116653 : Blo 1727064 13116653 := bstep (se 3 (by rfl) ⟨2459372, by rfl⟩ : syracuseStep 13116653 = 4918745) B4918745
theorem B161842465 : Blo 1727064 161842465 := bstep (se 2 (by rfl) ⟨60690924, by rfl⟩ : syracuseStep 161842465 = 121381849) B121381849
theorem B11077073 : Blo 1727064 11077073 := bstep (se 2 (by rfl) ⟨4153902, by rfl⟩ : syracuseStep 11077073 = 8307805) B8307805
theorem B4376065 : Blo 1727064 4376065 := bstep (se 2 (by rfl) ⟨1641024, by rfl⟩ : syracuseStep 4376065 = 3282049) B3282049
theorem B6563339 : Blo 1727064 6563339 := bstep (se 1 (by rfl) ⟨4922504, by rfl⟩ : syracuseStep 6563339 = 9845009) B9845009
theorem B37381661 : Blo 1727064 37381661 := bstep (se 3 (by rfl) ⟨7009061, by rfl⟩ : syracuseStep 37381661 = 14018123) B14018123
theorem B8300075 : Blo 1727064 8300075 := bstep (se 1 (by rfl) ⟨6225056, by rfl⟩ : syracuseStep 8300075 = 12450113) B12450113
theorem B7382765 : Blo 1727064 7382765 := bstep (se 3 (by rfl) ⟨1384268, by rfl⟩ : syracuseStep 7382765 = 2768537) B2768537
theorem B1943311 : Blo 1727064 1943311 := bstep (se 1 (by rfl) ⟨1457483, by rfl⟩ : syracuseStep 1943311 = 2914967) B2914967
theorem B2590607 : Blo 1727064 2590607 := bstep (se 1 (by rfl) ⟨1942955, by rfl⟩ : syracuseStep 2590607 = 3885911) B3885911
theorem B2590649 : Blo 1727064 2590649 := bstep (se 2 (by rfl) ⟨971493, by rfl⟩ : syracuseStep 2590649 = 1942987) B1942987
theorem B2590727 : Blo 1727064 2590727 := bstep (se 1 (by rfl) ⟨1943045, by rfl⟩ : syracuseStep 2590727 = 3886091) B3886091
theorem B2590763 : Blo 1727064 2590763 := bstep (se 1 (by rfl) ⟨1943072, by rfl⟩ : syracuseStep 2590763 = 3886145) B3886145
theorem B2590793 : Blo 1727064 2590793 := bstep (se 2 (by rfl) ⟨971547, by rfl⟩ : syracuseStep 2590793 = 1943095) B1943095
theorem B4376663 : Blo 1727064 4376663 := bstep (se 1 (by rfl) ⟨3282497, by rfl⟩ : syracuseStep 4376663 = 6564995) B6564995
theorem B2590907 : Blo 1727064 2590907 := bstep (se 1 (by rfl) ⟨1943180, by rfl⟩ : syracuseStep 2590907 = 3886361) B3886361
theorem B2590967 : Blo 1727064 2590967 := bstep (se 1 (by rfl) ⟨1943225, by rfl⟩ : syracuseStep 2590967 = 3886451) B3886451
theorem B1943815 : Blo 1727064 1943815 := bstep (se 1 (by rfl) ⟨1457861, by rfl⟩ : syracuseStep 1943815 = 2915723) B2915723
theorem B2590991 : Blo 1727064 2590991 := bstep (se 1 (by rfl) ⟨1943243, by rfl⟩ : syracuseStep 2590991 = 3886487) B3886487
theorem B5835023 : Blo 1727064 5835023 := bstep (se 1 (by rfl) ⟨4376267, by rfl⟩ : syracuseStep 5835023 = 8752535) B8752535
theorem B5613857 : Blo 1727064 5613857 := bstep (se 2 (by rfl) ⟨2105196, by rfl⟩ : syracuseStep 5613857 = 4210393) B4210393
theorem B2591033 : Blo 1727064 2591033 := bstep (se 2 (by rfl) ⟨971637, by rfl⟩ : syracuseStep 2591033 = 1943275) B1943275
theorem B2075015 : Blo 1727064 2075015 := bstep (se 1 (by rfl) ⟨1556261, by rfl⟩ : syracuseStep 2075015 = 3112523) B3112523
theorem B2591111 : Blo 1727064 2591111 := bstep (se 1 (by rfl) ⟨1943333, by rfl⟩ : syracuseStep 2591111 = 3886667) B3886667
theorem B15985031 : Blo 1727064 15985031 := bstep (se 1 (by rfl) ⟨11988773, by rfl⟩ : syracuseStep 15985031 = 23977547) B23977547
theorem B5613959 : Blo 1727064 5613959 := bstep (se 1 (by rfl) ⟨4210469, by rfl⟩ : syracuseStep 5613959 = 8420939) B8420939
theorem B7383449 : Blo 1727064 7383449 := bstep (se 2 (by rfl) ⟨2768793, by rfl⟩ : syracuseStep 7383449 = 5537587) B5537587
theorem B2591147 : Blo 1727064 2591147 := bstep (se 1 (by rfl) ⟨1943360, by rfl⟩ : syracuseStep 2591147 = 3886721) B3886721
theorem B1943995 : Blo 1727064 1943995 := bstep (se 1 (by rfl) ⟨1457996, by rfl⟩ : syracuseStep 1943995 = 2915993) B2915993
theorem B2591177 : Blo 1727064 2591177 := bstep (se 2 (by rfl) ⟨971691, by rfl⟩ : syracuseStep 2591177 = 1943383) B1943383
theorem B8751563 : Blo 1727064 8751563 := bstep (se 1 (by rfl) ⟨6563672, by rfl⟩ : syracuseStep 8751563 = 13127345) B13127345
theorem B11078147 : Blo 1727064 11078147 := bstep (se 1 (by rfl) ⟨8308610, by rfl⟩ : syracuseStep 11078147 = 16617221) B16617221
theorem B5835293 : Blo 1727064 5835293 := bstep (se 3 (by rfl) ⟨1094117, by rfl⟩ : syracuseStep 5835293 = 2188235) B2188235
theorem B2591291 : Blo 1727064 2591291 := bstep (se 1 (by rfl) ⟨1943468, by rfl⟩ : syracuseStep 2591291 = 3886937) B3886937
theorem B3115579 : Blo 1727064 3115579 := bstep (se 1 (by rfl) ⟨2336684, by rfl⟩ : syracuseStep 3115579 = 4673369) B4673369
theorem B2460233 : Blo 1727064 2460233 := bstep (se 2 (by rfl) ⟨922587, by rfl⟩ : syracuseStep 2460233 = 1845175) B1845175
theorem B2591351 : Blo 1727064 2591351 := bstep (se 1 (by rfl) ⟨1943513, by rfl⟩ : syracuseStep 2591351 = 3887027) B3887027
theorem B53217911 : Blo 1727064 53217911 := bstep (se 1 (by rfl) ⟨39913433, by rfl⟩ : syracuseStep 53217911 = 79826867) B79826867
theorem B33688183 : Blo 1727064 33688183 := bstep (se 1 (by rfl) ⟨25266137, by rfl⟩ : syracuseStep 33688183 = 50532275) B50532275
theorem B2591375 : Blo 1727064 2591375 := bstep (se 1 (by rfl) ⟨1943531, by rfl⟩ : syracuseStep 2591375 = 3887063) B3887063
theorem B2591417 : Blo 1727064 2591417 := bstep (se 2 (by rfl) ⟨971781, by rfl⟩ : syracuseStep 2591417 = 1943563) B1943563
theorem B2075323 : Blo 1727064 2075323 := bstep (se 1 (by rfl) ⟨1556492, by rfl⟩ : syracuseStep 2075323 = 3112985) B3112985
theorem B2247355 : Blo 1727064 2247355 := bstep (se 1 (by rfl) ⟨1685516, by rfl⟩ : syracuseStep 2247355 = 3371033) B3371033
theorem B8743625 : Blo 1727064 8743625 := bstep (se 2 (by rfl) ⟨3278859, by rfl⟩ : syracuseStep 8743625 = 6557719) B6557719
theorem B13126373 : Blo 1727064 13126373 := bstep (se 4 (by rfl) ⟨1230597, by rfl⟩ : syracuseStep 13126373 = 2461195) B2461195
theorem B9841409 : Blo 1727064 9841409 := bstep (se 2 (by rfl) ⟨3690528, by rfl⟩ : syracuseStep 9841409 = 7381057) B7381057
theorem B6228737 : Blo 1727064 6228737 := bstep (se 2 (by rfl) ⟨2335776, by rfl⟩ : syracuseStep 6228737 = 4671553) B4671553
theorem B2591495 : Blo 1727064 2591495 := bstep (se 1 (by rfl) ⟨1943621, by rfl⟩ : syracuseStep 2591495 = 3887243) B3887243
theorem B8751887 : Blo 1727064 8751887 := bstep (se 1 (by rfl) ⟨6563915, by rfl⟩ : syracuseStep 8751887 = 13127831) B13127831
theorem B2591531 : Blo 1727064 2591531 := bstep (se 1 (by rfl) ⟨1943648, by rfl⟩ : syracuseStep 2591531 = 3887297) B3887297
theorem B2591561 : Blo 1727064 2591561 := bstep (se 2 (by rfl) ⟨971835, by rfl⟩ : syracuseStep 2591561 = 1943671) B1943671
theorem B16599923 : Blo 1727064 16599923 := bstep (se 1 (by rfl) ⟨12449942, by rfl⟩ : syracuseStep 16599923 = 24899885) B24899885
theorem B5991283 : Blo 1727064 5991283 := bstep (se 1 (by rfl) ⟨4493462, by rfl⟩ : syracuseStep 5991283 = 8986925) B8986925
theorem B1944463 : Blo 1727064 1944463 := bstep (se 1 (by rfl) ⟨1458347, by rfl⟩ : syracuseStep 1944463 = 2916695) B2916695
theorem B3689401 : Blo 1727064 3689401 := bstep (se 2 (by rfl) ⟨1383525, by rfl⟩ : syracuseStep 3689401 = 2767051) B2767051
theorem B2591675 : Blo 1727064 2591675 := bstep (se 1 (by rfl) ⟨1943756, by rfl⟩ : syracuseStep 2591675 = 3887513) B3887513
theorem B2591735 : Blo 1727064 2591735 := bstep (se 1 (by rfl) ⟨1943801, by rfl⟩ : syracuseStep 2591735 = 3887603) B3887603
theorem B2591759 : Blo 1727064 2591759 := bstep (se 1 (by rfl) ⟨1943819, by rfl⟩ : syracuseStep 2591759 = 3887639) B3887639
theorem B2591801 : Blo 1727064 2591801 := bstep (se 2 (by rfl) ⟨971925, by rfl⟩ : syracuseStep 2591801 = 1943851) B1943851
theorem B239316029 : Blo 1727064 239316029 := bstep (se 3 (by rfl) ⟨44871755, by rfl⟩ : syracuseStep 239316029 = 89743511) B89743511
theorem B3886199 : Blo 1727064 3886199 := bstep (se 1 (by rfl) ⟨2914649, by rfl⟩ : syracuseStep 3886199 = 5829299) B5829299
theorem B13118597 : Blo 1727064 13118597 := bstep (se 4 (by rfl) ⟨1229868, by rfl⟩ : syracuseStep 13118597 = 2459737) B2459737
theorem B3280007 : Blo 1727064 3280007 := bstep (se 1 (by rfl) ⟨2460005, by rfl⟩ : syracuseStep 3280007 = 4920011) B4920011
theorem B2591879 : Blo 1727064 2591879 := bstep (se 1 (by rfl) ⟨1943909, by rfl⟩ : syracuseStep 2591879 = 3887819) B3887819
theorem B2591915 : Blo 1727064 2591915 := bstep (se 1 (by rfl) ⟨1943936, by rfl⟩ : syracuseStep 2591915 = 3887873) B3887873
theorem B2591945 : Blo 1727064 2591945 := bstep (se 2 (by rfl) ⟨971979, by rfl⟩ : syracuseStep 2591945 = 1943959) B1943959
theorem B3886379 : Blo 1727064 3886379 := bstep (se 1 (by rfl) ⟨2914784, by rfl⟩ : syracuseStep 3886379 = 5829569) B5829569
theorem B2592059 : Blo 1727064 2592059 := bstep (se 1 (by rfl) ⟨1944044, by rfl⟩ : syracuseStep 2592059 = 3888089) B3888089
theorem B33221987 : Blo 1727064 33221987 := bstep (se 1 (by rfl) ⟨24916490, by rfl⟩ : syracuseStep 33221987 = 49832981) B49832981
theorem B2592119 : Blo 1727064 2592119 := bstep (se 1 (by rfl) ⟨1944089, by rfl⟩ : syracuseStep 2592119 = 3888179) B3888179
theorem B1944967 : Blo 1727064 1944967 := bstep (se 1 (by rfl) ⟨1458725, by rfl⟩ : syracuseStep 1944967 = 2917451) B2917451
theorem B2592143 : Blo 1727064 2592143 := bstep (se 1 (by rfl) ⟨1944107, by rfl⟩ : syracuseStep 2592143 = 3888215) B3888215
theorem B2461099 : Blo 1727064 2461099 := bstep (se 1 (by rfl) ⟨1845824, by rfl⟩ : syracuseStep 2461099 = 3691649) B3691649
theorem B2592185 : Blo 1727064 2592185 := bstep (se 2 (by rfl) ⟨972069, by rfl⟩ : syracuseStep 2592185 = 1944139) B1944139
theorem B14757329 : Blo 1727064 14757329 := bstep (se 2 (by rfl) ⟨5533998, by rfl⟩ : syracuseStep 14757329 = 11067997) B11067997
theorem B2592263 : Blo 1727064 2592263 := bstep (se 1 (by rfl) ⟨1944197, by rfl⟩ : syracuseStep 2592263 = 3888395) B3888395
theorem B2592299 : Blo 1727064 2592299 := bstep (se 1 (by rfl) ⟨1944224, by rfl⟩ : syracuseStep 2592299 = 3888449) B3888449
theorem B13307435 : Blo 1727064 13307435 := bstep (se 1 (by rfl) ⟨9980576, by rfl⟩ : syracuseStep 13307435 = 19961153) B19961153
theorem B1945147 : Blo 1727064 1945147 := bstep (se 1 (by rfl) ⟨1458860, by rfl⟩ : syracuseStep 1945147 = 2917721) B2917721
theorem B2592329 : Blo 1727064 2592329 := bstep (se 2 (by rfl) ⟨972123, by rfl⟩ : syracuseStep 2592329 = 1944247) B1944247
theorem B3690119 : Blo 1727064 3690119 := bstep (se 1 (by rfl) ⟨2767589, by rfl⟩ : syracuseStep 3690119 = 5535179) B5535179
theorem B3886739 : Blo 1727064 3886739 := bstep (se 1 (by rfl) ⟨2915054, by rfl⟩ : syracuseStep 3886739 = 5830109) B5830109
theorem B2592443 : Blo 1727064 2592443 := bstep (se 1 (by rfl) ⟨1944332, by rfl⟩ : syracuseStep 2592443 = 3888665) B3888665
theorem B3886793 : Blo 1727064 3886793 := bstep (se 2 (by rfl) ⟨1457547, by rfl⟩ : syracuseStep 3886793 = 2915095) B2915095
theorem B19672793 : Blo 1727064 19672793 := bstep (se 2 (by rfl) ⟨7377297, by rfl⟩ : syracuseStep 19672793 = 14754595) B14754595
theorem B2592503 : Blo 1727064 2592503 := bstep (se 1 (by rfl) ⟨1944377, by rfl⟩ : syracuseStep 2592503 = 3888755) B3888755
theorem B2592527 : Blo 1727064 2592527 := bstep (se 1 (by rfl) ⟨1944395, by rfl⟩ : syracuseStep 2592527 = 3888791) B3888791
theorem B2592569 : Blo 1727064 2592569 := bstep (se 2 (by rfl) ⟨972213, by rfl⟩ : syracuseStep 2592569 = 1944427) B1944427
theorem B2592647 : Blo 1727064 2592647 := bstep (se 1 (by rfl) ⟨1944485, by rfl⟩ : syracuseStep 2592647 = 3888971) B3888971
theorem B2592683 : Blo 1727064 2592683 := bstep (se 1 (by rfl) ⟨1944512, by rfl⟩ : syracuseStep 2592683 = 3889025) B3889025
theorem B2592713 : Blo 1727064 2592713 := bstep (se 2 (by rfl) ⟨972267, by rfl⟩ : syracuseStep 2592713 = 1944535) B1944535
theorem B22147019 : Blo 1727064 22147019 := bstep (se 1 (by rfl) ⟨16610264, by rfl⟩ : syracuseStep 22147019 = 33220529) B33220529
theorem B4673551 : Blo 1727064 4673551 := bstep (se 1 (by rfl) ⟨3505163, by rfl⟩ : syracuseStep 4673551 = 7010327) B7010327
theorem B2592827 : Blo 1727064 2592827 := bstep (se 1 (by rfl) ⟨1944620, by rfl⟩ : syracuseStep 2592827 = 3889241) B3889241
theorem B4919383 : Blo 1727064 4919383 := bstep (se 1 (by rfl) ⟨3689537, by rfl⟩ : syracuseStep 4919383 = 7379075) B7379075
theorem B2592887 : Blo 1727064 2592887 := bstep (se 1 (by rfl) ⟨1944665, by rfl⟩ : syracuseStep 2592887 = 3889331) B3889331
theorem B3690631 : Blo 1727064 3690631 := bstep (se 1 (by rfl) ⟨2767973, by rfl⟩ : syracuseStep 3690631 = 5535947) B5535947
theorem B2592911 : Blo 1727064 2592911 := bstep (se 1 (by rfl) ⟨1944683, by rfl⟩ : syracuseStep 2592911 = 3889367) B3889367
theorem B2592953 : Blo 1727064 2592953 := bstep (se 2 (by rfl) ⟨972357, by rfl⟩ : syracuseStep 2592953 = 1944715) B1944715
theorem B8753345 : Blo 1727064 8753345 := bstep (se 2 (by rfl) ⟨3282504, by rfl⟩ : syracuseStep 8753345 = 6565009) B6565009
theorem B2593031 : Blo 1727064 2593031 := bstep (se 1 (by rfl) ⟨1944773, by rfl⟩ : syracuseStep 2593031 = 3889547) B3889547
theorem B3690785 : Blo 1727064 3690785 := bstep (se 2 (by rfl) ⟨1384044, by rfl⟩ : syracuseStep 3690785 = 2768089) B2768089
theorem B2593067 : Blo 1727064 2593067 := bstep (se 1 (by rfl) ⟨1944800, by rfl⟩ : syracuseStep 2593067 = 3889601) B3889601
theorem B4919611 : Blo 1727064 4919611 := bstep (se 1 (by rfl) ⟨3689708, by rfl⟩ : syracuseStep 4919611 = 7379417) B7379417
theorem B2593097 : Blo 1727064 2593097 := bstep (se 2 (by rfl) ⟨972411, by rfl⟩ : syracuseStep 2593097 = 1944823) B1944823
theorem B3887495 : Blo 1727064 3887495 := bstep (se 1 (by rfl) ⟨2915621, by rfl⟩ : syracuseStep 3887495 = 5831243) B5831243
theorem B4919737 : Blo 1727064 4919737 := bstep (se 2 (by rfl) ⟨1844901, by rfl⟩ : syracuseStep 4919737 = 3689803) B3689803
theorem B2593211 : Blo 1727064 2593211 := bstep (se 1 (by rfl) ⟨1944908, by rfl⟩ : syracuseStep 2593211 = 3889817) B3889817
theorem B2593271 : Blo 1727064 2593271 := bstep (se 1 (by rfl) ⟨1944953, by rfl⟩ : syracuseStep 2593271 = 3889907) B3889907
theorem B13308419 : Blo 1727064 13308419 := bstep (se 1 (by rfl) ⟨9981314, by rfl⟩ : syracuseStep 13308419 = 19962629) B19962629
theorem B7377419 : Blo 1727064 7377419 := bstep (se 1 (by rfl) ⟨5533064, by rfl⟩ : syracuseStep 7377419 = 11066129) B11066129
theorem B2626063 : Blo 1727064 2626063 := bstep (se 1 (by rfl) ⟨1969547, by rfl⟩ : syracuseStep 2626063 = 3939095) B3939095
theorem B2593295 : Blo 1727064 2593295 := bstep (se 1 (by rfl) ⟨1944971, by rfl⟩ : syracuseStep 2593295 = 3889943) B3889943
theorem B2593337 : Blo 1727064 2593337 := bstep (se 2 (by rfl) ⟨972501, by rfl⟩ : syracuseStep 2593337 = 1945003) B1945003
theorem B3887675 : Blo 1727064 3887675 := bstep (se 1 (by rfl) ⟨2915756, by rfl⟩ : syracuseStep 3887675 = 5831513) B5831513
theorem B2593415 : Blo 1727064 2593415 := bstep (se 1 (by rfl) ⟨1945061, by rfl⟩ : syracuseStep 2593415 = 3890123) B3890123
theorem B2593451 : Blo 1727064 2593451 := bstep (se 1 (by rfl) ⟨1945088, by rfl⟩ : syracuseStep 2593451 = 3890177) B3890177
theorem B3887801 : Blo 1727064 3887801 := bstep (se 2 (by rfl) ⟨1457925, by rfl⟩ : syracuseStep 3887801 = 2915851) B2915851
theorem B8303305 : Blo 1727064 8303305 := bstep (se 2 (by rfl) ⟨3113739, by rfl⟩ : syracuseStep 8303305 = 6227479) B6227479
theorem B3281609 : Blo 1727064 3281609 := bstep (se 2 (by rfl) ⟨1230603, by rfl⟩ : syracuseStep 3281609 = 2461207) B2461207
theorem B2593481 : Blo 1727064 2593481 := bstep (se 2 (by rfl) ⟨972555, by rfl⟩ : syracuseStep 2593481 = 1945111) B1945111
theorem B23646937 : Blo 1727064 23646937 := bstep (se 2 (by rfl) ⟨8867601, by rfl⟩ : syracuseStep 23646937 = 17735203) B17735203
theorem B6558479 : Blo 1727064 6558479 := bstep (se 1 (by rfl) ⟨4918859, by rfl⟩ : syracuseStep 6558479 = 9837719) B9837719
theorem B34124581 : Blo 1727064 34124581 := bstep (se 4 (by rfl) ⟨3199179, by rfl⟩ : syracuseStep 34124581 = 6398359) B6398359
theorem B3691307 : Blo 1727064 3691307 := bstep (se 1 (by rfl) ⟨2768480, by rfl⟩ : syracuseStep 3691307 = 5536961) B5536961
theorem B19690289 : Blo 1727064 19690289 := bstep (se 2 (by rfl) ⟨7383858, by rfl⟩ : syracuseStep 19690289 = 14767717) B14767717
theorem B2593595 : Blo 1727064 2593595 := bstep (se 1 (by rfl) ⟨1945196, by rfl⟩ : syracuseStep 2593595 = 3890393) B3890393
theorem B2216875 : Blo 1727064 2216875 := bstep (se 1 (by rfl) ⟨1662656, by rfl⟩ : syracuseStep 2216875 = 3325313) B3325313
theorem B6230969 : Blo 1727064 6230969 := bstep (se 2 (by rfl) ⟨2336613, by rfl⟩ : syracuseStep 6230969 = 4673227) B4673227
theorem B3888143 : Blo 1727064 3888143 := bstep (se 1 (by rfl) ⟨2916107, by rfl⟩ : syracuseStep 3888143 = 5832215) B5832215
theorem B3888161 : Blo 1727064 3888161 := bstep (se 2 (by rfl) ⟨1458060, by rfl⟩ : syracuseStep 3888161 = 2916121) B2916121
theorem B4371641 : Blo 1727064 4371641 := bstep (se 2 (by rfl) ⟨1639365, by rfl⟩ : syracuseStep 4371641 = 3278731) B3278731
theorem B11072713 : Blo 1727064 11072713 := bstep (se 2 (by rfl) ⟨4152267, by rfl⟩ : syracuseStep 11072713 = 8304535) B8304535
theorem B5829947 : Blo 1727064 5829947 := bstep (se 1 (by rfl) ⟨4372460, by rfl⟩ : syracuseStep 5829947 = 8744921) B8744921
theorem B4150615 : Blo 1727064 4150615 := bstep (se 1 (by rfl) ⟨3112961, by rfl⟩ : syracuseStep 4150615 = 6225923) B6225923
theorem B3888503 : Blo 1727064 3888503 := bstep (se 1 (by rfl) ⟨2916377, by rfl⟩ : syracuseStep 3888503 = 5832755) B5832755
theorem B6231431 : Blo 1727064 6231431 := bstep (se 1 (by rfl) ⟨4673573, by rfl⟩ : syracuseStep 6231431 = 9347147) B9347147
theorem B13121027 : Blo 1727064 13121027 := bstep (se 1 (by rfl) ⟨9840770, by rfl⟩ : syracuseStep 13121027 = 19681541) B19681541
theorem B3888683 : Blo 1727064 3888683 := bstep (se 1 (by rfl) ⟨2916512, by rfl⟩ : syracuseStep 3888683 = 5833025) B5833025
theorem B9836261 : Blo 1727064 9836261 := bstep (se 4 (by rfl) ⟨922149, by rfl⟩ : syracuseStep 9836261 = 1844299) B1844299
theorem B35452673 : Blo 1727064 35452673 := bstep (se 2 (by rfl) ⟨13294752, by rfl⟩ : syracuseStep 35452673 = 26589505) B26589505
theorem B5830433 : Blo 1727064 5830433 := bstep (se 2 (by rfl) ⟨2186412, by rfl⟩ : syracuseStep 5830433 = 4372825) B4372825
theorem B4372339 : Blo 1727064 4372339 := bstep (se 1 (by rfl) ⟨3279254, by rfl⟩ : syracuseStep 4372339 = 6558509) B6558509
theorem B3889043 : Blo 1727064 3889043 := bstep (se 1 (by rfl) ⟨2916782, by rfl⟩ : syracuseStep 3889043 = 5833565) B5833565
theorem B3889097 : Blo 1727064 3889097 := bstep (se 2 (by rfl) ⟨1458411, by rfl⟩ : syracuseStep 3889097 = 2916823) B2916823
theorem B9975773 : Blo 1727064 9975773 := bstep (se 3 (by rfl) ⟨1870457, by rfl⟩ : syracuseStep 9975773 = 3740915) B3740915
theorem B4372481 : Blo 1727064 4372481 := bstep (se 2 (by rfl) ⟨1639680, by rfl⟩ : syracuseStep 4372481 = 3279361) B3279361
theorem B10508291 : Blo 1727064 10508291 := bstep (se 1 (by rfl) ⟨7881218, by rfl⟩ : syracuseStep 10508291 = 15762437) B15762437
theorem B6830123 : Blo 1727064 6830123 := bstep (se 1 (by rfl) ⟨5122592, by rfl⟩ : syracuseStep 6830123 = 10245185) B10245185
theorem B4921661 : Blo 1727064 4921661 := bstep (se 3 (by rfl) ⟨922811, by rfl⟩ : syracuseStep 4921661 = 1845623) B1845623
theorem B5831027 : Blo 1727064 5831027 := bstep (se 1 (by rfl) ⟨4373270, by rfl⟩ : syracuseStep 5831027 = 8746541) B8746541
theorem B6560135 : Blo 1727064 6560135 := bstep (se 1 (by rfl) ⟨4920101, by rfl⟩ : syracuseStep 6560135 = 9840203) B9840203
theorem B4372937 : Blo 1727064 4372937 := bstep (se 2 (by rfl) ⟨1639851, by rfl⟩ : syracuseStep 4372937 = 3279703) B3279703
theorem B16603613 : Blo 1727064 16603613 := bstep (se 3 (by rfl) ⟨3113177, by rfl⟩ : syracuseStep 16603613 = 6226355) B6226355
theorem B12450347 : Blo 1727064 12450347 := bstep (se 1 (by rfl) ⟨9337760, by rfl⟩ : syracuseStep 12450347 = 18675521) B18675521
theorem B2914859 : Blo 1727064 2914859 := bstep (se 1 (by rfl) ⟨2186144, by rfl⟩ : syracuseStep 2914859 = 4372289) B4372289
theorem B1727111 : Blo 1727064 1727111 := bstep (se 1 (by rfl) ⟨1295333, by rfl⟩ : syracuseStep 1727111 = 2590667) B2590667
theorem B3889799 : Blo 1727064 3889799 := bstep (se 1 (by rfl) ⟨2917349, by rfl⟩ : syracuseStep 3889799 = 5834699) B5834699
theorem B1727119 : Blo 1727064 1727119 := bstep (se 1 (by rfl) ⟨1295339, by rfl⟩ : syracuseStep 1727119 = 2590679) B2590679
theorem B1727163 : Blo 1727064 1727163 := bstep (se 1 (by rfl) ⟨1295372, by rfl⟩ : syracuseStep 1727163 = 2590745) B2590745
theorem B16603841 : Blo 1727064 16603841 := bstep (se 2 (by rfl) ⟨6226440, by rfl⟩ : syracuseStep 16603841 = 12452881) B12452881
theorem B7379657 : Blo 1727064 7379657 := bstep (se 2 (by rfl) ⟨2767371, by rfl⟩ : syracuseStep 7379657 = 5534743) B5534743
theorem B56048345 : Blo 1727064 56048345 := bstep (se 2 (by rfl) ⟨21018129, by rfl⟩ : syracuseStep 56048345 = 42036259) B42036259
theorem B1727239 : Blo 1727064 1727239 := bstep (se 1 (by rfl) ⟨1295429, by rfl⟩ : syracuseStep 1727239 = 2590859) B2590859
theorem B1727247 : Blo 1727064 1727247 := bstep (se 1 (by rfl) ⟨1295435, by rfl⟩ : syracuseStep 1727247 = 2590871) B2590871
theorem B4373291 : Blo 1727064 4373291 := bstep (se 1 (by rfl) ⟨3279968, by rfl⟩ : syracuseStep 4373291 = 6559937) B6559937
theorem B1727291 : Blo 1727064 1727291 := bstep (se 1 (by rfl) ⟨1295468, by rfl⟩ : syracuseStep 1727291 = 2590937) B2590937
theorem B3889979 : Blo 1727064 3889979 := bstep (se 1 (by rfl) ⟨2917484, by rfl⟩ : syracuseStep 3889979 = 5834969) B5834969
theorem B5053271 : Blo 1727064 5053271 := bstep (se 1 (by rfl) ⟨3789953, by rfl⟩ : syracuseStep 5053271 = 7579907) B7579907
theorem B2186119 : Blo 1727064 2186119 := bstep (se 1 (by rfl) ⟨1639589, by rfl⟩ : syracuseStep 2186119 = 3279179) B3279179
theorem B1727367 : Blo 1727064 1727367 := bstep (se 1 (by rfl) ⟨1295525, by rfl⟩ : syracuseStep 1727367 = 2591051) B2591051
theorem B1727375 : Blo 1727064 1727375 := bstep (se 1 (by rfl) ⟨1295531, by rfl⟩ : syracuseStep 1727375 = 2591063) B2591063
theorem B2915257 : Blo 1727064 2915257 := bstep (se 2 (by rfl) ⟨1093221, by rfl⟩ : syracuseStep 2915257 = 2186443) B2186443
theorem B1727419 : Blo 1727064 1727419 := bstep (se 1 (by rfl) ⟨1295564, by rfl⟩ : syracuseStep 1727419 = 2591129) B2591129
theorem B3890105 : Blo 1727064 3890105 := bstep (se 2 (by rfl) ⟨1458789, by rfl⟩ : syracuseStep 3890105 = 2917579) B2917579
theorem B1727495 : Blo 1727064 1727495 := bstep (se 1 (by rfl) ⟨1295621, by rfl⟩ : syracuseStep 1727495 = 2591243) B2591243
theorem B1727503 : Blo 1727064 1727503 := bstep (se 1 (by rfl) ⟨1295627, by rfl⟩ : syracuseStep 1727503 = 2591255) B2591255
theorem B9845783 : Blo 1727064 9845783 := bstep (se 1 (by rfl) ⟨7384337, by rfl⟩ : syracuseStep 9845783 = 14768675) B14768675
theorem B1727547 : Blo 1727064 1727547 := bstep (se 1 (by rfl) ⟨1295660, by rfl⟩ : syracuseStep 1727547 = 2591321) B2591321
theorem B1727623 : Blo 1727064 1727623 := bstep (se 1 (by rfl) ⟨1295717, by rfl⟩ : syracuseStep 1727623 = 2591435) B2591435
theorem B1727631 : Blo 1727064 1727631 := bstep (se 1 (by rfl) ⟨1295723, by rfl⟩ : syracuseStep 1727631 = 2591447) B2591447
theorem B1727675 : Blo 1727064 1727675 := bstep (se 1 (by rfl) ⟨1295756, by rfl⟩ : syracuseStep 1727675 = 2591513) B2591513
theorem B1727751 : Blo 1727064 1727751 := bstep (se 1 (by rfl) ⟨1295813, by rfl⟩ : syracuseStep 1727751 = 2591627) B2591627
theorem B1727759 : Blo 1727064 1727759 := bstep (se 1 (by rfl) ⟨1295819, by rfl⟩ : syracuseStep 1727759 = 2591639) B2591639
theorem B16833809 : Blo 1727064 16833809 := bstep (se 2 (by rfl) ⟨6312678, by rfl⟩ : syracuseStep 16833809 = 12625357) B12625357
theorem B4922653 : Blo 1727064 4922653 := bstep (se 3 (by rfl) ⟨922997, by rfl⟩ : syracuseStep 4922653 = 1845995) B1845995
theorem B1727803 : Blo 1727064 1727803 := bstep (se 1 (by rfl) ⟨1295852, by rfl⟩ : syracuseStep 1727803 = 2591705) B2591705
theorem B2186615 : Blo 1727064 2186615 := bstep (se 1 (by rfl) ⟨1639961, by rfl⟩ : syracuseStep 2186615 = 3279923) B3279923
theorem B1727879 : Blo 1727064 1727879 := bstep (se 1 (by rfl) ⟨1295909, by rfl⟩ : syracuseStep 1727879 = 2591819) B2591819
theorem B1727887 : Blo 1727064 1727887 := bstep (se 1 (by rfl) ⟨1295915, by rfl⟩ : syracuseStep 1727887 = 2591831) B2591831
theorem B5537177 : Blo 1727064 5537177 := bstep (se 2 (by rfl) ⟨2076441, by rfl⟩ : syracuseStep 5537177 = 4152883) B4152883
theorem B1727931 : Blo 1727064 1727931 := bstep (se 1 (by rfl) ⟨1295948, by rfl⟩ : syracuseStep 1727931 = 2591897) B2591897
theorem B1728007 : Blo 1727064 1728007 := bstep (se 1 (by rfl) ⟨1296005, by rfl⟩ : syracuseStep 1728007 = 2592011) B2592011
theorem B2186767 : Blo 1727064 2186767 := bstep (se 1 (by rfl) ⟨1640075, by rfl⟩ : syracuseStep 2186767 = 3280151) B3280151
theorem B1728015 : Blo 1727064 1728015 := bstep (se 1 (by rfl) ⟨1296011, by rfl⟩ : syracuseStep 1728015 = 2592023) B2592023
theorem B1728059 : Blo 1727064 1728059 := bstep (se 1 (by rfl) ⟨1296044, by rfl⟩ : syracuseStep 1728059 = 2592089) B2592089
theorem B7003709 : Blo 1727064 7003709 := bstep (se 3 (by rfl) ⟨1313195, by rfl⟩ : syracuseStep 7003709 = 2626391) B2626391
theorem B2915959 : Blo 1727064 2915959 := bstep (se 1 (by rfl) ⟨2186969, by rfl⟩ : syracuseStep 2915959 = 4373939) B4373939
theorem B1728135 : Blo 1727064 1728135 := bstep (se 1 (by rfl) ⟨1296101, by rfl⟩ : syracuseStep 1728135 = 2592203) B2592203
theorem B1728143 : Blo 1727064 1728143 := bstep (se 1 (by rfl) ⟨1296107, by rfl⟩ : syracuseStep 1728143 = 2592215) B2592215
theorem B2186939 : Blo 1727064 2186939 := bstep (se 1 (by rfl) ⟨1640204, by rfl⟩ : syracuseStep 2186939 = 3280409) B3280409
theorem B1728187 : Blo 1727064 1728187 := bstep (se 1 (by rfl) ⟨1296140, by rfl⟩ : syracuseStep 1728187 = 2592281) B2592281
theorem B1728263 : Blo 1727064 1728263 := bstep (se 1 (by rfl) ⟨1296197, by rfl⟩ : syracuseStep 1728263 = 2592395) B2592395
theorem B4374283 : Blo 1727064 4374283 := bstep (se 1 (by rfl) ⟨3280712, by rfl⟩ : syracuseStep 4374283 = 6561425) B6561425
theorem B1728271 : Blo 1727064 1728271 := bstep (se 1 (by rfl) ⟨1296203, by rfl⟩ : syracuseStep 1728271 = 2592407) B2592407
theorem B21020465 : Blo 1727064 21020465 := bstep (se 2 (by rfl) ⟨7882674, by rfl⟩ : syracuseStep 21020465 = 15765349) B15765349
theorem B2916155 : Blo 1727064 2916155 := bstep (se 1 (by rfl) ⟨2187116, by rfl⟩ : syracuseStep 2916155 = 4374233) B4374233
theorem B1728315 : Blo 1727064 1728315 := bstep (se 1 (by rfl) ⟨1296236, by rfl⟩ : syracuseStep 1728315 = 2592473) B2592473
theorem B1728391 : Blo 1727064 1728391 := bstep (se 1 (by rfl) ⟨1296293, by rfl⟩ : syracuseStep 1728391 = 2592587) B2592587
theorem B1728399 : Blo 1727064 1728399 := bstep (se 1 (by rfl) ⟨1296299, by rfl⟩ : syracuseStep 1728399 = 2592599) B2592599
theorem B4374425 : Blo 1727064 4374425 := bstep (se 2 (by rfl) ⟨1640409, by rfl⟩ : syracuseStep 4374425 = 3280819) B3280819
theorem B1728443 : Blo 1727064 1728443 := bstep (se 1 (by rfl) ⟨1296332, by rfl⟩ : syracuseStep 1728443 = 2592665) B2592665
theorem B2916391 : Blo 1727064 2916391 := bstep (se 1 (by rfl) ⟨2187293, by rfl⟩ : syracuseStep 2916391 = 4374587) B4374587
theorem B1728551 : Blo 1727064 1728551 := bstep (se 1 (by rfl) ⟨1296413, by rfl⟩ : syracuseStep 1728551 = 2592827) B2592827
theorem B4374607 : Blo 1727064 4374607 := bstep (se 1 (by rfl) ⟨3280955, by rfl⟩ : syracuseStep 4374607 = 6561911) B6561911
theorem B1728591 : Blo 1727064 1728591 := bstep (se 1 (by rfl) ⟨1296443, by rfl⟩ : syracuseStep 1728591 = 2592887) B2592887
theorem B1728607 : Blo 1727064 1728607 := bstep (se 1 (by rfl) ⟨1296455, by rfl⟩ : syracuseStep 1728607 = 2592911) B2592911
theorem B1728635 : Blo 1727064 1728635 := bstep (se 1 (by rfl) ⟨1296476, by rfl⟩ : syracuseStep 1728635 = 2592953) B2592953
theorem B1728687 : Blo 1727064 1728687 := bstep (se 1 (by rfl) ⟨1296515, by rfl⟩ : syracuseStep 1728687 = 2593031) B2593031
theorem B1728711 : Blo 1727064 1728711 := bstep (se 1 (by rfl) ⟨1296533, by rfl⟩ : syracuseStep 1728711 = 2593067) B2593067
theorem B1728731 : Blo 1727064 1728731 := bstep (se 1 (by rfl) ⟨1296548, by rfl⟩ : syracuseStep 1728731 = 2593097) B2593097
theorem B5832971 : Blo 1727064 5832971 := bstep (se 1 (by rfl) ⟨4374728, by rfl⟩ : syracuseStep 5832971 = 8749457) B8749457
theorem B1728807 : Blo 1727064 1728807 := bstep (se 1 (by rfl) ⟨1296605, by rfl⟩ : syracuseStep 1728807 = 2593211) B2593211
theorem B1728847 : Blo 1727064 1728847 := bstep (se 1 (by rfl) ⟨1296635, by rfl⟩ : syracuseStep 1728847 = 2593271) B2593271
theorem B1728863 : Blo 1727064 1728863 := bstep (se 1 (by rfl) ⟨1296647, by rfl⟩ : syracuseStep 1728863 = 2593295) B2593295
theorem B2916715 : Blo 1727064 2916715 := bstep (se 1 (by rfl) ⟨2187536, by rfl⟩ : syracuseStep 2916715 = 4375073) B4375073
theorem B1728891 : Blo 1727064 1728891 := bstep (se 1 (by rfl) ⟨1296668, by rfl⟩ : syracuseStep 1728891 = 2593337) B2593337
theorem B1728943 : Blo 1727064 1728943 := bstep (se 1 (by rfl) ⟨1296707, by rfl⟩ : syracuseStep 1728943 = 2593415) B2593415
theorem B1728967 : Blo 1727064 1728967 := bstep (se 1 (by rfl) ⟨1296725, by rfl⟩ : syracuseStep 1728967 = 2593451) B2593451
theorem B2187739 : Blo 1727064 2187739 := bstep (se 1 (by rfl) ⟨1640804, by rfl⟩ : syracuseStep 2187739 = 3281609) B3281609
theorem B1728987 : Blo 1727064 1728987 := bstep (se 1 (by rfl) ⟨1296740, by rfl⟩ : syracuseStep 1728987 = 2593481) B2593481
theorem B5833241 : Blo 1727064 5833241 := bstep (se 2 (by rfl) ⟨2187465, by rfl⟩ : syracuseStep 5833241 = 4374931) B4374931
theorem B1729063 : Blo 1727064 1729063 := bstep (se 1 (by rfl) ⟨1296797, by rfl⟩ : syracuseStep 1729063 = 2593595) B2593595
theorem B4153979 : Blo 1727064 4153979 := bstep (se 1 (by rfl) ⟨3115484, by rfl⟩ : syracuseStep 4153979 = 6230969) B6230969
theorem B3326675 : Blo 1727064 3326675 := bstep (se 1 (by rfl) ⟨2495006, by rfl⟩ : syracuseStep 3326675 = 4990013) B4990013
theorem B4375255 : Blo 1727064 4375255 := bstep (se 1 (by rfl) ⟨3281441, by rfl⟩ : syracuseStep 4375255 = 6562883) B6562883
theorem B4154105 : Blo 1727064 4154105 := bstep (se 2 (by rfl) ⟨1557789, by rfl⟩ : syracuseStep 4154105 = 3115579) B3115579
theorem B22151987 : Blo 1727064 22151987 := bstep (se 1 (by rfl) ⟨16613990, by rfl⟩ : syracuseStep 22151987 = 33227981) B33227981
theorem B44917577 : Blo 1727064 44917577 := bstep (se 2 (by rfl) ⟨16844091, by rfl⟩ : syracuseStep 44917577 = 33688183) B33688183
theorem B13124429 : Blo 1727064 13124429 := bstep (se 3 (by rfl) ⟨2460830, by rfl⟩ : syracuseStep 13124429 = 4921661) B4921661
theorem B4154287 : Blo 1727064 4154287 := bstep (se 1 (by rfl) ⟨3115715, by rfl⟩ : syracuseStep 4154287 = 6231431) B6231431
theorem B11985893 : Blo 1727064 11985893 := bstep (se 4 (by rfl) ⟨1123677, by rfl⟩ : syracuseStep 11985893 = 2247355) B2247355
theorem B5538817 : Blo 1727064 5538817 := bstep (se 2 (by rfl) ⟨2077056, by rfl⟩ : syracuseStep 5538817 = 4154113) B4154113
theorem B4375559 : Blo 1727064 4375559 := bstep (se 1 (by rfl) ⟨3281669, by rfl⟩ : syracuseStep 4375559 = 6563339) B6563339
theorem B24921107 : Blo 1727064 24921107 := bstep (se 1 (by rfl) ⟨18690830, by rfl⟩ : syracuseStep 24921107 = 37381661) B37381661
theorem B7988377 : Blo 1727064 7988377 := bstep (se 2 (by rfl) ⟨2995641, by rfl⟩ : syracuseStep 7988377 = 5991283) B5991283
theorem B23635115 : Blo 1727064 23635115 := bstep (se 1 (by rfl) ⟨17726336, by rfl⟩ : syracuseStep 23635115 = 35452673) B35452673
theorem B7005527 : Blo 1727064 7005527 := bstep (se 1 (by rfl) ⟨5254145, by rfl⟩ : syracuseStep 7005527 = 10508291) B10508291
theorem B35489117 : Blo 1727064 35489117 := bstep (se 3 (by rfl) ⟨6654209, by rfl⟩ : syracuseStep 35489117 = 13308419) B13308419
theorem B2917775 : Blo 1727064 2917775 := bstep (se 1 (by rfl) ⟨2188331, by rfl⟩ : syracuseStep 2917775 = 4376663) B4376663
theorem B14763617 : Blo 1727064 14763617 := bstep (se 2 (by rfl) ⟨5536356, by rfl⟩ : syracuseStep 14763617 = 11072713) B11072713
theorem B5834375 : Blo 1727064 5834375 := bstep (se 1 (by rfl) ⟨4375781, by rfl⟩ : syracuseStep 5834375 = 8751563) B8751563
theorem B11069075 : Blo 1727064 11069075 := bstep (se 1 (by rfl) ⟨8301806, by rfl⟩ : syracuseStep 11069075 = 16603613) B16603613
theorem B5834429 : Blo 1727064 5834429 := bstep (se 3 (by rfl) ⟨1093955, by rfl⟩ : syracuseStep 5834429 = 2187911) B2187911
theorem B8300231 : Blo 1727064 8300231 := bstep (se 1 (by rfl) ⟨6225173, by rfl⟩ : syracuseStep 8300231 = 12450347) B12450347
theorem B1943239 : Blo 1727064 1943239 := bstep (se 1 (by rfl) ⟨1457429, by rfl⟩ : syracuseStep 1943239 = 2914859) B2914859
theorem B6563537 : Blo 1727064 6563537 := bstep (se 2 (by rfl) ⟨2461326, by rfl⟩ : syracuseStep 6563537 = 4922653) B4922653
theorem B11069227 : Blo 1727064 11069227 := bstep (se 1 (by rfl) ⟨8301920, by rfl⟩ : syracuseStep 11069227 = 16603841) B16603841
theorem B37365563 : Blo 1727064 37365563 := bstep (se 1 (by rfl) ⟨28024172, by rfl⟩ : syracuseStep 37365563 = 56048345) B56048345
theorem B8750915 : Blo 1727064 8750915 := bstep (se 1 (by rfl) ⟨6563186, by rfl⟩ : syracuseStep 8750915 = 13126373) B13126373
theorem B5834591 : Blo 1727064 5834591 := bstep (se 1 (by rfl) ⟨4375943, by rfl⟩ : syracuseStep 5834591 = 8751887) B8751887
theorem B19687373 : Blo 1727064 19687373 := bstep (se 3 (by rfl) ⟨3691382, by rfl⟩ : syracuseStep 19687373 = 7382765) B7382765
theorem B5834753 : Blo 1727064 5834753 := bstep (se 2 (by rfl) ⟨2188032, by rfl⟩ : syracuseStep 5834753 = 4376065) B4376065
theorem B6563855 : Blo 1727064 6563855 := bstep (se 1 (by rfl) ⟨4922891, by rfl⟩ : syracuseStep 6563855 = 9845783) B9845783
theorem B2590799 : Blo 1727064 2590799 := bstep (se 1 (by rfl) ⟨1943099, by rfl⟩ : syracuseStep 2590799 = 3886199) B3886199
theorem B2590919 : Blo 1727064 2590919 := bstep (se 1 (by rfl) ⟨1943189, by rfl⟩ : syracuseStep 2590919 = 3886379) B3886379
theorem B2591081 : Blo 1727064 2591081 := bstep (se 2 (by rfl) ⟨971655, by rfl⟩ : syracuseStep 2591081 = 1943311) B1943311
theorem B2460079 : Blo 1727064 2460079 := bstep (se 1 (by rfl) ⟨1845059, by rfl⟩ : syracuseStep 2460079 = 3690119) B3690119
theorem B2591159 : Blo 1727064 2591159 := bstep (se 1 (by rfl) ⟨1943369, by rfl⟩ : syracuseStep 2591159 = 3886739) B3886739
theorem B2591195 : Blo 1727064 2591195 := bstep (se 1 (by rfl) ⟨1943396, by rfl⟩ : syracuseStep 2591195 = 3886793) B3886793
theorem B1944103 : Blo 1727064 1944103 := bstep (se 1 (by rfl) ⟨1458077, by rfl⟩ : syracuseStep 1944103 = 2916155) B2916155
theorem B14764679 : Blo 1727064 14764679 := bstep (se 1 (by rfl) ⟨11073509, by rfl⟩ : syracuseStep 14764679 = 22147019) B22147019
theorem B5835563 : Blo 1727064 5835563 := bstep (se 1 (by rfl) ⟨4376672, by rfl⟩ : syracuseStep 5835563 = 8753345) B8753345
theorem B8743787 : Blo 1727064 8743787 := bstep (se 1 (by rfl) ⟨6557840, by rfl⟩ : syracuseStep 8743787 = 13115681) B13115681
theorem B2591663 : Blo 1727064 2591663 := bstep (se 1 (by rfl) ⟨1943747, by rfl⟩ : syracuseStep 2591663 = 3887495) B3887495
theorem B4918279 : Blo 1727064 4918279 := bstep (se 1 (by rfl) ⟨3688709, by rfl⟩ : syracuseStep 4918279 = 7377419) B7377419
theorem B2591753 : Blo 1727064 2591753 := bstep (se 2 (by rfl) ⟨971907, by rfl⟩ : syracuseStep 2591753 = 1943815) B1943815
theorem B2591783 : Blo 1727064 2591783 := bstep (se 1 (by rfl) ⟨1943837, by rfl⟩ : syracuseStep 2591783 = 3887675) B3887675
theorem B9972815 : Blo 1727064 9972815 := bstep (se 1 (by rfl) ⟨7479611, by rfl⟩ : syracuseStep 9972815 = 14959223) B14959223
theorem B72854645 : Blo 1727064 72854645 := bstep (se 5 (by rfl) ⟨3415061, by rfl⟩ : syracuseStep 72854645 = 6830123) B6830123
theorem B2591867 : Blo 1727064 2591867 := bstep (se 1 (by rfl) ⟨1943900, by rfl⟩ : syracuseStep 2591867 = 3887801) B3887801
theorem B2460871 : Blo 1727064 2460871 := bstep (se 1 (by rfl) ⟨1845653, by rfl⟩ : syracuseStep 2460871 = 3691307) B3691307
theorem B13126859 : Blo 1727064 13126859 := bstep (se 1 (by rfl) ⟨9845144, by rfl⟩ : syracuseStep 13126859 = 19690289) B19690289
theorem B2591993 : Blo 1727064 2591993 := bstep (se 2 (by rfl) ⟨971997, by rfl⟩ : syracuseStep 2591993 = 1943995) B1943995
theorem B2592095 : Blo 1727064 2592095 := bstep (se 1 (by rfl) ⟨1944071, by rfl⟩ : syracuseStep 2592095 = 3888143) B3888143
theorem B2592107 : Blo 1727064 2592107 := bstep (se 1 (by rfl) ⟨1944080, by rfl⟩ : syracuseStep 2592107 = 3888161) B3888161
theorem B13299059 : Blo 1727064 13299059 := bstep (se 1 (by rfl) ⟨9974294, by rfl⟩ : syracuseStep 13299059 = 19948589) B19948589
theorem B12152207 : Blo 1727064 12152207 := bstep (se 1 (by rfl) ⟨9114155, by rfl⟩ : syracuseStep 12152207 = 18228311) B18228311
theorem B9842093 : Blo 1727064 9842093 := bstep (se 3 (by rfl) ⟨1845392, by rfl⟩ : syracuseStep 9842093 = 3690785) B3690785
theorem B8744435 : Blo 1727064 8744435 := bstep (se 1 (by rfl) ⟨6558326, by rfl⟩ : syracuseStep 8744435 = 13116653) B13116653
theorem B3886631 : Blo 1727064 3886631 := bstep (se 1 (by rfl) ⟨2914973, by rfl⟩ : syracuseStep 3886631 = 5829947) B5829947
theorem B2592335 : Blo 1727064 2592335 := bstep (se 1 (by rfl) ⟨1944251, by rfl⟩ : syracuseStep 2592335 = 3888503) B3888503
theorem B11071073 : Blo 1727064 11071073 := bstep (se 2 (by rfl) ⟨4151652, by rfl⟩ : syracuseStep 11071073 = 8303305) B8303305
theorem B7384715 : Blo 1727064 7384715 := bstep (se 1 (by rfl) ⟨5538536, by rfl⟩ : syracuseStep 7384715 = 11077073) B11077073
theorem B5533373 : Blo 1727064 5533373 := bstep (se 3 (by rfl) ⟨1037507, by rfl⟩ : syracuseStep 5533373 = 2075015) B2075015
theorem B42626749 : Blo 1727064 42626749 := bstep (se 3 (by rfl) ⟨7992515, by rfl⟩ : syracuseStep 42626749 = 15985031) B15985031
theorem B14970557 : Blo 1727064 14970557 := bstep (se 3 (by rfl) ⟨2806979, by rfl⟩ : syracuseStep 14970557 = 5613959) B5613959
theorem B2592455 : Blo 1727064 2592455 := bstep (se 1 (by rfl) ⟨1944341, by rfl⟩ : syracuseStep 2592455 = 3888683) B3888683
theorem B6557507 : Blo 1727064 6557507 := bstep (se 1 (by rfl) ⟨4918130, by rfl⟩ : syracuseStep 6557507 = 9836261) B9836261
theorem B2592617 : Blo 1727064 2592617 := bstep (se 2 (by rfl) ⟨972231, by rfl⟩ : syracuseStep 2592617 = 1944463) B1944463
theorem B3886955 : Blo 1727064 3886955 := bstep (se 1 (by rfl) ⟨2915216, by rfl⟩ : syracuseStep 3886955 = 5830433) B5830433
theorem B4919201 : Blo 1727064 4919201 := bstep (se 2 (by rfl) ⟨1844700, by rfl⟩ : syracuseStep 4919201 = 3689401) B3689401
theorem B3887009 : Blo 1727064 3887009 := bstep (se 2 (by rfl) ⟨1457628, by rfl⟩ : syracuseStep 3887009 = 2915257) B2915257
theorem B9842593 : Blo 1727064 9842593 := bstep (se 2 (by rfl) ⟨3690972, by rfl⟩ : syracuseStep 9842593 = 7381945) B7381945
theorem B2592695 : Blo 1727064 2592695 := bstep (se 1 (by rfl) ⟨1944521, by rfl⟩ : syracuseStep 2592695 = 3889043) B3889043
theorem B2592731 : Blo 1727064 2592731 := bstep (se 1 (by rfl) ⟨1944548, by rfl⟩ : syracuseStep 2592731 = 3889097) B3889097
theorem B13119569 : Blo 1727064 13119569 := bstep (se 2 (by rfl) ⟨4919838, by rfl⟩ : syracuseStep 13119569 = 9839677) B9839677
theorem B181997765 : Blo 1727064 181997765 := bstep (se 4 (by rfl) ⟨17062290, by rfl⟩ : syracuseStep 181997765 = 34124581) B34124581
theorem B3887351 : Blo 1727064 3887351 := bstep (se 1 (by rfl) ⟨2915513, by rfl⟩ : syracuseStep 3887351 = 5831027) B5831027
theorem B141914429 : Blo 1727064 141914429 := bstep (se 3 (by rfl) ⟨26608955, by rfl⟩ : syracuseStep 141914429 = 53217911) B53217911
theorem B7385431 : Blo 1727064 7385431 := bstep (se 1 (by rfl) ⟨5539073, by rfl⟩ : syracuseStep 7385431 = 11078147) B11078147
theorem B215789953 : Blo 1727064 215789953 := bstep (se 2 (by rfl) ⟨80921232, by rfl⟩ : syracuseStep 215789953 = 161842465) B161842465
theorem B2593199 : Blo 1727064 2593199 := bstep (se 1 (by rfl) ⟨1944899, by rfl⟩ : syracuseStep 2593199 = 3889799) B3889799
theorem B5534153 : Blo 1727064 5534153 := bstep (se 2 (by rfl) ⟨2075307, by rfl⟩ : syracuseStep 5534153 = 4150615) B4150615
theorem B5829083 : Blo 1727064 5829083 := bstep (se 1 (by rfl) ⟨4371812, by rfl⟩ : syracuseStep 5829083 = 8743625) B8743625
theorem B4919771 : Blo 1727064 4919771 := bstep (se 1 (by rfl) ⟨3689828, by rfl⟩ : syracuseStep 4919771 = 7379657) B7379657
theorem B2593289 : Blo 1727064 2593289 := bstep (se 2 (by rfl) ⟨972483, by rfl⟩ : syracuseStep 2593289 = 1944967) B1944967
theorem B2593319 : Blo 1727064 2593319 := bstep (se 1 (by rfl) ⟨1944989, by rfl⟩ : syracuseStep 2593319 = 3889979) B3889979
theorem B3281465 : Blo 1727064 3281465 := bstep (se 2 (by rfl) ⟨1230549, by rfl⟩ : syracuseStep 3281465 = 2461099) B2461099
theorem B2593403 : Blo 1727064 2593403 := bstep (se 1 (by rfl) ⟨1945052, by rfl⟩ : syracuseStep 2593403 = 3890105) B3890105
theorem B159544019 : Blo 1727064 159544019 := bstep (se 1 (by rfl) ⟨119658014, by rfl⟩ : syracuseStep 159544019 = 239316029) B239316029
theorem B2593529 : Blo 1727064 2593529 := bstep (se 2 (by rfl) ⟨972573, by rfl⟩ : syracuseStep 2593529 = 1945147) B1945147
theorem B8745731 : Blo 1727064 8745731 := bstep (se 1 (by rfl) ⟨6559298, by rfl⟩ : syracuseStep 8745731 = 13118597) B13118597
theorem B102413069 : Blo 1727064 102413069 := bstep (se 3 (by rfl) ⟨19202450, by rfl⟩ : syracuseStep 102413069 = 38404901) B38404901
theorem B3887945 : Blo 1727064 3887945 := bstep (se 2 (by rfl) ⟨1457979, by rfl⟩ : syracuseStep 3887945 = 2915959) B2915959
theorem B22147991 : Blo 1727064 22147991 := bstep (se 1 (by rfl) ⟨16610993, by rfl⟩ : syracuseStep 22147991 = 33221987) B33221987
theorem B3691451 : Blo 1727064 3691451 := bstep (se 1 (by rfl) ⟨2768588, by rfl⟩ : syracuseStep 3691451 = 5537177) B5537177
theorem B5829785 : Blo 1727064 5829785 := bstep (se 2 (by rfl) ⟨2186169, by rfl⟩ : syracuseStep 5829785 = 4372339) B4372339
theorem B14013643 : Blo 1727064 14013643 := bstep (se 1 (by rfl) ⟨10510232, by rfl⟩ : syracuseStep 14013643 = 21020465) B21020465
theorem B6231401 : Blo 1727064 6231401 := bstep (se 2 (by rfl) ⟨2336775, by rfl⟩ : syracuseStep 6231401 = 4673551) B4673551
theorem B14005669 : Blo 1727064 14005669 := bstep (se 4 (by rfl) ⟨1313031, by rfl⟩ : syracuseStep 14005669 = 2626063) B2626063
theorem B6559177 : Blo 1727064 6559177 := bstep (se 2 (by rfl) ⟨2459691, by rfl⟩ : syracuseStep 6559177 = 4919383) B4919383
theorem B4920841 : Blo 1727064 4920841 := bstep (se 2 (by rfl) ⟨1845315, by rfl⟩ : syracuseStep 4920841 = 3690631) B3690631
theorem B3888737 : Blo 1727064 3888737 := bstep (se 2 (by rfl) ⟨1458276, by rfl⟩ : syracuseStep 3888737 = 2916553) B2916553
theorem B9344659 : Blo 1727064 9344659 := bstep (se 1 (by rfl) ⟨7008494, by rfl⟩ : syracuseStep 9344659 = 14016989) B14016989
theorem B6559481 : Blo 1727064 6559481 := bstep (se 2 (by rfl) ⟨2459805, by rfl⟩ : syracuseStep 6559481 = 4919611) B4919611
theorem B4372319 : Blo 1727064 4372319 := bstep (se 1 (by rfl) ⟨3279239, by rfl⟩ : syracuseStep 4372319 = 6558479) B6558479
theorem B4921195 : Blo 1727064 4921195 := bstep (se 1 (by rfl) ⟨3690896, by rfl⟩ : syracuseStep 4921195 = 7381793) B7381793
theorem B6559649 : Blo 1727064 6559649 := bstep (se 2 (by rfl) ⟨2459868, by rfl⟩ : syracuseStep 6559649 = 4919737) B4919737
theorem B6559663 : Blo 1727064 6559663 := bstep (se 1 (by rfl) ⟨4919747, by rfl⟩ : syracuseStep 6559663 = 9839495) B9839495
theorem B3889079 : Blo 1727064 3889079 := bstep (se 1 (by rfl) ⟨2916809, by rfl⟩ : syracuseStep 3889079 = 5833619) B5833619
theorem B44890157 : Blo 1727064 44890157 := bstep (se 3 (by rfl) ⟨8416904, by rfl⟩ : syracuseStep 44890157 = 16833809) B16833809
theorem B49829975 : Blo 1727064 49829975 := bstep (se 1 (by rfl) ⟨37372481, by rfl⟩ : syracuseStep 49829975 = 74744963) B74744963
theorem B7379059 : Blo 1727064 7379059 := bstep (se 1 (by rfl) ⟨5534294, by rfl⟩ : syracuseStep 7379059 = 11068589) B11068589
theorem B2914427 : Blo 1727064 2914427 := bstep (se 1 (by rfl) ⟨2185820, by rfl⟩ : syracuseStep 2914427 = 4371641) B4371641
theorem B2767097 : Blo 1727064 2767097 := bstep (se 2 (by rfl) ⟨1037661, by rfl⟩ : syracuseStep 2767097 = 2075323) B2075323
theorem B31529249 : Blo 1727064 31529249 := bstep (se 2 (by rfl) ⟨11823468, by rfl⟩ : syracuseStep 31529249 = 23646937) B23646937
theorem B5830973 : Blo 1727064 5830973 := bstep (se 3 (by rfl) ⟨1093307, by rfl⟩ : syracuseStep 5830973 = 2186615) B2186615
theorem B8747351 : Blo 1727064 8747351 := bstep (se 1 (by rfl) ⟨6560513, by rfl⟩ : syracuseStep 8747351 = 13121027) B13121027
theorem B2914825 : Blo 1727064 2914825 := bstep (se 2 (by rfl) ⟨1093059, by rfl⟩ : syracuseStep 2914825 = 2186119) B2186119
theorem B3889673 : Blo 1727064 3889673 := bstep (se 2 (by rfl) ⟨1458627, by rfl⟩ : syracuseStep 3889673 = 2917255) B2917255
theorem B2955833 : Blo 1727064 2955833 := bstep (se 2 (by rfl) ⟨1108437, by rfl⟩ : syracuseStep 2955833 = 2216875) B2216875
theorem B1727071 : Blo 1727064 1727071 := bstep (se 1 (by rfl) ⟨1295303, by rfl⟩ : syracuseStep 1727071 = 2590607) B2590607
theorem B1727099 : Blo 1727064 1727099 := bstep (se 1 (by rfl) ⟨1295324, by rfl⟩ : syracuseStep 1727099 = 2590649) B2590649
theorem B6650515 : Blo 1727064 6650515 := bstep (se 1 (by rfl) ⟨4987886, by rfl⟩ : syracuseStep 6650515 = 9975773) B9975773
theorem B2914987 : Blo 1727064 2914987 := bstep (se 1 (by rfl) ⟨2186240, by rfl⟩ : syracuseStep 2914987 = 4372481) B4372481
theorem B1727151 : Blo 1727064 1727151 := bstep (se 1 (by rfl) ⟨1295363, by rfl⟩ : syracuseStep 1727151 = 2590727) B2590727
theorem B1727175 : Blo 1727064 1727175 := bstep (se 1 (by rfl) ⟨1295381, by rfl⟩ : syracuseStep 1727175 = 2590763) B2590763
theorem B1727195 : Blo 1727064 1727195 := bstep (se 1 (by rfl) ⟨1295396, by rfl⟩ : syracuseStep 1727195 = 2590793) B2590793
theorem B22133533 : Blo 1727064 22133533 := bstep (se 3 (by rfl) ⟨4150037, by rfl⟩ : syracuseStep 22133533 = 8300075) B8300075
theorem B1727271 : Blo 1727064 1727271 := bstep (se 1 (by rfl) ⟨1295453, by rfl⟩ : syracuseStep 1727271 = 2590907) B2590907
theorem B1727311 : Blo 1727064 1727311 := bstep (se 1 (by rfl) ⟨1295483, by rfl⟩ : syracuseStep 1727311 = 2590967) B2590967
theorem B1727327 : Blo 1727064 1727327 := bstep (se 1 (by rfl) ⟨1295495, by rfl⟩ : syracuseStep 1727327 = 2590991) B2590991
theorem B3890015 : Blo 1727064 3890015 := bstep (se 1 (by rfl) ⟨2917511, by rfl⟩ : syracuseStep 3890015 = 5835023) B5835023
theorem B6560621 : Blo 1727064 6560621 := bstep (se 3 (by rfl) ⟨1230116, by rfl⟩ : syracuseStep 6560621 = 2460233) B2460233
theorem B3742571 : Blo 1727064 3742571 := bstep (se 1 (by rfl) ⟨2806928, by rfl⟩ : syracuseStep 3742571 = 5613857) B5613857
theorem B1727355 : Blo 1727064 1727355 := bstep (se 1 (by rfl) ⟨1295516, by rfl⟩ : syracuseStep 1727355 = 2591033) B2591033
theorem B1727407 : Blo 1727064 1727407 := bstep (se 1 (by rfl) ⟨1295555, by rfl⟩ : syracuseStep 1727407 = 2591111) B2591111
theorem B4373423 : Blo 1727064 4373423 := bstep (se 1 (by rfl) ⟨3280067, by rfl⟩ : syracuseStep 4373423 = 6560135) B6560135
theorem B4922299 : Blo 1727064 4922299 := bstep (se 1 (by rfl) ⟨3691724, by rfl⟩ : syracuseStep 4922299 = 7383449) B7383449
theorem B1727431 : Blo 1727064 1727431 := bstep (se 1 (by rfl) ⟨1295573, by rfl⟩ : syracuseStep 1727431 = 2591147) B2591147
theorem B1727451 : Blo 1727064 1727451 := bstep (se 1 (by rfl) ⟨1295588, by rfl⟩ : syracuseStep 1727451 = 2591177) B2591177
theorem B2915291 : Blo 1727064 2915291 := bstep (se 1 (by rfl) ⟨2186468, by rfl⟩ : syracuseStep 2915291 = 4372937) B4372937
theorem B3890195 : Blo 1727064 3890195 := bstep (se 1 (by rfl) ⟨2917646, by rfl⟩ : syracuseStep 3890195 = 5835293) B5835293
theorem B1727527 : Blo 1727064 1727527 := bstep (se 1 (by rfl) ⟨1295645, by rfl⟩ : syracuseStep 1727527 = 2591291) B2591291
theorem B1727567 : Blo 1727064 1727567 := bstep (se 1 (by rfl) ⟨1295675, by rfl⟩ : syracuseStep 1727567 = 2591351) B2591351
theorem B1727583 : Blo 1727064 1727583 := bstep (se 1 (by rfl) ⟨1295687, by rfl⟩ : syracuseStep 1727583 = 2591375) B2591375
theorem B1727611 : Blo 1727064 1727611 := bstep (se 1 (by rfl) ⟨1295708, by rfl⟩ : syracuseStep 1727611 = 2591417) B2591417
theorem B5831837 : Blo 1727064 5831837 := bstep (se 3 (by rfl) ⟨1093469, by rfl⟩ : syracuseStep 5831837 = 2186939) B2186939
theorem B6560939 : Blo 1727064 6560939 := bstep (se 1 (by rfl) ⟨4920704, by rfl⟩ : syracuseStep 6560939 = 9841409) B9841409
theorem B4152491 : Blo 1727064 4152491 := bstep (se 1 (by rfl) ⟨3114368, by rfl⟩ : syracuseStep 4152491 = 6228737) B6228737
theorem B1727663 : Blo 1727064 1727663 := bstep (se 1 (by rfl) ⟨1295747, by rfl⟩ : syracuseStep 1727663 = 2591495) B2591495
theorem B1727687 : Blo 1727064 1727687 := bstep (se 1 (by rfl) ⟨1295765, by rfl⟩ : syracuseStep 1727687 = 2591531) B2591531
theorem B2915527 : Blo 1727064 2915527 := bstep (se 1 (by rfl) ⟨2186645, by rfl⟩ : syracuseStep 2915527 = 4373291) B4373291
theorem B1727707 : Blo 1727064 1727707 := bstep (se 1 (by rfl) ⟨1295780, by rfl⟩ : syracuseStep 1727707 = 2591561) B2591561
theorem B11066615 : Blo 1727064 11066615 := bstep (se 1 (by rfl) ⟨8299961, by rfl⟩ : syracuseStep 11066615 = 16599923) B16599923
theorem B1727783 : Blo 1727064 1727783 := bstep (se 1 (by rfl) ⟨1295837, by rfl⟩ : syracuseStep 1727783 = 2591675) B2591675
theorem B1727823 : Blo 1727064 1727823 := bstep (se 1 (by rfl) ⟨1295867, by rfl⟩ : syracuseStep 1727823 = 2591735) B2591735
theorem B1727839 : Blo 1727064 1727839 := bstep (se 1 (by rfl) ⟨1295879, by rfl⟩ : syracuseStep 1727839 = 2591759) B2591759
theorem B2915689 : Blo 1727064 2915689 := bstep (se 2 (by rfl) ⟨1093383, by rfl⟩ : syracuseStep 2915689 = 2186767) B2186767
theorem B1727867 : Blo 1727064 1727867 := bstep (se 1 (by rfl) ⟨1295900, by rfl⟩ : syracuseStep 1727867 = 2591801) B2591801
theorem B2186671 : Blo 1727064 2186671 := bstep (se 1 (by rfl) ⟨1640003, by rfl⟩ : syracuseStep 2186671 = 3280007) B3280007
theorem B1727919 : Blo 1727064 1727919 := bstep (se 1 (by rfl) ⟨1295939, by rfl⟩ : syracuseStep 1727919 = 2591879) B2591879
theorem B1727943 : Blo 1727064 1727943 := bstep (se 1 (by rfl) ⟨1295957, by rfl⟩ : syracuseStep 1727943 = 2591915) B2591915
theorem B1727963 : Blo 1727064 1727963 := bstep (se 1 (by rfl) ⟨1295972, by rfl⟩ : syracuseStep 1727963 = 2591945) B2591945
theorem B1728039 : Blo 1727064 1728039 := bstep (se 1 (by rfl) ⟨1296029, by rfl⟩ : syracuseStep 1728039 = 2592059) B2592059
theorem B13475389 : Blo 1727064 13475389 := bstep (se 3 (by rfl) ⟨2526635, by rfl⟩ : syracuseStep 13475389 = 5053271) B5053271
theorem B1728079 : Blo 1727064 1728079 := bstep (se 1 (by rfl) ⟨1296059, by rfl⟩ : syracuseStep 1728079 = 2592119) B2592119
theorem B1728095 : Blo 1727064 1728095 := bstep (se 1 (by rfl) ⟨1296071, by rfl⟩ : syracuseStep 1728095 = 2592143) B2592143
theorem B1728123 : Blo 1727064 1728123 := bstep (se 1 (by rfl) ⟨1296092, by rfl⟩ : syracuseStep 1728123 = 2592185) B2592185
theorem B9838219 : Blo 1727064 9838219 := bstep (se 1 (by rfl) ⟨7378664, by rfl⟩ : syracuseStep 9838219 = 14757329) B14757329
theorem B1728175 : Blo 1727064 1728175 := bstep (se 1 (by rfl) ⟨1296131, by rfl⟩ : syracuseStep 1728175 = 2592263) B2592263
theorem B5832377 : Blo 1727064 5832377 := bstep (se 2 (by rfl) ⟨2187141, by rfl⟩ : syracuseStep 5832377 = 4374283) B4374283
theorem B1728199 : Blo 1727064 1728199 := bstep (se 1 (by rfl) ⟨1296149, by rfl⟩ : syracuseStep 1728199 = 2592299) B2592299
theorem B8871623 : Blo 1727064 8871623 := bstep (se 1 (by rfl) ⟨6653717, by rfl⟩ : syracuseStep 8871623 = 13307435) B13307435
theorem B4669139 : Blo 1727064 4669139 := bstep (se 1 (by rfl) ⟨3501854, by rfl⟩ : syracuseStep 4669139 = 7003709) B7003709
theorem B1728219 : Blo 1727064 1728219 := bstep (se 1 (by rfl) ⟨1296164, by rfl⟩ : syracuseStep 1728219 = 2592329) B2592329
theorem B1728295 : Blo 1727064 1728295 := bstep (se 1 (by rfl) ⟨1296221, by rfl⟩ : syracuseStep 1728295 = 2592443) B2592443
theorem B13115195 : Blo 1727064 13115195 := bstep (se 1 (by rfl) ⟨9836396, by rfl⟩ : syracuseStep 13115195 = 19672793) B19672793
theorem B1728335 : Blo 1727064 1728335 := bstep (se 1 (by rfl) ⟨1296251, by rfl⟩ : syracuseStep 1728335 = 2592503) B2592503
theorem B1728351 : Blo 1727064 1728351 := bstep (se 1 (by rfl) ⟨1296263, by rfl⟩ : syracuseStep 1728351 = 2592527) B2592527
theorem B1728379 : Blo 1727064 1728379 := bstep (se 1 (by rfl) ⟨1296284, by rfl⟩ : syracuseStep 1728379 = 2592569) B2592569
theorem B1728431 : Blo 1727064 1728431 := bstep (se 1 (by rfl) ⟨1296323, by rfl⟩ : syracuseStep 1728431 = 2592647) B2592647
theorem B2916283 : Blo 1727064 2916283 := bstep (se 1 (by rfl) ⟨2187212, by rfl⟩ : syracuseStep 2916283 = 4374425) B4374425
theorem B1728455 : Blo 1727064 1728455 := bstep (se 1 (by rfl) ⟨1296341, by rfl⟩ : syracuseStep 1728455 = 2592683) B2592683
theorem B1728475 : Blo 1727064 1728475 := bstep (se 1 (by rfl) ⟨1296356, by rfl⟩ : syracuseStep 1728475 = 2592713) B2592713
theorem B5832809 : Blo 1727064 5832809 := bstep (se 2 (by rfl) ⟨2187303, by rfl⟩ : syracuseStep 5832809 = 4374607) B4374607
theorem B121331843 : Blo 1727064 121331843 := bstep (se 1 (by rfl) ⟨90998882, by rfl⟩ : syracuseStep 121331843 = 181997765) B181997765
theorem B9838745 : Blo 1727064 9838745 := bstep (se 2 (by rfl) ⟨3689529, by rfl⟩ : syracuseStep 9838745 = 7379059) B7379059
theorem B94609619 : Blo 1727064 94609619 := bstep (se 1 (by rfl) ⟨70957214, by rfl⟩ : syracuseStep 94609619 = 141914429) B141914429
theorem B1728799 : Blo 1727064 1728799 := bstep (se 1 (by rfl) ⟨1296599, by rfl⟩ : syracuseStep 1728799 = 2593199) B2593199
theorem B1728859 : Blo 1727064 1728859 := bstep (se 1 (by rfl) ⟨1296644, by rfl⟩ : syracuseStep 1728859 = 2593289) B2593289
theorem B1728879 : Blo 1727064 1728879 := bstep (se 1 (by rfl) ⟨1296659, by rfl⟩ : syracuseStep 1728879 = 2593319) B2593319
theorem B2187643 : Blo 1727064 2187643 := bstep (se 1 (by rfl) ⟨1640732, by rfl⟩ : syracuseStep 2187643 = 3281465) B3281465
theorem B2769319 : Blo 1727064 2769319 := bstep (se 1 (by rfl) ⟨2076989, by rfl⟩ : syracuseStep 2769319 = 4153979) B4153979
theorem B1728935 : Blo 1727064 1728935 := bstep (se 1 (by rfl) ⟨1296701, by rfl⟩ : syracuseStep 1728935 = 2593403) B2593403
theorem B9847241 : Blo 1727064 9847241 := bstep (se 2 (by rfl) ⟨3692715, by rfl⟩ : syracuseStep 9847241 = 7385431) B7385431
theorem B2769403 : Blo 1727064 2769403 := bstep (se 1 (by rfl) ⟨2077052, by rfl⟩ : syracuseStep 2769403 = 4154105) B4154105
theorem B1729019 : Blo 1727064 1729019 := bstep (se 1 (by rfl) ⟨1296764, by rfl⟩ : syracuseStep 1729019 = 2593529) B2593529
theorem B287719937 : Blo 1727064 287719937 := bstep (se 2 (by rfl) ⟨107894976, by rfl⟩ : syracuseStep 287719937 = 215789953) B215789953
theorem B8749619 : Blo 1727064 8749619 := bstep (se 1 (by rfl) ⟨6562214, by rfl⟩ : syracuseStep 8749619 = 13124429) B13124429
theorem B2916985 : Blo 1727064 2916985 := bstep (se 2 (by rfl) ⟨1093869, by rfl⟩ : syracuseStep 2916985 = 2187739) B2187739
theorem B2917039 : Blo 1727064 2917039 := bstep (se 1 (by rfl) ⟨2187779, by rfl⟩ : syracuseStep 2917039 = 4375559) B4375559
theorem B16614071 : Blo 1727064 16614071 := bstep (se 1 (by rfl) ⟨12460553, by rfl⟩ : syracuseStep 16614071 = 24921107) B24921107
theorem B4670351 : Blo 1727064 4670351 := bstep (se 1 (by rfl) ⟨3502763, by rfl⟩ : syracuseStep 4670351 = 7005527) B7005527
theorem B23659411 : Blo 1727064 23659411 := bstep (se 1 (by rfl) ⟨17744558, by rfl⟩ : syracuseStep 23659411 = 35489117) B35489117
theorem B4154267 : Blo 1727064 4154267 := bstep (se 1 (by rfl) ⟨3115700, by rfl⟩ : syracuseStep 4154267 = 6231401) B6231401
theorem B5833673 : Blo 1727064 5833673 := bstep (se 2 (by rfl) ⟨2187627, by rfl⟩ : syracuseStep 5833673 = 4375255) B4375255
theorem B4375691 : Blo 1727064 4375691 := bstep (se 1 (by rfl) ⟨3281768, by rfl⟩ : syracuseStep 4375691 = 6563537) B6563537
theorem B5833943 : Blo 1727064 5833943 := bstep (se 1 (by rfl) ⟨4375457, by rfl⟩ : syracuseStep 5833943 = 8750915) B8750915
theorem B5539049 : Blo 1727064 5539049 := bstep (se 2 (by rfl) ⟨2077143, by rfl⟩ : syracuseStep 5539049 = 4154287) B4154287
theorem B6563065 : Blo 1727064 6563065 := bstep (se 2 (by rfl) ⟨2461149, by rfl⟩ : syracuseStep 6563065 = 4922299) B4922299
theorem B13124915 : Blo 1727064 13124915 := bstep (se 1 (by rfl) ⟨9843686, by rfl⟩ : syracuseStep 13124915 = 19687373) B19687373
theorem B4375903 : Blo 1727064 4375903 := bstep (se 1 (by rfl) ⟨3281927, by rfl⟩ : syracuseStep 4375903 = 6563855) B6563855
theorem B33219983 : Blo 1727064 33219983 := bstep (se 1 (by rfl) ⟨24914987, by rfl⟩ : syracuseStep 33219983 = 49829975) B49829975
theorem B1942951 : Blo 1727064 1942951 := bstep (se 1 (by rfl) ⟨1457213, by rfl⟩ : syracuseStep 1942951 = 2914427) B2914427
theorem B1844731 : Blo 1727064 1844731 := bstep (se 1 (by rfl) ⟨1383548, by rfl⟩ : syracuseStep 1844731 = 2767097) B2767097
theorem B10651169 : Blo 1727064 10651169 := bstep (se 2 (by rfl) ⟨3994188, by rfl⟩ : syracuseStep 10651169 = 7988377) B7988377
theorem B1943527 : Blo 1727064 1943527 := bstep (se 1 (by rfl) ⟨1457645, by rfl⟩ : syracuseStep 1943527 = 2915291) B2915291
theorem B17967185 : Blo 1727064 17967185 := bstep (se 2 (by rfl) ⟨6737694, by rfl⟩ : syracuseStep 17967185 = 13475389) B13475389
theorem B8751239 : Blo 1727064 8751239 := bstep (se 1 (by rfl) ⟨6563429, by rfl⟩ : syracuseStep 8751239 = 13126859) B13126859
theorem B13117625 : Blo 1727064 13117625 := bstep (se 2 (by rfl) ⟨4919109, by rfl⟩ : syracuseStep 13117625 = 9838219) B9838219
theorem B8866039 : Blo 1727064 8866039 := bstep (se 1 (by rfl) ⟨6649529, by rfl⟩ : syracuseStep 8866039 = 13299059) B13299059
theorem B2590985 : Blo 1727064 2590985 := bstep (se 2 (by rfl) ⟨971619, by rfl⟩ : syracuseStep 2590985 = 1943239) B1943239
theorem B2591087 : Blo 1727064 2591087 := bstep (se 1 (by rfl) ⟨1943315, by rfl⟩ : syracuseStep 2591087 = 3886631) B3886631
theorem B3688915 : Blo 1727064 3688915 := bstep (se 1 (by rfl) ⟨2766686, by rfl⟩ : syracuseStep 3688915 = 5533373) B5533373
theorem B9980371 : Blo 1727064 9980371 := bstep (se 1 (by rfl) ⟨7485278, by rfl⟩ : syracuseStep 9980371 = 14970557) B14970557
theorem B8743463 : Blo 1727064 8743463 := bstep (se 1 (by rfl) ⟨6557597, by rfl⟩ : syracuseStep 8743463 = 13115195) B13115195
theorem B2591303 : Blo 1727064 2591303 := bstep (se 1 (by rfl) ⟨1943477, by rfl⟩ : syracuseStep 2591303 = 3886955) B3886955
theorem B3279467 : Blo 1727064 3279467 := bstep (se 1 (by rfl) ⟨2459600, by rfl⟩ : syracuseStep 3279467 = 4919201) B4919201
theorem B2591339 : Blo 1727064 2591339 := bstep (se 1 (by rfl) ⟨1943504, by rfl⟩ : syracuseStep 2591339 = 3887009) B3887009
theorem B2591567 : Blo 1727064 2591567 := bstep (se 1 (by rfl) ⟨1943675, by rfl⟩ : syracuseStep 2591567 = 3887351) B3887351
theorem B26594173 : Blo 1727064 26594173 := bstep (se 3 (by rfl) ⟨4986407, by rfl⟩ : syracuseStep 26594173 = 9972815) B9972815
theorem B3689435 : Blo 1727064 3689435 := bstep (se 1 (by rfl) ⟨2767076, by rfl⟩ : syracuseStep 3689435 = 5534153) B5534153
theorem B3886055 : Blo 1727064 3886055 := bstep (se 1 (by rfl) ⟨2914541, by rfl⟩ : syracuseStep 3886055 = 5829083) B5829083
theorem B3279847 : Blo 1727064 3279847 := bstep (se 1 (by rfl) ⟨2459885, by rfl⟩ : syracuseStep 3279847 = 4919771) B4919771
theorem B68275379 : Blo 1727064 68275379 := bstep (se 1 (by rfl) ⟨51206534, by rfl⟩ : syracuseStep 68275379 = 102413069) B102413069
theorem B2591963 : Blo 1727064 2591963 := bstep (se 1 (by rfl) ⟨1943972, by rfl⟩ : syracuseStep 2591963 = 3887945) B3887945
theorem B29945051 : Blo 1727064 29945051 := bstep (se 1 (by rfl) ⟨22458788, by rfl⟩ : syracuseStep 29945051 = 44917577) B44917577
theorem B3280105 : Blo 1727064 3280105 := bstep (se 2 (by rfl) ⟨1230039, by rfl⟩ : syracuseStep 3280105 = 2460079) B2460079
theorem B14765327 : Blo 1727064 14765327 := bstep (se 1 (by rfl) ⟨11073995, by rfl⟩ : syracuseStep 14765327 = 22147991) B22147991
theorem B7990595 : Blo 1727064 7990595 := bstep (se 1 (by rfl) ⟨5992946, by rfl⟩ : syracuseStep 7990595 = 11985893) B11985893
theorem B3886433 : Blo 1727064 3886433 := bstep (se 2 (by rfl) ⟨1457412, by rfl⟩ : syracuseStep 3886433 = 2914825) B2914825
theorem B2592137 : Blo 1727064 2592137 := bstep (se 2 (by rfl) ⟨972051, by rfl⟩ : syracuseStep 2592137 = 1944103) B1944103
theorem B3886523 : Blo 1727064 3886523 := bstep (se 1 (by rfl) ⟨2914892, by rfl⟩ : syracuseStep 3886523 = 5829785) B5829785
theorem B15756743 : Blo 1727064 15756743 := bstep (se 1 (by rfl) ⟨11817557, by rfl⟩ : syracuseStep 15756743 = 23635115) B23635115
theorem B8867353 : Blo 1727064 8867353 := bstep (se 2 (by rfl) ⟨3325257, by rfl⟩ : syracuseStep 8867353 = 6650515) B6650515
theorem B3886649 : Blo 1727064 3886649 := bstep (se 2 (by rfl) ⟨1457493, by rfl⟩ : syracuseStep 3886649 = 2914987) B2914987
theorem B1945183 : Blo 1727064 1945183 := bstep (se 1 (by rfl) ⟨1458887, by rfl⟩ : syracuseStep 1945183 = 2917775) B2917775
theorem B29511377 : Blo 1727064 29511377 := bstep (se 2 (by rfl) ⟨11066766, by rfl⟩ : syracuseStep 29511377 = 22133533) B22133533
theorem B9842411 : Blo 1727064 9842411 := bstep (se 1 (by rfl) ⟨7381808, by rfl⟩ : syracuseStep 9842411 = 14763617) B14763617
theorem B2592491 : Blo 1727064 2592491 := bstep (se 1 (by rfl) ⟨1944368, by rfl⟩ : syracuseStep 2592491 = 3888737) B3888737
theorem B5533487 : Blo 1727064 5533487 := bstep (se 1 (by rfl) ⟨4150115, by rfl⟩ : syracuseStep 5533487 = 8300231) B8300231
theorem B2592719 : Blo 1727064 2592719 := bstep (se 1 (by rfl) ⟨1944539, by rfl⟩ : syracuseStep 2592719 = 3889079) B3889079
theorem B7385089 : Blo 1727064 7385089 := bstep (se 2 (by rfl) ⟨2769408, by rfl⟩ : syracuseStep 7385089 = 5538817) B5538817
theorem B6557705 : Blo 1727064 6557705 := bstep (se 2 (by rfl) ⟨2459139, by rfl⟩ : syracuseStep 6557705 = 4918279) B4918279
theorem B3887315 : Blo 1727064 3887315 := bstep (se 1 (by rfl) ⟨2915486, by rfl⟩ : syracuseStep 3887315 = 5830973) B5830973
theorem B3887369 : Blo 1727064 3887369 := bstep (se 2 (by rfl) ⟨1457763, by rfl⟩ : syracuseStep 3887369 = 2915527) B2915527
theorem B3281161 : Blo 1727064 3281161 := bstep (se 2 (by rfl) ⟨1230435, by rfl⟩ : syracuseStep 3281161 = 2460871) B2460871
theorem B2593115 : Blo 1727064 2593115 := bstep (se 1 (by rfl) ⟨1944836, by rfl⟩ : syracuseStep 2593115 = 3889673) B3889673
theorem B9843119 : Blo 1727064 9843119 := bstep (se 1 (by rfl) ⟨7382339, by rfl⟩ : syracuseStep 9843119 = 14764679) B14764679
theorem B3887585 : Blo 1727064 3887585 := bstep (se 2 (by rfl) ⟨1457844, by rfl⟩ : syracuseStep 3887585 = 2915689) B2915689
theorem B18674225 : Blo 1727064 18674225 := bstep (se 2 (by rfl) ⟨7002834, by rfl⟩ : syracuseStep 18674225 = 14005669) B14005669
theorem B2593343 : Blo 1727064 2593343 := bstep (se 1 (by rfl) ⟨1945007, by rfl⟩ : syracuseStep 2593343 = 3890015) B3890015
theorem B5829191 : Blo 1727064 5829191 := bstep (se 1 (by rfl) ⟨4371893, by rfl⟩ : syracuseStep 5829191 = 8743787) B8743787
theorem B2495047 : Blo 1727064 2495047 := bstep (se 1 (by rfl) ⟨1871285, by rfl⟩ : syracuseStep 2495047 = 3742571) B3742571
theorem B8745569 : Blo 1727064 8745569 := bstep (se 2 (by rfl) ⟨3279588, by rfl⟩ : syracuseStep 8745569 = 6559177) B6559177
theorem B2593463 : Blo 1727064 2593463 := bstep (se 1 (by rfl) ⟨1945097, by rfl⟩ : syracuseStep 2593463 = 3890195) B3890195
theorem B3887891 : Blo 1727064 3887891 := bstep (se 1 (by rfl) ⟨2915918, by rfl⟩ : syracuseStep 3887891 = 5831837) B5831837
theorem B7377743 : Blo 1727064 7377743 := bstep (se 1 (by rfl) ⟨5533307, by rfl⟩ : syracuseStep 7377743 = 11066615) B11066615
theorem B5829623 : Blo 1727064 5829623 := bstep (se 1 (by rfl) ⟨4372217, by rfl⟩ : syracuseStep 5829623 = 8744435) B8744435
theorem B14758969 : Blo 1727064 14758969 := bstep (se 2 (by rfl) ⟨5534613, by rfl⟩ : syracuseStep 14758969 = 11069227) B11069227
theorem B3888251 : Blo 1727064 3888251 := bstep (se 1 (by rfl) ⟨2916188, by rfl⟩ : syracuseStep 3888251 = 5832377) B5832377
theorem B9843869 : Blo 1727064 9843869 := bstep (se 3 (by rfl) ⟨1845725, by rfl⟩ : syracuseStep 9843869 = 3691451) B3691451
theorem B4371671 : Blo 1727064 4371671 := bstep (se 1 (by rfl) ⟨3278753, by rfl⟩ : syracuseStep 4371671 = 6557507) B6557507
theorem B8746217 : Blo 1727064 8746217 := bstep (se 2 (by rfl) ⟨3279831, by rfl⟩ : syracuseStep 8746217 = 6559663) B6559663
theorem B3888377 : Blo 1727064 3888377 := bstep (se 2 (by rfl) ⟨1458141, by rfl⟩ : syracuseStep 3888377 = 2916283) B2916283
theorem B3888521 : Blo 1727064 3888521 := bstep (se 2 (by rfl) ⟨1458195, by rfl⟩ : syracuseStep 3888521 = 2916391) B2916391
theorem B8746379 : Blo 1727064 8746379 := bstep (se 1 (by rfl) ⟨6559784, by rfl⟩ : syracuseStep 8746379 = 13119569) B13119569
theorem B119707085 : Blo 1727064 119707085 := bstep (se 3 (by rfl) ⟨22445078, by rfl⟩ : syracuseStep 119707085 = 44890157) B44890157
theorem B3888647 : Blo 1727064 3888647 := bstep (se 1 (by rfl) ⟨2916485, by rfl⟩ : syracuseStep 3888647 = 5832971) B5832971
theorem B194279053 : Blo 1727064 194279053 := bstep (se 3 (by rfl) ⟨36427322, by rfl⟩ : syracuseStep 194279053 = 72854645) B72854645
theorem B3888827 : Blo 1727064 3888827 := bstep (se 1 (by rfl) ⟨2916620, by rfl⟩ : syracuseStep 3888827 = 5833241) B5833241
theorem B106362679 : Blo 1727064 106362679 := bstep (se 1 (by rfl) ⟨79772009, by rfl⟩ : syracuseStep 106362679 = 159544019) B159544019
theorem B3888953 : Blo 1727064 3888953 := bstep (se 2 (by rfl) ⟨1458357, by rfl⟩ : syracuseStep 3888953 = 2916715) B2916715
theorem B5830487 : Blo 1727064 5830487 := bstep (se 1 (by rfl) ⟨4372865, by rfl⟩ : syracuseStep 5830487 = 8745731) B8745731
theorem B14767991 : Blo 1727064 14767991 := bstep (se 1 (by rfl) ⟨11075993, by rfl⟩ : syracuseStep 14767991 = 22151987) B22151987
theorem B31528885 : Blo 1727064 31528885 := bstep (se 5 (by rfl) ⟨1477916, by rfl⟩ : syracuseStep 31528885 = 2955833) B2955833
theorem B3889583 : Blo 1727064 3889583 := bstep (se 1 (by rfl) ⟨2917187, by rfl⟩ : syracuseStep 3889583 = 5834375) B5834375
theorem B7379383 : Blo 1727064 7379383 := bstep (se 1 (by rfl) ⟨5534537, by rfl⟩ : syracuseStep 7379383 = 11069075) B11069075
theorem B3889619 : Blo 1727064 3889619 := bstep (se 1 (by rfl) ⟨2917214, by rfl⟩ : syracuseStep 3889619 = 5834429) B5834429
theorem B4372987 : Blo 1727064 4372987 := bstep (se 1 (by rfl) ⟨3279740, by rfl⟩ : syracuseStep 4372987 = 6559481) B6559481
theorem B24910375 : Blo 1727064 24910375 := bstep (se 1 (by rfl) ⟨18682781, by rfl⟩ : syracuseStep 24910375 = 37365563) B37365563
theorem B2914879 : Blo 1727064 2914879 := bstep (se 1 (by rfl) ⟨2186159, by rfl⟩ : syracuseStep 2914879 = 4372319) B4372319
theorem B3889727 : Blo 1727064 3889727 := bstep (se 1 (by rfl) ⟨2917295, by rfl⟩ : syracuseStep 3889727 = 5834591) B5834591
theorem B4373099 : Blo 1727064 4373099 := bstep (se 1 (by rfl) ⟨3279824, by rfl⟩ : syracuseStep 4373099 = 6559649) B6559649
theorem B3889835 : Blo 1727064 3889835 := bstep (se 1 (by rfl) ⟨2917376, by rfl⟩ : syracuseStep 3889835 = 5834753) B5834753
theorem B1727199 : Blo 1727064 1727199 := bstep (se 1 (by rfl) ⟨1295399, by rfl⟩ : syracuseStep 1727199 = 2590799) B2590799
theorem B1727279 : Blo 1727064 1727279 := bstep (se 1 (by rfl) ⟨1295459, by rfl⟩ : syracuseStep 1727279 = 2590919) B2590919
theorem B21019499 : Blo 1727064 21019499 := bstep (se 1 (by rfl) ⟨15764624, by rfl⟩ : syracuseStep 21019499 = 31529249) B31529249
theorem B5831567 : Blo 1727064 5831567 := bstep (se 1 (by rfl) ⟨4373675, by rfl⟩ : syracuseStep 5831567 = 8747351) B8747351
theorem B1727387 : Blo 1727064 1727387 := bstep (se 1 (by rfl) ⟨1295540, by rfl⟩ : syracuseStep 1727387 = 2591081) B2591081
theorem B18684857 : Blo 1727064 18684857 := bstep (se 2 (by rfl) ⟨7006821, by rfl⟩ : syracuseStep 18684857 = 14013643) B14013643
theorem B1727439 : Blo 1727064 1727439 := bstep (se 1 (by rfl) ⟨1295579, by rfl⟩ : syracuseStep 1727439 = 2591159) B2591159
theorem B1727463 : Blo 1727064 1727463 := bstep (se 1 (by rfl) ⟨1295597, by rfl⟩ : syracuseStep 1727463 = 2591195) B2591195
theorem B3890375 : Blo 1727064 3890375 := bstep (se 1 (by rfl) ⟨2917781, by rfl⟩ : syracuseStep 3890375 = 5835563) B5835563
theorem B8871133 : Blo 1727064 8871133 := bstep (se 3 (by rfl) ⟨1663337, by rfl⟩ : syracuseStep 8871133 = 3326675) B3326675
theorem B2915561 : Blo 1727064 2915561 := bstep (se 2 (by rfl) ⟨1093335, by rfl⟩ : syracuseStep 2915561 = 2186671) B2186671
theorem B4373747 : Blo 1727064 4373747 := bstep (se 1 (by rfl) ⟨3280310, by rfl⟩ : syracuseStep 4373747 = 6560621) B6560621
theorem B2915615 : Blo 1727064 2915615 := bstep (se 1 (by rfl) ⟨2186711, by rfl⟩ : syracuseStep 2915615 = 4373423) B4373423
theorem B1727775 : Blo 1727064 1727775 := bstep (se 1 (by rfl) ⟨1295831, by rfl⟩ : syracuseStep 1727775 = 2591663) B2591663
theorem B1727835 : Blo 1727064 1727835 := bstep (se 1 (by rfl) ⟨1295876, by rfl⟩ : syracuseStep 1727835 = 2591753) B2591753
theorem B6561121 : Blo 1727064 6561121 := bstep (se 2 (by rfl) ⟨2460420, by rfl⟩ : syracuseStep 6561121 = 4920841) B4920841
theorem B1727855 : Blo 1727064 1727855 := bstep (se 1 (by rfl) ⟨1295891, by rfl⟩ : syracuseStep 1727855 = 2591783) B2591783
theorem B1727911 : Blo 1727064 1727911 := bstep (se 1 (by rfl) ⟨1295933, by rfl⟩ : syracuseStep 1727911 = 2591867) B2591867
theorem B4373959 : Blo 1727064 4373959 := bstep (se 1 (by rfl) ⟨3280469, by rfl⟩ : syracuseStep 4373959 = 6560939) B6560939
theorem B2768327 : Blo 1727064 2768327 := bstep (se 1 (by rfl) ⟨2076245, by rfl⟩ : syracuseStep 2768327 = 4152491) B4152491
theorem B1727995 : Blo 1727064 1727995 := bstep (se 1 (by rfl) ⟨1295996, by rfl⟩ : syracuseStep 1727995 = 2591993) B2591993
theorem B12459545 : Blo 1727064 12459545 := bstep (se 2 (by rfl) ⟨4672329, by rfl⟩ : syracuseStep 12459545 = 9344659) B9344659
theorem B1728063 : Blo 1727064 1728063 := bstep (se 1 (by rfl) ⟨1296047, by rfl⟩ : syracuseStep 1728063 = 2592095) B2592095
theorem B1728071 : Blo 1727064 1728071 := bstep (se 1 (by rfl) ⟨1296053, by rfl⟩ : syracuseStep 1728071 = 2592107) B2592107
theorem B56835665 : Blo 1727064 56835665 := bstep (se 2 (by rfl) ⟨21313374, by rfl⟩ : syracuseStep 56835665 = 42626749) B42626749
theorem B8101471 : Blo 1727064 8101471 := bstep (se 1 (by rfl) ⟨6076103, by rfl⟩ : syracuseStep 8101471 = 12152207) B12152207
theorem B6561395 : Blo 1727064 6561395 := bstep (se 1 (by rfl) ⟨4921046, by rfl⟩ : syracuseStep 6561395 = 9842093) B9842093
theorem B1728223 : Blo 1727064 1728223 := bstep (se 1 (by rfl) ⟨1296167, by rfl⟩ : syracuseStep 1728223 = 2592335) B2592335
theorem B7380715 : Blo 1727064 7380715 := bstep (se 1 (by rfl) ⟨5535536, by rfl⟩ : syracuseStep 7380715 = 11071073) B11071073
theorem B4923143 : Blo 1727064 4923143 := bstep (se 1 (by rfl) ⟨3692357, by rfl⟩ : syracuseStep 4923143 = 7384715) B7384715
theorem B1728303 : Blo 1727064 1728303 := bstep (se 1 (by rfl) ⟨1296227, by rfl⟩ : syracuseStep 1728303 = 2592455) B2592455
theorem B5914415 : Blo 1727064 5914415 := bstep (se 1 (by rfl) ⟨4435811, by rfl⟩ : syracuseStep 5914415 = 8871623) B8871623
theorem B3112759 : Blo 1727064 3112759 := bstep (se 1 (by rfl) ⟨2334569, by rfl⟩ : syracuseStep 3112759 = 4669139) B4669139
theorem B6561593 : Blo 1727064 6561593 := bstep (se 2 (by rfl) ⟨2460597, by rfl⟩ : syracuseStep 6561593 = 4921195) B4921195
theorem B13123457 : Blo 1727064 13123457 := bstep (se 2 (by rfl) ⟨4921296, by rfl⟩ : syracuseStep 13123457 = 9842593) B9842593
theorem B1728411 : Blo 1727064 1728411 := bstep (se 1 (by rfl) ⟨1296308, by rfl⟩ : syracuseStep 1728411 = 2592617) B2592617
theorem B1728463 : Blo 1727064 1728463 := bstep (se 1 (by rfl) ⟨1296347, by rfl⟩ : syracuseStep 1728463 = 2592695) B2592695
theorem B1728487 : Blo 1727064 1728487 := bstep (se 1 (by rfl) ⟨1296365, by rfl⟩ : syracuseStep 1728487 = 2592731) B2592731
theorem B9846785 : Blo 1727064 9846785 := bstep (se 2 (by rfl) ⟨3692544, by rfl⟩ : syracuseStep 9846785 = 7385089) B7385089
theorem B80887895 : Blo 1727064 80887895 := bstep (se 1 (by rfl) ⟨60665921, by rfl⟩ : syracuseStep 80887895 = 121331843) B121331843
theorem B1728743 : Blo 1727064 1728743 := bstep (se 1 (by rfl) ⟨1296557, by rfl⟩ : syracuseStep 1728743 = 2593115) B2593115
theorem B6562079 : Blo 1727064 6562079 := bstep (se 1 (by rfl) ⟨4921559, by rfl⟩ : syracuseStep 6562079 = 9843119) B9843119
theorem B11821385 : Blo 1727064 11821385 := bstep (se 2 (by rfl) ⟨4433019, by rfl⟩ : syracuseStep 11821385 = 8866039) B8866039
theorem B4374881 : Blo 1727064 4374881 := bstep (se 2 (by rfl) ⟨1640580, by rfl⟩ : syracuseStep 4374881 = 3281161) B3281161
theorem B5833079 : Blo 1727064 5833079 := bstep (se 1 (by rfl) ⟨4374809, by rfl⟩ : syracuseStep 5833079 = 8749619) B8749619
theorem B1728895 : Blo 1727064 1728895 := bstep (se 1 (by rfl) ⟨1296671, by rfl⟩ : syracuseStep 1728895 = 2593343) B2593343
theorem B11076047 : Blo 1727064 11076047 := bstep (se 1 (by rfl) ⟨8307035, by rfl⟩ : syracuseStep 11076047 = 16614071) B16614071
theorem B1728975 : Blo 1727064 1728975 := bstep (se 1 (by rfl) ⟨1296731, by rfl⟩ : syracuseStep 1728975 = 2593463) B2593463
theorem B2916857 : Blo 1727064 2916857 := bstep (se 2 (by rfl) ⟨1093821, by rfl⟩ : syracuseStep 2916857 = 2187643) B2187643
theorem B9839177 : Blo 1727064 9839177 := bstep (se 2 (by rfl) ⟨3689691, by rfl⟩ : syracuseStep 9839177 = 7379383) B7379383
theorem B3113567 : Blo 1727064 3113567 := bstep (se 1 (by rfl) ⟨2335175, by rfl⟩ : syracuseStep 3113567 = 4670351) B4670351
theorem B2917127 : Blo 1727064 2917127 := bstep (se 1 (by rfl) ⟨2187845, by rfl⟩ : syracuseStep 2917127 = 4375691) B4375691
theorem B3326729 : Blo 1727064 3326729 := bstep (se 2 (by rfl) ⟨1247523, by rfl⟩ : syracuseStep 3326729 = 2495047) B2495047
theorem B6562579 : Blo 1727064 6562579 := bstep (se 1 (by rfl) ⟨4921934, by rfl⟩ : syracuseStep 6562579 = 9843869) B9843869
theorem B8749943 : Blo 1727064 8749943 := bstep (se 1 (by rfl) ⟨6562457, by rfl⟩ : syracuseStep 8749943 = 13124915) B13124915
theorem B11978123 : Blo 1727064 11978123 := bstep (se 1 (by rfl) ⟨8983592, by rfl⟩ : syracuseStep 11978123 = 17967185) B17967185
theorem B19678625 : Blo 1727064 19678625 := bstep (se 2 (by rfl) ⟨7379484, by rfl⟩ : syracuseStep 19678625 = 14758969) B14758969
theorem B5834159 : Blo 1727064 5834159 := bstep (se 1 (by rfl) ⟨4375619, by rfl⟩ : syracuseStep 5834159 = 8751239) B8751239
theorem B8750753 : Blo 1727064 8750753 := bstep (se 2 (by rfl) ⟨3281532, by rfl⟩ : syracuseStep 8750753 = 6563065) B6563065
theorem B5834537 : Blo 1727064 5834537 := bstep (se 2 (by rfl) ⟨2187951, by rfl⟩ : syracuseStep 5834537 = 4375903) B4375903
theorem B2590601 : Blo 1727064 2590601 := bstep (se 2 (by rfl) ⟨971475, by rfl⟩ : syracuseStep 2590601 = 1942951) B1942951
theorem B2590703 : Blo 1727064 2590703 := bstep (se 1 (by rfl) ⟨1943027, by rfl⟩ : syracuseStep 2590703 = 3886055) B3886055
theorem B2459641 : Blo 1727064 2459641 := bstep (se 2 (by rfl) ⟨922365, by rfl⟩ : syracuseStep 2459641 = 1844731) B1844731
theorem B11823137 : Blo 1727064 11823137 := bstep (se 2 (by rfl) ⟨4433676, by rfl⟩ : syracuseStep 11823137 = 8867353) B8867353
theorem B45516919 : Blo 1727064 45516919 := bstep (se 1 (by rfl) ⟨34137689, by rfl⟩ : syracuseStep 45516919 = 68275379) B68275379
theorem B15771773 : Blo 1727064 15771773 := bstep (se 3 (by rfl) ⟨2957207, by rfl⟩ : syracuseStep 15771773 = 5914415) B5914415
theorem B1943707 : Blo 1727064 1943707 := bstep (se 1 (by rfl) ⟨1457780, by rfl⟩ : syracuseStep 1943707 = 2915561) B2915561
theorem B1943743 : Blo 1727064 1943743 := bstep (se 1 (by rfl) ⟨1457807, by rfl⟩ : syracuseStep 1943743 = 2915615) B2915615
theorem B5327063 : Blo 1727064 5327063 := bstep (se 1 (by rfl) ⟨3995297, by rfl⟩ : syracuseStep 5327063 = 7990595) B7990595
theorem B2590955 : Blo 1727064 2590955 := bstep (se 1 (by rfl) ⟨1943216, by rfl⟩ : syracuseStep 2590955 = 3886433) B3886433
theorem B2591015 : Blo 1727064 2591015 := bstep (se 1 (by rfl) ⟨1943261, by rfl⟩ : syracuseStep 2591015 = 3886523) B3886523
theorem B10504495 : Blo 1727064 10504495 := bstep (se 1 (by rfl) ⟨7878371, by rfl⟩ : syracuseStep 10504495 = 15756743) B15756743
theorem B1845551 : Blo 1727064 1845551 := bstep (se 1 (by rfl) ⟨1384163, by rfl⟩ : syracuseStep 1845551 = 2768327) B2768327
theorem B9840953 : Blo 1727064 9840953 := bstep (se 2 (by rfl) ⟨3690357, by rfl⟩ : syracuseStep 9840953 = 7380715) B7380715
theorem B2591099 : Blo 1727064 2591099 := bstep (se 1 (by rfl) ⟨1943324, by rfl⟩ : syracuseStep 2591099 = 3886649) B3886649
theorem B37890443 : Blo 1727064 37890443 := bstep (se 1 (by rfl) ⟨28417832, by rfl⟩ : syracuseStep 37890443 = 56835665) B56835665
theorem B11078045 : Blo 1727064 11078045 := bstep (se 3 (by rfl) ⟨2077133, by rfl⟩ : syracuseStep 11078045 = 4154267) B4154267
theorem B49826285 : Blo 1727064 49826285 := bstep (se 3 (by rfl) ⟨9342428, by rfl⟩ : syracuseStep 49826285 = 18684857) B18684857
theorem B3688991 : Blo 1727064 3688991 := bstep (se 1 (by rfl) ⟨2766743, by rfl⟩ : syracuseStep 3688991 = 5533487) B5533487
theorem B2591369 : Blo 1727064 2591369 := bstep (se 2 (by rfl) ⟨971763, by rfl⟩ : syracuseStep 2591369 = 1943527) B1943527
theorem B2591543 : Blo 1727064 2591543 := bstep (se 1 (by rfl) ⟨1943657, by rfl⟩ : syracuseStep 2591543 = 3887315) B3887315
theorem B63073079 : Blo 1727064 63073079 := bstep (se 1 (by rfl) ⟨47304809, by rfl⟩ : syracuseStep 63073079 = 94609619) B94609619
theorem B2591579 : Blo 1727064 2591579 := bstep (se 1 (by rfl) ⟨1943684, by rfl⟩ : syracuseStep 2591579 = 3887369) B3887369
theorem B6564827 : Blo 1727064 6564827 := bstep (se 1 (by rfl) ⟨4923620, by rfl⟩ : syracuseStep 6564827 = 9847241) B9847241
theorem B2591723 : Blo 1727064 2591723 := bstep (se 1 (by rfl) ⟨1943792, by rfl⟩ : syracuseStep 2591723 = 3887585) B3887585
theorem B3886127 : Blo 1727064 3886127 := bstep (se 1 (by rfl) ⟨2914595, by rfl⟩ : syracuseStep 3886127 = 5829191) B5829191
theorem B2591927 : Blo 1727064 2591927 := bstep (se 1 (by rfl) ⟨1943945, by rfl⟩ : syracuseStep 2591927 = 3887891) B3887891
theorem B4918495 : Blo 1727064 4918495 := bstep (se 1 (by rfl) ⟨3688871, by rfl⟩ : syracuseStep 4918495 = 7377743) B7377743
theorem B4918553 : Blo 1727064 4918553 := bstep (se 2 (by rfl) ⟨1844457, by rfl⟩ : syracuseStep 4918553 = 3688915) B3688915
theorem B13307161 : Blo 1727064 13307161 := bstep (se 2 (by rfl) ⟨4990185, by rfl⟩ : syracuseStep 13307161 = 9980371) B9980371
theorem B3886415 : Blo 1727064 3886415 := bstep (se 1 (by rfl) ⟨2914811, by rfl⟩ : syracuseStep 3886415 = 5829623) B5829623
theorem B33213833 : Blo 1727064 33213833 := bstep (se 2 (by rfl) ⟨12455187, by rfl⟩ : syracuseStep 33213833 = 24910375) B24910375
theorem B2592167 : Blo 1727064 2592167 := bstep (se 1 (by rfl) ⟨1944125, by rfl⟩ : syracuseStep 2592167 = 3888251) B3888251
theorem B3886505 : Blo 1727064 3886505 := bstep (se 2 (by rfl) ⟨1457439, by rfl⟩ : syracuseStep 3886505 = 2914879) B2914879
theorem B2592251 : Blo 1727064 2592251 := bstep (se 1 (by rfl) ⟨1944188, by rfl⟩ : syracuseStep 2592251 = 3888377) B3888377
theorem B2592347 : Blo 1727064 2592347 := bstep (se 1 (by rfl) ⟨1944260, by rfl⟩ : syracuseStep 2592347 = 3888521) B3888521
theorem B22146655 : Blo 1727064 22146655 := bstep (se 1 (by rfl) ⟨16609991, by rfl⟩ : syracuseStep 22146655 = 33219983) B33219983
theorem B2592431 : Blo 1727064 2592431 := bstep (se 1 (by rfl) ⟨1944323, by rfl⟩ : syracuseStep 2592431 = 3888647) B3888647
theorem B2592551 : Blo 1727064 2592551 := bstep (se 1 (by rfl) ⟨1944413, by rfl⟩ : syracuseStep 2592551 = 3888827) B3888827
theorem B35458897 : Blo 1727064 35458897 := bstep (se 2 (by rfl) ⟨13297086, by rfl⟩ : syracuseStep 35458897 = 26594173) B26594173
theorem B2592635 : Blo 1727064 2592635 := bstep (se 1 (by rfl) ⟨1944476, by rfl⟩ : syracuseStep 2592635 = 3888953) B3888953
theorem B3886991 : Blo 1727064 3886991 := bstep (se 1 (by rfl) ⟨2915243, by rfl⟩ : syracuseStep 3886991 = 5830487) B5830487
theorem B8745083 : Blo 1727064 8745083 := bstep (se 1 (by rfl) ⟨6558812, by rfl⟩ : syracuseStep 8745083 = 13117625) B13117625
theorem B8745245 : Blo 1727064 8745245 := bstep (se 3 (by rfl) ⟨1639733, by rfl⟩ : syracuseStep 8745245 = 3279467) B3279467
theorem B2593055 : Blo 1727064 2593055 := bstep (se 1 (by rfl) ⟨1944791, by rfl⟩ : syracuseStep 2593055 = 3889583) B3889583
theorem B16601381 : Blo 1727064 16601381 := bstep (se 4 (by rfl) ⟨1556379, by rfl⟩ : syracuseStep 16601381 = 3112759) B3112759
theorem B2593079 : Blo 1727064 2593079 := bstep (se 1 (by rfl) ⟨1944809, by rfl⟩ : syracuseStep 2593079 = 3889619) B3889619
theorem B5828975 : Blo 1727064 5828975 := bstep (se 1 (by rfl) ⟨4371731, by rfl⟩ : syracuseStep 5828975 = 8743463) B8743463
theorem B2593151 : Blo 1727064 2593151 := bstep (se 1 (by rfl) ⟨1944863, by rfl⟩ : syracuseStep 2593151 = 3889727) B3889727
theorem B2593223 : Blo 1727064 2593223 := bstep (se 1 (by rfl) ⟨1944917, by rfl⟩ : syracuseStep 2593223 = 3889835) B3889835
theorem B14012999 : Blo 1727064 14012999 := bstep (se 1 (by rfl) ⟨10509749, by rfl⟩ : syracuseStep 14012999 = 21019499) B21019499
theorem B3887711 : Blo 1727064 3887711 := bstep (se 1 (by rfl) ⟨2915783, by rfl⟩ : syracuseStep 3887711 = 5831567) B5831567
theorem B10801961 : Blo 1727064 10801961 := bstep (se 2 (by rfl) ⟨4050735, by rfl⟩ : syracuseStep 10801961 = 8101471) B8101471
theorem B2593577 : Blo 1727064 2593577 := bstep (se 2 (by rfl) ⟨972591, by rfl⟩ : syracuseStep 2593577 = 1945183) B1945183
theorem B2593583 : Blo 1727064 2593583 := bstep (se 1 (by rfl) ⟨1945187, by rfl⟩ : syracuseStep 2593583 = 3890375) B3890375
theorem B9843551 : Blo 1727064 9843551 := bstep (se 1 (by rfl) ⟨7382663, by rfl⟩ : syracuseStep 9843551 = 14765327) B14765327
theorem B141816905 : Blo 1727064 141816905 := bstep (se 2 (by rfl) ⟨53181339, by rfl⟩ : syracuseStep 141816905 = 106362679) B106362679
theorem B19674251 : Blo 1727064 19674251 := bstep (se 1 (by rfl) ⟨14755688, by rfl⟩ : syracuseStep 19674251 = 29511377) B29511377
theorem B3282095 : Blo 1727064 3282095 := bstep (se 1 (by rfl) ⟨2461571, by rfl⟩ : syracuseStep 3282095 = 4923143) B4923143
theorem B42038513 : Blo 1727064 42038513 := bstep (se 2 (by rfl) ⟨15764442, by rfl⟩ : syracuseStep 42038513 = 31528885) B31528885
theorem B4371803 : Blo 1727064 4371803 := bstep (se 1 (by rfl) ⟨3278852, by rfl⟩ : syracuseStep 4371803 = 6557705) B6557705
theorem B3888539 : Blo 1727064 3888539 := bstep (se 1 (by rfl) ⟨2916404, by rfl⟩ : syracuseStep 3888539 = 5832809) B5832809
theorem B6559163 : Blo 1727064 6559163 := bstep (se 1 (by rfl) ⟨4919372, by rfl⟩ : syracuseStep 6559163 = 9838745) B9838745
theorem B191813291 : Blo 1727064 191813291 := bstep (se 1 (by rfl) ⟨143859968, by rfl⟩ : syracuseStep 191813291 = 287719937) B287719937
theorem B12449483 : Blo 1727064 12449483 := bstep (se 1 (by rfl) ⟨9337112, by rfl⟩ : syracuseStep 12449483 = 18674225) B18674225
theorem B5830379 : Blo 1727064 5830379 := bstep (se 1 (by rfl) ⟨4372784, by rfl⟩ : syracuseStep 5830379 = 8745569) B8745569
theorem B3889115 : Blo 1727064 3889115 := bstep (se 1 (by rfl) ⟨2916836, by rfl⟩ : syracuseStep 3889115 = 5833673) B5833673
theorem B5830649 : Blo 1727064 5830649 := bstep (se 2 (by rfl) ⟨2186493, by rfl⟩ : syracuseStep 5830649 = 4372987) B4372987
theorem B3692537 : Blo 1727064 3692537 := bstep (se 2 (by rfl) ⟨1384701, by rfl⟩ : syracuseStep 3692537 = 2769403) B2769403
theorem B2914447 : Blo 1727064 2914447 := bstep (se 1 (by rfl) ⟨2185835, by rfl⟩ : syracuseStep 2914447 = 4371671) B4371671
theorem B3889295 : Blo 1727064 3889295 := bstep (se 1 (by rfl) ⟨2916971, by rfl⟩ : syracuseStep 3889295 = 5833943) B5833943
theorem B5830811 : Blo 1727064 5830811 := bstep (se 1 (by rfl) ⟨4373108, by rfl⟩ : syracuseStep 5830811 = 8746217) B8746217
theorem B3692699 : Blo 1727064 3692699 := bstep (se 1 (by rfl) ⟨2769524, by rfl⟩ : syracuseStep 3692699 = 5539049) B5539049
theorem B3889313 : Blo 1727064 3889313 := bstep (se 2 (by rfl) ⟨1458492, by rfl⟩ : syracuseStep 3889313 = 2916985) B2916985
theorem B3889385 : Blo 1727064 3889385 := bstep (se 2 (by rfl) ⟨1458519, by rfl⟩ : syracuseStep 3889385 = 2917039) B2917039
theorem B5830919 : Blo 1727064 5830919 := bstep (se 1 (by rfl) ⟨4373189, by rfl⟩ : syracuseStep 5830919 = 8746379) B8746379
theorem B79804723 : Blo 1727064 79804723 := bstep (se 1 (by rfl) ⟨59853542, by rfl⟩ : syracuseStep 79804723 = 119707085) B119707085
theorem B7100779 : Blo 1727064 7100779 := bstep (se 1 (by rfl) ⟨5325584, by rfl⟩ : syracuseStep 7100779 = 10651169) B10651169
theorem B31545881 : Blo 1727064 31545881 := bstep (se 2 (by rfl) ⟨11829705, by rfl⟩ : syracuseStep 31545881 = 23659411) B23659411
theorem B9845327 : Blo 1727064 9845327 := bstep (se 1 (by rfl) ⟨7383995, by rfl⟩ : syracuseStep 9845327 = 14767991) B14767991
theorem B4373129 : Blo 1727064 4373129 := bstep (se 2 (by rfl) ⟨1639923, by rfl⟩ : syracuseStep 4373129 = 3279847) B3279847
theorem B1727323 : Blo 1727064 1727323 := bstep (se 1 (by rfl) ⟨1295492, by rfl⟩ : syracuseStep 1727323 = 2590985) B2590985
theorem B1727391 : Blo 1727064 1727391 := bstep (se 1 (by rfl) ⟨1295543, by rfl⟩ : syracuseStep 1727391 = 2591087) B2591087
theorem B11828177 : Blo 1727064 11828177 := bstep (se 2 (by rfl) ⟨4435566, by rfl⟩ : syracuseStep 11828177 = 8871133) B8871133
theorem B4373473 : Blo 1727064 4373473 := bstep (se 2 (by rfl) ⟨1640052, by rfl⟩ : syracuseStep 4373473 = 3280105) B3280105
theorem B1727535 : Blo 1727064 1727535 := bstep (se 1 (by rfl) ⟨1295651, by rfl⟩ : syracuseStep 1727535 = 2591303) B2591303
theorem B1727559 : Blo 1727064 1727559 := bstep (se 1 (by rfl) ⟨1295669, by rfl⟩ : syracuseStep 1727559 = 2591339) B2591339
theorem B2915399 : Blo 1727064 2915399 := bstep (se 1 (by rfl) ⟨2186549, by rfl⟩ : syracuseStep 2915399 = 4373099) B4373099
theorem B8748161 : Blo 1727064 8748161 := bstep (se 2 (by rfl) ⟨3280560, by rfl⟩ : syracuseStep 8748161 = 6561121) B6561121
theorem B1727711 : Blo 1727064 1727711 := bstep (se 1 (by rfl) ⟨1295783, by rfl⟩ : syracuseStep 1727711 = 2591567) B2591567
theorem B5831945 : Blo 1727064 5831945 := bstep (se 2 (by rfl) ⟨2186979, by rfl⟩ : syracuseStep 5831945 = 4373959) B4373959
theorem B1727975 : Blo 1727064 1727975 := bstep (se 1 (by rfl) ⟨1295981, by rfl⟩ : syracuseStep 1727975 = 2591963) B2591963
theorem B19963367 : Blo 1727064 19963367 := bstep (se 1 (by rfl) ⟨14972525, by rfl⟩ : syracuseStep 19963367 = 29945051) B29945051
theorem B2915831 : Blo 1727064 2915831 := bstep (se 1 (by rfl) ⟨2186873, by rfl⟩ : syracuseStep 2915831 = 4373747) B4373747
theorem B259038737 : Blo 1727064 259038737 := bstep (se 2 (by rfl) ⟨97139526, by rfl⟩ : syracuseStep 259038737 = 194279053) B194279053
theorem B14769701 : Blo 1727064 14769701 := bstep (se 4 (by rfl) ⟨1384659, by rfl⟩ : syracuseStep 14769701 = 2769319) B2769319
theorem B1728091 : Blo 1727064 1728091 := bstep (se 1 (by rfl) ⟨1296068, by rfl⟩ : syracuseStep 1728091 = 2592137) B2592137
theorem B8306363 : Blo 1727064 8306363 := bstep (se 1 (by rfl) ⟨6229772, by rfl⟩ : syracuseStep 8306363 = 12459545) B12459545
theorem B4374263 : Blo 1727064 4374263 := bstep (se 1 (by rfl) ⟨3280697, by rfl⟩ : syracuseStep 4374263 = 6561395) B6561395
theorem B6561607 : Blo 1727064 6561607 := bstep (se 1 (by rfl) ⟨4921205, by rfl⟩ : syracuseStep 6561607 = 9842411) B9842411
theorem B1728327 : Blo 1727064 1728327 := bstep (se 1 (by rfl) ⟨1296245, by rfl⟩ : syracuseStep 1728327 = 2592491) B2592491
theorem B4374395 : Blo 1727064 4374395 := bstep (se 1 (by rfl) ⟨3280796, by rfl⟩ : syracuseStep 4374395 = 6561593) B6561593
theorem B9838493 : Blo 1727064 9838493 := bstep (se 3 (by rfl) ⟨1844717, by rfl⟩ : syracuseStep 9838493 = 3689435) B3689435
theorem B8748971 : Blo 1727064 8748971 := bstep (se 1 (by rfl) ⟨6561728, by rfl⟩ : syracuseStep 8748971 = 13123457) B13123457
theorem B1728479 : Blo 1727064 1728479 := bstep (se 1 (by rfl) ⟨1296359, by rfl⟩ : syracuseStep 1728479 = 2592719) B2592719
theorem B4374719 : Blo 1727064 4374719 := bstep (se 1 (by rfl) ⟨3281039, by rfl⟩ : syracuseStep 4374719 = 6562079) B6562079
theorem B1728703 : Blo 1727064 1728703 := bstep (se 1 (by rfl) ⟨1296527, by rfl⟩ : syracuseStep 1728703 = 2593055) B2593055
theorem B11067587 : Blo 1727064 11067587 := bstep (se 1 (by rfl) ⟨8300690, by rfl⟩ : syracuseStep 11067587 = 16601381) B16601381
theorem B1728719 : Blo 1727064 1728719 := bstep (se 1 (by rfl) ⟨1296539, by rfl⟩ : syracuseStep 1728719 = 2593079) B2593079
theorem B7880923 : Blo 1727064 7880923 := bstep (se 1 (by rfl) ⟨5910692, by rfl⟩ : syracuseStep 7880923 = 11821385) B11821385
theorem B2916587 : Blo 1727064 2916587 := bstep (se 1 (by rfl) ⟨2187440, by rfl⟩ : syracuseStep 2916587 = 4374881) B4374881
theorem B1728767 : Blo 1727064 1728767 := bstep (se 1 (by rfl) ⟨1296575, by rfl⟩ : syracuseStep 1728767 = 2593151) B2593151
theorem B1728815 : Blo 1727064 1728815 := bstep (se 1 (by rfl) ⟨1296611, by rfl⟩ : syracuseStep 1728815 = 2593223) B2593223
theorem B42058061 : Blo 1727064 42058061 := bstep (se 3 (by rfl) ⟨7885886, by rfl⟩ : syracuseStep 42058061 = 15771773) B15771773
theorem B106406297 : Blo 1727064 106406297 := bstep (se 2 (by rfl) ⟨39902361, by rfl⟩ : syracuseStep 106406297 = 79804723) B79804723
theorem B7201307 : Blo 1727064 7201307 := bstep (se 1 (by rfl) ⟨5400980, by rfl⟩ : syracuseStep 7201307 = 10801961) B10801961
theorem B1729051 : Blo 1727064 1729051 := bstep (se 1 (by rfl) ⟨1296788, by rfl⟩ : syracuseStep 1729051 = 2593577) B2593577
theorem B1729055 : Blo 1727064 1729055 := bstep (se 1 (by rfl) ⟨1296791, by rfl⟩ : syracuseStep 1729055 = 2593583) B2593583
theorem B6562367 : Blo 1727064 6562367 := bstep (se 1 (by rfl) ⟨4921775, by rfl⟩ : syracuseStep 6562367 = 9843551) B9843551
theorem B5833295 : Blo 1727064 5833295 := bstep (se 1 (by rfl) ⟨4374971, by rfl⟩ : syracuseStep 5833295 = 8749943) B8749943
theorem B94544603 : Blo 1727064 94544603 := bstep (se 1 (by rfl) ⟨70908452, by rfl⟩ : syracuseStep 94544603 = 141816905) B141816905
theorem B13116167 : Blo 1727064 13116167 := bstep (se 1 (by rfl) ⟨9837125, by rfl⟩ : syracuseStep 13116167 = 19674251) B19674251
theorem B2188063 : Blo 1727064 2188063 := bstep (se 1 (by rfl) ⟨1641047, by rfl⟩ : syracuseStep 2188063 = 3282095) B3282095
theorem B28025675 : Blo 1727064 28025675 := bstep (se 1 (by rfl) ⟨21019256, by rfl⟩ : syracuseStep 28025675 = 42038513) B42038513
theorem B8750105 : Blo 1727064 8750105 := bstep (se 2 (by rfl) ⟨3281289, by rfl⟩ : syracuseStep 8750105 = 6562579) B6562579
theorem B5833835 : Blo 1727064 5833835 := bstep (se 1 (by rfl) ⟨4375376, by rfl⟩ : syracuseStep 5833835 = 8750753) B8750753
theorem B8299655 : Blo 1727064 8299655 := bstep (se 1 (by rfl) ⟨6224741, by rfl⟩ : syracuseStep 8299655 = 12449483) B12449483
theorem B7882091 : Blo 1727064 7882091 := bstep (se 1 (by rfl) ⟨5911568, by rfl⟩ : syracuseStep 7882091 = 11823137) B11823137
theorem B21030587 : Blo 1727064 21030587 := bstep (se 1 (by rfl) ⟨15772940, by rfl⟩ : syracuseStep 21030587 = 31545881) B31545881
theorem B2459327 : Blo 1727064 2459327 := bstep (se 1 (by rfl) ⟨1844495, by rfl⟩ : syracuseStep 2459327 = 3688991) B3688991
theorem B6563551 : Blo 1727064 6563551 := bstep (se 1 (by rfl) ⟨4922663, by rfl⟩ : syracuseStep 6563551 = 9845327) B9845327
theorem B4376551 : Blo 1727064 4376551 := bstep (se 1 (by rfl) ⟨3282413, by rfl⟩ : syracuseStep 4376551 = 6564827) B6564827
theorem B2590751 : Blo 1727064 2590751 := bstep (se 1 (by rfl) ⟨1943063, by rfl⟩ : syracuseStep 2590751 = 3886127) B3886127
theorem B1943599 : Blo 1727064 1943599 := bstep (se 1 (by rfl) ⟨1457699, by rfl⟩ : syracuseStep 1943599 = 2915399) B2915399
theorem B3279035 : Blo 1727064 3279035 := bstep (se 1 (by rfl) ⟨2459276, by rfl⟩ : syracuseStep 3279035 = 4918553) B4918553
theorem B2590943 : Blo 1727064 2590943 := bstep (se 1 (by rfl) ⟨1943207, by rfl⟩ : syracuseStep 2590943 = 3886415) B3886415
theorem B2591003 : Blo 1727064 2591003 := bstep (se 1 (by rfl) ⟨1943252, by rfl⟩ : syracuseStep 2591003 = 3886505) B3886505
theorem B1943887 : Blo 1727064 1943887 := bstep (se 1 (by rfl) ⟨1457915, by rfl⟩ : syracuseStep 1943887 = 2915831) B2915831
theorem B47278529 : Blo 1727064 47278529 := bstep (se 2 (by rfl) ⟨17729448, by rfl⟩ : syracuseStep 47278529 = 35458897) B35458897
theorem B2591327 : Blo 1727064 2591327 := bstep (se 1 (by rfl) ⟨1943495, by rfl⟩ : syracuseStep 2591327 = 3886991) B3886991
theorem B3279521 : Blo 1727064 3279521 := bstep (se 2 (by rfl) ⟨1229820, by rfl⟩ : syracuseStep 3279521 = 2459641) B2459641
theorem B6564523 : Blo 1727064 6564523 := bstep (se 1 (by rfl) ⟨4923392, by rfl⟩ : syracuseStep 6564523 = 9846785) B9846785
theorem B60689225 : Blo 1727064 60689225 := bstep (se 2 (by rfl) ⟨22758459, by rfl⟩ : syracuseStep 60689225 = 45516919) B45516919
theorem B3885929 : Blo 1727064 3885929 := bstep (se 2 (by rfl) ⟨1457223, by rfl⟩ : syracuseStep 3885929 = 2914447) B2914447
theorem B2591609 : Blo 1727064 2591609 := bstep (se 2 (by rfl) ⟨971853, by rfl⟩ : syracuseStep 2591609 = 1943707) B1943707
theorem B3885983 : Blo 1727064 3885983 := bstep (se 1 (by rfl) ⟨2914487, by rfl⟩ : syracuseStep 3885983 = 5828975) B5828975
theorem B2591657 : Blo 1727064 2591657 := bstep (se 2 (by rfl) ⟨971871, by rfl⟩ : syracuseStep 2591657 = 1943743) B1943743
theorem B7384031 : Blo 1727064 7384031 := bstep (se 1 (by rfl) ⟨5538023, by rfl⟩ : syracuseStep 7384031 = 11076047) B11076047
theorem B1944571 : Blo 1727064 1944571 := bstep (se 1 (by rfl) ⟨1458428, by rfl⟩ : syracuseStep 1944571 = 2916857) B2916857
theorem B9341999 : Blo 1727064 9341999 := bstep (se 1 (by rfl) ⟨7006499, by rfl⟩ : syracuseStep 9341999 = 14012999) B14012999
theorem B2075711 : Blo 1727064 2075711 := bstep (se 1 (by rfl) ⟨1556783, by rfl⟩ : syracuseStep 2075711 = 3113567) B3113567
theorem B2591807 : Blo 1727064 2591807 := bstep (se 1 (by rfl) ⟨1943855, by rfl⟩ : syracuseStep 2591807 = 3887711) B3887711
theorem B1944751 : Blo 1727064 1944751 := bstep (se 1 (by rfl) ⟨1458563, by rfl⟩ : syracuseStep 1944751 = 2917127) B2917127
theorem B2592359 : Blo 1727064 2592359 := bstep (se 1 (by rfl) ⟨1944269, by rfl⟩ : syracuseStep 2592359 = 3888539) B3888539
theorem B13119083 : Blo 1727064 13119083 := bstep (se 1 (by rfl) ⟨9839312, by rfl⟩ : syracuseStep 13119083 = 19678625) B19678625
theorem B3886919 : Blo 1727064 3886919 := bstep (se 1 (by rfl) ⟨2915189, by rfl⟩ : syracuseStep 3886919 = 5830379) B5830379
theorem B2592743 : Blo 1727064 2592743 := bstep (se 1 (by rfl) ⟨1944557, by rfl⟩ : syracuseStep 2592743 = 3889115) B3889115
theorem B3887099 : Blo 1727064 3887099 := bstep (se 1 (by rfl) ⟨2915324, by rfl⟩ : syracuseStep 3887099 = 5830649) B5830649
theorem B2461691 : Blo 1727064 2461691 := bstep (se 1 (by rfl) ⟨1846268, by rfl⟩ : syracuseStep 2461691 = 3692537) B3692537
theorem B2592863 : Blo 1727064 2592863 := bstep (se 1 (by rfl) ⟨1944647, by rfl⟩ : syracuseStep 2592863 = 3889295) B3889295
theorem B3887207 : Blo 1727064 3887207 := bstep (se 1 (by rfl) ⟨2915405, by rfl⟩ : syracuseStep 3887207 = 5830811) B5830811
theorem B2461799 : Blo 1727064 2461799 := bstep (se 1 (by rfl) ⟨1846349, by rfl⟩ : syracuseStep 2461799 = 3692699) B3692699
theorem B2592875 : Blo 1727064 2592875 := bstep (se 1 (by rfl) ⟨1944656, by rfl⟩ : syracuseStep 2592875 = 3889313) B3889313
theorem B127766645 : Blo 1727064 127766645 := bstep (se 5 (by rfl) ⟨5989061, by rfl⟩ : syracuseStep 127766645 = 11978123) B11978123
theorem B3551375 : Blo 1727064 3551375 := bstep (se 1 (by rfl) ⟨2663531, by rfl⟩ : syracuseStep 3551375 = 5327063) B5327063
theorem B2592923 : Blo 1727064 2592923 := bstep (se 1 (by rfl) ⟨1944692, by rfl⟩ : syracuseStep 2592923 = 3889385) B3889385
theorem B3887279 : Blo 1727064 3887279 := bstep (se 1 (by rfl) ⟨2915459, by rfl⟩ : syracuseStep 3887279 = 5830919) B5830919
theorem B25260295 : Blo 1727064 25260295 := bstep (se 1 (by rfl) ⟨18945221, by rfl⟩ : syracuseStep 25260295 = 37890443) B37890443
theorem B7385363 : Blo 1727064 7385363 := bstep (se 1 (by rfl) ⟨5539022, by rfl⟩ : syracuseStep 7385363 = 11078045) B11078045
theorem B6557993 : Blo 1727064 6557993 := bstep (se 2 (by rfl) ⟨2459247, by rfl⟩ : syracuseStep 6557993 = 4918495) B4918495
theorem B7885451 : Blo 1727064 7885451 := bstep (se 1 (by rfl) ⟨5914088, by rfl⟩ : syracuseStep 7885451 = 11828177) B11828177
theorem B29528873 : Blo 1727064 29528873 := bstep (se 2 (by rfl) ⟨11073327, by rfl⟩ : syracuseStep 29528873 = 22146655) B22146655
theorem B3887963 : Blo 1727064 3887963 := bstep (se 1 (by rfl) ⟨2915972, by rfl⟩ : syracuseStep 3887963 = 5831945) B5831945
theorem B13308911 : Blo 1727064 13308911 := bstep (se 1 (by rfl) ⟨9981683, by rfl⟩ : syracuseStep 13308911 = 19963367) B19963367
theorem B172692491 : Blo 1727064 172692491 := bstep (se 1 (by rfl) ⟨129519368, by rfl⟩ : syracuseStep 172692491 = 259038737) B259038737
theorem B6558995 : Blo 1727064 6558995 := bstep (se 1 (by rfl) ⟨4919246, by rfl⟩ : syracuseStep 6558995 = 9838493) B9838493
theorem B53925263 : Blo 1727064 53925263 := bstep (se 1 (by rfl) ⟨40443947, by rfl⟩ : syracuseStep 53925263 = 80887895) B80887895
theorem B5830055 : Blo 1727064 5830055 := bstep (se 1 (by rfl) ⟨4372541, by rfl⟩ : syracuseStep 5830055 = 8745083) B8745083
theorem B5830163 : Blo 1727064 5830163 := bstep (se 1 (by rfl) ⟨4372622, by rfl⟩ : syracuseStep 5830163 = 8745245) B8745245
theorem B3888719 : Blo 1727064 3888719 := bstep (se 1 (by rfl) ⟨2916539, by rfl⟩ : syracuseStep 3888719 = 5833079) B5833079
theorem B6559451 : Blo 1727064 6559451 := bstep (se 1 (by rfl) ⟨4919588, by rfl⟩ : syracuseStep 6559451 = 9839177) B9839177
theorem B14005993 : Blo 1727064 14005993 := bstep (se 2 (by rfl) ⟨5252247, by rfl⟩ : syracuseStep 14005993 = 10504495) B10504495
theorem B9467705 : Blo 1727064 9467705 := bstep (se 2 (by rfl) ⟨3550389, by rfl⟩ : syracuseStep 9467705 = 7100779) B7100779
theorem B4921469 : Blo 1727064 4921469 := bstep (se 3 (by rfl) ⟨922775, by rfl⟩ : syracuseStep 4921469 = 1845551) B1845551
theorem B2914535 : Blo 1727064 2914535 := bstep (se 1 (by rfl) ⟨2185901, by rfl⟩ : syracuseStep 2914535 = 4371803) B4371803
theorem B3889439 : Blo 1727064 3889439 := bstep (se 1 (by rfl) ⟨2917079, by rfl⟩ : syracuseStep 3889439 = 5834159) B5834159
theorem B4372775 : Blo 1727064 4372775 := bstep (se 1 (by rfl) ⟨3279581, by rfl⟩ : syracuseStep 4372775 = 6559163) B6559163
theorem B127875527 : Blo 1727064 127875527 := bstep (se 1 (by rfl) ⟨95906645, by rfl⟩ : syracuseStep 127875527 = 191813291) B191813291
theorem B3889691 : Blo 1727064 3889691 := bstep (se 1 (by rfl) ⟨2917268, by rfl⟩ : syracuseStep 3889691 = 5834537) B5834537
theorem B1727067 : Blo 1727064 1727067 := bstep (se 1 (by rfl) ⟨1295300, by rfl⟩ : syracuseStep 1727067 = 2590601) B2590601
theorem B5831297 : Blo 1727064 5831297 := bstep (se 2 (by rfl) ⟨2186736, by rfl⟩ : syracuseStep 5831297 = 4373473) B4373473
theorem B1727135 : Blo 1727064 1727135 := bstep (se 1 (by rfl) ⟨1295351, by rfl⟩ : syracuseStep 1727135 = 2590703) B2590703
theorem B1727303 : Blo 1727064 1727303 := bstep (se 1 (by rfl) ⟨1295477, by rfl⟩ : syracuseStep 1727303 = 2590955) B2590955
theorem B1727343 : Blo 1727064 1727343 := bstep (se 1 (by rfl) ⟨1295507, by rfl⟩ : syracuseStep 1727343 = 2591015) B2591015
theorem B6560635 : Blo 1727064 6560635 := bstep (se 1 (by rfl) ⟨4920476, by rfl⟩ : syracuseStep 6560635 = 9840953) B9840953
theorem B1727399 : Blo 1727064 1727399 := bstep (se 1 (by rfl) ⟨1295549, by rfl⟩ : syracuseStep 1727399 = 2591099) B2591099
theorem B33217523 : Blo 1727064 33217523 := bstep (se 1 (by rfl) ⟨24913142, by rfl⟩ : syracuseStep 33217523 = 49826285) B49826285
theorem B17742881 : Blo 1727064 17742881 := bstep (se 2 (by rfl) ⟨6653580, by rfl⟩ : syracuseStep 17742881 = 13307161) B13307161
theorem B1727579 : Blo 1727064 1727579 := bstep (se 1 (by rfl) ⟨1295684, by rfl⟩ : syracuseStep 1727579 = 2591369) B2591369
theorem B2915419 : Blo 1727064 2915419 := bstep (se 1 (by rfl) ⟨2186564, by rfl⟩ : syracuseStep 2915419 = 4373129) B4373129
theorem B1727695 : Blo 1727064 1727695 := bstep (se 1 (by rfl) ⟨1295771, by rfl⟩ : syracuseStep 1727695 = 2591543) B2591543
theorem B42048719 : Blo 1727064 42048719 := bstep (se 1 (by rfl) ⟨31536539, by rfl⟩ : syracuseStep 42048719 = 63073079) B63073079
theorem B1727719 : Blo 1727064 1727719 := bstep (se 1 (by rfl) ⟨1295789, by rfl⟩ : syracuseStep 1727719 = 2591579) B2591579
theorem B1727815 : Blo 1727064 1727815 := bstep (se 1 (by rfl) ⟨1295861, by rfl⟩ : syracuseStep 1727815 = 2591723) B2591723
theorem B8871277 : Blo 1727064 8871277 := bstep (se 3 (by rfl) ⟨1663364, by rfl⟩ : syracuseStep 8871277 = 3326729) B3326729
theorem B5832107 : Blo 1727064 5832107 := bstep (se 1 (by rfl) ⟨4374080, by rfl⟩ : syracuseStep 5832107 = 8748161) B8748161
theorem B1727951 : Blo 1727064 1727951 := bstep (se 1 (by rfl) ⟨1295963, by rfl⟩ : syracuseStep 1727951 = 2591927) B2591927
theorem B22142555 : Blo 1727064 22142555 := bstep (se 1 (by rfl) ⟨16606916, by rfl⟩ : syracuseStep 22142555 = 33213833) B33213833
theorem B1728111 : Blo 1727064 1728111 := bstep (se 1 (by rfl) ⟨1296083, by rfl⟩ : syracuseStep 1728111 = 2592167) B2592167
theorem B1728167 : Blo 1727064 1728167 := bstep (se 1 (by rfl) ⟨1296125, by rfl⟩ : syracuseStep 1728167 = 2592251) B2592251
theorem B9846467 : Blo 1727064 9846467 := bstep (se 1 (by rfl) ⟨7384850, by rfl⟩ : syracuseStep 9846467 = 14769701) B14769701
theorem B1728231 : Blo 1727064 1728231 := bstep (se 1 (by rfl) ⟨1296173, by rfl⟩ : syracuseStep 1728231 = 2592347) B2592347
theorem B8748809 : Blo 1727064 8748809 := bstep (se 2 (by rfl) ⟨3280803, by rfl⟩ : syracuseStep 8748809 = 6561607) B6561607
theorem B1728287 : Blo 1727064 1728287 := bstep (se 1 (by rfl) ⟨1296215, by rfl⟩ : syracuseStep 1728287 = 2592431) B2592431
theorem B5537575 : Blo 1727064 5537575 := bstep (se 1 (by rfl) ⟨4153181, by rfl⟩ : syracuseStep 5537575 = 8306363) B8306363
theorem B2916175 : Blo 1727064 2916175 := bstep (se 1 (by rfl) ⟨2187131, by rfl⟩ : syracuseStep 2916175 = 4374263) B4374263
theorem B1728367 : Blo 1727064 1728367 := bstep (se 1 (by rfl) ⟨1296275, by rfl⟩ : syracuseStep 1728367 = 2592551) B2592551
theorem B2916263 : Blo 1727064 2916263 := bstep (se 1 (by rfl) ⟨2187197, by rfl⟩ : syracuseStep 2916263 = 4374395) B4374395
theorem B1728423 : Blo 1727064 1728423 := bstep (se 1 (by rfl) ⟨1296317, by rfl⟩ : syracuseStep 1728423 = 2592635) B2592635
theorem B5832647 : Blo 1727064 5832647 := bstep (se 1 (by rfl) ⟨4374485, by rfl⟩ : syracuseStep 5832647 = 8748971) B8748971
theorem B1728575 : Blo 1727064 1728575 := bstep (se 1 (by rfl) ⟨1296431, by rfl⟩ : syracuseStep 1728575 = 2592863) B2592863
theorem B1728583 : Blo 1727064 1728583 := bstep (se 1 (by rfl) ⟨1296437, by rfl⟩ : syracuseStep 1728583 = 2592875) B2592875
theorem B1728615 : Blo 1727064 1728615 := bstep (se 1 (by rfl) ⟨1296461, by rfl⟩ : syracuseStep 1728615 = 2592923) B2592923
theorem B1842053237 : Blo 1727064 1842053237 := bstep (se 5 (by rfl) ⟨86346245, by rfl⟩ : syracuseStep 1842053237 = 172692491) B172692491
theorem B2916479 : Blo 1727064 2916479 := bstep (se 1 (by rfl) ⟨2187359, by rfl⟩ : syracuseStep 2916479 = 4374719) B4374719
theorem B4923575 : Blo 1727064 4923575 := bstep (se 1 (by rfl) ⟨3692681, by rfl⟩ : syracuseStep 4923575 = 7385363) B7385363
theorem B4800871 : Blo 1727064 4800871 := bstep (se 1 (by rfl) ⟨3600653, by rfl⟩ : syracuseStep 4800871 = 7201307) B7201307
theorem B9470333 : Blo 1727064 9470333 := bstep (se 3 (by rfl) ⟨1775687, by rfl⟩ : syracuseStep 9470333 = 3551375) B3551375
theorem B4374911 : Blo 1727064 4374911 := bstep (se 1 (by rfl) ⟨3281183, by rfl⟩ : syracuseStep 4374911 = 6562367) B6562367
theorem B63029735 : Blo 1727064 63029735 := bstep (se 1 (by rfl) ⟨47272301, by rfl⟩ : syracuseStep 63029735 = 94544603) B94544603
theorem B19685915 : Blo 1727064 19685915 := bstep (se 1 (by rfl) ⟨14764436, by rfl⟩ : syracuseStep 19685915 = 29528873) B29528873
theorem B8872607 : Blo 1727064 8872607 := bstep (se 1 (by rfl) ⟨6654455, by rfl⟩ : syracuseStep 8872607 = 13308911) B13308911
theorem B5833403 : Blo 1727064 5833403 := bstep (se 1 (by rfl) ⟨4375052, by rfl⟩ : syracuseStep 5833403 = 8750105) B8750105
theorem B2917417 : Blo 1727064 2917417 := bstep (se 2 (by rfl) ⟨1094031, by rfl⟩ : syracuseStep 2917417 = 2188063) B2188063
theorem B1943023 : Blo 1727064 1943023 := bstep (se 1 (by rfl) ⟨1457267, by rfl⟩ : syracuseStep 1943023 = 2914535) B2914535
theorem B2590619 : Blo 1727064 2590619 := bstep (se 1 (by rfl) ⟨1942964, by rfl⟩ : syracuseStep 2590619 = 3885929) B3885929
theorem B2590655 : Blo 1727064 2590655 := bstep (se 1 (by rfl) ⟨1942991, by rfl⟩ : syracuseStep 2590655 = 3885983) B3885983
theorem B22145015 : Blo 1727064 22145015 := bstep (se 1 (by rfl) ⟨16608761, by rfl⟩ : syracuseStep 22145015 = 33217523) B33217523
theorem B6227999 : Blo 1727064 6227999 := bstep (se 1 (by rfl) ⟨4670999, by rfl⟩ : syracuseStep 6227999 = 9341999) B9341999
theorem B8751401 : Blo 1727064 8751401 := bstep (se 2 (by rfl) ⟨3281775, by rfl⟩ : syracuseStep 8751401 = 6563551) B6563551
theorem B7383433 : Blo 1727064 7383433 := bstep (se 2 (by rfl) ⟨2768787, by rfl⟩ : syracuseStep 7383433 = 5537575) B5537575
theorem B6564311 : Blo 1727064 6564311 := bstep (se 1 (by rfl) ⟨4923233, by rfl⟩ : syracuseStep 6564311 = 9846467) B9846467
theorem B2591279 : Blo 1727064 2591279 := bstep (se 1 (by rfl) ⟨1943459, by rfl⟩ : syracuseStep 2591279 = 3886919) B3886919
theorem B1944175 : Blo 1727064 1944175 := bstep (se 1 (by rfl) ⟨1458131, by rfl⟩ : syracuseStep 1944175 = 2916263) B2916263
theorem B5835401 : Blo 1727064 5835401 := bstep (se 2 (by rfl) ⟨2188275, by rfl⟩ : syracuseStep 5835401 = 4376551) B4376551
theorem B6564509 : Blo 1727064 6564509 := bstep (se 3 (by rfl) ⟨1230845, by rfl⟩ : syracuseStep 6564509 = 2461691) B2461691
theorem B2591399 : Blo 1727064 2591399 := bstep (se 1 (by rfl) ⟨1943549, by rfl⟩ : syracuseStep 2591399 = 3887099) B3887099
theorem B2591465 : Blo 1727064 2591465 := bstep (se 2 (by rfl) ⟨971799, by rfl⟩ : syracuseStep 2591465 = 1943599) B1943599
theorem B2591471 : Blo 1727064 2591471 := bstep (se 1 (by rfl) ⟨1943603, by rfl⟩ : syracuseStep 2591471 = 3887207) B3887207
theorem B2591519 : Blo 1727064 2591519 := bstep (se 1 (by rfl) ⟨1943639, by rfl⟩ : syracuseStep 2591519 = 3887279) B3887279
theorem B1944391 : Blo 1727064 1944391 := bstep (se 1 (by rfl) ⟨1458293, by rfl⟩ : syracuseStep 1944391 = 2916587) B2916587
theorem B70937531 : Blo 1727064 70937531 := bstep (se 1 (by rfl) ⟨53203148, by rfl⟩ : syracuseStep 70937531 = 106406297) B106406297
theorem B6564797 : Blo 1727064 6564797 := bstep (se 3 (by rfl) ⟨1230899, by rfl⟩ : syracuseStep 6564797 = 2461799) B2461799
theorem B33680393 : Blo 1727064 33680393 := bstep (se 2 (by rfl) ⟨12630147, by rfl⟩ : syracuseStep 33680393 = 25260295) B25260295
theorem B2591849 : Blo 1727064 2591849 := bstep (se 2 (by rfl) ⟨971943, by rfl⟩ : syracuseStep 2591849 = 1943887) B1943887
theorem B8744111 : Blo 1727064 8744111 := bstep (se 1 (by rfl) ⟨6558083, by rfl⟩ : syracuseStep 8744111 = 13116167) B13116167
theorem B2591975 : Blo 1727064 2591975 := bstep (se 1 (by rfl) ⟨1943981, by rfl⟩ : syracuseStep 2591975 = 3887963) B3887963
theorem B5533103 : Blo 1727064 5533103 := bstep (se 1 (by rfl) ⟨4149827, by rfl⟩ : syracuseStep 5533103 = 8299655) B8299655
theorem B8752697 : Blo 1727064 8752697 := bstep (se 2 (by rfl) ⟨3282261, by rfl⟩ : syracuseStep 8752697 = 6564523) B6564523
theorem B5254727 : Blo 1727064 5254727 := bstep (se 1 (by rfl) ⟨3941045, by rfl⟩ : syracuseStep 5254727 = 7882091) B7882091
theorem B35950175 : Blo 1727064 35950175 := bstep (se 1 (by rfl) ⟨26962631, by rfl⟩ : syracuseStep 35950175 = 53925263) B53925263
theorem B3886703 : Blo 1727064 3886703 := bstep (se 1 (by rfl) ⟨2915027, by rfl⟩ : syracuseStep 3886703 = 5830055) B5830055
theorem B3886775 : Blo 1727064 3886775 := bstep (se 1 (by rfl) ⟨2915081, by rfl⟩ : syracuseStep 3886775 = 5830163) B5830163
theorem B2592479 : Blo 1727064 2592479 := bstep (se 1 (by rfl) ⟨1944359, by rfl⟩ : syracuseStep 2592479 = 3888719) B3888719
theorem B14020391 : Blo 1727064 14020391 := bstep (se 1 (by rfl) ⟨10515293, by rfl⟩ : syracuseStep 14020391 = 21030587) B21030587
theorem B6311803 : Blo 1727064 6311803 := bstep (se 1 (by rfl) ⟨4733852, by rfl⟩ : syracuseStep 6311803 = 9467705) B9467705
theorem B2592761 : Blo 1727064 2592761 := bstep (se 2 (by rfl) ⟨972285, by rfl⟩ : syracuseStep 2592761 = 1944571) B1944571
theorem B3280979 : Blo 1727064 3280979 := bstep (se 1 (by rfl) ⟨2460734, by rfl⟩ : syracuseStep 3280979 = 4921469) B4921469
theorem B3887225 : Blo 1727064 3887225 := bstep (se 2 (by rfl) ⟨1457709, by rfl⟩ : syracuseStep 3887225 = 2915419) B2915419
theorem B2592959 : Blo 1727064 2592959 := bstep (se 1 (by rfl) ⟨1944719, by rfl⟩ : syracuseStep 2592959 = 3889439) B3889439
theorem B2593001 : Blo 1727064 2593001 := bstep (se 2 (by rfl) ⟨972375, by rfl⟩ : syracuseStep 2593001 = 1944751) B1944751
theorem B31519019 : Blo 1727064 31519019 := bstep (se 1 (by rfl) ⟨23639264, by rfl⟩ : syracuseStep 31519019 = 47278529) B47278529
theorem B85250351 : Blo 1727064 85250351 := bstep (se 1 (by rfl) ⟨63937763, by rfl⟩ : syracuseStep 85250351 = 127875527) B127875527
theorem B2593127 : Blo 1727064 2593127 := bstep (se 1 (by rfl) ⟨1944845, by rfl⟩ : syracuseStep 2593127 = 3889691) B3889691
theorem B3887531 : Blo 1727064 3887531 := bstep (se 1 (by rfl) ⟨2915648, by rfl⟩ : syracuseStep 3887531 = 5831297) B5831297
theorem B6558205 : Blo 1727064 6558205 := bstep (se 3 (by rfl) ⟨1229663, by rfl⟩ : syracuseStep 6558205 = 2459327) B2459327
theorem B3888071 : Blo 1727064 3888071 := bstep (se 1 (by rfl) ⟨2916053, by rfl⟩ : syracuseStep 3888071 = 5832107) B5832107
theorem B18674657 : Blo 1727064 18674657 := bstep (se 2 (by rfl) ⟨7002996, by rfl⟩ : syracuseStep 18674657 = 14005993) B14005993
theorem B8746055 : Blo 1727064 8746055 := bstep (se 1 (by rfl) ⟨6559541, by rfl⟩ : syracuseStep 8746055 = 13119083) B13119083
theorem B3888233 : Blo 1727064 3888233 := bstep (se 2 (by rfl) ⟨1458087, by rfl⟩ : syracuseStep 3888233 = 2916175) B2916175
theorem B3888431 : Blo 1727064 3888431 := bstep (se 1 (by rfl) ⟨2916323, by rfl⟩ : syracuseStep 3888431 = 5832647) B5832647
theorem B85177763 : Blo 1727064 85177763 := bstep (se 1 (by rfl) ⟨63883322, by rfl⟩ : syracuseStep 85177763 = 127766645) B127766645
theorem B7378391 : Blo 1727064 7378391 := bstep (se 1 (by rfl) ⟨5533793, by rfl⟩ : syracuseStep 7378391 = 11067587) B11067587
theorem B5535229 : Blo 1727064 5535229 := bstep (se 3 (by rfl) ⟨1037855, by rfl⟩ : syracuseStep 5535229 = 2075711) B2075711
theorem B4371995 : Blo 1727064 4371995 := bstep (se 1 (by rfl) ⟨3278996, by rfl⟩ : syracuseStep 4371995 = 6557993) B6557993
theorem B28038707 : Blo 1727064 28038707 := bstep (se 1 (by rfl) ⟨21029030, by rfl⟩ : syracuseStep 28038707 = 42058061) B42058061
theorem B10507897 : Blo 1727064 10507897 := bstep (se 2 (by rfl) ⟨3940461, by rfl⟩ : syracuseStep 10507897 = 7880923) B7880923
theorem B3888863 : Blo 1727064 3888863 := bstep (se 1 (by rfl) ⟨2916647, by rfl⟩ : syracuseStep 3888863 = 5833295) B5833295
theorem B18683783 : Blo 1727064 18683783 := bstep (se 1 (by rfl) ⟨14012837, by rfl⟩ : syracuseStep 18683783 = 28025675) B28025675
theorem B3889223 : Blo 1727064 3889223 := bstep (se 1 (by rfl) ⟨2916917, by rfl⟩ : syracuseStep 3889223 = 5833835) B5833835
theorem B4372663 : Blo 1727064 4372663 := bstep (se 1 (by rfl) ⟨3279497, by rfl⟩ : syracuseStep 4372663 = 6558995) B6558995
theorem B4372967 : Blo 1727064 4372967 := bstep (se 1 (by rfl) ⟨3279725, by rfl⟩ : syracuseStep 4372967 = 6559451) B6559451
theorem B8747513 : Blo 1727064 8747513 := bstep (se 2 (by rfl) ⟨3280317, by rfl⟩ : syracuseStep 8747513 = 6560635) B6560635
theorem B1727167 : Blo 1727064 1727167 := bstep (se 1 (by rfl) ⟨1295375, by rfl⟩ : syracuseStep 1727167 = 2590751) B2590751
theorem B2186023 : Blo 1727064 2186023 := bstep (se 1 (by rfl) ⟨1639517, by rfl⟩ : syracuseStep 2186023 = 3279035) B3279035
theorem B1727295 : Blo 1727064 1727295 := bstep (se 1 (by rfl) ⟨1295471, by rfl⟩ : syracuseStep 1727295 = 2590943) B2590943
theorem B1727335 : Blo 1727064 1727335 := bstep (se 1 (by rfl) ⟨1295501, by rfl⟩ : syracuseStep 1727335 = 2591003) B2591003
theorem B2915183 : Blo 1727064 2915183 := bstep (se 1 (by rfl) ⟨2186387, by rfl⟩ : syracuseStep 2915183 = 4372775) B4372775
theorem B21027869 : Blo 1727064 21027869 := bstep (se 3 (by rfl) ⟨3942725, by rfl⟩ : syracuseStep 21027869 = 7885451) B7885451
theorem B1727551 : Blo 1727064 1727551 := bstep (se 1 (by rfl) ⟨1295663, by rfl⟩ : syracuseStep 1727551 = 2591327) B2591327
theorem B2186347 : Blo 1727064 2186347 := bstep (se 1 (by rfl) ⟨1639760, by rfl⟩ : syracuseStep 2186347 = 3279521) B3279521
theorem B11828369 : Blo 1727064 11828369 := bstep (se 2 (by rfl) ⟨4435638, by rfl⟩ : syracuseStep 11828369 = 8871277) B8871277
theorem B40459483 : Blo 1727064 40459483 := bstep (se 1 (by rfl) ⟨30344612, by rfl⟩ : syracuseStep 40459483 = 60689225) B60689225
theorem B1727739 : Blo 1727064 1727739 := bstep (se 1 (by rfl) ⟨1295804, by rfl⟩ : syracuseStep 1727739 = 2591609) B2591609
theorem B1727771 : Blo 1727064 1727771 := bstep (se 1 (by rfl) ⟨1295828, by rfl⟩ : syracuseStep 1727771 = 2591657) B2591657
theorem B4922687 : Blo 1727064 4922687 := bstep (se 1 (by rfl) ⟨3692015, by rfl⟩ : syracuseStep 4922687 = 7384031) B7384031
theorem B11828587 : Blo 1727064 11828587 := bstep (se 1 (by rfl) ⟨8871440, by rfl⟩ : syracuseStep 11828587 = 17742881) B17742881
theorem B1727871 : Blo 1727064 1727871 := bstep (se 1 (by rfl) ⟨1295903, by rfl⟩ : syracuseStep 1727871 = 2591807) B2591807
theorem B28032479 : Blo 1727064 28032479 := bstep (se 1 (by rfl) ⟨21024359, by rfl⟩ : syracuseStep 28032479 = 42048719) B42048719
theorem B14761703 : Blo 1727064 14761703 := bstep (se 1 (by rfl) ⟨11071277, by rfl⟩ : syracuseStep 14761703 = 22142555) B22142555
theorem B1728239 : Blo 1727064 1728239 := bstep (se 1 (by rfl) ⟨1296179, by rfl⟩ : syracuseStep 1728239 = 2592359) B2592359
theorem B5832539 : Blo 1727064 5832539 := bstep (se 1 (by rfl) ⟨4374404, by rfl⟩ : syracuseStep 5832539 = 8748809) B8748809
theorem B1728495 : Blo 1727064 1728495 := bstep (se 1 (by rfl) ⟨1296371, by rfl⟩ : syracuseStep 1728495 = 2592743) B2592743
theorem B2187319 : Blo 1727064 2187319 := bstep (se 1 (by rfl) ⟨1640489, by rfl⟩ : syracuseStep 2187319 = 3280979) B3280979
theorem B1728639 : Blo 1727064 1728639 := bstep (se 1 (by rfl) ⟨1296479, by rfl⟩ : syracuseStep 1728639 = 2592959) B2592959
theorem B1728667 : Blo 1727064 1728667 := bstep (se 1 (by rfl) ⟨1296500, by rfl⟩ : syracuseStep 1728667 = 2593001) B2593001
theorem B21012679 : Blo 1727064 21012679 := bstep (se 1 (by rfl) ⟨15759509, by rfl⟩ : syracuseStep 21012679 = 31519019) B31519019
theorem B1728751 : Blo 1727064 1728751 := bstep (se 1 (by rfl) ⟨1296563, by rfl⟩ : syracuseStep 1728751 = 2593127) B2593127
theorem B2916607 : Blo 1727064 2916607 := bstep (se 1 (by rfl) ⟨2187455, by rfl⟩ : syracuseStep 2916607 = 4374911) B4374911
theorem B13123943 : Blo 1727064 13123943 := bstep (se 1 (by rfl) ⟨9842957, by rfl⟩ : syracuseStep 13123943 = 19685915) B19685915
theorem B5915071 : Blo 1727064 5915071 := bstep (se 1 (by rfl) ⟨4436303, by rfl⟩ : syracuseStep 5915071 = 8872607) B8872607
theorem B56042117 : Blo 1727064 56042117 := bstep (se 4 (by rfl) ⟨5253948, by rfl⟩ : syracuseStep 56042117 = 10507897) B10507897
theorem B14763343 : Blo 1727064 14763343 := bstep (se 1 (by rfl) ⟨11072507, by rfl⟩ : syracuseStep 14763343 = 22145015) B22145015
theorem B5834267 : Blo 1727064 5834267 := bstep (se 1 (by rfl) ⟨4375700, by rfl⟩ : syracuseStep 5834267 = 8751401) B8751401
theorem B4376207 : Blo 1727064 4376207 := bstep (se 1 (by rfl) ⟨3282155, by rfl⟩ : syracuseStep 4376207 = 6564311) B6564311
theorem B4376339 : Blo 1727064 4376339 := bstep (se 1 (by rfl) ⟨3282254, by rfl⟩ : syracuseStep 4376339 = 6564509) B6564509
theorem B15771449 : Blo 1727064 15771449 := bstep (se 2 (by rfl) ⟨5914293, by rfl⟩ : syracuseStep 15771449 = 11828587) B11828587
theorem B1943455 : Blo 1727064 1943455 := bstep (se 1 (by rfl) ⟨1457591, by rfl⟩ : syracuseStep 1943455 = 2915183) B2915183
theorem B4376531 : Blo 1727064 4376531 := bstep (se 1 (by rfl) ⟨3282398, by rfl⟩ : syracuseStep 4376531 = 6564797) B6564797
theorem B2590697 : Blo 1727064 2590697 := bstep (se 2 (by rfl) ⟨971511, by rfl⟩ : syracuseStep 2590697 = 1943023) B1943023
theorem B14018579 : Blo 1727064 14018579 := bstep (se 1 (by rfl) ⟨10513934, by rfl⟩ : syracuseStep 14018579 = 21027869) B21027869
theorem B3688735 : Blo 1727064 3688735 := bstep (se 1 (by rfl) ⟨2766551, by rfl⟩ : syracuseStep 3688735 = 5533103) B5533103
theorem B18688319 : Blo 1727064 18688319 := bstep (se 1 (by rfl) ⟨14016239, by rfl⟩ : syracuseStep 18688319 = 28032479) B28032479
theorem B5835131 : Blo 1727064 5835131 := bstep (se 1 (by rfl) ⟨4376348, by rfl⟩ : syracuseStep 5835131 = 8752697) B8752697
theorem B2591135 : Blo 1727064 2591135 := bstep (se 1 (by rfl) ⟨1943351, by rfl⟩ : syracuseStep 2591135 = 3886703) B3886703
theorem B2591183 : Blo 1727064 2591183 := bstep (se 1 (by rfl) ⟨1943387, by rfl⟩ : syracuseStep 2591183 = 3886775) B3886775
theorem B9841135 : Blo 1727064 9841135 := bstep (se 1 (by rfl) ⟨7380851, by rfl⟩ : syracuseStep 9841135 = 14761703) B14761703
theorem B8415737 : Blo 1727064 8415737 := bstep (se 2 (by rfl) ⟨3155901, by rfl⟩ : syracuseStep 8415737 = 6311803) B6311803
theorem B2591483 : Blo 1727064 2591483 := bstep (se 1 (by rfl) ⟨1943612, by rfl⟩ : syracuseStep 2591483 = 3887225) B3887225
theorem B1944319 : Blo 1727064 1944319 := bstep (se 1 (by rfl) ⟨1458239, by rfl⟩ : syracuseStep 1944319 = 2916479) B2916479
theorem B2591687 : Blo 1727064 2591687 := bstep (se 1 (by rfl) ⟨1943765, by rfl⟩ : syracuseStep 2591687 = 3887531) B3887531
theorem B42019823 : Blo 1727064 42019823 := bstep (se 1 (by rfl) ⟨31514867, by rfl⟩ : syracuseStep 42019823 = 63029735) B63029735
theorem B31542317 : Blo 1727064 31542317 := bstep (se 3 (by rfl) ⟨5914184, by rfl⟩ : syracuseStep 31542317 = 11828369) B11828369
theorem B6401161 : Blo 1727064 6401161 := bstep (se 2 (by rfl) ⟨2400435, by rfl⟩ : syracuseStep 6401161 = 4800871) B4800871
theorem B2592047 : Blo 1727064 2592047 := bstep (se 1 (by rfl) ⟨1944035, by rfl⟩ : syracuseStep 2592047 = 3888071) B3888071
theorem B8744273 : Blo 1727064 8744273 := bstep (se 2 (by rfl) ⟨3279102, by rfl⟩ : syracuseStep 8744273 = 6558205) B6558205
theorem B2592155 : Blo 1727064 2592155 := bstep (se 1 (by rfl) ⟨1944116, by rfl⟩ : syracuseStep 2592155 = 3888233) B3888233
theorem B2592233 : Blo 1727064 2592233 := bstep (se 2 (by rfl) ⟨972087, by rfl⟩ : syracuseStep 2592233 = 1944175) B1944175
theorem B2592287 : Blo 1727064 2592287 := bstep (se 1 (by rfl) ⟨1944215, by rfl⟩ : syracuseStep 2592287 = 3888431) B3888431
theorem B2592521 : Blo 1727064 2592521 := bstep (se 2 (by rfl) ⟨972195, by rfl⟩ : syracuseStep 2592521 = 1944391) B1944391
theorem B2592575 : Blo 1727064 2592575 := bstep (se 1 (by rfl) ⟨1944431, by rfl⟩ : syracuseStep 2592575 = 3888863) B3888863
theorem B12455855 : Blo 1727064 12455855 := bstep (se 1 (by rfl) ⟨9341891, by rfl⟩ : syracuseStep 12455855 = 18683783) B18683783
theorem B2592815 : Blo 1727064 2592815 := bstep (se 1 (by rfl) ⟨1944611, by rfl⟩ : syracuseStep 2592815 = 3889223) B3889223
theorem B14012605 : Blo 1727064 14012605 := bstep (se 3 (by rfl) ⟨2627363, by rfl⟩ : syracuseStep 14012605 = 5254727) B5254727
theorem B5829407 : Blo 1727064 5829407 := bstep (se 1 (by rfl) ⟨4372055, by rfl⟩ : syracuseStep 5829407 = 8744111) B8744111
theorem B3281791 : Blo 1727064 3281791 := bstep (se 1 (by rfl) ⟨2461343, by rfl⟩ : syracuseStep 3281791 = 4922687) B4922687
theorem B23966783 : Blo 1727064 23966783 := bstep (se 1 (by rfl) ⟨17975087, by rfl⟩ : syracuseStep 23966783 = 35950175) B35950175
theorem B3888359 : Blo 1727064 3888359 := bstep (se 1 (by rfl) ⟨2916269, by rfl⟩ : syracuseStep 3888359 = 5832539) B5832539
theorem B1228035491 : Blo 1727064 1228035491 := bstep (se 1 (by rfl) ⟨921026618, by rfl⟩ : syracuseStep 1228035491 = 1842053237) B1842053237
theorem B3282383 : Blo 1727064 3282383 := bstep (se 1 (by rfl) ⟨2461787, by rfl⟩ : syracuseStep 3282383 = 4923575) B4923575
theorem B5830217 : Blo 1727064 5830217 := bstep (se 2 (by rfl) ⟨2186331, by rfl⟩ : syracuseStep 5830217 = 4372663) B4372663
theorem B6313555 : Blo 1727064 6313555 := bstep (se 1 (by rfl) ⟨4735166, by rfl⟩ : syracuseStep 6313555 = 9470333) B9470333
theorem B3888935 : Blo 1727064 3888935 := bstep (se 1 (by rfl) ⟨2916701, by rfl⟩ : syracuseStep 3888935 = 5833403) B5833403
theorem B9844577 : Blo 1727064 9844577 := bstep (se 2 (by rfl) ⟨3691716, by rfl⟩ : syracuseStep 9844577 = 7383433) B7383433
theorem B12449771 : Blo 1727064 12449771 := bstep (se 1 (by rfl) ⟨9337328, by rfl⟩ : syracuseStep 12449771 = 18674657) B18674657
theorem B5830703 : Blo 1727064 5830703 := bstep (se 1 (by rfl) ⟨4373027, by rfl⟩ : syracuseStep 5830703 = 8746055) B8746055
theorem B227334269 : Blo 1727064 227334269 := bstep (se 3 (by rfl) ⟨42625175, by rfl⟩ : syracuseStep 227334269 = 85250351) B85250351
theorem B56785175 : Blo 1727064 56785175 := bstep (se 1 (by rfl) ⟨42588881, by rfl⟩ : syracuseStep 56785175 = 85177763) B85177763
theorem B2914663 : Blo 1727064 2914663 := bstep (se 1 (by rfl) ⟨2185997, by rfl⟩ : syracuseStep 2914663 = 4371995) B4371995
theorem B18692471 : Blo 1727064 18692471 := bstep (se 1 (by rfl) ⟨14019353, by rfl⟩ : syracuseStep 18692471 = 28038707) B28038707
theorem B2914697 : Blo 1727064 2914697 := bstep (se 2 (by rfl) ⟨1093011, by rfl⟩ : syracuseStep 2914697 = 2186023) B2186023
theorem B215783909 : Blo 1727064 215783909 := bstep (se 4 (by rfl) ⟨20229741, by rfl⟩ : syracuseStep 215783909 = 40459483) B40459483
theorem B19675709 : Blo 1727064 19675709 := bstep (se 3 (by rfl) ⟨3689195, by rfl⟩ : syracuseStep 19675709 = 7378391) B7378391
theorem B1727079 : Blo 1727064 1727079 := bstep (se 1 (by rfl) ⟨1295309, by rfl⟩ : syracuseStep 1727079 = 2590619) B2590619
theorem B1727103 : Blo 1727064 1727103 := bstep (se 1 (by rfl) ⟨1295327, by rfl⟩ : syracuseStep 1727103 = 2590655) B2590655
theorem B4151999 : Blo 1727064 4151999 := bstep (se 1 (by rfl) ⟨3113999, by rfl⟩ : syracuseStep 4151999 = 6227999) B6227999
theorem B3889889 : Blo 1727064 3889889 := bstep (se 2 (by rfl) ⟨1458708, by rfl⟩ : syracuseStep 3889889 = 2917417) B2917417
theorem B2915129 : Blo 1727064 2915129 := bstep (se 2 (by rfl) ⟨1093173, by rfl⟩ : syracuseStep 2915129 = 2186347) B2186347
theorem B2915311 : Blo 1727064 2915311 := bstep (se 1 (by rfl) ⟨2186483, by rfl⟩ : syracuseStep 2915311 = 4372967) B4372967
theorem B5831675 : Blo 1727064 5831675 := bstep (se 1 (by rfl) ⟨4373756, by rfl⟩ : syracuseStep 5831675 = 8747513) B8747513
theorem B1727519 : Blo 1727064 1727519 := bstep (se 1 (by rfl) ⟨1295639, by rfl⟩ : syracuseStep 1727519 = 2591279) B2591279
theorem B3890267 : Blo 1727064 3890267 := bstep (se 1 (by rfl) ⟨2917700, by rfl⟩ : syracuseStep 3890267 = 5835401) B5835401
theorem B1727599 : Blo 1727064 1727599 := bstep (se 1 (by rfl) ⟨1295699, by rfl⟩ : syracuseStep 1727599 = 2591399) B2591399
theorem B1727643 : Blo 1727064 1727643 := bstep (se 1 (by rfl) ⟨1295732, by rfl⟩ : syracuseStep 1727643 = 2591465) B2591465
theorem B1727647 : Blo 1727064 1727647 := bstep (se 1 (by rfl) ⟨1295735, by rfl⟩ : syracuseStep 1727647 = 2591471) B2591471
theorem B1727679 : Blo 1727064 1727679 := bstep (se 1 (by rfl) ⟨1295759, by rfl⟩ : syracuseStep 1727679 = 2591519) B2591519
theorem B47291687 : Blo 1727064 47291687 := bstep (se 1 (by rfl) ⟨35468765, by rfl⟩ : syracuseStep 47291687 = 70937531) B70937531
theorem B7380305 : Blo 1727064 7380305 := bstep (se 2 (by rfl) ⟨2767614, by rfl⟩ : syracuseStep 7380305 = 5535229) B5535229
theorem B22453595 : Blo 1727064 22453595 := bstep (se 1 (by rfl) ⟨16840196, by rfl⟩ : syracuseStep 22453595 = 33680393) B33680393
theorem B1727899 : Blo 1727064 1727899 := bstep (se 1 (by rfl) ⟨1295924, by rfl⟩ : syracuseStep 1727899 = 2591849) B2591849
theorem B1727983 : Blo 1727064 1727983 := bstep (se 1 (by rfl) ⟨1295987, by rfl⟩ : syracuseStep 1727983 = 2591975) B2591975
theorem B1728319 : Blo 1727064 1728319 := bstep (se 1 (by rfl) ⟨1296239, by rfl⟩ : syracuseStep 1728319 = 2592479) B2592479
theorem B9346927 : Blo 1727064 9346927 := bstep (se 1 (by rfl) ⟨7010195, by rfl⟩ : syracuseStep 9346927 = 14020391) B14020391
theorem B1728507 : Blo 1727064 1728507 := bstep (se 1 (by rfl) ⟨1296380, by rfl⟩ : syracuseStep 1728507 = 2592761) B2592761
theorem B1728543 : Blo 1727064 1728543 := bstep (se 1 (by rfl) ⟨1296407, by rfl⟩ : syracuseStep 1728543 = 2592815) B2592815
theorem B2916425 : Blo 1727064 2916425 := bstep (se 2 (by rfl) ⟨1093659, by rfl⟩ : syracuseStep 2916425 = 2187319) B2187319
theorem B8749295 : Blo 1727064 8749295 := bstep (se 1 (by rfl) ⟨6561971, by rfl⟩ : syracuseStep 8749295 = 13123943) B13123943
theorem B112067621 : Blo 1727064 112067621 := bstep (se 4 (by rfl) ⟨10506339, by rfl⟩ : syracuseStep 112067621 = 21012679) B21012679
theorem B2917471 : Blo 1727064 2917471 := bstep (se 1 (by rfl) ⟨2188103, by rfl⟩ : syracuseStep 2917471 = 4376207) B4376207
theorem B4375721 : Blo 1727064 4375721 := bstep (se 2 (by rfl) ⟨1640895, by rfl⟩ : syracuseStep 4375721 = 3281791) B3281791
theorem B2917559 : Blo 1727064 2917559 := bstep (se 1 (by rfl) ⟨2188169, by rfl⟩ : syracuseStep 2917559 = 4376339) B4376339
theorem B6563051 : Blo 1727064 6563051 := bstep (se 1 (by rfl) ⟨4922288, by rfl⟩ : syracuseStep 6563051 = 9844577) B9844577
theorem B2917687 : Blo 1727064 2917687 := bstep (se 1 (by rfl) ⟨2188265, by rfl⟩ : syracuseStep 2917687 = 4376531) B4376531
theorem B8299847 : Blo 1727064 8299847 := bstep (se 1 (by rfl) ⟨6224885, by rfl⟩ : syracuseStep 8299847 = 12449771) B12449771
theorem B37856783 : Blo 1727064 37856783 := bstep (se 1 (by rfl) ⟨28392587, by rfl⟩ : syracuseStep 37856783 = 56785175) B56785175
theorem B12461647 : Blo 1727064 12461647 := bstep (se 1 (by rfl) ⟨9346235, by rfl⟩ : syracuseStep 12461647 = 18692471) B18692471
theorem B1943131 : Blo 1727064 1943131 := bstep (se 1 (by rfl) ⟨1457348, by rfl⟩ : syracuseStep 1943131 = 2914697) B2914697
theorem B13117139 : Blo 1727064 13117139 := bstep (se 1 (by rfl) ⟨9837854, by rfl⟩ : syracuseStep 13117139 = 19675709) B19675709
theorem B1943419 : Blo 1727064 1943419 := bstep (se 1 (by rfl) ⟨1457564, by rfl⟩ : syracuseStep 1943419 = 2915129) B2915129
theorem B14969063 : Blo 1727064 14969063 := bstep (se 1 (by rfl) ⟨11226797, by rfl⟩ : syracuseStep 14969063 = 22453595) B22453595
theorem B12462569 : Blo 1727064 12462569 := bstep (se 2 (by rfl) ⟨4673463, by rfl⟩ : syracuseStep 12462569 = 9346927) B9346927
theorem B2591273 : Blo 1727064 2591273 := bstep (se 2 (by rfl) ⟨971727, by rfl⟩ : syracuseStep 2591273 = 1943455) B1943455
theorem B4918313 : Blo 1727064 4918313 := bstep (se 2 (by rfl) ⟨1844367, by rfl⟩ : syracuseStep 4918313 = 3688735) B3688735
theorem B3886217 : Blo 1727064 3886217 := bstep (se 2 (by rfl) ⟨1457331, by rfl⟩ : syracuseStep 3886217 = 2914663) B2914663
theorem B3886271 : Blo 1727064 3886271 := bstep (se 1 (by rfl) ⟨2914703, by rfl⟩ : syracuseStep 3886271 = 5829407) B5829407
theorem B15977855 : Blo 1727064 15977855 := bstep (se 1 (by rfl) ⟨11983391, by rfl⟩ : syracuseStep 15977855 = 23966783) B23966783
theorem B2592239 : Blo 1727064 2592239 := bstep (se 1 (by rfl) ⟨1944179, by rfl⟩ : syracuseStep 2592239 = 3888359) B3888359
theorem B2592425 : Blo 1727064 2592425 := bstep (se 2 (by rfl) ⟨972159, by rfl⟩ : syracuseStep 2592425 = 1944319) B1944319
theorem B3886811 : Blo 1727064 3886811 := bstep (se 1 (by rfl) ⟨2915108, by rfl⟩ : syracuseStep 3886811 = 5830217) B5830217
theorem B2592623 : Blo 1727064 2592623 := bstep (se 1 (by rfl) ⟨1944467, by rfl⟩ : syracuseStep 2592623 = 3888935) B3888935
theorem B10514299 : Blo 1727064 10514299 := bstep (se 1 (by rfl) ⟨7885724, by rfl⟩ : syracuseStep 10514299 = 15771449) B15771449
theorem B8753021 : Blo 1727064 8753021 := bstep (se 3 (by rfl) ⟨1641191, by rfl⟩ : syracuseStep 8753021 = 3282383) B3282383
theorem B3887081 : Blo 1727064 3887081 := bstep (se 2 (by rfl) ⟨1457655, by rfl⟩ : syracuseStep 3887081 = 2915311) B2915311
theorem B3887135 : Blo 1727064 3887135 := bstep (se 1 (by rfl) ⟨2915351, by rfl⟩ : syracuseStep 3887135 = 5830703) B5830703
theorem B151556179 : Blo 1727064 151556179 := bstep (se 1 (by rfl) ⟨113667134, by rfl⟩ : syracuseStep 151556179 = 227334269) B227334269
theorem B143855939 : Blo 1727064 143855939 := bstep (se 1 (by rfl) ⟨107891954, by rfl⟩ : syracuseStep 143855939 = 215783909) B215783909
theorem B2593259 : Blo 1727064 2593259 := bstep (se 1 (by rfl) ⟨1944944, by rfl⟩ : syracuseStep 2593259 = 3889889) B3889889
theorem B11071997 : Blo 1727064 11071997 := bstep (se 3 (by rfl) ⟨2075999, by rfl⟩ : syracuseStep 11071997 = 4151999) B4151999
theorem B28013215 : Blo 1727064 28013215 := bstep (se 1 (by rfl) ⟨21009911, by rfl⟩ : syracuseStep 28013215 = 42019823) B42019823
theorem B3887783 : Blo 1727064 3887783 := bstep (se 1 (by rfl) ⟨2915837, by rfl⟩ : syracuseStep 3887783 = 5831675) B5831675
theorem B2593511 : Blo 1727064 2593511 := bstep (se 1 (by rfl) ⟨1945133, by rfl⟩ : syracuseStep 2593511 = 3890267) B3890267
theorem B8418073 : Blo 1727064 8418073 := bstep (se 2 (by rfl) ⟨3156777, by rfl⟩ : syracuseStep 8418073 = 6313555) B6313555
theorem B31527791 : Blo 1727064 31527791 := bstep (se 1 (by rfl) ⟨23645843, by rfl⟩ : syracuseStep 31527791 = 47291687) B47291687
theorem B5829515 : Blo 1727064 5829515 := bstep (se 1 (by rfl) ⟨4372136, by rfl⟩ : syracuseStep 5829515 = 8744273) B8744273
theorem B4920203 : Blo 1727064 4920203 := bstep (se 1 (by rfl) ⟨3690152, by rfl⟩ : syracuseStep 4920203 = 7380305) B7380305
theorem B8303903 : Blo 1727064 8303903 := bstep (se 1 (by rfl) ⟨6227927, by rfl⟩ : syracuseStep 8303903 = 12455855) B12455855
theorem B18683473 : Blo 1727064 18683473 := bstep (se 2 (by rfl) ⟨7006302, by rfl⟩ : syracuseStep 18683473 = 14012605) B14012605
theorem B3888809 : Blo 1727064 3888809 := bstep (se 2 (by rfl) ⟨1458303, by rfl⟩ : syracuseStep 3888809 = 2916607) B2916607
theorem B37361411 : Blo 1727064 37361411 := bstep (se 1 (by rfl) ⟨28021058, by rfl⟩ : syracuseStep 37361411 = 56042117) B56042117
theorem B13121513 : Blo 1727064 13121513 := bstep (se 2 (by rfl) ⟨4920567, by rfl⟩ : syracuseStep 13121513 = 9841135) B9841135
theorem B818690327 : Blo 1727064 818690327 := bstep (se 1 (by rfl) ⟨614017745, by rfl⟩ : syracuseStep 818690327 = 1228035491) B1228035491
theorem B3889511 : Blo 1727064 3889511 := bstep (se 1 (by rfl) ⟨2917133, by rfl⟩ : syracuseStep 3889511 = 5834267) B5834267
theorem B1727131 : Blo 1727064 1727131 := bstep (se 1 (by rfl) ⟨1295348, by rfl⟩ : syracuseStep 1727131 = 2590697) B2590697
theorem B9345719 : Blo 1727064 9345719 := bstep (se 1 (by rfl) ⟨7009289, by rfl⟩ : syracuseStep 9345719 = 14018579) B14018579
theorem B8534881 : Blo 1727064 8534881 := bstep (se 2 (by rfl) ⟨3200580, by rfl⟩ : syracuseStep 8534881 = 6401161) B6401161
theorem B12458879 : Blo 1727064 12458879 := bstep (se 1 (by rfl) ⟨9344159, by rfl⟩ : syracuseStep 12458879 = 18688319) B18688319
theorem B3890087 : Blo 1727064 3890087 := bstep (se 1 (by rfl) ⟨2917565, by rfl⟩ : syracuseStep 3890087 = 5835131) B5835131
theorem B1727423 : Blo 1727064 1727423 := bstep (se 1 (by rfl) ⟨1295567, by rfl⟩ : syracuseStep 1727423 = 2591135) B2591135
theorem B1727455 : Blo 1727064 1727455 := bstep (se 1 (by rfl) ⟨1295591, by rfl⟩ : syracuseStep 1727455 = 2591183) B2591183
theorem B5610491 : Blo 1727064 5610491 := bstep (se 1 (by rfl) ⟨4207868, by rfl⟩ : syracuseStep 5610491 = 8415737) B8415737
theorem B19684457 : Blo 1727064 19684457 := bstep (se 2 (by rfl) ⟨7381671, by rfl⟩ : syracuseStep 19684457 = 14763343) B14763343
theorem B1727655 : Blo 1727064 1727655 := bstep (se 1 (by rfl) ⟨1295741, by rfl⟩ : syracuseStep 1727655 = 2591483) B2591483
theorem B1727791 : Blo 1727064 1727791 := bstep (se 1 (by rfl) ⟨1295843, by rfl⟩ : syracuseStep 1727791 = 2591687) B2591687
theorem B21028211 : Blo 1727064 21028211 := bstep (se 1 (by rfl) ⟨15771158, by rfl⟩ : syracuseStep 21028211 = 31542317) B31542317
theorem B1728031 : Blo 1727064 1728031 := bstep (se 1 (by rfl) ⟨1296023, by rfl⟩ : syracuseStep 1728031 = 2592047) B2592047
theorem B1728103 : Blo 1727064 1728103 := bstep (se 1 (by rfl) ⟨1296077, by rfl⟩ : syracuseStep 1728103 = 2592155) B2592155
theorem B1728155 : Blo 1727064 1728155 := bstep (se 1 (by rfl) ⟨1296116, by rfl⟩ : syracuseStep 1728155 = 2592233) B2592233
theorem B31547045 : Blo 1727064 31547045 := bstep (se 4 (by rfl) ⟨2957535, by rfl⟩ : syracuseStep 31547045 = 5915071) B5915071
theorem B1728191 : Blo 1727064 1728191 := bstep (se 1 (by rfl) ⟨1296143, by rfl⟩ : syracuseStep 1728191 = 2592287) B2592287
theorem B1728347 : Blo 1727064 1728347 := bstep (se 1 (by rfl) ⟨1296260, by rfl⟩ : syracuseStep 1728347 = 2592521) B2592521
theorem B1728383 : Blo 1727064 1728383 := bstep (se 1 (by rfl) ⟨1296287, by rfl⟩ : syracuseStep 1728383 = 2592575) B2592575
theorem B5832863 : Blo 1727064 5832863 := bstep (se 1 (by rfl) ⟨4374647, by rfl⟩ : syracuseStep 5832863 = 8749295) B8749295
theorem B95903959 : Blo 1727064 95903959 := bstep (se 1 (by rfl) ⟨71927969, by rfl⟩ : syracuseStep 95903959 = 143855939) B143855939
theorem B1728839 : Blo 1727064 1728839 := bstep (se 1 (by rfl) ⟨1296629, by rfl⟩ : syracuseStep 1728839 = 2593259) B2593259
theorem B7381331 : Blo 1727064 7381331 := bstep (se 1 (by rfl) ⟨5535998, by rfl⟩ : syracuseStep 7381331 = 11071997) B11071997
theorem B1729007 : Blo 1727064 1729007 := bstep (se 1 (by rfl) ⟨1296755, by rfl⟩ : syracuseStep 1729007 = 2593511) B2593511
theorem B74711747 : Blo 1727064 74711747 := bstep (se 1 (by rfl) ⟨56033810, by rfl⟩ : syracuseStep 74711747 = 112067621) B112067621
theorem B2917147 : Blo 1727064 2917147 := bstep (se 1 (by rfl) ⟨2187860, by rfl⟩ : syracuseStep 2917147 = 4375721) B4375721
theorem B4375367 : Blo 1727064 4375367 := bstep (se 1 (by rfl) ⟨3281525, by rfl⟩ : syracuseStep 4375367 = 6563051) B6563051
theorem B42607613 : Blo 1727064 42607613 := bstep (se 3 (by rfl) ⟨7988927, by rfl⟩ : syracuseStep 42607613 = 15977855) B15977855
theorem B11224097 : Blo 1727064 11224097 := bstep (se 2 (by rfl) ⟨4209036, by rfl⟩ : syracuseStep 11224097 = 8418073) B8418073
theorem B11379841 : Blo 1727064 11379841 := bstep (se 2 (by rfl) ⟨4267440, by rfl⟩ : syracuseStep 11379841 = 8534881) B8534881
theorem B545793551 : Blo 1727064 545793551 := bstep (se 1 (by rfl) ⟨409345163, by rfl⟩ : syracuseStep 545793551 = 818690327) B818690327
theorem B8308379 : Blo 1727064 8308379 := bstep (se 1 (by rfl) ⟨6231284, by rfl⟩ : syracuseStep 8308379 = 12462569) B12462569
theorem B3278875 : Blo 1727064 3278875 := bstep (se 1 (by rfl) ⟨2459156, by rfl⟩ : syracuseStep 3278875 = 4918313) B4918313
theorem B2590811 : Blo 1727064 2590811 := bstep (se 1 (by rfl) ⟨1943108, by rfl⟩ : syracuseStep 2590811 = 3886217) B3886217
theorem B16615529 : Blo 1727064 16615529 := bstep (se 2 (by rfl) ⟨6230823, by rfl⟩ : syracuseStep 16615529 = 12461647) B12461647
theorem B2590841 : Blo 1727064 2590841 := bstep (se 2 (by rfl) ⟨971565, by rfl⟩ : syracuseStep 2590841 = 1943131) B1943131
theorem B2590847 : Blo 1727064 2590847 := bstep (se 1 (by rfl) ⟨1943135, by rfl⟩ : syracuseStep 2590847 = 3886271) B3886271
theorem B14018807 : Blo 1727064 14018807 := bstep (se 1 (by rfl) ⟨10514105, by rfl⟩ : syracuseStep 14018807 = 21028211) B21028211
theorem B21031363 : Blo 1727064 21031363 := bstep (se 1 (by rfl) ⟨15773522, by rfl⟩ : syracuseStep 21031363 = 31547045) B31547045
theorem B2591207 : Blo 1727064 2591207 := bstep (se 1 (by rfl) ⟨1943405, by rfl⟩ : syracuseStep 2591207 = 3886811) B3886811
theorem B2591225 : Blo 1727064 2591225 := bstep (se 2 (by rfl) ⟨971709, by rfl⟩ : syracuseStep 2591225 = 1943419) B1943419
theorem B14019065 : Blo 1727064 14019065 := bstep (se 2 (by rfl) ⟨5257149, by rfl⟩ : syracuseStep 14019065 = 10514299) B10514299
theorem B5835347 : Blo 1727064 5835347 := bstep (se 1 (by rfl) ⟨4376510, by rfl⟩ : syracuseStep 5835347 = 8753021) B8753021
theorem B2591387 : Blo 1727064 2591387 := bstep (se 1 (by rfl) ⟨1943540, by rfl⟩ : syracuseStep 2591387 = 3887081) B3887081
theorem B2591423 : Blo 1727064 2591423 := bstep (se 1 (by rfl) ⟨1943567, by rfl⟩ : syracuseStep 2591423 = 3887135) B3887135
theorem B1944283 : Blo 1727064 1944283 := bstep (se 1 (by rfl) ⟨1458212, by rfl⟩ : syracuseStep 1944283 = 2916425) B2916425
theorem B202074905 : Blo 1727064 202074905 := bstep (se 2 (by rfl) ⟨75778089, by rfl⟩ : syracuseStep 202074905 = 151556179) B151556179
theorem B2591855 : Blo 1727064 2591855 := bstep (se 1 (by rfl) ⟨1943891, by rfl⟩ : syracuseStep 2591855 = 3887783) B3887783
theorem B3886343 : Blo 1727064 3886343 := bstep (se 1 (by rfl) ⟨2914757, by rfl⟩ : syracuseStep 3886343 = 5829515) B5829515
theorem B1945039 : Blo 1727064 1945039 := bstep (se 1 (by rfl) ⟨1458779, by rfl⟩ : syracuseStep 1945039 = 2917559) B2917559
theorem B37350953 : Blo 1727064 37350953 := bstep (se 2 (by rfl) ⟨14006607, by rfl⟩ : syracuseStep 37350953 = 28013215) B28013215
theorem B5533231 : Blo 1727064 5533231 := bstep (se 1 (by rfl) ⟨4149923, by rfl⟩ : syracuseStep 5533231 = 8299847) B8299847
theorem B2592539 : Blo 1727064 2592539 := bstep (se 1 (by rfl) ⟨1944404, by rfl⟩ : syracuseStep 2592539 = 3888809) B3888809
theorem B8744759 : Blo 1727064 8744759 := bstep (se 1 (by rfl) ⟨6558569, by rfl⟩ : syracuseStep 8744759 = 13117139) B13117139
theorem B24907607 : Blo 1727064 24907607 := bstep (se 1 (by rfl) ⟨18680705, by rfl⟩ : syracuseStep 24907607 = 37361411) B37361411
theorem B2593007 : Blo 1727064 2593007 := bstep (se 1 (by rfl) ⟨1944755, by rfl⟩ : syracuseStep 2593007 = 3889511) B3889511
theorem B6230479 : Blo 1727064 6230479 := bstep (se 1 (by rfl) ⟨4672859, by rfl⟩ : syracuseStep 6230479 = 9345719) B9345719
theorem B2593391 : Blo 1727064 2593391 := bstep (se 1 (by rfl) ⟨1945043, by rfl⟩ : syracuseStep 2593391 = 3890087) B3890087
theorem B3740327 : Blo 1727064 3740327 := bstep (se 1 (by rfl) ⟨2805245, by rfl⟩ : syracuseStep 3740327 = 5610491) B5610491
theorem B13120541 : Blo 1727064 13120541 := bstep (se 3 (by rfl) ⟨2460101, by rfl⟩ : syracuseStep 13120541 = 4920203) B4920203
theorem B21018527 : Blo 1727064 21018527 := bstep (se 1 (by rfl) ⟨15763895, by rfl⟩ : syracuseStep 21018527 = 31527791) B31527791
theorem B39917501 : Blo 1727064 39917501 := bstep (se 3 (by rfl) ⟨7484531, by rfl⟩ : syracuseStep 39917501 = 14969063) B14969063
theorem B5535935 : Blo 1727064 5535935 := bstep (se 1 (by rfl) ⟨4151951, by rfl⟩ : syracuseStep 5535935 = 8303903) B8303903
theorem B25237855 : Blo 1727064 25237855 := bstep (se 1 (by rfl) ⟨18928391, by rfl⟩ : syracuseStep 25237855 = 37856783) B37856783
theorem B8747675 : Blo 1727064 8747675 := bstep (se 1 (by rfl) ⟨6560756, by rfl⟩ : syracuseStep 8747675 = 13121513) B13121513
theorem B3889961 : Blo 1727064 3889961 := bstep (se 2 (by rfl) ⟨1458735, by rfl⟩ : syracuseStep 3889961 = 2917471) B2917471
theorem B1727515 : Blo 1727064 1727515 := bstep (se 1 (by rfl) ⟨1295636, by rfl⟩ : syracuseStep 1727515 = 2591273) B2591273
theorem B3890249 : Blo 1727064 3890249 := bstep (se 2 (by rfl) ⟨1458843, by rfl⟩ : syracuseStep 3890249 = 2917687) B2917687
theorem B8305919 : Blo 1727064 8305919 := bstep (se 1 (by rfl) ⟨6229439, by rfl⟩ : syracuseStep 8305919 = 12458879) B12458879
theorem B13122971 : Blo 1727064 13122971 := bstep (se 1 (by rfl) ⟨9842228, by rfl⟩ : syracuseStep 13122971 = 19684457) B19684457
theorem B24911297 : Blo 1727064 24911297 := bstep (se 2 (by rfl) ⟨9341736, by rfl⟩ : syracuseStep 24911297 = 18683473) B18683473
theorem B1728159 : Blo 1727064 1728159 := bstep (se 1 (by rfl) ⟨1296119, by rfl⟩ : syracuseStep 1728159 = 2592239) B2592239
theorem B1728283 : Blo 1727064 1728283 := bstep (se 1 (by rfl) ⟨1296212, by rfl⟩ : syracuseStep 1728283 = 2592425) B2592425
theorem B1728415 : Blo 1727064 1728415 := bstep (se 1 (by rfl) ⟨1296311, by rfl⟩ : syracuseStep 1728415 = 2592623) B2592623
theorem B1728671 : Blo 1727064 1728671 := bstep (se 1 (by rfl) ⟨1296503, by rfl⟩ : syracuseStep 1728671 = 2593007) B2593007
theorem B1728927 : Blo 1727064 1728927 := bstep (se 1 (by rfl) ⟨1296695, by rfl⟩ : syracuseStep 1728927 = 2593391) B2593391
theorem B49807831 : Blo 1727064 49807831 := bstep (se 1 (by rfl) ⟨37355873, by rfl⟩ : syracuseStep 49807831 = 74711747) B74711747
theorem B2916911 : Blo 1727064 2916911 := bstep (se 1 (by rfl) ⟨2187683, by rfl⟩ : syracuseStep 2916911 = 4375367) B4375367
theorem B28041817 : Blo 1727064 28041817 := bstep (se 2 (by rfl) ⟨10515681, by rfl⟩ : syracuseStep 28041817 = 21031363) B21031363
theorem B8307305 : Blo 1727064 8307305 := bstep (se 2 (by rfl) ⟨3115239, by rfl⟩ : syracuseStep 8307305 = 6230479) B6230479
theorem B11077019 : Blo 1727064 11077019 := bstep (se 1 (by rfl) ⟨8307764, by rfl⟩ : syracuseStep 11077019 = 16615529) B16615529
theorem B2590895 : Blo 1727064 2590895 := bstep (se 1 (by rfl) ⟨1943171, by rfl⟩ : syracuseStep 2590895 = 3886343) B3886343
theorem B16607531 : Blo 1727064 16607531 := bstep (se 1 (by rfl) ⟨12455648, by rfl⟩ : syracuseStep 16607531 = 24911297) B24911297
theorem B127871945 : Blo 1727064 127871945 := bstep (se 2 (by rfl) ⟨47951979, by rfl⟩ : syracuseStep 127871945 = 95903959) B95903959
theorem B2493551 : Blo 1727064 2493551 := bstep (se 1 (by rfl) ⟨1870163, by rfl⟩ : syracuseStep 2493551 = 3740327) B3740327
theorem B28405075 : Blo 1727064 28405075 := bstep (se 1 (by rfl) ⟨21303806, by rfl⟩ : syracuseStep 28405075 = 42607613) B42607613
theorem B7482731 : Blo 1727064 7482731 := bstep (se 1 (by rfl) ⟨5612048, by rfl⟩ : syracuseStep 7482731 = 11224097) B11224097
theorem B2592377 : Blo 1727064 2592377 := bstep (se 2 (by rfl) ⟨972141, by rfl⟩ : syracuseStep 2592377 = 1944283) B1944283
theorem B14012351 : Blo 1727064 14012351 := bstep (se 1 (by rfl) ⟨10509263, by rfl⟩ : syracuseStep 14012351 = 21018527) B21018527
theorem B26611667 : Blo 1727064 26611667 := bstep (se 1 (by rfl) ⟨19958750, by rfl⟩ : syracuseStep 26611667 = 39917501) B39917501
theorem B3690623 : Blo 1727064 3690623 := bstep (se 1 (by rfl) ⟨2767967, by rfl⟩ : syracuseStep 3690623 = 5535935) B5535935
theorem B22155677 : Blo 1727064 22155677 := bstep (se 3 (by rfl) ⟨4154189, by rfl⟩ : syracuseStep 22155677 = 8308379) B8308379
theorem B2593307 : Blo 1727064 2593307 := bstep (se 1 (by rfl) ⟨1944980, by rfl⟩ : syracuseStep 2593307 = 3889961) B3889961
theorem B2593385 : Blo 1727064 2593385 := bstep (se 2 (by rfl) ⟨972519, by rfl⟩ : syracuseStep 2593385 = 1945039) B1945039
theorem B2593499 : Blo 1727064 2593499 := bstep (se 1 (by rfl) ⟨1945124, by rfl⟩ : syracuseStep 2593499 = 3890249) B3890249
theorem B7377641 : Blo 1727064 7377641 := bstep (se 2 (by rfl) ⟨2766615, by rfl⟩ : syracuseStep 7377641 = 5533231) B5533231
theorem B24900635 : Blo 1727064 24900635 := bstep (se 1 (by rfl) ⟨18675476, by rfl⟩ : syracuseStep 24900635 = 37350953) B37350953
theorem B5829839 : Blo 1727064 5829839 := bstep (se 1 (by rfl) ⟨4372379, by rfl⟩ : syracuseStep 5829839 = 8744759) B8744759
theorem B4371833 : Blo 1727064 4371833 := bstep (se 2 (by rfl) ⟨1639437, by rfl⟩ : syracuseStep 4371833 = 3278875) B3278875
theorem B3888575 : Blo 1727064 3888575 := bstep (se 1 (by rfl) ⟨2916431, by rfl⟩ : syracuseStep 3888575 = 5832863) B5832863
theorem B4920887 : Blo 1727064 4920887 := bstep (se 1 (by rfl) ⟨3690665, by rfl⟩ : syracuseStep 4920887 = 7381331) B7381331
theorem B33650473 : Blo 1727064 33650473 := bstep (se 2 (by rfl) ⟨12618927, by rfl⟩ : syracuseStep 33650473 = 25237855) B25237855
theorem B60692485 : Blo 1727064 60692485 := bstep (se 4 (by rfl) ⟨5689920, by rfl⟩ : syracuseStep 60692485 = 11379841) B11379841
theorem B8747027 : Blo 1727064 8747027 := bstep (se 1 (by rfl) ⟨6560270, by rfl⟩ : syracuseStep 8747027 = 13120541) B13120541
theorem B363862367 : Blo 1727064 363862367 := bstep (se 1 (by rfl) ⟨272896775, by rfl⟩ : syracuseStep 363862367 = 545793551) B545793551
theorem B3889529 : Blo 1727064 3889529 := bstep (se 2 (by rfl) ⟨1458573, by rfl⟩ : syracuseStep 3889529 = 2917147) B2917147
theorem B1727207 : Blo 1727064 1727207 := bstep (se 1 (by rfl) ⟨1295405, by rfl⟩ : syracuseStep 1727207 = 2590811) B2590811
theorem B1727227 : Blo 1727064 1727227 := bstep (se 1 (by rfl) ⟨1295420, by rfl⟩ : syracuseStep 1727227 = 2590841) B2590841
theorem B1727231 : Blo 1727064 1727231 := bstep (se 1 (by rfl) ⟨1295423, by rfl⟩ : syracuseStep 1727231 = 2590847) B2590847
theorem B9345871 : Blo 1727064 9345871 := bstep (se 1 (by rfl) ⟨7009403, by rfl⟩ : syracuseStep 9345871 = 14018807) B14018807
theorem B1727471 : Blo 1727064 1727471 := bstep (se 1 (by rfl) ⟨1295603, by rfl⟩ : syracuseStep 1727471 = 2591207) B2591207
theorem B1727483 : Blo 1727064 1727483 := bstep (se 1 (by rfl) ⟨1295612, by rfl⟩ : syracuseStep 1727483 = 2591225) B2591225
theorem B9346043 : Blo 1727064 9346043 := bstep (se 1 (by rfl) ⟨7009532, by rfl⟩ : syracuseStep 9346043 = 14019065) B14019065
theorem B3890231 : Blo 1727064 3890231 := bstep (se 1 (by rfl) ⟨2917673, by rfl⟩ : syracuseStep 3890231 = 5835347) B5835347
theorem B1727591 : Blo 1727064 1727591 := bstep (se 1 (by rfl) ⟨1295693, by rfl⟩ : syracuseStep 1727591 = 2591387) B2591387
theorem B5831783 : Blo 1727064 5831783 := bstep (se 1 (by rfl) ⟨4373837, by rfl⟩ : syracuseStep 5831783 = 8747675) B8747675
theorem B1727615 : Blo 1727064 1727615 := bstep (se 1 (by rfl) ⟨1295711, by rfl⟩ : syracuseStep 1727615 = 2591423) B2591423
theorem B134716603 : Blo 1727064 134716603 := bstep (se 1 (by rfl) ⟨101037452, by rfl⟩ : syracuseStep 134716603 = 202074905) B202074905
theorem B1727903 : Blo 1727064 1727903 := bstep (se 1 (by rfl) ⟨1295927, by rfl⟩ : syracuseStep 1727903 = 2591855) B2591855
theorem B5537279 : Blo 1727064 5537279 := bstep (se 1 (by rfl) ⟨4152959, by rfl⟩ : syracuseStep 5537279 = 8305919) B8305919
theorem B8748647 : Blo 1727064 8748647 := bstep (se 1 (by rfl) ⟨6561485, by rfl⟩ : syracuseStep 8748647 = 13122971) B13122971
theorem B1728359 : Blo 1727064 1728359 := bstep (se 1 (by rfl) ⟨1296269, by rfl⟩ : syracuseStep 1728359 = 2592539) B2592539
theorem B16605071 : Blo 1727064 16605071 := bstep (se 1 (by rfl) ⟨12453803, by rfl⟩ : syracuseStep 16605071 = 24907607) B24907607
theorem B14770451 : Blo 1727064 14770451 := bstep (se 1 (by rfl) ⟨11077838, by rfl⟩ : syracuseStep 14770451 = 22155677) B22155677
theorem B1728871 : Blo 1727064 1728871 := bstep (se 1 (by rfl) ⟨1296653, by rfl⟩ : syracuseStep 1728871 = 2593307) B2593307
theorem B5538203 : Blo 1727064 5538203 := bstep (se 1 (by rfl) ⟨4153652, by rfl⟩ : syracuseStep 5538203 = 8307305) B8307305
theorem B1728923 : Blo 1727064 1728923 := bstep (se 1 (by rfl) ⟨1296692, by rfl⟩ : syracuseStep 1728923 = 2593385) B2593385
theorem B1728999 : Blo 1727064 1728999 := bstep (se 1 (by rfl) ⟨1296749, by rfl⟩ : syracuseStep 1728999 = 2593499) B2593499
theorem B44286749 : Blo 1727064 44286749 := bstep (se 3 (by rfl) ⟨8303765, by rfl⟩ : syracuseStep 44286749 = 16607531) B16607531
theorem B37389089 : Blo 1727064 37389089 := bstep (se 2 (by rfl) ⟨14020908, by rfl⟩ : syracuseStep 37389089 = 28041817) B28041817
theorem B12461161 : Blo 1727064 12461161 := bstep (se 2 (by rfl) ⟨4672935, by rfl⟩ : syracuseStep 12461161 = 9345871) B9345871
theorem B242574911 : Blo 1727064 242574911 := bstep (se 1 (by rfl) ⟨181931183, by rfl⟩ : syracuseStep 242574911 = 363862367) B363862367
theorem B37873433 : Blo 1727064 37873433 := bstep (se 2 (by rfl) ⟨14202537, by rfl⟩ : syracuseStep 37873433 = 28405075) B28405075
theorem B85247963 : Blo 1727064 85247963 := bstep (se 1 (by rfl) ⟨63935972, by rfl⟩ : syracuseStep 85247963 = 127871945) B127871945
theorem B11070047 : Blo 1727064 11070047 := bstep (se 1 (by rfl) ⟨8302535, by rfl⟩ : syracuseStep 11070047 = 16605071) B16605071
theorem B9341567 : Blo 1727064 9341567 := bstep (se 1 (by rfl) ⟨7006175, by rfl⟩ : syracuseStep 9341567 = 14012351) B14012351
theorem B80923313 : Blo 1727064 80923313 := bstep (se 2 (by rfl) ⟨30346242, by rfl⟩ : syracuseStep 80923313 = 60692485) B60692485
theorem B9841661 : Blo 1727064 9841661 := bstep (se 3 (by rfl) ⟨1845311, by rfl⟩ : syracuseStep 9841661 = 3690623) B3690623
theorem B1944607 : Blo 1727064 1944607 := bstep (se 1 (by rfl) ⟨1458455, by rfl⟩ : syracuseStep 1944607 = 2916911) B2916911
theorem B4918427 : Blo 1727064 4918427 := bstep (se 1 (by rfl) ⟨3688820, by rfl⟩ : syracuseStep 4918427 = 7377641) B7377641
theorem B16600423 : Blo 1727064 16600423 := bstep (se 1 (by rfl) ⟨12450317, by rfl⟩ : syracuseStep 16600423 = 24900635) B24900635
theorem B3886559 : Blo 1727064 3886559 := bstep (se 1 (by rfl) ⟨2914919, by rfl⟩ : syracuseStep 3886559 = 5829839) B5829839
theorem B7384679 : Blo 1727064 7384679 := bstep (se 1 (by rfl) ⟨5538509, by rfl⟩ : syracuseStep 7384679 = 11077019) B11077019
theorem B2592383 : Blo 1727064 2592383 := bstep (se 1 (by rfl) ⟨1944287, by rfl⟩ : syracuseStep 2592383 = 3888575) B3888575
theorem B3280591 : Blo 1727064 3280591 := bstep (se 1 (by rfl) ⟨2460443, by rfl⟩ : syracuseStep 3280591 = 4920887) B4920887
theorem B14766077 : Blo 1727064 14766077 := bstep (se 3 (by rfl) ⟨2768639, by rfl⟩ : syracuseStep 14766077 = 5537279) B5537279
theorem B179622137 : Blo 1727064 179622137 := bstep (se 2 (by rfl) ⟨67358301, by rfl⟩ : syracuseStep 179622137 = 134716603) B134716603
theorem B2593019 : Blo 1727064 2593019 := bstep (se 1 (by rfl) ⟨1944764, by rfl⟩ : syracuseStep 2593019 = 3889529) B3889529
theorem B6230695 : Blo 1727064 6230695 := bstep (se 1 (by rfl) ⟨4673021, by rfl⟩ : syracuseStep 6230695 = 9346043) B9346043
theorem B2593487 : Blo 1727064 2593487 := bstep (se 1 (by rfl) ⟨1945115, by rfl⟩ : syracuseStep 2593487 = 3890231) B3890231
theorem B3887855 : Blo 1727064 3887855 := bstep (se 1 (by rfl) ⟨2915891, by rfl⟩ : syracuseStep 3887855 = 5831783) B5831783
theorem B17741111 : Blo 1727064 17741111 := bstep (se 1 (by rfl) ⟨13305833, by rfl⟩ : syracuseStep 17741111 = 26611667) B26611667
theorem B6649469 : Blo 1727064 6649469 := bstep (se 3 (by rfl) ⟨1246775, by rfl⟩ : syracuseStep 6649469 = 2493551) B2493551
theorem B66410441 : Blo 1727064 66410441 := bstep (se 2 (by rfl) ⟨24903915, by rfl⟩ : syracuseStep 66410441 = 49807831) B49807831
theorem B2914555 : Blo 1727064 2914555 := bstep (se 1 (by rfl) ⟨2185916, by rfl⟩ : syracuseStep 2914555 = 4371833) B4371833
theorem B19953949 : Blo 1727064 19953949 := bstep (se 3 (by rfl) ⟨3741365, by rfl⟩ : syracuseStep 19953949 = 7482731) B7482731
theorem B5831351 : Blo 1727064 5831351 := bstep (se 1 (by rfl) ⟨4373513, by rfl⟩ : syracuseStep 5831351 = 8747027) B8747027
theorem B1727263 : Blo 1727064 1727263 := bstep (se 1 (by rfl) ⟨1295447, by rfl⟩ : syracuseStep 1727263 = 2590895) B2590895
theorem B44867297 : Blo 1727064 44867297 := bstep (se 2 (by rfl) ⟨16825236, by rfl⟩ : syracuseStep 44867297 = 33650473) B33650473
theorem B5832431 : Blo 1727064 5832431 := bstep (se 1 (by rfl) ⟨4374323, by rfl⟩ : syracuseStep 5832431 = 8748647) B8748647
theorem B1728251 : Blo 1727064 1728251 := bstep (se 1 (by rfl) ⟨1296188, by rfl⟩ : syracuseStep 1728251 = 2592377) B2592377
theorem B1728679 : Blo 1727064 1728679 := bstep (se 1 (by rfl) ⟨1296509, by rfl⟩ : syracuseStep 1728679 = 2593019) B2593019
theorem B9846967 : Blo 1727064 9846967 := bstep (se 1 (by rfl) ⟨7385225, by rfl⟩ : syracuseStep 9846967 = 14770451) B14770451
theorem B1728991 : Blo 1727064 1728991 := bstep (se 1 (by rfl) ⟨1296743, by rfl⟩ : syracuseStep 1728991 = 2593487) B2593487
theorem B29524499 : Blo 1727064 29524499 := bstep (se 1 (by rfl) ⟨22143374, by rfl⟩ : syracuseStep 29524499 = 44286749) B44286749
theorem B47309629 : Blo 1727064 47309629 := bstep (se 3 (by rfl) ⟨8870555, by rfl⟩ : syracuseStep 47309629 = 17741111) B17741111
theorem B8307593 : Blo 1727064 8307593 := bstep (se 2 (by rfl) ⟨3115347, by rfl⟩ : syracuseStep 8307593 = 6230695) B6230695
theorem B4432979 : Blo 1727064 4432979 := bstep (se 1 (by rfl) ⟨3324734, by rfl⟩ : syracuseStep 4432979 = 6649469) B6649469
theorem B16614881 : Blo 1727064 16614881 := bstep (se 2 (by rfl) ⟨6230580, by rfl⟩ : syracuseStep 16614881 = 12461161) B12461161
theorem B6227711 : Blo 1727064 6227711 := bstep (se 1 (by rfl) ⟨4670783, by rfl⟩ : syracuseStep 6227711 = 9341567) B9341567
theorem B3278951 : Blo 1727064 3278951 := bstep (se 1 (by rfl) ⟨2459213, by rfl⟩ : syracuseStep 3278951 = 4918427) B4918427
theorem B2591039 : Blo 1727064 2591039 := bstep (se 1 (by rfl) ⟨1943279, by rfl⟩ : syracuseStep 2591039 = 3886559) B3886559
theorem B29911531 : Blo 1727064 29911531 := bstep (se 1 (by rfl) ⟨22433648, by rfl⟩ : syracuseStep 29911531 = 44867297) B44867297
theorem B3886073 : Blo 1727064 3886073 := bstep (se 2 (by rfl) ⟨1457277, by rfl⟩ : syracuseStep 3886073 = 2914555) B2914555
theorem B2591903 : Blo 1727064 2591903 := bstep (se 1 (by rfl) ⟨1943927, by rfl⟩ : syracuseStep 2591903 = 3887855) B3887855
theorem B44273627 : Blo 1727064 44273627 := bstep (se 1 (by rfl) ⟨33205220, by rfl⟩ : syracuseStep 44273627 = 66410441) B66410441
theorem B56831975 : Blo 1727064 56831975 := bstep (se 1 (by rfl) ⟨42623981, by rfl⟩ : syracuseStep 56831975 = 85247963) B85247963
theorem B2592809 : Blo 1727064 2592809 := bstep (se 2 (by rfl) ⟨972303, by rfl⟩ : syracuseStep 2592809 = 1944607) B1944607
theorem B29520125 : Blo 1727064 29520125 := bstep (se 3 (by rfl) ⟨5535023, by rfl⟩ : syracuseStep 29520125 = 11070047) B11070047
theorem B53948875 : Blo 1727064 53948875 := bstep (se 1 (by rfl) ⟨40461656, by rfl⟩ : syracuseStep 53948875 = 80923313) B80923313
theorem B3887567 : Blo 1727064 3887567 := bstep (se 1 (by rfl) ⟨2915675, by rfl⟩ : syracuseStep 3887567 = 5831351) B5831351
theorem B100995821 : Blo 1727064 100995821 := bstep (se 3 (by rfl) ⟨18936716, by rfl⟩ : syracuseStep 100995821 = 37873433) B37873433
theorem B3888287 : Blo 1727064 3888287 := bstep (se 1 (by rfl) ⟨2916215, by rfl⟩ : syracuseStep 3888287 = 5832431) B5832431
theorem B9844051 : Blo 1727064 9844051 := bstep (se 1 (by rfl) ⟨7383038, by rfl⟩ : syracuseStep 9844051 = 14766077) B14766077
theorem B119748091 : Blo 1727064 119748091 := bstep (se 1 (by rfl) ⟨89811068, by rfl⟩ : syracuseStep 119748091 = 179622137) B179622137
theorem B3692135 : Blo 1727064 3692135 := bstep (se 1 (by rfl) ⟨2769101, by rfl⟩ : syracuseStep 3692135 = 5538203) B5538203
theorem B26605265 : Blo 1727064 26605265 := bstep (se 2 (by rfl) ⟨9976974, by rfl⟩ : syracuseStep 26605265 = 19953949) B19953949
theorem B24926059 : Blo 1727064 24926059 := bstep (se 1 (by rfl) ⟨18694544, by rfl⟩ : syracuseStep 24926059 = 37389089) B37389089
theorem B161716607 : Blo 1727064 161716607 := bstep (se 1 (by rfl) ⟨121287455, by rfl⟩ : syracuseStep 161716607 = 242574911) B242574911
theorem B22133897 : Blo 1727064 22133897 := bstep (se 2 (by rfl) ⟨8300211, by rfl⟩ : syracuseStep 22133897 = 16600423) B16600423
theorem B6561107 : Blo 1727064 6561107 := bstep (se 1 (by rfl) ⟨4920830, by rfl⟩ : syracuseStep 6561107 = 9841661) B9841661
theorem B4374121 : Blo 1727064 4374121 := bstep (se 2 (by rfl) ⟨1640295, by rfl⟩ : syracuseStep 4374121 = 3280591) B3280591
theorem B4923119 : Blo 1727064 4923119 := bstep (se 1 (by rfl) ⟨3692339, by rfl⟩ : syracuseStep 4923119 = 7384679) B7384679
theorem B1728255 : Blo 1727064 1728255 := bstep (se 1 (by rfl) ⟨1296191, by rfl⟩ : syracuseStep 1728255 = 2592383) B2592383
theorem B1728539 : Blo 1727064 1728539 := bstep (se 1 (by rfl) ⟨1296404, by rfl⟩ : syracuseStep 1728539 = 2592809) B2592809
theorem B11821277 : Blo 1727064 11821277 := bstep (se 3 (by rfl) ⟨2216489, by rfl⟩ : syracuseStep 11821277 = 4432979) B4432979
theorem B67330547 : Blo 1727064 67330547 := bstep (se 1 (by rfl) ⟨50497910, by rfl⟩ : syracuseStep 67330547 = 100995821) B100995821
theorem B5538395 : Blo 1727064 5538395 := bstep (se 1 (by rfl) ⟨4153796, by rfl⟩ : syracuseStep 5538395 = 8307593) B8307593
theorem B11076587 : Blo 1727064 11076587 := bstep (se 1 (by rfl) ⟨8307440, by rfl⟩ : syracuseStep 11076587 = 16614881) B16614881
theorem B63079505 : Blo 1727064 63079505 := bstep (se 2 (by rfl) ⟨23654814, by rfl⟩ : syracuseStep 63079505 = 47309629) B47309629
theorem B13125401 : Blo 1727064 13125401 := bstep (se 2 (by rfl) ⟨4922025, by rfl⟩ : syracuseStep 13125401 = 9844051) B9844051
theorem B2590715 : Blo 1727064 2590715 := bstep (se 1 (by rfl) ⟨1943036, by rfl⟩ : syracuseStep 2590715 = 3886073) B3886073
theorem B159664121 : Blo 1727064 159664121 := bstep (se 2 (by rfl) ⟨59874045, by rfl⟩ : syracuseStep 159664121 = 119748091) B119748091
theorem B14755931 : Blo 1727064 14755931 := bstep (se 1 (by rfl) ⟨11066948, by rfl⟩ : syracuseStep 14755931 = 22133897) B22133897
theorem B283789493 : Blo 1727064 283789493 := bstep (se 5 (by rfl) ⟨13302632, by rfl⟩ : syracuseStep 283789493 = 26605265) B26605265
theorem B19680083 : Blo 1727064 19680083 := bstep (se 1 (by rfl) ⟨14760062, by rfl⟩ : syracuseStep 19680083 = 29520125) B29520125
theorem B2591711 : Blo 1727064 2591711 := bstep (se 1 (by rfl) ⟨1943783, by rfl⟩ : syracuseStep 2591711 = 3887567) B3887567
theorem B39882041 : Blo 1727064 39882041 := bstep (se 2 (by rfl) ⟨14955765, by rfl⟩ : syracuseStep 39882041 = 29911531) B29911531
theorem B2592191 : Blo 1727064 2592191 := bstep (se 1 (by rfl) ⟨1944143, by rfl⟩ : syracuseStep 2592191 = 3888287) B3888287
theorem B2461423 : Blo 1727064 2461423 := bstep (se 1 (by rfl) ⟨1846067, by rfl⟩ : syracuseStep 2461423 = 3692135) B3692135
theorem B107811071 : Blo 1727064 107811071 := bstep (se 1 (by rfl) ⟨80858303, by rfl⟩ : syracuseStep 107811071 = 161716607) B161716607
theorem B13128317 : Blo 1727064 13128317 := bstep (se 3 (by rfl) ⟨2461559, by rfl⟩ : syracuseStep 13128317 = 4923119) B4923119
theorem B13129289 : Blo 1727064 13129289 := bstep (se 2 (by rfl) ⟨4923483, by rfl⟩ : syracuseStep 13129289 = 9846967) B9846967
theorem B19682999 : Blo 1727064 19682999 := bstep (se 1 (by rfl) ⟨14762249, by rfl⟩ : syracuseStep 19682999 = 29524499) B29524499
theorem B71931833 : Blo 1727064 71931833 := bstep (se 2 (by rfl) ⟨26974437, by rfl⟩ : syracuseStep 71931833 = 53948875) B53948875
theorem B4151807 : Blo 1727064 4151807 := bstep (se 1 (by rfl) ⟨3113855, by rfl⟩ : syracuseStep 4151807 = 6227711) B6227711
theorem B2185967 : Blo 1727064 2185967 := bstep (se 1 (by rfl) ⟨1639475, by rfl⟩ : syracuseStep 2185967 = 3278951) B3278951
theorem B1727359 : Blo 1727064 1727359 := bstep (se 1 (by rfl) ⟨1295519, by rfl⟩ : syracuseStep 1727359 = 2591039) B2591039
theorem B1727935 : Blo 1727064 1727935 := bstep (se 1 (by rfl) ⟨1295951, by rfl⟩ : syracuseStep 1727935 = 2591903) B2591903
theorem B5832161 : Blo 1727064 5832161 := bstep (se 2 (by rfl) ⟨2187060, by rfl⟩ : syracuseStep 5832161 = 4374121) B4374121
theorem B4374071 : Blo 1727064 4374071 := bstep (se 1 (by rfl) ⟨3280553, by rfl⟩ : syracuseStep 4374071 = 6561107) B6561107
theorem B33234745 : Blo 1727064 33234745 := bstep (se 2 (by rfl) ⟨12463029, by rfl⟩ : syracuseStep 33234745 = 24926059) B24926059
theorem B29515751 : Blo 1727064 29515751 := bstep (se 1 (by rfl) ⟨22136813, by rfl⟩ : syracuseStep 29515751 = 44273627) B44273627
theorem B37887983 : Blo 1727064 37887983 := bstep (se 1 (by rfl) ⟨28415987, by rfl⟩ : syracuseStep 37887983 = 56831975) B56831975
theorem B7880851 : Blo 1727064 7880851 := bstep (se 1 (by rfl) ⟨5910638, by rfl⟩ : syracuseStep 7880851 = 11821277) B11821277
theorem B8750267 : Blo 1727064 8750267 := bstep (se 1 (by rfl) ⟨6562700, by rfl⟩ : syracuseStep 8750267 = 13125401) B13125401
theorem B44312993 : Blo 1727064 44312993 := bstep (se 2 (by rfl) ⟨16617372, by rfl⟩ : syracuseStep 44312993 = 33234745) B33234745
theorem B25258655 : Blo 1727064 25258655 := bstep (se 1 (by rfl) ⟨18943991, by rfl⟩ : syracuseStep 25258655 = 37887983) B37887983
theorem B44887031 : Blo 1727064 44887031 := bstep (se 1 (by rfl) ⟨33665273, by rfl⟩ : syracuseStep 44887031 = 67330547) B67330547
theorem B8752211 : Blo 1727064 8752211 := bstep (se 1 (by rfl) ⟨6564158, by rfl⟩ : syracuseStep 8752211 = 13128317) B13128317
theorem B7384391 : Blo 1727064 7384391 := bstep (se 1 (by rfl) ⟨5538293, by rfl⟩ : syracuseStep 7384391 = 11076587) B11076587
theorem B42053003 : Blo 1727064 42053003 := bstep (se 1 (by rfl) ⟨31539752, by rfl⟩ : syracuseStep 42053003 = 63079505) B63079505
theorem B8752859 : Blo 1727064 8752859 := bstep (se 1 (by rfl) ⟨6564644, by rfl⟩ : syracuseStep 8752859 = 13129289) B13129289
theorem B106442747 : Blo 1727064 106442747 := bstep (se 1 (by rfl) ⟨79832060, by rfl⟩ : syracuseStep 106442747 = 159664121) B159664121
theorem B13120055 : Blo 1727064 13120055 := bstep (se 1 (by rfl) ⟨9840041, by rfl⟩ : syracuseStep 13120055 = 19680083) B19680083
theorem B5829245 : Blo 1727064 5829245 := bstep (se 3 (by rfl) ⟨1092983, by rfl⟩ : syracuseStep 5829245 = 2185967) B2185967
theorem B26588027 : Blo 1727064 26588027 := bstep (se 1 (by rfl) ⟨19941020, by rfl⟩ : syracuseStep 26588027 = 39882041) B39882041
theorem B3281897 : Blo 1727064 3281897 := bstep (se 2 (by rfl) ⟨1230711, by rfl⟩ : syracuseStep 3281897 = 2461423) B2461423
theorem B3888107 : Blo 1727064 3888107 := bstep (se 1 (by rfl) ⟨2916080, by rfl⟩ : syracuseStep 3888107 = 5832161) B5832161
theorem B71874047 : Blo 1727064 71874047 := bstep (se 1 (by rfl) ⟨53905535, by rfl⟩ : syracuseStep 71874047 = 107811071) B107811071
theorem B13121999 : Blo 1727064 13121999 := bstep (se 1 (by rfl) ⟨9841499, by rfl⟩ : syracuseStep 13121999 = 19682999) B19682999
theorem B47954555 : Blo 1727064 47954555 := bstep (se 1 (by rfl) ⟨35965916, by rfl⟩ : syracuseStep 47954555 = 71931833) B71931833
theorem B1727143 : Blo 1727064 1727143 := bstep (se 1 (by rfl) ⟨1295357, by rfl⟩ : syracuseStep 1727143 = 2590715) B2590715
theorem B9837287 : Blo 1727064 9837287 := bstep (se 1 (by rfl) ⟨7377965, by rfl⟩ : syracuseStep 9837287 = 14755931) B14755931
theorem B189192995 : Blo 1727064 189192995 := bstep (se 1 (by rfl) ⟨141894746, by rfl⟩ : syracuseStep 189192995 = 283789493) B283789493
theorem B14769053 : Blo 1727064 14769053 := bstep (se 3 (by rfl) ⟨2769197, by rfl⟩ : syracuseStep 14769053 = 5538395) B5538395
theorem B2767871 : Blo 1727064 2767871 := bstep (se 1 (by rfl) ⟨2075903, by rfl⟩ : syracuseStep 2767871 = 4151807) B4151807
theorem B1727807 : Blo 1727064 1727807 := bstep (se 1 (by rfl) ⟨1295855, by rfl⟩ : syracuseStep 1727807 = 2591711) B2591711
theorem B1728127 : Blo 1727064 1728127 := bstep (se 1 (by rfl) ⟨1296095, by rfl⟩ : syracuseStep 1728127 = 2592191) B2592191
theorem B2916047 : Blo 1727064 2916047 := bstep (se 1 (by rfl) ⟨2187035, by rfl⟩ : syracuseStep 2916047 = 4374071) B4374071
theorem B19677167 : Blo 1727064 19677167 := bstep (se 1 (by rfl) ⟨14757875, by rfl⟩ : syracuseStep 19677167 = 29515751) B29515751
theorem B5833511 : Blo 1727064 5833511 := bstep (se 1 (by rfl) ⟨4375133, by rfl⟩ : syracuseStep 5833511 = 8750267) B8750267
theorem B47916031 : Blo 1727064 47916031 := bstep (se 1 (by rfl) ⟨35937023, by rfl⟩ : syracuseStep 47916031 = 71874047) B71874047
theorem B29541995 : Blo 1727064 29541995 := bstep (se 1 (by rfl) ⟨22156496, by rfl⟩ : syracuseStep 29541995 = 44312993) B44312993
theorem B5834807 : Blo 1727064 5834807 := bstep (se 1 (by rfl) ⟨4376105, by rfl⟩ : syracuseStep 5834807 = 8752211) B8752211
theorem B28035335 : Blo 1727064 28035335 := bstep (se 1 (by rfl) ⟨21026501, by rfl⟩ : syracuseStep 28035335 = 42053003) B42053003
theorem B1944031 : Blo 1727064 1944031 := bstep (se 1 (by rfl) ⟨1458023, by rfl⟩ : syracuseStep 1944031 = 2916047) B2916047
theorem B5835239 : Blo 1727064 5835239 := bstep (se 1 (by rfl) ⟨4376429, by rfl⟩ : syracuseStep 5835239 = 8752859) B8752859
theorem B8751725 : Blo 1727064 8751725 := bstep (se 3 (by rfl) ⟨1640948, by rfl⟩ : syracuseStep 8751725 = 3281897) B3281897
theorem B13118111 : Blo 1727064 13118111 := bstep (se 1 (by rfl) ⟨9838583, by rfl⟩ : syracuseStep 13118111 = 19677167) B19677167
theorem B70961831 : Blo 1727064 70961831 := bstep (se 1 (by rfl) ⟨53221373, by rfl⟩ : syracuseStep 70961831 = 106442747) B106442747
theorem B3886163 : Blo 1727064 3886163 := bstep (se 1 (by rfl) ⟨2914622, by rfl⟩ : syracuseStep 3886163 = 5829245) B5829245
theorem B2592071 : Blo 1727064 2592071 := bstep (se 1 (by rfl) ⟨1944053, by rfl⟩ : syracuseStep 2592071 = 3888107) B3888107
theorem B31969703 : Blo 1727064 31969703 := bstep (se 1 (by rfl) ⟨23977277, by rfl⟩ : syracuseStep 31969703 = 47954555) B47954555
theorem B16839103 : Blo 1727064 16839103 := bstep (se 1 (by rfl) ⟨12629327, by rfl⟩ : syracuseStep 16839103 = 25258655) B25258655
theorem B6558191 : Blo 1727064 6558191 := bstep (se 1 (by rfl) ⟨4918643, by rfl⟩ : syracuseStep 6558191 = 9837287) B9837287
theorem B126128663 : Blo 1727064 126128663 := bstep (se 1 (by rfl) ⟨94596497, by rfl⟩ : syracuseStep 126128663 = 189192995) B189192995
theorem B10507801 : Blo 1727064 10507801 := bstep (se 2 (by rfl) ⟨3940425, by rfl⟩ : syracuseStep 10507801 = 7880851) B7880851
theorem B8746703 : Blo 1727064 8746703 := bstep (se 1 (by rfl) ⟨6560027, by rfl⟩ : syracuseStep 8746703 = 13120055) B13120055
theorem B17725351 : Blo 1727064 17725351 := bstep (se 1 (by rfl) ⟨13294013, by rfl⟩ : syracuseStep 17725351 = 26588027) B26588027
theorem B8747999 : Blo 1727064 8747999 := bstep (se 1 (by rfl) ⟨6560999, by rfl⟩ : syracuseStep 8747999 = 13121999) B13121999
theorem B9846035 : Blo 1727064 9846035 := bstep (se 1 (by rfl) ⟨7384526, by rfl⟩ : syracuseStep 9846035 = 14769053) B14769053
theorem B29924687 : Blo 1727064 29924687 := bstep (se 1 (by rfl) ⟨22443515, by rfl⟩ : syracuseStep 29924687 = 44887031) B44887031
theorem B4922927 : Blo 1727064 4922927 := bstep (se 1 (by rfl) ⟨3692195, by rfl⟩ : syracuseStep 4922927 = 7384391) B7384391
theorem B7380989 : Blo 1727064 7380989 := bstep (se 3 (by rfl) ⟨1383935, by rfl⟩ : syracuseStep 7380989 = 2767871) B2767871
theorem B79799165 : Blo 1727064 79799165 := bstep (se 3 (by rfl) ⟨14962343, by rfl⟩ : syracuseStep 79799165 = 29924687) B29924687
theorem B19694663 : Blo 1727064 19694663 := bstep (se 1 (by rfl) ⟨14770997, by rfl⟩ : syracuseStep 19694663 = 29541995) B29541995
theorem B5834483 : Blo 1727064 5834483 := bstep (se 1 (by rfl) ⟨4375862, by rfl⟩ : syracuseStep 5834483 = 8751725) B8751725
theorem B14010401 : Blo 1727064 14010401 := bstep (se 2 (by rfl) ⟨5253900, by rfl⟩ : syracuseStep 14010401 = 10507801) B10507801
theorem B2590775 : Blo 1727064 2590775 := bstep (se 1 (by rfl) ⟨1943081, by rfl⟩ : syracuseStep 2590775 = 3886163) B3886163
theorem B6564023 : Blo 1727064 6564023 := bstep (se 1 (by rfl) ⟨4923017, by rfl⟩ : syracuseStep 6564023 = 9846035) B9846035
theorem B84085775 : Blo 1727064 84085775 := bstep (se 1 (by rfl) ⟨63064331, by rfl⟩ : syracuseStep 84085775 = 126128663) B126128663
theorem B2592041 : Blo 1727064 2592041 := bstep (se 2 (by rfl) ⟨972015, by rfl⟩ : syracuseStep 2592041 = 1944031) B1944031
theorem B18690223 : Blo 1727064 18690223 := bstep (se 1 (by rfl) ⟨14017667, by rfl⟩ : syracuseStep 18690223 = 28035335) B28035335
theorem B8745407 : Blo 1727064 8745407 := bstep (se 1 (by rfl) ⟨6559055, by rfl⟩ : syracuseStep 8745407 = 13118111) B13118111
theorem B3281951 : Blo 1727064 3281951 := bstep (se 1 (by rfl) ⟨2461463, by rfl⟩ : syracuseStep 3281951 = 4922927) B4922927
theorem B4920659 : Blo 1727064 4920659 := bstep (se 1 (by rfl) ⟨3690494, by rfl⟩ : syracuseStep 4920659 = 7380989) B7380989
theorem B21313135 : Blo 1727064 21313135 := bstep (se 1 (by rfl) ⟨15984851, by rfl⟩ : syracuseStep 21313135 = 31969703) B31969703
theorem B4372127 : Blo 1727064 4372127 := bstep (se 1 (by rfl) ⟨3279095, by rfl⟩ : syracuseStep 4372127 = 6558191) B6558191
theorem B3889007 : Blo 1727064 3889007 := bstep (se 1 (by rfl) ⟨2916755, by rfl⟩ : syracuseStep 3889007 = 5833511) B5833511
theorem B22452137 : Blo 1727064 22452137 := bstep (se 2 (by rfl) ⟨8419551, by rfl⟩ : syracuseStep 22452137 = 16839103) B16839103
theorem B5831135 : Blo 1727064 5831135 := bstep (se 1 (by rfl) ⟨4373351, by rfl⟩ : syracuseStep 5831135 = 8746703) B8746703
theorem B63888041 : Blo 1727064 63888041 := bstep (se 2 (by rfl) ⟨23958015, by rfl⟩ : syracuseStep 63888041 = 47916031) B47916031
theorem B3889871 : Blo 1727064 3889871 := bstep (se 1 (by rfl) ⟨2917403, by rfl⟩ : syracuseStep 3889871 = 5834807) B5834807
theorem B3890159 : Blo 1727064 3890159 := bstep (se 1 (by rfl) ⟨2917619, by rfl⟩ : syracuseStep 3890159 = 5835239) B5835239
theorem B47307887 : Blo 1727064 47307887 := bstep (se 1 (by rfl) ⟨35480915, by rfl⟩ : syracuseStep 47307887 = 70961831) B70961831
theorem B5831999 : Blo 1727064 5831999 := bstep (se 1 (by rfl) ⟨4373999, by rfl⟩ : syracuseStep 5831999 = 8747999) B8747999
theorem B1728047 : Blo 1727064 1728047 := bstep (se 1 (by rfl) ⟨1296035, by rfl⟩ : syracuseStep 1728047 = 2592071) B2592071
theorem B23633801 : Blo 1727064 23633801 := bstep (se 2 (by rfl) ⟨8862675, by rfl⟩ : syracuseStep 23633801 = 17725351) B17725351
theorem B24920297 : Blo 1727064 24920297 := bstep (se 2 (by rfl) ⟨9345111, by rfl⟩ : syracuseStep 24920297 = 18690223) B18690223
theorem B53199443 : Blo 1727064 53199443 := bstep (se 1 (by rfl) ⟨39899582, by rfl⟩ : syracuseStep 53199443 = 79799165) B79799165
theorem B2187967 : Blo 1727064 2187967 := bstep (se 1 (by rfl) ⟨1640975, by rfl⟩ : syracuseStep 2187967 = 3281951) B3281951
theorem B14968091 : Blo 1727064 14968091 := bstep (se 1 (by rfl) ⟨11226068, by rfl⟩ : syracuseStep 14968091 = 22452137) B22452137
theorem B9340267 : Blo 1727064 9340267 := bstep (se 1 (by rfl) ⟨7005200, by rfl⟩ : syracuseStep 9340267 = 14010401) B14010401
theorem B4376015 : Blo 1727064 4376015 := bstep (se 1 (by rfl) ⟨3282011, by rfl⟩ : syracuseStep 4376015 = 6564023) B6564023
theorem B42592027 : Blo 1727064 42592027 := bstep (se 1 (by rfl) ⟨31944020, by rfl⟩ : syracuseStep 42592027 = 63888041) B63888041
theorem B15755867 : Blo 1727064 15755867 := bstep (se 1 (by rfl) ⟨11816900, by rfl⟩ : syracuseStep 15755867 = 23633801) B23633801
theorem B3280439 : Blo 1727064 3280439 := bstep (se 1 (by rfl) ⟨2460329, by rfl⟩ : syracuseStep 3280439 = 4920659) B4920659
theorem B2592671 : Blo 1727064 2592671 := bstep (se 1 (by rfl) ⟨1944503, by rfl⟩ : syracuseStep 2592671 = 3889007) B3889007
theorem B3887423 : Blo 1727064 3887423 := bstep (se 1 (by rfl) ⟨2915567, by rfl⟩ : syracuseStep 3887423 = 5831135) B5831135
theorem B2593247 : Blo 1727064 2593247 := bstep (se 1 (by rfl) ⟨1944935, by rfl⟩ : syracuseStep 2593247 = 3889871) B3889871
theorem B2593439 : Blo 1727064 2593439 := bstep (se 1 (by rfl) ⟨1945079, by rfl⟩ : syracuseStep 2593439 = 3890159) B3890159
theorem B3887999 : Blo 1727064 3887999 := bstep (se 1 (by rfl) ⟨2915999, by rfl⟩ : syracuseStep 3887999 = 5831999) B5831999
theorem B5830271 : Blo 1727064 5830271 := bstep (se 1 (by rfl) ⟨4372703, by rfl⟩ : syracuseStep 5830271 = 8745407) B8745407
theorem B13129775 : Blo 1727064 13129775 := bstep (se 1 (by rfl) ⟨9847331, by rfl⟩ : syracuseStep 13129775 = 19694663) B19694663
theorem B2914751 : Blo 1727064 2914751 := bstep (se 1 (by rfl) ⟨2186063, by rfl⟩ : syracuseStep 2914751 = 4372127) B4372127
theorem B3889655 : Blo 1727064 3889655 := bstep (se 1 (by rfl) ⟨2917241, by rfl⟩ : syracuseStep 3889655 = 5834483) B5834483
theorem B1727183 : Blo 1727064 1727183 := bstep (se 1 (by rfl) ⟨1295387, by rfl⟩ : syracuseStep 1727183 = 2590775) B2590775
theorem B56057183 : Blo 1727064 56057183 := bstep (se 1 (by rfl) ⟨42042887, by rfl⟩ : syracuseStep 56057183 = 84085775) B84085775
theorem B31538591 : Blo 1727064 31538591 := bstep (se 1 (by rfl) ⟨23653943, by rfl⟩ : syracuseStep 31538591 = 47307887) B47307887
theorem B28417513 : Blo 1727064 28417513 := bstep (se 2 (by rfl) ⟨10656567, by rfl⟩ : syracuseStep 28417513 = 21313135) B21313135
theorem B1728027 : Blo 1727064 1728027 := bstep (se 1 (by rfl) ⟨1296020, by rfl⟩ : syracuseStep 1728027 = 2592041) B2592041
theorem B16613531 : Blo 1727064 16613531 := bstep (se 1 (by rfl) ⟨12460148, by rfl⟩ : syracuseStep 16613531 = 24920297) B24920297
theorem B1728831 : Blo 1727064 1728831 := bstep (se 1 (by rfl) ⟨1296623, by rfl⟩ : syracuseStep 1728831 = 2593247) B2593247
theorem B1728959 : Blo 1727064 1728959 := bstep (se 1 (by rfl) ⟨1296719, by rfl⟩ : syracuseStep 1728959 = 2593439) B2593439
theorem B9978727 : Blo 1727064 9978727 := bstep (se 1 (by rfl) ⟨7484045, by rfl⟩ : syracuseStep 9978727 = 14968091) B14968091
theorem B2917289 : Blo 1727064 2917289 := bstep (se 2 (by rfl) ⟨1093983, by rfl⟩ : syracuseStep 2917289 = 2187967) B2187967
theorem B2917343 : Blo 1727064 2917343 := bstep (se 1 (by rfl) ⟨2188007, by rfl⟩ : syracuseStep 2917343 = 4376015) B4376015
theorem B1943167 : Blo 1727064 1943167 := bstep (se 1 (by rfl) ⟨1457375, by rfl⟩ : syracuseStep 1943167 = 2914751) B2914751
theorem B10503911 : Blo 1727064 10503911 := bstep (se 1 (by rfl) ⟨7877933, by rfl⟩ : syracuseStep 10503911 = 15755867) B15755867
theorem B12453689 : Blo 1727064 12453689 := bstep (se 2 (by rfl) ⟨4670133, by rfl⟩ : syracuseStep 12453689 = 9340267) B9340267
theorem B37890017 : Blo 1727064 37890017 := bstep (se 2 (by rfl) ⟨14208756, by rfl⟩ : syracuseStep 37890017 = 28417513) B28417513
theorem B56789369 : Blo 1727064 56789369 := bstep (se 2 (by rfl) ⟨21296013, by rfl⟩ : syracuseStep 56789369 = 42592027) B42592027
theorem B2591615 : Blo 1727064 2591615 := bstep (se 1 (by rfl) ⟨1943711, by rfl⟩ : syracuseStep 2591615 = 3887423) B3887423
theorem B35466295 : Blo 1727064 35466295 := bstep (se 1 (by rfl) ⟨26599721, by rfl⟩ : syracuseStep 35466295 = 53199443) B53199443
theorem B2591999 : Blo 1727064 2591999 := bstep (se 1 (by rfl) ⟨1943999, by rfl⟩ : syracuseStep 2591999 = 3887999) B3887999
theorem B3886847 : Blo 1727064 3886847 := bstep (se 1 (by rfl) ⟨2915135, by rfl⟩ : syracuseStep 3886847 = 5830271) B5830271
theorem B8753183 : Blo 1727064 8753183 := bstep (se 1 (by rfl) ⟨6564887, by rfl⟩ : syracuseStep 8753183 = 13129775) B13129775
theorem B2593103 : Blo 1727064 2593103 := bstep (se 1 (by rfl) ⟨1944827, by rfl⟩ : syracuseStep 2593103 = 3889655) B3889655
theorem B21025727 : Blo 1727064 21025727 := bstep (se 1 (by rfl) ⟨15769295, by rfl⟩ : syracuseStep 21025727 = 31538591) B31538591
theorem B8747837 : Blo 1727064 8747837 := bstep (se 3 (by rfl) ⟨1640219, by rfl⟩ : syracuseStep 8747837 = 3280439) B3280439
theorem B37371455 : Blo 1727064 37371455 := bstep (se 1 (by rfl) ⟨28028591, by rfl⟩ : syracuseStep 37371455 = 56057183) B56057183
theorem B1728447 : Blo 1727064 1728447 := bstep (se 1 (by rfl) ⟨1296335, by rfl⟩ : syracuseStep 1728447 = 2592671) B2592671
theorem B11075687 : Blo 1727064 11075687 := bstep (se 1 (by rfl) ⟨8306765, by rfl⟩ : syracuseStep 11075687 = 16613531) B16613531
theorem B1728735 : Blo 1727064 1728735 := bstep (se 1 (by rfl) ⟨1296551, by rfl⟩ : syracuseStep 1728735 = 2593103) B2593103
theorem B14017151 : Blo 1727064 14017151 := bstep (se 1 (by rfl) ⟨10512863, by rfl⟩ : syracuseStep 14017151 = 21025727) B21025727
theorem B13304969 : Blo 1727064 13304969 := bstep (se 2 (by rfl) ⟨4989363, by rfl⟩ : syracuseStep 13304969 = 9978727) B9978727
theorem B2590889 : Blo 1727064 2590889 := bstep (se 2 (by rfl) ⟨971583, by rfl⟩ : syracuseStep 2590889 = 1943167) B1943167
theorem B24914303 : Blo 1727064 24914303 := bstep (se 1 (by rfl) ⟨18685727, by rfl⟩ : syracuseStep 24914303 = 37371455) B37371455
theorem B2591231 : Blo 1727064 2591231 := bstep (se 1 (by rfl) ⟨1943423, by rfl⟩ : syracuseStep 2591231 = 3886847) B3886847
theorem B5835455 : Blo 1727064 5835455 := bstep (se 1 (by rfl) ⟨4376591, by rfl⟩ : syracuseStep 5835455 = 8753183) B8753183
theorem B1944859 : Blo 1727064 1944859 := bstep (se 1 (by rfl) ⟨1458644, by rfl⟩ : syracuseStep 1944859 = 2917289) B2917289
theorem B1944895 : Blo 1727064 1944895 := bstep (se 1 (by rfl) ⟨1458671, by rfl⟩ : syracuseStep 1944895 = 2917343) B2917343
theorem B25260011 : Blo 1727064 25260011 := bstep (se 1 (by rfl) ⟨18945008, by rfl⟩ : syracuseStep 25260011 = 37890017) B37890017
theorem B47288393 : Blo 1727064 47288393 := bstep (se 2 (by rfl) ⟨17733147, by rfl⟩ : syracuseStep 47288393 = 35466295) B35466295
theorem B37859579 : Blo 1727064 37859579 := bstep (se 1 (by rfl) ⟨28394684, by rfl⟩ : syracuseStep 37859579 = 56789369) B56789369
theorem B7002607 : Blo 1727064 7002607 := bstep (se 1 (by rfl) ⟨5251955, by rfl⟩ : syracuseStep 7002607 = 10503911) B10503911
theorem B5831891 : Blo 1727064 5831891 := bstep (se 1 (by rfl) ⟨4373918, by rfl⟩ : syracuseStep 5831891 = 8747837) B8747837
theorem B1727743 : Blo 1727064 1727743 := bstep (se 1 (by rfl) ⟨1295807, by rfl⟩ : syracuseStep 1727743 = 2591615) B2591615
theorem B33209837 : Blo 1727064 33209837 := bstep (se 3 (by rfl) ⟨6226844, by rfl⟩ : syracuseStep 33209837 = 12453689) B12453689
theorem B1727999 : Blo 1727064 1727999 := bstep (se 1 (by rfl) ⟨1295999, by rfl⟩ : syracuseStep 1727999 = 2591999) B2591999
theorem B25239719 : Blo 1727064 25239719 := bstep (se 1 (by rfl) ⟨18929789, by rfl⟩ : syracuseStep 25239719 = 37859579) B37859579
theorem B31525595 : Blo 1727064 31525595 := bstep (se 1 (by rfl) ⟨23644196, by rfl⟩ : syracuseStep 31525595 = 47288393) B47288393
theorem B7383791 : Blo 1727064 7383791 := bstep (se 1 (by rfl) ⟨5537843, by rfl⟩ : syracuseStep 7383791 = 11075687) B11075687
theorem B16609535 : Blo 1727064 16609535 := bstep (se 1 (by rfl) ⟨12457151, by rfl⟩ : syracuseStep 16609535 = 24914303) B24914303
theorem B2593145 : Blo 1727064 2593145 := bstep (se 2 (by rfl) ⟨972429, by rfl⟩ : syracuseStep 2593145 = 1944859) B1944859
theorem B2593193 : Blo 1727064 2593193 := bstep (se 2 (by rfl) ⟨972447, by rfl⟩ : syracuseStep 2593193 = 1944895) B1944895
theorem B3887927 : Blo 1727064 3887927 := bstep (se 1 (by rfl) ⟨2915945, by rfl⟩ : syracuseStep 3887927 = 5831891) B5831891
theorem B22139891 : Blo 1727064 22139891 := bstep (se 1 (by rfl) ⟨16604918, by rfl⟩ : syracuseStep 22139891 = 33209837) B33209837
theorem B16840007 : Blo 1727064 16840007 := bstep (se 1 (by rfl) ⟨12630005, by rfl⟩ : syracuseStep 16840007 = 25260011) B25260011
theorem B9344767 : Blo 1727064 9344767 := bstep (se 1 (by rfl) ⟨7008575, by rfl⟩ : syracuseStep 9344767 = 14017151) B14017151
theorem B9336809 : Blo 1727064 9336809 := bstep (se 2 (by rfl) ⟨3501303, by rfl⟩ : syracuseStep 9336809 = 7002607) B7002607
theorem B8869979 : Blo 1727064 8869979 := bstep (se 1 (by rfl) ⟨6652484, by rfl⟩ : syracuseStep 8869979 = 13304969) B13304969
theorem B1727259 : Blo 1727064 1727259 := bstep (se 1 (by rfl) ⟨1295444, by rfl⟩ : syracuseStep 1727259 = 2590889) B2590889
theorem B1727487 : Blo 1727064 1727487 := bstep (se 1 (by rfl) ⟨1295615, by rfl⟩ : syracuseStep 1727487 = 2591231) B2591231
theorem B3890303 : Blo 1727064 3890303 := bstep (se 1 (by rfl) ⟨2917727, by rfl⟩ : syracuseStep 3890303 = 5835455) B5835455
theorem B1728763 : Blo 1727064 1728763 := bstep (se 1 (by rfl) ⟨1296572, by rfl⟩ : syracuseStep 1728763 = 2593145) B2593145
theorem B1728795 : Blo 1727064 1728795 := bstep (se 1 (by rfl) ⟨1296596, by rfl⟩ : syracuseStep 1728795 = 2593193) B2593193
theorem B67305917 : Blo 1727064 67305917 := bstep (se 3 (by rfl) ⟨12619859, by rfl⟩ : syracuseStep 67305917 = 25239719) B25239719
theorem B23653277 : Blo 1727064 23653277 := bstep (se 3 (by rfl) ⟨4434989, by rfl⟩ : syracuseStep 23653277 = 8869979) B8869979
theorem B2591951 : Blo 1727064 2591951 := bstep (se 1 (by rfl) ⟨1943963, by rfl⟩ : syracuseStep 2591951 = 3887927) B3887927
theorem B11226671 : Blo 1727064 11226671 := bstep (se 1 (by rfl) ⟨8420003, by rfl⟩ : syracuseStep 11226671 = 16840007) B16840007
theorem B21017063 : Blo 1727064 21017063 := bstep (se 1 (by rfl) ⟨15762797, by rfl⟩ : syracuseStep 21017063 = 31525595) B31525595
theorem B2593535 : Blo 1727064 2593535 := bstep (se 1 (by rfl) ⟨1945151, by rfl⟩ : syracuseStep 2593535 = 3890303) B3890303
theorem B11073023 : Blo 1727064 11073023 := bstep (se 1 (by rfl) ⟨8304767, by rfl⟩ : syracuseStep 11073023 = 16609535) B16609535
theorem B14759927 : Blo 1727064 14759927 := bstep (se 1 (by rfl) ⟨11069945, by rfl⟩ : syracuseStep 14759927 = 22139891) B22139891
theorem B6224539 : Blo 1727064 6224539 := bstep (se 1 (by rfl) ⟨4668404, by rfl⟩ : syracuseStep 6224539 = 9336809) B9336809
theorem B4922527 : Blo 1727064 4922527 := bstep (se 1 (by rfl) ⟨3691895, by rfl⟩ : syracuseStep 4922527 = 7383791) B7383791
theorem B12459689 : Blo 1727064 12459689 := bstep (se 2 (by rfl) ⟨4672383, by rfl⟩ : syracuseStep 12459689 = 9344767) B9344767
theorem B1729023 : Blo 1727064 1729023 := bstep (se 1 (by rfl) ⟨1296767, by rfl⟩ : syracuseStep 1729023 = 2593535) B2593535
theorem B8299385 : Blo 1727064 8299385 := bstep (se 2 (by rfl) ⟨3112269, by rfl⟩ : syracuseStep 8299385 = 6224539) B6224539
theorem B7382015 : Blo 1727064 7382015 := bstep (se 1 (by rfl) ⟨5536511, by rfl⟩ : syracuseStep 7382015 = 11073023) B11073023
theorem B9839951 : Blo 1727064 9839951 := bstep (se 1 (by rfl) ⟨7379963, by rfl⟩ : syracuseStep 9839951 = 14759927) B14759927
theorem B6563369 : Blo 1727064 6563369 := bstep (se 2 (by rfl) ⟨2461263, by rfl⟩ : syracuseStep 6563369 = 4922527) B4922527
theorem B44870611 : Blo 1727064 44870611 := bstep (se 1 (by rfl) ⟨33652958, by rfl⟩ : syracuseStep 44870611 = 67305917) B67305917
theorem B14011375 : Blo 1727064 14011375 := bstep (se 1 (by rfl) ⟨10508531, by rfl⟩ : syracuseStep 14011375 = 21017063) B21017063
theorem B7484447 : Blo 1727064 7484447 := bstep (se 1 (by rfl) ⟨5613335, by rfl⟩ : syracuseStep 7484447 = 11226671) B11226671
theorem B15768851 : Blo 1727064 15768851 := bstep (se 1 (by rfl) ⟨11826638, by rfl⟩ : syracuseStep 15768851 = 23653277) B23653277
theorem B1727967 : Blo 1727064 1727967 := bstep (se 1 (by rfl) ⟨1295975, by rfl⟩ : syracuseStep 1727967 = 2591951) B2591951
theorem B8306459 : Blo 1727064 8306459 := bstep (se 1 (by rfl) ⟨6229844, by rfl⟩ : syracuseStep 8306459 = 12459689) B12459689
theorem B42050269 : Blo 1727064 42050269 := bstep (se 3 (by rfl) ⟨7884425, by rfl⟩ : syracuseStep 42050269 = 15768851) B15768851
theorem B4375579 : Blo 1727064 4375579 := bstep (se 1 (by rfl) ⟨3281684, by rfl⟩ : syracuseStep 4375579 = 6563369) B6563369
theorem B59827481 : Blo 1727064 59827481 := bstep (se 2 (by rfl) ⟨22435305, by rfl⟩ : syracuseStep 59827481 = 44870611) B44870611
theorem B19958525 : Blo 1727064 19958525 := bstep (se 3 (by rfl) ⟨3742223, by rfl⟩ : syracuseStep 19958525 = 7484447) B7484447
theorem B5532923 : Blo 1727064 5532923 := bstep (se 1 (by rfl) ⟨4149692, by rfl⟩ : syracuseStep 5532923 = 8299385) B8299385
theorem B18681833 : Blo 1727064 18681833 := bstep (se 2 (by rfl) ⟨7005687, by rfl⟩ : syracuseStep 18681833 = 14011375) B14011375
theorem B4921343 : Blo 1727064 4921343 := bstep (se 1 (by rfl) ⟨3691007, by rfl⟩ : syracuseStep 4921343 = 7382015) B7382015
theorem B6559967 : Blo 1727064 6559967 := bstep (se 1 (by rfl) ⟨4919975, by rfl⟩ : syracuseStep 6559967 = 9839951) B9839951
theorem B5537639 : Blo 1727064 5537639 := bstep (se 1 (by rfl) ⟨4153229, by rfl⟩ : syracuseStep 5537639 = 8306459) B8306459
theorem B5834105 : Blo 1727064 5834105 := bstep (se 2 (by rfl) ⟨2187789, by rfl⟩ : syracuseStep 5834105 = 4375579) B4375579
theorem B13305683 : Blo 1727064 13305683 := bstep (se 1 (by rfl) ⟨9979262, by rfl⟩ : syracuseStep 13305683 = 19958525) B19958525
theorem B3688615 : Blo 1727064 3688615 := bstep (se 1 (by rfl) ⟨2766461, by rfl⟩ : syracuseStep 3688615 = 5532923) B5532923
theorem B12454555 : Blo 1727064 12454555 := bstep (se 1 (by rfl) ⟨9340916, by rfl⟩ : syracuseStep 12454555 = 18681833) B18681833
theorem B224268101 : Blo 1727064 224268101 := bstep (se 4 (by rfl) ⟨21025134, by rfl⟩ : syracuseStep 224268101 = 42050269) B42050269
theorem B3280895 : Blo 1727064 3280895 := bstep (se 1 (by rfl) ⟨2460671, by rfl⟩ : syracuseStep 3280895 = 4921343) B4921343
theorem B3691759 : Blo 1727064 3691759 := bstep (se 1 (by rfl) ⟨2768819, by rfl⟩ : syracuseStep 3691759 = 5537639) B5537639
theorem B39884987 : Blo 1727064 39884987 := bstep (se 1 (by rfl) ⟨29913740, by rfl⟩ : syracuseStep 39884987 = 59827481) B59827481
theorem B4373311 : Blo 1727064 4373311 := bstep (se 1 (by rfl) ⟨3279983, by rfl⟩ : syracuseStep 4373311 = 6559967) B6559967
theorem B16606073 : Blo 1727064 16606073 := bstep (se 2 (by rfl) ⟨6227277, by rfl⟩ : syracuseStep 16606073 = 12454555) B12454555
theorem B4918153 : Blo 1727064 4918153 := bstep (se 2 (by rfl) ⟨1844307, by rfl⟩ : syracuseStep 4918153 = 3688615) B3688615
theorem B3889403 : Blo 1727064 3889403 := bstep (se 1 (by rfl) ⟨2917052, by rfl⟩ : syracuseStep 3889403 = 5834105) B5834105
theorem B5831081 : Blo 1727064 5831081 := bstep (se 2 (by rfl) ⟨2186655, by rfl⟩ : syracuseStep 5831081 = 4373311) B4373311
theorem B8870455 : Blo 1727064 8870455 := bstep (se 1 (by rfl) ⟨6652841, by rfl⟩ : syracuseStep 8870455 = 13305683) B13305683
theorem B26589991 : Blo 1727064 26589991 := bstep (se 1 (by rfl) ⟨19942493, by rfl⟩ : syracuseStep 26589991 = 39884987) B39884987
theorem B4922345 : Blo 1727064 4922345 := bstep (se 2 (by rfl) ⟨1845879, by rfl⟩ : syracuseStep 4922345 = 3691759) B3691759
theorem B149512067 : Blo 1727064 149512067 := bstep (se 1 (by rfl) ⟨112134050, by rfl⟩ : syracuseStep 149512067 = 224268101) B224268101
theorem B2187263 : Blo 1727064 2187263 := bstep (se 1 (by rfl) ⟨1640447, by rfl⟩ : syracuseStep 2187263 = 3280895) B3280895
theorem B47309093 : Blo 1727064 47309093 := bstep (se 4 (by rfl) ⟨4435227, by rfl⟩ : syracuseStep 47309093 = 8870455) B8870455
theorem B5832701 : Blo 1727064 5832701 := bstep (se 3 (by rfl) ⟨1093631, by rfl⟩ : syracuseStep 5832701 = 2187263) B2187263
theorem B99674711 : Blo 1727064 99674711 := bstep (se 1 (by rfl) ⟨74756033, by rfl⟩ : syracuseStep 99674711 = 149512067) B149512067
theorem B11070715 : Blo 1727064 11070715 := bstep (se 1 (by rfl) ⟨8303036, by rfl⟩ : syracuseStep 11070715 = 16606073) B16606073
theorem B6557537 : Blo 1727064 6557537 := bstep (se 2 (by rfl) ⟨2459076, by rfl⟩ : syracuseStep 6557537 = 4918153) B4918153
theorem B2592935 : Blo 1727064 2592935 := bstep (se 1 (by rfl) ⟨1944701, by rfl⟩ : syracuseStep 2592935 = 3889403) B3889403
theorem B3887387 : Blo 1727064 3887387 := bstep (se 1 (by rfl) ⟨2915540, by rfl⟩ : syracuseStep 3887387 = 5831081) B5831081
theorem B3281563 : Blo 1727064 3281563 := bstep (se 1 (by rfl) ⟨2461172, by rfl⟩ : syracuseStep 3281563 = 4922345) B4922345
theorem B35453321 : Blo 1727064 35453321 := bstep (se 2 (by rfl) ⟨13294995, by rfl⟩ : syracuseStep 35453321 = 26589991) B26589991
theorem B1728623 : Blo 1727064 1728623 := bstep (se 1 (by rfl) ⟨1296467, by rfl⟩ : syracuseStep 1728623 = 2592935) B2592935
theorem B31539395 : Blo 1727064 31539395 := bstep (se 1 (by rfl) ⟨23654546, by rfl⟩ : syracuseStep 31539395 = 47309093) B47309093
theorem B4375417 : Blo 1727064 4375417 := bstep (se 2 (by rfl) ⟨1640781, by rfl⟩ : syracuseStep 4375417 = 3281563) B3281563
theorem B23635547 : Blo 1727064 23635547 := bstep (se 1 (by rfl) ⟨17726660, by rfl⟩ : syracuseStep 23635547 = 35453321) B35453321
theorem B2591591 : Blo 1727064 2591591 := bstep (se 1 (by rfl) ⟨1943693, by rfl⟩ : syracuseStep 2591591 = 3887387) B3887387
theorem B66449807 : Blo 1727064 66449807 := bstep (se 1 (by rfl) ⟨49837355, by rfl⟩ : syracuseStep 66449807 = 99674711) B99674711
theorem B4371691 : Blo 1727064 4371691 := bstep (se 1 (by rfl) ⟨3278768, by rfl⟩ : syracuseStep 4371691 = 6557537) B6557537
theorem B3888467 : Blo 1727064 3888467 := bstep (se 1 (by rfl) ⟨2916350, by rfl⟩ : syracuseStep 3888467 = 5832701) B5832701
theorem B14760953 : Blo 1727064 14760953 := bstep (se 2 (by rfl) ⟨5535357, by rfl⟩ : syracuseStep 14760953 = 11070715) B11070715
theorem B5833889 : Blo 1727064 5833889 := bstep (se 2 (by rfl) ⟨2187708, by rfl⟩ : syracuseStep 5833889 = 4375417) B4375417
theorem B9840635 : Blo 1727064 9840635 := bstep (se 1 (by rfl) ⟨7380476, by rfl⟩ : syracuseStep 9840635 = 14760953) B14760953
theorem B2592311 : Blo 1727064 2592311 := bstep (se 1 (by rfl) ⟨1944233, by rfl⟩ : syracuseStep 2592311 = 3888467) B3888467
theorem B15757031 : Blo 1727064 15757031 := bstep (se 1 (by rfl) ⟨11817773, by rfl⟩ : syracuseStep 15757031 = 23635547) B23635547
theorem B5828921 : Blo 1727064 5828921 := bstep (se 2 (by rfl) ⟨2185845, by rfl⟩ : syracuseStep 5828921 = 4371691) B4371691
theorem B21026263 : Blo 1727064 21026263 := bstep (se 1 (by rfl) ⟨15769697, by rfl⟩ : syracuseStep 21026263 = 31539395) B31539395
theorem B44299871 : Blo 1727064 44299871 := bstep (se 1 (by rfl) ⟨33224903, by rfl⟩ : syracuseStep 44299871 = 66449807) B66449807
theorem B1727727 : Blo 1727064 1727727 := bstep (se 1 (by rfl) ⟨1295795, by rfl⟩ : syracuseStep 1727727 = 2591591) B2591591
theorem B29533247 : Blo 1727064 29533247 := bstep (se 1 (by rfl) ⟨22149935, by rfl⟩ : syracuseStep 29533247 = 44299871) B44299871
theorem B42018749 : Blo 1727064 42018749 := bstep (se 3 (by rfl) ⟨7878515, by rfl⟩ : syracuseStep 42018749 = 15757031) B15757031
theorem B28035017 : Blo 1727064 28035017 := bstep (se 2 (by rfl) ⟨10513131, by rfl⟩ : syracuseStep 28035017 = 21026263) B21026263
theorem B3885947 : Blo 1727064 3885947 := bstep (se 1 (by rfl) ⟨2914460, by rfl⟩ : syracuseStep 3885947 = 5828921) B5828921
theorem B3889259 : Blo 1727064 3889259 := bstep (se 1 (by rfl) ⟨2916944, by rfl⟩ : syracuseStep 3889259 = 5833889) B5833889
theorem B6560423 : Blo 1727064 6560423 := bstep (se 1 (by rfl) ⟨4920317, by rfl⟩ : syracuseStep 6560423 = 9840635) B9840635
theorem B1728207 : Blo 1727064 1728207 := bstep (se 1 (by rfl) ⟨1296155, by rfl⟩ : syracuseStep 1728207 = 2592311) B2592311
theorem B2590631 : Blo 1727064 2590631 := bstep (se 1 (by rfl) ⟨1942973, by rfl⟩ : syracuseStep 2590631 = 3885947) B3885947
theorem B19688831 : Blo 1727064 19688831 := bstep (se 1 (by rfl) ⟨14766623, by rfl⟩ : syracuseStep 19688831 = 29533247) B29533247
theorem B28012499 : Blo 1727064 28012499 := bstep (se 1 (by rfl) ⟨21009374, by rfl⟩ : syracuseStep 28012499 = 42018749) B42018749
theorem B18690011 : Blo 1727064 18690011 := bstep (se 1 (by rfl) ⟨14017508, by rfl⟩ : syracuseStep 18690011 = 28035017) B28035017
theorem B2592839 : Blo 1727064 2592839 := bstep (se 1 (by rfl) ⟨1944629, by rfl⟩ : syracuseStep 2592839 = 3889259) B3889259
theorem B4373615 : Blo 1727064 4373615 := bstep (se 1 (by rfl) ⟨3280211, by rfl⟩ : syracuseStep 4373615 = 6560423) B6560423
theorem B1728559 : Blo 1727064 1728559 := bstep (se 1 (by rfl) ⟨1296419, by rfl⟩ : syracuseStep 1728559 = 2592839) B2592839
theorem B13125887 : Blo 1727064 13125887 := bstep (se 1 (by rfl) ⟨9844415, by rfl⟩ : syracuseStep 13125887 = 19688831) B19688831
theorem B18674999 : Blo 1727064 18674999 := bstep (se 1 (by rfl) ⟨14006249, by rfl⟩ : syracuseStep 18674999 = 28012499) B28012499
theorem B1727087 : Blo 1727064 1727087 := bstep (se 1 (by rfl) ⟨1295315, by rfl⟩ : syracuseStep 1727087 = 2590631) B2590631
theorem B2915743 : Blo 1727064 2915743 := bstep (se 1 (by rfl) ⟨2186807, by rfl⟩ : syracuseStep 2915743 = 4373615) B4373615
theorem B12460007 : Blo 1727064 12460007 := bstep (se 1 (by rfl) ⟨9345005, by rfl⟩ : syracuseStep 12460007 = 18690011) B18690011
theorem B8750591 : Blo 1727064 8750591 := bstep (se 1 (by rfl) ⟨6562943, by rfl⟩ : syracuseStep 8750591 = 13125887) B13125887
theorem B3887657 : Blo 1727064 3887657 := bstep (se 2 (by rfl) ⟨1457871, by rfl⟩ : syracuseStep 3887657 = 2915743) B2915743
theorem B12449999 : Blo 1727064 12449999 := bstep (se 1 (by rfl) ⟨9337499, by rfl⟩ : syracuseStep 12449999 = 18674999) B18674999
theorem B8306671 : Blo 1727064 8306671 := bstep (se 1 (by rfl) ⟨6230003, by rfl⟩ : syracuseStep 8306671 = 12460007) B12460007
theorem B5833727 : Blo 1727064 5833727 := bstep (se 1 (by rfl) ⟨4375295, by rfl⟩ : syracuseStep 5833727 = 8750591) B8750591
theorem B8299999 : Blo 1727064 8299999 := bstep (se 1 (by rfl) ⟨6224999, by rfl⟩ : syracuseStep 8299999 = 12449999) B12449999
theorem B2591771 : Blo 1727064 2591771 := bstep (se 1 (by rfl) ⟨1943828, by rfl⟩ : syracuseStep 2591771 = 3887657) B3887657
theorem B11075561 : Blo 1727064 11075561 := bstep (se 2 (by rfl) ⟨4153335, by rfl⟩ : syracuseStep 11075561 = 8306671) B8306671
theorem B7383707 : Blo 1727064 7383707 := bstep (se 1 (by rfl) ⟨5537780, by rfl⟩ : syracuseStep 7383707 = 11075561) B11075561
theorem B3889151 : Blo 1727064 3889151 := bstep (se 1 (by rfl) ⟨2916863, by rfl⟩ : syracuseStep 3889151 = 5833727) B5833727
theorem B11066665 : Blo 1727064 11066665 := bstep (se 2 (by rfl) ⟨4149999, by rfl⟩ : syracuseStep 11066665 = 8299999) B8299999
theorem B1727847 : Blo 1727064 1727847 := bstep (se 1 (by rfl) ⟨1295885, by rfl⟩ : syracuseStep 1727847 = 2591771) B2591771
theorem B14755553 : Blo 1727064 14755553 := bstep (se 2 (by rfl) ⟨5533332, by rfl⟩ : syracuseStep 14755553 = 11066665) B11066665
theorem B2592767 : Blo 1727064 2592767 := bstep (se 1 (by rfl) ⟨1944575, by rfl⟩ : syracuseStep 2592767 = 3889151) B3889151
theorem B4922471 : Blo 1727064 4922471 := bstep (se 1 (by rfl) ⟨3691853, by rfl⟩ : syracuseStep 4922471 = 7383707) B7383707
theorem B3281647 : Blo 1727064 3281647 := bstep (se 1 (by rfl) ⟨2461235, by rfl⟩ : syracuseStep 3281647 = 4922471) B4922471
theorem B1728511 : Blo 1727064 1728511 := bstep (se 1 (by rfl) ⟨1296383, by rfl⟩ : syracuseStep 1728511 = 2592767) B2592767
theorem B9837035 : Blo 1727064 9837035 := bstep (se 1 (by rfl) ⟨7377776, by rfl⟩ : syracuseStep 9837035 = 14755553) B14755553
theorem B4375529 : Blo 1727064 4375529 := bstep (se 2 (by rfl) ⟨1640823, by rfl⟩ : syracuseStep 4375529 = 3281647) B3281647
theorem B6558023 : Blo 1727064 6558023 := bstep (se 1 (by rfl) ⟨4918517, by rfl⟩ : syracuseStep 6558023 = 9837035) B9837035
theorem B2917019 : Blo 1727064 2917019 := bstep (se 1 (by rfl) ⟨2187764, by rfl⟩ : syracuseStep 2917019 = 4375529) B4375529
theorem B4372015 : Blo 1727064 4372015 := bstep (se 1 (by rfl) ⟨3279011, by rfl⟩ : syracuseStep 4372015 = 6558023) B6558023
theorem B1944679 : Blo 1727064 1944679 := bstep (se 1 (by rfl) ⟨1458509, by rfl⟩ : syracuseStep 1944679 = 2917019) B2917019
theorem B5829353 : Blo 1727064 5829353 := bstep (se 2 (by rfl) ⟨2186007, by rfl⟩ : syracuseStep 5829353 = 4372015) B4372015
theorem B3886235 : Blo 1727064 3886235 := bstep (se 1 (by rfl) ⟨2914676, by rfl⟩ : syracuseStep 3886235 = 5829353) B5829353
theorem B2592905 : Blo 1727064 2592905 := bstep (se 2 (by rfl) ⟨972339, by rfl⟩ : syracuseStep 2592905 = 1944679) B1944679
theorem B1728603 : Blo 1727064 1728603 := bstep (se 1 (by rfl) ⟨1296452, by rfl⟩ : syracuseStep 1728603 = 2592905) B2592905
theorem B2590823 : Blo 1727064 2590823 := bstep (se 1 (by rfl) ⟨1943117, by rfl⟩ : syracuseStep 2590823 = 3886235) B3886235
theorem B1727215 : Blo 1727064 1727215 := bstep (se 1 (by rfl) ⟨1295411, by rfl⟩ : syracuseStep 1727215 = 2590823) B2590823

theorem C0 (j : ℕ) (h1 : 431766 ≤ j) (h2 : j ≤ 432265) : Blo 1727064 (4 * j + 3) := by
  interval_cases j
  · exact B1727067
  · exact B1727071
  · exact B1727075
  · exact B1727079
  · exact B1727083
  · exact B1727087
  · exact B1727091
  · exact B1727095
  · exact B1727099
  · exact B1727103
  · exact B1727107
  · exact B1727111
  · exact B1727115
  · exact B1727119
  · exact B1727123
  · exact B1727127
  · exact B1727131
  · exact B1727135
  · exact B1727139
  · exact B1727143
  · exact B1727147
  · exact B1727151
  · exact B1727155
  · exact B1727159
  · exact B1727163
  · exact B1727167
  · exact B1727171
  · exact B1727175
  · exact B1727179
  · exact B1727183
  · exact B1727187
  · exact B1727191
  · exact B1727195
  · exact B1727199
  · exact B1727203
  · exact B1727207
  · exact B1727211
  · exact B1727215
  · exact B1727219
  · exact B1727223
  · exact B1727227
  · exact B1727231
  · exact B1727235
  · exact B1727239
  · exact B1727243
  · exact B1727247
  · exact B1727251
  · exact B1727255
  · exact B1727259
  · exact B1727263
  · exact B1727267
  · exact B1727271
  · exact B1727275
  · exact B1727279
  · exact B1727283
  · exact B1727287
  · exact B1727291
  · exact B1727295
  · exact B1727299
  · exact B1727303
  · exact B1727307
  · exact B1727311
  · exact B1727315
  · exact B1727319
  · exact B1727323
  · exact B1727327
  · exact B1727331
  · exact B1727335
  · exact B1727339
  · exact B1727343
  · exact B1727347
  · exact B1727351
  · exact B1727355
  · exact B1727359
  · exact B1727363
  · exact B1727367
  · exact B1727371
  · exact B1727375
  · exact B1727379
  · exact B1727383
  · exact B1727387
  · exact B1727391
  · exact B1727395
  · exact B1727399
  · exact B1727403
  · exact B1727407
  · exact B1727411
  · exact B1727415
  · exact B1727419
  · exact B1727423
  · exact B1727427
  · exact B1727431
  · exact B1727435
  · exact B1727439
  · exact B1727443
  · exact B1727447
  · exact B1727451
  · exact B1727455
  · exact B1727459
  · exact B1727463
  · exact B1727467
  · exact B1727471
  · exact B1727475
  · exact B1727479
  · exact B1727483
  · exact B1727487
  · exact B1727491
  · exact B1727495
  · exact B1727499
  · exact B1727503
  · exact B1727507
  · exact B1727511
  · exact B1727515
  · exact B1727519
  · exact B1727523
  · exact B1727527
  · exact B1727531
  · exact B1727535
  · exact B1727539
  · exact B1727543
  · exact B1727547
  · exact B1727551
  · exact B1727555
  · exact B1727559
  · exact B1727563
  · exact B1727567
  · exact B1727571
  · exact B1727575
  · exact B1727579
  · exact B1727583
  · exact B1727587
  · exact B1727591
  · exact B1727595
  · exact B1727599
  · exact B1727603
  · exact B1727607
  · exact B1727611
  · exact B1727615
  · exact B1727619
  · exact B1727623
  · exact B1727627
  · exact B1727631
  · exact B1727635
  · exact B1727639
  · exact B1727643
  · exact B1727647
  · exact B1727651
  · exact B1727655
  · exact B1727659
  · exact B1727663
  · exact B1727667
  · exact B1727671
  · exact B1727675
  · exact B1727679
  · exact B1727683
  · exact B1727687
  · exact B1727691
  · exact B1727695
  · exact B1727699
  · exact B1727703
  · exact B1727707
  · exact B1727711
  · exact B1727715
  · exact B1727719
  · exact B1727723
  · exact B1727727
  · exact B1727731
  · exact B1727735
  · exact B1727739
  · exact B1727743
  · exact B1727747
  · exact B1727751
  · exact B1727755
  · exact B1727759
  · exact B1727763
  · exact B1727767
  · exact B1727771
  · exact B1727775
  · exact B1727779
  · exact B1727783
  · exact B1727787
  · exact B1727791
  · exact B1727795
  · exact B1727799
  · exact B1727803
  · exact B1727807
  · exact B1727811
  · exact B1727815
  · exact B1727819
  · exact B1727823
  · exact B1727827
  · exact B1727831
  · exact B1727835
  · exact B1727839
  · exact B1727843
  · exact B1727847
  · exact B1727851
  · exact B1727855
  · exact B1727859
  · exact B1727863
  · exact B1727867
  · exact B1727871
  · exact B1727875
  · exact B1727879
  · exact B1727883
  · exact B1727887
  · exact B1727891
  · exact B1727895
  · exact B1727899
  · exact B1727903
  · exact B1727907
  · exact B1727911
  · exact B1727915
  · exact B1727919
  · exact B1727923
  · exact B1727927
  · exact B1727931
  · exact B1727935
  · exact B1727939
  · exact B1727943
  · exact B1727947
  · exact B1727951
  · exact B1727955
  · exact B1727959
  · exact B1727963
  · exact B1727967
  · exact B1727971
  · exact B1727975
  · exact B1727979
  · exact B1727983
  · exact B1727987
  · exact B1727991
  · exact B1727995
  · exact B1727999
  · exact B1728003
  · exact B1728007
  · exact B1728011
  · exact B1728015
  · exact B1728019
  · exact B1728023
  · exact B1728027
  · exact B1728031
  · exact B1728035
  · exact B1728039
  · exact B1728043
  · exact B1728047
  · exact B1728051
  · exact B1728055
  · exact B1728059
  · exact B1728063
  · exact B1728067
  · exact B1728071
  · exact B1728075
  · exact B1728079
  · exact B1728083
  · exact B1728087
  · exact B1728091
  · exact B1728095
  · exact B1728099
  · exact B1728103
  · exact B1728107
  · exact B1728111
  · exact B1728115
  · exact B1728119
  · exact B1728123
  · exact B1728127
  · exact B1728131
  · exact B1728135
  · exact B1728139
  · exact B1728143
  · exact B1728147
  · exact B1728151
  · exact B1728155
  · exact B1728159
  · exact B1728163
  · exact B1728167
  · exact B1728171
  · exact B1728175
  · exact B1728179
  · exact B1728183
  · exact B1728187
  · exact B1728191
  · exact B1728195
  · exact B1728199
  · exact B1728203
  · exact B1728207
  · exact B1728211
  · exact B1728215
  · exact B1728219
  · exact B1728223
  · exact B1728227
  · exact B1728231
  · exact B1728235
  · exact B1728239
  · exact B1728243
  · exact B1728247
  · exact B1728251
  · exact B1728255
  · exact B1728259
  · exact B1728263
  · exact B1728267
  · exact B1728271
  · exact B1728275
  · exact B1728279
  · exact B1728283
  · exact B1728287
  · exact B1728291
  · exact B1728295
  · exact B1728299
  · exact B1728303
  · exact B1728307
  · exact B1728311
  · exact B1728315
  · exact B1728319
  · exact B1728323
  · exact B1728327
  · exact B1728331
  · exact B1728335
  · exact B1728339
  · exact B1728343
  · exact B1728347
  · exact B1728351
  · exact B1728355
  · exact B1728359
  · exact B1728363
  · exact B1728367
  · exact B1728371
  · exact B1728375
  · exact B1728379
  · exact B1728383
  · exact B1728387
  · exact B1728391
  · exact B1728395
  · exact B1728399
  · exact B1728403
  · exact B1728407
  · exact B1728411
  · exact B1728415
  · exact B1728419
  · exact B1728423
  · exact B1728427
  · exact B1728431
  · exact B1728435
  · exact B1728439
  · exact B1728443
  · exact B1728447
  · exact B1728451
  · exact B1728455
  · exact B1728459
  · exact B1728463
  · exact B1728467
  · exact B1728471
  · exact B1728475
  · exact B1728479
  · exact B1728483
  · exact B1728487
  · exact B1728491
  · exact B1728495
  · exact B1728499
  · exact B1728503
  · exact B1728507
  · exact B1728511
  · exact B1728515
  · exact B1728519
  · exact B1728523
  · exact B1728527
  · exact B1728531
  · exact B1728535
  · exact B1728539
  · exact B1728543
  · exact B1728547
  · exact B1728551
  · exact B1728555
  · exact B1728559
  · exact B1728563
  · exact B1728567
  · exact B1728571
  · exact B1728575
  · exact B1728579
  · exact B1728583
  · exact B1728587
  · exact B1728591
  · exact B1728595
  · exact B1728599
  · exact B1728603
  · exact B1728607
  · exact B1728611
  · exact B1728615
  · exact B1728619
  · exact B1728623
  · exact B1728627
  · exact B1728631
  · exact B1728635
  · exact B1728639
  · exact B1728643
  · exact B1728647
  · exact B1728651
  · exact B1728655
  · exact B1728659
  · exact B1728663
  · exact B1728667
  · exact B1728671
  · exact B1728675
  · exact B1728679
  · exact B1728683
  · exact B1728687
  · exact B1728691
  · exact B1728695
  · exact B1728699
  · exact B1728703
  · exact B1728707
  · exact B1728711
  · exact B1728715
  · exact B1728719
  · exact B1728723
  · exact B1728727
  · exact B1728731
  · exact B1728735
  · exact B1728739
  · exact B1728743
  · exact B1728747
  · exact B1728751
  · exact B1728755
  · exact B1728759
  · exact B1728763
  · exact B1728767
  · exact B1728771
  · exact B1728775
  · exact B1728779
  · exact B1728783
  · exact B1728787
  · exact B1728791
  · exact B1728795
  · exact B1728799
  · exact B1728803
  · exact B1728807
  · exact B1728811
  · exact B1728815
  · exact B1728819
  · exact B1728823
  · exact B1728827
  · exact B1728831
  · exact B1728835
  · exact B1728839
  · exact B1728843
  · exact B1728847
  · exact B1728851
  · exact B1728855
  · exact B1728859
  · exact B1728863
  · exact B1728867
  · exact B1728871
  · exact B1728875
  · exact B1728879
  · exact B1728883
  · exact B1728887
  · exact B1728891
  · exact B1728895
  · exact B1728899
  · exact B1728903
  · exact B1728907
  · exact B1728911
  · exact B1728915
  · exact B1728919
  · exact B1728923
  · exact B1728927
  · exact B1728931
  · exact B1728935
  · exact B1728939
  · exact B1728943
  · exact B1728947
  · exact B1728951
  · exact B1728955
  · exact B1728959
  · exact B1728963
  · exact B1728967
  · exact B1728971
  · exact B1728975
  · exact B1728979
  · exact B1728983
  · exact B1728987
  · exact B1728991
  · exact B1728995
  · exact B1728999
  · exact B1729003
  · exact B1729007
  · exact B1729011
  · exact B1729015
  · exact B1729019
  · exact B1729023
  · exact B1729027
  · exact B1729031
  · exact B1729035
  · exact B1729039
  · exact B1729043
  · exact B1729047
  · exact B1729051
  · exact B1729055
  · exact B1729059
  · exact B1729063

theorem solution (m : ℕ) (hlo : 1727064 ≤ m) (hhi : m ≤ 1729064) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 431766 ≤ j := by omega
    have hj2 : j ≤ 432265 := by omega
    have hb : Blo 1727064 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
