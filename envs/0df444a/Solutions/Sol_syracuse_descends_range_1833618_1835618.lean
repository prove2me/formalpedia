-- Prove2me | solution 1 for syracuse_descends_range_1833618_1835618
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T01:00:37.841642+00:00
-- url     : https://prove2.me/submissions/3053dd4b-b543-4296-b582-fdc77ffcf0b6

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


theorem B4407301 : Blo 1833618 4407301 := bbase (se 4 (by rfl) ⟨413184, by rfl⟩ : syracuseStep 4407301 = 826369) (by norm_num)
theorem B2752517 : Blo 1833618 2752517 := bbase (se 4 (by rfl) ⟨258048, by rfl⟩ : syracuseStep 2752517 = 516097) (by norm_num)
theorem B3481613 : Blo 1833618 3481613 := bbase (se 3 (by rfl) ⟨652802, by rfl⟩ : syracuseStep 3481613 = 1305605) (by norm_num)
theorem B3096589 : Blo 1833618 3096589 := bbase (se 3 (by rfl) ⟨580610, by rfl⟩ : syracuseStep 3096589 = 1161221) (by norm_num)
theorem B2064397 : Blo 1833618 2064397 := bbase (se 3 (by rfl) ⟨387074, by rfl⟩ : syracuseStep 2064397 = 774149) (by norm_num)
theorem B2752541 : Blo 1833618 2752541 := bbase (se 3 (by rfl) ⟨516101, by rfl⟩ : syracuseStep 2752541 = 1032203) (by norm_num)
theorem B2064433 : Blo 1833618 2064433 := bbase (se 2 (by rfl) ⟨774162, by rfl⟩ : syracuseStep 2064433 = 1548325) (by norm_num)
theorem B6193205 : Blo 1833618 6193205 := bbase (se 5 (by rfl) ⟨290306, by rfl⟩ : syracuseStep 6193205 = 580613) (by norm_num)
theorem B4128821 : Blo 1833618 4128821 := bbase (se 5 (by rfl) ⟨193538, by rfl⟩ : syracuseStep 4128821 = 387077) (by norm_num)
theorem B2752565 : Blo 1833618 2752565 := bbase (se 5 (by rfl) ⟨129026, by rfl⟩ : syracuseStep 2752565 = 258053) (by norm_num)
theorem B2752589 : Blo 1833618 2752589 := bbase (se 3 (by rfl) ⟨516110, by rfl⟩ : syracuseStep 2752589 = 1032221) (by norm_num)
theorem B2064469 : Blo 1833618 2064469 := bbase (se 8 (by rfl) ⟨12096, by rfl⟩ : syracuseStep 2064469 = 24193) (by norm_num)
theorem B4644965 : Blo 1833618 4644965 := bbase (se 4 (by rfl) ⟨435465, by rfl⟩ : syracuseStep 4644965 = 870931) (by norm_num)
theorem B3096677 : Blo 1833618 3096677 := bbase (se 4 (by rfl) ⟨290313, by rfl⟩ : syracuseStep 3096677 = 580627) (by norm_num)
theorem B2752613 : Blo 1833618 2752613 := bbase (se 4 (by rfl) ⟨258057, by rfl⟩ : syracuseStep 2752613 = 516115) (by norm_num)
theorem B6963317 : Blo 1833618 6963317 := bbase (se 5 (by rfl) ⟨326405, by rfl⟩ : syracuseStep 6963317 = 652811) (by norm_num)
theorem B2064505 : Blo 1833618 2064505 := bbase (se 2 (by rfl) ⟨774189, by rfl⟩ : syracuseStep 2064505 = 1548379) (by norm_num)
theorem B4128893 : Blo 1833618 4128893 := bbase (se 3 (by rfl) ⟨774167, by rfl⟩ : syracuseStep 4128893 = 1548335) (by norm_num)
theorem B2752637 : Blo 1833618 2752637 := bbase (se 3 (by rfl) ⟨516119, by rfl⟩ : syracuseStep 2752637 = 1032239) (by norm_num)
theorem B2752661 : Blo 1833618 2752661 := bbase (se 6 (by rfl) ⟨64515, by rfl⟩ : syracuseStep 2752661 = 129031) (by norm_num)
theorem B2613397 : Blo 1833618 2613397 := bbase (se 6 (by rfl) ⟨61251, by rfl⟩ : syracuseStep 2613397 = 122503) (by norm_num)
theorem B2064541 : Blo 1833618 2064541 := bbase (se 3 (by rfl) ⟨387101, by rfl⟩ : syracuseStep 2064541 = 774203) (by norm_num)
theorem B2752685 : Blo 1833618 2752685 := bbase (se 3 (by rfl) ⟨516128, by rfl⟩ : syracuseStep 2752685 = 1032257) (by norm_num)
theorem B2064577 : Blo 1833618 2064577 := bbase (se 2 (by rfl) ⟨774216, by rfl⟩ : syracuseStep 2064577 = 1548433) (by norm_num)
theorem B4128965 : Blo 1833618 4128965 := bbase (se 4 (by rfl) ⟨387090, by rfl⟩ : syracuseStep 4128965 = 774181) (by norm_num)
theorem B2752709 : Blo 1833618 2752709 := bbase (se 4 (by rfl) ⟨258066, by rfl⟩ : syracuseStep 2752709 = 516133) (by norm_num)
theorem B2752733 : Blo 1833618 2752733 := bbase (se 3 (by rfl) ⟨516137, by rfl⟩ : syracuseStep 2752733 = 1032275) (by norm_num)
theorem B3096805 : Blo 1833618 3096805 := bbase (se 4 (by rfl) ⟨290325, by rfl⟩ : syracuseStep 3096805 = 580651) (by norm_num)
theorem B2064613 : Blo 1833618 2064613 := bbase (se 4 (by rfl) ⟨193557, by rfl⟩ : syracuseStep 2064613 = 387115) (by norm_num)
theorem B2752757 : Blo 1833618 2752757 := bbase (se 5 (by rfl) ⟨129035, by rfl⟩ : syracuseStep 2752757 = 258071) (by norm_num)
theorem B2064649 : Blo 1833618 2064649 := bbase (se 2 (by rfl) ⟨774243, by rfl⟩ : syracuseStep 2064649 = 1548487) (by norm_num)
theorem B4129037 : Blo 1833618 4129037 := bbase (se 3 (by rfl) ⟨774194, by rfl⟩ : syracuseStep 4129037 = 1548389) (by norm_num)
theorem B2752781 : Blo 1833618 2752781 := bbase (se 3 (by rfl) ⟨516146, by rfl⟩ : syracuseStep 2752781 = 1032293) (by norm_num)
theorem B20906261 : Blo 1833618 20906261 := bbase (se 6 (by rfl) ⟨489990, by rfl⟩ : syracuseStep 20906261 = 979981) (by norm_num)
theorem B2752805 : Blo 1833618 2752805 := bbase (se 4 (by rfl) ⟨258075, by rfl⟩ : syracuseStep 2752805 = 516151) (by norm_num)
theorem B2064685 : Blo 1833618 2064685 := bbase (se 3 (by rfl) ⟨387128, by rfl⟩ : syracuseStep 2064685 = 774257) (by norm_num)
theorem B3096893 : Blo 1833618 3096893 := bbase (se 3 (by rfl) ⟨580667, by rfl⟩ : syracuseStep 3096893 = 1161335) (by norm_num)
theorem B2752829 : Blo 1833618 2752829 := bbase (se 3 (by rfl) ⟨516155, by rfl⟩ : syracuseStep 2752829 = 1032311) (by norm_num)
theorem B2064721 : Blo 1833618 2064721 := bbase (se 2 (by rfl) ⟨774270, by rfl⟩ : syracuseStep 2064721 = 1548541) (by norm_num)
theorem B4129109 : Blo 1833618 4129109 := bbase (se 10 (by rfl) ⟨6048, by rfl⟩ : syracuseStep 4129109 = 12097) (by norm_num)
theorem B2752853 : Blo 1833618 2752853 := bbase (se 10 (by rfl) ⟨4032, by rfl⟩ : syracuseStep 2752853 = 8065) (by norm_num)
theorem B2752877 : Blo 1833618 2752877 := bbase (se 3 (by rfl) ⟨516164, by rfl⟩ : syracuseStep 2752877 = 1032329) (by norm_num)
theorem B2064757 : Blo 1833618 2064757 := bbase (se 5 (by rfl) ⟨96785, by rfl⟩ : syracuseStep 2064757 = 193571) (by norm_num)
theorem B2752901 : Blo 1833618 2752901 := bbase (se 4 (by rfl) ⟨258084, by rfl⟩ : syracuseStep 2752901 = 516169) (by norm_num)
theorem B17629589 : Blo 1833618 17629589 := bbase (se 6 (by rfl) ⟨413193, by rfl⟩ : syracuseStep 17629589 = 826387) (by norm_num)
theorem B2064793 : Blo 1833618 2064793 := bbase (se 2 (by rfl) ⟨774297, by rfl⟩ : syracuseStep 2064793 = 1548595) (by norm_num)
theorem B4129181 : Blo 1833618 4129181 := bbase (se 3 (by rfl) ⟨774221, by rfl⟩ : syracuseStep 4129181 = 1548443) (by norm_num)
theorem B2752925 : Blo 1833618 2752925 := bbase (se 3 (by rfl) ⟨516173, by rfl⟩ : syracuseStep 2752925 = 1032347) (by norm_num)
theorem B1958305 : Blo 1833618 1958305 := bbase (se 2 (by rfl) ⟨734364, by rfl⟩ : syracuseStep 1958305 = 1468729) (by norm_num)
theorem B2204069 : Blo 1833618 2204069 := bbase (se 4 (by rfl) ⟨206631, by rfl⟩ : syracuseStep 2204069 = 413263) (by norm_num)
theorem B2752949 : Blo 1833618 2752949 := bbase (se 5 (by rfl) ⟨129044, by rfl⟩ : syracuseStep 2752949 = 258089) (by norm_num)
theorem B4645309 : Blo 1833618 4645309 := bbase (se 3 (by rfl) ⟨870995, by rfl⟩ : syracuseStep 4645309 = 1741991) (by norm_num)
theorem B3097021 : Blo 1833618 3097021 := bbase (se 3 (by rfl) ⟨580691, by rfl⟩ : syracuseStep 3097021 = 1161383) (by norm_num)
theorem B2064829 : Blo 1833618 2064829 := bbase (se 3 (by rfl) ⟨387155, by rfl⟩ : syracuseStep 2064829 = 774311) (by norm_num)
theorem B1860041 : Blo 1833618 1860041 := bbase (se 2 (by rfl) ⟨697515, by rfl⟩ : syracuseStep 1860041 = 1395031) (by norm_num)
theorem B2752973 : Blo 1833618 2752973 := bbase (se 3 (by rfl) ⟨516182, by rfl⟩ : syracuseStep 2752973 = 1032365) (by norm_num)
theorem B1958365 : Blo 1833618 1958365 := bbase (se 3 (by rfl) ⟨367193, by rfl⟩ : syracuseStep 1958365 = 734387) (by norm_num)
theorem B2064865 : Blo 1833618 2064865 := bbase (se 2 (by rfl) ⟨774324, by rfl⟩ : syracuseStep 2064865 = 1548649) (by norm_num)
theorem B9290213 : Blo 1833618 9290213 := bbase (se 4 (by rfl) ⟨870957, by rfl⟩ : syracuseStep 9290213 = 1741915) (by norm_num)
theorem B6193637 : Blo 1833618 6193637 := bbase (se 4 (by rfl) ⟨580653, by rfl⟩ : syracuseStep 6193637 = 1161307) (by norm_num)
theorem B4129253 : Blo 1833618 4129253 := bbase (se 4 (by rfl) ⟨387117, by rfl⟩ : syracuseStep 4129253 = 774235) (by norm_num)
theorem B2752997 : Blo 1833618 2752997 := bbase (se 4 (by rfl) ⟨258093, by rfl⟩ : syracuseStep 2752997 = 516187) (by norm_num)
theorem B2753021 : Blo 1833618 2753021 := bbase (se 3 (by rfl) ⟨516191, by rfl⟩ : syracuseStep 2753021 = 1032383) (by norm_num)
theorem B2064901 : Blo 1833618 2064901 := bbase (se 4 (by rfl) ⟨193584, by rfl⟩ : syracuseStep 2064901 = 387169) (by norm_num)
theorem B3097109 : Blo 1833618 3097109 := bbase (se 6 (by rfl) ⟨72588, by rfl⟩ : syracuseStep 3097109 = 145177) (by norm_num)
theorem B2753045 : Blo 1833618 2753045 := bbase (se 6 (by rfl) ⟨64524, by rfl⟩ : syracuseStep 2753045 = 129049) (by norm_num)
theorem B2204185 : Blo 1833618 2204185 := bbase (se 2 (by rfl) ⟨826569, by rfl⟩ : syracuseStep 2204185 = 1653139) (by norm_num)
theorem B2064937 : Blo 1833618 2064937 := bbase (se 2 (by rfl) ⟨774351, by rfl⟩ : syracuseStep 2064937 = 1548703) (by norm_num)
theorem B4645421 : Blo 1833618 4645421 := bbase (se 3 (by rfl) ⟨871016, by rfl⟩ : syracuseStep 4645421 = 1742033) (by norm_num)
theorem B4129325 : Blo 1833618 4129325 := bbase (se 3 (by rfl) ⟨774248, by rfl⟩ : syracuseStep 4129325 = 1548497) (by norm_num)
theorem B2753069 : Blo 1833618 2753069 := bbase (se 3 (by rfl) ⟨516200, by rfl⟩ : syracuseStep 2753069 = 1032401) (by norm_num)
theorem B2753093 : Blo 1833618 2753093 := bbase (se 4 (by rfl) ⟨258102, by rfl⟩ : syracuseStep 2753093 = 516205) (by norm_num)
theorem B2064973 : Blo 1833618 2064973 := bbase (se 3 (by rfl) ⟨387182, by rfl⟩ : syracuseStep 2064973 = 774365) (by norm_num)
theorem B2753117 : Blo 1833618 2753117 := bbase (se 3 (by rfl) ⟨516209, by rfl⟩ : syracuseStep 2753117 = 1032419) (by norm_num)
theorem B2065009 : Blo 1833618 2065009 := bbase (se 2 (by rfl) ⟨774378, by rfl⟩ : syracuseStep 2065009 = 1548757) (by norm_num)
theorem B4129397 : Blo 1833618 4129397 := bbase (se 5 (by rfl) ⟨193565, by rfl⟩ : syracuseStep 4129397 = 387131) (by norm_num)
theorem B2753141 : Blo 1833618 2753141 := bbase (se 5 (by rfl) ⟨129053, by rfl⟩ : syracuseStep 2753141 = 258107) (by norm_num)
theorem B2753165 : Blo 1833618 2753165 := bbase (se 3 (by rfl) ⟨516218, by rfl⟩ : syracuseStep 2753165 = 1032437) (by norm_num)
theorem B3097237 : Blo 1833618 3097237 := bbase (se 6 (by rfl) ⟨72591, by rfl⟩ : syracuseStep 3097237 = 145183) (by norm_num)
theorem B2065045 : Blo 1833618 2065045 := bbase (se 6 (by rfl) ⟨48399, by rfl⟩ : syracuseStep 2065045 = 96799) (by norm_num)
theorem B2753189 : Blo 1833618 2753189 := bbase (se 4 (by rfl) ⟨258111, by rfl⟩ : syracuseStep 2753189 = 516223) (by norm_num)
theorem B4129469 : Blo 1833618 4129469 := bbase (se 3 (by rfl) ⟨774275, by rfl⟩ : syracuseStep 4129469 = 1548551) (by norm_num)
theorem B2753213 : Blo 1833618 2753213 := bbase (se 3 (by rfl) ⟨516227, by rfl⟩ : syracuseStep 2753213 = 1032455) (by norm_num)
theorem B4408013 : Blo 1833618 4408013 := bbase (se 3 (by rfl) ⟨826502, by rfl⟩ : syracuseStep 4408013 = 1653005) (by norm_num)
theorem B2753237 : Blo 1833618 2753237 := bbase (se 7 (by rfl) ⟨32264, by rfl⟩ : syracuseStep 2753237 = 64529) (by norm_num)
theorem B2204381 : Blo 1833618 2204381 := bbase (se 3 (by rfl) ⟨413321, by rfl⟩ : syracuseStep 2204381 = 826643) (by norm_num)
theorem B3916525 : Blo 1833618 3916525 := bbase (se 3 (by rfl) ⟨734348, by rfl⟩ : syracuseStep 3916525 = 1468697) (by norm_num)
theorem B4645613 : Blo 1833618 4645613 := bbase (se 3 (by rfl) ⟨871052, by rfl⟩ : syracuseStep 4645613 = 1742105) (by norm_num)
theorem B3097325 : Blo 1833618 3097325 := bbase (se 3 (by rfl) ⟨580748, by rfl⟩ : syracuseStep 3097325 = 1161497) (by norm_num)
theorem B2753261 : Blo 1833618 2753261 := bbase (se 3 (by rfl) ⟨516236, by rfl⟩ : syracuseStep 2753261 = 1032473) (by norm_num)
theorem B3482365 : Blo 1833618 3482365 := bbase (se 3 (by rfl) ⟨652943, by rfl⟩ : syracuseStep 3482365 = 1305887) (by norm_num)
theorem B4129541 : Blo 1833618 4129541 := bbase (se 4 (by rfl) ⟨387144, by rfl⟩ : syracuseStep 4129541 = 774289) (by norm_num)
theorem B2753285 : Blo 1833618 2753285 := bbase (se 4 (by rfl) ⟨258120, by rfl⟩ : syracuseStep 2753285 = 516241) (by norm_num)
theorem B1958681 : Blo 1833618 1958681 := bbase (se 2 (by rfl) ⟨734505, by rfl⟩ : syracuseStep 1958681 = 1469011) (by norm_num)
theorem B2753309 : Blo 1833618 2753309 := bbase (se 3 (by rfl) ⟨516245, by rfl⟩ : syracuseStep 2753309 = 1032491) (by norm_num)
theorem B2753333 : Blo 1833618 2753333 := bbase (se 5 (by rfl) ⟨129062, by rfl⟩ : syracuseStep 2753333 = 258125) (by norm_num)
theorem B4129613 : Blo 1833618 4129613 := bbase (se 3 (by rfl) ⟨774302, by rfl⟩ : syracuseStep 4129613 = 1548605) (by norm_num)
theorem B2753357 : Blo 1833618 2753357 := bbase (se 3 (by rfl) ⟨516254, by rfl⟩ : syracuseStep 2753357 = 1032509) (by norm_num)
theorem B2753381 : Blo 1833618 2753381 := bbase (se 4 (by rfl) ⟨258129, by rfl⟩ : syracuseStep 2753381 = 516259) (by norm_num)
theorem B3097453 : Blo 1833618 3097453 := bbase (se 3 (by rfl) ⟨580772, by rfl⟩ : syracuseStep 3097453 = 1161545) (by norm_num)
theorem B2753405 : Blo 1833618 2753405 := bbase (se 3 (by rfl) ⟨516263, by rfl⟩ : syracuseStep 2753405 = 1032527) (by norm_num)
theorem B3482509 : Blo 1833618 3482509 := bbase (se 3 (by rfl) ⟨652970, by rfl⟩ : syracuseStep 3482509 = 1305941) (by norm_num)
theorem B6194069 : Blo 1833618 6194069 := bbase (se 6 (by rfl) ⟨145173, by rfl⟩ : syracuseStep 6194069 = 290347) (by norm_num)
theorem B4129685 : Blo 1833618 4129685 := bbase (se 6 (by rfl) ⟨96789, by rfl⟩ : syracuseStep 4129685 = 193579) (by norm_num)
theorem B3097541 : Blo 1833618 3097541 := bbase (se 4 (by rfl) ⟨290394, by rfl⟩ : syracuseStep 3097541 = 580789) (by norm_num)
theorem B4129757 : Blo 1833618 4129757 := bbase (se 3 (by rfl) ⟨774329, by rfl⟩ : syracuseStep 4129757 = 1548659) (by norm_num)
theorem B4129829 : Blo 1833618 4129829 := bbase (se 4 (by rfl) ⟨387171, by rfl⟩ : syracuseStep 4129829 = 774343) (by norm_num)
theorem B3482669 : Blo 1833618 3482669 := bbase (se 3 (by rfl) ⟨653000, by rfl⟩ : syracuseStep 3482669 = 1306001) (by norm_num)
theorem B4645957 : Blo 1833618 4645957 := bbase (se 4 (by rfl) ⟨435558, by rfl⟩ : syracuseStep 4645957 = 871117) (by norm_num)
theorem B4129901 : Blo 1833618 4129901 := bbase (se 3 (by rfl) ⟨774356, by rfl⟩ : syracuseStep 4129901 = 1548713) (by norm_num)
theorem B26461333 : Blo 1833618 26461333 := bbase (se 6 (by rfl) ⟨620187, by rfl⟩ : syracuseStep 26461333 = 1240375) (by norm_num)
theorem B4646069 : Blo 1833618 4646069 := bbase (se 5 (by rfl) ⟨217784, by rfl⟩ : syracuseStep 4646069 = 435569) (by norm_num)
theorem B4129973 : Blo 1833618 4129973 := bbase (se 5 (by rfl) ⟨193592, by rfl⟩ : syracuseStep 4129973 = 387185) (by norm_num)
theorem B3482813 : Blo 1833618 3482813 := bbase (se 3 (by rfl) ⟨653027, by rfl⟩ : syracuseStep 3482813 = 1306055) (by norm_num)
theorem B1959125 : Blo 1833618 1959125 := bbase (se 7 (by rfl) ⟨22958, by rfl⟩ : syracuseStep 1959125 = 45917) (by norm_num)
theorem B4130045 : Blo 1833618 4130045 := bbase (se 3 (by rfl) ⟨774383, by rfl⟩ : syracuseStep 4130045 = 1548767) (by norm_num)
theorem B2204929 : Blo 1833618 2204929 := bbase (se 2 (by rfl) ⟨826848, by rfl⟩ : syracuseStep 2204929 = 1653697) (by norm_num)
theorem B1959185 : Blo 1833618 1959185 := bbase (se 2 (by rfl) ⟨734694, by rfl⟩ : syracuseStep 1959185 = 1469389) (by norm_num)
theorem B6964501 : Blo 1833618 6964501 := bbase (se 6 (by rfl) ⟨163230, by rfl⟩ : syracuseStep 6964501 = 326461) (by norm_num)
theorem B5580085 : Blo 1833618 5580085 := bbase (se 5 (by rfl) ⟨261566, by rfl⟩ : syracuseStep 5580085 = 523133) (by norm_num)
theorem B6194501 : Blo 1833618 6194501 := bbase (se 4 (by rfl) ⟨580734, by rfl⟩ : syracuseStep 6194501 = 1161469) (by norm_num)
theorem B4130117 : Blo 1833618 4130117 := bbase (se 4 (by rfl) ⟨387198, by rfl⟩ : syracuseStep 4130117 = 774397) (by norm_num)
theorem B4408685 : Blo 1833618 4408685 := bbase (se 3 (by rfl) ⟨826628, by rfl⟩ : syracuseStep 4408685 = 1653257) (by norm_num)
theorem B4646261 : Blo 1833618 4646261 := bbase (se 5 (by rfl) ⟨217793, by rfl⟩ : syracuseStep 4646261 = 435587) (by norm_num)
theorem B3138949 : Blo 1833618 3138949 := bbase (se 4 (by rfl) ⟨294276, by rfl⟩ : syracuseStep 3138949 = 588553) (by norm_num)
theorem B1959313 : Blo 1833618 1959313 := bbase (se 2 (by rfl) ⟨734742, by rfl⟩ : syracuseStep 1959313 = 1469485) (by norm_num)
theorem B2205073 : Blo 1833618 2205073 := bbase (se 2 (by rfl) ⟨826902, by rfl⟩ : syracuseStep 2205073 = 1653805) (by norm_num)
theorem B8365525 : Blo 1833618 8365525 := bbase (se 7 (by rfl) ⟨98033, by rfl⟩ : syracuseStep 8365525 = 196067) (by norm_num)
theorem B35743189 : Blo 1833618 35743189 := bbase (se 7 (by rfl) ⟨418865, by rfl⟩ : syracuseStep 35743189 = 837731) (by norm_num)
theorem B3483101 : Blo 1833618 3483101 := bbase (se 3 (by rfl) ⟨653081, by rfl⟩ : syracuseStep 3483101 = 1306163) (by norm_num)
theorem B12895733 : Blo 1833618 12895733 := bbase (se 5 (by rfl) ⟨604487, by rfl⟩ : syracuseStep 12895733 = 1208975) (by norm_num)
theorem B2041357 : Blo 1833618 2041357 := bbase (se 3 (by rfl) ⟨382754, by rfl⟩ : syracuseStep 2041357 = 765509) (by norm_num)
theorem B15664661 : Blo 1833618 15664661 := bbase (se 6 (by rfl) ⟨367140, by rfl⟩ : syracuseStep 15664661 = 734281) (by norm_num)
theorem B9913877 : Blo 1833618 9913877 := bbase (se 6 (by rfl) ⟨232356, by rfl⟩ : syracuseStep 9913877 = 464713) (by norm_num)
theorem B6964805 : Blo 1833618 6964805 := bbase (se 4 (by rfl) ⟨652950, by rfl⟩ : syracuseStep 6964805 = 1305901) (by norm_num)
theorem B4957781 : Blo 1833618 4957781 := bbase (se 8 (by rfl) ⟨29049, by rfl⟩ : syracuseStep 4957781 = 58099) (by norm_num)
theorem B3917413 : Blo 1833618 3917413 := bbase (se 4 (by rfl) ⟨367257, by rfl⟩ : syracuseStep 3917413 = 734515) (by norm_num)
theorem B3483253 : Blo 1833618 3483253 := bbase (se 5 (by rfl) ⟨163277, by rfl⟩ : syracuseStep 3483253 = 326555) (by norm_num)
theorem B2352785 : Blo 1833618 2352785 := bbase (se 2 (by rfl) ⟨882294, by rfl⟩ : syracuseStep 2352785 = 1764589) (by norm_num)
theorem B9914005 : Blo 1833618 9914005 := bbase (se 6 (by rfl) ⟨232359, by rfl⟩ : syracuseStep 9914005 = 464719) (by norm_num)
theorem B8816293 : Blo 1833618 8816293 := bbase (se 4 (by rfl) ⟨826527, by rfl⟩ : syracuseStep 8816293 = 1653055) (by norm_num)
theorem B9291509 : Blo 1833618 9291509 := bbase (se 5 (by rfl) ⟨435539, by rfl⟩ : syracuseStep 9291509 = 871079) (by norm_num)
theorem B6194933 : Blo 1833618 6194933 := bbase (se 5 (by rfl) ⟨290387, by rfl⟩ : syracuseStep 6194933 = 580775) (by norm_num)
theorem B2647829 : Blo 1833618 2647829 := bbase (se 6 (by rfl) ⟨62058, by rfl⟩ : syracuseStep 2647829 = 124117) (by norm_num)
theorem B3139373 : Blo 1833618 3139373 := bbase (se 3 (by rfl) ⟨588632, by rfl⟩ : syracuseStep 3139373 = 1177265) (by norm_num)
theorem B1959757 : Blo 1833618 1959757 := bbase (se 3 (by rfl) ⟨367454, by rfl⟩ : syracuseStep 1959757 = 734909) (by norm_num)
theorem B3483557 : Blo 1833618 3483557 := bbase (se 4 (by rfl) ⟨326583, by rfl⟩ : syracuseStep 3483557 = 653167) (by norm_num)
theorem B1959877 : Blo 1833618 1959877 := bbase (se 4 (by rfl) ⟨183738, by rfl⟩ : syracuseStep 1959877 = 367477) (by norm_num)
theorem B7153717 : Blo 1833618 7153717 := bbase (se 5 (by rfl) ⟨335330, by rfl⟩ : syracuseStep 7153717 = 670661) (by norm_num)
theorem B7440437 : Blo 1833618 7440437 := bbase (se 5 (by rfl) ⟨348770, by rfl⟩ : syracuseStep 7440437 = 697541) (by norm_num)
theorem B3139661 : Blo 1833618 3139661 := bbase (se 3 (by rfl) ⟨588686, by rfl⟩ : syracuseStep 3139661 = 1177373) (by norm_num)
theorem B3917909 : Blo 1833618 3917909 := bbase (se 8 (by rfl) ⟨22956, by rfl⟩ : syracuseStep 3917909 = 45913) (by norm_num)
theorem B9283733 : Blo 1833618 9283733 := bbase (se 6 (by rfl) ⟨217587, by rfl⟩ : syracuseStep 9283733 = 435175) (by norm_num)
theorem B5875877 : Blo 1833618 5875877 := bbase (se 4 (by rfl) ⟨550863, by rfl⟩ : syracuseStep 5875877 = 1101727) (by norm_num)
theorem B1960129 : Blo 1833618 1960129 := bbase (se 2 (by rfl) ⟨735048, by rfl⟩ : syracuseStep 1960129 = 1470097) (by norm_num)
theorem B1960133 : Blo 1833618 1960133 := bbase (se 4 (by rfl) ⟨183762, by rfl⟩ : syracuseStep 1960133 = 367525) (by norm_num)
theorem B2320741 : Blo 1833618 2320741 := bbase (se 4 (by rfl) ⟨217569, by rfl⟩ : syracuseStep 2320741 = 435139) (by norm_num)
theorem B5294549 : Blo 1833618 5294549 := bbase (se 7 (by rfl) ⟨62045, by rfl⟩ : syracuseStep 5294549 = 124091) (by norm_num)
theorem B19843541 : Blo 1833618 19843541 := bbase (se 7 (by rfl) ⟨232541, by rfl⟩ : syracuseStep 19843541 = 465083) (by norm_num)
theorem B9415157 : Blo 1833618 9415157 := bbase (se 5 (by rfl) ⟨441335, by rfl⟩ : syracuseStep 9415157 = 882671) (by norm_num)
theorem B2320913 : Blo 1833618 2320913 := bbase (se 2 (by rfl) ⟨870342, by rfl⟩ : syracuseStep 2320913 = 1740685) (by norm_num)
theorem B2320969 : Blo 1833618 2320969 := bbase (se 2 (by rfl) ⟨870363, by rfl⟩ : syracuseStep 2320969 = 1740727) (by norm_num)
theorem B7834229 : Blo 1833618 7834229 := bbase (se 5 (by rfl) ⟨367229, by rfl⟩ : syracuseStep 7834229 = 734459) (by norm_num)
theorem B3484309 : Blo 1833618 3484309 := bbase (se 6 (by rfl) ⟨81663, by rfl⟩ : syracuseStep 3484309 = 163327) (by norm_num)
theorem B2321065 : Blo 1833618 2321065 := bbase (se 2 (by rfl) ⟨870399, by rfl⟩ : syracuseStep 2321065 = 1740799) (by norm_num)
theorem B3484453 : Blo 1833618 3484453 := bbase (se 4 (by rfl) ⟨326667, by rfl⟩ : syracuseStep 3484453 = 653335) (by norm_num)
theorem B2321237 : Blo 1833618 2321237 := bbase (se 9 (by rfl) ⟨6800, by rfl⟩ : syracuseStep 2321237 = 13601) (by norm_num)
theorem B2321293 : Blo 1833618 2321293 := bbase (se 3 (by rfl) ⟨435242, by rfl⟩ : syracuseStep 2321293 = 870485) (by norm_num)
theorem B3484613 : Blo 1833618 3484613 := bbase (se 4 (by rfl) ⟨326682, by rfl⟩ : syracuseStep 3484613 = 653365) (by norm_num)
theorem B3918797 : Blo 1833618 3918797 := bbase (se 3 (by rfl) ⟨734774, by rfl⟩ : syracuseStep 3918797 = 1469549) (by norm_num)
theorem B2321389 : Blo 1833618 2321389 := bbase (se 3 (by rfl) ⟨435260, by rfl⟩ : syracuseStep 2321389 = 870521) (by norm_num)
theorem B9292805 : Blo 1833618 9292805 := bbase (se 4 (by rfl) ⟨871200, by rfl⟩ : syracuseStep 9292805 = 1742401) (by norm_num)
theorem B3918917 : Blo 1833618 3918917 := bbase (se 4 (by rfl) ⟨367398, by rfl⟩ : syracuseStep 3918917 = 734797) (by norm_num)
theorem B4410445 : Blo 1833618 4410445 := bbase (se 3 (by rfl) ⟨826958, by rfl⟩ : syracuseStep 4410445 = 1653917) (by norm_num)
theorem B3484757 : Blo 1833618 3484757 := bbase (se 8 (by rfl) ⟨20418, by rfl⟩ : syracuseStep 3484757 = 40837) (by norm_num)
theorem B2321561 : Blo 1833618 2321561 := bbase (se 2 (by rfl) ⟨870585, by rfl⟩ : syracuseStep 2321561 = 1741171) (by norm_num)
theorem B2321617 : Blo 1833618 2321617 := bbase (se 2 (by rfl) ⟨870606, by rfl⟩ : syracuseStep 2321617 = 1741213) (by norm_num)
theorem B5876965 : Blo 1833618 5876965 := bbase (se 4 (by rfl) ⟨550965, by rfl⟩ : syracuseStep 5876965 = 1101931) (by norm_num)
theorem B2321713 : Blo 1833618 2321713 := bbase (se 2 (by rfl) ⟨870642, by rfl⟩ : syracuseStep 2321713 = 1741285) (by norm_num)
theorem B1985941 : Blo 1833618 1985941 := bbase (se 6 (by rfl) ⟨46545, by rfl⟩ : syracuseStep 1985941 = 93091) (by norm_num)
theorem B9285029 : Blo 1833618 9285029 := bbase (se 4 (by rfl) ⟨870471, by rfl⟩ : syracuseStep 9285029 = 1740943) (by norm_num)
theorem B2321885 : Blo 1833618 2321885 := bbase (se 3 (by rfl) ⟨435353, by rfl⟩ : syracuseStep 2321885 = 870707) (by norm_num)
theorem B3304957 : Blo 1833618 3304957 := bbase (se 3 (by rfl) ⟨619679, by rfl⟩ : syracuseStep 3304957 = 1239359) (by norm_num)
theorem B11750933 : Blo 1833618 11750933 := bbase (se 6 (by rfl) ⟨275412, by rfl⟩ : syracuseStep 11750933 = 550825) (by norm_num)
theorem B2321941 : Blo 1833618 2321941 := bbase (se 6 (by rfl) ⟨54420, by rfl⟩ : syracuseStep 2321941 = 108841) (by norm_num)
theorem B7835237 : Blo 1833618 7835237 := bbase (se 4 (by rfl) ⟨734553, by rfl⟩ : syracuseStep 7835237 = 1469107) (by norm_num)
theorem B2322037 : Blo 1833618 2322037 := bbase (se 5 (by rfl) ⟨108845, by rfl⟩ : syracuseStep 2322037 = 217691) (by norm_num)
theorem B6966917 : Blo 1833618 6966917 := bbase (se 4 (by rfl) ⟨653148, by rfl⟩ : syracuseStep 6966917 = 1306297) (by norm_num)
theorem B7057045 : Blo 1833618 7057045 := bbase (se 6 (by rfl) ⟨165399, by rfl⟩ : syracuseStep 7057045 = 330799) (by norm_num)
theorem B2092729 : Blo 1833618 2092729 := bbase (se 2 (by rfl) ⟨784773, by rfl⟩ : syracuseStep 2092729 = 1569547) (by norm_num)
theorem B3919549 : Blo 1833618 3919549 := bbase (se 3 (by rfl) ⟨734915, by rfl⟩ : syracuseStep 3919549 = 1469831) (by norm_num)
theorem B2322209 : Blo 1833618 2322209 := bbase (se 2 (by rfl) ⟨870828, by rfl⟩ : syracuseStep 2322209 = 1741657) (by norm_num)
theorem B6188885 : Blo 1833618 6188885 := bbase (se 9 (by rfl) ⟨18131, by rfl⟩ : syracuseStep 6188885 = 36263) (by norm_num)
theorem B2322265 : Blo 1833618 2322265 := bbase (se 2 (by rfl) ⟨870849, by rfl⟩ : syracuseStep 2322265 = 1741699) (by norm_num)
theorem B1986401 : Blo 1833618 1986401 := bbase (se 2 (by rfl) ⟨744900, by rfl⟩ : syracuseStep 1986401 = 1489801) (by norm_num)
theorem B4771685 : Blo 1833618 4771685 := bbase (se 4 (by rfl) ⟨447345, by rfl⟩ : syracuseStep 4771685 = 894691) (by norm_num)
theorem B6967205 : Blo 1833618 6967205 := bbase (se 4 (by rfl) ⟨653175, by rfl⟩ : syracuseStep 6967205 = 1306351) (by norm_num)
theorem B2322361 : Blo 1833618 2322361 := bbase (se 2 (by rfl) ⟨870885, by rfl⟩ : syracuseStep 2322361 = 1741771) (by norm_num)
theorem B2322533 : Blo 1833618 2322533 := bbase (se 4 (by rfl) ⟨217737, by rfl⟩ : syracuseStep 2322533 = 435475) (by norm_num)
theorem B4182125 : Blo 1833618 4182125 := bbase (se 3 (by rfl) ⟨784148, by rfl⟩ : syracuseStep 4182125 = 1568297) (by norm_num)
theorem B2322589 : Blo 1833618 2322589 := bbase (se 3 (by rfl) ⟨435485, by rfl⟩ : syracuseStep 2322589 = 870971) (by norm_num)
theorem B4182245 : Blo 1833618 4182245 := bbase (se 4 (by rfl) ⟨392085, by rfl⟩ : syracuseStep 4182245 = 784171) (by norm_num)
theorem B2322685 : Blo 1833618 2322685 := bbase (se 3 (by rfl) ⟨435503, by rfl⟩ : syracuseStep 2322685 = 871007) (by norm_num)
theorem B6189317 : Blo 1833618 6189317 := bbase (se 4 (by rfl) ⟨580248, by rfl⟩ : syracuseStep 6189317 = 1160497) (by norm_num)
theorem B2789653 : Blo 1833618 2789653 := bbase (se 6 (by rfl) ⟨65382, by rfl⟩ : syracuseStep 2789653 = 130765) (by norm_num)
theorem B13938965 : Blo 1833618 13938965 := bbase (se 6 (by rfl) ⟨326694, by rfl⟩ : syracuseStep 13938965 = 653389) (by norm_num)
theorem B5222693 : Blo 1833618 5222693 := bbase (se 4 (by rfl) ⟨489627, by rfl⟩ : syracuseStep 5222693 = 979255) (by norm_num)
theorem B3305765 : Blo 1833618 3305765 := bbase (se 4 (by rfl) ⟨309915, by rfl⟩ : syracuseStep 3305765 = 619831) (by norm_num)
theorem B4960549 : Blo 1833618 4960549 := bbase (se 4 (by rfl) ⟨465051, by rfl⟩ : syracuseStep 4960549 = 930103) (by norm_num)
theorem B4706677 : Blo 1833618 4706677 := bbase (se 5 (by rfl) ⟨220625, by rfl⟩ : syracuseStep 4706677 = 441251) (by norm_num)
theorem B5878133 : Blo 1833618 5878133 := bbase (se 5 (by rfl) ⟨275537, by rfl⟩ : syracuseStep 5878133 = 551075) (by norm_num)
theorem B2322857 : Blo 1833618 2322857 := bbase (se 2 (by rfl) ⟨871071, by rfl⟩ : syracuseStep 2322857 = 1742143) (by norm_num)
theorem B3305909 : Blo 1833618 3305909 := bbase (se 5 (by rfl) ⟨154964, by rfl⟩ : syracuseStep 3305909 = 309929) (by norm_num)
theorem B2322913 : Blo 1833618 2322913 := bbase (se 2 (by rfl) ⟨871092, by rfl⟩ : syracuseStep 2322913 = 1742185) (by norm_num)
theorem B2323009 : Blo 1833618 2323009 := bbase (se 2 (by rfl) ⟨871128, by rfl⟩ : syracuseStep 2323009 = 1742257) (by norm_num)
theorem B4641421 : Blo 1833618 4641421 := bbase (se 3 (by rfl) ⟨870266, by rfl⟩ : syracuseStep 4641421 = 1740533) (by norm_num)
theorem B11162261 : Blo 1833618 11162261 := bbase (se 6 (by rfl) ⟨261615, by rfl⟩ : syracuseStep 11162261 = 523231) (by norm_num)
theorem B6189749 : Blo 1833618 6189749 := bbase (se 5 (by rfl) ⟨290144, by rfl⟩ : syracuseStep 6189749 = 580289) (by norm_num)
theorem B9286325 : Blo 1833618 9286325 := bbase (se 5 (by rfl) ⟨435296, by rfl⟩ : syracuseStep 9286325 = 870593) (by norm_num)
theorem B13931189 : Blo 1833618 13931189 := bbase (se 5 (by rfl) ⟨653024, by rfl⟩ : syracuseStep 13931189 = 1306049) (by norm_num)
theorem B4707005 : Blo 1833618 4707005 := bbase (se 3 (by rfl) ⟨882563, by rfl⟩ : syracuseStep 4707005 = 1765127) (by norm_num)
theorem B2790109 : Blo 1833618 2790109 := bbase (se 3 (by rfl) ⟨523145, by rfl⟩ : syracuseStep 2790109 = 1046291) (by norm_num)
theorem B2323181 : Blo 1833618 2323181 := bbase (se 3 (by rfl) ⟨435596, by rfl⟩ : syracuseStep 2323181 = 871193) (by norm_num)
theorem B4641533 : Blo 1833618 4641533 := bbase (se 3 (by rfl) ⟨870287, by rfl⟩ : syracuseStep 4641533 = 1740575) (by norm_num)
theorem B2937637 : Blo 1833618 2937637 := bbase (se 4 (by rfl) ⟨275403, by rfl⟩ : syracuseStep 2937637 = 550807) (by norm_num)
theorem B8811413 : Blo 1833618 8811413 := bbase (se 6 (by rfl) ⟨206517, by rfl⟩ : syracuseStep 8811413 = 413035) (by norm_num)
theorem B4641725 : Blo 1833618 4641725 := bbase (se 3 (by rfl) ⟨870323, by rfl⟩ : syracuseStep 4641725 = 1740647) (by norm_num)
theorem B4125653 : Blo 1833618 4125653 := bbase (se 7 (by rfl) ⟨48347, by rfl⟩ : syracuseStep 4125653 = 96695) (by norm_num)
theorem B10187797 : Blo 1833618 10187797 := bbase (se 6 (by rfl) ⟨238776, by rfl⟩ : syracuseStep 10187797 = 477553) (by norm_num)
theorem B4125725 : Blo 1833618 4125725 := bbase (se 3 (by rfl) ⟨773573, by rfl⟩ : syracuseStep 4125725 = 1547147) (by norm_num)
theorem B2233405 : Blo 1833618 2233405 := bbase (se 3 (by rfl) ⟨418763, by rfl⟩ : syracuseStep 2233405 = 837527) (by norm_num)
theorem B6968389 : Blo 1833618 6968389 := bbase (se 4 (by rfl) ⟨653286, by rfl⟩ : syracuseStep 6968389 = 1306573) (by norm_num)
theorem B8811605 : Blo 1833618 8811605 := bbase (se 8 (by rfl) ⟨51630, by rfl⟩ : syracuseStep 8811605 = 103261) (by norm_num)
theorem B4125797 : Blo 1833618 4125797 := bbase (se 4 (by rfl) ⟨386793, by rfl⟩ : syracuseStep 4125797 = 773587) (by norm_num)
theorem B6190181 : Blo 1833618 6190181 := bbase (se 4 (by rfl) ⟨580329, by rfl⟩ : syracuseStep 6190181 = 1160659) (by norm_num)
theorem B3306629 : Blo 1833618 3306629 := bbase (se 4 (by rfl) ⟨309996, by rfl⟩ : syracuseStep 3306629 = 619993) (by norm_num)
theorem B4125869 : Blo 1833618 4125869 := bbase (se 3 (by rfl) ⟨773600, by rfl⟩ : syracuseStep 4125869 = 1547201) (by norm_num)
theorem B4125941 : Blo 1833618 4125941 := bbase (se 5 (by rfl) ⟨193403, by rfl⟩ : syracuseStep 4125941 = 386807) (by norm_num)
theorem B4642069 : Blo 1833618 4642069 := bbase (se 6 (by rfl) ⟨108798, by rfl⟩ : syracuseStep 4642069 = 217597) (by norm_num)
theorem B2479405 : Blo 1833618 2479405 := bbase (se 3 (by rfl) ⟨464888, by rfl⟩ : syracuseStep 2479405 = 929777) (by norm_num)
theorem B4126013 : Blo 1833618 4126013 := bbase (se 3 (by rfl) ⟨773627, by rfl⟩ : syracuseStep 4126013 = 1547255) (by norm_num)
theorem B7837013 : Blo 1833618 7837013 := bbase (se 14 (by rfl) ⟨717, by rfl⟩ : syracuseStep 7837013 = 1435) (by norm_num)
theorem B2233697 : Blo 1833618 2233697 := bbase (se 2 (by rfl) ⟨837636, by rfl⟩ : syracuseStep 2233697 = 1675273) (by norm_num)
theorem B6968693 : Blo 1833618 6968693 := bbase (se 5 (by rfl) ⟨326657, by rfl⟩ : syracuseStep 6968693 = 653315) (by norm_num)
theorem B4126085 : Blo 1833618 4126085 := bbase (se 4 (by rfl) ⟨386820, by rfl⟩ : syracuseStep 4126085 = 773641) (by norm_num)
theorem B4642181 : Blo 1833618 4642181 := bbase (se 4 (by rfl) ⟨435204, by rfl⟩ : syracuseStep 4642181 = 870409) (by norm_num)
theorem B4126157 : Blo 1833618 4126157 := bbase (se 3 (by rfl) ⟨773654, by rfl⟩ : syracuseStep 4126157 = 1547309) (by norm_num)
theorem B8811989 : Blo 1833618 8811989 := bbase (se 7 (by rfl) ⟨103265, by rfl⟩ : syracuseStep 8811989 = 206531) (by norm_num)
theorem B2938349 : Blo 1833618 2938349 := bbase (se 3 (by rfl) ⟨550940, by rfl⟩ : syracuseStep 2938349 = 1101881) (by norm_num)
theorem B4126229 : Blo 1833618 4126229 := bbase (se 6 (by rfl) ⟨96708, by rfl⟩ : syracuseStep 4126229 = 193417) (by norm_num)
theorem B6190613 : Blo 1833618 6190613 := bbase (se 6 (by rfl) ⟨145092, by rfl⟩ : syracuseStep 6190613 = 290185) (by norm_num)
theorem B10737173 : Blo 1833618 10737173 := bbase (se 6 (by rfl) ⟨251652, by rfl⟩ : syracuseStep 10737173 = 503305) (by norm_num)
theorem B4642373 : Blo 1833618 4642373 := bbase (se 4 (by rfl) ⟨435222, by rfl⟩ : syracuseStep 4642373 = 870445) (by norm_num)
theorem B4126301 : Blo 1833618 4126301 := bbase (se 3 (by rfl) ⟨773681, by rfl⟩ : syracuseStep 4126301 = 1547363) (by norm_num)
theorem B4126373 : Blo 1833618 4126373 := bbase (se 4 (by rfl) ⟨386847, by rfl⟩ : syracuseStep 4126373 = 773695) (by norm_num)
theorem B4126445 : Blo 1833618 4126445 := bbase (se 3 (by rfl) ⟨773708, by rfl⟩ : syracuseStep 4126445 = 1547417) (by norm_num)
theorem B6608645 : Blo 1833618 6608645 := bbase (se 4 (by rfl) ⟨619560, by rfl⟩ : syracuseStep 6608645 = 1239121) (by norm_num)
theorem B25098005 : Blo 1833618 25098005 := bbase (se 6 (by rfl) ⟨588234, by rfl⟩ : syracuseStep 25098005 = 1176469) (by norm_num)
theorem B22320917 : Blo 1833618 22320917 := bbase (se 6 (by rfl) ⟨523146, by rfl⟩ : syracuseStep 22320917 = 1046293) (by norm_num)
theorem B3094301 : Blo 1833618 3094301 := bbase (se 3 (by rfl) ⟨580181, by rfl⟩ : syracuseStep 3094301 = 1160363) (by norm_num)
theorem B4126517 : Blo 1833618 4126517 := bbase (se 5 (by rfl) ⟨193430, by rfl⟩ : syracuseStep 4126517 = 386861) (by norm_num)
theorem B5224277 : Blo 1833618 5224277 := bbase (se 9 (by rfl) ⟨15305, by rfl⟩ : syracuseStep 5224277 = 30611) (by norm_num)
theorem B2611045 : Blo 1833618 2611045 := bbase (se 4 (by rfl) ⟨244785, by rfl⟩ : syracuseStep 2611045 = 489571) (by norm_num)
theorem B4126589 : Blo 1833618 4126589 := bbase (se 3 (by rfl) ⟨773735, by rfl⟩ : syracuseStep 4126589 = 1547471) (by norm_num)
theorem B3094429 : Blo 1833618 3094429 := bbase (se 3 (by rfl) ⟨580205, by rfl⟩ : syracuseStep 3094429 = 1160411) (by norm_num)
theorem B4642717 : Blo 1833618 4642717 := bbase (se 3 (by rfl) ⟨870509, by rfl⟩ : syracuseStep 4642717 = 1741019) (by norm_num)
theorem B4126661 : Blo 1833618 4126661 := bbase (se 4 (by rfl) ⟨386874, by rfl⟩ : syracuseStep 4126661 = 773749) (by norm_num)
theorem B6191045 : Blo 1833618 6191045 := bbase (se 4 (by rfl) ⟨580410, by rfl⟩ : syracuseStep 6191045 = 1160821) (by norm_num)
theorem B9287621 : Blo 1833618 9287621 := bbase (se 4 (by rfl) ⟨870714, by rfl⟩ : syracuseStep 9287621 = 1741429) (by norm_num)
theorem B8820677 : Blo 1833618 8820677 := bbase (se 4 (by rfl) ⟨826938, by rfl⟩ : syracuseStep 8820677 = 1653877) (by norm_num)
theorem B2750429 : Blo 1833618 2750429 := bbase (se 3 (by rfl) ⟨515705, by rfl⟩ : syracuseStep 2750429 = 1031411) (by norm_num)
theorem B2750453 : Blo 1833618 2750453 := bbase (se 5 (by rfl) ⟨128927, by rfl⟩ : syracuseStep 2750453 = 257855) (by norm_num)
theorem B3094517 : Blo 1833618 3094517 := bbase (se 5 (by rfl) ⟨145055, by rfl⟩ : syracuseStep 3094517 = 290111) (by norm_num)
theorem B2750477 : Blo 1833618 2750477 := bbase (se 3 (by rfl) ⟨515714, by rfl⟩ : syracuseStep 2750477 = 1031429) (by norm_num)
theorem B4126733 : Blo 1833618 4126733 := bbase (se 3 (by rfl) ⟨773762, by rfl⟩ : syracuseStep 4126733 = 1547525) (by norm_num)
theorem B4642829 : Blo 1833618 4642829 := bbase (se 3 (by rfl) ⟨870530, by rfl⟩ : syracuseStep 4642829 = 1741061) (by norm_num)
theorem B2750501 : Blo 1833618 2750501 := bbase (se 4 (by rfl) ⟨257859, by rfl⟩ : syracuseStep 2750501 = 515719) (by norm_num)
theorem B2750525 : Blo 1833618 2750525 := bbase (se 3 (by rfl) ⟨515723, by rfl⟩ : syracuseStep 2750525 = 1031447) (by norm_num)
theorem B2750549 : Blo 1833618 2750549 := bbase (se 8 (by rfl) ⟨16116, by rfl⟩ : syracuseStep 2750549 = 32233) (by norm_num)
theorem B4126805 : Blo 1833618 4126805 := bbase (se 8 (by rfl) ⟨24180, by rfl⟩ : syracuseStep 4126805 = 48361) (by norm_num)
theorem B2750573 : Blo 1833618 2750573 := bbase (se 3 (by rfl) ⟨515732, by rfl⟩ : syracuseStep 2750573 = 1031465) (by norm_num)
theorem B3094645 : Blo 1833618 3094645 := bbase (se 5 (by rfl) ⟨145061, by rfl⟩ : syracuseStep 3094645 = 290123) (by norm_num)
theorem B2750597 : Blo 1833618 2750597 := bbase (se 4 (by rfl) ⟨257868, by rfl⟩ : syracuseStep 2750597 = 515737) (by norm_num)
theorem B2939021 : Blo 1833618 2939021 := bbase (se 3 (by rfl) ⟨551066, by rfl⟩ : syracuseStep 2939021 = 1102133) (by norm_num)
theorem B2750621 : Blo 1833618 2750621 := bbase (se 3 (by rfl) ⟨515741, by rfl⟩ : syracuseStep 2750621 = 1031483) (by norm_num)
theorem B4126877 : Blo 1833618 4126877 := bbase (se 3 (by rfl) ⟨773789, by rfl⟩ : syracuseStep 4126877 = 1547579) (by norm_num)
theorem B2750645 : Blo 1833618 2750645 := bbase (se 5 (by rfl) ⟨128936, by rfl⟩ : syracuseStep 2750645 = 257873) (by norm_num)
theorem B2611381 : Blo 1833618 2611381 := bbase (se 5 (by rfl) ⟨122408, by rfl⟩ : syracuseStep 2611381 = 244817) (by norm_num)
theorem B5879989 : Blo 1833618 5879989 := bbase (se 5 (by rfl) ⟨275624, by rfl⟩ : syracuseStep 5879989 = 551249) (by norm_num)
theorem B2750669 : Blo 1833618 2750669 := bbase (se 3 (by rfl) ⟨515750, by rfl⟩ : syracuseStep 2750669 = 1031501) (by norm_num)
theorem B3094733 : Blo 1833618 3094733 := bbase (se 3 (by rfl) ⟨580262, by rfl⟩ : syracuseStep 3094733 = 1160525) (by norm_num)
theorem B4643021 : Blo 1833618 4643021 := bbase (se 3 (by rfl) ⟨870566, by rfl⟩ : syracuseStep 4643021 = 1741133) (by norm_num)
theorem B2750693 : Blo 1833618 2750693 := bbase (se 4 (by rfl) ⟨257877, by rfl⟩ : syracuseStep 2750693 = 515755) (by norm_num)
theorem B4126949 : Blo 1833618 4126949 := bbase (se 4 (by rfl) ⟨386901, by rfl⟩ : syracuseStep 4126949 = 773803) (by norm_num)
theorem B2750717 : Blo 1833618 2750717 := bbase (se 3 (by rfl) ⟨515759, by rfl⟩ : syracuseStep 2750717 = 1031519) (by norm_num)
theorem B2750741 : Blo 1833618 2750741 := bbase (se 6 (by rfl) ⟨64470, by rfl⟩ : syracuseStep 2750741 = 128941) (by norm_num)
theorem B31357205 : Blo 1833618 31357205 := bbase (se 6 (by rfl) ⟨734934, by rfl⟩ : syracuseStep 31357205 = 1469869) (by norm_num)
theorem B2750765 : Blo 1833618 2750765 := bbase (se 3 (by rfl) ⟨515768, by rfl⟩ : syracuseStep 2750765 = 1031537) (by norm_num)
theorem B4127021 : Blo 1833618 4127021 := bbase (se 3 (by rfl) ⟨773816, by rfl⟩ : syracuseStep 4127021 = 1547633) (by norm_num)
theorem B11155765 : Blo 1833618 11155765 := bbase (se 5 (by rfl) ⟨522926, by rfl⟩ : syracuseStep 11155765 = 1045853) (by norm_num)
theorem B2750789 : Blo 1833618 2750789 := bbase (se 4 (by rfl) ⟨257886, by rfl⟩ : syracuseStep 2750789 = 515773) (by norm_num)
theorem B3094861 : Blo 1833618 3094861 := bbase (se 3 (by rfl) ⟨580286, by rfl⟩ : syracuseStep 3094861 = 1160573) (by norm_num)
theorem B3717461 : Blo 1833618 3717461 := bbase (se 10 (by rfl) ⟨5445, by rfl⟩ : syracuseStep 3717461 = 10891) (by norm_num)
theorem B2750813 : Blo 1833618 2750813 := bbase (se 3 (by rfl) ⟨515777, by rfl⟩ : syracuseStep 2750813 = 1031555) (by norm_num)
theorem B2750837 : Blo 1833618 2750837 := bbase (se 5 (by rfl) ⟨128945, by rfl⟩ : syracuseStep 2750837 = 257891) (by norm_num)
theorem B4127093 : Blo 1833618 4127093 := bbase (se 5 (by rfl) ⟨193457, by rfl⟩ : syracuseStep 4127093 = 386915) (by norm_num)
theorem B6191477 : Blo 1833618 6191477 := bbase (se 5 (by rfl) ⟨290225, by rfl⟩ : syracuseStep 6191477 = 580451) (by norm_num)
theorem B2750861 : Blo 1833618 2750861 := bbase (se 3 (by rfl) ⟨515786, by rfl⟩ : syracuseStep 2750861 = 1031573) (by norm_num)
theorem B2611597 : Blo 1833618 2611597 := bbase (se 3 (by rfl) ⟨489674, by rfl⟩ : syracuseStep 2611597 = 979349) (by norm_num)
theorem B2750885 : Blo 1833618 2750885 := bbase (se 4 (by rfl) ⟨257895, by rfl⟩ : syracuseStep 2750885 = 515791) (by norm_num)
theorem B3094949 : Blo 1833618 3094949 := bbase (se 4 (by rfl) ⟨290151, by rfl⟩ : syracuseStep 3094949 = 580303) (by norm_num)
theorem B2750909 : Blo 1833618 2750909 := bbase (se 3 (by rfl) ⟨515795, by rfl⟩ : syracuseStep 2750909 = 1031591) (by norm_num)
theorem B4127165 : Blo 1833618 4127165 := bbase (se 3 (by rfl) ⟨773843, by rfl⟩ : syracuseStep 4127165 = 1547687) (by norm_num)
theorem B4708813 : Blo 1833618 4708813 := bbase (se 3 (by rfl) ⟨882902, by rfl⟩ : syracuseStep 4708813 = 1765805) (by norm_num)
theorem B2750933 : Blo 1833618 2750933 := bbase (se 7 (by rfl) ⟨32237, by rfl⟩ : syracuseStep 2750933 = 64475) (by norm_num)
theorem B2750957 : Blo 1833618 2750957 := bbase (se 3 (by rfl) ⟨515804, by rfl⟩ : syracuseStep 2750957 = 1031609) (by norm_num)
theorem B5224949 : Blo 1833618 5224949 := bbase (se 5 (by rfl) ⟨244919, by rfl⟩ : syracuseStep 5224949 = 489839) (by norm_num)
theorem B2062849 : Blo 1833618 2062849 := bbase (se 2 (by rfl) ⟨773568, by rfl⟩ : syracuseStep 2062849 = 1547137) (by norm_num)
theorem B2234881 : Blo 1833618 2234881 := bbase (se 2 (by rfl) ⟨838080, by rfl⟩ : syracuseStep 2234881 = 1676161) (by norm_num)
theorem B2750981 : Blo 1833618 2750981 := bbase (se 4 (by rfl) ⟨257904, by rfl⟩ : syracuseStep 2750981 = 515809) (by norm_num)
theorem B4127237 : Blo 1833618 4127237 := bbase (se 4 (by rfl) ⟨386928, by rfl⟩ : syracuseStep 4127237 = 773857) (by norm_num)
theorem B2751005 : Blo 1833618 2751005 := bbase (se 3 (by rfl) ⟨515813, by rfl⟩ : syracuseStep 2751005 = 1031627) (by norm_num)
theorem B2062885 : Blo 1833618 2062885 := bbase (se 4 (by rfl) ⟨193395, by rfl⟩ : syracuseStep 2062885 = 386791) (by norm_num)
theorem B3095077 : Blo 1833618 3095077 := bbase (se 4 (by rfl) ⟨290163, by rfl⟩ : syracuseStep 3095077 = 580327) (by norm_num)
theorem B4643365 : Blo 1833618 4643365 := bbase (se 4 (by rfl) ⟨435315, by rfl⟩ : syracuseStep 4643365 = 870631) (by norm_num)
theorem B2751029 : Blo 1833618 2751029 := bbase (se 5 (by rfl) ⟨128954, by rfl⟩ : syracuseStep 2751029 = 257909) (by norm_num)
theorem B13220405 : Blo 1833618 13220405 := bbase (se 5 (by rfl) ⟨619706, by rfl⟩ : syracuseStep 13220405 = 1239413) (by norm_num)
theorem B2062921 : Blo 1833618 2062921 := bbase (se 2 (by rfl) ⟨773595, by rfl⟩ : syracuseStep 2062921 = 1547191) (by norm_num)
theorem B2751053 : Blo 1833618 2751053 := bbase (se 3 (by rfl) ⟨515822, by rfl⟩ : syracuseStep 2751053 = 1031645) (by norm_num)
theorem B4127309 : Blo 1833618 4127309 := bbase (se 3 (by rfl) ⟨773870, by rfl⟩ : syracuseStep 4127309 = 1547741) (by norm_num)
theorem B2751077 : Blo 1833618 2751077 := bbase (se 4 (by rfl) ⟨257913, by rfl⟩ : syracuseStep 2751077 = 515827) (by norm_num)
theorem B2062957 : Blo 1833618 2062957 := bbase (se 3 (by rfl) ⟨386804, by rfl⟩ : syracuseStep 2062957 = 773609) (by norm_num)
theorem B2751101 : Blo 1833618 2751101 := bbase (se 3 (by rfl) ⟨515831, by rfl⟩ : syracuseStep 2751101 = 1031663) (by norm_num)
theorem B3095165 : Blo 1833618 3095165 := bbase (se 3 (by rfl) ⟨580343, by rfl⟩ : syracuseStep 3095165 = 1160687) (by norm_num)
theorem B2939533 : Blo 1833618 2939533 := bbase (se 3 (by rfl) ⟨551162, by rfl⟩ : syracuseStep 2939533 = 1102325) (by norm_num)
theorem B2062993 : Blo 1833618 2062993 := bbase (se 2 (by rfl) ⟨773622, by rfl⟩ : syracuseStep 2062993 = 1547245) (by norm_num)
theorem B4405909 : Blo 1833618 4405909 := bbase (se 6 (by rfl) ⟨103263, by rfl⟩ : syracuseStep 4405909 = 206527) (by norm_num)
theorem B2751125 : Blo 1833618 2751125 := bbase (se 6 (by rfl) ⟨64479, by rfl⟩ : syracuseStep 2751125 = 128959) (by norm_num)
theorem B4127381 : Blo 1833618 4127381 := bbase (se 6 (by rfl) ⟨96735, by rfl⟩ : syracuseStep 4127381 = 193471) (by norm_num)
theorem B4643477 : Blo 1833618 4643477 := bbase (se 6 (by rfl) ⟨108831, by rfl⟩ : syracuseStep 4643477 = 217663) (by norm_num)
theorem B2751149 : Blo 1833618 2751149 := bbase (se 3 (by rfl) ⟨515840, by rfl⟩ : syracuseStep 2751149 = 1031681) (by norm_num)
theorem B2063029 : Blo 1833618 2063029 := bbase (se 5 (by rfl) ⟨96704, by rfl⟩ : syracuseStep 2063029 = 193409) (by norm_num)
theorem B2751173 : Blo 1833618 2751173 := bbase (se 4 (by rfl) ⟨257922, by rfl⟩ : syracuseStep 2751173 = 515845) (by norm_num)
theorem B2063065 : Blo 1833618 2063065 := bbase (se 2 (by rfl) ⟨773649, by rfl⟩ : syracuseStep 2063065 = 1547299) (by norm_num)
theorem B2751197 : Blo 1833618 2751197 := bbase (se 3 (by rfl) ⟨515849, by rfl⟩ : syracuseStep 2751197 = 1031699) (by norm_num)
theorem B4127453 : Blo 1833618 4127453 := bbase (se 3 (by rfl) ⟨773897, by rfl⟩ : syracuseStep 4127453 = 1547795) (by norm_num)
theorem B2751221 : Blo 1833618 2751221 := bbase (se 5 (by rfl) ⟨128963, by rfl⟩ : syracuseStep 2751221 = 257927) (by norm_num)
theorem B2063101 : Blo 1833618 2063101 := bbase (se 3 (by rfl) ⟨386831, by rfl⟩ : syracuseStep 2063101 = 773663) (by norm_num)
theorem B3095293 : Blo 1833618 3095293 := bbase (se 3 (by rfl) ⟨580367, by rfl⟩ : syracuseStep 3095293 = 1160735) (by norm_num)
theorem B2611973 : Blo 1833618 2611973 := bbase (se 4 (by rfl) ⟨244872, by rfl⟩ : syracuseStep 2611973 = 489745) (by norm_num)
theorem B2751245 : Blo 1833618 2751245 := bbase (se 3 (by rfl) ⟨515858, by rfl⟩ : syracuseStep 2751245 = 1031717) (by norm_num)
theorem B4299541 : Blo 1833618 4299541 := bbase (se 6 (by rfl) ⟨100770, by rfl⟩ : syracuseStep 4299541 = 201541) (by norm_num)
theorem B8370965 : Blo 1833618 8370965 := bbase (se 6 (by rfl) ⟨196194, by rfl⟩ : syracuseStep 8370965 = 392389) (by norm_num)
theorem B2063137 : Blo 1833618 2063137 := bbase (se 2 (by rfl) ⟨773676, by rfl⟩ : syracuseStep 2063137 = 1547353) (by norm_num)
theorem B2751269 : Blo 1833618 2751269 := bbase (se 4 (by rfl) ⟨257931, by rfl⟩ : syracuseStep 2751269 = 515863) (by norm_num)
theorem B4127525 : Blo 1833618 4127525 := bbase (se 4 (by rfl) ⟨386955, by rfl⟩ : syracuseStep 4127525 = 773911) (by norm_num)
theorem B6191909 : Blo 1833618 6191909 := bbase (se 4 (by rfl) ⟨580491, by rfl⟩ : syracuseStep 6191909 = 1160983) (by norm_num)
theorem B2751293 : Blo 1833618 2751293 := bbase (se 3 (by rfl) ⟨515867, by rfl⟩ : syracuseStep 2751293 = 1031735) (by norm_num)
theorem B2063173 : Blo 1833618 2063173 := bbase (se 4 (by rfl) ⟨193422, by rfl⟩ : syracuseStep 2063173 = 386845) (by norm_num)
theorem B2751317 : Blo 1833618 2751317 := bbase (se 9 (by rfl) ⟨8060, by rfl⟩ : syracuseStep 2751317 = 16121) (by norm_num)
theorem B3095381 : Blo 1833618 3095381 := bbase (se 9 (by rfl) ⟨9068, by rfl⟩ : syracuseStep 3095381 = 18137) (by norm_num)
theorem B4643669 : Blo 1833618 4643669 := bbase (se 9 (by rfl) ⟨13604, by rfl⟩ : syracuseStep 4643669 = 27209) (by norm_num)
theorem B2063209 : Blo 1833618 2063209 := bbase (se 2 (by rfl) ⟨773703, by rfl⟩ : syracuseStep 2063209 = 1547407) (by norm_num)
theorem B2751341 : Blo 1833618 2751341 := bbase (se 3 (by rfl) ⟨515876, by rfl⟩ : syracuseStep 2751341 = 1031753) (by norm_num)
theorem B4127597 : Blo 1833618 4127597 := bbase (se 3 (by rfl) ⟨773924, by rfl⟩ : syracuseStep 4127597 = 1547849) (by norm_num)
theorem B2751365 : Blo 1833618 2751365 := bbase (se 4 (by rfl) ⟨257940, by rfl⟩ : syracuseStep 2751365 = 515881) (by norm_num)
theorem B2063245 : Blo 1833618 2063245 := bbase (se 3 (by rfl) ⟨386858, by rfl⟩ : syracuseStep 2063245 = 773717) (by norm_num)
theorem B2751389 : Blo 1833618 2751389 := bbase (se 3 (by rfl) ⟨515885, by rfl⟩ : syracuseStep 2751389 = 1031771) (by norm_num)
theorem B5225381 : Blo 1833618 5225381 := bbase (se 4 (by rfl) ⟨489879, by rfl⟩ : syracuseStep 5225381 = 979759) (by norm_num)
theorem B2063281 : Blo 1833618 2063281 := bbase (se 2 (by rfl) ⟨773730, by rfl⟩ : syracuseStep 2063281 = 1547461) (by norm_num)
theorem B2751413 : Blo 1833618 2751413 := bbase (se 5 (by rfl) ⟨128972, by rfl⟩ : syracuseStep 2751413 = 257945) (by norm_num)
theorem B4127669 : Blo 1833618 4127669 := bbase (se 5 (by rfl) ⟨193484, by rfl⟩ : syracuseStep 4127669 = 386969) (by norm_num)
theorem B2751437 : Blo 1833618 2751437 := bbase (se 3 (by rfl) ⟨515894, by rfl⟩ : syracuseStep 2751437 = 1031789) (by norm_num)
theorem B2063317 : Blo 1833618 2063317 := bbase (se 7 (by rfl) ⟨24179, by rfl⟩ : syracuseStep 2063317 = 48359) (by norm_num)
theorem B3095509 : Blo 1833618 3095509 := bbase (se 7 (by rfl) ⟨36275, by rfl⟩ : syracuseStep 3095509 = 72551) (by norm_num)
theorem B2751461 : Blo 1833618 2751461 := bbase (se 4 (by rfl) ⟨257949, by rfl⟩ : syracuseStep 2751461 = 515899) (by norm_num)
theorem B6364133 : Blo 1833618 6364133 := bbase (se 4 (by rfl) ⟨596637, by rfl⟩ : syracuseStep 6364133 = 1193275) (by norm_num)
theorem B2063353 : Blo 1833618 2063353 := bbase (se 2 (by rfl) ⟨773757, by rfl⟩ : syracuseStep 2063353 = 1547515) (by norm_num)
theorem B2751485 : Blo 1833618 2751485 := bbase (se 3 (by rfl) ⟨515903, by rfl⟩ : syracuseStep 2751485 = 1031807) (by norm_num)
theorem B4127741 : Blo 1833618 4127741 := bbase (se 3 (by rfl) ⟨773951, by rfl⟩ : syracuseStep 4127741 = 1547903) (by norm_num)
theorem B2751509 : Blo 1833618 2751509 := bbase (se 6 (by rfl) ⟨64488, by rfl⟩ : syracuseStep 2751509 = 128977) (by norm_num)
theorem B2063389 : Blo 1833618 2063389 := bbase (se 3 (by rfl) ⟨386885, by rfl⟩ : syracuseStep 2063389 = 773771) (by norm_num)
theorem B2751533 : Blo 1833618 2751533 := bbase (se 3 (by rfl) ⟨515912, by rfl⟩ : syracuseStep 2751533 = 1031825) (by norm_num)
theorem B3095597 : Blo 1833618 3095597 := bbase (se 3 (by rfl) ⟨580424, by rfl⟩ : syracuseStep 3095597 = 1160849) (by norm_num)
theorem B2063425 : Blo 1833618 2063425 := bbase (se 2 (by rfl) ⟨773784, by rfl⟩ : syracuseStep 2063425 = 1547569) (by norm_num)
theorem B2751557 : Blo 1833618 2751557 := bbase (se 4 (by rfl) ⟨257958, by rfl⟩ : syracuseStep 2751557 = 515917) (by norm_num)
theorem B4127813 : Blo 1833618 4127813 := bbase (se 4 (by rfl) ⟨386982, by rfl⟩ : syracuseStep 4127813 = 773965) (by norm_num)
theorem B2939989 : Blo 1833618 2939989 := bbase (se 8 (by rfl) ⟨17226, by rfl⟩ : syracuseStep 2939989 = 34453) (by norm_num)
theorem B2751581 : Blo 1833618 2751581 := bbase (se 3 (by rfl) ⟨515921, by rfl⟩ : syracuseStep 2751581 = 1031843) (by norm_num)
theorem B2063461 : Blo 1833618 2063461 := bbase (se 4 (by rfl) ⟨193449, by rfl⟩ : syracuseStep 2063461 = 386899) (by norm_num)
theorem B13220981 : Blo 1833618 13220981 := bbase (se 5 (by rfl) ⟨619733, by rfl⟩ : syracuseStep 13220981 = 1239467) (by norm_num)
theorem B2751605 : Blo 1833618 2751605 := bbase (se 5 (by rfl) ⟨128981, by rfl⟩ : syracuseStep 2751605 = 257963) (by norm_num)
theorem B7158901 : Blo 1833618 7158901 := bbase (se 5 (by rfl) ⟨335573, by rfl⟩ : syracuseStep 7158901 = 671147) (by norm_num)
theorem B2063497 : Blo 1833618 2063497 := bbase (se 2 (by rfl) ⟨773811, by rfl⟩ : syracuseStep 2063497 = 1547623) (by norm_num)
theorem B2751629 : Blo 1833618 2751629 := bbase (se 3 (by rfl) ⟨515930, by rfl⟩ : syracuseStep 2751629 = 1031861) (by norm_num)
theorem B4127885 : Blo 1833618 4127885 := bbase (se 3 (by rfl) ⟨773978, by rfl⟩ : syracuseStep 4127885 = 1547957) (by norm_num)
theorem B2751653 : Blo 1833618 2751653 := bbase (se 4 (by rfl) ⟨257967, by rfl⟩ : syracuseStep 2751653 = 515935) (by norm_num)
theorem B2063533 : Blo 1833618 2063533 := bbase (se 3 (by rfl) ⟨386912, by rfl⟩ : syracuseStep 2063533 = 773825) (by norm_num)
theorem B3095725 : Blo 1833618 3095725 := bbase (se 3 (by rfl) ⟨580448, by rfl⟩ : syracuseStep 3095725 = 1160897) (by norm_num)
theorem B4644013 : Blo 1833618 4644013 := bbase (se 3 (by rfl) ⟨870752, by rfl⟩ : syracuseStep 4644013 = 1741505) (by norm_num)
theorem B2751677 : Blo 1833618 2751677 := bbase (se 3 (by rfl) ⟨515939, by rfl⟩ : syracuseStep 2751677 = 1031879) (by norm_num)
theorem B2063569 : Blo 1833618 2063569 := bbase (se 2 (by rfl) ⟨773838, by rfl⟩ : syracuseStep 2063569 = 1547677) (by norm_num)
theorem B2751701 : Blo 1833618 2751701 := bbase (se 7 (by rfl) ⟨32246, by rfl⟩ : syracuseStep 2751701 = 64493) (by norm_num)
theorem B4127957 : Blo 1833618 4127957 := bbase (se 7 (by rfl) ⟨48374, by rfl⟩ : syracuseStep 4127957 = 96749) (by norm_num)
theorem B6192341 : Blo 1833618 6192341 := bbase (se 7 (by rfl) ⟨72566, by rfl⟩ : syracuseStep 6192341 = 145133) (by norm_num)
theorem B9288917 : Blo 1833618 9288917 := bbase (se 7 (by rfl) ⟨108854, by rfl⟩ : syracuseStep 9288917 = 217709) (by norm_num)
theorem B2751725 : Blo 1833618 2751725 := bbase (se 3 (by rfl) ⟨515948, by rfl⟩ : syracuseStep 2751725 = 1031897) (by norm_num)
theorem B2063605 : Blo 1833618 2063605 := bbase (se 5 (by rfl) ⟨96731, by rfl⟩ : syracuseStep 2063605 = 193463) (by norm_num)
theorem B4406525 : Blo 1833618 4406525 := bbase (se 3 (by rfl) ⟨826223, by rfl⟩ : syracuseStep 4406525 = 1652447) (by norm_num)
theorem B2751749 : Blo 1833618 2751749 := bbase (se 4 (by rfl) ⟨257976, by rfl⟩ : syracuseStep 2751749 = 515953) (by norm_num)
theorem B3095813 : Blo 1833618 3095813 := bbase (se 4 (by rfl) ⟨290232, by rfl⟩ : syracuseStep 3095813 = 580465) (by norm_num)
theorem B2063641 : Blo 1833618 2063641 := bbase (se 2 (by rfl) ⟨773865, by rfl⟩ : syracuseStep 2063641 = 1547731) (by norm_num)
theorem B2751773 : Blo 1833618 2751773 := bbase (se 3 (by rfl) ⟨515957, by rfl⟩ : syracuseStep 2751773 = 1031915) (by norm_num)
theorem B4128029 : Blo 1833618 4128029 := bbase (se 3 (by rfl) ⟨774005, by rfl⟩ : syracuseStep 4128029 = 1548011) (by norm_num)
theorem B4644125 : Blo 1833618 4644125 := bbase (se 3 (by rfl) ⟨870773, by rfl⟩ : syracuseStep 4644125 = 1741547) (by norm_num)
theorem B2751797 : Blo 1833618 2751797 := bbase (se 5 (by rfl) ⟨128990, by rfl⟩ : syracuseStep 2751797 = 257981) (by norm_num)
theorem B2063677 : Blo 1833618 2063677 := bbase (se 3 (by rfl) ⟨386939, by rfl⟩ : syracuseStep 2063677 = 773879) (by norm_num)
theorem B2751821 : Blo 1833618 2751821 := bbase (se 3 (by rfl) ⟨515966, by rfl⟩ : syracuseStep 2751821 = 1031933) (by norm_num)
theorem B3530069 : Blo 1833618 3530069 := bbase (se 11 (by rfl) ⟨2585, by rfl⟩ : syracuseStep 3530069 = 5171) (by norm_num)
theorem B2063713 : Blo 1833618 2063713 := bbase (se 2 (by rfl) ⟨773892, by rfl⟩ : syracuseStep 2063713 = 1547785) (by norm_num)
theorem B5954917 : Blo 1833618 5954917 := bbase (se 4 (by rfl) ⟨558273, by rfl⟩ : syracuseStep 5954917 = 1116547) (by norm_num)
theorem B2751845 : Blo 1833618 2751845 := bbase (se 4 (by rfl) ⟨257985, by rfl⟩ : syracuseStep 2751845 = 515971) (by norm_num)
theorem B4128101 : Blo 1833618 4128101 := bbase (se 4 (by rfl) ⟨387009, by rfl⟩ : syracuseStep 4128101 = 774019) (by norm_num)
theorem B2751869 : Blo 1833618 2751869 := bbase (se 3 (by rfl) ⟨515975, by rfl⟩ : syracuseStep 2751869 = 1031951) (by norm_num)
theorem B2063749 : Blo 1833618 2063749 := bbase (se 4 (by rfl) ⟨193476, by rfl⟩ : syracuseStep 2063749 = 386953) (by norm_num)
theorem B3095941 : Blo 1833618 3095941 := bbase (se 4 (by rfl) ⟨290244, by rfl⟩ : syracuseStep 3095941 = 580489) (by norm_num)
theorem B2751893 : Blo 1833618 2751893 := bbase (se 6 (by rfl) ⟨64497, by rfl⟩ : syracuseStep 2751893 = 128995) (by norm_num)
theorem B2063785 : Blo 1833618 2063785 := bbase (se 2 (by rfl) ⟨773919, by rfl⟩ : syracuseStep 2063785 = 1547839) (by norm_num)
theorem B2751917 : Blo 1833618 2751917 := bbase (se 3 (by rfl) ⟨515984, by rfl⟩ : syracuseStep 2751917 = 1031969) (by norm_num)
theorem B4128173 : Blo 1833618 4128173 := bbase (se 3 (by rfl) ⟨774032, by rfl⟩ : syracuseStep 4128173 = 1548065) (by norm_num)
theorem B2751941 : Blo 1833618 2751941 := bbase (se 4 (by rfl) ⟨257994, by rfl⟩ : syracuseStep 2751941 = 515989) (by norm_num)
theorem B2063821 : Blo 1833618 2063821 := bbase (se 3 (by rfl) ⟨386966, by rfl⟩ : syracuseStep 2063821 = 773933) (by norm_num)
theorem B53632469 : Blo 1833618 53632469 := bbase (se 7 (by rfl) ⟨628505, by rfl⟩ : syracuseStep 53632469 = 1257011) (by norm_num)
theorem B2751965 : Blo 1833618 2751965 := bbase (se 3 (by rfl) ⟨515993, by rfl⟩ : syracuseStep 2751965 = 1031987) (by norm_num)
theorem B3096029 : Blo 1833618 3096029 := bbase (se 3 (by rfl) ⟨580505, by rfl⟩ : syracuseStep 3096029 = 1161011) (by norm_num)
theorem B4644317 : Blo 1833618 4644317 := bbase (se 3 (by rfl) ⟨870809, by rfl⟩ : syracuseStep 4644317 = 1741619) (by norm_num)
theorem B6610405 : Blo 1833618 6610405 := bbase (se 4 (by rfl) ⟨619725, by rfl⟩ : syracuseStep 6610405 = 1239451) (by norm_num)
theorem B2063857 : Blo 1833618 2063857 := bbase (se 2 (by rfl) ⟨773946, by rfl⟩ : syracuseStep 2063857 = 1547893) (by norm_num)
theorem B2751989 : Blo 1833618 2751989 := bbase (se 5 (by rfl) ⟨128999, by rfl⟩ : syracuseStep 2751989 = 257999) (by norm_num)
theorem B4128245 : Blo 1833618 4128245 := bbase (se 5 (by rfl) ⟨193511, by rfl⟩ : syracuseStep 4128245 = 387023) (by norm_num)
theorem B2752013 : Blo 1833618 2752013 := bbase (se 3 (by rfl) ⟨516002, by rfl⟩ : syracuseStep 2752013 = 1032005) (by norm_num)
theorem B2121229 : Blo 1833618 2121229 := bbase (se 3 (by rfl) ⟨397730, by rfl⟩ : syracuseStep 2121229 = 795461) (by norm_num)
theorem B2063893 : Blo 1833618 2063893 := bbase (se 6 (by rfl) ⟨48372, by rfl⟩ : syracuseStep 2063893 = 96745) (by norm_num)
theorem B14884373 : Blo 1833618 14884373 := bbase (se 6 (by rfl) ⟨348852, by rfl⟩ : syracuseStep 14884373 = 697705) (by norm_num)
theorem B2752037 : Blo 1833618 2752037 := bbase (se 4 (by rfl) ⟨258003, by rfl⟩ : syracuseStep 2752037 = 516007) (by norm_num)
theorem B2203189 : Blo 1833618 2203189 := bbase (se 5 (by rfl) ⟨103274, by rfl⟩ : syracuseStep 2203189 = 206549) (by norm_num)
theorem B2063929 : Blo 1833618 2063929 := bbase (se 2 (by rfl) ⟨773973, by rfl⟩ : syracuseStep 2063929 = 1547947) (by norm_num)
theorem B2752061 : Blo 1833618 2752061 := bbase (se 3 (by rfl) ⟨516011, by rfl⟩ : syracuseStep 2752061 = 1032023) (by norm_num)
theorem B4128317 : Blo 1833618 4128317 := bbase (se 3 (by rfl) ⟨774059, by rfl⟩ : syracuseStep 4128317 = 1548119) (by norm_num)
theorem B3481157 : Blo 1833618 3481157 := bbase (se 4 (by rfl) ⟨326358, by rfl⟩ : syracuseStep 3481157 = 652717) (by norm_num)
theorem B2752085 : Blo 1833618 2752085 := bbase (se 8 (by rfl) ⟨16125, by rfl⟩ : syracuseStep 2752085 = 32251) (by norm_num)
theorem B2063965 : Blo 1833618 2063965 := bbase (se 3 (by rfl) ⟨386993, by rfl⟩ : syracuseStep 2063965 = 773987) (by norm_num)
theorem B3096157 : Blo 1833618 3096157 := bbase (se 3 (by rfl) ⟨580529, by rfl⟩ : syracuseStep 3096157 = 1161059) (by norm_num)
theorem B2752109 : Blo 1833618 2752109 := bbase (se 3 (by rfl) ⟨516020, by rfl⟩ : syracuseStep 2752109 = 1032041) (by norm_num)
theorem B2064001 : Blo 1833618 2064001 := bbase (se 2 (by rfl) ⟨774000, by rfl⟩ : syracuseStep 2064001 = 1548001) (by norm_num)
theorem B2752133 : Blo 1833618 2752133 := bbase (se 4 (by rfl) ⟨258012, by rfl⟩ : syracuseStep 2752133 = 516025) (by norm_num)
theorem B4128389 : Blo 1833618 4128389 := bbase (se 4 (by rfl) ⟨387036, by rfl⟩ : syracuseStep 4128389 = 774073) (by norm_num)
theorem B6192773 : Blo 1833618 6192773 := bbase (se 4 (by rfl) ⟨580572, by rfl⟩ : syracuseStep 6192773 = 1161145) (by norm_num)
theorem B5226133 : Blo 1833618 5226133 := bbase (se 6 (by rfl) ⟨122487, by rfl⟩ : syracuseStep 5226133 = 244975) (by norm_num)
theorem B2752157 : Blo 1833618 2752157 := bbase (se 3 (by rfl) ⟨516029, by rfl⟩ : syracuseStep 2752157 = 1032059) (by norm_num)
theorem B2064037 : Blo 1833618 2064037 := bbase (se 4 (by rfl) ⟨193503, by rfl⟩ : syracuseStep 2064037 = 387007) (by norm_num)
theorem B2752181 : Blo 1833618 2752181 := bbase (se 5 (by rfl) ⟨129008, by rfl⟩ : syracuseStep 2752181 = 258017) (by norm_num)
theorem B3096245 : Blo 1833618 3096245 := bbase (se 5 (by rfl) ⟨145136, by rfl⟩ : syracuseStep 3096245 = 290273) (by norm_num)
theorem B2064073 : Blo 1833618 2064073 := bbase (se 2 (by rfl) ⟨774027, by rfl⟩ : syracuseStep 2064073 = 1548055) (by norm_num)
theorem B2752205 : Blo 1833618 2752205 := bbase (se 3 (by rfl) ⟨516038, by rfl⟩ : syracuseStep 2752205 = 1032077) (by norm_num)
theorem B4128461 : Blo 1833618 4128461 := bbase (se 3 (by rfl) ⟨774086, by rfl⟩ : syracuseStep 4128461 = 1548173) (by norm_num)
theorem B10051285 : Blo 1833618 10051285 := bbase (se 7 (by rfl) ⟨117788, by rfl⟩ : syracuseStep 10051285 = 235577) (by norm_num)
theorem B3481309 : Blo 1833618 3481309 := bbase (se 3 (by rfl) ⟨652745, by rfl⟩ : syracuseStep 3481309 = 1305491) (by norm_num)
theorem B2752229 : Blo 1833618 2752229 := bbase (se 4 (by rfl) ⟨258021, by rfl⟩ : syracuseStep 2752229 = 516043) (by norm_num)
theorem B2064109 : Blo 1833618 2064109 := bbase (se 3 (by rfl) ⟨387020, by rfl⟩ : syracuseStep 2064109 = 774041) (by norm_num)
theorem B2752253 : Blo 1833618 2752253 := bbase (se 3 (by rfl) ⟨516047, by rfl⟩ : syracuseStep 2752253 = 1032095) (by norm_num)
theorem B2064145 : Blo 1833618 2064145 := bbase (se 2 (by rfl) ⟨774054, by rfl⟩ : syracuseStep 2064145 = 1548109) (by norm_num)
theorem B10444565 : Blo 1833618 10444565 := bbase (se 6 (by rfl) ⟨244794, by rfl⟩ : syracuseStep 10444565 = 489589) (by norm_num)
theorem B6610709 : Blo 1833618 6610709 := bbase (se 6 (by rfl) ⟨154938, by rfl⟩ : syracuseStep 6610709 = 309877) (by norm_num)
theorem B2752277 : Blo 1833618 2752277 := bbase (se 6 (by rfl) ⟨64506, by rfl⟩ : syracuseStep 2752277 = 129013) (by norm_num)
theorem B4128533 : Blo 1833618 4128533 := bbase (se 6 (by rfl) ⟨96762, by rfl⟩ : syracuseStep 4128533 = 193525) (by norm_num)
theorem B1990441 : Blo 1833618 1990441 := bbase (se 2 (by rfl) ⟨746415, by rfl⟩ : syracuseStep 1990441 = 1492831) (by norm_num)
theorem B2752301 : Blo 1833618 2752301 := bbase (se 3 (by rfl) ⟨516056, by rfl⟩ : syracuseStep 2752301 = 1032113) (by norm_num)
theorem B2064181 : Blo 1833618 2064181 := bbase (se 5 (by rfl) ⟨96758, by rfl⟩ : syracuseStep 2064181 = 193517) (by norm_num)
theorem B3096373 : Blo 1833618 3096373 := bbase (se 5 (by rfl) ⟨145142, by rfl⟩ : syracuseStep 3096373 = 290285) (by norm_num)
theorem B4644661 : Blo 1833618 4644661 := bbase (se 5 (by rfl) ⟨217718, by rfl⟩ : syracuseStep 4644661 = 435437) (by norm_num)
theorem B2752325 : Blo 1833618 2752325 := bbase (se 4 (by rfl) ⟨258030, by rfl⟩ : syracuseStep 2752325 = 516061) (by norm_num)
theorem B6963029 : Blo 1833618 6963029 := bbase (se 9 (by rfl) ⟨20399, by rfl⟩ : syracuseStep 6963029 = 40799) (by norm_num)
theorem B2064217 : Blo 1833618 2064217 := bbase (se 2 (by rfl) ⟨774081, by rfl⟩ : syracuseStep 2064217 = 1548163) (by norm_num)
theorem B2752349 : Blo 1833618 2752349 := bbase (se 3 (by rfl) ⟨516065, by rfl⟩ : syracuseStep 2752349 = 1032131) (by norm_num)
theorem B4128605 : Blo 1833618 4128605 := bbase (se 3 (by rfl) ⟨774113, by rfl⟩ : syracuseStep 4128605 = 1548227) (by norm_num)
theorem B2752373 : Blo 1833618 2752373 := bbase (se 5 (by rfl) ⟨129017, by rfl⟩ : syracuseStep 2752373 = 258035) (by norm_num)
theorem B2064253 : Blo 1833618 2064253 := bbase (se 3 (by rfl) ⟨387047, by rfl⟩ : syracuseStep 2064253 = 774095) (by norm_num)
theorem B2752397 : Blo 1833618 2752397 := bbase (se 3 (by rfl) ⟨516074, by rfl⟩ : syracuseStep 2752397 = 1032149) (by norm_num)
theorem B3096461 : Blo 1833618 3096461 := bbase (se 3 (by rfl) ⟨580586, by rfl⟩ : syracuseStep 3096461 = 1161173) (by norm_num)
theorem B2064289 : Blo 1833618 2064289 := bbase (se 2 (by rfl) ⟨774108, by rfl⟩ : syracuseStep 2064289 = 1548217) (by norm_num)
theorem B2752421 : Blo 1833618 2752421 := bbase (se 4 (by rfl) ⟨258039, by rfl⟩ : syracuseStep 2752421 = 516079) (by norm_num)
theorem B4128677 : Blo 1833618 4128677 := bbase (se 4 (by rfl) ⟨387063, by rfl⟩ : syracuseStep 4128677 = 774127) (by norm_num)
theorem B4644773 : Blo 1833618 4644773 := bbase (se 4 (by rfl) ⟨435447, by rfl⟩ : syracuseStep 4644773 = 870895) (by norm_num)
theorem B2752445 : Blo 1833618 2752445 := bbase (se 3 (by rfl) ⟨516083, by rfl⟩ : syracuseStep 2752445 = 1032167) (by norm_num)
theorem B2064325 : Blo 1833618 2064325 := bbase (se 4 (by rfl) ⟨193530, by rfl⟩ : syracuseStep 2064325 = 387061) (by norm_num)
theorem B2752469 : Blo 1833618 2752469 := bbase (se 7 (by rfl) ⟨32255, by rfl⟩ : syracuseStep 2752469 = 64511) (by norm_num)
theorem B2064361 : Blo 1833618 2064361 := bbase (se 2 (by rfl) ⟨774135, by rfl⟩ : syracuseStep 2064361 = 1548271) (by norm_num)
theorem B2752493 : Blo 1833618 2752493 := bbase (se 3 (by rfl) ⟨516092, by rfl⟩ : syracuseStep 2752493 = 1032185) (by norm_num)
theorem B4128749 : Blo 1833618 4128749 := bbase (se 3 (by rfl) ⟨774140, by rfl⟩ : syracuseStep 4128749 = 1548281) (by norm_num)
theorem B1835011 : Blo 1833618 1835011 := bstep (se 1 (by rfl) ⟨1376258, by rfl⟩ : syracuseStep 1835011 = 2752517) B2752517
theorem B11919365 : Blo 1833618 11919365 := bstep (se 4 (by rfl) ⟨1117440, by rfl⟩ : syracuseStep 11919365 = 2234881) B2234881
theorem B4128785 : Blo 1833618 4128785 := bstep (se 2 (by rfl) ⟨1548294, by rfl⟩ : syracuseStep 4128785 = 3096589) B3096589
theorem B2752529 : Blo 1833618 2752529 := bstep (se 2 (by rfl) ⟨1032198, by rfl⟩ : syracuseStep 2752529 = 2064397) B2064397
theorem B1835027 : Blo 1833618 1835027 := bstep (se 1 (by rfl) ⟨1376270, by rfl⟩ : syracuseStep 1835027 = 2752541) B2752541
theorem B4128803 : Blo 1833618 4128803 := bstep (se 1 (by rfl) ⟨3096602, by rfl⟩ : syracuseStep 4128803 = 6193205) B6193205
theorem B2752547 : Blo 1833618 2752547 := bstep (se 1 (by rfl) ⟨2064410, by rfl⟩ : syracuseStep 2752547 = 4128821) B4128821
theorem B1835043 : Blo 1833618 1835043 := bstep (se 1 (by rfl) ⟨1376282, by rfl⟩ : syracuseStep 1835043 = 2752565) B2752565
theorem B1835059 : Blo 1833618 1835059 := bstep (se 1 (by rfl) ⟨1376294, by rfl⟩ : syracuseStep 1835059 = 2752589) B2752589
theorem B2752577 : Blo 1833618 2752577 := bstep (se 2 (by rfl) ⟨1032216, by rfl⟩ : syracuseStep 2752577 = 2064433) B2064433
theorem B3096643 : Blo 1833618 3096643 := bstep (se 1 (by rfl) ⟨2322482, by rfl⟩ : syracuseStep 3096643 = 4644965) B4644965
theorem B2064451 : Blo 1833618 2064451 := bstep (se 1 (by rfl) ⟨1548338, by rfl⟩ : syracuseStep 2064451 = 3096677) B3096677
theorem B1835075 : Blo 1833618 1835075 := bstep (se 1 (by rfl) ⟨1376306, by rfl⟩ : syracuseStep 1835075 = 2752613) B2752613
theorem B2752595 : Blo 1833618 2752595 := bstep (se 1 (by rfl) ⟨2064446, by rfl⟩ : syracuseStep 2752595 = 4128893) B4128893
theorem B1835091 : Blo 1833618 1835091 := bstep (se 1 (by rfl) ⟨1376318, by rfl⟩ : syracuseStep 1835091 = 2752637) B2752637
theorem B1835107 : Blo 1833618 1835107 := bstep (se 1 (by rfl) ⟨1376330, by rfl⟩ : syracuseStep 1835107 = 2752661) B2752661
theorem B2752625 : Blo 1833618 2752625 := bstep (se 2 (by rfl) ⟨1032234, by rfl⟩ : syracuseStep 2752625 = 2064469) B2064469
theorem B1835123 : Blo 1833618 1835123 := bstep (se 1 (by rfl) ⟨1376342, by rfl⟩ : syracuseStep 1835123 = 2752685) B2752685
theorem B2752643 : Blo 1833618 2752643 := bstep (se 1 (by rfl) ⟨2064482, by rfl⟩ : syracuseStep 2752643 = 4128965) B4128965
theorem B1835139 : Blo 1833618 1835139 := bstep (se 1 (by rfl) ⟨1376354, by rfl⟩ : syracuseStep 1835139 = 2752709) B2752709
theorem B1835155 : Blo 1833618 1835155 := bstep (se 1 (by rfl) ⟨1376366, by rfl⟩ : syracuseStep 1835155 = 2752733) B2752733
theorem B2752673 : Blo 1833618 2752673 := bstep (se 2 (by rfl) ⟨1032252, by rfl⟩ : syracuseStep 2752673 = 2064505) B2064505
theorem B1835171 : Blo 1833618 1835171 := bstep (se 1 (by rfl) ⟨1376378, by rfl⟩ : syracuseStep 1835171 = 2752757) B2752757
theorem B2752691 : Blo 1833618 2752691 := bstep (se 1 (by rfl) ⟨2064518, by rfl⟩ : syracuseStep 2752691 = 4129037) B4129037
theorem B1835187 : Blo 1833618 1835187 := bstep (se 1 (by rfl) ⟨1376390, by rfl⟩ : syracuseStep 1835187 = 2752781) B2752781
theorem B3481795 : Blo 1833618 3481795 := bstep (se 1 (by rfl) ⟨2611346, by rfl⟩ : syracuseStep 3481795 = 5222693) B5222693
theorem B2203843 : Blo 1833618 2203843 := bstep (se 1 (by rfl) ⟨1652882, by rfl⟩ : syracuseStep 2203843 = 3305765) B3305765
theorem B1835203 : Blo 1833618 1835203 := bstep (se 1 (by rfl) ⟨1376402, by rfl⟩ : syracuseStep 1835203 = 2752805) B2752805
theorem B8372429 : Blo 1833618 8372429 := bstep (se 3 (by rfl) ⟨1569830, by rfl⟩ : syracuseStep 8372429 = 3139661) B3139661
theorem B3096785 : Blo 1833618 3096785 := bstep (se 2 (by rfl) ⟨1161294, by rfl⟩ : syracuseStep 3096785 = 2322589) B2322589
theorem B2752721 : Blo 1833618 2752721 := bstep (se 2 (by rfl) ⟨1032270, by rfl⟩ : syracuseStep 2752721 = 2064541) B2064541
theorem B2064595 : Blo 1833618 2064595 := bstep (se 1 (by rfl) ⟨1548446, by rfl⟩ : syracuseStep 2064595 = 3096893) B3096893
theorem B1835219 : Blo 1833618 1835219 := bstep (se 1 (by rfl) ⟨1376414, by rfl⟩ : syracuseStep 1835219 = 2752829) B2752829
theorem B2752739 : Blo 1833618 2752739 := bstep (se 1 (by rfl) ⟨2064554, by rfl⟩ : syracuseStep 2752739 = 4129109) B4129109
theorem B1835235 : Blo 1833618 1835235 := bstep (se 1 (by rfl) ⟨1376426, by rfl⟩ : syracuseStep 1835235 = 2752853) B2752853
theorem B3481841 : Blo 1833618 3481841 := bstep (se 2 (by rfl) ⟨1305690, by rfl⟩ : syracuseStep 3481841 = 2611381) B2611381
theorem B1835251 : Blo 1833618 1835251 := bstep (se 1 (by rfl) ⟨1376438, by rfl⟩ : syracuseStep 1835251 = 2752877) B2752877
theorem B7839985 : Blo 1833618 7839985 := bstep (se 2 (by rfl) ⟨2939994, by rfl⟩ : syracuseStep 7839985 = 5879989) B5879989
theorem B2752769 : Blo 1833618 2752769 := bstep (se 2 (by rfl) ⟨1032288, by rfl⟩ : syracuseStep 2752769 = 2064577) B2064577
theorem B1835267 : Blo 1833618 1835267 := bstep (se 1 (by rfl) ⟨1376450, by rfl⟩ : syracuseStep 1835267 = 2752901) B2752901
theorem B6193421 : Blo 1833618 6193421 := bstep (se 3 (by rfl) ⟨1161266, by rfl⟩ : syracuseStep 6193421 = 2322533) B2322533
theorem B2752787 : Blo 1833618 2752787 := bstep (se 1 (by rfl) ⟨2064590, by rfl⟩ : syracuseStep 2752787 = 4129181) B4129181
theorem B1835283 : Blo 1833618 1835283 := bstep (se 1 (by rfl) ⟨1376462, by rfl⟩ : syracuseStep 1835283 = 2752925) B2752925
theorem B2203939 : Blo 1833618 2203939 := bstep (se 1 (by rfl) ⟨1652954, by rfl⟩ : syracuseStep 2203939 = 3305909) B3305909
theorem B1835299 : Blo 1833618 1835299 := bstep (se 1 (by rfl) ⟨1376474, by rfl⟩ : syracuseStep 1835299 = 2752949) B2752949
theorem B4129073 : Blo 1833618 4129073 := bstep (se 2 (by rfl) ⟨1548402, by rfl⟩ : syracuseStep 4129073 = 3096805) B3096805
theorem B2752817 : Blo 1833618 2752817 := bstep (se 2 (by rfl) ⟨1032306, by rfl⟩ : syracuseStep 2752817 = 2064613) B2064613
theorem B1835315 : Blo 1833618 1835315 := bstep (se 1 (by rfl) ⟨1376486, by rfl⟩ : syracuseStep 1835315 = 2752973) B2752973
theorem B6193475 : Blo 1833618 6193475 := bstep (se 1 (by rfl) ⟨4645106, by rfl⟩ : syracuseStep 6193475 = 9290213) B9290213
theorem B11911493 : Blo 1833618 11911493 := bstep (se 4 (by rfl) ⟨1116702, by rfl⟩ : syracuseStep 11911493 = 2233405) B2233405
theorem B4129091 : Blo 1833618 4129091 := bstep (se 1 (by rfl) ⟨3096818, by rfl⟩ : syracuseStep 4129091 = 6193637) B6193637
theorem B2752835 : Blo 1833618 2752835 := bstep (se 1 (by rfl) ⟨2064626, by rfl⟩ : syracuseStep 2752835 = 4129253) B4129253
theorem B3096913 : Blo 1833618 3096913 := bstep (se 2 (by rfl) ⟨1161342, by rfl⟩ : syracuseStep 3096913 = 2322685) B2322685
theorem B1835347 : Blo 1833618 1835347 := bstep (se 1 (by rfl) ⟨1376510, by rfl⟩ : syracuseStep 1835347 = 2753021) B2753021
theorem B2752865 : Blo 1833618 2752865 := bstep (se 2 (by rfl) ⟨1032324, by rfl⟩ : syracuseStep 2752865 = 2064649) B2064649
theorem B2064739 : Blo 1833618 2064739 := bstep (se 1 (by rfl) ⟨1548554, by rfl⟩ : syracuseStep 2064739 = 3097109) B3097109
theorem B1835363 : Blo 1833618 1835363 := bstep (se 1 (by rfl) ⟨1376522, by rfl⟩ : syracuseStep 1835363 = 2753045) B2753045
theorem B3719537 : Blo 1833618 3719537 := bstep (se 2 (by rfl) ⟨1394826, by rfl⟩ : syracuseStep 3719537 = 2789653) B2789653
theorem B3096947 : Blo 1833618 3096947 := bstep (se 1 (by rfl) ⟨2322710, by rfl⟩ : syracuseStep 3096947 = 4645421) B4645421
theorem B2752883 : Blo 1833618 2752883 := bstep (se 1 (by rfl) ⟨2064662, by rfl⟩ : syracuseStep 2752883 = 4129325) B4129325
theorem B1835379 : Blo 1833618 1835379 := bstep (se 1 (by rfl) ⟨1376534, by rfl⟩ : syracuseStep 1835379 = 2753069) B2753069
theorem B1835395 : Blo 1833618 1835395 := bstep (se 1 (by rfl) ⟨1376546, by rfl⟩ : syracuseStep 1835395 = 2753093) B2753093
theorem B2752913 : Blo 1833618 2752913 := bstep (se 2 (by rfl) ⟨1032342, by rfl⟩ : syracuseStep 2752913 = 2064685) B2064685
theorem B1835411 : Blo 1833618 1835411 := bstep (se 1 (by rfl) ⟨1376558, by rfl⟩ : syracuseStep 1835411 = 2753117) B2753117
theorem B2752931 : Blo 1833618 2752931 := bstep (se 1 (by rfl) ⟨2064698, by rfl⟩ : syracuseStep 2752931 = 4129397) B4129397
theorem B1835427 : Blo 1833618 1835427 := bstep (se 1 (by rfl) ⟨1376570, by rfl⟩ : syracuseStep 1835427 = 2753141) B2753141
theorem B1835443 : Blo 1833618 1835443 := bstep (se 1 (by rfl) ⟨1376582, by rfl⟩ : syracuseStep 1835443 = 2753165) B2753165
theorem B2752961 : Blo 1833618 2752961 := bstep (se 2 (by rfl) ⟨1032360, by rfl⟩ : syracuseStep 2752961 = 2064721) B2064721
theorem B1835459 : Blo 1833618 1835459 := bstep (se 1 (by rfl) ⟨1376594, by rfl⟩ : syracuseStep 1835459 = 2753189) B2753189
theorem B2752979 : Blo 1833618 2752979 := bstep (se 1 (by rfl) ⟨2064734, by rfl⟩ : syracuseStep 2752979 = 4129469) B4129469
theorem B1835475 : Blo 1833618 1835475 := bstep (se 1 (by rfl) ⟨1376606, by rfl⟩ : syracuseStep 1835475 = 2753213) B2753213
theorem B1835491 : Blo 1833618 1835491 := bstep (se 1 (by rfl) ⟨1376618, by rfl⟩ : syracuseStep 1835491 = 2753237) B2753237
theorem B6275569 : Blo 1833618 6275569 := bstep (se 2 (by rfl) ⟨2353338, by rfl⟩ : syracuseStep 6275569 = 4706677) B4706677
theorem B2753009 : Blo 1833618 2753009 := bstep (se 2 (by rfl) ⟨1032378, by rfl⟩ : syracuseStep 2753009 = 2064757) B2064757
theorem B3097075 : Blo 1833618 3097075 := bstep (se 1 (by rfl) ⟨2322806, by rfl⟩ : syracuseStep 3097075 = 4645613) B4645613
theorem B2064883 : Blo 1833618 2064883 := bstep (se 1 (by rfl) ⟨1548662, by rfl⟩ : syracuseStep 2064883 = 3097325) B3097325
theorem B1835507 : Blo 1833618 1835507 := bstep (se 1 (by rfl) ⟨1376630, by rfl⟩ : syracuseStep 1835507 = 2753261) B2753261
theorem B2753027 : Blo 1833618 2753027 := bstep (se 1 (by rfl) ⟨2064770, by rfl⟩ : syracuseStep 2753027 = 4129541) B4129541
theorem B1835523 : Blo 1833618 1835523 := bstep (se 1 (by rfl) ⟨1376642, by rfl⟩ : syracuseStep 1835523 = 2753285) B2753285
theorem B5227021 : Blo 1833618 5227021 := bstep (se 3 (by rfl) ⟨980066, by rfl⟩ : syracuseStep 5227021 = 1960133) B1960133
theorem B3482129 : Blo 1833618 3482129 := bstep (se 2 (by rfl) ⟨1305798, by rfl⟩ : syracuseStep 3482129 = 2611597) B2611597
theorem B1835539 : Blo 1833618 1835539 := bstep (se 1 (by rfl) ⟨1376654, by rfl⟩ : syracuseStep 1835539 = 2753309) B2753309
theorem B2753057 : Blo 1833618 2753057 := bstep (se 2 (by rfl) ⟨1032396, by rfl⟩ : syracuseStep 2753057 = 2064793) B2064793
theorem B1835555 : Blo 1833618 1835555 := bstep (se 1 (by rfl) ⟨1376666, by rfl⟩ : syracuseStep 1835555 = 2753333) B2753333
theorem B2753075 : Blo 1833618 2753075 := bstep (se 1 (by rfl) ⟨2064806, by rfl⟩ : syracuseStep 2753075 = 4129613) B4129613
theorem B1835571 : Blo 1833618 1835571 := bstep (se 1 (by rfl) ⟨1376678, by rfl⟩ : syracuseStep 1835571 = 2753357) B2753357
theorem B1835587 : Blo 1833618 1835587 := bstep (se 1 (by rfl) ⟨1376690, by rfl⟩ : syracuseStep 1835587 = 2753381) B2753381
theorem B6193745 : Blo 1833618 6193745 := bstep (se 2 (by rfl) ⟨2322654, by rfl⟩ : syracuseStep 6193745 = 4645309) B4645309
theorem B4129361 : Blo 1833618 4129361 := bstep (se 2 (by rfl) ⟨1548510, by rfl⟩ : syracuseStep 4129361 = 3097021) B3097021
theorem B2753105 : Blo 1833618 2753105 := bstep (se 2 (by rfl) ⟨1032414, by rfl⟩ : syracuseStep 2753105 = 2064829) B2064829
theorem B1835603 : Blo 1833618 1835603 := bstep (se 1 (by rfl) ⟨1376702, by rfl⟩ : syracuseStep 1835603 = 2753405) B2753405
theorem B5874275 : Blo 1833618 5874275 := bstep (se 1 (by rfl) ⟨4405706, by rfl⟩ : syracuseStep 5874275 = 8811413) B8811413
theorem B4129379 : Blo 1833618 4129379 := bstep (se 1 (by rfl) ⟨3097034, by rfl⟩ : syracuseStep 4129379 = 6194069) B6194069
theorem B2753123 : Blo 1833618 2753123 := bstep (se 1 (by rfl) ⟨2064842, by rfl⟩ : syracuseStep 2753123 = 4129685) B4129685
theorem B3097217 : Blo 1833618 3097217 := bstep (se 2 (by rfl) ⟨1161456, by rfl⟩ : syracuseStep 3097217 = 2322913) B2322913
theorem B2753153 : Blo 1833618 2753153 := bstep (se 2 (by rfl) ⟨1032432, by rfl⟩ : syracuseStep 2753153 = 2064865) B2064865
theorem B2065027 : Blo 1833618 2065027 := bstep (se 1 (by rfl) ⟨1548770, by rfl⟩ : syracuseStep 2065027 = 3097541) B3097541
theorem B2753171 : Blo 1833618 2753171 := bstep (se 1 (by rfl) ⟨2064878, by rfl⟩ : syracuseStep 2753171 = 4129757) B4129757
theorem B2753201 : Blo 1833618 2753201 := bstep (se 2 (by rfl) ⟨1032450, by rfl⟩ : syracuseStep 2753201 = 2064901) B2064901
theorem B2753219 : Blo 1833618 2753219 := bstep (se 1 (by rfl) ⟨2064914, by rfl⟩ : syracuseStep 2753219 = 4129829) B4129829
theorem B2753249 : Blo 1833618 2753249 := bstep (se 2 (by rfl) ⟨1032468, by rfl⟩ : syracuseStep 2753249 = 2064937) B2064937
theorem B5874403 : Blo 1833618 5874403 := bstep (se 1 (by rfl) ⟨4405802, by rfl⟩ : syracuseStep 5874403 = 8811605) B8811605
theorem B2753267 : Blo 1833618 2753267 := bstep (se 1 (by rfl) ⟨2064950, by rfl⟩ : syracuseStep 2753267 = 4129901) B4129901
theorem B3097345 : Blo 1833618 3097345 := bstep (se 2 (by rfl) ⟨1161504, by rfl⟩ : syracuseStep 3097345 = 2323009) B2323009
theorem B2753297 : Blo 1833618 2753297 := bstep (se 2 (by rfl) ⟨1032486, by rfl⟩ : syracuseStep 2753297 = 2064973) B2064973
theorem B3097379 : Blo 1833618 3097379 := bstep (se 1 (by rfl) ⟨2323034, by rfl⟩ : syracuseStep 3097379 = 4646069) B4646069
theorem B2753315 : Blo 1833618 2753315 := bstep (se 1 (by rfl) ⟨2064986, by rfl⟩ : syracuseStep 2753315 = 4129973) B4129973
theorem B2753345 : Blo 1833618 2753345 := bstep (se 2 (by rfl) ⟨1032504, by rfl⟩ : syracuseStep 2753345 = 2065009) B2065009
theorem B2753363 : Blo 1833618 2753363 := bstep (se 1 (by rfl) ⟨2065022, by rfl⟩ : syracuseStep 2753363 = 4130045) B4130045
theorem B5874545 : Blo 1833618 5874545 := bstep (se 2 (by rfl) ⟨2202954, by rfl⟩ : syracuseStep 5874545 = 4405909) B4405909
theorem B4645745 : Blo 1833618 4645745 := bstep (se 2 (by rfl) ⟨1742154, by rfl⟩ : syracuseStep 4645745 = 3484309) B3484309
theorem B4129649 : Blo 1833618 4129649 := bstep (se 2 (by rfl) ⟨1548618, by rfl⟩ : syracuseStep 4129649 = 3097237) B3097237
theorem B2753393 : Blo 1833618 2753393 := bstep (se 2 (by rfl) ⟨1032522, by rfl⟩ : syracuseStep 2753393 = 2065045) B2065045
theorem B4129667 : Blo 1833618 4129667 := bstep (se 1 (by rfl) ⟨3097250, by rfl⟩ : syracuseStep 4129667 = 6194501) B6194501
theorem B2753411 : Blo 1833618 2753411 := bstep (se 1 (by rfl) ⟨2065058, by rfl⟩ : syracuseStep 2753411 = 4130117) B4130117
theorem B4645795 : Blo 1833618 4645795 := bstep (se 1 (by rfl) ⟨3484346, by rfl⟩ : syracuseStep 4645795 = 6968693) B6968693
theorem B3097507 : Blo 1833618 3097507 := bstep (se 1 (by rfl) ⟨2323130, by rfl⟩ : syracuseStep 3097507 = 4646261) B4646261
theorem B5956525 : Blo 1833618 5956525 := bstep (se 3 (by rfl) ⟨1116848, by rfl⟩ : syracuseStep 5956525 = 2233697) B2233697
theorem B5874659 : Blo 1833618 5874659 := bstep (se 1 (by rfl) ⟨4405994, by rfl⟩ : syracuseStep 5874659 = 8811989) B8811989
theorem B1958899 : Blo 1833618 1958899 := bstep (se 1 (by rfl) ⟨1469174, by rfl⟩ : syracuseStep 1958899 = 2938349) B2938349
theorem B10454021 : Blo 1833618 10454021 := bstep (se 4 (by rfl) ⟨980064, by rfl⟩ : syracuseStep 10454021 = 1960129) B1960129
theorem B3916849 : Blo 1833618 3916849 := bstep (se 2 (by rfl) ⟨1468818, by rfl⟩ : syracuseStep 3916849 = 2937637) B2937637
theorem B4645937 : Blo 1833618 4645937 := bstep (se 2 (by rfl) ⟨1742226, by rfl⟩ : syracuseStep 4645937 = 3484453) B3484453
theorem B6194285 : Blo 1833618 6194285 := bstep (se 3 (by rfl) ⟨1161428, by rfl⟩ : syracuseStep 6194285 = 2322857) B2322857
theorem B4129937 : Blo 1833618 4129937 := bstep (se 2 (by rfl) ⟨1548726, by rfl⟩ : syracuseStep 4129937 = 3097453) B3097453
theorem B6194339 : Blo 1833618 6194339 := bstep (se 1 (by rfl) ⟨4645754, by rfl⟩ : syracuseStep 6194339 = 9291509) B9291509
theorem B4129955 : Blo 1833618 4129955 := bstep (se 1 (by rfl) ⟨3097466, by rfl⟩ : syracuseStep 4129955 = 6194933) B6194933
theorem B3482851 : Blo 1833618 3482851 := bstep (se 1 (by rfl) ⟨2612138, by rfl⟩ : syracuseStep 3482851 = 5224277) B5224277
theorem B13583729 : Blo 1833618 13583729 := bstep (se 2 (by rfl) ⟨5093898, by rfl⟩ : syracuseStep 13583729 = 10187797) B10187797
theorem B9291185 : Blo 1833618 9291185 := bstep (se 2 (by rfl) ⟨3484194, by rfl⟩ : syracuseStep 9291185 = 6968389) B6968389
theorem B1959347 : Blo 1833618 1959347 := bstep (se 1 (by rfl) ⟨1469510, by rfl⟩ : syracuseStep 1959347 = 2939021) B2939021
theorem B6194609 : Blo 1833618 6194609 := bstep (se 2 (by rfl) ⟨2322978, by rfl⟩ : syracuseStep 6194609 = 4645957) B4645957
theorem B3917251 : Blo 1833618 3917251 := bstep (se 1 (by rfl) ⟨2937938, by rfl⟩ : syracuseStep 3917251 = 5875877) B5875877
theorem B22930885 : Blo 1833618 22930885 := bstep (se 4 (by rfl) ⟨2149770, by rfl⟩ : syracuseStep 22930885 = 4299541) B4299541
theorem B9545201 : Blo 1833618 9545201 := bstep (se 2 (by rfl) ⟨3579450, by rfl⟩ : syracuseStep 9545201 = 7158901) B7158901
theorem B9283085 : Blo 1833618 9283085 := bstep (se 3 (by rfl) ⟨1740578, by rfl⟩ : syracuseStep 9283085 = 3481157) B3481157
theorem B1835331 : Blo 1833618 1835331 := bstep (se 1 (by rfl) ⟨1376498, by rfl⟩ : syracuseStep 1835331 = 2752997) B2752997
theorem B3483299 : Blo 1833618 3483299 := bstep (se 1 (by rfl) ⟨2612474, by rfl⟩ : syracuseStep 3483299 = 5224949) B5224949
theorem B7440113 : Blo 1833618 7440113 := bstep (se 2 (by rfl) ⟨2790042, by rfl⟩ : syracuseStep 7440113 = 5580085) B5580085
theorem B7939889 : Blo 1833618 7939889 := bstep (se 2 (by rfl) ⟨2977458, by rfl⟩ : syracuseStep 7939889 = 5954917) B5954917
theorem B12552013 : Blo 1833618 12552013 := bstep (se 3 (by rfl) ⟨2353502, by rfl⟩ : syracuseStep 12552013 = 4707005) B4707005
theorem B3483587 : Blo 1833618 3483587 := bstep (se 1 (by rfl) ⟨2612690, by rfl⟩ : syracuseStep 3483587 = 5225381) B5225381
theorem B6195149 : Blo 1833618 6195149 := bstep (se 3 (by rfl) ⟨1161590, by rfl⟩ : syracuseStep 6195149 = 2323181) B2323181
theorem B6195203 : Blo 1833618 6195203 := bstep (se 1 (by rfl) ⟨4646402, by rfl⟩ : syracuseStep 6195203 = 9292805) B9292805
theorem B6965261 : Blo 1833618 6965261 := bstep (se 3 (by rfl) ⟨1305986, by rfl⟩ : syracuseStep 6965261 = 2611973) B2611973
theorem B2828305 : Blo 1833618 2828305 := bstep (se 2 (by rfl) ⟨1060614, by rfl⟩ : syracuseStep 2828305 = 2121229) B2121229
theorem B2721809 : Blo 1833618 2721809 := bstep (se 2 (by rfl) ⟨1020678, by rfl⟩ : syracuseStep 2721809 = 2041357) B2041357
theorem B2353379 : Blo 1833618 2353379 := bstep (se 1 (by rfl) ⟨1765034, by rfl⟩ : syracuseStep 2353379 = 3530069) B3530069
theorem B7833955 : Blo 1833618 7833955 := bstep (se 1 (by rfl) ⟨5875466, by rfl⟩ : syracuseStep 7833955 = 11750933) B11750933
theorem B9922915 : Blo 1833618 9922915 := bstep (se 1 (by rfl) ⟨7442186, by rfl⟩ : syracuseStep 9922915 = 14884373) B14884373
theorem B44616133 : Blo 1833618 44616133 := bstep (se 4 (by rfl) ⟨4182762, by rfl⟩ : syracuseStep 44616133 = 8365525) B8365525
theorem B3181123 : Blo 1833618 3181123 := bstep (se 1 (by rfl) ⟨2385842, by rfl⟩ : syracuseStep 3181123 = 4771685) B4771685
theorem B5876401 : Blo 1833618 5876401 := bstep (se 2 (by rfl) ⟨2203650, by rfl⟩ : syracuseStep 5876401 = 4407301) B4407301
theorem B2321075 : Blo 1833618 2321075 := bstep (se 1 (by rfl) ⟨1740806, by rfl⟩ : syracuseStep 2321075 = 3481613) B3481613
theorem B9538289 : Blo 1833618 9538289 := bstep (se 2 (by rfl) ⟨3576858, by rfl⟩ : syracuseStep 9538289 = 7153717) B7153717
theorem B2788163 : Blo 1833618 2788163 := bstep (se 1 (by rfl) ⟨2091122, by rfl⟩ : syracuseStep 2788163 = 4182245) B4182245
theorem B13937507 : Blo 1833618 13937507 := bstep (se 1 (by rfl) ⟨10453130, by rfl⟩ : syracuseStep 13937507 = 20906261) B20906261
theorem B9292643 : Blo 1833618 9292643 := bstep (se 1 (by rfl) ⟨6969482, by rfl⟩ : syracuseStep 9292643 = 13938965) B13938965
theorem B3484529 : Blo 1833618 3484529 := bstep (se 2 (by rfl) ⟨1306698, by rfl⟩ : syracuseStep 3484529 = 2613397) B2613397
theorem B3918755 : Blo 1833618 3918755 := bstep (se 1 (by rfl) ⟨2939066, by rfl⟩ : syracuseStep 3918755 = 5878133) B5878133
theorem B11750341 : Blo 1833618 11750341 := bstep (se 4 (by rfl) ⟨1101594, by rfl⟩ : syracuseStep 11750341 = 2203189) B2203189
theorem B11152333 : Blo 1833618 11152333 := bstep (se 3 (by rfl) ⟨2091062, by rfl⟩ : syracuseStep 11152333 = 4182125) B4182125
theorem B8817677 : Blo 1833618 8817677 := bstep (se 3 (by rfl) ⟨1653314, by rfl⟩ : syracuseStep 8817677 = 3306629) B3306629
theorem B6614065 : Blo 1833618 6614065 := bstep (se 2 (by rfl) ⟨2480274, by rfl⟩ : syracuseStep 6614065 = 4960549) B4960549
theorem B7441507 : Blo 1833618 7441507 := bstep (se 1 (by rfl) ⟨5581130, by rfl⟩ : syracuseStep 7441507 = 11162261) B11162261
theorem B6278417 : Blo 1833618 6278417 := bstep (se 2 (by rfl) ⟨2354406, by rfl⟩ : syracuseStep 6278417 = 4708813) B4708813
theorem B2321779 : Blo 1833618 2321779 := bstep (se 1 (by rfl) ⟨1741334, by rfl⟩ : syracuseStep 2321779 = 3482669) B3482669
theorem B2321875 : Blo 1833618 2321875 := bstep (se 1 (by rfl) ⟨1741406, by rfl⟩ : syracuseStep 2321875 = 3482813) B3482813
theorem B6188561 : Blo 1833618 6188561 := bstep (se 2 (by rfl) ⟨2320710, by rfl⟩ : syracuseStep 6188561 = 4641421) B4641421
theorem B5222033 : Blo 1833618 5222033 := bstep (se 2 (by rfl) ⟨1958262, by rfl⟩ : syracuseStep 5222033 = 3916525) B3916525
theorem B5877517 : Blo 1833618 5877517 := bstep (se 3 (by rfl) ⟨1102034, by rfl⟩ : syracuseStep 5877517 = 2204069) B2204069
theorem B14880581 : Blo 1833618 14880581 := bstep (se 4 (by rfl) ⟨1395054, by rfl⟩ : syracuseStep 14880581 = 2790109) B2790109
theorem B16732003 : Blo 1833618 16732003 := bstep (se 1 (by rfl) ⟨12549002, by rfl⟩ : syracuseStep 16732003 = 25098005) B25098005
theorem B14880611 : Blo 1833618 14880611 := bstep (se 1 (by rfl) ⟨11160458, by rfl⟩ : syracuseStep 14880611 = 22320917) B22320917
theorem B4960109 : Blo 1833618 4960109 := bstep (se 3 (by rfl) ⟨930020, by rfl⟩ : syracuseStep 4960109 = 1860041) B1860041
theorem B2092915 : Blo 1833618 2092915 := bstep (se 1 (by rfl) ⟨1569686, by rfl⟩ : syracuseStep 2092915 = 3139373) B3139373
theorem B2322371 : Blo 1833618 2322371 := bstep (se 1 (by rfl) ⟨1741778, by rfl⟩ : syracuseStep 2322371 = 3483557) B3483557
theorem B4960291 : Blo 1833618 4960291 := bstep (se 1 (by rfl) ⟨3720218, by rfl⟩ : syracuseStep 4960291 = 7440437) B7440437
theorem B6189101 : Blo 1833618 6189101 := bstep (se 3 (by rfl) ⟨1160456, by rfl⟩ : syracuseStep 6189101 = 2320913) B2320913
theorem B6189155 : Blo 1833618 6189155 := bstep (se 1 (by rfl) ⟨4641866, by rfl⟩ : syracuseStep 6189155 = 9283733) B9283733
theorem B3919985 : Blo 1833618 3919985 := bstep (se 2 (by rfl) ⟨1469994, by rfl⟩ : syracuseStep 3919985 = 2939989) B2939989
theorem B2478307 : Blo 1833618 2478307 := bstep (se 1 (by rfl) ⟨1858730, by rfl⟩ : syracuseStep 2478307 = 3717461) B3717461
theorem B7835953 : Blo 1833618 7835953 := bstep (se 2 (by rfl) ⟨2938482, by rfl⟩ : syracuseStep 7835953 = 5876965) B5876965
theorem B6189425 : Blo 1833618 6189425 := bstep (se 2 (by rfl) ⟨2321034, by rfl⟩ : syracuseStep 6189425 = 4642069) B4642069
theorem B9286001 : Blo 1833618 9286001 := bstep (se 2 (by rfl) ⟨3482250, by rfl⟩ : syracuseStep 9286001 = 6964501) B6964501
theorem B3305873 : Blo 1833618 3305873 := bstep (se 2 (by rfl) ⟨1239702, by rfl⟩ : syracuseStep 3305873 = 2479405) B2479405
theorem B5222819 : Blo 1833618 5222819 := bstep (se 1 (by rfl) ⟨3917114, by rfl⟩ : syracuseStep 5222819 = 7834229) B7834229
theorem B5878349 : Blo 1833618 5878349 := bstep (se 3 (by rfl) ⟨1102190, by rfl⟩ : syracuseStep 5878349 = 2204381) B2204381
theorem B47657585 : Blo 1833618 47657585 := bstep (se 2 (by rfl) ⟨17871594, by rfl⟩ : syracuseStep 47657585 = 35743189) B35743189
theorem B2323075 : Blo 1833618 2323075 := bstep (se 1 (by rfl) ⟨1742306, by rfl⟩ : syracuseStep 2323075 = 3484613) B3484613
theorem B2323171 : Blo 1833618 2323171 := bstep (se 1 (by rfl) ⟨1742378, by rfl⟩ : syracuseStep 2323171 = 3484757) B3484757
theorem B5223149 : Blo 1833618 5223149 := bstep (se 3 (by rfl) ⟨979340, by rfl⟩ : syracuseStep 5223149 = 1958681) B1958681
theorem B11760389 : Blo 1833618 11760389 := bstep (se 4 (by rfl) ⟨1102536, by rfl⟩ : syracuseStep 11760389 = 2205073) B2205073
theorem B5223217 : Blo 1833618 5223217 := bstep (se 2 (by rfl) ⟨1958706, by rfl⟩ : syracuseStep 5223217 = 3917413) B3917413
theorem B2937683 : Blo 1833618 2937683 := bstep (se 1 (by rfl) ⟨2203262, by rfl⟩ : syracuseStep 2937683 = 4406525) B4406525
theorem B9409393 : Blo 1833618 9409393 := bstep (se 2 (by rfl) ⟨3528522, by rfl⟩ : syracuseStep 9409393 = 7057045) B7057045
theorem B13218673 : Blo 1833618 13218673 := bstep (se 2 (by rfl) ⟨4957002, by rfl⟩ : syracuseStep 13218673 = 9914005) B9914005
theorem B6968177 : Blo 1833618 6968177 := bstep (se 2 (by rfl) ⟨2613066, by rfl⟩ : syracuseStep 6968177 = 5226133) B5226133
theorem B6189965 : Blo 1833618 6189965 := bstep (se 3 (by rfl) ⟨1160618, by rfl⟩ : syracuseStep 6189965 = 2321237) B2321237
theorem B2790305 : Blo 1833618 2790305 := bstep (se 2 (by rfl) ⟨1046364, by rfl⟩ : syracuseStep 2790305 = 2092729) B2092729
theorem B5297069 : Blo 1833618 5297069 := bstep (se 3 (by rfl) ⟨993200, by rfl⟩ : syracuseStep 5297069 = 1986401) B1986401
theorem B6190019 : Blo 1833618 6190019 := bstep (se 1 (by rfl) ⟨4642514, by rfl⟩ : syracuseStep 6190019 = 9285029) B9285029
theorem B4641745 : Blo 1833618 4641745 := bstep (se 2 (by rfl) ⟨1740654, by rfl⟩ : syracuseStep 4641745 = 3481309) B3481309
theorem B35754979 : Blo 1833618 35754979 := bstep (se 1 (by rfl) ⟨26816234, by rfl⟩ : syracuseStep 35754979 = 53632469) B53632469
theorem B5223491 : Blo 1833618 5223491 := bstep (se 1 (by rfl) ⟨3917618, by rfl⟩ : syracuseStep 5223491 = 7835237) B7835237
theorem B4125905 : Blo 1833618 4125905 := bstep (se 2 (by rfl) ⟨1547214, by rfl⟩ : syracuseStep 4125905 = 3094429) B3094429
theorem B6190289 : Blo 1833618 6190289 := bstep (se 2 (by rfl) ⟨2321358, by rfl⟩ : syracuseStep 6190289 = 4642717) B4642717
theorem B4125923 : Blo 1833618 4125923 := bstep (se 1 (by rfl) ⟨3094442, by rfl⟩ : syracuseStep 4125923 = 6188885) B6188885
theorem B4642019 : Blo 1833618 4642019 := bstep (se 1 (by rfl) ⟨3481514, by rfl⟩ : syracuseStep 4642019 = 6963029) B6963029
theorem B4642211 : Blo 1833618 4642211 := bstep (se 1 (by rfl) ⟨3481658, by rfl⟩ : syracuseStep 4642211 = 6963317) B6963317
theorem B4126193 : Blo 1833618 4126193 := bstep (se 2 (by rfl) ⟨1547322, by rfl⟩ : syracuseStep 4126193 = 3094645) B3094645
theorem B4126211 : Blo 1833618 4126211 := bstep (se 1 (by rfl) ⟨3094658, by rfl⟩ : syracuseStep 4126211 = 6189317) B6189317
theorem B11753059 : Blo 1833618 11753059 := bstep (se 1 (by rfl) ⟨8814794, by rfl⟩ : syracuseStep 11753059 = 17629589) B17629589
theorem B6190829 : Blo 1833618 6190829 := bstep (se 3 (by rfl) ⟨1160780, by rfl⟩ : syracuseStep 6190829 = 2321561) B2321561
theorem B14874353 : Blo 1833618 14874353 := bstep (se 2 (by rfl) ⟨5577882, by rfl⟩ : syracuseStep 14874353 = 11155765) B11155765
theorem B4126481 : Blo 1833618 4126481 := bstep (se 2 (by rfl) ⟨1547430, by rfl⟩ : syracuseStep 4126481 = 3094861) B3094861
theorem B4126499 : Blo 1833618 4126499 := bstep (se 1 (by rfl) ⟨3094874, by rfl⟩ : syracuseStep 4126499 = 6189749) B6189749
theorem B6190883 : Blo 1833618 6190883 := bstep (se 1 (by rfl) ⟨4643162, by rfl⟩ : syracuseStep 6190883 = 9286325) B9286325
theorem B9287459 : Blo 1833618 9287459 := bstep (se 1 (by rfl) ⟨6965594, by rfl⟩ : syracuseStep 9287459 = 13931189) B13931189
theorem B3094321 : Blo 1833618 3094321 := bstep (se 2 (by rfl) ⟨1160370, by rfl⟩ : syracuseStep 3094321 = 2320741) B2320741
theorem B2938675 : Blo 1833618 2938675 := bstep (se 1 (by rfl) ⟨2204006, by rfl⟩ : syracuseStep 2938675 = 4408013) B4408013
theorem B3094355 : Blo 1833618 3094355 := bstep (se 1 (by rfl) ⟨2320766, by rfl⟩ : syracuseStep 3094355 = 4641533) B4641533
theorem B2611073 : Blo 1833618 2611073 := bstep (se 2 (by rfl) ⟨979152, by rfl⟩ : syracuseStep 2611073 = 1958305) B1958305
theorem B5224333 : Blo 1833618 5224333 := bstep (se 3 (by rfl) ⟨979562, by rfl⟩ : syracuseStep 5224333 = 1959125) B1959125
theorem B2611153 : Blo 1833618 2611153 := bstep (se 2 (by rfl) ⟨979182, by rfl⟩ : syracuseStep 2611153 = 1958365) B1958365
theorem B3094483 : Blo 1833618 3094483 := bstep (se 1 (by rfl) ⟨2320862, by rfl⟩ : syracuseStep 3094483 = 4641725) B4641725
theorem B2750435 : Blo 1833618 2750435 := bstep (se 1 (by rfl) ⟨2062826, by rfl⟩ : syracuseStep 2750435 = 4125653) B4125653
theorem B2750465 : Blo 1833618 2750465 := bstep (se 2 (by rfl) ⟨1031424, by rfl⟩ : syracuseStep 2750465 = 2062849) B2062849
theorem B2750483 : Blo 1833618 2750483 := bstep (se 1 (by rfl) ⟨2062862, by rfl⟩ : syracuseStep 2750483 = 4125725) B4125725
theorem B2938913 : Blo 1833618 2938913 := bstep (se 2 (by rfl) ⟨1102092, by rfl⟩ : syracuseStep 2938913 = 2204185) B2204185
theorem B5224493 : Blo 1833618 5224493 := bstep (se 3 (by rfl) ⟨979592, by rfl⟩ : syracuseStep 5224493 = 1959185) B1959185
theorem B2750513 : Blo 1833618 2750513 := bstep (se 2 (by rfl) ⟨1031442, by rfl⟩ : syracuseStep 2750513 = 2062885) B2062885
theorem B4126769 : Blo 1833618 4126769 := bstep (se 2 (by rfl) ⟨1547538, by rfl⟩ : syracuseStep 4126769 = 3095077) B3095077
theorem B6191153 : Blo 1833618 6191153 := bstep (se 2 (by rfl) ⟨2321682, by rfl⟩ : syracuseStep 6191153 = 4643365) B4643365
theorem B2750531 : Blo 1833618 2750531 := bstep (se 1 (by rfl) ⟨2062898, by rfl⟩ : syracuseStep 2750531 = 4125797) B4125797
theorem B4126787 : Blo 1833618 4126787 := bstep (se 1 (by rfl) ⟨3095090, by rfl⟩ : syracuseStep 4126787 = 6190181) B6190181
theorem B15677509 : Blo 1833618 15677509 := bstep (se 4 (by rfl) ⟨1469766, by rfl⟩ : syracuseStep 15677509 = 2939533) B2939533
theorem B2750561 : Blo 1833618 2750561 := bstep (se 2 (by rfl) ⟨1031460, by rfl⟩ : syracuseStep 2750561 = 2062921) B2062921
theorem B3094625 : Blo 1833618 3094625 := bstep (se 2 (by rfl) ⟨1160484, by rfl⟩ : syracuseStep 3094625 = 2320969) B2320969
theorem B2750579 : Blo 1833618 2750579 := bstep (se 1 (by rfl) ⟨2062934, by rfl⟩ : syracuseStep 2750579 = 4125869) B4125869
theorem B2750609 : Blo 1833618 2750609 := bstep (se 2 (by rfl) ⟨1031478, by rfl⟩ : syracuseStep 2750609 = 2062957) B2062957
theorem B2750627 : Blo 1833618 2750627 := bstep (se 1 (by rfl) ⟨2062970, by rfl⟩ : syracuseStep 2750627 = 4125941) B4125941
theorem B2750657 : Blo 1833618 2750657 := bstep (se 2 (by rfl) ⟨1031496, by rfl⟩ : syracuseStep 2750657 = 2062993) B2062993
theorem B2750675 : Blo 1833618 2750675 := bstep (se 1 (by rfl) ⟨2063006, by rfl⟩ : syracuseStep 2750675 = 4126013) B4126013
theorem B3094753 : Blo 1833618 3094753 := bstep (se 2 (by rfl) ⟨1160532, by rfl⟩ : syracuseStep 3094753 = 2321065) B2321065
theorem B5224675 : Blo 1833618 5224675 := bstep (se 1 (by rfl) ⟨3918506, by rfl⟩ : syracuseStep 5224675 = 7837013) B7837013
theorem B2750705 : Blo 1833618 2750705 := bstep (se 2 (by rfl) ⟨1031514, by rfl⟩ : syracuseStep 2750705 = 2063029) B2063029
theorem B2939123 : Blo 1833618 2939123 := bstep (se 1 (by rfl) ⟨2204342, by rfl⟩ : syracuseStep 2939123 = 4408685) B4408685
theorem B2750723 : Blo 1833618 2750723 := bstep (se 1 (by rfl) ⟨2063042, by rfl⟩ : syracuseStep 2750723 = 4126085) B4126085
theorem B3094787 : Blo 1833618 3094787 := bstep (se 1 (by rfl) ⟨2321090, by rfl⟩ : syracuseStep 3094787 = 4642181) B4642181
theorem B2750753 : Blo 1833618 2750753 := bstep (se 2 (by rfl) ⟨1031532, by rfl⟩ : syracuseStep 2750753 = 2063065) B2063065
theorem B2750771 : Blo 1833618 2750771 := bstep (se 1 (by rfl) ⟨2063078, by rfl⟩ : syracuseStep 2750771 = 4126157) B4126157
theorem B2750801 : Blo 1833618 2750801 := bstep (se 2 (by rfl) ⟨1031550, by rfl⟩ : syracuseStep 2750801 = 2063101) B2063101
theorem B4127057 : Blo 1833618 4127057 := bstep (se 2 (by rfl) ⟨1547646, by rfl⟩ : syracuseStep 4127057 = 3095293) B3095293
theorem B4643153 : Blo 1833618 4643153 := bstep (se 2 (by rfl) ⟨1741182, by rfl⟩ : syracuseStep 4643153 = 3482365) B3482365
theorem B10443107 : Blo 1833618 10443107 := bstep (se 1 (by rfl) ⟨7832330, by rfl⟩ : syracuseStep 10443107 = 15664661) B15664661
theorem B6609251 : Blo 1833618 6609251 := bstep (se 1 (by rfl) ⟨4956938, by rfl⟩ : syracuseStep 6609251 = 9913877) B9913877
theorem B2750819 : Blo 1833618 2750819 := bstep (se 1 (by rfl) ⟨2063114, by rfl⟩ : syracuseStep 2750819 = 4126229) B4126229
theorem B4127075 : Blo 1833618 4127075 := bstep (se 1 (by rfl) ⟨3095306, by rfl⟩ : syracuseStep 4127075 = 6190613) B6190613
theorem B7158115 : Blo 1833618 7158115 := bstep (se 1 (by rfl) ⟨5368586, by rfl⟩ : syracuseStep 7158115 = 10737173) B10737173
theorem B2750849 : Blo 1833618 2750849 := bstep (se 2 (by rfl) ⟨1031568, by rfl⟩ : syracuseStep 2750849 = 2063137) B2063137
theorem B3094915 : Blo 1833618 3094915 := bstep (se 1 (by rfl) ⟨2321186, by rfl⟩ : syracuseStep 3094915 = 4642373) B4642373
theorem B4643203 : Blo 1833618 4643203 := bstep (se 1 (by rfl) ⟨3482402, by rfl⟩ : syracuseStep 4643203 = 6964805) B6964805
theorem B2750867 : Blo 1833618 2750867 := bstep (se 1 (by rfl) ⟨2063150, by rfl⟩ : syracuseStep 2750867 = 4126301) B4126301
theorem B2750897 : Blo 1833618 2750897 := bstep (se 2 (by rfl) ⟨1031586, by rfl⟩ : syracuseStep 2750897 = 2063173) B2063173
theorem B2750915 : Blo 1833618 2750915 := bstep (se 1 (by rfl) ⟨2063186, by rfl⟩ : syracuseStep 2750915 = 4126373) B4126373
theorem B2750945 : Blo 1833618 2750945 := bstep (se 2 (by rfl) ⟨1031604, by rfl⟩ : syracuseStep 2750945 = 2063209) B2063209
theorem B2750963 : Blo 1833618 2750963 := bstep (se 1 (by rfl) ⟨2063222, by rfl⟩ : syracuseStep 2750963 = 4126445) B4126445
theorem B4405763 : Blo 1833618 4405763 := bstep (se 1 (by rfl) ⟨3304322, by rfl⟩ : syracuseStep 4405763 = 6608645) B6608645
theorem B4643345 : Blo 1833618 4643345 := bstep (se 2 (by rfl) ⟨1741254, by rfl⟩ : syracuseStep 4643345 = 3482509) B3482509
theorem B2750993 : Blo 1833618 2750993 := bstep (se 2 (by rfl) ⟨1031622, by rfl⟩ : syracuseStep 2750993 = 2063245) B2063245
theorem B2062867 : Blo 1833618 2062867 := bstep (se 1 (by rfl) ⟨1547150, by rfl⟩ : syracuseStep 2062867 = 3094301) B3094301
theorem B3095057 : Blo 1833618 3095057 := bstep (se 2 (by rfl) ⟨1160646, by rfl⟩ : syracuseStep 3095057 = 2321293) B2321293
theorem B2751011 : Blo 1833618 2751011 := bstep (se 1 (by rfl) ⟨2063258, by rfl⟩ : syracuseStep 2751011 = 4126517) B4126517
theorem B2751041 : Blo 1833618 2751041 := bstep (se 2 (by rfl) ⟨1031640, by rfl⟩ : syracuseStep 2751041 = 2063281) B2063281
theorem B6191693 : Blo 1833618 6191693 := bstep (se 3 (by rfl) ⟨1160942, by rfl⟩ : syracuseStep 6191693 = 2321885) B2321885
theorem B9288269 : Blo 1833618 9288269 := bstep (se 3 (by rfl) ⟨1741550, by rfl⟩ : syracuseStep 9288269 = 3483101) B3483101
theorem B2751059 : Blo 1833618 2751059 := bstep (se 1 (by rfl) ⟨2063294, by rfl⟩ : syracuseStep 2751059 = 4126589) B4126589
theorem B13229027 : Blo 1833618 13229027 := bstep (se 1 (by rfl) ⟨9921770, by rfl⟩ : syracuseStep 13229027 = 19843541) B19843541
theorem B2751089 : Blo 1833618 2751089 := bstep (se 2 (by rfl) ⟨1031658, by rfl⟩ : syracuseStep 2751089 = 2063317) B2063317
theorem B4127345 : Blo 1833618 4127345 := bstep (se 2 (by rfl) ⟨1547754, by rfl⟩ : syracuseStep 4127345 = 3095509) B3095509
theorem B2751107 : Blo 1833618 2751107 := bstep (se 1 (by rfl) ⟨2063330, by rfl⟩ : syracuseStep 2751107 = 4126661) B4126661
theorem B4127363 : Blo 1833618 4127363 := bstep (se 1 (by rfl) ⟨3095522, by rfl⟩ : syracuseStep 4127363 = 6191045) B6191045
theorem B6191747 : Blo 1833618 6191747 := bstep (se 1 (by rfl) ⟨4643810, by rfl⟩ : syracuseStep 6191747 = 9287621) B9287621
theorem B5880451 : Blo 1833618 5880451 := bstep (se 1 (by rfl) ⟨4410338, by rfl⟩ : syracuseStep 5880451 = 8820677) B8820677
theorem B34388621 : Blo 1833618 34388621 := bstep (se 3 (by rfl) ⟨6447866, by rfl⟩ : syracuseStep 34388621 = 12895733) B12895733
theorem B25107085 : Blo 1833618 25107085 := bstep (se 3 (by rfl) ⟨4707578, by rfl⟩ : syracuseStep 25107085 = 9415157) B9415157
theorem B3095185 : Blo 1833618 3095185 := bstep (se 2 (by rfl) ⟨1160694, by rfl⟩ : syracuseStep 3095185 = 2321389) B2321389
theorem B1833619 : Blo 1833618 1833619 := bstep (se 1 (by rfl) ⟨1375214, by rfl⟩ : syracuseStep 1833619 = 2750429) B2750429
theorem B2751137 : Blo 1833618 2751137 := bstep (se 2 (by rfl) ⟨1031676, by rfl⟩ : syracuseStep 2751137 = 2063353) B2063353
theorem B1833635 : Blo 1833618 1833635 := bstep (se 1 (by rfl) ⟨1375226, by rfl⟩ : syracuseStep 1833635 = 2750453) B2750453
theorem B2063011 : Blo 1833618 2063011 := bstep (se 1 (by rfl) ⟨1547258, by rfl⟩ : syracuseStep 2063011 = 3094517) B3094517
theorem B1833651 : Blo 1833618 1833651 := bstep (se 1 (by rfl) ⟨1375238, by rfl⟩ : syracuseStep 1833651 = 2750477) B2750477
theorem B2751155 : Blo 1833618 2751155 := bstep (se 1 (by rfl) ⟨2063366, by rfl⟩ : syracuseStep 2751155 = 4126733) B4126733
theorem B3095219 : Blo 1833618 3095219 := bstep (se 1 (by rfl) ⟨2321414, by rfl⟩ : syracuseStep 3095219 = 4642829) B4642829
theorem B1833667 : Blo 1833618 1833667 := bstep (se 1 (by rfl) ⟨1375250, by rfl⟩ : syracuseStep 1833667 = 2750501) B2750501
theorem B2751185 : Blo 1833618 2751185 := bstep (se 2 (by rfl) ⟨1031694, by rfl⟩ : syracuseStep 2751185 = 2063389) B2063389
theorem B1833683 : Blo 1833618 1833683 := bstep (se 1 (by rfl) ⟨1375262, by rfl⟩ : syracuseStep 1833683 = 2750525) B2750525
theorem B1833699 : Blo 1833618 1833699 := bstep (se 1 (by rfl) ⟨1375274, by rfl⟩ : syracuseStep 1833699 = 2750549) B2750549
theorem B2751203 : Blo 1833618 2751203 := bstep (se 1 (by rfl) ⟨2063402, by rfl⟩ : syracuseStep 2751203 = 4126805) B4126805
theorem B2611939 : Blo 1833618 2611939 := bstep (se 1 (by rfl) ⟨1958954, by rfl⟩ : syracuseStep 2611939 = 3917909) B3917909
theorem B1833715 : Blo 1833618 1833715 := bstep (se 1 (by rfl) ⟨1375286, by rfl⟩ : syracuseStep 1833715 = 2750573) B2750573
theorem B2751233 : Blo 1833618 2751233 := bstep (se 2 (by rfl) ⟨1031712, by rfl⟩ : syracuseStep 2751233 = 2063425) B2063425
theorem B1833731 : Blo 1833618 1833731 := bstep (se 1 (by rfl) ⟨1375298, by rfl⟩ : syracuseStep 1833731 = 2750597) B2750597
theorem B5880593 : Blo 1833618 5880593 := bstep (se 2 (by rfl) ⟨2205222, by rfl⟩ : syracuseStep 5880593 = 4410445) B4410445
theorem B1833747 : Blo 1833618 1833747 := bstep (se 1 (by rfl) ⟨1375310, by rfl⟩ : syracuseStep 1833747 = 2750621) B2750621
theorem B2751251 : Blo 1833618 2751251 := bstep (se 1 (by rfl) ⟨2063438, by rfl⟩ : syracuseStep 2751251 = 4126877) B4126877
theorem B1833763 : Blo 1833618 1833763 := bstep (se 1 (by rfl) ⟨1375322, by rfl⟩ : syracuseStep 1833763 = 2750645) B2750645
theorem B2751281 : Blo 1833618 2751281 := bstep (se 2 (by rfl) ⟨1031730, by rfl⟩ : syracuseStep 2751281 = 2063461) B2063461
theorem B1833779 : Blo 1833618 1833779 := bstep (se 1 (by rfl) ⟨1375334, by rfl⟩ : syracuseStep 1833779 = 2750669) B2750669
theorem B2063155 : Blo 1833618 2063155 := bstep (se 1 (by rfl) ⟨1547366, by rfl⟩ : syracuseStep 2063155 = 3094733) B3094733
theorem B3095347 : Blo 1833618 3095347 := bstep (se 1 (by rfl) ⟨2321510, by rfl⟩ : syracuseStep 3095347 = 4643021) B4643021
theorem B1833795 : Blo 1833618 1833795 := bstep (se 1 (by rfl) ⟨1375346, by rfl⟩ : syracuseStep 1833795 = 2750693) B2750693
theorem B2751299 : Blo 1833618 2751299 := bstep (se 1 (by rfl) ⟨2063474, by rfl⟩ : syracuseStep 2751299 = 4126949) B4126949
theorem B1833811 : Blo 1833618 1833811 := bstep (se 1 (by rfl) ⟨1375358, by rfl⟩ : syracuseStep 1833811 = 2750717) B2750717
theorem B2751329 : Blo 1833618 2751329 := bstep (se 2 (by rfl) ⟨1031748, by rfl⟩ : syracuseStep 2751329 = 2063497) B2063497
theorem B1833827 : Blo 1833618 1833827 := bstep (se 1 (by rfl) ⟨1375370, by rfl⟩ : syracuseStep 1833827 = 2750741) B2750741
theorem B20904803 : Blo 1833618 20904803 := bstep (se 1 (by rfl) ⟨15678602, by rfl⟩ : syracuseStep 20904803 = 31357205) B31357205
theorem B35281777 : Blo 1833618 35281777 := bstep (se 2 (by rfl) ⟨13230666, by rfl⟩ : syracuseStep 35281777 = 26461333) B26461333
theorem B1833843 : Blo 1833618 1833843 := bstep (se 1 (by rfl) ⟨1375382, by rfl⟩ : syracuseStep 1833843 = 2750765) B2750765
theorem B2751347 : Blo 1833618 2751347 := bstep (se 1 (by rfl) ⟨2063510, by rfl⟩ : syracuseStep 2751347 = 4127021) B4127021
theorem B1833859 : Blo 1833618 1833859 := bstep (se 1 (by rfl) ⟨1375394, by rfl⟩ : syracuseStep 1833859 = 2750789) B2750789
theorem B13220749 : Blo 1833618 13220749 := bstep (se 3 (by rfl) ⟨2478890, by rfl⟩ : syracuseStep 13220749 = 4957781) B4957781
theorem B2751377 : Blo 1833618 2751377 := bstep (se 2 (by rfl) ⟨1031766, by rfl⟩ : syracuseStep 2751377 = 2063533) B2063533
theorem B4127633 : Blo 1833618 4127633 := bstep (se 2 (by rfl) ⟨1547862, by rfl⟩ : syracuseStep 4127633 = 3095725) B3095725
theorem B1833875 : Blo 1833618 1833875 := bstep (se 1 (by rfl) ⟨1375406, by rfl⟩ : syracuseStep 1833875 = 2750813) B2750813
theorem B6192017 : Blo 1833618 6192017 := bstep (se 2 (by rfl) ⟨2322006, by rfl⟩ : syracuseStep 6192017 = 4644013) B4644013
theorem B1833891 : Blo 1833618 1833891 := bstep (se 1 (by rfl) ⟨1375418, by rfl⟩ : syracuseStep 1833891 = 2750837) B2750837
theorem B2751395 : Blo 1833618 2751395 := bstep (se 1 (by rfl) ⟨2063546, by rfl⟩ : syracuseStep 2751395 = 4127093) B4127093
theorem B4127651 : Blo 1833618 4127651 := bstep (se 1 (by rfl) ⟨3095738, by rfl⟩ : syracuseStep 4127651 = 6191477) B6191477
theorem B1833907 : Blo 1833618 1833907 := bstep (se 1 (by rfl) ⟨1375430, by rfl⟩ : syracuseStep 1833907 = 2750861) B2750861
theorem B2751425 : Blo 1833618 2751425 := bstep (se 2 (by rfl) ⟨1031784, by rfl⟩ : syracuseStep 2751425 = 2063569) B2063569
theorem B3095489 : Blo 1833618 3095489 := bstep (se 2 (by rfl) ⟨1160808, by rfl⟩ : syracuseStep 3095489 = 2321617) B2321617
theorem B1833923 : Blo 1833618 1833923 := bstep (se 1 (by rfl) ⟨1375442, by rfl⟩ : syracuseStep 1833923 = 2750885) B2750885
theorem B2063299 : Blo 1833618 2063299 := bstep (se 1 (by rfl) ⟨1547474, by rfl⟩ : syracuseStep 2063299 = 3094949) B3094949
theorem B1833939 : Blo 1833618 1833939 := bstep (se 1 (by rfl) ⟨1375454, by rfl⟩ : syracuseStep 1833939 = 2750909) B2750909
theorem B2751443 : Blo 1833618 2751443 := bstep (se 1 (by rfl) ⟨2063582, by rfl⟩ : syracuseStep 2751443 = 4127165) B4127165
theorem B1833955 : Blo 1833618 1833955 := bstep (se 1 (by rfl) ⟨1375466, by rfl⟩ : syracuseStep 1833955 = 2750933) B2750933
theorem B3529699 : Blo 1833618 3529699 := bstep (se 1 (by rfl) ⟨2647274, by rfl⟩ : syracuseStep 3529699 = 5294549) B5294549
theorem B2751473 : Blo 1833618 2751473 := bstep (se 2 (by rfl) ⟨1031802, by rfl⟩ : syracuseStep 2751473 = 2063605) B2063605
theorem B1833971 : Blo 1833618 1833971 := bstep (se 1 (by rfl) ⟨1375478, by rfl⟩ : syracuseStep 1833971 = 2750957) B2750957
theorem B2939905 : Blo 1833618 2939905 := bstep (se 2 (by rfl) ⟨1102464, by rfl⟩ : syracuseStep 2939905 = 2204929) B2204929
theorem B1833987 : Blo 1833618 1833987 := bstep (se 1 (by rfl) ⟨1375490, by rfl⟩ : syracuseStep 1833987 = 2750981) B2750981
theorem B2751491 : Blo 1833618 2751491 := bstep (se 1 (by rfl) ⟨2063618, by rfl⟩ : syracuseStep 2751491 = 4127237) B4127237
theorem B1834003 : Blo 1833618 1834003 := bstep (se 1 (by rfl) ⟨1375502, by rfl⟩ : syracuseStep 1834003 = 2751005) B2751005
theorem B2751521 : Blo 1833618 2751521 := bstep (se 2 (by rfl) ⟨1031820, by rfl⟩ : syracuseStep 2751521 = 2063641) B2063641
theorem B1834019 : Blo 1833618 1834019 := bstep (se 1 (by rfl) ⟨1375514, by rfl⟩ : syracuseStep 1834019 = 2751029) B2751029
theorem B8813603 : Blo 1833618 8813603 := bstep (se 1 (by rfl) ⟨6610202, by rfl⟩ : syracuseStep 8813603 = 13220405) B13220405
theorem B6274093 : Blo 1833618 6274093 := bstep (se 3 (by rfl) ⟨1176392, by rfl⟩ : syracuseStep 6274093 = 2352785) B2352785
theorem B1834035 : Blo 1833618 1834035 := bstep (se 1 (by rfl) ⟨1375526, by rfl⟩ : syracuseStep 1834035 = 2751053) B2751053
theorem B2751539 : Blo 1833618 2751539 := bstep (se 1 (by rfl) ⟨2063654, by rfl⟩ : syracuseStep 2751539 = 4127309) B4127309
theorem B3095617 : Blo 1833618 3095617 := bstep (se 2 (by rfl) ⟨1160856, by rfl⟩ : syracuseStep 3095617 = 2321713) B2321713
theorem B1834051 : Blo 1833618 1834051 := bstep (se 1 (by rfl) ⟨1375538, by rfl⟩ : syracuseStep 1834051 = 2751077) B2751077
theorem B10452037 : Blo 1833618 10452037 := bstep (se 4 (by rfl) ⟨979878, by rfl⟩ : syracuseStep 10452037 = 1959757) B1959757
theorem B2751569 : Blo 1833618 2751569 := bstep (se 2 (by rfl) ⟨1031838, by rfl⟩ : syracuseStep 2751569 = 2063677) B2063677
theorem B1834067 : Blo 1833618 1834067 := bstep (se 1 (by rfl) ⟨1375550, by rfl⟩ : syracuseStep 1834067 = 2751101) B2751101
theorem B2063443 : Blo 1833618 2063443 := bstep (se 1 (by rfl) ⟨1547582, by rfl⟩ : syracuseStep 2063443 = 3095165) B3095165
theorem B1834083 : Blo 1833618 1834083 := bstep (se 1 (by rfl) ⟨1375562, by rfl⟩ : syracuseStep 1834083 = 2751125) B2751125
theorem B2751587 : Blo 1833618 2751587 := bstep (se 1 (by rfl) ⟨2063690, by rfl⟩ : syracuseStep 2751587 = 4127381) B4127381
theorem B3095651 : Blo 1833618 3095651 := bstep (se 1 (by rfl) ⟨2321738, by rfl⟩ : syracuseStep 3095651 = 4643477) B4643477
theorem B1834099 : Blo 1833618 1834099 := bstep (se 1 (by rfl) ⟨1375574, by rfl⟩ : syracuseStep 1834099 = 2751149) B2751149
theorem B2751617 : Blo 1833618 2751617 := bstep (se 2 (by rfl) ⟨1031856, by rfl⟩ : syracuseStep 2751617 = 2063713) B2063713
theorem B1834115 : Blo 1833618 1834115 := bstep (se 1 (by rfl) ⟨1375586, by rfl⟩ : syracuseStep 1834115 = 2751173) B2751173
theorem B1834131 : Blo 1833618 1834131 := bstep (se 1 (by rfl) ⟨1375598, by rfl⟩ : syracuseStep 1834131 = 2751197) B2751197
theorem B2751635 : Blo 1833618 2751635 := bstep (se 1 (by rfl) ⟨2063726, by rfl⟩ : syracuseStep 2751635 = 4127453) B4127453
theorem B1834147 : Blo 1833618 1834147 := bstep (se 1 (by rfl) ⟨1375610, by rfl⟩ : syracuseStep 1834147 = 2751221) B2751221
theorem B2751665 : Blo 1833618 2751665 := bstep (se 2 (by rfl) ⟨1031874, by rfl⟩ : syracuseStep 2751665 = 2063749) B2063749
theorem B4127921 : Blo 1833618 4127921 := bstep (se 2 (by rfl) ⟨1547970, by rfl⟩ : syracuseStep 4127921 = 3095941) B3095941
theorem B1834163 : Blo 1833618 1834163 := bstep (se 1 (by rfl) ⟨1375622, by rfl⟩ : syracuseStep 1834163 = 2751245) B2751245
theorem B4185265 : Blo 1833618 4185265 := bstep (se 2 (by rfl) ⟨1569474, by rfl⟩ : syracuseStep 4185265 = 3138949) B3138949
theorem B2612417 : Blo 1833618 2612417 := bstep (se 2 (by rfl) ⟨979656, by rfl⟩ : syracuseStep 2612417 = 1959313) B1959313
theorem B1834179 : Blo 1833618 1834179 := bstep (se 1 (by rfl) ⟨1375634, by rfl⟩ : syracuseStep 1834179 = 2751269) B2751269
theorem B2751683 : Blo 1833618 2751683 := bstep (se 1 (by rfl) ⟨2063762, by rfl⟩ : syracuseStep 2751683 = 4127525) B4127525
theorem B4127939 : Blo 1833618 4127939 := bstep (se 1 (by rfl) ⟨3095954, by rfl⟩ : syracuseStep 4127939 = 6191909) B6191909
theorem B1834195 : Blo 1833618 1834195 := bstep (se 1 (by rfl) ⟨1375646, by rfl⟩ : syracuseStep 1834195 = 2751293) B2751293
theorem B2751713 : Blo 1833618 2751713 := bstep (se 2 (by rfl) ⟨1031892, by rfl⟩ : syracuseStep 2751713 = 2063785) B2063785
theorem B1834211 : Blo 1833618 1834211 := bstep (se 1 (by rfl) ⟨1375658, by rfl⟩ : syracuseStep 1834211 = 2751317) B2751317
theorem B2063587 : Blo 1833618 2063587 := bstep (se 1 (by rfl) ⟨1547690, by rfl⟩ : syracuseStep 2063587 = 3095381) B3095381
theorem B3095779 : Blo 1833618 3095779 := bstep (se 1 (by rfl) ⟨2321834, by rfl⟩ : syracuseStep 3095779 = 4643669) B4643669
theorem B1834227 : Blo 1833618 1834227 := bstep (se 1 (by rfl) ⟨1375670, by rfl⟩ : syracuseStep 1834227 = 2751341) B2751341
theorem B2751731 : Blo 1833618 2751731 := bstep (se 1 (by rfl) ⟨2063798, by rfl⟩ : syracuseStep 2751731 = 4127597) B4127597
theorem B1834243 : Blo 1833618 1834243 := bstep (se 1 (by rfl) ⟨1375682, by rfl⟩ : syracuseStep 1834243 = 2751365) B2751365
theorem B2751761 : Blo 1833618 2751761 := bstep (se 2 (by rfl) ⟨1031910, by rfl⟩ : syracuseStep 2751761 = 2063821) B2063821
theorem B1834259 : Blo 1833618 1834259 := bstep (se 1 (by rfl) ⟨1375694, by rfl⟩ : syracuseStep 1834259 = 2751389) B2751389
theorem B1834275 : Blo 1833618 1834275 := bstep (se 1 (by rfl) ⟨1375706, by rfl⟩ : syracuseStep 1834275 = 2751413) B2751413
theorem B2751779 : Blo 1833618 2751779 := bstep (se 1 (by rfl) ⟨2063834, by rfl⟩ : syracuseStep 2751779 = 4127669) B4127669
theorem B8813873 : Blo 1833618 8813873 := bstep (se 2 (by rfl) ⟨3305202, by rfl⟩ : syracuseStep 8813873 = 6610405) B6610405
theorem B1834291 : Blo 1833618 1834291 := bstep (se 1 (by rfl) ⟨1375718, by rfl⟩ : syracuseStep 1834291 = 2751437) B2751437
theorem B2612531 : Blo 1833618 2612531 := bstep (se 1 (by rfl) ⟨1959398, by rfl⟩ : syracuseStep 2612531 = 3918797) B3918797
theorem B2751809 : Blo 1833618 2751809 := bstep (se 2 (by rfl) ⟨1031928, by rfl⟩ : syracuseStep 2751809 = 2063857) B2063857
theorem B1834307 : Blo 1833618 1834307 := bstep (se 1 (by rfl) ⟨1375730, by rfl⟩ : syracuseStep 1834307 = 2751461) B2751461
theorem B4242755 : Blo 1833618 4242755 := bstep (se 1 (by rfl) ⟨3182066, by rfl⟩ : syracuseStep 4242755 = 6364133) B6364133
theorem B4406609 : Blo 1833618 4406609 := bstep (se 2 (by rfl) ⟨1652478, by rfl⟩ : syracuseStep 4406609 = 3304957) B3304957
theorem B1834323 : Blo 1833618 1834323 := bstep (se 1 (by rfl) ⟨1375742, by rfl⟩ : syracuseStep 1834323 = 2751485) B2751485
theorem B2751827 : Blo 1833618 2751827 := bstep (se 1 (by rfl) ⟨2063870, by rfl⟩ : syracuseStep 2751827 = 4127741) B4127741
theorem B1834339 : Blo 1833618 1834339 := bstep (se 1 (by rfl) ⟨1375754, by rfl⟩ : syracuseStep 1834339 = 2751509) B2751509
theorem B2751857 : Blo 1833618 2751857 := bstep (se 2 (by rfl) ⟨1031946, by rfl⟩ : syracuseStep 2751857 = 2063893) B2063893
theorem B3095921 : Blo 1833618 3095921 := bstep (se 2 (by rfl) ⟨1160970, by rfl⟩ : syracuseStep 3095921 = 2321941) B2321941
theorem B1834355 : Blo 1833618 1834355 := bstep (se 1 (by rfl) ⟨1375766, by rfl⟩ : syracuseStep 1834355 = 2751533) B2751533
theorem B2063731 : Blo 1833618 2063731 := bstep (se 1 (by rfl) ⟨1547798, by rfl⟩ : syracuseStep 2063731 = 3095597) B3095597
theorem B1834371 : Blo 1833618 1834371 := bstep (se 1 (by rfl) ⟨1375778, by rfl⟩ : syracuseStep 1834371 = 2751557) B2751557
theorem B2751875 : Blo 1833618 2751875 := bstep (se 1 (by rfl) ⟨2063906, by rfl⟩ : syracuseStep 2751875 = 4127813) B4127813
theorem B2612611 : Blo 1833618 2612611 := bstep (se 1 (by rfl) ⟨1959458, by rfl⟩ : syracuseStep 2612611 = 3918917) B3918917
theorem B7060877 : Blo 1833618 7060877 := bstep (se 3 (by rfl) ⟨1323914, by rfl⟩ : syracuseStep 7060877 = 2647829) B2647829
theorem B22322573 : Blo 1833618 22322573 := bstep (se 3 (by rfl) ⟨4185482, by rfl⟩ : syracuseStep 22322573 = 8370965) B8370965
theorem B1834387 : Blo 1833618 1834387 := bstep (se 1 (by rfl) ⟨1375790, by rfl⟩ : syracuseStep 1834387 = 2751581) B2751581
theorem B2751905 : Blo 1833618 2751905 := bstep (se 2 (by rfl) ⟨1031964, by rfl⟩ : syracuseStep 2751905 = 2063929) B2063929
theorem B8813987 : Blo 1833618 8813987 := bstep (se 1 (by rfl) ⟨6610490, by rfl⟩ : syracuseStep 8813987 = 13220981) B13220981
theorem B1834403 : Blo 1833618 1834403 := bstep (se 1 (by rfl) ⟨1375802, by rfl⟩ : syracuseStep 1834403 = 2751605) B2751605
theorem B6192557 : Blo 1833618 6192557 := bstep (se 3 (by rfl) ⟨1161104, by rfl⟩ : syracuseStep 6192557 = 2322209) B2322209
theorem B1834419 : Blo 1833618 1834419 := bstep (se 1 (by rfl) ⟨1375814, by rfl⟩ : syracuseStep 1834419 = 2751629) B2751629
theorem B2751923 : Blo 1833618 2751923 := bstep (se 1 (by rfl) ⟨2063942, by rfl⟩ : syracuseStep 2751923 = 4127885) B4127885
theorem B1834435 : Blo 1833618 1834435 := bstep (se 1 (by rfl) ⟨1375826, by rfl⟩ : syracuseStep 1834435 = 2751653) B2751653
theorem B10591685 : Blo 1833618 10591685 := bstep (se 4 (by rfl) ⟨992970, by rfl⟩ : syracuseStep 10591685 = 1985941) B1985941
theorem B2751953 : Blo 1833618 2751953 := bstep (se 2 (by rfl) ⟨1031982, by rfl⟩ : syracuseStep 2751953 = 2063965) B2063965
theorem B4128209 : Blo 1833618 4128209 := bstep (se 2 (by rfl) ⟨1548078, by rfl⟩ : syracuseStep 4128209 = 3096157) B3096157
theorem B1834451 : Blo 1833618 1834451 := bstep (se 1 (by rfl) ⟨1375838, by rfl⟩ : syracuseStep 1834451 = 2751677) B2751677
theorem B1834467 : Blo 1833618 1834467 := bstep (se 1 (by rfl) ⟨1375850, by rfl⟩ : syracuseStep 1834467 = 2751701) B2751701
theorem B2751971 : Blo 1833618 2751971 := bstep (se 1 (by rfl) ⟨2063978, by rfl⟩ : syracuseStep 2751971 = 4127957) B4127957
theorem B4128227 : Blo 1833618 4128227 := bstep (se 1 (by rfl) ⟨3096170, by rfl⟩ : syracuseStep 4128227 = 6192341) B6192341
theorem B6192611 : Blo 1833618 6192611 := bstep (se 1 (by rfl) ⟨4644458, by rfl⟩ : syracuseStep 6192611 = 9288917) B9288917
theorem B3096049 : Blo 1833618 3096049 := bstep (se 2 (by rfl) ⟨1161018, by rfl⟩ : syracuseStep 3096049 = 2322037) B2322037
theorem B1834483 : Blo 1833618 1834483 := bstep (se 1 (by rfl) ⟨1375862, by rfl⟩ : syracuseStep 1834483 = 2751725) B2751725
theorem B4644337 : Blo 1833618 4644337 := bstep (se 2 (by rfl) ⟨1741626, by rfl⟩ : syracuseStep 4644337 = 3483253) B3483253
theorem B2752001 : Blo 1833618 2752001 := bstep (se 2 (by rfl) ⟨1032000, by rfl⟩ : syracuseStep 2752001 = 2064001) B2064001
theorem B1834499 : Blo 1833618 1834499 := bstep (se 1 (by rfl) ⟨1375874, by rfl⟩ : syracuseStep 1834499 = 2751749) B2751749
theorem B2063875 : Blo 1833618 2063875 := bstep (se 1 (by rfl) ⟨1547906, by rfl⟩ : syracuseStep 2063875 = 3095813) B3095813
theorem B1834515 : Blo 1833618 1834515 := bstep (se 1 (by rfl) ⟨1375886, by rfl⟩ : syracuseStep 1834515 = 2751773) B2751773
theorem B2752019 : Blo 1833618 2752019 := bstep (se 1 (by rfl) ⟨2064014, by rfl⟩ : syracuseStep 2752019 = 4128029) B4128029
theorem B3096083 : Blo 1833618 3096083 := bstep (se 1 (by rfl) ⟨2322062, by rfl⟩ : syracuseStep 3096083 = 4644125) B4644125
theorem B1834531 : Blo 1833618 1834531 := bstep (se 1 (by rfl) ⟨1375898, by rfl⟩ : syracuseStep 1834531 = 2751797) B2751797
theorem B11755057 : Blo 1833618 11755057 := bstep (se 2 (by rfl) ⟨4408146, by rfl⟩ : syracuseStep 11755057 = 8816293) B8816293
theorem B2752049 : Blo 1833618 2752049 := bstep (se 2 (by rfl) ⟨1032018, by rfl⟩ : syracuseStep 2752049 = 2064037) B2064037
theorem B1834547 : Blo 1833618 1834547 := bstep (se 1 (by rfl) ⟨1375910, by rfl⟩ : syracuseStep 1834547 = 2751821) B2751821
theorem B1834563 : Blo 1833618 1834563 := bstep (se 1 (by rfl) ⟨1375922, by rfl⟩ : syracuseStep 1834563 = 2751845) B2751845
theorem B2752067 : Blo 1833618 2752067 := bstep (se 1 (by rfl) ⟨2064050, by rfl⟩ : syracuseStep 2752067 = 4128101) B4128101
theorem B1834579 : Blo 1833618 1834579 := bstep (se 1 (by rfl) ⟨1375934, by rfl⟩ : syracuseStep 1834579 = 2751869) B2751869
theorem B5226065 : Blo 1833618 5226065 := bstep (se 2 (by rfl) ⟨1959774, by rfl⟩ : syracuseStep 5226065 = 3919549) B3919549
theorem B2752097 : Blo 1833618 2752097 := bstep (se 2 (by rfl) ⟨1032036, by rfl⟩ : syracuseStep 2752097 = 2064073) B2064073
theorem B1834595 : Blo 1833618 1834595 := bstep (se 1 (by rfl) ⟨1375946, by rfl⟩ : syracuseStep 1834595 = 2751893) B2751893
theorem B13401713 : Blo 1833618 13401713 := bstep (se 2 (by rfl) ⟨5025642, by rfl⟩ : syracuseStep 13401713 = 10051285) B10051285
theorem B1834611 : Blo 1833618 1834611 := bstep (se 1 (by rfl) ⟨1375958, by rfl⟩ : syracuseStep 1834611 = 2751917) B2751917
theorem B2752115 : Blo 1833618 2752115 := bstep (se 1 (by rfl) ⟨2064086, by rfl⟩ : syracuseStep 2752115 = 4128173) B4128173
theorem B1834627 : Blo 1833618 1834627 := bstep (se 1 (by rfl) ⟨1375970, by rfl⟩ : syracuseStep 1834627 = 2751941) B2751941
theorem B2752145 : Blo 1833618 2752145 := bstep (se 2 (by rfl) ⟨1032054, by rfl⟩ : syracuseStep 2752145 = 2064109) B2064109
theorem B1834643 : Blo 1833618 1834643 := bstep (se 1 (by rfl) ⟨1375982, by rfl⟩ : syracuseStep 1834643 = 2751965) B2751965
theorem B2064019 : Blo 1833618 2064019 := bstep (se 1 (by rfl) ⟨1548014, by rfl⟩ : syracuseStep 2064019 = 3096029) B3096029
theorem B3096211 : Blo 1833618 3096211 := bstep (se 1 (by rfl) ⟨2322158, by rfl⟩ : syracuseStep 3096211 = 4644317) B4644317
theorem B1834659 : Blo 1833618 1834659 := bstep (se 1 (by rfl) ⟨1375994, by rfl⟩ : syracuseStep 1834659 = 2751989) B2751989
theorem B2752163 : Blo 1833618 2752163 := bstep (se 1 (by rfl) ⟨2064122, by rfl⟩ : syracuseStep 2752163 = 4128245) B4128245
theorem B1834675 : Blo 1833618 1834675 := bstep (se 1 (by rfl) ⟨1376006, by rfl⟩ : syracuseStep 1834675 = 2752013) B2752013
theorem B2752193 : Blo 1833618 2752193 := bstep (se 2 (by rfl) ⟨1032072, by rfl⟩ : syracuseStep 2752193 = 2064145) B2064145
theorem B1834691 : Blo 1833618 1834691 := bstep (se 1 (by rfl) ⟨1376018, by rfl⟩ : syracuseStep 1834691 = 2752037) B2752037
theorem B1834707 : Blo 1833618 1834707 := bstep (se 1 (by rfl) ⟨1376030, by rfl⟩ : syracuseStep 1834707 = 2752061) B2752061
theorem B2752211 : Blo 1833618 2752211 := bstep (se 1 (by rfl) ⟨2064158, by rfl⟩ : syracuseStep 2752211 = 4128317) B4128317
theorem B2653921 : Blo 1833618 2653921 := bstep (se 2 (by rfl) ⟨995220, by rfl⟩ : syracuseStep 2653921 = 1990441) B1990441
theorem B1834723 : Blo 1833618 1834723 := bstep (se 1 (by rfl) ⟨1376042, by rfl⟩ : syracuseStep 1834723 = 2752085) B2752085
theorem B2752241 : Blo 1833618 2752241 := bstep (se 2 (by rfl) ⟨1032090, by rfl⟩ : syracuseStep 2752241 = 2064181) B2064181
theorem B4128497 : Blo 1833618 4128497 := bstep (se 2 (by rfl) ⟨1548186, by rfl⟩ : syracuseStep 4128497 = 3096373) B3096373
theorem B1834739 : Blo 1833618 1834739 := bstep (se 1 (by rfl) ⟨1376054, by rfl⟩ : syracuseStep 1834739 = 2752109) B2752109
theorem B6192881 : Blo 1833618 6192881 := bstep (se 2 (by rfl) ⟨2322330, by rfl⟩ : syracuseStep 6192881 = 4644661) B4644661
theorem B1834755 : Blo 1833618 1834755 := bstep (se 1 (by rfl) ⟨1376066, by rfl⟩ : syracuseStep 1834755 = 2752133) B2752133
theorem B2752259 : Blo 1833618 2752259 := bstep (se 1 (by rfl) ⟨2064194, by rfl⟩ : syracuseStep 2752259 = 4128389) B4128389
theorem B4128515 : Blo 1833618 4128515 := bstep (se 1 (by rfl) ⟨3096386, by rfl⟩ : syracuseStep 4128515 = 6192773) B6192773
theorem B4644611 : Blo 1833618 4644611 := bstep (se 1 (by rfl) ⟨3483458, by rfl⟩ : syracuseStep 4644611 = 6966917) B6966917
theorem B1834771 : Blo 1833618 1834771 := bstep (se 1 (by rfl) ⟨1376078, by rfl⟩ : syracuseStep 1834771 = 2752157) B2752157
theorem B2752289 : Blo 1833618 2752289 := bstep (se 2 (by rfl) ⟨1032108, by rfl⟩ : syracuseStep 2752289 = 2064217) B2064217
theorem B3096353 : Blo 1833618 3096353 := bstep (se 2 (by rfl) ⟨1161132, by rfl⟩ : syracuseStep 3096353 = 2322265) B2322265
theorem B1834787 : Blo 1833618 1834787 := bstep (se 1 (by rfl) ⟨1376090, by rfl⟩ : syracuseStep 1834787 = 2752181) B2752181
theorem B2064163 : Blo 1833618 2064163 := bstep (se 1 (by rfl) ⟨1548122, by rfl⟩ : syracuseStep 2064163 = 3096245) B3096245
theorem B3481393 : Blo 1833618 3481393 := bstep (se 2 (by rfl) ⟨1305522, by rfl⟩ : syracuseStep 3481393 = 2611045) B2611045
theorem B1834803 : Blo 1833618 1834803 := bstep (se 1 (by rfl) ⟨1376102, by rfl⟩ : syracuseStep 1834803 = 2752205) B2752205
theorem B2752307 : Blo 1833618 2752307 := bstep (se 1 (by rfl) ⟨2064230, by rfl⟩ : syracuseStep 2752307 = 4128461) B4128461
theorem B1834819 : Blo 1833618 1834819 := bstep (se 1 (by rfl) ⟨1376114, by rfl⟩ : syracuseStep 1834819 = 2752229) B2752229
theorem B2752337 : Blo 1833618 2752337 := bstep (se 2 (by rfl) ⟨1032126, by rfl⟩ : syracuseStep 2752337 = 2064253) B2064253
theorem B1834835 : Blo 1833618 1834835 := bstep (se 1 (by rfl) ⟨1376126, by rfl⟩ : syracuseStep 1834835 = 2752253) B2752253
theorem B6963043 : Blo 1833618 6963043 := bstep (se 1 (by rfl) ⟨5222282, by rfl⟩ : syracuseStep 6963043 = 10444565) B10444565
theorem B4407139 : Blo 1833618 4407139 := bstep (se 1 (by rfl) ⟨3305354, by rfl⟩ : syracuseStep 4407139 = 6610709) B6610709
theorem B1834851 : Blo 1833618 1834851 := bstep (se 1 (by rfl) ⟨1376138, by rfl⟩ : syracuseStep 1834851 = 2752277) B2752277
theorem B2752355 : Blo 1833618 2752355 := bstep (se 1 (by rfl) ⟨2064266, by rfl⟩ : syracuseStep 2752355 = 4128533) B4128533
theorem B1834867 : Blo 1833618 1834867 := bstep (se 1 (by rfl) ⟨1376150, by rfl⟩ : syracuseStep 1834867 = 2752301) B2752301
theorem B2752385 : Blo 1833618 2752385 := bstep (se 2 (by rfl) ⟨1032144, by rfl⟩ : syracuseStep 2752385 = 2064289) B2064289
theorem B1834883 : Blo 1833618 1834883 := bstep (se 1 (by rfl) ⟨1376162, by rfl⟩ : syracuseStep 1834883 = 2752325) B2752325
theorem B1834899 : Blo 1833618 1834899 := bstep (se 1 (by rfl) ⟨1376174, by rfl⟩ : syracuseStep 1834899 = 2752349) B2752349
theorem B2752403 : Blo 1833618 2752403 := bstep (se 1 (by rfl) ⟨2064302, by rfl⟩ : syracuseStep 2752403 = 4128605) B4128605
theorem B1834915 : Blo 1833618 1834915 := bstep (se 1 (by rfl) ⟨1376186, by rfl⟩ : syracuseStep 1834915 = 2752373) B2752373
theorem B3096481 : Blo 1833618 3096481 := bstep (se 2 (by rfl) ⟨1161180, by rfl⟩ : syracuseStep 3096481 = 2322361) B2322361
theorem B2752433 : Blo 1833618 2752433 := bstep (se 2 (by rfl) ⟨1032162, by rfl⟩ : syracuseStep 2752433 = 2064325) B2064325
theorem B2613169 : Blo 1833618 2613169 := bstep (se 2 (by rfl) ⟨979938, by rfl⟩ : syracuseStep 2613169 = 1959877) B1959877
theorem B1834931 : Blo 1833618 1834931 := bstep (se 1 (by rfl) ⟨1376198, by rfl⟩ : syracuseStep 1834931 = 2752397) B2752397
theorem B2064307 : Blo 1833618 2064307 := bstep (se 1 (by rfl) ⟨1548230, by rfl⟩ : syracuseStep 2064307 = 3096461) B3096461
theorem B1834947 : Blo 1833618 1834947 := bstep (se 1 (by rfl) ⟨1376210, by rfl⟩ : syracuseStep 1834947 = 2752421) B2752421
theorem B2752451 : Blo 1833618 2752451 := bstep (se 1 (by rfl) ⟨2064338, by rfl⟩ : syracuseStep 2752451 = 4128677) B4128677
theorem B3096515 : Blo 1833618 3096515 := bstep (se 1 (by rfl) ⟨2322386, by rfl⟩ : syracuseStep 3096515 = 4644773) B4644773
theorem B4644803 : Blo 1833618 4644803 := bstep (se 1 (by rfl) ⟨3483602, by rfl⟩ : syracuseStep 4644803 = 6967205) B6967205
theorem B1834963 : Blo 1833618 1834963 := bstep (se 1 (by rfl) ⟨1376222, by rfl⟩ : syracuseStep 1834963 = 2752445) B2752445
theorem B2752481 : Blo 1833618 2752481 := bstep (se 2 (by rfl) ⟨1032180, by rfl⟩ : syracuseStep 2752481 = 2064361) B2064361
theorem B1834979 : Blo 1833618 1834979 := bstep (se 1 (by rfl) ⟨1376234, by rfl⟩ : syracuseStep 1834979 = 2752469) B2752469
theorem B1834995 : Blo 1833618 1834995 := bstep (se 1 (by rfl) ⟨1376246, by rfl⟩ : syracuseStep 1834995 = 2752493) B2752493
theorem B2752499 : Blo 1833618 2752499 := bstep (se 1 (by rfl) ⟨2064374, by rfl⟩ : syracuseStep 2752499 = 4128749) B4128749
theorem B7946243 : Blo 1833618 7946243 := bstep (se 1 (by rfl) ⟨5959682, by rfl⟩ : syracuseStep 7946243 = 11919365) B11919365
theorem B15679493 : Blo 1833618 15679493 := bstep (se 4 (by rfl) ⟨1469952, by rfl⟩ : syracuseStep 15679493 = 2939905) B2939905
theorem B2752523 : Blo 1833618 2752523 := bstep (se 1 (by rfl) ⟨2064392, by rfl⟩ : syracuseStep 2752523 = 4128785) B4128785
theorem B1835019 : Blo 1833618 1835019 := bstep (se 1 (by rfl) ⟨1376264, by rfl⟩ : syracuseStep 1835019 = 2752529) B2752529
theorem B2752535 : Blo 1833618 2752535 := bstep (se 1 (by rfl) ⟨2064401, by rfl⟩ : syracuseStep 2752535 = 4128803) B4128803
theorem B1835031 : Blo 1833618 1835031 := bstep (se 1 (by rfl) ⟨1376273, by rfl⟩ : syracuseStep 1835031 = 2752547) B2752547
theorem B1835051 : Blo 1833618 1835051 := bstep (se 1 (by rfl) ⟨1376288, by rfl⟩ : syracuseStep 1835051 = 2752577) B2752577
theorem B7258157 : Blo 1833618 7258157 := bstep (se 3 (by rfl) ⟨1360904, by rfl⟩ : syracuseStep 7258157 = 2721809) B2721809
theorem B1835063 : Blo 1833618 1835063 := bstep (se 1 (by rfl) ⟨1376297, by rfl⟩ : syracuseStep 1835063 = 2752595) B2752595
theorem B1835083 : Blo 1833618 1835083 := bstep (se 1 (by rfl) ⟨1376312, by rfl⟩ : syracuseStep 1835083 = 2752625) B2752625
theorem B2613323 : Blo 1833618 2613323 := bstep (se 1 (by rfl) ⟨1959992, by rfl⟩ : syracuseStep 2613323 = 3919985) B3919985
theorem B1835095 : Blo 1833618 1835095 := bstep (se 1 (by rfl) ⟨1376321, by rfl⟩ : syracuseStep 1835095 = 2752643) B2752643
theorem B4128857 : Blo 1833618 4128857 := bstep (se 2 (by rfl) ⟨1548321, by rfl⟩ : syracuseStep 4128857 = 3096643) B3096643
theorem B2752601 : Blo 1833618 2752601 := bstep (se 2 (by rfl) ⟨1032225, by rfl⟩ : syracuseStep 2752601 = 2064451) B2064451
theorem B1835115 : Blo 1833618 1835115 := bstep (se 1 (by rfl) ⟨1376336, by rfl⟩ : syracuseStep 1835115 = 2752673) B2752673
theorem B1835127 : Blo 1833618 1835127 := bstep (se 1 (by rfl) ⟨1376345, by rfl⟩ : syracuseStep 1835127 = 2752691) B2752691
theorem B2064523 : Blo 1833618 2064523 := bstep (se 1 (by rfl) ⟨1548392, by rfl⟩ : syracuseStep 2064523 = 3096785) B3096785
theorem B1835147 : Blo 1833618 1835147 := bstep (se 1 (by rfl) ⟨1376360, by rfl⟩ : syracuseStep 1835147 = 2752721) B2752721
theorem B1835159 : Blo 1833618 1835159 := bstep (se 1 (by rfl) ⟨1376369, by rfl⟩ : syracuseStep 1835159 = 2752739) B2752739
theorem B1835179 : Blo 1833618 1835179 := bstep (se 1 (by rfl) ⟨1376384, by rfl⟩ : syracuseStep 1835179 = 2752769) B2752769
theorem B4128947 : Blo 1833618 4128947 := bstep (se 1 (by rfl) ⟨3096710, by rfl⟩ : syracuseStep 4128947 = 6193421) B6193421
theorem B1835191 : Blo 1833618 1835191 := bstep (se 1 (by rfl) ⟨1376393, by rfl⟩ : syracuseStep 1835191 = 2752787) B2752787
theorem B2752715 : Blo 1833618 2752715 := bstep (se 1 (by rfl) ⟨2064536, by rfl⟩ : syracuseStep 2752715 = 4129073) B4129073
theorem B1835211 : Blo 1833618 1835211 := bstep (se 1 (by rfl) ⟨1376408, by rfl⟩ : syracuseStep 1835211 = 2752817) B2752817
theorem B4128983 : Blo 1833618 4128983 := bstep (se 1 (by rfl) ⟨3096737, by rfl⟩ : syracuseStep 4128983 = 6193475) B6193475
theorem B2752727 : Blo 1833618 2752727 := bstep (se 1 (by rfl) ⟨2064545, by rfl⟩ : syracuseStep 2752727 = 4129091) B4129091
theorem B1835223 : Blo 1833618 1835223 := bstep (se 1 (by rfl) ⟨1376417, by rfl⟩ : syracuseStep 1835223 = 2752835) B2752835
theorem B1835243 : Blo 1833618 1835243 := bstep (se 1 (by rfl) ⟨1376432, by rfl⟩ : syracuseStep 1835243 = 2752865) B2752865
theorem B2064631 : Blo 1833618 2064631 := bstep (se 1 (by rfl) ⟨1548473, by rfl⟩ : syracuseStep 2064631 = 3096947) B3096947
theorem B1835255 : Blo 1833618 1835255 := bstep (se 1 (by rfl) ⟨1376441, by rfl⟩ : syracuseStep 1835255 = 2752883) B2752883
theorem B35275013 : Blo 1833618 35275013 := bstep (se 4 (by rfl) ⟨3307032, by rfl⟩ : syracuseStep 35275013 = 6614065) B6614065
theorem B1835275 : Blo 1833618 1835275 := bstep (se 1 (by rfl) ⟨1376456, by rfl⟩ : syracuseStep 1835275 = 2752913) B2752913
theorem B3481879 : Blo 1833618 3481879 := bstep (se 1 (by rfl) ⟨2611409, by rfl⟩ : syracuseStep 3481879 = 5222819) B5222819
theorem B1835287 : Blo 1833618 1835287 := bstep (se 1 (by rfl) ⟨1376465, by rfl⟩ : syracuseStep 1835287 = 2752931) B2752931
theorem B2752793 : Blo 1833618 2752793 := bstep (se 2 (by rfl) ⟨1032297, by rfl⟩ : syracuseStep 2752793 = 2064595) B2064595
theorem B1835307 : Blo 1833618 1835307 := bstep (se 1 (by rfl) ⟨1376480, by rfl⟩ : syracuseStep 1835307 = 2752961) B2752961
theorem B1835319 : Blo 1833618 1835319 := bstep (se 1 (by rfl) ⟨1376489, by rfl⟩ : syracuseStep 1835319 = 2752979) B2752979
theorem B10453313 : Blo 1833618 10453313 := bstep (se 2 (by rfl) ⟨3919992, by rfl⟩ : syracuseStep 10453313 = 7839985) B7839985
theorem B1835339 : Blo 1833618 1835339 := bstep (se 1 (by rfl) ⟨1376504, by rfl⟩ : syracuseStep 1835339 = 2753009) B2753009
theorem B1835351 : Blo 1833618 1835351 := bstep (se 1 (by rfl) ⟨1376513, by rfl⟩ : syracuseStep 1835351 = 2753027) B2753027
theorem B1835371 : Blo 1833618 1835371 := bstep (se 1 (by rfl) ⟨1376528, by rfl⟩ : syracuseStep 1835371 = 2753057) B2753057
theorem B1835383 : Blo 1833618 1835383 := bstep (se 1 (by rfl) ⟨1376537, by rfl⟩ : syracuseStep 1835383 = 2753075) B2753075
theorem B4129163 : Blo 1833618 4129163 := bstep (se 1 (by rfl) ⟨3096872, by rfl⟩ : syracuseStep 4129163 = 6193745) B6193745
theorem B2752907 : Blo 1833618 2752907 := bstep (se 1 (by rfl) ⟨2064680, by rfl⟩ : syracuseStep 2752907 = 4129361) B4129361
theorem B1835403 : Blo 1833618 1835403 := bstep (se 1 (by rfl) ⟨1376552, by rfl⟩ : syracuseStep 1835403 = 2753105) B2753105
theorem B3916183 : Blo 1833618 3916183 := bstep (se 1 (by rfl) ⟨2937137, by rfl⟩ : syracuseStep 3916183 = 5874275) B5874275
theorem B2752919 : Blo 1833618 2752919 := bstep (se 1 (by rfl) ⟨2064689, by rfl⟩ : syracuseStep 2752919 = 4129379) B4129379
theorem B1835415 : Blo 1833618 1835415 := bstep (se 1 (by rfl) ⟨1376561, by rfl⟩ : syracuseStep 1835415 = 2753123) B2753123
theorem B2064811 : Blo 1833618 2064811 := bstep (se 1 (by rfl) ⟨1548608, by rfl⟩ : syracuseStep 2064811 = 3097217) B3097217
theorem B1835435 : Blo 1833618 1835435 := bstep (se 1 (by rfl) ⟨1376576, by rfl⟩ : syracuseStep 1835435 = 2753153) B2753153
theorem B1835447 : Blo 1833618 1835447 := bstep (se 1 (by rfl) ⟨1376585, by rfl⟩ : syracuseStep 1835447 = 2753171) B2753171
theorem B4129217 : Blo 1833618 4129217 := bstep (se 2 (by rfl) ⟨1548456, by rfl⟩ : syracuseStep 4129217 = 3096913) B3096913
theorem B1835467 : Blo 1833618 1835467 := bstep (se 1 (by rfl) ⟨1376600, by rfl⟩ : syracuseStep 1835467 = 2753201) B2753201
theorem B1835479 : Blo 1833618 1835479 := bstep (se 1 (by rfl) ⟨1376609, by rfl⟩ : syracuseStep 1835479 = 2753219) B2753219
theorem B10445273 : Blo 1833618 10445273 := bstep (se 2 (by rfl) ⟨3916977, by rfl⟩ : syracuseStep 10445273 = 7833955) B7833955
theorem B2752985 : Blo 1833618 2752985 := bstep (se 2 (by rfl) ⟨1032369, by rfl⟩ : syracuseStep 2752985 = 2064739) B2064739
theorem B13230553 : Blo 1833618 13230553 := bstep (se 2 (by rfl) ⟨4961457, by rfl⟩ : syracuseStep 13230553 = 9922915) B9922915
theorem B1835499 : Blo 1833618 1835499 := bstep (se 1 (by rfl) ⟨1376624, by rfl⟩ : syracuseStep 1835499 = 2753249) B2753249
theorem B3482099 : Blo 1833618 3482099 := bstep (se 1 (by rfl) ⟨2611574, by rfl⟩ : syracuseStep 3482099 = 5223149) B5223149
theorem B1835511 : Blo 1833618 1835511 := bstep (se 1 (by rfl) ⟨1376633, by rfl⟩ : syracuseStep 1835511 = 2753267) B2753267
theorem B7840259 : Blo 1833618 7840259 := bstep (se 1 (by rfl) ⟨5880194, by rfl⟩ : syracuseStep 7840259 = 11760389) B11760389
theorem B1835531 : Blo 1833618 1835531 := bstep (se 1 (by rfl) ⟨1376648, by rfl⟩ : syracuseStep 1835531 = 2753297) B2753297
theorem B2064919 : Blo 1833618 2064919 := bstep (se 1 (by rfl) ⟨1548689, by rfl⟩ : syracuseStep 2064919 = 3097379) B3097379
theorem B1835543 : Blo 1833618 1835543 := bstep (se 1 (by rfl) ⟨1376657, by rfl⟩ : syracuseStep 1835543 = 2753315) B2753315
theorem B1835563 : Blo 1833618 1835563 := bstep (se 1 (by rfl) ⟨1376672, by rfl⟩ : syracuseStep 1835563 = 2753345) B2753345
theorem B1958455 : Blo 1833618 1958455 := bstep (se 1 (by rfl) ⟨1468841, by rfl⟩ : syracuseStep 1958455 = 2937683) B2937683
theorem B1835575 : Blo 1833618 1835575 := bstep (se 1 (by rfl) ⟨1376681, by rfl⟩ : syracuseStep 1835575 = 2753363) B2753363
theorem B3916363 : Blo 1833618 3916363 := bstep (se 1 (by rfl) ⟨2937272, by rfl⟩ : syracuseStep 3916363 = 5874545) B5874545
theorem B4645451 : Blo 1833618 4645451 := bstep (se 1 (by rfl) ⟨3484088, by rfl⟩ : syracuseStep 4645451 = 6968177) B6968177
theorem B3097163 : Blo 1833618 3097163 := bstep (se 1 (by rfl) ⟨2322872, by rfl⟩ : syracuseStep 3097163 = 4645745) B4645745
theorem B2753099 : Blo 1833618 2753099 := bstep (se 1 (by rfl) ⟨2064824, by rfl⟩ : syracuseStep 2753099 = 4129649) B4129649
theorem B1835595 : Blo 1833618 1835595 := bstep (se 1 (by rfl) ⟨1376696, by rfl⟩ : syracuseStep 1835595 = 2753393) B2753393
theorem B2753111 : Blo 1833618 2753111 := bstep (se 1 (by rfl) ⟨2064833, by rfl⟩ : syracuseStep 2753111 = 4129667) B4129667
theorem B1835607 : Blo 1833618 1835607 := bstep (se 1 (by rfl) ⟨1376705, by rfl⟩ : syracuseStep 1835607 = 2753411) B2753411
theorem B1860203 : Blo 1833618 1860203 := bstep (se 1 (by rfl) ⟨1395152, by rfl⟩ : syracuseStep 1860203 = 2790305) B2790305
theorem B3531379 : Blo 1833618 3531379 := bstep (se 1 (by rfl) ⟨2648534, by rfl⟩ : syracuseStep 3531379 = 5297069) B5297069
theorem B3916439 : Blo 1833618 3916439 := bstep (se 1 (by rfl) ⟨2937329, by rfl⟩ : syracuseStep 3916439 = 5874659) B5874659
theorem B4129433 : Blo 1833618 4129433 := bstep (se 2 (by rfl) ⟨1548537, by rfl⟩ : syracuseStep 4129433 = 3097075) B3097075
theorem B2753177 : Blo 1833618 2753177 := bstep (se 2 (by rfl) ⟨1032441, by rfl⟩ : syracuseStep 2753177 = 2064883) B2064883
theorem B3097291 : Blo 1833618 3097291 := bstep (se 1 (by rfl) ⟨2322968, by rfl⟩ : syracuseStep 3097291 = 4645937) B4645937
theorem B3482327 : Blo 1833618 3482327 := bstep (se 1 (by rfl) ⟨2611745, by rfl⟩ : syracuseStep 3482327 = 5223491) B5223491
theorem B4129523 : Blo 1833618 4129523 := bstep (se 1 (by rfl) ⟨3097142, by rfl⟩ : syracuseStep 4129523 = 6194285) B6194285
theorem B2753291 : Blo 1833618 2753291 := bstep (se 1 (by rfl) ⟨2064968, by rfl⟩ : syracuseStep 2753291 = 4129937) B4129937
theorem B4129559 : Blo 1833618 4129559 := bstep (se 1 (by rfl) ⟨3097169, by rfl⟩ : syracuseStep 4129559 = 6194339) B6194339
theorem B2753303 : Blo 1833618 2753303 := bstep (se 1 (by rfl) ⟨2064977, by rfl⟩ : syracuseStep 2753303 = 4129955) B4129955
theorem B3097433 : Blo 1833618 3097433 := bstep (se 2 (by rfl) ⟨1161537, by rfl⟩ : syracuseStep 3097433 = 2323075) B2323075
theorem B7840601 : Blo 1833618 7840601 := bstep (se 2 (by rfl) ⟨2940225, by rfl⟩ : syracuseStep 7840601 = 5880451) B5880451
theorem B2753369 : Blo 1833618 2753369 := bstep (se 2 (by rfl) ⟨1032513, by rfl⟩ : syracuseStep 2753369 = 2065027) B2065027
theorem B6194123 : Blo 1833618 6194123 := bstep (se 1 (by rfl) ⟨4645592, by rfl⟩ : syracuseStep 6194123 = 9291185) B9291185
theorem B4129739 : Blo 1833618 4129739 := bstep (se 1 (by rfl) ⟨3097304, by rfl⟩ : syracuseStep 4129739 = 6194609) B6194609
theorem B7832537 : Blo 1833618 7832537 := bstep (se 2 (by rfl) ⟨2937201, by rfl⟩ : syracuseStep 7832537 = 5874403) B5874403
theorem B3482585 : Blo 1833618 3482585 := bstep (se 2 (by rfl) ⟨1305969, by rfl⟩ : syracuseStep 3482585 = 2611939) B2611939
theorem B3097561 : Blo 1833618 3097561 := bstep (se 2 (by rfl) ⟨1161585, by rfl⟩ : syracuseStep 3097561 = 2323171) B2323171
theorem B4129793 : Blo 1833618 4129793 := bstep (se 2 (by rfl) ⟨1548672, by rfl⟩ : syracuseStep 4129793 = 3097345) B3097345
theorem B8815661 : Blo 1833618 8815661 := bstep (se 3 (by rfl) ⟨1652936, by rfl⟩ : syracuseStep 8815661 = 3305873) B3305873
theorem B6964289 : Blo 1833618 6964289 := bstep (se 2 (by rfl) ⟨2611608, by rfl⟩ : syracuseStep 6964289 = 5223217) B5223217
theorem B5293259 : Blo 1833618 5293259 := bstep (se 1 (by rfl) ⟨3969944, by rfl⟩ : syracuseStep 5293259 = 7939889) B7939889
theorem B6194393 : Blo 1833618 6194393 := bstep (se 2 (by rfl) ⟨2322897, by rfl⟩ : syracuseStep 6194393 = 4645795) B4645795
theorem B4130009 : Blo 1833618 4130009 := bstep (se 2 (by rfl) ⟨1548753, by rfl⟩ : syracuseStep 4130009 = 3097507) B3097507
theorem B4130099 : Blo 1833618 4130099 := bstep (se 1 (by rfl) ⟨3097574, by rfl⟩ : syracuseStep 4130099 = 6195149) B6195149
theorem B4130135 : Blo 1833618 4130135 := bstep (se 1 (by rfl) ⟨3097601, by rfl⟩ : syracuseStep 4130135 = 6195203) B6195203
theorem B11748701 : Blo 1833618 11748701 := bstep (se 3 (by rfl) ⟨2202881, by rfl⟩ : syracuseStep 11748701 = 4405763) B4405763
theorem B1959275 : Blo 1833618 1959275 := bstep (se 1 (by rfl) ⟨1469456, by rfl⟩ : syracuseStep 1959275 = 2938913) B2938913
theorem B3482995 : Blo 1833618 3482995 := bstep (se 1 (by rfl) ⟨2612246, by rfl⟩ : syracuseStep 3482995 = 5224493) B5224493
theorem B8365457 : Blo 1833618 8365457 := bstep (se 2 (by rfl) ⟨3137046, by rfl⟩ : syracuseStep 8365457 = 6274093) B6274093
theorem B13936049 : Blo 1833618 13936049 := bstep (se 2 (by rfl) ⟨5226018, by rfl⟩ : syracuseStep 13936049 = 10452037) B10452037
theorem B9922009 : Blo 1833618 9922009 := bstep (se 2 (by rfl) ⟨3720753, by rfl⟩ : syracuseStep 9922009 = 7441507) B7441507
theorem B5580353 : Blo 1833618 5580353 := bstep (se 2 (by rfl) ⟨2092632, by rfl⟩ : syracuseStep 5580353 = 4185265) B4185265
theorem B6358859 : Blo 1833618 6358859 := bstep (se 1 (by rfl) ⟨4769144, by rfl⟩ : syracuseStep 6358859 = 9538289) B9538289
theorem B3483481 : Blo 1833618 3483481 := bstep (se 2 (by rfl) ⟨1306305, by rfl⟩ : syracuseStep 3483481 = 2612611) B2612611
theorem B38176613 : Blo 1833618 38176613 := bstep (se 4 (by rfl) ⟨3579057, by rfl⟩ : syracuseStep 38176613 = 7158115) B7158115
theorem B13936535 : Blo 1833618 13936535 := bstep (se 1 (by rfl) ⟨10452401, by rfl⟩ : syracuseStep 13936535 = 20904803) B20904803
theorem B9291671 : Blo 1833618 9291671 := bstep (se 1 (by rfl) ⟨6968753, by rfl⟩ : syracuseStep 9291671 = 13937507) B13937507
theorem B6195095 : Blo 1833618 6195095 := bstep (se 1 (by rfl) ⟨4646321, by rfl⟩ : syracuseStep 6195095 = 9292643) B9292643
theorem B30574513 : Blo 1833618 30574513 := bstep (se 2 (by rfl) ⟨11465442, by rfl⟩ : syracuseStep 30574513 = 22930885) B22930885
theorem B5875735 : Blo 1833618 5875735 := bstep (se 1 (by rfl) ⟨4406801, by rfl⟩ : syracuseStep 5875735 = 8813603) B8813603
theorem B15673409 : Blo 1833618 15673409 := bstep (se 2 (by rfl) ⟨5877528, by rfl⟩ : syracuseStep 15673409 = 11755057) B11755057
theorem B3538561 : Blo 1833618 3538561 := bstep (se 2 (by rfl) ⟨1326960, by rfl⟩ : syracuseStep 3538561 = 2653921) B2653921
theorem B5875915 : Blo 1833618 5875915 := bstep (se 1 (by rfl) ⟨4406936, by rfl⟩ : syracuseStep 5875915 = 8813873) B8813873
theorem B2828503 : Blo 1833618 2828503 := bstep (se 1 (by rfl) ⟨2121377, by rfl⟩ : syracuseStep 2828503 = 4242755) B4242755
theorem B5875991 : Blo 1833618 5875991 := bstep (se 1 (by rfl) ⟨4406993, by rfl⟩ : syracuseStep 5875991 = 8813987) B8813987
theorem B25102709 : Blo 1833618 25102709 := bstep (se 5 (by rfl) ⟨1176689, by rfl⟩ : syracuseStep 25102709 = 2353379) B2353379
theorem B3484043 : Blo 1833618 3484043 := bstep (se 1 (by rfl) ⟨2613032, by rfl⟩ : syracuseStep 3484043 = 5226065) B5226065
theorem B3918233 : Blo 1833618 3918233 := bstep (se 2 (by rfl) ⟨1469337, by rfl⟩ : syracuseStep 3918233 = 2938675) B2938675
theorem B9284057 : Blo 1833618 9284057 := bstep (se 2 (by rfl) ⟨3481521, by rfl⟩ : syracuseStep 9284057 = 6963043) B6963043
theorem B22309337 : Blo 1833618 22309337 := bstep (se 2 (by rfl) ⟨8366001, by rfl⟩ : syracuseStep 22309337 = 16732003) B16732003
theorem B5876185 : Blo 1833618 5876185 := bstep (se 2 (by rfl) ⟨2203569, by rfl⟩ : syracuseStep 5876185 = 4407139) B4407139
theorem B6965777 : Blo 1833618 6965777 := bstep (se 2 (by rfl) ⟨2612166, by rfl⟩ : syracuseStep 6965777 = 5224333) B5224333
theorem B3484225 : Blo 1833618 3484225 := bstep (se 2 (by rfl) ⟨1306584, by rfl⟩ : syracuseStep 3484225 = 2613169) B2613169
theorem B3771073 : Blo 1833618 3771073 := bstep (se 2 (by rfl) ⟨1414152, by rfl⟩ : syracuseStep 3771073 = 2828305) B2828305
theorem B6613721 : Blo 1833618 6613721 := bstep (se 2 (by rfl) ⟨2480145, by rfl⟩ : syracuseStep 6613721 = 4960291) B4960291
theorem B5581619 : Blo 1833618 5581619 := bstep (se 1 (by rfl) ⟨4186214, by rfl⟩ : syracuseStep 5581619 = 8372429) B8372429
theorem B2321227 : Blo 1833618 2321227 := bstep (se 1 (by rfl) ⟨1740920, by rfl⟩ : syracuseStep 2321227 = 3481841) B3481841
theorem B3304409 : Blo 1833618 3304409 := bstep (se 2 (by rfl) ⟨1239153, by rfl⟩ : syracuseStep 3304409 = 2478307) B2478307
theorem B6966233 : Blo 1833618 6966233 := bstep (se 2 (by rfl) ⟨2612337, by rfl⟩ : syracuseStep 6966233 = 5224675) B5224675
theorem B3918899 : Blo 1833618 3918899 := bstep (se 1 (by rfl) ⟨2939174, by rfl⟩ : syracuseStep 3918899 = 5878349) B5878349
theorem B10447937 : Blo 1833618 10447937 := bstep (se 2 (by rfl) ⟨3917976, by rfl⟩ : syracuseStep 10447937 = 7835953) B7835953
theorem B31771723 : Blo 1833618 31771723 := bstep (se 1 (by rfl) ⟨23828792, by rfl⟩ : syracuseStep 31771723 = 47657585) B47657585
theorem B6966445 : Blo 1833618 6966445 := bstep (se 3 (by rfl) ⟨1306208, by rfl⟩ : syracuseStep 6966445 = 2612417) B2612417
theorem B8367425 : Blo 1833618 8367425 := bstep (se 2 (by rfl) ⟨3137784, by rfl⟩ : syracuseStep 8367425 = 6275569) B6275569
theorem B6966749 : Blo 1833618 6966749 := bstep (se 3 (by rfl) ⟨1306265, by rfl⟩ : syracuseStep 6966749 = 2612531) B2612531
theorem B31763981 : Blo 1833618 31763981 := bstep (se 3 (by rfl) ⟨5955746, by rfl⟩ : syracuseStep 31763981 = 11911493) B11911493
theorem B33476113 : Blo 1833618 33476113 := bstep (se 2 (by rfl) ⟨12553542, by rfl⟩ : syracuseStep 33476113 = 25107085) B25107085
theorem B11750957 : Blo 1833618 11750957 := bstep (se 3 (by rfl) ⟨2203304, by rfl⟩ : syracuseStep 11750957 = 4406609) B4406609
theorem B7835201 : Blo 1833618 7835201 := bstep (se 2 (by rfl) ⟨2938200, by rfl⟩ : syracuseStep 7835201 = 5876401) B5876401
theorem B9055819 : Blo 1833618 9055819 := bstep (se 1 (by rfl) ⟨6791864, by rfl⟩ : syracuseStep 9055819 = 13583729) B13583729
theorem B6188723 : Blo 1833618 6188723 := bstep (se 1 (by rfl) ⟨4641542, by rfl⟩ : syracuseStep 6188723 = 9283085) B9283085
theorem B2322199 : Blo 1833618 2322199 := bstep (se 1 (by rfl) ⟨1741649, by rfl⟩ : syracuseStep 2322199 = 3483299) B3483299
theorem B12545857 : Blo 1833618 12545857 := bstep (se 2 (by rfl) ⟨4704696, by rfl⟩ : syracuseStep 12545857 = 9409393) B9409393
theorem B17624897 : Blo 1833618 17624897 := bstep (se 2 (by rfl) ⟨6609336, by rfl⟩ : syracuseStep 17624897 = 13218673) B13218673
theorem B47042369 : Blo 1833618 47042369 := bstep (se 2 (by rfl) ⟨17640888, by rfl⟩ : syracuseStep 47042369 = 35281777) B35281777
theorem B9916235 : Blo 1833618 9916235 := bstep (se 1 (by rfl) ⟨7437176, by rfl⟩ : syracuseStep 9916235 = 14874353) B14874353
theorem B4960075 : Blo 1833618 4960075 := bstep (se 1 (by rfl) ⟨3720056, by rfl⟩ : syracuseStep 4960075 = 7440113) B7440113
theorem B7942033 : Blo 1833618 7942033 := bstep (se 2 (by rfl) ⟨2978262, by rfl⟩ : syracuseStep 7942033 = 5956525) B5956525
theorem B15667121 : Blo 1833618 15667121 := bstep (se 2 (by rfl) ⟨5875170, by rfl⟩ : syracuseStep 15667121 = 11750341) B11750341
theorem B6188993 : Blo 1833618 6188993 := bstep (se 2 (by rfl) ⟨2320872, by rfl⟩ : syracuseStep 6188993 = 4641745) B4641745
theorem B47673305 : Blo 1833618 47673305 := bstep (se 2 (by rfl) ⟨17877489, by rfl⟩ : syracuseStep 47673305 = 35754979) B35754979
theorem B9285677 : Blo 1833618 9285677 := bstep (se 3 (by rfl) ⟨1741064, by rfl⟩ : syracuseStep 9285677 = 3482129) B3482129
theorem B5222465 : Blo 1833618 5222465 := bstep (se 2 (by rfl) ⟨1958424, by rfl⟩ : syracuseStep 5222465 = 3916849) B3916849
theorem B2612503 : Blo 1833618 2612503 := bstep (se 1 (by rfl) ⟨1959377, by rfl⟩ : syracuseStep 2612503 = 3918755) B3918755
theorem B22925747 : Blo 1833618 22925747 := bstep (se 1 (by rfl) ⟨17194310, by rfl⟩ : syracuseStep 22925747 = 34388621) B34388621
theorem B6189533 : Blo 1833618 6189533 := bstep (se 3 (by rfl) ⟨1160537, by rfl⟩ : syracuseStep 6189533 = 2321075) B2321075
theorem B3920395 : Blo 1833618 3920395 := bstep (se 1 (by rfl) ⟨2940296, by rfl⟩ : syracuseStep 3920395 = 5880593) B5880593
theorem B2323019 : Blo 1833618 2323019 := bstep (se 1 (by rfl) ⟨1742264, by rfl⟩ : syracuseStep 2323019 = 3484529) B3484529
theorem B5223001 : Blo 1833618 5223001 := bstep (se 2 (by rfl) ⟨1958625, by rfl⟩ : syracuseStep 5223001 = 3917251) B3917251
theorem B8819351 : Blo 1833618 8819351 := bstep (se 1 (by rfl) ⟨6614513, by rfl⟩ : syracuseStep 8819351 = 13229027) B13229027
theorem B5878451 : Blo 1833618 5878451 := bstep (se 1 (by rfl) ⟨4408838, by rfl⟩ : syracuseStep 5878451 = 8817677) B8817677
theorem B4707251 : Blo 1833618 4707251 := bstep (se 1 (by rfl) ⟨3530438, by rfl⟩ : syracuseStep 4707251 = 7060877) B7060877
theorem B14881715 : Blo 1833618 14881715 := bstep (se 1 (by rfl) ⟨11161286, by rfl⟩ : syracuseStep 14881715 = 22322573) B22322573
theorem B4125707 : Blo 1833618 4125707 := bstep (se 1 (by rfl) ⟨3094280, by rfl⟩ : syracuseStep 4125707 = 6188561) B6188561
theorem B7836689 : Blo 1833618 7836689 := bstep (se 2 (by rfl) ⟨2938758, by rfl⟩ : syracuseStep 7836689 = 5877517) B5877517
theorem B4125761 : Blo 1833618 4125761 := bstep (se 2 (by rfl) ⟨1547160, by rfl⟩ : syracuseStep 4125761 = 3094321) B3094321
theorem B4641857 : Blo 1833618 4641857 := bstep (se 2 (by rfl) ⟨1740696, by rfl⟩ : syracuseStep 4641857 = 3481393) B3481393
theorem B59479109 : Blo 1833618 59479109 := bstep (se 4 (by rfl) ⟨5576166, by rfl⟩ : syracuseStep 59479109 = 11152333) B11152333
theorem B8934475 : Blo 1833618 8934475 := bstep (se 1 (by rfl) ⟨6700856, by rfl⟩ : syracuseStep 8934475 = 13401713) B13401713
theorem B2790553 : Blo 1833618 2790553 := bstep (se 2 (by rfl) ⟨1046457, by rfl⟩ : syracuseStep 2790553 = 2092915) B2092915
theorem B3306739 : Blo 1833618 3306739 := bstep (se 1 (by rfl) ⟨2480054, by rfl⟩ : syracuseStep 3306739 = 4960109) B4960109
theorem B4125977 : Blo 1833618 4125977 := bstep (se 2 (by rfl) ⟨1547241, by rfl⟩ : syracuseStep 4125977 = 3094483) B3094483
theorem B4126067 : Blo 1833618 4126067 := bstep (se 1 (by rfl) ⟨3094550, by rfl⟩ : syracuseStep 4126067 = 6189101) B6189101
theorem B4126103 : Blo 1833618 4126103 := bstep (se 1 (by rfl) ⟨3094577, by rfl⟩ : syracuseStep 4126103 = 6189155) B6189155
theorem B20903345 : Blo 1833618 20903345 := bstep (se 2 (by rfl) ⟨7838754, by rfl⟩ : syracuseStep 20903345 = 15677509) B15677509
theorem B4126283 : Blo 1833618 4126283 := bstep (se 1 (by rfl) ⟨3094712, by rfl⟩ : syracuseStep 4126283 = 6189425) B6189425
theorem B6190667 : Blo 1833618 6190667 := bstep (se 1 (by rfl) ⟨4643000, by rfl⟩ : syracuseStep 6190667 = 9286001) B9286001
theorem B2479691 : Blo 1833618 2479691 := bstep (se 1 (by rfl) ⟨1859768, by rfl⟩ : syracuseStep 2479691 = 3719537) B3719537
theorem B4642393 : Blo 1833618 4642393 := bstep (se 2 (by rfl) ⟨1740897, by rfl⟩ : syracuseStep 4642393 = 3481795) B3481795
theorem B2938457 : Blo 1833618 2938457 := bstep (se 2 (by rfl) ⟨1101921, by rfl⟩ : syracuseStep 2938457 = 2203843) B2203843
theorem B4126337 : Blo 1833618 4126337 := bstep (se 2 (by rfl) ⟨1547376, by rfl⟩ : syracuseStep 4126337 = 3094753) B3094753
theorem B4126553 : Blo 1833618 4126553 := bstep (se 2 (by rfl) ⟨1547457, by rfl⟩ : syracuseStep 4126553 = 3094915) B3094915
theorem B6190937 : Blo 1833618 6190937 := bstep (se 2 (by rfl) ⟨2321601, by rfl⟩ : syracuseStep 6190937 = 4643203) B4643203
theorem B59488177 : Blo 1833618 59488177 := bstep (se 2 (by rfl) ⟨22308066, by rfl⟩ : syracuseStep 59488177 = 44616133) B44616133
theorem B4126643 : Blo 1833618 4126643 := bstep (se 1 (by rfl) ⟨3094982, by rfl⟩ : syracuseStep 4126643 = 6189965) B6189965
theorem B4126679 : Blo 1833618 4126679 := bstep (se 1 (by rfl) ⟨3095009, by rfl⟩ : syracuseStep 4126679 = 6190019) B6190019
theorem B7837661 : Blo 1833618 7837661 := bstep (se 3 (by rfl) ⟨1469561, by rfl⟩ : syracuseStep 7837661 = 2939123) B2939123
theorem B6969347 : Blo 1833618 6969347 := bstep (se 1 (by rfl) ⟨5227010, by rfl⟩ : syracuseStep 6969347 = 10454021) B10454021
theorem B6969361 : Blo 1833618 6969361 := bstep (se 2 (by rfl) ⟨2613510, by rfl⟩ : syracuseStep 6969361 = 5227021) B5227021
theorem B2750489 : Blo 1833618 2750489 := bstep (se 2 (by rfl) ⟨1031433, by rfl⟩ : syracuseStep 2750489 = 2062867) B2062867
theorem B4241497 : Blo 1833618 4241497 := bstep (se 2 (by rfl) ⟨1590561, by rfl⟩ : syracuseStep 4241497 = 3181123) B3181123
theorem B2750603 : Blo 1833618 2750603 := bstep (se 1 (by rfl) ⟨2062952, by rfl⟩ : syracuseStep 2750603 = 4125905) B4125905
theorem B4126859 : Blo 1833618 4126859 := bstep (se 1 (by rfl) ⟨3095144, by rfl⟩ : syracuseStep 4126859 = 6190289) B6190289
theorem B2750615 : Blo 1833618 2750615 := bstep (se 1 (by rfl) ⟨2062961, by rfl⟩ : syracuseStep 2750615 = 4125923) B4125923
theorem B3094679 : Blo 1833618 3094679 := bstep (se 1 (by rfl) ⟨2321009, by rfl⟩ : syracuseStep 3094679 = 4642019) B4642019
theorem B4126913 : Blo 1833618 4126913 := bstep (se 2 (by rfl) ⟨1547592, by rfl⟩ : syracuseStep 4126913 = 3095185) B3095185
theorem B2750681 : Blo 1833618 2750681 := bstep (se 2 (by rfl) ⟨1031505, by rfl⟩ : syracuseStep 2750681 = 2063011) B2063011
theorem B3094807 : Blo 1833618 3094807 := bstep (se 1 (by rfl) ⟨2321105, by rfl⟩ : syracuseStep 3094807 = 4642211) B4642211
theorem B2750795 : Blo 1833618 2750795 := bstep (se 1 (by rfl) ⟨2063096, by rfl⟩ : syracuseStep 2750795 = 4126193) B4126193
theorem B6363467 : Blo 1833618 6363467 := bstep (se 1 (by rfl) ⟨4772600, by rfl⟩ : syracuseStep 6363467 = 9545201) B9545201
theorem B2750807 : Blo 1833618 2750807 := bstep (se 1 (by rfl) ⟨2063105, by rfl⟩ : syracuseStep 2750807 = 4126211) B4126211
theorem B2750873 : Blo 1833618 2750873 := bstep (se 2 (by rfl) ⟨1031577, by rfl⟩ : syracuseStep 2750873 = 2063155) B2063155
theorem B4127129 : Blo 1833618 4127129 := bstep (se 2 (by rfl) ⟨1547673, by rfl⟩ : syracuseStep 4127129 = 3095347) B3095347
theorem B5224925 : Blo 1833618 5224925 := bstep (se 3 (by rfl) ⟨979673, by rfl⟩ : syracuseStep 5224925 = 1959347) B1959347
theorem B4127219 : Blo 1833618 4127219 := bstep (se 1 (by rfl) ⟨3095414, by rfl⟩ : syracuseStep 4127219 = 6190829) B6190829
theorem B2750987 : Blo 1833618 2750987 := bstep (se 1 (by rfl) ⟨2063240, by rfl⟩ : syracuseStep 2750987 = 4126481) B4126481
theorem B17627665 : Blo 1833618 17627665 := bstep (se 2 (by rfl) ⟨6610374, by rfl⟩ : syracuseStep 17627665 = 13220749) B13220749
theorem B2750999 : Blo 1833618 2750999 := bstep (se 1 (by rfl) ⟨2063249, by rfl⟩ : syracuseStep 2750999 = 4126499) B4126499
theorem B4127255 : Blo 1833618 4127255 := bstep (se 1 (by rfl) ⟨3095441, by rfl⟩ : syracuseStep 4127255 = 6190883) B6190883
theorem B6191639 : Blo 1833618 6191639 := bstep (se 1 (by rfl) ⟨4643729, by rfl⟩ : syracuseStep 6191639 = 9287459) B9287459
theorem B2062903 : Blo 1833618 2062903 := bstep (se 1 (by rfl) ⟨1547177, by rfl⟩ : syracuseStep 2062903 = 3094355) B3094355
theorem B2751065 : Blo 1833618 2751065 := bstep (se 2 (by rfl) ⟨1031649, by rfl⟩ : syracuseStep 2751065 = 2063299) B2063299
theorem B1833623 : Blo 1833618 1833623 := bstep (se 1 (by rfl) ⟨1375217, by rfl⟩ : syracuseStep 1833623 = 2750435) B2750435
theorem B2611865 : Blo 1833618 2611865 := bstep (se 2 (by rfl) ⟨979449, by rfl⟩ : syracuseStep 2611865 = 1958899) B1958899
theorem B1833643 : Blo 1833618 1833643 := bstep (se 1 (by rfl) ⟨1375232, by rfl⟩ : syracuseStep 1833643 = 2750465) B2750465
theorem B1833655 : Blo 1833618 1833655 := bstep (se 1 (by rfl) ⟨1375241, by rfl⟩ : syracuseStep 1833655 = 2750483) B2750483
theorem B4643507 : Blo 1833618 4643507 := bstep (se 1 (by rfl) ⟨3482630, by rfl⟩ : syracuseStep 4643507 = 6965261) B6965261
theorem B1833675 : Blo 1833618 1833675 := bstep (se 1 (by rfl) ⟨1375256, by rfl⟩ : syracuseStep 1833675 = 2750513) B2750513
theorem B2751179 : Blo 1833618 2751179 := bstep (se 1 (by rfl) ⟨2063384, by rfl⟩ : syracuseStep 2751179 = 4126769) B4126769
theorem B4127435 : Blo 1833618 4127435 := bstep (se 1 (by rfl) ⟨3095576, by rfl⟩ : syracuseStep 4127435 = 6191153) B6191153
theorem B1833687 : Blo 1833618 1833687 := bstep (se 1 (by rfl) ⟨1375265, by rfl⟩ : syracuseStep 1833687 = 2750531) B2750531
theorem B2751191 : Blo 1833618 2751191 := bstep (se 1 (by rfl) ⟨2063393, by rfl⟩ : syracuseStep 2751191 = 4126787) B4126787
theorem B1833707 : Blo 1833618 1833707 := bstep (se 1 (by rfl) ⟨1375280, by rfl⟩ : syracuseStep 1833707 = 2750561) B2750561
theorem B2063083 : Blo 1833618 2063083 := bstep (se 1 (by rfl) ⟨1547312, by rfl⟩ : syracuseStep 2063083 = 3094625) B3094625
theorem B1833719 : Blo 1833618 1833719 := bstep (se 1 (by rfl) ⟨1375289, by rfl⟩ : syracuseStep 1833719 = 2750579) B2750579
theorem B4127489 : Blo 1833618 4127489 := bstep (se 2 (by rfl) ⟨1547808, by rfl⟩ : syracuseStep 4127489 = 3095617) B3095617
theorem B1833739 : Blo 1833618 1833739 := bstep (se 1 (by rfl) ⟨1375304, by rfl⟩ : syracuseStep 1833739 = 2750609) B2750609
theorem B1833751 : Blo 1833618 1833751 := bstep (se 1 (by rfl) ⟨1375313, by rfl⟩ : syracuseStep 1833751 = 2750627) B2750627
theorem B2751257 : Blo 1833618 2751257 := bstep (se 2 (by rfl) ⟨1031721, by rfl⟩ : syracuseStep 2751257 = 2063443) B2063443
theorem B1833771 : Blo 1833618 1833771 := bstep (se 1 (by rfl) ⟨1375328, by rfl⟩ : syracuseStep 1833771 = 2750657) B2750657
theorem B1833783 : Blo 1833618 1833783 := bstep (se 1 (by rfl) ⟨1375337, by rfl⟩ : syracuseStep 1833783 = 2750675) B2750675
theorem B1833803 : Blo 1833618 1833803 := bstep (se 1 (by rfl) ⟨1375352, by rfl⟩ : syracuseStep 1833803 = 2750705) B2750705
theorem B1833815 : Blo 1833618 1833815 := bstep (se 1 (by rfl) ⟨1375361, by rfl⟩ : syracuseStep 1833815 = 2750723) B2750723
theorem B2063191 : Blo 1833618 2063191 := bstep (se 1 (by rfl) ⟨1547393, by rfl⟩ : syracuseStep 2063191 = 3094787) B3094787
theorem B11754341 : Blo 1833618 11754341 := bstep (se 4 (by rfl) ⟨1101969, by rfl⟩ : syracuseStep 11754341 = 2203939) B2203939
theorem B1833835 : Blo 1833618 1833835 := bstep (se 1 (by rfl) ⟨1375376, by rfl⟩ : syracuseStep 1833835 = 2750753) B2750753
theorem B1833847 : Blo 1833618 1833847 := bstep (se 1 (by rfl) ⟨1375385, by rfl⟩ : syracuseStep 1833847 = 2750771) B2750771
theorem B1833867 : Blo 1833618 1833867 := bstep (se 1 (by rfl) ⟨1375400, by rfl⟩ : syracuseStep 1833867 = 2750801) B2750801
theorem B2751371 : Blo 1833618 2751371 := bstep (se 1 (by rfl) ⟨2063528, by rfl⟩ : syracuseStep 2751371 = 4127057) B4127057
theorem B3095435 : Blo 1833618 3095435 := bstep (se 1 (by rfl) ⟨2321576, by rfl⟩ : syracuseStep 3095435 = 4643153) B4643153
theorem B6962071 : Blo 1833618 6962071 := bstep (se 1 (by rfl) ⟨5221553, by rfl⟩ : syracuseStep 6962071 = 10443107) B10443107
theorem B4406167 : Blo 1833618 4406167 := bstep (se 1 (by rfl) ⟨3304625, by rfl⟩ : syracuseStep 4406167 = 6609251) B6609251
theorem B1833879 : Blo 1833618 1833879 := bstep (se 1 (by rfl) ⟨1375409, by rfl⟩ : syracuseStep 1833879 = 2750819) B2750819
theorem B2751383 : Blo 1833618 2751383 := bstep (se 1 (by rfl) ⟨2063537, by rfl⟩ : syracuseStep 2751383 = 4127075) B4127075
theorem B1833899 : Blo 1833618 1833899 := bstep (se 1 (by rfl) ⟨1375424, by rfl⟩ : syracuseStep 1833899 = 2750849) B2750849
theorem B1833911 : Blo 1833618 1833911 := bstep (se 1 (by rfl) ⟨1375433, by rfl⟩ : syracuseStep 1833911 = 2750867) B2750867
theorem B1833931 : Blo 1833618 1833931 := bstep (se 1 (by rfl) ⟨1375448, by rfl⟩ : syracuseStep 1833931 = 2750897) B2750897
theorem B1833943 : Blo 1833618 1833943 := bstep (se 1 (by rfl) ⟨1375457, by rfl⟩ : syracuseStep 1833943 = 2750915) B2750915
theorem B2751449 : Blo 1833618 2751449 := bstep (se 2 (by rfl) ⟨1031793, by rfl⟩ : syracuseStep 2751449 = 2063587) B2063587
theorem B4127705 : Blo 1833618 4127705 := bstep (se 2 (by rfl) ⟨1547889, by rfl⟩ : syracuseStep 4127705 = 3095779) B3095779
theorem B4643801 : Blo 1833618 4643801 := bstep (se 2 (by rfl) ⟨1741425, by rfl⟩ : syracuseStep 4643801 = 3482851) B3482851
theorem B1833963 : Blo 1833618 1833963 := bstep (se 1 (by rfl) ⟨1375472, by rfl⟩ : syracuseStep 1833963 = 2750945) B2750945
theorem B1833975 : Blo 1833618 1833975 := bstep (se 1 (by rfl) ⟨1375481, by rfl⟩ : syracuseStep 1833975 = 2750963) B2750963
theorem B1833995 : Blo 1833618 1833995 := bstep (se 1 (by rfl) ⟨1375496, by rfl⟩ : syracuseStep 1833995 = 2750993) B2750993
theorem B2063371 : Blo 1833618 2063371 := bstep (se 1 (by rfl) ⟨1547528, by rfl⟩ : syracuseStep 2063371 = 3095057) B3095057
theorem B3095563 : Blo 1833618 3095563 := bstep (se 1 (by rfl) ⟨2321672, by rfl⟩ : syracuseStep 3095563 = 4643345) B4643345
theorem B1834007 : Blo 1833618 1834007 := bstep (se 1 (by rfl) ⟨1375505, by rfl⟩ : syracuseStep 1834007 = 2751011) B2751011
theorem B1834027 : Blo 1833618 1834027 := bstep (se 1 (by rfl) ⟨1375520, by rfl⟩ : syracuseStep 1834027 = 2751041) B2751041
theorem B4127795 : Blo 1833618 4127795 := bstep (se 1 (by rfl) ⟨3095846, by rfl⟩ : syracuseStep 4127795 = 6191693) B6191693
theorem B6192179 : Blo 1833618 6192179 := bstep (se 1 (by rfl) ⟨4644134, by rfl⟩ : syracuseStep 6192179 = 9288269) B9288269
theorem B1834039 : Blo 1833618 1834039 := bstep (se 1 (by rfl) ⟨1375529, by rfl⟩ : syracuseStep 1834039 = 2751059) B2751059
theorem B66944069 : Blo 1833618 66944069 := bstep (se 4 (by rfl) ⟨6276006, by rfl⟩ : syracuseStep 66944069 = 12552013) B12552013
theorem B1834059 : Blo 1833618 1834059 := bstep (se 1 (by rfl) ⟨1375544, by rfl⟩ : syracuseStep 1834059 = 2751089) B2751089
theorem B2751563 : Blo 1833618 2751563 := bstep (se 1 (by rfl) ⟨2063672, by rfl⟩ : syracuseStep 2751563 = 4127345) B4127345
theorem B1834071 : Blo 1833618 1834071 := bstep (se 1 (by rfl) ⟨1375553, by rfl⟩ : syracuseStep 1834071 = 2751107) B2751107
theorem B2751575 : Blo 1833618 2751575 := bstep (se 1 (by rfl) ⟨2063681, by rfl⟩ : syracuseStep 2751575 = 4127363) B4127363
theorem B4127831 : Blo 1833618 4127831 := bstep (se 1 (by rfl) ⟨3095873, by rfl⟩ : syracuseStep 4127831 = 6191747) B6191747
theorem B1834091 : Blo 1833618 1834091 := bstep (se 1 (by rfl) ⟨1375568, by rfl⟩ : syracuseStep 1834091 = 2751137) B2751137
theorem B1834103 : Blo 1833618 1834103 := bstep (se 1 (by rfl) ⟨1375577, by rfl⟩ : syracuseStep 1834103 = 2751155) B2751155
theorem B2063479 : Blo 1833618 2063479 := bstep (se 1 (by rfl) ⟨1547609, by rfl⟩ : syracuseStep 2063479 = 3095219) B3095219
theorem B1834123 : Blo 1833618 1834123 := bstep (se 1 (by rfl) ⟨1375592, by rfl⟩ : syracuseStep 1834123 = 2751185) B2751185
theorem B1834135 : Blo 1833618 1834135 := bstep (se 1 (by rfl) ⟨1375601, by rfl⟩ : syracuseStep 1834135 = 2751203) B2751203
theorem B2751641 : Blo 1833618 2751641 := bstep (se 2 (by rfl) ⟨1031865, by rfl⟩ : syracuseStep 2751641 = 2063731) B2063731
theorem B3095705 : Blo 1833618 3095705 := bstep (se 2 (by rfl) ⟨1160889, by rfl⟩ : syracuseStep 3095705 = 2321779) B2321779
theorem B1834155 : Blo 1833618 1834155 := bstep (se 1 (by rfl) ⟨1375616, by rfl⟩ : syracuseStep 1834155 = 2751233) B2751233
theorem B1834167 : Blo 1833618 1834167 := bstep (se 1 (by rfl) ⟨1375625, by rfl⟩ : syracuseStep 1834167 = 2751251) B2751251
theorem B1834187 : Blo 1833618 1834187 := bstep (se 1 (by rfl) ⟨1375640, by rfl⟩ : syracuseStep 1834187 = 2751281) B2751281
theorem B1858775 : Blo 1833618 1858775 := bstep (se 1 (by rfl) ⟨1394081, by rfl⟩ : syracuseStep 1858775 = 2788163) B2788163
theorem B1834199 : Blo 1833618 1834199 := bstep (se 1 (by rfl) ⟨1375649, by rfl⟩ : syracuseStep 1834199 = 2751299) B2751299
theorem B1834219 : Blo 1833618 1834219 := bstep (se 1 (by rfl) ⟨1375664, by rfl⟩ : syracuseStep 1834219 = 2751329) B2751329
theorem B1834231 : Blo 1833618 1834231 := bstep (se 1 (by rfl) ⟨1375673, by rfl⟩ : syracuseStep 1834231 = 2751347) B2751347
theorem B1834251 : Blo 1833618 1834251 := bstep (se 1 (by rfl) ⟨1375688, by rfl⟩ : syracuseStep 1834251 = 2751377) B2751377
theorem B2751755 : Blo 1833618 2751755 := bstep (se 1 (by rfl) ⟨2063816, by rfl⟩ : syracuseStep 2751755 = 4127633) B4127633
theorem B4128011 : Blo 1833618 4128011 := bstep (se 1 (by rfl) ⟨3096008, by rfl⟩ : syracuseStep 4128011 = 6192017) B6192017
theorem B1834263 : Blo 1833618 1834263 := bstep (se 1 (by rfl) ⟨1375697, by rfl⟩ : syracuseStep 1834263 = 2751395) B2751395
theorem B2751767 : Blo 1833618 2751767 := bstep (se 1 (by rfl) ⟨2063825, by rfl⟩ : syracuseStep 2751767 = 4127651) B4127651
theorem B3095833 : Blo 1833618 3095833 := bstep (se 2 (by rfl) ⟨1160937, by rfl⟩ : syracuseStep 3095833 = 2321875) B2321875
theorem B1834283 : Blo 1833618 1834283 := bstep (se 1 (by rfl) ⟨1375712, by rfl⟩ : syracuseStep 1834283 = 2751425) B2751425
theorem B2063659 : Blo 1833618 2063659 := bstep (se 1 (by rfl) ⟨1547744, by rfl⟩ : syracuseStep 2063659 = 3095489) B3095489
theorem B1834295 : Blo 1833618 1834295 := bstep (se 1 (by rfl) ⟨1375721, by rfl⟩ : syracuseStep 1834295 = 2751443) B2751443
theorem B4128065 : Blo 1833618 4128065 := bstep (se 2 (by rfl) ⟨1548024, by rfl⟩ : syracuseStep 4128065 = 3096049) B3096049
theorem B6192449 : Blo 1833618 6192449 := bstep (se 2 (by rfl) ⟨2322168, by rfl⟩ : syracuseStep 6192449 = 4644337) B4644337
theorem B1834315 : Blo 1833618 1834315 := bstep (se 1 (by rfl) ⟨1375736, by rfl⟩ : syracuseStep 1834315 = 2751473) B2751473
theorem B1834327 : Blo 1833618 1834327 := bstep (se 1 (by rfl) ⟨1375745, by rfl⟩ : syracuseStep 1834327 = 2751491) B2751491
theorem B2751833 : Blo 1833618 2751833 := bstep (se 2 (by rfl) ⟨1031937, by rfl⟩ : syracuseStep 2751833 = 2063875) B2063875
theorem B1834347 : Blo 1833618 1834347 := bstep (se 1 (by rfl) ⟨1375760, by rfl⟩ : syracuseStep 1834347 = 2751521) B2751521
theorem B1834359 : Blo 1833618 1834359 := bstep (se 1 (by rfl) ⟨1375769, by rfl⟩ : syracuseStep 1834359 = 2751539) B2751539
theorem B1834379 : Blo 1833618 1834379 := bstep (se 1 (by rfl) ⟨1375784, by rfl⟩ : syracuseStep 1834379 = 2751569) B2751569
theorem B1834391 : Blo 1833618 1834391 := bstep (se 1 (by rfl) ⟨1375793, by rfl⟩ : syracuseStep 1834391 = 2751587) B2751587
theorem B2063767 : Blo 1833618 2063767 := bstep (se 1 (by rfl) ⟨1547825, by rfl⟩ : syracuseStep 2063767 = 3095651) B3095651
theorem B1834411 : Blo 1833618 1834411 := bstep (se 1 (by rfl) ⟨1375808, by rfl⟩ : syracuseStep 1834411 = 2751617) B2751617
theorem B1834423 : Blo 1833618 1834423 := bstep (se 1 (by rfl) ⟨1375817, by rfl⟩ : syracuseStep 1834423 = 2751635) B2751635
theorem B1834443 : Blo 1833618 1834443 := bstep (se 1 (by rfl) ⟨1375832, by rfl⟩ : syracuseStep 1834443 = 2751665) B2751665
theorem B2751947 : Blo 1833618 2751947 := bstep (se 1 (by rfl) ⟨2063960, by rfl⟩ : syracuseStep 2751947 = 4127921) B4127921
theorem B1834455 : Blo 1833618 1834455 := bstep (se 1 (by rfl) ⟨1375841, by rfl⟩ : syracuseStep 1834455 = 2751683) B2751683
theorem B15670745 : Blo 1833618 15670745 := bstep (se 2 (by rfl) ⟨5876529, by rfl⟩ : syracuseStep 15670745 = 11753059) B11753059
theorem B2751959 : Blo 1833618 2751959 := bstep (se 1 (by rfl) ⟨2063969, by rfl⟩ : syracuseStep 2751959 = 4127939) B4127939
theorem B1834475 : Blo 1833618 1834475 := bstep (se 1 (by rfl) ⟨1375856, by rfl⟩ : syracuseStep 1834475 = 2751713) B2751713
theorem B1834487 : Blo 1833618 1834487 := bstep (se 1 (by rfl) ⟨1375865, by rfl⟩ : syracuseStep 1834487 = 2751731) B2751731
theorem B1834507 : Blo 1833618 1834507 := bstep (se 1 (by rfl) ⟨1375880, by rfl⟩ : syracuseStep 1834507 = 2751761) B2751761
theorem B4185611 : Blo 1833618 4185611 := bstep (se 1 (by rfl) ⟨3139208, by rfl⟩ : syracuseStep 4185611 = 6278417) B6278417
theorem B1834519 : Blo 1833618 1834519 := bstep (se 1 (by rfl) ⟨1375889, by rfl⟩ : syracuseStep 1834519 = 2751779) B2751779
theorem B2752025 : Blo 1833618 2752025 := bstep (se 2 (by rfl) ⟨1032009, by rfl⟩ : syracuseStep 2752025 = 2064019) B2064019
theorem B4128281 : Blo 1833618 4128281 := bstep (se 2 (by rfl) ⟨1548105, by rfl⟩ : syracuseStep 4128281 = 3096211) B3096211
theorem B1834539 : Blo 1833618 1834539 := bstep (se 1 (by rfl) ⟨1375904, by rfl⟩ : syracuseStep 1834539 = 2751809) B2751809
theorem B1834551 : Blo 1833618 1834551 := bstep (se 1 (by rfl) ⟨1375913, by rfl⟩ : syracuseStep 1834551 = 2751827) B2751827
theorem B1834571 : Blo 1833618 1834571 := bstep (se 1 (by rfl) ⟨1375928, by rfl⟩ : syracuseStep 1834571 = 2751857) B2751857
theorem B2063947 : Blo 1833618 2063947 := bstep (se 1 (by rfl) ⟨1547960, by rfl⟩ : syracuseStep 2063947 = 3095921) B3095921
theorem B1834583 : Blo 1833618 1834583 := bstep (se 1 (by rfl) ⟨1375937, by rfl⟩ : syracuseStep 1834583 = 2751875) B2751875
theorem B1834603 : Blo 1833618 1834603 := bstep (se 1 (by rfl) ⟨1375952, by rfl⟩ : syracuseStep 1834603 = 2751905) B2751905
theorem B4128371 : Blo 1833618 4128371 := bstep (se 1 (by rfl) ⟨3096278, by rfl⟩ : syracuseStep 4128371 = 6192557) B6192557
theorem B1834615 : Blo 1833618 1834615 := bstep (se 1 (by rfl) ⟨1375961, by rfl⟩ : syracuseStep 1834615 = 2751923) B2751923
theorem B7061123 : Blo 1833618 7061123 := bstep (se 1 (by rfl) ⟨5295842, by rfl⟩ : syracuseStep 7061123 = 10591685) B10591685
theorem B1834635 : Blo 1833618 1834635 := bstep (se 1 (by rfl) ⟨1375976, by rfl⟩ : syracuseStep 1834635 = 2751953) B2751953
theorem B2752139 : Blo 1833618 2752139 := bstep (se 1 (by rfl) ⟨2064104, by rfl⟩ : syracuseStep 2752139 = 4128209) B4128209
theorem B1834647 : Blo 1833618 1834647 := bstep (se 1 (by rfl) ⟨1375985, by rfl⟩ : syracuseStep 1834647 = 2751971) B2751971
theorem B2752151 : Blo 1833618 2752151 := bstep (se 1 (by rfl) ⟨2064113, by rfl⟩ : syracuseStep 2752151 = 4128227) B4128227
theorem B4128407 : Blo 1833618 4128407 := bstep (se 1 (by rfl) ⟨3096305, by rfl⟩ : syracuseStep 4128407 = 6192611) B6192611
theorem B1834667 : Blo 1833618 1834667 := bstep (se 1 (by rfl) ⟨1376000, by rfl⟩ : syracuseStep 1834667 = 2752001) B2752001
theorem B6962861 : Blo 1833618 6962861 := bstep (se 3 (by rfl) ⟨1305536, by rfl⟩ : syracuseStep 6962861 = 2611073) B2611073
theorem B1834679 : Blo 1833618 1834679 := bstep (se 1 (by rfl) ⟨1376009, by rfl⟩ : syracuseStep 1834679 = 2752019) B2752019
theorem B2064055 : Blo 1833618 2064055 := bstep (se 1 (by rfl) ⟨1548041, by rfl⟩ : syracuseStep 2064055 = 3096083) B3096083
theorem B1834699 : Blo 1833618 1834699 := bstep (se 1 (by rfl) ⟨1376024, by rfl⟩ : syracuseStep 1834699 = 2752049) B2752049
theorem B1834711 : Blo 1833618 1834711 := bstep (se 1 (by rfl) ⟨1376033, by rfl⟩ : syracuseStep 1834711 = 2752067) B2752067
theorem B2752217 : Blo 1833618 2752217 := bstep (se 2 (by rfl) ⟨1032081, by rfl⟩ : syracuseStep 2752217 = 2064163) B2064163
theorem B1834731 : Blo 1833618 1834731 := bstep (se 1 (by rfl) ⟨1376048, by rfl⟩ : syracuseStep 1834731 = 2752097) B2752097
theorem B1834743 : Blo 1833618 1834743 := bstep (se 1 (by rfl) ⟨1376057, by rfl⟩ : syracuseStep 1834743 = 2752115) B2752115
theorem B3481355 : Blo 1833618 3481355 := bstep (se 1 (by rfl) ⟨2611016, by rfl⟩ : syracuseStep 3481355 = 5222033) B5222033
theorem B1834763 : Blo 1833618 1834763 := bstep (se 1 (by rfl) ⟨1376072, by rfl⟩ : syracuseStep 1834763 = 2752145) B2752145
theorem B1834775 : Blo 1833618 1834775 := bstep (se 1 (by rfl) ⟨1376081, by rfl⟩ : syracuseStep 1834775 = 2752163) B2752163
theorem B1834795 : Blo 1833618 1834795 := bstep (se 1 (by rfl) ⟨1376096, by rfl⟩ : syracuseStep 1834795 = 2752193) B2752193
theorem B1834807 : Blo 1833618 1834807 := bstep (se 1 (by rfl) ⟨1376105, by rfl⟩ : syracuseStep 1834807 = 2752211) B2752211
theorem B1834827 : Blo 1833618 1834827 := bstep (se 1 (by rfl) ⟨1376120, by rfl⟩ : syracuseStep 1834827 = 2752241) B2752241
theorem B2752331 : Blo 1833618 2752331 := bstep (se 1 (by rfl) ⟨2064248, by rfl⟩ : syracuseStep 2752331 = 4128497) B4128497
theorem B4128587 : Blo 1833618 4128587 := bstep (se 1 (by rfl) ⟨3096440, by rfl⟩ : syracuseStep 4128587 = 6192881) B6192881
theorem B1834839 : Blo 1833618 1834839 := bstep (se 1 (by rfl) ⟨1376129, by rfl⟩ : syracuseStep 1834839 = 2752259) B2752259
theorem B2752343 : Blo 1833618 2752343 := bstep (se 1 (by rfl) ⟨2064257, by rfl⟩ : syracuseStep 2752343 = 4128515) B4128515
theorem B3096407 : Blo 1833618 3096407 := bstep (se 1 (by rfl) ⟨2322305, by rfl⟩ : syracuseStep 3096407 = 4644611) B4644611
theorem B6192989 : Blo 1833618 6192989 := bstep (se 3 (by rfl) ⟨1161185, by rfl⟩ : syracuseStep 6192989 = 2322371) B2322371
theorem B9289565 : Blo 1833618 9289565 := bstep (se 3 (by rfl) ⟨1741793, by rfl⟩ : syracuseStep 9289565 = 3483587) B3483587
theorem B18825061 : Blo 1833618 18825061 := bstep (se 4 (by rfl) ⟨1764849, by rfl⟩ : syracuseStep 18825061 = 3529699) B3529699
theorem B1834859 : Blo 1833618 1834859 := bstep (se 1 (by rfl) ⟨1376144, by rfl⟩ : syracuseStep 1834859 = 2752289) B2752289
theorem B2064235 : Blo 1833618 2064235 := bstep (se 1 (by rfl) ⟨1548176, by rfl⟩ : syracuseStep 2064235 = 3096353) B3096353
theorem B1834871 : Blo 1833618 1834871 := bstep (se 1 (by rfl) ⟨1376153, by rfl⟩ : syracuseStep 1834871 = 2752307) B2752307
theorem B4128641 : Blo 1833618 4128641 := bstep (se 2 (by rfl) ⟨1548240, by rfl⟩ : syracuseStep 4128641 = 3096481) B3096481
theorem B9920387 : Blo 1833618 9920387 := bstep (se 1 (by rfl) ⟨7440290, by rfl⟩ : syracuseStep 9920387 = 14880581) B14880581
theorem B1834891 : Blo 1833618 1834891 := bstep (se 1 (by rfl) ⟨1376168, by rfl⟩ : syracuseStep 1834891 = 2752337) B2752337
theorem B1834903 : Blo 1833618 1834903 := bstep (se 1 (by rfl) ⟨1376177, by rfl⟩ : syracuseStep 1834903 = 2752355) B2752355
theorem B9920407 : Blo 1833618 9920407 := bstep (se 1 (by rfl) ⟨7440305, by rfl⟩ : syracuseStep 9920407 = 14880611) B14880611
theorem B2752409 : Blo 1833618 2752409 := bstep (se 2 (by rfl) ⟨1032153, by rfl⟩ : syracuseStep 2752409 = 2064307) B2064307
theorem B1834923 : Blo 1833618 1834923 := bstep (se 1 (by rfl) ⟨1376192, by rfl⟩ : syracuseStep 1834923 = 2752385) B2752385
theorem B1834935 : Blo 1833618 1834935 := bstep (se 1 (by rfl) ⟨1376201, by rfl⟩ : syracuseStep 1834935 = 2752403) B2752403
theorem B3481537 : Blo 1833618 3481537 := bstep (se 2 (by rfl) ⟨1305576, by rfl⟩ : syracuseStep 3481537 = 2611153) B2611153
theorem B1834955 : Blo 1833618 1834955 := bstep (se 1 (by rfl) ⟨1376216, by rfl⟩ : syracuseStep 1834955 = 2752433) B2752433
theorem B1834967 : Blo 1833618 1834967 := bstep (se 1 (by rfl) ⟨1376225, by rfl⟩ : syracuseStep 1834967 = 2752451) B2752451
theorem B2064343 : Blo 1833618 2064343 := bstep (se 1 (by rfl) ⟨1548257, by rfl⟩ : syracuseStep 2064343 = 3096515) B3096515
theorem B3096535 : Blo 1833618 3096535 := bstep (se 1 (by rfl) ⟨2322401, by rfl⟩ : syracuseStep 3096535 = 4644803) B4644803
theorem B1834987 : Blo 1833618 1834987 := bstep (se 1 (by rfl) ⟨1376240, by rfl⟩ : syracuseStep 1834987 = 2752481) B2752481
theorem B1834999 : Blo 1833618 1834999 := bstep (se 1 (by rfl) ⟨1376249, by rfl⟩ : syracuseStep 1834999 = 2752499) B2752499
theorem B1835015 : Blo 1833618 1835015 := bstep (se 1 (by rfl) ⟨1376261, by rfl⟩ : syracuseStep 1835015 = 2752523) B2752523
theorem B10452995 : Blo 1833618 10452995 := bstep (se 1 (by rfl) ⟨7839746, by rfl⟩ : syracuseStep 10452995 = 15679493) B15679493
theorem B1835023 : Blo 1833618 1835023 := bstep (se 1 (by rfl) ⟨1376267, by rfl⟩ : syracuseStep 1835023 = 2752535) B2752535
theorem B3481643 : Blo 1833618 3481643 := bstep (se 1 (by rfl) ⟨2611232, by rfl⟩ : syracuseStep 3481643 = 5222465) B5222465
theorem B2752571 : Blo 1833618 2752571 := bstep (se 1 (by rfl) ⟨2064428, by rfl⟩ : syracuseStep 2752571 = 4128857) B4128857
theorem B1835067 : Blo 1833618 1835067 := bstep (se 1 (by rfl) ⟨1376300, by rfl⟩ : syracuseStep 1835067 = 2752601) B2752601
theorem B2752631 : Blo 1833618 2752631 := bstep (se 1 (by rfl) ⟨2064473, by rfl⟩ : syracuseStep 2752631 = 4128947) B4128947
theorem B1835143 : Blo 1833618 1835143 := bstep (se 1 (by rfl) ⟨1376357, by rfl⟩ : syracuseStep 1835143 = 2752715) B2752715
theorem B2752655 : Blo 1833618 2752655 := bstep (se 1 (by rfl) ⟨2064491, by rfl⟩ : syracuseStep 2752655 = 4128983) B4128983
theorem B1835151 : Blo 1833618 1835151 := bstep (se 1 (by rfl) ⟨1376363, by rfl⟩ : syracuseStep 1835151 = 2752727) B2752727
theorem B2752697 : Blo 1833618 2752697 := bstep (se 2 (by rfl) ⟨1032261, by rfl⟩ : syracuseStep 2752697 = 2064523) B2064523
theorem B1835195 : Blo 1833618 1835195 := bstep (se 1 (by rfl) ⟨1376396, by rfl⟩ : syracuseStep 1835195 = 2752793) B2752793
theorem B2752775 : Blo 1833618 2752775 := bstep (se 1 (by rfl) ⟨2064581, by rfl⟩ : syracuseStep 2752775 = 4129163) B4129163
theorem B1835271 : Blo 1833618 1835271 := bstep (se 1 (by rfl) ⟨1376453, by rfl⟩ : syracuseStep 1835271 = 2752907) B2752907
theorem B1835279 : Blo 1833618 1835279 := bstep (se 1 (by rfl) ⟨1376459, by rfl⟩ : syracuseStep 1835279 = 2752919) B2752919
theorem B2752811 : Blo 1833618 2752811 := bstep (se 1 (by rfl) ⟨2064608, by rfl⟩ : syracuseStep 2752811 = 4129217) B4129217
theorem B6963515 : Blo 1833618 6963515 := bstep (se 1 (by rfl) ⟨5222636, by rfl⟩ : syracuseStep 6963515 = 10445273) B10445273
theorem B1835323 : Blo 1833618 1835323 := bstep (se 1 (by rfl) ⟨1376492, by rfl⟩ : syracuseStep 1835323 = 2752985) B2752985
theorem B2752841 : Blo 1833618 2752841 := bstep (se 2 (by rfl) ⟨1032315, by rfl⟩ : syracuseStep 2752841 = 2064631) B2064631
theorem B5226839 : Blo 1833618 5226839 := bstep (se 1 (by rfl) ⟨3920129, by rfl⟩ : syracuseStep 5226839 = 7840259) B7840259
theorem B3096967 : Blo 1833618 3096967 := bstep (se 1 (by rfl) ⟨2322725, by rfl⟩ : syracuseStep 3096967 = 4645451) B4645451
theorem B2064775 : Blo 1833618 2064775 := bstep (se 1 (by rfl) ⟨1548581, by rfl⟩ : syracuseStep 2064775 = 3097163) B3097163
theorem B1835399 : Blo 1833618 1835399 := bstep (se 1 (by rfl) ⟨1376549, by rfl⟩ : syracuseStep 1835399 = 2753099) B2753099
theorem B1835407 : Blo 1833618 1835407 := bstep (se 1 (by rfl) ⟨1376555, by rfl⟩ : syracuseStep 1835407 = 2753111) B2753111
theorem B2752955 : Blo 1833618 2752955 := bstep (se 1 (by rfl) ⟨2064716, by rfl⟩ : syracuseStep 2752955 = 4129433) B4129433
theorem B1835451 : Blo 1833618 1835451 := bstep (se 1 (by rfl) ⟨1376588, by rfl⟩ : syracuseStep 1835451 = 2753177) B2753177
theorem B2753015 : Blo 1833618 2753015 := bstep (se 1 (by rfl) ⟨2064761, by rfl⟩ : syracuseStep 2753015 = 4129523) B4129523
theorem B1835527 : Blo 1833618 1835527 := bstep (se 1 (by rfl) ⟨1376645, by rfl⟩ : syracuseStep 1835527 = 2753291) B2753291
theorem B2753039 : Blo 1833618 2753039 := bstep (se 1 (by rfl) ⟨2064779, by rfl⟩ : syracuseStep 2753039 = 4129559) B4129559
theorem B1835535 : Blo 1833618 1835535 := bstep (se 1 (by rfl) ⟨1376651, by rfl⟩ : syracuseStep 1835535 = 2753303) B2753303
theorem B2753081 : Blo 1833618 2753081 := bstep (se 2 (by rfl) ⟨1032405, by rfl⟩ : syracuseStep 2753081 = 2064811) B2064811
theorem B2064955 : Blo 1833618 2064955 := bstep (se 1 (by rfl) ⟨1548716, by rfl⟩ : syracuseStep 2064955 = 3097433) B3097433
theorem B5227067 : Blo 1833618 5227067 := bstep (se 1 (by rfl) ⟨3920300, by rfl⟩ : syracuseStep 5227067 = 7840601) B7840601
theorem B4956733 : Blo 1833618 4956733 := bstep (se 3 (by rfl) ⟨929387, by rfl⟩ : syracuseStep 4956733 = 1858775) B1858775
theorem B1835579 : Blo 1833618 1835579 := bstep (se 1 (by rfl) ⟨1376684, by rfl⟩ : syracuseStep 1835579 = 2753369) B2753369
theorem B3138167 : Blo 1833618 3138167 := bstep (se 1 (by rfl) ⟨2353625, by rfl⟩ : syracuseStep 3138167 = 4707251) B4707251
theorem B9921143 : Blo 1833618 9921143 := bstep (se 1 (by rfl) ⟨7440857, by rfl⟩ : syracuseStep 9921143 = 14881715) B14881715
theorem B4129415 : Blo 1833618 4129415 := bstep (se 1 (by rfl) ⟨3097061, by rfl⟩ : syracuseStep 4129415 = 6194123) B6194123
theorem B2753159 : Blo 1833618 2753159 := bstep (se 1 (by rfl) ⟨2064869, by rfl⟩ : syracuseStep 2753159 = 4129739) B4129739
theorem B2753195 : Blo 1833618 2753195 := bstep (se 1 (by rfl) ⟨2064896, by rfl⟩ : syracuseStep 2753195 = 4129793) B4129793
theorem B5227193 : Blo 1833618 5227193 := bstep (se 2 (by rfl) ⟨1960197, by rfl⟩ : syracuseStep 5227193 = 3920395) B3920395
theorem B23503553 : Blo 1833618 23503553 := bstep (se 2 (by rfl) ⟨8813832, by rfl⟩ : syracuseStep 23503553 = 17627665) B17627665
theorem B2753225 : Blo 1833618 2753225 := bstep (se 2 (by rfl) ⟨1032459, by rfl⟩ : syracuseStep 2753225 = 2064919) B2064919
theorem B4645633 : Blo 1833618 4645633 := bstep (se 2 (by rfl) ⟨1742112, by rfl⟩ : syracuseStep 4645633 = 3484225) B3484225
theorem B6964001 : Blo 1833618 6964001 := bstep (se 2 (by rfl) ⟨2611500, by rfl⟩ : syracuseStep 6964001 = 5223001) B5223001
theorem B4129595 : Blo 1833618 4129595 := bstep (se 1 (by rfl) ⟨3097196, by rfl⟩ : syracuseStep 4129595 = 6194393) B6194393
theorem B2753339 : Blo 1833618 2753339 := bstep (se 1 (by rfl) ⟨2065004, by rfl⟩ : syracuseStep 2753339 = 4130009) B4130009
theorem B2753399 : Blo 1833618 2753399 := bstep (se 1 (by rfl) ⟨2065049, by rfl⟩ : syracuseStep 2753399 = 4130099) B4130099
theorem B2753423 : Blo 1833618 2753423 := bstep (se 1 (by rfl) ⟨2065067, by rfl⟩ : syracuseStep 2753423 = 4130135) B4130135
theorem B7832467 : Blo 1833618 7832467 := bstep (se 1 (by rfl) ⟨5874350, by rfl⟩ : syracuseStep 7832467 = 11748701) B11748701
theorem B4129721 : Blo 1833618 4129721 := bstep (se 2 (by rfl) ⟨1548645, by rfl⟩ : syracuseStep 4129721 = 3097291) B3097291
theorem B13935563 : Blo 1833618 13935563 := bstep (se 1 (by rfl) ⟨10451672, by rfl⟩ : syracuseStep 13935563 = 20903345) B20903345
theorem B9290699 : Blo 1833618 9290699 := bstep (se 1 (by rfl) ⟨6968024, by rfl⟩ : syracuseStep 9290699 = 13936049) B13936049
theorem B9282761 : Blo 1833618 9282761 := bstep (se 2 (by rfl) ⟨3481035, by rfl⟩ : syracuseStep 9282761 = 6962071) B6962071
theorem B9291023 : Blo 1833618 9291023 := bstep (se 1 (by rfl) ⟨6968267, by rfl⟩ : syracuseStep 9291023 = 13936535) B13936535
theorem B6194447 : Blo 1833618 6194447 := bstep (se 1 (by rfl) ⟨4645835, by rfl⟩ : syracuseStep 6194447 = 9291671) B9291671
theorem B4130063 : Blo 1833618 4130063 := bstep (se 1 (by rfl) ⟨3097547, by rfl⟩ : syracuseStep 4130063 = 6195095) B6195095
theorem B4130081 : Blo 1833618 4130081 := bstep (se 2 (by rfl) ⟨1548780, by rfl⟩ : syracuseStep 4130081 = 3097561) B3097561
theorem B4646231 : Blo 1833618 4646231 := bstep (se 1 (by rfl) ⟨3484673, by rfl⟩ : syracuseStep 4646231 = 6969347) B6969347
theorem B11912633 : Blo 1833618 11912633 := bstep (se 2 (by rfl) ⟨4467237, by rfl⟩ : syracuseStep 11912633 = 8934475) B8934475
theorem B42362297 : Blo 1833618 42362297 := bstep (se 2 (by rfl) ⟨15885861, by rfl⟩ : syracuseStep 42362297 = 31771723) B31771723
theorem B3917327 : Blo 1833618 3917327 := bstep (se 1 (by rfl) ⟨2937995, by rfl⟩ : syracuseStep 3917327 = 5875991) B5875991
theorem B6612509 : Blo 1833618 6612509 := bstep (se 3 (by rfl) ⟨1239845, by rfl⟩ : syracuseStep 6612509 = 2479691) B2479691
theorem B6194717 : Blo 1833618 6194717 := bstep (se 3 (by rfl) ⟨1161509, by rfl⟩ : syracuseStep 6194717 = 2323019) B2323019
theorem B3720737 : Blo 1833618 3720737 := bstep (se 2 (by rfl) ⟨1395276, by rfl⟩ : syracuseStep 3720737 = 2790553) B2790553
theorem B4408985 : Blo 1833618 4408985 := bstep (se 2 (by rfl) ⟨1653369, by rfl⟩ : syracuseStep 4408985 = 3306739) B3306739
theorem B3483337 : Blo 1833618 3483337 := bstep (se 2 (by rfl) ⟨1306251, by rfl⟩ : syracuseStep 3483337 = 2612503) B2612503
theorem B6964973 : Blo 1833618 6964973 := bstep (se 3 (by rfl) ⟨1305932, by rfl⟩ : syracuseStep 6964973 = 2611865) B2611865
theorem B4409147 : Blo 1833618 4409147 := bstep (se 1 (by rfl) ⟨3306860, by rfl⟩ : syracuseStep 4409147 = 6613721) B6613721
theorem B3721079 : Blo 1833618 3721079 := bstep (se 1 (by rfl) ⟨2790809, by rfl⟩ : syracuseStep 3721079 = 5581619) B5581619
theorem B6965291 : Blo 1833618 6965291 := bstep (se 1 (by rfl) ⟨5223968, by rfl⟩ : syracuseStep 6965291 = 10447937) B10447937
theorem B10447163 : Blo 1833618 10447163 := bstep (se 1 (by rfl) ⟨7835372, by rfl⟩ : syracuseStep 10447163 = 15670745) B15670745
theorem B7833971 : Blo 1833618 7833971 := bstep (se 1 (by rfl) ⟨5875478, by rfl⟩ : syracuseStep 7833971 = 11750957) B11750957
theorem B6613433 : Blo 1833618 6613433 := bstep (se 2 (by rfl) ⟨2480037, by rfl⟩ : syracuseStep 6613433 = 4960075) B4960075
theorem B2320903 : Blo 1833618 2320903 := bstep (se 1 (by rfl) ⟨1740677, by rfl⟩ : syracuseStep 2320903 = 3481355) B3481355
theorem B11749931 : Blo 1833618 11749931 := bstep (se 1 (by rfl) ⟨8812448, by rfl⟩ : syracuseStep 11749931 = 17624897) B17624897
theorem B31361579 : Blo 1833618 31361579 := bstep (se 1 (by rfl) ⟨23521184, by rfl⟩ : syracuseStep 31361579 = 47042369) B47042369
theorem B79317569 : Blo 1833618 79317569 := bstep (se 2 (by rfl) ⟨29744088, by rfl⟩ : syracuseStep 79317569 = 59488177) B59488177
theorem B40766017 : Blo 1833618 40766017 := bstep (se 2 (by rfl) ⟨15287256, by rfl⟩ : syracuseStep 40766017 = 30574513) B30574513
theorem B20900429 : Blo 1833618 20900429 := bstep (se 3 (by rfl) ⟨3918830, by rfl⟩ : syracuseStep 20900429 = 7837661) B7837661
theorem B6613591 : Blo 1833618 6613591 := bstep (se 1 (by rfl) ⟨4960193, by rfl⟩ : syracuseStep 6613591 = 9920387) B9920387
theorem B9292481 : Blo 1833618 9292481 := bstep (se 2 (by rfl) ⟨3484680, by rfl⟩ : syracuseStep 9292481 = 6969361) B6969361
theorem B7834313 : Blo 1833618 7834313 := bstep (se 2 (by rfl) ⟨2937867, by rfl⟩ : syracuseStep 7834313 = 5875735) B5875735
theorem B5655329 : Blo 1833618 5655329 := bstep (se 2 (by rfl) ⟨2120748, by rfl⟩ : syracuseStep 5655329 = 4241497) B4241497
theorem B7834553 : Blo 1833618 7834553 := bstep (se 2 (by rfl) ⟨2937957, by rfl⟩ : syracuseStep 7834553 = 5875915) B5875915
theorem B2321399 : Blo 1833618 2321399 := bstep (se 1 (by rfl) ⟨1741049, by rfl⟩ : syracuseStep 2321399 = 3482099) B3482099
theorem B2321551 : Blo 1833618 2321551 := bstep (se 1 (by rfl) ⟨1741163, by rfl⟩ : syracuseStep 2321551 = 3482327) B3482327
theorem B5221577 : Blo 1833618 5221577 := bstep (se 2 (by rfl) ⟨1958091, by rfl⟩ : syracuseStep 5221577 = 3916183) B3916183
theorem B7834913 : Blo 1833618 7834913 := bstep (se 2 (by rfl) ⟨2938092, by rfl⟩ : syracuseStep 7834913 = 5876185) B5876185
theorem B17640737 : Blo 1833618 17640737 := bstep (se 2 (by rfl) ⟨6615276, by rfl⟩ : syracuseStep 17640737 = 13230553) B13230553
theorem B5221691 : Blo 1833618 5221691 := bstep (se 1 (by rfl) ⟨3916268, by rfl⟩ : syracuseStep 5221691 = 7832537) B7832537
theorem B2321723 : Blo 1833618 2321723 := bstep (se 1 (by rfl) ⟨1741292, by rfl⟩ : syracuseStep 2321723 = 3482585) B3482585
theorem B5877107 : Blo 1833618 5877107 := bstep (se 1 (by rfl) ⟨4407830, by rfl⟩ : syracuseStep 5877107 = 8815661) B8815661
theorem B39652739 : Blo 1833618 39652739 := bstep (se 1 (by rfl) ⟨29739554, by rfl⟩ : syracuseStep 39652739 = 59479109) B59479109
theorem B5221817 : Blo 1833618 5221817 := bstep (se 2 (by rfl) ⟨1958181, by rfl⟩ : syracuseStep 5221817 = 3916363) B3916363
theorem B10448621 : Blo 1833618 10448621 := bstep (se 3 (by rfl) ⟨1959116, by rfl⟩ : syracuseStep 10448621 = 3918233) B3918233
theorem B15085349 : Blo 1833618 15085349 := bstep (se 4 (by rfl) ⟨1414251, by rfl⟩ : syracuseStep 15085349 = 2828503) B2828503
theorem B4239239 : Blo 1833618 4239239 := bstep (se 1 (by rfl) ⟨3179429, by rfl⟩ : syracuseStep 4239239 = 6358859) B6358859
theorem B10448939 : Blo 1833618 10448939 := bstep (se 1 (by rfl) ⟨7836704, by rfl⟩ : syracuseStep 10448939 = 15673409) B15673409
theorem B14880941 : Blo 1833618 14880941 := bstep (se 3 (by rfl) ⟨2790176, by rfl⟩ : syracuseStep 14880941 = 5580353) B5580353
theorem B7835885 : Blo 1833618 7835885 := bstep (se 3 (by rfl) ⟨1469228, by rfl⟩ : syracuseStep 7835885 = 2938457) B2938457
theorem B2322695 : Blo 1833618 2322695 := bstep (se 1 (by rfl) ⟨1742021, by rfl⟩ : syracuseStep 2322695 = 3484043) B3484043
theorem B4960541 : Blo 1833618 4960541 := bstep (se 3 (by rfl) ⟨930101, by rfl⟩ : syracuseStep 4960541 = 1860203) B1860203
theorem B6189371 : Blo 1833618 6189371 := bstep (se 1 (by rfl) ⟨4642028, by rfl⟩ : syracuseStep 6189371 = 9284057) B9284057
theorem B14872891 : Blo 1833618 14872891 := bstep (se 1 (by rfl) ⟨11154668, by rfl⟩ : syracuseStep 14872891 = 22309337) B22309337
theorem B15675869 : Blo 1833618 15675869 := bstep (se 3 (by rfl) ⟨2939225, by rfl⟩ : syracuseStep 15675869 = 5878451) B5878451
theorem B7836227 : Blo 1833618 7836227 := bstep (se 1 (by rfl) ⟨5877170, by rfl⟩ : syracuseStep 7836227 = 11754341) B11754341
theorem B44634817 : Blo 1833618 44634817 := bstep (se 2 (by rfl) ⟨16738056, by rfl⟩ : syracuseStep 44634817 = 33476113) B33476113
theorem B42357509 : Blo 1833618 42357509 := bstep (se 4 (by rfl) ⟨3971016, by rfl⟩ : syracuseStep 42357509 = 7942033) B7942033
theorem B6189857 : Blo 1833618 6189857 := bstep (se 2 (by rfl) ⟨2321196, by rfl⟩ : syracuseStep 6189857 = 4642393) B4642393
theorem B23499557 : Blo 1833618 23499557 := bstep (se 4 (by rfl) ⟨2203083, by rfl⟩ : syracuseStep 23499557 = 4406167) B4406167
theorem B2790407 : Blo 1833618 2790407 := bstep (se 1 (by rfl) ⟨2092805, by rfl⟩ : syracuseStep 2790407 = 4185611) B4185611
theorem B5223467 : Blo 1833618 5223467 := bstep (se 1 (by rfl) ⟨3917600, by rfl⟩ : syracuseStep 5223467 = 7835201) B7835201
theorem B4707415 : Blo 1833618 4707415 := bstep (se 1 (by rfl) ⟨3530561, by rfl⟩ : syracuseStep 4707415 = 7061123) B7061123
theorem B4641907 : Blo 1833618 4641907 := bstep (se 1 (by rfl) ⟨3481430, by rfl⟩ : syracuseStep 4641907 = 6962861) B6962861
theorem B4125815 : Blo 1833618 4125815 := bstep (se 1 (by rfl) ⟨3094361, by rfl⟩ : syracuseStep 4125815 = 6188723) B6188723
theorem B13227209 : Blo 1833618 13227209 := bstep (se 2 (by rfl) ⟨4960203, by rfl⟩ : syracuseStep 13227209 = 9920407) B9920407
theorem B8811757 : Blo 1833618 8811757 := bstep (se 3 (by rfl) ⟨1652204, by rfl⟩ : syracuseStep 8811757 = 3304409) B3304409
theorem B4642049 : Blo 1833618 4642049 := bstep (se 2 (by rfl) ⟨1740768, by rfl⟩ : syracuseStep 4642049 = 3481537) B3481537
theorem B4125995 : Blo 1833618 4125995 := bstep (se 1 (by rfl) ⟨3094496, by rfl⟩ : syracuseStep 4125995 = 6188993) B6188993
theorem B31782203 : Blo 1833618 31782203 := bstep (se 1 (by rfl) ⟨23836652, by rfl⟩ : syracuseStep 31782203 = 47673305) B47673305
theorem B5297495 : Blo 1833618 5297495 := bstep (se 1 (by rfl) ⟨3973121, by rfl⟩ : syracuseStep 5297495 = 7946243) B7946243
theorem B6190451 : Blo 1833618 6190451 := bstep (se 1 (by rfl) ⟨4642838, by rfl⟩ : syracuseStep 6190451 = 9285677) B9285677
theorem B4838771 : Blo 1833618 4838771 := bstep (se 1 (by rfl) ⟨3629078, by rfl⟩ : syracuseStep 4838771 = 7258157) B7258157
theorem B10450397 : Blo 1833618 10450397 := bstep (se 3 (by rfl) ⟨1959449, by rfl⟩ : syracuseStep 10450397 = 3918899) B3918899
theorem B23516675 : Blo 1833618 23516675 := bstep (se 1 (by rfl) ⟨17637506, by rfl⟩ : syracuseStep 23516675 = 35275013) B35275013
theorem B6968861 : Blo 1833618 6968861 := bstep (se 3 (by rfl) ⟨1306661, by rfl⟩ : syracuseStep 6968861 = 2613323) B2613323
theorem B6968875 : Blo 1833618 6968875 := bstep (se 1 (by rfl) ⟨5226656, by rfl⟩ : syracuseStep 6968875 = 10453313) B10453313
theorem B15283831 : Blo 1833618 15283831 := bstep (se 1 (by rfl) ⟨11462873, by rfl⟩ : syracuseStep 15283831 = 22925747) B22925747
theorem B4126355 : Blo 1833618 4126355 := bstep (se 1 (by rfl) ⟨3094766, by rfl⟩ : syracuseStep 4126355 = 6189533) B6189533
theorem B4126409 : Blo 1833618 4126409 := bstep (se 2 (by rfl) ⟨1547403, by rfl⟩ : syracuseStep 4126409 = 3094807) B3094807
theorem B4642505 : Blo 1833618 4642505 := bstep (se 2 (by rfl) ⟨1740939, by rfl⟩ : syracuseStep 4642505 = 3481879) B3481879
theorem B48297701 : Blo 1833618 48297701 := bstep (se 4 (by rfl) ⟨4527909, by rfl⟩ : syracuseStep 48297701 = 9055819) B9055819
theorem B2610959 : Blo 1833618 2610959 := bstep (se 1 (by rfl) ⟨1958219, by rfl⟩ : syracuseStep 2610959 = 3916439) B3916439
theorem B5879567 : Blo 1833618 5879567 := bstep (se 1 (by rfl) ⟨4409675, by rfl⟩ : syracuseStep 5879567 = 8819351) B8819351
theorem B2750471 : Blo 1833618 2750471 := bstep (se 1 (by rfl) ⟨2062853, by rfl⟩ : syracuseStep 2750471 = 4125707) B4125707
theorem B5224459 : Blo 1833618 5224459 := bstep (se 1 (by rfl) ⟨3918344, by rfl⟩ : syracuseStep 5224459 = 7836689) B7836689
theorem B2750507 : Blo 1833618 2750507 := bstep (se 1 (by rfl) ⟨2062880, by rfl⟩ : syracuseStep 2750507 = 4125761) B4125761
theorem B3094571 : Blo 1833618 3094571 := bstep (se 1 (by rfl) ⟨2320928, by rfl⟩ : syracuseStep 3094571 = 4641857) B4641857
theorem B4642859 : Blo 1833618 4642859 := bstep (se 1 (by rfl) ⟨3482144, by rfl⟩ : syracuseStep 4642859 = 6964289) B6964289
theorem B2750537 : Blo 1833618 2750537 := bstep (se 2 (by rfl) ⟨1031451, by rfl⟩ : syracuseStep 2750537 = 2062903) B2062903
theorem B2611273 : Blo 1833618 2611273 := bstep (se 2 (by rfl) ⟨979227, by rfl⟩ : syracuseStep 2611273 = 1958455) B1958455
theorem B3528839 : Blo 1833618 3528839 := bstep (se 1 (by rfl) ⟨2646629, by rfl⟩ : syracuseStep 3528839 = 5293259) B5293259
theorem B4708505 : Blo 1833618 4708505 := bstep (se 2 (by rfl) ⟨1765689, by rfl⟩ : syracuseStep 4708505 = 3531379) B3531379
theorem B2750651 : Blo 1833618 2750651 := bstep (se 1 (by rfl) ⟨2062988, by rfl⟩ : syracuseStep 2750651 = 4125977) B4125977
theorem B2750711 : Blo 1833618 2750711 := bstep (se 1 (by rfl) ⟨2063033, by rfl⟩ : syracuseStep 2750711 = 4126067) B4126067
theorem B5028097 : Blo 1833618 5028097 := bstep (se 2 (by rfl) ⟨1885536, by rfl⟩ : syracuseStep 5028097 = 3771073) B3771073
theorem B5576971 : Blo 1833618 5576971 := bstep (se 1 (by rfl) ⟨4182728, by rfl⟩ : syracuseStep 5576971 = 8365457) B8365457
theorem B2750735 : Blo 1833618 2750735 := bstep (se 1 (by rfl) ⟨2063051, by rfl⟩ : syracuseStep 2750735 = 4126103) B4126103
theorem B5224733 : Blo 1833618 5224733 := bstep (se 3 (by rfl) ⟨979637, by rfl⟩ : syracuseStep 5224733 = 1959275) B1959275
theorem B2750777 : Blo 1833618 2750777 := bstep (se 2 (by rfl) ⟨1031541, by rfl⟩ : syracuseStep 2750777 = 2063083) B2063083
theorem B2750855 : Blo 1833618 2750855 := bstep (se 1 (by rfl) ⟨2063141, by rfl⟩ : syracuseStep 2750855 = 4126283) B4126283
theorem B4127111 : Blo 1833618 4127111 := bstep (se 1 (by rfl) ⟨3095333, by rfl⟩ : syracuseStep 4127111 = 6190667) B6190667
theorem B2750891 : Blo 1833618 2750891 := bstep (se 1 (by rfl) ⟨2063168, by rfl⟩ : syracuseStep 2750891 = 4126337) B4126337
theorem B3094969 : Blo 1833618 3094969 := bstep (se 2 (by rfl) ⟨1160613, by rfl⟩ : syracuseStep 3094969 = 2321227) B2321227
theorem B2750921 : Blo 1833618 2750921 := bstep (se 2 (by rfl) ⟨1031595, by rfl⟩ : syracuseStep 2750921 = 2063191) B2063191
theorem B2751035 : Blo 1833618 2751035 := bstep (se 1 (by rfl) ⟨2063276, by rfl⟩ : syracuseStep 2751035 = 4126553) B4126553
theorem B4127291 : Blo 1833618 4127291 := bstep (se 1 (by rfl) ⟨3095468, by rfl⟩ : syracuseStep 4127291 = 6190937) B6190937
theorem B25451075 : Blo 1833618 25451075 := bstep (se 1 (by rfl) ⟨19088306, by rfl⟩ : syracuseStep 25451075 = 38176613) B38176613
theorem B13933133 : Blo 1833618 13933133 := bstep (se 3 (by rfl) ⟨2612462, by rfl⟩ : syracuseStep 13933133 = 5224925) B5224925
theorem B2751095 : Blo 1833618 2751095 := bstep (se 1 (by rfl) ⟨2063321, by rfl⟩ : syracuseStep 2751095 = 4126643) B4126643
theorem B2751119 : Blo 1833618 2751119 := bstep (se 1 (by rfl) ⟨2063339, by rfl⟩ : syracuseStep 2751119 = 4126679) B4126679
theorem B2751161 : Blo 1833618 2751161 := bstep (se 2 (by rfl) ⟨1031685, by rfl⟩ : syracuseStep 2751161 = 2063371) B2063371
theorem B4127417 : Blo 1833618 4127417 := bstep (se 2 (by rfl) ⟨1547781, by rfl⟩ : syracuseStep 4127417 = 3095563) B3095563
theorem B1833659 : Blo 1833618 1833659 := bstep (se 1 (by rfl) ⟨1375244, by rfl⟩ : syracuseStep 1833659 = 2750489) B2750489
theorem B1833735 : Blo 1833618 1833735 := bstep (se 1 (by rfl) ⟨1375301, by rfl⟩ : syracuseStep 1833735 = 2750603) B2750603
theorem B2751239 : Blo 1833618 2751239 := bstep (se 1 (by rfl) ⟨2063429, by rfl⟩ : syracuseStep 2751239 = 4126859) B4126859
theorem B1833743 : Blo 1833618 1833743 := bstep (se 1 (by rfl) ⟨1375307, by rfl⟩ : syracuseStep 1833743 = 2750615) B2750615
theorem B2063119 : Blo 1833618 2063119 := bstep (se 1 (by rfl) ⟨1547339, by rfl⟩ : syracuseStep 2063119 = 3094679) B3094679
theorem B2751275 : Blo 1833618 2751275 := bstep (se 1 (by rfl) ⟨2063456, by rfl⟩ : syracuseStep 2751275 = 4126913) B4126913
theorem B1833787 : Blo 1833618 1833787 := bstep (se 1 (by rfl) ⟨1375340, by rfl⟩ : syracuseStep 1833787 = 2750681) B2750681
theorem B2751305 : Blo 1833618 2751305 := bstep (se 2 (by rfl) ⟨1031739, by rfl⟩ : syracuseStep 2751305 = 2063479) B2063479
theorem B1833863 : Blo 1833618 1833863 := bstep (se 1 (by rfl) ⟨1375397, by rfl⟩ : syracuseStep 1833863 = 2750795) B2750795
theorem B4242311 : Blo 1833618 4242311 := bstep (se 1 (by rfl) ⟨3181733, by rfl⟩ : syracuseStep 4242311 = 6363467) B6363467
theorem B1833871 : Blo 1833618 1833871 := bstep (se 1 (by rfl) ⟨1375403, by rfl⟩ : syracuseStep 1833871 = 2750807) B2750807
theorem B9288593 : Blo 1833618 9288593 := bstep (se 2 (by rfl) ⟨3483222, by rfl⟩ : syracuseStep 9288593 = 6966445) B6966445
theorem B16735139 : Blo 1833618 16735139 := bstep (se 1 (by rfl) ⟨12551354, by rfl⟩ : syracuseStep 16735139 = 25102709) B25102709
theorem B1833915 : Blo 1833618 1833915 := bstep (se 1 (by rfl) ⟨1375436, by rfl⟩ : syracuseStep 1833915 = 2750873) B2750873
theorem B2751419 : Blo 1833618 2751419 := bstep (se 1 (by rfl) ⟨2063564, by rfl⟩ : syracuseStep 2751419 = 4127129) B4127129
theorem B2751479 : Blo 1833618 2751479 := bstep (se 1 (by rfl) ⟨2063609, by rfl⟩ : syracuseStep 2751479 = 4127219) B4127219
theorem B1833991 : Blo 1833618 1833991 := bstep (se 1 (by rfl) ⟨1375493, by rfl⟩ : syracuseStep 1833991 = 2750987) B2750987
theorem B4643851 : Blo 1833618 4643851 := bstep (se 1 (by rfl) ⟨3482888, by rfl⟩ : syracuseStep 4643851 = 6965777) B6965777
theorem B1833999 : Blo 1833618 1833999 := bstep (se 1 (by rfl) ⟨1375499, by rfl⟩ : syracuseStep 1833999 = 2750999) B2750999
theorem B2751503 : Blo 1833618 2751503 := bstep (se 1 (by rfl) ⟨2063627, by rfl⟩ : syracuseStep 2751503 = 4127255) B4127255
theorem B4127759 : Blo 1833618 4127759 := bstep (se 1 (by rfl) ⟨3095819, by rfl⟩ : syracuseStep 4127759 = 6191639) B6191639
theorem B4127777 : Blo 1833618 4127777 := bstep (se 2 (by rfl) ⟨1547916, by rfl⟩ : syracuseStep 4127777 = 3095833) B3095833
theorem B2751545 : Blo 1833618 2751545 := bstep (se 2 (by rfl) ⟨1031829, by rfl⟩ : syracuseStep 2751545 = 2063659) B2063659
theorem B1834043 : Blo 1833618 1834043 := bstep (se 1 (by rfl) ⟨1375532, by rfl⟩ : syracuseStep 1834043 = 2751065) B2751065
theorem B3095671 : Blo 1833618 3095671 := bstep (se 1 (by rfl) ⟨2321753, by rfl⟩ : syracuseStep 3095671 = 4643507) B4643507
theorem B1834119 : Blo 1833618 1834119 := bstep (se 1 (by rfl) ⟨1375589, by rfl⟩ : syracuseStep 1834119 = 2751179) B2751179
theorem B2751623 : Blo 1833618 2751623 := bstep (se 1 (by rfl) ⟨2063717, by rfl⟩ : syracuseStep 2751623 = 4127435) B4127435
theorem B1834127 : Blo 1833618 1834127 := bstep (se 1 (by rfl) ⟨1375595, by rfl⟩ : syracuseStep 1834127 = 2751191) B2751191
theorem B4643993 : Blo 1833618 4643993 := bstep (se 2 (by rfl) ⟨1741497, by rfl⟩ : syracuseStep 4643993 = 3482995) B3482995
theorem B2751659 : Blo 1833618 2751659 := bstep (se 1 (by rfl) ⟨2063744, by rfl⟩ : syracuseStep 2751659 = 4127489) B4127489
theorem B1834171 : Blo 1833618 1834171 := bstep (se 1 (by rfl) ⟨1375628, by rfl⟩ : syracuseStep 1834171 = 2751257) B2751257
theorem B2751689 : Blo 1833618 2751689 := bstep (se 2 (by rfl) ⟨1031883, by rfl⟩ : syracuseStep 2751689 = 2063767) B2063767
theorem B1834247 : Blo 1833618 1834247 := bstep (se 1 (by rfl) ⟨1375685, by rfl⟩ : syracuseStep 1834247 = 2751371) B2751371
theorem B2063623 : Blo 1833618 2063623 := bstep (se 1 (by rfl) ⟨1547717, by rfl⟩ : syracuseStep 2063623 = 3095435) B3095435
theorem B1834255 : Blo 1833618 1834255 := bstep (se 1 (by rfl) ⟨1375691, by rfl⟩ : syracuseStep 1834255 = 2751383) B2751383
theorem B13229345 : Blo 1833618 13229345 := bstep (se 2 (by rfl) ⟨4961004, by rfl⟩ : syracuseStep 13229345 = 9922009) B9922009
theorem B1834299 : Blo 1833618 1834299 := bstep (se 1 (by rfl) ⟨1375724, by rfl⟩ : syracuseStep 1834299 = 2751449) B2751449
theorem B2751803 : Blo 1833618 2751803 := bstep (se 1 (by rfl) ⟨2063852, by rfl⟩ : syracuseStep 2751803 = 4127705) B4127705
theorem B3095867 : Blo 1833618 3095867 := bstep (se 1 (by rfl) ⟨2321900, by rfl⟩ : syracuseStep 3095867 = 4643801) B4643801
theorem B4644155 : Blo 1833618 4644155 := bstep (se 1 (by rfl) ⟨3483116, by rfl⟩ : syracuseStep 4644155 = 6966233) B6966233
theorem B2751863 : Blo 1833618 2751863 := bstep (se 1 (by rfl) ⟨2063897, by rfl⟩ : syracuseStep 2751863 = 4127795) B4127795
theorem B4128119 : Blo 1833618 4128119 := bstep (se 1 (by rfl) ⟨3096089, by rfl⟩ : syracuseStep 4128119 = 6192179) B6192179
theorem B44629379 : Blo 1833618 44629379 := bstep (se 1 (by rfl) ⟨33472034, by rfl⟩ : syracuseStep 44629379 = 66944069) B66944069
theorem B1834375 : Blo 1833618 1834375 := bstep (se 1 (by rfl) ⟨1375781, by rfl⟩ : syracuseStep 1834375 = 2751563) B2751563
theorem B1834383 : Blo 1833618 1834383 := bstep (se 1 (by rfl) ⟨1375787, by rfl⟩ : syracuseStep 1834383 = 2751575) B2751575
theorem B2751887 : Blo 1833618 2751887 := bstep (se 1 (by rfl) ⟨2063915, by rfl⟩ : syracuseStep 2751887 = 4127831) B4127831
theorem B2751929 : Blo 1833618 2751929 := bstep (se 2 (by rfl) ⟨1031973, by rfl⟩ : syracuseStep 2751929 = 2063947) B2063947
theorem B1834427 : Blo 1833618 1834427 := bstep (se 1 (by rfl) ⟨1375820, by rfl⟩ : syracuseStep 1834427 = 2751641) B2751641
theorem B2063803 : Blo 1833618 2063803 := bstep (se 1 (by rfl) ⟨1547852, by rfl⟩ : syracuseStep 2063803 = 3095705) B3095705
theorem B4718081 : Blo 1833618 4718081 := bstep (se 2 (by rfl) ⟨1769280, by rfl⟩ : syracuseStep 4718081 = 3538561) B3538561
theorem B1834503 : Blo 1833618 1834503 := bstep (se 1 (by rfl) ⟨1375877, by rfl⟩ : syracuseStep 1834503 = 2751755) B2751755
theorem B2752007 : Blo 1833618 2752007 := bstep (se 1 (by rfl) ⟨2064005, by rfl⟩ : syracuseStep 2752007 = 4128011) B4128011
theorem B1834511 : Blo 1833618 1834511 := bstep (se 1 (by rfl) ⟨1375883, by rfl⟩ : syracuseStep 1834511 = 2751767) B2751767
theorem B5578283 : Blo 1833618 5578283 := bstep (se 1 (by rfl) ⟨4183712, by rfl⟩ : syracuseStep 5578283 = 8367425) B8367425
theorem B2752043 : Blo 1833618 2752043 := bstep (se 1 (by rfl) ⟨2064032, by rfl⟩ : syracuseStep 2752043 = 4128065) B4128065
theorem B4128299 : Blo 1833618 4128299 := bstep (se 1 (by rfl) ⟨3096224, by rfl⟩ : syracuseStep 4128299 = 6192449) B6192449
theorem B1834555 : Blo 1833618 1834555 := bstep (se 1 (by rfl) ⟨1375916, by rfl⟩ : syracuseStep 1834555 = 2751833) B2751833
theorem B2752073 : Blo 1833618 2752073 := bstep (se 2 (by rfl) ⟨1032027, by rfl⟩ : syracuseStep 2752073 = 2064055) B2064055
theorem B1834631 : Blo 1833618 1834631 := bstep (se 1 (by rfl) ⟨1375973, by rfl⟩ : syracuseStep 1834631 = 2751947) B2751947
theorem B1834639 : Blo 1833618 1834639 := bstep (se 1 (by rfl) ⟨1375979, by rfl⟩ : syracuseStep 1834639 = 2751959) B2751959
theorem B4644499 : Blo 1833618 4644499 := bstep (se 1 (by rfl) ⟨3483374, by rfl⟩ : syracuseStep 4644499 = 6966749) B6966749
theorem B21175987 : Blo 1833618 21175987 := bstep (se 1 (by rfl) ⟨15881990, by rfl⟩ : syracuseStep 21175987 = 31763981) B31763981
theorem B1834683 : Blo 1833618 1834683 := bstep (se 1 (by rfl) ⟨1376012, by rfl⟩ : syracuseStep 1834683 = 2752025) B2752025
theorem B2752187 : Blo 1833618 2752187 := bstep (se 1 (by rfl) ⟨2064140, by rfl⟩ : syracuseStep 2752187 = 4128281) B4128281
theorem B3096265 : Blo 1833618 3096265 := bstep (se 2 (by rfl) ⟨1161099, by rfl⟩ : syracuseStep 3096265 = 2322199) B2322199
theorem B2752247 : Blo 1833618 2752247 := bstep (se 1 (by rfl) ⟨2064185, by rfl⟩ : syracuseStep 2752247 = 4128371) B4128371
theorem B16727809 : Blo 1833618 16727809 := bstep (se 2 (by rfl) ⟨6272928, by rfl⟩ : syracuseStep 16727809 = 12545857) B12545857
theorem B1834759 : Blo 1833618 1834759 := bstep (se 1 (by rfl) ⟨1376069, by rfl⟩ : syracuseStep 1834759 = 2752139) B2752139
theorem B1834767 : Blo 1833618 1834767 := bstep (se 1 (by rfl) ⟨1376075, by rfl⟩ : syracuseStep 1834767 = 2752151) B2752151
theorem B2752271 : Blo 1833618 2752271 := bstep (se 1 (by rfl) ⟨2064203, by rfl⟩ : syracuseStep 2752271 = 4128407) B4128407
theorem B4644641 : Blo 1833618 4644641 := bstep (se 2 (by rfl) ⟨1741740, by rfl⟩ : syracuseStep 4644641 = 3483481) B3483481
theorem B25100081 : Blo 1833618 25100081 := bstep (se 2 (by rfl) ⟨9412530, by rfl⟩ : syracuseStep 25100081 = 18825061) B18825061
theorem B2752313 : Blo 1833618 2752313 := bstep (se 2 (by rfl) ⟨1032117, by rfl⟩ : syracuseStep 2752313 = 2064235) B2064235
theorem B1834811 : Blo 1833618 1834811 := bstep (se 1 (by rfl) ⟨1376108, by rfl⟩ : syracuseStep 1834811 = 2752217) B2752217
theorem B6610823 : Blo 1833618 6610823 := bstep (se 1 (by rfl) ⟨4958117, by rfl⟩ : syracuseStep 6610823 = 9916235) B9916235
theorem B1834887 : Blo 1833618 1834887 := bstep (se 1 (by rfl) ⟨1376165, by rfl⟩ : syracuseStep 1834887 = 2752331) B2752331
theorem B2752391 : Blo 1833618 2752391 := bstep (se 1 (by rfl) ⟨2064293, by rfl⟩ : syracuseStep 2752391 = 4128587) B4128587
theorem B1834895 : Blo 1833618 1834895 := bstep (se 1 (by rfl) ⟨1376171, by rfl⟩ : syracuseStep 1834895 = 2752343) B2752343
theorem B2064271 : Blo 1833618 2064271 := bstep (se 1 (by rfl) ⟨1548203, by rfl⟩ : syracuseStep 2064271 = 3096407) B3096407
theorem B4128659 : Blo 1833618 4128659 := bstep (se 1 (by rfl) ⟨3096494, by rfl⟩ : syracuseStep 4128659 = 6192989) B6192989
theorem B6193043 : Blo 1833618 6193043 := bstep (se 1 (by rfl) ⟨4644782, by rfl⟩ : syracuseStep 6193043 = 9289565) B9289565
theorem B2752427 : Blo 1833618 2752427 := bstep (se 1 (by rfl) ⟨2064320, by rfl⟩ : syracuseStep 2752427 = 4128641) B4128641
theorem B1834939 : Blo 1833618 1834939 := bstep (se 1 (by rfl) ⟨1376204, by rfl⟩ : syracuseStep 1834939 = 2752409) B2752409
theorem B2752457 : Blo 1833618 2752457 := bstep (se 2 (by rfl) ⟨1032171, by rfl⟩ : syracuseStep 2752457 = 2064343) B2064343
theorem B4128713 : Blo 1833618 4128713 := bstep (se 2 (by rfl) ⟨1548267, by rfl⟩ : syracuseStep 4128713 = 3096535) B3096535
theorem B10444747 : Blo 1833618 10444747 := bstep (se 1 (by rfl) ⟨7833560, by rfl⟩ : syracuseStep 10444747 = 15667121) B15667121
theorem B1835047 : Blo 1833618 1835047 := bstep (se 1 (by rfl) ⟨1376285, by rfl⟩ : syracuseStep 1835047 = 2752571) B2752571
theorem B1835087 : Blo 1833618 1835087 := bstep (se 1 (by rfl) ⟨1376315, by rfl⟩ : syracuseStep 1835087 = 2752631) B2752631
theorem B3481697 : Blo 1833618 3481697 := bstep (se 2 (by rfl) ⟨1305636, by rfl⟩ : syracuseStep 3481697 = 2611273) B2611273
theorem B1835103 : Blo 1833618 1835103 := bstep (se 1 (by rfl) ⟨1376327, by rfl⟩ : syracuseStep 1835103 = 2752655) B2752655
theorem B9920627 : Blo 1833618 9920627 := bstep (se 1 (by rfl) ⟨7440470, by rfl⟩ : syracuseStep 9920627 = 14880941) B14880941
theorem B1835131 : Blo 1833618 1835131 := bstep (se 1 (by rfl) ⟨1376348, by rfl⟩ : syracuseStep 1835131 = 2752697) B2752697
theorem B1835183 : Blo 1833618 1835183 := bstep (se 1 (by rfl) ⟨1376387, by rfl⟩ : syracuseStep 1835183 = 2752775) B2752775
theorem B1835207 : Blo 1833618 1835207 := bstep (se 1 (by rfl) ⟨1376405, by rfl⟩ : syracuseStep 1835207 = 2752811) B2752811
theorem B1835227 : Blo 1833618 1835227 := bstep (se 1 (by rfl) ⟨1376420, by rfl⟩ : syracuseStep 1835227 = 2752841) B2752841
theorem B1835303 : Blo 1833618 1835303 := bstep (se 1 (by rfl) ⟨1376477, by rfl⟩ : syracuseStep 1835303 = 2752955) B2752955
theorem B26435909 : Blo 1833618 26435909 := bstep (se 4 (by rfl) ⟨2478366, by rfl⟩ : syracuseStep 26435909 = 4956733) B4956733
theorem B1835343 : Blo 1833618 1835343 := bstep (se 1 (by rfl) ⟨1376507, by rfl⟩ : syracuseStep 1835343 = 2753015) B2753015
theorem B1835359 : Blo 1833618 1835359 := bstep (se 1 (by rfl) ⟨1376519, by rfl⟩ : syracuseStep 1835359 = 2753039) B2753039
theorem B1835387 : Blo 1833618 1835387 := bstep (se 1 (by rfl) ⟨1376540, by rfl⟩ : syracuseStep 1835387 = 2753081) B2753081
theorem B2752943 : Blo 1833618 2752943 := bstep (se 1 (by rfl) ⟨2064707, by rfl⟩ : syracuseStep 2752943 = 4129415) B4129415
theorem B1835439 : Blo 1833618 1835439 := bstep (se 1 (by rfl) ⟨1376579, by rfl⟩ : syracuseStep 1835439 = 2753159) B2753159
theorem B1835463 : Blo 1833618 1835463 := bstep (se 1 (by rfl) ⟨1376597, by rfl⟩ : syracuseStep 1835463 = 2753195) B2753195
theorem B1835483 : Blo 1833618 1835483 := bstep (se 1 (by rfl) ⟨1376612, by rfl⟩ : syracuseStep 1835483 = 2753225) B2753225
theorem B28238339 : Blo 1833618 28238339 := bstep (se 1 (by rfl) ⟨21178754, by rfl⟩ : syracuseStep 28238339 = 42357509) B42357509
theorem B4129289 : Blo 1833618 4129289 := bstep (se 2 (by rfl) ⟨1548483, by rfl⟩ : syracuseStep 4129289 = 3096967) B3096967
theorem B2753033 : Blo 1833618 2753033 := bstep (se 2 (by rfl) ⟨1032387, by rfl⟩ : syracuseStep 2753033 = 2064775) B2064775
theorem B2753063 : Blo 1833618 2753063 := bstep (se 1 (by rfl) ⟨2064797, by rfl⟩ : syracuseStep 2753063 = 4129595) B4129595
theorem B1835559 : Blo 1833618 1835559 := bstep (se 1 (by rfl) ⟨1376669, by rfl⟩ : syracuseStep 1835559 = 2753339) B2753339
theorem B1835599 : Blo 1833618 1835599 := bstep (se 1 (by rfl) ⟨1376699, by rfl⟩ : syracuseStep 1835599 = 2753399) B2753399
theorem B1835615 : Blo 1833618 1835615 := bstep (se 1 (by rfl) ⟨1376711, by rfl⟩ : syracuseStep 1835615 = 2753423) B2753423
theorem B2753147 : Blo 1833618 2753147 := bstep (se 1 (by rfl) ⟨2064860, by rfl⟩ : syracuseStep 2753147 = 4129721) B4129721
theorem B9290375 : Blo 1833618 9290375 := bstep (se 1 (by rfl) ⟨6967781, by rfl⟩ : syracuseStep 9290375 = 13935563) B13935563
theorem B6193799 : Blo 1833618 6193799 := bstep (se 1 (by rfl) ⟨4645349, by rfl⟩ : syracuseStep 6193799 = 9290699) B9290699
theorem B6193853 : Blo 1833618 6193853 := bstep (se 3 (by rfl) ⟨1161347, by rfl⟩ : syracuseStep 6193853 = 2322695) B2322695
theorem B2753273 : Blo 1833618 2753273 := bstep (se 2 (by rfl) ⟨1032477, by rfl⟩ : syracuseStep 2753273 = 2064955) B2064955
theorem B54354689 : Blo 1833618 54354689 := bstep (se 2 (by rfl) ⟨20383008, by rfl⟩ : syracuseStep 54354689 = 40766017) B40766017
theorem B6194015 : Blo 1833618 6194015 := bstep (se 1 (by rfl) ⟨4645511, by rfl⟩ : syracuseStep 6194015 = 9291023) B9291023
theorem B4129631 : Blo 1833618 4129631 := bstep (se 1 (by rfl) ⟨3097223, by rfl⟩ : syracuseStep 4129631 = 6194447) B6194447
theorem B2753375 : Blo 1833618 2753375 := bstep (se 1 (by rfl) ⟨2065031, by rfl⟩ : syracuseStep 2753375 = 4130063) B4130063
theorem B2753387 : Blo 1833618 2753387 := bstep (se 1 (by rfl) ⟨2065040, by rfl⟩ : syracuseStep 2753387 = 4130081) B4130081
theorem B3097487 : Blo 1833618 3097487 := bstep (se 1 (by rfl) ⟨2323115, by rfl⟩ : syracuseStep 3097487 = 4646231) B4646231
theorem B6194177 : Blo 1833618 6194177 := bstep (se 2 (by rfl) ⟨2322816, by rfl⟩ : syracuseStep 6194177 = 4645633) B4645633
theorem B4408339 : Blo 1833618 4408339 := bstep (se 1 (by rfl) ⟨3306254, by rfl⟩ : syracuseStep 4408339 = 6612509) B6612509
theorem B4645907 : Blo 1833618 4645907 := bstep (se 1 (by rfl) ⟨3484430, by rfl⟩ : syracuseStep 4645907 = 6968861) B6968861
theorem B4129811 : Blo 1833618 4129811 := bstep (se 1 (by rfl) ⟨3097358, by rfl⟩ : syracuseStep 4129811 = 6194717) B6194717
theorem B10446205 : Blo 1833618 10446205 := bstep (se 3 (by rfl) ⟨1958663, by rfl⟩ : syracuseStep 10446205 = 3917327) B3917327
theorem B2352559 : Blo 1833618 2352559 := bstep (se 1 (by rfl) ⟨1764419, by rfl⟩ : syracuseStep 2352559 = 3528839) B3528839
theorem B3139003 : Blo 1833618 3139003 := bstep (se 1 (by rfl) ⟨2354252, by rfl⟩ : syracuseStep 3139003 = 4708505) B4708505
theorem B3483155 : Blo 1833618 3483155 := bstep (se 1 (by rfl) ⟨2612366, by rfl⟩ : syracuseStep 3483155 = 5224733) B5224733
theorem B6964775 : Blo 1833618 6964775 := bstep (se 1 (by rfl) ⟨5223581, by rfl⟩ : syracuseStep 6964775 = 10447163) B10447163
theorem B4408955 : Blo 1833618 4408955 := bstep (se 1 (by rfl) ⟨3306716, by rfl⟩ : syracuseStep 4408955 = 6613433) B6613433
theorem B11749009 : Blo 1833618 11749009 := bstep (se 2 (by rfl) ⟨4405878, by rfl⟩ : syracuseStep 11749009 = 8811757) B8811757
theorem B7833287 : Blo 1833618 7833287 := bstep (se 1 (by rfl) ⟨5874965, by rfl⟩ : syracuseStep 7833287 = 11749931) B11749931
theorem B20907719 : Blo 1833618 20907719 := bstep (se 1 (by rfl) ⟨15680789, by rfl⟩ : syracuseStep 20907719 = 31361579) B31361579
theorem B16967383 : Blo 1833618 16967383 := bstep (se 1 (by rfl) ⟨12725537, by rfl⟩ : syracuseStep 16967383 = 25451075) B25451075
theorem B6194987 : Blo 1833618 6194987 := bstep (se 1 (by rfl) ⟨4646240, by rfl⟩ : syracuseStep 6194987 = 9292481) B9292481
theorem B3770219 : Blo 1833618 3770219 := bstep (se 1 (by rfl) ⟨2827664, by rfl⟩ : syracuseStep 3770219 = 5655329) B5655329
theorem B2828207 : Blo 1833618 2828207 := bstep (se 1 (by rfl) ⟨2121155, by rfl⟩ : syracuseStep 2828207 = 4242311) B4242311
theorem B9291833 : Blo 1833618 9291833 := bstep (se 2 (by rfl) ⟨3484437, by rfl⟩ : syracuseStep 9291833 = 6968875) B6968875
theorem B3918071 : Blo 1833618 3918071 := bstep (se 1 (by rfl) ⟨2938553, by rfl⟩ : syracuseStep 3918071 = 5877107) B5877107
theorem B6965747 : Blo 1833618 6965747 := bstep (se 1 (by rfl) ⟨5224310, by rfl⟩ : syracuseStep 6965747 = 10448621) B10448621
theorem B6965945 : Blo 1833618 6965945 := bstep (se 2 (by rfl) ⟨2612229, by rfl⟩ : syracuseStep 6965945 = 5224459) B5224459
theorem B7441085 : Blo 1833618 7441085 := bstep (se 3 (by rfl) ⟨1395203, by rfl⟩ : syracuseStep 7441085 = 2790407) B2790407
theorem B6965959 : Blo 1833618 6965959 := bstep (se 1 (by rfl) ⟨5224469, by rfl⟩ : syracuseStep 6965959 = 10448939) B10448939
theorem B9284381 : Blo 1833618 9284381 := bstep (se 3 (by rfl) ⟨1740821, by rfl⟩ : syracuseStep 9284381 = 3481643) B3481643
theorem B13929245 : Blo 1833618 13929245 := bstep (se 3 (by rfl) ⟨2611733, by rfl⟩ : syracuseStep 13929245 = 5223467) B5223467
theorem B3484559 : Blo 1833618 3484559 := bstep (se 1 (by rfl) ⟨2613419, by rfl⟩ : syracuseStep 3484559 = 5226839) B5226839
theorem B6704129 : Blo 1833618 6704129 := bstep (se 2 (by rfl) ⟨2514048, by rfl⟩ : syracuseStep 6704129 = 5028097) B5028097
theorem B3484711 : Blo 1833618 3484711 := bstep (se 1 (by rfl) ⟨2613533, by rfl⟩ : syracuseStep 3484711 = 5227067) B5227067
theorem B3484795 : Blo 1833618 3484795 := bstep (se 1 (by rfl) ⟨2613596, by rfl⟩ : syracuseStep 3484795 = 5227193) B5227193
theorem B15666371 : Blo 1833618 15666371 := bstep (se 1 (by rfl) ⟨11749778, by rfl⟩ : syracuseStep 15666371 = 23499557) B23499557
theorem B8818121 : Blo 1833618 8818121 := bstep (se 2 (by rfl) ⟨3306795, by rfl⟩ : syracuseStep 8818121 = 6613591) B6613591
theorem B6188507 : Blo 1833618 6188507 := bstep (se 1 (by rfl) ⟨4641380, by rfl⟩ : syracuseStep 6188507 = 9282761) B9282761
theorem B8818139 : Blo 1833618 8818139 := bstep (se 1 (by rfl) ⟨6613604, by rfl⟩ : syracuseStep 8818139 = 13227209) B13227209
theorem B21188135 : Blo 1833618 21188135 := bstep (se 1 (by rfl) ⟨15891101, by rfl⟩ : syracuseStep 21188135 = 31782203) B31782203
theorem B14126653 : Blo 1833618 14126653 := bstep (se 3 (by rfl) ⟨2648747, by rfl⟩ : syracuseStep 14126653 = 5297495) B5297495
theorem B7941755 : Blo 1833618 7941755 := bstep (se 1 (by rfl) ⟨5956316, by rfl⟩ : syracuseStep 7941755 = 11912633) B11912633
theorem B28241531 : Blo 1833618 28241531 := bstep (se 1 (by rfl) ⟨21181148, by rfl⟩ : syracuseStep 28241531 = 42362297) B42362297
theorem B6966931 : Blo 1833618 6966931 := bstep (se 1 (by rfl) ⟨5225198, by rfl⟩ : syracuseStep 6966931 = 10450397) B10450397
theorem B32198467 : Blo 1833618 32198467 := bstep (se 1 (by rfl) ⟨24148850, by rfl⟩ : syracuseStep 32198467 = 48297701) B48297701
theorem B6189209 : Blo 1833618 6189209 := bstep (se 2 (by rfl) ⟨2320953, by rfl⟩ : syracuseStep 6189209 = 4641907) B4641907
theorem B5222647 : Blo 1833618 5222647 := bstep (se 1 (by rfl) ⟨3916985, by rfl⟩ : syracuseStep 5222647 = 7833971) B7833971
theorem B8368445 : Blo 1833618 8368445 := bstep (se 3 (by rfl) ⟨1569083, by rfl⟩ : syracuseStep 8368445 = 3138167) B3138167
theorem B26456381 : Blo 1833618 26456381 := bstep (se 3 (by rfl) ⟨4960571, by rfl⟩ : syracuseStep 26456381 = 9921143) B9921143
theorem B5222875 : Blo 1833618 5222875 := bstep (se 1 (by rfl) ⟨3917156, by rfl⟩ : syracuseStep 5222875 = 7834313) B7834313
theorem B5223035 : Blo 1833618 5223035 := bstep (se 1 (by rfl) ⟨3917276, by rfl⟩ : syracuseStep 5223035 = 7834553) B7834553
theorem B20378441 : Blo 1833618 20378441 := bstep (se 2 (by rfl) ⟨7641915, by rfl⟩ : syracuseStep 20378441 = 15283831) B15283831
theorem B5223275 : Blo 1833618 5223275 := bstep (se 1 (by rfl) ⟨3917456, by rfl⟩ : syracuseStep 5223275 = 7834913) B7834913
theorem B8819563 : Blo 1833618 8819563 := bstep (se 1 (by rfl) ⟨6614672, by rfl⟩ : syracuseStep 8819563 = 13229345) B13229345
theorem B11760491 : Blo 1833618 11760491 := bstep (se 1 (by rfl) ⟨8820368, by rfl⟩ : syracuseStep 11760491 = 17640737) B17640737
theorem B28234649 : Blo 1833618 28234649 := bstep (se 2 (by rfl) ⟨10587993, by rfl⟩ : syracuseStep 28234649 = 21175987) B21175987
theorem B22303745 : Blo 1833618 22303745 := bstep (se 2 (by rfl) ⟨8363904, by rfl⟩ : syracuseStep 22303745 = 16727809) B16727809
theorem B10056899 : Blo 1833618 10056899 := bstep (se 1 (by rfl) ⟨7542674, by rfl⟩ : syracuseStep 10056899 = 15085349) B15085349
theorem B16733387 : Blo 1833618 16733387 := bstep (se 1 (by rfl) ⟨12550040, by rfl⟩ : syracuseStep 16733387 = 25100081) B25100081
theorem B6190397 : Blo 1833618 6190397 := bstep (se 3 (by rfl) ⟨1160699, by rfl⟩ : syracuseStep 6190397 = 2321399) B2321399
theorem B6968663 : Blo 1833618 6968663 := bstep (se 1 (by rfl) ⟨5226497, by rfl⟩ : syracuseStep 6968663 = 10452995) B10452995
theorem B5223923 : Blo 1833618 5223923 := bstep (se 1 (by rfl) ⟨3917942, by rfl⟩ : syracuseStep 5223923 = 7835885) B7835885
theorem B3307027 : Blo 1833618 3307027 := bstep (se 1 (by rfl) ⟨2480270, by rfl⟩ : syracuseStep 3307027 = 4960541) B4960541
theorem B4126247 : Blo 1833618 4126247 := bstep (se 1 (by rfl) ⟨3094685, by rfl⟩ : syracuseStep 4126247 = 6189371) B6189371
theorem B4642343 : Blo 1833618 4642343 := bstep (se 1 (by rfl) ⟨3481757, by rfl⟩ : syracuseStep 4642343 = 6963515) B6963515
theorem B10450579 : Blo 1833618 10450579 := bstep (se 1 (by rfl) ⟨7837934, by rfl⟩ : syracuseStep 10450579 = 15675869) B15675869
theorem B7435961 : Blo 1833618 7435961 := bstep (se 2 (by rfl) ⟨2788485, by rfl⟩ : syracuseStep 7435961 = 5576971) B5576971
theorem B5224151 : Blo 1833618 5224151 := bstep (se 1 (by rfl) ⟨3918113, by rfl⟩ : syracuseStep 5224151 = 7836227) B7836227
theorem B19830521 : Blo 1833618 19830521 := bstep (se 2 (by rfl) ⟨7436445, by rfl⟩ : syracuseStep 19830521 = 14872891) B14872891
theorem B25106213 : Blo 1833618 25106213 := bstep (se 4 (by rfl) ⟨2353707, by rfl⟩ : syracuseStep 25106213 = 4707415) B4707415
theorem B15669035 : Blo 1833618 15669035 := bstep (se 1 (by rfl) ⟨11751776, by rfl⟩ : syracuseStep 15669035 = 23503553) B23503553
theorem B4126571 : Blo 1833618 4126571 := bstep (se 1 (by rfl) ⟨3094928, by rfl⟩ : syracuseStep 4126571 = 6189857) B6189857
theorem B4642667 : Blo 1833618 4642667 := bstep (se 1 (by rfl) ⟨3482000, by rfl⟩ : syracuseStep 4642667 = 6964001) B6964001
theorem B4126625 : Blo 1833618 4126625 := bstep (se 2 (by rfl) ⟨1547484, by rfl⟩ : syracuseStep 4126625 = 3094969) B3094969
theorem B3094537 : Blo 1833618 3094537 := bstep (se 2 (by rfl) ⟨1160451, by rfl⟩ : syracuseStep 3094537 = 2320903) B2320903
theorem B2750543 : Blo 1833618 2750543 := bstep (se 1 (by rfl) ⟨2062907, by rfl⟩ : syracuseStep 2750543 = 4125815) B4125815
theorem B6191261 : Blo 1833618 6191261 := bstep (se 3 (by rfl) ⟨1160861, by rfl⟩ : syracuseStep 6191261 = 2321723) B2321723
theorem B3094699 : Blo 1833618 3094699 := bstep (se 1 (by rfl) ⟨2321024, by rfl⟩ : syracuseStep 3094699 = 4642049) B4642049
theorem B2750663 : Blo 1833618 2750663 := bstep (se 1 (by rfl) ⟨2062997, by rfl⟩ : syracuseStep 2750663 = 4125995) B4125995
theorem B4126967 : Blo 1833618 4126967 := bstep (se 1 (by rfl) ⟨3095225, by rfl⟩ : syracuseStep 4126967 = 6190451) B6190451
theorem B3225847 : Blo 1833618 3225847 := bstep (se 1 (by rfl) ⟨2419385, by rfl⟩ : syracuseStep 3225847 = 4838771) B4838771
theorem B59513089 : Blo 1833618 59513089 := bstep (se 2 (by rfl) ⟨22317408, by rfl⟩ : syracuseStep 59513089 = 44634817) B44634817
theorem B15677783 : Blo 1833618 15677783 := bstep (se 1 (by rfl) ⟨11758337, by rfl⟩ : syracuseStep 15677783 = 23516675) B23516675
theorem B2750825 : Blo 1833618 2750825 := bstep (se 2 (by rfl) ⟨1031559, by rfl⟩ : syracuseStep 2750825 = 2063119) B2063119
theorem B2480491 : Blo 1833618 2480491 := bstep (se 1 (by rfl) ⟨1860368, by rfl⟩ : syracuseStep 2480491 = 3720737) B3720737
theorem B2750903 : Blo 1833618 2750903 := bstep (se 1 (by rfl) ⟨2063177, by rfl⟩ : syracuseStep 2750903 = 4126355) B4126355
theorem B2939323 : Blo 1833618 2939323 := bstep (se 1 (by rfl) ⟨2204492, by rfl⟩ : syracuseStep 2939323 = 4408985) B4408985
theorem B2750939 : Blo 1833618 2750939 := bstep (se 1 (by rfl) ⟨2063204, by rfl⟩ : syracuseStep 2750939 = 4126409) B4126409
theorem B3095003 : Blo 1833618 3095003 := bstep (se 1 (by rfl) ⟨2321252, by rfl⟩ : syracuseStep 3095003 = 4642505) B4642505
theorem B4643315 : Blo 1833618 4643315 := bstep (se 1 (by rfl) ⟨3482486, by rfl⟩ : syracuseStep 4643315 = 6964973) B6964973
theorem B10443289 : Blo 1833618 10443289 := bstep (se 2 (by rfl) ⟨3916233, by rfl⟩ : syracuseStep 10443289 = 7832467) B7832467
theorem B2939431 : Blo 1833618 2939431 := bstep (se 1 (by rfl) ⟨2204573, by rfl⟩ : syracuseStep 2939431 = 4409147) B4409147
theorem B2480719 : Blo 1833618 2480719 := bstep (se 1 (by rfl) ⟨1860539, by rfl⟩ : syracuseStep 2480719 = 3721079) B3721079
theorem B1833647 : Blo 1833618 1833647 := bstep (se 1 (by rfl) ⟨1375235, by rfl⟩ : syracuseStep 1833647 = 2750471) B2750471
theorem B6191801 : Blo 1833618 6191801 := bstep (se 2 (by rfl) ⟨2321925, by rfl⟩ : syracuseStep 6191801 = 4643851) B4643851
theorem B1833671 : Blo 1833618 1833671 := bstep (se 1 (by rfl) ⟨1375253, by rfl⟩ : syracuseStep 1833671 = 2750507) B2750507
theorem B2063047 : Blo 1833618 2063047 := bstep (se 1 (by rfl) ⟨1547285, by rfl⟩ : syracuseStep 2063047 = 3094571) B3094571
theorem B3095239 : Blo 1833618 3095239 := bstep (se 1 (by rfl) ⟨2321429, by rfl⟩ : syracuseStep 3095239 = 4642859) B4642859
theorem B4643527 : Blo 1833618 4643527 := bstep (se 1 (by rfl) ⟨3482645, by rfl⟩ : syracuseStep 4643527 = 6965291) B6965291
theorem B1833691 : Blo 1833618 1833691 := bstep (se 1 (by rfl) ⟨1375268, by rfl⟩ : syracuseStep 1833691 = 2750537) B2750537
theorem B45218549 : Blo 1833618 45218549 := bstep (se 5 (by rfl) ⟨2119619, by rfl⟩ : syracuseStep 45218549 = 4239239) B4239239
theorem B1833767 : Blo 1833618 1833767 := bstep (se 1 (by rfl) ⟨1375325, by rfl⟩ : syracuseStep 1833767 = 2750651) B2750651
theorem B4127561 : Blo 1833618 4127561 := bstep (se 2 (by rfl) ⟨1547835, by rfl⟩ : syracuseStep 4127561 = 3095671) B3095671
theorem B1833807 : Blo 1833618 1833807 := bstep (se 1 (by rfl) ⟨1375355, by rfl⟩ : syracuseStep 1833807 = 2750711) B2750711
theorem B1833823 : Blo 1833618 1833823 := bstep (se 1 (by rfl) ⟨1375367, by rfl⟩ : syracuseStep 1833823 = 2750735) B2750735
theorem B3095401 : Blo 1833618 3095401 := bstep (se 2 (by rfl) ⟨1160775, by rfl⟩ : syracuseStep 3095401 = 2321551) B2321551
theorem B1833851 : Blo 1833618 1833851 := bstep (se 1 (by rfl) ⟨1375388, by rfl⟩ : syracuseStep 1833851 = 2750777) B2750777
theorem B1833903 : Blo 1833618 1833903 := bstep (se 1 (by rfl) ⟨1375427, by rfl⟩ : syracuseStep 1833903 = 2750855) B2750855
theorem B2751407 : Blo 1833618 2751407 := bstep (se 1 (by rfl) ⟨2063555, by rfl⟩ : syracuseStep 2751407 = 4127111) B4127111
theorem B1833927 : Blo 1833618 1833927 := bstep (se 1 (by rfl) ⟨1375445, by rfl⟩ : syracuseStep 1833927 = 2750891) B2750891
theorem B1833947 : Blo 1833618 1833947 := bstep (se 1 (by rfl) ⟨1375460, by rfl⟩ : syracuseStep 1833947 = 2750921) B2750921
theorem B2751497 : Blo 1833618 2751497 := bstep (se 2 (by rfl) ⟨1031811, by rfl⟩ : syracuseStep 2751497 = 2063623) B2063623
theorem B1834023 : Blo 1833618 1834023 := bstep (se 1 (by rfl) ⟨1375517, by rfl⟩ : syracuseStep 1834023 = 2751035) B2751035
theorem B2751527 : Blo 1833618 2751527 := bstep (se 1 (by rfl) ⟨2063645, by rfl⟩ : syracuseStep 2751527 = 4127291) B4127291
theorem B52878379 : Blo 1833618 52878379 := bstep (se 1 (by rfl) ⟨39658784, by rfl⟩ : syracuseStep 52878379 = 79317569) B79317569
theorem B9288755 : Blo 1833618 9288755 := bstep (se 1 (by rfl) ⟨6966566, by rfl⟩ : syracuseStep 9288755 = 13933133) B13933133
theorem B13933619 : Blo 1833618 13933619 := bstep (se 1 (by rfl) ⟨10450214, by rfl⟩ : syracuseStep 13933619 = 20900429) B20900429
theorem B1834063 : Blo 1833618 1834063 := bstep (se 1 (by rfl) ⟨1375547, by rfl⟩ : syracuseStep 1834063 = 2751095) B2751095
theorem B1834079 : Blo 1833618 1834079 := bstep (se 1 (by rfl) ⟨1375559, by rfl⟩ : syracuseStep 1834079 = 2751119) B2751119
theorem B1834107 : Blo 1833618 1834107 := bstep (se 1 (by rfl) ⟨1375580, by rfl⟩ : syracuseStep 1834107 = 2751161) B2751161
theorem B2751611 : Blo 1833618 2751611 := bstep (se 1 (by rfl) ⟨2063708, by rfl⟩ : syracuseStep 2751611 = 4127417) B4127417
theorem B1834159 : Blo 1833618 1834159 := bstep (se 1 (by rfl) ⟨1375619, by rfl⟩ : syracuseStep 1834159 = 2751239) B2751239
theorem B1834183 : Blo 1833618 1834183 := bstep (se 1 (by rfl) ⟨1375637, by rfl⟩ : syracuseStep 1834183 = 2751275) B2751275
theorem B1834203 : Blo 1833618 1834203 := bstep (se 1 (by rfl) ⟨1375652, by rfl⟩ : syracuseStep 1834203 = 2751305) B2751305
theorem B2751737 : Blo 1833618 2751737 := bstep (se 2 (by rfl) ⟨1031901, by rfl⟩ : syracuseStep 2751737 = 2063803) B2063803
theorem B6192395 : Blo 1833618 6192395 := bstep (se 1 (by rfl) ⟨4644296, by rfl⟩ : syracuseStep 6192395 = 9288593) B9288593
theorem B11156759 : Blo 1833618 11156759 := bstep (se 1 (by rfl) ⟨8367569, by rfl⟩ : syracuseStep 11156759 = 16735139) B16735139
theorem B1834279 : Blo 1833618 1834279 := bstep (se 1 (by rfl) ⟨1375709, by rfl⟩ : syracuseStep 1834279 = 2751419) B2751419
theorem B1834319 : Blo 1833618 1834319 := bstep (se 1 (by rfl) ⟨1375739, by rfl⟩ : syracuseStep 1834319 = 2751479) B2751479
theorem B1834335 : Blo 1833618 1834335 := bstep (se 1 (by rfl) ⟨1375751, by rfl⟩ : syracuseStep 1834335 = 2751503) B2751503
theorem B2751839 : Blo 1833618 2751839 := bstep (se 1 (by rfl) ⟨2063879, by rfl⟩ : syracuseStep 2751839 = 4127759) B4127759
theorem B2751851 : Blo 1833618 2751851 := bstep (se 1 (by rfl) ⟨2063888, by rfl⟩ : syracuseStep 2751851 = 4127777) B4127777
theorem B1834363 : Blo 1833618 1834363 := bstep (se 1 (by rfl) ⟨1375772, by rfl⟩ : syracuseStep 1834363 = 2751545) B2751545
theorem B6962557 : Blo 1833618 6962557 := bstep (se 3 (by rfl) ⟨1305479, by rfl⟩ : syracuseStep 6962557 = 2610959) B2610959
theorem B15678845 : Blo 1833618 15678845 := bstep (se 3 (by rfl) ⟨2939783, by rfl⟩ : syracuseStep 15678845 = 5879567) B5879567
theorem B1834415 : Blo 1833618 1834415 := bstep (se 1 (by rfl) ⟨1375811, by rfl⟩ : syracuseStep 1834415 = 2751623) B2751623
theorem B3095995 : Blo 1833618 3095995 := bstep (se 1 (by rfl) ⟨2321996, by rfl⟩ : syracuseStep 3095995 = 4643993) B4643993
theorem B1834439 : Blo 1833618 1834439 := bstep (se 1 (by rfl) ⟨1375829, by rfl⟩ : syracuseStep 1834439 = 2751659) B2751659
theorem B3481051 : Blo 1833618 3481051 := bstep (se 1 (by rfl) ⟨2610788, by rfl⟩ : syracuseStep 3481051 = 5221577) B5221577
theorem B1834459 : Blo 1833618 1834459 := bstep (se 1 (by rfl) ⟨1375844, by rfl⟩ : syracuseStep 1834459 = 2751689) B2751689
theorem B6192665 : Blo 1833618 6192665 := bstep (se 2 (by rfl) ⟨2322249, by rfl⟩ : syracuseStep 6192665 = 4644499) B4644499
theorem B3481127 : Blo 1833618 3481127 := bstep (se 1 (by rfl) ⟨2610845, by rfl⟩ : syracuseStep 3481127 = 5221691) B5221691
theorem B1834535 : Blo 1833618 1834535 := bstep (se 1 (by rfl) ⟨1375901, by rfl⟩ : syracuseStep 1834535 = 2751803) B2751803
theorem B2063911 : Blo 1833618 2063911 := bstep (se 1 (by rfl) ⟨1547933, by rfl⟩ : syracuseStep 2063911 = 3095867) B3095867
theorem B3096103 : Blo 1833618 3096103 := bstep (se 1 (by rfl) ⟨2322077, by rfl⟩ : syracuseStep 3096103 = 4644155) B4644155
theorem B1834575 : Blo 1833618 1834575 := bstep (se 1 (by rfl) ⟨1375931, by rfl⟩ : syracuseStep 1834575 = 2751863) B2751863
theorem B2752079 : Blo 1833618 2752079 := bstep (se 1 (by rfl) ⟨2064059, by rfl⟩ : syracuseStep 2752079 = 4128119) B4128119
theorem B26435159 : Blo 1833618 26435159 := bstep (se 1 (by rfl) ⟨19826369, by rfl⟩ : syracuseStep 26435159 = 39652739) B39652739
theorem B29752919 : Blo 1833618 29752919 := bstep (se 1 (by rfl) ⟨22314689, by rfl⟩ : syracuseStep 29752919 = 44629379) B44629379
theorem B1834591 : Blo 1833618 1834591 := bstep (se 1 (by rfl) ⟨1375943, by rfl⟩ : syracuseStep 1834591 = 2751887) B2751887
theorem B4128353 : Blo 1833618 4128353 := bstep (se 2 (by rfl) ⟨1548132, by rfl⟩ : syracuseStep 4128353 = 3096265) B3096265
theorem B4644449 : Blo 1833618 4644449 := bstep (se 2 (by rfl) ⟨1741668, by rfl⟩ : syracuseStep 4644449 = 3483337) B3483337
theorem B3481211 : Blo 1833618 3481211 := bstep (se 1 (by rfl) ⟨2610908, by rfl⟩ : syracuseStep 3481211 = 5221817) B5221817
theorem B1834619 : Blo 1833618 1834619 := bstep (se 1 (by rfl) ⟨1375964, by rfl⟩ : syracuseStep 1834619 = 2751929) B2751929
theorem B3145387 : Blo 1833618 3145387 := bstep (se 1 (by rfl) ⟨2359040, by rfl⟩ : syracuseStep 3145387 = 4718081) B4718081
theorem B1834671 : Blo 1833618 1834671 := bstep (se 1 (by rfl) ⟨1376003, by rfl⟩ : syracuseStep 1834671 = 2752007) B2752007
theorem B3718855 : Blo 1833618 3718855 := bstep (se 1 (by rfl) ⟨2789141, by rfl⟩ : syracuseStep 3718855 = 5578283) B5578283
theorem B1834695 : Blo 1833618 1834695 := bstep (se 1 (by rfl) ⟨1376021, by rfl⟩ : syracuseStep 1834695 = 2752043) B2752043
theorem B2752199 : Blo 1833618 2752199 := bstep (se 1 (by rfl) ⟨2064149, by rfl⟩ : syracuseStep 2752199 = 4128299) B4128299
theorem B1834715 : Blo 1833618 1834715 := bstep (se 1 (by rfl) ⟨1376036, by rfl⟩ : syracuseStep 1834715 = 2752073) B2752073
theorem B1834791 : Blo 1833618 1834791 := bstep (se 1 (by rfl) ⟨1376093, by rfl⟩ : syracuseStep 1834791 = 2752187) B2752187
theorem B1834831 : Blo 1833618 1834831 := bstep (se 1 (by rfl) ⟨1376123, by rfl⟩ : syracuseStep 1834831 = 2752247) B2752247
theorem B1834847 : Blo 1833618 1834847 := bstep (se 1 (by rfl) ⟨1376135, by rfl⟩ : syracuseStep 1834847 = 2752271) B2752271
theorem B2752361 : Blo 1833618 2752361 := bstep (se 2 (by rfl) ⟨1032135, by rfl⟩ : syracuseStep 2752361 = 2064271) B2064271
theorem B3096427 : Blo 1833618 3096427 := bstep (se 1 (by rfl) ⟨2322320, by rfl⟩ : syracuseStep 3096427 = 4644641) B4644641
theorem B1834875 : Blo 1833618 1834875 := bstep (se 1 (by rfl) ⟨1376156, by rfl⟩ : syracuseStep 1834875 = 2752313) B2752313
theorem B4407215 : Blo 1833618 4407215 := bstep (se 1 (by rfl) ⟨3305411, by rfl⟩ : syracuseStep 4407215 = 6610823) B6610823
theorem B1834927 : Blo 1833618 1834927 := bstep (se 1 (by rfl) ⟨1376195, by rfl⟩ : syracuseStep 1834927 = 2752391) B2752391
theorem B2752439 : Blo 1833618 2752439 := bstep (se 1 (by rfl) ⟨2064329, by rfl⟩ : syracuseStep 2752439 = 4128659) B4128659
theorem B13926329 : Blo 1833618 13926329 := bstep (se 2 (by rfl) ⟨5222373, by rfl⟩ : syracuseStep 13926329 = 10444747) B10444747
theorem B4128695 : Blo 1833618 4128695 := bstep (se 1 (by rfl) ⟨3096521, by rfl⟩ : syracuseStep 4128695 = 6193043) B6193043
theorem B1834951 : Blo 1833618 1834951 := bstep (se 1 (by rfl) ⟨1376213, by rfl⟩ : syracuseStep 1834951 = 2752427) B2752427
theorem B1834971 : Blo 1833618 1834971 := bstep (se 1 (by rfl) ⟨1376228, by rfl⟩ : syracuseStep 1834971 = 2752457) B2752457
theorem B2752475 : Blo 1833618 2752475 := bstep (se 1 (by rfl) ⟨2064356, by rfl⟩ : syracuseStep 2752475 = 4128713) B4128713
theorem B5578963 : Blo 1833618 5578963 := bstep (se 1 (by rfl) ⟨4184222, by rfl⟩ : syracuseStep 5578963 = 8368445) B8368445
theorem B17637587 : Blo 1833618 17637587 := bstep (se 1 (by rfl) ⟨13228190, by rfl⟩ : syracuseStep 17637587 = 26456381) B26456381
theorem B1835295 : Blo 1833618 1835295 := bstep (se 1 (by rfl) ⟨1376471, by rfl⟩ : syracuseStep 1835295 = 2752943) B2752943
theorem B6963529 : Blo 1833618 6963529 := bstep (se 2 (by rfl) ⟨2611323, by rfl⟩ : syracuseStep 6963529 = 5222647) B5222647
theorem B75342149 : Blo 1833618 75342149 := bstep (se 4 (by rfl) ⟨7063326, by rfl⟩ : syracuseStep 75342149 = 14126653) B14126653
theorem B2752859 : Blo 1833618 2752859 := bstep (se 1 (by rfl) ⟨2064644, by rfl⟩ : syracuseStep 2752859 = 4129289) B4129289
theorem B1835355 : Blo 1833618 1835355 := bstep (se 1 (by rfl) ⟨1376516, by rfl⟩ : syracuseStep 1835355 = 2753033) B2753033
theorem B1835375 : Blo 1833618 1835375 := bstep (se 1 (by rfl) ⟨1376531, by rfl⟩ : syracuseStep 1835375 = 2753063) B2753063
theorem B3482023 : Blo 1833618 3482023 := bstep (se 1 (by rfl) ⟨2611517, by rfl⟩ : syracuseStep 3482023 = 5223035) B5223035
theorem B1835431 : Blo 1833618 1835431 := bstep (se 1 (by rfl) ⟨1376573, by rfl⟩ : syracuseStep 1835431 = 2753147) B2753147
theorem B6193583 : Blo 1833618 6193583 := bstep (se 1 (by rfl) ⟨4645187, by rfl⟩ : syracuseStep 6193583 = 9290375) B9290375
theorem B4129199 : Blo 1833618 4129199 := bstep (se 1 (by rfl) ⟨3096899, by rfl⟩ : syracuseStep 4129199 = 6193799) B6193799
theorem B4129235 : Blo 1833618 4129235 := bstep (se 1 (by rfl) ⟨3096926, by rfl⟩ : syracuseStep 4129235 = 6193853) B6193853
theorem B1835515 : Blo 1833618 1835515 := bstep (se 1 (by rfl) ⟨1376636, by rfl⟩ : syracuseStep 1835515 = 2753273) B2753273
theorem B4129343 : Blo 1833618 4129343 := bstep (se 1 (by rfl) ⟨3097007, by rfl⟩ : syracuseStep 4129343 = 6194015) B6194015
theorem B2753087 : Blo 1833618 2753087 := bstep (se 1 (by rfl) ⟨2064815, by rfl⟩ : syracuseStep 2753087 = 4129631) B4129631
theorem B1835583 : Blo 1833618 1835583 := bstep (se 1 (by rfl) ⟨1376687, by rfl⟩ : syracuseStep 1835583 = 2753375) B2753375
theorem B3482183 : Blo 1833618 3482183 := bstep (se 1 (by rfl) ⟨2611637, by rfl⟩ : syracuseStep 3482183 = 5223275) B5223275
theorem B7840327 : Blo 1833618 7840327 := bstep (se 1 (by rfl) ⟨5880245, by rfl⟩ : syracuseStep 7840327 = 11760491) B11760491
theorem B1835591 : Blo 1833618 1835591 := bstep (se 1 (by rfl) ⟨1376693, by rfl⟩ : syracuseStep 1835591 = 2753387) B2753387
theorem B2064991 : Blo 1833618 2064991 := bstep (se 1 (by rfl) ⟨1548743, by rfl⟩ : syracuseStep 2064991 = 3097487) B3097487
theorem B6963833 : Blo 1833618 6963833 := bstep (se 2 (by rfl) ⟨2611437, by rfl⟩ : syracuseStep 6963833 = 5222875) B5222875
theorem B14869163 : Blo 1833618 14869163 := bstep (se 1 (by rfl) ⟨11151872, by rfl⟩ : syracuseStep 14869163 = 22303745) B22303745
theorem B4129451 : Blo 1833618 4129451 := bstep (se 1 (by rfl) ⟨3097088, by rfl⟩ : syracuseStep 4129451 = 6194177) B6194177
theorem B3097271 : Blo 1833618 3097271 := bstep (se 1 (by rfl) ⟨2322953, by rfl⟩ : syracuseStep 3097271 = 4645907) B4645907
theorem B2753207 : Blo 1833618 2753207 := bstep (se 1 (by rfl) ⟨2064905, by rfl⟩ : syracuseStep 2753207 = 4129811) B4129811
theorem B4645775 : Blo 1833618 4645775 := bstep (se 1 (by rfl) ⟨3484331, by rfl⟩ : syracuseStep 4645775 = 6968663) B6968663
theorem B3482615 : Blo 1833618 3482615 := bstep (se 1 (by rfl) ⟨2611961, by rfl⟩ : syracuseStep 3482615 = 5223923) B5223923
theorem B19833893 : Blo 1833618 19833893 := bstep (se 4 (by rfl) ⟨1859427, by rfl⟩ : syracuseStep 19833893 = 3718855) B3718855
theorem B4957307 : Blo 1833618 4957307 := bstep (se 1 (by rfl) ⟨3717980, by rfl⟩ : syracuseStep 4957307 = 7435961) B7435961
theorem B3482767 : Blo 1833618 3482767 := bstep (se 1 (by rfl) ⟨2612075, by rfl⟩ : syracuseStep 3482767 = 5224151) B5224151
theorem B10446023 : Blo 1833618 10446023 := bstep (se 1 (by rfl) ⟨7834517, by rfl⟩ : syracuseStep 10446023 = 15669035) B15669035
theorem B4129991 : Blo 1833618 4129991 := bstep (se 1 (by rfl) ⟨3097493, by rfl⟩ : syracuseStep 4129991 = 6194987) B6194987
theorem B75302237 : Blo 1833618 75302237 := bstep (se 3 (by rfl) ⟨14119169, by rfl⟩ : syracuseStep 75302237 = 28238339) B28238339
theorem B6194555 : Blo 1833618 6194555 := bstep (se 1 (by rfl) ⟨4645916, by rfl⟩ : syracuseStep 6194555 = 9291833) B9291833
theorem B4646281 : Blo 1833618 4646281 := bstep (se 2 (by rfl) ⟨1742355, by rfl⟩ : syracuseStep 4646281 = 3484711) B3484711
theorem B4646393 : Blo 1833618 4646393 := bstep (se 2 (by rfl) ⟨1742397, by rfl⟩ : syracuseStep 4646393 = 3484795) B3484795
theorem B19842893 : Blo 1833618 19842893 := bstep (se 3 (by rfl) ⟨3720542, by rfl⟩ : syracuseStep 19842893 = 7441085) B7441085
theorem B9283409 : Blo 1833618 9283409 := bstep (se 2 (by rfl) ⟨3481278, by rfl⟩ : syracuseStep 9283409 = 6962557) B6962557
theorem B13928273 : Blo 1833618 13928273 := bstep (se 2 (by rfl) ⟨5223102, by rfl⟩ : syracuseStep 13928273 = 10446205) B10446205
theorem B4409369 : Blo 1833618 4409369 := bstep (se 2 (by rfl) ⟨1653513, by rfl⟩ : syracuseStep 4409369 = 3307027) B3307027
theorem B15665345 : Blo 1833618 15665345 := bstep (se 2 (by rfl) ⟨5874504, by rfl⟩ : syracuseStep 15665345 = 11749009) B11749009
theorem B2320751 : Blo 1833618 2320751 := bstep (se 1 (by rfl) ⟨1740563, by rfl⟩ : syracuseStep 2320751 = 3481127) B3481127
theorem B14125423 : Blo 1833618 14125423 := bstep (se 1 (by rfl) ⟨10594067, by rfl⟩ : syracuseStep 14125423 = 21188135) B21188135
theorem B9292157 : Blo 1833618 9292157 := bstep (se 3 (by rfl) ⟨1742279, by rfl⟩ : syracuseStep 9292157 = 3484559) B3484559
theorem B17623439 : Blo 1833618 17623439 := bstep (se 1 (by rfl) ⟨13217579, by rfl⟩ : syracuseStep 17623439 = 26435159) B26435159
theorem B19835279 : Blo 1833618 19835279 := bstep (se 1 (by rfl) ⟨14876459, by rfl⟩ : syracuseStep 19835279 = 29752919) B29752919
theorem B2320807 : Blo 1833618 2320807 := bstep (se 1 (by rfl) ⟨1740605, by rfl⟩ : syracuseStep 2320807 = 3481211) B3481211
theorem B5294503 : Blo 1833618 5294503 := bstep (se 1 (by rfl) ⟨3970877, by rfl⟩ : syracuseStep 5294503 = 7941755) B7941755
theorem B18827687 : Blo 1833618 18827687 := bstep (se 1 (by rfl) ⟨14120765, by rfl⟩ : syracuseStep 18827687 = 28241531) B28241531
theorem B9284219 : Blo 1833618 9284219 := bstep (se 1 (by rfl) ⟨6963164, by rfl⟩ : syracuseStep 9284219 = 13926329) B13926329
theorem B17877677 : Blo 1833618 17877677 := bstep (se 3 (by rfl) ⟨3352064, by rfl⟩ : syracuseStep 17877677 = 6704129) B6704129
theorem B2321131 : Blo 1833618 2321131 := bstep (se 1 (by rfl) ⟨1740848, by rfl⟩ : syracuseStep 2321131 = 3481697) B3481697
theorem B6613751 : Blo 1833618 6613751 := bstep (se 1 (by rfl) ⟨4960313, by rfl⟩ : syracuseStep 6613751 = 9920627) B9920627
theorem B17623939 : Blo 1833618 17623939 := bstep (se 1 (by rfl) ⟨13217954, by rfl⟩ : syracuseStep 17623939 = 26435909) B26435909
theorem B79350785 : Blo 1833618 79350785 := bstep (se 2 (by rfl) ⟨29756544, by rfl⟩ : syracuseStep 79350785 = 59513089) B59513089
theorem B36236459 : Blo 1833618 36236459 := bstep (se 1 (by rfl) ⟨27177344, by rfl⟩ : syracuseStep 36236459 = 54354689) B54354689
theorem B13585627 : Blo 1833618 13585627 := bstep (se 1 (by rfl) ⟨10189220, by rfl⟩ : syracuseStep 13585627 = 20378441) B20378441
theorem B3919097 : Blo 1833618 3919097 := bstep (se 2 (by rfl) ⟨1469661, by rfl⟩ : syracuseStep 3919097 = 2939323) B2939323
theorem B10448189 : Blo 1833618 10448189 := bstep (se 3 (by rfl) ⟨1959035, by rfl⟩ : syracuseStep 10448189 = 3918071) B3918071
theorem B3919241 : Blo 1833618 3919241 := bstep (se 2 (by rfl) ⟨1469715, by rfl⟩ : syracuseStep 3919241 = 2939431) B2939431
theorem B2322103 : Blo 1833618 2322103 := bstep (se 1 (by rfl) ⟨1741577, by rfl⟩ : syracuseStep 2322103 = 3483155) B3483155
theorem B90492709 : Blo 1833618 90492709 := bstep (se 4 (by rfl) ⟨8483691, by rfl⟩ : syracuseStep 90492709 = 16967383) B16967383
theorem B13938479 : Blo 1833618 13938479 := bstep (se 1 (by rfl) ⟨10453859, by rfl⟩ : syracuseStep 13938479 = 20907719) B20907719
theorem B11759417 : Blo 1833618 11759417 := bstep (se 2 (by rfl) ⟨4409781, by rfl⟩ : syracuseStep 11759417 = 8819563) B8819563
theorem B5877785 : Blo 1833618 5877785 := bstep (se 2 (by rfl) ⟨2204169, by rfl⟩ : syracuseStep 5877785 = 4408339) B4408339
theorem B70504505 : Blo 1833618 70504505 := bstep (se 2 (by rfl) ⟨26439189, by rfl⟩ : syracuseStep 70504505 = 52878379) B52878379
theorem B6189587 : Blo 1833618 6189587 := bstep (se 1 (by rfl) ⟨4642190, by rfl⟩ : syracuseStep 6189587 = 9284381) B9284381
theorem B9286163 : Blo 1833618 9286163 := bstep (se 1 (by rfl) ⟨6964622, by rfl⟩ : syracuseStep 9286163 = 13929245) B13929245
theorem B4641401 : Blo 1833618 4641401 := bstep (se 2 (by rfl) ⟨1740525, by rfl⟩ : syracuseStep 4641401 = 3481051) B3481051
theorem B66949901 : Blo 1833618 66949901 := bstep (se 3 (by rfl) ⟨12553106, by rfl⟩ : syracuseStep 66949901 = 25106213) B25106213
theorem B4301129 : Blo 1833618 4301129 := bstep (se 2 (by rfl) ⟨1612923, by rfl⟩ : syracuseStep 4301129 = 3225847) B3225847
theorem B5878747 : Blo 1833618 5878747 := bstep (se 1 (by rfl) ⟨4409060, by rfl⟩ : syracuseStep 5878747 = 8818121) B8818121
theorem B16741349 : Blo 1833618 16741349 := bstep (se 4 (by rfl) ⟨1569501, by rfl⟩ : syracuseStep 16741349 = 3139003) B3139003
theorem B4125671 : Blo 1833618 4125671 := bstep (se 1 (by rfl) ⟨3094253, by rfl⟩ : syracuseStep 4125671 = 6188507) B6188507
theorem B5878759 : Blo 1833618 5878759 := bstep (se 1 (by rfl) ⟨4409069, by rfl⟩ : syracuseStep 5878759 = 8818139) B8818139
theorem B42931289 : Blo 1833618 42931289 := bstep (se 2 (by rfl) ⟨16099233, by rfl⟩ : syracuseStep 42931289 = 32198467) B32198467
theorem B11752573 : Blo 1833618 11752573 := bstep (se 3 (by rfl) ⟨2203607, by rfl⟩ : syracuseStep 11752573 = 4407215) B4407215
theorem B7541885 : Blo 1833618 7541885 := bstep (se 3 (by rfl) ⟨1414103, by rfl⟩ : syracuseStep 7541885 = 2828207) B2828207
theorem B4126049 : Blo 1833618 4126049 := bstep (se 2 (by rfl) ⟨1547268, by rfl⟩ : syracuseStep 4126049 = 3094537) B3094537
theorem B4126139 : Blo 1833618 4126139 := bstep (se 1 (by rfl) ⟨3094604, by rfl⟩ : syracuseStep 4126139 = 6189209) B6189209
theorem B4126265 : Blo 1833618 4126265 := bstep (se 2 (by rfl) ⟨1547349, by rfl⟩ : syracuseStep 4126265 = 3094699) B3094699
theorem B3307321 : Blo 1833618 3307321 := bstep (se 2 (by rfl) ⟨1240245, by rfl⟩ : syracuseStep 3307321 = 2480491) B2480491
theorem B26818397 : Blo 1833618 26818397 := bstep (se 3 (by rfl) ⟨5028449, by rfl⟩ : syracuseStep 26818397 = 10056899) B10056899
theorem B18823099 : Blo 1833618 18823099 := bstep (se 1 (by rfl) ⟨14117324, by rfl⟩ : syracuseStep 18823099 = 28234649) B28234649
theorem B13924385 : Blo 1833618 13924385 := bstep (se 2 (by rfl) ⟨5221644, by rfl⟩ : syracuseStep 13924385 = 10443289) B10443289
theorem B3307625 : Blo 1833618 3307625 := bstep (se 2 (by rfl) ⟨1240359, by rfl⟩ : syracuseStep 3307625 = 2480719) B2480719
theorem B11155591 : Blo 1833618 11155591 := bstep (se 1 (by rfl) ⟨8366693, by rfl⟩ : syracuseStep 11155591 = 16733387) B16733387
theorem B4126931 : Blo 1833618 4126931 := bstep (se 1 (by rfl) ⟨3095198, by rfl⟩ : syracuseStep 4126931 = 6190397) B6190397
theorem B2750729 : Blo 1833618 2750729 := bstep (se 2 (by rfl) ⟨1031523, by rfl⟩ : syracuseStep 2750729 = 2063047) B2063047
theorem B4126985 : Blo 1833618 4126985 := bstep (se 2 (by rfl) ⟨1547619, by rfl⟩ : syracuseStep 4126985 = 3095239) B3095239
theorem B6191369 : Blo 1833618 6191369 := bstep (se 2 (by rfl) ⟨2321763, by rfl⟩ : syracuseStep 6191369 = 4643527) B4643527
theorem B9287945 : Blo 1833618 9287945 := bstep (se 2 (by rfl) ⟨3482979, by rfl⟩ : syracuseStep 9287945 = 6965959) B6965959
theorem B2750831 : Blo 1833618 2750831 := bstep (se 1 (by rfl) ⟨2063123, by rfl⟩ : syracuseStep 2750831 = 4126247) B4126247
theorem B3094895 : Blo 1833618 3094895 := bstep (se 1 (by rfl) ⟨2321171, by rfl⟩ : syracuseStep 3094895 = 4642343) B4642343
theorem B4643183 : Blo 1833618 4643183 := bstep (se 1 (by rfl) ⟨3482387, by rfl⟩ : syracuseStep 4643183 = 6964775) B6964775
theorem B2939303 : Blo 1833618 2939303 := bstep (se 1 (by rfl) ⟨2204477, by rfl⟩ : syracuseStep 2939303 = 4408955) B4408955
theorem B4127201 : Blo 1833618 4127201 := bstep (se 2 (by rfl) ⟨1547700, by rfl⟩ : syracuseStep 4127201 = 3095401) B3095401
theorem B13220347 : Blo 1833618 13220347 := bstep (se 1 (by rfl) ⟨9915260, by rfl⟩ : syracuseStep 13220347 = 19830521) B19830521
theorem B2751047 : Blo 1833618 2751047 := bstep (se 1 (by rfl) ⟨2063285, by rfl⟩ : syracuseStep 2751047 = 4126571) B4126571
theorem B3095111 : Blo 1833618 3095111 := bstep (se 1 (by rfl) ⟨2321333, by rfl⟩ : syracuseStep 3095111 = 4642667) B4642667
theorem B2513479 : Blo 1833618 2513479 := bstep (se 1 (by rfl) ⟨1885109, by rfl⟩ : syracuseStep 2513479 = 3770219) B3770219
theorem B2751083 : Blo 1833618 2751083 := bstep (se 1 (by rfl) ⟨2063312, by rfl⟩ : syracuseStep 2751083 = 4126625) B4126625
theorem B1833695 : Blo 1833618 1833695 := bstep (se 1 (by rfl) ⟨1375271, by rfl⟩ : syracuseStep 1833695 = 2750543) B2750543
theorem B4127507 : Blo 1833618 4127507 := bstep (se 1 (by rfl) ⟨3095630, by rfl⟩ : syracuseStep 4127507 = 6191261) B6191261
theorem B1833775 : Blo 1833618 1833775 := bstep (se 1 (by rfl) ⟨1375331, by rfl⟩ : syracuseStep 1833775 = 2750663) B2750663
theorem B2751311 : Blo 1833618 2751311 := bstep (se 1 (by rfl) ⟨2063483, by rfl⟩ : syracuseStep 2751311 = 4126967) B4126967
theorem B10451855 : Blo 1833618 10451855 := bstep (se 1 (by rfl) ⟨7838891, by rfl⟩ : syracuseStep 10451855 = 15677783) B15677783
theorem B1833883 : Blo 1833618 1833883 := bstep (se 1 (by rfl) ⟨1375412, by rfl⟩ : syracuseStep 1833883 = 2750825) B2750825
theorem B1833935 : Blo 1833618 1833935 := bstep (se 1 (by rfl) ⟨1375451, by rfl⟩ : syracuseStep 1833935 = 2750903) B2750903
theorem B1833959 : Blo 1833618 1833959 := bstep (se 1 (by rfl) ⟨1375469, by rfl⟩ : syracuseStep 1833959 = 2750939) B2750939
theorem B2063335 : Blo 1833618 2063335 := bstep (se 1 (by rfl) ⟨1547501, by rfl⟩ : syracuseStep 2063335 = 3095003) B3095003
theorem B3095543 : Blo 1833618 3095543 := bstep (se 1 (by rfl) ⟨2321657, by rfl⟩ : syracuseStep 3095543 = 4643315) B4643315
theorem B4643831 : Blo 1833618 4643831 := bstep (se 1 (by rfl) ⟨3482873, by rfl⟩ : syracuseStep 4643831 = 6965747) B6965747
theorem B4127867 : Blo 1833618 4127867 := bstep (se 1 (by rfl) ⟨3095900, by rfl⟩ : syracuseStep 4127867 = 6191801) B6191801
theorem B4643963 : Blo 1833618 4643963 := bstep (se 1 (by rfl) ⟨3482972, by rfl⟩ : syracuseStep 4643963 = 6965945) B6965945
theorem B30145699 : Blo 1833618 30145699 := bstep (se 1 (by rfl) ⟨22609274, by rfl⟩ : syracuseStep 30145699 = 45218549) B45218549
theorem B20888765 : Blo 1833618 20888765 := bstep (se 3 (by rfl) ⟨3916643, by rfl⟩ : syracuseStep 20888765 = 7833287) B7833287
theorem B2751707 : Blo 1833618 2751707 := bstep (se 1 (by rfl) ⟨2063780, by rfl⟩ : syracuseStep 2751707 = 4127561) B4127561
theorem B3136745 : Blo 1833618 3136745 := bstep (se 2 (by rfl) ⟨1176279, by rfl⟩ : syracuseStep 3136745 = 2352559) B2352559
theorem B4127993 : Blo 1833618 4127993 := bstep (se 2 (by rfl) ⟨1547997, by rfl⟩ : syracuseStep 4127993 = 3095995) B3095995
theorem B1834271 : Blo 1833618 1834271 := bstep (se 1 (by rfl) ⟨1375703, by rfl⟩ : syracuseStep 1834271 = 2751407) B2751407
theorem B1834331 : Blo 1833618 1834331 := bstep (se 1 (by rfl) ⟨1375748, by rfl⟩ : syracuseStep 1834331 = 2751497) B2751497
theorem B1834351 : Blo 1833618 1834351 := bstep (se 1 (by rfl) ⟨1375763, by rfl⟩ : syracuseStep 1834351 = 2751527) B2751527
theorem B6192503 : Blo 1833618 6192503 := bstep (se 1 (by rfl) ⟨4644377, by rfl⟩ : syracuseStep 6192503 = 9288755) B9288755
theorem B9289079 : Blo 1833618 9289079 := bstep (se 1 (by rfl) ⟨6966809, by rfl⟩ : syracuseStep 9289079 = 13933619) B13933619
theorem B2751881 : Blo 1833618 2751881 := bstep (se 2 (by rfl) ⟨1031955, by rfl⟩ : syracuseStep 2751881 = 2063911) B2063911
theorem B4128137 : Blo 1833618 4128137 := bstep (se 2 (by rfl) ⟨1548051, by rfl⟩ : syracuseStep 4128137 = 3096103) B3096103
theorem B1834407 : Blo 1833618 1834407 := bstep (se 1 (by rfl) ⟨1375805, by rfl⟩ : syracuseStep 1834407 = 2751611) B2751611
theorem B10444247 : Blo 1833618 10444247 := bstep (se 1 (by rfl) ⟨7833185, by rfl⟩ : syracuseStep 10444247 = 15666371) B15666371
theorem B1834491 : Blo 1833618 1834491 := bstep (se 1 (by rfl) ⟨1375868, by rfl⟩ : syracuseStep 1834491 = 2751737) B2751737
theorem B4128263 : Blo 1833618 4128263 := bstep (se 1 (by rfl) ⟨3096197, by rfl⟩ : syracuseStep 4128263 = 6192395) B6192395
theorem B7437839 : Blo 1833618 7437839 := bstep (se 1 (by rfl) ⟨5578379, by rfl⟩ : syracuseStep 7437839 = 11156759) B11156759
theorem B9289241 : Blo 1833618 9289241 := bstep (se 2 (by rfl) ⟨3483465, by rfl⟩ : syracuseStep 9289241 = 6966931) B6966931
theorem B13934105 : Blo 1833618 13934105 := bstep (se 2 (by rfl) ⟨5225289, by rfl⟩ : syracuseStep 13934105 = 10450579) B10450579
theorem B4193849 : Blo 1833618 4193849 := bstep (se 2 (by rfl) ⟨1572693, by rfl⟩ : syracuseStep 4193849 = 3145387) B3145387
theorem B1834559 : Blo 1833618 1834559 := bstep (se 1 (by rfl) ⟨1375919, by rfl⟩ : syracuseStep 1834559 = 2751839) B2751839
theorem B1834567 : Blo 1833618 1834567 := bstep (se 1 (by rfl) ⟨1375925, by rfl⟩ : syracuseStep 1834567 = 2751851) B2751851
theorem B10452563 : Blo 1833618 10452563 := bstep (se 1 (by rfl) ⟨7839422, by rfl⟩ : syracuseStep 10452563 = 15678845) B15678845
theorem B4128443 : Blo 1833618 4128443 := bstep (se 1 (by rfl) ⟨3096332, by rfl⟩ : syracuseStep 4128443 = 6192665) B6192665
theorem B1834719 : Blo 1833618 1834719 := bstep (se 1 (by rfl) ⟨1376039, by rfl⟩ : syracuseStep 1834719 = 2752079) B2752079
theorem B2752235 : Blo 1833618 2752235 := bstep (se 1 (by rfl) ⟨2064176, by rfl⟩ : syracuseStep 2752235 = 4128353) B4128353
theorem B3096299 : Blo 1833618 3096299 := bstep (se 1 (by rfl) ⟨2322224, by rfl⟩ : syracuseStep 3096299 = 4644449) B4644449
theorem B1834799 : Blo 1833618 1834799 := bstep (se 1 (by rfl) ⟨1376099, by rfl⟩ : syracuseStep 1834799 = 2752199) B2752199
theorem B4128569 : Blo 1833618 4128569 := bstep (se 2 (by rfl) ⟨1548213, by rfl⟩ : syracuseStep 4128569 = 3096427) B3096427
theorem B1834907 : Blo 1833618 1834907 := bstep (se 1 (by rfl) ⟨1376180, by rfl⟩ : syracuseStep 1834907 = 2752361) B2752361
theorem B1834959 : Blo 1833618 1834959 := bstep (se 1 (by rfl) ⟨1376219, by rfl⟩ : syracuseStep 1834959 = 2752439) B2752439
theorem B2752463 : Blo 1833618 2752463 := bstep (se 1 (by rfl) ⟨2064347, by rfl⟩ : syracuseStep 2752463 = 4128695) B4128695
theorem B1834983 : Blo 1833618 1834983 := bstep (se 1 (by rfl) ⟨1376237, by rfl⟩ : syracuseStep 1834983 = 2752475) B2752475
theorem B2867419 : Blo 1833618 2867419 := bstep (se 1 (by rfl) ⟨2150564, by rfl⟩ : syracuseStep 2867419 = 4301129) B4301129
theorem B1835239 : Blo 1833618 1835239 := bstep (se 1 (by rfl) ⟨1376429, by rfl⟩ : syracuseStep 1835239 = 2752859) B2752859
theorem B4129055 : Blo 1833618 4129055 := bstep (se 1 (by rfl) ⟨3096791, by rfl⟩ : syracuseStep 4129055 = 6193583) B6193583
theorem B2752799 : Blo 1833618 2752799 := bstep (se 1 (by rfl) ⟨2064599, by rfl⟩ : syracuseStep 2752799 = 4129199) B4129199
theorem B2752823 : Blo 1833618 2752823 := bstep (se 1 (by rfl) ⟨2064617, by rfl⟩ : syracuseStep 2752823 = 4129235) B4129235
theorem B2752895 : Blo 1833618 2752895 := bstep (se 1 (by rfl) ⟨2064671, by rfl⟩ : syracuseStep 2752895 = 4129343) B4129343
theorem B1835391 : Blo 1833618 1835391 := bstep (se 1 (by rfl) ⟨1376543, by rfl⟩ : syracuseStep 1835391 = 2753087) B2753087
theorem B9912775 : Blo 1833618 9912775 := bstep (se 1 (by rfl) ⟨7434581, by rfl⟩ : syracuseStep 9912775 = 14869163) B14869163
theorem B2752967 : Blo 1833618 2752967 := bstep (se 1 (by rfl) ⟨2064725, by rfl⟩ : syracuseStep 2752967 = 4129451) B4129451
theorem B2064847 : Blo 1833618 2064847 := bstep (se 1 (by rfl) ⟨1548635, by rfl⟩ : syracuseStep 2064847 = 3097271) B3097271
theorem B1835471 : Blo 1833618 1835471 := bstep (se 1 (by rfl) ⟨1376603, by rfl⟩ : syracuseStep 1835471 = 2753207) B2753207
theorem B18833897 : Blo 1833618 18833897 := bstep (se 2 (by rfl) ⟨7062711, by rfl⟩ : syracuseStep 18833897 = 14125423) B14125423
theorem B3097183 : Blo 1833618 3097183 := bstep (se 1 (by rfl) ⟨2322887, by rfl⟩ : syracuseStep 3097183 = 4645775) B4645775
theorem B8364653 : Blo 1833618 8364653 := bstep (se 3 (by rfl) ⟨1568372, by rfl⟩ : syracuseStep 8364653 = 3136745) B3136745
theorem B13222595 : Blo 1833618 13222595 := bstep (se 1 (by rfl) ⟨9916946, by rfl⟩ : syracuseStep 13222595 = 19833893) B19833893
theorem B3351305 : Blo 1833618 3351305 := bstep (se 2 (by rfl) ⟨1256739, by rfl⟩ : syracuseStep 3351305 = 2513479) B2513479
theorem B10453769 : Blo 1833618 10453769 := bstep (se 2 (by rfl) ⟨3920163, by rfl⟩ : syracuseStep 10453769 = 7840327) B7840327
theorem B2753321 : Blo 1833618 2753321 := bstep (se 2 (by rfl) ⟨1032495, by rfl⟩ : syracuseStep 2753321 = 2064991) B2064991
theorem B6964015 : Blo 1833618 6964015 := bstep (se 1 (by rfl) ⟨5223011, by rfl⟩ : syracuseStep 6964015 = 10446023) B10446023
theorem B2753327 : Blo 1833618 2753327 := bstep (se 1 (by rfl) ⟨2064995, by rfl⟩ : syracuseStep 2753327 = 4129991) B4129991
theorem B50201491 : Blo 1833618 50201491 := bstep (se 1 (by rfl) ⟨37651118, by rfl⟩ : syracuseStep 50201491 = 75302237) B75302237
theorem B4129703 : Blo 1833618 4129703 := bstep (se 1 (by rfl) ⟨3097277, by rfl⟩ : syracuseStep 4129703 = 6194555) B6194555
theorem B3097595 : Blo 1833618 3097595 := bstep (se 1 (by rfl) ⟨2323196, by rfl⟩ : syracuseStep 3097595 = 4646393) B4646393
theorem B29754469 : Blo 1833618 29754469 := bstep (se 4 (by rfl) ⟨2789481, by rfl⟩ : syracuseStep 29754469 = 5578963) B5578963
theorem B9282923 : Blo 1833618 9282923 := bstep (se 1 (by rfl) ⟨6962192, by rfl⟩ : syracuseStep 9282923 = 13924385) B13924385
theorem B19834237 : Blo 1833618 19834237 := bstep (se 3 (by rfl) ⟨3718919, by rfl⟩ : syracuseStep 19834237 = 7437839) B7437839
theorem B2205083 : Blo 1833618 2205083 := bstep (se 1 (by rfl) ⟨1653812, by rfl⟩ : syracuseStep 2205083 = 3307625) B3307625
theorem B6194771 : Blo 1833618 6194771 := bstep (se 1 (by rfl) ⟨4646078, by rfl⟩ : syracuseStep 6194771 = 9292157) B9292157
theorem B11748959 : Blo 1833618 11748959 := bstep (se 1 (by rfl) ⟨8811719, by rfl⟩ : syracuseStep 11748959 = 17623439) B17623439
theorem B13223519 : Blo 1833618 13223519 := bstep (se 1 (by rfl) ⟨9917639, by rfl⟩ : syracuseStep 13223519 = 19835279) B19835279
theorem B1959535 : Blo 1833618 1959535 := bstep (se 1 (by rfl) ⟨1469651, by rfl⟩ : syracuseStep 1959535 = 2939303) B2939303
theorem B17639045 : Blo 1833618 17639045 := bstep (se 4 (by rfl) ⟨1653660, by rfl⟩ : syracuseStep 17639045 = 3307321) B3307321
theorem B4409167 : Blo 1833618 4409167 := bstep (se 1 (by rfl) ⟨3306875, by rfl⟩ : syracuseStep 4409167 = 6613751) B6613751
theorem B6195041 : Blo 1833618 6195041 := bstep (se 2 (by rfl) ⟨2323140, by rfl⟩ : syracuseStep 6195041 = 4646281) B4646281
theorem B6965459 : Blo 1833618 6965459 := bstep (se 1 (by rfl) ⟨5224094, by rfl⟩ : syracuseStep 6965459 = 10448189) B10448189
theorem B2795899 : Blo 1833618 2795899 := bstep (se 1 (by rfl) ⟨2096924, by rfl⟩ : syracuseStep 2795899 = 4193849) B4193849
theorem B9292319 : Blo 1833618 9292319 := bstep (se 1 (by rfl) ⟨6969239, by rfl⟩ : syracuseStep 9292319 = 13938479) B13938479
theorem B15674093 : Blo 1833618 15674093 := bstep (se 3 (by rfl) ⟨2938892, by rfl⟩ : syracuseStep 15674093 = 5877785) B5877785
theorem B11758391 : Blo 1833618 11758391 := bstep (se 1 (by rfl) ⟨8818793, by rfl⟩ : syracuseStep 11758391 = 17637587) B17637587
theorem B50228099 : Blo 1833618 50228099 := bstep (se 1 (by rfl) ⟨37671074, by rfl⟩ : syracuseStep 50228099 = 75342149) B75342149
theorem B2321455 : Blo 1833618 2321455 := bstep (se 1 (by rfl) ⟨1741091, by rfl⟩ : syracuseStep 2321455 = 3482183) B3482183
theorem B9284705 : Blo 1833618 9284705 := bstep (se 2 (by rfl) ⟨3481764, by rfl⟩ : syracuseStep 9284705 = 6963529) B6963529
theorem B44633267 : Blo 1833618 44633267 := bstep (se 1 (by rfl) ⟨33474950, by rfl⟩ : syracuseStep 44633267 = 66949901) B66949901
theorem B11160899 : Blo 1833618 11160899 := bstep (se 1 (by rfl) ⟨8370674, by rfl⟩ : syracuseStep 11160899 = 16741349) B16741349
theorem B3304871 : Blo 1833618 3304871 := bstep (se 1 (by rfl) ⟨2478653, by rfl⟩ : syracuseStep 3304871 = 4957307) B4957307
theorem B6188669 : Blo 1833618 6188669 := bstep (se 3 (by rfl) ⟨1160375, by rfl⟩ : syracuseStep 6188669 = 2320751) B2320751
theorem B23498585 : Blo 1833618 23498585 := bstep (se 2 (by rfl) ⟨8811969, by rfl⟩ : syracuseStep 23498585 = 17623939) B17623939
theorem B6188939 : Blo 1833618 6188939 := bstep (se 1 (by rfl) ⟨4641704, by rfl⟩ : syracuseStep 6188939 = 9283409) B9283409
theorem B9285515 : Blo 1833618 9285515 := bstep (se 1 (by rfl) ⟨6964136, by rfl⟩ : syracuseStep 9285515 = 13928273) B13928273
theorem B17878931 : Blo 1833618 17878931 := bstep (se 1 (by rfl) ⟨13409198, by rfl⟩ : syracuseStep 17878931 = 26818397) B26818397
theorem B40194265 : Blo 1833618 40194265 := bstep (se 2 (by rfl) ⟨15072849, by rfl⟩ : syracuseStep 40194265 = 30145699) B30145699
theorem B6189479 : Blo 1833618 6189479 := bstep (se 1 (by rfl) ⟨4642109, by rfl⟩ : syracuseStep 6189479 = 9284219) B9284219
theorem B47673805 : Blo 1833618 47673805 := bstep (se 3 (by rfl) ⟨8938838, by rfl⟩ : syracuseStep 47673805 = 17877677) B17877677
theorem B6967903 : Blo 1833618 6967903 := bstep (se 1 (by rfl) ⟨5225927, by rfl⟩ : syracuseStep 6967903 = 10451855) B10451855
theorem B52900523 : Blo 1833618 52900523 := bstep (se 1 (by rfl) ⟨39675392, by rfl⟩ : syracuseStep 52900523 = 79350785) B79350785
theorem B120656945 : Blo 1833618 120656945 := bstep (se 2 (by rfl) ⟨45246354, by rfl⟩ : syracuseStep 120656945 = 90492709) B90492709
theorem B6968375 : Blo 1833618 6968375 := bstep (se 1 (by rfl) ⟨5226281, by rfl⟩ : syracuseStep 6968375 = 10452563) B10452563
theorem B25097465 : Blo 1833618 25097465 := bstep (se 2 (by rfl) ⟨9411549, by rfl⟩ : syracuseStep 25097465 = 18823099) B18823099
theorem B9286973 : Blo 1833618 9286973 := bstep (se 3 (by rfl) ⟨1741307, by rfl⟩ : syracuseStep 9286973 = 3482615) B3482615
theorem B47003003 : Blo 1833618 47003003 := bstep (se 1 (by rfl) ⟨35252252, by rfl⟩ : syracuseStep 47003003 = 70504505) B70504505
theorem B14874121 : Blo 1833618 14874121 := bstep (se 2 (by rfl) ⟨5577795, by rfl⟩ : syracuseStep 14874121 = 11155591) B11155591
theorem B4126391 : Blo 1833618 4126391 := bstep (se 1 (by rfl) ⟨3094793, by rfl⟩ : syracuseStep 4126391 = 6189587) B6189587
theorem B6190775 : Blo 1833618 6190775 := bstep (se 1 (by rfl) ⟨4643081, by rfl⟩ : syracuseStep 6190775 = 9286163) B9286163
theorem B2612827 : Blo 1833618 2612827 := bstep (se 1 (by rfl) ⟨1959620, by rfl⟩ : syracuseStep 2612827 = 3919241) B3919241
theorem B3094267 : Blo 1833618 3094267 := bstep (se 1 (by rfl) ⟨2320700, by rfl⟩ : syracuseStep 3094267 = 4641401) B4641401
theorem B4642555 : Blo 1833618 4642555 := bstep (se 1 (by rfl) ⟨3481916, by rfl⟩ : syracuseStep 4642555 = 6963833) B6963833
theorem B3094409 : Blo 1833618 3094409 := bstep (se 2 (by rfl) ⟨1160403, by rfl⟩ : syracuseStep 3094409 = 2320807) B2320807
theorem B4642697 : Blo 1833618 4642697 := bstep (se 2 (by rfl) ⟨1741011, by rfl⟩ : syracuseStep 4642697 = 3482023) B3482023
theorem B2750447 : Blo 1833618 2750447 := bstep (se 1 (by rfl) ⟨2062835, by rfl⟩ : syracuseStep 2750447 = 4125671) B4125671
theorem B17627129 : Blo 1833618 17627129 := bstep (se 2 (by rfl) ⟨6610173, by rfl⟩ : syracuseStep 17627129 = 13220347) B13220347
theorem B28620859 : Blo 1833618 28620859 := bstep (se 1 (by rfl) ⟨21465644, by rfl⟩ : syracuseStep 28620859 = 42931289) B42931289
theorem B5027923 : Blo 1833618 5027923 := bstep (se 1 (by rfl) ⟨3770942, by rfl⟩ : syracuseStep 5027923 = 7541885) B7541885
theorem B2750699 : Blo 1833618 2750699 := bstep (se 1 (by rfl) ⟨2063024, by rfl⟩ : syracuseStep 2750699 = 4126049) B4126049
theorem B2750759 : Blo 1833618 2750759 := bstep (se 1 (by rfl) ⟨2063069, by rfl⟩ : syracuseStep 2750759 = 4126139) B4126139
theorem B3094841 : Blo 1833618 3094841 := bstep (se 2 (by rfl) ⟨1160565, by rfl⟩ : syracuseStep 3094841 = 2321131) B2321131
theorem B2750843 : Blo 1833618 2750843 := bstep (se 1 (by rfl) ⟨2063132, by rfl⟩ : syracuseStep 2750843 = 4126265) B4126265
theorem B50207165 : Blo 1833618 50207165 := bstep (se 3 (by rfl) ⟨9413843, by rfl⟩ : syracuseStep 50207165 = 18827687) B18827687
theorem B72456677 : Blo 1833618 72456677 := bstep (se 4 (by rfl) ⟨6792813, by rfl⟩ : syracuseStep 72456677 = 13585627) B13585627
theorem B13228595 : Blo 1833618 13228595 := bstep (se 1 (by rfl) ⟨9921446, by rfl⟩ : syracuseStep 13228595 = 19842893) B19842893
theorem B7838329 : Blo 1833618 7838329 := bstep (se 2 (by rfl) ⟨2939373, by rfl⟩ : syracuseStep 7838329 = 5878747) B5878747
theorem B2751113 : Blo 1833618 2751113 := bstep (se 2 (by rfl) ⟨1031667, by rfl⟩ : syracuseStep 2751113 = 2063335) B2063335
theorem B7838345 : Blo 1833618 7838345 := bstep (se 2 (by rfl) ⟨2939379, by rfl⟩ : syracuseStep 7838345 = 5878759) B5878759
theorem B2939579 : Blo 1833618 2939579 := bstep (se 1 (by rfl) ⟨2204684, by rfl⟩ : syracuseStep 2939579 = 4409369) B4409369
theorem B10443563 : Blo 1833618 10443563 := bstep (se 1 (by rfl) ⟨7832672, by rfl⟩ : syracuseStep 10443563 = 15665345) B15665345
theorem B2751287 : Blo 1833618 2751287 := bstep (se 1 (by rfl) ⟨2063465, by rfl⟩ : syracuseStep 2751287 = 4126931) B4126931
theorem B15670097 : Blo 1833618 15670097 := bstep (se 2 (by rfl) ⟨5876286, by rfl⟩ : syracuseStep 15670097 = 11752573) B11752573
theorem B1833819 : Blo 1833618 1833819 := bstep (se 1 (by rfl) ⟨1375364, by rfl⟩ : syracuseStep 1833819 = 2750729) B2750729
theorem B2751323 : Blo 1833618 2751323 := bstep (se 1 (by rfl) ⟨2063492, by rfl⟩ : syracuseStep 2751323 = 4126985) B4126985
theorem B4127579 : Blo 1833618 4127579 := bstep (se 1 (by rfl) ⟨3095684, by rfl⟩ : syracuseStep 4127579 = 6191369) B6191369
theorem B6191963 : Blo 1833618 6191963 := bstep (se 1 (by rfl) ⟨4643972, by rfl⟩ : syracuseStep 6191963 = 9287945) B9287945
theorem B4643689 : Blo 1833618 4643689 := bstep (se 2 (by rfl) ⟨1741383, by rfl⟩ : syracuseStep 4643689 = 3482767) B3482767
theorem B1833887 : Blo 1833618 1833887 := bstep (se 1 (by rfl) ⟨1375415, by rfl⟩ : syracuseStep 1833887 = 2750831) B2750831
theorem B2063263 : Blo 1833618 2063263 := bstep (se 1 (by rfl) ⟨1547447, by rfl⟩ : syracuseStep 2063263 = 3094895) B3094895
theorem B3095455 : Blo 1833618 3095455 := bstep (se 1 (by rfl) ⟨2321591, by rfl⟩ : syracuseStep 3095455 = 4643183) B4643183
theorem B2751467 : Blo 1833618 2751467 := bstep (se 1 (by rfl) ⟨2063600, by rfl⟩ : syracuseStep 2751467 = 4127201) B4127201
theorem B1834031 : Blo 1833618 1834031 := bstep (se 1 (by rfl) ⟨1375523, by rfl⟩ : syracuseStep 1834031 = 2751047) B2751047
theorem B2063407 : Blo 1833618 2063407 := bstep (se 1 (by rfl) ⟨1547555, by rfl⟩ : syracuseStep 2063407 = 3095111) B3095111
theorem B1834055 : Blo 1833618 1834055 := bstep (se 1 (by rfl) ⟨1375541, by rfl⟩ : syracuseStep 1834055 = 2751083) B2751083
theorem B2751671 : Blo 1833618 2751671 := bstep (se 1 (by rfl) ⟨2063753, by rfl⟩ : syracuseStep 2751671 = 4127507) B4127507
theorem B1834207 : Blo 1833618 1834207 := bstep (se 1 (by rfl) ⟨1375655, by rfl⟩ : syracuseStep 1834207 = 2751311) B2751311
theorem B2063695 : Blo 1833618 2063695 := bstep (se 1 (by rfl) ⟨1547771, by rfl⟩ : syracuseStep 2063695 = 3095543) B3095543
theorem B3095887 : Blo 1833618 3095887 := bstep (se 1 (by rfl) ⟨2321915, by rfl⟩ : syracuseStep 3095887 = 4643831) B4643831
theorem B2751911 : Blo 1833618 2751911 := bstep (se 1 (by rfl) ⟨2063933, by rfl⟩ : syracuseStep 2751911 = 4127867) B4127867
theorem B3095975 : Blo 1833618 3095975 := bstep (se 1 (by rfl) ⟨2321981, by rfl⟩ : syracuseStep 3095975 = 4643963) B4643963
theorem B24157639 : Blo 1833618 24157639 := bstep (se 1 (by rfl) ⟨18118229, by rfl⟩ : syracuseStep 24157639 = 36236459) B36236459
theorem B13925843 : Blo 1833618 13925843 := bstep (se 1 (by rfl) ⟨10444382, by rfl⟩ : syracuseStep 13925843 = 20888765) B20888765
theorem B1834471 : Blo 1833618 1834471 := bstep (se 1 (by rfl) ⟨1375853, by rfl⟩ : syracuseStep 1834471 = 2751707) B2751707
theorem B2751995 : Blo 1833618 2751995 := bstep (se 1 (by rfl) ⟨2063996, by rfl⟩ : syracuseStep 2751995 = 4127993) B4127993
theorem B2612731 : Blo 1833618 2612731 := bstep (se 1 (by rfl) ⟨1959548, by rfl⟩ : syracuseStep 2612731 = 3919097) B3919097
theorem B28237349 : Blo 1833618 28237349 := bstep (se 4 (by rfl) ⟨2647251, by rfl⟩ : syracuseStep 28237349 = 5294503) B5294503
theorem B3096137 : Blo 1833618 3096137 := bstep (se 2 (by rfl) ⟨1161051, by rfl⟩ : syracuseStep 3096137 = 2322103) B2322103
theorem B4128335 : Blo 1833618 4128335 := bstep (se 1 (by rfl) ⟨3096251, by rfl⟩ : syracuseStep 4128335 = 6192503) B6192503
theorem B6192719 : Blo 1833618 6192719 := bstep (se 1 (by rfl) ⟨4644539, by rfl⟩ : syracuseStep 6192719 = 9289079) B9289079
theorem B1834587 : Blo 1833618 1834587 := bstep (se 1 (by rfl) ⟨1375940, by rfl⟩ : syracuseStep 1834587 = 2751881) B2751881
theorem B2752091 : Blo 1833618 2752091 := bstep (se 1 (by rfl) ⟨2064068, by rfl⟩ : syracuseStep 2752091 = 4128137) B4128137
theorem B6962831 : Blo 1833618 6962831 := bstep (se 1 (by rfl) ⟨5222123, by rfl⟩ : syracuseStep 6962831 = 10444247) B10444247
theorem B2752175 : Blo 1833618 2752175 := bstep (se 1 (by rfl) ⟨2064131, by rfl⟩ : syracuseStep 2752175 = 4128263) B4128263
theorem B6192827 : Blo 1833618 6192827 := bstep (se 1 (by rfl) ⟨4644620, by rfl⟩ : syracuseStep 6192827 = 9289241) B9289241
theorem B9289403 : Blo 1833618 9289403 := bstep (se 1 (by rfl) ⟨6967052, by rfl⟩ : syracuseStep 9289403 = 13934105) B13934105
theorem B2752295 : Blo 1833618 2752295 := bstep (se 1 (by rfl) ⟨2064221, by rfl⟩ : syracuseStep 2752295 = 4128443) B4128443
theorem B1834823 : Blo 1833618 1834823 := bstep (se 1 (by rfl) ⟨1376117, by rfl⟩ : syracuseStep 1834823 = 2752235) B2752235
theorem B2064199 : Blo 1833618 2064199 := bstep (se 1 (by rfl) ⟨1548149, by rfl⟩ : syracuseStep 2064199 = 3096299) B3096299
theorem B2752379 : Blo 1833618 2752379 := bstep (se 1 (by rfl) ⟨2064284, by rfl⟩ : syracuseStep 2752379 = 4128569) B4128569
theorem B7839611 : Blo 1833618 7839611 := bstep (se 1 (by rfl) ⟨5879708, by rfl⟩ : syracuseStep 7839611 = 11759417) B11759417
theorem B1834975 : Blo 1833618 1834975 := bstep (se 1 (by rfl) ⟨1376231, by rfl⟩ : syracuseStep 1834975 = 2752463) B2752463
theorem B2752703 : Blo 1833618 2752703 := bstep (se 1 (by rfl) ⟨2064527, by rfl⟩ : syracuseStep 2752703 = 4129055) B4129055
theorem B1835199 : Blo 1833618 1835199 := bstep (se 1 (by rfl) ⟨1376399, by rfl⟩ : syracuseStep 1835199 = 2752799) B2752799
theorem B1835215 : Blo 1833618 1835215 := bstep (se 1 (by rfl) ⟨1376411, by rfl⟩ : syracuseStep 1835215 = 2752823) B2752823
theorem B1835263 : Blo 1833618 1835263 := bstep (se 1 (by rfl) ⟨1376447, by rfl⟩ : syracuseStep 1835263 = 2752895) B2752895
theorem B53592353 : Blo 1833618 53592353 := bstep (se 2 (by rfl) ⟨20097132, by rfl⟩ : syracuseStep 53592353 = 40194265) B40194265
theorem B1835311 : Blo 1833618 1835311 := bstep (se 1 (by rfl) ⟨1376483, by rfl⟩ : syracuseStep 1835311 = 2752967) B2752967
theorem B35267015 : Blo 1833618 35267015 := bstep (se 1 (by rfl) ⟨26450261, by rfl⟩ : syracuseStep 35267015 = 52900523) B52900523
theorem B8815063 : Blo 1833618 8815063 := bstep (se 1 (by rfl) ⟨6611297, by rfl⟩ : syracuseStep 8815063 = 13222595) B13222595
theorem B13935077 : Blo 1833618 13935077 := bstep (se 4 (by rfl) ⟨1306413, by rfl⟩ : syracuseStep 13935077 = 2612827) B2612827
theorem B3727865 : Blo 1833618 3727865 := bstep (se 2 (by rfl) ⟨1397949, by rfl⟩ : syracuseStep 3727865 = 2795899) B2795899
theorem B1835547 : Blo 1833618 1835547 := bstep (se 1 (by rfl) ⟨1376660, by rfl⟩ : syracuseStep 1835547 = 2753321) B2753321
theorem B1835551 : Blo 1833618 1835551 := bstep (se 1 (by rfl) ⟨1376663, by rfl⟩ : syracuseStep 1835551 = 2753327) B2753327
theorem B2753129 : Blo 1833618 2753129 := bstep (se 2 (by rfl) ⟨1032423, by rfl⟩ : syracuseStep 2753129 = 2064847) B2064847
theorem B2753135 : Blo 1833618 2753135 := bstep (se 1 (by rfl) ⟨2064851, by rfl⟩ : syracuseStep 2753135 = 4129703) B4129703
theorem B2065063 : Blo 1833618 2065063 := bstep (se 1 (by rfl) ⟨1548797, by rfl⟩ : syracuseStep 2065063 = 3097595) B3097595
theorem B80437963 : Blo 1833618 80437963 := bstep (se 1 (by rfl) ⟨60328472, by rfl⟩ : syracuseStep 80437963 = 120656945) B120656945
theorem B4645583 : Blo 1833618 4645583 := bstep (se 1 (by rfl) ⟨3484187, by rfl⟩ : syracuseStep 4645583 = 6968375) B6968375
theorem B9290537 : Blo 1833618 9290537 := bstep (se 2 (by rfl) ⟨3483951, by rfl⟩ : syracuseStep 9290537 = 6967903) B6967903
theorem B4129577 : Blo 1833618 4129577 := bstep (se 2 (by rfl) ⟨1548591, by rfl⟩ : syracuseStep 4129577 = 3097183) B3097183
theorem B31335335 : Blo 1833618 31335335 := bstep (se 1 (by rfl) ⟨23501501, by rfl⟩ : syracuseStep 31335335 = 47003003) B47003003
theorem B4129847 : Blo 1833618 4129847 := bstep (se 1 (by rfl) ⟨3097385, by rfl⟩ : syracuseStep 4129847 = 6194771) B6194771
theorem B7832639 : Blo 1833618 7832639 := bstep (se 1 (by rfl) ⟨5874479, by rfl⟩ : syracuseStep 7832639 = 11748959) B11748959
theorem B8815679 : Blo 1833618 8815679 := bstep (se 1 (by rfl) ⟨6611759, by rfl⟩ : syracuseStep 8815679 = 13223519) B13223519
theorem B4130027 : Blo 1833618 4130027 := bstep (se 1 (by rfl) ⟨3097520, by rfl⟩ : syracuseStep 4130027 = 6195041) B6195041
theorem B6194879 : Blo 1833618 6194879 := bstep (se 1 (by rfl) ⟨4646159, by rfl⟩ : syracuseStep 6194879 = 9292319) B9292319
theorem B1959719 : Blo 1833618 1959719 := bstep (se 1 (by rfl) ⟨1469789, by rfl⟩ : syracuseStep 1959719 = 2939579) B2939579
theorem B26445649 : Blo 1833618 26445649 := bstep (se 2 (by rfl) ⟨9917118, by rfl⟩ : syracuseStep 26445649 = 19834237) B19834237
theorem B10446731 : Blo 1833618 10446731 := bstep (se 1 (by rfl) ⟨7835048, by rfl⟩ : syracuseStep 10446731 = 15670097) B15670097
theorem B3483641 : Blo 1833618 3483641 := bstep (se 2 (by rfl) ⟨1306365, by rfl⟩ : syracuseStep 3483641 = 2612731) B2612731
theorem B29755511 : Blo 1833618 29755511 := bstep (se 1 (by rfl) ⟨22316633, by rfl⟩ : syracuseStep 29755511 = 44633267) B44633267
theorem B7440599 : Blo 1833618 7440599 := bstep (se 1 (by rfl) ⟨5580449, by rfl⟩ : syracuseStep 7440599 = 11160899) B11160899
theorem B9283895 : Blo 1833618 9283895 := bstep (se 1 (by rfl) ⟨6962921, by rfl⟩ : syracuseStep 9283895 = 13925843) B13925843
theorem B15665723 : Blo 1833618 15665723 := bstep (se 1 (by rfl) ⟨11749292, by rfl⟩ : syracuseStep 15665723 = 23498585) B23498585
theorem B38161145 : Blo 1833618 38161145 := bstep (se 2 (by rfl) ⟨14310429, by rfl⟩ : syracuseStep 38161145 = 28620859) B28620859
theorem B6703897 : Blo 1833618 6703897 := bstep (se 2 (by rfl) ⟨2513961, by rfl⟩ : syracuseStep 6703897 = 5027923) B5027923
theorem B13217033 : Blo 1833618 13217033 := bstep (se 2 (by rfl) ⟨4956387, by rfl⟩ : syracuseStep 13217033 = 9912775) B9912775
theorem B63565073 : Blo 1833618 63565073 := bstep (se 2 (by rfl) ⟨23836902, by rfl⟩ : syracuseStep 63565073 = 47673805) B47673805
theorem B16731643 : Blo 1833618 16731643 := bstep (se 1 (by rfl) ⟨12548732, by rfl⟩ : syracuseStep 16731643 = 25097465) B25097465
theorem B6188615 : Blo 1833618 6188615 := bstep (se 1 (by rfl) ⟨4641461, by rfl⟩ : syracuseStep 6188615 = 9282923) B9282923
theorem B9285353 : Blo 1833618 9285353 := bstep (se 2 (by rfl) ⟨3482007, by rfl⟩ : syracuseStep 9285353 = 6964015) B6964015
theorem B11759363 : Blo 1833618 11759363 := bstep (se 1 (by rfl) ⟨8819522, by rfl⟩ : syracuseStep 11759363 = 17639045) B17639045
theorem B11751419 : Blo 1833618 11751419 := bstep (se 1 (by rfl) ⟨8813564, by rfl⟩ : syracuseStep 11751419 = 17627129) B17627129
theorem B48304451 : Blo 1833618 48304451 := bstep (se 1 (by rfl) ⟨36228338, by rfl⟩ : syracuseStep 48304451 = 72456677) B72456677
theorem B8819063 : Blo 1833618 8819063 := bstep (se 1 (by rfl) ⟨6614297, by rfl⟩ : syracuseStep 8819063 = 13228595) B13228595
theorem B10449395 : Blo 1833618 10449395 := bstep (se 1 (by rfl) ⟨7837046, by rfl⟩ : syracuseStep 10449395 = 15674093) B15674093
theorem B33485399 : Blo 1833618 33485399 := bstep (se 1 (by rfl) ⟨25114049, by rfl⟩ : syracuseStep 33485399 = 50228099) B50228099
theorem B6189803 : Blo 1833618 6189803 := bstep (se 1 (by rfl) ⟨4642352, by rfl⟩ : syracuseStep 6189803 = 9284705) B9284705
theorem B4125689 : Blo 1833618 4125689 := bstep (se 2 (by rfl) ⟨1547133, by rfl⟩ : syracuseStep 4125689 = 3094267) B3094267
theorem B6190073 : Blo 1833618 6190073 := bstep (se 2 (by rfl) ⟨2321277, by rfl⟩ : syracuseStep 6190073 = 4642555) B4642555
theorem B4125779 : Blo 1833618 4125779 := bstep (se 1 (by rfl) ⟨3094334, by rfl⟩ : syracuseStep 4125779 = 6188669) B6188669
theorem B4641887 : Blo 1833618 4641887 := bstep (se 1 (by rfl) ⟨3481415, by rfl⟩ : syracuseStep 4641887 = 6962831) B6962831
theorem B5878889 : Blo 1833618 5878889 := bstep (se 2 (by rfl) ⟨2204583, by rfl⟩ : syracuseStep 5878889 = 4409167) B4409167
theorem B4125959 : Blo 1833618 4125959 := bstep (se 1 (by rfl) ⟨3094469, by rfl⟩ : syracuseStep 4125959 = 6188939) B6188939
theorem B6190343 : Blo 1833618 6190343 := bstep (se 1 (by rfl) ⟨4642757, by rfl⟩ : syracuseStep 6190343 = 9285515) B9285515
theorem B4126319 : Blo 1833618 4126319 := bstep (se 1 (by rfl) ⟨3094739, by rfl⟩ : syracuseStep 4126319 = 6189479) B6189479
theorem B12555931 : Blo 1833618 12555931 := bstep (se 1 (by rfl) ⟨9416948, by rfl⟩ : syracuseStep 12555931 = 18833897) B18833897
theorem B5576435 : Blo 1833618 5576435 := bstep (se 1 (by rfl) ⟨4182326, by rfl⟩ : syracuseStep 5576435 = 8364653) B8364653
theorem B6969179 : Blo 1833618 6969179 := bstep (se 1 (by rfl) ⟨5226884, by rfl⟩ : syracuseStep 6969179 = 10453769) B10453769
theorem B10450853 : Blo 1833618 10450853 := bstep (se 4 (by rfl) ⟨979767, by rfl⟩ : syracuseStep 10450853 = 1959535) B1959535
theorem B10451105 : Blo 1833618 10451105 := bstep (se 2 (by rfl) ⟨3919164, by rfl⟩ : syracuseStep 10451105 = 7838329) B7838329
theorem B6191315 : Blo 1833618 6191315 := bstep (se 1 (by rfl) ⟨4643486, by rfl⟩ : syracuseStep 6191315 = 9286973) B9286973
theorem B5880221 : Blo 1833618 5880221 := bstep (se 3 (by rfl) ⟨1102541, by rfl⟩ : syracuseStep 5880221 = 2205083) B2205083
theorem B2750927 : Blo 1833618 2750927 := bstep (se 1 (by rfl) ⟨2063195, by rfl⟩ : syracuseStep 2750927 = 4126391) B4126391
theorem B4127183 : Blo 1833618 4127183 := bstep (se 1 (by rfl) ⟨3095387, by rfl⟩ : syracuseStep 4127183 = 6190775) B6190775
theorem B6191585 : Blo 1833618 6191585 := bstep (se 2 (by rfl) ⟨2321844, by rfl⟩ : syracuseStep 6191585 = 4643689) B4643689
theorem B15292901 : Blo 1833618 15292901 := bstep (se 4 (by rfl) ⟨1433709, by rfl⟩ : syracuseStep 15292901 = 2867419) B2867419
theorem B66935321 : Blo 1833618 66935321 := bstep (se 2 (by rfl) ⟨25100745, by rfl⟩ : syracuseStep 66935321 = 50201491) B50201491
theorem B2751017 : Blo 1833618 2751017 := bstep (se 2 (by rfl) ⟨1031631, by rfl⟩ : syracuseStep 2751017 = 2063263) B2063263
theorem B4127273 : Blo 1833618 4127273 := bstep (se 2 (by rfl) ⟨1547727, by rfl⟩ : syracuseStep 4127273 = 3095455) B3095455
theorem B2062939 : Blo 1833618 2062939 := bstep (se 1 (by rfl) ⟨1547204, by rfl⟩ : syracuseStep 2062939 = 3094409) B3094409
theorem B3095131 : Blo 1833618 3095131 := bstep (se 1 (by rfl) ⟨2321348, by rfl⟩ : syracuseStep 3095131 = 4642697) B4642697
theorem B1833631 : Blo 1833618 1833631 := bstep (se 1 (by rfl) ⟨1375223, by rfl⟩ : syracuseStep 1833631 = 2750447) B2750447
theorem B3095273 : Blo 1833618 3095273 := bstep (se 2 (by rfl) ⟨1160727, by rfl⟩ : syracuseStep 3095273 = 2321455) B2321455
theorem B2751209 : Blo 1833618 2751209 := bstep (se 2 (by rfl) ⟨1031703, by rfl⟩ : syracuseStep 2751209 = 2063407) B2063407
theorem B39672625 : Blo 1833618 39672625 := bstep (se 2 (by rfl) ⟨14877234, by rfl⟩ : syracuseStep 39672625 = 29754469) B29754469
theorem B4643639 : Blo 1833618 4643639 := bstep (se 1 (by rfl) ⟨3482729, by rfl⟩ : syracuseStep 4643639 = 6965459) B6965459
theorem B1833799 : Blo 1833618 1833799 := bstep (se 1 (by rfl) ⟨1375349, by rfl⟩ : syracuseStep 1833799 = 2750699) B2750699
theorem B1833839 : Blo 1833618 1833839 := bstep (se 1 (by rfl) ⟨1375379, by rfl⟩ : syracuseStep 1833839 = 2750759) B2750759
theorem B2063227 : Blo 1833618 2063227 := bstep (se 1 (by rfl) ⟨1547420, by rfl⟩ : syracuseStep 2063227 = 3094841) B3094841
theorem B1833895 : Blo 1833618 1833895 := bstep (se 1 (by rfl) ⟨1375421, by rfl⟩ : syracuseStep 1833895 = 2750843) B2750843
theorem B33471443 : Blo 1833618 33471443 := bstep (se 1 (by rfl) ⟨25103582, by rfl⟩ : syracuseStep 33471443 = 50207165) B50207165
theorem B1834075 : Blo 1833618 1834075 := bstep (se 1 (by rfl) ⟨1375556, by rfl⟩ : syracuseStep 1834075 = 2751113) B2751113
theorem B5225563 : Blo 1833618 5225563 := bstep (se 1 (by rfl) ⟨3919172, by rfl⟩ : syracuseStep 5225563 = 7838345) B7838345
theorem B2751593 : Blo 1833618 2751593 := bstep (se 2 (by rfl) ⟨1031847, by rfl⟩ : syracuseStep 2751593 = 2063695) B2063695
theorem B4127849 : Blo 1833618 4127849 := bstep (se 2 (by rfl) ⟨1547943, by rfl⟩ : syracuseStep 4127849 = 3095887) B3095887
theorem B6962375 : Blo 1833618 6962375 := bstep (se 1 (by rfl) ⟨5221781, by rfl⟩ : syracuseStep 6962375 = 10443563) B10443563
theorem B1834191 : Blo 1833618 1834191 := bstep (se 1 (by rfl) ⟨1375643, by rfl⟩ : syracuseStep 1834191 = 2751287) B2751287
theorem B7838927 : Blo 1833618 7838927 := bstep (se 1 (by rfl) ⟨5879195, by rfl⟩ : syracuseStep 7838927 = 11758391) B11758391
theorem B1834215 : Blo 1833618 1834215 := bstep (se 1 (by rfl) ⟨1375661, by rfl⟩ : syracuseStep 1834215 = 2751323) B2751323
theorem B2751719 : Blo 1833618 2751719 := bstep (se 1 (by rfl) ⟨2063789, by rfl⟩ : syracuseStep 2751719 = 4127579) B4127579
theorem B4127975 : Blo 1833618 4127975 := bstep (se 1 (by rfl) ⟨3095981, by rfl⟩ : syracuseStep 4127975 = 6191963) B6191963
theorem B32210185 : Blo 1833618 32210185 := bstep (se 2 (by rfl) ⟨12078819, by rfl⟩ : syracuseStep 32210185 = 24157639) B24157639
theorem B1834311 : Blo 1833618 1834311 := bstep (se 1 (by rfl) ⟨1375733, by rfl⟩ : syracuseStep 1834311 = 2751467) B2751467
theorem B19832161 : Blo 1833618 19832161 := bstep (se 2 (by rfl) ⟨7437060, by rfl⟩ : syracuseStep 19832161 = 14874121) B14874121
theorem B8936813 : Blo 1833618 8936813 := bstep (se 3 (by rfl) ⟨1675652, by rfl⟩ : syracuseStep 8936813 = 3351305) B3351305
theorem B1834447 : Blo 1833618 1834447 := bstep (se 1 (by rfl) ⟨1375835, by rfl⟩ : syracuseStep 1834447 = 2751671) B2751671
theorem B2203247 : Blo 1833618 2203247 := bstep (se 1 (by rfl) ⟨1652435, by rfl⟩ : syracuseStep 2203247 = 3304871) B3304871
theorem B1834607 : Blo 1833618 1834607 := bstep (se 1 (by rfl) ⟨1375955, by rfl⟩ : syracuseStep 1834607 = 2751911) B2751911
theorem B2063983 : Blo 1833618 2063983 := bstep (se 1 (by rfl) ⟨1547987, by rfl⟩ : syracuseStep 2063983 = 3095975) B3095975
theorem B1834663 : Blo 1833618 1834663 := bstep (se 1 (by rfl) ⟨1375997, by rfl⟩ : syracuseStep 1834663 = 2751995) B2751995
theorem B18824899 : Blo 1833618 18824899 := bstep (se 1 (by rfl) ⟨14118674, by rfl⟩ : syracuseStep 18824899 = 28237349) B28237349
theorem B2064091 : Blo 1833618 2064091 := bstep (se 1 (by rfl) ⟨1548068, by rfl⟩ : syracuseStep 2064091 = 3096137) B3096137
theorem B2752223 : Blo 1833618 2752223 := bstep (se 1 (by rfl) ⟨2064167, by rfl⟩ : syracuseStep 2752223 = 4128335) B4128335
theorem B4128479 : Blo 1833618 4128479 := bstep (se 1 (by rfl) ⟨3096359, by rfl⟩ : syracuseStep 4128479 = 6192719) B6192719
theorem B1834727 : Blo 1833618 1834727 := bstep (se 1 (by rfl) ⟨1376045, by rfl⟩ : syracuseStep 1834727 = 2752091) B2752091
theorem B2752265 : Blo 1833618 2752265 := bstep (se 2 (by rfl) ⟨1032099, by rfl⟩ : syracuseStep 2752265 = 2064199) B2064199
theorem B1834783 : Blo 1833618 1834783 := bstep (se 1 (by rfl) ⟨1376087, by rfl⟩ : syracuseStep 1834783 = 2752175) B2752175
theorem B4128551 : Blo 1833618 4128551 := bstep (se 1 (by rfl) ⟨3096413, by rfl⟩ : syracuseStep 4128551 = 6192827) B6192827
theorem B6192935 : Blo 1833618 6192935 := bstep (se 1 (by rfl) ⟨4644701, by rfl⟩ : syracuseStep 6192935 = 9289403) B9289403
theorem B1834863 : Blo 1833618 1834863 := bstep (se 1 (by rfl) ⟨1376147, by rfl⟩ : syracuseStep 1834863 = 2752295) B2752295
theorem B1834919 : Blo 1833618 1834919 := bstep (se 1 (by rfl) ⟨1376189, by rfl⟩ : syracuseStep 1834919 = 2752379) B2752379
theorem B5226407 : Blo 1833618 5226407 := bstep (se 1 (by rfl) ⟨3919805, by rfl⟩ : syracuseStep 5226407 = 7839611) B7839611
theorem B11919287 : Blo 1833618 11919287 := bstep (se 1 (by rfl) ⟨8939465, by rfl⟩ : syracuseStep 11919287 = 17878931) B17878931
theorem B1835135 : Blo 1833618 1835135 := bstep (se 1 (by rfl) ⟨1376351, by rfl⟩ : syracuseStep 1835135 = 2752703) B2752703
theorem B32202967 : Blo 1833618 32202967 := bstep (se 1 (by rfl) ⟨24152225, by rfl⟩ : syracuseStep 32202967 = 48304451) B48304451
theorem B23511343 : Blo 1833618 23511343 := bstep (se 1 (by rfl) ⟨17633507, by rfl⟩ : syracuseStep 23511343 = 35267015) B35267015
theorem B9290051 : Blo 1833618 9290051 := bstep (se 1 (by rfl) ⟨6967538, by rfl⟩ : syracuseStep 9290051 = 13935077) B13935077
theorem B22323599 : Blo 1833618 22323599 := bstep (se 1 (by rfl) ⟨16742699, by rfl⟩ : syracuseStep 22323599 = 33485399) B33485399
theorem B1835419 : Blo 1833618 1835419 := bstep (se 1 (by rfl) ⟨1376564, by rfl⟩ : syracuseStep 1835419 = 2753129) B2753129
theorem B1835423 : Blo 1833618 1835423 := bstep (se 1 (by rfl) ⟨1376567, by rfl⟩ : syracuseStep 1835423 = 2753135) B2753135
theorem B3097055 : Blo 1833618 3097055 := bstep (se 1 (by rfl) ⟨2322791, by rfl⟩ : syracuseStep 3097055 = 4645583) B4645583
theorem B6193691 : Blo 1833618 6193691 := bstep (se 1 (by rfl) ⟨4645268, by rfl⟩ : syracuseStep 6193691 = 9290537) B9290537
theorem B2753051 : Blo 1833618 2753051 := bstep (se 1 (by rfl) ⟨2064788, by rfl⟩ : syracuseStep 2753051 = 4129577) B4129577
theorem B20890223 : Blo 1833618 20890223 := bstep (se 1 (by rfl) ⟨15667667, by rfl⟩ : syracuseStep 20890223 = 31335335) B31335335
theorem B2753231 : Blo 1833618 2753231 := bstep (se 1 (by rfl) ⟨2064923, by rfl⟩ : syracuseStep 2753231 = 4129847) B4129847
theorem B2753351 : Blo 1833618 2753351 := bstep (se 1 (by rfl) ⟨2065013, by rfl⟩ : syracuseStep 2753351 = 4130027) B4130027
theorem B2753417 : Blo 1833618 2753417 := bstep (se 2 (by rfl) ⟨1032531, by rfl⟩ : syracuseStep 2753417 = 2065063) B2065063
theorem B107250617 : Blo 1833618 107250617 := bstep (se 2 (by rfl) ⟨40218981, by rfl⟩ : syracuseStep 107250617 = 80437963) B80437963
theorem B8938529 : Blo 1833618 8938529 := bstep (se 2 (by rfl) ⟨3351948, by rfl⟩ : syracuseStep 8938529 = 6703897) B6703897
theorem B52896833 : Blo 1833618 52896833 := bstep (se 2 (by rfl) ⟨19836312, by rfl⟩ : syracuseStep 52896833 = 39672625) B39672625
theorem B4129919 : Blo 1833618 4129919 := bstep (se 1 (by rfl) ⟨3097439, by rfl⟩ : syracuseStep 4129919 = 6194879) B6194879
theorem B4646119 : Blo 1833618 4646119 := bstep (se 1 (by rfl) ⟨3484589, by rfl⟩ : syracuseStep 4646119 = 6969179) B6969179
theorem B6964487 : Blo 1833618 6964487 := bstep (se 1 (by rfl) ⟨5223365, by rfl⟩ : syracuseStep 6964487 = 10446731) B10446731
theorem B5875325 : Blo 1833618 5875325 := bstep (se 3 (by rfl) ⟨1101623, by rfl⟩ : syracuseStep 5875325 = 2203247) B2203247
theorem B44623547 : Blo 1833618 44623547 := bstep (se 1 (by rfl) ⟨33467660, by rfl⟩ : syracuseStep 44623547 = 66935321) B66935321
theorem B22308857 : Blo 1833618 22308857 := bstep (se 2 (by rfl) ⟨8365821, by rfl⟩ : syracuseStep 22308857 = 16731643) B16731643
theorem B5957875 : Blo 1833618 5957875 := bstep (se 1 (by rfl) ⟨4468406, by rfl⟩ : syracuseStep 5957875 = 8936813) B8936813
theorem B35260865 : Blo 1833618 35260865 := bstep (se 2 (by rfl) ⟨13222824, by rfl⟩ : syracuseStep 35260865 = 26445649) B26445649
theorem B3484271 : Blo 1833618 3484271 := bstep (se 1 (by rfl) ⟨2613203, by rfl⟩ : syracuseStep 3484271 = 5226407) B5226407
theorem B7834279 : Blo 1833618 7834279 := bstep (se 1 (by rfl) ⟨5875709, by rfl⟩ : syracuseStep 7834279 = 11751419) B11751419
theorem B35728235 : Blo 1833618 35728235 := bstep (se 1 (by rfl) ⟨26796176, by rfl⟩ : syracuseStep 35728235 = 53592353) B53592353
theorem B6966263 : Blo 1833618 6966263 := bstep (se 1 (by rfl) ⟨5224697, by rfl⟩ : syracuseStep 6966263 = 10449395) B10449395
theorem B2485243 : Blo 1833618 2485243 := bstep (se 1 (by rfl) ⟨1863932, by rfl⟩ : syracuseStep 2485243 = 3727865) B3727865
theorem B5221759 : Blo 1833618 5221759 := bstep (se 1 (by rfl) ⟨3916319, by rfl⟩ : syracuseStep 5221759 = 7832639) B7832639
theorem B5877119 : Blo 1833618 5877119 := bstep (se 1 (by rfl) ⟨4407839, by rfl⟩ : syracuseStep 5877119 = 8815679) B8815679
theorem B3919259 : Blo 1833618 3919259 := bstep (se 1 (by rfl) ⟨2939444, by rfl⟩ : syracuseStep 3919259 = 5878889) B5878889
theorem B6967235 : Blo 1833618 6967235 := bstep (se 1 (by rfl) ⟨5225426, by rfl⟩ : syracuseStep 6967235 = 10450853) B10450853
theorem B2322427 : Blo 1833618 2322427 := bstep (se 1 (by rfl) ⟨1741820, by rfl⟩ : syracuseStep 2322427 = 3483641) B3483641
theorem B19837007 : Blo 1833618 19837007 := bstep (se 1 (by rfl) ⟨14877755, by rfl⟩ : syracuseStep 19837007 = 29755511) B29755511
theorem B6967403 : Blo 1833618 6967403 := bstep (se 1 (by rfl) ⟨5225552, by rfl⟩ : syracuseStep 6967403 = 10451105) B10451105
theorem B6967417 : Blo 1833618 6967417 := bstep (se 2 (by rfl) ⟨2612781, by rfl⟩ : syracuseStep 6967417 = 5225563) B5225563
theorem B4960399 : Blo 1833618 4960399 := bstep (se 1 (by rfl) ⟨3720299, by rfl⟩ : syracuseStep 4960399 = 7440599) B7440599
theorem B6189263 : Blo 1833618 6189263 := bstep (se 1 (by rfl) ⟨4641947, by rfl⟩ : syracuseStep 6189263 = 9283895) B9283895
theorem B3920147 : Blo 1833618 3920147 := bstep (se 1 (by rfl) ⟨2940110, by rfl⟩ : syracuseStep 3920147 = 5880221) B5880221
theorem B10195267 : Blo 1833618 10195267 := bstep (se 1 (by rfl) ⟨7646450, by rfl⟩ : syracuseStep 10195267 = 15292901) B15292901
theorem B42946913 : Blo 1833618 42946913 := bstep (se 2 (by rfl) ⟨16105092, by rfl⟩ : syracuseStep 42946913 = 32210185) B32210185
theorem B25440763 : Blo 1833618 25440763 := bstep (se 1 (by rfl) ⟨19080572, by rfl⟩ : syracuseStep 25440763 = 38161145) B38161145
theorem B4641583 : Blo 1833618 4641583 := bstep (se 1 (by rfl) ⟨3481187, by rfl⟩ : syracuseStep 4641583 = 6962375) B6962375
theorem B8811355 : Blo 1833618 8811355 := bstep (se 1 (by rfl) ⟨6608516, by rfl⟩ : syracuseStep 8811355 = 13217033) B13217033
theorem B16741241 : Blo 1833618 16741241 := bstep (se 2 (by rfl) ⟨6277965, by rfl⟩ : syracuseStep 16741241 = 12555931) B12555931
theorem B4125743 : Blo 1833618 4125743 := bstep (se 1 (by rfl) ⟨3094307, by rfl⟩ : syracuseStep 4125743 = 6188615) B6188615
theorem B6190235 : Blo 1833618 6190235 := bstep (se 1 (by rfl) ⟨4642676, by rfl⟩ : syracuseStep 6190235 = 9285353) B9285353
theorem B5879375 : Blo 1833618 5879375 := bstep (se 1 (by rfl) ⟨4409531, by rfl⟩ : syracuseStep 5879375 = 8819063) B8819063
theorem B4126535 : Blo 1833618 4126535 := bstep (se 1 (by rfl) ⟨3094901, by rfl⟩ : syracuseStep 4126535 = 6189803) B6189803
theorem B11753417 : Blo 1833618 11753417 := bstep (se 2 (by rfl) ⟨4407531, by rfl⟩ : syracuseStep 11753417 = 8815063) B8815063
theorem B4126715 : Blo 1833618 4126715 := bstep (se 1 (by rfl) ⟨3095036, by rfl⟩ : syracuseStep 4126715 = 6190073) B6190073
theorem B2750459 : Blo 1833618 2750459 := bstep (se 1 (by rfl) ⟨2062844, by rfl⟩ : syracuseStep 2750459 = 4125689) B4125689
theorem B2750519 : Blo 1833618 2750519 := bstep (se 1 (by rfl) ⟨2062889, by rfl⟩ : syracuseStep 2750519 = 4125779) B4125779
theorem B3094591 : Blo 1833618 3094591 := bstep (se 1 (by rfl) ⟨2320943, by rfl⟩ : syracuseStep 3094591 = 4641887) B4641887
theorem B2750585 : Blo 1833618 2750585 := bstep (se 2 (by rfl) ⟨1031469, by rfl⟩ : syracuseStep 2750585 = 2062939) B2062939
theorem B4126841 : Blo 1833618 4126841 := bstep (se 2 (by rfl) ⟨1547565, by rfl⟩ : syracuseStep 4126841 = 3095131) B3095131
theorem B2750639 : Blo 1833618 2750639 := bstep (se 1 (by rfl) ⟨2062979, by rfl⟩ : syracuseStep 2750639 = 4125959) B4125959
theorem B4126895 : Blo 1833618 4126895 := bstep (se 1 (by rfl) ⟨3095171, by rfl⟩ : syracuseStep 4126895 = 6190343) B6190343
theorem B2750879 : Blo 1833618 2750879 := bstep (se 1 (by rfl) ⟨2063159, by rfl⟩ : syracuseStep 2750879 = 4126319) B4126319
theorem B3717623 : Blo 1833618 3717623 := bstep (se 1 (by rfl) ⟨2788217, by rfl⟩ : syracuseStep 3717623 = 5576435) B5576435
theorem B2750969 : Blo 1833618 2750969 := bstep (se 2 (by rfl) ⟨1031613, by rfl⟩ : syracuseStep 2750969 = 2063227) B2063227
theorem B4127543 : Blo 1833618 4127543 := bstep (se 1 (by rfl) ⟨3095657, by rfl⟩ : syracuseStep 4127543 = 6191315) B6191315
theorem B1833951 : Blo 1833618 1833951 := bstep (se 1 (by rfl) ⟨1375463, by rfl⟩ : syracuseStep 1833951 = 2750927) B2750927
theorem B2751455 : Blo 1833618 2751455 := bstep (se 1 (by rfl) ⟨2063591, by rfl⟩ : syracuseStep 2751455 = 4127183) B4127183
theorem B4127723 : Blo 1833618 4127723 := bstep (se 1 (by rfl) ⟨3095792, by rfl⟩ : syracuseStep 4127723 = 6191585) B6191585
theorem B1834011 : Blo 1833618 1834011 := bstep (se 1 (by rfl) ⟨1375508, by rfl⟩ : syracuseStep 1834011 = 2751017) B2751017
theorem B2751515 : Blo 1833618 2751515 := bstep (se 1 (by rfl) ⟨2063636, by rfl⟩ : syracuseStep 2751515 = 4127273) B4127273
theorem B10443815 : Blo 1833618 10443815 := bstep (se 1 (by rfl) ⟨7832861, by rfl⟩ : syracuseStep 10443815 = 15665723) B15665723
theorem B26442881 : Blo 1833618 26442881 := bstep (se 2 (by rfl) ⟨9916080, by rfl⟩ : syracuseStep 26442881 = 19832161) B19832161
theorem B1834139 : Blo 1833618 1834139 := bstep (se 1 (by rfl) ⟨1375604, by rfl⟩ : syracuseStep 1834139 = 2751209) B2751209
theorem B2063515 : Blo 1833618 2063515 := bstep (se 1 (by rfl) ⟨1547636, by rfl⟩ : syracuseStep 2063515 = 3095273) B3095273
theorem B3095759 : Blo 1833618 3095759 := bstep (se 1 (by rfl) ⟨2321819, by rfl⟩ : syracuseStep 3095759 = 4643639) B4643639
theorem B22314295 : Blo 1833618 22314295 := bstep (se 1 (by rfl) ⟨16735721, by rfl⟩ : syracuseStep 22314295 = 33471443) B33471443
theorem B1834395 : Blo 1833618 1834395 := bstep (se 1 (by rfl) ⟨1375796, by rfl⟩ : syracuseStep 1834395 = 2751593) B2751593
theorem B2751899 : Blo 1833618 2751899 := bstep (se 1 (by rfl) ⟨2063924, by rfl⟩ : syracuseStep 2751899 = 4127849) B4127849
theorem B5225917 : Blo 1833618 5225917 := bstep (se 3 (by rfl) ⟨979859, by rfl⟩ : syracuseStep 5225917 = 1959719) B1959719
theorem B5225951 : Blo 1833618 5225951 := bstep (se 1 (by rfl) ⟨3919463, by rfl⟩ : syracuseStep 5225951 = 7838927) B7838927
theorem B2751977 : Blo 1833618 2751977 := bstep (se 2 (by rfl) ⟨1031991, by rfl⟩ : syracuseStep 2751977 = 2063983) B2063983
theorem B1834479 : Blo 1833618 1834479 := bstep (se 1 (by rfl) ⟨1375859, by rfl⟩ : syracuseStep 1834479 = 2751719) B2751719
theorem B2751983 : Blo 1833618 2751983 := bstep (se 1 (by rfl) ⟨2063987, by rfl⟩ : syracuseStep 2751983 = 4127975) B4127975
theorem B42376715 : Blo 1833618 42376715 := bstep (se 1 (by rfl) ⟨31782536, by rfl⟩ : syracuseStep 42376715 = 63565073) B63565073
theorem B25099865 : Blo 1833618 25099865 := bstep (se 2 (by rfl) ⟨9412449, by rfl⟩ : syracuseStep 25099865 = 18824899) B18824899
theorem B2752121 : Blo 1833618 2752121 := bstep (se 2 (by rfl) ⟨1032045, by rfl⟩ : syracuseStep 2752121 = 2064091) B2064091
theorem B1834815 : Blo 1833618 1834815 := bstep (se 1 (by rfl) ⟨1376111, by rfl⟩ : syracuseStep 1834815 = 2752223) B2752223
theorem B2752319 : Blo 1833618 2752319 := bstep (se 1 (by rfl) ⟨2064239, by rfl⟩ : syracuseStep 2752319 = 4128479) B4128479
theorem B1834843 : Blo 1833618 1834843 := bstep (se 1 (by rfl) ⟨1376132, by rfl⟩ : syracuseStep 1834843 = 2752265) B2752265
theorem B7839575 : Blo 1833618 7839575 := bstep (se 1 (by rfl) ⟨5879681, by rfl⟩ : syracuseStep 7839575 = 11759363) B11759363
theorem B2752367 : Blo 1833618 2752367 := bstep (se 1 (by rfl) ⟨2064275, by rfl⟩ : syracuseStep 2752367 = 4128551) B4128551
theorem B4128623 : Blo 1833618 4128623 := bstep (se 1 (by rfl) ⟨3096467, by rfl⟩ : syracuseStep 4128623 = 6192935) B6192935
theorem B7946191 : Blo 1833618 7946191 := bstep (se 1 (by rfl) ⟨5959643, by rfl⟩ : syracuseStep 7946191 = 11919287) B11919287
theorem B4644935 : Blo 1833618 4644935 := bstep (se 1 (by rfl) ⟨3483701, by rfl⟩ : syracuseStep 4644935 = 6967403) B6967403
theorem B9289889 : Blo 1833618 9289889 := bstep (se 2 (by rfl) ⟨3483708, by rfl⟩ : syracuseStep 9289889 = 6967417) B6967417
theorem B2613431 : Blo 1833618 2613431 := bstep (se 1 (by rfl) ⟨1960073, by rfl⟩ : syracuseStep 2613431 = 3920147) B3920147
theorem B6193367 : Blo 1833618 6193367 := bstep (se 1 (by rfl) ⟨4645025, by rfl⟩ : syracuseStep 6193367 = 9290051) B9290051
theorem B28631275 : Blo 1833618 28631275 := bstep (se 1 (by rfl) ⟨21473456, by rfl⟩ : syracuseStep 28631275 = 42946913) B42946913
theorem B2064703 : Blo 1833618 2064703 := bstep (se 1 (by rfl) ⟨1548527, by rfl⟩ : syracuseStep 2064703 = 3097055) B3097055
theorem B4129127 : Blo 1833618 4129127 := bstep (se 1 (by rfl) ⟨3096845, by rfl⟩ : syracuseStep 4129127 = 6193691) B6193691
theorem B1835367 : Blo 1833618 1835367 := bstep (se 1 (by rfl) ⟨1376525, by rfl⟩ : syracuseStep 1835367 = 2753051) B2753051
theorem B13926815 : Blo 1833618 13926815 := bstep (se 1 (by rfl) ⟨10445111, by rfl⟩ : syracuseStep 13926815 = 20890223) B20890223
theorem B1835487 : Blo 1833618 1835487 := bstep (se 1 (by rfl) ⟨1376615, by rfl⟩ : syracuseStep 1835487 = 2753231) B2753231
theorem B1835567 : Blo 1833618 1835567 := bstep (se 1 (by rfl) ⟨1376675, by rfl⟩ : syracuseStep 1835567 = 2753351) B2753351
theorem B1835611 : Blo 1833618 1835611 := bstep (se 1 (by rfl) ⟨1376708, by rfl⟩ : syracuseStep 1835611 = 2753417) B2753417
theorem B71500411 : Blo 1833618 71500411 := bstep (se 1 (by rfl) ⟨53625308, by rfl⟩ : syracuseStep 71500411 = 107250617) B107250617
theorem B2753279 : Blo 1833618 2753279 := bstep (se 1 (by rfl) ⟨2064959, by rfl⟩ : syracuseStep 2753279 = 4129919) B4129919
theorem B10445705 : Blo 1833618 10445705 := bstep (se 2 (by rfl) ⟨3917139, by rfl⟩ : syracuseStep 10445705 = 7834279) B7834279
theorem B3916883 : Blo 1833618 3916883 := bstep (se 1 (by rfl) ⟨2937662, by rfl⟩ : syracuseStep 3916883 = 5875325) B5875325
theorem B11748473 : Blo 1833618 11748473 := bstep (se 2 (by rfl) ⟨4405677, by rfl⟩ : syracuseStep 11748473 = 8811355) B8811355
theorem B9913661 : Blo 1833618 9913661 := bstep (se 3 (by rfl) ⟨1858811, by rfl⟩ : syracuseStep 9913661 = 3717623) B3717623
theorem B6194825 : Blo 1833618 6194825 := bstep (se 2 (by rfl) ⟨2323059, by rfl⟩ : syracuseStep 6194825 = 4646119) B4646119
theorem B3918079 : Blo 1833618 3918079 := bstep (se 1 (by rfl) ⟨2938559, by rfl⟩ : syracuseStep 3918079 = 5877119) B5877119
theorem B3483967 : Blo 1833618 3483967 := bstep (se 1 (by rfl) ⟨2612975, by rfl⟩ : syracuseStep 3483967 = 5225951) B5225951
theorem B4644175 : Blo 1833618 4644175 := bstep (se 1 (by rfl) ⟨3483131, by rfl⟩ : syracuseStep 4644175 = 6966263) B6966263
theorem B42379685 : Blo 1833618 42379685 := bstep (se 4 (by rfl) ⟨3973095, by rfl⟩ : syracuseStep 42379685 = 7946191) B7946191
theorem B13224671 : Blo 1833618 13224671 := bstep (se 1 (by rfl) ⟨9918503, by rfl⟩ : syracuseStep 13224671 = 19837007) B19837007
theorem B6613865 : Blo 1833618 6613865 := bstep (se 2 (by rfl) ⟨2480199, by rfl⟩ : syracuseStep 6613865 = 4960399) B4960399
theorem B42937289 : Blo 1833618 42937289 := bstep (se 2 (by rfl) ⟨16101483, by rfl⟩ : syracuseStep 42937289 = 32202967) B32202967
theorem B13593689 : Blo 1833618 13593689 := bstep (se 2 (by rfl) ⟨5097633, by rfl⟩ : syracuseStep 13593689 = 10195267) B10195267
theorem B11160827 : Blo 1833618 11160827 := bstep (se 1 (by rfl) ⟨8370620, by rfl⟩ : syracuseStep 11160827 = 16741241) B16741241
theorem B5959019 : Blo 1833618 5959019 := bstep (se 1 (by rfl) ⟨4469264, by rfl⟩ : syracuseStep 5959019 = 8938529) B8938529
theorem B3919583 : Blo 1833618 3919583 := bstep (se 1 (by rfl) ⟨2939687, by rfl⟩ : syracuseStep 3919583 = 5879375) B5879375
theorem B6188777 : Blo 1833618 6188777 := bstep (se 2 (by rfl) ⟨2320791, by rfl⟩ : syracuseStep 6188777 = 4641583) B4641583
theorem B29749031 : Blo 1833618 29749031 := bstep (se 1 (by rfl) ⟨22311773, by rfl⟩ : syracuseStep 29749031 = 44623547) B44623547
theorem B7835611 : Blo 1833618 7835611 := bstep (se 1 (by rfl) ⟨5876708, by rfl⟩ : syracuseStep 7835611 = 11753417) B11753417
theorem B3313657 : Blo 1833618 3313657 := bstep (se 2 (by rfl) ⟨1242621, by rfl⟩ : syracuseStep 3313657 = 2485243) B2485243
theorem B14872571 : Blo 1833618 14872571 := bstep (se 1 (by rfl) ⟨11154428, by rfl⟩ : syracuseStep 14872571 = 22308857) B22308857
theorem B23507243 : Blo 1833618 23507243 := bstep (se 1 (by rfl) ⟨17630432, by rfl⟩ : syracuseStep 23507243 = 35260865) B35260865
theorem B2322847 : Blo 1833618 2322847 := bstep (se 1 (by rfl) ⟨1742135, by rfl⟩ : syracuseStep 2322847 = 3484271) B3484271
theorem B23818823 : Blo 1833618 23818823 := bstep (se 1 (by rfl) ⟨17864117, by rfl⟩ : syracuseStep 23818823 = 35728235) B35728235
theorem B6967889 : Blo 1833618 6967889 := bstep (se 2 (by rfl) ⟨2612958, by rfl⟩ : syracuseStep 6967889 = 5225917) B5225917
theorem B28251143 : Blo 1833618 28251143 := bstep (se 1 (by rfl) ⟨21188357, by rfl⟩ : syracuseStep 28251143 = 42376715) B42376715
theorem B16733243 : Blo 1833618 16733243 := bstep (se 1 (by rfl) ⟨12549932, by rfl⟩ : syracuseStep 16733243 = 25099865) B25099865
theorem B4126121 : Blo 1833618 4126121 := bstep (se 2 (by rfl) ⟨1547295, by rfl⟩ : syracuseStep 4126121 = 3094591) B3094591
theorem B4126175 : Blo 1833618 4126175 := bstep (se 1 (by rfl) ⟨3094631, by rfl⟩ : syracuseStep 4126175 = 6189263) B6189263
theorem B14882399 : Blo 1833618 14882399 := bstep (se 1 (by rfl) ⟨11161799, by rfl⟩ : syracuseStep 14882399 = 22323599) B22323599
theorem B31348457 : Blo 1833618 31348457 := bstep (se 2 (by rfl) ⟨11755671, by rfl⟩ : syracuseStep 31348457 = 23511343) B23511343
theorem B33921017 : Blo 1833618 33921017 := bstep (se 2 (by rfl) ⟨12720381, by rfl⟩ : syracuseStep 33921017 = 25440763) B25440763
theorem B2750495 : Blo 1833618 2750495 := bstep (se 1 (by rfl) ⟨2062871, by rfl⟩ : syracuseStep 2750495 = 4125743) B4125743
theorem B35264555 : Blo 1833618 35264555 := bstep (se 1 (by rfl) ⟨26448416, by rfl⟩ : syracuseStep 35264555 = 52896833) B52896833
theorem B4126823 : Blo 1833618 4126823 := bstep (se 1 (by rfl) ⟨3095117, by rfl⟩ : syracuseStep 4126823 = 6190235) B6190235
theorem B4642991 : Blo 1833618 4642991 := bstep (se 1 (by rfl) ⟨3482243, by rfl⟩ : syracuseStep 4642991 = 6964487) B6964487
theorem B3096569 : Blo 1833618 3096569 := bstep (se 2 (by rfl) ⟨1161213, by rfl⟩ : syracuseStep 3096569 = 2322427) B2322427
theorem B2751023 : Blo 1833618 2751023 := bstep (se 1 (by rfl) ⟨2063267, by rfl⟩ : syracuseStep 2751023 = 4126535) B4126535
theorem B31775333 : Blo 1833618 31775333 := bstep (se 4 (by rfl) ⟨2978937, by rfl⟩ : syracuseStep 31775333 = 5957875) B5957875
theorem B1833639 : Blo 1833618 1833639 := bstep (se 1 (by rfl) ⟨1375229, by rfl⟩ : syracuseStep 1833639 = 2750459) B2750459
theorem B2751143 : Blo 1833618 2751143 := bstep (se 1 (by rfl) ⟨2063357, by rfl⟩ : syracuseStep 2751143 = 4126715) B4126715
theorem B1833679 : Blo 1833618 1833679 := bstep (se 1 (by rfl) ⟨1375259, by rfl⟩ : syracuseStep 1833679 = 2750519) B2750519
theorem B1833723 : Blo 1833618 1833723 := bstep (se 1 (by rfl) ⟨1375292, by rfl⟩ : syracuseStep 1833723 = 2750585) B2750585
theorem B2751227 : Blo 1833618 2751227 := bstep (se 1 (by rfl) ⟨2063420, by rfl⟩ : syracuseStep 2751227 = 4126841) B4126841
theorem B1833759 : Blo 1833618 1833759 := bstep (se 1 (by rfl) ⟨1375319, by rfl⟩ : syracuseStep 1833759 = 2750639) B2750639
theorem B2751263 : Blo 1833618 2751263 := bstep (se 1 (by rfl) ⟨2063447, by rfl⟩ : syracuseStep 2751263 = 4126895) B4126895
theorem B2751353 : Blo 1833618 2751353 := bstep (se 2 (by rfl) ⟨1031757, by rfl⟩ : syracuseStep 2751353 = 2063515) B2063515
theorem B1833919 : Blo 1833618 1833919 := bstep (se 1 (by rfl) ⟨1375439, by rfl⟩ : syracuseStep 1833919 = 2750879) B2750879
theorem B1833979 : Blo 1833618 1833979 := bstep (se 1 (by rfl) ⟨1375484, by rfl⟩ : syracuseStep 1833979 = 2750969) B2750969
theorem B29752393 : Blo 1833618 29752393 := bstep (se 2 (by rfl) ⟨11157147, by rfl⟩ : syracuseStep 29752393 = 22314295) B22314295
theorem B6962345 : Blo 1833618 6962345 := bstep (se 2 (by rfl) ⟨2610879, by rfl⟩ : syracuseStep 6962345 = 5221759) B5221759
theorem B2751695 : Blo 1833618 2751695 := bstep (se 1 (by rfl) ⟨2063771, by rfl⟩ : syracuseStep 2751695 = 4127543) B4127543
theorem B1834303 : Blo 1833618 1834303 := bstep (se 1 (by rfl) ⟨1375727, by rfl⟩ : syracuseStep 1834303 = 2751455) B2751455
theorem B2751815 : Blo 1833618 2751815 := bstep (se 1 (by rfl) ⟨2063861, by rfl⟩ : syracuseStep 2751815 = 4127723) B4127723
theorem B1834343 : Blo 1833618 1834343 := bstep (se 1 (by rfl) ⟨1375757, by rfl⟩ : syracuseStep 1834343 = 2751515) B2751515
theorem B6962543 : Blo 1833618 6962543 := bstep (se 1 (by rfl) ⟨5221907, by rfl⟩ : syracuseStep 6962543 = 10443815) B10443815
theorem B17628587 : Blo 1833618 17628587 := bstep (se 1 (by rfl) ⟨13221440, by rfl⟩ : syracuseStep 17628587 = 26442881) B26442881
theorem B2063839 : Blo 1833618 2063839 := bstep (se 1 (by rfl) ⟨1547879, by rfl⟩ : syracuseStep 2063839 = 3095759) B3095759
theorem B1834599 : Blo 1833618 1834599 := bstep (se 1 (by rfl) ⟨1375949, by rfl⟩ : syracuseStep 1834599 = 2751899) B2751899
theorem B2612839 : Blo 1833618 2612839 := bstep (se 1 (by rfl) ⟨1959629, by rfl⟩ : syracuseStep 2612839 = 3919259) B3919259
theorem B1834651 : Blo 1833618 1834651 := bstep (se 1 (by rfl) ⟨1375988, by rfl⟩ : syracuseStep 1834651 = 2751977) B2751977
theorem B1834655 : Blo 1833618 1834655 := bstep (se 1 (by rfl) ⟨1375991, by rfl⟩ : syracuseStep 1834655 = 2751983) B2751983
theorem B1834747 : Blo 1833618 1834747 := bstep (se 1 (by rfl) ⟨1376060, by rfl⟩ : syracuseStep 1834747 = 2752121) B2752121
theorem B1834879 : Blo 1833618 1834879 := bstep (se 1 (by rfl) ⟨1376159, by rfl⟩ : syracuseStep 1834879 = 2752319) B2752319
theorem B5226383 : Blo 1833618 5226383 := bstep (se 1 (by rfl) ⟨3919787, by rfl⟩ : syracuseStep 5226383 = 7839575) B7839575
theorem B1834911 : Blo 1833618 1834911 := bstep (se 1 (by rfl) ⟨1376183, by rfl⟩ : syracuseStep 1834911 = 2752367) B2752367
theorem B2752415 : Blo 1833618 2752415 := bstep (se 1 (by rfl) ⟨2064311, by rfl⟩ : syracuseStep 2752415 = 4128623) B4128623
theorem B4644823 : Blo 1833618 4644823 := bstep (se 1 (by rfl) ⟨3483617, by rfl⟩ : syracuseStep 4644823 = 6967235) B6967235
theorem B3096623 : Blo 1833618 3096623 := bstep (se 1 (by rfl) ⟨2322467, by rfl⟩ : syracuseStep 3096623 = 4644935) B4644935
theorem B6193259 : Blo 1833618 6193259 := bstep (se 1 (by rfl) ⟨4644944, by rfl⟩ : syracuseStep 6193259 = 9289889) B9289889
theorem B4128911 : Blo 1833618 4128911 := bstep (se 1 (by rfl) ⟨3096683, by rfl⟩ : syracuseStep 4128911 = 6193367) B6193367
theorem B15671495 : Blo 1833618 15671495 := bstep (se 1 (by rfl) ⟨11753621, by rfl⟩ : syracuseStep 15671495 = 23507243) B23507243
theorem B10445021 : Blo 1833618 10445021 := bstep (se 3 (by rfl) ⟨1958441, by rfl⟩ : syracuseStep 10445021 = 3916883) B3916883
theorem B2752751 : Blo 1833618 2752751 := bstep (se 1 (by rfl) ⟨2064563, by rfl⟩ : syracuseStep 2752751 = 4129127) B4129127
theorem B4645259 : Blo 1833618 4645259 := bstep (se 1 (by rfl) ⟨3483944, by rfl⟩ : syracuseStep 4645259 = 6967889) B6967889
theorem B4645289 : Blo 1833618 4645289 := bstep (se 2 (by rfl) ⟨1741983, by rfl⟩ : syracuseStep 4645289 = 3483967) B3483967
theorem B2752937 : Blo 1833618 2752937 := bstep (se 2 (by rfl) ⟨1032351, by rfl⟩ : syracuseStep 2752937 = 2064703) B2064703
theorem B1835519 : Blo 1833618 1835519 := bstep (se 1 (by rfl) ⟨1376639, by rfl⟩ : syracuseStep 1835519 = 2753279) B2753279
theorem B3097129 : Blo 1833618 3097129 := bstep (se 2 (by rfl) ⟨1161423, by rfl⟩ : syracuseStep 3097129 = 2322847) B2322847
theorem B6963803 : Blo 1833618 6963803 := bstep (se 1 (by rfl) ⟨5222852, by rfl⟩ : syracuseStep 6963803 = 10445705) B10445705
theorem B18834095 : Blo 1833618 18834095 := bstep (se 1 (by rfl) ⟨14125571, by rfl⟩ : syracuseStep 18834095 = 28251143) B28251143
theorem B7832315 : Blo 1833618 7832315 := bstep (se 1 (by rfl) ⟨5874236, by rfl⟩ : syracuseStep 7832315 = 11748473) B11748473
theorem B338936885 : Blo 1833618 338936885 := bstep (se 5 (by rfl) ⟨15887666, by rfl⟩ : syracuseStep 338936885 = 31775333) B31775333
theorem B9921599 : Blo 1833618 9921599 := bstep (se 1 (by rfl) ⟨7441199, by rfl⟩ : syracuseStep 9921599 = 14882399) B14882399
theorem B4129883 : Blo 1833618 4129883 := bstep (se 1 (by rfl) ⟨3097412, by rfl⟩ : syracuseStep 4129883 = 6194825) B6194825
theorem B20898971 : Blo 1833618 20898971 := bstep (se 1 (by rfl) ⟨15674228, by rfl⟩ : syracuseStep 20898971 = 31348457) B31348457
theorem B8816447 : Blo 1833618 8816447 := bstep (se 1 (by rfl) ⟨6612335, by rfl⟩ : syracuseStep 8816447 = 13224671) B13224671
theorem B4409243 : Blo 1833618 4409243 := bstep (se 1 (by rfl) ⟨3306932, by rfl⟩ : syracuseStep 4409243 = 6613865) B6613865
theorem B28624859 : Blo 1833618 28624859 := bstep (se 1 (by rfl) ⟨21468644, by rfl⟩ : syracuseStep 28624859 = 42937289) B42937289
theorem B9062459 : Blo 1833618 9062459 := bstep (se 1 (by rfl) ⟨6796844, by rfl⟩ : syracuseStep 9062459 = 13593689) B13593689
theorem B3483785 : Blo 1833618 3483785 := bstep (se 2 (by rfl) ⟨1306419, by rfl⟩ : syracuseStep 3483785 = 2612839) B2612839
theorem B7440551 : Blo 1833618 7440551 := bstep (se 1 (by rfl) ⟨5580413, by rfl⟩ : syracuseStep 7440551 = 11160827) B11160827
theorem B13937021 : Blo 1833618 13937021 := bstep (se 3 (by rfl) ⟨2613191, by rfl⟩ : syracuseStep 13937021 = 5226383) B5226383
theorem B10447481 : Blo 1833618 10447481 := bstep (se 2 (by rfl) ⟨3917805, by rfl⟩ : syracuseStep 10447481 = 7835611) B7835611
theorem B4418209 : Blo 1833618 4418209 := bstep (se 2 (by rfl) ⟨1656828, by rfl⟩ : syracuseStep 4418209 = 3313657) B3313657
theorem B9915047 : Blo 1833618 9915047 := bstep (se 1 (by rfl) ⟨7436285, by rfl⟩ : syracuseStep 9915047 = 14872571) B14872571
theorem B9284543 : Blo 1833618 9284543 := bstep (se 1 (by rfl) ⟨6963407, by rfl⟩ : syracuseStep 9284543 = 13926815) B13926815
theorem B15879215 : Blo 1833618 15879215 := bstep (se 1 (by rfl) ⟨11909411, by rfl⟩ : syracuseStep 15879215 = 23818823) B23818823
theorem B22614011 : Blo 1833618 22614011 := bstep (se 1 (by rfl) ⟨16960508, by rfl⟩ : syracuseStep 22614011 = 33921017) B33921017
theorem B39669857 : Blo 1833618 39669857 := bstep (se 2 (by rfl) ⟨14876196, by rfl⟩ : syracuseStep 39669857 = 29752393) B29752393
theorem B4641563 : Blo 1833618 4641563 := bstep (se 1 (by rfl) ⟨3481172, by rfl⟩ : syracuseStep 4641563 = 6962345) B6962345
theorem B610800533 : Blo 1833618 610800533 := bstep (se 6 (by rfl) ⟨14315637, by rfl⟩ : syracuseStep 610800533 = 28631275) B28631275
theorem B4641695 : Blo 1833618 4641695 := bstep (se 1 (by rfl) ⟨3481271, by rfl⟩ : syracuseStep 4641695 = 6962543) B6962543
theorem B11752391 : Blo 1833618 11752391 := bstep (se 1 (by rfl) ⟨8814293, by rfl⟩ : syracuseStep 11752391 = 17628587) B17628587
theorem B4125851 : Blo 1833618 4125851 := bstep (se 1 (by rfl) ⟨3094388, by rfl⟩ : syracuseStep 4125851 = 6188777) B6188777
theorem B5224105 : Blo 1833618 5224105 := bstep (se 2 (by rfl) ⟨1959039, by rfl⟩ : syracuseStep 5224105 = 3918079) B3918079
theorem B6969149 : Blo 1833618 6969149 := bstep (se 3 (by rfl) ⟨1306715, by rfl⟩ : syracuseStep 6969149 = 2613431) B2613431
theorem B381335525 : Blo 1833618 381335525 := bstep (se 4 (by rfl) ⟨35750205, by rfl⟩ : syracuseStep 381335525 = 71500411) B71500411
theorem B11155495 : Blo 1833618 11155495 := bstep (se 1 (by rfl) ⟨8366621, by rfl⟩ : syracuseStep 11155495 = 16733243) B16733243
theorem B6609107 : Blo 1833618 6609107 := bstep (se 1 (by rfl) ⟨4956830, by rfl⟩ : syracuseStep 6609107 = 9913661) B9913661
theorem B2750747 : Blo 1833618 2750747 := bstep (se 1 (by rfl) ⟨2063060, by rfl⟩ : syracuseStep 2750747 = 4126121) B4126121
theorem B15890717 : Blo 1833618 15890717 := bstep (se 3 (by rfl) ⟨2979509, by rfl⟩ : syracuseStep 15890717 = 5959019) B5959019
theorem B2750783 : Blo 1833618 2750783 := bstep (se 1 (by rfl) ⟨2063087, by rfl⟩ : syracuseStep 2750783 = 4126175) B4126175
theorem B1833663 : Blo 1833618 1833663 := bstep (se 1 (by rfl) ⟨1375247, by rfl⟩ : syracuseStep 1833663 = 2750495) B2750495
theorem B23509703 : Blo 1833618 23509703 := bstep (se 1 (by rfl) ⟨17632277, by rfl⟩ : syracuseStep 23509703 = 35264555) B35264555
theorem B2751215 : Blo 1833618 2751215 := bstep (se 1 (by rfl) ⟨2063411, by rfl⟩ : syracuseStep 2751215 = 4126823) B4126823
theorem B3095327 : Blo 1833618 3095327 := bstep (se 1 (by rfl) ⟨2321495, by rfl⟩ : syracuseStep 3095327 = 4642991) B4642991
theorem B28253123 : Blo 1833618 28253123 := bstep (se 1 (by rfl) ⟨21189842, by rfl⟩ : syracuseStep 28253123 = 42379685) B42379685
theorem B2064379 : Blo 1833618 2064379 := bstep (se 1 (by rfl) ⟨1548284, by rfl⟩ : syracuseStep 2064379 = 3096569) B3096569
theorem B1834015 : Blo 1833618 1834015 := bstep (se 1 (by rfl) ⟨1375511, by rfl⟩ : syracuseStep 1834015 = 2751023) B2751023
theorem B6192233 : Blo 1833618 6192233 := bstep (se 2 (by rfl) ⟨2322087, by rfl⟩ : syracuseStep 6192233 = 4644175) B4644175
theorem B1834095 : Blo 1833618 1834095 := bstep (se 1 (by rfl) ⟨1375571, by rfl⟩ : syracuseStep 1834095 = 2751143) B2751143
theorem B1834151 : Blo 1833618 1834151 := bstep (se 1 (by rfl) ⟨1375613, by rfl⟩ : syracuseStep 1834151 = 2751227) B2751227
theorem B1834175 : Blo 1833618 1834175 := bstep (se 1 (by rfl) ⟨1375631, by rfl⟩ : syracuseStep 1834175 = 2751263) B2751263
theorem B1834235 : Blo 1833618 1834235 := bstep (se 1 (by rfl) ⟨1375676, by rfl⟩ : syracuseStep 1834235 = 2751353) B2751353
theorem B2751785 : Blo 1833618 2751785 := bstep (se 2 (by rfl) ⟨1031919, by rfl⟩ : syracuseStep 2751785 = 2063839) B2063839
theorem B1834463 : Blo 1833618 1834463 := bstep (se 1 (by rfl) ⟨1375847, by rfl⟩ : syracuseStep 1834463 = 2751695) B2751695
theorem B1834543 : Blo 1833618 1834543 := bstep (se 1 (by rfl) ⟨1375907, by rfl⟩ : syracuseStep 1834543 = 2751815) B2751815
theorem B2613055 : Blo 1833618 2613055 := bstep (se 1 (by rfl) ⟨1959791, by rfl⟩ : syracuseStep 2613055 = 3919583) B3919583
theorem B19832687 : Blo 1833618 19832687 := bstep (se 1 (by rfl) ⟨14874515, by rfl⟩ : syracuseStep 19832687 = 29749031) B29749031
theorem B1834943 : Blo 1833618 1834943 := bstep (se 1 (by rfl) ⟨1376207, by rfl⟩ : syracuseStep 1834943 = 2752415) B2752415
theorem B6193097 : Blo 1833618 6193097 := bstep (se 2 (by rfl) ⟨2322411, by rfl⟩ : syracuseStep 6193097 = 4644823) B4644823
theorem B2064415 : Blo 1833618 2064415 := bstep (se 1 (by rfl) ⟨1548311, by rfl⟩ : syracuseStep 2064415 = 3096623) B3096623
theorem B4128839 : Blo 1833618 4128839 := bstep (se 1 (by rfl) ⟨3096629, by rfl⟩ : syracuseStep 4128839 = 6193259) B6193259
theorem B2752607 : Blo 1833618 2752607 := bstep (se 1 (by rfl) ⟨2064455, by rfl⟩ : syracuseStep 2752607 = 4128911) B4128911
theorem B6963347 : Blo 1833618 6963347 := bstep (se 1 (by rfl) ⟨5222510, by rfl⟩ : syracuseStep 6963347 = 10445021) B10445021
theorem B1835167 : Blo 1833618 1835167 := bstep (se 1 (by rfl) ⟨1376375, by rfl⟩ : syracuseStep 1835167 = 2752751) B2752751
theorem B3096839 : Blo 1833618 3096839 := bstep (se 1 (by rfl) ⟨2322629, by rfl⟩ : syracuseStep 3096839 = 4645259) B4645259
theorem B3096859 : Blo 1833618 3096859 := bstep (se 1 (by rfl) ⟨2322644, by rfl⟩ : syracuseStep 3096859 = 4645289) B4645289
theorem B1835291 : Blo 1833618 1835291 := bstep (se 1 (by rfl) ⟨1376468, by rfl⟩ : syracuseStep 1835291 = 2752937) B2752937
theorem B407200355 : Blo 1833618 407200355 := bstep (se 1 (by rfl) ⟨305400266, by rfl⟩ : syracuseStep 407200355 = 610800533) B610800533
theorem B4129505 : Blo 1833618 4129505 := bstep (se 2 (by rfl) ⟨1548564, by rfl⟩ : syracuseStep 4129505 = 3097129) B3097129
theorem B2753255 : Blo 1833618 2753255 := bstep (se 1 (by rfl) ⟨2064941, by rfl⟩ : syracuseStep 2753255 = 4129883) B4129883
theorem B4646099 : Blo 1833618 4646099 := bstep (se 1 (by rfl) ⟨3484574, by rfl⟩ : syracuseStep 4646099 = 6969149) B6969149
theorem B254223683 : Blo 1833618 254223683 := bstep (se 1 (by rfl) ⟨190667762, by rfl⟩ : syracuseStep 254223683 = 381335525) B381335525
theorem B10593811 : Blo 1833618 10593811 := bstep (se 1 (by rfl) ⟨7945358, by rfl⟩ : syracuseStep 10593811 = 15890717) B15890717
theorem B9291347 : Blo 1833618 9291347 := bstep (se 1 (by rfl) ⟨6968510, by rfl⟩ : syracuseStep 9291347 = 13937021) B13937021
theorem B6964987 : Blo 1833618 6964987 := bstep (se 1 (by rfl) ⟨5223740, by rfl⟩ : syracuseStep 6964987 = 10447481) B10447481
theorem B15673135 : Blo 1833618 15673135 := bstep (se 1 (by rfl) ⟨11754851, by rfl⟩ : syracuseStep 15673135 = 23509703) B23509703
theorem B18835415 : Blo 1833618 18835415 := bstep (se 1 (by rfl) ⟨14126561, by rfl⟩ : syracuseStep 18835415 = 28253123) B28253123
theorem B10586143 : Blo 1833618 10586143 := bstep (se 1 (by rfl) ⟨7939607, by rfl⟩ : syracuseStep 10586143 = 15879215) B15879215
theorem B6965473 : Blo 1833618 6965473 := bstep (se 2 (by rfl) ⟨2612052, by rfl⟩ : syracuseStep 6965473 = 5224105) B5224105
theorem B3484073 : Blo 1833618 3484073 := bstep (se 2 (by rfl) ⟨1306527, by rfl⟩ : syracuseStep 3484073 = 2613055) B2613055
theorem B15076007 : Blo 1833618 15076007 := bstep (se 1 (by rfl) ⟨11307005, by rfl⟩ : syracuseStep 15076007 = 22614011) B22614011
theorem B26446571 : Blo 1833618 26446571 := bstep (se 1 (by rfl) ⟨19834928, by rfl⟩ : syracuseStep 26446571 = 39669857) B39669857
theorem B10447663 : Blo 1833618 10447663 := bstep (se 1 (by rfl) ⟨7835747, by rfl⟩ : syracuseStep 10447663 = 15671495) B15671495
theorem B5221543 : Blo 1833618 5221543 := bstep (se 1 (by rfl) ⟨3916157, by rfl⟩ : syracuseStep 5221543 = 7832315) B7832315
theorem B6614399 : Blo 1833618 6614399 := bstep (se 1 (by rfl) ⟨4960799, by rfl⟩ : syracuseStep 6614399 = 9921599) B9921599
theorem B23563781 : Blo 1833618 23563781 := bstep (se 4 (by rfl) ⟨2209104, by rfl⟩ : syracuseStep 23563781 = 4418209) B4418209
theorem B5877631 : Blo 1833618 5877631 := bstep (se 1 (by rfl) ⟨4408223, by rfl⟩ : syracuseStep 5877631 = 8816447) B8816447
theorem B19083239 : Blo 1833618 19083239 := bstep (se 1 (by rfl) ⟨14312429, by rfl⟩ : syracuseStep 19083239 = 28624859) B28624859
theorem B6041639 : Blo 1833618 6041639 := bstep (se 1 (by rfl) ⟨4531229, by rfl⟩ : syracuseStep 6041639 = 9062459) B9062459
theorem B2322523 : Blo 1833618 2322523 := bstep (se 1 (by rfl) ⟨1741892, by rfl⟩ : syracuseStep 2322523 = 3483785) B3483785
theorem B4960367 : Blo 1833618 4960367 := bstep (se 1 (by rfl) ⟨3720275, by rfl⟩ : syracuseStep 4960367 = 7440551) B7440551
theorem B6189695 : Blo 1833618 6189695 := bstep (se 1 (by rfl) ⟨4642271, by rfl⟩ : syracuseStep 6189695 = 9284543) B9284543
theorem B31339709 : Blo 1833618 31339709 := bstep (se 3 (by rfl) ⟨5876195, by rfl⟩ : syracuseStep 31339709 = 11752391) B11752391
theorem B14873993 : Blo 1833618 14873993 := bstep (se 2 (by rfl) ⟨5577747, by rfl⟩ : syracuseStep 14873993 = 11155495) B11155495
theorem B4642535 : Blo 1833618 4642535 := bstep (se 1 (by rfl) ⟨3481901, by rfl⟩ : syracuseStep 4642535 = 6963803) B6963803
theorem B12556063 : Blo 1833618 12556063 := bstep (se 1 (by rfl) ⟨9417047, by rfl⟩ : syracuseStep 12556063 = 18834095) B18834095
theorem B3094375 : Blo 1833618 3094375 := bstep (se 1 (by rfl) ⟨2320781, by rfl⟩ : syracuseStep 3094375 = 4641563) B4641563
theorem B3094463 : Blo 1833618 3094463 := bstep (se 1 (by rfl) ⟨2320847, by rfl⟩ : syracuseStep 3094463 = 4641695) B4641695
theorem B225957923 : Blo 1833618 225957923 := bstep (se 1 (by rfl) ⟨169468442, by rfl⟩ : syracuseStep 225957923 = 338936885) B338936885
theorem B2750567 : Blo 1833618 2750567 := bstep (se 1 (by rfl) ⟨2062925, by rfl⟩ : syracuseStep 2750567 = 4125851) B4125851
theorem B13932647 : Blo 1833618 13932647 := bstep (se 1 (by rfl) ⟨10449485, by rfl⟩ : syracuseStep 13932647 = 20898971) B20898971
theorem B2939495 : Blo 1833618 2939495 := bstep (se 1 (by rfl) ⟨2204621, by rfl⟩ : syracuseStep 2939495 = 4409243) B4409243
theorem B4406071 : Blo 1833618 4406071 := bstep (se 1 (by rfl) ⟨3304553, by rfl⟩ : syracuseStep 4406071 = 6609107) B6609107
theorem B1833831 : Blo 1833618 1833831 := bstep (se 1 (by rfl) ⟨1375373, by rfl⟩ : syracuseStep 1833831 = 2750747) B2750747
theorem B1833855 : Blo 1833618 1833855 := bstep (se 1 (by rfl) ⟨1375391, by rfl⟩ : syracuseStep 1833855 = 2750783) B2750783
theorem B6610031 : Blo 1833618 6610031 := bstep (se 1 (by rfl) ⟨4957523, by rfl⟩ : syracuseStep 6610031 = 9915047) B9915047
theorem B1834143 : Blo 1833618 1834143 := bstep (se 1 (by rfl) ⟨1375607, by rfl⟩ : syracuseStep 1834143 = 2751215) B2751215
theorem B2063551 : Blo 1833618 2063551 := bstep (se 1 (by rfl) ⟨1547663, by rfl⟩ : syracuseStep 2063551 = 3095327) B3095327
theorem B4128155 : Blo 1833618 4128155 := bstep (se 1 (by rfl) ⟨3096116, by rfl⟩ : syracuseStep 4128155 = 6192233) B6192233
theorem B1834523 : Blo 1833618 1834523 := bstep (se 1 (by rfl) ⟨1375892, by rfl⟩ : syracuseStep 1834523 = 2751785) B2751785
theorem B13221791 : Blo 1833618 13221791 := bstep (se 1 (by rfl) ⟨9916343, by rfl⟩ : syracuseStep 13221791 = 19832687) B19832687
theorem B4128731 : Blo 1833618 4128731 := bstep (se 1 (by rfl) ⟨3096548, by rfl⟩ : syracuseStep 4128731 = 6193097) B6193097
theorem B2752505 : Blo 1833618 2752505 := bstep (se 2 (by rfl) ⟨1032189, by rfl⟩ : syracuseStep 2752505 = 2064379) B2064379
theorem B14114857 : Blo 1833618 14114857 := bstep (se 2 (by rfl) ⟨5293071, by rfl⟩ : syracuseStep 14114857 = 10586143) B10586143
theorem B2752553 : Blo 1833618 2752553 := bstep (se 2 (by rfl) ⟨1032207, by rfl⟩ : syracuseStep 2752553 = 2064415) B2064415
theorem B2752559 : Blo 1833618 2752559 := bstep (se 1 (by rfl) ⟨2064419, by rfl⟩ : syracuseStep 2752559 = 4128839) B4128839
theorem B1835071 : Blo 1833618 1835071 := bstep (se 1 (by rfl) ⟨1376303, by rfl⟩ : syracuseStep 1835071 = 2752607) B2752607
theorem B56500325 : Blo 1833618 56500325 := bstep (se 4 (by rfl) ⟨5296905, by rfl⟩ : syracuseStep 56500325 = 10593811) B10593811
theorem B3096697 : Blo 1833618 3096697 := bstep (se 2 (by rfl) ⟨1161261, by rfl⟩ : syracuseStep 3096697 = 2322523) B2322523
theorem B2064559 : Blo 1833618 2064559 := bstep (se 1 (by rfl) ⟨1548419, by rfl⟩ : syracuseStep 2064559 = 3096839) B3096839
theorem B4129145 : Blo 1833618 4129145 := bstep (se 2 (by rfl) ⟨1548429, by rfl⟩ : syracuseStep 4129145 = 3096859) B3096859
theorem B271466903 : Blo 1833618 271466903 := bstep (se 1 (by rfl) ⟨203600177, by rfl⟩ : syracuseStep 271466903 = 407200355) B407200355
theorem B2753003 : Blo 1833618 2753003 := bstep (se 1 (by rfl) ⟨2064752, by rfl⟩ : syracuseStep 2753003 = 4129505) B4129505
theorem B1835503 : Blo 1833618 1835503 := bstep (se 1 (by rfl) ⟨1376627, by rfl⟩ : syracuseStep 1835503 = 2753255) B2753255
theorem B3097399 : Blo 1833618 3097399 := bstep (se 1 (by rfl) ⟨2323049, by rfl⟩ : syracuseStep 3097399 = 4646099) B4646099
theorem B17638397 : Blo 1833618 17638397 := bstep (se 3 (by rfl) ⟨3307199, by rfl⟩ : syracuseStep 17638397 = 6614399) B6614399
theorem B6194231 : Blo 1833618 6194231 := bstep (se 1 (by rfl) ⟨4645673, by rfl⟩ : syracuseStep 6194231 = 9291347) B9291347
theorem B5874761 : Blo 1833618 5874761 := bstep (se 2 (by rfl) ⟨2203035, by rfl⟩ : syracuseStep 5874761 = 4406071) B4406071
theorem B9290861 : Blo 1833618 9290861 := bstep (se 3 (by rfl) ⟨1742036, by rfl⟩ : syracuseStep 9290861 = 3484073) B3484073
theorem B17631047 : Blo 1833618 17631047 := bstep (se 1 (by rfl) ⟨13223285, by rfl⟩ : syracuseStep 17631047 = 26446571) B26446571
theorem B20893139 : Blo 1833618 20893139 := bstep (se 1 (by rfl) ⟨15669854, by rfl⟩ : syracuseStep 20893139 = 31339709) B31339709
theorem B9915995 : Blo 1833618 9915995 := bstep (se 1 (by rfl) ⟨7436996, by rfl⟩ : syracuseStep 9915995 = 14873993) B14873993
theorem B13930217 : Blo 1833618 13930217 := bstep (se 2 (by rfl) ⟨5223831, by rfl⟩ : syracuseStep 13930217 = 10447663) B10447663
theorem B150638615 : Blo 1833618 150638615 := bstep (se 1 (by rfl) ⟨112978961, by rfl⟩ : syracuseStep 150638615 = 225957923) B225957923
theorem B9286649 : Blo 1833618 9286649 := bstep (se 2 (by rfl) ⟨3482493, by rfl⟩ : syracuseStep 9286649 = 6964987) B6964987
theorem B15709187 : Blo 1833618 15709187 := bstep (se 1 (by rfl) ⟨11781890, by rfl⟩ : syracuseStep 15709187 = 23563781) B23563781
theorem B16741417 : Blo 1833618 16741417 := bstep (se 2 (by rfl) ⟨6278031, by rfl⟩ : syracuseStep 16741417 = 12556063) B12556063
theorem B4125833 : Blo 1833618 4125833 := bstep (se 2 (by rfl) ⟨1547187, by rfl⟩ : syracuseStep 4125833 = 3094375) B3094375
theorem B7836841 : Blo 1833618 7836841 := bstep (se 2 (by rfl) ⟨2938815, by rfl⟩ : syracuseStep 7836841 = 5877631) B5877631
theorem B3306911 : Blo 1833618 3306911 := bstep (se 1 (by rfl) ⟨2480183, by rfl⟩ : syracuseStep 3306911 = 4960367) B4960367
theorem B4642231 : Blo 1833618 4642231 := bstep (se 1 (by rfl) ⟨3481673, by rfl⟩ : syracuseStep 4642231 = 6963347) B6963347
theorem B16111037 : Blo 1833618 16111037 := bstep (se 3 (by rfl) ⟨3020819, by rfl⟩ : syracuseStep 16111037 = 6041639) B6041639
theorem B9287297 : Blo 1833618 9287297 := bstep (se 2 (by rfl) ⟨3482736, by rfl⟩ : syracuseStep 9287297 = 6965473) B6965473
theorem B4126463 : Blo 1833618 4126463 := bstep (se 1 (by rfl) ⟨3094847, by rfl⟩ : syracuseStep 4126463 = 6189695) B6189695
theorem B169482455 : Blo 1833618 169482455 := bstep (se 1 (by rfl) ⟨127111841, by rfl⟩ : syracuseStep 169482455 = 254223683) B254223683
theorem B3095023 : Blo 1833618 3095023 := bstep (se 1 (by rfl) ⟨2321267, by rfl⟩ : syracuseStep 3095023 = 4642535) B4642535
theorem B2062975 : Blo 1833618 2062975 := bstep (se 1 (by rfl) ⟨1547231, by rfl⟩ : syracuseStep 2062975 = 3094463) B3094463
theorem B12556943 : Blo 1833618 12556943 := bstep (se 1 (by rfl) ⟨9417707, by rfl⟩ : syracuseStep 12556943 = 18835415) B18835415
theorem B1833711 : Blo 1833618 1833711 := bstep (se 1 (by rfl) ⟨1375283, by rfl⟩ : syracuseStep 1833711 = 2750567) B2750567
theorem B9288431 : Blo 1833618 9288431 := bstep (se 1 (by rfl) ⟨6966323, by rfl⟩ : syracuseStep 9288431 = 13932647) B13932647
theorem B6962057 : Blo 1833618 6962057 := bstep (se 2 (by rfl) ⟨2610771, by rfl⟩ : syracuseStep 6962057 = 5221543) B5221543
theorem B2751401 : Blo 1833618 2751401 := bstep (se 2 (by rfl) ⟨1031775, by rfl⟩ : syracuseStep 2751401 = 2063551) B2063551
theorem B7838653 : Blo 1833618 7838653 := bstep (se 3 (by rfl) ⟨1469747, by rfl⟩ : syracuseStep 7838653 = 2939495) B2939495
theorem B10050671 : Blo 1833618 10050671 := bstep (se 1 (by rfl) ⟨7538003, by rfl⟩ : syracuseStep 10050671 = 15076007) B15076007
theorem B4406687 : Blo 1833618 4406687 := bstep (se 1 (by rfl) ⟨3305015, by rfl⟩ : syracuseStep 4406687 = 6610031) B6610031
theorem B2752103 : Blo 1833618 2752103 := bstep (se 1 (by rfl) ⟨2064077, by rfl⟩ : syracuseStep 2752103 = 4128155) B4128155
theorem B20897513 : Blo 1833618 20897513 := bstep (se 2 (by rfl) ⟨7836567, by rfl⟩ : syracuseStep 20897513 = 15673135) B15673135
theorem B8814527 : Blo 1833618 8814527 := bstep (se 1 (by rfl) ⟨6610895, by rfl⟩ : syracuseStep 8814527 = 13221791) B13221791
theorem B2752487 : Blo 1833618 2752487 := bstep (se 1 (by rfl) ⟨2064365, by rfl⟩ : syracuseStep 2752487 = 4128731) B4128731
theorem B12722159 : Blo 1833618 12722159 := bstep (se 1 (by rfl) ⟨9541619, by rfl⟩ : syracuseStep 12722159 = 19083239) B19083239
theorem B1835003 : Blo 1833618 1835003 := bstep (se 1 (by rfl) ⟨1376252, by rfl⟩ : syracuseStep 1835003 = 2752505) B2752505
theorem B100425743 : Blo 1833618 100425743 := bstep (se 1 (by rfl) ⟨75319307, by rfl⟩ : syracuseStep 100425743 = 150638615) B150638615
theorem B1835035 : Blo 1833618 1835035 := bstep (se 1 (by rfl) ⟨1376276, by rfl⟩ : syracuseStep 1835035 = 2752553) B2752553
theorem B1835039 : Blo 1833618 1835039 := bstep (se 1 (by rfl) ⟨1376279, by rfl⟩ : syracuseStep 1835039 = 2752559) B2752559
theorem B37666883 : Blo 1833618 37666883 := bstep (se 1 (by rfl) ⟨28250162, by rfl⟩ : syracuseStep 37666883 = 56500325) B56500325
theorem B4128929 : Blo 1833618 4128929 := bstep (se 2 (by rfl) ⟨1548348, by rfl⟩ : syracuseStep 4128929 = 3096697) B3096697
theorem B2752745 : Blo 1833618 2752745 := bstep (se 2 (by rfl) ⟨1032279, by rfl⟩ : syracuseStep 2752745 = 2064559) B2064559
theorem B2752763 : Blo 1833618 2752763 := bstep (se 1 (by rfl) ⟨2064572, by rfl⟩ : syracuseStep 2752763 = 4129145) B4129145
theorem B1835335 : Blo 1833618 1835335 := bstep (se 1 (by rfl) ⟨1376501, by rfl⟩ : syracuseStep 1835335 = 2753003) B2753003
theorem B4129487 : Blo 1833618 4129487 := bstep (se 1 (by rfl) ⟨3097115, by rfl⟩ : syracuseStep 4129487 = 6194231) B6194231
theorem B3916507 : Blo 1833618 3916507 := bstep (se 1 (by rfl) ⟨2937380, by rfl⟩ : syracuseStep 3916507 = 5874761) B5874761
theorem B6193907 : Blo 1833618 6193907 := bstep (se 1 (by rfl) ⟨4645430, by rfl⟩ : syracuseStep 6193907 = 9290861) B9290861
theorem B10740691 : Blo 1833618 10740691 := bstep (se 1 (by rfl) ⟨8055518, by rfl⟩ : syracuseStep 10740691 = 16111037) B16111037
theorem B723911741 : Blo 1833618 723911741 := bstep (se 3 (by rfl) ⟨135733451, by rfl⟩ : syracuseStep 723911741 = 271466903) B271466903
theorem B4129865 : Blo 1833618 4129865 := bstep (se 2 (by rfl) ⟨1548699, by rfl⟩ : syracuseStep 4129865 = 3097399) B3097399
theorem B47016125 : Blo 1833618 47016125 := bstep (se 3 (by rfl) ⟨8815523, by rfl⟩ : syracuseStep 47016125 = 17631047) B17631047
theorem B13928759 : Blo 1833618 13928759 := bstep (se 1 (by rfl) ⟨10446569, by rfl⟩ : syracuseStep 13928759 = 20893139) B20893139
theorem B5876351 : Blo 1833618 5876351 := bstep (se 1 (by rfl) ⟨4407263, by rfl⟩ : syracuseStep 5876351 = 8814527) B8814527
theorem B8481439 : Blo 1833618 8481439 := bstep (se 1 (by rfl) ⟨6361079, by rfl⟩ : syracuseStep 8481439 = 12722159) B12722159
theorem B18819809 : Blo 1833618 18819809 := bstep (se 2 (by rfl) ⟨7057428, by rfl⟩ : syracuseStep 18819809 = 14114857) B14114857
theorem B11758931 : Blo 1833618 11758931 := bstep (se 1 (by rfl) ⟨8819198, by rfl⟩ : syracuseStep 11758931 = 17638397) B17638397
theorem B8818429 : Blo 1833618 8818429 := bstep (se 3 (by rfl) ⟨1653455, by rfl⟩ : syracuseStep 8818429 = 3306911) B3306911
theorem B112988303 : Blo 1833618 112988303 := bstep (se 1 (by rfl) ⟨84741227, by rfl⟩ : syracuseStep 112988303 = 169482455) B169482455
theorem B10449121 : Blo 1833618 10449121 := bstep (se 2 (by rfl) ⟨3918420, by rfl⟩ : syracuseStep 10449121 = 7836841) B7836841
theorem B6189641 : Blo 1833618 6189641 := bstep (se 2 (by rfl) ⟨2321115, by rfl⟩ : syracuseStep 6189641 = 4642231) B4642231
theorem B4641371 : Blo 1833618 4641371 := bstep (se 1 (by rfl) ⟨3481028, by rfl⟩ : syracuseStep 4641371 = 6962057) B6962057
theorem B2937791 : Blo 1833618 2937791 := bstep (se 1 (by rfl) ⟨2203343, by rfl⟩ : syracuseStep 2937791 = 4406687) B4406687
theorem B9286811 : Blo 1833618 9286811 := bstep (se 1 (by rfl) ⟨6965108, by rfl⟩ : syracuseStep 9286811 = 13930217) B13930217
theorem B13931675 : Blo 1833618 13931675 := bstep (se 1 (by rfl) ⟨10448756, by rfl⟩ : syracuseStep 13931675 = 20897513) B20897513
theorem B41891165 : Blo 1833618 41891165 := bstep (se 3 (by rfl) ⟨7854593, by rfl⟩ : syracuseStep 41891165 = 15709187) B15709187
theorem B4126697 : Blo 1833618 4126697 := bstep (se 2 (by rfl) ⟨1547511, by rfl⟩ : syracuseStep 4126697 = 3095023) B3095023
theorem B6191099 : Blo 1833618 6191099 := bstep (se 1 (by rfl) ⟨4643324, by rfl⟩ : syracuseStep 6191099 = 9286649) B9286649
theorem B2750555 : Blo 1833618 2750555 := bstep (se 1 (by rfl) ⟨2062916, by rfl⟩ : syracuseStep 2750555 = 4125833) B4125833
theorem B2750633 : Blo 1833618 2750633 := bstep (se 2 (by rfl) ⟨1031487, by rfl⟩ : syracuseStep 2750633 = 2062975) B2062975
theorem B6191531 : Blo 1833618 6191531 := bstep (se 1 (by rfl) ⟨4643648, by rfl⟩ : syracuseStep 6191531 = 9287297) B9287297
theorem B2750975 : Blo 1833618 2750975 := bstep (se 1 (by rfl) ⟨2063231, by rfl⟩ : syracuseStep 2750975 = 4126463) B4126463
theorem B10451537 : Blo 1833618 10451537 := bstep (se 2 (by rfl) ⟨3919326, by rfl⟩ : syracuseStep 10451537 = 7838653) B7838653
theorem B22321889 : Blo 1833618 22321889 := bstep (se 2 (by rfl) ⟨8370708, by rfl⟩ : syracuseStep 22321889 = 16741417) B16741417
theorem B8371295 : Blo 1833618 8371295 := bstep (se 1 (by rfl) ⟨6278471, by rfl⟩ : syracuseStep 8371295 = 12556943) B12556943
theorem B6192287 : Blo 1833618 6192287 := bstep (se 1 (by rfl) ⟨4644215, by rfl⟩ : syracuseStep 6192287 = 9288431) B9288431
theorem B1834267 : Blo 1833618 1834267 := bstep (se 1 (by rfl) ⟨1375700, by rfl⟩ : syracuseStep 1834267 = 2751401) B2751401
theorem B6700447 : Blo 1833618 6700447 := bstep (se 1 (by rfl) ⟨5025335, by rfl⟩ : syracuseStep 6700447 = 10050671) B10050671
theorem B6610663 : Blo 1833618 6610663 := bstep (se 1 (by rfl) ⟨4957997, by rfl⟩ : syracuseStep 6610663 = 9915995) B9915995
theorem B1834735 : Blo 1833618 1834735 := bstep (se 1 (by rfl) ⟨1376051, by rfl⟩ : syracuseStep 1834735 = 2752103) B2752103
theorem B1834991 : Blo 1833618 1834991 := bstep (se 1 (by rfl) ⟨1376243, by rfl⟩ : syracuseStep 1834991 = 2752487) B2752487
theorem B75325535 : Blo 1833618 75325535 := bstep (se 1 (by rfl) ⟨56494151, by rfl⟩ : syracuseStep 75325535 = 112988303) B112988303
theorem B2752619 : Blo 1833618 2752619 := bstep (se 1 (by rfl) ⟨2064464, by rfl⟩ : syracuseStep 2752619 = 4128929) B4128929
theorem B1835163 : Blo 1833618 1835163 := bstep (se 1 (by rfl) ⟨1376372, by rfl⟩ : syracuseStep 1835163 = 2752745) B2752745
theorem B1835175 : Blo 1833618 1835175 := bstep (se 1 (by rfl) ⟨1376381, by rfl⟩ : syracuseStep 1835175 = 2752763) B2752763
theorem B2752991 : Blo 1833618 2752991 := bstep (se 1 (by rfl) ⟨2064743, by rfl⟩ : syracuseStep 2752991 = 4129487) B4129487
theorem B4129271 : Blo 1833618 4129271 := bstep (se 1 (by rfl) ⟨3096953, by rfl⟩ : syracuseStep 4129271 = 6193907) B6193907
theorem B1958527 : Blo 1833618 1958527 := bstep (se 1 (by rfl) ⟨1468895, by rfl⟩ : syracuseStep 1958527 = 2937791) B2937791
theorem B482607827 : Blo 1833618 482607827 := bstep (se 1 (by rfl) ⟨361955870, by rfl⟩ : syracuseStep 482607827 = 723911741) B723911741
theorem B2753243 : Blo 1833618 2753243 := bstep (se 1 (by rfl) ⟨2064932, by rfl⟩ : syracuseStep 2753243 = 4129865) B4129865
theorem B27927443 : Blo 1833618 27927443 := bstep (se 1 (by rfl) ⟨20945582, by rfl⟩ : syracuseStep 27927443 = 41891165) B41891165
theorem B14320921 : Blo 1833618 14320921 := bstep (se 2 (by rfl) ⟨5370345, by rfl⟩ : syracuseStep 14320921 = 10740691) B10740691
theorem B31344083 : Blo 1833618 31344083 := bstep (se 1 (by rfl) ⟨23508062, by rfl⟩ : syracuseStep 31344083 = 47016125) B47016125
theorem B3917567 : Blo 1833618 3917567 := bstep (se 1 (by rfl) ⟨2938175, by rfl⟩ : syracuseStep 3917567 = 5876351) B5876351
theorem B5580863 : Blo 1833618 5580863 := bstep (se 1 (by rfl) ⟨4185647, by rfl⟩ : syracuseStep 5580863 = 8371295) B8371295
theorem B35735717 : Blo 1833618 35735717 := bstep (se 4 (by rfl) ⟨3350223, by rfl⟩ : syracuseStep 35735717 = 6700447) B6700447
theorem B11757905 : Blo 1833618 11757905 := bstep (se 2 (by rfl) ⟨4409214, by rfl⟩ : syracuseStep 11757905 = 8818429) B8818429
theorem B25111255 : Blo 1833618 25111255 := bstep (se 1 (by rfl) ⟨18833441, by rfl⟩ : syracuseStep 25111255 = 37666883) B37666883
theorem B11308585 : Blo 1833618 11308585 := bstep (se 2 (by rfl) ⟨4240719, by rfl⟩ : syracuseStep 11308585 = 8481439) B8481439
theorem B5222009 : Blo 1833618 5222009 := bstep (se 2 (by rfl) ⟨1958253, by rfl⟩ : syracuseStep 5222009 = 3916507) B3916507
theorem B9285839 : Blo 1833618 9285839 := bstep (se 1 (by rfl) ⟨6964379, by rfl⟩ : syracuseStep 9285839 = 13928759) B13928759
theorem B6967691 : Blo 1833618 6967691 := bstep (se 1 (by rfl) ⟨5225768, by rfl⟩ : syracuseStep 6967691 = 10451537) B10451537
theorem B12546539 : Blo 1833618 12546539 := bstep (se 1 (by rfl) ⟨9409904, by rfl⟩ : syracuseStep 12546539 = 18819809) B18819809
theorem B14881259 : Blo 1833618 14881259 := bstep (se 1 (by rfl) ⟨11160944, by rfl⟩ : syracuseStep 14881259 = 22321889) B22321889
theorem B66950495 : Blo 1833618 66950495 := bstep (se 1 (by rfl) ⟨50212871, by rfl⟩ : syracuseStep 66950495 = 100425743) B100425743
theorem B13932161 : Blo 1833618 13932161 := bstep (se 2 (by rfl) ⟨5224560, by rfl⟩ : syracuseStep 13932161 = 10449121) B10449121
theorem B4126427 : Blo 1833618 4126427 := bstep (se 1 (by rfl) ⟨3094820, by rfl⟩ : syracuseStep 4126427 = 6189641) B6189641
theorem B3094247 : Blo 1833618 3094247 := bstep (se 1 (by rfl) ⟨2320685, by rfl⟩ : syracuseStep 3094247 = 4641371) B4641371
theorem B6191207 : Blo 1833618 6191207 := bstep (se 1 (by rfl) ⟨4643405, by rfl⟩ : syracuseStep 6191207 = 9286811) B9286811
theorem B9287783 : Blo 1833618 9287783 := bstep (se 1 (by rfl) ⟨6965837, by rfl⟩ : syracuseStep 9287783 = 13931675) B13931675
theorem B35256869 : Blo 1833618 35256869 := bstep (se 4 (by rfl) ⟨3305331, by rfl⟩ : syracuseStep 35256869 = 6610663) B6610663
theorem B2751131 : Blo 1833618 2751131 := bstep (se 1 (by rfl) ⟨2063348, by rfl⟩ : syracuseStep 2751131 = 4126697) B4126697
theorem B4127399 : Blo 1833618 4127399 := bstep (se 1 (by rfl) ⟨3095549, by rfl⟩ : syracuseStep 4127399 = 6191099) B6191099
theorem B1833703 : Blo 1833618 1833703 := bstep (se 1 (by rfl) ⟨1375277, by rfl⟩ : syracuseStep 1833703 = 2750555) B2750555
theorem B1833755 : Blo 1833618 1833755 := bstep (se 1 (by rfl) ⟨1375316, by rfl⟩ : syracuseStep 1833755 = 2750633) B2750633
theorem B4127687 : Blo 1833618 4127687 := bstep (se 1 (by rfl) ⟨3095765, by rfl⟩ : syracuseStep 4127687 = 6191531) B6191531
theorem B1833983 : Blo 1833618 1833983 := bstep (se 1 (by rfl) ⟨1375487, by rfl⟩ : syracuseStep 1833983 = 2750975) B2750975
theorem B4128191 : Blo 1833618 4128191 := bstep (se 1 (by rfl) ⟨3096143, by rfl⟩ : syracuseStep 4128191 = 6192287) B6192287
theorem B7839287 : Blo 1833618 7839287 := bstep (se 1 (by rfl) ⟨5879465, by rfl⟩ : syracuseStep 7839287 = 11758931) B11758931
theorem B50217023 : Blo 1833618 50217023 := bstep (se 1 (by rfl) ⟨37662767, by rfl⟩ : syracuseStep 50217023 = 75325535) B75325535
theorem B1835079 : Blo 1833618 1835079 := bstep (se 1 (by rfl) ⟨1376309, by rfl⟩ : syracuseStep 1835079 = 2752619) B2752619
theorem B4645127 : Blo 1833618 4645127 := bstep (se 1 (by rfl) ⟨3483845, by rfl⟩ : syracuseStep 4645127 = 6967691) B6967691
theorem B1835327 : Blo 1833618 1835327 := bstep (se 1 (by rfl) ⟨1376495, by rfl⟩ : syracuseStep 1835327 = 2752991) B2752991
theorem B8364359 : Blo 1833618 8364359 := bstep (se 1 (by rfl) ⟨6273269, by rfl⟩ : syracuseStep 8364359 = 12546539) B12546539
theorem B2752847 : Blo 1833618 2752847 := bstep (se 1 (by rfl) ⟨2064635, by rfl⟩ : syracuseStep 2752847 = 4129271) B4129271
theorem B1835495 : Blo 1833618 1835495 := bstep (se 1 (by rfl) ⟨1376621, by rfl⟩ : syracuseStep 1835495 = 2753243) B2753243
theorem B33481673 : Blo 1833618 33481673 := bstep (se 2 (by rfl) ⟨12555627, by rfl⟩ : syracuseStep 33481673 = 25111255) B25111255
theorem B39683357 : Blo 1833618 39683357 := bstep (se 3 (by rfl) ⟨7440629, by rfl⟩ : syracuseStep 39683357 = 14881259) B14881259
theorem B3720575 : Blo 1833618 3720575 := bstep (se 1 (by rfl) ⟨2790431, by rfl⟩ : syracuseStep 3720575 = 5580863) B5580863
theorem B23823811 : Blo 1833618 23823811 := bstep (se 1 (by rfl) ⟨17867858, by rfl⟩ : syracuseStep 23823811 = 35735717) B35735717
theorem B7838603 : Blo 1833618 7838603 := bstep (se 1 (by rfl) ⟨5878952, by rfl⟩ : syracuseStep 7838603 = 11757905) B11757905
theorem B23504579 : Blo 1833618 23504579 := bstep (se 1 (by rfl) ⟨17628434, by rfl⟩ : syracuseStep 23504579 = 35256869) B35256869
theorem B44633663 : Blo 1833618 44633663 := bstep (se 1 (by rfl) ⟨33475247, by rfl⟩ : syracuseStep 44633663 = 66950495) B66950495
theorem B15078113 : Blo 1833618 15078113 := bstep (se 2 (by rfl) ⟨5654292, by rfl⟩ : syracuseStep 15078113 = 11308585) B11308585
theorem B6190559 : Blo 1833618 6190559 := bstep (se 1 (by rfl) ⟨4642919, by rfl⟩ : syracuseStep 6190559 = 9285839) B9285839
theorem B321738551 : Blo 1833618 321738551 := bstep (se 1 (by rfl) ⟨241303913, by rfl⟩ : syracuseStep 321738551 = 482607827) B482607827
theorem B2611369 : Blo 1833618 2611369 := bstep (se 2 (by rfl) ⟨979263, by rfl⟩ : syracuseStep 2611369 = 1958527) B1958527
theorem B20896055 : Blo 1833618 20896055 := bstep (se 1 (by rfl) ⟨15672041, by rfl⟩ : syracuseStep 20896055 = 31344083) B31344083
theorem B9288107 : Blo 1833618 9288107 := bstep (se 1 (by rfl) ⟨6966080, by rfl⟩ : syracuseStep 9288107 = 13932161) B13932161
theorem B2750951 : Blo 1833618 2750951 := bstep (se 1 (by rfl) ⟨2063213, by rfl⟩ : syracuseStep 2750951 = 4126427) B4126427
theorem B2062831 : Blo 1833618 2062831 := bstep (se 1 (by rfl) ⟨1547123, by rfl⟩ : syracuseStep 2062831 = 3094247) B3094247
theorem B2611711 : Blo 1833618 2611711 := bstep (se 1 (by rfl) ⟨1958783, by rfl⟩ : syracuseStep 2611711 = 3917567) B3917567
theorem B4127471 : Blo 1833618 4127471 := bstep (se 1 (by rfl) ⟨3095603, by rfl⟩ : syracuseStep 4127471 = 6191207) B6191207
theorem B6191855 : Blo 1833618 6191855 := bstep (se 1 (by rfl) ⟨4643891, by rfl⟩ : syracuseStep 6191855 = 9287783) B9287783
theorem B13925357 : Blo 1833618 13925357 := bstep (se 3 (by rfl) ⟨2611004, by rfl⟩ : syracuseStep 13925357 = 5222009) B5222009
theorem B19094561 : Blo 1833618 19094561 := bstep (se 2 (by rfl) ⟨7160460, by rfl⟩ : syracuseStep 19094561 = 14320921) B14320921
theorem B1834087 : Blo 1833618 1834087 := bstep (se 1 (by rfl) ⟨1375565, by rfl⟩ : syracuseStep 1834087 = 2751131) B2751131
theorem B2751599 : Blo 1833618 2751599 := bstep (se 1 (by rfl) ⟨2063699, by rfl⟩ : syracuseStep 2751599 = 4127399) B4127399
theorem B2751791 : Blo 1833618 2751791 := bstep (se 1 (by rfl) ⟨2063843, by rfl⟩ : syracuseStep 2751791 = 4127687) B4127687
theorem B2752127 : Blo 1833618 2752127 := bstep (se 1 (by rfl) ⟨2064095, by rfl⟩ : syracuseStep 2752127 = 4128191) B4128191
theorem B5226191 : Blo 1833618 5226191 := bstep (se 1 (by rfl) ⟨3919643, by rfl⟩ : syracuseStep 5226191 = 7839287) B7839287
theorem B74473181 : Blo 1833618 74473181 := bstep (se 3 (by rfl) ⟨13963721, by rfl⟩ : syracuseStep 74473181 = 27927443) B27927443
theorem B3096751 : Blo 1833618 3096751 := bstep (se 1 (by rfl) ⟨2322563, by rfl⟩ : syracuseStep 3096751 = 4645127) B4645127
theorem B1835231 : Blo 1833618 1835231 := bstep (se 1 (by rfl) ⟨1376423, by rfl⟩ : syracuseStep 1835231 = 2752847) B2752847
theorem B10052075 : Blo 1833618 10052075 := bstep (se 1 (by rfl) ⟨7539056, by rfl⟩ : syracuseStep 10052075 = 15078113) B15078113
theorem B3482281 : Blo 1833618 3482281 := bstep (se 2 (by rfl) ⟨1305855, by rfl⟩ : syracuseStep 3482281 = 2611711) B2611711
theorem B13927301 : Blo 1833618 13927301 := bstep (se 4 (by rfl) ⟨1305684, by rfl⟩ : syracuseStep 13927301 = 2611369) B2611369
theorem B214492367 : Blo 1833618 214492367 := bstep (se 1 (by rfl) ⟨160869275, by rfl⟩ : syracuseStep 214492367 = 321738551) B321738551
theorem B9283571 : Blo 1833618 9283571 := bstep (se 1 (by rfl) ⟨6962678, by rfl⟩ : syracuseStep 9283571 = 13925357) B13925357
theorem B29755775 : Blo 1833618 29755775 := bstep (se 1 (by rfl) ⟨22316831, by rfl⟩ : syracuseStep 29755775 = 44633663) B44633663
theorem B3484127 : Blo 1833618 3484127 := bstep (se 1 (by rfl) ⟨2613095, by rfl⟩ : syracuseStep 3484127 = 5226191) B5226191
theorem B26455571 : Blo 1833618 26455571 := bstep (se 1 (by rfl) ⟨19841678, by rfl⟩ : syracuseStep 26455571 = 39683357) B39683357
theorem B13930703 : Blo 1833618 13930703 := bstep (se 1 (by rfl) ⟨10448027, by rfl⟩ : syracuseStep 13930703 = 20896055) B20896055
theorem B31765081 : Blo 1833618 31765081 := bstep (se 2 (by rfl) ⟨11911905, by rfl⟩ : syracuseStep 31765081 = 23823811) B23823811
theorem B49648787 : Blo 1833618 49648787 := bstep (se 1 (by rfl) ⟨37236590, by rfl⟩ : syracuseStep 49648787 = 74473181) B74473181
theorem B133912061 : Blo 1833618 133912061 := bstep (se 3 (by rfl) ⟨25108511, by rfl⟩ : syracuseStep 133912061 = 50217023) B50217023
theorem B5576239 : Blo 1833618 5576239 := bstep (se 1 (by rfl) ⟨4182179, by rfl⟩ : syracuseStep 5576239 = 8364359) B8364359
theorem B22321115 : Blo 1833618 22321115 := bstep (se 1 (by rfl) ⟨16740836, by rfl⟩ : syracuseStep 22321115 = 33481673) B33481673
theorem B2750441 : Blo 1833618 2750441 := bstep (se 2 (by rfl) ⟨1031415, by rfl⟩ : syracuseStep 2750441 = 2062831) B2062831
theorem B2480383 : Blo 1833618 2480383 := bstep (se 1 (by rfl) ⟨1860287, by rfl⟩ : syracuseStep 2480383 = 3720575) B3720575
theorem B4127039 : Blo 1833618 4127039 := bstep (se 1 (by rfl) ⟨3095279, by rfl⟩ : syracuseStep 4127039 = 6190559) B6190559
theorem B15669719 : Blo 1833618 15669719 := bstep (se 1 (by rfl) ⟨11752289, by rfl⟩ : syracuseStep 15669719 = 23504579) B23504579
theorem B6192071 : Blo 1833618 6192071 := bstep (se 1 (by rfl) ⟨4644053, by rfl⟩ : syracuseStep 6192071 = 9288107) B9288107
theorem B1833967 : Blo 1833618 1833967 := bstep (se 1 (by rfl) ⟨1375475, by rfl⟩ : syracuseStep 1833967 = 2750951) B2750951
theorem B2751647 : Blo 1833618 2751647 := bstep (se 1 (by rfl) ⟨2063735, by rfl⟩ : syracuseStep 2751647 = 4127471) B4127471
theorem B4127903 : Blo 1833618 4127903 := bstep (se 1 (by rfl) ⟨3095927, by rfl⟩ : syracuseStep 4127903 = 6191855) B6191855
theorem B5225735 : Blo 1833618 5225735 := bstep (se 1 (by rfl) ⟨3919301, by rfl⟩ : syracuseStep 5225735 = 7838603) B7838603
theorem B12729707 : Blo 1833618 12729707 := bstep (se 1 (by rfl) ⟨9547280, by rfl⟩ : syracuseStep 12729707 = 19094561) B19094561
theorem B1834399 : Blo 1833618 1834399 := bstep (se 1 (by rfl) ⟨1375799, by rfl⟩ : syracuseStep 1834399 = 2751599) B2751599
theorem B1834527 : Blo 1833618 1834527 := bstep (se 1 (by rfl) ⟨1375895, by rfl⟩ : syracuseStep 1834527 = 2751791) B2751791
theorem B1834751 : Blo 1833618 1834751 := bstep (se 1 (by rfl) ⟨1376063, by rfl⟩ : syracuseStep 1834751 = 2752127) B2752127
theorem B4129001 : Blo 1833618 4129001 := bstep (se 2 (by rfl) ⟨1548375, by rfl⟩ : syracuseStep 4129001 = 3096751) B3096751
theorem B6701383 : Blo 1833618 6701383 := bstep (se 1 (by rfl) ⟨5026037, by rfl⟩ : syracuseStep 6701383 = 10052075) B10052075
theorem B42353441 : Blo 1833618 42353441 := bstep (se 2 (by rfl) ⟨15882540, by rfl⟩ : syracuseStep 42353441 = 31765081) B31765081
theorem B10446479 : Blo 1833618 10446479 := bstep (se 1 (by rfl) ⟨7834859, by rfl⟩ : syracuseStep 10446479 = 15669719) B15669719
theorem B3483823 : Blo 1833618 3483823 := bstep (se 1 (by rfl) ⟨2612867, by rfl⟩ : syracuseStep 3483823 = 5225735) B5225735
theorem B9284867 : Blo 1833618 9284867 := bstep (se 1 (by rfl) ⟨6963650, by rfl⟩ : syracuseStep 9284867 = 13927301) B13927301
theorem B33099191 : Blo 1833618 33099191 := bstep (se 1 (by rfl) ⟨24824393, by rfl⟩ : syracuseStep 33099191 = 49648787) B49648787
theorem B142994911 : Blo 1833618 142994911 := bstep (se 1 (by rfl) ⟨107246183, by rfl⟩ : syracuseStep 142994911 = 214492367) B214492367
theorem B14880743 : Blo 1833618 14880743 := bstep (se 1 (by rfl) ⟨11160557, by rfl⟩ : syracuseStep 14880743 = 22321115) B22321115
theorem B6189047 : Blo 1833618 6189047 := bstep (se 1 (by rfl) ⟨4641785, by rfl⟩ : syracuseStep 6189047 = 9283571) B9283571
theorem B19837183 : Blo 1833618 19837183 := bstep (se 1 (by rfl) ⟨14877887, by rfl⟩ : syracuseStep 19837183 = 29755775) B29755775
theorem B2322751 : Blo 1833618 2322751 := bstep (se 1 (by rfl) ⟨1742063, by rfl⟩ : syracuseStep 2322751 = 3484127) B3484127
theorem B7434985 : Blo 1833618 7434985 := bstep (se 2 (by rfl) ⟨2788119, by rfl⟩ : syracuseStep 7434985 = 5576239) B5576239
theorem B9287135 : Blo 1833618 9287135 := bstep (se 1 (by rfl) ⟨6965351, by rfl⟩ : syracuseStep 9287135 = 13930703) B13930703
theorem B3307177 : Blo 1833618 3307177 := bstep (se 2 (by rfl) ⟨1240191, by rfl⟩ : syracuseStep 3307177 = 2480383) B2480383
theorem B4643041 : Blo 1833618 4643041 := bstep (se 2 (by rfl) ⟨1741140, by rfl⟩ : syracuseStep 4643041 = 3482281) B3482281
theorem B89274707 : Blo 1833618 89274707 := bstep (se 1 (by rfl) ⟨66956030, by rfl⟩ : syracuseStep 89274707 = 133912061) B133912061
theorem B1833627 : Blo 1833618 1833627 := bstep (se 1 (by rfl) ⟨1375220, by rfl⟩ : syracuseStep 1833627 = 2750441) B2750441
theorem B2751359 : Blo 1833618 2751359 := bstep (se 1 (by rfl) ⟨2063519, by rfl⟩ : syracuseStep 2751359 = 4127039) B4127039
theorem B4128047 : Blo 1833618 4128047 := bstep (se 1 (by rfl) ⟨3096035, by rfl⟩ : syracuseStep 4128047 = 6192071) B6192071
theorem B1834431 : Blo 1833618 1834431 := bstep (se 1 (by rfl) ⟨1375823, by rfl⟩ : syracuseStep 1834431 = 2751647) B2751647
theorem B2751935 : Blo 1833618 2751935 := bstep (se 1 (by rfl) ⟨2063951, by rfl⟩ : syracuseStep 2751935 = 4127903) B4127903
theorem B8486471 : Blo 1833618 8486471 := bstep (se 1 (by rfl) ⟨6364853, by rfl⟩ : syracuseStep 8486471 = 12729707) B12729707
theorem B17637047 : Blo 1833618 17637047 := bstep (se 1 (by rfl) ⟨13227785, by rfl⟩ : syracuseStep 17637047 = 26455571) B26455571
theorem B2752667 : Blo 1833618 2752667 := bstep (se 1 (by rfl) ⟨2064500, by rfl⟩ : syracuseStep 2752667 = 4129001) B4129001
theorem B4645097 : Blo 1833618 4645097 := bstep (se 2 (by rfl) ⟨1741911, by rfl⟩ : syracuseStep 4645097 = 3483823) B3483823
theorem B3097001 : Blo 1833618 3097001 := bstep (se 2 (by rfl) ⟨1161375, by rfl⟩ : syracuseStep 3097001 = 2322751) B2322751
theorem B9913313 : Blo 1833618 9913313 := bstep (se 2 (by rfl) ⟨3717492, by rfl⟩ : syracuseStep 9913313 = 7434985) B7434985
theorem B6964319 : Blo 1833618 6964319 := bstep (se 1 (by rfl) ⟨5223239, by rfl⟩ : syracuseStep 6964319 = 10446479) B10446479
theorem B59516471 : Blo 1833618 59516471 := bstep (se 1 (by rfl) ⟨44637353, by rfl⟩ : syracuseStep 59516471 = 89274707) B89274707
theorem B4409569 : Blo 1833618 4409569 := bstep (se 2 (by rfl) ⟨1653588, by rfl⟩ : syracuseStep 4409569 = 3307177) B3307177
theorem B11758031 : Blo 1833618 11758031 := bstep (se 1 (by rfl) ⟨8818523, by rfl⟩ : syracuseStep 11758031 = 17637047) B17637047
theorem B6189911 : Blo 1833618 6189911 := bstep (se 1 (by rfl) ⟨4642433, by rfl⟩ : syracuseStep 6189911 = 9284867) B9284867
theorem B22066127 : Blo 1833618 22066127 := bstep (se 1 (by rfl) ⟨16549595, by rfl⟩ : syracuseStep 22066127 = 33099191) B33099191
theorem B5657647 : Blo 1833618 5657647 := bstep (se 1 (by rfl) ⟨4243235, by rfl⟩ : syracuseStep 5657647 = 8486471) B8486471
theorem B4126031 : Blo 1833618 4126031 := bstep (se 1 (by rfl) ⟨3094523, by rfl⟩ : syracuseStep 4126031 = 6189047) B6189047
theorem B6190721 : Blo 1833618 6190721 := bstep (se 2 (by rfl) ⟨2321520, by rfl⟩ : syracuseStep 6190721 = 4643041) B4643041
theorem B26449577 : Blo 1833618 26449577 := bstep (se 2 (by rfl) ⟨9918591, by rfl⟩ : syracuseStep 26449577 = 19837183) B19837183
theorem B8935177 : Blo 1833618 8935177 := bstep (se 2 (by rfl) ⟨3350691, by rfl⟩ : syracuseStep 8935177 = 6701383) B6701383
theorem B28235627 : Blo 1833618 28235627 := bstep (se 1 (by rfl) ⟨21176720, by rfl⟩ : syracuseStep 28235627 = 42353441) B42353441
theorem B6191423 : Blo 1833618 6191423 := bstep (se 1 (by rfl) ⟨4643567, by rfl⟩ : syracuseStep 6191423 = 9287135) B9287135
theorem B1834239 : Blo 1833618 1834239 := bstep (se 1 (by rfl) ⟨1375679, by rfl⟩ : syracuseStep 1834239 = 2751359) B2751359
theorem B190659881 : Blo 1833618 190659881 := bstep (se 2 (by rfl) ⟨71497455, by rfl⟩ : syracuseStep 190659881 = 142994911) B142994911
theorem B2752031 : Blo 1833618 2752031 := bstep (se 1 (by rfl) ⟨2064023, by rfl⟩ : syracuseStep 2752031 = 4128047) B4128047
theorem B1834623 : Blo 1833618 1834623 := bstep (se 1 (by rfl) ⟨1375967, by rfl⟩ : syracuseStep 1834623 = 2751935) B2751935
theorem B9920495 : Blo 1833618 9920495 := bstep (se 1 (by rfl) ⟨7440371, by rfl⟩ : syracuseStep 9920495 = 14880743) B14880743
theorem B1835111 : Blo 1833618 1835111 := bstep (se 1 (by rfl) ⟨1376333, by rfl⟩ : syracuseStep 1835111 = 2752667) B2752667
theorem B3096731 : Blo 1833618 3096731 := bstep (se 1 (by rfl) ⟨2322548, by rfl⟩ : syracuseStep 3096731 = 4645097) B4645097
theorem B2064667 : Blo 1833618 2064667 := bstep (se 1 (by rfl) ⟨1548500, by rfl⟩ : syracuseStep 2064667 = 3097001) B3097001
theorem B11913569 : Blo 1833618 11913569 := bstep (se 2 (by rfl) ⟨4467588, by rfl⟩ : syracuseStep 11913569 = 8935177) B8935177
theorem B6613663 : Blo 1833618 6613663 := bstep (se 1 (by rfl) ⟨4960247, by rfl⟩ : syracuseStep 6613663 = 9920495) B9920495
theorem B39677647 : Blo 1833618 39677647 := bstep (se 1 (by rfl) ⟨29758235, by rfl⟩ : syracuseStep 39677647 = 59516471) B59516471
theorem B17633051 : Blo 1833618 17633051 := bstep (se 1 (by rfl) ⟨13224788, by rfl⟩ : syracuseStep 17633051 = 26449577) B26449577
theorem B4126607 : Blo 1833618 4126607 := bstep (se 1 (by rfl) ⟨3094955, by rfl⟩ : syracuseStep 4126607 = 6189911) B6189911
theorem B14710751 : Blo 1833618 14710751 := bstep (se 1 (by rfl) ⟨11033063, by rfl⟩ : syracuseStep 14710751 = 22066127) B22066127
theorem B6608875 : Blo 1833618 6608875 := bstep (se 1 (by rfl) ⟨4956656, by rfl⟩ : syracuseStep 6608875 = 9913313) B9913313
theorem B4642879 : Blo 1833618 4642879 := bstep (se 1 (by rfl) ⟨3482159, by rfl⟩ : syracuseStep 4642879 = 6964319) B6964319
theorem B2750687 : Blo 1833618 2750687 := bstep (se 1 (by rfl) ⟨2063015, by rfl⟩ : syracuseStep 2750687 = 4126031) B4126031
theorem B4127147 : Blo 1833618 4127147 := bstep (se 1 (by rfl) ⟨3095360, by rfl⟩ : syracuseStep 4127147 = 6190721) B6190721
theorem B23517701 : Blo 1833618 23517701 := bstep (se 4 (by rfl) ⟨2204784, by rfl⟩ : syracuseStep 23517701 = 4409569) B4409569
theorem B18823751 : Blo 1833618 18823751 := bstep (se 1 (by rfl) ⟨14117813, by rfl⟩ : syracuseStep 18823751 = 28235627) B28235627
theorem B7543529 : Blo 1833618 7543529 := bstep (se 2 (by rfl) ⟨2828823, by rfl⟩ : syracuseStep 7543529 = 5657647) B5657647
theorem B4127615 : Blo 1833618 4127615 := bstep (se 1 (by rfl) ⟨3095711, by rfl⟩ : syracuseStep 4127615 = 6191423) B6191423
theorem B7838687 : Blo 1833618 7838687 := bstep (se 1 (by rfl) ⟨5879015, by rfl⟩ : syracuseStep 7838687 = 11758031) B11758031
theorem B127106587 : Blo 1833618 127106587 := bstep (se 1 (by rfl) ⟨95329940, by rfl⟩ : syracuseStep 127106587 = 190659881) B190659881
theorem B1834687 : Blo 1833618 1834687 := bstep (se 1 (by rfl) ⟨1376015, by rfl⟩ : syracuseStep 1834687 = 2752031) B2752031
theorem B2064487 : Blo 1833618 2064487 := bstep (se 1 (by rfl) ⟨1548365, by rfl⟩ : syracuseStep 2064487 = 3096731) B3096731
theorem B2752889 : Blo 1833618 2752889 := bstep (se 2 (by rfl) ⟨1032333, by rfl⟩ : syracuseStep 2752889 = 2064667) B2064667
theorem B9807167 : Blo 1833618 9807167 := bstep (se 1 (by rfl) ⟨7355375, by rfl⟩ : syracuseStep 9807167 = 14710751) B14710751
theorem B8818217 : Blo 1833618 8818217 := bstep (se 2 (by rfl) ⟨3306831, by rfl⟩ : syracuseStep 8818217 = 6613663) B6613663
theorem B7942379 : Blo 1833618 7942379 := bstep (se 1 (by rfl) ⟨5956784, by rfl⟩ : syracuseStep 7942379 = 11913569) B11913569
theorem B5029019 : Blo 1833618 5029019 := bstep (se 1 (by rfl) ⟨3771764, by rfl⟩ : syracuseStep 5029019 = 7543529) B7543529
theorem B8811833 : Blo 1833618 8811833 := bstep (se 2 (by rfl) ⟨3304437, by rfl⟩ : syracuseStep 8811833 = 6608875) B6608875
theorem B6190505 : Blo 1833618 6190505 := bstep (se 2 (by rfl) ⟨2321439, by rfl⟩ : syracuseStep 6190505 = 4642879) B4642879
theorem B2751071 : Blo 1833618 2751071 := bstep (se 1 (by rfl) ⟨2063303, by rfl⟩ : syracuseStep 2751071 = 4126607) B4126607
theorem B1833791 : Blo 1833618 1833791 := bstep (se 1 (by rfl) ⟨1375343, by rfl⟩ : syracuseStep 1833791 = 2750687) B2750687
theorem B2751431 : Blo 1833618 2751431 := bstep (se 1 (by rfl) ⟨2063573, by rfl⟩ : syracuseStep 2751431 = 4127147) B4127147
theorem B15678467 : Blo 1833618 15678467 := bstep (se 1 (by rfl) ⟨11758850, by rfl⟩ : syracuseStep 15678467 = 23517701) B23517701
theorem B12549167 : Blo 1833618 12549167 := bstep (se 1 (by rfl) ⟨9411875, by rfl⟩ : syracuseStep 12549167 = 18823751) B18823751
theorem B2751743 : Blo 1833618 2751743 := bstep (se 1 (by rfl) ⟨2063807, by rfl⟩ : syracuseStep 2751743 = 4127615) B4127615
theorem B5225791 : Blo 1833618 5225791 := bstep (se 1 (by rfl) ⟨3919343, by rfl⟩ : syracuseStep 5225791 = 7838687) B7838687
theorem B169475449 : Blo 1833618 169475449 := bstep (se 2 (by rfl) ⟨63553293, by rfl⟩ : syracuseStep 169475449 = 127106587) B127106587
theorem B52903529 : Blo 1833618 52903529 := bstep (se 2 (by rfl) ⟨19838823, by rfl⟩ : syracuseStep 52903529 = 39677647) B39677647
theorem B11755367 : Blo 1833618 11755367 := bstep (se 1 (by rfl) ⟨8816525, by rfl⟩ : syracuseStep 11755367 = 17633051) B17633051
theorem B2752649 : Blo 1833618 2752649 := bstep (se 2 (by rfl) ⟨1032243, by rfl⟩ : syracuseStep 2752649 = 2064487) B2064487
theorem B1835259 : Blo 1833618 1835259 := bstep (se 1 (by rfl) ⟨1376444, by rfl⟩ : syracuseStep 1835259 = 2752889) B2752889
theorem B8366111 : Blo 1833618 8366111 := bstep (se 1 (by rfl) ⟨6274583, by rfl⟩ : syracuseStep 8366111 = 12549167) B12549167
theorem B3352679 : Blo 1833618 3352679 := bstep (se 1 (by rfl) ⟨2514509, by rfl⟩ : syracuseStep 3352679 = 5029019) B5029019
theorem B35269019 : Blo 1833618 35269019 := bstep (se 1 (by rfl) ⟨26451764, by rfl⟩ : syracuseStep 35269019 = 52903529) B52903529
theorem B23498221 : Blo 1833618 23498221 := bstep (se 3 (by rfl) ⟨4405916, by rfl⟩ : syracuseStep 23498221 = 8811833) B8811833
theorem B26152445 : Blo 1833618 26152445 := bstep (se 3 (by rfl) ⟨4903583, by rfl⟩ : syracuseStep 26152445 = 9807167) B9807167
theorem B6967721 : Blo 1833618 6967721 := bstep (se 2 (by rfl) ⟨2612895, by rfl⟩ : syracuseStep 6967721 = 5225791) B5225791
theorem B5878811 : Blo 1833618 5878811 := bstep (se 1 (by rfl) ⟨4409108, by rfl⟩ : syracuseStep 5878811 = 8818217) B8818217
theorem B84718709 : Blo 1833618 84718709 := bstep (se 5 (by rfl) ⟨3971189, by rfl⟩ : syracuseStep 84718709 = 7942379) B7942379
theorem B7836911 : Blo 1833618 7836911 := bstep (se 1 (by rfl) ⟨5877683, by rfl⟩ : syracuseStep 7836911 = 11755367) B11755367
theorem B4127003 : Blo 1833618 4127003 := bstep (se 1 (by rfl) ⟨3095252, by rfl⟩ : syracuseStep 4127003 = 6190505) B6190505
theorem B1834047 : Blo 1833618 1834047 := bstep (se 1 (by rfl) ⟨1375535, by rfl⟩ : syracuseStep 1834047 = 2751071) B2751071
theorem B225967265 : Blo 1833618 225967265 := bstep (se 2 (by rfl) ⟨84737724, by rfl⟩ : syracuseStep 225967265 = 169475449) B169475449
theorem B1834287 : Blo 1833618 1834287 := bstep (se 1 (by rfl) ⟨1375715, by rfl⟩ : syracuseStep 1834287 = 2751431) B2751431
theorem B10452311 : Blo 1833618 10452311 := bstep (se 1 (by rfl) ⟨7839233, by rfl⟩ : syracuseStep 10452311 = 15678467) B15678467
theorem B1834495 : Blo 1833618 1834495 := bstep (se 1 (by rfl) ⟨1375871, by rfl⟩ : syracuseStep 1834495 = 2751743) B2751743
theorem B1835099 : Blo 1833618 1835099 := bstep (se 1 (by rfl) ⟨1376324, by rfl⟩ : syracuseStep 1835099 = 2752649) B2752649
theorem B4645147 : Blo 1833618 4645147 := bstep (se 1 (by rfl) ⟨3483860, by rfl⟩ : syracuseStep 4645147 = 6967721) B6967721
theorem B23512679 : Blo 1833618 23512679 := bstep (se 1 (by rfl) ⟨17634509, by rfl⟩ : syracuseStep 23512679 = 35269019) B35269019
theorem B150644843 : Blo 1833618 150644843 := bstep (se 1 (by rfl) ⟨112983632, by rfl⟩ : syracuseStep 150644843 = 225967265) B225967265
theorem B3919207 : Blo 1833618 3919207 := bstep (se 1 (by rfl) ⟨2939405, by rfl⟩ : syracuseStep 3919207 = 5878811) B5878811
theorem B56479139 : Blo 1833618 56479139 := bstep (se 1 (by rfl) ⟨42359354, by rfl⟩ : syracuseStep 56479139 = 84718709) B84718709
theorem B31330961 : Blo 1833618 31330961 := bstep (se 2 (by rfl) ⟨11749110, by rfl⟩ : syracuseStep 31330961 = 23498221) B23498221
theorem B6968207 : Blo 1833618 6968207 := bstep (se 1 (by rfl) ⟨5226155, by rfl⟩ : syracuseStep 6968207 = 10452311) B10452311
theorem B1115837653 : Blo 1833618 1115837653 := bstep (se 7 (by rfl) ⟨13076222, by rfl⟩ : syracuseStep 1115837653 = 26152445) B26152445
theorem B2235119 : Blo 1833618 2235119 := bstep (se 1 (by rfl) ⟨1676339, by rfl⟩ : syracuseStep 2235119 = 3352679) B3352679
theorem B5224607 : Blo 1833618 5224607 := bstep (se 1 (by rfl) ⟨3918455, by rfl⟩ : syracuseStep 5224607 = 7836911) B7836911
theorem B5577407 : Blo 1833618 5577407 := bstep (se 1 (by rfl) ⟨4183055, by rfl⟩ : syracuseStep 5577407 = 8366111) B8366111
theorem B2751335 : Blo 1833618 2751335 := bstep (se 1 (by rfl) ⟨2063501, by rfl⟩ : syracuseStep 2751335 = 4127003) B4127003
theorem B6193529 : Blo 1833618 6193529 := bstep (se 2 (by rfl) ⟨2322573, by rfl⟩ : syracuseStep 6193529 = 4645147) B4645147
theorem B4645471 : Blo 1833618 4645471 := bstep (se 1 (by rfl) ⟨3484103, by rfl⟩ : syracuseStep 4645471 = 6968207) B6968207
theorem B3483071 : Blo 1833618 3483071 := bstep (se 1 (by rfl) ⟨2612303, by rfl⟩ : syracuseStep 3483071 = 5224607) B5224607
theorem B1487783537 : Blo 1833618 1487783537 := bstep (se 2 (by rfl) ⟨557918826, by rfl⟩ : syracuseStep 1487783537 = 1115837653) B1115837653
theorem B37652759 : Blo 1833618 37652759 := bstep (se 1 (by rfl) ⟨28239569, by rfl⟩ : syracuseStep 37652759 = 56479139) B56479139
theorem B15675119 : Blo 1833618 15675119 := bstep (se 1 (by rfl) ⟨11756339, by rfl⟩ : syracuseStep 15675119 = 23512679) B23512679
theorem B100429895 : Blo 1833618 100429895 := bstep (se 1 (by rfl) ⟨75322421, by rfl⟩ : syracuseStep 100429895 = 150644843) B150644843
theorem B5960317 : Blo 1833618 5960317 := bstep (se 3 (by rfl) ⟨1117559, by rfl⟩ : syracuseStep 5960317 = 2235119) B2235119
theorem B20887307 : Blo 1833618 20887307 := bstep (se 1 (by rfl) ⟨15665480, by rfl⟩ : syracuseStep 20887307 = 31330961) B31330961
theorem B3718271 : Blo 1833618 3718271 := bstep (se 1 (by rfl) ⟨2788703, by rfl⟩ : syracuseStep 3718271 = 5577407) B5577407
theorem B5225609 : Blo 1833618 5225609 := bstep (se 2 (by rfl) ⟨1959603, by rfl⟩ : syracuseStep 5225609 = 3919207) B3919207
theorem B1834223 : Blo 1833618 1834223 := bstep (se 1 (by rfl) ⟨1375667, by rfl⟩ : syracuseStep 1834223 = 2751335) B2751335
theorem B66953263 : Blo 1833618 66953263 := bstep (se 1 (by rfl) ⟨50214947, by rfl⟩ : syracuseStep 66953263 = 100429895) B100429895
theorem B4129019 : Blo 1833618 4129019 := bstep (se 1 (by rfl) ⟨3096764, by rfl⟩ : syracuseStep 4129019 = 6193529) B6193529
theorem B6193961 : Blo 1833618 6193961 := bstep (se 2 (by rfl) ⟨2322735, by rfl⟩ : syracuseStep 6193961 = 4645471) B4645471
theorem B7947089 : Blo 1833618 7947089 := bstep (se 2 (by rfl) ⟨2980158, by rfl⟩ : syracuseStep 7947089 = 5960317) B5960317
theorem B991855691 : Blo 1833618 991855691 := bstep (se 1 (by rfl) ⟨743891768, by rfl⟩ : syracuseStep 991855691 = 1487783537) B1487783537
theorem B25101839 : Blo 1833618 25101839 := bstep (se 1 (by rfl) ⟨18826379, by rfl⟩ : syracuseStep 25101839 = 37652759) B37652759
theorem B3483739 : Blo 1833618 3483739 := bstep (se 1 (by rfl) ⟨2612804, by rfl⟩ : syracuseStep 3483739 = 5225609) B5225609
theorem B9915389 : Blo 1833618 9915389 := bstep (se 3 (by rfl) ⟨1859135, by rfl⟩ : syracuseStep 9915389 = 3718271) B3718271
theorem B2322047 : Blo 1833618 2322047 := bstep (se 1 (by rfl) ⟨1741535, by rfl⟩ : syracuseStep 2322047 = 3483071) B3483071
theorem B10450079 : Blo 1833618 10450079 := bstep (se 1 (by rfl) ⟨7837559, by rfl⟩ : syracuseStep 10450079 = 15675119) B15675119
theorem B13924871 : Blo 1833618 13924871 := bstep (se 1 (by rfl) ⟨10443653, by rfl⟩ : syracuseStep 13924871 = 20887307) B20887307
theorem B4644985 : Blo 1833618 4644985 := bstep (se 2 (by rfl) ⟨1741869, by rfl⟩ : syracuseStep 4644985 = 3483739) B3483739
theorem B2752679 : Blo 1833618 2752679 := bstep (se 1 (by rfl) ⟨2064509, by rfl⟩ : syracuseStep 2752679 = 4129019) B4129019
theorem B4129307 : Blo 1833618 4129307 := bstep (se 1 (by rfl) ⟨3096980, by rfl⟩ : syracuseStep 4129307 = 6193961) B6193961
theorem B9283247 : Blo 1833618 9283247 := bstep (se 1 (by rfl) ⟨6962435, by rfl⟩ : syracuseStep 9283247 = 13924871) B13924871
theorem B89271017 : Blo 1833618 89271017 := bstep (se 2 (by rfl) ⟨33476631, by rfl⟩ : syracuseStep 89271017 = 66953263) B66953263
theorem B661237127 : Blo 1833618 661237127 := bstep (se 1 (by rfl) ⟨495927845, by rfl⟩ : syracuseStep 661237127 = 991855691) B991855691
theorem B6966719 : Blo 1833618 6966719 := bstep (se 1 (by rfl) ⟨5225039, by rfl⟩ : syracuseStep 6966719 = 10450079) B10450079
theorem B5298059 : Blo 1833618 5298059 := bstep (se 1 (by rfl) ⟨3973544, by rfl⟩ : syracuseStep 5298059 = 7947089) B7947089
theorem B16734559 : Blo 1833618 16734559 := bstep (se 1 (by rfl) ⟨12550919, by rfl⟩ : syracuseStep 16734559 = 25101839) B25101839
theorem B6192125 : Blo 1833618 6192125 := bstep (se 3 (by rfl) ⟨1161023, by rfl⟩ : syracuseStep 6192125 = 2322047) B2322047
theorem B6610259 : Blo 1833618 6610259 := bstep (se 1 (by rfl) ⟨4957694, by rfl⟩ : syracuseStep 6610259 = 9915389) B9915389
theorem B1835119 : Blo 1833618 1835119 := bstep (se 1 (by rfl) ⟨1376339, by rfl⟩ : syracuseStep 1835119 = 2752679) B2752679
theorem B6193313 : Blo 1833618 6193313 := bstep (se 2 (by rfl) ⟨2322492, by rfl⟩ : syracuseStep 6193313 = 4644985) B4644985
theorem B2752871 : Blo 1833618 2752871 := bstep (se 1 (by rfl) ⟨2064653, by rfl⟩ : syracuseStep 2752871 = 4129307) B4129307
theorem B6188831 : Blo 1833618 6188831 := bstep (se 1 (by rfl) ⟨4641623, by rfl⟩ : syracuseStep 6188831 = 9283247) B9283247
theorem B440824751 : Blo 1833618 440824751 := bstep (se 1 (by rfl) ⟨330618563, by rfl⟩ : syracuseStep 440824751 = 661237127) B661237127
theorem B14128157 : Blo 1833618 14128157 := bstep (se 3 (by rfl) ⟨2649029, by rfl⟩ : syracuseStep 14128157 = 5298059) B5298059
theorem B22312745 : Blo 1833618 22312745 := bstep (se 2 (by rfl) ⟨8367279, by rfl⟩ : syracuseStep 22312745 = 16734559) B16734559
theorem B17627357 : Blo 1833618 17627357 := bstep (se 3 (by rfl) ⟨3305129, by rfl⟩ : syracuseStep 17627357 = 6610259) B6610259
theorem B59514011 : Blo 1833618 59514011 := bstep (se 1 (by rfl) ⟨44635508, by rfl⟩ : syracuseStep 59514011 = 89271017) B89271017
theorem B4128083 : Blo 1833618 4128083 := bstep (se 1 (by rfl) ⟨3096062, by rfl⟩ : syracuseStep 4128083 = 6192125) B6192125
theorem B4644479 : Blo 1833618 4644479 := bstep (se 1 (by rfl) ⟨3483359, by rfl⟩ : syracuseStep 4644479 = 6966719) B6966719
theorem B4128875 : Blo 1833618 4128875 := bstep (se 1 (by rfl) ⟨3096656, by rfl⟩ : syracuseStep 4128875 = 6193313) B6193313
theorem B1835247 : Blo 1833618 1835247 := bstep (se 1 (by rfl) ⟨1376435, by rfl⟩ : syracuseStep 1835247 = 2752871) B2752871
theorem B39676007 : Blo 1833618 39676007 := bstep (se 1 (by rfl) ⟨29757005, by rfl⟩ : syracuseStep 39676007 = 59514011) B59514011
theorem B293883167 : Blo 1833618 293883167 := bstep (se 1 (by rfl) ⟨220412375, by rfl⟩ : syracuseStep 293883167 = 440824751) B440824751
theorem B11751571 : Blo 1833618 11751571 := bstep (se 1 (by rfl) ⟨8813678, by rfl⟩ : syracuseStep 11751571 = 17627357) B17627357
theorem B4125887 : Blo 1833618 4125887 := bstep (se 1 (by rfl) ⟨3094415, by rfl⟩ : syracuseStep 4125887 = 6188831) B6188831
theorem B9418771 : Blo 1833618 9418771 := bstep (se 1 (by rfl) ⟨7064078, by rfl⟩ : syracuseStep 9418771 = 14128157) B14128157
theorem B14875163 : Blo 1833618 14875163 := bstep (se 1 (by rfl) ⟨11156372, by rfl⟩ : syracuseStep 14875163 = 22312745) B22312745
theorem B2752055 : Blo 1833618 2752055 := bstep (se 1 (by rfl) ⟨2064041, by rfl⟩ : syracuseStep 2752055 = 4128083) B4128083
theorem B3096319 : Blo 1833618 3096319 := bstep (se 1 (by rfl) ⟨2322239, by rfl⟩ : syracuseStep 3096319 = 4644479) B4644479
theorem B2752583 : Blo 1833618 2752583 := bstep (se 1 (by rfl) ⟨2064437, by rfl⟩ : syracuseStep 2752583 = 4128875) B4128875
theorem B195922111 : Blo 1833618 195922111 := bstep (se 1 (by rfl) ⟨146941583, by rfl⟩ : syracuseStep 195922111 = 293883167) B293883167
theorem B9916775 : Blo 1833618 9916775 := bstep (se 1 (by rfl) ⟨7437581, by rfl⟩ : syracuseStep 9916775 = 14875163) B14875163
theorem B50233445 : Blo 1833618 50233445 := bstep (se 4 (by rfl) ⟨4709385, by rfl⟩ : syracuseStep 50233445 = 9418771) B9418771
theorem B15668761 : Blo 1833618 15668761 := bstep (se 2 (by rfl) ⟨5875785, by rfl⟩ : syracuseStep 15668761 = 11751571) B11751571
theorem B2750591 : Blo 1833618 2750591 := bstep (se 1 (by rfl) ⟨2062943, by rfl⟩ : syracuseStep 2750591 = 4125887) B4125887
theorem B26450671 : Blo 1833618 26450671 := bstep (se 1 (by rfl) ⟨19838003, by rfl⟩ : syracuseStep 26450671 = 39676007) B39676007
theorem B4128425 : Blo 1833618 4128425 := bstep (se 2 (by rfl) ⟨1548159, by rfl⟩ : syracuseStep 4128425 = 3096319) B3096319
theorem B1834703 : Blo 1833618 1834703 := bstep (se 1 (by rfl) ⟨1376027, by rfl⟩ : syracuseStep 1834703 = 2752055) B2752055
theorem B1835055 : Blo 1833618 1835055 := bstep (se 1 (by rfl) ⟨1376291, by rfl⟩ : syracuseStep 1835055 = 2752583) B2752583
theorem B6611183 : Blo 1833618 6611183 := bstep (se 1 (by rfl) ⟨4958387, by rfl⟩ : syracuseStep 6611183 = 9916775) B9916775
theorem B35267561 : Blo 1833618 35267561 := bstep (se 2 (by rfl) ⟨13225335, by rfl⟩ : syracuseStep 35267561 = 26450671) B26450671
theorem B20891681 : Blo 1833618 20891681 := bstep (se 2 (by rfl) ⟨7834380, by rfl⟩ : syracuseStep 20891681 = 15668761) B15668761
theorem B261229481 : Blo 1833618 261229481 := bstep (se 2 (by rfl) ⟨97961055, by rfl⟩ : syracuseStep 261229481 = 195922111) B195922111
theorem B33488963 : Blo 1833618 33488963 := bstep (se 1 (by rfl) ⟨25116722, by rfl⟩ : syracuseStep 33488963 = 50233445) B50233445
theorem B1833727 : Blo 1833618 1833727 := bstep (se 1 (by rfl) ⟨1375295, by rfl⟩ : syracuseStep 1833727 = 2750591) B2750591
theorem B2752283 : Blo 1833618 2752283 := bstep (se 1 (by rfl) ⟨2064212, by rfl⟩ : syracuseStep 2752283 = 4128425) B4128425
theorem B4407455 : Blo 1833618 4407455 := bstep (se 1 (by rfl) ⟨3305591, by rfl⟩ : syracuseStep 4407455 = 6611183) B6611183
theorem B23511707 : Blo 1833618 23511707 := bstep (se 1 (by rfl) ⟨17633780, by rfl⟩ : syracuseStep 23511707 = 35267561) B35267561
theorem B13927787 : Blo 1833618 13927787 := bstep (se 1 (by rfl) ⟨10445840, by rfl⟩ : syracuseStep 13927787 = 20891681) B20891681
theorem B22325975 : Blo 1833618 22325975 := bstep (se 1 (by rfl) ⟨16744481, by rfl⟩ : syracuseStep 22325975 = 33488963) B33488963
theorem B174152987 : Blo 1833618 174152987 := bstep (se 1 (by rfl) ⟨130614740, by rfl⟩ : syracuseStep 174152987 = 261229481) B261229481
theorem B1834855 : Blo 1833618 1834855 := bstep (se 1 (by rfl) ⟨1376141, by rfl⟩ : syracuseStep 1834855 = 2752283) B2752283
theorem B15674471 : Blo 1833618 15674471 := bstep (se 1 (by rfl) ⟨11755853, by rfl⟩ : syracuseStep 15674471 = 23511707) B23511707
theorem B9285191 : Blo 1833618 9285191 := bstep (se 1 (by rfl) ⟨6963893, by rfl⟩ : syracuseStep 9285191 = 13927787) B13927787
theorem B116101991 : Blo 1833618 116101991 := bstep (se 1 (by rfl) ⟨87076493, by rfl⟩ : syracuseStep 116101991 = 174152987) B174152987
theorem B2938303 : Blo 1833618 2938303 := bstep (se 1 (by rfl) ⟨2203727, by rfl⟩ : syracuseStep 2938303 = 4407455) B4407455
theorem B14883983 : Blo 1833618 14883983 := bstep (se 1 (by rfl) ⟨11162987, by rfl⟩ : syracuseStep 14883983 = 22325975) B22325975
theorem B3917737 : Blo 1833618 3917737 := bstep (se 2 (by rfl) ⟨1469151, by rfl⟩ : syracuseStep 3917737 = 2938303) B2938303
theorem B9922655 : Blo 1833618 9922655 := bstep (se 1 (by rfl) ⟨7441991, by rfl⟩ : syracuseStep 9922655 = 14883983) B14883983
theorem B77401327 : Blo 1833618 77401327 := bstep (se 1 (by rfl) ⟨58050995, by rfl⟩ : syracuseStep 77401327 = 116101991) B116101991
theorem B10449647 : Blo 1833618 10449647 := bstep (se 1 (by rfl) ⟨7837235, by rfl⟩ : syracuseStep 10449647 = 15674471) B15674471
theorem B6190127 : Blo 1833618 6190127 := bstep (se 1 (by rfl) ⟨4642595, by rfl⟩ : syracuseStep 6190127 = 9285191) B9285191
theorem B6966431 : Blo 1833618 6966431 := bstep (se 1 (by rfl) ⟨5224823, by rfl⟩ : syracuseStep 6966431 = 10449647) B10449647
theorem B6615103 : Blo 1833618 6615103 := bstep (se 1 (by rfl) ⟨4961327, by rfl⟩ : syracuseStep 6615103 = 9922655) B9922655
theorem B20894597 : Blo 1833618 20894597 := bstep (se 4 (by rfl) ⟨1958868, by rfl⟩ : syracuseStep 20894597 = 3917737) B3917737
theorem B4126751 : Blo 1833618 4126751 := bstep (se 1 (by rfl) ⟨3095063, by rfl⟩ : syracuseStep 4126751 = 6190127) B6190127
theorem B103201769 : Blo 1833618 103201769 := bstep (se 2 (by rfl) ⟨38700663, by rfl⟩ : syracuseStep 103201769 = 77401327) B77401327
theorem B13929731 : Blo 1833618 13929731 := bstep (se 1 (by rfl) ⟨10447298, by rfl⟩ : syracuseStep 13929731 = 20894597) B20894597
theorem B68801179 : Blo 1833618 68801179 := bstep (se 1 (by rfl) ⟨51600884, by rfl⟩ : syracuseStep 68801179 = 103201769) B103201769
theorem B8820137 : Blo 1833618 8820137 := bstep (se 2 (by rfl) ⟨3307551, by rfl⟩ : syracuseStep 8820137 = 6615103) B6615103
theorem B2751167 : Blo 1833618 2751167 := bstep (se 1 (by rfl) ⟨2063375, by rfl⟩ : syracuseStep 2751167 = 4126751) B4126751
theorem B4644287 : Blo 1833618 4644287 := bstep (se 1 (by rfl) ⟨3483215, by rfl⟩ : syracuseStep 4644287 = 6966431) B6966431
theorem B23520365 : Blo 1833618 23520365 := bstep (se 3 (by rfl) ⟨4410068, by rfl⟩ : syracuseStep 23520365 = 8820137) B8820137
theorem B9286487 : Blo 1833618 9286487 := bstep (se 1 (by rfl) ⟨6964865, by rfl⟩ : syracuseStep 9286487 = 13929731) B13929731
theorem B1467758485 : Blo 1833618 1467758485 := bstep (se 6 (by rfl) ⟨34400589, by rfl⟩ : syracuseStep 1467758485 = 68801179) B68801179
theorem B1834111 : Blo 1833618 1834111 := bstep (se 1 (by rfl) ⟨1375583, by rfl⟩ : syracuseStep 1834111 = 2751167) B2751167
theorem B3096191 : Blo 1833618 3096191 := bstep (se 1 (by rfl) ⟨2322143, by rfl⟩ : syracuseStep 3096191 = 4644287) B4644287
theorem B15680243 : Blo 1833618 15680243 := bstep (se 1 (by rfl) ⟨11760182, by rfl⟩ : syracuseStep 15680243 = 23520365) B23520365
theorem B6190991 : Blo 1833618 6190991 := bstep (se 1 (by rfl) ⟨4643243, by rfl⟩ : syracuseStep 6190991 = 9286487) B9286487
theorem B7828045253 : Blo 1833618 7828045253 := bstep (se 4 (by rfl) ⟨733879242, by rfl⟩ : syracuseStep 7828045253 = 1467758485) B1467758485
theorem B2064127 : Blo 1833618 2064127 := bstep (se 1 (by rfl) ⟨1548095, by rfl⟩ : syracuseStep 2064127 = 3096191) B3096191
theorem B10453495 : Blo 1833618 10453495 := bstep (se 1 (by rfl) ⟨7840121, by rfl⟩ : syracuseStep 10453495 = 15680243) B15680243
theorem B4127327 : Blo 1833618 4127327 := bstep (se 1 (by rfl) ⟨3095495, by rfl⟩ : syracuseStep 4127327 = 6190991) B6190991
theorem B5218696835 : Blo 1833618 5218696835 := bstep (se 1 (by rfl) ⟨3914022626, by rfl⟩ : syracuseStep 5218696835 = 7828045253) B7828045253
theorem B2752169 : Blo 1833618 2752169 := bstep (se 2 (by rfl) ⟨1032063, by rfl⟩ : syracuseStep 2752169 = 2064127) B2064127
theorem B13937993 : Blo 1833618 13937993 := bstep (se 2 (by rfl) ⟨5226747, by rfl⟩ : syracuseStep 13937993 = 10453495) B10453495
theorem B3479131223 : Blo 1833618 3479131223 := bstep (se 1 (by rfl) ⟨2609348417, by rfl⟩ : syracuseStep 3479131223 = 5218696835) B5218696835
theorem B2751551 : Blo 1833618 2751551 := bstep (se 1 (by rfl) ⟨2063663, by rfl⟩ : syracuseStep 2751551 = 4127327) B4127327
theorem B1834779 : Blo 1833618 1834779 := bstep (se 1 (by rfl) ⟨1376084, by rfl⟩ : syracuseStep 1834779 = 2752169) B2752169
theorem B9291995 : Blo 1833618 9291995 := bstep (se 1 (by rfl) ⟨6968996, by rfl⟩ : syracuseStep 9291995 = 13937993) B13937993
theorem B2319420815 : Blo 1833618 2319420815 := bstep (se 1 (by rfl) ⟨1739565611, by rfl⟩ : syracuseStep 2319420815 = 3479131223) B3479131223
theorem B1834367 : Blo 1833618 1834367 := bstep (se 1 (by rfl) ⟨1375775, by rfl⟩ : syracuseStep 1834367 = 2751551) B2751551
theorem B6194663 : Blo 1833618 6194663 := bstep (se 1 (by rfl) ⟨4645997, by rfl⟩ : syracuseStep 6194663 = 9291995) B9291995
theorem B1546280543 : Blo 1833618 1546280543 := bstep (se 1 (by rfl) ⟨1159710407, by rfl⟩ : syracuseStep 1546280543 = 2319420815) B2319420815
theorem B4129775 : Blo 1833618 4129775 := bstep (se 1 (by rfl) ⟨3097331, by rfl⟩ : syracuseStep 4129775 = 6194663) B6194663
theorem B4123414781 : Blo 1833618 4123414781 := bstep (se 3 (by rfl) ⟨773140271, by rfl⟩ : syracuseStep 4123414781 = 1546280543) B1546280543
theorem B2753183 : Blo 1833618 2753183 := bstep (se 1 (by rfl) ⟨2064887, by rfl⟩ : syracuseStep 2753183 = 4129775) B4129775
theorem B2748943187 : Blo 1833618 2748943187 := bstep (se 1 (by rfl) ⟨2061707390, by rfl⟩ : syracuseStep 2748943187 = 4123414781) B4123414781
theorem B1835455 : Blo 1833618 1835455 := bstep (se 1 (by rfl) ⟨1376591, by rfl⟩ : syracuseStep 1835455 = 2753183) B2753183
theorem B1832628791 : Blo 1833618 1832628791 := bstep (se 1 (by rfl) ⟨1374471593, by rfl⟩ : syracuseStep 1832628791 = 2748943187) B2748943187
theorem B4887010109 : Blo 1833618 4887010109 := bstep (se 3 (by rfl) ⟨916314395, by rfl⟩ : syracuseStep 4887010109 = 1832628791) B1832628791
theorem B13032026957 : Blo 1833618 13032026957 := bstep (se 3 (by rfl) ⟨2443505054, by rfl⟩ : syracuseStep 13032026957 = 4887010109) B4887010109
theorem B8688017971 : Blo 1833618 8688017971 := bstep (se 1 (by rfl) ⟨6516013478, by rfl⟩ : syracuseStep 8688017971 = 13032026957) B13032026957
theorem B11584023961 : Blo 1833618 11584023961 := bstep (se 2 (by rfl) ⟨4344008985, by rfl⟩ : syracuseStep 11584023961 = 8688017971) B8688017971
theorem B15445365281 : Blo 1833618 15445365281 := bstep (se 2 (by rfl) ⟨5792011980, by rfl⟩ : syracuseStep 15445365281 = 11584023961) B11584023961
theorem B10296910187 : Blo 1833618 10296910187 := bstep (se 1 (by rfl) ⟨7722682640, by rfl⟩ : syracuseStep 10296910187 = 15445365281) B15445365281
theorem B6864606791 : Blo 1833618 6864606791 := bstep (se 1 (by rfl) ⟨5148455093, by rfl⟩ : syracuseStep 6864606791 = 10296910187) B10296910187
theorem B4576404527 : Blo 1833618 4576404527 := bstep (se 1 (by rfl) ⟨3432303395, by rfl⟩ : syracuseStep 4576404527 = 6864606791) B6864606791
theorem B3050936351 : Blo 1833618 3050936351 := bstep (se 1 (by rfl) ⟨2288202263, by rfl⟩ : syracuseStep 3050936351 = 4576404527) B4576404527
theorem B2033957567 : Blo 1833618 2033957567 := bstep (se 1 (by rfl) ⟨1525468175, by rfl⟩ : syracuseStep 2033957567 = 3050936351) B3050936351
theorem B1355971711 : Blo 1833618 1355971711 := bstep (se 1 (by rfl) ⟨1016978783, by rfl⟩ : syracuseStep 1355971711 = 2033957567) B2033957567
theorem B1807962281 : Blo 1833618 1807962281 := bstep (se 2 (by rfl) ⟨677985855, by rfl⟩ : syracuseStep 1807962281 = 1355971711) B1355971711
theorem B1205308187 : Blo 1833618 1205308187 := bstep (se 1 (by rfl) ⟨903981140, by rfl⟩ : syracuseStep 1205308187 = 1807962281) B1807962281
theorem B803538791 : Blo 1833618 803538791 := bstep (se 1 (by rfl) ⟨602654093, by rfl⟩ : syracuseStep 803538791 = 1205308187) B1205308187
theorem B535692527 : Blo 1833618 535692527 := bstep (se 1 (by rfl) ⟨401769395, by rfl⟩ : syracuseStep 535692527 = 803538791) B803538791
theorem B357128351 : Blo 1833618 357128351 := bstep (se 1 (by rfl) ⟨267846263, by rfl⟩ : syracuseStep 357128351 = 535692527) B535692527
theorem B238085567 : Blo 1833618 238085567 := bstep (se 1 (by rfl) ⟨178564175, by rfl⟩ : syracuseStep 238085567 = 357128351) B357128351
theorem B158723711 : Blo 1833618 158723711 := bstep (se 1 (by rfl) ⟨119042783, by rfl⟩ : syracuseStep 158723711 = 238085567) B238085567
theorem B105815807 : Blo 1833618 105815807 := bstep (se 1 (by rfl) ⟨79361855, by rfl⟩ : syracuseStep 105815807 = 158723711) B158723711
theorem B70543871 : Blo 1833618 70543871 := bstep (se 1 (by rfl) ⟨52907903, by rfl⟩ : syracuseStep 70543871 = 105815807) B105815807
theorem B47029247 : Blo 1833618 47029247 := bstep (se 1 (by rfl) ⟨35271935, by rfl⟩ : syracuseStep 47029247 = 70543871) B70543871
theorem B31352831 : Blo 1833618 31352831 := bstep (se 1 (by rfl) ⟨23514623, by rfl⟩ : syracuseStep 31352831 = 47029247) B47029247
theorem B20901887 : Blo 1833618 20901887 := bstep (se 1 (by rfl) ⟨15676415, by rfl⟩ : syracuseStep 20901887 = 31352831) B31352831
theorem B13934591 : Blo 1833618 13934591 := bstep (se 1 (by rfl) ⟨10450943, by rfl⟩ : syracuseStep 13934591 = 20901887) B20901887
theorem B9289727 : Blo 1833618 9289727 := bstep (se 1 (by rfl) ⟨6967295, by rfl⟩ : syracuseStep 9289727 = 13934591) B13934591
theorem B6193151 : Blo 1833618 6193151 := bstep (se 1 (by rfl) ⟨4644863, by rfl⟩ : syracuseStep 6193151 = 9289727) B9289727
theorem B4128767 : Blo 1833618 4128767 := bstep (se 1 (by rfl) ⟨3096575, by rfl⟩ : syracuseStep 4128767 = 6193151) B6193151
theorem B2752511 : Blo 1833618 2752511 := bstep (se 1 (by rfl) ⟨2064383, by rfl⟩ : syracuseStep 2752511 = 4128767) B4128767
theorem B1835007 : Blo 1833618 1835007 := bstep (se 1 (by rfl) ⟨1376255, by rfl⟩ : syracuseStep 1835007 = 2752511) B2752511

theorem C0 (j : ℕ) (h1 : 458404 ≤ j) (h2 : j ≤ 458903) : Blo 1833618 (4 * j + 3) := by
  interval_cases j
  · exact B1833619
  · exact B1833623
  · exact B1833627
  · exact B1833631
  · exact B1833635
  · exact B1833639
  · exact B1833643
  · exact B1833647
  · exact B1833651
  · exact B1833655
  · exact B1833659
  · exact B1833663
  · exact B1833667
  · exact B1833671
  · exact B1833675
  · exact B1833679
  · exact B1833683
  · exact B1833687
  · exact B1833691
  · exact B1833695
  · exact B1833699
  · exact B1833703
  · exact B1833707
  · exact B1833711
  · exact B1833715
  · exact B1833719
  · exact B1833723
  · exact B1833727
  · exact B1833731
  · exact B1833735
  · exact B1833739
  · exact B1833743
  · exact B1833747
  · exact B1833751
  · exact B1833755
  · exact B1833759
  · exact B1833763
  · exact B1833767
  · exact B1833771
  · exact B1833775
  · exact B1833779
  · exact B1833783
  · exact B1833787
  · exact B1833791
  · exact B1833795
  · exact B1833799
  · exact B1833803
  · exact B1833807
  · exact B1833811
  · exact B1833815
  · exact B1833819
  · exact B1833823
  · exact B1833827
  · exact B1833831
  · exact B1833835
  · exact B1833839
  · exact B1833843
  · exact B1833847
  · exact B1833851
  · exact B1833855
  · exact B1833859
  · exact B1833863
  · exact B1833867
  · exact B1833871
  · exact B1833875
  · exact B1833879
  · exact B1833883
  · exact B1833887
  · exact B1833891
  · exact B1833895
  · exact B1833899
  · exact B1833903
  · exact B1833907
  · exact B1833911
  · exact B1833915
  · exact B1833919
  · exact B1833923
  · exact B1833927
  · exact B1833931
  · exact B1833935
  · exact B1833939
  · exact B1833943
  · exact B1833947
  · exact B1833951
  · exact B1833955
  · exact B1833959
  · exact B1833963
  · exact B1833967
  · exact B1833971
  · exact B1833975
  · exact B1833979
  · exact B1833983
  · exact B1833987
  · exact B1833991
  · exact B1833995
  · exact B1833999
  · exact B1834003
  · exact B1834007
  · exact B1834011
  · exact B1834015
  · exact B1834019
  · exact B1834023
  · exact B1834027
  · exact B1834031
  · exact B1834035
  · exact B1834039
  · exact B1834043
  · exact B1834047
  · exact B1834051
  · exact B1834055
  · exact B1834059
  · exact B1834063
  · exact B1834067
  · exact B1834071
  · exact B1834075
  · exact B1834079
  · exact B1834083
  · exact B1834087
  · exact B1834091
  · exact B1834095
  · exact B1834099
  · exact B1834103
  · exact B1834107
  · exact B1834111
  · exact B1834115
  · exact B1834119
  · exact B1834123
  · exact B1834127
  · exact B1834131
  · exact B1834135
  · exact B1834139
  · exact B1834143
  · exact B1834147
  · exact B1834151
  · exact B1834155
  · exact B1834159
  · exact B1834163
  · exact B1834167
  · exact B1834171
  · exact B1834175
  · exact B1834179
  · exact B1834183
  · exact B1834187
  · exact B1834191
  · exact B1834195
  · exact B1834199
  · exact B1834203
  · exact B1834207
  · exact B1834211
  · exact B1834215
  · exact B1834219
  · exact B1834223
  · exact B1834227
  · exact B1834231
  · exact B1834235
  · exact B1834239
  · exact B1834243
  · exact B1834247
  · exact B1834251
  · exact B1834255
  · exact B1834259
  · exact B1834263
  · exact B1834267
  · exact B1834271
  · exact B1834275
  · exact B1834279
  · exact B1834283
  · exact B1834287
  · exact B1834291
  · exact B1834295
  · exact B1834299
  · exact B1834303
  · exact B1834307
  · exact B1834311
  · exact B1834315
  · exact B1834319
  · exact B1834323
  · exact B1834327
  · exact B1834331
  · exact B1834335
  · exact B1834339
  · exact B1834343
  · exact B1834347
  · exact B1834351
  · exact B1834355
  · exact B1834359
  · exact B1834363
  · exact B1834367
  · exact B1834371
  · exact B1834375
  · exact B1834379
  · exact B1834383
  · exact B1834387
  · exact B1834391
  · exact B1834395
  · exact B1834399
  · exact B1834403
  · exact B1834407
  · exact B1834411
  · exact B1834415
  · exact B1834419
  · exact B1834423
  · exact B1834427
  · exact B1834431
  · exact B1834435
  · exact B1834439
  · exact B1834443
  · exact B1834447
  · exact B1834451
  · exact B1834455
  · exact B1834459
  · exact B1834463
  · exact B1834467
  · exact B1834471
  · exact B1834475
  · exact B1834479
  · exact B1834483
  · exact B1834487
  · exact B1834491
  · exact B1834495
  · exact B1834499
  · exact B1834503
  · exact B1834507
  · exact B1834511
  · exact B1834515
  · exact B1834519
  · exact B1834523
  · exact B1834527
  · exact B1834531
  · exact B1834535
  · exact B1834539
  · exact B1834543
  · exact B1834547
  · exact B1834551
  · exact B1834555
  · exact B1834559
  · exact B1834563
  · exact B1834567
  · exact B1834571
  · exact B1834575
  · exact B1834579
  · exact B1834583
  · exact B1834587
  · exact B1834591
  · exact B1834595
  · exact B1834599
  · exact B1834603
  · exact B1834607
  · exact B1834611
  · exact B1834615
  · exact B1834619
  · exact B1834623
  · exact B1834627
  · exact B1834631
  · exact B1834635
  · exact B1834639
  · exact B1834643
  · exact B1834647
  · exact B1834651
  · exact B1834655
  · exact B1834659
  · exact B1834663
  · exact B1834667
  · exact B1834671
  · exact B1834675
  · exact B1834679
  · exact B1834683
  · exact B1834687
  · exact B1834691
  · exact B1834695
  · exact B1834699
  · exact B1834703
  · exact B1834707
  · exact B1834711
  · exact B1834715
  · exact B1834719
  · exact B1834723
  · exact B1834727
  · exact B1834731
  · exact B1834735
  · exact B1834739
  · exact B1834743
  · exact B1834747
  · exact B1834751
  · exact B1834755
  · exact B1834759
  · exact B1834763
  · exact B1834767
  · exact B1834771
  · exact B1834775
  · exact B1834779
  · exact B1834783
  · exact B1834787
  · exact B1834791
  · exact B1834795
  · exact B1834799
  · exact B1834803
  · exact B1834807
  · exact B1834811
  · exact B1834815
  · exact B1834819
  · exact B1834823
  · exact B1834827
  · exact B1834831
  · exact B1834835
  · exact B1834839
  · exact B1834843
  · exact B1834847
  · exact B1834851
  · exact B1834855
  · exact B1834859
  · exact B1834863
  · exact B1834867
  · exact B1834871
  · exact B1834875
  · exact B1834879
  · exact B1834883
  · exact B1834887
  · exact B1834891
  · exact B1834895
  · exact B1834899
  · exact B1834903
  · exact B1834907
  · exact B1834911
  · exact B1834915
  · exact B1834919
  · exact B1834923
  · exact B1834927
  · exact B1834931
  · exact B1834935
  · exact B1834939
  · exact B1834943
  · exact B1834947
  · exact B1834951
  · exact B1834955
  · exact B1834959
  · exact B1834963
  · exact B1834967
  · exact B1834971
  · exact B1834975
  · exact B1834979
  · exact B1834983
  · exact B1834987
  · exact B1834991
  · exact B1834995
  · exact B1834999
  · exact B1835003
  · exact B1835007
  · exact B1835011
  · exact B1835015
  · exact B1835019
  · exact B1835023
  · exact B1835027
  · exact B1835031
  · exact B1835035
  · exact B1835039
  · exact B1835043
  · exact B1835047
  · exact B1835051
  · exact B1835055
  · exact B1835059
  · exact B1835063
  · exact B1835067
  · exact B1835071
  · exact B1835075
  · exact B1835079
  · exact B1835083
  · exact B1835087
  · exact B1835091
  · exact B1835095
  · exact B1835099
  · exact B1835103
  · exact B1835107
  · exact B1835111
  · exact B1835115
  · exact B1835119
  · exact B1835123
  · exact B1835127
  · exact B1835131
  · exact B1835135
  · exact B1835139
  · exact B1835143
  · exact B1835147
  · exact B1835151
  · exact B1835155
  · exact B1835159
  · exact B1835163
  · exact B1835167
  · exact B1835171
  · exact B1835175
  · exact B1835179
  · exact B1835183
  · exact B1835187
  · exact B1835191
  · exact B1835195
  · exact B1835199
  · exact B1835203
  · exact B1835207
  · exact B1835211
  · exact B1835215
  · exact B1835219
  · exact B1835223
  · exact B1835227
  · exact B1835231
  · exact B1835235
  · exact B1835239
  · exact B1835243
  · exact B1835247
  · exact B1835251
  · exact B1835255
  · exact B1835259
  · exact B1835263
  · exact B1835267
  · exact B1835271
  · exact B1835275
  · exact B1835279
  · exact B1835283
  · exact B1835287
  · exact B1835291
  · exact B1835295
  · exact B1835299
  · exact B1835303
  · exact B1835307
  · exact B1835311
  · exact B1835315
  · exact B1835319
  · exact B1835323
  · exact B1835327
  · exact B1835331
  · exact B1835335
  · exact B1835339
  · exact B1835343
  · exact B1835347
  · exact B1835351
  · exact B1835355
  · exact B1835359
  · exact B1835363
  · exact B1835367
  · exact B1835371
  · exact B1835375
  · exact B1835379
  · exact B1835383
  · exact B1835387
  · exact B1835391
  · exact B1835395
  · exact B1835399
  · exact B1835403
  · exact B1835407
  · exact B1835411
  · exact B1835415
  · exact B1835419
  · exact B1835423
  · exact B1835427
  · exact B1835431
  · exact B1835435
  · exact B1835439
  · exact B1835443
  · exact B1835447
  · exact B1835451
  · exact B1835455
  · exact B1835459
  · exact B1835463
  · exact B1835467
  · exact B1835471
  · exact B1835475
  · exact B1835479
  · exact B1835483
  · exact B1835487
  · exact B1835491
  · exact B1835495
  · exact B1835499
  · exact B1835503
  · exact B1835507
  · exact B1835511
  · exact B1835515
  · exact B1835519
  · exact B1835523
  · exact B1835527
  · exact B1835531
  · exact B1835535
  · exact B1835539
  · exact B1835543
  · exact B1835547
  · exact B1835551
  · exact B1835555
  · exact B1835559
  · exact B1835563
  · exact B1835567
  · exact B1835571
  · exact B1835575
  · exact B1835579
  · exact B1835583
  · exact B1835587
  · exact B1835591
  · exact B1835595
  · exact B1835599
  · exact B1835603
  · exact B1835607
  · exact B1835611
  · exact B1835615

theorem solution (m : ℕ) (hlo : 1833618 ≤ m) (hhi : m ≤ 1835618) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 458404 ≤ j := by omega
    have hj2 : j ≤ 458903 := by omega
    have hb : Blo 1833618 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
