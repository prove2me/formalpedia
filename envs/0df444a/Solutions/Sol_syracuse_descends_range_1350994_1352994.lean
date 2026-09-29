-- Prove2me | solution 1 for syracuse_descends_range_1350994_1352994
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:12:50.111967+00:00
-- url     : https://prove2.me/submissions/33e714a8-6640-482a-8c4c-645a37cca854

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


theorem B2056205 : Blo 1350994 2056205 := bbase (se 3 (by rfl) ⟨385538, by rfl⟩ : syracuseStep 2056205 = 771077) (by norm_num)
theorem B6848549 : Blo 1350994 6848549 := bbase (se 4 (by rfl) ⟨642051, by rfl⟩ : syracuseStep 6848549 = 1284103) (by norm_num)
theorem B1712173 : Blo 1350994 1712173 := bbase (se 3 (by rfl) ⟨321032, by rfl⟩ : syracuseStep 1712173 = 642065) (by norm_num)
theorem B1925221 : Blo 1350994 1925221 := bbase (se 4 (by rfl) ⟨180489, by rfl⟩ : syracuseStep 1925221 = 360979) (by norm_num)
theorem B8216693 : Blo 1350994 8216693 := bbase (se 5 (by rfl) ⟨385157, by rfl⟩ : syracuseStep 8216693 = 770315) (by norm_num)
theorem B1712269 : Blo 1350994 1712269 := bbase (se 3 (by rfl) ⟨321050, by rfl⟩ : syracuseStep 1712269 = 642101) (by norm_num)
theorem B6496469 : Blo 1350994 6496469 := bbase (se 7 (by rfl) ⟨76130, by rfl⟩ : syracuseStep 6496469 = 152261) (by norm_num)
theorem B3424477 : Blo 1350994 3424477 := bbase (se 3 (by rfl) ⟨642089, by rfl⟩ : syracuseStep 3424477 = 1284179) (by norm_num)
theorem B4563269 : Blo 1350994 4563269 := bbase (se 4 (by rfl) ⟨427806, by rfl⟩ : syracuseStep 4563269 = 855613) (by norm_num)
theorem B3424589 : Blo 1350994 3424589 := bbase (se 3 (by rfl) ⟨642110, by rfl⟩ : syracuseStep 3424589 = 1284221) (by norm_num)
theorem B6840773 : Blo 1350994 6840773 := bbase (se 4 (by rfl) ⟨641322, by rfl⟩ : syracuseStep 6840773 = 1282645) (by norm_num)
theorem B10961365 : Blo 1350994 10961365 := bbase (se 7 (by rfl) ⟨128453, by rfl⟩ : syracuseStep 10961365 = 256907) (by norm_num)
theorem B6496757 : Blo 1350994 6496757 := bbase (se 5 (by rfl) ⟨304535, by rfl⟩ : syracuseStep 6496757 = 609071) (by norm_num)
theorem B3039749 : Blo 1350994 3039749 := bbase (se 4 (by rfl) ⟨284976, by rfl⟩ : syracuseStep 3039749 = 569953) (by norm_num)
theorem B3039821 : Blo 1350994 3039821 := bbase (se 3 (by rfl) ⟨569966, by rfl⟩ : syracuseStep 3039821 = 1139933) (by norm_num)
theorem B2925181 : Blo 1350994 2925181 := bbase (se 3 (by rfl) ⟨548471, by rfl⟩ : syracuseStep 2925181 = 1096943) (by norm_num)
theorem B3039893 : Blo 1350994 3039893 := bbase (se 6 (by rfl) ⟨71247, by rfl⟩ : syracuseStep 3039893 = 142495) (by norm_num)
theorem B1925813 : Blo 1350994 1925813 := bbase (se 5 (by rfl) ⟨90272, by rfl⟩ : syracuseStep 1925813 = 180545) (by norm_num)
theorem B2564797 : Blo 1350994 2564797 := bbase (se 3 (by rfl) ⟨480899, by rfl⟩ : syracuseStep 2564797 = 961799) (by norm_num)
theorem B3039965 : Blo 1350994 3039965 := bbase (se 3 (by rfl) ⟨569993, by rfl⟩ : syracuseStep 3039965 = 1139987) (by norm_num)
theorem B4563701 : Blo 1350994 4563701 := bbase (se 5 (by rfl) ⟨213923, by rfl⟩ : syracuseStep 4563701 = 427847) (by norm_num)
theorem B5137141 : Blo 1350994 5137141 := bbase (se 5 (by rfl) ⟨240803, by rfl⟩ : syracuseStep 5137141 = 481607) (by norm_num)
theorem B1925893 : Blo 1350994 1925893 := bbase (se 4 (by rfl) ⟨180552, by rfl⟩ : syracuseStep 1925893 = 361105) (by norm_num)
theorem B2196229 : Blo 1350994 2196229 := bbase (se 4 (by rfl) ⟨205896, by rfl⟩ : syracuseStep 2196229 = 411793) (by norm_num)
theorem B3040037 : Blo 1350994 3040037 := bbase (se 4 (by rfl) ⟨285003, by rfl⟩ : syracuseStep 3040037 = 570007) (by norm_num)
theorem B2564941 : Blo 1350994 2564941 := bbase (se 3 (by rfl) ⟨480926, by rfl⟩ : syracuseStep 2564941 = 961853) (by norm_num)
theorem B1540949 : Blo 1350994 1540949 := bbase (se 9 (by rfl) ⟨4514, by rfl⟩ : syracuseStep 1540949 = 9029) (by norm_num)
theorem B3040109 : Blo 1350994 3040109 := bbase (se 3 (by rfl) ⟨570020, by rfl⟩ : syracuseStep 3040109 = 1140041) (by norm_num)
theorem B1926013 : Blo 1350994 1926013 := bbase (se 3 (by rfl) ⟨361127, by rfl⟩ : syracuseStep 1926013 = 722255) (by norm_num)
theorem B3040181 : Blo 1350994 3040181 := bbase (se 5 (by rfl) ⟨142508, by rfl⟩ : syracuseStep 3040181 = 285017) (by norm_num)
theorem B1926109 : Blo 1350994 1926109 := bbase (se 3 (by rfl) ⟨361145, by rfl⟩ : syracuseStep 1926109 = 722291) (by norm_num)
theorem B2565101 : Blo 1350994 2565101 := bbase (se 3 (by rfl) ⟨480956, by rfl⟩ : syracuseStep 2565101 = 961913) (by norm_num)
theorem B3040253 : Blo 1350994 3040253 := bbase (se 3 (by rfl) ⟨570047, by rfl⟩ : syracuseStep 3040253 = 1140095) (by norm_num)
theorem B3040325 : Blo 1350994 3040325 := bbase (se 4 (by rfl) ⟨285030, by rfl⟩ : syracuseStep 3040325 = 570061) (by norm_num)
theorem B1541201 : Blo 1350994 1541201 := bbase (se 2 (by rfl) ⟨577950, by rfl⟩ : syracuseStep 1541201 = 1155901) (by norm_num)
theorem B2565245 : Blo 1350994 2565245 := bbase (se 3 (by rfl) ⟨480983, by rfl⟩ : syracuseStep 2565245 = 961967) (by norm_num)
theorem B1827965 : Blo 1350994 1827965 := bbase (se 3 (by rfl) ⟨342743, by rfl⟩ : syracuseStep 1827965 = 685487) (by norm_num)
theorem B3040397 : Blo 1350994 3040397 := bbase (se 3 (by rfl) ⟨570074, by rfl⟩ : syracuseStep 3040397 = 1140149) (by norm_num)
theorem B4564133 : Blo 1350994 4564133 := bbase (se 4 (by rfl) ⟨427887, by rfl⟩ : syracuseStep 4564133 = 855775) (by norm_num)
theorem B1442993 : Blo 1350994 1442993 := bbase (se 2 (by rfl) ⟨541122, by rfl⟩ : syracuseStep 1442993 = 1082245) (by norm_num)
theorem B3040469 : Blo 1350994 3040469 := bbase (se 7 (by rfl) ⟨35630, by rfl⟩ : syracuseStep 3040469 = 71261) (by norm_num)
theorem B1443053 : Blo 1350994 1443053 := bbase (se 3 (by rfl) ⟨270572, by rfl⟩ : syracuseStep 1443053 = 541145) (by norm_num)
theorem B7701749 : Blo 1350994 7701749 := bbase (se 5 (by rfl) ⟨361019, by rfl⟩ : syracuseStep 7701749 = 722039) (by norm_num)
theorem B3040541 : Blo 1350994 3040541 := bbase (se 3 (by rfl) ⟨570101, by rfl⟩ : syracuseStep 3040541 = 1140203) (by norm_num)
theorem B1951061 : Blo 1350994 1951061 := bbase (se 12 (by rfl) ⟨714, by rfl⟩ : syracuseStep 1951061 = 1429) (by norm_num)
theorem B3040613 : Blo 1350994 3040613 := bbase (se 4 (by rfl) ⟨285057, by rfl⟩ : syracuseStep 3040613 = 570115) (by norm_num)
theorem B1443181 : Blo 1350994 1443181 := bbase (se 3 (by rfl) ⟨270596, by rfl⟩ : syracuseStep 1443181 = 541193) (by norm_num)
theorem B5776757 : Blo 1350994 5776757 := bbase (se 5 (by rfl) ⟨270785, by rfl⟩ : syracuseStep 5776757 = 541571) (by norm_num)
theorem B2565533 : Blo 1350994 2565533 := bbase (se 3 (by rfl) ⟨481037, by rfl⟩ : syracuseStep 2565533 = 962075) (by norm_num)
theorem B3040685 : Blo 1350994 3040685 := bbase (se 3 (by rfl) ⟨570128, by rfl⟩ : syracuseStep 3040685 = 1140257) (by norm_num)
theorem B5129669 : Blo 1350994 5129669 := bbase (se 4 (by rfl) ⟨480906, by rfl⟩ : syracuseStep 5129669 = 961813) (by norm_num)
theorem B1623521 : Blo 1350994 1623521 := bbase (se 2 (by rfl) ⟨608820, by rfl⟩ : syracuseStep 1623521 = 1217641) (by norm_num)
theorem B3040757 : Blo 1350994 3040757 := bbase (se 5 (by rfl) ⟨142535, by rfl⟩ : syracuseStep 3040757 = 285071) (by norm_num)
theorem B2565685 : Blo 1350994 2565685 := bbase (se 5 (by rfl) ⟨120266, by rfl⟩ : syracuseStep 2565685 = 240533) (by norm_num)
theorem B3040829 : Blo 1350994 3040829 := bbase (se 3 (by rfl) ⟨570155, by rfl⟩ : syracuseStep 3040829 = 1140311) (by norm_num)
theorem B4564565 : Blo 1350994 4564565 := bbase (se 8 (by rfl) ⟨26745, by rfl⟩ : syracuseStep 4564565 = 53491) (by norm_num)
theorem B3040901 : Blo 1350994 3040901 := bbase (se 4 (by rfl) ⟨285084, by rfl⟩ : syracuseStep 3040901 = 570169) (by norm_num)
theorem B27829909 : Blo 1350994 27829909 := bbase (se 6 (by rfl) ⟨652263, by rfl⟩ : syracuseStep 27829909 = 1304527) (by norm_num)
theorem B1369765 : Blo 1350994 1369765 := bbase (se 4 (by rfl) ⟨128415, by rfl⟩ : syracuseStep 1369765 = 256831) (by norm_num)
theorem B3040973 : Blo 1350994 3040973 := bbase (se 3 (by rfl) ⟨570182, by rfl⟩ : syracuseStep 3040973 = 1140365) (by norm_num)
theorem B6842069 : Blo 1350994 6842069 := bbase (se 7 (by rfl) ⟨80180, by rfl⟩ : syracuseStep 6842069 = 160361) (by norm_num)
theorem B7309045 : Blo 1350994 7309045 := bbase (se 5 (by rfl) ⟨342611, by rfl⟩ : syracuseStep 7309045 = 685223) (by norm_num)
theorem B2164477 : Blo 1350994 2164477 := bbase (se 3 (by rfl) ⟨405839, by rfl⟩ : syracuseStep 2164477 = 811679) (by norm_num)
theorem B3041045 : Blo 1350994 3041045 := bbase (se 6 (by rfl) ⟨71274, by rfl⟩ : syracuseStep 3041045 = 142549) (by norm_num)
theorem B1623829 : Blo 1350994 1623829 := bbase (se 6 (by rfl) ⟨38058, by rfl⟩ : syracuseStep 1623829 = 76117) (by norm_num)
theorem B1443625 : Blo 1350994 1443625 := bbase (se 2 (by rfl) ⟨541359, by rfl⟩ : syracuseStep 1443625 = 1082719) (by norm_num)
theorem B3082045 : Blo 1350994 3082045 := bbase (se 3 (by rfl) ⟨577883, by rfl⟩ : syracuseStep 3082045 = 1155767) (by norm_num)
theorem B1541953 : Blo 1350994 1541953 := bbase (se 2 (by rfl) ⟨578232, by rfl⟩ : syracuseStep 1541953 = 1156465) (by norm_num)
theorem B3041117 : Blo 1350994 3041117 := bbase (se 3 (by rfl) ⟨570209, by rfl⟩ : syracuseStep 3041117 = 1140419) (by norm_num)
theorem B2565989 : Blo 1350994 2565989 := bbase (se 4 (by rfl) ⟨240561, by rfl⟩ : syracuseStep 2565989 = 481123) (by norm_num)
theorem B1623925 : Blo 1350994 1623925 := bbase (se 5 (by rfl) ⟨76121, by rfl⟩ : syracuseStep 1623925 = 152243) (by norm_num)
theorem B17336213 : Blo 1350994 17336213 := bbase (se 6 (by rfl) ⟨406317, by rfl⟩ : syracuseStep 17336213 = 812635) (by norm_num)
theorem B1443745 : Blo 1350994 1443745 := bbase (se 2 (by rfl) ⟨541404, by rfl⟩ : syracuseStep 1443745 = 1082809) (by norm_num)
theorem B3041189 : Blo 1350994 3041189 := bbase (se 4 (by rfl) ⟨285111, by rfl⟩ : syracuseStep 3041189 = 570223) (by norm_num)
theorem B1623973 : Blo 1350994 1623973 := bbase (se 4 (by rfl) ⟨152247, by rfl⟩ : syracuseStep 1623973 = 304495) (by norm_num)
theorem B3041261 : Blo 1350994 3041261 := bbase (se 3 (by rfl) ⟨570236, by rfl⟩ : syracuseStep 3041261 = 1140473) (by norm_num)
theorem B2926573 : Blo 1350994 2926573 := bbase (se 3 (by rfl) ⟨548732, by rfl⟩ : syracuseStep 2926573 = 1097465) (by norm_num)
theorem B4564997 : Blo 1350994 4564997 := bbase (se 4 (by rfl) ⟨427968, by rfl⟩ : syracuseStep 4564997 = 855937) (by norm_num)
theorem B2885645 : Blo 1350994 2885645 := bbase (se 3 (by rfl) ⟨541058, by rfl⟩ : syracuseStep 2885645 = 1082117) (by norm_num)
theorem B3041333 : Blo 1350994 3041333 := bbase (se 5 (by rfl) ⟨142562, by rfl⟩ : syracuseStep 3041333 = 285125) (by norm_num)
theorem B3655733 : Blo 1350994 3655733 := bbase (se 5 (by rfl) ⟨171362, by rfl⟩ : syracuseStep 3655733 = 342725) (by norm_num)
theorem B3041405 : Blo 1350994 3041405 := bbase (se 3 (by rfl) ⟨570263, by rfl⟩ : syracuseStep 3041405 = 1140527) (by norm_num)
theorem B1443997 : Blo 1350994 1443997 := bbase (se 3 (by rfl) ⟨270749, by rfl⟩ : syracuseStep 1443997 = 541499) (by norm_num)
theorem B1444001 : Blo 1350994 1444001 := bbase (se 2 (by rfl) ⟨541500, by rfl⟩ : syracuseStep 1444001 = 1083001) (by norm_num)
theorem B2164925 : Blo 1350994 2164925 := bbase (se 3 (by rfl) ⟨405923, by rfl⟩ : syracuseStep 2164925 = 811847) (by norm_num)
theorem B3041477 : Blo 1350994 3041477 := bbase (se 4 (by rfl) ⟨285138, by rfl⟩ : syracuseStep 3041477 = 570277) (by norm_num)
theorem B3041549 : Blo 1350994 3041549 := bbase (se 3 (by rfl) ⟨570290, by rfl⟩ : syracuseStep 3041549 = 1140581) (by norm_num)
theorem B3246389 : Blo 1350994 3246389 := bbase (se 5 (by rfl) ⟨152174, by rfl⟩ : syracuseStep 3246389 = 304349) (by norm_num)
theorem B3041621 : Blo 1350994 3041621 := bbase (se 10 (by rfl) ⟨4455, by rfl⟩ : syracuseStep 3041621 = 8911) (by norm_num)
theorem B3852629 : Blo 1350994 3852629 := bbase (se 10 (by rfl) ⟨5643, by rfl⟩ : syracuseStep 3852629 = 11287) (by norm_num)
theorem B2165125 : Blo 1350994 2165125 := bbase (se 4 (by rfl) ⟨202980, by rfl⟩ : syracuseStep 2165125 = 405961) (by norm_num)
theorem B3041693 : Blo 1350994 3041693 := bbase (se 3 (by rfl) ⟨570317, by rfl⟩ : syracuseStep 3041693 = 1140635) (by norm_num)
theorem B4565429 : Blo 1350994 4565429 := bbase (se 5 (by rfl) ⟨214004, by rfl⟩ : syracuseStep 4565429 = 428009) (by norm_num)
theorem B2279893 : Blo 1350994 2279893 := bbase (se 7 (by rfl) ⟨26717, by rfl⟩ : syracuseStep 2279893 = 53435) (by norm_num)
theorem B3041765 : Blo 1350994 3041765 := bbase (se 4 (by rfl) ⟨285165, by rfl⟩ : syracuseStep 3041765 = 570331) (by norm_num)
theorem B3246581 : Blo 1350994 3246581 := bbase (se 5 (by rfl) ⟨152183, by rfl⟩ : syracuseStep 3246581 = 304367) (by norm_num)
theorem B9882101 : Blo 1350994 9882101 := bbase (se 5 (by rfl) ⟨463223, by rfl⟩ : syracuseStep 9882101 = 926447) (by norm_num)
theorem B2279981 : Blo 1350994 2279981 := bbase (se 3 (by rfl) ⟨427496, by rfl⟩ : syracuseStep 2279981 = 854993) (by norm_num)
theorem B3041837 : Blo 1350994 3041837 := bbase (se 3 (by rfl) ⟨570344, by rfl⟩ : syracuseStep 3041837 = 1140689) (by norm_num)
theorem B2566741 : Blo 1350994 2566741 := bbase (se 8 (by rfl) ⟨15039, by rfl⟩ : syracuseStep 2566741 = 30079) (by norm_num)
theorem B2927197 : Blo 1350994 2927197 := bbase (se 3 (by rfl) ⟨548849, by rfl⟩ : syracuseStep 2927197 = 1097699) (by norm_num)
theorem B3041909 : Blo 1350994 3041909 := bbase (se 5 (by rfl) ⟨142589, by rfl⟩ : syracuseStep 3041909 = 285179) (by norm_num)
theorem B2165381 : Blo 1350994 2165381 := bbase (se 4 (by rfl) ⟨203004, by rfl⟩ : syracuseStep 2165381 = 406009) (by norm_num)
theorem B6941333 : Blo 1350994 6941333 := bbase (se 6 (by rfl) ⟨162687, by rfl⟩ : syracuseStep 6941333 = 325375) (by norm_num)
theorem B5204645 : Blo 1350994 5204645 := bbase (se 4 (by rfl) ⟨487935, by rfl⟩ : syracuseStep 5204645 = 975871) (by norm_num)
theorem B2280109 : Blo 1350994 2280109 := bbase (se 3 (by rfl) ⟨427520, by rfl⟩ : syracuseStep 2280109 = 855041) (by norm_num)
theorem B1542829 : Blo 1350994 1542829 := bbase (se 3 (by rfl) ⟨289280, by rfl⟩ : syracuseStep 1542829 = 578561) (by norm_num)
theorem B10963637 : Blo 1350994 10963637 := bbase (se 5 (by rfl) ⟨513920, by rfl⟩ : syracuseStep 10963637 = 1027841) (by norm_num)
theorem B3041981 : Blo 1350994 3041981 := bbase (se 3 (by rfl) ⟨570371, by rfl⟩ : syracuseStep 3041981 = 1140743) (by norm_num)
theorem B6163141 : Blo 1350994 6163141 := bbase (se 4 (by rfl) ⟨577794, by rfl⟩ : syracuseStep 6163141 = 1155589) (by norm_num)
theorem B1444565 : Blo 1350994 1444565 := bbase (se 7 (by rfl) ⟨16928, by rfl⟩ : syracuseStep 1444565 = 33857) (by norm_num)
theorem B2566885 : Blo 1350994 2566885 := bbase (se 4 (by rfl) ⟨240645, by rfl⟩ : syracuseStep 2566885 = 481291) (by norm_num)
theorem B2280197 : Blo 1350994 2280197 := bbase (se 4 (by rfl) ⟨213768, by rfl⟩ : syracuseStep 2280197 = 427537) (by norm_num)
theorem B3042053 : Blo 1350994 3042053 := bbase (se 4 (by rfl) ⟨285192, by rfl⟩ : syracuseStep 3042053 = 570385) (by norm_num)
theorem B1370929 : Blo 1350994 1370929 := bbase (se 2 (by rfl) ⟨514098, by rfl⟩ : syracuseStep 1370929 = 1028197) (by norm_num)
theorem B2739005 : Blo 1350994 2739005 := bbase (se 3 (by rfl) ⟨513563, by rfl⟩ : syracuseStep 2739005 = 1027127) (by norm_num)
theorem B3042125 : Blo 1350994 3042125 := bbase (se 3 (by rfl) ⟨570398, by rfl⟩ : syracuseStep 3042125 = 1140797) (by norm_num)
theorem B4565861 : Blo 1350994 4565861 := bbase (se 4 (by rfl) ⟨428049, by rfl⟩ : syracuseStep 4565861 = 856099) (by norm_num)
theorem B2280325 : Blo 1350994 2280325 := bbase (se 4 (by rfl) ⟨213780, by rfl⟩ : syracuseStep 2280325 = 427561) (by norm_num)
theorem B2886533 : Blo 1350994 2886533 := bbase (se 4 (by rfl) ⟨270612, by rfl⟩ : syracuseStep 2886533 = 541225) (by norm_num)
theorem B2567045 : Blo 1350994 2567045 := bbase (se 4 (by rfl) ⟨240660, by rfl⟩ : syracuseStep 2567045 = 481321) (by norm_num)
theorem B1444753 : Blo 1350994 1444753 := bbase (se 2 (by rfl) ⟨541782, by rfl⟩ : syracuseStep 1444753 = 1083565) (by norm_num)
theorem B3042197 : Blo 1350994 3042197 := bbase (se 6 (by rfl) ⟨71301, by rfl⟩ : syracuseStep 3042197 = 142603) (by norm_num)
theorem B2280413 : Blo 1350994 2280413 := bbase (se 3 (by rfl) ⟨427577, by rfl⟩ : syracuseStep 2280413 = 855155) (by norm_num)
theorem B3042269 : Blo 1350994 3042269 := bbase (se 3 (by rfl) ⟨570425, by rfl⟩ : syracuseStep 3042269 = 1140851) (by norm_num)
theorem B6843365 : Blo 1350994 6843365 := bbase (se 4 (by rfl) ⟨641565, by rfl⟩ : syracuseStep 6843365 = 1283131) (by norm_num)
theorem B2026493 : Blo 1350994 2026493 := bbase (se 3 (by rfl) ⟨379967, by rfl⟩ : syracuseStep 2026493 = 759935) (by norm_num)
theorem B2886653 : Blo 1350994 2886653 := bbase (se 3 (by rfl) ⟨541247, by rfl⟩ : syracuseStep 2886653 = 1082495) (by norm_num)
theorem B2739205 : Blo 1350994 2739205 := bbase (se 4 (by rfl) ⟨256800, by rfl⟩ : syracuseStep 2739205 = 513601) (by norm_num)
theorem B2026517 : Blo 1350994 2026517 := bbase (se 6 (by rfl) ⟨47496, by rfl⟩ : syracuseStep 2026517 = 94993) (by norm_num)
theorem B2567189 : Blo 1350994 2567189 := bbase (se 6 (by rfl) ⟨60168, by rfl⟩ : syracuseStep 2567189 = 120337) (by norm_num)
theorem B3042341 : Blo 1350994 3042341 := bbase (se 4 (by rfl) ⟨285219, by rfl⟩ : syracuseStep 3042341 = 570439) (by norm_num)
theorem B2026541 : Blo 1350994 2026541 := bbase (se 3 (by rfl) ⟨379976, by rfl⟩ : syracuseStep 2026541 = 759953) (by norm_num)
theorem B2026565 : Blo 1350994 2026565 := bbase (se 4 (by rfl) ⟨189990, by rfl⟩ : syracuseStep 2026565 = 379981) (by norm_num)
theorem B2026589 : Blo 1350994 2026589 := bbase (se 3 (by rfl) ⟨379985, by rfl⟩ : syracuseStep 2026589 = 759971) (by norm_num)
theorem B2280541 : Blo 1350994 2280541 := bbase (se 3 (by rfl) ⟨427601, by rfl⟩ : syracuseStep 2280541 = 855203) (by norm_num)
theorem B1625189 : Blo 1350994 1625189 := bbase (se 4 (by rfl) ⟨152361, by rfl⟩ : syracuseStep 1625189 = 304723) (by norm_num)
theorem B5778533 : Blo 1350994 5778533 := bbase (se 4 (by rfl) ⟨541737, by rfl⟩ : syracuseStep 5778533 = 1083475) (by norm_num)
theorem B3042413 : Blo 1350994 3042413 := bbase (se 3 (by rfl) ⟨570452, by rfl⟩ : syracuseStep 3042413 = 1140905) (by norm_num)
theorem B2026613 : Blo 1350994 2026613 := bbase (se 5 (by rfl) ⟨94997, by rfl⟩ : syracuseStep 2026613 = 189995) (by norm_num)
theorem B2026637 : Blo 1350994 2026637 := bbase (se 3 (by rfl) ⟨379994, by rfl⟩ : syracuseStep 2026637 = 759989) (by norm_num)
theorem B19762325 : Blo 1350994 19762325 := bbase (se 6 (by rfl) ⟨463179, by rfl⟩ : syracuseStep 19762325 = 926359) (by norm_num)
theorem B2026661 : Blo 1350994 2026661 := bbase (se 4 (by rfl) ⟨189999, by rfl⟩ : syracuseStep 2026661 = 379999) (by norm_num)
theorem B2280629 : Blo 1350994 2280629 := bbase (se 5 (by rfl) ⟨106904, by rfl⟩ : syracuseStep 2280629 = 213809) (by norm_num)
theorem B3042485 : Blo 1350994 3042485 := bbase (se 5 (by rfl) ⟨142616, by rfl⟩ : syracuseStep 3042485 = 285233) (by norm_num)
theorem B2026685 : Blo 1350994 2026685 := bbase (se 3 (by rfl) ⟨380003, by rfl⟩ : syracuseStep 2026685 = 760007) (by norm_num)
theorem B2026709 : Blo 1350994 2026709 := bbase (se 7 (by rfl) ⟨23750, by rfl⟩ : syracuseStep 2026709 = 47501) (by norm_num)
theorem B2026733 : Blo 1350994 2026733 := bbase (se 3 (by rfl) ⟨380012, by rfl⟩ : syracuseStep 2026733 = 760025) (by norm_num)
theorem B3042557 : Blo 1350994 3042557 := bbase (se 3 (by rfl) ⟨570479, by rfl⟩ : syracuseStep 3042557 = 1140959) (by norm_num)
theorem B2026757 : Blo 1350994 2026757 := bbase (se 4 (by rfl) ⟨190008, by rfl⟩ : syracuseStep 2026757 = 380017) (by norm_num)
theorem B1625357 : Blo 1350994 1625357 := bbase (se 3 (by rfl) ⟨304754, by rfl⟩ : syracuseStep 1625357 = 609509) (by norm_num)
theorem B4566293 : Blo 1350994 4566293 := bbase (se 6 (by rfl) ⟨107022, by rfl⟩ : syracuseStep 4566293 = 214045) (by norm_num)
theorem B2026781 : Blo 1350994 2026781 := bbase (se 3 (by rfl) ⟨380021, by rfl⟩ : syracuseStep 2026781 = 760043) (by norm_num)
theorem B2026805 : Blo 1350994 2026805 := bbase (se 5 (by rfl) ⟨95006, by rfl⟩ : syracuseStep 2026805 = 190013) (by norm_num)
theorem B2280757 : Blo 1350994 2280757 := bbase (se 5 (by rfl) ⟨106910, by rfl⟩ : syracuseStep 2280757 = 213821) (by norm_num)
theorem B2567477 : Blo 1350994 2567477 := bbase (se 5 (by rfl) ⟨120350, by rfl⟩ : syracuseStep 2567477 = 240701) (by norm_num)
theorem B2436421 : Blo 1350994 2436421 := bbase (se 4 (by rfl) ⟨228414, by rfl⟩ : syracuseStep 2436421 = 456829) (by norm_num)
theorem B3042629 : Blo 1350994 3042629 := bbase (se 4 (by rfl) ⟨285246, by rfl⟩ : syracuseStep 3042629 = 570493) (by norm_num)
theorem B2026829 : Blo 1350994 2026829 := bbase (se 3 (by rfl) ⟨380030, by rfl⟩ : syracuseStep 2026829 = 760061) (by norm_num)
theorem B5778773 : Blo 1350994 5778773 := bbase (se 11 (by rfl) ⟨4232, by rfl⟩ : syracuseStep 5778773 = 8465) (by norm_num)
theorem B2026853 : Blo 1350994 2026853 := bbase (se 4 (by rfl) ⟨190017, by rfl⟩ : syracuseStep 2026853 = 380035) (by norm_num)
theorem B2026877 : Blo 1350994 2026877 := bbase (se 3 (by rfl) ⟨380039, by rfl⟩ : syracuseStep 2026877 = 760079) (by norm_num)
theorem B2280845 : Blo 1350994 2280845 := bbase (se 3 (by rfl) ⟨427658, by rfl⟩ : syracuseStep 2280845 = 855317) (by norm_num)
theorem B3042701 : Blo 1350994 3042701 := bbase (se 3 (by rfl) ⟨570506, by rfl⟩ : syracuseStep 3042701 = 1141013) (by norm_num)
theorem B2026901 : Blo 1350994 2026901 := bbase (se 6 (by rfl) ⟨47505, by rfl⟩ : syracuseStep 2026901 = 95011) (by norm_num)
theorem B3657109 : Blo 1350994 3657109 := bbase (se 6 (by rfl) ⟨85713, by rfl⟩ : syracuseStep 3657109 = 171427) (by norm_num)
theorem B2026925 : Blo 1350994 2026925 := bbase (se 3 (by rfl) ⟨380048, by rfl⟩ : syracuseStep 2026925 = 760097) (by norm_num)
theorem B2026949 : Blo 1350994 2026949 := bbase (se 4 (by rfl) ⟨190026, by rfl⟩ : syracuseStep 2026949 = 380053) (by norm_num)
theorem B2567629 : Blo 1350994 2567629 := bbase (se 3 (by rfl) ⟨481430, by rfl⟩ : syracuseStep 2567629 = 962861) (by norm_num)
theorem B3042773 : Blo 1350994 3042773 := bbase (se 7 (by rfl) ⟨35657, by rfl⟩ : syracuseStep 3042773 = 71315) (by norm_num)
theorem B2026973 : Blo 1350994 2026973 := bbase (se 3 (by rfl) ⟨380057, by rfl⟩ : syracuseStep 2026973 = 760115) (by norm_num)
theorem B2026997 : Blo 1350994 2026997 := bbase (se 5 (by rfl) ⟨95015, by rfl⟩ : syracuseStep 2026997 = 190031) (by norm_num)
theorem B8220149 : Blo 1350994 8220149 := bbase (se 5 (by rfl) ⟨385319, by rfl⟩ : syracuseStep 8220149 = 770639) (by norm_num)
theorem B5131781 : Blo 1350994 5131781 := bbase (se 4 (by rfl) ⟨481104, by rfl⟩ : syracuseStep 5131781 = 962209) (by norm_num)
theorem B2027021 : Blo 1350994 2027021 := bbase (se 3 (by rfl) ⟨380066, by rfl⟩ : syracuseStep 2027021 = 760133) (by norm_num)
theorem B2280973 : Blo 1350994 2280973 := bbase (se 3 (by rfl) ⟨427682, by rfl⟩ : syracuseStep 2280973 = 855365) (by norm_num)
theorem B2436637 : Blo 1350994 2436637 := bbase (se 3 (by rfl) ⟨456869, by rfl⟩ : syracuseStep 2436637 = 913739) (by norm_num)
theorem B3042845 : Blo 1350994 3042845 := bbase (se 3 (by rfl) ⟨570533, by rfl⟩ : syracuseStep 3042845 = 1141067) (by norm_num)
theorem B2027045 : Blo 1350994 2027045 := bbase (se 4 (by rfl) ⟨190035, by rfl⟩ : syracuseStep 2027045 = 380071) (by norm_num)
theorem B2027069 : Blo 1350994 2027069 := bbase (se 3 (by rfl) ⟨380075, by rfl⟩ : syracuseStep 2027069 = 760151) (by norm_num)
theorem B2027093 : Blo 1350994 2027093 := bbase (se 8 (by rfl) ⟨11877, by rfl⟩ : syracuseStep 2027093 = 23755) (by norm_num)
theorem B2281061 : Blo 1350994 2281061 := bbase (se 4 (by rfl) ⟨213849, by rfl⟩ : syracuseStep 2281061 = 427699) (by norm_num)
theorem B3042917 : Blo 1350994 3042917 := bbase (se 4 (by rfl) ⟨285273, by rfl⟩ : syracuseStep 3042917 = 570547) (by norm_num)
theorem B2027117 : Blo 1350994 2027117 := bbase (se 3 (by rfl) ⟨380084, by rfl⟩ : syracuseStep 2027117 = 760169) (by norm_num)
theorem B2887285 : Blo 1350994 2887285 := bbase (se 5 (by rfl) ⟨135341, by rfl⟩ : syracuseStep 2887285 = 270683) (by norm_num)
theorem B10407541 : Blo 1350994 10407541 := bbase (se 5 (by rfl) ⟨487853, by rfl⟩ : syracuseStep 10407541 = 975707) (by norm_num)
theorem B2027141 : Blo 1350994 2027141 := bbase (se 4 (by rfl) ⟨190044, by rfl⟩ : syracuseStep 2027141 = 380089) (by norm_num)
theorem B27741845 : Blo 1350994 27741845 := bbase (se 6 (by rfl) ⟨650199, by rfl⟩ : syracuseStep 27741845 = 1300399) (by norm_num)
theorem B2027165 : Blo 1350994 2027165 := bbase (se 3 (by rfl) ⟨380093, by rfl⟩ : syracuseStep 2027165 = 760187) (by norm_num)
theorem B3124909 : Blo 1350994 3124909 := bbase (se 3 (by rfl) ⟨585920, by rfl⟩ : syracuseStep 3124909 = 1171841) (by norm_num)
theorem B3042989 : Blo 1350994 3042989 := bbase (se 3 (by rfl) ⟨570560, by rfl⟩ : syracuseStep 3042989 = 1141121) (by norm_num)
theorem B2027189 : Blo 1350994 2027189 := bbase (se 5 (by rfl) ⟨95024, by rfl⟩ : syracuseStep 2027189 = 190049) (by norm_num)
theorem B8220341 : Blo 1350994 8220341 := bbase (se 5 (by rfl) ⟨385328, by rfl⟩ : syracuseStep 8220341 = 770657) (by norm_num)
theorem B2027213 : Blo 1350994 2027213 := bbase (se 3 (by rfl) ⟨380102, by rfl⟩ : syracuseStep 2027213 = 760205) (by norm_num)
theorem B24678101 : Blo 1350994 24678101 := bbase (se 7 (by rfl) ⟨289196, by rfl⟩ : syracuseStep 24678101 = 578393) (by norm_num)
theorem B2027237 : Blo 1350994 2027237 := bbase (se 4 (by rfl) ⟨190053, by rfl⟩ : syracuseStep 2027237 = 380107) (by norm_num)
theorem B2281189 : Blo 1350994 2281189 := bbase (se 4 (by rfl) ⟨213861, by rfl⟩ : syracuseStep 2281189 = 427723) (by norm_num)
theorem B2166509 : Blo 1350994 2166509 := bbase (se 3 (by rfl) ⟨406220, by rfl⟩ : syracuseStep 2166509 = 812441) (by norm_num)
theorem B3043061 : Blo 1350994 3043061 := bbase (se 5 (by rfl) ⟨142643, by rfl⟩ : syracuseStep 3043061 = 285287) (by norm_num)
theorem B2027261 : Blo 1350994 2027261 := bbase (se 3 (by rfl) ⟨380111, by rfl⟩ : syracuseStep 2027261 = 760223) (by norm_num)
theorem B2567933 : Blo 1350994 2567933 := bbase (se 3 (by rfl) ⟨481487, by rfl⟩ : syracuseStep 2567933 = 962975) (by norm_num)
theorem B2027285 : Blo 1350994 2027285 := bbase (se 6 (by rfl) ⟨47514, by rfl⟩ : syracuseStep 2027285 = 95029) (by norm_num)
theorem B3419941 : Blo 1350994 3419941 := bbase (se 4 (by rfl) ⟨320619, by rfl⟩ : syracuseStep 3419941 = 641239) (by norm_num)
theorem B5132069 : Blo 1350994 5132069 := bbase (se 4 (by rfl) ⟨481131, by rfl⟩ : syracuseStep 5132069 = 962263) (by norm_num)
theorem B2027309 : Blo 1350994 2027309 := bbase (se 3 (by rfl) ⟨380120, by rfl⟩ : syracuseStep 2027309 = 760241) (by norm_num)
theorem B2281277 : Blo 1350994 2281277 := bbase (se 3 (by rfl) ⟨427739, by rfl⟩ : syracuseStep 2281277 = 855479) (by norm_num)
theorem B3043133 : Blo 1350994 3043133 := bbase (se 3 (by rfl) ⟨570587, by rfl⟩ : syracuseStep 3043133 = 1141175) (by norm_num)
theorem B2027333 : Blo 1350994 2027333 := bbase (se 4 (by rfl) ⟨190062, by rfl⟩ : syracuseStep 2027333 = 380125) (by norm_num)
theorem B6254405 : Blo 1350994 6254405 := bbase (se 4 (by rfl) ⟨586350, by rfl⟩ : syracuseStep 6254405 = 1172701) (by norm_num)
theorem B2027357 : Blo 1350994 2027357 := bbase (se 3 (by rfl) ⟨380129, by rfl⟩ : syracuseStep 2027357 = 760259) (by norm_num)
theorem B2027381 : Blo 1350994 2027381 := bbase (se 5 (by rfl) ⟨95033, by rfl⟩ : syracuseStep 2027381 = 190067) (by norm_num)
theorem B3043205 : Blo 1350994 3043205 := bbase (se 4 (by rfl) ⟨285300, by rfl⟩ : syracuseStep 3043205 = 570601) (by norm_num)
theorem B2027405 : Blo 1350994 2027405 := bbase (se 3 (by rfl) ⟨380138, by rfl⟩ : syracuseStep 2027405 = 760277) (by norm_num)
theorem B3420053 : Blo 1350994 3420053 := bbase (se 6 (by rfl) ⟨80157, by rfl⟩ : syracuseStep 3420053 = 160315) (by norm_num)
theorem B2027429 : Blo 1350994 2027429 := bbase (se 4 (by rfl) ⟨190071, by rfl⟩ : syracuseStep 2027429 = 380143) (by norm_num)
theorem B2027453 : Blo 1350994 2027453 := bbase (se 3 (by rfl) ⟨380147, by rfl⟩ : syracuseStep 2027453 = 760295) (by norm_num)
theorem B2281405 : Blo 1350994 2281405 := bbase (se 3 (by rfl) ⟨427763, by rfl⟩ : syracuseStep 2281405 = 855527) (by norm_num)
theorem B3043277 : Blo 1350994 3043277 := bbase (se 3 (by rfl) ⟨570614, by rfl⟩ : syracuseStep 3043277 = 1141229) (by norm_num)
theorem B2027477 : Blo 1350994 2027477 := bbase (se 7 (by rfl) ⟨23759, by rfl⟩ : syracuseStep 2027477 = 47519) (by norm_num)
theorem B2027501 : Blo 1350994 2027501 := bbase (se 3 (by rfl) ⟨380156, by rfl⟩ : syracuseStep 2027501 = 760313) (by norm_num)
theorem B2027525 : Blo 1350994 2027525 := bbase (se 4 (by rfl) ⟨190080, by rfl⟩ : syracuseStep 2027525 = 380161) (by norm_num)
theorem B2281493 : Blo 1350994 2281493 := bbase (se 6 (by rfl) ⟨53472, by rfl⟩ : syracuseStep 2281493 = 106945) (by norm_num)
theorem B10268693 : Blo 1350994 10268693 := bbase (se 6 (by rfl) ⟨240672, by rfl⟩ : syracuseStep 10268693 = 481345) (by norm_num)
theorem B3043349 : Blo 1350994 3043349 := bbase (se 6 (by rfl) ⟨71328, by rfl⟩ : syracuseStep 3043349 = 142657) (by norm_num)
theorem B2027549 : Blo 1350994 2027549 := bbase (se 3 (by rfl) ⟨380165, by rfl⟩ : syracuseStep 2027549 = 760331) (by norm_num)
theorem B2027573 : Blo 1350994 2027573 := bbase (se 5 (by rfl) ⟨95042, by rfl⟩ : syracuseStep 2027573 = 190085) (by norm_num)
theorem B2027597 : Blo 1350994 2027597 := bbase (se 3 (by rfl) ⟨380174, by rfl⟩ : syracuseStep 2027597 = 760349) (by norm_num)
theorem B3420245 : Blo 1350994 3420245 := bbase (se 8 (by rfl) ⟨20040, by rfl⟩ : syracuseStep 3420245 = 40081) (by norm_num)
theorem B18493525 : Blo 1350994 18493525 := bbase (se 8 (by rfl) ⟨108360, by rfl⟩ : syracuseStep 18493525 = 216721) (by norm_num)
theorem B3043421 : Blo 1350994 3043421 := bbase (se 3 (by rfl) ⟨570641, by rfl⟩ : syracuseStep 3043421 = 1141283) (by norm_num)
theorem B2027621 : Blo 1350994 2027621 := bbase (se 4 (by rfl) ⟨190089, by rfl⟩ : syracuseStep 2027621 = 380179) (by norm_num)
theorem B2027645 : Blo 1350994 2027645 := bbase (se 3 (by rfl) ⟨380183, by rfl⟩ : syracuseStep 2027645 = 760367) (by norm_num)
theorem B4108421 : Blo 1350994 4108421 := bbase (se 4 (by rfl) ⟨385164, by rfl⟩ : syracuseStep 4108421 = 770329) (by norm_num)
theorem B2027669 : Blo 1350994 2027669 := bbase (se 6 (by rfl) ⟨47523, by rfl⟩ : syracuseStep 2027669 = 95047) (by norm_num)
theorem B2281621 : Blo 1350994 2281621 := bbase (se 6 (by rfl) ⟨53475, by rfl⟩ : syracuseStep 2281621 = 106951) (by norm_num)
theorem B3043493 : Blo 1350994 3043493 := bbase (se 4 (by rfl) ⟨285327, by rfl⟩ : syracuseStep 3043493 = 570655) (by norm_num)
theorem B2027693 : Blo 1350994 2027693 := bbase (se 3 (by rfl) ⟨380192, by rfl⟩ : syracuseStep 2027693 = 760385) (by norm_num)
theorem B2027717 : Blo 1350994 2027717 := bbase (se 4 (by rfl) ⟨190098, by rfl⟩ : syracuseStep 2027717 = 380197) (by norm_num)
theorem B2027741 : Blo 1350994 2027741 := bbase (se 3 (by rfl) ⟨380201, by rfl⟩ : syracuseStep 2027741 = 760403) (by norm_num)
theorem B2281709 : Blo 1350994 2281709 := bbase (se 3 (by rfl) ⟨427820, by rfl⟩ : syracuseStep 2281709 = 855641) (by norm_num)
theorem B3043565 : Blo 1350994 3043565 := bbase (se 3 (by rfl) ⟨570668, by rfl⟩ : syracuseStep 3043565 = 1141337) (by norm_num)
theorem B2167021 : Blo 1350994 2167021 := bbase (se 3 (by rfl) ⟨406316, by rfl⟩ : syracuseStep 2167021 = 812633) (by norm_num)
theorem B2027765 : Blo 1350994 2027765 := bbase (se 5 (by rfl) ⟨95051, by rfl⟩ : syracuseStep 2027765 = 190103) (by norm_num)
theorem B6844661 : Blo 1350994 6844661 := bbase (se 5 (by rfl) ⟨320843, by rfl⟩ : syracuseStep 6844661 = 641687) (by norm_num)
theorem B2027789 : Blo 1350994 2027789 := bbase (se 3 (by rfl) ⟨380210, by rfl⟩ : syracuseStep 2027789 = 760421) (by norm_num)
theorem B1519897 : Blo 1350994 1519897 := bbase (se 2 (by rfl) ⟨569961, by rfl⟩ : syracuseStep 1519897 = 1139923) (by norm_num)
theorem B2027813 : Blo 1350994 2027813 := bbase (se 4 (by rfl) ⟨190107, by rfl⟩ : syracuseStep 2027813 = 380215) (by norm_num)
theorem B6492469 : Blo 1350994 6492469 := bbase (se 5 (by rfl) ⟨304334, by rfl⟩ : syracuseStep 6492469 = 608669) (by norm_num)
theorem B2601269 : Blo 1350994 2601269 := bbase (se 5 (by rfl) ⟨121934, by rfl⟩ : syracuseStep 2601269 = 243869) (by norm_num)
theorem B3043637 : Blo 1350994 3043637 := bbase (se 5 (by rfl) ⟨142670, by rfl⟩ : syracuseStep 3043637 = 285341) (by norm_num)
theorem B1519933 : Blo 1350994 1519933 := bbase (se 3 (by rfl) ⟨284987, by rfl⟩ : syracuseStep 1519933 = 569975) (by norm_num)
theorem B2027837 : Blo 1350994 2027837 := bbase (se 3 (by rfl) ⟨380219, by rfl⟩ : syracuseStep 2027837 = 760439) (by norm_num)
theorem B2437445 : Blo 1350994 2437445 := bbase (se 4 (by rfl) ⟨228510, by rfl⟩ : syracuseStep 2437445 = 457021) (by norm_num)
theorem B2027861 : Blo 1350994 2027861 := bbase (se 10 (by rfl) ⟨2970, by rfl⟩ : syracuseStep 2027861 = 5941) (by norm_num)
theorem B19501397 : Blo 1350994 19501397 := bbase (se 10 (by rfl) ⟨28566, by rfl⟩ : syracuseStep 19501397 = 57133) (by norm_num)
theorem B1519969 : Blo 1350994 1519969 := bbase (se 2 (by rfl) ⟨569988, by rfl⟩ : syracuseStep 1519969 = 1139977) (by norm_num)
theorem B2027885 : Blo 1350994 2027885 := bbase (se 3 (by rfl) ⟨380228, by rfl⟩ : syracuseStep 2027885 = 760457) (by norm_num)
theorem B2281837 : Blo 1350994 2281837 := bbase (se 3 (by rfl) ⟨427844, by rfl⟩ : syracuseStep 2281837 = 855689) (by norm_num)
theorem B3043709 : Blo 1350994 3043709 := bbase (se 3 (by rfl) ⟨570695, by rfl⟩ : syracuseStep 3043709 = 1141391) (by norm_num)
theorem B1520005 : Blo 1350994 1520005 := bbase (se 4 (by rfl) ⟨142500, by rfl⟩ : syracuseStep 1520005 = 285001) (by norm_num)
theorem B2027909 : Blo 1350994 2027909 := bbase (se 4 (by rfl) ⟨190116, by rfl⟩ : syracuseStep 2027909 = 380233) (by norm_num)
theorem B2027933 : Blo 1350994 2027933 := bbase (se 3 (by rfl) ⟨380237, by rfl⟩ : syracuseStep 2027933 = 760475) (by norm_num)
theorem B1520041 : Blo 1350994 1520041 := bbase (se 2 (by rfl) ⟨570015, by rfl⟩ : syracuseStep 1520041 = 1140031) (by norm_num)
theorem B3420589 : Blo 1350994 3420589 := bbase (se 3 (by rfl) ⟨641360, by rfl⟩ : syracuseStep 3420589 = 1282721) (by norm_num)
theorem B10260917 : Blo 1350994 10260917 := bbase (se 5 (by rfl) ⟨480980, by rfl⟩ : syracuseStep 10260917 = 961961) (by norm_num)
theorem B2027957 : Blo 1350994 2027957 := bbase (se 5 (by rfl) ⟨95060, by rfl⟩ : syracuseStep 2027957 = 190121) (by norm_num)
theorem B2281925 : Blo 1350994 2281925 := bbase (se 4 (by rfl) ⟨213930, by rfl⟩ : syracuseStep 2281925 = 427861) (by norm_num)
theorem B3043781 : Blo 1350994 3043781 := bbase (se 4 (by rfl) ⟨285354, by rfl⟩ : syracuseStep 3043781 = 570709) (by norm_num)
theorem B1520077 : Blo 1350994 1520077 := bbase (se 3 (by rfl) ⟨285014, by rfl⟩ : syracuseStep 1520077 = 570029) (by norm_num)
theorem B2027981 : Blo 1350994 2027981 := bbase (se 3 (by rfl) ⟨380246, by rfl⟩ : syracuseStep 2027981 = 760493) (by norm_num)
theorem B2437589 : Blo 1350994 2437589 := bbase (se 7 (by rfl) ⟨28565, by rfl⟩ : syracuseStep 2437589 = 57131) (by norm_num)
theorem B2224613 : Blo 1350994 2224613 := bbase (se 4 (by rfl) ⟨208557, by rfl⟩ : syracuseStep 2224613 = 417115) (by norm_num)
theorem B2028005 : Blo 1350994 2028005 := bbase (se 4 (by rfl) ⟨190125, by rfl⟩ : syracuseStep 2028005 = 380251) (by norm_num)
theorem B2888173 : Blo 1350994 2888173 := bbase (se 3 (by rfl) ⟨541532, by rfl⟩ : syracuseStep 2888173 = 1083065) (by norm_num)
theorem B1520113 : Blo 1350994 1520113 := bbase (se 2 (by rfl) ⟨570042, by rfl⟩ : syracuseStep 1520113 = 1140085) (by norm_num)
theorem B2028029 : Blo 1350994 2028029 := bbase (se 3 (by rfl) ⟨380255, by rfl⟩ : syracuseStep 2028029 = 760511) (by norm_num)
theorem B3043853 : Blo 1350994 3043853 := bbase (se 3 (by rfl) ⟨570722, by rfl⟩ : syracuseStep 3043853 = 1141445) (by norm_num)
theorem B1520149 : Blo 1350994 1520149 := bbase (se 6 (by rfl) ⟨35628, by rfl⟩ : syracuseStep 1520149 = 71257) (by norm_num)
theorem B2028053 : Blo 1350994 2028053 := bbase (se 6 (by rfl) ⟨47532, by rfl⟩ : syracuseStep 2028053 = 95065) (by norm_num)
theorem B3420701 : Blo 1350994 3420701 := bbase (se 3 (by rfl) ⟨641381, by rfl⟩ : syracuseStep 3420701 = 1282763) (by norm_num)
theorem B2028077 : Blo 1350994 2028077 := bbase (se 3 (by rfl) ⟨380264, by rfl⟩ : syracuseStep 2028077 = 760529) (by norm_num)
theorem B1520185 : Blo 1350994 1520185 := bbase (se 2 (by rfl) ⟨570069, by rfl⟩ : syracuseStep 1520185 = 1140139) (by norm_num)
theorem B2028101 : Blo 1350994 2028101 := bbase (se 4 (by rfl) ⟨190134, by rfl⟩ : syracuseStep 2028101 = 380269) (by norm_num)
theorem B2282053 : Blo 1350994 2282053 := bbase (se 4 (by rfl) ⟨213942, by rfl⟩ : syracuseStep 2282053 = 427885) (by norm_num)
theorem B12997205 : Blo 1350994 12997205 := bbase (se 8 (by rfl) ⟨76155, by rfl⟩ : syracuseStep 12997205 = 152311) (by norm_num)
theorem B3043925 : Blo 1350994 3043925 := bbase (se 8 (by rfl) ⟨17835, by rfl⟩ : syracuseStep 3043925 = 35671) (by norm_num)
theorem B1520221 : Blo 1350994 1520221 := bbase (se 3 (by rfl) ⟨285041, by rfl⟩ : syracuseStep 1520221 = 570083) (by norm_num)
theorem B2028125 : Blo 1350994 2028125 := bbase (se 3 (by rfl) ⟨380273, by rfl⟩ : syracuseStep 2028125 = 760547) (by norm_num)
theorem B2888293 : Blo 1350994 2888293 := bbase (se 4 (by rfl) ⟨270777, by rfl⟩ : syracuseStep 2888293 = 541555) (by norm_num)
theorem B2028149 : Blo 1350994 2028149 := bbase (se 5 (by rfl) ⟨95069, by rfl⟩ : syracuseStep 2028149 = 190139) (by norm_num)
theorem B1520257 : Blo 1350994 1520257 := bbase (se 2 (by rfl) ⟨570096, by rfl⟩ : syracuseStep 1520257 = 1140193) (by norm_num)
theorem B2028173 : Blo 1350994 2028173 := bbase (se 3 (by rfl) ⟨380282, by rfl⟩ : syracuseStep 2028173 = 760565) (by norm_num)
theorem B2282141 : Blo 1350994 2282141 := bbase (se 3 (by rfl) ⟨427901, by rfl⟩ : syracuseStep 2282141 = 855803) (by norm_num)
theorem B3043997 : Blo 1350994 3043997 := bbase (se 3 (by rfl) ⟨570749, by rfl⟩ : syracuseStep 3043997 = 1141499) (by norm_num)
theorem B1520293 : Blo 1350994 1520293 := bbase (se 4 (by rfl) ⟨142527, by rfl⟩ : syracuseStep 1520293 = 285055) (by norm_num)
theorem B2028197 : Blo 1350994 2028197 := bbase (se 4 (by rfl) ⟨190143, by rfl⟩ : syracuseStep 2028197 = 380287) (by norm_num)
theorem B2437805 : Blo 1350994 2437805 := bbase (se 3 (by rfl) ⟨457088, by rfl⟩ : syracuseStep 2437805 = 914177) (by norm_num)
theorem B2028221 : Blo 1350994 2028221 := bbase (se 3 (by rfl) ⟨380291, by rfl⟩ : syracuseStep 2028221 = 760583) (by norm_num)
theorem B4870853 : Blo 1350994 4870853 := bbase (se 4 (by rfl) ⟨456642, by rfl⟩ : syracuseStep 4870853 = 913285) (by norm_num)
theorem B1520329 : Blo 1350994 1520329 := bbase (se 2 (by rfl) ⟨570123, by rfl⟩ : syracuseStep 1520329 = 1140247) (by norm_num)
theorem B2028245 : Blo 1350994 2028245 := bbase (se 7 (by rfl) ⟨23768, by rfl⟩ : syracuseStep 2028245 = 47537) (by norm_num)
theorem B3420893 : Blo 1350994 3420893 := bbase (se 3 (by rfl) ⟨641417, by rfl⟩ : syracuseStep 3420893 = 1282835) (by norm_num)
theorem B3248869 : Blo 1350994 3248869 := bbase (se 4 (by rfl) ⟨304581, by rfl⟩ : syracuseStep 3248869 = 609163) (by norm_num)
theorem B3044069 : Blo 1350994 3044069 := bbase (se 4 (by rfl) ⟨285381, by rfl⟩ : syracuseStep 3044069 = 570763) (by norm_num)
theorem B1520365 : Blo 1350994 1520365 := bbase (se 3 (by rfl) ⟨285068, by rfl⟩ : syracuseStep 1520365 = 570137) (by norm_num)
theorem B2028269 : Blo 1350994 2028269 := bbase (se 3 (by rfl) ⟨380300, by rfl⟩ : syracuseStep 2028269 = 760601) (by norm_num)
theorem B2028293 : Blo 1350994 2028293 := bbase (se 4 (by rfl) ⟨190152, by rfl⟩ : syracuseStep 2028293 = 380305) (by norm_num)
theorem B1520401 : Blo 1350994 1520401 := bbase (se 2 (by rfl) ⟨570150, by rfl⟩ : syracuseStep 1520401 = 1140301) (by norm_num)
theorem B2028317 : Blo 1350994 2028317 := bbase (se 3 (by rfl) ⟨380309, by rfl⟩ : syracuseStep 2028317 = 760619) (by norm_num)
theorem B2282269 : Blo 1350994 2282269 := bbase (se 3 (by rfl) ⟨427925, by rfl⟩ : syracuseStep 2282269 = 855851) (by norm_num)
theorem B3044141 : Blo 1350994 3044141 := bbase (se 3 (by rfl) ⟨570776, by rfl⟩ : syracuseStep 3044141 = 1141553) (by norm_num)
theorem B1520437 : Blo 1350994 1520437 := bbase (se 5 (by rfl) ⟨71270, by rfl⟩ : syracuseStep 1520437 = 142541) (by norm_num)
theorem B2028341 : Blo 1350994 2028341 := bbase (se 5 (by rfl) ⟨95078, by rfl⟩ : syracuseStep 2028341 = 190157) (by norm_num)
theorem B2028365 : Blo 1350994 2028365 := bbase (se 3 (by rfl) ⟨380318, by rfl⟩ : syracuseStep 2028365 = 760637) (by norm_num)
theorem B1520473 : Blo 1350994 1520473 := bbase (se 2 (by rfl) ⟨570177, by rfl⟩ : syracuseStep 1520473 = 1140355) (by norm_num)
theorem B2028389 : Blo 1350994 2028389 := bbase (se 4 (by rfl) ⟨190161, by rfl⟩ : syracuseStep 2028389 = 380323) (by norm_num)
theorem B2888549 : Blo 1350994 2888549 := bbase (se 4 (by rfl) ⟨270801, by rfl⟩ : syracuseStep 2888549 = 541603) (by norm_num)
theorem B2282357 : Blo 1350994 2282357 := bbase (se 5 (by rfl) ⟨106985, by rfl⟩ : syracuseStep 2282357 = 213971) (by norm_num)
theorem B3044213 : Blo 1350994 3044213 := bbase (se 5 (by rfl) ⟨142697, by rfl⟩ : syracuseStep 3044213 = 285395) (by norm_num)
theorem B1520509 : Blo 1350994 1520509 := bbase (se 3 (by rfl) ⟨285095, by rfl⟩ : syracuseStep 1520509 = 570191) (by norm_num)
theorem B2028413 : Blo 1350994 2028413 := bbase (se 3 (by rfl) ⟨380327, by rfl⟩ : syracuseStep 2028413 = 760655) (by norm_num)
theorem B2028437 : Blo 1350994 2028437 := bbase (se 6 (by rfl) ⟨47541, by rfl⟩ : syracuseStep 2028437 = 95083) (by norm_num)
theorem B1520545 : Blo 1350994 1520545 := bbase (se 2 (by rfl) ⟨570204, by rfl⟩ : syracuseStep 1520545 = 1140409) (by norm_num)
theorem B2028461 : Blo 1350994 2028461 := bbase (se 3 (by rfl) ⟨380336, by rfl⟩ : syracuseStep 2028461 = 760673) (by norm_num)
theorem B14062517 : Blo 1350994 14062517 := bbase (se 5 (by rfl) ⟨659180, by rfl⟩ : syracuseStep 14062517 = 1318361) (by norm_num)
theorem B4559813 : Blo 1350994 4559813 := bbase (se 4 (by rfl) ⟨427482, by rfl⟩ : syracuseStep 4559813 = 854965) (by norm_num)
theorem B1520581 : Blo 1350994 1520581 := bbase (se 4 (by rfl) ⟨142554, by rfl⟩ : syracuseStep 1520581 = 285109) (by norm_num)
theorem B5133253 : Blo 1350994 5133253 := bbase (se 4 (by rfl) ⟨481242, by rfl⟩ : syracuseStep 5133253 = 962485) (by norm_num)
theorem B2028485 : Blo 1350994 2028485 := bbase (se 4 (by rfl) ⟨190170, by rfl⟩ : syracuseStep 2028485 = 380341) (by norm_num)
theorem B2028509 : Blo 1350994 2028509 := bbase (se 3 (by rfl) ⟨380345, by rfl⟩ : syracuseStep 2028509 = 760691) (by norm_num)
theorem B4109285 : Blo 1350994 4109285 := bbase (se 4 (by rfl) ⟨385245, by rfl⟩ : syracuseStep 4109285 = 770491) (by norm_num)
theorem B1520617 : Blo 1350994 1520617 := bbase (se 2 (by rfl) ⟨570231, by rfl⟩ : syracuseStep 1520617 = 1140463) (by norm_num)
theorem B2028533 : Blo 1350994 2028533 := bbase (se 5 (by rfl) ⟨95087, by rfl⟩ : syracuseStep 2028533 = 190175) (by norm_num)
theorem B2282485 : Blo 1350994 2282485 := bbase (se 5 (by rfl) ⟨106991, by rfl⟩ : syracuseStep 2282485 = 213983) (by norm_num)
theorem B1520653 : Blo 1350994 1520653 := bbase (se 3 (by rfl) ⟨285122, by rfl⟩ : syracuseStep 1520653 = 570245) (by norm_num)
theorem B2028557 : Blo 1350994 2028557 := bbase (se 3 (by rfl) ⟨380354, by rfl⟩ : syracuseStep 2028557 = 760709) (by norm_num)
theorem B2028581 : Blo 1350994 2028581 := bbase (se 4 (by rfl) ⟨190179, by rfl⟩ : syracuseStep 2028581 = 380359) (by norm_num)
theorem B1520689 : Blo 1350994 1520689 := bbase (se 2 (by rfl) ⟨570258, by rfl⟩ : syracuseStep 1520689 = 1140517) (by norm_num)
theorem B3421237 : Blo 1350994 3421237 := bbase (se 5 (by rfl) ⟨160370, by rfl⟩ : syracuseStep 3421237 = 320741) (by norm_num)
theorem B2028605 : Blo 1350994 2028605 := bbase (se 3 (by rfl) ⟨380363, by rfl⟩ : syracuseStep 2028605 = 760727) (by norm_num)
theorem B2282573 : Blo 1350994 2282573 := bbase (se 3 (by rfl) ⟨427982, by rfl⟩ : syracuseStep 2282573 = 855965) (by norm_num)
theorem B1520725 : Blo 1350994 1520725 := bbase (se 8 (by rfl) ⟨8910, by rfl⟩ : syracuseStep 1520725 = 17821) (by norm_num)
theorem B2028629 : Blo 1350994 2028629 := bbase (se 8 (by rfl) ⟨11886, by rfl⟩ : syracuseStep 2028629 = 23773) (by norm_num)
theorem B1733729 : Blo 1350994 1733729 := bbase (se 2 (by rfl) ⟨650148, by rfl⟩ : syracuseStep 1733729 = 1300297) (by norm_num)
theorem B2028653 : Blo 1350994 2028653 := bbase (se 3 (by rfl) ⟨380372, by rfl⟩ : syracuseStep 2028653 = 760745) (by norm_num)
theorem B1520761 : Blo 1350994 1520761 := bbase (se 2 (by rfl) ⟨570285, by rfl⟩ : syracuseStep 1520761 = 1140571) (by norm_num)
theorem B2028677 : Blo 1350994 2028677 := bbase (se 4 (by rfl) ⟨190188, by rfl⟩ : syracuseStep 2028677 = 380377) (by norm_num)
theorem B1520797 : Blo 1350994 1520797 := bbase (se 3 (by rfl) ⟨285149, by rfl⟩ : syracuseStep 1520797 = 570299) (by norm_num)
theorem B2028701 : Blo 1350994 2028701 := bbase (se 3 (by rfl) ⟨380381, by rfl⟩ : syracuseStep 2028701 = 760763) (by norm_num)
theorem B3421349 : Blo 1350994 3421349 := bbase (se 4 (by rfl) ⟨320751, by rfl⟩ : syracuseStep 3421349 = 641503) (by norm_num)
theorem B5633189 : Blo 1350994 5633189 := bbase (se 4 (by rfl) ⟨528111, by rfl⟩ : syracuseStep 5633189 = 1056223) (by norm_num)
theorem B6501541 : Blo 1350994 6501541 := bbase (se 4 (by rfl) ⟨609519, by rfl⟩ : syracuseStep 6501541 = 1219039) (by norm_num)
theorem B2028725 : Blo 1350994 2028725 := bbase (se 5 (by rfl) ⟨95096, by rfl⟩ : syracuseStep 2028725 = 190193) (by norm_num)
theorem B1520833 : Blo 1350994 1520833 := bbase (se 2 (by rfl) ⟨570312, by rfl⟩ : syracuseStep 1520833 = 1140625) (by norm_num)
theorem B5772485 : Blo 1350994 5772485 := bbase (se 4 (by rfl) ⟨541170, by rfl⟩ : syracuseStep 5772485 = 1082341) (by norm_num)
theorem B2028749 : Blo 1350994 2028749 := bbase (se 3 (by rfl) ⟨380390, by rfl⟩ : syracuseStep 2028749 = 760781) (by norm_num)
theorem B2282701 : Blo 1350994 2282701 := bbase (se 3 (by rfl) ⟨428006, by rfl⟩ : syracuseStep 2282701 = 856013) (by norm_num)
theorem B1520869 : Blo 1350994 1520869 := bbase (se 4 (by rfl) ⟨142581, by rfl⟩ : syracuseStep 1520869 = 285163) (by norm_num)
theorem B2028773 : Blo 1350994 2028773 := bbase (se 4 (by rfl) ⟨190197, by rfl⟩ : syracuseStep 2028773 = 380395) (by norm_num)
theorem B5133557 : Blo 1350994 5133557 := bbase (se 5 (by rfl) ⟨240635, by rfl⟩ : syracuseStep 5133557 = 481271) (by norm_num)
theorem B2028797 : Blo 1350994 2028797 := bbase (se 3 (by rfl) ⟨380399, by rfl⟩ : syracuseStep 2028797 = 760799) (by norm_num)
theorem B1520905 : Blo 1350994 1520905 := bbase (se 2 (by rfl) ⟨570339, by rfl⟩ : syracuseStep 1520905 = 1140679) (by norm_num)
theorem B2028821 : Blo 1350994 2028821 := bbase (se 6 (by rfl) ⟨47550, by rfl⟩ : syracuseStep 2028821 = 95101) (by norm_num)
theorem B2282789 : Blo 1350994 2282789 := bbase (se 4 (by rfl) ⟨214011, by rfl⟩ : syracuseStep 2282789 = 428023) (by norm_num)
theorem B1520941 : Blo 1350994 1520941 := bbase (se 3 (by rfl) ⟨285176, by rfl⟩ : syracuseStep 1520941 = 570353) (by norm_num)
theorem B2028845 : Blo 1350994 2028845 := bbase (se 3 (by rfl) ⟨380408, by rfl⟩ : syracuseStep 2028845 = 760817) (by norm_num)
theorem B2028869 : Blo 1350994 2028869 := bbase (se 4 (by rfl) ⟨190206, by rfl⟩ : syracuseStep 2028869 = 380413) (by norm_num)
theorem B1520977 : Blo 1350994 1520977 := bbase (se 2 (by rfl) ⟨570366, by rfl⟩ : syracuseStep 1520977 = 1140733) (by norm_num)
theorem B2028893 : Blo 1350994 2028893 := bbase (se 3 (by rfl) ⟨380417, by rfl⟩ : syracuseStep 2028893 = 760835) (by norm_num)
theorem B3421541 : Blo 1350994 3421541 := bbase (se 4 (by rfl) ⟨320769, by rfl⟩ : syracuseStep 3421541 = 641539) (by norm_num)
theorem B4560245 : Blo 1350994 4560245 := bbase (se 5 (by rfl) ⟨213761, by rfl⟩ : syracuseStep 4560245 = 427523) (by norm_num)
theorem B1521013 : Blo 1350994 1521013 := bbase (se 5 (by rfl) ⟨71297, by rfl⟩ : syracuseStep 1521013 = 142595) (by norm_num)
theorem B2028917 : Blo 1350994 2028917 := bbase (se 5 (by rfl) ⟨95105, by rfl⟩ : syracuseStep 2028917 = 190211) (by norm_num)
theorem B3249533 : Blo 1350994 3249533 := bbase (se 3 (by rfl) ⟨609287, by rfl⟩ : syracuseStep 3249533 = 1218575) (by norm_num)
theorem B2028941 : Blo 1350994 2028941 := bbase (se 3 (by rfl) ⟨380426, by rfl⟩ : syracuseStep 2028941 = 760853) (by norm_num)
theorem B1521049 : Blo 1350994 1521049 := bbase (se 2 (by rfl) ⟨570393, by rfl⟩ : syracuseStep 1521049 = 1140787) (by norm_num)
theorem B2028965 : Blo 1350994 2028965 := bbase (se 4 (by rfl) ⟨190215, by rfl⟩ : syracuseStep 2028965 = 380431) (by norm_num)
theorem B2282917 : Blo 1350994 2282917 := bbase (se 4 (by rfl) ⟨214023, by rfl⟩ : syracuseStep 2282917 = 428047) (by norm_num)
theorem B1521085 : Blo 1350994 1521085 := bbase (se 3 (by rfl) ⟨285203, by rfl⟩ : syracuseStep 1521085 = 570407) (by norm_num)
theorem B2028989 : Blo 1350994 2028989 := bbase (se 3 (by rfl) ⟨380435, by rfl⟩ : syracuseStep 2028989 = 760871) (by norm_num)
theorem B1734097 : Blo 1350994 1734097 := bbase (se 2 (by rfl) ⟨650286, by rfl⟩ : syracuseStep 1734097 = 1300573) (by norm_num)
theorem B2029013 : Blo 1350994 2029013 := bbase (se 7 (by rfl) ⟨23777, by rfl⟩ : syracuseStep 2029013 = 47555) (by norm_num)
theorem B1521121 : Blo 1350994 1521121 := bbase (se 2 (by rfl) ⟨570420, by rfl⟩ : syracuseStep 1521121 = 1140841) (by norm_num)
theorem B2029037 : Blo 1350994 2029037 := bbase (se 3 (by rfl) ⟨380444, by rfl⟩ : syracuseStep 2029037 = 760889) (by norm_num)
theorem B2283005 : Blo 1350994 2283005 := bbase (se 3 (by rfl) ⟨428063, by rfl⟩ : syracuseStep 2283005 = 856127) (by norm_num)
theorem B4388357 : Blo 1350994 4388357 := bbase (se 4 (by rfl) ⟨411408, by rfl⟩ : syracuseStep 4388357 = 822817) (by norm_num)
theorem B1521157 : Blo 1350994 1521157 := bbase (se 4 (by rfl) ⟨142608, by rfl⟩ : syracuseStep 1521157 = 285217) (by norm_num)
theorem B6845957 : Blo 1350994 6845957 := bbase (se 4 (by rfl) ⟨641808, by rfl⟩ : syracuseStep 6845957 = 1283617) (by norm_num)
theorem B2029061 : Blo 1350994 2029061 := bbase (se 4 (by rfl) ⟨190224, by rfl⟩ : syracuseStep 2029061 = 380449) (by norm_num)
theorem B2029085 : Blo 1350994 2029085 := bbase (se 3 (by rfl) ⟨380453, by rfl⟩ : syracuseStep 2029085 = 760907) (by norm_num)
theorem B1521193 : Blo 1350994 1521193 := bbase (se 2 (by rfl) ⟨570447, by rfl⟩ : syracuseStep 1521193 = 1140895) (by norm_num)
theorem B2029109 : Blo 1350994 2029109 := bbase (se 5 (by rfl) ⟨95114, by rfl⟩ : syracuseStep 2029109 = 190229) (by norm_num)
theorem B1734205 : Blo 1350994 1734205 := bbase (se 3 (by rfl) ⟨325163, by rfl⟩ : syracuseStep 1734205 = 650327) (by norm_num)
theorem B1521229 : Blo 1350994 1521229 := bbase (se 3 (by rfl) ⟨285230, by rfl⟩ : syracuseStep 1521229 = 570461) (by norm_num)
theorem B2029133 : Blo 1350994 2029133 := bbase (se 3 (by rfl) ⟨380462, by rfl⟩ : syracuseStep 2029133 = 760925) (by norm_num)
theorem B2029157 : Blo 1350994 2029157 := bbase (se 4 (by rfl) ⟨190233, by rfl⟩ : syracuseStep 2029157 = 380467) (by norm_num)
theorem B1521265 : Blo 1350994 1521265 := bbase (se 2 (by rfl) ⟨570474, by rfl⟩ : syracuseStep 1521265 = 1140949) (by norm_num)
theorem B2029181 : Blo 1350994 2029181 := bbase (se 3 (by rfl) ⟨380471, by rfl⟩ : syracuseStep 2029181 = 760943) (by norm_num)
theorem B2283133 : Blo 1350994 2283133 := bbase (se 3 (by rfl) ⟨428087, by rfl⟩ : syracuseStep 2283133 = 856175) (by norm_num)
theorem B1521301 : Blo 1350994 1521301 := bbase (se 6 (by rfl) ⟨35655, by rfl⟩ : syracuseStep 1521301 = 71311) (by norm_num)
theorem B2029205 : Blo 1350994 2029205 := bbase (se 6 (by rfl) ⟨47559, by rfl⟩ : syracuseStep 2029205 = 95119) (by norm_num)
theorem B2029229 : Blo 1350994 2029229 := bbase (se 3 (by rfl) ⟨380480, by rfl⟩ : syracuseStep 2029229 = 760961) (by norm_num)
theorem B1521337 : Blo 1350994 1521337 := bbase (se 2 (by rfl) ⟨570501, by rfl⟩ : syracuseStep 1521337 = 1141003) (by norm_num)
theorem B3421885 : Blo 1350994 3421885 := bbase (se 3 (by rfl) ⟨641603, by rfl⟩ : syracuseStep 3421885 = 1283207) (by norm_num)
theorem B2029253 : Blo 1350994 2029253 := bbase (se 4 (by rfl) ⟨190242, by rfl⟩ : syracuseStep 2029253 = 380485) (by norm_num)
theorem B23099093 : Blo 1350994 23099093 := bbase (se 7 (by rfl) ⟨270692, by rfl⟩ : syracuseStep 23099093 = 541385) (by norm_num)
theorem B1521373 : Blo 1350994 1521373 := bbase (se 3 (by rfl) ⟨285257, by rfl⟩ : syracuseStep 1521373 = 570515) (by norm_num)
theorem B2029277 : Blo 1350994 2029277 := bbase (se 3 (by rfl) ⟨380489, by rfl⟩ : syracuseStep 2029277 = 760979) (by norm_num)
theorem B2889437 : Blo 1350994 2889437 := bbase (se 3 (by rfl) ⟨541769, by rfl⟩ : syracuseStep 2889437 = 1083539) (by norm_num)
theorem B3471077 : Blo 1350994 3471077 := bbase (se 4 (by rfl) ⟨325413, by rfl⟩ : syracuseStep 3471077 = 650827) (by norm_num)
theorem B1734385 : Blo 1350994 1734385 := bbase (se 2 (by rfl) ⟨650394, by rfl⟩ : syracuseStep 1734385 = 1300789) (by norm_num)
theorem B3847925 : Blo 1350994 3847925 := bbase (se 5 (by rfl) ⟨180371, by rfl⟩ : syracuseStep 3847925 = 360743) (by norm_num)
theorem B2029301 : Blo 1350994 2029301 := bbase (se 5 (by rfl) ⟨95123, by rfl⟩ : syracuseStep 2029301 = 190247) (by norm_num)
theorem B1521409 : Blo 1350994 1521409 := bbase (se 2 (by rfl) ⟨570528, by rfl⟩ : syracuseStep 1521409 = 1141057) (by norm_num)
theorem B3381005 : Blo 1350994 3381005 := bbase (se 3 (by rfl) ⟨633938, by rfl⟩ : syracuseStep 3381005 = 1267877) (by norm_num)
theorem B2029325 : Blo 1350994 2029325 := bbase (se 3 (by rfl) ⟨380498, by rfl⟩ : syracuseStep 2029325 = 760997) (by norm_num)
theorem B4560677 : Blo 1350994 4560677 := bbase (se 4 (by rfl) ⟨427563, by rfl⟩ : syracuseStep 4560677 = 855127) (by norm_num)
theorem B1521445 : Blo 1350994 1521445 := bbase (se 4 (by rfl) ⟨142635, by rfl⟩ : syracuseStep 1521445 = 285271) (by norm_num)
theorem B2029349 : Blo 1350994 2029349 := bbase (se 4 (by rfl) ⟨190251, by rfl⟩ : syracuseStep 2029349 = 380503) (by norm_num)
theorem B3421997 : Blo 1350994 3421997 := bbase (se 3 (by rfl) ⟨641624, by rfl⟩ : syracuseStep 3421997 = 1283249) (by norm_num)
theorem B2029373 : Blo 1350994 2029373 := bbase (se 3 (by rfl) ⟨380507, by rfl⟩ : syracuseStep 2029373 = 761015) (by norm_num)
theorem B4872005 : Blo 1350994 4872005 := bbase (se 4 (by rfl) ⟨456750, by rfl⟩ : syracuseStep 4872005 = 913501) (by norm_num)
theorem B1521481 : Blo 1350994 1521481 := bbase (se 2 (by rfl) ⟨570555, by rfl⟩ : syracuseStep 1521481 = 1141111) (by norm_num)
theorem B1709905 : Blo 1350994 1709905 := bbase (se 2 (by rfl) ⟨641214, by rfl⟩ : syracuseStep 1709905 = 1282429) (by norm_num)
theorem B2029397 : Blo 1350994 2029397 := bbase (se 9 (by rfl) ⟨5945, by rfl⟩ : syracuseStep 2029397 = 11891) (by norm_num)
theorem B1521517 : Blo 1350994 1521517 := bbase (se 3 (by rfl) ⟨285284, by rfl⟩ : syracuseStep 1521517 = 570569) (by norm_num)
theorem B2029421 : Blo 1350994 2029421 := bbase (se 3 (by rfl) ⟨380516, by rfl⟩ : syracuseStep 2029421 = 761033) (by norm_num)
theorem B2029445 : Blo 1350994 2029445 := bbase (se 4 (by rfl) ⟨190260, by rfl⟩ : syracuseStep 2029445 = 380521) (by norm_num)
theorem B1521553 : Blo 1350994 1521553 := bbase (se 2 (by rfl) ⟨570582, by rfl⟩ : syracuseStep 1521553 = 1141165) (by norm_num)
theorem B2029469 : Blo 1350994 2029469 := bbase (se 3 (by rfl) ⟨380525, by rfl⟩ : syracuseStep 2029469 = 761051) (by norm_num)
theorem B7034789 : Blo 1350994 7034789 := bbase (se 4 (by rfl) ⟨659511, by rfl⟩ : syracuseStep 7034789 = 1319023) (by norm_num)
theorem B1710001 : Blo 1350994 1710001 := bbase (se 2 (by rfl) ⟨641250, by rfl⟩ : syracuseStep 1710001 = 1282501) (by norm_num)
theorem B1521589 : Blo 1350994 1521589 := bbase (se 5 (by rfl) ⟨71324, by rfl⟩ : syracuseStep 1521589 = 142649) (by norm_num)
theorem B1521625 : Blo 1350994 1521625 := bbase (se 2 (by rfl) ⟨570609, by rfl⟩ : syracuseStep 1521625 = 1141219) (by norm_num)
theorem B3422189 : Blo 1350994 3422189 := bbase (se 3 (by rfl) ⟨641660, by rfl⟩ : syracuseStep 3422189 = 1283321) (by norm_num)
theorem B1521661 : Blo 1350994 1521661 := bbase (se 3 (by rfl) ⟨285311, by rfl⟩ : syracuseStep 1521661 = 570623) (by norm_num)
theorem B1521697 : Blo 1350994 1521697 := bbase (se 2 (by rfl) ⟨570636, by rfl⟩ : syracuseStep 1521697 = 1141273) (by norm_num)
theorem B1521733 : Blo 1350994 1521733 := bbase (se 4 (by rfl) ⟨142662, by rfl⟩ : syracuseStep 1521733 = 285325) (by norm_num)
theorem B17324117 : Blo 1350994 17324117 := bbase (se 8 (by rfl) ⟨101508, by rfl⟩ : syracuseStep 17324117 = 203017) (by norm_num)
theorem B1710173 : Blo 1350994 1710173 := bbase (se 3 (by rfl) ⟨320657, by rfl⟩ : syracuseStep 1710173 = 641315) (by norm_num)
theorem B1521769 : Blo 1350994 1521769 := bbase (se 2 (by rfl) ⟨570663, by rfl⟩ : syracuseStep 1521769 = 1141327) (by norm_num)
theorem B1521805 : Blo 1350994 1521805 := bbase (se 3 (by rfl) ⟨285338, by rfl⟩ : syracuseStep 1521805 = 570677) (by norm_num)
theorem B1710229 : Blo 1350994 1710229 := bbase (se 6 (by rfl) ⟨40083, by rfl⟩ : syracuseStep 1710229 = 80167) (by norm_num)
theorem B1521841 : Blo 1350994 1521841 := bbase (se 2 (by rfl) ⟨570690, by rfl⟩ : syracuseStep 1521841 = 1141381) (by norm_num)
theorem B4561109 : Blo 1350994 4561109 := bbase (se 7 (by rfl) ⟨53450, by rfl⟩ : syracuseStep 4561109 = 106901) (by norm_num)
theorem B1521877 : Blo 1350994 1521877 := bbase (se 7 (by rfl) ⟨17834, by rfl⟩ : syracuseStep 1521877 = 35669) (by norm_num)
theorem B1710325 : Blo 1350994 1710325 := bbase (se 5 (by rfl) ⟨80171, by rfl⟩ : syracuseStep 1710325 = 160343) (by norm_num)
theorem B1521913 : Blo 1350994 1521913 := bbase (se 2 (by rfl) ⟨570717, by rfl⟩ : syracuseStep 1521913 = 1141435) (by norm_num)
theorem B1521949 : Blo 1350994 1521949 := bbase (se 3 (by rfl) ⟨285365, by rfl⟩ : syracuseStep 1521949 = 570731) (by norm_num)
theorem B1521985 : Blo 1350994 1521985 := bbase (se 2 (by rfl) ⟨570744, by rfl⟩ : syracuseStep 1521985 = 1141489) (by norm_num)
theorem B3422533 : Blo 1350994 3422533 := bbase (se 4 (by rfl) ⟨320862, by rfl⟩ : syracuseStep 3422533 = 641725) (by norm_num)
theorem B1522021 : Blo 1350994 1522021 := bbase (se 4 (by rfl) ⟨142689, by rfl⟩ : syracuseStep 1522021 = 285379) (by norm_num)
theorem B1522057 : Blo 1350994 1522057 := bbase (se 2 (by rfl) ⟨570771, by rfl⟩ : syracuseStep 1522057 = 1141543) (by norm_num)
theorem B3848597 : Blo 1350994 3848597 := bbase (se 6 (by rfl) ⟨90201, by rfl⟩ : syracuseStep 3848597 = 180403) (by norm_num)
theorem B1710497 : Blo 1350994 1710497 := bbase (se 2 (by rfl) ⟨641436, by rfl⟩ : syracuseStep 1710497 = 1282873) (by norm_num)
theorem B1522093 : Blo 1350994 1522093 := bbase (se 3 (by rfl) ⟨285392, by rfl⟩ : syracuseStep 1522093 = 570785) (by norm_num)
theorem B3422645 : Blo 1350994 3422645 := bbase (se 5 (by rfl) ⟨160436, by rfl⟩ : syracuseStep 3422645 = 320873) (by norm_num)
theorem B1710553 : Blo 1350994 1710553 := bbase (se 2 (by rfl) ⟨641457, by rfl⟩ : syracuseStep 1710553 = 1282915) (by norm_num)
theorem B2193893 : Blo 1350994 2193893 := bbase (se 4 (by rfl) ⟨205677, by rfl⟩ : syracuseStep 2193893 = 411355) (by norm_num)
theorem B3381805 : Blo 1350994 3381805 := bbase (se 3 (by rfl) ⟨634088, by rfl⟩ : syracuseStep 3381805 = 1268177) (by norm_num)
theorem B1710649 : Blo 1350994 1710649 := bbase (se 2 (by rfl) ⟨641493, by rfl⟩ : syracuseStep 1710649 = 1282987) (by norm_num)
theorem B3422837 : Blo 1350994 3422837 := bbase (se 5 (by rfl) ⟨160445, by rfl⟩ : syracuseStep 3422837 = 320891) (by norm_num)
theorem B4561541 : Blo 1350994 4561541 := bbase (se 4 (by rfl) ⟨427644, by rfl⟩ : syracuseStep 4561541 = 855289) (by norm_num)
theorem B4332197 : Blo 1350994 4332197 := bbase (se 4 (by rfl) ⟨406143, by rfl⟩ : syracuseStep 4332197 = 812287) (by norm_num)
theorem B9747125 : Blo 1350994 9747125 := bbase (se 5 (by rfl) ⟨456896, by rfl⟩ : syracuseStep 9747125 = 913793) (by norm_num)
theorem B1923797 : Blo 1350994 1923797 := bbase (se 7 (by rfl) ⟨22544, by rfl⟩ : syracuseStep 1923797 = 45089) (by norm_num)
theorem B1710821 : Blo 1350994 1710821 := bbase (se 4 (by rfl) ⟨160389, by rfl⟩ : syracuseStep 1710821 = 320779) (by norm_num)
theorem B6847253 : Blo 1350994 6847253 := bbase (se 6 (by rfl) ⟨160482, by rfl⟩ : syracuseStep 6847253 = 320965) (by norm_num)
theorem B1710877 : Blo 1350994 1710877 := bbase (se 3 (by rfl) ⟨320789, by rfl⟩ : syracuseStep 1710877 = 641579) (by norm_num)
theorem B3849029 : Blo 1350994 3849029 := bbase (se 4 (by rfl) ⟨360846, by rfl⟩ : syracuseStep 3849029 = 721693) (by norm_num)
theorem B1710973 : Blo 1350994 1710973 := bbase (se 3 (by rfl) ⟨320807, by rfl⟩ : syracuseStep 1710973 = 641615) (by norm_num)
theorem B9255829 : Blo 1350994 9255829 := bbase (se 6 (by rfl) ⟨216933, by rfl⟩ : syracuseStep 9255829 = 433867) (by norm_num)
theorem B3423181 : Blo 1350994 3423181 := bbase (se 3 (by rfl) ⟨641846, by rfl⟩ : syracuseStep 3423181 = 1283693) (by norm_num)
theorem B1711145 : Blo 1350994 1711145 := bbase (se 2 (by rfl) ⟨641679, by rfl⟩ : syracuseStep 1711145 = 1283359) (by norm_num)
theorem B4561973 : Blo 1350994 4561973 := bbase (se 5 (by rfl) ⟨213842, by rfl⟩ : syracuseStep 4561973 = 427685) (by norm_num)
theorem B3423293 : Blo 1350994 3423293 := bbase (se 3 (by rfl) ⟨641867, by rfl⟩ : syracuseStep 3423293 = 1283735) (by norm_num)
theorem B1711201 : Blo 1350994 1711201 := bbase (se 2 (by rfl) ⟨641700, by rfl⟩ : syracuseStep 1711201 = 1283401) (by norm_num)
theorem B8666261 : Blo 1350994 8666261 := bbase (se 6 (by rfl) ⟨203115, by rfl⟩ : syracuseStep 8666261 = 406231) (by norm_num)
theorem B6839477 : Blo 1350994 6839477 := bbase (se 5 (by rfl) ⟨320600, by rfl⟩ : syracuseStep 6839477 = 641201) (by norm_num)
theorem B1711297 : Blo 1350994 1711297 := bbase (se 2 (by rfl) ⟨641736, by rfl⟩ : syracuseStep 1711297 = 1283473) (by norm_num)
theorem B3423485 : Blo 1350994 3423485 := bbase (se 3 (by rfl) ⟨641903, by rfl⟩ : syracuseStep 3423485 = 1283807) (by norm_num)
theorem B5135669 : Blo 1350994 5135669 := bbase (se 5 (by rfl) ⟨240734, by rfl⟩ : syracuseStep 5135669 = 481469) (by norm_num)
theorem B1711469 : Blo 1350994 1711469 := bbase (se 3 (by rfl) ⟨320900, by rfl⟩ : syracuseStep 1711469 = 641801) (by norm_num)
theorem B1711525 : Blo 1350994 1711525 := bbase (se 4 (by rfl) ⟨160455, by rfl⟩ : syracuseStep 1711525 = 320911) (by norm_num)
theorem B4562405 : Blo 1350994 4562405 := bbase (se 4 (by rfl) ⟨427725, by rfl⟩ : syracuseStep 4562405 = 855451) (by norm_num)
theorem B1711621 : Blo 1350994 1711621 := bbase (se 4 (by rfl) ⟨160464, by rfl⟩ : syracuseStep 1711621 = 320929) (by norm_num)
theorem B13876757 : Blo 1350994 13876757 := bbase (se 6 (by rfl) ⟨325236, by rfl⟩ : syracuseStep 13876757 = 650473) (by norm_num)
theorem B3849781 : Blo 1350994 3849781 := bbase (se 5 (by rfl) ⟨180458, by rfl⟩ : syracuseStep 3849781 = 360917) (by norm_num)
theorem B3423829 : Blo 1350994 3423829 := bbase (se 8 (by rfl) ⟨20061, by rfl⟩ : syracuseStep 3423829 = 40123) (by norm_num)
theorem B5135957 : Blo 1350994 5135957 := bbase (se 8 (by rfl) ⟨30093, by rfl⟩ : syracuseStep 5135957 = 60187) (by norm_num)
theorem B1711793 : Blo 1350994 1711793 := bbase (se 2 (by rfl) ⟨641922, by rfl⟩ : syracuseStep 1711793 = 1283845) (by norm_num)
theorem B3423941 : Blo 1350994 3423941 := bbase (se 4 (by rfl) ⟨320994, by rfl⟩ : syracuseStep 3423941 = 641989) (by norm_num)
theorem B1711849 : Blo 1350994 1711849 := bbase (se 2 (by rfl) ⟨641943, by rfl⟩ : syracuseStep 1711849 = 1283887) (by norm_num)
theorem B1711945 : Blo 1350994 1711945 := bbase (se 2 (by rfl) ⟨641979, by rfl⟩ : syracuseStep 1711945 = 1283959) (by norm_num)
theorem B3424133 : Blo 1350994 3424133 := bbase (se 4 (by rfl) ⟨321012, by rfl⟩ : syracuseStep 3424133 = 642025) (by norm_num)
theorem B4562837 : Blo 1350994 4562837 := bbase (se 6 (by rfl) ⟨106941, by rfl⟩ : syracuseStep 4562837 = 213883) (by norm_num)
theorem B15400853 : Blo 1350994 15400853 := bbase (se 6 (by rfl) ⟨360957, by rfl⟩ : syracuseStep 15400853 = 721915) (by norm_num)
theorem B8339381 : Blo 1350994 8339381 := bbase (se 5 (by rfl) ⟨390908, by rfl⟩ : syracuseStep 8339381 = 781817) (by norm_num)
theorem B14622677 : Blo 1350994 14622677 := bbase (se 7 (by rfl) ⟨171359, by rfl⟩ : syracuseStep 14622677 = 342719) (by norm_num)
theorem B1712117 : Blo 1350994 1712117 := bbase (se 5 (by rfl) ⟨80255, by rfl⟩ : syracuseStep 1712117 = 160511) (by norm_num)
theorem B1351683 : Blo 1350994 1351683 := bstep (se 1 (by rfl) ⟨1013762, by rfl⟩ : syracuseStep 1351683 = 2027525) B2027525
theorem B1351699 : Blo 1350994 1351699 := bstep (se 1 (by rfl) ⟨1013774, by rfl⟩ : syracuseStep 1351699 = 2027549) B2027549
theorem B1351715 : Blo 1350994 1351715 := bstep (se 1 (by rfl) ⟨1013786, by rfl⟩ : syracuseStep 1351715 = 2027573) B2027573
theorem B1351731 : Blo 1350994 1351731 := bstep (se 1 (by rfl) ⟨1013798, by rfl⟩ : syracuseStep 1351731 = 2027597) B2027597
theorem B1351747 : Blo 1350994 1351747 := bstep (se 1 (by rfl) ⟨1013810, by rfl⟩ : syracuseStep 1351747 = 2027621) B2027621
theorem B1351763 : Blo 1350994 1351763 := bstep (se 1 (by rfl) ⟨1013822, by rfl⟩ : syracuseStep 1351763 = 2027645) B2027645
theorem B1351779 : Blo 1350994 1351779 := bstep (se 1 (by rfl) ⟨1013834, by rfl⟩ : syracuseStep 1351779 = 2027669) B2027669
theorem B4563053 : Blo 1350994 4563053 := bstep (se 3 (by rfl) ⟨855572, by rfl⟩ : syracuseStep 4563053 = 1711145) B1711145
theorem B24658033 : Blo 1350994 24658033 := bstep (se 2 (by rfl) ⟨9246762, by rfl⟩ : syracuseStep 24658033 = 18493525) B18493525
theorem B1351795 : Blo 1350994 1351795 := bstep (se 1 (by rfl) ⟨1013846, by rfl⟩ : syracuseStep 1351795 = 2027693) B2027693
theorem B1351811 : Blo 1350994 1351811 := bstep (se 1 (by rfl) ⟨1013858, by rfl⟩ : syracuseStep 1351811 = 2027717) B2027717
theorem B9748621 : Blo 1350994 9748621 := bstep (se 3 (by rfl) ⟨1827866, by rfl⟩ : syracuseStep 9748621 = 3655733) B3655733
theorem B1351827 : Blo 1350994 1351827 := bstep (se 1 (by rfl) ⟨1013870, by rfl⟩ : syracuseStep 1351827 = 2027741) B2027741
theorem B1351843 : Blo 1350994 1351843 := bstep (se 1 (by rfl) ⟨1013882, by rfl⟩ : syracuseStep 1351843 = 2027765) B2027765
theorem B4563107 : Blo 1350994 4563107 := bstep (se 1 (by rfl) ⟨3422330, by rfl⟩ : syracuseStep 4563107 = 6844661) B6844661
theorem B1351859 : Blo 1350994 1351859 := bstep (se 1 (by rfl) ⟨1013894, by rfl⟩ : syracuseStep 1351859 = 2027789) B2027789
theorem B1351875 : Blo 1350994 1351875 := bstep (se 1 (by rfl) ⟨1013906, by rfl⟩ : syracuseStep 1351875 = 2027813) B2027813
theorem B1351891 : Blo 1350994 1351891 := bstep (se 1 (by rfl) ⟨1013918, by rfl⟩ : syracuseStep 1351891 = 2027837) B2027837
theorem B1351907 : Blo 1350994 1351907 := bstep (se 1 (by rfl) ⟨1013930, by rfl⟩ : syracuseStep 1351907 = 2027861) B2027861
theorem B13000931 : Blo 1350994 13000931 := bstep (se 1 (by rfl) ⟨9750698, by rfl⟩ : syracuseStep 13000931 = 19501397) B19501397
theorem B1351923 : Blo 1350994 1351923 := bstep (se 1 (by rfl) ⟨1013942, by rfl⟩ : syracuseStep 1351923 = 2027885) B2027885
theorem B1351939 : Blo 1350994 1351939 := bstep (se 1 (by rfl) ⟨1013954, by rfl⟩ : syracuseStep 1351939 = 2027909) B2027909
theorem B4333837 : Blo 1350994 4333837 := bstep (se 3 (by rfl) ⟨812594, by rfl⟩ : syracuseStep 4333837 = 1625189) B1625189
theorem B1351955 : Blo 1350994 1351955 := bstep (se 1 (by rfl) ⟨1013966, by rfl⟩ : syracuseStep 1351955 = 2027933) B2027933
theorem B6840611 : Blo 1350994 6840611 := bstep (se 1 (by rfl) ⟨5130458, by rfl⟩ : syracuseStep 6840611 = 10260917) B10260917
theorem B1351971 : Blo 1350994 1351971 := bstep (se 1 (by rfl) ⟨1013978, by rfl⟩ : syracuseStep 1351971 = 2027957) B2027957
theorem B1351987 : Blo 1350994 1351987 := bstep (se 1 (by rfl) ⟨1013990, by rfl⟩ : syracuseStep 1351987 = 2027981) B2027981
theorem B1483075 : Blo 1350994 1483075 := bstep (se 1 (by rfl) ⟨1112306, by rfl⟩ : syracuseStep 1483075 = 2224613) B2224613
theorem B1352003 : Blo 1350994 1352003 := bstep (se 1 (by rfl) ⟨1014002, by rfl⟩ : syracuseStep 1352003 = 2028005) B2028005
theorem B4874573 : Blo 1350994 4874573 := bstep (se 3 (by rfl) ⟨913982, by rfl⟩ : syracuseStep 4874573 = 1827965) B1827965
theorem B1352019 : Blo 1350994 1352019 := bstep (se 1 (by rfl) ⟨1014014, by rfl⟩ : syracuseStep 1352019 = 2028029) B2028029
theorem B1352035 : Blo 1350994 1352035 := bstep (se 1 (by rfl) ⟨1014026, by rfl⟩ : syracuseStep 1352035 = 2028053) B2028053
theorem B1352051 : Blo 1350994 1352051 := bstep (se 1 (by rfl) ⟨1014038, by rfl⟩ : syracuseStep 1352051 = 2028077) B2028077
theorem B1352067 : Blo 1350994 1352067 := bstep (se 1 (by rfl) ⟨1014050, by rfl⟩ : syracuseStep 1352067 = 2028101) B2028101
theorem B1352083 : Blo 1350994 1352083 := bstep (se 1 (by rfl) ⟨1014062, by rfl⟩ : syracuseStep 1352083 = 2028125) B2028125
theorem B1352099 : Blo 1350994 1352099 := bstep (se 1 (by rfl) ⟨1014074, by rfl⟩ : syracuseStep 1352099 = 2028149) B2028149
theorem B3850669 : Blo 1350994 3850669 := bstep (se 3 (by rfl) ⟨722000, by rfl⟩ : syracuseStep 3850669 = 1444001) B1444001
theorem B4563377 : Blo 1350994 4563377 := bstep (se 2 (by rfl) ⟨1711266, by rfl⟩ : syracuseStep 4563377 = 3422533) B3422533
theorem B1352115 : Blo 1350994 1352115 := bstep (se 1 (by rfl) ⟨1014086, by rfl⟩ : syracuseStep 1352115 = 2028173) B2028173
theorem B1352131 : Blo 1350994 1352131 := bstep (se 1 (by rfl) ⟨1014098, by rfl⟩ : syracuseStep 1352131 = 2028197) B2028197
theorem B1352147 : Blo 1350994 1352147 := bstep (se 1 (by rfl) ⟨1014110, by rfl⟩ : syracuseStep 1352147 = 2028221) B2028221
theorem B1352163 : Blo 1350994 1352163 := bstep (se 1 (by rfl) ⟨1014122, by rfl⟩ : syracuseStep 1352163 = 2028245) B2028245
theorem B1352179 : Blo 1350994 1352179 := bstep (se 1 (by rfl) ⟨1014134, by rfl⟩ : syracuseStep 1352179 = 2028269) B2028269
theorem B1352195 : Blo 1350994 1352195 := bstep (se 1 (by rfl) ⟨1014146, by rfl⟩ : syracuseStep 1352195 = 2028293) B2028293
theorem B1352211 : Blo 1350994 1352211 := bstep (se 1 (by rfl) ⟨1014158, by rfl⟩ : syracuseStep 1352211 = 2028317) B2028317
theorem B1352227 : Blo 1350994 1352227 := bstep (se 1 (by rfl) ⟨1014170, by rfl⟩ : syracuseStep 1352227 = 2028341) B2028341
theorem B1352243 : Blo 1350994 1352243 := bstep (se 1 (by rfl) ⟨1014182, by rfl⟩ : syracuseStep 1352243 = 2028365) B2028365
theorem B1352259 : Blo 1350994 1352259 := bstep (se 1 (by rfl) ⟨1014194, by rfl⟩ : syracuseStep 1352259 = 2028389) B2028389
theorem B1925699 : Blo 1350994 1925699 := bstep (se 1 (by rfl) ⟨1444274, by rfl⟩ : syracuseStep 1925699 = 2888549) B2888549
theorem B1352275 : Blo 1350994 1352275 := bstep (se 1 (by rfl) ⟨1014206, by rfl⟩ : syracuseStep 1352275 = 2028413) B2028413
theorem B1352291 : Blo 1350994 1352291 := bstep (se 1 (by rfl) ⟨1014218, by rfl⟩ : syracuseStep 1352291 = 2028437) B2028437
theorem B3039857 : Blo 1350994 3039857 := bstep (se 2 (by rfl) ⟨1139946, by rfl⟩ : syracuseStep 3039857 = 2279893) B2279893
theorem B14615153 : Blo 1350994 14615153 := bstep (se 2 (by rfl) ⟨5480682, by rfl⟩ : syracuseStep 14615153 = 10961365) B10961365
theorem B1352307 : Blo 1350994 1352307 := bstep (se 1 (by rfl) ⟨1014230, by rfl⟩ : syracuseStep 1352307 = 2028461) B2028461
theorem B3039875 : Blo 1350994 3039875 := bstep (se 1 (by rfl) ⟨2279906, by rfl⟩ : syracuseStep 3039875 = 4559813) B4559813
theorem B1352323 : Blo 1350994 1352323 := bstep (se 1 (by rfl) ⟨1014242, by rfl⟩ : syracuseStep 1352323 = 2028485) B2028485
theorem B3850897 : Blo 1350994 3850897 := bstep (se 2 (by rfl) ⟨1444086, by rfl⟩ : syracuseStep 3850897 = 2888173) B2888173
theorem B1352339 : Blo 1350994 1352339 := bstep (se 1 (by rfl) ⟨1014254, by rfl⟩ : syracuseStep 1352339 = 2028509) B2028509
theorem B1352355 : Blo 1350994 1352355 := bstep (se 1 (by rfl) ⟨1014266, by rfl⟩ : syracuseStep 1352355 = 2028533) B2028533
theorem B1352371 : Blo 1350994 1352371 := bstep (se 1 (by rfl) ⟨1014278, by rfl⟩ : syracuseStep 1352371 = 2028557) B2028557
theorem B1352387 : Blo 1350994 1352387 := bstep (se 1 (by rfl) ⟨1014290, by rfl⟩ : syracuseStep 1352387 = 2028581) B2028581
theorem B4334285 : Blo 1350994 4334285 := bstep (se 3 (by rfl) ⟨812678, by rfl⟩ : syracuseStep 4334285 = 1625357) B1625357
theorem B1352403 : Blo 1350994 1352403 := bstep (se 1 (by rfl) ⟨1014302, by rfl⟩ : syracuseStep 1352403 = 2028605) B2028605
theorem B1352419 : Blo 1350994 1352419 := bstep (se 1 (by rfl) ⟨1014314, by rfl⟩ : syracuseStep 1352419 = 2028629) B2028629
theorem B1352435 : Blo 1350994 1352435 := bstep (se 1 (by rfl) ⟨1014326, by rfl⟩ : syracuseStep 1352435 = 2028653) B2028653
theorem B1352451 : Blo 1350994 1352451 := bstep (se 1 (by rfl) ⟨1014338, by rfl⟩ : syracuseStep 1352451 = 2028677) B2028677
theorem B1352467 : Blo 1350994 1352467 := bstep (se 1 (by rfl) ⟨1014350, by rfl⟩ : syracuseStep 1352467 = 2028701) B2028701
theorem B1352483 : Blo 1350994 1352483 := bstep (se 1 (by rfl) ⟨1014362, by rfl⟩ : syracuseStep 1352483 = 2028725) B2028725
theorem B3851057 : Blo 1350994 3851057 := bstep (se 2 (by rfl) ⟨1444146, by rfl⟩ : syracuseStep 3851057 = 2888293) B2888293
theorem B1352499 : Blo 1350994 1352499 := bstep (se 1 (by rfl) ⟨1014374, by rfl⟩ : syracuseStep 1352499 = 2028749) B2028749
theorem B1352515 : Blo 1350994 1352515 := bstep (se 1 (by rfl) ⟨1014386, by rfl⟩ : syracuseStep 1352515 = 2028773) B2028773
theorem B7701317 : Blo 1350994 7701317 := bstep (se 4 (by rfl) ⟨721998, by rfl⟩ : syracuseStep 7701317 = 1443997) B1443997
theorem B3900241 : Blo 1350994 3900241 := bstep (se 2 (by rfl) ⟨1462590, by rfl⟩ : syracuseStep 3900241 = 2925181) B2925181
theorem B1352531 : Blo 1350994 1352531 := bstep (se 1 (by rfl) ⟨1014398, by rfl⟩ : syracuseStep 1352531 = 2028797) B2028797
theorem B1352547 : Blo 1350994 1352547 := bstep (se 1 (by rfl) ⟨1014410, by rfl⟩ : syracuseStep 1352547 = 2028821) B2028821
theorem B1352563 : Blo 1350994 1352563 := bstep (se 1 (by rfl) ⟨1014422, by rfl⟩ : syracuseStep 1352563 = 2028845) B2028845
theorem B1352579 : Blo 1350994 1352579 := bstep (se 1 (by rfl) ⟨1014434, by rfl⟩ : syracuseStep 1352579 = 2028869) B2028869
theorem B5202829 : Blo 1350994 5202829 := bstep (se 3 (by rfl) ⟨975530, by rfl⟩ : syracuseStep 5202829 = 1951061) B1951061
theorem B3040145 : Blo 1350994 3040145 := bstep (se 2 (by rfl) ⟨1140054, by rfl⟩ : syracuseStep 3040145 = 2280109) B2280109
theorem B1352595 : Blo 1350994 1352595 := bstep (se 1 (by rfl) ⟨1014446, by rfl⟩ : syracuseStep 1352595 = 2028893) B2028893
theorem B2057105 : Blo 1350994 2057105 := bstep (se 2 (by rfl) ⟨771414, by rfl⟩ : syracuseStep 2057105 = 1542829) B1542829
theorem B3040163 : Blo 1350994 3040163 := bstep (se 1 (by rfl) ⟨2280122, by rfl⟩ : syracuseStep 3040163 = 4560245) B4560245
theorem B3851171 : Blo 1350994 3851171 := bstep (se 1 (by rfl) ⟨2888378, by rfl⟩ : syracuseStep 3851171 = 5776757) B5776757
theorem B1352611 : Blo 1350994 1352611 := bstep (se 1 (by rfl) ⟨1014458, by rfl⟩ : syracuseStep 1352611 = 2028917) B2028917
theorem B8217521 : Blo 1350994 8217521 := bstep (se 2 (by rfl) ⟨3081570, by rfl⟩ : syracuseStep 8217521 = 6163141) B6163141
theorem B1352627 : Blo 1350994 1352627 := bstep (se 1 (by rfl) ⟨1014470, by rfl⟩ : syracuseStep 1352627 = 2028941) B2028941
theorem B1352643 : Blo 1350994 1352643 := bstep (se 1 (by rfl) ⟨1014482, by rfl⟩ : syracuseStep 1352643 = 2028965) B2028965
theorem B4563917 : Blo 1350994 4563917 := bstep (se 3 (by rfl) ⟨855734, by rfl⟩ : syracuseStep 4563917 = 1711469) B1711469
theorem B1352659 : Blo 1350994 1352659 := bstep (se 1 (by rfl) ⟨1014494, by rfl⟩ : syracuseStep 1352659 = 2028989) B2028989
theorem B1352675 : Blo 1350994 1352675 := bstep (se 1 (by rfl) ⟨1014506, by rfl⟩ : syracuseStep 1352675 = 2029013) B2029013
theorem B6849521 : Blo 1350994 6849521 := bstep (se 2 (by rfl) ⟨2568570, by rfl⟩ : syracuseStep 6849521 = 5137141) B5137141
theorem B1352691 : Blo 1350994 1352691 := bstep (se 1 (by rfl) ⟨1014518, by rfl⟩ : syracuseStep 1352691 = 2029037) B2029037
theorem B2925571 : Blo 1350994 2925571 := bstep (se 1 (by rfl) ⟨2194178, by rfl⟩ : syracuseStep 2925571 = 4388357) B4388357
theorem B4563971 : Blo 1350994 4563971 := bstep (se 1 (by rfl) ⟨3422978, by rfl⟩ : syracuseStep 4563971 = 6845957) B6845957
theorem B1352707 : Blo 1350994 1352707 := bstep (se 1 (by rfl) ⟨1014530, by rfl⟩ : syracuseStep 1352707 = 2029061) B2029061
theorem B1352723 : Blo 1350994 1352723 := bstep (se 1 (by rfl) ⟨1014542, by rfl⟩ : syracuseStep 1352723 = 2029085) B2029085
theorem B1352739 : Blo 1350994 1352739 := bstep (se 1 (by rfl) ⟨1014554, by rfl⟩ : syracuseStep 1352739 = 2029109) B2029109
theorem B1352755 : Blo 1350994 1352755 := bstep (se 1 (by rfl) ⟨1014566, by rfl⟩ : syracuseStep 1352755 = 2029133) B2029133
theorem B1827905 : Blo 1350994 1827905 := bstep (se 2 (by rfl) ⟨685464, by rfl⟩ : syracuseStep 1827905 = 1370929) B1370929
theorem B1352771 : Blo 1350994 1352771 := bstep (se 1 (by rfl) ⟨1014578, by rfl⟩ : syracuseStep 1352771 = 2029157) B2029157
theorem B6841421 : Blo 1350994 6841421 := bstep (se 3 (by rfl) ⟨1282766, by rfl⟩ : syracuseStep 6841421 = 2565533) B2565533
theorem B1352787 : Blo 1350994 1352787 := bstep (se 1 (by rfl) ⟨1014590, by rfl⟩ : syracuseStep 1352787 = 2029181) B2029181
theorem B1352803 : Blo 1350994 1352803 := bstep (se 1 (by rfl) ⟨1014602, by rfl⟩ : syracuseStep 1352803 = 2029205) B2029205
theorem B1352819 : Blo 1350994 1352819 := bstep (se 1 (by rfl) ⟨1014614, by rfl⟩ : syracuseStep 1352819 = 2029229) B2029229
theorem B1352835 : Blo 1350994 1352835 := bstep (se 1 (by rfl) ⟨1014626, by rfl⟩ : syracuseStep 1352835 = 2029253) B2029253
theorem B1352851 : Blo 1350994 1352851 := bstep (se 1 (by rfl) ⟨1014638, by rfl⟩ : syracuseStep 1352851 = 2029277) B2029277
theorem B2565283 : Blo 1350994 2565283 := bstep (se 1 (by rfl) ⟨1923962, by rfl⟩ : syracuseStep 2565283 = 3847925) B3847925
theorem B1352867 : Blo 1350994 1352867 := bstep (se 1 (by rfl) ⟨1014650, by rfl⟩ : syracuseStep 1352867 = 2029301) B2029301
theorem B3040433 : Blo 1350994 3040433 := bstep (se 2 (by rfl) ⟨1140162, by rfl⟩ : syracuseStep 3040433 = 2280325) B2280325
theorem B2254003 : Blo 1350994 2254003 := bstep (se 1 (by rfl) ⟨1690502, by rfl⟩ : syracuseStep 2254003 = 3381005) B3381005
theorem B1352883 : Blo 1350994 1352883 := bstep (se 1 (by rfl) ⟨1014662, by rfl⟩ : syracuseStep 1352883 = 2029325) B2029325
theorem B1926337 : Blo 1350994 1926337 := bstep (se 2 (by rfl) ⟨722376, by rfl⟩ : syracuseStep 1926337 = 1444753) B1444753
theorem B3040451 : Blo 1350994 3040451 := bstep (se 1 (by rfl) ⟨2280338, by rfl⟩ : syracuseStep 3040451 = 4560677) B4560677
theorem B1352899 : Blo 1350994 1352899 := bstep (se 1 (by rfl) ⟨1014674, by rfl⟩ : syracuseStep 1352899 = 2029349) B2029349
theorem B1352915 : Blo 1350994 1352915 := bstep (se 1 (by rfl) ⟨1014686, by rfl⟩ : syracuseStep 1352915 = 2029373) B2029373
theorem B1352931 : Blo 1350994 1352931 := bstep (se 1 (by rfl) ⟨1014698, by rfl⟩ : syracuseStep 1352931 = 2029397) B2029397
theorem B1352947 : Blo 1350994 1352947 := bstep (se 1 (by rfl) ⟨1014710, by rfl⟩ : syracuseStep 1352947 = 2029421) B2029421
theorem B1352963 : Blo 1350994 1352963 := bstep (se 1 (by rfl) ⟨1014722, by rfl⟩ : syracuseStep 1352963 = 2029445) B2029445
theorem B4564241 : Blo 1350994 4564241 := bstep (se 2 (by rfl) ⟨1711590, by rfl⟩ : syracuseStep 4564241 = 3423181) B3423181
theorem B1352979 : Blo 1350994 1352979 := bstep (se 1 (by rfl) ⟨1014734, by rfl⟩ : syracuseStep 1352979 = 2029469) B2029469
theorem B3040721 : Blo 1350994 3040721 := bstep (se 2 (by rfl) ⟨1140270, by rfl⟩ : syracuseStep 3040721 = 2280541) B2280541
theorem B3040739 : Blo 1350994 3040739 := bstep (se 1 (by rfl) ⟨2280554, by rfl⟩ : syracuseStep 3040739 = 4561109) B4561109
theorem B2164259 : Blo 1350994 2164259 := bstep (se 1 (by rfl) ⟨1623194, by rfl⟩ : syracuseStep 2164259 = 3246389) B3246389
theorem B8668721 : Blo 1350994 8668721 := bstep (se 2 (by rfl) ⟨3250770, by rfl⟩ : syracuseStep 8668721 = 6501541) B6501541
theorem B2565731 : Blo 1350994 2565731 := bstep (se 1 (by rfl) ⟨1924298, by rfl⟩ : syracuseStep 2565731 = 3848597) B3848597
theorem B6588067 : Blo 1350994 6588067 := bstep (se 1 (by rfl) ⟨4941050, by rfl⟩ : syracuseStep 6588067 = 9882101) B9882101
theorem B3041009 : Blo 1350994 3041009 := bstep (se 2 (by rfl) ⟨1140378, by rfl⟩ : syracuseStep 3041009 = 2280757) B2280757
theorem B3041027 : Blo 1350994 3041027 := bstep (se 1 (by rfl) ⟨2280770, by rfl⟩ : syracuseStep 3041027 = 4561541) B4561541
theorem B1443587 : Blo 1350994 1443587 := bstep (se 1 (by rfl) ⟨1082690, by rfl⟩ : syracuseStep 1443587 = 2165381) B2165381
theorem B7309091 : Blo 1350994 7309091 := bstep (se 1 (by rfl) ⟨5481818, by rfl⟩ : syracuseStep 7309091 = 10963637) B10963637
theorem B6498083 : Blo 1350994 6498083 := bstep (se 1 (by rfl) ⟨4873562, by rfl⟩ : syracuseStep 6498083 = 9747125) B9747125
theorem B4564781 : Blo 1350994 4564781 := bstep (se 3 (by rfl) ⟨855896, by rfl⟩ : syracuseStep 4564781 = 1711793) B1711793
theorem B4564835 : Blo 1350994 4564835 := bstep (se 1 (by rfl) ⟨3423626, by rfl⟩ : syracuseStep 4564835 = 6847253) B6847253
theorem B4876145 : Blo 1350994 4876145 := bstep (se 2 (by rfl) ⟨1828554, by rfl⟩ : syracuseStep 4876145 = 3657109) B3657109
theorem B2566019 : Blo 1350994 2566019 := bstep (se 1 (by rfl) ⟨1924514, by rfl⟩ : syracuseStep 2566019 = 3849029) B3849029
theorem B5130125 : Blo 1350994 5130125 := bstep (se 3 (by rfl) ⟨961898, by rfl⟩ : syracuseStep 5130125 = 1923797) B1923797
theorem B3852173 : Blo 1350994 3852173 := bstep (se 3 (by rfl) ⟨722282, by rfl⟩ : syracuseStep 3852173 = 1444565) B1444565
theorem B2312129 : Blo 1350994 2312129 := bstep (se 2 (by rfl) ⟨867048, by rfl⟩ : syracuseStep 2312129 = 1734097) B1734097
theorem B3041297 : Blo 1350994 3041297 := bstep (se 2 (by rfl) ⟨1140486, by rfl⟩ : syracuseStep 3041297 = 2280973) B2280973
theorem B3041315 : Blo 1350994 3041315 := bstep (se 1 (by rfl) ⟨2280986, by rfl⟩ : syracuseStep 3041315 = 4561973) B4561973
theorem B3852355 : Blo 1350994 3852355 := bstep (se 1 (by rfl) ⟨2889266, by rfl⟩ : syracuseStep 3852355 = 5778533) B5778533
theorem B2312273 : Blo 1350994 2312273 := bstep (se 2 (by rfl) ⟨867102, by rfl⟩ : syracuseStep 2312273 = 1734205) B1734205
theorem B13174883 : Blo 1350994 13174883 := bstep (se 1 (by rfl) ⟨9881162, by rfl⟩ : syracuseStep 13174883 = 19762325) B19762325
theorem B5777507 : Blo 1350994 5777507 := bstep (se 1 (by rfl) ⟨4333130, by rfl⟩ : syracuseStep 5777507 = 8666261) B8666261
theorem B4565105 : Blo 1350994 4565105 := bstep (se 2 (by rfl) ⟨1711914, by rfl⟩ : syracuseStep 4565105 = 3423829) B3423829
theorem B3852515 : Blo 1350994 3852515 := bstep (se 1 (by rfl) ⟨2889386, by rfl⟩ : syracuseStep 3852515 = 5778773) B5778773
theorem B3041585 : Blo 1350994 3041585 := bstep (se 2 (by rfl) ⟨1140594, by rfl⟩ : syracuseStep 3041585 = 2281189) B2281189
theorem B2312513 : Blo 1350994 2312513 := bstep (se 2 (by rfl) ⟨867192, by rfl⟩ : syracuseStep 2312513 = 1734385) B1734385
theorem B3041603 : Blo 1350994 3041603 := bstep (se 1 (by rfl) ⟨2281202, by rfl⟩ : syracuseStep 3041603 = 4562405) B4562405
theorem B2885969 : Blo 1350994 2885969 := bstep (se 2 (by rfl) ⟨1082238, by rfl⟩ : syracuseStep 2885969 = 2164477) B2164477
theorem B9251171 : Blo 1350994 9251171 := bstep (se 1 (by rfl) ⟨6938378, by rfl⟩ : syracuseStep 9251171 = 13876757) B13876757
theorem B2165105 : Blo 1350994 2165105 := bstep (se 2 (by rfl) ⟨811914, by rfl⟩ : syracuseStep 2165105 = 1623829) B1623829
theorem B2279873 : Blo 1350994 2279873 := bstep (se 2 (by rfl) ⟨854952, by rfl⟩ : syracuseStep 2279873 = 1709905) B1709905
theorem B16452067 : Blo 1350994 16452067 := bstep (se 1 (by rfl) ⟨12339050, by rfl⟩ : syracuseStep 16452067 = 24678101) B24678101
theorem B2165233 : Blo 1350994 2165233 := bstep (se 2 (by rfl) ⟨811962, by rfl⟩ : syracuseStep 2165233 = 1623925) B1623925
theorem B1444339 : Blo 1350994 1444339 := bstep (se 1 (by rfl) ⟨1083254, by rfl⟩ : syracuseStep 1444339 = 2166509) B2166509
theorem B2165297 : Blo 1350994 2165297 := bstep (se 2 (by rfl) ⟨811986, by rfl⟩ : syracuseStep 2165297 = 1623973) B1623973
theorem B2280001 : Blo 1350994 2280001 := bstep (se 2 (by rfl) ⟨855000, by rfl⟩ : syracuseStep 2280001 = 1710001) B1710001
theorem B15608389 : Blo 1350994 15608389 := bstep (se 4 (by rfl) ⟨1463286, by rfl⟩ : syracuseStep 15608389 = 2926573) B2926573
theorem B3041873 : Blo 1350994 3041873 := bstep (se 2 (by rfl) ⟨1140702, by rfl⟩ : syracuseStep 3041873 = 2281405) B2281405
theorem B2280035 : Blo 1350994 2280035 := bstep (se 1 (by rfl) ⟨1710026, by rfl⟩ : syracuseStep 2280035 = 3420053) B3420053
theorem B3041891 : Blo 1350994 3041891 := bstep (se 1 (by rfl) ⟨2281418, by rfl⟩ : syracuseStep 3041891 = 4562837) B4562837
theorem B10267235 : Blo 1350994 10267235 := bstep (se 1 (by rfl) ⟨7700426, by rfl⟩ : syracuseStep 10267235 = 15400853) B15400853
theorem B4565645 : Blo 1350994 4565645 := bstep (se 3 (by rfl) ⟨856058, by rfl⟩ : syracuseStep 4565645 = 1712117) B1712117
theorem B4565699 : Blo 1350994 4565699 := bstep (se 1 (by rfl) ⟨3424274, by rfl⟩ : syracuseStep 4565699 = 6848549) B6848549
theorem B5483213 : Blo 1350994 5483213 := bstep (se 3 (by rfl) ⟨1028102, by rfl⟩ : syracuseStep 5483213 = 2056205) B2056205
theorem B2280163 : Blo 1350994 2280163 := bstep (se 1 (by rfl) ⟨1710122, by rfl⟩ : syracuseStep 2280163 = 3420245) B3420245
theorem B2738947 : Blo 1350994 2738947 := bstep (se 1 (by rfl) ⟨2054210, by rfl⟩ : syracuseStep 2738947 = 4108421) B4108421
theorem B2566961 : Blo 1350994 2566961 := bstep (se 2 (by rfl) ⟨962610, by rfl⟩ : syracuseStep 2566961 = 1925221) B1925221
theorem B2280305 : Blo 1350994 2280305 := bstep (se 2 (by rfl) ⟨855114, by rfl⟩ : syracuseStep 2280305 = 1710229) B1710229
theorem B3042161 : Blo 1350994 3042161 := bstep (se 2 (by rfl) ⟨1140810, by rfl⟩ : syracuseStep 3042161 = 2281621) B2281621
theorem B3042179 : Blo 1350994 3042179 := bstep (se 1 (by rfl) ⟨2281634, by rfl⟩ : syracuseStep 3042179 = 4563269) B4563269
theorem B1624963 : Blo 1350994 1624963 := bstep (se 1 (by rfl) ⟨1218722, by rfl⟩ : syracuseStep 1624963 = 2437445) B2437445
theorem B4623277 : Blo 1350994 4623277 := bstep (se 3 (by rfl) ⟨866864, by rfl⟩ : syracuseStep 4623277 = 1733729) B1733729
theorem B4565969 : Blo 1350994 4565969 := bstep (se 2 (by rfl) ⟨1712238, by rfl⟩ : syracuseStep 4565969 = 3424477) B3424477
theorem B1625059 : Blo 1350994 1625059 := bstep (se 1 (by rfl) ⟨1218794, by rfl⟩ : syracuseStep 1625059 = 2437589) B2437589
theorem B2280433 : Blo 1350994 2280433 := bstep (se 2 (by rfl) ⟨855162, by rfl⟩ : syracuseStep 2280433 = 1710325) B1710325
theorem B2026499 : Blo 1350994 2026499 := bstep (se 1 (by rfl) ⟨1519874, by rfl⟩ : syracuseStep 2026499 = 3039749) B3039749
theorem B2280467 : Blo 1350994 2280467 := bstep (se 1 (by rfl) ⟨1710350, by rfl⟩ : syracuseStep 2280467 = 3420701) B3420701
theorem B2026529 : Blo 1350994 2026529 := bstep (se 2 (by rfl) ⟨759948, by rfl⟩ : syracuseStep 2026529 = 1519897) B1519897
theorem B2026547 : Blo 1350994 2026547 := bstep (se 1 (by rfl) ⟨1519910, by rfl⟩ : syracuseStep 2026547 = 3039821) B3039821
theorem B2026577 : Blo 1350994 2026577 := bstep (se 2 (by rfl) ⟨759966, by rfl⟩ : syracuseStep 2026577 = 1519933) B1519933
theorem B2026595 : Blo 1350994 2026595 := bstep (se 1 (by rfl) ⟨1519946, by rfl⟩ : syracuseStep 2026595 = 3039893) B3039893
theorem B1625203 : Blo 1350994 1625203 := bstep (se 1 (by rfl) ⟨1218902, by rfl⟩ : syracuseStep 1625203 = 2437805) B2437805
theorem B2026625 : Blo 1350994 2026625 := bstep (se 2 (by rfl) ⟨759984, by rfl⟩ : syracuseStep 2026625 = 1519969) B1519969
theorem B3247235 : Blo 1350994 3247235 := bstep (se 1 (by rfl) ⟨2435426, by rfl⟩ : syracuseStep 3247235 = 4870853) B4870853
theorem B3042449 : Blo 1350994 3042449 := bstep (se 2 (by rfl) ⟨1140918, by rfl⟩ : syracuseStep 3042449 = 2281837) B2281837
theorem B2026643 : Blo 1350994 2026643 := bstep (se 1 (by rfl) ⟨1519982, by rfl⟩ : syracuseStep 2026643 = 3039965) B3039965
theorem B2280595 : Blo 1350994 2280595 := bstep (se 1 (by rfl) ⟨1710446, by rfl⟩ : syracuseStep 2280595 = 3420893) B3420893
theorem B3042467 : Blo 1350994 3042467 := bstep (se 1 (by rfl) ⟨2281850, by rfl⟩ : syracuseStep 3042467 = 4563701) B4563701
theorem B2026673 : Blo 1350994 2026673 := bstep (se 2 (by rfl) ⟨760002, by rfl⟩ : syracuseStep 2026673 = 1520005) B1520005
theorem B2886833 : Blo 1350994 2886833 := bstep (se 2 (by rfl) ⟨1082562, by rfl⟩ : syracuseStep 2886833 = 2165125) B2165125
theorem B2026691 : Blo 1350994 2026691 := bstep (se 1 (by rfl) ⟨1520018, by rfl⟩ : syracuseStep 2026691 = 3040037) B3040037
theorem B2026721 : Blo 1350994 2026721 := bstep (se 2 (by rfl) ⟨760020, by rfl⟩ : syracuseStep 2026721 = 1520041) B1520041
theorem B2026739 : Blo 1350994 2026739 := bstep (se 1 (by rfl) ⟨1520054, by rfl⟩ : syracuseStep 2026739 = 3040109) B3040109
theorem B2026769 : Blo 1350994 2026769 := bstep (se 2 (by rfl) ⟨760038, by rfl⟩ : syracuseStep 2026769 = 1520077) B1520077
theorem B2280737 : Blo 1350994 2280737 := bstep (se 2 (by rfl) ⟨855276, by rfl⟩ : syracuseStep 2280737 = 1710553) B1710553
theorem B2026787 : Blo 1350994 2026787 := bstep (se 1 (by rfl) ⟨1520090, by rfl⟩ : syracuseStep 2026787 = 3040181) B3040181
theorem B9375011 : Blo 1350994 9375011 := bstep (se 1 (by rfl) ⟨7031258, by rfl⟩ : syracuseStep 9375011 = 14062517) B14062517
theorem B2026817 : Blo 1350994 2026817 := bstep (se 2 (by rfl) ⟨760056, by rfl⟩ : syracuseStep 2026817 = 1520113) B1520113
theorem B2739523 : Blo 1350994 2739523 := bstep (se 1 (by rfl) ⟨2054642, by rfl⟩ : syracuseStep 2739523 = 4109285) B4109285
theorem B2026835 : Blo 1350994 2026835 := bstep (se 1 (by rfl) ⟨1520126, by rfl⟩ : syracuseStep 2026835 = 3040253) B3040253
theorem B2026865 : Blo 1350994 2026865 := bstep (se 2 (by rfl) ⟨760074, by rfl⟩ : syracuseStep 2026865 = 1520149) B1520149
theorem B2026883 : Blo 1350994 2026883 := bstep (se 1 (by rfl) ⟨1520162, by rfl⟩ : syracuseStep 2026883 = 3040325) B3040325
theorem B4509073 : Blo 1350994 4509073 := bstep (se 2 (by rfl) ⟨1690902, by rfl⟩ : syracuseStep 4509073 = 3381805) B3381805
theorem B2026913 : Blo 1350994 2026913 := bstep (se 2 (by rfl) ⟨760092, by rfl⟩ : syracuseStep 2026913 = 1520185) B1520185
theorem B2280865 : Blo 1350994 2280865 := bstep (se 2 (by rfl) ⟨855324, by rfl⟩ : syracuseStep 2280865 = 1710649) B1710649
theorem B3042737 : Blo 1350994 3042737 := bstep (se 2 (by rfl) ⟨1141026, by rfl⟩ : syracuseStep 3042737 = 2282053) B2282053
theorem B2026931 : Blo 1350994 2026931 := bstep (se 1 (by rfl) ⟨1520198, by rfl⟩ : syracuseStep 2026931 = 3040397) B3040397
theorem B2280899 : Blo 1350994 2280899 := bstep (se 1 (by rfl) ⟨1710674, by rfl⟩ : syracuseStep 2280899 = 3421349) B3421349
theorem B3755459 : Blo 1350994 3755459 := bstep (se 1 (by rfl) ⟨2816594, by rfl⟩ : syracuseStep 3755459 = 5633189) B5633189
theorem B3042755 : Blo 1350994 3042755 := bstep (se 1 (by rfl) ⟨2282066, by rfl⟩ : syracuseStep 3042755 = 4564133) B4564133
theorem B2026961 : Blo 1350994 2026961 := bstep (se 2 (by rfl) ⟨760110, by rfl⟩ : syracuseStep 2026961 = 1520221) B1520221
theorem B2026979 : Blo 1350994 2026979 := bstep (se 1 (by rfl) ⟨1520234, by rfl⟩ : syracuseStep 2026979 = 3040469) B3040469
theorem B2027009 : Blo 1350994 2027009 := bstep (se 2 (by rfl) ⟨760128, by rfl⟩ : syracuseStep 2027009 = 1520257) B1520257
theorem B2027027 : Blo 1350994 2027027 := bstep (se 1 (by rfl) ⟨1520270, by rfl⟩ : syracuseStep 2027027 = 3040541) B3040541
theorem B2027057 : Blo 1350994 2027057 := bstep (se 2 (by rfl) ⟨760146, by rfl⟩ : syracuseStep 2027057 = 1520293) B1520293
theorem B2027075 : Blo 1350994 2027075 := bstep (se 1 (by rfl) ⟨1520306, by rfl⟩ : syracuseStep 2027075 = 3040613) B3040613
theorem B2281027 : Blo 1350994 2281027 := bstep (se 1 (by rfl) ⟨1710770, by rfl⟩ : syracuseStep 2281027 = 3421541) B3421541
theorem B3419729 : Blo 1350994 3419729 := bstep (se 2 (by rfl) ⟨1282398, by rfl⟩ : syracuseStep 3419729 = 2564797) B2564797
theorem B2166355 : Blo 1350994 2166355 := bstep (se 1 (by rfl) ⟨1624766, by rfl⟩ : syracuseStep 2166355 = 3249533) B3249533
theorem B2027105 : Blo 1350994 2027105 := bstep (se 2 (by rfl) ⟨760164, by rfl⟩ : syracuseStep 2027105 = 1520329) B1520329
theorem B2027123 : Blo 1350994 2027123 := bstep (se 1 (by rfl) ⟨1520342, by rfl⟩ : syracuseStep 2027123 = 3040685) B3040685
theorem B3419779 : Blo 1350994 3419779 := bstep (se 1 (by rfl) ⟨2564834, by rfl⟩ : syracuseStep 3419779 = 5129669) B5129669
theorem B2027153 : Blo 1350994 2027153 := bstep (se 2 (by rfl) ⟨760182, by rfl⟩ : syracuseStep 2027153 = 1520365) B1520365
theorem B2027171 : Blo 1350994 2027171 := bstep (se 1 (by rfl) ⟨1520378, by rfl⟩ : syracuseStep 2027171 = 3040757) B3040757
theorem B2567857 : Blo 1350994 2567857 := bstep (se 2 (by rfl) ⟨962946, by rfl⟩ : syracuseStep 2567857 = 1925893) B1925893
theorem B2928305 : Blo 1350994 2928305 := bstep (se 2 (by rfl) ⟨1098114, by rfl⟩ : syracuseStep 2928305 = 2196229) B2196229
theorem B2027201 : Blo 1350994 2027201 := bstep (se 2 (by rfl) ⟨760200, by rfl⟩ : syracuseStep 2027201 = 1520401) B1520401
theorem B2281169 : Blo 1350994 2281169 := bstep (se 2 (by rfl) ⟨855438, by rfl⟩ : syracuseStep 2281169 = 1710877) B1710877
theorem B2027219 : Blo 1350994 2027219 := bstep (se 1 (by rfl) ⟨1520414, by rfl⟩ : syracuseStep 2027219 = 3040829) B3040829
theorem B3043025 : Blo 1350994 3043025 := bstep (se 2 (by rfl) ⟨1141134, by rfl⟩ : syracuseStep 3043025 = 2282269) B2282269
theorem B3043043 : Blo 1350994 3043043 := bstep (se 1 (by rfl) ⟨2282282, by rfl⟩ : syracuseStep 3043043 = 4564565) B4564565
theorem B2027249 : Blo 1350994 2027249 := bstep (se 2 (by rfl) ⟨760218, by rfl⟩ : syracuseStep 2027249 = 1520437) B1520437
theorem B2027267 : Blo 1350994 2027267 := bstep (se 1 (by rfl) ⟨1520450, by rfl⟩ : syracuseStep 2027267 = 3040901) B3040901
theorem B3419921 : Blo 1350994 3419921 := bstep (se 2 (by rfl) ⟨1282470, by rfl⟩ : syracuseStep 3419921 = 2564941) B2564941
theorem B2027297 : Blo 1350994 2027297 := bstep (se 2 (by rfl) ⟨760236, by rfl⟩ : syracuseStep 2027297 = 1520473) B1520473
theorem B2027315 : Blo 1350994 2027315 := bstep (se 1 (by rfl) ⟨1520486, by rfl⟩ : syracuseStep 2027315 = 3040973) B3040973
theorem B2314051 : Blo 1350994 2314051 := bstep (se 1 (by rfl) ⟨1735538, by rfl⟩ : syracuseStep 2314051 = 3471077) B3471077
theorem B2027345 : Blo 1350994 2027345 := bstep (se 2 (by rfl) ⟨760254, by rfl⟩ : syracuseStep 2027345 = 1520509) B1520509
theorem B2281297 : Blo 1350994 2281297 := bstep (se 2 (by rfl) ⟨855486, by rfl⟩ : syracuseStep 2281297 = 1710973) B1710973
theorem B2568017 : Blo 1350994 2568017 := bstep (se 2 (by rfl) ⟨963006, by rfl⟩ : syracuseStep 2568017 = 1926013) B1926013
theorem B2027363 : Blo 1350994 2027363 := bstep (se 1 (by rfl) ⟨1520522, by rfl⟩ : syracuseStep 2027363 = 3041045) B3041045
theorem B12341105 : Blo 1350994 12341105 := bstep (se 2 (by rfl) ⟨4627914, by rfl⟩ : syracuseStep 12341105 = 9255829) B9255829
theorem B2281331 : Blo 1350994 2281331 := bstep (se 1 (by rfl) ⟨1710998, by rfl⟩ : syracuseStep 2281331 = 3421997) B3421997
theorem B2027393 : Blo 1350994 2027393 := bstep (se 2 (by rfl) ⟨760272, by rfl⟩ : syracuseStep 2027393 = 1520545) B1520545
theorem B3248003 : Blo 1350994 3248003 := bstep (se 1 (by rfl) ⟨2436002, by rfl⟩ : syracuseStep 3248003 = 4872005) B4872005
theorem B2027411 : Blo 1350994 2027411 := bstep (se 1 (by rfl) ⟨1520558, by rfl⟩ : syracuseStep 2027411 = 3041117) B3041117
theorem B4329389 : Blo 1350994 4329389 := bstep (se 3 (by rfl) ⟨811760, by rfl⟩ : syracuseStep 4329389 = 1623521) B1623521
theorem B2027441 : Blo 1350994 2027441 := bstep (se 2 (by rfl) ⟨760290, by rfl⟩ : syracuseStep 2027441 = 1520581) B1520581
theorem B6844337 : Blo 1350994 6844337 := bstep (se 2 (by rfl) ⟨2566626, by rfl⟩ : syracuseStep 6844337 = 5133253) B5133253
theorem B2027459 : Blo 1350994 2027459 := bstep (se 1 (by rfl) ⟨1520594, by rfl⟩ : syracuseStep 2027459 = 3041189) B3041189
theorem B4689859 : Blo 1350994 4689859 := bstep (se 1 (by rfl) ⟨3517394, by rfl⟩ : syracuseStep 4689859 = 7034789) B7034789
theorem B2027489 : Blo 1350994 2027489 := bstep (se 2 (by rfl) ⟨760308, by rfl⟩ : syracuseStep 2027489 = 1520617) B1520617
theorem B3043313 : Blo 1350994 3043313 := bstep (se 2 (by rfl) ⟨1141242, by rfl⟩ : syracuseStep 3043313 = 2282485) B2282485
theorem B2027507 : Blo 1350994 2027507 := bstep (se 1 (by rfl) ⟨1520630, by rfl⟩ : syracuseStep 2027507 = 3041261) B3041261
theorem B2281459 : Blo 1350994 2281459 := bstep (se 1 (by rfl) ⟨1711094, by rfl⟩ : syracuseStep 2281459 = 3422189) B3422189
theorem B3043331 : Blo 1350994 3043331 := bstep (se 1 (by rfl) ⟨2282498, by rfl⟩ : syracuseStep 3043331 = 4564997) B4564997
theorem B2027537 : Blo 1350994 2027537 := bstep (se 2 (by rfl) ⟨760326, by rfl⟩ : syracuseStep 2027537 = 1520653) B1520653
theorem B2027555 : Blo 1350994 2027555 := bstep (se 1 (by rfl) ⟨1520666, by rfl⟩ : syracuseStep 2027555 = 3041333) B3041333
theorem B2027585 : Blo 1350994 2027585 := bstep (se 2 (by rfl) ⟨760344, by rfl⟩ : syracuseStep 2027585 = 1520689) B1520689
theorem B2027603 : Blo 1350994 2027603 := bstep (se 1 (by rfl) ⟨1520702, by rfl⟩ : syracuseStep 2027603 = 3041405) B3041405
theorem B2027633 : Blo 1350994 2027633 := bstep (se 2 (by rfl) ⟨760362, by rfl⟩ : syracuseStep 2027633 = 1520725) B1520725
theorem B2281601 : Blo 1350994 2281601 := bstep (se 2 (by rfl) ⟨855600, by rfl⟩ : syracuseStep 2281601 = 1711201) B1711201
theorem B2027651 : Blo 1350994 2027651 := bstep (se 1 (by rfl) ⟨1520738, by rfl⟩ : syracuseStep 2027651 = 3041477) B3041477
theorem B2027681 : Blo 1350994 2027681 := bstep (se 2 (by rfl) ⟨760380, by rfl⟩ : syracuseStep 2027681 = 1520761) B1520761
theorem B2027699 : Blo 1350994 2027699 := bstep (se 1 (by rfl) ⟨1520774, by rfl⟩ : syracuseStep 2027699 = 3041549) B3041549
theorem B2027729 : Blo 1350994 2027729 := bstep (se 2 (by rfl) ⟨760398, by rfl⟩ : syracuseStep 2027729 = 1520797) B1520797
theorem B2027747 : Blo 1350994 2027747 := bstep (se 1 (by rfl) ⟨1520810, by rfl⟩ : syracuseStep 2027747 = 3041621) B3041621
theorem B2568419 : Blo 1350994 2568419 := bstep (se 1 (by rfl) ⟨1926314, by rfl⟩ : syracuseStep 2568419 = 3852629) B3852629
theorem B2027777 : Blo 1350994 2027777 := bstep (se 2 (by rfl) ⟨760416, by rfl⟩ : syracuseStep 2027777 = 1520833) B1520833
theorem B2281729 : Blo 1350994 2281729 := bstep (se 2 (by rfl) ⟨855648, by rfl⟩ : syracuseStep 2281729 = 1711297) B1711297
theorem B3043601 : Blo 1350994 3043601 := bstep (se 2 (by rfl) ⟨1141350, by rfl⟩ : syracuseStep 3043601 = 2282701) B2282701
theorem B2027795 : Blo 1350994 2027795 := bstep (se 1 (by rfl) ⟨1520846, by rfl⟩ : syracuseStep 2027795 = 3041693) B3041693
theorem B2281763 : Blo 1350994 2281763 := bstep (se 1 (by rfl) ⟨1711322, by rfl⟩ : syracuseStep 2281763 = 3422645) B3422645
theorem B3043619 : Blo 1350994 3043619 := bstep (se 1 (by rfl) ⟨2282714, by rfl⟩ : syracuseStep 3043619 = 4565429) B4565429
theorem B2027825 : Blo 1350994 2027825 := bstep (se 2 (by rfl) ⟨760434, by rfl⟩ : syracuseStep 2027825 = 1520869) B1520869
theorem B1462595 : Blo 1350994 1462595 := bstep (se 1 (by rfl) ⟨1096946, by rfl⟩ : syracuseStep 1462595 = 2193893) B2193893
theorem B2027843 : Blo 1350994 2027843 := bstep (se 1 (by rfl) ⟨1520882, by rfl⟩ : syracuseStep 2027843 = 3041765) B3041765
theorem B2027873 : Blo 1350994 2027873 := bstep (se 2 (by rfl) ⟨760452, by rfl⟩ : syracuseStep 2027873 = 1520905) B1520905
theorem B1519987 : Blo 1350994 1519987 := bstep (se 1 (by rfl) ⟨1139990, by rfl⟩ : syracuseStep 1519987 = 2279981) B2279981
theorem B2027891 : Blo 1350994 2027891 := bstep (se 1 (by rfl) ⟨1520918, by rfl⟩ : syracuseStep 2027891 = 3041837) B3041837
theorem B18510221 : Blo 1350994 18510221 := bstep (se 3 (by rfl) ⟨3470666, by rfl⟩ : syracuseStep 18510221 = 6941333) B6941333
theorem B2027921 : Blo 1350994 2027921 := bstep (se 2 (by rfl) ⟨760470, by rfl⟩ : syracuseStep 2027921 = 1520941) B1520941
theorem B2027939 : Blo 1350994 2027939 := bstep (se 1 (by rfl) ⟨1520954, by rfl⟩ : syracuseStep 2027939 = 3041909) B3041909
theorem B2281891 : Blo 1350994 2281891 := bstep (se 1 (by rfl) ⟨1711418, by rfl⟩ : syracuseStep 2281891 = 3422837) B3422837
theorem B3248561 : Blo 1350994 3248561 := bstep (se 2 (by rfl) ⟨1218210, by rfl⟩ : syracuseStep 3248561 = 2436421) B2436421
theorem B2027969 : Blo 1350994 2027969 := bstep (se 2 (by rfl) ⟨760488, by rfl⟩ : syracuseStep 2027969 = 1520977) B1520977
theorem B2888131 : Blo 1350994 2888131 := bstep (se 1 (by rfl) ⟨2166098, by rfl⟩ : syracuseStep 2888131 = 4332197) B4332197
theorem B3469763 : Blo 1350994 3469763 := bstep (se 1 (by rfl) ⟨2602322, by rfl⟩ : syracuseStep 3469763 = 5204645) B5204645
theorem B2027987 : Blo 1350994 2027987 := bstep (se 1 (by rfl) ⟨1520990, by rfl⟩ : syracuseStep 2027987 = 3041981) B3041981
theorem B2028017 : Blo 1350994 2028017 := bstep (se 2 (by rfl) ⟨760506, by rfl⟩ : syracuseStep 2028017 = 1521013) B1521013
theorem B1520131 : Blo 1350994 1520131 := bstep (se 1 (by rfl) ⟨1140098, by rfl⟩ : syracuseStep 1520131 = 2280197) B2280197
theorem B2028035 : Blo 1350994 2028035 := bstep (se 1 (by rfl) ⟨1521026, by rfl⟩ : syracuseStep 2028035 = 3042053) B3042053
theorem B2028065 : Blo 1350994 2028065 := bstep (se 2 (by rfl) ⟨760524, by rfl⟩ : syracuseStep 2028065 = 1521049) B1521049
theorem B2282033 : Blo 1350994 2282033 := bstep (se 2 (by rfl) ⟨855762, by rfl⟩ : syracuseStep 2282033 = 1711525) B1711525
theorem B2028083 : Blo 1350994 2028083 := bstep (se 1 (by rfl) ⟨1521062, by rfl⟩ : syracuseStep 2028083 = 3042125) B3042125
theorem B3043889 : Blo 1350994 3043889 := bstep (se 2 (by rfl) ⟨1141458, by rfl⟩ : syracuseStep 3043889 = 2282917) B2282917
theorem B3043907 : Blo 1350994 3043907 := bstep (se 1 (by rfl) ⟨2282930, by rfl⟩ : syracuseStep 3043907 = 4565861) B4565861
theorem B7705165 : Blo 1350994 7705165 := bstep (se 3 (by rfl) ⟨1444718, by rfl⟩ : syracuseStep 7705165 = 2889437) B2889437
theorem B2028113 : Blo 1350994 2028113 := bstep (se 2 (by rfl) ⟨760542, by rfl⟩ : syracuseStep 2028113 = 1521085) B1521085
theorem B2028131 : Blo 1350994 2028131 := bstep (se 1 (by rfl) ⟨1521098, by rfl⟩ : syracuseStep 2028131 = 3042197) B3042197
theorem B2028161 : Blo 1350994 2028161 := bstep (se 2 (by rfl) ⟨760560, by rfl⟩ : syracuseStep 2028161 = 1521121) B1521121
theorem B1520275 : Blo 1350994 1520275 := bstep (se 1 (by rfl) ⟨1140206, by rfl⟩ : syracuseStep 1520275 = 2280413) B2280413
theorem B2028179 : Blo 1350994 2028179 := bstep (se 1 (by rfl) ⟨1521134, by rfl⟩ : syracuseStep 2028179 = 3042269) B3042269
theorem B2028209 : Blo 1350994 2028209 := bstep (se 2 (by rfl) ⟨760578, by rfl⟩ : syracuseStep 2028209 = 1521157) B1521157
theorem B2282161 : Blo 1350994 2282161 := bstep (se 2 (by rfl) ⟨855810, by rfl⟩ : syracuseStep 2282161 = 1711621) B1711621
theorem B2028227 : Blo 1350994 2028227 := bstep (se 1 (by rfl) ⟨1521170, by rfl⟩ : syracuseStep 2028227 = 3042341) B3042341
theorem B3248849 : Blo 1350994 3248849 := bstep (se 2 (by rfl) ⟨1218318, by rfl⟩ : syracuseStep 3248849 = 2436637) B2436637
theorem B2282195 : Blo 1350994 2282195 := bstep (se 1 (by rfl) ⟨1711646, by rfl⟩ : syracuseStep 2282195 = 3423293) B3423293
theorem B2028257 : Blo 1350994 2028257 := bstep (se 2 (by rfl) ⟨760596, by rfl⟩ : syracuseStep 2028257 = 1521193) B1521193
theorem B3420913 : Blo 1350994 3420913 := bstep (se 2 (by rfl) ⟨1282842, by rfl⟩ : syracuseStep 3420913 = 2565685) B2565685
theorem B5133041 : Blo 1350994 5133041 := bstep (se 2 (by rfl) ⟨1924890, by rfl⟩ : syracuseStep 5133041 = 3849781) B3849781
theorem B2028275 : Blo 1350994 2028275 := bstep (se 1 (by rfl) ⟨1521206, by rfl⟩ : syracuseStep 2028275 = 3042413) B3042413
theorem B2028305 : Blo 1350994 2028305 := bstep (se 2 (by rfl) ⟨760614, by rfl⟩ : syracuseStep 2028305 = 1521229) B1521229
theorem B4559651 : Blo 1350994 4559651 := bstep (se 1 (by rfl) ⟨3419738, by rfl⟩ : syracuseStep 4559651 = 6839477) B6839477
theorem B1520419 : Blo 1350994 1520419 := bstep (se 1 (by rfl) ⟨1140314, by rfl⟩ : syracuseStep 1520419 = 2280629) B2280629
theorem B2028323 : Blo 1350994 2028323 := bstep (se 1 (by rfl) ⟨1521242, by rfl⟩ : syracuseStep 2028323 = 3042485) B3042485
theorem B2028353 : Blo 1350994 2028353 := bstep (se 2 (by rfl) ⟨760632, by rfl⟩ : syracuseStep 2028353 = 1521265) B1521265
theorem B3044177 : Blo 1350994 3044177 := bstep (se 2 (by rfl) ⟨1141566, by rfl⟩ : syracuseStep 3044177 = 2283133) B2283133
theorem B2028371 : Blo 1350994 2028371 := bstep (se 1 (by rfl) ⟨1521278, by rfl⟩ : syracuseStep 2028371 = 3042557) B3042557
theorem B2282323 : Blo 1350994 2282323 := bstep (se 1 (by rfl) ⟨1711742, by rfl⟩ : syracuseStep 2282323 = 3423485) B3423485
theorem B3044195 : Blo 1350994 3044195 := bstep (se 1 (by rfl) ⟨2283146, by rfl⟩ : syracuseStep 3044195 = 4566293) B4566293
theorem B2028401 : Blo 1350994 2028401 := bstep (se 2 (by rfl) ⟨760650, by rfl⟩ : syracuseStep 2028401 = 1521301) B1521301
theorem B37106545 : Blo 1350994 37106545 := bstep (se 2 (by rfl) ⟨13914954, by rfl⟩ : syracuseStep 37106545 = 27829909) B27829909
theorem B2028419 : Blo 1350994 2028419 := bstep (se 1 (by rfl) ⟨1521314, by rfl⟩ : syracuseStep 2028419 = 3042629) B3042629
theorem B4109197 : Blo 1350994 4109197 := bstep (se 3 (by rfl) ⟨770474, by rfl⟩ : syracuseStep 4109197 = 1540949) B1540949
theorem B4166545 : Blo 1350994 4166545 := bstep (se 2 (by rfl) ⟨1562454, by rfl⟩ : syracuseStep 4166545 = 3124909) B3124909
theorem B2028449 : Blo 1350994 2028449 := bstep (se 2 (by rfl) ⟨760668, by rfl⟩ : syracuseStep 2028449 = 1521337) B1521337
theorem B1520563 : Blo 1350994 1520563 := bstep (se 1 (by rfl) ⟨1140422, by rfl⟩ : syracuseStep 1520563 = 2280845) B2280845
theorem B2028467 : Blo 1350994 2028467 := bstep (se 1 (by rfl) ⟨1521350, by rfl⟩ : syracuseStep 2028467 = 3042701) B3042701
theorem B2028497 : Blo 1350994 2028497 := bstep (se 2 (by rfl) ⟨760686, by rfl⟩ : syracuseStep 2028497 = 1521373) B1521373
theorem B2282465 : Blo 1350994 2282465 := bstep (se 2 (by rfl) ⟨855924, by rfl⟩ : syracuseStep 2282465 = 1711849) B1711849
theorem B2028515 : Blo 1350994 2028515 := bstep (se 1 (by rfl) ⟨1521386, by rfl⟩ : syracuseStep 2028515 = 3042773) B3042773
theorem B9745393 : Blo 1350994 9745393 := bstep (se 2 (by rfl) ⟨3654522, by rfl⟩ : syracuseStep 9745393 = 7309045) B7309045
theorem B2028545 : Blo 1350994 2028545 := bstep (se 2 (by rfl) ⟨760704, by rfl⟩ : syracuseStep 2028545 = 1521409) B1521409
theorem B3421187 : Blo 1350994 3421187 := bstep (se 1 (by rfl) ⟨2565890, by rfl⟩ : syracuseStep 3421187 = 5131781) B5131781
theorem B2028563 : Blo 1350994 2028563 := bstep (se 1 (by rfl) ⟨1521422, by rfl⟩ : syracuseStep 2028563 = 3042845) B3042845
theorem B4559921 : Blo 1350994 4559921 := bstep (se 2 (by rfl) ⟨1709970, by rfl⟩ : syracuseStep 4559921 = 3419941) B3419941
theorem B2028593 : Blo 1350994 2028593 := bstep (se 2 (by rfl) ⟨760722, by rfl⟩ : syracuseStep 2028593 = 1521445) B1521445
theorem B1520707 : Blo 1350994 1520707 := bstep (se 1 (by rfl) ⟨1140530, by rfl⟩ : syracuseStep 1520707 = 2281061) B2281061
theorem B2028611 : Blo 1350994 2028611 := bstep (se 1 (by rfl) ⟨1521458, by rfl⟩ : syracuseStep 2028611 = 3042917) B3042917
theorem B4109393 : Blo 1350994 4109393 := bstep (se 2 (by rfl) ⟨1541022, by rfl⟩ : syracuseStep 4109393 = 3082045) B3082045
theorem B2028641 : Blo 1350994 2028641 := bstep (se 2 (by rfl) ⟨760740, by rfl⟩ : syracuseStep 2028641 = 1521481) B1521481
theorem B18494563 : Blo 1350994 18494563 := bstep (se 1 (by rfl) ⟨13870922, by rfl⟩ : syracuseStep 18494563 = 27741845) B27741845
theorem B2282593 : Blo 1350994 2282593 := bstep (se 2 (by rfl) ⟨855972, by rfl⟩ : syracuseStep 2282593 = 1711945) B1711945
theorem B2028659 : Blo 1350994 2028659 := bstep (se 1 (by rfl) ⟨1521494, by rfl⟩ : syracuseStep 2028659 = 3042989) B3042989
theorem B2282627 : Blo 1350994 2282627 := bstep (se 1 (by rfl) ⟨1711970, by rfl⟩ : syracuseStep 2282627 = 3423941) B3423941
theorem B2028689 : Blo 1350994 2028689 := bstep (se 2 (by rfl) ⟨760758, by rfl⟩ : syracuseStep 2028689 = 1521517) B1521517
theorem B2028707 : Blo 1350994 2028707 := bstep (se 1 (by rfl) ⟨1521530, by rfl⟩ : syracuseStep 2028707 = 3043061) B3043061
theorem B3421379 : Blo 1350994 3421379 := bstep (se 1 (by rfl) ⟨2566034, by rfl⟩ : syracuseStep 3421379 = 5132069) B5132069
theorem B2028737 : Blo 1350994 2028737 := bstep (se 2 (by rfl) ⟨760776, by rfl⟩ : syracuseStep 2028737 = 1521553) B1521553
theorem B1520851 : Blo 1350994 1520851 := bstep (se 1 (by rfl) ⟨1140638, by rfl⟩ : syracuseStep 1520851 = 2281277) B2281277
theorem B2028755 : Blo 1350994 2028755 := bstep (se 1 (by rfl) ⟨1521566, by rfl⟩ : syracuseStep 2028755 = 3043133) B3043133
theorem B2028785 : Blo 1350994 2028785 := bstep (se 2 (by rfl) ⟨760794, by rfl⟩ : syracuseStep 2028785 = 1521589) B1521589
theorem B2028803 : Blo 1350994 2028803 := bstep (se 1 (by rfl) ⟨1521602, by rfl⟩ : syracuseStep 2028803 = 3043205) B3043205
theorem B2282755 : Blo 1350994 2282755 := bstep (se 1 (by rfl) ⟨1712066, by rfl⟩ : syracuseStep 2282755 = 3424133) B3424133
theorem B2028833 : Blo 1350994 2028833 := bstep (se 2 (by rfl) ⟨760812, by rfl⟩ : syracuseStep 2028833 = 1521625) B1521625
theorem B5559587 : Blo 1350994 5559587 := bstep (se 1 (by rfl) ⟨4169690, by rfl⟩ : syracuseStep 5559587 = 8339381) B8339381
theorem B2028851 : Blo 1350994 2028851 := bstep (se 1 (by rfl) ⟨1521638, by rfl⟩ : syracuseStep 2028851 = 3043277) B3043277
theorem B2028881 : Blo 1350994 2028881 := bstep (se 2 (by rfl) ⟨760830, by rfl⟩ : syracuseStep 2028881 = 1521661) B1521661
theorem B1520995 : Blo 1350994 1520995 := bstep (se 1 (by rfl) ⟨1140746, by rfl⟩ : syracuseStep 1520995 = 2281493) B2281493
theorem B6845795 : Blo 1350994 6845795 := bstep (se 1 (by rfl) ⟨5134346, by rfl⟩ : syracuseStep 6845795 = 10268693) B10268693
theorem B2028899 : Blo 1350994 2028899 := bstep (se 1 (by rfl) ⟨1521674, by rfl⟩ : syracuseStep 2028899 = 3043349) B3043349
theorem B2028929 : Blo 1350994 2028929 := bstep (se 2 (by rfl) ⟨760848, by rfl⟩ : syracuseStep 2028929 = 1521697) B1521697
theorem B2282897 : Blo 1350994 2282897 := bstep (se 2 (by rfl) ⟨856086, by rfl⟩ : syracuseStep 2282897 = 1712173) B1712173
theorem B2028947 : Blo 1350994 2028947 := bstep (se 1 (by rfl) ⟨1521710, by rfl⟩ : syracuseStep 2028947 = 3043421) B3043421
theorem B5477795 : Blo 1350994 5477795 := bstep (se 1 (by rfl) ⟨4108346, by rfl⟩ : syracuseStep 5477795 = 8216693) B8216693
theorem B2028977 : Blo 1350994 2028977 := bstep (se 2 (by rfl) ⟨760866, by rfl⟩ : syracuseStep 2028977 = 1521733) B1521733
theorem B2028995 : Blo 1350994 2028995 := bstep (se 1 (by rfl) ⟨1521746, by rfl⟩ : syracuseStep 2028995 = 3043493) B3043493
theorem B4330979 : Blo 1350994 4330979 := bstep (se 1 (by rfl) ⟨3248234, by rfl⟩ : syracuseStep 4330979 = 6496469) B6496469
theorem B2029025 : Blo 1350994 2029025 := bstep (se 2 (by rfl) ⟨760884, by rfl⟩ : syracuseStep 2029025 = 1521769) B1521769
theorem B1521139 : Blo 1350994 1521139 := bstep (se 1 (by rfl) ⟨1140854, by rfl⟩ : syracuseStep 1521139 = 2281709) B2281709
theorem B2029043 : Blo 1350994 2029043 := bstep (se 1 (by rfl) ⟨1521782, by rfl⟩ : syracuseStep 2029043 = 3043565) B3043565
theorem B2029073 : Blo 1350994 2029073 := bstep (se 2 (by rfl) ⟨760902, by rfl⟩ : syracuseStep 2029073 = 1521805) B1521805
theorem B2283025 : Blo 1350994 2283025 := bstep (se 2 (by rfl) ⟨856134, by rfl⟩ : syracuseStep 2283025 = 1712269) B1712269
theorem B1734179 : Blo 1350994 1734179 := bstep (se 1 (by rfl) ⟨1300634, by rfl⟩ : syracuseStep 1734179 = 2601269) B2601269
theorem B2029091 : Blo 1350994 2029091 := bstep (se 1 (by rfl) ⟨1521818, by rfl⟩ : syracuseStep 2029091 = 3043637) B3043637
theorem B4109869 : Blo 1350994 4109869 := bstep (se 3 (by rfl) ⟨770600, by rfl⟩ : syracuseStep 4109869 = 1541201) B1541201
theorem B2283059 : Blo 1350994 2283059 := bstep (se 1 (by rfl) ⟨1712294, by rfl⟩ : syracuseStep 2283059 = 3424589) B3424589
theorem B2029121 : Blo 1350994 2029121 := bstep (se 2 (by rfl) ⟨760920, by rfl⟩ : syracuseStep 2029121 = 1521841) B1521841
theorem B4560461 : Blo 1350994 4560461 := bstep (se 3 (by rfl) ⟨855086, by rfl⟩ : syracuseStep 4560461 = 1710173) B1710173
theorem B2029139 : Blo 1350994 2029139 := bstep (se 1 (by rfl) ⟨1521854, by rfl⟩ : syracuseStep 2029139 = 3043709) B3043709
theorem B2029169 : Blo 1350994 2029169 := bstep (se 2 (by rfl) ⟨760938, by rfl⟩ : syracuseStep 2029169 = 1521877) B1521877
theorem B4560515 : Blo 1350994 4560515 := bstep (se 1 (by rfl) ⟨3420386, by rfl⟩ : syracuseStep 4560515 = 6840773) B6840773
theorem B1521283 : Blo 1350994 1521283 := bstep (se 1 (by rfl) ⟨1140962, by rfl⟩ : syracuseStep 1521283 = 2281925) B2281925
theorem B2029187 : Blo 1350994 2029187 := bstep (se 1 (by rfl) ⟨1521890, by rfl⟩ : syracuseStep 2029187 = 3043781) B3043781
theorem B2889361 : Blo 1350994 2889361 := bstep (se 2 (by rfl) ⟨1083510, by rfl⟩ : syracuseStep 2889361 = 2167021) B2167021
theorem B2029217 : Blo 1350994 2029217 := bstep (se 2 (by rfl) ⟨760956, by rfl⟩ : syracuseStep 2029217 = 1521913) B1521913
theorem B4331171 : Blo 1350994 4331171 := bstep (se 1 (by rfl) ⟨3248378, by rfl⟩ : syracuseStep 4331171 = 6496757) B6496757
theorem B2029235 : Blo 1350994 2029235 := bstep (se 1 (by rfl) ⟨1521926, by rfl⟩ : syracuseStep 2029235 = 3043853) B3043853
theorem B2029265 : Blo 1350994 2029265 := bstep (se 2 (by rfl) ⟨760974, by rfl⟩ : syracuseStep 2029265 = 1521949) B1521949
theorem B8664803 : Blo 1350994 8664803 := bstep (se 1 (by rfl) ⟨6498602, by rfl⟩ : syracuseStep 8664803 = 12997205) B12997205
theorem B2029283 : Blo 1350994 2029283 := bstep (se 1 (by rfl) ⟨1521962, by rfl⟩ : syracuseStep 2029283 = 3043925) B3043925
theorem B8656625 : Blo 1350994 8656625 := bstep (se 2 (by rfl) ⟨3246234, by rfl⟩ : syracuseStep 8656625 = 6492469) B6492469
theorem B2029313 : Blo 1350994 2029313 := bstep (se 2 (by rfl) ⟨760992, by rfl⟩ : syracuseStep 2029313 = 1521985) B1521985
theorem B1521427 : Blo 1350994 1521427 := bstep (se 1 (by rfl) ⟨1141070, by rfl⟩ : syracuseStep 1521427 = 2282141) B2282141
theorem B2029331 : Blo 1350994 2029331 := bstep (se 1 (by rfl) ⟨1521998, by rfl⟩ : syracuseStep 2029331 = 3043997) B3043997
theorem B3847981 : Blo 1350994 3847981 := bstep (se 3 (by rfl) ⟨721496, by rfl⟩ : syracuseStep 3847981 = 1442993) B1442993
theorem B2029361 : Blo 1350994 2029361 := bstep (se 2 (by rfl) ⟨761010, by rfl⟩ : syracuseStep 2029361 = 1522021) B1522021
theorem B2029379 : Blo 1350994 2029379 := bstep (se 1 (by rfl) ⟨1522034, by rfl⟩ : syracuseStep 2029379 = 3044069) B3044069
theorem B15611717 : Blo 1350994 15611717 := bstep (se 4 (by rfl) ⟨1463598, by rfl⟩ : syracuseStep 15611717 = 2927197) B2927197
theorem B5773133 : Blo 1350994 5773133 := bstep (se 3 (by rfl) ⟨1082462, by rfl⟩ : syracuseStep 5773133 = 2164925) B2164925
theorem B2029409 : Blo 1350994 2029409 := bstep (se 2 (by rfl) ⟨761028, by rfl⟩ : syracuseStep 2029409 = 1522057) B1522057
theorem B2029427 : Blo 1350994 2029427 := bstep (se 1 (by rfl) ⟨1522070, by rfl⟩ : syracuseStep 2029427 = 3044141) B3044141
theorem B4560785 : Blo 1350994 4560785 := bstep (se 2 (by rfl) ⟨1710294, by rfl⟩ : syracuseStep 4560785 = 3420589) B3420589
theorem B2029457 : Blo 1350994 2029457 := bstep (se 2 (by rfl) ⟨761046, by rfl⟩ : syracuseStep 2029457 = 1522093) B1522093
theorem B1521571 : Blo 1350994 1521571 := bstep (se 1 (by rfl) ⟨1141178, by rfl⟩ : syracuseStep 1521571 = 2282357) B2282357
theorem B2029475 : Blo 1350994 2029475 := bstep (se 1 (by rfl) ⟨1522106, by rfl⟩ : syracuseStep 2029475 = 3044213) B3044213
theorem B3848141 : Blo 1350994 3848141 := bstep (se 3 (by rfl) ⟨721526, by rfl⟩ : syracuseStep 3848141 = 1443053) B1443053
theorem B1710067 : Blo 1350994 1710067 := bstep (se 1 (by rfl) ⟨1282550, by rfl⟩ : syracuseStep 1710067 = 2565101) B2565101
theorem B1521715 : Blo 1350994 1521715 := bstep (se 1 (by rfl) ⟨1141286, by rfl⟩ : syracuseStep 1521715 = 2282573) B2282573
theorem B1710163 : Blo 1350994 1710163 := bstep (se 1 (by rfl) ⟨1282622, by rfl⟩ : syracuseStep 1710163 = 2565245) B2565245
theorem B3422321 : Blo 1350994 3422321 := bstep (se 2 (by rfl) ⟨1283370, by rfl⟩ : syracuseStep 3422321 = 2566741) B2566741
theorem B3848323 : Blo 1350994 3848323 := bstep (se 1 (by rfl) ⟨2886242, by rfl⟩ : syracuseStep 3848323 = 5772485) B5772485
theorem B6846605 : Blo 1350994 6846605 := bstep (se 3 (by rfl) ⟨1283738, by rfl⟩ : syracuseStep 6846605 = 2567477) B2567477
theorem B3422371 : Blo 1350994 3422371 := bstep (se 1 (by rfl) ⟨2566778, by rfl⟩ : syracuseStep 3422371 = 5133557) B5133557
theorem B5134499 : Blo 1350994 5134499 := bstep (se 1 (by rfl) ⟨3850874, by rfl⟩ : syracuseStep 5134499 = 7701749) B7701749
theorem B1521859 : Blo 1350994 1521859 := bstep (se 1 (by rfl) ⟨1141394, by rfl⟩ : syracuseStep 1521859 = 2282789) B2282789
theorem B3422513 : Blo 1350994 3422513 := bstep (se 2 (by rfl) ⟨1283442, by rfl⟩ : syracuseStep 3422513 = 2566885) B2566885
theorem B4331825 : Blo 1350994 4331825 := bstep (se 2 (by rfl) ⟨1624434, by rfl⟩ : syracuseStep 4331825 = 3248869) B3248869
theorem B1522003 : Blo 1350994 1522003 := bstep (se 1 (by rfl) ⟨1141502, by rfl⟩ : syracuseStep 1522003 = 2283005) B2283005
theorem B4561325 : Blo 1350994 4561325 := bstep (se 3 (by rfl) ⟨855248, by rfl⟩ : syracuseStep 4561325 = 1710497) B1710497
theorem B4561379 : Blo 1350994 4561379 := bstep (se 1 (by rfl) ⟨3421034, by rfl⟩ : syracuseStep 4561379 = 6842069) B6842069
theorem B15399395 : Blo 1350994 15399395 := bstep (se 1 (by rfl) ⟨11549546, by rfl⟩ : syracuseStep 15399395 = 23099093) B23099093
theorem B1710659 : Blo 1350994 1710659 := bstep (se 1 (by rfl) ⟨1282994, by rfl⟩ : syracuseStep 1710659 = 2565989) B2565989
theorem B11557475 : Blo 1350994 11557475 := bstep (se 1 (by rfl) ⟨8668106, by rfl⟩ : syracuseStep 11557475 = 17336213) B17336213
theorem B8657549 : Blo 1350994 8657549 := bstep (se 3 (by rfl) ⟨1623290, by rfl⟩ : syracuseStep 8657549 = 3246581) B3246581
theorem B3652273 : Blo 1350994 3652273 := bstep (se 2 (by rfl) ⟨1369602, by rfl⟩ : syracuseStep 3652273 = 2739205) B2739205
theorem B1923763 : Blo 1350994 1923763 := bstep (se 1 (by rfl) ⟨1442822, by rfl⟩ : syracuseStep 1923763 = 2885645) B2885645
theorem B11549411 : Blo 1350994 11549411 := bstep (se 1 (by rfl) ⟨8662058, by rfl⟩ : syracuseStep 11549411 = 17324117) B17324117
theorem B4561649 : Blo 1350994 4561649 := bstep (se 2 (by rfl) ⟨1710618, by rfl⟩ : syracuseStep 4561649 = 3421237) B3421237
theorem B7699333 : Blo 1350994 7699333 := bstep (se 4 (by rfl) ⟨721812, by rfl⟩ : syracuseStep 7699333 = 1443625) B1443625
theorem B5135501 : Blo 1350994 5135501 := bstep (se 3 (by rfl) ⟨962906, by rfl⟩ : syracuseStep 5135501 = 1925813) B1925813
theorem B1924241 : Blo 1350994 1924241 := bstep (se 2 (by rfl) ⟨721590, by rfl⟩ : syracuseStep 1924241 = 1443181) B1443181
theorem B1826003 : Blo 1350994 1826003 := bstep (se 1 (by rfl) ⟨1369502, by rfl⟩ : syracuseStep 1826003 = 2739005) B2739005
theorem B1924355 : Blo 1350994 1924355 := bstep (se 1 (by rfl) ⟨1443266, by rfl⟩ : syracuseStep 1924355 = 2886533) B2886533
theorem B1711363 : Blo 1350994 1711363 := bstep (se 1 (by rfl) ⟨1283522, by rfl⟩ : syracuseStep 1711363 = 2567045) B2567045
theorem B4562189 : Blo 1350994 4562189 := bstep (se 3 (by rfl) ⟨855410, by rfl⟩ : syracuseStep 4562189 = 1710821) B1710821
theorem B3423505 : Blo 1350994 3423505 := bstep (se 2 (by rfl) ⟨1283814, by rfl⟩ : syracuseStep 3423505 = 2567629) B2567629
theorem B4562243 : Blo 1350994 4562243 := bstep (se 1 (by rfl) ⟨3421682, by rfl⟩ : syracuseStep 4562243 = 6843365) B6843365
theorem B1350995 : Blo 1350994 1350995 := bstep (se 1 (by rfl) ⟨1013246, by rfl⟩ : syracuseStep 1350995 = 2026493) B2026493
theorem B1924435 : Blo 1350994 1924435 := bstep (se 1 (by rfl) ⟨1443326, by rfl⟩ : syracuseStep 1924435 = 2886653) B2886653
theorem B1351011 : Blo 1350994 1351011 := bstep (se 1 (by rfl) ⟨1013258, by rfl⟩ : syracuseStep 1351011 = 2026517) B2026517
theorem B1711459 : Blo 1350994 1711459 := bstep (se 1 (by rfl) ⟨1283594, by rfl⟩ : syracuseStep 1711459 = 2567189) B2567189
theorem B1351027 : Blo 1350994 1351027 := bstep (se 1 (by rfl) ⟨1013270, by rfl⟩ : syracuseStep 1351027 = 2026541) B2026541
theorem B1351043 : Blo 1350994 1351043 := bstep (se 1 (by rfl) ⟨1013282, by rfl⟩ : syracuseStep 1351043 = 2026565) B2026565
theorem B1351059 : Blo 1350994 1351059 := bstep (se 1 (by rfl) ⟨1013294, by rfl⟩ : syracuseStep 1351059 = 2026589) B2026589
theorem B1351075 : Blo 1350994 1351075 := bstep (se 1 (by rfl) ⟨1013306, by rfl⟩ : syracuseStep 1351075 = 2026613) B2026613
theorem B1351091 : Blo 1350994 1351091 := bstep (se 1 (by rfl) ⟨1013318, by rfl⟩ : syracuseStep 1351091 = 2026637) B2026637
theorem B1351107 : Blo 1350994 1351107 := bstep (se 1 (by rfl) ⟨1013330, by rfl⟩ : syracuseStep 1351107 = 2026661) B2026661
theorem B1351123 : Blo 1350994 1351123 := bstep (se 1 (by rfl) ⟨1013342, by rfl⟩ : syracuseStep 1351123 = 2026685) B2026685
theorem B1351139 : Blo 1350994 1351139 := bstep (se 1 (by rfl) ⟨1013354, by rfl⟩ : syracuseStep 1351139 = 2026709) B2026709
theorem B3849713 : Blo 1350994 3849713 := bstep (se 2 (by rfl) ⟨1443642, by rfl⟩ : syracuseStep 3849713 = 2887285) B2887285
theorem B13876721 : Blo 1350994 13876721 := bstep (se 2 (by rfl) ⟨5203770, by rfl⟩ : syracuseStep 13876721 = 10407541) B10407541
theorem B1351155 : Blo 1350994 1351155 := bstep (se 1 (by rfl) ⟨1013366, by rfl⟩ : syracuseStep 1351155 = 2026733) B2026733
theorem B1351171 : Blo 1350994 1351171 := bstep (se 1 (by rfl) ⟨1013378, by rfl⟩ : syracuseStep 1351171 = 2026757) B2026757
theorem B1351187 : Blo 1350994 1351187 := bstep (se 1 (by rfl) ⟨1013390, by rfl⟩ : syracuseStep 1351187 = 2026781) B2026781
theorem B1351203 : Blo 1350994 1351203 := bstep (se 1 (by rfl) ⟨1013402, by rfl⟩ : syracuseStep 1351203 = 2026805) B2026805
theorem B3423779 : Blo 1350994 3423779 := bstep (se 1 (by rfl) ⟨2567834, by rfl⟩ : syracuseStep 3423779 = 5135669) B5135669
theorem B1826353 : Blo 1350994 1826353 := bstep (se 2 (by rfl) ⟨684882, by rfl⟩ : syracuseStep 1826353 = 1369765) B1369765
theorem B1351219 : Blo 1350994 1351219 := bstep (se 1 (by rfl) ⟨1013414, by rfl⟩ : syracuseStep 1351219 = 2026829) B2026829
theorem B1351235 : Blo 1350994 1351235 := bstep (se 1 (by rfl) ⟨1013426, by rfl⟩ : syracuseStep 1351235 = 2026853) B2026853
theorem B4562513 : Blo 1350994 4562513 := bstep (se 2 (by rfl) ⟨1710942, by rfl⟩ : syracuseStep 4562513 = 3421885) B3421885
theorem B1351251 : Blo 1350994 1351251 := bstep (se 1 (by rfl) ⟨1013438, by rfl⟩ : syracuseStep 1351251 = 2026877) B2026877
theorem B1351267 : Blo 1350994 1351267 := bstep (se 1 (by rfl) ⟨1013450, by rfl⟩ : syracuseStep 1351267 = 2026901) B2026901
theorem B1351283 : Blo 1350994 1351283 := bstep (se 1 (by rfl) ⟨1013462, by rfl⟩ : syracuseStep 1351283 = 2026925) B2026925
theorem B1351299 : Blo 1350994 1351299 := bstep (se 1 (by rfl) ⟨1013474, by rfl⟩ : syracuseStep 1351299 = 2026949) B2026949
theorem B1351315 : Blo 1350994 1351315 := bstep (se 1 (by rfl) ⟨1013486, by rfl⟩ : syracuseStep 1351315 = 2026973) B2026973
theorem B1351331 : Blo 1350994 1351331 := bstep (se 1 (by rfl) ⟨1013498, by rfl⟩ : syracuseStep 1351331 = 2026997) B2026997
theorem B5480099 : Blo 1350994 5480099 := bstep (se 1 (by rfl) ⟨4110074, by rfl⟩ : syracuseStep 5480099 = 8220149) B8220149
theorem B1351347 : Blo 1350994 1351347 := bstep (se 1 (by rfl) ⟨1013510, by rfl⟩ : syracuseStep 1351347 = 2027021) B2027021
theorem B1351363 : Blo 1350994 1351363 := bstep (se 1 (by rfl) ⟨1013522, by rfl⟩ : syracuseStep 1351363 = 2027045) B2027045
theorem B1351379 : Blo 1350994 1351379 := bstep (se 1 (by rfl) ⟨1013534, by rfl⟩ : syracuseStep 1351379 = 2027069) B2027069
theorem B1351395 : Blo 1350994 1351395 := bstep (se 1 (by rfl) ⟨1013546, by rfl⟩ : syracuseStep 1351395 = 2027093) B2027093
theorem B3423971 : Blo 1350994 3423971 := bstep (se 1 (by rfl) ⟨2567978, by rfl⟩ : syracuseStep 3423971 = 5135957) B5135957
theorem B1351411 : Blo 1350994 1351411 := bstep (se 1 (by rfl) ⟨1013558, by rfl⟩ : syracuseStep 1351411 = 2027117) B2027117
theorem B2055937 : Blo 1350994 2055937 := bstep (se 2 (by rfl) ⟨770976, by rfl⟩ : syracuseStep 2055937 = 1541953) B1541953
theorem B1351427 : Blo 1350994 1351427 := bstep (se 1 (by rfl) ⟨1013570, by rfl⟩ : syracuseStep 1351427 = 2027141) B2027141
theorem B1351443 : Blo 1350994 1351443 := bstep (se 1 (by rfl) ⟨1013582, by rfl⟩ : syracuseStep 1351443 = 2027165) B2027165
theorem B1351459 : Blo 1350994 1351459 := bstep (se 1 (by rfl) ⟨1013594, by rfl⟩ : syracuseStep 1351459 = 2027189) B2027189
theorem B5480227 : Blo 1350994 5480227 := bstep (se 1 (by rfl) ⟨4110170, by rfl⟩ : syracuseStep 5480227 = 8220341) B8220341
theorem B1351475 : Blo 1350994 1351475 := bstep (se 1 (by rfl) ⟨1013606, by rfl⟩ : syracuseStep 1351475 = 2027213) B2027213
theorem B1351491 : Blo 1350994 1351491 := bstep (se 1 (by rfl) ⟨1013618, by rfl⟩ : syracuseStep 1351491 = 2027237) B2027237
theorem B10272581 : Blo 1350994 10272581 := bstep (se 4 (by rfl) ⟨963054, by rfl⟩ : syracuseStep 10272581 = 1926109) B1926109
theorem B1351507 : Blo 1350994 1351507 := bstep (se 1 (by rfl) ⟨1013630, by rfl⟩ : syracuseStep 1351507 = 2027261) B2027261
theorem B1711955 : Blo 1350994 1711955 := bstep (se 1 (by rfl) ⟨1283966, by rfl⟩ : syracuseStep 1711955 = 2567933) B2567933
theorem B1351523 : Blo 1350994 1351523 := bstep (se 1 (by rfl) ⟨1013642, by rfl⟩ : syracuseStep 1351523 = 2027285) B2027285
theorem B1351539 : Blo 1350994 1351539 := bstep (se 1 (by rfl) ⟨1013654, by rfl⟩ : syracuseStep 1351539 = 2027309) B2027309
theorem B1924993 : Blo 1350994 1924993 := bstep (se 2 (by rfl) ⟨721872, by rfl⟩ : syracuseStep 1924993 = 1443745) B1443745
theorem B1351555 : Blo 1350994 1351555 := bstep (se 1 (by rfl) ⟨1013666, by rfl⟩ : syracuseStep 1351555 = 2027333) B2027333
theorem B4169603 : Blo 1350994 4169603 := bstep (se 1 (by rfl) ⟨3127202, by rfl⟩ : syracuseStep 4169603 = 6254405) B6254405
theorem B1351571 : Blo 1350994 1351571 := bstep (se 1 (by rfl) ⟨1013678, by rfl⟩ : syracuseStep 1351571 = 2027357) B2027357
theorem B1351587 : Blo 1350994 1351587 := bstep (se 1 (by rfl) ⟨1013690, by rfl⟩ : syracuseStep 1351587 = 2027381) B2027381
theorem B1351603 : Blo 1350994 1351603 := bstep (se 1 (by rfl) ⟨1013702, by rfl⟩ : syracuseStep 1351603 = 2027405) B2027405
theorem B1351619 : Blo 1350994 1351619 := bstep (se 1 (by rfl) ⟨1013714, by rfl⟩ : syracuseStep 1351619 = 2027429) B2027429
theorem B1351635 : Blo 1350994 1351635 := bstep (se 1 (by rfl) ⟨1013726, by rfl⟩ : syracuseStep 1351635 = 2027453) B2027453
theorem B1351651 : Blo 1350994 1351651 := bstep (se 1 (by rfl) ⟨1013738, by rfl⟩ : syracuseStep 1351651 = 2027477) B2027477
theorem B9748451 : Blo 1350994 9748451 := bstep (se 1 (by rfl) ⟨7311338, by rfl⟩ : syracuseStep 9748451 = 14622677) B14622677
theorem B1351667 : Blo 1350994 1351667 := bstep (se 1 (by rfl) ⟨1013750, by rfl⟩ : syracuseStep 1351667 = 2027501) B2027501
theorem B1351691 : Blo 1350994 1351691 := bstep (se 1 (by rfl) ⟨1013768, by rfl⟩ : syracuseStep 1351691 = 2027537) B2027537
theorem B1351703 : Blo 1350994 1351703 := bstep (se 1 (by rfl) ⟨1013777, by rfl⟩ : syracuseStep 1351703 = 2027555) B2027555
theorem B1351723 : Blo 1350994 1351723 := bstep (se 1 (by rfl) ⟨1013792, by rfl⟩ : syracuseStep 1351723 = 2027585) B2027585
theorem B1351735 : Blo 1350994 1351735 := bstep (se 1 (by rfl) ⟨1013801, by rfl⟩ : syracuseStep 1351735 = 2027603) B2027603
theorem B1351755 : Blo 1350994 1351755 := bstep (se 1 (by rfl) ⟨1013816, by rfl⟩ : syracuseStep 1351755 = 2027633) B2027633
theorem B1351767 : Blo 1350994 1351767 := bstep (se 1 (by rfl) ⟨1013825, by rfl⟩ : syracuseStep 1351767 = 2027651) B2027651
theorem B5136473 : Blo 1350994 5136473 := bstep (se 2 (by rfl) ⟨1926177, by rfl⟩ : syracuseStep 5136473 = 3852355) B3852355
theorem B1351787 : Blo 1350994 1351787 := bstep (se 1 (by rfl) ⟨1013840, by rfl⟩ : syracuseStep 1351787 = 2027681) B2027681
theorem B1351799 : Blo 1350994 1351799 := bstep (se 1 (by rfl) ⟨1013849, by rfl⟩ : syracuseStep 1351799 = 2027699) B2027699
theorem B1351819 : Blo 1350994 1351819 := bstep (se 1 (by rfl) ⟨1013864, by rfl⟩ : syracuseStep 1351819 = 2027729) B2027729
theorem B1351831 : Blo 1350994 1351831 := bstep (se 1 (by rfl) ⟨1013873, by rfl⟩ : syracuseStep 1351831 = 2027747) B2027747
theorem B8667287 : Blo 1350994 8667287 := bstep (se 1 (by rfl) ⟨6500465, by rfl⟩ : syracuseStep 8667287 = 13000931) B13000931
theorem B1712279 : Blo 1350994 1712279 := bstep (se 1 (by rfl) ⟨1284209, by rfl⟩ : syracuseStep 1712279 = 2568419) B2568419
theorem B1351851 : Blo 1350994 1351851 := bstep (se 1 (by rfl) ⟨1013888, by rfl⟩ : syracuseStep 1351851 = 2027777) B2027777
theorem B4874413 : Blo 1350994 4874413 := bstep (se 3 (by rfl) ⟨913952, by rfl⟩ : syracuseStep 4874413 = 1827905) B1827905
theorem B1351863 : Blo 1350994 1351863 := bstep (se 1 (by rfl) ⟨1013897, by rfl⟩ : syracuseStep 1351863 = 2027795) B2027795
theorem B1351883 : Blo 1350994 1351883 := bstep (se 1 (by rfl) ⟨1013912, by rfl⟩ : syracuseStep 1351883 = 2027825) B2027825
theorem B1351895 : Blo 1350994 1351895 := bstep (se 1 (by rfl) ⟨1013921, by rfl⟩ : syracuseStep 1351895 = 2027843) B2027843
theorem B4563161 : Blo 1350994 4563161 := bstep (se 2 (by rfl) ⟨1711185, by rfl⟩ : syracuseStep 4563161 = 3422371) B3422371
theorem B1351915 : Blo 1350994 1351915 := bstep (se 1 (by rfl) ⟨1013936, by rfl⟩ : syracuseStep 1351915 = 2027873) B2027873
theorem B1351927 : Blo 1350994 1351927 := bstep (se 1 (by rfl) ⟨1013945, by rfl⟩ : syracuseStep 1351927 = 2027891) B2027891
theorem B9740549 : Blo 1350994 9740549 := bstep (se 4 (by rfl) ⟨913176, by rfl⟩ : syracuseStep 9740549 = 1826353) B1826353
theorem B1351947 : Blo 1350994 1351947 := bstep (se 1 (by rfl) ⟨1013960, by rfl⟩ : syracuseStep 1351947 = 2027921) B2027921
theorem B1351959 : Blo 1350994 1351959 := bstep (se 1 (by rfl) ⟨1013969, by rfl⟩ : syracuseStep 1351959 = 2027939) B2027939
theorem B1351979 : Blo 1350994 1351979 := bstep (se 1 (by rfl) ⟨1013984, by rfl⟩ : syracuseStep 1351979 = 2027969) B2027969
theorem B1351991 : Blo 1350994 1351991 := bstep (se 1 (by rfl) ⟨1013993, by rfl⟩ : syracuseStep 1351991 = 2027987) B2027987
theorem B1352011 : Blo 1350994 1352011 := bstep (se 1 (by rfl) ⟨1014008, by rfl⟩ : syracuseStep 1352011 = 2028017) B2028017
theorem B1352023 : Blo 1350994 1352023 := bstep (se 1 (by rfl) ⟨1014017, by rfl⟩ : syracuseStep 1352023 = 2028035) B2028035
theorem B1352043 : Blo 1350994 1352043 := bstep (se 1 (by rfl) ⟨1014032, by rfl⟩ : syracuseStep 1352043 = 2028065) B2028065
theorem B18497909 : Blo 1350994 18497909 := bstep (se 5 (by rfl) ⟨867089, by rfl⟩ : syracuseStep 18497909 = 1734179) B1734179
theorem B1352055 : Blo 1350994 1352055 := bstep (se 1 (by rfl) ⟨1014041, by rfl⟩ : syracuseStep 1352055 = 2028083) B2028083
theorem B1352075 : Blo 1350994 1352075 := bstep (se 1 (by rfl) ⟨1014056, by rfl⟩ : syracuseStep 1352075 = 2028113) B2028113
theorem B1352087 : Blo 1350994 1352087 := bstep (se 1 (by rfl) ⟨1014065, by rfl⟩ : syracuseStep 1352087 = 2028131) B2028131
theorem B1352107 : Blo 1350994 1352107 := bstep (se 1 (by rfl) ⟨1014080, by rfl⟩ : syracuseStep 1352107 = 2028161) B2028161
theorem B1352119 : Blo 1350994 1352119 := bstep (se 1 (by rfl) ⟨1014089, by rfl⟩ : syracuseStep 1352119 = 2028179) B2028179
theorem B1352139 : Blo 1350994 1352139 := bstep (se 1 (by rfl) ⟨1014104, by rfl⟩ : syracuseStep 1352139 = 2028209) B2028209
theorem B1352151 : Blo 1350994 1352151 := bstep (se 1 (by rfl) ⟨1014113, by rfl⟩ : syracuseStep 1352151 = 2028227) B2028227
theorem B1352171 : Blo 1350994 1352171 := bstep (se 1 (by rfl) ⟨1014128, by rfl⟩ : syracuseStep 1352171 = 2028257) B2028257
theorem B1352183 : Blo 1350994 1352183 := bstep (se 1 (by rfl) ⟨1014137, by rfl⟩ : syracuseStep 1352183 = 2028275) B2028275
theorem B1352203 : Blo 1350994 1352203 := bstep (se 1 (by rfl) ⟨1014152, by rfl⟩ : syracuseStep 1352203 = 2028305) B2028305
theorem B3039767 : Blo 1350994 3039767 := bstep (se 1 (by rfl) ⟨2279825, by rfl⟩ : syracuseStep 3039767 = 4559651) B4559651
theorem B1352215 : Blo 1350994 1352215 := bstep (se 1 (by rfl) ⟨1014161, by rfl⟩ : syracuseStep 1352215 = 2028323) B2028323
theorem B1352235 : Blo 1350994 1352235 := bstep (se 1 (by rfl) ⟨1014176, by rfl⟩ : syracuseStep 1352235 = 2028353) B2028353
theorem B1352247 : Blo 1350994 1352247 := bstep (se 1 (by rfl) ⟨1014185, by rfl⟩ : syracuseStep 1352247 = 2028371) B2028371
theorem B1352267 : Blo 1350994 1352267 := bstep (se 1 (by rfl) ⟨1014200, by rfl⟩ : syracuseStep 1352267 = 2028401) B2028401
theorem B1352279 : Blo 1350994 1352279 := bstep (se 1 (by rfl) ⟨1014209, by rfl⟩ : syracuseStep 1352279 = 2028419) B2028419
theorem B3850841 : Blo 1350994 3850841 := bstep (se 2 (by rfl) ⟨1444065, by rfl⟩ : syracuseStep 3850841 = 2888131) B2888131
theorem B8667749 : Blo 1350994 8667749 := bstep (se 4 (by rfl) ⟨812601, by rfl⟩ : syracuseStep 8667749 = 1625203) B1625203
theorem B1352299 : Blo 1350994 1352299 := bstep (se 1 (by rfl) ⟨1014224, by rfl⟩ : syracuseStep 1352299 = 2028449) B2028449
theorem B1352311 : Blo 1350994 1352311 := bstep (se 1 (by rfl) ⟨1014233, by rfl⟩ : syracuseStep 1352311 = 2028467) B2028467
theorem B1352331 : Blo 1350994 1352331 := bstep (se 1 (by rfl) ⟨1014248, by rfl⟩ : syracuseStep 1352331 = 2028497) B2028497
theorem B1352343 : Blo 1350994 1352343 := bstep (se 1 (by rfl) ⟨1014257, by rfl⟩ : syracuseStep 1352343 = 2028515) B2028515
theorem B1925785 : Blo 1350994 1925785 := bstep (se 2 (by rfl) ⟨722169, by rfl⟩ : syracuseStep 1925785 = 1444339) B1444339
theorem B1352363 : Blo 1350994 1352363 := bstep (se 1 (by rfl) ⟨1014272, by rfl⟩ : syracuseStep 1352363 = 2028545) B2028545
theorem B1352375 : Blo 1350994 1352375 := bstep (se 1 (by rfl) ⟨1014281, by rfl⟩ : syracuseStep 1352375 = 2028563) B2028563
theorem B3039947 : Blo 1350994 3039947 := bstep (se 1 (by rfl) ⟨2279960, by rfl⟩ : syracuseStep 3039947 = 4559921) B4559921
theorem B1352395 : Blo 1350994 1352395 := bstep (se 1 (by rfl) ⟨1014296, by rfl⟩ : syracuseStep 1352395 = 2028593) B2028593
theorem B1352407 : Blo 1350994 1352407 := bstep (se 1 (by rfl) ⟨1014305, by rfl⟩ : syracuseStep 1352407 = 2028611) B2028611
theorem B1352427 : Blo 1350994 1352427 := bstep (se 1 (by rfl) ⟨1014320, by rfl⟩ : syracuseStep 1352427 = 2028641) B2028641
theorem B1352439 : Blo 1350994 1352439 := bstep (se 1 (by rfl) ⟨1014329, by rfl⟩ : syracuseStep 1352439 = 2028659) B2028659
theorem B3040001 : Blo 1350994 3040001 := bstep (se 2 (by rfl) ⟨1140000, by rfl⟩ : syracuseStep 3040001 = 2280001) B2280001
theorem B1352459 : Blo 1350994 1352459 := bstep (se 1 (by rfl) ⟨1014344, by rfl⟩ : syracuseStep 1352459 = 2028689) B2028689
theorem B10273553 : Blo 1350994 10273553 := bstep (se 2 (by rfl) ⟨3852582, by rfl⟩ : syracuseStep 10273553 = 7705165) B7705165
theorem B1352471 : Blo 1350994 1352471 := bstep (se 1 (by rfl) ⟨1014353, by rfl⟩ : syracuseStep 1352471 = 2028707) B2028707
theorem B1352491 : Blo 1350994 1352491 := bstep (se 1 (by rfl) ⟨1014368, by rfl⟩ : syracuseStep 1352491 = 2028737) B2028737
theorem B1352503 : Blo 1350994 1352503 := bstep (se 1 (by rfl) ⟨1014377, by rfl⟩ : syracuseStep 1352503 = 2028755) B2028755
theorem B1352523 : Blo 1350994 1352523 := bstep (se 1 (by rfl) ⟨1014392, by rfl⟩ : syracuseStep 1352523 = 2028785) B2028785
theorem B1352535 : Blo 1350994 1352535 := bstep (se 1 (by rfl) ⟨1014401, by rfl⟩ : syracuseStep 1352535 = 2028803) B2028803
theorem B3900253 : Blo 1350994 3900253 := bstep (se 3 (by rfl) ⟨731297, by rfl⟩ : syracuseStep 3900253 = 1462595) B1462595
theorem B1352555 : Blo 1350994 1352555 := bstep (se 1 (by rfl) ⟨1014416, by rfl⟩ : syracuseStep 1352555 = 2028833) B2028833
theorem B1352567 : Blo 1350994 1352567 := bstep (se 1 (by rfl) ⟨1014425, by rfl⟩ : syracuseStep 1352567 = 2028851) B2028851
theorem B1352587 : Blo 1350994 1352587 := bstep (se 1 (by rfl) ⟨1014440, by rfl⟩ : syracuseStep 1352587 = 2028881) B2028881
theorem B4563863 : Blo 1350994 4563863 := bstep (se 1 (by rfl) ⟨3422897, by rfl⟩ : syracuseStep 4563863 = 6845795) B6845795
theorem B1352599 : Blo 1350994 1352599 := bstep (se 1 (by rfl) ⟨1014449, by rfl⟩ : syracuseStep 1352599 = 2028899) B2028899
theorem B2565017 : Blo 1350994 2565017 := bstep (se 2 (by rfl) ⟨961881, by rfl⟩ : syracuseStep 2565017 = 1923763) B1923763
theorem B1352619 : Blo 1350994 1352619 := bstep (se 1 (by rfl) ⟨1014464, by rfl⟩ : syracuseStep 1352619 = 2028929) B2028929
theorem B1352631 : Blo 1350994 1352631 := bstep (se 1 (by rfl) ⟨1014473, by rfl⟩ : syracuseStep 1352631 = 2028947) B2028947
theorem B1352651 : Blo 1350994 1352651 := bstep (se 1 (by rfl) ⟨1014488, by rfl⟩ : syracuseStep 1352651 = 2028977) B2028977
theorem B1352663 : Blo 1350994 1352663 := bstep (se 1 (by rfl) ⟨1014497, by rfl⟩ : syracuseStep 1352663 = 2028995) B2028995
theorem B3040217 : Blo 1350994 3040217 := bstep (se 2 (by rfl) ⟨1140081, by rfl⟩ : syracuseStep 3040217 = 2280163) B2280163
theorem B1352683 : Blo 1350994 1352683 := bstep (se 1 (by rfl) ⟨1014512, by rfl⟩ : syracuseStep 1352683 = 2029025) B2029025
theorem B1352695 : Blo 1350994 1352695 := bstep (se 1 (by rfl) ⟨1014521, by rfl⟩ : syracuseStep 1352695 = 2029043) B2029043
theorem B1352715 : Blo 1350994 1352715 := bstep (se 1 (by rfl) ⟨1014536, by rfl⟩ : syracuseStep 1352715 = 2029073) B2029073
theorem B1352727 : Blo 1350994 1352727 := bstep (se 1 (by rfl) ⟨1014545, by rfl⟩ : syracuseStep 1352727 = 2029091) B2029091
theorem B1352747 : Blo 1350994 1352747 := bstep (se 1 (by rfl) ⟨1014560, by rfl⟩ : syracuseStep 1352747 = 2029121) B2029121
theorem B3040307 : Blo 1350994 3040307 := bstep (se 1 (by rfl) ⟨2280230, by rfl⟩ : syracuseStep 3040307 = 4560461) B4560461
theorem B1352759 : Blo 1350994 1352759 := bstep (se 1 (by rfl) ⟨1014569, by rfl⟩ : syracuseStep 1352759 = 2029139) B2029139
theorem B1352779 : Blo 1350994 1352779 := bstep (se 1 (by rfl) ⟨1014584, by rfl⟩ : syracuseStep 1352779 = 2029169) B2029169
theorem B3040343 : Blo 1350994 3040343 := bstep (se 1 (by rfl) ⟨2280257, by rfl⟩ : syracuseStep 3040343 = 4560515) B4560515
theorem B1352791 : Blo 1350994 1352791 := bstep (se 1 (by rfl) ⟨1014593, by rfl⟩ : syracuseStep 1352791 = 2029187) B2029187
theorem B1352811 : Blo 1350994 1352811 := bstep (se 1 (by rfl) ⟨1014608, by rfl⟩ : syracuseStep 1352811 = 2029217) B2029217
theorem B1352823 : Blo 1350994 1352823 := bstep (se 1 (by rfl) ⟨1014617, by rfl⟩ : syracuseStep 1352823 = 2029235) B2029235
theorem B1352843 : Blo 1350994 1352843 := bstep (se 1 (by rfl) ⟨1014632, by rfl⟩ : syracuseStep 1352843 = 2029265) B2029265
theorem B5776535 : Blo 1350994 5776535 := bstep (se 1 (by rfl) ⟨4332401, by rfl⟩ : syracuseStep 5776535 = 8664803) B8664803
theorem B1352855 : Blo 1350994 1352855 := bstep (se 1 (by rfl) ⟨1014641, by rfl⟩ : syracuseStep 1352855 = 2029283) B2029283
theorem B1352875 : Blo 1350994 1352875 := bstep (se 1 (by rfl) ⟨1014656, by rfl⟩ : syracuseStep 1352875 = 2029313) B2029313
theorem B10265777 : Blo 1350994 10265777 := bstep (se 2 (by rfl) ⟨3849666, by rfl⟩ : syracuseStep 10265777 = 7699333) B7699333
theorem B1352887 : Blo 1350994 1352887 := bstep (se 1 (by rfl) ⟨1014665, by rfl⟩ : syracuseStep 1352887 = 2029331) B2029331
theorem B5555393 : Blo 1350994 5555393 := bstep (se 2 (by rfl) ⟨2083272, by rfl⟩ : syracuseStep 5555393 = 4166545) B4166545
theorem B1352907 : Blo 1350994 1352907 := bstep (se 1 (by rfl) ⟨1014680, by rfl⟩ : syracuseStep 1352907 = 2029361) B2029361
theorem B1352919 : Blo 1350994 1352919 := bstep (se 1 (by rfl) ⟨1014689, by rfl⟩ : syracuseStep 1352919 = 2029379) B2029379
theorem B1352939 : Blo 1350994 1352939 := bstep (se 1 (by rfl) ⟨1014704, by rfl⟩ : syracuseStep 1352939 = 2029409) B2029409
theorem B1352951 : Blo 1350994 1352951 := bstep (se 1 (by rfl) ⟨1014713, by rfl⟩ : syracuseStep 1352951 = 2029427) B2029427
theorem B3040523 : Blo 1350994 3040523 := bstep (se 1 (by rfl) ⟨2280392, by rfl⟩ : syracuseStep 3040523 = 4560785) B4560785
theorem B1352971 : Blo 1350994 1352971 := bstep (se 1 (by rfl) ⟨1014728, by rfl⟩ : syracuseStep 1352971 = 2029457) B2029457
theorem B1352983 : Blo 1350994 1352983 := bstep (se 1 (by rfl) ⟨1014737, by rfl⟩ : syracuseStep 1352983 = 2029475) B2029475
theorem B2565427 : Blo 1350994 2565427 := bstep (se 1 (by rfl) ⟨1924070, by rfl⟩ : syracuseStep 2565427 = 3848141) B3848141
theorem B3040577 : Blo 1350994 3040577 := bstep (se 2 (by rfl) ⟨1140216, by rfl⟩ : syracuseStep 3040577 = 2280433) B2280433
theorem B12993857 : Blo 1350994 12993857 := bstep (se 2 (by rfl) ⟨4872696, by rfl⟩ : syracuseStep 12993857 = 9745393) B9745393
theorem B3900761 : Blo 1350994 3900761 := bstep (se 2 (by rfl) ⟨1462785, by rfl⟩ : syracuseStep 3900761 = 2925571) B2925571
theorem B1541515 : Blo 1350994 1541515 := bstep (se 1 (by rfl) ⟨1156136, by rfl⟩ : syracuseStep 1541515 = 2312273) B2312273
theorem B8783255 : Blo 1350994 8783255 := bstep (se 1 (by rfl) ⟨6587441, by rfl⟩ : syracuseStep 8783255 = 13174883) B13174883
theorem B4564403 : Blo 1350994 4564403 := bstep (se 1 (by rfl) ⟨3423302, by rfl⟩ : syracuseStep 4564403 = 6846605) B6846605
theorem B24659417 : Blo 1350994 24659417 := bstep (se 2 (by rfl) ⟨9247281, by rfl⟩ : syracuseStep 24659417 = 18494563) B18494563
theorem B3040793 : Blo 1350994 3040793 := bstep (se 2 (by rfl) ⟨1140297, by rfl⟩ : syracuseStep 3040793 = 2280595) B2280595
theorem B1541675 : Blo 1350994 1541675 := bstep (se 1 (by rfl) ⟨1156256, by rfl⟩ : syracuseStep 1541675 = 2312513) B2312513
theorem B1443403 : Blo 1350994 1443403 := bstep (se 1 (by rfl) ⟨1082552, by rfl⟩ : syracuseStep 1443403 = 2165105) B2165105
theorem B3040883 : Blo 1350994 3040883 := bstep (se 1 (by rfl) ⟨2280662, by rfl⟩ : syracuseStep 3040883 = 4561325) B4561325
theorem B3040919 : Blo 1350994 3040919 := bstep (se 1 (by rfl) ⟨2280689, by rfl⟩ : syracuseStep 3040919 = 4561379) B4561379
theorem B10266263 : Blo 1350994 10266263 := bstep (se 1 (by rfl) ⟨7699697, by rfl⟩ : syracuseStep 10266263 = 15399395) B15399395
theorem B4564673 : Blo 1350994 4564673 := bstep (se 2 (by rfl) ⟨1711752, by rfl⟩ : syracuseStep 4564673 = 3423505) B3423505
theorem B20801285 : Blo 1350994 20801285 := bstep (se 4 (by rfl) ⟨1950120, by rfl⟩ : syracuseStep 20801285 = 3900241) B3900241
theorem B2565913 : Blo 1350994 2565913 := bstep (se 2 (by rfl) ⟨962217, by rfl⟩ : syracuseStep 2565913 = 1924435) B1924435
theorem B7808813 : Blo 1350994 7808813 := bstep (se 3 (by rfl) ⟨1464152, by rfl⟩ : syracuseStep 7808813 = 2928305) B2928305
theorem B3655475 : Blo 1350994 3655475 := bstep (se 1 (by rfl) ⟨2741606, by rfl⟩ : syracuseStep 3655475 = 5483213) B5483213
theorem B3041099 : Blo 1350994 3041099 := bstep (se 1 (by rfl) ⟨2280824, by rfl⟩ : syracuseStep 3041099 = 4561649) B4561649
theorem B3041153 : Blo 1350994 3041153 := bstep (se 2 (by rfl) ⟨1140432, by rfl⟩ : syracuseStep 3041153 = 2280865) B2280865
theorem B2164823 : Blo 1350994 2164823 := bstep (se 1 (by rfl) ⟨1623617, by rfl⟩ : syracuseStep 2164823 = 3247235) B3247235
theorem B3041369 : Blo 1350994 3041369 := bstep (se 2 (by rfl) ⟨1140513, by rfl⟩ : syracuseStep 3041369 = 2281027) B2281027
theorem B3041459 : Blo 1350994 3041459 := bstep (se 1 (by rfl) ⟨2281094, by rfl⟩ : syracuseStep 3041459 = 4562189) B4562189
theorem B3852481 : Blo 1350994 3852481 := bstep (se 2 (by rfl) ⟨1444680, by rfl⟩ : syracuseStep 3852481 = 2889361) B2889361
theorem B15395021 : Blo 1350994 15395021 := bstep (se 3 (by rfl) ⟨2886566, by rfl⟩ : syracuseStep 15395021 = 5773133) B5773133
theorem B3041495 : Blo 1350994 3041495 := bstep (se 1 (by rfl) ⟨2281121, by rfl⟩ : syracuseStep 3041495 = 4562243) B4562243
theorem B8784089 : Blo 1350994 8784089 := bstep (se 2 (by rfl) ⟨3294033, by rfl⟩ : syracuseStep 8784089 = 6588067) B6588067
theorem B4565213 : Blo 1350994 4565213 := bstep (se 3 (by rfl) ⟨855977, by rfl⟩ : syracuseStep 4565213 = 1711955) B1711955
theorem B2566475 : Blo 1350994 2566475 := bstep (se 1 (by rfl) ⟨1924856, by rfl⟩ : syracuseStep 2566475 = 3849713) B3849713
theorem B9251147 : Blo 1350994 9251147 := bstep (se 1 (by rfl) ⟨6938360, by rfl⟩ : syracuseStep 9251147 = 13876721) B13876721
theorem B6842717 : Blo 1350994 6842717 := bstep (se 3 (by rfl) ⟨1283009, by rfl⟩ : syracuseStep 6842717 = 2566019) B2566019
theorem B11118941 : Blo 1350994 11118941 := bstep (se 3 (by rfl) ⟨2084801, by rfl⟩ : syracuseStep 11118941 = 4169603) B4169603
theorem B2279819 : Blo 1350994 2279819 := bstep (se 1 (by rfl) ⟨1709864, by rfl⟩ : syracuseStep 2279819 = 3419729) B3419729
theorem B3041675 : Blo 1350994 3041675 := bstep (se 1 (by rfl) ⟨2281256, by rfl⟩ : syracuseStep 3041675 = 4562513) B4562513
theorem B5130641 : Blo 1350994 5130641 := bstep (se 2 (by rfl) ⟨1923990, by rfl⟩ : syracuseStep 5130641 = 3847981) B3847981
theorem B3041729 : Blo 1350994 3041729 := bstep (se 2 (by rfl) ⟨1140648, by rfl⟩ : syracuseStep 3041729 = 2281297) B2281297
theorem B11545037 : Blo 1350994 11545037 := bstep (se 3 (by rfl) ⟨2164694, by rfl⟩ : syracuseStep 11545037 = 4329389) B4329389
theorem B2566657 : Blo 1350994 2566657 := bstep (se 2 (by rfl) ⟨962496, by rfl⟩ : syracuseStep 2566657 = 1924993) B1924993
theorem B2279947 : Blo 1350994 2279947 := bstep (se 1 (by rfl) ⟨1709960, by rfl⟩ : syracuseStep 2279947 = 3419921) B3419921
theorem B8227403 : Blo 1350994 8227403 := bstep (se 1 (by rfl) ⟨6170552, by rfl⟩ : syracuseStep 8227403 = 12341105) B12341105
theorem B2165335 : Blo 1350994 2165335 := bstep (se 1 (by rfl) ⟨1624001, by rfl⟩ : syracuseStep 2165335 = 3248003) B3248003
theorem B6253145 : Blo 1350994 6253145 := bstep (se 2 (by rfl) ⟨2344929, by rfl⟩ : syracuseStep 6253145 = 4689859) B4689859
theorem B6498967 : Blo 1350994 6498967 := bstep (se 1 (by rfl) ⟨4874225, by rfl⟩ : syracuseStep 6498967 = 9748451) B9748451
theorem B2280089 : Blo 1350994 2280089 := bstep (se 2 (by rfl) ⟨855033, by rfl⟩ : syracuseStep 2280089 = 1710067) B1710067
theorem B3041945 : Blo 1350994 3041945 := bstep (se 2 (by rfl) ⟨1140729, by rfl⟩ : syracuseStep 3041945 = 2281459) B2281459
theorem B3042035 : Blo 1350994 3042035 := bstep (se 1 (by rfl) ⟨2281526, by rfl⟩ : syracuseStep 3042035 = 4563053) B4563053
theorem B3042071 : Blo 1350994 3042071 := bstep (se 1 (by rfl) ⟨2281553, by rfl⟩ : syracuseStep 3042071 = 4563107) B4563107
theorem B2280217 : Blo 1350994 2280217 := bstep (se 2 (by rfl) ⟨855081, by rfl⟩ : syracuseStep 2280217 = 1710163) B1710163
theorem B32877377 : Blo 1350994 32877377 := bstep (se 2 (by rfl) ⟨12329016, by rfl⟩ : syracuseStep 32877377 = 24658033) B24658033
theorem B5131097 : Blo 1350994 5131097 := bstep (se 2 (by rfl) ⟨1924161, by rfl⟩ : syracuseStep 5131097 = 3848323) B3848323
theorem B2165707 : Blo 1350994 2165707 := bstep (se 1 (by rfl) ⟨1624280, by rfl⟩ : syracuseStep 2165707 = 3248561) B3248561
theorem B3042251 : Blo 1350994 3042251 := bstep (se 1 (by rfl) ⟨2281688, by rfl⟩ : syracuseStep 3042251 = 4563377) B4563377
theorem B3042305 : Blo 1350994 3042305 := bstep (se 2 (by rfl) ⟨1140864, by rfl⟩ : syracuseStep 3042305 = 2281729) B2281729
theorem B5778449 : Blo 1350994 5778449 := bstep (se 2 (by rfl) ⟨2166918, by rfl⟩ : syracuseStep 5778449 = 4333837) B4333837
theorem B5131309 : Blo 1350994 5131309 := bstep (se 3 (by rfl) ⟨962120, by rfl⟩ : syracuseStep 5131309 = 1924241) B1924241
theorem B2026571 : Blo 1350994 2026571 := bstep (se 1 (by rfl) ⟨1519928, by rfl⟩ : syracuseStep 2026571 = 3039857) B3039857
theorem B9743435 : Blo 1350994 9743435 := bstep (se 1 (by rfl) ⟨7307576, by rfl⟩ : syracuseStep 9743435 = 14615153) B14615153
theorem B2026583 : Blo 1350994 2026583 := bstep (se 1 (by rfl) ⟨1519937, by rfl⟩ : syracuseStep 2026583 = 3039875) B3039875
theorem B1977433 : Blo 1350994 1977433 := bstep (se 2 (by rfl) ⟨741537, by rfl⟩ : syracuseStep 1977433 = 1483075) B1483075
theorem B2026649 : Blo 1350994 2026649 := bstep (se 2 (by rfl) ⟨759993, by rfl⟩ : syracuseStep 2026649 = 1519987) B1519987
theorem B2567371 : Blo 1350994 2567371 := bstep (se 1 (by rfl) ⟨1925528, by rfl⟩ : syracuseStep 2567371 = 3851057) B3851057
theorem B3042521 : Blo 1350994 3042521 := bstep (se 2 (by rfl) ⟨1140945, by rfl⟩ : syracuseStep 3042521 = 2281891) B2281891
theorem B4869341 : Blo 1350994 4869341 := bstep (se 3 (by rfl) ⟨913001, by rfl⟩ : syracuseStep 4869341 = 1826003) B1826003
theorem B2026763 : Blo 1350994 2026763 := bstep (se 1 (by rfl) ⟨1520072, by rfl⟩ : syracuseStep 2026763 = 3040145) B3040145
theorem B1371403 : Blo 1350994 1371403 := bstep (se 1 (by rfl) ⟨1028552, by rfl⟩ : syracuseStep 1371403 = 2057105) B2057105
theorem B2026775 : Blo 1350994 2026775 := bstep (se 1 (by rfl) ⟨1520081, by rfl⟩ : syracuseStep 2026775 = 3040163) B3040163
theorem B2567447 : Blo 1350994 2567447 := bstep (se 1 (by rfl) ⟨1925585, by rfl⟩ : syracuseStep 2567447 = 3851171) B3851171
theorem B3042611 : Blo 1350994 3042611 := bstep (se 1 (by rfl) ⟨2281958, by rfl⟩ : syracuseStep 3042611 = 4563917) B4563917
theorem B2886977 : Blo 1350994 2886977 := bstep (se 2 (by rfl) ⟨1082616, by rfl⟩ : syracuseStep 2886977 = 2165233) B2165233
theorem B4566347 : Blo 1350994 4566347 := bstep (se 1 (by rfl) ⟨3424760, by rfl⟩ : syracuseStep 4566347 = 6849521) B6849521
theorem B2280791 : Blo 1350994 2280791 := bstep (se 1 (by rfl) ⟨1710593, by rfl⟩ : syracuseStep 2280791 = 3421187) B3421187
theorem B3042647 : Blo 1350994 3042647 := bstep (se 1 (by rfl) ⟨2281985, by rfl⟩ : syracuseStep 3042647 = 4563971) B4563971
theorem B2026841 : Blo 1350994 2026841 := bstep (se 2 (by rfl) ⟨760065, by rfl⟩ : syracuseStep 2026841 = 1520131) B1520131
theorem B5131613 : Blo 1350994 5131613 := bstep (se 3 (by rfl) ⟨962177, by rfl⟩ : syracuseStep 5131613 = 1924355) B1924355
theorem B2739595 : Blo 1350994 2739595 := bstep (se 1 (by rfl) ⟨2054696, by rfl⟩ : syracuseStep 2739595 = 4109393) B4109393
theorem B20811185 : Blo 1350994 20811185 := bstep (se 2 (by rfl) ⟨7804194, by rfl⟩ : syracuseStep 20811185 = 15608389) B15608389
theorem B2026955 : Blo 1350994 2026955 := bstep (se 1 (by rfl) ⟨1520216, by rfl⟩ : syracuseStep 2026955 = 3040433) B3040433
theorem B2026967 : Blo 1350994 2026967 := bstep (se 1 (by rfl) ⟨1520225, by rfl⟩ : syracuseStep 2026967 = 3040451) B3040451
theorem B2280919 : Blo 1350994 2280919 := bstep (se 1 (by rfl) ⟨1710689, by rfl⟩ : syracuseStep 2280919 = 3421379) B3421379
theorem B3042827 : Blo 1350994 3042827 := bstep (se 1 (by rfl) ⟨2282120, by rfl⟩ : syracuseStep 3042827 = 4564241) B4564241
theorem B3706391 : Blo 1350994 3706391 := bstep (se 1 (by rfl) ⟨2779793, by rfl⟩ : syracuseStep 3706391 = 5559587) B5559587
theorem B2027033 : Blo 1350994 2027033 := bstep (se 2 (by rfl) ⟨760137, by rfl⟩ : syracuseStep 2027033 = 1520275) B1520275
theorem B7695917 : Blo 1350994 7695917 := bstep (se 3 (by rfl) ⟨1442984, by rfl⟩ : syracuseStep 7695917 = 2885969) B2885969
theorem B3042881 : Blo 1350994 3042881 := bstep (se 2 (by rfl) ⟨1141080, by rfl⟩ : syracuseStep 3042881 = 2282161) B2282161
theorem B2027147 : Blo 1350994 2027147 := bstep (se 1 (by rfl) ⟨1520360, by rfl⟩ : syracuseStep 2027147 = 3040721) B3040721
theorem B2027159 : Blo 1350994 2027159 := bstep (se 1 (by rfl) ⟨1520369, by rfl⟩ : syracuseStep 2027159 = 3040739) B3040739
theorem B2887319 : Blo 1350994 2887319 := bstep (se 1 (by rfl) ⟨2165489, by rfl⟩ : syracuseStep 2887319 = 4330979) B4330979
theorem B49360589 : Blo 1350994 49360589 := bstep (se 3 (by rfl) ⟨9255110, by rfl⟩ : syracuseStep 49360589 = 18510221) B18510221
theorem B2027225 : Blo 1350994 2027225 := bstep (se 2 (by rfl) ⟨760209, by rfl⟩ : syracuseStep 2027225 = 1520419) B1520419
theorem B3043097 : Blo 1350994 3043097 := bstep (se 2 (by rfl) ⟨1141161, by rfl⟩ : syracuseStep 3043097 = 2282323) B2282323
theorem B49475393 : Blo 1350994 49475393 := bstep (se 2 (by rfl) ⟨18553272, by rfl⟩ : syracuseStep 49475393 = 37106545) B37106545
theorem B5771083 : Blo 1350994 5771083 := bstep (se 1 (by rfl) ⟨4328312, by rfl⟩ : syracuseStep 5771083 = 8656625) B8656625
theorem B2027339 : Blo 1350994 2027339 := bstep (se 1 (by rfl) ⟨1520504, by rfl⟩ : syracuseStep 2027339 = 3041009) B3041009
theorem B2027351 : Blo 1350994 2027351 := bstep (se 1 (by rfl) ⟨1520513, by rfl⟩ : syracuseStep 2027351 = 3041027) B3041027
theorem B2166617 : Blo 1350994 2166617 := bstep (se 2 (by rfl) ⟨812481, by rfl⟩ : syracuseStep 2166617 = 1624963) B1624963
theorem B9252701 : Blo 1350994 9252701 := bstep (se 3 (by rfl) ⟨1734881, by rfl⟩ : syracuseStep 9252701 = 3469763) B3469763
theorem B3043187 : Blo 1350994 3043187 := bstep (se 1 (by rfl) ⟨2282390, by rfl⟩ : syracuseStep 3043187 = 4564781) B4564781
theorem B10407811 : Blo 1350994 10407811 := bstep (se 1 (by rfl) ⟨7805858, by rfl⟩ : syracuseStep 10407811 = 15611717) B15611717
theorem B6164369 : Blo 1350994 6164369 := bstep (se 2 (by rfl) ⟨2311638, by rfl⟩ : syracuseStep 6164369 = 4623277) B4623277
theorem B3043223 : Blo 1350994 3043223 := bstep (se 1 (by rfl) ⟨2282417, by rfl⟩ : syracuseStep 3043223 = 4564835) B4564835
theorem B2027417 : Blo 1350994 2027417 := bstep (se 2 (by rfl) ⟨760281, by rfl⟩ : syracuseStep 2027417 = 1520563) B1520563
theorem B3420083 : Blo 1350994 3420083 := bstep (se 1 (by rfl) ⟨2565062, by rfl⟩ : syracuseStep 3420083 = 5130125) B5130125
theorem B2568115 : Blo 1350994 2568115 := bstep (se 1 (by rfl) ⟨1926086, by rfl⟩ : syracuseStep 2568115 = 3852173) B3852173
theorem B2166745 : Blo 1350994 2166745 := bstep (se 2 (by rfl) ⟨812529, by rfl⟩ : syracuseStep 2166745 = 1625059) B1625059
theorem B2027531 : Blo 1350994 2027531 := bstep (se 1 (by rfl) ⟨1520648, by rfl⟩ : syracuseStep 2027531 = 3041297) B3041297
theorem B2027543 : Blo 1350994 2027543 := bstep (se 1 (by rfl) ⟨1520657, by rfl⟩ : syracuseStep 2027543 = 3041315) B3041315
theorem B2281547 : Blo 1350994 2281547 := bstep (se 1 (by rfl) ⟨1711160, by rfl⟩ : syracuseStep 2281547 = 3422321) B3422321
theorem B3043403 : Blo 1350994 3043403 := bstep (se 1 (by rfl) ⟨2282552, by rfl⟩ : syracuseStep 3043403 = 4565105) B4565105
theorem B2027609 : Blo 1350994 2027609 := bstep (se 2 (by rfl) ⟨760353, by rfl⟩ : syracuseStep 2027609 = 1520707) B1520707
theorem B5771357 : Blo 1350994 5771357 := bstep (se 3 (by rfl) ⟨1082129, by rfl⟩ : syracuseStep 5771357 = 2164259) B2164259
theorem B3043457 : Blo 1350994 3043457 := bstep (se 2 (by rfl) ⟨1141296, by rfl⟩ : syracuseStep 3043457 = 2282593) B2282593
theorem B2568343 : Blo 1350994 2568343 := bstep (se 1 (by rfl) ⟨1926257, by rfl⟩ : syracuseStep 2568343 = 3852515) B3852515
theorem B2027723 : Blo 1350994 2027723 := bstep (se 1 (by rfl) ⟨1520792, by rfl⟩ : syracuseStep 2027723 = 3041585) B3041585
theorem B2281675 : Blo 1350994 2281675 := bstep (se 1 (by rfl) ⟨1711256, by rfl⟩ : syracuseStep 2281675 = 3422513) B3422513
theorem B2887883 : Blo 1350994 2887883 := bstep (se 1 (by rfl) ⟨2165912, by rfl⟩ : syracuseStep 2887883 = 4331825) B4331825
theorem B2027735 : Blo 1350994 2027735 := bstep (se 1 (by rfl) ⟨1520801, by rfl⟩ : syracuseStep 2027735 = 3041603) B3041603
theorem B3420377 : Blo 1350994 3420377 := bstep (se 2 (by rfl) ⟨1282641, by rfl⟩ : syracuseStep 3420377 = 2565283) B2565283
theorem B2568449 : Blo 1350994 2568449 := bstep (se 2 (by rfl) ⟨963168, by rfl⟩ : syracuseStep 2568449 = 1926337) B1926337
theorem B2027801 : Blo 1350994 2027801 := bstep (se 2 (by rfl) ⟨760425, by rfl⟩ : syracuseStep 2027801 = 1520851) B1520851
theorem B1519915 : Blo 1350994 1519915 := bstep (se 1 (by rfl) ⟨1139936, by rfl⟩ : syracuseStep 1519915 = 2279873) B2279873
theorem B2281817 : Blo 1350994 2281817 := bstep (se 2 (by rfl) ⟨855681, by rfl⟩ : syracuseStep 2281817 = 1711363) B1711363
theorem B3043673 : Blo 1350994 3043673 := bstep (se 2 (by rfl) ⟨1141377, by rfl⟩ : syracuseStep 3043673 = 2282755) B2282755
theorem B12341605 : Blo 1350994 12341605 := bstep (se 4 (by rfl) ⟨1157025, by rfl⟩ : syracuseStep 12341605 = 2314051) B2314051
theorem B2027915 : Blo 1350994 2027915 := bstep (se 1 (by rfl) ⟨1520936, by rfl⟩ : syracuseStep 2027915 = 3041873) B3041873
theorem B1520023 : Blo 1350994 1520023 := bstep (se 1 (by rfl) ⟨1140017, by rfl⟩ : syracuseStep 1520023 = 2280035) B2280035
theorem B2027927 : Blo 1350994 2027927 := bstep (se 1 (by rfl) ⟨1520945, by rfl⟩ : syracuseStep 2027927 = 3041891) B3041891
theorem B6844823 : Blo 1350994 6844823 := bstep (se 1 (by rfl) ⟨5133617, by rfl⟩ : syracuseStep 6844823 = 10267235) B10267235
theorem B7704983 : Blo 1350994 7704983 := bstep (se 1 (by rfl) ⟨5778737, by rfl⟩ : syracuseStep 7704983 = 11557475) B11557475
theorem B5771699 : Blo 1350994 5771699 := bstep (se 1 (by rfl) ⟨4328774, by rfl⟩ : syracuseStep 5771699 = 8657549) B8657549
theorem B3043763 : Blo 1350994 3043763 := bstep (se 1 (by rfl) ⟨2282822, by rfl⟩ : syracuseStep 3043763 = 4565645) B4565645
theorem B3043799 : Blo 1350994 3043799 := bstep (se 1 (by rfl) ⟨2282849, by rfl⟩ : syracuseStep 3043799 = 4565699) B4565699
theorem B2027993 : Blo 1350994 2027993 := bstep (se 2 (by rfl) ⟨760497, by rfl⟩ : syracuseStep 2027993 = 1520995) B1520995
theorem B2281945 : Blo 1350994 2281945 := bstep (se 2 (by rfl) ⟨855729, by rfl⟩ : syracuseStep 2281945 = 1711459) B1711459
theorem B8663597 : Blo 1350994 8663597 := bstep (se 3 (by rfl) ⟨1624424, by rfl⟩ : syracuseStep 8663597 = 3248849) B3248849
theorem B1520203 : Blo 1350994 1520203 := bstep (se 1 (by rfl) ⟨1140152, by rfl⟩ : syracuseStep 1520203 = 2280305) B2280305
theorem B2028107 : Blo 1350994 2028107 := bstep (se 1 (by rfl) ⟨1521080, by rfl⟩ : syracuseStep 2028107 = 3042161) B3042161
theorem B2028119 : Blo 1350994 2028119 := bstep (se 1 (by rfl) ⟨1521089, by rfl⟩ : syracuseStep 2028119 = 3042179) B3042179
theorem B3043979 : Blo 1350994 3043979 := bstep (se 1 (by rfl) ⟨2282984, by rfl⟩ : syracuseStep 3043979 = 4565969) B4565969
theorem B2028185 : Blo 1350994 2028185 := bstep (se 2 (by rfl) ⟨760569, by rfl⟩ : syracuseStep 2028185 = 1521139) B1521139
theorem B1520311 : Blo 1350994 1520311 := bstep (se 1 (by rfl) ⟨1140233, by rfl⟩ : syracuseStep 1520311 = 2280467) B2280467
theorem B3044033 : Blo 1350994 3044033 := bstep (se 2 (by rfl) ⟨1141512, by rfl⟩ : syracuseStep 3044033 = 2283025) B2283025
theorem B24048389 : Blo 1350994 24048389 := bstep (se 4 (by rfl) ⟨2254536, by rfl⟩ : syracuseStep 24048389 = 4509073) B4509073
theorem B2028299 : Blo 1350994 2028299 := bstep (se 1 (by rfl) ⟨1521224, by rfl⟩ : syracuseStep 2028299 = 3042449) B3042449
theorem B2028311 : Blo 1350994 2028311 := bstep (se 1 (by rfl) ⟨1521233, by rfl⟩ : syracuseStep 2028311 = 3042467) B3042467
theorem B2888473 : Blo 1350994 2888473 := bstep (se 2 (by rfl) ⟨1083177, by rfl⟩ : syracuseStep 2888473 = 2166355) B2166355
theorem B4559705 : Blo 1350994 4559705 := bstep (se 2 (by rfl) ⟨1709889, by rfl⟩ : syracuseStep 4559705 = 3419779) B3419779
theorem B2028377 : Blo 1350994 2028377 := bstep (se 2 (by rfl) ⟨760641, by rfl⟩ : syracuseStep 2028377 = 1521283) B1521283
theorem B1520491 : Blo 1350994 1520491 := bstep (se 1 (by rfl) ⟨1140368, by rfl⟩ : syracuseStep 1520491 = 2280737) B2280737
theorem B2028491 : Blo 1350994 2028491 := bstep (se 1 (by rfl) ⟨1521368, by rfl⟩ : syracuseStep 2028491 = 3042737) B3042737
theorem B1520599 : Blo 1350994 1520599 := bstep (se 1 (by rfl) ⟨1140449, by rfl⟩ : syracuseStep 1520599 = 2280899) B2280899
theorem B2503639 : Blo 1350994 2503639 := bstep (se 1 (by rfl) ⟨1877729, by rfl⟩ : syracuseStep 2503639 = 3755459) B3755459
theorem B2028503 : Blo 1350994 2028503 := bstep (se 1 (by rfl) ⟨1521377, by rfl⟩ : syracuseStep 2028503 = 3042755) B3042755
theorem B2741249 : Blo 1350994 2741249 := bstep (se 2 (by rfl) ⟨1027968, by rfl⟩ : syracuseStep 2741249 = 2055937) B2055937
theorem B2282519 : Blo 1350994 2282519 := bstep (se 1 (by rfl) ⟨1711889, by rfl⟩ : syracuseStep 2282519 = 3423779) B3423779
theorem B2028569 : Blo 1350994 2028569 := bstep (se 2 (by rfl) ⟨760713, by rfl⟩ : syracuseStep 2028569 = 1521427) B1521427
theorem B1520779 : Blo 1350994 1520779 := bstep (se 1 (by rfl) ⟨1140584, by rfl⟩ : syracuseStep 1520779 = 2281169) B2281169
theorem B2028683 : Blo 1350994 2028683 := bstep (se 1 (by rfl) ⟨1521512, by rfl⟩ : syracuseStep 2028683 = 3043025) B3043025
theorem B2028695 : Blo 1350994 2028695 := bstep (se 1 (by rfl) ⟨1521521, by rfl⟩ : syracuseStep 2028695 = 3043043) B3043043
theorem B2282647 : Blo 1350994 2282647 := bstep (se 1 (by rfl) ⟨1711985, by rfl⟩ : syracuseStep 2282647 = 3423971) B3423971
theorem B6165677 : Blo 1350994 6165677 := bstep (se 3 (by rfl) ⟨1156064, by rfl⟩ : syracuseStep 6165677 = 2312129) B2312129
theorem B2028761 : Blo 1350994 2028761 := bstep (se 2 (by rfl) ⟨760785, by rfl⟩ : syracuseStep 2028761 = 1521571) B1521571
theorem B1520887 : Blo 1350994 1520887 := bstep (se 1 (by rfl) ⟨1140665, by rfl⟩ : syracuseStep 1520887 = 2281331) B2281331
theorem B2028875 : Blo 1350994 2028875 := bstep (se 1 (by rfl) ⟨1521656, by rfl⟩ : syracuseStep 2028875 = 3043313) B3043313
theorem B2028887 : Blo 1350994 2028887 := bstep (se 1 (by rfl) ⟨1521665, by rfl⟩ : syracuseStep 2028887 = 3043331) B3043331
theorem B2028953 : Blo 1350994 2028953 := bstep (se 2 (by rfl) ⟨760857, by rfl⟩ : syracuseStep 2028953 = 1521715) B1521715
theorem B1521067 : Blo 1350994 1521067 := bstep (se 1 (by rfl) ⟨1140800, by rfl⟩ : syracuseStep 1521067 = 2281601) B2281601
theorem B2029067 : Blo 1350994 2029067 := bstep (se 1 (by rfl) ⟨1521800, by rfl⟩ : syracuseStep 2029067 = 3043601) B3043601
theorem B12998161 : Blo 1350994 12998161 := bstep (se 2 (by rfl) ⟨4874310, by rfl⟩ : syracuseStep 12998161 = 9748621) B9748621
theorem B4560407 : Blo 1350994 4560407 := bstep (se 1 (by rfl) ⟨3420305, by rfl⟩ : syracuseStep 4560407 = 6840611) B6840611
theorem B1521175 : Blo 1350994 1521175 := bstep (se 1 (by rfl) ⟨1140881, by rfl⟩ : syracuseStep 1521175 = 2281763) B2281763
theorem B2029079 : Blo 1350994 2029079 := bstep (se 1 (by rfl) ⟨1521809, by rfl⟩ : syracuseStep 2029079 = 3043619) B3043619
theorem B3249715 : Blo 1350994 3249715 := bstep (se 1 (by rfl) ⟨2437286, by rfl⟩ : syracuseStep 3249715 = 4874573) B4874573
theorem B2029145 : Blo 1350994 2029145 := bstep (se 2 (by rfl) ⟨760929, by rfl⟩ : syracuseStep 2029145 = 1521859) B1521859
theorem B15406685 : Blo 1350994 15406685 := bstep (se 3 (by rfl) ⟨2888753, by rfl⟩ : syracuseStep 15406685 = 5777507) B5777507
theorem B1521355 : Blo 1350994 1521355 := bstep (se 1 (by rfl) ⟨1141016, by rfl⟩ : syracuseStep 1521355 = 2282033) B2282033
theorem B2029259 : Blo 1350994 2029259 := bstep (se 1 (by rfl) ⟨1521944, by rfl⟩ : syracuseStep 2029259 = 3043889) B3043889
theorem B2029271 : Blo 1350994 2029271 := bstep (se 1 (by rfl) ⟨1521953, by rfl⟩ : syracuseStep 2029271 = 3043907) B3043907
theorem B2029337 : Blo 1350994 2029337 := bstep (se 2 (by rfl) ⟨761001, by rfl⟩ : syracuseStep 2029337 = 1522003) B1522003
theorem B2889523 : Blo 1350994 2889523 := bstep (se 1 (by rfl) ⟨2167142, by rfl⟩ : syracuseStep 2889523 = 4334285) B4334285
theorem B1521463 : Blo 1350994 1521463 := bstep (se 1 (by rfl) ⟨1141097, by rfl⟩ : syracuseStep 1521463 = 2282195) B2282195
theorem B3422027 : Blo 1350994 3422027 := bstep (se 1 (by rfl) ⟨2566520, by rfl⟩ : syracuseStep 3422027 = 5133041) B5133041
theorem B5134211 : Blo 1350994 5134211 := bstep (se 1 (by rfl) ⟨3850658, by rfl⟩ : syracuseStep 5134211 = 7701317) B7701317
theorem B2029451 : Blo 1350994 2029451 := bstep (se 1 (by rfl) ⟨1522088, by rfl⟩ : syracuseStep 2029451 = 3044177) B3044177
theorem B5134225 : Blo 1350994 5134225 := bstep (se 2 (by rfl) ⟨1925334, by rfl⟩ : syracuseStep 5134225 = 3850669) B3850669
theorem B2029463 : Blo 1350994 2029463 := bstep (se 1 (by rfl) ⟨1522097, by rfl⟩ : syracuseStep 2029463 = 3044195) B3044195
theorem B5478347 : Blo 1350994 5478347 := bstep (se 1 (by rfl) ⟨4108760, by rfl⟩ : syracuseStep 5478347 = 8217521) B8217521
theorem B21936089 : Blo 1350994 21936089 := bstep (se 2 (by rfl) ⟨8226033, by rfl⟩ : syracuseStep 21936089 = 16452067) B16452067
theorem B1521643 : Blo 1350994 1521643 := bstep (se 1 (by rfl) ⟨1141232, by rfl⟩ : syracuseStep 1521643 = 2282465) B2282465
theorem B4560947 : Blo 1350994 4560947 := bstep (se 1 (by rfl) ⟨3420710, by rfl⟩ : syracuseStep 4560947 = 6841421) B6841421
theorem B1521751 : Blo 1350994 1521751 := bstep (se 1 (by rfl) ⟨1141313, by rfl⟩ : syracuseStep 1521751 = 2282627) B2282627
theorem B5134529 : Blo 1350994 5134529 := bstep (se 2 (by rfl) ⟨1925448, by rfl⟩ : syracuseStep 5134529 = 3850897) B3850897
theorem B19478789 : Blo 1350994 19478789 := bstep (se 4 (by rfl) ⟨1826136, by rfl⟩ : syracuseStep 19478789 = 3652273) B3652273
theorem B1521931 : Blo 1350994 1521931 := bstep (se 1 (by rfl) ⟨1141448, by rfl⟩ : syracuseStep 1521931 = 2282897) B2282897
theorem B3651863 : Blo 1350994 3651863 := bstep (se 1 (by rfl) ⟨2738897, by rfl⟩ : syracuseStep 3651863 = 5477795) B5477795
theorem B4561217 : Blo 1350994 4561217 := bstep (se 2 (by rfl) ⟨1710456, by rfl⟩ : syracuseStep 4561217 = 3420913) B3420913
theorem B3651929 : Blo 1350994 3651929 := bstep (se 2 (by rfl) ⟨1369473, by rfl⟩ : syracuseStep 3651929 = 2738947) B2738947
theorem B1522039 : Blo 1350994 1522039 := bstep (se 1 (by rfl) ⟨1141529, by rfl⟩ : syracuseStep 1522039 = 2283059) B2283059
theorem B48085397 : Blo 1350994 48085397 := bstep (se 6 (by rfl) ⟨1127001, by rfl⟩ : syracuseStep 48085397 = 2254003) B2254003
theorem B1710487 : Blo 1350994 1710487 := bstep (se 1 (by rfl) ⟨1282865, by rfl⟩ : syracuseStep 1710487 = 2565731) B2565731
theorem B5478929 : Blo 1350994 5478929 := bstep (se 2 (by rfl) ⟨2054598, by rfl⟩ : syracuseStep 5478929 = 4109197) B4109197
theorem B6937105 : Blo 1350994 6937105 := bstep (se 2 (by rfl) ⟨2601414, by rfl⟩ : syracuseStep 6937105 = 5202829) B5202829
theorem B4872727 : Blo 1350994 4872727 := bstep (se 1 (by rfl) ⟨3654545, by rfl⟩ : syracuseStep 4872727 = 7309091) B7309091
theorem B4332055 : Blo 1350994 4332055 := bstep (se 1 (by rfl) ⟨3249041, by rfl⟩ : syracuseStep 4332055 = 6498083) B6498083
theorem B3250763 : Blo 1350994 3250763 := bstep (se 1 (by rfl) ⟨2438072, by rfl⟩ : syracuseStep 3250763 = 4876145) B4876145
theorem B3422999 : Blo 1350994 3422999 := bstep (se 1 (by rfl) ⟨2567249, by rfl⟩ : syracuseStep 3422999 = 5134499) B5134499
theorem B5774125 : Blo 1350994 5774125 := bstep (se 3 (by rfl) ⟨1082648, by rfl⟩ : syracuseStep 5774125 = 2165297) B2165297
theorem B23116589 : Blo 1350994 23116589 := bstep (se 3 (by rfl) ⟨4334360, by rfl⟩ : syracuseStep 23116589 = 8668721) B8668721
theorem B4561757 : Blo 1350994 4561757 := bstep (se 3 (by rfl) ⟨855329, by rfl⟩ : syracuseStep 4561757 = 1710659) B1710659
theorem B5135197 : Blo 1350994 5135197 := bstep (se 3 (by rfl) ⟨962849, by rfl⟩ : syracuseStep 5135197 = 1925699) B1925699
theorem B6167447 : Blo 1350994 6167447 := bstep (se 1 (by rfl) ⟨4625585, by rfl⟩ : syracuseStep 6167447 = 9251171) B9251171
theorem B3652697 : Blo 1350994 3652697 := bstep (se 2 (by rfl) ⟨1369761, by rfl⟩ : syracuseStep 3652697 = 2739523) B2739523
theorem B11549789 : Blo 1350994 11549789 := bstep (se 3 (by rfl) ⟨2165585, by rfl⟩ : syracuseStep 11549789 = 4331171) B4331171
theorem B7699607 : Blo 1350994 7699607 := bstep (se 1 (by rfl) ⟨5774705, by rfl⟩ : syracuseStep 7699607 = 11549411) B11549411
theorem B1711307 : Blo 1350994 1711307 := bstep (se 1 (by rfl) ⟨1283480, by rfl⟩ : syracuseStep 1711307 = 2566961) B2566961
theorem B1350999 : Blo 1350994 1350999 := bstep (se 1 (by rfl) ⟨1013249, by rfl⟩ : syracuseStep 1350999 = 2026499) B2026499
theorem B3849565 : Blo 1350994 3849565 := bstep (se 3 (by rfl) ⟨721793, by rfl⟩ : syracuseStep 3849565 = 1443587) B1443587
theorem B1351019 : Blo 1350994 1351019 := bstep (se 1 (by rfl) ⟨1013264, by rfl⟩ : syracuseStep 1351019 = 2026529) B2026529
theorem B1351031 : Blo 1350994 1351031 := bstep (se 1 (by rfl) ⟨1013273, by rfl⟩ : syracuseStep 1351031 = 2026547) B2026547
theorem B1351051 : Blo 1350994 1351051 := bstep (se 1 (by rfl) ⟨1013288, by rfl⟩ : syracuseStep 1351051 = 2026577) B2026577
theorem B5479825 : Blo 1350994 5479825 := bstep (se 2 (by rfl) ⟨2054934, by rfl⟩ : syracuseStep 5479825 = 4109869) B4109869
theorem B1351063 : Blo 1350994 1351063 := bstep (se 1 (by rfl) ⟨1013297, by rfl⟩ : syracuseStep 1351063 = 2026595) B2026595
theorem B1351083 : Blo 1350994 1351083 := bstep (se 1 (by rfl) ⟨1013312, by rfl⟩ : syracuseStep 1351083 = 2026625) B2026625
theorem B3423667 : Blo 1350994 3423667 := bstep (se 1 (by rfl) ⟨2567750, by rfl⟩ : syracuseStep 3423667 = 5135501) B5135501
theorem B1351095 : Blo 1350994 1351095 := bstep (se 1 (by rfl) ⟨1013321, by rfl⟩ : syracuseStep 1351095 = 2026643) B2026643
theorem B1351115 : Blo 1350994 1351115 := bstep (se 1 (by rfl) ⟨1013336, by rfl⟩ : syracuseStep 1351115 = 2026673) B2026673
theorem B1924555 : Blo 1350994 1924555 := bstep (se 1 (by rfl) ⟨1443416, by rfl⟩ : syracuseStep 1924555 = 2886833) B2886833
theorem B1351127 : Blo 1350994 1351127 := bstep (se 1 (by rfl) ⟨1013345, by rfl⟩ : syracuseStep 1351127 = 2026691) B2026691
theorem B1351147 : Blo 1350994 1351147 := bstep (se 1 (by rfl) ⟨1013360, by rfl⟩ : syracuseStep 1351147 = 2026721) B2026721
theorem B1351159 : Blo 1350994 1351159 := bstep (se 1 (by rfl) ⟨1013369, by rfl⟩ : syracuseStep 1351159 = 2026739) B2026739
theorem B1351179 : Blo 1350994 1351179 := bstep (se 1 (by rfl) ⟨1013384, by rfl⟩ : syracuseStep 1351179 = 2026769) B2026769
theorem B1351191 : Blo 1350994 1351191 := bstep (se 1 (by rfl) ⟨1013393, by rfl⟩ : syracuseStep 1351191 = 2026787) B2026787
theorem B6250007 : Blo 1350994 6250007 := bstep (se 1 (by rfl) ⟨4687505, by rfl⟩ : syracuseStep 6250007 = 9375011) B9375011
theorem B1351211 : Blo 1350994 1351211 := bstep (se 1 (by rfl) ⟨1013408, by rfl⟩ : syracuseStep 1351211 = 2026817) B2026817
theorem B1351223 : Blo 1350994 1351223 := bstep (se 1 (by rfl) ⟨1013417, by rfl⟩ : syracuseStep 1351223 = 2026835) B2026835
theorem B3423809 : Blo 1350994 3423809 := bstep (se 2 (by rfl) ⟨1283928, by rfl⟩ : syracuseStep 3423809 = 2567857) B2567857
theorem B1351243 : Blo 1350994 1351243 := bstep (se 1 (by rfl) ⟨1013432, by rfl⟩ : syracuseStep 1351243 = 2026865) B2026865
theorem B1351255 : Blo 1350994 1351255 := bstep (se 1 (by rfl) ⟨1013441, by rfl⟩ : syracuseStep 1351255 = 2026883) B2026883
theorem B1351275 : Blo 1350994 1351275 := bstep (se 1 (by rfl) ⟨1013456, by rfl⟩ : syracuseStep 1351275 = 2026913) B2026913
theorem B1351287 : Blo 1350994 1351287 := bstep (se 1 (by rfl) ⟨1013465, by rfl⟩ : syracuseStep 1351287 = 2026931) B2026931
theorem B1351307 : Blo 1350994 1351307 := bstep (se 1 (by rfl) ⟨1013480, by rfl⟩ : syracuseStep 1351307 = 2026961) B2026961
theorem B1351319 : Blo 1350994 1351319 := bstep (se 1 (by rfl) ⟨1013489, by rfl⟩ : syracuseStep 1351319 = 2026979) B2026979
theorem B1351339 : Blo 1350994 1351339 := bstep (se 1 (by rfl) ⟨1013504, by rfl⟩ : syracuseStep 1351339 = 2027009) B2027009
theorem B1351351 : Blo 1350994 1351351 := bstep (se 1 (by rfl) ⟨1013513, by rfl⟩ : syracuseStep 1351351 = 2027027) B2027027
theorem B1351371 : Blo 1350994 1351371 := bstep (se 1 (by rfl) ⟨1013528, by rfl⟩ : syracuseStep 1351371 = 2027057) B2027057
theorem B1351383 : Blo 1350994 1351383 := bstep (se 1 (by rfl) ⟨1013537, by rfl⟩ : syracuseStep 1351383 = 2027075) B2027075
theorem B7306969 : Blo 1350994 7306969 := bstep (se 2 (by rfl) ⟨2740113, by rfl⟩ : syracuseStep 7306969 = 5480227) B5480227
theorem B1351403 : Blo 1350994 1351403 := bstep (se 1 (by rfl) ⟨1013552, by rfl⟩ : syracuseStep 1351403 = 2027105) B2027105
theorem B1351415 : Blo 1350994 1351415 := bstep (se 1 (by rfl) ⟨1013561, by rfl⟩ : syracuseStep 1351415 = 2027123) B2027123
theorem B1351435 : Blo 1350994 1351435 := bstep (se 1 (by rfl) ⟨1013576, by rfl⟩ : syracuseStep 1351435 = 2027153) B2027153
theorem B1351447 : Blo 1350994 1351447 := bstep (se 1 (by rfl) ⟨1013585, by rfl⟩ : syracuseStep 1351447 = 2027171) B2027171
theorem B3653399 : Blo 1350994 3653399 := bstep (se 1 (by rfl) ⟨2740049, by rfl⟩ : syracuseStep 3653399 = 5480099) B5480099
theorem B1351467 : Blo 1350994 1351467 := bstep (se 1 (by rfl) ⟨1013600, by rfl⟩ : syracuseStep 1351467 = 2027201) B2027201
theorem B1351479 : Blo 1350994 1351479 := bstep (se 1 (by rfl) ⟨1013609, by rfl⟩ : syracuseStep 1351479 = 2027219) B2027219
theorem B1351499 : Blo 1350994 1351499 := bstep (se 1 (by rfl) ⟨1013624, by rfl⟩ : syracuseStep 1351499 = 2027249) B2027249
theorem B1351511 : Blo 1350994 1351511 := bstep (se 1 (by rfl) ⟨1013633, by rfl⟩ : syracuseStep 1351511 = 2027267) B2027267
theorem B1351531 : Blo 1350994 1351531 := bstep (se 1 (by rfl) ⟨1013648, by rfl⟩ : syracuseStep 1351531 = 2027297) B2027297
theorem B1351543 : Blo 1350994 1351543 := bstep (se 1 (by rfl) ⟨1013657, by rfl⟩ : syracuseStep 1351543 = 2027315) B2027315
theorem B6848387 : Blo 1350994 6848387 := bstep (se 1 (by rfl) ⟨5136290, by rfl⟩ : syracuseStep 6848387 = 10272581) B10272581
theorem B1351563 : Blo 1350994 1351563 := bstep (se 1 (by rfl) ⟨1013672, by rfl⟩ : syracuseStep 1351563 = 2027345) B2027345
theorem B1712011 : Blo 1350994 1712011 := bstep (se 1 (by rfl) ⟨1284008, by rfl⟩ : syracuseStep 1712011 = 2568017) B2568017
theorem B1351575 : Blo 1350994 1351575 := bstep (se 1 (by rfl) ⟨1013681, by rfl⟩ : syracuseStep 1351575 = 2027363) B2027363
theorem B1351595 : Blo 1350994 1351595 := bstep (se 1 (by rfl) ⟨1013696, by rfl⟩ : syracuseStep 1351595 = 2027393) B2027393
theorem B1351607 : Blo 1350994 1351607 := bstep (se 1 (by rfl) ⟨1013705, by rfl⟩ : syracuseStep 1351607 = 2027411) B2027411
theorem B1351627 : Blo 1350994 1351627 := bstep (se 1 (by rfl) ⟨1013720, by rfl⟩ : syracuseStep 1351627 = 2027441) B2027441
theorem B4562891 : Blo 1350994 4562891 := bstep (se 1 (by rfl) ⟨3422168, by rfl⟩ : syracuseStep 4562891 = 6844337) B6844337
theorem B1351639 : Blo 1350994 1351639 := bstep (se 1 (by rfl) ⟨1013729, by rfl⟩ : syracuseStep 1351639 = 2027459) B2027459
theorem B1351659 : Blo 1350994 1351659 := bstep (se 1 (by rfl) ⟨1013744, by rfl⟩ : syracuseStep 1351659 = 2027489) B2027489
theorem B1351671 : Blo 1350994 1351671 := bstep (se 1 (by rfl) ⟨1013753, by rfl⟩ : syracuseStep 1351671 = 2027507) B2027507
theorem B1351687 : Blo 1350994 1351687 := bstep (se 1 (by rfl) ⟨1013765, by rfl⟩ : syracuseStep 1351687 = 2027531) B2027531
theorem B1351695 : Blo 1350994 1351695 := bstep (se 1 (by rfl) ⟨1013771, by rfl⟩ : syracuseStep 1351695 = 2027543) B2027543
theorem B1351739 : Blo 1350994 1351739 := bstep (se 1 (by rfl) ⟨1013804, by rfl⟩ : syracuseStep 1351739 = 2027609) B2027609
theorem B3424315 : Blo 1350994 3424315 := bstep (se 1 (by rfl) ⟨2568236, by rfl⟩ : syracuseStep 3424315 = 5136473) B5136473
theorem B1351815 : Blo 1350994 1351815 := bstep (se 1 (by rfl) ⟨1013861, by rfl⟩ : syracuseStep 1351815 = 2027723) B2027723
theorem B1925255 : Blo 1350994 1925255 := bstep (se 1 (by rfl) ⟨1443941, by rfl⟩ : syracuseStep 1925255 = 2887883) B2887883
theorem B1351823 : Blo 1350994 1351823 := bstep (se 1 (by rfl) ⟨1013867, by rfl⟩ : syracuseStep 1351823 = 2027735) B2027735
theorem B1351867 : Blo 1350994 1351867 := bstep (se 1 (by rfl) ⟨1013900, by rfl⟩ : syracuseStep 1351867 = 2027801) B2027801
theorem B3424457 : Blo 1350994 3424457 := bstep (se 2 (by rfl) ⟨1284171, by rfl⟩ : syracuseStep 3424457 = 2568343) B2568343
theorem B5136641 : Blo 1350994 5136641 := bstep (se 2 (by rfl) ⟨1926240, by rfl⟩ : syracuseStep 5136641 = 3852481) B3852481
theorem B1351943 : Blo 1350994 1351943 := bstep (se 1 (by rfl) ⟨1013957, by rfl⟩ : syracuseStep 1351943 = 2027915) B2027915
theorem B1351951 : Blo 1350994 1351951 := bstep (se 1 (by rfl) ⟨1013963, by rfl⟩ : syracuseStep 1351951 = 2027927) B2027927
theorem B4563215 : Blo 1350994 4563215 := bstep (se 1 (by rfl) ⟨3422411, by rfl⟩ : syracuseStep 4563215 = 6844823) B6844823
theorem B5136655 : Blo 1350994 5136655 := bstep (se 1 (by rfl) ⟨3852491, by rfl⟩ : syracuseStep 5136655 = 7704983) B7704983
theorem B1351995 : Blo 1350994 1351995 := bstep (se 1 (by rfl) ⟨1013996, by rfl⟩ : syracuseStep 1351995 = 2027993) B2027993
theorem B5775731 : Blo 1350994 5775731 := bstep (se 1 (by rfl) ⟨4331798, by rfl⟩ : syracuseStep 5775731 = 8663597) B8663597
theorem B1352071 : Blo 1350994 1352071 := bstep (se 1 (by rfl) ⟨1014053, by rfl⟩ : syracuseStep 1352071 = 2028107) B2028107
theorem B1352079 : Blo 1350994 1352079 := bstep (se 1 (by rfl) ⟨1014059, by rfl⟩ : syracuseStep 1352079 = 2028119) B2028119
theorem B1352123 : Blo 1350994 1352123 := bstep (se 1 (by rfl) ⟨1014092, by rfl⟩ : syracuseStep 1352123 = 2028185) B2028185
theorem B16441805 : Blo 1350994 16441805 := bstep (se 3 (by rfl) ⟨3082838, by rfl⟩ : syracuseStep 16441805 = 6165677) B6165677
theorem B16032259 : Blo 1350994 16032259 := bstep (se 1 (by rfl) ⟨12024194, by rfl⟩ : syracuseStep 16032259 = 24048389) B24048389
theorem B1352199 : Blo 1350994 1352199 := bstep (se 1 (by rfl) ⟨1014149, by rfl⟩ : syracuseStep 1352199 = 2028299) B2028299
theorem B6849035 : Blo 1350994 6849035 := bstep (se 1 (by rfl) ⟨5136776, by rfl⟩ : syracuseStep 6849035 = 10273553) B10273553
theorem B1352207 : Blo 1350994 1352207 := bstep (se 1 (by rfl) ⟨1014155, by rfl⟩ : syracuseStep 1352207 = 2028311) B2028311
theorem B4563485 : Blo 1350994 4563485 := bstep (se 3 (by rfl) ⟨855653, by rfl⟩ : syracuseStep 4563485 = 1711307) B1711307
theorem B3039803 : Blo 1350994 3039803 := bstep (se 1 (by rfl) ⟨2279852, by rfl⟩ : syracuseStep 3039803 = 4559705) B4559705
theorem B1352251 : Blo 1350994 1352251 := bstep (se 1 (by rfl) ⟨1014188, by rfl⟩ : syracuseStep 1352251 = 2028377) B2028377
theorem B1352327 : Blo 1350994 1352327 := bstep (se 1 (by rfl) ⟨1014245, by rfl⟩ : syracuseStep 1352327 = 2028491) B2028491
theorem B1352335 : Blo 1350994 1352335 := bstep (se 1 (by rfl) ⟨1014251, by rfl⟩ : syracuseStep 1352335 = 2028503) B2028503
theorem B6849197 : Blo 1350994 6849197 := bstep (se 3 (by rfl) ⟨1284224, by rfl⟩ : syracuseStep 6849197 = 2568449) B2568449
theorem B3039929 : Blo 1350994 3039929 := bstep (se 2 (by rfl) ⟨1139973, by rfl⟩ : syracuseStep 3039929 = 2279947) B2279947
theorem B1352379 : Blo 1350994 1352379 := bstep (se 1 (by rfl) ⟨1014284, by rfl⟩ : syracuseStep 1352379 = 2028569) B2028569
theorem B9249473 : Blo 1350994 9249473 := bstep (se 2 (by rfl) ⟨3468552, by rfl⟩ : syracuseStep 9249473 = 6937105) B6937105
theorem B6496969 : Blo 1350994 6496969 := bstep (se 2 (by rfl) ⟨2436363, by rfl⟩ : syracuseStep 6496969 = 4872727) B4872727
theorem B5776073 : Blo 1350994 5776073 := bstep (se 2 (by rfl) ⟨2166027, by rfl⟩ : syracuseStep 5776073 = 4332055) B4332055
theorem B1352455 : Blo 1350994 1352455 := bstep (se 1 (by rfl) ⟨1014341, by rfl⟩ : syracuseStep 1352455 = 2028683) B2028683
theorem B3851023 : Blo 1350994 3851023 := bstep (se 1 (by rfl) ⟨2888267, by rfl⟩ : syracuseStep 3851023 = 5776535) B5776535
theorem B1352463 : Blo 1350994 1352463 := bstep (se 1 (by rfl) ⟨1014347, by rfl⟩ : syracuseStep 1352463 = 2028695) B2028695
theorem B3703595 : Blo 1350994 3703595 := bstep (se 1 (by rfl) ⟨2777696, by rfl⟩ : syracuseStep 3703595 = 5555393) B5555393
theorem B1352507 : Blo 1350994 1352507 := bstep (se 1 (by rfl) ⟨1014380, by rfl⟩ : syracuseStep 1352507 = 2028761) B2028761
theorem B1352583 : Blo 1350994 1352583 := bstep (se 1 (by rfl) ⟨1014437, by rfl⟩ : syracuseStep 1352583 = 2028875) B2028875
theorem B1352591 : Blo 1350994 1352591 := bstep (se 1 (by rfl) ⟨1014443, by rfl⟩ : syracuseStep 1352591 = 2028887) B2028887
theorem B1352635 : Blo 1350994 1352635 := bstep (se 1 (by rfl) ⟨1014476, by rfl⟩ : syracuseStep 1352635 = 2028953) B2028953
theorem B1352711 : Blo 1350994 1352711 := bstep (se 1 (by rfl) ⟨1014533, by rfl⟩ : syracuseStep 1352711 = 2029067) B2029067
theorem B3040271 : Blo 1350994 3040271 := bstep (se 1 (by rfl) ⟨2280203, by rfl⟩ : syracuseStep 3040271 = 4560407) B4560407
theorem B1352719 : Blo 1350994 1352719 := bstep (se 1 (by rfl) ⟨1014539, by rfl⟩ : syracuseStep 1352719 = 2029079) B2029079
theorem B3040289 : Blo 1350994 3040289 := bstep (se 2 (by rfl) ⟨1140108, by rfl⟩ : syracuseStep 3040289 = 2280217) B2280217
theorem B3851297 : Blo 1350994 3851297 := bstep (se 2 (by rfl) ⟨1444236, by rfl⟩ : syracuseStep 3851297 = 2888473) B2888473
theorem B1352763 : Blo 1350994 1352763 := bstep (se 1 (by rfl) ⟨1014572, by rfl⟩ : syracuseStep 1352763 = 2029145) B2029145
theorem B1352839 : Blo 1350994 1352839 := bstep (se 1 (by rfl) ⟨1014629, by rfl⟩ : syracuseStep 1352839 = 2029259) B2029259
theorem B1352847 : Blo 1350994 1352847 := bstep (se 1 (by rfl) ⟨1014635, by rfl⟩ : syracuseStep 1352847 = 2029271) B2029271
theorem B1352891 : Blo 1350994 1352891 := bstep (se 1 (by rfl) ⟨1014668, by rfl⟩ : syracuseStep 1352891 = 2029337) B2029337
theorem B1352967 : Blo 1350994 1352967 := bstep (se 1 (by rfl) ⟨1014725, by rfl⟩ : syracuseStep 1352967 = 2029451) B2029451
theorem B1352975 : Blo 1350994 1352975 := bstep (se 1 (by rfl) ⟨1014731, by rfl⟩ : syracuseStep 1352975 = 2029463) B2029463
theorem B14624059 : Blo 1350994 14624059 := bstep (se 1 (by rfl) ⟨10968044, by rfl⟩ : syracuseStep 14624059 = 21936089) B21936089
theorem B3040631 : Blo 1350994 3040631 := bstep (se 1 (by rfl) ⟨2280473, by rfl⟩ : syracuseStep 3040631 = 4560947) B4560947
theorem B1443215 : Blo 1350994 1443215 := bstep (se 1 (by rfl) ⟨1082411, by rfl⟩ : syracuseStep 1443215 = 2164823) B2164823
theorem B6841745 : Blo 1350994 6841745 := bstep (se 2 (by rfl) ⟨2565654, by rfl⟩ : syracuseStep 6841745 = 5131309) B5131309
theorem B12985859 : Blo 1350994 12985859 := bstep (se 1 (by rfl) ⟨9739394, by rfl⟩ : syracuseStep 12985859 = 19478789) B19478789
theorem B3040811 : Blo 1350994 3040811 := bstep (se 1 (by rfl) ⟨2280608, by rfl⟩ : syracuseStep 3040811 = 4561217) B4561217
theorem B2434619 : Blo 1350994 2434619 := bstep (se 1 (by rfl) ⟨1825964, by rfl⟩ : syracuseStep 2434619 = 3651929) B3651929
theorem B32056931 : Blo 1350994 32056931 := bstep (se 1 (by rfl) ⟨24042698, by rfl⟩ : syracuseStep 32056931 = 48085397) B48085397
theorem B1828537 : Blo 1350994 1828537 := bstep (se 2 (by rfl) ⟨685701, by rfl⟩ : syracuseStep 1828537 = 1371403) B1371403
theorem B15411059 : Blo 1350994 15411059 := bstep (se 1 (by rfl) ⟨11558294, by rfl⟩ : syracuseStep 15411059 = 23116589) B23116589
theorem B3041171 : Blo 1350994 3041171 := bstep (se 1 (by rfl) ⟨2280878, by rfl⟩ : syracuseStep 3041171 = 4561757) B4561757
theorem B4564889 : Blo 1350994 4564889 := bstep (se 2 (by rfl) ⟨1711833, by rfl⟩ : syracuseStep 4564889 = 3423667) B3423667
theorem B2566073 : Blo 1350994 2566073 := bstep (se 2 (by rfl) ⟨962277, by rfl⟩ : syracuseStep 2566073 = 1924555) B1924555
theorem B3041225 : Blo 1350994 3041225 := bstep (se 2 (by rfl) ⟨1140459, by rfl⟩ : syracuseStep 3041225 = 2280919) B2280919
theorem B3852299 : Blo 1350994 3852299 := bstep (se 1 (by rfl) ⟨2889224, by rfl⟩ : syracuseStep 3852299 = 5778449) B5778449
theorem B2435131 : Blo 1350994 2435131 := bstep (se 1 (by rfl) ⟨1826348, by rfl⟩ : syracuseStep 2435131 = 3652697) B3652697
theorem B3246227 : Blo 1350994 3246227 := bstep (se 1 (by rfl) ⟨2434670, by rfl⟩ : syracuseStep 3246227 = 4869341) B4869341
theorem B9742625 : Blo 1350994 9742625 := bstep (se 2 (by rfl) ⟨3653484, by rfl⟩ : syracuseStep 9742625 = 7306969) B7306969
theorem B5130611 : Blo 1350994 5130611 := bstep (se 1 (by rfl) ⟨3847958, by rfl⟩ : syracuseStep 5130611 = 7695917) B7695917
theorem B3852697 : Blo 1350994 3852697 := bstep (se 2 (by rfl) ⟨1444761, by rfl⟩ : syracuseStep 3852697 = 2889523) B2889523
theorem B7694777 : Blo 1350994 7694777 := bstep (se 2 (by rfl) ⟨2885541, by rfl⟩ : syracuseStep 7694777 = 5771083) B5771083
theorem B2435599 : Blo 1350994 2435599 := bstep (se 1 (by rfl) ⟨1826699, by rfl⟩ : syracuseStep 2435599 = 3653399) B3653399
theorem B32983595 : Blo 1350994 32983595 := bstep (se 1 (by rfl) ⟨24737696, by rfl⟩ : syracuseStep 32983595 = 49475393) B49475393
theorem B1444411 : Blo 1350994 1444411 := bstep (se 1 (by rfl) ⟨1083308, by rfl⟩ : syracuseStep 1444411 = 2166617) B2166617
theorem B4565591 : Blo 1350994 4565591 := bstep (se 1 (by rfl) ⟨3424193, by rfl⟩ : syracuseStep 4565591 = 6848387) B6848387
theorem B2280055 : Blo 1350994 2280055 := bstep (se 1 (by rfl) ⟨1710041, by rfl⟩ : syracuseStep 2280055 = 3420083) B3420083
theorem B3041927 : Blo 1350994 3041927 := bstep (se 1 (by rfl) ⟨2281445, by rfl⟩ : syracuseStep 3041927 = 4562891) B4562891
theorem B7309997 : Blo 1350994 7309997 := bstep (se 3 (by rfl) ⟨1370624, by rfl⟩ : syracuseStep 7309997 = 2741249) B2741249
theorem B5778191 : Blo 1350994 5778191 := bstep (se 1 (by rfl) ⟨4333643, by rfl⟩ : syracuseStep 5778191 = 8667287) B8667287
theorem B2280251 : Blo 1350994 2280251 := bstep (se 1 (by rfl) ⟨1710188, by rfl⟩ : syracuseStep 2280251 = 3420377) B3420377
theorem B3042107 : Blo 1350994 3042107 := bstep (se 1 (by rfl) ⟨2281580, by rfl⟩ : syracuseStep 3042107 = 4563161) B4563161
theorem B6499217 : Blo 1350994 6499217 := bstep (se 2 (by rfl) ⟨2437206, by rfl⟩ : syracuseStep 6499217 = 4874413) B4874413
theorem B12331939 : Blo 1350994 12331939 := bstep (se 1 (by rfl) ⟨9248954, by rfl⟩ : syracuseStep 12331939 = 18497909) B18497909
theorem B3042233 : Blo 1350994 3042233 := bstep (se 2 (by rfl) ⟨1140837, by rfl⟩ : syracuseStep 3042233 = 2281675) B2281675
theorem B2026511 : Blo 1350994 2026511 := bstep (se 1 (by rfl) ⟨1519883, by rfl⟩ : syracuseStep 2026511 = 3039767) B3039767
theorem B2026553 : Blo 1350994 2026553 := bstep (se 2 (by rfl) ⟨759957, by rfl⟩ : syracuseStep 2026553 = 1519915) B1519915
theorem B2567227 : Blo 1350994 2567227 := bstep (se 1 (by rfl) ⟨1925420, by rfl⟩ : syracuseStep 2567227 = 3850841) B3850841
theorem B4566077 : Blo 1350994 4566077 := bstep (se 3 (by rfl) ⟨856139, by rfl⟩ : syracuseStep 4566077 = 1712279) B1712279
theorem B5778499 : Blo 1350994 5778499 := bstep (se 1 (by rfl) ⟨4333874, by rfl⟩ : syracuseStep 5778499 = 8667749) B8667749
theorem B10546309 : Blo 1350994 10546309 := bstep (se 4 (by rfl) ⟨988716, by rfl⟩ : syracuseStep 10546309 = 1977433) B1977433
theorem B2026631 : Blo 1350994 2026631 := bstep (se 1 (by rfl) ⟨1519973, by rfl⟩ : syracuseStep 2026631 = 3039947) B3039947
theorem B2026667 : Blo 1350994 2026667 := bstep (se 1 (by rfl) ⟨1520000, by rfl⟩ : syracuseStep 2026667 = 3040001) B3040001
theorem B2026697 : Blo 1350994 2026697 := bstep (se 2 (by rfl) ⟨760011, by rfl⟩ : syracuseStep 2026697 = 1520023) B1520023
theorem B2280649 : Blo 1350994 2280649 := bstep (se 2 (by rfl) ⟨855243, by rfl⟩ : syracuseStep 2280649 = 1710487) B1710487
theorem B3042575 : Blo 1350994 3042575 := bstep (se 1 (by rfl) ⟨2281931, by rfl⟩ : syracuseStep 3042575 = 4563863) B4563863
theorem B3042593 : Blo 1350994 3042593 := bstep (se 2 (by rfl) ⟨1140972, by rfl⟩ : syracuseStep 3042593 = 2281945) B2281945
theorem B2026811 : Blo 1350994 2026811 := bstep (se 1 (by rfl) ⟨1520108, by rfl⟩ : syracuseStep 2026811 = 3040217) B3040217
theorem B2026871 : Blo 1350994 2026871 := bstep (se 1 (by rfl) ⟨1520153, by rfl⟩ : syracuseStep 2026871 = 3040307) B3040307
theorem B2026895 : Blo 1350994 2026895 := bstep (se 1 (by rfl) ⟨1520171, by rfl⟩ : syracuseStep 2026895 = 3040343) B3040343
theorem B2026937 : Blo 1350994 2026937 := bstep (se 2 (by rfl) ⟨760101, by rfl⟩ : syracuseStep 2026937 = 1520203) B1520203
theorem B6843851 : Blo 1350994 6843851 := bstep (se 1 (by rfl) ⟨5132888, by rfl⟩ : syracuseStep 6843851 = 10265777) B10265777
theorem B2027015 : Blo 1350994 2027015 := bstep (se 1 (by rfl) ⟨1520261, by rfl⟩ : syracuseStep 2027015 = 3040523) B3040523
theorem B2567713 : Blo 1350994 2567713 := bstep (se 2 (by rfl) ⟨962892, by rfl⟩ : syracuseStep 2567713 = 1925785) B1925785
theorem B2027051 : Blo 1350994 2027051 := bstep (se 1 (by rfl) ⟨1520288, by rfl⟩ : syracuseStep 2027051 = 3040577) B3040577
theorem B8662571 : Blo 1350994 8662571 := bstep (se 1 (by rfl) ⟨6496928, by rfl⟩ : syracuseStep 8662571 = 12993857) B12993857
theorem B2600507 : Blo 1350994 2600507 := bstep (se 1 (by rfl) ⟨1950380, by rfl⟩ : syracuseStep 2600507 = 3900761) B3900761
theorem B2027081 : Blo 1350994 2027081 := bstep (se 2 (by rfl) ⟨760155, by rfl⟩ : syracuseStep 2027081 = 1520311) B1520311
theorem B3042935 : Blo 1350994 3042935 := bstep (se 1 (by rfl) ⟨2282201, by rfl⟩ : syracuseStep 3042935 = 4564403) B4564403
theorem B2027195 : Blo 1350994 2027195 := bstep (se 1 (by rfl) ⟨1520396, by rfl⟩ : syracuseStep 2027195 = 3040793) B3040793
theorem B2027255 : Blo 1350994 2027255 := bstep (se 1 (by rfl) ⟨1520441, by rfl⟩ : syracuseStep 2027255 = 3040883) B3040883
theorem B2027279 : Blo 1350994 2027279 := bstep (se 1 (by rfl) ⟨1520459, by rfl⟩ : syracuseStep 2027279 = 3040919) B3040919
theorem B6844175 : Blo 1350994 6844175 := bstep (se 1 (by rfl) ⟨5133131, by rfl⟩ : syracuseStep 6844175 = 10266263) B10266263
theorem B3043115 : Blo 1350994 3043115 := bstep (se 1 (by rfl) ⟨2282336, by rfl⟩ : syracuseStep 3043115 = 4564673) B4564673
theorem B2027321 : Blo 1350994 2027321 := bstep (se 2 (by rfl) ⟨760245, by rfl⟩ : syracuseStep 2027321 = 1520491) B1520491
theorem B2436983 : Blo 1350994 2436983 := bstep (se 1 (by rfl) ⟨1827737, by rfl⟩ : syracuseStep 2436983 = 3655475) B3655475
theorem B5205875 : Blo 1350994 5205875 := bstep (se 1 (by rfl) ⟨3904406, by rfl⟩ : syracuseStep 5205875 = 7808813) B7808813
theorem B2027399 : Blo 1350994 2027399 := bstep (se 1 (by rfl) ⟨1520549, by rfl⟩ : syracuseStep 2027399 = 3041099) B3041099
theorem B2281351 : Blo 1350994 2281351 := bstep (se 1 (by rfl) ⟨1711013, by rfl⟩ : syracuseStep 2281351 = 3422027) B3422027
theorem B2027435 : Blo 1350994 2027435 := bstep (se 1 (by rfl) ⟨1520576, by rfl⟩ : syracuseStep 2027435 = 3041153) B3041153
theorem B2027465 : Blo 1350994 2027465 := bstep (se 2 (by rfl) ⟨760299, by rfl⟩ : syracuseStep 2027465 = 1520599) B1520599
theorem B3338185 : Blo 1350994 3338185 := bstep (se 2 (by rfl) ⟨1251819, by rfl⟩ : syracuseStep 3338185 = 2503639) B2503639
theorem B2027579 : Blo 1350994 2027579 := bstep (se 1 (by rfl) ⟨1520684, by rfl⟩ : syracuseStep 2027579 = 3041369) B3041369
theorem B2027639 : Blo 1350994 2027639 := bstep (se 1 (by rfl) ⟨1520729, by rfl⟩ : syracuseStep 2027639 = 3041459) B3041459
theorem B2027663 : Blo 1350994 2027663 := bstep (se 1 (by rfl) ⟨1520747, by rfl⟩ : syracuseStep 2027663 = 3041495) B3041495
theorem B3043475 : Blo 1350994 3043475 := bstep (se 1 (by rfl) ⟨2282606, by rfl⟩ : syracuseStep 3043475 = 4565213) B4565213
theorem B2027705 : Blo 1350994 2027705 := bstep (se 2 (by rfl) ⟨760389, by rfl⟩ : syracuseStep 2027705 = 1520779) B1520779
theorem B3043529 : Blo 1350994 3043529 := bstep (se 2 (by rfl) ⟨1141323, by rfl⟩ : syracuseStep 3043529 = 2282647) B2282647
theorem B1519879 : Blo 1350994 1519879 := bstep (se 1 (by rfl) ⟨1139909, by rfl⟩ : syracuseStep 1519879 = 2279819) B2279819
theorem B2027783 : Blo 1350994 2027783 := bstep (se 1 (by rfl) ⟨1520837, by rfl⟩ : syracuseStep 2027783 = 3041675) B3041675
theorem B3420427 : Blo 1350994 3420427 := bstep (se 1 (by rfl) ⟨2565320, by rfl⟩ : syracuseStep 3420427 = 5130641) B5130641
theorem B2027819 : Blo 1350994 2027819 := bstep (se 1 (by rfl) ⟨1520864, by rfl⟩ : syracuseStep 2027819 = 3041729) B3041729
theorem B7696691 : Blo 1350994 7696691 := bstep (se 1 (by rfl) ⟨5772518, by rfl⟩ : syracuseStep 7696691 = 11545037) B11545037
theorem B2027849 : Blo 1350994 2027849 := bstep (se 2 (by rfl) ⟨760443, by rfl⟩ : syracuseStep 2027849 = 1520887) B1520887
theorem B5484935 : Blo 1350994 5484935 := bstep (se 1 (by rfl) ⟨4113701, by rfl⟩ : syracuseStep 5484935 = 8227403) B8227403
theorem B2167175 : Blo 1350994 2167175 := bstep (se 1 (by rfl) ⟨1625381, by rfl⟩ : syracuseStep 2167175 = 3250763) B3250763
theorem B3420569 : Blo 1350994 3420569 := bstep (se 2 (by rfl) ⟨1282713, by rfl⟩ : syracuseStep 3420569 = 2565427) B2565427
theorem B1520059 : Blo 1350994 1520059 := bstep (se 1 (by rfl) ⟨1140044, by rfl⟩ : syracuseStep 1520059 = 2280089) B2280089
theorem B2027963 : Blo 1350994 2027963 := bstep (se 1 (by rfl) ⟨1520972, by rfl⟩ : syracuseStep 2027963 = 3041945) B3041945
theorem B5132753 : Blo 1350994 5132753 := bstep (se 2 (by rfl) ⟨1924782, by rfl⟩ : syracuseStep 5132753 = 3849565) B3849565
theorem B2028023 : Blo 1350994 2028023 := bstep (se 1 (by rfl) ⟨1521017, by rfl⟩ : syracuseStep 2028023 = 3042035) B3042035
theorem B2028047 : Blo 1350994 2028047 := bstep (se 1 (by rfl) ⟨1521035, by rfl⟩ : syracuseStep 2028047 = 3042071) B3042071
theorem B2281999 : Blo 1350994 2281999 := bstep (se 1 (by rfl) ⟨1711499, by rfl⟩ : syracuseStep 2281999 = 3422999) B3422999
theorem B21918251 : Blo 1350994 21918251 := bstep (se 1 (by rfl) ⟨16438688, by rfl⟩ : syracuseStep 21918251 = 32877377) B32877377
theorem B2028089 : Blo 1350994 2028089 := bstep (se 2 (by rfl) ⟨760533, by rfl⟩ : syracuseStep 2028089 = 1521067) B1521067
theorem B3420731 : Blo 1350994 3420731 := bstep (se 1 (by rfl) ⟨2565548, by rfl⟩ : syracuseStep 3420731 = 5131097) B5131097
theorem B2028167 : Blo 1350994 2028167 := bstep (se 1 (by rfl) ⟨1521125, by rfl⟩ : syracuseStep 2028167 = 3042251) B3042251
theorem B2028203 : Blo 1350994 2028203 := bstep (se 1 (by rfl) ⟨1521152, by rfl⟩ : syracuseStep 2028203 = 3042305) B3042305
theorem B17330881 : Blo 1350994 17330881 := bstep (se 2 (by rfl) ⟨6499080, by rfl⟩ : syracuseStep 17330881 = 12998161) B12998161
theorem B2028233 : Blo 1350994 2028233 := bstep (se 2 (by rfl) ⟨760587, by rfl⟩ : syracuseStep 2028233 = 1521175) B1521175
theorem B5133071 : Blo 1350994 5133071 := bstep (se 1 (by rfl) ⟨3849803, by rfl⟩ : syracuseStep 5133071 = 7699607) B7699607
theorem B2028347 : Blo 1350994 2028347 := bstep (se 1 (by rfl) ⟨1521260, by rfl⟩ : syracuseStep 2028347 = 3042521) B3042521
theorem B2028407 : Blo 1350994 2028407 := bstep (se 1 (by rfl) ⟨1521305, by rfl⟩ : syracuseStep 2028407 = 3042611) B3042611
theorem B3044231 : Blo 1350994 3044231 := bstep (se 1 (by rfl) ⟨2283173, by rfl⟩ : syracuseStep 3044231 = 4566347) B4566347
theorem B1520527 : Blo 1350994 1520527 := bstep (se 1 (by rfl) ⟨1140395, by rfl⟩ : syracuseStep 1520527 = 2280791) B2280791
theorem B2028431 : Blo 1350994 2028431 := bstep (se 1 (by rfl) ⟨1521323, by rfl⟩ : syracuseStep 2028431 = 3042647) B3042647
theorem B3421075 : Blo 1350994 3421075 := bstep (se 1 (by rfl) ⟨2565806, by rfl⟩ : syracuseStep 3421075 = 5131613) B5131613
theorem B2028473 : Blo 1350994 2028473 := bstep (se 2 (by rfl) ⟨760677, by rfl⟩ : syracuseStep 2028473 = 1521355) B1521355
theorem B13874123 : Blo 1350994 13874123 := bstep (se 1 (by rfl) ⟨10405592, by rfl⟩ : syracuseStep 13874123 = 20811185) B20811185
theorem B2028551 : Blo 1350994 2028551 := bstep (se 1 (by rfl) ⟨1521413, by rfl⟩ : syracuseStep 2028551 = 3042827) B3042827
theorem B4166671 : Blo 1350994 4166671 := bstep (se 1 (by rfl) ⟨3125003, by rfl⟩ : syracuseStep 4166671 = 6250007) B6250007
theorem B2470927 : Blo 1350994 2470927 := bstep (se 1 (by rfl) ⟨1853195, by rfl⟩ : syracuseStep 2470927 = 3706391) B3706391
theorem B3421217 : Blo 1350994 3421217 := bstep (se 2 (by rfl) ⟨1282956, by rfl⟩ : syracuseStep 3421217 = 2565913) B2565913
theorem B2028587 : Blo 1350994 2028587 := bstep (se 1 (by rfl) ⟨1521440, by rfl⟩ : syracuseStep 2028587 = 3042881) B3042881
theorem B2282539 : Blo 1350994 2282539 := bstep (se 1 (by rfl) ⟨1711904, by rfl⟩ : syracuseStep 2282539 = 3423809) B3423809
theorem B2028617 : Blo 1350994 2028617 := bstep (se 2 (by rfl) ⟨760731, by rfl⟩ : syracuseStep 2028617 = 1521463) B1521463
theorem B2282681 : Blo 1350994 2282681 := bstep (se 2 (by rfl) ⟨856005, by rfl⟩ : syracuseStep 2282681 = 1712011) B1712011
theorem B2028731 : Blo 1350994 2028731 := bstep (se 1 (by rfl) ⟨1521548, by rfl⟩ : syracuseStep 2028731 = 3043097) B3043097
theorem B6845633 : Blo 1350994 6845633 := bstep (se 2 (by rfl) ⟨2567112, by rfl⟩ : syracuseStep 6845633 = 5134225) B5134225
theorem B2028791 : Blo 1350994 2028791 := bstep (se 1 (by rfl) ⟨1521593, by rfl⟩ : syracuseStep 2028791 = 3043187) B3043187
theorem B4109579 : Blo 1350994 4109579 := bstep (se 1 (by rfl) ⟨3082184, by rfl⟩ : syracuseStep 4109579 = 6164369) B6164369
theorem B2028815 : Blo 1350994 2028815 := bstep (se 1 (by rfl) ⟨1521611, by rfl⟩ : syracuseStep 2028815 = 3043223) B3043223
theorem B2888993 : Blo 1350994 2888993 := bstep (se 2 (by rfl) ⟨1083372, by rfl⟩ : syracuseStep 2888993 = 2166745) B2166745
theorem B2028857 : Blo 1350994 2028857 := bstep (se 2 (by rfl) ⟨760821, by rfl⟩ : syracuseStep 2028857 = 1521643) B1521643
theorem B1521031 : Blo 1350994 1521031 := bstep (se 1 (by rfl) ⟨1140773, by rfl⟩ : syracuseStep 1521031 = 2281547) B2281547
theorem B2028935 : Blo 1350994 2028935 := bstep (se 1 (by rfl) ⟨1521701, by rfl⟩ : syracuseStep 2028935 = 3043403) B3043403
theorem B3847571 : Blo 1350994 3847571 := bstep (se 1 (by rfl) ⟨2885678, by rfl⟩ : syracuseStep 3847571 = 5771357) B5771357
theorem B2028971 : Blo 1350994 2028971 := bstep (se 1 (by rfl) ⟨1521728, by rfl⟩ : syracuseStep 2028971 = 3043457) B3043457
theorem B2029001 : Blo 1350994 2029001 := bstep (se 2 (by rfl) ⟨760875, by rfl⟩ : syracuseStep 2029001 = 1521751) B1521751
theorem B6493699 : Blo 1350994 6493699 := bstep (se 1 (by rfl) ⟨4870274, by rfl⟩ : syracuseStep 6493699 = 9740549) B9740549
theorem B1521211 : Blo 1350994 1521211 := bstep (se 1 (by rfl) ⟨1140908, by rfl⟩ : syracuseStep 1521211 = 2281817) B2281817
theorem B2029115 : Blo 1350994 2029115 := bstep (se 1 (by rfl) ⟨1521836, by rfl⟩ : syracuseStep 2029115 = 3043673) B3043673
theorem B3847799 : Blo 1350994 3847799 := bstep (se 1 (by rfl) ⟨2885849, by rfl⟩ : syracuseStep 3847799 = 5771699) B5771699
theorem B2029175 : Blo 1350994 2029175 := bstep (se 1 (by rfl) ⟨1521881, by rfl⟩ : syracuseStep 2029175 = 3043763) B3043763
theorem B2029199 : Blo 1350994 2029199 := bstep (se 1 (by rfl) ⟨1521899, by rfl⟩ : syracuseStep 2029199 = 3043799) B3043799
theorem B2029241 : Blo 1350994 2029241 := bstep (se 2 (by rfl) ⟨760965, by rfl⟩ : syracuseStep 2029241 = 1521931) B1521931
theorem B7698149 : Blo 1350994 7698149 := bstep (se 4 (by rfl) ⟨721701, by rfl⟩ : syracuseStep 7698149 = 1443403) B1443403
theorem B2029319 : Blo 1350994 2029319 := bstep (se 1 (by rfl) ⟨1521989, by rfl⟩ : syracuseStep 2029319 = 3043979) B3043979
theorem B11548453 : Blo 1350994 11548453 := bstep (se 4 (by rfl) ⟨1082667, by rfl⟩ : syracuseStep 11548453 = 2165335) B2165335
theorem B2029355 : Blo 1350994 2029355 := bstep (se 1 (by rfl) ⟨1522016, by rfl⟩ : syracuseStep 2029355 = 3044033) B3044033
theorem B16455473 : Blo 1350994 16455473 := bstep (se 2 (by rfl) ⟨6170802, by rfl⟩ : syracuseStep 16455473 = 12341605) B12341605
theorem B2029385 : Blo 1350994 2029385 := bstep (se 2 (by rfl) ⟨761019, by rfl⟩ : syracuseStep 2029385 = 1522039) B1522039
theorem B1710011 : Blo 1350994 1710011 := bstep (se 1 (by rfl) ⟨1282508, by rfl⟩ : syracuseStep 1710011 = 2565017) B2565017
theorem B3422209 : Blo 1350994 3422209 := bstep (se 2 (by rfl) ⟨1283328, by rfl⟩ : syracuseStep 3422209 = 2566657) B2566657
theorem B1521679 : Blo 1350994 1521679 := bstep (se 1 (by rfl) ⟨1141259, by rfl⟩ : syracuseStep 1521679 = 2282519) B2282519
theorem B9738301 : Blo 1350994 9738301 := bstep (se 3 (by rfl) ⟨1825931, by rfl⟩ : syracuseStep 9738301 = 3651863) B3651863
theorem B8665289 : Blo 1350994 8665289 := bstep (se 2 (by rfl) ⟨3249483, by rfl⟩ : syracuseStep 8665289 = 6498967) B6498967
theorem B5855503 : Blo 1350994 5855503 := bstep (se 1 (by rfl) ⟨4391627, by rfl⟩ : syracuseStep 5855503 = 8783255) B8783255
theorem B16439611 : Blo 1350994 16439611 := bstep (se 1 (by rfl) ⟨12329708, by rfl⟩ : syracuseStep 16439611 = 24659417) B24659417
theorem B7698833 : Blo 1350994 7698833 := bstep (se 2 (by rfl) ⟨2887062, by rfl⟩ : syracuseStep 7698833 = 5774125) B5774125
theorem B10271123 : Blo 1350994 10271123 := bstep (se 1 (by rfl) ⟨7703342, by rfl⟩ : syracuseStep 10271123 = 15406685) B15406685
theorem B5200337 : Blo 1350994 5200337 := bstep (se 2 (by rfl) ⟨1950126, by rfl⟩ : syracuseStep 5200337 = 3900253) B3900253
theorem B6846929 : Blo 1350994 6846929 := bstep (se 2 (by rfl) ⟨2567598, by rfl⟩ : syracuseStep 6846929 = 5135197) B5135197
theorem B13867523 : Blo 1350994 13867523 := bstep (se 1 (by rfl) ⟨10400642, by rfl⟩ : syracuseStep 13867523 = 20801285) B20801285
theorem B3422807 : Blo 1350994 3422807 := bstep (se 1 (by rfl) ⟨2567105, by rfl⟩ : syracuseStep 3422807 = 5134211) B5134211
theorem B3652231 : Blo 1350994 3652231 := bstep (se 1 (by rfl) ⟨2739173, by rfl⟩ : syracuseStep 3652231 = 5478347) B5478347
theorem B4111133 : Blo 1350994 4111133 := bstep (se 3 (by rfl) ⟨770837, by rfl⟩ : syracuseStep 4111133 = 1541675) B1541675
theorem B3423019 : Blo 1350994 3423019 := bstep (se 1 (by rfl) ⟨2567264, by rfl⟩ : syracuseStep 3423019 = 5134529) B5134529
theorem B10263347 : Blo 1350994 10263347 := bstep (se 1 (by rfl) ⟨7697510, by rfl⟩ : syracuseStep 10263347 = 15395021) B15395021
theorem B5856059 : Blo 1350994 5856059 := bstep (se 1 (by rfl) ⟨4392044, by rfl⟩ : syracuseStep 5856059 = 8784089) B8784089
theorem B1710983 : Blo 1350994 1710983 := bstep (se 1 (by rfl) ⟨1283237, by rfl⟩ : syracuseStep 1710983 = 2566475) B2566475
theorem B6167431 : Blo 1350994 6167431 := bstep (se 1 (by rfl) ⟨4625573, by rfl⟩ : syracuseStep 6167431 = 9251147) B9251147
theorem B4561811 : Blo 1350994 4561811 := bstep (se 1 (by rfl) ⟨3421358, by rfl⟩ : syracuseStep 4561811 = 6842717) B6842717
theorem B7412627 : Blo 1350994 7412627 := bstep (se 1 (by rfl) ⟨5559470, by rfl⟩ : syracuseStep 7412627 = 11118941) B11118941
theorem B3423161 : Blo 1350994 3423161 := bstep (se 2 (by rfl) ⟨1283685, by rfl⟩ : syracuseStep 3423161 = 2567371) B2567371
theorem B3652619 : Blo 1350994 3652619 := bstep (se 1 (by rfl) ⟨2739464, by rfl⟩ : syracuseStep 3652619 = 5478929) B5478929
theorem B4168763 : Blo 1350994 4168763 := bstep (se 1 (by rfl) ⟨3126572, by rfl⟩ : syracuseStep 4168763 = 6253145) B6253145
theorem B3652793 : Blo 1350994 3652793 := bstep (se 2 (by rfl) ⟨1369797, by rfl⟩ : syracuseStep 3652793 = 2739595) B2739595
theorem B2055353 : Blo 1350994 2055353 := bstep (se 2 (by rfl) ⟨770757, by rfl⟩ : syracuseStep 2055353 = 1541515) B1541515
theorem B7306433 : Blo 1350994 7306433 := bstep (se 2 (by rfl) ⟨2739912, by rfl⟩ : syracuseStep 7306433 = 5479825) B5479825
theorem B4111631 : Blo 1350994 4111631 := bstep (se 1 (by rfl) ⟨3083723, by rfl⟩ : syracuseStep 4111631 = 6167447) B6167447
theorem B1351047 : Blo 1350994 1351047 := bstep (se 1 (by rfl) ⟨1013285, by rfl⟩ : syracuseStep 1351047 = 2026571) B2026571
theorem B6495623 : Blo 1350994 6495623 := bstep (se 1 (by rfl) ⟨4871717, by rfl⟩ : syracuseStep 6495623 = 9743435) B9743435
theorem B1351055 : Blo 1350994 1351055 := bstep (se 1 (by rfl) ⟨1013291, by rfl⟩ : syracuseStep 1351055 = 2026583) B2026583
theorem B7699859 : Blo 1350994 7699859 := bstep (se 1 (by rfl) ⟨5774894, by rfl⟩ : syracuseStep 7699859 = 11549789) B11549789
theorem B4332953 : Blo 1350994 4332953 := bstep (se 2 (by rfl) ⟨1624857, by rfl⟩ : syracuseStep 4332953 = 3249715) B3249715
theorem B1351099 : Blo 1350994 1351099 := bstep (se 1 (by rfl) ⟨1013324, by rfl⟩ : syracuseStep 1351099 = 2026649) B2026649
theorem B1351175 : Blo 1350994 1351175 := bstep (se 1 (by rfl) ⟨1013381, by rfl⟩ : syracuseStep 1351175 = 2026763) B2026763
theorem B1351183 : Blo 1350994 1351183 := bstep (se 1 (by rfl) ⟨1013387, by rfl⟩ : syracuseStep 1351183 = 2026775) B2026775
theorem B1711631 : Blo 1350994 1711631 := bstep (se 1 (by rfl) ⟨1283723, by rfl⟩ : syracuseStep 1711631 = 2567447) B2567447
theorem B1924651 : Blo 1350994 1924651 := bstep (se 1 (by rfl) ⟨1443488, by rfl⟩ : syracuseStep 1924651 = 2886977) B2886977
theorem B1351227 : Blo 1350994 1351227 := bstep (se 1 (by rfl) ⟨1013420, by rfl⟩ : syracuseStep 1351227 = 2026841) B2026841
theorem B1351303 : Blo 1350994 1351303 := bstep (se 1 (by rfl) ⟨1013477, by rfl⟩ : syracuseStep 1351303 = 2026955) B2026955
theorem B1351311 : Blo 1350994 1351311 := bstep (se 1 (by rfl) ⟨1013483, by rfl⟩ : syracuseStep 1351311 = 2026967) B2026967
theorem B1351355 : Blo 1350994 1351355 := bstep (se 1 (by rfl) ⟨1013516, by rfl⟩ : syracuseStep 1351355 = 2027033) B2027033
theorem B11550437 : Blo 1350994 11550437 := bstep (se 4 (by rfl) ⟨1082853, by rfl⟩ : syracuseStep 11550437 = 2165707) B2165707
theorem B1351431 : Blo 1350994 1351431 := bstep (se 1 (by rfl) ⟨1013573, by rfl⟩ : syracuseStep 1351431 = 2027147) B2027147
theorem B1351439 : Blo 1350994 1351439 := bstep (se 1 (by rfl) ⟨1013579, by rfl⟩ : syracuseStep 1351439 = 2027159) B2027159
theorem B1924879 : Blo 1350994 1924879 := bstep (se 1 (by rfl) ⟨1443659, by rfl⟩ : syracuseStep 1924879 = 2887319) B2887319
theorem B32907059 : Blo 1350994 32907059 := bstep (se 1 (by rfl) ⟨24680294, by rfl⟩ : syracuseStep 32907059 = 49360589) B49360589
theorem B1351483 : Blo 1350994 1351483 := bstep (se 1 (by rfl) ⟨1013612, by rfl⟩ : syracuseStep 1351483 = 2027225) B2027225
theorem B13877081 : Blo 1350994 13877081 := bstep (se 2 (by rfl) ⟨5203905, by rfl⟩ : syracuseStep 13877081 = 10407811) B10407811
theorem B1351559 : Blo 1350994 1351559 := bstep (se 1 (by rfl) ⟨1013669, by rfl⟩ : syracuseStep 1351559 = 2027339) B2027339
theorem B1351567 : Blo 1350994 1351567 := bstep (se 1 (by rfl) ⟨1013675, by rfl⟩ : syracuseStep 1351567 = 2027351) B2027351
theorem B6168467 : Blo 1350994 6168467 := bstep (se 1 (by rfl) ⟨4626350, by rfl⟩ : syracuseStep 6168467 = 9252701) B9252701
theorem B3424153 : Blo 1350994 3424153 := bstep (se 2 (by rfl) ⟨1284057, by rfl⟩ : syracuseStep 3424153 = 2568115) B2568115
theorem B1351611 : Blo 1350994 1351611 := bstep (se 1 (by rfl) ⟨1013708, by rfl⟩ : syracuseStep 1351611 = 2027417) B2027417
theorem B4562945 : Blo 1350994 4562945 := bstep (se 2 (by rfl) ⟨1711104, by rfl⟩ : syracuseStep 4562945 = 3422209) B3422209
theorem B1351719 : Blo 1350994 1351719 := bstep (se 1 (by rfl) ⟨1013789, by rfl⟩ : syracuseStep 1351719 = 2027579) B2027579
theorem B1351759 : Blo 1350994 1351759 := bstep (se 1 (by rfl) ⟨1013819, by rfl⟩ : syracuseStep 1351759 = 2027639) B2027639
theorem B12984401 : Blo 1350994 12984401 := bstep (se 2 (by rfl) ⟨4869150, by rfl⟩ : syracuseStep 12984401 = 9738301) B9738301
theorem B1351775 : Blo 1350994 1351775 := bstep (se 1 (by rfl) ⟨1013831, by rfl⟩ : syracuseStep 1351775 = 2027663) B2027663
theorem B38961269 : Blo 1350994 38961269 := bstep (se 5 (by rfl) ⟨1826309, by rfl⟩ : syracuseStep 38961269 = 3652619) B3652619
theorem B1351803 : Blo 1350994 1351803 := bstep (se 1 (by rfl) ⟨1013852, by rfl⟩ : syracuseStep 1351803 = 2027705) B2027705
theorem B3424427 : Blo 1350994 3424427 := bstep (se 1 (by rfl) ⟨2568320, by rfl⟩ : syracuseStep 3424427 = 5136641) B5136641
theorem B1351855 : Blo 1350994 1351855 := bstep (se 1 (by rfl) ⟨1013891, by rfl⟩ : syracuseStep 1351855 = 2027783) B2027783
theorem B1351879 : Blo 1350994 1351879 := bstep (se 1 (by rfl) ⟨1013909, by rfl⟩ : syracuseStep 1351879 = 2027819) B2027819
theorem B1351899 : Blo 1350994 1351899 := bstep (se 1 (by rfl) ⟨1013924, by rfl⟩ : syracuseStep 1351899 = 2027849) B2027849
theorem B10264805 : Blo 1350994 10264805 := bstep (se 4 (by rfl) ⟨962325, by rfl⟩ : syracuseStep 10264805 = 1924651) B1924651
theorem B3850487 : Blo 1350994 3850487 := bstep (se 1 (by rfl) ⟨2887865, by rfl⟩ : syracuseStep 3850487 = 5775731) B5775731
theorem B1351975 : Blo 1350994 1351975 := bstep (se 1 (by rfl) ⟨1013981, by rfl⟩ : syracuseStep 1351975 = 2027963) B2027963
theorem B10961203 : Blo 1350994 10961203 := bstep (se 1 (by rfl) ⟨8220902, by rfl⟩ : syracuseStep 10961203 = 16441805) B16441805
theorem B1352015 : Blo 1350994 1352015 := bstep (se 1 (by rfl) ⟨1014011, by rfl⟩ : syracuseStep 1352015 = 2028023) B2028023
theorem B1352031 : Blo 1350994 1352031 := bstep (se 1 (by rfl) ⟨1014023, by rfl⟩ : syracuseStep 1352031 = 2028047) B2028047
theorem B7807337 : Blo 1350994 7807337 := bstep (se 2 (by rfl) ⟨2927751, by rfl⟩ : syracuseStep 7807337 = 5855503) B5855503
theorem B6848873 : Blo 1350994 6848873 := bstep (se 2 (by rfl) ⟨2568327, by rfl⟩ : syracuseStep 6848873 = 5136655) B5136655
theorem B1352059 : Blo 1350994 1352059 := bstep (se 1 (by rfl) ⟨1014044, by rfl⟩ : syracuseStep 1352059 = 2028089) B2028089
theorem B1352111 : Blo 1350994 1352111 := bstep (se 1 (by rfl) ⟨1014083, by rfl⟩ : syracuseStep 1352111 = 2028167) B2028167
theorem B1352135 : Blo 1350994 1352135 := bstep (se 1 (by rfl) ⟨1014101, by rfl⟩ : syracuseStep 1352135 = 2028203) B2028203
theorem B1352155 : Blo 1350994 1352155 := bstep (se 1 (by rfl) ⟨1014116, by rfl⟩ : syracuseStep 1352155 = 2028233) B2028233
theorem B3850715 : Blo 1350994 3850715 := bstep (se 1 (by rfl) ⟨2888036, by rfl⟩ : syracuseStep 3850715 = 5776073) B5776073
theorem B5480941 : Blo 1350994 5480941 := bstep (se 3 (by rfl) ⟨1027676, by rfl⟩ : syracuseStep 5480941 = 2055353) B2055353
theorem B5136929 : Blo 1350994 5136929 := bstep (se 2 (by rfl) ⟨1926348, by rfl⟩ : syracuseStep 5136929 = 3852697) B3852697
theorem B1352231 : Blo 1350994 1352231 := bstep (se 1 (by rfl) ⟨1014173, by rfl⟩ : syracuseStep 1352231 = 2028347) B2028347
theorem B1352271 : Blo 1350994 1352271 := bstep (se 1 (by rfl) ⟨1014203, by rfl⟩ : syracuseStep 1352271 = 2028407) B2028407
theorem B1352287 : Blo 1350994 1352287 := bstep (se 1 (by rfl) ⟨1014215, by rfl⟩ : syracuseStep 1352287 = 2028431) B2028431
theorem B1352315 : Blo 1350994 1352315 := bstep (se 1 (by rfl) ⟨1014236, by rfl⟩ : syracuseStep 1352315 = 2028473) B2028473
theorem B1352367 : Blo 1350994 1352367 := bstep (se 1 (by rfl) ⟨1014275, by rfl⟩ : syracuseStep 1352367 = 2028551) B2028551
theorem B1352391 : Blo 1350994 1352391 := bstep (se 1 (by rfl) ⟨1014293, by rfl⟩ : syracuseStep 1352391 = 2028587) B2028587
theorem B1352411 : Blo 1350994 1352411 := bstep (se 1 (by rfl) ⟨1014308, by rfl⟩ : syracuseStep 1352411 = 2028617) B2028617
theorem B1352487 : Blo 1350994 1352487 := bstep (se 1 (by rfl) ⟨1014365, by rfl⟩ : syracuseStep 1352487 = 2028731) B2028731
theorem B4563755 : Blo 1350994 4563755 := bstep (se 1 (by rfl) ⟨3422816, by rfl⟩ : syracuseStep 4563755 = 6845633) B6845633
theorem B3040073 : Blo 1350994 3040073 := bstep (se 2 (by rfl) ⟨1140027, by rfl⟩ : syracuseStep 3040073 = 2280055) B2280055
theorem B1352527 : Blo 1350994 1352527 := bstep (se 1 (by rfl) ⟨1014395, by rfl⟩ : syracuseStep 1352527 = 2028791) B2028791
theorem B1352543 : Blo 1350994 1352543 := bstep (se 1 (by rfl) ⟨1014407, by rfl⟩ : syracuseStep 1352543 = 2028815) B2028815
theorem B1352571 : Blo 1350994 1352571 := bstep (se 1 (by rfl) ⟨1014428, by rfl⟩ : syracuseStep 1352571 = 2028857) B2028857
theorem B1352623 : Blo 1350994 1352623 := bstep (se 1 (by rfl) ⟨1014467, by rfl⟩ : syracuseStep 1352623 = 2028935) B2028935
theorem B2565047 : Blo 1350994 2565047 := bstep (se 1 (by rfl) ⟨1923785, by rfl⟩ : syracuseStep 2565047 = 3847571) B3847571
theorem B1352647 : Blo 1350994 1352647 := bstep (se 1 (by rfl) ⟨1014485, by rfl⟩ : syracuseStep 1352647 = 2028971) B2028971
theorem B1352667 : Blo 1350994 1352667 := bstep (se 1 (by rfl) ⟨1014500, by rfl⟩ : syracuseStep 1352667 = 2029001) B2029001
theorem B1623079 : Blo 1350994 1623079 := bstep (se 1 (by rfl) ⟨1217309, by rfl⟩ : syracuseStep 1623079 = 2434619) B2434619
theorem B1352743 : Blo 1350994 1352743 := bstep (se 1 (by rfl) ⟨1014557, by rfl⟩ : syracuseStep 1352743 = 2029115) B2029115
theorem B4564025 : Blo 1350994 4564025 := bstep (se 2 (by rfl) ⟨1711509, by rfl⟩ : syracuseStep 4564025 = 3423019) B3423019
theorem B2565199 : Blo 1350994 2565199 := bstep (se 1 (by rfl) ⟨1923899, by rfl⟩ : syracuseStep 2565199 = 3847799) B3847799
theorem B1352783 : Blo 1350994 1352783 := bstep (se 1 (by rfl) ⟨1014587, by rfl⟩ : syracuseStep 1352783 = 2029175) B2029175
theorem B1352799 : Blo 1350994 1352799 := bstep (se 1 (by rfl) ⟨1014599, by rfl⟩ : syracuseStep 1352799 = 2029199) B2029199
theorem B1352827 : Blo 1350994 1352827 := bstep (se 1 (by rfl) ⟨1014620, by rfl⟩ : syracuseStep 1352827 = 2029241) B2029241
theorem B1352879 : Blo 1350994 1352879 := bstep (se 1 (by rfl) ⟨1014659, by rfl⟩ : syracuseStep 1352879 = 2029319) B2029319
theorem B1352903 : Blo 1350994 1352903 := bstep (se 1 (by rfl) ⟨1014677, by rfl⟩ : syracuseStep 1352903 = 2029355) B2029355
theorem B10970315 : Blo 1350994 10970315 := bstep (se 1 (by rfl) ⟨8227736, by rfl⟩ : syracuseStep 10970315 = 16455473) B16455473
theorem B16442585 : Blo 1350994 16442585 := bstep (se 2 (by rfl) ⟨6165969, by rfl⟩ : syracuseStep 16442585 = 12331939) B12331939
theorem B1352923 : Blo 1350994 1352923 := bstep (se 1 (by rfl) ⟨1014692, by rfl⟩ : syracuseStep 1352923 = 2029385) B2029385
theorem B10274039 : Blo 1350994 10274039 := bstep (se 1 (by rfl) ⟨7705529, by rfl⟩ : syracuseStep 10274039 = 15411059) B15411059
theorem B34628957 : Blo 1350994 34628957 := bstep (se 3 (by rfl) ⟨6492929, by rfl⟩ : syracuseStep 34628957 = 12985859) B12985859
theorem B5555561 : Blo 1350994 5555561 := bstep (se 2 (by rfl) ⟨2083335, by rfl⟩ : syracuseStep 5555561 = 4166671) B4166671
theorem B3294569 : Blo 1350994 3294569 := bstep (se 2 (by rfl) ⟨1235463, by rfl⟩ : syracuseStep 3294569 = 2470927) B2470927
theorem B4564349 : Blo 1350994 4564349 := bstep (se 3 (by rfl) ⟨855815, by rfl⟩ : syracuseStep 4564349 = 1711631) B1711631
theorem B2164151 : Blo 1350994 2164151 := bstep (se 1 (by rfl) ⟨1623113, by rfl⟩ : syracuseStep 2164151 = 3246227) B3246227
theorem B5776859 : Blo 1350994 5776859 := bstep (se 1 (by rfl) ⟨4332644, by rfl⟩ : syracuseStep 5776859 = 8665289) B8665289
theorem B85485149 : Blo 1350994 85485149 := bstep (se 3 (by rfl) ⟨16028465, by rfl⟩ : syracuseStep 85485149 = 32056931) B32056931
theorem B3040865 : Blo 1350994 3040865 := bstep (se 2 (by rfl) ⟨1140324, by rfl⟩ : syracuseStep 3040865 = 2280649) B2280649
theorem B5129851 : Blo 1350994 5129851 := bstep (se 1 (by rfl) ⟨3847388, by rfl⟩ : syracuseStep 5129851 = 7694777) B7694777
theorem B3466891 : Blo 1350994 3466891 := bstep (se 1 (by rfl) ⟨2600168, by rfl⟩ : syracuseStep 3466891 = 5200337) B5200337
theorem B4564619 : Blo 1350994 4564619 := bstep (se 1 (by rfl) ⟨3423464, by rfl⟩ : syracuseStep 4564619 = 6846929) B6846929
theorem B21989063 : Blo 1350994 21989063 := bstep (se 1 (by rfl) ⟨16491797, by rfl⟩ : syracuseStep 21989063 = 32983595) B32983595
theorem B19498745 : Blo 1350994 19498745 := bstep (se 2 (by rfl) ⟨7312029, by rfl⟩ : syracuseStep 19498745 = 14624059) B14624059
theorem B3852127 : Blo 1350994 3852127 := bstep (se 1 (by rfl) ⟨2889095, by rfl⟩ : syracuseStep 3852127 = 5778191) B5778191
theorem B6842231 : Blo 1350994 6842231 := bstep (se 1 (by rfl) ⟨5131673, by rfl⟩ : syracuseStep 6842231 = 10263347) B10263347
theorem B3041207 : Blo 1350994 3041207 := bstep (se 1 (by rfl) ⟨2280905, by rfl⟩ : syracuseStep 3041207 = 4561811) B4561811
theorem B4941751 : Blo 1350994 4941751 := bstep (se 1 (by rfl) ⟨3706313, by rfl⟩ : syracuseStep 4941751 = 7412627) B7412627
theorem B2779175 : Blo 1350994 2779175 := bstep (se 1 (by rfl) ⟨2084381, by rfl⟩ : syracuseStep 2779175 = 4168763) B4168763
theorem B10963021 : Blo 1350994 10963021 := bstep (se 3 (by rfl) ⟨2055566, by rfl⟩ : syracuseStep 10963021 = 4111133) B4111133
theorem B2435195 : Blo 1350994 2435195 := bstep (se 1 (by rfl) ⟨1826396, by rfl⟩ : syracuseStep 2435195 = 3652793) B3652793
theorem B2566505 : Blo 1350994 2566505 := bstep (se 2 (by rfl) ⟨962439, by rfl⟩ : syracuseStep 2566505 = 1924879) B1924879
theorem B3041801 : Blo 1350994 3041801 := bstep (se 2 (by rfl) ⟨1140675, by rfl⟩ : syracuseStep 3041801 = 2281351) B2281351
theorem B36997661 : Blo 1350994 36997661 := bstep (se 3 (by rfl) ⟨6937061, by rfl⟩ : syracuseStep 36997661 = 13874123) B13874123
theorem B4565537 : Blo 1350994 4565537 := bstep (se 2 (by rfl) ⟨1712076, by rfl⟩ : syracuseStep 4565537 = 3424153) B3424153
theorem B9251387 : Blo 1350994 9251387 := bstep (se 1 (by rfl) ⟨6938540, by rfl⟩ : syracuseStep 9251387 = 13877081) B13877081
theorem B1624655 : Blo 1350994 1624655 := bstep (se 1 (by rfl) ⟨1218491, by rfl⟩ : syracuseStep 1624655 = 2436983) B2436983
theorem B4450913 : Blo 1350994 4450913 := bstep (se 2 (by rfl) ⟨1669092, by rfl⟩ : syracuseStep 4450913 = 3338185) B3338185
theorem B3246841 : Blo 1350994 3246841 := bstep (se 2 (by rfl) ⟨1217565, by rfl⟩ : syracuseStep 3246841 = 2435131) B2435131
theorem B4565753 : Blo 1350994 4565753 := bstep (se 2 (by rfl) ⟨1712157, by rfl⟩ : syracuseStep 4565753 = 3424315) B3424315
theorem B3042143 : Blo 1350994 3042143 := bstep (se 1 (by rfl) ⟨2281607, by rfl⟩ : syracuseStep 3042143 = 4563215) B4563215
theorem B5131127 : Blo 1350994 5131127 := bstep (se 1 (by rfl) ⟨3848345, by rfl⟩ : syracuseStep 5131127 = 7696691) B7696691
theorem B3656623 : Blo 1350994 3656623 := bstep (se 1 (by rfl) ⟨2742467, by rfl⟩ : syracuseStep 3656623 = 5484935) B5484935
theorem B2280379 : Blo 1350994 2280379 := bstep (se 1 (by rfl) ⟨1710284, by rfl⟩ : syracuseStep 2280379 = 3420569) B3420569
theorem B7703525 : Blo 1350994 7703525 := bstep (se 4 (by rfl) ⟨722205, by rfl⟩ : syracuseStep 7703525 = 1444411) B1444411
theorem B2026505 : Blo 1350994 2026505 := bstep (se 2 (by rfl) ⟨759939, by rfl⟩ : syracuseStep 2026505 = 1519879) B1519879
theorem B4566023 : Blo 1350994 4566023 := bstep (se 1 (by rfl) ⟨3424517, by rfl⟩ : syracuseStep 4566023 = 6849035) B6849035
theorem B3042323 : Blo 1350994 3042323 := bstep (se 1 (by rfl) ⟨2281742, by rfl⟩ : syracuseStep 3042323 = 4563485) B4563485
theorem B2026535 : Blo 1350994 2026535 := bstep (se 1 (by rfl) ⟨1519901, by rfl⟩ : syracuseStep 2026535 = 3039803) B3039803
theorem B2280487 : Blo 1350994 2280487 := bstep (se 1 (by rfl) ⟨1710365, by rfl⟩ : syracuseStep 2280487 = 3420731) B3420731
theorem B4566131 : Blo 1350994 4566131 := bstep (se 1 (by rfl) ⟨3424598, by rfl⟩ : syracuseStep 4566131 = 6849197) B6849197
theorem B2026619 : Blo 1350994 2026619 := bstep (se 1 (by rfl) ⟨1519964, by rfl⟩ : syracuseStep 2026619 = 3039929) B3039929
theorem B2026745 : Blo 1350994 2026745 := bstep (se 2 (by rfl) ⟨760029, by rfl⟩ : syracuseStep 2026745 = 1520059) B1520059
theorem B2026847 : Blo 1350994 2026847 := bstep (se 1 (by rfl) ⟨1520135, by rfl⟩ : syracuseStep 2026847 = 3040271) B3040271
theorem B3247465 : Blo 1350994 3247465 := bstep (se 2 (by rfl) ⟨1217799, by rfl⟩ : syracuseStep 3247465 = 2435599) B2435599
theorem B3042665 : Blo 1350994 3042665 := bstep (se 2 (by rfl) ⟨1140999, by rfl⟩ : syracuseStep 3042665 = 2281999) B2281999
theorem B2026859 : Blo 1350994 2026859 := bstep (se 1 (by rfl) ⟨1520144, by rfl⟩ : syracuseStep 2026859 = 3040289) B3040289
theorem B2280811 : Blo 1350994 2280811 := bstep (se 1 (by rfl) ⟨1710608, by rfl⟩ : syracuseStep 2280811 = 3421217) B3421217
theorem B2567531 : Blo 1350994 2567531 := bstep (se 1 (by rfl) ⟨1925648, by rfl⟩ : syracuseStep 2567531 = 3851297) B3851297
theorem B7703981 : Blo 1350994 7703981 := bstep (se 3 (by rfl) ⟨1444496, by rfl⟩ : syracuseStep 7703981 = 2888993) B2888993
theorem B2739719 : Blo 1350994 2739719 := bstep (se 1 (by rfl) ⟨2054789, by rfl⟩ : syracuseStep 2739719 = 4109579) B4109579
theorem B4869641 : Blo 1350994 4869641 := bstep (se 2 (by rfl) ⟨1826115, by rfl⟩ : syracuseStep 4869641 = 3652231) B3652231
theorem B2027087 : Blo 1350994 2027087 := bstep (se 1 (by rfl) ⟨1520315, by rfl⟩ : syracuseStep 2027087 = 3040631) B3040631
theorem B8662625 : Blo 1350994 8662625 := bstep (se 2 (by rfl) ⟨3248484, by rfl⟩ : syracuseStep 8662625 = 6496969) B6496969
theorem B5779133 : Blo 1350994 5779133 := bstep (se 3 (by rfl) ⟨1083587, by rfl⟩ : syracuseStep 5779133 = 2167175) B2167175
theorem B2027207 : Blo 1350994 2027207 := bstep (se 1 (by rfl) ⟨1520405, by rfl⟩ : syracuseStep 2027207 = 3040811) B3040811
theorem B5132099 : Blo 1350994 5132099 := bstep (se 1 (by rfl) ⟨3849074, by rfl⟩ : syracuseStep 5132099 = 7698149) B7698149
theorem B2027369 : Blo 1350994 2027369 := bstep (se 2 (by rfl) ⟨760263, by rfl⟩ : syracuseStep 2027369 = 1520527) B1520527
theorem B55529333 : Blo 1350994 55529333 := bstep (se 5 (by rfl) ⟨2602937, by rfl⟩ : syracuseStep 55529333 = 5205875) B5205875
theorem B2027447 : Blo 1350994 2027447 := bstep (se 1 (by rfl) ⟨1520585, by rfl⟩ : syracuseStep 2027447 = 3041171) B3041171
theorem B3043259 : Blo 1350994 3043259 := bstep (se 1 (by rfl) ⟨2282444, by rfl⟩ : syracuseStep 3043259 = 4564889) B4564889
theorem B2027483 : Blo 1350994 2027483 := bstep (se 1 (by rfl) ⟨1520612, by rfl⟩ : syracuseStep 2027483 = 3041225) B3041225
theorem B2568199 : Blo 1350994 2568199 := bstep (se 1 (by rfl) ⟨1926149, by rfl⟩ : syracuseStep 2568199 = 3852299) B3852299
theorem B3043385 : Blo 1350994 3043385 := bstep (se 2 (by rfl) ⟨1141269, by rfl⟩ : syracuseStep 3043385 = 2282539) B2282539
theorem B7704665 : Blo 1350994 7704665 := bstep (se 2 (by rfl) ⟨2889249, by rfl⟩ : syracuseStep 7704665 = 5778499) B5778499
theorem B14061745 : Blo 1350994 14061745 := bstep (se 2 (by rfl) ⟨5273154, by rfl⟩ : syracuseStep 14061745 = 10546309) B10546309
theorem B3420407 : Blo 1350994 3420407 := bstep (se 1 (by rfl) ⟨2565305, by rfl⟩ : syracuseStep 3420407 = 5130611) B5130611
theorem B5132555 : Blo 1350994 5132555 := bstep (se 1 (by rfl) ⟨3849416, by rfl⟩ : syracuseStep 5132555 = 7698833) B7698833
theorem B9245015 : Blo 1350994 9245015 := bstep (se 1 (by rfl) ⟨6933761, by rfl⟩ : syracuseStep 9245015 = 13867523) B13867523
theorem B2281871 : Blo 1350994 2281871 := bstep (se 1 (by rfl) ⟨1711403, by rfl⟩ : syracuseStep 2281871 = 3422807) B3422807
theorem B3043727 : Blo 1350994 3043727 := bstep (se 1 (by rfl) ⟨2282795, by rfl⟩ : syracuseStep 3043727 = 4565591) B4565591
theorem B2027951 : Blo 1350994 2027951 := bstep (se 1 (by rfl) ⟨1520963, by rfl⟩ : syracuseStep 2027951 = 3041927) B3041927
theorem B2028041 : Blo 1350994 2028041 := bstep (se 2 (by rfl) ⟨760515, by rfl⟩ : syracuseStep 2028041 = 1521031) B1521031
theorem B1520167 : Blo 1350994 1520167 := bstep (se 1 (by rfl) ⟨1140125, by rfl⟩ : syracuseStep 1520167 = 2280251) B2280251
theorem B2028071 : Blo 1350994 2028071 := bstep (se 1 (by rfl) ⟨1521053, by rfl⟩ : syracuseStep 2028071 = 3042107) B3042107
theorem B3904039 : Blo 1350994 3904039 := bstep (se 1 (by rfl) ⟨2928029, by rfl⟩ : syracuseStep 3904039 = 5856059) B5856059
theorem B2028155 : Blo 1350994 2028155 := bstep (se 1 (by rfl) ⟨1521116, by rfl⟩ : syracuseStep 2028155 = 3042233) B3042233
theorem B2282107 : Blo 1350994 2282107 := bstep (se 1 (by rfl) ⟨1711580, by rfl⟩ : syracuseStep 2282107 = 3423161) B3423161
theorem B3044051 : Blo 1350994 3044051 := bstep (se 1 (by rfl) ⟨2283038, by rfl⟩ : syracuseStep 3044051 = 4566077) B4566077
theorem B2028281 : Blo 1350994 2028281 := bstep (se 2 (by rfl) ⟨760605, by rfl⟩ : syracuseStep 2028281 = 1521211) B1521211
theorem B9876253 : Blo 1350994 9876253 := bstep (se 3 (by rfl) ⟨1851797, by rfl⟩ : syracuseStep 9876253 = 3703595) B3703595
theorem B4870955 : Blo 1350994 4870955 := bstep (se 1 (by rfl) ⟨3653216, by rfl⟩ : syracuseStep 4870955 = 7306433) B7306433
theorem B2741087 : Blo 1350994 2741087 := bstep (se 1 (by rfl) ⟨2055815, by rfl⟩ : syracuseStep 2741087 = 4111631) B4111631
theorem B2028383 : Blo 1350994 2028383 := bstep (se 1 (by rfl) ⟨1521287, by rfl⟩ : syracuseStep 2028383 = 3042575) B3042575
theorem B2028395 : Blo 1350994 2028395 := bstep (se 1 (by rfl) ⟨1521296, by rfl⟩ : syracuseStep 2028395 = 3042593) B3042593
theorem B4330415 : Blo 1350994 4330415 := bstep (se 1 (by rfl) ⟨3247811, by rfl⟩ : syracuseStep 4330415 = 6495623) B6495623
theorem B5133239 : Blo 1350994 5133239 := bstep (se 1 (by rfl) ⟨3849929, by rfl⟩ : syracuseStep 5133239 = 7699859) B7699859
theorem B2888635 : Blo 1350994 2888635 := bstep (se 1 (by rfl) ⟨2166476, by rfl⟩ : syracuseStep 2888635 = 4332953) B4332953
theorem B1733671 : Blo 1350994 1733671 := bstep (se 1 (by rfl) ⟨1300253, by rfl⟩ : syracuseStep 1733671 = 2600507) B2600507
theorem B17331245 : Blo 1350994 17331245 := bstep (se 3 (by rfl) ⟨3249608, by rfl⟩ : syracuseStep 17331245 = 6499217) B6499217
theorem B15397937 : Blo 1350994 15397937 := bstep (se 2 (by rfl) ⟨5774226, by rfl⟩ : syracuseStep 15397937 = 11548453) B11548453
theorem B2028623 : Blo 1350994 2028623 := bstep (se 1 (by rfl) ⟨1521467, by rfl⟩ : syracuseStep 2028623 = 3042935) B3042935
theorem B4560029 : Blo 1350994 4560029 := bstep (se 3 (by rfl) ⟨855005, by rfl⟩ : syracuseStep 4560029 = 1710011) B1710011
theorem B2028743 : Blo 1350994 2028743 := bstep (se 1 (by rfl) ⟨1521557, by rfl⟩ : syracuseStep 2028743 = 3043115) B3043115
theorem B85505381 : Blo 1350994 85505381 := bstep (se 4 (by rfl) ⟨8016129, by rfl⟩ : syracuseStep 85505381 = 16032259) B16032259
theorem B2028905 : Blo 1350994 2028905 := bstep (se 2 (by rfl) ⟨760839, by rfl⟩ : syracuseStep 2028905 = 1521679) B1521679
theorem B2028983 : Blo 1350994 2028983 := bstep (se 1 (by rfl) ⟨1521737, by rfl⟩ : syracuseStep 2028983 = 3043475) B3043475
theorem B2029019 : Blo 1350994 2029019 := bstep (se 1 (by rfl) ⟨1521764, by rfl⟩ : syracuseStep 2029019 = 3043529) B3043529
theorem B2282971 : Blo 1350994 2282971 := bstep (se 1 (by rfl) ⟨1712228, by rfl⟩ : syracuseStep 2282971 = 3424457) B3424457
theorem B3421835 : Blo 1350994 3421835 := bstep (se 1 (by rfl) ⟨2566376, by rfl⟩ : syracuseStep 3421835 = 5132753) B5132753
theorem B4560569 : Blo 1350994 4560569 := bstep (se 2 (by rfl) ⟨1710213, by rfl⟩ : syracuseStep 4560569 = 3420427) B3420427
theorem B5134013 : Blo 1350994 5134013 := bstep (se 3 (by rfl) ⟨962627, by rfl⟩ : syracuseStep 5134013 = 1925255) B1925255
theorem B14612167 : Blo 1350994 14612167 := bstep (se 1 (by rfl) ⟨10959125, by rfl⟩ : syracuseStep 14612167 = 21918251) B21918251
theorem B21919481 : Blo 1350994 21919481 := bstep (se 2 (by rfl) ⟨8219805, by rfl⟩ : syracuseStep 21919481 = 16439611) B16439611
theorem B6166315 : Blo 1350994 6166315 := bstep (se 1 (by rfl) ⟨4624736, by rfl⟩ : syracuseStep 6166315 = 9249473) B9249473
theorem B3422047 : Blo 1350994 3422047 := bstep (se 1 (by rfl) ⟨2566535, by rfl⟩ : syracuseStep 3422047 = 5133071) B5133071
theorem B2029487 : Blo 1350994 2029487 := bstep (se 1 (by rfl) ⟨1522115, by rfl⟩ : syracuseStep 2029487 = 3044231) B3044231
theorem B1521787 : Blo 1350994 1521787 := bstep (se 1 (by rfl) ⟨1141340, by rfl⟩ : syracuseStep 1521787 = 2282681) B2282681
theorem B23107841 : Blo 1350994 23107841 := bstep (se 2 (by rfl) ⟨8665440, by rfl⟩ : syracuseStep 23107841 = 17330881) B17330881
theorem B4561163 : Blo 1350994 4561163 := bstep (se 1 (by rfl) ⟨3420872, by rfl⟩ : syracuseStep 4561163 = 6841745) B6841745
theorem B5134697 : Blo 1350994 5134697 := bstep (se 2 (by rfl) ⟨1925511, by rfl⟩ : syracuseStep 5134697 = 3851023) B3851023
theorem B3848573 : Blo 1350994 3848573 := bstep (se 3 (by rfl) ⟨721607, by rfl⟩ : syracuseStep 3848573 = 1443215) B1443215
theorem B8223241 : Blo 1350994 8223241 := bstep (se 2 (by rfl) ⟨3083715, by rfl⟩ : syracuseStep 8223241 = 6167431) B6167431
theorem B39008789 : Blo 1350994 39008789 := bstep (se 6 (by rfl) ⟨914268, by rfl⟩ : syracuseStep 39008789 = 1828537) B1828537
theorem B4561433 : Blo 1350994 4561433 := bstep (se 2 (by rfl) ⟨1710537, by rfl⟩ : syracuseStep 4561433 = 3421075) B3421075
theorem B1710715 : Blo 1350994 1710715 := bstep (se 1 (by rfl) ⟨1283036, by rfl⟩ : syracuseStep 1710715 = 2566073) B2566073
theorem B3422969 : Blo 1350994 3422969 := bstep (se 2 (by rfl) ⟨1283613, by rfl⟩ : syracuseStep 3422969 = 2567227) B2567227
theorem B6495083 : Blo 1350994 6495083 := bstep (se 1 (by rfl) ⟨4871312, by rfl⟩ : syracuseStep 6495083 = 9742625) B9742625
theorem B6847415 : Blo 1350994 6847415 := bstep (se 1 (by rfl) ⟨5135561, by rfl⟩ : syracuseStep 6847415 = 10271123) B10271123
theorem B4873331 : Blo 1350994 4873331 := bstep (se 1 (by rfl) ⟨3654998, by rfl⟩ : syracuseStep 4873331 = 7309997) B7309997
theorem B8658265 : Blo 1350994 8658265 := bstep (se 2 (by rfl) ⟨3246849, by rfl⟩ : syracuseStep 8658265 = 6493699) B6493699
theorem B1351007 : Blo 1350994 1351007 := bstep (se 1 (by rfl) ⟨1013255, by rfl⟩ : syracuseStep 1351007 = 2026511) B2026511
theorem B1351035 : Blo 1350994 1351035 := bstep (se 1 (by rfl) ⟨1013276, by rfl⟩ : syracuseStep 1351035 = 2026553) B2026553
theorem B3423617 : Blo 1350994 3423617 := bstep (se 2 (by rfl) ⟨1283856, by rfl⟩ : syracuseStep 3423617 = 2567713) B2567713
theorem B1351087 : Blo 1350994 1351087 := bstep (se 1 (by rfl) ⟨1013315, by rfl⟩ : syracuseStep 1351087 = 2026631) B2026631
theorem B1351111 : Blo 1350994 1351111 := bstep (se 1 (by rfl) ⟨1013333, by rfl⟩ : syracuseStep 1351111 = 2026667) B2026667
theorem B1351131 : Blo 1350994 1351131 := bstep (se 1 (by rfl) ⟨1013348, by rfl⟩ : syracuseStep 1351131 = 2026697) B2026697
theorem B1351207 : Blo 1350994 1351207 := bstep (se 1 (by rfl) ⟨1013405, by rfl⟩ : syracuseStep 1351207 = 2026811) B2026811
theorem B1351247 : Blo 1350994 1351247 := bstep (se 1 (by rfl) ⟨1013435, by rfl⟩ : syracuseStep 1351247 = 2026871) B2026871
theorem B1351263 : Blo 1350994 1351263 := bstep (se 1 (by rfl) ⟨1013447, by rfl⟩ : syracuseStep 1351263 = 2026895) B2026895
theorem B1351291 : Blo 1350994 1351291 := bstep (se 1 (by rfl) ⟨1013468, by rfl⟩ : syracuseStep 1351291 = 2026937) B2026937
theorem B4562567 : Blo 1350994 4562567 := bstep (se 1 (by rfl) ⟨3421925, by rfl⟩ : syracuseStep 4562567 = 6843851) B6843851
theorem B1351343 : Blo 1350994 1351343 := bstep (se 1 (by rfl) ⟨1013507, by rfl⟩ : syracuseStep 1351343 = 2027015) B2027015
theorem B4562621 : Blo 1350994 4562621 := bstep (se 3 (by rfl) ⟨855491, by rfl⟩ : syracuseStep 4562621 = 1710983) B1710983
theorem B1351367 : Blo 1350994 1351367 := bstep (se 1 (by rfl) ⟨1013525, by rfl⟩ : syracuseStep 1351367 = 2027051) B2027051
theorem B5775047 : Blo 1350994 5775047 := bstep (se 1 (by rfl) ⟨4331285, by rfl⟩ : syracuseStep 5775047 = 8662571) B8662571
theorem B1351387 : Blo 1350994 1351387 := bstep (se 1 (by rfl) ⟨1013540, by rfl⟩ : syracuseStep 1351387 = 2027081) B2027081
theorem B1351463 : Blo 1350994 1351463 := bstep (se 1 (by rfl) ⟨1013597, by rfl⟩ : syracuseStep 1351463 = 2027195) B2027195
theorem B7700291 : Blo 1350994 7700291 := bstep (se 1 (by rfl) ⟨5775218, by rfl⟩ : syracuseStep 7700291 = 11550437) B11550437
theorem B1351503 : Blo 1350994 1351503 := bstep (se 1 (by rfl) ⟨1013627, by rfl⟩ : syracuseStep 1351503 = 2027255) B2027255
theorem B1351519 : Blo 1350994 1351519 := bstep (se 1 (by rfl) ⟨1013639, by rfl⟩ : syracuseStep 1351519 = 2027279) B2027279
theorem B4562783 : Blo 1350994 4562783 := bstep (se 1 (by rfl) ⟨3422087, by rfl⟩ : syracuseStep 4562783 = 6844175) B6844175
theorem B21938039 : Blo 1350994 21938039 := bstep (se 1 (by rfl) ⟨16453529, by rfl⟩ : syracuseStep 21938039 = 32907059) B32907059
theorem B1351547 : Blo 1350994 1351547 := bstep (se 1 (by rfl) ⟨1013660, by rfl⟩ : syracuseStep 1351547 = 2027321) B2027321
theorem B1351599 : Blo 1350994 1351599 := bstep (se 1 (by rfl) ⟨1013699, by rfl⟩ : syracuseStep 1351599 = 2027399) B2027399
theorem B4112311 : Blo 1350994 4112311 := bstep (se 1 (by rfl) ⟨3084233, by rfl⟩ : syracuseStep 4112311 = 6168467) B6168467
theorem B1351623 : Blo 1350994 1351623 := bstep (se 1 (by rfl) ⟨1013717, by rfl⟩ : syracuseStep 1351623 = 2027435) B2027435
theorem B1351643 : Blo 1350994 1351643 := bstep (se 1 (by rfl) ⟨1013732, by rfl⟩ : syracuseStep 1351643 = 2027465) B2027465
theorem B3424265 : Blo 1350994 3424265 := bstep (se 2 (by rfl) ⟨1284099, by rfl⟩ : syracuseStep 3424265 = 2568199) B2568199
theorem B5136443 : Blo 1350994 5136443 := bstep (se 1 (by rfl) ⟨3852332, by rfl⟩ : syracuseStep 5136443 = 7704665) B7704665
theorem B1351967 : Blo 1350994 1351967 := bstep (se 1 (by rfl) ⟨1013975, by rfl⟩ : syracuseStep 1351967 = 2027951) B2027951
theorem B1352027 : Blo 1350994 1352027 := bstep (se 1 (by rfl) ⟨1014020, by rfl⟩ : syracuseStep 1352027 = 2028041) B2028041
theorem B3424619 : Blo 1350994 3424619 := bstep (se 1 (by rfl) ⟨2568464, by rfl⟩ : syracuseStep 3424619 = 5136929) B5136929
theorem B1352047 : Blo 1350994 1352047 := bstep (se 1 (by rfl) ⟨1014035, by rfl⟩ : syracuseStep 1352047 = 2028071) B2028071
theorem B14614937 : Blo 1350994 14614937 := bstep (se 2 (by rfl) ⟨5480601, by rfl⟩ : syracuseStep 14614937 = 10961203) B10961203
theorem B1352103 : Blo 1350994 1352103 := bstep (se 1 (by rfl) ⟨1014077, by rfl⟩ : syracuseStep 1352103 = 2028155) B2028155
theorem B1352187 : Blo 1350994 1352187 := bstep (se 1 (by rfl) ⟨1014140, by rfl⟩ : syracuseStep 1352187 = 2028281) B2028281
theorem B1352255 : Blo 1350994 1352255 := bstep (se 1 (by rfl) ⟨1014191, by rfl⟩ : syracuseStep 1352255 = 2028383) B2028383
theorem B1352263 : Blo 1350994 1352263 := bstep (se 1 (by rfl) ⟨1014197, by rfl⟩ : syracuseStep 1352263 = 2028395) B2028395
theorem B7307921 : Blo 1350994 7307921 := bstep (se 2 (by rfl) ⟨2740470, by rfl⟩ : syracuseStep 7307921 = 5480941) B5480941
theorem B10265291 : Blo 1350994 10265291 := bstep (se 1 (by rfl) ⟨7698968, by rfl⟩ : syracuseStep 10265291 = 15397937) B15397937
theorem B1352415 : Blo 1350994 1352415 := bstep (se 1 (by rfl) ⟨1014311, by rfl⟩ : syracuseStep 1352415 = 2028623) B2028623
theorem B3040019 : Blo 1350994 3040019 := bstep (se 1 (by rfl) ⟨2280014, by rfl⟩ : syracuseStep 3040019 = 4560029) B4560029
theorem B1352495 : Blo 1350994 1352495 := bstep (se 1 (by rfl) ⟨1014371, by rfl⟩ : syracuseStep 1352495 = 2028743) B2028743
theorem B10961723 : Blo 1350994 10961723 := bstep (se 1 (by rfl) ⟨8221292, by rfl⟩ : syracuseStep 10961723 = 16442585) B16442585
theorem B6849359 : Blo 1350994 6849359 := bstep (se 1 (by rfl) ⟨5137019, by rfl⟩ : syracuseStep 6849359 = 10274039) B10274039
theorem B23085971 : Blo 1350994 23085971 := bstep (se 1 (by rfl) ⟨17314478, by rfl⟩ : syracuseStep 23085971 = 34628957) B34628957
theorem B1352603 : Blo 1350994 1352603 := bstep (se 1 (by rfl) ⟨1014452, by rfl⟩ : syracuseStep 1352603 = 2028905) B2028905
theorem B2196379 : Blo 1350994 2196379 := bstep (se 1 (by rfl) ⟨1647284, by rfl⟩ : syracuseStep 2196379 = 3294569) B3294569
theorem B1442767 : Blo 1350994 1442767 := bstep (se 1 (by rfl) ⟨1082075, by rfl⟩ : syracuseStep 1442767 = 2164151) B2164151
theorem B1352655 : Blo 1350994 1352655 := bstep (se 1 (by rfl) ⟨1014491, by rfl⟩ : syracuseStep 1352655 = 2028983) B2028983
theorem B3851239 : Blo 1350994 3851239 := bstep (se 1 (by rfl) ⟨2888429, by rfl⟩ : syracuseStep 3851239 = 5776859) B5776859
theorem B1352679 : Blo 1350994 1352679 := bstep (se 1 (by rfl) ⟨1014509, by rfl⟩ : syracuseStep 1352679 = 2029019) B2029019
theorem B3040379 : Blo 1350994 3040379 := bstep (se 1 (by rfl) ⟨2280284, by rfl⟩ : syracuseStep 3040379 = 4560569) B4560569
theorem B4875497 : Blo 1350994 4875497 := bstep (se 2 (by rfl) ⟨1828311, by rfl⟩ : syracuseStep 4875497 = 3656623) B3656623
theorem B3040505 : Blo 1350994 3040505 := bstep (se 2 (by rfl) ⟨1140189, by rfl⟩ : syracuseStep 3040505 = 2280379) B2280379
theorem B3851513 : Blo 1350994 3851513 := bstep (se 2 (by rfl) ⟨1444317, by rfl⟩ : syracuseStep 3851513 = 2888635) B2888635
theorem B1352991 : Blo 1350994 1352991 := bstep (se 1 (by rfl) ⟨1014743, by rfl⟩ : syracuseStep 1352991 = 2029487) B2029487
theorem B2164105 : Blo 1350994 2164105 := bstep (se 2 (by rfl) ⟨811539, by rfl⟩ : syracuseStep 2164105 = 1623079) B1623079
theorem B2311561 : Blo 1350994 2311561 := bstep (se 2 (by rfl) ⟨866835, by rfl⟩ : syracuseStep 2311561 = 1733671) B1733671
theorem B3040649 : Blo 1350994 3040649 := bstep (se 2 (by rfl) ⟨1140243, by rfl⟩ : syracuseStep 3040649 = 2280487) B2280487
theorem B3040775 : Blo 1350994 3040775 := bstep (se 1 (by rfl) ⟨2280581, by rfl⟩ : syracuseStep 3040775 = 4561163) B4561163
theorem B3040955 : Blo 1350994 3040955 := bstep (se 1 (by rfl) ⟨2280716, by rfl⟩ : syracuseStep 3040955 = 4561433) B4561433
theorem B2967275 : Blo 1350994 2967275 := bstep (se 1 (by rfl) ⟨2225456, by rfl⟩ : syracuseStep 2967275 = 4450913) B4450913
theorem B11544353 : Blo 1350994 11544353 := bstep (se 2 (by rfl) ⟨4329132, by rfl⟩ : syracuseStep 11544353 = 8658265) B8658265
theorem B3041081 : Blo 1350994 3041081 := bstep (se 2 (by rfl) ⟨1140405, by rfl⟩ : syracuseStep 3041081 = 2280811) B2280811
theorem B4564943 : Blo 1350994 4564943 := bstep (se 1 (by rfl) ⟨3423707, by rfl⟩ : syracuseStep 4564943 = 6847415) B6847415
theorem B4622521 : Blo 1350994 4622521 := bstep (se 2 (by rfl) ⟨1733445, by rfl⟩ : syracuseStep 4622521 = 3466891) B3466891
theorem B7309565 : Blo 1350994 7309565 := bstep (se 3 (by rfl) ⟨1370543, by rfl⟩ : syracuseStep 7309565 = 2741087) B2741087
theorem B19482889 : Blo 1350994 19482889 := bstep (se 2 (by rfl) ⟨7306083, by rfl⟩ : syracuseStep 19482889 = 14612167) B14612167
theorem B3246427 : Blo 1350994 3246427 := bstep (se 1 (by rfl) ⟨2434820, by rfl⟩ : syracuseStep 3246427 = 4869641) B4869641
theorem B3041711 : Blo 1350994 3041711 := bstep (se 1 (by rfl) ⟨2281283, by rfl⟩ : syracuseStep 3041711 = 4562567) B4562567
theorem B3041747 : Blo 1350994 3041747 := bstep (se 1 (by rfl) ⟨2281310, by rfl⟩ : syracuseStep 3041747 = 4562621) B4562621
theorem B3852755 : Blo 1350994 3852755 := bstep (se 1 (by rfl) ⟨2889566, by rfl⟩ : syracuseStep 3852755 = 5779133) B5779133
theorem B3041855 : Blo 1350994 3041855 := bstep (se 1 (by rfl) ⟨2281391, by rfl⟩ : syracuseStep 3041855 = 4562783) B4562783
theorem B5483081 : Blo 1350994 5483081 := bstep (se 2 (by rfl) ⟨2056155, by rfl⟩ : syracuseStep 5483081 = 4112311) B4112311
theorem B6589001 : Blo 1350994 6589001 := bstep (se 2 (by rfl) ⟨2470875, by rfl⟩ : syracuseStep 6589001 = 4941751) B4941751
theorem B14625359 : Blo 1350994 14625359 := bstep (se 1 (by rfl) ⟨10969019, by rfl⟩ : syracuseStep 14625359 = 21938039) B21938039
theorem B3041963 : Blo 1350994 3041963 := bstep (se 1 (by rfl) ⟨2281472, by rfl⟩ : syracuseStep 3041963 = 4562945) B4562945
theorem B14617361 : Blo 1350994 14617361 := bstep (se 2 (by rfl) ⟨5481510, by rfl⟩ : syracuseStep 14617361 = 10963021) B10963021
theorem B6843203 : Blo 1350994 6843203 := bstep (se 1 (by rfl) ⟨5132402, by rfl⟩ : syracuseStep 6843203 = 10264805) B10264805
theorem B2280271 : Blo 1350994 2280271 := bstep (se 1 (by rfl) ⟨1710203, by rfl⟩ : syracuseStep 2280271 = 3420407) B3420407
theorem B2566991 : Blo 1350994 2566991 := bstep (se 1 (by rfl) ⟨1925243, by rfl⟩ : syracuseStep 2566991 = 3850487) B3850487
theorem B6163343 : Blo 1350994 6163343 := bstep (se 1 (by rfl) ⟨4622507, by rfl⟩ : syracuseStep 6163343 = 9245015) B9245015
theorem B5204891 : Blo 1350994 5204891 := bstep (se 1 (by rfl) ⟨3903668, by rfl⟩ : syracuseStep 5204891 = 7807337) B7807337
theorem B4565915 : Blo 1350994 4565915 := bstep (se 1 (by rfl) ⟨3424436, by rfl⟩ : syracuseStep 4565915 = 6848873) B6848873
theorem B12995549 : Blo 1350994 12995549 := bstep (se 3 (by rfl) ⟨2436665, by rfl⟩ : syracuseStep 12995549 = 4873331) B4873331
theorem B2567143 : Blo 1350994 2567143 := bstep (se 1 (by rfl) ⟨1925357, by rfl⟩ : syracuseStep 2567143 = 3850715) B3850715
theorem B3247303 : Blo 1350994 3247303 := bstep (se 1 (by rfl) ⟨2435477, by rfl⟩ : syracuseStep 3247303 = 4870955) B4870955
theorem B3042503 : Blo 1350994 3042503 := bstep (se 1 (by rfl) ⟨2281877, by rfl⟩ : syracuseStep 3042503 = 4563755) B4563755
theorem B2026715 : Blo 1350994 2026715 := bstep (se 1 (by rfl) ⟨1520036, by rfl⟩ : syracuseStep 2026715 = 3040073) B3040073
theorem B2886943 : Blo 1350994 2886943 := bstep (se 1 (by rfl) ⟨2165207, by rfl⟩ : syracuseStep 2886943 = 4330415) B4330415
theorem B10964321 : Blo 1350994 10964321 := bstep (se 2 (by rfl) ⟨4111620, by rfl⟩ : syracuseStep 10964321 = 8223241) B8223241
theorem B11554163 : Blo 1350994 11554163 := bstep (se 1 (by rfl) ⟨8665622, by rfl⟩ : syracuseStep 11554163 = 17331245) B17331245
theorem B3042683 : Blo 1350994 3042683 := bstep (se 1 (by rfl) ⟨2282012, by rfl⟩ : syracuseStep 3042683 = 4564025) B4564025
theorem B2026889 : Blo 1350994 2026889 := bstep (se 2 (by rfl) ⟨760083, by rfl⟩ : syracuseStep 2026889 = 1520167) B1520167
theorem B5205385 : Blo 1350994 5205385 := bstep (se 2 (by rfl) ⟨1952019, by rfl⟩ : syracuseStep 5205385 = 3904039) B3904039
theorem B2280953 : Blo 1350994 2280953 := bstep (se 2 (by rfl) ⟨855357, by rfl⟩ : syracuseStep 2280953 = 1710715) B1710715
theorem B3042809 : Blo 1350994 3042809 := bstep (se 2 (by rfl) ⟨1141053, by rfl⟩ : syracuseStep 3042809 = 2282107) B2282107
theorem B57003587 : Blo 1350994 57003587 := bstep (se 1 (by rfl) ⟨42752690, by rfl⟩ : syracuseStep 57003587 = 85505381) B85505381
theorem B3042899 : Blo 1350994 3042899 := bstep (se 1 (by rfl) ⟨2282174, by rfl⟩ : syracuseStep 3042899 = 4564349) B4564349
theorem B14814829 : Blo 1350994 14814829 := bstep (se 3 (by rfl) ⟨2777780, by rfl⟩ : syracuseStep 14814829 = 5555561) B5555561
theorem B6844013 : Blo 1350994 6844013 := bstep (se 3 (by rfl) ⟨1283252, by rfl⟩ : syracuseStep 6844013 = 2566505) B2566505
theorem B4329121 : Blo 1350994 4329121 := bstep (se 2 (by rfl) ⟨1623420, by rfl⟩ : syracuseStep 4329121 = 3246841) B3246841
theorem B13168337 : Blo 1350994 13168337 := bstep (se 2 (by rfl) ⟨4938126, by rfl⟩ : syracuseStep 13168337 = 9876253) B9876253
theorem B2027243 : Blo 1350994 2027243 := bstep (se 1 (by rfl) ⟨1520432, by rfl⟩ : syracuseStep 2027243 = 3040865) B3040865
theorem B2281223 : Blo 1350994 2281223 := bstep (se 1 (by rfl) ⟨1710917, by rfl⟩ : syracuseStep 2281223 = 3421835) B3421835
theorem B3043079 : Blo 1350994 3043079 := bstep (se 1 (by rfl) ⟨2282309, by rfl⟩ : syracuseStep 3043079 = 4564619) B4564619
theorem B14659375 : Blo 1350994 14659375 := bstep (se 1 (by rfl) ⟨10994531, by rfl⟩ : syracuseStep 14659375 = 21989063) B21989063
theorem B2027471 : Blo 1350994 2027471 := bstep (se 1 (by rfl) ⟨1520603, by rfl⟩ : syracuseStep 2027471 = 3041207) B3041207
theorem B3420265 : Blo 1350994 3420265 := bstep (se 2 (by rfl) ⟨1282599, by rfl⟩ : syracuseStep 3420265 = 2565199) B2565199
theorem B15405227 : Blo 1350994 15405227 := bstep (se 1 (by rfl) ⟨11553920, by rfl⟩ : syracuseStep 15405227 = 23107841) B23107841
theorem B2027867 : Blo 1350994 2027867 := bstep (se 1 (by rfl) ⟨1520900, by rfl⟩ : syracuseStep 2027867 = 3041801) B3041801
theorem B26005859 : Blo 1350994 26005859 := bstep (se 1 (by rfl) ⟨19504394, by rfl⟩ : syracuseStep 26005859 = 39008789) B39008789
theorem B3043691 : Blo 1350994 3043691 := bstep (se 1 (by rfl) ⟨2282768, by rfl⟩ : syracuseStep 3043691 = 4565537) B4565537
theorem B4329953 : Blo 1350994 4329953 := bstep (se 2 (by rfl) ⟨1623732, by rfl⟩ : syracuseStep 4329953 = 3247465) B3247465
theorem B2281979 : Blo 1350994 2281979 := bstep (se 1 (by rfl) ⟨1711484, by rfl⟩ : syracuseStep 2281979 = 3422969) B3422969
theorem B3043835 : Blo 1350994 3043835 := bstep (se 1 (by rfl) ⟨2282876, by rfl⟩ : syracuseStep 3043835 = 4565753) B4565753
theorem B2028095 : Blo 1350994 2028095 := bstep (se 1 (by rfl) ⟨1521071, by rfl⟩ : syracuseStep 2028095 = 3042143) B3042143
theorem B4330055 : Blo 1350994 4330055 := bstep (se 1 (by rfl) ⟨3247541, by rfl⟩ : syracuseStep 4330055 = 6495083) B6495083
theorem B3420751 : Blo 1350994 3420751 := bstep (se 1 (by rfl) ⟨2565563, by rfl⟩ : syracuseStep 3420751 = 5131127) B5131127
theorem B3043961 : Blo 1350994 3043961 := bstep (se 2 (by rfl) ⟨1141485, by rfl⟩ : syracuseStep 3043961 = 2282971) B2282971
theorem B3044015 : Blo 1350994 3044015 := bstep (se 1 (by rfl) ⟨2283011, by rfl⟩ : syracuseStep 3044015 = 4566023) B4566023
theorem B2028215 : Blo 1350994 2028215 := bstep (se 1 (by rfl) ⟨1521161, by rfl⟩ : syracuseStep 2028215 = 3042323) B3042323
theorem B3044087 : Blo 1350994 3044087 := bstep (se 1 (by rfl) ⟨2283065, by rfl⟩ : syracuseStep 3044087 = 4566131) B4566131
theorem B2028443 : Blo 1350994 2028443 := bstep (se 1 (by rfl) ⟨1521332, by rfl⟩ : syracuseStep 2028443 = 3042665) B3042665
theorem B2282411 : Blo 1350994 2282411 := bstep (se 1 (by rfl) ⟨1711808, by rfl⟩ : syracuseStep 2282411 = 3423617) B3423617
theorem B8221753 : Blo 1350994 8221753 := bstep (se 2 (by rfl) ⟨3083157, by rfl⟩ : syracuseStep 8221753 = 6166315) B6166315
theorem B3421399 : Blo 1350994 3421399 := bstep (se 1 (by rfl) ⟨2566049, by rfl⟩ : syracuseStep 3421399 = 5132099) B5132099
theorem B5133527 : Blo 1350994 5133527 := bstep (se 1 (by rfl) ⟨3850145, by rfl⟩ : syracuseStep 5133527 = 7700291) B7700291
theorem B2028839 : Blo 1350994 2028839 := bstep (se 1 (by rfl) ⟨1521629, by rfl⟩ : syracuseStep 2028839 = 3043259) B3043259
theorem B2028923 : Blo 1350994 2028923 := bstep (se 1 (by rfl) ⟨1521692, by rfl⟩ : syracuseStep 2028923 = 3043385) B3043385
theorem B8656267 : Blo 1350994 8656267 := bstep (se 1 (by rfl) ⟨6492200, by rfl⟩ : syracuseStep 8656267 = 12984401) B12984401
theorem B25974179 : Blo 1350994 25974179 := bstep (se 1 (by rfl) ⟨19480634, by rfl⟩ : syracuseStep 25974179 = 38961269) B38961269
theorem B7411133 : Blo 1350994 7411133 := bstep (se 3 (by rfl) ⟨1389587, by rfl⟩ : syracuseStep 7411133 = 2779175) B2779175
theorem B2282951 : Blo 1350994 2282951 := bstep (se 1 (by rfl) ⟨1712213, by rfl⟩ : syracuseStep 2282951 = 3424427) B3424427
theorem B2029049 : Blo 1350994 2029049 := bstep (se 2 (by rfl) ⟨760893, by rfl⟩ : syracuseStep 2029049 = 1521787) B1521787
theorem B3421703 : Blo 1350994 3421703 := bstep (se 1 (by rfl) ⟨2566277, by rfl⟩ : syracuseStep 3421703 = 5132555) B5132555
theorem B18748993 : Blo 1350994 18748993 := bstep (se 2 (by rfl) ⟨7030872, by rfl⟩ : syracuseStep 18748993 = 14061745) B14061745
theorem B1521247 : Blo 1350994 1521247 := bstep (se 1 (by rfl) ⟨1140935, by rfl⟩ : syracuseStep 1521247 = 2281871) B2281871
theorem B2029151 : Blo 1350994 2029151 := bstep (se 1 (by rfl) ⟨1521863, by rfl⟩ : syracuseStep 2029151 = 3043727) B3043727
theorem B6493853 : Blo 1350994 6493853 := bstep (se 3 (by rfl) ⟨1217597, by rfl⟩ : syracuseStep 6493853 = 2435195) B2435195
theorem B2029367 : Blo 1350994 2029367 := bstep (se 1 (by rfl) ⟨1522025, by rfl⟩ : syracuseStep 2029367 = 3044051) B3044051
theorem B3422159 : Blo 1350994 3422159 := bstep (se 1 (by rfl) ⟨2566619, by rfl⟩ : syracuseStep 3422159 = 5133239) B5133239
theorem B7313543 : Blo 1350994 7313543 := bstep (se 1 (by rfl) ⟨5485157, by rfl⟩ : syracuseStep 7313543 = 10970315) B10970315
theorem B10262861 : Blo 1350994 10262861 := bstep (se 3 (by rfl) ⟨1924286, by rfl⟩ : syracuseStep 10262861 = 3848573) B3848573
theorem B56990099 : Blo 1350994 56990099 := bstep (se 1 (by rfl) ⟨42742574, by rfl⟩ : syracuseStep 56990099 = 85485149) B85485149
theorem B3422675 : Blo 1350994 3422675 := bstep (se 1 (by rfl) ⟨2567006, by rfl⟩ : syracuseStep 3422675 = 5134013) B5134013
theorem B14612987 : Blo 1350994 14612987 := bstep (se 1 (by rfl) ⟨10959740, by rfl⟩ : syracuseStep 14612987 = 21919481) B21919481
theorem B12999163 : Blo 1350994 12999163 := bstep (se 1 (by rfl) ⟨9749372, by rfl⟩ : syracuseStep 12999163 = 19498745) B19498745
theorem B4561487 : Blo 1350994 4561487 := bstep (se 1 (by rfl) ⟨3421115, by rfl⟩ : syracuseStep 4561487 = 6842231) B6842231
theorem B4332413 : Blo 1350994 4332413 := bstep (se 3 (by rfl) ⟨812327, by rfl⟩ : syracuseStep 4332413 = 1624655) B1624655
theorem B3423131 : Blo 1350994 3423131 := bstep (se 1 (by rfl) ⟨2567348, by rfl⟩ : syracuseStep 3423131 = 5134697) B5134697
theorem B24665107 : Blo 1350994 24665107 := bstep (se 1 (by rfl) ⟨18498830, by rfl⟩ : syracuseStep 24665107 = 36997661) B36997661
theorem B6167591 : Blo 1350994 6167591 := bstep (se 1 (by rfl) ⟨4625693, by rfl⟩ : syracuseStep 6167591 = 9251387) B9251387
theorem B5135683 : Blo 1350994 5135683 := bstep (se 1 (by rfl) ⟨3851762, by rfl⟩ : syracuseStep 5135683 = 7703525) B7703525
theorem B1351003 : Blo 1350994 1351003 := bstep (se 1 (by rfl) ⟨1013252, by rfl⟩ : syracuseStep 1351003 = 2026505) B2026505
theorem B1351023 : Blo 1350994 1351023 := bstep (se 1 (by rfl) ⟨1013267, by rfl⟩ : syracuseStep 1351023 = 2026535) B2026535
theorem B1351079 : Blo 1350994 1351079 := bstep (se 1 (by rfl) ⟨1013309, by rfl⟩ : syracuseStep 1351079 = 2026619) B2026619
theorem B6839801 : Blo 1350994 6839801 := bstep (se 2 (by rfl) ⟨2564925, by rfl⟩ : syracuseStep 6839801 = 5129851) B5129851
theorem B1351163 : Blo 1350994 1351163 := bstep (se 1 (by rfl) ⟨1013372, by rfl⟩ : syracuseStep 1351163 = 2026745) B2026745
theorem B1351231 : Blo 1350994 1351231 := bstep (se 1 (by rfl) ⟨1013423, by rfl⟩ : syracuseStep 1351231 = 2026847) B2026847
theorem B1351239 : Blo 1350994 1351239 := bstep (se 1 (by rfl) ⟨1013429, by rfl⟩ : syracuseStep 1351239 = 2026859) B2026859
theorem B1711687 : Blo 1350994 1711687 := bstep (se 1 (by rfl) ⟨1283765, by rfl⟩ : syracuseStep 1711687 = 2567531) B2567531
theorem B5135987 : Blo 1350994 5135987 := bstep (se 1 (by rfl) ⟨3851990, by rfl⟩ : syracuseStep 5135987 = 7703981) B7703981
theorem B1826479 : Blo 1350994 1826479 := bstep (se 1 (by rfl) ⟨1369859, by rfl⟩ : syracuseStep 1826479 = 2739719) B2739719
theorem B1351391 : Blo 1350994 1351391 := bstep (se 1 (by rfl) ⟨1013543, by rfl⟩ : syracuseStep 1351391 = 2027087) B2027087
theorem B5775083 : Blo 1350994 5775083 := bstep (se 1 (by rfl) ⟨4331312, by rfl⟩ : syracuseStep 5775083 = 8662625) B8662625
theorem B4562729 : Blo 1350994 4562729 := bstep (se 2 (by rfl) ⟨1711023, by rfl⟩ : syracuseStep 4562729 = 3422047) B3422047
theorem B5136169 : Blo 1350994 5136169 := bstep (se 2 (by rfl) ⟨1926063, by rfl⟩ : syracuseStep 5136169 = 3852127) B3852127
theorem B1351471 : Blo 1350994 1351471 := bstep (se 1 (by rfl) ⟨1013603, by rfl⟩ : syracuseStep 1351471 = 2027207) B2027207
theorem B3850031 : Blo 1350994 3850031 := bstep (se 1 (by rfl) ⟨2887523, by rfl⟩ : syracuseStep 3850031 = 5775047) B5775047
theorem B6840125 : Blo 1350994 6840125 := bstep (se 3 (by rfl) ⟨1282523, by rfl⟩ : syracuseStep 6840125 = 2565047) B2565047
theorem B1351579 : Blo 1350994 1351579 := bstep (se 1 (by rfl) ⟨1013684, by rfl⟩ : syracuseStep 1351579 = 2027369) B2027369
theorem B37019555 : Blo 1350994 37019555 := bstep (se 1 (by rfl) ⟨27764666, by rfl⟩ : syracuseStep 37019555 = 55529333) B55529333
theorem B1351631 : Blo 1350994 1351631 := bstep (se 1 (by rfl) ⟨1013723, by rfl⟩ : syracuseStep 1351631 = 2027447) B2027447
theorem B1351655 : Blo 1350994 1351655 := bstep (se 1 (by rfl) ⟨1013741, by rfl⟩ : syracuseStep 1351655 = 2027483) B2027483
theorem B3424295 : Blo 1350994 3424295 := bstep (se 1 (by rfl) ⟨2568221, by rfl⟩ : syracuseStep 3424295 = 5136443) B5136443
theorem B1351911 : Blo 1350994 1351911 := bstep (se 1 (by rfl) ⟨1013933, by rfl⟩ : syracuseStep 1351911 = 2027867) B2027867
theorem B25977185 : Blo 1350994 25977185 := bstep (se 2 (by rfl) ⟨9741444, by rfl⟩ : syracuseStep 25977185 = 19482889) B19482889
theorem B1352063 : Blo 1350994 1352063 := bstep (se 1 (by rfl) ⟨1014047, by rfl⟩ : syracuseStep 1352063 = 2028095) B2028095
theorem B1352143 : Blo 1350994 1352143 := bstep (se 1 (by rfl) ⟨1014107, by rfl⟩ : syracuseStep 1352143 = 2028215) B2028215
theorem B7307815 : Blo 1350994 7307815 := bstep (se 1 (by rfl) ⟨5480861, by rfl⟩ : syracuseStep 7307815 = 10961723) B10961723
theorem B1352295 : Blo 1350994 1352295 := bstep (se 1 (by rfl) ⟨1014221, by rfl⟩ : syracuseStep 1352295 = 2028443) B2028443
theorem B1352559 : Blo 1350994 1352559 := bstep (se 1 (by rfl) ⟨1014419, by rfl⟩ : syracuseStep 1352559 = 2028839) B2028839
theorem B1352615 : Blo 1350994 1352615 := bstep (se 1 (by rfl) ⟨1014461, by rfl⟩ : syracuseStep 1352615 = 2028923) B2028923
theorem B1352699 : Blo 1350994 1352699 := bstep (se 1 (by rfl) ⟨1014524, by rfl⟩ : syracuseStep 1352699 = 2029049) B2029049
theorem B1352767 : Blo 1350994 1352767 := bstep (se 1 (by rfl) ⟨1014575, by rfl⟩ : syracuseStep 1352767 = 2029151) B2029151
theorem B3040361 : Blo 1350994 3040361 := bstep (se 2 (by rfl) ⟨1140135, by rfl⟩ : syracuseStep 3040361 = 2280271) B2280271
theorem B1352911 : Blo 1350994 1352911 := bstep (se 1 (by rfl) ⟨1014683, by rfl⟩ : syracuseStep 1352911 = 2029367) B2029367
theorem B4875695 : Blo 1350994 4875695 := bstep (se 1 (by rfl) ⟨3656771, by rfl⟩ : syracuseStep 4875695 = 7313543) B7313543
theorem B6841907 : Blo 1350994 6841907 := bstep (se 1 (by rfl) ⟨5131430, by rfl⟩ : syracuseStep 6841907 = 10262861) B10262861
theorem B3655387 : Blo 1350994 3655387 := bstep (se 1 (by rfl) ⟨2741540, by rfl⟩ : syracuseStep 3655387 = 5483081) B5483081
theorem B4392667 : Blo 1350994 4392667 := bstep (se 1 (by rfl) ⟨3294500, by rfl⟩ : syracuseStep 4392667 = 6589001) B6589001
theorem B3040991 : Blo 1350994 3040991 := bstep (se 1 (by rfl) ⟨2280743, by rfl⟩ : syracuseStep 3040991 = 4561487) B4561487
theorem B9750239 : Blo 1350994 9750239 := bstep (se 1 (by rfl) ⟨7312679, by rfl⟩ : syracuseStep 9750239 = 14625359) B14625359
theorem B2885473 : Blo 1350994 2885473 := bstep (se 2 (by rfl) ⟨1082052, by rfl⟩ : syracuseStep 2885473 = 2164105) B2164105
theorem B6940513 : Blo 1350994 6940513 := bstep (se 2 (by rfl) ⟨2602692, by rfl⟩ : syracuseStep 6940513 = 5205385) B5205385
theorem B10266749 : Blo 1350994 10266749 := bstep (se 3 (by rfl) ⟨1925015, by rfl⟩ : syracuseStep 10266749 = 3850031) B3850031
theorem B19753105 : Blo 1350994 19753105 := bstep (se 2 (by rfl) ⟨7407414, by rfl⟩ : syracuseStep 19753105 = 14814829) B14814829
theorem B2435305 : Blo 1350994 2435305 := bstep (se 2 (by rfl) ⟨913239, by rfl⟩ : syracuseStep 2435305 = 1826479) B1826479
theorem B7309547 : Blo 1350994 7309547 := bstep (se 1 (by rfl) ⟨5482160, by rfl⟩ : syracuseStep 7309547 = 10964321) B10964321
theorem B7702775 : Blo 1350994 7702775 := bstep (se 1 (by rfl) ⟨5777081, by rfl⟩ : syracuseStep 7702775 = 11554163) B11554163
theorem B11553101 : Blo 1350994 11553101 := bstep (se 3 (by rfl) ⟨2166206, by rfl⟩ : syracuseStep 11553101 = 4332413) B4332413
theorem B3041819 : Blo 1350994 3041819 := bstep (se 1 (by rfl) ⟨2281364, by rfl⟩ : syracuseStep 3041819 = 4562729) B4562729
theorem B17337239 : Blo 1350994 17337239 := bstep (se 1 (by rfl) ⟨13002929, by rfl⟩ : syracuseStep 17337239 = 26005859) B26005859
theorem B6163361 : Blo 1350994 6163361 := bstep (se 2 (by rfl) ⟨2311260, by rfl⟩ : syracuseStep 6163361 = 4622521) B4622521
theorem B9743291 : Blo 1350994 9743291 := bstep (se 1 (by rfl) ⟨7307468, by rfl⟩ : syracuseStep 9743291 = 14614937) B14614937
theorem B2886635 : Blo 1350994 2886635 := bstep (se 1 (by rfl) ⟨2164976, by rfl⟩ : syracuseStep 2886635 = 4329953) B4329953
theorem B4328569 : Blo 1350994 4328569 := bstep (se 2 (by rfl) ⟨1623213, by rfl⟩ : syracuseStep 4328569 = 3246427) B3246427
theorem B6843527 : Blo 1350994 6843527 := bstep (se 1 (by rfl) ⟨5132645, by rfl⟩ : syracuseStep 6843527 = 10265291) B10265291
theorem B2026679 : Blo 1350994 2026679 := bstep (se 1 (by rfl) ⟨1520009, by rfl⟩ : syracuseStep 2026679 = 3040019) B3040019
theorem B4566239 : Blo 1350994 4566239 := bstep (se 1 (by rfl) ⟨3424679, by rfl⟩ : syracuseStep 4566239 = 6849359) B6849359
theorem B2026919 : Blo 1350994 2026919 := bstep (se 1 (by rfl) ⟨1520189, by rfl⟩ : syracuseStep 2026919 = 3040379) B3040379
theorem B2027003 : Blo 1350994 2027003 := bstep (se 1 (by rfl) ⟨1520252, by rfl⟩ : syracuseStep 2027003 = 3040505) B3040505
theorem B2567675 : Blo 1350994 2567675 := bstep (se 1 (by rfl) ⟨1925756, by rfl⟩ : syracuseStep 2567675 = 3851513) B3851513
theorem B2027099 : Blo 1350994 2027099 := bstep (se 1 (by rfl) ⟨1520324, by rfl⟩ : syracuseStep 2027099 = 3040649) B3040649
theorem B2027183 : Blo 1350994 2027183 := bstep (se 1 (by rfl) ⟨1520387, by rfl⟩ : syracuseStep 2027183 = 3040775) B3040775
theorem B2281135 : Blo 1350994 2281135 := bstep (se 1 (by rfl) ⟨1710851, by rfl⟩ : syracuseStep 2281135 = 3421703) B3421703
theorem B151973597 : Blo 1350994 151973597 := bstep (se 3 (by rfl) ⟨28495049, by rfl⟩ : syracuseStep 151973597 = 56990099) B56990099
theorem B4329235 : Blo 1350994 4329235 := bstep (se 1 (by rfl) ⟨3246926, by rfl⟩ : syracuseStep 4329235 = 6493853) B6493853
theorem B2027303 : Blo 1350994 2027303 := bstep (se 1 (by rfl) ⟨1520477, by rfl⟩ : syracuseStep 2027303 = 3040955) B3040955
theorem B19763021 : Blo 1350994 19763021 := bstep (se 3 (by rfl) ⟨3705566, by rfl⟩ : syracuseStep 19763021 = 7411133) B7411133
theorem B7696235 : Blo 1350994 7696235 := bstep (se 1 (by rfl) ⟨5772176, by rfl⟩ : syracuseStep 7696235 = 11544353) B11544353
theorem B2928505 : Blo 1350994 2928505 := bstep (se 2 (by rfl) ⟨1098189, by rfl⟩ : syracuseStep 2928505 = 2196379) B2196379
theorem B2027387 : Blo 1350994 2027387 := bstep (se 1 (by rfl) ⟨1520540, by rfl⟩ : syracuseStep 2027387 = 3041081) B3041081
theorem B2281439 : Blo 1350994 2281439 := bstep (se 1 (by rfl) ⟨1711079, by rfl⟩ : syracuseStep 2281439 = 3422159) B3422159
theorem B3043295 : Blo 1350994 3043295 := bstep (se 1 (by rfl) ⟨2282471, by rfl⟩ : syracuseStep 3043295 = 4564943) B4564943
theorem B32886809 : Blo 1350994 32886809 := bstep (se 2 (by rfl) ⟨12332553, by rfl⟩ : syracuseStep 32886809 = 24665107) B24665107
theorem B11546813 : Blo 1350994 11546813 := bstep (se 3 (by rfl) ⟨2165027, by rfl⟩ : syracuseStep 11546813 = 4330055) B4330055
theorem B4329737 : Blo 1350994 4329737 := bstep (se 2 (by rfl) ⟨1623651, by rfl⟩ : syracuseStep 4329737 = 3247303) B3247303
theorem B2027807 : Blo 1350994 2027807 := bstep (se 1 (by rfl) ⟨1520855, by rfl⟩ : syracuseStep 2027807 = 3041711) B3041711
theorem B2027831 : Blo 1350994 2027831 := bstep (se 1 (by rfl) ⟨1520873, by rfl⟩ : syracuseStep 2027831 = 3041747) B3041747
theorem B2281783 : Blo 1350994 2281783 := bstep (se 1 (by rfl) ⟨1711337, by rfl⟩ : syracuseStep 2281783 = 3422675) B3422675
theorem B2568503 : Blo 1350994 2568503 := bstep (se 1 (by rfl) ⟨1926377, by rfl⟩ : syracuseStep 2568503 = 3852755) B3852755
theorem B2027903 : Blo 1350994 2027903 := bstep (se 1 (by rfl) ⟨1520927, by rfl⟩ : syracuseStep 2027903 = 3041855) B3041855
theorem B2027975 : Blo 1350994 2027975 := bstep (se 1 (by rfl) ⟨1520981, by rfl⟩ : syracuseStep 2027975 = 3041963) B3041963
theorem B9744907 : Blo 1350994 9744907 := bstep (se 1 (by rfl) ⟨7308680, by rfl⟩ : syracuseStep 9744907 = 14617361) B14617361
theorem B35115565 : Blo 1350994 35115565 := bstep (se 3 (by rfl) ⟨6584168, by rfl⟩ : syracuseStep 35115565 = 13168337) B13168337
theorem B4108895 : Blo 1350994 4108895 := bstep (se 1 (by rfl) ⟨3081671, by rfl⟩ : syracuseStep 4108895 = 6163343) B6163343
theorem B2282087 : Blo 1350994 2282087 := bstep (se 1 (by rfl) ⟨1711565, by rfl⟩ : syracuseStep 2282087 = 3423131) B3423131
theorem B3469927 : Blo 1350994 3469927 := bstep (se 1 (by rfl) ⟨2602445, by rfl⟩ : syracuseStep 3469927 = 5204891) B5204891
theorem B3043943 : Blo 1350994 3043943 := bstep (se 1 (by rfl) ⟨2282957, by rfl⟩ : syracuseStep 3043943 = 4565915) B4565915
theorem B8663699 : Blo 1350994 8663699 := bstep (se 1 (by rfl) ⟨6497774, by rfl⟩ : syracuseStep 8663699 = 12995549) B12995549
theorem B24998657 : Blo 1350994 24998657 := bstep (se 2 (by rfl) ⟨9374496, by rfl⟩ : syracuseStep 24998657 = 18748993) B18748993
theorem B2282249 : Blo 1350994 2282249 := bstep (se 2 (by rfl) ⟨855843, by rfl⟩ : syracuseStep 2282249 = 1711687) B1711687
theorem B2028329 : Blo 1350994 2028329 := bstep (se 2 (by rfl) ⟨760623, by rfl⟩ : syracuseStep 2028329 = 1521247) B1521247
theorem B2028335 : Blo 1350994 2028335 := bstep (se 1 (by rfl) ⟨1521251, by rfl⟩ : syracuseStep 2028335 = 3042503) B3042503
theorem B6845309 : Blo 1350994 6845309 := bstep (se 3 (by rfl) ⟨1283495, by rfl⟩ : syracuseStep 6845309 = 2566991) B2566991
theorem B5772161 : Blo 1350994 5772161 := bstep (se 2 (by rfl) ⟨2164560, by rfl⟩ : syracuseStep 5772161 = 4329121) B4329121
theorem B2028455 : Blo 1350994 2028455 := bstep (se 1 (by rfl) ⟨1521341, by rfl⟩ : syracuseStep 2028455 = 3042683) B3042683
theorem B4559867 : Blo 1350994 4559867 := bstep (se 1 (by rfl) ⟨3419900, by rfl⟩ : syracuseStep 4559867 = 6839801) B6839801
theorem B1520635 : Blo 1350994 1520635 := bstep (se 1 (by rfl) ⟨1140476, by rfl⟩ : syracuseStep 1520635 = 2280953) B2280953
theorem B2028539 : Blo 1350994 2028539 := bstep (se 1 (by rfl) ⟨1521404, by rfl⟩ : syracuseStep 2028539 = 3042809) B3042809
theorem B2028599 : Blo 1350994 2028599 := bstep (se 1 (by rfl) ⟨1521449, by rfl⟩ : syracuseStep 2028599 = 3042899) B3042899
theorem B1520815 : Blo 1350994 1520815 := bstep (se 1 (by rfl) ⟨1140611, by rfl⟩ : syracuseStep 1520815 = 2281223) B2281223
theorem B2028719 : Blo 1350994 2028719 := bstep (se 1 (by rfl) ⟨1521539, by rfl⟩ : syracuseStep 2028719 = 3043079) B3043079
theorem B4560083 : Blo 1350994 4560083 := bstep (se 1 (by rfl) ⟨3420062, by rfl⟩ : syracuseStep 4560083 = 6840125) B6840125
theorem B24679703 : Blo 1350994 24679703 := bstep (se 1 (by rfl) ⟨18509777, by rfl⟩ : syracuseStep 24679703 = 37019555) B37019555
theorem B2282843 : Blo 1350994 2282843 := bstep (se 1 (by rfl) ⟨1712132, by rfl⟩ : syracuseStep 2282843 = 3424265) B3424265
theorem B10270151 : Blo 1350994 10270151 := bstep (se 1 (by rfl) ⟨7702613, by rfl⟩ : syracuseStep 10270151 = 15405227) B15405227
theorem B4560353 : Blo 1350994 4560353 := bstep (se 2 (by rfl) ⟨1710132, by rfl⟩ : syracuseStep 4560353 = 3420265) B3420265
theorem B2029127 : Blo 1350994 2029127 := bstep (se 1 (by rfl) ⟨1521845, by rfl⟩ : syracuseStep 2029127 = 3043691) B3043691
theorem B2283079 : Blo 1350994 2283079 := bstep (se 1 (by rfl) ⟨1712309, by rfl⟩ : syracuseStep 2283079 = 3424619) B3424619
theorem B43849349 : Blo 1350994 43849349 := bstep (se 4 (by rfl) ⟨4110876, by rfl⟩ : syracuseStep 43849349 = 8221753) B8221753
theorem B1521319 : Blo 1350994 1521319 := bstep (se 1 (by rfl) ⟨1140989, by rfl⟩ : syracuseStep 1521319 = 2281979) B2281979
theorem B2029223 : Blo 1350994 2029223 := bstep (se 1 (by rfl) ⟨1521917, by rfl⟩ : syracuseStep 2029223 = 3043835) B3043835
theorem B2029307 : Blo 1350994 2029307 := bstep (se 1 (by rfl) ⟨1521980, by rfl⟩ : syracuseStep 2029307 = 3043961) B3043961
theorem B2029343 : Blo 1350994 2029343 := bstep (se 1 (by rfl) ⟨1522007, by rfl⟩ : syracuseStep 2029343 = 3044015) B3044015
theorem B2029391 : Blo 1350994 2029391 := bstep (se 1 (by rfl) ⟨1522043, by rfl⟩ : syracuseStep 2029391 = 3044087) B3044087
theorem B15390647 : Blo 1350994 15390647 := bstep (se 1 (by rfl) ⟨11542985, by rfl⟩ : syracuseStep 15390647 = 23085971) B23085971
theorem B1521607 : Blo 1350994 1521607 := bstep (se 1 (by rfl) ⟨1141205, by rfl⟩ : syracuseStep 1521607 = 2282411) B2282411
theorem B17332217 : Blo 1350994 17332217 := bstep (se 2 (by rfl) ⟨6499581, by rfl⟩ : syracuseStep 17332217 = 12999163) B12999163
theorem B4561001 : Blo 1350994 4561001 := bstep (se 2 (by rfl) ⟨1710375, by rfl⟩ : syracuseStep 4561001 = 3420751) B3420751
theorem B3422351 : Blo 1350994 3422351 := bstep (se 1 (by rfl) ⟨2566763, by rfl⟩ : syracuseStep 3422351 = 5133527) B5133527
theorem B3250331 : Blo 1350994 3250331 := bstep (se 1 (by rfl) ⟨2437748, by rfl⟩ : syracuseStep 3250331 = 4875497) B4875497
theorem B17316119 : Blo 1350994 17316119 := bstep (se 1 (by rfl) ⟨12987089, by rfl⟩ : syracuseStep 17316119 = 25974179) B25974179
theorem B1521967 : Blo 1350994 1521967 := bstep (se 1 (by rfl) ⟨1141475, by rfl⟩ : syracuseStep 1521967 = 2282951) B2282951
theorem B1923689 : Blo 1350994 1923689 := bstep (se 2 (by rfl) ⟨721383, by rfl⟩ : syracuseStep 1923689 = 1442767) B1442767
theorem B3422857 : Blo 1350994 3422857 := bstep (se 2 (by rfl) ⟨1283571, by rfl⟩ : syracuseStep 3422857 = 2567143) B2567143
theorem B5134985 : Blo 1350994 5134985 := bstep (se 2 (by rfl) ⟨1925619, by rfl⟩ : syracuseStep 5134985 = 3851239) B3851239
theorem B38967965 : Blo 1350994 38967965 := bstep (se 3 (by rfl) ⟨7306493, by rfl⟩ : syracuseStep 38967965 = 14612987) B14612987
theorem B4873043 : Blo 1350994 4873043 := bstep (se 1 (by rfl) ⟨3654782, by rfl⟩ : syracuseStep 4873043 = 7309565) B7309565
theorem B4561865 : Blo 1350994 4561865 := bstep (se 2 (by rfl) ⟨1710699, by rfl⟩ : syracuseStep 4561865 = 3421399) B3421399
theorem B3849257 : Blo 1350994 3849257 := bstep (se 2 (by rfl) ⟨1443471, by rfl⟩ : syracuseStep 3849257 = 2886943) B2886943
theorem B19487789 : Blo 1350994 19487789 := bstep (se 3 (by rfl) ⟨3653960, by rfl⟩ : syracuseStep 19487789 = 7307921) B7307921
theorem B6847577 : Blo 1350994 6847577 := bstep (se 2 (by rfl) ⟨2567841, by rfl⟩ : syracuseStep 6847577 = 5135683) B5135683
theorem B11541689 : Blo 1350994 11541689 := bstep (se 2 (by rfl) ⟨4328133, by rfl⟩ : syracuseStep 11541689 = 8656267) B8656267
theorem B4562135 : Blo 1350994 4562135 := bstep (se 1 (by rfl) ⟨3421601, by rfl⟩ : syracuseStep 4562135 = 6843203) B6843203
theorem B7912733 : Blo 1350994 7912733 := bstep (se 3 (by rfl) ⟨1483637, by rfl⟩ : syracuseStep 7912733 = 2967275) B2967275
theorem B4111727 : Blo 1350994 4111727 := bstep (se 1 (by rfl) ⟨3083795, by rfl⟩ : syracuseStep 4111727 = 6167591) B6167591
theorem B12328325 : Blo 1350994 12328325 := bstep (se 4 (by rfl) ⟨1155780, by rfl⟩ : syracuseStep 12328325 = 2311561) B2311561
theorem B1351143 : Blo 1350994 1351143 := bstep (se 1 (by rfl) ⟨1013357, by rfl⟩ : syracuseStep 1351143 = 2026715) B2026715
theorem B1351259 : Blo 1350994 1351259 := bstep (se 1 (by rfl) ⟨1013444, by rfl⟩ : syracuseStep 1351259 = 2026889) B2026889
theorem B38002391 : Blo 1350994 38002391 := bstep (se 1 (by rfl) ⟨28501793, by rfl⟩ : syracuseStep 38002391 = 57003587) B57003587
theorem B6848225 : Blo 1350994 6848225 := bstep (se 2 (by rfl) ⟨2568084, by rfl⟩ : syracuseStep 6848225 = 5136169) B5136169
theorem B19545833 : Blo 1350994 19545833 := bstep (se 2 (by rfl) ⟨7329687, by rfl⟩ : syracuseStep 19545833 = 14659375) B14659375
theorem B4562675 : Blo 1350994 4562675 := bstep (se 1 (by rfl) ⟨3422006, by rfl⟩ : syracuseStep 4562675 = 6844013) B6844013
theorem B3423991 : Blo 1350994 3423991 := bstep (se 1 (by rfl) ⟨2567993, by rfl⟩ : syracuseStep 3423991 = 5135987) B5135987
theorem B1351495 : Blo 1350994 1351495 := bstep (se 1 (by rfl) ⟨1013621, by rfl⟩ : syracuseStep 1351495 = 2027243) B2027243
theorem B3850055 : Blo 1350994 3850055 := bstep (se 1 (by rfl) ⟨2887541, by rfl⟩ : syracuseStep 3850055 = 5775083) B5775083
theorem B1351647 : Blo 1350994 1351647 := bstep (se 1 (by rfl) ⟨1013735, by rfl⟩ : syracuseStep 1351647 = 2027471) B2027471
theorem B1351871 : Blo 1350994 1351871 := bstep (se 1 (by rfl) ⟨1013903, by rfl⟩ : syracuseStep 1351871 = 2027807) B2027807
theorem B26337473 : Blo 1350994 26337473 := bstep (se 2 (by rfl) ⟨9876552, by rfl⟩ : syracuseStep 26337473 = 19753105) B19753105
theorem B1351887 : Blo 1350994 1351887 := bstep (se 1 (by rfl) ⟨1013915, by rfl⟩ : syracuseStep 1351887 = 2027831) B2027831
theorem B1712335 : Blo 1350994 1712335 := bstep (se 1 (by rfl) ⟨1284251, by rfl⟩ : syracuseStep 1712335 = 2568503) B2568503
theorem B17318123 : Blo 1350994 17318123 := bstep (se 1 (by rfl) ⟨12988592, by rfl⟩ : syracuseStep 17318123 = 25977185) B25977185
theorem B1351935 : Blo 1350994 1351935 := bstep (se 1 (by rfl) ⟨1013951, by rfl⟩ : syracuseStep 1351935 = 2027903) B2027903
theorem B1351983 : Blo 1350994 1351983 := bstep (se 1 (by rfl) ⟨1013987, by rfl⟩ : syracuseStep 1351983 = 2027975) B2027975
theorem B5775799 : Blo 1350994 5775799 := bstep (se 1 (by rfl) ⟨4331849, by rfl⟩ : syracuseStep 5775799 = 8663699) B8663699
theorem B1352219 : Blo 1350994 1352219 := bstep (se 1 (by rfl) ⟨1014164, by rfl⟩ : syracuseStep 1352219 = 2028329) B2028329
theorem B1352223 : Blo 1350994 1352223 := bstep (se 1 (by rfl) ⟨1014167, by rfl⟩ : syracuseStep 1352223 = 2028335) B2028335
theorem B4563539 : Blo 1350994 4563539 := bstep (se 1 (by rfl) ⟨3422654, by rfl⟩ : syracuseStep 4563539 = 6845309) B6845309
theorem B1352303 : Blo 1350994 1352303 := bstep (se 1 (by rfl) ⟨1014227, by rfl⟩ : syracuseStep 1352303 = 2028455) B2028455
theorem B3039911 : Blo 1350994 3039911 := bstep (se 1 (by rfl) ⟨2279933, by rfl⟩ : syracuseStep 3039911 = 4559867) B4559867
theorem B1352359 : Blo 1350994 1352359 := bstep (se 1 (by rfl) ⟨1014269, by rfl⟩ : syracuseStep 1352359 = 2028539) B2028539
theorem B12993209 : Blo 1350994 12993209 := bstep (se 2 (by rfl) ⟨4872453, by rfl⟩ : syracuseStep 12993209 = 9744907) B9744907
theorem B1352399 : Blo 1350994 1352399 := bstep (se 1 (by rfl) ⟨1014299, by rfl⟩ : syracuseStep 1352399 = 2028599) B2028599
theorem B1352479 : Blo 1350994 1352479 := bstep (se 1 (by rfl) ⟨1014359, by rfl⟩ : syracuseStep 1352479 = 2028719) B2028719
theorem B3040055 : Blo 1350994 3040055 := bstep (se 1 (by rfl) ⟨2280041, by rfl⟩ : syracuseStep 3040055 = 4560083) B4560083
theorem B4563809 : Blo 1350994 4563809 := bstep (se 2 (by rfl) ⟨1711428, by rfl⟩ : syracuseStep 4563809 = 3422857) B3422857
theorem B3040235 : Blo 1350994 3040235 := bstep (se 1 (by rfl) ⟨2280176, by rfl⟩ : syracuseStep 3040235 = 4560353) B4560353
theorem B1352751 : Blo 1350994 1352751 := bstep (se 1 (by rfl) ⟨1014563, by rfl⟩ : syracuseStep 1352751 = 2029127) B2029127
theorem B1352815 : Blo 1350994 1352815 := bstep (se 1 (by rfl) ⟨1014611, by rfl⟩ : syracuseStep 1352815 = 2029223) B2029223
theorem B1352871 : Blo 1350994 1352871 := bstep (se 1 (by rfl) ⟨1014653, by rfl⟩ : syracuseStep 1352871 = 2029307) B2029307
theorem B1352895 : Blo 1350994 1352895 := bstep (se 1 (by rfl) ⟨1014671, by rfl⟩ : syracuseStep 1352895 = 2029343) B2029343
theorem B1352927 : Blo 1350994 1352927 := bstep (se 1 (by rfl) ⟨1014695, by rfl⟩ : syracuseStep 1352927 = 2029391) B2029391
theorem B3040667 : Blo 1350994 3040667 := bstep (se 1 (by rfl) ⟨2280500, by rfl⟩ : syracuseStep 3040667 = 4561001) B4561001
theorem B11544079 : Blo 1350994 11544079 := bstep (se 1 (by rfl) ⟨8658059, by rfl⟩ : syracuseStep 11544079 = 17316119) B17316119
theorem B7702067 : Blo 1350994 7702067 := bstep (se 1 (by rfl) ⟨5776550, by rfl⟩ : syracuseStep 7702067 = 11553101) B11553101
theorem B5129837 : Blo 1350994 5129837 := bstep (se 3 (by rfl) ⟨961844, by rfl⟩ : syracuseStep 5129837 = 1923689) B1923689
theorem B25978643 : Blo 1350994 25978643 := bstep (se 1 (by rfl) ⟨19483982, by rfl⟩ : syracuseStep 25978643 = 38967965) B38967965
theorem B3041243 : Blo 1350994 3041243 := bstep (se 1 (by rfl) ⟨2280932, by rfl⟩ : syracuseStep 3041243 = 4561865) B4561865
theorem B2566171 : Blo 1350994 2566171 := bstep (se 1 (by rfl) ⟨1924628, by rfl⟩ : syracuseStep 2566171 = 3849257) B3849257
theorem B4565051 : Blo 1350994 4565051 := bstep (se 1 (by rfl) ⟨3423788, by rfl⟩ : syracuseStep 4565051 = 6847577) B6847577
theorem B7694459 : Blo 1350994 7694459 := bstep (se 1 (by rfl) ⟨5770844, by rfl⟩ : syracuseStep 7694459 = 11541689) B11541689
theorem B3041423 : Blo 1350994 3041423 := bstep (se 1 (by rfl) ⟨2281067, by rfl⟩ : syracuseStep 3041423 = 4562135) B4562135
theorem B3041513 : Blo 1350994 3041513 := bstep (se 2 (by rfl) ⟨1140567, by rfl⟩ : syracuseStep 3041513 = 2281135) B2281135
theorem B8218883 : Blo 1350994 8218883 := bstep (se 1 (by rfl) ⟨6164162, by rfl⟩ : syracuseStep 8218883 = 12328325) B12328325
theorem B4565321 : Blo 1350994 4565321 := bstep (se 2 (by rfl) ⟨1711995, by rfl⟩ : syracuseStep 4565321 = 3423991) B3423991
theorem B4565483 : Blo 1350994 4565483 := bstep (se 1 (by rfl) ⟨3424112, by rfl⟩ : syracuseStep 4565483 = 6848225) B6848225
theorem B3041783 : Blo 1350994 3041783 := bstep (se 1 (by rfl) ⟨2281337, by rfl⟩ : syracuseStep 3041783 = 4562675) B4562675
theorem B2566703 : Blo 1350994 2566703 := bstep (se 1 (by rfl) ⟨1925027, by rfl⟩ : syracuseStep 2566703 = 3850055) B3850055
theorem B13175347 : Blo 1350994 13175347 := bstep (se 1 (by rfl) ⟨9881510, by rfl⟩ : syracuseStep 13175347 = 19763021) B19763021
theorem B5130823 : Blo 1350994 5130823 := bstep (se 1 (by rfl) ⟨3848117, by rfl⟩ : syracuseStep 5130823 = 7696235) B7696235
theorem B21924539 : Blo 1350994 21924539 := bstep (se 1 (by rfl) ⟨16443404, by rfl⟩ : syracuseStep 21924539 = 32886809) B32886809
theorem B2886491 : Blo 1350994 2886491 := bstep (se 1 (by rfl) ⟨2164868, by rfl⟩ : syracuseStep 2886491 = 4329737) B4329737
theorem B3247073 : Blo 1350994 3247073 := bstep (se 2 (by rfl) ⟨1217652, by rfl⟩ : syracuseStep 3247073 = 2435305) B2435305
theorem B2739263 : Blo 1350994 2739263 := bstep (se 1 (by rfl) ⟨2054447, by rfl⟩ : syracuseStep 2739263 = 4108895) B4108895
theorem B3042377 : Blo 1350994 3042377 := bstep (se 2 (by rfl) ⟨1140891, by rfl⟩ : syracuseStep 3042377 = 2281783) B2281783
theorem B9743753 : Blo 1350994 9743753 := bstep (se 2 (by rfl) ⟨3653907, by rfl⟩ : syracuseStep 9743753 = 7307815) B7307815
theorem B46820753 : Blo 1350994 46820753 := bstep (se 2 (by rfl) ⟨17557782, by rfl⟩ : syracuseStep 46820753 = 35115565) B35115565
theorem B2026907 : Blo 1350994 2026907 := bstep (se 1 (by rfl) ⟨1520180, by rfl⟩ : syracuseStep 2026907 = 3040361) B3040361
theorem B16453135 : Blo 1350994 16453135 := bstep (se 1 (by rfl) ⟨12339851, by rfl⟩ : syracuseStep 16453135 = 24679703) B24679703
theorem B10964605 : Blo 1350994 10964605 := bstep (se 3 (by rfl) ⟨2055863, by rfl⟩ : syracuseStep 10964605 = 4111727) B4111727
theorem B29232899 : Blo 1350994 29232899 := bstep (se 1 (by rfl) ⟨21924674, by rfl⟩ : syracuseStep 29232899 = 43849349) B43849349
theorem B2027327 : Blo 1350994 2027327 := bstep (se 1 (by rfl) ⟨1520495, by rfl⟩ : syracuseStep 2027327 = 3040991) B3040991
theorem B6500159 : Blo 1350994 6500159 := bstep (se 1 (by rfl) ⟨4875119, by rfl⟩ : syracuseStep 6500159 = 9750239) B9750239
theorem B10260431 : Blo 1350994 10260431 := bstep (se 1 (by rfl) ⟨7695323, by rfl⟩ : syracuseStep 10260431 = 15390647) B15390647
theorem B2027513 : Blo 1350994 2027513 := bstep (se 2 (by rfl) ⟨760317, by rfl⟩ : syracuseStep 2027513 = 1520635) B1520635
theorem B11554811 : Blo 1350994 11554811 := bstep (se 1 (by rfl) ⟨8666108, by rfl⟩ : syracuseStep 11554811 = 17332217) B17332217
theorem B6844499 : Blo 1350994 6844499 := bstep (se 1 (by rfl) ⟨5133374, by rfl⟩ : syracuseStep 6844499 = 10266749) B10266749
theorem B2281567 : Blo 1350994 2281567 := bstep (se 1 (by rfl) ⟨1711175, by rfl⟩ : syracuseStep 2281567 = 3422351) B3422351
theorem B2166887 : Blo 1350994 2166887 := bstep (se 1 (by rfl) ⟨1625165, by rfl⟩ : syracuseStep 2166887 = 3250331) B3250331
theorem B5771425 : Blo 1350994 5771425 := bstep (se 2 (by rfl) ⟨2164284, by rfl⟩ : syracuseStep 5771425 = 4328569) B4328569
theorem B2027753 : Blo 1350994 2027753 := bstep (se 2 (by rfl) ⟨760407, by rfl⟩ : syracuseStep 2027753 = 1520815) B1520815
theorem B2027879 : Blo 1350994 2027879 := bstep (se 1 (by rfl) ⟨1520909, by rfl⟩ : syracuseStep 2027879 = 3041819) B3041819
theorem B15389189 : Blo 1350994 15389189 := bstep (se 4 (by rfl) ⟨1442736, by rfl⟩ : syracuseStep 15389189 = 2885473) B2885473
theorem B3248695 : Blo 1350994 3248695 := bstep (se 1 (by rfl) ⟨2436521, by rfl⟩ : syracuseStep 3248695 = 4873043) B4873043
theorem B405262925 : Blo 1350994 405262925 := bstep (se 3 (by rfl) ⟨75986798, by rfl⟩ : syracuseStep 405262925 = 151973597) B151973597
theorem B4108907 : Blo 1350994 4108907 := bstep (se 1 (by rfl) ⟨3081680, by rfl⟩ : syracuseStep 4108907 = 6163361) B6163361
theorem B66663085 : Blo 1350994 66663085 := bstep (se 3 (by rfl) ⟨12499328, by rfl⟩ : syracuseStep 66663085 = 24998657) B24998657
theorem B3044105 : Blo 1350994 3044105 := bstep (se 2 (by rfl) ⟨1141539, by rfl⟩ : syracuseStep 3044105 = 2283079) B2283079
theorem B3044159 : Blo 1350994 3044159 := bstep (se 1 (by rfl) ⟨2283119, by rfl⟩ : syracuseStep 3044159 = 4566239) B4566239
theorem B2028425 : Blo 1350994 2028425 := bstep (se 2 (by rfl) ⟨760659, by rfl⟩ : syracuseStep 2028425 = 1521319) B1521319
theorem B5772313 : Blo 1350994 5772313 := bstep (se 2 (by rfl) ⟨2164617, by rfl⟩ : syracuseStep 5772313 = 4329235) B4329235
theorem B9254017 : Blo 1350994 9254017 := bstep (se 2 (by rfl) ⟨3470256, by rfl⟩ : syracuseStep 9254017 = 6940513) B6940513
theorem B25334927 : Blo 1350994 25334927 := bstep (se 1 (by rfl) ⟨19001195, by rfl⟩ : syracuseStep 25334927 = 38002391) B38002391
theorem B13030555 : Blo 1350994 13030555 := bstep (se 1 (by rfl) ⟨9772916, by rfl⟩ : syracuseStep 13030555 = 19545833) B19545833
theorem B3904673 : Blo 1350994 3904673 := bstep (se 2 (by rfl) ⟨1464252, by rfl⟩ : syracuseStep 3904673 = 2928505) B2928505
theorem B2028809 : Blo 1350994 2028809 := bstep (se 2 (by rfl) ⟨760803, by rfl⟩ : syracuseStep 2028809 = 1521607) B1521607
theorem B7697693 : Blo 1350994 7697693 := bstep (se 3 (by rfl) ⟨1443317, by rfl⟩ : syracuseStep 7697693 = 2886635) B2886635
theorem B1520959 : Blo 1350994 1520959 := bstep (se 1 (by rfl) ⟨1140719, by rfl⟩ : syracuseStep 1520959 = 2281439) B2281439
theorem B2028863 : Blo 1350994 2028863 := bstep (se 1 (by rfl) ⟨1521647, by rfl⟩ : syracuseStep 2028863 = 3043295) B3043295
theorem B2282863 : Blo 1350994 2282863 := bstep (se 1 (by rfl) ⟨1712147, by rfl⟩ : syracuseStep 2282863 = 3424295) B3424295
theorem B7697875 : Blo 1350994 7697875 := bstep (se 1 (by rfl) ⟨5773406, by rfl⟩ : syracuseStep 7697875 = 11546813) B11546813
theorem B2029289 : Blo 1350994 2029289 := bstep (se 2 (by rfl) ⟨760983, by rfl⟩ : syracuseStep 2029289 = 1521967) B1521967
theorem B1521391 : Blo 1350994 1521391 := bstep (se 1 (by rfl) ⟨1141043, by rfl⟩ : syracuseStep 1521391 = 2282087) B2282087
theorem B2029295 : Blo 1350994 2029295 := bstep (se 1 (by rfl) ⟨1521971, by rfl⟩ : syracuseStep 2029295 = 3043943) B3043943
theorem B1521499 : Blo 1350994 1521499 := bstep (se 1 (by rfl) ⟨1141124, by rfl⟩ : syracuseStep 1521499 = 2282249) B2282249
theorem B3848107 : Blo 1350994 3848107 := bstep (se 1 (by rfl) ⟨2886080, by rfl⟩ : syracuseStep 3848107 = 5772161) B5772161
theorem B21100621 : Blo 1350994 21100621 := bstep (se 3 (by rfl) ⟨3956366, by rfl⟩ : syracuseStep 21100621 = 7912733) B7912733
theorem B4626569 : Blo 1350994 4626569 := bstep (se 2 (by rfl) ⟨1734963, by rfl⟩ : syracuseStep 4626569 = 3469927) B3469927
theorem B1521895 : Blo 1350994 1521895 := bstep (se 1 (by rfl) ⟨1141421, by rfl⟩ : syracuseStep 1521895 = 2282843) B2282843
theorem B3250463 : Blo 1350994 3250463 := bstep (se 1 (by rfl) ⟨2437847, by rfl⟩ : syracuseStep 3250463 = 4875695) B4875695
theorem B6846767 : Blo 1350994 6846767 := bstep (se 1 (by rfl) ⟨5135075, by rfl⟩ : syracuseStep 6846767 = 10270151) B10270151
theorem B4561271 : Blo 1350994 4561271 := bstep (se 1 (by rfl) ⟨3420953, by rfl⟩ : syracuseStep 4561271 = 6841907) B6841907
theorem B19495397 : Blo 1350994 19495397 := bstep (se 4 (by rfl) ⟨1827693, by rfl⟩ : syracuseStep 19495397 = 3655387) B3655387
theorem B4873031 : Blo 1350994 4873031 := bstep (se 1 (by rfl) ⟨3654773, by rfl⟩ : syracuseStep 4873031 = 7309547) B7309547
theorem B5135183 : Blo 1350994 5135183 := bstep (se 1 (by rfl) ⟨3851387, by rfl⟩ : syracuseStep 5135183 = 7702775) B7702775
theorem B3423323 : Blo 1350994 3423323 := bstep (se 1 (by rfl) ⟨2567492, by rfl⟩ : syracuseStep 3423323 = 5134985) B5134985
theorem B11558159 : Blo 1350994 11558159 := bstep (se 1 (by rfl) ⟨8668619, by rfl⟩ : syracuseStep 11558159 = 17337239) B17337239
theorem B6495527 : Blo 1350994 6495527 := bstep (se 1 (by rfl) ⟨4871645, by rfl⟩ : syracuseStep 6495527 = 9743291) B9743291
theorem B12991859 : Blo 1350994 12991859 := bstep (se 1 (by rfl) ⟨9743894, by rfl⟩ : syracuseStep 12991859 = 19487789) B19487789
theorem B4562351 : Blo 1350994 4562351 := bstep (se 1 (by rfl) ⟨3421763, by rfl⟩ : syracuseStep 4562351 = 6843527) B6843527
theorem B1351119 : Blo 1350994 1351119 := bstep (se 1 (by rfl) ⟨1013339, by rfl⟩ : syracuseStep 1351119 = 2026679) B2026679
theorem B1351279 : Blo 1350994 1351279 := bstep (se 1 (by rfl) ⟨1013459, by rfl⟩ : syracuseStep 1351279 = 2026919) B2026919
theorem B5856889 : Blo 1350994 5856889 := bstep (se 2 (by rfl) ⟨2196333, by rfl⟩ : syracuseStep 5856889 = 4392667) B4392667
theorem B1351335 : Blo 1350994 1351335 := bstep (se 1 (by rfl) ⟨1013501, by rfl⟩ : syracuseStep 1351335 = 2027003) B2027003
theorem B1711783 : Blo 1350994 1711783 := bstep (se 1 (by rfl) ⟨1283837, by rfl⟩ : syracuseStep 1711783 = 2567675) B2567675
theorem B1351399 : Blo 1350994 1351399 := bstep (se 1 (by rfl) ⟨1013549, by rfl⟩ : syracuseStep 1351399 = 2027099) B2027099
theorem B1351455 : Blo 1350994 1351455 := bstep (se 1 (by rfl) ⟨1013591, by rfl⟩ : syracuseStep 1351455 = 2027183) B2027183
theorem B1351535 : Blo 1350994 1351535 := bstep (se 1 (by rfl) ⟨1013651, by rfl⟩ : syracuseStep 1351535 = 2027303) B2027303
theorem B1351591 : Blo 1350994 1351591 := bstep (se 1 (by rfl) ⟨1013693, by rfl⟩ : syracuseStep 1351591 = 2027387) B2027387
theorem B4562999 : Blo 1350994 4562999 := bstep (se 1 (by rfl) ⟨3422249, by rfl⟩ : syracuseStep 4562999 = 6844499) B6844499
theorem B1351835 : Blo 1350994 1351835 := bstep (se 1 (by rfl) ⟨1013876, by rfl⟩ : syracuseStep 1351835 = 2027753) B2027753
theorem B1351919 : Blo 1350994 1351919 := bstep (se 1 (by rfl) ⟨1013939, by rfl⟩ : syracuseStep 1351919 = 2027879) B2027879
theorem B12337517 : Blo 1350994 12337517 := bstep (se 3 (by rfl) ⟨2313284, by rfl⟩ : syracuseStep 12337517 = 4626569) B4626569
theorem B10412461 : Blo 1350994 10412461 := bstep (se 3 (by rfl) ⟨1952336, by rfl⟩ : syracuseStep 10412461 = 3904673) B3904673
theorem B7701065 : Blo 1350994 7701065 := bstep (se 2 (by rfl) ⟨2887899, by rfl⟩ : syracuseStep 7701065 = 5775799) B5775799
theorem B1352283 : Blo 1350994 1352283 := bstep (se 1 (by rfl) ⟨1014212, by rfl⟩ : syracuseStep 1352283 = 2028425) B2028425
theorem B8667901 : Blo 1350994 8667901 := bstep (se 3 (by rfl) ⟨1625231, by rfl⟩ : syracuseStep 8667901 = 3250463) B3250463
theorem B6841097 : Blo 1350994 6841097 := bstep (se 2 (by rfl) ⟨2565411, by rfl⟩ : syracuseStep 6841097 = 5130823) B5130823
theorem B1352539 : Blo 1350994 1352539 := bstep (se 1 (by rfl) ⟨1014404, by rfl⟩ : syracuseStep 1352539 = 2028809) B2028809
theorem B1352575 : Blo 1350994 1352575 := bstep (se 1 (by rfl) ⟨1014431, by rfl⟩ : syracuseStep 1352575 = 2028863) B2028863
theorem B88884113 : Blo 1350994 88884113 := bstep (se 2 (by rfl) ⟨33331542, by rfl⟩ : syracuseStep 88884113 = 66663085) B66663085
theorem B1352859 : Blo 1350994 1352859 := bstep (se 1 (by rfl) ⟨1014644, by rfl⟩ : syracuseStep 1352859 = 2029289) B2029289
theorem B1352863 : Blo 1350994 1352863 := bstep (se 1 (by rfl) ⟨1014647, by rfl⟩ : syracuseStep 1352863 = 2029295) B2029295
theorem B17319095 : Blo 1350994 17319095 := bstep (se 1 (by rfl) ⟨12989321, by rfl⟩ : syracuseStep 17319095 = 25978643) B25978643
theorem B5129639 : Blo 1350994 5129639 := bstep (se 1 (by rfl) ⟨3847229, by rfl⟩ : syracuseStep 5129639 = 7694459) B7694459
theorem B12338689 : Blo 1350994 12338689 := bstep (se 2 (by rfl) ⟨4627008, by rfl⟩ : syracuseStep 12338689 = 9254017) B9254017
theorem B4564511 : Blo 1350994 4564511 := bstep (se 1 (by rfl) ⟨3423383, by rfl⟩ : syracuseStep 4564511 = 6846767) B6846767
theorem B3040847 : Blo 1350994 3040847 := bstep (se 1 (by rfl) ⟨2280635, by rfl⟩ : syracuseStep 3040847 = 4561271) B4561271
theorem B14616359 : Blo 1350994 14616359 := bstep (se 1 (by rfl) ⟨10962269, by rfl⟩ : syracuseStep 14616359 = 21924539) B21924539
theorem B2164715 : Blo 1350994 2164715 := bstep (se 1 (by rfl) ⟨1623536, by rfl⟩ : syracuseStep 2164715 = 3247073) B3247073
theorem B7809185 : Blo 1350994 7809185 := bstep (se 2 (by rfl) ⟨2928444, by rfl⟩ : syracuseStep 7809185 = 5856889) B5856889
theorem B8661239 : Blo 1350994 8661239 := bstep (se 1 (by rfl) ⟨6495929, by rfl⟩ : syracuseStep 8661239 = 12991859) B12991859
theorem B31213835 : Blo 1350994 31213835 := bstep (se 1 (by rfl) ⟨23410376, by rfl⟩ : syracuseStep 31213835 = 46820753) B46820753
theorem B3041567 : Blo 1350994 3041567 := bstep (se 1 (by rfl) ⟨2281175, by rfl⟩ : syracuseStep 3041567 = 4562351) B4562351
theorem B5130809 : Blo 1350994 5130809 := bstep (se 2 (by rfl) ⟨1924053, by rfl⟩ : syracuseStep 5130809 = 3848107) B3848107
theorem B7703207 : Blo 1350994 7703207 := bstep (se 1 (by rfl) ⟨5777405, by rfl⟩ : syracuseStep 7703207 = 11554811) B11554811
theorem B1444591 : Blo 1350994 1444591 := bstep (se 1 (by rfl) ⟨1083443, by rfl⟩ : syracuseStep 1444591 = 2166887) B2166887
theorem B28134161 : Blo 1350994 28134161 := bstep (se 2 (by rfl) ⟨10550310, by rfl⟩ : syracuseStep 28134161 = 21100621) B21100621
theorem B3042089 : Blo 1350994 3042089 := bstep (se 2 (by rfl) ⟨1140783, by rfl⟩ : syracuseStep 3042089 = 2281567) B2281567
theorem B17558315 : Blo 1350994 17558315 := bstep (se 1 (by rfl) ⟨13168736, by rfl⟩ : syracuseStep 17558315 = 26337473) B26337473
theorem B11545415 : Blo 1350994 11545415 := bstep (se 1 (by rfl) ⟨8659061, by rfl⟩ : syracuseStep 11545415 = 17318123) B17318123
theorem B7695233 : Blo 1350994 7695233 := bstep (se 2 (by rfl) ⟨2885712, by rfl⟩ : syracuseStep 7695233 = 5771425) B5771425
theorem B10259459 : Blo 1350994 10259459 := bstep (se 1 (by rfl) ⟨7694594, by rfl⟩ : syracuseStep 10259459 = 15389189) B15389189
theorem B270175283 : Blo 1350994 270175283 := bstep (se 1 (by rfl) ⟨202631462, by rfl⟩ : syracuseStep 270175283 = 405262925) B405262925
theorem B3042359 : Blo 1350994 3042359 := bstep (se 1 (by rfl) ⟨2281769, by rfl⟩ : syracuseStep 3042359 = 4563539) B4563539
theorem B2739271 : Blo 1350994 2739271 := bstep (se 1 (by rfl) ⟨2054453, by rfl⟩ : syracuseStep 2739271 = 4108907) B4108907
theorem B2026607 : Blo 1350994 2026607 := bstep (se 1 (by rfl) ⟨1519955, by rfl⟩ : syracuseStep 2026607 = 3039911) B3039911
theorem B8662139 : Blo 1350994 8662139 := bstep (se 1 (by rfl) ⟨6496604, by rfl⟩ : syracuseStep 8662139 = 12993209) B12993209
theorem B2026703 : Blo 1350994 2026703 := bstep (se 1 (by rfl) ⟨1520027, by rfl⟩ : syracuseStep 2026703 = 3040055) B3040055
theorem B3042539 : Blo 1350994 3042539 := bstep (se 1 (by rfl) ⟨2281904, by rfl⟩ : syracuseStep 3042539 = 4563809) B4563809
theorem B2026823 : Blo 1350994 2026823 := bstep (se 1 (by rfl) ⟨1520117, by rfl⟩ : syracuseStep 2026823 = 3040235) B3040235
theorem B17567129 : Blo 1350994 17567129 := bstep (se 2 (by rfl) ⟨6587673, by rfl⟩ : syracuseStep 17567129 = 13175347) B13175347
theorem B5131795 : Blo 1350994 5131795 := bstep (se 1 (by rfl) ⟨3848846, by rfl⟩ : syracuseStep 5131795 = 7697693) B7697693
theorem B2027111 : Blo 1350994 2027111 := bstep (se 1 (by rfl) ⟨1520333, by rfl⟩ : syracuseStep 2027111 = 3040667) B3040667
theorem B3419891 : Blo 1350994 3419891 := bstep (se 1 (by rfl) ⟨2564918, by rfl⟩ : syracuseStep 3419891 = 5129837) B5129837
theorem B2027495 : Blo 1350994 2027495 := bstep (se 1 (by rfl) ⟨1520621, by rfl⟩ : syracuseStep 2027495 = 3041243) B3041243
theorem B7696417 : Blo 1350994 7696417 := bstep (se 2 (by rfl) ⟨2886156, by rfl⟩ : syracuseStep 7696417 = 5772313) B5772313
theorem B3043367 : Blo 1350994 3043367 := bstep (se 1 (by rfl) ⟨2282525, by rfl⟩ : syracuseStep 3043367 = 4565051) B4565051
theorem B2027615 : Blo 1350994 2027615 := bstep (se 1 (by rfl) ⟨1520711, by rfl⟩ : syracuseStep 2027615 = 3041423) B3041423
theorem B2027675 : Blo 1350994 2027675 := bstep (se 1 (by rfl) ⟨1520756, by rfl⟩ : syracuseStep 2027675 = 3041513) B3041513
theorem B3043547 : Blo 1350994 3043547 := bstep (se 1 (by rfl) ⟨2282660, by rfl⟩ : syracuseStep 3043547 = 4565321) B4565321
theorem B12996931 : Blo 1350994 12996931 := bstep (se 1 (by rfl) ⟨9747698, by rfl⟩ : syracuseStep 12996931 = 19495397) B19495397
theorem B3043655 : Blo 1350994 3043655 := bstep (se 1 (by rfl) ⟨2282741, by rfl⟩ : syracuseStep 3043655 = 4565483) B4565483
theorem B2027855 : Blo 1350994 2027855 := bstep (se 1 (by rfl) ⟨1520891, by rfl⟩ : syracuseStep 2027855 = 3041783) B3041783
theorem B2027945 : Blo 1350994 2027945 := bstep (se 2 (by rfl) ⟨760479, by rfl⟩ : syracuseStep 2027945 = 1520959) B1520959
theorem B3043817 : Blo 1350994 3043817 := bstep (se 2 (by rfl) ⟨1141431, by rfl⟩ : syracuseStep 3043817 = 2282863) B2282863
theorem B3248687 : Blo 1350994 3248687 := bstep (se 1 (by rfl) ⟨2436515, by rfl⟩ : syracuseStep 3248687 = 4873031) B4873031
theorem B2028251 : Blo 1350994 2028251 := bstep (se 1 (by rfl) ⟨1521188, by rfl⟩ : syracuseStep 2028251 = 3042377) B3042377
theorem B2282215 : Blo 1350994 2282215 := bstep (se 1 (by rfl) ⟨1711661, by rfl⟩ : syracuseStep 2282215 = 3423323) B3423323
theorem B14619473 : Blo 1350994 14619473 := bstep (se 2 (by rfl) ⟨5482302, by rfl⟩ : syracuseStep 14619473 = 10964605) B10964605
theorem B7705439 : Blo 1350994 7705439 := bstep (se 1 (by rfl) ⟨5779079, by rfl⟩ : syracuseStep 7705439 = 11558159) B11558159
theorem B4330351 : Blo 1350994 4330351 := bstep (se 1 (by rfl) ⟨3247763, by rfl⟩ : syracuseStep 4330351 = 6495527) B6495527
theorem B2282377 : Blo 1350994 2282377 := bstep (se 2 (by rfl) ⟨855891, by rfl⟩ : syracuseStep 2282377 = 1711783) B1711783
theorem B2028521 : Blo 1350994 2028521 := bstep (se 2 (by rfl) ⟨760695, by rfl⟩ : syracuseStep 2028521 = 1521391) B1521391
theorem B2028665 : Blo 1350994 2028665 := bstep (se 2 (by rfl) ⟨760749, by rfl⟩ : syracuseStep 2028665 = 1521499) B1521499
theorem B3421561 : Blo 1350994 3421561 := bstep (se 2 (by rfl) ⟨1283085, by rfl⟩ : syracuseStep 3421561 = 2566171) B2566171
theorem B7304701 : Blo 1350994 7304701 := bstep (se 3 (by rfl) ⟨1369631, by rfl⟩ : syracuseStep 7304701 = 2739263) B2739263
theorem B2283113 : Blo 1350994 2283113 := bstep (se 2 (by rfl) ⟨856167, by rfl⟩ : syracuseStep 2283113 = 1712335) B1712335
theorem B2029193 : Blo 1350994 2029193 := bstep (se 2 (by rfl) ⟨760947, by rfl⟩ : syracuseStep 2029193 = 1521895) B1521895
theorem B2029403 : Blo 1350994 2029403 := bstep (se 1 (by rfl) ⟨1522052, by rfl⟩ : syracuseStep 2029403 = 3044105) B3044105
theorem B2029439 : Blo 1350994 2029439 := bstep (se 1 (by rfl) ⟨1522079, by rfl⟩ : syracuseStep 2029439 = 3044159) B3044159
theorem B4331593 : Blo 1350994 4331593 := bstep (se 2 (by rfl) ⟨1624347, by rfl⟩ : syracuseStep 4331593 = 3248695) B3248695
theorem B16889951 : Blo 1350994 16889951 := bstep (se 1 (by rfl) ⟨12667463, by rfl⟩ : syracuseStep 16889951 = 25334927) B25334927
theorem B5134711 : Blo 1350994 5134711 := bstep (se 1 (by rfl) ⟨3851033, by rfl⟩ : syracuseStep 5134711 = 7702067) B7702067
theorem B5479255 : Blo 1350994 5479255 := bstep (se 1 (by rfl) ⟨4109441, by rfl⟩ : syracuseStep 5479255 = 8218883) B8218883
theorem B17374073 : Blo 1350994 17374073 := bstep (se 2 (by rfl) ⟨6515277, by rfl⟩ : syracuseStep 17374073 = 13030555) B13030555
theorem B1711135 : Blo 1350994 1711135 := bstep (se 1 (by rfl) ⟨1283351, by rfl⟩ : syracuseStep 1711135 = 2566703) B2566703
theorem B3423455 : Blo 1350994 3423455 := bstep (se 1 (by rfl) ⟨2567591, by rfl⟩ : syracuseStep 3423455 = 5135183) B5135183
theorem B1924327 : Blo 1350994 1924327 := bstep (se 1 (by rfl) ⟨1443245, by rfl⟩ : syracuseStep 1924327 = 2886491) B2886491
theorem B10263833 : Blo 1350994 10263833 := bstep (se 2 (by rfl) ⟨3848937, by rfl⟩ : syracuseStep 10263833 = 7697875) B7697875
theorem B15392105 : Blo 1350994 15392105 := bstep (se 2 (by rfl) ⟨5772039, by rfl⟩ : syracuseStep 15392105 = 11544079) B11544079
theorem B21937513 : Blo 1350994 21937513 := bstep (se 2 (by rfl) ⟨8226567, by rfl⟩ : syracuseStep 21937513 = 16453135) B16453135
theorem B6495835 : Blo 1350994 6495835 := bstep (se 1 (by rfl) ⟨4871876, by rfl⟩ : syracuseStep 6495835 = 9743753) B9743753
theorem B1351271 : Blo 1350994 1351271 := bstep (se 1 (by rfl) ⟨1013453, by rfl⟩ : syracuseStep 1351271 = 2026907) B2026907
theorem B19488599 : Blo 1350994 19488599 := bstep (se 1 (by rfl) ⟨14616449, by rfl⟩ : syracuseStep 19488599 = 29232899) B29232899
theorem B1351551 : Blo 1350994 1351551 := bstep (se 1 (by rfl) ⟨1013663, by rfl⟩ : syracuseStep 1351551 = 2027327) B2027327
theorem B4333439 : Blo 1350994 4333439 := bstep (se 1 (by rfl) ⟨3250079, by rfl⟩ : syracuseStep 4333439 = 6500159) B6500159
theorem B6840287 : Blo 1350994 6840287 := bstep (se 1 (by rfl) ⟨5130215, by rfl⟩ : syracuseStep 6840287 = 10260431) B10260431
theorem B1351675 : Blo 1350994 1351675 := bstep (se 1 (by rfl) ⟨1013756, by rfl⟩ : syracuseStep 1351675 = 2027513) B2027513
theorem B1351743 : Blo 1350994 1351743 := bstep (se 1 (by rfl) ⟨1013807, by rfl⟩ : syracuseStep 1351743 = 2027615) B2027615
theorem B5775457 : Blo 1350994 5775457 := bstep (se 2 (by rfl) ⟨2165796, by rfl⟩ : syracuseStep 5775457 = 4331593) B4331593
theorem B1351783 : Blo 1350994 1351783 := bstep (se 1 (by rfl) ⟨1013837, by rfl⟩ : syracuseStep 1351783 = 2027675) B2027675
theorem B1351903 : Blo 1350994 1351903 := bstep (se 1 (by rfl) ⟨1013927, by rfl⟩ : syracuseStep 1351903 = 2027855) B2027855
theorem B8225011 : Blo 1350994 8225011 := bstep (se 1 (by rfl) ⟨6168758, by rfl⟩ : syracuseStep 8225011 = 12337517) B12337517
theorem B1351963 : Blo 1350994 1351963 := bstep (se 1 (by rfl) ⟨1013972, by rfl⟩ : syracuseStep 1351963 = 2027945) B2027945
theorem B1352167 : Blo 1350994 1352167 := bstep (se 1 (by rfl) ⟨1014125, by rfl⟩ : syracuseStep 1352167 = 2028251) B2028251
theorem B5136959 : Blo 1350994 5136959 := bstep (se 1 (by rfl) ⟨3852719, by rfl⟩ : syracuseStep 5136959 = 7705439) B7705439
theorem B1352347 : Blo 1350994 1352347 := bstep (se 1 (by rfl) ⟨1014260, by rfl⟩ : syracuseStep 1352347 = 2028521) B2028521
theorem B1352443 : Blo 1350994 1352443 := bstep (se 1 (by rfl) ⟨1014332, by rfl⟩ : syracuseStep 1352443 = 2028665) B2028665
theorem B1926121 : Blo 1350994 1926121 := bstep (se 2 (by rfl) ⟨722295, by rfl⟩ : syracuseStep 1926121 = 1444591) B1444591
theorem B1352795 : Blo 1350994 1352795 := bstep (se 1 (by rfl) ⟨1014596, by rfl⟩ : syracuseStep 1352795 = 2029193) B2029193
theorem B1352935 : Blo 1350994 1352935 := bstep (se 1 (by rfl) ⟨1014701, by rfl⟩ : syracuseStep 1352935 = 2029403) B2029403
theorem B1352959 : Blo 1350994 1352959 := bstep (se 1 (by rfl) ⟨1014719, by rfl⟩ : syracuseStep 1352959 = 2029439) B2029439
theorem B1443143 : Blo 1350994 1443143 := bstep (se 1 (by rfl) ⟨1082357, by rfl⟩ : syracuseStep 1443143 = 2164715) B2164715
theorem B20809223 : Blo 1350994 20809223 := bstep (se 1 (by rfl) ⟨15606917, by rfl⟩ : syracuseStep 20809223 = 31213835) B31213835
theorem B2565769 : Blo 1350994 2565769 := bstep (se 2 (by rfl) ⟨962163, by rfl⟩ : syracuseStep 2565769 = 1924327) B1924327
theorem B29222693 : Blo 1350994 29222693 := bstep (se 4 (by rfl) ⟨2739627, by rfl⟩ : syracuseStep 29222693 = 5479255) B5479255
theorem B5130155 : Blo 1350994 5130155 := bstep (se 1 (by rfl) ⟨3847616, by rfl⟩ : syracuseStep 5130155 = 7695233) B7695233
theorem B16451585 : Blo 1350994 16451585 := bstep (se 2 (by rfl) ⟨6169344, by rfl⟩ : syracuseStep 16451585 = 12338689) B12338689
theorem B6842393 : Blo 1350994 6842393 := bstep (se 2 (by rfl) ⟨2565897, by rfl⟩ : syracuseStep 6842393 = 5131795) B5131795
theorem B8661113 : Blo 1350994 8661113 := bstep (se 2 (by rfl) ⟨3247917, by rfl⟩ : syracuseStep 8661113 = 6495835) B6495835
theorem B6842555 : Blo 1350994 6842555 := bstep (se 1 (by rfl) ⟨5131916, by rfl⟩ : syracuseStep 6842555 = 10263833) B10263833
theorem B2279927 : Blo 1350994 2279927 := bstep (se 1 (by rfl) ⟨1709945, by rfl⟩ : syracuseStep 2279927 = 3419891) B3419891
theorem B3041999 : Blo 1350994 3041999 := bstep (se 1 (by rfl) ⟨2281499, by rfl⟩ : syracuseStep 3041999 = 4562999) B4562999
theorem B2165791 : Blo 1350994 2165791 := bstep (se 1 (by rfl) ⟨1624343, by rfl⟩ : syracuseStep 2165791 = 3248687) B3248687
theorem B17329241 : Blo 1350994 17329241 := bstep (se 2 (by rfl) ⟨6498465, by rfl⟩ : syracuseStep 17329241 = 12996931) B12996931
theorem B11546063 : Blo 1350994 11546063 := bstep (se 1 (by rfl) ⟨8659547, by rfl⟩ : syracuseStep 11546063 = 17319095) B17319095
theorem B3419759 : Blo 1350994 3419759 := bstep (se 1 (by rfl) ⟨2564819, by rfl⟩ : syracuseStep 3419759 = 5129639) B5129639
theorem B3042953 : Blo 1350994 3042953 := bstep (se 2 (by rfl) ⟨1141107, by rfl⟩ : syracuseStep 3042953 = 2282215) B2282215
theorem B3043007 : Blo 1350994 3043007 := bstep (se 1 (by rfl) ⟨2282255, by rfl⟩ : syracuseStep 3043007 = 4564511) B4564511
theorem B2027231 : Blo 1350994 2027231 := bstep (se 1 (by rfl) ⟨1520423, by rfl⟩ : syracuseStep 2027231 = 3040847) B3040847
theorem B46845677 : Blo 1350994 46845677 := bstep (se 3 (by rfl) ⟨8783564, by rfl⟩ : syracuseStep 46845677 = 17567129) B17567129
theorem B3043169 : Blo 1350994 3043169 := bstep (se 2 (by rfl) ⟨1141188, by rfl⟩ : syracuseStep 3043169 = 2282377) B2282377
theorem B9744239 : Blo 1350994 9744239 := bstep (se 1 (by rfl) ⟨7308179, by rfl⟩ : syracuseStep 9744239 = 14616359) B14616359
theorem B2281513 : Blo 1350994 2281513 := bstep (se 2 (by rfl) ⟨855567, by rfl⟩ : syracuseStep 2281513 = 1711135) B1711135
theorem B11259967 : Blo 1350994 11259967 := bstep (se 1 (by rfl) ⟨8444975, by rfl⟩ : syracuseStep 11259967 = 16889951) B16889951
theorem B5206123 : Blo 1350994 5206123 := bstep (se 1 (by rfl) ⟨3904592, by rfl⟩ : syracuseStep 5206123 = 7809185) B7809185
theorem B2027711 : Blo 1350994 2027711 := bstep (se 1 (by rfl) ⟨1520783, by rfl⟩ : syracuseStep 2027711 = 3041567) B3041567
theorem B3420539 : Blo 1350994 3420539 := bstep (se 1 (by rfl) ⟨2565404, by rfl⟩ : syracuseStep 3420539 = 5130809) B5130809
theorem B29250017 : Blo 1350994 29250017 := bstep (se 2 (by rfl) ⟨10968756, by rfl⟩ : syracuseStep 29250017 = 21937513) B21937513
theorem B18756107 : Blo 1350994 18756107 := bstep (se 1 (by rfl) ⟨14067080, by rfl⟩ : syracuseStep 18756107 = 28134161) B28134161
theorem B2028059 : Blo 1350994 2028059 := bstep (se 1 (by rfl) ⟨1521044, by rfl⟩ : syracuseStep 2028059 = 3042089) B3042089
theorem B7696943 : Blo 1350994 7696943 := bstep (se 1 (by rfl) ⟨5772707, by rfl⟩ : syracuseStep 7696943 = 11545415) B11545415
theorem B2028239 : Blo 1350994 2028239 := bstep (se 1 (by rfl) ⟨1521179, by rfl⟩ : syracuseStep 2028239 = 3042359) B3042359
theorem B2282303 : Blo 1350994 2282303 := bstep (se 1 (by rfl) ⟨1711727, by rfl⟩ : syracuseStep 2282303 = 3423455) B3423455
theorem B2028359 : Blo 1350994 2028359 := bstep (se 1 (by rfl) ⟨1521269, by rfl⟩ : syracuseStep 2028359 = 3042539) B3042539
theorem B10261403 : Blo 1350994 10261403 := bstep (se 1 (by rfl) ⟨7696052, by rfl⟩ : syracuseStep 10261403 = 15392105) B15392105
theorem B46330861 : Blo 1350994 46330861 := bstep (se 3 (by rfl) ⟨8687036, by rfl⟩ : syracuseStep 46330861 = 17374073) B17374073
theorem B237024301 : Blo 1350994 237024301 := bstep (se 3 (by rfl) ⟨44442056, by rfl⟩ : syracuseStep 237024301 = 88884113) B88884113
theorem B2888959 : Blo 1350994 2888959 := bstep (se 1 (by rfl) ⟨2166719, by rfl⟩ : syracuseStep 2888959 = 4333439) B4333439
theorem B4560191 : Blo 1350994 4560191 := bstep (se 1 (by rfl) ⟨3420143, by rfl⟩ : syracuseStep 4560191 = 6840287) B6840287
theorem B2028911 : Blo 1350994 2028911 := bstep (se 1 (by rfl) ⟨1521683, by rfl⟩ : syracuseStep 2028911 = 3043367) B3043367
theorem B10261889 : Blo 1350994 10261889 := bstep (se 2 (by rfl) ⟨3848208, by rfl⟩ : syracuseStep 10261889 = 7696417) B7696417
theorem B2029031 : Blo 1350994 2029031 := bstep (se 1 (by rfl) ⟨1521773, by rfl⟩ : syracuseStep 2029031 = 3043547) B3043547
theorem B2029103 : Blo 1350994 2029103 := bstep (se 1 (by rfl) ⟨1521827, by rfl⟩ : syracuseStep 2029103 = 3043655) B3043655
theorem B2029211 : Blo 1350994 2029211 := bstep (se 1 (by rfl) ⟨1521908, by rfl⟩ : syracuseStep 2029211 = 3043817) B3043817
theorem B5134043 : Blo 1350994 5134043 := bstep (se 1 (by rfl) ⟨3850532, by rfl⟩ : syracuseStep 5134043 = 7701065) B7701065
theorem B6846281 : Blo 1350994 6846281 := bstep (se 2 (by rfl) ⟨2567355, by rfl⟩ : syracuseStep 6846281 = 5134711) B5134711
theorem B4560731 : Blo 1350994 4560731 := bstep (se 1 (by rfl) ⟨3420548, by rfl⟩ : syracuseStep 4560731 = 6841097) B6841097
theorem B9746315 : Blo 1350994 9746315 := bstep (se 1 (by rfl) ⟨7309736, by rfl⟩ : syracuseStep 9746315 = 14619473) B14619473
theorem B13883281 : Blo 1350994 13883281 := bstep (se 2 (by rfl) ⟨5206230, by rfl⟩ : syracuseStep 13883281 = 10412461) B10412461
theorem B11557201 : Blo 1350994 11557201 := bstep (se 2 (by rfl) ⟨4333950, by rfl⟩ : syracuseStep 11557201 = 8667901) B8667901
theorem B1522075 : Blo 1350994 1522075 := bstep (se 1 (by rfl) ⟨1141556, by rfl⟩ : syracuseStep 1522075 = 2283113) B2283113
theorem B5773801 : Blo 1350994 5773801 := bstep (se 2 (by rfl) ⟨2165175, by rfl⟩ : syracuseStep 5773801 = 4330351) B4330351
theorem B3652361 : Blo 1350994 3652361 := bstep (se 2 (by rfl) ⟨1369635, by rfl⟩ : syracuseStep 3652361 = 2739271) B2739271
theorem B5774159 : Blo 1350994 5774159 := bstep (se 1 (by rfl) ⟨4330619, by rfl⟩ : syracuseStep 5774159 = 8661239) B8661239
theorem B5135471 : Blo 1350994 5135471 := bstep (se 1 (by rfl) ⟨3851603, by rfl⟩ : syracuseStep 5135471 = 7703207) B7703207
theorem B4562081 : Blo 1350994 4562081 := bstep (se 2 (by rfl) ⟨1710780, by rfl⟩ : syracuseStep 4562081 = 3421561) B3421561
theorem B11705543 : Blo 1350994 11705543 := bstep (se 1 (by rfl) ⟨8779157, by rfl⟩ : syracuseStep 11705543 = 17558315) B17558315
theorem B9739601 : Blo 1350994 9739601 := bstep (se 2 (by rfl) ⟨3652350, by rfl⟩ : syracuseStep 9739601 = 7304701) B7304701
theorem B6839639 : Blo 1350994 6839639 := bstep (se 1 (by rfl) ⟨5129729, by rfl⟩ : syracuseStep 6839639 = 10259459) B10259459
theorem B180116855 : Blo 1350994 180116855 := bstep (se 1 (by rfl) ⟨135087641, by rfl⟩ : syracuseStep 180116855 = 270175283) B270175283
theorem B1351071 : Blo 1350994 1351071 := bstep (se 1 (by rfl) ⟨1013303, by rfl⟩ : syracuseStep 1351071 = 2026607) B2026607
theorem B5774759 : Blo 1350994 5774759 := bstep (se 1 (by rfl) ⟨4331069, by rfl⟩ : syracuseStep 5774759 = 8662139) B8662139
theorem B1351135 : Blo 1350994 1351135 := bstep (se 1 (by rfl) ⟨1013351, by rfl⟩ : syracuseStep 1351135 = 2026703) B2026703
theorem B1351215 : Blo 1350994 1351215 := bstep (se 1 (by rfl) ⟨1013411, by rfl⟩ : syracuseStep 1351215 = 2026823) B2026823
theorem B1351407 : Blo 1350994 1351407 := bstep (se 1 (by rfl) ⟨1013555, by rfl⟩ : syracuseStep 1351407 = 2027111) B2027111
theorem B12992399 : Blo 1350994 12992399 := bstep (se 1 (by rfl) ⟨9744299, by rfl⟩ : syracuseStep 12992399 = 19488599) B19488599
theorem B1351663 : Blo 1350994 1351663 := bstep (se 1 (by rfl) ⟨1013747, by rfl⟩ : syracuseStep 1351663 = 2027495) B2027495
theorem B1351807 : Blo 1350994 1351807 := bstep (se 1 (by rfl) ⟨1013855, by rfl⟩ : syracuseStep 1351807 = 2027711) B2027711
theorem B7700609 : Blo 1350994 7700609 := bstep (se 2 (by rfl) ⟨2887728, by rfl⟩ : syracuseStep 7700609 = 5775457) B5775457
theorem B1352039 : Blo 1350994 1352039 := bstep (se 1 (by rfl) ⟨1014029, by rfl⟩ : syracuseStep 1352039 = 2028059) B2028059
theorem B3424639 : Blo 1350994 3424639 := bstep (se 1 (by rfl) ⟨2568479, by rfl⟩ : syracuseStep 3424639 = 5136959) B5136959
theorem B15409601 : Blo 1350994 15409601 := bstep (se 2 (by rfl) ⟨5778600, by rfl⟩ : syracuseStep 15409601 = 11557201) B11557201
theorem B1352159 : Blo 1350994 1352159 := bstep (se 1 (by rfl) ⟨1014119, by rfl⟩ : syracuseStep 1352159 = 2028239) B2028239
theorem B1352239 : Blo 1350994 1352239 := bstep (se 1 (by rfl) ⟨1014179, by rfl⟩ : syracuseStep 1352239 = 2028359) B2028359
theorem B6840935 : Blo 1350994 6840935 := bstep (se 1 (by rfl) ⟨5130701, by rfl⟩ : syracuseStep 6840935 = 10261403) B10261403
theorem B3040127 : Blo 1350994 3040127 := bstep (se 1 (by rfl) ⟨2280095, by rfl⟩ : syracuseStep 3040127 = 4560191) B4560191
theorem B1352607 : Blo 1350994 1352607 := bstep (se 1 (by rfl) ⟨1014455, by rfl⟩ : syracuseStep 1352607 = 2028911) B2028911
theorem B6841259 : Blo 1350994 6841259 := bstep (se 1 (by rfl) ⟨5130944, by rfl⟩ : syracuseStep 6841259 = 10261889) B10261889
theorem B1352687 : Blo 1350994 1352687 := bstep (se 1 (by rfl) ⟨1014515, by rfl⟩ : syracuseStep 1352687 = 2029031) B2029031
theorem B1352735 : Blo 1350994 1352735 := bstep (se 1 (by rfl) ⟨1014551, by rfl⟩ : syracuseStep 1352735 = 2029103) B2029103
theorem B1352807 : Blo 1350994 1352807 := bstep (se 1 (by rfl) ⟨1014605, by rfl⟩ : syracuseStep 1352807 = 2029211) B2029211
theorem B19481795 : Blo 1350994 19481795 := bstep (se 1 (by rfl) ⟨14611346, by rfl⟩ : syracuseStep 19481795 = 29222693) B29222693
theorem B4564187 : Blo 1350994 4564187 := bstep (se 1 (by rfl) ⟨3423140, by rfl⟩ : syracuseStep 4564187 = 6846281) B6846281
theorem B3040487 : Blo 1350994 3040487 := bstep (se 1 (by rfl) ⟨2280365, by rfl⟩ : syracuseStep 3040487 = 4560731) B4560731
theorem B6497543 : Blo 1350994 6497543 := bstep (se 1 (by rfl) ⟨4873157, by rfl⟩ : syracuseStep 6497543 = 9746315) B9746315
theorem B316032401 : Blo 1350994 316032401 := bstep (se 2 (by rfl) ⟨118512150, by rfl⟩ : syracuseStep 316032401 = 237024301) B237024301
theorem B3851945 : Blo 1350994 3851945 := bstep (se 2 (by rfl) ⟨1444479, by rfl⟩ : syracuseStep 3851945 = 2888959) B2888959
theorem B2434907 : Blo 1350994 2434907 := bstep (se 1 (by rfl) ⟨1826180, by rfl⟩ : syracuseStep 2434907 = 3652361) B3652361
theorem B11552827 : Blo 1350994 11552827 := bstep (se 1 (by rfl) ⟨8664620, by rfl⟩ : syracuseStep 11552827 = 17329241) B17329241
theorem B3041387 : Blo 1350994 3041387 := bstep (se 1 (by rfl) ⟨2281040, by rfl⟩ : syracuseStep 3041387 = 4562081) B4562081
theorem B2279839 : Blo 1350994 2279839 := bstep (se 1 (by rfl) ⟨1709879, by rfl⟩ : syracuseStep 2279839 = 3419759) B3419759
theorem B31230451 : Blo 1350994 31230451 := bstep (se 1 (by rfl) ⟨23422838, by rfl⟩ : syracuseStep 31230451 = 46845677) B46845677
theorem B8661599 : Blo 1350994 8661599 := bstep (se 1 (by rfl) ⟨6496199, by rfl⟩ : syracuseStep 8661599 = 12992399) B12992399
theorem B3042017 : Blo 1350994 3042017 := bstep (se 2 (by rfl) ⟨1140756, by rfl⟩ : syracuseStep 3042017 = 2281513) B2281513
theorem B6941497 : Blo 1350994 6941497 := bstep (se 2 (by rfl) ⟨2603061, by rfl⟩ : syracuseStep 6941497 = 5206123) B5206123
theorem B2280359 : Blo 1350994 2280359 := bstep (se 1 (by rfl) ⟨1710269, by rfl⟩ : syracuseStep 2280359 = 3420539) B3420539
theorem B19500011 : Blo 1350994 19500011 := bstep (se 1 (by rfl) ⟨14625008, by rfl⟩ : syracuseStep 19500011 = 29250017) B29250017
theorem B12504071 : Blo 1350994 12504071 := bstep (se 1 (by rfl) ⟨9378053, by rfl⟩ : syracuseStep 12504071 = 18756107) B18756107
theorem B5131295 : Blo 1350994 5131295 := bstep (se 1 (by rfl) ⟨3848471, by rfl⟩ : syracuseStep 5131295 = 7696943) B7696943
theorem B13872815 : Blo 1350994 13872815 := bstep (se 1 (by rfl) ⟨10404611, by rfl⟩ : syracuseStep 13872815 = 20809223) B20809223
theorem B3420103 : Blo 1350994 3420103 := bstep (se 1 (by rfl) ⟨2565077, by rfl⟩ : syracuseStep 3420103 = 5130155) B5130155
theorem B2568161 : Blo 1350994 2568161 := bstep (se 2 (by rfl) ⟨963060, by rfl⟩ : syracuseStep 2568161 = 1926121) B1926121
theorem B2887721 : Blo 1350994 2887721 := bstep (se 2 (by rfl) ⟨1082895, by rfl⟩ : syracuseStep 2887721 = 2165791) B2165791
theorem B1519951 : Blo 1350994 1519951 := bstep (se 1 (by rfl) ⟨1139963, by rfl⟩ : syracuseStep 1519951 = 2279927) B2279927
theorem B2027999 : Blo 1350994 2027999 := bstep (se 1 (by rfl) ⟨1520999, by rfl⟩ : syracuseStep 2027999 = 3041999) B3041999
theorem B74044165 : Blo 1350994 74044165 := bstep (se 4 (by rfl) ⟨6941640, by rfl⟩ : syracuseStep 74044165 = 13883281) B13883281
theorem B7803695 : Blo 1350994 7803695 := bstep (se 1 (by rfl) ⟨5852771, by rfl⟩ : syracuseStep 7803695 = 11705543) B11705543
theorem B3421025 : Blo 1350994 3421025 := bstep (se 2 (by rfl) ⟨1282884, by rfl⟩ : syracuseStep 3421025 = 2565769) B2565769
theorem B6493067 : Blo 1350994 6493067 := bstep (se 1 (by rfl) ⟨4869800, by rfl⟩ : syracuseStep 6493067 = 9739601) B9739601
theorem B4559759 : Blo 1350994 4559759 := bstep (se 1 (by rfl) ⟨3419819, by rfl⟩ : syracuseStep 4559759 = 6839639) B6839639
theorem B7697375 : Blo 1350994 7697375 := bstep (se 1 (by rfl) ⟨5773031, by rfl⟩ : syracuseStep 7697375 = 11546063) B11546063
theorem B2028635 : Blo 1350994 2028635 := bstep (se 1 (by rfl) ⟨1521476, by rfl⟩ : syracuseStep 2028635 = 3042953) B3042953
theorem B2028671 : Blo 1350994 2028671 := bstep (se 1 (by rfl) ⟨1521503, by rfl⟩ : syracuseStep 2028671 = 3043007) B3043007
theorem B2028779 : Blo 1350994 2028779 := bstep (se 1 (by rfl) ⟨1521584, by rfl⟩ : syracuseStep 2028779 = 3043169) B3043169
theorem B15013289 : Blo 1350994 15013289 := bstep (se 2 (by rfl) ⟨5629983, by rfl⟩ : syracuseStep 15013289 = 11259967) B11259967
theorem B10966681 : Blo 1350994 10966681 := bstep (se 2 (by rfl) ⟨4112505, by rfl⟩ : syracuseStep 10966681 = 8225011) B8225011
theorem B2029433 : Blo 1350994 2029433 := bstep (se 2 (by rfl) ⟨761037, by rfl⟩ : syracuseStep 2029433 = 1522075) B1522075
theorem B1521535 : Blo 1350994 1521535 := bstep (se 1 (by rfl) ⟨1141151, by rfl⟩ : syracuseStep 1521535 = 2282303) B2282303
theorem B7698401 : Blo 1350994 7698401 := bstep (se 2 (by rfl) ⟨2886900, by rfl⟩ : syracuseStep 7698401 = 5773801) B5773801
theorem B3848381 : Blo 1350994 3848381 := bstep (se 3 (by rfl) ⟨721571, by rfl⟩ : syracuseStep 3848381 = 1443143) B1443143
theorem B3422695 : Blo 1350994 3422695 := bstep (se 1 (by rfl) ⟨2567021, by rfl⟩ : syracuseStep 3422695 = 5134043) B5134043
theorem B61774481 : Blo 1350994 61774481 := bstep (se 2 (by rfl) ⟨23165430, by rfl⟩ : syracuseStep 61774481 = 46330861) B46330861
theorem B10967723 : Blo 1350994 10967723 := bstep (se 1 (by rfl) ⟨8225792, by rfl⟩ : syracuseStep 10967723 = 16451585) B16451585
theorem B4561595 : Blo 1350994 4561595 := bstep (se 1 (by rfl) ⟨3421196, by rfl⟩ : syracuseStep 4561595 = 6842393) B6842393
theorem B5774075 : Blo 1350994 5774075 := bstep (se 1 (by rfl) ⟨4330556, by rfl⟩ : syracuseStep 5774075 = 8661113) B8661113
theorem B4561703 : Blo 1350994 4561703 := bstep (se 1 (by rfl) ⟨3421277, by rfl⟩ : syracuseStep 4561703 = 6842555) B6842555
theorem B3849439 : Blo 1350994 3849439 := bstep (se 1 (by rfl) ⟨2887079, by rfl⟩ : syracuseStep 3849439 = 5774159) B5774159
theorem B3423647 : Blo 1350994 3423647 := bstep (se 1 (by rfl) ⟨2567735, by rfl⟩ : syracuseStep 3423647 = 5135471) B5135471
theorem B120077903 : Blo 1350994 120077903 := bstep (se 1 (by rfl) ⟨90058427, by rfl⟩ : syracuseStep 120077903 = 180116855) B180116855
theorem B3849839 : Blo 1350994 3849839 := bstep (se 1 (by rfl) ⟨2887379, by rfl⟩ : syracuseStep 3849839 = 5774759) B5774759
theorem B25984637 : Blo 1350994 25984637 := bstep (se 3 (by rfl) ⟨4872119, by rfl⟩ : syracuseStep 25984637 = 9744239) B9744239
theorem B1351487 : Blo 1350994 1351487 := bstep (se 1 (by rfl) ⟨1013615, by rfl⟩ : syracuseStep 1351487 = 2027231) B2027231
theorem B1925147 : Blo 1350994 1925147 := bstep (se 1 (by rfl) ⟨1443860, by rfl⟩ : syracuseStep 1925147 = 2887721) B2887721
theorem B10273067 : Blo 1350994 10273067 := bstep (se 1 (by rfl) ⟨7704800, by rfl⟩ : syracuseStep 10273067 = 15409601) B15409601
theorem B1351999 : Blo 1350994 1351999 := bstep (se 1 (by rfl) ⟨1013999, by rfl⟩ : syracuseStep 1351999 = 2027999) B2027999
theorem B5202463 : Blo 1350994 5202463 := bstep (se 1 (by rfl) ⟨3901847, by rfl⟩ : syracuseStep 5202463 = 7803695) B7803695
theorem B3039785 : Blo 1350994 3039785 := bstep (se 2 (by rfl) ⟨1139919, by rfl⟩ : syracuseStep 3039785 = 2279839) B2279839
theorem B3039839 : Blo 1350994 3039839 := bstep (se 1 (by rfl) ⟨2279879, by rfl⟩ : syracuseStep 3039839 = 4559759) B4559759
theorem B4563593 : Blo 1350994 4563593 := bstep (se 2 (by rfl) ⟨1711347, by rfl⟩ : syracuseStep 4563593 = 3422695) B3422695
theorem B41640601 : Blo 1350994 41640601 := bstep (se 2 (by rfl) ⟨15615225, by rfl⟩ : syracuseStep 41640601 = 31230451) B31230451
theorem B17326781 : Blo 1350994 17326781 := bstep (se 3 (by rfl) ⟨3248771, by rfl⟩ : syracuseStep 17326781 = 6497543) B6497543
theorem B1352423 : Blo 1350994 1352423 := bstep (se 1 (by rfl) ⟨1014317, by rfl⟩ : syracuseStep 1352423 = 2028635) B2028635
theorem B1352447 : Blo 1350994 1352447 := bstep (se 1 (by rfl) ⟨1014335, by rfl⟩ : syracuseStep 1352447 = 2028671) B2028671
theorem B1352519 : Blo 1350994 1352519 := bstep (se 1 (by rfl) ⟨1014389, by rfl⟩ : syracuseStep 1352519 = 2028779) B2028779
theorem B842753069 : Blo 1350994 842753069 := bstep (se 3 (by rfl) ⟨158016200, by rfl⟩ : syracuseStep 842753069 = 316032401) B316032401
theorem B40035437 : Blo 1350994 40035437 := bstep (se 3 (by rfl) ⟨7506644, by rfl⟩ : syracuseStep 40035437 = 15013289) B15013289
theorem B1352955 : Blo 1350994 1352955 := bstep (se 1 (by rfl) ⟨1014716, by rfl⟩ : syracuseStep 1352955 = 2029433) B2029433
theorem B2565587 : Blo 1350994 2565587 := bstep (se 1 (by rfl) ⟨1924190, by rfl⟩ : syracuseStep 2565587 = 3848381) B3848381
theorem B41182987 : Blo 1350994 41182987 := bstep (se 1 (by rfl) ⟨30887240, by rfl⟩ : syracuseStep 41182987 = 61774481) B61774481
theorem B3041063 : Blo 1350994 3041063 := bstep (se 1 (by rfl) ⟨2280797, by rfl⟩ : syracuseStep 3041063 = 4561595) B4561595
theorem B3041135 : Blo 1350994 3041135 := bstep (se 1 (by rfl) ⟨2280851, by rfl⟩ : syracuseStep 3041135 = 4561703) B4561703
theorem B2566559 : Blo 1350994 2566559 := bstep (se 1 (by rfl) ⟨1924919, by rfl⟩ : syracuseStep 2566559 = 3849839) B3849839
theorem B15403769 : Blo 1350994 15403769 := bstep (se 2 (by rfl) ⟨5776413, by rfl⟩ : syracuseStep 15403769 = 11552827) B11552827
theorem B2026601 : Blo 1350994 2026601 := bstep (se 2 (by rfl) ⟨759975, by rfl⟩ : syracuseStep 2026601 = 1519951) B1519951
theorem B4566185 : Blo 1350994 4566185 := bstep (se 2 (by rfl) ⟨1712319, by rfl⟩ : syracuseStep 4566185 = 3424639) B3424639
theorem B2280683 : Blo 1350994 2280683 := bstep (se 1 (by rfl) ⟨1710512, by rfl⟩ : syracuseStep 2280683 = 3421025) B3421025
theorem B2026751 : Blo 1350994 2026751 := bstep (se 1 (by rfl) ⟨1520063, by rfl⟩ : syracuseStep 2026751 = 3040127) B3040127
theorem B4328711 : Blo 1350994 4328711 := bstep (se 1 (by rfl) ⟨3246533, by rfl⟩ : syracuseStep 4328711 = 6493067) B6493067
theorem B5131583 : Blo 1350994 5131583 := bstep (se 1 (by rfl) ⟨3848687, by rfl⟩ : syracuseStep 5131583 = 7697375) B7697375
theorem B12987863 : Blo 1350994 12987863 := bstep (se 1 (by rfl) ⟨9740897, by rfl⟩ : syracuseStep 12987863 = 19481795) B19481795
theorem B3042791 : Blo 1350994 3042791 := bstep (se 1 (by rfl) ⟨2282093, by rfl⟩ : syracuseStep 3042791 = 4564187) B4564187
theorem B2026991 : Blo 1350994 2026991 := bstep (se 1 (by rfl) ⟨1520243, by rfl⟩ : syracuseStep 2026991 = 3040487) B3040487
theorem B98725553 : Blo 1350994 98725553 := bstep (se 2 (by rfl) ⟨37022082, by rfl⟩ : syracuseStep 98725553 = 74044165) B74044165
theorem B2567963 : Blo 1350994 2567963 := bstep (se 1 (by rfl) ⟨1925972, by rfl⟩ : syracuseStep 2567963 = 3851945) B3851945
theorem B5132267 : Blo 1350994 5132267 := bstep (se 1 (by rfl) ⟨3849200, by rfl⟩ : syracuseStep 5132267 = 7698401) B7698401
theorem B2027591 : Blo 1350994 2027591 := bstep (se 1 (by rfl) ⟨1520693, by rfl⟩ : syracuseStep 2027591 = 3041387) B3041387
theorem B5132585 : Blo 1350994 5132585 := bstep (se 2 (by rfl) ⟨1924719, by rfl⟩ : syracuseStep 5132585 = 3849439) B3849439
theorem B7311815 : Blo 1350994 7311815 := bstep (se 1 (by rfl) ⟨5483861, by rfl⟩ : syracuseStep 7311815 = 10967723) B10967723
theorem B2028011 : Blo 1350994 2028011 := bstep (se 1 (by rfl) ⟨1521008, by rfl⟩ : syracuseStep 2028011 = 3042017) B3042017
theorem B1520239 : Blo 1350994 1520239 := bstep (se 1 (by rfl) ⟨1140179, by rfl⟩ : syracuseStep 1520239 = 2280359) B2280359
theorem B8336047 : Blo 1350994 8336047 := bstep (se 1 (by rfl) ⟨6252035, by rfl⟩ : syracuseStep 8336047 = 12504071) B12504071
theorem B3420863 : Blo 1350994 3420863 := bstep (se 1 (by rfl) ⟨2565647, by rfl⟩ : syracuseStep 3420863 = 5131295) B5131295
theorem B6493085 : Blo 1350994 6493085 := bstep (se 3 (by rfl) ⟨1217453, by rfl⟩ : syracuseStep 6493085 = 2434907) B2434907
theorem B2282431 : Blo 1350994 2282431 := bstep (se 1 (by rfl) ⟨1711823, by rfl⟩ : syracuseStep 2282431 = 3423647) B3423647
theorem B17323091 : Blo 1350994 17323091 := bstep (se 1 (by rfl) ⟨12992318, by rfl⟩ : syracuseStep 17323091 = 25984637) B25984637
theorem B2028713 : Blo 1350994 2028713 := bstep (se 2 (by rfl) ⟨760767, by rfl⟩ : syracuseStep 2028713 = 1521535) B1521535
theorem B4560137 : Blo 1350994 4560137 := bstep (se 2 (by rfl) ⟨1710051, by rfl⟩ : syracuseStep 4560137 = 3420103) B3420103
theorem B5133739 : Blo 1350994 5133739 := bstep (se 1 (by rfl) ⟨3850304, by rfl⟩ : syracuseStep 5133739 = 7700609) B7700609
theorem B4560623 : Blo 1350994 4560623 := bstep (se 1 (by rfl) ⟨3420467, by rfl⟩ : syracuseStep 4560623 = 6840935) B6840935
theorem B4560839 : Blo 1350994 4560839 := bstep (se 1 (by rfl) ⟨3420629, by rfl⟩ : syracuseStep 4560839 = 6841259) B6841259
theorem B9255329 : Blo 1350994 9255329 := bstep (se 2 (by rfl) ⟨3470748, by rfl⟩ : syracuseStep 9255329 = 6941497) B6941497
theorem B5774399 : Blo 1350994 5774399 := bstep (se 1 (by rfl) ⟨4330799, by rfl⟩ : syracuseStep 5774399 = 8661599) B8661599
theorem B3849383 : Blo 1350994 3849383 := bstep (se 1 (by rfl) ⟨2887037, by rfl⟩ : syracuseStep 3849383 = 5774075) B5774075
theorem B13000007 : Blo 1350994 13000007 := bstep (se 1 (by rfl) ⟨9750005, by rfl⟩ : syracuseStep 13000007 = 19500011) B19500011
theorem B14622241 : Blo 1350994 14622241 := bstep (se 2 (by rfl) ⟨5483340, by rfl⟩ : syracuseStep 14622241 = 10966681) B10966681
theorem B80051935 : Blo 1350994 80051935 := bstep (se 1 (by rfl) ⟨60038951, by rfl⟩ : syracuseStep 80051935 = 120077903) B120077903
theorem B9248543 : Blo 1350994 9248543 := bstep (se 1 (by rfl) ⟨6936407, by rfl⟩ : syracuseStep 9248543 = 13872815) B13872815
theorem B1712107 : Blo 1350994 1712107 := bstep (se 1 (by rfl) ⟨1284080, by rfl⟩ : syracuseStep 1712107 = 2568161) B2568161
theorem B1351727 : Blo 1350994 1351727 := bstep (se 1 (by rfl) ⟨1013795, by rfl⟩ : syracuseStep 1351727 = 2027591) B2027591
theorem B6848711 : Blo 1350994 6848711 := bstep (se 1 (by rfl) ⟨5136533, by rfl⟩ : syracuseStep 6848711 = 10273067) B10273067
theorem B4874543 : Blo 1350994 4874543 := bstep (se 1 (by rfl) ⟨3655907, by rfl⟩ : syracuseStep 4874543 = 7311815) B7311815
theorem B1352007 : Blo 1350994 1352007 := bstep (se 1 (by rfl) ⟨1014005, by rfl⟩ : syracuseStep 1352007 = 2028011) B2028011
theorem B11551187 : Blo 1350994 11551187 := bstep (se 1 (by rfl) ⟨8663390, by rfl⟩ : syracuseStep 11551187 = 17326781) B17326781
theorem B26690291 : Blo 1350994 26690291 := bstep (se 1 (by rfl) ⟨20017718, by rfl⟩ : syracuseStep 26690291 = 40035437) B40035437
theorem B1352475 : Blo 1350994 1352475 := bstep (se 1 (by rfl) ⟨1014356, by rfl⟩ : syracuseStep 1352475 = 2028713) B2028713
theorem B3040091 : Blo 1350994 3040091 := bstep (se 1 (by rfl) ⟨2280068, by rfl⟩ : syracuseStep 3040091 = 4560137) B4560137
theorem B3040415 : Blo 1350994 3040415 := bstep (se 1 (by rfl) ⟨2280311, by rfl⟩ : syracuseStep 3040415 = 4560623) B4560623
theorem B3040559 : Blo 1350994 3040559 := bstep (se 1 (by rfl) ⟨2280419, by rfl⟩ : syracuseStep 3040559 = 4560839) B4560839
theorem B6170219 : Blo 1350994 6170219 := bstep (se 1 (by rfl) ⟨4627664, by rfl⟩ : syracuseStep 6170219 = 9255329) B9255329
theorem B2566255 : Blo 1350994 2566255 := bstep (se 1 (by rfl) ⟨1924691, by rfl⟩ : syracuseStep 2566255 = 3849383) B3849383
theorem B2885807 : Blo 1350994 2885807 := bstep (se 1 (by rfl) ⟨2164355, by rfl⟩ : syracuseStep 2885807 = 4328711) B4328711
theorem B106735913 : Blo 1350994 106735913 := bstep (se 2 (by rfl) ⟨40025967, by rfl⟩ : syracuseStep 106735913 = 80051935) B80051935
theorem B65817035 : Blo 1350994 65817035 := bstep (se 1 (by rfl) ⟨49362776, by rfl⟩ : syracuseStep 65817035 = 98725553) B98725553
theorem B2026523 : Blo 1350994 2026523 := bstep (se 1 (by rfl) ⟨1519892, by rfl⟩ : syracuseStep 2026523 = 3039785) B3039785
theorem B2026559 : Blo 1350994 2026559 := bstep (se 1 (by rfl) ⟨1519919, by rfl⟩ : syracuseStep 2026559 = 3039839) B3039839
theorem B3042395 : Blo 1350994 3042395 := bstep (se 1 (by rfl) ⟨2281796, by rfl⟩ : syracuseStep 3042395 = 4563593) B4563593
theorem B2280575 : Blo 1350994 2280575 := bstep (se 1 (by rfl) ⟨1710431, by rfl⟩ : syracuseStep 2280575 = 3420863) B3420863
theorem B4328723 : Blo 1350994 4328723 := bstep (se 1 (by rfl) ⟨3246542, by rfl⟩ : syracuseStep 4328723 = 6493085) B6493085
theorem B561835379 : Blo 1350994 561835379 := bstep (se 1 (by rfl) ⟨421376534, by rfl⟩ : syracuseStep 561835379 = 842753069) B842753069
theorem B2026985 : Blo 1350994 2026985 := bstep (se 2 (by rfl) ⟨760119, by rfl⟩ : syracuseStep 2026985 = 1520239) B1520239
theorem B55520801 : Blo 1350994 55520801 := bstep (se 2 (by rfl) ⟨20820300, by rfl⟩ : syracuseStep 55520801 = 41640601) B41640601
theorem B2027375 : Blo 1350994 2027375 := bstep (se 1 (by rfl) ⟨1520531, by rfl⟩ : syracuseStep 2027375 = 3041063) B3041063
theorem B2027423 : Blo 1350994 2027423 := bstep (se 1 (by rfl) ⟨1520567, by rfl⟩ : syracuseStep 2027423 = 3041135) B3041135
theorem B3043241 : Blo 1350994 3043241 := bstep (se 2 (by rfl) ⟨1141215, by rfl⟩ : syracuseStep 3043241 = 2282431) B2282431
theorem B10269179 : Blo 1350994 10269179 := bstep (se 1 (by rfl) ⟨7701884, by rfl⟩ : syracuseStep 10269179 = 15403769) B15403769
theorem B6844985 : Blo 1350994 6844985 := bstep (se 2 (by rfl) ⟨2566869, by rfl⟩ : syracuseStep 6844985 = 5133739) B5133739
theorem B3044123 : Blo 1350994 3044123 := bstep (se 1 (by rfl) ⟨2283092, by rfl⟩ : syracuseStep 3044123 = 4566185) B4566185
theorem B1520455 : Blo 1350994 1520455 := bstep (se 1 (by rfl) ⟨1140341, by rfl⟩ : syracuseStep 1520455 = 2280683) B2280683
theorem B3421055 : Blo 1350994 3421055 := bstep (se 1 (by rfl) ⟨2565791, by rfl⟩ : syracuseStep 3421055 = 5131583) B5131583
theorem B2028527 : Blo 1350994 2028527 := bstep (se 1 (by rfl) ⟨1521395, by rfl⟩ : syracuseStep 2028527 = 3042791) B3042791
theorem B6165695 : Blo 1350994 6165695 := bstep (se 1 (by rfl) ⟨4624271, by rfl⟩ : syracuseStep 6165695 = 9248543) B9248543
theorem B2282809 : Blo 1350994 2282809 := bstep (se 2 (by rfl) ⟨856053, by rfl⟩ : syracuseStep 2282809 = 1712107) B1712107
theorem B3421511 : Blo 1350994 3421511 := bstep (se 1 (by rfl) ⟨2566133, by rfl⟩ : syracuseStep 3421511 = 5132267) B5132267
theorem B5133725 : Blo 1350994 5133725 := bstep (se 3 (by rfl) ⟨962573, by rfl⟩ : syracuseStep 5133725 = 1925147) B1925147
theorem B3421723 : Blo 1350994 3421723 := bstep (se 1 (by rfl) ⟨2566292, by rfl⟩ : syracuseStep 3421723 = 5132585) B5132585
theorem B6936617 : Blo 1350994 6936617 := bstep (se 2 (by rfl) ⟨2601231, by rfl⟩ : syracuseStep 6936617 = 5202463) B5202463
theorem B11548727 : Blo 1350994 11548727 := bstep (se 1 (by rfl) ⟨8661545, by rfl⟩ : syracuseStep 11548727 = 17323091) B17323091
theorem B11114729 : Blo 1350994 11114729 := bstep (se 2 (by rfl) ⟨4168023, by rfl⟩ : syracuseStep 11114729 = 8336047) B8336047
theorem B1710391 : Blo 1350994 1710391 := bstep (se 1 (by rfl) ⟨1282793, by rfl⟩ : syracuseStep 1710391 = 2565587) B2565587
theorem B1711039 : Blo 1350994 1711039 := bstep (se 1 (by rfl) ⟨1283279, by rfl⟩ : syracuseStep 1711039 = 2566559) B2566559
theorem B3849599 : Blo 1350994 3849599 := bstep (se 1 (by rfl) ⟨2887199, by rfl⟩ : syracuseStep 3849599 = 5774399) B5774399
theorem B19496321 : Blo 1350994 19496321 := bstep (se 2 (by rfl) ⟨7311120, by rfl⟩ : syracuseStep 19496321 = 14622241) B14622241
theorem B1351067 : Blo 1350994 1351067 := bstep (se 1 (by rfl) ⟨1013300, by rfl⟩ : syracuseStep 1351067 = 2026601) B2026601
theorem B6847901 : Blo 1350994 6847901 := bstep (se 3 (by rfl) ⟨1283981, by rfl⟩ : syracuseStep 6847901 = 2567963) B2567963
theorem B1351167 : Blo 1350994 1351167 := bstep (se 1 (by rfl) ⟨1013375, by rfl⟩ : syracuseStep 1351167 = 2026751) B2026751
theorem B8666671 : Blo 1350994 8666671 := bstep (se 1 (by rfl) ⟨6500003, by rfl⟩ : syracuseStep 8666671 = 13000007) B13000007
theorem B8658575 : Blo 1350994 8658575 := bstep (se 1 (by rfl) ⟨6493931, by rfl⟩ : syracuseStep 8658575 = 12987863) B12987863
theorem B1351327 : Blo 1350994 1351327 := bstep (se 1 (by rfl) ⟨1013495, by rfl⟩ : syracuseStep 1351327 = 2026991) B2026991
theorem B54910649 : Blo 1350994 54910649 := bstep (se 2 (by rfl) ⟨20591493, by rfl⟩ : syracuseStep 54910649 = 41182987) B41182987
theorem B18497645 : Blo 1350994 18497645 := bstep (se 3 (by rfl) ⟨3468308, by rfl⟩ : syracuseStep 18497645 = 6936617) B6936617
theorem B7700791 : Blo 1350994 7700791 := bstep (se 1 (by rfl) ⟨5775593, by rfl⟩ : syracuseStep 7700791 = 11551187) B11551187
theorem B4563323 : Blo 1350994 4563323 := bstep (se 1 (by rfl) ⟨3422492, by rfl⟩ : syracuseStep 4563323 = 6844985) B6844985
theorem B17793527 : Blo 1350994 17793527 := bstep (se 1 (by rfl) ⟨13345145, by rfl⟩ : syracuseStep 17793527 = 26690291) B26690291
theorem B1352351 : Blo 1350994 1352351 := bstep (se 1 (by rfl) ⟨1014263, by rfl⟩ : syracuseStep 1352351 = 2028527) B2028527
theorem B1498227677 : Blo 1350994 1498227677 := bstep (se 3 (by rfl) ⟨280917689, by rfl⟩ : syracuseStep 1498227677 = 561835379) B561835379
theorem B4113479 : Blo 1350994 4113479 := bstep (se 1 (by rfl) ⟨3085109, by rfl⟩ : syracuseStep 4113479 = 6170219) B6170219
theorem B71157275 : Blo 1350994 71157275 := bstep (se 1 (by rfl) ⟨53367956, by rfl⟩ : syracuseStep 71157275 = 106735913) B106735913
theorem B43878023 : Blo 1350994 43878023 := bstep (se 1 (by rfl) ⟨32908517, by rfl⟩ : syracuseStep 43878023 = 65817035) B65817035
theorem B2885815 : Blo 1350994 2885815 := bstep (se 1 (by rfl) ⟨2164361, by rfl⟩ : syracuseStep 2885815 = 4328723) B4328723
theorem B2566399 : Blo 1350994 2566399 := bstep (se 1 (by rfl) ⟨1924799, by rfl⟩ : syracuseStep 2566399 = 3849599) B3849599
theorem B4565267 : Blo 1350994 4565267 := bstep (se 1 (by rfl) ⟨3423950, by rfl⟩ : syracuseStep 4565267 = 6847901) B6847901
theorem B37013867 : Blo 1350994 37013867 := bstep (se 1 (by rfl) ⟨27760400, by rfl⟩ : syracuseStep 37013867 = 55520801) B55520801
theorem B4565807 : Blo 1350994 4565807 := bstep (se 1 (by rfl) ⟨3424355, by rfl⟩ : syracuseStep 4565807 = 6848711) B6848711
theorem B2280521 : Blo 1350994 2280521 := bstep (se 2 (by rfl) ⟨855195, by rfl⟩ : syracuseStep 2280521 = 1710391) B1710391
theorem B7695485 : Blo 1350994 7695485 := bstep (se 3 (by rfl) ⟨1442903, by rfl⟩ : syracuseStep 7695485 = 2885807) B2885807
theorem B2026727 : Blo 1350994 2026727 := bstep (se 1 (by rfl) ⟨1520045, by rfl⟩ : syracuseStep 2026727 = 3040091) B3040091
theorem B2280703 : Blo 1350994 2280703 := bstep (se 1 (by rfl) ⟨1710527, by rfl⟩ : syracuseStep 2280703 = 3421055) B3421055
theorem B2026943 : Blo 1350994 2026943 := bstep (se 1 (by rfl) ⟨1520207, by rfl⟩ : syracuseStep 2026943 = 3040415) B3040415
theorem B2027039 : Blo 1350994 2027039 := bstep (se 1 (by rfl) ⟨1520279, by rfl⟩ : syracuseStep 2027039 = 3040559) B3040559
theorem B2281007 : Blo 1350994 2281007 := bstep (se 1 (by rfl) ⟨1710755, by rfl⟩ : syracuseStep 2281007 = 3421511) B3421511
theorem B2027273 : Blo 1350994 2027273 := bstep (se 2 (by rfl) ⟨760227, by rfl⟩ : syracuseStep 2027273 = 1520455) B1520455
theorem B2281385 : Blo 1350994 2281385 := bstep (se 2 (by rfl) ⟨855519, by rfl⟩ : syracuseStep 2281385 = 1711039) B1711039
theorem B7409819 : Blo 1350994 7409819 := bstep (se 1 (by rfl) ⟨5557364, by rfl⟩ : syracuseStep 7409819 = 11114729) B11114729
theorem B3043745 : Blo 1350994 3043745 := bstep (se 2 (by rfl) ⟨1141404, by rfl⟩ : syracuseStep 3043745 = 2282809) B2282809
theorem B2028263 : Blo 1350994 2028263 := bstep (se 1 (by rfl) ⟨1521197, by rfl⟩ : syracuseStep 2028263 = 3042395) B3042395
theorem B11555561 : Blo 1350994 11555561 := bstep (se 2 (by rfl) ⟨4333335, by rfl⟩ : syracuseStep 11555561 = 8666671) B8666671
theorem B1520383 : Blo 1350994 1520383 := bstep (se 1 (by rfl) ⟨1140287, by rfl⟩ : syracuseStep 1520383 = 2280575) B2280575
theorem B12997547 : Blo 1350994 12997547 := bstep (se 1 (by rfl) ⟨9748160, by rfl⟩ : syracuseStep 12997547 = 19496321) B19496321
theorem B5772383 : Blo 1350994 5772383 := bstep (se 1 (by rfl) ⟨4329287, by rfl⟩ : syracuseStep 5772383 = 8658575) B8658575
theorem B36607099 : Blo 1350994 36607099 := bstep (se 1 (by rfl) ⟨27455324, by rfl⟩ : syracuseStep 36607099 = 54910649) B54910649
theorem B2028827 : Blo 1350994 2028827 := bstep (se 1 (by rfl) ⟨1521620, by rfl⟩ : syracuseStep 2028827 = 3043241) B3043241
theorem B3421673 : Blo 1350994 3421673 := bstep (se 2 (by rfl) ⟨1283127, by rfl⟩ : syracuseStep 3421673 = 2566255) B2566255
theorem B3249695 : Blo 1350994 3249695 := bstep (se 1 (by rfl) ⟨2437271, by rfl⟩ : syracuseStep 3249695 = 4874543) B4874543
theorem B6846119 : Blo 1350994 6846119 := bstep (se 1 (by rfl) ⟨5134589, by rfl⟩ : syracuseStep 6846119 = 10269179) B10269179
theorem B2029415 : Blo 1350994 2029415 := bstep (se 1 (by rfl) ⟨1522061, by rfl⟩ : syracuseStep 2029415 = 3044123) B3044123
theorem B4110463 : Blo 1350994 4110463 := bstep (se 1 (by rfl) ⟨3082847, by rfl⟩ : syracuseStep 4110463 = 6165695) B6165695
theorem B3422483 : Blo 1350994 3422483 := bstep (se 1 (by rfl) ⟨2566862, by rfl⟩ : syracuseStep 3422483 = 5133725) B5133725
theorem B7699151 : Blo 1350994 7699151 := bstep (se 1 (by rfl) ⟨5774363, by rfl⟩ : syracuseStep 7699151 = 11548727) B11548727
theorem B1351015 : Blo 1350994 1351015 := bstep (se 1 (by rfl) ⟨1013261, by rfl⟩ : syracuseStep 1351015 = 2026523) B2026523
theorem B4562297 : Blo 1350994 4562297 := bstep (se 2 (by rfl) ⟨1710861, by rfl⟩ : syracuseStep 4562297 = 3421723) B3421723
theorem B1351039 : Blo 1350994 1351039 := bstep (se 1 (by rfl) ⟨1013279, by rfl⟩ : syracuseStep 1351039 = 2026559) B2026559
theorem B1351323 : Blo 1350994 1351323 := bstep (se 1 (by rfl) ⟨1013492, by rfl⟩ : syracuseStep 1351323 = 2026985) B2026985
theorem B1351583 : Blo 1350994 1351583 := bstep (se 1 (by rfl) ⟨1013687, by rfl⟩ : syracuseStep 1351583 = 2027375) B2027375
theorem B1351615 : Blo 1350994 1351615 := bstep (se 1 (by rfl) ⟨1013711, by rfl⟩ : syracuseStep 1351615 = 2027423) B2027423
theorem B4939879 : Blo 1350994 4939879 := bstep (se 1 (by rfl) ⟨3704909, by rfl⟩ : syracuseStep 4939879 = 7409819) B7409819
theorem B5480617 : Blo 1350994 5480617 := bstep (se 2 (by rfl) ⟨2055231, by rfl⟩ : syracuseStep 5480617 = 4110463) B4110463
theorem B1352175 : Blo 1350994 1352175 := bstep (se 1 (by rfl) ⟨1014131, by rfl⟩ : syracuseStep 1352175 = 2028263) B2028263
theorem B998818451 : Blo 1350994 998818451 := bstep (se 1 (by rfl) ⟨749113838, by rfl⟩ : syracuseStep 998818451 = 1498227677) B1498227677
theorem B1352551 : Blo 1350994 1352551 := bstep (se 1 (by rfl) ⟨1014413, by rfl⟩ : syracuseStep 1352551 = 2028827) B2028827
theorem B4564079 : Blo 1350994 4564079 := bstep (se 1 (by rfl) ⟨3423059, by rfl⟩ : syracuseStep 4564079 = 6846119) B6846119
theorem B1352943 : Blo 1350994 1352943 := bstep (se 1 (by rfl) ⟨1014707, by rfl⟩ : syracuseStep 1352943 = 2029415) B2029415
theorem B47449405 : Blo 1350994 47449405 := bstep (se 3 (by rfl) ⟨8896763, by rfl⟩ : syracuseStep 47449405 = 17793527) B17793527
theorem B48809465 : Blo 1350994 48809465 := bstep (se 2 (by rfl) ⟨18303549, by rfl⟩ : syracuseStep 48809465 = 36607099) B36607099
theorem B24675911 : Blo 1350994 24675911 := bstep (se 1 (by rfl) ⟨18506933, by rfl⟩ : syracuseStep 24675911 = 37013867) B37013867
theorem B3040937 : Blo 1350994 3040937 := bstep (se 2 (by rfl) ⟨1140351, by rfl⟩ : syracuseStep 3040937 = 2280703) B2280703
theorem B5130323 : Blo 1350994 5130323 := bstep (se 1 (by rfl) ⟨3847742, by rfl⟩ : syracuseStep 5130323 = 7695485) B7695485
theorem B3041531 : Blo 1350994 3041531 := bstep (se 1 (by rfl) ⟨2281148, by rfl⟩ : syracuseStep 3041531 = 4562297) B4562297
theorem B12331763 : Blo 1350994 12331763 := bstep (se 1 (by rfl) ⟨9248822, by rfl⟩ : syracuseStep 12331763 = 18497645) B18497645
theorem B3042215 : Blo 1350994 3042215 := bstep (se 1 (by rfl) ⟨2281661, by rfl⟩ : syracuseStep 3042215 = 4563323) B4563323
theorem B10267721 : Blo 1350994 10267721 := bstep (se 2 (by rfl) ⟨3850395, by rfl⟩ : syracuseStep 10267721 = 7700791) B7700791
theorem B7703707 : Blo 1350994 7703707 := bstep (se 1 (by rfl) ⟨5777780, by rfl⟩ : syracuseStep 7703707 = 11555561) B11555561
theorem B2281115 : Blo 1350994 2281115 := bstep (se 1 (by rfl) ⟨1710836, by rfl⟩ : syracuseStep 2281115 = 3421673) B3421673
theorem B2027177 : Blo 1350994 2027177 := bstep (se 2 (by rfl) ⟨760191, by rfl⟩ : syracuseStep 2027177 = 1520383) B1520383
theorem B2166463 : Blo 1350994 2166463 := bstep (se 1 (by rfl) ⟨1624847, by rfl⟩ : syracuseStep 2166463 = 3249695) B3249695
theorem B2281655 : Blo 1350994 2281655 := bstep (se 1 (by rfl) ⟨1711241, by rfl⟩ : syracuseStep 2281655 = 3422483) B3422483
theorem B3043511 : Blo 1350994 3043511 := bstep (se 1 (by rfl) ⟨2282633, by rfl⟩ : syracuseStep 3043511 = 4565267) B4565267
theorem B5132767 : Blo 1350994 5132767 := bstep (se 1 (by rfl) ⟨3849575, by rfl⟩ : syracuseStep 5132767 = 7699151) B7699151
theorem B3043871 : Blo 1350994 3043871 := bstep (se 1 (by rfl) ⟨2282903, by rfl⟩ : syracuseStep 3043871 = 4565807) B4565807
theorem B1520347 : Blo 1350994 1520347 := bstep (se 1 (by rfl) ⟨1140260, by rfl⟩ : syracuseStep 1520347 = 2280521) B2280521
theorem B1520671 : Blo 1350994 1520671 := bstep (se 1 (by rfl) ⟨1140503, by rfl⟩ : syracuseStep 1520671 = 2281007) B2281007
theorem B1520923 : Blo 1350994 1520923 := bstep (se 1 (by rfl) ⟨1140692, by rfl⟩ : syracuseStep 1520923 = 2281385) B2281385
theorem B3847753 : Blo 1350994 3847753 := bstep (se 2 (by rfl) ⟨1442907, by rfl⟩ : syracuseStep 3847753 = 2885815) B2885815
theorem B2029163 : Blo 1350994 2029163 := bstep (se 1 (by rfl) ⟨1521872, by rfl⟩ : syracuseStep 2029163 = 3043745) B3043745
theorem B3421865 : Blo 1350994 3421865 := bstep (se 2 (by rfl) ⟨1283199, by rfl⟩ : syracuseStep 3421865 = 2566399) B2566399
theorem B8665031 : Blo 1350994 8665031 := bstep (se 1 (by rfl) ⟨6498773, by rfl⟩ : syracuseStep 8665031 = 12997547) B12997547
theorem B2742319 : Blo 1350994 2742319 := bstep (se 1 (by rfl) ⟨2056739, by rfl⟩ : syracuseStep 2742319 = 4113479) B4113479
theorem B3848255 : Blo 1350994 3848255 := bstep (se 1 (by rfl) ⟨2886191, by rfl⟩ : syracuseStep 3848255 = 5772383) B5772383
theorem B47438183 : Blo 1350994 47438183 := bstep (se 1 (by rfl) ⟨35578637, by rfl⟩ : syracuseStep 47438183 = 71157275) B71157275
theorem B29252015 : Blo 1350994 29252015 := bstep (se 1 (by rfl) ⟨21939011, by rfl⟩ : syracuseStep 29252015 = 43878023) B43878023
theorem B1351151 : Blo 1350994 1351151 := bstep (se 1 (by rfl) ⟨1013363, by rfl⟩ : syracuseStep 1351151 = 2026727) B2026727
theorem B1351295 : Blo 1350994 1351295 := bstep (se 1 (by rfl) ⟨1013471, by rfl⟩ : syracuseStep 1351295 = 2026943) B2026943
theorem B1351359 : Blo 1350994 1351359 := bstep (se 1 (by rfl) ⟨1013519, by rfl⟩ : syracuseStep 1351359 = 2027039) B2027039
theorem B1351515 : Blo 1350994 1351515 := bstep (se 1 (by rfl) ⟨1013636, by rfl⟩ : syracuseStep 1351515 = 2027273) B2027273
theorem B6586505 : Blo 1350994 6586505 := bstep (se 2 (by rfl) ⟨2469939, by rfl⟩ : syracuseStep 6586505 = 4939879) B4939879
theorem B7307489 : Blo 1350994 7307489 := bstep (se 2 (by rfl) ⟨2740308, by rfl⟩ : syracuseStep 7307489 = 5480617) B5480617
theorem B665878967 : Blo 1350994 665878967 := bstep (se 1 (by rfl) ⟨499409225, by rfl⟩ : syracuseStep 665878967 = 998818451) B998818451
theorem B126501821 : Blo 1350994 126501821 := bstep (se 3 (by rfl) ⟨23719091, by rfl⟩ : syracuseStep 126501821 = 47438183) B47438183
theorem B32539643 : Blo 1350994 32539643 := bstep (se 1 (by rfl) ⟨24404732, by rfl⟩ : syracuseStep 32539643 = 48809465) B48809465
theorem B16450607 : Blo 1350994 16450607 := bstep (se 1 (by rfl) ⟨12337955, by rfl⟩ : syracuseStep 16450607 = 24675911) B24675911
theorem B1352775 : Blo 1350994 1352775 := bstep (se 1 (by rfl) ⟨1014581, by rfl⟩ : syracuseStep 1352775 = 2029163) B2029163
theorem B5776687 : Blo 1350994 5776687 := bstep (se 1 (by rfl) ⟨4332515, by rfl⟩ : syracuseStep 5776687 = 8665031) B8665031
theorem B2565503 : Blo 1350994 2565503 := bstep (se 1 (by rfl) ⟨1924127, by rfl⟩ : syracuseStep 2565503 = 3848255) B3848255
theorem B5130337 : Blo 1350994 5130337 := bstep (se 2 (by rfl) ⟨1923876, by rfl⟩ : syracuseStep 5130337 = 3847753) B3847753
theorem B3656425 : Blo 1350994 3656425 := bstep (se 2 (by rfl) ⟨1371159, by rfl⟩ : syracuseStep 3656425 = 2742319) B2742319
theorem B6843689 : Blo 1350994 6843689 := bstep (se 2 (by rfl) ⟨2566383, by rfl⟩ : syracuseStep 6843689 = 5132767) B5132767
theorem B3042719 : Blo 1350994 3042719 := bstep (se 1 (by rfl) ⟨2282039, by rfl⟩ : syracuseStep 3042719 = 4564079) B4564079
theorem B2027129 : Blo 1350994 2027129 := bstep (se 2 (by rfl) ⟨760173, by rfl⟩ : syracuseStep 2027129 = 1520347) B1520347
theorem B2027291 : Blo 1350994 2027291 := bstep (se 1 (by rfl) ⟨1520468, by rfl⟩ : syracuseStep 2027291 = 3040937) B3040937
theorem B2281243 : Blo 1350994 2281243 := bstep (se 1 (by rfl) ⟨1710932, by rfl⟩ : syracuseStep 2281243 = 3421865) B3421865
theorem B2027561 : Blo 1350994 2027561 := bstep (se 2 (by rfl) ⟨760335, by rfl⟩ : syracuseStep 2027561 = 1520671) B1520671
theorem B3420215 : Blo 1350994 3420215 := bstep (se 1 (by rfl) ⟨2565161, by rfl⟩ : syracuseStep 3420215 = 5130323) B5130323
theorem B2027687 : Blo 1350994 2027687 := bstep (se 1 (by rfl) ⟨1520765, by rfl⟩ : syracuseStep 2027687 = 3041531) B3041531
theorem B19501343 : Blo 1350994 19501343 := bstep (se 1 (by rfl) ⟨14626007, by rfl⟩ : syracuseStep 19501343 = 29252015) B29252015
theorem B2027897 : Blo 1350994 2027897 := bstep (se 2 (by rfl) ⟨760461, by rfl⟩ : syracuseStep 2027897 = 1520923) B1520923
theorem B8221175 : Blo 1350994 8221175 := bstep (se 1 (by rfl) ⟨6165881, by rfl⟩ : syracuseStep 8221175 = 12331763) B12331763
theorem B2028143 : Blo 1350994 2028143 := bstep (se 1 (by rfl) ⟨1521107, by rfl⟩ : syracuseStep 2028143 = 3042215) B3042215
theorem B6845147 : Blo 1350994 6845147 := bstep (se 1 (by rfl) ⟨5133860, by rfl⟩ : syracuseStep 6845147 = 10267721) B10267721
theorem B2888617 : Blo 1350994 2888617 := bstep (se 2 (by rfl) ⟨1083231, by rfl⟩ : syracuseStep 2888617 = 2166463) B2166463
theorem B1520743 : Blo 1350994 1520743 := bstep (se 1 (by rfl) ⟨1140557, by rfl⟩ : syracuseStep 1520743 = 2281115) B2281115
theorem B1521103 : Blo 1350994 1521103 := bstep (se 1 (by rfl) ⟨1140827, by rfl⟩ : syracuseStep 1521103 = 2281655) B2281655
theorem B2029007 : Blo 1350994 2029007 := bstep (se 1 (by rfl) ⟨1521755, by rfl⟩ : syracuseStep 2029007 = 3043511) B3043511
theorem B2029247 : Blo 1350994 2029247 := bstep (se 1 (by rfl) ⟨1521935, by rfl⟩ : syracuseStep 2029247 = 3043871) B3043871
theorem B10271609 : Blo 1350994 10271609 := bstep (se 2 (by rfl) ⟨3851853, by rfl⟩ : syracuseStep 10271609 = 7703707) B7703707
theorem B63265873 : Blo 1350994 63265873 := bstep (se 2 (by rfl) ⟨23724702, by rfl⟩ : syracuseStep 63265873 = 47449405) B47449405
theorem B1351451 : Blo 1350994 1351451 := bstep (se 1 (by rfl) ⟨1013588, by rfl⟩ : syracuseStep 1351451 = 2027177) B2027177
theorem B1351707 : Blo 1350994 1351707 := bstep (se 1 (by rfl) ⟨1013780, by rfl⟩ : syracuseStep 1351707 = 2027561) B2027561
theorem B4391003 : Blo 1350994 4391003 := bstep (se 1 (by rfl) ⟨3293252, by rfl⟩ : syracuseStep 4391003 = 6586505) B6586505
theorem B1351791 : Blo 1350994 1351791 := bstep (se 1 (by rfl) ⟨1013843, by rfl⟩ : syracuseStep 1351791 = 2027687) B2027687
theorem B6840449 : Blo 1350994 6840449 := bstep (se 2 (by rfl) ⟨2565168, by rfl⟩ : syracuseStep 6840449 = 5130337) B5130337
theorem B13000895 : Blo 1350994 13000895 := bstep (se 1 (by rfl) ⟨9750671, by rfl⟩ : syracuseStep 13000895 = 19501343) B19501343
theorem B1351931 : Blo 1350994 1351931 := bstep (se 1 (by rfl) ⟨1013948, by rfl⟩ : syracuseStep 1351931 = 2027897) B2027897
theorem B5480783 : Blo 1350994 5480783 := bstep (se 1 (by rfl) ⟨4110587, by rfl⟩ : syracuseStep 5480783 = 8221175) B8221175
theorem B1352095 : Blo 1350994 1352095 := bstep (se 1 (by rfl) ⟨1014071, by rfl⟩ : syracuseStep 1352095 = 2028143) B2028143
theorem B4563431 : Blo 1350994 4563431 := bstep (se 1 (by rfl) ⟨3422573, by rfl⟩ : syracuseStep 4563431 = 6845147) B6845147
theorem B21693095 : Blo 1350994 21693095 := bstep (se 1 (by rfl) ⟨16269821, by rfl⟩ : syracuseStep 21693095 = 32539643) B32539643
theorem B1352671 : Blo 1350994 1352671 := bstep (se 1 (by rfl) ⟨1014503, by rfl⟩ : syracuseStep 1352671 = 2029007) B2029007
theorem B4875233 : Blo 1350994 4875233 := bstep (se 2 (by rfl) ⟨1828212, by rfl⟩ : syracuseStep 4875233 = 3656425) B3656425
theorem B1352831 : Blo 1350994 1352831 := bstep (se 1 (by rfl) ⟨1014623, by rfl⟩ : syracuseStep 1352831 = 2029247) B2029247
theorem B3851489 : Blo 1350994 3851489 := bstep (se 2 (by rfl) ⟨1444308, by rfl⟩ : syracuseStep 3851489 = 2888617) B2888617
theorem B84354497 : Blo 1350994 84354497 := bstep (se 2 (by rfl) ⟨31632936, by rfl⟩ : syracuseStep 84354497 = 63265873) B63265873
theorem B7702249 : Blo 1350994 7702249 := bstep (se 2 (by rfl) ⟨2888343, by rfl⟩ : syracuseStep 7702249 = 5776687) B5776687
theorem B3041657 : Blo 1350994 3041657 := bstep (se 2 (by rfl) ⟨1140621, by rfl⟩ : syracuseStep 3041657 = 2281243) B2281243
theorem B2280143 : Blo 1350994 2280143 := bstep (se 1 (by rfl) ⟨1710107, by rfl⟩ : syracuseStep 2280143 = 3420215) B3420215
theorem B443919311 : Blo 1350994 443919311 := bstep (se 1 (by rfl) ⟨332939483, by rfl⟩ : syracuseStep 443919311 = 665878967) B665878967
theorem B2027657 : Blo 1350994 2027657 := bstep (se 2 (by rfl) ⟨760371, by rfl⟩ : syracuseStep 2027657 = 1520743) B1520743
theorem B2028137 : Blo 1350994 2028137 := bstep (se 2 (by rfl) ⟨760551, by rfl⟩ : syracuseStep 2028137 = 1521103) B1521103
theorem B2028479 : Blo 1350994 2028479 := bstep (se 1 (by rfl) ⟨1521359, by rfl⟩ : syracuseStep 2028479 = 3042719) B3042719
theorem B4871659 : Blo 1350994 4871659 := bstep (se 1 (by rfl) ⟨3653744, by rfl⟩ : syracuseStep 4871659 = 7307489) B7307489
theorem B84334547 : Blo 1350994 84334547 := bstep (se 1 (by rfl) ⟨63250910, by rfl⟩ : syracuseStep 84334547 = 126501821) B126501821
theorem B10967071 : Blo 1350994 10967071 := bstep (se 1 (by rfl) ⟨8225303, by rfl⟩ : syracuseStep 10967071 = 16450607) B16450607
theorem B1710335 : Blo 1350994 1710335 := bstep (se 1 (by rfl) ⟨1282751, by rfl⟩ : syracuseStep 1710335 = 2565503) B2565503
theorem B6847739 : Blo 1350994 6847739 := bstep (se 1 (by rfl) ⟨5135804, by rfl⟩ : syracuseStep 6847739 = 10271609) B10271609
theorem B4562459 : Blo 1350994 4562459 := bstep (se 1 (by rfl) ⟨3421844, by rfl⟩ : syracuseStep 4562459 = 6843689) B6843689
theorem B1351419 : Blo 1350994 1351419 := bstep (se 1 (by rfl) ⟨1013564, by rfl⟩ : syracuseStep 1351419 = 2027129) B2027129
theorem B1351527 : Blo 1350994 1351527 := bstep (se 1 (by rfl) ⟨1013645, by rfl⟩ : syracuseStep 1351527 = 2027291) B2027291
theorem B14622761 : Blo 1350994 14622761 := bstep (se 2 (by rfl) ⟨5483535, by rfl⟩ : syracuseStep 14622761 = 10967071) B10967071
theorem B1351771 : Blo 1350994 1351771 := bstep (se 1 (by rfl) ⟨1013828, by rfl⟩ : syracuseStep 1351771 = 2027657) B2027657
theorem B8667263 : Blo 1350994 8667263 := bstep (se 1 (by rfl) ⟨6500447, by rfl⟩ : syracuseStep 8667263 = 13000895) B13000895
theorem B3653855 : Blo 1350994 3653855 := bstep (se 1 (by rfl) ⟨2740391, by rfl⟩ : syracuseStep 3653855 = 5480783) B5480783
theorem B1352091 : Blo 1350994 1352091 := bstep (se 1 (by rfl) ⟨1014068, by rfl⟩ : syracuseStep 1352091 = 2028137) B2028137
theorem B1352319 : Blo 1350994 1352319 := bstep (se 1 (by rfl) ⟨1014239, by rfl⟩ : syracuseStep 1352319 = 2028479) B2028479
theorem B56223031 : Blo 1350994 56223031 := bstep (se 1 (by rfl) ⟨42167273, by rfl⟩ : syracuseStep 56223031 = 84334547) B84334547
theorem B295946207 : Blo 1350994 295946207 := bstep (se 1 (by rfl) ⟨221959655, by rfl⟩ : syracuseStep 295946207 = 443919311) B443919311
theorem B4565159 : Blo 1350994 4565159 := bstep (se 1 (by rfl) ⟨3423869, by rfl⟩ : syracuseStep 4565159 = 6847739) B6847739
theorem B3041639 : Blo 1350994 3041639 := bstep (se 1 (by rfl) ⟨2281229, by rfl⟩ : syracuseStep 3041639 = 4562459) B4562459
theorem B2927335 : Blo 1350994 2927335 := bstep (se 1 (by rfl) ⟨2195501, by rfl⟩ : syracuseStep 2927335 = 4391003) B4391003
theorem B3042287 : Blo 1350994 3042287 := bstep (se 1 (by rfl) ⟨2281715, by rfl⟩ : syracuseStep 3042287 = 4563431) B4563431
theorem B14462063 : Blo 1350994 14462063 := bstep (se 1 (by rfl) ⟨10846547, by rfl⟩ : syracuseStep 14462063 = 21693095) B21693095
theorem B2027771 : Blo 1350994 2027771 := bstep (se 1 (by rfl) ⟨1520828, by rfl⟩ : syracuseStep 2027771 = 3041657) B3041657
theorem B1520095 : Blo 1350994 1520095 := bstep (se 1 (by rfl) ⟨1140071, by rfl⟩ : syracuseStep 1520095 = 2280143) B2280143
theorem B10269665 : Blo 1350994 10269665 := bstep (se 2 (by rfl) ⟨3851124, by rfl⟩ : syracuseStep 10269665 = 7702249) B7702249
theorem B4560299 : Blo 1350994 4560299 := bstep (se 1 (by rfl) ⟨3420224, by rfl⟩ : syracuseStep 4560299 = 6840449) B6840449
theorem B10270637 : Blo 1350994 10270637 := bstep (se 3 (by rfl) ⟨1925744, by rfl⟩ : syracuseStep 10270637 = 3851489) B3851489
theorem B4560893 : Blo 1350994 4560893 := bstep (se 3 (by rfl) ⟨855167, by rfl⟩ : syracuseStep 4560893 = 1710335) B1710335
theorem B56236331 : Blo 1350994 56236331 := bstep (se 1 (by rfl) ⟨42177248, by rfl⟩ : syracuseStep 56236331 = 84354497) B84354497
theorem B6495545 : Blo 1350994 6495545 := bstep (se 2 (by rfl) ⟨2435829, by rfl⟩ : syracuseStep 6495545 = 4871659) B4871659
theorem B52002485 : Blo 1350994 52002485 := bstep (se 5 (by rfl) ⟨2437616, by rfl⟩ : syracuseStep 52002485 = 4875233) B4875233
theorem B9748507 : Blo 1350994 9748507 := bstep (se 1 (by rfl) ⟨7311380, by rfl⟩ : syracuseStep 9748507 = 14622761) B14622761
theorem B1351847 : Blo 1350994 1351847 := bstep (se 1 (by rfl) ⟨1013885, by rfl⟩ : syracuseStep 1351847 = 2027771) B2027771
theorem B3040199 : Blo 1350994 3040199 := bstep (se 1 (by rfl) ⟨2280149, by rfl⟩ : syracuseStep 3040199 = 4560299) B4560299
theorem B197297471 : Blo 1350994 197297471 := bstep (se 1 (by rfl) ⟨147973103, by rfl⟩ : syracuseStep 197297471 = 295946207) B295946207
theorem B3040595 : Blo 1350994 3040595 := bstep (se 1 (by rfl) ⟨2280446, by rfl⟩ : syracuseStep 3040595 = 4560893) B4560893
theorem B5778175 : Blo 1350994 5778175 := bstep (se 1 (by rfl) ⟨4333631, by rfl⟩ : syracuseStep 5778175 = 8667263) B8667263
theorem B2435903 : Blo 1350994 2435903 := bstep (se 1 (by rfl) ⟨1826927, by rfl⟩ : syracuseStep 2435903 = 3653855) B3653855
theorem B2026793 : Blo 1350994 2026793 := bstep (se 2 (by rfl) ⟨760047, by rfl⟩ : syracuseStep 2026793 = 1520095) B1520095
theorem B3903113 : Blo 1350994 3903113 := bstep (se 2 (by rfl) ⟨1463667, by rfl⟩ : syracuseStep 3903113 = 2927335) B2927335
theorem B3043439 : Blo 1350994 3043439 := bstep (se 1 (by rfl) ⟨2282579, by rfl⟩ : syracuseStep 3043439 = 4565159) B4565159
theorem B37490887 : Blo 1350994 37490887 := bstep (se 1 (by rfl) ⟨28118165, by rfl⟩ : syracuseStep 37490887 = 56236331) B56236331
theorem B2027759 : Blo 1350994 2027759 := bstep (se 1 (by rfl) ⟨1520819, by rfl⟩ : syracuseStep 2027759 = 3041639) B3041639
theorem B2028191 : Blo 1350994 2028191 := bstep (se 1 (by rfl) ⟨1521143, by rfl⟩ : syracuseStep 2028191 = 3042287) B3042287
theorem B4330363 : Blo 1350994 4330363 := bstep (se 1 (by rfl) ⟨3247772, by rfl⟩ : syracuseStep 4330363 = 6495545) B6495545
theorem B6846443 : Blo 1350994 6846443 := bstep (se 1 (by rfl) ⟨5134832, by rfl⟩ : syracuseStep 6846443 = 10269665) B10269665
theorem B6847091 : Blo 1350994 6847091 := bstep (se 1 (by rfl) ⟨5135318, by rfl⟩ : syracuseStep 6847091 = 10270637) B10270637
theorem B74964041 : Blo 1350994 74964041 := bstep (se 2 (by rfl) ⟨28111515, by rfl⟩ : syracuseStep 74964041 = 56223031) B56223031
theorem B9641375 : Blo 1350994 9641375 := bstep (se 1 (by rfl) ⟨7231031, by rfl⟩ : syracuseStep 9641375 = 14462063) B14462063
theorem B34668323 : Blo 1350994 34668323 := bstep (se 1 (by rfl) ⟨26001242, by rfl⟩ : syracuseStep 34668323 = 52002485) B52002485
theorem B1351839 : Blo 1350994 1351839 := bstep (se 1 (by rfl) ⟨1013879, by rfl⟩ : syracuseStep 1351839 = 2027759) B2027759
theorem B49987849 : Blo 1350994 49987849 := bstep (se 2 (by rfl) ⟨18745443, by rfl⟩ : syracuseStep 49987849 = 37490887) B37490887
theorem B1352127 : Blo 1350994 1352127 := bstep (se 1 (by rfl) ⟨1014095, by rfl⟩ : syracuseStep 1352127 = 2028191) B2028191
theorem B131531647 : Blo 1350994 131531647 := bstep (se 1 (by rfl) ⟨98648735, by rfl⟩ : syracuseStep 131531647 = 197297471) B197297471
theorem B4564295 : Blo 1350994 4564295 := bstep (se 1 (by rfl) ⟨3423221, by rfl⟩ : syracuseStep 4564295 = 6846443) B6846443
theorem B4564727 : Blo 1350994 4564727 := bstep (se 1 (by rfl) ⟨3423545, by rfl⟩ : syracuseStep 4564727 = 6847091) B6847091
theorem B1623935 : Blo 1350994 1623935 := bstep (se 1 (by rfl) ⟨1217951, by rfl⟩ : syracuseStep 1623935 = 2435903) B2435903
theorem B23112215 : Blo 1350994 23112215 := bstep (se 1 (by rfl) ⟨17334161, by rfl⟩ : syracuseStep 23112215 = 34668323) B34668323
theorem B2026799 : Blo 1350994 2026799 := bstep (se 1 (by rfl) ⟨1520099, by rfl⟩ : syracuseStep 2026799 = 3040199) B3040199
theorem B2027063 : Blo 1350994 2027063 := bstep (se 1 (by rfl) ⟨1520297, by rfl⟩ : syracuseStep 2027063 = 3040595) B3040595
theorem B7704233 : Blo 1350994 7704233 := bstep (se 2 (by rfl) ⟨2889087, by rfl⟩ : syracuseStep 7704233 = 5778175) B5778175
theorem B10408301 : Blo 1350994 10408301 := bstep (se 3 (by rfl) ⟨1951556, by rfl⟩ : syracuseStep 10408301 = 3903113) B3903113
theorem B49976027 : Blo 1350994 49976027 := bstep (se 1 (by rfl) ⟨37482020, by rfl⟩ : syracuseStep 49976027 = 74964041) B74964041
theorem B6427583 : Blo 1350994 6427583 := bstep (se 1 (by rfl) ⟨4820687, by rfl⟩ : syracuseStep 6427583 = 9641375) B9641375
theorem B12998009 : Blo 1350994 12998009 := bstep (se 2 (by rfl) ⟨4874253, by rfl⟩ : syracuseStep 12998009 = 9748507) B9748507
theorem B2028959 : Blo 1350994 2028959 := bstep (se 1 (by rfl) ⟨1521719, by rfl⟩ : syracuseStep 2028959 = 3043439) B3043439
theorem B5773817 : Blo 1350994 5773817 := bstep (se 2 (by rfl) ⟨2165181, by rfl⟩ : syracuseStep 5773817 = 4330363) B4330363
theorem B1351195 : Blo 1350994 1351195 := bstep (se 1 (by rfl) ⟨1013396, by rfl⟩ : syracuseStep 1351195 = 2026793) B2026793
theorem B6938867 : Blo 1350994 6938867 := bstep (se 1 (by rfl) ⟨5204150, by rfl⟩ : syracuseStep 6938867 = 10408301) B10408301
theorem B66650465 : Blo 1350994 66650465 := bstep (se 2 (by rfl) ⟨24993924, by rfl⟩ : syracuseStep 66650465 = 49987849) B49987849
theorem B33317351 : Blo 1350994 33317351 := bstep (se 1 (by rfl) ⟨24988013, by rfl⟩ : syracuseStep 33317351 = 49976027) B49976027
theorem B4285055 : Blo 1350994 4285055 := bstep (se 1 (by rfl) ⟨3213791, by rfl⟩ : syracuseStep 4285055 = 6427583) B6427583
theorem B1352639 : Blo 1350994 1352639 := bstep (se 1 (by rfl) ⟨1014479, by rfl⟩ : syracuseStep 1352639 = 2028959) B2028959
theorem B175375529 : Blo 1350994 175375529 := bstep (se 2 (by rfl) ⟨65765823, by rfl⟩ : syracuseStep 175375529 = 131531647) B131531647
theorem B3042863 : Blo 1350994 3042863 := bstep (se 1 (by rfl) ⟨2282147, by rfl⟩ : syracuseStep 3042863 = 4564295) B4564295
theorem B3043151 : Blo 1350994 3043151 := bstep (se 1 (by rfl) ⟨2282363, by rfl⟩ : syracuseStep 3043151 = 4564727) B4564727
theorem B4330493 : Blo 1350994 4330493 := bstep (se 3 (by rfl) ⟨811967, by rfl⟩ : syracuseStep 4330493 = 1623935) B1623935
theorem B8665339 : Blo 1350994 8665339 := bstep (se 1 (by rfl) ⟨6499004, by rfl⟩ : syracuseStep 8665339 = 12998009) B12998009
theorem B3849211 : Blo 1350994 3849211 := bstep (se 1 (by rfl) ⟨2886908, by rfl⟩ : syracuseStep 3849211 = 5773817) B5773817
theorem B15408143 : Blo 1350994 15408143 := bstep (se 1 (by rfl) ⟨11556107, by rfl⟩ : syracuseStep 15408143 = 23112215) B23112215
theorem B1351199 : Blo 1350994 1351199 := bstep (se 1 (by rfl) ⟨1013399, by rfl⟩ : syracuseStep 1351199 = 2026799) B2026799
theorem B1351375 : Blo 1350994 1351375 := bstep (se 1 (by rfl) ⟨1013531, by rfl⟩ : syracuseStep 1351375 = 2027063) B2027063
theorem B5136155 : Blo 1350994 5136155 := bstep (se 1 (by rfl) ⟨3852116, by rfl⟩ : syracuseStep 5136155 = 7704233) B7704233
theorem B116917019 : Blo 1350994 116917019 := bstep (se 1 (by rfl) ⟨87687764, by rfl⟩ : syracuseStep 116917019 = 175375529) B175375529
theorem B177734573 : Blo 1350994 177734573 := bstep (se 3 (by rfl) ⟨33325232, by rfl⟩ : syracuseStep 177734573 = 66650465) B66650465
theorem B22211567 : Blo 1350994 22211567 := bstep (se 1 (by rfl) ⟨16658675, by rfl⟩ : syracuseStep 22211567 = 33317351) B33317351
theorem B11553785 : Blo 1350994 11553785 := bstep (se 2 (by rfl) ⟨4332669, by rfl⟩ : syracuseStep 11553785 = 8665339) B8665339
theorem B2886995 : Blo 1350994 2886995 := bstep (se 1 (by rfl) ⟨2165246, by rfl⟩ : syracuseStep 2886995 = 4330493) B4330493
theorem B5132281 : Blo 1350994 5132281 := bstep (se 2 (by rfl) ⟨1924605, by rfl⟩ : syracuseStep 5132281 = 3849211) B3849211
theorem B2028575 : Blo 1350994 2028575 := bstep (se 1 (by rfl) ⟨1521431, by rfl⟩ : syracuseStep 2028575 = 3042863) B3042863
theorem B2028767 : Blo 1350994 2028767 := bstep (se 1 (by rfl) ⟨1521575, by rfl⟩ : syracuseStep 2028767 = 3043151) B3043151
theorem B2856703 : Blo 1350994 2856703 := bstep (se 1 (by rfl) ⟨2142527, by rfl⟩ : syracuseStep 2856703 = 4285055) B4285055
theorem B18503645 : Blo 1350994 18503645 := bstep (se 3 (by rfl) ⟨3469433, by rfl⟩ : syracuseStep 18503645 = 6938867) B6938867
theorem B10272095 : Blo 1350994 10272095 := bstep (se 1 (by rfl) ⟨7704071, by rfl⟩ : syracuseStep 10272095 = 15408143) B15408143
theorem B3424103 : Blo 1350994 3424103 := bstep (se 1 (by rfl) ⟨2568077, by rfl⟩ : syracuseStep 3424103 = 5136155) B5136155
theorem B118489715 : Blo 1350994 118489715 := bstep (se 1 (by rfl) ⟨88867286, by rfl⟩ : syracuseStep 118489715 = 177734573) B177734573
theorem B1352383 : Blo 1350994 1352383 := bstep (se 1 (by rfl) ⟨1014287, by rfl⟩ : syracuseStep 1352383 = 2028575) B2028575
theorem B1352511 : Blo 1350994 1352511 := bstep (se 1 (by rfl) ⟨1014383, by rfl⟩ : syracuseStep 1352511 = 2028767) B2028767
theorem B7702523 : Blo 1350994 7702523 := bstep (se 1 (by rfl) ⟨5776892, by rfl⟩ : syracuseStep 7702523 = 11553785) B11553785
theorem B49343053 : Blo 1350994 49343053 := bstep (se 3 (by rfl) ⟨9251822, by rfl⟩ : syracuseStep 49343053 = 18503645) B18503645
theorem B6843041 : Blo 1350994 6843041 := bstep (se 2 (by rfl) ⟨2566140, by rfl⟩ : syracuseStep 6843041 = 5132281) B5132281
theorem B14807711 : Blo 1350994 14807711 := bstep (se 1 (by rfl) ⟨11105783, by rfl⟩ : syracuseStep 14807711 = 22211567) B22211567
theorem B2282735 : Blo 1350994 2282735 := bstep (se 1 (by rfl) ⟨1712051, by rfl⟩ : syracuseStep 2282735 = 3424103) B3424103
theorem B77944679 : Blo 1350994 77944679 := bstep (se 1 (by rfl) ⟨58458509, by rfl⟩ : syracuseStep 77944679 = 116917019) B116917019
theorem B1924663 : Blo 1350994 1924663 := bstep (se 1 (by rfl) ⟨1443497, by rfl⟩ : syracuseStep 1924663 = 2886995) B2886995
theorem B6848063 : Blo 1350994 6848063 := bstep (se 1 (by rfl) ⟨5136047, by rfl⟩ : syracuseStep 6848063 = 10272095) B10272095
theorem B3808937 : Blo 1350994 3808937 := bstep (se 2 (by rfl) ⟨1428351, by rfl⟩ : syracuseStep 3808937 = 2856703) B2856703
theorem B9871807 : Blo 1350994 9871807 := bstep (se 1 (by rfl) ⟨7403855, by rfl⟩ : syracuseStep 9871807 = 14807711) B14807711
theorem B65790737 : Blo 1350994 65790737 := bstep (se 2 (by rfl) ⟨24671526, by rfl⟩ : syracuseStep 65790737 = 49343053) B49343053
theorem B51963119 : Blo 1350994 51963119 := bstep (se 1 (by rfl) ⟨38972339, by rfl⟩ : syracuseStep 51963119 = 77944679) B77944679
theorem B2566217 : Blo 1350994 2566217 := bstep (se 2 (by rfl) ⟨962331, by rfl⟩ : syracuseStep 2566217 = 1924663) B1924663
theorem B4565375 : Blo 1350994 4565375 := bstep (se 1 (by rfl) ⟨3424031, by rfl⟩ : syracuseStep 4565375 = 6848063) B6848063
theorem B78993143 : Blo 1350994 78993143 := bstep (se 1 (by rfl) ⟨59244857, by rfl⟩ : syracuseStep 78993143 = 118489715) B118489715
theorem B1521823 : Blo 1350994 1521823 := bstep (se 1 (by rfl) ⟨1141367, by rfl⟩ : syracuseStep 1521823 = 2282735) B2282735
theorem B5135015 : Blo 1350994 5135015 := bstep (se 1 (by rfl) ⟨3851261, by rfl⟩ : syracuseStep 5135015 = 7702523) B7702523
theorem B4562027 : Blo 1350994 4562027 := bstep (se 1 (by rfl) ⟨3421520, by rfl⟩ : syracuseStep 4562027 = 6843041) B6843041
theorem B2539291 : Blo 1350994 2539291 := bstep (se 1 (by rfl) ⟨1904468, by rfl⟩ : syracuseStep 2539291 = 3808937) B3808937
theorem B43860491 : Blo 1350994 43860491 := bstep (se 1 (by rfl) ⟨32895368, by rfl⟩ : syracuseStep 43860491 = 65790737) B65790737
theorem B3041351 : Blo 1350994 3041351 := bstep (se 1 (by rfl) ⟨2281013, by rfl⟩ : syracuseStep 3041351 = 4562027) B4562027
theorem B3385721 : Blo 1350994 3385721 := bstep (se 2 (by rfl) ⟨1269645, by rfl⟩ : syracuseStep 3385721 = 2539291) B2539291
theorem B52662095 : Blo 1350994 52662095 := bstep (se 1 (by rfl) ⟨39496571, by rfl⟩ : syracuseStep 52662095 = 78993143) B78993143
theorem B3043583 : Blo 1350994 3043583 := bstep (se 1 (by rfl) ⟨2282687, by rfl⟩ : syracuseStep 3043583 = 4565375) B4565375
theorem B2029097 : Blo 1350994 2029097 := bstep (se 2 (by rfl) ⟨760911, by rfl⟩ : syracuseStep 2029097 = 1521823) B1521823
theorem B13162409 : Blo 1350994 13162409 := bstep (se 2 (by rfl) ⟨4935903, by rfl⟩ : syracuseStep 13162409 = 9871807) B9871807
theorem B34642079 : Blo 1350994 34642079 := bstep (se 1 (by rfl) ⟨25981559, by rfl⟩ : syracuseStep 34642079 = 51963119) B51963119
theorem B1710811 : Blo 1350994 1710811 := bstep (se 1 (by rfl) ⟨1283108, by rfl⟩ : syracuseStep 1710811 = 2566217) B2566217
theorem B3423343 : Blo 1350994 3423343 := bstep (se 1 (by rfl) ⟨2567507, by rfl⟩ : syracuseStep 3423343 = 5135015) B5135015
theorem B1352731 : Blo 1350994 1352731 := bstep (se 1 (by rfl) ⟨1014548, by rfl⟩ : syracuseStep 1352731 = 2029097) B2029097
theorem B8774939 : Blo 1350994 8774939 := bstep (se 1 (by rfl) ⟨6581204, by rfl⟩ : syracuseStep 8774939 = 13162409) B13162409
theorem B23094719 : Blo 1350994 23094719 := bstep (se 1 (by rfl) ⟨17321039, by rfl⟩ : syracuseStep 23094719 = 34642079) B34642079
theorem B4564457 : Blo 1350994 4564457 := bstep (se 2 (by rfl) ⟨1711671, by rfl⟩ : syracuseStep 4564457 = 3423343) B3423343
theorem B29240327 : Blo 1350994 29240327 := bstep (se 1 (by rfl) ⟨21930245, by rfl⟩ : syracuseStep 29240327 = 43860491) B43860491
theorem B2281081 : Blo 1350994 2281081 := bstep (se 2 (by rfl) ⟨855405, by rfl⟩ : syracuseStep 2281081 = 1710811) B1710811
theorem B2027567 : Blo 1350994 2027567 := bstep (se 1 (by rfl) ⟨1520675, by rfl⟩ : syracuseStep 2027567 = 3041351) B3041351
theorem B2257147 : Blo 1350994 2257147 := bstep (se 1 (by rfl) ⟨1692860, by rfl⟩ : syracuseStep 2257147 = 3385721) B3385721
theorem B35108063 : Blo 1350994 35108063 := bstep (se 1 (by rfl) ⟨26331047, by rfl⟩ : syracuseStep 35108063 = 52662095) B52662095
theorem B2029055 : Blo 1350994 2029055 := bstep (se 1 (by rfl) ⟨1521791, by rfl⟩ : syracuseStep 2029055 = 3043583) B3043583
theorem B1351711 : Blo 1350994 1351711 := bstep (se 1 (by rfl) ⟨1013783, by rfl⟩ : syracuseStep 1351711 = 2027567) B2027567
theorem B23405375 : Blo 1350994 23405375 := bstep (se 1 (by rfl) ⟨17554031, by rfl⟩ : syracuseStep 23405375 = 35108063) B35108063
theorem B1352703 : Blo 1350994 1352703 := bstep (se 1 (by rfl) ⟨1014527, by rfl⟩ : syracuseStep 1352703 = 2029055) B2029055
theorem B3041441 : Blo 1350994 3041441 := bstep (se 2 (by rfl) ⟨1140540, by rfl⟩ : syracuseStep 3041441 = 2281081) B2281081
theorem B3009529 : Blo 1350994 3009529 := bstep (se 2 (by rfl) ⟨1128573, by rfl⟩ : syracuseStep 3009529 = 2257147) B2257147
theorem B23399837 : Blo 1350994 23399837 := bstep (se 3 (by rfl) ⟨4387469, by rfl⟩ : syracuseStep 23399837 = 8774939) B8774939
theorem B15396479 : Blo 1350994 15396479 := bstep (se 1 (by rfl) ⟨11547359, by rfl⟩ : syracuseStep 15396479 = 23094719) B23094719
theorem B3042971 : Blo 1350994 3042971 := bstep (se 1 (by rfl) ⟨2282228, by rfl⟩ : syracuseStep 3042971 = 4564457) B4564457
theorem B19493551 : Blo 1350994 19493551 := bstep (se 1 (by rfl) ⟨14620163, by rfl⟩ : syracuseStep 19493551 = 29240327) B29240327
theorem B15599891 : Blo 1350994 15599891 := bstep (se 1 (by rfl) ⟨11699918, by rfl⟩ : syracuseStep 15599891 = 23399837) B23399837
theorem B2027627 : Blo 1350994 2027627 := bstep (se 1 (by rfl) ⟨1520720, by rfl⟩ : syracuseStep 2027627 = 3041441) B3041441
theorem B2028647 : Blo 1350994 2028647 := bstep (se 1 (by rfl) ⟨1521485, by rfl⟩ : syracuseStep 2028647 = 3042971) B3042971
theorem B25991401 : Blo 1350994 25991401 := bstep (se 2 (by rfl) ⟨9746775, by rfl⟩ : syracuseStep 25991401 = 19493551) B19493551
theorem B4012705 : Blo 1350994 4012705 := bstep (se 2 (by rfl) ⟨1504764, by rfl⟩ : syracuseStep 4012705 = 3009529) B3009529
theorem B62414333 : Blo 1350994 62414333 := bstep (se 3 (by rfl) ⟨11702687, by rfl⟩ : syracuseStep 62414333 = 23405375) B23405375
theorem B10264319 : Blo 1350994 10264319 := bstep (se 1 (by rfl) ⟨7698239, by rfl⟩ : syracuseStep 10264319 = 15396479) B15396479
theorem B1351751 : Blo 1350994 1351751 := bstep (se 1 (by rfl) ⟨1013813, by rfl⟩ : syracuseStep 1351751 = 2027627) B2027627
theorem B1352431 : Blo 1350994 1352431 := bstep (se 1 (by rfl) ⟨1014323, by rfl⟩ : syracuseStep 1352431 = 2028647) B2028647
theorem B5350273 : Blo 1350994 5350273 := bstep (se 2 (by rfl) ⟨2006352, by rfl⟩ : syracuseStep 5350273 = 4012705) B4012705
theorem B41609555 : Blo 1350994 41609555 := bstep (se 1 (by rfl) ⟨31207166, by rfl⟩ : syracuseStep 41609555 = 62414333) B62414333
theorem B6842879 : Blo 1350994 6842879 := bstep (se 1 (by rfl) ⟨5132159, by rfl⟩ : syracuseStep 6842879 = 10264319) B10264319
theorem B34655201 : Blo 1350994 34655201 := bstep (se 2 (by rfl) ⟨12995700, by rfl⟩ : syracuseStep 34655201 = 25991401) B25991401
theorem B10399927 : Blo 1350994 10399927 := bstep (se 1 (by rfl) ⟨7799945, by rfl⟩ : syracuseStep 10399927 = 15599891) B15599891
theorem B27739703 : Blo 1350994 27739703 := bstep (se 1 (by rfl) ⟨20804777, by rfl⟩ : syracuseStep 27739703 = 41609555) B41609555
theorem B23103467 : Blo 1350994 23103467 := bstep (se 1 (by rfl) ⟨17327600, by rfl⟩ : syracuseStep 23103467 = 34655201) B34655201
theorem B28534789 : Blo 1350994 28534789 := bstep (se 4 (by rfl) ⟨2675136, by rfl⟩ : syracuseStep 28534789 = 5350273) B5350273
theorem B13866569 : Blo 1350994 13866569 := bstep (se 2 (by rfl) ⟨5199963, by rfl⟩ : syracuseStep 13866569 = 10399927) B10399927
theorem B4561919 : Blo 1350994 4561919 := bstep (se 1 (by rfl) ⟨3421439, by rfl⟩ : syracuseStep 4561919 = 6842879) B6842879
theorem B15402311 : Blo 1350994 15402311 := bstep (se 1 (by rfl) ⟨11551733, by rfl⟩ : syracuseStep 15402311 = 23103467) B23103467
theorem B3041279 : Blo 1350994 3041279 := bstep (se 1 (by rfl) ⟨2280959, by rfl⟩ : syracuseStep 3041279 = 4561919) B4561919
theorem B38046385 : Blo 1350994 38046385 := bstep (se 2 (by rfl) ⟨14267394, by rfl⟩ : syracuseStep 38046385 = 28534789) B28534789
theorem B9244379 : Blo 1350994 9244379 := bstep (se 1 (by rfl) ⟨6933284, by rfl⟩ : syracuseStep 9244379 = 13866569) B13866569
theorem B73972541 : Blo 1350994 73972541 := bstep (se 3 (by rfl) ⟨13869851, by rfl⟩ : syracuseStep 73972541 = 27739703) B27739703
theorem B24651677 : Blo 1350994 24651677 := bstep (se 3 (by rfl) ⟨4622189, by rfl⟩ : syracuseStep 24651677 = 9244379) B9244379
theorem B10268207 : Blo 1350994 10268207 := bstep (se 1 (by rfl) ⟨7701155, by rfl⟩ : syracuseStep 10268207 = 15402311) B15402311
theorem B50728513 : Blo 1350994 50728513 := bstep (se 2 (by rfl) ⟨19023192, by rfl⟩ : syracuseStep 50728513 = 38046385) B38046385
theorem B2027519 : Blo 1350994 2027519 := bstep (se 1 (by rfl) ⟨1520639, by rfl⟩ : syracuseStep 2027519 = 3041279) B3041279
theorem B197260109 : Blo 1350994 197260109 := bstep (se 3 (by rfl) ⟨36986270, by rfl⟩ : syracuseStep 197260109 = 73972541) B73972541
theorem B131506739 : Blo 1350994 131506739 := bstep (se 1 (by rfl) ⟨98630054, by rfl⟩ : syracuseStep 131506739 = 197260109) B197260109
theorem B16434451 : Blo 1350994 16434451 := bstep (se 1 (by rfl) ⟨12325838, by rfl⟩ : syracuseStep 16434451 = 24651677) B24651677
theorem B67638017 : Blo 1350994 67638017 := bstep (se 2 (by rfl) ⟨25364256, by rfl⟩ : syracuseStep 67638017 = 50728513) B50728513
theorem B6845471 : Blo 1350994 6845471 := bstep (se 1 (by rfl) ⟨5134103, by rfl⟩ : syracuseStep 6845471 = 10268207) B10268207
theorem B1351679 : Blo 1350994 1351679 := bstep (se 1 (by rfl) ⟨1013759, by rfl⟩ : syracuseStep 1351679 = 2027519) B2027519
theorem B87671159 : Blo 1350994 87671159 := bstep (se 1 (by rfl) ⟨65753369, by rfl⟩ : syracuseStep 87671159 = 131506739) B131506739
theorem B4563647 : Blo 1350994 4563647 := bstep (se 1 (by rfl) ⟨3422735, by rfl⟩ : syracuseStep 4563647 = 6845471) B6845471
theorem B45092011 : Blo 1350994 45092011 := bstep (se 1 (by rfl) ⟨33819008, by rfl⟩ : syracuseStep 45092011 = 67638017) B67638017
theorem B21912601 : Blo 1350994 21912601 := bstep (se 2 (by rfl) ⟨8217225, by rfl⟩ : syracuseStep 21912601 = 16434451) B16434451
theorem B60122681 : Blo 1350994 60122681 := bstep (se 2 (by rfl) ⟨22546005, by rfl⟩ : syracuseStep 60122681 = 45092011) B45092011
theorem B3042431 : Blo 1350994 3042431 := bstep (se 1 (by rfl) ⟨2281823, by rfl⟩ : syracuseStep 3042431 = 4563647) B4563647
theorem B29216801 : Blo 1350994 29216801 := bstep (se 2 (by rfl) ⟨10956300, by rfl⟩ : syracuseStep 29216801 = 21912601) B21912601
theorem B58447439 : Blo 1350994 58447439 := bstep (se 1 (by rfl) ⟨43835579, by rfl⟩ : syracuseStep 58447439 = 87671159) B87671159
theorem B38964959 : Blo 1350994 38964959 := bstep (se 1 (by rfl) ⟨29223719, by rfl⟩ : syracuseStep 38964959 = 58447439) B58447439
theorem B2028287 : Blo 1350994 2028287 := bstep (se 1 (by rfl) ⟨1521215, by rfl⟩ : syracuseStep 2028287 = 3042431) B3042431
theorem B19477867 : Blo 1350994 19477867 := bstep (se 1 (by rfl) ⟨14608400, by rfl⟩ : syracuseStep 19477867 = 29216801) B29216801
theorem B40081787 : Blo 1350994 40081787 := bstep (se 1 (by rfl) ⟨30061340, by rfl⟩ : syracuseStep 40081787 = 60122681) B60122681
theorem B1352191 : Blo 1350994 1352191 := bstep (se 1 (by rfl) ⟨1014143, by rfl⟩ : syracuseStep 1352191 = 2028287) B2028287
theorem B25970489 : Blo 1350994 25970489 := bstep (se 2 (by rfl) ⟨9738933, by rfl⟩ : syracuseStep 25970489 = 19477867) B19477867
theorem B26721191 : Blo 1350994 26721191 := bstep (se 1 (by rfl) ⟨20040893, by rfl⟩ : syracuseStep 26721191 = 40081787) B40081787
theorem B25976639 : Blo 1350994 25976639 := bstep (se 1 (by rfl) ⟨19482479, by rfl⟩ : syracuseStep 25976639 = 38964959) B38964959
theorem B17313659 : Blo 1350994 17313659 := bstep (se 1 (by rfl) ⟨12985244, by rfl⟩ : syracuseStep 17313659 = 25970489) B25970489
theorem B17814127 : Blo 1350994 17814127 := bstep (se 1 (by rfl) ⟨13360595, by rfl⟩ : syracuseStep 17814127 = 26721191) B26721191
theorem B17317759 : Blo 1350994 17317759 := bstep (se 1 (by rfl) ⟨12988319, by rfl⟩ : syracuseStep 17317759 = 25976639) B25976639
theorem B23752169 : Blo 1350994 23752169 := bstep (se 2 (by rfl) ⟨8907063, by rfl⟩ : syracuseStep 23752169 = 17814127) B17814127
theorem B23090345 : Blo 1350994 23090345 := bstep (se 2 (by rfl) ⟨8658879, by rfl⟩ : syracuseStep 23090345 = 17317759) B17317759
theorem B11542439 : Blo 1350994 11542439 := bstep (se 1 (by rfl) ⟨8656829, by rfl⟩ : syracuseStep 11542439 = 17313659) B17313659
theorem B15393563 : Blo 1350994 15393563 := bstep (se 1 (by rfl) ⟨11545172, by rfl⟩ : syracuseStep 15393563 = 23090345) B23090345
theorem B7694959 : Blo 1350994 7694959 := bstep (se 1 (by rfl) ⟨5771219, by rfl⟩ : syracuseStep 7694959 = 11542439) B11542439
theorem B15834779 : Blo 1350994 15834779 := bstep (se 1 (by rfl) ⟨11876084, by rfl⟩ : syracuseStep 15834779 = 23752169) B23752169
theorem B10259945 : Blo 1350994 10259945 := bstep (se 2 (by rfl) ⟨3847479, by rfl⟩ : syracuseStep 10259945 = 7694959) B7694959
theorem B10556519 : Blo 1350994 10556519 := bstep (se 1 (by rfl) ⟨7917389, by rfl⟩ : syracuseStep 10556519 = 15834779) B15834779
theorem B10262375 : Blo 1350994 10262375 := bstep (se 1 (by rfl) ⟨7696781, by rfl⟩ : syracuseStep 10262375 = 15393563) B15393563
theorem B6841583 : Blo 1350994 6841583 := bstep (se 1 (by rfl) ⟨5131187, by rfl⟩ : syracuseStep 6841583 = 10262375) B10262375
theorem B112602869 : Blo 1350994 112602869 := bstep (se 5 (by rfl) ⟨5278259, by rfl⟩ : syracuseStep 112602869 = 10556519) B10556519
theorem B6839963 : Blo 1350994 6839963 := bstep (se 1 (by rfl) ⟨5129972, by rfl⟩ : syracuseStep 6839963 = 10259945) B10259945
theorem B4559975 : Blo 1350994 4559975 := bstep (se 1 (by rfl) ⟨3419981, by rfl⟩ : syracuseStep 4559975 = 6839963) B6839963
theorem B75068579 : Blo 1350994 75068579 := bstep (se 1 (by rfl) ⟨56301434, by rfl⟩ : syracuseStep 75068579 = 112602869) B112602869
theorem B4561055 : Blo 1350994 4561055 := bstep (se 1 (by rfl) ⟨3420791, by rfl⟩ : syracuseStep 4561055 = 6841583) B6841583
theorem B3039983 : Blo 1350994 3039983 := bstep (se 1 (by rfl) ⟨2279987, by rfl⟩ : syracuseStep 3039983 = 4559975) B4559975
theorem B3040703 : Blo 1350994 3040703 := bstep (se 1 (by rfl) ⟨2280527, by rfl⟩ : syracuseStep 3040703 = 4561055) B4561055
theorem B200182877 : Blo 1350994 200182877 := bstep (se 3 (by rfl) ⟨37534289, by rfl⟩ : syracuseStep 200182877 = 75068579) B75068579
theorem B2026655 : Blo 1350994 2026655 := bstep (se 1 (by rfl) ⟨1519991, by rfl⟩ : syracuseStep 2026655 = 3039983) B3039983
theorem B2027135 : Blo 1350994 2027135 := bstep (se 1 (by rfl) ⟨1520351, by rfl⟩ : syracuseStep 2027135 = 3040703) B3040703
theorem B133455251 : Blo 1350994 133455251 := bstep (se 1 (by rfl) ⟨100091438, by rfl⟩ : syracuseStep 133455251 = 200182877) B200182877
theorem B88970167 : Blo 1350994 88970167 := bstep (se 1 (by rfl) ⟨66727625, by rfl⟩ : syracuseStep 88970167 = 133455251) B133455251
theorem B1351103 : Blo 1350994 1351103 := bstep (se 1 (by rfl) ⟨1013327, by rfl⟩ : syracuseStep 1351103 = 2026655) B2026655
theorem B1351423 : Blo 1350994 1351423 := bstep (se 1 (by rfl) ⟨1013567, by rfl⟩ : syracuseStep 1351423 = 2027135) B2027135
theorem B118626889 : Blo 1350994 118626889 := bstep (se 2 (by rfl) ⟨44485083, by rfl⟩ : syracuseStep 118626889 = 88970167) B88970167
theorem B158169185 : Blo 1350994 158169185 := bstep (se 2 (by rfl) ⟨59313444, by rfl⟩ : syracuseStep 158169185 = 118626889) B118626889
theorem B105446123 : Blo 1350994 105446123 := bstep (se 1 (by rfl) ⟨79084592, by rfl⟩ : syracuseStep 105446123 = 158169185) B158169185
theorem B70297415 : Blo 1350994 70297415 := bstep (se 1 (by rfl) ⟨52723061, by rfl⟩ : syracuseStep 70297415 = 105446123) B105446123
theorem B46864943 : Blo 1350994 46864943 := bstep (se 1 (by rfl) ⟨35148707, by rfl⟩ : syracuseStep 46864943 = 70297415) B70297415
theorem B31243295 : Blo 1350994 31243295 := bstep (se 1 (by rfl) ⟨23432471, by rfl⟩ : syracuseStep 31243295 = 46864943) B46864943
theorem B20828863 : Blo 1350994 20828863 := bstep (se 1 (by rfl) ⟨15621647, by rfl⟩ : syracuseStep 20828863 = 31243295) B31243295
theorem B27771817 : Blo 1350994 27771817 := bstep (se 2 (by rfl) ⟨10414431, by rfl⟩ : syracuseStep 27771817 = 20828863) B20828863
theorem B37029089 : Blo 1350994 37029089 := bstep (se 2 (by rfl) ⟨13885908, by rfl⟩ : syracuseStep 37029089 = 27771817) B27771817
theorem B24686059 : Blo 1350994 24686059 := bstep (se 1 (by rfl) ⟨18514544, by rfl⟩ : syracuseStep 24686059 = 37029089) B37029089
theorem B32914745 : Blo 1350994 32914745 := bstep (se 2 (by rfl) ⟨12343029, by rfl⟩ : syracuseStep 32914745 = 24686059) B24686059
theorem B21943163 : Blo 1350994 21943163 := bstep (se 1 (by rfl) ⟨16457372, by rfl⟩ : syracuseStep 21943163 = 32914745) B32914745
theorem B14628775 : Blo 1350994 14628775 := bstep (se 1 (by rfl) ⟨10971581, by rfl⟩ : syracuseStep 14628775 = 21943163) B21943163
theorem B19505033 : Blo 1350994 19505033 := bstep (se 2 (by rfl) ⟨7314387, by rfl⟩ : syracuseStep 19505033 = 14628775) B14628775
theorem B13003355 : Blo 1350994 13003355 := bstep (se 1 (by rfl) ⟨9752516, by rfl⟩ : syracuseStep 13003355 = 19505033) B19505033
theorem B8668903 : Blo 1350994 8668903 := bstep (se 1 (by rfl) ⟨6501677, by rfl⟩ : syracuseStep 8668903 = 13003355) B13003355
theorem B11558537 : Blo 1350994 11558537 := bstep (se 2 (by rfl) ⟨4334451, by rfl⟩ : syracuseStep 11558537 = 8668903) B8668903
theorem B7705691 : Blo 1350994 7705691 := bstep (se 1 (by rfl) ⟨5779268, by rfl⟩ : syracuseStep 7705691 = 11558537) B11558537
theorem B5137127 : Blo 1350994 5137127 := bstep (se 1 (by rfl) ⟨3852845, by rfl⟩ : syracuseStep 5137127 = 7705691) B7705691
theorem B3424751 : Blo 1350994 3424751 := bstep (se 1 (by rfl) ⟨2568563, by rfl⟩ : syracuseStep 3424751 = 5137127) B5137127
theorem B2283167 : Blo 1350994 2283167 := bstep (se 1 (by rfl) ⟨1712375, by rfl⟩ : syracuseStep 2283167 = 3424751) B3424751
theorem B1522111 : Blo 1350994 1522111 := bstep (se 1 (by rfl) ⟨1141583, by rfl⟩ : syracuseStep 1522111 = 2283167) B2283167
theorem B2029481 : Blo 1350994 2029481 := bstep (se 2 (by rfl) ⟨761055, by rfl⟩ : syracuseStep 2029481 = 1522111) B1522111
theorem B1352987 : Blo 1350994 1352987 := bstep (se 1 (by rfl) ⟨1014740, by rfl⟩ : syracuseStep 1352987 = 2029481) B2029481

theorem C0 (j : ℕ) (h1 : 337748 ≤ j) (h2 : j ≤ 338247) : Blo 1350994 (4 * j + 3) := by
  interval_cases j
  · exact B1350995
  · exact B1350999
  · exact B1351003
  · exact B1351007
  · exact B1351011
  · exact B1351015
  · exact B1351019
  · exact B1351023
  · exact B1351027
  · exact B1351031
  · exact B1351035
  · exact B1351039
  · exact B1351043
  · exact B1351047
  · exact B1351051
  · exact B1351055
  · exact B1351059
  · exact B1351063
  · exact B1351067
  · exact B1351071
  · exact B1351075
  · exact B1351079
  · exact B1351083
  · exact B1351087
  · exact B1351091
  · exact B1351095
  · exact B1351099
  · exact B1351103
  · exact B1351107
  · exact B1351111
  · exact B1351115
  · exact B1351119
  · exact B1351123
  · exact B1351127
  · exact B1351131
  · exact B1351135
  · exact B1351139
  · exact B1351143
  · exact B1351147
  · exact B1351151
  · exact B1351155
  · exact B1351159
  · exact B1351163
  · exact B1351167
  · exact B1351171
  · exact B1351175
  · exact B1351179
  · exact B1351183
  · exact B1351187
  · exact B1351191
  · exact B1351195
  · exact B1351199
  · exact B1351203
  · exact B1351207
  · exact B1351211
  · exact B1351215
  · exact B1351219
  · exact B1351223
  · exact B1351227
  · exact B1351231
  · exact B1351235
  · exact B1351239
  · exact B1351243
  · exact B1351247
  · exact B1351251
  · exact B1351255
  · exact B1351259
  · exact B1351263
  · exact B1351267
  · exact B1351271
  · exact B1351275
  · exact B1351279
  · exact B1351283
  · exact B1351287
  · exact B1351291
  · exact B1351295
  · exact B1351299
  · exact B1351303
  · exact B1351307
  · exact B1351311
  · exact B1351315
  · exact B1351319
  · exact B1351323
  · exact B1351327
  · exact B1351331
  · exact B1351335
  · exact B1351339
  · exact B1351343
  · exact B1351347
  · exact B1351351
  · exact B1351355
  · exact B1351359
  · exact B1351363
  · exact B1351367
  · exact B1351371
  · exact B1351375
  · exact B1351379
  · exact B1351383
  · exact B1351387
  · exact B1351391
  · exact B1351395
  · exact B1351399
  · exact B1351403
  · exact B1351407
  · exact B1351411
  · exact B1351415
  · exact B1351419
  · exact B1351423
  · exact B1351427
  · exact B1351431
  · exact B1351435
  · exact B1351439
  · exact B1351443
  · exact B1351447
  · exact B1351451
  · exact B1351455
  · exact B1351459
  · exact B1351463
  · exact B1351467
  · exact B1351471
  · exact B1351475
  · exact B1351479
  · exact B1351483
  · exact B1351487
  · exact B1351491
  · exact B1351495
  · exact B1351499
  · exact B1351503
  · exact B1351507
  · exact B1351511
  · exact B1351515
  · exact B1351519
  · exact B1351523
  · exact B1351527
  · exact B1351531
  · exact B1351535
  · exact B1351539
  · exact B1351543
  · exact B1351547
  · exact B1351551
  · exact B1351555
  · exact B1351559
  · exact B1351563
  · exact B1351567
  · exact B1351571
  · exact B1351575
  · exact B1351579
  · exact B1351583
  · exact B1351587
  · exact B1351591
  · exact B1351595
  · exact B1351599
  · exact B1351603
  · exact B1351607
  · exact B1351611
  · exact B1351615
  · exact B1351619
  · exact B1351623
  · exact B1351627
  · exact B1351631
  · exact B1351635
  · exact B1351639
  · exact B1351643
  · exact B1351647
  · exact B1351651
  · exact B1351655
  · exact B1351659
  · exact B1351663
  · exact B1351667
  · exact B1351671
  · exact B1351675
  · exact B1351679
  · exact B1351683
  · exact B1351687
  · exact B1351691
  · exact B1351695
  · exact B1351699
  · exact B1351703
  · exact B1351707
  · exact B1351711
  · exact B1351715
  · exact B1351719
  · exact B1351723
  · exact B1351727
  · exact B1351731
  · exact B1351735
  · exact B1351739
  · exact B1351743
  · exact B1351747
  · exact B1351751
  · exact B1351755
  · exact B1351759
  · exact B1351763
  · exact B1351767
  · exact B1351771
  · exact B1351775
  · exact B1351779
  · exact B1351783
  · exact B1351787
  · exact B1351791
  · exact B1351795
  · exact B1351799
  · exact B1351803
  · exact B1351807
  · exact B1351811
  · exact B1351815
  · exact B1351819
  · exact B1351823
  · exact B1351827
  · exact B1351831
  · exact B1351835
  · exact B1351839
  · exact B1351843
  · exact B1351847
  · exact B1351851
  · exact B1351855
  · exact B1351859
  · exact B1351863
  · exact B1351867
  · exact B1351871
  · exact B1351875
  · exact B1351879
  · exact B1351883
  · exact B1351887
  · exact B1351891
  · exact B1351895
  · exact B1351899
  · exact B1351903
  · exact B1351907
  · exact B1351911
  · exact B1351915
  · exact B1351919
  · exact B1351923
  · exact B1351927
  · exact B1351931
  · exact B1351935
  · exact B1351939
  · exact B1351943
  · exact B1351947
  · exact B1351951
  · exact B1351955
  · exact B1351959
  · exact B1351963
  · exact B1351967
  · exact B1351971
  · exact B1351975
  · exact B1351979
  · exact B1351983
  · exact B1351987
  · exact B1351991
  · exact B1351995
  · exact B1351999
  · exact B1352003
  · exact B1352007
  · exact B1352011
  · exact B1352015
  · exact B1352019
  · exact B1352023
  · exact B1352027
  · exact B1352031
  · exact B1352035
  · exact B1352039
  · exact B1352043
  · exact B1352047
  · exact B1352051
  · exact B1352055
  · exact B1352059
  · exact B1352063
  · exact B1352067
  · exact B1352071
  · exact B1352075
  · exact B1352079
  · exact B1352083
  · exact B1352087
  · exact B1352091
  · exact B1352095
  · exact B1352099
  · exact B1352103
  · exact B1352107
  · exact B1352111
  · exact B1352115
  · exact B1352119
  · exact B1352123
  · exact B1352127
  · exact B1352131
  · exact B1352135
  · exact B1352139
  · exact B1352143
  · exact B1352147
  · exact B1352151
  · exact B1352155
  · exact B1352159
  · exact B1352163
  · exact B1352167
  · exact B1352171
  · exact B1352175
  · exact B1352179
  · exact B1352183
  · exact B1352187
  · exact B1352191
  · exact B1352195
  · exact B1352199
  · exact B1352203
  · exact B1352207
  · exact B1352211
  · exact B1352215
  · exact B1352219
  · exact B1352223
  · exact B1352227
  · exact B1352231
  · exact B1352235
  · exact B1352239
  · exact B1352243
  · exact B1352247
  · exact B1352251
  · exact B1352255
  · exact B1352259
  · exact B1352263
  · exact B1352267
  · exact B1352271
  · exact B1352275
  · exact B1352279
  · exact B1352283
  · exact B1352287
  · exact B1352291
  · exact B1352295
  · exact B1352299
  · exact B1352303
  · exact B1352307
  · exact B1352311
  · exact B1352315
  · exact B1352319
  · exact B1352323
  · exact B1352327
  · exact B1352331
  · exact B1352335
  · exact B1352339
  · exact B1352343
  · exact B1352347
  · exact B1352351
  · exact B1352355
  · exact B1352359
  · exact B1352363
  · exact B1352367
  · exact B1352371
  · exact B1352375
  · exact B1352379
  · exact B1352383
  · exact B1352387
  · exact B1352391
  · exact B1352395
  · exact B1352399
  · exact B1352403
  · exact B1352407
  · exact B1352411
  · exact B1352415
  · exact B1352419
  · exact B1352423
  · exact B1352427
  · exact B1352431
  · exact B1352435
  · exact B1352439
  · exact B1352443
  · exact B1352447
  · exact B1352451
  · exact B1352455
  · exact B1352459
  · exact B1352463
  · exact B1352467
  · exact B1352471
  · exact B1352475
  · exact B1352479
  · exact B1352483
  · exact B1352487
  · exact B1352491
  · exact B1352495
  · exact B1352499
  · exact B1352503
  · exact B1352507
  · exact B1352511
  · exact B1352515
  · exact B1352519
  · exact B1352523
  · exact B1352527
  · exact B1352531
  · exact B1352535
  · exact B1352539
  · exact B1352543
  · exact B1352547
  · exact B1352551
  · exact B1352555
  · exact B1352559
  · exact B1352563
  · exact B1352567
  · exact B1352571
  · exact B1352575
  · exact B1352579
  · exact B1352583
  · exact B1352587
  · exact B1352591
  · exact B1352595
  · exact B1352599
  · exact B1352603
  · exact B1352607
  · exact B1352611
  · exact B1352615
  · exact B1352619
  · exact B1352623
  · exact B1352627
  · exact B1352631
  · exact B1352635
  · exact B1352639
  · exact B1352643
  · exact B1352647
  · exact B1352651
  · exact B1352655
  · exact B1352659
  · exact B1352663
  · exact B1352667
  · exact B1352671
  · exact B1352675
  · exact B1352679
  · exact B1352683
  · exact B1352687
  · exact B1352691
  · exact B1352695
  · exact B1352699
  · exact B1352703
  · exact B1352707
  · exact B1352711
  · exact B1352715
  · exact B1352719
  · exact B1352723
  · exact B1352727
  · exact B1352731
  · exact B1352735
  · exact B1352739
  · exact B1352743
  · exact B1352747
  · exact B1352751
  · exact B1352755
  · exact B1352759
  · exact B1352763
  · exact B1352767
  · exact B1352771
  · exact B1352775
  · exact B1352779
  · exact B1352783
  · exact B1352787
  · exact B1352791
  · exact B1352795
  · exact B1352799
  · exact B1352803
  · exact B1352807
  · exact B1352811
  · exact B1352815
  · exact B1352819
  · exact B1352823
  · exact B1352827
  · exact B1352831
  · exact B1352835
  · exact B1352839
  · exact B1352843
  · exact B1352847
  · exact B1352851
  · exact B1352855
  · exact B1352859
  · exact B1352863
  · exact B1352867
  · exact B1352871
  · exact B1352875
  · exact B1352879
  · exact B1352883
  · exact B1352887
  · exact B1352891
  · exact B1352895
  · exact B1352899
  · exact B1352903
  · exact B1352907
  · exact B1352911
  · exact B1352915
  · exact B1352919
  · exact B1352923
  · exact B1352927
  · exact B1352931
  · exact B1352935
  · exact B1352939
  · exact B1352943
  · exact B1352947
  · exact B1352951
  · exact B1352955
  · exact B1352959
  · exact B1352963
  · exact B1352967
  · exact B1352971
  · exact B1352975
  · exact B1352979
  · exact B1352983
  · exact B1352987
  · exact B1352991

theorem solution (m : ℕ) (hlo : 1350994 ≤ m) (hhi : m ≤ 1352994) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 337748 ≤ j := by omega
    have hj2 : j ≤ 338247 := by omega
    have hb : Blo 1350994 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
