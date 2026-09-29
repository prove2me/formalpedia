-- Prove2me | solution 1 for syracuse_descends_range_574812_578812
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:48:40.15572+00:00
-- url     : https://prove2.me/submissions/24b28276-a14f-4525-8987-e3456c45571b

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


theorem B2916485 : Blo 574812 2916485 := bbase (se 4 (by rfl) ⟨273420, by rfl⟩ : syracuseStep 2916485 = 546841) (by norm_num)
theorem B1475101 : Blo 574812 1475101 := bbase (se 3 (by rfl) ⟨276581, by rfl⟩ : syracuseStep 1475101 = 553163) (by norm_num)
theorem B1966693 : Blo 574812 1966693 := bbase (se 4 (by rfl) ⟨184377, by rfl⟩ : syracuseStep 1966693 = 368755) (by norm_num)
theorem B4915829 : Blo 574812 4915829 := bbase (se 5 (by rfl) ⟨230429, by rfl⟩ : syracuseStep 4915829 = 460859) (by norm_num)
theorem B819829 : Blo 574812 819829 := bbase (se 5 (by rfl) ⟨38429, by rfl⟩ : syracuseStep 819829 = 76859) (by norm_num)
theorem B3277493 : Blo 574812 3277493 := bbase (se 5 (by rfl) ⟨153632, by rfl⟩ : syracuseStep 3277493 = 307265) (by norm_num)
theorem B2458309 : Blo 574812 2458309 := bbase (se 4 (by rfl) ⟨230466, by rfl⟩ : syracuseStep 2458309 = 460933) (by norm_num)
theorem B2458325 : Blo 574812 2458325 := bbase (se 7 (by rfl) ⟨28808, by rfl⟩ : syracuseStep 2458325 = 57617) (by norm_num)
theorem B623417 : Blo 574812 623417 := bbase (se 2 (by rfl) ⟨233781, by rfl⟩ : syracuseStep 623417 = 467563) (by norm_num)
theorem B1639237 : Blo 574812 1639237 := bbase (se 4 (by rfl) ⟨153678, by rfl⟩ : syracuseStep 1639237 = 307357) (by norm_num)
theorem B983909 : Blo 574812 983909 := bbase (se 4 (by rfl) ⟨92241, by rfl⟩ : syracuseStep 983909 = 184483) (by norm_num)
theorem B2196341 : Blo 574812 2196341 := bbase (se 5 (by rfl) ⟨102953, by rfl⟩ : syracuseStep 2196341 = 205907) (by norm_num)
theorem B656257 : Blo 574812 656257 := bbase (se 2 (by rfl) ⟨246096, by rfl⟩ : syracuseStep 656257 = 492193) (by norm_num)
theorem B7406549 : Blo 574812 7406549 := bbase (se 7 (by rfl) ⟨86795, by rfl⟩ : syracuseStep 7406549 = 173591) (by norm_num)
theorem B2196629 : Blo 574812 2196629 := bbase (se 6 (by rfl) ⟨51483, by rfl⟩ : syracuseStep 2196629 = 102967) (by norm_num)
theorem B820621 : Blo 574812 820621 := bbase (se 3 (by rfl) ⟨153866, by rfl⟩ : syracuseStep 820621 = 307733) (by norm_num)
theorem B2917781 : Blo 574812 2917781 := bbase (se 6 (by rfl) ⟨68385, by rfl⟩ : syracuseStep 2917781 = 136771) (by norm_num)
theorem B984565 : Blo 574812 984565 := bbase (se 5 (by rfl) ⟨46151, by rfl⟩ : syracuseStep 984565 = 92303) (by norm_num)
theorem B820957 : Blo 574812 820957 := bbase (se 3 (by rfl) ⟨153929, by rfl⟩ : syracuseStep 820957 = 307859) (by norm_num)
theorem B5605141 : Blo 574812 5605141 := bbase (se 6 (by rfl) ⟨131370, by rfl⟩ : syracuseStep 5605141 = 262741) (by norm_num)
theorem B3278677 : Blo 574812 3278677 := bbase (se 9 (by rfl) ⟨9605, by rfl⟩ : syracuseStep 3278677 = 19211) (by norm_num)
theorem B1640341 : Blo 574812 1640341 := bbase (se 6 (by rfl) ⟨38445, by rfl⟩ : syracuseStep 1640341 = 76891) (by norm_num)
theorem B821173 : Blo 574812 821173 := bbase (se 5 (by rfl) ⟨38492, by rfl⟩ : syracuseStep 821173 = 76985) (by norm_num)
theorem B821549 : Blo 574812 821549 := bbase (se 3 (by rfl) ⟨154040, by rfl⟩ : syracuseStep 821549 = 308081) (by norm_num)
theorem B3705173 : Blo 574812 3705173 := bbase (se 10 (by rfl) ⟨5427, by rfl⟩ : syracuseStep 3705173 = 10855) (by norm_num)
theorem B2623861 : Blo 574812 2623861 := bbase (se 5 (by rfl) ⟨122993, by rfl⟩ : syracuseStep 2623861 = 245987) (by norm_num)
theorem B2919077 : Blo 574812 2919077 := bbase (se 4 (by rfl) ⟨273663, by rfl⟩ : syracuseStep 2919077 = 547327) (by norm_num)
theorem B789277 : Blo 574812 789277 := bbase (se 3 (by rfl) ⟨147989, by rfl⟩ : syracuseStep 789277 = 295979) (by norm_num)
theorem B2460581 : Blo 574812 2460581 := bbase (se 4 (by rfl) ⟨230679, by rfl⟩ : syracuseStep 2460581 = 461359) (by norm_num)
theorem B592861 : Blo 574812 592861 := bbase (se 3 (by rfl) ⟨111161, by rfl⟩ : syracuseStep 592861 = 222323) (by norm_num)
theorem B691193 : Blo 574812 691193 := bbase (se 2 (by rfl) ⟨259197, by rfl⟩ : syracuseStep 691193 = 518395) (by norm_num)
theorem B691453 : Blo 574812 691453 := bbase (se 3 (by rfl) ⟨129647, by rfl⟩ : syracuseStep 691453 = 259295) (by norm_num)
theorem B1641845 : Blo 574812 1641845 := bbase (se 5 (by rfl) ⟨76961, by rfl⟩ : syracuseStep 1641845 = 153923) (by norm_num)
theorem B691645 : Blo 574812 691645 := bbase (se 3 (by rfl) ⟨129683, by rfl⟩ : syracuseStep 691645 = 259367) (by norm_num)
theorem B691669 : Blo 574812 691669 := bbase (se 7 (by rfl) ⟨8105, by rfl⟩ : syracuseStep 691669 = 16211) (by norm_num)
theorem B691673 : Blo 574812 691673 := bbase (se 2 (by rfl) ⟨259377, by rfl⟩ : syracuseStep 691673 = 518755) (by norm_num)
theorem B4918805 : Blo 574812 4918805 := bbase (se 6 (by rfl) ⟨115284, by rfl⟩ : syracuseStep 4918805 = 230569) (by norm_num)
theorem B2428453 : Blo 574812 2428453 := bbase (se 4 (by rfl) ⟨227667, by rfl⟩ : syracuseStep 2428453 = 455335) (by norm_num)
theorem B921149 : Blo 574812 921149 := bbase (se 3 (by rfl) ⟨172715, by rfl⟩ : syracuseStep 921149 = 345431) (by norm_num)
theorem B626257 : Blo 574812 626257 := bbase (se 2 (by rfl) ⟨234846, by rfl⟩ : syracuseStep 626257 = 469693) (by norm_num)
theorem B822973 : Blo 574812 822973 := bbase (se 3 (by rfl) ⟨154307, by rfl⟩ : syracuseStep 822973 = 308615) (by norm_num)
theorem B3280661 : Blo 574812 3280661 := bbase (se 6 (by rfl) ⟨76890, by rfl⟩ : syracuseStep 3280661 = 153781) (by norm_num)
theorem B2920373 : Blo 574812 2920373 := bbase (se 5 (by rfl) ⟨136892, by rfl⟩ : syracuseStep 2920373 = 273785) (by norm_num)
theorem B692173 : Blo 574812 692173 := bbase (se 3 (by rfl) ⟨129782, by rfl⟩ : syracuseStep 692173 = 259565) (by norm_num)
theorem B692269 : Blo 574812 692269 := bbase (se 3 (by rfl) ⟨129800, by rfl⟩ : syracuseStep 692269 = 259601) (by norm_num)
theorem B823565 : Blo 574812 823565 := bbase (se 3 (by rfl) ⟨154418, by rfl⟩ : syracuseStep 823565 = 308837) (by norm_num)
theorem B823645 : Blo 574812 823645 := bbase (se 3 (by rfl) ⟨154433, by rfl⟩ : syracuseStep 823645 = 308867) (by norm_num)
theorem B823765 : Blo 574812 823765 := bbase (se 7 (by rfl) ⟨9653, by rfl⟩ : syracuseStep 823765 = 19307) (by norm_num)
theorem B823861 : Blo 574812 823861 := bbase (se 5 (by rfl) ⟨38618, by rfl⟩ : syracuseStep 823861 = 77237) (by norm_num)
theorem B1643429 : Blo 574812 1643429 := bbase (se 4 (by rfl) ⟨154071, by rfl⟩ : syracuseStep 1643429 = 308143) (by norm_num)
theorem B922565 : Blo 574812 922565 := bbase (se 4 (by rfl) ⟨86490, by rfl⟩ : syracuseStep 922565 = 172981) (by norm_num)
theorem B2888677 : Blo 574812 2888677 := bbase (se 4 (by rfl) ⟨270813, by rfl⟩ : syracuseStep 2888677 = 541627) (by norm_num)
theorem B4166645 : Blo 574812 4166645 := bbase (se 5 (by rfl) ⟨195311, by rfl⟩ : syracuseStep 4166645 = 390623) (by norm_num)
theorem B693245 : Blo 574812 693245 := bbase (se 3 (by rfl) ⟨129983, by rfl⟩ : syracuseStep 693245 = 259967) (by norm_num)
theorem B1381445 : Blo 574812 1381445 := bbase (se 4 (by rfl) ⟨129510, by rfl⟩ : syracuseStep 1381445 = 259021) (by norm_num)
theorem B922789 : Blo 574812 922789 := bbase (se 4 (by rfl) ⟨86511, by rfl⟩ : syracuseStep 922789 = 173023) (by norm_num)
theorem B2921669 : Blo 574812 2921669 := bbase (se 4 (by rfl) ⟨273906, by rfl⟩ : syracuseStep 2921669 = 547813) (by norm_num)
theorem B1480133 : Blo 574812 1480133 := bbase (se 4 (by rfl) ⟨138762, by rfl⟩ : syracuseStep 1480133 = 277525) (by norm_num)
theorem B693721 : Blo 574812 693721 := bbase (se 2 (by rfl) ⟨260145, by rfl⟩ : syracuseStep 693721 = 520291) (by norm_num)
theorem B1381877 : Blo 574812 1381877 := bbase (se 5 (by rfl) ⟨64775, by rfl⟩ : syracuseStep 1381877 = 129551) (by norm_num)
theorem B693749 : Blo 574812 693749 := bbase (se 5 (by rfl) ⟨32519, by rfl⟩ : syracuseStep 693749 = 65039) (by norm_num)
theorem B1644101 : Blo 574812 1644101 := bbase (se 4 (by rfl) ⟨154134, by rfl⟩ : syracuseStep 1644101 = 308269) (by norm_num)
theorem B693937 : Blo 574812 693937 := bbase (se 2 (by rfl) ⟨260226, by rfl⟩ : syracuseStep 693937 = 520453) (by norm_num)
theorem B694057 : Blo 574812 694057 := bbase (se 2 (by rfl) ⟨260271, by rfl⟩ : syracuseStep 694057 = 520543) (by norm_num)
theorem B1316677 : Blo 574812 1316677 := bbase (se 4 (by rfl) ⟨123438, by rfl⟩ : syracuseStep 1316677 = 246877) (by norm_num)
theorem B3282869 : Blo 574812 3282869 := bbase (se 5 (by rfl) ⟨153884, by rfl⟩ : syracuseStep 3282869 = 307769) (by norm_num)
theorem B1054661 : Blo 574812 1054661 := bbase (se 4 (by rfl) ⟨98874, by rfl⟩ : syracuseStep 1054661 = 197749) (by norm_num)
theorem B1644533 : Blo 574812 1644533 := bbase (se 5 (by rfl) ⟨77087, by rfl⟩ : syracuseStep 1644533 = 154175) (by norm_num)
theorem B1382501 : Blo 574812 1382501 := bbase (se 4 (by rfl) ⟨129609, by rfl⟩ : syracuseStep 1382501 = 259219) (by norm_num)
theorem B1480933 : Blo 574812 1480933 := bbase (se 4 (by rfl) ⟨138837, by rfl⟩ : syracuseStep 1480933 = 277675) (by norm_num)
theorem B2922965 : Blo 574812 2922965 := bbase (se 7 (by rfl) ⟨34253, by rfl⟩ : syracuseStep 2922965 = 68507) (by norm_num)
theorem B727537 : Blo 574812 727537 := bbase (se 2 (by rfl) ⟨272826, by rfl⟩ : syracuseStep 727537 = 545653) (by norm_num)
theorem B924205 : Blo 574812 924205 := bbase (se 3 (by rfl) ⟨173288, by rfl⟩ : syracuseStep 924205 = 346577) (by norm_num)
theorem B727633 : Blo 574812 727633 := bbase (se 2 (by rfl) ⟨272862, by rfl⟩ : syracuseStep 727633 = 545725) (by norm_num)
theorem B1940165 : Blo 574812 1940165 := bbase (se 4 (by rfl) ⟨181890, by rfl⟩ : syracuseStep 1940165 = 363781) (by norm_num)
theorem B1645285 : Blo 574812 1645285 := bbase (se 4 (by rfl) ⟨154245, by rfl⟩ : syracuseStep 1645285 = 308491) (by norm_num)
theorem B727805 : Blo 574812 727805 := bbase (se 3 (by rfl) ⟨136463, by rfl⟩ : syracuseStep 727805 = 272927) (by norm_num)
theorem B924461 : Blo 574812 924461 := bbase (se 3 (by rfl) ⟨173336, by rfl⟩ : syracuseStep 924461 = 346673) (by norm_num)
theorem B727861 : Blo 574812 727861 := bbase (se 5 (by rfl) ⟨34118, by rfl⟩ : syracuseStep 727861 = 68237) (by norm_num)
theorem B2464613 : Blo 574812 2464613 := bbase (se 4 (by rfl) ⟨231057, by rfl⟩ : syracuseStep 2464613 = 462115) (by norm_num)
theorem B727957 : Blo 574812 727957 := bbase (se 6 (by rfl) ⟨17061, by rfl⟩ : syracuseStep 727957 = 34123) (by norm_num)
theorem B1874917 : Blo 574812 1874917 := bbase (se 4 (by rfl) ⟨175773, by rfl⟩ : syracuseStep 1874917 = 351547) (by norm_num)
theorem B924653 : Blo 574812 924653 := bbase (se 3 (by rfl) ⟨173372, by rfl⟩ : syracuseStep 924653 = 346745) (by norm_num)
theorem B728129 : Blo 574812 728129 := bbase (se 2 (by rfl) ⟨273048, by rfl⟩ : syracuseStep 728129 = 546097) (by norm_num)
theorem B1940597 : Blo 574812 1940597 := bbase (se 5 (by rfl) ⟨90965, by rfl⟩ : syracuseStep 1940597 = 181931) (by norm_num)
theorem B728185 : Blo 574812 728185 := bbase (se 2 (by rfl) ⟨273069, by rfl⟩ : syracuseStep 728185 = 546139) (by norm_num)
theorem B728281 : Blo 574812 728281 := bbase (se 2 (by rfl) ⟨273105, by rfl⟩ : syracuseStep 728281 = 546211) (by norm_num)
theorem B728453 : Blo 574812 728453 := bbase (se 4 (by rfl) ⟨68292, by rfl⟩ : syracuseStep 728453 = 136585) (by norm_num)
theorem B1318301 : Blo 574812 1318301 := bbase (se 3 (by rfl) ⟨247181, by rfl⟩ : syracuseStep 1318301 = 494363) (by norm_num)
theorem B728509 : Blo 574812 728509 := bbase (se 3 (by rfl) ⟨136595, by rfl⟩ : syracuseStep 728509 = 273191) (by norm_num)
theorem B728605 : Blo 574812 728605 := bbase (se 3 (by rfl) ⟨136613, by rfl⟩ : syracuseStep 728605 = 273227) (by norm_num)
theorem B1941029 : Blo 574812 1941029 := bbase (se 4 (by rfl) ⟨181971, by rfl⟩ : syracuseStep 1941029 = 363943) (by norm_num)
theorem B1318565 : Blo 574812 1318565 := bbase (se 4 (by rfl) ⟨123615, by rfl⟩ : syracuseStep 1318565 = 247231) (by norm_num)
theorem B728777 : Blo 574812 728777 := bbase (se 2 (by rfl) ⟨273291, by rfl⟩ : syracuseStep 728777 = 546583) (by norm_num)
theorem B5545685 : Blo 574812 5545685 := bbase (se 7 (by rfl) ⟨64988, by rfl⟩ : syracuseStep 5545685 = 129977) (by norm_num)
theorem B2924261 : Blo 574812 2924261 := bbase (se 4 (by rfl) ⟨274149, by rfl⟩ : syracuseStep 2924261 = 548299) (by norm_num)
theorem B728833 : Blo 574812 728833 := bbase (se 2 (by rfl) ⟨273312, by rfl⟩ : syracuseStep 728833 = 546625) (by norm_num)
theorem B728929 : Blo 574812 728929 := bbase (se 2 (by rfl) ⟨273348, by rfl⟩ : syracuseStep 728929 = 546697) (by norm_num)
theorem B925589 : Blo 574812 925589 := bbase (se 6 (by rfl) ⟨21693, by rfl⟩ : syracuseStep 925589 = 43387) (by norm_num)
theorem B1941461 : Blo 574812 1941461 := bbase (se 7 (by rfl) ⟨22751, by rfl⟩ : syracuseStep 1941461 = 45503) (by norm_num)
theorem B2957269 : Blo 574812 2957269 := bbase (se 7 (by rfl) ⟨34655, by rfl⟩ : syracuseStep 2957269 = 69311) (by norm_num)
theorem B729101 : Blo 574812 729101 := bbase (se 3 (by rfl) ⟨136706, by rfl⟩ : syracuseStep 729101 = 273413) (by norm_num)
theorem B729157 : Blo 574812 729157 := bbase (se 4 (by rfl) ⟨68358, by rfl⟩ : syracuseStep 729157 = 136717) (by norm_num)
theorem B729253 : Blo 574812 729253 := bbase (se 4 (by rfl) ⟨68367, by rfl⟩ : syracuseStep 729253 = 136735) (by norm_num)
theorem B925973 : Blo 574812 925973 := bbase (se 6 (by rfl) ⟨21702, by rfl⟩ : syracuseStep 925973 = 43405) (by norm_num)
theorem B729425 : Blo 574812 729425 := bbase (se 2 (by rfl) ⟨273534, by rfl⟩ : syracuseStep 729425 = 547069) (by norm_num)
theorem B4366709 : Blo 574812 4366709 := bbase (se 5 (by rfl) ⟨204689, by rfl⟩ : syracuseStep 4366709 = 409379) (by norm_num)
theorem B1941893 : Blo 574812 1941893 := bbase (se 4 (by rfl) ⟨182052, by rfl⟩ : syracuseStep 1941893 = 364105) (by norm_num)
theorem B729481 : Blo 574812 729481 := bbase (se 2 (by rfl) ⟨273555, by rfl⟩ : syracuseStep 729481 = 547111) (by norm_num)
theorem B631181 : Blo 574812 631181 := bbase (se 3 (by rfl) ⟨118346, by rfl⟩ : syracuseStep 631181 = 236693) (by norm_num)
theorem B926101 : Blo 574812 926101 := bbase (se 6 (by rfl) ⟨21705, by rfl⟩ : syracuseStep 926101 = 43411) (by norm_num)
theorem B729577 : Blo 574812 729577 := bbase (se 2 (by rfl) ⟨273591, by rfl⟩ : syracuseStep 729577 = 547183) (by norm_num)
theorem B1122797 : Blo 574812 1122797 := bbase (se 3 (by rfl) ⟨210524, by rfl⟩ : syracuseStep 1122797 = 421049) (by norm_num)
theorem B2466389 : Blo 574812 2466389 := bbase (se 8 (by rfl) ⟨14451, by rfl⟩ : syracuseStep 2466389 = 28903) (by norm_num)
theorem B729749 : Blo 574812 729749 := bbase (se 6 (by rfl) ⟨17103, by rfl⟩ : syracuseStep 729749 = 34207) (by norm_num)
theorem B5415605 : Blo 574812 5415605 := bbase (se 5 (by rfl) ⟨253856, by rfl⟩ : syracuseStep 5415605 = 507713) (by norm_num)
theorem B729805 : Blo 574812 729805 := bbase (se 3 (by rfl) ⟨136838, by rfl⟩ : syracuseStep 729805 = 273677) (by norm_num)
theorem B16622293 : Blo 574812 16622293 := bbase (se 7 (by rfl) ⟨194792, by rfl⟩ : syracuseStep 16622293 = 389585) (by norm_num)
theorem B729901 : Blo 574812 729901 := bbase (se 3 (by rfl) ⟨136856, by rfl⟩ : syracuseStep 729901 = 273713) (by norm_num)
theorem B1942325 : Blo 574812 1942325 := bbase (se 5 (by rfl) ⟨91046, by rfl⟩ : syracuseStep 1942325 = 182093) (by norm_num)
theorem B2073509 : Blo 574812 2073509 := bbase (se 4 (by rfl) ⟨194391, by rfl⟩ : syracuseStep 2073509 = 388783) (by norm_num)
theorem B730073 : Blo 574812 730073 := bbase (se 2 (by rfl) ⟨273777, by rfl⟩ : syracuseStep 730073 = 547555) (by norm_num)
theorem B1385461 : Blo 574812 1385461 := bbase (se 5 (by rfl) ⟨64943, by rfl⟩ : syracuseStep 1385461 = 129887) (by norm_num)
theorem B2925557 : Blo 574812 2925557 := bbase (se 5 (by rfl) ⟨137135, by rfl⟩ : syracuseStep 2925557 = 274271) (by norm_num)
theorem B730129 : Blo 574812 730129 := bbase (se 2 (by rfl) ⟨273798, by rfl⟩ : syracuseStep 730129 = 547597) (by norm_num)
theorem B1844309 : Blo 574812 1844309 := bbase (se 8 (by rfl) ⟨10806, by rfl⟩ : syracuseStep 1844309 = 21613) (by norm_num)
theorem B730225 : Blo 574812 730225 := bbase (se 2 (by rfl) ⟨273834, by rfl⟩ : syracuseStep 730225 = 547669) (by norm_num)
theorem B1385653 : Blo 574812 1385653 := bbase (se 5 (by rfl) ⟨64952, by rfl⟩ : syracuseStep 1385653 = 129905) (by norm_num)
theorem B1385693 : Blo 574812 1385693 := bbase (se 3 (by rfl) ⟨259817, by rfl⟩ : syracuseStep 1385693 = 519635) (by norm_num)
theorem B1942757 : Blo 574812 1942757 := bbase (se 4 (by rfl) ⟨182133, by rfl⟩ : syracuseStep 1942757 = 364267) (by norm_num)
theorem B730397 : Blo 574812 730397 := bbase (se 3 (by rfl) ⟨136949, by rfl⟩ : syracuseStep 730397 = 273899) (by norm_num)
theorem B730453 : Blo 574812 730453 := bbase (se 12 (by rfl) ⟨267, by rfl⟩ : syracuseStep 730453 = 535) (by norm_num)
theorem B927101 : Blo 574812 927101 := bbase (se 3 (by rfl) ⟨173831, by rfl⟩ : syracuseStep 927101 = 347663) (by norm_num)
theorem B730549 : Blo 574812 730549 := bbase (se 5 (by rfl) ⟨34244, by rfl⟩ : syracuseStep 730549 = 68489) (by norm_num)
theorem B1385981 : Blo 574812 1385981 := bbase (se 3 (by rfl) ⟨259871, by rfl⟩ : syracuseStep 1385981 = 519743) (by norm_num)
theorem B1648133 : Blo 574812 1648133 := bbase (se 4 (by rfl) ⟨154512, by rfl⟩ : syracuseStep 1648133 = 309025) (by norm_num)
theorem B2467381 : Blo 574812 2467381 := bbase (se 5 (by rfl) ⟨115658, by rfl⟩ : syracuseStep 2467381 = 231317) (by norm_num)
theorem B730721 : Blo 574812 730721 := bbase (se 2 (by rfl) ⟨274020, by rfl⟩ : syracuseStep 730721 = 548041) (by norm_num)
theorem B1943189 : Blo 574812 1943189 := bbase (se 6 (by rfl) ⟨45543, by rfl⟩ : syracuseStep 1943189 = 91087) (by norm_num)
theorem B730777 : Blo 574812 730777 := bbase (se 2 (by rfl) ⟨274041, by rfl⟩ : syracuseStep 730777 = 548083) (by norm_num)
theorem B730873 : Blo 574812 730873 := bbase (se 2 (by rfl) ⟨274077, by rfl⟩ : syracuseStep 730873 = 548155) (by norm_num)
theorem B1091389 : Blo 574812 1091389 := bbase (se 3 (by rfl) ⟨204635, by rfl⟩ : syracuseStep 1091389 = 409271) (by norm_num)
theorem B2074501 : Blo 574812 2074501 := bbase (se 4 (by rfl) ⟨194484, by rfl⟩ : syracuseStep 2074501 = 388969) (by norm_num)
theorem B731045 : Blo 574812 731045 := bbase (se 4 (by rfl) ⟨68535, by rfl⟩ : syracuseStep 731045 = 137071) (by norm_num)
theorem B1091549 : Blo 574812 1091549 := bbase (se 3 (by rfl) ⟨204665, by rfl⟩ : syracuseStep 1091549 = 409331) (by norm_num)
theorem B731101 : Blo 574812 731101 := bbase (se 3 (by rfl) ⟨137081, by rfl⟩ : syracuseStep 731101 = 274163) (by norm_num)
theorem B862229 : Blo 574812 862229 := bbase (se 6 (by rfl) ⟨20208, by rfl⟩ : syracuseStep 862229 = 40417) (by norm_num)
theorem B862253 : Blo 574812 862253 := bbase (se 3 (by rfl) ⟨161672, by rfl⟩ : syracuseStep 862253 = 323345) (by norm_num)
theorem B731197 : Blo 574812 731197 := bbase (se 3 (by rfl) ⟨137099, by rfl⟩ : syracuseStep 731197 = 274199) (by norm_num)
theorem B862277 : Blo 574812 862277 := bbase (se 4 (by rfl) ⟨80838, by rfl⟩ : syracuseStep 862277 = 161677) (by norm_num)
theorem B1943621 : Blo 574812 1943621 := bbase (se 4 (by rfl) ⟨182214, by rfl⟩ : syracuseStep 1943621 = 364429) (by norm_num)
theorem B862301 : Blo 574812 862301 := bbase (se 3 (by rfl) ⟨161681, by rfl⟩ : syracuseStep 862301 = 323363) (by norm_num)
theorem B1091693 : Blo 574812 1091693 := bbase (se 3 (by rfl) ⟨204692, by rfl⟩ : syracuseStep 1091693 = 409385) (by norm_num)
theorem B862325 : Blo 574812 862325 := bbase (se 5 (by rfl) ⟨40421, by rfl⟩ : syracuseStep 862325 = 80843) (by norm_num)
theorem B862349 : Blo 574812 862349 := bbase (se 3 (by rfl) ⟨161690, by rfl⟩ : syracuseStep 862349 = 323381) (by norm_num)
theorem B862373 : Blo 574812 862373 := bbase (se 4 (by rfl) ⟨80847, by rfl⟩ : syracuseStep 862373 = 161695) (by norm_num)
theorem B862397 : Blo 574812 862397 := bbase (se 3 (by rfl) ⟨161699, by rfl⟩ : syracuseStep 862397 = 323399) (by norm_num)
theorem B862421 : Blo 574812 862421 := bbase (se 7 (by rfl) ⟨10106, by rfl⟩ : syracuseStep 862421 = 20213) (by norm_num)
theorem B731369 : Blo 574812 731369 := bbase (se 2 (by rfl) ⟨274263, by rfl⟩ : syracuseStep 731369 = 548527) (by norm_num)
theorem B862445 : Blo 574812 862445 := bbase (se 3 (by rfl) ⟨161708, by rfl⟩ : syracuseStep 862445 = 323417) (by norm_num)
theorem B862469 : Blo 574812 862469 := bbase (se 4 (by rfl) ⟨80856, by rfl⟩ : syracuseStep 862469 = 161713) (by norm_num)
theorem B2926853 : Blo 574812 2926853 := bbase (se 4 (by rfl) ⟨274392, by rfl⟩ : syracuseStep 2926853 = 548785) (by norm_num)
theorem B862493 : Blo 574812 862493 := bbase (se 3 (by rfl) ⟨161717, by rfl⟩ : syracuseStep 862493 = 323435) (by norm_num)
theorem B731425 : Blo 574812 731425 := bbase (se 2 (by rfl) ⟨274284, by rfl⟩ : syracuseStep 731425 = 548569) (by norm_num)
theorem B862517 : Blo 574812 862517 := bbase (se 5 (by rfl) ⟨40430, by rfl⟩ : syracuseStep 862517 = 80861) (by norm_num)
theorem B862541 : Blo 574812 862541 := bbase (se 3 (by rfl) ⟨161726, by rfl⟩ : syracuseStep 862541 = 323453) (by norm_num)
theorem B862565 : Blo 574812 862565 := bbase (se 4 (by rfl) ⟨80865, by rfl⟩ : syracuseStep 862565 = 161731) (by norm_num)
theorem B862589 : Blo 574812 862589 := bbase (se 3 (by rfl) ⟨161735, by rfl⟩ : syracuseStep 862589 = 323471) (by norm_num)
theorem B731521 : Blo 574812 731521 := bbase (se 2 (by rfl) ⟨274320, by rfl⟩ : syracuseStep 731521 = 548641) (by norm_num)
theorem B1091981 : Blo 574812 1091981 := bbase (se 3 (by rfl) ⟨204746, by rfl⟩ : syracuseStep 1091981 = 409493) (by norm_num)
theorem B862613 : Blo 574812 862613 := bbase (se 6 (by rfl) ⟨20217, by rfl⟩ : syracuseStep 862613 = 40435) (by norm_num)
theorem B862637 : Blo 574812 862637 := bbase (se 3 (by rfl) ⟨161744, by rfl⟩ : syracuseStep 862637 = 323489) (by norm_num)
theorem B862661 : Blo 574812 862661 := bbase (se 4 (by rfl) ⟨80874, by rfl⟩ : syracuseStep 862661 = 161749) (by norm_num)
theorem B862685 : Blo 574812 862685 := bbase (se 3 (by rfl) ⟨161753, by rfl⟩ : syracuseStep 862685 = 323507) (by norm_num)
theorem B862709 : Blo 574812 862709 := bbase (se 5 (by rfl) ⟨40439, by rfl⟩ : syracuseStep 862709 = 80879) (by norm_num)
theorem B1944053 : Blo 574812 1944053 := bbase (se 5 (by rfl) ⟨91127, by rfl⟩ : syracuseStep 1944053 = 182255) (by norm_num)
theorem B862733 : Blo 574812 862733 := bbase (se 3 (by rfl) ⟨161762, by rfl⟩ : syracuseStep 862733 = 323525) (by norm_num)
theorem B862757 : Blo 574812 862757 := bbase (se 4 (by rfl) ⟨80883, by rfl⟩ : syracuseStep 862757 = 161767) (by norm_num)
theorem B1092133 : Blo 574812 1092133 := bbase (se 4 (by rfl) ⟨102387, by rfl⟩ : syracuseStep 1092133 = 204775) (by norm_num)
theorem B1878565 : Blo 574812 1878565 := bbase (se 4 (by rfl) ⟨176115, by rfl⟩ : syracuseStep 1878565 = 352231) (by norm_num)
theorem B731693 : Blo 574812 731693 := bbase (se 3 (by rfl) ⟨137192, by rfl⟩ : syracuseStep 731693 = 274385) (by norm_num)
theorem B862781 : Blo 574812 862781 := bbase (se 3 (by rfl) ⟨161771, by rfl⟩ : syracuseStep 862781 = 323543) (by norm_num)
theorem B862805 : Blo 574812 862805 := bbase (se 8 (by rfl) ⟨5055, by rfl⟩ : syracuseStep 862805 = 10111) (by norm_num)
theorem B731749 : Blo 574812 731749 := bbase (se 4 (by rfl) ⟨68601, by rfl⟩ : syracuseStep 731749 = 137203) (by norm_num)
theorem B862829 : Blo 574812 862829 := bbase (se 3 (by rfl) ⟨161780, by rfl⟩ : syracuseStep 862829 = 323561) (by norm_num)
theorem B862853 : Blo 574812 862853 := bbase (se 4 (by rfl) ⟨80892, by rfl⟩ : syracuseStep 862853 = 161785) (by norm_num)
theorem B862877 : Blo 574812 862877 := bbase (se 3 (by rfl) ⟨161789, by rfl⟩ : syracuseStep 862877 = 323579) (by norm_num)
theorem B862901 : Blo 574812 862901 := bbase (se 5 (by rfl) ⟨40448, by rfl⟩ : syracuseStep 862901 = 80897) (by norm_num)
theorem B731845 : Blo 574812 731845 := bbase (se 4 (by rfl) ⟨68610, by rfl⟩ : syracuseStep 731845 = 137221) (by norm_num)
theorem B862925 : Blo 574812 862925 := bbase (se 3 (by rfl) ⟨161798, by rfl⟩ : syracuseStep 862925 = 323597) (by norm_num)
theorem B862949 : Blo 574812 862949 := bbase (se 4 (by rfl) ⟨80901, by rfl⟩ : syracuseStep 862949 = 161803) (by norm_num)
theorem B862973 : Blo 574812 862973 := bbase (se 3 (by rfl) ⟨161807, by rfl⟩ : syracuseStep 862973 = 323615) (by norm_num)
theorem B862997 : Blo 574812 862997 := bbase (se 6 (by rfl) ⟨20226, by rfl⟩ : syracuseStep 862997 = 40453) (by norm_num)
theorem B863021 : Blo 574812 863021 := bbase (se 3 (by rfl) ⟨161816, by rfl⟩ : syracuseStep 863021 = 323633) (by norm_num)
theorem B863045 : Blo 574812 863045 := bbase (se 4 (by rfl) ⟨80910, by rfl⟩ : syracuseStep 863045 = 161821) (by norm_num)
theorem B1092437 : Blo 574812 1092437 := bbase (se 9 (by rfl) ⟨3200, by rfl⟩ : syracuseStep 1092437 = 6401) (by norm_num)
theorem B863069 : Blo 574812 863069 := bbase (se 3 (by rfl) ⟨161825, by rfl⟩ : syracuseStep 863069 = 323651) (by norm_num)
theorem B732017 : Blo 574812 732017 := bbase (se 2 (by rfl) ⟨274506, by rfl⟩ : syracuseStep 732017 = 549013) (by norm_num)
theorem B863093 : Blo 574812 863093 := bbase (se 5 (by rfl) ⟨40457, by rfl⟩ : syracuseStep 863093 = 80915) (by norm_num)
theorem B863117 : Blo 574812 863117 := bbase (se 3 (by rfl) ⟨161834, by rfl⟩ : syracuseStep 863117 = 323669) (by norm_num)
theorem B863141 : Blo 574812 863141 := bbase (se 4 (by rfl) ⟨80919, by rfl⟩ : syracuseStep 863141 = 161839) (by norm_num)
theorem B1944485 : Blo 574812 1944485 := bbase (se 4 (by rfl) ⟨182295, by rfl⟩ : syracuseStep 1944485 = 364591) (by norm_num)
theorem B732073 : Blo 574812 732073 := bbase (se 2 (by rfl) ⟨274527, by rfl⟩ : syracuseStep 732073 = 549055) (by norm_num)
theorem B863165 : Blo 574812 863165 := bbase (se 3 (by rfl) ⟨161843, by rfl⟩ : syracuseStep 863165 = 323687) (by norm_num)
theorem B863189 : Blo 574812 863189 := bbase (se 7 (by rfl) ⟨10115, by rfl⟩ : syracuseStep 863189 = 20231) (by norm_num)
theorem B863213 : Blo 574812 863213 := bbase (se 3 (by rfl) ⟨161852, by rfl⟩ : syracuseStep 863213 = 323705) (by norm_num)
theorem B863237 : Blo 574812 863237 := bbase (se 4 (by rfl) ⟨80928, by rfl⟩ : syracuseStep 863237 = 161857) (by norm_num)
theorem B732169 : Blo 574812 732169 := bbase (se 2 (by rfl) ⟨274563, by rfl⟩ : syracuseStep 732169 = 549127) (by norm_num)
theorem B863261 : Blo 574812 863261 := bbase (se 3 (by rfl) ⟨161861, by rfl⟩ : syracuseStep 863261 = 323723) (by norm_num)
theorem B863285 : Blo 574812 863285 := bbase (se 5 (by rfl) ⟨40466, by rfl⟩ : syracuseStep 863285 = 80933) (by norm_num)
theorem B863309 : Blo 574812 863309 := bbase (se 3 (by rfl) ⟨161870, by rfl⟩ : syracuseStep 863309 = 323741) (by norm_num)
theorem B863333 : Blo 574812 863333 := bbase (se 4 (by rfl) ⟨80937, by rfl⟩ : syracuseStep 863333 = 161875) (by norm_num)
theorem B863357 : Blo 574812 863357 := bbase (se 3 (by rfl) ⟨161879, by rfl⟩ : syracuseStep 863357 = 323759) (by norm_num)
theorem B863381 : Blo 574812 863381 := bbase (se 6 (by rfl) ⟨20235, by rfl⟩ : syracuseStep 863381 = 40471) (by norm_num)
theorem B863405 : Blo 574812 863405 := bbase (se 3 (by rfl) ⟨161888, by rfl⟩ : syracuseStep 863405 = 323777) (by norm_num)
theorem B732341 : Blo 574812 732341 := bbase (se 5 (by rfl) ⟨34328, by rfl⟩ : syracuseStep 732341 = 68657) (by norm_num)
theorem B863429 : Blo 574812 863429 := bbase (se 4 (by rfl) ⟨80946, by rfl⟩ : syracuseStep 863429 = 161893) (by norm_num)
theorem B863453 : Blo 574812 863453 := bbase (se 3 (by rfl) ⟨161897, by rfl⟩ : syracuseStep 863453 = 323795) (by norm_num)
theorem B732397 : Blo 574812 732397 := bbase (se 3 (by rfl) ⟨137324, by rfl⟩ : syracuseStep 732397 = 274649) (by norm_num)
theorem B863477 : Blo 574812 863477 := bbase (se 5 (by rfl) ⟨40475, by rfl⟩ : syracuseStep 863477 = 80951) (by norm_num)
theorem B863501 : Blo 574812 863501 := bbase (se 3 (by rfl) ⟨161906, by rfl⟩ : syracuseStep 863501 = 323813) (by norm_num)
theorem B863525 : Blo 574812 863525 := bbase (se 4 (by rfl) ⟨80955, by rfl⟩ : syracuseStep 863525 = 161911) (by norm_num)
theorem B863549 : Blo 574812 863549 := bbase (se 3 (by rfl) ⟨161915, by rfl⟩ : syracuseStep 863549 = 323831) (by norm_num)
theorem B732493 : Blo 574812 732493 := bbase (se 3 (by rfl) ⟨137342, by rfl⟩ : syracuseStep 732493 = 274685) (by norm_num)
theorem B863573 : Blo 574812 863573 := bbase (se 11 (by rfl) ⟨632, by rfl⟩ : syracuseStep 863573 = 1265) (by norm_num)
theorem B7384405 : Blo 574812 7384405 := bbase (se 11 (by rfl) ⟨5408, by rfl⟩ : syracuseStep 7384405 = 10817) (by norm_num)
theorem B1944917 : Blo 574812 1944917 := bbase (se 11 (by rfl) ⟨1424, by rfl⟩ : syracuseStep 1944917 = 2849) (by norm_num)
theorem B863597 : Blo 574812 863597 := bbase (se 3 (by rfl) ⟨161924, by rfl⟩ : syracuseStep 863597 = 323849) (by norm_num)
theorem B863621 : Blo 574812 863621 := bbase (se 4 (by rfl) ⟨80964, by rfl⟩ : syracuseStep 863621 = 161929) (by norm_num)
theorem B863645 : Blo 574812 863645 := bbase (se 3 (by rfl) ⟨161933, by rfl⟩ : syracuseStep 863645 = 323867) (by norm_num)
theorem B863669 : Blo 574812 863669 := bbase (se 5 (by rfl) ⟨40484, by rfl⟩ : syracuseStep 863669 = 80969) (by norm_num)
theorem B863693 : Blo 574812 863693 := bbase (se 3 (by rfl) ⟨161942, by rfl⟩ : syracuseStep 863693 = 323885) (by norm_num)
theorem B863717 : Blo 574812 863717 := bbase (se 4 (by rfl) ⟨80973, by rfl⟩ : syracuseStep 863717 = 161947) (by norm_num)
theorem B863741 : Blo 574812 863741 := bbase (se 3 (by rfl) ⟨161951, by rfl⟩ : syracuseStep 863741 = 323903) (by norm_num)
theorem B863765 : Blo 574812 863765 := bbase (se 6 (by rfl) ⟨20244, by rfl⟩ : syracuseStep 863765 = 40489) (by norm_num)
theorem B2928149 : Blo 574812 2928149 := bbase (se 6 (by rfl) ⟨68628, by rfl⟩ : syracuseStep 2928149 = 137257) (by norm_num)
theorem B863789 : Blo 574812 863789 := bbase (se 3 (by rfl) ⟨161960, by rfl⟩ : syracuseStep 863789 = 323921) (by norm_num)
theorem B1093189 : Blo 574812 1093189 := bbase (se 4 (by rfl) ⟨102486, by rfl⟩ : syracuseStep 1093189 = 204973) (by norm_num)
theorem B863813 : Blo 574812 863813 := bbase (se 4 (by rfl) ⟨80982, by rfl⟩ : syracuseStep 863813 = 161965) (by norm_num)
theorem B863837 : Blo 574812 863837 := bbase (se 3 (by rfl) ⟨161969, by rfl⟩ : syracuseStep 863837 = 323939) (by norm_num)
theorem B863861 : Blo 574812 863861 := bbase (se 5 (by rfl) ⟨40493, by rfl⟩ : syracuseStep 863861 = 80987) (by norm_num)
theorem B863885 : Blo 574812 863885 := bbase (se 3 (by rfl) ⟨161978, by rfl⟩ : syracuseStep 863885 = 323957) (by norm_num)
theorem B863909 : Blo 574812 863909 := bbase (se 4 (by rfl) ⟨80991, by rfl⟩ : syracuseStep 863909 = 161983) (by norm_num)
theorem B863933 : Blo 574812 863933 := bbase (se 3 (by rfl) ⟨161987, by rfl⟩ : syracuseStep 863933 = 323975) (by norm_num)
theorem B1093333 : Blo 574812 1093333 := bbase (se 7 (by rfl) ⟨12812, by rfl⟩ : syracuseStep 1093333 = 25625) (by norm_num)
theorem B863957 : Blo 574812 863957 := bbase (se 7 (by rfl) ⟨10124, by rfl⟩ : syracuseStep 863957 = 20249) (by norm_num)
theorem B634601 : Blo 574812 634601 := bbase (se 2 (by rfl) ⟨237975, by rfl⟩ : syracuseStep 634601 = 475951) (by norm_num)
theorem B863981 : Blo 574812 863981 := bbase (se 3 (by rfl) ⟨161996, by rfl⟩ : syracuseStep 863981 = 323993) (by norm_num)
theorem B864005 : Blo 574812 864005 := bbase (se 4 (by rfl) ⟨81000, by rfl⟩ : syracuseStep 864005 = 162001) (by norm_num)
theorem B1945349 : Blo 574812 1945349 := bbase (se 4 (by rfl) ⟨182376, by rfl⟩ : syracuseStep 1945349 = 364753) (by norm_num)
theorem B864029 : Blo 574812 864029 := bbase (se 3 (by rfl) ⟨162005, by rfl⟩ : syracuseStep 864029 = 324011) (by norm_num)
theorem B864053 : Blo 574812 864053 := bbase (se 5 (by rfl) ⟨40502, by rfl⟩ : syracuseStep 864053 = 81005) (by norm_num)
theorem B864077 : Blo 574812 864077 := bbase (se 3 (by rfl) ⟨162014, by rfl⟩ : syracuseStep 864077 = 324029) (by norm_num)
theorem B864101 : Blo 574812 864101 := bbase (se 4 (by rfl) ⟨81009, by rfl⟩ : syracuseStep 864101 = 162019) (by norm_num)
theorem B1093493 : Blo 574812 1093493 := bbase (se 5 (by rfl) ⟨51257, by rfl⟩ : syracuseStep 1093493 = 102515) (by norm_num)
theorem B864125 : Blo 574812 864125 := bbase (se 3 (by rfl) ⟨162023, by rfl⟩ : syracuseStep 864125 = 324047) (by norm_num)
theorem B864149 : Blo 574812 864149 := bbase (se 6 (by rfl) ⟨20253, by rfl⟩ : syracuseStep 864149 = 40507) (by norm_num)
theorem B3125141 : Blo 574812 3125141 := bbase (se 6 (by rfl) ⟨73245, by rfl⟩ : syracuseStep 3125141 = 146491) (by norm_num)
theorem B864173 : Blo 574812 864173 := bbase (se 3 (by rfl) ⟨162032, by rfl⟩ : syracuseStep 864173 = 324065) (by norm_num)
theorem B864197 : Blo 574812 864197 := bbase (se 4 (by rfl) ⟨81018, by rfl⟩ : syracuseStep 864197 = 162037) (by norm_num)
theorem B864221 : Blo 574812 864221 := bbase (se 3 (by rfl) ⟨162041, by rfl⟩ : syracuseStep 864221 = 324083) (by norm_num)
theorem B864245 : Blo 574812 864245 := bbase (se 5 (by rfl) ⟨40511, by rfl⟩ : syracuseStep 864245 = 81023) (by norm_num)
theorem B1093637 : Blo 574812 1093637 := bbase (se 4 (by rfl) ⟨102528, by rfl⟩ : syracuseStep 1093637 = 205057) (by norm_num)
theorem B864269 : Blo 574812 864269 := bbase (se 3 (by rfl) ⟨162050, by rfl⟩ : syracuseStep 864269 = 324101) (by norm_num)
theorem B864293 : Blo 574812 864293 := bbase (se 4 (by rfl) ⟨81027, by rfl⟩ : syracuseStep 864293 = 162055) (by norm_num)
theorem B864317 : Blo 574812 864317 := bbase (se 3 (by rfl) ⟨162059, by rfl⟩ : syracuseStep 864317 = 324119) (by norm_num)
theorem B864341 : Blo 574812 864341 := bbase (se 8 (by rfl) ⟨5064, by rfl⟩ : syracuseStep 864341 = 10129) (by norm_num)
theorem B864365 : Blo 574812 864365 := bbase (se 3 (by rfl) ⟨162068, by rfl⟩ : syracuseStep 864365 = 324137) (by norm_num)
theorem B864389 : Blo 574812 864389 := bbase (se 4 (by rfl) ⟨81036, by rfl⟩ : syracuseStep 864389 = 162073) (by norm_num)
theorem B864413 : Blo 574812 864413 := bbase (se 3 (by rfl) ⟨162077, by rfl⟩ : syracuseStep 864413 = 324155) (by norm_num)
theorem B1847461 : Blo 574812 1847461 := bbase (se 4 (by rfl) ⟨173199, by rfl⟩ : syracuseStep 1847461 = 346399) (by norm_num)
theorem B2076853 : Blo 574812 2076853 := bbase (se 5 (by rfl) ⟨97352, by rfl⟩ : syracuseStep 2076853 = 194705) (by norm_num)
theorem B864437 : Blo 574812 864437 := bbase (se 5 (by rfl) ⟨40520, by rfl⟩ : syracuseStep 864437 = 81041) (by norm_num)
theorem B1945781 : Blo 574812 1945781 := bbase (se 5 (by rfl) ⟨91208, by rfl⟩ : syracuseStep 1945781 = 182417) (by norm_num)
theorem B864461 : Blo 574812 864461 := bbase (se 3 (by rfl) ⟨162086, by rfl⟩ : syracuseStep 864461 = 324173) (by norm_num)
theorem B864485 : Blo 574812 864485 := bbase (se 4 (by rfl) ⟨81045, by rfl⟩ : syracuseStep 864485 = 162091) (by norm_num)
theorem B864509 : Blo 574812 864509 := bbase (se 3 (by rfl) ⟨162095, by rfl⟩ : syracuseStep 864509 = 324191) (by norm_num)
theorem B700693 : Blo 574812 700693 := bbase (se 6 (by rfl) ⟨16422, by rfl⟩ : syracuseStep 700693 = 32845) (by norm_num)
theorem B864533 : Blo 574812 864533 := bbase (se 6 (by rfl) ⟨20262, by rfl⟩ : syracuseStep 864533 = 40525) (by norm_num)
theorem B1093925 : Blo 574812 1093925 := bbase (se 4 (by rfl) ⟨102555, by rfl⟩ : syracuseStep 1093925 = 205111) (by norm_num)
theorem B864557 : Blo 574812 864557 := bbase (se 3 (by rfl) ⟨162104, by rfl⟩ : syracuseStep 864557 = 324209) (by norm_num)
theorem B864581 : Blo 574812 864581 := bbase (se 4 (by rfl) ⟨81054, by rfl⟩ : syracuseStep 864581 = 162109) (by norm_num)
theorem B864605 : Blo 574812 864605 := bbase (se 3 (by rfl) ⟨162113, by rfl⟩ : syracuseStep 864605 = 324227) (by norm_num)
theorem B864629 : Blo 574812 864629 := bbase (se 5 (by rfl) ⟨40529, by rfl⟩ : syracuseStep 864629 = 81059) (by norm_num)
theorem B864653 : Blo 574812 864653 := bbase (se 3 (by rfl) ⟨162122, by rfl⟩ : syracuseStep 864653 = 324245) (by norm_num)
theorem B864677 : Blo 574812 864677 := bbase (se 4 (by rfl) ⟨81063, by rfl⟩ : syracuseStep 864677 = 162127) (by norm_num)
theorem B1094077 : Blo 574812 1094077 := bbase (se 3 (by rfl) ⟨205139, by rfl⟩ : syracuseStep 1094077 = 410279) (by norm_num)
theorem B864701 : Blo 574812 864701 := bbase (se 3 (by rfl) ⟨162131, by rfl⟩ : syracuseStep 864701 = 324263) (by norm_num)
theorem B864725 : Blo 574812 864725 := bbase (se 7 (by rfl) ⟨10133, by rfl⟩ : syracuseStep 864725 = 20267) (by norm_num)
theorem B864749 : Blo 574812 864749 := bbase (se 3 (by rfl) ⟨162140, by rfl⟩ : syracuseStep 864749 = 324281) (by norm_num)
theorem B864773 : Blo 574812 864773 := bbase (se 4 (by rfl) ⟨81072, by rfl⟩ : syracuseStep 864773 = 162145) (by norm_num)
theorem B864797 : Blo 574812 864797 := bbase (se 3 (by rfl) ⟨162149, by rfl⟩ : syracuseStep 864797 = 324299) (by norm_num)
theorem B864821 : Blo 574812 864821 := bbase (se 5 (by rfl) ⟨40538, by rfl⟩ : syracuseStep 864821 = 81077) (by norm_num)
theorem B864845 : Blo 574812 864845 := bbase (se 3 (by rfl) ⟨162158, by rfl⟩ : syracuseStep 864845 = 324317) (by norm_num)
theorem B864869 : Blo 574812 864869 := bbase (se 4 (by rfl) ⟨81081, by rfl⟩ : syracuseStep 864869 = 162163) (by norm_num)
theorem B1946213 : Blo 574812 1946213 := bbase (se 4 (by rfl) ⟨182457, by rfl⟩ : syracuseStep 1946213 = 364915) (by norm_num)
theorem B864893 : Blo 574812 864893 := bbase (se 3 (by rfl) ⟨162167, by rfl⟩ : syracuseStep 864893 = 324335) (by norm_num)
theorem B864917 : Blo 574812 864917 := bbase (se 6 (by rfl) ⟨20271, by rfl⟩ : syracuseStep 864917 = 40543) (by norm_num)
theorem B864941 : Blo 574812 864941 := bbase (se 3 (by rfl) ⟨162176, by rfl⟩ : syracuseStep 864941 = 324353) (by norm_num)
theorem B864965 : Blo 574812 864965 := bbase (se 4 (by rfl) ⟨81090, by rfl⟩ : syracuseStep 864965 = 162181) (by norm_num)
theorem B3683029 : Blo 574812 3683029 := bbase (se 7 (by rfl) ⟨43160, by rfl⟩ : syracuseStep 3683029 = 86321) (by norm_num)
theorem B864989 : Blo 574812 864989 := bbase (se 3 (by rfl) ⟨162185, by rfl⟩ : syracuseStep 864989 = 324371) (by norm_num)
theorem B1094381 : Blo 574812 1094381 := bbase (se 3 (by rfl) ⟨205196, by rfl⟩ : syracuseStep 1094381 = 410393) (by norm_num)
theorem B865013 : Blo 574812 865013 := bbase (se 5 (by rfl) ⟨40547, by rfl⟩ : syracuseStep 865013 = 81095) (by norm_num)
theorem B865037 : Blo 574812 865037 := bbase (se 3 (by rfl) ⟨162194, by rfl⟩ : syracuseStep 865037 = 324389) (by norm_num)
theorem B865061 : Blo 574812 865061 := bbase (se 4 (by rfl) ⟨81099, by rfl⟩ : syracuseStep 865061 = 162199) (by norm_num)
theorem B2929445 : Blo 574812 2929445 := bbase (se 4 (by rfl) ⟨274635, by rfl⟩ : syracuseStep 2929445 = 549271) (by norm_num)
theorem B865085 : Blo 574812 865085 := bbase (se 3 (by rfl) ⟨162203, by rfl⟩ : syracuseStep 865085 = 324407) (by norm_num)
theorem B1684309 : Blo 574812 1684309 := bbase (se 9 (by rfl) ⟨4934, by rfl⟩ : syracuseStep 1684309 = 9869) (by norm_num)
theorem B865109 : Blo 574812 865109 := bbase (se 9 (by rfl) ⟨2534, by rfl⟩ : syracuseStep 865109 = 5069) (by norm_num)
theorem B2962277 : Blo 574812 2962277 := bbase (se 4 (by rfl) ⟨277713, by rfl⟩ : syracuseStep 2962277 = 555427) (by norm_num)
theorem B865133 : Blo 574812 865133 := bbase (se 3 (by rfl) ⟨162212, by rfl⟩ : syracuseStep 865133 = 324425) (by norm_num)
theorem B865157 : Blo 574812 865157 := bbase (se 4 (by rfl) ⟨81108, by rfl⟩ : syracuseStep 865157 = 162217) (by norm_num)
theorem B865181 : Blo 574812 865181 := bbase (se 3 (by rfl) ⟨162221, by rfl⟩ : syracuseStep 865181 = 324443) (by norm_num)
theorem B865205 : Blo 574812 865205 := bbase (se 5 (by rfl) ⟨40556, by rfl⟩ : syracuseStep 865205 = 81113) (by norm_num)
theorem B865229 : Blo 574812 865229 := bbase (se 3 (by rfl) ⟨162230, by rfl⟩ : syracuseStep 865229 = 324461) (by norm_num)
theorem B12530645 : Blo 574812 12530645 := bbase (se 7 (by rfl) ⟨146843, by rfl⟩ : syracuseStep 12530645 = 293687) (by norm_num)
theorem B865253 : Blo 574812 865253 := bbase (se 4 (by rfl) ⟨81117, by rfl⟩ : syracuseStep 865253 = 162235) (by norm_num)
theorem B865277 : Blo 574812 865277 := bbase (se 3 (by rfl) ⟨162239, by rfl⟩ : syracuseStep 865277 = 324479) (by norm_num)
theorem B1389565 : Blo 574812 1389565 := bbase (se 3 (by rfl) ⟨260543, by rfl⟩ : syracuseStep 1389565 = 521087) (by norm_num)
theorem B1946645 : Blo 574812 1946645 := bbase (se 6 (by rfl) ⟨45624, by rfl⟩ : syracuseStep 1946645 = 91249) (by norm_num)
theorem B865301 : Blo 574812 865301 := bbase (se 6 (by rfl) ⟨20280, by rfl⟩ : syracuseStep 865301 = 40561) (by norm_num)
theorem B865325 : Blo 574812 865325 := bbase (se 3 (by rfl) ⟨162248, by rfl⟩ : syracuseStep 865325 = 324497) (by norm_num)
theorem B865349 : Blo 574812 865349 := bbase (se 4 (by rfl) ⟨81126, by rfl⟩ : syracuseStep 865349 = 162253) (by norm_num)
theorem B865373 : Blo 574812 865373 := bbase (se 3 (by rfl) ⟨162257, by rfl⟩ : syracuseStep 865373 = 324515) (by norm_num)
theorem B1455205 : Blo 574812 1455205 := bbase (se 4 (by rfl) ⟨136425, by rfl⟩ : syracuseStep 1455205 = 272851) (by norm_num)
theorem B865397 : Blo 574812 865397 := bbase (se 5 (by rfl) ⟨40565, by rfl⟩ : syracuseStep 865397 = 81131) (by norm_num)
theorem B865421 : Blo 574812 865421 := bbase (se 3 (by rfl) ⟨162266, by rfl⟩ : syracuseStep 865421 = 324533) (by norm_num)
theorem B865445 : Blo 574812 865445 := bbase (se 4 (by rfl) ⟨81135, by rfl⟩ : syracuseStep 865445 = 162271) (by norm_num)
theorem B865469 : Blo 574812 865469 := bbase (se 3 (by rfl) ⟨162275, by rfl⟩ : syracuseStep 865469 = 324551) (by norm_num)
theorem B1455317 : Blo 574812 1455317 := bbase (se 7 (by rfl) ⟨17054, by rfl⟩ : syracuseStep 1455317 = 34109) (by norm_num)
theorem B865493 : Blo 574812 865493 := bbase (se 7 (by rfl) ⟨10142, by rfl⟩ : syracuseStep 865493 = 20285) (by norm_num)
theorem B865517 : Blo 574812 865517 := bbase (se 3 (by rfl) ⟨162284, by rfl⟩ : syracuseStep 865517 = 324569) (by norm_num)
theorem B865541 : Blo 574812 865541 := bbase (se 4 (by rfl) ⟨81144, by rfl⟩ : syracuseStep 865541 = 162289) (by norm_num)
theorem B865565 : Blo 574812 865565 := bbase (se 3 (by rfl) ⟨162293, by rfl⟩ : syracuseStep 865565 = 324587) (by norm_num)
theorem B865589 : Blo 574812 865589 := bbase (se 5 (by rfl) ⟨40574, by rfl⟩ : syracuseStep 865589 = 81149) (by norm_num)
theorem B865613 : Blo 574812 865613 := bbase (se 3 (by rfl) ⟨162302, by rfl⟩ : syracuseStep 865613 = 324605) (by norm_num)
theorem B865637 : Blo 574812 865637 := bbase (se 4 (by rfl) ⟨81153, by rfl⟩ : syracuseStep 865637 = 162307) (by norm_num)
theorem B865661 : Blo 574812 865661 := bbase (se 3 (by rfl) ⟨162311, by rfl⟩ : syracuseStep 865661 = 324623) (by norm_num)
theorem B1455509 : Blo 574812 1455509 := bbase (se 6 (by rfl) ⟨34113, by rfl⟩ : syracuseStep 1455509 = 68227) (by norm_num)
theorem B865685 : Blo 574812 865685 := bbase (se 6 (by rfl) ⟨20289, by rfl⟩ : syracuseStep 865685 = 40579) (by norm_num)
theorem B865709 : Blo 574812 865709 := bbase (se 3 (by rfl) ⟨162320, by rfl⟩ : syracuseStep 865709 = 324641) (by norm_num)
theorem B1947077 : Blo 574812 1947077 := bbase (se 4 (by rfl) ⟨182538, by rfl⟩ : syracuseStep 1947077 = 365077) (by norm_num)
theorem B865733 : Blo 574812 865733 := bbase (se 4 (by rfl) ⟨81162, by rfl⟩ : syracuseStep 865733 = 162325) (by norm_num)
theorem B1095133 : Blo 574812 1095133 := bbase (se 3 (by rfl) ⟨205337, by rfl⟩ : syracuseStep 1095133 = 410675) (by norm_num)
theorem B865757 : Blo 574812 865757 := bbase (se 3 (by rfl) ⟨162329, by rfl⟩ : syracuseStep 865757 = 324659) (by norm_num)
theorem B865781 : Blo 574812 865781 := bbase (se 5 (by rfl) ⟨40583, by rfl⟩ : syracuseStep 865781 = 81167) (by norm_num)
theorem B865805 : Blo 574812 865805 := bbase (se 3 (by rfl) ⟨162338, by rfl⟩ : syracuseStep 865805 = 324677) (by norm_num)
theorem B865829 : Blo 574812 865829 := bbase (se 4 (by rfl) ⟨81171, by rfl⟩ : syracuseStep 865829 = 162343) (by norm_num)
theorem B865853 : Blo 574812 865853 := bbase (se 3 (by rfl) ⟨162347, by rfl⟩ : syracuseStep 865853 = 324695) (by norm_num)
theorem B865877 : Blo 574812 865877 := bbase (se 8 (by rfl) ⟨5073, by rfl⟩ : syracuseStep 865877 = 10147) (by norm_num)
theorem B8336981 : Blo 574812 8336981 := bbase (se 8 (by rfl) ⟨48849, by rfl⟩ : syracuseStep 8336981 = 97699) (by norm_num)
theorem B1095277 : Blo 574812 1095277 := bbase (se 3 (by rfl) ⟨205364, by rfl⟩ : syracuseStep 1095277 = 410729) (by norm_num)
theorem B865901 : Blo 574812 865901 := bbase (se 3 (by rfl) ⟨162356, by rfl⟩ : syracuseStep 865901 = 324713) (by norm_num)
theorem B865925 : Blo 574812 865925 := bbase (se 4 (by rfl) ⟨81180, by rfl⟩ : syracuseStep 865925 = 162361) (by norm_num)
theorem B1390229 : Blo 574812 1390229 := bbase (se 6 (by rfl) ⟨32583, by rfl⟩ : syracuseStep 1390229 = 65167) (by norm_num)
theorem B865949 : Blo 574812 865949 := bbase (se 3 (by rfl) ⟨162365, by rfl⟩ : syracuseStep 865949 = 324731) (by norm_num)
theorem B865973 : Blo 574812 865973 := bbase (se 5 (by rfl) ⟨40592, by rfl⟩ : syracuseStep 865973 = 81185) (by norm_num)
theorem B865997 : Blo 574812 865997 := bbase (se 3 (by rfl) ⟨162374, by rfl⟩ : syracuseStep 865997 = 324749) (by norm_num)
theorem B866021 : Blo 574812 866021 := bbase (se 4 (by rfl) ⟨81189, by rfl⟩ : syracuseStep 866021 = 162379) (by norm_num)
theorem B1455853 : Blo 574812 1455853 := bbase (se 3 (by rfl) ⟨272972, by rfl⟩ : syracuseStep 1455853 = 545945) (by norm_num)
theorem B866045 : Blo 574812 866045 := bbase (se 3 (by rfl) ⟨162383, by rfl⟩ : syracuseStep 866045 = 324767) (by norm_num)
theorem B1095437 : Blo 574812 1095437 := bbase (se 3 (by rfl) ⟨205394, by rfl⟩ : syracuseStep 1095437 = 410789) (by norm_num)
theorem B866069 : Blo 574812 866069 := bbase (se 6 (by rfl) ⟨20298, by rfl⟩ : syracuseStep 866069 = 40597) (by norm_num)
theorem B2635541 : Blo 574812 2635541 := bbase (se 6 (by rfl) ⟨61770, by rfl⟩ : syracuseStep 2635541 = 123541) (by norm_num)
theorem B3127061 : Blo 574812 3127061 := bbase (se 6 (by rfl) ⟨73290, by rfl⟩ : syracuseStep 3127061 = 146581) (by norm_num)
theorem B866093 : Blo 574812 866093 := bbase (se 3 (by rfl) ⟨162392, by rfl⟩ : syracuseStep 866093 = 324785) (by norm_num)
theorem B866117 : Blo 574812 866117 := bbase (se 4 (by rfl) ⟨81198, by rfl⟩ : syracuseStep 866117 = 162397) (by norm_num)
theorem B1455965 : Blo 574812 1455965 := bbase (se 3 (by rfl) ⟨272993, by rfl⟩ : syracuseStep 1455965 = 545987) (by norm_num)
theorem B866141 : Blo 574812 866141 := bbase (se 3 (by rfl) ⟨162401, by rfl⟩ : syracuseStep 866141 = 324803) (by norm_num)
theorem B1947509 : Blo 574812 1947509 := bbase (se 5 (by rfl) ⟨91289, by rfl⟩ : syracuseStep 1947509 = 182579) (by norm_num)
theorem B866165 : Blo 574812 866165 := bbase (se 5 (by rfl) ⟨40601, by rfl⟩ : syracuseStep 866165 = 81203) (by norm_num)
theorem B866189 : Blo 574812 866189 := bbase (se 3 (by rfl) ⟨162410, by rfl⟩ : syracuseStep 866189 = 324821) (by norm_num)
theorem B11384725 : Blo 574812 11384725 := bbase (se 6 (by rfl) ⟨266829, by rfl⟩ : syracuseStep 11384725 = 533659) (by norm_num)
theorem B2635669 : Blo 574812 2635669 := bbase (se 6 (by rfl) ⟨61773, by rfl⟩ : syracuseStep 2635669 = 123547) (by norm_num)
theorem B1095581 : Blo 574812 1095581 := bbase (se 3 (by rfl) ⟨205421, by rfl⟩ : syracuseStep 1095581 = 410843) (by norm_num)
theorem B866213 : Blo 574812 866213 := bbase (se 4 (by rfl) ⟨81207, by rfl⟩ : syracuseStep 866213 = 162415) (by norm_num)
theorem B1390517 : Blo 574812 1390517 := bbase (se 5 (by rfl) ⟨65180, by rfl⟩ : syracuseStep 1390517 = 130361) (by norm_num)
theorem B866237 : Blo 574812 866237 := bbase (se 3 (by rfl) ⟨162419, by rfl⟩ : syracuseStep 866237 = 324839) (by norm_num)
theorem B866261 : Blo 574812 866261 := bbase (se 7 (by rfl) ⟨10151, by rfl⟩ : syracuseStep 866261 = 20303) (by norm_num)
theorem B866285 : Blo 574812 866285 := bbase (se 3 (by rfl) ⟨162428, by rfl⟩ : syracuseStep 866285 = 324857) (by norm_num)
theorem B866309 : Blo 574812 866309 := bbase (se 4 (by rfl) ⟨81216, by rfl⟩ : syracuseStep 866309 = 162433) (by norm_num)
theorem B1456157 : Blo 574812 1456157 := bbase (se 3 (by rfl) ⟨273029, by rfl⟩ : syracuseStep 1456157 = 546059) (by norm_num)
theorem B866333 : Blo 574812 866333 := bbase (se 3 (by rfl) ⟨162437, by rfl⟩ : syracuseStep 866333 = 324875) (by norm_num)
theorem B866357 : Blo 574812 866357 := bbase (se 5 (by rfl) ⟨40610, by rfl⟩ : syracuseStep 866357 = 81221) (by norm_num)
theorem B866381 : Blo 574812 866381 := bbase (se 3 (by rfl) ⟨162446, by rfl⟩ : syracuseStep 866381 = 324893) (by norm_num)
theorem B702553 : Blo 574812 702553 := bbase (se 2 (by rfl) ⟨263457, by rfl⟩ : syracuseStep 702553 = 526915) (by norm_num)
theorem B866405 : Blo 574812 866405 := bbase (se 4 (by rfl) ⟨81225, by rfl⟩ : syracuseStep 866405 = 162451) (by norm_num)
theorem B866429 : Blo 574812 866429 := bbase (se 3 (by rfl) ⟨162455, by rfl⟩ : syracuseStep 866429 = 324911) (by norm_num)
theorem B866453 : Blo 574812 866453 := bbase (se 6 (by rfl) ⟨20307, by rfl⟩ : syracuseStep 866453 = 40615) (by norm_num)
theorem B2078885 : Blo 574812 2078885 := bbase (se 4 (by rfl) ⟨194895, by rfl⟩ : syracuseStep 2078885 = 389791) (by norm_num)
theorem B866477 : Blo 574812 866477 := bbase (se 3 (by rfl) ⟨162464, by rfl⟩ : syracuseStep 866477 = 324929) (by norm_num)
theorem B1095869 : Blo 574812 1095869 := bbase (se 3 (by rfl) ⟨205475, by rfl⟩ : syracuseStep 1095869 = 410951) (by norm_num)
theorem B866501 : Blo 574812 866501 := bbase (se 4 (by rfl) ⟨81234, by rfl⟩ : syracuseStep 866501 = 162469) (by norm_num)
theorem B866525 : Blo 574812 866525 := bbase (se 3 (by rfl) ⟨162473, by rfl⟩ : syracuseStep 866525 = 324947) (by norm_num)
theorem B866549 : Blo 574812 866549 := bbase (se 5 (by rfl) ⟨40619, by rfl⟩ : syracuseStep 866549 = 81239) (by norm_num)
theorem B866573 : Blo 574812 866573 := bbase (se 3 (by rfl) ⟨162482, by rfl⟩ : syracuseStep 866573 = 324965) (by norm_num)
theorem B1947941 : Blo 574812 1947941 := bbase (se 4 (by rfl) ⟨182619, by rfl⟩ : syracuseStep 1947941 = 365239) (by norm_num)
theorem B866597 : Blo 574812 866597 := bbase (se 4 (by rfl) ⟨81243, by rfl⟩ : syracuseStep 866597 = 162487) (by norm_num)
theorem B866621 : Blo 574812 866621 := bbase (se 3 (by rfl) ⟨162491, by rfl⟩ : syracuseStep 866621 = 324983) (by norm_num)
theorem B1096021 : Blo 574812 1096021 := bbase (se 10 (by rfl) ⟨1605, by rfl⟩ : syracuseStep 1096021 = 3211) (by norm_num)
theorem B866645 : Blo 574812 866645 := bbase (se 10 (by rfl) ⟨1269, by rfl⟩ : syracuseStep 866645 = 2539) (by norm_num)
theorem B866669 : Blo 574812 866669 := bbase (se 3 (by rfl) ⟨162500, by rfl⟩ : syracuseStep 866669 = 325001) (by norm_num)
theorem B1456501 : Blo 574812 1456501 := bbase (se 5 (by rfl) ⟨68273, by rfl⟩ : syracuseStep 1456501 = 136547) (by norm_num)
theorem B866693 : Blo 574812 866693 := bbase (se 4 (by rfl) ⟨81252, by rfl⟩ : syracuseStep 866693 = 162505) (by norm_num)
theorem B866717 : Blo 574812 866717 := bbase (se 3 (by rfl) ⟨162509, by rfl⟩ : syracuseStep 866717 = 325019) (by norm_num)
theorem B866741 : Blo 574812 866741 := bbase (se 5 (by rfl) ⟨40628, by rfl⟩ : syracuseStep 866741 = 81257) (by norm_num)
theorem B2472389 : Blo 574812 2472389 := bbase (se 4 (by rfl) ⟨231786, by rfl⟩ : syracuseStep 2472389 = 463573) (by norm_num)
theorem B866765 : Blo 574812 866765 := bbase (se 3 (by rfl) ⟨162518, by rfl⟩ : syracuseStep 866765 = 325037) (by norm_num)
theorem B1456613 : Blo 574812 1456613 := bbase (se 4 (by rfl) ⟨136557, by rfl⟩ : syracuseStep 1456613 = 273115) (by norm_num)
theorem B866789 : Blo 574812 866789 := bbase (se 4 (by rfl) ⟨81261, by rfl⟩ : syracuseStep 866789 = 162523) (by norm_num)
theorem B866813 : Blo 574812 866813 := bbase (se 3 (by rfl) ⟨162527, by rfl⟩ : syracuseStep 866813 = 325055) (by norm_num)
theorem B866837 : Blo 574812 866837 := bbase (se 6 (by rfl) ⟨20316, by rfl⟩ : syracuseStep 866837 = 40633) (by norm_num)
theorem B866861 : Blo 574812 866861 := bbase (se 3 (by rfl) ⟨162536, by rfl⟩ : syracuseStep 866861 = 325073) (by norm_num)
theorem B866885 : Blo 574812 866885 := bbase (se 4 (by rfl) ⟨81270, by rfl⟩ : syracuseStep 866885 = 162541) (by norm_num)
theorem B2767445 : Blo 574812 2767445 := bbase (se 8 (by rfl) ⟨16215, by rfl⟩ : syracuseStep 2767445 = 32431) (by norm_num)
theorem B834133 : Blo 574812 834133 := bbase (se 8 (by rfl) ⟨4887, by rfl⟩ : syracuseStep 834133 = 9775) (by norm_num)
theorem B866909 : Blo 574812 866909 := bbase (se 3 (by rfl) ⟨162545, by rfl⟩ : syracuseStep 866909 = 325091) (by norm_num)
theorem B866933 : Blo 574812 866933 := bbase (se 5 (by rfl) ⟨40637, by rfl⟩ : syracuseStep 866933 = 81275) (by norm_num)
theorem B1096325 : Blo 574812 1096325 := bbase (se 4 (by rfl) ⟨102780, by rfl⟩ : syracuseStep 1096325 = 205561) (by norm_num)
theorem B866957 : Blo 574812 866957 := bbase (se 3 (by rfl) ⟨162554, by rfl⟩ : syracuseStep 866957 = 325109) (by norm_num)
theorem B1456805 : Blo 574812 1456805 := bbase (se 4 (by rfl) ⟨136575, by rfl⟩ : syracuseStep 1456805 = 273151) (by norm_num)
theorem B866981 : Blo 574812 866981 := bbase (se 4 (by rfl) ⟨81279, by rfl⟩ : syracuseStep 866981 = 162559) (by norm_num)
theorem B867005 : Blo 574812 867005 := bbase (se 3 (by rfl) ⟨162563, by rfl⟩ : syracuseStep 867005 = 325127) (by norm_num)
theorem B2243285 : Blo 574812 2243285 := bbase (se 7 (by rfl) ⟨26288, by rfl⟩ : syracuseStep 2243285 = 52577) (by norm_num)
theorem B1948373 : Blo 574812 1948373 := bbase (se 7 (by rfl) ⟨22832, by rfl⟩ : syracuseStep 1948373 = 45665) (by norm_num)
theorem B867029 : Blo 574812 867029 := bbase (se 7 (by rfl) ⟨10160, by rfl⟩ : syracuseStep 867029 = 20321) (by norm_num)
theorem B867053 : Blo 574812 867053 := bbase (se 3 (by rfl) ⟨162572, by rfl⟩ : syracuseStep 867053 = 325145) (by norm_num)
theorem B867077 : Blo 574812 867077 := bbase (se 4 (by rfl) ⟨81288, by rfl⟩ : syracuseStep 867077 = 162577) (by norm_num)
theorem B867101 : Blo 574812 867101 := bbase (se 3 (by rfl) ⟨162581, by rfl⟩ : syracuseStep 867101 = 325163) (by norm_num)
theorem B867125 : Blo 574812 867125 := bbase (se 5 (by rfl) ⟨40646, by rfl⟩ : syracuseStep 867125 = 81293) (by norm_num)
theorem B867149 : Blo 574812 867149 := bbase (se 3 (by rfl) ⟨162590, by rfl⟩ : syracuseStep 867149 = 325181) (by norm_num)
theorem B867173 : Blo 574812 867173 := bbase (se 4 (by rfl) ⟨81297, by rfl⟩ : syracuseStep 867173 = 162595) (by norm_num)
theorem B867197 : Blo 574812 867197 := bbase (se 3 (by rfl) ⟨162599, by rfl⟩ : syracuseStep 867197 = 325199) (by norm_num)
theorem B867221 : Blo 574812 867221 := bbase (se 6 (by rfl) ⟨20325, by rfl⟩ : syracuseStep 867221 = 40651) (by norm_num)
theorem B867245 : Blo 574812 867245 := bbase (se 3 (by rfl) ⟨162608, by rfl⟩ : syracuseStep 867245 = 325217) (by norm_num)
theorem B1850293 : Blo 574812 1850293 := bbase (se 5 (by rfl) ⟨86732, by rfl⟩ : syracuseStep 1850293 = 173465) (by norm_num)
theorem B867269 : Blo 574812 867269 := bbase (se 4 (by rfl) ⟨81306, by rfl⟩ : syracuseStep 867269 = 162613) (by norm_num)
theorem B867293 : Blo 574812 867293 := bbase (se 3 (by rfl) ⟨162617, by rfl⟩ : syracuseStep 867293 = 325235) (by norm_num)
theorem B1850357 : Blo 574812 1850357 := bbase (se 5 (by rfl) ⟨86735, by rfl⟩ : syracuseStep 1850357 = 173471) (by norm_num)
theorem B867317 : Blo 574812 867317 := bbase (se 5 (by rfl) ⟨40655, by rfl⟩ : syracuseStep 867317 = 81311) (by norm_num)
theorem B1457149 : Blo 574812 1457149 := bbase (se 3 (by rfl) ⟨273215, by rfl⟩ : syracuseStep 1457149 = 546431) (by norm_num)
theorem B2079749 : Blo 574812 2079749 := bbase (se 4 (by rfl) ⟨194976, by rfl⟩ : syracuseStep 2079749 = 389953) (by norm_num)
theorem B867341 : Blo 574812 867341 := bbase (se 3 (by rfl) ⟨162626, by rfl⟩ : syracuseStep 867341 = 325253) (by norm_num)
theorem B867365 : Blo 574812 867365 := bbase (se 4 (by rfl) ⟨81315, by rfl⟩ : syracuseStep 867365 = 162631) (by norm_num)
theorem B867389 : Blo 574812 867389 := bbase (se 3 (by rfl) ⟨162635, by rfl⟩ : syracuseStep 867389 = 325271) (by norm_num)
theorem B1293389 : Blo 574812 1293389 := bbase (se 3 (by rfl) ⟨242510, by rfl⟩ : syracuseStep 1293389 = 485021) (by norm_num)
theorem B867413 : Blo 574812 867413 := bbase (se 8 (by rfl) ⟨5082, by rfl⟩ : syracuseStep 867413 = 10165) (by norm_num)
theorem B1457261 : Blo 574812 1457261 := bbase (se 3 (by rfl) ⟨273236, by rfl⟩ : syracuseStep 1457261 = 546473) (by norm_num)
theorem B867437 : Blo 574812 867437 := bbase (se 3 (by rfl) ⟨162644, by rfl⟩ : syracuseStep 867437 = 325289) (by norm_num)
theorem B1948805 : Blo 574812 1948805 := bbase (se 4 (by rfl) ⟨182700, by rfl⟩ : syracuseStep 1948805 = 365401) (by norm_num)
theorem B867461 : Blo 574812 867461 := bbase (se 4 (by rfl) ⟨81324, by rfl⟩ : syracuseStep 867461 = 162649) (by norm_num)
theorem B1293461 : Blo 574812 1293461 := bbase (se 6 (by rfl) ⟨30315, by rfl⟩ : syracuseStep 1293461 = 60631) (by norm_num)
theorem B867485 : Blo 574812 867485 := bbase (se 3 (by rfl) ⟨162653, by rfl⟩ : syracuseStep 867485 = 325307) (by norm_num)
theorem B867509 : Blo 574812 867509 := bbase (se 5 (by rfl) ⟨40664, by rfl⟩ : syracuseStep 867509 = 81329) (by norm_num)
theorem B867533 : Blo 574812 867533 := bbase (se 3 (by rfl) ⟨162662, by rfl⟩ : syracuseStep 867533 = 325325) (by norm_num)
theorem B1293533 : Blo 574812 1293533 := bbase (se 3 (by rfl) ⟨242537, by rfl⟩ : syracuseStep 1293533 = 485075) (by norm_num)
theorem B867557 : Blo 574812 867557 := bbase (se 4 (by rfl) ⟨81333, by rfl⟩ : syracuseStep 867557 = 162667) (by norm_num)
theorem B867581 : Blo 574812 867581 := bbase (se 3 (by rfl) ⟨162671, by rfl⟩ : syracuseStep 867581 = 325343) (by norm_num)
theorem B867605 : Blo 574812 867605 := bbase (se 6 (by rfl) ⟨20334, by rfl⟩ : syracuseStep 867605 = 40669) (by norm_num)
theorem B1228061 : Blo 574812 1228061 := bbase (se 3 (by rfl) ⟨230261, by rfl⟩ : syracuseStep 1228061 = 460523) (by norm_num)
theorem B1293605 : Blo 574812 1293605 := bbase (se 4 (by rfl) ⟨121275, by rfl⟩ : syracuseStep 1293605 = 242551) (by norm_num)
theorem B1228069 : Blo 574812 1228069 := bbase (se 4 (by rfl) ⟨115131, by rfl⟩ : syracuseStep 1228069 = 230263) (by norm_num)
theorem B1457453 : Blo 574812 1457453 := bbase (se 3 (by rfl) ⟨273272, by rfl⟩ : syracuseStep 1457453 = 546545) (by norm_num)
theorem B867629 : Blo 574812 867629 := bbase (se 3 (by rfl) ⟨162680, by rfl⟩ : syracuseStep 867629 = 325361) (by norm_num)
theorem B867653 : Blo 574812 867653 := bbase (se 4 (by rfl) ⟨81342, by rfl⟩ : syracuseStep 867653 = 162685) (by norm_num)
theorem B867677 : Blo 574812 867677 := bbase (se 3 (by rfl) ⟨162689, by rfl⟩ : syracuseStep 867677 = 325379) (by norm_num)
theorem B1293677 : Blo 574812 1293677 := bbase (se 3 (by rfl) ⟨242564, by rfl⟩ : syracuseStep 1293677 = 485129) (by norm_num)
theorem B1097077 : Blo 574812 1097077 := bbase (se 5 (by rfl) ⟨51425, by rfl⟩ : syracuseStep 1097077 = 102851) (by norm_num)
theorem B867701 : Blo 574812 867701 := bbase (se 5 (by rfl) ⟨40673, by rfl⟩ : syracuseStep 867701 = 81347) (by norm_num)
theorem B867725 : Blo 574812 867725 := bbase (se 3 (by rfl) ⟨162698, by rfl⟩ : syracuseStep 867725 = 325397) (by norm_num)
theorem B867749 : Blo 574812 867749 := bbase (se 4 (by rfl) ⟨81351, by rfl⟩ : syracuseStep 867749 = 162703) (by norm_num)
theorem B1293749 : Blo 574812 1293749 := bbase (se 5 (by rfl) ⟨60644, by rfl⟩ : syracuseStep 1293749 = 121289) (by norm_num)
theorem B867773 : Blo 574812 867773 := bbase (se 3 (by rfl) ⟨162707, by rfl⟩ : syracuseStep 867773 = 325415) (by norm_num)
theorem B867797 : Blo 574812 867797 := bbase (se 7 (by rfl) ⟨10169, by rfl⟩ : syracuseStep 867797 = 20339) (by norm_num)
theorem B867821 : Blo 574812 867821 := bbase (se 3 (by rfl) ⟨162716, by rfl⟩ : syracuseStep 867821 = 325433) (by norm_num)
theorem B1293821 : Blo 574812 1293821 := bbase (se 3 (by rfl) ⟨242591, by rfl⟩ : syracuseStep 1293821 = 485183) (by norm_num)
theorem B1097221 : Blo 574812 1097221 := bbase (se 4 (by rfl) ⟨102864, by rfl⟩ : syracuseStep 1097221 = 205729) (by norm_num)
theorem B867845 : Blo 574812 867845 := bbase (se 4 (by rfl) ⟨81360, by rfl⟩ : syracuseStep 867845 = 162721) (by norm_num)
theorem B867869 : Blo 574812 867869 := bbase (se 3 (by rfl) ⟨162725, by rfl⟩ : syracuseStep 867869 = 325451) (by norm_num)
theorem B1949237 : Blo 574812 1949237 := bbase (se 5 (by rfl) ⟨91370, by rfl⟩ : syracuseStep 1949237 = 182741) (by norm_num)
theorem B867893 : Blo 574812 867893 := bbase (se 5 (by rfl) ⟨40682, by rfl⟩ : syracuseStep 867893 = 81365) (by norm_num)
theorem B1293893 : Blo 574812 1293893 := bbase (se 4 (by rfl) ⟨121302, by rfl⟩ : syracuseStep 1293893 = 242605) (by norm_num)
theorem B2080325 : Blo 574812 2080325 := bbase (se 4 (by rfl) ⟨195030, by rfl⟩ : syracuseStep 2080325 = 390061) (by norm_num)
theorem B867917 : Blo 574812 867917 := bbase (se 3 (by rfl) ⟨162734, by rfl⟩ : syracuseStep 867917 = 325469) (by norm_num)
theorem B3292757 : Blo 574812 3292757 := bbase (se 8 (by rfl) ⟨19293, by rfl⟩ : syracuseStep 3292757 = 38587) (by norm_num)
theorem B867941 : Blo 574812 867941 := bbase (se 4 (by rfl) ⟨81369, by rfl⟩ : syracuseStep 867941 = 162739) (by norm_num)
theorem B867965 : Blo 574812 867965 := bbase (se 3 (by rfl) ⟨162743, by rfl⟩ : syracuseStep 867965 = 325487) (by norm_num)
theorem B1457797 : Blo 574812 1457797 := bbase (se 4 (by rfl) ⟨136668, by rfl⟩ : syracuseStep 1457797 = 273337) (by norm_num)
theorem B1293965 : Blo 574812 1293965 := bbase (se 3 (by rfl) ⟨242618, by rfl⟩ : syracuseStep 1293965 = 485237) (by norm_num)
theorem B867989 : Blo 574812 867989 := bbase (se 6 (by rfl) ⟨20343, by rfl⟩ : syracuseStep 867989 = 40687) (by norm_num)
theorem B1097381 : Blo 574812 1097381 := bbase (se 4 (by rfl) ⟨102879, by rfl⟩ : syracuseStep 1097381 = 205759) (by norm_num)
theorem B868013 : Blo 574812 868013 := bbase (se 3 (by rfl) ⟨162752, by rfl⟩ : syracuseStep 868013 = 325505) (by norm_num)
theorem B868037 : Blo 574812 868037 := bbase (se 4 (by rfl) ⟨81378, by rfl⟩ : syracuseStep 868037 = 162757) (by norm_num)
theorem B1294037 : Blo 574812 1294037 := bbase (se 7 (by rfl) ⟨15164, by rfl⟩ : syracuseStep 1294037 = 30329) (by norm_num)
theorem B868061 : Blo 574812 868061 := bbase (se 3 (by rfl) ⟨162761, by rfl⟩ : syracuseStep 868061 = 325523) (by norm_num)
theorem B1457909 : Blo 574812 1457909 := bbase (se 5 (by rfl) ⟨68339, by rfl⟩ : syracuseStep 1457909 = 136679) (by norm_num)
theorem B868085 : Blo 574812 868085 := bbase (se 5 (by rfl) ⟨40691, by rfl⟩ : syracuseStep 868085 = 81383) (by norm_num)
theorem B868109 : Blo 574812 868109 := bbase (se 3 (by rfl) ⟨162770, by rfl⟩ : syracuseStep 868109 = 325541) (by norm_num)
theorem B1294109 : Blo 574812 1294109 := bbase (se 3 (by rfl) ⟨242645, by rfl⟩ : syracuseStep 1294109 = 485291) (by norm_num)
theorem B868133 : Blo 574812 868133 := bbase (se 4 (by rfl) ⟨81387, by rfl⟩ : syracuseStep 868133 = 162775) (by norm_num)
theorem B1097525 : Blo 574812 1097525 := bbase (se 5 (by rfl) ⟨51446, by rfl⟩ : syracuseStep 1097525 = 102893) (by norm_num)
theorem B868157 : Blo 574812 868157 := bbase (se 3 (by rfl) ⟨162779, by rfl⟩ : syracuseStep 868157 = 325559) (by norm_num)
theorem B868181 : Blo 574812 868181 := bbase (se 9 (by rfl) ⟨2543, by rfl⟩ : syracuseStep 868181 = 5087) (by norm_num)
theorem B1294181 : Blo 574812 1294181 := bbase (se 4 (by rfl) ⟨121329, by rfl⟩ : syracuseStep 1294181 = 242659) (by norm_num)
theorem B868205 : Blo 574812 868205 := bbase (se 3 (by rfl) ⟨162788, by rfl⟩ : syracuseStep 868205 = 325577) (by norm_num)
theorem B1294253 : Blo 574812 1294253 := bbase (se 3 (by rfl) ⟨242672, by rfl⟩ : syracuseStep 1294253 = 485345) (by norm_num)
theorem B1458101 : Blo 574812 1458101 := bbase (se 5 (by rfl) ⟨68348, by rfl⟩ : syracuseStep 1458101 = 136697) (by norm_num)
theorem B4374485 : Blo 574812 4374485 := bbase (se 7 (by rfl) ⟨51263, by rfl⟩ : syracuseStep 4374485 = 102527) (by norm_num)
theorem B1949669 : Blo 574812 1949669 := bbase (se 4 (by rfl) ⟨182781, by rfl⟩ : syracuseStep 1949669 = 365563) (by norm_num)
theorem B1294325 : Blo 574812 1294325 := bbase (se 5 (by rfl) ⟨60671, by rfl⟩ : syracuseStep 1294325 = 121343) (by norm_num)
theorem B1294397 : Blo 574812 1294397 := bbase (se 3 (by rfl) ⟨242699, by rfl⟩ : syracuseStep 1294397 = 485399) (by norm_num)
theorem B1097813 : Blo 574812 1097813 := bbase (se 8 (by rfl) ⟨6432, by rfl⟩ : syracuseStep 1097813 = 12865) (by norm_num)
theorem B1294469 : Blo 574812 1294469 := bbase (se 4 (by rfl) ⟨121356, by rfl⟩ : syracuseStep 1294469 = 242713) (by norm_num)
theorem B1294541 : Blo 574812 1294541 := bbase (se 3 (by rfl) ⟨242726, by rfl⟩ : syracuseStep 1294541 = 485453) (by norm_num)
theorem B1097965 : Blo 574812 1097965 := bbase (se 3 (by rfl) ⟨205868, by rfl⟩ : syracuseStep 1097965 = 411737) (by norm_num)
theorem B1458445 : Blo 574812 1458445 := bbase (se 3 (by rfl) ⟨273458, by rfl⟩ : syracuseStep 1458445 = 546917) (by norm_num)
theorem B1294613 : Blo 574812 1294613 := bbase (se 6 (by rfl) ⟨30342, by rfl⟩ : syracuseStep 1294613 = 60685) (by norm_num)
theorem B1294685 : Blo 574812 1294685 := bbase (se 3 (by rfl) ⟨242753, by rfl⟩ : syracuseStep 1294685 = 485507) (by norm_num)
theorem B737633 : Blo 574812 737633 := bbase (se 2 (by rfl) ⟨276612, by rfl⟩ : syracuseStep 737633 = 553225) (by norm_num)
theorem B1458557 : Blo 574812 1458557 := bbase (se 3 (by rfl) ⟨273479, by rfl⟩ : syracuseStep 1458557 = 546959) (by norm_num)
theorem B1229197 : Blo 574812 1229197 := bbase (se 3 (by rfl) ⟨230474, by rfl⟩ : syracuseStep 1229197 = 460949) (by norm_num)
theorem B1950101 : Blo 574812 1950101 := bbase (se 6 (by rfl) ⟨45705, by rfl⟩ : syracuseStep 1950101 = 91411) (by norm_num)
theorem B1294757 : Blo 574812 1294757 := bbase (se 4 (by rfl) ⟨121383, by rfl⟩ : syracuseStep 1294757 = 242767) (by norm_num)
theorem B1294829 : Blo 574812 1294829 := bbase (se 3 (by rfl) ⟨242780, by rfl⟩ : syracuseStep 1294829 = 485561) (by norm_num)
theorem B737797 : Blo 574812 737797 := bbase (se 4 (by rfl) ⟨69168, by rfl⟩ : syracuseStep 737797 = 138337) (by norm_num)
theorem B1098269 : Blo 574812 1098269 := bbase (se 3 (by rfl) ⟨205925, by rfl⟩ : syracuseStep 1098269 = 411851) (by norm_num)
theorem B1294901 : Blo 574812 1294901 := bbase (se 5 (by rfl) ⟨60698, by rfl⟩ : syracuseStep 1294901 = 121397) (by norm_num)
theorem B2769461 : Blo 574812 2769461 := bbase (se 5 (by rfl) ⟨129818, by rfl⟩ : syracuseStep 2769461 = 259637) (by norm_num)
theorem B1458749 : Blo 574812 1458749 := bbase (se 3 (by rfl) ⟨273515, by rfl⟩ : syracuseStep 1458749 = 547031) (by norm_num)
theorem B1294973 : Blo 574812 1294973 := bbase (se 3 (by rfl) ⟨242807, by rfl⟩ : syracuseStep 1294973 = 485615) (by norm_num)
theorem B1295045 : Blo 574812 1295045 := bbase (se 4 (by rfl) ⟨121410, by rfl⟩ : syracuseStep 1295045 = 242821) (by norm_num)
theorem B2966213 : Blo 574812 2966213 := bbase (se 4 (by rfl) ⟨278082, by rfl⟩ : syracuseStep 2966213 = 556165) (by norm_num)
theorem B2769653 : Blo 574812 2769653 := bbase (se 5 (by rfl) ⟨129827, by rfl⟩ : syracuseStep 2769653 = 259655) (by norm_num)
theorem B1229573 : Blo 574812 1229573 := bbase (se 4 (by rfl) ⟨115272, by rfl⟩ : syracuseStep 1229573 = 230545) (by norm_num)
theorem B1295117 : Blo 574812 1295117 := bbase (se 3 (by rfl) ⟨242834, by rfl⟩ : syracuseStep 1295117 = 485669) (by norm_num)
theorem B1950533 : Blo 574812 1950533 := bbase (se 4 (by rfl) ⟨182862, by rfl⟩ : syracuseStep 1950533 = 365725) (by norm_num)
theorem B4146005 : Blo 574812 4146005 := bbase (se 9 (by rfl) ⟨12146, by rfl⟩ : syracuseStep 4146005 = 24293) (by norm_num)
theorem B1295189 : Blo 574812 1295189 := bbase (se 9 (by rfl) ⟨3794, by rfl⟩ : syracuseStep 1295189 = 7589) (by norm_num)
theorem B1459093 : Blo 574812 1459093 := bbase (se 6 (by rfl) ⟨34197, by rfl⟩ : syracuseStep 1459093 = 68395) (by norm_num)
theorem B1295261 : Blo 574812 1295261 := bbase (se 3 (by rfl) ⟨242861, by rfl⟩ : syracuseStep 1295261 = 485723) (by norm_num)
theorem B1557413 : Blo 574812 1557413 := bbase (se 4 (by rfl) ⟨146007, by rfl⟩ : syracuseStep 1557413 = 292015) (by norm_num)
theorem B1295333 : Blo 574812 1295333 := bbase (se 4 (by rfl) ⟨121437, by rfl⟩ : syracuseStep 1295333 = 242875) (by norm_num)
theorem B1459205 : Blo 574812 1459205 := bbase (se 4 (by rfl) ⟨136800, by rfl⟩ : syracuseStep 1459205 = 273601) (by norm_num)
theorem B1295405 : Blo 574812 1295405 := bbase (se 3 (by rfl) ⟨242888, by rfl⟩ : syracuseStep 1295405 = 485777) (by norm_num)
theorem B1295477 : Blo 574812 1295477 := bbase (se 5 (by rfl) ⟨60725, by rfl⟩ : syracuseStep 1295477 = 121451) (by norm_num)
theorem B1295549 : Blo 574812 1295549 := bbase (se 3 (by rfl) ⟨242915, by rfl⟩ : syracuseStep 1295549 = 485831) (by norm_num)
theorem B1459397 : Blo 574812 1459397 := bbase (se 4 (by rfl) ⟨136818, by rfl⟩ : syracuseStep 1459397 = 273637) (by norm_num)
theorem B1950965 : Blo 574812 1950965 := bbase (se 5 (by rfl) ⟨91451, by rfl⟩ : syracuseStep 1950965 = 182903) (by norm_num)
theorem B1295621 : Blo 574812 1295621 := bbase (se 4 (by rfl) ⟨121464, by rfl⟩ : syracuseStep 1295621 = 242929) (by norm_num)
theorem B1295693 : Blo 574812 1295693 := bbase (se 3 (by rfl) ⟨242942, by rfl⟩ : syracuseStep 1295693 = 485885) (by norm_num)
theorem B1295765 : Blo 574812 1295765 := bbase (se 6 (by rfl) ⟨30369, by rfl⟩ : syracuseStep 1295765 = 60739) (by norm_num)
theorem B1295837 : Blo 574812 1295837 := bbase (se 3 (by rfl) ⟨242969, by rfl⟩ : syracuseStep 1295837 = 485939) (by norm_num)
theorem B1459741 : Blo 574812 1459741 := bbase (se 3 (by rfl) ⟨273701, by rfl⟩ : syracuseStep 1459741 = 547403) (by norm_num)
theorem B1295909 : Blo 574812 1295909 := bbase (se 4 (by rfl) ⟨121491, by rfl⟩ : syracuseStep 1295909 = 242983) (by norm_num)
theorem B1295981 : Blo 574812 1295981 := bbase (se 3 (by rfl) ⟨242996, by rfl⟩ : syracuseStep 1295981 = 485993) (by norm_num)
theorem B1459853 : Blo 574812 1459853 := bbase (se 3 (by rfl) ⟨273722, by rfl⟩ : syracuseStep 1459853 = 547445) (by norm_num)
theorem B1951397 : Blo 574812 1951397 := bbase (se 4 (by rfl) ⟨182943, by rfl⟩ : syracuseStep 1951397 = 365887) (by norm_num)
theorem B1296053 : Blo 574812 1296053 := bbase (se 5 (by rfl) ⟨60752, by rfl⟩ : syracuseStep 1296053 = 121505) (by norm_num)
theorem B1296125 : Blo 574812 1296125 := bbase (se 3 (by rfl) ⟨243023, by rfl⟩ : syracuseStep 1296125 = 486047) (by norm_num)
theorem B1296197 : Blo 574812 1296197 := bbase (se 4 (by rfl) ⟨121518, by rfl⟩ : syracuseStep 1296197 = 243037) (by norm_num)
theorem B1460045 : Blo 574812 1460045 := bbase (se 3 (by rfl) ⟨273758, by rfl⟩ : syracuseStep 1460045 = 547517) (by norm_num)
theorem B1296269 : Blo 574812 1296269 := bbase (se 3 (by rfl) ⟨243050, by rfl⟩ : syracuseStep 1296269 = 486101) (by norm_num)
theorem B1853381 : Blo 574812 1853381 := bbase (se 4 (by rfl) ⟨173754, by rfl⟩ : syracuseStep 1853381 = 347509) (by norm_num)
theorem B1296341 : Blo 574812 1296341 := bbase (se 7 (by rfl) ⟨15191, by rfl⟩ : syracuseStep 1296341 = 30383) (by norm_num)
theorem B1296413 : Blo 574812 1296413 := bbase (se 3 (by rfl) ⟨243077, by rfl⟩ : syracuseStep 1296413 = 486155) (by norm_num)
theorem B1951829 : Blo 574812 1951829 := bbase (se 8 (by rfl) ⟨11436, by rfl⟩ : syracuseStep 1951829 = 22873) (by norm_num)
theorem B1296485 : Blo 574812 1296485 := bbase (se 4 (by rfl) ⟨121545, by rfl⟩ : syracuseStep 1296485 = 243091) (by norm_num)
theorem B1460389 : Blo 574812 1460389 := bbase (se 4 (by rfl) ⟨136911, by rfl⟩ : syracuseStep 1460389 = 273823) (by norm_num)
theorem B1296557 : Blo 574812 1296557 := bbase (se 3 (by rfl) ⟨243104, by rfl⟩ : syracuseStep 1296557 = 486209) (by norm_num)
theorem B1296629 : Blo 574812 1296629 := bbase (se 5 (by rfl) ⟨60779, by rfl⟩ : syracuseStep 1296629 = 121559) (by norm_num)
theorem B1460501 : Blo 574812 1460501 := bbase (se 6 (by rfl) ⟨34230, by rfl⟩ : syracuseStep 1460501 = 68461) (by norm_num)
theorem B1296701 : Blo 574812 1296701 := bbase (se 3 (by rfl) ⟨243131, by rfl⟩ : syracuseStep 1296701 = 486263) (by norm_num)
theorem B936269 : Blo 574812 936269 := bbase (se 3 (by rfl) ⟨175550, by rfl⟩ : syracuseStep 936269 = 351101) (by norm_num)
theorem B1231213 : Blo 574812 1231213 := bbase (se 3 (by rfl) ⟨230852, by rfl⟩ : syracuseStep 1231213 = 461705) (by norm_num)
theorem B1296773 : Blo 574812 1296773 := bbase (se 4 (by rfl) ⟨121572, by rfl⟩ : syracuseStep 1296773 = 243145) (by norm_num)
theorem B1296845 : Blo 574812 1296845 := bbase (se 3 (by rfl) ⟨243158, by rfl⟩ : syracuseStep 1296845 = 486317) (by norm_num)
theorem B1460693 : Blo 574812 1460693 := bbase (se 7 (by rfl) ⟨17117, by rfl⟩ : syracuseStep 1460693 = 34235) (by norm_num)
theorem B1952261 : Blo 574812 1952261 := bbase (se 4 (by rfl) ⟨183024, by rfl⟩ : syracuseStep 1952261 = 366049) (by norm_num)
theorem B1296917 : Blo 574812 1296917 := bbase (se 6 (by rfl) ⟨30396, by rfl⟩ : syracuseStep 1296917 = 60793) (by norm_num)
theorem B5556757 : Blo 574812 5556757 := bbase (se 6 (by rfl) ⟨130236, by rfl⟩ : syracuseStep 5556757 = 260473) (by norm_num)
theorem B1296989 : Blo 574812 1296989 := bbase (se 3 (by rfl) ⟨243185, by rfl⟩ : syracuseStep 1296989 = 486371) (by norm_num)
theorem B1297061 : Blo 574812 1297061 := bbase (se 4 (by rfl) ⟨121599, by rfl⟩ : syracuseStep 1297061 = 243199) (by norm_num)
theorem B1297133 : Blo 574812 1297133 := bbase (se 3 (by rfl) ⟨243212, by rfl⟩ : syracuseStep 1297133 = 486425) (by norm_num)
theorem B2771749 : Blo 574812 2771749 := bbase (se 4 (by rfl) ⟨259851, by rfl⟩ : syracuseStep 2771749 = 519703) (by norm_num)
theorem B1461037 : Blo 574812 1461037 := bbase (se 3 (by rfl) ⟨273944, by rfl⟩ : syracuseStep 1461037 = 547889) (by norm_num)
theorem B1297205 : Blo 574812 1297205 := bbase (se 5 (by rfl) ⟨60806, by rfl⟩ : syracuseStep 1297205 = 121613) (by norm_num)
theorem B3689333 : Blo 574812 3689333 := bbase (se 5 (by rfl) ⟨172937, by rfl⟩ : syracuseStep 3689333 = 345875) (by norm_num)
theorem B1297277 : Blo 574812 1297277 := bbase (se 3 (by rfl) ⟨243239, by rfl⟩ : syracuseStep 1297277 = 486479) (by norm_num)
theorem B1461149 : Blo 574812 1461149 := bbase (se 3 (by rfl) ⟨273965, by rfl⟩ : syracuseStep 1461149 = 547931) (by norm_num)
theorem B1952693 : Blo 574812 1952693 := bbase (se 5 (by rfl) ⟨91532, by rfl⟩ : syracuseStep 1952693 = 183065) (by norm_num)
theorem B1297349 : Blo 574812 1297349 := bbase (se 4 (by rfl) ⟨121626, by rfl⟩ : syracuseStep 1297349 = 243253) (by norm_num)
theorem B1166309 : Blo 574812 1166309 := bbase (se 4 (by rfl) ⟨109341, by rfl⟩ : syracuseStep 1166309 = 218683) (by norm_num)
theorem B1297421 : Blo 574812 1297421 := bbase (se 3 (by rfl) ⟨243266, by rfl⟩ : syracuseStep 1297421 = 486533) (by norm_num)
theorem B1297493 : Blo 574812 1297493 := bbase (se 8 (by rfl) ⟨7602, by rfl⟩ : syracuseStep 1297493 = 15205) (by norm_num)
theorem B1461341 : Blo 574812 1461341 := bbase (se 3 (by rfl) ⟨274001, by rfl⟩ : syracuseStep 1461341 = 548003) (by norm_num)
theorem B1297565 : Blo 574812 1297565 := bbase (se 3 (by rfl) ⟨243293, by rfl⟩ : syracuseStep 1297565 = 486587) (by norm_num)
theorem B1297637 : Blo 574812 1297637 := bbase (se 4 (by rfl) ⟨121653, by rfl⟩ : syracuseStep 1297637 = 243307) (by norm_num)
theorem B1232101 : Blo 574812 1232101 := bbase (se 4 (by rfl) ⟨115509, by rfl⟩ : syracuseStep 1232101 = 231019) (by norm_num)
theorem B642325 : Blo 574812 642325 := bbase (se 6 (by rfl) ⟨15054, by rfl⟩ : syracuseStep 642325 = 30109) (by norm_num)
theorem B1297709 : Blo 574812 1297709 := bbase (se 3 (by rfl) ⟨243320, by rfl⟩ : syracuseStep 1297709 = 486641) (by norm_num)
theorem B4934965 : Blo 574812 4934965 := bbase (se 5 (by rfl) ⟨231326, by rfl⟩ : syracuseStep 4934965 = 462653) (by norm_num)
theorem B970069 : Blo 574812 970069 := bbase (se 11 (by rfl) ⟨710, by rfl⟩ : syracuseStep 970069 = 1421) (by norm_num)
theorem B1953125 : Blo 574812 1953125 := bbase (se 4 (by rfl) ⟨183105, by rfl⟩ : syracuseStep 1953125 = 366211) (by norm_num)
theorem B1297781 : Blo 574812 1297781 := bbase (se 5 (by rfl) ⟨60833, by rfl⟩ : syracuseStep 1297781 = 121667) (by norm_num)
theorem B2182565 : Blo 574812 2182565 := bbase (se 4 (by rfl) ⟨204615, by rfl⟩ : syracuseStep 2182565 = 409231) (by norm_num)
theorem B970157 : Blo 574812 970157 := bbase (se 3 (by rfl) ⟨181904, by rfl⟩ : syracuseStep 970157 = 363809) (by norm_num)
theorem B1461685 : Blo 574812 1461685 := bbase (se 5 (by rfl) ⟨68516, by rfl⟩ : syracuseStep 1461685 = 137033) (by norm_num)
theorem B1297853 : Blo 574812 1297853 := bbase (se 3 (by rfl) ⟨243347, by rfl⟩ : syracuseStep 1297853 = 486695) (by norm_num)
theorem B1297925 : Blo 574812 1297925 := bbase (se 4 (by rfl) ⟨121680, by rfl⟩ : syracuseStep 1297925 = 243361) (by norm_num)
theorem B1461797 : Blo 574812 1461797 := bbase (se 4 (by rfl) ⟨137043, by rfl⟩ : syracuseStep 1461797 = 274087) (by norm_num)
theorem B970285 : Blo 574812 970285 := bbase (se 3 (by rfl) ⟨181928, by rfl⟩ : syracuseStep 970285 = 363857) (by norm_num)
theorem B4574773 : Blo 574812 4574773 := bbase (se 5 (by rfl) ⟨214442, by rfl⟩ : syracuseStep 4574773 = 428885) (by norm_num)
theorem B1297997 : Blo 574812 1297997 := bbase (se 3 (by rfl) ⟨243374, by rfl⟩ : syracuseStep 1297997 = 486749) (by norm_num)
theorem B1560181 : Blo 574812 1560181 := bbase (se 5 (by rfl) ⟨73133, by rfl⟩ : syracuseStep 1560181 = 146267) (by norm_num)
theorem B970373 : Blo 574812 970373 := bbase (se 4 (by rfl) ⟨90972, by rfl⟩ : syracuseStep 970373 = 181945) (by norm_num)
theorem B1298069 : Blo 574812 1298069 := bbase (se 6 (by rfl) ⟨30423, by rfl⟩ : syracuseStep 1298069 = 60847) (by norm_num)
theorem B1232597 : Blo 574812 1232597 := bbase (se 7 (by rfl) ⟨14444, by rfl⟩ : syracuseStep 1232597 = 28889) (by norm_num)
theorem B1298141 : Blo 574812 1298141 := bbase (se 3 (by rfl) ⟨243401, by rfl⟩ : syracuseStep 1298141 = 486803) (by norm_num)
theorem B1461989 : Blo 574812 1461989 := bbase (se 4 (by rfl) ⟨137061, by rfl⟩ : syracuseStep 1461989 = 274123) (by norm_num)
theorem B970501 : Blo 574812 970501 := bbase (se 4 (by rfl) ⟨90984, by rfl⟩ : syracuseStep 970501 = 181969) (by norm_num)
theorem B741133 : Blo 574812 741133 := bbase (se 3 (by rfl) ⟨138962, by rfl⟩ : syracuseStep 741133 = 277925) (by norm_num)
theorem B1298213 : Blo 574812 1298213 := bbase (se 4 (by rfl) ⟨121707, by rfl⟩ : syracuseStep 1298213 = 243415) (by norm_num)
theorem B970589 : Blo 574812 970589 := bbase (se 3 (by rfl) ⟨181985, by rfl⟩ : syracuseStep 970589 = 363971) (by norm_num)
theorem B1298285 : Blo 574812 1298285 := bbase (se 3 (by rfl) ⟨243428, by rfl⟩ : syracuseStep 1298285 = 486857) (by norm_num)
theorem B1298357 : Blo 574812 1298357 := bbase (se 5 (by rfl) ⟨60860, by rfl⟩ : syracuseStep 1298357 = 121721) (by norm_num)
theorem B970717 : Blo 574812 970717 := bbase (se 3 (by rfl) ⟨182009, by rfl⟩ : syracuseStep 970717 = 364019) (by norm_num)
theorem B1298429 : Blo 574812 1298429 := bbase (se 3 (by rfl) ⟨243455, by rfl⟩ : syracuseStep 1298429 = 486911) (by norm_num)
theorem B970805 : Blo 574812 970805 := bbase (se 5 (by rfl) ⟨45506, by rfl⟩ : syracuseStep 970805 = 91013) (by norm_num)
theorem B1462333 : Blo 574812 1462333 := bbase (se 3 (by rfl) ⟨274187, by rfl⟩ : syracuseStep 1462333 = 548375) (by norm_num)
theorem B1298501 : Blo 574812 1298501 := bbase (se 4 (by rfl) ⟨121734, by rfl⟩ : syracuseStep 1298501 = 243469) (by norm_num)
theorem B1298573 : Blo 574812 1298573 := bbase (se 3 (by rfl) ⟨243482, by rfl⟩ : syracuseStep 1298573 = 486965) (by norm_num)
theorem B1462445 : Blo 574812 1462445 := bbase (se 3 (by rfl) ⟨274208, by rfl⟩ : syracuseStep 1462445 = 548417) (by norm_num)
theorem B970933 : Blo 574812 970933 := bbase (se 5 (by rfl) ⟨45512, by rfl⟩ : syracuseStep 970933 = 91025) (by norm_num)
theorem B1298645 : Blo 574812 1298645 := bbase (se 7 (by rfl) ⟨15218, by rfl⟩ : syracuseStep 1298645 = 30437) (by norm_num)
theorem B971021 : Blo 574812 971021 := bbase (se 3 (by rfl) ⟨182066, by rfl⟩ : syracuseStep 971021 = 364133) (by norm_num)
theorem B1298717 : Blo 574812 1298717 := bbase (se 3 (by rfl) ⟨243509, by rfl⟩ : syracuseStep 1298717 = 487019) (by norm_num)
theorem B1167653 : Blo 574812 1167653 := bbase (se 4 (by rfl) ⟨109467, by rfl⟩ : syracuseStep 1167653 = 218935) (by norm_num)
theorem B1298789 : Blo 574812 1298789 := bbase (se 4 (by rfl) ⟨121761, by rfl⟩ : syracuseStep 1298789 = 243523) (by norm_num)
theorem B1462637 : Blo 574812 1462637 := bbase (se 3 (by rfl) ⟨274244, by rfl⟩ : syracuseStep 1462637 = 548489) (by norm_num)
theorem B971149 : Blo 574812 971149 := bbase (se 3 (by rfl) ⟨182090, by rfl⟩ : syracuseStep 971149 = 364181) (by norm_num)
theorem B1298861 : Blo 574812 1298861 := bbase (se 3 (by rfl) ⟨243536, by rfl⟩ : syracuseStep 1298861 = 487073) (by norm_num)
theorem B971237 : Blo 574812 971237 := bbase (se 4 (by rfl) ⟨91053, by rfl⟩ : syracuseStep 971237 = 182107) (by norm_num)
theorem B1298933 : Blo 574812 1298933 := bbase (se 5 (by rfl) ⟨60887, by rfl⟩ : syracuseStep 1298933 = 121775) (by norm_num)
theorem B1233461 : Blo 574812 1233461 := bbase (se 5 (by rfl) ⟨57818, by rfl⟩ : syracuseStep 1233461 = 115637) (by norm_num)
theorem B1299005 : Blo 574812 1299005 := bbase (se 3 (by rfl) ⟨243563, by rfl⟩ : syracuseStep 1299005 = 487127) (by norm_num)
theorem B15782485 : Blo 574812 15782485 := bbase (se 8 (by rfl) ⟨92475, by rfl⟩ : syracuseStep 15782485 = 184951) (by norm_num)
theorem B971365 : Blo 574812 971365 := bbase (se 4 (by rfl) ⟨91065, by rfl⟩ : syracuseStep 971365 = 182131) (by norm_num)
theorem B1299077 : Blo 574812 1299077 := bbase (se 4 (by rfl) ⟨121788, by rfl⟩ : syracuseStep 1299077 = 243577) (by norm_num)
theorem B971453 : Blo 574812 971453 := bbase (se 3 (by rfl) ⟨182147, by rfl⟩ : syracuseStep 971453 = 364295) (by norm_num)
theorem B1233605 : Blo 574812 1233605 := bbase (se 4 (by rfl) ⟨115650, by rfl⟩ : syracuseStep 1233605 = 231301) (by norm_num)
theorem B1462981 : Blo 574812 1462981 := bbase (se 4 (by rfl) ⟨137154, by rfl⟩ : syracuseStep 1462981 = 274309) (by norm_num)
theorem B1299149 : Blo 574812 1299149 := bbase (se 3 (by rfl) ⟨243590, by rfl⟩ : syracuseStep 1299149 = 487181) (by norm_num)
theorem B1168141 : Blo 574812 1168141 := bbase (se 3 (by rfl) ⟨219026, by rfl⟩ : syracuseStep 1168141 = 438053) (by norm_num)
theorem B1299221 : Blo 574812 1299221 := bbase (se 6 (by rfl) ⟨30450, by rfl⟩ : syracuseStep 1299221 = 60901) (by norm_num)
theorem B1463093 : Blo 574812 1463093 := bbase (se 5 (by rfl) ⟨68582, by rfl⟩ : syracuseStep 1463093 = 137165) (by norm_num)
theorem B971581 : Blo 574812 971581 := bbase (se 3 (by rfl) ⟨182171, by rfl⟩ : syracuseStep 971581 = 364343) (by norm_num)
theorem B1299293 : Blo 574812 1299293 := bbase (se 3 (by rfl) ⟨243617, by rfl⟩ : syracuseStep 1299293 = 487235) (by norm_num)
theorem B971669 : Blo 574812 971669 := bbase (se 6 (by rfl) ⟨22773, by rfl⟩ : syracuseStep 971669 = 45547) (by norm_num)
theorem B1299365 : Blo 574812 1299365 := bbase (se 4 (by rfl) ⟨121815, by rfl⟩ : syracuseStep 1299365 = 243631) (by norm_num)
theorem B1299437 : Blo 574812 1299437 := bbase (se 3 (by rfl) ⟨243644, by rfl⟩ : syracuseStep 1299437 = 487289) (by norm_num)
theorem B1463285 : Blo 574812 1463285 := bbase (se 5 (by rfl) ⟨68591, by rfl⟩ : syracuseStep 1463285 = 137183) (by norm_num)
theorem B971797 : Blo 574812 971797 := bbase (se 6 (by rfl) ⟨22776, by rfl⟩ : syracuseStep 971797 = 45553) (by norm_num)
theorem B1299509 : Blo 574812 1299509 := bbase (se 5 (by rfl) ⟨60914, by rfl⟩ : syracuseStep 1299509 = 121829) (by norm_num)
theorem B971885 : Blo 574812 971885 := bbase (se 3 (by rfl) ⟨182228, by rfl⟩ : syracuseStep 971885 = 364457) (by norm_num)
theorem B1299581 : Blo 574812 1299581 := bbase (se 3 (by rfl) ⟨243671, by rfl⟩ : syracuseStep 1299581 = 487343) (by norm_num)
theorem B1299653 : Blo 574812 1299653 := bbase (se 4 (by rfl) ⟨121842, by rfl⟩ : syracuseStep 1299653 = 243685) (by norm_num)
theorem B972013 : Blo 574812 972013 := bbase (se 3 (by rfl) ⟨182252, by rfl⟩ : syracuseStep 972013 = 364505) (by norm_num)
theorem B4936949 : Blo 574812 4936949 := bbase (se 5 (by rfl) ⟨231419, by rfl⟩ : syracuseStep 4936949 = 462839) (by norm_num)
theorem B1299725 : Blo 574812 1299725 := bbase (se 3 (by rfl) ⟨243698, by rfl⟩ : syracuseStep 1299725 = 487397) (by norm_num)
theorem B3855637 : Blo 574812 3855637 := bbase (se 6 (by rfl) ⟨90366, by rfl⟩ : syracuseStep 3855637 = 180733) (by norm_num)
theorem B972101 : Blo 574812 972101 := bbase (se 4 (by rfl) ⟨91134, by rfl⟩ : syracuseStep 972101 = 182269) (by norm_num)
theorem B1463629 : Blo 574812 1463629 := bbase (se 3 (by rfl) ⟨274430, by rfl⟩ : syracuseStep 1463629 = 548861) (by norm_num)
theorem B1299797 : Blo 574812 1299797 := bbase (se 15 (by rfl) ⟨59, by rfl⟩ : syracuseStep 1299797 = 119) (by norm_num)
theorem B1299869 : Blo 574812 1299869 := bbase (se 3 (by rfl) ⟨243725, by rfl⟩ : syracuseStep 1299869 = 487451) (by norm_num)
theorem B1168813 : Blo 574812 1168813 := bbase (se 3 (by rfl) ⟨219152, by rfl⟩ : syracuseStep 1168813 = 438305) (by norm_num)
theorem B1234349 : Blo 574812 1234349 := bbase (se 3 (by rfl) ⟨231440, by rfl⟩ : syracuseStep 1234349 = 462881) (by norm_num)
theorem B1463741 : Blo 574812 1463741 := bbase (se 3 (by rfl) ⟨274451, by rfl⟩ : syracuseStep 1463741 = 548903) (by norm_num)
theorem B972229 : Blo 574812 972229 := bbase (se 4 (by rfl) ⟨91146, by rfl⟩ : syracuseStep 972229 = 182293) (by norm_num)
theorem B2184677 : Blo 574812 2184677 := bbase (se 4 (by rfl) ⟨204813, by rfl⟩ : syracuseStep 2184677 = 409627) (by norm_num)
theorem B1299941 : Blo 574812 1299941 := bbase (se 4 (by rfl) ⟨121869, by rfl⟩ : syracuseStep 1299941 = 243739) (by norm_num)
theorem B972317 : Blo 574812 972317 := bbase (se 3 (by rfl) ⟨182309, by rfl⟩ : syracuseStep 972317 = 364619) (by norm_num)
theorem B1300013 : Blo 574812 1300013 := bbase (se 3 (by rfl) ⟨243752, by rfl⟩ : syracuseStep 1300013 = 487505) (by norm_num)
theorem B874037 : Blo 574812 874037 := bbase (se 5 (by rfl) ⟨40970, by rfl⟩ : syracuseStep 874037 = 81941) (by norm_num)
theorem B1300085 : Blo 574812 1300085 := bbase (se 5 (by rfl) ⟨60941, by rfl⟩ : syracuseStep 1300085 = 121883) (by norm_num)
theorem B1463933 : Blo 574812 1463933 := bbase (se 3 (by rfl) ⟨274487, by rfl⟩ : syracuseStep 1463933 = 548975) (by norm_num)
theorem B972445 : Blo 574812 972445 := bbase (se 3 (by rfl) ⟨182333, by rfl⟩ : syracuseStep 972445 = 364667) (by norm_num)
theorem B1300157 : Blo 574812 1300157 := bbase (se 3 (by rfl) ⟨243779, by rfl⟩ : syracuseStep 1300157 = 487559) (by norm_num)
theorem B972533 : Blo 574812 972533 := bbase (se 5 (by rfl) ⟨45587, by rfl⟩ : syracuseStep 972533 = 91175) (by norm_num)
theorem B2184965 : Blo 574812 2184965 := bbase (se 4 (by rfl) ⟨204840, by rfl⟩ : syracuseStep 2184965 = 409681) (by norm_num)
theorem B2807557 : Blo 574812 2807557 := bbase (se 4 (by rfl) ⟨263208, by rfl⟩ : syracuseStep 2807557 = 526417) (by norm_num)
theorem B1300229 : Blo 574812 1300229 := bbase (se 4 (by rfl) ⟨121896, by rfl⟩ : syracuseStep 1300229 = 243793) (by norm_num)
theorem B1300301 : Blo 574812 1300301 := bbase (se 3 (by rfl) ⟨243806, by rfl⟩ : syracuseStep 1300301 = 487613) (by norm_num)
theorem B972661 : Blo 574812 972661 := bbase (se 5 (by rfl) ⟨45593, by rfl⟩ : syracuseStep 972661 = 91187) (by norm_num)
theorem B1300373 : Blo 574812 1300373 := bbase (se 6 (by rfl) ⟨30477, by rfl⟩ : syracuseStep 1300373 = 60955) (by norm_num)
theorem B1038253 : Blo 574812 1038253 := bbase (se 3 (by rfl) ⟨194672, by rfl⟩ : syracuseStep 1038253 = 389345) (by norm_num)
theorem B972749 : Blo 574812 972749 := bbase (se 3 (by rfl) ⟨182390, by rfl⟩ : syracuseStep 972749 = 364781) (by norm_num)
theorem B1464277 : Blo 574812 1464277 := bbase (se 7 (by rfl) ⟨17159, by rfl⟩ : syracuseStep 1464277 = 34319) (by norm_num)
theorem B1300445 : Blo 574812 1300445 := bbase (se 3 (by rfl) ⟨243833, by rfl⟩ : syracuseStep 1300445 = 487667) (by norm_num)
theorem B1038317 : Blo 574812 1038317 := bbase (se 3 (by rfl) ⟨194684, by rfl⟩ : syracuseStep 1038317 = 389369) (by norm_num)
theorem B5527541 : Blo 574812 5527541 := bbase (se 5 (by rfl) ⟨259103, by rfl⟩ : syracuseStep 5527541 = 518207) (by norm_num)
theorem B1169405 : Blo 574812 1169405 := bbase (se 3 (by rfl) ⟨219263, by rfl⟩ : syracuseStep 1169405 = 438527) (by norm_num)
theorem B1300517 : Blo 574812 1300517 := bbase (se 4 (by rfl) ⟨121923, by rfl⟩ : syracuseStep 1300517 = 243847) (by norm_num)
theorem B1464389 : Blo 574812 1464389 := bbase (se 4 (by rfl) ⟨137286, by rfl⟩ : syracuseStep 1464389 = 274573) (by norm_num)
theorem B972877 : Blo 574812 972877 := bbase (se 3 (by rfl) ⟨182414, by rfl⟩ : syracuseStep 972877 = 364829) (by norm_num)
theorem B1300589 : Blo 574812 1300589 := bbase (se 3 (by rfl) ⟨243860, by rfl⟩ : syracuseStep 1300589 = 487721) (by norm_num)
theorem B1235101 : Blo 574812 1235101 := bbase (se 3 (by rfl) ⟨231581, by rfl⟩ : syracuseStep 1235101 = 463163) (by norm_num)
theorem B972965 : Blo 574812 972965 := bbase (se 4 (by rfl) ⟨91215, by rfl⟩ : syracuseStep 972965 = 182431) (by norm_num)
theorem B1300661 : Blo 574812 1300661 := bbase (se 5 (by rfl) ⟨60968, by rfl⟩ : syracuseStep 1300661 = 121937) (by norm_num)
theorem B1300733 : Blo 574812 1300733 := bbase (se 3 (by rfl) ⟨243887, by rfl⟩ : syracuseStep 1300733 = 487775) (by norm_num)
theorem B1464581 : Blo 574812 1464581 := bbase (se 4 (by rfl) ⟨137304, by rfl⟩ : syracuseStep 1464581 = 274609) (by norm_num)
theorem B973093 : Blo 574812 973093 := bbase (se 4 (by rfl) ⟨91227, by rfl⟩ : syracuseStep 973093 = 182455) (by norm_num)
theorem B1235245 : Blo 574812 1235245 := bbase (se 3 (by rfl) ⟨231608, by rfl⟩ : syracuseStep 1235245 = 463217) (by norm_num)
theorem B1300805 : Blo 574812 1300805 := bbase (se 4 (by rfl) ⟨121950, by rfl⟩ : syracuseStep 1300805 = 243901) (by norm_num)
theorem B973181 : Blo 574812 973181 := bbase (se 3 (by rfl) ⟨182471, by rfl⟩ : syracuseStep 973181 = 364943) (by norm_num)
theorem B1300877 : Blo 574812 1300877 := bbase (se 3 (by rfl) ⟨243914, by rfl⟩ : syracuseStep 1300877 = 487829) (by norm_num)
theorem B5560757 : Blo 574812 5560757 := bbase (se 5 (by rfl) ⟨260660, by rfl⟩ : syracuseStep 5560757 = 521321) (by norm_num)
theorem B1300949 : Blo 574812 1300949 := bbase (se 7 (by rfl) ⟨15245, by rfl⟩ : syracuseStep 1300949 = 30491) (by norm_num)
theorem B875005 : Blo 574812 875005 := bbase (se 3 (by rfl) ⟨164063, by rfl⟩ : syracuseStep 875005 = 328127) (by norm_num)
theorem B973309 : Blo 574812 973309 := bbase (se 3 (by rfl) ⟨182495, by rfl⟩ : syracuseStep 973309 = 364991) (by norm_num)
theorem B2808341 : Blo 574812 2808341 := bbase (se 6 (by rfl) ⟨65820, by rfl⟩ : syracuseStep 2808341 = 131641) (by norm_num)
theorem B1301021 : Blo 574812 1301021 := bbase (se 3 (by rfl) ⟨243941, by rfl⟩ : syracuseStep 1301021 = 487883) (by norm_num)
theorem B973397 : Blo 574812 973397 := bbase (se 8 (by rfl) ⟨5703, by rfl⟩ : syracuseStep 973397 = 11407) (by norm_num)
theorem B1464925 : Blo 574812 1464925 := bbase (se 3 (by rfl) ⟨274673, by rfl⟩ : syracuseStep 1464925 = 549347) (by norm_num)
theorem B2775653 : Blo 574812 2775653 := bbase (se 4 (by rfl) ⟨260217, by rfl⟩ : syracuseStep 2775653 = 520435) (by norm_num)
theorem B1301093 : Blo 574812 1301093 := bbase (se 4 (by rfl) ⟨121977, by rfl⟩ : syracuseStep 1301093 = 243955) (by norm_num)
theorem B1235621 : Blo 574812 1235621 := bbase (se 4 (by rfl) ⟨115839, by rfl⟩ : syracuseStep 1235621 = 231679) (by norm_num)
theorem B1301165 : Blo 574812 1301165 := bbase (se 3 (by rfl) ⟨243968, by rfl⟩ : syracuseStep 1301165 = 487937) (by norm_num)
theorem B1465037 : Blo 574812 1465037 := bbase (se 3 (by rfl) ⟨274694, by rfl⟩ : syracuseStep 1465037 = 549389) (by norm_num)
theorem B1039061 : Blo 574812 1039061 := bbase (se 7 (by rfl) ⟨12176, by rfl⟩ : syracuseStep 1039061 = 24353) (by norm_num)
theorem B973525 : Blo 574812 973525 := bbase (se 7 (by rfl) ⟨11408, by rfl⟩ : syracuseStep 973525 = 22817) (by norm_num)
theorem B1301237 : Blo 574812 1301237 := bbase (se 5 (by rfl) ⟨60995, by rfl⟩ : syracuseStep 1301237 = 121991) (by norm_num)
theorem B973613 : Blo 574812 973613 := bbase (se 3 (by rfl) ⟨182552, by rfl⟩ : syracuseStep 973613 = 365105) (by norm_num)
theorem B1301309 : Blo 574812 1301309 := bbase (se 3 (by rfl) ⟨243995, by rfl⟩ : syracuseStep 1301309 = 487991) (by norm_num)
theorem B1760069 : Blo 574812 1760069 := bbase (se 4 (by rfl) ⟨165006, by rfl⟩ : syracuseStep 1760069 = 330013) (by norm_num)
theorem B1301381 : Blo 574812 1301381 := bbase (se 4 (by rfl) ⟨122004, by rfl⟩ : syracuseStep 1301381 = 244009) (by norm_num)
theorem B2186149 : Blo 574812 2186149 := bbase (se 4 (by rfl) ⟨204951, by rfl⟩ : syracuseStep 2186149 = 409903) (by norm_num)
theorem B973741 : Blo 574812 973741 := bbase (se 3 (by rfl) ⟨182576, by rfl⟩ : syracuseStep 973741 = 365153) (by norm_num)
theorem B1301453 : Blo 574812 1301453 := bbase (se 3 (by rfl) ⟨244022, by rfl⟩ : syracuseStep 1301453 = 488045) (by norm_num)
theorem B1039349 : Blo 574812 1039349 := bbase (se 5 (by rfl) ⟨48719, by rfl⟩ : syracuseStep 1039349 = 97439) (by norm_num)
theorem B973829 : Blo 574812 973829 := bbase (se 4 (by rfl) ⟨91296, by rfl⟩ : syracuseStep 973829 = 182593) (by norm_num)
theorem B1301525 : Blo 574812 1301525 := bbase (se 6 (by rfl) ⟨30504, by rfl⟩ : syracuseStep 1301525 = 61009) (by norm_num)
theorem B1235989 : Blo 574812 1235989 := bbase (se 6 (by rfl) ⟨28968, by rfl⟩ : syracuseStep 1235989 = 57937) (by norm_num)
theorem B1301597 : Blo 574812 1301597 := bbase (se 3 (by rfl) ⟨244049, by rfl⟩ : syracuseStep 1301597 = 488099) (by norm_num)
theorem B1170541 : Blo 574812 1170541 := bbase (se 3 (by rfl) ⟨219476, by rfl⟩ : syracuseStep 1170541 = 438953) (by norm_num)
theorem B973957 : Blo 574812 973957 := bbase (se 4 (by rfl) ⟨91308, by rfl⟩ : syracuseStep 973957 = 182617) (by norm_num)
theorem B1301669 : Blo 574812 1301669 := bbase (se 4 (by rfl) ⟨122031, by rfl⟩ : syracuseStep 1301669 = 244063) (by norm_num)
theorem B2186453 : Blo 574812 2186453 := bbase (se 7 (by rfl) ⟨25622, by rfl⟩ : syracuseStep 2186453 = 51245) (by norm_num)
theorem B974045 : Blo 574812 974045 := bbase (se 3 (by rfl) ⟨182633, by rfl⟩ : syracuseStep 974045 = 365267) (by norm_num)
theorem B1301741 : Blo 574812 1301741 := bbase (se 3 (by rfl) ⟨244076, by rfl⟩ : syracuseStep 1301741 = 488153) (by norm_num)
theorem B875765 : Blo 574812 875765 := bbase (se 5 (by rfl) ⟨41051, by rfl⟩ : syracuseStep 875765 = 82103) (by norm_num)
theorem B1301813 : Blo 574812 1301813 := bbase (se 5 (by rfl) ⟨61022, by rfl⟩ : syracuseStep 1301813 = 122045) (by norm_num)
theorem B974173 : Blo 574812 974173 := bbase (se 3 (by rfl) ⟨182657, by rfl⟩ : syracuseStep 974173 = 365315) (by norm_num)
theorem B777581 : Blo 574812 777581 := bbase (se 3 (by rfl) ⟨145796, by rfl⟩ : syracuseStep 777581 = 291593) (by norm_num)
theorem B1301885 : Blo 574812 1301885 := bbase (se 3 (by rfl) ⟨244103, by rfl⟩ : syracuseStep 1301885 = 488207) (by norm_num)
theorem B974261 : Blo 574812 974261 := bbase (se 5 (by rfl) ⟨45668, by rfl⟩ : syracuseStep 974261 = 91337) (by norm_num)
theorem B1301957 : Blo 574812 1301957 := bbase (se 4 (by rfl) ⟨122058, by rfl⟩ : syracuseStep 1301957 = 244117) (by norm_num)
theorem B1302029 : Blo 574812 1302029 := bbase (se 3 (by rfl) ⟨244130, by rfl⟩ : syracuseStep 1302029 = 488261) (by norm_num)
theorem B1564181 : Blo 574812 1564181 := bbase (se 6 (by rfl) ⟨36660, by rfl⟩ : syracuseStep 1564181 = 73321) (by norm_num)
theorem B646681 : Blo 574812 646681 := bbase (se 2 (by rfl) ⟨242505, by rfl⟩ : syracuseStep 646681 = 485011) (by norm_num)
theorem B4382261 : Blo 574812 4382261 := bbase (se 5 (by rfl) ⟨205418, by rfl⟩ : syracuseStep 4382261 = 410837) (by norm_num)
theorem B974389 : Blo 574812 974389 := bbase (se 5 (by rfl) ⟨45674, by rfl⟩ : syracuseStep 974389 = 91349) (by norm_num)
theorem B646717 : Blo 574812 646717 := bbase (se 3 (by rfl) ⟨121259, by rfl⟩ : syracuseStep 646717 = 242519) (by norm_num)
theorem B1302101 : Blo 574812 1302101 := bbase (se 8 (by rfl) ⟨7629, by rfl⟩ : syracuseStep 1302101 = 15259) (by norm_num)
theorem B646753 : Blo 574812 646753 := bbase (se 2 (by rfl) ⟨242532, by rfl⟩ : syracuseStep 646753 = 485065) (by norm_num)
theorem B1662565 : Blo 574812 1662565 := bbase (se 4 (by rfl) ⟨155865, by rfl⟩ : syracuseStep 1662565 = 311731) (by norm_num)
theorem B2842229 : Blo 574812 2842229 := bbase (se 5 (by rfl) ⟨133229, by rfl⟩ : syracuseStep 2842229 = 266459) (by norm_num)
theorem B646789 : Blo 574812 646789 := bbase (se 4 (by rfl) ⟨60636, by rfl⟩ : syracuseStep 646789 = 121273) (by norm_num)
theorem B974477 : Blo 574812 974477 := bbase (se 3 (by rfl) ⟨182714, by rfl⟩ : syracuseStep 974477 = 365429) (by norm_num)
theorem B1564309 : Blo 574812 1564309 := bbase (se 6 (by rfl) ⟨36663, by rfl⟩ : syracuseStep 1564309 = 73327) (by norm_num)
theorem B1302173 : Blo 574812 1302173 := bbase (se 3 (by rfl) ⟨244157, by rfl⟩ : syracuseStep 1302173 = 488315) (by norm_num)
theorem B646825 : Blo 574812 646825 := bbase (se 2 (by rfl) ⟨242559, by rfl⟩ : syracuseStep 646825 = 485119) (by norm_num)
theorem B876221 : Blo 574812 876221 := bbase (se 3 (by rfl) ⟨164291, by rfl⟩ : syracuseStep 876221 = 328583) (by norm_num)
theorem B646861 : Blo 574812 646861 := bbase (se 3 (by rfl) ⟨121286, by rfl⟩ : syracuseStep 646861 = 242573) (by norm_num)
theorem B1302245 : Blo 574812 1302245 := bbase (se 4 (by rfl) ⟨122085, by rfl⟩ : syracuseStep 1302245 = 244171) (by norm_num)
theorem B646897 : Blo 574812 646897 := bbase (se 2 (by rfl) ⟨242586, by rfl⟩ : syracuseStep 646897 = 485173) (by norm_num)
theorem B974605 : Blo 574812 974605 := bbase (se 3 (by rfl) ⟨182738, by rfl⟩ : syracuseStep 974605 = 365477) (by norm_num)
theorem B646933 : Blo 574812 646933 := bbase (se 6 (by rfl) ⟨15162, by rfl⟩ : syracuseStep 646933 = 30325) (by norm_num)
theorem B1302317 : Blo 574812 1302317 := bbase (se 3 (by rfl) ⟨244184, by rfl⟩ : syracuseStep 1302317 = 488369) (by norm_num)
theorem B646969 : Blo 574812 646969 := bbase (se 2 (by rfl) ⟨242613, by rfl⟩ : syracuseStep 646969 = 485227) (by norm_num)
theorem B876349 : Blo 574812 876349 := bbase (se 3 (by rfl) ⟨164315, by rfl⟩ : syracuseStep 876349 = 328631) (by norm_num)
theorem B647005 : Blo 574812 647005 := bbase (se 3 (by rfl) ⟨121313, by rfl⟩ : syracuseStep 647005 = 242627) (by norm_num)
theorem B974693 : Blo 574812 974693 := bbase (se 4 (by rfl) ⟨91377, by rfl⟩ : syracuseStep 974693 = 182755) (by norm_num)
theorem B647041 : Blo 574812 647041 := bbase (se 2 (by rfl) ⟨242640, by rfl⟩ : syracuseStep 647041 = 485281) (by norm_num)
theorem B647077 : Blo 574812 647077 := bbase (se 4 (by rfl) ⟨60663, by rfl⟩ : syracuseStep 647077 = 121327) (by norm_num)
theorem B647113 : Blo 574812 647113 := bbase (se 2 (by rfl) ⟨242667, by rfl⟩ : syracuseStep 647113 = 485335) (by norm_num)
theorem B974821 : Blo 574812 974821 := bbase (se 4 (by rfl) ⟨91389, by rfl⟩ : syracuseStep 974821 = 182779) (by norm_num)
theorem B647149 : Blo 574812 647149 := bbase (se 3 (by rfl) ⟨121340, by rfl⟩ : syracuseStep 647149 = 242681) (by norm_num)
theorem B647185 : Blo 574812 647185 := bbase (se 2 (by rfl) ⟨242694, by rfl⟩ : syracuseStep 647185 = 485389) (by norm_num)
theorem B647221 : Blo 574812 647221 := bbase (se 5 (by rfl) ⟨30338, by rfl⟩ : syracuseStep 647221 = 60677) (by norm_num)
theorem B974909 : Blo 574812 974909 := bbase (se 3 (by rfl) ⟨182795, by rfl⟩ : syracuseStep 974909 = 365591) (by norm_num)
theorem B647257 : Blo 574812 647257 := bbase (se 2 (by rfl) ⟨242721, by rfl⟩ : syracuseStep 647257 = 485443) (by norm_num)
theorem B778349 : Blo 574812 778349 := bbase (se 3 (by rfl) ⟨145940, by rfl⟩ : syracuseStep 778349 = 291881) (by norm_num)
theorem B614513 : Blo 574812 614513 := bbase (se 2 (by rfl) ⟨230442, by rfl⟩ : syracuseStep 614513 = 460885) (by norm_num)
theorem B647293 : Blo 574812 647293 := bbase (se 3 (by rfl) ⟨121367, by rfl⟩ : syracuseStep 647293 = 242735) (by norm_num)
theorem B647329 : Blo 574812 647329 := bbase (se 2 (by rfl) ⟨242748, by rfl⟩ : syracuseStep 647329 = 485497) (by norm_num)
theorem B876725 : Blo 574812 876725 := bbase (se 5 (by rfl) ⟨41096, by rfl⟩ : syracuseStep 876725 = 82193) (by norm_num)
theorem B975037 : Blo 574812 975037 := bbase (se 3 (by rfl) ⟨182819, by rfl⟩ : syracuseStep 975037 = 365639) (by norm_num)
theorem B647365 : Blo 574812 647365 := bbase (se 4 (by rfl) ⟨60690, by rfl⟩ : syracuseStep 647365 = 121381) (by norm_num)
theorem B647401 : Blo 574812 647401 := bbase (se 2 (by rfl) ⟨242775, by rfl⟩ : syracuseStep 647401 = 485551) (by norm_num)
theorem B647437 : Blo 574812 647437 := bbase (se 3 (by rfl) ⟨121394, by rfl⟩ : syracuseStep 647437 = 242789) (by norm_num)
theorem B975125 : Blo 574812 975125 := bbase (se 6 (by rfl) ⟨22854, by rfl⟩ : syracuseStep 975125 = 45709) (by norm_num)
theorem B647473 : Blo 574812 647473 := bbase (se 2 (by rfl) ⟨242802, by rfl⟩ : syracuseStep 647473 = 485605) (by norm_num)
theorem B1663301 : Blo 574812 1663301 := bbase (se 4 (by rfl) ⟨155934, by rfl⟩ : syracuseStep 1663301 = 311869) (by norm_num)
theorem B647509 : Blo 574812 647509 := bbase (se 10 (by rfl) ⟨948, by rfl⟩ : syracuseStep 647509 = 1897) (by norm_num)
theorem B1171805 : Blo 574812 1171805 := bbase (se 3 (by rfl) ⟨219713, by rfl⟩ : syracuseStep 1171805 = 439427) (by norm_num)
theorem B647545 : Blo 574812 647545 := bbase (se 2 (by rfl) ⟨242829, by rfl⟩ : syracuseStep 647545 = 485659) (by norm_num)
theorem B3498389 : Blo 574812 3498389 := bbase (se 6 (by rfl) ⟨81993, by rfl⟩ : syracuseStep 3498389 = 163987) (by norm_num)
theorem B975253 : Blo 574812 975253 := bbase (se 6 (by rfl) ⟨22857, by rfl⟩ : syracuseStep 975253 = 45715) (by norm_num)
theorem B647581 : Blo 574812 647581 := bbase (se 3 (by rfl) ⟨121421, by rfl⟩ : syracuseStep 647581 = 242843) (by norm_num)
theorem B1040797 : Blo 574812 1040797 := bbase (se 3 (by rfl) ⟨195149, by rfl⟩ : syracuseStep 1040797 = 390299) (by norm_num)
theorem B647617 : Blo 574812 647617 := bbase (se 2 (by rfl) ⟨242856, by rfl⟩ : syracuseStep 647617 = 485713) (by norm_num)
theorem B1106389 : Blo 574812 1106389 := bbase (se 7 (by rfl) ⟨12965, by rfl⟩ : syracuseStep 1106389 = 25931) (by norm_num)
theorem B647653 : Blo 574812 647653 := bbase (se 4 (by rfl) ⟨60717, by rfl⟩ : syracuseStep 647653 = 121435) (by norm_num)
theorem B975341 : Blo 574812 975341 := bbase (se 3 (by rfl) ⟨182876, by rfl⟩ : syracuseStep 975341 = 365753) (by norm_num)
theorem B647689 : Blo 574812 647689 := bbase (se 2 (by rfl) ⟨242883, by rfl⟩ : syracuseStep 647689 = 485767) (by norm_num)
theorem B647725 : Blo 574812 647725 := bbase (se 3 (by rfl) ⟨121448, by rfl⟩ : syracuseStep 647725 = 242897) (by norm_num)
theorem B614957 : Blo 574812 614957 := bbase (se 3 (by rfl) ⟨115304, by rfl⟩ : syracuseStep 614957 = 230609) (by norm_num)
theorem B1040941 : Blo 574812 1040941 := bbase (se 3 (by rfl) ⟨195176, by rfl⟩ : syracuseStep 1040941 = 390353) (by norm_num)
theorem B647761 : Blo 574812 647761 := bbase (se 2 (by rfl) ⟨242910, by rfl⟩ : syracuseStep 647761 = 485821) (by norm_num)
theorem B975469 : Blo 574812 975469 := bbase (se 3 (by rfl) ⟨182900, by rfl⟩ : syracuseStep 975469 = 365801) (by norm_num)
theorem B647797 : Blo 574812 647797 := bbase (se 5 (by rfl) ⟨30365, by rfl⟩ : syracuseStep 647797 = 60731) (by norm_num)
theorem B647833 : Blo 574812 647833 := bbase (se 2 (by rfl) ⟨242937, by rfl⟩ : syracuseStep 647833 = 485875) (by norm_num)
theorem B647869 : Blo 574812 647869 := bbase (se 3 (by rfl) ⟨121475, by rfl⟩ : syracuseStep 647869 = 242951) (by norm_num)
theorem B975557 : Blo 574812 975557 := bbase (se 4 (by rfl) ⟨91458, by rfl⟩ : syracuseStep 975557 = 182917) (by norm_num)
theorem B647905 : Blo 574812 647905 := bbase (se 2 (by rfl) ⟨242964, by rfl⟩ : syracuseStep 647905 = 485929) (by norm_num)
theorem B647941 : Blo 574812 647941 := bbase (se 4 (by rfl) ⟨60744, by rfl⟩ : syracuseStep 647941 = 121489) (by norm_num)
theorem B615205 : Blo 574812 615205 := bbase (se 4 (by rfl) ⟨57675, by rfl⟩ : syracuseStep 615205 = 115351) (by norm_num)
theorem B647977 : Blo 574812 647977 := bbase (se 2 (by rfl) ⟨242991, by rfl⟩ : syracuseStep 647977 = 485983) (by norm_num)
theorem B779053 : Blo 574812 779053 := bbase (se 3 (by rfl) ⟨146072, by rfl⟩ : syracuseStep 779053 = 292145) (by norm_num)
theorem B975685 : Blo 574812 975685 := bbase (se 4 (by rfl) ⟨91470, by rfl⟩ : syracuseStep 975685 = 182941) (by norm_num)
theorem B648013 : Blo 574812 648013 := bbase (se 3 (by rfl) ⟨121502, by rfl⟩ : syracuseStep 648013 = 243005) (by norm_num)
theorem B648049 : Blo 574812 648049 := bbase (se 2 (by rfl) ⟨243018, by rfl⟩ : syracuseStep 648049 = 486037) (by norm_num)
theorem B779149 : Blo 574812 779149 := bbase (se 3 (by rfl) ⟨146090, by rfl⟩ : syracuseStep 779149 = 292181) (by norm_num)
theorem B648085 : Blo 574812 648085 := bbase (se 6 (by rfl) ⟨15189, by rfl⟩ : syracuseStep 648085 = 30379) (by norm_num)
theorem B975773 : Blo 574812 975773 := bbase (se 3 (by rfl) ⟨182957, by rfl⟩ : syracuseStep 975773 = 365915) (by norm_num)
theorem B648121 : Blo 574812 648121 := bbase (se 2 (by rfl) ⟨243045, by rfl⟩ : syracuseStep 648121 = 486091) (by norm_num)
theorem B648157 : Blo 574812 648157 := bbase (se 3 (by rfl) ⟨121529, by rfl⟩ : syracuseStep 648157 = 243059) (by norm_num)
theorem B648193 : Blo 574812 648193 := bbase (se 2 (by rfl) ⟨243072, by rfl⟩ : syracuseStep 648193 = 486145) (by norm_num)
theorem B975901 : Blo 574812 975901 := bbase (se 3 (by rfl) ⟨182981, by rfl⟩ : syracuseStep 975901 = 365963) (by norm_num)
theorem B648229 : Blo 574812 648229 := bbase (se 4 (by rfl) ⟨60771, by rfl⟩ : syracuseStep 648229 = 121543) (by norm_num)
theorem B648265 : Blo 574812 648265 := bbase (se 2 (by rfl) ⟨243099, by rfl⟩ : syracuseStep 648265 = 486199) (by norm_num)
theorem B648301 : Blo 574812 648301 := bbase (se 3 (by rfl) ⟨121556, by rfl⟩ : syracuseStep 648301 = 243113) (by norm_num)
theorem B582773 : Blo 574812 582773 := bbase (se 5 (by rfl) ⟨27317, by rfl⟩ : syracuseStep 582773 = 54635) (by norm_num)
theorem B975989 : Blo 574812 975989 := bbase (se 5 (by rfl) ⟨45749, by rfl⟩ : syracuseStep 975989 = 91499) (by norm_num)
theorem B648337 : Blo 574812 648337 := bbase (se 2 (by rfl) ⟨243126, by rfl⟩ : syracuseStep 648337 = 486253) (by norm_num)
theorem B582805 : Blo 574812 582805 := bbase (se 6 (by rfl) ⟨13659, by rfl⟩ : syracuseStep 582805 = 27319) (by norm_num)
theorem B648373 : Blo 574812 648373 := bbase (se 5 (by rfl) ⟨30392, by rfl⟩ : syracuseStep 648373 = 60785) (by norm_num)
theorem B615637 : Blo 574812 615637 := bbase (se 7 (by rfl) ⟨7214, by rfl⟩ : syracuseStep 615637 = 14429) (by norm_num)
theorem B648409 : Blo 574812 648409 := bbase (se 2 (by rfl) ⟨243153, by rfl⟩ : syracuseStep 648409 = 486307) (by norm_num)
theorem B779485 : Blo 574812 779485 := bbase (se 3 (by rfl) ⟨146153, by rfl⟩ : syracuseStep 779485 = 292307) (by norm_num)
theorem B976117 : Blo 574812 976117 := bbase (se 5 (by rfl) ⟨45755, by rfl⟩ : syracuseStep 976117 = 91511) (by norm_num)
theorem B648445 : Blo 574812 648445 := bbase (se 3 (by rfl) ⟨121583, by rfl⟩ : syracuseStep 648445 = 243167) (by norm_num)
theorem B2188565 : Blo 574812 2188565 := bbase (se 6 (by rfl) ⟨51294, by rfl⟩ : syracuseStep 2188565 = 102589) (by norm_num)
theorem B615709 : Blo 574812 615709 := bbase (se 3 (by rfl) ⟨115445, by rfl⟩ : syracuseStep 615709 = 230891) (by norm_num)
theorem B648481 : Blo 574812 648481 := bbase (se 2 (by rfl) ⟨243180, by rfl⟩ : syracuseStep 648481 = 486361) (by norm_num)
theorem B1402181 : Blo 574812 1402181 := bbase (se 4 (by rfl) ⟨131454, by rfl⟩ : syracuseStep 1402181 = 262909) (by norm_num)
theorem B648517 : Blo 574812 648517 := bbase (se 4 (by rfl) ⟨60798, by rfl⟩ : syracuseStep 648517 = 121597) (by norm_num)
theorem B976205 : Blo 574812 976205 := bbase (se 3 (by rfl) ⟨183038, by rfl⟩ : syracuseStep 976205 = 366077) (by norm_num)
theorem B1041749 : Blo 574812 1041749 := bbase (se 12 (by rfl) ⟨381, by rfl⟩ : syracuseStep 1041749 = 763) (by norm_num)
theorem B648553 : Blo 574812 648553 := bbase (se 2 (by rfl) ⟨243207, by rfl⟩ : syracuseStep 648553 = 486415) (by norm_num)
theorem B648589 : Blo 574812 648589 := bbase (se 3 (by rfl) ⟨121610, by rfl⟩ : syracuseStep 648589 = 243221) (by norm_num)
theorem B1336733 : Blo 574812 1336733 := bbase (se 3 (by rfl) ⟨250637, by rfl⟩ : syracuseStep 1336733 = 501275) (by norm_num)
theorem B2778533 : Blo 574812 2778533 := bbase (se 4 (by rfl) ⟨260487, by rfl⟩ : syracuseStep 2778533 = 520975) (by norm_num)
theorem B648625 : Blo 574812 648625 := bbase (se 2 (by rfl) ⟨243234, by rfl⟩ : syracuseStep 648625 = 486469) (by norm_num)
theorem B976333 : Blo 574812 976333 := bbase (se 3 (by rfl) ⟨183062, by rfl⟩ : syracuseStep 976333 = 366125) (by norm_num)
theorem B648661 : Blo 574812 648661 := bbase (se 7 (by rfl) ⟨7601, by rfl⟩ : syracuseStep 648661 = 15203) (by norm_num)
theorem B1172965 : Blo 574812 1172965 := bbase (se 4 (by rfl) ⟨109965, by rfl⟩ : syracuseStep 1172965 = 219931) (by norm_num)
theorem B648697 : Blo 574812 648697 := bbase (se 2 (by rfl) ⟨243261, by rfl⟩ : syracuseStep 648697 = 486523) (by norm_num)
theorem B648733 : Blo 574812 648733 := bbase (se 3 (by rfl) ⟨121637, by rfl⟩ : syracuseStep 648733 = 243275) (by norm_num)
theorem B976421 : Blo 574812 976421 := bbase (se 4 (by rfl) ⟨91539, by rfl⟩ : syracuseStep 976421 = 183079) (by norm_num)
theorem B2188853 : Blo 574812 2188853 := bbase (se 5 (by rfl) ⟨102602, by rfl⟩ : syracuseStep 2188853 = 205205) (by norm_num)
theorem B648769 : Blo 574812 648769 := bbase (se 2 (by rfl) ⟨243288, by rfl⟩ : syracuseStep 648769 = 486577) (by norm_num)
theorem B648805 : Blo 574812 648805 := bbase (se 4 (by rfl) ⟨60825, by rfl⟩ : syracuseStep 648805 = 121651) (by norm_num)
theorem B648841 : Blo 574812 648841 := bbase (se 2 (by rfl) ⟨243315, by rfl⟩ : syracuseStep 648841 = 486631) (by norm_num)
theorem B616081 : Blo 574812 616081 := bbase (se 2 (by rfl) ⟨231030, by rfl⟩ : syracuseStep 616081 = 462061) (by norm_num)
theorem B1107613 : Blo 574812 1107613 := bbase (se 3 (by rfl) ⟨207677, by rfl⟩ : syracuseStep 1107613 = 415355) (by norm_num)
theorem B976549 : Blo 574812 976549 := bbase (se 4 (by rfl) ⟨91551, by rfl⟩ : syracuseStep 976549 = 183103) (by norm_num)
theorem B648877 : Blo 574812 648877 := bbase (se 3 (by rfl) ⟨121664, by rfl⟩ : syracuseStep 648877 = 243329) (by norm_num)
theorem B648913 : Blo 574812 648913 := bbase (se 2 (by rfl) ⟨243342, by rfl⟩ : syracuseStep 648913 = 486685) (by norm_num)
theorem B583405 : Blo 574812 583405 := bbase (se 3 (by rfl) ⟨109388, by rfl⟩ : syracuseStep 583405 = 218777) (by norm_num)
theorem B648949 : Blo 574812 648949 := bbase (se 5 (by rfl) ⟨30419, by rfl⟩ : syracuseStep 648949 = 60839) (by norm_num)
theorem B976637 : Blo 574812 976637 := bbase (se 3 (by rfl) ⟨183119, by rfl⟩ : syracuseStep 976637 = 366239) (by norm_num)
theorem B648985 : Blo 574812 648985 := bbase (se 2 (by rfl) ⟨243369, by rfl⟩ : syracuseStep 648985 = 486739) (by norm_num)
theorem B2910005 : Blo 574812 2910005 := bbase (se 5 (by rfl) ⟨136406, by rfl⟩ : syracuseStep 2910005 = 272813) (by norm_num)
theorem B649021 : Blo 574812 649021 := bbase (se 3 (by rfl) ⟨121691, by rfl⟩ : syracuseStep 649021 = 243383) (by norm_num)
theorem B649057 : Blo 574812 649057 := bbase (se 2 (by rfl) ⟨243396, by rfl⟩ : syracuseStep 649057 = 486793) (by norm_num)
theorem B649093 : Blo 574812 649093 := bbase (se 4 (by rfl) ⟨60852, by rfl⟩ : syracuseStep 649093 = 121705) (by norm_num)
theorem B649129 : Blo 574812 649129 := bbase (se 2 (by rfl) ⟨243423, by rfl⟩ : syracuseStep 649129 = 486847) (by norm_num)
theorem B649165 : Blo 574812 649165 := bbase (se 3 (by rfl) ⟨121718, by rfl⟩ : syracuseStep 649165 = 243437) (by norm_num)
theorem B649201 : Blo 574812 649201 := bbase (se 2 (by rfl) ⟨243450, by rfl⟩ : syracuseStep 649201 = 486901) (by norm_num)
theorem B616457 : Blo 574812 616457 := bbase (se 2 (by rfl) ⟨231171, by rfl⟩ : syracuseStep 616457 = 462343) (by norm_num)
theorem B649237 : Blo 574812 649237 := bbase (se 6 (by rfl) ⟨15216, by rfl⟩ : syracuseStep 649237 = 30433) (by norm_num)
theorem B6252565 : Blo 574812 6252565 := bbase (se 6 (by rfl) ⟨146544, by rfl⟩ : syracuseStep 6252565 = 293089) (by norm_num)
theorem B583705 : Blo 574812 583705 := bbase (se 2 (by rfl) ⟨218889, by rfl⟩ : syracuseStep 583705 = 437779) (by norm_num)
theorem B649273 : Blo 574812 649273 := bbase (se 2 (by rfl) ⟨243477, by rfl⟩ : syracuseStep 649273 = 486955) (by norm_num)
theorem B616529 : Blo 574812 616529 := bbase (se 2 (by rfl) ⟨231198, by rfl⟩ : syracuseStep 616529 = 462397) (by norm_num)
theorem B649309 : Blo 574812 649309 := bbase (se 3 (by rfl) ⟨121745, by rfl⟩ : syracuseStep 649309 = 243491) (by norm_num)
theorem B649345 : Blo 574812 649345 := bbase (se 2 (by rfl) ⟨243504, by rfl⟩ : syracuseStep 649345 = 487009) (by norm_num)
theorem B649381 : Blo 574812 649381 := bbase (se 4 (by rfl) ⟨60879, by rfl⟩ : syracuseStep 649381 = 121759) (by norm_num)
theorem B649417 : Blo 574812 649417 := bbase (se 2 (by rfl) ⟨243531, by rfl⟩ : syracuseStep 649417 = 487063) (by norm_num)
theorem B649453 : Blo 574812 649453 := bbase (se 3 (by rfl) ⟨121772, by rfl⟩ : syracuseStep 649453 = 243545) (by norm_num)
theorem B616717 : Blo 574812 616717 := bbase (se 3 (by rfl) ⟨115634, by rfl⟩ : syracuseStep 616717 = 231269) (by norm_num)
theorem B649489 : Blo 574812 649489 := bbase (se 2 (by rfl) ⟨243558, by rfl⟩ : syracuseStep 649489 = 487117) (by norm_num)
theorem B649525 : Blo 574812 649525 := bbase (se 5 (by rfl) ⟨30446, by rfl⟩ : syracuseStep 649525 = 60893) (by norm_num)
theorem B649561 : Blo 574812 649561 := bbase (se 2 (by rfl) ⟨243585, by rfl⟩ : syracuseStep 649561 = 487171) (by norm_num)
theorem B649597 : Blo 574812 649597 := bbase (se 3 (by rfl) ⟨121799, by rfl⟩ : syracuseStep 649597 = 243599) (by norm_num)
theorem B1337741 : Blo 574812 1337741 := bbase (se 3 (by rfl) ⟨250826, by rfl⟩ : syracuseStep 1337741 = 501653) (by norm_num)
theorem B649633 : Blo 574812 649633 := bbase (se 2 (by rfl) ⟨243612, by rfl⟩ : syracuseStep 649633 = 487225) (by norm_num)
theorem B649669 : Blo 574812 649669 := bbase (se 4 (by rfl) ⟨60906, by rfl⟩ : syracuseStep 649669 = 121813) (by norm_num)
theorem B616901 : Blo 574812 616901 := bbase (se 4 (by rfl) ⟨57834, by rfl⟩ : syracuseStep 616901 = 115669) (by norm_num)
theorem B649705 : Blo 574812 649705 := bbase (se 2 (by rfl) ⟨243639, by rfl⟩ : syracuseStep 649705 = 487279) (by norm_num)
theorem B649741 : Blo 574812 649741 := bbase (se 3 (by rfl) ⟨121826, by rfl⟩ : syracuseStep 649741 = 243653) (by norm_num)
theorem B649777 : Blo 574812 649777 := bbase (se 2 (by rfl) ⟨243666, by rfl⟩ : syracuseStep 649777 = 487333) (by norm_num)
theorem B649813 : Blo 574812 649813 := bbase (se 8 (by rfl) ⟨3807, by rfl⟩ : syracuseStep 649813 = 7615) (by norm_num)
theorem B649849 : Blo 574812 649849 := bbase (se 2 (by rfl) ⟨243693, by rfl⟩ : syracuseStep 649849 = 487387) (by norm_num)
theorem B1108637 : Blo 574812 1108637 := bbase (se 3 (by rfl) ⟨207869, by rfl⟩ : syracuseStep 1108637 = 415739) (by norm_num)
theorem B649885 : Blo 574812 649885 := bbase (se 3 (by rfl) ⟨121853, by rfl⟩ : syracuseStep 649885 = 243707) (by norm_num)
theorem B649921 : Blo 574812 649921 := bbase (se 2 (by rfl) ⟨243720, by rfl⟩ : syracuseStep 649921 = 487441) (by norm_num)
theorem B2190037 : Blo 574812 2190037 := bbase (se 7 (by rfl) ⟨25664, by rfl⟩ : syracuseStep 2190037 = 51329) (by norm_num)
theorem B649957 : Blo 574812 649957 := bbase (se 4 (by rfl) ⟨60933, by rfl⟩ : syracuseStep 649957 = 121867) (by norm_num)
theorem B879341 : Blo 574812 879341 := bbase (se 3 (by rfl) ⟨164876, by rfl⟩ : syracuseStep 879341 = 329753) (by norm_num)
theorem B649993 : Blo 574812 649993 := bbase (se 2 (by rfl) ⟨243747, by rfl⟩ : syracuseStep 649993 = 487495) (by norm_num)
theorem B650029 : Blo 574812 650029 := bbase (se 3 (by rfl) ⟨121880, by rfl⟩ : syracuseStep 650029 = 243761) (by norm_num)
theorem B650065 : Blo 574812 650065 := bbase (se 2 (by rfl) ⟨243774, by rfl⟩ : syracuseStep 650065 = 487549) (by norm_num)
theorem B650101 : Blo 574812 650101 := bbase (se 5 (by rfl) ⟨30473, by rfl⟩ : syracuseStep 650101 = 60947) (by norm_num)
theorem B650137 : Blo 574812 650137 := bbase (se 2 (by rfl) ⟨243801, by rfl⟩ : syracuseStep 650137 = 487603) (by norm_num)
theorem B584621 : Blo 574812 584621 := bbase (se 3 (by rfl) ⟨109616, by rfl⟩ : syracuseStep 584621 = 219233) (by norm_num)
theorem B650173 : Blo 574812 650173 := bbase (se 3 (by rfl) ⟨121907, by rfl⟩ : syracuseStep 650173 = 243815) (by norm_num)
theorem B9989077 : Blo 574812 9989077 := bbase (se 7 (by rfl) ⟨117059, by rfl⟩ : syracuseStep 9989077 = 234119) (by norm_num)
theorem B650209 : Blo 574812 650209 := bbase (se 2 (by rfl) ⟨243828, by rfl⟩ : syracuseStep 650209 = 487657) (by norm_num)
theorem B2190341 : Blo 574812 2190341 := bbase (se 4 (by rfl) ⟨205344, by rfl⟩ : syracuseStep 2190341 = 410689) (by norm_num)
theorem B650245 : Blo 574812 650245 := bbase (se 4 (by rfl) ⟨60960, by rfl⟩ : syracuseStep 650245 = 121921) (by norm_num)
theorem B650281 : Blo 574812 650281 := bbase (se 2 (by rfl) ⟨243855, by rfl⟩ : syracuseStep 650281 = 487711) (by norm_num)
theorem B1109053 : Blo 574812 1109053 := bbase (se 3 (by rfl) ⟨207947, by rfl⟩ : syracuseStep 1109053 = 415895) (by norm_num)
theorem B2911301 : Blo 574812 2911301 := bbase (se 4 (by rfl) ⟨272934, by rfl⟩ : syracuseStep 2911301 = 545869) (by norm_num)
theorem B650317 : Blo 574812 650317 := bbase (se 3 (by rfl) ⟨121934, by rfl⟩ : syracuseStep 650317 = 243869) (by norm_num)
theorem B650353 : Blo 574812 650353 := bbase (se 2 (by rfl) ⟨243882, by rfl⟩ : syracuseStep 650353 = 487765) (by norm_num)
theorem B650389 : Blo 574812 650389 := bbase (se 6 (by rfl) ⟨15243, by rfl⟩ : syracuseStep 650389 = 30487) (by norm_num)
theorem B617653 : Blo 574812 617653 := bbase (se 5 (by rfl) ⟨28952, by rfl⟩ : syracuseStep 617653 = 57905) (by norm_num)
theorem B650425 : Blo 574812 650425 := bbase (se 2 (by rfl) ⟨243909, by rfl⟩ : syracuseStep 650425 = 487819) (by norm_num)
theorem B650461 : Blo 574812 650461 := bbase (se 3 (by rfl) ⟨121961, by rfl⟩ : syracuseStep 650461 = 243923) (by norm_num)
theorem B617725 : Blo 574812 617725 := bbase (se 3 (by rfl) ⟨115823, by rfl⟩ : syracuseStep 617725 = 231647) (by norm_num)
theorem B650497 : Blo 574812 650497 := bbase (se 2 (by rfl) ⟨243936, by rfl⟩ : syracuseStep 650497 = 487873) (by norm_num)
theorem B650533 : Blo 574812 650533 := bbase (se 4 (by rfl) ⟨60987, by rfl⟩ : syracuseStep 650533 = 121975) (by norm_num)
theorem B650569 : Blo 574812 650569 := bbase (se 2 (by rfl) ⟨243963, by rfl⟩ : syracuseStep 650569 = 487927) (by norm_num)
theorem B781669 : Blo 574812 781669 := bbase (se 4 (by rfl) ⟨73281, by rfl⟩ : syracuseStep 781669 = 146563) (by norm_num)
theorem B650605 : Blo 574812 650605 := bbase (se 3 (by rfl) ⟨121988, by rfl⟩ : syracuseStep 650605 = 243977) (by norm_num)
theorem B650641 : Blo 574812 650641 := bbase (se 2 (by rfl) ⟨243990, by rfl⟩ : syracuseStep 650641 = 487981) (by norm_num)
theorem B5270933 : Blo 574812 5270933 := bbase (se 6 (by rfl) ⟨123537, by rfl⟩ : syracuseStep 5270933 = 247075) (by norm_num)
theorem B781733 : Blo 574812 781733 := bbase (se 4 (by rfl) ⟨73287, by rfl⟩ : syracuseStep 781733 = 146575) (by norm_num)
theorem B617905 : Blo 574812 617905 := bbase (se 2 (by rfl) ⟨231714, by rfl⟩ : syracuseStep 617905 = 463429) (by norm_num)
theorem B650677 : Blo 574812 650677 := bbase (se 5 (by rfl) ⟨30500, by rfl⟩ : syracuseStep 650677 = 61001) (by norm_num)
theorem B2223557 : Blo 574812 2223557 := bbase (se 4 (by rfl) ⟨208458, by rfl⟩ : syracuseStep 2223557 = 416917) (by norm_num)
theorem B650713 : Blo 574812 650713 := bbase (se 2 (by rfl) ⟨244017, by rfl⟩ : syracuseStep 650713 = 488035) (by norm_num)
theorem B585185 : Blo 574812 585185 := bbase (se 2 (by rfl) ⟨219444, by rfl⟩ : syracuseStep 585185 = 438889) (by norm_num)
theorem B749029 : Blo 574812 749029 := bbase (se 4 (by rfl) ⟨70221, by rfl⟩ : syracuseStep 749029 = 140443) (by norm_num)
theorem B650749 : Blo 574812 650749 := bbase (se 3 (by rfl) ⟨122015, by rfl⟩ : syracuseStep 650749 = 244031) (by norm_num)
theorem B650785 : Blo 574812 650785 := bbase (se 2 (by rfl) ⟨244044, by rfl⟩ : syracuseStep 650785 = 488089) (by norm_num)
theorem B2780725 : Blo 574812 2780725 := bbase (se 5 (by rfl) ⟨130346, by rfl⟩ : syracuseStep 2780725 = 260693) (by norm_num)
theorem B650821 : Blo 574812 650821 := bbase (se 4 (by rfl) ⟨61014, by rfl⟩ : syracuseStep 650821 = 122029) (by norm_num)
theorem B650857 : Blo 574812 650857 := bbase (se 2 (by rfl) ⟨244071, by rfl⟩ : syracuseStep 650857 = 488143) (by norm_num)
theorem B650893 : Blo 574812 650893 := bbase (se 3 (by rfl) ⟨122042, by rfl⟩ : syracuseStep 650893 = 244085) (by norm_num)
theorem B1502885 : Blo 574812 1502885 := bbase (se 4 (by rfl) ⟨140895, by rfl⟩ : syracuseStep 1502885 = 281791) (by norm_num)
theorem B650929 : Blo 574812 650929 := bbase (se 2 (by rfl) ⟨244098, by rfl⟩ : syracuseStep 650929 = 488197) (by norm_num)
theorem B650965 : Blo 574812 650965 := bbase (se 7 (by rfl) ⟨7628, by rfl⟩ : syracuseStep 650965 = 15257) (by norm_num)
theorem B651001 : Blo 574812 651001 := bbase (se 2 (by rfl) ⟨244125, by rfl⟩ : syracuseStep 651001 = 488251) (by norm_num)
theorem B651037 : Blo 574812 651037 := bbase (se 3 (by rfl) ⟨122069, by rfl⟩ : syracuseStep 651037 = 244139) (by norm_num)
theorem B651073 : Blo 574812 651073 := bbase (se 2 (by rfl) ⟨244152, by rfl⟩ : syracuseStep 651073 = 488305) (by norm_num)
theorem B651109 : Blo 574812 651109 := bbase (se 4 (by rfl) ⟨61041, by rfl⟩ : syracuseStep 651109 = 122083) (by norm_num)
theorem B651145 : Blo 574812 651145 := bbase (se 2 (by rfl) ⟨244179, by rfl⟩ : syracuseStep 651145 = 488359) (by norm_num)
theorem B3502037 : Blo 574812 3502037 := bbase (se 7 (by rfl) ⟨41039, by rfl⟩ : syracuseStep 3502037 = 82079) (by norm_num)
theorem B585749 : Blo 574812 585749 := bbase (se 6 (by rfl) ⟨13728, by rfl⟩ : syracuseStep 585749 = 27457) (by norm_num)
theorem B2912597 : Blo 574812 2912597 := bbase (se 10 (by rfl) ⟨4266, by rfl⟩ : syracuseStep 2912597 = 8533) (by norm_num)
theorem B1667525 : Blo 574812 1667525 := bbase (se 4 (by rfl) ⟨156330, by rfl⟩ : syracuseStep 1667525 = 312661) (by norm_num)
theorem B6582869 : Blo 574812 6582869 := bbase (se 8 (by rfl) ⟨38571, by rfl⟩ : syracuseStep 6582869 = 77143) (by norm_num)
theorem B2257573 : Blo 574812 2257573 := bbase (se 4 (by rfl) ⟨211647, by rfl⟩ : syracuseStep 2257573 = 423295) (by norm_num)
theorem B750277 : Blo 574812 750277 := bbase (se 4 (by rfl) ⟨70338, by rfl⟩ : syracuseStep 750277 = 140677) (by norm_num)
theorem B4682549 : Blo 574812 4682549 := bbase (se 5 (by rfl) ⟨219494, by rfl⟩ : syracuseStep 4682549 = 438989) (by norm_num)
theorem B684893 : Blo 574812 684893 := bbase (se 3 (by rfl) ⟨128417, by rfl⟩ : syracuseStep 684893 = 256835) (by norm_num)
theorem B586649 : Blo 574812 586649 := bbase (se 2 (by rfl) ⟨219993, by rfl⟩ : syracuseStep 586649 = 439987) (by norm_num)
theorem B2192453 : Blo 574812 2192453 := bbase (se 4 (by rfl) ⟨205542, by rfl⟩ : syracuseStep 2192453 = 411085) (by norm_num)
theorem B2225461 : Blo 574812 2225461 := bbase (se 5 (by rfl) ⟨104318, by rfl⟩ : syracuseStep 2225461 = 208637) (by norm_num)
theorem B2192741 : Blo 574812 2192741 := bbase (se 4 (by rfl) ⟨205569, by rfl⟩ : syracuseStep 2192741 = 411139) (by norm_num)
theorem B2913893 : Blo 574812 2913893 := bbase (se 4 (by rfl) ⟨273177, by rfl⟩ : syracuseStep 2913893 = 546355) (by norm_num)
theorem B16644437 : Blo 574812 16644437 := bbase (se 10 (by rfl) ⟨24381, by rfl⟩ : syracuseStep 16644437 = 48763) (by norm_num)
theorem B2849269 : Blo 574812 2849269 := bbase (se 5 (by rfl) ⟨133559, by rfl⟩ : syracuseStep 2849269 = 267119) (by norm_num)
theorem B2193925 : Blo 574812 2193925 := bbase (se 4 (by rfl) ⟨205680, by rfl⟩ : syracuseStep 2193925 = 411361) (by norm_num)
theorem B2194229 : Blo 574812 2194229 := bbase (se 5 (by rfl) ⟨102854, by rfl⟩ : syracuseStep 2194229 = 205709) (by norm_num)
theorem B2915189 : Blo 574812 2915189 := bbase (se 5 (by rfl) ⟨136649, by rfl⟩ : syracuseStep 2915189 = 273299) (by norm_num)
theorem B4390037 : Blo 574812 4390037 := bbase (se 6 (by rfl) ⟨102891, by rfl⟩ : syracuseStep 4390037 = 205783) (by norm_num)
theorem B1408213 : Blo 574812 1408213 := bbase (se 7 (by rfl) ⟨16502, by rfl⟩ : syracuseStep 1408213 = 33005) (by norm_num)
theorem B2456821 : Blo 574812 2456821 := bbase (se 5 (by rfl) ⟨115163, by rfl⟩ : syracuseStep 2456821 = 230327) (by norm_num)
theorem B1637653 : Blo 574812 1637653 := bbase (se 6 (by rfl) ⟨38382, by rfl⟩ : syracuseStep 1637653 = 76765) (by norm_num)
theorem B687421 : Blo 574812 687421 := bbase (se 3 (by rfl) ⟨128891, by rfl⟩ : syracuseStep 687421 = 257783) (by norm_num)
theorem B818525 : Blo 574812 818525 := bbase (se 3 (by rfl) ⟨153473, by rfl⟩ : syracuseStep 818525 = 306947) (by norm_num)
theorem B1637813 : Blo 574812 1637813 := bbase (se 5 (by rfl) ⟨76772, by rfl⟩ : syracuseStep 1637813 = 153545) (by norm_num)
theorem B1638053 : Blo 574812 1638053 := bbase (se 4 (by rfl) ⟨153567, by rfl⟩ : syracuseStep 1638053 = 307135) (by norm_num)
theorem B1638245 : Blo 574812 1638245 := bbase (se 4 (by rfl) ⟨153585, by rfl⟩ : syracuseStep 1638245 = 307171) (by norm_num)
theorem B819077 : Blo 574812 819077 := bbase (se 4 (by rfl) ⟨76788, by rfl⟩ : syracuseStep 819077 = 153577) (by norm_num)
theorem B3113093 : Blo 574812 3113093 := bstep (se 4 (by rfl) ⟨291852, by rfl⟩ : syracuseStep 3113093 = 583705) B583705
theorem B1638701 : Blo 574812 1638701 := bstep (se 3 (by rfl) ⟨307256, by rfl⟩ : syracuseStep 1638701 = 614513) B614513
theorem B3277219 : Blo 574812 3277219 := bstep (se 1 (by rfl) ⟨2457914, by rfl⟩ : syracuseStep 3277219 = 4915829) B4915829
theorem B1638883 : Blo 574812 1638883 := bstep (se 1 (by rfl) ⟨1229162, by rfl⟩ : syracuseStep 1638883 = 2458325) B2458325
theorem B819715 : Blo 574812 819715 := bstep (se 1 (by rfl) ⟨614786, by rfl⟩ : syracuseStep 819715 = 1229573) B1229573
theorem B1638929 : Blo 574812 1638929 := bstep (se 2 (by rfl) ⟨614598, by rfl⟩ : syracuseStep 1638929 = 1229197) B1229197
theorem B655939 : Blo 574812 655939 := bstep (se 1 (by rfl) ⟨491954, by rfl⟩ : syracuseStep 655939 = 983909) B983909
theorem B1475185 : Blo 574812 1475185 := bstep (se 2 (by rfl) ⟨553194, by rfl⟩ : syracuseStep 1475185 = 1106389) B1106389
theorem B983729 : Blo 574812 983729 := bstep (se 2 (by rfl) ⟨368898, by rfl⟩ : syracuseStep 983729 = 737797) B737797
theorem B2196173 : Blo 574812 2196173 := bstep (se 3 (by rfl) ⟨411782, by rfl⟩ : syracuseStep 2196173 = 823565) B823565
theorem B3113741 : Blo 574812 3113741 := bstep (se 3 (by rfl) ⟨583826, by rfl⟩ : syracuseStep 3113741 = 1167653) B1167653
theorem B2917133 : Blo 574812 2917133 := bstep (se 3 (by rfl) ⟨546962, by rfl⟩ : syracuseStep 2917133 = 1093925) B1093925
theorem B2622257 : Blo 574812 2622257 := bstep (se 2 (by rfl) ⟨983346, by rfl⟩ : syracuseStep 2622257 = 1966693) B1966693
theorem B1967021 : Blo 574812 1967021 := bstep (se 3 (by rfl) ⟨368816, by rfl⟩ : syracuseStep 1967021 = 737633) B737633
theorem B3277745 : Blo 574812 3277745 := bstep (se 2 (by rfl) ⟨1229154, by rfl⟩ : syracuseStep 3277745 = 2458309) B2458309
theorem B3737029 : Blo 574812 3737029 := bstep (se 4 (by rfl) ⟨350346, by rfl⟩ : syracuseStep 3737029 = 700693) B700693
theorem B624179 : Blo 574812 624179 := bstep (se 1 (by rfl) ⟨468134, by rfl⟩ : syracuseStep 624179 = 936269) B936269
theorem B820849 : Blo 574812 820849 := bstep (se 2 (by rfl) ⟨307818, by rfl⟩ : syracuseStep 820849 = 615637) B615637
theorem B820945 : Blo 574812 820945 := bstep (se 2 (by rfl) ⟨307854, by rfl⟩ : syracuseStep 820945 = 615709) B615709
theorem B2459555 : Blo 574812 2459555 := bstep (se 1 (by rfl) ⟨1844666, by rfl⟩ : syracuseStep 2459555 = 3689333) B3689333
theorem B1640387 : Blo 574812 1640387 := bstep (se 1 (by rfl) ⟨1230290, by rfl⟩ : syracuseStep 1640387 = 2460581) B2460581
theorem B1312753 : Blo 574812 1312753 := bstep (se 2 (by rfl) ⟨492282, by rfl⟩ : syracuseStep 1312753 = 984565) B984565
theorem B821441 : Blo 574812 821441 := bstep (se 2 (by rfl) ⟨308040, by rfl⟩ : syracuseStep 821441 = 616081) B616081
theorem B3279203 : Blo 574812 3279203 := bstep (se 1 (by rfl) ⟨2459402, by rfl⟩ : syracuseStep 3279203 = 4918805) B4918805
theorem B7473521 : Blo 574812 7473521 := bstep (se 2 (by rfl) ⟨2802570, by rfl⟩ : syracuseStep 7473521 = 5605141) B5605141
theorem B11111053 : Blo 574812 11111053 := bstep (se 3 (by rfl) ⟨2083322, by rfl⟩ : syracuseStep 11111053 = 4166645) B4166645
theorem B7867205 : Blo 574812 7867205 := bstep (se 4 (by rfl) ⟨737550, by rfl⟩ : syracuseStep 7867205 = 1475101) B1475101
theorem B4393925 : Blo 574812 4393925 := bstep (se 4 (by rfl) ⟨411930, by rfl⟩ : syracuseStep 4393925 = 823861) B823861
theorem B822307 : Blo 574812 822307 := bstep (se 1 (by rfl) ⟨616730, by rfl⟩ : syracuseStep 822307 = 1233461) B1233461
theorem B822403 : Blo 574812 822403 := bstep (se 1 (by rfl) ⟨616802, by rfl⟩ : syracuseStep 822403 = 1233605) B1233605
theorem B1641617 : Blo 574812 1641617 := bstep (se 2 (by rfl) ⟨615606, by rfl⟩ : syracuseStep 1641617 = 1231213) B1231213
theorem B7409009 : Blo 574812 7409009 := bstep (se 2 (by rfl) ⟨2778378, by rfl⟩ : syracuseStep 7409009 = 5556757) B5556757
theorem B920963 : Blo 574812 920963 := bstep (se 1 (by rfl) ⟨690722, by rfl⟩ : syracuseStep 920963 = 1381445) B1381445
theorem B2920049 : Blo 574812 2920049 := bstep (se 2 (by rfl) ⟨1095018, by rfl⟩ : syracuseStep 2920049 = 2190037) B2190037
theorem B822899 : Blo 574812 822899 := bstep (se 1 (by rfl) ⟨617174, by rfl⟩ : syracuseStep 822899 = 1234349) B1234349
theorem B986755 : Blo 574812 986755 := bstep (se 1 (by rfl) ⟨740066, by rfl⟩ : syracuseStep 986755 = 1480133) B1480133
theorem B921251 : Blo 574812 921251 := bstep (se 1 (by rfl) ⟨690938, by rfl⟩ : syracuseStep 921251 = 1381877) B1381877
theorem B1052369 : Blo 574812 1052369 := bstep (se 2 (by rfl) ⟨394638, by rfl⟩ : syracuseStep 1052369 = 789277) B789277
theorem B8294197 : Blo 574812 8294197 := bstep (se 5 (by rfl) ⟨388790, by rfl⟩ : syracuseStep 8294197 = 777581) B777581
theorem B790481 : Blo 574812 790481 := bstep (se 2 (by rfl) ⟨296430, by rfl⟩ : syracuseStep 790481 = 592861) B592861
theorem B921667 : Blo 574812 921667 := bstep (se 1 (by rfl) ⟨691250, by rfl⟩ : syracuseStep 921667 = 1382501) B1382501
theorem B1478737 : Blo 574812 1478737 := bstep (se 2 (by rfl) ⟨554526, by rfl⟩ : syracuseStep 1478737 = 1109053) B1109053
theorem B2330765 : Blo 574812 2330765 := bstep (se 3 (by rfl) ⟨437018, by rfl⟩ : syracuseStep 2330765 = 874037) B874037
theorem B3281093 : Blo 574812 3281093 := bstep (se 4 (by rfl) ⟨307602, by rfl⟩ : syracuseStep 3281093 = 615205) B615205
theorem B823537 : Blo 574812 823537 := bstep (se 2 (by rfl) ⟨308826, by rfl⟩ : syracuseStep 823537 = 617653) B617653
theorem B3707171 : Blo 574812 3707171 := bstep (se 1 (by rfl) ⟨2780378, by rfl⟩ : syracuseStep 3707171 = 5560757) B5560757
theorem B921937 : Blo 574812 921937 := bstep (se 2 (by rfl) ⟨345726, by rfl⟩ : syracuseStep 921937 = 691453) B691453
theorem B1872227 : Blo 574812 1872227 := bstep (se 1 (by rfl) ⟨1404170, by rfl⟩ : syracuseStep 1872227 = 2808341) B2808341
theorem B856433 : Blo 574812 856433 := bstep (se 2 (by rfl) ⟨321162, by rfl⟩ : syracuseStep 856433 = 642325) B642325
theorem B692707 : Blo 574812 692707 := bstep (se 1 (by rfl) ⟨519530, by rfl⟩ : syracuseStep 692707 = 1039061) B1039061
theorem B823873 : Blo 574812 823873 := bstep (se 2 (by rfl) ⟨308952, by rfl⟩ : syracuseStep 823873 = 617905) B617905
theorem B1643075 : Blo 574812 1643075 := bstep (se 1 (by rfl) ⟨1232306, by rfl⟩ : syracuseStep 1643075 = 2464613) B2464613
theorem B922193 : Blo 574812 922193 := bstep (se 2 (by rfl) ⟨345822, by rfl⟩ : syracuseStep 922193 = 691645) B691645
theorem B6099697 : Blo 574812 6099697 := bstep (se 2 (by rfl) ⟨2287386, by rfl⟩ : syracuseStep 6099697 = 4574773) B4574773
theorem B3707633 : Blo 574812 3707633 := bstep (se 2 (by rfl) ⟨1390362, by rfl⟩ : syracuseStep 3707633 = 2780725) B2780725
theorem B2921507 : Blo 574812 2921507 := bstep (se 1 (by rfl) ⟨2191130, by rfl⟩ : syracuseStep 2921507 = 4382261) B4382261
theorem B9999557 : Blo 574812 9999557 := bstep (se 4 (by rfl) ⟨937458, by rfl⟩ : syracuseStep 9999557 = 1874917) B1874917
theorem B922897 : Blo 574812 922897 := bstep (se 2 (by rfl) ⟨346086, by rfl⟩ : syracuseStep 922897 = 692173) B692173
theorem B7411013 : Blo 574812 7411013 := bstep (se 4 (by rfl) ⟨694782, by rfl⟩ : syracuseStep 7411013 = 1389565) B1389565
theorem B1643885 : Blo 574812 1643885 := bstep (se 3 (by rfl) ⟨308228, by rfl⟩ : syracuseStep 1643885 = 616457) B616457
theorem B1644077 : Blo 574812 1644077 := bstep (se 3 (by rfl) ⟨308264, by rfl⟩ : syracuseStep 1644077 = 616529) B616529
theorem B2463281 : Blo 574812 2463281 := bstep (se 2 (by rfl) ⟨923730, by rfl⟩ : syracuseStep 2463281 = 1847461) B1847461
theorem B2332259 : Blo 574812 2332259 := bstep (se 1 (by rfl) ⟨1749194, by rfl⟩ : syracuseStep 2332259 = 3498389) B3498389
theorem B3610403 : Blo 574812 3610403 := bstep (se 1 (by rfl) ⟨2707802, by rfl⟩ : syracuseStep 3610403 = 5415605) B5415605
theorem B6559541 : Blo 574812 6559541 := bstep (se 5 (by rfl) ⟨307478, by rfl⟩ : syracuseStep 6559541 = 614957) B614957
theorem B2922317 : Blo 574812 2922317 := bstep (se 3 (by rfl) ⟨547934, by rfl⟩ : syracuseStep 2922317 = 1095869) B1095869
theorem B1382339 : Blo 574812 1382339 := bstep (se 1 (by rfl) ⟨1036754, by rfl⟩ : syracuseStep 1382339 = 2073509) B2073509
theorem B21043313 : Blo 574812 21043313 := bstep (se 2 (by rfl) ⟨7891242, by rfl⟩ : syracuseStep 21043313 = 15782485) B15782485
theorem B923795 : Blo 574812 923795 := bstep (se 1 (by rfl) ⟨692846, by rfl⟩ : syracuseStep 923795 = 1385693) B1385693
theorem B694499 : Blo 574812 694499 := bstep (se 1 (by rfl) ⟨520874, by rfl⟩ : syracuseStep 694499 = 1041749) B1041749
theorem B891155 : Blo 574812 891155 := bstep (se 1 (by rfl) ⟨668366, by rfl⟩ : syracuseStep 891155 = 1336733) B1336733
theorem B923987 : Blo 574812 923987 := bstep (se 1 (by rfl) ⟨692990, by rfl⟩ : syracuseStep 923987 = 1385981) B1385981
theorem B1645069 : Blo 574812 1645069 := bstep (se 3 (by rfl) ⟨308450, by rfl⟩ : syracuseStep 1645069 = 616901) B616901
theorem B1940003 : Blo 574812 1940003 := bstep (se 1 (by rfl) ⟨1455002, by rfl⟩ : syracuseStep 1940003 = 2910005) B2910005
theorem B727699 : Blo 574812 727699 := bstep (se 1 (by rfl) ⟨545774, by rfl⟩ : syracuseStep 727699 = 1091549) B1091549
theorem B727795 : Blo 574812 727795 := bstep (se 1 (by rfl) ⟨545846, by rfl⟩ : syracuseStep 727795 = 1091693) B1091693
theorem B1940273 : Blo 574812 1940273 := bstep (se 2 (by rfl) ⟨727602, by rfl⟩ : syracuseStep 1940273 = 1455205) B1455205
theorem B891827 : Blo 574812 891827 := bstep (se 1 (by rfl) ⟨668870, by rfl⟩ : syracuseStep 891827 = 1337741) B1337741
theorem B4168901 : Blo 574812 4168901 := bstep (se 4 (by rfl) ⟨390834, by rfl⟩ : syracuseStep 4168901 = 781669) B781669
theorem B728291 : Blo 574812 728291 := bstep (se 1 (by rfl) ⟨546218, by rfl⟩ : syracuseStep 728291 = 1092437) B1092437
theorem B924961 : Blo 574812 924961 := bstep (se 2 (by rfl) ⟨346860, by rfl⟩ : syracuseStep 924961 = 693721) B693721
theorem B1940813 : Blo 574812 1940813 := bstep (se 3 (by rfl) ⟨363902, by rfl⟩ : syracuseStep 1940813 = 727805) B727805
theorem B1940867 : Blo 574812 1940867 := bstep (se 1 (by rfl) ⟨1455650, by rfl⟩ : syracuseStep 1940867 = 2911301) B2911301
theorem B6233669 : Blo 574812 6233669 := bstep (se 4 (by rfl) ⟨584406, by rfl⟩ : syracuseStep 6233669 = 1168813) B1168813
theorem B3513955 : Blo 574812 3513955 := bstep (se 1 (by rfl) ⟨2635466, by rfl⟩ : syracuseStep 3513955 = 5270933) B5270933
theorem B1482371 : Blo 574812 1482371 := bstep (se 1 (by rfl) ⟨1111778, by rfl⟩ : syracuseStep 1482371 = 2223557) B2223557
theorem B1941137 : Blo 574812 1941137 := bstep (se 2 (by rfl) ⟨727926, by rfl⟩ : syracuseStep 1941137 = 1455853) B1455853
theorem B925409 : Blo 574812 925409 := bstep (se 2 (by rfl) ⟨347028, by rfl⟩ : syracuseStep 925409 = 694057) B694057
theorem B15179633 : Blo 574812 15179633 := bstep (se 2 (by rfl) ⟨5692362, by rfl⟩ : syracuseStep 15179633 = 11384725) B11384725
theorem B3514225 : Blo 574812 3514225 := bstep (se 2 (by rfl) ⟨1317834, by rfl⟩ : syracuseStep 3514225 = 2635669) B2635669
theorem B1384337 : Blo 574812 1384337 := bstep (se 2 (by rfl) ⟨519126, by rfl⟩ : syracuseStep 1384337 = 1038253) B1038253
theorem B728995 : Blo 574812 728995 := bstep (se 1 (by rfl) ⟨546746, by rfl⟩ : syracuseStep 728995 = 1093493) B1093493
theorem B2465741 : Blo 574812 2465741 := bstep (se 3 (by rfl) ⟨462326, by rfl⟩ : syracuseStep 2465741 = 924653) B924653
theorem B2334691 : Blo 574812 2334691 := bstep (se 1 (by rfl) ⟨1751018, by rfl⟩ : syracuseStep 2334691 = 3502037) B3502037
theorem B1843181 : Blo 574812 1843181 := bstep (se 3 (by rfl) ⟨345596, by rfl⟩ : syracuseStep 1843181 = 691193) B691193
theorem B729091 : Blo 574812 729091 := bstep (se 1 (by rfl) ⟨546818, by rfl⟩ : syracuseStep 729091 = 1093637) B1093637
theorem B14000149 : Blo 574812 14000149 := bstep (se 6 (by rfl) ⟨328128, by rfl⟩ : syracuseStep 14000149 = 656257) B656257
theorem B1941677 : Blo 574812 1941677 := bstep (se 3 (by rfl) ⟨364064, by rfl⟩ : syracuseStep 1941677 = 728129) B728129
theorem B1646801 : Blo 574812 1646801 := bstep (se 2 (by rfl) ⟨617550, by rfl⟩ : syracuseStep 1646801 = 1235101) B1235101
theorem B1941731 : Blo 574812 1941731 := bstep (se 1 (by rfl) ⟨1456298, by rfl⟩ : syracuseStep 1941731 = 2912597) B2912597
theorem B1974577 : Blo 574812 1974577 := bstep (se 2 (by rfl) ⟨740466, by rfl⟩ : syracuseStep 1974577 = 1480933) B1480933
theorem B1646993 : Blo 574812 1646993 := bstep (se 2 (by rfl) ⟨617622, by rfl⟩ : syracuseStep 1646993 = 1235245) B1235245
theorem B1942001 : Blo 574812 1942001 := bstep (se 2 (by rfl) ⟨728250, by rfl⟩ : syracuseStep 1942001 = 1456501) B1456501
theorem B729587 : Blo 574812 729587 := bstep (se 1 (by rfl) ⟨547190, by rfl⟩ : syracuseStep 729587 = 1094381) B1094381
theorem B3121699 : Blo 574812 3121699 := bstep (se 1 (by rfl) ⟨2341274, by rfl⟩ : syracuseStep 3121699 = 4682549) B4682549
theorem B1974851 : Blo 574812 1974851 := bstep (se 1 (by rfl) ⟨1481138, by rfl⟩ : syracuseStep 1974851 = 2962277) B2962277
theorem B2925233 : Blo 574812 2925233 := bstep (se 2 (by rfl) ⟨1096962, by rfl⟩ : syracuseStep 2925233 = 2193925) B2193925
theorem B5907269 : Blo 574812 5907269 := bstep (se 4 (by rfl) ⟨553806, by rfl⟩ : syracuseStep 5907269 = 1107613) B1107613
theorem B1942541 : Blo 574812 1942541 := bstep (se 3 (by rfl) ⟨364226, by rfl⟩ : syracuseStep 1942541 = 728453) B728453
theorem B1942595 : Blo 574812 1942595 := bstep (se 1 (by rfl) ⟨1456946, by rfl⟩ : syracuseStep 1942595 = 2913893) B2913893
theorem B926819 : Blo 574812 926819 := bstep (se 1 (by rfl) ⟨695114, by rfl⟩ : syracuseStep 926819 = 1390229) B1390229
theorem B730291 : Blo 574812 730291 := bstep (se 1 (by rfl) ⟨547718, by rfl⟩ : syracuseStep 730291 = 1095437) B1095437
theorem B1844461 : Blo 574812 1844461 := bstep (se 3 (by rfl) ⟨345836, by rfl⟩ : syracuseStep 1844461 = 691673) B691673
theorem B2467057 : Blo 574812 2467057 := bstep (se 2 (by rfl) ⟨925146, by rfl⟩ : syracuseStep 2467057 = 1850293) B1850293
theorem B730387 : Blo 574812 730387 := bstep (se 1 (by rfl) ⟨547790, by rfl⟩ : syracuseStep 730387 = 1095581) B1095581
theorem B927011 : Blo 574812 927011 := bstep (se 1 (by rfl) ⟨695258, by rfl⟩ : syracuseStep 927011 = 1390517) B1390517
theorem B1942865 : Blo 574812 1942865 := bstep (se 2 (by rfl) ⟨728574, by rfl⟩ : syracuseStep 1942865 = 1457149) B1457149
theorem B1647985 : Blo 574812 1647985 := bstep (se 2 (by rfl) ⟨617994, by rfl⟩ : syracuseStep 1647985 = 1235989) B1235989
theorem B1385923 : Blo 574812 1385923 := bstep (se 1 (by rfl) ⟨1039442, by rfl⟩ : syracuseStep 1385923 = 2078885) B2078885
theorem B1877617 : Blo 574812 1877617 := bstep (se 2 (by rfl) ⟨704106, by rfl⟩ : syracuseStep 1877617 = 1408213) B1408213
theorem B1648259 : Blo 574812 1648259 := bstep (se 1 (by rfl) ⟨1236194, by rfl⟩ : syracuseStep 1648259 = 2472389) B2472389
theorem B1844963 : Blo 574812 1844963 := bstep (se 1 (by rfl) ⟨1383722, by rfl⟩ : syracuseStep 1844963 = 2767445) B2767445
theorem B730883 : Blo 574812 730883 := bstep (se 1 (by rfl) ⟨548162, by rfl⟩ : syracuseStep 730883 = 1096325) B1096325
theorem B4007693 : Blo 574812 4007693 := bstep (se 3 (by rfl) ⟨751442, by rfl⟩ : syracuseStep 4007693 = 1502885) B1502885
theorem B3516173 : Blo 574812 3516173 := bstep (se 3 (by rfl) ⟨659282, by rfl⟩ : syracuseStep 3516173 = 1318565) B1318565
theorem B6235957 : Blo 574812 6235957 := bstep (se 5 (by rfl) ⟨292310, by rfl⟩ : syracuseStep 6235957 = 584621) B584621
theorem B1943405 : Blo 574812 1943405 := bstep (se 3 (by rfl) ⟨364388, by rfl⟩ : syracuseStep 1943405 = 728777) B728777
theorem B14788493 : Blo 574812 14788493 := bstep (se 3 (by rfl) ⟨2772842, by rfl⟩ : syracuseStep 14788493 = 5545685) B5545685
theorem B3286925 : Blo 574812 3286925 := bstep (se 3 (by rfl) ⟨616298, by rfl⟩ : syracuseStep 3286925 = 1232597) B1232597
theorem B1943459 : Blo 574812 1943459 := bstep (se 1 (by rfl) ⟨1457594, by rfl⟩ : syracuseStep 1943459 = 2915189) B2915189
theorem B1386499 : Blo 574812 1386499 := bstep (se 1 (by rfl) ⟨1039874, by rfl⟩ : syracuseStep 1386499 = 2079749) B2079749
theorem B862241 : Blo 574812 862241 := bstep (se 2 (by rfl) ⟨323340, by rfl⟩ : syracuseStep 862241 = 646681) B646681
theorem B862259 : Blo 574812 862259 := bstep (se 1 (by rfl) ⟨646694, by rfl⟩ : syracuseStep 862259 = 1293389) B1293389
theorem B862289 : Blo 574812 862289 := bstep (se 2 (by rfl) ⟨323358, by rfl⟩ : syracuseStep 862289 = 646717) B646717
theorem B862307 : Blo 574812 862307 := bstep (se 1 (by rfl) ⟨646730, by rfl⟩ : syracuseStep 862307 = 1293461) B1293461
theorem B2926691 : Blo 574812 2926691 := bstep (se 1 (by rfl) ⟨2195018, by rfl⟩ : syracuseStep 2926691 = 4390037) B4390037
theorem B862337 : Blo 574812 862337 := bstep (se 2 (by rfl) ⟨323376, by rfl⟩ : syracuseStep 862337 = 646753) B646753
theorem B862355 : Blo 574812 862355 := bstep (se 1 (by rfl) ⟨646766, by rfl⟩ : syracuseStep 862355 = 1293533) B1293533
theorem B862385 : Blo 574812 862385 := bstep (se 2 (by rfl) ⟨323394, by rfl⟩ : syracuseStep 862385 = 646789) B646789
theorem B1943729 : Blo 574812 1943729 := bstep (se 2 (by rfl) ⟨728898, by rfl⟩ : syracuseStep 1943729 = 1457797) B1457797
theorem B862403 : Blo 574812 862403 := bstep (se 1 (by rfl) ⟨646802, by rfl⟩ : syracuseStep 862403 = 1293605) B1293605
theorem B862433 : Blo 574812 862433 := bstep (se 2 (by rfl) ⟨323412, by rfl⟩ : syracuseStep 862433 = 646825) B646825
theorem B862451 : Blo 574812 862451 := bstep (se 1 (by rfl) ⟨646838, by rfl⟩ : syracuseStep 862451 = 1293677) B1293677
theorem B4368653 : Blo 574812 4368653 := bstep (se 3 (by rfl) ⟨819122, by rfl⟩ : syracuseStep 4368653 = 1638245) B1638245
theorem B862481 : Blo 574812 862481 := bstep (se 2 (by rfl) ⟨323430, by rfl⟩ : syracuseStep 862481 = 646861) B646861
theorem B862499 : Blo 574812 862499 := bstep (se 1 (by rfl) ⟨646874, by rfl⟩ : syracuseStep 862499 = 1293749) B1293749
theorem B1091875 : Blo 574812 1091875 := bstep (se 1 (by rfl) ⟨818906, by rfl⟩ : syracuseStep 1091875 = 1637813) B1637813
theorem B862529 : Blo 574812 862529 := bstep (se 2 (by rfl) ⟨323448, by rfl⟩ : syracuseStep 862529 = 646897) B646897
theorem B862547 : Blo 574812 862547 := bstep (se 1 (by rfl) ⟨646910, by rfl⟩ : syracuseStep 862547 = 1293821) B1293821
theorem B862577 : Blo 574812 862577 := bstep (se 2 (by rfl) ⟨323466, by rfl⟩ : syracuseStep 862577 = 646933) B646933
theorem B862595 : Blo 574812 862595 := bstep (se 1 (by rfl) ⟨646946, by rfl⟩ : syracuseStep 862595 = 1293893) B1293893
theorem B1386883 : Blo 574812 1386883 := bstep (se 1 (by rfl) ⟨1040162, by rfl⟩ : syracuseStep 1386883 = 2080325) B2080325
theorem B862625 : Blo 574812 862625 := bstep (se 2 (by rfl) ⟨323484, by rfl⟩ : syracuseStep 862625 = 646969) B646969
theorem B862643 : Blo 574812 862643 := bstep (se 1 (by rfl) ⟨646982, by rfl⟩ : syracuseStep 862643 = 1293965) B1293965
theorem B1092035 : Blo 574812 1092035 := bstep (se 1 (by rfl) ⟨819026, by rfl⟩ : syracuseStep 1092035 = 1638053) B1638053
theorem B731587 : Blo 574812 731587 := bstep (se 1 (by rfl) ⟨548690, by rfl⟩ : syracuseStep 731587 = 1097381) B1097381
theorem B862673 : Blo 574812 862673 := bstep (se 2 (by rfl) ⟨323502, by rfl⟩ : syracuseStep 862673 = 647005) B647005
theorem B862691 : Blo 574812 862691 := bstep (se 1 (by rfl) ⟨647018, by rfl⟩ : syracuseStep 862691 = 1294037) B1294037
theorem B862721 : Blo 574812 862721 := bstep (se 2 (by rfl) ⟨323520, by rfl⟩ : syracuseStep 862721 = 647041) B647041
theorem B862739 : Blo 574812 862739 := bstep (se 1 (by rfl) ⟨647054, by rfl⟩ : syracuseStep 862739 = 1294109) B1294109
theorem B731683 : Blo 574812 731683 := bstep (se 1 (by rfl) ⟨548762, by rfl⟩ : syracuseStep 731683 = 1097525) B1097525
theorem B862769 : Blo 574812 862769 := bstep (se 2 (by rfl) ⟨323538, by rfl⟩ : syracuseStep 862769 = 647077) B647077
theorem B862787 : Blo 574812 862787 := bstep (se 1 (by rfl) ⟨647090, by rfl⟩ : syracuseStep 862787 = 1294181) B1294181
theorem B862817 : Blo 574812 862817 := bstep (se 2 (by rfl) ⟨323556, by rfl⟩ : syracuseStep 862817 = 647113) B647113
theorem B3943025 : Blo 574812 3943025 := bstep (se 2 (by rfl) ⟨1478634, by rfl⟩ : syracuseStep 3943025 = 2957269) B2957269
theorem B862835 : Blo 574812 862835 := bstep (se 1 (by rfl) ⟨647126, by rfl⟩ : syracuseStep 862835 = 1294253) B1294253
theorem B862865 : Blo 574812 862865 := bstep (se 2 (by rfl) ⟨323574, by rfl⟩ : syracuseStep 862865 = 647149) B647149
theorem B862883 : Blo 574812 862883 := bstep (se 1 (by rfl) ⟨647162, by rfl⟩ : syracuseStep 862883 = 1294325) B1294325
theorem B862913 : Blo 574812 862913 := bstep (se 2 (by rfl) ⟨323592, by rfl⟩ : syracuseStep 862913 = 647185) B647185
theorem B1944269 : Blo 574812 1944269 := bstep (se 3 (by rfl) ⟨364550, by rfl⟩ : syracuseStep 1944269 = 729101) B729101
theorem B862931 : Blo 574812 862931 := bstep (se 1 (by rfl) ⟨647198, by rfl⟩ : syracuseStep 862931 = 1294397) B1294397
theorem B862961 : Blo 574812 862961 := bstep (se 2 (by rfl) ⟨323610, by rfl⟩ : syracuseStep 862961 = 647221) B647221
theorem B862979 : Blo 574812 862979 := bstep (se 1 (by rfl) ⟨647234, by rfl⟩ : syracuseStep 862979 = 1294469) B1294469
theorem B1944323 : Blo 574812 1944323 := bstep (se 1 (by rfl) ⟨1458242, by rfl⟩ : syracuseStep 1944323 = 2916485) B2916485
theorem B863009 : Blo 574812 863009 := bstep (se 2 (by rfl) ⟨323628, by rfl⟩ : syracuseStep 863009 = 647257) B647257
theorem B863027 : Blo 574812 863027 := bstep (se 1 (by rfl) ⟨647270, by rfl⟩ : syracuseStep 863027 = 1294541) B1294541
theorem B863057 : Blo 574812 863057 := bstep (se 2 (by rfl) ⟨323646, by rfl⟩ : syracuseStep 863057 = 647293) B647293
theorem B863075 : Blo 574812 863075 := bstep (se 1 (by rfl) ⟨647306, by rfl⟩ : syracuseStep 863075 = 1294613) B1294613
theorem B863105 : Blo 574812 863105 := bstep (se 2 (by rfl) ⟨323664, by rfl⟩ : syracuseStep 863105 = 647329) B647329
theorem B2927501 : Blo 574812 2927501 := bstep (se 3 (by rfl) ⟨548906, by rfl⟩ : syracuseStep 2927501 = 1097813) B1097813
theorem B863123 : Blo 574812 863123 := bstep (se 1 (by rfl) ⟨647342, by rfl⟩ : syracuseStep 863123 = 1294685) B1294685
theorem B863153 : Blo 574812 863153 := bstep (se 2 (by rfl) ⟨323682, by rfl⟩ : syracuseStep 863153 = 647365) B647365
theorem B863171 : Blo 574812 863171 := bstep (se 1 (by rfl) ⟨647378, by rfl⟩ : syracuseStep 863171 = 1294757) B1294757
theorem B2075597 : Blo 574812 2075597 := bstep (se 3 (by rfl) ⟨389174, by rfl⟩ : syracuseStep 2075597 = 778349) B778349
theorem B863201 : Blo 574812 863201 := bstep (se 2 (by rfl) ⟨323700, by rfl⟩ : syracuseStep 863201 = 647401) B647401
theorem B863219 : Blo 574812 863219 := bstep (se 1 (by rfl) ⟨647414, by rfl⟩ : syracuseStep 863219 = 1294829) B1294829
theorem B863249 : Blo 574812 863249 := bstep (se 2 (by rfl) ⟨323718, by rfl⟩ : syracuseStep 863249 = 647437) B647437
theorem B1944593 : Blo 574812 1944593 := bstep (se 2 (by rfl) ⟨729222, by rfl⟩ : syracuseStep 1944593 = 1458445) B1458445
theorem B732179 : Blo 574812 732179 := bstep (se 1 (by rfl) ⟨549134, by rfl⟩ : syracuseStep 732179 = 1098269) B1098269
theorem B863267 : Blo 574812 863267 := bstep (se 1 (by rfl) ⟨647450, by rfl⟩ : syracuseStep 863267 = 1294901) B1294901
theorem B1846307 : Blo 574812 1846307 := bstep (se 1 (by rfl) ⟨1384730, by rfl⟩ : syracuseStep 1846307 = 2769461) B2769461
theorem B863297 : Blo 574812 863297 := bstep (se 2 (by rfl) ⟨323736, by rfl⟩ : syracuseStep 863297 = 647473) B647473
theorem B863315 : Blo 574812 863315 := bstep (se 1 (by rfl) ⟨647486, by rfl⟩ : syracuseStep 863315 = 1294973) B1294973
theorem B863345 : Blo 574812 863345 := bstep (se 2 (by rfl) ⟨323754, by rfl⟩ : syracuseStep 863345 = 647509) B647509
theorem B863363 : Blo 574812 863363 := bstep (se 1 (by rfl) ⟨647522, by rfl⟩ : syracuseStep 863363 = 1295045) B1295045
theorem B863393 : Blo 574812 863393 := bstep (se 2 (by rfl) ⟨323772, by rfl⟩ : syracuseStep 863393 = 647545) B647545
theorem B863411 : Blo 574812 863411 := bstep (se 1 (by rfl) ⟨647558, by rfl⟩ : syracuseStep 863411 = 1295117) B1295117
theorem B863441 : Blo 574812 863441 := bstep (se 2 (by rfl) ⟨323790, by rfl⟩ : syracuseStep 863441 = 647581) B647581
theorem B1387729 : Blo 574812 1387729 := bstep (se 2 (by rfl) ⟨520398, by rfl⟩ : syracuseStep 1387729 = 1040797) B1040797
theorem B2764003 : Blo 574812 2764003 := bstep (se 1 (by rfl) ⟨2073002, by rfl⟩ : syracuseStep 2764003 = 4146005) B4146005
theorem B863459 : Blo 574812 863459 := bstep (se 1 (by rfl) ⟨647594, by rfl⟩ : syracuseStep 863459 = 1295189) B1295189
theorem B863489 : Blo 574812 863489 := bstep (se 2 (by rfl) ⟨323808, by rfl⟩ : syracuseStep 863489 = 647617) B647617
theorem B863507 : Blo 574812 863507 := bstep (se 1 (by rfl) ⟨647630, by rfl⟩ : syracuseStep 863507 = 1295261) B1295261
theorem B863537 : Blo 574812 863537 := bstep (se 2 (by rfl) ⟨323826, by rfl⟩ : syracuseStep 863537 = 647653) B647653
theorem B863555 : Blo 574812 863555 := bstep (se 1 (by rfl) ⟨647666, by rfl⟩ : syracuseStep 863555 = 1295333) B1295333
theorem B863585 : Blo 574812 863585 := bstep (se 2 (by rfl) ⟨323844, by rfl⟩ : syracuseStep 863585 = 647689) B647689
theorem B863603 : Blo 574812 863603 := bstep (se 1 (by rfl) ⟨647702, by rfl⟩ : syracuseStep 863603 = 1295405) B1295405
theorem B863633 : Blo 574812 863633 := bstep (se 2 (by rfl) ⟨323862, by rfl⟩ : syracuseStep 863633 = 647725) B647725
theorem B863651 : Blo 574812 863651 := bstep (se 1 (by rfl) ⟨647738, by rfl⟩ : syracuseStep 863651 = 1295477) B1295477
theorem B863681 : Blo 574812 863681 := bstep (se 2 (by rfl) ⟨323880, by rfl⟩ : syracuseStep 863681 = 647761) B647761
theorem B863699 : Blo 574812 863699 := bstep (se 1 (by rfl) ⟨647774, by rfl⟩ : syracuseStep 863699 = 1295549) B1295549
theorem B1093105 : Blo 574812 1093105 := bstep (se 2 (by rfl) ⟨409914, by rfl⟩ : syracuseStep 1093105 = 819829) B819829
theorem B863729 : Blo 574812 863729 := bstep (se 2 (by rfl) ⟨323898, by rfl⟩ : syracuseStep 863729 = 647797) B647797
theorem B863747 : Blo 574812 863747 := bstep (se 1 (by rfl) ⟨647810, by rfl⟩ : syracuseStep 863747 = 1295621) B1295621
theorem B4435469 : Blo 574812 4435469 := bstep (se 3 (by rfl) ⟨831650, by rfl⟩ : syracuseStep 4435469 = 1663301) B1663301
theorem B863777 : Blo 574812 863777 := bstep (se 2 (by rfl) ⟨323916, by rfl⟩ : syracuseStep 863777 = 647833) B647833
theorem B1945133 : Blo 574812 1945133 := bstep (se 3 (by rfl) ⟨364712, by rfl⟩ : syracuseStep 1945133 = 729425) B729425
theorem B863795 : Blo 574812 863795 := bstep (se 1 (by rfl) ⟨647846, by rfl⟩ : syracuseStep 863795 = 1295693) B1295693
theorem B3124813 : Blo 574812 3124813 := bstep (se 3 (by rfl) ⟨585902, by rfl⟩ : syracuseStep 3124813 = 1171805) B1171805
theorem B863825 : Blo 574812 863825 := bstep (se 2 (by rfl) ⟨323934, by rfl⟩ : syracuseStep 863825 = 647869) B647869
theorem B863843 : Blo 574812 863843 := bstep (se 1 (by rfl) ⟨647882, by rfl⟩ : syracuseStep 863843 = 1295765) B1295765
theorem B1945187 : Blo 574812 1945187 := bstep (se 1 (by rfl) ⟨1458890, by rfl⟩ : syracuseStep 1945187 = 2917781) B2917781
theorem B22163057 : Blo 574812 22163057 := bstep (se 2 (by rfl) ⟨8311146, by rfl⟩ : syracuseStep 22163057 = 16622293) B16622293
theorem B863873 : Blo 574812 863873 := bstep (se 2 (by rfl) ⟨323952, by rfl⟩ : syracuseStep 863873 = 647905) B647905
theorem B863891 : Blo 574812 863891 := bstep (se 1 (by rfl) ⟨647918, by rfl⟩ : syracuseStep 863891 = 1295837) B1295837
theorem B863921 : Blo 574812 863921 := bstep (se 2 (by rfl) ⟨323970, by rfl⟩ : syracuseStep 863921 = 647941) B647941
theorem B863939 : Blo 574812 863939 := bstep (se 1 (by rfl) ⟨647954, by rfl⟩ : syracuseStep 863939 = 1295909) B1295909
theorem B1683149 : Blo 574812 1683149 := bstep (se 3 (by rfl) ⟨315590, by rfl⟩ : syracuseStep 1683149 = 631181) B631181
theorem B863969 : Blo 574812 863969 := bstep (se 2 (by rfl) ⟨323988, by rfl⟩ : syracuseStep 863969 = 647977) B647977
theorem B863987 : Blo 574812 863987 := bstep (se 1 (by rfl) ⟨647990, by rfl⟩ : syracuseStep 863987 = 1295981) B1295981
theorem B864017 : Blo 574812 864017 := bstep (se 2 (by rfl) ⟨324006, by rfl⟩ : syracuseStep 864017 = 648013) B648013
theorem B864035 : Blo 574812 864035 := bstep (se 1 (by rfl) ⟨648026, by rfl⟩ : syracuseStep 864035 = 1296053) B1296053
theorem B864065 : Blo 574812 864065 := bstep (se 2 (by rfl) ⟨324024, by rfl⟩ : syracuseStep 864065 = 648049) B648049
theorem B864083 : Blo 574812 864083 := bstep (se 1 (by rfl) ⟨648062, by rfl⟩ : syracuseStep 864083 = 1296125) B1296125
theorem B864113 : Blo 574812 864113 := bstep (se 2 (by rfl) ⟨324042, by rfl⟩ : syracuseStep 864113 = 648085) B648085
theorem B1945457 : Blo 574812 1945457 := bstep (se 2 (by rfl) ⟨729546, by rfl⟩ : syracuseStep 1945457 = 1459093) B1459093
theorem B864131 : Blo 574812 864131 := bstep (se 1 (by rfl) ⟨648098, by rfl⟩ : syracuseStep 864131 = 1296197) B1296197
theorem B864161 : Blo 574812 864161 := bstep (se 2 (by rfl) ⟨324060, by rfl⟩ : syracuseStep 864161 = 648121) B648121
theorem B864179 : Blo 574812 864179 := bstep (se 1 (by rfl) ⟨648134, by rfl⟩ : syracuseStep 864179 = 1296269) B1296269
theorem B864209 : Blo 574812 864209 := bstep (se 2 (by rfl) ⟨324078, by rfl⟩ : syracuseStep 864209 = 648157) B648157
theorem B864227 : Blo 574812 864227 := bstep (se 1 (by rfl) ⟨648170, by rfl⟩ : syracuseStep 864227 = 1296341) B1296341
theorem B1847281 : Blo 574812 1847281 := bstep (se 2 (by rfl) ⟨692730, by rfl⟩ : syracuseStep 1847281 = 1385461) B1385461
theorem B864257 : Blo 574812 864257 := bstep (se 2 (by rfl) ⟨324096, by rfl⟩ : syracuseStep 864257 = 648193) B648193
theorem B864275 : Blo 574812 864275 := bstep (se 1 (by rfl) ⟨648206, by rfl⟩ : syracuseStep 864275 = 1296413) B1296413
theorem B864305 : Blo 574812 864305 := bstep (se 2 (by rfl) ⟨324114, by rfl⟩ : syracuseStep 864305 = 648229) B648229
theorem B864323 : Blo 574812 864323 := bstep (se 1 (by rfl) ⟨648242, by rfl⟩ : syracuseStep 864323 = 1296485) B1296485
theorem B3289157 : Blo 574812 3289157 := bstep (se 4 (by rfl) ⟨308358, by rfl⟩ : syracuseStep 3289157 = 616717) B616717
theorem B864353 : Blo 574812 864353 := bstep (se 2 (by rfl) ⟨324132, by rfl⟩ : syracuseStep 864353 = 648265) B648265
theorem B864371 : Blo 574812 864371 := bstep (se 1 (by rfl) ⟨648278, by rfl⟩ : syracuseStep 864371 = 1296557) B1296557
theorem B864401 : Blo 574812 864401 := bstep (se 2 (by rfl) ⟨324150, by rfl⟩ : syracuseStep 864401 = 648301) B648301
theorem B864419 : Blo 574812 864419 := bstep (se 1 (by rfl) ⟨648314, by rfl⟩ : syracuseStep 864419 = 1296629) B1296629
theorem B864449 : Blo 574812 864449 := bstep (se 2 (by rfl) ⟨324168, by rfl⟩ : syracuseStep 864449 = 648337) B648337
theorem B864467 : Blo 574812 864467 := bstep (se 1 (by rfl) ⟨648350, by rfl⟩ : syracuseStep 864467 = 1296701) B1296701
theorem B2470115 : Blo 574812 2470115 := bstep (se 1 (by rfl) ⟨1852586, by rfl⟩ : syracuseStep 2470115 = 3705173) B3705173
theorem B864497 : Blo 574812 864497 := bstep (se 2 (by rfl) ⟨324186, by rfl⟩ : syracuseStep 864497 = 648373) B648373
theorem B1847537 : Blo 574812 1847537 := bstep (se 2 (by rfl) ⟨692826, by rfl⟩ : syracuseStep 1847537 = 1385653) B1385653
theorem B864515 : Blo 574812 864515 := bstep (se 1 (by rfl) ⟨648386, by rfl⟩ : syracuseStep 864515 = 1296773) B1296773
theorem B864545 : Blo 574812 864545 := bstep (se 2 (by rfl) ⟨324204, by rfl⟩ : syracuseStep 864545 = 648409) B648409
theorem B864563 : Blo 574812 864563 := bstep (se 1 (by rfl) ⟨648422, by rfl⟩ : syracuseStep 864563 = 1296845) B1296845
theorem B864593 : Blo 574812 864593 := bstep (se 2 (by rfl) ⟨324222, by rfl⟩ : syracuseStep 864593 = 648445) B648445
theorem B864611 : Blo 574812 864611 := bstep (se 1 (by rfl) ⟨648458, by rfl⟩ : syracuseStep 864611 = 1296917) B1296917
theorem B864641 : Blo 574812 864641 := bstep (se 2 (by rfl) ⟨324240, by rfl⟩ : syracuseStep 864641 = 648481) B648481
theorem B1945997 : Blo 574812 1945997 := bstep (se 3 (by rfl) ⟨364874, by rfl⟩ : syracuseStep 1945997 = 729749) B729749
theorem B864659 : Blo 574812 864659 := bstep (se 1 (by rfl) ⟨648494, by rfl⟩ : syracuseStep 864659 = 1296989) B1296989
theorem B864689 : Blo 574812 864689 := bstep (se 2 (by rfl) ⟨324258, by rfl⟩ : syracuseStep 864689 = 648517) B648517
theorem B864707 : Blo 574812 864707 := bstep (se 1 (by rfl) ⟨648530, by rfl⟩ : syracuseStep 864707 = 1297061) B1297061
theorem B1946051 : Blo 574812 1946051 := bstep (se 1 (by rfl) ⟨1459538, by rfl⟩ : syracuseStep 1946051 = 2919077) B2919077
theorem B864737 : Blo 574812 864737 := bstep (se 2 (by rfl) ⟨324276, by rfl⟩ : syracuseStep 864737 = 648553) B648553
theorem B864755 : Blo 574812 864755 := bstep (se 1 (by rfl) ⟨648566, by rfl⟩ : syracuseStep 864755 = 1297133) B1297133
theorem B7909901 : Blo 574812 7909901 := bstep (se 3 (by rfl) ⟨1483106, by rfl⟩ : syracuseStep 7909901 = 2966213) B2966213
theorem B1094161 : Blo 574812 1094161 := bstep (se 2 (by rfl) ⟨410310, by rfl⟩ : syracuseStep 1094161 = 820621) B820621
theorem B864785 : Blo 574812 864785 := bstep (se 2 (by rfl) ⟨324294, by rfl⟩ : syracuseStep 864785 = 648589) B648589
theorem B864803 : Blo 574812 864803 := bstep (se 1 (by rfl) ⟨648602, by rfl⟩ : syracuseStep 864803 = 1297205) B1297205
theorem B9351733 : Blo 574812 9351733 := bstep (se 5 (by rfl) ⟨438362, by rfl⟩ : syracuseStep 9351733 = 876725) B876725
theorem B864833 : Blo 574812 864833 := bstep (se 2 (by rfl) ⟨324312, by rfl⟩ : syracuseStep 864833 = 648625) B648625
theorem B864851 : Blo 574812 864851 := bstep (se 1 (by rfl) ⟨648638, by rfl⟩ : syracuseStep 864851 = 1297277) B1297277
theorem B864881 : Blo 574812 864881 := bstep (se 2 (by rfl) ⟨324330, by rfl⟩ : syracuseStep 864881 = 648661) B648661
theorem B864899 : Blo 574812 864899 := bstep (se 1 (by rfl) ⟨648674, by rfl⟩ : syracuseStep 864899 = 1297349) B1297349
theorem B7385741 : Blo 574812 7385741 := bstep (se 3 (by rfl) ⟨1384826, by rfl⟩ : syracuseStep 7385741 = 2769653) B2769653
theorem B864929 : Blo 574812 864929 := bstep (se 2 (by rfl) ⟨324348, by rfl⟩ : syracuseStep 864929 = 648697) B648697
theorem B864947 : Blo 574812 864947 := bstep (se 1 (by rfl) ⟨648710, by rfl⟩ : syracuseStep 864947 = 1297421) B1297421
theorem B864977 : Blo 574812 864977 := bstep (se 2 (by rfl) ⟨324366, by rfl⟩ : syracuseStep 864977 = 648733) B648733
theorem B1946321 : Blo 574812 1946321 := bstep (se 2 (by rfl) ⟨729870, by rfl⟩ : syracuseStep 1946321 = 1459741) B1459741
theorem B864995 : Blo 574812 864995 := bstep (se 1 (by rfl) ⟨648746, by rfl⟩ : syracuseStep 864995 = 1297493) B1297493
theorem B3289841 : Blo 574812 3289841 := bstep (se 2 (by rfl) ⟨1233690, by rfl⟩ : syracuseStep 3289841 = 2467381) B2467381
theorem B865025 : Blo 574812 865025 := bstep (se 2 (by rfl) ⟨324384, by rfl⟩ : syracuseStep 865025 = 648769) B648769
theorem B865043 : Blo 574812 865043 := bstep (se 1 (by rfl) ⟨648782, by rfl⟩ : syracuseStep 865043 = 1297565) B1297565
theorem B865073 : Blo 574812 865073 := bstep (se 2 (by rfl) ⟨324402, by rfl⟩ : syracuseStep 865073 = 648805) B648805
theorem B865091 : Blo 574812 865091 := bstep (se 1 (by rfl) ⟨648818, by rfl⟩ : syracuseStep 865091 = 1297637) B1297637
theorem B865121 : Blo 574812 865121 := bstep (se 2 (by rfl) ⟨324420, by rfl⟩ : syracuseStep 865121 = 648841) B648841
theorem B865139 : Blo 574812 865139 := bstep (se 1 (by rfl) ⟨648854, by rfl⟩ : syracuseStep 865139 = 1297709) B1297709
theorem B865169 : Blo 574812 865169 := bstep (se 2 (by rfl) ⟨324438, by rfl⟩ : syracuseStep 865169 = 648877) B648877
theorem B1094563 : Blo 574812 1094563 := bstep (se 1 (by rfl) ⟨820922, by rfl⟩ : syracuseStep 1094563 = 1641845) B1641845
theorem B865187 : Blo 574812 865187 := bstep (se 1 (by rfl) ⟨648890, by rfl⟩ : syracuseStep 865187 = 1297781) B1297781
theorem B865217 : Blo 574812 865217 := bstep (se 2 (by rfl) ⟨324456, by rfl⟩ : syracuseStep 865217 = 648913) B648913
theorem B1455043 : Blo 574812 1455043 := bstep (se 1 (by rfl) ⟨1091282, by rfl⟩ : syracuseStep 1455043 = 2182565) B2182565
theorem B1094609 : Blo 574812 1094609 := bstep (se 2 (by rfl) ⟨410478, by rfl⟩ : syracuseStep 1094609 = 820957) B820957
theorem B865235 : Blo 574812 865235 := bstep (se 1 (by rfl) ⟨648926, by rfl⟩ : syracuseStep 865235 = 1297853) B1297853
theorem B865265 : Blo 574812 865265 := bstep (se 2 (by rfl) ⟨324474, by rfl⟩ : syracuseStep 865265 = 648949) B648949
theorem B865283 : Blo 574812 865283 := bstep (se 1 (by rfl) ⟨648962, by rfl⟩ : syracuseStep 865283 = 1297925) B1297925
theorem B865313 : Blo 574812 865313 := bstep (se 2 (by rfl) ⟨324492, by rfl⟩ : syracuseStep 865313 = 648985) B648985
theorem B865331 : Blo 574812 865331 := bstep (se 1 (by rfl) ⟨648998, by rfl⟩ : syracuseStep 865331 = 1297997) B1297997
theorem B1455185 : Blo 574812 1455185 := bstep (se 2 (by rfl) ⟨545694, by rfl⟩ : syracuseStep 1455185 = 1091389) B1091389
theorem B865361 : Blo 574812 865361 := bstep (se 2 (by rfl) ⟨324510, by rfl⟩ : syracuseStep 865361 = 649021) B649021
theorem B865379 : Blo 574812 865379 := bstep (se 1 (by rfl) ⟨649034, by rfl⟩ : syracuseStep 865379 = 1298069) B1298069
theorem B4371569 : Blo 574812 4371569 := bstep (se 2 (by rfl) ⟨1639338, by rfl⟩ : syracuseStep 4371569 = 3278677) B3278677
theorem B865409 : Blo 574812 865409 := bstep (se 2 (by rfl) ⟨324528, by rfl⟩ : syracuseStep 865409 = 649057) B649057
theorem B865427 : Blo 574812 865427 := bstep (se 1 (by rfl) ⟨649070, by rfl⟩ : syracuseStep 865427 = 1298141) B1298141
theorem B2766001 : Blo 574812 2766001 := bstep (se 2 (by rfl) ⟨1037250, by rfl⟩ : syracuseStep 2766001 = 2074501) B2074501
theorem B865457 : Blo 574812 865457 := bstep (se 2 (by rfl) ⟨324546, by rfl⟩ : syracuseStep 865457 = 649093) B649093
theorem B865475 : Blo 574812 865475 := bstep (se 1 (by rfl) ⟨649106, by rfl⟩ : syracuseStep 865475 = 1298213) B1298213
theorem B865505 : Blo 574812 865505 := bstep (se 2 (by rfl) ⟨324564, by rfl⟩ : syracuseStep 865505 = 649129) B649129
theorem B1946861 : Blo 574812 1946861 := bstep (se 3 (by rfl) ⟨365036, by rfl⟩ : syracuseStep 1946861 = 730073) B730073
theorem B1094897 : Blo 574812 1094897 := bstep (se 2 (by rfl) ⟨410586, by rfl⟩ : syracuseStep 1094897 = 821173) B821173
theorem B865523 : Blo 574812 865523 := bstep (se 1 (by rfl) ⟨649142, by rfl⟩ : syracuseStep 865523 = 1298285) B1298285
theorem B865553 : Blo 574812 865553 := bstep (se 2 (by rfl) ⟨324582, by rfl⟩ : syracuseStep 865553 = 649165) B649165
theorem B1946915 : Blo 574812 1946915 := bstep (se 1 (by rfl) ⟨1460186, by rfl⟩ : syracuseStep 1946915 = 2920373) B2920373
theorem B865571 : Blo 574812 865571 := bstep (se 1 (by rfl) ⟨649178, by rfl⟩ : syracuseStep 865571 = 1298357) B1298357
theorem B865601 : Blo 574812 865601 := bstep (se 2 (by rfl) ⟨324600, by rfl⟩ : syracuseStep 865601 = 649201) B649201
theorem B4666693 : Blo 574812 4666693 := bstep (se 4 (by rfl) ⟨437502, by rfl⟩ : syracuseStep 4666693 = 875005) B875005
theorem B1848653 : Blo 574812 1848653 := bstep (se 3 (by rfl) ⟨346622, by rfl⟩ : syracuseStep 1848653 = 693245) B693245
theorem B865619 : Blo 574812 865619 := bstep (se 1 (by rfl) ⟨649214, by rfl⟩ : syracuseStep 865619 = 1298429) B1298429
theorem B865649 : Blo 574812 865649 := bstep (se 2 (by rfl) ⟨324618, by rfl⟩ : syracuseStep 865649 = 649237) B649237
theorem B8336753 : Blo 574812 8336753 := bstep (se 2 (by rfl) ⟨3126282, by rfl⟩ : syracuseStep 8336753 = 6252565) B6252565
theorem B865667 : Blo 574812 865667 := bstep (se 1 (by rfl) ⟨649250, by rfl⟩ : syracuseStep 865667 = 1298501) B1298501
theorem B865697 : Blo 574812 865697 := bstep (se 2 (by rfl) ⟨324636, by rfl⟩ : syracuseStep 865697 = 649273) B649273
theorem B865715 : Blo 574812 865715 := bstep (se 1 (by rfl) ⟨649286, by rfl⟩ : syracuseStep 865715 = 1298573) B1298573
theorem B865745 : Blo 574812 865745 := bstep (se 2 (by rfl) ⟨324654, by rfl⟩ : syracuseStep 865745 = 649309) B649309
theorem B865763 : Blo 574812 865763 := bstep (se 1 (by rfl) ⟨649322, by rfl⟩ : syracuseStep 865763 = 1298645) B1298645
theorem B865793 : Blo 574812 865793 := bstep (se 2 (by rfl) ⟨324672, by rfl⟩ : syracuseStep 865793 = 649345) B649345
theorem B865811 : Blo 574812 865811 := bstep (se 1 (by rfl) ⟨649358, by rfl⟩ : syracuseStep 865811 = 1298717) B1298717
theorem B1947185 : Blo 574812 1947185 := bstep (se 2 (by rfl) ⟨730194, by rfl⟩ : syracuseStep 1947185 = 1460389) B1460389
theorem B865841 : Blo 574812 865841 := bstep (se 2 (by rfl) ⟨324690, by rfl⟩ : syracuseStep 865841 = 649381) B649381
theorem B865859 : Blo 574812 865859 := bstep (se 1 (by rfl) ⟨649394, by rfl⟩ : syracuseStep 865859 = 1298789) B1298789
theorem B5551685 : Blo 574812 5551685 := bstep (se 4 (by rfl) ⟨520470, by rfl⟩ : syracuseStep 5551685 = 1040941) B1040941
theorem B865889 : Blo 574812 865889 := bstep (se 2 (by rfl) ⟨324708, by rfl⟩ : syracuseStep 865889 = 649417) B649417
theorem B865907 : Blo 574812 865907 := bstep (se 1 (by rfl) ⟨649430, by rfl⟩ : syracuseStep 865907 = 1298861) B1298861
theorem B1554061 : Blo 574812 1554061 := bstep (se 3 (by rfl) ⟨291386, by rfl⟩ : syracuseStep 1554061 = 582773) B582773
theorem B865937 : Blo 574812 865937 := bstep (se 2 (by rfl) ⟨324726, by rfl⟩ : syracuseStep 865937 = 649453) B649453
theorem B865955 : Blo 574812 865955 := bstep (se 1 (by rfl) ⟨649466, by rfl⟩ : syracuseStep 865955 = 1298933) B1298933
theorem B865985 : Blo 574812 865985 := bstep (se 2 (by rfl) ⟨324744, by rfl⟩ : syracuseStep 865985 = 649489) B649489
theorem B866003 : Blo 574812 866003 := bstep (se 1 (by rfl) ⟨649502, by rfl⟩ : syracuseStep 866003 = 1299005) B1299005
theorem B866033 : Blo 574812 866033 := bstep (se 2 (by rfl) ⟨324762, by rfl⟩ : syracuseStep 866033 = 649525) B649525
theorem B866051 : Blo 574812 866051 := bstep (se 1 (by rfl) ⟨649538, by rfl⟩ : syracuseStep 866051 = 1299077) B1299077
theorem B866081 : Blo 574812 866081 := bstep (se 2 (by rfl) ⟨324780, by rfl⟩ : syracuseStep 866081 = 649561) B649561
theorem B866099 : Blo 574812 866099 := bstep (se 1 (by rfl) ⟨649574, by rfl⟩ : syracuseStep 866099 = 1299149) B1299149
theorem B866129 : Blo 574812 866129 := bstep (se 2 (by rfl) ⟨324798, by rfl⟩ : syracuseStep 866129 = 649597) B649597
theorem B866147 : Blo 574812 866147 := bstep (se 1 (by rfl) ⟨649610, by rfl⟩ : syracuseStep 866147 = 1299221) B1299221
theorem B866177 : Blo 574812 866177 := bstep (se 2 (by rfl) ⟨324816, by rfl⟩ : syracuseStep 866177 = 649633) B649633
theorem B866195 : Blo 574812 866195 := bstep (se 1 (by rfl) ⟨649646, by rfl⟩ : syracuseStep 866195 = 1299293) B1299293
theorem B866225 : Blo 574812 866225 := bstep (se 2 (by rfl) ⟨324834, by rfl⟩ : syracuseStep 866225 = 649669) B649669
theorem B1095619 : Blo 574812 1095619 := bstep (se 1 (by rfl) ⟨821714, by rfl⟩ : syracuseStep 1095619 = 1643429) B1643429
theorem B866243 : Blo 574812 866243 := bstep (se 1 (by rfl) ⟨649682, by rfl⟩ : syracuseStep 866243 = 1299365) B1299365
theorem B866273 : Blo 574812 866273 := bstep (se 2 (by rfl) ⟨324852, by rfl⟩ : syracuseStep 866273 = 649705) B649705
theorem B866291 : Blo 574812 866291 := bstep (se 1 (by rfl) ⟨649718, by rfl⟩ : syracuseStep 866291 = 1299437) B1299437
theorem B866321 : Blo 574812 866321 := bstep (se 2 (by rfl) ⟨324870, by rfl⟩ : syracuseStep 866321 = 649741) B649741
theorem B866339 : Blo 574812 866339 := bstep (se 1 (by rfl) ⟨649754, by rfl⟩ : syracuseStep 866339 = 1299509) B1299509
theorem B1456177 : Blo 574812 1456177 := bstep (se 2 (by rfl) ⟨546066, by rfl⟩ : syracuseStep 1456177 = 1092133) B1092133
theorem B2504753 : Blo 574812 2504753 := bstep (se 2 (by rfl) ⟨939282, by rfl⟩ : syracuseStep 2504753 = 1878565) B1878565
theorem B14956597 : Blo 574812 14956597 := bstep (se 5 (by rfl) ⟨701090, by rfl⟩ : syracuseStep 14956597 = 1402181) B1402181
theorem B866369 : Blo 574812 866369 := bstep (se 2 (by rfl) ⟨324888, by rfl⟩ : syracuseStep 866369 = 649777) B649777
theorem B1947725 : Blo 574812 1947725 := bstep (se 3 (by rfl) ⟨365198, by rfl⟩ : syracuseStep 1947725 = 730397) B730397
theorem B866387 : Blo 574812 866387 := bstep (se 1 (by rfl) ⟨649790, by rfl⟩ : syracuseStep 866387 = 1299581) B1299581
theorem B866417 : Blo 574812 866417 := bstep (se 2 (by rfl) ⟨324906, by rfl⟩ : syracuseStep 866417 = 649813) B649813
theorem B1947779 : Blo 574812 1947779 := bstep (se 1 (by rfl) ⟨1460834, by rfl⟩ : syracuseStep 1947779 = 2921669) B2921669
theorem B866435 : Blo 574812 866435 := bstep (se 1 (by rfl) ⟨649826, by rfl⟩ : syracuseStep 866435 = 1299653) B1299653
theorem B866465 : Blo 574812 866465 := bstep (se 2 (by rfl) ⟨324924, by rfl⟩ : syracuseStep 866465 = 649849) B649849
theorem B3291299 : Blo 574812 3291299 := bstep (se 1 (by rfl) ⟨2468474, by rfl⟩ : syracuseStep 3291299 = 4936949) B4936949
theorem B866483 : Blo 574812 866483 := bstep (se 1 (by rfl) ⟨649862, by rfl⟩ : syracuseStep 866483 = 1299725) B1299725
theorem B866513 : Blo 574812 866513 := bstep (se 2 (by rfl) ⟨324942, by rfl⟩ : syracuseStep 866513 = 649885) B649885
theorem B866531 : Blo 574812 866531 := bstep (se 1 (by rfl) ⟨649898, by rfl⟩ : syracuseStep 866531 = 1299797) B1299797
theorem B866561 : Blo 574812 866561 := bstep (se 2 (by rfl) ⟨324960, by rfl⟩ : syracuseStep 866561 = 649921) B649921
theorem B866579 : Blo 574812 866579 := bstep (se 1 (by rfl) ⟨649934, by rfl⟩ : syracuseStep 866579 = 1299869) B1299869
theorem B866609 : Blo 574812 866609 := bstep (se 2 (by rfl) ⟨324978, by rfl⟩ : syracuseStep 866609 = 649957) B649957
theorem B1456451 : Blo 574812 1456451 := bstep (se 1 (by rfl) ⟨1092338, by rfl⟩ : syracuseStep 1456451 = 2184677) B2184677
theorem B866627 : Blo 574812 866627 := bstep (se 1 (by rfl) ⟨649970, by rfl⟩ : syracuseStep 866627 = 1299941) B1299941
theorem B866657 : Blo 574812 866657 := bstep (se 2 (by rfl) ⟨324996, by rfl⟩ : syracuseStep 866657 = 649993) B649993
theorem B866675 : Blo 574812 866675 := bstep (se 1 (by rfl) ⟨650006, by rfl⟩ : syracuseStep 866675 = 1300013) B1300013
theorem B1096067 : Blo 574812 1096067 := bstep (se 1 (by rfl) ⟨822050, by rfl⟩ : syracuseStep 1096067 = 1644101) B1644101
theorem B1948049 : Blo 574812 1948049 := bstep (se 2 (by rfl) ⟨730518, by rfl⟩ : syracuseStep 1948049 = 1461037) B1461037
theorem B866705 : Blo 574812 866705 := bstep (se 2 (by rfl) ⟨325014, by rfl⟩ : syracuseStep 866705 = 650029) B650029
theorem B866723 : Blo 574812 866723 := bstep (se 1 (by rfl) ⟨650042, by rfl⟩ : syracuseStep 866723 = 1300085) B1300085
theorem B866753 : Blo 574812 866753 := bstep (se 2 (by rfl) ⟨325032, by rfl⟩ : syracuseStep 866753 = 650065) B650065
theorem B866771 : Blo 574812 866771 := bstep (se 1 (by rfl) ⟨650078, by rfl⟩ : syracuseStep 866771 = 1300157) B1300157
theorem B866801 : Blo 574812 866801 := bstep (se 2 (by rfl) ⟨325050, by rfl⟩ : syracuseStep 866801 = 650101) B650101
theorem B1456643 : Blo 574812 1456643 := bstep (se 1 (by rfl) ⟨1092482, by rfl⟩ : syracuseStep 1456643 = 2184965) B2184965
theorem B866819 : Blo 574812 866819 := bstep (se 1 (by rfl) ⟨650114, by rfl⟩ : syracuseStep 866819 = 1300229) B1300229
theorem B866849 : Blo 574812 866849 := bstep (se 2 (by rfl) ⟨325068, by rfl⟩ : syracuseStep 866849 = 650137) B650137
theorem B866867 : Blo 574812 866867 := bstep (se 1 (by rfl) ⟨650150, by rfl⟩ : syracuseStep 866867 = 1300301) B1300301
theorem B866897 : Blo 574812 866897 := bstep (se 2 (by rfl) ⟨325086, by rfl⟩ : syracuseStep 866897 = 650173) B650173
theorem B866915 : Blo 574812 866915 := bstep (se 1 (by rfl) ⟨650186, by rfl⟩ : syracuseStep 866915 = 1300373) B1300373
theorem B13318769 : Blo 574812 13318769 := bstep (se 2 (by rfl) ⟨4994538, by rfl⟩ : syracuseStep 13318769 = 9989077) B9989077
theorem B866945 : Blo 574812 866945 := bstep (se 2 (by rfl) ⟨325104, by rfl⟩ : syracuseStep 866945 = 650209) B650209
theorem B1849997 : Blo 574812 1849997 := bstep (se 3 (by rfl) ⟨346874, by rfl⟩ : syracuseStep 1849997 = 693749) B693749
theorem B866963 : Blo 574812 866963 := bstep (se 1 (by rfl) ⟨650222, by rfl⟩ : syracuseStep 866963 = 1300445) B1300445
theorem B3685027 : Blo 574812 3685027 := bstep (se 1 (by rfl) ⟨2763770, by rfl⟩ : syracuseStep 3685027 = 5527541) B5527541
theorem B1096355 : Blo 574812 1096355 := bstep (se 1 (by rfl) ⟨822266, by rfl⟩ : syracuseStep 1096355 = 1644533) B1644533
theorem B866993 : Blo 574812 866993 := bstep (se 2 (by rfl) ⟨325122, by rfl⟩ : syracuseStep 866993 = 650245) B650245
theorem B867011 : Blo 574812 867011 := bstep (se 1 (by rfl) ⟨650258, by rfl⟩ : syracuseStep 867011 = 1300517) B1300517
theorem B867041 : Blo 574812 867041 := bstep (se 2 (by rfl) ⟨325140, by rfl⟩ : syracuseStep 867041 = 650281) B650281
theorem B867059 : Blo 574812 867059 := bstep (se 1 (by rfl) ⟨650294, by rfl⟩ : syracuseStep 867059 = 1300589) B1300589
theorem B867089 : Blo 574812 867089 := bstep (se 2 (by rfl) ⟨325158, by rfl⟩ : syracuseStep 867089 = 650317) B650317
theorem B867107 : Blo 574812 867107 := bstep (se 1 (by rfl) ⟨650330, by rfl⟩ : syracuseStep 867107 = 1300661) B1300661
theorem B867137 : Blo 574812 867137 := bstep (se 2 (by rfl) ⟨325176, by rfl⟩ : syracuseStep 867137 = 650353) B650353
theorem B867155 : Blo 574812 867155 := bstep (se 1 (by rfl) ⟨650366, by rfl⟩ : syracuseStep 867155 = 1300733) B1300733
theorem B867185 : Blo 574812 867185 := bstep (se 2 (by rfl) ⟨325194, by rfl⟩ : syracuseStep 867185 = 650389) B650389
theorem B867203 : Blo 574812 867203 := bstep (se 1 (by rfl) ⟨650402, by rfl⟩ : syracuseStep 867203 = 1300805) B1300805
theorem B867233 : Blo 574812 867233 := bstep (se 2 (by rfl) ⟨325212, by rfl⟩ : syracuseStep 867233 = 650425) B650425
theorem B1948589 : Blo 574812 1948589 := bstep (se 3 (by rfl) ⟨365360, by rfl⟩ : syracuseStep 1948589 = 730721) B730721
theorem B867251 : Blo 574812 867251 := bstep (se 1 (by rfl) ⟨650438, by rfl⟩ : syracuseStep 867251 = 1300877) B1300877
theorem B867281 : Blo 574812 867281 := bstep (se 2 (by rfl) ⟨325230, by rfl⟩ : syracuseStep 867281 = 650461) B650461
theorem B1948643 : Blo 574812 1948643 := bstep (se 1 (by rfl) ⟨1461482, by rfl⟩ : syracuseStep 1948643 = 2922965) B2922965
theorem B867299 : Blo 574812 867299 := bstep (se 1 (by rfl) ⟨650474, by rfl⟩ : syracuseStep 867299 = 1300949) B1300949
theorem B867329 : Blo 574812 867329 := bstep (se 2 (by rfl) ⟨325248, by rfl⟩ : syracuseStep 867329 = 650497) B650497
theorem B867347 : Blo 574812 867347 := bstep (se 1 (by rfl) ⟨650510, by rfl⟩ : syracuseStep 867347 = 1301021) B1301021
theorem B867377 : Blo 574812 867377 := bstep (se 2 (by rfl) ⟨325266, by rfl⟩ : syracuseStep 867377 = 650533) B650533
theorem B1850435 : Blo 574812 1850435 := bstep (se 1 (by rfl) ⟨1387826, by rfl⟩ : syracuseStep 1850435 = 2775653) B2775653
theorem B867395 : Blo 574812 867395 := bstep (se 1 (by rfl) ⟨650546, by rfl⟩ : syracuseStep 867395 = 1301093) B1301093
theorem B867425 : Blo 574812 867425 := bstep (se 2 (by rfl) ⟨325284, by rfl⟩ : syracuseStep 867425 = 650569) B650569
theorem B1293425 : Blo 574812 1293425 := bstep (se 2 (by rfl) ⟨485034, by rfl⟩ : syracuseStep 1293425 = 970069) B970069
theorem B9845873 : Blo 574812 9845873 := bstep (se 2 (by rfl) ⟨3692202, by rfl⟩ : syracuseStep 9845873 = 7384405) B7384405
theorem B867443 : Blo 574812 867443 := bstep (se 1 (by rfl) ⟨650582, by rfl⟩ : syracuseStep 867443 = 1301165) B1301165
theorem B1293443 : Blo 574812 1293443 := bstep (se 1 (by rfl) ⟨970082, by rfl⟩ : syracuseStep 1293443 = 1940165) B1940165
theorem B867473 : Blo 574812 867473 := bstep (se 2 (by rfl) ⟨325302, by rfl⟩ : syracuseStep 867473 = 650605) B650605
theorem B867491 : Blo 574812 867491 := bstep (se 1 (by rfl) ⟨650618, by rfl⟩ : syracuseStep 867491 = 1301237) B1301237
theorem B867521 : Blo 574812 867521 := bstep (se 2 (by rfl) ⟨325320, by rfl⟩ : syracuseStep 867521 = 650641) B650641
theorem B867539 : Blo 574812 867539 := bstep (se 1 (by rfl) ⟨650654, by rfl⟩ : syracuseStep 867539 = 1301309) B1301309
theorem B1948913 : Blo 574812 1948913 := bstep (se 2 (by rfl) ⟨730842, by rfl⟩ : syracuseStep 1948913 = 1461685) B1461685
theorem B867569 : Blo 574812 867569 := bstep (se 2 (by rfl) ⟨325338, by rfl⟩ : syracuseStep 867569 = 650677) B650677
theorem B867587 : Blo 574812 867587 := bstep (se 1 (by rfl) ⟨650690, by rfl⟩ : syracuseStep 867587 = 1301381) B1301381
theorem B867617 : Blo 574812 867617 := bstep (se 2 (by rfl) ⟨325356, by rfl⟩ : syracuseStep 867617 = 650713) B650713
theorem B998705 : Blo 574812 998705 := bstep (se 2 (by rfl) ⟨374514, by rfl⟩ : syracuseStep 998705 = 749029) B749029
theorem B867635 : Blo 574812 867635 := bstep (se 1 (by rfl) ⟨650726, by rfl⟩ : syracuseStep 867635 = 1301453) B1301453
theorem B867665 : Blo 574812 867665 := bstep (se 2 (by rfl) ⟨325374, by rfl⟩ : syracuseStep 867665 = 650749) B650749
theorem B867683 : Blo 574812 867683 := bstep (se 1 (by rfl) ⟨650762, by rfl⟩ : syracuseStep 867683 = 1301525) B1301525
theorem B867713 : Blo 574812 867713 := bstep (se 2 (by rfl) ⟨325392, by rfl⟩ : syracuseStep 867713 = 650785) B650785
theorem B1293713 : Blo 574812 1293713 := bstep (se 2 (by rfl) ⟨485142, by rfl⟩ : syracuseStep 1293713 = 970285) B970285
theorem B867731 : Blo 574812 867731 := bstep (se 1 (by rfl) ⟨650798, by rfl⟩ : syracuseStep 867731 = 1301597) B1301597
theorem B1293731 : Blo 574812 1293731 := bstep (se 1 (by rfl) ⟨970298, by rfl⟩ : syracuseStep 1293731 = 1940597) B1940597
theorem B1457585 : Blo 574812 1457585 := bstep (se 2 (by rfl) ⟨546594, by rfl⟩ : syracuseStep 1457585 = 1093189) B1093189
theorem B867761 : Blo 574812 867761 := bstep (se 2 (by rfl) ⟨325410, by rfl⟩ : syracuseStep 867761 = 650821) B650821
theorem B835009 : Blo 574812 835009 := bstep (se 2 (by rfl) ⟨313128, by rfl⟩ : syracuseStep 835009 = 626257) B626257
theorem B867779 : Blo 574812 867779 := bstep (se 1 (by rfl) ⟨650834, by rfl⟩ : syracuseStep 867779 = 1301669) B1301669
theorem B867809 : Blo 574812 867809 := bstep (se 2 (by rfl) ⟨325428, by rfl⟩ : syracuseStep 867809 = 650857) B650857
theorem B1457635 : Blo 574812 1457635 := bstep (se 1 (by rfl) ⟨1093226, by rfl⟩ : syracuseStep 1457635 = 2186453) B2186453
theorem B2080241 : Blo 574812 2080241 := bstep (se 2 (by rfl) ⟨780090, by rfl⟩ : syracuseStep 2080241 = 1560181) B1560181
theorem B867827 : Blo 574812 867827 := bstep (se 1 (by rfl) ⟨650870, by rfl⟩ : syracuseStep 867827 = 1301741) B1301741
theorem B867857 : Blo 574812 867857 := bstep (se 2 (by rfl) ⟨325446, by rfl⟩ : syracuseStep 867857 = 650893) B650893
theorem B867875 : Blo 574812 867875 := bstep (se 1 (by rfl) ⟨650906, by rfl⟩ : syracuseStep 867875 = 1301813) B1301813
theorem B867905 : Blo 574812 867905 := bstep (se 2 (by rfl) ⟨325464, by rfl⟩ : syracuseStep 867905 = 650929) B650929
theorem B1097297 : Blo 574812 1097297 := bstep (se 2 (by rfl) ⟨411486, by rfl⟩ : syracuseStep 1097297 = 822973) B822973
theorem B867923 : Blo 574812 867923 := bstep (se 1 (by rfl) ⟨650942, by rfl⟩ : syracuseStep 867923 = 1301885) B1301885
theorem B1457777 : Blo 574812 1457777 := bstep (se 2 (by rfl) ⟨546666, by rfl⟩ : syracuseStep 1457777 = 1093333) B1093333
theorem B867953 : Blo 574812 867953 := bstep (se 2 (by rfl) ⟨325482, by rfl⟩ : syracuseStep 867953 = 650965) B650965
theorem B867971 : Blo 574812 867971 := bstep (se 1 (by rfl) ⟨650978, by rfl⟩ : syracuseStep 867971 = 1301957) B1301957
theorem B868001 : Blo 574812 868001 := bstep (se 2 (by rfl) ⟨325500, by rfl⟩ : syracuseStep 868001 = 651001) B651001
theorem B1294001 : Blo 574812 1294001 := bstep (se 2 (by rfl) ⟨485250, by rfl⟩ : syracuseStep 1294001 = 970501) B970501
theorem B868019 : Blo 574812 868019 := bstep (se 1 (by rfl) ⟨651014, by rfl⟩ : syracuseStep 868019 = 1302029) B1302029
theorem B1294019 : Blo 574812 1294019 := bstep (se 1 (by rfl) ⟨970514, by rfl⟩ : syracuseStep 1294019 = 1941029) B1941029
theorem B868049 : Blo 574812 868049 := bstep (se 2 (by rfl) ⟨325518, by rfl⟩ : syracuseStep 868049 = 651037) B651037
theorem B868067 : Blo 574812 868067 := bstep (se 1 (by rfl) ⟨651050, by rfl⟩ : syracuseStep 868067 = 1302101) B1302101
theorem B868097 : Blo 574812 868097 := bstep (se 2 (by rfl) ⟨325536, by rfl⟩ : syracuseStep 868097 = 651073) B651073
theorem B1949453 : Blo 574812 1949453 := bstep (se 3 (by rfl) ⟨365522, by rfl⟩ : syracuseStep 1949453 = 731045) B731045
theorem B868115 : Blo 574812 868115 := bstep (se 1 (by rfl) ⟨651086, by rfl⟩ : syracuseStep 868115 = 1302173) B1302173
theorem B868145 : Blo 574812 868145 := bstep (se 2 (by rfl) ⟨325554, by rfl⟩ : syracuseStep 868145 = 651109) B651109
theorem B1949507 : Blo 574812 1949507 := bstep (se 1 (by rfl) ⟨1462130, by rfl⟩ : syracuseStep 1949507 = 2924261) B2924261
theorem B868163 : Blo 574812 868163 := bstep (se 1 (by rfl) ⟨651122, by rfl⟩ : syracuseStep 868163 = 1302245) B1302245
theorem B868193 : Blo 574812 868193 := bstep (se 2 (by rfl) ⟨325572, by rfl⟩ : syracuseStep 868193 = 651145) B651145
theorem B868211 : Blo 574812 868211 := bstep (se 1 (by rfl) ⟨651158, by rfl⟩ : syracuseStep 868211 = 1302317) B1302317
theorem B2768845 : Blo 574812 2768845 := bstep (se 3 (by rfl) ⟨519158, by rfl⟩ : syracuseStep 2768845 = 1038317) B1038317
theorem B1294289 : Blo 574812 1294289 := bstep (se 2 (by rfl) ⟨485358, by rfl⟩ : syracuseStep 1294289 = 970717) B970717
theorem B1294307 : Blo 574812 1294307 := bstep (se 1 (by rfl) ⟨970730, by rfl⟩ : syracuseStep 1294307 = 1941461) B1941461
theorem B1949777 : Blo 574812 1949777 := bstep (se 2 (by rfl) ⟨731166, by rfl⟩ : syracuseStep 1949777 = 1462333) B1462333
theorem B1294577 : Blo 574812 1294577 := bstep (se 2 (by rfl) ⟨485466, by rfl⟩ : syracuseStep 1294577 = 970933) B970933
theorem B2769137 : Blo 574812 2769137 := bstep (se 2 (by rfl) ⟨1038426, by rfl⟩ : syracuseStep 2769137 = 2076853) B2076853
theorem B1294595 : Blo 574812 1294595 := bstep (se 1 (by rfl) ⟨970946, by rfl⟩ : syracuseStep 1294595 = 1941893) B1941893
theorem B1098193 : Blo 574812 1098193 := bstep (se 2 (by rfl) ⟨411822, by rfl⟩ : syracuseStep 1098193 = 823645) B823645
theorem B1294865 : Blo 574812 1294865 := bstep (se 2 (by rfl) ⟨485574, by rfl⟩ : syracuseStep 1294865 = 971149) B971149
theorem B1294883 : Blo 574812 1294883 := bstep (se 1 (by rfl) ⟨971162, by rfl⟩ : syracuseStep 1294883 = 1942325) B1942325
theorem B1458769 : Blo 574812 1458769 := bstep (se 2 (by rfl) ⟨547038, by rfl⟩ : syracuseStep 1458769 = 1094077) B1094077
theorem B1950317 : Blo 574812 1950317 := bstep (se 3 (by rfl) ⟨365684, by rfl⟩ : syracuseStep 1950317 = 731369) B731369
theorem B1098353 : Blo 574812 1098353 := bstep (se 2 (by rfl) ⟨411882, by rfl⟩ : syracuseStep 1098353 = 823765) B823765
theorem B1950371 : Blo 574812 1950371 := bstep (se 1 (by rfl) ⟨1462778, by rfl⟩ : syracuseStep 1950371 = 2925557) B2925557
theorem B1229539 : Blo 574812 1229539 := bstep (se 1 (by rfl) ⟨922154, by rfl⟩ : syracuseStep 1229539 = 1844309) B1844309
theorem B1295153 : Blo 574812 1295153 := bstep (se 2 (by rfl) ⟨485682, by rfl⟩ : syracuseStep 1295153 = 971365) B971365
theorem B1295171 : Blo 574812 1295171 := bstep (se 1 (by rfl) ⟨971378, by rfl⟩ : syracuseStep 1295171 = 1942757) B1942757
theorem B1459043 : Blo 574812 1459043 := bstep (se 1 (by rfl) ⟨1094282, by rfl⟩ : syracuseStep 1459043 = 2188565) B2188565
theorem B1000369 : Blo 574812 1000369 := bstep (se 2 (by rfl) ⟨375138, by rfl⟩ : syracuseStep 1000369 = 750277) B750277
theorem B1950641 : Blo 574812 1950641 := bstep (se 2 (by rfl) ⟨731490, by rfl⟩ : syracuseStep 1950641 = 1462981) B1462981
theorem B1852355 : Blo 574812 1852355 := bstep (se 1 (by rfl) ⟨1389266, by rfl⟩ : syracuseStep 1852355 = 2778533) B2778533
theorem B1098755 : Blo 574812 1098755 := bstep (se 1 (by rfl) ⟨824066, by rfl⟩ : syracuseStep 1098755 = 1648133) B1648133
theorem B1557521 : Blo 574812 1557521 := bstep (se 2 (by rfl) ⟨584070, by rfl⟩ : syracuseStep 1557521 = 1168141) B1168141
theorem B1459235 : Blo 574812 1459235 := bstep (se 1 (by rfl) ⟨1094426, by rfl⟩ : syracuseStep 1459235 = 2188853) B2188853
theorem B1295441 : Blo 574812 1295441 := bstep (se 2 (by rfl) ⟨485790, by rfl⟩ : syracuseStep 1295441 = 971581) B971581
theorem B1295459 : Blo 574812 1295459 := bstep (se 1 (by rfl) ⟨971594, by rfl⟩ : syracuseStep 1295459 = 1943189) B1943189
theorem B2245745 : Blo 574812 2245745 := bstep (se 2 (by rfl) ⟨842154, by rfl⟩ : syracuseStep 2245745 = 1684309) B1684309
theorem B6571205 : Blo 574812 6571205 := bstep (se 4 (by rfl) ⟨616050, by rfl⟩ : syracuseStep 6571205 = 1232101) B1232101
theorem B3851569 : Blo 574812 3851569 := bstep (se 2 (by rfl) ⟨1444338, by rfl⟩ : syracuseStep 3851569 = 2888677) B2888677
theorem B3294533 : Blo 574812 3294533 := bstep (se 4 (by rfl) ⟨308862, by rfl⟩ : syracuseStep 3294533 = 617725) B617725
theorem B574819 : Blo 574812 574819 := bstep (se 1 (by rfl) ⟨431114, by rfl⟩ : syracuseStep 574819 = 862229) B862229
theorem B1295729 : Blo 574812 1295729 := bstep (se 2 (by rfl) ⟨485898, by rfl⟩ : syracuseStep 1295729 = 971797) B971797
theorem B574835 : Blo 574812 574835 := bstep (se 1 (by rfl) ⟨431126, by rfl⟩ : syracuseStep 574835 = 862253) B862253
theorem B574851 : Blo 574812 574851 := bstep (se 1 (by rfl) ⟨431138, by rfl⟩ : syracuseStep 574851 = 862277) B862277
theorem B1295747 : Blo 574812 1295747 := bstep (se 1 (by rfl) ⟨971810, by rfl⟩ : syracuseStep 1295747 = 1943621) B1943621
theorem B574867 : Blo 574812 574867 := bstep (se 1 (by rfl) ⟨431150, by rfl⟩ : syracuseStep 574867 = 862301) B862301
theorem B574883 : Blo 574812 574883 := bstep (se 1 (by rfl) ⟨431162, by rfl⟩ : syracuseStep 574883 = 862325) B862325
theorem B574899 : Blo 574812 574899 := bstep (se 1 (by rfl) ⟨431174, by rfl⟩ : syracuseStep 574899 = 862349) B862349
theorem B574915 : Blo 574812 574915 := bstep (se 1 (by rfl) ⟨431186, by rfl⟩ : syracuseStep 574915 = 862373) B862373
theorem B1951181 : Blo 574812 1951181 := bstep (se 3 (by rfl) ⟨365846, by rfl⟩ : syracuseStep 1951181 = 731693) B731693
theorem B574931 : Blo 574812 574931 := bstep (se 1 (by rfl) ⟨431198, by rfl⟩ : syracuseStep 574931 = 862397) B862397
theorem B574947 : Blo 574812 574947 := bstep (se 1 (by rfl) ⟨431210, by rfl⟩ : syracuseStep 574947 = 862421) B862421
theorem B574963 : Blo 574812 574963 := bstep (se 1 (by rfl) ⟨431222, by rfl⟩ : syracuseStep 574963 = 862445) B862445
theorem B574979 : Blo 574812 574979 := bstep (se 1 (by rfl) ⟨431234, by rfl⟩ : syracuseStep 574979 = 862469) B862469
theorem B1951235 : Blo 574812 1951235 := bstep (se 1 (by rfl) ⟨1463426, by rfl⟩ : syracuseStep 1951235 = 2926853) B2926853
theorem B574995 : Blo 574812 574995 := bstep (se 1 (by rfl) ⟨431246, by rfl⟩ : syracuseStep 574995 = 862493) B862493
theorem B575011 : Blo 574812 575011 := bstep (se 1 (by rfl) ⟨431258, by rfl⟩ : syracuseStep 575011 = 862517) B862517
theorem B1230385 : Blo 574812 1230385 := bstep (se 2 (by rfl) ⟨461394, by rfl⟩ : syracuseStep 1230385 = 922789) B922789
theorem B575027 : Blo 574812 575027 := bstep (se 1 (by rfl) ⟨431270, by rfl⟩ : syracuseStep 575027 = 862541) B862541
theorem B575043 : Blo 574812 575043 := bstep (se 1 (by rfl) ⟨431282, by rfl⟩ : syracuseStep 575043 = 862565) B862565
theorem B575059 : Blo 574812 575059 := bstep (se 1 (by rfl) ⟨431294, by rfl⟩ : syracuseStep 575059 = 862589) B862589
theorem B575075 : Blo 574812 575075 := bstep (se 1 (by rfl) ⟨431306, by rfl⟩ : syracuseStep 575075 = 862613) B862613
theorem B575091 : Blo 574812 575091 := bstep (se 1 (by rfl) ⟨431318, by rfl⟩ : syracuseStep 575091 = 862637) B862637
theorem B575107 : Blo 574812 575107 := bstep (se 1 (by rfl) ⟨431330, by rfl⟩ : syracuseStep 575107 = 862661) B862661
theorem B1296017 : Blo 574812 1296017 := bstep (se 2 (by rfl) ⟨486006, by rfl⟩ : syracuseStep 1296017 = 972013) B972013
theorem B575123 : Blo 574812 575123 := bstep (se 1 (by rfl) ⟨431342, by rfl⟩ : syracuseStep 575123 = 862685) B862685
theorem B575139 : Blo 574812 575139 := bstep (se 1 (by rfl) ⟨431354, by rfl⟩ : syracuseStep 575139 = 862709) B862709
theorem B1296035 : Blo 574812 1296035 := bstep (se 1 (by rfl) ⟨972026, by rfl⟩ : syracuseStep 1296035 = 1944053) B1944053
theorem B575155 : Blo 574812 575155 := bstep (se 1 (by rfl) ⟨431366, by rfl⟩ : syracuseStep 575155 = 862733) B862733
theorem B575171 : Blo 574812 575171 := bstep (se 1 (by rfl) ⟨431378, by rfl⟩ : syracuseStep 575171 = 862757) B862757
theorem B575187 : Blo 574812 575187 := bstep (se 1 (by rfl) ⟨431390, by rfl⟩ : syracuseStep 575187 = 862781) B862781
theorem B575203 : Blo 574812 575203 := bstep (se 1 (by rfl) ⟨431402, by rfl⟩ : syracuseStep 575203 = 862805) B862805
theorem B2967281 : Blo 574812 2967281 := bstep (se 2 (by rfl) ⟨1112730, by rfl⟩ : syracuseStep 2967281 = 2225461) B2225461
theorem B575219 : Blo 574812 575219 := bstep (se 1 (by rfl) ⟨431414, by rfl⟩ : syracuseStep 575219 = 862829) B862829
theorem B575235 : Blo 574812 575235 := bstep (se 1 (by rfl) ⟨431426, by rfl⟩ : syracuseStep 575235 = 862853) B862853
theorem B3294989 : Blo 574812 3294989 := bstep (se 3 (by rfl) ⟨617810, by rfl⟩ : syracuseStep 3294989 = 1235621) B1235621
theorem B1951505 : Blo 574812 1951505 := bstep (se 2 (by rfl) ⟨731814, by rfl⟩ : syracuseStep 1951505 = 1463629) B1463629
theorem B575251 : Blo 574812 575251 := bstep (se 1 (by rfl) ⟨431438, by rfl⟩ : syracuseStep 575251 = 862877) B862877
theorem B739091 : Blo 574812 739091 := bstep (se 1 (by rfl) ⟨554318, by rfl⟩ : syracuseStep 739091 = 1108637) B1108637
theorem B575267 : Blo 574812 575267 := bstep (se 1 (by rfl) ⟨431450, by rfl⟩ : syracuseStep 575267 = 862901) B862901
theorem B575283 : Blo 574812 575283 := bstep (se 1 (by rfl) ⟨431462, by rfl⟩ : syracuseStep 575283 = 862925) B862925
theorem B575299 : Blo 574812 575299 := bstep (se 1 (by rfl) ⟨431474, by rfl⟩ : syracuseStep 575299 = 862949) B862949
theorem B575315 : Blo 574812 575315 := bstep (se 1 (by rfl) ⟨431486, by rfl⟩ : syracuseStep 575315 = 862973) B862973
theorem B575331 : Blo 574812 575331 := bstep (se 1 (by rfl) ⟨431498, by rfl⟩ : syracuseStep 575331 = 862997) B862997
theorem B575347 : Blo 574812 575347 := bstep (se 1 (by rfl) ⟨431510, by rfl⟩ : syracuseStep 575347 = 863021) B863021
theorem B575363 : Blo 574812 575363 := bstep (se 1 (by rfl) ⟨431522, by rfl⟩ : syracuseStep 575363 = 863045) B863045
theorem B575379 : Blo 574812 575379 := bstep (se 1 (by rfl) ⟨431534, by rfl⟩ : syracuseStep 575379 = 863069) B863069
theorem B575395 : Blo 574812 575395 := bstep (se 1 (by rfl) ⟨431546, by rfl⟩ : syracuseStep 575395 = 863093) B863093
theorem B1296305 : Blo 574812 1296305 := bstep (se 2 (by rfl) ⟨486114, by rfl⟩ : syracuseStep 1296305 = 972229) B972229
theorem B575411 : Blo 574812 575411 := bstep (se 1 (by rfl) ⟨431558, by rfl⟩ : syracuseStep 575411 = 863117) B863117
theorem B575427 : Blo 574812 575427 := bstep (se 1 (by rfl) ⟨431570, by rfl⟩ : syracuseStep 575427 = 863141) B863141
theorem B1296323 : Blo 574812 1296323 := bstep (se 1 (by rfl) ⟨972242, by rfl⟩ : syracuseStep 1296323 = 1944485) B1944485
theorem B2344909 : Blo 574812 2344909 := bstep (se 3 (by rfl) ⟨439670, by rfl⟩ : syracuseStep 2344909 = 879341) B879341
theorem B1460177 : Blo 574812 1460177 := bstep (se 2 (by rfl) ⟨547566, by rfl⟩ : syracuseStep 1460177 = 1095133) B1095133
theorem B575443 : Blo 574812 575443 := bstep (se 1 (by rfl) ⟨431582, by rfl⟩ : syracuseStep 575443 = 863165) B863165
theorem B575459 : Blo 574812 575459 := bstep (se 1 (by rfl) ⟨431594, by rfl⟩ : syracuseStep 575459 = 863189) B863189
theorem B575475 : Blo 574812 575475 := bstep (se 1 (by rfl) ⟨431606, by rfl⟩ : syracuseStep 575475 = 863213) B863213
theorem B575491 : Blo 574812 575491 := bstep (se 1 (by rfl) ⟨431618, by rfl⟩ : syracuseStep 575491 = 863237) B863237
theorem B1460227 : Blo 574812 1460227 := bstep (se 1 (by rfl) ⟨1095170, by rfl⟩ : syracuseStep 1460227 = 2190341) B2190341
theorem B575507 : Blo 574812 575507 := bstep (se 1 (by rfl) ⟨431630, by rfl⟩ : syracuseStep 575507 = 863261) B863261
theorem B575523 : Blo 574812 575523 := bstep (se 1 (by rfl) ⟨431642, by rfl⟩ : syracuseStep 575523 = 863285) B863285
theorem B575539 : Blo 574812 575539 := bstep (se 1 (by rfl) ⟨431654, by rfl⟩ : syracuseStep 575539 = 863309) B863309
theorem B575555 : Blo 574812 575555 := bstep (se 1 (by rfl) ⟨431666, by rfl⟩ : syracuseStep 575555 = 863333) B863333
theorem B575571 : Blo 574812 575571 := bstep (se 1 (by rfl) ⟨431678, by rfl⟩ : syracuseStep 575571 = 863357) B863357
theorem B575587 : Blo 574812 575587 := bstep (se 1 (by rfl) ⟨431690, by rfl⟩ : syracuseStep 575587 = 863381) B863381
theorem B575603 : Blo 574812 575603 := bstep (se 1 (by rfl) ⟨431702, by rfl⟩ : syracuseStep 575603 = 863405) B863405
theorem B575619 : Blo 574812 575619 := bstep (se 1 (by rfl) ⟨431714, by rfl⟩ : syracuseStep 575619 = 863429) B863429
theorem B1460369 : Blo 574812 1460369 := bstep (se 2 (by rfl) ⟨547638, by rfl⟩ : syracuseStep 1460369 = 1095277) B1095277
theorem B575635 : Blo 574812 575635 := bstep (se 1 (by rfl) ⟨431726, by rfl⟩ : syracuseStep 575635 = 863453) B863453
theorem B575651 : Blo 574812 575651 := bstep (se 1 (by rfl) ⟨431738, by rfl⟩ : syracuseStep 575651 = 863477) B863477
theorem B575667 : Blo 574812 575667 := bstep (se 1 (by rfl) ⟨431750, by rfl⟩ : syracuseStep 575667 = 863501) B863501
theorem B575683 : Blo 574812 575683 := bstep (se 1 (by rfl) ⟨431762, by rfl⟩ : syracuseStep 575683 = 863525) B863525
theorem B1296593 : Blo 574812 1296593 := bstep (se 2 (by rfl) ⟨486222, by rfl⟩ : syracuseStep 1296593 = 972445) B972445
theorem B575699 : Blo 574812 575699 := bstep (se 1 (by rfl) ⟨431774, by rfl⟩ : syracuseStep 575699 = 863549) B863549
theorem B575715 : Blo 574812 575715 := bstep (se 1 (by rfl) ⟨431786, by rfl⟩ : syracuseStep 575715 = 863573) B863573
theorem B1296611 : Blo 574812 1296611 := bstep (se 1 (by rfl) ⟨972458, by rfl⟩ : syracuseStep 1296611 = 1944917) B1944917
theorem B575731 : Blo 574812 575731 := bstep (se 1 (by rfl) ⟨431798, by rfl⟩ : syracuseStep 575731 = 863597) B863597
theorem B575747 : Blo 574812 575747 := bstep (se 1 (by rfl) ⟨431810, by rfl⟩ : syracuseStep 575747 = 863621) B863621
theorem B575763 : Blo 574812 575763 := bstep (se 1 (by rfl) ⟨431822, by rfl⟩ : syracuseStep 575763 = 863645) B863645
theorem B575779 : Blo 574812 575779 := bstep (se 1 (by rfl) ⟨431834, by rfl⟩ : syracuseStep 575779 = 863669) B863669
theorem B1952045 : Blo 574812 1952045 := bstep (se 3 (by rfl) ⟨366008, by rfl⟩ : syracuseStep 1952045 = 732017) B732017
theorem B575795 : Blo 574812 575795 := bstep (se 1 (by rfl) ⟨431846, by rfl⟩ : syracuseStep 575795 = 863693) B863693
theorem B575811 : Blo 574812 575811 := bstep (se 1 (by rfl) ⟨431858, by rfl⟩ : syracuseStep 575811 = 863717) B863717
theorem B575827 : Blo 574812 575827 := bstep (se 1 (by rfl) ⟨431870, by rfl⟩ : syracuseStep 575827 = 863741) B863741
theorem B575843 : Blo 574812 575843 := bstep (se 1 (by rfl) ⟨431882, by rfl⟩ : syracuseStep 575843 = 863765) B863765
theorem B1952099 : Blo 574812 1952099 := bstep (se 1 (by rfl) ⟨1464074, by rfl⟩ : syracuseStep 1952099 = 2928149) B2928149
theorem B575859 : Blo 574812 575859 := bstep (se 1 (by rfl) ⟨431894, by rfl⟩ : syracuseStep 575859 = 863789) B863789
theorem B575875 : Blo 574812 575875 := bstep (se 1 (by rfl) ⟨431906, by rfl⟩ : syracuseStep 575875 = 863813) B863813
theorem B575891 : Blo 574812 575891 := bstep (se 1 (by rfl) ⟨431918, by rfl⟩ : syracuseStep 575891 = 863837) B863837
theorem B575907 : Blo 574812 575907 := bstep (se 1 (by rfl) ⟨431930, by rfl⟩ : syracuseStep 575907 = 863861) B863861
theorem B1755569 : Blo 574812 1755569 := bstep (se 2 (by rfl) ⟨658338, by rfl⟩ : syracuseStep 1755569 = 1316677) B1316677
theorem B575923 : Blo 574812 575923 := bstep (se 1 (by rfl) ⟨431942, by rfl⟩ : syracuseStep 575923 = 863885) B863885
theorem B575939 : Blo 574812 575939 := bstep (se 1 (by rfl) ⟨431954, by rfl⟩ : syracuseStep 575939 = 863909) B863909
theorem B3688901 : Blo 574812 3688901 := bstep (se 4 (by rfl) ⟨345834, by rfl⟩ : syracuseStep 3688901 = 691669) B691669
theorem B575955 : Blo 574812 575955 := bstep (se 1 (by rfl) ⟨431966, by rfl⟩ : syracuseStep 575955 = 863933) B863933
theorem B575971 : Blo 574812 575971 := bstep (se 1 (by rfl) ⟨431978, by rfl⟩ : syracuseStep 575971 = 863957) B863957
theorem B1296881 : Blo 574812 1296881 := bstep (se 2 (by rfl) ⟨486330, by rfl⟩ : syracuseStep 1296881 = 972661) B972661
theorem B575987 : Blo 574812 575987 := bstep (se 1 (by rfl) ⟨431990, by rfl⟩ : syracuseStep 575987 = 863981) B863981
theorem B576003 : Blo 574812 576003 := bstep (se 1 (by rfl) ⟨432002, by rfl⟩ : syracuseStep 576003 = 864005) B864005
theorem B1296899 : Blo 574812 1296899 := bstep (se 1 (by rfl) ⟨972674, by rfl⟩ : syracuseStep 1296899 = 1945349) B1945349
theorem B576019 : Blo 574812 576019 := bstep (se 1 (by rfl) ⟨432014, by rfl⟩ : syracuseStep 576019 = 864029) B864029
theorem B576035 : Blo 574812 576035 := bstep (se 1 (by rfl) ⟨432026, by rfl⟩ : syracuseStep 576035 = 864053) B864053
theorem B576051 : Blo 574812 576051 := bstep (se 1 (by rfl) ⟨432038, by rfl⟩ : syracuseStep 576051 = 864077) B864077
theorem B576067 : Blo 574812 576067 := bstep (se 1 (by rfl) ⟨432050, by rfl⟩ : syracuseStep 576067 = 864101) B864101
theorem B576083 : Blo 574812 576083 := bstep (se 1 (by rfl) ⟨432062, by rfl⟩ : syracuseStep 576083 = 864125) B864125
theorem B576099 : Blo 574812 576099 := bstep (se 1 (by rfl) ⟨432074, by rfl⟩ : syracuseStep 576099 = 864149) B864149
theorem B2083427 : Blo 574812 2083427 := bstep (se 1 (by rfl) ⟨1562570, by rfl⟩ : syracuseStep 2083427 = 3125141) B3125141
theorem B1952369 : Blo 574812 1952369 := bstep (se 2 (by rfl) ⟨732138, by rfl⟩ : syracuseStep 1952369 = 1464277) B1464277
theorem B576115 : Blo 574812 576115 := bstep (se 1 (by rfl) ⟨432086, by rfl⟩ : syracuseStep 576115 = 864173) B864173
theorem B576131 : Blo 574812 576131 := bstep (se 1 (by rfl) ⟨432098, by rfl⟩ : syracuseStep 576131 = 864197) B864197
theorem B2771597 : Blo 574812 2771597 := bstep (se 3 (by rfl) ⟨519674, by rfl⟩ : syracuseStep 2771597 = 1039349) B1039349
theorem B576147 : Blo 574812 576147 := bstep (se 1 (by rfl) ⟨432110, by rfl⟩ : syracuseStep 576147 = 864221) B864221
theorem B576163 : Blo 574812 576163 := bstep (se 1 (by rfl) ⟨432122, by rfl⟩ : syracuseStep 576163 = 864245) B864245
theorem B576179 : Blo 574812 576179 := bstep (se 1 (by rfl) ⟨432134, by rfl⟩ : syracuseStep 576179 = 864269) B864269
theorem B576195 : Blo 574812 576195 := bstep (se 1 (by rfl) ⟨432146, by rfl⟩ : syracuseStep 576195 = 864293) B864293
theorem B576211 : Blo 574812 576211 := bstep (se 1 (by rfl) ⟨432158, by rfl⟩ : syracuseStep 576211 = 864317) B864317
theorem B576227 : Blo 574812 576227 := bstep (se 1 (by rfl) ⟨432170, by rfl⟩ : syracuseStep 576227 = 864341) B864341
theorem B576243 : Blo 574812 576243 := bstep (se 1 (by rfl) ⟨432182, by rfl⟩ : syracuseStep 576243 = 864365) B864365
theorem B576259 : Blo 574812 576259 := bstep (se 1 (by rfl) ⟨432194, by rfl⟩ : syracuseStep 576259 = 864389) B864389
theorem B1297169 : Blo 574812 1297169 := bstep (se 2 (by rfl) ⟨486438, by rfl⟩ : syracuseStep 1297169 = 972877) B972877
theorem B576275 : Blo 574812 576275 := bstep (se 1 (by rfl) ⟨432206, by rfl⟩ : syracuseStep 576275 = 864413) B864413
theorem B936737 : Blo 574812 936737 := bstep (se 2 (by rfl) ⟨351276, by rfl⟩ : syracuseStep 936737 = 702553) B702553
theorem B576291 : Blo 574812 576291 := bstep (se 1 (by rfl) ⟨432218, by rfl⟩ : syracuseStep 576291 = 864437) B864437
theorem B1297187 : Blo 574812 1297187 := bstep (se 1 (by rfl) ⟨972890, by rfl⟩ : syracuseStep 1297187 = 1945781) B1945781
theorem B576307 : Blo 574812 576307 := bstep (se 1 (by rfl) ⟨432230, by rfl⟩ : syracuseStep 576307 = 864461) B864461
theorem B576323 : Blo 574812 576323 := bstep (se 1 (by rfl) ⟨432242, by rfl⟩ : syracuseStep 576323 = 864485) B864485
theorem B576339 : Blo 574812 576339 := bstep (se 1 (by rfl) ⟨432254, by rfl⟩ : syracuseStep 576339 = 864509) B864509
theorem B576355 : Blo 574812 576355 := bstep (se 1 (by rfl) ⟨432266, by rfl⟩ : syracuseStep 576355 = 864533) B864533
theorem B576371 : Blo 574812 576371 := bstep (se 1 (by rfl) ⟨432278, by rfl⟩ : syracuseStep 576371 = 864557) B864557
theorem B576387 : Blo 574812 576387 := bstep (se 1 (by rfl) ⟨432290, by rfl⟩ : syracuseStep 576387 = 864581) B864581
theorem B576403 : Blo 574812 576403 := bstep (se 1 (by rfl) ⟨432302, by rfl⟩ : syracuseStep 576403 = 864605) B864605
theorem B576419 : Blo 574812 576419 := bstep (se 1 (by rfl) ⟨432314, by rfl⟩ : syracuseStep 576419 = 864629) B864629
theorem B576435 : Blo 574812 576435 := bstep (se 1 (by rfl) ⟨432326, by rfl⟩ : syracuseStep 576435 = 864653) B864653
theorem B576451 : Blo 574812 576451 := bstep (se 1 (by rfl) ⟨432338, by rfl⟩ : syracuseStep 576451 = 864677) B864677
theorem B576467 : Blo 574812 576467 := bstep (se 1 (by rfl) ⟨432350, by rfl⟩ : syracuseStep 576467 = 864701) B864701
theorem B576483 : Blo 574812 576483 := bstep (se 1 (by rfl) ⟨432362, by rfl⟩ : syracuseStep 576483 = 864725) B864725
theorem B576499 : Blo 574812 576499 := bstep (se 1 (by rfl) ⟨432374, by rfl⟩ : syracuseStep 576499 = 864749) B864749
theorem B576515 : Blo 574812 576515 := bstep (se 1 (by rfl) ⟨432386, by rfl⟩ : syracuseStep 576515 = 864773) B864773
theorem B576531 : Blo 574812 576531 := bstep (se 1 (by rfl) ⟨432398, by rfl⟩ : syracuseStep 576531 = 864797) B864797
theorem B576547 : Blo 574812 576547 := bstep (se 1 (by rfl) ⟨432410, by rfl⟩ : syracuseStep 576547 = 864821) B864821
theorem B1297457 : Blo 574812 1297457 := bstep (se 2 (by rfl) ⟨486546, by rfl⟩ : syracuseStep 1297457 = 973093) B973093
theorem B576563 : Blo 574812 576563 := bstep (se 1 (by rfl) ⟨432422, by rfl⟩ : syracuseStep 576563 = 864845) B864845
theorem B576579 : Blo 574812 576579 := bstep (se 1 (by rfl) ⟨432434, by rfl⟩ : syracuseStep 576579 = 864869) B864869
theorem B1297475 : Blo 574812 1297475 := bstep (se 1 (by rfl) ⟨973106, by rfl⟩ : syracuseStep 1297475 = 1946213) B1946213
theorem B576595 : Blo 574812 576595 := bstep (se 1 (by rfl) ⟨432446, by rfl⟩ : syracuseStep 576595 = 864893) B864893
theorem B576611 : Blo 574812 576611 := bstep (se 1 (by rfl) ⟨432458, by rfl⟩ : syracuseStep 576611 = 864917) B864917
theorem B1461361 : Blo 574812 1461361 := bstep (se 2 (by rfl) ⟨548010, by rfl⟩ : syracuseStep 1461361 = 1096021) B1096021
theorem B576627 : Blo 574812 576627 := bstep (se 1 (by rfl) ⟨432470, by rfl⟩ : syracuseStep 576627 = 864941) B864941
theorem B576643 : Blo 574812 576643 := bstep (se 1 (by rfl) ⟨432482, by rfl⟩ : syracuseStep 576643 = 864965) B864965
theorem B1952909 : Blo 574812 1952909 := bstep (se 3 (by rfl) ⟨366170, by rfl⟩ : syracuseStep 1952909 = 732341) B732341
theorem B576659 : Blo 574812 576659 := bstep (se 1 (by rfl) ⟨432494, by rfl⟩ : syracuseStep 576659 = 864989) B864989
theorem B576675 : Blo 574812 576675 := bstep (se 1 (by rfl) ⟨432506, by rfl⟩ : syracuseStep 576675 = 865013) B865013
theorem B576691 : Blo 574812 576691 := bstep (se 1 (by rfl) ⟨432518, by rfl⟩ : syracuseStep 576691 = 865037) B865037
theorem B576707 : Blo 574812 576707 := bstep (se 1 (by rfl) ⟨432530, by rfl⟩ : syracuseStep 576707 = 865061) B865061
theorem B1952963 : Blo 574812 1952963 := bstep (se 1 (by rfl) ⟨1464722, by rfl⟩ : syracuseStep 1952963 = 2929445) B2929445
theorem B576723 : Blo 574812 576723 := bstep (se 1 (by rfl) ⟨432542, by rfl⟩ : syracuseStep 576723 = 865085) B865085
theorem B576739 : Blo 574812 576739 := bstep (se 1 (by rfl) ⟨432554, by rfl⟩ : syracuseStep 576739 = 865109) B865109
theorem B576755 : Blo 574812 576755 := bstep (se 1 (by rfl) ⟨432566, by rfl⟩ : syracuseStep 576755 = 865133) B865133
theorem B576771 : Blo 574812 576771 := bstep (se 1 (by rfl) ⟨432578, by rfl⟩ : syracuseStep 576771 = 865157) B865157
theorem B576787 : Blo 574812 576787 := bstep (se 1 (by rfl) ⟨432590, by rfl⟩ : syracuseStep 576787 = 865181) B865181
theorem B576803 : Blo 574812 576803 := bstep (se 1 (by rfl) ⟨432602, by rfl⟩ : syracuseStep 576803 = 865205) B865205
theorem B576819 : Blo 574812 576819 := bstep (se 1 (by rfl) ⟨432614, by rfl⟩ : syracuseStep 576819 = 865229) B865229
theorem B970049 : Blo 574812 970049 := bstep (se 2 (by rfl) ⟨363768, by rfl⟩ : syracuseStep 970049 = 727537) B727537
theorem B576835 : Blo 574812 576835 := bstep (se 1 (by rfl) ⟨432626, by rfl⟩ : syracuseStep 576835 = 865253) B865253
theorem B1297745 : Blo 574812 1297745 := bstep (se 2 (by rfl) ⟨486654, by rfl⟩ : syracuseStep 1297745 = 973309) B973309
theorem B576851 : Blo 574812 576851 := bstep (se 1 (by rfl) ⟨432638, by rfl⟩ : syracuseStep 576851 = 865277) B865277
theorem B1297763 : Blo 574812 1297763 := bstep (se 1 (by rfl) ⟨973322, by rfl⟩ : syracuseStep 1297763 = 1946645) B1946645
theorem B576867 : Blo 574812 576867 := bstep (se 1 (by rfl) ⟨432650, by rfl⟩ : syracuseStep 576867 = 865301) B865301
theorem B576883 : Blo 574812 576883 := bstep (se 1 (by rfl) ⟨432662, by rfl⟩ : syracuseStep 576883 = 865325) B865325
theorem B576899 : Blo 574812 576899 := bstep (se 1 (by rfl) ⟨432674, by rfl⟩ : syracuseStep 576899 = 865349) B865349
theorem B1461635 : Blo 574812 1461635 := bstep (se 1 (by rfl) ⟨1096226, by rfl⟩ : syracuseStep 1461635 = 2192453) B2192453
theorem B1232273 : Blo 574812 1232273 := bstep (se 2 (by rfl) ⟨462102, by rfl⟩ : syracuseStep 1232273 = 924205) B924205
theorem B576915 : Blo 574812 576915 := bstep (se 1 (by rfl) ⟨432686, by rfl⟩ : syracuseStep 576915 = 865373) B865373
theorem B576931 : Blo 574812 576931 := bstep (se 1 (by rfl) ⟨432698, by rfl⟩ : syracuseStep 576931 = 865397) B865397
theorem B576947 : Blo 574812 576947 := bstep (se 1 (by rfl) ⟨432710, by rfl⟩ : syracuseStep 576947 = 865421) B865421
theorem B970177 : Blo 574812 970177 := bstep (se 2 (by rfl) ⟨363816, by rfl⟩ : syracuseStep 970177 = 727633) B727633
theorem B576963 : Blo 574812 576963 := bstep (se 1 (by rfl) ⟨432722, by rfl⟩ : syracuseStep 576963 = 865445) B865445
theorem B1953233 : Blo 574812 1953233 := bstep (se 2 (by rfl) ⟨732462, by rfl⟩ : syracuseStep 1953233 = 1464925) B1464925
theorem B576979 : Blo 574812 576979 := bstep (se 1 (by rfl) ⟨432734, by rfl⟩ : syracuseStep 576979 = 865469) B865469
theorem B970211 : Blo 574812 970211 := bstep (se 1 (by rfl) ⟨727658, by rfl⟩ : syracuseStep 970211 = 1455317) B1455317
theorem B576995 : Blo 574812 576995 := bstep (se 1 (by rfl) ⟨432746, by rfl⟩ : syracuseStep 576995 = 865493) B865493
theorem B577011 : Blo 574812 577011 := bstep (se 1 (by rfl) ⟨432758, by rfl⟩ : syracuseStep 577011 = 865517) B865517
theorem B577027 : Blo 574812 577027 := bstep (se 1 (by rfl) ⟨432770, by rfl⟩ : syracuseStep 577027 = 865541) B865541
theorem B577043 : Blo 574812 577043 := bstep (se 1 (by rfl) ⟨432782, by rfl⟩ : syracuseStep 577043 = 865565) B865565
theorem B577059 : Blo 574812 577059 := bstep (se 1 (by rfl) ⟨432794, by rfl⟩ : syracuseStep 577059 = 865589) B865589
theorem B577075 : Blo 574812 577075 := bstep (se 1 (by rfl) ⟨432806, by rfl⟩ : syracuseStep 577075 = 865613) B865613
theorem B577091 : Blo 574812 577091 := bstep (se 1 (by rfl) ⟨432818, by rfl⟩ : syracuseStep 577091 = 865637) B865637
theorem B1461827 : Blo 574812 1461827 := bstep (se 1 (by rfl) ⟨1096370, by rfl⟩ : syracuseStep 1461827 = 2192741) B2192741
theorem B2182733 : Blo 574812 2182733 := bstep (se 3 (by rfl) ⟨409262, by rfl⟩ : syracuseStep 2182733 = 818525) B818525
theorem B577107 : Blo 574812 577107 := bstep (se 1 (by rfl) ⟨432830, by rfl⟩ : syracuseStep 577107 = 865661) B865661
theorem B970339 : Blo 574812 970339 := bstep (se 1 (by rfl) ⟨727754, by rfl⟩ : syracuseStep 970339 = 1455509) B1455509
theorem B577123 : Blo 574812 577123 := bstep (se 1 (by rfl) ⟨432842, by rfl⟩ : syracuseStep 577123 = 865685) B865685
theorem B1298033 : Blo 574812 1298033 := bstep (se 2 (by rfl) ⟨486762, by rfl⟩ : syracuseStep 1298033 = 973525) B973525
theorem B577139 : Blo 574812 577139 := bstep (se 1 (by rfl) ⟨432854, by rfl⟩ : syracuseStep 577139 = 865709) B865709
theorem B1298051 : Blo 574812 1298051 := bstep (se 1 (by rfl) ⟨973538, by rfl⟩ : syracuseStep 1298051 = 1947077) B1947077
theorem B577155 : Blo 574812 577155 := bstep (se 1 (by rfl) ⟨432866, by rfl⟩ : syracuseStep 577155 = 865733) B865733
theorem B577171 : Blo 574812 577171 := bstep (se 1 (by rfl) ⟨432878, by rfl⟩ : syracuseStep 577171 = 865757) B865757
theorem B577187 : Blo 574812 577187 := bstep (se 1 (by rfl) ⟨432890, by rfl⟩ : syracuseStep 577187 = 865781) B865781
theorem B577203 : Blo 574812 577203 := bstep (se 1 (by rfl) ⟨432902, by rfl⟩ : syracuseStep 577203 = 865805) B865805
theorem B577219 : Blo 574812 577219 := bstep (se 1 (by rfl) ⟨432914, by rfl⟩ : syracuseStep 577219 = 865829) B865829
theorem B577235 : Blo 574812 577235 := bstep (se 1 (by rfl) ⟨432926, by rfl⟩ : syracuseStep 577235 = 865853) B865853
theorem B577251 : Blo 574812 577251 := bstep (se 1 (by rfl) ⟨432938, by rfl⟩ : syracuseStep 577251 = 865877) B865877
theorem B5557987 : Blo 574812 5557987 := bstep (se 1 (by rfl) ⟨4168490, by rfl⟩ : syracuseStep 5557987 = 8336981) B8336981
theorem B970481 : Blo 574812 970481 := bstep (se 2 (by rfl) ⟨363930, by rfl⟩ : syracuseStep 970481 = 727861) B727861
theorem B577267 : Blo 574812 577267 := bstep (se 1 (by rfl) ⟨432950, by rfl⟩ : syracuseStep 577267 = 865901) B865901
theorem B577283 : Blo 574812 577283 := bstep (se 1 (by rfl) ⟨432962, by rfl⟩ : syracuseStep 577283 = 865925) B865925
theorem B2084621 : Blo 574812 2084621 := bstep (se 3 (by rfl) ⟨390866, by rfl⟩ : syracuseStep 2084621 = 781733) B781733
theorem B577299 : Blo 574812 577299 := bstep (se 1 (by rfl) ⟨432974, by rfl⟩ : syracuseStep 577299 = 865949) B865949
theorem B577315 : Blo 574812 577315 := bstep (se 1 (by rfl) ⟨432986, by rfl⟩ : syracuseStep 577315 = 865973) B865973
theorem B577331 : Blo 574812 577331 := bstep (se 1 (by rfl) ⟨432998, by rfl⟩ : syracuseStep 577331 = 865997) B865997
theorem B577347 : Blo 574812 577347 := bstep (se 1 (by rfl) ⟨433010, by rfl⟩ : syracuseStep 577347 = 866021) B866021
theorem B577363 : Blo 574812 577363 := bstep (se 1 (by rfl) ⟨433022, by rfl⟩ : syracuseStep 577363 = 866045) B866045
theorem B577379 : Blo 574812 577379 := bstep (se 1 (by rfl) ⟨433034, by rfl⟩ : syracuseStep 577379 = 866069) B866069
theorem B1757027 : Blo 574812 1757027 := bstep (se 1 (by rfl) ⟨1317770, by rfl⟩ : syracuseStep 1757027 = 2635541) B2635541
theorem B2084707 : Blo 574812 2084707 := bstep (se 1 (by rfl) ⟨1563530, by rfl⟩ : syracuseStep 2084707 = 3127061) B3127061
theorem B970609 : Blo 574812 970609 := bstep (se 2 (by rfl) ⟨363978, by rfl⟩ : syracuseStep 970609 = 727957) B727957
theorem B577395 : Blo 574812 577395 := bstep (se 1 (by rfl) ⟨433046, by rfl⟩ : syracuseStep 577395 = 866093) B866093
theorem B577411 : Blo 574812 577411 := bstep (se 1 (by rfl) ⟨433058, by rfl⟩ : syracuseStep 577411 = 866117) B866117
theorem B1298321 : Blo 574812 1298321 := bstep (se 2 (by rfl) ⟨486870, by rfl⟩ : syracuseStep 1298321 = 973741) B973741
theorem B970643 : Blo 574812 970643 := bstep (se 1 (by rfl) ⟨727982, by rfl⟩ : syracuseStep 970643 = 1455965) B1455965
theorem B577427 : Blo 574812 577427 := bstep (se 1 (by rfl) ⟨433070, by rfl⟩ : syracuseStep 577427 = 866141) B866141
theorem B1298339 : Blo 574812 1298339 := bstep (se 1 (by rfl) ⟨973754, by rfl⟩ : syracuseStep 1298339 = 1947509) B1947509
theorem B577443 : Blo 574812 577443 := bstep (se 1 (by rfl) ⟨433082, by rfl⟩ : syracuseStep 577443 = 866165) B866165
theorem B1560493 : Blo 574812 1560493 := bstep (se 3 (by rfl) ⟨292592, by rfl⟩ : syracuseStep 1560493 = 585185) B585185
theorem B577459 : Blo 574812 577459 := bstep (se 1 (by rfl) ⟨433094, by rfl⟩ : syracuseStep 577459 = 866189) B866189
theorem B577475 : Blo 574812 577475 := bstep (se 1 (by rfl) ⟨433106, by rfl⟩ : syracuseStep 577475 = 866213) B866213
theorem B577491 : Blo 574812 577491 := bstep (se 1 (by rfl) ⟨433118, by rfl⟩ : syracuseStep 577491 = 866237) B866237
theorem B577507 : Blo 574812 577507 := bstep (se 1 (by rfl) ⟨433130, by rfl⟩ : syracuseStep 577507 = 866261) B866261
theorem B577523 : Blo 574812 577523 := bstep (se 1 (by rfl) ⟨433142, by rfl⟩ : syracuseStep 577523 = 866285) B866285
theorem B577539 : Blo 574812 577539 := bstep (se 1 (by rfl) ⟨433154, by rfl⟩ : syracuseStep 577539 = 866309) B866309
theorem B970771 : Blo 574812 970771 := bstep (se 1 (by rfl) ⟨728078, by rfl⟩ : syracuseStep 970771 = 1456157) B1456157
theorem B577555 : Blo 574812 577555 := bstep (se 1 (by rfl) ⟨433166, by rfl⟩ : syracuseStep 577555 = 866333) B866333
theorem B577571 : Blo 574812 577571 := bstep (se 1 (by rfl) ⟨433178, by rfl⟩ : syracuseStep 577571 = 866357) B866357
theorem B577587 : Blo 574812 577587 := bstep (se 1 (by rfl) ⟨433190, by rfl⟩ : syracuseStep 577587 = 866381) B866381
theorem B577603 : Blo 574812 577603 := bstep (se 1 (by rfl) ⟨433202, by rfl⟩ : syracuseStep 577603 = 866405) B866405
theorem B3952709 : Blo 574812 3952709 := bstep (se 4 (by rfl) ⟨370566, by rfl⟩ : syracuseStep 3952709 = 741133) B741133
theorem B577619 : Blo 574812 577619 := bstep (se 1 (by rfl) ⟨433214, by rfl⟩ : syracuseStep 577619 = 866429) B866429
theorem B577635 : Blo 574812 577635 := bstep (se 1 (by rfl) ⟨433226, by rfl⟩ : syracuseStep 577635 = 866453) B866453
theorem B577651 : Blo 574812 577651 := bstep (se 1 (by rfl) ⟨433238, by rfl⟩ : syracuseStep 577651 = 866477) B866477
theorem B577667 : Blo 574812 577667 := bstep (se 1 (by rfl) ⟨433250, by rfl⟩ : syracuseStep 577667 = 866501) B866501
theorem B1560721 : Blo 574812 1560721 := bstep (se 2 (by rfl) ⟨585270, by rfl⟩ : syracuseStep 1560721 = 1170541) B1170541
theorem B577683 : Blo 574812 577683 := bstep (se 1 (by rfl) ⟨433262, by rfl⟩ : syracuseStep 577683 = 866525) B866525
theorem B970913 : Blo 574812 970913 := bstep (se 2 (by rfl) ⟨364092, by rfl⟩ : syracuseStep 970913 = 728185) B728185
theorem B577699 : Blo 574812 577699 := bstep (se 1 (by rfl) ⟨433274, by rfl⟩ : syracuseStep 577699 = 866549) B866549
theorem B1298609 : Blo 574812 1298609 := bstep (se 2 (by rfl) ⟨486978, by rfl⟩ : syracuseStep 1298609 = 973957) B973957
theorem B577715 : Blo 574812 577715 := bstep (se 1 (by rfl) ⟨433286, by rfl⟩ : syracuseStep 577715 = 866573) B866573
theorem B1298627 : Blo 574812 1298627 := bstep (se 1 (by rfl) ⟨973970, by rfl⟩ : syracuseStep 1298627 = 1947941) B1947941
theorem B577731 : Blo 574812 577731 := bstep (se 1 (by rfl) ⟨433298, by rfl⟩ : syracuseStep 577731 = 866597) B866597
theorem B577747 : Blo 574812 577747 := bstep (se 1 (by rfl) ⟨433310, by rfl⟩ : syracuseStep 577747 = 866621) B866621
theorem B11096291 : Blo 574812 11096291 := bstep (se 1 (by rfl) ⟨8322218, by rfl⟩ : syracuseStep 11096291 = 16644437) B16644437
theorem B577763 : Blo 574812 577763 := bstep (se 1 (by rfl) ⟨433322, by rfl⟩ : syracuseStep 577763 = 866645) B866645
theorem B577779 : Blo 574812 577779 := bstep (se 1 (by rfl) ⟨433334, by rfl⟩ : syracuseStep 577779 = 866669) B866669
theorem B577795 : Blo 574812 577795 := bstep (se 1 (by rfl) ⟨433346, by rfl⟩ : syracuseStep 577795 = 866693) B866693
theorem B577811 : Blo 574812 577811 := bstep (se 1 (by rfl) ⟨433358, by rfl⟩ : syracuseStep 577811 = 866717) B866717
theorem B971041 : Blo 574812 971041 := bstep (se 2 (by rfl) ⟨364140, by rfl⟩ : syracuseStep 971041 = 728281) B728281
theorem B577827 : Blo 574812 577827 := bstep (se 1 (by rfl) ⟨433370, by rfl⟩ : syracuseStep 577827 = 866741) B866741
theorem B577843 : Blo 574812 577843 := bstep (se 1 (by rfl) ⟨433382, by rfl⟩ : syracuseStep 577843 = 866765) B866765
theorem B971075 : Blo 574812 971075 := bstep (se 1 (by rfl) ⟨728306, by rfl⟩ : syracuseStep 971075 = 1456613) B1456613
theorem B577859 : Blo 574812 577859 := bstep (se 1 (by rfl) ⟨433394, by rfl⟩ : syracuseStep 577859 = 866789) B866789
theorem B4673861 : Blo 574812 4673861 := bstep (se 4 (by rfl) ⟨438174, by rfl⟩ : syracuseStep 4673861 = 876349) B876349
theorem B577875 : Blo 574812 577875 := bstep (se 1 (by rfl) ⟨433406, by rfl⟩ : syracuseStep 577875 = 866813) B866813
theorem B577891 : Blo 574812 577891 := bstep (se 1 (by rfl) ⟨433418, by rfl⟩ : syracuseStep 577891 = 866837) B866837
theorem B2183537 : Blo 574812 2183537 := bstep (se 2 (by rfl) ⟨818826, by rfl⟩ : syracuseStep 2183537 = 1637653) B1637653
theorem B577907 : Blo 574812 577907 := bstep (se 1 (by rfl) ⟨433430, by rfl⟩ : syracuseStep 577907 = 866861) B866861
theorem B577923 : Blo 574812 577923 := bstep (se 1 (by rfl) ⟨433442, by rfl⟩ : syracuseStep 577923 = 866885) B866885
theorem B577939 : Blo 574812 577939 := bstep (se 1 (by rfl) ⟨433454, by rfl⟩ : syracuseStep 577939 = 866909) B866909
theorem B577955 : Blo 574812 577955 := bstep (se 1 (by rfl) ⟨433466, by rfl⟩ : syracuseStep 577955 = 866933) B866933
theorem B577971 : Blo 574812 577971 := bstep (se 1 (by rfl) ⟨433478, by rfl⟩ : syracuseStep 577971 = 866957) B866957
theorem B971203 : Blo 574812 971203 := bstep (se 1 (by rfl) ⟨728402, by rfl⟩ : syracuseStep 971203 = 1456805) B1456805
theorem B577987 : Blo 574812 577987 := bstep (se 1 (by rfl) ⟨433490, by rfl⟩ : syracuseStep 577987 = 866981) B866981
theorem B1298897 : Blo 574812 1298897 := bstep (se 2 (by rfl) ⟨487086, by rfl⟩ : syracuseStep 1298897 = 974173) B974173
theorem B578003 : Blo 574812 578003 := bstep (se 1 (by rfl) ⟨433502, by rfl⟩ : syracuseStep 578003 = 867005) B867005
theorem B1495523 : Blo 574812 1495523 := bstep (se 1 (by rfl) ⟨1121642, by rfl⟩ : syracuseStep 1495523 = 2243285) B2243285
theorem B1298915 : Blo 574812 1298915 := bstep (se 1 (by rfl) ⟨974186, by rfl⟩ : syracuseStep 1298915 = 1948373) B1948373
theorem B578019 : Blo 574812 578019 := bstep (se 1 (by rfl) ⟨433514, by rfl⟩ : syracuseStep 578019 = 867029) B867029
theorem B1462769 : Blo 574812 1462769 := bstep (se 2 (by rfl) ⟨548538, by rfl⟩ : syracuseStep 1462769 = 1097077) B1097077
theorem B578035 : Blo 574812 578035 := bstep (se 1 (by rfl) ⟨433526, by rfl⟩ : syracuseStep 578035 = 867053) B867053
theorem B578051 : Blo 574812 578051 := bstep (se 1 (by rfl) ⟨433538, by rfl⟩ : syracuseStep 578051 = 867077) B867077
theorem B578067 : Blo 574812 578067 := bstep (se 1 (by rfl) ⟨433550, by rfl⟩ : syracuseStep 578067 = 867101) B867101
theorem B1462819 : Blo 574812 1462819 := bstep (se 1 (by rfl) ⟨1097114, by rfl⟩ : syracuseStep 1462819 = 2194229) B2194229
theorem B578083 : Blo 574812 578083 := bstep (se 1 (by rfl) ⟨433562, by rfl⟩ : syracuseStep 578083 = 867125) B867125
theorem B578099 : Blo 574812 578099 := bstep (se 1 (by rfl) ⟨433574, by rfl⟩ : syracuseStep 578099 = 867149) B867149
theorem B578115 : Blo 574812 578115 := bstep (se 1 (by rfl) ⟨433586, by rfl⟩ : syracuseStep 578115 = 867173) B867173
theorem B971345 : Blo 574812 971345 := bstep (se 2 (by rfl) ⟨364254, by rfl⟩ : syracuseStep 971345 = 728509) B728509
theorem B578131 : Blo 574812 578131 := bstep (se 1 (by rfl) ⟨433598, by rfl⟩ : syracuseStep 578131 = 867197) B867197
theorem B578147 : Blo 574812 578147 := bstep (se 1 (by rfl) ⟨433610, by rfl⟩ : syracuseStep 578147 = 867221) B867221
theorem B1692269 : Blo 574812 1692269 := bstep (se 3 (by rfl) ⟨317300, by rfl⟩ : syracuseStep 1692269 = 634601) B634601
theorem B578163 : Blo 574812 578163 := bstep (se 1 (by rfl) ⟨433622, by rfl⟩ : syracuseStep 578163 = 867245) B867245
theorem B578179 : Blo 574812 578179 := bstep (se 1 (by rfl) ⟨433634, by rfl⟩ : syracuseStep 578179 = 867269) B867269
theorem B578195 : Blo 574812 578195 := bstep (se 1 (by rfl) ⟨433646, by rfl⟩ : syracuseStep 578195 = 867293) B867293
theorem B1233571 : Blo 574812 1233571 := bstep (se 1 (by rfl) ⟨925178, by rfl⟩ : syracuseStep 1233571 = 1850357) B1850357
theorem B578211 : Blo 574812 578211 := bstep (se 1 (by rfl) ⟨433658, by rfl⟩ : syracuseStep 578211 = 867317) B867317
theorem B1462961 : Blo 574812 1462961 := bstep (se 2 (by rfl) ⟨548610, by rfl⟩ : syracuseStep 1462961 = 1097221) B1097221
theorem B578227 : Blo 574812 578227 := bstep (se 1 (by rfl) ⟨433670, by rfl⟩ : syracuseStep 578227 = 867341) B867341
theorem B578243 : Blo 574812 578243 := bstep (se 1 (by rfl) ⟨433682, by rfl⟩ : syracuseStep 578243 = 867365) B867365
theorem B971473 : Blo 574812 971473 := bstep (se 2 (by rfl) ⟨364302, by rfl⟩ : syracuseStep 971473 = 728605) B728605
theorem B578259 : Blo 574812 578259 := bstep (se 1 (by rfl) ⟨433694, by rfl⟩ : syracuseStep 578259 = 867389) B867389
theorem B578275 : Blo 574812 578275 := bstep (se 1 (by rfl) ⟨433706, by rfl⟩ : syracuseStep 578275 = 867413) B867413
theorem B1299185 : Blo 574812 1299185 := bstep (se 2 (by rfl) ⟨487194, by rfl⟩ : syracuseStep 1299185 = 974389) B974389
theorem B971507 : Blo 574812 971507 := bstep (se 1 (by rfl) ⟨728630, by rfl⟩ : syracuseStep 971507 = 1457261) B1457261
theorem B578291 : Blo 574812 578291 := bstep (se 1 (by rfl) ⟨433718, by rfl⟩ : syracuseStep 578291 = 867437) B867437
theorem B1299203 : Blo 574812 1299203 := bstep (se 1 (by rfl) ⟨974402, by rfl⟩ : syracuseStep 1299203 = 1948805) B1948805
theorem B578307 : Blo 574812 578307 := bstep (se 1 (by rfl) ⟨433730, by rfl⟩ : syracuseStep 578307 = 867461) B867461
theorem B578323 : Blo 574812 578323 := bstep (se 1 (by rfl) ⟨433742, by rfl⟩ : syracuseStep 578323 = 867485) B867485
theorem B578339 : Blo 574812 578339 := bstep (se 1 (by rfl) ⟨433754, by rfl⟩ : syracuseStep 578339 = 867509) B867509
theorem B2216753 : Blo 574812 2216753 := bstep (se 2 (by rfl) ⟨831282, by rfl⟩ : syracuseStep 2216753 = 1662565) B1662565
theorem B578355 : Blo 574812 578355 := bstep (se 1 (by rfl) ⟨433766, by rfl⟩ : syracuseStep 578355 = 867533) B867533
theorem B578371 : Blo 574812 578371 := bstep (se 1 (by rfl) ⟨433778, by rfl⟩ : syracuseStep 578371 = 867557) B867557
theorem B578387 : Blo 574812 578387 := bstep (se 1 (by rfl) ⟨433790, by rfl⟩ : syracuseStep 578387 = 867581) B867581
theorem B578403 : Blo 574812 578403 := bstep (se 1 (by rfl) ⟨433802, by rfl⟩ : syracuseStep 578403 = 867605) B867605
theorem B2085745 : Blo 574812 2085745 := bstep (se 2 (by rfl) ⟨782154, by rfl⟩ : syracuseStep 2085745 = 1564309) B1564309
theorem B971635 : Blo 574812 971635 := bstep (se 1 (by rfl) ⟨728726, by rfl⟩ : syracuseStep 971635 = 1457453) B1457453
theorem B578419 : Blo 574812 578419 := bstep (se 1 (by rfl) ⟨433814, by rfl⟩ : syracuseStep 578419 = 867629) B867629
theorem B578435 : Blo 574812 578435 := bstep (se 1 (by rfl) ⟨433826, by rfl⟩ : syracuseStep 578435 = 867653) B867653
theorem B578451 : Blo 574812 578451 := bstep (se 1 (by rfl) ⟨433838, by rfl⟩ : syracuseStep 578451 = 867677) B867677
theorem B578467 : Blo 574812 578467 := bstep (se 1 (by rfl) ⟨433850, by rfl⟩ : syracuseStep 578467 = 867701) B867701
theorem B578483 : Blo 574812 578483 := bstep (se 1 (by rfl) ⟨433862, by rfl⟩ : syracuseStep 578483 = 867725) B867725
theorem B578499 : Blo 574812 578499 := bstep (se 1 (by rfl) ⟨433874, by rfl⟩ : syracuseStep 578499 = 867749) B867749
theorem B578515 : Blo 574812 578515 := bstep (se 1 (by rfl) ⟨433886, by rfl⟩ : syracuseStep 578515 = 867773) B867773
theorem B578531 : Blo 574812 578531 := bstep (se 1 (by rfl) ⟨433898, by rfl⟩ : syracuseStep 578531 = 867797) B867797
theorem B578547 : Blo 574812 578547 := bstep (se 1 (by rfl) ⟨433910, by rfl⟩ : syracuseStep 578547 = 867821) B867821
theorem B971777 : Blo 574812 971777 := bstep (se 2 (by rfl) ⟨364416, by rfl⟩ : syracuseStep 971777 = 728833) B728833
theorem B578563 : Blo 574812 578563 := bstep (se 1 (by rfl) ⟨433922, by rfl⟩ : syracuseStep 578563 = 867845) B867845
theorem B2184205 : Blo 574812 2184205 := bstep (se 3 (by rfl) ⟨409538, by rfl⟩ : syracuseStep 2184205 = 819077) B819077
theorem B1299473 : Blo 574812 1299473 := bstep (se 2 (by rfl) ⟨487302, by rfl⟩ : syracuseStep 1299473 = 974605) B974605
theorem B578579 : Blo 574812 578579 := bstep (se 1 (by rfl) ⟨433934, by rfl⟩ : syracuseStep 578579 = 867869) B867869
theorem B1299491 : Blo 574812 1299491 := bstep (se 1 (by rfl) ⟨974618, by rfl⟩ : syracuseStep 1299491 = 1949237) B1949237
theorem B578595 : Blo 574812 578595 := bstep (se 1 (by rfl) ⟨433946, by rfl⟩ : syracuseStep 578595 = 867893) B867893
theorem B578611 : Blo 574812 578611 := bstep (se 1 (by rfl) ⟨433958, by rfl⟩ : syracuseStep 578611 = 867917) B867917
theorem B578627 : Blo 574812 578627 := bstep (se 1 (by rfl) ⟨433970, by rfl⟩ : syracuseStep 578627 = 867941) B867941
theorem B578643 : Blo 574812 578643 := bstep (se 1 (by rfl) ⟨433982, by rfl⟩ : syracuseStep 578643 = 867965) B867965
theorem B578659 : Blo 574812 578659 := bstep (se 1 (by rfl) ⟨433994, by rfl⟩ : syracuseStep 578659 = 867989) B867989
theorem B578675 : Blo 574812 578675 := bstep (se 1 (by rfl) ⟨434006, by rfl⟩ : syracuseStep 578675 = 868013) B868013
theorem B971905 : Blo 574812 971905 := bstep (se 2 (by rfl) ⟨364464, by rfl⟩ : syracuseStep 971905 = 728929) B728929
theorem B578691 : Blo 574812 578691 := bstep (se 1 (by rfl) ⟨434018, by rfl⟩ : syracuseStep 578691 = 868037) B868037
theorem B578707 : Blo 574812 578707 := bstep (se 1 (by rfl) ⟨434030, by rfl⟩ : syracuseStep 578707 = 868061) B868061
theorem B971939 : Blo 574812 971939 := bstep (se 1 (by rfl) ⟨728954, by rfl⟩ : syracuseStep 971939 = 1457909) B1457909
theorem B578723 : Blo 574812 578723 := bstep (se 1 (by rfl) ⟨434042, by rfl⟩ : syracuseStep 578723 = 868085) B868085
theorem B578739 : Blo 574812 578739 := bstep (se 1 (by rfl) ⟨434054, by rfl⟩ : syracuseStep 578739 = 868109) B868109
theorem B578755 : Blo 574812 578755 := bstep (se 1 (by rfl) ⟨434066, by rfl⟩ : syracuseStep 578755 = 868133) B868133
theorem B578771 : Blo 574812 578771 := bstep (se 1 (by rfl) ⟨434078, by rfl⟩ : syracuseStep 578771 = 868157) B868157
theorem B578787 : Blo 574812 578787 := bstep (se 1 (by rfl) ⟨434090, by rfl⟩ : syracuseStep 578787 = 868181) B868181
theorem B578803 : Blo 574812 578803 := bstep (se 1 (by rfl) ⟨434102, by rfl⟩ : syracuseStep 578803 = 868205) B868205
theorem B972067 : Blo 574812 972067 := bstep (se 1 (by rfl) ⟨729050, by rfl⟩ : syracuseStep 972067 = 1458101) B1458101
theorem B1299761 : Blo 574812 1299761 := bstep (se 2 (by rfl) ⟨487410, by rfl⟩ : syracuseStep 1299761 = 974821) B974821
theorem B1299779 : Blo 574812 1299779 := bstep (se 1 (by rfl) ⟨974834, by rfl⟩ : syracuseStep 1299779 = 1949669) B1949669
theorem B1561997 : Blo 574812 1561997 := bstep (se 3 (by rfl) ⟨292874, by rfl⟩ : syracuseStep 1561997 = 585749) B585749
theorem B972209 : Blo 574812 972209 := bstep (se 2 (by rfl) ⟨364578, by rfl⟩ : syracuseStep 972209 = 729157) B729157
theorem B972337 : Blo 574812 972337 := bstep (se 2 (by rfl) ⟨364626, by rfl⟩ : syracuseStep 972337 = 729253) B729253
theorem B3692101 : Blo 574812 3692101 := bstep (se 4 (by rfl) ⟨346134, by rfl⟩ : syracuseStep 3692101 = 692269) B692269
theorem B1300049 : Blo 574812 1300049 := bstep (se 2 (by rfl) ⟨487518, by rfl⟩ : syracuseStep 1300049 = 975037) B975037
theorem B972371 : Blo 574812 972371 := bstep (se 1 (by rfl) ⟨729278, by rfl⟩ : syracuseStep 972371 = 1458557) B1458557
theorem B1300067 : Blo 574812 1300067 := bstep (se 1 (by rfl) ⟨975050, by rfl⟩ : syracuseStep 1300067 = 1950101) B1950101
theorem B1463953 : Blo 574812 1463953 := bstep (se 2 (by rfl) ⟨548982, by rfl⟩ : syracuseStep 1463953 = 1097965) B1097965
theorem B972499 : Blo 574812 972499 := bstep (se 1 (by rfl) ⟨729374, by rfl⟩ : syracuseStep 972499 = 1458749) B1458749
theorem B2184995 : Blo 574812 2184995 := bstep (se 1 (by rfl) ⟨1638746, by rfl⟩ : syracuseStep 2184995 = 3277493) B3277493
theorem B972641 : Blo 574812 972641 := bstep (se 2 (by rfl) ⟨364740, by rfl⟩ : syracuseStep 972641 = 729481) B729481
theorem B1300337 : Blo 574812 1300337 := bstep (se 2 (by rfl) ⟨487626, by rfl⟩ : syracuseStep 1300337 = 975253) B975253
theorem B1234801 : Blo 574812 1234801 := bstep (se 2 (by rfl) ⟨463050, by rfl⟩ : syracuseStep 1234801 = 926101) B926101
theorem B1300355 : Blo 574812 1300355 := bstep (se 1 (by rfl) ⟨975266, by rfl⟩ : syracuseStep 1300355 = 1950533) B1950533
theorem B1464227 : Blo 574812 1464227 := bstep (se 1 (by rfl) ⟨1098170, by rfl⟩ : syracuseStep 1464227 = 2196341) B2196341
theorem B1038275 : Blo 574812 1038275 := bstep (se 1 (by rfl) ⟨778706, by rfl⟩ : syracuseStep 1038275 = 1557413) B1557413
theorem B972769 : Blo 574812 972769 := bstep (se 2 (by rfl) ⟨364788, by rfl⟩ : syracuseStep 972769 = 729577) B729577
theorem B4937699 : Blo 574812 4937699 := bstep (se 1 (by rfl) ⟨3703274, by rfl⟩ : syracuseStep 4937699 = 7406549) B7406549
theorem B972803 : Blo 574812 972803 := bstep (se 1 (by rfl) ⟨729602, by rfl⟩ : syracuseStep 972803 = 1459205) B1459205
theorem B1464419 : Blo 574812 1464419 := bstep (se 1 (by rfl) ⟨1098314, by rfl⟩ : syracuseStep 1464419 = 2196629) B2196629
theorem B972931 : Blo 574812 972931 := bstep (se 1 (by rfl) ⟨729698, by rfl⟩ : syracuseStep 972931 = 1459397) B1459397
theorem B1300625 : Blo 574812 1300625 := bstep (se 2 (by rfl) ⟨487734, by rfl⟩ : syracuseStep 1300625 = 975469) B975469
theorem B1300643 : Blo 574812 1300643 := bstep (se 1 (by rfl) ⟨975482, by rfl⟩ : syracuseStep 1300643 = 1950965) B1950965
theorem B973073 : Blo 574812 973073 := bstep (se 2 (by rfl) ⟨364902, by rfl⟩ : syracuseStep 973073 = 729805) B729805
theorem B1038737 : Blo 574812 1038737 := bstep (se 2 (by rfl) ⟨389526, by rfl⟩ : syracuseStep 1038737 = 779053) B779053
theorem B973201 : Blo 574812 973201 := bstep (se 2 (by rfl) ⟨364950, by rfl⟩ : syracuseStep 973201 = 729901) B729901
theorem B2185649 : Blo 574812 2185649 := bstep (se 2 (by rfl) ⟨819618, by rfl⟩ : syracuseStep 2185649 = 1639237) B1639237
theorem B1300913 : Blo 574812 1300913 := bstep (se 2 (by rfl) ⟨487842, by rfl⟩ : syracuseStep 1300913 = 975685) B975685
theorem B973235 : Blo 574812 973235 := bstep (se 1 (by rfl) ⟨729926, by rfl⟩ : syracuseStep 973235 = 1459853) B1459853
theorem B1300931 : Blo 574812 1300931 := bstep (se 1 (by rfl) ⟨975698, by rfl⟩ : syracuseStep 1300931 = 1951397) B1951397
theorem B4446733 : Blo 574812 4446733 := bstep (se 3 (by rfl) ⟨833762, by rfl⟩ : syracuseStep 4446733 = 1667525) B1667525
theorem B973363 : Blo 574812 973363 := bstep (se 1 (by rfl) ⟨730022, by rfl⟩ : syracuseStep 973363 = 1460045) B1460045
theorem B1235587 : Blo 574812 1235587 := bstep (se 1 (by rfl) ⟨926690, by rfl⟩ : syracuseStep 1235587 = 1853381) B1853381
theorem B973505 : Blo 574812 973505 := bstep (se 2 (by rfl) ⟨365064, by rfl⟩ : syracuseStep 973505 = 730129) B730129
theorem B1301201 : Blo 574812 1301201 := bstep (se 2 (by rfl) ⟨487950, by rfl⟩ : syracuseStep 1301201 = 975901) B975901
theorem B1301219 : Blo 574812 1301219 := bstep (se 1 (by rfl) ⟨975914, by rfl⟩ : syracuseStep 1301219 = 1951829) B1951829
theorem B973633 : Blo 574812 973633 := bstep (se 2 (by rfl) ⟨365112, by rfl⟩ : syracuseStep 973633 = 730225) B730225
theorem B973667 : Blo 574812 973667 := bstep (se 1 (by rfl) ⟨730250, by rfl⟩ : syracuseStep 973667 = 1460501) B1460501
theorem B6577037 : Blo 574812 6577037 := bstep (se 3 (by rfl) ⟨1233194, by rfl⟩ : syracuseStep 6577037 = 2466389) B2466389
theorem B1039313 : Blo 574812 1039313 := bstep (se 2 (by rfl) ⟨389742, by rfl⟩ : syracuseStep 1039313 = 779485) B779485
theorem B973795 : Blo 574812 973795 := bstep (se 1 (by rfl) ⟨730346, by rfl⟩ : syracuseStep 973795 = 1460693) B1460693
theorem B1301489 : Blo 574812 1301489 := bstep (se 2 (by rfl) ⟨488058, by rfl⟩ : syracuseStep 1301489 = 976117) B976117
theorem B1301507 : Blo 574812 1301507 := bstep (se 1 (by rfl) ⟨976130, by rfl⟩ : syracuseStep 1301507 = 1952261) B1952261
theorem B973937 : Blo 574812 973937 := bstep (se 2 (by rfl) ⟨365226, by rfl⟩ : syracuseStep 973937 = 730453) B730453
theorem B974065 : Blo 574812 974065 := bstep (se 2 (by rfl) ⟨365274, by rfl⟩ : syracuseStep 974065 = 730549) B730549
theorem B1301777 : Blo 574812 1301777 := bstep (se 2 (by rfl) ⟨488166, by rfl⟩ : syracuseStep 1301777 = 976333) B976333
theorem B974099 : Blo 574812 974099 := bstep (se 1 (by rfl) ⟨730574, by rfl⟩ : syracuseStep 974099 = 1461149) B1461149
theorem B1301795 : Blo 574812 1301795 := bstep (se 1 (by rfl) ⟨976346, by rfl⟩ : syracuseStep 1301795 = 1952693) B1952693
theorem B1563953 : Blo 574812 1563953 := bstep (se 2 (by rfl) ⟨586482, by rfl⟩ : syracuseStep 1563953 = 1172965) B1172965
theorem B777539 : Blo 574812 777539 := bstep (se 1 (by rfl) ⟨583154, by rfl⟩ : syracuseStep 777539 = 1166309) B1166309
theorem B974227 : Blo 574812 974227 := bstep (se 1 (by rfl) ⟨730670, by rfl⟩ : syracuseStep 974227 = 1461341) B1461341
theorem B1662445 : Blo 574812 1662445 := bstep (se 3 (by rfl) ⟨311708, by rfl⟩ : syracuseStep 1662445 = 623417) B623417
theorem B974369 : Blo 574812 974369 := bstep (se 2 (by rfl) ⟨365388, by rfl⟩ : syracuseStep 974369 = 730777) B730777
theorem B1302065 : Blo 574812 1302065 := bstep (se 2 (by rfl) ⟨488274, by rfl⟩ : syracuseStep 1302065 = 976549) B976549
theorem B1302083 : Blo 574812 1302083 := bstep (se 1 (by rfl) ⟨976562, by rfl⟩ : syracuseStep 1302083 = 1953125) B1953125
theorem B1826381 : Blo 574812 1826381 := bstep (se 3 (by rfl) ⟨342446, by rfl⟩ : syracuseStep 1826381 = 684893) B684893
theorem B646771 : Blo 574812 646771 := bstep (se 1 (by rfl) ⟨485078, by rfl⟩ : syracuseStep 646771 = 970157) B970157
theorem B974497 : Blo 574812 974497 := bstep (se 2 (by rfl) ⟨365436, by rfl⟩ : syracuseStep 974497 = 730873) B730873
theorem B974531 : Blo 574812 974531 := bstep (se 1 (by rfl) ⟨730898, by rfl⟩ : syracuseStep 974531 = 1461797) B1461797
theorem B614099 : Blo 574812 614099 := bstep (se 1 (by rfl) ⟨460574, by rfl⟩ : syracuseStep 614099 = 921149) B921149
theorem B1564397 : Blo 574812 1564397 := bstep (se 3 (by rfl) ⟨293324, by rfl⟩ : syracuseStep 1564397 = 586649) B586649
theorem B646915 : Blo 574812 646915 := bstep (se 1 (by rfl) ⟨485186, by rfl⟩ : syracuseStep 646915 = 970373) B970373
theorem B974659 : Blo 574812 974659 := bstep (se 1 (by rfl) ⟨730994, by rfl⟩ : syracuseStep 974659 = 1461989) B1461989
theorem B2187107 : Blo 574812 2187107 := bstep (se 1 (by rfl) ⟨1640330, by rfl⟩ : syracuseStep 2187107 = 3280661) B3280661
theorem B2187121 : Blo 574812 2187121 := bstep (se 2 (by rfl) ⟨820170, by rfl⟩ : syracuseStep 2187121 = 1640341) B1640341
theorem B647059 : Blo 574812 647059 := bstep (se 1 (by rfl) ⟨485294, by rfl⟩ : syracuseStep 647059 = 970589) B970589
theorem B974801 : Blo 574812 974801 := bstep (se 2 (by rfl) ⟨365550, by rfl⟩ : syracuseStep 974801 = 731101) B731101
theorem B647203 : Blo 574812 647203 := bstep (se 1 (by rfl) ⟨485402, by rfl⟩ : syracuseStep 647203 = 970805) B970805
theorem B974929 : Blo 574812 974929 := bstep (se 2 (by rfl) ⟨365598, by rfl⟩ : syracuseStep 974929 = 731197) B731197
theorem B974963 : Blo 574812 974963 := bstep (se 1 (by rfl) ⟨731222, by rfl⟩ : syracuseStep 974963 = 1462445) B1462445
theorem B647347 : Blo 574812 647347 := bstep (se 1 (by rfl) ⟨485510, by rfl⟩ : syracuseStep 647347 = 971021) B971021
theorem B975091 : Blo 574812 975091 := bstep (se 1 (by rfl) ⟨731318, by rfl⟩ : syracuseStep 975091 = 1462637) B1462637
theorem B647491 : Blo 574812 647491 := bstep (se 1 (by rfl) ⟨485618, by rfl⟩ : syracuseStep 647491 = 971237) B971237
theorem B975233 : Blo 574812 975233 := bstep (se 2 (by rfl) ⟨365712, by rfl⟩ : syracuseStep 975233 = 731425) B731425
theorem B647635 : Blo 574812 647635 := bstep (se 1 (by rfl) ⟨485726, by rfl⟩ : syracuseStep 647635 = 971453) B971453
theorem B3498481 : Blo 574812 3498481 := bstep (se 2 (by rfl) ⟨1311930, by rfl⟩ : syracuseStep 3498481 = 2623861) B2623861
theorem B975361 : Blo 574812 975361 := bstep (se 2 (by rfl) ⟨365760, by rfl⟩ : syracuseStep 975361 = 731521) B731521
theorem B975395 : Blo 574812 975395 := bstep (se 1 (by rfl) ⟨731546, by rfl⟩ : syracuseStep 975395 = 1463093) B1463093
theorem B647779 : Blo 574812 647779 := bstep (se 1 (by rfl) ⟨485834, by rfl⟩ : syracuseStep 647779 = 971669) B971669
theorem B615043 : Blo 574812 615043 := bstep (se 1 (by rfl) ⟨461282, by rfl⟩ : syracuseStep 615043 = 922565) B922565
theorem B975523 : Blo 574812 975523 := bstep (se 1 (by rfl) ⟨731642, by rfl⟩ : syracuseStep 975523 = 1463285) B1463285
theorem B647923 : Blo 574812 647923 := bstep (se 1 (by rfl) ⟨485942, by rfl⟩ : syracuseStep 647923 = 971885) B971885
theorem B975665 : Blo 574812 975665 := bstep (se 2 (by rfl) ⟨365874, by rfl⟩ : syracuseStep 975665 = 731749) B731749
theorem B648067 : Blo 574812 648067 := bstep (se 1 (by rfl) ⟨486050, by rfl⟩ : syracuseStep 648067 = 972101) B972101
theorem B975793 : Blo 574812 975793 := bstep (se 2 (by rfl) ⟨365922, by rfl⟩ : syracuseStep 975793 = 731845) B731845
theorem B975827 : Blo 574812 975827 := bstep (se 1 (by rfl) ⟨731870, by rfl⟩ : syracuseStep 975827 = 1463741) B1463741
theorem B648211 : Blo 574812 648211 := bstep (se 1 (by rfl) ⟨486158, by rfl⟩ : syracuseStep 648211 = 972317) B972317
theorem B3695665 : Blo 574812 3695665 := bstep (se 2 (by rfl) ⟨1385874, by rfl⟩ : syracuseStep 3695665 = 2771749) B2771749
theorem B975955 : Blo 574812 975955 := bstep (se 1 (by rfl) ⟨731966, by rfl⟩ : syracuseStep 975955 = 1463933) B1463933
theorem B648355 : Blo 574812 648355 := bstep (se 1 (by rfl) ⟨486266, by rfl⟩ : syracuseStep 648355 = 972533) B972533
theorem B976097 : Blo 574812 976097 := bstep (se 2 (by rfl) ⟨366036, by rfl⟩ : syracuseStep 976097 = 732073) B732073
theorem B2188579 : Blo 574812 2188579 := bstep (se 1 (by rfl) ⟨1641434, by rfl⟩ : syracuseStep 2188579 = 3282869) B3282869
theorem B648499 : Blo 574812 648499 := bstep (se 1 (by rfl) ⟨486374, by rfl⟩ : syracuseStep 648499 = 972749) B972749
theorem B779603 : Blo 574812 779603 := bstep (se 1 (by rfl) ⟨584702, by rfl⟩ : syracuseStep 779603 = 1169405) B1169405
theorem B976225 : Blo 574812 976225 := bstep (se 2 (by rfl) ⟨366084, by rfl⟩ : syracuseStep 976225 = 732169) B732169
theorem B976259 : Blo 574812 976259 := bstep (se 1 (by rfl) ⟨732194, by rfl⟩ : syracuseStep 976259 = 1464389) B1464389
theorem B648643 : Blo 574812 648643 := bstep (se 1 (by rfl) ⟨486482, by rfl⟩ : syracuseStep 648643 = 972965) B972965
theorem B976387 : Blo 574812 976387 := bstep (se 1 (by rfl) ⟨732290, by rfl⟩ : syracuseStep 976387 = 1464581) B1464581
theorem B648787 : Blo 574812 648787 := bstep (se 1 (by rfl) ⟨486590, by rfl⟩ : syracuseStep 648787 = 973181) B973181
theorem B976529 : Blo 574812 976529 := bstep (se 2 (by rfl) ⟨366198, by rfl⟩ : syracuseStep 976529 = 732397) B732397
theorem B648931 : Blo 574812 648931 := bstep (se 1 (by rfl) ⟨486698, by rfl⟩ : syracuseStep 648931 = 973397) B973397
theorem B6579953 : Blo 574812 6579953 := bstep (se 2 (by rfl) ⟨2467482, by rfl⟩ : syracuseStep 6579953 = 4934965) B4934965
theorem B976657 : Blo 574812 976657 := bstep (se 2 (by rfl) ⟨366246, by rfl⟩ : syracuseStep 976657 = 732493) B732493
theorem B976691 : Blo 574812 976691 := bstep (se 1 (by rfl) ⟨732518, by rfl⟩ : syracuseStep 976691 = 1465037) B1465037
theorem B649075 : Blo 574812 649075 := bstep (se 1 (by rfl) ⟨486806, by rfl⟩ : syracuseStep 649075 = 973613) B973613
theorem B616307 : Blo 574812 616307 := bstep (se 1 (by rfl) ⟨462230, by rfl⟩ : syracuseStep 616307 = 924461) B924461
theorem B1173379 : Blo 574812 1173379 := bstep (se 1 (by rfl) ⟨880034, by rfl⟩ : syracuseStep 1173379 = 1760069) B1760069
theorem B649219 : Blo 574812 649219 := bstep (se 1 (by rfl) ⟨486914, by rfl⟩ : syracuseStep 649219 = 973829) B973829
theorem B3237937 : Blo 574812 3237937 := bstep (se 2 (by rfl) ⟨1214226, by rfl⟩ : syracuseStep 3237937 = 2428453) B2428453
theorem B4155461 : Blo 574812 4155461 := bstep (se 4 (by rfl) ⟨389574, by rfl⟩ : syracuseStep 4155461 = 779149) B779149
theorem B649363 : Blo 574812 649363 := bstep (se 1 (by rfl) ⟨487022, by rfl⟩ : syracuseStep 649363 = 974045) B974045
theorem B583843 : Blo 574812 583843 := bstep (se 1 (by rfl) ⟨437882, by rfl⟩ : syracuseStep 583843 = 875765) B875765
theorem B878867 : Blo 574812 878867 := bstep (se 1 (by rfl) ⟨659150, by rfl⟩ : syracuseStep 878867 = 1318301) B1318301
theorem B649507 : Blo 574812 649507 := bstep (se 1 (by rfl) ⟨487130, by rfl⟩ : syracuseStep 649507 = 974261) B974261
theorem B1042787 : Blo 574812 1042787 := bstep (se 1 (by rfl) ⟨782090, by rfl⟩ : syracuseStep 1042787 = 1564181) B1564181
theorem B1894819 : Blo 574812 1894819 := bstep (se 1 (by rfl) ⟨1421114, by rfl⟩ : syracuseStep 1894819 = 2842229) B2842229
theorem B649651 : Blo 574812 649651 := bstep (se 1 (by rfl) ⟨487238, by rfl⟩ : syracuseStep 649651 = 974477) B974477
theorem B584147 : Blo 574812 584147 := bstep (se 1 (by rfl) ⟨438110, by rfl⟩ : syracuseStep 584147 = 876221) B876221
theorem B2812429 : Blo 574812 2812429 := bstep (se 3 (by rfl) ⟨527330, by rfl⟩ : syracuseStep 2812429 = 1054661) B1054661
theorem B649795 : Blo 574812 649795 := bstep (se 1 (by rfl) ⟨487346, by rfl⟩ : syracuseStep 649795 = 974693) B974693
theorem B617059 : Blo 574812 617059 := bstep (se 1 (by rfl) ⟨462794, by rfl⟩ : syracuseStep 617059 = 925589) B925589
theorem B649939 : Blo 574812 649939 := bstep (se 1 (by rfl) ⟨487454, by rfl⟩ : syracuseStep 649939 = 974909) B974909
theorem B59894549 : Blo 574812 59894549 := bstep (se 6 (by rfl) ⟨1403778, by rfl⟩ : syracuseStep 59894549 = 2807557) B2807557
theorem B650083 : Blo 574812 650083 := bstep (se 1 (by rfl) ⟨487562, by rfl⟩ : syracuseStep 650083 = 975125) B975125
theorem B617315 : Blo 574812 617315 := bstep (se 1 (by rfl) ⟨462986, by rfl⟩ : syracuseStep 617315 = 925973) B925973
theorem B2911139 : Blo 574812 2911139 := bstep (se 1 (by rfl) ⟨2183354, by rfl⟩ : syracuseStep 2911139 = 4366709) B4366709
theorem B748531 : Blo 574812 748531 := bstep (se 1 (by rfl) ⟨561398, by rfl⟩ : syracuseStep 748531 = 1122797) B1122797
theorem B650227 : Blo 574812 650227 := bstep (se 1 (by rfl) ⟨487670, by rfl⟩ : syracuseStep 650227 = 975341) B975341
theorem B650371 : Blo 574812 650371 := bstep (se 1 (by rfl) ⟨487778, by rfl⟩ : syracuseStep 650371 = 975557) B975557
theorem B650515 : Blo 574812 650515 := bstep (se 1 (by rfl) ⟨487886, by rfl⟩ : syracuseStep 650515 = 975773) B975773
theorem B650659 : Blo 574812 650659 := bstep (se 1 (by rfl) ⟨487994, by rfl⟩ : syracuseStep 650659 = 975989) B975989
theorem B3108293 : Blo 574812 3108293 := bstep (se 4 (by rfl) ⟨291402, by rfl⟩ : syracuseStep 3108293 = 582805) B582805
theorem B2190797 : Blo 574812 2190797 := bstep (se 3 (by rfl) ⟨410774, by rfl⟩ : syracuseStep 2190797 = 821549) B821549
theorem B3010097 : Blo 574812 3010097 := bstep (se 2 (by rfl) ⟨1128786, by rfl⟩ : syracuseStep 3010097 = 2257573) B2257573
theorem B650803 : Blo 574812 650803 := bstep (se 1 (by rfl) ⟨488102, by rfl⟩ : syracuseStep 650803 = 976205) B976205
theorem B618067 : Blo 574812 618067 := bstep (se 1 (by rfl) ⟨463550, by rfl⟩ : syracuseStep 618067 = 927101) B927101
theorem B4910705 : Blo 574812 4910705 := bstep (se 2 (by rfl) ⟨1841514, by rfl⟩ : syracuseStep 4910705 = 3683029) B3683029
theorem B650947 : Blo 574812 650947 := bstep (se 1 (by rfl) ⟨488210, by rfl⟩ : syracuseStep 650947 = 976421) B976421
theorem B2911949 : Blo 574812 2911949 := bstep (se 3 (by rfl) ⟨545990, by rfl⟩ : syracuseStep 2911949 = 1091981) B1091981
theorem B651091 : Blo 574812 651091 := bstep (se 1 (by rfl) ⟨488318, by rfl⟩ : syracuseStep 651091 = 976637) B976637
theorem B5140849 : Blo 574812 5140849 := bstep (se 2 (by rfl) ⟨1927818, by rfl⟩ : syracuseStep 5140849 = 3855637) B3855637
theorem B4388579 : Blo 574812 4388579 := bstep (se 1 (by rfl) ⟨3291434, by rfl⟩ : syracuseStep 4388579 = 6582869) B6582869
theorem B8353763 : Blo 574812 8353763 := bstep (se 1 (by rfl) ⟨6265322, by rfl⟩ : syracuseStep 8353763 = 12530645) B12530645
theorem B3799025 : Blo 574812 3799025 := bstep (se 2 (by rfl) ⟨1424634, by rfl⟩ : syracuseStep 3799025 = 2849269) B2849269
theorem B3274829 : Blo 574812 3274829 := bstep (se 3 (by rfl) ⟨614030, by rfl⟩ : syracuseStep 3274829 = 1228061) B1228061
theorem B1112177 : Blo 574812 1112177 := bstep (se 2 (by rfl) ⟨417066, by rfl⟩ : syracuseStep 1112177 = 834133) B834133
theorem B3700997 : Blo 574812 3700997 := bstep (se 4 (by rfl) ⟨346968, by rfl⟩ : syracuseStep 3700997 = 693937) B693937
theorem B2193713 : Blo 574812 2193713 := bstep (se 2 (by rfl) ⟨822642, by rfl⟩ : syracuseStep 2193713 = 1645285) B1645285
theorem B2914865 : Blo 574812 2914865 := bstep (se 2 (by rfl) ⟨1093074, by rfl⟩ : syracuseStep 2914865 = 2186149) B2186149
theorem B3111493 : Blo 574812 3111493 := bstep (se 4 (by rfl) ⟨291702, by rfl⟩ : syracuseStep 3111493 = 583405) B583405
theorem B3275761 : Blo 574812 3275761 := bstep (se 2 (by rfl) ⟨1228410, by rfl⟩ : syracuseStep 3275761 = 2456821) B2456821
theorem B1637425 : Blo 574812 1637425 := bstep (se 2 (by rfl) ⟨614034, by rfl⟩ : syracuseStep 1637425 = 1228069) B1228069
theorem B916561 : Blo 574812 916561 := bstep (se 2 (by rfl) ⟨343710, by rfl⟩ : syracuseStep 916561 = 687421) B687421
theorem B2195171 : Blo 574812 2195171 := bstep (se 1 (by rfl) ⟨1646378, by rfl⟩ : syracuseStep 2195171 = 3292757) B3292757
theorem B2916323 : Blo 574812 2916323 := bstep (se 1 (by rfl) ⟨2187242, by rfl⟩ : syracuseStep 2916323 = 4374485) B4374485
theorem B17268997 : Blo 574812 17268997 := bstep (se 4 (by rfl) ⟨1618968, by rfl⟩ : syracuseStep 17268997 = 3237937) B3237937
theorem B1311347 : Blo 574812 1311347 := bstep (se 1 (by rfl) ⟨983510, by rfl⟩ : syracuseStep 1311347 = 1967021) B1967021
theorem B4162265 : Blo 574812 4162265 := bstep (se 2 (by rfl) ⟨1560849, by rfl⟩ : syracuseStep 4162265 = 3121699) B3121699
theorem B1966913 : Blo 574812 1966913 := bstep (se 2 (by rfl) ⟨737592, by rfl⟩ : syracuseStep 1966913 = 1475185) B1475185
theorem B820057 : Blo 574812 820057 := bstep (se 2 (by rfl) ⟨307521, by rfl⟩ : syracuseStep 820057 = 615043) B615043
theorem B2196355 : Blo 574812 2196355 := bstep (se 1 (by rfl) ⟨1647266, by rfl⟩ : syracuseStep 2196355 = 3294533) B3294533
theorem B1639385 : Blo 574812 1639385 := bstep (se 2 (by rfl) ⟨614769, by rfl⟩ : syracuseStep 1639385 = 1229539) B1229539
theorem B4391981 : Blo 574812 4391981 := bstep (se 3 (by rfl) ⟨823496, by rfl⟩ : syracuseStep 4391981 = 1646993) B1646993
theorem B2196659 : Blo 574812 2196659 := bstep (se 1 (by rfl) ⟨1647494, by rfl⟩ : syracuseStep 2196659 = 3294989) B3294989
theorem B1639703 : Blo 574812 1639703 := bstep (se 1 (by rfl) ⟨1229777, by rfl⟩ : syracuseStep 1639703 = 2459555) B2459555
theorem B4982347 : Blo 574812 4982347 := bstep (se 1 (by rfl) ⟨3736760, by rfl⟩ : syracuseStep 4982347 = 7473521) B7473521
theorem B2459267 : Blo 574812 2459267 := bstep (se 1 (by rfl) ⟨1844450, by rfl⟩ : syracuseStep 2459267 = 3688901) B3688901
theorem B2918105 : Blo 574812 2918105 := bstep (se 2 (by rfl) ⟨1094289, by rfl⟩ : syracuseStep 2918105 = 2188579) B2188579
theorem B2623277 : Blo 574812 2623277 := bstep (se 3 (by rfl) ⟨491864, by rfl⟩ : syracuseStep 2623277 = 983729) B983729
theorem B2197313 : Blo 574812 2197313 := bstep (se 2 (by rfl) ⟨823992, by rfl⟩ : syracuseStep 2197313 = 1647985) B1647985
theorem B624491 : Blo 574812 624491 := bstep (se 1 (by rfl) ⟨468368, by rfl⟩ : syracuseStep 624491 = 936737) B936737
theorem B5244803 : Blo 574812 5244803 := bstep (se 1 (by rfl) ⟨3933602, by rfl⟩ : syracuseStep 5244803 = 7867205) B7867205
theorem B4982705 : Blo 574812 4982705 := bstep (se 2 (by rfl) ⟨1868514, by rfl⟩ : syracuseStep 4982705 = 3737029) B3737029
theorem B1640513 : Blo 574812 1640513 := bstep (se 2 (by rfl) ⟨615192, by rfl⟩ : syracuseStep 1640513 = 1230385) B1230385
theorem B821515 : Blo 574812 821515 := bstep (se 1 (by rfl) ⟨616136, by rfl⟩ : syracuseStep 821515 = 1232273) B1232273
theorem B3115907 : Blo 574812 3115907 := bstep (se 1 (by rfl) ⟨2336930, by rfl⟩ : syracuseStep 3115907 = 4673861) B4673861
theorem B1248151 : Blo 574812 1248151 := bstep (se 1 (by rfl) ⟨936113, by rfl⟩ : syracuseStep 1248151 = 1872227) B1872227
theorem B1477835 : Blo 574812 1477835 := bstep (se 1 (by rfl) ⟨1108376, by rfl⟩ : syracuseStep 1477835 = 2216753) B2216753
theorem B2526425 : Blo 574812 2526425 := bstep (se 2 (by rfl) ⟨947409, by rfl⟩ : syracuseStep 2526425 = 1894819) B1894819
theorem B2919725 : Blo 574812 2919725 := bstep (se 3 (by rfl) ⟨547448, by rfl⟩ : syracuseStep 2919725 = 1094897) B1094897
theorem B822745 : Blo 574812 822745 := bstep (se 2 (by rfl) ⟨308529, by rfl⟩ : syracuseStep 822745 = 617059) B617059
theorem B14814737 : Blo 574812 14814737 := bstep (se 2 (by rfl) ⟨5555526, by rfl⟩ : syracuseStep 14814737 = 11111053) B11111053
theorem B1642187 : Blo 574812 1642187 := bstep (se 1 (by rfl) ⟨1231640, by rfl⟩ : syracuseStep 1642187 = 2463281) B2463281
theorem B921559 : Blo 574812 921559 := bstep (se 1 (by rfl) ⟨691169, by rfl⟩ : syracuseStep 921559 = 1382339) B1382339
theorem B692183 : Blo 574812 692183 := bstep (se 1 (by rfl) ⟨519137, by rfl⟩ : syracuseStep 692183 = 1038275) B1038275
theorem B14028875 : Blo 574812 14028875 := bstep (se 1 (by rfl) ⟨10521656, by rfl⟩ : syracuseStep 14028875 = 21043313) B21043313
theorem B594103 : Blo 574812 594103 := bstep (se 1 (by rfl) ⟨445577, by rfl⟩ : syracuseStep 594103 = 891155) B891155
theorem B692491 : Blo 574812 692491 := bstep (se 1 (by rfl) ⟨519368, by rfl⟩ : syracuseStep 692491 = 1038737) B1038737
theorem B594551 : Blo 574812 594551 := bstep (se 1 (by rfl) ⟨445913, by rfl⟩ : syracuseStep 594551 = 891827) B891827
theorem B692875 : Blo 574812 692875 := bstep (se 1 (by rfl) ⟨519656, by rfl⟩ : syracuseStep 692875 = 1039313) B1039313
theorem B1970909 : Blo 574812 1970909 := bstep (se 3 (by rfl) ⟨369545, by rfl⟩ : syracuseStep 1970909 = 739091) B739091
theorem B4166417 : Blo 574812 4166417 := bstep (se 2 (by rfl) ⟨1562406, by rfl⟩ : syracuseStep 4166417 = 3124813) B3124813
theorem B824089 : Blo 574812 824089 := bstep (se 2 (by rfl) ⟨309033, by rfl⟩ : syracuseStep 824089 = 618067) B618067
theorem B1315673 : Blo 574812 1315673 := bstep (se 2 (by rfl) ⟨493377, by rfl⟩ : syracuseStep 1315673 = 986755) B986755
theorem B7410649 : Blo 574812 7410649 := bstep (se 2 (by rfl) ⟨2778993, by rfl⟩ : syracuseStep 7410649 = 5557987) B5557987
theorem B1643485 : Blo 574812 1643485 := bstep (se 3 (by rfl) ⟨308153, by rfl⟩ : syracuseStep 1643485 = 616307) B616307
theorem B1217587 : Blo 574812 1217587 := bstep (se 1 (by rfl) ⟨913190, by rfl⟩ : syracuseStep 1217587 = 1826381) B1826381
theorem B988247 : Blo 574812 988247 := bstep (se 1 (by rfl) ⟨741185, by rfl⟩ : syracuseStep 988247 = 1482371) B1482371
theorem B1643827 : Blo 574812 1643827 := bstep (se 1 (by rfl) ⟨1232870, by rfl⟩ : syracuseStep 1643827 = 2465741) B2465741
theorem B2463041 : Blo 574812 2463041 := bstep (se 2 (by rfl) ⟨923640, by rfl⟩ : syracuseStep 2463041 = 1847281) B1847281
theorem B1971649 : Blo 574812 1971649 := bstep (se 2 (by rfl) ⟨739368, by rfl⟩ : syracuseStep 1971649 = 1478737) B1478737
theorem B1316567 : Blo 574812 1316567 := bstep (se 1 (by rfl) ⟨987425, by rfl⟩ : syracuseStep 1316567 = 1974851) B1974851
theorem B4888325 : Blo 574812 4888325 := bstep (se 4 (by rfl) ⟨458280, by rfl⟩ : syracuseStep 4888325 = 916561) B916561
theorem B6854465 : Blo 574812 6854465 := bstep (se 2 (by rfl) ⟨2570424, by rfl⟩ : syracuseStep 6854465 = 5140849) B5140849
theorem B3938179 : Blo 574812 3938179 := bstep (se 1 (by rfl) ⟨2953634, by rfl⟩ : syracuseStep 3938179 = 5907269) B5907269
theorem B923609 : Blo 574812 923609 := bstep (se 2 (by rfl) ⟨346353, by rfl⟩ : syracuseStep 923609 = 692707) B692707
theorem B1644761 : Blo 574812 1644761 := bstep (se 2 (by rfl) ⟨616785, by rfl⟩ : syracuseStep 1644761 = 1233571) B1233571
theorem B2463965 : Blo 574812 2463965 := bstep (se 3 (by rfl) ⟨461993, by rfl⟩ : syracuseStep 2463965 = 923987) B923987
theorem B9837125 : Blo 574812 9837125 := bstep (se 4 (by rfl) ⟨922230, by rfl⟩ : syracuseStep 9837125 = 1844461) B1844461
theorem B1940057 : Blo 574812 1940057 := bstep (se 2 (by rfl) ⟨727521, by rfl⟩ : syracuseStep 1940057 = 1455043) B1455043
theorem B4922117 : Blo 574812 4922117 := bstep (se 4 (by rfl) ⟨461448, by rfl⟩ : syracuseStep 4922117 = 922897) B922897
theorem B695191 : Blo 574812 695191 := bstep (se 1 (by rfl) ⟨521393, by rfl⟩ : syracuseStep 695191 = 1042787) B1042787
theorem B728023 : Blo 574812 728023 := bstep (se 1 (by rfl) ⟨546017, by rfl⟩ : syracuseStep 728023 = 1092035) B1092035
theorem B2628683 : Blo 574812 2628683 := bstep (se 1 (by rfl) ⟨1971512, by rfl⟩ : syracuseStep 2628683 = 3943025) B3943025
theorem B2923613 : Blo 574812 2923613 := bstep (se 3 (by rfl) ⟨548177, by rfl⟩ : syracuseStep 2923613 = 1096355) B1096355
theorem B1940759 : Blo 574812 1940759 := bstep (se 1 (by rfl) ⟨1455569, by rfl⟩ : syracuseStep 1940759 = 2911139) B2911139
theorem B1383731 : Blo 574812 1383731 := bstep (se 1 (by rfl) ⟨1037798, by rfl⟩ : syracuseStep 1383731 = 2075597) B2075597
theorem B4922801 : Blo 574812 4922801 := bstep (se 2 (by rfl) ⟨1846050, by rfl⟩ : syracuseStep 4922801 = 3692101) B3692101
theorem B2072081 : Blo 574812 2072081 := bstep (se 2 (by rfl) ⟨777030, by rfl⟩ : syracuseStep 2072081 = 1554061) B1554061
theorem B1646173 : Blo 574812 1646173 := bstep (se 3 (by rfl) ⟨308657, by rfl⟩ : syracuseStep 1646173 = 617315) B617315
theorem B2072195 : Blo 574812 2072195 := bstep (se 1 (by rfl) ⟨1554146, by rfl⟩ : syracuseStep 2072195 = 3108293) B3108293
theorem B2956979 : Blo 574812 2956979 := bstep (se 1 (by rfl) ⟨2217734, by rfl⟩ : syracuseStep 2956979 = 4435469) B4435469
theorem B2006731 : Blo 574812 2006731 := bstep (se 1 (by rfl) ⟨1505048, by rfl⟩ : syracuseStep 2006731 = 3010097) B3010097
theorem B1941299 : Blo 574812 1941299 := bstep (se 1 (by rfl) ⟨1455974, by rfl⟩ : syracuseStep 1941299 = 2911949) B2911949
theorem B1646401 : Blo 574812 1646401 := bstep (se 2 (by rfl) ⟨617400, by rfl⟩ : syracuseStep 1646401 = 1234801) B1234801
theorem B1941569 : Blo 574812 1941569 := bstep (se 2 (by rfl) ⟨728088, by rfl⟩ : syracuseStep 1941569 = 1456177) B1456177
theorem B1646743 : Blo 574812 1646743 := bstep (se 1 (by rfl) ⟨1235057, by rfl⟩ : syracuseStep 1646743 = 2470115) B2470115
theorem B4923827 : Blo 574812 4923827 := bstep (se 1 (by rfl) ⟨3692870, by rfl⟩ : syracuseStep 4923827 = 7385741) B7385741
theorem B1942109 : Blo 574812 1942109 := bstep (se 3 (by rfl) ⟨364145, by rfl⟩ : syracuseStep 1942109 = 728291) B728291
theorem B729739 : Blo 574812 729739 := bstep (se 1 (by rfl) ⟨547304, by rfl⟩ : syracuseStep 729739 = 1094609) B1094609
theorem B4170541 : Blo 574812 4170541 := bstep (se 3 (by rfl) ⟨781976, by rfl⟩ : syracuseStep 4170541 = 1563953) B1563953
theorem B1647449 : Blo 574812 1647449 := bstep (se 2 (by rfl) ⟨617793, by rfl⟩ : syracuseStep 1647449 = 1235587) B1235587
theorem B2073437 : Blo 574812 2073437 := bstep (se 3 (by rfl) ⟨388769, by rfl⟩ : syracuseStep 2073437 = 777539) B777539
theorem B2925719 : Blo 574812 2925719 := bstep (se 1 (by rfl) ⟨2194289, by rfl⟩ : syracuseStep 2925719 = 4388579) B4388579
theorem B4367681 : Blo 574812 4367681 := bstep (se 2 (by rfl) ⟨1637880, by rfl⟩ : syracuseStep 4367681 = 3275761) B3275761
theorem B2532683 : Blo 574812 2532683 := bstep (se 1 (by rfl) ⟨1899512, by rfl⟩ : syracuseStep 2532683 = 3799025) B3799025
theorem B2467331 : Blo 574812 2467331 := bstep (se 1 (by rfl) ⟨1850498, by rfl⟩ : syracuseStep 2467331 = 3700997) B3700997
theorem B730711 : Blo 574812 730711 := bstep (se 1 (by rfl) ⟨548033, by rfl⟩ : syracuseStep 730711 = 1096067) B1096067
theorem B1943243 : Blo 574812 1943243 := bstep (se 1 (by rfl) ⟨1457432, by rfl⟩ : syracuseStep 1943243 = 2914865) B2914865
theorem B1943513 : Blo 574812 1943513 := bstep (se 2 (by rfl) ⟨728817, by rfl⟩ : syracuseStep 1943513 = 1457635) B1457635
theorem B862283 : Blo 574812 862283 := bstep (se 1 (by rfl) ⟨646712, by rfl⟩ : syracuseStep 862283 = 1293425) B1293425
theorem B6563915 : Blo 574812 6563915 := bstep (se 1 (by rfl) ⟨4922936, by rfl⟩ : syracuseStep 6563915 = 9845873) B9845873
theorem B862295 : Blo 574812 862295 := bstep (se 1 (by rfl) ⟨646721, by rfl⟩ : syracuseStep 862295 = 1293443) B1293443
theorem B862361 : Blo 574812 862361 := bstep (se 2 (by rfl) ⟨323385, by rfl⟩ : syracuseStep 862361 = 646771) B646771
theorem B665803 : Blo 574812 665803 := bstep (se 1 (by rfl) ⟨499352, by rfl⟩ : syracuseStep 665803 = 998705) B998705
theorem B862475 : Blo 574812 862475 := bstep (se 1 (by rfl) ⟨646856, by rfl⟩ : syracuseStep 862475 = 1293713) B1293713
theorem B862487 : Blo 574812 862487 := bstep (se 1 (by rfl) ⟨646865, by rfl⟩ : syracuseStep 862487 = 1293731) B1293731
theorem B1386827 : Blo 574812 1386827 := bstep (se 1 (by rfl) ⟨1040120, by rfl⟩ : syracuseStep 1386827 = 2080241) B2080241
theorem B862553 : Blo 574812 862553 := bstep (se 2 (by rfl) ⟨323457, by rfl⟩ : syracuseStep 862553 = 646915) B646915
theorem B731531 : Blo 574812 731531 := bstep (se 1 (by rfl) ⟨548648, by rfl⟩ : syracuseStep 731531 = 1097297) B1097297
theorem B862667 : Blo 574812 862667 := bstep (se 1 (by rfl) ⟨647000, by rfl⟩ : syracuseStep 862667 = 1294001) B1294001
theorem B862679 : Blo 574812 862679 := bstep (se 1 (by rfl) ⟨647009, by rfl⟩ : syracuseStep 862679 = 1294019) B1294019
theorem B862745 : Blo 574812 862745 := bstep (se 2 (by rfl) ⟨323529, by rfl⟩ : syracuseStep 862745 = 647059) B647059
theorem B2107949 : Blo 574812 2107949 := bstep (se 3 (by rfl) ⟨395240, by rfl⟩ : syracuseStep 2107949 = 790481) B790481
theorem B862859 : Blo 574812 862859 := bstep (se 1 (by rfl) ⟨647144, by rfl⟩ : syracuseStep 862859 = 1294289) B1294289
theorem B862871 : Blo 574812 862871 := bstep (se 1 (by rfl) ⟨647153, by rfl⟩ : syracuseStep 862871 = 1294307) B1294307
theorem B1944215 : Blo 574812 1944215 := bstep (se 1 (by rfl) ⟨1458161, by rfl⟩ : syracuseStep 1944215 = 2916323) B2916323
theorem B862937 : Blo 574812 862937 := bstep (se 2 (by rfl) ⟨323601, by rfl⟩ : syracuseStep 862937 = 647203) B647203
theorem B2075395 : Blo 574812 2075395 := bstep (se 1 (by rfl) ⟨1556546, by rfl⟩ : syracuseStep 2075395 = 3113093) B3113093
theorem B863051 : Blo 574812 863051 := bstep (se 1 (by rfl) ⟨647288, by rfl⟩ : syracuseStep 863051 = 1294577) B1294577
theorem B1846091 : Blo 574812 1846091 := bstep (se 1 (by rfl) ⟨1384568, by rfl⟩ : syracuseStep 1846091 = 2769137) B2769137
theorem B863063 : Blo 574812 863063 := bstep (se 1 (by rfl) ⟨647297, by rfl⟩ : syracuseStep 863063 = 1294595) B1294595
theorem B1092467 : Blo 574812 1092467 := bstep (se 1 (by rfl) ⟨819350, by rfl⟩ : syracuseStep 1092467 = 1638701) B1638701
theorem B863129 : Blo 574812 863129 := bstep (se 2 (by rfl) ⟨323673, by rfl⟩ : syracuseStep 863129 = 647347) B647347
theorem B863243 : Blo 574812 863243 := bstep (se 1 (by rfl) ⟨647432, by rfl⟩ : syracuseStep 863243 = 1294865) B1294865
theorem B1092619 : Blo 574812 1092619 := bstep (se 1 (by rfl) ⟨819464, by rfl⟩ : syracuseStep 1092619 = 1638929) B1638929
theorem B863255 : Blo 574812 863255 := bstep (se 1 (by rfl) ⟨647441, by rfl⟩ : syracuseStep 863255 = 1294883) B1294883
theorem B2632769 : Blo 574812 2632769 := bstep (se 2 (by rfl) ⟨987288, by rfl⟩ : syracuseStep 2632769 = 1974577) B1974577
theorem B732235 : Blo 574812 732235 := bstep (se 1 (by rfl) ⟨549176, by rfl⟩ : syracuseStep 732235 = 1098353) B1098353
theorem B863321 : Blo 574812 863321 := bstep (se 2 (by rfl) ⟨323745, by rfl⟩ : syracuseStep 863321 = 647491) B647491
theorem B1944755 : Blo 574812 1944755 := bstep (se 1 (by rfl) ⟨1458566, by rfl⟩ : syracuseStep 1944755 = 2917133) B2917133
theorem B1748171 : Blo 574812 1748171 := bstep (se 1 (by rfl) ⟨1311128, by rfl⟩ : syracuseStep 1748171 = 2622257) B2622257
theorem B863435 : Blo 574812 863435 := bstep (se 1 (by rfl) ⟨647576, by rfl⟩ : syracuseStep 863435 = 1295153) B1295153
theorem B863447 : Blo 574812 863447 := bstep (se 1 (by rfl) ⟨647585, by rfl⟩ : syracuseStep 863447 = 1295171) B1295171
theorem B4369625 : Blo 574812 4369625 := bstep (se 2 (by rfl) ⟨1638609, by rfl⟩ : syracuseStep 4369625 = 3277219) B3277219
theorem B863513 : Blo 574812 863513 := bstep (se 2 (by rfl) ⟨323817, by rfl⟩ : syracuseStep 863513 = 647635) B647635
theorem B4664641 : Blo 574812 4664641 := bstep (se 2 (by rfl) ⟨1749240, by rfl⟩ : syracuseStep 4664641 = 3498481) B3498481
theorem B732503 : Blo 574812 732503 := bstep (se 1 (by rfl) ⟨549377, by rfl⟩ : syracuseStep 732503 = 1098755) B1098755
theorem B1092953 : Blo 574812 1092953 := bstep (se 2 (by rfl) ⟨409857, by rfl⟩ : syracuseStep 1092953 = 819715) B819715
theorem B863627 : Blo 574812 863627 := bstep (se 1 (by rfl) ⟨647720, by rfl⟩ : syracuseStep 863627 = 1295441) B1295441
theorem B863639 : Blo 574812 863639 := bstep (se 1 (by rfl) ⟨647729, by rfl⟩ : syracuseStep 863639 = 1295459) B1295459
theorem B1945025 : Blo 574812 1945025 := bstep (se 2 (by rfl) ⟨729384, by rfl⟩ : syracuseStep 1945025 = 1458769) B1458769
theorem B863705 : Blo 574812 863705 := bstep (se 2 (by rfl) ⟨323889, by rfl⟩ : syracuseStep 863705 = 647779) B647779
theorem B863819 : Blo 574812 863819 := bstep (se 1 (by rfl) ⟨647864, by rfl⟩ : syracuseStep 863819 = 1295729) B1295729
theorem B863831 : Blo 574812 863831 := bstep (se 1 (by rfl) ⟨647873, by rfl⟩ : syracuseStep 863831 = 1295747) B1295747
theorem B863897 : Blo 574812 863897 := bstep (se 2 (by rfl) ⟨323961, by rfl⟩ : syracuseStep 863897 = 647923) B647923
theorem B864011 : Blo 574812 864011 := bstep (se 1 (by rfl) ⟨648008, by rfl⟩ : syracuseStep 864011 = 1296017) B1296017
theorem B864023 : Blo 574812 864023 := bstep (se 1 (by rfl) ⟨648017, by rfl⟩ : syracuseStep 864023 = 1296035) B1296035
theorem B1978187 : Blo 574812 1978187 := bstep (se 1 (by rfl) ⟨1483640, by rfl⟩ : syracuseStep 1978187 = 2967281) B2967281
theorem B864089 : Blo 574812 864089 := bstep (se 2 (by rfl) ⟨324033, by rfl⟩ : syracuseStep 864089 = 648067) B648067
theorem B864203 : Blo 574812 864203 := bstep (se 1 (by rfl) ⟨648152, by rfl⟩ : syracuseStep 864203 = 1296305) B1296305
theorem B1093591 : Blo 574812 1093591 := bstep (se 1 (by rfl) ⟨820193, by rfl⟩ : syracuseStep 1093591 = 1640387) B1640387
theorem B864215 : Blo 574812 864215 := bstep (se 1 (by rfl) ⟨648161, by rfl⟩ : syracuseStep 864215 = 1296323) B1296323
theorem B1945565 : Blo 574812 1945565 := bstep (se 3 (by rfl) ⟨364793, by rfl⟩ : syracuseStep 1945565 = 729587) B729587
theorem B864281 : Blo 574812 864281 := bstep (se 2 (by rfl) ⟨324105, by rfl⟩ : syracuseStep 864281 = 648211) B648211
theorem B4927553 : Blo 574812 4927553 := bstep (se 2 (by rfl) ⟨1847832, by rfl⟩ : syracuseStep 4927553 = 3695665) B3695665
theorem B864395 : Blo 574812 864395 := bstep (se 1 (by rfl) ⟨648296, by rfl⟩ : syracuseStep 864395 = 1296593) B1296593
theorem B864407 : Blo 574812 864407 := bstep (se 1 (by rfl) ⟨648305, by rfl⟩ : syracuseStep 864407 = 1296611) B1296611
theorem B864473 : Blo 574812 864473 := bstep (se 2 (by rfl) ⟨324177, by rfl⟩ : syracuseStep 864473 = 648355) B648355
theorem B3289409 : Blo 574812 3289409 := bstep (se 2 (by rfl) ⟨1233528, by rfl⟩ : syracuseStep 3289409 = 2467057) B2467057
theorem B864587 : Blo 574812 864587 := bstep (se 1 (by rfl) ⟨648440, by rfl⟩ : syracuseStep 864587 = 1296881) B1296881
theorem B864599 : Blo 574812 864599 := bstep (se 1 (by rfl) ⟨648449, by rfl⟩ : syracuseStep 864599 = 1296899) B1296899
theorem B1388951 : Blo 574812 1388951 := bstep (se 1 (by rfl) ⟨1041713, by rfl⟩ : syracuseStep 1388951 = 2083427) B2083427
theorem B864665 : Blo 574812 864665 := bstep (se 2 (by rfl) ⟨324249, by rfl⟩ : syracuseStep 864665 = 648499) B648499
theorem B1847731 : Blo 574812 1847731 := bstep (se 1 (by rfl) ⟨1385798, by rfl⟩ : syracuseStep 1847731 = 2771597) B2771597
theorem B864779 : Blo 574812 864779 := bstep (se 1 (by rfl) ⟨648584, by rfl⟩ : syracuseStep 864779 = 1297169) B1297169
theorem B864791 : Blo 574812 864791 := bstep (se 1 (by rfl) ⟨648593, by rfl⟩ : syracuseStep 864791 = 1297187) B1297187
theorem B864857 : Blo 574812 864857 := bstep (se 2 (by rfl) ⟨324321, by rfl⟩ : syracuseStep 864857 = 648643) B648643
theorem B1847897 : Blo 574812 1847897 := bstep (se 2 (by rfl) ⟨692961, by rfl⟩ : syracuseStep 1847897 = 1385923) B1385923
theorem B2929283 : Blo 574812 2929283 := bstep (se 1 (by rfl) ⟨2196962, by rfl⟩ : syracuseStep 2929283 = 4393925) B4393925
theorem B864971 : Blo 574812 864971 := bstep (se 1 (by rfl) ⟨648728, by rfl⟩ : syracuseStep 864971 = 1297457) B1297457
theorem B8303309 : Blo 574812 8303309 := bstep (se 3 (by rfl) ⟨1556870, by rfl⟩ : syracuseStep 8303309 = 3113741) B3113741
theorem B864983 : Blo 574812 864983 := bstep (se 1 (by rfl) ⟨648737, by rfl⟩ : syracuseStep 864983 = 1297475) B1297475
theorem B1094411 : Blo 574812 1094411 := bstep (se 1 (by rfl) ⟨820808, by rfl⟩ : syracuseStep 1094411 = 1641617) B1641617
theorem B865049 : Blo 574812 865049 := bstep (se 2 (by rfl) ⟨324393, by rfl⟩ : syracuseStep 865049 = 648787) B648787
theorem B1094465 : Blo 574812 1094465 := bstep (se 2 (by rfl) ⟨410424, by rfl⟩ : syracuseStep 1094465 = 820849) B820849
theorem B2503489 : Blo 574812 2503489 := bstep (se 2 (by rfl) ⟨938808, by rfl⟩ : syracuseStep 2503489 = 1877617) B1877617
theorem B865163 : Blo 574812 865163 := bstep (se 1 (by rfl) ⟨648872, by rfl⟩ : syracuseStep 865163 = 1297745) B1297745
theorem B865175 : Blo 574812 865175 := bstep (se 1 (by rfl) ⟨648881, by rfl⟩ : syracuseStep 865175 = 1297763) B1297763
theorem B865241 : Blo 574812 865241 := bstep (se 2 (by rfl) ⟨324465, by rfl⟩ : syracuseStep 865241 = 648931) B648931
theorem B1455155 : Blo 574812 1455155 := bstep (se 1 (by rfl) ⟨1091366, by rfl⟩ : syracuseStep 1455155 = 2182733) B2182733
theorem B1946699 : Blo 574812 1946699 := bstep (se 1 (by rfl) ⟨1460024, by rfl⟩ : syracuseStep 1946699 = 2920049) B2920049
theorem B865355 : Blo 574812 865355 := bstep (se 1 (by rfl) ⟨649016, by rfl⟩ : syracuseStep 865355 = 1298033) B1298033
theorem B865367 : Blo 574812 865367 := bstep (se 1 (by rfl) ⟨649025, by rfl⟩ : syracuseStep 865367 = 1298051) B1298051
theorem B701579 : Blo 574812 701579 := bstep (se 1 (by rfl) ⟨526184, by rfl⟩ : syracuseStep 701579 = 1052369) B1052369
theorem B865433 : Blo 574812 865433 := bstep (se 2 (by rfl) ⟨324537, by rfl⟩ : syracuseStep 865433 = 649075) B649075
theorem B865547 : Blo 574812 865547 := bstep (se 1 (by rfl) ⟨649160, by rfl⟩ : syracuseStep 865547 = 1298321) B1298321
theorem B3126545 : Blo 574812 3126545 := bstep (se 2 (by rfl) ⟨1172454, by rfl⟩ : syracuseStep 3126545 = 2344909) B2344909
theorem B865559 : Blo 574812 865559 := bstep (se 1 (by rfl) ⟨649169, by rfl⟩ : syracuseStep 865559 = 1298339) B1298339
theorem B1750337 : Blo 574812 1750337 := bstep (se 2 (by rfl) ⟨656376, by rfl⟩ : syracuseStep 1750337 = 1312753) B1312753
theorem B1946969 : Blo 574812 1946969 := bstep (se 2 (by rfl) ⟨730113, by rfl⟩ : syracuseStep 1946969 = 1460227) B1460227
theorem B1848665 : Blo 574812 1848665 := bstep (se 2 (by rfl) ⟨693249, by rfl⟩ : syracuseStep 1848665 = 1386499) B1386499
theorem B865625 : Blo 574812 865625 := bstep (se 2 (by rfl) ⟨324609, by rfl⟩ : syracuseStep 865625 = 649219) B649219
theorem B2635139 : Blo 574812 2635139 := bstep (se 1 (by rfl) ⟨1976354, by rfl⟩ : syracuseStep 2635139 = 3952709) B3952709
theorem B1553843 : Blo 574812 1553843 := bstep (se 1 (by rfl) ⟨1165382, by rfl⟩ : syracuseStep 1553843 = 2330765) B2330765
theorem B865739 : Blo 574812 865739 := bstep (se 1 (by rfl) ⟨649304, by rfl⟩ : syracuseStep 865739 = 1298609) B1298609
theorem B865751 : Blo 574812 865751 := bstep (se 1 (by rfl) ⟨649313, by rfl⟩ : syracuseStep 865751 = 1298627) B1298627
theorem B2471447 : Blo 574812 2471447 := bstep (se 1 (by rfl) ⟨1853585, by rfl⟩ : syracuseStep 2471447 = 3707171) B3707171
theorem B865817 : Blo 574812 865817 := bstep (se 2 (by rfl) ⟨324681, by rfl⟩ : syracuseStep 865817 = 649363) B649363
theorem B1455691 : Blo 574812 1455691 := bstep (se 1 (by rfl) ⟨1091768, by rfl⟩ : syracuseStep 1455691 = 2183537) B2183537
theorem B865931 : Blo 574812 865931 := bstep (se 1 (by rfl) ⟨649448, by rfl⟩ : syracuseStep 865931 = 1298897) B1298897
theorem B997015 : Blo 574812 997015 := bstep (se 1 (by rfl) ⟨747761, by rfl⟩ : syracuseStep 997015 = 1495523) B1495523
theorem B865943 : Blo 574812 865943 := bstep (se 1 (by rfl) ⟨649457, by rfl⟩ : syracuseStep 865943 = 1298915) B1298915
theorem B1095383 : Blo 574812 1095383 := bstep (se 1 (by rfl) ⟨821537, by rfl⟩ : syracuseStep 1095383 = 1643075) B1643075
theorem B1455833 : Blo 574812 1455833 := bstep (se 2 (by rfl) ⟨545937, by rfl⟩ : syracuseStep 1455833 = 1091875) B1091875
theorem B866009 : Blo 574812 866009 := bstep (se 2 (by rfl) ⟨324753, by rfl⟩ : syracuseStep 866009 = 649507) B649507
theorem B1128179 : Blo 574812 1128179 := bstep (se 1 (by rfl) ⟨846134, by rfl⟩ : syracuseStep 1128179 = 1692269) B1692269
theorem B866123 : Blo 574812 866123 := bstep (se 1 (by rfl) ⟨649592, by rfl⟩ : syracuseStep 866123 = 1299185) B1299185
theorem B2471755 : Blo 574812 2471755 := bstep (se 1 (by rfl) ⟨1853816, by rfl⟩ : syracuseStep 2471755 = 3707633) B3707633
theorem B866135 : Blo 574812 866135 := bstep (se 1 (by rfl) ⟨649601, by rfl⟩ : syracuseStep 866135 = 1299203) B1299203
theorem B1849177 : Blo 574812 1849177 := bstep (se 2 (by rfl) ⟨693441, by rfl⟩ : syracuseStep 1849177 = 1386883) B1386883
theorem B866201 : Blo 574812 866201 := bstep (se 2 (by rfl) ⟨324825, by rfl⟩ : syracuseStep 866201 = 649651) B649651
theorem B866315 : Blo 574812 866315 := bstep (se 1 (by rfl) ⟨649736, by rfl⟩ : syracuseStep 866315 = 1299473) B1299473
theorem B3749905 : Blo 574812 3749905 := bstep (se 2 (by rfl) ⟨1406214, by rfl⟩ : syracuseStep 3749905 = 2812429) B2812429
theorem B1947671 : Blo 574812 1947671 := bstep (se 1 (by rfl) ⟨1460753, by rfl⟩ : syracuseStep 1947671 = 2921507) B2921507
theorem B866327 : Blo 574812 866327 := bstep (se 1 (by rfl) ⟨649745, by rfl⟩ : syracuseStep 866327 = 1299491) B1299491
theorem B866393 : Blo 574812 866393 := bstep (se 2 (by rfl) ⟨324897, by rfl⟩ : syracuseStep 866393 = 649795) B649795
theorem B2472029 : Blo 574812 2472029 := bstep (se 3 (by rfl) ⟨463505, by rfl⟩ : syracuseStep 2472029 = 927011) B927011
theorem B6666371 : Blo 574812 6666371 := bstep (se 1 (by rfl) ⟨4999778, by rfl⟩ : syracuseStep 6666371 = 9999557) B9999557
theorem B866507 : Blo 574812 866507 := bstep (se 1 (by rfl) ⟨649880, by rfl⟩ : syracuseStep 866507 = 1299761) B1299761
theorem B866519 : Blo 574812 866519 := bstep (se 1 (by rfl) ⟨649889, by rfl⟩ : syracuseStep 866519 = 1299779) B1299779
theorem B2078941 : Blo 574812 2078941 := bstep (se 3 (by rfl) ⟨389801, by rfl⟩ : syracuseStep 2078941 = 779603) B779603
theorem B1095923 : Blo 574812 1095923 := bstep (se 1 (by rfl) ⟨821942, by rfl⟩ : syracuseStep 1095923 = 1643885) B1643885
theorem B866585 : Blo 574812 866585 := bstep (se 2 (by rfl) ⟨324969, by rfl⟩ : syracuseStep 866585 = 649939) B649939
theorem B866699 : Blo 574812 866699 := bstep (se 1 (by rfl) ⟨650024, by rfl⟩ : syracuseStep 866699 = 1300049) B1300049
theorem B1554839 : Blo 574812 1554839 := bstep (se 1 (by rfl) ⟨1166129, by rfl⟩ : syracuseStep 1554839 = 2332259) B2332259
theorem B866711 : Blo 574812 866711 := bstep (se 1 (by rfl) ⟨650033, by rfl⟩ : syracuseStep 866711 = 1300067) B1300067
theorem B866777 : Blo 574812 866777 := bstep (se 2 (by rfl) ⟨325041, by rfl⟩ : syracuseStep 866777 = 650083) B650083
theorem B1456663 : Blo 574812 1456663 := bstep (se 1 (by rfl) ⟨1092497, by rfl⟩ : syracuseStep 1456663 = 2184995) B2184995
theorem B2406935 : Blo 574812 2406935 := bstep (se 1 (by rfl) ⟨1805201, by rfl⟩ : syracuseStep 2406935 = 3610403) B3610403
theorem B4373027 : Blo 574812 4373027 := bstep (se 1 (by rfl) ⟨3279770, by rfl⟩ : syracuseStep 4373027 = 6559541) B6559541
theorem B1948211 : Blo 574812 1948211 := bstep (se 1 (by rfl) ⟨1461158, by rfl⟩ : syracuseStep 1948211 = 2922317) B2922317
theorem B866891 : Blo 574812 866891 := bstep (se 1 (by rfl) ⟨650168, by rfl⟩ : syracuseStep 866891 = 1300337) B1300337
theorem B866903 : Blo 574812 866903 := bstep (se 1 (by rfl) ⟨650177, by rfl⟩ : syracuseStep 866903 = 1300355) B1300355
theorem B3291799 : Blo 574812 3291799 := bstep (se 1 (by rfl) ⟨2468849, by rfl⟩ : syracuseStep 3291799 = 4937699) B4937699
theorem B866969 : Blo 574812 866969 := bstep (se 2 (by rfl) ⟨325113, by rfl⟩ : syracuseStep 866969 = 650227) B650227
theorem B1096409 : Blo 574812 1096409 := bstep (se 2 (by rfl) ⟨411153, by rfl⟩ : syracuseStep 1096409 = 822307) B822307
theorem B867083 : Blo 574812 867083 := bstep (se 1 (by rfl) ⟨650312, by rfl⟩ : syracuseStep 867083 = 1300625) B1300625
theorem B867095 : Blo 574812 867095 := bstep (se 1 (by rfl) ⟨650321, by rfl⟩ : syracuseStep 867095 = 1300643) B1300643
theorem B1948481 : Blo 574812 1948481 := bstep (se 2 (by rfl) ⟨730680, by rfl⟩ : syracuseStep 1948481 = 1461361) B1461361
theorem B867161 : Blo 574812 867161 := bstep (se 2 (by rfl) ⟨325185, by rfl⟩ : syracuseStep 867161 = 650371) B650371
theorem B1850305 : Blo 574812 1850305 := bstep (se 2 (by rfl) ⟨693864, by rfl⟩ : syracuseStep 1850305 = 1387729) B1387729
theorem B1457099 : Blo 574812 1457099 := bstep (se 1 (by rfl) ⟨1092824, by rfl⟩ : syracuseStep 1457099 = 2185649) B2185649
theorem B867275 : Blo 574812 867275 := bstep (se 1 (by rfl) ⟨650456, by rfl⟩ : syracuseStep 867275 = 1300913) B1300913
theorem B867287 : Blo 574812 867287 := bstep (se 1 (by rfl) ⟨650465, by rfl⟩ : syracuseStep 867287 = 1300931) B1300931
theorem B3685337 : Blo 574812 3685337 := bstep (se 2 (by rfl) ⟨1382001, by rfl⟩ : syracuseStep 3685337 = 2764003) B2764003
theorem B1293335 : Blo 574812 1293335 := bstep (se 1 (by rfl) ⟨970001, by rfl⟩ : syracuseStep 1293335 = 1940003) B1940003
theorem B867353 : Blo 574812 867353 := bstep (se 2 (by rfl) ⟨325257, by rfl⟩ : syracuseStep 867353 = 650515) B650515
theorem B867467 : Blo 574812 867467 := bstep (se 1 (by rfl) ⟨650600, by rfl⟩ : syracuseStep 867467 = 1301201) B1301201
theorem B867479 : Blo 574812 867479 := bstep (se 1 (by rfl) ⟨650609, by rfl⟩ : syracuseStep 867479 = 1301219) B1301219
theorem B1293515 : Blo 574812 1293515 := bstep (se 1 (by rfl) ⟨970136, by rfl⟩ : syracuseStep 1293515 = 1940273) B1940273
theorem B867545 : Blo 574812 867545 := bstep (se 2 (by rfl) ⟨325329, by rfl⟩ : syracuseStep 867545 = 650659) B650659
theorem B1293569 : Blo 574812 1293569 := bstep (se 2 (by rfl) ⟨485088, by rfl⟩ : syracuseStep 1293569 = 970177) B970177
theorem B1457473 : Blo 574812 1457473 := bstep (se 2 (by rfl) ⟨546552, by rfl⟩ : syracuseStep 1457473 = 1093105) B1093105
theorem B867659 : Blo 574812 867659 := bstep (se 1 (by rfl) ⟨650744, by rfl⟩ : syracuseStep 867659 = 1301489) B1301489
theorem B867671 : Blo 574812 867671 := bstep (se 1 (by rfl) ⟨650753, by rfl⟩ : syracuseStep 867671 = 1301507) B1301507
theorem B1949021 : Blo 574812 1949021 := bstep (se 3 (by rfl) ⟨365441, by rfl⟩ : syracuseStep 1949021 = 730883) B730883
theorem B867737 : Blo 574812 867737 := bstep (se 2 (by rfl) ⟨325401, by rfl⟩ : syracuseStep 867737 = 650803) B650803
theorem B1293785 : Blo 574812 1293785 := bstep (se 2 (by rfl) ⟨485169, by rfl⟩ : syracuseStep 1293785 = 970339) B970339
theorem B867851 : Blo 574812 867851 := bstep (se 1 (by rfl) ⟨650888, by rfl⟩ : syracuseStep 867851 = 1301777) B1301777
theorem B867863 : Blo 574812 867863 := bstep (se 1 (by rfl) ⟨650897, by rfl⟩ : syracuseStep 867863 = 1301795) B1301795
theorem B1293875 : Blo 574812 1293875 := bstep (se 1 (by rfl) ⟨970406, by rfl⟩ : syracuseStep 1293875 = 1940813) B1940813
theorem B1293911 : Blo 574812 1293911 := bstep (se 1 (by rfl) ⟨970433, by rfl⟩ : syracuseStep 1293911 = 1940867) B1940867
theorem B867929 : Blo 574812 867929 := bstep (se 2 (by rfl) ⟨325473, by rfl⟩ : syracuseStep 867929 = 650947) B650947
theorem B868043 : Blo 574812 868043 := bstep (se 1 (by rfl) ⟨651032, by rfl⟩ : syracuseStep 868043 = 1302065) B1302065
theorem B868055 : Blo 574812 868055 := bstep (se 1 (by rfl) ⟨651041, by rfl⟩ : syracuseStep 868055 = 1302083) B1302083
theorem B11058929 : Blo 574812 11058929 := bstep (se 2 (by rfl) ⟨4147098, by rfl⟩ : syracuseStep 11058929 = 8294197) B8294197
theorem B1294091 : Blo 574812 1294091 := bstep (se 1 (by rfl) ⟨970568, by rfl⟩ : syracuseStep 1294091 = 1941137) B1941137
theorem B868121 : Blo 574812 868121 := bstep (se 2 (by rfl) ⟨325545, by rfl⟩ : syracuseStep 868121 = 651091) B651091
theorem B1294145 : Blo 574812 1294145 := bstep (se 2 (by rfl) ⟨485304, by rfl⟩ : syracuseStep 1294145 = 970609) B970609
theorem B2080657 : Blo 574812 2080657 := bstep (se 2 (by rfl) ⟨780246, by rfl⟩ : syracuseStep 2080657 = 1560493) B1560493
theorem B1458071 : Blo 574812 1458071 := bstep (se 1 (by rfl) ⟨1093553, by rfl⟩ : syracuseStep 1458071 = 2187107) B2187107
theorem B1228787 : Blo 574812 1228787 := bstep (se 1 (by rfl) ⟨921590, by rfl⟩ : syracuseStep 1228787 = 1843181) B1843181
theorem B1294361 : Blo 574812 1294361 := bstep (se 2 (by rfl) ⟨485385, by rfl⟩ : syracuseStep 1294361 = 970771) B970771
theorem B1228889 : Blo 574812 1228889 := bstep (se 2 (by rfl) ⟨460833, by rfl⟩ : syracuseStep 1228889 = 921667) B921667
theorem B1294451 : Blo 574812 1294451 := bstep (se 1 (by rfl) ⟨970838, by rfl⟩ : syracuseStep 1294451 = 1941677) B1941677
theorem B1097867 : Blo 574812 1097867 := bstep (se 1 (by rfl) ⟨823400, by rfl⟩ : syracuseStep 1097867 = 1646801) B1646801
theorem B1294487 : Blo 574812 1294487 := bstep (se 1 (by rfl) ⟨970865, by rfl⟩ : syracuseStep 1294487 = 1941731) B1941731
theorem B2080961 : Blo 574812 2080961 := bstep (se 2 (by rfl) ⟨780360, by rfl⟩ : syracuseStep 2080961 = 1560721) B1560721
theorem B2965805 : Blo 574812 2965805 := bstep (se 3 (by rfl) ⟨556088, by rfl⟩ : syracuseStep 2965805 = 1112177) B1112177
theorem B1098049 : Blo 574812 1098049 := bstep (se 2 (by rfl) ⟨411768, by rfl⟩ : syracuseStep 1098049 = 823537) B823537
theorem B1294667 : Blo 574812 1294667 := bstep (se 1 (by rfl) ⟨971000, by rfl⟩ : syracuseStep 1294667 = 1942001) B1942001
theorem B1294721 : Blo 574812 1294721 := bstep (se 2 (by rfl) ⟨485520, by rfl⟩ : syracuseStep 1294721 = 971041) B971041
theorem B1229249 : Blo 574812 1229249 := bstep (se 2 (by rfl) ⟨460968, by rfl⟩ : syracuseStep 1229249 = 921937) B921937
theorem B1950155 : Blo 574812 1950155 := bstep (se 1 (by rfl) ⟨1462616, by rfl⟩ : syracuseStep 1950155 = 2925233) B2925233
theorem B1294937 : Blo 574812 1294937 := bstep (se 2 (by rfl) ⟨485601, by rfl⟩ : syracuseStep 1294937 = 971203) B971203
theorem B1851997 : Blo 574812 1851997 := bstep (se 3 (by rfl) ⟨347249, by rfl⟩ : syracuseStep 1851997 = 694499) B694499
theorem B1295027 : Blo 574812 1295027 := bstep (se 1 (by rfl) ⟨971270, by rfl⟩ : syracuseStep 1295027 = 1942541) B1942541
theorem B1458881 : Blo 574812 1458881 := bstep (se 2 (by rfl) ⟨547080, by rfl⟩ : syracuseStep 1458881 = 1094161) B1094161
theorem B1295063 : Blo 574812 1295063 := bstep (se 1 (by rfl) ⟨971297, by rfl⟩ : syracuseStep 1295063 = 1942595) B1942595
theorem B1950425 : Blo 574812 1950425 := bstep (se 2 (by rfl) ⟨731409, by rfl⟩ : syracuseStep 1950425 = 1462819) B1462819
theorem B12468977 : Blo 574812 12468977 := bstep (se 2 (by rfl) ⟨4675866, by rfl⟩ : syracuseStep 12468977 = 9351733) B9351733
theorem B1098497 : Blo 574812 1098497 := bstep (se 2 (by rfl) ⟨411936, by rfl⟩ : syracuseStep 1098497 = 823873) B823873
theorem B1295243 : Blo 574812 1295243 := bstep (se 1 (by rfl) ⟨971432, by rfl⟩ : syracuseStep 1295243 = 1942865) B1942865
theorem B1295297 : Blo 574812 1295297 := bstep (se 2 (by rfl) ⟨485736, by rfl⟩ : syracuseStep 1295297 = 971473) B971473
theorem B1098839 : Blo 574812 1098839 := bstep (se 1 (by rfl) ⟨824129, by rfl⟩ : syracuseStep 1098839 = 1648259) B1648259
theorem B1229975 : Blo 574812 1229975 := bstep (se 1 (by rfl) ⟨922481, by rfl⟩ : syracuseStep 1229975 = 1844963) B1844963
theorem B1295513 : Blo 574812 1295513 := bstep (se 2 (by rfl) ⟨485817, by rfl⟩ : syracuseStep 1295513 = 971635) B971635
theorem B2671795 : Blo 574812 2671795 := bstep (se 1 (by rfl) ⟨2003846, by rfl⟩ : syracuseStep 2671795 = 4007693) B4007693
theorem B2344115 : Blo 574812 2344115 := bstep (se 1 (by rfl) ⟨1758086, by rfl⟩ : syracuseStep 2344115 = 3516173) B3516173
theorem B1459417 : Blo 574812 1459417 := bstep (se 2 (by rfl) ⟨547281, by rfl⟩ : syracuseStep 1459417 = 1094563) B1094563
theorem B1557725 : Blo 574812 1557725 := bstep (se 3 (by rfl) ⟨292073, by rfl⟩ : syracuseStep 1557725 = 584147) B584147
theorem B1295603 : Blo 574812 1295603 := bstep (se 1 (by rfl) ⟨971702, by rfl⟩ : syracuseStep 1295603 = 1943405) B1943405
theorem B1295639 : Blo 574812 1295639 := bstep (se 1 (by rfl) ⟨971729, by rfl⟩ : syracuseStep 1295639 = 1943459) B1943459
theorem B574827 : Blo 574812 574827 := bstep (se 1 (by rfl) ⟨431120, by rfl⟩ : syracuseStep 574827 = 862241) B862241
theorem B574839 : Blo 574812 574839 := bstep (se 1 (by rfl) ⟨431129, by rfl⟩ : syracuseStep 574839 = 862259) B862259
theorem B2770307 : Blo 574812 2770307 := bstep (se 1 (by rfl) ⟨2077730, by rfl⟩ : syracuseStep 2770307 = 4155461) B4155461
theorem B574859 : Blo 574812 574859 := bstep (se 1 (by rfl) ⟨431144, by rfl⟩ : syracuseStep 574859 = 862289) B862289
theorem B574871 : Blo 574812 574871 := bstep (se 1 (by rfl) ⟨431153, by rfl⟩ : syracuseStep 574871 = 862307) B862307
theorem B1951127 : Blo 574812 1951127 := bstep (se 1 (by rfl) ⟨1463345, by rfl⟩ : syracuseStep 1951127 = 2926691) B2926691
theorem B574891 : Blo 574812 574891 := bstep (se 1 (by rfl) ⟨431168, by rfl⟩ : syracuseStep 574891 = 862337) B862337
theorem B574903 : Blo 574812 574903 := bstep (se 1 (by rfl) ⟨431177, by rfl⟩ : syracuseStep 574903 = 862355) B862355
theorem B574923 : Blo 574812 574923 := bstep (se 1 (by rfl) ⟨431192, by rfl⟩ : syracuseStep 574923 = 862385) B862385
theorem B1295819 : Blo 574812 1295819 := bstep (se 1 (by rfl) ⟨971864, by rfl⟩ : syracuseStep 1295819 = 1943729) B1943729
theorem B574935 : Blo 574812 574935 := bstep (se 1 (by rfl) ⟨431201, by rfl⟩ : syracuseStep 574935 = 862403) B862403
theorem B574955 : Blo 574812 574955 := bstep (se 1 (by rfl) ⟨431216, by rfl⟩ : syracuseStep 574955 = 862433) B862433
theorem B574967 : Blo 574812 574967 := bstep (se 1 (by rfl) ⟨431225, by rfl⟩ : syracuseStep 574967 = 862451) B862451
theorem B1295873 : Blo 574812 1295873 := bstep (se 2 (by rfl) ⟨485952, by rfl⟩ : syracuseStep 1295873 = 971905) B971905
theorem B574987 : Blo 574812 574987 := bstep (se 1 (by rfl) ⟨431240, by rfl⟩ : syracuseStep 574987 = 862481) B862481
theorem B574999 : Blo 574812 574999 := bstep (se 1 (by rfl) ⟨431249, by rfl⟩ : syracuseStep 574999 = 862499) B862499
theorem B575019 : Blo 574812 575019 := bstep (se 1 (by rfl) ⟨431264, by rfl⟩ : syracuseStep 575019 = 862529) B862529
theorem B575031 : Blo 574812 575031 := bstep (se 1 (by rfl) ⟨431273, by rfl⟩ : syracuseStep 575031 = 862547) B862547
theorem B3688001 : Blo 574812 3688001 := bstep (se 2 (by rfl) ⟨1383000, by rfl⟩ : syracuseStep 3688001 = 2766001) B2766001
theorem B575051 : Blo 574812 575051 := bstep (se 1 (by rfl) ⟨431288, by rfl⟩ : syracuseStep 575051 = 862577) B862577
theorem B575063 : Blo 574812 575063 := bstep (se 1 (by rfl) ⟨431297, by rfl⟩ : syracuseStep 575063 = 862595) B862595
theorem B575083 : Blo 574812 575083 := bstep (se 1 (by rfl) ⟨431312, by rfl⟩ : syracuseStep 575083 = 862625) B862625
theorem B575095 : Blo 574812 575095 := bstep (se 1 (by rfl) ⟨431321, by rfl⟩ : syracuseStep 575095 = 862643) B862643
theorem B575115 : Blo 574812 575115 := bstep (se 1 (by rfl) ⟨431336, by rfl⟩ : syracuseStep 575115 = 862673) B862673
theorem B575127 : Blo 574812 575127 := bstep (se 1 (by rfl) ⟨431345, by rfl⟩ : syracuseStep 575127 = 862691) B862691
theorem B575147 : Blo 574812 575147 := bstep (se 1 (by rfl) ⟨431360, by rfl⟩ : syracuseStep 575147 = 862721) B862721
theorem B575159 : Blo 574812 575159 := bstep (se 1 (by rfl) ⟨431369, by rfl⟩ : syracuseStep 575159 = 862739) B862739
theorem B575179 : Blo 574812 575179 := bstep (se 1 (by rfl) ⟨431384, by rfl⟩ : syracuseStep 575179 = 862769) B862769
theorem B4933325 : Blo 574812 4933325 := bstep (se 3 (by rfl) ⟨924998, by rfl⟩ : syracuseStep 4933325 = 1849997) B1849997
theorem B575191 : Blo 574812 575191 := bstep (se 1 (by rfl) ⟨431393, by rfl⟩ : syracuseStep 575191 = 862787) B862787
theorem B1296089 : Blo 574812 1296089 := bstep (se 2 (by rfl) ⟨486033, by rfl⟩ : syracuseStep 1296089 = 972067) B972067
theorem B575211 : Blo 574812 575211 := bstep (se 1 (by rfl) ⟨431408, by rfl⟩ : syracuseStep 575211 = 862817) B862817
theorem B575223 : Blo 574812 575223 := bstep (se 1 (by rfl) ⟨431417, by rfl⟩ : syracuseStep 575223 = 862835) B862835
theorem B575243 : Blo 574812 575243 := bstep (se 1 (by rfl) ⟨431432, by rfl⟩ : syracuseStep 575243 = 862865) B862865
theorem B575255 : Blo 574812 575255 := bstep (se 1 (by rfl) ⟨431441, by rfl⟩ : syracuseStep 575255 = 862883) B862883
theorem B575275 : Blo 574812 575275 := bstep (se 1 (by rfl) ⟨431456, by rfl⟩ : syracuseStep 575275 = 862913) B862913
theorem B1296179 : Blo 574812 1296179 := bstep (se 1 (by rfl) ⟨972134, by rfl⟩ : syracuseStep 1296179 = 1944269) B1944269
theorem B575287 : Blo 574812 575287 := bstep (se 1 (by rfl) ⟨431465, by rfl⟩ : syracuseStep 575287 = 862931) B862931
theorem B575307 : Blo 574812 575307 := bstep (se 1 (by rfl) ⟨431480, by rfl⟩ : syracuseStep 575307 = 862961) B862961
theorem B575319 : Blo 574812 575319 := bstep (se 1 (by rfl) ⟨431489, by rfl⟩ : syracuseStep 575319 = 862979) B862979
theorem B1296215 : Blo 574812 1296215 := bstep (se 1 (by rfl) ⟨972161, by rfl⟩ : syracuseStep 1296215 = 1944323) B1944323
theorem B39929699 : Blo 574812 39929699 := bstep (se 1 (by rfl) ⟨29947274, by rfl⟩ : syracuseStep 39929699 = 59894549) B59894549
theorem B575339 : Blo 574812 575339 := bstep (se 1 (by rfl) ⟨431504, by rfl⟩ : syracuseStep 575339 = 863009) B863009
theorem B575351 : Blo 574812 575351 := bstep (se 1 (by rfl) ⟨431513, by rfl⟩ : syracuseStep 575351 = 863027) B863027
theorem B575371 : Blo 574812 575371 := bstep (se 1 (by rfl) ⟨431528, by rfl⟩ : syracuseStep 575371 = 863057) B863057
theorem B575383 : Blo 574812 575383 := bstep (se 1 (by rfl) ⟨431537, by rfl⟩ : syracuseStep 575383 = 863075) B863075
theorem B575403 : Blo 574812 575403 := bstep (se 1 (by rfl) ⟨431552, by rfl⟩ : syracuseStep 575403 = 863105) B863105
theorem B1951667 : Blo 574812 1951667 := bstep (se 1 (by rfl) ⟨1463750, by rfl⟩ : syracuseStep 1951667 = 2927501) B2927501
theorem B575415 : Blo 574812 575415 := bstep (se 1 (by rfl) ⟨431561, by rfl⟩ : syracuseStep 575415 = 863123) B863123
theorem B575435 : Blo 574812 575435 := bstep (se 1 (by rfl) ⟨431576, by rfl⟩ : syracuseStep 575435 = 863153) B863153
theorem B575447 : Blo 574812 575447 := bstep (se 1 (by rfl) ⟨431585, by rfl⟩ : syracuseStep 575447 = 863171) B863171
theorem B575467 : Blo 574812 575467 := bstep (se 1 (by rfl) ⟨431600, by rfl⟩ : syracuseStep 575467 = 863201) B863201
theorem B575479 : Blo 574812 575479 := bstep (se 1 (by rfl) ⟨431609, by rfl⟩ : syracuseStep 575479 = 863219) B863219
theorem B575499 : Blo 574812 575499 := bstep (se 1 (by rfl) ⟨431624, by rfl⟩ : syracuseStep 575499 = 863249) B863249
theorem B1296395 : Blo 574812 1296395 := bstep (se 1 (by rfl) ⟨972296, by rfl⟩ : syracuseStep 1296395 = 1944593) B1944593
theorem B575511 : Blo 574812 575511 := bstep (se 1 (by rfl) ⟨431633, by rfl⟩ : syracuseStep 575511 = 863267) B863267
theorem B1230871 : Blo 574812 1230871 := bstep (se 1 (by rfl) ⟨923153, by rfl⟩ : syracuseStep 1230871 = 1846307) B1846307
theorem B575531 : Blo 574812 575531 := bstep (se 1 (by rfl) ⟨431648, by rfl⟩ : syracuseStep 575531 = 863297) B863297
theorem B575543 : Blo 574812 575543 := bstep (se 1 (by rfl) ⟨431657, by rfl⟩ : syracuseStep 575543 = 863315) B863315
theorem B1296449 : Blo 574812 1296449 := bstep (se 2 (by rfl) ⟨486168, by rfl⟩ : syracuseStep 1296449 = 972337) B972337
theorem B575563 : Blo 574812 575563 := bstep (se 1 (by rfl) ⟨431672, by rfl⟩ : syracuseStep 575563 = 863345) B863345
theorem B575575 : Blo 574812 575575 := bstep (se 1 (by rfl) ⟨431681, by rfl⟩ : syracuseStep 575575 = 863363) B863363
theorem B575595 : Blo 574812 575595 := bstep (se 1 (by rfl) ⟨431696, by rfl⟩ : syracuseStep 575595 = 863393) B863393
theorem B575607 : Blo 574812 575607 := bstep (se 1 (by rfl) ⟨431705, by rfl⟩ : syracuseStep 575607 = 863411) B863411
theorem B575627 : Blo 574812 575627 := bstep (se 1 (by rfl) ⟨431720, by rfl⟩ : syracuseStep 575627 = 863441) B863441
theorem B575639 : Blo 574812 575639 := bstep (se 1 (by rfl) ⟨431729, by rfl⟩ : syracuseStep 575639 = 863459) B863459
theorem B575659 : Blo 574812 575659 := bstep (se 1 (by rfl) ⟨431744, by rfl⟩ : syracuseStep 575659 = 863489) B863489
theorem B575671 : Blo 574812 575671 := bstep (se 1 (by rfl) ⟨431753, by rfl⟩ : syracuseStep 575671 = 863507) B863507
theorem B1951937 : Blo 574812 1951937 := bstep (se 2 (by rfl) ⟨731976, by rfl⟩ : syracuseStep 1951937 = 1463953) B1463953
theorem B575691 : Blo 574812 575691 := bstep (se 1 (by rfl) ⟨431768, by rfl⟩ : syracuseStep 575691 = 863537) B863537
theorem B575703 : Blo 574812 575703 := bstep (se 1 (by rfl) ⟨431777, by rfl⟩ : syracuseStep 575703 = 863555) B863555
theorem B575723 : Blo 574812 575723 := bstep (se 1 (by rfl) ⟨431792, by rfl⟩ : syracuseStep 575723 = 863585) B863585
theorem B575735 : Blo 574812 575735 := bstep (se 1 (by rfl) ⟨431801, by rfl⟩ : syracuseStep 575735 = 863603) B863603
theorem B575755 : Blo 574812 575755 := bstep (se 1 (by rfl) ⟨431816, by rfl⟩ : syracuseStep 575755 = 863633) B863633
theorem B575767 : Blo 574812 575767 := bstep (se 1 (by rfl) ⟨431825, by rfl⟩ : syracuseStep 575767 = 863651) B863651
theorem B1296665 : Blo 574812 1296665 := bstep (se 2 (by rfl) ⟨486249, by rfl⟩ : syracuseStep 1296665 = 972499) B972499
theorem B575787 : Blo 574812 575787 := bstep (se 1 (by rfl) ⟨431840, by rfl⟩ : syracuseStep 575787 = 863681) B863681
theorem B1460531 : Blo 574812 1460531 := bstep (se 1 (by rfl) ⟨1095398, by rfl⟩ : syracuseStep 1460531 = 2190797) B2190797
theorem B575799 : Blo 574812 575799 := bstep (se 1 (by rfl) ⟨431849, by rfl⟩ : syracuseStep 575799 = 863699) B863699
theorem B575819 : Blo 574812 575819 := bstep (se 1 (by rfl) ⟨431864, by rfl⟩ : syracuseStep 575819 = 863729) B863729
theorem B575831 : Blo 574812 575831 := bstep (se 1 (by rfl) ⟨431873, by rfl⟩ : syracuseStep 575831 = 863747) B863747
theorem B575851 : Blo 574812 575851 := bstep (se 1 (by rfl) ⟨431888, by rfl⟩ : syracuseStep 575851 = 863777) B863777
theorem B1296755 : Blo 574812 1296755 := bstep (se 1 (by rfl) ⟨972566, by rfl⟩ : syracuseStep 1296755 = 1945133) B1945133
theorem B575863 : Blo 574812 575863 := bstep (se 1 (by rfl) ⟨431897, by rfl⟩ : syracuseStep 575863 = 863795) B863795
theorem B575883 : Blo 574812 575883 := bstep (se 1 (by rfl) ⟨431912, by rfl⟩ : syracuseStep 575883 = 863825) B863825
theorem B575895 : Blo 574812 575895 := bstep (se 1 (by rfl) ⟨431921, by rfl⟩ : syracuseStep 575895 = 863843) B863843
theorem B1296791 : Blo 574812 1296791 := bstep (se 1 (by rfl) ⟨972593, by rfl⟩ : syracuseStep 1296791 = 1945187) B1945187
theorem B575915 : Blo 574812 575915 := bstep (se 1 (by rfl) ⟨431936, by rfl⟩ : syracuseStep 575915 = 863873) B863873
theorem B575927 : Blo 574812 575927 := bstep (se 1 (by rfl) ⟨431945, by rfl⟩ : syracuseStep 575927 = 863891) B863891
theorem B575947 : Blo 574812 575947 := bstep (se 1 (by rfl) ⟨431960, by rfl⟩ : syracuseStep 575947 = 863921) B863921
theorem B575959 : Blo 574812 575959 := bstep (se 1 (by rfl) ⟨431969, by rfl⟩ : syracuseStep 575959 = 863939) B863939
theorem B575979 : Blo 574812 575979 := bstep (se 1 (by rfl) ⟨431984, by rfl⟩ : syracuseStep 575979 = 863969) B863969
theorem B575991 : Blo 574812 575991 := bstep (se 1 (by rfl) ⟨431993, by rfl⟩ : syracuseStep 575991 = 863987) B863987
theorem B576011 : Blo 574812 576011 := bstep (se 1 (by rfl) ⟨432008, by rfl⟩ : syracuseStep 576011 = 864017) B864017
theorem B576023 : Blo 574812 576023 := bstep (se 1 (by rfl) ⟨432017, by rfl⟩ : syracuseStep 576023 = 864035) B864035
theorem B576043 : Blo 574812 576043 := bstep (se 1 (by rfl) ⟨432032, by rfl⟩ : syracuseStep 576043 = 864065) B864065
theorem B576055 : Blo 574812 576055 := bstep (se 1 (by rfl) ⟨432041, by rfl⟩ : syracuseStep 576055 = 864083) B864083
theorem B576075 : Blo 574812 576075 := bstep (se 1 (by rfl) ⟨432056, by rfl⟩ : syracuseStep 576075 = 864113) B864113
theorem B1296971 : Blo 574812 1296971 := bstep (se 1 (by rfl) ⟨972728, by rfl⟩ : syracuseStep 1296971 = 1945457) B1945457
theorem B576087 : Blo 574812 576087 := bstep (se 1 (by rfl) ⟨432065, by rfl⟩ : syracuseStep 576087 = 864131) B864131
theorem B1460825 : Blo 574812 1460825 := bstep (se 2 (by rfl) ⟨547809, by rfl⟩ : syracuseStep 1460825 = 1095619) B1095619
theorem B576107 : Blo 574812 576107 := bstep (se 1 (by rfl) ⟨432080, by rfl⟩ : syracuseStep 576107 = 864161) B864161
theorem B576119 : Blo 574812 576119 := bstep (se 1 (by rfl) ⟨432089, by rfl⟩ : syracuseStep 576119 = 864179) B864179
theorem B1297025 : Blo 574812 1297025 := bstep (se 2 (by rfl) ⟨486384, by rfl⟩ : syracuseStep 1297025 = 972769) B972769
theorem B576139 : Blo 574812 576139 := bstep (se 1 (by rfl) ⟨432104, by rfl⟩ : syracuseStep 576139 = 864209) B864209
theorem B576151 : Blo 574812 576151 := bstep (se 1 (by rfl) ⟨432113, by rfl⟩ : syracuseStep 576151 = 864227) B864227
theorem B576171 : Blo 574812 576171 := bstep (se 1 (by rfl) ⟨432128, by rfl⟩ : syracuseStep 576171 = 864257) B864257
theorem B576183 : Blo 574812 576183 := bstep (se 1 (by rfl) ⟨432137, by rfl⟩ : syracuseStep 576183 = 864275) B864275
theorem B576203 : Blo 574812 576203 := bstep (se 1 (by rfl) ⟨432152, by rfl⟩ : syracuseStep 576203 = 864305) B864305
theorem B576215 : Blo 574812 576215 := bstep (se 1 (by rfl) ⟨432161, by rfl⟩ : syracuseStep 576215 = 864323) B864323
theorem B1952477 : Blo 574812 1952477 := bstep (se 3 (by rfl) ⟨366089, by rfl⟩ : syracuseStep 1952477 = 732179) B732179
theorem B576235 : Blo 574812 576235 := bstep (se 1 (by rfl) ⟨432176, by rfl⟩ : syracuseStep 576235 = 864353) B864353
theorem B19942129 : Blo 574812 19942129 := bstep (se 2 (by rfl) ⟨7478298, by rfl⟩ : syracuseStep 19942129 = 14956597) B14956597
theorem B576247 : Blo 574812 576247 := bstep (se 1 (by rfl) ⟨432185, by rfl⟩ : syracuseStep 576247 = 864371) B864371
theorem B576267 : Blo 574812 576267 := bstep (se 1 (by rfl) ⟨432200, by rfl⟩ : syracuseStep 576267 = 864401) B864401
theorem B576279 : Blo 574812 576279 := bstep (se 1 (by rfl) ⟨432209, by rfl⟩ : syracuseStep 576279 = 864419) B864419
theorem B576299 : Blo 574812 576299 := bstep (se 1 (by rfl) ⟨432224, by rfl⟩ : syracuseStep 576299 = 864449) B864449
theorem B576311 : Blo 574812 576311 := bstep (se 1 (by rfl) ⟨432233, by rfl⟩ : syracuseStep 576311 = 864467) B864467
theorem B576331 : Blo 574812 576331 := bstep (se 1 (by rfl) ⟨432248, by rfl⟩ : syracuseStep 576331 = 864497) B864497
theorem B1231691 : Blo 574812 1231691 := bstep (se 1 (by rfl) ⟨923768, by rfl⟩ : syracuseStep 1231691 = 1847537) B1847537
theorem B576343 : Blo 574812 576343 := bstep (se 1 (by rfl) ⟨432257, by rfl⟩ : syracuseStep 576343 = 864515) B864515
theorem B1297241 : Blo 574812 1297241 := bstep (se 2 (by rfl) ⟨486465, by rfl⟩ : syracuseStep 1297241 = 972931) B972931
theorem B576363 : Blo 574812 576363 := bstep (se 1 (by rfl) ⟨432272, by rfl⟩ : syracuseStep 576363 = 864545) B864545
theorem B576375 : Blo 574812 576375 := bstep (se 1 (by rfl) ⟨432281, by rfl⟩ : syracuseStep 576375 = 864563) B864563
theorem B576395 : Blo 574812 576395 := bstep (se 1 (by rfl) ⟨432296, by rfl⟩ : syracuseStep 576395 = 864593) B864593
theorem B576407 : Blo 574812 576407 := bstep (se 1 (by rfl) ⟨432305, by rfl⟩ : syracuseStep 576407 = 864611) B864611
theorem B576427 : Blo 574812 576427 := bstep (se 1 (by rfl) ⟨432320, by rfl⟩ : syracuseStep 576427 = 864641) B864641
theorem B1297331 : Blo 574812 1297331 := bstep (se 1 (by rfl) ⟨972998, by rfl⟩ : syracuseStep 1297331 = 1945997) B1945997
theorem B576439 : Blo 574812 576439 := bstep (se 1 (by rfl) ⟨432329, by rfl⟩ : syracuseStep 576439 = 864659) B864659
theorem B576459 : Blo 574812 576459 := bstep (se 1 (by rfl) ⟨432344, by rfl⟩ : syracuseStep 576459 = 864689) B864689
theorem B576471 : Blo 574812 576471 := bstep (se 1 (by rfl) ⟨432353, by rfl⟩ : syracuseStep 576471 = 864707) B864707
theorem B1297367 : Blo 574812 1297367 := bstep (se 1 (by rfl) ⟨973025, by rfl⟩ : syracuseStep 1297367 = 1946051) B1946051
theorem B576491 : Blo 574812 576491 := bstep (se 1 (by rfl) ⟨432368, by rfl⟩ : syracuseStep 576491 = 864737) B864737
theorem B576503 : Blo 574812 576503 := bstep (se 1 (by rfl) ⟨432377, by rfl⟩ : syracuseStep 576503 = 864755) B864755
theorem B576523 : Blo 574812 576523 := bstep (se 1 (by rfl) ⟨432392, by rfl⟩ : syracuseStep 576523 = 864785) B864785
theorem B576535 : Blo 574812 576535 := bstep (se 1 (by rfl) ⟨432401, by rfl⟩ : syracuseStep 576535 = 864803) B864803
theorem B576555 : Blo 574812 576555 := bstep (se 1 (by rfl) ⟨432416, by rfl⟩ : syracuseStep 576555 = 864833) B864833
theorem B576567 : Blo 574812 576567 := bstep (se 1 (by rfl) ⟨432425, by rfl⟩ : syracuseStep 576567 = 864851) B864851
theorem B576587 : Blo 574812 576587 := bstep (se 1 (by rfl) ⟨432440, by rfl⟩ : syracuseStep 576587 = 864881) B864881
theorem B576599 : Blo 574812 576599 := bstep (se 1 (by rfl) ⟨432449, by rfl⟩ : syracuseStep 576599 = 864899) B864899
theorem B576619 : Blo 574812 576619 := bstep (se 1 (by rfl) ⟨432464, by rfl⟩ : syracuseStep 576619 = 864929) B864929
theorem B576631 : Blo 574812 576631 := bstep (se 1 (by rfl) ⟨432473, by rfl⟩ : syracuseStep 576631 = 864947) B864947
theorem B576651 : Blo 574812 576651 := bstep (se 1 (by rfl) ⟨432488, by rfl⟩ : syracuseStep 576651 = 864977) B864977
theorem B1297547 : Blo 574812 1297547 := bstep (se 1 (by rfl) ⟨973160, by rfl⟩ : syracuseStep 1297547 = 1946321) B1946321
theorem B576663 : Blo 574812 576663 := bstep (se 1 (by rfl) ⟨432497, by rfl⟩ : syracuseStep 576663 = 864995) B864995
theorem B576683 : Blo 574812 576683 := bstep (se 1 (by rfl) ⟨432512, by rfl⟩ : syracuseStep 576683 = 865025) B865025
theorem B576695 : Blo 574812 576695 := bstep (se 1 (by rfl) ⟨432521, by rfl⟩ : syracuseStep 576695 = 865043) B865043
theorem B1297601 : Blo 574812 1297601 := bstep (se 2 (by rfl) ⟨486600, by rfl⟩ : syracuseStep 1297601 = 973201) B973201
theorem B576715 : Blo 574812 576715 := bstep (se 1 (by rfl) ⟨432536, by rfl⟩ : syracuseStep 576715 = 865073) B865073
theorem B576727 : Blo 574812 576727 := bstep (se 1 (by rfl) ⟨432545, by rfl⟩ : syracuseStep 576727 = 865091) B865091
theorem B576747 : Blo 574812 576747 := bstep (se 1 (by rfl) ⟨432560, by rfl⟩ : syracuseStep 576747 = 865121) B865121
theorem B576759 : Blo 574812 576759 := bstep (se 1 (by rfl) ⟨432569, by rfl⟩ : syracuseStep 576759 = 865139) B865139
theorem B576779 : Blo 574812 576779 := bstep (se 1 (by rfl) ⟨432584, by rfl⟩ : syracuseStep 576779 = 865169) B865169
theorem B576791 : Blo 574812 576791 := bstep (se 1 (by rfl) ⟨432593, by rfl⟩ : syracuseStep 576791 = 865187) B865187
theorem B576811 : Blo 574812 576811 := bstep (se 1 (by rfl) ⟨432608, by rfl⟩ : syracuseStep 576811 = 865217) B865217
theorem B576823 : Blo 574812 576823 := bstep (se 1 (by rfl) ⟨432617, by rfl⟩ : syracuseStep 576823 = 865235) B865235
theorem B576843 : Blo 574812 576843 := bstep (se 1 (by rfl) ⟨432632, by rfl⟩ : syracuseStep 576843 = 865265) B865265
theorem B576855 : Blo 574812 576855 := bstep (se 1 (by rfl) ⟨432641, by rfl⟩ : syracuseStep 576855 = 865283) B865283
theorem B576875 : Blo 574812 576875 := bstep (se 1 (by rfl) ⟨432656, by rfl⟩ : syracuseStep 576875 = 865313) B865313
theorem B576887 : Blo 574812 576887 := bstep (se 1 (by rfl) ⟨432665, by rfl⟩ : syracuseStep 576887 = 865331) B865331
theorem B970123 : Blo 574812 970123 := bstep (se 1 (by rfl) ⟨727592, by rfl⟩ : syracuseStep 970123 = 1455185) B1455185
theorem B576907 : Blo 574812 576907 := bstep (se 1 (by rfl) ⟨432680, by rfl⟩ : syracuseStep 576907 = 865361) B865361
theorem B576919 : Blo 574812 576919 := bstep (se 1 (by rfl) ⟨432689, by rfl⟩ : syracuseStep 576919 = 865379) B865379
theorem B1297817 : Blo 574812 1297817 := bstep (se 2 (by rfl) ⟨486681, by rfl⟩ : syracuseStep 1297817 = 973363) B973363
theorem B576939 : Blo 574812 576939 := bstep (se 1 (by rfl) ⟨432704, by rfl⟩ : syracuseStep 576939 = 865409) B865409
theorem B4148657 : Blo 574812 4148657 := bstep (se 2 (by rfl) ⟨1555746, by rfl⟩ : syracuseStep 4148657 = 3111493) B3111493
theorem B576951 : Blo 574812 576951 := bstep (se 1 (by rfl) ⟨432713, by rfl⟩ : syracuseStep 576951 = 865427) B865427
theorem B576971 : Blo 574812 576971 := bstep (se 1 (by rfl) ⟨432728, by rfl⟩ : syracuseStep 576971 = 865457) B865457
theorem B576983 : Blo 574812 576983 := bstep (se 1 (by rfl) ⟨432737, by rfl⟩ : syracuseStep 576983 = 865475) B865475
theorem B577003 : Blo 574812 577003 := bstep (se 1 (by rfl) ⟨432752, by rfl⟩ : syracuseStep 577003 = 865505) B865505
theorem B1297907 : Blo 574812 1297907 := bstep (se 1 (by rfl) ⟨973430, by rfl⟩ : syracuseStep 1297907 = 1946861) B1946861
theorem B577015 : Blo 574812 577015 := bstep (se 1 (by rfl) ⟨432761, by rfl⟩ : syracuseStep 577015 = 865523) B865523
theorem B577035 : Blo 574812 577035 := bstep (se 1 (by rfl) ⟨432776, by rfl⟩ : syracuseStep 577035 = 865553) B865553
theorem B1297943 : Blo 574812 1297943 := bstep (se 1 (by rfl) ⟨973457, by rfl⟩ : syracuseStep 1297943 = 1946915) B1946915
theorem B577047 : Blo 574812 577047 := bstep (se 1 (by rfl) ⟨432785, by rfl⟩ : syracuseStep 577047 = 865571) B865571
theorem B970265 : Blo 574812 970265 := bstep (se 2 (by rfl) ⟨363849, by rfl⟩ : syracuseStep 970265 = 727699) B727699
theorem B577067 : Blo 574812 577067 := bstep (se 1 (by rfl) ⟨432800, by rfl⟩ : syracuseStep 577067 = 865601) B865601
theorem B1232435 : Blo 574812 1232435 := bstep (se 1 (by rfl) ⟨924326, by rfl⟩ : syracuseStep 1232435 = 1848653) B1848653
theorem B577079 : Blo 574812 577079 := bstep (se 1 (by rfl) ⟨432809, by rfl⟩ : syracuseStep 577079 = 865619) B865619
theorem B577099 : Blo 574812 577099 := bstep (se 1 (by rfl) ⟨432824, by rfl⟩ : syracuseStep 577099 = 865649) B865649
theorem B5557835 : Blo 574812 5557835 := bstep (se 1 (by rfl) ⟨4168376, by rfl⟩ : syracuseStep 5557835 = 8336753) B8336753
theorem B577111 : Blo 574812 577111 := bstep (se 1 (by rfl) ⟨432833, by rfl⟩ : syracuseStep 577111 = 865667) B865667
theorem B577131 : Blo 574812 577131 := bstep (se 1 (by rfl) ⟨432848, by rfl⟩ : syracuseStep 577131 = 865697) B865697
theorem B577143 : Blo 574812 577143 := bstep (se 1 (by rfl) ⟨432857, by rfl⟩ : syracuseStep 577143 = 865715) B865715
theorem B577163 : Blo 574812 577163 := bstep (se 1 (by rfl) ⟨432872, by rfl⟩ : syracuseStep 577163 = 865745) B865745
theorem B577175 : Blo 574812 577175 := bstep (se 1 (by rfl) ⟨432881, by rfl⟩ : syracuseStep 577175 = 865763) B865763
theorem B970393 : Blo 574812 970393 := bstep (se 2 (by rfl) ⟨363897, by rfl⟩ : syracuseStep 970393 = 727795) B727795
theorem B577195 : Blo 574812 577195 := bstep (se 1 (by rfl) ⟨432896, by rfl⟩ : syracuseStep 577195 = 865793) B865793
theorem B577207 : Blo 574812 577207 := bstep (se 1 (by rfl) ⟨432905, by rfl⟩ : syracuseStep 577207 = 865811) B865811
theorem B1298123 : Blo 574812 1298123 := bstep (se 1 (by rfl) ⟨973592, by rfl⟩ : syracuseStep 1298123 = 1947185) B1947185
theorem B577227 : Blo 574812 577227 := bstep (se 1 (by rfl) ⟨432920, by rfl⟩ : syracuseStep 577227 = 865841) B865841
theorem B577239 : Blo 574812 577239 := bstep (se 1 (by rfl) ⟨432929, by rfl⟩ : syracuseStep 577239 = 865859) B865859
theorem B577259 : Blo 574812 577259 := bstep (se 1 (by rfl) ⟨432944, by rfl⟩ : syracuseStep 577259 = 865889) B865889
theorem B577271 : Blo 574812 577271 := bstep (se 1 (by rfl) ⟨432953, by rfl⟩ : syracuseStep 577271 = 865907) B865907
theorem B1298177 : Blo 574812 1298177 := bstep (se 2 (by rfl) ⟨486816, by rfl⟩ : syracuseStep 1298177 = 973633) B973633
theorem B4378373 : Blo 574812 4378373 := bstep (se 4 (by rfl) ⟨410472, by rfl⟩ : syracuseStep 4378373 = 820945) B820945
theorem B577291 : Blo 574812 577291 := bstep (se 1 (by rfl) ⟨432968, by rfl⟩ : syracuseStep 577291 = 865937) B865937
theorem B577303 : Blo 574812 577303 := bstep (se 1 (by rfl) ⟨432977, by rfl⟩ : syracuseStep 577303 = 865955) B865955
theorem B577323 : Blo 574812 577323 := bstep (se 1 (by rfl) ⟨432992, by rfl⟩ : syracuseStep 577323 = 865985) B865985
theorem B577335 : Blo 574812 577335 := bstep (se 1 (by rfl) ⟨433001, by rfl⟩ : syracuseStep 577335 = 866003) B866003
theorem B577355 : Blo 574812 577355 := bstep (se 1 (by rfl) ⟨433016, by rfl⟩ : syracuseStep 577355 = 866033) B866033
theorem B577367 : Blo 574812 577367 := bstep (se 1 (by rfl) ⟨433025, by rfl⟩ : syracuseStep 577367 = 866051) B866051
theorem B577387 : Blo 574812 577387 := bstep (se 1 (by rfl) ⟨433040, by rfl⟩ : syracuseStep 577387 = 866081) B866081
theorem B577399 : Blo 574812 577399 := bstep (se 1 (by rfl) ⟨433049, by rfl⟩ : syracuseStep 577399 = 866099) B866099
theorem B577419 : Blo 574812 577419 := bstep (se 1 (by rfl) ⟨433064, by rfl⟩ : syracuseStep 577419 = 866129) B866129
theorem B577431 : Blo 574812 577431 := bstep (se 1 (by rfl) ⟨433073, by rfl⟩ : syracuseStep 577431 = 866147) B866147
theorem B577451 : Blo 574812 577451 := bstep (se 1 (by rfl) ⟨433088, by rfl⟩ : syracuseStep 577451 = 866177) B866177
theorem B577463 : Blo 574812 577463 := bstep (se 1 (by rfl) ⟨433097, by rfl⟩ : syracuseStep 577463 = 866195) B866195
theorem B577483 : Blo 574812 577483 := bstep (se 1 (by rfl) ⟨433112, by rfl⟩ : syracuseStep 577483 = 866225) B866225
theorem B577495 : Blo 574812 577495 := bstep (se 1 (by rfl) ⟨433121, by rfl⟩ : syracuseStep 577495 = 866243) B866243
theorem B1298393 : Blo 574812 1298393 := bstep (se 2 (by rfl) ⟨486897, by rfl⟩ : syracuseStep 1298393 = 973795) B973795
theorem B577515 : Blo 574812 577515 := bstep (se 1 (by rfl) ⟨433136, by rfl⟩ : syracuseStep 577515 = 866273) B866273
theorem B577527 : Blo 574812 577527 := bstep (se 1 (by rfl) ⟨433145, by rfl⟩ : syracuseStep 577527 = 866291) B866291
theorem B577547 : Blo 574812 577547 := bstep (se 1 (by rfl) ⟨433160, by rfl⟩ : syracuseStep 577547 = 866321) B866321
theorem B17813525 : Blo 574812 17813525 := bstep (se 6 (by rfl) ⟨417504, by rfl⟩ : syracuseStep 17813525 = 835009) B835009
theorem B577559 : Blo 574812 577559 := bstep (se 1 (by rfl) ⟨433169, by rfl⟩ : syracuseStep 577559 = 866339) B866339
theorem B577579 : Blo 574812 577579 := bstep (se 1 (by rfl) ⟨433184, by rfl⟩ : syracuseStep 577579 = 866369) B866369
theorem B2183219 : Blo 574812 2183219 := bstep (se 1 (by rfl) ⟨1637414, by rfl⟩ : syracuseStep 2183219 = 3274829) B3274829
theorem B1298483 : Blo 574812 1298483 := bstep (se 1 (by rfl) ⟨973862, by rfl⟩ : syracuseStep 1298483 = 1947725) B1947725
theorem B577591 : Blo 574812 577591 := bstep (se 1 (by rfl) ⟨433193, by rfl⟩ : syracuseStep 577591 = 866387) B866387
theorem B2183233 : Blo 574812 2183233 := bstep (se 2 (by rfl) ⟨818712, by rfl⟩ : syracuseStep 2183233 = 1637425) B1637425
theorem B577611 : Blo 574812 577611 := bstep (se 1 (by rfl) ⟨433208, by rfl⟩ : syracuseStep 577611 = 866417) B866417
theorem B1298519 : Blo 574812 1298519 := bstep (se 1 (by rfl) ⟨973889, by rfl⟩ : syracuseStep 1298519 = 1947779) B1947779
theorem B577623 : Blo 574812 577623 := bstep (se 1 (by rfl) ⟨433217, by rfl⟩ : syracuseStep 577623 = 866435) B866435
theorem B577643 : Blo 574812 577643 := bstep (se 1 (by rfl) ⟨433232, by rfl⟩ : syracuseStep 577643 = 866465) B866465
theorem B577655 : Blo 574812 577655 := bstep (se 1 (by rfl) ⟨433241, by rfl⟩ : syracuseStep 577655 = 866483) B866483
theorem B577675 : Blo 574812 577675 := bstep (se 1 (by rfl) ⟨433256, by rfl⟩ : syracuseStep 577675 = 866513) B866513
theorem B577687 : Blo 574812 577687 := bstep (se 1 (by rfl) ⟨433265, by rfl⟩ : syracuseStep 577687 = 866531) B866531
theorem B577707 : Blo 574812 577707 := bstep (se 1 (by rfl) ⟨433280, by rfl⟩ : syracuseStep 577707 = 866561) B866561
theorem B577719 : Blo 574812 577719 := bstep (se 1 (by rfl) ⟨433289, by rfl⟩ : syracuseStep 577719 = 866579) B866579
theorem B577739 : Blo 574812 577739 := bstep (se 1 (by rfl) ⟨433304, by rfl⟩ : syracuseStep 577739 = 866609) B866609
theorem B1462475 : Blo 574812 1462475 := bstep (se 1 (by rfl) ⟨1096856, by rfl⟩ : syracuseStep 1462475 = 2193713) B2193713
theorem B970967 : Blo 574812 970967 := bstep (se 1 (by rfl) ⟨728225, by rfl⟩ : syracuseStep 970967 = 1456451) B1456451
theorem B577751 : Blo 574812 577751 := bstep (se 1 (by rfl) ⟨433313, by rfl⟩ : syracuseStep 577751 = 866627) B866627
theorem B577771 : Blo 574812 577771 := bstep (se 1 (by rfl) ⟨433328, by rfl⟩ : syracuseStep 577771 = 866657) B866657
theorem B577783 : Blo 574812 577783 := bstep (se 1 (by rfl) ⟨433337, by rfl⟩ : syracuseStep 577783 = 866675) B866675
theorem B1298699 : Blo 574812 1298699 := bstep (se 1 (by rfl) ⟨974024, by rfl⟩ : syracuseStep 1298699 = 1948049) B1948049
theorem B577803 : Blo 574812 577803 := bstep (se 1 (by rfl) ⟨433352, by rfl⟩ : syracuseStep 577803 = 866705) B866705
theorem B577815 : Blo 574812 577815 := bstep (se 1 (by rfl) ⟨433361, by rfl⟩ : syracuseStep 577815 = 866723) B866723
theorem B577835 : Blo 574812 577835 := bstep (se 1 (by rfl) ⟨433376, by rfl⟩ : syracuseStep 577835 = 866753) B866753
theorem B577847 : Blo 574812 577847 := bstep (se 1 (by rfl) ⟨433385, by rfl⟩ : syracuseStep 577847 = 866771) B866771
theorem B1298753 : Blo 574812 1298753 := bstep (se 2 (by rfl) ⟨487032, by rfl⟩ : syracuseStep 1298753 = 974065) B974065
theorem B577867 : Blo 574812 577867 := bstep (se 1 (by rfl) ⟨433400, by rfl⟩ : syracuseStep 577867 = 866801) B866801
theorem B971095 : Blo 574812 971095 := bstep (se 1 (by rfl) ⟨728321, by rfl⟩ : syracuseStep 971095 = 1456643) B1456643
theorem B577879 : Blo 574812 577879 := bstep (se 1 (by rfl) ⟨433409, by rfl⟩ : syracuseStep 577879 = 866819) B866819
theorem B577899 : Blo 574812 577899 := bstep (se 1 (by rfl) ⟨433424, by rfl⟩ : syracuseStep 577899 = 866849) B866849
theorem B577911 : Blo 574812 577911 := bstep (se 1 (by rfl) ⟨433433, by rfl⟩ : syracuseStep 577911 = 866867) B866867
theorem B1233281 : Blo 574812 1233281 := bstep (se 2 (by rfl) ⟨462480, by rfl⟩ : syracuseStep 1233281 = 924961) B924961
theorem B577931 : Blo 574812 577931 := bstep (se 1 (by rfl) ⟨433448, by rfl⟩ : syracuseStep 577931 = 866897) B866897
theorem B577943 : Blo 574812 577943 := bstep (se 1 (by rfl) ⟨433457, by rfl⟩ : syracuseStep 577943 = 866915) B866915
theorem B577963 : Blo 574812 577963 := bstep (se 1 (by rfl) ⟨433472, by rfl⟩ : syracuseStep 577963 = 866945) B866945
theorem B577975 : Blo 574812 577975 := bstep (se 1 (by rfl) ⟨433481, by rfl⟩ : syracuseStep 577975 = 866963) B866963
theorem B577995 : Blo 574812 577995 := bstep (se 1 (by rfl) ⟨433496, by rfl⟩ : syracuseStep 577995 = 866993) B866993
theorem B578007 : Blo 574812 578007 := bstep (se 1 (by rfl) ⟨433505, by rfl⟩ : syracuseStep 578007 = 867011) B867011
theorem B578027 : Blo 574812 578027 := bstep (se 1 (by rfl) ⟨433520, by rfl⟩ : syracuseStep 578027 = 867041) B867041
theorem B578039 : Blo 574812 578039 := bstep (se 1 (by rfl) ⟨433529, by rfl⟩ : syracuseStep 578039 = 867059) B867059
theorem B578059 : Blo 574812 578059 := bstep (se 1 (by rfl) ⟨433544, by rfl⟩ : syracuseStep 578059 = 867089) B867089
theorem B578071 : Blo 574812 578071 := bstep (se 1 (by rfl) ⟨433553, by rfl⟩ : syracuseStep 578071 = 867107) B867107
theorem B1298969 : Blo 574812 1298969 := bstep (se 2 (by rfl) ⟨487113, by rfl⟩ : syracuseStep 1298969 = 974227) B974227
theorem B578091 : Blo 574812 578091 := bstep (se 1 (by rfl) ⟨433568, by rfl⟩ : syracuseStep 578091 = 867137) B867137
theorem B578103 : Blo 574812 578103 := bstep (se 1 (by rfl) ⟨433577, by rfl⟩ : syracuseStep 578103 = 867155) B867155
theorem B578123 : Blo 574812 578123 := bstep (se 1 (by rfl) ⟨433592, by rfl⟩ : syracuseStep 578123 = 867185) B867185
theorem B578135 : Blo 574812 578135 := bstep (se 1 (by rfl) ⟨433601, by rfl⟩ : syracuseStep 578135 = 867203) B867203
theorem B578155 : Blo 574812 578155 := bstep (se 1 (by rfl) ⟨433616, by rfl⟩ : syracuseStep 578155 = 867233) B867233
theorem B1299059 : Blo 574812 1299059 := bstep (se 1 (by rfl) ⟨974294, by rfl⟩ : syracuseStep 1299059 = 1948589) B1948589
theorem B578167 : Blo 574812 578167 := bstep (se 1 (by rfl) ⟨433625, by rfl⟩ : syracuseStep 578167 = 867251) B867251
theorem B578187 : Blo 574812 578187 := bstep (se 1 (by rfl) ⟨433640, by rfl⟩ : syracuseStep 578187 = 867281) B867281
theorem B2216593 : Blo 574812 2216593 := bstep (se 2 (by rfl) ⟨831222, by rfl⟩ : syracuseStep 2216593 = 1662445) B1662445
theorem B1299095 : Blo 574812 1299095 := bstep (se 1 (by rfl) ⟨974321, by rfl⟩ : syracuseStep 1299095 = 1948643) B1948643
theorem B578199 : Blo 574812 578199 := bstep (se 1 (by rfl) ⟨433649, by rfl⟩ : syracuseStep 578199 = 867299) B867299
theorem B578219 : Blo 574812 578219 := bstep (se 1 (by rfl) ⟨433664, by rfl⟩ : syracuseStep 578219 = 867329) B867329
theorem B578231 : Blo 574812 578231 := bstep (se 1 (by rfl) ⟨433673, by rfl⟩ : syracuseStep 578231 = 867347) B867347
theorem B578251 : Blo 574812 578251 := bstep (se 1 (by rfl) ⟨433688, by rfl⟩ : syracuseStep 578251 = 867377) B867377
theorem B5558989 : Blo 574812 5558989 := bstep (se 3 (by rfl) ⟨1042310, by rfl⟩ : syracuseStep 5558989 = 2084621) B2084621
theorem B1233623 : Blo 574812 1233623 := bstep (se 1 (by rfl) ⟨925217, by rfl⟩ : syracuseStep 1233623 = 1850435) B1850435
theorem B578263 : Blo 574812 578263 := bstep (se 1 (by rfl) ⟨433697, by rfl⟩ : syracuseStep 578263 = 867395) B867395
theorem B578283 : Blo 574812 578283 := bstep (se 1 (by rfl) ⟨433712, by rfl⟩ : syracuseStep 578283 = 867425) B867425
theorem B578295 : Blo 574812 578295 := bstep (se 1 (by rfl) ⟨433721, by rfl⟩ : syracuseStep 578295 = 867443) B867443
theorem B578315 : Blo 574812 578315 := bstep (se 1 (by rfl) ⟨433736, by rfl⟩ : syracuseStep 578315 = 867473) B867473
theorem B578327 : Blo 574812 578327 := bstep (se 1 (by rfl) ⟨433745, by rfl⟩ : syracuseStep 578327 = 867491) B867491
theorem B578347 : Blo 574812 578347 := bstep (se 1 (by rfl) ⟨433760, by rfl⟩ : syracuseStep 578347 = 867521) B867521
theorem B578359 : Blo 574812 578359 := bstep (se 1 (by rfl) ⟨433769, by rfl⟩ : syracuseStep 578359 = 867539) B867539
theorem B1299275 : Blo 574812 1299275 := bstep (se 1 (by rfl) ⟨974456, by rfl⟩ : syracuseStep 1299275 = 1948913) B1948913
theorem B578379 : Blo 574812 578379 := bstep (se 1 (by rfl) ⟨433784, by rfl⟩ : syracuseStep 578379 = 867569) B867569
theorem B578391 : Blo 574812 578391 := bstep (se 1 (by rfl) ⟨433793, by rfl⟩ : syracuseStep 578391 = 867587) B867587
theorem B578411 : Blo 574812 578411 := bstep (se 1 (by rfl) ⟨433808, by rfl⟩ : syracuseStep 578411 = 867617) B867617
theorem B578423 : Blo 574812 578423 := bstep (se 1 (by rfl) ⟨433817, by rfl⟩ : syracuseStep 578423 = 867635) B867635
theorem B1299329 : Blo 574812 1299329 := bstep (se 2 (by rfl) ⟨487248, by rfl⟩ : syracuseStep 1299329 = 974497) B974497
theorem B578443 : Blo 574812 578443 := bstep (se 1 (by rfl) ⟨433832, by rfl⟩ : syracuseStep 578443 = 867665) B867665
theorem B578455 : Blo 574812 578455 := bstep (se 1 (by rfl) ⟨433841, by rfl⟩ : syracuseStep 578455 = 867683) B867683
theorem B578475 : Blo 574812 578475 := bstep (se 1 (by rfl) ⟨433856, by rfl⟩ : syracuseStep 578475 = 867713) B867713
theorem B578487 : Blo 574812 578487 := bstep (se 1 (by rfl) ⟨433865, by rfl⟩ : syracuseStep 578487 = 867731) B867731
theorem B971723 : Blo 574812 971723 := bstep (se 1 (by rfl) ⟨728792, by rfl⟩ : syracuseStep 971723 = 1457585) B1457585
theorem B578507 : Blo 574812 578507 := bstep (se 1 (by rfl) ⟨433880, by rfl⟩ : syracuseStep 578507 = 867761) B867761
theorem B578519 : Blo 574812 578519 := bstep (se 1 (by rfl) ⟨433889, by rfl⟩ : syracuseStep 578519 = 867779) B867779
theorem B578539 : Blo 574812 578539 := bstep (se 1 (by rfl) ⟨433904, by rfl⟩ : syracuseStep 578539 = 867809) B867809
theorem B578551 : Blo 574812 578551 := bstep (se 1 (by rfl) ⟨433913, by rfl⟩ : syracuseStep 578551 = 867827) B867827
theorem B578571 : Blo 574812 578571 := bstep (se 1 (by rfl) ⟨433928, by rfl⟩ : syracuseStep 578571 = 867857) B867857
theorem B578583 : Blo 574812 578583 := bstep (se 1 (by rfl) ⟨433937, by rfl⟩ : syracuseStep 578583 = 867875) B867875
theorem B578603 : Blo 574812 578603 := bstep (se 1 (by rfl) ⟨433952, by rfl⟩ : syracuseStep 578603 = 867905) B867905
theorem B3691565 : Blo 574812 3691565 := bstep (se 3 (by rfl) ⟨692168, by rfl⟩ : syracuseStep 3691565 = 1384337) B1384337
theorem B578615 : Blo 574812 578615 := bstep (se 1 (by rfl) ⟨433961, by rfl⟩ : syracuseStep 578615 = 867923) B867923
theorem B971851 : Blo 574812 971851 := bstep (se 1 (by rfl) ⟨728888, by rfl⟩ : syracuseStep 971851 = 1457777) B1457777
theorem B578635 : Blo 574812 578635 := bstep (se 1 (by rfl) ⟨433976, by rfl⟩ : syracuseStep 578635 = 867953) B867953
theorem B578647 : Blo 574812 578647 := bstep (se 1 (by rfl) ⟨433985, by rfl⟩ : syracuseStep 578647 = 867971) B867971
theorem B1299545 : Blo 574812 1299545 := bstep (se 2 (by rfl) ⟨487329, by rfl⟩ : syracuseStep 1299545 = 974659) B974659
theorem B578667 : Blo 574812 578667 := bstep (se 1 (by rfl) ⟨434000, by rfl⟩ : syracuseStep 578667 = 868001) B868001
theorem B578679 : Blo 574812 578679 := bstep (se 1 (by rfl) ⟨434009, by rfl⟩ : syracuseStep 578679 = 868019) B868019
theorem B578699 : Blo 574812 578699 := bstep (se 1 (by rfl) ⟨434024, by rfl⟩ : syracuseStep 578699 = 868049) B868049
theorem B1463447 : Blo 574812 1463447 := bstep (se 1 (by rfl) ⟨1097585, by rfl⟩ : syracuseStep 1463447 = 2195171) B2195171
theorem B578711 : Blo 574812 578711 := bstep (se 1 (by rfl) ⟨434033, by rfl⟩ : syracuseStep 578711 = 868067) B868067
theorem B578731 : Blo 574812 578731 := bstep (se 1 (by rfl) ⟨434048, by rfl⟩ : syracuseStep 578731 = 868097) B868097
theorem B1299635 : Blo 574812 1299635 := bstep (se 1 (by rfl) ⟨974726, by rfl⟩ : syracuseStep 1299635 = 1949453) B1949453
theorem B578743 : Blo 574812 578743 := bstep (se 1 (by rfl) ⟨434057, by rfl⟩ : syracuseStep 578743 = 868115) B868115
theorem B578763 : Blo 574812 578763 := bstep (se 1 (by rfl) ⟨434072, by rfl⟩ : syracuseStep 578763 = 868145) B868145
theorem B1299671 : Blo 574812 1299671 := bstep (se 1 (by rfl) ⟨974753, by rfl⟩ : syracuseStep 1299671 = 1949507) B1949507
theorem B578775 : Blo 574812 578775 := bstep (se 1 (by rfl) ⟨434081, by rfl⟩ : syracuseStep 578775 = 868163) B868163
theorem B971993 : Blo 574812 971993 := bstep (se 2 (by rfl) ⟨364497, by rfl⟩ : syracuseStep 971993 = 728995) B728995
theorem B578795 : Blo 574812 578795 := bstep (se 1 (by rfl) ⟨434096, by rfl⟩ : syracuseStep 578795 = 868193) B868193
theorem B578807 : Blo 574812 578807 := bstep (se 1 (by rfl) ⟨434105, by rfl⟩ : syracuseStep 578807 = 868211) B868211
theorem B3691793 : Blo 574812 3691793 := bstep (se 2 (by rfl) ⟨1384422, by rfl⟩ : syracuseStep 3691793 = 2768845) B2768845
theorem B972121 : Blo 574812 972121 := bstep (se 2 (by rfl) ⟨364545, by rfl⟩ : syracuseStep 972121 = 729091) B729091
theorem B18666865 : Blo 574812 18666865 := bstep (se 2 (by rfl) ⟨7000074, by rfl⟩ : syracuseStep 18666865 = 14000149) B14000149
theorem B1299851 : Blo 574812 1299851 := bstep (se 1 (by rfl) ⟨974888, by rfl⟩ : syracuseStep 1299851 = 1949777) B1949777
theorem B1299905 : Blo 574812 1299905 := bstep (se 2 (by rfl) ⟨487464, by rfl⟩ : syracuseStep 1299905 = 974929) B974929
theorem B1300121 : Blo 574812 1300121 := bstep (se 2 (by rfl) ⟨487545, by rfl⟩ : syracuseStep 1300121 = 975091) B975091
theorem B1300211 : Blo 574812 1300211 := bstep (se 1 (by rfl) ⟨975158, by rfl⟩ : syracuseStep 1300211 = 1950317) B1950317
theorem B1300247 : Blo 574812 1300247 := bstep (se 1 (by rfl) ⟨975185, by rfl⟩ : syracuseStep 1300247 = 1950371) B1950371
theorem B1464115 : Blo 574812 1464115 := bstep (se 1 (by rfl) ⟨1098086, by rfl⟩ : syracuseStep 1464115 = 2196173) B2196173
theorem B972695 : Blo 574812 972695 := bstep (se 1 (by rfl) ⟨729521, by rfl⟩ : syracuseStep 972695 = 1459043) B1459043
theorem B1464257 : Blo 574812 1464257 := bstep (se 2 (by rfl) ⟨549096, by rfl⟩ : syracuseStep 1464257 = 1098193) B1098193
theorem B2185163 : Blo 574812 2185163 := bstep (se 1 (by rfl) ⟨1638872, by rfl⟩ : syracuseStep 2185163 = 3277745) B3277745
theorem B1300427 : Blo 574812 1300427 := bstep (se 1 (by rfl) ⟨975320, by rfl⟩ : syracuseStep 1300427 = 1950641) B1950641
theorem B2185177 : Blo 574812 2185177 := bstep (se 2 (by rfl) ⟨819441, by rfl⟩ : syracuseStep 2185177 = 1638883) B1638883
theorem B1300481 : Blo 574812 1300481 := bstep (se 2 (by rfl) ⟨487680, by rfl⟩ : syracuseStep 1300481 = 975361) B975361
theorem B1038347 : Blo 574812 1038347 := bstep (se 1 (by rfl) ⟨778760, by rfl⟩ : syracuseStep 1038347 = 1557521) B1557521
theorem B972823 : Blo 574812 972823 := bstep (se 1 (by rfl) ⟨729617, by rfl⟩ : syracuseStep 972823 = 1459235) B1459235
theorem B1497163 : Blo 574812 1497163 := bstep (se 1 (by rfl) ⟨1122872, by rfl⟩ : syracuseStep 1497163 = 2245745) B2245745
theorem B874585 : Blo 574812 874585 := bstep (se 2 (by rfl) ⟨327969, by rfl⟩ : syracuseStep 874585 = 655939) B655939
theorem B4380803 : Blo 574812 4380803 := bstep (se 1 (by rfl) ⟨3285602, by rfl⟩ : syracuseStep 4380803 = 6571205) B6571205
theorem B1300697 : Blo 574812 1300697 := bstep (se 2 (by rfl) ⟨487761, by rfl⟩ : syracuseStep 1300697 = 975523) B975523
theorem B2283821 : Blo 574812 2283821 := bstep (se 3 (by rfl) ⟨428216, by rfl⟩ : syracuseStep 2283821 = 856433) B856433
theorem B1300787 : Blo 574812 1300787 := bstep (se 1 (by rfl) ⟨975590, by rfl⟩ : syracuseStep 1300787 = 1951181) B1951181
theorem B1300823 : Blo 574812 1300823 := bstep (se 1 (by rfl) ⟨975617, by rfl⟩ : syracuseStep 1300823 = 1951235) B1951235
theorem B1301003 : Blo 574812 1301003 := bstep (se 1 (by rfl) ⟨975752, by rfl⟩ : syracuseStep 1301003 = 1951505) B1951505
theorem B1301057 : Blo 574812 1301057 := bstep (se 2 (by rfl) ⟨487896, by rfl⟩ : syracuseStep 1301057 = 975793) B975793
theorem B973451 : Blo 574812 973451 := bstep (se 1 (by rfl) ⟨730088, by rfl⟩ : syracuseStep 973451 = 1460177) B1460177
theorem B973579 : Blo 574812 973579 := bstep (se 1 (by rfl) ⟨730184, by rfl⟩ : syracuseStep 973579 = 1460369) B1460369
theorem B1301273 : Blo 574812 1301273 := bstep (se 2 (by rfl) ⟨487977, by rfl⟩ : syracuseStep 1301273 = 975955) B975955
theorem B1301363 : Blo 574812 1301363 := bstep (se 1 (by rfl) ⟨976022, by rfl⟩ : syracuseStep 1301363 = 1952045) B1952045
theorem B2186135 : Blo 574812 2186135 := bstep (se 1 (by rfl) ⟨1639601, by rfl⟩ : syracuseStep 2186135 = 3279203) B3279203
theorem B1301399 : Blo 574812 1301399 := bstep (se 1 (by rfl) ⟨976049, by rfl⟩ : syracuseStep 1301399 = 1952099) B1952099
theorem B973721 : Blo 574812 973721 := bstep (se 2 (by rfl) ⟨365145, by rfl⟩ : syracuseStep 973721 = 730291) B730291
theorem B1170379 : Blo 574812 1170379 := bstep (se 1 (by rfl) ⟨877784, by rfl⟩ : syracuseStep 1170379 = 1755569) B1755569
theorem B973849 : Blo 574812 973849 := bstep (se 2 (by rfl) ⟨365193, by rfl⟩ : syracuseStep 973849 = 730387) B730387
theorem B5135425 : Blo 574812 5135425 := bstep (se 2 (by rfl) ⟨1925784, by rfl⟩ : syracuseStep 5135425 = 3851569) B3851569
theorem B1301579 : Blo 574812 1301579 := bstep (se 1 (by rfl) ⟨976184, by rfl⟩ : syracuseStep 1301579 = 1952369) B1952369
theorem B1301633 : Blo 574812 1301633 := bstep (se 2 (by rfl) ⟨488112, by rfl⟩ : syracuseStep 1301633 = 976225) B976225
theorem B1301849 : Blo 574812 1301849 := bstep (se 2 (by rfl) ⟨488193, by rfl⟩ : syracuseStep 1301849 = 976387) B976387
theorem B1301939 : Blo 574812 1301939 := bstep (se 1 (by rfl) ⟨976454, by rfl⟩ : syracuseStep 1301939 = 1952909) B1952909
theorem B1301975 : Blo 574812 1301975 := bstep (se 1 (by rfl) ⟨976481, by rfl⟩ : syracuseStep 1301975 = 1952963) B1952963
theorem B646699 : Blo 574812 646699 := bstep (se 1 (by rfl) ⟨485024, by rfl⟩ : syracuseStep 646699 = 970049) B970049
theorem B4939339 : Blo 574812 4939339 := bstep (se 1 (by rfl) ⟨3704504, by rfl⟩ : syracuseStep 4939339 = 7409009) B7409009
theorem B613975 : Blo 574812 613975 := bstep (se 1 (by rfl) ⟨460481, by rfl⟩ : syracuseStep 613975 = 920963) B920963
theorem B974423 : Blo 574812 974423 := bstep (se 1 (by rfl) ⟨730817, by rfl⟩ : syracuseStep 974423 = 1461635) B1461635
theorem B1302155 : Blo 574812 1302155 := bstep (se 1 (by rfl) ⟨976616, by rfl⟩ : syracuseStep 1302155 = 1953233) B1953233
theorem B646807 : Blo 574812 646807 := bstep (se 1 (by rfl) ⟨485105, by rfl⟩ : syracuseStep 646807 = 970211) B970211
theorem B1302209 : Blo 574812 1302209 := bstep (se 2 (by rfl) ⟨488328, by rfl⟩ : syracuseStep 1302209 = 976657) B976657
theorem B974551 : Blo 574812 974551 := bstep (se 1 (by rfl) ⟨730913, by rfl⟩ : syracuseStep 974551 = 1461827) B1461827
theorem B8314609 : Blo 574812 8314609 := bstep (se 2 (by rfl) ⟨3117978, by rfl⟩ : syracuseStep 8314609 = 6235957) B6235957
theorem B646987 : Blo 574812 646987 := bstep (se 1 (by rfl) ⟨485240, by rfl⟩ : syracuseStep 646987 = 970481) B970481
theorem B1564505 : Blo 574812 1564505 := bstep (se 2 (by rfl) ⟨586689, by rfl⟩ : syracuseStep 1564505 = 1173379) B1173379
theorem B4939613 : Blo 574812 4939613 := bstep (se 3 (by rfl) ⟨926177, by rfl⟩ : syracuseStep 4939613 = 1852355) B1852355
theorem B1171351 : Blo 574812 1171351 := bstep (se 1 (by rfl) ⟨878513, by rfl⟩ : syracuseStep 1171351 = 1757027) B1757027
theorem B647095 : Blo 574812 647095 := bstep (se 1 (by rfl) ⟨485321, by rfl⟩ : syracuseStep 647095 = 970643) B970643
theorem B647275 : Blo 574812 647275 := bstep (se 1 (by rfl) ⟨485456, by rfl⟩ : syracuseStep 647275 = 970913) B970913
theorem B2187395 : Blo 574812 2187395 := bstep (se 1 (by rfl) ⟨1640546, by rfl⟩ : syracuseStep 2187395 = 3281093) B3281093
theorem B7397527 : Blo 574812 7397527 := bstep (se 1 (by rfl) ⟨5548145, by rfl⟩ : syracuseStep 7397527 = 11096291) B11096291
theorem B647383 : Blo 574812 647383 := bstep (se 1 (by rfl) ⟨485537, by rfl⟩ : syracuseStep 647383 = 971075) B971075
theorem B778457 : Blo 574812 778457 := bstep (se 2 (by rfl) ⟨291921, by rfl⟩ : syracuseStep 778457 = 583843) B583843
theorem B975179 : Blo 574812 975179 := bstep (se 1 (by rfl) ⟨731384, by rfl⟩ : syracuseStep 975179 = 1462769) B1462769
theorem B647563 : Blo 574812 647563 := bstep (se 1 (by rfl) ⟨485672, by rfl⟩ : syracuseStep 647563 = 971345) B971345
theorem B614795 : Blo 574812 614795 := bstep (se 1 (by rfl) ⟨461096, by rfl⟩ : syracuseStep 614795 = 922193) B922193
theorem B975307 : Blo 574812 975307 := bstep (se 1 (by rfl) ⟨731480, by rfl⟩ : syracuseStep 975307 = 1462961) B1462961
theorem B647671 : Blo 574812 647671 := bstep (se 1 (by rfl) ⟨485753, by rfl⟩ : syracuseStep 647671 = 971507) B971507
theorem B975449 : Blo 574812 975449 := bstep (se 2 (by rfl) ⟨365793, by rfl⟩ : syracuseStep 975449 = 731587) B731587
theorem B647851 : Blo 574812 647851 := bstep (se 1 (by rfl) ⟨485888, by rfl⟩ : syracuseStep 647851 = 971777) B971777
theorem B975577 : Blo 574812 975577 := bstep (se 2 (by rfl) ⟨365841, by rfl⟩ : syracuseStep 975577 = 731683) B731683
theorem B647959 : Blo 574812 647959 := bstep (se 1 (by rfl) ⟨485969, by rfl⟩ : syracuseStep 647959 = 971939) B971939
theorem B4940675 : Blo 574812 4940675 := bstep (se 1 (by rfl) ⟨3705506, by rfl⟩ : syracuseStep 4940675 = 7411013) B7411013
theorem B1041331 : Blo 574812 1041331 := bstep (se 1 (by rfl) ⟨780998, by rfl⟩ : syracuseStep 1041331 = 1561997) B1561997
theorem B648139 : Blo 574812 648139 := bstep (se 1 (by rfl) ⟨486104, by rfl⟩ : syracuseStep 648139 = 972209) B972209
theorem B648247 : Blo 574812 648247 := bstep (se 1 (by rfl) ⟨486185, by rfl⟩ : syracuseStep 648247 = 972371) B972371
theorem B648427 : Blo 574812 648427 := bstep (se 1 (by rfl) ⟨486320, by rfl⟩ : syracuseStep 648427 = 972641) B972641
theorem B32531717 : Blo 574812 32531717 := bstep (se 4 (by rfl) ⟨3049848, by rfl⟩ : syracuseStep 32531717 = 6099697) B6099697
theorem B976151 : Blo 574812 976151 := bstep (se 1 (by rfl) ⟨732113, by rfl⟩ : syracuseStep 976151 = 1464227) B1464227
theorem B648535 : Blo 574812 648535 := bstep (se 1 (by rfl) ⟨486401, by rfl⟩ : syracuseStep 648535 = 972803) B972803
theorem B976279 : Blo 574812 976279 := bstep (se 1 (by rfl) ⟨732209, by rfl⟩ : syracuseStep 976279 = 1464419) B1464419
theorem B615863 : Blo 574812 615863 := bstep (se 1 (by rfl) ⟨461897, by rfl⟩ : syracuseStep 615863 = 923795) B923795
theorem B4384205 : Blo 574812 4384205 := bstep (se 3 (by rfl) ⟨822038, by rfl⟩ : syracuseStep 4384205 = 1644077) B1644077
theorem B1664477 : Blo 574812 1664477 := bstep (se 3 (by rfl) ⟨312089, by rfl⟩ : syracuseStep 1664477 = 624179) B624179
theorem B648715 : Blo 574812 648715 := bstep (se 1 (by rfl) ⟨486536, by rfl⟩ : syracuseStep 648715 = 973073) B973073
theorem B648823 : Blo 574812 648823 := bstep (se 1 (by rfl) ⟨486617, by rfl⟩ : syracuseStep 648823 = 973235) B973235
theorem B649003 : Blo 574812 649003 := bstep (se 1 (by rfl) ⟨486752, by rfl⟩ : syracuseStep 649003 = 973505) B973505
theorem B649111 : Blo 574812 649111 := bstep (se 1 (by rfl) ⟨486833, by rfl⟩ : syracuseStep 649111 = 973667) B973667
theorem B4384691 : Blo 574812 4384691 := bstep (se 1 (by rfl) ⟨3288518, by rfl⟩ : syracuseStep 4384691 = 6577037) B6577037
theorem B649291 : Blo 574812 649291 := bstep (se 1 (by rfl) ⟨486968, by rfl⟩ : syracuseStep 649291 = 973937) B973937
theorem B2779267 : Blo 574812 2779267 := bstep (se 1 (by rfl) ⟨2084450, by rfl⟩ : syracuseStep 2779267 = 4168901) B4168901
theorem B649399 : Blo 574812 649399 := bstep (se 1 (by rfl) ⟨487049, by rfl⟩ : syracuseStep 649399 = 974099) B974099
theorem B5335301 : Blo 574812 5335301 := bstep (se 4 (by rfl) ⟨500184, by rfl⟩ : syracuseStep 5335301 = 1000369) B1000369
theorem B649579 : Blo 574812 649579 := bstep (se 1 (by rfl) ⟨487184, by rfl⟩ : syracuseStep 649579 = 974369) B974369
theorem B4155779 : Blo 574812 4155779 := bstep (se 1 (by rfl) ⟨3116834, by rfl⟩ : syracuseStep 4155779 = 6233669) B6233669
theorem B649687 : Blo 574812 649687 := bstep (se 1 (by rfl) ⟨487265, by rfl⟩ : syracuseStep 649687 = 974531) B974531
theorem B2779609 : Blo 574812 2779609 := bstep (se 2 (by rfl) ⟨1042353, by rfl⟩ : syracuseStep 2779609 = 2084707) B2084707
theorem B616939 : Blo 574812 616939 := bstep (se 1 (by rfl) ⟨462704, by rfl⟩ : syracuseStep 616939 = 925409) B925409
theorem B1042931 : Blo 574812 1042931 := bstep (se 1 (by rfl) ⟨782198, by rfl⟩ : syracuseStep 1042931 = 1564397) B1564397
theorem B10119755 : Blo 574812 10119755 := bstep (se 1 (by rfl) ⟨7589816, by rfl⟩ : syracuseStep 10119755 = 15179633) B15179633
theorem B3992165 : Blo 574812 3992165 := bstep (se 4 (by rfl) ⟨374265, by rfl⟩ : syracuseStep 3992165 = 748531) B748531
theorem B649867 : Blo 574812 649867 := bstep (se 1 (by rfl) ⟨487400, by rfl⟩ : syracuseStep 649867 = 974801) B974801
theorem B649975 : Blo 574812 649975 := bstep (se 1 (by rfl) ⟨487481, by rfl⟩ : syracuseStep 649975 = 974963) B974963
theorem B650155 : Blo 574812 650155 := bstep (se 1 (by rfl) ⟨487616, by rfl⟩ : syracuseStep 650155 = 975233) B975233
theorem B650263 : Blo 574812 650263 := bstep (se 1 (by rfl) ⟨487697, by rfl⟩ : syracuseStep 650263 = 975395) B975395
theorem B2190509 : Blo 574812 2190509 := bstep (se 3 (by rfl) ⟨410720, by rfl⟩ : syracuseStep 2190509 = 821441) B821441
theorem B650443 : Blo 574812 650443 := bstep (se 1 (by rfl) ⟨487832, by rfl⟩ : syracuseStep 650443 = 975665) B975665
theorem B650551 : Blo 574812 650551 := bstep (se 1 (by rfl) ⟨487913, by rfl⟩ : syracuseStep 650551 = 975827) B975827
theorem B4386149 : Blo 574812 4386149 := bstep (se 4 (by rfl) ⟨411201, by rfl⟩ : syracuseStep 4386149 = 822403) B822403
theorem B617879 : Blo 574812 617879 := bstep (se 1 (by rfl) ⟨463409, by rfl⟩ : syracuseStep 617879 = 926819) B926819
theorem B650731 : Blo 574812 650731 := bstep (se 1 (by rfl) ⟨488048, by rfl⟩ : syracuseStep 650731 = 976097) B976097
theorem B650839 : Blo 574812 650839 := bstep (se 1 (by rfl) ⟨488129, by rfl⟩ : syracuseStep 650839 = 976259) B976259
theorem B651019 : Blo 574812 651019 := bstep (se 1 (by rfl) ⟨488264, by rfl⟩ : syracuseStep 651019 = 976529) B976529
theorem B2780993 : Blo 574812 2780993 := bstep (se 2 (by rfl) ⟨1042872, by rfl⟩ : syracuseStep 2780993 = 2085745) B2085745
theorem B4386635 : Blo 574812 4386635 := bstep (se 1 (by rfl) ⟨3289976, by rfl⟩ : syracuseStep 4386635 = 6579953) B6579953
theorem B651127 : Blo 574812 651127 := bstep (se 1 (by rfl) ⟨488345, by rfl⟩ : syracuseStep 651127 = 976691) B976691
theorem B9858995 : Blo 574812 9858995 := bstep (se 1 (by rfl) ⟨7394246, by rfl⟩ : syracuseStep 9858995 = 14788493) B14788493
theorem B2191283 : Blo 574812 2191283 := bstep (se 1 (by rfl) ⟨1643462, by rfl⟩ : syracuseStep 2191283 = 3286925) B3286925
theorem B2912273 : Blo 574812 2912273 := bstep (se 2 (by rfl) ⟨1092102, by rfl⟩ : syracuseStep 2912273 = 2184205) B2184205
theorem B2912435 : Blo 574812 2912435 := bstep (se 1 (by rfl) ⟨2184326, by rfl⟩ : syracuseStep 2912435 = 4368653) B4368653
theorem B585911 : Blo 574812 585911 := bstep (se 1 (by rfl) ⟨439433, by rfl⟩ : syracuseStep 585911 = 878867) B878867
theorem B6222257 : Blo 574812 6222257 := bstep (se 2 (by rfl) ⟨2333346, by rfl⟩ : syracuseStep 6222257 = 4666693) B4666693
theorem B17953589 : Blo 574812 17953589 := bstep (se 5 (by rfl) ⟨841574, by rfl⟩ : syracuseStep 17953589 = 1683149) B1683149
theorem B3273803 : Blo 574812 3273803 := bstep (se 1 (by rfl) ⟨2455352, by rfl⟩ : syracuseStep 3273803 = 4910705) B4910705
theorem B14775371 : Blo 574812 14775371 := bstep (se 1 (by rfl) ⟨11081528, by rfl⟩ : syracuseStep 14775371 = 22163057) B22163057
theorem B2192771 : Blo 574812 2192771 := bstep (se 1 (by rfl) ⟨1644578, by rfl⟩ : syracuseStep 2192771 = 3289157) B3289157
theorem B5273267 : Blo 574812 5273267 := bstep (se 1 (by rfl) ⟨3954950, by rfl⟩ : syracuseStep 5273267 = 7909901) B7909901
theorem B2193227 : Blo 574812 2193227 := bstep (se 1 (by rfl) ⟨1644920, by rfl⟩ : syracuseStep 2193227 = 3289841) B3289841
theorem B2193425 : Blo 574812 2193425 := bstep (se 2 (by rfl) ⟨822534, by rfl⟩ : syracuseStep 2193425 = 1645069) B1645069
theorem B5928977 : Blo 574812 5928977 := bstep (se 2 (by rfl) ⟨2223366, by rfl⟩ : syracuseStep 5928977 = 4446733) B4446733
theorem B2914379 : Blo 574812 2914379 := bstep (se 1 (by rfl) ⟨2185784, by rfl⟩ : syracuseStep 2914379 = 4371569) B4371569
theorem B4913369 : Blo 574812 4913369 := bstep (se 2 (by rfl) ⟨1842513, by rfl⟩ : syracuseStep 4913369 = 3685027) B3685027
theorem B3701123 : Blo 574812 3701123 := bstep (se 1 (by rfl) ⟨2775842, by rfl⟩ : syracuseStep 3701123 = 5551685) B5551685
theorem B5569175 : Blo 574812 5569175 := bstep (se 1 (by rfl) ⟨4176881, by rfl⟩ : syracuseStep 5569175 = 8353763) B8353763
theorem B1669835 : Blo 574812 1669835 := bstep (se 1 (by rfl) ⟨1252376, by rfl⟩ : syracuseStep 1669835 = 2504753) B2504753
theorem B2194199 : Blo 574812 2194199 := bstep (se 1 (by rfl) ⟨1645649, by rfl⟩ : syracuseStep 2194199 = 3291299) B3291299
theorem B2194397 : Blo 574812 2194397 := bstep (se 3 (by rfl) ⟨411449, by rfl⟩ : syracuseStep 2194397 = 822899) B822899
theorem B8879179 : Blo 574812 8879179 := bstep (se 1 (by rfl) ⟨6659384, by rfl⟩ : syracuseStep 8879179 = 13318769) B13318769
theorem B2456669 : Blo 574812 2456669 := bstep (se 3 (by rfl) ⟨460625, by rfl⟩ : syracuseStep 2456669 = 921251) B921251
theorem B1637597 : Blo 574812 1637597 := bstep (se 3 (by rfl) ⟨307049, by rfl⟩ : syracuseStep 1637597 = 614099) B614099
theorem B4685273 : Blo 574812 4685273 := bstep (se 2 (by rfl) ⟨1756977, by rfl⟩ : syracuseStep 4685273 = 3513955) B3513955
theorem B2916161 : Blo 574812 2916161 := bstep (se 2 (by rfl) ⟨1093560, by rfl⟩ : syracuseStep 2916161 = 2187121) B2187121
theorem B4685633 : Blo 574812 4685633 := bstep (se 2 (by rfl) ⟨1757112, by rfl⟩ : syracuseStep 4685633 = 3514225) B3514225
theorem B3112921 : Blo 574812 3112921 := bstep (se 2 (by rfl) ⟨1167345, by rfl⟩ : syracuseStep 3112921 = 2334691) B2334691
theorem B9863369 : Blo 574812 9863369 := bstep (se 2 (by rfl) ⟨3698763, by rfl⟩ : syracuseStep 9863369 = 7397527) B7397527
theorem B2195657 : Blo 574812 2195657 := bstep (se 2 (by rfl) ⟨823371, by rfl⟩ : syracuseStep 2195657 = 1646743) B1646743
theorem B3277037 : Blo 574812 3277037 := bstep (se 3 (by rfl) ⟨614444, by rfl⟩ : syracuseStep 3277037 = 1228889) B1228889
theorem B819499 : Blo 574812 819499 := bstep (se 1 (by rfl) ⟨614624, by rfl⟩ : syracuseStep 819499 = 1229249) B1229249
theorem B1311275 : Blo 574812 1311275 := bstep (se 1 (by rfl) ⟨983456, by rfl⟩ : syracuseStep 1311275 = 1966913) B1966913
theorem B819983 : Blo 574812 819983 := bstep (se 1 (by rfl) ⟨614987, by rfl⟩ : syracuseStep 819983 = 1229975) B1229975
theorem B1639453 : Blo 574812 1639453 := bstep (se 3 (by rfl) ⟨307397, by rfl⟩ : syracuseStep 1639453 = 614795) B614795
theorem B2458667 : Blo 574812 2458667 := bstep (se 1 (by rfl) ⟨1844000, by rfl⟩ : syracuseStep 2458667 = 3688001) B3688001
theorem B1639511 : Blo 574812 1639511 := bstep (se 1 (by rfl) ⟨1229633, by rfl⟩ : syracuseStep 1639511 = 2459267) B2459267
theorem B2918429 : Blo 574812 2918429 := bstep (se 3 (by rfl) ⟨547205, by rfl⟩ : syracuseStep 2918429 = 1094411) B1094411
theorem B985223 : Blo 574812 985223 := bstep (se 1 (by rfl) ⟨738917, by rfl⟩ : syracuseStep 985223 = 1477835) B1477835
theorem B3705223 : Blo 574812 3705223 := bstep (se 1 (by rfl) ⟨2778917, by rfl⟩ : syracuseStep 3705223 = 5557835) B5557835
theorem B2918915 : Blo 574812 2918915 := bstep (se 1 (by rfl) ⟨2189186, by rfl⟩ : syracuseStep 2918915 = 4378373) B4378373
theorem B1641161 : Blo 574812 1641161 := bstep (se 2 (by rfl) ⟨615435, by rfl⟩ : syracuseStep 1641161 = 1230871) B1230871
theorem B3705689 : Blo 574812 3705689 := bstep (se 2 (by rfl) ⟨1389633, by rfl⟩ : syracuseStep 3705689 = 2779267) B2779267
theorem B822187 : Blo 574812 822187 := bstep (se 1 (by rfl) ⟨616640, by rfl⟩ : syracuseStep 822187 = 1233281) B1233281
theorem B1870877 : Blo 574812 1870877 := bstep (se 3 (by rfl) ⟨350789, by rfl⟩ : syracuseStep 1870877 = 701579) B701579
theorem B822415 : Blo 574812 822415 := bstep (se 1 (by rfl) ⟨616811, by rfl⟩ : syracuseStep 822415 = 1233623) B1233623
theorem B1313939 : Blo 574812 1313939 := bstep (se 1 (by rfl) ⟨985454, by rfl⟩ : syracuseStep 1313939 = 1970909) B1970909
theorem B3706145 : Blo 574812 3706145 := bstep (se 2 (by rfl) ⟨1389804, by rfl⟩ : syracuseStep 3706145 = 2779609) B2779609
theorem B2461043 : Blo 574812 2461043 := bstep (se 1 (by rfl) ⟨1845782, by rfl⟩ : syracuseStep 2461043 = 3691565) B3691565
theorem B2461195 : Blo 574812 2461195 := bstep (se 1 (by rfl) ⟨1845896, by rfl⟩ : syracuseStep 2461195 = 3691793) B3691793
theorem B1642027 : Blo 574812 1642027 := bstep (se 1 (by rfl) ⟨1231520, by rfl⟩ : syracuseStep 1642027 = 2463041) B2463041
theorem B1642301 : Blo 574812 1642301 := bstep (se 3 (by rfl) ⟨307931, by rfl⟩ : syracuseStep 1642301 = 615863) B615863
theorem B692231 : Blo 574812 692231 := bstep (se 1 (by rfl) ⟨519173, by rfl⟩ : syracuseStep 692231 = 1038347) B1038347
theorem B2920535 : Blo 574812 2920535 := bstep (se 1 (by rfl) ⟨2190401, by rfl⟩ : syracuseStep 2920535 = 4380803) B4380803
theorem B1642643 : Blo 574812 1642643 := bstep (se 1 (by rfl) ⟨1231982, by rfl⟩ : syracuseStep 1642643 = 2463965) B2463965
theorem B6558083 : Blo 574812 6558083 := bstep (se 1 (by rfl) ⟨4918562, by rfl⟩ : syracuseStep 6558083 = 9837125) B9837125
theorem B14062045 : Blo 574812 14062045 := bstep (se 3 (by rfl) ⟨2636633, by rfl⟩ : syracuseStep 14062045 = 5273267) B5273267
theorem B3281411 : Blo 574812 3281411 := bstep (se 1 (by rfl) ⟨2461058, by rfl⟩ : syracuseStep 3281411 = 4922117) B4922117
theorem B2921021 : Blo 574812 2921021 := bstep (se 3 (by rfl) ⟨547691, by rfl⟩ : syracuseStep 2921021 = 1095383) B1095383
theorem B922487 : Blo 574812 922487 := bstep (se 1 (by rfl) ⟨691865, by rfl⟩ : syracuseStep 922487 = 1383731) B1383731
theorem B3281867 : Blo 574812 3281867 := bstep (se 1 (by rfl) ⟨2461400, by rfl⟩ : syracuseStep 3281867 = 4922801) B4922801
theorem B1381387 : Blo 574812 1381387 := bstep (se 1 (by rfl) ⟨1036040, by rfl⟩ : syracuseStep 1381387 = 2072081) B2072081
theorem B1381463 : Blo 574812 1381463 := bstep (se 1 (by rfl) ⟨1036097, by rfl⟩ : syracuseStep 1381463 = 2072195) B2072195
theorem B1971319 : Blo 574812 1971319 := bstep (se 1 (by rfl) ⟨1478489, by rfl⟩ : syracuseStep 1971319 = 2956979) B2956979
theorem B2462957 : Blo 574812 2462957 := bstep (se 3 (by rfl) ⟨461804, by rfl⟩ : syracuseStep 2462957 = 923609) B923609
theorem B792137 : Blo 574812 792137 := bstep (se 2 (by rfl) ⟨297051, by rfl⟩ : syracuseStep 792137 = 594103) B594103
theorem B3282551 : Blo 574812 3282551 := bstep (se 1 (by rfl) ⟨2461913, by rfl⟩ : syracuseStep 3282551 = 4923827) B4923827
theorem B923321 : Blo 574812 923321 := bstep (se 2 (by rfl) ⟨346245, by rfl⟩ : syracuseStep 923321 = 692491) B692491
theorem B22484789 : Blo 574812 22484789 := bstep (se 5 (by rfl) ⟨1053974, by rfl⟩ : syracuseStep 22484789 = 2107949) B2107949
theorem B1382291 : Blo 574812 1382291 := bstep (se 1 (by rfl) ⟨1036718, by rfl⟩ : syracuseStep 1382291 = 2073437) B2073437
theorem B2463641 : Blo 574812 2463641 := bstep (se 2 (by rfl) ⟨923865, by rfl⟩ : syracuseStep 2463641 = 1847731) B1847731
theorem B923833 : Blo 574812 923833 := bstep (se 2 (by rfl) ⟨346437, by rfl⟩ : syracuseStep 923833 = 692875) B692875
theorem B2955457 : Blo 574812 2955457 := bstep (se 2 (by rfl) ⟨1108296, by rfl⟩ : syracuseStep 2955457 = 2216593) B2216593
theorem B7411985 : Blo 574812 7411985 := bstep (se 2 (by rfl) ⟨2779494, by rfl⟩ : syracuseStep 7411985 = 5558989) B5558989
theorem B2922803 : Blo 574812 2922803 := bstep (se 1 (by rfl) ⟨2192102, by rfl⟩ : syracuseStep 2922803 = 4384205) B4384205
theorem B1644887 : Blo 574812 1644887 := bstep (se 1 (by rfl) ⟨1233665, by rfl⟩ : syracuseStep 1644887 = 2467331) B2467331
theorem B2923127 : Blo 574812 2923127 := bstep (se 1 (by rfl) ⟨2192345, by rfl⟩ : syracuseStep 2923127 = 4384691) B4384691
theorem B924551 : Blo 574812 924551 := bstep (se 1 (by rfl) ⟨693413, by rfl⟩ : syracuseStep 924551 = 1386827) B1386827
theorem B695287 : Blo 574812 695287 := bstep (se 1 (by rfl) ⟨521465, by rfl⟩ : syracuseStep 695287 = 1042931) B1042931
theorem B14851133 : Blo 574812 14851133 := bstep (se 3 (by rfl) ⟨2784587, by rfl⟩ : syracuseStep 14851133 = 5569175) B5569175
theorem B2661443 : Blo 574812 2661443 := bstep (se 1 (by rfl) ⟨1996082, by rfl⟩ : syracuseStep 2661443 = 3992165) B3992165
theorem B2628865 : Blo 574812 2628865 := bstep (se 2 (by rfl) ⟨985824, by rfl⟩ : syracuseStep 2628865 = 1971649) B1971649
theorem B1940921 : Blo 574812 1940921 := bstep (se 2 (by rfl) ⟨727845, by rfl⟩ : syracuseStep 1940921 = 1455691) B1455691
theorem B3284509 : Blo 574812 3284509 := bstep (se 3 (by rfl) ⟨615845, by rfl⟩ : syracuseStep 3284509 = 1231691) B1231691
theorem B2924099 : Blo 574812 2924099 := bstep (se 1 (by rfl) ⟨2193074, by rfl⟩ : syracuseStep 2924099 = 4386149) B4386149
theorem B2465569 : Blo 574812 2465569 := bstep (se 2 (by rfl) ⟨924588, by rfl⟩ : syracuseStep 2465569 = 1849177) B1849177
theorem B5250905 : Blo 574812 5250905 := bstep (se 2 (by rfl) ⟨1969089, by rfl⟩ : syracuseStep 5250905 = 3938179) B3938179
theorem B2924423 : Blo 574812 2924423 := bstep (se 1 (by rfl) ⟨2193317, by rfl⟩ : syracuseStep 2924423 = 4386635) B4386635
theorem B1941515 : Blo 574812 1941515 := bstep (se 1 (by rfl) ⟨1456136, by rfl⟩ : syracuseStep 1941515 = 2912273) B2912273
theorem B3285035 : Blo 574812 3285035 := bstep (se 1 (by rfl) ⟨2463776, by rfl⟩ : syracuseStep 3285035 = 4927553) B4927553
theorem B1941623 : Blo 574812 1941623 := bstep (se 1 (by rfl) ⟨1456217, by rfl⟩ : syracuseStep 1941623 = 2912435) B2912435
theorem B925967 : Blo 574812 925967 := bstep (se 1 (by rfl) ⟨694475, by rfl⟩ : syracuseStep 925967 = 1388951) B1388951
theorem B11969059 : Blo 574812 11969059 := bstep (se 1 (by rfl) ⟨8976794, by rfl⟩ : syracuseStep 11969059 = 17953589) B17953589
theorem B729643 : Blo 574812 729643 := bstep (se 1 (by rfl) ⟨547232, by rfl⟩ : syracuseStep 729643 = 1094465) B1094465
theorem B1942217 : Blo 574812 1942217 := bstep (se 2 (by rfl) ⟨728331, by rfl⟩ : syracuseStep 1942217 = 1456663) B1456663
theorem B1647631 : Blo 574812 1647631 := bstep (se 1 (by rfl) ⟨1235723, by rfl⟩ : syracuseStep 1647631 = 2471447) B2471447
theorem B1647677 : Blo 574812 1647677 := bstep (se 3 (by rfl) ⟨308939, by rfl⟩ : syracuseStep 1647677 = 617879) B617879
theorem B6661237 : Blo 574812 6661237 := bstep (se 5 (by rfl) ⟨312245, by rfl⟩ : syracuseStep 6661237 = 624491) B624491
theorem B926921 : Blo 574812 926921 := bstep (se 2 (by rfl) ⟨347595, by rfl⟩ : syracuseStep 926921 = 695191) B695191
theorem B2467073 : Blo 574812 2467073 := bstep (se 2 (by rfl) ⟨925152, by rfl⟩ : syracuseStep 2467073 = 1850305) B1850305
theorem B1942919 : Blo 574812 1942919 := bstep (se 1 (by rfl) ⟨1457189, by rfl⟩ : syracuseStep 1942919 = 2914379) B2914379
theorem B1648019 : Blo 574812 1648019 := bstep (se 1 (by rfl) ⟨1236014, by rfl⟩ : syracuseStep 1648019 = 2472029) B2472029
theorem B11838905 : Blo 574812 11838905 := bstep (se 2 (by rfl) ⟨4439589, by rfl⟩ : syracuseStep 11838905 = 8879179) B8879179
theorem B3286493 : Blo 574812 3286493 := bstep (se 3 (by rfl) ⟨616217, by rfl⟩ : syracuseStep 3286493 = 1232435) B1232435
theorem B730615 : Blo 574812 730615 := bstep (se 1 (by rfl) ⟨547961, by rfl⟩ : syracuseStep 730615 = 1095923) B1095923
theorem B2467415 : Blo 574812 2467415 := bstep (se 1 (by rfl) ⟨1850561, by rfl⟩ : syracuseStep 2467415 = 3701123) B3701123
theorem B1943297 : Blo 574812 1943297 := bstep (se 2 (by rfl) ⟨728736, by rfl⟩ : syracuseStep 1943297 = 1457473) B1457473
theorem B730939 : Blo 574812 730939 := bstep (se 1 (by rfl) ⟨548204, by rfl⟩ : syracuseStep 730939 = 1096409) B1096409
theorem B862223 : Blo 574812 862223 := bstep (se 1 (by rfl) ⟨646667, by rfl⟩ : syracuseStep 862223 = 1293335) B1293335
theorem B862265 : Blo 574812 862265 := bstep (se 2 (by rfl) ⟨323349, by rfl⟩ : syracuseStep 862265 = 646699) B646699
theorem B862343 : Blo 574812 862343 := bstep (se 1 (by rfl) ⟨646757, by rfl⟩ : syracuseStep 862343 = 1293515) B1293515
theorem B1091731 : Blo 574812 1091731 := bstep (se 1 (by rfl) ⟨818798, by rfl⟩ : syracuseStep 1091731 = 1637597) B1637597
theorem B862379 : Blo 574812 862379 := bstep (se 1 (by rfl) ⟨646784, by rfl⟩ : syracuseStep 862379 = 1293569) B1293569
theorem B7415981 : Blo 574812 7415981 := bstep (se 3 (by rfl) ⟨1390496, by rfl⟩ : syracuseStep 7415981 = 2780993) B2780993
theorem B862409 : Blo 574812 862409 := bstep (se 2 (by rfl) ⟨323403, by rfl⟩ : syracuseStep 862409 = 646807) B646807
theorem B862523 : Blo 574812 862523 := bstep (se 1 (by rfl) ⟨646892, by rfl⟩ : syracuseStep 862523 = 1293785) B1293785
theorem B3123515 : Blo 574812 3123515 := bstep (se 1 (by rfl) ⟨2342636, by rfl⟩ : syracuseStep 3123515 = 4685273) B4685273
theorem B11086145 : Blo 574812 11086145 := bstep (se 2 (by rfl) ⟨4157304, by rfl⟩ : syracuseStep 11086145 = 8314609) B8314609
theorem B862583 : Blo 574812 862583 := bstep (se 1 (by rfl) ⟨646937, by rfl⟩ : syracuseStep 862583 = 1293875) B1293875
theorem B862607 : Blo 574812 862607 := bstep (se 1 (by rfl) ⟨646955, by rfl⟩ : syracuseStep 862607 = 1293911) B1293911
theorem B862649 : Blo 574812 862649 := bstep (se 2 (by rfl) ⟨323493, by rfl⟩ : syracuseStep 862649 = 646987) B646987
theorem B862727 : Blo 574812 862727 := bstep (se 1 (by rfl) ⟨647045, by rfl⟩ : syracuseStep 862727 = 1294091) B1294091
theorem B862763 : Blo 574812 862763 := bstep (se 1 (by rfl) ⟨647072, by rfl⟩ : syracuseStep 862763 = 1294145) B1294145
theorem B1944107 : Blo 574812 1944107 := bstep (se 1 (by rfl) ⟨1458080, by rfl⟩ : syracuseStep 1944107 = 2916161) B2916161
theorem B3123755 : Blo 574812 3123755 := bstep (se 1 (by rfl) ⟨2342816, by rfl⟩ : syracuseStep 3123755 = 4685633) B4685633
theorem B1845821 : Blo 574812 1845821 := bstep (se 3 (by rfl) ⟨346091, by rfl⟩ : syracuseStep 1845821 = 692183) B692183
theorem B862793 : Blo 574812 862793 := bstep (se 2 (by rfl) ⟨323547, by rfl⟩ : syracuseStep 862793 = 647095) B647095
theorem B862907 : Blo 574812 862907 := bstep (se 1 (by rfl) ⟨647180, by rfl⟩ : syracuseStep 862907 = 1294361) B1294361
theorem B862967 : Blo 574812 862967 := bstep (se 1 (by rfl) ⟨647225, by rfl⟩ : syracuseStep 862967 = 1294451) B1294451
theorem B19999493 : Blo 574812 19999493 := bstep (se 4 (by rfl) ⟨1874952, by rfl⟩ : syracuseStep 19999493 = 3749905) B3749905
theorem B731911 : Blo 574812 731911 := bstep (se 1 (by rfl) ⟨548933, by rfl⟩ : syracuseStep 731911 = 1097867) B1097867
theorem B862991 : Blo 574812 862991 := bstep (se 1 (by rfl) ⟨647243, by rfl⟩ : syracuseStep 862991 = 1294487) B1294487
theorem B1387307 : Blo 574812 1387307 := bstep (se 1 (by rfl) ⟨1040480, by rfl⟩ : syracuseStep 1387307 = 2080961) B2080961
theorem B863033 : Blo 574812 863033 := bstep (se 2 (by rfl) ⟨323637, by rfl⟩ : syracuseStep 863033 = 647275) B647275
theorem B1977203 : Blo 574812 1977203 := bstep (se 1 (by rfl) ⟨1482902, by rfl⟩ : syracuseStep 1977203 = 2965805) B2965805
theorem B863111 : Blo 574812 863111 := bstep (se 1 (by rfl) ⟨647333, by rfl⟩ : syracuseStep 863111 = 1294667) B1294667
theorem B863147 : Blo 574812 863147 := bstep (se 1 (by rfl) ⟨647360, by rfl⟩ : syracuseStep 863147 = 1294721) B1294721
theorem B863177 : Blo 574812 863177 := bstep (se 2 (by rfl) ⟨323691, by rfl⟩ : syracuseStep 863177 = 647383) B647383
theorem B863291 : Blo 574812 863291 := bstep (se 1 (by rfl) ⟨647468, by rfl⟩ : syracuseStep 863291 = 1294937) B1294937
theorem B863351 : Blo 574812 863351 := bstep (se 1 (by rfl) ⟨647513, by rfl⟩ : syracuseStep 863351 = 1295027) B1295027
theorem B863375 : Blo 574812 863375 := bstep (se 1 (by rfl) ⟨647531, by rfl⟩ : syracuseStep 863375 = 1295063) B1295063
theorem B732331 : Blo 574812 732331 := bstep (se 1 (by rfl) ⟨549248, by rfl⟩ : syracuseStep 732331 = 1098497) B1098497
theorem B863417 : Blo 574812 863417 := bstep (se 2 (by rfl) ⟨323781, by rfl⟩ : syracuseStep 863417 = 647563) B647563
theorem B2075885 : Blo 574812 2075885 := bstep (se 3 (by rfl) ⟨389228, by rfl⟩ : syracuseStep 2075885 = 778457) B778457
theorem B863495 : Blo 574812 863495 := bstep (se 1 (by rfl) ⟨647621, by rfl⟩ : syracuseStep 863495 = 1295243) B1295243
theorem B863531 : Blo 574812 863531 := bstep (se 1 (by rfl) ⟨647648, by rfl⟩ : syracuseStep 863531 = 1295297) B1295297
theorem B1092923 : Blo 574812 1092923 := bstep (se 1 (by rfl) ⟨819692, by rfl⟩ : syracuseStep 1092923 = 1639385) B1639385
theorem B863561 : Blo 574812 863561 := bstep (se 2 (by rfl) ⟨323835, by rfl⟩ : syracuseStep 863561 = 647671) B647671
theorem B2927987 : Blo 574812 2927987 := bstep (se 1 (by rfl) ⟨2195990, by rfl⟩ : syracuseStep 2927987 = 4391981) B4391981
theorem B732559 : Blo 574812 732559 := bstep (se 1 (by rfl) ⟨549419, by rfl⟩ : syracuseStep 732559 = 1098839) B1098839
theorem B863675 : Blo 574812 863675 := bstep (se 1 (by rfl) ⟨647756, by rfl⟩ : syracuseStep 863675 = 1295513) B1295513
theorem B2469329 : Blo 574812 2469329 := bstep (se 2 (by rfl) ⟨925998, by rfl⟩ : syracuseStep 2469329 = 1851997) B1851997
theorem B863735 : Blo 574812 863735 := bstep (se 1 (by rfl) ⟨647801, by rfl⟩ : syracuseStep 863735 = 1295603) B1295603
theorem B863759 : Blo 574812 863759 := bstep (se 1 (by rfl) ⟨647819, by rfl⟩ : syracuseStep 863759 = 1295639) B1295639
theorem B863801 : Blo 574812 863801 := bstep (se 2 (by rfl) ⟨323925, by rfl⟩ : syracuseStep 863801 = 647851) B647851
theorem B1846871 : Blo 574812 1846871 := bstep (se 1 (by rfl) ⟨1385153, by rfl⟩ : syracuseStep 1846871 = 2770307) B2770307
theorem B863879 : Blo 574812 863879 := bstep (se 1 (by rfl) ⟨647909, by rfl⟩ : syracuseStep 863879 = 1295819) B1295819
theorem B863915 : Blo 574812 863915 := bstep (se 1 (by rfl) ⟨647936, by rfl⟩ : syracuseStep 863915 = 1295873) B1295873
theorem B863945 : Blo 574812 863945 := bstep (se 2 (by rfl) ⟨323979, by rfl⟩ : syracuseStep 863945 = 647959) B647959
theorem B3550949 : Blo 574812 3550949 := bstep (se 4 (by rfl) ⟨332901, by rfl⟩ : syracuseStep 3550949 = 665803) B665803
theorem B1093409 : Blo 574812 1093409 := bstep (se 2 (by rfl) ⟨410028, by rfl⟩ : syracuseStep 1093409 = 820057) B820057
theorem B3288883 : Blo 574812 3288883 := bstep (se 1 (by rfl) ⟨2466662, by rfl⟩ : syracuseStep 3288883 = 4933325) B4933325
theorem B864059 : Blo 574812 864059 := bstep (se 1 (by rfl) ⟨648044, by rfl⟩ : syracuseStep 864059 = 1296089) B1296089
theorem B1945403 : Blo 574812 1945403 := bstep (se 1 (by rfl) ⟨1459052, by rfl⟩ : syracuseStep 1945403 = 2918105) B2918105
theorem B2928473 : Blo 574812 2928473 := bstep (se 2 (by rfl) ⟨1098177, by rfl⟩ : syracuseStep 2928473 = 2196355) B2196355
theorem B864119 : Blo 574812 864119 := bstep (se 1 (by rfl) ⟨648089, by rfl⟩ : syracuseStep 864119 = 1296179) B1296179
theorem B864143 : Blo 574812 864143 := bstep (se 1 (by rfl) ⟨648107, by rfl⟩ : syracuseStep 864143 = 1296215) B1296215
theorem B26619799 : Blo 574812 26619799 := bstep (se 1 (by rfl) ⟨19964849, by rfl⟩ : syracuseStep 26619799 = 39929699) B39929699
theorem B1388441 : Blo 574812 1388441 := bstep (se 2 (by rfl) ⟨520665, by rfl⟩ : syracuseStep 1388441 = 1041331) B1041331
theorem B864185 : Blo 574812 864185 := bstep (se 2 (by rfl) ⟨324069, by rfl⟩ : syracuseStep 864185 = 648139) B648139
theorem B3321803 : Blo 574812 3321803 := bstep (se 1 (by rfl) ⟨2491352, by rfl⟩ : syracuseStep 3321803 = 4982705) B4982705
theorem B864263 : Blo 574812 864263 := bstep (se 1 (by rfl) ⟨648197, by rfl⟩ : syracuseStep 864263 = 1296395) B1296395
theorem B109555733 : Blo 574812 109555733 := bstep (se 6 (by rfl) ⟨2567712, by rfl⟩ : syracuseStep 109555733 = 5135425) B5135425
theorem B1093675 : Blo 574812 1093675 := bstep (se 1 (by rfl) ⟨820256, by rfl⟩ : syracuseStep 1093675 = 1640513) B1640513
theorem B864299 : Blo 574812 864299 := bstep (se 1 (by rfl) ⟨648224, by rfl⟩ : syracuseStep 864299 = 1296449) B1296449
theorem B864329 : Blo 574812 864329 := bstep (se 2 (by rfl) ⟨324123, by rfl⟩ : syracuseStep 864329 = 648247) B648247
theorem B864443 : Blo 574812 864443 := bstep (se 1 (by rfl) ⟨648332, by rfl⟩ : syracuseStep 864443 = 1296665) B1296665
theorem B864503 : Blo 574812 864503 := bstep (se 1 (by rfl) ⟨648377, by rfl⟩ : syracuseStep 864503 = 1296755) B1296755
theorem B864527 : Blo 574812 864527 := bstep (se 1 (by rfl) ⟨648395, by rfl⟩ : syracuseStep 864527 = 1296791) B1296791
theorem B1945889 : Blo 574812 1945889 := bstep (se 2 (by rfl) ⟨729708, by rfl⟩ : syracuseStep 1945889 = 1459417) B1459417
theorem B864569 : Blo 574812 864569 := bstep (se 2 (by rfl) ⟨324213, by rfl⟩ : syracuseStep 864569 = 648427) B648427
theorem B1585469 : Blo 574812 1585469 := bstep (se 3 (by rfl) ⟨297275, by rfl⟩ : syracuseStep 1585469 = 594551) B594551
theorem B864647 : Blo 574812 864647 := bstep (se 1 (by rfl) ⟨648485, by rfl⟩ : syracuseStep 864647 = 1296971) B1296971
theorem B864683 : Blo 574812 864683 := bstep (se 1 (by rfl) ⟨648512, by rfl⟩ : syracuseStep 864683 = 1297025) B1297025
theorem B864713 : Blo 574812 864713 := bstep (se 2 (by rfl) ⟨324267, by rfl⟩ : syracuseStep 864713 = 648535) B648535
theorem B864827 : Blo 574812 864827 := bstep (se 1 (by rfl) ⟨648620, by rfl⟩ : syracuseStep 864827 = 1297241) B1297241
theorem B2077271 : Blo 574812 2077271 := bstep (se 1 (by rfl) ⟨1557953, by rfl⟩ : syracuseStep 2077271 = 3115907) B3115907
theorem B864887 : Blo 574812 864887 := bstep (se 1 (by rfl) ⟨648665, by rfl⟩ : syracuseStep 864887 = 1297331) B1297331
theorem B864911 : Blo 574812 864911 := bstep (se 1 (by rfl) ⟨648683, by rfl⟩ : syracuseStep 864911 = 1297367) B1297367
theorem B864953 : Blo 574812 864953 := bstep (se 2 (by rfl) ⟨324357, by rfl⟩ : syracuseStep 864953 = 648715) B648715
theorem B865031 : Blo 574812 865031 := bstep (se 1 (by rfl) ⟨648773, by rfl⟩ : syracuseStep 865031 = 1297547) B1297547
theorem B865067 : Blo 574812 865067 := bstep (se 1 (by rfl) ⟨648800, by rfl⟩ : syracuseStep 865067 = 1297601) B1297601
theorem B1684283 : Blo 574812 1684283 := bstep (se 1 (by rfl) ⟨1263212, by rfl⟩ : syracuseStep 1684283 = 2526425) B2526425
theorem B865097 : Blo 574812 865097 := bstep (se 2 (by rfl) ⟨324411, by rfl⟩ : syracuseStep 865097 = 648823) B648823
theorem B1946483 : Blo 574812 1946483 := bstep (se 1 (by rfl) ⟨1459862, by rfl⟩ : syracuseStep 1946483 = 2919725) B2919725
theorem B865211 : Blo 574812 865211 := bstep (se 1 (by rfl) ⟨648908, by rfl⟩ : syracuseStep 865211 = 1297817) B1297817
theorem B2765771 : Blo 574812 2765771 := bstep (se 1 (by rfl) ⟨2074328, by rfl⟩ : syracuseStep 2765771 = 4148657) B4148657
theorem B865271 : Blo 574812 865271 := bstep (se 1 (by rfl) ⟨648953, by rfl⟩ : syracuseStep 865271 = 1297907) B1297907
theorem B9876491 : Blo 574812 9876491 := bstep (se 1 (by rfl) ⟨7407368, by rfl⟩ : syracuseStep 9876491 = 14814737) B14814737
theorem B865295 : Blo 574812 865295 := bstep (se 1 (by rfl) ⟨648971, by rfl⟩ : syracuseStep 865295 = 1297943) B1297943
theorem B865337 : Blo 574812 865337 := bstep (se 2 (by rfl) ⟨324501, by rfl⟩ : syracuseStep 865337 = 649003) B649003
theorem B1094791 : Blo 574812 1094791 := bstep (se 1 (by rfl) ⟨821093, by rfl⟩ : syracuseStep 1094791 = 1642187) B1642187
theorem B865415 : Blo 574812 865415 := bstep (se 1 (by rfl) ⟨649061, by rfl⟩ : syracuseStep 865415 = 1298123) B1298123
theorem B865451 : Blo 574812 865451 := bstep (se 1 (by rfl) ⟨649088, by rfl⟩ : syracuseStep 865451 = 1298177) B1298177
theorem B865481 : Blo 574812 865481 := bstep (se 2 (by rfl) ⟨324555, by rfl⟩ : syracuseStep 865481 = 649111) B649111
theorem B3290341 : Blo 574812 3290341 := bstep (se 4 (by rfl) ⟨308469, by rfl⟩ : syracuseStep 3290341 = 616939) B616939
theorem B865595 : Blo 574812 865595 := bstep (se 1 (by rfl) ⟨649196, by rfl⟩ : syracuseStep 865595 = 1298393) B1298393
theorem B1455479 : Blo 574812 1455479 := bstep (se 1 (by rfl) ⟨1091609, by rfl⟩ : syracuseStep 1455479 = 2183219) B2183219
theorem B865655 : Blo 574812 865655 := bstep (se 1 (by rfl) ⟨649241, by rfl⟩ : syracuseStep 865655 = 1298483) B1298483
theorem B9352583 : Blo 574812 9352583 := bstep (se 1 (by rfl) ⟨7014437, by rfl⟩ : syracuseStep 9352583 = 14028875) B14028875
theorem B865679 : Blo 574812 865679 := bstep (se 1 (by rfl) ⟨649259, by rfl⟩ : syracuseStep 865679 = 1298519) B1298519
theorem B865721 : Blo 574812 865721 := bstep (se 2 (by rfl) ⟨324645, by rfl⟩ : syracuseStep 865721 = 649291) B649291
theorem B865799 : Blo 574812 865799 := bstep (se 1 (by rfl) ⟨649349, by rfl⟩ : syracuseStep 865799 = 1298699) B1298699
theorem B865835 : Blo 574812 865835 := bstep (se 1 (by rfl) ⟨649376, by rfl⟩ : syracuseStep 865835 = 1298753) B1298753
theorem B2635325 : Blo 574812 2635325 := bstep (se 3 (by rfl) ⟨494123, by rfl⟩ : syracuseStep 2635325 = 988247) B988247
theorem B865865 : Blo 574812 865865 := bstep (se 2 (by rfl) ⟨324699, by rfl⟩ : syracuseStep 865865 = 649399) B649399
theorem B1095353 : Blo 574812 1095353 := bstep (se 2 (by rfl) ⟨410757, by rfl⟩ : syracuseStep 1095353 = 821515) B821515
theorem B865979 : Blo 574812 865979 := bstep (se 1 (by rfl) ⟨649484, by rfl⟩ : syracuseStep 865979 = 1298969) B1298969
theorem B866039 : Blo 574812 866039 := bstep (se 1 (by rfl) ⟨649529, by rfl⟩ : syracuseStep 866039 = 1299059) B1299059
theorem B866063 : Blo 574812 866063 := bstep (se 1 (by rfl) ⟨649547, by rfl⟩ : syracuseStep 866063 = 1299095) B1299095
theorem B866105 : Blo 574812 866105 := bstep (se 2 (by rfl) ⟨324789, by rfl⟩ : syracuseStep 866105 = 649579) B649579
theorem B866183 : Blo 574812 866183 := bstep (se 1 (by rfl) ⟨649637, by rfl⟩ : syracuseStep 866183 = 1299275) B1299275
theorem B866219 : Blo 574812 866219 := bstep (se 1 (by rfl) ⟨649664, by rfl⟩ : syracuseStep 866219 = 1299329) B1299329
theorem B866249 : Blo 574812 866249 := bstep (se 2 (by rfl) ⟨324843, by rfl⟩ : syracuseStep 866249 = 649687) B649687
theorem B86751245 : Blo 574812 86751245 := bstep (se 3 (by rfl) ⟨16265858, by rfl⟩ : syracuseStep 86751245 = 32531717) B32531717
theorem B866363 : Blo 574812 866363 := bstep (se 1 (by rfl) ⟨649772, by rfl⟩ : syracuseStep 866363 = 1299545) B1299545
theorem B4372541 : Blo 574812 4372541 := bstep (se 3 (by rfl) ⟨819851, by rfl⟩ : syracuseStep 4372541 = 1639703) B1639703
theorem B866423 : Blo 574812 866423 := bstep (se 1 (by rfl) ⟨649817, by rfl⟩ : syracuseStep 866423 = 1299635) B1299635
theorem B866447 : Blo 574812 866447 := bstep (se 1 (by rfl) ⟨649835, by rfl⟩ : syracuseStep 866447 = 1299671) B1299671
theorem B866489 : Blo 574812 866489 := bstep (se 2 (by rfl) ⟨324933, by rfl⟩ : syracuseStep 866489 = 649867) B649867
theorem B866567 : Blo 574812 866567 := bstep (se 1 (by rfl) ⟨649925, by rfl⟩ : syracuseStep 866567 = 1299851) B1299851
theorem B866603 : Blo 574812 866603 := bstep (se 1 (by rfl) ⟨649952, by rfl⟩ : syracuseStep 866603 = 1299905) B1299905
theorem B26589505 : Blo 574812 26589505 := bstep (se 2 (by rfl) ⟨9971064, by rfl⟩ : syracuseStep 26589505 = 19942129) B19942129
theorem B866633 : Blo 574812 866633 := bstep (se 2 (by rfl) ⟨324987, by rfl⟩ : syracuseStep 866633 = 649975) B649975
theorem B2767193 : Blo 574812 2767193 := bstep (se 2 (by rfl) ⟨1037697, by rfl⟩ : syracuseStep 2767193 = 2075395) B2075395
theorem B7027037 : Blo 574812 7027037 := bstep (se 3 (by rfl) ⟨1317569, by rfl⟩ : syracuseStep 7027037 = 2635139) B2635139
theorem B866747 : Blo 574812 866747 := bstep (se 1 (by rfl) ⟨650060, by rfl⟩ : syracuseStep 866747 = 1300121) B1300121
theorem B4143581 : Blo 574812 4143581 := bstep (se 3 (by rfl) ⟨776921, by rfl⟩ : syracuseStep 4143581 = 1553843) B1553843
theorem B866807 : Blo 574812 866807 := bstep (se 1 (by rfl) ⟨650105, by rfl⟩ : syracuseStep 866807 = 1300211) B1300211
theorem B3258883 : Blo 574812 3258883 := bstep (se 1 (by rfl) ⟨2444162, by rfl⟩ : syracuseStep 3258883 = 4888325) B4888325
theorem B866831 : Blo 574812 866831 := bstep (se 1 (by rfl) ⟨650123, by rfl⟩ : syracuseStep 866831 = 1300247) B1300247
theorem B4569643 : Blo 574812 4569643 := bstep (se 1 (by rfl) ⟨3427232, by rfl⟩ : syracuseStep 4569643 = 6854465) B6854465
theorem B866873 : Blo 574812 866873 := bstep (se 2 (by rfl) ⟨325077, by rfl⟩ : syracuseStep 866873 = 650155) B650155
theorem B1456775 : Blo 574812 1456775 := bstep (se 1 (by rfl) ⟨1092581, by rfl⟩ : syracuseStep 1456775 = 2185163) B2185163
theorem B866951 : Blo 574812 866951 := bstep (se 1 (by rfl) ⟨650213, by rfl⟩ : syracuseStep 866951 = 1300427) B1300427
theorem B866987 : Blo 574812 866987 := bstep (se 1 (by rfl) ⟨650240, by rfl⟩ : syracuseStep 866987 = 1300481) B1300481
theorem B1456825 : Blo 574812 1456825 := bstep (se 2 (by rfl) ⟨546309, by rfl⟩ : syracuseStep 1456825 = 1092619) B1092619
theorem B867017 : Blo 574812 867017 := bstep (se 2 (by rfl) ⟨325131, by rfl⟩ : syracuseStep 867017 = 650263) B650263
theorem B1096507 : Blo 574812 1096507 := bstep (se 1 (by rfl) ⟨822380, by rfl⟩ : syracuseStep 1096507 = 1644761) B1644761
theorem B867131 : Blo 574812 867131 := bstep (se 1 (by rfl) ⟨650348, by rfl⟩ : syracuseStep 867131 = 1300697) B1300697
theorem B1522547 : Blo 574812 1522547 := bstep (se 1 (by rfl) ⟨1141910, by rfl⟩ : syracuseStep 1522547 = 2283821) B2283821
theorem B867191 : Blo 574812 867191 := bstep (se 1 (by rfl) ⟨650393, by rfl⟩ : syracuseStep 867191 = 1300787) B1300787
theorem B867215 : Blo 574812 867215 := bstep (se 1 (by rfl) ⟨650411, by rfl⟩ : syracuseStep 867215 = 1300823) B1300823
theorem B867257 : Blo 574812 867257 := bstep (se 2 (by rfl) ⟨325221, by rfl⟩ : syracuseStep 867257 = 650443) B650443
theorem B867335 : Blo 574812 867335 := bstep (se 1 (by rfl) ⟨650501, by rfl⟩ : syracuseStep 867335 = 1301003) B1301003
theorem B867371 : Blo 574812 867371 := bstep (se 1 (by rfl) ⟨650528, by rfl⟩ : syracuseStep 867371 = 1301057) B1301057
theorem B1293371 : Blo 574812 1293371 := bstep (se 1 (by rfl) ⟨970028, by rfl⟩ : syracuseStep 1293371 = 1940057) B1940057
theorem B867401 : Blo 574812 867401 := bstep (se 2 (by rfl) ⟨325275, by rfl⟩ : syracuseStep 867401 = 650551) B650551
theorem B1293497 : Blo 574812 1293497 := bstep (se 2 (by rfl) ⟨485061, by rfl⟩ : syracuseStep 1293497 = 970123) B970123
theorem B867515 : Blo 574812 867515 := bstep (se 1 (by rfl) ⟨650636, by rfl⟩ : syracuseStep 867515 = 1301273) B1301273
theorem B867575 : Blo 574812 867575 := bstep (se 1 (by rfl) ⟨650681, by rfl⟩ : syracuseStep 867575 = 1301363) B1301363
theorem B1457423 : Blo 574812 1457423 := bstep (se 1 (by rfl) ⟨1093067, by rfl⟩ : syracuseStep 1457423 = 2186135) B2186135
theorem B867599 : Blo 574812 867599 := bstep (se 1 (by rfl) ⟨650699, by rfl⟩ : syracuseStep 867599 = 1301399) B1301399
theorem B1096993 : Blo 574812 1096993 := bstep (se 2 (by rfl) ⟨411372, by rfl⟩ : syracuseStep 1096993 = 822745) B822745
theorem B867641 : Blo 574812 867641 := bstep (se 2 (by rfl) ⟨325365, by rfl⟩ : syracuseStep 867641 = 650731) B650731
theorem B1752455 : Blo 574812 1752455 := bstep (se 1 (by rfl) ⟨1314341, by rfl⟩ : syracuseStep 1752455 = 2628683) B2628683
theorem B867719 : Blo 574812 867719 := bstep (se 1 (by rfl) ⟨650789, by rfl⟩ : syracuseStep 867719 = 1301579) B1301579
theorem B1949075 : Blo 574812 1949075 := bstep (se 1 (by rfl) ⟨1461806, by rfl⟩ : syracuseStep 1949075 = 2923613) B2923613
theorem B867755 : Blo 574812 867755 := bstep (se 1 (by rfl) ⟨650816, by rfl⟩ : syracuseStep 867755 = 1301633) B1301633
theorem B867785 : Blo 574812 867785 := bstep (se 2 (by rfl) ⟨325419, by rfl⟩ : syracuseStep 867785 = 650839) B650839
theorem B6995405 : Blo 574812 6995405 := bstep (se 3 (by rfl) ⟨1311638, by rfl⟩ : syracuseStep 6995405 = 2623277) B2623277
theorem B1293839 : Blo 574812 1293839 := bstep (se 1 (by rfl) ⟨970379, by rfl⟩ : syracuseStep 1293839 = 1940759) B1940759
theorem B1293857 : Blo 574812 1293857 := bstep (se 2 (by rfl) ⟨485196, by rfl⟩ : syracuseStep 1293857 = 970393) B970393
theorem B867899 : Blo 574812 867899 := bstep (se 1 (by rfl) ⟨650924, by rfl⟩ : syracuseStep 867899 = 1301849) B1301849
theorem B867959 : Blo 574812 867959 := bstep (se 1 (by rfl) ⟨650969, by rfl⟩ : syracuseStep 867959 = 1301939) B1301939
theorem B867983 : Blo 574812 867983 := bstep (se 1 (by rfl) ⟨650987, by rfl⟩ : syracuseStep 867983 = 1301975) B1301975
theorem B868025 : Blo 574812 868025 := bstep (se 2 (by rfl) ⟨325509, by rfl⟩ : syracuseStep 868025 = 651019) B651019
theorem B868103 : Blo 574812 868103 := bstep (se 1 (by rfl) ⟨651077, by rfl⟩ : syracuseStep 868103 = 1302155) B1302155
theorem B868139 : Blo 574812 868139 := bstep (se 1 (by rfl) ⟨651104, by rfl⟩ : syracuseStep 868139 = 1302209) B1302209
theorem B868169 : Blo 574812 868169 := bstep (se 2 (by rfl) ⟨325563, by rfl⟩ : syracuseStep 868169 = 651127) B651127
theorem B1294199 : Blo 574812 1294199 := bstep (se 1 (by rfl) ⟨970649, by rfl⟩ : syracuseStep 1294199 = 1941299) B1941299
theorem B3293075 : Blo 574812 3293075 := bstep (se 1 (by rfl) ⟨2469806, by rfl⟩ : syracuseStep 3293075 = 4939613) B4939613
theorem B1228745 : Blo 574812 1228745 := bstep (se 2 (by rfl) ⟨460779, by rfl⟩ : syracuseStep 1228745 = 921559) B921559
theorem B1458121 : Blo 574812 1458121 := bstep (se 2 (by rfl) ⟨546795, by rfl⟩ : syracuseStep 1458121 = 1093591) B1093591
theorem B1294379 : Blo 574812 1294379 := bstep (se 1 (by rfl) ⟨970784, by rfl⟩ : syracuseStep 1294379 = 1941569) B1941569
theorem B1458263 : Blo 574812 1458263 := bstep (se 1 (by rfl) ⟨1093697, by rfl⟩ : syracuseStep 1458263 = 2187395) B2187395
theorem B1294739 : Blo 574812 1294739 := bstep (se 1 (by rfl) ⟨971054, by rfl⟩ : syracuseStep 1294739 = 1942109) B1942109
theorem B1294793 : Blo 574812 1294793 := bstep (se 2 (by rfl) ⟨485547, by rfl⟩ : syracuseStep 1294793 = 971095) B971095
theorem B1098299 : Blo 574812 1098299 := bstep (se 1 (by rfl) ⟨823724, by rfl⟩ : syracuseStep 1098299 = 1647449) B1647449
theorem B3293783 : Blo 574812 3293783 := bstep (se 1 (by rfl) ⟨2470337, by rfl⟩ : syracuseStep 3293783 = 4940675) B4940675
theorem B1950479 : Blo 574812 1950479 := bstep (se 1 (by rfl) ⟨1462859, by rfl⟩ : syracuseStep 1950479 = 2925719) B2925719
theorem B1688455 : Blo 574812 1688455 := bstep (se 1 (by rfl) ⟨1266341, by rfl⟩ : syracuseStep 1688455 = 2532683) B2532683
theorem B1950749 : Blo 574812 1950749 := bstep (se 3 (by rfl) ⟨365765, by rfl⟩ : syracuseStep 1950749 = 731531) B731531
theorem B1098785 : Blo 574812 1098785 := bstep (se 2 (by rfl) ⟨412044, by rfl⟩ : syracuseStep 1098785 = 824089) B824089
theorem B1295495 : Blo 574812 1295495 := bstep (se 1 (by rfl) ⟨971621, by rfl⟩ : syracuseStep 1295495 = 1943243) B1943243
theorem B9880865 : Blo 574812 9880865 := bstep (se 2 (by rfl) ⟨3705324, by rfl⟩ : syracuseStep 9880865 = 7410649) B7410649
theorem B1295675 : Blo 574812 1295675 := bstep (se 1 (by rfl) ⟨971756, by rfl⟩ : syracuseStep 1295675 = 1943513) B1943513
theorem B574855 : Blo 574812 574855 := bstep (se 1 (by rfl) ⟨431141, by rfl⟩ : syracuseStep 574855 = 862283) B862283
theorem B4375943 : Blo 574812 4375943 := bstep (se 1 (by rfl) ⟨3281957, by rfl⟩ : syracuseStep 4375943 = 6563915) B6563915
theorem B574863 : Blo 574812 574863 := bstep (se 1 (by rfl) ⟨431147, by rfl⟩ : syracuseStep 574863 = 862295) B862295
theorem B1623449 : Blo 574812 1623449 := bstep (se 2 (by rfl) ⟨608793, by rfl⟩ : syracuseStep 1623449 = 1217587) B1217587
theorem B1295801 : Blo 574812 1295801 := bstep (se 2 (by rfl) ⟨485925, by rfl⟩ : syracuseStep 1295801 = 971851) B971851
theorem B574907 : Blo 574812 574907 := bstep (se 1 (by rfl) ⟨431180, by rfl⟩ : syracuseStep 574907 = 862361) B862361
theorem B3556867 : Blo 574812 3556867 := bstep (se 1 (by rfl) ⟨2667650, by rfl⟩ : syracuseStep 3556867 = 5335301) B5335301
theorem B574983 : Blo 574812 574983 := bstep (se 1 (by rfl) ⟨431237, by rfl⟩ : syracuseStep 574983 = 862475) B862475
theorem B574991 : Blo 574812 574991 := bstep (se 1 (by rfl) ⟨431243, by rfl⟩ : syracuseStep 574991 = 862487) B862487
theorem B575035 : Blo 574812 575035 := bstep (se 1 (by rfl) ⟨431276, by rfl⟩ : syracuseStep 575035 = 862553) B862553
theorem B2770519 : Blo 574812 2770519 := bstep (se 1 (by rfl) ⟨2077889, by rfl⟩ : syracuseStep 2770519 = 4155779) B4155779
theorem B575111 : Blo 574812 575111 := bstep (se 1 (by rfl) ⟨431333, by rfl⟩ : syracuseStep 575111 = 862667) B862667
theorem B575119 : Blo 574812 575119 := bstep (se 1 (by rfl) ⟨431339, by rfl⟩ : syracuseStep 575119 = 862679) B862679
theorem B575163 : Blo 574812 575163 := bstep (se 1 (by rfl) ⟨431372, by rfl⟩ : syracuseStep 575163 = 862745) B862745
theorem B575239 : Blo 574812 575239 := bstep (se 1 (by rfl) ⟨431429, by rfl⟩ : syracuseStep 575239 = 862859) B862859
theorem B575247 : Blo 574812 575247 := bstep (se 1 (by rfl) ⟨431435, by rfl⟩ : syracuseStep 575247 = 862871) B862871
theorem B1296143 : Blo 574812 1296143 := bstep (se 1 (by rfl) ⟨972107, by rfl⟩ : syracuseStep 1296143 = 1944215) B1944215
theorem B1296161 : Blo 574812 1296161 := bstep (se 2 (by rfl) ⟨486060, by rfl⟩ : syracuseStep 1296161 = 972121) B972121
theorem B575291 : Blo 574812 575291 := bstep (se 1 (by rfl) ⟨431468, by rfl⟩ : syracuseStep 575291 = 862937) B862937
theorem B24889153 : Blo 574812 24889153 := bstep (se 2 (by rfl) ⟨9333432, by rfl⟩ : syracuseStep 24889153 = 18666865) B18666865
theorem B575367 : Blo 574812 575367 := bstep (se 1 (by rfl) ⟨431525, by rfl⟩ : syracuseStep 575367 = 863051) B863051
theorem B1230727 : Blo 574812 1230727 := bstep (se 1 (by rfl) ⟨923045, by rfl⟩ : syracuseStep 1230727 = 1846091) B1846091
theorem B575375 : Blo 574812 575375 := bstep (se 1 (by rfl) ⟨431531, by rfl⟩ : syracuseStep 575375 = 863063) B863063
theorem B575419 : Blo 574812 575419 := bstep (se 1 (by rfl) ⟨431564, by rfl⟩ : syracuseStep 575419 = 863129) B863129
theorem B575495 : Blo 574812 575495 := bstep (se 1 (by rfl) ⟨431621, by rfl⟩ : syracuseStep 575495 = 863243) B863243
theorem B575503 : Blo 574812 575503 := bstep (se 1 (by rfl) ⟨431627, by rfl⟩ : syracuseStep 575503 = 863255) B863255
theorem B1755179 : Blo 574812 1755179 := bstep (se 1 (by rfl) ⟨1316384, by rfl⟩ : syracuseStep 1755179 = 2632769) B2632769
theorem B575547 : Blo 574812 575547 := bstep (se 1 (by rfl) ⟨431660, by rfl⟩ : syracuseStep 575547 = 863321) B863321
theorem B1460339 : Blo 574812 1460339 := bstep (se 1 (by rfl) ⟨1095254, by rfl⟩ : syracuseStep 1460339 = 2190509) B2190509
theorem B1296503 : Blo 574812 1296503 := bstep (se 1 (by rfl) ⟨972377, by rfl⟩ : syracuseStep 1296503 = 1944755) B1944755
theorem B1165447 : Blo 574812 1165447 := bstep (se 1 (by rfl) ⟨874085, by rfl⟩ : syracuseStep 1165447 = 1748171) B1748171
theorem B575623 : Blo 574812 575623 := bstep (se 1 (by rfl) ⟨431717, by rfl⟩ : syracuseStep 575623 = 863435) B863435
theorem B575631 : Blo 574812 575631 := bstep (se 1 (by rfl) ⟨431723, by rfl⟩ : syracuseStep 575631 = 863447) B863447
theorem B575675 : Blo 574812 575675 := bstep (se 1 (by rfl) ⟨431756, by rfl⟩ : syracuseStep 575675 = 863513) B863513
theorem B1329353 : Blo 574812 1329353 := bstep (se 2 (by rfl) ⟨498507, by rfl⟩ : syracuseStep 1329353 = 997015) B997015
theorem B575751 : Blo 574812 575751 := bstep (se 1 (by rfl) ⟨431813, by rfl⟩ : syracuseStep 575751 = 863627) B863627
theorem B575759 : Blo 574812 575759 := bstep (se 1 (by rfl) ⟨431819, by rfl⟩ : syracuseStep 575759 = 863639) B863639
theorem B1296683 : Blo 574812 1296683 := bstep (se 1 (by rfl) ⟨972512, by rfl⟩ : syracuseStep 1296683 = 1945025) B1945025
theorem B575803 : Blo 574812 575803 := bstep (se 1 (by rfl) ⟨431852, by rfl⟩ : syracuseStep 575803 = 863705) B863705
theorem B575879 : Blo 574812 575879 := bstep (se 1 (by rfl) ⟨431909, by rfl⟩ : syracuseStep 575879 = 863819) B863819
theorem B575887 : Blo 574812 575887 := bstep (se 1 (by rfl) ⟨431915, by rfl⟩ : syracuseStep 575887 = 863831) B863831
theorem B1952153 : Blo 574812 1952153 := bstep (se 2 (by rfl) ⟨732057, by rfl⟩ : syracuseStep 1952153 = 1464115) B1464115
theorem B3295673 : Blo 574812 3295673 := bstep (se 2 (by rfl) ⟨1235877, by rfl⟩ : syracuseStep 3295673 = 2471755) B2471755
theorem B575931 : Blo 574812 575931 := bstep (se 1 (by rfl) ⟨431948, by rfl⟩ : syracuseStep 575931 = 863897) B863897
theorem B576007 : Blo 574812 576007 := bstep (se 1 (by rfl) ⟨432005, by rfl⟩ : syracuseStep 576007 = 864011) B864011
theorem B576015 : Blo 574812 576015 := bstep (se 1 (by rfl) ⟨432011, by rfl⟩ : syracuseStep 576015 = 864023) B864023
theorem B576059 : Blo 574812 576059 := bstep (se 1 (by rfl) ⟨432044, by rfl⟩ : syracuseStep 576059 = 864089) B864089
theorem B6572663 : Blo 574812 6572663 := bstep (se 1 (by rfl) ⟨4929497, by rfl⟩ : syracuseStep 6572663 = 9858995) B9858995
theorem B1460855 : Blo 574812 1460855 := bstep (se 1 (by rfl) ⟨1095641, by rfl⟩ : syracuseStep 1460855 = 2191283) B2191283
theorem B576135 : Blo 574812 576135 := bstep (se 1 (by rfl) ⟨432101, by rfl⟩ : syracuseStep 576135 = 864203) B864203
theorem B576143 : Blo 574812 576143 := bstep (se 1 (by rfl) ⟨432107, by rfl⟩ : syracuseStep 576143 = 864215) B864215
theorem B1297043 : Blo 574812 1297043 := bstep (se 1 (by rfl) ⟨972782, by rfl⟩ : syracuseStep 1297043 = 1945565) B1945565
theorem B576187 : Blo 574812 576187 := bstep (se 1 (by rfl) ⟨432140, by rfl⟩ : syracuseStep 576187 = 864281) B864281
theorem B1297097 : Blo 574812 1297097 := bstep (se 2 (by rfl) ⟨486411, by rfl⟩ : syracuseStep 1297097 = 972823) B972823
theorem B576263 : Blo 574812 576263 := bstep (se 1 (by rfl) ⟨432197, by rfl⟩ : syracuseStep 576263 = 864395) B864395
theorem B576271 : Blo 574812 576271 := bstep (se 1 (by rfl) ⟨432203, by rfl⟩ : syracuseStep 576271 = 864407) B864407
theorem B1166113 : Blo 574812 1166113 := bstep (se 2 (by rfl) ⟨437292, by rfl⟩ : syracuseStep 1166113 = 874585) B874585
theorem B576315 : Blo 574812 576315 := bstep (se 1 (by rfl) ⟨432236, by rfl⟩ : syracuseStep 576315 = 864473) B864473
theorem B576391 : Blo 574812 576391 := bstep (se 1 (by rfl) ⟨432293, by rfl⟩ : syracuseStep 576391 = 864587) B864587
theorem B576399 : Blo 574812 576399 := bstep (se 1 (by rfl) ⟨432299, by rfl⟩ : syracuseStep 576399 = 864599) B864599
theorem B576443 : Blo 574812 576443 := bstep (se 1 (by rfl) ⟨432332, by rfl⟩ : syracuseStep 576443 = 864665) B864665
theorem B4148171 : Blo 574812 4148171 := bstep (se 1 (by rfl) ⟨3111128, by rfl⟩ : syracuseStep 4148171 = 6222257) B6222257
theorem B2771921 : Blo 574812 2771921 := bstep (se 2 (by rfl) ⟨1039470, by rfl⟩ : syracuseStep 2771921 = 2078941) B2078941
theorem B576519 : Blo 574812 576519 := bstep (se 1 (by rfl) ⟨432389, by rfl⟩ : syracuseStep 576519 = 864779) B864779
theorem B576527 : Blo 574812 576527 := bstep (se 1 (by rfl) ⟨432395, by rfl⟩ : syracuseStep 576527 = 864791) B864791
theorem B576571 : Blo 574812 576571 := bstep (se 1 (by rfl) ⟨432428, by rfl⟩ : syracuseStep 576571 = 864857) B864857
theorem B1231931 : Blo 574812 1231931 := bstep (se 1 (by rfl) ⟨923948, by rfl⟩ : syracuseStep 1231931 = 1847897) B1847897
theorem B1952855 : Blo 574812 1952855 := bstep (se 1 (by rfl) ⟨1464641, by rfl⟩ : syracuseStep 1952855 = 2929283) B2929283
theorem B576647 : Blo 574812 576647 := bstep (se 1 (by rfl) ⟨432485, by rfl⟩ : syracuseStep 576647 = 864971) B864971
theorem B576655 : Blo 574812 576655 := bstep (se 1 (by rfl) ⟨432491, by rfl⟩ : syracuseStep 576655 = 864983) B864983
theorem B576699 : Blo 574812 576699 := bstep (se 1 (by rfl) ⟨432524, by rfl⟩ : syracuseStep 576699 = 865049) B865049
theorem B576775 : Blo 574812 576775 := bstep (se 1 (by rfl) ⟨432581, by rfl⟩ : syracuseStep 576775 = 865163) B865163
theorem B576783 : Blo 574812 576783 := bstep (se 1 (by rfl) ⟨432587, by rfl⟩ : syracuseStep 576783 = 865175) B865175
theorem B576827 : Blo 574812 576827 := bstep (se 1 (by rfl) ⟨432620, by rfl⟩ : syracuseStep 576827 = 865241) B865241
theorem B970103 : Blo 574812 970103 := bstep (se 1 (by rfl) ⟨727577, by rfl⟩ : syracuseStep 970103 = 1455155) B1455155
theorem B576903 : Blo 574812 576903 := bstep (se 1 (by rfl) ⟨432677, by rfl⟩ : syracuseStep 576903 = 865355) B865355
theorem B2182535 : Blo 574812 2182535 := bstep (se 1 (by rfl) ⟨1636901, by rfl⟩ : syracuseStep 2182535 = 3273803) B3273803
theorem B9850247 : Blo 574812 9850247 := bstep (se 1 (by rfl) ⟨7387685, by rfl⟩ : syracuseStep 9850247 = 14775371) B14775371
theorem B1297799 : Blo 574812 1297799 := bstep (se 1 (by rfl) ⟨973349, by rfl⟩ : syracuseStep 1297799 = 1946699) B1946699
theorem B576911 : Blo 574812 576911 := bstep (se 1 (by rfl) ⟨432683, by rfl⟩ : syracuseStep 576911 = 865367) B865367
theorem B576955 : Blo 574812 576955 := bstep (se 1 (by rfl) ⟨432716, by rfl⟩ : syracuseStep 576955 = 865433) B865433
theorem B577031 : Blo 574812 577031 := bstep (se 1 (by rfl) ⟨432773, by rfl⟩ : syracuseStep 577031 = 865547) B865547
theorem B2084363 : Blo 574812 2084363 := bstep (se 1 (by rfl) ⟨1563272, by rfl⟩ : syracuseStep 2084363 = 3126545) B3126545
theorem B577039 : Blo 574812 577039 := bstep (se 1 (by rfl) ⟨432779, by rfl⟩ : syracuseStep 577039 = 865559) B865559
theorem B1166891 : Blo 574812 1166891 := bstep (se 1 (by rfl) ⟨875168, by rfl⟩ : syracuseStep 1166891 = 1750337) B1750337
theorem B1297979 : Blo 574812 1297979 := bstep (se 1 (by rfl) ⟨973484, by rfl⟩ : syracuseStep 1297979 = 1946969) B1946969
theorem B1232443 : Blo 574812 1232443 := bstep (se 1 (by rfl) ⟨924332, by rfl⟩ : syracuseStep 1232443 = 1848665) B1848665
theorem B577083 : Blo 574812 577083 := bstep (se 1 (by rfl) ⟨432812, by rfl⟩ : syracuseStep 577083 = 865625) B865625
theorem B1953341 : Blo 574812 1953341 := bstep (se 3 (by rfl) ⟨366251, by rfl⟩ : syracuseStep 1953341 = 732503) B732503
theorem B1461847 : Blo 574812 1461847 := bstep (se 1 (by rfl) ⟨1096385, by rfl⟩ : syracuseStep 1461847 = 2192771) B2192771
theorem B577159 : Blo 574812 577159 := bstep (se 1 (by rfl) ⟨432869, by rfl⟩ : syracuseStep 577159 = 865739) B865739
theorem B577167 : Blo 574812 577167 := bstep (se 1 (by rfl) ⟨432875, by rfl⟩ : syracuseStep 577167 = 865751) B865751
theorem B1298105 : Blo 574812 1298105 := bstep (se 2 (by rfl) ⟨486789, by rfl⟩ : syracuseStep 1298105 = 973579) B973579
theorem B577211 : Blo 574812 577211 := bstep (se 1 (by rfl) ⟨432908, by rfl⟩ : syracuseStep 577211 = 865817) B865817
theorem B577287 : Blo 574812 577287 := bstep (se 1 (by rfl) ⟨432965, by rfl⟩ : syracuseStep 577287 = 865931) B865931
theorem B577295 : Blo 574812 577295 := bstep (se 1 (by rfl) ⟨432971, by rfl⟩ : syracuseStep 577295 = 865943) B865943
theorem B970555 : Blo 574812 970555 := bstep (se 1 (by rfl) ⟨727916, by rfl⟩ : syracuseStep 970555 = 1455833) B1455833
theorem B577339 : Blo 574812 577339 := bstep (se 1 (by rfl) ⟨433004, by rfl⟩ : syracuseStep 577339 = 866009) B866009
theorem B577415 : Blo 574812 577415 := bstep (se 1 (by rfl) ⟨433061, by rfl⟩ : syracuseStep 577415 = 866123) B866123
theorem B1462151 : Blo 574812 1462151 := bstep (se 1 (by rfl) ⟨1096613, by rfl⟩ : syracuseStep 1462151 = 2193227) B2193227
theorem B577423 : Blo 574812 577423 := bstep (se 1 (by rfl) ⟨433067, by rfl⟩ : syracuseStep 577423 = 866135) B866135
theorem B1560505 : Blo 574812 1560505 := bstep (se 2 (by rfl) ⟨585189, by rfl⟩ : syracuseStep 1560505 = 1170379) B1170379
theorem B577467 : Blo 574812 577467 := bstep (se 1 (by rfl) ⟨433100, by rfl⟩ : syracuseStep 577467 = 866201) B866201
theorem B970697 : Blo 574812 970697 := bstep (se 2 (by rfl) ⟨364011, by rfl⟩ : syracuseStep 970697 = 728023) B728023
theorem B577543 : Blo 574812 577543 := bstep (se 1 (by rfl) ⟨433157, by rfl⟩ : syracuseStep 577543 = 866315) B866315
theorem B1462283 : Blo 574812 1462283 := bstep (se 1 (by rfl) ⟨1096712, by rfl⟩ : syracuseStep 1462283 = 2193425) B2193425
theorem B3952651 : Blo 574812 3952651 := bstep (se 1 (by rfl) ⟨2964488, by rfl⟩ : syracuseStep 3952651 = 5928977) B5928977
theorem B1298447 : Blo 574812 1298447 := bstep (se 1 (by rfl) ⟨973835, by rfl⟩ : syracuseStep 1298447 = 1947671) B1947671
theorem B577551 : Blo 574812 577551 := bstep (se 1 (by rfl) ⟨433163, by rfl⟩ : syracuseStep 577551 = 866327) B866327
theorem B1298465 : Blo 574812 1298465 := bstep (se 2 (by rfl) ⟨486924, by rfl⟩ : syracuseStep 1298465 = 973849) B973849
theorem B577595 : Blo 574812 577595 := bstep (se 1 (by rfl) ⟨433196, by rfl⟩ : syracuseStep 577595 = 866393) B866393
theorem B4444247 : Blo 574812 4444247 := bstep (se 1 (by rfl) ⟨3333185, by rfl⟩ : syracuseStep 4444247 = 6666371) B6666371
theorem B577671 : Blo 574812 577671 := bstep (se 1 (by rfl) ⟨433253, by rfl⟩ : syracuseStep 577671 = 866507) B866507
theorem B577679 : Blo 574812 577679 := bstep (se 1 (by rfl) ⟨433259, by rfl⟩ : syracuseStep 577679 = 866519) B866519
theorem B577723 : Blo 574812 577723 := bstep (se 1 (by rfl) ⟨433292, by rfl⟩ : syracuseStep 577723 = 866585) B866585
theorem B577799 : Blo 574812 577799 := bstep (se 1 (by rfl) ⟨433349, by rfl⟩ : syracuseStep 577799 = 866699) B866699
theorem B1036559 : Blo 574812 1036559 := bstep (se 1 (by rfl) ⟨777419, by rfl⟩ : syracuseStep 1036559 = 1554839) B1554839
theorem B577807 : Blo 574812 577807 := bstep (se 1 (by rfl) ⟨433355, by rfl⟩ : syracuseStep 577807 = 866711) B866711
theorem B577851 : Blo 574812 577851 := bstep (se 1 (by rfl) ⟨433388, by rfl⟩ : syracuseStep 577851 = 866777) B866777
theorem B1298807 : Blo 574812 1298807 := bstep (se 1 (by rfl) ⟨974105, by rfl⟩ : syracuseStep 1298807 = 1948211) B1948211
theorem B577927 : Blo 574812 577927 := bstep (se 1 (by rfl) ⟨433445, by rfl⟩ : syracuseStep 577927 = 866891) B866891
theorem B577935 : Blo 574812 577935 := bstep (se 1 (by rfl) ⟨433451, by rfl⟩ : syracuseStep 577935 = 866903) B866903
theorem B577979 : Blo 574812 577979 := bstep (se 1 (by rfl) ⟨433484, by rfl⟩ : syracuseStep 577979 = 866969) B866969
theorem B578055 : Blo 574812 578055 := bstep (se 1 (by rfl) ⟨433541, by rfl⟩ : syracuseStep 578055 = 867083) B867083
theorem B1462799 : Blo 574812 1462799 := bstep (se 1 (by rfl) ⟨1097099, by rfl⟩ : syracuseStep 1462799 = 2194199) B2194199
theorem B578063 : Blo 574812 578063 := bstep (se 1 (by rfl) ⟨433547, by rfl⟩ : syracuseStep 578063 = 867095) B867095
theorem B1298987 : Blo 574812 1298987 := bstep (se 1 (by rfl) ⟨974240, by rfl⟩ : syracuseStep 1298987 = 1948481) B1948481
theorem B578107 : Blo 574812 578107 := bstep (se 1 (by rfl) ⟨433580, by rfl⟩ : syracuseStep 578107 = 867161) B867161
theorem B971399 : Blo 574812 971399 := bstep (se 1 (by rfl) ⟨728549, by rfl⟩ : syracuseStep 971399 = 1457099) B1457099
theorem B578183 : Blo 574812 578183 := bstep (se 1 (by rfl) ⟨433637, by rfl⟩ : syracuseStep 578183 = 867275) B867275
theorem B578191 : Blo 574812 578191 := bstep (se 1 (by rfl) ⟨433643, by rfl⟩ : syracuseStep 578191 = 867287) B867287
theorem B1462931 : Blo 574812 1462931 := bstep (se 1 (by rfl) ⟨1097198, by rfl⟩ : syracuseStep 1462931 = 2194397) B2194397
theorem B578235 : Blo 574812 578235 := bstep (se 1 (by rfl) ⟨433676, by rfl⟩ : syracuseStep 578235 = 867353) B867353
theorem B11096837 : Blo 574812 11096837 := bstep (se 4 (by rfl) ⟨1040328, by rfl⟩ : syracuseStep 11096837 = 2080657) B2080657
theorem B578311 : Blo 574812 578311 := bstep (se 1 (by rfl) ⟨433733, by rfl⟩ : syracuseStep 578311 = 867467) B867467
theorem B578319 : Blo 574812 578319 := bstep (se 1 (by rfl) ⟨433739, by rfl⟩ : syracuseStep 578319 = 867479) B867479
theorem B578363 : Blo 574812 578363 := bstep (se 1 (by rfl) ⟨433772, by rfl⟩ : syracuseStep 578363 = 867545) B867545
theorem B578439 : Blo 574812 578439 := bstep (se 1 (by rfl) ⟨433829, by rfl⟩ : syracuseStep 578439 = 867659) B867659
theorem B578447 : Blo 574812 578447 := bstep (se 1 (by rfl) ⟨433835, by rfl⟩ : syracuseStep 578447 = 867671) B867671
theorem B1299347 : Blo 574812 1299347 := bstep (se 1 (by rfl) ⟨974510, by rfl⟩ : syracuseStep 1299347 = 1949021) B1949021
theorem B2675641 : Blo 574812 2675641 := bstep (se 2 (by rfl) ⟨1003365, by rfl⟩ : syracuseStep 2675641 = 2006731) B2006731
theorem B578491 : Blo 574812 578491 := bstep (se 1 (by rfl) ⟨433868, by rfl⟩ : syracuseStep 578491 = 867737) B867737
theorem B1299401 : Blo 574812 1299401 := bstep (se 2 (by rfl) ⟨487275, by rfl⟩ : syracuseStep 1299401 = 974551) B974551
theorem B578567 : Blo 574812 578567 := bstep (se 1 (by rfl) ⟨433925, by rfl⟩ : syracuseStep 578567 = 867851) B867851
theorem B578575 : Blo 574812 578575 := bstep (se 1 (by rfl) ⟨433931, by rfl⟩ : syracuseStep 578575 = 867863) B867863
theorem B578619 : Blo 574812 578619 := bstep (se 1 (by rfl) ⟨433964, by rfl⟩ : syracuseStep 578619 = 867929) B867929
theorem B578695 : Blo 574812 578695 := bstep (se 1 (by rfl) ⟨434021, by rfl⟩ : syracuseStep 578695 = 868043) B868043
theorem B578703 : Blo 574812 578703 := bstep (se 1 (by rfl) ⟨434027, by rfl⟩ : syracuseStep 578703 = 868055) B868055
theorem B578747 : Blo 574812 578747 := bstep (se 1 (by rfl) ⟨434060, by rfl⟩ : syracuseStep 578747 = 868121) B868121
theorem B1561801 : Blo 574812 1561801 := bstep (se 2 (by rfl) ⟨585675, by rfl⟩ : syracuseStep 1561801 = 1171351) B1171351
theorem B972047 : Blo 574812 972047 := bstep (se 1 (by rfl) ⟨729035, by rfl⟩ : syracuseStep 972047 = 1458071) B1458071
theorem B4150561 : Blo 574812 4150561 := bstep (se 2 (by rfl) ⟨1556460, by rfl⟩ : syracuseStep 4150561 = 3112921) B3112921
theorem B47502733 : Blo 574812 47502733 := bstep (se 3 (by rfl) ⟨8906762, by rfl⟩ : syracuseStep 47502733 = 17813525) B17813525
theorem B1300103 : Blo 574812 1300103 := bstep (se 1 (by rfl) ⟨975077, by rfl⟩ : syracuseStep 1300103 = 1950155) B1950155
theorem B23025329 : Blo 574812 23025329 := bstep (se 2 (by rfl) ⟨8634498, by rfl⟩ : syracuseStep 23025329 = 17268997) B17268997
theorem B1464065 : Blo 574812 1464065 := bstep (se 2 (by rfl) ⟨549024, by rfl⟩ : syracuseStep 1464065 = 1098049) B1098049
theorem B972587 : Blo 574812 972587 := bstep (se 1 (by rfl) ⟨729440, by rfl⟩ : syracuseStep 972587 = 1458881) B1458881
theorem B2774843 : Blo 574812 2774843 := bstep (se 1 (by rfl) ⟨2081132, by rfl⟩ : syracuseStep 2774843 = 4162265) B4162265
theorem B1300283 : Blo 574812 1300283 := bstep (se 1 (by rfl) ⟨975212, by rfl⟩ : syracuseStep 1300283 = 1950425) B1950425
theorem B1562429 : Blo 574812 1562429 := bstep (se 3 (by rfl) ⟨292955, by rfl⟩ : syracuseStep 1562429 = 585911) B585911
theorem B8312651 : Blo 574812 8312651 := bstep (se 1 (by rfl) ⟨6234488, by rfl⟩ : syracuseStep 8312651 = 12468977) B12468977
theorem B1300409 : Blo 574812 1300409 := bstep (se 2 (by rfl) ⟨487653, by rfl⟩ : syracuseStep 1300409 = 975307) B975307
theorem B1562743 : Blo 574812 1562743 := bstep (se 1 (by rfl) ⟨1172057, by rfl⟩ : syracuseStep 1562743 = 2344115) B2344115
theorem B1464439 : Blo 574812 1464439 := bstep (se 1 (by rfl) ⟨1098329, by rfl⟩ : syracuseStep 1464439 = 2196659) B2196659
theorem B972985 : Blo 574812 972985 := bstep (se 2 (by rfl) ⟨364869, by rfl⟩ : syracuseStep 972985 = 729739) B729739
theorem B1300751 : Blo 574812 1300751 := bstep (se 1 (by rfl) ⟨975563, by rfl⟩ : syracuseStep 1300751 = 1951127) B1951127
theorem B1300769 : Blo 574812 1300769 := bstep (se 2 (by rfl) ⟨487788, by rfl⟩ : syracuseStep 1300769 = 975577) B975577
theorem B5560721 : Blo 574812 5560721 := bstep (se 2 (by rfl) ⟨2085270, by rfl⟩ : syracuseStep 5560721 = 4170541) B4170541
theorem B1464875 : Blo 574812 1464875 := bstep (se 1 (by rfl) ⟨1098656, by rfl⟩ : syracuseStep 1464875 = 2197313) B2197313
theorem B3496535 : Blo 574812 3496535 := bstep (se 1 (by rfl) ⟨2622401, by rfl⟩ : syracuseStep 3496535 = 5244803) B5244803
theorem B1301111 : Blo 574812 1301111 := bstep (se 1 (by rfl) ⟨975833, by rfl⟩ : syracuseStep 1301111 = 1951667) B1951667
theorem B1301291 : Blo 574812 1301291 := bstep (se 1 (by rfl) ⟨975968, by rfl⟩ : syracuseStep 1301291 = 1951937) B1951937
theorem B973687 : Blo 574812 973687 := bstep (se 1 (by rfl) ⟨730265, by rfl⟩ : syracuseStep 973687 = 1460531) B1460531
theorem B3562393 : Blo 574812 3562393 := bstep (se 2 (by rfl) ⟨1335897, by rfl⟩ : syracuseStep 3562393 = 2671795) B2671795
theorem B3496925 : Blo 574812 3496925 := bstep (se 3 (by rfl) ⟨655673, by rfl⟩ : syracuseStep 3496925 = 1311347) B1311347
theorem B973883 : Blo 574812 973883 := bstep (se 1 (by rfl) ⟨730412, by rfl⟩ : syracuseStep 973883 = 1460825) B1460825
theorem B1301651 : Blo 574812 1301651 := bstep (se 1 (by rfl) ⟨976238, by rfl⟩ : syracuseStep 1301651 = 1952477) B1952477
theorem B1301705 : Blo 574812 1301705 := bstep (se 2 (by rfl) ⟨488139, by rfl⟩ : syracuseStep 1301705 = 976279) B976279
theorem B6643129 : Blo 574812 6643129 := bstep (se 2 (by rfl) ⟨2491173, by rfl⟩ : syracuseStep 6643129 = 4982347) B4982347
theorem B974281 : Blo 574812 974281 := bstep (se 2 (by rfl) ⟨365355, by rfl⟩ : syracuseStep 974281 = 730711) B730711
theorem B646843 : Blo 574812 646843 := bstep (se 1 (by rfl) ⟨485132, by rfl⟩ : syracuseStep 646843 = 970265) B970265
theorem B974983 : Blo 574812 974983 := bstep (se 1 (by rfl) ⟨731237, by rfl⟩ : syracuseStep 974983 = 1462475) B1462475
theorem B647311 : Blo 574812 647311 := bstep (se 1 (by rfl) ⟨485483, by rfl⟩ : syracuseStep 647311 = 970967) B970967
theorem B2777611 : Blo 574812 2777611 := bstep (se 1 (by rfl) ⟨2083208, by rfl⟩ : syracuseStep 2777611 = 4166417) B4166417
theorem B877115 : Blo 574812 877115 := bstep (se 1 (by rfl) ⟨657836, by rfl⟩ : syracuseStep 877115 = 1315673) B1315673
theorem B4153933 : Blo 574812 4153933 := bstep (se 3 (by rfl) ⟨778862, by rfl⟩ : syracuseStep 4153933 = 1557725) B1557725
theorem B647815 : Blo 574812 647815 := bstep (se 1 (by rfl) ⟨485861, by rfl⟩ : syracuseStep 647815 = 971723) B971723
theorem B975631 : Blo 574812 975631 := bstep (se 1 (by rfl) ⟨731723, by rfl⟩ : syracuseStep 975631 = 1463447) B1463447
theorem B647995 : Blo 574812 647995 := bstep (se 1 (by rfl) ⟨485996, by rfl⟩ : syracuseStep 647995 = 971993) B971993
theorem B877711 : Blo 574812 877711 := bstep (se 1 (by rfl) ⟨658283, by rfl⟩ : syracuseStep 877711 = 1316567) B1316567
theorem B1664201 : Blo 574812 1664201 := bstep (se 2 (by rfl) ⟨624075, by rfl⟩ : syracuseStep 1664201 = 1248151) B1248151
theorem B648463 : Blo 574812 648463 := bstep (se 1 (by rfl) ⟨486347, by rfl⟩ : syracuseStep 648463 = 972695) B972695
theorem B976171 : Blo 574812 976171 := bstep (se 1 (by rfl) ⟨732128, by rfl⟩ : syracuseStep 976171 = 1464257) B1464257
theorem B976313 : Blo 574812 976313 := bstep (se 2 (by rfl) ⟨366117, by rfl⟩ : syracuseStep 976313 = 732235) B732235
theorem B6219521 : Blo 574812 6219521 := bstep (se 2 (by rfl) ⟨2332320, by rfl⟩ : syracuseStep 6219521 = 4664641) B4664641
theorem B648967 : Blo 574812 648967 := bstep (se 1 (by rfl) ⟨486725, by rfl⟩ : syracuseStep 648967 = 973451) B973451
theorem B649147 : Blo 574812 649147 := bstep (se 1 (by rfl) ⟨486860, by rfl⟩ : syracuseStep 649147 = 973721) B973721
theorem B3008477 : Blo 574812 3008477 := bstep (se 3 (by rfl) ⟨564089, by rfl⟩ : syracuseStep 3008477 = 1128179) B1128179
theorem B649615 : Blo 574812 649615 := bstep (se 1 (by rfl) ⟨487211, by rfl⟩ : syracuseStep 649615 = 974423) B974423
theorem B1043003 : Blo 574812 1043003 := bstep (se 1 (by rfl) ⟨782252, by rfl⟩ : syracuseStep 1043003 = 1564505) B1564505
theorem B2910977 : Blo 574812 2910977 := bstep (se 2 (by rfl) ⟨1091616, by rfl⟩ : syracuseStep 2910977 = 2183233) B2183233
theorem B650119 : Blo 574812 650119 := bstep (se 1 (by rfl) ⟨487589, by rfl⟩ : syracuseStep 650119 = 975179) B975179
theorem B650299 : Blo 574812 650299 := bstep (se 1 (by rfl) ⟨487724, by rfl⟩ : syracuseStep 650299 = 975449) B975449
theorem B650767 : Blo 574812 650767 := bstep (se 1 (by rfl) ⟨488075, by rfl⟩ : syracuseStep 650767 = 976151) B976151
theorem B2911787 : Blo 574812 2911787 := bstep (se 1 (by rfl) ⟨2183840, by rfl⟩ : syracuseStep 2911787 = 4367681) B4367681
theorem B1109651 : Blo 574812 1109651 := bstep (se 1 (by rfl) ⟨832238, by rfl⟩ : syracuseStep 1109651 = 1664477) B1664477
theorem B3337985 : Blo 574812 3337985 := bstep (se 2 (by rfl) ⟨1251744, by rfl⟩ : syracuseStep 3337985 = 2503489) B2503489
theorem B2191313 : Blo 574812 2191313 := bstep (se 2 (by rfl) ⟨821742, by rfl⟩ : syracuseStep 2191313 = 1643485) B1643485
theorem B6746503 : Blo 574812 6746503 := bstep (se 1 (by rfl) ⟨5059877, by rfl⟩ : syracuseStep 6746503 = 10119755) B10119755
theorem B2191769 : Blo 574812 2191769 := bstep (se 2 (by rfl) ⟨821913, by rfl⟩ : syracuseStep 2191769 = 1643827) B1643827
theorem B4452893 : Blo 574812 4452893 := bstep (se 3 (by rfl) ⟨834917, by rfl⟩ : syracuseStep 4452893 = 1669835) B1669835
theorem B2913083 : Blo 574812 2913083 := bstep (se 1 (by rfl) ⟨2184812, by rfl⟩ : syracuseStep 2913083 = 4369625) B4369625
theorem B2913245 : Blo 574812 2913245 := bstep (se 3 (by rfl) ⟨546233, by rfl⟩ : syracuseStep 2913245 = 1092467) B1092467
theorem B2913569 : Blo 574812 2913569 := bstep (se 2 (by rfl) ⟨1092588, by rfl⟩ : syracuseStep 2913569 = 2185177) B2185177
theorem B1996217 : Blo 574812 1996217 := bstep (se 2 (by rfl) ⟨748581, by rfl⟩ : syracuseStep 1996217 = 1497163) B1497163
theorem B2192939 : Blo 574812 2192939 := bstep (se 1 (by rfl) ⟨1644704, by rfl⟩ : syracuseStep 2192939 = 3289409) B3289409
theorem B5535539 : Blo 574812 5535539 := bstep (se 1 (by rfl) ⟨4151654, by rfl⟩ : syracuseStep 5535539 = 8303309) B8303309
theorem B4389065 : Blo 574812 4389065 := bstep (se 2 (by rfl) ⟨1645899, by rfl⟩ : syracuseStep 4389065 = 3291799) B3291799
theorem B2914541 : Blo 574812 2914541 := bstep (se 3 (by rfl) ⟨546476, by rfl⟩ : syracuseStep 2914541 = 1092953) B1092953
theorem B3275579 : Blo 574812 3275579 := bstep (se 1 (by rfl) ⟨2456684, by rfl⟩ : syracuseStep 3275579 = 4913369) B4913369
theorem B1604623 : Blo 574812 1604623 := bstep (se 1 (by rfl) ⟨1203467, by rfl⟩ : syracuseStep 1604623 = 2406935) B2406935
theorem B2915351 : Blo 574812 2915351 := bstep (se 1 (by rfl) ⟨2186513, by rfl⟩ : syracuseStep 2915351 = 4373027) B4373027
theorem B2456891 : Blo 574812 2456891 := bstep (se 1 (by rfl) ⟨1842668, by rfl⟩ : syracuseStep 2456891 = 3685337) B3685337
theorem B1637779 : Blo 574812 1637779 := bstep (se 1 (by rfl) ⟨1228334, by rfl⟩ : syracuseStep 1637779 = 2456669) B2456669
theorem B6585785 : Blo 574812 6585785 := bstep (se 2 (by rfl) ⟨2469669, by rfl⟩ : syracuseStep 6585785 = 4939339) B4939339
theorem B818633 : Blo 574812 818633 := bstep (se 2 (by rfl) ⟨306987, by rfl⟩ : syracuseStep 818633 = 613975) B613975
theorem B2194897 : Blo 574812 2194897 := bstep (se 2 (by rfl) ⟨823086, by rfl⟩ : syracuseStep 2194897 = 1646173) B1646173
theorem B5275165 : Blo 574812 5275165 := bstep (se 3 (by rfl) ⟨989093, by rfl⟩ : syracuseStep 5275165 = 1978187) B1978187
theorem B2195201 : Blo 574812 2195201 := bstep (se 2 (by rfl) ⟨823200, by rfl⟩ : syracuseStep 2195201 = 1646401) B1646401
theorem B7372619 : Blo 574812 7372619 := bstep (se 1 (by rfl) ⟨5529464, by rfl⟩ : syracuseStep 7372619 = 11058929) B11058929
theorem B819191 : Blo 574812 819191 := bstep (se 1 (by rfl) ⟨614393, by rfl⟩ : syracuseStep 819191 = 1228787) B1228787
theorem B2195855 : Blo 574812 2195855 := bstep (se 1 (by rfl) ⟨1646891, by rfl⟩ : syracuseStep 2195855 = 3293783) B3293783
theorem B3703481 : Blo 574812 3703481 := bstep (se 2 (by rfl) ⟨1388805, by rfl⟩ : syracuseStep 3703481 = 2777611) B2777611
theorem B1639111 : Blo 574812 1639111 := bstep (se 1 (by rfl) ⟨1229333, by rfl⟩ : syracuseStep 1639111 = 2458667) B2458667
theorem B15958745 : Blo 574812 15958745 := bstep (se 2 (by rfl) ⟨5984529, by rfl⟩ : syracuseStep 15958745 = 11969059) B11969059
theorem B5538577 : Blo 574812 5538577 := bstep (se 2 (by rfl) ⟨2076966, by rfl⟩ : syracuseStep 5538577 = 4153933) B4153933
theorem B6587243 : Blo 574812 6587243 := bstep (se 1 (by rfl) ⟨4940432, by rfl⟩ : syracuseStep 6587243 = 9880865) B9880865
theorem B2917295 : Blo 574812 2917295 := bstep (se 1 (by rfl) ⟨2187971, by rfl⟩ : syracuseStep 2917295 = 4375943) B4375943
theorem B1082299 : Blo 574812 1082299 := bstep (se 1 (by rfl) ⟨811724, by rfl⟩ : syracuseStep 1082299 = 1623449) B1623449
theorem B15762437 : Blo 574812 15762437 := bstep (se 4 (by rfl) ⟨1477728, by rfl⟩ : syracuseStep 15762437 = 2955457) B2955457
theorem B2196841 : Blo 574812 2196841 := bstep (se 2 (by rfl) ⟨823815, by rfl⟩ : syracuseStep 2196841 = 1647631) B1647631
theorem B886235 : Blo 574812 886235 := bstep (se 1 (by rfl) ⟨664676, by rfl⟩ : syracuseStep 886235 = 1329353) B1329353
theorem B8881649 : Blo 574812 8881649 := bstep (se 2 (by rfl) ⟨3330618, by rfl⟩ : syracuseStep 8881649 = 6661237) B6661237
theorem B2197115 : Blo 574812 2197115 := bstep (se 1 (by rfl) ⟨1647836, by rfl⟩ : syracuseStep 2197115 = 3295673) B3295673
theorem B1247251 : Blo 574812 1247251 := bstep (se 1 (by rfl) ⟨935438, by rfl⟩ : syracuseStep 1247251 = 1870877) B1870877
theorem B821287 : Blo 574812 821287 := bstep (se 1 (by rfl) ⟨615965, by rfl⟩ : syracuseStep 821287 = 1231931) B1231931
theorem B4491421 : Blo 574812 4491421 := bstep (se 3 (by rfl) ⟨842141, by rfl⟩ : syracuseStep 4491421 = 1684283) B1684283
theorem B1640695 : Blo 574812 1640695 := bstep (se 1 (by rfl) ⟨1230521, by rfl⟩ : syracuseStep 1640695 = 2461043) B2461043
theorem B2459965 : Blo 574812 2459965 := bstep (se 3 (by rfl) ⟨461243, by rfl⟩ : syracuseStep 2459965 = 922487) B922487
theorem B1640969 : Blo 574812 1640969 := bstep (se 2 (by rfl) ⟨615363, by rfl⟩ : syracuseStep 1640969 = 1230727) B1230727
theorem B691039 : Blo 574812 691039 := bstep (se 1 (by rfl) ⟨518279, by rfl⟩ : syracuseStep 691039 = 1036559) B1036559
theorem B920975 : Blo 574812 920975 := bstep (se 1 (by rfl) ⟨690731, by rfl⟩ : syracuseStep 920975 = 1381463) B1381463
theorem B1641971 : Blo 574812 1641971 := bstep (se 1 (by rfl) ⟨1231478, by rfl⟩ : syracuseStep 1641971 = 2462957) B2462957
theorem B5541767 : Blo 574812 5541767 := bstep (se 1 (by rfl) ⟨4156325, by rfl⟩ : syracuseStep 5541767 = 8312651) B8312651
theorem B921527 : Blo 574812 921527 := bstep (se 1 (by rfl) ⟨691145, by rfl⟩ : syracuseStep 921527 = 1382291) B1382291
theorem B1642427 : Blo 574812 1642427 := bstep (se 1 (by rfl) ⟨1231820, by rfl⟩ : syracuseStep 1642427 = 2463641) B2463641
theorem B3707147 : Blo 574812 3707147 := bstep (se 1 (by rfl) ⟨2780360, by rfl⟩ : syracuseStep 3707147 = 5560721) B5560721
theorem B2331023 : Blo 574812 2331023 := bstep (se 1 (by rfl) ⟨1748267, by rfl⟩ : syracuseStep 2331023 = 3496535) B3496535
theorem B2331283 : Blo 574812 2331283 := bstep (se 1 (by rfl) ⟨1748462, by rfl⟩ : syracuseStep 2331283 = 3496925) B3496925
theorem B3281593 : Blo 574812 3281593 := bstep (se 2 (by rfl) ⟨1230597, by rfl⟩ : syracuseStep 3281593 = 2461195) B2461195
theorem B9900755 : Blo 574812 9900755 := bstep (se 1 (by rfl) ⟨7425566, by rfl⟩ : syracuseStep 9900755 = 14851133) B14851133
theorem B1774295 : Blo 574812 1774295 := bstep (se 1 (by rfl) ⟨1330721, by rfl⟩ : syracuseStep 1774295 = 2661443) B2661443
theorem B1643257 : Blo 574812 1643257 := bstep (se 2 (by rfl) ⟨616221, by rfl⟩ : syracuseStep 1643257 = 1232443) B1232443
theorem B4166477 : Blo 574812 4166477 := bstep (se 3 (by rfl) ⟨781214, by rfl⟩ : syracuseStep 4166477 = 1562429) B1562429
theorem B35493065 : Blo 574812 35493065 := bstep (se 2 (by rfl) ⟨13309899, by rfl⟩ : syracuseStep 35493065 = 26619799) B26619799
theorem B2627261 : Blo 574812 2627261 := bstep (se 3 (by rfl) ⟨492611, by rfl⟩ : syracuseStep 2627261 = 985223) B985223
theorem B18749393 : Blo 574812 18749393 := bstep (se 2 (by rfl) ⟨7031022, by rfl⟩ : syracuseStep 18749393 = 14062045) B14062045
theorem B1644715 : Blo 574812 1644715 := bstep (se 1 (by rfl) ⟨1233536, by rfl⟩ : syracuseStep 1644715 = 2467073) B2467073
theorem B1644943 : Blo 574812 1644943 := bstep (se 1 (by rfl) ⟨1233707, by rfl⟩ : syracuseStep 1644943 = 2467415) B2467415
theorem B2005651 : Blo 574812 2005651 := bstep (se 1 (by rfl) ⟨1504238, by rfl⟩ : syracuseStep 2005651 = 3008477) B3008477
theorem B1841849 : Blo 574812 1841849 := bstep (se 2 (by rfl) ⟨690693, by rfl⟩ : syracuseStep 1841849 = 1381387) B1381387
theorem B2628425 : Blo 574812 2628425 := bstep (se 2 (by rfl) ⟨985659, by rfl⟩ : syracuseStep 2628425 = 1971319) B1971319
theorem B11836277 : Blo 574812 11836277 := bstep (se 5 (by rfl) ⟨554825, by rfl⟩ : syracuseStep 11836277 = 1109651) B1109651
theorem B1940651 : Blo 574812 1940651 := bstep (se 1 (by rfl) ⟨1455488, by rfl⟩ : syracuseStep 1940651 = 2910977) B2910977
theorem B924871 : Blo 574812 924871 := bstep (se 1 (by rfl) ⟨693653, by rfl⟩ : syracuseStep 924871 = 1387307) B1387307
theorem B1318135 : Blo 574812 1318135 := bstep (se 1 (by rfl) ⟨988601, by rfl⟩ : syracuseStep 1318135 = 1977203) B1977203
theorem B1383923 : Blo 574812 1383923 := bstep (se 1 (by rfl) ⟨1037942, by rfl⟩ : syracuseStep 1383923 = 2075885) B2075885
theorem B728615 : Blo 574812 728615 := bstep (se 1 (by rfl) ⟨546461, by rfl⟩ : syracuseStep 728615 = 1092923) B1092923
theorem B1646219 : Blo 574812 1646219 := bstep (se 1 (by rfl) ⟨1234664, by rfl⟩ : syracuseStep 1646219 = 2469329) B2469329
theorem B1941191 : Blo 574812 1941191 := bstep (se 1 (by rfl) ⟨1455893, by rfl⟩ : syracuseStep 1941191 = 2911787) B2911787
theorem B2367299 : Blo 574812 2367299 := bstep (se 1 (by rfl) ⟨1775474, by rfl⟩ : syracuseStep 2367299 = 3550949) B3550949
theorem B728939 : Blo 574812 728939 := bstep (se 1 (by rfl) ⟨546704, by rfl⟩ : syracuseStep 728939 = 1093409) B1093409
theorem B1056979 : Blo 574812 1056979 := bstep (se 1 (by rfl) ⟨792734, by rfl⟩ : syracuseStep 1056979 = 1585469) B1585469
theorem B1384847 : Blo 574812 1384847 := bstep (se 1 (by rfl) ⟨1038635, by rfl⟩ : syracuseStep 1384847 = 2077271) B2077271
theorem B1942055 : Blo 574812 1942055 := bstep (se 1 (by rfl) ⟨1456541, by rfl⟩ : syracuseStep 1942055 = 2913083) B2913083
theorem B1843847 : Blo 574812 1843847 := bstep (se 1 (by rfl) ⟨1382885, by rfl⟩ : syracuseStep 1843847 = 2765771) B2765771
theorem B1942163 : Blo 574812 1942163 := bstep (se 1 (by rfl) ⟨1456622, by rfl⟩ : syracuseStep 1942163 = 2913245) B2913245
theorem B1942379 : Blo 574812 1942379 := bstep (se 1 (by rfl) ⟨1456784, by rfl⟩ : syracuseStep 1942379 = 2913569) B2913569
theorem B1942433 : Blo 574812 1942433 := bstep (se 2 (by rfl) ⟨728412, by rfl⟩ : syracuseStep 1942433 = 1456825) B1456825
theorem B6235055 : Blo 574812 6235055 := bstep (se 1 (by rfl) ⟨4676291, by rfl⟩ : syracuseStep 6235055 = 9352583) B9352583
theorem B730235 : Blo 574812 730235 := bstep (se 1 (by rfl) ⟨547676, by rfl⟩ : syracuseStep 730235 = 1095353) B1095353
theorem B927049 : Blo 574812 927049 := bstep (se 2 (by rfl) ⟨347643, by rfl⟩ : syracuseStep 927049 = 695287) B695287
theorem B2139497 : Blo 574812 2139497 := bstep (se 2 (by rfl) ⟨802311, by rfl⟩ : syracuseStep 2139497 = 1604623) B1604623
theorem B2926043 : Blo 574812 2926043 := bstep (se 1 (by rfl) ⟨2194532, by rfl⟩ : syracuseStep 2926043 = 4389065) B4389065
theorem B1943027 : Blo 574812 1943027 := bstep (se 1 (by rfl) ⟨1457270, by rfl⟩ : syracuseStep 1943027 = 2914541) B2914541
theorem B1844795 : Blo 574812 1844795 := bstep (se 1 (by rfl) ⟨1383596, by rfl⟩ : syracuseStep 1844795 = 2767193) B2767193
theorem B2762387 : Blo 574812 2762387 := bstep (se 1 (by rfl) ⟨2071790, by rfl⟩ : syracuseStep 2762387 = 4143581) B4143581
theorem B8857505 : Blo 574812 8857505 := bstep (se 2 (by rfl) ⟨3321564, by rfl⟩ : syracuseStep 8857505 = 6643129) B6643129
theorem B2926529 : Blo 574812 2926529 := bstep (se 2 (by rfl) ⟨1097448, by rfl⟩ : syracuseStep 2926529 = 2194897) B2194897
theorem B1943567 : Blo 574812 1943567 := bstep (se 1 (by rfl) ⟨1457675, by rfl⟩ : syracuseStep 1943567 = 2915351) B2915351
theorem B862247 : Blo 574812 862247 := bstep (se 1 (by rfl) ⟨646685, by rfl⟩ : syracuseStep 862247 = 1293371) B1293371
theorem B862331 : Blo 574812 862331 := bstep (se 1 (by rfl) ⟨646748, by rfl⟩ : syracuseStep 862331 = 1293497) B1293497
theorem B862457 : Blo 574812 862457 := bstep (se 2 (by rfl) ⟨323421, by rfl⟩ : syracuseStep 862457 = 646843) B646843
theorem B4663603 : Blo 574812 4663603 := bstep (se 1 (by rfl) ⟨3497702, by rfl⟩ : syracuseStep 4663603 = 6995405) B6995405
theorem B862559 : Blo 574812 862559 := bstep (se 1 (by rfl) ⟨646919, by rfl⟩ : syracuseStep 862559 = 1293839) B1293839
theorem B862571 : Blo 574812 862571 := bstep (se 1 (by rfl) ⟨646928, by rfl⟩ : syracuseStep 862571 = 1293857) B1293857
theorem B3287425 : Blo 574812 3287425 := bstep (se 2 (by rfl) ⟨1232784, by rfl⟩ : syracuseStep 3287425 = 2465569) B2465569
theorem B862799 : Blo 574812 862799 := bstep (se 1 (by rfl) ⟨647099, by rfl⟩ : syracuseStep 862799 = 1294199) B1294199
theorem B1944161 : Blo 574812 1944161 := bstep (se 2 (by rfl) ⟨729060, by rfl⟩ : syracuseStep 1944161 = 1458121) B1458121
theorem B1845949 : Blo 574812 1845949 := bstep (se 3 (by rfl) ⟨346115, by rfl⟩ : syracuseStep 1845949 = 692231) B692231
theorem B862919 : Blo 574812 862919 := bstep (se 1 (by rfl) ⟨647189, by rfl⟩ : syracuseStep 862919 = 1294379) B1294379
theorem B863081 : Blo 574812 863081 := bstep (se 2 (by rfl) ⟨323655, by rfl⟩ : syracuseStep 863081 = 647311) B647311
theorem B863159 : Blo 574812 863159 := bstep (se 1 (by rfl) ⟨647369, by rfl⟩ : syracuseStep 863159 = 1294739) B1294739
theorem B863195 : Blo 574812 863195 := bstep (se 1 (by rfl) ⟨647396, by rfl⟩ : syracuseStep 863195 = 1294793) B1294793
theorem B1092665 : Blo 574812 1092665 := bstep (se 2 (by rfl) ⟨409749, by rfl⟩ : syracuseStep 1092665 = 819499) B819499
theorem B1093007 : Blo 574812 1093007 := bstep (se 1 (by rfl) ⟨819755, by rfl⟩ : syracuseStep 1093007 = 1639511) B1639511
theorem B863663 : Blo 574812 863663 := bstep (se 1 (by rfl) ⟨647747, by rfl⟩ : syracuseStep 863663 = 1295495) B1295495
theorem B863753 : Blo 574812 863753 := bstep (se 2 (by rfl) ⟨323907, by rfl⟩ : syracuseStep 863753 = 647815) B647815
theorem B863783 : Blo 574812 863783 := bstep (se 1 (by rfl) ⟨647837, by rfl⟩ : syracuseStep 863783 = 1295675) B1295675
theorem B863867 : Blo 574812 863867 := bstep (se 1 (by rfl) ⟨647900, by rfl⟩ : syracuseStep 863867 = 1295801) B1295801
theorem B863993 : Blo 574812 863993 := bstep (se 2 (by rfl) ⟨323997, by rfl⟩ : syracuseStep 863993 = 647995) B647995
theorem B864095 : Blo 574812 864095 := bstep (se 1 (by rfl) ⟨648071, by rfl⟩ : syracuseStep 864095 = 1296143) B1296143
theorem B864107 : Blo 574812 864107 := bstep (se 1 (by rfl) ⟨648080, by rfl⟩ : syracuseStep 864107 = 1296161) B1296161
theorem B1945619 : Blo 574812 1945619 := bstep (se 1 (by rfl) ⟨1459214, by rfl⟩ : syracuseStep 1945619 = 2918429) B2918429
theorem B864335 : Blo 574812 864335 := bstep (se 1 (by rfl) ⟨648251, by rfl⟩ : syracuseStep 864335 = 1296503) B1296503
theorem B2928797 : Blo 574812 2928797 := bstep (se 3 (by rfl) ⟨549149, by rfl⟩ : syracuseStep 2928797 = 1098299) B1098299
theorem B864455 : Blo 574812 864455 := bstep (se 1 (by rfl) ⟨648341, by rfl⟩ : syracuseStep 864455 = 1296683) B1296683
theorem B1945943 : Blo 574812 1945943 := bstep (se 1 (by rfl) ⟨1459457, by rfl⟩ : syracuseStep 1945943 = 2918915) B2918915
theorem B864617 : Blo 574812 864617 := bstep (se 2 (by rfl) ⟨324231, by rfl⟩ : syracuseStep 864617 = 648463) B648463
theorem B864695 : Blo 574812 864695 := bstep (se 1 (by rfl) ⟨648521, by rfl⟩ : syracuseStep 864695 = 1297043) B1297043
theorem B864731 : Blo 574812 864731 := bstep (se 1 (by rfl) ⟨648548, by rfl⟩ : syracuseStep 864731 = 1297097) B1297097
theorem B2470459 : Blo 574812 2470459 := bstep (se 1 (by rfl) ⟨1852844, by rfl⟩ : syracuseStep 2470459 = 3705689) B3705689
theorem B2765447 : Blo 574812 2765447 := bstep (se 1 (by rfl) ⟨2074085, by rfl⟩ : syracuseStep 2765447 = 4148171) B4148171
theorem B1847947 : Blo 574812 1847947 := bstep (se 1 (by rfl) ⟨1385960, by rfl⟩ : syracuseStep 1847947 = 2771921) B2771921
theorem B2470763 : Blo 574812 2470763 := bstep (se 1 (by rfl) ⟨1853072, by rfl⟩ : syracuseStep 2470763 = 3706145) B3706145
theorem B1455023 : Blo 574812 1455023 := bstep (se 1 (by rfl) ⟨1091267, by rfl⟩ : syracuseStep 1455023 = 2182535) B2182535
theorem B6566831 : Blo 574812 6566831 := bstep (se 1 (by rfl) ⟨4925123, by rfl⟩ : syracuseStep 6566831 = 9850247) B9850247
theorem B865199 : Blo 574812 865199 := bstep (se 1 (by rfl) ⟨648899, by rfl⟩ : syracuseStep 865199 = 1297799) B1297799
theorem B1389575 : Blo 574812 1389575 := bstep (se 1 (by rfl) ⟨1042181, by rfl⟩ : syracuseStep 1389575 = 2084363) B2084363
theorem B865289 : Blo 574812 865289 := bstep (se 2 (by rfl) ⟨324483, by rfl⟩ : syracuseStep 865289 = 648967) B648967
theorem B865319 : Blo 574812 865319 := bstep (se 1 (by rfl) ⟨648989, by rfl⟩ : syracuseStep 865319 = 1297979) B1297979
theorem B865403 : Blo 574812 865403 := bstep (se 1 (by rfl) ⟨649052, by rfl⟩ : syracuseStep 865403 = 1298105) B1298105
theorem B1094867 : Blo 574812 1094867 := bstep (se 1 (by rfl) ⟨821150, by rfl⟩ : syracuseStep 1094867 = 1642301) B1642301
theorem B865529 : Blo 574812 865529 := bstep (se 2 (by rfl) ⟨324573, by rfl⟩ : syracuseStep 865529 = 649147) B649147
theorem B865631 : Blo 574812 865631 := bstep (se 1 (by rfl) ⟨649223, by rfl⟩ : syracuseStep 865631 = 1298447) B1298447
theorem B865643 : Blo 574812 865643 := bstep (se 1 (by rfl) ⟨649232, by rfl⟩ : syracuseStep 865643 = 1298465) B1298465
theorem B1947023 : Blo 574812 1947023 := bstep (se 1 (by rfl) ⟨1460267, by rfl⟩ : syracuseStep 1947023 = 2920535) B2920535
theorem B2962831 : Blo 574812 2962831 := bstep (se 1 (by rfl) ⟨2222123, by rfl⟩ : syracuseStep 2962831 = 4444247) B4444247
theorem B2930093 : Blo 574812 2930093 := bstep (se 3 (by rfl) ⟨549392, by rfl⟩ : syracuseStep 2930093 = 1098785) B1098785
theorem B1095095 : Blo 574812 1095095 := bstep (se 1 (by rfl) ⟨821321, by rfl⟩ : syracuseStep 1095095 = 1642643) B1642643
theorem B1455641 : Blo 574812 1455641 := bstep (se 2 (by rfl) ⟨545865, by rfl⟩ : syracuseStep 1455641 = 1091731) B1091731
theorem B865871 : Blo 574812 865871 := bstep (se 1 (by rfl) ⟨649403, by rfl⟩ : syracuseStep 865871 = 1298807) B1298807
theorem B4372055 : Blo 574812 4372055 := bstep (se 1 (by rfl) ⟨3279041, by rfl⟩ : syracuseStep 4372055 = 6558083) B6558083
theorem B865991 : Blo 574812 865991 := bstep (se 1 (by rfl) ⟨649493, by rfl⟩ : syracuseStep 865991 = 1298987) B1298987
theorem B1947347 : Blo 574812 1947347 := bstep (se 1 (by rfl) ⟨1460510, by rfl⟩ : syracuseStep 1947347 = 2921021) B2921021
theorem B866153 : Blo 574812 866153 := bstep (se 2 (by rfl) ⟨324807, by rfl⟩ : syracuseStep 866153 = 649615) B649615
theorem B2471789 : Blo 574812 2471789 := bstep (se 3 (by rfl) ⟨463460, by rfl⟩ : syracuseStep 2471789 = 926921) B926921
theorem B866231 : Blo 574812 866231 := bstep (se 1 (by rfl) ⟨649673, by rfl⟩ : syracuseStep 866231 = 1299347) B1299347
theorem B866267 : Blo 574812 866267 := bstep (se 1 (by rfl) ⟨649700, by rfl⟩ : syracuseStep 866267 = 1299401) B1299401
theorem B1554817 : Blo 574812 1554817 := bstep (se 2 (by rfl) ⟨583056, by rfl⟩ : syracuseStep 1554817 = 1166113) B1166113
theorem B866735 : Blo 574812 866735 := bstep (se 1 (by rfl) ⟨650051, by rfl⟩ : syracuseStep 866735 = 1300103) B1300103
theorem B15350219 : Blo 574812 15350219 := bstep (se 1 (by rfl) ⟨11512664, by rfl⟩ : syracuseStep 15350219 = 23025329) B23025329
theorem B866825 : Blo 574812 866825 := bstep (se 2 (by rfl) ⟨325059, by rfl⟩ : syracuseStep 866825 = 650119) B650119
theorem B14989859 : Blo 574812 14989859 := bstep (se 1 (by rfl) ⟨11242394, by rfl⟩ : syracuseStep 14989859 = 22484789) B22484789
theorem B1849895 : Blo 574812 1849895 := bstep (se 1 (by rfl) ⟨1387421, by rfl⟩ : syracuseStep 1849895 = 2774843) B2774843
theorem B866855 : Blo 574812 866855 := bstep (se 1 (by rfl) ⟨650141, by rfl⟩ : syracuseStep 866855 = 1300283) B1300283
theorem B1096249 : Blo 574812 1096249 := bstep (se 2 (by rfl) ⟨411093, by rfl⟩ : syracuseStep 1096249 = 822187) B822187
theorem B866939 : Blo 574812 866939 := bstep (se 1 (by rfl) ⟨650204, by rfl⟩ : syracuseStep 866939 = 1300409) B1300409
theorem B867065 : Blo 574812 867065 := bstep (se 2 (by rfl) ⟨325149, by rfl⟩ : syracuseStep 867065 = 650299) B650299
theorem B867167 : Blo 574812 867167 := bstep (se 1 (by rfl) ⟨650375, by rfl⟩ : syracuseStep 867167 = 1300751) B1300751
theorem B1096553 : Blo 574812 1096553 := bstep (se 2 (by rfl) ⟨411207, by rfl⟩ : syracuseStep 1096553 = 822415) B822415
theorem B867179 : Blo 574812 867179 := bstep (se 1 (by rfl) ⟨650384, by rfl⟩ : syracuseStep 867179 = 1300769) B1300769
theorem B2112365 : Blo 574812 2112365 := bstep (se 3 (by rfl) ⟨396068, by rfl⟩ : syracuseStep 2112365 = 792137) B792137
theorem B1948535 : Blo 574812 1948535 := bstep (se 1 (by rfl) ⟨1461401, by rfl⟩ : syracuseStep 1948535 = 2922803) B2922803
theorem B1096591 : Blo 574812 1096591 := bstep (se 1 (by rfl) ⟨822443, by rfl⟩ : syracuseStep 1096591 = 1644887) B1644887
theorem B1948751 : Blo 574812 1948751 := bstep (se 1 (by rfl) ⟨1461563, by rfl⟩ : syracuseStep 1948751 = 2923127) B2923127
theorem B867407 : Blo 574812 867407 := bstep (se 1 (by rfl) ⟨650555, by rfl⟩ : syracuseStep 867407 = 1301111) B1301111
theorem B867527 : Blo 574812 867527 := bstep (se 1 (by rfl) ⟨650645, by rfl⟩ : syracuseStep 867527 = 1301291) B1301291
theorem B867689 : Blo 574812 867689 := bstep (se 2 (by rfl) ⟨325383, by rfl⟩ : syracuseStep 867689 = 650767) B650767
theorem B867767 : Blo 574812 867767 := bstep (se 1 (by rfl) ⟨650825, by rfl⟩ : syracuseStep 867767 = 1301651) B1301651
theorem B1949129 : Blo 574812 1949129 := bstep (se 2 (by rfl) ⟨730923, by rfl⟩ : syracuseStep 1949129 = 1461847) B1461847
theorem B867803 : Blo 574812 867803 := bstep (se 1 (by rfl) ⟨650852, by rfl⟩ : syracuseStep 867803 = 1301705) B1301705
theorem B1293947 : Blo 574812 1293947 := bstep (se 1 (by rfl) ⟨970460, by rfl⟩ : syracuseStep 1293947 = 1940921) B1940921
theorem B1949399 : Blo 574812 1949399 := bstep (se 1 (by rfl) ⟨1462049, by rfl⟩ : syracuseStep 1949399 = 2924099) B2924099
theorem B1294073 : Blo 574812 1294073 := bstep (se 2 (by rfl) ⟨485277, by rfl⟩ : syracuseStep 1294073 = 970555) B970555
theorem B2080673 : Blo 574812 2080673 := bstep (se 2 (by rfl) ⟨780252, by rfl⟩ : syracuseStep 2080673 = 1560505) B1560505
theorem B1949615 : Blo 574812 1949615 := bstep (se 1 (by rfl) ⟨1462211, by rfl⟩ : syracuseStep 1949615 = 2924423) B2924423
theorem B1294343 : Blo 574812 1294343 := bstep (se 1 (by rfl) ⟨970757, by rfl⟩ : syracuseStep 1294343 = 1941515) B1941515
theorem B1458233 : Blo 574812 1458233 := bstep (se 2 (by rfl) ⟨546837, by rfl⟩ : syracuseStep 1458233 = 1093675) B1093675
theorem B1294415 : Blo 574812 1294415 := bstep (se 1 (by rfl) ⟨970811, by rfl⟩ : syracuseStep 1294415 = 1941623) B1941623
theorem B1294811 : Blo 574812 1294811 := bstep (se 1 (by rfl) ⟨971108, by rfl⟩ : syracuseStep 1294811 = 1942217) B1942217
theorem B8995337 : Blo 574812 8995337 := bstep (se 2 (by rfl) ⟨3373251, by rfl⟩ : syracuseStep 8995337 = 6746503) B6746503
theorem B1098451 : Blo 574812 1098451 := bstep (se 1 (by rfl) ⟨823838, by rfl⟩ : syracuseStep 1098451 = 1647677) B1647677
theorem B1295279 : Blo 574812 1295279 := bstep (se 1 (by rfl) ⟨971459, by rfl⟩ : syracuseStep 1295279 = 1942919) B1942919
theorem B1098679 : Blo 574812 1098679 := bstep (se 1 (by rfl) ⟨824009, by rfl⟩ : syracuseStep 1098679 = 1648019) B1648019
theorem B4146347 : Blo 574812 4146347 := bstep (se 1 (by rfl) ⟨3109760, by rfl⟩ : syracuseStep 4146347 = 6219521) B6219521
theorem B1295531 : Blo 574812 1295531 := bstep (se 1 (by rfl) ⟨971648, by rfl⟩ : syracuseStep 1295531 = 1943297) B1943297
theorem B574815 : Blo 574812 574815 := bstep (se 1 (by rfl) ⟨431111, by rfl⟩ : syracuseStep 574815 = 862223) B862223
theorem B574843 : Blo 574812 574843 := bstep (se 1 (by rfl) ⟨431132, by rfl⟩ : syracuseStep 574843 = 862265) B862265
theorem B574895 : Blo 574812 574895 := bstep (se 1 (by rfl) ⟨431171, by rfl⟩ : syracuseStep 574895 = 862343) B862343
theorem B574919 : Blo 574812 574919 := bstep (se 1 (by rfl) ⟨431189, by rfl⟩ : syracuseStep 574919 = 862379) B862379
theorem B574939 : Blo 574812 574939 := bstep (se 1 (by rfl) ⟨431204, by rfl⟩ : syracuseStep 574939 = 862409) B862409
theorem B1459721 : Blo 574812 1459721 := bstep (se 2 (by rfl) ⟨547395, by rfl⟩ : syracuseStep 1459721 = 1094791) B1094791
theorem B575015 : Blo 574812 575015 := bstep (se 1 (by rfl) ⟨431261, by rfl⟩ : syracuseStep 575015 = 862523) B862523
theorem B2082343 : Blo 574812 2082343 := bstep (se 1 (by rfl) ⟨1561757, by rfl⟩ : syracuseStep 2082343 = 3123515) B3123515
theorem B7390763 : Blo 574812 7390763 := bstep (se 1 (by rfl) ⟨5543072, by rfl⟩ : syracuseStep 7390763 = 11086145) B11086145
theorem B575055 : Blo 574812 575055 := bstep (se 1 (by rfl) ⟨431291, by rfl⟩ : syracuseStep 575055 = 862583) B862583
theorem B575071 : Blo 574812 575071 := bstep (se 1 (by rfl) ⟨431303, by rfl⟩ : syracuseStep 575071 = 862607) B862607
theorem B2082401 : Blo 574812 2082401 := bstep (se 2 (by rfl) ⟨780900, by rfl⟩ : syracuseStep 2082401 = 1561801) B1561801
theorem B575099 : Blo 574812 575099 := bstep (se 1 (by rfl) ⟨431324, by rfl⟩ : syracuseStep 575099 = 862649) B862649
theorem B575151 : Blo 574812 575151 := bstep (se 1 (by rfl) ⟨431363, by rfl⟩ : syracuseStep 575151 = 862727) B862727
theorem B575175 : Blo 574812 575175 := bstep (se 1 (by rfl) ⟨431381, by rfl⟩ : syracuseStep 575175 = 862763) B862763
theorem B1296071 : Blo 574812 1296071 := bstep (se 1 (by rfl) ⟨972053, by rfl⟩ : syracuseStep 1296071 = 1944107) B1944107
theorem B2082503 : Blo 574812 2082503 := bstep (se 1 (by rfl) ⟨1561877, by rfl⟩ : syracuseStep 2082503 = 3123755) B3123755
theorem B1230547 : Blo 574812 1230547 := bstep (se 1 (by rfl) ⟨922910, by rfl⟩ : syracuseStep 1230547 = 1845821) B1845821
theorem B575195 : Blo 574812 575195 := bstep (se 1 (by rfl) ⟨431396, by rfl⟩ : syracuseStep 575195 = 862793) B862793
theorem B575271 : Blo 574812 575271 := bstep (se 1 (by rfl) ⟨431453, by rfl⟩ : syracuseStep 575271 = 862907) B862907
theorem B575311 : Blo 574812 575311 := bstep (se 1 (by rfl) ⟨431483, by rfl⟩ : syracuseStep 575311 = 862967) B862967
theorem B575327 : Blo 574812 575327 := bstep (se 1 (by rfl) ⟨431495, by rfl⟩ : syracuseStep 575327 = 862991) B862991
theorem B4376429 : Blo 574812 4376429 := bstep (se 3 (by rfl) ⟨820580, by rfl⟩ : syracuseStep 4376429 = 1641161) B1641161
theorem B575355 : Blo 574812 575355 := bstep (se 1 (by rfl) ⟨431516, by rfl⟩ : syracuseStep 575355 = 863033) B863033
theorem B575407 : Blo 574812 575407 := bstep (se 1 (by rfl) ⟨431555, by rfl⟩ : syracuseStep 575407 = 863111) B863111
theorem B575431 : Blo 574812 575431 := bstep (se 1 (by rfl) ⟨431573, by rfl⟩ : syracuseStep 575431 = 863147) B863147
theorem B575451 : Blo 574812 575451 := bstep (se 1 (by rfl) ⟨431588, by rfl⟩ : syracuseStep 575451 = 863177) B863177
theorem B575527 : Blo 574812 575527 := bstep (se 1 (by rfl) ⟨431645, by rfl⟩ : syracuseStep 575527 = 863291) B863291
theorem B575567 : Blo 574812 575567 := bstep (se 1 (by rfl) ⟨431675, by rfl⟩ : syracuseStep 575567 = 863351) B863351
theorem B575583 : Blo 574812 575583 := bstep (se 1 (by rfl) ⟨431687, by rfl⟩ : syracuseStep 575583 = 863375) B863375
theorem B575611 : Blo 574812 575611 := bstep (se 1 (by rfl) ⟨431708, by rfl⟩ : syracuseStep 575611 = 863417) B863417
theorem B575663 : Blo 574812 575663 := bstep (se 1 (by rfl) ⟨431747, by rfl⟩ : syracuseStep 575663 = 863495) B863495
theorem B575687 : Blo 574812 575687 := bstep (se 1 (by rfl) ⟨431765, by rfl⟩ : syracuseStep 575687 = 863531) B863531
theorem B575707 : Blo 574812 575707 := bstep (se 1 (by rfl) ⟨431780, by rfl⟩ : syracuseStep 575707 = 863561) B863561
theorem B1951991 : Blo 574812 1951991 := bstep (se 1 (by rfl) ⟨1463993, by rfl⟩ : syracuseStep 1951991 = 2927987) B2927987
theorem B575783 : Blo 574812 575783 := bstep (se 1 (by rfl) ⟨431837, by rfl⟩ : syracuseStep 575783 = 863675) B863675
theorem B575823 : Blo 574812 575823 := bstep (se 1 (by rfl) ⟨431867, by rfl⟩ : syracuseStep 575823 = 863735) B863735
theorem B575839 : Blo 574812 575839 := bstep (se 1 (by rfl) ⟨431879, by rfl⟩ : syracuseStep 575839 = 863759) B863759
theorem B575867 : Blo 574812 575867 := bstep (se 1 (by rfl) ⟨431900, by rfl⟩ : syracuseStep 575867 = 863801) B863801
theorem B1231247 : Blo 574812 1231247 := bstep (se 1 (by rfl) ⟨923435, by rfl⟩ : syracuseStep 1231247 = 1846871) B1846871
theorem B575919 : Blo 574812 575919 := bstep (se 1 (by rfl) ⟨431939, by rfl⟩ : syracuseStep 575919 = 863879) B863879
theorem B575943 : Blo 574812 575943 := bstep (se 1 (by rfl) ⟨431957, by rfl⟩ : syracuseStep 575943 = 863915) B863915
theorem B575963 : Blo 574812 575963 := bstep (se 1 (by rfl) ⟨431972, by rfl⟩ : syracuseStep 575963 = 863945) B863945
theorem B576039 : Blo 574812 576039 := bstep (se 1 (by rfl) ⟨432029, by rfl⟩ : syracuseStep 576039 = 864059) B864059
theorem B1296935 : Blo 574812 1296935 := bstep (se 1 (by rfl) ⟨972701, by rfl⟩ : syracuseStep 1296935 = 1945403) B1945403
theorem B1952315 : Blo 574812 1952315 := bstep (se 1 (by rfl) ⟨1464236, by rfl⟩ : syracuseStep 1952315 = 2928473) B2928473
theorem B576079 : Blo 574812 576079 := bstep (se 1 (by rfl) ⟨432059, by rfl⟩ : syracuseStep 576079 = 864119) B864119
theorem B576095 : Blo 574812 576095 := bstep (se 1 (by rfl) ⟨432071, by rfl⟩ : syracuseStep 576095 = 864143) B864143
theorem B576123 : Blo 574812 576123 := bstep (se 1 (by rfl) ⟨432092, by rfl⟩ : syracuseStep 576123 = 864185) B864185
theorem B2214535 : Blo 574812 2214535 := bstep (se 1 (by rfl) ⟨1660901, by rfl⟩ : syracuseStep 2214535 = 3321803) B3321803
theorem B1460875 : Blo 574812 1460875 := bstep (se 1 (by rfl) ⟨1095656, by rfl⟩ : syracuseStep 1460875 = 2191313) B2191313
theorem B576175 : Blo 574812 576175 := bstep (se 1 (by rfl) ⟨432131, by rfl⟩ : syracuseStep 576175 = 864263) B864263
theorem B576199 : Blo 574812 576199 := bstep (se 1 (by rfl) ⟨432149, by rfl⟩ : syracuseStep 576199 = 864299) B864299
theorem B576219 : Blo 574812 576219 := bstep (se 1 (by rfl) ⟨432164, by rfl⟩ : syracuseStep 576219 = 864329) B864329
theorem B576295 : Blo 574812 576295 := bstep (se 1 (by rfl) ⟨432221, by rfl⟩ : syracuseStep 576295 = 864443) B864443
theorem B2083657 : Blo 574812 2083657 := bstep (se 2 (by rfl) ⟨781371, by rfl⟩ : syracuseStep 2083657 = 1562743) B1562743
theorem B1952585 : Blo 574812 1952585 := bstep (se 2 (by rfl) ⟨732219, by rfl⟩ : syracuseStep 1952585 = 1464439) B1464439
theorem B576335 : Blo 574812 576335 := bstep (se 1 (by rfl) ⟨432251, by rfl⟩ : syracuseStep 576335 = 864503) B864503
theorem B576351 : Blo 574812 576351 := bstep (se 1 (by rfl) ⟨432263, by rfl⟩ : syracuseStep 576351 = 864527) B864527
theorem B1297259 : Blo 574812 1297259 := bstep (se 1 (by rfl) ⟨972944, by rfl⟩ : syracuseStep 1297259 = 1945889) B1945889
theorem B576379 : Blo 574812 576379 := bstep (se 1 (by rfl) ⟨432284, by rfl⟩ : syracuseStep 576379 = 864569) B864569
theorem B1297313 : Blo 574812 1297313 := bstep (se 2 (by rfl) ⟨486492, by rfl⟩ : syracuseStep 1297313 = 972985) B972985
theorem B1231777 : Blo 574812 1231777 := bstep (se 2 (by rfl) ⟨461916, by rfl⟩ : syracuseStep 1231777 = 923833) B923833
theorem B576431 : Blo 574812 576431 := bstep (se 1 (by rfl) ⟨432323, by rfl⟩ : syracuseStep 576431 = 864647) B864647
theorem B1461179 : Blo 574812 1461179 := bstep (se 1 (by rfl) ⟨1095884, by rfl⟩ : syracuseStep 1461179 = 2191769) B2191769
theorem B576455 : Blo 574812 576455 := bstep (se 1 (by rfl) ⟨432341, by rfl⟩ : syracuseStep 576455 = 864683) B864683
theorem B576475 : Blo 574812 576475 := bstep (se 1 (by rfl) ⟨432356, by rfl⟩ : syracuseStep 576475 = 864713) B864713
theorem B2968595 : Blo 574812 2968595 := bstep (se 1 (by rfl) ⟨2226446, by rfl⟩ : syracuseStep 2968595 = 4452893) B4452893
theorem B576551 : Blo 574812 576551 := bstep (se 1 (by rfl) ⟨432413, by rfl⟩ : syracuseStep 576551 = 864827) B864827
theorem B576591 : Blo 574812 576591 := bstep (se 1 (by rfl) ⟨432443, by rfl⟩ : syracuseStep 576591 = 864887) B864887
theorem B576607 : Blo 574812 576607 := bstep (se 1 (by rfl) ⟨432455, by rfl⟩ : syracuseStep 576607 = 864911) B864911
theorem B576635 : Blo 574812 576635 := bstep (se 1 (by rfl) ⟨432476, by rfl⟩ : syracuseStep 576635 = 864953) B864953
theorem B576687 : Blo 574812 576687 := bstep (se 1 (by rfl) ⟨432515, by rfl⟩ : syracuseStep 576687 = 865031) B865031
theorem B576711 : Blo 574812 576711 := bstep (se 1 (by rfl) ⟨432533, by rfl⟩ : syracuseStep 576711 = 865067) B865067
theorem B576731 : Blo 574812 576731 := bstep (se 1 (by rfl) ⟨432548, by rfl⟩ : syracuseStep 576731 = 865097) B865097
theorem B1297655 : Blo 574812 1297655 := bstep (se 1 (by rfl) ⟨973241, by rfl⟩ : syracuseStep 1297655 = 1946483) B1946483
theorem B576807 : Blo 574812 576807 := bstep (se 1 (by rfl) ⟨432605, by rfl⟩ : syracuseStep 576807 = 865211) B865211
theorem B576847 : Blo 574812 576847 := bstep (se 1 (by rfl) ⟨432635, by rfl⟩ : syracuseStep 576847 = 865271) B865271
theorem B4345177 : Blo 574812 4345177 := bstep (se 2 (by rfl) ⟨1629441, by rfl⟩ : syracuseStep 4345177 = 3258883) B3258883
theorem B576863 : Blo 574812 576863 := bstep (se 1 (by rfl) ⟨432647, by rfl⟩ : syracuseStep 576863 = 865295) B865295
theorem B576891 : Blo 574812 576891 := bstep (se 1 (by rfl) ⟨432668, by rfl⟩ : syracuseStep 576891 = 865337) B865337
theorem B576943 : Blo 574812 576943 := bstep (se 1 (by rfl) ⟨432707, by rfl⟩ : syracuseStep 576943 = 865415) B865415
theorem B576967 : Blo 574812 576967 := bstep (se 1 (by rfl) ⟨432725, by rfl⟩ : syracuseStep 576967 = 865451) B865451
theorem B576987 : Blo 574812 576987 := bstep (se 1 (by rfl) ⟨432740, by rfl⟩ : syracuseStep 576987 = 865481) B865481
theorem B577063 : Blo 574812 577063 := bstep (se 1 (by rfl) ⟨432797, by rfl⟩ : syracuseStep 577063 = 865595) B865595
theorem B970319 : Blo 574812 970319 := bstep (se 1 (by rfl) ⟨727739, by rfl⟩ : syracuseStep 970319 = 1455479) B1455479
theorem B577103 : Blo 574812 577103 := bstep (se 1 (by rfl) ⟨432827, by rfl⟩ : syracuseStep 577103 = 865655) B865655
theorem B577119 : Blo 574812 577119 := bstep (se 1 (by rfl) ⟨432839, by rfl⟩ : syracuseStep 577119 = 865679) B865679
theorem B1330811 : Blo 574812 1330811 := bstep (se 1 (by rfl) ⟨998108, by rfl⟩ : syracuseStep 1330811 = 1996217) B1996217
theorem B577147 : Blo 574812 577147 := bstep (se 1 (by rfl) ⟨432860, by rfl⟩ : syracuseStep 577147 = 865721) B865721
theorem B577199 : Blo 574812 577199 := bstep (se 1 (by rfl) ⟨432899, by rfl⟩ : syracuseStep 577199 = 865799) B865799
theorem B577223 : Blo 574812 577223 := bstep (se 1 (by rfl) ⟨432917, by rfl⟩ : syracuseStep 577223 = 865835) B865835
theorem B1461959 : Blo 574812 1461959 := bstep (se 1 (by rfl) ⟨1096469, by rfl⟩ : syracuseStep 1461959 = 2192939) B2192939
theorem B1756883 : Blo 574812 1756883 := bstep (se 1 (by rfl) ⟨1317662, by rfl⟩ : syracuseStep 1756883 = 2635325) B2635325
theorem B577243 : Blo 574812 577243 := bstep (se 1 (by rfl) ⟨432932, by rfl⟩ : syracuseStep 577243 = 865865) B865865
theorem B1462009 : Blo 574812 1462009 := bstep (se 2 (by rfl) ⟨548253, by rfl⟩ : syracuseStep 1462009 = 1096507) B1096507
theorem B577319 : Blo 574812 577319 := bstep (se 1 (by rfl) ⟨432989, by rfl⟩ : syracuseStep 577319 = 865979) B865979
theorem B1298249 : Blo 574812 1298249 := bstep (se 2 (by rfl) ⟨486843, by rfl⟩ : syracuseStep 1298249 = 973687) B973687
theorem B577359 : Blo 574812 577359 := bstep (se 1 (by rfl) ⟨433019, by rfl⟩ : syracuseStep 577359 = 866039) B866039
theorem B577375 : Blo 574812 577375 := bstep (se 1 (by rfl) ⟨433031, by rfl⟩ : syracuseStep 577375 = 866063) B866063
theorem B2183021 : Blo 574812 2183021 := bstep (se 3 (by rfl) ⟨409316, by rfl⟩ : syracuseStep 2183021 = 818633) B818633
theorem B3690359 : Blo 574812 3690359 := bstep (se 1 (by rfl) ⟨2767769, by rfl⟩ : syracuseStep 3690359 = 5535539) B5535539
theorem B577403 : Blo 574812 577403 := bstep (se 1 (by rfl) ⟨433052, by rfl⟩ : syracuseStep 577403 = 866105) B866105
theorem B577455 : Blo 574812 577455 := bstep (se 1 (by rfl) ⟨433091, by rfl⟩ : syracuseStep 577455 = 866183) B866183
theorem B577479 : Blo 574812 577479 := bstep (se 1 (by rfl) ⟨433109, by rfl⟩ : syracuseStep 577479 = 866219) B866219
theorem B577499 : Blo 574812 577499 := bstep (se 1 (by rfl) ⟨433124, by rfl⟩ : syracuseStep 577499 = 866249) B866249
theorem B577575 : Blo 574812 577575 := bstep (se 1 (by rfl) ⟨433181, by rfl⟩ : syracuseStep 577575 = 866363) B866363
theorem B577615 : Blo 574812 577615 := bstep (se 1 (by rfl) ⟨433211, by rfl⟩ : syracuseStep 577615 = 866423) B866423
theorem B577631 : Blo 574812 577631 := bstep (se 1 (by rfl) ⟨433223, by rfl⟩ : syracuseStep 577631 = 866447) B866447
theorem B577659 : Blo 574812 577659 := bstep (se 1 (by rfl) ⟨433244, by rfl⟩ : syracuseStep 577659 = 866489) B866489
theorem B577711 : Blo 574812 577711 := bstep (se 1 (by rfl) ⟨433283, by rfl⟩ : syracuseStep 577711 = 866567) B866567
theorem B577735 : Blo 574812 577735 := bstep (se 1 (by rfl) ⟨433301, by rfl⟩ : syracuseStep 577735 = 866603) B866603
theorem B577755 : Blo 574812 577755 := bstep (se 1 (by rfl) ⟨433316, by rfl⟩ : syracuseStep 577755 = 866633) B866633
theorem B577831 : Blo 574812 577831 := bstep (se 1 (by rfl) ⟨433373, by rfl⟩ : syracuseStep 577831 = 866747) B866747
theorem B577871 : Blo 574812 577871 := bstep (se 1 (by rfl) ⟨433403, by rfl⟩ : syracuseStep 577871 = 866807) B866807
theorem B577887 : Blo 574812 577887 := bstep (se 1 (by rfl) ⟨433415, by rfl⟩ : syracuseStep 577887 = 866831) B866831
theorem B577915 : Blo 574812 577915 := bstep (se 1 (by rfl) ⟨433436, by rfl⟩ : syracuseStep 577915 = 866873) B866873
theorem B1462657 : Blo 574812 1462657 := bstep (se 2 (by rfl) ⟨548496, by rfl⟩ : syracuseStep 1462657 = 1096993) B1096993
theorem B971183 : Blo 574812 971183 := bstep (se 1 (by rfl) ⟨728387, by rfl⟩ : syracuseStep 971183 = 1456775) B1456775
theorem B577967 : Blo 574812 577967 := bstep (se 1 (by rfl) ⟨433475, by rfl⟩ : syracuseStep 577967 = 866951) B866951
theorem B577991 : Blo 574812 577991 := bstep (se 1 (by rfl) ⟨433493, by rfl⟩ : syracuseStep 577991 = 866987) B866987
theorem B578011 : Blo 574812 578011 := bstep (se 1 (by rfl) ⟨433508, by rfl⟩ : syracuseStep 578011 = 867017) B867017
theorem B2183705 : Blo 574812 2183705 := bstep (se 2 (by rfl) ⟨818889, by rfl⟩ : syracuseStep 2183705 = 1637779) B1637779
theorem B2183719 : Blo 574812 2183719 := bstep (se 1 (by rfl) ⟨1637789, by rfl⟩ : syracuseStep 2183719 = 3275579) B3275579
theorem B578087 : Blo 574812 578087 := bstep (se 1 (by rfl) ⟨433565, by rfl⟩ : syracuseStep 578087 = 867131) B867131
theorem B578127 : Blo 574812 578127 := bstep (se 1 (by rfl) ⟨433595, by rfl⟩ : syracuseStep 578127 = 867191) B867191
theorem B578143 : Blo 574812 578143 := bstep (se 1 (by rfl) ⟨433607, by rfl⟩ : syracuseStep 578143 = 867215) B867215
theorem B1299041 : Blo 574812 1299041 := bstep (se 2 (by rfl) ⟨487140, by rfl⟩ : syracuseStep 1299041 = 974281) B974281
theorem B578171 : Blo 574812 578171 := bstep (se 1 (by rfl) ⟨433628, by rfl⟩ : syracuseStep 578171 = 867257) B867257
theorem B578223 : Blo 574812 578223 := bstep (se 1 (by rfl) ⟨433667, by rfl⟩ : syracuseStep 578223 = 867335) B867335
theorem B578247 : Blo 574812 578247 := bstep (se 1 (by rfl) ⟨433685, by rfl⟩ : syracuseStep 578247 = 867371) B867371
theorem B4379345 : Blo 574812 4379345 := bstep (se 2 (by rfl) ⟨1642254, by rfl⟩ : syracuseStep 4379345 = 3284509) B3284509
theorem B7033553 : Blo 574812 7033553 := bstep (se 2 (by rfl) ⟨2637582, by rfl⟩ : syracuseStep 7033553 = 5275165) B5275165
theorem B578267 : Blo 574812 578267 := bstep (se 1 (by rfl) ⟨433700, by rfl⟩ : syracuseStep 578267 = 867401) B867401
theorem B578343 : Blo 574812 578343 := bstep (se 1 (by rfl) ⟨433757, by rfl⟩ : syracuseStep 578343 = 867515) B867515
theorem B578383 : Blo 574812 578383 := bstep (se 1 (by rfl) ⟨433787, by rfl⟩ : syracuseStep 578383 = 867575) B867575
theorem B971615 : Blo 574812 971615 := bstep (se 1 (by rfl) ⟨728711, by rfl⟩ : syracuseStep 971615 = 1457423) B1457423
theorem B578399 : Blo 574812 578399 := bstep (se 1 (by rfl) ⟨433799, by rfl⟩ : syracuseStep 578399 = 867599) B867599
theorem B578427 : Blo 574812 578427 := bstep (se 1 (by rfl) ⟨433820, by rfl⟩ : syracuseStep 578427 = 867641) B867641
theorem B1168303 : Blo 574812 1168303 := bstep (se 1 (by rfl) ⟨876227, by rfl⟩ : syracuseStep 1168303 = 1752455) B1752455
theorem B578479 : Blo 574812 578479 := bstep (se 1 (by rfl) ⟨433859, by rfl⟩ : syracuseStep 578479 = 867719) B867719
theorem B1299383 : Blo 574812 1299383 := bstep (se 1 (by rfl) ⟨974537, by rfl⟩ : syracuseStep 1299383 = 1949075) B1949075
theorem B578503 : Blo 574812 578503 := bstep (se 1 (by rfl) ⟨433877, by rfl⟩ : syracuseStep 578503 = 867755) B867755
theorem B578523 : Blo 574812 578523 := bstep (se 1 (by rfl) ⟨433892, by rfl⟩ : syracuseStep 578523 = 867785) B867785
theorem B578599 : Blo 574812 578599 := bstep (se 1 (by rfl) ⟨433949, by rfl⟩ : syracuseStep 578599 = 867899) B867899
theorem B578639 : Blo 574812 578639 := bstep (se 1 (by rfl) ⟨433979, by rfl⟩ : syracuseStep 578639 = 867959) B867959
theorem B578655 : Blo 574812 578655 := bstep (se 1 (by rfl) ⟨433991, by rfl⟩ : syracuseStep 578655 = 867983) B867983
theorem B578683 : Blo 574812 578683 := bstep (se 1 (by rfl) ⟨434012, by rfl⟩ : syracuseStep 578683 = 868025) B868025
theorem B1463467 : Blo 574812 1463467 := bstep (se 1 (by rfl) ⟨1097600, by rfl⟩ : syracuseStep 1463467 = 2195201) B2195201
theorem B578735 : Blo 574812 578735 := bstep (se 1 (by rfl) ⟨434051, by rfl⟩ : syracuseStep 578735 = 868103) B868103
theorem B578759 : Blo 574812 578759 := bstep (se 1 (by rfl) ⟨434069, by rfl⟩ : syracuseStep 578759 = 868139) B868139
theorem B578779 : Blo 574812 578779 := bstep (se 1 (by rfl) ⟨434084, by rfl⟩ : syracuseStep 578779 = 868169) B868169
theorem B2184509 : Blo 574812 2184509 := bstep (se 3 (by rfl) ⟨409595, by rfl⟩ : syracuseStep 2184509 = 819191) B819191
theorem B972175 : Blo 574812 972175 := bstep (se 1 (by rfl) ⟨729131, by rfl⟩ : syracuseStep 972175 = 1458263) B1458263
theorem B6575579 : Blo 574812 6575579 := bstep (se 1 (by rfl) ⟨4931684, by rfl⟩ : syracuseStep 6575579 = 9863369) B9863369
theorem B1463771 : Blo 574812 1463771 := bstep (se 1 (by rfl) ⟨1097828, by rfl⟩ : syracuseStep 1463771 = 2195657) B2195657
theorem B2184691 : Blo 574812 2184691 := bstep (se 1 (by rfl) ⟨1638518, by rfl⟩ : syracuseStep 2184691 = 3277037) B3277037
theorem B1299977 : Blo 574812 1299977 := bstep (se 2 (by rfl) ⟨487491, by rfl⟩ : syracuseStep 1299977 = 974983) B974983
theorem B1300319 : Blo 574812 1300319 := bstep (se 1 (by rfl) ⟨975239, by rfl⟩ : syracuseStep 1300319 = 1950479) B1950479
theorem B1300499 : Blo 574812 1300499 := bstep (se 1 (by rfl) ⟨975374, by rfl⟩ : syracuseStep 1300499 = 1950749) B1950749
theorem B6215717 : Blo 574812 6215717 := bstep (se 4 (by rfl) ⟨582723, by rfl⟩ : syracuseStep 6215717 = 1165447) B1165447
theorem B972857 : Blo 574812 972857 := bstep (se 2 (by rfl) ⟨364821, by rfl⟩ : syracuseStep 972857 = 729643) B729643
theorem B1300841 : Blo 574812 1300841 := bstep (se 2 (by rfl) ⟨487815, by rfl⟩ : syracuseStep 1300841 = 975631) B975631
theorem B2251273 : Blo 574812 2251273 := bstep (se 2 (by rfl) ⟨844227, by rfl⟩ : syracuseStep 2251273 = 1688455) B1688455
theorem B1170119 : Blo 574812 1170119 := bstep (se 1 (by rfl) ⟨877589, by rfl⟩ : syracuseStep 1170119 = 1755179) B1755179
theorem B2185937 : Blo 574812 2185937 := bstep (se 2 (by rfl) ⟨819726, by rfl⟩ : syracuseStep 2185937 = 1639453) B1639453
theorem B973559 : Blo 574812 973559 := bstep (se 1 (by rfl) ⟨730169, by rfl⟩ : syracuseStep 973559 = 1460339) B1460339
theorem B3496733 : Blo 574812 3496733 := bstep (se 3 (by rfl) ⟨655637, by rfl⟩ : syracuseStep 3496733 = 1311275) B1311275
theorem B1170281 : Blo 574812 1170281 := bstep (se 2 (by rfl) ⟨438855, by rfl⟩ : syracuseStep 1170281 = 877711) B877711
theorem B1301435 : Blo 574812 1301435 := bstep (se 1 (by rfl) ⟨976076, by rfl⟩ : syracuseStep 1301435 = 1952153) B1952153
theorem B1301561 : Blo 574812 1301561 := bstep (se 2 (by rfl) ⟨488085, by rfl⟩ : syracuseStep 1301561 = 976171) B976171
theorem B4381775 : Blo 574812 4381775 := bstep (se 1 (by rfl) ⟨3286331, by rfl⟩ : syracuseStep 4381775 = 6572663) B6572663
theorem B973903 : Blo 574812 973903 := bstep (se 1 (by rfl) ⟨730427, by rfl⟩ : syracuseStep 973903 = 1460855) B1460855
theorem B974153 : Blo 574812 974153 := bstep (se 2 (by rfl) ⟨365307, by rfl⟩ : syracuseStep 974153 = 730615) B730615
theorem B4742489 : Blo 574812 4742489 := bstep (se 2 (by rfl) ⟨1778433, by rfl⟩ : syracuseStep 4742489 = 3556867) B3556867
theorem B2186621 : Blo 574812 2186621 := bstep (se 3 (by rfl) ⟨409991, by rfl⟩ : syracuseStep 2186621 = 819983) B819983
theorem B1301903 : Blo 574812 1301903 := bstep (se 1 (by rfl) ⟨976427, by rfl⟩ : syracuseStep 1301903 = 1952855) B1952855
theorem B3694025 : Blo 574812 3694025 := bstep (se 2 (by rfl) ⟨1385259, by rfl⟩ : syracuseStep 3694025 = 2770519) B2770519
theorem B646735 : Blo 574812 646735 := bstep (se 1 (by rfl) ⟨485051, by rfl⟩ : syracuseStep 646735 = 970103) B970103
theorem B1302227 : Blo 574812 1302227 := bstep (se 1 (by rfl) ⟨976670, by rfl⟩ : syracuseStep 1302227 = 1953341) B1953341
theorem B974585 : Blo 574812 974585 := bstep (se 2 (by rfl) ⟨365469, by rfl⟩ : syracuseStep 974585 = 730939) B730939
theorem B33185537 : Blo 574812 33185537 := bstep (se 2 (by rfl) ⟨12444576, by rfl⟩ : syracuseStep 33185537 = 24889153) B24889153
theorem B974767 : Blo 574812 974767 := bstep (se 1 (by rfl) ⟨731075, by rfl⟩ : syracuseStep 974767 = 1462151) B1462151
theorem B647131 : Blo 574812 647131 := bstep (se 1 (by rfl) ⟨485348, by rfl⟩ : syracuseStep 647131 = 970697) B970697
theorem B974855 : Blo 574812 974855 := bstep (se 1 (by rfl) ⟨731141, by rfl⟩ : syracuseStep 974855 = 1462283) B1462283
theorem B2187607 : Blo 574812 2187607 := bstep (se 1 (by rfl) ⟨1640705, by rfl⟩ : syracuseStep 2187607 = 3281411) B3281411
theorem B975199 : Blo 574812 975199 := bstep (se 1 (by rfl) ⟨731399, by rfl⟩ : syracuseStep 975199 = 1462799) B1462799
theorem B647599 : Blo 574812 647599 := bstep (se 1 (by rfl) ⟨485699, by rfl⟩ : syracuseStep 647599 = 971399) B971399
theorem B975287 : Blo 574812 975287 := bstep (se 1 (by rfl) ⟨731465, by rfl⟩ : syracuseStep 975287 = 1462931) B1462931
theorem B7397891 : Blo 574812 7397891 := bstep (se 1 (by rfl) ⟨5548418, by rfl⟩ : syracuseStep 7397891 = 11096837) B11096837
theorem B4940297 : Blo 574812 4940297 := bstep (se 2 (by rfl) ⟨1852611, by rfl⟩ : syracuseStep 4940297 = 3705223) B3705223
theorem B2187911 : Blo 574812 2187911 := bstep (se 1 (by rfl) ⟨1640933, by rfl⟩ : syracuseStep 2187911 = 3281867) B3281867
theorem B648031 : Blo 574812 648031 := bstep (se 1 (by rfl) ⟨486023, by rfl⟩ : syracuseStep 648031 = 972047) B972047
theorem B975881 : Blo 574812 975881 := bstep (se 2 (by rfl) ⟨365955, by rfl⟩ : syracuseStep 975881 = 731911) B731911
theorem B2188367 : Blo 574812 2188367 := bstep (se 1 (by rfl) ⟨1641275, by rfl⟩ : syracuseStep 2188367 = 3282551) B3282551
theorem B615547 : Blo 574812 615547 := bstep (se 1 (by rfl) ⟨461660, by rfl⟩ : syracuseStep 615547 = 923321) B923321
theorem B976043 : Blo 574812 976043 := bstep (se 1 (by rfl) ⟨732032, by rfl⟩ : syracuseStep 976043 = 1464065) B1464065
theorem B648391 : Blo 574812 648391 := bstep (se 1 (by rfl) ⟨486293, by rfl⟩ : syracuseStep 648391 = 972587) B972587
theorem B4941323 : Blo 574812 4941323 := bstep (se 1 (by rfl) ⟨3705992, by rfl⟩ : syracuseStep 4941323 = 7411985) B7411985
theorem B976441 : Blo 574812 976441 := bstep (se 2 (by rfl) ⟨366165, by rfl⟩ : syracuseStep 976441 = 732331) B732331
theorem B976583 : Blo 574812 976583 := bstep (se 1 (by rfl) ⟨732437, by rfl⟩ : syracuseStep 976583 = 1464875) B1464875
theorem B976745 : Blo 574812 976745 := bstep (se 2 (by rfl) ⟨366279, by rfl⟩ : syracuseStep 976745 = 732559) B732559
theorem B616367 : Blo 574812 616367 := bstep (se 1 (by rfl) ⟨462275, by rfl⟩ : syracuseStep 616367 = 924551) B924551
theorem B649255 : Blo 574812 649255 := bstep (se 1 (by rfl) ⟨486941, by rfl⟩ : syracuseStep 649255 = 973883) B973883
theorem B2189369 : Blo 574812 2189369 := bstep (se 2 (by rfl) ⟨821013, by rfl⟩ : syracuseStep 2189369 = 1642027) B1642027
theorem B4385177 : Blo 574812 4385177 := bstep (se 2 (by rfl) ⟨1644441, by rfl⟩ : syracuseStep 4385177 = 3288883) B3288883
theorem B3500603 : Blo 574812 3500603 := bstep (se 1 (by rfl) ⟨2625452, by rfl⟩ : syracuseStep 3500603 = 5250905) B5250905
theorem B5270201 : Blo 574812 5270201 := bstep (se 2 (by rfl) ⟨1976325, by rfl⟩ : syracuseStep 5270201 = 3952651) B3952651
theorem B2190023 : Blo 574812 2190023 := bstep (se 1 (by rfl) ⟨1642517, by rfl⟩ : syracuseStep 2190023 = 3285035) B3285035
theorem B617311 : Blo 574812 617311 := bstep (se 1 (by rfl) ⟨462983, by rfl⟩ : syracuseStep 617311 = 925967) B925967
theorem B584743 : Blo 574812 584743 := bstep (se 1 (by rfl) ⟨438557, by rfl⟩ : syracuseStep 584743 = 877115) B877115
theorem B1109467 : Blo 574812 1109467 := bstep (se 1 (by rfl) ⟨832100, by rfl⟩ : syracuseStep 1109467 = 1664201) B1664201
theorem B7892603 : Blo 574812 7892603 := bstep (se 1 (by rfl) ⟨5919452, by rfl⟩ : syracuseStep 7892603 = 11838905) B11838905
theorem B650875 : Blo 574812 650875 := bstep (se 1 (by rfl) ⟨488156, by rfl⟩ : syracuseStep 650875 = 976313) B976313
theorem B2190995 : Blo 574812 2190995 := bstep (se 1 (by rfl) ⟨1643246, by rfl⟩ : syracuseStep 2190995 = 3286493) B3286493
theorem B3567521 : Blo 574812 3567521 := bstep (se 2 (by rfl) ⟨1337820, by rfl⟩ : syracuseStep 3567521 = 2675641) B2675641
theorem B4943987 : Blo 574812 4943987 := bstep (se 1 (by rfl) ⟨3707990, by rfl⟩ : syracuseStep 4943987 = 7415981) B7415981
theorem B2781341 : Blo 574812 2781341 := bstep (se 3 (by rfl) ⟨521501, by rfl⟩ : syracuseStep 2781341 = 1043003) B1043003
theorem B4387121 : Blo 574812 4387121 := bstep (se 2 (by rfl) ⟨1645170, by rfl⟩ : syracuseStep 4387121 = 3290341) B3290341
theorem B5534081 : Blo 574812 5534081 := bstep (se 2 (by rfl) ⟨2075280, by rfl⟩ : syracuseStep 5534081 = 4150561) B4150561
theorem B13332995 : Blo 574812 13332995 := bstep (se 1 (by rfl) ⟨9999746, by rfl⟩ : syracuseStep 13332995 = 19999493) B19999493
theorem B63336977 : Blo 574812 63336977 := bstep (se 2 (by rfl) ⟨23751366, by rfl⟩ : syracuseStep 63336977 = 47502733) B47502733
theorem B2225323 : Blo 574812 2225323 := bstep (se 1 (by rfl) ⟨1668992, by rfl⟩ : syracuseStep 2225323 = 3337985) B3337985
theorem B73037155 : Blo 574812 73037155 := bstep (se 1 (by rfl) ⟨54777866, by rfl⟩ : syracuseStep 73037155 = 109555733) B109555733
theorem B3503837 : Blo 574812 3503837 := bstep (se 3 (by rfl) ⟨656969, by rfl⟩ : syracuseStep 3503837 = 1313939) B1313939
theorem B35452673 : Blo 574812 35452673 := bstep (se 2 (by rfl) ⟨13294752, by rfl⟩ : syracuseStep 35452673 = 26589505) B26589505
theorem B6584327 : Blo 574812 6584327 := bstep (se 1 (by rfl) ⟨4938245, by rfl⟩ : syracuseStep 6584327 = 9876491) B9876491
theorem B6092857 : Blo 574812 6092857 := bstep (se 2 (by rfl) ⟨2284821, by rfl⟩ : syracuseStep 6092857 = 4569643) B4569643
theorem B4749857 : Blo 574812 4749857 := bstep (se 2 (by rfl) ⟨1781196, by rfl⟩ : syracuseStep 4749857 = 3562393) B3562393
theorem B57834163 : Blo 574812 57834163 := bstep (se 1 (by rfl) ⟨43375622, by rfl⟩ : syracuseStep 57834163 = 86751245) B86751245
theorem B2915027 : Blo 574812 2915027 := bstep (se 1 (by rfl) ⟨2186270, by rfl⟩ : syracuseStep 2915027 = 4372541) B4372541
theorem B3111709 : Blo 574812 3111709 := bstep (se 3 (by rfl) ⟨583445, by rfl⟩ : syracuseStep 3111709 = 1166891) B1166891
theorem B4684691 : Blo 574812 4684691 := bstep (se 1 (by rfl) ⟨3513518, by rfl⟩ : syracuseStep 4684691 = 7027037) B7027037
theorem B3505153 : Blo 574812 3505153 := bstep (se 2 (by rfl) ⟨1314432, by rfl⟩ : syracuseStep 3505153 = 2628865) B2628865
theorem B1015031 : Blo 574812 1015031 := bstep (se 1 (by rfl) ⟨761273, by rfl⟩ : syracuseStep 1015031 = 1522547) B1522547
theorem B1637927 : Blo 574812 1637927 := bstep (se 1 (by rfl) ⟨1228445, by rfl⟩ : syracuseStep 1637927 = 2456891) B2456891
theorem B4390523 : Blo 574812 4390523 := bstep (se 1 (by rfl) ⟨3292892, by rfl⟩ : syracuseStep 4390523 = 6585785) B6585785
theorem B3702509 : Blo 574812 3702509 := bstep (se 3 (by rfl) ⟨694220, by rfl⟩ : syracuseStep 3702509 = 1388441) B1388441
theorem B4915079 : Blo 574812 4915079 := bstep (se 1 (by rfl) ⟨3686309, by rfl⟩ : syracuseStep 4915079 = 7372619) B7372619
theorem B2195383 : Blo 574812 2195383 := bstep (se 1 (by rfl) ⟨1646537, by rfl⟩ : syracuseStep 2195383 = 3293075) B3293075
theorem B819163 : Blo 574812 819163 := bstep (se 1 (by rfl) ⟨614372, by rfl⟩ : syracuseStep 819163 = 1228745) B1228745
theorem B5996891 : Blo 574812 5996891 := bstep (se 1 (by rfl) ⟨4497668, by rfl⟩ : syracuseStep 5996891 = 8995337) B8995337
theorem B2916809 : Blo 574812 2916809 := bstep (se 2 (by rfl) ⟨1093803, by rfl⟩ : syracuseStep 2916809 = 2187607) B2187607
theorem B4391495 : Blo 574812 4391495 := bstep (se 1 (by rfl) ⟨3293621, by rfl⟩ : syracuseStep 4391495 = 6587243) B6587243
theorem B5637221 : Blo 574812 5637221 := bstep (se 4 (by rfl) ⟨528489, by rfl⟩ : syracuseStep 5637221 = 1056979) B1056979
theorem B2917619 : Blo 574812 2917619 := bstep (se 1 (by rfl) ⟨2188214, by rfl⟩ : syracuseStep 2917619 = 4376429) B4376429
theorem B1443065 : Blo 574812 1443065 := bstep (se 2 (by rfl) ⟨541149, by rfl⟩ : syracuseStep 1443065 = 1082299) B1082299
theorem B820729 : Blo 574812 820729 := bstep (se 2 (by rfl) ⟨307773, by rfl⟩ : syracuseStep 820729 = 615547) B615547
theorem B1640729 : Blo 574812 1640729 := bstep (se 2 (by rfl) ⟨615273, by rfl⟩ : syracuseStep 1640729 = 1230547) B1230547
theorem B6588701 : Blo 574812 6588701 := bstep (se 3 (by rfl) ⟨1235381, by rfl⟩ : syracuseStep 6588701 = 2470763) B2470763
theorem B2460239 : Blo 574812 2460239 := bstep (se 1 (by rfl) ⟨1845179, by rfl⟩ : syracuseStep 2460239 = 3690359) B3690359
theorem B3279953 : Blo 574812 3279953 := bstep (se 2 (by rfl) ⟨1229982, by rfl⟩ : syracuseStep 3279953 = 2459965) B2459965
theorem B2919563 : Blo 574812 2919563 := bstep (se 1 (by rfl) ⟨2189672, by rfl⟩ : syracuseStep 2919563 = 4379345) B4379345
theorem B4689035 : Blo 574812 4689035 := bstep (se 1 (by rfl) ⟨3516776, by rfl⟩ : syracuseStep 4689035 = 7033553) B7033553
theorem B1182863 : Blo 574812 1182863 := bstep (se 1 (by rfl) ⟨887147, by rfl⟩ : syracuseStep 1182863 = 1774295) B1774295
theorem B95816981 : Blo 574812 95816981 := bstep (se 6 (by rfl) ⟨2245710, by rfl⟩ : syracuseStep 95816981 = 4491421) B4491421
theorem B23662043 : Blo 574812 23662043 := bstep (se 1 (by rfl) ⟨17746532, by rfl⟩ : syracuseStep 23662043 = 35493065) B35493065
theorem B2952713 : Blo 574812 2952713 := bstep (se 2 (by rfl) ⟨1107267, by rfl⟩ : syracuseStep 2952713 = 2214535) B2214535
theorem B2461265 : Blo 574812 2461265 := bstep (se 2 (by rfl) ⟨922974, by rfl⟩ : syracuseStep 2461265 = 1845949) B1845949
theorem B921385 : Blo 574812 921385 := bstep (se 2 (by rfl) ⟨345519, by rfl⟩ : syracuseStep 921385 = 691039) B691039
theorem B1642369 : Blo 574812 1642369 := bstep (se 2 (by rfl) ⟨615888, by rfl⟩ : syracuseStep 1642369 = 1231777) B1231777
theorem B2363293 : Blo 574812 2363293 := bstep (se 3 (by rfl) ⟨443117, by rfl⟩ : syracuseStep 2363293 = 886235) B886235
theorem B4919453 : Blo 574812 4919453 := bstep (se 3 (by rfl) ⟨922397, by rfl⟩ : syracuseStep 4919453 = 1844795) B1844795
theorem B2331155 : Blo 574812 2331155 := bstep (se 1 (by rfl) ⟨1748366, by rfl⟩ : syracuseStep 2331155 = 3496733) B3496733
theorem B2921183 : Blo 574812 2921183 := bstep (se 1 (by rfl) ⟨2190887, by rfl⟩ : syracuseStep 2921183 = 4381775) B4381775
theorem B2462683 : Blo 574812 2462683 := bstep (se 1 (by rfl) ⟨1847012, by rfl⟩ : syracuseStep 2462683 = 3694025) B3694025
theorem B1643645 : Blo 574812 1643645 := bstep (se 3 (by rfl) ⟨308183, by rfl⟩ : syracuseStep 1643645 = 616367) B616367
theorem B22123691 : Blo 574812 22123691 := bstep (se 1 (by rfl) ⟨16592768, by rfl⟩ : syracuseStep 22123691 = 33185537) B33185537
theorem B1578199 : Blo 574812 1578199 := bstep (se 1 (by rfl) ⟨1183649, by rfl⟩ : syracuseStep 1578199 = 2367299) B2367299
theorem B923231 : Blo 574812 923231 := bstep (se 1 (by rfl) ⟨692423, by rfl⟩ : syracuseStep 923231 = 1384847) B1384847
theorem B2463929 : Blo 574812 2463929 := bstep (se 2 (by rfl) ⟨923973, by rfl⟩ : syracuseStep 2463929 = 1847947) B1847947
theorem B11868389 : Blo 574812 11868389 := bstep (se 4 (by rfl) ⟨1112661, by rfl⟩ : syracuseStep 11868389 = 2225323) B2225323
theorem B3283325 : Blo 574812 3283325 := bstep (se 3 (by rfl) ⟨615623, by rfl⟩ : syracuseStep 3283325 = 1231247) B1231247
theorem B1841591 : Blo 574812 1841591 := bstep (se 1 (by rfl) ⟨1381193, by rfl⟩ : syracuseStep 1841591 = 2762387) B2762387
theorem B5905003 : Blo 574812 5905003 := bstep (se 1 (by rfl) ⟨4428752, by rfl⟩ : syracuseStep 5905003 = 8857505) B8857505
theorem B14195317 : Blo 574812 14195317 := bstep (se 5 (by rfl) ⟨665405, by rfl⟩ : syracuseStep 14195317 = 1330811) B1330811
theorem B2923451 : Blo 574812 2923451 := bstep (se 1 (by rfl) ⟨2192588, by rfl⟩ : syracuseStep 2923451 = 4385177) B4385177
theorem B2333735 : Blo 574812 2333735 := bstep (se 1 (by rfl) ⟨1750301, by rfl⟩ : syracuseStep 2333735 = 3500603) B3500603
theorem B3513467 : Blo 574812 3513467 := bstep (se 1 (by rfl) ⟨2635100, by rfl⟩ : syracuseStep 3513467 = 5270201) B5270201
theorem B728443 : Blo 574812 728443 := bstep (se 1 (by rfl) ⟨546332, by rfl⟩ : syracuseStep 728443 = 1092665) B1092665
theorem B728671 : Blo 574812 728671 := bstep (se 1 (by rfl) ⟨546503, by rfl⟩ : syracuseStep 728671 = 1093007) B1093007
theorem B2924747 : Blo 574812 2924747 := bstep (se 1 (by rfl) ⟨2193560, by rfl⟩ : syracuseStep 2924747 = 4387121) B4387121
theorem B8888663 : Blo 574812 8888663 := bstep (se 1 (by rfl) ⟨6666497, by rfl⟩ : syracuseStep 8888663 = 13332995) B13332995
theorem B1843631 : Blo 574812 1843631 := bstep (se 1 (by rfl) ⟨1382723, by rfl⟩ : syracuseStep 1843631 = 2765447) B2765447
theorem B2073089 : Blo 574812 2073089 := bstep (se 2 (by rfl) ⟨777408, by rfl⟩ : syracuseStep 2073089 = 1554817) B1554817
theorem B926383 : Blo 574812 926383 := bstep (se 1 (by rfl) ⟨694787, by rfl⟩ : syracuseStep 926383 = 1389575) B1389575
theorem B729911 : Blo 574812 729911 := bstep (se 1 (by rfl) ⟨547433, by rfl⟩ : syracuseStep 729911 = 1094867) B1094867
theorem B77112217 : Blo 574812 77112217 := bstep (se 2 (by rfl) ⟨28917081, by rfl⟩ : syracuseStep 77112217 = 57834163) B57834163
theorem B730063 : Blo 574812 730063 := bstep (se 1 (by rfl) ⟨547547, by rfl⟩ : syracuseStep 730063 = 1095095) B1095095
theorem B2335891 : Blo 574812 2335891 := bstep (se 1 (by rfl) ⟨1751918, by rfl⟩ : syracuseStep 2335891 = 3503837) B3503837
theorem B23635115 : Blo 574812 23635115 := bstep (se 1 (by rfl) ⟨17726336, by rfl⟩ : syracuseStep 23635115 = 35452673) B35452673
theorem B1647859 : Blo 574812 1647859 := bstep (se 1 (by rfl) ⟨1235894, by rfl⟩ : syracuseStep 1647859 = 2471789) B2471789
theorem B1942973 : Blo 574812 1942973 := bstep (se 3 (by rfl) ⟨364307, by rfl⟩ : syracuseStep 1942973 = 728615) B728615
theorem B10233479 : Blo 574812 10233479 := bstep (se 1 (by rfl) ⟨7675109, by rfl⟩ : syracuseStep 10233479 = 15350219) B15350219
theorem B1943351 : Blo 574812 1943351 := bstep (se 1 (by rfl) ⟨1457513, by rfl⟩ : syracuseStep 1943351 = 2915027) B2915027
theorem B731035 : Blo 574812 731035 := bstep (se 1 (by rfl) ⟨548276, by rfl⟩ : syracuseStep 731035 = 1096553) B1096553
theorem B3123127 : Blo 574812 3123127 := bstep (se 1 (by rfl) ⟨2342345, by rfl⟩ : syracuseStep 3123127 = 4684691) B4684691
theorem B862313 : Blo 574812 862313 := bstep (se 2 (by rfl) ⟨323367, by rfl⟩ : syracuseStep 862313 = 646735) B646735
theorem B1943837 : Blo 574812 1943837 := bstep (se 3 (by rfl) ⟨364469, by rfl⟩ : syracuseStep 1943837 = 728939) B728939
theorem B1091951 : Blo 574812 1091951 := bstep (se 1 (by rfl) ⟨818963, by rfl⟩ : syracuseStep 1091951 = 1637927) B1637927
theorem B862631 : Blo 574812 862631 := bstep (se 1 (by rfl) ⟨646973, by rfl⟩ : syracuseStep 862631 = 1293947) B1293947
theorem B2927015 : Blo 574812 2927015 := bstep (se 1 (by rfl) ⟨2195261, by rfl⟩ : syracuseStep 2927015 = 4390523) B4390523
theorem B9513389 : Blo 574812 9513389 := bstep (se 3 (by rfl) ⟨1783760, by rfl⟩ : syracuseStep 9513389 = 3567521) B3567521
theorem B2468339 : Blo 574812 2468339 := bstep (se 1 (by rfl) ⟨1851254, by rfl⟩ : syracuseStep 2468339 = 3702509) B3702509
theorem B862715 : Blo 574812 862715 := bstep (se 1 (by rfl) ⟨647036, by rfl⟩ : syracuseStep 862715 = 1294073) B1294073
theorem B2927177 : Blo 574812 2927177 := bstep (se 2 (by rfl) ⟨1097691, by rfl⟩ : syracuseStep 2927177 = 2195383) B2195383
theorem B1387115 : Blo 574812 1387115 := bstep (se 1 (by rfl) ⟨1040336, by rfl⟩ : syracuseStep 1387115 = 2080673) B2080673
theorem B862841 : Blo 574812 862841 := bstep (se 2 (by rfl) ⟨323565, by rfl⟩ : syracuseStep 862841 = 647131) B647131
theorem B1092217 : Blo 574812 1092217 := bstep (se 2 (by rfl) ⟨409581, by rfl⟩ : syracuseStep 1092217 = 819163) B819163
theorem B862895 : Blo 574812 862895 := bstep (se 1 (by rfl) ⟨647171, by rfl⟩ : syracuseStep 862895 = 1294343) B1294343
theorem B862943 : Blo 574812 862943 := bstep (se 1 (by rfl) ⟨647207, by rfl⟩ : syracuseStep 862943 = 1294415) B1294415
theorem B863207 : Blo 574812 863207 := bstep (se 1 (by rfl) ⟨647405, by rfl⟩ : syracuseStep 863207 = 1294811) B1294811
theorem B2468987 : Blo 574812 2468987 := bstep (se 1 (by rfl) ⟨1851740, by rfl⟩ : syracuseStep 2468987 = 3703481) B3703481
theorem B863465 : Blo 574812 863465 := bstep (se 2 (by rfl) ⟨323799, by rfl⟩ : syracuseStep 863465 = 647599) B647599
theorem B863519 : Blo 574812 863519 := bstep (se 1 (by rfl) ⟨647639, by rfl⟩ : syracuseStep 863519 = 1295279) B1295279
theorem B1944863 : Blo 574812 1944863 := bstep (se 1 (by rfl) ⟨1458647, by rfl⟩ : syracuseStep 1944863 = 2917295) B2917295
theorem B863687 : Blo 574812 863687 := bstep (se 1 (by rfl) ⟨647765, by rfl⟩ : syracuseStep 863687 = 1295531) B1295531
theorem B7384769 : Blo 574812 7384769 := bstep (se 2 (by rfl) ⟨2769288, by rfl⟩ : syracuseStep 7384769 = 5538577) B5538577
theorem B4927175 : Blo 574812 4927175 := bstep (se 1 (by rfl) ⟨3695381, by rfl⟩ : syracuseStep 4927175 = 7390763) B7390763
theorem B1388267 : Blo 574812 1388267 := bstep (se 1 (by rfl) ⟨1041200, by rfl⟩ : syracuseStep 1388267 = 2082401) B2082401
theorem B864041 : Blo 574812 864041 := bstep (se 2 (by rfl) ⟨324015, by rfl⟩ : syracuseStep 864041 = 648031) B648031
theorem B864047 : Blo 574812 864047 := bstep (se 1 (by rfl) ⟨648035, by rfl⟩ : syracuseStep 864047 = 1296071) B1296071
theorem B1388335 : Blo 574812 1388335 := bstep (se 1 (by rfl) ⟨1041251, by rfl⟩ : syracuseStep 1388335 = 2082503) B2082503
theorem B864521 : Blo 574812 864521 := bstep (se 2 (by rfl) ⟨324195, by rfl⟩ : syracuseStep 864521 = 648391) B648391
theorem B1093979 : Blo 574812 1093979 := bstep (se 1 (by rfl) ⟨820484, by rfl⟩ : syracuseStep 1093979 = 1640969) B1640969
theorem B864623 : Blo 574812 864623 := bstep (se 1 (by rfl) ⟨648467, by rfl⟩ : syracuseStep 864623 = 1296935) B1296935
theorem B2929121 : Blo 574812 2929121 := bstep (se 2 (by rfl) ⟨1098420, by rfl⟩ : syracuseStep 2929121 = 2196841) B2196841
theorem B864839 : Blo 574812 864839 := bstep (se 1 (by rfl) ⟨648629, by rfl⟩ : syracuseStep 864839 = 1297259) B1297259
theorem B864875 : Blo 574812 864875 := bstep (se 1 (by rfl) ⟨648656, by rfl⟩ : syracuseStep 864875 = 1297313) B1297313
theorem B1979063 : Blo 574812 1979063 := bstep (se 1 (by rfl) ⟨1484297, by rfl⟩ : syracuseStep 1979063 = 2968595) B2968595
theorem B865103 : Blo 574812 865103 := bstep (se 1 (by rfl) ⟨648827, by rfl⟩ : syracuseStep 865103 = 1297655) B1297655
theorem B1094647 : Blo 574812 1094647 := bstep (se 1 (by rfl) ⟨820985, by rfl⟩ : syracuseStep 1094647 = 1641971) B1641971
theorem B865499 : Blo 574812 865499 := bstep (se 1 (by rfl) ⟨649124, by rfl⟩ : syracuseStep 865499 = 1298249) B1298249
theorem B1455347 : Blo 574812 1455347 := bstep (se 1 (by rfl) ⟨1091510, by rfl⟩ : syracuseStep 1455347 = 2183021) B2183021
theorem B1094951 : Blo 574812 1094951 := bstep (se 1 (by rfl) ⟨821213, by rfl⟩ : syracuseStep 1094951 = 1642427) B1642427
theorem B1095049 : Blo 574812 1095049 := bstep (se 2 (by rfl) ⟨410643, by rfl⟩ : syracuseStep 1095049 = 821287) B821287
theorem B865673 : Blo 574812 865673 := bstep (se 2 (by rfl) ⟨324627, by rfl⟩ : syracuseStep 865673 = 649255) B649255
theorem B2471431 : Blo 574812 2471431 := bstep (se 1 (by rfl) ⟨1853573, by rfl⟩ : syracuseStep 2471431 = 3707147) B3707147
theorem B1947293 : Blo 574812 1947293 := bstep (se 3 (by rfl) ⟨365117, by rfl⟩ : syracuseStep 1947293 = 730235) B730235
theorem B1455803 : Blo 574812 1455803 := bstep (se 1 (by rfl) ⟨1091852, by rfl⟩ : syracuseStep 1455803 = 2183705) B2183705
theorem B866027 : Blo 574812 866027 := bstep (se 1 (by rfl) ⟨649520, by rfl⟩ : syracuseStep 866027 = 1299041) B1299041
theorem B11056925 : Blo 574812 11056925 := bstep (se 3 (by rfl) ⟨2073173, by rfl⟩ : syracuseStep 11056925 = 4146347) B4146347
theorem B6600503 : Blo 574812 6600503 := bstep (se 1 (by rfl) ⟨4950377, by rfl⟩ : syracuseStep 6600503 = 9900755) B9900755
theorem B866255 : Blo 574812 866255 := bstep (se 1 (by rfl) ⟨649691, by rfl⟩ : syracuseStep 866255 = 1299383) B1299383
theorem B1947833 : Blo 574812 1947833 := bstep (se 2 (by rfl) ⟨730437, by rfl⟩ : syracuseStep 1947833 = 1460875) B1460875
theorem B1456339 : Blo 574812 1456339 := bstep (se 1 (by rfl) ⟨1092254, by rfl⟩ : syracuseStep 1456339 = 2184509) B2184509
theorem B866651 : Blo 574812 866651 := bstep (se 1 (by rfl) ⟨649988, by rfl⟩ : syracuseStep 866651 = 1299977) B1299977
theorem B1751507 : Blo 574812 1751507 := bstep (se 1 (by rfl) ⟨1313630, by rfl⟩ : syracuseStep 1751507 = 2627261) B2627261
theorem B866879 : Blo 574812 866879 := bstep (se 1 (by rfl) ⟨650159, by rfl⟩ : syracuseStep 866879 = 1300319) B1300319
theorem B12499595 : Blo 574812 12499595 := bstep (se 1 (by rfl) ⟨9374696, by rfl⟩ : syracuseStep 12499595 = 18749393) B18749393
theorem B866999 : Blo 574812 866999 := bstep (se 1 (by rfl) ⟨650249, by rfl⟩ : syracuseStep 866999 = 1300499) B1300499
theorem B4143811 : Blo 574812 4143811 := bstep (se 1 (by rfl) ⟨3107858, by rfl⟩ : syracuseStep 4143811 = 6215717) B6215717
theorem B867227 : Blo 574812 867227 := bstep (se 1 (by rfl) ⟨650420, by rfl⟩ : syracuseStep 867227 = 1300841) B1300841
theorem B1227899 : Blo 574812 1227899 := bstep (se 1 (by rfl) ⟨920924, by rfl⟩ : syracuseStep 1227899 = 1841849) B1841849
theorem B1457291 : Blo 574812 1457291 := bstep (se 1 (by rfl) ⟨1092968, by rfl⟩ : syracuseStep 1457291 = 2185937) B2185937
theorem B3292325 : Blo 574812 3292325 := bstep (se 4 (by rfl) ⟨308655, by rfl⟩ : syracuseStep 3292325 = 617311) B617311
theorem B1752283 : Blo 574812 1752283 := bstep (se 1 (by rfl) ⟨1314212, by rfl⟩ : syracuseStep 1752283 = 2628425) B2628425
theorem B867623 : Blo 574812 867623 := bstep (se 1 (by rfl) ⟨650717, by rfl⟩ : syracuseStep 867623 = 1301435) B1301435
theorem B867707 : Blo 574812 867707 := bstep (se 1 (by rfl) ⟨650780, by rfl⟩ : syracuseStep 867707 = 1301561) B1301561
theorem B1293767 : Blo 574812 1293767 := bstep (se 1 (by rfl) ⟨970325, by rfl⟩ : syracuseStep 1293767 = 1940651) B1940651
theorem B867833 : Blo 574812 867833 := bstep (se 2 (by rfl) ⟨325437, by rfl⟩ : syracuseStep 867833 = 650875) B650875
theorem B3161659 : Blo 574812 3161659 := bstep (se 1 (by rfl) ⟨2371244, by rfl⟩ : syracuseStep 3161659 = 4742489) B4742489
theorem B1457747 : Blo 574812 1457747 := bstep (se 1 (by rfl) ⟨1093310, by rfl⟩ : syracuseStep 1457747 = 2186621) B2186621
theorem B867935 : Blo 574812 867935 := bstep (se 1 (by rfl) ⟨650951, by rfl⟩ : syracuseStep 867935 = 1301903) B1301903
theorem B1949345 : Blo 574812 1949345 := bstep (se 2 (by rfl) ⟨731004, by rfl⟩ : syracuseStep 1949345 = 1462009) B1462009
theorem B1097479 : Blo 574812 1097479 := bstep (se 1 (by rfl) ⟨823109, by rfl⟩ : syracuseStep 1097479 = 1646219) B1646219
theorem B1294127 : Blo 574812 1294127 := bstep (se 1 (by rfl) ⟨970595, by rfl⟩ : syracuseStep 1294127 = 1941191) B1941191
theorem B868151 : Blo 574812 868151 := bstep (se 1 (by rfl) ⟨651113, by rfl⟩ : syracuseStep 868151 = 1302227) B1302227
theorem B4931927 : Blo 574812 4931927 := bstep (se 1 (by rfl) ⟨3698945, by rfl⟩ : syracuseStep 4931927 = 7397891) B7397891
theorem B3293531 : Blo 574812 3293531 := bstep (se 1 (by rfl) ⟨2470148, by rfl⟩ : syracuseStep 3293531 = 4940297) B4940297
theorem B1294703 : Blo 574812 1294703 := bstep (se 1 (by rfl) ⟨971027, by rfl⟩ : syracuseStep 1294703 = 1942055) B1942055
theorem B1229231 : Blo 574812 1229231 := bstep (se 1 (by rfl) ⟨921923, by rfl⟩ : syracuseStep 1229231 = 1843847) B1843847
theorem B1458607 : Blo 574812 1458607 := bstep (se 1 (by rfl) ⟨1093955, by rfl⟩ : syracuseStep 1458607 = 2187911) B2187911
theorem B1294775 : Blo 574812 1294775 := bstep (se 1 (by rfl) ⟨971081, by rfl⟩ : syracuseStep 1294775 = 1942163) B1942163
theorem B1950209 : Blo 574812 1950209 := bstep (se 2 (by rfl) ⟨731328, by rfl⟩ : syracuseStep 1950209 = 1462657) B1462657
theorem B1294919 : Blo 574812 1294919 := bstep (se 1 (by rfl) ⟨971189, by rfl⟩ : syracuseStep 1294919 = 1942379) B1942379
theorem B1294955 : Blo 574812 1294955 := bstep (se 1 (by rfl) ⟨971216, by rfl⟩ : syracuseStep 1294955 = 1942433) B1942433
theorem B1458911 : Blo 574812 1458911 := bstep (se 1 (by rfl) ⟨1094183, by rfl⟩ : syracuseStep 1458911 = 2188367) B2188367
theorem B3293945 : Blo 574812 3293945 := bstep (se 2 (by rfl) ⟨1235229, by rfl⟩ : syracuseStep 3293945 = 2470459) B2470459
theorem B1426331 : Blo 574812 1426331 := bstep (se 1 (by rfl) ⟨1069748, by rfl⟩ : syracuseStep 1426331 = 2139497) B2139497
theorem B4375457 : Blo 574812 4375457 := bstep (se 2 (by rfl) ⟨1640796, by rfl⟩ : syracuseStep 4375457 = 3281593) B3281593
theorem B1950695 : Blo 574812 1950695 := bstep (se 1 (by rfl) ⟨1463021, by rfl⟩ : syracuseStep 1950695 = 2926043) B2926043
theorem B1295351 : Blo 574812 1295351 := bstep (se 1 (by rfl) ⟨971513, by rfl⟩ : syracuseStep 1295351 = 1943027) B1943027
theorem B3294215 : Blo 574812 3294215 := bstep (se 1 (by rfl) ⟨2470661, by rfl⟩ : syracuseStep 3294215 = 4941323) B4941323
theorem B1557737 : Blo 574812 1557737 := bstep (se 2 (by rfl) ⟨584151, by rfl⟩ : syracuseStep 1557737 = 1168303) B1168303
theorem B1951019 : Blo 574812 1951019 := bstep (se 1 (by rfl) ⟨1463264, by rfl⟩ : syracuseStep 1951019 = 2926529) B2926529
theorem B1295711 : Blo 574812 1295711 := bstep (se 1 (by rfl) ⟨971783, by rfl⟩ : syracuseStep 1295711 = 1943567) B1943567
theorem B574831 : Blo 574812 574831 := bstep (se 1 (by rfl) ⟨431123, by rfl⟩ : syracuseStep 574831 = 862247) B862247
theorem B1459579 : Blo 574812 1459579 := bstep (se 1 (by rfl) ⟨1094684, by rfl⟩ : syracuseStep 1459579 = 2189369) B2189369
theorem B574887 : Blo 574812 574887 := bstep (se 1 (by rfl) ⟨431165, by rfl⟩ : syracuseStep 574887 = 862331) B862331
theorem B574971 : Blo 574812 574971 := bstep (se 1 (by rfl) ⟨431228, by rfl⟩ : syracuseStep 574971 = 862457) B862457
theorem B1951289 : Blo 574812 1951289 := bstep (se 2 (by rfl) ⟨731733, by rfl⟩ : syracuseStep 1951289 = 1463467) B1463467
theorem B575039 : Blo 574812 575039 := bstep (se 1 (by rfl) ⟨431279, by rfl⟩ : syracuseStep 575039 = 862559) B862559
theorem B575047 : Blo 574812 575047 := bstep (se 1 (by rfl) ⟨431285, by rfl⟩ : syracuseStep 575047 = 862571) B862571
theorem B575199 : Blo 574812 575199 := bstep (se 1 (by rfl) ⟨431399, by rfl⟩ : syracuseStep 575199 = 862799) B862799
theorem B1296107 : Blo 574812 1296107 := bstep (se 1 (by rfl) ⟨972080, by rfl⟩ : syracuseStep 1296107 = 1944161) B1944161
theorem B575279 : Blo 574812 575279 := bstep (se 1 (by rfl) ⟨431459, by rfl⟩ : syracuseStep 575279 = 862919) B862919
theorem B1460015 : Blo 574812 1460015 := bstep (se 1 (by rfl) ⟨1095011, by rfl⟩ : syracuseStep 1460015 = 2190023) B2190023
theorem B1296233 : Blo 574812 1296233 := bstep (se 2 (by rfl) ⟨486087, by rfl⟩ : syracuseStep 1296233 = 972175) B972175
theorem B3950441 : Blo 574812 3950441 := bstep (se 2 (by rfl) ⟨1481415, by rfl⟩ : syracuseStep 3950441 = 2962831) B2962831
theorem B575387 : Blo 574812 575387 := bstep (se 1 (by rfl) ⟨431540, by rfl⟩ : syracuseStep 575387 = 863081) B863081
theorem B575439 : Blo 574812 575439 := bstep (se 1 (by rfl) ⟨431579, by rfl⟩ : syracuseStep 575439 = 863159) B863159
theorem B575463 : Blo 574812 575463 := bstep (se 1 (by rfl) ⟨431597, by rfl⟩ : syracuseStep 575463 = 863195) B863195
theorem B575775 : Blo 574812 575775 := bstep (se 1 (by rfl) ⟨431831, by rfl⟩ : syracuseStep 575775 = 863663) B863663
theorem B575835 : Blo 574812 575835 := bstep (se 1 (by rfl) ⟨431876, by rfl⟩ : syracuseStep 575835 = 863753) B863753
theorem B575855 : Blo 574812 575855 := bstep (se 1 (by rfl) ⟨431891, by rfl⟩ : syracuseStep 575855 = 863783) B863783
theorem B575911 : Blo 574812 575911 := bstep (se 1 (by rfl) ⟨431933, by rfl⟩ : syracuseStep 575911 = 863867) B863867
theorem B5261735 : Blo 574812 5261735 := bstep (se 1 (by rfl) ⟨3946301, by rfl⟩ : syracuseStep 5261735 = 7892603) B7892603
theorem B1460663 : Blo 574812 1460663 := bstep (se 1 (by rfl) ⟨1095497, by rfl⟩ : syracuseStep 1460663 = 2190995) B2190995
theorem B5917157 : Blo 574812 5917157 := bstep (se 4 (by rfl) ⟨554733, by rfl⟩ : syracuseStep 5917157 = 1109467) B1109467
theorem B575995 : Blo 574812 575995 := bstep (se 1 (by rfl) ⟨431996, by rfl⟩ : syracuseStep 575995 = 863993) B863993
theorem B576063 : Blo 574812 576063 := bstep (se 1 (by rfl) ⟨432047, by rfl⟩ : syracuseStep 576063 = 864095) B864095
theorem B576071 : Blo 574812 576071 := bstep (se 1 (by rfl) ⟨432053, by rfl⟩ : syracuseStep 576071 = 864107) B864107
theorem B1297079 : Blo 574812 1297079 := bstep (se 1 (by rfl) ⟨972809, by rfl⟩ : syracuseStep 1297079 = 1945619) B1945619
theorem B576223 : Blo 574812 576223 := bstep (se 1 (by rfl) ⟨432167, by rfl⟩ : syracuseStep 576223 = 864335) B864335
theorem B3295991 : Blo 574812 3295991 := bstep (se 1 (by rfl) ⟨2471993, by rfl⟩ : syracuseStep 3295991 = 4943987) B4943987
theorem B1952531 : Blo 574812 1952531 := bstep (se 1 (by rfl) ⟨1464398, by rfl⟩ : syracuseStep 1952531 = 2928797) B2928797
theorem B1854227 : Blo 574812 1854227 := bstep (se 1 (by rfl) ⟨1390670, by rfl⟩ : syracuseStep 1854227 = 2781341) B2781341
theorem B576303 : Blo 574812 576303 := bstep (se 1 (by rfl) ⟨432227, by rfl⟩ : syracuseStep 576303 = 864455) B864455
theorem B1297295 : Blo 574812 1297295 := bstep (se 1 (by rfl) ⟨972971, by rfl⟩ : syracuseStep 1297295 = 1945943) B1945943
theorem B576411 : Blo 574812 576411 := bstep (se 1 (by rfl) ⟨432308, by rfl⟩ : syracuseStep 576411 = 864617) B864617
theorem B3689387 : Blo 574812 3689387 := bstep (se 1 (by rfl) ⟨2767040, by rfl⟩ : syracuseStep 3689387 = 5534081) B5534081
theorem B576463 : Blo 574812 576463 := bstep (se 1 (by rfl) ⟨432347, by rfl⟩ : syracuseStep 576463 = 864695) B864695
theorem B576487 : Blo 574812 576487 := bstep (se 1 (by rfl) ⟨432365, by rfl⟩ : syracuseStep 576487 = 864731) B864731
theorem B42224651 : Blo 574812 42224651 := bstep (se 1 (by rfl) ⟨31668488, by rfl⟩ : syracuseStep 42224651 = 63336977) B63336977
theorem B970015 : Blo 574812 970015 := bstep (se 1 (by rfl) ⟨727511, by rfl⟩ : syracuseStep 970015 = 1455023) B1455023
theorem B4377887 : Blo 574812 4377887 := bstep (se 1 (by rfl) ⟨3283415, by rfl⟩ : syracuseStep 4377887 = 6566831) B6566831
theorem B576799 : Blo 574812 576799 := bstep (se 1 (by rfl) ⟨432599, by rfl⟩ : syracuseStep 576799 = 865199) B865199
theorem B576859 : Blo 574812 576859 := bstep (se 1 (by rfl) ⟨432644, by rfl⟩ : syracuseStep 576859 = 865289) B865289
theorem B3001697 : Blo 574812 3001697 := bstep (se 2 (by rfl) ⟨1125636, by rfl⟩ : syracuseStep 3001697 = 2251273) B2251273
theorem B576879 : Blo 574812 576879 := bstep (se 1 (by rfl) ⟨432659, by rfl⟩ : syracuseStep 576879 = 865319) B865319
theorem B1461665 : Blo 574812 1461665 := bstep (se 2 (by rfl) ⟨548124, by rfl⟩ : syracuseStep 1461665 = 1096249) B1096249
theorem B576935 : Blo 574812 576935 := bstep (se 1 (by rfl) ⟨432701, by rfl⟩ : syracuseStep 576935 = 865403) B865403
theorem B577019 : Blo 574812 577019 := bstep (se 1 (by rfl) ⟨432764, by rfl⟩ : syracuseStep 577019 = 865529) B865529
theorem B2674201 : Blo 574812 2674201 := bstep (se 2 (by rfl) ⟨1002825, by rfl⟩ : syracuseStep 2674201 = 2005651) B2005651
theorem B577087 : Blo 574812 577087 := bstep (se 1 (by rfl) ⟨432815, by rfl⟩ : syracuseStep 577087 = 865631) B865631
theorem B577095 : Blo 574812 577095 := bstep (se 1 (by rfl) ⟨432821, by rfl⟩ : syracuseStep 577095 = 865643) B865643
theorem B1298015 : Blo 574812 1298015 := bstep (se 1 (by rfl) ⟨973511, by rfl⟩ : syracuseStep 1298015 = 1947023) B1947023
theorem B1953395 : Blo 574812 1953395 := bstep (se 1 (by rfl) ⟨1465046, by rfl⟩ : syracuseStep 1953395 = 2930093) B2930093
theorem B970427 : Blo 574812 970427 := bstep (se 1 (by rfl) ⟨727820, by rfl⟩ : syracuseStep 970427 = 1455641) B1455641
theorem B4148945 : Blo 574812 4148945 := bstep (se 2 (by rfl) ⟨1555854, by rfl⟩ : syracuseStep 4148945 = 3111709) B3111709
theorem B577247 : Blo 574812 577247 := bstep (se 1 (by rfl) ⟨432935, by rfl⟩ : syracuseStep 577247 = 865871) B865871
theorem B577327 : Blo 574812 577327 := bstep (se 1 (by rfl) ⟨432995, by rfl⟩ : syracuseStep 577327 = 865991) B865991
theorem B1298231 : Blo 574812 1298231 := bstep (se 1 (by rfl) ⟨973673, by rfl⟩ : syracuseStep 1298231 = 1947347) B1947347
theorem B1462121 : Blo 574812 1462121 := bstep (se 2 (by rfl) ⟨548295, by rfl⟩ : syracuseStep 1462121 = 1096591) B1096591
theorem B577435 : Blo 574812 577435 := bstep (se 1 (by rfl) ⟨433076, by rfl⟩ : syracuseStep 577435 = 866153) B866153
theorem B577487 : Blo 574812 577487 := bstep (se 1 (by rfl) ⟨433115, by rfl⟩ : syracuseStep 577487 = 866231) B866231
theorem B3690461 : Blo 574812 3690461 := bstep (se 3 (by rfl) ⟨691961, by rfl⟩ : syracuseStep 3690461 = 1383923) B1383923
theorem B577511 : Blo 574812 577511 := bstep (se 1 (by rfl) ⟨433133, by rfl⟩ : syracuseStep 577511 = 866267) B866267
theorem B4673537 : Blo 574812 4673537 := bstep (se 2 (by rfl) ⟨1752576, by rfl⟩ : syracuseStep 4673537 = 3505153) B3505153
theorem B1298537 : Blo 574812 1298537 := bstep (se 2 (by rfl) ⟨486951, by rfl⟩ : syracuseStep 1298537 = 973903) B973903
theorem B1233161 : Blo 574812 1233161 := bstep (se 2 (by rfl) ⟨462435, by rfl⟩ : syracuseStep 1233161 = 924871) B924871
theorem B577823 : Blo 574812 577823 := bstep (se 1 (by rfl) ⟨433367, by rfl⟩ : syracuseStep 577823 = 866735) B866735
theorem B1757513 : Blo 574812 1757513 := bstep (se 2 (by rfl) ⟨659067, by rfl⟩ : syracuseStep 1757513 = 1318135) B1318135
theorem B577883 : Blo 574812 577883 := bstep (se 1 (by rfl) ⟨433412, by rfl⟩ : syracuseStep 577883 = 866825) B866825
theorem B3166571 : Blo 574812 3166571 := bstep (se 1 (by rfl) ⟨2374928, by rfl⟩ : syracuseStep 3166571 = 4749857) B4749857
theorem B1233263 : Blo 574812 1233263 := bstep (se 1 (by rfl) ⟨924947, by rfl⟩ : syracuseStep 1233263 = 1849895) B1849895
theorem B577903 : Blo 574812 577903 := bstep (se 1 (by rfl) ⟨433427, by rfl⟩ : syracuseStep 577903 = 866855) B866855
theorem B577959 : Blo 574812 577959 := bstep (se 1 (by rfl) ⟨433469, by rfl⟩ : syracuseStep 577959 = 866939) B866939
theorem B578043 : Blo 574812 578043 := bstep (se 1 (by rfl) ⟨433532, by rfl⟩ : syracuseStep 578043 = 867065) B867065
theorem B578111 : Blo 574812 578111 := bstep (se 1 (by rfl) ⟨433583, by rfl⟩ : syracuseStep 578111 = 867167) B867167
theorem B578119 : Blo 574812 578119 := bstep (se 1 (by rfl) ⟨433589, by rfl⟩ : syracuseStep 578119 = 867179) B867179
theorem B1299023 : Blo 574812 1299023 := bstep (se 1 (by rfl) ⟨974267, by rfl⟩ : syracuseStep 1299023 = 1948535) B1948535
theorem B1299167 : Blo 574812 1299167 := bstep (se 1 (by rfl) ⟨974375, by rfl⟩ : syracuseStep 1299167 = 1948751) B1948751
theorem B578271 : Blo 574812 578271 := bstep (se 1 (by rfl) ⟨433703, by rfl⟩ : syracuseStep 578271 = 867407) B867407
theorem B578351 : Blo 574812 578351 := bstep (se 1 (by rfl) ⟨433763, by rfl⟩ : syracuseStep 578351 = 867527) B867527
theorem B676687 : Blo 574812 676687 := bstep (se 1 (by rfl) ⟨507515, by rfl⟩ : syracuseStep 676687 = 1015031) B1015031
theorem B578459 : Blo 574812 578459 := bstep (se 1 (by rfl) ⟨433844, by rfl⟩ : syracuseStep 578459 = 867689) B867689
theorem B578511 : Blo 574812 578511 := bstep (se 1 (by rfl) ⟨433883, by rfl⟩ : syracuseStep 578511 = 867767) B867767
theorem B1299419 : Blo 574812 1299419 := bstep (se 1 (by rfl) ⟨974564, by rfl⟩ : syracuseStep 1299419 = 1949129) B1949129
theorem B578535 : Blo 574812 578535 := bstep (se 1 (by rfl) ⟨433901, by rfl⟩ : syracuseStep 578535 = 867803) B867803
theorem B1299599 : Blo 574812 1299599 := bstep (se 1 (by rfl) ⟨974699, by rfl⟩ : syracuseStep 1299599 = 1949399) B1949399
theorem B1299689 : Blo 574812 1299689 := bstep (se 2 (by rfl) ⟨487383, by rfl⟩ : syracuseStep 1299689 = 974767) B974767
theorem B1299743 : Blo 574812 1299743 := bstep (se 1 (by rfl) ⟨974807, by rfl⟩ : syracuseStep 1299743 = 1949615) B1949615
theorem B972155 : Blo 574812 972155 := bstep (se 1 (by rfl) ⟨729116, by rfl⟩ : syracuseStep 972155 = 1458233) B1458233
theorem B1463903 : Blo 574812 1463903 := bstep (se 1 (by rfl) ⟨1097927, by rfl⟩ : syracuseStep 1463903 = 2195855) B2195855
theorem B1300265 : Blo 574812 1300265 := bstep (se 2 (by rfl) ⟨487599, by rfl⟩ : syracuseStep 1300265 = 975199) B975199
theorem B10639163 : Blo 574812 10639163 := bstep (se 1 (by rfl) ⟨7979372, by rfl⟩ : syracuseStep 10639163 = 15958745) B15958745
theorem B10508291 : Blo 574812 10508291 := bstep (se 1 (by rfl) ⟨7881218, by rfl⟩ : syracuseStep 10508291 = 15762437) B15762437
theorem B2185481 : Blo 574812 2185481 := bstep (se 2 (by rfl) ⟨819555, by rfl⟩ : syracuseStep 2185481 = 1639111) B1639111
theorem B1464601 : Blo 574812 1464601 := bstep (se 2 (by rfl) ⟨549225, by rfl⟩ : syracuseStep 1464601 = 1098451) B1098451
theorem B5921099 : Blo 574812 5921099 := bstep (se 1 (by rfl) ⟨4440824, by rfl⟩ : syracuseStep 5921099 = 8881649) B8881649
theorem B973147 : Blo 574812 973147 := bstep (se 1 (by rfl) ⟨729860, by rfl⟩ : syracuseStep 973147 = 1459721) B1459721
theorem B1464743 : Blo 574812 1464743 := bstep (se 1 (by rfl) ⟨1098557, by rfl⟩ : syracuseStep 1464743 = 2197115) B2197115
theorem B1464905 : Blo 574812 1464905 := bstep (se 2 (by rfl) ⟨549339, by rfl⟩ : syracuseStep 1464905 = 1098679) B1098679
theorem B1301327 : Blo 574812 1301327 := bstep (se 1 (by rfl) ⟨975995, by rfl⟩ : syracuseStep 1301327 = 1951991) B1951991
theorem B1301543 : Blo 574812 1301543 := bstep (se 1 (by rfl) ⟨976157, by rfl⟩ : syracuseStep 1301543 = 1952315) B1952315
theorem B1236065 : Blo 574812 1236065 := bstep (se 2 (by rfl) ⟨463524, by rfl⟩ : syracuseStep 1236065 = 927049) B927049
theorem B1301723 : Blo 574812 1301723 := bstep (se 1 (by rfl) ⟨976292, by rfl⟩ : syracuseStep 1301723 = 1952585) B1952585
theorem B974119 : Blo 574812 974119 := bstep (se 1 (by rfl) ⟨730589, by rfl⟩ : syracuseStep 974119 = 1461179) B1461179
theorem B2776457 : Blo 574812 2776457 := bstep (se 2 (by rfl) ⟨1041171, by rfl⟩ : syracuseStep 2776457 = 2082343) B2082343
theorem B1301921 : Blo 574812 1301921 := bstep (se 2 (by rfl) ⟨488220, by rfl⟩ : syracuseStep 1301921 = 976441) B976441
theorem B646879 : Blo 574812 646879 := bstep (se 1 (by rfl) ⟨485159, by rfl⟩ : syracuseStep 646879 = 970319) B970319
theorem B974639 : Blo 574812 974639 := bstep (se 1 (by rfl) ⟨730979, by rfl⟩ : syracuseStep 974639 = 1461959) B1461959
theorem B1171255 : Blo 574812 1171255 := bstep (se 1 (by rfl) ⟨878441, by rfl⟩ : syracuseStep 1171255 = 1756883) B1756883
theorem B3694511 : Blo 574812 3694511 := bstep (se 1 (by rfl) ⟨2770883, by rfl⟩ : syracuseStep 3694511 = 5541767) B5541767
theorem B614351 : Blo 574812 614351 := bstep (se 1 (by rfl) ⟨460763, by rfl⟩ : syracuseStep 614351 = 921527) B921527
theorem B1663001 : Blo 574812 1663001 := bstep (se 2 (by rfl) ⟨623625, by rfl⟩ : syracuseStep 1663001 = 1247251) B1247251
theorem B647455 : Blo 574812 647455 := bstep (se 1 (by rfl) ⟨485591, by rfl⟩ : syracuseStep 647455 = 971183) B971183
theorem B2187593 : Blo 574812 2187593 := bstep (se 2 (by rfl) ⟨820347, by rfl⟩ : syracuseStep 2187593 = 1640695) B1640695
theorem B6218137 : Blo 574812 6218137 := bstep (se 2 (by rfl) ⟨2331801, by rfl⟩ : syracuseStep 6218137 = 4663603) B4663603
theorem B4383233 : Blo 574812 4383233 := bstep (se 2 (by rfl) ⟨1643712, by rfl⟩ : syracuseStep 4383233 = 3287425) B3287425
theorem B2777651 : Blo 574812 2777651 := bstep (se 1 (by rfl) ⟨2083238, by rfl⟩ : syracuseStep 2777651 = 4166477) B4166477
theorem B647743 : Blo 574812 647743 := bstep (se 1 (by rfl) ⟨485807, by rfl⟩ : syracuseStep 647743 = 971615) B971615
theorem B4383719 : Blo 574812 4383719 := bstep (se 1 (by rfl) ⟨3287789, by rfl⟩ : syracuseStep 4383719 = 6575579) B6575579
theorem B975847 : Blo 574812 975847 := bstep (se 1 (by rfl) ⟨731885, by rfl⟩ : syracuseStep 975847 = 1463771) B1463771
theorem B2778209 : Blo 574812 2778209 := bstep (se 2 (by rfl) ⟨1041828, by rfl⟩ : syracuseStep 2778209 = 2083657) B2083657
theorem B648571 : Blo 574812 648571 := bstep (se 1 (by rfl) ⟨486428, by rfl⟩ : syracuseStep 648571 = 972857) B972857
theorem B779657 : Blo 574812 779657 := bstep (se 2 (by rfl) ⟨292371, by rfl⟩ : syracuseStep 779657 = 584743) B584743
theorem B24864245 : Blo 574812 24864245 := bstep (se 5 (by rfl) ⟨1165511, by rfl⟩ : syracuseStep 24864245 = 2331023) B2331023
theorem B5793569 : Blo 574812 5793569 := bstep (se 2 (by rfl) ⟨2172588, by rfl⟩ : syracuseStep 5793569 = 4345177) B4345177
theorem B780079 : Blo 574812 780079 := bstep (se 1 (by rfl) ⟨585059, by rfl⟩ : syracuseStep 780079 = 1170119) B1170119
theorem B649039 : Blo 574812 649039 := bstep (se 1 (by rfl) ⟨486779, by rfl⟩ : syracuseStep 649039 = 973559) B973559
theorem B780187 : Blo 574812 780187 := bstep (se 1 (by rfl) ⟨585140, by rfl⟩ : syracuseStep 780187 = 1170281) B1170281
theorem B7890851 : Blo 574812 7890851 := bstep (se 1 (by rfl) ⟨5918138, by rfl⟩ : syracuseStep 7890851 = 11836277) B11836277
theorem B649435 : Blo 574812 649435 := bstep (se 1 (by rfl) ⟨487076, by rfl⟩ : syracuseStep 649435 = 974153) B974153
theorem B649723 : Blo 574812 649723 := bstep (se 1 (by rfl) ⟨487292, by rfl⟩ : syracuseStep 649723 = 974585) B974585
theorem B649903 : Blo 574812 649903 := bstep (se 1 (by rfl) ⟨487427, by rfl⟩ : syracuseStep 649903 = 974855) B974855
theorem B650191 : Blo 574812 650191 := bstep (se 1 (by rfl) ⟨487643, by rfl⟩ : syracuseStep 650191 = 975287) B975287
theorem B4156703 : Blo 574812 4156703 := bstep (se 1 (by rfl) ⟨3117527, by rfl⟩ : syracuseStep 4156703 = 6235055) B6235055
theorem B650587 : Blo 574812 650587 := bstep (se 1 (by rfl) ⟨487940, by rfl⟩ : syracuseStep 650587 = 975881) B975881
theorem B2911625 : Blo 574812 2911625 := bstep (se 2 (by rfl) ⟨1091859, by rfl⟩ : syracuseStep 2911625 = 2183719) B2183719
theorem B650695 : Blo 574812 650695 := bstep (se 1 (by rfl) ⟨488021, by rfl⟩ : syracuseStep 650695 = 976043) B976043
theorem B3108377 : Blo 574812 3108377 := bstep (se 2 (by rfl) ⟨1165641, by rfl⟩ : syracuseStep 3108377 = 2331283) B2331283
theorem B2191009 : Blo 574812 2191009 := bstep (se 2 (by rfl) ⟨821628, by rfl⟩ : syracuseStep 2191009 = 1643257) B1643257
theorem B651055 : Blo 574812 651055 := bstep (se 1 (by rfl) ⟨488291, by rfl⟩ : syracuseStep 651055 = 976583) B976583
theorem B651163 : Blo 574812 651163 := bstep (se 1 (by rfl) ⟨488372, by rfl⟩ : syracuseStep 651163 = 976745) B976745
theorem B97382873 : Blo 574812 97382873 := bstep (se 2 (by rfl) ⟨36518577, by rfl⟩ : syracuseStep 97382873 = 73037155) B73037155
theorem B2912921 : Blo 574812 2912921 := bstep (se 2 (by rfl) ⟨1092345, by rfl⟩ : syracuseStep 2912921 = 2184691) B2184691
theorem B5632973 : Blo 574812 5632973 := bstep (se 3 (by rfl) ⟨1056182, by rfl⟩ : syracuseStep 5632973 = 2112365) B2112365
theorem B8123809 : Blo 574812 8123809 := bstep (se 2 (by rfl) ⟨3046428, by rfl⟩ : syracuseStep 8123809 = 6092857) B6092857
theorem B2192953 : Blo 574812 2192953 := bstep (se 2 (by rfl) ⟨822357, by rfl⟩ : syracuseStep 2192953 = 1644715) B1644715
theorem B2193257 : Blo 574812 2193257 := bstep (se 2 (by rfl) ⟨822471, by rfl⟩ : syracuseStep 2193257 = 1644943) B1644943
theorem B2455933 : Blo 574812 2455933 := bstep (se 3 (by rfl) ⟨460487, by rfl⟩ : syracuseStep 2455933 = 920975) B920975
theorem B2914703 : Blo 574812 2914703 := bstep (se 1 (by rfl) ⟨2186027, by rfl⟩ : syracuseStep 2914703 = 4372055) B4372055
theorem B4389551 : Blo 574812 4389551 := bstep (se 1 (by rfl) ⟨3292163, by rfl⟩ : syracuseStep 4389551 = 6584327) B6584327
theorem B9993239 : Blo 574812 9993239 := bstep (se 1 (by rfl) ⟨7494929, by rfl⟩ : syracuseStep 9993239 = 14989859) B14989859
theorem B3276719 : Blo 574812 3276719 := bstep (se 1 (by rfl) ⟨2457539, by rfl⟩ : syracuseStep 3276719 = 4915079) B4915079
theorem B3997927 : Blo 574812 3997927 := bstep (se 1 (by rfl) ⟨2998445, by rfl⟩ : syracuseStep 3997927 = 5996891) B5996891
theorem B2195687 : Blo 574812 2195687 := bstep (se 1 (by rfl) ⟨1646765, by rfl⟩ : syracuseStep 2195687 = 3293531) B3293531
theorem B819487 : Blo 574812 819487 := bstep (se 1 (by rfl) ⟨614615, by rfl⟩ : syracuseStep 819487 = 1229231) B1229231
theorem B2195963 : Blo 574812 2195963 := bstep (se 1 (by rfl) ⟨1646972, by rfl⟩ : syracuseStep 2195963 = 3293945) B3293945
theorem B8290849 : Blo 574812 8290849 := bstep (se 2 (by rfl) ⟨3109068, by rfl⟩ : syracuseStep 8290849 = 6218137) B6218137
theorem B950887 : Blo 574812 950887 := bstep (se 1 (by rfl) ⟨713165, by rfl⟩ : syracuseStep 950887 = 1426331) B1426331
theorem B2916971 : Blo 574812 2916971 := bstep (se 1 (by rfl) ⟨2187728, by rfl⟩ : syracuseStep 2916971 = 4375457) B4375457
theorem B2196143 : Blo 574812 2196143 := bstep (se 1 (by rfl) ⟨1647107, by rfl⟩ : syracuseStep 2196143 = 3294215) B3294215
theorem B4392467 : Blo 574812 4392467 := bstep (se 1 (by rfl) ⟨3294350, by rfl⟩ : syracuseStep 4392467 = 6588701) B6588701
theorem B3114521 : Blo 574812 3114521 := bstep (se 2 (by rfl) ⟨1167945, by rfl⟩ : syracuseStep 3114521 = 2335891) B2335891
theorem B3507823 : Blo 574812 3507823 := bstep (se 1 (by rfl) ⟨2630867, by rfl⟩ : syracuseStep 3507823 = 5261735) B5261735
theorem B2197145 : Blo 574812 2197145 := bstep (se 2 (by rfl) ⟨823929, by rfl⟩ : syracuseStep 2197145 = 1647859) B1647859
theorem B1640159 : Blo 574812 1640159 := bstep (se 1 (by rfl) ⟨1230119, by rfl⟩ : syracuseStep 1640159 = 2460239) B2460239
theorem B2197327 : Blo 574812 2197327 := bstep (se 1 (by rfl) ⟨1647995, by rfl⟩ : syracuseStep 2197327 = 3295991) B3295991
theorem B2459591 : Blo 574812 2459591 := bstep (se 1 (by rfl) ⟨1844693, by rfl⟩ : syracuseStep 2459591 = 3689387) B3689387
theorem B28149767 : Blo 574812 28149767 := bstep (se 1 (by rfl) ⟨21112325, by rfl⟩ : syracuseStep 28149767 = 42224651) B42224651
theorem B2918591 : Blo 574812 2918591 := bstep (se 1 (by rfl) ⟨2188943, by rfl⟩ : syracuseStep 2918591 = 4377887) B4377887
theorem B2001131 : Blo 574812 2001131 := bstep (se 1 (by rfl) ⟨1500848, by rfl⟩ : syracuseStep 2001131 = 3001697) B3001697
theorem B1968475 : Blo 574812 1968475 := bstep (se 1 (by rfl) ⟨1476356, by rfl⟩ : syracuseStep 1968475 = 2952713) B2952713
theorem B1640843 : Blo 574812 1640843 := bstep (se 1 (by rfl) ⟨1230632, by rfl⟩ : syracuseStep 1640843 = 2461265) B2461265
theorem B4164169 : Blo 574812 4164169 := bstep (se 2 (by rfl) ⟨1561563, by rfl⟩ : syracuseStep 4164169 = 3123127) B3123127
theorem B2460307 : Blo 574812 2460307 := bstep (se 1 (by rfl) ⟨1845230, by rfl⟩ : syracuseStep 2460307 = 3690461) B3690461
theorem B3115691 : Blo 574812 3115691 := bstep (se 1 (by rfl) ⟨2336768, by rfl⟩ : syracuseStep 3115691 = 4673537) B4673537
theorem B3279635 : Blo 574812 3279635 := bstep (se 1 (by rfl) ⟨2459726, by rfl⟩ : syracuseStep 3279635 = 4919453) B4919453
theorem B822107 : Blo 574812 822107 := bstep (se 1 (by rfl) ⟨616580, by rfl⟩ : syracuseStep 822107 = 1233161) B1233161
theorem B14749127 : Blo 574812 14749127 := bstep (se 1 (by rfl) ⟨11061845, by rfl⟩ : syracuseStep 14749127 = 22123691) B22123691
theorem B1642619 : Blo 574812 1642619 := bstep (se 1 (by rfl) ⟨1231964, by rfl⟩ : syracuseStep 1642619 = 2463929) B2463929
theorem B2921345 : Blo 574812 2921345 := bstep (se 2 (by rfl) ⟨1095504, by rfl⟩ : syracuseStep 2921345 = 2191009) B2191009
theorem B3151057 : Blo 574812 3151057 := bstep (se 2 (by rfl) ⟨1181646, by rfl⟩ : syracuseStep 3151057 = 2363293) B2363293
theorem B2463007 : Blo 574812 2463007 := bstep (se 1 (by rfl) ⟨1847255, by rfl⟩ : syracuseStep 2463007 = 3694511) B3694511
theorem B1382059 : Blo 574812 1382059 := bstep (se 1 (by rfl) ⟨1036544, by rfl⟩ : syracuseStep 1382059 = 2073089) B2073089
theorem B2922155 : Blo 574812 2922155 := bstep (se 1 (by rfl) ⟨2191616, by rfl⟩ : syracuseStep 2922155 = 4383233) B4383233
theorem B2922479 : Blo 574812 2922479 := bstep (se 1 (by rfl) ⟨2191859, by rfl⟩ : syracuseStep 2922479 = 4383719) B4383719
theorem B6822319 : Blo 574812 6822319 := bstep (se 1 (by rfl) ⟨5116739, by rfl⟩ : syracuseStep 6822319 = 10233479) B10233479
theorem B3283577 : Blo 574812 3283577 := bstep (se 2 (by rfl) ⟨1231341, by rfl⟩ : syracuseStep 3283577 = 2462683) B2462683
theorem B727967 : Blo 574812 727967 := bstep (se 1 (by rfl) ⟨545975, by rfl⟩ : syracuseStep 727967 = 1091951) B1091951
theorem B2104265 : Blo 574812 2104265 := bstep (se 2 (by rfl) ⟨789099, by rfl⟩ : syracuseStep 2104265 = 1578199) B1578199
theorem B1645559 : Blo 574812 1645559 := bstep (se 1 (by rfl) ⟨1234169, by rfl⟩ : syracuseStep 1645559 = 2468339) B2468339
theorem B924743 : Blo 574812 924743 := bstep (se 1 (by rfl) ⟨693557, by rfl⟩ : syracuseStep 924743 = 1387115) B1387115
theorem B2923937 : Blo 574812 2923937 := bstep (se 2 (by rfl) ⟨1096476, by rfl⟩ : syracuseStep 2923937 = 2192953) B2192953
theorem B1645991 : Blo 574812 1645991 := bstep (se 1 (by rfl) ⟨1234493, by rfl⟩ : syracuseStep 1645991 = 2468987) B2468987
theorem B1941083 : Blo 574812 1941083 := bstep (se 1 (by rfl) ⟨1455812, by rfl⟩ : syracuseStep 1941083 = 2911625) B2911625
theorem B2072251 : Blo 574812 2072251 := bstep (se 1 (by rfl) ⟨1554188, by rfl⟩ : syracuseStep 2072251 = 3108377) B3108377
theorem B4923179 : Blo 574812 4923179 := bstep (se 1 (by rfl) ⟨3692384, by rfl⟩ : syracuseStep 4923179 = 7384769) B7384769
theorem B3284783 : Blo 574812 3284783 := bstep (se 1 (by rfl) ⟨2463587, by rfl⟩ : syracuseStep 3284783 = 4927175) B4927175
theorem B925511 : Blo 574812 925511 := bstep (se 1 (by rfl) ⟨694133, by rfl⟩ : syracuseStep 925511 = 1388267) B1388267
theorem B729319 : Blo 574812 729319 := bstep (se 1 (by rfl) ⟨546989, by rfl⟩ : syracuseStep 729319 = 1093979) B1093979
theorem B1941785 : Blo 574812 1941785 := bstep (se 2 (by rfl) ⟨728169, by rfl⟩ : syracuseStep 1941785 = 1456339) B1456339
theorem B64921915 : Blo 574812 64921915 := bstep (se 1 (by rfl) ⟨48691436, by rfl⟩ : syracuseStep 64921915 = 97382873) B97382873
theorem B3154301 : Blo 574812 3154301 := bstep (se 3 (by rfl) ⟨591431, by rfl⟩ : syracuseStep 3154301 = 1182863) B1182863
theorem B1941947 : Blo 574812 1941947 := bstep (se 1 (by rfl) ⟨1456460, by rfl⟩ : syracuseStep 1941947 = 2912921) B2912921
theorem B1319375 : Blo 574812 1319375 := bstep (se 1 (by rfl) ⟨989531, by rfl⟩ : syracuseStep 1319375 = 1979063) B1979063
theorem B7873337 : Blo 574812 7873337 := bstep (se 2 (by rfl) ⟨2952501, by rfl⟩ : syracuseStep 7873337 = 5905003) B5905003
theorem B729967 : Blo 574812 729967 := bstep (se 1 (by rfl) ⟨547475, by rfl⟩ : syracuseStep 729967 = 1094951) B1094951
theorem B4400335 : Blo 574812 4400335 := bstep (se 1 (by rfl) ⟨3300251, by rfl⟩ : syracuseStep 4400335 = 6600503) B6600503
theorem B1943135 : Blo 574812 1943135 := bstep (se 1 (by rfl) ⟨1457351, by rfl⟩ : syracuseStep 1943135 = 2914703) B2914703
theorem B2336377 : Blo 574812 2336377 := bstep (se 2 (by rfl) ⟨876141, by rfl⟩ : syracuseStep 2336377 = 1752283) B1752283
theorem B8333063 : Blo 574812 8333063 := bstep (se 1 (by rfl) ⟨6249797, by rfl⟩ : syracuseStep 8333063 = 12499595) B12499595
theorem B2926367 : Blo 574812 2926367 := bstep (se 1 (by rfl) ⟨2194775, by rfl⟩ : syracuseStep 2926367 = 4389551) B4389551
theorem B6662159 : Blo 574812 6662159 := bstep (se 1 (by rfl) ⟨4996619, by rfl⟩ : syracuseStep 6662159 = 9993239) B9993239
theorem B862505 : Blo 574812 862505 := bstep (se 2 (by rfl) ⟨323439, by rfl⟩ : syracuseStep 862505 = 646879) B646879
theorem B862511 : Blo 574812 862511 := bstep (se 1 (by rfl) ⟨646883, by rfl⟩ : syracuseStep 862511 = 1293767) B1293767
theorem B862751 : Blo 574812 862751 := bstep (se 1 (by rfl) ⟨647063, by rfl⟩ : syracuseStep 862751 = 1294127) B1294127
theorem B3287951 : Blo 574812 3287951 := bstep (se 1 (by rfl) ⟨2465963, by rfl⟩ : syracuseStep 3287951 = 4931927) B4931927
theorem B863135 : Blo 574812 863135 := bstep (se 1 (by rfl) ⟨647351, by rfl⟩ : syracuseStep 863135 = 1294703) B1294703
theorem B863183 : Blo 574812 863183 := bstep (se 1 (by rfl) ⟨647387, by rfl⟩ : syracuseStep 863183 = 1294775) B1294775
theorem B1944539 : Blo 574812 1944539 := bstep (se 1 (by rfl) ⟨1458404, by rfl⟩ : syracuseStep 1944539 = 2916809) B2916809
theorem B863273 : Blo 574812 863273 := bstep (se 2 (by rfl) ⟨323727, by rfl⟩ : syracuseStep 863273 = 647455) B647455
theorem B863279 : Blo 574812 863279 := bstep (se 1 (by rfl) ⟨647459, by rfl⟩ : syracuseStep 863279 = 1294919) B1294919
theorem B2927663 : Blo 574812 2927663 := bstep (se 1 (by rfl) ⟨2195747, by rfl⟩ : syracuseStep 2927663 = 4391495) B4391495
theorem B863303 : Blo 574812 863303 := bstep (se 1 (by rfl) ⟨647477, by rfl⟩ : syracuseStep 863303 = 1294955) B1294955
theorem B1944809 : Blo 574812 1944809 := bstep (se 2 (by rfl) ⟨729303, by rfl⟩ : syracuseStep 1944809 = 1458607) B1458607
theorem B863567 : Blo 574812 863567 := bstep (se 1 (by rfl) ⟨647675, by rfl⟩ : syracuseStep 863567 = 1295351) B1295351
theorem B863657 : Blo 574812 863657 := bstep (se 2 (by rfl) ⟨323871, by rfl⟩ : syracuseStep 863657 = 647743) B647743
theorem B1945079 : Blo 574812 1945079 := bstep (se 1 (by rfl) ⟨1458809, by rfl⟩ : syracuseStep 1945079 = 2917619) B2917619
theorem B23703101 : Blo 574812 23703101 := bstep (se 3 (by rfl) ⟨4444331, by rfl⟩ : syracuseStep 23703101 = 8888663) B8888663
theorem B863807 : Blo 574812 863807 := bstep (se 1 (by rfl) ⟨647855, by rfl⟩ : syracuseStep 863807 = 1295711) B1295711
theorem B3288701 : Blo 574812 3288701 := bstep (se 3 (by rfl) ⟨616631, by rfl⟩ : syracuseStep 3288701 = 1233263) B1233263
theorem B864071 : Blo 574812 864071 := bstep (se 1 (by rfl) ⟨648053, by rfl⟩ : syracuseStep 864071 = 1296107) B1296107
theorem B864155 : Blo 574812 864155 := bstep (se 1 (by rfl) ⟨648116, by rfl⟩ : syracuseStep 864155 = 1296233) B1296233
theorem B2633627 : Blo 574812 2633627 := bstep (se 1 (by rfl) ⟨1975220, by rfl⟩ : syracuseStep 2633627 = 3950441) B3950441
theorem B1093819 : Blo 574812 1093819 := bstep (se 1 (by rfl) ⟨820364, by rfl⟩ : syracuseStep 1093819 = 1640729) B1640729
theorem B3944771 : Blo 574812 3944771 := bstep (se 1 (by rfl) ⟨2958578, by rfl⟩ : syracuseStep 3944771 = 5917157) B5917157
theorem B864719 : Blo 574812 864719 := bstep (se 1 (by rfl) ⟨648539, by rfl⟩ : syracuseStep 864719 = 1297079) B1297079
theorem B864761 : Blo 574812 864761 := bstep (se 2 (by rfl) ⟨324285, by rfl⟩ : syracuseStep 864761 = 648571) B648571
theorem B1946105 : Blo 574812 1946105 := bstep (se 2 (by rfl) ⟨729789, by rfl⟩ : syracuseStep 1946105 = 1459579) B1459579
theorem B864863 : Blo 574812 864863 := bstep (se 1 (by rfl) ⟨648647, by rfl⟩ : syracuseStep 864863 = 1297295) B1297295
theorem B1094305 : Blo 574812 1094305 := bstep (se 2 (by rfl) ⟨410364, by rfl⟩ : syracuseStep 1094305 = 820729) B820729
theorem B1946375 : Blo 574812 1946375 := bstep (se 1 (by rfl) ⟨1459781, by rfl⟩ : syracuseStep 1946375 = 2919563) B2919563
theorem B3126023 : Blo 574812 3126023 := bstep (se 1 (by rfl) ⟨2344517, by rfl⟩ : syracuseStep 3126023 = 4689035) B4689035
theorem B1946429 : Blo 574812 1946429 := bstep (se 3 (by rfl) ⟨364955, by rfl⟩ : syracuseStep 1946429 = 729911) B729911
theorem B63877987 : Blo 574812 63877987 := bstep (se 1 (by rfl) ⟨47908490, by rfl⟩ : syracuseStep 63877987 = 95816981) B95816981
theorem B15774695 : Blo 574812 15774695 := bstep (se 1 (by rfl) ⟨11831021, by rfl⟩ : syracuseStep 15774695 = 23662043) B23662043
theorem B865343 : Blo 574812 865343 := bstep (se 1 (by rfl) ⟨649007, by rfl⟩ : syracuseStep 865343 = 1298015) B1298015
theorem B865385 : Blo 574812 865385 := bstep (se 2 (by rfl) ⟨324519, by rfl⟩ : syracuseStep 865385 = 649039) B649039
theorem B2765963 : Blo 574812 2765963 := bstep (se 1 (by rfl) ⟨2074472, by rfl⟩ : syracuseStep 2765963 = 4148945) B4148945
theorem B865487 : Blo 574812 865487 := bstep (se 1 (by rfl) ⟨649115, by rfl⟩ : syracuseStep 865487 = 1298231) B1298231
theorem B865691 : Blo 574812 865691 := bstep (se 1 (by rfl) ⟨649268, by rfl⟩ : syracuseStep 865691 = 1298537) B1298537
theorem B865913 : Blo 574812 865913 := bstep (se 2 (by rfl) ⟨324717, by rfl⟩ : syracuseStep 865913 = 649435) B649435
theorem B1554103 : Blo 574812 1554103 := bstep (se 1 (by rfl) ⟨1165577, by rfl⟩ : syracuseStep 1554103 = 2331155) B2331155
theorem B866015 : Blo 574812 866015 := bstep (se 1 (by rfl) ⟨649511, by rfl⟩ : syracuseStep 866015 = 1299023) B1299023
theorem B1947455 : Blo 574812 1947455 := bstep (se 1 (by rfl) ⟨1460591, by rfl⟩ : syracuseStep 1947455 = 2921183) B2921183
theorem B866111 : Blo 574812 866111 := bstep (se 1 (by rfl) ⟨649583, by rfl⟩ : syracuseStep 866111 = 1299167) B1299167
theorem B866279 : Blo 574812 866279 := bstep (se 1 (by rfl) ⟨649709, by rfl⟩ : syracuseStep 866279 = 1299419) B1299419
theorem B866297 : Blo 574812 866297 := bstep (se 2 (by rfl) ⟨324861, by rfl⟩ : syracuseStep 866297 = 649723) B649723
theorem B1095763 : Blo 574812 1095763 := bstep (se 1 (by rfl) ⟨821822, by rfl⟩ : syracuseStep 1095763 = 1643645) B1643645
theorem B866399 : Blo 574812 866399 := bstep (se 1 (by rfl) ⟨649799, by rfl⟩ : syracuseStep 866399 = 1299599) B1299599
theorem B866459 : Blo 574812 866459 := bstep (se 1 (by rfl) ⟨649844, by rfl⟩ : syracuseStep 866459 = 1299689) B1299689
theorem B1456289 : Blo 574812 1456289 := bstep (se 2 (by rfl) ⟨546108, by rfl⟩ : syracuseStep 1456289 = 1092217) B1092217
theorem B866495 : Blo 574812 866495 := bstep (se 1 (by rfl) ⟨649871, by rfl⟩ : syracuseStep 866495 = 1299743) B1299743
theorem B866537 : Blo 574812 866537 := bstep (se 2 (by rfl) ⟨324951, by rfl⟩ : syracuseStep 866537 = 649903) B649903
theorem B866843 : Blo 574812 866843 := bstep (se 1 (by rfl) ⟨650132, by rfl⟩ : syracuseStep 866843 = 1300265) B1300265
theorem B7092775 : Blo 574812 7092775 := bstep (se 1 (by rfl) ⟨5319581, by rfl⟩ : syracuseStep 7092775 = 10639163) B10639163
theorem B866921 : Blo 574812 866921 := bstep (se 2 (by rfl) ⟨325095, by rfl⟩ : syracuseStep 866921 = 650191) B650191
theorem B7912259 : Blo 574812 7912259 := bstep (se 1 (by rfl) ⟨5934194, by rfl⟩ : syracuseStep 7912259 = 11868389) B11868389
theorem B1456987 : Blo 574812 1456987 := bstep (se 1 (by rfl) ⟨1092740, by rfl⟩ : syracuseStep 1456987 = 2185481) B2185481
theorem B3947399 : Blo 574812 3947399 := bstep (se 1 (by rfl) ⟨2960549, by rfl⟩ : syracuseStep 3947399 = 5921099) B5921099
theorem B1227727 : Blo 574812 1227727 := bstep (se 1 (by rfl) ⟨920795, by rfl⟩ : syracuseStep 1227727 = 1841591) B1841591
theorem B1293353 : Blo 574812 1293353 := bstep (se 2 (by rfl) ⟨485007, by rfl⟩ : syracuseStep 1293353 = 970015) B970015
theorem B867449 : Blo 574812 867449 := bstep (se 2 (by rfl) ⟨325293, by rfl⟩ : syracuseStep 867449 = 650587) B650587
theorem B867551 : Blo 574812 867551 := bstep (se 1 (by rfl) ⟨650663, by rfl⟩ : syracuseStep 867551 = 1301327) B1301327
theorem B867593 : Blo 574812 867593 := bstep (se 2 (by rfl) ⟨325347, by rfl⟩ : syracuseStep 867593 = 650695) B650695
theorem B1948967 : Blo 574812 1948967 := bstep (se 1 (by rfl) ⟨1461725, by rfl⟩ : syracuseStep 1948967 = 2923451) B2923451
theorem B1555823 : Blo 574812 1555823 := bstep (se 1 (by rfl) ⟨1166867, by rfl⟩ : syracuseStep 1555823 = 2333735) B2333735
theorem B867695 : Blo 574812 867695 := bstep (se 1 (by rfl) ⟨650771, by rfl⟩ : syracuseStep 867695 = 1301543) B1301543
theorem B867815 : Blo 574812 867815 := bstep (se 1 (by rfl) ⟨650861, by rfl⟩ : syracuseStep 867815 = 1301723) B1301723
theorem B867947 : Blo 574812 867947 := bstep (se 1 (by rfl) ⟨650960, by rfl⟩ : syracuseStep 867947 = 1301921) B1301921
theorem B1851113 : Blo 574812 1851113 := bstep (se 2 (by rfl) ⟨694167, by rfl⟩ : syracuseStep 1851113 = 1388335) B1388335
theorem B868073 : Blo 574812 868073 := bstep (se 2 (by rfl) ⟨325527, by rfl⟩ : syracuseStep 868073 = 651055) B651055
theorem B868217 : Blo 574812 868217 := bstep (se 2 (by rfl) ⟨325581, by rfl⟩ : syracuseStep 868217 = 651163) B651163
theorem B1949831 : Blo 574812 1949831 := bstep (se 1 (by rfl) ⟨1462373, by rfl⟩ : syracuseStep 1949831 = 2924747) B2924747
theorem B1458395 : Blo 574812 1458395 := bstep (se 1 (by rfl) ⟨1093796, by rfl⟩ : syracuseStep 1458395 = 2187593) B2187593
theorem B1229087 : Blo 574812 1229087 := bstep (se 1 (by rfl) ⟨921815, by rfl⟩ : syracuseStep 1229087 = 1843631) B1843631
theorem B1851767 : Blo 574812 1851767 := bstep (se 1 (by rfl) ⟨1388825, by rfl⟩ : syracuseStep 1851767 = 2777651) B2777651
theorem B1852139 : Blo 574812 1852139 := bstep (se 1 (by rfl) ⟨1389104, by rfl⟩ : syracuseStep 1852139 = 2778209) B2778209
theorem B1295315 : Blo 574812 1295315 := bstep (se 1 (by rfl) ⟨971486, by rfl⟩ : syracuseStep 1295315 = 1942973) B1942973
theorem B902249 : Blo 574812 902249 := bstep (se 2 (by rfl) ⟨338343, by rfl⟩ : syracuseStep 902249 = 676687) B676687
theorem B1295567 : Blo 574812 1295567 := bstep (se 1 (by rfl) ⟨971675, by rfl⟩ : syracuseStep 1295567 = 1943351) B1943351
theorem B5260567 : Blo 574812 5260567 := bstep (se 1 (by rfl) ⟨3945425, by rfl⟩ : syracuseStep 5260567 = 7890851) B7890851
theorem B1459529 : Blo 574812 1459529 := bstep (se 2 (by rfl) ⟨547323, by rfl⟩ : syracuseStep 1459529 = 1094647) B1094647
theorem B574875 : Blo 574812 574875 := bstep (se 1 (by rfl) ⟨431156, by rfl⟩ : syracuseStep 574875 = 862313) B862313
theorem B1295891 : Blo 574812 1295891 := bstep (se 1 (by rfl) ⟨971918, by rfl⟩ : syracuseStep 1295891 = 1943837) B1943837
theorem B575087 : Blo 574812 575087 := bstep (se 1 (by rfl) ⟨431315, by rfl⟩ : syracuseStep 575087 = 862631) B862631
theorem B1951343 : Blo 574812 1951343 := bstep (se 1 (by rfl) ⟨1463507, by rfl⟩ : syracuseStep 1951343 = 2927015) B2927015
theorem B6342259 : Blo 574812 6342259 := bstep (se 1 (by rfl) ⟨4756694, by rfl⟩ : syracuseStep 6342259 = 9513389) B9513389
theorem B575143 : Blo 574812 575143 := bstep (se 1 (by rfl) ⟨431357, by rfl⟩ : syracuseStep 575143 = 862715) B862715
theorem B1951451 : Blo 574812 1951451 := bstep (se 1 (by rfl) ⟨1463588, by rfl⟩ : syracuseStep 1951451 = 2927177) B2927177
theorem B575227 : Blo 574812 575227 := bstep (se 1 (by rfl) ⟨431420, by rfl⟩ : syracuseStep 575227 = 862841) B862841
theorem B575263 : Blo 574812 575263 := bstep (se 1 (by rfl) ⟨431447, by rfl⟩ : syracuseStep 575263 = 862895) B862895
theorem B575295 : Blo 574812 575295 := bstep (se 1 (by rfl) ⟨431471, by rfl⟩ : syracuseStep 575295 = 862943) B862943
theorem B1460065 : Blo 574812 1460065 := bstep (se 2 (by rfl) ⟨547524, by rfl⟩ : syracuseStep 1460065 = 1095049) B1095049
theorem B10831745 : Blo 574812 10831745 := bstep (se 2 (by rfl) ⟨4061904, by rfl⟩ : syracuseStep 10831745 = 8123809) B8123809
theorem B575471 : Blo 574812 575471 := bstep (se 1 (by rfl) ⟨431603, by rfl⟩ : syracuseStep 575471 = 863207) B863207
theorem B3295241 : Blo 574812 3295241 := bstep (se 2 (by rfl) ⟨1235715, by rfl⟩ : syracuseStep 3295241 = 2471431) B2471431
theorem B575643 : Blo 574812 575643 := bstep (se 1 (by rfl) ⟨431732, by rfl⟩ : syracuseStep 575643 = 863465) B863465
theorem B575679 : Blo 574812 575679 := bstep (se 1 (by rfl) ⟨431759, by rfl⟩ : syracuseStep 575679 = 863519) B863519
theorem B1296575 : Blo 574812 1296575 := bstep (se 1 (by rfl) ⟨972431, by rfl⟩ : syracuseStep 1296575 = 1944863) B1944863
theorem B2771135 : Blo 574812 2771135 := bstep (se 1 (by rfl) ⟨2078351, by rfl⟩ : syracuseStep 2771135 = 4156703) B4156703
theorem B575791 : Blo 574812 575791 := bstep (se 1 (by rfl) ⟨431843, by rfl⟩ : syracuseStep 575791 = 863687) B863687
theorem B576027 : Blo 574812 576027 := bstep (se 1 (by rfl) ⟨432020, by rfl⟩ : syracuseStep 576027 = 864041) B864041
theorem B576031 : Blo 574812 576031 := bstep (se 1 (by rfl) ⟨432023, by rfl⟩ : syracuseStep 576031 = 864047) B864047
theorem B576347 : Blo 574812 576347 := bstep (se 1 (by rfl) ⟨432260, by rfl⟩ : syracuseStep 576347 = 864521) B864521
theorem B576415 : Blo 574812 576415 := bstep (se 1 (by rfl) ⟨432311, by rfl⟩ : syracuseStep 576415 = 864623) B864623
theorem B3296173 : Blo 574812 3296173 := bstep (se 3 (by rfl) ⟨618032, by rfl⟩ : syracuseStep 3296173 = 1236065) B1236065
theorem B1952747 : Blo 574812 1952747 := bstep (se 1 (by rfl) ⟨1464560, by rfl⟩ : syracuseStep 1952747 = 2929121) B2929121
theorem B1952801 : Blo 574812 1952801 := bstep (se 2 (by rfl) ⟨732300, by rfl⟩ : syracuseStep 1952801 = 1464601) B1464601
theorem B576559 : Blo 574812 576559 := bstep (se 1 (by rfl) ⟨432419, by rfl⟩ : syracuseStep 576559 = 864839) B864839
theorem B576583 : Blo 574812 576583 := bstep (se 1 (by rfl) ⟨432437, by rfl⟩ : syracuseStep 576583 = 864875) B864875
theorem B1297529 : Blo 574812 1297529 := bstep (se 2 (by rfl) ⟨486573, by rfl⟩ : syracuseStep 1297529 = 973147) B973147
theorem B576735 : Blo 574812 576735 := bstep (se 1 (by rfl) ⟨432551, by rfl⟩ : syracuseStep 576735 = 865103) B865103
theorem B3755315 : Blo 574812 3755315 := bstep (se 1 (by rfl) ⟨2816486, by rfl⟩ : syracuseStep 3755315 = 5632973) B5632973
theorem B576999 : Blo 574812 576999 := bstep (se 1 (by rfl) ⟨432749, by rfl⟩ : syracuseStep 576999 = 865499) B865499
theorem B18927089 : Blo 574812 18927089 := bstep (se 2 (by rfl) ⟨7097658, by rfl⟩ : syracuseStep 18927089 = 14195317) B14195317
theorem B970231 : Blo 574812 970231 := bstep (se 1 (by rfl) ⟨727673, by rfl⟩ : syracuseStep 970231 = 1455347) B1455347
theorem B5525081 : Blo 574812 5525081 := bstep (se 2 (by rfl) ⟨2071905, by rfl⟩ : syracuseStep 5525081 = 4143811) B4143811
theorem B577115 : Blo 574812 577115 := bstep (se 1 (by rfl) ⟨432836, by rfl⟩ : syracuseStep 577115 = 865673) B865673
theorem B1298195 : Blo 574812 1298195 := bstep (se 1 (by rfl) ⟨973646, by rfl⟩ : syracuseStep 1298195 = 1947293) B1947293
theorem B970535 : Blo 574812 970535 := bstep (se 1 (by rfl) ⟨727901, by rfl⟩ : syracuseStep 970535 = 1455803) B1455803
theorem B577351 : Blo 574812 577351 := bstep (se 1 (by rfl) ⟨433013, by rfl⟩ : syracuseStep 577351 = 866027) B866027
theorem B1462171 : Blo 574812 1462171 := bstep (se 1 (by rfl) ⟨1096628, by rfl⟩ : syracuseStep 1462171 = 2193257) B2193257
theorem B577503 : Blo 574812 577503 := bstep (se 1 (by rfl) ⟨433127, by rfl⟩ : syracuseStep 577503 = 866255) B866255
theorem B1298555 : Blo 574812 1298555 := bstep (se 1 (by rfl) ⟨973916, by rfl⟩ : syracuseStep 1298555 = 1947833) B1947833
theorem B577767 : Blo 574812 577767 := bstep (se 1 (by rfl) ⟨433325, by rfl⟩ : syracuseStep 577767 = 866651) B866651
theorem B1167671 : Blo 574812 1167671 := bstep (se 1 (by rfl) ⟨875753, by rfl⟩ : syracuseStep 1167671 = 1751507) B1751507
theorem B577919 : Blo 574812 577919 := bstep (se 1 (by rfl) ⟨433439, by rfl⟩ : syracuseStep 577919 = 866879) B866879
theorem B1298825 : Blo 574812 1298825 := bstep (se 2 (by rfl) ⟨487059, by rfl⟩ : syracuseStep 1298825 = 974119) B974119
theorem B577999 : Blo 574812 577999 := bstep (se 1 (by rfl) ⟨433499, by rfl⟩ : syracuseStep 577999 = 866999) B866999
theorem B971257 : Blo 574812 971257 := bstep (se 2 (by rfl) ⟨364221, by rfl⟩ : syracuseStep 971257 = 728443) B728443
theorem B578151 : Blo 574812 578151 := bstep (se 1 (by rfl) ⟨433613, by rfl⟩ : syracuseStep 578151 = 867227) B867227
theorem B4215545 : Blo 574812 4215545 := bstep (se 2 (by rfl) ⟨1580829, by rfl⟩ : syracuseStep 4215545 = 3161659) B3161659
theorem B971527 : Blo 574812 971527 := bstep (se 1 (by rfl) ⟨728645, by rfl⟩ : syracuseStep 971527 = 1457291) B1457291
theorem B971561 : Blo 574812 971561 := bstep (se 2 (by rfl) ⟨364335, by rfl⟩ : syracuseStep 971561 = 728671) B728671
theorem B578415 : Blo 574812 578415 := bstep (se 1 (by rfl) ⟨433811, by rfl⟩ : syracuseStep 578415 = 867623) B867623
theorem B578471 : Blo 574812 578471 := bstep (se 1 (by rfl) ⟨433853, by rfl⟩ : syracuseStep 578471 = 867707) B867707
theorem B578555 : Blo 574812 578555 := bstep (se 1 (by rfl) ⟨433916, by rfl⟩ : syracuseStep 578555 = 867833) B867833
theorem B1463305 : Blo 574812 1463305 := bstep (se 2 (by rfl) ⟨548739, by rfl⟩ : syracuseStep 1463305 = 1097479) B1097479
theorem B971831 : Blo 574812 971831 := bstep (se 1 (by rfl) ⟨728873, by rfl⟩ : syracuseStep 971831 = 1457747) B1457747
theorem B578623 : Blo 574812 578623 := bstep (se 1 (by rfl) ⟨433967, by rfl⟩ : syracuseStep 578623 = 867935) B867935
theorem B1561673 : Blo 574812 1561673 := bstep (se 2 (by rfl) ⟨585627, by rfl⟩ : syracuseStep 1561673 = 1171255) B1171255
theorem B1299563 : Blo 574812 1299563 := bstep (se 1 (by rfl) ⟨974672, by rfl⟩ : syracuseStep 1299563 = 1949345) B1949345
theorem B578767 : Blo 574812 578767 := bstep (se 1 (by rfl) ⟨434075, by rfl⟩ : syracuseStep 578767 = 868151) B868151
theorem B2184479 : Blo 574812 2184479 := bstep (se 1 (by rfl) ⟨1638359, by rfl⟩ : syracuseStep 2184479 = 3276719) B3276719
theorem B1300139 : Blo 574812 1300139 := bstep (se 1 (by rfl) ⟨975104, by rfl⟩ : syracuseStep 1300139 = 1950209) B1950209
theorem B972607 : Blo 574812 972607 := bstep (se 1 (by rfl) ⟨729455, by rfl⟩ : syracuseStep 972607 = 1458911) B1458911
theorem B1300463 : Blo 574812 1300463 := bstep (se 1 (by rfl) ⟨975347, by rfl⟩ : syracuseStep 1300463 = 1950695) B1950695
theorem B3758147 : Blo 574812 3758147 := bstep (se 1 (by rfl) ⟨2818610, by rfl⟩ : syracuseStep 3758147 = 5637221) B5637221
theorem B1038491 : Blo 574812 1038491 := bstep (se 1 (by rfl) ⟨778868, by rfl⟩ : syracuseStep 1038491 = 1557737) B1557737
theorem B1300679 : Blo 574812 1300679 := bstep (se 1 (by rfl) ⟨975509, by rfl⟩ : syracuseStep 1300679 = 1951019) B1951019
theorem B1235177 : Blo 574812 1235177 := bstep (se 2 (by rfl) ⟨463191, by rfl⟩ : syracuseStep 1235177 = 926383) B926383
theorem B8444189 : Blo 574812 8444189 := bstep (se 3 (by rfl) ⟨1583285, by rfl⟩ : syracuseStep 8444189 = 3166571) B3166571
theorem B1300859 : Blo 574812 1300859 := bstep (se 1 (by rfl) ⟨975644, by rfl⟩ : syracuseStep 1300859 = 1951289) B1951289
theorem B973343 : Blo 574812 973343 := bstep (se 1 (by rfl) ⟨730007, by rfl⟩ : syracuseStep 973343 = 1460015) B1460015
theorem B102816289 : Blo 574812 102816289 := bstep (se 2 (by rfl) ⟨38556108, by rfl⟩ : syracuseStep 102816289 = 77112217) B77112217
theorem B973417 : Blo 574812 973417 := bstep (se 2 (by rfl) ⟨365031, by rfl⟩ : syracuseStep 973417 = 730063) B730063
theorem B1301129 : Blo 574812 1301129 := bstep (se 2 (by rfl) ⟨487923, by rfl⟩ : syracuseStep 1301129 = 975847) B975847
theorem B973775 : Blo 574812 973775 := bstep (se 1 (by rfl) ⟨730331, by rfl⟩ : syracuseStep 973775 = 1460663) B1460663
theorem B1301687 : Blo 574812 1301687 := bstep (se 1 (by rfl) ⟨976265, by rfl⟩ : syracuseStep 1301687 = 1952531) B1952531
theorem B1236151 : Blo 574812 1236151 := bstep (se 1 (by rfl) ⟨927113, by rfl⟩ : syracuseStep 1236151 = 1854227) B1854227
theorem B2186635 : Blo 574812 2186635 := bstep (se 1 (by rfl) ⟨1639976, by rfl⟩ : syracuseStep 2186635 = 3279953) B3279953
theorem B974443 : Blo 574812 974443 := bstep (se 1 (by rfl) ⟨730832, by rfl⟩ : syracuseStep 974443 = 1461665) B1461665
theorem B1040105 : Blo 574812 1040105 := bstep (se 2 (by rfl) ⟨390039, by rfl⟩ : syracuseStep 1040105 = 780079) B780079
theorem B1302263 : Blo 574812 1302263 := bstep (se 1 (by rfl) ⟨976697, by rfl⟩ : syracuseStep 1302263 = 1953395) B1953395
theorem B646951 : Blo 574812 646951 := bstep (se 1 (by rfl) ⟨485213, by rfl⟩ : syracuseStep 646951 = 970427) B970427
theorem B1040249 : Blo 574812 1040249 := bstep (se 2 (by rfl) ⟨390093, by rfl⟩ : syracuseStep 1040249 = 780187) B780187
theorem B974713 : Blo 574812 974713 := bstep (se 2 (by rfl) ⟨365517, by rfl⟩ : syracuseStep 974713 = 731035) B731035
theorem B974747 : Blo 574812 974747 := bstep (se 1 (by rfl) ⟨731060, by rfl⟩ : syracuseStep 974747 = 1462121) B1462121
theorem B15392693 : Blo 574812 15392693 := bstep (se 5 (by rfl) ⟨721532, by rfl⟩ : syracuseStep 15392693 = 1443065) B1443065
theorem B1171675 : Blo 574812 1171675 := bstep (se 1 (by rfl) ⟨878756, by rfl⟩ : syracuseStep 1171675 = 1757513) B1757513
theorem B648103 : Blo 574812 648103 := bstep (se 1 (by rfl) ⟨486077, by rfl⟩ : syracuseStep 648103 = 972155) B972155
theorem B615487 : Blo 574812 615487 := bstep (se 1 (by rfl) ⟨461615, by rfl⟩ : syracuseStep 615487 = 923231) B923231
theorem B975935 : Blo 574812 975935 := bstep (se 1 (by rfl) ⟨731951, by rfl⟩ : syracuseStep 975935 = 1463903) B1463903
theorem B7005527 : Blo 574812 7005527 := bstep (se 1 (by rfl) ⟨5254145, by rfl⟩ : syracuseStep 7005527 = 10508291) B10508291
theorem B8316341 : Blo 574812 8316341 := bstep (se 5 (by rfl) ⟨389828, by rfl⟩ : syracuseStep 8316341 = 779657) B779657
theorem B2188883 : Blo 574812 2188883 := bstep (se 1 (by rfl) ⟨1641662, by rfl⟩ : syracuseStep 2188883 = 3283325) B3283325
theorem B976495 : Blo 574812 976495 := bstep (se 1 (by rfl) ⟨732371, by rfl⟩ : syracuseStep 976495 = 1464743) B1464743
theorem B976603 : Blo 574812 976603 := bstep (se 1 (by rfl) ⟨732452, by rfl⟩ : syracuseStep 976603 = 1464905) B1464905
theorem B3565601 : Blo 574812 3565601 := bstep (se 2 (by rfl) ⟨1337100, by rfl⟩ : syracuseStep 3565601 = 2674201) B2674201
theorem B2189825 : Blo 574812 2189825 := bstep (se 2 (by rfl) ⟨821184, by rfl⟩ : syracuseStep 2189825 = 1642369) B1642369
theorem B649759 : Blo 574812 649759 := bstep (se 1 (by rfl) ⟨487319, by rfl⟩ : syracuseStep 649759 = 974639) B974639
theorem B1108667 : Blo 574812 1108667 := bstep (se 1 (by rfl) ⟨831500, by rfl⟩ : syracuseStep 1108667 = 1663001) B1663001
theorem B15756743 : Blo 574812 15756743 := bstep (se 1 (by rfl) ⟨11817557, by rfl⟩ : syracuseStep 15756743 = 23635115) B23635115
theorem B16576163 : Blo 574812 16576163 := bstep (se 1 (by rfl) ⟨12432122, by rfl⟩ : syracuseStep 16576163 = 24864245) B24864245
theorem B3862379 : Blo 574812 3862379 := bstep (se 1 (by rfl) ⟨2896784, by rfl⟩ : syracuseStep 3862379 = 5793569) B5793569
theorem B9369245 : Blo 574812 9369245 := bstep (se 3 (by rfl) ⟨1756733, by rfl⟩ : syracuseStep 9369245 = 3513467) B3513467
theorem B3274577 : Blo 574812 3274577 := bstep (se 2 (by rfl) ⟨1227966, by rfl⟩ : syracuseStep 3274577 = 2455933) B2455933
theorem B7403885 : Blo 574812 7403885 := bstep (se 3 (by rfl) ⟨1388228, by rfl⟩ : syracuseStep 7403885 = 2776457) B2776457
theorem B7371283 : Blo 574812 7371283 := bstep (se 1 (by rfl) ⟨5528462, by rfl⟩ : syracuseStep 7371283 = 11056925) B11056925
theorem B4914053 : Blo 574812 4914053 := bstep (se 4 (by rfl) ⟨460692, by rfl⟩ : syracuseStep 4914053 = 921385) B921385
theorem B818599 : Blo 574812 818599 := bstep (se 1 (by rfl) ⟨613949, by rfl⟩ : syracuseStep 818599 = 1227899) B1227899
theorem B2194883 : Blo 574812 2194883 := bstep (se 1 (by rfl) ⟨1646162, by rfl⟩ : syracuseStep 2194883 = 3292325) B3292325
theorem B1638269 : Blo 574812 1638269 := bstep (se 3 (by rfl) ⟨307175, by rfl⟩ : syracuseStep 1638269 = 614351) B614351
theorem B819391 : Blo 574812 819391 := bstep (se 1 (by rfl) ⟨614543, by rfl⟩ : syracuseStep 819391 = 1229087) B1229087
theorem B1639727 : Blo 574812 1639727 := bstep (se 1 (by rfl) ⟨1229795, by rfl⟩ : syracuseStep 1639727 = 2459591) B2459591
theorem B2196827 : Blo 574812 2196827 := bstep (se 1 (by rfl) ⟨1647620, by rfl⟩ : syracuseStep 2196827 = 3295241) B3295241
theorem B820649 : Blo 574812 820649 := bstep (se 2 (by rfl) ⟨307743, by rfl⟩ : syracuseStep 820649 = 615487) B615487
theorem B5867113 : Blo 574812 5867113 := bstep (se 2 (by rfl) ⟨2200167, by rfl⟩ : syracuseStep 5867113 = 4400335) B4400335
theorem B7014089 : Blo 574812 7014089 := bstep (se 2 (by rfl) ⟨2630283, by rfl⟩ : syracuseStep 7014089 = 5260567) B5260567
theorem B8456345 : Blo 574812 8456345 := bstep (se 2 (by rfl) ⟨3171129, by rfl⟩ : syracuseStep 8456345 = 6342259) B6342259
theorem B3115169 : Blo 574812 3115169 := bstep (se 2 (by rfl) ⟨1168188, by rfl⟩ : syracuseStep 3115169 = 2336377) B2336377
theorem B9832751 : Blo 574812 9832751 := bstep (se 1 (by rfl) ⟨7374563, by rfl⟩ : syracuseStep 9832751 = 14749127) B14749127
theorem B12618059 : Blo 574812 12618059 := bstep (se 1 (by rfl) ⟨9463544, by rfl⟩ : syracuseStep 12618059 = 18927089) B18927089
theorem B2624633 : Blo 574812 2624633 := bstep (se 2 (by rfl) ⟨984237, by rfl⟩ : syracuseStep 2624633 = 1968475) B1968475
theorem B3280409 : Blo 574812 3280409 := bstep (se 2 (by rfl) ⟨1230153, by rfl⟩ : syracuseStep 3280409 = 2460307) B2460307
theorem B4394897 : Blo 574812 4394897 := bstep (se 2 (by rfl) ⟨1648086, by rfl⟩ : syracuseStep 4394897 = 3296173) B3296173
theorem B692327 : Blo 574812 692327 := bstep (se 1 (by rfl) ⟨519245, by rfl⟩ : syracuseStep 692327 = 1038491) B1038491
theorem B823451 : Blo 574812 823451 := bstep (se 1 (by rfl) ⟨617588, by rfl⟩ : syracuseStep 823451 = 1235177) B1235177
theorem B693403 : Blo 574812 693403 := bstep (se 1 (by rfl) ⟨520052, by rfl⟩ : syracuseStep 693403 = 1040105) B1040105
theorem B3282119 : Blo 574812 3282119 := bstep (se 1 (by rfl) ⟨2461589, by rfl⟩ : syracuseStep 3282119 = 4923179) B4923179
theorem B2102867 : Blo 574812 2102867 := bstep (se 1 (by rfl) ⟨1577150, by rfl⟩ : syracuseStep 2102867 = 3154301) B3154301
theorem B5248891 : Blo 574812 5248891 := bstep (se 1 (by rfl) ⟨3936668, by rfl⟩ : syracuseStep 5248891 = 7873337) B7873337
theorem B5544227 : Blo 574812 5544227 := bstep (se 1 (by rfl) ⟨4158170, by rfl⟩ : syracuseStep 5544227 = 8316341) B8316341
theorem B85170649 : Blo 574812 85170649 := bstep (se 2 (by rfl) ⟨31938993, by rfl⟩ : syracuseStep 85170649 = 63877987) B63877987
theorem B4201409 : Blo 574812 4201409 := bstep (se 2 (by rfl) ⟨1575528, by rfl⟩ : syracuseStep 4201409 = 3151057) B3151057
theorem B3284009 : Blo 574812 3284009 := bstep (se 2 (by rfl) ⟨1231503, by rfl⟩ : syracuseStep 3284009 = 2463007) B2463007
theorem B2956445 : Blo 574812 2956445 := bstep (se 3 (by rfl) ⟨554333, by rfl⟩ : syracuseStep 2956445 = 1108667) B1108667
theorem B1842745 : Blo 574812 1842745 := bstep (se 2 (by rfl) ⟨691029, by rfl⟩ : syracuseStep 1842745 = 1382059) B1382059
theorem B2072137 : Blo 574812 2072137 := bstep (se 2 (by rfl) ⟨777051, by rfl⟩ : syracuseStep 2072137 = 1554103) B1554103
theorem B15802067 : Blo 574812 15802067 := bstep (se 1 (by rfl) ⟨11851550, by rfl⟩ : syracuseStep 15802067 = 23703101) B23703101
theorem B1941245 : Blo 574812 1941245 := bstep (se 3 (by rfl) ⟨363983, by rfl⟩ : syracuseStep 1941245 = 727967) B727967
theorem B11050775 : Blo 574812 11050775 := bstep (se 1 (by rfl) ⟨8288081, by rfl⟩ : syracuseStep 11050775 = 16576163) B16576163
theorem B5611373 : Blo 574812 5611373 := bstep (se 3 (by rfl) ⟨1052132, by rfl⟩ : syracuseStep 5611373 = 2104265) B2104265
theorem B44965813 : Blo 574812 44965813 := bstep (se 5 (by rfl) ⟨2107772, by rfl⟩ : syracuseStep 44965813 = 4215545) B4215545
theorem B2629847 : Blo 574812 2629847 := bstep (se 1 (by rfl) ⟨1972385, by rfl⟩ : syracuseStep 2629847 = 3944771) B3944771
theorem B9872117 : Blo 574812 9872117 := bstep (se 5 (by rfl) ⟨462755, by rfl⟩ : syracuseStep 9872117 = 925511) B925511
theorem B1843975 : Blo 574812 1843975 := bstep (se 1 (by rfl) ⟨1382981, by rfl⟩ : syracuseStep 1843975 = 2765963) B2765963
theorem B1942649 : Blo 574812 1942649 := bstep (se 2 (by rfl) ⟨728493, by rfl⟩ : syracuseStep 1942649 = 1456987) B1456987
theorem B1648201 : Blo 574812 1648201 := bstep (se 2 (by rfl) ⟨618075, by rfl⟩ : syracuseStep 1648201 = 1236151) B1236151
theorem B1091465 : Blo 574812 1091465 := bstep (se 2 (by rfl) ⟨409299, by rfl⟩ : syracuseStep 1091465 = 818599) B818599
theorem B2631599 : Blo 574812 2631599 := bstep (se 1 (by rfl) ⟨1973699, by rfl⟩ : syracuseStep 2631599 = 3947399) B3947399
theorem B862235 : Blo 574812 862235 := bstep (se 1 (by rfl) ⟨646676, by rfl⟩ : syracuseStep 862235 = 1293353) B1293353
theorem B2763001 : Blo 574812 2763001 := bstep (se 2 (by rfl) ⟨1036125, by rfl⟩ : syracuseStep 2763001 = 2072251) B2072251
theorem B862601 : Blo 574812 862601 := bstep (se 2 (by rfl) ⟨323475, by rfl⟩ : syracuseStep 862601 = 646951) B646951
theorem B1092179 : Blo 574812 1092179 := bstep (se 1 (by rfl) ⟨819134, by rfl⟩ : syracuseStep 1092179 = 1638269) B1638269
theorem B1944647 : Blo 574812 1944647 := bstep (se 1 (by rfl) ⟨1458485, by rfl⟩ : syracuseStep 1944647 = 2916971) B2916971
theorem B863543 : Blo 574812 863543 := bstep (se 1 (by rfl) ⟨647657, by rfl⟩ : syracuseStep 863543 = 1295315) B1295315
theorem B11054465 : Blo 574812 11054465 := bstep (se 2 (by rfl) ⟨4145424, by rfl⟩ : syracuseStep 11054465 = 8290849) B8290849
theorem B601499 : Blo 574812 601499 := bstep (se 1 (by rfl) ⟨451124, by rfl⟩ : syracuseStep 601499 = 902249) B902249
theorem B863711 : Blo 574812 863711 := bstep (se 1 (by rfl) ⟨647783, by rfl⟩ : syracuseStep 863711 = 1295567) B1295567
theorem B863927 : Blo 574812 863927 := bstep (se 1 (by rfl) ⟨647945, by rfl⟩ : syracuseStep 863927 = 1295891) B1295891
theorem B2928311 : Blo 574812 2928311 := bstep (se 1 (by rfl) ⟨2196233, by rfl⟩ : syracuseStep 2928311 = 4392467) B4392467
theorem B2076347 : Blo 574812 2076347 := bstep (se 1 (by rfl) ⟨1557260, by rfl⟩ : syracuseStep 2076347 = 3114521) B3114521
theorem B1093439 : Blo 574812 1093439 := bstep (se 1 (by rfl) ⟨820079, by rfl⟩ : syracuseStep 1093439 = 1640159) B1640159
theorem B3518333 : Blo 574812 3518333 := bstep (se 3 (by rfl) ⟨659687, by rfl⟩ : syracuseStep 3518333 = 1319375) B1319375
theorem B864137 : Blo 574812 864137 := bstep (se 2 (by rfl) ⟨324051, by rfl⟩ : syracuseStep 864137 = 648103) B648103
theorem B7221163 : Blo 574812 7221163 := bstep (se 1 (by rfl) ⟨5415872, by rfl⟩ : syracuseStep 7221163 = 10831745) B10831745
theorem B864383 : Blo 574812 864383 := bstep (se 1 (by rfl) ⟨648287, by rfl⟩ : syracuseStep 864383 = 1296575) B1296575
theorem B1945727 : Blo 574812 1945727 := bstep (se 1 (by rfl) ⟨1459295, by rfl⟩ : syracuseStep 1945727 = 2918591) B2918591
theorem B1847423 : Blo 574812 1847423 := bstep (se 1 (by rfl) ⟨1385567, by rfl⟩ : syracuseStep 1847423 = 2771135) B2771135
theorem B4370597 : Blo 574812 4370597 := bstep (se 4 (by rfl) ⟨409743, by rfl⟩ : syracuseStep 4370597 = 819487) B819487
theorem B1093895 : Blo 574812 1093895 := bstep (se 1 (by rfl) ⟨820421, by rfl⟩ : syracuseStep 1093895 = 1640843) B1640843
theorem B2077127 : Blo 574812 2077127 := bstep (se 1 (by rfl) ⟨1557845, by rfl⟩ : syracuseStep 2077127 = 3115691) B3115691
theorem B865019 : Blo 574812 865019 := bstep (se 1 (by rfl) ⟨648764, by rfl⟩ : syracuseStep 865019 = 1297529) B1297529
theorem B2503543 : Blo 574812 2503543 := bstep (se 1 (by rfl) ⟨1877657, by rfl⟩ : syracuseStep 2503543 = 3755315) B3755315
theorem B3683387 : Blo 574812 3683387 := bstep (se 1 (by rfl) ⟨2762540, by rfl⟩ : syracuseStep 3683387 = 5525081) B5525081
theorem B2929769 : Blo 574812 2929769 := bstep (se 2 (by rfl) ⟨1098663, by rfl⟩ : syracuseStep 2929769 = 2197327) B2197327
theorem B1946753 : Blo 574812 1946753 := bstep (se 2 (by rfl) ⟨730032, by rfl⟩ : syracuseStep 1946753 = 1460065) B1460065
theorem B865463 : Blo 574812 865463 := bstep (se 1 (by rfl) ⟨649097, by rfl⟩ : syracuseStep 865463 = 1298195) B1298195
theorem B865703 : Blo 574812 865703 := bstep (se 1 (by rfl) ⟨649277, by rfl⟩ : syracuseStep 865703 = 1298555) B1298555
theorem B865883 : Blo 574812 865883 := bstep (se 1 (by rfl) ⟨649412, by rfl⟩ : syracuseStep 865883 = 1298825) B1298825
theorem B1947563 : Blo 574812 1947563 := bstep (se 1 (by rfl) ⟨1460672, by rfl⟩ : syracuseStep 1947563 = 2921345) B2921345
theorem B866345 : Blo 574812 866345 := bstep (se 2 (by rfl) ⟨324879, by rfl⟩ : syracuseStep 866345 = 649759) B649759
theorem B866375 : Blo 574812 866375 := bstep (se 1 (by rfl) ⟨649781, by rfl⟩ : syracuseStep 866375 = 1299563) B1299563
theorem B5552225 : Blo 574812 5552225 := bstep (se 2 (by rfl) ⟨2082084, by rfl⟩ : syracuseStep 5552225 = 4164169) B4164169
theorem B1456319 : Blo 574812 1456319 := bstep (se 1 (by rfl) ⟨1092239, by rfl⟩ : syracuseStep 1456319 = 2184479) B2184479
theorem B1948103 : Blo 574812 1948103 := bstep (se 1 (by rfl) ⟨1461077, by rfl⟩ : syracuseStep 1948103 = 2922155) B2922155
theorem B866759 : Blo 574812 866759 := bstep (se 1 (by rfl) ⟨650069, by rfl⟩ : syracuseStep 866759 = 1300139) B1300139
theorem B1948319 : Blo 574812 1948319 := bstep (se 1 (by rfl) ⟨1461239, by rfl⟩ : syracuseStep 1948319 = 2922479) B2922479
theorem B866975 : Blo 574812 866975 := bstep (se 1 (by rfl) ⟨650231, by rfl⟩ : syracuseStep 866975 = 1300463) B1300463
theorem B2505431 : Blo 574812 2505431 := bstep (se 1 (by rfl) ⟨1879073, by rfl⟩ : syracuseStep 2505431 = 3758147) B3758147
theorem B867119 : Blo 574812 867119 := bstep (se 1 (by rfl) ⟨650339, by rfl⟩ : syracuseStep 867119 = 1300679) B1300679
theorem B867239 : Blo 574812 867239 := bstep (se 1 (by rfl) ⟨650429, by rfl⟩ : syracuseStep 867239 = 1300859) B1300859
theorem B867419 : Blo 574812 867419 := bstep (se 1 (by rfl) ⟨650564, by rfl⟩ : syracuseStep 867419 = 1301129) B1301129
theorem B1293641 : Blo 574812 1293641 := bstep (se 2 (by rfl) ⟨485115, by rfl⟩ : syracuseStep 1293641 = 970231) B970231
theorem B1097039 : Blo 574812 1097039 := bstep (se 1 (by rfl) ⟨822779, by rfl⟩ : syracuseStep 1097039 = 1645559) B1645559
theorem B867791 : Blo 574812 867791 := bstep (se 1 (by rfl) ⟨650843, by rfl⟩ : syracuseStep 867791 = 1301687) B1301687
theorem B1949291 : Blo 574812 1949291 := bstep (se 1 (by rfl) ⟨1461968, by rfl⟩ : syracuseStep 1949291 = 2923937) B2923937
theorem B1097327 : Blo 574812 1097327 := bstep (se 1 (by rfl) ⟨822995, by rfl⟩ : syracuseStep 1097327 = 1645991) B1645991
theorem B1294055 : Blo 574812 1294055 := bstep (se 1 (by rfl) ⟨970541, by rfl⟩ : syracuseStep 1294055 = 1941083) B1941083
theorem B868175 : Blo 574812 868175 := bstep (se 1 (by rfl) ⟨651131, by rfl⟩ : syracuseStep 868175 = 1302263) B1302263
theorem B1949561 : Blo 574812 1949561 := bstep (se 2 (by rfl) ⟨731085, by rfl⟩ : syracuseStep 1949561 = 1462171) B1462171
theorem B1294523 : Blo 574812 1294523 := bstep (se 1 (by rfl) ⟨970892, by rfl⟩ : syracuseStep 1294523 = 1941785) B1941785
theorem B1458425 : Blo 574812 1458425 := bstep (se 2 (by rfl) ⟨546909, by rfl⟩ : syracuseStep 1458425 = 1093819) B1093819
theorem B1294631 : Blo 574812 1294631 := bstep (se 1 (by rfl) ⟨970973, by rfl⟩ : syracuseStep 1294631 = 1941947) B1941947
theorem B1295009 : Blo 574812 1295009 := bstep (se 2 (by rfl) ⟨485628, by rfl⟩ : syracuseStep 1295009 = 971257) B971257
theorem B1459073 : Blo 574812 1459073 := bstep (se 2 (by rfl) ⟨547152, by rfl⟩ : syracuseStep 1459073 = 1094305) B1094305
theorem B4670351 : Blo 574812 4670351 := bstep (se 1 (by rfl) ⟨3502763, by rfl⟩ : syracuseStep 4670351 = 7005527) B7005527
theorem B1295369 : Blo 574812 1295369 := bstep (se 2 (by rfl) ⟨485763, by rfl⟩ : syracuseStep 1295369 = 971527) B971527
theorem B1459255 : Blo 574812 1459255 := bstep (se 1 (by rfl) ⟨1094441, by rfl⟩ : syracuseStep 1459255 = 2188883) B2188883
theorem B1295423 : Blo 574812 1295423 := bstep (se 1 (by rfl) ⟨971567, by rfl⟩ : syracuseStep 1295423 = 1943135) B1943135
theorem B5555375 : Blo 574812 5555375 := bstep (se 1 (by rfl) ⟨4166531, by rfl⟩ : syracuseStep 5555375 = 8333063) B8333063
theorem B1950911 : Blo 574812 1950911 := bstep (se 1 (by rfl) ⟨1463183, by rfl⟩ : syracuseStep 1950911 = 2926367) B2926367
theorem B4441439 : Blo 574812 4441439 := bstep (se 1 (by rfl) ⟨3331079, by rfl⟩ : syracuseStep 4441439 = 6662159) B6662159
theorem B1951073 : Blo 574812 1951073 := bstep (se 2 (by rfl) ⟨731652, by rfl⟩ : syracuseStep 1951073 = 1463305) B1463305
theorem B2377067 : Blo 574812 2377067 := bstep (se 1 (by rfl) ⟨1782800, by rfl⟩ : syracuseStep 2377067 = 3565601) B3565601
theorem B575003 : Blo 574812 575003 := bstep (se 1 (by rfl) ⟨431252, by rfl⟩ : syracuseStep 575003 = 862505) B862505
theorem B575007 : Blo 574812 575007 := bstep (se 1 (by rfl) ⟨431255, by rfl⟩ : syracuseStep 575007 = 862511) B862511
theorem B1459883 : Blo 574812 1459883 := bstep (se 1 (by rfl) ⟨1094912, by rfl⟩ : syracuseStep 1459883 = 2189825) B2189825
theorem B575167 : Blo 574812 575167 := bstep (se 1 (by rfl) ⟨431375, by rfl⟩ : syracuseStep 575167 = 862751) B862751
theorem B575423 : Blo 574812 575423 := bstep (se 1 (by rfl) ⟨431567, by rfl⟩ : syracuseStep 575423 = 863135) B863135
theorem B575455 : Blo 574812 575455 := bstep (se 1 (by rfl) ⟨431591, by rfl⟩ : syracuseStep 575455 = 863183) B863183
theorem B1296359 : Blo 574812 1296359 := bstep (se 1 (by rfl) ⟨972269, by rfl⟩ : syracuseStep 1296359 = 1944539) B1944539
theorem B575515 : Blo 574812 575515 := bstep (se 1 (by rfl) ⟨431636, by rfl⟩ : syracuseStep 575515 = 863273) B863273
theorem B575519 : Blo 574812 575519 := bstep (se 1 (by rfl) ⟨431639, by rfl⟩ : syracuseStep 575519 = 863279) B863279
theorem B1951775 : Blo 574812 1951775 := bstep (se 1 (by rfl) ⟨1463831, by rfl⟩ : syracuseStep 1951775 = 2927663) B2927663
theorem B575535 : Blo 574812 575535 := bstep (se 1 (by rfl) ⟨431651, by rfl⟩ : syracuseStep 575535 = 863303) B863303
theorem B1296539 : Blo 574812 1296539 := bstep (se 1 (by rfl) ⟨972404, by rfl⟩ : syracuseStep 1296539 = 1944809) B1944809
theorem B575711 : Blo 574812 575711 := bstep (se 1 (by rfl) ⟨431783, by rfl⟩ : syracuseStep 575711 = 863567) B863567
theorem B575771 : Blo 574812 575771 := bstep (se 1 (by rfl) ⟨431828, by rfl⟩ : syracuseStep 575771 = 863657) B863657
theorem B10504495 : Blo 574812 10504495 := bstep (se 1 (by rfl) ⟨7878371, by rfl⟩ : syracuseStep 10504495 = 15756743) B15756743
theorem B1296719 : Blo 574812 1296719 := bstep (se 1 (by rfl) ⟨972539, by rfl⟩ : syracuseStep 1296719 = 1945079) B1945079
theorem B575871 : Blo 574812 575871 := bstep (se 1 (by rfl) ⟨431903, by rfl⟩ : syracuseStep 575871 = 863807) B863807
theorem B1296809 : Blo 574812 1296809 := bstep (se 2 (by rfl) ⟨486303, by rfl⟩ : syracuseStep 1296809 = 972607) B972607
theorem B576047 : Blo 574812 576047 := bstep (se 1 (by rfl) ⟨432035, by rfl⟩ : syracuseStep 576047 = 864071) B864071
theorem B2574919 : Blo 574812 2574919 := bstep (se 1 (by rfl) ⟨1931189, by rfl⟩ : syracuseStep 2574919 = 3862379) B3862379
theorem B576103 : Blo 574812 576103 := bstep (se 1 (by rfl) ⟨432077, by rfl⟩ : syracuseStep 576103 = 864155) B864155
theorem B1755751 : Blo 574812 1755751 := bstep (se 1 (by rfl) ⟨1316813, by rfl⟩ : syracuseStep 1755751 = 2633627) B2633627
theorem B1461017 : Blo 574812 1461017 := bstep (se 2 (by rfl) ⟨547881, by rfl⟩ : syracuseStep 1461017 = 1095763) B1095763
theorem B576479 : Blo 574812 576479 := bstep (se 1 (by rfl) ⟨432359, by rfl⟩ : syracuseStep 576479 = 864719) B864719
theorem B576507 : Blo 574812 576507 := bstep (se 1 (by rfl) ⟨432380, by rfl⟩ : syracuseStep 576507 = 864761) B864761
theorem B1297403 : Blo 574812 1297403 := bstep (se 1 (by rfl) ⟨973052, by rfl⟩ : syracuseStep 1297403 = 1946105) B1946105
theorem B576575 : Blo 574812 576575 := bstep (se 1 (by rfl) ⟨432431, by rfl⟩ : syracuseStep 576575 = 864863) B864863
theorem B1297583 : Blo 574812 1297583 := bstep (se 1 (by rfl) ⟨973187, by rfl⟩ : syracuseStep 1297583 = 1946375) B1946375
theorem B2084015 : Blo 574812 2084015 := bstep (se 1 (by rfl) ⟨1563011, by rfl⟩ : syracuseStep 2084015 = 3126023) B3126023
theorem B1297619 : Blo 574812 1297619 := bstep (se 1 (by rfl) ⟨973214, by rfl⟩ : syracuseStep 1297619 = 1946429) B1946429
theorem B9096425 : Blo 574812 9096425 := bstep (se 2 (by rfl) ⟨3411159, by rfl⟩ : syracuseStep 9096425 = 6822319) B6822319
theorem B576895 : Blo 574812 576895 := bstep (se 1 (by rfl) ⟨432671, by rfl⟩ : syracuseStep 576895 = 865343) B865343
theorem B137088385 : Blo 574812 137088385 := bstep (se 2 (by rfl) ⟨51408144, by rfl⟩ : syracuseStep 137088385 = 102816289) B102816289
theorem B9457033 : Blo 574812 9457033 := bstep (se 2 (by rfl) ⟨3546387, by rfl⟩ : syracuseStep 9457033 = 7092775) B7092775
theorem B576923 : Blo 574812 576923 := bstep (se 1 (by rfl) ⟨432692, by rfl⟩ : syracuseStep 576923 = 865385) B865385
theorem B576991 : Blo 574812 576991 := bstep (se 1 (by rfl) ⟨432743, by rfl⟩ : syracuseStep 576991 = 865487) B865487
theorem B1297889 : Blo 574812 1297889 := bstep (se 2 (by rfl) ⟨486708, by rfl⟩ : syracuseStep 1297889 = 973417) B973417
theorem B577127 : Blo 574812 577127 := bstep (se 1 (by rfl) ⟨432845, by rfl⟩ : syracuseStep 577127 = 865691) B865691
theorem B577275 : Blo 574812 577275 := bstep (se 1 (by rfl) ⟨432956, by rfl⟩ : syracuseStep 577275 = 865913) B865913
theorem B6246163 : Blo 574812 6246163 := bstep (se 1 (by rfl) ⟨4684622, by rfl⟩ : syracuseStep 6246163 = 9369245) B9369245
theorem B577343 : Blo 574812 577343 := bstep (se 1 (by rfl) ⟨433007, by rfl⟩ : syracuseStep 577343 = 866015) B866015
theorem B1298303 : Blo 574812 1298303 := bstep (se 1 (by rfl) ⟨973727, by rfl⟩ : syracuseStep 1298303 = 1947455) B1947455
theorem B577407 : Blo 574812 577407 := bstep (se 1 (by rfl) ⟨433055, by rfl⟩ : syracuseStep 577407 = 866111) B866111
theorem B2183051 : Blo 574812 2183051 := bstep (se 1 (by rfl) ⟨1637288, by rfl⟩ : syracuseStep 2183051 = 3274577) B3274577
theorem B577519 : Blo 574812 577519 := bstep (se 1 (by rfl) ⟨433139, by rfl⟩ : syracuseStep 577519 = 866279) B866279
theorem B577531 : Blo 574812 577531 := bstep (se 1 (by rfl) ⟨433148, by rfl⟩ : syracuseStep 577531 = 866297) B866297
theorem B577599 : Blo 574812 577599 := bstep (se 1 (by rfl) ⟨433199, by rfl⟩ : syracuseStep 577599 = 866399) B866399
theorem B577639 : Blo 574812 577639 := bstep (se 1 (by rfl) ⟨433229, by rfl⟩ : syracuseStep 577639 = 866459) B866459
theorem B970859 : Blo 574812 970859 := bstep (se 1 (by rfl) ⟨728144, by rfl⟩ : syracuseStep 970859 = 1456289) B1456289
theorem B577663 : Blo 574812 577663 := bstep (se 1 (by rfl) ⟨433247, by rfl⟩ : syracuseStep 577663 = 866495) B866495
theorem B577691 : Blo 574812 577691 := bstep (se 1 (by rfl) ⟨433268, by rfl⟩ : syracuseStep 577691 = 866537) B866537
theorem B4935923 : Blo 574812 4935923 := bstep (se 1 (by rfl) ⟨3701942, by rfl⟩ : syracuseStep 4935923 = 7403885) B7403885
theorem B577895 : Blo 574812 577895 := bstep (se 1 (by rfl) ⟨433421, by rfl⟩ : syracuseStep 577895 = 866843) B866843
theorem B577947 : Blo 574812 577947 := bstep (se 1 (by rfl) ⟨433460, by rfl⟩ : syracuseStep 577947 = 866921) B866921
theorem B4936301 : Blo 574812 4936301 := bstep (se 3 (by rfl) ⟨925556, by rfl⟩ : syracuseStep 4936301 = 1851113) B1851113
theorem B578299 : Blo 574812 578299 := bstep (se 1 (by rfl) ⟨433724, by rfl⟩ : syracuseStep 578299 = 867449) B867449
theorem B1299257 : Blo 574812 1299257 := bstep (se 2 (by rfl) ⟨487221, by rfl⟩ : syracuseStep 1299257 = 974443) B974443
theorem B578367 : Blo 574812 578367 := bstep (se 1 (by rfl) ⟨433775, by rfl⟩ : syracuseStep 578367 = 867551) B867551
theorem B578395 : Blo 574812 578395 := bstep (se 1 (by rfl) ⟨433796, by rfl⟩ : syracuseStep 578395 = 867593) B867593
theorem B1299311 : Blo 574812 1299311 := bstep (se 1 (by rfl) ⟨974483, by rfl⟩ : syracuseStep 1299311 = 1948967) B1948967
theorem B1037215 : Blo 574812 1037215 := bstep (se 1 (by rfl) ⟨777911, by rfl⟩ : syracuseStep 1037215 = 1555823) B1555823
theorem B578463 : Blo 574812 578463 := bstep (se 1 (by rfl) ⟨433847, by rfl⟩ : syracuseStep 578463 = 867695) B867695
theorem B1463255 : Blo 574812 1463255 := bstep (se 1 (by rfl) ⟨1097441, by rfl⟩ : syracuseStep 1463255 = 2194883) B2194883
theorem B2773997 : Blo 574812 2773997 := bstep (se 3 (by rfl) ⟨520124, by rfl⟩ : syracuseStep 2773997 = 1040249) B1040249
theorem B578543 : Blo 574812 578543 := bstep (se 1 (by rfl) ⟨433907, by rfl⟩ : syracuseStep 578543 = 867815) B867815
theorem B578631 : Blo 574812 578631 := bstep (se 1 (by rfl) ⟨433973, by rfl⟩ : syracuseStep 578631 = 867947) B867947
theorem B41047181 : Blo 574812 41047181 := bstep (se 3 (by rfl) ⟨7696346, by rfl⟩ : syracuseStep 41047181 = 15392693) B15392693
theorem B578715 : Blo 574812 578715 := bstep (se 1 (by rfl) ⟨434036, by rfl⟩ : syracuseStep 578715 = 868073) B868073
theorem B1299617 : Blo 574812 1299617 := bstep (se 2 (by rfl) ⟨487356, by rfl⟩ : syracuseStep 1299617 = 974713) B974713
theorem B578811 : Blo 574812 578811 := bstep (se 1 (by rfl) ⟨434108, by rfl⟩ : syracuseStep 578811 = 868217) B868217
theorem B1299887 : Blo 574812 1299887 := bstep (se 1 (by rfl) ⟨974915, by rfl⟩ : syracuseStep 1299887 = 1949831) B1949831
theorem B972263 : Blo 574812 972263 := bstep (se 1 (by rfl) ⟨729197, by rfl⟩ : syracuseStep 972263 = 1458395) B1458395
theorem B1463791 : Blo 574812 1463791 := bstep (se 1 (by rfl) ⟨1097843, by rfl⟩ : syracuseStep 1463791 = 2195687) B2195687
theorem B1234511 : Blo 574812 1234511 := bstep (se 1 (by rfl) ⟨925883, by rfl⟩ : syracuseStep 1234511 = 1851767) B1851767
theorem B972425 : Blo 574812 972425 := bstep (se 2 (by rfl) ⟨364659, by rfl⟩ : syracuseStep 972425 = 729319) B729319
theorem B5330569 : Blo 574812 5330569 := bstep (se 2 (by rfl) ⟨1998963, by rfl⟩ : syracuseStep 5330569 = 3997927) B3997927
theorem B4380317 : Blo 574812 4380317 := bstep (se 3 (by rfl) ⟨821309, by rfl⟩ : syracuseStep 4380317 = 1642619) B1642619
theorem B1463975 : Blo 574812 1463975 := bstep (se 1 (by rfl) ⟨1097981, by rfl⟩ : syracuseStep 1463975 = 2195963) B2195963
theorem B86562553 : Blo 574812 86562553 := bstep (se 2 (by rfl) ⟨32460957, by rfl⟩ : syracuseStep 86562553 = 64921915) B64921915
theorem B1464095 : Blo 574812 1464095 := bstep (se 1 (by rfl) ⟨1098071, by rfl⟩ : syracuseStep 1464095 = 2196143) B2196143
theorem B1234759 : Blo 574812 1234759 := bstep (se 1 (by rfl) ⟨926069, by rfl⟩ : syracuseStep 1234759 = 1852139) B1852139
theorem B1267849 : Blo 574812 1267849 := bstep (se 2 (by rfl) ⟨475443, by rfl⟩ : syracuseStep 1267849 = 950887) B950887
theorem B973019 : Blo 574812 973019 := bstep (se 1 (by rfl) ⟨729764, by rfl⟩ : syracuseStep 973019 = 1459529) B1459529
theorem B1300895 : Blo 574812 1300895 := bstep (se 1 (by rfl) ⟨975671, by rfl⟩ : syracuseStep 1300895 = 1951343) B1951343
theorem B1464763 : Blo 574812 1464763 := bstep (se 1 (by rfl) ⟨1098572, by rfl⟩ : syracuseStep 1464763 = 2197145) B2197145
theorem B6248933 : Blo 574812 6248933 := bstep (se 4 (by rfl) ⟨585837, by rfl⟩ : syracuseStep 6248933 = 1171675) B1171675
theorem B1300967 : Blo 574812 1300967 := bstep (se 1 (by rfl) ⟨975725, by rfl⟩ : syracuseStep 1300967 = 1951451) B1951451
theorem B973289 : Blo 574812 973289 := bstep (se 2 (by rfl) ⟨364983, by rfl⟩ : syracuseStep 973289 = 729967) B729967
theorem B18766511 : Blo 574812 18766511 := bstep (se 1 (by rfl) ⟨14074883, by rfl⟩ : syracuseStep 18766511 = 28149767) B28149767
theorem B1334087 : Blo 574812 1334087 := bstep (se 1 (by rfl) ⟨1000565, by rfl⟩ : syracuseStep 1334087 = 2001131) B2001131
theorem B2186423 : Blo 574812 2186423 := bstep (se 1 (by rfl) ⟨1639817, by rfl⟩ : syracuseStep 2186423 = 3279635) B3279635
theorem B1301831 : Blo 574812 1301831 := bstep (se 1 (by rfl) ⟨976373, by rfl⟩ : syracuseStep 1301831 = 1952747) B1952747
theorem B1301867 : Blo 574812 1301867 := bstep (se 1 (by rfl) ⟨976400, by rfl⟩ : syracuseStep 1301867 = 1952801) B1952801
theorem B4677097 : Blo 574812 4677097 := bstep (se 2 (by rfl) ⟨1753911, by rfl⟩ : syracuseStep 4677097 = 3507823) B3507823
theorem B1301993 : Blo 574812 1301993 := bstep (se 2 (by rfl) ⟨488247, by rfl⟩ : syracuseStep 1301993 = 976495) B976495
theorem B1302137 : Blo 574812 1302137 := bstep (se 2 (by rfl) ⟨488301, by rfl⟩ : syracuseStep 1302137 = 976603) B976603
theorem B647023 : Blo 574812 647023 := bstep (se 1 (by rfl) ⟨485267, by rfl⟩ : syracuseStep 647023 = 970535) B970535
theorem B778447 : Blo 574812 778447 := bstep (se 1 (by rfl) ⟨583835, by rfl⟩ : syracuseStep 778447 = 1167671) B1167671
theorem B647707 : Blo 574812 647707 := bstep (se 1 (by rfl) ⟨485780, by rfl⟩ : syracuseStep 647707 = 971561) B971561
theorem B647887 : Blo 574812 647887 := bstep (se 1 (by rfl) ⟨485915, by rfl⟩ : syracuseStep 647887 = 971831) B971831
theorem B1041115 : Blo 574812 1041115 := bstep (se 1 (by rfl) ⟨780836, by rfl⟩ : syracuseStep 1041115 = 1561673) B1561673
theorem B5629459 : Blo 574812 5629459 := bstep (se 1 (by rfl) ⟨4222094, by rfl⟩ : syracuseStep 5629459 = 8444189) B8444189
theorem B648895 : Blo 574812 648895 := bstep (se 1 (by rfl) ⟨486671, by rfl⟩ : syracuseStep 648895 = 973343) B973343
theorem B2189051 : Blo 574812 2189051 := bstep (se 1 (by rfl) ⟨1641788, by rfl⟩ : syracuseStep 2189051 = 3283577) B3283577
theorem B649183 : Blo 574812 649183 := bstep (se 1 (by rfl) ⟨486887, by rfl⟩ : syracuseStep 649183 = 973775) B973775
theorem B616495 : Blo 574812 616495 := bstep (se 1 (by rfl) ⟨462371, by rfl⟩ : syracuseStep 616495 = 924743) B924743
theorem B6547877 : Blo 574812 6547877 := bstep (se 4 (by rfl) ⟨613863, by rfl⟩ : syracuseStep 6547877 = 1227727) B1227727
theorem B2189855 : Blo 574812 2189855 := bstep (se 1 (by rfl) ⟨1642391, by rfl⟩ : syracuseStep 2189855 = 3284783) B3284783
theorem B649831 : Blo 574812 649831 := bstep (se 1 (by rfl) ⟨487373, by rfl⟩ : syracuseStep 649831 = 974747) B974747
theorem B650623 : Blo 574812 650623 := bstep (se 1 (by rfl) ⟨487967, by rfl⟩ : syracuseStep 650623 = 975935) B975935
theorem B2191967 : Blo 574812 2191967 := bstep (se 1 (by rfl) ⟨1643975, by rfl⟩ : syracuseStep 2191967 = 3287951) B3287951
theorem B2192285 : Blo 574812 2192285 := bstep (se 3 (by rfl) ⟨411053, by rfl⟩ : syracuseStep 2192285 = 822107) B822107
theorem B2192467 : Blo 574812 2192467 := bstep (se 1 (by rfl) ⟨1644350, by rfl⟩ : syracuseStep 2192467 = 3288701) B3288701
theorem B10516463 : Blo 574812 10516463 := bstep (se 1 (by rfl) ⟨7887347, by rfl⟩ : syracuseStep 10516463 = 15774695) B15774695
theorem B9828377 : Blo 574812 9828377 := bstep (se 2 (by rfl) ⟨3685641, by rfl⟩ : syracuseStep 9828377 = 7371283) B7371283
theorem B2915513 : Blo 574812 2915513 := bstep (se 2 (by rfl) ⟨1093317, by rfl⟩ : syracuseStep 2915513 = 2186635) B2186635
theorem B5274839 : Blo 574812 5274839 := bstep (se 1 (by rfl) ⟨3956129, by rfl⟩ : syracuseStep 5274839 = 7912259) B7912259
theorem B3276035 : Blo 574812 3276035 := bstep (se 1 (by rfl) ⟨2457026, by rfl⟩ : syracuseStep 3276035 = 4914053) B4914053
theorem B2195869 : Blo 574812 2195869 := bstep (se 3 (by rfl) ⟨411725, by rfl⟩ : syracuseStep 2195869 = 823451) B823451
theorem B7012925 : Blo 574812 7012925 := bstep (se 3 (by rfl) ⟨1314923, by rfl⟩ : syracuseStep 7012925 = 2629847) B2629847
theorem B3113567 : Blo 574812 3113567 := bstep (se 1 (by rfl) ⟨2335175, by rfl⟩ : syracuseStep 3113567 = 4670351) B4670351
theorem B3703583 : Blo 574812 3703583 := bstep (se 1 (by rfl) ⟨2777687, by rfl⟩ : syracuseStep 3703583 = 5555375) B5555375
theorem B2458633 : Blo 574812 2458633 := bstep (se 2 (by rfl) ⟨921987, by rfl⟩ : syracuseStep 2458633 = 1843975) B1843975
theorem B5637563 : Blo 574812 5637563 := bstep (se 1 (by rfl) ⟨4228172, by rfl⟩ : syracuseStep 5637563 = 8456345) B8456345
theorem B6555167 : Blo 574812 6555167 := bstep (se 1 (by rfl) ⟨4916375, by rfl⟩ : syracuseStep 6555167 = 9832751) B9832751
theorem B7505945 : Blo 574812 7505945 := bstep (se 2 (by rfl) ⟨2814729, by rfl⟩ : syracuseStep 7505945 = 5629459) B5629459
theorem B2197601 : Blo 574812 2197601 := bstep (se 2 (by rfl) ⟨824100, by rfl⟩ : syracuseStep 2197601 = 1648201) B1648201
theorem B6064283 : Blo 574812 6064283 := bstep (se 1 (by rfl) ⟨4548212, by rfl⟩ : syracuseStep 6064283 = 9096425) B9096425
theorem B821993 : Blo 574812 821993 := bstep (se 2 (by rfl) ⟨308247, by rfl⟩ : syracuseStep 821993 = 616495) B616495
theorem B13732901 : Blo 574812 13732901 := bstep (se 4 (by rfl) ⟨1287459, by rfl⟩ : syracuseStep 13732901 = 2574919) B2574919
theorem B27364787 : Blo 574812 27364787 := bstep (se 1 (by rfl) ⟨20523590, by rfl⟩ : syracuseStep 27364787 = 41047181) B41047181
theorem B823007 : Blo 574812 823007 := bstep (se 1 (by rfl) ⟨617255, by rfl⟩ : syracuseStep 823007 = 1234511) B1234511
theorem B2920211 : Blo 574812 2920211 := bstep (se 1 (by rfl) ⟨2190158, by rfl⟩ : syracuseStep 2920211 = 4380317) B4380317
theorem B4165955 : Blo 574812 4165955 := bstep (se 1 (by rfl) ⟨3124466, by rfl⟩ : syracuseStep 4165955 = 6248933) B6248933
theorem B889391 : Blo 574812 889391 := bstep (se 1 (by rfl) ⟨667043, by rfl⟩ : syracuseStep 889391 = 1334087) B1334087
theorem B1970963 : Blo 574812 1970963 := bstep (se 1 (by rfl) ⟨1478222, by rfl⟩ : syracuseStep 1970963 = 2956445) B2956445
theorem B8328217 : Blo 574812 8328217 := bstep (se 2 (by rfl) ⟨3123081, by rfl⟩ : syracuseStep 8328217 = 6246163) B6246163
theorem B3740915 : Blo 574812 3740915 := bstep (se 1 (by rfl) ⟨2805686, by rfl⟩ : syracuseStep 3740915 = 5611373) B5611373
theorem B727643 : Blo 574812 727643 := bstep (se 1 (by rfl) ⟨545732, by rfl⟩ : syracuseStep 727643 = 1091465) B1091465
theorem B2923289 : Blo 574812 2923289 := bstep (se 2 (by rfl) ⟨1096233, by rfl⟩ : syracuseStep 2923289 = 2192467) B2192467
theorem B4365251 : Blo 574812 4365251 := bstep (se 1 (by rfl) ⟨3273938, by rfl⟩ : syracuseStep 4365251 = 6547877) B6547877
theorem B728119 : Blo 574812 728119 := bstep (se 1 (by rfl) ⟨546089, by rfl⟩ : syracuseStep 728119 = 1092179) B1092179
theorem B115416737 : Blo 574812 115416737 := bstep (se 2 (by rfl) ⟨43281276, by rfl⟩ : syracuseStep 115416737 = 86562553) B86562553
theorem B1646345 : Blo 574812 1646345 := bstep (se 2 (by rfl) ⟨617379, by rfl⟩ : syracuseStep 1646345 = 1234759) B1234759
theorem B1384231 : Blo 574812 1384231 := bstep (se 1 (by rfl) ⟨1038173, by rfl⟩ : syracuseStep 1384231 = 2076347) B2076347
theorem B2924552213 : Blo 574812 2924552213 := bstep (se 6 (by rfl) ⟨68544192, by rfl⟩ : syracuseStep 2924552213 = 137088385) B137088385
theorem B729263 : Blo 574812 729263 := bstep (se 1 (by rfl) ⟨546947, by rfl⟩ : syracuseStep 729263 = 1093895) B1093895
theorem B1384751 : Blo 574812 1384751 := bstep (se 1 (by rfl) ⟨1038563, by rfl⟩ : syracuseStep 1384751 = 2077127) B2077127
theorem B14066237 : Blo 574812 14066237 := bstep (se 3 (by rfl) ⟨2637419, by rfl⟩ : syracuseStep 14066237 = 5274839) B5274839
theorem B2926205 : Blo 574812 2926205 := bstep (se 3 (by rfl) ⟨548663, by rfl⟩ : syracuseStep 2926205 = 1097327) B1097327
theorem B6236129 : Blo 574812 6236129 := bstep (se 2 (by rfl) ⟨2338548, by rfl⟩ : syracuseStep 6236129 = 4677097) B4677097
theorem B2762849 : Blo 574812 2762849 := bstep (se 2 (by rfl) ⟨1036068, by rfl⟩ : syracuseStep 2762849 = 2072137) B2072137
theorem B1943675 : Blo 574812 1943675 := bstep (se 1 (by rfl) ⟨1457756, by rfl⟩ : syracuseStep 1943675 = 2915513) B2915513
theorem B862427 : Blo 574812 862427 := bstep (se 1 (by rfl) ⟨646820, by rfl⟩ : syracuseStep 862427 = 1293641) B1293641
theorem B731359 : Blo 574812 731359 := bstep (se 1 (by rfl) ⟨548519, by rfl⟩ : syracuseStep 731359 = 1097039) B1097039
theorem B862697 : Blo 574812 862697 := bstep (se 2 (by rfl) ⟨323511, by rfl⟩ : syracuseStep 862697 = 647023) B647023
theorem B862703 : Blo 574812 862703 := bstep (se 1 (by rfl) ⟨647027, by rfl⟩ : syracuseStep 862703 = 1294055) B1294055
theorem B863015 : Blo 574812 863015 := bstep (se 1 (by rfl) ⟨647261, by rfl⟩ : syracuseStep 863015 = 1294523) B1294523
theorem B863087 : Blo 574812 863087 := bstep (se 1 (by rfl) ⟨647315, by rfl⟩ : syracuseStep 863087 = 1294631) B1294631
theorem B1092521 : Blo 574812 1092521 := bstep (se 2 (by rfl) ⟨409695, by rfl⟩ : syracuseStep 1092521 = 819391) B819391
theorem B1846205 : Blo 574812 1846205 := bstep (se 3 (by rfl) ⟨346163, by rfl⟩ : syracuseStep 1846205 = 692327) B692327
theorem B863339 : Blo 574812 863339 := bstep (se 1 (by rfl) ⟨647504, by rfl⟩ : syracuseStep 863339 = 1295009) B1295009
theorem B863579 : Blo 574812 863579 := bstep (se 1 (by rfl) ⟨647684, by rfl⟩ : syracuseStep 863579 = 1295369) B1295369
theorem B863609 : Blo 574812 863609 := bstep (se 2 (by rfl) ⟨323853, by rfl⟩ : syracuseStep 863609 = 647707) B647707
theorem B863615 : Blo 574812 863615 := bstep (se 1 (by rfl) ⟨647711, by rfl⟩ : syracuseStep 863615 = 1295423) B1295423
theorem B6761861 : Blo 574812 6761861 := bstep (se 4 (by rfl) ⟨633924, by rfl⟩ : syracuseStep 6761861 = 1267849) B1267849
theorem B1093151 : Blo 574812 1093151 := bstep (se 1 (by rfl) ⟨819863, by rfl⟩ : syracuseStep 1093151 = 1639727) B1639727
theorem B2960959 : Blo 574812 2960959 := bstep (se 1 (by rfl) ⟨2220719, by rfl⟩ : syracuseStep 2960959 = 4441439) B4441439
theorem B863849 : Blo 574812 863849 := bstep (se 2 (by rfl) ⟨323943, by rfl⟩ : syracuseStep 863849 = 647887) B647887
theorem B1388153 : Blo 574812 1388153 := bstep (se 2 (by rfl) ⟨520557, by rfl⟩ : syracuseStep 1388153 = 1041115) B1041115
theorem B864239 : Blo 574812 864239 := bstep (se 1 (by rfl) ⟨648179, by rfl⟩ : syracuseStep 864239 = 1296359) B1296359
theorem B1945673 : Blo 574812 1945673 := bstep (se 2 (by rfl) ⟨729627, by rfl⟩ : syracuseStep 1945673 = 1459255) B1459255
theorem B864359 : Blo 574812 864359 := bstep (se 1 (by rfl) ⟨648269, by rfl⟩ : syracuseStep 864359 = 1296539) B1296539
theorem B2076779 : Blo 574812 2076779 := bstep (se 1 (by rfl) ⟨1557584, by rfl⟩ : syracuseStep 2076779 = 3115169) B3115169
theorem B864479 : Blo 574812 864479 := bstep (se 1 (by rfl) ⟨648359, by rfl⟩ : syracuseStep 864479 = 1296719) B1296719
theorem B864539 : Blo 574812 864539 := bstep (se 1 (by rfl) ⟨648404, by rfl⟩ : syracuseStep 864539 = 1296809) B1296809
theorem B864935 : Blo 574812 864935 := bstep (se 1 (by rfl) ⟨648701, by rfl⟩ : syracuseStep 864935 = 1297403) B1297403
theorem B1749755 : Blo 574812 1749755 := bstep (se 1 (by rfl) ⟨1312316, by rfl⟩ : syracuseStep 1749755 = 2624633) B2624633
theorem B865055 : Blo 574812 865055 := bstep (se 1 (by rfl) ⟨648791, by rfl⟩ : syracuseStep 865055 = 1297583) B1297583
theorem B865079 : Blo 574812 865079 := bstep (se 1 (by rfl) ⟨648809, by rfl⟩ : syracuseStep 865079 = 1297619) B1297619
theorem B865193 : Blo 574812 865193 := bstep (se 2 (by rfl) ⟨324447, by rfl⟩ : syracuseStep 865193 = 648895) B648895
theorem B865259 : Blo 574812 865259 := bstep (se 1 (by rfl) ⟨648944, by rfl⟩ : syracuseStep 865259 = 1297889) B1297889
theorem B865535 : Blo 574812 865535 := bstep (se 1 (by rfl) ⟨649151, by rfl⟩ : syracuseStep 865535 = 1298303) B1298303
theorem B1455367 : Blo 574812 1455367 := bstep (se 1 (by rfl) ⟨1091525, by rfl⟩ : syracuseStep 1455367 = 2183051) B2183051
theorem B2929931 : Blo 574812 2929931 := bstep (se 1 (by rfl) ⟨2197448, by rfl⟩ : syracuseStep 2929931 = 4394897) B4394897
theorem B865577 : Blo 574812 865577 := bstep (se 2 (by rfl) ⟨324591, by rfl⟩ : syracuseStep 865577 = 649183) B649183
theorem B3290615 : Blo 574812 3290615 := bstep (se 1 (by rfl) ⟨2467961, by rfl⟩ : syracuseStep 3290615 = 4935923) B4935923
theorem B14005993 : Blo 574812 14005993 := bstep (se 2 (by rfl) ⟨5252247, by rfl⟩ : syracuseStep 14005993 = 10504495) B10504495
theorem B3290867 : Blo 574812 3290867 := bstep (se 1 (by rfl) ⟨2468150, by rfl⟩ : syracuseStep 3290867 = 4936301) B4936301
theorem B866171 : Blo 574812 866171 := bstep (se 1 (by rfl) ⟨649628, by rfl⟩ : syracuseStep 866171 = 1299257) B1299257
theorem B866207 : Blo 574812 866207 := bstep (se 1 (by rfl) ⟨649655, by rfl⟩ : syracuseStep 866207 = 1299311) B1299311
theorem B1849331 : Blo 574812 1849331 := bstep (se 1 (by rfl) ⟨1386998, by rfl⟩ : syracuseStep 1849331 = 2773997) B2773997
theorem B866411 : Blo 574812 866411 := bstep (se 1 (by rfl) ⟨649808, by rfl⟩ : syracuseStep 866411 = 1299617) B1299617
theorem B2341001 : Blo 574812 2341001 := bstep (se 2 (by rfl) ⟨877875, by rfl⟩ : syracuseStep 2341001 = 1755751) B1755751
theorem B866441 : Blo 574812 866441 := bstep (se 2 (by rfl) ⟨324915, by rfl⟩ : syracuseStep 866441 = 649831) B649831
theorem B6338845 : Blo 574812 6338845 := bstep (se 3 (by rfl) ⟨1188533, by rfl⟩ : syracuseStep 6338845 = 2377067) B2377067
theorem B866591 : Blo 574812 866591 := bstep (se 1 (by rfl) ⟨649943, by rfl⟩ : syracuseStep 866591 = 1299887) B1299887
theorem B867263 : Blo 574812 867263 := bstep (se 1 (by rfl) ⟨650447, by rfl⟩ : syracuseStep 867263 = 1300895) B1300895
theorem B867311 : Blo 574812 867311 := bstep (se 1 (by rfl) ⟨650483, by rfl⟩ : syracuseStep 867311 = 1300967) B1300967
theorem B867497 : Blo 574812 867497 := bstep (se 2 (by rfl) ⟨325311, by rfl⟩ : syracuseStep 867497 = 650623) B650623
theorem B2800939 : Blo 574812 2800939 := bstep (se 1 (by rfl) ⟨2100704, by rfl⟩ : syracuseStep 2800939 = 4201409) B4201409
theorem B1457615 : Blo 574812 1457615 := bstep (se 1 (by rfl) ⟨1093211, by rfl⟩ : syracuseStep 1457615 = 2186423) B2186423
theorem B867887 : Blo 574812 867887 := bstep (se 1 (by rfl) ⟨650915, by rfl⟩ : syracuseStep 867887 = 1301831) B1301831
theorem B867911 : Blo 574812 867911 := bstep (se 1 (by rfl) ⟨650933, by rfl⟩ : syracuseStep 867911 = 1301867) B1301867
theorem B867995 : Blo 574812 867995 := bstep (se 1 (by rfl) ⟨650996, by rfl⟩ : syracuseStep 867995 = 1301993) B1301993
theorem B868091 : Blo 574812 868091 := bstep (se 1 (by rfl) ⟨651068, by rfl⟩ : syracuseStep 868091 = 1302137) B1302137
theorem B10534711 : Blo 574812 10534711 := bstep (se 1 (by rfl) ⟨7901033, by rfl⟩ : syracuseStep 10534711 = 15802067) B15802067
theorem B1294163 : Blo 574812 1294163 := bstep (se 1 (by rfl) ⟨970622, by rfl⟩ : syracuseStep 1294163 = 1941245) B1941245
theorem B1295099 : Blo 574812 1295099 := bstep (se 1 (by rfl) ⟨971324, by rfl⟩ : syracuseStep 1295099 = 1942649) B1942649
theorem B1459367 : Blo 574812 1459367 := bstep (se 1 (by rfl) ⟨1094525, by rfl⟩ : syracuseStep 1459367 = 2189051) B2189051
theorem B1754399 : Blo 574812 1754399 := bstep (se 1 (by rfl) ⟨1315799, by rfl⟩ : syracuseStep 1754399 = 2631599) B2631599
theorem B574823 : Blo 574812 574823 := bstep (se 1 (by rfl) ⟨431117, by rfl⟩ : syracuseStep 574823 = 862235) B862235
theorem B575067 : Blo 574812 575067 := bstep (se 1 (by rfl) ⟨431300, by rfl⟩ : syracuseStep 575067 = 862601) B862601
theorem B1459903 : Blo 574812 1459903 := bstep (se 1 (by rfl) ⟨1094927, by rfl⟩ : syracuseStep 1459903 = 2189855) B2189855
theorem B1951721 : Blo 574812 1951721 := bstep (se 2 (by rfl) ⟨731895, by rfl⟩ : syracuseStep 1951721 = 1463791) B1463791
theorem B1296431 : Blo 574812 1296431 := bstep (se 1 (by rfl) ⟨972323, by rfl⟩ : syracuseStep 1296431 = 1944647) B1944647
theorem B575695 : Blo 574812 575695 := bstep (se 1 (by rfl) ⟨431771, by rfl⟩ : syracuseStep 575695 = 863543) B863543
theorem B575807 : Blo 574812 575807 := bstep (se 1 (by rfl) ⟨431855, by rfl⟩ : syracuseStep 575807 = 863711) B863711
theorem B575951 : Blo 574812 575951 := bstep (se 1 (by rfl) ⟨431963, by rfl⟩ : syracuseStep 575951 = 863927) B863927
theorem B1952207 : Blo 574812 1952207 := bstep (se 1 (by rfl) ⟨1464155, by rfl⟩ : syracuseStep 1952207 = 2928311) B2928311
theorem B6998521 : Blo 574812 6998521 := bstep (se 2 (by rfl) ⟨2624445, by rfl⟩ : syracuseStep 6998521 = 5248891) B5248891
theorem B2345555 : Blo 574812 2345555 := bstep (se 1 (by rfl) ⟨1759166, by rfl⟩ : syracuseStep 2345555 = 3518333) B3518333
theorem B576091 : Blo 574812 576091 := bstep (se 1 (by rfl) ⟨432068, by rfl⟩ : syracuseStep 576091 = 864137) B864137
theorem B576255 : Blo 574812 576255 := bstep (se 1 (by rfl) ⟨432191, by rfl⟩ : syracuseStep 576255 = 864383) B864383
theorem B1297151 : Blo 574812 1297151 := bstep (se 1 (by rfl) ⟨972863, by rfl⟩ : syracuseStep 1297151 = 1945727) B1945727
theorem B1231615 : Blo 574812 1231615 := bstep (se 1 (by rfl) ⟨923711, by rfl⟩ : syracuseStep 1231615 = 1847423) B1847423
theorem B1461311 : Blo 574812 1461311 := bstep (se 1 (by rfl) ⟨1095983, by rfl⟩ : syracuseStep 1461311 = 2191967) B2191967
theorem B5557373 : Blo 574812 5557373 := bstep (se 3 (by rfl) ⟨1042007, by rfl⟩ : syracuseStep 5557373 = 2084015) B2084015
theorem B576679 : Blo 574812 576679 := bstep (se 1 (by rfl) ⟨432509, by rfl⟩ : syracuseStep 576679 = 865019) B865019
theorem B1953017 : Blo 574812 1953017 := bstep (se 2 (by rfl) ⟨732381, by rfl⟩ : syracuseStep 1953017 = 1464763) B1464763
theorem B1461523 : Blo 574812 1461523 := bstep (se 1 (by rfl) ⟨1096142, by rfl⟩ : syracuseStep 1461523 = 2192285) B2192285
theorem B113560865 : Blo 574812 113560865 := bstep (se 2 (by rfl) ⟨42585324, by rfl⟩ : syracuseStep 113560865 = 85170649) B85170649
theorem B1953179 : Blo 574812 1953179 := bstep (se 1 (by rfl) ⟨1464884, by rfl⟩ : syracuseStep 1953179 = 2929769) B2929769
theorem B1297835 : Blo 574812 1297835 := bstep (se 1 (by rfl) ⟨973376, by rfl⟩ : syracuseStep 1297835 = 1946753) B1946753
theorem B576975 : Blo 574812 576975 := bstep (se 1 (by rfl) ⟨432731, by rfl⟩ : syracuseStep 576975 = 865463) B865463
theorem B577135 : Blo 574812 577135 := bstep (se 1 (by rfl) ⟨432851, by rfl⟩ : syracuseStep 577135 = 865703) B865703
theorem B577255 : Blo 574812 577255 := bstep (se 1 (by rfl) ⟨432941, by rfl⟩ : syracuseStep 577255 = 865883) B865883
theorem B1298375 : Blo 574812 1298375 := bstep (se 1 (by rfl) ⟨973781, by rfl⟩ : syracuseStep 1298375 = 1947563) B1947563
theorem B577563 : Blo 574812 577563 := bstep (se 1 (by rfl) ⟨433172, by rfl⟩ : syracuseStep 577563 = 866345) B866345
theorem B577583 : Blo 574812 577583 := bstep (se 1 (by rfl) ⟨433187, by rfl⟩ : syracuseStep 577583 = 866375) B866375
theorem B970879 : Blo 574812 970879 := bstep (se 1 (by rfl) ⟨728159, by rfl⟩ : syracuseStep 970879 = 1456319) B1456319
theorem B1298735 : Blo 574812 1298735 := bstep (se 1 (by rfl) ⟨974051, by rfl⟩ : syracuseStep 1298735 = 1948103) B1948103
theorem B577839 : Blo 574812 577839 := bstep (se 1 (by rfl) ⟨433379, by rfl⟩ : syracuseStep 577839 = 866759) B866759
theorem B1298879 : Blo 574812 1298879 := bstep (se 1 (by rfl) ⟨974159, by rfl⟩ : syracuseStep 1298879 = 1948319) B1948319
theorem B577983 : Blo 574812 577983 := bstep (se 1 (by rfl) ⟨433487, by rfl⟩ : syracuseStep 577983 = 866975) B866975
theorem B578079 : Blo 574812 578079 := bstep (se 1 (by rfl) ⟨433559, by rfl⟩ : syracuseStep 578079 = 867119) B867119
theorem B578159 : Blo 574812 578159 := bstep (se 1 (by rfl) ⟨433619, by rfl⟩ : syracuseStep 578159 = 867239) B867239
theorem B578279 : Blo 574812 578279 := bstep (se 1 (by rfl) ⟨433709, by rfl⟩ : syracuseStep 578279 = 867419) B867419
theorem B2184023 : Blo 574812 2184023 := bstep (se 1 (by rfl) ⟨1638017, by rfl⟩ : syracuseStep 2184023 = 3276035) B3276035
theorem B578527 : Blo 574812 578527 := bstep (se 1 (by rfl) ⟨433895, by rfl⟩ : syracuseStep 578527 = 867791) B867791
theorem B1299527 : Blo 574812 1299527 := bstep (se 1 (by rfl) ⟨974645, by rfl⟩ : syracuseStep 1299527 = 1949291) B1949291
theorem B578783 : Blo 574812 578783 := bstep (se 1 (by rfl) ⟨434087, by rfl⟩ : syracuseStep 578783 = 868175) B868175
theorem B59954417 : Blo 574812 59954417 := bstep (se 2 (by rfl) ⟨22482906, by rfl⟩ : syracuseStep 59954417 = 44965813) B44965813
theorem B1299707 : Blo 574812 1299707 := bstep (se 1 (by rfl) ⟨974780, by rfl⟩ : syracuseStep 1299707 = 1949561) B1949561
theorem B972283 : Blo 574812 972283 := bstep (se 1 (by rfl) ⟨729212, by rfl⟩ : syracuseStep 972283 = 1458425) B1458425
theorem B1037929 : Blo 574812 1037929 := bstep (se 2 (by rfl) ⟨389223, by rfl⟩ : syracuseStep 1037929 = 778447) B778447
theorem B972715 : Blo 574812 972715 := bstep (se 1 (by rfl) ⟨729536, by rfl⟩ : syracuseStep 972715 = 1459073) B1459073
theorem B1300607 : Blo 574812 1300607 := bstep (se 1 (by rfl) ⟨975455, by rfl⟩ : syracuseStep 1300607 = 1950911) B1950911
theorem B1464551 : Blo 574812 1464551 := bstep (se 1 (by rfl) ⟨1098413, by rfl⟩ : syracuseStep 1464551 = 2196827) B2196827
theorem B1300715 : Blo 574812 1300715 := bstep (se 1 (by rfl) ⟨975536, by rfl⟩ : syracuseStep 1300715 = 1951073) B1951073
theorem B973255 : Blo 574812 973255 := bstep (se 1 (by rfl) ⟨729941, by rfl⟩ : syracuseStep 973255 = 1459883) B1459883
theorem B4676059 : Blo 574812 4676059 := bstep (se 1 (by rfl) ⟨3507044, by rfl⟩ : syracuseStep 4676059 = 7014089) B7014089
theorem B14736005 : Blo 574812 14736005 := bstep (se 4 (by rfl) ⟨1381500, by rfl⟩ : syracuseStep 14736005 = 2763001) B2763001
theorem B1301183 : Blo 574812 1301183 := bstep (se 1 (by rfl) ⟨975887, by rfl⟩ : syracuseStep 1301183 = 1951775) B1951775
theorem B974011 : Blo 574812 974011 := bstep (se 1 (by rfl) ⟨730508, by rfl⟩ : syracuseStep 974011 = 1461017) B1461017
theorem B7822817 : Blo 574812 7822817 := bstep (se 2 (by rfl) ⟨2933556, by rfl⟩ : syracuseStep 7822817 = 5867113) B5867113
theorem B2186939 : Blo 574812 2186939 := bstep (se 1 (by rfl) ⟨1640204, by rfl⟩ : syracuseStep 2186939 = 3280409) B3280409
theorem B647239 : Blo 574812 647239 := bstep (se 1 (by rfl) ⟨485429, by rfl⟩ : syracuseStep 647239 = 970859) B970859
theorem B975503 : Blo 574812 975503 := bstep (se 1 (by rfl) ⟨731627, by rfl⟩ : syracuseStep 975503 = 1463255) B1463255
theorem B2188079 : Blo 574812 2188079 := bstep (se 1 (by rfl) ⟨1641059, by rfl⟩ : syracuseStep 2188079 = 3282119) B3282119
theorem B648175 : Blo 574812 648175 := bstep (se 1 (by rfl) ⟨486131, by rfl⟩ : syracuseStep 648175 = 972263) B972263
theorem B1401911 : Blo 574812 1401911 := bstep (se 1 (by rfl) ⟨1051433, by rfl⟩ : syracuseStep 1401911 = 2102867) B2102867
theorem B648283 : Blo 574812 648283 := bstep (se 1 (by rfl) ⟨486212, by rfl⟩ : syracuseStep 648283 = 972425) B972425
theorem B2188397 : Blo 574812 2188397 := bstep (se 3 (by rfl) ⟨410324, by rfl⟩ : syracuseStep 2188397 = 820649) B820649
theorem B975983 : Blo 574812 975983 := bstep (se 1 (by rfl) ⟨731987, by rfl⟩ : syracuseStep 975983 = 1463975) B1463975
theorem B976063 : Blo 574812 976063 := bstep (se 1 (by rfl) ⟨732047, by rfl⟩ : syracuseStep 976063 = 1464095) B1464095
theorem B648679 : Blo 574812 648679 := bstep (se 1 (by rfl) ⟨486509, by rfl⟩ : syracuseStep 648679 = 973019) B973019
theorem B3696151 : Blo 574812 3696151 := bstep (se 1 (by rfl) ⟨2772113, by rfl⟩ : syracuseStep 3696151 = 5544227) B5544227
theorem B648859 : Blo 574812 648859 := bstep (se 1 (by rfl) ⟨486644, by rfl⟩ : syracuseStep 648859 = 973289) B973289
theorem B12511007 : Blo 574812 12511007 := bstep (se 1 (by rfl) ⟨9383255, by rfl⟩ : syracuseStep 12511007 = 18766511) B18766511
theorem B12609377 : Blo 574812 12609377 := bstep (se 2 (by rfl) ⟨4728516, by rfl⟩ : syracuseStep 12609377 = 9457033) B9457033
theorem B2189339 : Blo 574812 2189339 := bstep (se 1 (by rfl) ⟨1642004, by rfl⟩ : syracuseStep 2189339 = 3284009) B3284009
theorem B5531813 : Blo 574812 5531813 := bstep (se 4 (by rfl) ⟨518607, by rfl⟩ : syracuseStep 5531813 = 1037215) B1037215
theorem B7367183 : Blo 574812 7367183 := bstep (se 1 (by rfl) ⟨5525387, by rfl⟩ : syracuseStep 7367183 = 11050775) B11050775
theorem B9628217 : Blo 574812 9628217 := bstep (se 2 (by rfl) ⟨3610581, by rfl⟩ : syracuseStep 9628217 = 7221163) B7221163
theorem B6581411 : Blo 574812 6581411 := bstep (se 1 (by rfl) ⟨4936058, by rfl⟩ : syracuseStep 6581411 = 9872117) B9872117
theorem B3698149 : Blo 574812 3698149 := bstep (se 4 (by rfl) ⟨346701, by rfl⟩ : syracuseStep 3698149 = 693403) B693403
theorem B33648157 : Blo 574812 33648157 := bstep (se 3 (by rfl) ⟨6309029, by rfl⟩ : syracuseStep 33648157 = 12618059) B12618059
theorem B3338057 : Blo 574812 3338057 := bstep (se 2 (by rfl) ⟨1251771, by rfl⟩ : syracuseStep 3338057 = 2503543) B2503543
theorem B6681149 : Blo 574812 6681149 := bstep (se 3 (by rfl) ⟨1252715, by rfl⟩ : syracuseStep 6681149 = 2505431) B2505431
theorem B7107425 : Blo 574812 7107425 := bstep (se 2 (by rfl) ⟨2665284, by rfl⟩ : syracuseStep 7107425 = 5330569) B5330569
theorem B7369643 : Blo 574812 7369643 := bstep (se 1 (by rfl) ⟨5527232, by rfl⟩ : syracuseStep 7369643 = 11054465) B11054465
theorem B2913731 : Blo 574812 2913731 := bstep (se 1 (by rfl) ⟨2185298, by rfl⟩ : syracuseStep 2913731 = 4370597) B4370597
theorem B2455591 : Blo 574812 2455591 := bstep (se 1 (by rfl) ⟨1841693, by rfl⟩ : syracuseStep 2455591 = 3683387) B3683387
theorem B1603997 : Blo 574812 1603997 := bstep (se 3 (by rfl) ⟨300749, by rfl⟩ : syracuseStep 1603997 = 601499) B601499
theorem B7010975 : Blo 574812 7010975 := bstep (se 1 (by rfl) ⟨5258231, by rfl⟩ : syracuseStep 7010975 = 10516463) B10516463
theorem B6552251 : Blo 574812 6552251 := bstep (se 1 (by rfl) ⟨4914188, by rfl⟩ : syracuseStep 6552251 = 9828377) B9828377
theorem B3701483 : Blo 574812 3701483 := bstep (se 1 (by rfl) ⟨2776112, by rfl⟩ : syracuseStep 3701483 = 5552225) B5552225
theorem B2456993 : Blo 574812 2456993 := bstep (se 2 (by rfl) ⟨921372, by rfl⟩ : syracuseStep 2456993 = 1842745) B1842745
theorem B2915837 : Blo 574812 2915837 := bstep (se 3 (by rfl) ⟨546719, by rfl⟩ : syracuseStep 2915837 = 1093439) B1093439
theorem B5538077 : Blo 574812 5538077 := bstep (se 3 (by rfl) ⟨1038389, by rfl⟩ : syracuseStep 5538077 = 2076779) B2076779
theorem B3278177 : Blo 574812 3278177 := bstep (se 2 (by rfl) ⟨1229316, by rfl⟩ : syracuseStep 3278177 = 2458633) B2458633
theorem B3704915 : Blo 574812 3704915 := bstep (se 1 (by rfl) ⟨2778686, by rfl⟩ : syracuseStep 3704915 = 5557373) B5557373
theorem B592927 : Blo 574812 592927 := bstep (se 1 (by rfl) ⟨444695, by rfl⟩ : syracuseStep 592927 = 889391) B889391
theorem B1313975 : Blo 574812 1313975 := bstep (se 1 (by rfl) ⟨985481, by rfl⟩ : syracuseStep 1313975 = 1970963) B1970963
theorem B1642153 : Blo 574812 1642153 := bstep (se 2 (by rfl) ⟨615807, by rfl⟩ : syracuseStep 1642153 = 1231615) B1231615
theorem B44864209 : Blo 574812 44864209 := bstep (se 2 (by rfl) ⟨16824078, by rfl⟩ : syracuseStep 44864209 = 33648157) B33648157
theorem B5215211 : Blo 574812 5215211 := bstep (se 1 (by rfl) ⟨3911408, by rfl⟩ : syracuseStep 5215211 = 7822817) B7822817
theorem B76944491 : Blo 574812 76944491 := bstep (se 1 (by rfl) ⟨57708368, by rfl⟩ : syracuseStep 76944491 = 115416737) B115416737
theorem B1949701475 : Blo 574812 1949701475 := bstep (se 1 (by rfl) ⟨1462276106, by rfl⟩ : syracuseStep 1949701475 = 2924552213) B2924552213
theorem B923167 : Blo 574812 923167 := bstep (se 1 (by rfl) ⟨692375, by rfl⟩ : syracuseStep 923167 = 1384751) B1384751
theorem B9377491 : Blo 574812 9377491 := bstep (se 1 (by rfl) ⟨7033118, by rfl⟩ : syracuseStep 9377491 = 14066237) B14066237
theorem B1841899 : Blo 574812 1841899 := bstep (se 1 (by rfl) ⟨1381424, by rfl⟩ : syracuseStep 1841899 = 2762849) B2762849
theorem B1940381 : Blo 574812 1940381 := bstep (se 3 (by rfl) ⟨363821, by rfl⟩ : syracuseStep 1940381 = 727643) B727643
theorem B1940489 : Blo 574812 1940489 := bstep (se 2 (by rfl) ⟨727683, by rfl⟩ : syracuseStep 1940489 = 1455367) B1455367
theorem B728347 : Blo 574812 728347 := bstep (se 1 (by rfl) ⟨546260, by rfl⟩ : syracuseStep 728347 = 1092521) B1092521
theorem B1383905 : Blo 574812 1383905 := bstep (se 2 (by rfl) ⟨518964, by rfl⟩ : syracuseStep 1383905 = 1037929) B1037929
theorem B728767 : Blo 574812 728767 := bstep (se 1 (by rfl) ⟨546575, by rfl⟩ : syracuseStep 728767 = 1093151) B1093151
theorem B925435 : Blo 574812 925435 := bstep (se 1 (by rfl) ⟨694076, by rfl⟩ : syracuseStep 925435 = 1388153) B1388153
theorem B6234745 : Blo 574812 6234745 := bstep (se 2 (by rfl) ⟨2338029, by rfl⟩ : syracuseStep 6234745 = 4676059) B4676059
theorem B1942487 : Blo 574812 1942487 := bstep (se 1 (by rfl) ⟨1456865, by rfl⟩ : syracuseStep 1942487 = 2913731) B2913731
theorem B4368167 : Blo 574812 4368167 := bstep (se 1 (by rfl) ⟨3276125, by rfl⟩ : syracuseStep 4368167 = 6552251) B6552251
theorem B2467655 : Blo 574812 2467655 := bstep (se 1 (by rfl) ⟨1850741, by rfl⟩ : syracuseStep 2467655 = 3701483) B3701483
theorem B1943891 : Blo 574812 1943891 := bstep (se 1 (by rfl) ⟨1457918, by rfl⟩ : syracuseStep 1943891 = 2915837) B2915837
theorem B1845641 : Blo 574812 1845641 := bstep (se 2 (by rfl) ⟨692115, by rfl⟩ : syracuseStep 1845641 = 1384231) B1384231
theorem B862775 : Blo 574812 862775 := bstep (se 1 (by rfl) ⟨647081, by rfl⟩ : syracuseStep 862775 = 1294163) B1294163
theorem B862985 : Blo 574812 862985 := bstep (se 2 (by rfl) ⟨323619, by rfl⟩ : syracuseStep 862985 = 647239) B647239
theorem B2075711 : Blo 574812 2075711 := bstep (se 1 (by rfl) ⟨1556783, by rfl⟩ : syracuseStep 2075711 = 3113567) B3113567
theorem B1944701 : Blo 574812 1944701 := bstep (se 3 (by rfl) ⟨364631, by rfl⟩ : syracuseStep 1944701 = 729263) B729263
theorem B863399 : Blo 574812 863399 := bstep (se 1 (by rfl) ⟨647549, by rfl⟩ : syracuseStep 863399 = 1295099) B1295099
theorem B2469055 : Blo 574812 2469055 := bstep (se 1 (by rfl) ⟨1851791, by rfl⟩ : syracuseStep 2469055 = 3703583) B3703583
theorem B2927825 : Blo 574812 2927825 := bstep (se 2 (by rfl) ⟨1097934, by rfl⟩ : syracuseStep 2927825 = 2195869) B2195869
theorem B4370111 : Blo 574812 4370111 := bstep (se 1 (by rfl) ⟨3277583, by rfl⟩ : syracuseStep 4370111 = 6555167) B6555167
theorem B864233 : Blo 574812 864233 := bstep (se 2 (by rfl) ⟨324087, by rfl⟩ : syracuseStep 864233 = 648175) B648175
theorem B864287 : Blo 574812 864287 := bstep (se 1 (by rfl) ⟨648215, by rfl⟩ : syracuseStep 864287 = 1296431) B1296431
theorem B4042855 : Blo 574812 4042855 := bstep (se 1 (by rfl) ⟨3032141, by rfl⟩ : syracuseStep 4042855 = 6064283) B6064283
theorem B864377 : Blo 574812 864377 := bstep (se 2 (by rfl) ⟨324141, by rfl⟩ : syracuseStep 864377 = 648283) B648283
theorem B864767 : Blo 574812 864767 := bstep (se 1 (by rfl) ⟨648575, by rfl⟩ : syracuseStep 864767 = 1297151) B1297151
theorem B864905 : Blo 574812 864905 := bstep (se 2 (by rfl) ⟨324339, by rfl⟩ : syracuseStep 864905 = 648679) B648679
theorem B9155267 : Blo 574812 9155267 := bstep (se 1 (by rfl) ⟨6866450, by rfl⟩ : syracuseStep 9155267 = 13732901) B13732901
theorem B4928201 : Blo 574812 4928201 := bstep (se 2 (by rfl) ⟨1848075, by rfl⟩ : syracuseStep 4928201 = 3696151) B3696151
theorem B75707243 : Blo 574812 75707243 := bstep (se 1 (by rfl) ⟨56780432, by rfl⟩ : syracuseStep 75707243 = 113560865) B113560865
theorem B865145 : Blo 574812 865145 := bstep (se 2 (by rfl) ⟨324429, by rfl⟩ : syracuseStep 865145 = 648859) B648859
theorem B1946537 : Blo 574812 1946537 := bstep (se 2 (by rfl) ⟨729951, by rfl⟩ : syracuseStep 1946537 = 1459903) B1459903
theorem B865223 : Blo 574812 865223 := bstep (se 1 (by rfl) ⟨648917, by rfl⟩ : syracuseStep 865223 = 1297835) B1297835
theorem B1946807 : Blo 574812 1946807 := bstep (se 1 (by rfl) ⟨1460105, by rfl⟩ : syracuseStep 1946807 = 2920211) B2920211
theorem B865583 : Blo 574812 865583 := bstep (se 1 (by rfl) ⟨649187, by rfl⟩ : syracuseStep 865583 = 1298375) B1298375
theorem B865823 : Blo 574812 865823 := bstep (se 1 (by rfl) ⟨649367, by rfl⟩ : syracuseStep 865823 = 1298735) B1298735
theorem B2602621 : Blo 574812 2602621 := bstep (se 3 (by rfl) ⟨487991, by rfl⟩ : syracuseStep 2602621 = 975983) B975983
theorem B865919 : Blo 574812 865919 := bstep (se 1 (by rfl) ⟨649439, by rfl⟩ : syracuseStep 865919 = 1298879) B1298879
theorem B1456015 : Blo 574812 1456015 := bstep (se 1 (by rfl) ⟨1092011, by rfl⟩ : syracuseStep 1456015 = 2184023) B2184023
theorem B9975773 : Blo 574812 9975773 := bstep (se 3 (by rfl) ⟨1870457, by rfl⟩ : syracuseStep 9975773 = 3740915) B3740915
theorem B866351 : Blo 574812 866351 := bstep (se 1 (by rfl) ⟨649763, by rfl⟩ : syracuseStep 866351 = 1299527) B1299527
theorem B866471 : Blo 574812 866471 := bstep (se 1 (by rfl) ⟨649853, by rfl⟩ : syracuseStep 866471 = 1299707) B1299707
theorem B867071 : Blo 574812 867071 := bstep (se 1 (by rfl) ⟨650303, by rfl⟩ : syracuseStep 867071 = 1300607) B1300607
theorem B867143 : Blo 574812 867143 := bstep (se 1 (by rfl) ⟨650357, by rfl⟩ : syracuseStep 867143 = 1300715) B1300715
theorem B1948697 : Blo 574812 1948697 := bstep (se 2 (by rfl) ⟨730761, by rfl⟩ : syracuseStep 1948697 = 1461523) B1461523
theorem B867455 : Blo 574812 867455 := bstep (se 1 (by rfl) ⟨650591, by rfl⟩ : syracuseStep 867455 = 1301183) B1301183
theorem B1948859 : Blo 574812 1948859 := bstep (se 1 (by rfl) ⟨1461644, by rfl⟩ : syracuseStep 1948859 = 2923289) B2923289
theorem B4930865 : Blo 574812 4930865 := bstep (se 2 (by rfl) ⟨1849074, by rfl⟩ : syracuseStep 4930865 = 3698149) B3698149
theorem B3947945 : Blo 574812 3947945 := bstep (se 2 (by rfl) ⟨1480479, by rfl⟩ : syracuseStep 3947945 = 2960959) B2960959
theorem B1457959 : Blo 574812 1457959 := bstep (se 1 (by rfl) ⟨1093469, by rfl⟩ : syracuseStep 1457959 = 2186939) B2186939
theorem B1097563 : Blo 574812 1097563 := bstep (se 1 (by rfl) ⟨823172, by rfl⟩ : syracuseStep 1097563 = 1646345) B1646345
theorem B4931549 : Blo 574812 4931549 := bstep (se 3 (by rfl) ⟨924665, by rfl⟩ : syracuseStep 4931549 = 1849331) B1849331
theorem B1294505 : Blo 574812 1294505 := bstep (se 2 (by rfl) ⟨485439, by rfl⟩ : syracuseStep 1294505 = 970879) B970879
theorem B6242669 : Blo 574812 6242669 := bstep (se 3 (by rfl) ⟨1170500, by rfl⟩ : syracuseStep 6242669 = 2341001) B2341001
theorem B1458719 : Blo 574812 1458719 := bstep (se 1 (by rfl) ⟨1094039, by rfl⟩ : syracuseStep 1458719 = 2188079) B2188079
theorem B934607 : Blo 574812 934607 := bstep (se 1 (by rfl) ⟨700955, by rfl⟩ : syracuseStep 934607 = 1401911) B1401911
theorem B1458931 : Blo 574812 1458931 := bstep (se 1 (by rfl) ⟨1094198, by rfl⟩ : syracuseStep 1458931 = 2188397) B2188397
theorem B1950803 : Blo 574812 1950803 := bstep (se 1 (by rfl) ⟨1463102, by rfl⟩ : syracuseStep 1950803 = 2926205) B2926205
theorem B8340671 : Blo 574812 8340671 := bstep (se 1 (by rfl) ⟨6255503, by rfl⟩ : syracuseStep 8340671 = 12511007) B12511007
theorem B8406251 : Blo 574812 8406251 := bstep (se 1 (by rfl) ⟨6304688, by rfl⟩ : syracuseStep 8406251 = 12609377) B12609377
theorem B1459559 : Blo 574812 1459559 := bstep (se 1 (by rfl) ⟨1094669, by rfl⟩ : syracuseStep 1459559 = 2189339) B2189339
theorem B1295783 : Blo 574812 1295783 := bstep (se 1 (by rfl) ⟨971837, by rfl⟩ : syracuseStep 1295783 = 1943675) B1943675
theorem B3687875 : Blo 574812 3687875 := bstep (se 1 (by rfl) ⟨2765906, by rfl⟩ : syracuseStep 3687875 = 5531813) B5531813
theorem B574951 : Blo 574812 574951 := bstep (se 1 (by rfl) ⟨431213, by rfl⟩ : syracuseStep 574951 = 862427) B862427
theorem B575131 : Blo 574812 575131 := bstep (se 1 (by rfl) ⟨431348, by rfl⟩ : syracuseStep 575131 = 862697) B862697
theorem B575135 : Blo 574812 575135 := bstep (se 1 (by rfl) ⟨431351, by rfl⟩ : syracuseStep 575135 = 862703) B862703
theorem B18695933 : Blo 574812 18695933 := bstep (se 3 (by rfl) ⟨3505487, by rfl⟩ : syracuseStep 18695933 = 7010975) B7010975
theorem B575343 : Blo 574812 575343 := bstep (se 1 (by rfl) ⟨431507, by rfl⟩ : syracuseStep 575343 = 863015) B863015
theorem B575391 : Blo 574812 575391 := bstep (se 1 (by rfl) ⟨431543, by rfl⟩ : syracuseStep 575391 = 863087) B863087
theorem B1230803 : Blo 574812 1230803 := bstep (se 1 (by rfl) ⟨923102, by rfl⟩ : syracuseStep 1230803 = 1846205) B1846205
theorem B1296377 : Blo 574812 1296377 := bstep (se 2 (by rfl) ⟨486141, by rfl⟩ : syracuseStep 1296377 = 972283) B972283
theorem B575559 : Blo 574812 575559 := bstep (se 1 (by rfl) ⟨431669, by rfl⟩ : syracuseStep 575559 = 863339) B863339
theorem B575719 : Blo 574812 575719 := bstep (se 1 (by rfl) ⟨431789, by rfl⟩ : syracuseStep 575719 = 863579) B863579
theorem B575739 : Blo 574812 575739 := bstep (se 1 (by rfl) ⟨431804, by rfl⟩ : syracuseStep 575739 = 863609) B863609
theorem B575743 : Blo 574812 575743 := bstep (se 1 (by rfl) ⟨431807, by rfl⟩ : syracuseStep 575743 = 863615) B863615
theorem B4507907 : Blo 574812 4507907 := bstep (se 1 (by rfl) ⟨3380930, by rfl⟩ : syracuseStep 4507907 = 6761861) B6761861
theorem B575899 : Blo 574812 575899 := bstep (se 1 (by rfl) ⟨431924, by rfl⟩ : syracuseStep 575899 = 863849) B863849
theorem B1296953 : Blo 574812 1296953 := bstep (se 2 (by rfl) ⟨486357, by rfl⟩ : syracuseStep 1296953 = 972715) B972715
theorem B576159 : Blo 574812 576159 := bstep (se 1 (by rfl) ⟨432119, by rfl⟩ : syracuseStep 576159 = 864239) B864239
theorem B1297115 : Blo 574812 1297115 := bstep (se 1 (by rfl) ⟨972836, by rfl⟩ : syracuseStep 1297115 = 1945673) B1945673
theorem B576239 : Blo 574812 576239 := bstep (se 1 (by rfl) ⟨432179, by rfl⟩ : syracuseStep 576239 = 864359) B864359
theorem B576319 : Blo 574812 576319 := bstep (se 1 (by rfl) ⟨432239, by rfl⟩ : syracuseStep 576319 = 864479) B864479
theorem B576359 : Blo 574812 576359 := bstep (se 1 (by rfl) ⟨432269, by rfl⟩ : syracuseStep 576359 = 864539) B864539
theorem B576623 : Blo 574812 576623 := bstep (se 1 (by rfl) ⟨432467, by rfl⟩ : syracuseStep 576623 = 864935) B864935
theorem B1166503 : Blo 574812 1166503 := bstep (se 1 (by rfl) ⟨874877, by rfl⟩ : syracuseStep 1166503 = 1749755) B1749755
theorem B576703 : Blo 574812 576703 := bstep (se 1 (by rfl) ⟨432527, by rfl⟩ : syracuseStep 576703 = 865055) B865055
theorem B576719 : Blo 574812 576719 := bstep (se 1 (by rfl) ⟨432539, by rfl⟩ : syracuseStep 576719 = 865079) B865079
theorem B4738283 : Blo 574812 4738283 := bstep (se 1 (by rfl) ⟨3553712, by rfl⟩ : syracuseStep 4738283 = 7107425) B7107425
theorem B1297673 : Blo 574812 1297673 := bstep (se 2 (by rfl) ⟨486627, by rfl⟩ : syracuseStep 1297673 = 973255) B973255
theorem B576795 : Blo 574812 576795 := bstep (se 1 (by rfl) ⟨432596, by rfl⟩ : syracuseStep 576795 = 865193) B865193
theorem B576839 : Blo 574812 576839 := bstep (se 1 (by rfl) ⟨432629, by rfl⟩ : syracuseStep 576839 = 865259) B865259
theorem B577023 : Blo 574812 577023 := bstep (se 1 (by rfl) ⟨432767, by rfl⟩ : syracuseStep 577023 = 865535) B865535
theorem B1953287 : Blo 574812 1953287 := bstep (se 1 (by rfl) ⟨1464965, by rfl⟩ : syracuseStep 1953287 = 2929931) B2929931
theorem B577051 : Blo 574812 577051 := bstep (se 1 (by rfl) ⟨432788, by rfl⟩ : syracuseStep 577051 = 865577) B865577
theorem B577447 : Blo 574812 577447 := bstep (se 1 (by rfl) ⟨433085, by rfl⟩ : syracuseStep 577447 = 866171) B866171
theorem B577471 : Blo 574812 577471 := bstep (se 1 (by rfl) ⟨433103, by rfl⟩ : syracuseStep 577471 = 866207) B866207
theorem B577607 : Blo 574812 577607 := bstep (se 1 (by rfl) ⟨433205, by rfl⟩ : syracuseStep 577607 = 866411) B866411
theorem B970825 : Blo 574812 970825 := bstep (se 2 (by rfl) ⟨364059, by rfl⟩ : syracuseStep 970825 = 728119) B728119
theorem B577627 : Blo 574812 577627 := bstep (se 1 (by rfl) ⟨433220, by rfl⟩ : syracuseStep 577627 = 866441) B866441
theorem B577727 : Blo 574812 577727 := bstep (se 1 (by rfl) ⟨433295, by rfl⟩ : syracuseStep 577727 = 866591) B866591
theorem B1298681 : Blo 574812 1298681 := bstep (se 2 (by rfl) ⟨487005, by rfl⟩ : syracuseStep 1298681 = 974011) B974011
theorem B1069331 : Blo 574812 1069331 := bstep (se 1 (by rfl) ⟨801998, by rfl⟩ : syracuseStep 1069331 = 1603997) B1603997
theorem B578175 : Blo 574812 578175 := bstep (se 1 (by rfl) ⟨433631, by rfl⟩ : syracuseStep 578175 = 867263) B867263
theorem B578207 : Blo 574812 578207 := bstep (se 1 (by rfl) ⟨433655, by rfl⟩ : syracuseStep 578207 = 867311) B867311
theorem B578331 : Blo 574812 578331 := bstep (se 1 (by rfl) ⟨433748, by rfl⟩ : syracuseStep 578331 = 867497) B867497
theorem B8901485 : Blo 574812 8901485 := bstep (se 3 (by rfl) ⟨1669028, by rfl⟩ : syracuseStep 8901485 = 3338057) B3338057
theorem B971743 : Blo 574812 971743 := bstep (se 1 (by rfl) ⟨728807, by rfl⟩ : syracuseStep 971743 = 1457615) B1457615
theorem B578591 : Blo 574812 578591 := bstep (se 1 (by rfl) ⟨433943, by rfl⟩ : syracuseStep 578591 = 867887) B867887
theorem B578607 : Blo 574812 578607 := bstep (se 1 (by rfl) ⟨433955, by rfl⟩ : syracuseStep 578607 = 867911) B867911
theorem B14046281 : Blo 574812 14046281 := bstep (se 2 (by rfl) ⟨5267355, by rfl⟩ : syracuseStep 14046281 = 10534711) B10534711
theorem B578663 : Blo 574812 578663 := bstep (se 1 (by rfl) ⟨433997, by rfl⟩ : syracuseStep 578663 = 867995) B867995
theorem B578727 : Blo 574812 578727 := bstep (se 1 (by rfl) ⟨434045, by rfl⟩ : syracuseStep 578727 = 868091) B868091
theorem B4675283 : Blo 574812 4675283 := bstep (se 1 (by rfl) ⟨3506462, by rfl⟩ : syracuseStep 4675283 = 7012925) B7012925
theorem B972911 : Blo 574812 972911 := bstep (se 1 (by rfl) ⟨729683, by rfl⟩ : syracuseStep 972911 = 1459367) B1459367
theorem B3758375 : Blo 574812 3758375 := bstep (se 1 (by rfl) ⟨2818781, by rfl⟩ : syracuseStep 3758375 = 5637563) B5637563
theorem B1301147 : Blo 574812 1301147 := bstep (se 1 (by rfl) ⟨975860, by rfl⟩ : syracuseStep 1301147 = 1951721) B1951721
theorem B5003963 : Blo 574812 5003963 := bstep (se 1 (by rfl) ⟨3752972, by rfl⟩ : syracuseStep 5003963 = 7505945) B7505945
theorem B1465067 : Blo 574812 1465067 := bstep (se 1 (by rfl) ⟨1098800, by rfl⟩ : syracuseStep 1465067 = 2197601) B2197601
theorem B1301417 : Blo 574812 1301417 := bstep (se 2 (by rfl) ⟨488031, by rfl⟩ : syracuseStep 1301417 = 976063) B976063
theorem B1301471 : Blo 574812 1301471 := bstep (se 1 (by rfl) ⟨976103, by rfl⟩ : syracuseStep 1301471 = 1952207) B1952207
theorem B974207 : Blo 574812 974207 := bstep (se 1 (by rfl) ⟨730655, by rfl⟩ : syracuseStep 974207 = 1461311) B1461311
theorem B1302011 : Blo 574812 1302011 := bstep (se 1 (by rfl) ⟨976508, by rfl⟩ : syracuseStep 1302011 = 1953017) B1953017
theorem B1302119 : Blo 574812 1302119 := bstep (se 1 (by rfl) ⟨976589, by rfl⟩ : syracuseStep 1302119 = 1953179) B1953179
theorem B18243191 : Blo 574812 18243191 := bstep (se 1 (by rfl) ⟨13682393, by rfl⟩ : syracuseStep 18243191 = 27364787) B27364787
theorem B2777303 : Blo 574812 2777303 := bstep (se 1 (by rfl) ⟨2082977, by rfl⟩ : syracuseStep 2777303 = 4165955) B4165955
theorem B975145 : Blo 574812 975145 := bstep (se 2 (by rfl) ⟨365679, by rfl⟩ : syracuseStep 975145 = 731359) B731359
theorem B9331361 : Blo 574812 9331361 := bstep (se 2 (by rfl) ⟨3499260, by rfl⟩ : syracuseStep 9331361 = 6998521) B6998521
theorem B4678397 : Blo 574812 4678397 := bstep (se 3 (by rfl) ⟨877199, by rfl⟩ : syracuseStep 4678397 = 1754399) B1754399
theorem B39969611 : Blo 574812 39969611 := bstep (se 1 (by rfl) ⟨29977208, by rfl⟩ : syracuseStep 39969611 = 59954417) B59954417
theorem B976367 : Blo 574812 976367 := bstep (se 1 (by rfl) ⟨732275, by rfl⟩ : syracuseStep 976367 = 1464551) B1464551
theorem B9824003 : Blo 574812 9824003 := bstep (se 1 (by rfl) ⟨7368002, by rfl⟩ : syracuseStep 9824003 = 14736005) B14736005
theorem B2910167 : Blo 574812 2910167 := bstep (se 1 (by rfl) ⟨2182625, by rfl⟩ : syracuseStep 2910167 = 4365251) B4365251
theorem B650335 : Blo 574812 650335 := bstep (se 1 (by rfl) ⟨487751, by rfl⟩ : syracuseStep 650335 = 975503) B975503
theorem B4157419 : Blo 574812 4157419 := bstep (se 1 (by rfl) ⟨3118064, by rfl⟩ : syracuseStep 4157419 = 6236129) B6236129
theorem B11104289 : Blo 574812 11104289 := bstep (se 2 (by rfl) ⟨4164108, by rfl⟩ : syracuseStep 11104289 = 8328217) B8328217
theorem B6254813 : Blo 574812 6254813 := bstep (se 3 (by rfl) ⟨1172777, by rfl⟩ : syracuseStep 6254813 = 2345555) B2345555
theorem B4911455 : Blo 574812 4911455 := bstep (se 1 (by rfl) ⟨3683591, by rfl⟩ : syracuseStep 4911455 = 7367183) B7367183
theorem B6418811 : Blo 574812 6418811 := bstep (se 1 (by rfl) ⟨4814108, by rfl⟩ : syracuseStep 6418811 = 9628217) B9628217
theorem B2191981 : Blo 574812 2191981 := bstep (se 3 (by rfl) ⟨410996, by rfl⟩ : syracuseStep 2191981 = 821993) B821993
theorem B4387607 : Blo 574812 4387607 := bstep (se 1 (by rfl) ⟨3290705, by rfl⟩ : syracuseStep 4387607 = 6581411) B6581411
theorem B18674657 : Blo 574812 18674657 := bstep (se 2 (by rfl) ⟨7002996, by rfl⟩ : syracuseStep 18674657 = 14005993) B14005993
theorem B3274121 : Blo 574812 3274121 := bstep (se 2 (by rfl) ⟨1227795, by rfl⟩ : syracuseStep 3274121 = 2455591) B2455591
theorem B8451793 : Blo 574812 8451793 := bstep (se 2 (by rfl) ⟨3169422, by rfl⟩ : syracuseStep 8451793 = 6338845) B6338845
theorem B4454099 : Blo 574812 4454099 := bstep (se 1 (by rfl) ⟨3340574, by rfl⟩ : syracuseStep 4454099 = 6681149) B6681149
theorem B4913095 : Blo 574812 4913095 := bstep (se 1 (by rfl) ⟨3684821, by rfl⟩ : syracuseStep 4913095 = 7369643) B7369643
theorem B2193743 : Blo 574812 2193743 := bstep (se 1 (by rfl) ⟨1645307, by rfl⟩ : syracuseStep 2193743 = 3290615) B3290615
theorem B2193911 : Blo 574812 2193911 := bstep (se 1 (by rfl) ⟨1645433, by rfl⟩ : syracuseStep 2193911 = 3290867) B3290867
theorem B3734585 : Blo 574812 3734585 := bstep (se 2 (by rfl) ⟨1400469, by rfl⟩ : syracuseStep 3734585 = 2800939) B2800939
theorem B2194685 : Blo 574812 2194685 := bstep (se 3 (by rfl) ⟨411503, by rfl⟩ : syracuseStep 2194685 = 823007) B823007
theorem B1637995 : Blo 574812 1637995 := bstep (se 1 (by rfl) ⟨1228496, by rfl⟩ : syracuseStep 1637995 = 2456993) B2456993
theorem B4161779 : Blo 574812 4161779 := bstep (se 1 (by rfl) ⟨3121334, by rfl⟩ : syracuseStep 4161779 = 6242669) B6242669
theorem B623071 : Blo 574812 623071 := bstep (se 1 (by rfl) ⟨467303, by rfl⟩ : syracuseStep 623071 = 934607) B934607
theorem B2851549 : Blo 574812 2851549 := bstep (se 3 (by rfl) ⟨534665, by rfl⟩ : syracuseStep 2851549 = 1069331) B1069331
theorem B5604167 : Blo 574812 5604167 := bstep (se 1 (by rfl) ⟨4203125, by rfl⟩ : syracuseStep 5604167 = 8406251) B8406251
theorem B2458583 : Blo 574812 2458583 := bstep (se 1 (by rfl) ⟨1843937, by rfl⟩ : syracuseStep 2458583 = 3687875) B3687875
theorem B820535 : Blo 574812 820535 := bstep (se 1 (by rfl) ⟨615401, by rfl⟩ : syracuseStep 820535 = 1230803) B1230803
theorem B5934323 : Blo 574812 5934323 := bstep (se 1 (by rfl) ⟨4450742, by rfl⟩ : syracuseStep 5934323 = 8901485) B8901485
theorem B3476807 : Blo 574812 3476807 := bstep (se 1 (by rfl) ⟨2607605, by rfl⟩ : syracuseStep 3476807 = 5215211) B5215211
theorem B5199203933 : Blo 574812 5199203933 := bstep (se 3 (by rfl) ⟨974850737, by rfl⟩ : syracuseStep 5199203933 = 1949701475) B1949701475
theorem B3116855 : Blo 574812 3116855 := bstep (se 1 (by rfl) ⟨2337641, by rfl⟩ : syracuseStep 3116855 = 4675283) B4675283
theorem B922603 : Blo 574812 922603 := bstep (se 1 (by rfl) ⟨691952, by rfl⟩ : syracuseStep 922603 = 1383905) B1383905
theorem B5543225 : Blo 574812 5543225 := bstep (se 2 (by rfl) ⟨2078709, by rfl⟩ : syracuseStep 5543225 = 4157419) B4157419
theorem B3118931 : Blo 574812 3118931 := bstep (se 1 (by rfl) ⟨2339198, by rfl⟩ : syracuseStep 3118931 = 4678397) B4678397
theorem B26646407 : Blo 574812 26646407 := bstep (se 1 (by rfl) ⟨19984805, by rfl⟩ : syracuseStep 26646407 = 39969611) B39969611
theorem B2922641 : Blo 574812 2922641 := bstep (se 2 (by rfl) ⟨1095990, by rfl⟩ : syracuseStep 2922641 = 2191981) B2191981
theorem B1645103 : Blo 574812 1645103 := bstep (se 1 (by rfl) ⟨1233827, by rfl⟩ : syracuseStep 1645103 = 2467655) B2467655
theorem B1940111 : Blo 574812 1940111 := bstep (se 1 (by rfl) ⟨1455083, by rfl⟩ : syracuseStep 1940111 = 2910167) B2910167
theorem B1941353 : Blo 574812 1941353 := bstep (se 2 (by rfl) ⟨728007, by rfl⟩ : syracuseStep 1941353 = 1456015) B1456015
theorem B4169875 : Blo 574812 4169875 := bstep (se 1 (by rfl) ⟨3127406, by rfl⟩ : syracuseStep 4169875 = 6254813) B6254813
theorem B6103511 : Blo 574812 6103511 := bstep (se 1 (by rfl) ⟨4577633, by rfl⟩ : syracuseStep 6103511 = 9155267) B9155267
theorem B3285467 : Blo 574812 3285467 := bstep (se 1 (by rfl) ⟨2464100, by rfl⟩ : syracuseStep 3285467 = 4928201) B4928201
theorem B2925071 : Blo 574812 2925071 := bstep (se 1 (by rfl) ⟨2193803, by rfl⟩ : syracuseStep 2925071 = 4387607) B4387607
theorem B50471495 : Blo 574812 50471495 := bstep (se 1 (by rfl) ⟨37853621, by rfl⟩ : syracuseStep 50471495 = 75707243) B75707243
theorem B10527853 : Blo 574812 10527853 := bstep (se 3 (by rfl) ⟨1973972, by rfl⟩ : syracuseStep 10527853 = 3947945) B3947945
theorem B3287243 : Blo 574812 3287243 := bstep (se 1 (by rfl) ⟨2465432, by rfl⟩ : syracuseStep 3287243 = 4930865) B4930865
theorem B1943945 : Blo 574812 1943945 := bstep (se 2 (by rfl) ⟨728979, by rfl⟩ : syracuseStep 1943945 = 1457959) B1457959
theorem B3287699 : Blo 574812 3287699 := bstep (se 1 (by rfl) ⟨2465774, by rfl⟩ : syracuseStep 3287699 = 4931549) B4931549
theorem B863003 : Blo 574812 863003 := bstep (se 1 (by rfl) ⟨647252, by rfl⟩ : syracuseStep 863003 = 1294505) B1294505
theorem B863855 : Blo 574812 863855 := bstep (se 1 (by rfl) ⟨647891, by rfl⟩ : syracuseStep 863855 = 1295783) B1295783
theorem B1945241 : Blo 574812 1945241 := bstep (se 2 (by rfl) ⟨729465, by rfl⟩ : syracuseStep 1945241 = 1458931) B1458931
theorem B17116829 : Blo 574812 17116829 := bstep (se 3 (by rfl) ⟨3209405, by rfl⟩ : syracuseStep 17116829 = 6418811) B6418811
theorem B12463955 : Blo 574812 12463955 := bstep (se 1 (by rfl) ⟨9347966, by rfl⟩ : syracuseStep 12463955 = 18695933) B18695933
theorem B864251 : Blo 574812 864251 := bstep (se 1 (by rfl) ⟨648188, by rfl⟩ : syracuseStep 864251 = 1296377) B1296377
theorem B2469943 : Blo 574812 2469943 := bstep (se 1 (by rfl) ⟨1852457, by rfl⟩ : syracuseStep 2469943 = 3704915) B3704915
theorem B864635 : Blo 574812 864635 := bstep (se 1 (by rfl) ⟨648476, by rfl⟩ : syracuseStep 864635 = 1296953) B1296953
theorem B864743 : Blo 574812 864743 := bstep (se 1 (by rfl) ⟨648557, by rfl⟩ : syracuseStep 864743 = 1297115) B1297115
theorem B3158855 : Blo 574812 3158855 := bstep (se 1 (by rfl) ⟨2369141, by rfl⟩ : syracuseStep 3158855 = 4738283) B4738283
theorem B865115 : Blo 574812 865115 := bstep (se 1 (by rfl) ⟨648836, by rfl⟩ : syracuseStep 865115 = 1297673) B1297673
theorem B865787 : Blo 574812 865787 := bstep (se 1 (by rfl) ⟨649340, by rfl⟩ : syracuseStep 865787 = 1298681) B1298681
theorem B51296327 : Blo 574812 51296327 := bstep (se 1 (by rfl) ⟨38472245, by rfl⟩ : syracuseStep 51296327 = 76944491) B76944491
theorem B867113 : Blo 574812 867113 := bstep (se 2 (by rfl) ⟨325167, by rfl⟩ : syracuseStep 867113 = 650335) B650335
theorem B2505583 : Blo 574812 2505583 := bstep (se 1 (by rfl) ⟨1879187, by rfl⟩ : syracuseStep 2505583 = 3758375) B3758375
theorem B1555337 : Blo 574812 1555337 := bstep (se 2 (by rfl) ⟨583251, by rfl⟩ : syracuseStep 1555337 = 1166503) B1166503
theorem B3292073 : Blo 574812 3292073 := bstep (se 2 (by rfl) ⟨1234527, by rfl⟩ : syracuseStep 3292073 = 2469055) B2469055
theorem B867431 : Blo 574812 867431 := bstep (se 1 (by rfl) ⟨650573, by rfl⟩ : syracuseStep 867431 = 1301147) B1301147
theorem B1293587 : Blo 574812 1293587 := bstep (se 1 (by rfl) ⟨970190, by rfl⟩ : syracuseStep 1293587 = 1940381) B1940381
theorem B867611 : Blo 574812 867611 := bstep (se 1 (by rfl) ⟨650708, by rfl⟩ : syracuseStep 867611 = 1301417) B1301417
theorem B867647 : Blo 574812 867647 := bstep (se 1 (by rfl) ⟨650735, by rfl⟩ : syracuseStep 867647 = 1301471) B1301471
theorem B1293659 : Blo 574812 1293659 := bstep (se 1 (by rfl) ⟨970244, by rfl⟩ : syracuseStep 1293659 = 1940489) B1940489
theorem B868007 : Blo 574812 868007 := bstep (se 1 (by rfl) ⟨651005, by rfl⟩ : syracuseStep 868007 = 1302011) B1302011
theorem B868079 : Blo 574812 868079 := bstep (se 1 (by rfl) ⟨651059, by rfl⟩ : syracuseStep 868079 = 1302119) B1302119
theorem B1294433 : Blo 574812 1294433 := bstep (se 2 (by rfl) ⟨485412, by rfl⟩ : syracuseStep 1294433 = 970825) B970825
theorem B5390473 : Blo 574812 5390473 := bstep (se 2 (by rfl) ⟨2021427, by rfl⟩ : syracuseStep 5390473 = 4042855) B4042855
theorem B1851535 : Blo 574812 1851535 := bstep (se 1 (by rfl) ⟨1388651, by rfl⟩ : syracuseStep 1851535 = 2777303) B2777303
theorem B3162277 : Blo 574812 3162277 := bstep (se 4 (by rfl) ⟨296463, by rfl⟩ : syracuseStep 3162277 = 592927) B592927
theorem B1294991 : Blo 574812 1294991 := bstep (se 1 (by rfl) ⟨971243, by rfl⟩ : syracuseStep 1294991 = 1942487) B1942487
theorem B59818945 : Blo 574812 59818945 := bstep (se 2 (by rfl) ⟨22432104, by rfl⟩ : syracuseStep 59818945 = 44864209) B44864209
theorem B1295657 : Blo 574812 1295657 := bstep (se 2 (by rfl) ⟨485871, by rfl⟩ : syracuseStep 1295657 = 971743) B971743
theorem B1295927 : Blo 574812 1295927 := bstep (se 1 (by rfl) ⟨971945, by rfl⟩ : syracuseStep 1295927 = 1943891) B1943891
theorem B1230427 : Blo 574812 1230427 := bstep (se 1 (by rfl) ⟨922820, by rfl⟩ : syracuseStep 1230427 = 1845641) B1845641
theorem B575183 : Blo 574812 575183 := bstep (se 1 (by rfl) ⟨431387, by rfl⟩ : syracuseStep 575183 = 862775) B862775
theorem B575323 : Blo 574812 575323 := bstep (se 1 (by rfl) ⟨431492, by rfl⟩ : syracuseStep 575323 = 862985) B862985
theorem B1230889 : Blo 574812 1230889 := bstep (se 2 (by rfl) ⟨461583, by rfl⟩ : syracuseStep 1230889 = 923167) B923167
theorem B1296467 : Blo 574812 1296467 := bstep (se 1 (by rfl) ⟨972350, by rfl⟩ : syracuseStep 1296467 = 1944701) B1944701
theorem B575599 : Blo 574812 575599 := bstep (se 1 (by rfl) ⟨431699, by rfl⟩ : syracuseStep 575599 = 863399) B863399
theorem B1951883 : Blo 574812 1951883 := bstep (se 1 (by rfl) ⟨1463912, by rfl⟩ : syracuseStep 1951883 = 2927825) B2927825
theorem B12503321 : Blo 574812 12503321 := bstep (se 2 (by rfl) ⟨4688745, by rfl⟩ : syracuseStep 12503321 = 9377491) B9377491
theorem B576155 : Blo 574812 576155 := bstep (se 1 (by rfl) ⟨432116, by rfl⟩ : syracuseStep 576155 = 864233) B864233
theorem B576191 : Blo 574812 576191 := bstep (se 1 (by rfl) ⟨432143, by rfl⟩ : syracuseStep 576191 = 864287) B864287
theorem B576251 : Blo 574812 576251 := bstep (se 1 (by rfl) ⟨432188, by rfl⟩ : syracuseStep 576251 = 864377) B864377
theorem B576511 : Blo 574812 576511 := bstep (se 1 (by rfl) ⟨432383, by rfl⟩ : syracuseStep 576511 = 864767) B864767
theorem B576603 : Blo 574812 576603 := bstep (se 1 (by rfl) ⟨432452, by rfl⟩ : syracuseStep 576603 = 864905) B864905
theorem B576763 : Blo 574812 576763 := bstep (se 1 (by rfl) ⟨432572, by rfl⟩ : syracuseStep 576763 = 865145) B865145
theorem B1297691 : Blo 574812 1297691 := bstep (se 1 (by rfl) ⟨973268, by rfl⟩ : syracuseStep 1297691 = 1946537) B1946537
theorem B576815 : Blo 574812 576815 := bstep (se 1 (by rfl) ⟨432611, by rfl⟩ : syracuseStep 576815 = 865223) B865223
theorem B1297871 : Blo 574812 1297871 := bstep (se 1 (by rfl) ⟨973403, by rfl⟩ : syracuseStep 1297871 = 1946807) B1946807
theorem B577055 : Blo 574812 577055 := bstep (se 1 (by rfl) ⟨432791, by rfl⟩ : syracuseStep 577055 = 865583) B865583
theorem B2182747 : Blo 574812 2182747 := bstep (se 1 (by rfl) ⟨1637060, by rfl⟩ : syracuseStep 2182747 = 3274121) B3274121
theorem B577215 : Blo 574812 577215 := bstep (se 1 (by rfl) ⟨432911, by rfl⟩ : syracuseStep 577215 = 865823) B865823
theorem B577279 : Blo 574812 577279 := bstep (se 1 (by rfl) ⟨432959, by rfl⟩ : syracuseStep 577279 = 865919) B865919
theorem B2969399 : Blo 574812 2969399 := bstep (se 1 (by rfl) ⟨2227049, by rfl⟩ : syracuseStep 2969399 = 4454099) B4454099
theorem B577567 : Blo 574812 577567 := bstep (se 1 (by rfl) ⟨433175, by rfl⟩ : syracuseStep 577567 = 866351) B866351
theorem B577647 : Blo 574812 577647 := bstep (se 1 (by rfl) ⟨433235, by rfl⟩ : syracuseStep 577647 = 866471) B866471
theorem B1462495 : Blo 574812 1462495 := bstep (se 1 (by rfl) ⟨1096871, by rfl⟩ : syracuseStep 1462495 = 2193743) B2193743
theorem B48648509 : Blo 574812 48648509 := bstep (se 3 (by rfl) ⟨9121595, by rfl⟩ : syracuseStep 48648509 = 18243191) B18243191
theorem B1462607 : Blo 574812 1462607 := bstep (se 1 (by rfl) ⟨1096955, by rfl⟩ : syracuseStep 1462607 = 2193911) B2193911
theorem B971129 : Blo 574812 971129 := bstep (se 2 (by rfl) ⟨364173, by rfl⟩ : syracuseStep 971129 = 728347) B728347
theorem B578047 : Blo 574812 578047 := bstep (se 1 (by rfl) ⟨433535, by rfl⟩ : syracuseStep 578047 = 867071) B867071
theorem B578095 : Blo 574812 578095 := bstep (se 1 (by rfl) ⟨433571, by rfl⟩ : syracuseStep 578095 = 867143) B867143
theorem B1299131 : Blo 574812 1299131 := bstep (se 1 (by rfl) ⟨974348, by rfl⟩ : syracuseStep 1299131 = 1948697) B1948697
theorem B578303 : Blo 574812 578303 := bstep (se 1 (by rfl) ⟨433727, by rfl⟩ : syracuseStep 578303 = 867455) B867455
theorem B1299239 : Blo 574812 1299239 := bstep (se 1 (by rfl) ⟨974429, by rfl⟩ : syracuseStep 1299239 = 1948859) B1948859
theorem B2183993 : Blo 574812 2183993 := bstep (se 2 (by rfl) ⟨818997, by rfl⟩ : syracuseStep 2183993 = 1637995) B1637995
theorem B1463123 : Blo 574812 1463123 := bstep (se 1 (by rfl) ⟨1097342, by rfl⟩ : syracuseStep 1463123 = 2194685) B2194685
theorem B971689 : Blo 574812 971689 := bstep (se 2 (by rfl) ⟨364383, by rfl⟩ : syracuseStep 971689 = 728767) B728767
theorem B1233913 : Blo 574812 1233913 := bstep (se 2 (by rfl) ⟨462717, by rfl⟩ : syracuseStep 1233913 = 925435) B925435
theorem B1463417 : Blo 574812 1463417 := bstep (se 2 (by rfl) ⟨548781, by rfl⟩ : syracuseStep 1463417 = 1097563) B1097563
theorem B3692051 : Blo 574812 3692051 := bstep (se 1 (by rfl) ⟨2769038, by rfl⟩ : syracuseStep 3692051 = 5538077) B5538077
theorem B972479 : Blo 574812 972479 := bstep (se 1 (by rfl) ⟨729359, by rfl⟩ : syracuseStep 972479 = 1458719) B1458719
theorem B1300193 : Blo 574812 1300193 := bstep (se 2 (by rfl) ⟨487572, by rfl⟩ : syracuseStep 1300193 = 975145) B975145
theorem B1300535 : Blo 574812 1300535 := bstep (se 1 (by rfl) ⟨975401, by rfl⟩ : syracuseStep 1300535 = 1950803) B1950803
theorem B8312993 : Blo 574812 8312993 := bstep (se 2 (by rfl) ⟨3117372, by rfl⟩ : syracuseStep 8312993 = 6234745) B6234745
theorem B2185451 : Blo 574812 2185451 := bstep (se 1 (by rfl) ⟨1639088, by rfl⟩ : syracuseStep 2185451 = 3278177) B3278177
theorem B973039 : Blo 574812 973039 := bstep (se 1 (by rfl) ⟨729779, by rfl⟩ : syracuseStep 973039 = 1459559) B1459559
theorem B875983 : Blo 574812 875983 := bstep (se 1 (by rfl) ⟨656987, by rfl⟩ : syracuseStep 875983 = 1313975) B1313975
theorem B1302191 : Blo 574812 1302191 := bstep (se 1 (by rfl) ⟨976643, by rfl⟩ : syracuseStep 1302191 = 1953287) B1953287
theorem B22241789 : Blo 574812 22241789 := bstep (se 3 (by rfl) ⟨4170335, by rfl⟩ : syracuseStep 22241789 = 8340671) B8340671
theorem B9364187 : Blo 574812 9364187 := bstep (se 1 (by rfl) ⟨7023140, by rfl⟩ : syracuseStep 9364187 = 14046281) B14046281
theorem B648607 : Blo 574812 648607 := bstep (se 1 (by rfl) ⟨486455, by rfl⟩ : syracuseStep 648607 = 972911) B972911
theorem B3335975 : Blo 574812 3335975 := bstep (se 1 (by rfl) ⟨2501981, by rfl⟩ : syracuseStep 3335975 = 5003963) B5003963
theorem B976711 : Blo 574812 976711 := bstep (se 1 (by rfl) ⟨732533, by rfl⟩ : syracuseStep 976711 = 1465067) B1465067
theorem B2189537 : Blo 574812 2189537 := bstep (se 2 (by rfl) ⟨821076, by rfl⟩ : syracuseStep 2189537 = 1642153) B1642153
theorem B649471 : Blo 574812 649471 := bstep (se 1 (by rfl) ⟨487103, by rfl⟩ : syracuseStep 649471 = 974207) B974207
theorem B6220907 : Blo 574812 6220907 := bstep (se 1 (by rfl) ⟨4665680, by rfl⟩ : syracuseStep 6220907 = 9331361) B9331361
theorem B12021085 : Blo 574812 12021085 := bstep (se 3 (by rfl) ⟨2253953, by rfl⟩ : syracuseStep 12021085 = 4507907) B4507907
theorem B650911 : Blo 574812 650911 := bstep (se 1 (by rfl) ⟨488183, by rfl⟩ : syracuseStep 650911 = 976367) B976367
theorem B6549335 : Blo 574812 6549335 := bstep (se 1 (by rfl) ⟨4912001, by rfl⟩ : syracuseStep 6549335 = 9824003) B9824003
theorem B2912111 : Blo 574812 2912111 := bstep (se 1 (by rfl) ⟨2184083, by rfl⟩ : syracuseStep 2912111 = 4368167) B4368167
theorem B3470161 : Blo 574812 3470161 := bstep (se 2 (by rfl) ⟨1301310, by rfl⟩ : syracuseStep 3470161 = 2602621) B2602621
theorem B11269057 : Blo 574812 11269057 := bstep (se 2 (by rfl) ⟨4225896, by rfl⟩ : syracuseStep 11269057 = 8451793) B8451793
theorem B2913407 : Blo 574812 2913407 := bstep (se 1 (by rfl) ⟨2185055, by rfl⟩ : syracuseStep 2913407 = 4370111) B4370111
theorem B6550793 : Blo 574812 6550793 := bstep (se 2 (by rfl) ⟨2456547, by rfl⟩ : syracuseStep 6550793 = 4913095) B4913095
theorem B7402859 : Blo 574812 7402859 := bstep (se 1 (by rfl) ⟨5552144, by rfl⟩ : syracuseStep 7402859 = 11104289) B11104289
theorem B5535229 : Blo 574812 5535229 := bstep (se 3 (by rfl) ⟨1037855, by rfl⟩ : syracuseStep 5535229 = 2075711) B2075711
theorem B3274303 : Blo 574812 3274303 := bstep (se 1 (by rfl) ⟨2455727, by rfl⟩ : syracuseStep 3274303 = 4911455) B4911455
theorem B12449771 : Blo 574812 12449771 := bstep (se 1 (by rfl) ⟨9337328, by rfl⟩ : syracuseStep 12449771 = 18674657) B18674657
theorem B2455865 : Blo 574812 2455865 := bstep (se 2 (by rfl) ⟨920949, by rfl⟩ : syracuseStep 2455865 = 1841899) B1841899
theorem B6650515 : Blo 574812 6650515 := bstep (se 1 (by rfl) ⟨4987886, by rfl⟩ : syracuseStep 6650515 = 9975773) B9975773
theorem B2489723 : Blo 574812 2489723 := bstep (se 1 (by rfl) ⟨1867292, by rfl⟩ : syracuseStep 2489723 = 3734585) B3734585
theorem B3736111 : Blo 574812 3736111 := bstep (se 1 (by rfl) ⟨2802083, by rfl⟩ : syracuseStep 3736111 = 5604167) B5604167
theorem B1639055 : Blo 574812 1639055 := bstep (se 1 (by rfl) ⟨1229291, by rfl⟩ : syracuseStep 1639055 = 2458583) B2458583
theorem B79758593 : Blo 574812 79758593 := bstep (se 2 (by rfl) ⟨29909472, by rfl⟩ : syracuseStep 79758593 = 59818945) B59818945
theorem B24971165 : Blo 574812 24971165 := bstep (se 3 (by rfl) ⟨4682093, by rfl⟩ : syracuseStep 24971165 = 9364187) B9364187
theorem B1640569 : Blo 574812 1640569 := bstep (se 2 (by rfl) ⟨615213, by rfl⟩ : syracuseStep 1640569 = 1230427) B1230427
theorem B3466135955 : Blo 574812 3466135955 := bstep (se 1 (by rfl) ⟨2599601966, by rfl⟩ : syracuseStep 3466135955 = 5199203933) B5199203933
theorem B1641185 : Blo 574812 1641185 := bstep (se 2 (by rfl) ⟨615444, by rfl⟩ : syracuseStep 1641185 = 1230889) B1230889
theorem B2461367 : Blo 574812 2461367 := bstep (se 1 (by rfl) ⟨1846025, by rfl⟩ : syracuseStep 2461367 = 3692051) B3692051
theorem B17764271 : Blo 574812 17764271 := bstep (se 1 (by rfl) ⟨13323203, by rfl⟩ : syracuseStep 17764271 = 26646407) B26646407
theorem B5541995 : Blo 574812 5541995 := bstep (se 1 (by rfl) ⟨4156496, by rfl⟩ : syracuseStep 5541995 = 8312993) B8312993
theorem B16028113 : Blo 574812 16028113 := bstep (se 2 (by rfl) ⟨6010542, by rfl⟩ : syracuseStep 16028113 = 12021085) B12021085
theorem B4069007 : Blo 574812 4069007 := bstep (se 1 (by rfl) ⟨3051755, by rfl⟩ : syracuseStep 4069007 = 6103511) B6103511
theorem B4626881 : Blo 574812 4626881 := bstep (se 2 (by rfl) ⟨1735080, by rfl⟩ : syracuseStep 4626881 = 3470161) B3470161
theorem B1645217 : Blo 574812 1645217 := bstep (se 2 (by rfl) ⟨616956, by rfl⟩ : syracuseStep 1645217 = 1233913) B1233913
theorem B7380305 : Blo 574812 7380305 := bstep (se 2 (by rfl) ⟨2767614, by rfl⟩ : syracuseStep 7380305 = 5535229) B5535229
theorem B4365737 : Blo 574812 4365737 := bstep (se 2 (by rfl) ⟨1637151, by rfl⟩ : syracuseStep 4365737 = 3274303) B3274303
theorem B11411219 : Blo 574812 11411219 := bstep (se 1 (by rfl) ⟨8558414, by rfl⟩ : syracuseStep 11411219 = 17116829) B17116829
theorem B4366223 : Blo 574812 4366223 := bstep (se 1 (by rfl) ⟨3274667, by rfl⟩ : syracuseStep 4366223 = 6549335) B6549335
theorem B1941407 : Blo 574812 1941407 := bstep (se 1 (by rfl) ⟨1456055, by rfl⟩ : syracuseStep 1941407 = 2912111) B2912111
theorem B2105903 : Blo 574812 2105903 := bstep (se 1 (by rfl) ⟨1579427, by rfl⟩ : syracuseStep 2105903 = 3158855) B3158855
theorem B1942271 : Blo 574812 1942271 := bstep (se 1 (by rfl) ⟨1456703, by rfl⟩ : syracuseStep 1942271 = 2913407) B2913407
theorem B4367195 : Blo 574812 4367195 := bstep (se 1 (by rfl) ⟨3275396, by rfl⟩ : syracuseStep 4367195 = 6550793) B6550793
theorem B8299847 : Blo 574812 8299847 := bstep (se 1 (by rfl) ⟨6224885, by rfl⟩ : syracuseStep 8299847 = 12449771) B12449771
theorem B862391 : Blo 574812 862391 := bstep (se 1 (by rfl) ⟨646793, by rfl⟩ : syracuseStep 862391 = 1293587) B1293587
theorem B862439 : Blo 574812 862439 := bstep (se 1 (by rfl) ⟨646829, by rfl⟩ : syracuseStep 862439 = 1293659) B1293659
theorem B862955 : Blo 574812 862955 := bstep (se 1 (by rfl) ⟨647216, by rfl⟩ : syracuseStep 862955 = 1294433) B1294433
theorem B7187297 : Blo 574812 7187297 := bstep (se 2 (by rfl) ⟨2695236, by rfl⟩ : syracuseStep 7187297 = 5390473) B5390473
theorem B2468713 : Blo 574812 2468713 := bstep (se 2 (by rfl) ⟨925767, by rfl⟩ : syracuseStep 2468713 = 1851535) B1851535
theorem B863327 : Blo 574812 863327 := bstep (se 1 (by rfl) ⟨647495, by rfl⟩ : syracuseStep 863327 = 1294991) B1294991
theorem B863771 : Blo 574812 863771 := bstep (se 1 (by rfl) ⟨647828, by rfl⟩ : syracuseStep 863771 = 1295657) B1295657
theorem B863951 : Blo 574812 863951 := bstep (se 1 (by rfl) ⟨647963, by rfl⟩ : syracuseStep 863951 = 1295927) B1295927
theorem B864311 : Blo 574812 864311 := bstep (se 1 (by rfl) ⟨648233, by rfl⟩ : syracuseStep 864311 = 1296467) B1296467
theorem B14037137 : Blo 574812 14037137 := bstep (se 2 (by rfl) ⟨5263926, by rfl⟩ : syracuseStep 14037137 = 10527853) B10527853
theorem B8335547 : Blo 574812 8335547 := bstep (se 1 (by rfl) ⟨6251660, by rfl⟩ : syracuseStep 8335547 = 12503321) B12503321
theorem B864809 : Blo 574812 864809 := bstep (se 2 (by rfl) ⟨324303, by rfl⟩ : syracuseStep 864809 = 648607) B648607
theorem B865127 : Blo 574812 865127 := bstep (se 1 (by rfl) ⟨648845, by rfl⟩ : syracuseStep 865127 = 1297691) B1297691
theorem B865247 : Blo 574812 865247 := bstep (se 1 (by rfl) ⟨648935, by rfl⟩ : syracuseStep 865247 = 1297871) B1297871
theorem B3323045 : Blo 574812 3323045 := bstep (se 4 (by rfl) ⟨311535, by rfl⟩ : syracuseStep 3323045 = 623071) B623071
theorem B2077903 : Blo 574812 2077903 := bstep (se 1 (by rfl) ⟨1558427, by rfl⟩ : syracuseStep 2077903 = 3116855) B3116855
theorem B865961 : Blo 574812 865961 := bstep (se 2 (by rfl) ⟨324735, by rfl⟩ : syracuseStep 865961 = 649471) B649471
theorem B866087 : Blo 574812 866087 := bstep (se 1 (by rfl) ⟨649565, by rfl⟩ : syracuseStep 866087 = 1299131) B1299131
theorem B866159 : Blo 574812 866159 := bstep (se 1 (by rfl) ⟨649619, by rfl⟩ : syracuseStep 866159 = 1299239) B1299239
theorem B1455995 : Blo 574812 1455995 := bstep (se 1 (by rfl) ⟨1091996, by rfl⟩ : syracuseStep 1455995 = 2183993) B2183993
theorem B866795 : Blo 574812 866795 := bstep (se 1 (by rfl) ⟨650096, by rfl⟩ : syracuseStep 866795 = 1300193) B1300193
theorem B2079287 : Blo 574812 2079287 := bstep (se 1 (by rfl) ⟨1559465, by rfl⟩ : syracuseStep 2079287 = 3118931) B3118931
theorem B867023 : Blo 574812 867023 := bstep (se 1 (by rfl) ⟨650267, by rfl⟩ : syracuseStep 867023 = 1300535) B1300535
theorem B1948427 : Blo 574812 1948427 := bstep (se 1 (by rfl) ⟨1461320, by rfl⟩ : syracuseStep 1948427 = 2922641) B2922641
theorem B1456967 : Blo 574812 1456967 := bstep (se 1 (by rfl) ⟨1092725, by rfl⟩ : syracuseStep 1456967 = 2185451) B2185451
theorem B1096735 : Blo 574812 1096735 := bstep (se 1 (by rfl) ⟨822551, by rfl⟩ : syracuseStep 1096735 = 1645103) B1645103
theorem B1293407 : Blo 574812 1293407 := bstep (se 1 (by rfl) ⟨970055, by rfl⟩ : syracuseStep 1293407 = 1940111) B1940111
theorem B60833045 : Blo 574812 60833045 := bstep (se 6 (by rfl) ⟨1425774, by rfl⟩ : syracuseStep 60833045 = 2851549) B2851549
theorem B867881 : Blo 574812 867881 := bstep (se 2 (by rfl) ⟨325455, by rfl⟩ : syracuseStep 867881 = 650911) B650911
theorem B868127 : Blo 574812 868127 := bstep (se 1 (by rfl) ⟨651095, by rfl⟩ : syracuseStep 868127 = 1302191) B1302191
theorem B1294235 : Blo 574812 1294235 := bstep (se 1 (by rfl) ⟨970676, by rfl⟩ : syracuseStep 1294235 = 1941353) B1941353
theorem B3293257 : Blo 574812 3293257 := bstep (se 2 (by rfl) ⟨1234971, by rfl⟩ : syracuseStep 3293257 = 2469943) B2469943
theorem B1949993 : Blo 574812 1949993 := bstep (se 2 (by rfl) ⟨731247, by rfl⟩ : syracuseStep 1949993 = 1462495) B1462495
theorem B14827859 : Blo 574812 14827859 := bstep (se 1 (by rfl) ⟨11120894, by rfl⟩ : syracuseStep 14827859 = 22241789) B22241789
theorem B1950047 : Blo 574812 1950047 := bstep (se 1 (by rfl) ⟨1462535, by rfl⟩ : syracuseStep 1950047 = 2925071) B2925071
theorem B1295585 : Blo 574812 1295585 := bstep (se 2 (by rfl) ⟨485844, by rfl⟩ : syracuseStep 1295585 = 971689) B971689
theorem B15025409 : Blo 574812 15025409 := bstep (se 2 (by rfl) ⟨5634528, by rfl⟩ : syracuseStep 15025409 = 11269057) B11269057
theorem B1230137 : Blo 574812 1230137 := bstep (se 2 (by rfl) ⟨461301, by rfl⟩ : syracuseStep 1230137 = 922603) B922603
theorem B1459691 : Blo 574812 1459691 := bstep (se 1 (by rfl) ⟨1094768, by rfl⟩ : syracuseStep 1459691 = 2189537) B2189537
theorem B1295963 : Blo 574812 1295963 := bstep (se 1 (by rfl) ⟨971972, by rfl⟩ : syracuseStep 1295963 = 1943945) B1943945
theorem B575335 : Blo 574812 575335 := bstep (se 1 (by rfl) ⟨431501, by rfl⟩ : syracuseStep 575335 = 863003) B863003
theorem B4147271 : Blo 574812 4147271 := bstep (se 1 (by rfl) ⟨3110453, by rfl⟩ : syracuseStep 4147271 = 6220907) B6220907
theorem B575903 : Blo 574812 575903 := bstep (se 1 (by rfl) ⟨431927, by rfl⟩ : syracuseStep 575903 = 863855) B863855
theorem B1296827 : Blo 574812 1296827 := bstep (se 1 (by rfl) ⟨972620, by rfl⟩ : syracuseStep 1296827 = 1945241) B1945241
theorem B8309303 : Blo 574812 8309303 := bstep (se 1 (by rfl) ⟨6231977, by rfl⟩ : syracuseStep 8309303 = 12463955) B12463955
theorem B576167 : Blo 574812 576167 := bstep (se 1 (by rfl) ⟨432125, by rfl⟩ : syracuseStep 576167 = 864251) B864251
theorem B576423 : Blo 574812 576423 := bstep (se 1 (by rfl) ⟨432317, by rfl⟩ : syracuseStep 576423 = 864635) B864635
theorem B1297385 : Blo 574812 1297385 := bstep (se 2 (by rfl) ⟨486519, by rfl⟩ : syracuseStep 1297385 = 973039) B973039
theorem B576495 : Blo 574812 576495 := bstep (se 1 (by rfl) ⟨432371, by rfl⟩ : syracuseStep 576495 = 864743) B864743
theorem B576743 : Blo 574812 576743 := bstep (se 1 (by rfl) ⟨432557, by rfl⟩ : syracuseStep 576743 = 865115) B865115
theorem B8867353 : Blo 574812 8867353 := bstep (se 2 (by rfl) ⟨3325257, by rfl⟩ : syracuseStep 8867353 = 6650515) B6650515
theorem B4935239 : Blo 574812 4935239 := bstep (se 1 (by rfl) ⟨3701429, by rfl⟩ : syracuseStep 4935239 = 7402859) B7402859
theorem B577191 : Blo 574812 577191 := bstep (se 1 (by rfl) ⟨432893, by rfl⟩ : syracuseStep 577191 = 865787) B865787
theorem B34197551 : Blo 574812 34197551 := bstep (se 1 (by rfl) ⟨25648163, by rfl⟩ : syracuseStep 34197551 = 51296327) B51296327
theorem B578075 : Blo 574812 578075 := bstep (se 1 (by rfl) ⟨433556, by rfl⟩ : syracuseStep 578075 = 867113) B867113
theorem B1036891 : Blo 574812 1036891 := bstep (se 1 (by rfl) ⟨777668, by rfl⟩ : syracuseStep 1036891 = 1555337) B1555337
theorem B1167977 : Blo 574812 1167977 := bstep (se 2 (by rfl) ⟨437991, by rfl⟩ : syracuseStep 1167977 = 875983) B875983
theorem B578287 : Blo 574812 578287 := bstep (se 1 (by rfl) ⟨433715, by rfl⟩ : syracuseStep 578287 = 867431) B867431
theorem B7918397 : Blo 574812 7918397 := bstep (se 3 (by rfl) ⟨1484699, by rfl⟩ : syracuseStep 7918397 = 2969399) B2969399
theorem B578407 : Blo 574812 578407 := bstep (se 1 (by rfl) ⟨433805, by rfl⟩ : syracuseStep 578407 = 867611) B867611
theorem B578431 : Blo 574812 578431 := bstep (se 1 (by rfl) ⟨433823, by rfl⟩ : syracuseStep 578431 = 867647) B867647
theorem B1659815 : Blo 574812 1659815 := bstep (se 1 (by rfl) ⟨1244861, by rfl⟩ : syracuseStep 1659815 = 2489723) B2489723
theorem B578671 : Blo 574812 578671 := bstep (se 1 (by rfl) ⟨434003, by rfl⟩ : syracuseStep 578671 = 868007) B868007
theorem B578719 : Blo 574812 578719 := bstep (se 1 (by rfl) ⟨434039, by rfl⟩ : syracuseStep 578719 = 868079) B868079
theorem B2774519 : Blo 574812 2774519 := bstep (se 1 (by rfl) ⟨2080889, by rfl⟩ : syracuseStep 2774519 = 4161779) B4161779
theorem B5559833 : Blo 574812 5559833 := bstep (se 2 (by rfl) ⟨2084937, by rfl⟩ : syracuseStep 5559833 = 4169875) B4169875
theorem B4216369 : Blo 574812 4216369 := bstep (se 2 (by rfl) ⟨1581138, by rfl⟩ : syracuseStep 4216369 = 3162277) B3162277
theorem B1301255 : Blo 574812 1301255 := bstep (se 1 (by rfl) ⟨975941, by rfl⟩ : syracuseStep 1301255 = 1951883) B1951883
theorem B3956215 : Blo 574812 3956215 := bstep (se 1 (by rfl) ⟨2967161, by rfl⟩ : syracuseStep 3956215 = 5934323) B5934323
theorem B2317871 : Blo 574812 2317871 := bstep (se 1 (by rfl) ⟨1738403, by rfl⟩ : syracuseStep 2317871 = 3476807) B3476807
theorem B1302281 : Blo 574812 1302281 := bstep (se 2 (by rfl) ⟨488355, by rfl⟩ : syracuseStep 1302281 = 976711) B976711
theorem B32432339 : Blo 574812 32432339 := bstep (se 1 (by rfl) ⟨24324254, by rfl⟩ : syracuseStep 32432339 = 48648509) B48648509
theorem B975071 : Blo 574812 975071 := bstep (se 1 (by rfl) ⟨731303, by rfl⟩ : syracuseStep 975071 = 1462607) B1462607
theorem B647419 : Blo 574812 647419 := bstep (se 1 (by rfl) ⟨485564, by rfl⟩ : syracuseStep 647419 = 971129) B971129
theorem B975415 : Blo 574812 975415 := bstep (se 1 (by rfl) ⟨731561, by rfl⟩ : syracuseStep 975415 = 1463123) B1463123
theorem B975611 : Blo 574812 975611 := bstep (se 1 (by rfl) ⟨731708, by rfl⟩ : syracuseStep 975611 = 1463417) B1463417
theorem B2188093 : Blo 574812 2188093 := bstep (se 3 (by rfl) ⟨410267, by rfl⟩ : syracuseStep 2188093 = 820535) B820535
theorem B3695483 : Blo 574812 3695483 := bstep (se 1 (by rfl) ⟨2771612, by rfl⟩ : syracuseStep 3695483 = 5543225) B5543225
theorem B648319 : Blo 574812 648319 := bstep (se 1 (by rfl) ⟨486239, by rfl⟩ : syracuseStep 648319 = 972479) B972479
theorem B2910329 : Blo 574812 2910329 := bstep (se 2 (by rfl) ⟨1091373, by rfl⟩ : syracuseStep 2910329 = 2182747) B2182747
theorem B2190311 : Blo 574812 2190311 := bstep (se 1 (by rfl) ⟨1642733, by rfl⟩ : syracuseStep 2190311 = 3285467) B3285467
theorem B33647663 : Blo 574812 33647663 := bstep (se 1 (by rfl) ⟨25235747, by rfl⟩ : syracuseStep 33647663 = 50471495) B50471495
theorem B2223983 : Blo 574812 2223983 := bstep (se 1 (by rfl) ⟨1667987, by rfl⟩ : syracuseStep 2223983 = 3335975) B3335975
theorem B2191495 : Blo 574812 2191495 := bstep (se 1 (by rfl) ⟨1643621, by rfl⟩ : syracuseStep 2191495 = 3287243) B3287243
theorem B2191799 : Blo 574812 2191799 := bstep (se 1 (by rfl) ⟨1643849, by rfl⟩ : syracuseStep 2191799 = 3287699) B3287699
theorem B3340777 : Blo 574812 3340777 := bstep (se 2 (by rfl) ⟨1252791, by rfl⟩ : syracuseStep 3340777 = 2505583) B2505583
theorem B1637243 : Blo 574812 1637243 := bstep (se 1 (by rfl) ⟨1227932, by rfl⟩ : syracuseStep 1637243 = 2455865) B2455865
theorem B2194715 : Blo 574812 2194715 := bstep (se 1 (by rfl) ⟨1646036, by rfl⟩ : syracuseStep 2194715 = 3292073) B3292073
theorem B4391009 : Blo 574812 4391009 := bstep (se 2 (by rfl) ⟨1646628, by rfl⟩ : syracuseStep 4391009 = 3293257) B3293257
theorem B4981481 : Blo 574812 4981481 := bstep (se 2 (by rfl) ⟨1868055, by rfl⟩ : syracuseStep 4981481 = 3736111) B3736111
theorem B820091 : Blo 574812 820091 := bstep (se 1 (by rfl) ⟨615068, by rfl⟩ : syracuseStep 820091 = 1230137) B1230137
theorem B2917457 : Blo 574812 2917457 := bstep (se 2 (by rfl) ⟨1094046, by rfl⟩ : syracuseStep 2917457 = 2188093) B2188093
theorem B16647443 : Blo 574812 16647443 := bstep (se 1 (by rfl) ⟨12485582, by rfl⟩ : syracuseStep 16647443 = 24971165) B24971165
theorem B3114605 : Blo 574812 3114605 := bstep (se 3 (by rfl) ⟨583988, by rfl⟩ : syracuseStep 3114605 = 1167977) B1167977
theorem B5539535 : Blo 574812 5539535 := bstep (se 1 (by rfl) ⟨4154651, by rfl⟩ : syracuseStep 5539535 = 8309303) B8309303
theorem B1640911 : Blo 574812 1640911 := bstep (se 1 (by rfl) ⟨1230683, by rfl⟩ : syracuseStep 1640911 = 2461367) B2461367
theorem B5278931 : Blo 574812 5278931 := bstep (se 1 (by rfl) ⟨3959198, by rfl⟩ : syracuseStep 5278931 = 7918397) B7918397
theorem B3706555 : Blo 574812 3706555 := bstep (se 1 (by rfl) ⟨2779916, by rfl⟩ : syracuseStep 3706555 = 5559833) B5559833
theorem B3084587 : Blo 574812 3084587 := bstep (se 1 (by rfl) ⟨2313440, by rfl⟩ : syracuseStep 3084587 = 4626881) B4626881
theorem B4920203 : Blo 574812 4920203 := bstep (se 1 (by rfl) ⟨3690152, by rfl⟩ : syracuseStep 4920203 = 7380305) B7380305
theorem B1545247 : Blo 574812 1545247 := bstep (se 1 (by rfl) ⟨1158935, by rfl⟩ : syracuseStep 1545247 = 2317871) B2317871
theorem B7607479 : Blo 574812 7607479 := bstep (se 1 (by rfl) ⟨5705609, by rfl⟩ : syracuseStep 7607479 = 11411219) B11411219
theorem B2921993 : Blo 574812 2921993 := bstep (se 2 (by rfl) ⟨1095747, by rfl⟩ : syracuseStep 2921993 = 2191495) B2191495
theorem B21370817 : Blo 574812 21370817 := bstep (se 2 (by rfl) ⟨8014056, by rfl⟩ : syracuseStep 21370817 = 16028113) B16028113
theorem B1382521 : Blo 574812 1382521 := bstep (se 2 (by rfl) ⟨518445, by rfl⟩ : syracuseStep 1382521 = 1036891) B1036891
theorem B1940219 : Blo 574812 1940219 := bstep (se 1 (by rfl) ⟨1455164, by rfl⟩ : syracuseStep 1940219 = 2910329) B2910329
theorem B1386191 : Blo 574812 1386191 := bstep (se 1 (by rfl) ⟨1039643, by rfl⟩ : syracuseStep 1386191 = 2079287) B2079287
theorem B1091495 : Blo 574812 1091495 := bstep (se 1 (by rfl) ⟨818621, by rfl⟩ : syracuseStep 1091495 = 1637243) B1637243
theorem B862271 : Blo 574812 862271 := bstep (se 1 (by rfl) ⟨646703, by rfl⟩ : syracuseStep 862271 = 1293407) B1293407
theorem B862823 : Blo 574812 862823 := bstep (se 1 (by rfl) ⟨647117, by rfl⟩ : syracuseStep 862823 = 1294235) B1294235
theorem B863225 : Blo 574812 863225 := bstep (se 2 (by rfl) ⟨323709, by rfl⟩ : syracuseStep 863225 = 647419) B647419
theorem B1092703 : Blo 574812 1092703 := bstep (se 1 (by rfl) ⟨819527, by rfl⟩ : syracuseStep 1092703 = 1639055) B1639055
theorem B86486237 : Blo 574812 86486237 := bstep (se 3 (by rfl) ⟨16216169, by rfl⟩ : syracuseStep 86486237 = 32432339) B32432339
theorem B863723 : Blo 574812 863723 := bstep (se 1 (by rfl) ⟨647792, by rfl⟩ : syracuseStep 863723 = 1295585) B1295585
theorem B863975 : Blo 574812 863975 := bstep (se 1 (by rfl) ⟨647981, by rfl⟩ : syracuseStep 863975 = 1295963) B1295963
theorem B2764847 : Blo 574812 2764847 := bstep (se 1 (by rfl) ⟨2073635, by rfl⟩ : syracuseStep 2764847 = 4147271) B4147271
theorem B864425 : Blo 574812 864425 := bstep (se 2 (by rfl) ⟨324159, by rfl⟩ : syracuseStep 864425 = 648319) B648319
theorem B864551 : Blo 574812 864551 := bstep (se 1 (by rfl) ⟨648413, by rfl⟩ : syracuseStep 864551 = 1296827) B1296827
theorem B1094123 : Blo 574812 1094123 := bstep (se 1 (by rfl) ⟨820592, by rfl⟩ : syracuseStep 1094123 = 1641185) B1641185
theorem B864923 : Blo 574812 864923 := bstep (se 1 (by rfl) ⟨648692, by rfl⟩ : syracuseStep 864923 = 1297385) B1297385
theorem B3290159 : Blo 574812 3290159 := bstep (se 1 (by rfl) ⟨2467619, by rfl⟩ : syracuseStep 3290159 = 4935239) B4935239
theorem B11842847 : Blo 574812 11842847 := bstep (se 1 (by rfl) ⟨8882135, by rfl⟩ : syracuseStep 11842847 = 17764271) B17764271
theorem B1849679 : Blo 574812 1849679 := bstep (se 1 (by rfl) ⟨1387259, by rfl⟩ : syracuseStep 1849679 = 2774519) B2774519
theorem B3291617 : Blo 574812 3291617 := bstep (se 2 (by rfl) ⟨1234356, by rfl⟩ : syracuseStep 3291617 = 2468713) B2468713
theorem B1096811 : Blo 574812 1096811 := bstep (se 1 (by rfl) ⟨822608, by rfl⟩ : syracuseStep 1096811 = 1645217) B1645217
theorem B867503 : Blo 574812 867503 := bstep (se 1 (by rfl) ⟨650627, by rfl⟩ : syracuseStep 867503 = 1301255) B1301255
theorem B868187 : Blo 574812 868187 := bstep (se 1 (by rfl) ⟨651140, by rfl⟩ : syracuseStep 868187 = 1302281) B1302281
theorem B1294271 : Blo 574812 1294271 := bstep (se 1 (by rfl) ⟨970703, by rfl⟩ : syracuseStep 1294271 = 1941407) B1941407
theorem B1294847 : Blo 574812 1294847 := bstep (se 1 (by rfl) ⟨971135, by rfl⟩ : syracuseStep 1294847 = 1942271) B1942271
theorem B574927 : Blo 574812 574927 := bstep (se 1 (by rfl) ⟨431195, by rfl⟩ : syracuseStep 574927 = 862391) B862391
theorem B574959 : Blo 574812 574959 := bstep (se 1 (by rfl) ⟨431219, by rfl⟩ : syracuseStep 574959 = 862439) B862439
theorem B2770537 : Blo 574812 2770537 := bstep (se 2 (by rfl) ⟨1038951, by rfl⟩ : syracuseStep 2770537 = 2077903) B2077903
theorem B575303 : Blo 574812 575303 := bstep (se 1 (by rfl) ⟨431477, by rfl⟩ : syracuseStep 575303 = 862955) B862955
theorem B1460207 : Blo 574812 1460207 := bstep (se 1 (by rfl) ⟨1095155, by rfl⟩ : syracuseStep 1460207 = 2190311) B2190311
theorem B22431775 : Blo 574812 22431775 := bstep (se 1 (by rfl) ⟨16823831, by rfl⟩ : syracuseStep 22431775 = 33647663) B33647663
theorem B575551 : Blo 574812 575551 := bstep (se 1 (by rfl) ⟨431663, by rfl⟩ : syracuseStep 575551 = 863327) B863327
theorem B5621825 : Blo 574812 5621825 := bstep (se 2 (by rfl) ⟨2108184, by rfl⟩ : syracuseStep 5621825 = 4216369) B4216369
theorem B575847 : Blo 574812 575847 := bstep (se 1 (by rfl) ⟨431885, by rfl⟩ : syracuseStep 575847 = 863771) B863771
theorem B575967 : Blo 574812 575967 := bstep (se 1 (by rfl) ⟨431975, by rfl⟩ : syracuseStep 575967 = 863951) B863951
theorem B576207 : Blo 574812 576207 := bstep (se 1 (by rfl) ⟨432155, by rfl⟩ : syracuseStep 576207 = 864311) B864311
theorem B9358091 : Blo 574812 9358091 := bstep (se 1 (by rfl) ⟨7018568, by rfl⟩ : syracuseStep 9358091 = 14037137) B14037137
theorem B5557031 : Blo 574812 5557031 := bstep (se 1 (by rfl) ⟨4167773, by rfl⟩ : syracuseStep 5557031 = 8335547) B8335547
theorem B1461199 : Blo 574812 1461199 := bstep (se 1 (by rfl) ⟨1095899, by rfl⟩ : syracuseStep 1461199 = 2191799) B2191799
theorem B576539 : Blo 574812 576539 := bstep (se 1 (by rfl) ⟨432404, by rfl⟩ : syracuseStep 576539 = 864809) B864809
theorem B576751 : Blo 574812 576751 := bstep (se 1 (by rfl) ⟨432563, by rfl⟩ : syracuseStep 576751 = 865127) B865127
theorem B576831 : Blo 574812 576831 := bstep (se 1 (by rfl) ⟨432623, by rfl⟩ : syracuseStep 576831 = 865247) B865247
theorem B2215363 : Blo 574812 2215363 := bstep (se 1 (by rfl) ⟨1661522, by rfl⟩ : syracuseStep 2215363 = 3323045) B3323045
theorem B76664501 : Blo 574812 76664501 := bstep (se 5 (by rfl) ⟨3593648, by rfl⟩ : syracuseStep 76664501 = 7187297) B7187297
theorem B577307 : Blo 574812 577307 := bstep (se 1 (by rfl) ⟨432980, by rfl⟩ : syracuseStep 577307 = 865961) B865961
theorem B577391 : Blo 574812 577391 := bstep (se 1 (by rfl) ⟨433043, by rfl⟩ : syracuseStep 577391 = 866087) B866087
theorem B577439 : Blo 574812 577439 := bstep (se 1 (by rfl) ⟨433079, by rfl⟩ : syracuseStep 577439 = 866159) B866159
theorem B970663 : Blo 574812 970663 := bstep (se 1 (by rfl) ⟨727997, by rfl⟩ : syracuseStep 970663 = 1455995) B1455995
theorem B1462313 : Blo 574812 1462313 := bstep (se 2 (by rfl) ⟨548367, by rfl⟩ : syracuseStep 1462313 = 1096735) B1096735
theorem B577863 : Blo 574812 577863 := bstep (se 1 (by rfl) ⟨433397, by rfl⟩ : syracuseStep 577863 = 866795) B866795
theorem B578015 : Blo 574812 578015 := bstep (se 1 (by rfl) ⟨433511, by rfl⟩ : syracuseStep 578015 = 867023) B867023
theorem B1298951 : Blo 574812 1298951 := bstep (se 1 (by rfl) ⟨974213, by rfl⟩ : syracuseStep 1298951 = 1948427) B1948427
theorem B971311 : Blo 574812 971311 := bstep (se 1 (by rfl) ⟨728483, by rfl⟩ : syracuseStep 971311 = 1456967) B1456967
theorem B40555363 : Blo 574812 40555363 := bstep (se 1 (by rfl) ⟨30416522, by rfl⟩ : syracuseStep 40555363 = 60833045) B60833045
theorem B1463143 : Blo 574812 1463143 := bstep (se 1 (by rfl) ⟨1097357, by rfl⟩ : syracuseStep 1463143 = 2194715) B2194715
theorem B578587 : Blo 574812 578587 := bstep (se 1 (by rfl) ⟨433940, by rfl⟩ : syracuseStep 578587 = 867881) B867881
theorem B578751 : Blo 574812 578751 := bstep (se 1 (by rfl) ⟨434063, by rfl⟩ : syracuseStep 578751 = 868127) B868127
theorem B1299995 : Blo 574812 1299995 := bstep (se 1 (by rfl) ⟨974996, by rfl⟩ : syracuseStep 1299995 = 1949993) B1949993
theorem B9885239 : Blo 574812 9885239 := bstep (se 1 (by rfl) ⟨7413929, by rfl⟩ : syracuseStep 9885239 = 14827859) B14827859
theorem B1300031 : Blo 574812 1300031 := bstep (se 1 (by rfl) ⟨975023, by rfl⟩ : syracuseStep 1300031 = 1950047) B1950047
theorem B1300553 : Blo 574812 1300553 := bstep (se 2 (by rfl) ⟨487707, by rfl⟩ : syracuseStep 1300553 = 975415) B975415
theorem B53172395 : Blo 574812 53172395 := bstep (se 1 (by rfl) ⟨39879296, by rfl⟩ : syracuseStep 53172395 = 79758593) B79758593
theorem B10016939 : Blo 574812 10016939 := bstep (se 1 (by rfl) ⟨7512704, by rfl⟩ : syracuseStep 10016939 = 15025409) B15025409
theorem B973127 : Blo 574812 973127 := bstep (se 1 (by rfl) ⟨729845, by rfl⟩ : syracuseStep 973127 = 1459691) B1459691
theorem B2310757303 : Blo 574812 2310757303 := bstep (se 1 (by rfl) ⟨1733067977, by rfl⟩ : syracuseStep 2310757303 = 3466135955) B3466135955
theorem B9854621 : Blo 574812 9854621 := bstep (se 3 (by rfl) ⟨1847741, by rfl⟩ : syracuseStep 9854621 = 3695483) B3695483
theorem B22798367 : Blo 574812 22798367 := bstep (se 1 (by rfl) ⟨17098775, by rfl⟩ : syracuseStep 22798367 = 34197551) B34197551
theorem B3694663 : Blo 574812 3694663 := bstep (se 1 (by rfl) ⟨2770997, by rfl⟩ : syracuseStep 3694663 = 5541995) B5541995
theorem B2187425 : Blo 574812 2187425 := bstep (se 2 (by rfl) ⟨820284, by rfl⟩ : syracuseStep 2187425 = 1640569) B1640569
theorem B1106543 : Blo 574812 1106543 := bstep (se 1 (by rfl) ⟨829907, by rfl⟩ : syracuseStep 1106543 = 1659815) B1659815
theorem B2712671 : Blo 574812 2712671 := bstep (se 1 (by rfl) ⟨2034503, by rfl⟩ : syracuseStep 2712671 = 4069007) B4069007
theorem B11823137 : Blo 574812 11823137 := bstep (se 2 (by rfl) ⟨4433676, by rfl⟩ : syracuseStep 11823137 = 8867353) B8867353
theorem B2910491 : Blo 574812 2910491 := bstep (se 1 (by rfl) ⟨2182868, by rfl⟩ : syracuseStep 2910491 = 4365737) B4365737
theorem B2910815 : Blo 574812 2910815 := bstep (se 1 (by rfl) ⟨2183111, by rfl⟩ : syracuseStep 2910815 = 4366223) B4366223
theorem B650047 : Blo 574812 650047 := bstep (se 1 (by rfl) ⟨487535, by rfl⟩ : syracuseStep 650047 = 975071) B975071
theorem B1403935 : Blo 574812 1403935 := bstep (se 1 (by rfl) ⟨1052951, by rfl⟩ : syracuseStep 1403935 = 2105903) B2105903
theorem B650407 : Blo 574812 650407 := bstep (se 1 (by rfl) ⟨487805, by rfl⟩ : syracuseStep 650407 = 975611) B975611
theorem B2911463 : Blo 574812 2911463 := bstep (se 1 (by rfl) ⟨2183597, by rfl⟩ : syracuseStep 2911463 = 4367195) B4367195
theorem B5533231 : Blo 574812 5533231 := bstep (se 1 (by rfl) ⟨4149923, by rfl⟩ : syracuseStep 5533231 = 8299847) B8299847
theorem B4454369 : Blo 574812 4454369 := bstep (se 2 (by rfl) ⟨1670388, by rfl⟩ : syracuseStep 4454369 = 3340777) B3340777
theorem B5274953 : Blo 574812 5274953 := bstep (se 2 (by rfl) ⟨1978107, by rfl⟩ : syracuseStep 5274953 = 3956215) B3956215
theorem B5930621 : Blo 574812 5930621 := bstep (se 3 (by rfl) ⟨1111991, by rfl⟩ : syracuseStep 5930621 = 2223983) B2223983
theorem B3704687 : Blo 574812 3704687 := bstep (se 1 (by rfl) ⟨2778515, by rfl⟩ : syracuseStep 3704687 = 5557031) B5557031
theorem B3280135 : Blo 574812 3280135 := bstep (se 1 (by rfl) ⟨2460101, by rfl⟩ : syracuseStep 3280135 = 4920203) B4920203
theorem B6590159 : Blo 574812 6590159 := bstep (se 1 (by rfl) ⟨4942619, by rfl⟩ : syracuseStep 6590159 = 9885239) B9885239
theorem B2953817 : Blo 574812 2953817 := bstep (se 2 (by rfl) ⟨1107681, by rfl⟩ : syracuseStep 2953817 = 2215363) B2215363
theorem B7377641 : Blo 574812 7377641 := bstep (se 2 (by rfl) ⟨2766615, by rfl⟩ : syracuseStep 7377641 = 5533231) B5533231
theorem B56988845 : Blo 574812 56988845 := bstep (se 3 (by rfl) ⟨10685408, by rfl⟩ : syracuseStep 56988845 = 21370817) B21370817
theorem B1808447 : Blo 574812 1808447 := bstep (se 1 (by rfl) ⟨1356335, by rfl⟩ : syracuseStep 1808447 = 2712671) B2712671
theorem B54073817 : Blo 574812 54073817 := bstep (se 2 (by rfl) ⟨20277681, by rfl⟩ : syracuseStep 54073817 = 40555363) B40555363
theorem B1940327 : Blo 574812 1940327 := bstep (se 1 (by rfl) ⟨1455245, by rfl⟩ : syracuseStep 1940327 = 2910491) B2910491
theorem B1940543 : Blo 574812 1940543 := bstep (se 1 (by rfl) ⟨1455407, by rfl⟩ : syracuseStep 1940543 = 2910815) B2910815
theorem B1940975 : Blo 574812 1940975 := bstep (se 1 (by rfl) ⟨1455731, by rfl⟩ : syracuseStep 1940975 = 2911463) B2911463
theorem B1843231 : Blo 574812 1843231 := bstep (se 1 (by rfl) ⟨1382423, by rfl⟩ : syracuseStep 1843231 = 2764847) B2764847
theorem B1843361 : Blo 574812 1843361 := bstep (se 2 (by rfl) ⟨691260, by rfl⟩ : syracuseStep 1843361 = 1382521) B1382521
theorem B729415 : Blo 574812 729415 := bstep (se 1 (by rfl) ⟨547061, by rfl⟩ : syracuseStep 729415 = 1094123) B1094123
theorem B731207 : Blo 574812 731207 := bstep (se 1 (by rfl) ⟨548405, by rfl⟩ : syracuseStep 731207 = 1096811) B1096811
theorem B3516635 : Blo 574812 3516635 := bstep (se 1 (by rfl) ⟨2637476, by rfl⟩ : syracuseStep 3516635 = 5274953) B5274953
theorem B862847 : Blo 574812 862847 := bstep (se 1 (by rfl) ⟨647135, by rfl⟩ : syracuseStep 862847 = 1294271) B1294271
theorem B2927339 : Blo 574812 2927339 := bstep (se 1 (by rfl) ⟨2195504, by rfl⟩ : syracuseStep 2927339 = 4391009) B4391009
theorem B4926217 : Blo 574812 4926217 := bstep (se 2 (by rfl) ⟨1847331, by rfl⟩ : syracuseStep 4926217 = 3694663) B3694663
theorem B863231 : Blo 574812 863231 := bstep (se 1 (by rfl) ⟨647423, by rfl⟩ : syracuseStep 863231 = 1294847) B1294847
theorem B1944971 : Blo 574812 1944971 := bstep (se 1 (by rfl) ⟨1458728, by rfl⟩ : syracuseStep 1944971 = 2917457) B2917457
theorem B2076403 : Blo 574812 2076403 := bstep (se 1 (by rfl) ⟨1557302, by rfl⟩ : syracuseStep 2076403 = 3114605) B3114605
theorem B3747883 : Blo 574812 3747883 := bstep (se 1 (by rfl) ⟨2810912, by rfl⟩ : syracuseStep 3747883 = 5621825) B5621825
theorem B6238727 : Blo 574812 6238727 := bstep (se 1 (by rfl) ⟨4679045, by rfl⟩ : syracuseStep 6238727 = 9358091) B9358091
theorem B3519287 : Blo 574812 3519287 := bstep (se 1 (by rfl) ⟨2639465, by rfl⟩ : syracuseStep 3519287 = 5278931) B5278931
theorem B865967 : Blo 574812 865967 := bstep (se 1 (by rfl) ⟨649475, by rfl⟩ : syracuseStep 865967 = 1298951) B1298951
theorem B1947995 : Blo 574812 1947995 := bstep (se 1 (by rfl) ⟨1460996, by rfl⟩ : syracuseStep 1947995 = 2921993) B2921993
theorem B866663 : Blo 574812 866663 := bstep (se 1 (by rfl) ⟨649997, by rfl⟩ : syracuseStep 866663 = 1299995) B1299995
theorem B866687 : Blo 574812 866687 := bstep (se 1 (by rfl) ⟨650015, by rfl⟩ : syracuseStep 866687 = 1300031) B1300031
theorem B866729 : Blo 574812 866729 := bstep (se 2 (by rfl) ⟨325023, by rfl⟩ : syracuseStep 866729 = 650047) B650047
theorem B1948265 : Blo 574812 1948265 := bstep (se 2 (by rfl) ⟨730599, by rfl⟩ : syracuseStep 1948265 = 1461199) B1461199
theorem B867035 : Blo 574812 867035 := bstep (se 1 (by rfl) ⟨650276, by rfl⟩ : syracuseStep 867035 = 1300553) B1300553
theorem B1456937 : Blo 574812 1456937 := bstep (se 2 (by rfl) ⟨546351, by rfl⟩ : syracuseStep 1456937 = 1092703) B1092703
theorem B867209 : Blo 574812 867209 := bstep (se 2 (by rfl) ⟨325203, by rfl⟩ : syracuseStep 867209 = 650407) B650407
theorem B1293479 : Blo 574812 1293479 := bstep (se 1 (by rfl) ⟨970109, by rfl⟩ : syracuseStep 1293479 = 1940219) B1940219
theorem B6569747 : Blo 574812 6569747 := bstep (se 1 (by rfl) ⟨4927310, by rfl⟩ : syracuseStep 6569747 = 9854621) B9854621
theorem B1294217 : Blo 574812 1294217 := bstep (se 2 (by rfl) ⟨485331, by rfl⟩ : syracuseStep 1294217 = 970663) B970663
theorem B1458283 : Blo 574812 1458283 := bstep (se 1 (by rfl) ⟨1093712, by rfl⟩ : syracuseStep 1458283 = 2187425) B2187425
theorem B7487653 : Blo 574812 7487653 := bstep (se 4 (by rfl) ⟨701967, by rfl⟩ : syracuseStep 7487653 = 1403935) B1403935
theorem B737695 : Blo 574812 737695 := bstep (se 1 (by rfl) ⟨553271, by rfl⟩ : syracuseStep 737695 = 1106543) B1106543
theorem B1295081 : Blo 574812 1295081 := bstep (se 2 (by rfl) ⟨485655, by rfl⟩ : syracuseStep 1295081 = 971311) B971311
theorem B1950857 : Blo 574812 1950857 := bstep (se 2 (by rfl) ⟨731571, by rfl⟩ : syracuseStep 1950857 = 1463143) B1463143
theorem B7882091 : Blo 574812 7882091 := bstep (se 1 (by rfl) ⟨5911568, by rfl⟩ : syracuseStep 7882091 = 11823137) B11823137
theorem B574847 : Blo 574812 574847 := bstep (se 1 (by rfl) ⟨431135, by rfl⟩ : syracuseStep 574847 = 862271) B862271
theorem B10143305 : Blo 574812 10143305 := bstep (se 2 (by rfl) ⟨3803739, by rfl⟩ : syracuseStep 10143305 = 7607479) B7607479
theorem B575215 : Blo 574812 575215 := bstep (se 1 (by rfl) ⟨431411, by rfl⟩ : syracuseStep 575215 = 862823) B862823
theorem B575483 : Blo 574812 575483 := bstep (se 1 (by rfl) ⟨431612, by rfl⟩ : syracuseStep 575483 = 863225) B863225
theorem B57657491 : Blo 574812 57657491 := bstep (se 1 (by rfl) ⟨43243118, by rfl⟩ : syracuseStep 57657491 = 86486237) B86486237
theorem B575815 : Blo 574812 575815 := bstep (se 1 (by rfl) ⟨431861, by rfl⟩ : syracuseStep 575815 = 863723) B863723
theorem B53135797 : Blo 574812 53135797 := bstep (se 5 (by rfl) ⟨2490740, by rfl⟩ : syracuseStep 53135797 = 4981481) B4981481
theorem B575983 : Blo 574812 575983 := bstep (se 1 (by rfl) ⟨431987, by rfl⟩ : syracuseStep 575983 = 863975) B863975
theorem B576283 : Blo 574812 576283 := bstep (se 1 (by rfl) ⟨432212, by rfl⟩ : syracuseStep 576283 = 864425) B864425
theorem B576367 : Blo 574812 576367 := bstep (se 1 (by rfl) ⟨432275, by rfl⟩ : syracuseStep 576367 = 864551) B864551
theorem B576615 : Blo 574812 576615 := bstep (se 1 (by rfl) ⟨432461, by rfl⟩ : syracuseStep 576615 = 864923) B864923
theorem B2969579 : Blo 574812 2969579 := bstep (se 1 (by rfl) ⟨2227184, by rfl⟩ : syracuseStep 2969579 = 4454369) B4454369
theorem B1233119 : Blo 574812 1233119 := bstep (se 1 (by rfl) ⟨924839, by rfl⟩ : syracuseStep 1233119 = 1849679) B1849679
theorem B578335 : Blo 574812 578335 := bstep (se 1 (by rfl) ⟨433751, by rfl⟩ : syracuseStep 578335 = 867503) B867503
theorem B3953747 : Blo 574812 3953747 := bstep (se 1 (by rfl) ⟨2965310, by rfl⟩ : syracuseStep 3953747 = 5930621) B5930621
theorem B578791 : Blo 574812 578791 := bstep (se 1 (by rfl) ⟨434093, by rfl⟩ : syracuseStep 578791 = 868187) B868187
theorem B11098295 : Blo 574812 11098295 := bstep (se 1 (by rfl) ⟨8323721, by rfl⟩ : syracuseStep 11098295 = 16647443) B16647443
theorem B3693023 : Blo 574812 3693023 := bstep (se 1 (by rfl) ⟨2769767, by rfl⟩ : syracuseStep 3693023 = 5539535) B5539535
theorem B973471 : Blo 574812 973471 := bstep (se 1 (by rfl) ⟨730103, by rfl⟩ : syracuseStep 973471 = 1460207) B1460207
theorem B3694049 : Blo 574812 3694049 := bstep (se 2 (by rfl) ⟨1385268, by rfl⟩ : syracuseStep 3694049 = 2770537) B2770537
theorem B2186909 : Blo 574812 2186909 := bstep (se 3 (by rfl) ⟨410045, by rfl⟩ : syracuseStep 2186909 = 820091) B820091
theorem B51109667 : Blo 574812 51109667 := bstep (se 1 (by rfl) ⟨38332250, by rfl⟩ : syracuseStep 51109667 = 76664501) B76664501
theorem B974875 : Blo 574812 974875 := bstep (se 1 (by rfl) ⟨731156, by rfl⟩ : syracuseStep 974875 = 1462313) B1462313
theorem B29909033 : Blo 574812 29909033 := bstep (se 2 (by rfl) ⟨11215887, by rfl⟩ : syracuseStep 29909033 = 22431775) B22431775
theorem B2056391 : Blo 574812 2056391 := bstep (se 1 (by rfl) ⟨1542293, by rfl⟩ : syracuseStep 2056391 = 3084587) B3084587
theorem B2187881 : Blo 574812 2187881 := bstep (se 2 (by rfl) ⟨820455, by rfl⟩ : syracuseStep 2187881 = 1640911) B1640911
theorem B35448263 : Blo 574812 35448263 := bstep (se 1 (by rfl) ⟨26586197, by rfl⟩ : syracuseStep 35448263 = 53172395) B53172395
theorem B6677959 : Blo 574812 6677959 := bstep (se 1 (by rfl) ⟨5008469, by rfl⟩ : syracuseStep 6677959 = 10016939) B10016939
theorem B648751 : Blo 574812 648751 := bstep (se 1 (by rfl) ⟨486563, by rfl⟩ : syracuseStep 648751 = 973127) B973127
theorem B3696509 : Blo 574812 3696509 := bstep (se 3 (by rfl) ⟨693095, by rfl⟩ : syracuseStep 3696509 = 1386191) B1386191
theorem B4942073 : Blo 574812 4942073 := bstep (se 2 (by rfl) ⟨1853277, by rfl⟩ : syracuseStep 4942073 = 3706555) B3706555
theorem B2910653 : Blo 574812 2910653 := bstep (se 3 (by rfl) ⟨545747, by rfl⟩ : syracuseStep 2910653 = 1091495) B1091495
theorem B15198911 : Blo 574812 15198911 := bstep (se 1 (by rfl) ⟨11399183, by rfl⟩ : syracuseStep 15198911 = 22798367) B22798367
theorem B2060329 : Blo 574812 2060329 := bstep (se 2 (by rfl) ⟨772623, by rfl⟩ : syracuseStep 2060329 = 1545247) B1545247
theorem B2193439 : Blo 574812 2193439 := bstep (se 1 (by rfl) ⟨1645079, by rfl⟩ : syracuseStep 2193439 = 3290159) B3290159
theorem B7895231 : Blo 574812 7895231 := bstep (se 1 (by rfl) ⟨5921423, by rfl⟩ : syracuseStep 7895231 = 11842847) B11842847
theorem B3081009737 : Blo 574812 3081009737 := bstep (se 2 (by rfl) ⟨1155378651, by rfl⟩ : syracuseStep 3081009737 = 2310757303) B2310757303
theorem B2194411 : Blo 574812 2194411 := bstep (se 1 (by rfl) ⟨1645808, by rfl⟩ : syracuseStep 2194411 = 3291617) B3291617
theorem B2457641 : Blo 574812 2457641 := bstep (se 2 (by rfl) ⟨921615, by rfl⟩ : syracuseStep 2457641 = 1843231) B1843231
theorem B983593 : Blo 574812 983593 := bstep (se 2 (by rfl) ⟨368847, by rfl⟩ : syracuseStep 983593 = 737695) B737695
theorem B38438327 : Blo 574812 38438327 := bstep (se 1 (by rfl) ⟨28828745, by rfl⟩ : syracuseStep 38438327 = 57657491) B57657491
theorem B4393439 : Blo 574812 4393439 := bstep (se 1 (by rfl) ⟨3295079, by rfl⟩ : syracuseStep 4393439 = 6590159) B6590159
theorem B822079 : Blo 574812 822079 := bstep (se 1 (by rfl) ⟨616559, by rfl⟩ : syracuseStep 822079 = 1233119) B1233119
theorem B1969211 : Blo 574812 1969211 := bstep (se 1 (by rfl) ⟨1476908, by rfl⟩ : syracuseStep 1969211 = 2953817) B2953817
theorem B4918427 : Blo 574812 4918427 := bstep (se 1 (by rfl) ⟨3688820, by rfl⟩ : syracuseStep 4918427 = 7377641) B7377641
theorem B70847729 : Blo 574812 70847729 := bstep (se 2 (by rfl) ⟨26567898, by rfl⟩ : syracuseStep 70847729 = 53135797) B53135797
theorem B36049211 : Blo 574812 36049211 := bstep (se 1 (by rfl) ⟨27036908, by rfl⟩ : syracuseStep 36049211 = 54073817) B54073817
theorem B2462015 : Blo 574812 2462015 := bstep (se 1 (by rfl) ⟨1846511, by rfl⟩ : syracuseStep 2462015 = 3693023) B3693023
theorem B2462699 : Blo 574812 2462699 := bstep (se 1 (by rfl) ⟨1847024, by rfl⟩ : syracuseStep 2462699 = 3694049) B3694049
theorem B4822525 : Blo 574812 4822525 := bstep (se 3 (by rfl) ⟨904223, by rfl⟩ : syracuseStep 4822525 = 1808447) B1808447
theorem B23632175 : Blo 574812 23632175 := bstep (se 1 (by rfl) ⟨17724131, by rfl⟩ : syracuseStep 23632175 = 35448263) B35448263
theorem B2464339 : Blo 574812 2464339 := bstep (se 1 (by rfl) ⟨1848254, by rfl⟩ : syracuseStep 2464339 = 3696509) B3696509
theorem B8216025965 : Blo 574812 8216025965 := bstep (se 3 (by rfl) ⟨1540504868, by rfl⟩ : syracuseStep 8216025965 = 3081009737) B3081009737
theorem B1940435 : Blo 574812 1940435 := bstep (se 1 (by rfl) ⟨1455326, by rfl⟩ : syracuseStep 1940435 = 2910653) B2910653
theorem B10132607 : Blo 574812 10132607 := bstep (se 1 (by rfl) ⟨7599455, by rfl⟩ : syracuseStep 10132607 = 15198911) B15198911
theorem B2924585 : Blo 574812 2924585 := bstep (se 2 (by rfl) ⟨1096719, by rfl⟩ : syracuseStep 2924585 = 2193439) B2193439
theorem B2925881 : Blo 574812 2925881 := bstep (se 2 (by rfl) ⟨1097205, by rfl⟩ : syracuseStep 2925881 = 2194411) B2194411
theorem B862319 : Blo 574812 862319 := bstep (se 1 (by rfl) ⟨646739, by rfl⟩ : syracuseStep 862319 = 1293479) B1293479
theorem B862811 : Blo 574812 862811 := bstep (se 1 (by rfl) ⟨647108, by rfl⟩ : syracuseStep 862811 = 1294217) B1294217
theorem B1944377 : Blo 574812 1944377 := bstep (se 2 (by rfl) ⟨729141, by rfl⟩ : syracuseStep 1944377 = 1458283) B1458283
theorem B863387 : Blo 574812 863387 := bstep (se 1 (by rfl) ⟨647540, by rfl⟩ : syracuseStep 863387 = 1295081) B1295081
theorem B5254727 : Blo 574812 5254727 := bstep (se 1 (by rfl) ⟨3941045, by rfl⟩ : syracuseStep 5254727 = 7882091) B7882091
theorem B6762203 : Blo 574812 6762203 := bstep (se 1 (by rfl) ⟨5071652, by rfl⟩ : syracuseStep 6762203 = 10143305) B10143305
theorem B2469791 : Blo 574812 2469791 := bstep (se 1 (by rfl) ⟨1852343, by rfl⟩ : syracuseStep 2469791 = 3704687) B3704687
theorem B865001 : Blo 574812 865001 := bstep (se 2 (by rfl) ⟨324375, by rfl⟩ : syracuseStep 865001 = 648751) B648751
theorem B2635831 : Blo 574812 2635831 := bstep (se 1 (by rfl) ⟨1976873, by rfl⟩ : syracuseStep 2635831 = 3953747) B3953747
theorem B37992563 : Blo 574812 37992563 := bstep (se 1 (by rfl) ⟨28494422, by rfl⟩ : syracuseStep 37992563 = 56988845) B56988845
theorem B6568289 : Blo 574812 6568289 := bstep (se 2 (by rfl) ⟨2463108, by rfl⟩ : syracuseStep 6568289 = 4926217) B4926217
theorem B4373513 : Blo 574812 4373513 := bstep (se 2 (by rfl) ⟨1640067, by rfl⟩ : syracuseStep 4373513 = 3280135) B3280135
theorem B1293551 : Blo 574812 1293551 := bstep (se 1 (by rfl) ⟨970163, by rfl⟩ : syracuseStep 1293551 = 1940327) B1940327
theorem B1293695 : Blo 574812 1293695 := bstep (se 1 (by rfl) ⟨970271, by rfl⟩ : syracuseStep 1293695 = 1940543) B1940543
theorem B2768537 : Blo 574812 2768537 := bstep (se 2 (by rfl) ⟨1038201, by rfl⟩ : syracuseStep 2768537 = 2076403) B2076403
theorem B1293983 : Blo 574812 1293983 := bstep (se 1 (by rfl) ⟨970487, by rfl⟩ : syracuseStep 1293983 = 1940975) B1940975
theorem B1457939 : Blo 574812 1457939 := bstep (se 1 (by rfl) ⟨1093454, by rfl⟩ : syracuseStep 1457939 = 2186909) B2186909
theorem B19939355 : Blo 574812 19939355 := bstep (se 1 (by rfl) ⟨14954516, by rfl⟩ : syracuseStep 19939355 = 29909033) B29909033
theorem B4997177 : Blo 574812 4997177 := bstep (se 2 (by rfl) ⟨1873941, by rfl⟩ : syracuseStep 4997177 = 3747883) B3747883
theorem B1228907 : Blo 574812 1228907 := bstep (se 1 (by rfl) ⟨921680, by rfl⟩ : syracuseStep 1228907 = 1843361) B1843361
theorem B1949885 : Blo 574812 1949885 := bstep (se 3 (by rfl) ⟨365603, by rfl⟩ : syracuseStep 1949885 = 731207) B731207
theorem B1458587 : Blo 574812 1458587 := bstep (se 1 (by rfl) ⟨1093940, by rfl⟩ : syracuseStep 1458587 = 2187881) B2187881
theorem B2344423 : Blo 574812 2344423 := bstep (se 1 (by rfl) ⟨1758317, by rfl⟩ : syracuseStep 2344423 = 3516635) B3516635
theorem B3294715 : Blo 574812 3294715 := bstep (se 1 (by rfl) ⟨2471036, by rfl⟩ : syracuseStep 3294715 = 4942073) B4942073
theorem B575231 : Blo 574812 575231 := bstep (se 1 (by rfl) ⟨431423, by rfl⟩ : syracuseStep 575231 = 862847) B862847
theorem B1951559 : Blo 574812 1951559 := bstep (se 1 (by rfl) ⟨1463669, by rfl⟩ : syracuseStep 1951559 = 2927339) B2927339
theorem B575487 : Blo 574812 575487 := bstep (se 1 (by rfl) ⟨431615, by rfl⟩ : syracuseStep 575487 = 863231) B863231
theorem B1296647 : Blo 574812 1296647 := bstep (se 1 (by rfl) ⟨972485, by rfl⟩ : syracuseStep 1296647 = 1944971) B1944971
theorem B2346191 : Blo 574812 2346191 := bstep (se 1 (by rfl) ⟨1759643, by rfl⟩ : syracuseStep 2346191 = 3519287) B3519287
theorem B1297961 : Blo 574812 1297961 := bstep (se 2 (by rfl) ⟨486735, by rfl⟩ : syracuseStep 1297961 = 973471) B973471
theorem B577311 : Blo 574812 577311 := bstep (se 1 (by rfl) ⟨432983, by rfl⟩ : syracuseStep 577311 = 865967) B865967
theorem B5263487 : Blo 574812 5263487 := bstep (se 1 (by rfl) ⟨3947615, by rfl⟩ : syracuseStep 5263487 = 7895231) B7895231
theorem B1298663 : Blo 574812 1298663 := bstep (se 1 (by rfl) ⟨973997, by rfl⟩ : syracuseStep 1298663 = 1947995) B1947995
theorem B577775 : Blo 574812 577775 := bstep (se 1 (by rfl) ⟨433331, by rfl⟩ : syracuseStep 577775 = 866663) B866663
theorem B577791 : Blo 574812 577791 := bstep (se 1 (by rfl) ⟨433343, by rfl⟩ : syracuseStep 577791 = 866687) B866687
theorem B577819 : Blo 574812 577819 := bstep (se 1 (by rfl) ⟨433364, by rfl⟩ : syracuseStep 577819 = 866729) B866729
theorem B1298843 : Blo 574812 1298843 := bstep (se 1 (by rfl) ⟨974132, by rfl⟩ : syracuseStep 1298843 = 1948265) B1948265
theorem B578023 : Blo 574812 578023 := bstep (se 1 (by rfl) ⟨433517, by rfl⟩ : syracuseStep 578023 = 867035) B867035
theorem B971291 : Blo 574812 971291 := bstep (se 1 (by rfl) ⟨728468, by rfl⟩ : syracuseStep 971291 = 1456937) B1456937
theorem B578139 : Blo 574812 578139 := bstep (se 1 (by rfl) ⟨433604, by rfl⟩ : syracuseStep 578139 = 867209) B867209
theorem B4379831 : Blo 574812 4379831 := bstep (se 1 (by rfl) ⟨3284873, by rfl⟩ : syracuseStep 4379831 = 6569747) B6569747
theorem B7918877 : Blo 574812 7918877 := bstep (se 3 (by rfl) ⟨1484789, by rfl⟩ : syracuseStep 7918877 = 2969579) B2969579
theorem B1299833 : Blo 574812 1299833 := bstep (se 2 (by rfl) ⟨487437, by rfl⟩ : syracuseStep 1299833 = 974875) B974875
theorem B9983537 : Blo 574812 9983537 := bstep (se 2 (by rfl) ⟨3743826, by rfl⟩ : syracuseStep 9983537 = 7487653) B7487653
theorem B972553 : Blo 574812 972553 := bstep (se 2 (by rfl) ⟨364707, by rfl⟩ : syracuseStep 972553 = 729415) B729415
theorem B1300571 : Blo 574812 1300571 := bstep (se 1 (by rfl) ⟨975428, by rfl⟩ : syracuseStep 1300571 = 1950857) B1950857
theorem B8903945 : Blo 574812 8903945 := bstep (se 2 (by rfl) ⟨3338979, by rfl⟩ : syracuseStep 8903945 = 6677959) B6677959
theorem B7398863 : Blo 574812 7398863 := bstep (se 1 (by rfl) ⟨5549147, by rfl⟩ : syracuseStep 7398863 = 11098295) B11098295
theorem B34073111 : Blo 574812 34073111 := bstep (se 1 (by rfl) ⟨25554833, by rfl⟩ : syracuseStep 34073111 = 51109667) B51109667
theorem B2747105 : Blo 574812 2747105 := bstep (se 2 (by rfl) ⟨1030164, by rfl⟩ : syracuseStep 2747105 = 2060329) B2060329
theorem B1370927 : Blo 574812 1370927 := bstep (se 1 (by rfl) ⟨1028195, by rfl⟩ : syracuseStep 1370927 = 2056391) B2056391
theorem B4159151 : Blo 574812 4159151 := bstep (se 1 (by rfl) ⟨3119363, by rfl⟩ : syracuseStep 4159151 = 6238727) B6238727
theorem B819271 : Blo 574812 819271 := bstep (se 1 (by rfl) ⟨614453, by rfl⟩ : syracuseStep 819271 = 1228907) B1228907
theorem B6553709 : Blo 574812 6553709 := bstep (se 3 (by rfl) ⟨1228820, by rfl⟩ : syracuseStep 6553709 = 2457641) B2457641
theorem B4392953 : Blo 574812 4392953 := bstep (se 2 (by rfl) ⟨1647357, by rfl⟩ : syracuseStep 4392953 = 3294715) B3294715
theorem B3278951 : Blo 574812 3278951 := bstep (se 1 (by rfl) ⟨2459213, by rfl⟩ : syracuseStep 3278951 = 4918427) B4918427
theorem B3508991 : Blo 574812 3508991 := bstep (se 1 (by rfl) ⟨2631743, by rfl⟩ : syracuseStep 3508991 = 5263487) B5263487
theorem B5245829 : Blo 574812 5245829 := bstep (se 4 (by rfl) ⟨491796, by rfl⟩ : syracuseStep 5245829 = 983593) B983593
theorem B1641799 : Blo 574812 1641799 := bstep (se 1 (by rfl) ⟨1231349, by rfl⟩ : syracuseStep 1641799 = 2462699) B2462699
theorem B2919887 : Blo 574812 2919887 := bstep (se 1 (by rfl) ⟨2189915, by rfl⟩ : syracuseStep 2919887 = 4379831) B4379831
theorem B5279251 : Blo 574812 5279251 := bstep (se 1 (by rfl) ⟨3959438, by rfl⟩ : syracuseStep 5279251 = 7918877) B7918877
theorem B6655691 : Blo 574812 6655691 := bstep (se 1 (by rfl) ⟨4991768, by rfl⟩ : syracuseStep 6655691 = 9983537) B9983537
theorem B102502205 : Blo 574812 102502205 := bstep (se 3 (by rfl) ⟨19219163, by rfl⟩ : syracuseStep 102502205 = 38438327) B38438327
theorem B6755071 : Blo 574812 6755071 := bstep (se 1 (by rfl) ⟨5066303, by rfl⟩ : syracuseStep 6755071 = 10132607) B10132607
theorem B5935963 : Blo 574812 5935963 := bstep (se 1 (by rfl) ⟨4451972, by rfl⟩ : syracuseStep 5935963 = 8903945) B8903945
theorem B22715407 : Blo 574812 22715407 := bstep (se 1 (by rfl) ⟨17036555, by rfl⟩ : syracuseStep 22715407 = 34073111) B34073111
theorem B6430033 : Blo 574812 6430033 := bstep (se 2 (by rfl) ⟨2411262, by rfl⟩ : syracuseStep 6430033 = 4822525) B4822525
theorem B1646527 : Blo 574812 1646527 := bstep (se 1 (by rfl) ⟨1234895, by rfl⟩ : syracuseStep 1646527 = 2469791) B2469791
theorem B3514441 : Blo 574812 3514441 := bstep (se 2 (by rfl) ⟨1317915, by rfl⟩ : syracuseStep 3514441 = 2635831) B2635831
theorem B5251229 : Blo 574812 5251229 := bstep (se 3 (by rfl) ⟨984605, by rfl⟩ : syracuseStep 5251229 = 1969211) B1969211
theorem B3285785 : Blo 574812 3285785 := bstep (se 2 (by rfl) ⟨1232169, by rfl⟩ : syracuseStep 3285785 = 2464339) B2464339
theorem B7382765 : Blo 574812 7382765 := bstep (se 3 (by rfl) ⟨1384268, by rfl⟩ : syracuseStep 7382765 = 2768537) B2768537
theorem B862367 : Blo 574812 862367 := bstep (se 1 (by rfl) ⟨646775, by rfl⟩ : syracuseStep 862367 = 1293551) B1293551
theorem B862463 : Blo 574812 862463 := bstep (se 1 (by rfl) ⟨646847, by rfl⟩ : syracuseStep 862463 = 1293695) B1293695
theorem B862655 : Blo 574812 862655 := bstep (se 1 (by rfl) ⟨646991, by rfl⟩ : syracuseStep 862655 = 1293983) B1293983
theorem B6565373 : Blo 574812 6565373 := bstep (se 3 (by rfl) ⟨1231007, by rfl⟩ : syracuseStep 6565373 = 2462015) B2462015
theorem B864431 : Blo 574812 864431 := bstep (se 1 (by rfl) ⟨648323, by rfl⟩ : syracuseStep 864431 = 1296647) B1296647
theorem B2928959 : Blo 574812 2928959 := bstep (se 1 (by rfl) ⟨2196719, by rfl⟩ : syracuseStep 2928959 = 4393439) B4393439
theorem B3125897 : Blo 574812 3125897 := bstep (se 2 (by rfl) ⟨1172211, by rfl⟩ : syracuseStep 3125897 = 2344423) B2344423
theorem B47231819 : Blo 574812 47231819 := bstep (se 1 (by rfl) ⟨35423864, by rfl⟩ : syracuseStep 47231819 = 70847729) B70847729
theorem B865307 : Blo 574812 865307 := bstep (se 1 (by rfl) ⟨648980, by rfl⟩ : syracuseStep 865307 = 1297961) B1297961
theorem B865775 : Blo 574812 865775 := bstep (se 1 (by rfl) ⟨649331, by rfl⟩ : syracuseStep 865775 = 1298663) B1298663
theorem B24032807 : Blo 574812 24032807 := bstep (se 1 (by rfl) ⟨18024605, by rfl⟩ : syracuseStep 24032807 = 36049211) B36049211
theorem B865895 : Blo 574812 865895 := bstep (se 1 (by rfl) ⟨649421, by rfl⟩ : syracuseStep 865895 = 1298843) B1298843
theorem B866555 : Blo 574812 866555 := bstep (se 1 (by rfl) ⟨649916, by rfl⟩ : syracuseStep 866555 = 1299833) B1299833
theorem B1096105 : Blo 574812 1096105 := bstep (se 2 (by rfl) ⟨411039, by rfl⟩ : syracuseStep 1096105 = 822079) B822079
theorem B867047 : Blo 574812 867047 := bstep (se 1 (by rfl) ⟨650285, by rfl⟩ : syracuseStep 867047 = 1300571) B1300571
theorem B5477350643 : Blo 574812 5477350643 := bstep (se 1 (by rfl) ⟨4108012982, by rfl⟩ : syracuseStep 5477350643 = 8216025965) B8216025965
theorem B1293623 : Blo 574812 1293623 := bstep (se 1 (by rfl) ⟨970217, by rfl⟩ : syracuseStep 1293623 = 1940435) B1940435
theorem B1949723 : Blo 574812 1949723 := bstep (se 1 (by rfl) ⟨1462292, by rfl⟩ : syracuseStep 1949723 = 2924585) B2924585
theorem B1950587 : Blo 574812 1950587 := bstep (se 1 (by rfl) ⟨1462940, by rfl⟩ : syracuseStep 1950587 = 2925881) B2925881
theorem B4932575 : Blo 574812 4932575 := bstep (se 1 (by rfl) ⟨3699431, by rfl⟩ : syracuseStep 4932575 = 7398863) B7398863
theorem B574879 : Blo 574812 574879 := bstep (se 1 (by rfl) ⟨431159, by rfl⟩ : syracuseStep 574879 = 862319) B862319
theorem B575207 : Blo 574812 575207 := bstep (se 1 (by rfl) ⟨431405, by rfl⟩ : syracuseStep 575207 = 862811) B862811
theorem B1296251 : Blo 574812 1296251 := bstep (se 1 (by rfl) ⟨972188, by rfl⟩ : syracuseStep 1296251 = 1944377) B1944377
theorem B575591 : Blo 574812 575591 := bstep (se 1 (by rfl) ⟨431693, by rfl⟩ : syracuseStep 575591 = 863387) B863387
theorem B1296737 : Blo 574812 1296737 := bstep (se 2 (by rfl) ⟨486276, by rfl⟩ : syracuseStep 1296737 = 972553) B972553
theorem B4508135 : Blo 574812 4508135 := bstep (se 1 (by rfl) ⟨3381101, by rfl⟩ : syracuseStep 4508135 = 6762203) B6762203
theorem B576667 : Blo 574812 576667 := bstep (se 1 (by rfl) ⟨432500, by rfl⟩ : syracuseStep 576667 = 865001) B865001
theorem B2772767 : Blo 574812 2772767 := bstep (se 1 (by rfl) ⟨2079575, by rfl⟩ : syracuseStep 2772767 = 4159151) B4159151
theorem B14012605 : Blo 574812 14012605 := bstep (se 3 (by rfl) ⟨2627363, by rfl⟩ : syracuseStep 14012605 = 5254727) B5254727
theorem B4378859 : Blo 574812 4378859 := bstep (se 1 (by rfl) ⟨3284144, by rfl⟩ : syracuseStep 4378859 = 6568289) B6568289
theorem B971959 : Blo 574812 971959 := bstep (se 1 (by rfl) ⟨728969, by rfl⟩ : syracuseStep 971959 = 1457939) B1457939
theorem B13292903 : Blo 574812 13292903 := bstep (se 1 (by rfl) ⟨9969677, by rfl⟩ : syracuseStep 13292903 = 19939355) B19939355
theorem B3331451 : Blo 574812 3331451 := bstep (se 1 (by rfl) ⟨2498588, by rfl⟩ : syracuseStep 3331451 = 4997177) B4997177
theorem B1299923 : Blo 574812 1299923 := bstep (se 1 (by rfl) ⟨974942, by rfl⟩ : syracuseStep 1299923 = 1949885) B1949885
theorem B972391 : Blo 574812 972391 := bstep (se 1 (by rfl) ⟨729293, by rfl⟩ : syracuseStep 972391 = 1458587) B1458587
theorem B1301039 : Blo 574812 1301039 := bstep (se 1 (by rfl) ⟨975779, by rfl⟩ : syracuseStep 1301039 = 1951559) B1951559
theorem B1564127 : Blo 574812 1564127 := bstep (se 1 (by rfl) ⟨1173095, by rfl⟩ : syracuseStep 1564127 = 2346191) B2346191
theorem B647527 : Blo 574812 647527 := bstep (se 1 (by rfl) ⟨485645, by rfl⟩ : syracuseStep 647527 = 971291) B971291
theorem B15754783 : Blo 574812 15754783 := bstep (se 1 (by rfl) ⟨11816087, by rfl⟩ : syracuseStep 15754783 = 23632175) B23632175
theorem B1831403 : Blo 574812 1831403 := bstep (se 1 (by rfl) ⟨1373552, by rfl⟩ : syracuseStep 1831403 = 2747105) B2747105
theorem B913951 : Blo 574812 913951 := bstep (se 1 (by rfl) ⟨685463, by rfl⟩ : syracuseStep 913951 = 1370927) B1370927
theorem B25328375 : Blo 574812 25328375 := bstep (se 1 (by rfl) ⟨18996281, by rfl⟩ : syracuseStep 25328375 = 37992563) B37992563
theorem B2915675 : Blo 574812 2915675 := bstep (se 1 (by rfl) ⟨2186756, by rfl⟩ : syracuseStep 2915675 = 4373513) B4373513
theorem B4685921 : Blo 574812 4685921 := bstep (se 2 (by rfl) ⟨1757220, by rfl⟩ : syracuseStep 4685921 = 3514441) B3514441
theorem B21006377 : Blo 574812 21006377 := bstep (se 2 (by rfl) ⟨7877391, by rfl⟩ : syracuseStep 21006377 = 15754783) B15754783
theorem B2919239 : Blo 574812 2919239 := bstep (se 1 (by rfl) ⟨2189429, by rfl⟩ : syracuseStep 2919239 = 4378859) B4378859
theorem B18683473 : Blo 574812 18683473 := bstep (se 2 (by rfl) ⟨7006302, by rfl⟩ : syracuseStep 18683473 = 14012605) B14012605
theorem B1218601 : Blo 574812 1218601 := bstep (se 2 (by rfl) ⟨456975, by rfl⟩ : syracuseStep 1218601 = 913951) B913951
theorem B4921843 : Blo 574812 4921843 := bstep (se 1 (by rfl) ⟨3691382, by rfl⟩ : syracuseStep 4921843 = 7382765) B7382765
theorem B1220935 : Blo 574812 1220935 := bstep (se 1 (by rfl) ⟨915701, by rfl⟩ : syracuseStep 1220935 = 1831403) B1831403
theorem B30287209 : Blo 574812 30287209 := bstep (se 2 (by rfl) ⟨11357703, by rfl⟩ : syracuseStep 30287209 = 22715407) B22715407
theorem B16885583 : Blo 574812 16885583 := bstep (se 1 (by rfl) ⟨12664187, by rfl⟩ : syracuseStep 16885583 = 25328375) B25328375
theorem B862415 : Blo 574812 862415 := bstep (se 1 (by rfl) ⟨646811, by rfl⟩ : syracuseStep 862415 = 1293623) B1293623
theorem B1943783 : Blo 574812 1943783 := bstep (se 1 (by rfl) ⟨1457837, by rfl⟩ : syracuseStep 1943783 = 2915675) B2915675
theorem B4369139 : Blo 574812 4369139 := bstep (se 1 (by rfl) ⟨3276854, by rfl⟩ : syracuseStep 4369139 = 6553709) B6553709
theorem B1092361 : Blo 574812 1092361 := bstep (se 2 (by rfl) ⟨409635, by rfl⟩ : syracuseStep 1092361 = 819271) B819271
theorem B863369 : Blo 574812 863369 := bstep (se 2 (by rfl) ⟨323763, by rfl⟩ : syracuseStep 863369 = 647527) B647527
theorem B3288383 : Blo 574812 3288383 := bstep (se 1 (by rfl) ⟨2466287, by rfl⟩ : syracuseStep 3288383 = 4932575) B4932575
theorem B864167 : Blo 574812 864167 := bstep (se 1 (by rfl) ⟨648125, by rfl⟩ : syracuseStep 864167 = 1296251) B1296251
theorem B2928635 : Blo 574812 2928635 := bstep (se 1 (by rfl) ⟨2196476, by rfl⟩ : syracuseStep 2928635 = 4392953) B4392953
theorem B864491 : Blo 574812 864491 := bstep (se 1 (by rfl) ⟨648368, by rfl⟩ : syracuseStep 864491 = 1296737) B1296737
theorem B2339327 : Blo 574812 2339327 := bstep (se 1 (by rfl) ⟨1754495, by rfl⟩ : syracuseStep 2339327 = 3508991) B3508991
theorem B1946591 : Blo 574812 1946591 := bstep (se 1 (by rfl) ⟨1459943, by rfl⟩ : syracuseStep 1946591 = 2919887) B2919887
theorem B4437127 : Blo 574812 4437127 := bstep (se 1 (by rfl) ⟨3327845, by rfl⟩ : syracuseStep 4437127 = 6655691) B6655691
theorem B1848511 : Blo 574812 1848511 := bstep (se 1 (by rfl) ⟨1386383, by rfl⟩ : syracuseStep 1848511 = 2772767) B2772767
theorem B68334803 : Blo 574812 68334803 := bstep (se 1 (by rfl) ⟨51251102, by rfl⟩ : syracuseStep 68334803 = 102502205) B102502205
theorem B8861935 : Blo 574812 8861935 := bstep (se 1 (by rfl) ⟨6646451, by rfl⟩ : syracuseStep 8861935 = 13292903) B13292903
theorem B866615 : Blo 574812 866615 := bstep (se 1 (by rfl) ⟨649961, by rfl⟩ : syracuseStep 866615 = 1299923) B1299923
theorem B867359 : Blo 574812 867359 := bstep (se 1 (by rfl) ⟨650519, by rfl⟩ : syracuseStep 867359 = 1301039) B1301039
theorem B7914617 : Blo 574812 7914617 := bstep (se 2 (by rfl) ⟨2967981, by rfl⟩ : syracuseStep 7914617 = 5935963) B5935963
theorem B574911 : Blo 574812 574911 := bstep (se 1 (by rfl) ⟨431183, by rfl⟩ : syracuseStep 574911 = 862367) B862367
theorem B574975 : Blo 574812 574975 := bstep (se 1 (by rfl) ⟨431231, by rfl⟩ : syracuseStep 574975 = 862463) B862463
theorem B1295945 : Blo 574812 1295945 := bstep (se 2 (by rfl) ⟨485979, by rfl⟩ : syracuseStep 1295945 = 971959) B971959
theorem B575103 : Blo 574812 575103 := bstep (se 1 (by rfl) ⟨431327, by rfl⟩ : syracuseStep 575103 = 862655) B862655
theorem B1296521 : Blo 574812 1296521 := bstep (se 2 (by rfl) ⟨486195, by rfl⟩ : syracuseStep 1296521 = 972391) B972391
theorem B4376915 : Blo 574812 4376915 := bstep (se 1 (by rfl) ⟨3282686, by rfl⟩ : syracuseStep 4376915 = 6565373) B6565373
theorem B576287 : Blo 574812 576287 := bstep (se 1 (by rfl) ⟨432215, by rfl⟩ : syracuseStep 576287 = 864431) B864431
theorem B1952639 : Blo 574812 1952639 := bstep (se 1 (by rfl) ⟨1464479, by rfl⟩ : syracuseStep 1952639 = 2928959) B2928959
theorem B2083931 : Blo 574812 2083931 := bstep (se 1 (by rfl) ⟨1562948, by rfl⟩ : syracuseStep 2083931 = 3125897) B3125897
theorem B1461473 : Blo 574812 1461473 := bstep (se 2 (by rfl) ⟨548052, by rfl⟩ : syracuseStep 1461473 = 1096105) B1096105
theorem B576871 : Blo 574812 576871 := bstep (se 1 (by rfl) ⟨432653, by rfl⟩ : syracuseStep 576871 = 865307) B865307
theorem B577183 : Blo 574812 577183 := bstep (se 1 (by rfl) ⟨432887, by rfl⟩ : syracuseStep 577183 = 865775) B865775
theorem B577263 : Blo 574812 577263 := bstep (se 1 (by rfl) ⟨432947, by rfl⟩ : syracuseStep 577263 = 865895) B865895
theorem B577703 : Blo 574812 577703 := bstep (se 1 (by rfl) ⟨433277, by rfl⟩ : syracuseStep 577703 = 866555) B866555
theorem B8573377 : Blo 574812 8573377 := bstep (se 2 (by rfl) ⟨3215016, by rfl⟩ : syracuseStep 8573377 = 6430033) B6430033
theorem B578031 : Blo 574812 578031 := bstep (se 1 (by rfl) ⟨433523, by rfl⟩ : syracuseStep 578031 = 867047) B867047
theorem B1299815 : Blo 574812 1299815 := bstep (se 1 (by rfl) ⟨974861, by rfl⟩ : syracuseStep 1299815 = 1949723) B1949723
theorem B1300391 : Blo 574812 1300391 := bstep (se 1 (by rfl) ⟨975293, by rfl⟩ : syracuseStep 1300391 = 1950587) B1950587
theorem B2185967 : Blo 574812 2185967 := bstep (se 1 (by rfl) ⟨1639475, by rfl⟩ : syracuseStep 2185967 = 3278951) B3278951
theorem B3005423 : Blo 574812 3005423 := bstep (se 1 (by rfl) ⟨2254067, by rfl⟩ : syracuseStep 3005423 = 4508135) B4508135
theorem B3497219 : Blo 574812 3497219 := bstep (se 1 (by rfl) ⟨2622914, by rfl⟩ : syracuseStep 3497219 = 5245829) B5245829
theorem B2220967 : Blo 574812 2220967 := bstep (se 1 (by rfl) ⟨1665725, by rfl⟩ : syracuseStep 2220967 = 3331451) B3331451
theorem B2189065 : Blo 574812 2189065 := bstep (se 2 (by rfl) ⟨820899, by rfl⟩ : syracuseStep 2189065 = 1641799) B1641799
theorem B7039001 : Blo 574812 7039001 := bstep (se 2 (by rfl) ⟨2639625, by rfl⟩ : syracuseStep 7039001 = 5279251) B5279251
theorem B1042751 : Blo 574812 1042751 := bstep (se 1 (by rfl) ⟨782063, by rfl⟩ : syracuseStep 1042751 = 1564127) B1564127
theorem B3500819 : Blo 574812 3500819 := bstep (se 1 (by rfl) ⟨2625614, by rfl⟩ : syracuseStep 3500819 = 5251229) B5251229
theorem B2190523 : Blo 574812 2190523 := bstep (se 1 (by rfl) ⟨1642892, by rfl⟩ : syracuseStep 2190523 = 3285785) B3285785
theorem B9006761 : Blo 574812 9006761 := bstep (se 2 (by rfl) ⟨3377535, by rfl⟩ : syracuseStep 9006761 = 6755071) B6755071
theorem B31487879 : Blo 574812 31487879 := bstep (se 1 (by rfl) ⟨23615909, by rfl⟩ : syracuseStep 31487879 = 47231819) B47231819
theorem B16021871 : Blo 574812 16021871 := bstep (se 1 (by rfl) ⟨12016403, by rfl⟩ : syracuseStep 16021871 = 24032807) B24032807
theorem B3651567095 : Blo 574812 3651567095 := bstep (se 1 (by rfl) ⟨2738675321, by rfl⟩ : syracuseStep 3651567095 = 5477350643) B5477350643
theorem B2195369 : Blo 574812 2195369 := bstep (se 2 (by rfl) ⟨823263, by rfl⟩ : syracuseStep 2195369 = 1646527) B1646527
theorem B5276411 : Blo 574812 5276411 := bstep (se 1 (by rfl) ⟨3957308, by rfl⟩ : syracuseStep 5276411 = 7914617) B7914617
theorem B2917943 : Blo 574812 2917943 := bstep (se 1 (by rfl) ⟨2188457, by rfl⟩ : syracuseStep 2917943 = 4376915) B4376915
theorem B2918753 : Blo 574812 2918753 := bstep (se 2 (by rfl) ⟨1094532, by rfl⟩ : syracuseStep 2918753 = 2189065) B2189065
theorem B2920697 : Blo 574812 2920697 := bstep (se 2 (by rfl) ⟨1095261, by rfl⟩ : syracuseStep 2920697 = 2190523) B2190523
theorem B2003615 : Blo 574812 2003615 := bstep (se 1 (by rfl) ⟨1502711, by rfl⟩ : syracuseStep 2003615 = 3005423) B3005423
theorem B2331479 : Blo 574812 2331479 := bstep (se 1 (by rfl) ⟨1748609, by rfl⟩ : syracuseStep 2331479 = 3497219) B3497219
theorem B4692667 : Blo 574812 4692667 := bstep (se 1 (by rfl) ⟨3519500, by rfl⟩ : syracuseStep 4692667 = 7039001) B7039001
theorem B2464681 : Blo 574812 2464681 := bstep (se 2 (by rfl) ⟨924255, by rfl⟩ : syracuseStep 2464681 = 1848511) B1848511
theorem B2333879 : Blo 574812 2333879 := bstep (se 1 (by rfl) ⟨1750409, by rfl⟩ : syracuseStep 2333879 = 3500819) B3500819
theorem B24911297 : Blo 574812 24911297 := bstep (se 2 (by rfl) ⟨9341736, by rfl⟩ : syracuseStep 24911297 = 18683473) B18683473
theorem B6004507 : Blo 574812 6004507 := bstep (se 1 (by rfl) ⟨4503380, by rfl⟩ : syracuseStep 6004507 = 9006761) B9006761
theorem B6562457 : Blo 574812 6562457 := bstep (se 2 (by rfl) ⟨2460921, by rfl⟩ : syracuseStep 6562457 = 4921843) B4921843
theorem B45556535 : Blo 574812 45556535 := bstep (se 1 (by rfl) ⟨34167401, by rfl⟩ : syracuseStep 45556535 = 68334803) B68334803
theorem B2434378063 : Blo 574812 2434378063 := bstep (se 1 (by rfl) ⟨1825783547, by rfl⟩ : syracuseStep 2434378063 = 3651567095) B3651567095
theorem B3123947 : Blo 574812 3123947 := bstep (se 1 (by rfl) ⟨2342960, by rfl⟩ : syracuseStep 3123947 = 4685921) B4685921
theorem B863963 : Blo 574812 863963 := bstep (se 1 (by rfl) ⟨647972, by rfl⟩ : syracuseStep 863963 = 1295945) B1295945
theorem B2961289 : Blo 574812 2961289 := bstep (se 2 (by rfl) ⟨1110483, by rfl⟩ : syracuseStep 2961289 = 2220967) B2220967
theorem B6238205 : Blo 574812 6238205 := bstep (se 3 (by rfl) ⟨1169663, by rfl⟩ : syracuseStep 6238205 = 2339327) B2339327
theorem B14004251 : Blo 574812 14004251 := bstep (se 1 (by rfl) ⟨10503188, by rfl⟩ : syracuseStep 14004251 = 21006377) B21006377
theorem B864347 : Blo 574812 864347 := bstep (se 1 (by rfl) ⟨648260, by rfl⟩ : syracuseStep 864347 = 1296521) B1296521
theorem B40382945 : Blo 574812 40382945 := bstep (se 2 (by rfl) ⟨15143604, by rfl⟩ : syracuseStep 40382945 = 30287209) B30287209
theorem B1946159 : Blo 574812 1946159 := bstep (se 1 (by rfl) ⟨1459619, by rfl⟩ : syracuseStep 1946159 = 2919239) B2919239
theorem B1389287 : Blo 574812 1389287 := bstep (se 1 (by rfl) ⟨1041965, by rfl⟩ : syracuseStep 1389287 = 2083931) B2083931
theorem B866543 : Blo 574812 866543 := bstep (se 1 (by rfl) ⟨649907, by rfl⟩ : syracuseStep 866543 = 1299815) B1299815
theorem B1456481 : Blo 574812 1456481 := bstep (se 2 (by rfl) ⟨546180, by rfl⟩ : syracuseStep 1456481 = 1092361) B1092361
theorem B866927 : Blo 574812 866927 := bstep (se 1 (by rfl) ⟨650195, by rfl⟩ : syracuseStep 866927 = 1300391) B1300391
theorem B1457311 : Blo 574812 1457311 := bstep (se 1 (by rfl) ⟨1092983, by rfl⟩ : syracuseStep 1457311 = 2185967) B2185967
theorem B83967677 : Blo 574812 83967677 := bstep (se 3 (by rfl) ⟨15743939, by rfl⟩ : syracuseStep 83967677 = 31487879) B31487879
theorem B11257055 : Blo 574812 11257055 := bstep (se 1 (by rfl) ⟨8442791, by rfl⟩ : syracuseStep 11257055 = 16885583) B16885583
theorem B574943 : Blo 574812 574943 := bstep (se 1 (by rfl) ⟨431207, by rfl⟩ : syracuseStep 574943 = 862415) B862415
theorem B1295855 : Blo 574812 1295855 := bstep (se 1 (by rfl) ⟨971891, by rfl⟩ : syracuseStep 1295855 = 1943783) B1943783
theorem B5916169 : Blo 574812 5916169 := bstep (se 2 (by rfl) ⟨2218563, by rfl⟩ : syracuseStep 5916169 = 4437127) B4437127
theorem B575579 : Blo 574812 575579 := bstep (se 1 (by rfl) ⟨431684, by rfl⟩ : syracuseStep 575579 = 863369) B863369
theorem B576111 : Blo 574812 576111 := bstep (se 1 (by rfl) ⟨432083, by rfl⟩ : syracuseStep 576111 = 864167) B864167
theorem B1952423 : Blo 574812 1952423 := bstep (se 1 (by rfl) ⟨1464317, by rfl⟩ : syracuseStep 1952423 = 2928635) B2928635
theorem B1624801 : Blo 574812 1624801 := bstep (se 2 (by rfl) ⟨609300, by rfl⟩ : syracuseStep 1624801 = 1218601) B1218601
theorem B576327 : Blo 574812 576327 := bstep (se 1 (by rfl) ⟨432245, by rfl⟩ : syracuseStep 576327 = 864491) B864491
theorem B11815913 : Blo 574812 11815913 := bstep (se 2 (by rfl) ⟨4430967, by rfl⟩ : syracuseStep 11815913 = 8861935) B8861935
theorem B1297727 : Blo 574812 1297727 := bstep (se 1 (by rfl) ⟨973295, by rfl⟩ : syracuseStep 1297727 = 1946591) B1946591
theorem B577743 : Blo 574812 577743 := bstep (se 1 (by rfl) ⟨433307, by rfl⟩ : syracuseStep 577743 = 866615) B866615
theorem B578239 : Blo 574812 578239 := bstep (se 1 (by rfl) ⟨433679, by rfl⟩ : syracuseStep 578239 = 867359) B867359
theorem B1463579 : Blo 574812 1463579 := bstep (se 1 (by rfl) ⟨1097684, by rfl⟩ : syracuseStep 1463579 = 2195369) B2195369
theorem B1627913 : Blo 574812 1627913 := bstep (se 2 (by rfl) ⟨610467, by rfl⟩ : syracuseStep 1627913 = 1220935) B1220935
theorem B1301759 : Blo 574812 1301759 := bstep (se 1 (by rfl) ⟨976319, by rfl⟩ : syracuseStep 1301759 = 1952639) B1952639
theorem B974315 : Blo 574812 974315 := bstep (se 1 (by rfl) ⟨730736, by rfl⟩ : syracuseStep 974315 = 1461473) B1461473
theorem B11431169 : Blo 574812 11431169 := bstep (se 2 (by rfl) ⟨4286688, by rfl⟩ : syracuseStep 11431169 = 8573377) B8573377
theorem B2780669 : Blo 574812 2780669 := bstep (se 3 (by rfl) ⟨521375, by rfl⟩ : syracuseStep 2780669 = 1042751) B1042751
theorem B2912759 : Blo 574812 2912759 := bstep (se 1 (by rfl) ⟨2184569, by rfl⟩ : syracuseStep 2912759 = 4369139) B4369139
theorem B2192255 : Blo 574812 2192255 := bstep (se 1 (by rfl) ⟨1644191, by rfl⟩ : syracuseStep 2192255 = 3288383) B3288383
theorem B10681247 : Blo 574812 10681247 := bstep (se 1 (by rfl) ⟨8010935, by rfl⟩ : syracuseStep 10681247 = 16021871) B16021871
theorem B7504703 : Blo 574812 7504703 := bstep (se 1 (by rfl) ⟨5628527, by rfl⟩ : syracuseStep 7504703 = 11257055) B11257055
theorem B3245837417 : Blo 574812 3245837417 := bstep (se 2 (by rfl) ⟨1217189031, by rfl⟩ : syracuseStep 3245837417 = 2434378063) B2434378063
theorem B2166401 : Blo 574812 2166401 := bstep (se 2 (by rfl) ⟨812400, by rfl⟩ : syracuseStep 2166401 = 1624801) B1624801
theorem B1085275 : Blo 574812 1085275 := bstep (se 1 (by rfl) ⟨813956, by rfl⟩ : syracuseStep 1085275 = 1627913) B1627913
theorem B8330525 : Blo 574812 8330525 := bstep (se 3 (by rfl) ⟨1561973, by rfl⟩ : syracuseStep 8330525 = 3123947) B3123947
theorem B1941839 : Blo 574812 1941839 := bstep (se 1 (by rfl) ⟨1456379, by rfl⟩ : syracuseStep 1941839 = 2912759) B2912759
theorem B926191 : Blo 574812 926191 := bstep (se 1 (by rfl) ⟨694643, by rfl⟩ : syracuseStep 926191 = 1389287) B1389287
theorem B3286241 : Blo 574812 3286241 := bstep (se 2 (by rfl) ⟨1232340, by rfl⟩ : syracuseStep 3286241 = 2464681) B2464681
theorem B1943081 : Blo 574812 1943081 := bstep (se 2 (by rfl) ⟨728655, by rfl⟩ : syracuseStep 1943081 = 1457311) B1457311
theorem B7120831 : Blo 574812 7120831 := bstep (se 1 (by rfl) ⟨5340623, by rfl⟩ : syracuseStep 7120831 = 10681247) B10681247
theorem B8006009 : Blo 574812 8006009 := bstep (se 2 (by rfl) ⟨3002253, by rfl⟩ : syracuseStep 8006009 = 6004507) B6004507
theorem B55978451 : Blo 574812 55978451 := bstep (se 1 (by rfl) ⟨41983838, by rfl⟩ : syracuseStep 55978451 = 83967677) B83967677
theorem B3517607 : Blo 574812 3517607 := bstep (se 1 (by rfl) ⟨2638205, by rfl⟩ : syracuseStep 3517607 = 5276411) B5276411
theorem B863903 : Blo 574812 863903 := bstep (se 1 (by rfl) ⟨647927, by rfl⟩ : syracuseStep 863903 = 1295855) B1295855
theorem B1945295 : Blo 574812 1945295 := bstep (se 1 (by rfl) ⟨1458971, by rfl⟩ : syracuseStep 1945295 = 2917943) B2917943
theorem B1945835 : Blo 574812 1945835 := bstep (se 1 (by rfl) ⟨1459376, by rfl⟩ : syracuseStep 1945835 = 2918753) B2918753
theorem B865151 : Blo 574812 865151 := bstep (se 1 (by rfl) ⟨648863, by rfl⟩ : syracuseStep 865151 = 1297727) B1297727
theorem B1947131 : Blo 574812 1947131 := bstep (se 1 (by rfl) ⟨1460348, by rfl⟩ : syracuseStep 1947131 = 2920697) B2920697
theorem B1554319 : Blo 574812 1554319 := bstep (se 1 (by rfl) ⟨1165739, by rfl⟩ : syracuseStep 1554319 = 2331479) B2331479
theorem B1555919 : Blo 574812 1555919 := bstep (se 1 (by rfl) ⟨1166939, by rfl⟩ : syracuseStep 1555919 = 2333879) B2333879
theorem B867839 : Blo 574812 867839 := bstep (se 1 (by rfl) ⟨650879, by rfl⟩ : syracuseStep 867839 = 1301759) B1301759
theorem B3948385 : Blo 574812 3948385 := bstep (se 2 (by rfl) ⟨1480644, by rfl⟩ : syracuseStep 3948385 = 2961289) B2961289
theorem B4374971 : Blo 574812 4374971 := bstep (se 1 (by rfl) ⟨3281228, by rfl⟩ : syracuseStep 4374971 = 6562457) B6562457
theorem B7620779 : Blo 574812 7620779 := bstep (se 1 (by rfl) ⟨5715584, by rfl⟩ : syracuseStep 7620779 = 11431169) B11431169
theorem B1853779 : Blo 574812 1853779 := bstep (se 1 (by rfl) ⟨1390334, by rfl⟩ : syracuseStep 1853779 = 2780669) B2780669
theorem B575975 : Blo 574812 575975 := bstep (se 1 (by rfl) ⟨431981, by rfl⟩ : syracuseStep 575975 = 863963) B863963
theorem B31509101 : Blo 574812 31509101 := bstep (se 3 (by rfl) ⟨5907956, by rfl⟩ : syracuseStep 31509101 = 11815913) B11815913
theorem B576231 : Blo 574812 576231 := bstep (se 1 (by rfl) ⟨432173, by rfl⟩ : syracuseStep 576231 = 864347) B864347
theorem B26921963 : Blo 574812 26921963 := bstep (se 1 (by rfl) ⟨20191472, by rfl⟩ : syracuseStep 26921963 = 40382945) B40382945
theorem B1297439 : Blo 574812 1297439 := bstep (se 1 (by rfl) ⟨973079, by rfl⟩ : syracuseStep 1297439 = 1946159) B1946159
theorem B1461503 : Blo 574812 1461503 := bstep (se 1 (by rfl) ⟨1096127, by rfl⟩ : syracuseStep 1461503 = 2192255) B2192255
theorem B577695 : Blo 574812 577695 := bstep (se 1 (by rfl) ⟨433271, by rfl⟩ : syracuseStep 577695 = 866543) B866543
theorem B970987 : Blo 574812 970987 := bstep (se 1 (by rfl) ⟨728240, by rfl⟩ : syracuseStep 970987 = 1456481) B1456481
theorem B577951 : Blo 574812 577951 := bstep (se 1 (by rfl) ⟨433463, by rfl⟩ : syracuseStep 577951 = 866927) B866927
theorem B1301615 : Blo 574812 1301615 := bstep (se 1 (by rfl) ⟨976211, by rfl⟩ : syracuseStep 1301615 = 1952423) B1952423
theorem B7888225 : Blo 574812 7888225 := bstep (se 2 (by rfl) ⟨2958084, by rfl⟩ : syracuseStep 7888225 = 5916169) B5916169
theorem B1335743 : Blo 574812 1335743 := bstep (se 1 (by rfl) ⟨1001807, by rfl⟩ : syracuseStep 1335743 = 2003615) B2003615
theorem B975719 : Blo 574812 975719 := bstep (se 1 (by rfl) ⟨731789, by rfl⟩ : syracuseStep 975719 = 1463579) B1463579
theorem B16607531 : Blo 574812 16607531 := bstep (se 1 (by rfl) ⟨12455648, by rfl⟩ : syracuseStep 16607531 = 24911297) B24911297
theorem B649543 : Blo 574812 649543 := bstep (se 1 (by rfl) ⟨487157, by rfl⟩ : syracuseStep 649543 = 974315) B974315
theorem B30371023 : Blo 574812 30371023 := bstep (se 1 (by rfl) ⟨22778267, by rfl⟩ : syracuseStep 30371023 = 45556535) B45556535
theorem B4158803 : Blo 574812 4158803 := bstep (se 1 (by rfl) ⟨3119102, by rfl⟩ : syracuseStep 4158803 = 6238205) B6238205
theorem B9336167 : Blo 574812 9336167 := bstep (se 1 (by rfl) ⟨7002125, by rfl⟩ : syracuseStep 9336167 = 14004251) B14004251
theorem B6256889 : Blo 574812 6256889 := bstep (se 2 (by rfl) ⟨2346333, by rfl⟩ : syracuseStep 6256889 = 4692667) B4692667
theorem B2916647 : Blo 574812 2916647 := bstep (se 1 (by rfl) ⟨2187485, by rfl⟩ : syracuseStep 2916647 = 4374971) B4374971
theorem B5080519 : Blo 574812 5080519 := bstep (se 1 (by rfl) ⟨3810389, by rfl⟩ : syracuseStep 5080519 = 7620779) B7620779
theorem B21006067 : Blo 574812 21006067 := bstep (se 1 (by rfl) ⟨15754550, by rfl⟩ : syracuseStep 21006067 = 31509101) B31509101
theorem B1444267 : Blo 574812 1444267 := bstep (se 1 (by rfl) ⟨1083200, by rfl⟩ : syracuseStep 1444267 = 2166401) B2166401
theorem B85397429 : Blo 574812 85397429 := bstep (se 5 (by rfl) ⟨4003004, by rfl⟩ : syracuseStep 85397429 = 8006009) B8006009
theorem B1447033 : Blo 574812 1447033 := bstep (se 2 (by rfl) ⟨542637, by rfl⟩ : syracuseStep 1447033 = 1085275) B1085275
theorem B890495 : Blo 574812 890495 := bstep (se 1 (by rfl) ⟨667871, by rfl⟩ : syracuseStep 890495 = 1335743) B1335743
theorem B9380285 : Blo 574812 9380285 := bstep (se 3 (by rfl) ⟨1758803, by rfl⟩ : syracuseStep 9380285 = 3517607) B3517607
theorem B4171259 : Blo 574812 4171259 := bstep (se 1 (by rfl) ⟨3128444, by rfl⟩ : syracuseStep 4171259 = 6256889) B6256889
theorem B864959 : Blo 574812 864959 := bstep (se 1 (by rfl) ⟨648719, by rfl⟩ : syracuseStep 864959 = 1297439) B1297439
theorem B866057 : Blo 574812 866057 := bstep (se 2 (by rfl) ⟨324771, by rfl⟩ : syracuseStep 866057 = 649543) B649543
theorem B2471705 : Blo 574812 2471705 := bstep (se 2 (by rfl) ⟨926889, by rfl⟩ : syracuseStep 2471705 = 1853779) B1853779
theorem B11090141 : Blo 574812 11090141 := bstep (se 3 (by rfl) ⟨2079401, by rfl⟩ : syracuseStep 11090141 = 4158803) B4158803
theorem B867743 : Blo 574812 867743 := bstep (se 1 (by rfl) ⟨650807, by rfl⟩ : syracuseStep 867743 = 1301615) B1301615
theorem B5553683 : Blo 574812 5553683 := bstep (se 1 (by rfl) ⟨4165262, by rfl⟩ : syracuseStep 5553683 = 8330525) B8330525
theorem B1294559 : Blo 574812 1294559 := bstep (se 1 (by rfl) ⟨970919, by rfl⟩ : syracuseStep 1294559 = 1941839) B1941839
theorem B1294649 : Blo 574812 1294649 := bstep (se 2 (by rfl) ⟨485493, by rfl⟩ : syracuseStep 1294649 = 970987) B970987
theorem B1295387 : Blo 574812 1295387 := bstep (se 1 (by rfl) ⟨971540, by rfl⟩ : syracuseStep 1295387 = 1943081) B1943081
theorem B575935 : Blo 574812 575935 := bstep (se 1 (by rfl) ⟨431951, by rfl⟩ : syracuseStep 575935 = 863903) B863903
theorem B1296863 : Blo 574812 1296863 := bstep (se 1 (by rfl) ⟨972647, by rfl⟩ : syracuseStep 1296863 = 1945295) B1945295
theorem B1297223 : Blo 574812 1297223 := bstep (se 1 (by rfl) ⟨972917, by rfl⟩ : syracuseStep 1297223 = 1945835) B1945835
theorem B576767 : Blo 574812 576767 := bstep (se 1 (by rfl) ⟨432575, by rfl⟩ : syracuseStep 576767 = 865151) B865151
theorem B1298087 : Blo 574812 1298087 := bstep (se 1 (by rfl) ⟨973565, by rfl⟩ : syracuseStep 1298087 = 1947131) B1947131
theorem B1037279 : Blo 574812 1037279 := bstep (se 1 (by rfl) ⟨777959, by rfl⟩ : syracuseStep 1037279 = 1555919) B1555919
theorem B578559 : Blo 574812 578559 := bstep (se 1 (by rfl) ⟨433919, by rfl⟩ : syracuseStep 578559 = 867839) B867839
theorem B5264513 : Blo 574812 5264513 := bstep (se 2 (by rfl) ⟨1974192, by rfl⟩ : syracuseStep 5264513 = 3948385) B3948385
theorem B5003135 : Blo 574812 5003135 := bstep (se 1 (by rfl) ⟨3752351, by rfl⟩ : syracuseStep 5003135 = 7504703) B7504703
theorem B1234921 : Blo 574812 1234921 := bstep (se 2 (by rfl) ⟨463095, by rfl⟩ : syracuseStep 1234921 = 926191) B926191
theorem B17947975 : Blo 574812 17947975 := bstep (se 1 (by rfl) ⟨13460981, by rfl⟩ : syracuseStep 17947975 = 26921963) B26921963
theorem B2163891611 : Blo 574812 2163891611 := bstep (se 1 (by rfl) ⟨1622918708, by rfl⟩ : syracuseStep 2163891611 = 3245837417) B3245837417
theorem B974335 : Blo 574812 974335 := bstep (se 1 (by rfl) ⟨730751, by rfl⟩ : syracuseStep 974335 = 1461503) B1461503
theorem B9494441 : Blo 574812 9494441 := bstep (se 2 (by rfl) ⟨3560415, by rfl⟩ : syracuseStep 9494441 = 7120831) B7120831
theorem B40494697 : Blo 574812 40494697 := bstep (se 2 (by rfl) ⟨15185511, by rfl⟩ : syracuseStep 40494697 = 30371023) B30371023
theorem B650479 : Blo 574812 650479 := bstep (se 1 (by rfl) ⟨487859, by rfl⟩ : syracuseStep 650479 = 975719) B975719
theorem B2190827 : Blo 574812 2190827 := bstep (se 1 (by rfl) ⟨1643120, by rfl⟩ : syracuseStep 2190827 = 3286241) B3286241
theorem B11071687 : Blo 574812 11071687 := bstep (se 1 (by rfl) ⟨8303765, by rfl⟩ : syracuseStep 11071687 = 16607531) B16607531
theorem B37318967 : Blo 574812 37318967 := bstep (se 1 (by rfl) ⟨27989225, by rfl⟩ : syracuseStep 37318967 = 55978451) B55978451
theorem B6224111 : Blo 574812 6224111 := bstep (se 1 (by rfl) ⟨4668083, by rfl⟩ : syracuseStep 6224111 = 9336167) B9336167
theorem B10517633 : Blo 574812 10517633 := bstep (se 2 (by rfl) ⟨3944112, by rfl⟩ : syracuseStep 10517633 = 7888225) B7888225
theorem B8289701 : Blo 574812 8289701 := bstep (se 4 (by rfl) ⟨777159, by rfl⟩ : syracuseStep 8289701 = 1554319) B1554319
theorem B3509675 : Blo 574812 3509675 := bstep (se 1 (by rfl) ⟨2632256, by rfl⟩ : syracuseStep 3509675 = 5264513) B5264513
theorem B593663 : Blo 574812 593663 := bstep (se 1 (by rfl) ⟨445247, by rfl⟩ : syracuseStep 593663 = 890495) B890495
theorem B6329627 : Blo 574812 6329627 := bstep (se 1 (by rfl) ⟨4747220, by rfl⟩ : syracuseStep 6329627 = 9494441) B9494441
theorem B1646561 : Blo 574812 1646561 := bstep (se 2 (by rfl) ⟨617460, by rfl⟩ : syracuseStep 1646561 = 1234921) B1234921
theorem B24879311 : Blo 574812 24879311 := bstep (se 1 (by rfl) ⟨18659483, by rfl⟩ : syracuseStep 24879311 = 37318967) B37318967
theorem B1647803 : Blo 574812 1647803 := bstep (se 1 (by rfl) ⟨1235852, by rfl⟩ : syracuseStep 1647803 = 2471705) B2471705
theorem B23930633 : Blo 574812 23930633 := bstep (se 2 (by rfl) ⟨8973987, by rfl⟩ : syracuseStep 23930633 = 17947975) B17947975
theorem B863039 : Blo 574812 863039 := bstep (se 1 (by rfl) ⟨647279, by rfl⟩ : syracuseStep 863039 = 1294559) B1294559
theorem B1944431 : Blo 574812 1944431 := bstep (se 1 (by rfl) ⟨1458323, by rfl⟩ : syracuseStep 1944431 = 2916647) B2916647
theorem B863099 : Blo 574812 863099 := bstep (se 1 (by rfl) ⟨647324, by rfl⟩ : syracuseStep 863099 = 1294649) B1294649
theorem B863591 : Blo 574812 863591 := bstep (se 1 (by rfl) ⟨647693, by rfl⟩ : syracuseStep 863591 = 1295387) B1295387
theorem B864575 : Blo 574812 864575 := bstep (se 1 (by rfl) ⟨648431, by rfl⟩ : syracuseStep 864575 = 1296863) B1296863
theorem B864815 : Blo 574812 864815 := bstep (se 1 (by rfl) ⟨648611, by rfl⟩ : syracuseStep 864815 = 1297223) B1297223
theorem B865391 : Blo 574812 865391 := bstep (se 1 (by rfl) ⟨649043, by rfl⟩ : syracuseStep 865391 = 1298087) B1298087
theorem B2766077 : Blo 574812 2766077 := bstep (se 3 (by rfl) ⟨518639, by rfl⟩ : syracuseStep 2766077 = 1037279) B1037279
theorem B56931619 : Blo 574812 56931619 := bstep (se 1 (by rfl) ⟨42698714, by rfl⟩ : syracuseStep 56931619 = 85397429) B85397429
theorem B867305 : Blo 574812 867305 := bstep (se 2 (by rfl) ⟨325239, by rfl⟩ : syracuseStep 867305 = 650479) B650479
theorem B1442594407 : Blo 574812 1442594407 := bstep (se 1 (by rfl) ⟨1081945805, by rfl⟩ : syracuseStep 1442594407 = 2163891611) B2163891611
theorem B14762249 : Blo 574812 14762249 := bstep (se 2 (by rfl) ⟨5535843, by rfl⟩ : syracuseStep 14762249 = 11071687) B11071687
theorem B1460551 : Blo 574812 1460551 := bstep (se 1 (by rfl) ⟨1095413, by rfl⟩ : syracuseStep 1460551 = 2190827) B2190827
theorem B576639 : Blo 574812 576639 := bstep (se 1 (by rfl) ⟨432479, by rfl⟩ : syracuseStep 576639 = 864959) B864959
theorem B577371 : Blo 574812 577371 := bstep (se 1 (by rfl) ⟨433028, by rfl⟩ : syracuseStep 577371 = 866057) B866057
theorem B7393427 : Blo 574812 7393427 := bstep (se 1 (by rfl) ⟨5545070, by rfl⟩ : syracuseStep 7393427 = 11090141) B11090141
theorem B4149407 : Blo 574812 4149407 := bstep (se 1 (by rfl) ⟨3112055, by rfl⟩ : syracuseStep 4149407 = 6224111) B6224111
theorem B1299113 : Blo 574812 1299113 := bstep (se 2 (by rfl) ⟨487167, by rfl⟩ : syracuseStep 1299113 = 974335) B974335
theorem B578495 : Blo 574812 578495 := bstep (se 1 (by rfl) ⟨433871, by rfl⟩ : syracuseStep 578495 = 867743) B867743
theorem B5526467 : Blo 574812 5526467 := bstep (se 1 (by rfl) ⟨4144850, by rfl⟩ : syracuseStep 5526467 = 8289701) B8289701
theorem B6774025 : Blo 574812 6774025 := bstep (se 2 (by rfl) ⟨2540259, by rfl⟩ : syracuseStep 6774025 = 5080519) B5080519
theorem B28008089 : Blo 574812 28008089 := bstep (se 2 (by rfl) ⟨10503033, by rfl⟩ : syracuseStep 28008089 = 21006067) B21006067
theorem B1925689 : Blo 574812 1925689 := bstep (se 2 (by rfl) ⟨722133, by rfl⟩ : syracuseStep 1925689 = 1444267) B1444267
theorem B3335423 : Blo 574812 3335423 := bstep (se 1 (by rfl) ⟨2501567, by rfl⟩ : syracuseStep 3335423 = 5003135) B5003135
theorem B6253523 : Blo 574812 6253523 := bstep (se 1 (by rfl) ⟨4690142, by rfl⟩ : syracuseStep 6253523 = 9380285) B9380285
theorem B2780839 : Blo 574812 2780839 := bstep (se 1 (by rfl) ⟨2085629, by rfl⟩ : syracuseStep 2780839 = 4171259) B4171259
theorem B1929377 : Blo 574812 1929377 := bstep (se 2 (by rfl) ⟨723516, by rfl⟩ : syracuseStep 1929377 = 1447033) B1447033
theorem B215971717 : Blo 574812 215971717 := bstep (se 4 (by rfl) ⟨20247348, by rfl⟩ : syracuseStep 215971717 = 40494697) B40494697
theorem B7011755 : Blo 574812 7011755 := bstep (se 1 (by rfl) ⟨5258816, by rfl⟩ : syracuseStep 7011755 = 10517633) B10517633
theorem B3702455 : Blo 574812 3702455 := bstep (se 1 (by rfl) ⟨2776841, by rfl⟩ : syracuseStep 3702455 = 5553683) B5553683
theorem B5145005 : Blo 574812 5145005 := bstep (se 3 (by rfl) ⟨964688, by rfl⟩ : syracuseStep 5145005 = 1929377) B1929377
theorem B3707785 : Blo 574812 3707785 := bstep (se 2 (by rfl) ⟨1390419, by rfl⟩ : syracuseStep 3707785 = 2780839) B2780839
theorem B16586207 : Blo 574812 16586207 := bstep (se 1 (by rfl) ⟨12439655, by rfl⟩ : syracuseStep 16586207 = 24879311) B24879311
theorem B4169015 : Blo 574812 4169015 := bstep (se 1 (by rfl) ⟨3126761, by rfl⟩ : syracuseStep 4169015 = 6253523) B6253523
theorem B1844051 : Blo 574812 1844051 := bstep (se 1 (by rfl) ⟨1383038, by rfl⟩ : syracuseStep 1844051 = 2766077) B2766077
theorem B1583101 : Blo 574812 1583101 := bstep (se 3 (by rfl) ⟨296831, by rfl⟩ : syracuseStep 1583101 = 593663) B593663
theorem B1923459209 : Blo 574812 1923459209 := bstep (se 2 (by rfl) ⟨721297203, by rfl⟩ : syracuseStep 1923459209 = 1442594407) B1442594407
theorem B2468303 : Blo 574812 2468303 := bstep (se 1 (by rfl) ⟨1851227, by rfl⟩ : syracuseStep 2468303 = 3702455) B3702455
theorem B9841499 : Blo 574812 9841499 := bstep (se 1 (by rfl) ⟨7381124, by rfl⟩ : syracuseStep 9841499 = 14762249) B14762249
theorem B2567585 : Blo 574812 2567585 := bstep (se 2 (by rfl) ⟨962844, by rfl⟩ : syracuseStep 2567585 = 1925689) B1925689
theorem B2339783 : Blo 574812 2339783 := bstep (se 1 (by rfl) ⟨1754837, by rfl⟩ : syracuseStep 2339783 = 3509675) B3509675
theorem B4928951 : Blo 574812 4928951 := bstep (se 1 (by rfl) ⟨3696713, by rfl⟩ : syracuseStep 4928951 = 7393427) B7393427
theorem B2766271 : Blo 574812 2766271 := bstep (se 1 (by rfl) ⟨2074703, by rfl⟩ : syracuseStep 2766271 = 4149407) B4149407
theorem B1947401 : Blo 574812 1947401 := bstep (se 2 (by rfl) ⟨730275, by rfl⟩ : syracuseStep 1947401 = 1460551) B1460551
theorem B866075 : Blo 574812 866075 := bstep (se 1 (by rfl) ⟨649556, by rfl⟩ : syracuseStep 866075 = 1299113) B1299113
theorem B3684311 : Blo 574812 3684311 := bstep (se 1 (by rfl) ⟨2763233, by rfl⟩ : syracuseStep 3684311 = 5526467) B5526467
theorem B8894461 : Blo 574812 8894461 := bstep (se 3 (by rfl) ⟨1667711, by rfl⟩ : syracuseStep 8894461 = 3335423) B3335423
theorem B1097707 : Blo 574812 1097707 := bstep (se 1 (by rfl) ⟨823280, by rfl⟩ : syracuseStep 1097707 = 1646561) B1646561
theorem B1098535 : Blo 574812 1098535 := bstep (se 1 (by rfl) ⟨823901, by rfl⟩ : syracuseStep 1098535 = 1647803) B1647803
theorem B75908825 : Blo 574812 75908825 := bstep (se 2 (by rfl) ⟨28465809, by rfl⟩ : syracuseStep 75908825 = 56931619) B56931619
theorem B575359 : Blo 574812 575359 := bstep (se 1 (by rfl) ⟨431519, by rfl⟩ : syracuseStep 575359 = 863039) B863039
theorem B1296287 : Blo 574812 1296287 := bstep (se 1 (by rfl) ⟨972215, by rfl⟩ : syracuseStep 1296287 = 1944431) B1944431
theorem B575399 : Blo 574812 575399 := bstep (se 1 (by rfl) ⟨431549, by rfl⟩ : syracuseStep 575399 = 863099) B863099
theorem B575727 : Blo 574812 575727 := bstep (se 1 (by rfl) ⟨431795, by rfl⟩ : syracuseStep 575727 = 863591) B863591
theorem B576383 : Blo 574812 576383 := bstep (se 1 (by rfl) ⟨432287, by rfl⟩ : syracuseStep 576383 = 864575) B864575
theorem B576543 : Blo 574812 576543 := bstep (se 1 (by rfl) ⟨432407, by rfl⟩ : syracuseStep 576543 = 864815) B864815
theorem B576927 : Blo 574812 576927 := bstep (se 1 (by rfl) ⟨432695, by rfl⟩ : syracuseStep 576927 = 865391) B865391
theorem B9032033 : Blo 574812 9032033 := bstep (se 2 (by rfl) ⟨3387012, by rfl⟩ : syracuseStep 9032033 = 6774025) B6774025
theorem B578203 : Blo 574812 578203 := bstep (se 1 (by rfl) ⟨433652, by rfl⟩ : syracuseStep 578203 = 867305) B867305
theorem B4674503 : Blo 574812 4674503 := bstep (se 1 (by rfl) ⟨3505877, by rfl⟩ : syracuseStep 4674503 = 7011755) B7011755
theorem B4219751 : Blo 574812 4219751 := bstep (se 1 (by rfl) ⟨3164813, by rfl⟩ : syracuseStep 4219751 = 6329627) B6329627
theorem B18672059 : Blo 574812 18672059 := bstep (se 1 (by rfl) ⟨14004044, by rfl⟩ : syracuseStep 18672059 = 28008089) B28008089
theorem B15953755 : Blo 574812 15953755 := bstep (se 1 (by rfl) ⟨11965316, by rfl⟩ : syracuseStep 15953755 = 23930633) B23930633
theorem B287962289 : Blo 574812 287962289 := bstep (se 2 (by rfl) ⟨107985858, by rfl⟩ : syracuseStep 287962289 = 215971717) B215971717
theorem B24085421 : Blo 574812 24085421 := bstep (se 3 (by rfl) ⟨4516016, by rfl⟩ : syracuseStep 24085421 = 9032033) B9032033
theorem B4917469 : Blo 574812 4917469 := bstep (se 3 (by rfl) ⟨922025, by rfl⟩ : syracuseStep 4917469 = 1844051) B1844051
theorem B3116335 : Blo 574812 3116335 := bstep (se 1 (by rfl) ⟨2337251, by rfl⟩ : syracuseStep 3116335 = 4674503) B4674503
theorem B21271673 : Blo 574812 21271673 := bstep (se 2 (by rfl) ⟨7976877, by rfl⟩ : syracuseStep 21271673 = 15953755) B15953755
theorem B1645535 : Blo 574812 1645535 := bstep (se 1 (by rfl) ⟨1234151, by rfl⟩ : syracuseStep 1645535 = 2468303) B2468303
theorem B6560999 : Blo 574812 6560999 := bstep (se 1 (by rfl) ⟨4920749, by rfl⟩ : syracuseStep 6560999 = 9841499) B9841499
theorem B3285967 : Blo 574812 3285967 := bstep (se 1 (by rfl) ⟨2464475, by rfl⟩ : syracuseStep 3285967 = 4928951) B4928951
theorem B50605883 : Blo 574812 50605883 := bstep (se 1 (by rfl) ⟨37954412, by rfl⟩ : syracuseStep 50605883 = 75908825) B75908825
theorem B864191 : Blo 574812 864191 := bstep (se 1 (by rfl) ⟨648143, by rfl⟩ : syracuseStep 864191 = 1296287) B1296287
theorem B2110801 : Blo 574812 2110801 := bstep (se 2 (by rfl) ⟨791550, by rfl⟩ : syracuseStep 2110801 = 1583101) B1583101
theorem B11057471 : Blo 574812 11057471 := bstep (se 1 (by rfl) ⟨8293103, by rfl⟩ : syracuseStep 11057471 = 16586207) B16586207
theorem B180042709 : Blo 574812 180042709 := bstep (se 7 (by rfl) ⟨2109875, by rfl⟩ : syracuseStep 180042709 = 4219751) B4219751
theorem B3688361 : Blo 574812 3688361 := bstep (se 2 (by rfl) ⟨1383135, by rfl⟩ : syracuseStep 3688361 = 2766271) B2766271
theorem B1559855 : Blo 574812 1559855 := bstep (se 1 (by rfl) ⟨1169891, by rfl⟩ : syracuseStep 1559855 = 2339783) B2339783
theorem B191974859 : Blo 574812 191974859 := bstep (se 1 (by rfl) ⟨143981144, by rfl⟩ : syracuseStep 191974859 = 287962289) B287962289
theorem B1298267 : Blo 574812 1298267 := bstep (se 1 (by rfl) ⟨973700, by rfl⟩ : syracuseStep 1298267 = 1947401) B1947401
theorem B577383 : Blo 574812 577383 := bstep (se 1 (by rfl) ⟨433037, by rfl⟩ : syracuseStep 577383 = 866075) B866075
theorem B1463609 : Blo 574812 1463609 := bstep (se 2 (by rfl) ⟨548853, by rfl⟩ : syracuseStep 1463609 = 1097707) B1097707
theorem B1464713 : Blo 574812 1464713 := bstep (se 2 (by rfl) ⟨549267, by rfl⟩ : syracuseStep 1464713 = 1098535) B1098535
theorem B13720013 : Blo 574812 13720013 := bstep (se 3 (by rfl) ⟨2572502, by rfl⟩ : syracuseStep 13720013 = 5145005) B5145005
theorem B2779343 : Blo 574812 2779343 := bstep (se 1 (by rfl) ⟨2084507, by rfl⟩ : syracuseStep 2779343 = 4169015) B4169015
theorem B4943713 : Blo 574812 4943713 := bstep (se 2 (by rfl) ⟨1853892, by rfl⟩ : syracuseStep 4943713 = 3707785) B3707785
theorem B1282306139 : Blo 574812 1282306139 := bstep (se 1 (by rfl) ⟨961729604, by rfl⟩ : syracuseStep 1282306139 = 1923459209) B1923459209
theorem B12448039 : Blo 574812 12448039 := bstep (se 1 (by rfl) ⟨9336029, by rfl⟩ : syracuseStep 12448039 = 18672059) B18672059
theorem B11859281 : Blo 574812 11859281 := bstep (se 2 (by rfl) ⟨4447230, by rfl⟩ : syracuseStep 11859281 = 8894461) B8894461
theorem B6846893 : Blo 574812 6846893 := bstep (se 3 (by rfl) ⟨1283792, by rfl⟩ : syracuseStep 6846893 = 2567585) B2567585
theorem B2456207 : Blo 574812 2456207 := bstep (se 1 (by rfl) ⟨1842155, by rfl⟩ : syracuseStep 2456207 = 3684311) B3684311
theorem B16056947 : Blo 574812 16056947 := bstep (se 1 (by rfl) ⟨12042710, by rfl⟩ : syracuseStep 16056947 = 24085421) B24085421
theorem B2458907 : Blo 574812 2458907 := bstep (se 1 (by rfl) ⟨1844180, by rfl⟩ : syracuseStep 2458907 = 3688361) B3688361
theorem B6556625 : Blo 574812 6556625 := bstep (se 2 (by rfl) ⟨2458734, by rfl⟩ : syracuseStep 6556625 = 4917469) B4917469
theorem B56724461 : Blo 574812 56724461 := bstep (se 3 (by rfl) ⟨10635836, by rfl⟩ : syracuseStep 56724461 = 21271673) B21271673
theorem B9146675 : Blo 574812 9146675 := bstep (se 1 (by rfl) ⟨6860006, by rfl⟩ : syracuseStep 9146675 = 13720013) B13720013
theorem B6591617 : Blo 574812 6591617 := bstep (se 2 (by rfl) ⟨2471856, by rfl⟩ : syracuseStep 6591617 = 4943713) B4943713
theorem B7906187 : Blo 574812 7906187 := bstep (se 1 (by rfl) ⟨5929640, by rfl⟩ : syracuseStep 7906187 = 11859281) B11859281
theorem B4564595 : Blo 574812 4564595 := bstep (se 1 (by rfl) ⟨3423446, by rfl⟩ : syracuseStep 4564595 = 6846893) B6846893
theorem B865511 : Blo 574812 865511 := bstep (se 1 (by rfl) ⟨649133, by rfl⟩ : syracuseStep 865511 = 1298267) B1298267
theorem B4373999 : Blo 574812 4373999 := bstep (se 1 (by rfl) ⟨3280499, by rfl⟩ : syracuseStep 4373999 = 6560999) B6560999
theorem B16597385 : Blo 574812 16597385 := bstep (se 2 (by rfl) ⟨6224019, by rfl⟩ : syracuseStep 16597385 = 12448039) B12448039
theorem B1852895 : Blo 574812 1852895 := bstep (se 1 (by rfl) ⟨1389671, by rfl⟩ : syracuseStep 1852895 = 2779343) B2779343
theorem B33737255 : Blo 574812 33737255 := bstep (se 1 (by rfl) ⟨25302941, by rfl⟩ : syracuseStep 33737255 = 50605883) B50605883
theorem B576127 : Blo 574812 576127 := bstep (se 1 (by rfl) ⟨432095, by rfl⟩ : syracuseStep 576127 = 864191) B864191
theorem B854870759 : Blo 574812 854870759 := bstep (se 1 (by rfl) ⟨641153069, by rfl⟩ : syracuseStep 854870759 = 1282306139) B1282306139
theorem B4381289 : Blo 574812 4381289 := bstep (se 2 (by rfl) ⟨1642983, by rfl⟩ : syracuseStep 4381289 = 3285967) B3285967
theorem B127983239 : Blo 574812 127983239 := bstep (se 1 (by rfl) ⟨95987429, by rfl⟩ : syracuseStep 127983239 = 191974859) B191974859
theorem B975739 : Blo 574812 975739 := bstep (se 1 (by rfl) ⟨731804, by rfl⟩ : syracuseStep 975739 = 1463609) B1463609
theorem B976475 : Blo 574812 976475 := bstep (se 1 (by rfl) ⟨732356, by rfl⟩ : syracuseStep 976475 = 1464713) B1464713
theorem B4155113 : Blo 574812 4155113 := bstep (se 2 (by rfl) ⟨1558167, by rfl⟩ : syracuseStep 4155113 = 3116335) B3116335
theorem B2814401 : Blo 574812 2814401 := bstep (se 2 (by rfl) ⟨1055400, by rfl⟩ : syracuseStep 2814401 = 2110801) B2110801
theorem B4388093 : Blo 574812 4388093 := bstep (se 3 (by rfl) ⟨822767, by rfl⟩ : syracuseStep 4388093 = 1645535) B1645535
theorem B4159613 : Blo 574812 4159613 := bstep (se 3 (by rfl) ⟨779927, by rfl⟩ : syracuseStep 4159613 = 1559855) B1559855
theorem B240056945 : Blo 574812 240056945 := bstep (se 2 (by rfl) ⟨90021354, by rfl⟩ : syracuseStep 240056945 = 180042709) B180042709
theorem B7371647 : Blo 574812 7371647 := bstep (se 1 (by rfl) ⟨5528735, by rfl⟩ : syracuseStep 7371647 = 11057471) B11057471
theorem B1637471 : Blo 574812 1637471 := bstep (se 1 (by rfl) ⟨1228103, by rfl⟩ : syracuseStep 1637471 = 2456207) B2456207
theorem B1639271 : Blo 574812 1639271 := bstep (se 1 (by rfl) ⟨1229453, by rfl⟩ : syracuseStep 1639271 = 2458907) B2458907
theorem B37816307 : Blo 574812 37816307 := bstep (se 1 (by rfl) ⟨28362230, by rfl⟩ : syracuseStep 37816307 = 56724461) B56724461
theorem B6097783 : Blo 574812 6097783 := bstep (se 1 (by rfl) ⟨4573337, by rfl⟩ : syracuseStep 6097783 = 9146675) B9146675
theorem B4394411 : Blo 574812 4394411 := bstep (se 1 (by rfl) ⟨3295808, by rfl⟩ : syracuseStep 4394411 = 6591617) B6591617
theorem B2920859 : Blo 574812 2920859 := bstep (se 1 (by rfl) ⟨2190644, by rfl⟩ : syracuseStep 2920859 = 4381289) B4381289
theorem B1876267 : Blo 574812 1876267 := bstep (se 1 (by rfl) ⟨1407200, by rfl⟩ : syracuseStep 1876267 = 2814401) B2814401
theorem B2925395 : Blo 574812 2925395 := bstep (se 1 (by rfl) ⟨2194046, by rfl⟩ : syracuseStep 2925395 = 4388093) B4388093
theorem B1091647 : Blo 574812 1091647 := bstep (se 1 (by rfl) ⟨818735, by rfl⟩ : syracuseStep 1091647 = 1637471) B1637471
theorem B22491503 : Blo 574812 22491503 := bstep (se 1 (by rfl) ⟨16868627, by rfl⟩ : syracuseStep 22491503 = 33737255) B33737255
theorem B569913839 : Blo 574812 569913839 := bstep (se 1 (by rfl) ⟨427435379, by rfl⟩ : syracuseStep 569913839 = 854870759) B854870759
theorem B4371083 : Blo 574812 4371083 := bstep (se 1 (by rfl) ⟨3278312, by rfl⟩ : syracuseStep 4371083 = 6556625) B6556625
theorem B2770075 : Blo 574812 2770075 := bstep (se 1 (by rfl) ⟨2077556, by rfl⟩ : syracuseStep 2770075 = 4155113) B4155113
theorem B577007 : Blo 574812 577007 := bstep (se 1 (by rfl) ⟨432755, by rfl⟩ : syracuseStep 577007 = 865511) B865511
theorem B2773075 : Blo 574812 2773075 := bstep (se 1 (by rfl) ⟨2079806, by rfl⟩ : syracuseStep 2773075 = 4159613) B4159613
theorem B11064923 : Blo 574812 11064923 := bstep (se 1 (by rfl) ⟨8298692, by rfl⟩ : syracuseStep 11064923 = 16597385) B16597385
theorem B10704631 : Blo 574812 10704631 := bstep (se 1 (by rfl) ⟨8028473, by rfl⟩ : syracuseStep 10704631 = 16056947) B16056947
theorem B1235263 : Blo 574812 1235263 := bstep (se 1 (by rfl) ⟨926447, by rfl⟩ : syracuseStep 1235263 = 1852895) B1852895
theorem B1300985 : Blo 574812 1300985 := bstep (se 2 (by rfl) ⟨487869, by rfl⟩ : syracuseStep 1300985 = 975739) B975739
theorem B85322159 : Blo 574812 85322159 := bstep (se 1 (by rfl) ⟨63991619, by rfl⟩ : syracuseStep 85322159 = 127983239) B127983239
theorem B5270791 : Blo 574812 5270791 := bstep (se 1 (by rfl) ⟨3953093, by rfl⟩ : syracuseStep 5270791 = 7906187) B7906187
theorem B650983 : Blo 574812 650983 := bstep (se 1 (by rfl) ⟨488237, by rfl⟩ : syracuseStep 650983 = 976475) B976475
theorem B3043063 : Blo 574812 3043063 := bstep (se 1 (by rfl) ⟨2282297, by rfl⟩ : syracuseStep 3043063 = 4564595) B4564595
theorem B160037963 : Blo 574812 160037963 := bstep (se 1 (by rfl) ⟨120028472, by rfl⟩ : syracuseStep 160037963 = 240056945) B240056945
theorem B4914431 : Blo 574812 4914431 := bstep (se 1 (by rfl) ⟨3685823, by rfl⟩ : syracuseStep 4914431 = 7371647) B7371647
theorem B2915999 : Blo 574812 2915999 := bstep (se 1 (by rfl) ⟨2186999, by rfl⟩ : syracuseStep 2915999 = 4373999) B4373999
theorem B7376615 : Blo 574812 7376615 := bstep (se 1 (by rfl) ⟨5532461, by rfl⟩ : syracuseStep 7376615 = 11064923) B11064923
theorem B8130377 : Blo 574812 8130377 := bstep (se 2 (by rfl) ⟨3048891, by rfl⟩ : syracuseStep 8130377 = 6097783) B6097783
theorem B1647017 : Blo 574812 1647017 := bstep (se 2 (by rfl) ⟨617631, by rfl⟩ : syracuseStep 1647017 = 1235263) B1235263
theorem B1943999 : Blo 574812 1943999 := bstep (se 1 (by rfl) ⟨1457999, by rfl⟩ : syracuseStep 1943999 = 2915999) B2915999
theorem B2501689 : Blo 574812 2501689 := bstep (se 2 (by rfl) ⟨938133, by rfl⟩ : syracuseStep 2501689 = 1876267) B1876267
theorem B1092847 : Blo 574812 1092847 := bstep (se 1 (by rfl) ⟨819635, by rfl⟩ : syracuseStep 1092847 = 1639271) B1639271
theorem B25210871 : Blo 574812 25210871 := bstep (se 1 (by rfl) ⟨18908153, by rfl⟩ : syracuseStep 25210871 = 37816307) B37816307
theorem B2929607 : Blo 574812 2929607 := bstep (se 1 (by rfl) ⟨2197205, by rfl⟩ : syracuseStep 2929607 = 4394411) B4394411
theorem B1455529 : Blo 574812 1455529 := bstep (se 2 (by rfl) ⟨545823, by rfl⟩ : syracuseStep 1455529 = 1091647) B1091647
theorem B1947239 : Blo 574812 1947239 := bstep (se 1 (by rfl) ⟨1460429, by rfl⟩ : syracuseStep 1947239 = 2920859) B2920859
theorem B867323 : Blo 574812 867323 := bstep (se 1 (by rfl) ⟨650492, by rfl⟩ : syracuseStep 867323 = 1300985) B1300985
theorem B7027721 : Blo 574812 7027721 := bstep (se 2 (by rfl) ⟨2635395, by rfl⟩ : syracuseStep 7027721 = 5270791) B5270791
theorem B867977 : Blo 574812 867977 := bstep (se 2 (by rfl) ⟨325491, by rfl⟩ : syracuseStep 867977 = 650983) B650983
theorem B1950263 : Blo 574812 1950263 := bstep (se 1 (by rfl) ⟨1462697, by rfl⟩ : syracuseStep 1950263 = 2925395) B2925395
theorem B14272841 : Blo 574812 14272841 := bstep (se 2 (by rfl) ⟨5352315, by rfl⟩ : syracuseStep 14272841 = 10704631) B10704631
theorem B14994335 : Blo 574812 14994335 := bstep (se 1 (by rfl) ⟨11245751, by rfl⟩ : syracuseStep 14994335 = 22491503) B22491503
theorem B3693433 : Blo 574812 3693433 := bstep (se 2 (by rfl) ⟨1385037, by rfl⟩ : syracuseStep 3693433 = 2770075) B2770075
theorem B4057417 : Blo 574812 4057417 := bstep (se 2 (by rfl) ⟨1521531, by rfl⟩ : syracuseStep 4057417 = 3043063) B3043063
theorem B3697433 : Blo 574812 3697433 := bstep (se 2 (by rfl) ⟨1386537, by rfl⟩ : syracuseStep 3697433 = 2773075) B2773075
theorem B56881439 : Blo 574812 56881439 := bstep (se 1 (by rfl) ⟨42661079, by rfl⟩ : syracuseStep 56881439 = 85322159) B85322159
theorem B379942559 : Blo 574812 379942559 := bstep (se 1 (by rfl) ⟨284956919, by rfl⟩ : syracuseStep 379942559 = 569913839) B569913839
theorem B2914055 : Blo 574812 2914055 := bstep (se 1 (by rfl) ⟨2185541, by rfl⟩ : syracuseStep 2914055 = 4371083) B4371083
theorem B106691975 : Blo 574812 106691975 := bstep (se 1 (by rfl) ⟨80018981, by rfl⟩ : syracuseStep 106691975 = 160037963) B160037963
theorem B3276287 : Blo 574812 3276287 := bstep (se 1 (by rfl) ⟨2457215, by rfl⟩ : syracuseStep 3276287 = 4914431) B4914431
theorem B9996223 : Blo 574812 9996223 := bstep (se 1 (by rfl) ⟨7497167, by rfl⟩ : syracuseStep 9996223 = 14994335) B14994335
theorem B4917743 : Blo 574812 4917743 := bstep (se 1 (by rfl) ⟨3688307, by rfl⟩ : syracuseStep 4917743 = 7376615) B7376615
theorem B2464955 : Blo 574812 2464955 := bstep (se 1 (by rfl) ⟨1848716, by rfl⟩ : syracuseStep 2464955 = 3697433) B3697433
theorem B1940705 : Blo 574812 1940705 := bstep (se 2 (by rfl) ⟨727764, by rfl⟩ : syracuseStep 1940705 = 1455529) B1455529
theorem B37920959 : Blo 574812 37920959 := bstep (se 1 (by rfl) ⟨28440719, by rfl⟩ : syracuseStep 37920959 = 56881439) B56881439
theorem B4924577 : Blo 574812 4924577 := bstep (se 2 (by rfl) ⟨1846716, by rfl⟩ : syracuseStep 4924577 = 3693433) B3693433
theorem B1942703 : Blo 574812 1942703 := bstep (se 1 (by rfl) ⟨1457027, by rfl⟩ : syracuseStep 1942703 = 2914055) B2914055
theorem B9515227 : Blo 574812 9515227 := bstep (se 1 (by rfl) ⟨7136420, by rfl⟩ : syracuseStep 9515227 = 14272841) B14272841
theorem B21639557 : Blo 574812 21639557 := bstep (se 4 (by rfl) ⟨2028708, by rfl⟩ : syracuseStep 21639557 = 4057417) B4057417
theorem B5420251 : Blo 574812 5420251 := bstep (se 1 (by rfl) ⟨4065188, by rfl⟩ : syracuseStep 5420251 = 8130377) B8130377
theorem B1457129 : Blo 574812 1457129 := bstep (se 2 (by rfl) ⟨546423, by rfl⟩ : syracuseStep 1457129 = 1092847) B1092847
theorem B1098011 : Blo 574812 1098011 := bstep (se 1 (by rfl) ⟨823508, by rfl⟩ : syracuseStep 1098011 = 1647017) B1647017
theorem B1295999 : Blo 574812 1295999 := bstep (se 1 (by rfl) ⟨971999, by rfl⟩ : syracuseStep 1295999 = 1943999) B1943999
theorem B1953071 : Blo 574812 1953071 := bstep (se 1 (by rfl) ⟨1464803, by rfl⟩ : syracuseStep 1953071 = 2929607) B2929607
theorem B1298159 : Blo 574812 1298159 := bstep (se 1 (by rfl) ⟨973619, by rfl⟩ : syracuseStep 1298159 = 1947239) B1947239
theorem B578215 : Blo 574812 578215 := bstep (se 1 (by rfl) ⟨433661, by rfl⟩ : syracuseStep 578215 = 867323) B867323
theorem B71127983 : Blo 574812 71127983 := bstep (se 1 (by rfl) ⟨53345987, by rfl⟩ : syracuseStep 71127983 = 106691975) B106691975
theorem B2184191 : Blo 574812 2184191 := bstep (se 1 (by rfl) ⟨1638143, by rfl⟩ : syracuseStep 2184191 = 3276287) B3276287
theorem B578651 : Blo 574812 578651 := bstep (se 1 (by rfl) ⟨433988, by rfl⟩ : syracuseStep 578651 = 867977) B867977
theorem B1300175 : Blo 574812 1300175 := bstep (se 1 (by rfl) ⟨975131, by rfl⟩ : syracuseStep 1300175 = 1950263) B1950263
theorem B3335585 : Blo 574812 3335585 := bstep (se 2 (by rfl) ⟨1250844, by rfl⟩ : syracuseStep 3335585 = 2501689) B2501689
theorem B16807247 : Blo 574812 16807247 := bstep (se 1 (by rfl) ⟨12605435, by rfl⟩ : syracuseStep 16807247 = 25210871) B25210871
theorem B253295039 : Blo 574812 253295039 := bstep (se 1 (by rfl) ⟨189971279, by rfl⟩ : syracuseStep 253295039 = 379942559) B379942559
theorem B4685147 : Blo 574812 4685147 := bstep (se 1 (by rfl) ⟨3513860, by rfl⟩ : syracuseStep 4685147 = 7027721) B7027721
theorem B3278495 : Blo 574812 3278495 := bstep (se 1 (by rfl) ⟨2458871, by rfl⟩ : syracuseStep 3278495 = 4917743) B4917743
theorem B47418655 : Blo 574812 47418655 := bstep (se 1 (by rfl) ⟨35563991, by rfl⟩ : syracuseStep 47418655 = 71127983) B71127983
theorem B1643303 : Blo 574812 1643303 := bstep (se 1 (by rfl) ⟨1232477, by rfl⟩ : syracuseStep 1643303 = 2464955) B2464955
theorem B12686969 : Blo 574812 12686969 := bstep (se 2 (by rfl) ⟨4757613, by rfl⟩ : syracuseStep 12686969 = 9515227) B9515227
theorem B3283051 : Blo 574812 3283051 := bstep (se 1 (by rfl) ⟨2462288, by rfl⟩ : syracuseStep 3283051 = 4924577) B4924577
theorem B14426371 : Blo 574812 14426371 := bstep (se 1 (by rfl) ⟨10819778, by rfl⟩ : syracuseStep 14426371 = 21639557) B21639557
theorem B168863359 : Blo 574812 168863359 := bstep (se 1 (by rfl) ⟨126647519, by rfl⟩ : syracuseStep 168863359 = 253295039) B253295039
theorem B3123431 : Blo 574812 3123431 := bstep (se 1 (by rfl) ⟨2342573, by rfl⟩ : syracuseStep 3123431 = 4685147) B4685147
theorem B732007 : Blo 574812 732007 := bstep (se 1 (by rfl) ⟨549005, by rfl⟩ : syracuseStep 732007 = 1098011) B1098011
theorem B863999 : Blo 574812 863999 := bstep (se 1 (by rfl) ⟨647999, by rfl⟩ : syracuseStep 863999 = 1295999) B1295999
theorem B865439 : Blo 574812 865439 := bstep (se 1 (by rfl) ⟨649079, by rfl⟩ : syracuseStep 865439 = 1298159) B1298159
theorem B1456127 : Blo 574812 1456127 := bstep (se 1 (by rfl) ⟨1092095, by rfl⟩ : syracuseStep 1456127 = 2184191) B2184191
theorem B8894893 : Blo 574812 8894893 := bstep (se 3 (by rfl) ⟨1667792, by rfl⟩ : syracuseStep 8894893 = 3335585) B3335585
theorem B866783 : Blo 574812 866783 := bstep (se 1 (by rfl) ⟨650087, by rfl⟩ : syracuseStep 866783 = 1300175) B1300175
theorem B1293803 : Blo 574812 1293803 := bstep (se 1 (by rfl) ⟨970352, by rfl⟩ : syracuseStep 1293803 = 1940705) B1940705
theorem B25280639 : Blo 574812 25280639 := bstep (se 1 (by rfl) ⟨18960479, by rfl⟩ : syracuseStep 25280639 = 37920959) B37920959
theorem B1295135 : Blo 574812 1295135 := bstep (se 1 (by rfl) ⟨971351, by rfl⟩ : syracuseStep 1295135 = 1942703) B1942703
theorem B7227001 : Blo 574812 7227001 := bstep (se 2 (by rfl) ⟨2710125, by rfl⟩ : syracuseStep 7227001 = 5420251) B5420251
theorem B971419 : Blo 574812 971419 := bstep (se 1 (by rfl) ⟨728564, by rfl⟩ : syracuseStep 971419 = 1457129) B1457129
theorem B1302047 : Blo 574812 1302047 := bstep (se 1 (by rfl) ⟨976535, by rfl⟩ : syracuseStep 1302047 = 1953071) B1953071
theorem B13328297 : Blo 574812 13328297 := bstep (se 2 (by rfl) ⟨4998111, by rfl⟩ : syracuseStep 13328297 = 9996223) B9996223
theorem B11204831 : Blo 574812 11204831 := bstep (se 1 (by rfl) ⟨8403623, by rfl⟩ : syracuseStep 11204831 = 16807247) B16807247
theorem B19235161 : Blo 574812 19235161 := bstep (se 2 (by rfl) ⟨7213185, by rfl⟩ : syracuseStep 19235161 = 14426371) B14426371
theorem B225151145 : Blo 574812 225151145 := bstep (se 2 (by rfl) ⟨84431679, by rfl⟩ : syracuseStep 225151145 = 168863359) B168863359
theorem B8457979 : Blo 574812 8457979 := bstep (se 1 (by rfl) ⟨6343484, by rfl⟩ : syracuseStep 8457979 = 12686969) B12686969
theorem B8885531 : Blo 574812 8885531 := bstep (se 1 (by rfl) ⟨6664148, by rfl⟩ : syracuseStep 8885531 = 13328297) B13328297
theorem B38544005 : Blo 574812 38544005 := bstep (se 4 (by rfl) ⟨3613500, by rfl⟩ : syracuseStep 38544005 = 7227001) B7227001
theorem B862535 : Blo 574812 862535 := bstep (se 1 (by rfl) ⟨646901, by rfl⟩ : syracuseStep 862535 = 1293803) B1293803
theorem B16853759 : Blo 574812 16853759 := bstep (se 1 (by rfl) ⟨12640319, by rfl⟩ : syracuseStep 16853759 = 25280639) B25280639
theorem B863423 : Blo 574812 863423 := bstep (se 1 (by rfl) ⟨647567, by rfl⟩ : syracuseStep 863423 = 1295135) B1295135
theorem B1095535 : Blo 574812 1095535 := bstep (se 1 (by rfl) ⟨821651, by rfl⟩ : syracuseStep 1095535 = 1643303) B1643303
theorem B63224873 : Blo 574812 63224873 := bstep (se 2 (by rfl) ⟨23709327, by rfl⟩ : syracuseStep 63224873 = 47418655) B47418655
theorem B868031 : Blo 574812 868031 := bstep (se 1 (by rfl) ⟨651023, by rfl⟩ : syracuseStep 868031 = 1302047) B1302047
theorem B1295225 : Blo 574812 1295225 := bstep (se 2 (by rfl) ⟨485709, by rfl⟩ : syracuseStep 1295225 = 971419) B971419
theorem B2082287 : Blo 574812 2082287 := bstep (se 1 (by rfl) ⟨1561715, by rfl⟩ : syracuseStep 2082287 = 3123431) B3123431
theorem B575999 : Blo 574812 575999 := bstep (se 1 (by rfl) ⟨431999, by rfl⟩ : syracuseStep 575999 = 863999) B863999
theorem B4377401 : Blo 574812 4377401 := bstep (se 2 (by rfl) ⟨1641525, by rfl⟩ : syracuseStep 4377401 = 3283051) B3283051
theorem B576959 : Blo 574812 576959 := bstep (se 1 (by rfl) ⟨432719, by rfl⟩ : syracuseStep 576959 = 865439) B865439
theorem B970751 : Blo 574812 970751 := bstep (se 1 (by rfl) ⟨728063, by rfl⟩ : syracuseStep 970751 = 1456127) B1456127
theorem B577855 : Blo 574812 577855 := bstep (se 1 (by rfl) ⟨433391, by rfl⟩ : syracuseStep 577855 = 866783) B866783
theorem B2185663 : Blo 574812 2185663 := bstep (se 1 (by rfl) ⟨1639247, by rfl⟩ : syracuseStep 2185663 = 3278495) B3278495
theorem B976009 : Blo 574812 976009 := bstep (se 2 (by rfl) ⟨366003, by rfl⟩ : syracuseStep 976009 = 732007) B732007
theorem B11859857 : Blo 574812 11859857 := bstep (se 2 (by rfl) ⟨4447446, by rfl⟩ : syracuseStep 11859857 = 8894893) B8894893
theorem B7469887 : Blo 574812 7469887 := bstep (se 1 (by rfl) ⟨5602415, by rfl⟩ : syracuseStep 7469887 = 11204831) B11204831
theorem B2918267 : Blo 574812 2918267 := bstep (se 1 (by rfl) ⟨2188700, by rfl⟩ : syracuseStep 2918267 = 4377401) B4377401
theorem B11277305 : Blo 574812 11277305 := bstep (se 2 (by rfl) ⟨4228989, by rfl⟩ : syracuseStep 11277305 = 8457979) B8457979
theorem B25696003 : Blo 574812 25696003 := bstep (se 1 (by rfl) ⟨19272002, by rfl⟩ : syracuseStep 25696003 = 38544005) B38544005
theorem B7906571 : Blo 574812 7906571 := bstep (se 1 (by rfl) ⟨5929928, by rfl⟩ : syracuseStep 7906571 = 11859857) B11859857
theorem B42149915 : Blo 574812 42149915 := bstep (se 1 (by rfl) ⟨31612436, by rfl⟩ : syracuseStep 42149915 = 63224873) B63224873
theorem B863483 : Blo 574812 863483 := bstep (se 1 (by rfl) ⟨647612, by rfl⟩ : syracuseStep 863483 = 1295225) B1295225
theorem B1388191 : Blo 574812 1388191 := bstep (se 1 (by rfl) ⟨1041143, by rfl⟩ : syracuseStep 1388191 = 2082287) B2082287
theorem B2401612213 : Blo 574812 2401612213 := bstep (se 5 (by rfl) ⟨112575572, by rfl⟩ : syracuseStep 2401612213 = 225151145) B225151145
theorem B575023 : Blo 574812 575023 := bstep (se 1 (by rfl) ⟨431267, by rfl⟩ : syracuseStep 575023 = 862535) B862535
theorem B575615 : Blo 574812 575615 := bstep (se 1 (by rfl) ⟨431711, by rfl⟩ : syracuseStep 575615 = 863423) B863423
theorem B1460713 : Blo 574812 1460713 := bstep (se 2 (by rfl) ⟨547767, by rfl⟩ : syracuseStep 1460713 = 1095535) B1095535
theorem B578687 : Blo 574812 578687 := bstep (se 1 (by rfl) ⟨434015, by rfl⟩ : syracuseStep 578687 = 868031) B868031
theorem B25646881 : Blo 574812 25646881 := bstep (se 2 (by rfl) ⟨9617580, by rfl⟩ : syracuseStep 25646881 = 19235161) B19235161
theorem B1301345 : Blo 574812 1301345 := bstep (se 2 (by rfl) ⟨488004, by rfl⟩ : syracuseStep 1301345 = 976009) B976009
theorem B647167 : Blo 574812 647167 := bstep (se 1 (by rfl) ⟨485375, by rfl⟩ : syracuseStep 647167 = 970751) B970751
theorem B5923687 : Blo 574812 5923687 := bstep (se 1 (by rfl) ⟨4442765, by rfl⟩ : syracuseStep 5923687 = 8885531) B8885531
theorem B11235839 : Blo 574812 11235839 := bstep (se 1 (by rfl) ⟨8426879, by rfl⟩ : syracuseStep 11235839 = 16853759) B16853759
theorem B2914217 : Blo 574812 2914217 := bstep (se 2 (by rfl) ⟨1092831, by rfl⟩ : syracuseStep 2914217 = 2185663) B2185663
theorem B9959849 : Blo 574812 9959849 := bstep (se 2 (by rfl) ⟨3734943, by rfl⟩ : syracuseStep 9959849 = 7469887) B7469887
theorem B7898249 : Blo 574812 7898249 := bstep (se 2 (by rfl) ⟨2961843, by rfl⟩ : syracuseStep 7898249 = 5923687) B5923687
theorem B1942811 : Blo 574812 1942811 := bstep (se 1 (by rfl) ⟨1457108, by rfl⟩ : syracuseStep 1942811 = 2914217) B2914217
theorem B862889 : Blo 574812 862889 := bstep (se 2 (by rfl) ⟨323583, by rfl⟩ : syracuseStep 862889 = 647167) B647167
theorem B1945511 : Blo 574812 1945511 := bstep (se 1 (by rfl) ⟨1459133, by rfl⟩ : syracuseStep 1945511 = 2918267) B2918267
theorem B29962237 : Blo 574812 29962237 := bstep (se 3 (by rfl) ⟨5617919, by rfl⟩ : syracuseStep 29962237 = 11235839) B11235839
theorem B1947617 : Blo 574812 1947617 := bstep (se 2 (by rfl) ⟨730356, by rfl⟩ : syracuseStep 1947617 = 1460713) B1460713
theorem B7518203 : Blo 574812 7518203 := bstep (se 1 (by rfl) ⟨5638652, by rfl⟩ : syracuseStep 7518203 = 11277305) B11277305
theorem B867563 : Blo 574812 867563 := bstep (se 1 (by rfl) ⟨650672, by rfl⟩ : syracuseStep 867563 = 1301345) B1301345
theorem B1850921 : Blo 574812 1850921 := bstep (se 2 (by rfl) ⟨694095, by rfl⟩ : syracuseStep 1850921 = 1388191) B1388191
theorem B28099943 : Blo 574812 28099943 := bstep (se 1 (by rfl) ⟨21074957, by rfl⟩ : syracuseStep 28099943 = 42149915) B42149915
theorem B575655 : Blo 574812 575655 := bstep (se 1 (by rfl) ⟨431741, by rfl⟩ : syracuseStep 575655 = 863483) B863483
theorem B34261337 : Blo 574812 34261337 := bstep (se 2 (by rfl) ⟨12848001, by rfl⟩ : syracuseStep 34261337 = 25696003) B25696003
theorem B34195841 : Blo 574812 34195841 := bstep (se 2 (by rfl) ⟨12823440, by rfl⟩ : syracuseStep 34195841 = 25646881) B25646881
theorem B6639899 : Blo 574812 6639899 := bstep (se 1 (by rfl) ⟨4979924, by rfl⟩ : syracuseStep 6639899 = 9959849) B9959849
theorem B3202149617 : Blo 574812 3202149617 := bstep (se 2 (by rfl) ⟨1200806106, by rfl⟩ : syracuseStep 3202149617 = 2401612213) B2401612213
theorem B5271047 : Blo 574812 5271047 := bstep (se 1 (by rfl) ⟨3953285, by rfl⟩ : syracuseStep 5271047 = 7906571) B7906571
theorem B39949649 : Blo 574812 39949649 := bstep (se 2 (by rfl) ⟨14981118, by rfl⟩ : syracuseStep 39949649 = 29962237) B29962237
theorem B91363565 : Blo 574812 91363565 := bstep (se 3 (by rfl) ⟨17130668, by rfl⟩ : syracuseStep 91363565 = 34261337) B34261337
theorem B3514031 : Blo 574812 3514031 := bstep (se 1 (by rfl) ⟨2635523, by rfl⟩ : syracuseStep 3514031 = 5271047) B5271047
theorem B17706397 : Blo 574812 17706397 := bstep (se 3 (by rfl) ⟨3319949, by rfl⟩ : syracuseStep 17706397 = 6639899) B6639899
theorem B1295207 : Blo 574812 1295207 := bstep (se 1 (by rfl) ⟨971405, by rfl⟩ : syracuseStep 1295207 = 1942811) B1942811
theorem B575259 : Blo 574812 575259 := bstep (se 1 (by rfl) ⟨431444, by rfl⟩ : syracuseStep 575259 = 862889) B862889
theorem B1297007 : Blo 574812 1297007 := bstep (se 1 (by rfl) ⟨972755, by rfl⟩ : syracuseStep 1297007 = 1945511) B1945511
theorem B1298411 : Blo 574812 1298411 := bstep (se 1 (by rfl) ⟨973808, by rfl⟩ : syracuseStep 1298411 = 1947617) B1947617
theorem B578375 : Blo 574812 578375 := bstep (se 1 (by rfl) ⟨433781, by rfl⟩ : syracuseStep 578375 = 867563) B867563
theorem B1233947 : Blo 574812 1233947 := bstep (se 1 (by rfl) ⟨925460, by rfl⟩ : syracuseStep 1233947 = 1850921) B1850921
theorem B5265499 : Blo 574812 5265499 := bstep (se 1 (by rfl) ⟨3949124, by rfl⟩ : syracuseStep 5265499 = 7898249) B7898249
theorem B18733295 : Blo 574812 18733295 := bstep (se 1 (by rfl) ⟨14049971, by rfl⟩ : syracuseStep 18733295 = 28099943) B28099943
theorem B22797227 : Blo 574812 22797227 := bstep (se 1 (by rfl) ⟨17097920, by rfl⟩ : syracuseStep 22797227 = 34195841) B34195841
theorem B2134766411 : Blo 574812 2134766411 := bstep (se 1 (by rfl) ⟨1601074808, by rfl⟩ : syracuseStep 2134766411 = 3202149617) B3202149617
theorem B5012135 : Blo 574812 5012135 := bstep (se 1 (by rfl) ⟨3759101, by rfl⟩ : syracuseStep 5012135 = 7518203) B7518203
theorem B822631 : Blo 574812 822631 := bstep (se 1 (by rfl) ⟨616973, by rfl⟩ : syracuseStep 822631 = 1233947) B1233947
theorem B7020665 : Blo 574812 7020665 := bstep (se 2 (by rfl) ⟨2632749, by rfl⟩ : syracuseStep 7020665 = 5265499) B5265499
theorem B863471 : Blo 574812 863471 := bstep (se 1 (by rfl) ⟨647603, by rfl⟩ : syracuseStep 863471 = 1295207) B1295207
theorem B864671 : Blo 574812 864671 := bstep (se 1 (by rfl) ⟨648503, by rfl⟩ : syracuseStep 864671 = 1297007) B1297007
theorem B865607 : Blo 574812 865607 := bstep (se 1 (by rfl) ⟨649205, by rfl⟩ : syracuseStep 865607 = 1298411) B1298411
theorem B23608529 : Blo 574812 23608529 := bstep (se 2 (by rfl) ⟨8853198, by rfl⟩ : syracuseStep 23608529 = 17706397) B17706397
theorem B2342687 : Blo 574812 2342687 := bstep (se 1 (by rfl) ⟨1757015, by rfl⟩ : syracuseStep 2342687 = 3514031) B3514031
theorem B49955453 : Blo 574812 49955453 := bstep (se 3 (by rfl) ⟨9366647, by rfl⟩ : syracuseStep 49955453 = 18733295) B18733295
theorem B26633099 : Blo 574812 26633099 := bstep (se 1 (by rfl) ⟨19974824, by rfl⟩ : syracuseStep 26633099 = 39949649) B39949649
theorem B60909043 : Blo 574812 60909043 := bstep (se 1 (by rfl) ⟨45681782, by rfl⟩ : syracuseStep 60909043 = 91363565) B91363565
theorem B15198151 : Blo 574812 15198151 := bstep (se 1 (by rfl) ⟨11398613, by rfl⟩ : syracuseStep 15198151 = 22797227) B22797227
theorem B1423177607 : Blo 574812 1423177607 := bstep (se 1 (by rfl) ⟨1067383205, by rfl⟩ : syracuseStep 1423177607 = 2134766411) B2134766411
theorem B3341423 : Blo 574812 3341423 := bstep (se 1 (by rfl) ⟨2506067, by rfl⟩ : syracuseStep 3341423 = 5012135) B5012135
theorem B15739019 : Blo 574812 15739019 := bstep (se 1 (by rfl) ⟨11804264, by rfl⟩ : syracuseStep 15739019 = 23608529) B23608529
theorem B33303635 : Blo 574812 33303635 := bstep (se 1 (by rfl) ⟨24977726, by rfl⟩ : syracuseStep 33303635 = 49955453) B49955453
theorem B81212057 : Blo 574812 81212057 := bstep (se 2 (by rfl) ⟨30454521, by rfl⟩ : syracuseStep 81212057 = 60909043) B60909043
theorem B20264201 : Blo 574812 20264201 := bstep (se 2 (by rfl) ⟨7599075, by rfl⟩ : syracuseStep 20264201 = 15198151) B15198151
theorem B1096841 : Blo 574812 1096841 := bstep (se 2 (by rfl) ⟨411315, by rfl⟩ : syracuseStep 1096841 = 822631) B822631
theorem B575647 : Blo 574812 575647 := bstep (se 1 (by rfl) ⟨431735, by rfl⟩ : syracuseStep 575647 = 863471) B863471
theorem B576447 : Blo 574812 576447 := bstep (se 1 (by rfl) ⟨432335, by rfl⟩ : syracuseStep 576447 = 864671) B864671
theorem B577071 : Blo 574812 577071 := bstep (se 1 (by rfl) ⟨432803, by rfl⟩ : syracuseStep 577071 = 865607) B865607
theorem B948785071 : Blo 574812 948785071 := bstep (se 1 (by rfl) ⟨711588803, by rfl⟩ : syracuseStep 948785071 = 1423177607) B1423177607
theorem B6247165 : Blo 574812 6247165 := bstep (se 3 (by rfl) ⟨1171343, by rfl⟩ : syracuseStep 6247165 = 2342687) B2342687
theorem B4680443 : Blo 574812 4680443 := bstep (se 1 (by rfl) ⟨3510332, by rfl⟩ : syracuseStep 4680443 = 7020665) B7020665
theorem B17755399 : Blo 574812 17755399 := bstep (se 1 (by rfl) ⟨13316549, by rfl⟩ : syracuseStep 17755399 = 26633099) B26633099
theorem B8910461 : Blo 574812 8910461 := bstep (se 3 (by rfl) ⟨1670711, by rfl⟩ : syracuseStep 8910461 = 3341423) B3341423
theorem B1265046761 : Blo 574812 1265046761 := bstep (se 2 (by rfl) ⟨474392535, by rfl⟩ : syracuseStep 1265046761 = 948785071) B948785071
theorem B8329553 : Blo 574812 8329553 := bstep (se 2 (by rfl) ⟨3123582, by rfl⟩ : syracuseStep 8329553 = 6247165) B6247165
theorem B10492679 : Blo 574812 10492679 := bstep (se 1 (by rfl) ⟨7869509, by rfl⟩ : syracuseStep 10492679 = 15739019) B15739019
theorem B3120295 : Blo 574812 3120295 := bstep (se 1 (by rfl) ⟨2340221, by rfl⟩ : syracuseStep 3120295 = 4680443) B4680443
theorem B2924909 : Blo 574812 2924909 := bstep (se 3 (by rfl) ⟨548420, by rfl⟩ : syracuseStep 2924909 = 1096841) B1096841
theorem B54141371 : Blo 574812 54141371 := bstep (se 1 (by rfl) ⟨40606028, by rfl⟩ : syracuseStep 54141371 = 81212057) B81212057
theorem B13509467 : Blo 574812 13509467 := bstep (se 1 (by rfl) ⟨10132100, by rfl⟩ : syracuseStep 13509467 = 20264201) B20264201
theorem B5940307 : Blo 574812 5940307 := bstep (se 1 (by rfl) ⟨4455230, by rfl⟩ : syracuseStep 5940307 = 8910461) B8910461
theorem B23673865 : Blo 574812 23673865 := bstep (se 2 (by rfl) ⟨8877699, by rfl⟩ : syracuseStep 23673865 = 17755399) B17755399
theorem B22202423 : Blo 574812 22202423 := bstep (se 1 (by rfl) ⟨16651817, by rfl⟩ : syracuseStep 22202423 = 33303635) B33303635
theorem B31565153 : Blo 574812 31565153 := bstep (se 2 (by rfl) ⟨11836932, by rfl⟩ : syracuseStep 31565153 = 23673865) B23673865
theorem B843364507 : Blo 574812 843364507 := bstep (se 1 (by rfl) ⟨632523380, by rfl⟩ : syracuseStep 843364507 = 1265046761) B1265046761
theorem B5553035 : Blo 574812 5553035 := bstep (se 1 (by rfl) ⟨4164776, by rfl⟩ : syracuseStep 5553035 = 8329553) B8329553
theorem B6995119 : Blo 574812 6995119 := bstep (se 1 (by rfl) ⟨5246339, by rfl⟩ : syracuseStep 6995119 = 10492679) B10492679
theorem B1949939 : Blo 574812 1949939 := bstep (se 1 (by rfl) ⟨1462454, by rfl⟩ : syracuseStep 1949939 = 2924909) B2924909
theorem B36094247 : Blo 574812 36094247 := bstep (se 1 (by rfl) ⟨27070685, by rfl⟩ : syracuseStep 36094247 = 54141371) B54141371
theorem B14801615 : Blo 574812 14801615 := bstep (se 1 (by rfl) ⟨11101211, by rfl⟩ : syracuseStep 14801615 = 22202423) B22202423
theorem B7920409 : Blo 574812 7920409 := bstep (se 2 (by rfl) ⟨2970153, by rfl⟩ : syracuseStep 7920409 = 5940307) B5940307
theorem B9006311 : Blo 574812 9006311 := bstep (se 1 (by rfl) ⟨6754733, by rfl⟩ : syracuseStep 9006311 = 13509467) B13509467
theorem B4160393 : Blo 574812 4160393 := bstep (se 2 (by rfl) ⟨1560147, by rfl⟩ : syracuseStep 4160393 = 3120295) B3120295
theorem B9867743 : Blo 574812 9867743 := bstep (se 1 (by rfl) ⟨7400807, by rfl⟩ : syracuseStep 9867743 = 14801615) B14801615
theorem B21043435 : Blo 574812 21043435 := bstep (se 1 (by rfl) ⟨15782576, by rfl⟩ : syracuseStep 21043435 = 31565153) B31565153
theorem B6004207 : Blo 574812 6004207 := bstep (se 1 (by rfl) ⟨4503155, by rfl⟩ : syracuseStep 6004207 = 9006311) B9006311
theorem B10560545 : Blo 574812 10560545 := bstep (se 2 (by rfl) ⟨3960204, by rfl⟩ : syracuseStep 10560545 = 7920409) B7920409
theorem B24062831 : Blo 574812 24062831 := bstep (se 1 (by rfl) ⟨18047123, by rfl⟩ : syracuseStep 24062831 = 36094247) B36094247
theorem B1124486009 : Blo 574812 1124486009 := bstep (se 2 (by rfl) ⟨421682253, by rfl⟩ : syracuseStep 1124486009 = 843364507) B843364507
theorem B9326825 : Blo 574812 9326825 := bstep (se 2 (by rfl) ⟨3497559, by rfl⟩ : syracuseStep 9326825 = 6995119) B6995119
theorem B2773595 : Blo 574812 2773595 := bstep (se 1 (by rfl) ⟨2080196, by rfl⟩ : syracuseStep 2773595 = 4160393) B4160393
theorem B1299959 : Blo 574812 1299959 := bstep (se 1 (by rfl) ⟨974969, by rfl⟩ : syracuseStep 1299959 = 1949939) B1949939
theorem B3702023 : Blo 574812 3702023 := bstep (se 1 (by rfl) ⟨2776517, by rfl⟩ : syracuseStep 3702023 = 5553035) B5553035
theorem B28057913 : Blo 574812 28057913 := bstep (se 2 (by rfl) ⟨10521717, by rfl⟩ : syracuseStep 28057913 = 21043435) B21043435
theorem B8005609 : Blo 574812 8005609 := bstep (se 2 (by rfl) ⟨3002103, by rfl⟩ : syracuseStep 8005609 = 6004207) B6004207
theorem B2468015 : Blo 574812 2468015 := bstep (se 1 (by rfl) ⟨1851011, by rfl⟩ : syracuseStep 2468015 = 3702023) B3702023
theorem B1849063 : Blo 574812 1849063 := bstep (se 1 (by rfl) ⟨1386797, by rfl⟩ : syracuseStep 1849063 = 2773595) B2773595
theorem B866639 : Blo 574812 866639 := bstep (se 1 (by rfl) ⟨649979, by rfl⟩ : syracuseStep 866639 = 1299959) B1299959
theorem B16041887 : Blo 574812 16041887 := bstep (se 1 (by rfl) ⟨12031415, by rfl⟩ : syracuseStep 16041887 = 24062831) B24062831
theorem B749657339 : Blo 574812 749657339 := bstep (se 1 (by rfl) ⟨562243004, by rfl⟩ : syracuseStep 749657339 = 1124486009) B1124486009
theorem B6217883 : Blo 574812 6217883 := bstep (se 1 (by rfl) ⟨4663412, by rfl⟩ : syracuseStep 6217883 = 9326825) B9326825
theorem B6578495 : Blo 574812 6578495 := bstep (se 1 (by rfl) ⟨4933871, by rfl⟩ : syracuseStep 6578495 = 9867743) B9867743
theorem B7040363 : Blo 574812 7040363 := bstep (se 1 (by rfl) ⟨5280272, by rfl⟩ : syracuseStep 7040363 = 10560545) B10560545
theorem B1645343 : Blo 574812 1645343 := bstep (se 1 (by rfl) ⟨1234007, by rfl⟩ : syracuseStep 1645343 = 2468015) B2468015
theorem B2465417 : Blo 574812 2465417 := bstep (se 2 (by rfl) ⟨924531, by rfl⟩ : syracuseStep 2465417 = 1849063) B1849063
theorem B10694591 : Blo 574812 10694591 := bstep (se 1 (by rfl) ⟨8020943, by rfl⟩ : syracuseStep 10694591 = 16041887) B16041887
theorem B4145255 : Blo 574812 4145255 := bstep (se 1 (by rfl) ⟨3108941, by rfl⟩ : syracuseStep 4145255 = 6217883) B6217883
theorem B577759 : Blo 574812 577759 := bstep (se 1 (by rfl) ⟨433319, by rfl⟩ : syracuseStep 577759 = 866639) B866639
theorem B10674145 : Blo 574812 10674145 := bstep (se 2 (by rfl) ⟨4002804, by rfl⟩ : syracuseStep 10674145 = 8005609) B8005609
theorem B499771559 : Blo 574812 499771559 := bstep (se 1 (by rfl) ⟨374828669, by rfl⟩ : syracuseStep 499771559 = 749657339) B749657339
theorem B18705275 : Blo 574812 18705275 := bstep (se 1 (by rfl) ⟨14028956, by rfl⟩ : syracuseStep 18705275 = 28057913) B28057913
theorem B4385663 : Blo 574812 4385663 := bstep (se 1 (by rfl) ⟨3289247, by rfl⟩ : syracuseStep 4385663 = 6578495) B6578495
theorem B18774301 : Blo 574812 18774301 := bstep (se 3 (by rfl) ⟨3520181, by rfl⟩ : syracuseStep 18774301 = 7040363) B7040363
theorem B1643611 : Blo 574812 1643611 := bstep (se 1 (by rfl) ⟨1232708, by rfl⟩ : syracuseStep 1643611 = 2465417) B2465417
theorem B2923775 : Blo 574812 2923775 := bstep (se 1 (by rfl) ⟨2192831, by rfl⟩ : syracuseStep 2923775 = 4385663) B4385663
theorem B14232193 : Blo 574812 14232193 := bstep (se 2 (by rfl) ⟨5337072, by rfl⟩ : syracuseStep 14232193 = 10674145) B10674145
theorem B2763503 : Blo 574812 2763503 := bstep (se 1 (by rfl) ⟨2072627, by rfl⟩ : syracuseStep 2763503 = 4145255) B4145255
theorem B1096895 : Blo 574812 1096895 := bstep (se 1 (by rfl) ⟨822671, by rfl⟩ : syracuseStep 1096895 = 1645343) B1645343
theorem B12470183 : Blo 574812 12470183 := bstep (se 1 (by rfl) ⟨9352637, by rfl⟩ : syracuseStep 12470183 = 18705275) B18705275
theorem B7129727 : Blo 574812 7129727 := bstep (se 1 (by rfl) ⟨5347295, by rfl⟩ : syracuseStep 7129727 = 10694591) B10694591
theorem B333181039 : Blo 574812 333181039 := bstep (se 1 (by rfl) ⟨249885779, by rfl⟩ : syracuseStep 333181039 = 499771559) B499771559
theorem B25032401 : Blo 574812 25032401 := bstep (se 2 (by rfl) ⟨9387150, by rfl⟩ : syracuseStep 25032401 = 18774301) B18774301
theorem B4753151 : Blo 574812 4753151 := bstep (se 1 (by rfl) ⟨3564863, by rfl⟩ : syracuseStep 4753151 = 7129727) B7129727
theorem B444241385 : Blo 574812 444241385 := bstep (se 2 (by rfl) ⟨166590519, by rfl⟩ : syracuseStep 444241385 = 333181039) B333181039
theorem B1842335 : Blo 574812 1842335 := bstep (se 1 (by rfl) ⟨1381751, by rfl⟩ : syracuseStep 1842335 = 2763503) B2763503
theorem B16688267 : Blo 574812 16688267 := bstep (se 1 (by rfl) ⟨12516200, by rfl⟩ : syracuseStep 16688267 = 25032401) B25032401
theorem B731263 : Blo 574812 731263 := bstep (se 1 (by rfl) ⟨548447, by rfl⟩ : syracuseStep 731263 = 1096895) B1096895
theorem B75905029 : Blo 574812 75905029 := bstep (se 4 (by rfl) ⟨7116096, by rfl⟩ : syracuseStep 75905029 = 14232193) B14232193
theorem B1949183 : Blo 574812 1949183 := bstep (se 1 (by rfl) ⟨1461887, by rfl⟩ : syracuseStep 1949183 = 2923775) B2923775
theorem B8313455 : Blo 574812 8313455 := bstep (se 1 (by rfl) ⟨6235091, by rfl⟩ : syracuseStep 8313455 = 12470183) B12470183
theorem B2191481 : Blo 574812 2191481 := bstep (se 2 (by rfl) ⟨821805, by rfl⟩ : syracuseStep 2191481 = 1643611) B1643611
theorem B296160923 : Blo 574812 296160923 := bstep (se 1 (by rfl) ⟨222120692, by rfl⟩ : syracuseStep 296160923 = 444241385) B444241385
theorem B5542303 : Blo 574812 5542303 := bstep (se 1 (by rfl) ⟨4156727, by rfl⟩ : syracuseStep 5542303 = 8313455) B8313455
theorem B1228223 : Blo 574812 1228223 := bstep (se 1 (by rfl) ⟨921167, by rfl⟩ : syracuseStep 1228223 = 1842335) B1842335
theorem B11125511 : Blo 574812 11125511 := bstep (se 1 (by rfl) ⟨8344133, by rfl⟩ : syracuseStep 11125511 = 16688267) B16688267
theorem B101206705 : Blo 574812 101206705 := bstep (se 2 (by rfl) ⟨37952514, by rfl⟩ : syracuseStep 101206705 = 75905029) B75905029
theorem B1460987 : Blo 574812 1460987 := bstep (se 1 (by rfl) ⟨1095740, by rfl⟩ : syracuseStep 1460987 = 2191481) B2191481
theorem B1299455 : Blo 574812 1299455 := bstep (se 1 (by rfl) ⟨974591, by rfl⟩ : syracuseStep 1299455 = 1949183) B1949183
theorem B3168767 : Blo 574812 3168767 := bstep (se 1 (by rfl) ⟨2376575, by rfl⟩ : syracuseStep 3168767 = 4753151) B4753151
theorem B975017 : Blo 574812 975017 := bstep (se 2 (by rfl) ⟨365631, by rfl⟩ : syracuseStep 975017 = 731263) B731263
theorem B134942273 : Blo 574812 134942273 := bstep (se 2 (by rfl) ⟨50603352, by rfl⟩ : syracuseStep 134942273 = 101206705) B101206705
theorem B7417007 : Blo 574812 7417007 := bstep (se 1 (by rfl) ⟨5562755, by rfl⟩ : syracuseStep 7417007 = 11125511) B11125511
theorem B197440615 : Blo 574812 197440615 := bstep (se 1 (by rfl) ⟨148080461, by rfl⟩ : syracuseStep 197440615 = 296160923) B296160923
theorem B866303 : Blo 574812 866303 := bstep (se 1 (by rfl) ⟨649727, by rfl⟩ : syracuseStep 866303 = 1299455) B1299455
theorem B7389737 : Blo 574812 7389737 := bstep (se 2 (by rfl) ⟨2771151, by rfl⟩ : syracuseStep 7389737 = 5542303) B5542303
theorem B973991 : Blo 574812 973991 := bstep (se 1 (by rfl) ⟨730493, by rfl⟩ : syracuseStep 973991 = 1460987) B1460987
theorem B650011 : Blo 574812 650011 := bstep (se 1 (by rfl) ⟨487508, by rfl⟩ : syracuseStep 650011 = 975017) B975017
theorem B8450045 : Blo 574812 8450045 := bstep (se 3 (by rfl) ⟨1584383, by rfl⟩ : syracuseStep 8450045 = 3168767) B3168767
theorem B3275261 : Blo 574812 3275261 := bstep (se 3 (by rfl) ⟨614111, by rfl⟩ : syracuseStep 3275261 = 1228223) B1228223
theorem B4926491 : Blo 574812 4926491 := bstep (se 1 (by rfl) ⟨3694868, by rfl⟩ : syracuseStep 4926491 = 7389737) B7389737
theorem B89961515 : Blo 574812 89961515 := bstep (se 1 (by rfl) ⟨67471136, by rfl⟩ : syracuseStep 89961515 = 134942273) B134942273
theorem B866681 : Blo 574812 866681 := bstep (se 2 (by rfl) ⟨325005, by rfl⟩ : syracuseStep 866681 = 650011) B650011
theorem B577535 : Blo 574812 577535 := bstep (se 1 (by rfl) ⟨433151, by rfl⟩ : syracuseStep 577535 = 866303) B866303
theorem B2183507 : Blo 574812 2183507 := bstep (se 1 (by rfl) ⟨1637630, by rfl⟩ : syracuseStep 2183507 = 3275261) B3275261
theorem B649327 : Blo 574812 649327 := bstep (se 1 (by rfl) ⟨486995, by rfl⟩ : syracuseStep 649327 = 973991) B973991
theorem B263254153 : Blo 574812 263254153 := bstep (se 2 (by rfl) ⟨98720307, by rfl⟩ : syracuseStep 263254153 = 197440615) B197440615
theorem B4944671 : Blo 574812 4944671 := bstep (se 1 (by rfl) ⟨3708503, by rfl⟩ : syracuseStep 4944671 = 7417007) B7417007
theorem B5633363 : Blo 574812 5633363 := bstep (se 1 (by rfl) ⟨4225022, by rfl⟩ : syracuseStep 5633363 = 8450045) B8450045
theorem B3284327 : Blo 574812 3284327 := bstep (se 1 (by rfl) ⟨2463245, by rfl⟩ : syracuseStep 3284327 = 4926491) B4926491
theorem B59974343 : Blo 574812 59974343 := bstep (se 1 (by rfl) ⟨44980757, by rfl⟩ : syracuseStep 59974343 = 89961515) B89961515
theorem B865769 : Blo 574812 865769 := bstep (se 2 (by rfl) ⟨324663, by rfl⟩ : syracuseStep 865769 = 649327) B649327
theorem B1455671 : Blo 574812 1455671 := bstep (se 1 (by rfl) ⟨1091753, by rfl⟩ : syracuseStep 1455671 = 2183507) B2183507
theorem B3296447 : Blo 574812 3296447 := bstep (se 1 (by rfl) ⟨2472335, by rfl⟩ : syracuseStep 3296447 = 4944671) B4944671
theorem B3755575 : Blo 574812 3755575 := bstep (se 1 (by rfl) ⟨2816681, by rfl⟩ : syracuseStep 3755575 = 5633363) B5633363
theorem B577787 : Blo 574812 577787 := bstep (se 1 (by rfl) ⟨433340, by rfl⟩ : syracuseStep 577787 = 866681) B866681
theorem B351005537 : Blo 574812 351005537 := bstep (se 2 (by rfl) ⟨131627076, by rfl⟩ : syracuseStep 351005537 = 263254153) B263254153
theorem B2197631 : Blo 574812 2197631 := bstep (se 1 (by rfl) ⟨1648223, by rfl⟩ : syracuseStep 2197631 = 3296447) B3296447
theorem B39982895 : Blo 574812 39982895 := bstep (se 1 (by rfl) ⟨29987171, by rfl⟩ : syracuseStep 39982895 = 59974343) B59974343
theorem B234003691 : Blo 574812 234003691 := bstep (se 1 (by rfl) ⟨175502768, by rfl⟩ : syracuseStep 234003691 = 351005537) B351005537
theorem B577179 : Blo 574812 577179 := bstep (se 1 (by rfl) ⟨432884, by rfl⟩ : syracuseStep 577179 = 865769) B865769
theorem B970447 : Blo 574812 970447 := bstep (se 1 (by rfl) ⟨727835, by rfl⟩ : syracuseStep 970447 = 1455671) B1455671
theorem B5007433 : Blo 574812 5007433 := bstep (se 2 (by rfl) ⟨1877787, by rfl⟩ : syracuseStep 5007433 = 3755575) B3755575
theorem B2189551 : Blo 574812 2189551 := bstep (se 1 (by rfl) ⟨1642163, by rfl⟩ : syracuseStep 2189551 = 3284327) B3284327
theorem B2919401 : Blo 574812 2919401 := bstep (se 2 (by rfl) ⟨1094775, by rfl⟩ : syracuseStep 2919401 = 2189551) B2189551
theorem B26655263 : Blo 574812 26655263 := bstep (se 1 (by rfl) ⟨19991447, by rfl⟩ : syracuseStep 26655263 = 39982895) B39982895
theorem B1293929 : Blo 574812 1293929 := bstep (se 2 (by rfl) ⟨485223, by rfl⟩ : syracuseStep 1293929 = 970447) B970447
theorem B312004921 : Blo 574812 312004921 := bstep (se 2 (by rfl) ⟨117001845, by rfl⟩ : syracuseStep 312004921 = 234003691) B234003691
theorem B1465087 : Blo 574812 1465087 := bstep (se 1 (by rfl) ⟨1098815, by rfl⟩ : syracuseStep 1465087 = 2197631) B2197631
theorem B6676577 : Blo 574812 6676577 := bstep (se 2 (by rfl) ⟨2503716, by rfl⟩ : syracuseStep 6676577 = 5007433) B5007433
theorem B17770175 : Blo 574812 17770175 := bstep (se 1 (by rfl) ⟨13327631, by rfl⟩ : syracuseStep 17770175 = 26655263) B26655263
theorem B862619 : Blo 574812 862619 := bstep (se 1 (by rfl) ⟨646964, by rfl⟩ : syracuseStep 862619 = 1293929) B1293929
theorem B1946267 : Blo 574812 1946267 := bstep (se 1 (by rfl) ⟨1459700, by rfl⟩ : syracuseStep 1946267 = 2919401) B2919401
theorem B416006561 : Blo 574812 416006561 := bstep (se 2 (by rfl) ⟨156002460, by rfl⟩ : syracuseStep 416006561 = 312004921) B312004921
theorem B1953449 : Blo 574812 1953449 := bstep (se 2 (by rfl) ⟨732543, by rfl⟩ : syracuseStep 1953449 = 1465087) B1465087
theorem B4451051 : Blo 574812 4451051 := bstep (se 1 (by rfl) ⟨3338288, by rfl⟩ : syracuseStep 4451051 = 6676577) B6676577
theorem B11846783 : Blo 574812 11846783 := bstep (se 1 (by rfl) ⟨8885087, by rfl⟩ : syracuseStep 11846783 = 17770175) B17770175
theorem B575079 : Blo 574812 575079 := bstep (se 1 (by rfl) ⟨431309, by rfl⟩ : syracuseStep 575079 = 862619) B862619
theorem B2967367 : Blo 574812 2967367 := bstep (se 1 (by rfl) ⟨2225525, by rfl⟩ : syracuseStep 2967367 = 4451051) B4451051
theorem B1297511 : Blo 574812 1297511 := bstep (se 1 (by rfl) ⟨973133, by rfl⟩ : syracuseStep 1297511 = 1946267) B1946267
theorem B1109350829 : Blo 574812 1109350829 := bstep (se 3 (by rfl) ⟨208003280, by rfl⟩ : syracuseStep 1109350829 = 416006561) B416006561
theorem B1302299 : Blo 574812 1302299 := bstep (se 1 (by rfl) ⟨976724, by rfl⟩ : syracuseStep 1302299 = 1953449) B1953449
theorem B31591421 : Blo 574812 31591421 := bstep (se 3 (by rfl) ⟨5923391, by rfl⟩ : syracuseStep 31591421 = 11846783) B11846783
theorem B865007 : Blo 574812 865007 := bstep (se 1 (by rfl) ⟨648755, by rfl⟩ : syracuseStep 865007 = 1297511) B1297511
theorem B868199 : Blo 574812 868199 := bstep (se 1 (by rfl) ⟨651149, by rfl⟩ : syracuseStep 868199 = 1302299) B1302299
theorem B3956489 : Blo 574812 3956489 := bstep (se 2 (by rfl) ⟨1483683, by rfl⟩ : syracuseStep 3956489 = 2967367) B2967367
theorem B739567219 : Blo 574812 739567219 := bstep (se 1 (by rfl) ⟨554675414, by rfl⟩ : syracuseStep 739567219 = 1109350829) B1109350829
theorem B986089625 : Blo 574812 986089625 := bstep (se 2 (by rfl) ⟨369783609, by rfl⟩ : syracuseStep 986089625 = 739567219) B739567219
theorem B2637659 : Blo 574812 2637659 := bstep (se 1 (by rfl) ⟨1978244, by rfl⟩ : syracuseStep 2637659 = 3956489) B3956489
theorem B576671 : Blo 574812 576671 := bstep (se 1 (by rfl) ⟨432503, by rfl⟩ : syracuseStep 576671 = 865007) B865007
theorem B578799 : Blo 574812 578799 := bstep (se 1 (by rfl) ⟨434099, by rfl⟩ : syracuseStep 578799 = 868199) B868199
theorem B21060947 : Blo 574812 21060947 := bstep (se 1 (by rfl) ⟨15795710, by rfl⟩ : syracuseStep 21060947 = 31591421) B31591421
theorem B657393083 : Blo 574812 657393083 := bstep (se 1 (by rfl) ⟨493044812, by rfl⟩ : syracuseStep 657393083 = 986089625) B986089625
theorem B14040631 : Blo 574812 14040631 := bstep (se 1 (by rfl) ⟨10530473, by rfl⟩ : syracuseStep 14040631 = 21060947) B21060947
theorem B1758439 : Blo 574812 1758439 := bstep (se 1 (by rfl) ⟨1318829, by rfl⟩ : syracuseStep 1758439 = 2637659) B2637659
theorem B18720841 : Blo 574812 18720841 := bstep (se 2 (by rfl) ⟨7020315, by rfl⟩ : syracuseStep 18720841 = 14040631) B14040631
theorem B2344585 : Blo 574812 2344585 := bstep (se 2 (by rfl) ⟨879219, by rfl⟩ : syracuseStep 2344585 = 1758439) B1758439
theorem B438262055 : Blo 574812 438262055 := bstep (se 1 (by rfl) ⟨328696541, by rfl⟩ : syracuseStep 438262055 = 657393083) B657393083
theorem B3126113 : Blo 574812 3126113 := bstep (se 2 (by rfl) ⟨1172292, by rfl⟩ : syracuseStep 3126113 = 2344585) B2344585
theorem B292174703 : Blo 574812 292174703 := bstep (se 1 (by rfl) ⟨219131027, by rfl⟩ : syracuseStep 292174703 = 438262055) B438262055
theorem B24961121 : Blo 574812 24961121 := bstep (se 2 (by rfl) ⟨9360420, by rfl⟩ : syracuseStep 24961121 = 18720841) B18720841
theorem B194783135 : Blo 574812 194783135 := bstep (se 1 (by rfl) ⟨146087351, by rfl⟩ : syracuseStep 194783135 = 292174703) B292174703
theorem B2084075 : Blo 574812 2084075 := bstep (se 1 (by rfl) ⟨1563056, by rfl⟩ : syracuseStep 2084075 = 3126113) B3126113
theorem B16640747 : Blo 574812 16640747 := bstep (se 1 (by rfl) ⟨12480560, by rfl⟩ : syracuseStep 16640747 = 24961121) B24961121
theorem B1389383 : Blo 574812 1389383 := bstep (se 1 (by rfl) ⟨1042037, by rfl⟩ : syracuseStep 1389383 = 2084075) B2084075
theorem B519421693 : Blo 574812 519421693 := bstep (se 3 (by rfl) ⟨97391567, by rfl⟩ : syracuseStep 519421693 = 194783135) B194783135
theorem B11093831 : Blo 574812 11093831 := bstep (se 1 (by rfl) ⟨8320373, by rfl⟩ : syracuseStep 11093831 = 16640747) B16640747
theorem B926255 : Blo 574812 926255 := bstep (se 1 (by rfl) ⟨694691, by rfl⟩ : syracuseStep 926255 = 1389383) B1389383
theorem B692562257 : Blo 574812 692562257 := bstep (se 2 (by rfl) ⟨259710846, by rfl⟩ : syracuseStep 692562257 = 519421693) B519421693
theorem B7395887 : Blo 574812 7395887 := bstep (se 1 (by rfl) ⟨5546915, by rfl⟩ : syracuseStep 7395887 = 11093831) B11093831
theorem B461708171 : Blo 574812 461708171 := bstep (se 1 (by rfl) ⟨346281128, by rfl⟩ : syracuseStep 461708171 = 692562257) B692562257
theorem B2470013 : Blo 574812 2470013 := bstep (se 3 (by rfl) ⟨463127, by rfl⟩ : syracuseStep 2470013 = 926255) B926255
theorem B4930591 : Blo 574812 4930591 := bstep (se 1 (by rfl) ⟨3697943, by rfl⟩ : syracuseStep 4930591 = 7395887) B7395887
theorem B1646675 : Blo 574812 1646675 := bstep (se 1 (by rfl) ⟨1235006, by rfl⟩ : syracuseStep 1646675 = 2470013) B2470013
theorem B307805447 : Blo 574812 307805447 := bstep (se 1 (by rfl) ⟨230854085, by rfl⟩ : syracuseStep 307805447 = 461708171) B461708171
theorem B6574121 : Blo 574812 6574121 := bstep (se 2 (by rfl) ⟨2465295, by rfl⟩ : syracuseStep 6574121 = 4930591) B4930591
theorem B205203631 : Blo 574812 205203631 := bstep (se 1 (by rfl) ⟨153902723, by rfl⟩ : syracuseStep 205203631 = 307805447) B307805447
theorem B1097783 : Blo 574812 1097783 := bstep (se 1 (by rfl) ⟨823337, by rfl⟩ : syracuseStep 1097783 = 1646675) B1646675
theorem B4382747 : Blo 574812 4382747 := bstep (se 1 (by rfl) ⟨3287060, by rfl⟩ : syracuseStep 4382747 = 6574121) B6574121
theorem B2921831 : Blo 574812 2921831 := bstep (se 1 (by rfl) ⟨2191373, by rfl⟩ : syracuseStep 2921831 = 4382747) B4382747
theorem B731855 : Blo 574812 731855 := bstep (se 1 (by rfl) ⟨548891, by rfl⟩ : syracuseStep 731855 = 1097783) B1097783
theorem B273604841 : Blo 574812 273604841 := bstep (se 2 (by rfl) ⟨102601815, by rfl⟩ : syracuseStep 273604841 = 205203631) B205203631
theorem B1947887 : Blo 574812 1947887 := bstep (se 1 (by rfl) ⟨1460915, by rfl⟩ : syracuseStep 1947887 = 2921831) B2921831
theorem B182403227 : Blo 574812 182403227 := bstep (se 1 (by rfl) ⟨136802420, by rfl⟩ : syracuseStep 182403227 = 273604841) B273604841
theorem B1951613 : Blo 574812 1951613 := bstep (se 3 (by rfl) ⟨365927, by rfl⟩ : syracuseStep 1951613 = 731855) B731855
theorem B121602151 : Blo 574812 121602151 := bstep (se 1 (by rfl) ⟨91201613, by rfl⟩ : syracuseStep 121602151 = 182403227) B182403227
theorem B1298591 : Blo 574812 1298591 := bstep (se 1 (by rfl) ⟨973943, by rfl⟩ : syracuseStep 1298591 = 1947887) B1947887
theorem B1301075 : Blo 574812 1301075 := bstep (se 1 (by rfl) ⟨975806, by rfl⟩ : syracuseStep 1301075 = 1951613) B1951613
theorem B648544805 : Blo 574812 648544805 := bstep (se 4 (by rfl) ⟨60801075, by rfl⟩ : syracuseStep 648544805 = 121602151) B121602151
theorem B865727 : Blo 574812 865727 := bstep (se 1 (by rfl) ⟨649295, by rfl⟩ : syracuseStep 865727 = 1298591) B1298591
theorem B867383 : Blo 574812 867383 := bstep (se 1 (by rfl) ⟨650537, by rfl⟩ : syracuseStep 867383 = 1301075) B1301075
theorem B577151 : Blo 574812 577151 := bstep (se 1 (by rfl) ⟨432863, by rfl⟩ : syracuseStep 577151 = 865727) B865727
theorem B578255 : Blo 574812 578255 := bstep (se 1 (by rfl) ⟨433691, by rfl⟩ : syracuseStep 578255 = 867383) B867383
theorem B432363203 : Blo 574812 432363203 := bstep (se 1 (by rfl) ⟨324272402, by rfl⟩ : syracuseStep 432363203 = 648544805) B648544805
theorem B288242135 : Blo 574812 288242135 := bstep (se 1 (by rfl) ⟨216181601, by rfl⟩ : syracuseStep 288242135 = 432363203) B432363203
theorem B192161423 : Blo 574812 192161423 := bstep (se 1 (by rfl) ⟨144121067, by rfl⟩ : syracuseStep 192161423 = 288242135) B288242135
theorem B128107615 : Blo 574812 128107615 := bstep (se 1 (by rfl) ⟨96080711, by rfl⟩ : syracuseStep 128107615 = 192161423) B192161423
theorem B170810153 : Blo 574812 170810153 := bstep (se 2 (by rfl) ⟨64053807, by rfl⟩ : syracuseStep 170810153 = 128107615) B128107615
theorem B113873435 : Blo 574812 113873435 := bstep (se 1 (by rfl) ⟨85405076, by rfl⟩ : syracuseStep 113873435 = 170810153) B170810153
theorem B75915623 : Blo 574812 75915623 := bstep (se 1 (by rfl) ⟨56936717, by rfl⟩ : syracuseStep 75915623 = 113873435) B113873435
theorem B50610415 : Blo 574812 50610415 := bstep (se 1 (by rfl) ⟨37957811, by rfl⟩ : syracuseStep 50610415 = 75915623) B75915623
theorem B67480553 : Blo 574812 67480553 := bstep (se 2 (by rfl) ⟨25305207, by rfl⟩ : syracuseStep 67480553 = 50610415) B50610415
theorem B44987035 : Blo 574812 44987035 := bstep (se 1 (by rfl) ⟨33740276, by rfl⟩ : syracuseStep 44987035 = 67480553) B67480553
theorem B59982713 : Blo 574812 59982713 := bstep (se 2 (by rfl) ⟨22493517, by rfl⟩ : syracuseStep 59982713 = 44987035) B44987035
theorem B39988475 : Blo 574812 39988475 := bstep (se 1 (by rfl) ⟨29991356, by rfl⟩ : syracuseStep 39988475 = 59982713) B59982713
theorem B26658983 : Blo 574812 26658983 := bstep (se 1 (by rfl) ⟨19994237, by rfl⟩ : syracuseStep 26658983 = 39988475) B39988475
theorem B71090621 : Blo 574812 71090621 := bstep (se 3 (by rfl) ⟨13329491, by rfl⟩ : syracuseStep 71090621 = 26658983) B26658983
theorem B47393747 : Blo 574812 47393747 := bstep (se 1 (by rfl) ⟨35545310, by rfl⟩ : syracuseStep 47393747 = 71090621) B71090621
theorem B31595831 : Blo 574812 31595831 := bstep (se 1 (by rfl) ⟨23696873, by rfl⟩ : syracuseStep 31595831 = 47393747) B47393747
theorem B21063887 : Blo 574812 21063887 := bstep (se 1 (by rfl) ⟨15797915, by rfl⟩ : syracuseStep 21063887 = 31595831) B31595831
theorem B14042591 : Blo 574812 14042591 := bstep (se 1 (by rfl) ⟨10531943, by rfl⟩ : syracuseStep 14042591 = 21063887) B21063887
theorem B9361727 : Blo 574812 9361727 := bstep (se 1 (by rfl) ⟨7021295, by rfl⟩ : syracuseStep 9361727 = 14042591) B14042591
theorem B6241151 : Blo 574812 6241151 := bstep (se 1 (by rfl) ⟨4680863, by rfl⟩ : syracuseStep 6241151 = 9361727) B9361727
theorem B4160767 : Blo 574812 4160767 := bstep (se 1 (by rfl) ⟨3120575, by rfl⟩ : syracuseStep 4160767 = 6241151) B6241151
theorem B5547689 : Blo 574812 5547689 := bstep (se 2 (by rfl) ⟨2080383, by rfl⟩ : syracuseStep 5547689 = 4160767) B4160767
theorem B3698459 : Blo 574812 3698459 := bstep (se 1 (by rfl) ⟨2773844, by rfl⟩ : syracuseStep 3698459 = 5547689) B5547689
theorem B2465639 : Blo 574812 2465639 := bstep (se 1 (by rfl) ⟨1849229, by rfl⟩ : syracuseStep 2465639 = 3698459) B3698459
theorem B1643759 : Blo 574812 1643759 := bstep (se 1 (by rfl) ⟨1232819, by rfl⟩ : syracuseStep 1643759 = 2465639) B2465639
theorem B1095839 : Blo 574812 1095839 := bstep (se 1 (by rfl) ⟨821879, by rfl⟩ : syracuseStep 1095839 = 1643759) B1643759
theorem B730559 : Blo 574812 730559 := bstep (se 1 (by rfl) ⟨547919, by rfl⟩ : syracuseStep 730559 = 1095839) B1095839
theorem B1948157 : Blo 574812 1948157 := bstep (se 3 (by rfl) ⟨365279, by rfl⟩ : syracuseStep 1948157 = 730559) B730559
theorem B1298771 : Blo 574812 1298771 := bstep (se 1 (by rfl) ⟨974078, by rfl⟩ : syracuseStep 1298771 = 1948157) B1948157
theorem B865847 : Blo 574812 865847 := bstep (se 1 (by rfl) ⟨649385, by rfl⟩ : syracuseStep 865847 = 1298771) B1298771
theorem B577231 : Blo 574812 577231 := bstep (se 1 (by rfl) ⟨432923, by rfl⟩ : syracuseStep 577231 = 865847) B865847

theorem C0 (j : ℕ) (h1 : 143703 ≤ j) (h2 : j ≤ 144402) : Blo 574812 (4 * j + 3) := by
  interval_cases j
  · exact B574815
  · exact B574819
  · exact B574823
  · exact B574827
  · exact B574831
  · exact B574835
  · exact B574839
  · exact B574843
  · exact B574847
  · exact B574851
  · exact B574855
  · exact B574859
  · exact B574863
  · exact B574867
  · exact B574871
  · exact B574875
  · exact B574879
  · exact B574883
  · exact B574887
  · exact B574891
  · exact B574895
  · exact B574899
  · exact B574903
  · exact B574907
  · exact B574911
  · exact B574915
  · exact B574919
  · exact B574923
  · exact B574927
  · exact B574931
  · exact B574935
  · exact B574939
  · exact B574943
  · exact B574947
  · exact B574951
  · exact B574955
  · exact B574959
  · exact B574963
  · exact B574967
  · exact B574971
  · exact B574975
  · exact B574979
  · exact B574983
  · exact B574987
  · exact B574991
  · exact B574995
  · exact B574999
  · exact B575003
  · exact B575007
  · exact B575011
  · exact B575015
  · exact B575019
  · exact B575023
  · exact B575027
  · exact B575031
  · exact B575035
  · exact B575039
  · exact B575043
  · exact B575047
  · exact B575051
  · exact B575055
  · exact B575059
  · exact B575063
  · exact B575067
  · exact B575071
  · exact B575075
  · exact B575079
  · exact B575083
  · exact B575087
  · exact B575091
  · exact B575095
  · exact B575099
  · exact B575103
  · exact B575107
  · exact B575111
  · exact B575115
  · exact B575119
  · exact B575123
  · exact B575127
  · exact B575131
  · exact B575135
  · exact B575139
  · exact B575143
  · exact B575147
  · exact B575151
  · exact B575155
  · exact B575159
  · exact B575163
  · exact B575167
  · exact B575171
  · exact B575175
  · exact B575179
  · exact B575183
  · exact B575187
  · exact B575191
  · exact B575195
  · exact B575199
  · exact B575203
  · exact B575207
  · exact B575211
  · exact B575215
  · exact B575219
  · exact B575223
  · exact B575227
  · exact B575231
  · exact B575235
  · exact B575239
  · exact B575243
  · exact B575247
  · exact B575251
  · exact B575255
  · exact B575259
  · exact B575263
  · exact B575267
  · exact B575271
  · exact B575275
  · exact B575279
  · exact B575283
  · exact B575287
  · exact B575291
  · exact B575295
  · exact B575299
  · exact B575303
  · exact B575307
  · exact B575311
  · exact B575315
  · exact B575319
  · exact B575323
  · exact B575327
  · exact B575331
  · exact B575335
  · exact B575339
  · exact B575343
  · exact B575347
  · exact B575351
  · exact B575355
  · exact B575359
  · exact B575363
  · exact B575367
  · exact B575371
  · exact B575375
  · exact B575379
  · exact B575383
  · exact B575387
  · exact B575391
  · exact B575395
  · exact B575399
  · exact B575403
  · exact B575407
  · exact B575411
  · exact B575415
  · exact B575419
  · exact B575423
  · exact B575427
  · exact B575431
  · exact B575435
  · exact B575439
  · exact B575443
  · exact B575447
  · exact B575451
  · exact B575455
  · exact B575459
  · exact B575463
  · exact B575467
  · exact B575471
  · exact B575475
  · exact B575479
  · exact B575483
  · exact B575487
  · exact B575491
  · exact B575495
  · exact B575499
  · exact B575503
  · exact B575507
  · exact B575511
  · exact B575515
  · exact B575519
  · exact B575523
  · exact B575527
  · exact B575531
  · exact B575535
  · exact B575539
  · exact B575543
  · exact B575547
  · exact B575551
  · exact B575555
  · exact B575559
  · exact B575563
  · exact B575567
  · exact B575571
  · exact B575575
  · exact B575579
  · exact B575583
  · exact B575587
  · exact B575591
  · exact B575595
  · exact B575599
  · exact B575603
  · exact B575607
  · exact B575611
  · exact B575615
  · exact B575619
  · exact B575623
  · exact B575627
  · exact B575631
  · exact B575635
  · exact B575639
  · exact B575643
  · exact B575647
  · exact B575651
  · exact B575655
  · exact B575659
  · exact B575663
  · exact B575667
  · exact B575671
  · exact B575675
  · exact B575679
  · exact B575683
  · exact B575687
  · exact B575691
  · exact B575695
  · exact B575699
  · exact B575703
  · exact B575707
  · exact B575711
  · exact B575715
  · exact B575719
  · exact B575723
  · exact B575727
  · exact B575731
  · exact B575735
  · exact B575739
  · exact B575743
  · exact B575747
  · exact B575751
  · exact B575755
  · exact B575759
  · exact B575763
  · exact B575767
  · exact B575771
  · exact B575775
  · exact B575779
  · exact B575783
  · exact B575787
  · exact B575791
  · exact B575795
  · exact B575799
  · exact B575803
  · exact B575807
  · exact B575811
  · exact B575815
  · exact B575819
  · exact B575823
  · exact B575827
  · exact B575831
  · exact B575835
  · exact B575839
  · exact B575843
  · exact B575847
  · exact B575851
  · exact B575855
  · exact B575859
  · exact B575863
  · exact B575867
  · exact B575871
  · exact B575875
  · exact B575879
  · exact B575883
  · exact B575887
  · exact B575891
  · exact B575895
  · exact B575899
  · exact B575903
  · exact B575907
  · exact B575911
  · exact B575915
  · exact B575919
  · exact B575923
  · exact B575927
  · exact B575931
  · exact B575935
  · exact B575939
  · exact B575943
  · exact B575947
  · exact B575951
  · exact B575955
  · exact B575959
  · exact B575963
  · exact B575967
  · exact B575971
  · exact B575975
  · exact B575979
  · exact B575983
  · exact B575987
  · exact B575991
  · exact B575995
  · exact B575999
  · exact B576003
  · exact B576007
  · exact B576011
  · exact B576015
  · exact B576019
  · exact B576023
  · exact B576027
  · exact B576031
  · exact B576035
  · exact B576039
  · exact B576043
  · exact B576047
  · exact B576051
  · exact B576055
  · exact B576059
  · exact B576063
  · exact B576067
  · exact B576071
  · exact B576075
  · exact B576079
  · exact B576083
  · exact B576087
  · exact B576091
  · exact B576095
  · exact B576099
  · exact B576103
  · exact B576107
  · exact B576111
  · exact B576115
  · exact B576119
  · exact B576123
  · exact B576127
  · exact B576131
  · exact B576135
  · exact B576139
  · exact B576143
  · exact B576147
  · exact B576151
  · exact B576155
  · exact B576159
  · exact B576163
  · exact B576167
  · exact B576171
  · exact B576175
  · exact B576179
  · exact B576183
  · exact B576187
  · exact B576191
  · exact B576195
  · exact B576199
  · exact B576203
  · exact B576207
  · exact B576211
  · exact B576215
  · exact B576219
  · exact B576223
  · exact B576227
  · exact B576231
  · exact B576235
  · exact B576239
  · exact B576243
  · exact B576247
  · exact B576251
  · exact B576255
  · exact B576259
  · exact B576263
  · exact B576267
  · exact B576271
  · exact B576275
  · exact B576279
  · exact B576283
  · exact B576287
  · exact B576291
  · exact B576295
  · exact B576299
  · exact B576303
  · exact B576307
  · exact B576311
  · exact B576315
  · exact B576319
  · exact B576323
  · exact B576327
  · exact B576331
  · exact B576335
  · exact B576339
  · exact B576343
  · exact B576347
  · exact B576351
  · exact B576355
  · exact B576359
  · exact B576363
  · exact B576367
  · exact B576371
  · exact B576375
  · exact B576379
  · exact B576383
  · exact B576387
  · exact B576391
  · exact B576395
  · exact B576399
  · exact B576403
  · exact B576407
  · exact B576411
  · exact B576415
  · exact B576419
  · exact B576423
  · exact B576427
  · exact B576431
  · exact B576435
  · exact B576439
  · exact B576443
  · exact B576447
  · exact B576451
  · exact B576455
  · exact B576459
  · exact B576463
  · exact B576467
  · exact B576471
  · exact B576475
  · exact B576479
  · exact B576483
  · exact B576487
  · exact B576491
  · exact B576495
  · exact B576499
  · exact B576503
  · exact B576507
  · exact B576511
  · exact B576515
  · exact B576519
  · exact B576523
  · exact B576527
  · exact B576531
  · exact B576535
  · exact B576539
  · exact B576543
  · exact B576547
  · exact B576551
  · exact B576555
  · exact B576559
  · exact B576563
  · exact B576567
  · exact B576571
  · exact B576575
  · exact B576579
  · exact B576583
  · exact B576587
  · exact B576591
  · exact B576595
  · exact B576599
  · exact B576603
  · exact B576607
  · exact B576611
  · exact B576615
  · exact B576619
  · exact B576623
  · exact B576627
  · exact B576631
  · exact B576635
  · exact B576639
  · exact B576643
  · exact B576647
  · exact B576651
  · exact B576655
  · exact B576659
  · exact B576663
  · exact B576667
  · exact B576671
  · exact B576675
  · exact B576679
  · exact B576683
  · exact B576687
  · exact B576691
  · exact B576695
  · exact B576699
  · exact B576703
  · exact B576707
  · exact B576711
  · exact B576715
  · exact B576719
  · exact B576723
  · exact B576727
  · exact B576731
  · exact B576735
  · exact B576739
  · exact B576743
  · exact B576747
  · exact B576751
  · exact B576755
  · exact B576759
  · exact B576763
  · exact B576767
  · exact B576771
  · exact B576775
  · exact B576779
  · exact B576783
  · exact B576787
  · exact B576791
  · exact B576795
  · exact B576799
  · exact B576803
  · exact B576807
  · exact B576811
  · exact B576815
  · exact B576819
  · exact B576823
  · exact B576827
  · exact B576831
  · exact B576835
  · exact B576839
  · exact B576843
  · exact B576847
  · exact B576851
  · exact B576855
  · exact B576859
  · exact B576863
  · exact B576867
  · exact B576871
  · exact B576875
  · exact B576879
  · exact B576883
  · exact B576887
  · exact B576891
  · exact B576895
  · exact B576899
  · exact B576903
  · exact B576907
  · exact B576911
  · exact B576915
  · exact B576919
  · exact B576923
  · exact B576927
  · exact B576931
  · exact B576935
  · exact B576939
  · exact B576943
  · exact B576947
  · exact B576951
  · exact B576955
  · exact B576959
  · exact B576963
  · exact B576967
  · exact B576971
  · exact B576975
  · exact B576979
  · exact B576983
  · exact B576987
  · exact B576991
  · exact B576995
  · exact B576999
  · exact B577003
  · exact B577007
  · exact B577011
  · exact B577015
  · exact B577019
  · exact B577023
  · exact B577027
  · exact B577031
  · exact B577035
  · exact B577039
  · exact B577043
  · exact B577047
  · exact B577051
  · exact B577055
  · exact B577059
  · exact B577063
  · exact B577067
  · exact B577071
  · exact B577075
  · exact B577079
  · exact B577083
  · exact B577087
  · exact B577091
  · exact B577095
  · exact B577099
  · exact B577103
  · exact B577107
  · exact B577111
  · exact B577115
  · exact B577119
  · exact B577123
  · exact B577127
  · exact B577131
  · exact B577135
  · exact B577139
  · exact B577143
  · exact B577147
  · exact B577151
  · exact B577155
  · exact B577159
  · exact B577163
  · exact B577167
  · exact B577171
  · exact B577175
  · exact B577179
  · exact B577183
  · exact B577187
  · exact B577191
  · exact B577195
  · exact B577199
  · exact B577203
  · exact B577207
  · exact B577211
  · exact B577215
  · exact B577219
  · exact B577223
  · exact B577227
  · exact B577231
  · exact B577235
  · exact B577239
  · exact B577243
  · exact B577247
  · exact B577251
  · exact B577255
  · exact B577259
  · exact B577263
  · exact B577267
  · exact B577271
  · exact B577275
  · exact B577279
  · exact B577283
  · exact B577287
  · exact B577291
  · exact B577295
  · exact B577299
  · exact B577303
  · exact B577307
  · exact B577311
  · exact B577315
  · exact B577319
  · exact B577323
  · exact B577327
  · exact B577331
  · exact B577335
  · exact B577339
  · exact B577343
  · exact B577347
  · exact B577351
  · exact B577355
  · exact B577359
  · exact B577363
  · exact B577367
  · exact B577371
  · exact B577375
  · exact B577379
  · exact B577383
  · exact B577387
  · exact B577391
  · exact B577395
  · exact B577399
  · exact B577403
  · exact B577407
  · exact B577411
  · exact B577415
  · exact B577419
  · exact B577423
  · exact B577427
  · exact B577431
  · exact B577435
  · exact B577439
  · exact B577443
  · exact B577447
  · exact B577451
  · exact B577455
  · exact B577459
  · exact B577463
  · exact B577467
  · exact B577471
  · exact B577475
  · exact B577479
  · exact B577483
  · exact B577487
  · exact B577491
  · exact B577495
  · exact B577499
  · exact B577503
  · exact B577507
  · exact B577511
  · exact B577515
  · exact B577519
  · exact B577523
  · exact B577527
  · exact B577531
  · exact B577535
  · exact B577539
  · exact B577543
  · exact B577547
  · exact B577551
  · exact B577555
  · exact B577559
  · exact B577563
  · exact B577567
  · exact B577571
  · exact B577575
  · exact B577579
  · exact B577583
  · exact B577587
  · exact B577591
  · exact B577595
  · exact B577599
  · exact B577603
  · exact B577607
  · exact B577611

theorem C1 (j : ℕ) (h1 : 144403 ≤ j) (h2 : j ≤ 144702) : Blo 574812 (4 * j + 3) := by
  interval_cases j
  · exact B577615
  · exact B577619
  · exact B577623
  · exact B577627
  · exact B577631
  · exact B577635
  · exact B577639
  · exact B577643
  · exact B577647
  · exact B577651
  · exact B577655
  · exact B577659
  · exact B577663
  · exact B577667
  · exact B577671
  · exact B577675
  · exact B577679
  · exact B577683
  · exact B577687
  · exact B577691
  · exact B577695
  · exact B577699
  · exact B577703
  · exact B577707
  · exact B577711
  · exact B577715
  · exact B577719
  · exact B577723
  · exact B577727
  · exact B577731
  · exact B577735
  · exact B577739
  · exact B577743
  · exact B577747
  · exact B577751
  · exact B577755
  · exact B577759
  · exact B577763
  · exact B577767
  · exact B577771
  · exact B577775
  · exact B577779
  · exact B577783
  · exact B577787
  · exact B577791
  · exact B577795
  · exact B577799
  · exact B577803
  · exact B577807
  · exact B577811
  · exact B577815
  · exact B577819
  · exact B577823
  · exact B577827
  · exact B577831
  · exact B577835
  · exact B577839
  · exact B577843
  · exact B577847
  · exact B577851
  · exact B577855
  · exact B577859
  · exact B577863
  · exact B577867
  · exact B577871
  · exact B577875
  · exact B577879
  · exact B577883
  · exact B577887
  · exact B577891
  · exact B577895
  · exact B577899
  · exact B577903
  · exact B577907
  · exact B577911
  · exact B577915
  · exact B577919
  · exact B577923
  · exact B577927
  · exact B577931
  · exact B577935
  · exact B577939
  · exact B577943
  · exact B577947
  · exact B577951
  · exact B577955
  · exact B577959
  · exact B577963
  · exact B577967
  · exact B577971
  · exact B577975
  · exact B577979
  · exact B577983
  · exact B577987
  · exact B577991
  · exact B577995
  · exact B577999
  · exact B578003
  · exact B578007
  · exact B578011
  · exact B578015
  · exact B578019
  · exact B578023
  · exact B578027
  · exact B578031
  · exact B578035
  · exact B578039
  · exact B578043
  · exact B578047
  · exact B578051
  · exact B578055
  · exact B578059
  · exact B578063
  · exact B578067
  · exact B578071
  · exact B578075
  · exact B578079
  · exact B578083
  · exact B578087
  · exact B578091
  · exact B578095
  · exact B578099
  · exact B578103
  · exact B578107
  · exact B578111
  · exact B578115
  · exact B578119
  · exact B578123
  · exact B578127
  · exact B578131
  · exact B578135
  · exact B578139
  · exact B578143
  · exact B578147
  · exact B578151
  · exact B578155
  · exact B578159
  · exact B578163
  · exact B578167
  · exact B578171
  · exact B578175
  · exact B578179
  · exact B578183
  · exact B578187
  · exact B578191
  · exact B578195
  · exact B578199
  · exact B578203
  · exact B578207
  · exact B578211
  · exact B578215
  · exact B578219
  · exact B578223
  · exact B578227
  · exact B578231
  · exact B578235
  · exact B578239
  · exact B578243
  · exact B578247
  · exact B578251
  · exact B578255
  · exact B578259
  · exact B578263
  · exact B578267
  · exact B578271
  · exact B578275
  · exact B578279
  · exact B578283
  · exact B578287
  · exact B578291
  · exact B578295
  · exact B578299
  · exact B578303
  · exact B578307
  · exact B578311
  · exact B578315
  · exact B578319
  · exact B578323
  · exact B578327
  · exact B578331
  · exact B578335
  · exact B578339
  · exact B578343
  · exact B578347
  · exact B578351
  · exact B578355
  · exact B578359
  · exact B578363
  · exact B578367
  · exact B578371
  · exact B578375
  · exact B578379
  · exact B578383
  · exact B578387
  · exact B578391
  · exact B578395
  · exact B578399
  · exact B578403
  · exact B578407
  · exact B578411
  · exact B578415
  · exact B578419
  · exact B578423
  · exact B578427
  · exact B578431
  · exact B578435
  · exact B578439
  · exact B578443
  · exact B578447
  · exact B578451
  · exact B578455
  · exact B578459
  · exact B578463
  · exact B578467
  · exact B578471
  · exact B578475
  · exact B578479
  · exact B578483
  · exact B578487
  · exact B578491
  · exact B578495
  · exact B578499
  · exact B578503
  · exact B578507
  · exact B578511
  · exact B578515
  · exact B578519
  · exact B578523
  · exact B578527
  · exact B578531
  · exact B578535
  · exact B578539
  · exact B578543
  · exact B578547
  · exact B578551
  · exact B578555
  · exact B578559
  · exact B578563
  · exact B578567
  · exact B578571
  · exact B578575
  · exact B578579
  · exact B578583
  · exact B578587
  · exact B578591
  · exact B578595
  · exact B578599
  · exact B578603
  · exact B578607
  · exact B578611
  · exact B578615
  · exact B578619
  · exact B578623
  · exact B578627
  · exact B578631
  · exact B578635
  · exact B578639
  · exact B578643
  · exact B578647
  · exact B578651
  · exact B578655
  · exact B578659
  · exact B578663
  · exact B578667
  · exact B578671
  · exact B578675
  · exact B578679
  · exact B578683
  · exact B578687
  · exact B578691
  · exact B578695
  · exact B578699
  · exact B578703
  · exact B578707
  · exact B578711
  · exact B578715
  · exact B578719
  · exact B578723
  · exact B578727
  · exact B578731
  · exact B578735
  · exact B578739
  · exact B578743
  · exact B578747
  · exact B578751
  · exact B578755
  · exact B578759
  · exact B578763
  · exact B578767
  · exact B578771
  · exact B578775
  · exact B578779
  · exact B578783
  · exact B578787
  · exact B578791
  · exact B578795
  · exact B578799
  · exact B578803
  · exact B578807
  · exact B578811

theorem solution (m : ℕ) (hlo : 574812 ≤ m) (hhi : m ≤ 578812) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 143703 ≤ j := by omega
    have hj2 : j ≤ 144702 := by omega
    have hb : Blo 574812 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 144403 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
