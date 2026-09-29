-- Prove2me | solution 1 for syracuse_descends_range_401768_405768
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:47:48.911976+00:00
-- url     : https://prove2.me/submissions/5f7cec19-b55a-4f32-9d96-69964ff49813

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


theorem B983125 : Blo 401768 983125 := bbase (se 8 (by rfl) ⟨5760, by rfl⟩ : syracuseStep 983125 = 11521) (by norm_num)
theorem B3277205 : Blo 401768 3277205 := bbase (se 6 (by rfl) ⟨76809, by rfl⟩ : syracuseStep 3277205 = 153619) (by norm_num)
theorem B819821 : Blo 401768 819821 := bbase (se 3 (by rfl) ⟨153716, by rfl⟩ : syracuseStep 819821 = 307433) (by norm_num)
theorem B459497 : Blo 401768 459497 := bbase (se 2 (by rfl) ⟨172311, by rfl⟩ : syracuseStep 459497 = 344623) (by norm_num)
theorem B1147765 : Blo 401768 1147765 := bbase (se 5 (by rfl) ⟨53801, by rfl⟩ : syracuseStep 1147765 = 107603) (by norm_num)
theorem B1147925 : Blo 401768 1147925 := bbase (se 6 (by rfl) ⟨26904, by rfl⟩ : syracuseStep 1147925 = 53809) (by norm_num)
theorem B820469 : Blo 401768 820469 := bbase (se 5 (by rfl) ⟨38459, by rfl⟩ : syracuseStep 820469 = 76919) (by norm_num)
theorem B525569 : Blo 401768 525569 := bbase (se 2 (by rfl) ⟨197088, by rfl⟩ : syracuseStep 525569 = 394177) (by norm_num)
theorem B1148165 : Blo 401768 1148165 := bbase (se 4 (by rfl) ⟨107640, by rfl⟩ : syracuseStep 1148165 = 215281) (by norm_num)
theorem B1017157 : Blo 401768 1017157 := bbase (se 4 (by rfl) ⟨95358, by rfl⟩ : syracuseStep 1017157 = 190717) (by norm_num)
theorem B1377605 : Blo 401768 1377605 := bbase (se 4 (by rfl) ⟨129150, by rfl⟩ : syracuseStep 1377605 = 258301) (by norm_num)
theorem B1017269 : Blo 401768 1017269 := bbase (se 5 (by rfl) ⟨47684, by rfl⟩ : syracuseStep 1017269 = 95369) (by norm_num)
theorem B1148357 : Blo 401768 1148357 := bbase (se 4 (by rfl) ⟨107658, by rfl⟩ : syracuseStep 1148357 = 215317) (by norm_num)
theorem B984565 : Blo 401768 984565 := bbase (se 5 (by rfl) ⟨46151, by rfl⟩ : syracuseStep 984565 = 92303) (by norm_num)
theorem B1017461 : Blo 401768 1017461 := bbase (se 5 (by rfl) ⟨47693, by rfl⟩ : syracuseStep 1017461 = 95387) (by norm_num)
theorem B886477 : Blo 401768 886477 := bbase (se 3 (by rfl) ⟨166214, by rfl⟩ : syracuseStep 886477 = 332429) (by norm_num)
theorem B591733 : Blo 401768 591733 := bbase (se 5 (by rfl) ⟨27737, by rfl⟩ : syracuseStep 591733 = 55475) (by norm_num)
theorem B1017805 : Blo 401768 1017805 := bbase (se 3 (by rfl) ⟨190838, by rfl⟩ : syracuseStep 1017805 = 381677) (by norm_num)
theorem B1017917 : Blo 401768 1017917 := bbase (se 3 (by rfl) ⟨190859, by rfl⟩ : syracuseStep 1017917 = 381719) (by norm_num)
theorem B1018109 : Blo 401768 1018109 := bbase (se 3 (by rfl) ⟨190895, by rfl⟩ : syracuseStep 1018109 = 381791) (by norm_num)
theorem B985421 : Blo 401768 985421 := bbase (se 3 (by rfl) ⟨184766, by rfl⟩ : syracuseStep 985421 = 369533) (by norm_num)
theorem B1935701 : Blo 401768 1935701 := bbase (se 10 (by rfl) ⟨2835, by rfl⟩ : syracuseStep 1935701 = 5671) (by norm_num)
theorem B1149349 : Blo 401768 1149349 := bbase (se 4 (by rfl) ⟨107751, by rfl⟩ : syracuseStep 1149349 = 215503) (by norm_num)
theorem B1018453 : Blo 401768 1018453 := bbase (se 8 (by rfl) ⟨5967, by rfl⟩ : syracuseStep 1018453 = 11935) (by norm_num)
theorem B1018565 : Blo 401768 1018565 := bbase (se 4 (by rfl) ⟨95490, by rfl⟩ : syracuseStep 1018565 = 190981) (by norm_num)
theorem B428885 : Blo 401768 428885 := bbase (se 9 (by rfl) ⟨1256, by rfl⟩ : syracuseStep 428885 = 2513) (by norm_num)
theorem B1018757 : Blo 401768 1018757 := bbase (se 4 (by rfl) ⟨95508, by rfl⟩ : syracuseStep 1018757 = 191017) (by norm_num)
theorem B920693 : Blo 401768 920693 := bbase (se 5 (by rfl) ⟨43157, by rfl⟩ : syracuseStep 920693 = 86315) (by norm_num)
theorem B429229 : Blo 401768 429229 := bbase (se 3 (by rfl) ⟨80480, by rfl⟩ : syracuseStep 429229 = 160961) (by norm_num)
theorem B429233 : Blo 401768 429233 := bbase (se 2 (by rfl) ⟨160962, by rfl⟩ : syracuseStep 429233 = 321925) (by norm_num)
theorem B1019101 : Blo 401768 1019101 := bbase (se 3 (by rfl) ⟨191081, by rfl⟩ : syracuseStep 1019101 = 382163) (by norm_num)
theorem B658661 : Blo 401768 658661 := bbase (se 4 (by rfl) ⟨61749, by rfl⟩ : syracuseStep 658661 = 123499) (by norm_num)
theorem B1019213 : Blo 401768 1019213 := bbase (se 3 (by rfl) ⟨191102, by rfl⟩ : syracuseStep 1019213 = 382205) (by norm_num)
theorem B2985461 : Blo 401768 2985461 := bbase (se 5 (by rfl) ⟨139943, by rfl⟩ : syracuseStep 2985461 = 279887) (by norm_num)
theorem B1150453 : Blo 401768 1150453 := bbase (se 5 (by rfl) ⟨53927, by rfl⟩ : syracuseStep 1150453 = 107855) (by norm_num)
theorem B2035205 : Blo 401768 2035205 := bbase (se 4 (by rfl) ⟨190800, by rfl⟩ : syracuseStep 2035205 = 381601) (by norm_num)
theorem B1019405 : Blo 401768 1019405 := bbase (se 3 (by rfl) ⟨191138, by rfl⟩ : syracuseStep 1019405 = 382277) (by norm_num)
theorem B429797 : Blo 401768 429797 := bbase (se 4 (by rfl) ⟨40293, by rfl⟩ : syracuseStep 429797 = 80587) (by norm_num)
theorem B986941 : Blo 401768 986941 := bbase (se 3 (by rfl) ⟨185051, by rfl⟩ : syracuseStep 986941 = 370103) (by norm_num)
theorem B1019749 : Blo 401768 1019749 := bbase (se 4 (by rfl) ⟨95601, by rfl⟩ : syracuseStep 1019749 = 191203) (by norm_num)
theorem B2297717 : Blo 401768 2297717 := bbase (se 5 (by rfl) ⟨107705, by rfl⟩ : syracuseStep 2297717 = 215411) (by norm_num)
theorem B429985 : Blo 401768 429985 := bbase (se 2 (by rfl) ⟨161244, by rfl⟩ : syracuseStep 429985 = 322489) (by norm_num)
theorem B1937317 : Blo 401768 1937317 := bbase (se 4 (by rfl) ⟨181623, by rfl⟩ : syracuseStep 1937317 = 363247) (by norm_num)
theorem B1019861 : Blo 401768 1019861 := bbase (se 7 (by rfl) ⟨11951, by rfl⟩ : syracuseStep 1019861 = 23903) (by norm_num)
theorem B1020053 : Blo 401768 1020053 := bbase (se 6 (by rfl) ⟨23907, by rfl⟩ : syracuseStep 1020053 = 47815) (by norm_num)
theorem B1020397 : Blo 401768 1020397 := bbase (se 3 (by rfl) ⟨191324, by rfl⟩ : syracuseStep 1020397 = 382649) (by norm_num)
theorem B692749 : Blo 401768 692749 := bbase (se 3 (by rfl) ⟨129890, by rfl⟩ : syracuseStep 692749 = 259781) (by norm_num)
theorem B1020509 : Blo 401768 1020509 := bbase (se 3 (by rfl) ⟨191345, by rfl⟩ : syracuseStep 1020509 = 382691) (by norm_num)
theorem B430805 : Blo 401768 430805 := bbase (se 7 (by rfl) ⟨5048, by rfl⟩ : syracuseStep 430805 = 10097) (by norm_num)
theorem B725773 : Blo 401768 725773 := bbase (se 3 (by rfl) ⟨136082, by rfl⟩ : syracuseStep 725773 = 272165) (by norm_num)
theorem B2036501 : Blo 401768 2036501 := bbase (se 6 (by rfl) ⟨47730, by rfl⟩ : syracuseStep 2036501 = 95461) (by norm_num)
theorem B1020701 : Blo 401768 1020701 := bbase (se 3 (by rfl) ⟨191381, by rfl⟩ : syracuseStep 1020701 = 382763) (by norm_num)
theorem B725845 : Blo 401768 725845 := bbase (se 9 (by rfl) ⟨2126, by rfl⟩ : syracuseStep 725845 = 4253) (by norm_num)
theorem B1151957 : Blo 401768 1151957 := bbase (se 7 (by rfl) ⟨13499, by rfl⟩ : syracuseStep 1151957 = 26999) (by norm_num)
theorem B3052565 : Blo 401768 3052565 := bbase (se 6 (by rfl) ⟨71544, by rfl⟩ : syracuseStep 3052565 = 143089) (by norm_num)
theorem B2298901 : Blo 401768 2298901 := bbase (se 6 (by rfl) ⟨53880, by rfl⟩ : syracuseStep 2298901 = 107761) (by norm_num)
theorem B726077 : Blo 401768 726077 := bbase (se 3 (by rfl) ⟨136139, by rfl⟩ : syracuseStep 726077 = 272279) (by norm_num)
theorem B922709 : Blo 401768 922709 := bbase (se 8 (by rfl) ⟨5406, by rfl⟩ : syracuseStep 922709 = 10813) (by norm_num)
theorem B1021045 : Blo 401768 1021045 := bbase (se 5 (by rfl) ⟨47861, by rfl⟩ : syracuseStep 1021045 = 95723) (by norm_num)
theorem B431245 : Blo 401768 431245 := bbase (se 3 (by rfl) ⟨80858, by rfl⟩ : syracuseStep 431245 = 161717) (by norm_num)
theorem B431249 : Blo 401768 431249 := bbase (se 2 (by rfl) ⟨161718, by rfl⟩ : syracuseStep 431249 = 323437) (by norm_num)
theorem B1021157 : Blo 401768 1021157 := bbase (se 4 (by rfl) ⟨95733, by rfl⟩ : syracuseStep 1021157 = 191467) (by norm_num)
theorem B431497 : Blo 401768 431497 := bbase (se 2 (by rfl) ⟨161811, by rfl⟩ : syracuseStep 431497 = 323623) (by norm_num)
theorem B3446165 : Blo 401768 3446165 := bbase (se 6 (by rfl) ⟨80769, by rfl⟩ : syracuseStep 3446165 = 161539) (by norm_num)
theorem B1021349 : Blo 401768 1021349 := bbase (se 4 (by rfl) ⟨95751, by rfl⟩ : syracuseStep 1021349 = 191503) (by norm_num)
theorem B2594261 : Blo 401768 2594261 := bbase (se 7 (by rfl) ⟨30401, by rfl⟩ : syracuseStep 2594261 = 60803) (by norm_num)
theorem B693749 : Blo 401768 693749 := bbase (se 5 (by rfl) ⟨32519, by rfl⟩ : syracuseStep 693749 = 65039) (by norm_num)
theorem B1054237 : Blo 401768 1054237 := bbase (se 3 (by rfl) ⟨197669, by rfl⟩ : syracuseStep 1054237 = 395339) (by norm_num)
theorem B1021693 : Blo 401768 1021693 := bbase (se 3 (by rfl) ⟨191567, by rfl⟩ : syracuseStep 1021693 = 383135) (by norm_num)
theorem B431929 : Blo 401768 431929 := bbase (se 2 (by rfl) ⟨161973, by rfl⟩ : syracuseStep 431929 = 323947) (by norm_num)
theorem B726869 : Blo 401768 726869 := bbase (se 9 (by rfl) ⟨2129, by rfl⟩ : syracuseStep 726869 = 4259) (by norm_num)
theorem B1021805 : Blo 401768 1021805 := bbase (se 3 (by rfl) ⟨191588, by rfl⟩ : syracuseStep 1021805 = 383177) (by norm_num)
theorem B432001 : Blo 401768 432001 := bbase (se 2 (by rfl) ⟨162000, by rfl⟩ : syracuseStep 432001 = 324001) (by norm_num)
theorem B1841093 : Blo 401768 1841093 := bbase (se 4 (by rfl) ⟨172602, by rfl⟩ : syracuseStep 1841093 = 345205) (by norm_num)
theorem B13277141 : Blo 401768 13277141 := bbase (se 7 (by rfl) ⟨155591, by rfl⟩ : syracuseStep 13277141 = 311183) (by norm_num)
theorem B2037797 : Blo 401768 2037797 := bbase (se 4 (by rfl) ⟨191043, by rfl⟩ : syracuseStep 2037797 = 382087) (by norm_num)
theorem B1021997 : Blo 401768 1021997 := bbase (se 3 (by rfl) ⟨191624, by rfl⟩ : syracuseStep 1021997 = 383249) (by norm_num)
theorem B727157 : Blo 401768 727157 := bbase (se 5 (by rfl) ⟨34085, by rfl⟩ : syracuseStep 727157 = 68171) (by norm_num)
theorem B727229 : Blo 401768 727229 := bbase (se 3 (by rfl) ⟨136355, by rfl⟩ : syracuseStep 727229 = 272711) (by norm_num)
theorem B432373 : Blo 401768 432373 := bbase (se 5 (by rfl) ⟨20267, by rfl⟩ : syracuseStep 432373 = 40535) (by norm_num)
theorem B1022341 : Blo 401768 1022341 := bbase (se 4 (by rfl) ⟨95844, by rfl⟩ : syracuseStep 1022341 = 191689) (by norm_num)
theorem B1382789 : Blo 401768 1382789 := bbase (se 4 (by rfl) ⟨129636, by rfl⟩ : syracuseStep 1382789 = 259273) (by norm_num)
theorem B1022453 : Blo 401768 1022453 := bbase (se 5 (by rfl) ⟨47927, by rfl⟩ : syracuseStep 1022453 = 95855) (by norm_num)
theorem B1153541 : Blo 401768 1153541 := bbase (se 4 (by rfl) ⟨108144, by rfl⟩ : syracuseStep 1153541 = 216289) (by norm_num)
theorem B858637 : Blo 401768 858637 := bbase (se 3 (by rfl) ⟨160994, by rfl⟩ : syracuseStep 858637 = 321989) (by norm_num)
theorem B4659797 : Blo 401768 4659797 := bbase (se 8 (by rfl) ⟨27303, by rfl⟩ : syracuseStep 4659797 = 54607) (by norm_num)
theorem B432749 : Blo 401768 432749 := bbase (se 3 (by rfl) ⟨81140, by rfl⟩ : syracuseStep 432749 = 162281) (by norm_num)
theorem B858757 : Blo 401768 858757 := bbase (se 4 (by rfl) ⟨80508, by rfl⟩ : syracuseStep 858757 = 161017) (by norm_num)
theorem B3480245 : Blo 401768 3480245 := bbase (se 5 (by rfl) ⟨163136, by rfl⟩ : syracuseStep 3480245 = 326273) (by norm_num)
theorem B1022645 : Blo 401768 1022645 := bbase (se 5 (by rfl) ⟨47936, by rfl⟩ : syracuseStep 1022645 = 95873) (by norm_num)
theorem B432821 : Blo 401768 432821 := bbase (se 5 (by rfl) ⟨20288, by rfl⟩ : syracuseStep 432821 = 40577) (by norm_num)
theorem B1481509 : Blo 401768 1481509 := bbase (se 4 (by rfl) ⟨138891, by rfl⟩ : syracuseStep 1481509 = 277783) (by norm_num)
theorem B924461 : Blo 401768 924461 := bbase (se 3 (by rfl) ⟨173336, by rfl⟩ : syracuseStep 924461 = 346673) (by norm_num)
theorem B433009 : Blo 401768 433009 := bbase (se 2 (by rfl) ⟨162378, by rfl⟩ : syracuseStep 433009 = 324757) (by norm_num)
theorem B859013 : Blo 401768 859013 := bbase (se 4 (by rfl) ⟨80532, by rfl⟩ : syracuseStep 859013 = 161065) (by norm_num)
theorem B2300885 : Blo 401768 2300885 := bbase (se 7 (by rfl) ⟨26963, by rfl⟩ : syracuseStep 2300885 = 53927) (by norm_num)
theorem B1022989 : Blo 401768 1022989 := bbase (se 3 (by rfl) ⟨191810, by rfl⟩ : syracuseStep 1022989 = 383621) (by norm_num)
theorem B433193 : Blo 401768 433193 := bbase (se 2 (by rfl) ⟨162447, by rfl⟩ : syracuseStep 433193 = 324895) (by norm_num)
theorem B1023101 : Blo 401768 1023101 := bbase (se 3 (by rfl) ⟨191831, by rfl⟩ : syracuseStep 1023101 = 383663) (by norm_num)
theorem B1154213 : Blo 401768 1154213 := bbase (se 4 (by rfl) ⟨108207, by rfl⟩ : syracuseStep 1154213 = 216415) (by norm_num)
theorem B2039093 : Blo 401768 2039093 := bbase (se 5 (by rfl) ⟨95582, by rfl⟩ : syracuseStep 2039093 = 191165) (by norm_num)
theorem B1023293 : Blo 401768 1023293 := bbase (se 3 (by rfl) ⟨191867, by rfl⟩ : syracuseStep 1023293 = 383735) (by norm_num)
theorem B2334197 : Blo 401768 2334197 := bbase (se 5 (by rfl) ⟨109415, by rfl⟩ : syracuseStep 2334197 = 218831) (by norm_num)
theorem B1121861 : Blo 401768 1121861 := bbase (se 4 (by rfl) ⟨105174, by rfl⟩ : syracuseStep 1121861 = 210349) (by norm_num)
theorem B7347797 : Blo 401768 7347797 := bbase (se 8 (by rfl) ⟨43053, by rfl⟩ : syracuseStep 7347797 = 86107) (by norm_num)
theorem B1154645 : Blo 401768 1154645 := bbase (se 8 (by rfl) ⟨6765, by rfl⟩ : syracuseStep 1154645 = 13531) (by norm_num)
theorem B1023637 : Blo 401768 1023637 := bbase (se 6 (by rfl) ⟨23991, by rfl⟩ : syracuseStep 1023637 = 47983) (by norm_num)
theorem B1449701 : Blo 401768 1449701 := bbase (se 4 (by rfl) ⟨135909, by rfl⟩ : syracuseStep 1449701 = 271819) (by norm_num)
theorem B859901 : Blo 401768 859901 := bbase (se 3 (by rfl) ⟨161231, by rfl⟩ : syracuseStep 859901 = 322463) (by norm_num)
theorem B1023749 : Blo 401768 1023749 := bbase (se 4 (by rfl) ⟨95976, by rfl⟩ : syracuseStep 1023749 = 191953) (by norm_num)
theorem B499469 : Blo 401768 499469 := bbase (se 3 (by rfl) ⟨93650, by rfl⟩ : syracuseStep 499469 = 187301) (by norm_num)
theorem B1023941 : Blo 401768 1023941 := bbase (se 4 (by rfl) ⟨95994, by rfl⟩ : syracuseStep 1023941 = 191989) (by norm_num)
theorem B860141 : Blo 401768 860141 := bbase (se 3 (by rfl) ⟨161276, by rfl⟩ : syracuseStep 860141 = 322553) (by norm_num)
theorem B1024285 : Blo 401768 1024285 := bbase (se 3 (by rfl) ⟨192053, by rfl⟩ : syracuseStep 1024285 = 384107) (by norm_num)
theorem B3449141 : Blo 401768 3449141 := bbase (se 5 (by rfl) ⟨161678, by rfl⟩ : syracuseStep 3449141 = 323357) (by norm_num)
theorem B1155397 : Blo 401768 1155397 := bbase (se 4 (by rfl) ⟨108318, by rfl⟩ : syracuseStep 1155397 = 216637) (by norm_num)
theorem B1024397 : Blo 401768 1024397 := bbase (se 3 (by rfl) ⟨192074, by rfl⟩ : syracuseStep 1024397 = 384149) (by norm_num)
theorem B860645 : Blo 401768 860645 := bbase (se 4 (by rfl) ⟨80685, by rfl⟩ : syracuseStep 860645 = 161371) (by norm_num)
theorem B860653 : Blo 401768 860653 := bbase (se 3 (by rfl) ⟨161372, by rfl⟩ : syracuseStep 860653 = 322745) (by norm_num)
theorem B2040389 : Blo 401768 2040389 := bbase (se 4 (by rfl) ⟨191286, by rfl⟩ : syracuseStep 2040389 = 382573) (by norm_num)
theorem B1024589 : Blo 401768 1024589 := bbase (se 3 (by rfl) ⟨192110, by rfl⟩ : syracuseStep 1024589 = 384221) (by norm_num)
theorem B1843829 : Blo 401768 1843829 := bbase (se 5 (by rfl) ⟨86429, by rfl⟩ : syracuseStep 1843829 = 172859) (by norm_num)
theorem B1450853 : Blo 401768 1450853 := bbase (se 4 (by rfl) ⟨136017, by rfl⟩ : syracuseStep 1450853 = 272035) (by norm_num)
theorem B1024933 : Blo 401768 1024933 := bbase (se 4 (by rfl) ⟨96087, by rfl⟩ : syracuseStep 1024933 = 192175) (by norm_num)
theorem B4137941 : Blo 401768 4137941 := bbase (se 7 (by rfl) ⟨48491, by rfl⟩ : syracuseStep 4137941 = 96983) (by norm_num)
theorem B762853 : Blo 401768 762853 := bbase (se 4 (by rfl) ⟨71517, by rfl⟩ : syracuseStep 762853 = 143035) (by norm_num)
theorem B1025045 : Blo 401768 1025045 := bbase (se 6 (by rfl) ⟨24024, by rfl⟩ : syracuseStep 1025045 = 48049) (by norm_num)
theorem B2303093 : Blo 401768 2303093 := bbase (se 5 (by rfl) ⟨107957, by rfl⟩ : syracuseStep 2303093 = 215915) (by norm_num)
theorem B763013 : Blo 401768 763013 := bbase (se 4 (by rfl) ⟨71532, by rfl⟩ : syracuseStep 763013 = 143065) (by norm_num)
theorem B828613 : Blo 401768 828613 := bbase (se 4 (by rfl) ⟨77682, by rfl⟩ : syracuseStep 828613 = 155365) (by norm_num)
theorem B1025237 : Blo 401768 1025237 := bbase (se 7 (by rfl) ⟨12014, by rfl⟩ : syracuseStep 1025237 = 24029) (by norm_num)
theorem B763157 : Blo 401768 763157 := bbase (se 6 (by rfl) ⟨17886, by rfl⟩ : syracuseStep 763157 = 35773) (by norm_num)
theorem B959941 : Blo 401768 959941 := bbase (se 4 (by rfl) ⟨89994, by rfl⟩ : syracuseStep 959941 = 179989) (by norm_num)
theorem B1025581 : Blo 401768 1025581 := bbase (se 3 (by rfl) ⟨192296, by rfl⟩ : syracuseStep 1025581 = 384593) (by norm_num)
theorem B763445 : Blo 401768 763445 := bbase (se 5 (by rfl) ⟨35786, by rfl⟩ : syracuseStep 763445 = 71573) (by norm_num)
theorem B861781 : Blo 401768 861781 := bbase (se 8 (by rfl) ⟨5049, by rfl⟩ : syracuseStep 861781 = 10099) (by norm_num)
theorem B1025693 : Blo 401768 1025693 := bbase (se 3 (by rfl) ⟨192317, by rfl⟩ : syracuseStep 1025693 = 384635) (by norm_num)
theorem B763597 : Blo 401768 763597 := bbase (se 3 (by rfl) ⟨143174, by rfl⟩ : syracuseStep 763597 = 286349) (by norm_num)
theorem B1287893 : Blo 401768 1287893 := bbase (se 7 (by rfl) ⟨15092, by rfl⟩ : syracuseStep 1287893 = 30185) (by norm_num)
theorem B468725 : Blo 401768 468725 := bbase (se 5 (by rfl) ⟨21971, by rfl⟩ : syracuseStep 468725 = 43943) (by norm_num)
theorem B2041685 : Blo 401768 2041685 := bbase (se 9 (by rfl) ⟨5981, by rfl⟩ : syracuseStep 2041685 = 11963) (by norm_num)
theorem B1025885 : Blo 401768 1025885 := bbase (se 3 (by rfl) ⟨192353, by rfl⟩ : syracuseStep 1025885 = 384707) (by norm_num)
theorem B1845125 : Blo 401768 1845125 := bbase (se 4 (by rfl) ⟨172980, by rfl⟩ : syracuseStep 1845125 = 345961) (by norm_num)
theorem B862157 : Blo 401768 862157 := bbase (se 3 (by rfl) ⟨161654, by rfl⟩ : syracuseStep 862157 = 323309) (by norm_num)
theorem B763901 : Blo 401768 763901 := bbase (se 3 (by rfl) ⟨143231, by rfl⟩ : syracuseStep 763901 = 286463) (by norm_num)
theorem B1943621 : Blo 401768 1943621 := bbase (se 4 (by rfl) ⟨182214, by rfl⟩ : syracuseStep 1943621 = 364429) (by norm_num)
theorem B1026229 : Blo 401768 1026229 := bbase (se 5 (by rfl) ⟨48104, by rfl⟩ : syracuseStep 1026229 = 96209) (by norm_num)
theorem B1026341 : Blo 401768 1026341 := bbase (se 4 (by rfl) ⟨96219, by rfl⟩ : syracuseStep 1026341 = 192439) (by norm_num)
theorem B436553 : Blo 401768 436553 := bbase (se 2 (by rfl) ⟨163707, by rfl⟩ : syracuseStep 436553 = 327415) (by norm_num)
theorem B1026533 : Blo 401768 1026533 := bbase (se 4 (by rfl) ⟨96237, by rfl⟩ : syracuseStep 1026533 = 192475) (by norm_num)
theorem B1452613 : Blo 401768 1452613 := bbase (se 4 (by rfl) ⟨136182, by rfl⟩ : syracuseStep 1452613 = 272365) (by norm_num)
theorem B1092197 : Blo 401768 1092197 := bbase (se 4 (by rfl) ⟨102393, by rfl⟩ : syracuseStep 1092197 = 204787) (by norm_num)
theorem B764653 : Blo 401768 764653 := bbase (se 3 (by rfl) ⟨143372, by rfl⟩ : syracuseStep 764653 = 286745) (by norm_num)
theorem B1026877 : Blo 401768 1026877 := bbase (se 3 (by rfl) ⟨192539, by rfl⟩ : syracuseStep 1026877 = 385079) (by norm_num)
theorem B2796373 : Blo 401768 2796373 := bbase (se 9 (by rfl) ⟨8192, by rfl⟩ : syracuseStep 2796373 = 16385) (by norm_num)
theorem B764797 : Blo 401768 764797 := bbase (se 3 (by rfl) ⟨143399, by rfl⟩ : syracuseStep 764797 = 286799) (by norm_num)
theorem B1026989 : Blo 401768 1026989 := bbase (se 3 (by rfl) ⟨192560, by rfl⟩ : syracuseStep 1026989 = 385121) (by norm_num)
theorem B1092629 : Blo 401768 1092629 := bbase (se 6 (by rfl) ⟨25608, by rfl⟩ : syracuseStep 1092629 = 51217) (by norm_num)
theorem B764957 : Blo 401768 764957 := bbase (se 3 (by rfl) ⟨143429, by rfl⟩ : syracuseStep 764957 = 286859) (by norm_num)
theorem B2042981 : Blo 401768 2042981 := bbase (se 4 (by rfl) ⟨191529, by rfl⟩ : syracuseStep 2042981 = 383059) (by norm_num)
theorem B765101 : Blo 401768 765101 := bbase (se 3 (by rfl) ⟨143456, by rfl⟩ : syracuseStep 765101 = 286913) (by norm_num)
theorem B2174357 : Blo 401768 2174357 := bbase (se 6 (by rfl) ⟨50961, by rfl⟩ : syracuseStep 2174357 = 101923) (by norm_num)
theorem B765389 : Blo 401768 765389 := bbase (se 3 (by rfl) ⟨143510, by rfl⟩ : syracuseStep 765389 = 287021) (by norm_num)
theorem B1093157 : Blo 401768 1093157 := bbase (se 4 (by rfl) ⟨102483, by rfl⟩ : syracuseStep 1093157 = 204967) (by norm_num)
theorem B1453621 : Blo 401768 1453621 := bbase (se 5 (by rfl) ⟨68138, by rfl⟩ : syracuseStep 1453621 = 136277) (by norm_num)
theorem B863797 : Blo 401768 863797 := bbase (se 5 (by rfl) ⟨40490, by rfl⟩ : syracuseStep 863797 = 80981) (by norm_num)
theorem B765541 : Blo 401768 765541 := bbase (se 4 (by rfl) ⟨71769, by rfl⟩ : syracuseStep 765541 = 143539) (by norm_num)
theorem B4140725 : Blo 401768 4140725 := bbase (se 5 (by rfl) ⟨194096, by rfl⟩ : syracuseStep 4140725 = 388193) (by norm_num)
theorem B438053 : Blo 401768 438053 := bbase (se 4 (by rfl) ⟨41067, by rfl⟩ : syracuseStep 438053 = 82135) (by norm_num)
theorem B765845 : Blo 401768 765845 := bbase (se 6 (by rfl) ⟨17949, by rfl⟩ : syracuseStep 765845 = 35899) (by norm_num)
theorem B405433 : Blo 401768 405433 := bbase (se 2 (by rfl) ⟨152037, by rfl⟩ : syracuseStep 405433 = 304075) (by norm_num)
theorem B1847461 : Blo 401768 1847461 := bbase (se 4 (by rfl) ⟨173199, by rfl⟩ : syracuseStep 1847461 = 346399) (by norm_num)
theorem B1356101 : Blo 401768 1356101 := bbase (se 4 (by rfl) ⟨127134, by rfl⟩ : syracuseStep 1356101 = 254269) (by norm_num)
theorem B2044277 : Blo 401768 2044277 := bbase (se 5 (by rfl) ⟨95825, by rfl⟩ : syracuseStep 2044277 = 191651) (by norm_num)
theorem B864685 : Blo 401768 864685 := bbase (se 3 (by rfl) ⟨162128, by rfl⟩ : syracuseStep 864685 = 324257) (by norm_num)
theorem B1290725 : Blo 401768 1290725 := bbase (se 4 (by rfl) ⟨121005, by rfl⟩ : syracuseStep 1290725 = 242011) (by norm_num)
theorem B602669 : Blo 401768 602669 := bbase (se 3 (by rfl) ⟨113000, by rfl⟩ : syracuseStep 602669 = 226001) (by norm_num)
theorem B438841 : Blo 401768 438841 := bbase (se 2 (by rfl) ⟨164565, by rfl⟩ : syracuseStep 438841 = 329131) (by norm_num)
theorem B602693 : Blo 401768 602693 := bbase (se 4 (by rfl) ⟨56502, by rfl⟩ : syracuseStep 602693 = 113005) (by norm_num)
theorem B602717 : Blo 401768 602717 := bbase (se 3 (by rfl) ⟨113009, by rfl⟩ : syracuseStep 602717 = 226019) (by norm_num)
theorem B602741 : Blo 401768 602741 := bbase (se 5 (by rfl) ⟨28253, by rfl⟩ : syracuseStep 602741 = 56507) (by norm_num)
theorem B3060341 : Blo 401768 3060341 := bbase (se 5 (by rfl) ⟨143453, by rfl⟩ : syracuseStep 3060341 = 286907) (by norm_num)
theorem B766597 : Blo 401768 766597 := bbase (se 4 (by rfl) ⟨71868, by rfl⟩ : syracuseStep 766597 = 143737) (by norm_num)
theorem B602765 : Blo 401768 602765 := bbase (se 3 (by rfl) ⟨113018, by rfl⟩ : syracuseStep 602765 = 226037) (by norm_num)
theorem B602789 : Blo 401768 602789 := bbase (se 4 (by rfl) ⟨56511, by rfl⟩ : syracuseStep 602789 = 113023) (by norm_num)
theorem B602813 : Blo 401768 602813 := bbase (se 3 (by rfl) ⟨113027, by rfl⟩ : syracuseStep 602813 = 226055) (by norm_num)
theorem B602837 : Blo 401768 602837 := bbase (se 7 (by rfl) ⟨7064, by rfl⟩ : syracuseStep 602837 = 14129) (by norm_num)
theorem B602861 : Blo 401768 602861 := bbase (se 3 (by rfl) ⟨113036, by rfl⟩ : syracuseStep 602861 = 226073) (by norm_num)
theorem B1356533 : Blo 401768 1356533 := bbase (se 5 (by rfl) ⟨63587, by rfl⟩ : syracuseStep 1356533 = 127175) (by norm_num)
theorem B602885 : Blo 401768 602885 := bbase (se 4 (by rfl) ⟨56520, by rfl⟩ : syracuseStep 602885 = 113041) (by norm_num)
theorem B766741 : Blo 401768 766741 := bbase (se 6 (by rfl) ⟨17970, by rfl⟩ : syracuseStep 766741 = 35941) (by norm_num)
theorem B1946389 : Blo 401768 1946389 := bbase (se 6 (by rfl) ⟨45618, by rfl⟩ : syracuseStep 1946389 = 91237) (by norm_num)
theorem B602909 : Blo 401768 602909 := bbase (se 3 (by rfl) ⟨113045, by rfl⟩ : syracuseStep 602909 = 226091) (by norm_num)
theorem B602933 : Blo 401768 602933 := bbase (se 5 (by rfl) ⟨28262, by rfl⟩ : syracuseStep 602933 = 56525) (by norm_num)
theorem B602957 : Blo 401768 602957 := bbase (se 3 (by rfl) ⟨113054, by rfl⟩ : syracuseStep 602957 = 226109) (by norm_num)
theorem B602981 : Blo 401768 602981 := bbase (se 4 (by rfl) ⟨56529, by rfl⟩ : syracuseStep 602981 = 113059) (by norm_num)
theorem B603005 : Blo 401768 603005 := bbase (se 3 (by rfl) ⟨113063, by rfl⟩ : syracuseStep 603005 = 226127) (by norm_num)
theorem B603029 : Blo 401768 603029 := bbase (se 6 (by rfl) ⟨14133, by rfl⟩ : syracuseStep 603029 = 28267) (by norm_num)
theorem B865181 : Blo 401768 865181 := bbase (se 3 (by rfl) ⟨162221, by rfl⟩ : syracuseStep 865181 = 324443) (by norm_num)
theorem B1160101 : Blo 401768 1160101 := bbase (se 4 (by rfl) ⟨108759, by rfl⟩ : syracuseStep 1160101 = 217519) (by norm_num)
theorem B603053 : Blo 401768 603053 := bbase (se 3 (by rfl) ⟨113072, by rfl⟩ : syracuseStep 603053 = 226145) (by norm_num)
theorem B766901 : Blo 401768 766901 := bbase (se 5 (by rfl) ⟨35948, by rfl⟩ : syracuseStep 766901 = 71897) (by norm_num)
theorem B603077 : Blo 401768 603077 := bbase (se 4 (by rfl) ⟨56538, by rfl⟩ : syracuseStep 603077 = 113077) (by norm_num)
theorem B603101 : Blo 401768 603101 := bbase (se 3 (by rfl) ⟨113081, by rfl⟩ : syracuseStep 603101 = 226163) (by norm_num)
theorem B603125 : Blo 401768 603125 := bbase (se 5 (by rfl) ⟨28271, by rfl⟩ : syracuseStep 603125 = 56543) (by norm_num)
theorem B832501 : Blo 401768 832501 := bbase (se 5 (by rfl) ⟨39023, by rfl⟩ : syracuseStep 832501 = 78047) (by norm_num)
theorem B603149 : Blo 401768 603149 := bbase (se 3 (by rfl) ⟨113090, by rfl⟩ : syracuseStep 603149 = 226181) (by norm_num)
theorem B603173 : Blo 401768 603173 := bbase (se 4 (by rfl) ⟨56547, by rfl⟩ : syracuseStep 603173 = 113095) (by norm_num)
theorem B603197 : Blo 401768 603197 := bbase (se 3 (by rfl) ⟨113099, by rfl⟩ : syracuseStep 603197 = 226199) (by norm_num)
theorem B767045 : Blo 401768 767045 := bbase (se 4 (by rfl) ⟨71910, by rfl⟩ : syracuseStep 767045 = 143821) (by norm_num)
theorem B603221 : Blo 401768 603221 := bbase (se 8 (by rfl) ⟨3534, by rfl⟩ : syracuseStep 603221 = 7069) (by norm_num)
theorem B603245 : Blo 401768 603245 := bbase (se 3 (by rfl) ⟨113108, by rfl⟩ : syracuseStep 603245 = 226217) (by norm_num)
theorem B603269 : Blo 401768 603269 := bbase (se 4 (by rfl) ⟨56556, by rfl⟩ : syracuseStep 603269 = 113113) (by norm_num)
theorem B603293 : Blo 401768 603293 := bbase (se 3 (by rfl) ⟨113117, by rfl⟩ : syracuseStep 603293 = 226235) (by norm_num)
theorem B1356965 : Blo 401768 1356965 := bbase (se 4 (by rfl) ⟨127215, by rfl⟩ : syracuseStep 1356965 = 254431) (by norm_num)
theorem B603317 : Blo 401768 603317 := bbase (se 5 (by rfl) ⟨28280, by rfl⟩ : syracuseStep 603317 = 56561) (by norm_num)
theorem B603341 : Blo 401768 603341 := bbase (se 3 (by rfl) ⟨113126, by rfl⟩ : syracuseStep 603341 = 226253) (by norm_num)
theorem B603365 : Blo 401768 603365 := bbase (se 4 (by rfl) ⟨56565, by rfl⟩ : syracuseStep 603365 = 113131) (by norm_num)
theorem B603389 : Blo 401768 603389 := bbase (se 3 (by rfl) ⟨113135, by rfl⟩ : syracuseStep 603389 = 226271) (by norm_num)
theorem B603413 : Blo 401768 603413 := bbase (se 6 (by rfl) ⟨14142, by rfl⟩ : syracuseStep 603413 = 28285) (by norm_num)
theorem B603437 : Blo 401768 603437 := bbase (se 3 (by rfl) ⟨113144, by rfl⟩ : syracuseStep 603437 = 226289) (by norm_num)
theorem B603461 : Blo 401768 603461 := bbase (se 4 (by rfl) ⟨56574, by rfl⟩ : syracuseStep 603461 = 113149) (by norm_num)
theorem B603485 : Blo 401768 603485 := bbase (se 3 (by rfl) ⟨113153, by rfl⟩ : syracuseStep 603485 = 226307) (by norm_num)
theorem B1291621 : Blo 401768 1291621 := bbase (se 4 (by rfl) ⟨121089, by rfl⟩ : syracuseStep 1291621 = 242179) (by norm_num)
theorem B767333 : Blo 401768 767333 := bbase (se 4 (by rfl) ⟨71937, by rfl⟩ : syracuseStep 767333 = 143875) (by norm_num)
theorem B603509 : Blo 401768 603509 := bbase (se 5 (by rfl) ⟨28289, by rfl⟩ : syracuseStep 603509 = 56579) (by norm_num)
theorem B603533 : Blo 401768 603533 := bbase (se 3 (by rfl) ⟨113162, by rfl⟩ : syracuseStep 603533 = 226325) (by norm_num)
theorem B603557 : Blo 401768 603557 := bbase (se 4 (by rfl) ⟨56583, by rfl⟩ : syracuseStep 603557 = 113167) (by norm_num)
theorem B1717685 : Blo 401768 1717685 := bbase (se 5 (by rfl) ⟨80516, by rfl⟩ : syracuseStep 1717685 = 161033) (by norm_num)
theorem B603581 : Blo 401768 603581 := bbase (se 3 (by rfl) ⟨113171, by rfl⟩ : syracuseStep 603581 = 226343) (by norm_num)
theorem B603605 : Blo 401768 603605 := bbase (se 7 (by rfl) ⟨7073, by rfl⟩ : syracuseStep 603605 = 14147) (by norm_num)
theorem B603629 : Blo 401768 603629 := bbase (se 3 (by rfl) ⟨113180, by rfl⟩ : syracuseStep 603629 = 226361) (by norm_num)
theorem B2635253 : Blo 401768 2635253 := bbase (se 5 (by rfl) ⟨123527, by rfl⟩ : syracuseStep 2635253 = 247055) (by norm_num)
theorem B767485 : Blo 401768 767485 := bbase (se 3 (by rfl) ⟨143903, by rfl⟩ : syracuseStep 767485 = 287807) (by norm_num)
theorem B603653 : Blo 401768 603653 := bbase (se 4 (by rfl) ⟨56592, by rfl⟩ : syracuseStep 603653 = 113185) (by norm_num)
theorem B603677 : Blo 401768 603677 := bbase (se 3 (by rfl) ⟨113189, by rfl⟩ : syracuseStep 603677 = 226379) (by norm_num)
theorem B603701 : Blo 401768 603701 := bbase (se 5 (by rfl) ⟨28298, by rfl⟩ : syracuseStep 603701 = 56597) (by norm_num)
theorem B603725 : Blo 401768 603725 := bbase (se 3 (by rfl) ⟨113198, by rfl⟩ : syracuseStep 603725 = 226397) (by norm_num)
theorem B1357397 : Blo 401768 1357397 := bbase (se 8 (by rfl) ⟨7953, by rfl⟩ : syracuseStep 1357397 = 15907) (by norm_num)
theorem B603749 : Blo 401768 603749 := bbase (se 4 (by rfl) ⟨56601, by rfl⟩ : syracuseStep 603749 = 113203) (by norm_num)
theorem B603773 : Blo 401768 603773 := bbase (se 3 (by rfl) ⟨113207, by rfl⟩ : syracuseStep 603773 = 226415) (by norm_num)
theorem B2045573 : Blo 401768 2045573 := bbase (se 4 (by rfl) ⟨191772, by rfl⟩ : syracuseStep 2045573 = 383545) (by norm_num)
theorem B603797 : Blo 401768 603797 := bbase (se 6 (by rfl) ⟨14151, by rfl⟩ : syracuseStep 603797 = 28303) (by norm_num)
theorem B603821 : Blo 401768 603821 := bbase (se 3 (by rfl) ⟨113216, by rfl⟩ : syracuseStep 603821 = 226433) (by norm_num)
theorem B603845 : Blo 401768 603845 := bbase (se 4 (by rfl) ⟨56610, by rfl⟩ : syracuseStep 603845 = 113221) (by norm_num)
theorem B603869 : Blo 401768 603869 := bbase (se 3 (by rfl) ⟨113225, by rfl⟩ : syracuseStep 603869 = 226451) (by norm_num)
theorem B603893 : Blo 401768 603893 := bbase (se 5 (by rfl) ⟨28307, by rfl⟩ : syracuseStep 603893 = 56615) (by norm_num)
theorem B866045 : Blo 401768 866045 := bbase (se 3 (by rfl) ⟨162383, by rfl⟩ : syracuseStep 866045 = 324767) (by norm_num)
theorem B603917 : Blo 401768 603917 := bbase (se 3 (by rfl) ⟨113234, by rfl⟩ : syracuseStep 603917 = 226469) (by norm_num)
theorem B603941 : Blo 401768 603941 := bbase (se 4 (by rfl) ⟨56619, by rfl⟩ : syracuseStep 603941 = 113239) (by norm_num)
theorem B767789 : Blo 401768 767789 := bbase (se 3 (by rfl) ⟨143960, by rfl⟩ : syracuseStep 767789 = 287921) (by norm_num)
theorem B603965 : Blo 401768 603965 := bbase (se 3 (by rfl) ⟨113243, by rfl⟩ : syracuseStep 603965 = 226487) (by norm_num)
theorem B603989 : Blo 401768 603989 := bbase (se 9 (by rfl) ⟨1769, by rfl⟩ : syracuseStep 603989 = 3539) (by norm_num)
theorem B604013 : Blo 401768 604013 := bbase (se 3 (by rfl) ⟨113252, by rfl⟩ : syracuseStep 604013 = 226505) (by norm_num)
theorem B2176885 : Blo 401768 2176885 := bbase (se 5 (by rfl) ⟨102041, by rfl⟩ : syracuseStep 2176885 = 204083) (by norm_num)
theorem B604037 : Blo 401768 604037 := bbase (se 4 (by rfl) ⟨56628, by rfl⟩ : syracuseStep 604037 = 113257) (by norm_num)
theorem B866189 : Blo 401768 866189 := bbase (se 3 (by rfl) ⟨162410, by rfl⟩ : syracuseStep 866189 = 324821) (by norm_num)
theorem B604061 : Blo 401768 604061 := bbase (se 3 (by rfl) ⟨113261, by rfl⟩ : syracuseStep 604061 = 226523) (by norm_num)
theorem B604085 : Blo 401768 604085 := bbase (se 5 (by rfl) ⟨28316, by rfl⟩ : syracuseStep 604085 = 56633) (by norm_num)
theorem B604109 : Blo 401768 604109 := bbase (se 3 (by rfl) ⟨113270, by rfl⟩ : syracuseStep 604109 = 226541) (by norm_num)
theorem B604133 : Blo 401768 604133 := bbase (se 4 (by rfl) ⟨56637, by rfl⟩ : syracuseStep 604133 = 113275) (by norm_num)
theorem B604157 : Blo 401768 604157 := bbase (se 3 (by rfl) ⟨113279, by rfl⟩ : syracuseStep 604157 = 226559) (by norm_num)
theorem B1357829 : Blo 401768 1357829 := bbase (se 4 (by rfl) ⟨127296, by rfl⟩ : syracuseStep 1357829 = 254593) (by norm_num)
theorem B604181 : Blo 401768 604181 := bbase (se 6 (by rfl) ⟨14160, by rfl⟩ : syracuseStep 604181 = 28321) (by norm_num)
theorem B604205 : Blo 401768 604205 := bbase (se 3 (by rfl) ⟨113288, by rfl⟩ : syracuseStep 604205 = 226577) (by norm_num)
theorem B604229 : Blo 401768 604229 := bbase (se 4 (by rfl) ⟨56646, by rfl⟩ : syracuseStep 604229 = 113293) (by norm_num)
theorem B5158997 : Blo 401768 5158997 := bbase (se 8 (by rfl) ⟨30228, by rfl⟩ : syracuseStep 5158997 = 60457) (by norm_num)
theorem B604253 : Blo 401768 604253 := bbase (se 3 (by rfl) ⟨113297, by rfl⟩ : syracuseStep 604253 = 226595) (by norm_num)
theorem B604277 : Blo 401768 604277 := bbase (se 5 (by rfl) ⟨28325, by rfl⟩ : syracuseStep 604277 = 56651) (by norm_num)
theorem B1554565 : Blo 401768 1554565 := bbase (se 4 (by rfl) ⟨145740, by rfl⟩ : syracuseStep 1554565 = 291481) (by norm_num)
theorem B604301 : Blo 401768 604301 := bbase (se 3 (by rfl) ⟨113306, by rfl⟩ : syracuseStep 604301 = 226613) (by norm_num)
theorem B604325 : Blo 401768 604325 := bbase (se 4 (by rfl) ⟨56655, by rfl⟩ : syracuseStep 604325 = 113311) (by norm_num)
theorem B407737 : Blo 401768 407737 := bbase (se 2 (by rfl) ⟨152901, by rfl⟩ : syracuseStep 407737 = 305803) (by norm_num)
theorem B604349 : Blo 401768 604349 := bbase (se 3 (by rfl) ⟨113315, by rfl⟩ : syracuseStep 604349 = 226631) (by norm_num)
theorem B604373 : Blo 401768 604373 := bbase (se 7 (by rfl) ⟨7082, by rfl⟩ : syracuseStep 604373 = 14165) (by norm_num)
theorem B604397 : Blo 401768 604397 := bbase (se 3 (by rfl) ⟨113324, by rfl⟩ : syracuseStep 604397 = 226649) (by norm_num)
theorem B1095925 : Blo 401768 1095925 := bbase (se 5 (by rfl) ⟨51371, by rfl⟩ : syracuseStep 1095925 = 102743) (by norm_num)
theorem B604421 : Blo 401768 604421 := bbase (se 4 (by rfl) ⟨56664, by rfl⟩ : syracuseStep 604421 = 113329) (by norm_num)
theorem B735517 : Blo 401768 735517 := bbase (se 3 (by rfl) ⟨137909, by rfl⟩ : syracuseStep 735517 = 275819) (by norm_num)
theorem B604445 : Blo 401768 604445 := bbase (se 3 (by rfl) ⟨113333, by rfl⟩ : syracuseStep 604445 = 226667) (by norm_num)
theorem B604469 : Blo 401768 604469 := bbase (se 5 (by rfl) ⟨28334, by rfl⟩ : syracuseStep 604469 = 56669) (by norm_num)
theorem B604493 : Blo 401768 604493 := bbase (se 3 (by rfl) ⟨113342, by rfl⟩ : syracuseStep 604493 = 226685) (by norm_num)
theorem B604517 : Blo 401768 604517 := bbase (se 4 (by rfl) ⟨56673, by rfl⟩ : syracuseStep 604517 = 113347) (by norm_num)
theorem B604541 : Blo 401768 604541 := bbase (se 3 (by rfl) ⟨113351, by rfl⟩ : syracuseStep 604541 = 226703) (by norm_num)
theorem B604565 : Blo 401768 604565 := bbase (se 6 (by rfl) ⟨14169, by rfl⟩ : syracuseStep 604565 = 28339) (by norm_num)
theorem B604589 : Blo 401768 604589 := bbase (se 3 (by rfl) ⟨113360, by rfl⟩ : syracuseStep 604589 = 226721) (by norm_num)
theorem B1358261 : Blo 401768 1358261 := bbase (se 5 (by rfl) ⟨63668, by rfl⟩ : syracuseStep 1358261 = 127337) (by norm_num)
theorem B604613 : Blo 401768 604613 := bbase (se 4 (by rfl) ⟨56682, by rfl⟩ : syracuseStep 604613 = 113365) (by norm_num)
theorem B408017 : Blo 401768 408017 := bbase (se 2 (by rfl) ⟨153006, by rfl⟩ : syracuseStep 408017 = 306013) (by norm_num)
theorem B604637 : Blo 401768 604637 := bbase (se 3 (by rfl) ⟨113369, by rfl⟩ : syracuseStep 604637 = 226739) (by norm_num)
theorem B604661 : Blo 401768 604661 := bbase (se 5 (by rfl) ⟨28343, by rfl⟩ : syracuseStep 604661 = 56687) (by norm_num)
theorem B604685 : Blo 401768 604685 := bbase (se 3 (by rfl) ⟨113378, by rfl⟩ : syracuseStep 604685 = 226757) (by norm_num)
theorem B768541 : Blo 401768 768541 := bbase (se 3 (by rfl) ⟨144101, by rfl⟩ : syracuseStep 768541 = 288203) (by norm_num)
theorem B604709 : Blo 401768 604709 := bbase (se 4 (by rfl) ⟨56691, by rfl⟩ : syracuseStep 604709 = 113383) (by norm_num)
theorem B1096229 : Blo 401768 1096229 := bbase (se 4 (by rfl) ⟨102771, by rfl⟩ : syracuseStep 1096229 = 205543) (by norm_num)
theorem B604733 : Blo 401768 604733 := bbase (se 3 (by rfl) ⟨113387, by rfl⟩ : syracuseStep 604733 = 226775) (by norm_num)
theorem B604757 : Blo 401768 604757 := bbase (se 8 (by rfl) ⟨3543, by rfl⟩ : syracuseStep 604757 = 7087) (by norm_num)
theorem B604781 : Blo 401768 604781 := bbase (se 3 (by rfl) ⟨113396, by rfl⟩ : syracuseStep 604781 = 226793) (by norm_num)
theorem B604805 : Blo 401768 604805 := bbase (se 4 (by rfl) ⟨56700, by rfl⟩ : syracuseStep 604805 = 113401) (by norm_num)
theorem B604829 : Blo 401768 604829 := bbase (se 3 (by rfl) ⟨113405, by rfl⟩ : syracuseStep 604829 = 226811) (by norm_num)
theorem B768685 : Blo 401768 768685 := bbase (se 3 (by rfl) ⟨144128, by rfl⟩ : syracuseStep 768685 = 288257) (by norm_num)
theorem B604853 : Blo 401768 604853 := bbase (se 5 (by rfl) ⟨28352, by rfl⟩ : syracuseStep 604853 = 56705) (by norm_num)
theorem B604877 : Blo 401768 604877 := bbase (se 3 (by rfl) ⟨113414, by rfl⟩ : syracuseStep 604877 = 226829) (by norm_num)
theorem B604901 : Blo 401768 604901 := bbase (se 4 (by rfl) ⟨56709, by rfl⟩ : syracuseStep 604901 = 113419) (by norm_num)
theorem B604925 : Blo 401768 604925 := bbase (se 3 (by rfl) ⟨113423, by rfl⟩ : syracuseStep 604925 = 226847) (by norm_num)
theorem B604949 : Blo 401768 604949 := bbase (se 6 (by rfl) ⟨14178, by rfl⟩ : syracuseStep 604949 = 28357) (by norm_num)
theorem B572197 : Blo 401768 572197 := bbase (se 4 (by rfl) ⟨53643, by rfl⟩ : syracuseStep 572197 = 107287) (by norm_num)
theorem B604973 : Blo 401768 604973 := bbase (se 3 (by rfl) ⟨113432, by rfl⟩ : syracuseStep 604973 = 226865) (by norm_num)
theorem B604997 : Blo 401768 604997 := bbase (se 4 (by rfl) ⟨56718, by rfl⟩ : syracuseStep 604997 = 113437) (by norm_num)
theorem B768845 : Blo 401768 768845 := bbase (se 3 (by rfl) ⟨144158, by rfl⟩ : syracuseStep 768845 = 288317) (by norm_num)
theorem B605021 : Blo 401768 605021 := bbase (se 3 (by rfl) ⟨113441, by rfl⟩ : syracuseStep 605021 = 226883) (by norm_num)
theorem B1358693 : Blo 401768 1358693 := bbase (se 4 (by rfl) ⟨127377, by rfl⟩ : syracuseStep 1358693 = 254755) (by norm_num)
theorem B605045 : Blo 401768 605045 := bbase (se 5 (by rfl) ⟨28361, by rfl⟩ : syracuseStep 605045 = 56723) (by norm_num)
theorem B605069 : Blo 401768 605069 := bbase (se 3 (by rfl) ⟨113450, by rfl⟩ : syracuseStep 605069 = 226901) (by norm_num)
theorem B2046869 : Blo 401768 2046869 := bbase (se 6 (by rfl) ⟨47973, by rfl⟩ : syracuseStep 2046869 = 95947) (by norm_num)
theorem B1031077 : Blo 401768 1031077 := bbase (se 4 (by rfl) ⟨96663, by rfl⟩ : syracuseStep 1031077 = 193327) (by norm_num)
theorem B605093 : Blo 401768 605093 := bbase (se 4 (by rfl) ⟨56727, by rfl⟩ : syracuseStep 605093 = 113455) (by norm_num)
theorem B605117 : Blo 401768 605117 := bbase (se 3 (by rfl) ⟨113459, by rfl⟩ : syracuseStep 605117 = 226919) (by norm_num)
theorem B605141 : Blo 401768 605141 := bbase (se 7 (by rfl) ⟨7091, by rfl⟩ : syracuseStep 605141 = 14183) (by norm_num)
theorem B768989 : Blo 401768 768989 := bbase (se 3 (by rfl) ⟨144185, by rfl⟩ : syracuseStep 768989 = 288371) (by norm_num)
theorem B605165 : Blo 401768 605165 := bbase (se 3 (by rfl) ⟨113468, by rfl⟩ : syracuseStep 605165 = 226937) (by norm_num)
theorem B965621 : Blo 401768 965621 := bbase (se 5 (by rfl) ⟨45263, by rfl⟩ : syracuseStep 965621 = 90527) (by norm_num)
theorem B605189 : Blo 401768 605189 := bbase (se 4 (by rfl) ⟨56736, by rfl⟩ : syracuseStep 605189 = 113473) (by norm_num)
theorem B408601 : Blo 401768 408601 := bbase (se 2 (by rfl) ⟨153225, by rfl⟩ : syracuseStep 408601 = 306451) (by norm_num)
theorem B605213 : Blo 401768 605213 := bbase (se 3 (by rfl) ⟨113477, by rfl⟩ : syracuseStep 605213 = 226955) (by norm_num)
theorem B605237 : Blo 401768 605237 := bbase (se 5 (by rfl) ⟨28370, by rfl⟩ : syracuseStep 605237 = 56741) (by norm_num)
theorem B605261 : Blo 401768 605261 := bbase (se 3 (by rfl) ⟨113486, by rfl⟩ : syracuseStep 605261 = 226973) (by norm_num)
theorem B605285 : Blo 401768 605285 := bbase (se 4 (by rfl) ⟨56745, by rfl⟩ : syracuseStep 605285 = 113491) (by norm_num)
theorem B605309 : Blo 401768 605309 := bbase (se 3 (by rfl) ⟨113495, by rfl⟩ : syracuseStep 605309 = 226991) (by norm_num)
theorem B605333 : Blo 401768 605333 := bbase (se 6 (by rfl) ⟨14187, by rfl⟩ : syracuseStep 605333 = 28375) (by norm_num)
theorem B1719461 : Blo 401768 1719461 := bbase (se 4 (by rfl) ⟨161199, by rfl⟩ : syracuseStep 1719461 = 322399) (by norm_num)
theorem B605357 : Blo 401768 605357 := bbase (se 3 (by rfl) ⟨113504, by rfl⟩ : syracuseStep 605357 = 227009) (by norm_num)
theorem B605381 : Blo 401768 605381 := bbase (se 4 (by rfl) ⟨56754, by rfl⟩ : syracuseStep 605381 = 113509) (by norm_num)
theorem B605405 : Blo 401768 605405 := bbase (se 3 (by rfl) ⟨113513, by rfl⟩ : syracuseStep 605405 = 227027) (by norm_num)
theorem B605429 : Blo 401768 605429 := bbase (se 5 (by rfl) ⟨28379, by rfl⟩ : syracuseStep 605429 = 56759) (by norm_num)
theorem B769277 : Blo 401768 769277 := bbase (se 3 (by rfl) ⟨144239, by rfl⟩ : syracuseStep 769277 = 288479) (by norm_num)
theorem B605453 : Blo 401768 605453 := bbase (se 3 (by rfl) ⟨113522, by rfl⟩ : syracuseStep 605453 = 227045) (by norm_num)
theorem B1359125 : Blo 401768 1359125 := bbase (se 6 (by rfl) ⟨31854, by rfl⟩ : syracuseStep 1359125 = 63709) (by norm_num)
theorem B605477 : Blo 401768 605477 := bbase (se 4 (by rfl) ⟨56763, by rfl⟩ : syracuseStep 605477 = 113527) (by norm_num)
theorem B605501 : Blo 401768 605501 := bbase (se 3 (by rfl) ⟨113531, by rfl⟩ : syracuseStep 605501 = 227063) (by norm_num)
theorem B605525 : Blo 401768 605525 := bbase (se 11 (by rfl) ⟨443, by rfl⟩ : syracuseStep 605525 = 887) (by norm_num)
theorem B605549 : Blo 401768 605549 := bbase (se 3 (by rfl) ⟨113540, by rfl⟩ : syracuseStep 605549 = 227081) (by norm_num)
theorem B572789 : Blo 401768 572789 := bbase (se 5 (by rfl) ⟨26849, by rfl⟩ : syracuseStep 572789 = 53699) (by norm_num)
theorem B605573 : Blo 401768 605573 := bbase (se 4 (by rfl) ⟨56772, by rfl⟩ : syracuseStep 605573 = 113545) (by norm_num)
theorem B1719701 : Blo 401768 1719701 := bbase (se 6 (by rfl) ⟨40305, by rfl⟩ : syracuseStep 1719701 = 80611) (by norm_num)
theorem B769429 : Blo 401768 769429 := bbase (se 6 (by rfl) ⟨18033, by rfl⟩ : syracuseStep 769429 = 36067) (by norm_num)
theorem B605597 : Blo 401768 605597 := bbase (se 3 (by rfl) ⟨113549, by rfl⟩ : syracuseStep 605597 = 227099) (by norm_num)
theorem B605621 : Blo 401768 605621 := bbase (se 5 (by rfl) ⟨28388, by rfl⟩ : syracuseStep 605621 = 56777) (by norm_num)
theorem B572869 : Blo 401768 572869 := bbase (se 4 (by rfl) ⟨53706, by rfl⟩ : syracuseStep 572869 = 107413) (by norm_num)
theorem B605645 : Blo 401768 605645 := bbase (se 3 (by rfl) ⟨113558, by rfl⟩ : syracuseStep 605645 = 227117) (by norm_num)
theorem B605669 : Blo 401768 605669 := bbase (se 4 (by rfl) ⟨56781, by rfl⟩ : syracuseStep 605669 = 113563) (by norm_num)
theorem B605693 : Blo 401768 605693 := bbase (se 3 (by rfl) ⟨113567, by rfl⟩ : syracuseStep 605693 = 227135) (by norm_num)
theorem B605717 : Blo 401768 605717 := bbase (se 6 (by rfl) ⟨14196, by rfl⟩ : syracuseStep 605717 = 28393) (by norm_num)
theorem B605741 : Blo 401768 605741 := bbase (se 3 (by rfl) ⟨113576, by rfl⟩ : syracuseStep 605741 = 227153) (by norm_num)
theorem B572989 : Blo 401768 572989 := bbase (se 3 (by rfl) ⟨107435, by rfl⟩ : syracuseStep 572989 = 214871) (by norm_num)
theorem B605765 : Blo 401768 605765 := bbase (se 4 (by rfl) ⟨56790, by rfl⟩ : syracuseStep 605765 = 113581) (by norm_num)
theorem B605789 : Blo 401768 605789 := bbase (se 3 (by rfl) ⟨113585, by rfl⟩ : syracuseStep 605789 = 227171) (by norm_num)
theorem B605813 : Blo 401768 605813 := bbase (se 5 (by rfl) ⟨28397, by rfl⟩ : syracuseStep 605813 = 56795) (by norm_num)
theorem B409217 : Blo 401768 409217 := bbase (se 2 (by rfl) ⟨153456, by rfl⟩ : syracuseStep 409217 = 306913) (by norm_num)
theorem B605837 : Blo 401768 605837 := bbase (se 3 (by rfl) ⟨113594, by rfl⟩ : syracuseStep 605837 = 227189) (by norm_num)
theorem B1031837 : Blo 401768 1031837 := bbase (se 3 (by rfl) ⟨193469, by rfl⟩ : syracuseStep 1031837 = 386939) (by norm_num)
theorem B573085 : Blo 401768 573085 := bbase (se 3 (by rfl) ⟨107453, by rfl⟩ : syracuseStep 573085 = 214907) (by norm_num)
theorem B605861 : Blo 401768 605861 := bbase (se 4 (by rfl) ⟨56799, by rfl⟩ : syracuseStep 605861 = 113599) (by norm_num)
theorem B442045 : Blo 401768 442045 := bbase (se 3 (by rfl) ⟨82883, by rfl⟩ : syracuseStep 442045 = 165767) (by norm_num)
theorem B605885 : Blo 401768 605885 := bbase (se 3 (by rfl) ⟨113603, by rfl⟩ : syracuseStep 605885 = 227207) (by norm_num)
theorem B1359557 : Blo 401768 1359557 := bbase (se 4 (by rfl) ⟨127458, by rfl⟩ : syracuseStep 1359557 = 254917) (by norm_num)
theorem B769733 : Blo 401768 769733 := bbase (se 4 (by rfl) ⟨72162, by rfl⟩ : syracuseStep 769733 = 144325) (by norm_num)
theorem B605909 : Blo 401768 605909 := bbase (se 7 (by rfl) ⟨7100, by rfl⟩ : syracuseStep 605909 = 14201) (by norm_num)
theorem B605933 : Blo 401768 605933 := bbase (se 3 (by rfl) ⟨113612, by rfl⟩ : syracuseStep 605933 = 227225) (by norm_num)
theorem B605957 : Blo 401768 605957 := bbase (se 4 (by rfl) ⟨56808, by rfl⟩ : syracuseStep 605957 = 113617) (by norm_num)
theorem B605981 : Blo 401768 605981 := bbase (se 3 (by rfl) ⟨113621, by rfl⟩ : syracuseStep 605981 = 227243) (by norm_num)
theorem B606005 : Blo 401768 606005 := bbase (se 5 (by rfl) ⟨28406, by rfl⟩ : syracuseStep 606005 = 56813) (by norm_num)
theorem B606029 : Blo 401768 606029 := bbase (se 3 (by rfl) ⟨113630, by rfl⟩ : syracuseStep 606029 = 227261) (by norm_num)
theorem B606053 : Blo 401768 606053 := bbase (se 4 (by rfl) ⟨56817, by rfl⟩ : syracuseStep 606053 = 113635) (by norm_num)
theorem B606077 : Blo 401768 606077 := bbase (se 3 (by rfl) ⟨113639, by rfl⟩ : syracuseStep 606077 = 227279) (by norm_num)
theorem B606101 : Blo 401768 606101 := bbase (se 6 (by rfl) ⟨14205, by rfl⟩ : syracuseStep 606101 = 28411) (by norm_num)
theorem B606125 : Blo 401768 606125 := bbase (se 3 (by rfl) ⟨113648, by rfl⟩ : syracuseStep 606125 = 227297) (by norm_num)
theorem B606149 : Blo 401768 606149 := bbase (se 4 (by rfl) ⟨56826, by rfl⟩ : syracuseStep 606149 = 113653) (by norm_num)
theorem B606173 : Blo 401768 606173 := bbase (se 3 (by rfl) ⟨113657, by rfl⟩ : syracuseStep 606173 = 227315) (by norm_num)
theorem B606197 : Blo 401768 606197 := bbase (se 5 (by rfl) ⟨28415, by rfl⟩ : syracuseStep 606197 = 56831) (by norm_num)
theorem B606221 : Blo 401768 606221 := bbase (se 3 (by rfl) ⟨113666, by rfl⟩ : syracuseStep 606221 = 227333) (by norm_num)
theorem B606245 : Blo 401768 606245 := bbase (se 4 (by rfl) ⟨56835, by rfl⟩ : syracuseStep 606245 = 113671) (by norm_num)
theorem B606269 : Blo 401768 606269 := bbase (se 3 (by rfl) ⟨113675, by rfl⟩ : syracuseStep 606269 = 227351) (by norm_num)
theorem B3686485 : Blo 401768 3686485 := bbase (se 8 (by rfl) ⟨21600, by rfl⟩ : syracuseStep 3686485 = 43201) (by norm_num)
theorem B606293 : Blo 401768 606293 := bbase (se 8 (by rfl) ⟨3552, by rfl⟩ : syracuseStep 606293 = 7105) (by norm_num)
theorem B606317 : Blo 401768 606317 := bbase (se 3 (by rfl) ⟨113684, by rfl⟩ : syracuseStep 606317 = 227369) (by norm_num)
theorem B1359989 : Blo 401768 1359989 := bbase (se 5 (by rfl) ⟨63749, by rfl⟩ : syracuseStep 1359989 = 127499) (by norm_num)
theorem B606341 : Blo 401768 606341 := bbase (se 4 (by rfl) ⟨56844, by rfl⟩ : syracuseStep 606341 = 113689) (by norm_num)
theorem B573581 : Blo 401768 573581 := bbase (se 3 (by rfl) ⟨107546, by rfl⟩ : syracuseStep 573581 = 215093) (by norm_num)
theorem B606365 : Blo 401768 606365 := bbase (se 3 (by rfl) ⟨113693, by rfl⟩ : syracuseStep 606365 = 227387) (by norm_num)
theorem B2048165 : Blo 401768 2048165 := bbase (se 4 (by rfl) ⟨192015, by rfl⟩ : syracuseStep 2048165 = 384031) (by norm_num)
theorem B1294517 : Blo 401768 1294517 := bbase (se 5 (by rfl) ⟨60680, by rfl⟩ : syracuseStep 1294517 = 121361) (by norm_num)
theorem B606389 : Blo 401768 606389 := bbase (se 5 (by rfl) ⟨28424, by rfl⟩ : syracuseStep 606389 = 56849) (by norm_num)
theorem B606413 : Blo 401768 606413 := bbase (se 3 (by rfl) ⟨113702, by rfl⟩ : syracuseStep 606413 = 227405) (by norm_num)
theorem B606437 : Blo 401768 606437 := bbase (se 4 (by rfl) ⟨56853, by rfl⟩ : syracuseStep 606437 = 113707) (by norm_num)
theorem B606461 : Blo 401768 606461 := bbase (se 3 (by rfl) ⟨113711, by rfl⟩ : syracuseStep 606461 = 227423) (by norm_num)
theorem B606485 : Blo 401768 606485 := bbase (se 6 (by rfl) ⟨14214, by rfl⟩ : syracuseStep 606485 = 28429) (by norm_num)
theorem B606509 : Blo 401768 606509 := bbase (se 3 (by rfl) ⟨113720, by rfl⟩ : syracuseStep 606509 = 227441) (by norm_num)
theorem B606533 : Blo 401768 606533 := bbase (se 4 (by rfl) ⟨56862, by rfl⟩ : syracuseStep 606533 = 113725) (by norm_num)
theorem B606557 : Blo 401768 606557 := bbase (se 3 (by rfl) ⟨113729, by rfl⟩ : syracuseStep 606557 = 227459) (by norm_num)
theorem B606581 : Blo 401768 606581 := bbase (se 5 (by rfl) ⟨28433, by rfl⟩ : syracuseStep 606581 = 56867) (by norm_num)
theorem B606605 : Blo 401768 606605 := bbase (se 3 (by rfl) ⟨113738, by rfl⟩ : syracuseStep 606605 = 227477) (by norm_num)
theorem B606629 : Blo 401768 606629 := bbase (se 4 (by rfl) ⟨56871, by rfl⟩ : syracuseStep 606629 = 113743) (by norm_num)
theorem B606653 : Blo 401768 606653 := bbase (se 3 (by rfl) ⟨113747, by rfl⟩ : syracuseStep 606653 = 227495) (by norm_num)
theorem B606677 : Blo 401768 606677 := bbase (se 7 (by rfl) ⟨7109, by rfl⟩ : syracuseStep 606677 = 14219) (by norm_num)
theorem B606701 : Blo 401768 606701 := bbase (se 3 (by rfl) ⟨113756, by rfl⟩ : syracuseStep 606701 = 227513) (by norm_num)
theorem B410113 : Blo 401768 410113 := bbase (se 2 (by rfl) ⟨153792, by rfl⟩ : syracuseStep 410113 = 307585) (by norm_num)
theorem B606725 : Blo 401768 606725 := bbase (se 4 (by rfl) ⟨56880, by rfl⟩ : syracuseStep 606725 = 113761) (by norm_num)
theorem B606749 : Blo 401768 606749 := bbase (se 3 (by rfl) ⟨113765, by rfl⟩ : syracuseStep 606749 = 227531) (by norm_num)
theorem B1360421 : Blo 401768 1360421 := bbase (se 4 (by rfl) ⟨127539, by rfl⟩ : syracuseStep 1360421 = 255079) (by norm_num)
theorem B410161 : Blo 401768 410161 := bbase (se 2 (by rfl) ⟨153810, by rfl⟩ : syracuseStep 410161 = 307621) (by norm_num)
theorem B606773 : Blo 401768 606773 := bbase (se 5 (by rfl) ⟨28442, by rfl⟩ : syracuseStep 606773 = 56885) (by norm_num)
theorem B606797 : Blo 401768 606797 := bbase (se 3 (by rfl) ⟨113774, by rfl⟩ : syracuseStep 606797 = 227549) (by norm_num)
theorem B508513 : Blo 401768 508513 := bbase (se 2 (by rfl) ⟨190692, by rfl⟩ : syracuseStep 508513 = 381385) (by norm_num)
theorem B1229413 : Blo 401768 1229413 := bbase (se 4 (by rfl) ⟨115257, by rfl⟩ : syracuseStep 1229413 = 230515) (by norm_num)
theorem B606821 : Blo 401768 606821 := bbase (se 4 (by rfl) ⟨56889, by rfl⟩ : syracuseStep 606821 = 113779) (by norm_num)
theorem B639605 : Blo 401768 639605 := bbase (se 5 (by rfl) ⟨29981, by rfl⟩ : syracuseStep 639605 = 59963) (by norm_num)
theorem B606845 : Blo 401768 606845 := bbase (se 3 (by rfl) ⟨113783, by rfl⟩ : syracuseStep 606845 = 227567) (by norm_num)
theorem B606869 : Blo 401768 606869 := bbase (se 6 (by rfl) ⟨14223, by rfl⟩ : syracuseStep 606869 = 28447) (by norm_num)
theorem B606893 : Blo 401768 606893 := bbase (se 3 (by rfl) ⟨113792, by rfl⟩ : syracuseStep 606893 = 227585) (by norm_num)
theorem B574133 : Blo 401768 574133 := bbase (se 5 (by rfl) ⟨26912, by rfl⟩ : syracuseStep 574133 = 53825) (by norm_num)
theorem B508609 : Blo 401768 508609 := bbase (se 2 (by rfl) ⟨190728, by rfl⟩ : syracuseStep 508609 = 381457) (by norm_num)
theorem B606917 : Blo 401768 606917 := bbase (se 4 (by rfl) ⟨56898, by rfl⟩ : syracuseStep 606917 = 113797) (by norm_num)
theorem B606941 : Blo 401768 606941 := bbase (se 3 (by rfl) ⟨113801, by rfl⟩ : syracuseStep 606941 = 227603) (by norm_num)
theorem B606965 : Blo 401768 606965 := bbase (se 5 (by rfl) ⟨28451, by rfl⟩ : syracuseStep 606965 = 56903) (by norm_num)
theorem B606989 : Blo 401768 606989 := bbase (se 3 (by rfl) ⟨113810, by rfl⟩ : syracuseStep 606989 = 227621) (by norm_num)
theorem B607013 : Blo 401768 607013 := bbase (se 4 (by rfl) ⟨56907, by rfl⟩ : syracuseStep 607013 = 113815) (by norm_num)
theorem B3687221 : Blo 401768 3687221 := bbase (se 5 (by rfl) ⟨172838, by rfl⟩ : syracuseStep 3687221 = 345677) (by norm_num)
theorem B607037 : Blo 401768 607037 := bbase (se 3 (by rfl) ⟨113819, by rfl⟩ : syracuseStep 607037 = 227639) (by norm_num)
theorem B607061 : Blo 401768 607061 := bbase (se 9 (by rfl) ⟨1778, by rfl⟩ : syracuseStep 607061 = 3557) (by norm_num)
theorem B508781 : Blo 401768 508781 := bbase (se 3 (by rfl) ⟨95396, by rfl⟩ : syracuseStep 508781 = 190793) (by norm_num)
theorem B607085 : Blo 401768 607085 := bbase (se 3 (by rfl) ⟨113828, by rfl⟩ : syracuseStep 607085 = 227657) (by norm_num)
theorem B607109 : Blo 401768 607109 := bbase (se 4 (by rfl) ⟨56916, by rfl⟩ : syracuseStep 607109 = 113833) (by norm_num)
theorem B607133 : Blo 401768 607133 := bbase (se 3 (by rfl) ⟨113837, by rfl⟩ : syracuseStep 607133 = 227675) (by norm_num)
theorem B508837 : Blo 401768 508837 := bbase (se 4 (by rfl) ⟨47703, by rfl⟩ : syracuseStep 508837 = 95407) (by norm_num)
theorem B607157 : Blo 401768 607157 := bbase (se 5 (by rfl) ⟨28460, by rfl⟩ : syracuseStep 607157 = 56921) (by norm_num)
theorem B607181 : Blo 401768 607181 := bbase (se 3 (by rfl) ⟨113846, by rfl⟩ : syracuseStep 607181 = 227693) (by norm_num)
theorem B1360853 : Blo 401768 1360853 := bbase (se 7 (by rfl) ⟨15947, by rfl⟩ : syracuseStep 1360853 = 31895) (by norm_num)
theorem B607205 : Blo 401768 607205 := bbase (se 4 (by rfl) ⟨56925, by rfl⟩ : syracuseStep 607205 = 113851) (by norm_num)
theorem B607229 : Blo 401768 607229 := bbase (se 3 (by rfl) ⟨113855, by rfl⟩ : syracuseStep 607229 = 227711) (by norm_num)
theorem B508933 : Blo 401768 508933 := bbase (se 4 (by rfl) ⟨47712, by rfl⟩ : syracuseStep 508933 = 95425) (by norm_num)
theorem B607253 : Blo 401768 607253 := bbase (se 6 (by rfl) ⟨14232, by rfl⟩ : syracuseStep 607253 = 28465) (by norm_num)
theorem B967717 : Blo 401768 967717 := bbase (se 4 (by rfl) ⟨90723, by rfl⟩ : syracuseStep 967717 = 181447) (by norm_num)
theorem B607277 : Blo 401768 607277 := bbase (se 3 (by rfl) ⟨113864, by rfl⟩ : syracuseStep 607277 = 227729) (by norm_num)
theorem B607301 : Blo 401768 607301 := bbase (se 4 (by rfl) ⟨56934, by rfl⟩ : syracuseStep 607301 = 113869) (by norm_num)
theorem B607325 : Blo 401768 607325 := bbase (se 3 (by rfl) ⟨113873, by rfl⟩ : syracuseStep 607325 = 227747) (by norm_num)
theorem B410729 : Blo 401768 410729 := bbase (se 2 (by rfl) ⟨154023, by rfl⟩ : syracuseStep 410729 = 308047) (by norm_num)
theorem B607349 : Blo 401768 607349 := bbase (se 5 (by rfl) ⟨28469, by rfl⟩ : syracuseStep 607349 = 56939) (by norm_num)
theorem B607373 : Blo 401768 607373 := bbase (se 3 (by rfl) ⟨113882, by rfl⟩ : syracuseStep 607373 = 227765) (by norm_num)
theorem B607397 : Blo 401768 607397 := bbase (se 4 (by rfl) ⟨56943, by rfl⟩ : syracuseStep 607397 = 113887) (by norm_num)
theorem B509105 : Blo 401768 509105 := bbase (se 2 (by rfl) ⟨190914, by rfl⟩ : syracuseStep 509105 = 381829) (by norm_num)
theorem B607421 : Blo 401768 607421 := bbase (se 3 (by rfl) ⟨113891, by rfl⟩ : syracuseStep 607421 = 227783) (by norm_num)
theorem B1557701 : Blo 401768 1557701 := bbase (se 4 (by rfl) ⟨146034, by rfl⟩ : syracuseStep 1557701 = 292069) (by norm_num)
theorem B607445 : Blo 401768 607445 := bbase (se 7 (by rfl) ⟨7118, by rfl⟩ : syracuseStep 607445 = 14237) (by norm_num)
theorem B509161 : Blo 401768 509161 := bbase (se 2 (by rfl) ⟨190935, by rfl⟩ : syracuseStep 509161 = 381871) (by norm_num)
theorem B607469 : Blo 401768 607469 := bbase (se 3 (by rfl) ⟨113900, by rfl⟩ : syracuseStep 607469 = 227801) (by norm_num)
theorem B607493 : Blo 401768 607493 := bbase (se 4 (by rfl) ⟨56952, by rfl⟩ : syracuseStep 607493 = 113905) (by norm_num)
theorem B607517 : Blo 401768 607517 := bbase (se 3 (by rfl) ⟨113909, by rfl⟩ : syracuseStep 607517 = 227819) (by norm_num)
theorem B607541 : Blo 401768 607541 := bbase (se 5 (by rfl) ⟨28478, by rfl⟩ : syracuseStep 607541 = 56957) (by norm_num)
theorem B509257 : Blo 401768 509257 := bbase (se 2 (by rfl) ⟨190971, by rfl⟩ : syracuseStep 509257 = 381943) (by norm_num)
theorem B607565 : Blo 401768 607565 := bbase (se 3 (by rfl) ⟨113918, by rfl⟩ : syracuseStep 607565 = 227837) (by norm_num)
theorem B607589 : Blo 401768 607589 := bbase (se 4 (by rfl) ⟨56961, by rfl⟩ : syracuseStep 607589 = 113923) (by norm_num)
theorem B607613 : Blo 401768 607613 := bbase (se 3 (by rfl) ⟨113927, by rfl⟩ : syracuseStep 607613 = 227855) (by norm_num)
theorem B1361285 : Blo 401768 1361285 := bbase (se 4 (by rfl) ⟨127620, by rfl⟩ : syracuseStep 1361285 = 255241) (by norm_num)
theorem B607637 : Blo 401768 607637 := bbase (se 6 (by rfl) ⟨14241, by rfl⟩ : syracuseStep 607637 = 28483) (by norm_num)
theorem B574885 : Blo 401768 574885 := bbase (se 4 (by rfl) ⟨53895, by rfl⟩ : syracuseStep 574885 = 107791) (by norm_num)
theorem B607661 : Blo 401768 607661 := bbase (se 3 (by rfl) ⟨113936, by rfl⟩ : syracuseStep 607661 = 227873) (by norm_num)
theorem B2049461 : Blo 401768 2049461 := bbase (se 5 (by rfl) ⟨96068, by rfl⟩ : syracuseStep 2049461 = 192137) (by norm_num)
theorem B607685 : Blo 401768 607685 := bbase (se 4 (by rfl) ⟨56970, by rfl⟩ : syracuseStep 607685 = 113941) (by norm_num)
theorem B607709 : Blo 401768 607709 := bbase (se 3 (by rfl) ⟨113945, by rfl⟩ : syracuseStep 607709 = 227891) (by norm_num)
theorem B509429 : Blo 401768 509429 := bbase (se 5 (by rfl) ⟨23879, by rfl⟩ : syracuseStep 509429 = 47759) (by norm_num)
theorem B607733 : Blo 401768 607733 := bbase (se 5 (by rfl) ⟨28487, by rfl⟩ : syracuseStep 607733 = 56975) (by norm_num)
theorem B607757 : Blo 401768 607757 := bbase (se 3 (by rfl) ⟨113954, by rfl⟩ : syracuseStep 607757 = 227909) (by norm_num)
theorem B607781 : Blo 401768 607781 := bbase (se 4 (by rfl) ⟨56979, by rfl⟩ : syracuseStep 607781 = 113959) (by norm_num)
theorem B509485 : Blo 401768 509485 := bbase (se 3 (by rfl) ⟨95528, by rfl⟩ : syracuseStep 509485 = 191057) (by norm_num)
theorem B607805 : Blo 401768 607805 := bbase (se 3 (by rfl) ⟨113963, by rfl⟩ : syracuseStep 607805 = 227927) (by norm_num)
theorem B607829 : Blo 401768 607829 := bbase (se 8 (by rfl) ⟨3561, by rfl⟩ : syracuseStep 607829 = 7123) (by norm_num)
theorem B607853 : Blo 401768 607853 := bbase (se 3 (by rfl) ⟨113972, by rfl⟩ : syracuseStep 607853 = 227945) (by norm_num)
theorem B1721989 : Blo 401768 1721989 := bbase (se 4 (by rfl) ⟨161436, by rfl⟩ : syracuseStep 1721989 = 322873) (by norm_num)
theorem B607877 : Blo 401768 607877 := bbase (se 4 (by rfl) ⟨56988, by rfl⟩ : syracuseStep 607877 = 113977) (by norm_num)
theorem B509581 : Blo 401768 509581 := bbase (se 3 (by rfl) ⟨95546, by rfl⟩ : syracuseStep 509581 = 191093) (by norm_num)
theorem B607901 : Blo 401768 607901 := bbase (se 3 (by rfl) ⟨113981, by rfl⟩ : syracuseStep 607901 = 227963) (by norm_num)
theorem B607925 : Blo 401768 607925 := bbase (se 5 (by rfl) ⟨28496, by rfl⟩ : syracuseStep 607925 = 56993) (by norm_num)
theorem B968381 : Blo 401768 968381 := bbase (se 3 (by rfl) ⟨181571, by rfl⟩ : syracuseStep 968381 = 363143) (by norm_num)
theorem B607949 : Blo 401768 607949 := bbase (se 3 (by rfl) ⟨113990, by rfl⟩ : syracuseStep 607949 = 227981) (by norm_num)
theorem B607973 : Blo 401768 607973 := bbase (se 4 (by rfl) ⟨56997, by rfl⟩ : syracuseStep 607973 = 113995) (by norm_num)
theorem B1525493 : Blo 401768 1525493 := bbase (se 5 (by rfl) ⟨71507, by rfl⟩ : syracuseStep 1525493 = 143015) (by norm_num)
theorem B607997 : Blo 401768 607997 := bbase (se 3 (by rfl) ⟨113999, by rfl⟩ : syracuseStep 607997 = 227999) (by norm_num)
theorem B608021 : Blo 401768 608021 := bbase (se 6 (by rfl) ⟨14250, by rfl⟩ : syracuseStep 608021 = 28501) (by norm_num)
theorem B608045 : Blo 401768 608045 := bbase (se 3 (by rfl) ⟨114008, by rfl⟩ : syracuseStep 608045 = 228017) (by norm_num)
theorem B1361717 : Blo 401768 1361717 := bbase (se 5 (by rfl) ⟨63830, by rfl⟩ : syracuseStep 1361717 = 127661) (by norm_num)
theorem B509753 : Blo 401768 509753 := bbase (se 2 (by rfl) ⟨191157, by rfl⟩ : syracuseStep 509753 = 382315) (by norm_num)
theorem B608069 : Blo 401768 608069 := bbase (se 4 (by rfl) ⟨57006, by rfl⟩ : syracuseStep 608069 = 114013) (by norm_num)
theorem B608093 : Blo 401768 608093 := bbase (se 3 (by rfl) ⟨114017, by rfl⟩ : syracuseStep 608093 = 228035) (by norm_num)
theorem B509809 : Blo 401768 509809 := bbase (se 2 (by rfl) ⟨191178, by rfl⟩ : syracuseStep 509809 = 382357) (by norm_num)
theorem B608117 : Blo 401768 608117 := bbase (se 5 (by rfl) ⟨28505, by rfl⟩ : syracuseStep 608117 = 57011) (by norm_num)
theorem B608141 : Blo 401768 608141 := bbase (se 3 (by rfl) ⟨114026, by rfl⟩ : syracuseStep 608141 = 228053) (by norm_num)
theorem B608165 : Blo 401768 608165 := bbase (se 4 (by rfl) ⟨57015, by rfl⟩ : syracuseStep 608165 = 114031) (by norm_num)
theorem B608189 : Blo 401768 608189 := bbase (se 3 (by rfl) ⟨114035, by rfl⟩ : syracuseStep 608189 = 228071) (by norm_num)
theorem B509905 : Blo 401768 509905 := bbase (se 2 (by rfl) ⟨191214, by rfl⟩ : syracuseStep 509905 = 382429) (by norm_num)
theorem B608213 : Blo 401768 608213 := bbase (se 7 (by rfl) ⟨7127, by rfl⟩ : syracuseStep 608213 = 14255) (by norm_num)
theorem B608237 : Blo 401768 608237 := bbase (se 3 (by rfl) ⟨114044, by rfl⟩ : syracuseStep 608237 = 228089) (by norm_num)
theorem B608261 : Blo 401768 608261 := bbase (se 4 (by rfl) ⟨57024, by rfl⟩ : syracuseStep 608261 = 114049) (by norm_num)
theorem B608285 : Blo 401768 608285 := bbase (se 3 (by rfl) ⟨114053, by rfl⟩ : syracuseStep 608285 = 228107) (by norm_num)
theorem B608309 : Blo 401768 608309 := bbase (se 5 (by rfl) ⟨28514, by rfl⟩ : syracuseStep 608309 = 57029) (by norm_num)
theorem B608333 : Blo 401768 608333 := bbase (se 3 (by rfl) ⟨114062, by rfl⟩ : syracuseStep 608333 = 228125) (by norm_num)
theorem B608357 : Blo 401768 608357 := bbase (se 4 (by rfl) ⟨57033, by rfl⟩ : syracuseStep 608357 = 114067) (by norm_num)
theorem B510077 : Blo 401768 510077 := bbase (se 3 (by rfl) ⟨95639, by rfl⟩ : syracuseStep 510077 = 191279) (by norm_num)
theorem B608381 : Blo 401768 608381 := bbase (se 3 (by rfl) ⟨114071, by rfl⟩ : syracuseStep 608381 = 228143) (by norm_num)
theorem B3885205 : Blo 401768 3885205 := bbase (se 6 (by rfl) ⟨91059, by rfl⟩ : syracuseStep 3885205 = 182119) (by norm_num)
theorem B1230997 : Blo 401768 1230997 := bbase (se 6 (by rfl) ⟨28851, by rfl⟩ : syracuseStep 1230997 = 57703) (by norm_num)
theorem B608405 : Blo 401768 608405 := bbase (se 6 (by rfl) ⟨14259, by rfl⟩ : syracuseStep 608405 = 28519) (by norm_num)
theorem B608429 : Blo 401768 608429 := bbase (se 3 (by rfl) ⟨114080, by rfl⟩ : syracuseStep 608429 = 228161) (by norm_num)
theorem B510133 : Blo 401768 510133 := bbase (se 5 (by rfl) ⟨23912, by rfl⟩ : syracuseStep 510133 = 47825) (by norm_num)
theorem B575677 : Blo 401768 575677 := bbase (se 3 (by rfl) ⟨107939, by rfl⟩ : syracuseStep 575677 = 215879) (by norm_num)
theorem B608453 : Blo 401768 608453 := bbase (se 4 (by rfl) ⟨57042, by rfl⟩ : syracuseStep 608453 = 114085) (by norm_num)
theorem B608477 : Blo 401768 608477 := bbase (se 3 (by rfl) ⟨114089, by rfl⟩ : syracuseStep 608477 = 228179) (by norm_num)
theorem B1362149 : Blo 401768 1362149 := bbase (se 4 (by rfl) ⟨127701, by rfl⟩ : syracuseStep 1362149 = 255403) (by norm_num)
theorem B608501 : Blo 401768 608501 := bbase (se 5 (by rfl) ⟨28523, by rfl⟩ : syracuseStep 608501 = 57047) (by norm_num)
theorem B608525 : Blo 401768 608525 := bbase (se 3 (by rfl) ⟨114098, by rfl⟩ : syracuseStep 608525 = 228197) (by norm_num)
theorem B510229 : Blo 401768 510229 := bbase (se 6 (by rfl) ⟨11958, by rfl⟩ : syracuseStep 510229 = 23917) (by norm_num)
theorem B608549 : Blo 401768 608549 := bbase (se 4 (by rfl) ⟨57051, by rfl⟩ : syracuseStep 608549 = 114103) (by norm_num)
theorem B608573 : Blo 401768 608573 := bbase (se 3 (by rfl) ⟨114107, by rfl⟩ : syracuseStep 608573 = 228215) (by norm_num)
theorem B608597 : Blo 401768 608597 := bbase (se 10 (by rfl) ⟨891, by rfl⟩ : syracuseStep 608597 = 1783) (by norm_num)
theorem B608621 : Blo 401768 608621 := bbase (se 3 (by rfl) ⟨114116, by rfl⟩ : syracuseStep 608621 = 228233) (by norm_num)
theorem B1296773 : Blo 401768 1296773 := bbase (se 4 (by rfl) ⟨121572, by rfl⟩ : syracuseStep 1296773 = 243145) (by norm_num)
theorem B608645 : Blo 401768 608645 := bbase (se 4 (by rfl) ⟨57060, by rfl⟩ : syracuseStep 608645 = 114121) (by norm_num)
theorem B510401 : Blo 401768 510401 := bbase (se 2 (by rfl) ⟨191400, by rfl⟩ : syracuseStep 510401 = 382801) (by norm_num)
theorem B510457 : Blo 401768 510457 := bbase (se 2 (by rfl) ⟨191421, by rfl⟩ : syracuseStep 510457 = 382843) (by norm_num)
theorem B576013 : Blo 401768 576013 := bbase (se 3 (by rfl) ⟨108002, by rfl⟩ : syracuseStep 576013 = 216005) (by norm_num)
theorem B510553 : Blo 401768 510553 := bbase (se 2 (by rfl) ⟨191457, by rfl⟩ : syracuseStep 510553 = 382915) (by norm_num)
theorem B3263125 : Blo 401768 3263125 := bbase (se 6 (by rfl) ⟨76479, by rfl⟩ : syracuseStep 3263125 = 152959) (by norm_num)
theorem B1362581 : Blo 401768 1362581 := bbase (se 6 (by rfl) ⟨31935, by rfl⟩ : syracuseStep 1362581 = 63871) (by norm_num)
theorem B2050757 : Blo 401768 2050757 := bbase (se 4 (by rfl) ⟨192258, by rfl⟩ : syracuseStep 2050757 = 384517) (by norm_num)
theorem B576229 : Blo 401768 576229 := bbase (se 4 (by rfl) ⟨54021, by rfl⟩ : syracuseStep 576229 = 108043) (by norm_num)
theorem B510725 : Blo 401768 510725 := bbase (se 4 (by rfl) ⟨47880, by rfl⟩ : syracuseStep 510725 = 95761) (by norm_num)
theorem B510781 : Blo 401768 510781 := bbase (se 3 (by rfl) ⟨95771, by rfl⟩ : syracuseStep 510781 = 191543) (by norm_num)
theorem B904013 : Blo 401768 904013 := bbase (se 3 (by rfl) ⟨169502, by rfl⟩ : syracuseStep 904013 = 339005) (by norm_num)
theorem B904085 : Blo 401768 904085 := bbase (se 6 (by rfl) ⟨21189, by rfl⟩ : syracuseStep 904085 = 42379) (by norm_num)
theorem B3263381 : Blo 401768 3263381 := bbase (se 6 (by rfl) ⟨76485, by rfl⟩ : syracuseStep 3263381 = 152971) (by norm_num)
theorem B510877 : Blo 401768 510877 := bbase (se 3 (by rfl) ⟨95789, by rfl⟩ : syracuseStep 510877 = 191579) (by norm_num)
theorem B904157 : Blo 401768 904157 := bbase (se 3 (by rfl) ⟨169529, by rfl⟩ : syracuseStep 904157 = 339059) (by norm_num)
theorem B904229 : Blo 401768 904229 := bbase (se 4 (by rfl) ⟨84771, by rfl⟩ : syracuseStep 904229 = 169543) (by norm_num)
theorem B1363013 : Blo 401768 1363013 := bbase (se 4 (by rfl) ⟨127782, by rfl⟩ : syracuseStep 1363013 = 255565) (by norm_num)
theorem B511049 : Blo 401768 511049 := bbase (se 2 (by rfl) ⟨191643, by rfl⟩ : syracuseStep 511049 = 383287) (by norm_num)
theorem B1723477 : Blo 401768 1723477 := bbase (se 8 (by rfl) ⟨10098, by rfl⟩ : syracuseStep 1723477 = 20197) (by norm_num)
theorem B576605 : Blo 401768 576605 := bbase (se 3 (by rfl) ⟨108113, by rfl⟩ : syracuseStep 576605 = 216227) (by norm_num)
theorem B1723493 : Blo 401768 1723493 := bbase (se 4 (by rfl) ⟨161577, by rfl⟩ : syracuseStep 1723493 = 323155) (by norm_num)
theorem B904301 : Blo 401768 904301 := bbase (se 3 (by rfl) ⟨169556, by rfl⟩ : syracuseStep 904301 = 339113) (by norm_num)
theorem B1559669 : Blo 401768 1559669 := bbase (se 5 (by rfl) ⟨73109, by rfl⟩ : syracuseStep 1559669 = 146219) (by norm_num)
theorem B511105 : Blo 401768 511105 := bbase (se 2 (by rfl) ⟨191664, by rfl⟩ : syracuseStep 511105 = 383329) (by norm_num)
theorem B1297541 : Blo 401768 1297541 := bbase (se 4 (by rfl) ⟨121644, by rfl⟩ : syracuseStep 1297541 = 243289) (by norm_num)
theorem B904373 : Blo 401768 904373 := bbase (se 5 (by rfl) ⟨42392, by rfl⟩ : syracuseStep 904373 = 84785) (by norm_num)
theorem B511201 : Blo 401768 511201 := bbase (se 2 (by rfl) ⟨191700, by rfl⟩ : syracuseStep 511201 = 383401) (by norm_num)
theorem B904445 : Blo 401768 904445 := bbase (se 3 (by rfl) ⟨169583, by rfl⟩ : syracuseStep 904445 = 339167) (by norm_num)
theorem B2182421 : Blo 401768 2182421 := bbase (se 6 (by rfl) ⟨51150, by rfl⟩ : syracuseStep 2182421 = 102301) (by norm_num)
theorem B904517 : Blo 401768 904517 := bbase (se 4 (by rfl) ⟨84798, by rfl⟩ : syracuseStep 904517 = 169597) (by norm_num)
theorem B904589 : Blo 401768 904589 := bbase (se 3 (by rfl) ⟨169610, by rfl⟩ : syracuseStep 904589 = 339221) (by norm_num)
theorem B511373 : Blo 401768 511373 := bbase (se 3 (by rfl) ⟨95882, by rfl⟩ : syracuseStep 511373 = 191765) (by norm_num)
theorem B773525 : Blo 401768 773525 := bbase (se 6 (by rfl) ⟨18129, by rfl⟩ : syracuseStep 773525 = 36259) (by norm_num)
theorem B970157 : Blo 401768 970157 := bbase (se 3 (by rfl) ⟨181904, by rfl⟩ : syracuseStep 970157 = 363809) (by norm_num)
theorem B511429 : Blo 401768 511429 := bbase (se 4 (by rfl) ⟨47946, by rfl⟩ : syracuseStep 511429 = 95893) (by norm_num)
theorem B904661 : Blo 401768 904661 := bbase (se 7 (by rfl) ⟨10601, by rfl⟩ : syracuseStep 904661 = 21203) (by norm_num)
theorem B1363445 : Blo 401768 1363445 := bbase (se 5 (by rfl) ⟨63911, by rfl⟩ : syracuseStep 1363445 = 127823) (by norm_num)
theorem B904733 : Blo 401768 904733 := bbase (se 3 (by rfl) ⟨169637, by rfl⟩ : syracuseStep 904733 = 339275) (by norm_num)
theorem B511525 : Blo 401768 511525 := bbase (se 4 (by rfl) ⟨47955, by rfl⟩ : syracuseStep 511525 = 95911) (by norm_num)
theorem B1461797 : Blo 401768 1461797 := bbase (se 4 (by rfl) ⟨137043, by rfl⟩ : syracuseStep 1461797 = 274087) (by norm_num)
theorem B773677 : Blo 401768 773677 := bbase (se 3 (by rfl) ⟨145064, by rfl⟩ : syracuseStep 773677 = 290129) (by norm_num)
theorem B904805 : Blo 401768 904805 := bbase (se 4 (by rfl) ⟨84825, by rfl⟩ : syracuseStep 904805 = 169651) (by norm_num)
theorem B1298053 : Blo 401768 1298053 := bbase (se 4 (by rfl) ⟨121692, by rfl⟩ : syracuseStep 1298053 = 243385) (by norm_num)
theorem B904877 : Blo 401768 904877 := bbase (se 3 (by rfl) ⟨169664, by rfl⟩ : syracuseStep 904877 = 339329) (by norm_num)
theorem B511697 : Blo 401768 511697 := bbase (se 2 (by rfl) ⟨191886, by rfl⟩ : syracuseStep 511697 = 383773) (by norm_num)
theorem B904949 : Blo 401768 904949 := bbase (se 5 (by rfl) ⟨42419, by rfl⟩ : syracuseStep 904949 = 84839) (by norm_num)
theorem B511753 : Blo 401768 511753 := bbase (se 2 (by rfl) ⟨191907, by rfl⟩ : syracuseStep 511753 = 383815) (by norm_num)
theorem B1527605 : Blo 401768 1527605 := bbase (se 5 (by rfl) ⟨71606, by rfl⟩ : syracuseStep 1527605 = 143213) (by norm_num)
theorem B905021 : Blo 401768 905021 := bbase (se 3 (by rfl) ⟨169691, by rfl⟩ : syracuseStep 905021 = 339383) (by norm_num)
theorem B511849 : Blo 401768 511849 := bbase (se 2 (by rfl) ⟨191943, by rfl⟩ : syracuseStep 511849 = 383887) (by norm_num)
theorem B905093 : Blo 401768 905093 := bbase (se 4 (by rfl) ⟨84852, by rfl⟩ : syracuseStep 905093 = 169705) (by norm_num)
theorem B1363877 : Blo 401768 1363877 := bbase (se 4 (by rfl) ⟨127863, by rfl⟩ : syracuseStep 1363877 = 255727) (by norm_num)
theorem B905165 : Blo 401768 905165 := bbase (se 3 (by rfl) ⟨169718, by rfl⟩ : syracuseStep 905165 = 339437) (by norm_num)
theorem B2052053 : Blo 401768 2052053 := bbase (se 7 (by rfl) ⟨24047, by rfl⟩ : syracuseStep 2052053 = 48095) (by norm_num)
theorem B905237 : Blo 401768 905237 := bbase (se 6 (by rfl) ⟨21216, by rfl⟩ : syracuseStep 905237 = 42433) (by norm_num)
theorem B512021 : Blo 401768 512021 := bbase (se 6 (by rfl) ⟨12000, by rfl⟩ : syracuseStep 512021 = 24001) (by norm_num)
theorem B512077 : Blo 401768 512077 := bbase (se 3 (by rfl) ⟨96014, by rfl⟩ : syracuseStep 512077 = 192029) (by norm_num)
theorem B1527893 : Blo 401768 1527893 := bbase (se 8 (by rfl) ⟨8952, by rfl⟩ : syracuseStep 1527893 = 17905) (by norm_num)
theorem B905309 : Blo 401768 905309 := bbase (se 3 (by rfl) ⟨169745, by rfl⟩ : syracuseStep 905309 = 339491) (by norm_num)
theorem B774293 : Blo 401768 774293 := bbase (se 6 (by rfl) ⟨18147, by rfl⟩ : syracuseStep 774293 = 36295) (by norm_num)
theorem B905381 : Blo 401768 905381 := bbase (se 4 (by rfl) ⟨84879, by rfl⟩ : syracuseStep 905381 = 169759) (by norm_num)
theorem B512173 : Blo 401768 512173 := bbase (se 3 (by rfl) ⟨96032, by rfl⟩ : syracuseStep 512173 = 192065) (by norm_num)
theorem B2904245 : Blo 401768 2904245 := bbase (se 5 (by rfl) ⟨136136, by rfl⟩ : syracuseStep 2904245 = 272273) (by norm_num)
theorem B3068117 : Blo 401768 3068117 := bbase (se 7 (by rfl) ⟨35954, by rfl⟩ : syracuseStep 3068117 = 71909) (by norm_num)
theorem B905453 : Blo 401768 905453 := bbase (se 3 (by rfl) ⟨169772, by rfl⟩ : syracuseStep 905453 = 339545) (by norm_num)
theorem B905525 : Blo 401768 905525 := bbase (se 5 (by rfl) ⟨42446, by rfl⟩ : syracuseStep 905525 = 84893) (by norm_num)
theorem B1364309 : Blo 401768 1364309 := bbase (se 10 (by rfl) ⟨1998, by rfl⟩ : syracuseStep 1364309 = 3997) (by norm_num)
theorem B512345 : Blo 401768 512345 := bbase (se 2 (by rfl) ⟨192129, by rfl⟩ : syracuseStep 512345 = 384259) (by norm_num)
theorem B905597 : Blo 401768 905597 := bbase (se 3 (by rfl) ⟨169799, by rfl⟩ : syracuseStep 905597 = 339599) (by norm_num)
theorem B512401 : Blo 401768 512401 := bbase (se 2 (by rfl) ⟨192150, by rfl⟩ : syracuseStep 512401 = 384301) (by norm_num)
theorem B905669 : Blo 401768 905669 := bbase (se 4 (by rfl) ⟨84906, by rfl⟩ : syracuseStep 905669 = 169813) (by norm_num)
theorem B512497 : Blo 401768 512497 := bbase (se 2 (by rfl) ⟨192186, by rfl⟩ : syracuseStep 512497 = 384373) (by norm_num)
theorem B905741 : Blo 401768 905741 := bbase (se 3 (by rfl) ⟨169826, by rfl⟩ : syracuseStep 905741 = 339653) (by norm_num)
theorem B905813 : Blo 401768 905813 := bbase (se 8 (by rfl) ⟨5307, by rfl⟩ : syracuseStep 905813 = 10615) (by norm_num)
theorem B905885 : Blo 401768 905885 := bbase (se 3 (by rfl) ⟨169853, by rfl⟩ : syracuseStep 905885 = 339707) (by norm_num)
theorem B512669 : Blo 401768 512669 := bbase (se 3 (by rfl) ⟨96125, by rfl⟩ : syracuseStep 512669 = 192251) (by norm_num)
theorem B840389 : Blo 401768 840389 := bbase (se 4 (by rfl) ⟨78786, by rfl⟩ : syracuseStep 840389 = 157573) (by norm_num)
theorem B512725 : Blo 401768 512725 := bbase (se 7 (by rfl) ⟨6008, by rfl⟩ : syracuseStep 512725 = 12017) (by norm_num)
theorem B905957 : Blo 401768 905957 := bbase (se 4 (by rfl) ⟨84933, by rfl⟩ : syracuseStep 905957 = 169867) (by norm_num)
theorem B1364741 : Blo 401768 1364741 := bbase (se 4 (by rfl) ⟨127944, by rfl⟩ : syracuseStep 1364741 = 255889) (by norm_num)
theorem B906029 : Blo 401768 906029 := bbase (se 3 (by rfl) ⟨169880, by rfl⟩ : syracuseStep 906029 = 339761) (by norm_num)
theorem B512821 : Blo 401768 512821 := bbase (se 5 (by rfl) ⟨24038, by rfl⟩ : syracuseStep 512821 = 48077) (by norm_num)
theorem B447293 : Blo 401768 447293 := bbase (se 3 (by rfl) ⟨83867, by rfl⟩ : syracuseStep 447293 = 167735) (by norm_num)
theorem B1168229 : Blo 401768 1168229 := bbase (se 4 (by rfl) ⟨109521, by rfl⟩ : syracuseStep 1168229 = 219043) (by norm_num)
theorem B906101 : Blo 401768 906101 := bbase (se 5 (by rfl) ⟨42473, by rfl⟩ : syracuseStep 906101 = 84947) (by norm_num)
theorem B906173 : Blo 401768 906173 := bbase (se 3 (by rfl) ⟨169907, by rfl⟩ : syracuseStep 906173 = 339815) (by norm_num)
theorem B545725 : Blo 401768 545725 := bbase (se 3 (by rfl) ⟨102323, by rfl⟩ : syracuseStep 545725 = 204647) (by norm_num)
theorem B512993 : Blo 401768 512993 := bbase (se 2 (by rfl) ⟨192372, by rfl⟩ : syracuseStep 512993 = 384745) (by norm_num)
theorem B1168357 : Blo 401768 1168357 := bbase (se 4 (by rfl) ⟨109533, by rfl⟩ : syracuseStep 1168357 = 219067) (by norm_num)
theorem B1102837 : Blo 401768 1102837 := bbase (se 5 (by rfl) ⟨51695, by rfl⟩ : syracuseStep 1102837 = 103391) (by norm_num)
theorem B906245 : Blo 401768 906245 := bbase (se 4 (by rfl) ⟨84960, by rfl⟩ : syracuseStep 906245 = 169921) (by norm_num)
theorem B513049 : Blo 401768 513049 := bbase (se 2 (by rfl) ⟨192393, by rfl⟩ : syracuseStep 513049 = 384787) (by norm_num)
theorem B906317 : Blo 401768 906317 := bbase (se 3 (by rfl) ⟨169934, by rfl⟩ : syracuseStep 906317 = 339869) (by norm_num)
theorem B513145 : Blo 401768 513145 := bbase (se 2 (by rfl) ⟨192429, by rfl⟩ : syracuseStep 513145 = 384859) (by norm_num)
theorem B906389 : Blo 401768 906389 := bbase (se 6 (by rfl) ⟨21243, by rfl⟩ : syracuseStep 906389 = 42487) (by norm_num)
theorem B1365173 : Blo 401768 1365173 := bbase (se 5 (by rfl) ⟨63992, by rfl⟩ : syracuseStep 1365173 = 127985) (by norm_num)
theorem B4183253 : Blo 401768 4183253 := bbase (se 7 (by rfl) ⟨49022, by rfl⟩ : syracuseStep 4183253 = 98045) (by norm_num)
theorem B906461 : Blo 401768 906461 := bbase (se 3 (by rfl) ⟨169961, by rfl⟩ : syracuseStep 906461 = 339923) (by norm_num)
theorem B2053349 : Blo 401768 2053349 := bbase (se 4 (by rfl) ⟨192501, by rfl⟩ : syracuseStep 2053349 = 385003) (by norm_num)
theorem B2577653 : Blo 401768 2577653 := bbase (se 5 (by rfl) ⟨120827, by rfl⟩ : syracuseStep 2577653 = 241655) (by norm_num)
theorem B1529077 : Blo 401768 1529077 := bbase (se 5 (by rfl) ⟨71675, by rfl⟩ : syracuseStep 1529077 = 143351) (by norm_num)
theorem B644357 : Blo 401768 644357 := bbase (se 4 (by rfl) ⟨60408, by rfl⟩ : syracuseStep 644357 = 120817) (by norm_num)
theorem B2446613 : Blo 401768 2446613 := bbase (se 6 (by rfl) ⟨57342, by rfl⟩ : syracuseStep 2446613 = 114685) (by norm_num)
theorem B906533 : Blo 401768 906533 := bbase (se 4 (by rfl) ⟨84987, by rfl⟩ : syracuseStep 906533 = 169975) (by norm_num)
theorem B513317 : Blo 401768 513317 := bbase (se 4 (by rfl) ⟨48123, by rfl⟩ : syracuseStep 513317 = 96247) (by norm_num)
theorem B1725749 : Blo 401768 1725749 := bbase (se 5 (by rfl) ⟨80894, by rfl⟩ : syracuseStep 1725749 = 161789) (by norm_num)
theorem B1299797 : Blo 401768 1299797 := bbase (se 15 (by rfl) ⟨59, by rfl⟩ : syracuseStep 1299797 = 119) (by norm_num)
theorem B513373 : Blo 401768 513373 := bbase (se 3 (by rfl) ⟨96257, by rfl⟩ : syracuseStep 513373 = 192515) (by norm_num)
theorem B906605 : Blo 401768 906605 := bbase (se 3 (by rfl) ⟨169988, by rfl⟩ : syracuseStep 906605 = 339977) (by norm_num)
theorem B4576661 : Blo 401768 4576661 := bbase (se 6 (by rfl) ⟨107265, by rfl⟩ : syracuseStep 4576661 = 214531) (by norm_num)
theorem B906677 : Blo 401768 906677 := bbase (se 5 (by rfl) ⟨42500, by rfl⟩ : syracuseStep 906677 = 85001) (by norm_num)
theorem B513469 : Blo 401768 513469 := bbase (se 3 (by rfl) ⟨96275, by rfl⟩ : syracuseStep 513469 = 192551) (by norm_num)
theorem B972253 : Blo 401768 972253 := bbase (se 3 (by rfl) ⟨182297, by rfl⟩ : syracuseStep 972253 = 364595) (by norm_num)
theorem B906749 : Blo 401768 906749 := bbase (se 3 (by rfl) ⟨170015, by rfl⟩ : syracuseStep 906749 = 340031) (by norm_num)
theorem B1529381 : Blo 401768 1529381 := bbase (se 4 (by rfl) ⟨143379, by rfl⟩ : syracuseStep 1529381 = 286759) (by norm_num)
theorem B906821 : Blo 401768 906821 := bbase (se 4 (by rfl) ⟨85014, by rfl⟩ : syracuseStep 906821 = 170029) (by norm_num)
theorem B1037893 : Blo 401768 1037893 := bbase (se 4 (by rfl) ⟨97302, by rfl⟩ : syracuseStep 1037893 = 194605) (by norm_num)
theorem B611933 : Blo 401768 611933 := bbase (se 3 (by rfl) ⟨114737, by rfl⟩ : syracuseStep 611933 = 229475) (by norm_num)
theorem B1365605 : Blo 401768 1365605 := bbase (se 4 (by rfl) ⟨128025, by rfl⟩ : syracuseStep 1365605 = 256051) (by norm_num)
theorem B906893 : Blo 401768 906893 := bbase (se 3 (by rfl) ⟨170042, by rfl⟩ : syracuseStep 906893 = 340085) (by norm_num)
theorem B906965 : Blo 401768 906965 := bbase (se 7 (by rfl) ⟨10628, by rfl⟩ : syracuseStep 906965 = 21257) (by norm_num)
theorem B644869 : Blo 401768 644869 := bbase (se 4 (by rfl) ⟨60456, by rfl⟩ : syracuseStep 644869 = 120913) (by norm_num)
theorem B907037 : Blo 401768 907037 := bbase (se 3 (by rfl) ⟨170069, by rfl⟩ : syracuseStep 907037 = 340139) (by norm_num)
theorem B907109 : Blo 401768 907109 := bbase (se 4 (by rfl) ⟨85041, by rfl⟩ : syracuseStep 907109 = 170083) (by norm_num)
theorem B907181 : Blo 401768 907181 := bbase (se 3 (by rfl) ⟨170096, by rfl⟩ : syracuseStep 907181 = 340193) (by norm_num)
theorem B907253 : Blo 401768 907253 := bbase (se 5 (by rfl) ⟨42527, by rfl⟩ : syracuseStep 907253 = 85055) (by norm_num)
theorem B1366037 : Blo 401768 1366037 := bbase (se 6 (by rfl) ⟨32016, by rfl⟩ : syracuseStep 1366037 = 64033) (by norm_num)
theorem B907325 : Blo 401768 907325 := bbase (se 3 (by rfl) ⟨170123, by rfl⟩ : syracuseStep 907325 = 340247) (by norm_num)
theorem B546925 : Blo 401768 546925 := bbase (se 3 (by rfl) ⟨102548, by rfl⟩ : syracuseStep 546925 = 205097) (by norm_num)
theorem B907397 : Blo 401768 907397 := bbase (se 4 (by rfl) ⟨85068, by rfl⟩ : syracuseStep 907397 = 170137) (by norm_num)
theorem B678037 : Blo 401768 678037 := bbase (se 6 (by rfl) ⟨15891, by rfl⟩ : syracuseStep 678037 = 31783) (by norm_num)
theorem B612517 : Blo 401768 612517 := bbase (se 4 (by rfl) ⟨57423, by rfl⟩ : syracuseStep 612517 = 114847) (by norm_num)
theorem B972965 : Blo 401768 972965 := bbase (se 4 (by rfl) ⟨91215, by rfl⟩ : syracuseStep 972965 = 182431) (by norm_num)
theorem B907469 : Blo 401768 907469 := bbase (se 3 (by rfl) ⟨170150, by rfl⟩ : syracuseStep 907469 = 340301) (by norm_num)
theorem B678125 : Blo 401768 678125 := bbase (se 3 (by rfl) ⟨127148, by rfl⟩ : syracuseStep 678125 = 254297) (by norm_num)
theorem B907541 : Blo 401768 907541 := bbase (se 6 (by rfl) ⟨21270, by rfl⟩ : syracuseStep 907541 = 42541) (by norm_num)
theorem B645413 : Blo 401768 645413 := bbase (se 4 (by rfl) ⟨60507, by rfl⟩ : syracuseStep 645413 = 121015) (by norm_num)
theorem B907613 : Blo 401768 907613 := bbase (se 3 (by rfl) ⟨170177, by rfl⟩ : syracuseStep 907613 = 340355) (by norm_num)
theorem B678253 : Blo 401768 678253 := bbase (se 3 (by rfl) ⟨127172, by rfl⟩ : syracuseStep 678253 = 254345) (by norm_num)
theorem B907685 : Blo 401768 907685 := bbase (se 4 (by rfl) ⟨85095, by rfl⟩ : syracuseStep 907685 = 170191) (by norm_num)
theorem B1366469 : Blo 401768 1366469 := bbase (se 4 (by rfl) ⟨128106, by rfl⟩ : syracuseStep 1366469 = 256213) (by norm_num)
theorem B678341 : Blo 401768 678341 := bbase (se 4 (by rfl) ⟨63594, by rfl⟩ : syracuseStep 678341 = 127189) (by norm_num)
theorem B907757 : Blo 401768 907757 := bbase (se 3 (by rfl) ⟨170204, by rfl⟩ : syracuseStep 907757 = 340409) (by norm_num)
theorem B1104389 : Blo 401768 1104389 := bbase (se 4 (by rfl) ⟨103536, by rfl⟩ : syracuseStep 1104389 = 207073) (by norm_num)
theorem B973349 : Blo 401768 973349 := bbase (se 4 (by rfl) ⟨91251, by rfl⟩ : syracuseStep 973349 = 182503) (by norm_num)
theorem B907829 : Blo 401768 907829 := bbase (se 5 (by rfl) ⟨42554, by rfl⟩ : syracuseStep 907829 = 85109) (by norm_num)
theorem B678469 : Blo 401768 678469 := bbase (se 4 (by rfl) ⟨63606, by rfl⟩ : syracuseStep 678469 = 127213) (by norm_num)
theorem B907901 : Blo 401768 907901 := bbase (se 3 (by rfl) ⟨170231, by rfl⟩ : syracuseStep 907901 = 340463) (by norm_num)
theorem B678557 : Blo 401768 678557 := bbase (se 3 (by rfl) ⟨127229, by rfl⟩ : syracuseStep 678557 = 254459) (by norm_num)
theorem B907973 : Blo 401768 907973 := bbase (se 4 (by rfl) ⟨85122, by rfl⟩ : syracuseStep 907973 = 170245) (by norm_num)
theorem B908045 : Blo 401768 908045 := bbase (se 3 (by rfl) ⟨170258, by rfl⟩ : syracuseStep 908045 = 340517) (by norm_num)
theorem B678685 : Blo 401768 678685 := bbase (se 3 (by rfl) ⟨127253, by rfl⟩ : syracuseStep 678685 = 254507) (by norm_num)
theorem B973637 : Blo 401768 973637 := bbase (se 4 (by rfl) ⟨91278, by rfl⟩ : syracuseStep 973637 = 182557) (by norm_num)
theorem B645965 : Blo 401768 645965 := bbase (se 3 (by rfl) ⟨121118, by rfl⟩ : syracuseStep 645965 = 242237) (by norm_num)
theorem B908117 : Blo 401768 908117 := bbase (se 9 (by rfl) ⟨2660, by rfl⟩ : syracuseStep 908117 = 5321) (by norm_num)
theorem B645997 : Blo 401768 645997 := bbase (se 3 (by rfl) ⟨121124, by rfl⟩ : syracuseStep 645997 = 242249) (by norm_num)
theorem B678773 : Blo 401768 678773 := bbase (se 5 (by rfl) ⟨31817, by rfl⟩ : syracuseStep 678773 = 63635) (by norm_num)
theorem B1366901 : Blo 401768 1366901 := bbase (se 5 (by rfl) ⟨64073, by rfl⟩ : syracuseStep 1366901 = 128147) (by norm_num)
theorem B908189 : Blo 401768 908189 := bbase (se 3 (by rfl) ⟨170285, by rfl⟩ : syracuseStep 908189 = 340571) (by norm_num)
theorem B547741 : Blo 401768 547741 := bbase (se 3 (by rfl) ⟨102701, by rfl⟩ : syracuseStep 547741 = 205403) (by norm_num)
theorem B908261 : Blo 401768 908261 := bbase (se 4 (by rfl) ⟨85149, by rfl⟩ : syracuseStep 908261 = 170299) (by norm_num)
theorem B678901 : Blo 401768 678901 := bbase (se 5 (by rfl) ⟨31823, by rfl⟩ : syracuseStep 678901 = 63647) (by norm_num)
theorem B908333 : Blo 401768 908333 := bbase (se 3 (by rfl) ⟨170312, by rfl⟩ : syracuseStep 908333 = 340625) (by norm_num)
theorem B678989 : Blo 401768 678989 := bbase (se 3 (by rfl) ⟨127310, by rfl⟩ : syracuseStep 678989 = 254621) (by norm_num)
theorem B908405 : Blo 401768 908405 := bbase (se 5 (by rfl) ⟨42581, by rfl⟩ : syracuseStep 908405 = 85163) (by norm_num)
theorem B908477 : Blo 401768 908477 := bbase (se 3 (by rfl) ⟨170339, by rfl⟩ : syracuseStep 908477 = 340679) (by norm_num)
theorem B679117 : Blo 401768 679117 := bbase (se 3 (by rfl) ⟨127334, by rfl⟩ : syracuseStep 679117 = 254669) (by norm_num)
theorem B580853 : Blo 401768 580853 := bbase (se 5 (by rfl) ⟨27227, by rfl⟩ : syracuseStep 580853 = 54455) (by norm_num)
theorem B908549 : Blo 401768 908549 := bbase (se 4 (by rfl) ⟨85176, by rfl⟩ : syracuseStep 908549 = 170353) (by norm_num)
theorem B679205 : Blo 401768 679205 := bbase (se 4 (by rfl) ⟨63675, by rfl⟩ : syracuseStep 679205 = 127351) (by norm_num)
theorem B1367333 : Blo 401768 1367333 := bbase (se 4 (by rfl) ⟨128187, by rfl⟩ : syracuseStep 1367333 = 256375) (by norm_num)
theorem B613685 : Blo 401768 613685 := bbase (se 5 (by rfl) ⟨28766, by rfl⟩ : syracuseStep 613685 = 57533) (by norm_num)
theorem B908621 : Blo 401768 908621 := bbase (se 3 (by rfl) ⟨170366, by rfl⟩ : syracuseStep 908621 = 340733) (by norm_num)
theorem B908693 : Blo 401768 908693 := bbase (se 6 (by rfl) ⟨21297, by rfl⟩ : syracuseStep 908693 = 42595) (by norm_num)
theorem B679333 : Blo 401768 679333 := bbase (se 4 (by rfl) ⟨63687, by rfl⟩ : syracuseStep 679333 = 127375) (by norm_num)
theorem B548309 : Blo 401768 548309 := bbase (se 7 (by rfl) ⟨6425, by rfl⟩ : syracuseStep 548309 = 12851) (by norm_num)
theorem B908765 : Blo 401768 908765 := bbase (se 3 (by rfl) ⟨170393, by rfl⟩ : syracuseStep 908765 = 340787) (by norm_num)
theorem B679421 : Blo 401768 679421 := bbase (se 3 (by rfl) ⟨127391, by rfl⟩ : syracuseStep 679421 = 254783) (by norm_num)
theorem B908837 : Blo 401768 908837 := bbase (se 4 (by rfl) ⟨85203, by rfl⟩ : syracuseStep 908837 = 170407) (by norm_num)
theorem B1531493 : Blo 401768 1531493 := bbase (se 4 (by rfl) ⟨143577, by rfl⟩ : syracuseStep 1531493 = 287155) (by norm_num)
theorem B908909 : Blo 401768 908909 := bbase (se 3 (by rfl) ⟨170420, by rfl⟩ : syracuseStep 908909 = 340841) (by norm_num)
theorem B679549 : Blo 401768 679549 := bbase (se 3 (by rfl) ⟨127415, by rfl⟩ : syracuseStep 679549 = 254831) (by norm_num)
theorem B614069 : Blo 401768 614069 := bbase (se 5 (by rfl) ⟨28784, by rfl⟩ : syracuseStep 614069 = 57569) (by norm_num)
theorem B908981 : Blo 401768 908981 := bbase (se 5 (by rfl) ⟨42608, by rfl⟩ : syracuseStep 908981 = 85217) (by norm_num)
theorem B679637 : Blo 401768 679637 := bbase (se 7 (by rfl) ⟨7964, by rfl⟩ : syracuseStep 679637 = 15929) (by norm_num)
theorem B1367765 : Blo 401768 1367765 := bbase (se 7 (by rfl) ⟨16028, by rfl⟩ : syracuseStep 1367765 = 32057) (by norm_num)
theorem B483041 : Blo 401768 483041 := bbase (se 2 (by rfl) ⟨181140, by rfl⟩ : syracuseStep 483041 = 362281) (by norm_num)
theorem B909053 : Blo 401768 909053 := bbase (se 3 (by rfl) ⟨170447, by rfl⟩ : syracuseStep 909053 = 340895) (by norm_num)
theorem B646925 : Blo 401768 646925 := bbase (se 3 (by rfl) ⟨121298, by rfl⟩ : syracuseStep 646925 = 242597) (by norm_num)
theorem B909125 : Blo 401768 909125 := bbase (se 4 (by rfl) ⟨85230, by rfl⟩ : syracuseStep 909125 = 170461) (by norm_num)
theorem B679765 : Blo 401768 679765 := bbase (se 9 (by rfl) ⟨1991, by rfl⟩ : syracuseStep 679765 = 3983) (by norm_num)
theorem B515929 : Blo 401768 515929 := bbase (se 2 (by rfl) ⟨193473, by rfl⟩ : syracuseStep 515929 = 386947) (by norm_num)
theorem B1531781 : Blo 401768 1531781 := bbase (se 4 (by rfl) ⟨143604, by rfl⟩ : syracuseStep 1531781 = 287209) (by norm_num)
theorem B909197 : Blo 401768 909197 := bbase (se 3 (by rfl) ⟨170474, by rfl⟩ : syracuseStep 909197 = 340949) (by norm_num)
theorem B679853 : Blo 401768 679853 := bbase (se 3 (by rfl) ⟨127472, by rfl⟩ : syracuseStep 679853 = 254945) (by norm_num)
theorem B3694517 : Blo 401768 3694517 := bbase (se 5 (by rfl) ⟨173180, by rfl⟩ : syracuseStep 3694517 = 346361) (by norm_num)
theorem B909269 : Blo 401768 909269 := bbase (se 7 (by rfl) ⟨10655, by rfl⟩ : syracuseStep 909269 = 21311) (by norm_num)
theorem B483349 : Blo 401768 483349 := bbase (se 6 (by rfl) ⟨11328, by rfl⟩ : syracuseStep 483349 = 22657) (by norm_num)
theorem B909341 : Blo 401768 909341 := bbase (se 3 (by rfl) ⟨170501, by rfl⟩ : syracuseStep 909341 = 341003) (by norm_num)
theorem B679981 : Blo 401768 679981 := bbase (se 3 (by rfl) ⟨127496, by rfl⟩ : syracuseStep 679981 = 254993) (by norm_num)
theorem B3465301 : Blo 401768 3465301 := bbase (se 8 (by rfl) ⟨20304, by rfl⟩ : syracuseStep 3465301 = 40609) (by norm_num)
theorem B909413 : Blo 401768 909413 := bbase (se 4 (by rfl) ⟨85257, by rfl⟩ : syracuseStep 909413 = 170515) (by norm_num)
theorem B483445 : Blo 401768 483445 := bbase (se 5 (by rfl) ⟨22661, by rfl⟩ : syracuseStep 483445 = 45323) (by norm_num)
theorem B680069 : Blo 401768 680069 := bbase (se 4 (by rfl) ⟨63756, by rfl⟩ : syracuseStep 680069 = 127513) (by norm_num)
theorem B1368197 : Blo 401768 1368197 := bbase (se 4 (by rfl) ⟨128268, by rfl⟩ : syracuseStep 1368197 = 256537) (by norm_num)
theorem B909485 : Blo 401768 909485 := bbase (se 3 (by rfl) ⟨170528, by rfl⟩ : syracuseStep 909485 = 341057) (by norm_num)
theorem B909557 : Blo 401768 909557 := bbase (se 5 (by rfl) ⟨42635, by rfl⟩ : syracuseStep 909557 = 85271) (by norm_num)
theorem B483589 : Blo 401768 483589 := bbase (se 4 (by rfl) ⟨45336, by rfl⟩ : syracuseStep 483589 = 90673) (by norm_num)
theorem B680197 : Blo 401768 680197 := bbase (se 4 (by rfl) ⟨63768, by rfl⟩ : syracuseStep 680197 = 127537) (by norm_num)
theorem B909629 : Blo 401768 909629 := bbase (se 3 (by rfl) ⟨170555, by rfl⟩ : syracuseStep 909629 = 341111) (by norm_num)
theorem B1040725 : Blo 401768 1040725 := bbase (se 10 (by rfl) ⟨1524, by rfl⟩ : syracuseStep 1040725 = 3049) (by norm_num)
theorem B680285 : Blo 401768 680285 := bbase (se 3 (by rfl) ⟨127553, by rfl⟩ : syracuseStep 680285 = 255107) (by norm_num)
theorem B909701 : Blo 401768 909701 := bbase (se 4 (by rfl) ⟨85284, by rfl⟩ : syracuseStep 909701 = 170569) (by norm_num)
theorem B647605 : Blo 401768 647605 := bbase (se 5 (by rfl) ⟨30356, by rfl⟩ : syracuseStep 647605 = 60713) (by norm_num)
theorem B909773 : Blo 401768 909773 := bbase (se 3 (by rfl) ⟨170582, by rfl⟩ : syracuseStep 909773 = 341165) (by norm_num)
theorem B680413 : Blo 401768 680413 := bbase (se 3 (by rfl) ⟨127577, by rfl⟩ : syracuseStep 680413 = 255155) (by norm_num)
theorem B647669 : Blo 401768 647669 := bbase (se 5 (by rfl) ⟨30359, by rfl⟩ : syracuseStep 647669 = 60719) (by norm_num)
theorem B909845 : Blo 401768 909845 := bbase (se 6 (by rfl) ⟨21324, by rfl⟩ : syracuseStep 909845 = 42649) (by norm_num)
theorem B680501 : Blo 401768 680501 := bbase (se 5 (by rfl) ⟨31898, by rfl⟩ : syracuseStep 680501 = 63797) (by norm_num)
theorem B1368629 : Blo 401768 1368629 := bbase (se 5 (by rfl) ⟨64154, by rfl⟩ : syracuseStep 1368629 = 128309) (by norm_num)
theorem B909917 : Blo 401768 909917 := bbase (se 3 (by rfl) ⟨170609, by rfl⟩ : syracuseStep 909917 = 341219) (by norm_num)
theorem B909989 : Blo 401768 909989 := bbase (se 4 (by rfl) ⟨85311, by rfl⟩ : syracuseStep 909989 = 170623) (by norm_num)
theorem B680629 : Blo 401768 680629 := bbase (se 5 (by rfl) ⟨31904, by rfl⟩ : syracuseStep 680629 = 63809) (by norm_num)
theorem B910061 : Blo 401768 910061 := bbase (se 3 (by rfl) ⟨170636, by rfl⟩ : syracuseStep 910061 = 341273) (by norm_num)
theorem B680717 : Blo 401768 680717 := bbase (se 3 (by rfl) ⟨127634, by rfl⟩ : syracuseStep 680717 = 255269) (by norm_num)
theorem B910133 : Blo 401768 910133 := bbase (se 5 (by rfl) ⟨42662, by rfl⟩ : syracuseStep 910133 = 85325) (by norm_num)
theorem B910205 : Blo 401768 910205 := bbase (se 3 (by rfl) ⟨170663, by rfl⟩ : syracuseStep 910205 = 341327) (by norm_num)
theorem B680845 : Blo 401768 680845 := bbase (se 3 (by rfl) ⟨127658, by rfl⟩ : syracuseStep 680845 = 255317) (by norm_num)
theorem B910277 : Blo 401768 910277 := bbase (se 4 (by rfl) ⟨85338, by rfl⟩ : syracuseStep 910277 = 170677) (by norm_num)
theorem B680933 : Blo 401768 680933 := bbase (se 4 (by rfl) ⟨63837, by rfl⟩ : syracuseStep 680933 = 127675) (by norm_num)
theorem B1369061 : Blo 401768 1369061 := bbase (se 4 (by rfl) ⟨128349, by rfl⟩ : syracuseStep 1369061 = 256699) (by norm_num)
theorem B582661 : Blo 401768 582661 := bbase (se 4 (by rfl) ⟨54624, by rfl⟩ : syracuseStep 582661 = 109249) (by norm_num)
theorem B910349 : Blo 401768 910349 := bbase (se 3 (by rfl) ⟨170690, by rfl⟩ : syracuseStep 910349 = 341381) (by norm_num)
theorem B1532965 : Blo 401768 1532965 := bbase (se 4 (by rfl) ⟨143715, by rfl⟩ : syracuseStep 1532965 = 287431) (by norm_num)
theorem B615485 : Blo 401768 615485 := bbase (se 3 (by rfl) ⟨115403, by rfl⟩ : syracuseStep 615485 = 230807) (by norm_num)
theorem B910421 : Blo 401768 910421 := bbase (se 8 (by rfl) ⟨5334, by rfl⟩ : syracuseStep 910421 = 10669) (by norm_num)
theorem B681061 : Blo 401768 681061 := bbase (se 4 (by rfl) ⟨63849, by rfl⟩ : syracuseStep 681061 = 127699) (by norm_num)
theorem B910493 : Blo 401768 910493 := bbase (se 3 (by rfl) ⟨170717, by rfl⟩ : syracuseStep 910493 = 341435) (by norm_num)
theorem B681149 : Blo 401768 681149 := bbase (se 3 (by rfl) ⟨127715, by rfl⟩ : syracuseStep 681149 = 255431) (by norm_num)
theorem B910565 : Blo 401768 910565 := bbase (se 4 (by rfl) ⟨85365, by rfl⟩ : syracuseStep 910565 = 170731) (by norm_num)
theorem B484589 : Blo 401768 484589 := bbase (se 3 (by rfl) ⟨90860, by rfl⟩ : syracuseStep 484589 = 181721) (by norm_num)
theorem B1729781 : Blo 401768 1729781 := bbase (se 5 (by rfl) ⟨81083, by rfl⟩ : syracuseStep 1729781 = 162167) (by norm_num)
theorem B910637 : Blo 401768 910637 := bbase (se 3 (by rfl) ⟨170744, by rfl⟩ : syracuseStep 910637 = 341489) (by norm_num)
theorem B681277 : Blo 401768 681277 := bbase (se 3 (by rfl) ⟨127739, by rfl⟩ : syracuseStep 681277 = 255479) (by norm_num)
theorem B1402181 : Blo 401768 1402181 := bbase (se 4 (by rfl) ⟨131454, by rfl⟩ : syracuseStep 1402181 = 262909) (by norm_num)
theorem B1533269 : Blo 401768 1533269 := bbase (se 12 (by rfl) ⟨561, by rfl⟩ : syracuseStep 1533269 = 1123) (by norm_num)
theorem B910709 : Blo 401768 910709 := bbase (se 5 (by rfl) ⟨42689, by rfl⟩ : syracuseStep 910709 = 85379) (by norm_num)
theorem B779645 : Blo 401768 779645 := bbase (se 3 (by rfl) ⟨146183, by rfl⟩ : syracuseStep 779645 = 292367) (by norm_num)
theorem B681365 : Blo 401768 681365 := bbase (se 6 (by rfl) ⟨15969, by rfl⟩ : syracuseStep 681365 = 31939) (by norm_num)
theorem B451993 : Blo 401768 451993 := bbase (se 2 (by rfl) ⟨169497, by rfl⟩ : syracuseStep 451993 = 338995) (by norm_num)
theorem B452029 : Blo 401768 452029 := bbase (se 3 (by rfl) ⟨84755, by rfl⟩ : syracuseStep 452029 = 169511) (by norm_num)
theorem B910781 : Blo 401768 910781 := bbase (se 3 (by rfl) ⟨170771, by rfl⟩ : syracuseStep 910781 = 341543) (by norm_num)
theorem B452065 : Blo 401768 452065 := bbase (se 2 (by rfl) ⟨169524, by rfl⟩ : syracuseStep 452065 = 339049) (by norm_num)
theorem B452101 : Blo 401768 452101 := bbase (se 4 (by rfl) ⟨42384, by rfl⟩ : syracuseStep 452101 = 84769) (by norm_num)
theorem B910853 : Blo 401768 910853 := bbase (se 4 (by rfl) ⟨85392, by rfl⟩ : syracuseStep 910853 = 170785) (by norm_num)
theorem B681493 : Blo 401768 681493 := bbase (se 6 (by rfl) ⟨15972, by rfl⟩ : syracuseStep 681493 = 31945) (by norm_num)
theorem B452137 : Blo 401768 452137 := bbase (se 2 (by rfl) ⟨169551, by rfl⟩ : syracuseStep 452137 = 339103) (by norm_num)
theorem B517685 : Blo 401768 517685 := bbase (se 5 (by rfl) ⟨24266, by rfl⟩ : syracuseStep 517685 = 48533) (by norm_num)
theorem B4154933 : Blo 401768 4154933 := bbase (se 5 (by rfl) ⟨194762, by rfl⟩ : syracuseStep 4154933 = 389525) (by norm_num)
theorem B452173 : Blo 401768 452173 := bbase (se 3 (by rfl) ⟨84782, by rfl⟩ : syracuseStep 452173 = 169565) (by norm_num)
theorem B910925 : Blo 401768 910925 := bbase (se 3 (by rfl) ⟨170798, by rfl⟩ : syracuseStep 910925 = 341597) (by norm_num)
theorem B681581 : Blo 401768 681581 := bbase (se 3 (by rfl) ⟨127796, by rfl⟩ : syracuseStep 681581 = 255593) (by norm_num)
theorem B452209 : Blo 401768 452209 := bbase (se 2 (by rfl) ⟨169578, by rfl⟩ : syracuseStep 452209 = 339157) (by norm_num)
theorem B452245 : Blo 401768 452245 := bbase (se 6 (by rfl) ⟨10599, by rfl⟩ : syracuseStep 452245 = 21199) (by norm_num)
theorem B910997 : Blo 401768 910997 := bbase (se 6 (by rfl) ⟨21351, by rfl⟩ : syracuseStep 910997 = 42703) (by norm_num)
theorem B452281 : Blo 401768 452281 := bbase (se 2 (by rfl) ⟨169605, by rfl⟩ : syracuseStep 452281 = 339211) (by norm_num)
theorem B452317 : Blo 401768 452317 := bbase (se 3 (by rfl) ⟨84809, by rfl⟩ : syracuseStep 452317 = 169619) (by norm_num)
theorem B911069 : Blo 401768 911069 := bbase (se 3 (by rfl) ⟨170825, by rfl⟩ : syracuseStep 911069 = 341651) (by norm_num)
theorem B681709 : Blo 401768 681709 := bbase (se 3 (by rfl) ⟨127820, by rfl⟩ : syracuseStep 681709 = 255641) (by norm_num)
theorem B452353 : Blo 401768 452353 := bbase (se 2 (by rfl) ⟨169632, by rfl⟩ : syracuseStep 452353 = 339265) (by norm_num)
theorem B648989 : Blo 401768 648989 := bbase (se 3 (by rfl) ⟨121685, by rfl⟩ : syracuseStep 648989 = 243371) (by norm_num)
theorem B452389 : Blo 401768 452389 := bbase (se 4 (by rfl) ⟨42411, by rfl⟩ : syracuseStep 452389 = 84823) (by norm_num)
theorem B911141 : Blo 401768 911141 := bbase (se 4 (by rfl) ⟨85419, by rfl⟩ : syracuseStep 911141 = 170839) (by norm_num)
theorem B681797 : Blo 401768 681797 := bbase (se 4 (by rfl) ⟨63918, by rfl⟩ : syracuseStep 681797 = 127837) (by norm_num)
theorem B452425 : Blo 401768 452425 := bbase (se 2 (by rfl) ⟨169659, by rfl⟩ : syracuseStep 452425 = 339319) (by norm_num)
theorem B452461 : Blo 401768 452461 := bbase (se 3 (by rfl) ⟨84836, by rfl⟩ : syracuseStep 452461 = 169673) (by norm_num)
theorem B911213 : Blo 401768 911213 := bbase (se 3 (by rfl) ⟨170852, by rfl⟩ : syracuseStep 911213 = 341705) (by norm_num)
theorem B452497 : Blo 401768 452497 := bbase (se 2 (by rfl) ⟨169686, by rfl⟩ : syracuseStep 452497 = 339373) (by norm_num)
theorem B485281 : Blo 401768 485281 := bbase (se 2 (by rfl) ⟨181980, by rfl⟩ : syracuseStep 485281 = 363961) (by norm_num)
theorem B452533 : Blo 401768 452533 := bbase (se 5 (by rfl) ⟨21212, by rfl⟩ : syracuseStep 452533 = 42425) (by norm_num)
theorem B911285 : Blo 401768 911285 := bbase (se 5 (by rfl) ⟨42716, by rfl⟩ : syracuseStep 911285 = 85433) (by norm_num)
theorem B681925 : Blo 401768 681925 := bbase (se 4 (by rfl) ⟨63930, by rfl⟩ : syracuseStep 681925 = 127861) (by norm_num)
theorem B7858133 : Blo 401768 7858133 := bbase (se 7 (by rfl) ⟨92087, by rfl⟩ : syracuseStep 7858133 = 184175) (by norm_num)
theorem B452569 : Blo 401768 452569 := bbase (se 2 (by rfl) ⟨169713, by rfl⟩ : syracuseStep 452569 = 339427) (by norm_num)
theorem B649181 : Blo 401768 649181 := bbase (se 3 (by rfl) ⟨121721, by rfl⟩ : syracuseStep 649181 = 243443) (by norm_num)
theorem B452605 : Blo 401768 452605 := bbase (se 3 (by rfl) ⟨84863, by rfl⟩ : syracuseStep 452605 = 169727) (by norm_num)
theorem B911357 : Blo 401768 911357 := bbase (se 3 (by rfl) ⟨170879, by rfl⟩ : syracuseStep 911357 = 341759) (by norm_num)
theorem B682013 : Blo 401768 682013 := bbase (se 3 (by rfl) ⟨127877, by rfl⟩ : syracuseStep 682013 = 255755) (by norm_num)
theorem B452641 : Blo 401768 452641 := bbase (se 2 (by rfl) ⟨169740, by rfl⟩ : syracuseStep 452641 = 339481) (by norm_num)
theorem B452677 : Blo 401768 452677 := bbase (se 4 (by rfl) ⟨42438, by rfl⟩ : syracuseStep 452677 = 84877) (by norm_num)
theorem B911429 : Blo 401768 911429 := bbase (se 4 (by rfl) ⟨85446, by rfl⟩ : syracuseStep 911429 = 170893) (by norm_num)
theorem B649309 : Blo 401768 649309 := bbase (se 3 (by rfl) ⟨121745, by rfl⟩ : syracuseStep 649309 = 243491) (by norm_num)
theorem B452713 : Blo 401768 452713 := bbase (se 2 (by rfl) ⟨169767, by rfl⟩ : syracuseStep 452713 = 339535) (by norm_num)
theorem B485497 : Blo 401768 485497 := bbase (se 2 (by rfl) ⟨182061, by rfl⟩ : syracuseStep 485497 = 364123) (by norm_num)
theorem B452749 : Blo 401768 452749 := bbase (se 3 (by rfl) ⟨84890, by rfl⟩ : syracuseStep 452749 = 169781) (by norm_num)
theorem B911501 : Blo 401768 911501 := bbase (se 3 (by rfl) ⟨170906, by rfl⟩ : syracuseStep 911501 = 341813) (by norm_num)
theorem B682141 : Blo 401768 682141 := bbase (se 3 (by rfl) ⟨127901, by rfl⟩ : syracuseStep 682141 = 255803) (by norm_num)
theorem B452785 : Blo 401768 452785 := bbase (se 2 (by rfl) ⟨169794, by rfl⟩ : syracuseStep 452785 = 339589) (by norm_num)
theorem B452821 : Blo 401768 452821 := bbase (se 7 (by rfl) ⟨5306, by rfl⟩ : syracuseStep 452821 = 10613) (by norm_num)
theorem B911573 : Blo 401768 911573 := bbase (se 7 (by rfl) ⟨10682, by rfl⟩ : syracuseStep 911573 = 21365) (by norm_num)
theorem B682229 : Blo 401768 682229 := bbase (se 5 (by rfl) ⟨31979, by rfl⟩ : syracuseStep 682229 = 63959) (by norm_num)
theorem B452857 : Blo 401768 452857 := bbase (se 2 (by rfl) ⟨169821, by rfl⟩ : syracuseStep 452857 = 339643) (by norm_num)
theorem B452893 : Blo 401768 452893 := bbase (se 3 (by rfl) ⟨84917, by rfl⟩ : syracuseStep 452893 = 169835) (by norm_num)
theorem B911645 : Blo 401768 911645 := bbase (se 3 (by rfl) ⟨170933, by rfl⟩ : syracuseStep 911645 = 341867) (by norm_num)
theorem B452929 : Blo 401768 452929 := bbase (se 2 (by rfl) ⟨169848, by rfl⟩ : syracuseStep 452929 = 339697) (by norm_num)
theorem B452965 : Blo 401768 452965 := bbase (se 4 (by rfl) ⟨42465, by rfl⟩ : syracuseStep 452965 = 84931) (by norm_num)
theorem B911717 : Blo 401768 911717 := bbase (se 4 (by rfl) ⟨85473, by rfl⟩ : syracuseStep 911717 = 170947) (by norm_num)
theorem B780653 : Blo 401768 780653 := bbase (se 3 (by rfl) ⟨146372, by rfl⟩ : syracuseStep 780653 = 292745) (by norm_num)
theorem B682357 : Blo 401768 682357 := bbase (se 5 (by rfl) ⟨31985, by rfl⟩ : syracuseStep 682357 = 63971) (by norm_num)
theorem B453001 : Blo 401768 453001 := bbase (se 2 (by rfl) ⟨169875, by rfl⟩ : syracuseStep 453001 = 339751) (by norm_num)
theorem B518557 : Blo 401768 518557 := bbase (se 3 (by rfl) ⟨97229, by rfl⟩ : syracuseStep 518557 = 194459) (by norm_num)
theorem B453037 : Blo 401768 453037 := bbase (se 3 (by rfl) ⟨84944, by rfl⟩ : syracuseStep 453037 = 169889) (by norm_num)
theorem B911789 : Blo 401768 911789 := bbase (se 3 (by rfl) ⟨170960, by rfl⟩ : syracuseStep 911789 = 341921) (by norm_num)
theorem B682445 : Blo 401768 682445 := bbase (se 3 (by rfl) ⟨127958, by rfl⟩ : syracuseStep 682445 = 255917) (by norm_num)
theorem B453073 : Blo 401768 453073 := bbase (se 2 (by rfl) ⟨169902, by rfl⟩ : syracuseStep 453073 = 339805) (by norm_num)
theorem B453109 : Blo 401768 453109 := bbase (se 5 (by rfl) ⟨21239, by rfl⟩ : syracuseStep 453109 = 42479) (by norm_num)
theorem B911861 : Blo 401768 911861 := bbase (se 5 (by rfl) ⟨42743, by rfl⟩ : syracuseStep 911861 = 85487) (by norm_num)
theorem B453145 : Blo 401768 453145 := bbase (se 2 (by rfl) ⟨169929, by rfl⟩ : syracuseStep 453145 = 339859) (by norm_num)
theorem B453181 : Blo 401768 453181 := bbase (se 3 (by rfl) ⟨84971, by rfl⟩ : syracuseStep 453181 = 169943) (by norm_num)
theorem B911933 : Blo 401768 911933 := bbase (se 3 (by rfl) ⟨170987, by rfl⟩ : syracuseStep 911933 = 341975) (by norm_num)
theorem B682573 : Blo 401768 682573 := bbase (se 3 (by rfl) ⟨127982, by rfl⟩ : syracuseStep 682573 = 255965) (by norm_num)
theorem B453217 : Blo 401768 453217 := bbase (se 2 (by rfl) ⟨169956, by rfl⟩ : syracuseStep 453217 = 339913) (by norm_num)
theorem B453253 : Blo 401768 453253 := bbase (se 4 (by rfl) ⟨42492, by rfl⟩ : syracuseStep 453253 = 84985) (by norm_num)
theorem B912005 : Blo 401768 912005 := bbase (se 4 (by rfl) ⟨85500, by rfl⟩ : syracuseStep 912005 = 171001) (by norm_num)
theorem B682661 : Blo 401768 682661 := bbase (se 4 (by rfl) ⟨63999, by rfl⟩ : syracuseStep 682661 = 127999) (by norm_num)
theorem B453289 : Blo 401768 453289 := bbase (se 2 (by rfl) ⟨169983, by rfl⟩ : syracuseStep 453289 = 339967) (by norm_num)
theorem B453325 : Blo 401768 453325 := bbase (se 3 (by rfl) ⟨84998, by rfl⟩ : syracuseStep 453325 = 169997) (by norm_num)
theorem B912077 : Blo 401768 912077 := bbase (se 3 (by rfl) ⟨171014, by rfl⟩ : syracuseStep 912077 = 342029) (by norm_num)
theorem B649949 : Blo 401768 649949 := bbase (se 3 (by rfl) ⟨121865, by rfl⟩ : syracuseStep 649949 = 243731) (by norm_num)
theorem B453361 : Blo 401768 453361 := bbase (se 2 (by rfl) ⟨170010, by rfl⟩ : syracuseStep 453361 = 340021) (by norm_num)
theorem B453397 : Blo 401768 453397 := bbase (se 6 (by rfl) ⟨10626, by rfl⟩ : syracuseStep 453397 = 21253) (by norm_num)
theorem B912149 : Blo 401768 912149 := bbase (se 6 (by rfl) ⟨21378, by rfl⟩ : syracuseStep 912149 = 42757) (by norm_num)
theorem B682789 : Blo 401768 682789 := bbase (se 4 (by rfl) ⟨64011, by rfl⟩ : syracuseStep 682789 = 128023) (by norm_num)
theorem B453433 : Blo 401768 453433 := bbase (se 2 (by rfl) ⟨170037, by rfl⟩ : syracuseStep 453433 = 340075) (by norm_num)
theorem B453469 : Blo 401768 453469 := bbase (se 3 (by rfl) ⟨85025, by rfl⟩ : syracuseStep 453469 = 170051) (by norm_num)
theorem B912221 : Blo 401768 912221 := bbase (se 3 (by rfl) ⟨171041, by rfl⟩ : syracuseStep 912221 = 342083) (by norm_num)
theorem B682877 : Blo 401768 682877 := bbase (se 3 (by rfl) ⟨128039, by rfl⟩ : syracuseStep 682877 = 256079) (by norm_num)
theorem B453505 : Blo 401768 453505 := bbase (se 2 (by rfl) ⟨170064, by rfl⟩ : syracuseStep 453505 = 340129) (by norm_num)
theorem B453541 : Blo 401768 453541 := bbase (se 4 (by rfl) ⟨42519, by rfl⟩ : syracuseStep 453541 = 85039) (by norm_num)
theorem B912293 : Blo 401768 912293 := bbase (se 4 (by rfl) ⟨85527, by rfl⟩ : syracuseStep 912293 = 171055) (by norm_num)
theorem B453577 : Blo 401768 453577 := bbase (se 2 (by rfl) ⟨170091, by rfl⟩ : syracuseStep 453577 = 340183) (by norm_num)
theorem B2190293 : Blo 401768 2190293 := bbase (se 7 (by rfl) ⟨25667, by rfl⟩ : syracuseStep 2190293 = 51335) (by norm_num)
theorem B1731557 : Blo 401768 1731557 := bbase (se 4 (by rfl) ⟨162333, by rfl⟩ : syracuseStep 1731557 = 324667) (by norm_num)
theorem B453613 : Blo 401768 453613 := bbase (se 3 (by rfl) ⟨85052, by rfl⟩ : syracuseStep 453613 = 170105) (by norm_num)
theorem B912365 : Blo 401768 912365 := bbase (se 3 (by rfl) ⟨171068, by rfl⟩ : syracuseStep 912365 = 342137) (by norm_num)
theorem B683005 : Blo 401768 683005 := bbase (se 3 (by rfl) ⟨128063, by rfl⟩ : syracuseStep 683005 = 256127) (by norm_num)
theorem B453649 : Blo 401768 453649 := bbase (se 2 (by rfl) ⟨170118, by rfl⟩ : syracuseStep 453649 = 340237) (by norm_num)
theorem B453685 : Blo 401768 453685 := bbase (se 5 (by rfl) ⟨21266, by rfl⟩ : syracuseStep 453685 = 42533) (by norm_num)
theorem B912437 : Blo 401768 912437 := bbase (se 5 (by rfl) ⟨42770, by rfl⟩ : syracuseStep 912437 = 85541) (by norm_num)
theorem B519229 : Blo 401768 519229 := bbase (se 3 (by rfl) ⟨97355, by rfl⟩ : syracuseStep 519229 = 194711) (by norm_num)
theorem B683093 : Blo 401768 683093 := bbase (se 8 (by rfl) ⟨4002, by rfl⟩ : syracuseStep 683093 = 8005) (by norm_num)
theorem B453721 : Blo 401768 453721 := bbase (se 2 (by rfl) ⟨170145, by rfl⟩ : syracuseStep 453721 = 340291) (by norm_num)
theorem B453757 : Blo 401768 453757 := bbase (se 3 (by rfl) ⟨85079, by rfl⟩ : syracuseStep 453757 = 170159) (by norm_num)
theorem B912509 : Blo 401768 912509 := bbase (se 3 (by rfl) ⟨171095, by rfl⟩ : syracuseStep 912509 = 342191) (by norm_num)
theorem B453793 : Blo 401768 453793 := bbase (se 2 (by rfl) ⟨170172, by rfl⟩ : syracuseStep 453793 = 340345) (by norm_num)
theorem B453829 : Blo 401768 453829 := bbase (se 4 (by rfl) ⟨42546, by rfl⟩ : syracuseStep 453829 = 85093) (by norm_num)
theorem B912581 : Blo 401768 912581 := bbase (se 4 (by rfl) ⟨85554, by rfl⟩ : syracuseStep 912581 = 171109) (by norm_num)
theorem B683221 : Blo 401768 683221 := bbase (se 7 (by rfl) ⟨8006, by rfl⟩ : syracuseStep 683221 = 16013) (by norm_num)
theorem B453865 : Blo 401768 453865 := bbase (se 2 (by rfl) ⟨170199, by rfl⟩ : syracuseStep 453865 = 340399) (by norm_num)
theorem B453901 : Blo 401768 453901 := bbase (se 3 (by rfl) ⟨85106, by rfl⟩ : syracuseStep 453901 = 170213) (by norm_num)
theorem B912653 : Blo 401768 912653 := bbase (se 3 (by rfl) ⟨171122, by rfl⟩ : syracuseStep 912653 = 342245) (by norm_num)
theorem B683309 : Blo 401768 683309 := bbase (se 3 (by rfl) ⟨128120, by rfl⟩ : syracuseStep 683309 = 256241) (by norm_num)
theorem B453937 : Blo 401768 453937 := bbase (se 2 (by rfl) ⟨170226, by rfl⟩ : syracuseStep 453937 = 340453) (by norm_num)
theorem B453973 : Blo 401768 453973 := bbase (se 11 (by rfl) ⟨332, by rfl⟩ : syracuseStep 453973 = 665) (by norm_num)
theorem B912725 : Blo 401768 912725 := bbase (se 11 (by rfl) ⟨668, by rfl⟩ : syracuseStep 912725 = 1337) (by norm_num)
theorem B454009 : Blo 401768 454009 := bbase (se 2 (by rfl) ⟨170253, by rfl⟩ : syracuseStep 454009 = 340507) (by norm_num)
theorem B1535381 : Blo 401768 1535381 := bbase (se 6 (by rfl) ⟨35985, by rfl⟩ : syracuseStep 1535381 = 71971) (by norm_num)
theorem B454045 : Blo 401768 454045 := bbase (se 3 (by rfl) ⟨85133, by rfl⟩ : syracuseStep 454045 = 170267) (by norm_num)
theorem B912797 : Blo 401768 912797 := bbase (se 3 (by rfl) ⟨171149, by rfl⟩ : syracuseStep 912797 = 342299) (by norm_num)
theorem B683437 : Blo 401768 683437 := bbase (se 3 (by rfl) ⟨128144, by rfl⟩ : syracuseStep 683437 = 256289) (by norm_num)
theorem B454081 : Blo 401768 454081 := bbase (se 2 (by rfl) ⟨170280, by rfl⟩ : syracuseStep 454081 = 340561) (by norm_num)
theorem B454117 : Blo 401768 454117 := bbase (se 4 (by rfl) ⟨42573, by rfl⟩ : syracuseStep 454117 = 85147) (by norm_num)
theorem B912869 : Blo 401768 912869 := bbase (se 4 (by rfl) ⟨85581, by rfl⟩ : syracuseStep 912869 = 171163) (by norm_num)
theorem B683525 : Blo 401768 683525 := bbase (se 4 (by rfl) ⟨64080, by rfl⟩ : syracuseStep 683525 = 128161) (by norm_num)
theorem B454153 : Blo 401768 454153 := bbase (se 2 (by rfl) ⟨170307, by rfl⟩ : syracuseStep 454153 = 340615) (by norm_num)
theorem B454189 : Blo 401768 454189 := bbase (se 3 (by rfl) ⟨85160, by rfl⟩ : syracuseStep 454189 = 170321) (by norm_num)
theorem B912941 : Blo 401768 912941 := bbase (se 3 (by rfl) ⟨171176, by rfl⟩ : syracuseStep 912941 = 342353) (by norm_num)
theorem B454225 : Blo 401768 454225 := bbase (se 2 (by rfl) ⟨170334, by rfl⟩ : syracuseStep 454225 = 340669) (by norm_num)
theorem B454261 : Blo 401768 454261 := bbase (se 5 (by rfl) ⟨21293, by rfl⟩ : syracuseStep 454261 = 42587) (by norm_num)
theorem B683653 : Blo 401768 683653 := bbase (se 4 (by rfl) ⟨64092, by rfl⟩ : syracuseStep 683653 = 128185) (by norm_num)
theorem B454297 : Blo 401768 454297 := bbase (se 2 (by rfl) ⟨170361, by rfl⟩ : syracuseStep 454297 = 340723) (by norm_num)
theorem B1535669 : Blo 401768 1535669 := bbase (se 5 (by rfl) ⟨71984, by rfl⟩ : syracuseStep 1535669 = 143969) (by norm_num)
theorem B454333 : Blo 401768 454333 := bbase (se 3 (by rfl) ⟨85187, by rfl⟩ : syracuseStep 454333 = 170375) (by norm_num)
theorem B683741 : Blo 401768 683741 := bbase (se 3 (by rfl) ⟨128201, by rfl⟩ : syracuseStep 683741 = 256403) (by norm_num)
theorem B454369 : Blo 401768 454369 := bbase (se 2 (by rfl) ⟨170388, by rfl⟩ : syracuseStep 454369 = 340777) (by norm_num)
theorem B454405 : Blo 401768 454405 := bbase (se 4 (by rfl) ⟨42600, by rfl⟩ : syracuseStep 454405 = 85201) (by norm_num)
theorem B487193 : Blo 401768 487193 := bbase (se 2 (by rfl) ⟨182697, by rfl⟩ : syracuseStep 487193 = 365395) (by norm_num)
theorem B454441 : Blo 401768 454441 := bbase (se 2 (by rfl) ⟨170415, by rfl⟩ : syracuseStep 454441 = 340831) (by norm_num)
theorem B3075893 : Blo 401768 3075893 := bbase (se 5 (by rfl) ⟨144182, by rfl⟩ : syracuseStep 3075893 = 288365) (by norm_num)
theorem B454477 : Blo 401768 454477 := bbase (se 3 (by rfl) ⟨85214, by rfl⟩ : syracuseStep 454477 = 170429) (by norm_num)
theorem B683869 : Blo 401768 683869 := bbase (se 3 (by rfl) ⟨128225, by rfl⟩ : syracuseStep 683869 = 256451) (by norm_num)
theorem B454513 : Blo 401768 454513 := bbase (se 2 (by rfl) ⟨170442, by rfl⟩ : syracuseStep 454513 = 340885) (by norm_num)
theorem B454549 : Blo 401768 454549 := bbase (se 6 (by rfl) ⟨10653, by rfl⟩ : syracuseStep 454549 = 21307) (by norm_num)
theorem B683957 : Blo 401768 683957 := bbase (se 5 (by rfl) ⟨32060, by rfl⟩ : syracuseStep 683957 = 64121) (by norm_num)
theorem B454585 : Blo 401768 454585 := bbase (se 2 (by rfl) ⟨170469, by rfl⟩ : syracuseStep 454585 = 340939) (by norm_num)
theorem B1732549 : Blo 401768 1732549 := bbase (se 4 (by rfl) ⟨162426, by rfl⟩ : syracuseStep 1732549 = 324853) (by norm_num)
theorem B454621 : Blo 401768 454621 := bbase (se 3 (by rfl) ⟨85241, by rfl⟩ : syracuseStep 454621 = 170483) (by norm_num)
theorem B487405 : Blo 401768 487405 := bbase (se 3 (by rfl) ⟨91388, by rfl⟩ : syracuseStep 487405 = 182777) (by norm_num)
theorem B2289653 : Blo 401768 2289653 := bbase (se 5 (by rfl) ⟨107327, by rfl⟩ : syracuseStep 2289653 = 214655) (by norm_num)
theorem B454657 : Blo 401768 454657 := bbase (se 2 (by rfl) ⟨170496, by rfl⟩ : syracuseStep 454657 = 340993) (by norm_num)
theorem B815125 : Blo 401768 815125 := bbase (se 6 (by rfl) ⟨19104, by rfl⟩ : syracuseStep 815125 = 38209) (by norm_num)
theorem B454693 : Blo 401768 454693 := bbase (se 4 (by rfl) ⟨42627, by rfl⟩ : syracuseStep 454693 = 85255) (by norm_num)
theorem B684085 : Blo 401768 684085 := bbase (se 5 (by rfl) ⟨32066, by rfl⟩ : syracuseStep 684085 = 64133) (by norm_num)
theorem B454729 : Blo 401768 454729 := bbase (se 2 (by rfl) ⟨170523, by rfl⟩ : syracuseStep 454729 = 341047) (by norm_num)
theorem B454765 : Blo 401768 454765 := bbase (se 3 (by rfl) ⟨85268, by rfl⟩ : syracuseStep 454765 = 170537) (by norm_num)
theorem B684173 : Blo 401768 684173 := bbase (se 3 (by rfl) ⟨128282, by rfl⟩ : syracuseStep 684173 = 256565) (by norm_num)
theorem B454801 : Blo 401768 454801 := bbase (se 2 (by rfl) ⟨170550, by rfl⟩ : syracuseStep 454801 = 341101) (by norm_num)
theorem B454837 : Blo 401768 454837 := bbase (se 5 (by rfl) ⟨21320, by rfl⟩ : syracuseStep 454837 = 42641) (by norm_num)
theorem B454873 : Blo 401768 454873 := bbase (se 2 (by rfl) ⟨170577, by rfl⟩ : syracuseStep 454873 = 341155) (by norm_num)
theorem B454909 : Blo 401768 454909 := bbase (se 3 (by rfl) ⟨85295, by rfl⟩ : syracuseStep 454909 = 170591) (by norm_num)
theorem B684301 : Blo 401768 684301 := bbase (se 3 (by rfl) ⟨128306, by rfl⟩ : syracuseStep 684301 = 256613) (by norm_num)
theorem B454945 : Blo 401768 454945 := bbase (se 2 (by rfl) ⟨170604, by rfl⟩ : syracuseStep 454945 = 341209) (by norm_num)
theorem B454981 : Blo 401768 454981 := bbase (se 4 (by rfl) ⟨42654, by rfl⟩ : syracuseStep 454981 = 85309) (by norm_num)
theorem B684389 : Blo 401768 684389 := bbase (se 4 (by rfl) ⟨64161, by rfl⟩ : syracuseStep 684389 = 128323) (by norm_num)
theorem B455017 : Blo 401768 455017 := bbase (se 2 (by rfl) ⟨170631, by rfl⟩ : syracuseStep 455017 = 341263) (by norm_num)
theorem B455053 : Blo 401768 455053 := bbase (se 3 (by rfl) ⟨85322, by rfl⟩ : syracuseStep 455053 = 170645) (by norm_num)
theorem B455089 : Blo 401768 455089 := bbase (se 2 (by rfl) ⟨170658, by rfl⟩ : syracuseStep 455089 = 341317) (by norm_num)
theorem B455125 : Blo 401768 455125 := bbase (se 7 (by rfl) ⟨5333, by rfl⟩ : syracuseStep 455125 = 10667) (by norm_num)
theorem B684517 : Blo 401768 684517 := bbase (se 4 (by rfl) ⟨64173, by rfl⟩ : syracuseStep 684517 = 128347) (by norm_num)
theorem B455161 : Blo 401768 455161 := bbase (se 2 (by rfl) ⟨170685, by rfl⟩ : syracuseStep 455161 = 341371) (by norm_num)
theorem B455197 : Blo 401768 455197 := bbase (se 3 (by rfl) ⟨85349, by rfl⟩ : syracuseStep 455197 = 170699) (by norm_num)
theorem B684605 : Blo 401768 684605 := bbase (se 3 (by rfl) ⟨128363, by rfl⟩ : syracuseStep 684605 = 256727) (by norm_num)
theorem B455233 : Blo 401768 455233 := bbase (se 2 (by rfl) ⟨170712, by rfl⟩ : syracuseStep 455233 = 341425) (by norm_num)
theorem B455269 : Blo 401768 455269 := bbase (se 4 (by rfl) ⟨42681, by rfl⟩ : syracuseStep 455269 = 85363) (by norm_num)
theorem B455305 : Blo 401768 455305 := bbase (se 2 (by rfl) ⟨170739, by rfl⟩ : syracuseStep 455305 = 341479) (by norm_num)
theorem B455341 : Blo 401768 455341 := bbase (se 3 (by rfl) ⟨85376, by rfl⟩ : syracuseStep 455341 = 170753) (by norm_num)
theorem B684733 : Blo 401768 684733 := bbase (se 3 (by rfl) ⟨128387, by rfl⟩ : syracuseStep 684733 = 256775) (by norm_num)
theorem B455377 : Blo 401768 455377 := bbase (se 2 (by rfl) ⟨170766, by rfl⟩ : syracuseStep 455377 = 341533) (by norm_num)
theorem B455413 : Blo 401768 455413 := bbase (se 5 (by rfl) ⟨21347, by rfl⟩ : syracuseStep 455413 = 42695) (by norm_num)
theorem B455449 : Blo 401768 455449 := bbase (se 2 (by rfl) ⟨170793, by rfl⟩ : syracuseStep 455449 = 341587) (by norm_num)
theorem B455485 : Blo 401768 455485 := bbase (se 3 (by rfl) ⟨85403, by rfl⟩ : syracuseStep 455485 = 170807) (by norm_num)
theorem B1536853 : Blo 401768 1536853 := bbase (se 9 (by rfl) ⟨4502, by rfl⟩ : syracuseStep 1536853 = 9005) (by norm_num)
theorem B455521 : Blo 401768 455521 := bbase (se 2 (by rfl) ⟨170820, by rfl⟩ : syracuseStep 455521 = 341641) (by norm_num)
theorem B2749301 : Blo 401768 2749301 := bbase (se 5 (by rfl) ⟨128873, by rfl⟩ : syracuseStep 2749301 = 257747) (by norm_num)
theorem B455557 : Blo 401768 455557 := bbase (se 4 (by rfl) ⟨42708, by rfl⟩ : syracuseStep 455557 = 85417) (by norm_num)
theorem B455593 : Blo 401768 455593 := bbase (se 2 (by rfl) ⟨170847, by rfl⟩ : syracuseStep 455593 = 341695) (by norm_num)
theorem B455629 : Blo 401768 455629 := bbase (se 3 (by rfl) ⟨85430, by rfl⟩ : syracuseStep 455629 = 170861) (by norm_num)
theorem B455665 : Blo 401768 455665 := bbase (se 2 (by rfl) ⟨170874, by rfl⟩ : syracuseStep 455665 = 341749) (by norm_num)
theorem B455701 : Blo 401768 455701 := bbase (se 6 (by rfl) ⟨10680, by rfl⟩ : syracuseStep 455701 = 21361) (by norm_num)
theorem B455737 : Blo 401768 455737 := bbase (se 2 (by rfl) ⟨170901, by rfl⟩ : syracuseStep 455737 = 341803) (by norm_num)
theorem B455773 : Blo 401768 455773 := bbase (se 3 (by rfl) ⟨85457, by rfl⟩ : syracuseStep 455773 = 170915) (by norm_num)
theorem B455809 : Blo 401768 455809 := bbase (se 2 (by rfl) ⟨170928, by rfl⟩ : syracuseStep 455809 = 341857) (by norm_num)
theorem B1537157 : Blo 401768 1537157 := bbase (se 4 (by rfl) ⟨144108, by rfl⟩ : syracuseStep 1537157 = 288217) (by norm_num)
theorem B455845 : Blo 401768 455845 := bbase (se 4 (by rfl) ⟨42735, by rfl⟩ : syracuseStep 455845 = 85471) (by norm_num)
theorem B455881 : Blo 401768 455881 := bbase (se 2 (by rfl) ⟨170955, by rfl⟩ : syracuseStep 455881 = 341911) (by norm_num)
theorem B816365 : Blo 401768 816365 := bbase (se 3 (by rfl) ⟨153068, by rfl⟩ : syracuseStep 816365 = 306137) (by norm_num)
theorem B455917 : Blo 401768 455917 := bbase (se 3 (by rfl) ⟨85484, by rfl⟩ : syracuseStep 455917 = 170969) (by norm_num)
theorem B455953 : Blo 401768 455953 := bbase (se 2 (by rfl) ⟨170982, by rfl⟩ : syracuseStep 455953 = 341965) (by norm_num)
theorem B455989 : Blo 401768 455989 := bbase (se 5 (by rfl) ⟨21374, by rfl⟩ : syracuseStep 455989 = 42749) (by norm_num)
theorem B456025 : Blo 401768 456025 := bbase (se 2 (by rfl) ⟨171009, by rfl⟩ : syracuseStep 456025 = 342019) (by norm_num)
theorem B456061 : Blo 401768 456061 := bbase (se 3 (by rfl) ⟨85511, by rfl⟩ : syracuseStep 456061 = 171023) (by norm_num)
theorem B456097 : Blo 401768 456097 := bbase (se 2 (by rfl) ⟨171036, by rfl⟩ : syracuseStep 456097 = 342073) (by norm_num)
theorem B456133 : Blo 401768 456133 := bbase (se 4 (by rfl) ⟨42762, by rfl⟩ : syracuseStep 456133 = 85525) (by norm_num)
theorem B456169 : Blo 401768 456169 := bbase (se 2 (by rfl) ⟨171063, by rfl⟩ : syracuseStep 456169 = 342127) (by norm_num)
theorem B456205 : Blo 401768 456205 := bbase (se 3 (by rfl) ⟨85538, by rfl⟩ : syracuseStep 456205 = 171077) (by norm_num)
theorem B456241 : Blo 401768 456241 := bbase (se 2 (by rfl) ⟨171090, by rfl⟩ : syracuseStep 456241 = 342181) (by norm_num)
theorem B456277 : Blo 401768 456277 := bbase (se 8 (by rfl) ⟨2673, by rfl⟩ : syracuseStep 456277 = 5347) (by norm_num)
theorem B456313 : Blo 401768 456313 := bbase (se 2 (by rfl) ⟨171117, by rfl⟩ : syracuseStep 456313 = 342235) (by norm_num)
theorem B456349 : Blo 401768 456349 := bbase (se 3 (by rfl) ⟨85565, by rfl⟩ : syracuseStep 456349 = 171131) (by norm_num)
theorem B456385 : Blo 401768 456385 := bbase (se 2 (by rfl) ⟨171144, by rfl⟩ : syracuseStep 456385 = 342289) (by norm_num)
theorem B456421 : Blo 401768 456421 := bbase (se 4 (by rfl) ⟨42789, by rfl⟩ : syracuseStep 456421 = 85579) (by norm_num)
theorem B456457 : Blo 401768 456457 := bbase (se 2 (by rfl) ⟨171171, by rfl⟩ : syracuseStep 456457 = 342343) (by norm_num)
theorem B2193493 : Blo 401768 2193493 := bbase (se 8 (by rfl) ⟨12852, by rfl⟩ : syracuseStep 2193493 = 25705) (by norm_num)
theorem B1374661 : Blo 401768 1374661 := bbase (se 4 (by rfl) ⟨128874, by rfl⟩ : syracuseStep 1374661 = 257749) (by norm_num)
theorem B948893 : Blo 401768 948893 := bbase (se 3 (by rfl) ⟨177917, by rfl⟩ : syracuseStep 948893 = 355835) (by norm_num)
theorem B818149 : Blo 401768 818149 := bbase (se 4 (by rfl) ⟨76701, by rfl⟩ : syracuseStep 818149 = 153403) (by norm_num)
theorem B1539269 : Blo 401768 1539269 := bbase (se 4 (by rfl) ⟨144306, by rfl⟩ : syracuseStep 1539269 = 288613) (by norm_num)
theorem B1539557 : Blo 401768 1539557 := bbase (se 4 (by rfl) ⟨144333, by rfl⟩ : syracuseStep 1539557 = 288667) (by norm_num)
theorem B2588213 : Blo 401768 2588213 := bbase (se 5 (by rfl) ⟨121322, by rfl⟩ : syracuseStep 2588213 = 242645) (by norm_num)
theorem B458329 : Blo 401768 458329 := bbase (se 2 (by rfl) ⟨171873, by rfl⟩ : syracuseStep 458329 = 343747) (by norm_num)
theorem B1146581 : Blo 401768 1146581 := bbase (se 7 (by rfl) ⟨13436, by rfl⟩ : syracuseStep 1146581 = 26873) (by norm_num)
theorem B917237 : Blo 401768 917237 := bbase (se 5 (by rfl) ⟨42995, by rfl⟩ : syracuseStep 917237 = 85991) (by norm_num)
theorem B1310453 : Blo 401768 1310453 := bbase (se 5 (by rfl) ⟨61427, by rfl⟩ : syracuseStep 1310453 = 122855) (by norm_num)
theorem B1310833 : Blo 401768 1310833 := bstep (se 2 (by rfl) ⟨491562, by rfl⟩ : syracuseStep 1310833 = 983125) B983125
theorem B4915313 : Blo 401768 4915313 := bstep (se 2 (by rfl) ⟨1843242, by rfl⟩ : syracuseStep 4915313 = 3686485) B3686485
theorem B4620401 : Blo 401768 4620401 := bstep (se 2 (by rfl) ⟨1732650, by rfl⟩ : syracuseStep 4620401 = 3465301) B3465301
theorem B2064781 : Blo 401768 2064781 := bstep (se 3 (by rfl) ⟨387146, by rfl⟩ : syracuseStep 2064781 = 774293) B774293
theorem B426403 : Blo 401768 426403 := bstep (se 1 (by rfl) ⟨319802, by rfl⟩ : syracuseStep 426403 = 639605) B639605
theorem B1540529 : Blo 401768 1540529 := bstep (se 2 (by rfl) ⟨577698, by rfl⟩ : syracuseStep 1540529 = 1155397) B1155397
theorem B2458147 : Blo 401768 2458147 := bstep (se 1 (by rfl) ⟨1843610, by rfl⟩ : syracuseStep 2458147 = 3687221) B3687221
theorem B2589317 : Blo 401768 2589317 := bstep (se 4 (by rfl) ⟨242748, by rfl⟩ : syracuseStep 2589317 = 485497) B485497
theorem B1147537 : Blo 401768 1147537 := bstep (se 2 (by rfl) ⟨430326, by rfl⟩ : syracuseStep 1147537 = 860653) B860653
theorem B1639217 : Blo 401768 1639217 := bstep (se 2 (by rfl) ⟨614706, by rfl⟩ : syracuseStep 1639217 = 1229413) B1229413
theorem B1016995 : Blo 401768 1016995 := bstep (se 1 (by rfl) ⟨762746, by rfl⟩ : syracuseStep 1016995 = 1525493) B1525493
theorem B2295053 : Blo 401768 2295053 := bstep (se 3 (by rfl) ⟨430322, by rfl⟩ : syracuseStep 2295053 = 860645) B860645
theorem B1017137 : Blo 401768 1017137 := bstep (se 2 (by rfl) ⟨381426, by rfl⟩ : syracuseStep 1017137 = 762853) B762853
theorem B656947 : Blo 401768 656947 := bstep (se 1 (by rfl) ⟨492710, by rfl⟩ : syracuseStep 656947 = 985421) B985421
theorem B1148813 : Blo 401768 1148813 := bstep (se 3 (by rfl) ⟨215402, by rfl⟩ : syracuseStep 1148813 = 430805) B430805
theorem B1312753 : Blo 401768 1312753 := bstep (se 2 (by rfl) ⟨492282, by rfl⟩ : syracuseStep 1312753 = 984565) B984565
theorem B1148995 : Blo 401768 1148995 := bstep (se 1 (by rfl) ⟨861746, by rfl⟩ : syracuseStep 1148995 = 1723493) B1723493
theorem B1149041 : Blo 401768 1149041 := bstep (se 2 (by rfl) ⟨430890, by rfl⟩ : syracuseStep 1149041 = 861781) B861781
theorem B2295985 : Blo 401768 2295985 := bstep (se 2 (by rfl) ⟨860994, by rfl⟩ : syracuseStep 2295985 = 1721989) B1721989
theorem B1018129 : Blo 401768 1018129 := bstep (se 2 (by rfl) ⟨381798, by rfl⟩ : syracuseStep 1018129 = 763597) B763597
theorem B1181969 : Blo 401768 1181969 := bstep (se 2 (by rfl) ⟨443238, by rfl⟩ : syracuseStep 1181969 = 886477) B886477
theorem B788977 : Blo 401768 788977 := bstep (se 2 (by rfl) ⟨295866, by rfl⟩ : syracuseStep 788977 = 591733) B591733
theorem B1018403 : Blo 401768 1018403 := bstep (se 1 (by rfl) ⟨763802, by rfl⟩ : syracuseStep 1018403 = 1527605) B1527605
theorem B1018595 : Blo 401768 1018595 := bstep (se 1 (by rfl) ⟨763946, by rfl⟩ : syracuseStep 1018595 = 1527893) B1527893
theorem B1936163 : Blo 401768 1936163 := bstep (se 1 (by rfl) ⟨1452122, by rfl⟩ : syracuseStep 1936163 = 2904245) B2904245
theorem B1641293 : Blo 401768 1641293 := bstep (se 3 (by rfl) ⟨307742, by rfl⟩ : syracuseStep 1641293 = 615485) B615485
theorem B5180273 : Blo 401768 5180273 := bstep (se 2 (by rfl) ⟨1942602, by rfl⟩ : syracuseStep 5180273 = 3885205) B3885205
theorem B1641329 : Blo 401768 1641329 := bstep (se 2 (by rfl) ⟨615498, by rfl⟩ : syracuseStep 1641329 = 1230997) B1230997
theorem B2460557 : Blo 401768 2460557 := bstep (se 3 (by rfl) ⟨461354, by rfl⟩ : syracuseStep 2460557 = 922709) B922709
theorem B691409 : Blo 401768 691409 := bstep (se 2 (by rfl) ⟨259278, by rfl⟩ : syracuseStep 691409 = 518557) B518557
theorem B2035043 : Blo 401768 2035043 := bstep (se 1 (by rfl) ⟨1526282, by rfl⟩ : syracuseStep 2035043 = 3052565) B3052565
theorem B1936817 : Blo 401768 1936817 := bstep (se 2 (by rfl) ⟨726306, by rfl⟩ : syracuseStep 1936817 = 1452613) B1452613
theorem B4656565 : Blo 401768 4656565 := bstep (se 5 (by rfl) ⟨218276, by rfl⟩ : syracuseStep 4656565 = 436553) B436553
theorem B2788835 : Blo 401768 2788835 := bstep (se 1 (by rfl) ⟨2091626, by rfl⟩ : syracuseStep 2788835 = 4183253) B4183253
theorem B429571 : Blo 401768 429571 := bstep (se 1 (by rfl) ⟨322178, by rfl⟩ : syracuseStep 429571 = 644357) B644357
theorem B3673613 : Blo 401768 3673613 := bstep (se 3 (by rfl) ⟨688802, by rfl⟩ : syracuseStep 3673613 = 1377605) B1377605
theorem B1150499 : Blo 401768 1150499 := bstep (se 1 (by rfl) ⟨862874, by rfl⟩ : syracuseStep 1150499 = 1725749) B1725749
theorem B3051107 : Blo 401768 3051107 := bstep (se 1 (by rfl) ⟨2288330, by rfl⟩ : syracuseStep 3051107 = 4576661) B4576661
theorem B2297443 : Blo 401768 2297443 := bstep (se 1 (by rfl) ⟨1723082, by rfl⟩ : syracuseStep 2297443 = 3446165) B3446165
theorem B1019537 : Blo 401768 1019537 := bstep (se 2 (by rfl) ⟨382326, by rfl⟩ : syracuseStep 1019537 = 764653) B764653
theorem B1019587 : Blo 401768 1019587 := bstep (se 1 (by rfl) ⟨764690, by rfl⟩ : syracuseStep 1019587 = 1529381) B1529381
theorem B1019729 : Blo 401768 1019729 := bstep (se 2 (by rfl) ⟨382398, by rfl⟩ : syracuseStep 1019729 = 764797) B764797
theorem B8851427 : Blo 401768 8851427 := bstep (se 1 (by rfl) ⟨6638570, by rfl⟩ : syracuseStep 8851427 = 13277141) B13277141
theorem B2297969 : Blo 401768 2297969 := bstep (se 2 (by rfl) ⟨861738, by rfl⟩ : syracuseStep 2297969 = 1723477) B1723477
theorem B2035853 : Blo 401768 2035853 := bstep (se 3 (by rfl) ⟨381722, by rfl⟩ : syracuseStep 2035853 = 763445) B763445
theorem B1380493 : Blo 401768 1380493 := bstep (se 3 (by rfl) ⟨258842, by rfl⟩ : syracuseStep 1380493 = 517685) B517685
theorem B11079821 : Blo 401768 11079821 := bstep (se 3 (by rfl) ⟨2077466, by rfl⟩ : syracuseStep 11079821 = 4154933) B4154933
theorem B7901381 : Blo 401768 7901381 := bstep (se 4 (by rfl) ⟨740754, by rfl⟩ : syracuseStep 7901381 = 1481509) B1481509
theorem B14913989 : Blo 401768 14913989 := bstep (se 4 (by rfl) ⟨1398186, by rfl⟩ : syracuseStep 14913989 = 2796373) B2796373
theorem B430643 : Blo 401768 430643 := bstep (se 1 (by rfl) ⟨322982, by rfl⟩ : syracuseStep 430643 = 645965) B645965
theorem B1249933 : Blo 401768 1249933 := bstep (se 3 (by rfl) ⟨234362, by rfl⟩ : syracuseStep 1249933 = 468725) B468725
theorem B1938161 : Blo 401768 1938161 := bstep (se 2 (by rfl) ⟨726810, by rfl⟩ : syracuseStep 1938161 = 1453621) B1453621
theorem B1151729 : Blo 401768 1151729 := bstep (se 2 (by rfl) ⟨431898, by rfl⟩ : syracuseStep 1151729 = 863797) B863797
theorem B1020721 : Blo 401768 1020721 := bstep (se 2 (by rfl) ⟨382770, by rfl⟩ : syracuseStep 1020721 = 765541) B765541
theorem B2921285 : Blo 401768 2921285 := bstep (se 4 (by rfl) ⟨273870, by rfl⟩ : syracuseStep 2921285 = 547741) B547741
theorem B1020995 : Blo 401768 1020995 := bstep (se 1 (by rfl) ⟨765746, by rfl⟩ : syracuseStep 1020995 = 1531493) B1531493
theorem B1315921 : Blo 401768 1315921 := bstep (se 2 (by rfl) ⟨493470, by rfl⟩ : syracuseStep 1315921 = 986941) B986941
theorem B1021187 : Blo 401768 1021187 := bstep (se 1 (by rfl) ⟨765890, by rfl⟩ : syracuseStep 1021187 = 1531781) B1531781
theorem B2463011 : Blo 401768 2463011 := bstep (se 1 (by rfl) ⟨1847258, by rfl⟩ : syracuseStep 2463011 = 3694517) B3694517
theorem B1086833 : Blo 401768 1086833 := bstep (se 2 (by rfl) ⟨407562, by rfl⟩ : syracuseStep 1086833 = 815125) B815125
theorem B2299427 : Blo 401768 2299427 := bstep (se 1 (by rfl) ⟨1724570, by rfl⟩ : syracuseStep 2299427 = 3449141) B3449141
theorem B2463281 : Blo 401768 2463281 := bstep (se 2 (by rfl) ⟨923730, by rfl⟩ : syracuseStep 2463281 = 1847461) B1847461
theorem B1939085 : Blo 401768 1939085 := bstep (se 3 (by rfl) ⟨363578, by rfl⟩ : syracuseStep 1939085 = 727157) B727157
theorem B431779 : Blo 401768 431779 := bstep (se 1 (by rfl) ⟨323834, by rfl⟩ : syracuseStep 431779 = 647669) B647669
theorem B1939277 : Blo 401768 1939277 := bstep (se 3 (by rfl) ⟨363614, by rfl⟩ : syracuseStep 1939277 = 727229) B727229
theorem B2758627 : Blo 401768 2758627 := bstep (se 1 (by rfl) ⟨2068970, by rfl⟩ : syracuseStep 2758627 = 4137941) B4137941
theorem B923665 : Blo 401768 923665 := bstep (se 2 (by rfl) ⟨346374, by rfl⟩ : syracuseStep 923665 = 692749) B692749
theorem B1153187 : Blo 401768 1153187 := bstep (se 1 (by rfl) ⟨864890, by rfl⟩ : syracuseStep 1153187 = 1729781) B1729781
theorem B1022129 : Blo 401768 1022129 := bstep (se 2 (by rfl) ⟨383298, by rfl⟩ : syracuseStep 1022129 = 766597) B766597
theorem B1022179 : Blo 401768 1022179 := bstep (se 1 (by rfl) ⟨766634, by rfl⟩ : syracuseStep 1022179 = 1533269) B1533269
theorem B1022321 : Blo 401768 1022321 := bstep (se 2 (by rfl) ⟨383370, by rfl⟩ : syracuseStep 1022321 = 766741) B766741
theorem B2595185 : Blo 401768 2595185 := bstep (se 2 (by rfl) ⟨973194, by rfl⟩ : syracuseStep 2595185 = 1946389) B1946389
theorem B858595 : Blo 401768 858595 := bstep (se 1 (by rfl) ⟨643946, by rfl⟩ : syracuseStep 858595 = 1287893) B1287893
theorem B432659 : Blo 401768 432659 := bstep (se 1 (by rfl) ⟨324494, by rfl⟩ : syracuseStep 432659 = 648989) B648989
theorem B1088045 : Blo 401768 1088045 := bstep (se 3 (by rfl) ⟨204008, by rfl⟩ : syracuseStep 1088045 = 408017) B408017
theorem B727633 : Blo 401768 727633 := bstep (se 2 (by rfl) ⟨272862, by rfl⟩ : syracuseStep 727633 = 545725) B545725
theorem B432787 : Blo 401768 432787 := bstep (se 1 (by rfl) ⟨324590, by rfl⟩ : syracuseStep 432787 = 649181) B649181
theorem B1153997 : Blo 401768 1153997 := bstep (se 3 (by rfl) ⟨216374, by rfl⟩ : syracuseStep 1153997 = 432749) B432749
theorem B2038769 : Blo 401768 2038769 := bstep (se 2 (by rfl) ⟨764538, by rfl⟩ : syracuseStep 2038769 = 1529077) B1529077
theorem B728131 : Blo 401768 728131 := bstep (se 1 (by rfl) ⟨546098, by rfl⟩ : syracuseStep 728131 = 1092197) B1092197
theorem B2530381 : Blo 401768 2530381 := bstep (se 3 (by rfl) ⟨474446, by rfl⟩ : syracuseStep 2530381 = 948893) B948893
theorem B1154189 : Blo 401768 1154189 := bstep (se 3 (by rfl) ⟨216410, by rfl⟩ : syracuseStep 1154189 = 432821) B432821
theorem B1023313 : Blo 401768 1023313 := bstep (se 2 (by rfl) ⟨383742, by rfl⟩ : syracuseStep 1023313 = 767485) B767485
theorem B2301317 : Blo 401768 2301317 := bstep (se 4 (by rfl) ⟨215748, by rfl⟩ : syracuseStep 2301317 = 431497) B431497
theorem B1383857 : Blo 401768 1383857 := bstep (se 2 (by rfl) ⟨518946, by rfl⟩ : syracuseStep 1383857 = 1037893) B1037893
theorem B1449571 : Blo 401768 1449571 := bstep (se 1 (by rfl) ⟨1087178, by rfl⟩ : syracuseStep 1449571 = 2174357) B2174357
theorem B1023587 : Blo 401768 1023587 := bstep (se 1 (by rfl) ⟨767690, by rfl⟩ : syracuseStep 1023587 = 1535381) B1535381
theorem B859825 : Blo 401768 859825 := bstep (se 2 (by rfl) ⟨322434, by rfl⟩ : syracuseStep 859825 = 644869) B644869
theorem B728771 : Blo 401768 728771 := bstep (se 1 (by rfl) ⟨546578, by rfl⟩ : syracuseStep 728771 = 1093157) B1093157
theorem B5119685 : Blo 401768 5119685 := bstep (se 4 (by rfl) ⟨479970, by rfl⟩ : syracuseStep 5119685 = 959941) B959941
theorem B1023779 : Blo 401768 1023779 := bstep (se 1 (by rfl) ⟨767834, by rfl⟩ : syracuseStep 1023779 = 1535669) B1535669
theorem B1155181 : Blo 401768 1155181 := bstep (se 3 (by rfl) ⟨216596, by rfl⟩ : syracuseStep 1155181 = 433193) B433193
theorem B2924657 : Blo 401768 2924657 := bstep (se 2 (by rfl) ⟨1096746, by rfl⟩ : syracuseStep 2924657 = 2193493) B2193493
theorem B729233 : Blo 401768 729233 := bstep (se 2 (by rfl) ⟨273462, by rfl⟩ : syracuseStep 729233 = 546925) B546925
theorem B2072753 : Blo 401768 2072753 := bstep (se 2 (by rfl) ⟨777282, by rfl⟩ : syracuseStep 2072753 = 1554565) B1554565
theorem B860483 : Blo 401768 860483 := bstep (se 1 (by rfl) ⟨645362, by rfl⟩ : syracuseStep 860483 = 1290725) B1290725
theorem B401779 : Blo 401768 401779 := bstep (se 1 (by rfl) ⟨301334, by rfl⟩ : syracuseStep 401779 = 602669) B602669
theorem B401795 : Blo 401768 401795 := bstep (se 1 (by rfl) ⟨301346, by rfl⟩ : syracuseStep 401795 = 602693) B602693
theorem B401811 : Blo 401768 401811 := bstep (se 1 (by rfl) ⟨301358, by rfl⟩ : syracuseStep 401811 = 602717) B602717
theorem B401827 : Blo 401768 401827 := bstep (se 1 (by rfl) ⟨301370, by rfl⟩ : syracuseStep 401827 = 602741) B602741
theorem B2040227 : Blo 401768 2040227 := bstep (se 1 (by rfl) ⟨1530170, by rfl⟩ : syracuseStep 2040227 = 3060341) B3060341
theorem B401843 : Blo 401768 401843 := bstep (se 1 (by rfl) ⟨301382, by rfl⟩ : syracuseStep 401843 = 602765) B602765
theorem B401859 : Blo 401768 401859 := bstep (se 1 (by rfl) ⟨301394, by rfl⟩ : syracuseStep 401859 = 602789) B602789
theorem B401875 : Blo 401768 401875 := bstep (se 1 (by rfl) ⟨301406, by rfl⟩ : syracuseStep 401875 = 602813) B602813
theorem B401891 : Blo 401768 401891 := bstep (se 1 (by rfl) ⟨301418, by rfl⟩ : syracuseStep 401891 = 602837) B602837
theorem B401907 : Blo 401768 401907 := bstep (se 1 (by rfl) ⟨301430, by rfl⟩ : syracuseStep 401907 = 602861) B602861
theorem B401923 : Blo 401768 401923 := bstep (se 1 (by rfl) ⟨301442, by rfl⟩ : syracuseStep 401923 = 602885) B602885
theorem B401939 : Blo 401768 401939 := bstep (se 1 (by rfl) ⟨301454, by rfl⟩ : syracuseStep 401939 = 602909) B602909
theorem B401955 : Blo 401768 401955 := bstep (se 1 (by rfl) ⟨301466, by rfl⟩ : syracuseStep 401955 = 602933) B602933
theorem B401971 : Blo 401768 401971 := bstep (se 1 (by rfl) ⟨301478, by rfl⟩ : syracuseStep 401971 = 602957) B602957
theorem B401987 : Blo 401768 401987 := bstep (se 1 (by rfl) ⟨301490, by rfl⟩ : syracuseStep 401987 = 602981) B602981
theorem B402003 : Blo 401768 402003 := bstep (se 1 (by rfl) ⟨301502, by rfl⟩ : syracuseStep 402003 = 603005) B603005
theorem B402019 : Blo 401768 402019 := bstep (se 1 (by rfl) ⟨301514, by rfl⟩ : syracuseStep 402019 = 603029) B603029
theorem B402035 : Blo 401768 402035 := bstep (se 1 (by rfl) ⟨301526, by rfl⟩ : syracuseStep 402035 = 603053) B603053
theorem B402051 : Blo 401768 402051 := bstep (se 1 (by rfl) ⟨301538, by rfl⟩ : syracuseStep 402051 = 603077) B603077
theorem B1548941 : Blo 401768 1548941 := bstep (se 3 (by rfl) ⟨290426, by rfl⟩ : syracuseStep 1548941 = 580853) B580853
theorem B402067 : Blo 401768 402067 := bstep (se 1 (by rfl) ⟨301550, by rfl⟩ : syracuseStep 402067 = 603101) B603101
theorem B402083 : Blo 401768 402083 := bstep (se 1 (by rfl) ⟨301562, by rfl⟩ : syracuseStep 402083 = 603125) B603125
theorem B402099 : Blo 401768 402099 := bstep (se 1 (by rfl) ⟨301574, by rfl⟩ : syracuseStep 402099 = 603149) B603149
theorem B402115 : Blo 401768 402115 := bstep (se 1 (by rfl) ⟨301586, by rfl⟩ : syracuseStep 402115 = 603173) B603173
theorem B1024721 : Blo 401768 1024721 := bstep (se 2 (by rfl) ⟨384270, by rfl⟩ : syracuseStep 1024721 = 768541) B768541
theorem B402131 : Blo 401768 402131 := bstep (se 1 (by rfl) ⟨301598, by rfl⟩ : syracuseStep 402131 = 603197) B603197
theorem B402147 : Blo 401768 402147 := bstep (se 1 (by rfl) ⟨301610, by rfl⟩ : syracuseStep 402147 = 603221) B603221
theorem B402163 : Blo 401768 402163 := bstep (se 1 (by rfl) ⟨301622, by rfl⟩ : syracuseStep 402163 = 603245) B603245
theorem B402179 : Blo 401768 402179 := bstep (se 1 (by rfl) ⟨301634, by rfl⟩ : syracuseStep 402179 = 603269) B603269
theorem B1024771 : Blo 401768 1024771 := bstep (se 1 (by rfl) ⟨768578, by rfl⟩ : syracuseStep 1024771 = 1537157) B1537157
theorem B402195 : Blo 401768 402195 := bstep (se 1 (by rfl) ⟨301646, by rfl⟩ : syracuseStep 402195 = 603293) B603293
theorem B402211 : Blo 401768 402211 := bstep (se 1 (by rfl) ⟨301658, by rfl⟩ : syracuseStep 402211 = 603317) B603317
theorem B402227 : Blo 401768 402227 := bstep (se 1 (by rfl) ⟨301670, by rfl⟩ : syracuseStep 402227 = 603341) B603341
theorem B402243 : Blo 401768 402243 := bstep (se 1 (by rfl) ⟨301682, by rfl⟩ : syracuseStep 402243 = 603365) B603365
theorem B3056453 : Blo 401768 3056453 := bstep (se 4 (by rfl) ⟨286542, by rfl⟩ : syracuseStep 3056453 = 573085) B573085
theorem B402259 : Blo 401768 402259 := bstep (se 1 (by rfl) ⟨301694, by rfl⟩ : syracuseStep 402259 = 603389) B603389
theorem B402275 : Blo 401768 402275 := bstep (se 1 (by rfl) ⟨301706, by rfl⟩ : syracuseStep 402275 = 603413) B603413
theorem B402291 : Blo 401768 402291 := bstep (se 1 (by rfl) ⟨301718, by rfl⟩ : syracuseStep 402291 = 603437) B603437
theorem B402307 : Blo 401768 402307 := bstep (se 1 (by rfl) ⟨301730, by rfl⟩ : syracuseStep 402307 = 603461) B603461
theorem B1024913 : Blo 401768 1024913 := bstep (se 2 (by rfl) ⟨384342, by rfl⟩ : syracuseStep 1024913 = 768685) B768685
theorem B402323 : Blo 401768 402323 := bstep (se 1 (by rfl) ⟨301742, by rfl⟩ : syracuseStep 402323 = 603485) B603485
theorem B402339 : Blo 401768 402339 := bstep (se 1 (by rfl) ⟨301754, by rfl⟩ : syracuseStep 402339 = 603509) B603509
theorem B402355 : Blo 401768 402355 := bstep (se 1 (by rfl) ⟨301766, by rfl⟩ : syracuseStep 402355 = 603533) B603533
theorem B402371 : Blo 401768 402371 := bstep (se 1 (by rfl) ⟨301778, by rfl⟩ : syracuseStep 402371 = 603557) B603557
theorem B402387 : Blo 401768 402387 := bstep (se 1 (by rfl) ⟨301790, by rfl⟩ : syracuseStep 402387 = 603581) B603581
theorem B402403 : Blo 401768 402403 := bstep (se 1 (by rfl) ⟨301802, by rfl⟩ : syracuseStep 402403 = 603605) B603605
theorem B402419 : Blo 401768 402419 := bstep (se 1 (by rfl) ⟨301814, by rfl⟩ : syracuseStep 402419 = 603629) B603629
theorem B402435 : Blo 401768 402435 := bstep (se 1 (by rfl) ⟨301826, by rfl⟩ : syracuseStep 402435 = 603653) B603653
theorem B402451 : Blo 401768 402451 := bstep (se 1 (by rfl) ⟨301838, by rfl⟩ : syracuseStep 402451 = 603677) B603677
theorem B402467 : Blo 401768 402467 := bstep (se 1 (by rfl) ⟨301850, by rfl⟩ : syracuseStep 402467 = 603701) B603701
theorem B762929 : Blo 401768 762929 := bstep (se 2 (by rfl) ⟨286098, by rfl⟩ : syracuseStep 762929 = 572197) B572197
theorem B402483 : Blo 401768 402483 := bstep (se 1 (by rfl) ⟨301862, by rfl⟩ : syracuseStep 402483 = 603725) B603725
theorem B402499 : Blo 401768 402499 := bstep (se 1 (by rfl) ⟨301874, by rfl⟩ : syracuseStep 402499 = 603749) B603749
theorem B402515 : Blo 401768 402515 := bstep (se 1 (by rfl) ⟨301886, by rfl⟩ : syracuseStep 402515 = 603773) B603773
theorem B402531 : Blo 401768 402531 := bstep (se 1 (by rfl) ⟨301898, by rfl⟩ : syracuseStep 402531 = 603797) B603797
theorem B402547 : Blo 401768 402547 := bstep (se 1 (by rfl) ⟨301910, by rfl⟩ : syracuseStep 402547 = 603821) B603821
theorem B402563 : Blo 401768 402563 := bstep (se 1 (by rfl) ⟨301922, by rfl⟩ : syracuseStep 402563 = 603845) B603845
theorem B861329 : Blo 401768 861329 := bstep (se 2 (by rfl) ⟨322998, by rfl⟩ : syracuseStep 861329 = 645997) B645997
theorem B402579 : Blo 401768 402579 := bstep (se 1 (by rfl) ⟨301934, by rfl⟩ : syracuseStep 402579 = 603869) B603869
theorem B402595 : Blo 401768 402595 := bstep (se 1 (by rfl) ⟨301946, by rfl⟩ : syracuseStep 402595 = 603893) B603893
theorem B402611 : Blo 401768 402611 := bstep (se 1 (by rfl) ⟨301958, by rfl⟩ : syracuseStep 402611 = 603917) B603917
theorem B402627 : Blo 401768 402627 := bstep (se 1 (by rfl) ⟨301970, by rfl⟩ : syracuseStep 402627 = 603941) B603941
theorem B2041037 : Blo 401768 2041037 := bstep (se 3 (by rfl) ⟨382694, by rfl⟩ : syracuseStep 2041037 = 765389) B765389
theorem B402643 : Blo 401768 402643 := bstep (se 1 (by rfl) ⟨301982, by rfl⟩ : syracuseStep 402643 = 603965) B603965
theorem B402659 : Blo 401768 402659 := bstep (se 1 (by rfl) ⟨301994, by rfl⟩ : syracuseStep 402659 = 603989) B603989
theorem B402675 : Blo 401768 402675 := bstep (se 1 (by rfl) ⟨302006, by rfl⟩ : syracuseStep 402675 = 604013) B604013
theorem B402691 : Blo 401768 402691 := bstep (se 1 (by rfl) ⟨302018, by rfl⟩ : syracuseStep 402691 = 604037) B604037
theorem B402707 : Blo 401768 402707 := bstep (se 1 (by rfl) ⟨302030, by rfl⟩ : syracuseStep 402707 = 604061) B604061
theorem B402723 : Blo 401768 402723 := bstep (se 1 (by rfl) ⟨302042, by rfl⟩ : syracuseStep 402723 = 604085) B604085
theorem B1090865 : Blo 401768 1090865 := bstep (se 2 (by rfl) ⟨409074, by rfl⟩ : syracuseStep 1090865 = 818149) B818149
theorem B402739 : Blo 401768 402739 := bstep (se 1 (by rfl) ⟨302054, by rfl⟩ : syracuseStep 402739 = 604109) B604109
theorem B402755 : Blo 401768 402755 := bstep (se 1 (by rfl) ⟨302066, by rfl⟩ : syracuseStep 402755 = 604133) B604133
theorem B402771 : Blo 401768 402771 := bstep (se 1 (by rfl) ⟨302078, by rfl⟩ : syracuseStep 402771 = 604157) B604157
theorem B402787 : Blo 401768 402787 := bstep (se 1 (by rfl) ⟨302090, by rfl⟩ : syracuseStep 402787 = 604181) B604181
theorem B402803 : Blo 401768 402803 := bstep (se 1 (by rfl) ⟨302102, by rfl⟩ : syracuseStep 402803 = 604205) B604205
theorem B402819 : Blo 401768 402819 := bstep (se 1 (by rfl) ⟨302114, by rfl⟩ : syracuseStep 402819 = 604229) B604229
theorem B402835 : Blo 401768 402835 := bstep (se 1 (by rfl) ⟨302126, by rfl⟩ : syracuseStep 402835 = 604253) B604253
theorem B402851 : Blo 401768 402851 := bstep (se 1 (by rfl) ⟨302138, by rfl⟩ : syracuseStep 402851 = 604277) B604277
theorem B402867 : Blo 401768 402867 := bstep (se 1 (by rfl) ⟨302150, by rfl⟩ : syracuseStep 402867 = 604301) B604301
theorem B402883 : Blo 401768 402883 := bstep (se 1 (by rfl) ⟨302162, by rfl⟩ : syracuseStep 402883 = 604325) B604325
theorem B402899 : Blo 401768 402899 := bstep (se 1 (by rfl) ⟨302174, by rfl⟩ : syracuseStep 402899 = 604349) B604349
theorem B402915 : Blo 401768 402915 := bstep (se 1 (by rfl) ⟨302186, by rfl⟩ : syracuseStep 402915 = 604373) B604373
theorem B402931 : Blo 401768 402931 := bstep (se 1 (by rfl) ⟨302198, by rfl⟩ : syracuseStep 402931 = 604397) B604397
theorem B402947 : Blo 401768 402947 := bstep (se 1 (by rfl) ⟨302210, by rfl⟩ : syracuseStep 402947 = 604421) B604421
theorem B2991629 : Blo 401768 2991629 := bstep (se 3 (by rfl) ⟨560930, by rfl⟩ : syracuseStep 2991629 = 1121861) B1121861
theorem B402963 : Blo 401768 402963 := bstep (se 1 (by rfl) ⟨302222, by rfl⟩ : syracuseStep 402963 = 604445) B604445
theorem B402979 : Blo 401768 402979 := bstep (se 1 (by rfl) ⟨302234, by rfl⟩ : syracuseStep 402979 = 604469) B604469
theorem B402995 : Blo 401768 402995 := bstep (se 1 (by rfl) ⟨302246, by rfl⟩ : syracuseStep 402995 = 604493) B604493
theorem B403011 : Blo 401768 403011 := bstep (se 1 (by rfl) ⟨302258, by rfl⟩ : syracuseStep 403011 = 604517) B604517
theorem B403027 : Blo 401768 403027 := bstep (se 1 (by rfl) ⟨302270, by rfl⟩ : syracuseStep 403027 = 604541) B604541
theorem B403043 : Blo 401768 403043 := bstep (se 1 (by rfl) ⟨302282, by rfl⟩ : syracuseStep 403043 = 604565) B604565
theorem B403059 : Blo 401768 403059 := bstep (se 1 (by rfl) ⟨302294, by rfl⟩ : syracuseStep 403059 = 604589) B604589
theorem B403075 : Blo 401768 403075 := bstep (se 1 (by rfl) ⟨302306, by rfl⟩ : syracuseStep 403075 = 604613) B604613
theorem B403091 : Blo 401768 403091 := bstep (se 1 (by rfl) ⟨302318, by rfl⟩ : syracuseStep 403091 = 604637) B604637
theorem B403107 : Blo 401768 403107 := bstep (se 1 (by rfl) ⟨302330, by rfl⟩ : syracuseStep 403107 = 604661) B604661
theorem B1091245 : Blo 401768 1091245 := bstep (se 3 (by rfl) ⟨204608, by rfl⟩ : syracuseStep 1091245 = 409217) B409217
theorem B403123 : Blo 401768 403123 := bstep (se 1 (by rfl) ⟨302342, by rfl⟩ : syracuseStep 403123 = 604685) B604685
theorem B403139 : Blo 401768 403139 := bstep (se 1 (by rfl) ⟨302354, by rfl⟩ : syracuseStep 403139 = 604709) B604709
theorem B730819 : Blo 401768 730819 := bstep (se 1 (by rfl) ⟨548114, by rfl⟩ : syracuseStep 730819 = 1096229) B1096229
theorem B403155 : Blo 401768 403155 := bstep (se 1 (by rfl) ⟨302366, by rfl⟩ : syracuseStep 403155 = 604733) B604733
theorem B403171 : Blo 401768 403171 := bstep (se 1 (by rfl) ⟨302378, by rfl⟩ : syracuseStep 403171 = 604757) B604757
theorem B403187 : Blo 401768 403187 := bstep (se 1 (by rfl) ⟨302390, by rfl⟩ : syracuseStep 403187 = 604781) B604781
theorem B403203 : Blo 401768 403203 := bstep (se 1 (by rfl) ⟨302402, by rfl⟩ : syracuseStep 403203 = 604805) B604805
theorem B403219 : Blo 401768 403219 := bstep (se 1 (by rfl) ⟨302414, by rfl⟩ : syracuseStep 403219 = 604829) B604829
theorem B403235 : Blo 401768 403235 := bstep (se 1 (by rfl) ⟨302426, by rfl⟩ : syracuseStep 403235 = 604853) B604853
theorem B403251 : Blo 401768 403251 := bstep (se 1 (by rfl) ⟨302438, by rfl⟩ : syracuseStep 403251 = 604877) B604877
theorem B403267 : Blo 401768 403267 := bstep (se 1 (by rfl) ⟨302450, by rfl⟩ : syracuseStep 403267 = 604901) B604901
theorem B403283 : Blo 401768 403283 := bstep (se 1 (by rfl) ⟨302462, by rfl⟩ : syracuseStep 403283 = 604925) B604925
theorem B403299 : Blo 401768 403299 := bstep (se 1 (by rfl) ⟨302474, by rfl⟩ : syracuseStep 403299 = 604949) B604949
theorem B1025905 : Blo 401768 1025905 := bstep (se 2 (by rfl) ⟨384714, by rfl⟩ : syracuseStep 1025905 = 769429) B769429
theorem B403315 : Blo 401768 403315 := bstep (se 1 (by rfl) ⟨302486, by rfl⟩ : syracuseStep 403315 = 604973) B604973
theorem B403331 : Blo 401768 403331 := bstep (se 1 (by rfl) ⟨302498, by rfl⟩ : syracuseStep 403331 = 604997) B604997
theorem B403347 : Blo 401768 403347 := bstep (se 1 (by rfl) ⟨302510, by rfl⟩ : syracuseStep 403347 = 605021) B605021
theorem B403363 : Blo 401768 403363 := bstep (se 1 (by rfl) ⟨302522, by rfl⟩ : syracuseStep 403363 = 605045) B605045
theorem B1288109 : Blo 401768 1288109 := bstep (se 3 (by rfl) ⟨241520, by rfl⟩ : syracuseStep 1288109 = 483041) B483041
theorem B763825 : Blo 401768 763825 := bstep (se 2 (by rfl) ⟨286434, by rfl⟩ : syracuseStep 763825 = 572869) B572869
theorem B403379 : Blo 401768 403379 := bstep (se 1 (by rfl) ⟨302534, by rfl⟩ : syracuseStep 403379 = 605069) B605069
theorem B403395 : Blo 401768 403395 := bstep (se 1 (by rfl) ⟨302546, by rfl⟩ : syracuseStep 403395 = 605093) B605093
theorem B11610053 : Blo 401768 11610053 := bstep (se 4 (by rfl) ⟨1088442, by rfl⟩ : syracuseStep 11610053 = 2176885) B2176885
theorem B403411 : Blo 401768 403411 := bstep (se 1 (by rfl) ⟨302558, by rfl⟩ : syracuseStep 403411 = 605117) B605117
theorem B403427 : Blo 401768 403427 := bstep (se 1 (by rfl) ⟨302570, by rfl⟩ : syracuseStep 403427 = 605141) B605141
theorem B403443 : Blo 401768 403443 := bstep (se 1 (by rfl) ⟨302582, by rfl⟩ : syracuseStep 403443 = 605165) B605165
theorem B403459 : Blo 401768 403459 := bstep (se 1 (by rfl) ⟨302594, by rfl⟩ : syracuseStep 403459 = 605189) B605189
theorem B403475 : Blo 401768 403475 := bstep (se 1 (by rfl) ⟨302606, by rfl⟩ : syracuseStep 403475 = 605213) B605213
theorem B403491 : Blo 401768 403491 := bstep (se 1 (by rfl) ⟨302618, by rfl⟩ : syracuseStep 403491 = 605237) B605237
theorem B403507 : Blo 401768 403507 := bstep (se 1 (by rfl) ⟨302630, by rfl⟩ : syracuseStep 403507 = 605261) B605261
theorem B403523 : Blo 401768 403523 := bstep (se 1 (by rfl) ⟨302642, by rfl⟩ : syracuseStep 403523 = 605285) B605285
theorem B763985 : Blo 401768 763985 := bstep (se 2 (by rfl) ⟨286494, by rfl⟩ : syracuseStep 763985 = 572989) B572989
theorem B403539 : Blo 401768 403539 := bstep (se 1 (by rfl) ⟨302654, by rfl⟩ : syracuseStep 403539 = 605309) B605309
theorem B403555 : Blo 401768 403555 := bstep (se 1 (by rfl) ⟨302666, by rfl⟩ : syracuseStep 403555 = 605333) B605333
theorem B403571 : Blo 401768 403571 := bstep (se 1 (by rfl) ⟨302678, by rfl⟩ : syracuseStep 403571 = 605357) B605357
theorem B403587 : Blo 401768 403587 := bstep (se 1 (by rfl) ⟨302690, by rfl⟩ : syracuseStep 403587 = 605381) B605381
theorem B1026179 : Blo 401768 1026179 := bstep (se 1 (by rfl) ⟨769634, by rfl⟩ : syracuseStep 1026179 = 1539269) B1539269
theorem B403603 : Blo 401768 403603 := bstep (se 1 (by rfl) ⟨302702, by rfl⟩ : syracuseStep 403603 = 605405) B605405
theorem B403619 : Blo 401768 403619 := bstep (se 1 (by rfl) ⟨302714, by rfl⟩ : syracuseStep 403619 = 605429) B605429
theorem B403635 : Blo 401768 403635 := bstep (se 1 (by rfl) ⟨302726, by rfl⟩ : syracuseStep 403635 = 605453) B605453
theorem B403651 : Blo 401768 403651 := bstep (se 1 (by rfl) ⟨302738, by rfl⟩ : syracuseStep 403651 = 605477) B605477
theorem B403667 : Blo 401768 403667 := bstep (se 1 (by rfl) ⟨302750, by rfl⟩ : syracuseStep 403667 = 605501) B605501
theorem B403683 : Blo 401768 403683 := bstep (se 1 (by rfl) ⟨302762, by rfl⟩ : syracuseStep 403683 = 605525) B605525
theorem B403699 : Blo 401768 403699 := bstep (se 1 (by rfl) ⟨302774, by rfl⟩ : syracuseStep 403699 = 605549) B605549
theorem B403715 : Blo 401768 403715 := bstep (se 1 (by rfl) ⟨302786, by rfl⟩ : syracuseStep 403715 = 605573) B605573
theorem B403731 : Blo 401768 403731 := bstep (se 1 (by rfl) ⟨302798, by rfl⟩ : syracuseStep 403731 = 605597) B605597
theorem B403747 : Blo 401768 403747 := bstep (se 1 (by rfl) ⟨302810, by rfl⟩ : syracuseStep 403747 = 605621) B605621
theorem B403763 : Blo 401768 403763 := bstep (se 1 (by rfl) ⟨302822, by rfl⟩ : syracuseStep 403763 = 605645) B605645
theorem B403779 : Blo 401768 403779 := bstep (se 1 (by rfl) ⟨302834, by rfl⟩ : syracuseStep 403779 = 605669) B605669
theorem B1026371 : Blo 401768 1026371 := bstep (se 1 (by rfl) ⟨769778, by rfl⟩ : syracuseStep 1026371 = 1539557) B1539557
theorem B403795 : Blo 401768 403795 := bstep (se 1 (by rfl) ⟨302846, by rfl⟩ : syracuseStep 403795 = 605693) B605693
theorem B403811 : Blo 401768 403811 := bstep (se 1 (by rfl) ⟨302858, by rfl⟩ : syracuseStep 403811 = 605717) B605717
theorem B403827 : Blo 401768 403827 := bstep (se 1 (by rfl) ⟨302870, by rfl⟩ : syracuseStep 403827 = 605741) B605741
theorem B403843 : Blo 401768 403843 := bstep (se 1 (by rfl) ⟨302882, by rfl⟩ : syracuseStep 403843 = 605765) B605765
theorem B403859 : Blo 401768 403859 := bstep (se 1 (by rfl) ⟨302894, by rfl⟩ : syracuseStep 403859 = 605789) B605789
theorem B403875 : Blo 401768 403875 := bstep (se 1 (by rfl) ⟨302906, by rfl⟩ : syracuseStep 403875 = 605813) B605813
theorem B403891 : Blo 401768 403891 := bstep (se 1 (by rfl) ⟨302918, by rfl⟩ : syracuseStep 403891 = 605837) B605837
theorem B403907 : Blo 401768 403907 := bstep (se 1 (by rfl) ⟨302930, by rfl⟩ : syracuseStep 403907 = 605861) B605861
theorem B403923 : Blo 401768 403923 := bstep (se 1 (by rfl) ⟨302942, by rfl⟩ : syracuseStep 403923 = 605885) B605885
theorem B764387 : Blo 401768 764387 := bstep (se 1 (by rfl) ⟨573290, by rfl⟩ : syracuseStep 764387 = 1146581) B1146581
theorem B403939 : Blo 401768 403939 := bstep (se 1 (by rfl) ⟨302954, by rfl⟩ : syracuseStep 403939 = 605909) B605909
theorem B403955 : Blo 401768 403955 := bstep (se 1 (by rfl) ⟨302966, by rfl⟩ : syracuseStep 403955 = 605933) B605933
theorem B403971 : Blo 401768 403971 := bstep (se 1 (by rfl) ⟨302978, by rfl⟩ : syracuseStep 403971 = 605957) B605957
theorem B403987 : Blo 401768 403987 := bstep (se 1 (by rfl) ⟨302990, by rfl⟩ : syracuseStep 403987 = 605981) B605981
theorem B404003 : Blo 401768 404003 := bstep (se 1 (by rfl) ⟨303002, by rfl⟩ : syracuseStep 404003 = 606005) B606005
theorem B404019 : Blo 401768 404019 := bstep (se 1 (by rfl) ⟨303014, by rfl⟩ : syracuseStep 404019 = 606029) B606029
theorem B404035 : Blo 401768 404035 := bstep (se 1 (by rfl) ⟨303026, by rfl⟩ : syracuseStep 404035 = 606053) B606053
theorem B404051 : Blo 401768 404051 := bstep (se 1 (by rfl) ⟨303038, by rfl⟩ : syracuseStep 404051 = 606077) B606077
theorem B404067 : Blo 401768 404067 := bstep (se 1 (by rfl) ⟨303050, by rfl⟩ : syracuseStep 404067 = 606101) B606101
theorem B404083 : Blo 401768 404083 := bstep (se 1 (by rfl) ⟨303062, by rfl⟩ : syracuseStep 404083 = 606125) B606125
theorem B404099 : Blo 401768 404099 := bstep (se 1 (by rfl) ⟨303074, by rfl⟩ : syracuseStep 404099 = 606149) B606149
theorem B404115 : Blo 401768 404115 := bstep (se 1 (by rfl) ⟨303086, by rfl⟩ : syracuseStep 404115 = 606173) B606173
theorem B404131 : Blo 401768 404131 := bstep (se 1 (by rfl) ⟨303098, by rfl⟩ : syracuseStep 404131 = 606197) B606197
theorem B404147 : Blo 401768 404147 := bstep (se 1 (by rfl) ⟨303110, by rfl⟩ : syracuseStep 404147 = 606221) B606221
theorem B404163 : Blo 401768 404163 := bstep (se 1 (by rfl) ⟨303122, by rfl⟩ : syracuseStep 404163 = 606245) B606245
theorem B404179 : Blo 401768 404179 := bstep (se 1 (by rfl) ⟨303134, by rfl⟩ : syracuseStep 404179 = 606269) B606269
theorem B404195 : Blo 401768 404195 := bstep (se 1 (by rfl) ⟨303146, by rfl⟩ : syracuseStep 404195 = 606293) B606293
theorem B404211 : Blo 401768 404211 := bstep (se 1 (by rfl) ⟨303158, by rfl⟩ : syracuseStep 404211 = 606317) B606317
theorem B404227 : Blo 401768 404227 := bstep (se 1 (by rfl) ⟨303170, by rfl⟩ : syracuseStep 404227 = 606341) B606341
theorem B404243 : Blo 401768 404243 := bstep (se 1 (by rfl) ⟨303182, by rfl⟩ : syracuseStep 404243 = 606365) B606365
theorem B863011 : Blo 401768 863011 := bstep (se 1 (by rfl) ⟨647258, by rfl⟩ : syracuseStep 863011 = 1294517) B1294517
theorem B404259 : Blo 401768 404259 := bstep (se 1 (by rfl) ⟨303194, by rfl⟩ : syracuseStep 404259 = 606389) B606389
theorem B404275 : Blo 401768 404275 := bstep (se 1 (by rfl) ⟨303206, by rfl⟩ : syracuseStep 404275 = 606413) B606413
theorem B404291 : Blo 401768 404291 := bstep (se 1 (by rfl) ⟨303218, by rfl⟩ : syracuseStep 404291 = 606437) B606437
theorem B404307 : Blo 401768 404307 := bstep (se 1 (by rfl) ⟨303230, by rfl⟩ : syracuseStep 404307 = 606461) B606461
theorem B404323 : Blo 401768 404323 := bstep (se 1 (by rfl) ⟨303242, by rfl⟩ : syracuseStep 404323 = 606485) B606485
theorem B404339 : Blo 401768 404339 := bstep (se 1 (by rfl) ⟨303254, by rfl⟩ : syracuseStep 404339 = 606509) B606509
theorem B404355 : Blo 401768 404355 := bstep (se 1 (by rfl) ⟨303266, by rfl⟩ : syracuseStep 404355 = 606533) B606533
theorem B404371 : Blo 401768 404371 := bstep (se 1 (by rfl) ⟨303278, by rfl⟩ : syracuseStep 404371 = 606557) B606557
theorem B404387 : Blo 401768 404387 := bstep (se 1 (by rfl) ⟨303290, by rfl⟩ : syracuseStep 404387 = 606581) B606581
theorem B404403 : Blo 401768 404403 := bstep (se 1 (by rfl) ⟨303302, by rfl⟩ : syracuseStep 404403 = 606605) B606605
theorem B404419 : Blo 401768 404419 := bstep (se 1 (by rfl) ⟨303314, by rfl⟩ : syracuseStep 404419 = 606629) B606629
theorem B404435 : Blo 401768 404435 := bstep (se 1 (by rfl) ⟨303326, by rfl⟩ : syracuseStep 404435 = 606653) B606653
theorem B404451 : Blo 401768 404451 := bstep (se 1 (by rfl) ⟨303338, by rfl⟩ : syracuseStep 404451 = 606677) B606677
theorem B404467 : Blo 401768 404467 := bstep (se 1 (by rfl) ⟨303350, by rfl⟩ : syracuseStep 404467 = 606701) B606701
theorem B404483 : Blo 401768 404483 := bstep (se 1 (by rfl) ⟨303362, by rfl⟩ : syracuseStep 404483 = 606725) B606725
theorem B404499 : Blo 401768 404499 := bstep (se 1 (by rfl) ⟨303374, by rfl⟩ : syracuseStep 404499 = 606749) B606749
theorem B404515 : Blo 401768 404515 := bstep (se 1 (by rfl) ⟨303386, by rfl⟩ : syracuseStep 404515 = 606773) B606773
theorem B404531 : Blo 401768 404531 := bstep (se 1 (by rfl) ⟨303398, by rfl⟩ : syracuseStep 404531 = 606797) B606797
theorem B404547 : Blo 401768 404547 := bstep (se 1 (by rfl) ⟨303410, by rfl⟩ : syracuseStep 404547 = 606821) B606821
theorem B404563 : Blo 401768 404563 := bstep (se 1 (by rfl) ⟨303422, by rfl⟩ : syracuseStep 404563 = 606845) B606845
theorem B404579 : Blo 401768 404579 := bstep (se 1 (by rfl) ⟨303434, by rfl⟩ : syracuseStep 404579 = 606869) B606869
theorem B1387633 : Blo 401768 1387633 := bstep (se 2 (by rfl) ⟨520362, by rfl⟩ : syracuseStep 1387633 = 1040725) B1040725
theorem B404595 : Blo 401768 404595 := bstep (se 1 (by rfl) ⟨303446, by rfl⟩ : syracuseStep 404595 = 606893) B606893
theorem B404611 : Blo 401768 404611 := bstep (se 1 (by rfl) ⟨303458, by rfl⟩ : syracuseStep 404611 = 606917) B606917
theorem B404627 : Blo 401768 404627 := bstep (se 1 (by rfl) ⟨303470, by rfl⟩ : syracuseStep 404627 = 606941) B606941
theorem B404643 : Blo 401768 404643 := bstep (se 1 (by rfl) ⟨303482, by rfl⟩ : syracuseStep 404643 = 606965) B606965
theorem B404659 : Blo 401768 404659 := bstep (se 1 (by rfl) ⟨303494, by rfl⟩ : syracuseStep 404659 = 606989) B606989
theorem B404675 : Blo 401768 404675 := bstep (se 1 (by rfl) ⟨303506, by rfl⟩ : syracuseStep 404675 = 607013) B607013
theorem B404691 : Blo 401768 404691 := bstep (se 1 (by rfl) ⟨303518, by rfl⟩ : syracuseStep 404691 = 607037) B607037
theorem B404707 : Blo 401768 404707 := bstep (se 1 (by rfl) ⟨303530, by rfl⟩ : syracuseStep 404707 = 607061) B607061
theorem B863473 : Blo 401768 863473 := bstep (se 2 (by rfl) ⟨323802, by rfl⟩ : syracuseStep 863473 = 647605) B647605
theorem B404723 : Blo 401768 404723 := bstep (se 1 (by rfl) ⟨303542, by rfl⟩ : syracuseStep 404723 = 607085) B607085
theorem B404739 : Blo 401768 404739 := bstep (se 1 (by rfl) ⟨303554, by rfl⟩ : syracuseStep 404739 = 607109) B607109
theorem B404755 : Blo 401768 404755 := bstep (se 1 (by rfl) ⟨303566, by rfl⟩ : syracuseStep 404755 = 607133) B607133
theorem B404771 : Blo 401768 404771 := bstep (se 1 (by rfl) ⟨303578, by rfl⟩ : syracuseStep 404771 = 607157) B607157
theorem B404787 : Blo 401768 404787 := bstep (se 1 (by rfl) ⟨303590, by rfl⟩ : syracuseStep 404787 = 607181) B607181
theorem B404803 : Blo 401768 404803 := bstep (se 1 (by rfl) ⟨303602, by rfl⟩ : syracuseStep 404803 = 607205) B607205
theorem B404819 : Blo 401768 404819 := bstep (se 1 (by rfl) ⟨303614, by rfl⟩ : syracuseStep 404819 = 607229) B607229
theorem B765283 : Blo 401768 765283 := bstep (se 1 (by rfl) ⟨573962, by rfl⟩ : syracuseStep 765283 = 1147925) B1147925
theorem B404835 : Blo 401768 404835 := bstep (se 1 (by rfl) ⟨303626, by rfl⟩ : syracuseStep 404835 = 607253) B607253
theorem B404851 : Blo 401768 404851 := bstep (se 1 (by rfl) ⟨303638, by rfl⟩ : syracuseStep 404851 = 607277) B607277
theorem B404867 : Blo 401768 404867 := bstep (se 1 (by rfl) ⟨303650, by rfl⟩ : syracuseStep 404867 = 607301) B607301
theorem B404883 : Blo 401768 404883 := bstep (se 1 (by rfl) ⟨303662, by rfl⟩ : syracuseStep 404883 = 607325) B607325
theorem B404899 : Blo 401768 404899 := bstep (se 1 (by rfl) ⟨303674, by rfl⟩ : syracuseStep 404899 = 607349) B607349
theorem B404915 : Blo 401768 404915 := bstep (se 1 (by rfl) ⟨303686, by rfl⟩ : syracuseStep 404915 = 607373) B607373
theorem B404931 : Blo 401768 404931 := bstep (se 1 (by rfl) ⟨303698, by rfl⟩ : syracuseStep 404931 = 607397) B607397
theorem B404947 : Blo 401768 404947 := bstep (se 1 (by rfl) ⟨303710, by rfl⟩ : syracuseStep 404947 = 607421) B607421
theorem B404963 : Blo 401768 404963 := bstep (se 1 (by rfl) ⟨303722, by rfl⟩ : syracuseStep 404963 = 607445) B607445
theorem B404979 : Blo 401768 404979 := bstep (se 1 (by rfl) ⟨303734, by rfl⟩ : syracuseStep 404979 = 607469) B607469
theorem B765443 : Blo 401768 765443 := bstep (se 1 (by rfl) ⟨574082, by rfl⟩ : syracuseStep 765443 = 1148165) B1148165
theorem B404995 : Blo 401768 404995 := bstep (se 1 (by rfl) ⟨303746, by rfl⟩ : syracuseStep 404995 = 607493) B607493
theorem B405011 : Blo 401768 405011 := bstep (se 1 (by rfl) ⟨303758, by rfl⟩ : syracuseStep 405011 = 607517) B607517
theorem B405027 : Blo 401768 405027 := bstep (se 1 (by rfl) ⟨303770, by rfl⟩ : syracuseStep 405027 = 607541) B607541
theorem B405043 : Blo 401768 405043 := bstep (se 1 (by rfl) ⟨303782, by rfl⟩ : syracuseStep 405043 = 607565) B607565
theorem B405059 : Blo 401768 405059 := bstep (se 1 (by rfl) ⟨303794, by rfl⟩ : syracuseStep 405059 = 607589) B607589
theorem B405075 : Blo 401768 405075 := bstep (se 1 (by rfl) ⟨303806, by rfl⟩ : syracuseStep 405075 = 607613) B607613
theorem B405091 : Blo 401768 405091 := bstep (se 1 (by rfl) ⟨303818, by rfl⟩ : syracuseStep 405091 = 607637) B607637
theorem B405107 : Blo 401768 405107 := bstep (se 1 (by rfl) ⟨303830, by rfl⟩ : syracuseStep 405107 = 607661) B607661
theorem B405123 : Blo 401768 405123 := bstep (se 1 (by rfl) ⟨303842, by rfl⟩ : syracuseStep 405123 = 607685) B607685
theorem B2174597 : Blo 401768 2174597 := bstep (se 4 (by rfl) ⟨203868, by rfl⟩ : syracuseStep 2174597 = 407737) B407737
theorem B405139 : Blo 401768 405139 := bstep (se 1 (by rfl) ⟨303854, by rfl⟩ : syracuseStep 405139 = 607709) B607709
theorem B405155 : Blo 401768 405155 := bstep (se 1 (by rfl) ⟨303866, by rfl⟩ : syracuseStep 405155 = 607733) B607733
theorem B405171 : Blo 401768 405171 := bstep (se 1 (by rfl) ⟨303878, by rfl⟩ : syracuseStep 405171 = 607757) B607757
theorem B405187 : Blo 401768 405187 := bstep (se 1 (by rfl) ⟨303890, by rfl⟩ : syracuseStep 405187 = 607781) B607781
theorem B405203 : Blo 401768 405203 := bstep (se 1 (by rfl) ⟨303902, by rfl⟩ : syracuseStep 405203 = 607805) B607805
theorem B405219 : Blo 401768 405219 := bstep (se 1 (by rfl) ⟨303914, by rfl⟩ : syracuseStep 405219 = 607829) B607829
theorem B405235 : Blo 401768 405235 := bstep (se 1 (by rfl) ⟨303926, by rfl⟩ : syracuseStep 405235 = 607853) B607853
theorem B405251 : Blo 401768 405251 := bstep (se 1 (by rfl) ⟨303938, by rfl⟩ : syracuseStep 405251 = 607877) B607877
theorem B405267 : Blo 401768 405267 := bstep (se 1 (by rfl) ⟨303950, by rfl⟩ : syracuseStep 405267 = 607901) B607901
theorem B405283 : Blo 401768 405283 := bstep (se 1 (by rfl) ⟨303962, by rfl⟩ : syracuseStep 405283 = 607925) B607925
theorem B405299 : Blo 401768 405299 := bstep (se 1 (by rfl) ⟨303974, by rfl⟩ : syracuseStep 405299 = 607949) B607949
theorem B405315 : Blo 401768 405315 := bstep (se 1 (by rfl) ⟨303986, by rfl⟩ : syracuseStep 405315 = 607973) B607973
theorem B405331 : Blo 401768 405331 := bstep (se 1 (by rfl) ⟨303998, by rfl⟩ : syracuseStep 405331 = 607997) B607997
theorem B405347 : Blo 401768 405347 := bstep (se 1 (by rfl) ⟨304010, by rfl⟩ : syracuseStep 405347 = 608021) B608021
theorem B405363 : Blo 401768 405363 := bstep (se 1 (by rfl) ⟨304022, by rfl⟩ : syracuseStep 405363 = 608045) B608045
theorem B405379 : Blo 401768 405379 := bstep (se 1 (by rfl) ⟨304034, by rfl⟩ : syracuseStep 405379 = 608069) B608069
theorem B405395 : Blo 401768 405395 := bstep (se 1 (by rfl) ⟨304046, by rfl⟩ : syracuseStep 405395 = 608093) B608093
theorem B405411 : Blo 401768 405411 := bstep (se 1 (by rfl) ⟨304058, by rfl⟩ : syracuseStep 405411 = 608117) B608117
theorem B405427 : Blo 401768 405427 := bstep (se 1 (by rfl) ⟨304070, by rfl⟩ : syracuseStep 405427 = 608141) B608141
theorem B405443 : Blo 401768 405443 := bstep (se 1 (by rfl) ⟨304082, by rfl⟩ : syracuseStep 405443 = 608165) B608165
theorem B405459 : Blo 401768 405459 := bstep (se 1 (by rfl) ⟨304094, by rfl⟩ : syracuseStep 405459 = 608189) B608189
theorem B405475 : Blo 401768 405475 := bstep (se 1 (by rfl) ⟨304106, by rfl⟩ : syracuseStep 405475 = 608213) B608213
theorem B405491 : Blo 401768 405491 := bstep (se 1 (by rfl) ⟨304118, by rfl⟩ : syracuseStep 405491 = 608237) B608237
theorem B405507 : Blo 401768 405507 := bstep (se 1 (by rfl) ⟨304130, by rfl⟩ : syracuseStep 405507 = 608261) B608261
theorem B405523 : Blo 401768 405523 := bstep (se 1 (by rfl) ⟨304142, by rfl⟩ : syracuseStep 405523 = 608285) B608285
theorem B405539 : Blo 401768 405539 := bstep (se 1 (by rfl) ⟨304154, by rfl⟩ : syracuseStep 405539 = 608309) B608309
theorem B1290289 : Blo 401768 1290289 := bstep (se 2 (by rfl) ⟨483858, by rfl⟩ : syracuseStep 1290289 = 967717) B967717
theorem B2043953 : Blo 401768 2043953 := bstep (se 2 (by rfl) ⟨766482, by rfl⟩ : syracuseStep 2043953 = 1532965) B1532965
theorem B405555 : Blo 401768 405555 := bstep (se 1 (by rfl) ⟨304166, by rfl⟩ : syracuseStep 405555 = 608333) B608333
theorem B405571 : Blo 401768 405571 := bstep (se 1 (by rfl) ⟨304178, by rfl⟩ : syracuseStep 405571 = 608357) B608357
theorem B405587 : Blo 401768 405587 := bstep (se 1 (by rfl) ⟨304190, by rfl⟩ : syracuseStep 405587 = 608381) B608381
theorem B405603 : Blo 401768 405603 := bstep (se 1 (by rfl) ⟨304202, by rfl⟩ : syracuseStep 405603 = 608405) B608405
theorem B405619 : Blo 401768 405619 := bstep (se 1 (by rfl) ⟨304214, by rfl⟩ : syracuseStep 405619 = 608429) B608429
theorem B405635 : Blo 401768 405635 := bstep (se 1 (by rfl) ⟨304226, by rfl⟩ : syracuseStep 405635 = 608453) B608453
theorem B405651 : Blo 401768 405651 := bstep (se 1 (by rfl) ⟨304238, by rfl⟩ : syracuseStep 405651 = 608477) B608477
theorem B405667 : Blo 401768 405667 := bstep (se 1 (by rfl) ⟨304250, by rfl⟩ : syracuseStep 405667 = 608501) B608501
theorem B405683 : Blo 401768 405683 := bstep (se 1 (by rfl) ⟨304262, by rfl⟩ : syracuseStep 405683 = 608525) B608525
theorem B4599989 : Blo 401768 4599989 := bstep (se 5 (by rfl) ⟨215624, by rfl⟩ : syracuseStep 4599989 = 431249) B431249
theorem B405699 : Blo 401768 405699 := bstep (se 1 (by rfl) ⟨304274, by rfl⟩ : syracuseStep 405699 = 608549) B608549
theorem B405715 : Blo 401768 405715 := bstep (se 1 (by rfl) ⟨304286, by rfl⟩ : syracuseStep 405715 = 608573) B608573
theorem B1290467 : Blo 401768 1290467 := bstep (se 1 (by rfl) ⟨967850, by rfl⟩ : syracuseStep 1290467 = 1935701) B1935701
theorem B405731 : Blo 401768 405731 := bstep (se 1 (by rfl) ⟨304298, by rfl⟩ : syracuseStep 405731 = 608597) B608597
theorem B405747 : Blo 401768 405747 := bstep (se 1 (by rfl) ⟨304310, by rfl⟩ : syracuseStep 405747 = 608621) B608621
theorem B864515 : Blo 401768 864515 := bstep (se 1 (by rfl) ⟨648386, by rfl⟩ : syracuseStep 864515 = 1296773) B1296773
theorem B405763 : Blo 401768 405763 := bstep (se 1 (by rfl) ⟨304322, by rfl⟩ : syracuseStep 405763 = 608645) B608645
theorem B1356209 : Blo 401768 1356209 := bstep (se 2 (by rfl) ⟨508578, by rfl⟩ : syracuseStep 1356209 = 1017157) B1017157
theorem B2241037 : Blo 401768 2241037 := bstep (se 3 (by rfl) ⟨420194, by rfl⟩ : syracuseStep 2241037 = 840389) B840389
theorem B9777685 : Blo 401768 9777685 := bstep (se 6 (by rfl) ⟨229164, by rfl⟩ : syracuseStep 9777685 = 458329) B458329
theorem B602657 : Blo 401768 602657 := bstep (se 2 (by rfl) ⟨225996, by rfl⟩ : syracuseStep 602657 = 451993) B451993
theorem B766513 : Blo 401768 766513 := bstep (se 2 (by rfl) ⟨287442, by rfl⟩ : syracuseStep 766513 = 574885) B574885
theorem B602675 : Blo 401768 602675 := bstep (se 1 (by rfl) ⟨452006, by rfl⟩ : syracuseStep 602675 = 904013) B904013
theorem B602705 : Blo 401768 602705 := bstep (se 2 (by rfl) ⟨226014, by rfl⟩ : syracuseStep 602705 = 452029) B452029
theorem B602723 : Blo 401768 602723 := bstep (se 1 (by rfl) ⟨452042, by rfl⟩ : syracuseStep 602723 = 904085) B904085
theorem B2175587 : Blo 401768 2175587 := bstep (se 1 (by rfl) ⟨1631690, by rfl⟩ : syracuseStep 2175587 = 3263381) B3263381
theorem B1225325 : Blo 401768 1225325 := bstep (se 3 (by rfl) ⟨229748, by rfl⟩ : syracuseStep 1225325 = 459497) B459497
theorem B602753 : Blo 401768 602753 := bstep (se 2 (by rfl) ⟨226032, by rfl⟩ : syracuseStep 602753 = 452065) B452065
theorem B602771 : Blo 401768 602771 := bstep (se 1 (by rfl) ⟨452078, by rfl⟩ : syracuseStep 602771 = 904157) B904157
theorem B602801 : Blo 401768 602801 := bstep (se 2 (by rfl) ⟨226050, by rfl⟩ : syracuseStep 602801 = 452101) B452101
theorem B602819 : Blo 401768 602819 := bstep (se 1 (by rfl) ⟨452114, by rfl⟩ : syracuseStep 602819 = 904229) B904229
theorem B602849 : Blo 401768 602849 := bstep (se 2 (by rfl) ⟨226068, by rfl⟩ : syracuseStep 602849 = 452137) B452137
theorem B602867 : Blo 401768 602867 := bstep (se 1 (by rfl) ⟨452150, by rfl⟩ : syracuseStep 602867 = 904301) B904301
theorem B865027 : Blo 401768 865027 := bstep (se 1 (by rfl) ⟨648770, by rfl⟩ : syracuseStep 865027 = 1297541) B1297541
theorem B602897 : Blo 401768 602897 := bstep (se 2 (by rfl) ⟨226086, by rfl⟩ : syracuseStep 602897 = 452173) B452173
theorem B602915 : Blo 401768 602915 := bstep (se 1 (by rfl) ⟨452186, by rfl⟩ : syracuseStep 602915 = 904373) B904373
theorem B602945 : Blo 401768 602945 := bstep (se 2 (by rfl) ⟨226104, by rfl⟩ : syracuseStep 602945 = 452209) B452209
theorem B1192781 : Blo 401768 1192781 := bstep (se 3 (by rfl) ⟨223646, by rfl⟩ : syracuseStep 1192781 = 447293) B447293
theorem B602963 : Blo 401768 602963 := bstep (se 1 (by rfl) ⟨452222, by rfl⟩ : syracuseStep 602963 = 904445) B904445
theorem B602993 : Blo 401768 602993 := bstep (se 2 (by rfl) ⟨226122, by rfl⟩ : syracuseStep 602993 = 452245) B452245
theorem B603011 : Blo 401768 603011 := bstep (se 1 (by rfl) ⟨452258, by rfl⟩ : syracuseStep 603011 = 904517) B904517
theorem B603041 : Blo 401768 603041 := bstep (se 2 (by rfl) ⟨226140, by rfl⟩ : syracuseStep 603041 = 452281) B452281
theorem B603059 : Blo 401768 603059 := bstep (se 1 (by rfl) ⟨452294, by rfl⟩ : syracuseStep 603059 = 904589) B904589
theorem B1356749 : Blo 401768 1356749 := bstep (se 3 (by rfl) ⟨254390, by rfl⟩ : syracuseStep 1356749 = 508781) B508781
theorem B603089 : Blo 401768 603089 := bstep (se 2 (by rfl) ⟨226158, by rfl⟩ : syracuseStep 603089 = 452317) B452317
theorem B603107 : Blo 401768 603107 := bstep (se 1 (by rfl) ⟨452330, by rfl⟩ : syracuseStep 603107 = 904661) B904661
theorem B603137 : Blo 401768 603137 := bstep (se 2 (by rfl) ⟨226176, by rfl⟩ : syracuseStep 603137 = 452353) B452353
theorem B1356803 : Blo 401768 1356803 := bstep (se 1 (by rfl) ⟨1017602, by rfl⟩ : syracuseStep 1356803 = 2035205) B2035205
theorem B603155 : Blo 401768 603155 := bstep (se 1 (by rfl) ⟨452366, by rfl⟩ : syracuseStep 603155 = 904733) B904733
theorem B603185 : Blo 401768 603185 := bstep (se 2 (by rfl) ⟨226194, by rfl⟩ : syracuseStep 603185 = 452389) B452389
theorem B7025717 : Blo 401768 7025717 := bstep (se 5 (by rfl) ⟨329330, by rfl⟩ : syracuseStep 7025717 = 658661) B658661
theorem B603203 : Blo 401768 603203 := bstep (se 1 (by rfl) ⟨452402, by rfl⟩ : syracuseStep 603203 = 904805) B904805
theorem B2307149 : Blo 401768 2307149 := bstep (se 3 (by rfl) ⟨432590, by rfl⟩ : syracuseStep 2307149 = 865181) B865181
theorem B603233 : Blo 401768 603233 := bstep (se 2 (by rfl) ⟨226212, by rfl⟩ : syracuseStep 603233 = 452425) B452425
theorem B603251 : Blo 401768 603251 := bstep (se 1 (by rfl) ⟨452438, by rfl⟩ : syracuseStep 603251 = 904877) B904877
theorem B603281 : Blo 401768 603281 := bstep (se 2 (by rfl) ⟨226230, by rfl⟩ : syracuseStep 603281 = 452461) B452461
theorem B603299 : Blo 401768 603299 := bstep (se 1 (by rfl) ⟨452474, by rfl⟩ : syracuseStep 603299 = 904949) B904949
theorem B603329 : Blo 401768 603329 := bstep (se 2 (by rfl) ⟨226248, by rfl⟩ : syracuseStep 603329 = 452497) B452497
theorem B603347 : Blo 401768 603347 := bstep (se 1 (by rfl) ⟨452510, by rfl⟩ : syracuseStep 603347 = 905021) B905021
theorem B603377 : Blo 401768 603377 := bstep (se 2 (by rfl) ⟨226266, by rfl⟩ : syracuseStep 603377 = 452533) B452533
theorem B603395 : Blo 401768 603395 := bstep (se 1 (by rfl) ⟨452546, by rfl⟩ : syracuseStep 603395 = 905093) B905093
theorem B1357073 : Blo 401768 1357073 := bstep (se 2 (by rfl) ⟨508902, by rfl⟩ : syracuseStep 1357073 = 1017805) B1017805
theorem B603425 : Blo 401768 603425 := bstep (se 2 (by rfl) ⟨226284, by rfl⟩ : syracuseStep 603425 = 452569) B452569
theorem B603443 : Blo 401768 603443 := bstep (se 1 (by rfl) ⟨452582, by rfl⟩ : syracuseStep 603443 = 905165) B905165
theorem B603473 : Blo 401768 603473 := bstep (se 2 (by rfl) ⟨226302, by rfl⟩ : syracuseStep 603473 = 452605) B452605
theorem B603491 : Blo 401768 603491 := bstep (se 1 (by rfl) ⟨452618, by rfl⟩ : syracuseStep 603491 = 905237) B905237
theorem B603521 : Blo 401768 603521 := bstep (se 2 (by rfl) ⟨226320, by rfl⟩ : syracuseStep 603521 = 452641) B452641
theorem B603539 : Blo 401768 603539 := bstep (se 1 (by rfl) ⟨452654, by rfl⟩ : syracuseStep 603539 = 905309) B905309
theorem B603569 : Blo 401768 603569 := bstep (se 2 (by rfl) ⟨226338, by rfl⟩ : syracuseStep 603569 = 452677) B452677
theorem B603587 : Blo 401768 603587 := bstep (se 1 (by rfl) ⟨452690, by rfl⟩ : syracuseStep 603587 = 905381) B905381
theorem B865745 : Blo 401768 865745 := bstep (se 2 (by rfl) ⟨324654, by rfl⟩ : syracuseStep 865745 = 649309) B649309
theorem B603617 : Blo 401768 603617 := bstep (se 2 (by rfl) ⟨226356, by rfl⟩ : syracuseStep 603617 = 452713) B452713
theorem B2045411 : Blo 401768 2045411 := bstep (se 1 (by rfl) ⟨1534058, by rfl⟩ : syracuseStep 2045411 = 3068117) B3068117
theorem B603635 : Blo 401768 603635 := bstep (se 1 (by rfl) ⟨452726, by rfl⟩ : syracuseStep 603635 = 905453) B905453
theorem B603665 : Blo 401768 603665 := bstep (se 2 (by rfl) ⟨226374, by rfl⟩ : syracuseStep 603665 = 452749) B452749
theorem B603683 : Blo 401768 603683 := bstep (se 1 (by rfl) ⟨452762, by rfl⟩ : syracuseStep 603683 = 905525) B905525
theorem B603713 : Blo 401768 603713 := bstep (se 2 (by rfl) ⟨226392, by rfl⟩ : syracuseStep 603713 = 452785) B452785
theorem B767569 : Blo 401768 767569 := bstep (se 2 (by rfl) ⟨287838, by rfl⟩ : syracuseStep 767569 = 575677) B575677
theorem B603731 : Blo 401768 603731 := bstep (se 1 (by rfl) ⟨452798, by rfl⟩ : syracuseStep 603731 = 905597) B905597
theorem B1095277 : Blo 401768 1095277 := bstep (se 3 (by rfl) ⟨205364, by rfl⟩ : syracuseStep 1095277 = 410729) B410729
theorem B603761 : Blo 401768 603761 := bstep (se 2 (by rfl) ⟨226410, by rfl⟩ : syracuseStep 603761 = 452821) B452821
theorem B603779 : Blo 401768 603779 := bstep (se 1 (by rfl) ⟨452834, by rfl⟩ : syracuseStep 603779 = 905669) B905669
theorem B2340485 : Blo 401768 2340485 := bstep (se 4 (by rfl) ⟨219420, by rfl⟩ : syracuseStep 2340485 = 438841) B438841
theorem B603809 : Blo 401768 603809 := bstep (se 2 (by rfl) ⟨226428, by rfl⟩ : syracuseStep 603809 = 452857) B452857
theorem B603827 : Blo 401768 603827 := bstep (se 1 (by rfl) ⟨452870, by rfl⟩ : syracuseStep 603827 = 905741) B905741
theorem B603857 : Blo 401768 603857 := bstep (se 2 (by rfl) ⟨226446, by rfl⟩ : syracuseStep 603857 = 452893) B452893
theorem B603875 : Blo 401768 603875 := bstep (se 1 (by rfl) ⟨452906, by rfl⟩ : syracuseStep 603875 = 905813) B905813
theorem B603905 : Blo 401768 603905 := bstep (se 2 (by rfl) ⟨226464, by rfl⟩ : syracuseStep 603905 = 452929) B452929
theorem B603923 : Blo 401768 603923 := bstep (se 1 (by rfl) ⟨452942, by rfl⟩ : syracuseStep 603923 = 905885) B905885
theorem B1357613 : Blo 401768 1357613 := bstep (se 3 (by rfl) ⟨254552, by rfl⟩ : syracuseStep 1357613 = 509105) B509105
theorem B603953 : Blo 401768 603953 := bstep (se 2 (by rfl) ⟨226482, by rfl⟩ : syracuseStep 603953 = 452965) B452965
theorem B603971 : Blo 401768 603971 := bstep (se 1 (by rfl) ⟨452978, by rfl⟩ : syracuseStep 603971 = 905957) B905957
theorem B604001 : Blo 401768 604001 := bstep (se 2 (by rfl) ⟨226500, by rfl⟩ : syracuseStep 604001 = 453001) B453001
theorem B1357667 : Blo 401768 1357667 := bstep (se 1 (by rfl) ⟨1018250, by rfl⟩ : syracuseStep 1357667 = 2036501) B2036501
theorem B604019 : Blo 401768 604019 := bstep (se 1 (by rfl) ⟨453014, by rfl⟩ : syracuseStep 604019 = 906029) B906029
theorem B604049 : Blo 401768 604049 := bstep (se 2 (by rfl) ⟨226518, by rfl⟩ : syracuseStep 604049 = 453037) B453037
theorem B604067 : Blo 401768 604067 := bstep (se 1 (by rfl) ⟨453050, by rfl⟩ : syracuseStep 604067 = 906101) B906101
theorem B604097 : Blo 401768 604097 := bstep (se 2 (by rfl) ⟨226536, by rfl⟩ : syracuseStep 604097 = 453073) B453073
theorem B1292237 : Blo 401768 1292237 := bstep (se 3 (by rfl) ⟨242294, by rfl⟩ : syracuseStep 1292237 = 484589) B484589
theorem B604115 : Blo 401768 604115 := bstep (se 1 (by rfl) ⟨453086, by rfl⟩ : syracuseStep 604115 = 906173) B906173
theorem B767971 : Blo 401768 767971 := bstep (se 1 (by rfl) ⟨575978, by rfl⟩ : syracuseStep 767971 = 1151957) B1151957
theorem B604145 : Blo 401768 604145 := bstep (se 2 (by rfl) ⟨226554, by rfl⟩ : syracuseStep 604145 = 453109) B453109
theorem B604163 : Blo 401768 604163 := bstep (se 1 (by rfl) ⟨453122, by rfl⟩ : syracuseStep 604163 = 906245) B906245
theorem B768017 : Blo 401768 768017 := bstep (se 2 (by rfl) ⟨288006, by rfl⟩ : syracuseStep 768017 = 576013) B576013
theorem B604193 : Blo 401768 604193 := bstep (se 2 (by rfl) ⟨226572, by rfl⟩ : syracuseStep 604193 = 453145) B453145
theorem B604211 : Blo 401768 604211 := bstep (se 1 (by rfl) ⟨453158, by rfl⟩ : syracuseStep 604211 = 906317) B906317
theorem B14956597 : Blo 401768 14956597 := bstep (se 5 (by rfl) ⟨701090, by rfl⟩ : syracuseStep 14956597 = 1402181) B1402181
theorem B604241 : Blo 401768 604241 := bstep (se 2 (by rfl) ⟨226590, by rfl⟩ : syracuseStep 604241 = 453181) B453181
theorem B604259 : Blo 401768 604259 := bstep (se 1 (by rfl) ⟨453194, by rfl⟩ : syracuseStep 604259 = 906389) B906389
theorem B1357937 : Blo 401768 1357937 := bstep (se 2 (by rfl) ⟨509226, by rfl⟩ : syracuseStep 1357937 = 1018453) B1018453
theorem B604289 : Blo 401768 604289 := bstep (se 2 (by rfl) ⟨226608, by rfl⟩ : syracuseStep 604289 = 453217) B453217
theorem B604307 : Blo 401768 604307 := bstep (se 1 (by rfl) ⟨453230, by rfl⟩ : syracuseStep 604307 = 906461) B906461
theorem B1718435 : Blo 401768 1718435 := bstep (se 1 (by rfl) ⟨1288826, by rfl⟩ : syracuseStep 1718435 = 2577653) B2577653
theorem B604337 : Blo 401768 604337 := bstep (se 2 (by rfl) ⟨226626, by rfl⟩ : syracuseStep 604337 = 453253) B453253
theorem B604355 : Blo 401768 604355 := bstep (se 1 (by rfl) ⟨453266, by rfl⟩ : syracuseStep 604355 = 906533) B906533
theorem B604385 : Blo 401768 604385 := bstep (se 2 (by rfl) ⟨226644, by rfl⟩ : syracuseStep 604385 = 453289) B453289
theorem B866531 : Blo 401768 866531 := bstep (se 1 (by rfl) ⟨649898, by rfl⟩ : syracuseStep 866531 = 1299797) B1299797
theorem B604403 : Blo 401768 604403 := bstep (se 1 (by rfl) ⟨453302, by rfl⟩ : syracuseStep 604403 = 906605) B906605
theorem B2046221 : Blo 401768 2046221 := bstep (se 3 (by rfl) ⟨383666, by rfl⟩ : syracuseStep 2046221 = 767333) B767333
theorem B604433 : Blo 401768 604433 := bstep (se 2 (by rfl) ⟨226662, by rfl⟩ : syracuseStep 604433 = 453325) B453325
theorem B604451 : Blo 401768 604451 := bstep (se 1 (by rfl) ⟨453338, by rfl⟩ : syracuseStep 604451 = 906677) B906677
theorem B768305 : Blo 401768 768305 := bstep (se 2 (by rfl) ⟨288114, by rfl⟩ : syracuseStep 768305 = 576229) B576229
theorem B604481 : Blo 401768 604481 := bstep (se 2 (by rfl) ⟨226680, by rfl⟩ : syracuseStep 604481 = 453361) B453361
theorem B2079053 : Blo 401768 2079053 := bstep (se 3 (by rfl) ⟨389822, by rfl⟩ : syracuseStep 2079053 = 779645) B779645
theorem B604499 : Blo 401768 604499 := bstep (se 1 (by rfl) ⟨453374, by rfl⟩ : syracuseStep 604499 = 906749) B906749
theorem B604529 : Blo 401768 604529 := bstep (se 2 (by rfl) ⟨226698, by rfl⟩ : syracuseStep 604529 = 453397) B453397
theorem B604547 : Blo 401768 604547 := bstep (se 1 (by rfl) ⟨453410, by rfl⟩ : syracuseStep 604547 = 906821) B906821
theorem B604577 : Blo 401768 604577 := bstep (se 2 (by rfl) ⟨226716, by rfl⟩ : syracuseStep 604577 = 453433) B453433
theorem B604595 : Blo 401768 604595 := bstep (se 1 (by rfl) ⟨453446, by rfl⟩ : syracuseStep 604595 = 906893) B906893
theorem B604625 : Blo 401768 604625 := bstep (se 2 (by rfl) ⟨226734, by rfl⟩ : syracuseStep 604625 = 453469) B453469
theorem B604643 : Blo 401768 604643 := bstep (se 1 (by rfl) ⟨453482, by rfl⟩ : syracuseStep 604643 = 906965) B906965
theorem B604673 : Blo 401768 604673 := bstep (se 2 (by rfl) ⟨226752, by rfl⟩ : syracuseStep 604673 = 453505) B453505
theorem B3062285 : Blo 401768 3062285 := bstep (se 3 (by rfl) ⟨574178, by rfl⟩ : syracuseStep 3062285 = 1148357) B1148357
theorem B604691 : Blo 401768 604691 := bstep (se 1 (by rfl) ⟨453518, by rfl⟩ : syracuseStep 604691 = 907037) B907037
theorem B604721 : Blo 401768 604721 := bstep (se 2 (by rfl) ⟨226770, by rfl⟩ : syracuseStep 604721 = 453541) B453541
theorem B604739 : Blo 401768 604739 := bstep (se 1 (by rfl) ⟨453554, by rfl⟩ : syracuseStep 604739 = 907109) B907109
theorem B604769 : Blo 401768 604769 := bstep (se 2 (by rfl) ⟨226788, by rfl⟩ : syracuseStep 604769 = 453577) B453577
theorem B604787 : Blo 401768 604787 := bstep (se 1 (by rfl) ⟨453590, by rfl⟩ : syracuseStep 604787 = 907181) B907181
theorem B1227395 : Blo 401768 1227395 := bstep (se 1 (by rfl) ⟨920546, by rfl⟩ : syracuseStep 1227395 = 1841093) B1841093
theorem B1358477 : Blo 401768 1358477 := bstep (se 3 (by rfl) ⟨254714, by rfl⟩ : syracuseStep 1358477 = 509429) B509429
theorem B1849997 : Blo 401768 1849997 := bstep (se 3 (by rfl) ⟨346874, by rfl⟩ : syracuseStep 1849997 = 693749) B693749
theorem B604817 : Blo 401768 604817 := bstep (se 2 (by rfl) ⟨226806, by rfl⟩ : syracuseStep 604817 = 453613) B453613
theorem B604835 : Blo 401768 604835 := bstep (se 1 (by rfl) ⟨453626, by rfl⟩ : syracuseStep 604835 = 907253) B907253
theorem B604865 : Blo 401768 604865 := bstep (se 2 (by rfl) ⟨226824, by rfl⟩ : syracuseStep 604865 = 453649) B453649
theorem B1358531 : Blo 401768 1358531 := bstep (se 1 (by rfl) ⟨1018898, by rfl⟩ : syracuseStep 1358531 = 2037797) B2037797
theorem B604883 : Blo 401768 604883 := bstep (se 1 (by rfl) ⟨453662, by rfl⟩ : syracuseStep 604883 = 907325) B907325
theorem B604913 : Blo 401768 604913 := bstep (se 2 (by rfl) ⟨226842, by rfl⟩ : syracuseStep 604913 = 453685) B453685
theorem B604931 : Blo 401768 604931 := bstep (se 1 (by rfl) ⟨453698, by rfl⟩ : syracuseStep 604931 = 907397) B907397
theorem B604961 : Blo 401768 604961 := bstep (se 2 (by rfl) ⟨226860, by rfl⟩ : syracuseStep 604961 = 453721) B453721
theorem B604979 : Blo 401768 604979 := bstep (se 1 (by rfl) ⟨453734, by rfl⟩ : syracuseStep 604979 = 907469) B907469
theorem B605009 : Blo 401768 605009 := bstep (se 2 (by rfl) ⟨226878, by rfl⟩ : syracuseStep 605009 = 453757) B453757
theorem B605027 : Blo 401768 605027 := bstep (se 1 (by rfl) ⟨453770, by rfl⟩ : syracuseStep 605027 = 907541) B907541
theorem B605057 : Blo 401768 605057 := bstep (se 2 (by rfl) ⟨226896, by rfl⟩ : syracuseStep 605057 = 453793) B453793
theorem B605075 : Blo 401768 605075 := bstep (se 1 (by rfl) ⟨453806, by rfl⟩ : syracuseStep 605075 = 907613) B907613
theorem B605105 : Blo 401768 605105 := bstep (se 2 (by rfl) ⟨226914, by rfl⟩ : syracuseStep 605105 = 453829) B453829
theorem B605123 : Blo 401768 605123 := bstep (se 1 (by rfl) ⟨453842, by rfl⟩ : syracuseStep 605123 = 907685) B907685
theorem B1358801 : Blo 401768 1358801 := bstep (se 2 (by rfl) ⟨509550, by rfl⟩ : syracuseStep 1358801 = 1019101) B1019101
theorem B605153 : Blo 401768 605153 := bstep (se 2 (by rfl) ⟨226932, by rfl⟩ : syracuseStep 605153 = 453865) B453865
theorem B605171 : Blo 401768 605171 := bstep (se 1 (by rfl) ⟨453878, by rfl⟩ : syracuseStep 605171 = 907757) B907757
theorem B736259 : Blo 401768 736259 := bstep (se 1 (by rfl) ⟨552194, by rfl⟩ : syracuseStep 736259 = 1104389) B1104389
theorem B769027 : Blo 401768 769027 := bstep (se 1 (by rfl) ⟨576770, by rfl⟩ : syracuseStep 769027 = 1153541) B1153541
theorem B605201 : Blo 401768 605201 := bstep (se 2 (by rfl) ⟨226950, by rfl⟩ : syracuseStep 605201 = 453901) B453901
theorem B605219 : Blo 401768 605219 := bstep (se 1 (by rfl) ⟨453914, by rfl⟩ : syracuseStep 605219 = 907829) B907829
theorem B605249 : Blo 401768 605249 := bstep (se 2 (by rfl) ⟨226968, by rfl⟩ : syracuseStep 605249 = 453937) B453937
theorem B605267 : Blo 401768 605267 := bstep (se 1 (by rfl) ⟨453950, by rfl⟩ : syracuseStep 605267 = 907901) B907901
theorem B605297 : Blo 401768 605297 := bstep (se 2 (by rfl) ⟨226986, by rfl⟩ : syracuseStep 605297 = 453973) B453973
theorem B605315 : Blo 401768 605315 := bstep (se 1 (by rfl) ⟨453986, by rfl⟩ : syracuseStep 605315 = 907973) B907973
theorem B605345 : Blo 401768 605345 := bstep (se 2 (by rfl) ⟨227004, by rfl⟩ : syracuseStep 605345 = 454009) B454009
theorem B605363 : Blo 401768 605363 := bstep (se 1 (by rfl) ⟨454022, by rfl⟩ : syracuseStep 605363 = 908045) B908045
theorem B605393 : Blo 401768 605393 := bstep (se 2 (by rfl) ⟨227022, by rfl⟩ : syracuseStep 605393 = 454045) B454045
theorem B605411 : Blo 401768 605411 := bstep (se 1 (by rfl) ⟨454058, by rfl⟩ : syracuseStep 605411 = 908117) B908117
theorem B605441 : Blo 401768 605441 := bstep (se 2 (by rfl) ⟨227040, by rfl⟩ : syracuseStep 605441 = 454081) B454081
theorem B572675 : Blo 401768 572675 := bstep (se 1 (by rfl) ⟨429506, by rfl⟩ : syracuseStep 572675 = 859013) B859013
theorem B2309381 : Blo 401768 2309381 := bstep (se 4 (by rfl) ⟨216504, by rfl⟩ : syracuseStep 2309381 = 433009) B433009
theorem B605459 : Blo 401768 605459 := bstep (se 1 (by rfl) ⟨454094, by rfl⟩ : syracuseStep 605459 = 908189) B908189
theorem B605489 : Blo 401768 605489 := bstep (se 2 (by rfl) ⟨227058, by rfl⟩ : syracuseStep 605489 = 454117) B454117
theorem B605507 : Blo 401768 605507 := bstep (se 1 (by rfl) ⟨454130, by rfl⟩ : syracuseStep 605507 = 908261) B908261
theorem B605537 : Blo 401768 605537 := bstep (se 2 (by rfl) ⟨227076, by rfl⟩ : syracuseStep 605537 = 454153) B454153
theorem B605555 : Blo 401768 605555 := bstep (se 1 (by rfl) ⟨454166, by rfl⟩ : syracuseStep 605555 = 908333) B908333
theorem B605585 : Blo 401768 605585 := bstep (se 2 (by rfl) ⟨227094, by rfl⟩ : syracuseStep 605585 = 454189) B454189
theorem B605603 : Blo 401768 605603 := bstep (se 1 (by rfl) ⟨454202, by rfl⟩ : syracuseStep 605603 = 908405) B908405
theorem B605633 : Blo 401768 605633 := bstep (se 2 (by rfl) ⟨227112, by rfl⟩ : syracuseStep 605633 = 454225) B454225
theorem B769475 : Blo 401768 769475 := bstep (se 1 (by rfl) ⟨577106, by rfl⟩ : syracuseStep 769475 = 1154213) B1154213
theorem B605651 : Blo 401768 605651 := bstep (se 1 (by rfl) ⟨454238, by rfl⟩ : syracuseStep 605651 = 908477) B908477
theorem B1359341 : Blo 401768 1359341 := bstep (se 3 (by rfl) ⟨254876, by rfl⟩ : syracuseStep 1359341 = 509753) B509753
theorem B605681 : Blo 401768 605681 := bstep (se 2 (by rfl) ⟨227130, by rfl⟩ : syracuseStep 605681 = 454261) B454261
theorem B605699 : Blo 401768 605699 := bstep (se 1 (by rfl) ⟨454274, by rfl⟩ : syracuseStep 605699 = 908549) B908549
theorem B605729 : Blo 401768 605729 := bstep (se 2 (by rfl) ⟨227148, by rfl⟩ : syracuseStep 605729 = 454297) B454297
theorem B1359395 : Blo 401768 1359395 := bstep (se 1 (by rfl) ⟨1019546, by rfl⟩ : syracuseStep 1359395 = 2039093) B2039093
theorem B409123 : Blo 401768 409123 := bstep (se 1 (by rfl) ⟨306842, by rfl⟩ : syracuseStep 409123 = 613685) B613685
theorem B605747 : Blo 401768 605747 := bstep (se 1 (by rfl) ⟨454310, by rfl⟩ : syracuseStep 605747 = 908621) B908621
theorem B605777 : Blo 401768 605777 := bstep (se 2 (by rfl) ⟨227166, by rfl⟩ : syracuseStep 605777 = 454333) B454333
theorem B605795 : Blo 401768 605795 := bstep (se 1 (by rfl) ⟨454346, by rfl⟩ : syracuseStep 605795 = 908693) B908693
theorem B605825 : Blo 401768 605825 := bstep (se 2 (by rfl) ⟨227184, by rfl⟩ : syracuseStep 605825 = 454369) B454369
theorem B605843 : Blo 401768 605843 := bstep (se 1 (by rfl) ⟨454382, by rfl⟩ : syracuseStep 605843 = 908765) B908765
theorem B1556131 : Blo 401768 1556131 := bstep (se 1 (by rfl) ⟨1167098, by rfl⟩ : syracuseStep 1556131 = 2334197) B2334197
theorem B605873 : Blo 401768 605873 := bstep (se 2 (by rfl) ⟨227202, by rfl⟩ : syracuseStep 605873 = 454405) B454405
theorem B605891 : Blo 401768 605891 := bstep (se 1 (by rfl) ⟨454418, by rfl⟩ : syracuseStep 605891 = 908837) B908837
theorem B605921 : Blo 401768 605921 := bstep (se 2 (by rfl) ⟨227220, by rfl⟩ : syracuseStep 605921 = 454441) B454441
theorem B4898531 : Blo 401768 4898531 := bstep (se 1 (by rfl) ⟨3673898, by rfl⟩ : syracuseStep 4898531 = 7347797) B7347797
theorem B769763 : Blo 401768 769763 := bstep (se 1 (by rfl) ⟨577322, by rfl⟩ : syracuseStep 769763 = 1154645) B1154645
theorem B605939 : Blo 401768 605939 := bstep (se 1 (by rfl) ⟨454454, by rfl⟩ : syracuseStep 605939 = 908909) B908909
theorem B605969 : Blo 401768 605969 := bstep (se 2 (by rfl) ⟨227238, by rfl⟩ : syracuseStep 605969 = 454477) B454477
theorem B409379 : Blo 401768 409379 := bstep (se 1 (by rfl) ⟨307034, by rfl⟩ : syracuseStep 409379 = 614069) B614069
theorem B605987 : Blo 401768 605987 := bstep (se 1 (by rfl) ⟨454490, by rfl⟩ : syracuseStep 605987 = 908981) B908981
theorem B1359665 : Blo 401768 1359665 := bstep (se 2 (by rfl) ⟨509874, by rfl⟩ : syracuseStep 1359665 = 1019749) B1019749
theorem B606017 : Blo 401768 606017 := bstep (se 2 (by rfl) ⟨227256, by rfl⟩ : syracuseStep 606017 = 454513) B454513
theorem B966467 : Blo 401768 966467 := bstep (se 1 (by rfl) ⟨724850, by rfl⟩ : syracuseStep 966467 = 1449701) B1449701
theorem B606035 : Blo 401768 606035 := bstep (se 1 (by rfl) ⟨454526, by rfl⟩ : syracuseStep 606035 = 909053) B909053
theorem B606065 : Blo 401768 606065 := bstep (se 2 (by rfl) ⟨227274, by rfl⟩ : syracuseStep 606065 = 454549) B454549
theorem B573313 : Blo 401768 573313 := bstep (se 2 (by rfl) ⟨214992, by rfl⟩ : syracuseStep 573313 = 429985) B429985
theorem B606083 : Blo 401768 606083 := bstep (se 1 (by rfl) ⟨454562, by rfl⟩ : syracuseStep 606083 = 909125) B909125
theorem B606113 : Blo 401768 606113 := bstep (se 2 (by rfl) ⟨227292, by rfl⟩ : syracuseStep 606113 = 454585) B454585
theorem B540577 : Blo 401768 540577 := bstep (se 2 (by rfl) ⟨202716, by rfl⟩ : syracuseStep 540577 = 405433) B405433
theorem B2310065 : Blo 401768 2310065 := bstep (se 2 (by rfl) ⟨866274, by rfl⟩ : syracuseStep 2310065 = 1732549) B1732549
theorem B606131 : Blo 401768 606131 := bstep (se 1 (by rfl) ⟨454598, by rfl⟩ : syracuseStep 606131 = 909197) B909197
theorem B4440005 : Blo 401768 4440005 := bstep (se 4 (by rfl) ⟨416250, by rfl⟩ : syracuseStep 4440005 = 832501) B832501
theorem B606161 : Blo 401768 606161 := bstep (se 2 (by rfl) ⟨227310, by rfl⟩ : syracuseStep 606161 = 454621) B454621
theorem B606179 : Blo 401768 606179 := bstep (se 1 (by rfl) ⟨454634, by rfl⟩ : syracuseStep 606179 = 909269) B909269
theorem B573427 : Blo 401768 573427 := bstep (se 1 (by rfl) ⟨430070, by rfl⟩ : syracuseStep 573427 = 860141) B860141
theorem B606209 : Blo 401768 606209 := bstep (se 2 (by rfl) ⟨227328, by rfl⟩ : syracuseStep 606209 = 454657) B454657
theorem B606227 : Blo 401768 606227 := bstep (se 1 (by rfl) ⟨454670, by rfl⟩ : syracuseStep 606227 = 909341) B909341
theorem B606257 : Blo 401768 606257 := bstep (se 2 (by rfl) ⟨227346, by rfl⟩ : syracuseStep 606257 = 454693) B454693
theorem B606275 : Blo 401768 606275 := bstep (se 1 (by rfl) ⟨454706, by rfl⟩ : syracuseStep 606275 = 909413) B909413
theorem B606305 : Blo 401768 606305 := bstep (se 2 (by rfl) ⟨227364, by rfl⟩ : syracuseStep 606305 = 454729) B454729
theorem B606323 : Blo 401768 606323 := bstep (se 1 (by rfl) ⟨454742, by rfl⟩ : syracuseStep 606323 = 909485) B909485
theorem B606353 : Blo 401768 606353 := bstep (se 2 (by rfl) ⟨227382, by rfl⟩ : syracuseStep 606353 = 454765) B454765
theorem B606371 : Blo 401768 606371 := bstep (se 1 (by rfl) ⟨454778, by rfl⟩ : syracuseStep 606371 = 909557) B909557
theorem B606401 : Blo 401768 606401 := bstep (se 2 (by rfl) ⟨227400, by rfl⟩ : syracuseStep 606401 = 454801) B454801
theorem B606419 : Blo 401768 606419 := bstep (se 1 (by rfl) ⟨454814, by rfl⟩ : syracuseStep 606419 = 909629) B909629
theorem B606449 : Blo 401768 606449 := bstep (se 2 (by rfl) ⟨227418, by rfl⟩ : syracuseStep 606449 = 454837) B454837
theorem B606467 : Blo 401768 606467 := bstep (se 1 (by rfl) ⟨454850, by rfl⟩ : syracuseStep 606467 = 909701) B909701
theorem B606497 : Blo 401768 606497 := bstep (se 2 (by rfl) ⟨227436, by rfl⟩ : syracuseStep 606497 = 454873) B454873
theorem B606515 : Blo 401768 606515 := bstep (se 1 (by rfl) ⟨454886, by rfl⟩ : syracuseStep 606515 = 909773) B909773
theorem B2769221 : Blo 401768 2769221 := bstep (se 4 (by rfl) ⟨259614, by rfl⟩ : syracuseStep 2769221 = 519229) B519229
theorem B1360205 : Blo 401768 1360205 := bstep (se 3 (by rfl) ⟨255038, by rfl⟩ : syracuseStep 1360205 = 510077) B510077
theorem B606545 : Blo 401768 606545 := bstep (se 2 (by rfl) ⟨227454, by rfl⟩ : syracuseStep 606545 = 454909) B454909
theorem B606563 : Blo 401768 606563 := bstep (se 1 (by rfl) ⟨454922, by rfl⟩ : syracuseStep 606563 = 909845) B909845
theorem B606593 : Blo 401768 606593 := bstep (se 2 (by rfl) ⟨227472, by rfl⟩ : syracuseStep 606593 = 454945) B454945
theorem B1360259 : Blo 401768 1360259 := bstep (se 1 (by rfl) ⟨1020194, by rfl⟩ : syracuseStep 1360259 = 2040389) B2040389
theorem B606611 : Blo 401768 606611 := bstep (se 1 (by rfl) ⟨454958, by rfl⟩ : syracuseStep 606611 = 909917) B909917
theorem B1229219 : Blo 401768 1229219 := bstep (se 1 (by rfl) ⟨921914, by rfl⟩ : syracuseStep 1229219 = 1843829) B1843829
theorem B606641 : Blo 401768 606641 := bstep (se 2 (by rfl) ⟨227490, by rfl⟩ : syracuseStep 606641 = 454981) B454981
theorem B606659 : Blo 401768 606659 := bstep (se 1 (by rfl) ⟨454994, by rfl⟩ : syracuseStep 606659 = 909989) B909989
theorem B606689 : Blo 401768 606689 := bstep (se 2 (by rfl) ⟨227508, by rfl⟩ : syracuseStep 606689 = 455017) B455017
theorem B606707 : Blo 401768 606707 := bstep (se 1 (by rfl) ⟨455030, by rfl⟩ : syracuseStep 606707 = 910061) B910061
theorem B606737 : Blo 401768 606737 := bstep (se 2 (by rfl) ⟨227526, by rfl⟩ : syracuseStep 606737 = 455053) B455053
theorem B606755 : Blo 401768 606755 := bstep (se 1 (by rfl) ⟨455066, by rfl⟩ : syracuseStep 606755 = 910133) B910133
theorem B606785 : Blo 401768 606785 := bstep (se 2 (by rfl) ⟨227544, by rfl⟩ : syracuseStep 606785 = 455089) B455089
theorem B967235 : Blo 401768 967235 := bstep (se 1 (by rfl) ⟨725426, by rfl⟩ : syracuseStep 967235 = 1450853) B1450853
theorem B606803 : Blo 401768 606803 := bstep (se 1 (by rfl) ⟨455102, by rfl⟩ : syracuseStep 606803 = 910205) B910205
theorem B606833 : Blo 401768 606833 := bstep (se 2 (by rfl) ⟨227562, by rfl⟩ : syracuseStep 606833 = 455125) B455125
theorem B606851 : Blo 401768 606851 := bstep (se 1 (by rfl) ⟨455138, by rfl⟩ : syracuseStep 606851 = 910277) B910277
theorem B1360529 : Blo 401768 1360529 := bstep (se 2 (by rfl) ⟨510198, by rfl⟩ : syracuseStep 1360529 = 1020397) B1020397
theorem B606881 : Blo 401768 606881 := bstep (se 2 (by rfl) ⟨227580, by rfl⟩ : syracuseStep 606881 = 455161) B455161
theorem B606899 : Blo 401768 606899 := bstep (se 1 (by rfl) ⟨455174, by rfl⟩ : syracuseStep 606899 = 910349) B910349
theorem B606929 : Blo 401768 606929 := bstep (se 2 (by rfl) ⟨227598, by rfl⟩ : syracuseStep 606929 = 455197) B455197
theorem B606947 : Blo 401768 606947 := bstep (se 1 (by rfl) ⟨455210, by rfl⟩ : syracuseStep 606947 = 910421) B910421
theorem B606977 : Blo 401768 606977 := bstep (se 2 (by rfl) ⟨227616, by rfl⟩ : syracuseStep 606977 = 455233) B455233
theorem B508675 : Blo 401768 508675 := bstep (se 1 (by rfl) ⟨381506, by rfl⟩ : syracuseStep 508675 = 763013) B763013
theorem B1721101 : Blo 401768 1721101 := bstep (se 3 (by rfl) ⟨322706, by rfl⟩ : syracuseStep 1721101 = 645413) B645413
theorem B606995 : Blo 401768 606995 := bstep (se 1 (by rfl) ⟨455246, by rfl⟩ : syracuseStep 606995 = 910493) B910493
theorem B607025 : Blo 401768 607025 := bstep (se 2 (by rfl) ⟨227634, by rfl⟩ : syracuseStep 607025 = 455269) B455269
theorem B607043 : Blo 401768 607043 := bstep (se 1 (by rfl) ⟨455282, by rfl⟩ : syracuseStep 607043 = 910565) B910565
theorem B607073 : Blo 401768 607073 := bstep (se 2 (by rfl) ⟨227652, by rfl⟩ : syracuseStep 607073 = 455305) B455305
theorem B508771 : Blo 401768 508771 := bstep (se 1 (by rfl) ⟨381578, by rfl⟩ : syracuseStep 508771 = 763157) B763157
theorem B607091 : Blo 401768 607091 := bstep (se 1 (by rfl) ⟨455318, by rfl⟩ : syracuseStep 607091 = 910637) B910637
theorem B607121 : Blo 401768 607121 := bstep (se 2 (by rfl) ⟨227670, by rfl⟩ : syracuseStep 607121 = 455341) B455341
theorem B607139 : Blo 401768 607139 := bstep (se 1 (by rfl) ⟨455354, by rfl⟩ : syracuseStep 607139 = 910709) B910709
theorem B607169 : Blo 401768 607169 := bstep (se 2 (by rfl) ⟨227688, by rfl⟩ : syracuseStep 607169 = 455377) B455377
theorem B607187 : Blo 401768 607187 := bstep (se 1 (by rfl) ⟨455390, by rfl⟩ : syracuseStep 607187 = 910781) B910781
theorem B607217 : Blo 401768 607217 := bstep (se 2 (by rfl) ⟨227706, by rfl⟩ : syracuseStep 607217 = 455413) B455413
theorem B607235 : Blo 401768 607235 := bstep (se 1 (by rfl) ⟨455426, by rfl⟩ : syracuseStep 607235 = 910853) B910853
theorem B3687437 : Blo 401768 3687437 := bstep (se 3 (by rfl) ⟨691394, by rfl⟩ : syracuseStep 3687437 = 1382789) B1382789
theorem B967697 : Blo 401768 967697 := bstep (se 2 (by rfl) ⟨362886, by rfl⟩ : syracuseStep 967697 = 725773) B725773
theorem B607265 : Blo 401768 607265 := bstep (se 2 (by rfl) ⟨227724, by rfl⟩ : syracuseStep 607265 = 455449) B455449
theorem B607283 : Blo 401768 607283 := bstep (se 1 (by rfl) ⟨455462, by rfl⟩ : syracuseStep 607283 = 910925) B910925
theorem B607313 : Blo 401768 607313 := bstep (se 2 (by rfl) ⟨227742, by rfl⟩ : syracuseStep 607313 = 455485) B455485
theorem B607331 : Blo 401768 607331 := bstep (se 1 (by rfl) ⟨455498, by rfl⟩ : syracuseStep 607331 = 910997) B910997
theorem B967793 : Blo 401768 967793 := bstep (se 2 (by rfl) ⟨362922, by rfl⟩ : syracuseStep 967793 = 725845) B725845
theorem B2049137 : Blo 401768 2049137 := bstep (se 2 (by rfl) ⟨768426, by rfl⟩ : syracuseStep 2049137 = 1536853) B1536853
theorem B607361 : Blo 401768 607361 := bstep (se 2 (by rfl) ⟨227760, by rfl⟩ : syracuseStep 607361 = 455521) B455521
theorem B607379 : Blo 401768 607379 := bstep (se 1 (by rfl) ⟨455534, by rfl⟩ : syracuseStep 607379 = 911069) B911069
theorem B1361069 : Blo 401768 1361069 := bstep (se 3 (by rfl) ⟨255200, by rfl⟩ : syracuseStep 1361069 = 510401) B510401
theorem B607409 : Blo 401768 607409 := bstep (se 2 (by rfl) ⟨227778, by rfl⟩ : syracuseStep 607409 = 455557) B455557
theorem B607427 : Blo 401768 607427 := bstep (se 1 (by rfl) ⟨455570, by rfl⟩ : syracuseStep 607427 = 911141) B911141
theorem B607457 : Blo 401768 607457 := bstep (se 2 (by rfl) ⟨227796, by rfl⟩ : syracuseStep 607457 = 455593) B455593
theorem B1361123 : Blo 401768 1361123 := bstep (se 1 (by rfl) ⟨1020842, by rfl⟩ : syracuseStep 1361123 = 2041685) B2041685
theorem B607475 : Blo 401768 607475 := bstep (se 1 (by rfl) ⟨455606, by rfl⟩ : syracuseStep 607475 = 911213) B911213
theorem B1230083 : Blo 401768 1230083 := bstep (se 1 (by rfl) ⟨922562, by rfl⟩ : syracuseStep 1230083 = 1845125) B1845125
theorem B607505 : Blo 401768 607505 := bstep (se 2 (by rfl) ⟨227814, by rfl⟩ : syracuseStep 607505 = 455629) B455629
theorem B607523 : Blo 401768 607523 := bstep (se 1 (by rfl) ⟨455642, by rfl⟩ : syracuseStep 607523 = 911285) B911285
theorem B1557809 : Blo 401768 1557809 := bstep (se 2 (by rfl) ⟨584178, by rfl⟩ : syracuseStep 1557809 = 1168357) B1168357
theorem B574771 : Blo 401768 574771 := bstep (se 1 (by rfl) ⟨431078, by rfl⟩ : syracuseStep 574771 = 862157) B862157
theorem B607553 : Blo 401768 607553 := bstep (se 2 (by rfl) ⟨227832, by rfl⟩ : syracuseStep 607553 = 455665) B455665
theorem B509267 : Blo 401768 509267 := bstep (se 1 (by rfl) ⟨381950, by rfl⟩ : syracuseStep 509267 = 763901) B763901
theorem B607571 : Blo 401768 607571 := bstep (se 1 (by rfl) ⟨455678, by rfl⟩ : syracuseStep 607571 = 911357) B911357
theorem B3065201 : Blo 401768 3065201 := bstep (se 2 (by rfl) ⟨1149450, by rfl⟩ : syracuseStep 3065201 = 2298901) B2298901
theorem B607601 : Blo 401768 607601 := bstep (se 2 (by rfl) ⟨227850, by rfl⟩ : syracuseStep 607601 = 455701) B455701
theorem B1295747 : Blo 401768 1295747 := bstep (se 1 (by rfl) ⟨971810, by rfl⟩ : syracuseStep 1295747 = 1943621) B1943621
theorem B607619 : Blo 401768 607619 := bstep (se 1 (by rfl) ⟨455714, by rfl⟩ : syracuseStep 607619 = 911429) B911429
theorem B607649 : Blo 401768 607649 := bstep (se 2 (by rfl) ⟨227868, by rfl⟩ : syracuseStep 607649 = 455737) B455737
theorem B607667 : Blo 401768 607667 := bstep (se 1 (by rfl) ⟨455750, by rfl⟩ : syracuseStep 607667 = 911501) B911501
theorem B607697 : Blo 401768 607697 := bstep (se 2 (by rfl) ⟨227886, by rfl⟩ : syracuseStep 607697 = 455773) B455773
theorem B607715 : Blo 401768 607715 := bstep (se 1 (by rfl) ⟨455786, by rfl⟩ : syracuseStep 607715 = 911573) B911573
theorem B1361393 : Blo 401768 1361393 := bstep (se 2 (by rfl) ⟨510522, by rfl⟩ : syracuseStep 1361393 = 1021045) B1021045
theorem B607745 : Blo 401768 607745 := bstep (se 2 (by rfl) ⟨227904, by rfl⟩ : syracuseStep 607745 = 455809) B455809
theorem B574993 : Blo 401768 574993 := bstep (se 2 (by rfl) ⟨215622, by rfl⟩ : syracuseStep 574993 = 431245) B431245
theorem B607763 : Blo 401768 607763 := bstep (se 1 (by rfl) ⟨455822, by rfl⟩ : syracuseStep 607763 = 911645) B911645
theorem B607793 : Blo 401768 607793 := bstep (se 2 (by rfl) ⟨227922, by rfl⟩ : syracuseStep 607793 = 455845) B455845
theorem B607811 : Blo 401768 607811 := bstep (se 1 (by rfl) ⟨455858, by rfl⟩ : syracuseStep 607811 = 911717) B911717
theorem B607841 : Blo 401768 607841 := bstep (se 2 (by rfl) ⟨227940, by rfl⟩ : syracuseStep 607841 = 455881) B455881
theorem B607859 : Blo 401768 607859 := bstep (se 1 (by rfl) ⟨455894, by rfl⟩ : syracuseStep 607859 = 911789) B911789
theorem B607889 : Blo 401768 607889 := bstep (se 2 (by rfl) ⟨227958, by rfl⟩ : syracuseStep 607889 = 455917) B455917
theorem B607907 : Blo 401768 607907 := bstep (se 1 (by rfl) ⟨455930, by rfl⟩ : syracuseStep 607907 = 911861) B911861
theorem B607937 : Blo 401768 607937 := bstep (se 2 (by rfl) ⟨227976, by rfl⟩ : syracuseStep 607937 = 455953) B455953
theorem B607955 : Blo 401768 607955 := bstep (se 1 (by rfl) ⟨455966, by rfl⟩ : syracuseStep 607955 = 911933) B911933
theorem B607985 : Blo 401768 607985 := bstep (se 2 (by rfl) ⟨227994, by rfl⟩ : syracuseStep 607985 = 455989) B455989
theorem B608003 : Blo 401768 608003 := bstep (se 1 (by rfl) ⟨456002, by rfl⟩ : syracuseStep 608003 = 912005) B912005
theorem B608033 : Blo 401768 608033 := bstep (se 2 (by rfl) ⟨228012, by rfl⟩ : syracuseStep 608033 = 456025) B456025
theorem B1722161 : Blo 401768 1722161 := bstep (se 2 (by rfl) ⟨645810, by rfl⟩ : syracuseStep 1722161 = 1291621) B1291621
theorem B608051 : Blo 401768 608051 := bstep (se 1 (by rfl) ⟨456038, by rfl⟩ : syracuseStep 608051 = 912077) B912077
theorem B608081 : Blo 401768 608081 := bstep (se 2 (by rfl) ⟨228030, by rfl⟩ : syracuseStep 608081 = 456061) B456061
theorem B608099 : Blo 401768 608099 := bstep (se 1 (by rfl) ⟨456074, by rfl⟩ : syracuseStep 608099 = 912149) B912149
theorem B608129 : Blo 401768 608129 := bstep (se 2 (by rfl) ⟨228048, by rfl⟩ : syracuseStep 608129 = 456097) B456097
theorem B608147 : Blo 401768 608147 := bstep (se 1 (by rfl) ⟨456110, by rfl⟩ : syracuseStep 608147 = 912221) B912221
theorem B608177 : Blo 401768 608177 := bstep (se 2 (by rfl) ⟨228066, by rfl⟩ : syracuseStep 608177 = 456133) B456133
theorem B608195 : Blo 401768 608195 := bstep (se 1 (by rfl) ⟨456146, by rfl⟩ : syracuseStep 608195 = 912293) B912293
theorem B1296337 : Blo 401768 1296337 := bstep (se 2 (by rfl) ⟨486126, by rfl⟩ : syracuseStep 1296337 = 972253) B972253
theorem B608225 : Blo 401768 608225 := bstep (se 2 (by rfl) ⟨228084, by rfl⟩ : syracuseStep 608225 = 456169) B456169
theorem B1460195 : Blo 401768 1460195 := bstep (se 1 (by rfl) ⟨1095146, by rfl⟩ : syracuseStep 1460195 = 2190293) B2190293
theorem B608243 : Blo 401768 608243 := bstep (se 1 (by rfl) ⟨456182, by rfl⟩ : syracuseStep 608243 = 912365) B912365
theorem B1361933 : Blo 401768 1361933 := bstep (se 3 (by rfl) ⟨255362, by rfl⟩ : syracuseStep 1361933 = 510725) B510725
theorem B608273 : Blo 401768 608273 := bstep (se 2 (by rfl) ⟨228102, by rfl⟩ : syracuseStep 608273 = 456205) B456205
theorem B509971 : Blo 401768 509971 := bstep (se 1 (by rfl) ⟨382478, by rfl⟩ : syracuseStep 509971 = 764957) B764957
theorem B608291 : Blo 401768 608291 := bstep (se 1 (by rfl) ⟨456218, by rfl⟩ : syracuseStep 608291 = 912437) B912437
theorem B608321 : Blo 401768 608321 := bstep (se 2 (by rfl) ⟨228120, by rfl⟩ : syracuseStep 608321 = 456241) B456241
theorem B1361987 : Blo 401768 1361987 := bstep (se 1 (by rfl) ⟨1021490, by rfl⟩ : syracuseStep 1361987 = 2042981) B2042981
theorem B608339 : Blo 401768 608339 := bstep (se 1 (by rfl) ⟨456254, by rfl⟩ : syracuseStep 608339 = 912509) B912509
theorem B608369 : Blo 401768 608369 := bstep (se 2 (by rfl) ⟨228138, by rfl⟩ : syracuseStep 608369 = 456277) B456277
theorem B510067 : Blo 401768 510067 := bstep (se 1 (by rfl) ⟨382550, by rfl⟩ : syracuseStep 510067 = 765101) B765101
theorem B608387 : Blo 401768 608387 := bstep (se 1 (by rfl) ⟨456290, by rfl⟩ : syracuseStep 608387 = 912581) B912581
theorem B608417 : Blo 401768 608417 := bstep (se 2 (by rfl) ⟨228156, by rfl⟩ : syracuseStep 608417 = 456313) B456313
theorem B608435 : Blo 401768 608435 := bstep (se 1 (by rfl) ⟨456326, by rfl⟩ : syracuseStep 608435 = 912653) B912653
theorem B608465 : Blo 401768 608465 := bstep (se 2 (by rfl) ⟨228174, by rfl⟩ : syracuseStep 608465 = 456349) B456349
theorem B608483 : Blo 401768 608483 := bstep (se 1 (by rfl) ⟨456362, by rfl⟩ : syracuseStep 608483 = 912725) B912725
theorem B608513 : Blo 401768 608513 := bstep (se 2 (by rfl) ⟨228192, by rfl⟩ : syracuseStep 608513 = 456385) B456385
theorem B608531 : Blo 401768 608531 := bstep (se 1 (by rfl) ⟨456398, by rfl⟩ : syracuseStep 608531 = 912797) B912797
theorem B608561 : Blo 401768 608561 := bstep (se 2 (by rfl) ⟨228210, by rfl⟩ : syracuseStep 608561 = 456421) B456421
theorem B6932789 : Blo 401768 6932789 := bstep (se 5 (by rfl) ⟨324974, by rfl⟩ : syracuseStep 6932789 = 649949) B649949
theorem B608579 : Blo 401768 608579 := bstep (se 1 (by rfl) ⟨456434, by rfl⟩ : syracuseStep 608579 = 912869) B912869
theorem B1362257 : Blo 401768 1362257 := bstep (se 2 (by rfl) ⟨510846, by rfl⟩ : syracuseStep 1362257 = 1021693) B1021693
theorem B608609 : Blo 401768 608609 := bstep (se 2 (by rfl) ⟨228228, by rfl⟩ : syracuseStep 608609 = 456457) B456457
theorem B608627 : Blo 401768 608627 := bstep (se 1 (by rfl) ⟨456470, by rfl⟩ : syracuseStep 608627 = 912941) B912941
theorem B575905 : Blo 401768 575905 := bstep (se 2 (by rfl) ⟨215964, by rfl⟩ : syracuseStep 575905 = 431929) B431929
theorem B576001 : Blo 401768 576001 := bstep (se 2 (by rfl) ⟨216000, by rfl⟩ : syracuseStep 576001 = 432001) B432001
theorem B2050595 : Blo 401768 2050595 := bstep (se 1 (by rfl) ⟨1537946, by rfl⟩ : syracuseStep 2050595 = 3075893) B3075893
theorem B510563 : Blo 401768 510563 := bstep (se 1 (by rfl) ⟨382922, by rfl⟩ : syracuseStep 510563 = 765845) B765845
theorem B2574989 : Blo 401768 2574989 := bstep (se 3 (by rfl) ⟨482810, by rfl⟩ : syracuseStep 2574989 = 965621) B965621
theorem B1526435 : Blo 401768 1526435 := bstep (se 1 (by rfl) ⟨1144826, by rfl⟩ : syracuseStep 1526435 = 2289653) B2289653
theorem B5327669 : Blo 401768 5327669 := bstep (se 5 (by rfl) ⟨249734, by rfl⟩ : syracuseStep 5327669 = 499469) B499469
theorem B1362797 : Blo 401768 1362797 := bstep (se 3 (by rfl) ⟨255524, by rfl⟩ : syracuseStep 1362797 = 511049) B511049
theorem B904049 : Blo 401768 904049 := bstep (se 2 (by rfl) ⟨339018, by rfl⟩ : syracuseStep 904049 = 678037) B678037
theorem B904067 : Blo 401768 904067 := bstep (se 1 (by rfl) ⟨678050, by rfl⟩ : syracuseStep 904067 = 1356101) B1356101
theorem B1362851 : Blo 401768 1362851 := bstep (se 1 (by rfl) ⟨1022138, by rfl⟩ : syracuseStep 1362851 = 2044277) B2044277
theorem B576497 : Blo 401768 576497 := bstep (se 2 (by rfl) ⟨216186, by rfl⟩ : syracuseStep 576497 = 432373) B432373
theorem B1461233 : Blo 401768 1461233 := bstep (se 2 (by rfl) ⟨547962, by rfl⟩ : syracuseStep 1461233 = 1095925) B1095925
theorem B904337 : Blo 401768 904337 := bstep (se 2 (by rfl) ⟨339126, by rfl⟩ : syracuseStep 904337 = 678253) B678253
theorem B904355 : Blo 401768 904355 := bstep (se 1 (by rfl) ⟨678266, by rfl⟩ : syracuseStep 904355 = 1356533) B1356533
theorem B1363121 : Blo 401768 1363121 := bstep (se 2 (by rfl) ⟨511170, by rfl⟩ : syracuseStep 1363121 = 1022341) B1022341
theorem B511267 : Blo 401768 511267 := bstep (se 1 (by rfl) ⟨383450, by rfl⟩ : syracuseStep 511267 = 766901) B766901
theorem B2051405 : Blo 401768 2051405 := bstep (se 3 (by rfl) ⟨384638, by rfl⟩ : syracuseStep 2051405 = 769277) B769277
theorem B511363 : Blo 401768 511363 := bstep (se 1 (by rfl) ⟨383522, by rfl⟩ : syracuseStep 511363 = 767045) B767045
theorem B5819789 : Blo 401768 5819789 := bstep (se 3 (by rfl) ⟨1091210, by rfl⟩ : syracuseStep 5819789 = 2182421) B2182421
theorem B904625 : Blo 401768 904625 := bstep (se 2 (by rfl) ⟨339234, by rfl⟩ : syracuseStep 904625 = 678469) B678469
theorem B904643 : Blo 401768 904643 := bstep (se 1 (by rfl) ⟨678482, by rfl⟩ : syracuseStep 904643 = 1356965) B1356965
theorem B544243 : Blo 401768 544243 := bstep (se 1 (by rfl) ⟨408182, by rfl⟩ : syracuseStep 544243 = 816365) B816365
theorem B4574773 : Blo 401768 4574773 := bstep (se 5 (by rfl) ⟨214442, by rfl⟩ : syracuseStep 4574773 = 428885) B428885
theorem B1527437 : Blo 401768 1527437 := bstep (se 3 (by rfl) ⟨286394, by rfl⟩ : syracuseStep 1527437 = 572789) B572789
theorem B1756835 : Blo 401768 1756835 := bstep (se 1 (by rfl) ⟨1317626, by rfl⟩ : syracuseStep 1756835 = 2635253) B2635253
theorem B1363661 : Blo 401768 1363661 := bstep (se 3 (by rfl) ⟨255686, by rfl⟩ : syracuseStep 1363661 = 511373) B511373
theorem B904913 : Blo 401768 904913 := bstep (se 2 (by rfl) ⟨339342, by rfl⟩ : syracuseStep 904913 = 678685) B678685
theorem B904931 : Blo 401768 904931 := bstep (se 1 (by rfl) ⟨678698, by rfl⟩ : syracuseStep 904931 = 1357397) B1357397
theorem B1363715 : Blo 401768 1363715 := bstep (se 1 (by rfl) ⟨1022786, by rfl⟩ : syracuseStep 1363715 = 2045573) B2045573
theorem B577363 : Blo 401768 577363 := bstep (se 1 (by rfl) ⟨433022, by rfl⟩ : syracuseStep 577363 = 866045) B866045
theorem B511859 : Blo 401768 511859 := bstep (se 1 (by rfl) ⟨383894, by rfl⟩ : syracuseStep 511859 = 767789) B767789
theorem B1462157 : Blo 401768 1462157 := bstep (se 3 (by rfl) ⟨274154, by rfl⟩ : syracuseStep 1462157 = 548309) B548309
theorem B577459 : Blo 401768 577459 := bstep (se 1 (by rfl) ⟨433094, by rfl⟩ : syracuseStep 577459 = 866189) B866189
theorem B905201 : Blo 401768 905201 := bstep (se 2 (by rfl) ⟨339450, by rfl⟩ : syracuseStep 905201 = 678901) B678901
theorem B905219 : Blo 401768 905219 := bstep (se 1 (by rfl) ⟨678914, by rfl⟩ : syracuseStep 905219 = 1357829) B1357829
theorem B1363985 : Blo 401768 1363985 := bstep (se 2 (by rfl) ⟨511494, by rfl⟩ : syracuseStep 1363985 = 1022989) B1022989
theorem B544801 : Blo 401768 544801 := bstep (se 2 (by rfl) ⟨204300, by rfl⟩ : syracuseStep 544801 = 408601) B408601
theorem B905489 : Blo 401768 905489 := bstep (se 2 (by rfl) ⟨339558, by rfl⟩ : syracuseStep 905489 = 679117) B679117
theorem B905507 : Blo 401768 905507 := bstep (se 1 (by rfl) ⟨679130, by rfl⟩ : syracuseStep 905507 = 1358261) B1358261
theorem B1364525 : Blo 401768 1364525 := bstep (se 3 (by rfl) ⟨255848, by rfl⟩ : syracuseStep 1364525 = 511697) B511697
theorem B905777 : Blo 401768 905777 := bstep (se 2 (by rfl) ⟨339666, by rfl⟩ : syracuseStep 905777 = 679333) B679333
theorem B512563 : Blo 401768 512563 := bstep (se 1 (by rfl) ⟨384422, by rfl⟩ : syracuseStep 512563 = 768845) B768845
theorem B905795 : Blo 401768 905795 := bstep (se 1 (by rfl) ⟨679346, by rfl⟩ : syracuseStep 905795 = 1358693) B1358693
theorem B1364579 : Blo 401768 1364579 := bstep (se 1 (by rfl) ⟨1023434, by rfl⟩ : syracuseStep 1364579 = 2046869) B2046869
theorem B512659 : Blo 401768 512659 := bstep (se 1 (by rfl) ⟨384494, by rfl⟩ : syracuseStep 512659 = 768989) B768989
theorem B1725133 : Blo 401768 1725133 := bstep (se 3 (by rfl) ⟨323462, by rfl⟩ : syracuseStep 1725133 = 646925) B646925
theorem B1299181 : Blo 401768 1299181 := bstep (se 3 (by rfl) ⟨243596, by rfl⟩ : syracuseStep 1299181 = 487193) B487193
theorem B1168141 : Blo 401768 1168141 := bstep (se 3 (by rfl) ⟨219026, by rfl⟩ : syracuseStep 1168141 = 438053) B438053
theorem B906065 : Blo 401768 906065 := bstep (se 2 (by rfl) ⟨339774, by rfl⟩ : syracuseStep 906065 = 679549) B679549
theorem B906083 : Blo 401768 906083 := bstep (se 1 (by rfl) ⟨679562, by rfl⟩ : syracuseStep 906083 = 1359125) B1359125
theorem B1364849 : Blo 401768 1364849 := bstep (se 2 (by rfl) ⟨511818, by rfl⟩ : syracuseStep 1364849 = 1023637) B1023637
theorem B1725475 : Blo 401768 1725475 := bstep (se 1 (by rfl) ⟨1294106, by rfl⟩ : syracuseStep 1725475 = 2588213) B2588213
theorem B906353 : Blo 401768 906353 := bstep (se 2 (by rfl) ⟨339882, by rfl⟩ : syracuseStep 906353 = 679765) B679765
theorem B906371 : Blo 401768 906371 := bstep (se 1 (by rfl) ⟨679778, by rfl⟩ : syracuseStep 906371 = 1359557) B1359557
theorem B513155 : Blo 401768 513155 := bstep (se 1 (by rfl) ⟨384866, by rfl⟩ : syracuseStep 513155 = 769733) B769733
theorem B611491 : Blo 401768 611491 := bstep (se 1 (by rfl) ⟨458618, by rfl⟩ : syracuseStep 611491 = 917237) B917237
theorem B873635 : Blo 401768 873635 := bstep (se 1 (by rfl) ⟨655226, by rfl⟩ : syracuseStep 873635 = 1310453) B1310453
theorem B644465 : Blo 401768 644465 := bstep (se 2 (by rfl) ⟨241674, by rfl⟩ : syracuseStep 644465 = 483349) B483349
theorem B1365389 : Blo 401768 1365389 := bstep (se 3 (by rfl) ⟨256010, by rfl⟩ : syracuseStep 1365389 = 512021) B512021
theorem B906641 : Blo 401768 906641 := bstep (se 2 (by rfl) ⟨339990, by rfl⟩ : syracuseStep 906641 = 679981) B679981
theorem B906659 : Blo 401768 906659 := bstep (se 1 (by rfl) ⟨679994, by rfl⟩ : syracuseStep 906659 = 1359989) B1359989
theorem B1365443 : Blo 401768 1365443 := bstep (se 1 (by rfl) ⟨1024082, by rfl⟩ : syracuseStep 1365443 = 2048165) B2048165
theorem B644593 : Blo 401768 644593 := bstep (se 2 (by rfl) ⟨241722, by rfl⟩ : syracuseStep 644593 = 483445) B483445
theorem B2184803 : Blo 401768 2184803 := bstep (se 1 (by rfl) ⟨1638602, by rfl⟩ : syracuseStep 2184803 = 3277205) B3277205
theorem B906929 : Blo 401768 906929 := bstep (se 2 (by rfl) ⟨340098, by rfl⟩ : syracuseStep 906929 = 680197) B680197
theorem B906947 : Blo 401768 906947 := bstep (se 1 (by rfl) ⟨680210, by rfl⟩ : syracuseStep 906947 = 1360421) B1360421
theorem B1529549 : Blo 401768 1529549 := bstep (se 3 (by rfl) ⟨286790, by rfl⟩ : syracuseStep 1529549 = 573581) B573581
theorem B1365713 : Blo 401768 1365713 := bstep (se 2 (by rfl) ⟨512142, by rfl⟩ : syracuseStep 1365713 = 1024285) B1024285
theorem B907217 : Blo 401768 907217 := bstep (se 2 (by rfl) ⟨340206, by rfl⟩ : syracuseStep 907217 = 680413) B680413
theorem B907235 : Blo 401768 907235 := bstep (se 1 (by rfl) ⟨680426, by rfl⟩ : syracuseStep 907235 = 1360853) B1360853
theorem B546817 : Blo 401768 546817 := bstep (se 2 (by rfl) ⟨205056, by rfl⟩ : syracuseStep 546817 = 410113) B410113
theorem B546881 : Blo 401768 546881 := bstep (se 2 (by rfl) ⟨205080, by rfl⟩ : syracuseStep 546881 = 410161) B410161
theorem B678017 : Blo 401768 678017 := bstep (se 2 (by rfl) ⟨254256, by rfl⟩ : syracuseStep 678017 = 508513) B508513
theorem B1038467 : Blo 401768 1038467 := bstep (se 1 (by rfl) ⟨778850, by rfl⟩ : syracuseStep 1038467 = 1557701) B1557701
theorem B1366253 : Blo 401768 1366253 := bstep (se 3 (by rfl) ⟨256172, by rfl⟩ : syracuseStep 1366253 = 512345) B512345
theorem B907505 : Blo 401768 907505 := bstep (se 2 (by rfl) ⟨340314, by rfl⟩ : syracuseStep 907505 = 680629) B680629
theorem B678145 : Blo 401768 678145 := bstep (se 2 (by rfl) ⟨254304, by rfl⟩ : syracuseStep 678145 = 508609) B508609
theorem B907523 : Blo 401768 907523 := bstep (se 1 (by rfl) ⟨680642, by rfl⟩ : syracuseStep 907523 = 1361285) B1361285
theorem B678179 : Blo 401768 678179 := bstep (se 1 (by rfl) ⟨508634, by rfl⟩ : syracuseStep 678179 = 1017269) B1017269
theorem B1366307 : Blo 401768 1366307 := bstep (se 1 (by rfl) ⟨1024730, by rfl⟩ : syracuseStep 1366307 = 2049461) B2049461
theorem B678307 : Blo 401768 678307 := bstep (se 1 (by rfl) ⟨508730, by rfl⟩ : syracuseStep 678307 = 1017461) B1017461
theorem B645587 : Blo 401768 645587 := bstep (se 1 (by rfl) ⟨484190, by rfl⟩ : syracuseStep 645587 = 968381) B968381
theorem B1530353 : Blo 401768 1530353 := bstep (se 2 (by rfl) ⟨573882, by rfl⟩ : syracuseStep 1530353 = 1147765) B1147765
theorem B907793 : Blo 401768 907793 := bstep (se 2 (by rfl) ⟨340422, by rfl⟩ : syracuseStep 907793 = 680845) B680845
theorem B907811 : Blo 401768 907811 := bstep (se 1 (by rfl) ⟨680858, by rfl⟩ : syracuseStep 907811 = 1361717) B1361717
theorem B678449 : Blo 401768 678449 := bstep (se 2 (by rfl) ⟨254418, by rfl⟩ : syracuseStep 678449 = 508837) B508837
theorem B1366577 : Blo 401768 1366577 := bstep (se 2 (by rfl) ⟨512466, by rfl⟩ : syracuseStep 1366577 = 1024933) B1024933
theorem B678577 : Blo 401768 678577 := bstep (se 2 (by rfl) ⟨254466, by rfl⟩ : syracuseStep 678577 = 508933) B508933
theorem B776881 : Blo 401768 776881 := bstep (se 2 (by rfl) ⟨291330, by rfl⟩ : syracuseStep 776881 = 582661) B582661
theorem B2579141 : Blo 401768 2579141 := bstep (se 4 (by rfl) ⟨241794, by rfl⟩ : syracuseStep 2579141 = 483589) B483589
theorem B678611 : Blo 401768 678611 := bstep (se 1 (by rfl) ⟨508958, by rfl⟩ : syracuseStep 678611 = 1017917) B1017917
theorem B908081 : Blo 401768 908081 := bstep (se 2 (by rfl) ⟨340530, by rfl⟩ : syracuseStep 908081 = 681061) B681061
theorem B908099 : Blo 401768 908099 := bstep (se 1 (by rfl) ⟨681074, by rfl⟩ : syracuseStep 908099 = 1362149) B1362149
theorem B678739 : Blo 401768 678739 := bstep (se 1 (by rfl) ⟨509054, by rfl⟩ : syracuseStep 678739 = 1018109) B1018109
theorem B2186189 : Blo 401768 2186189 := bstep (se 3 (by rfl) ⟨409910, by rfl⟩ : syracuseStep 2186189 = 819821) B819821
theorem B678881 : Blo 401768 678881 := bstep (se 2 (by rfl) ⟨254580, by rfl⟩ : syracuseStep 678881 = 509161) B509161
theorem B1367117 : Blo 401768 1367117 := bstep (se 3 (by rfl) ⟨256334, by rfl⟩ : syracuseStep 1367117 = 512669) B512669
theorem B908369 : Blo 401768 908369 := bstep (se 2 (by rfl) ⟨340638, by rfl⟩ : syracuseStep 908369 = 681277) B681277
theorem B679009 : Blo 401768 679009 := bstep (se 2 (by rfl) ⟨254628, by rfl⟩ : syracuseStep 679009 = 509257) B509257
theorem B908387 : Blo 401768 908387 := bstep (se 1 (by rfl) ⟨681290, by rfl⟩ : syracuseStep 908387 = 1362581) B1362581
theorem B679043 : Blo 401768 679043 := bstep (se 1 (by rfl) ⟨509282, by rfl⟩ : syracuseStep 679043 = 1018565) B1018565
theorem B1367171 : Blo 401768 1367171 := bstep (se 1 (by rfl) ⟨1025378, by rfl⟩ : syracuseStep 1367171 = 2050757) B2050757
theorem B1531021 : Blo 401768 1531021 := bstep (se 3 (by rfl) ⟨287066, by rfl⟩ : syracuseStep 1531021 = 574133) B574133
theorem B679171 : Blo 401768 679171 := bstep (se 1 (by rfl) ⟨509378, by rfl⟩ : syracuseStep 679171 = 1018757) B1018757
theorem B908657 : Blo 401768 908657 := bstep (se 2 (by rfl) ⟨340746, by rfl⟩ : syracuseStep 908657 = 681493) B681493
theorem B908675 : Blo 401768 908675 := bstep (se 1 (by rfl) ⟨681506, by rfl⟩ : syracuseStep 908675 = 1363013) B1363013
theorem B679313 : Blo 401768 679313 := bstep (se 2 (by rfl) ⟨254742, by rfl⟩ : syracuseStep 679313 = 509485) B509485
theorem B1367441 : Blo 401768 1367441 := bstep (se 2 (by rfl) ⟨512790, by rfl⟩ : syracuseStep 1367441 = 1025581) B1025581
theorem B679441 : Blo 401768 679441 := bstep (se 2 (by rfl) ⟨254790, by rfl⟩ : syracuseStep 679441 = 509581) B509581
theorem B679475 : Blo 401768 679475 := bstep (se 1 (by rfl) ⟨509606, by rfl⟩ : syracuseStep 679475 = 1019213) B1019213
theorem B4611653 : Blo 401768 4611653 := bstep (se 4 (by rfl) ⟨432342, by rfl⟩ : syracuseStep 4611653 = 864685) B864685
theorem B515683 : Blo 401768 515683 := bstep (se 1 (by rfl) ⟨386762, by rfl⟩ : syracuseStep 515683 = 773525) B773525
theorem B908945 : Blo 401768 908945 := bstep (se 2 (by rfl) ⟨340854, by rfl⟩ : syracuseStep 908945 = 681709) B681709
theorem B1990307 : Blo 401768 1990307 := bstep (se 1 (by rfl) ⟨1492730, by rfl⟩ : syracuseStep 1990307 = 2985461) B2985461
theorem B908963 : Blo 401768 908963 := bstep (se 1 (by rfl) ⟨681722, by rfl⟩ : syracuseStep 908963 = 1363445) B1363445
theorem B679603 : Blo 401768 679603 := bstep (se 1 (by rfl) ⟨509702, by rfl⟩ : syracuseStep 679603 = 1019405) B1019405
theorem B974531 : Blo 401768 974531 := bstep (se 1 (by rfl) ⟨730898, by rfl⟩ : syracuseStep 974531 = 1461797) B1461797
theorem B679745 : Blo 401768 679745 := bstep (se 2 (by rfl) ⟨254904, by rfl⟩ : syracuseStep 679745 = 509809) B509809
theorem B647041 : Blo 401768 647041 := bstep (se 2 (by rfl) ⟨242640, by rfl⟩ : syracuseStep 647041 = 485281) B485281
theorem B1531811 : Blo 401768 1531811 := bstep (se 1 (by rfl) ⟨1148858, by rfl⟩ : syracuseStep 1531811 = 2297717) B2297717
theorem B1367981 : Blo 401768 1367981 := bstep (se 3 (by rfl) ⟨256496, by rfl⟩ : syracuseStep 1367981 = 512993) B512993
theorem B909233 : Blo 401768 909233 := bstep (se 2 (by rfl) ⟨340962, by rfl⟩ : syracuseStep 909233 = 681925) B681925
theorem B679873 : Blo 401768 679873 := bstep (se 2 (by rfl) ⟨254952, by rfl⟩ : syracuseStep 679873 = 509905) B509905
theorem B909251 : Blo 401768 909251 := bstep (se 1 (by rfl) ⟨681938, by rfl⟩ : syracuseStep 909251 = 1363877) B1363877
theorem B679907 : Blo 401768 679907 := bstep (se 1 (by rfl) ⟨509930, by rfl⟩ : syracuseStep 679907 = 1019861) B1019861
theorem B1368035 : Blo 401768 1368035 := bstep (se 1 (by rfl) ⟨1026026, by rfl⟩ : syracuseStep 1368035 = 2052053) B2052053
theorem B680035 : Blo 401768 680035 := bstep (se 1 (by rfl) ⟨510026, by rfl⟩ : syracuseStep 680035 = 1020053) B1020053
theorem B909521 : Blo 401768 909521 := bstep (se 2 (by rfl) ⟨341070, by rfl⟩ : syracuseStep 909521 = 682141) B682141
theorem B909539 : Blo 401768 909539 := bstep (se 1 (by rfl) ⟨682154, by rfl⟩ : syracuseStep 909539 = 1364309) B1364309
theorem B680177 : Blo 401768 680177 := bstep (se 2 (by rfl) ⟨255066, by rfl⟩ : syracuseStep 680177 = 510133) B510133
theorem B1368305 : Blo 401768 1368305 := bstep (se 2 (by rfl) ⟨513114, by rfl⟩ : syracuseStep 1368305 = 1026229) B1026229
theorem B680305 : Blo 401768 680305 := bstep (se 2 (by rfl) ⟨255114, by rfl⟩ : syracuseStep 680305 = 510229) B510229
theorem B680339 : Blo 401768 680339 := bstep (se 1 (by rfl) ⟨510254, by rfl⟩ : syracuseStep 680339 = 1020509) B1020509
theorem B909809 : Blo 401768 909809 := bstep (se 2 (by rfl) ⟨341178, by rfl⟩ : syracuseStep 909809 = 682357) B682357
theorem B909827 : Blo 401768 909827 := bstep (se 1 (by rfl) ⟨682370, by rfl⟩ : syracuseStep 909827 = 1364741) B1364741
theorem B680467 : Blo 401768 680467 := bstep (se 1 (by rfl) ⟨510350, by rfl⟩ : syracuseStep 680467 = 1020701) B1020701
theorem B1532465 : Blo 401768 1532465 := bstep (se 2 (by rfl) ⟨574674, by rfl⟩ : syracuseStep 1532465 = 1149349) B1149349
theorem B778819 : Blo 401768 778819 := bstep (se 1 (by rfl) ⟨584114, by rfl⟩ : syracuseStep 778819 = 1168229) B1168229
theorem B2187917 : Blo 401768 2187917 := bstep (se 3 (by rfl) ⟨410234, by rfl⟩ : syracuseStep 2187917 = 820469) B820469
theorem B680609 : Blo 401768 680609 := bstep (se 2 (by rfl) ⟨255228, by rfl⟩ : syracuseStep 680609 = 510457) B510457
theorem B1401517 : Blo 401768 1401517 := bstep (se 3 (by rfl) ⟨262784, by rfl⟩ : syracuseStep 1401517 = 525569) B525569
theorem B484051 : Blo 401768 484051 := bstep (se 1 (by rfl) ⟨363038, by rfl⟩ : syracuseStep 484051 = 726077) B726077
theorem B1368845 : Blo 401768 1368845 := bstep (se 3 (by rfl) ⟨256658, by rfl⟩ : syracuseStep 1368845 = 513317) B513317
theorem B910097 : Blo 401768 910097 := bstep (se 2 (by rfl) ⟨341286, by rfl⟩ : syracuseStep 910097 = 682573) B682573
theorem B680737 : Blo 401768 680737 := bstep (se 2 (by rfl) ⟨255276, by rfl⟩ : syracuseStep 680737 = 510553) B510553
theorem B910115 : Blo 401768 910115 := bstep (se 1 (by rfl) ⟨682586, by rfl⟩ : syracuseStep 910115 = 1365173) B1365173
theorem B680771 : Blo 401768 680771 := bstep (se 1 (by rfl) ⟨510578, by rfl⟩ : syracuseStep 680771 = 1021157) B1021157
theorem B1368899 : Blo 401768 1368899 := bstep (se 1 (by rfl) ⟨1026674, by rfl⟩ : syracuseStep 1368899 = 2053349) B2053349
theorem B1631075 : Blo 401768 1631075 := bstep (se 1 (by rfl) ⟨1223306, by rfl⟩ : syracuseStep 1631075 = 2446613) B2446613
theorem B4350833 : Blo 401768 4350833 := bstep (se 2 (by rfl) ⟨1631562, by rfl⟩ : syracuseStep 4350833 = 3263125) B3263125
theorem B680899 : Blo 401768 680899 := bstep (se 1 (by rfl) ⟨510674, by rfl⟩ : syracuseStep 680899 = 1021349) B1021349
theorem B1729507 : Blo 401768 1729507 := bstep (se 1 (by rfl) ⟨1297130, by rfl⟩ : syracuseStep 1729507 = 2594261) B2594261
theorem B910385 : Blo 401768 910385 := bstep (se 2 (by rfl) ⟨341394, by rfl⟩ : syracuseStep 910385 = 682789) B682789
theorem B910403 : Blo 401768 910403 := bstep (se 1 (by rfl) ⟨682802, by rfl⟩ : syracuseStep 910403 = 1365605) B1365605
theorem B681041 : Blo 401768 681041 := bstep (se 2 (by rfl) ⟨255390, by rfl⟩ : syracuseStep 681041 = 510781) B510781
theorem B1369169 : Blo 401768 1369169 := bstep (se 2 (by rfl) ⟨513438, by rfl⟩ : syracuseStep 1369169 = 1026877) B1026877
theorem B681169 : Blo 401768 681169 := bstep (se 2 (by rfl) ⟨255438, by rfl⟩ : syracuseStep 681169 = 510877) B510877
theorem B484579 : Blo 401768 484579 := bstep (se 1 (by rfl) ⟨363434, by rfl⟩ : syracuseStep 484579 = 726869) B726869
theorem B681203 : Blo 401768 681203 := bstep (se 1 (by rfl) ⟨510902, by rfl⟩ : syracuseStep 681203 = 1021805) B1021805
theorem B910673 : Blo 401768 910673 := bstep (se 2 (by rfl) ⟨341502, by rfl⟩ : syracuseStep 910673 = 683005) B683005
theorem B910691 : Blo 401768 910691 := bstep (se 1 (by rfl) ⟨683018, by rfl⟩ : syracuseStep 910691 = 1366037) B1366037
theorem B681331 : Blo 401768 681331 := bstep (se 1 (by rfl) ⟨510998, by rfl⟩ : syracuseStep 681331 = 1021997) B1021997
theorem B648643 : Blo 401768 648643 := bstep (se 1 (by rfl) ⟨486482, by rfl⟩ : syracuseStep 648643 = 972965) B972965
theorem B452083 : Blo 401768 452083 := bstep (se 1 (by rfl) ⟨339062, by rfl⟩ : syracuseStep 452083 = 678125) B678125
theorem B681473 : Blo 401768 681473 := bstep (se 2 (by rfl) ⟨255552, by rfl⟩ : syracuseStep 681473 = 511105) B511105
theorem B1631821 : Blo 401768 1631821 := bstep (se 3 (by rfl) ⟨305966, by rfl⟩ : syracuseStep 1631821 = 611933) B611933
theorem B910961 : Blo 401768 910961 := bstep (se 2 (by rfl) ⟨341610, by rfl⟩ : syracuseStep 910961 = 683221) B683221
theorem B681601 : Blo 401768 681601 := bstep (se 2 (by rfl) ⟨255600, by rfl⟩ : syracuseStep 681601 = 511201) B511201
theorem B452227 : Blo 401768 452227 := bstep (se 1 (by rfl) ⟨339170, by rfl⟩ : syracuseStep 452227 = 678341) B678341
theorem B910979 : Blo 401768 910979 := bstep (se 1 (by rfl) ⟨683234, by rfl⟩ : syracuseStep 910979 = 1366469) B1366469
theorem B681635 : Blo 401768 681635 := bstep (se 1 (by rfl) ⟨511226, by rfl⟩ : syracuseStep 681635 = 1022453) B1022453
theorem B648899 : Blo 401768 648899 := bstep (se 1 (by rfl) ⟨486674, by rfl⟩ : syracuseStep 648899 = 973349) B973349
theorem B3106531 : Blo 401768 3106531 := bstep (se 1 (by rfl) ⟨2329898, by rfl⟩ : syracuseStep 3106531 = 4659797) B4659797
theorem B452371 : Blo 401768 452371 := bstep (se 1 (by rfl) ⟨339278, by rfl⟩ : syracuseStep 452371 = 678557) B678557
theorem B2320163 : Blo 401768 2320163 := bstep (se 1 (by rfl) ⟨1740122, by rfl⟩ : syracuseStep 2320163 = 3480245) B3480245
theorem B681763 : Blo 401768 681763 := bstep (se 1 (by rfl) ⟨511322, by rfl⟩ : syracuseStep 681763 = 1022645) B1022645
theorem B616307 : Blo 401768 616307 := bstep (se 1 (by rfl) ⟨462230, by rfl⟩ : syracuseStep 616307 = 924461) B924461
theorem B649091 : Blo 401768 649091 := bstep (se 1 (by rfl) ⟨486818, by rfl⟩ : syracuseStep 649091 = 973637) B973637
theorem B911249 : Blo 401768 911249 := bstep (se 2 (by rfl) ⟨341718, by rfl⟩ : syracuseStep 911249 = 683437) B683437
theorem B452515 : Blo 401768 452515 := bstep (se 1 (by rfl) ⟨339386, by rfl⟩ : syracuseStep 452515 = 678773) B678773
theorem B911267 : Blo 401768 911267 := bstep (se 1 (by rfl) ⟨683450, by rfl⟩ : syracuseStep 911267 = 1366901) B1366901
theorem B681905 : Blo 401768 681905 := bstep (se 2 (by rfl) ⟨255714, by rfl⟩ : syracuseStep 681905 = 511429) B511429
theorem B1533923 : Blo 401768 1533923 := bstep (se 1 (by rfl) ⟨1150442, by rfl⟩ : syracuseStep 1533923 = 2300885) B2300885
theorem B1533937 : Blo 401768 1533937 := bstep (se 2 (by rfl) ⟨575226, by rfl⟩ : syracuseStep 1533937 = 1150453) B1150453
theorem B682033 : Blo 401768 682033 := bstep (se 2 (by rfl) ⟨255762, by rfl⟩ : syracuseStep 682033 = 511525) B511525
theorem B452659 : Blo 401768 452659 := bstep (se 1 (by rfl) ⟨339494, by rfl⟩ : syracuseStep 452659 = 678989) B678989
theorem B682067 : Blo 401768 682067 := bstep (se 1 (by rfl) ⟨511550, by rfl⟩ : syracuseStep 682067 = 1023101) B1023101
theorem B911537 : Blo 401768 911537 := bstep (se 2 (by rfl) ⟨341826, by rfl⟩ : syracuseStep 911537 = 683653) B683653
theorem B1730737 : Blo 401768 1730737 := bstep (se 2 (by rfl) ⟨649026, by rfl⟩ : syracuseStep 1730737 = 1298053) B1298053
theorem B452803 : Blo 401768 452803 := bstep (se 1 (by rfl) ⟨339602, by rfl⟩ : syracuseStep 452803 = 679205) B679205
theorem B911555 : Blo 401768 911555 := bstep (se 1 (by rfl) ⟨683666, by rfl⟩ : syracuseStep 911555 = 1367333) B1367333
theorem B6187205 : Blo 401768 6187205 := bstep (se 4 (by rfl) ⟨580050, by rfl⟩ : syracuseStep 6187205 = 1160101) B1160101
theorem B682195 : Blo 401768 682195 := bstep (se 1 (by rfl) ⟨511646, by rfl⟩ : syracuseStep 682195 = 1023293) B1023293
theorem B452947 : Blo 401768 452947 := bstep (se 1 (by rfl) ⟨339710, by rfl⟩ : syracuseStep 452947 = 679421) B679421
theorem B682337 : Blo 401768 682337 := bstep (se 2 (by rfl) ⟨255876, by rfl⟩ : syracuseStep 682337 = 511753) B511753
theorem B911825 : Blo 401768 911825 := bstep (se 2 (by rfl) ⟨341934, by rfl⟩ : syracuseStep 911825 = 683869) B683869
theorem B682465 : Blo 401768 682465 := bstep (se 2 (by rfl) ⟨255924, by rfl⟩ : syracuseStep 682465 = 511849) B511849
theorem B453091 : Blo 401768 453091 := bstep (se 1 (by rfl) ⟨339818, by rfl⟩ : syracuseStep 453091 = 679637) B679637
theorem B911843 : Blo 401768 911843 := bstep (se 1 (by rfl) ⟨683882, by rfl⟩ : syracuseStep 911843 = 1367765) B1367765
theorem B682499 : Blo 401768 682499 := bstep (se 1 (by rfl) ⟨511874, by rfl⟩ : syracuseStep 682499 = 1023749) B1023749
theorem B2583089 : Blo 401768 2583089 := bstep (se 2 (by rfl) ⟨968658, by rfl⟩ : syracuseStep 2583089 = 1937317) B1937317
theorem B453235 : Blo 401768 453235 := bstep (se 1 (by rfl) ⟨339926, by rfl⟩ : syracuseStep 453235 = 679853) B679853
theorem B682627 : Blo 401768 682627 := bstep (se 1 (by rfl) ⟨511970, by rfl⟩ : syracuseStep 682627 = 1023941) B1023941
theorem B649873 : Blo 401768 649873 := bstep (se 2 (by rfl) ⟨243702, by rfl⟩ : syracuseStep 649873 = 487405) B487405
theorem B912113 : Blo 401768 912113 := bstep (se 2 (by rfl) ⟨342042, by rfl⟩ : syracuseStep 912113 = 684085) B684085
theorem B453379 : Blo 401768 453379 := bstep (se 1 (by rfl) ⟨340034, by rfl⟩ : syracuseStep 453379 = 680069) B680069
theorem B912131 : Blo 401768 912131 := bstep (se 1 (by rfl) ⟨684098, by rfl⟩ : syracuseStep 912131 = 1368197) B1368197
theorem B682769 : Blo 401768 682769 := bstep (se 2 (by rfl) ⟨256038, by rfl⟩ : syracuseStep 682769 = 512077) B512077
theorem B682897 : Blo 401768 682897 := bstep (se 2 (by rfl) ⟨256086, by rfl⟩ : syracuseStep 682897 = 512173) B512173
theorem B453523 : Blo 401768 453523 := bstep (se 1 (by rfl) ⟨340142, by rfl⟩ : syracuseStep 453523 = 680285) B680285
theorem B682931 : Blo 401768 682931 := bstep (se 1 (by rfl) ⟨512198, by rfl⟩ : syracuseStep 682931 = 1024397) B1024397
theorem B912401 : Blo 401768 912401 := bstep (se 2 (by rfl) ⟨342150, by rfl⟩ : syracuseStep 912401 = 684301) B684301
theorem B453667 : Blo 401768 453667 := bstep (se 1 (by rfl) ⟨340250, by rfl⟩ : syracuseStep 453667 = 680501) B680501
theorem B912419 : Blo 401768 912419 := bstep (se 1 (by rfl) ⟨684314, by rfl⟩ : syracuseStep 912419 = 1368629) B1368629
theorem B683059 : Blo 401768 683059 := bstep (se 1 (by rfl) ⟨512294, by rfl⟩ : syracuseStep 683059 = 1024589) B1024589
theorem B453811 : Blo 401768 453811 := bstep (se 1 (by rfl) ⟨340358, by rfl⟩ : syracuseStep 453811 = 680717) B680717
theorem B683201 : Blo 401768 683201 := bstep (se 2 (by rfl) ⟨256200, by rfl⟩ : syracuseStep 683201 = 512401) B512401
theorem B912689 : Blo 401768 912689 := bstep (se 2 (by rfl) ⟨342258, by rfl⟩ : syracuseStep 912689 = 684517) B684517
theorem B683329 : Blo 401768 683329 := bstep (se 2 (by rfl) ⟨256248, by rfl⟩ : syracuseStep 683329 = 512497) B512497
theorem B453955 : Blo 401768 453955 := bstep (se 1 (by rfl) ⟨340466, by rfl⟩ : syracuseStep 453955 = 680933) B680933
theorem B912707 : Blo 401768 912707 := bstep (se 1 (by rfl) ⟨684530, by rfl⟩ : syracuseStep 912707 = 1369061) B1369061
theorem B683363 : Blo 401768 683363 := bstep (se 1 (by rfl) ⟨512522, by rfl⟩ : syracuseStep 683363 = 1025045) B1025045
theorem B1535395 : Blo 401768 1535395 := bstep (se 1 (by rfl) ⟨1151546, by rfl⟩ : syracuseStep 1535395 = 2303093) B2303093
theorem B454099 : Blo 401768 454099 := bstep (se 1 (by rfl) ⟨340574, by rfl⟩ : syracuseStep 454099 = 681149) B681149
theorem B683491 : Blo 401768 683491 := bstep (se 1 (by rfl) ⟨512618, by rfl⟩ : syracuseStep 683491 = 1025237) B1025237
theorem B2289221 : Blo 401768 2289221 := bstep (se 4 (by rfl) ⟨214614, by rfl⟩ : syracuseStep 2289221 = 429229) B429229
theorem B912977 : Blo 401768 912977 := bstep (se 2 (by rfl) ⟨342366, by rfl⟩ : syracuseStep 912977 = 684733) B684733
theorem B454243 : Blo 401768 454243 := bstep (se 1 (by rfl) ⟨340682, by rfl⟩ : syracuseStep 454243 = 681365) B681365
theorem B683633 : Blo 401768 683633 := bstep (se 2 (by rfl) ⟨256362, by rfl⟩ : syracuseStep 683633 = 512725) B512725
theorem B4419269 : Blo 401768 4419269 := bstep (se 4 (by rfl) ⟨414306, by rfl⟩ : syracuseStep 4419269 = 828613) B828613
theorem B683761 : Blo 401768 683761 := bstep (se 2 (by rfl) ⟨256410, by rfl⟩ : syracuseStep 683761 = 512821) B512821
theorem B454387 : Blo 401768 454387 := bstep (se 1 (by rfl) ⟨340790, by rfl⟩ : syracuseStep 454387 = 681581) B681581
theorem B683795 : Blo 401768 683795 := bstep (se 1 (by rfl) ⟨512846, by rfl⟩ : syracuseStep 683795 = 1025693) B1025693
theorem B454531 : Blo 401768 454531 := bstep (se 1 (by rfl) ⟨340898, by rfl⟩ : syracuseStep 454531 = 681797) B681797
theorem B683923 : Blo 401768 683923 := bstep (se 1 (by rfl) ⟨512942, by rfl⟩ : syracuseStep 683923 = 1025885) B1025885
theorem B5238755 : Blo 401768 5238755 := bstep (se 1 (by rfl) ⟨3929066, by rfl⟩ : syracuseStep 5238755 = 7858133) B7858133
theorem B1470449 : Blo 401768 1470449 := bstep (se 2 (by rfl) ⟨551418, by rfl⟩ : syracuseStep 1470449 = 1102837) B1102837
theorem B454675 : Blo 401768 454675 := bstep (se 1 (by rfl) ⟨341006, by rfl⟩ : syracuseStep 454675 = 682013) B682013
theorem B684065 : Blo 401768 684065 := bstep (se 2 (by rfl) ⟨256524, by rfl⟩ : syracuseStep 684065 = 513049) B513049
theorem B684193 : Blo 401768 684193 := bstep (se 2 (by rfl) ⟨256572, by rfl⟩ : syracuseStep 684193 = 513145) B513145
theorem B454819 : Blo 401768 454819 := bstep (se 1 (by rfl) ⟨341114, by rfl⟩ : syracuseStep 454819 = 682229) B682229
theorem B684227 : Blo 401768 684227 := bstep (se 1 (by rfl) ⟨513170, by rfl⟩ : syracuseStep 684227 = 1026341) B1026341
theorem B520435 : Blo 401768 520435 := bstep (se 1 (by rfl) ⟨390326, by rfl⟩ : syracuseStep 520435 = 780653) B780653
theorem B454963 : Blo 401768 454963 := bstep (se 1 (by rfl) ⟨341222, by rfl⟩ : syracuseStep 454963 = 682445) B682445
theorem B684355 : Blo 401768 684355 := bstep (se 1 (by rfl) ⟨513266, by rfl⟩ : syracuseStep 684355 = 1026533) B1026533
theorem B455107 : Blo 401768 455107 := bstep (se 1 (by rfl) ⟨341330, by rfl⟩ : syracuseStep 455107 = 682661) B682661
theorem B684497 : Blo 401768 684497 := bstep (se 2 (by rfl) ⟨256686, by rfl⟩ : syracuseStep 684497 = 513373) B513373
theorem B684625 : Blo 401768 684625 := bstep (se 2 (by rfl) ⟨256734, by rfl⟩ : syracuseStep 684625 = 513469) B513469
theorem B455251 : Blo 401768 455251 := bstep (se 1 (by rfl) ⟨341438, by rfl⟩ : syracuseStep 455251 = 682877) B682877
theorem B684659 : Blo 401768 684659 := bstep (se 1 (by rfl) ⟨513494, by rfl⟩ : syracuseStep 684659 = 1026989) B1026989
theorem B1405649 : Blo 401768 1405649 := bstep (se 2 (by rfl) ⟨527118, by rfl⟩ : syracuseStep 1405649 = 1054237) B1054237
theorem B455395 : Blo 401768 455395 := bstep (se 1 (by rfl) ⟨341546, by rfl⟩ : syracuseStep 455395 = 683093) B683093
theorem B455539 : Blo 401768 455539 := bstep (se 1 (by rfl) ⟨341654, by rfl⟩ : syracuseStep 455539 = 683309) B683309
theorem B455683 : Blo 401768 455683 := bstep (se 1 (by rfl) ⟨341762, by rfl⟩ : syracuseStep 455683 = 683525) B683525
theorem B455827 : Blo 401768 455827 := bstep (se 1 (by rfl) ⟨341870, by rfl⟩ : syracuseStep 455827 = 683741) B683741
theorem B4617485 : Blo 401768 4617485 := bstep (se 3 (by rfl) ⟨865778, by rfl⟩ : syracuseStep 4617485 = 1731557) B1731557
theorem B455971 : Blo 401768 455971 := bstep (se 1 (by rfl) ⟨341978, by rfl⟩ : syracuseStep 455971 = 683957) B683957
theorem B2913677 : Blo 401768 2913677 := bstep (se 3 (by rfl) ⟨546314, by rfl⟩ : syracuseStep 2913677 = 1092629) B1092629
theorem B456115 : Blo 401768 456115 := bstep (se 1 (by rfl) ⟨342086, by rfl⟩ : syracuseStep 456115 = 684173) B684173
theorem B816689 : Blo 401768 816689 := bstep (se 2 (by rfl) ⟨306258, by rfl⟩ : syracuseStep 816689 = 612517) B612517
theorem B456259 : Blo 401768 456259 := bstep (se 1 (by rfl) ⟨342194, by rfl⟩ : syracuseStep 456259 = 684389) B684389
theorem B4126277 : Blo 401768 4126277 := bstep (se 4 (by rfl) ⟨386838, by rfl⟩ : syracuseStep 4126277 = 773677) B773677
theorem B1537613 : Blo 401768 1537613 := bstep (se 3 (by rfl) ⟨288302, by rfl⟩ : syracuseStep 1537613 = 576605) B576605
theorem B2455181 : Blo 401768 2455181 := bstep (se 3 (by rfl) ⟨460346, by rfl⟩ : syracuseStep 2455181 = 920693) B920693
theorem B4159117 : Blo 401768 4159117 := bstep (se 3 (by rfl) ⟨779834, by rfl⟩ : syracuseStep 4159117 = 1559669) B1559669
theorem B980689 : Blo 401768 980689 := bstep (se 2 (by rfl) ⟨367758, by rfl⟩ : syracuseStep 980689 = 735517) B735517
theorem B456403 : Blo 401768 456403 := bstep (se 1 (by rfl) ⟨342302, by rfl⟩ : syracuseStep 456403 = 684605) B684605
theorem B1144621 : Blo 401768 1144621 := bstep (se 3 (by rfl) ⟨214616, by rfl⟩ : syracuseStep 1144621 = 429233) B429233
theorem B1832867 : Blo 401768 1832867 := bstep (se 1 (by rfl) ⟨1374650, by rfl⟩ : syracuseStep 1832867 = 2749301) B2749301
theorem B1832881 : Blo 401768 1832881 := bstep (se 2 (by rfl) ⟨687330, by rfl⟩ : syracuseStep 1832881 = 1374661) B1374661
theorem B1144849 : Blo 401768 1144849 := bstep (se 2 (by rfl) ⟨429318, by rfl⟩ : syracuseStep 1144849 = 858637) B858637
theorem B1145009 : Blo 401768 1145009 := bstep (se 2 (by rfl) ⟨429378, by rfl⟩ : syracuseStep 1145009 = 858757) B858757
theorem B1145123 : Blo 401768 1145123 := bstep (se 1 (by rfl) ⟨858842, by rfl⟩ : syracuseStep 1145123 = 1717685) B1717685
theorem B2587085 : Blo 401768 2587085 := bstep (se 3 (by rfl) ⟨485078, by rfl⟩ : syracuseStep 2587085 = 970157) B970157
theorem B1374769 : Blo 401768 1374769 := bstep (se 2 (by rfl) ⟨515538, by rfl⟩ : syracuseStep 1374769 = 1031077) B1031077
theorem B3439331 : Blo 401768 3439331 := bstep (se 1 (by rfl) ⟨2579498, by rfl⟩ : syracuseStep 3439331 = 5158997) B5158997
theorem B2751565 : Blo 401768 2751565 := bstep (se 3 (by rfl) ⟨515918, by rfl⟩ : syracuseStep 2751565 = 1031837) B1031837
theorem B11041933 : Blo 401768 11041933 := bstep (se 3 (by rfl) ⟨2070362, by rfl⟩ : syracuseStep 11041933 = 4140725) B4140725
theorem B1146125 : Blo 401768 1146125 := bstep (se 3 (by rfl) ⟨214898, by rfl⟩ : syracuseStep 1146125 = 429797) B429797
theorem B2293069 : Blo 401768 2293069 := bstep (se 3 (by rfl) ⟨429950, by rfl⟩ : syracuseStep 2293069 = 859901) B859901
theorem B1146307 : Blo 401768 1146307 := bstep (se 1 (by rfl) ⟨859730, by rfl⟩ : syracuseStep 1146307 = 1719461) B1719461
theorem B589393 : Blo 401768 589393 := bstep (se 2 (by rfl) ⟨221022, by rfl⟩ : syracuseStep 589393 = 442045) B442045
theorem B1146467 : Blo 401768 1146467 := bstep (se 1 (by rfl) ⟨859850, by rfl⟩ : syracuseStep 1146467 = 1719701) B1719701
theorem B687905 : Blo 401768 687905 := bstep (se 2 (by rfl) ⟨257964, by rfl⟩ : syracuseStep 687905 = 515929) B515929
theorem B3276875 : Blo 401768 3276875 := bstep (se 1 (by rfl) ⟨2457656, by rfl⟩ : syracuseStep 3276875 = 4915313) B4915313
theorem B3080267 : Blo 401768 3080267 := bstep (se 1 (by rfl) ⟨2310200, by rfl⟩ : syracuseStep 3080267 = 4620401) B4620401
theorem B1540241 : Blo 401768 1540241 := bstep (se 2 (by rfl) ⟨577590, by rfl⟩ : syracuseStep 1540241 = 1155181) B1155181
theorem B819479 : Blo 401768 819479 := bstep (se 1 (by rfl) ⟨614609, by rfl⟩ : syracuseStep 819479 = 1229219) B1229219
theorem B2753041 : Blo 401768 2753041 := bstep (se 2 (by rfl) ⟨1032390, by rfl⟩ : syracuseStep 2753041 = 2064781) B2064781
theorem B2458291 : Blo 401768 2458291 := bstep (se 1 (by rfl) ⟨1843718, by rfl⟩ : syracuseStep 2458291 = 3687437) B3687437
theorem B5833397 : Blo 401768 5833397 := bstep (se 5 (by rfl) ⟨273440, by rfl⟩ : syracuseStep 5833397 = 546881) B546881
theorem B3277529 : Blo 401768 3277529 := bstep (se 2 (by rfl) ⟨1229073, by rfl⟩ : syracuseStep 3277529 = 2458147) B2458147
theorem B820055 : Blo 401768 820055 := bstep (se 1 (by rfl) ⟨615041, by rfl⟩ : syracuseStep 820055 = 1230083) B1230083
theorem B1868689 : Blo 401768 1868689 := bstep (se 2 (by rfl) ⟨700758, by rfl⟩ : syracuseStep 1868689 = 1401517) B1401517
theorem B2294801 : Blo 401768 2294801 := bstep (se 2 (by rfl) ⟨860550, by rfl⟩ : syracuseStep 2294801 = 1721101) B1721101
theorem B1148107 : Blo 401768 1148107 := bstep (se 1 (by rfl) ⟨861080, by rfl⟩ : syracuseStep 1148107 = 1722161) B1722161
theorem B1148381 : Blo 401768 1148381 := bstep (se 3 (by rfl) ⟨215321, by rfl⟩ : syracuseStep 1148381 = 430643) B430643
theorem B787979 : Blo 401768 787979 := bstep (se 1 (by rfl) ⟨590984, by rfl⟩ : syracuseStep 787979 = 1181969) B1181969
theorem B4621859 : Blo 401768 4621859 := bstep (se 1 (by rfl) ⟨3466394, by rfl⟩ : syracuseStep 4621859 = 6932789) B6932789
theorem B4130509 : Blo 401768 4130509 := bstep (se 3 (by rfl) ⟨774470, by rfl⟩ : syracuseStep 4130509 = 1548941) B1548941
theorem B1017623 : Blo 401768 1017623 := bstep (se 1 (by rfl) ⟨763217, by rfl⟩ : syracuseStep 1017623 = 1526435) B1526435
theorem B1640371 : Blo 401768 1640371 := bstep (se 1 (by rfl) ⟨1230278, by rfl⟩ : syracuseStep 1640371 = 2460557) B2460557
theorem B460939 : Blo 401768 460939 := bstep (se 1 (by rfl) ⟨345704, by rfl⟩ : syracuseStep 460939 = 691409) B691409
theorem B2034071 : Blo 401768 2034071 := bstep (se 1 (by rfl) ⟨1525553, by rfl⟩ : syracuseStep 2034071 = 3051107) B3051107
theorem B1018291 : Blo 401768 1018291 := bstep (se 1 (by rfl) ⟨763718, by rfl⟩ : syracuseStep 1018291 = 1527437) B1527437
theorem B1018433 : Blo 401768 1018433 := bstep (se 2 (by rfl) ⟨381912, by rfl⟩ : syracuseStep 1018433 = 763825) B763825
theorem B5900951 : Blo 401768 5900951 := bstep (se 1 (by rfl) ⟨4425713, by rfl⟩ : syracuseStep 5900951 = 8851427) B8851427
theorem B1051969 : Blo 401768 1051969 := bstep (se 2 (by rfl) ⟨394488, by rfl⟩ : syracuseStep 1051969 = 788977) B788977
theorem B1642007 : Blo 401768 1642007 := bstep (se 1 (by rfl) ⟨1231505, by rfl⟩ : syracuseStep 1642007 = 2463011) B2463011
theorem B724555 : Blo 401768 724555 := bstep (se 1 (by rfl) ⟨543416, by rfl⟩ : syracuseStep 724555 = 1086833) B1086833
theorem B429643 : Blo 401768 429643 := bstep (se 1 (by rfl) ⟨322232, by rfl⟩ : syracuseStep 429643 = 644465) B644465
theorem B1642187 : Blo 401768 1642187 := bstep (se 1 (by rfl) ⟨1231640, by rfl⟩ : syracuseStep 1642187 = 2463281) B2463281
theorem B1150681 : Blo 401768 1150681 := bstep (se 2 (by rfl) ⟨431505, by rfl⟩ : syracuseStep 1150681 = 863011) B863011
theorem B1019699 : Blo 401768 1019699 := bstep (se 1 (by rfl) ⟨764774, by rfl⟩ : syracuseStep 1019699 = 1529549) B1529549
theorem B692311 : Blo 401768 692311 := bstep (se 1 (by rfl) ⟨519233, by rfl⟩ : syracuseStep 692311 = 1038467) B1038467
theorem B430391 : Blo 401768 430391 := bstep (se 1 (by rfl) ⟨322793, by rfl⟩ : syracuseStep 430391 = 645587) B645587
theorem B1151297 : Blo 401768 1151297 := bstep (se 2 (by rfl) ⟨431736, by rfl⟩ : syracuseStep 1151297 = 863473) B863473
theorem B1020235 : Blo 401768 1020235 := bstep (se 1 (by rfl) ⟨765176, by rfl⟩ : syracuseStep 1020235 = 1530353) B1530353
theorem B725363 : Blo 401768 725363 := bstep (se 1 (by rfl) ⟨544022, by rfl⟩ : syracuseStep 725363 = 1088045) B1088045
theorem B1020377 : Blo 401768 1020377 := bstep (se 2 (by rfl) ⟨382641, by rfl⟩ : syracuseStep 1020377 = 765283) B765283
theorem B725657 : Blo 401768 725657 := bstep (se 2 (by rfl) ⟨272121, by rfl⟩ : syracuseStep 725657 = 544243) B544243
theorem B6099697 : Blo 401768 6099697 := bstep (se 2 (by rfl) ⟨2287386, by rfl⟩ : syracuseStep 6099697 = 4574773) B4574773
theorem B922571 : Blo 401768 922571 := bstep (se 1 (by rfl) ⟨691928, by rfl⟩ : syracuseStep 922571 = 1383857) B1383857
theorem B1643485 : Blo 401768 1643485 := bstep (se 3 (by rfl) ⟨308153, by rfl⟩ : syracuseStep 1643485 = 616307) B616307
theorem B3413123 : Blo 401768 3413123 := bstep (se 1 (by rfl) ⟨2559842, by rfl⟩ : syracuseStep 3413123 = 5119685) B5119685
theorem B1021207 : Blo 401768 1021207 := bstep (se 1 (by rfl) ⟨765905, by rfl⟩ : syracuseStep 1021207 = 1531811) B1531811
theorem B726401 : Blo 401768 726401 := bstep (se 2 (by rfl) ⟨272400, by rfl⟩ : syracuseStep 726401 = 544801) B544801
theorem B1381835 : Blo 401768 1381835 := bstep (se 1 (by rfl) ⟨1036376, by rfl⟩ : syracuseStep 1381835 = 2072753) B2072753
theorem B1840657 : Blo 401768 1840657 := bstep (se 2 (by rfl) ⟨690246, by rfl⟩ : syracuseStep 1840657 = 1380493) B1380493
theorem B1021643 : Blo 401768 1021643 := bstep (se 1 (by rfl) ⟨766232, by rfl⟩ : syracuseStep 1021643 = 1532465) B1532465
theorem B2037635 : Blo 401768 2037635 := bstep (se 1 (by rfl) ⟨1528226, by rfl⟩ : syracuseStep 2037635 = 3056453) B3056453
theorem B1022017 : Blo 401768 1022017 := bstep (se 2 (by rfl) ⟨383256, by rfl⟩ : syracuseStep 1022017 = 766513) B766513
theorem B2300177 : Blo 401768 2300177 := bstep (se 2 (by rfl) ⟨862566, by rfl⟩ : syracuseStep 2300177 = 1725133) B1725133
theorem B1153369 : Blo 401768 1153369 := bstep (se 2 (by rfl) ⟨432513, by rfl⟩ : syracuseStep 1153369 = 865027) B865027
theorem B432599 : Blo 401768 432599 := bstep (se 1 (by rfl) ⟨324449, by rfl⟩ : syracuseStep 432599 = 648899) B648899
theorem B1546775 : Blo 401768 1546775 := bstep (se 1 (by rfl) ⟨1160081, by rfl⟩ : syracuseStep 1546775 = 2320163) B2320163
theorem B7740035 : Blo 401768 7740035 := bstep (se 1 (by rfl) ⟨5805026, by rfl⟩ : syracuseStep 7740035 = 11610053) B11610053
theorem B1022615 : Blo 401768 1022615 := bstep (se 1 (by rfl) ⟨766961, by rfl⟩ : syracuseStep 1022615 = 1533923) B1533923
theorem B2300633 : Blo 401768 2300633 := bstep (se 2 (by rfl) ⟨862737, by rfl⟩ : syracuseStep 2300633 = 1725475) B1725475
theorem B1153757 : Blo 401768 1153757 := bstep (se 3 (by rfl) ⟨216329, by rfl⟩ : syracuseStep 1153757 = 432659) B432659
theorem B859457 : Blo 401768 859457 := bstep (se 2 (by rfl) ⟨322296, by rfl⟩ : syracuseStep 859457 = 644593) B644593
theorem B1023425 : Blo 401768 1023425 := bstep (se 2 (by rfl) ⟨383784, by rfl⟩ : syracuseStep 1023425 = 767569) B767569
theorem B1449731 : Blo 401768 1449731 := bstep (se 1 (by rfl) ⟨1087298, by rfl⟩ : syracuseStep 1449731 = 2174597) B2174597
theorem B3678169 : Blo 401768 3678169 := bstep (se 2 (by rfl) ⟨1379313, by rfl⟩ : syracuseStep 3678169 = 2758627) B2758627
theorem B1023961 : Blo 401768 1023961 := bstep (se 2 (by rfl) ⟨383985, by rfl⟩ : syracuseStep 1023961 = 767971) B767971
theorem B729089 : Blo 401768 729089 := bstep (se 2 (by rfl) ⟨273408, by rfl⟩ : syracuseStep 729089 = 546817) B546817
theorem B860311 : Blo 401768 860311 := bstep (se 1 (by rfl) ⟨645233, by rfl⟩ : syracuseStep 860311 = 1290467) B1290467
theorem B401771 : Blo 401768 401771 := bstep (se 1 (by rfl) ⟨301328, by rfl⟩ : syracuseStep 401771 = 602657) B602657
theorem B4366709 : Blo 401768 4366709 := bstep (se 5 (by rfl) ⟨204689, by rfl⟩ : syracuseStep 4366709 = 409379) B409379
theorem B401783 : Blo 401768 401783 := bstep (se 1 (by rfl) ⟨301337, by rfl⟩ : syracuseStep 401783 = 602675) B602675
theorem B401803 : Blo 401768 401803 := bstep (se 1 (by rfl) ⟨301352, by rfl⟩ : syracuseStep 401803 = 602705) B602705
theorem B401815 : Blo 401768 401815 := bstep (se 1 (by rfl) ⟨301361, by rfl⟩ : syracuseStep 401815 = 602723) B602723
theorem B1450391 : Blo 401768 1450391 := bstep (se 1 (by rfl) ⟨1087793, by rfl⟩ : syracuseStep 1450391 = 2175587) B2175587
theorem B401835 : Blo 401768 401835 := bstep (se 1 (by rfl) ⟨301376, by rfl⟩ : syracuseStep 401835 = 602753) B602753
theorem B401847 : Blo 401768 401847 := bstep (se 1 (by rfl) ⟨301385, by rfl⟩ : syracuseStep 401847 = 602771) B602771
theorem B401867 : Blo 401768 401867 := bstep (se 1 (by rfl) ⟨301400, by rfl⟩ : syracuseStep 401867 = 602801) B602801
theorem B401879 : Blo 401768 401879 := bstep (se 1 (by rfl) ⟨301409, by rfl⟩ : syracuseStep 401879 = 602819) B602819
theorem B401899 : Blo 401768 401899 := bstep (se 1 (by rfl) ⟨301424, by rfl⟩ : syracuseStep 401899 = 602849) B602849
theorem B401911 : Blo 401768 401911 := bstep (se 1 (by rfl) ⟨301433, by rfl⟩ : syracuseStep 401911 = 602867) B602867
theorem B401931 : Blo 401768 401931 := bstep (se 1 (by rfl) ⟨301448, by rfl⟩ : syracuseStep 401931 = 602897) B602897
theorem B401943 : Blo 401768 401943 := bstep (se 1 (by rfl) ⟨301457, by rfl⟩ : syracuseStep 401943 = 602915) B602915
theorem B401963 : Blo 401768 401963 := bstep (se 1 (by rfl) ⟨301472, by rfl⟩ : syracuseStep 401963 = 602945) B602945
theorem B795187 : Blo 401768 795187 := bstep (se 1 (by rfl) ⟨596390, by rfl⟩ : syracuseStep 795187 = 1192781) B1192781
theorem B401975 : Blo 401768 401975 := bstep (se 1 (by rfl) ⟨301481, by rfl⟩ : syracuseStep 401975 = 602963) B602963
theorem B401995 : Blo 401768 401995 := bstep (se 1 (by rfl) ⟨301496, by rfl⟩ : syracuseStep 401995 = 602993) B602993
theorem B402007 : Blo 401768 402007 := bstep (se 1 (by rfl) ⟨301505, by rfl⟩ : syracuseStep 402007 = 603011) B603011
theorem B402027 : Blo 401768 402027 := bstep (se 1 (by rfl) ⟨301520, by rfl⟩ : syracuseStep 402027 = 603041) B603041
theorem B402039 : Blo 401768 402039 := bstep (se 1 (by rfl) ⟨301529, by rfl⟩ : syracuseStep 402039 = 603059) B603059
theorem B402059 : Blo 401768 402059 := bstep (se 1 (by rfl) ⟨301544, by rfl⟩ : syracuseStep 402059 = 603089) B603089
theorem B402071 : Blo 401768 402071 := bstep (se 1 (by rfl) ⟨301553, by rfl⟩ : syracuseStep 402071 = 603107) B603107
theorem B402091 : Blo 401768 402091 := bstep (se 1 (by rfl) ⟨301568, by rfl⟩ : syracuseStep 402091 = 603137) B603137
theorem B402103 : Blo 401768 402103 := bstep (se 1 (by rfl) ⟨301577, by rfl⟩ : syracuseStep 402103 = 603155) B603155
theorem B402123 : Blo 401768 402123 := bstep (se 1 (by rfl) ⟨301592, by rfl⟩ : syracuseStep 402123 = 603185) B603185
theorem B402135 : Blo 401768 402135 := bstep (se 1 (by rfl) ⟨301601, by rfl⟩ : syracuseStep 402135 = 603203) B603203
theorem B402155 : Blo 401768 402155 := bstep (se 1 (by rfl) ⟨301616, by rfl⟩ : syracuseStep 402155 = 603233) B603233
theorem B402167 : Blo 401768 402167 := bstep (se 1 (by rfl) ⟨301625, by rfl⟩ : syracuseStep 402167 = 603251) B603251
theorem B402187 : Blo 401768 402187 := bstep (se 1 (by rfl) ⟨301640, by rfl⟩ : syracuseStep 402187 = 603281) B603281
theorem B402199 : Blo 401768 402199 := bstep (se 1 (by rfl) ⟨301649, by rfl⟩ : syracuseStep 402199 = 603299) B603299
theorem B402219 : Blo 401768 402219 := bstep (se 1 (by rfl) ⟨301664, by rfl⟩ : syracuseStep 402219 = 603329) B603329
theorem B402231 : Blo 401768 402231 := bstep (se 1 (by rfl) ⟨301673, by rfl⟩ : syracuseStep 402231 = 603347) B603347
theorem B402251 : Blo 401768 402251 := bstep (se 1 (by rfl) ⟨301688, by rfl⟩ : syracuseStep 402251 = 603377) B603377
theorem B402263 : Blo 401768 402263 := bstep (se 1 (by rfl) ⟨301697, by rfl⟩ : syracuseStep 402263 = 603395) B603395
theorem B402283 : Blo 401768 402283 := bstep (se 1 (by rfl) ⟨301712, by rfl⟩ : syracuseStep 402283 = 603425) B603425
theorem B402295 : Blo 401768 402295 := bstep (se 1 (by rfl) ⟨301721, by rfl⟩ : syracuseStep 402295 = 603443) B603443
theorem B402315 : Blo 401768 402315 := bstep (se 1 (by rfl) ⟨301736, by rfl⟩ : syracuseStep 402315 = 603473) B603473
theorem B402327 : Blo 401768 402327 := bstep (se 1 (by rfl) ⟨301745, by rfl⟩ : syracuseStep 402327 = 603491) B603491
theorem B402347 : Blo 401768 402347 := bstep (se 1 (by rfl) ⟨301760, by rfl⟩ : syracuseStep 402347 = 603521) B603521
theorem B1942451 : Blo 401768 1942451 := bstep (se 1 (by rfl) ⟨1456838, by rfl⟩ : syracuseStep 1942451 = 2913677) B2913677
theorem B402359 : Blo 401768 402359 := bstep (se 1 (by rfl) ⟨301769, by rfl⟩ : syracuseStep 402359 = 603539) B603539
theorem B402379 : Blo 401768 402379 := bstep (se 1 (by rfl) ⟨301784, by rfl⟩ : syracuseStep 402379 = 603569) B603569
theorem B402391 : Blo 401768 402391 := bstep (se 1 (by rfl) ⟨301793, by rfl⟩ : syracuseStep 402391 = 603587) B603587
theorem B402411 : Blo 401768 402411 := bstep (se 1 (by rfl) ⟨301808, by rfl⟩ : syracuseStep 402411 = 603617) B603617
theorem B402423 : Blo 401768 402423 := bstep (se 1 (by rfl) ⟨301817, by rfl⟩ : syracuseStep 402423 = 603635) B603635
theorem B402443 : Blo 401768 402443 := bstep (se 1 (by rfl) ⟨301832, by rfl⟩ : syracuseStep 402443 = 603665) B603665
theorem B402455 : Blo 401768 402455 := bstep (se 1 (by rfl) ⟨301841, by rfl⟩ : syracuseStep 402455 = 603683) B603683
theorem B402475 : Blo 401768 402475 := bstep (se 1 (by rfl) ⟨301856, by rfl⟩ : syracuseStep 402475 = 603713) B603713
theorem B1025075 : Blo 401768 1025075 := bstep (se 1 (by rfl) ⟨768806, by rfl⟩ : syracuseStep 1025075 = 1537613) B1537613
theorem B402487 : Blo 401768 402487 := bstep (se 1 (by rfl) ⟨301865, by rfl⟩ : syracuseStep 402487 = 603731) B603731
theorem B402507 : Blo 401768 402507 := bstep (se 1 (by rfl) ⟨301880, by rfl⟩ : syracuseStep 402507 = 603761) B603761
theorem B402519 : Blo 401768 402519 := bstep (se 1 (by rfl) ⟨301889, by rfl⟩ : syracuseStep 402519 = 603779) B603779
theorem B402539 : Blo 401768 402539 := bstep (se 1 (by rfl) ⟨301904, by rfl⟩ : syracuseStep 402539 = 603809) B603809
theorem B402551 : Blo 401768 402551 := bstep (se 1 (by rfl) ⟨301913, by rfl⟩ : syracuseStep 402551 = 603827) B603827
theorem B402571 : Blo 401768 402571 := bstep (se 1 (by rfl) ⟨301928, by rfl⟩ : syracuseStep 402571 = 603857) B603857
theorem B402583 : Blo 401768 402583 := bstep (se 1 (by rfl) ⟨301937, by rfl⟩ : syracuseStep 402583 = 603875) B603875
theorem B402603 : Blo 401768 402603 := bstep (se 1 (by rfl) ⟨301952, by rfl⟩ : syracuseStep 402603 = 603905) B603905
theorem B402615 : Blo 401768 402615 := bstep (se 1 (by rfl) ⟨301961, by rfl⟩ : syracuseStep 402615 = 603923) B603923
theorem B402635 : Blo 401768 402635 := bstep (se 1 (by rfl) ⟨301976, by rfl⟩ : syracuseStep 402635 = 603953) B603953
theorem B402647 : Blo 401768 402647 := bstep (se 1 (by rfl) ⟨301985, by rfl⟩ : syracuseStep 402647 = 603971) B603971
theorem B402667 : Blo 401768 402667 := bstep (se 1 (by rfl) ⟨302000, by rfl⟩ : syracuseStep 402667 = 604001) B604001
theorem B402679 : Blo 401768 402679 := bstep (se 1 (by rfl) ⟨302009, by rfl⟩ : syracuseStep 402679 = 604019) B604019
theorem B402699 : Blo 401768 402699 := bstep (se 1 (by rfl) ⟨302024, by rfl⟩ : syracuseStep 402699 = 604049) B604049
theorem B1221911 : Blo 401768 1221911 := bstep (se 1 (by rfl) ⟨916433, by rfl⟩ : syracuseStep 1221911 = 1832867) B1832867
theorem B402711 : Blo 401768 402711 := bstep (se 1 (by rfl) ⟨302033, by rfl⟩ : syracuseStep 402711 = 604067) B604067
theorem B402731 : Blo 401768 402731 := bstep (se 1 (by rfl) ⟨302048, by rfl⟩ : syracuseStep 402731 = 604097) B604097
theorem B861491 : Blo 401768 861491 := bstep (se 1 (by rfl) ⟨646118, by rfl⟩ : syracuseStep 861491 = 1292237) B1292237
theorem B402743 : Blo 401768 402743 := bstep (se 1 (by rfl) ⟨302057, by rfl⟩ : syracuseStep 402743 = 604115) B604115
theorem B402763 : Blo 401768 402763 := bstep (se 1 (by rfl) ⟨302072, by rfl⟩ : syracuseStep 402763 = 604145) B604145
theorem B402775 : Blo 401768 402775 := bstep (se 1 (by rfl) ⟨302081, by rfl⟩ : syracuseStep 402775 = 604163) B604163
theorem B1025369 : Blo 401768 1025369 := bstep (se 2 (by rfl) ⟨384513, by rfl⟩ : syracuseStep 1025369 = 769027) B769027
theorem B402795 : Blo 401768 402795 := bstep (se 1 (by rfl) ⟨302096, by rfl⟩ : syracuseStep 402795 = 604193) B604193
theorem B402807 : Blo 401768 402807 := bstep (se 1 (by rfl) ⟨302105, by rfl⟩ : syracuseStep 402807 = 604211) B604211
theorem B402827 : Blo 401768 402827 := bstep (se 1 (by rfl) ⟨302120, by rfl⟩ : syracuseStep 402827 = 604241) B604241
theorem B402839 : Blo 401768 402839 := bstep (se 1 (by rfl) ⟨302129, by rfl⟩ : syracuseStep 402839 = 604259) B604259
theorem B402859 : Blo 401768 402859 := bstep (se 1 (by rfl) ⟨302144, by rfl⟩ : syracuseStep 402859 = 604289) B604289
theorem B402871 : Blo 401768 402871 := bstep (se 1 (by rfl) ⟨302153, by rfl⟩ : syracuseStep 402871 = 604307) B604307
theorem B763339 : Blo 401768 763339 := bstep (se 1 (by rfl) ⟨572504, by rfl⟩ : syracuseStep 763339 = 1145009) B1145009
theorem B402891 : Blo 401768 402891 := bstep (se 1 (by rfl) ⟨302168, by rfl⟩ : syracuseStep 402891 = 604337) B604337
theorem B402903 : Blo 401768 402903 := bstep (se 1 (by rfl) ⟨302177, by rfl⟩ : syracuseStep 402903 = 604355) B604355
theorem B402923 : Blo 401768 402923 := bstep (se 1 (by rfl) ⟨302192, by rfl⟩ : syracuseStep 402923 = 604385) B604385
theorem B402935 : Blo 401768 402935 := bstep (se 1 (by rfl) ⟨302201, by rfl⟩ : syracuseStep 402935 = 604403) B604403
theorem B402955 : Blo 401768 402955 := bstep (se 1 (by rfl) ⟨302216, by rfl⟩ : syracuseStep 402955 = 604433) B604433
theorem B2041361 : Blo 401768 2041361 := bstep (se 2 (by rfl) ⟨765510, by rfl⟩ : syracuseStep 2041361 = 1531021) B1531021
theorem B14722577 : Blo 401768 14722577 := bstep (se 2 (by rfl) ⟨5520966, by rfl⟩ : syracuseStep 14722577 = 11041933) B11041933
theorem B763415 : Blo 401768 763415 := bstep (se 1 (by rfl) ⟨572561, by rfl⟩ : syracuseStep 763415 = 1145123) B1145123
theorem B402967 : Blo 401768 402967 := bstep (se 1 (by rfl) ⟨302225, by rfl⟩ : syracuseStep 402967 = 604451) B604451
theorem B402987 : Blo 401768 402987 := bstep (se 1 (by rfl) ⟨302240, by rfl⟩ : syracuseStep 402987 = 604481) B604481
theorem B1386035 : Blo 401768 1386035 := bstep (se 1 (by rfl) ⟨1039526, by rfl⟩ : syracuseStep 1386035 = 2079053) B2079053
theorem B402999 : Blo 401768 402999 := bstep (se 1 (by rfl) ⟨302249, by rfl⟩ : syracuseStep 402999 = 604499) B604499
theorem B403019 : Blo 401768 403019 := bstep (se 1 (by rfl) ⟨302264, by rfl⟩ : syracuseStep 403019 = 604529) B604529
theorem B403031 : Blo 401768 403031 := bstep (se 1 (by rfl) ⟨302273, by rfl⟩ : syracuseStep 403031 = 604547) B604547
theorem B403051 : Blo 401768 403051 := bstep (se 1 (by rfl) ⟨302288, by rfl⟩ : syracuseStep 403051 = 604577) B604577
theorem B403063 : Blo 401768 403063 := bstep (se 1 (by rfl) ⟨302297, by rfl⟩ : syracuseStep 403063 = 604595) B604595
theorem B403083 : Blo 401768 403083 := bstep (se 1 (by rfl) ⟨302312, by rfl⟩ : syracuseStep 403083 = 604625) B604625
theorem B403095 : Blo 401768 403095 := bstep (se 1 (by rfl) ⟨302321, by rfl⟩ : syracuseStep 403095 = 604643) B604643
theorem B403115 : Blo 401768 403115 := bstep (se 1 (by rfl) ⟨302336, by rfl⟩ : syracuseStep 403115 = 604673) B604673
theorem B2041523 : Blo 401768 2041523 := bstep (se 1 (by rfl) ⟨1531142, by rfl⟩ : syracuseStep 2041523 = 3062285) B3062285
theorem B403127 : Blo 401768 403127 := bstep (se 1 (by rfl) ⟨302345, by rfl⟩ : syracuseStep 403127 = 604691) B604691
theorem B403147 : Blo 401768 403147 := bstep (se 1 (by rfl) ⟨302360, by rfl⟩ : syracuseStep 403147 = 604721) B604721
theorem B403159 : Blo 401768 403159 := bstep (se 1 (by rfl) ⟨302369, by rfl⟩ : syracuseStep 403159 = 604739) B604739
theorem B403179 : Blo 401768 403179 := bstep (se 1 (by rfl) ⟨302384, by rfl⟩ : syracuseStep 403179 = 604769) B604769
theorem B403191 : Blo 401768 403191 := bstep (se 1 (by rfl) ⟨302393, by rfl⟩ : syracuseStep 403191 = 604787) B604787
theorem B403211 : Blo 401768 403211 := bstep (se 1 (by rfl) ⟨302408, by rfl⟩ : syracuseStep 403211 = 604817) B604817
theorem B3057425 : Blo 401768 3057425 := bstep (se 2 (by rfl) ⟨1146534, by rfl⟩ : syracuseStep 3057425 = 2293069) B2293069
theorem B403223 : Blo 401768 403223 := bstep (se 1 (by rfl) ⟨302417, by rfl⟩ : syracuseStep 403223 = 604835) B604835
theorem B403243 : Blo 401768 403243 := bstep (se 1 (by rfl) ⟨302432, by rfl⟩ : syracuseStep 403243 = 604865) B604865
theorem B403255 : Blo 401768 403255 := bstep (se 1 (by rfl) ⟨302441, by rfl⟩ : syracuseStep 403255 = 604883) B604883
theorem B403275 : Blo 401768 403275 := bstep (se 1 (by rfl) ⟨302456, by rfl⟩ : syracuseStep 403275 = 604913) B604913
theorem B403287 : Blo 401768 403287 := bstep (se 1 (by rfl) ⟨302465, by rfl⟩ : syracuseStep 403287 = 604931) B604931
theorem B1943389 : Blo 401768 1943389 := bstep (se 3 (by rfl) ⟨364385, by rfl⟩ : syracuseStep 1943389 = 728771) B728771
theorem B2598749 : Blo 401768 2598749 := bstep (se 3 (by rfl) ⟨487265, by rfl⟩ : syracuseStep 2598749 = 974531) B974531
theorem B403307 : Blo 401768 403307 := bstep (se 1 (by rfl) ⟨302480, by rfl⟩ : syracuseStep 403307 = 604961) B604961
theorem B403319 : Blo 401768 403319 := bstep (se 1 (by rfl) ⟨302489, by rfl⟩ : syracuseStep 403319 = 604979) B604979
theorem B403339 : Blo 401768 403339 := bstep (se 1 (by rfl) ⟨302504, by rfl⟩ : syracuseStep 403339 = 605009) B605009
theorem B403351 : Blo 401768 403351 := bstep (se 1 (by rfl) ⟨302513, by rfl⟩ : syracuseStep 403351 = 605027) B605027
theorem B403371 : Blo 401768 403371 := bstep (se 1 (by rfl) ⟨302528, by rfl⟩ : syracuseStep 403371 = 605057) B605057
theorem B403383 : Blo 401768 403383 := bstep (se 1 (by rfl) ⟨302537, by rfl⟩ : syracuseStep 403383 = 605075) B605075
theorem B403403 : Blo 401768 403403 := bstep (se 1 (by rfl) ⟨302552, by rfl⟩ : syracuseStep 403403 = 605105) B605105
theorem B403415 : Blo 401768 403415 := bstep (se 1 (by rfl) ⟨302561, by rfl⟩ : syracuseStep 403415 = 605123) B605123
theorem B403435 : Blo 401768 403435 := bstep (se 1 (by rfl) ⟨302576, by rfl⟩ : syracuseStep 403435 = 605153) B605153
theorem B403447 : Blo 401768 403447 := bstep (se 1 (by rfl) ⟨302585, by rfl⟩ : syracuseStep 403447 = 605171) B605171
theorem B403467 : Blo 401768 403467 := bstep (se 1 (by rfl) ⟨302600, by rfl⟩ : syracuseStep 403467 = 605201) B605201
theorem B403479 : Blo 401768 403479 := bstep (se 1 (by rfl) ⟨302609, by rfl⟩ : syracuseStep 403479 = 605219) B605219
theorem B403499 : Blo 401768 403499 := bstep (se 1 (by rfl) ⟨302624, by rfl⟩ : syracuseStep 403499 = 605249) B605249
theorem B403511 : Blo 401768 403511 := bstep (se 1 (by rfl) ⟨302633, by rfl⟩ : syracuseStep 403511 = 605267) B605267
theorem B403531 : Blo 401768 403531 := bstep (se 1 (by rfl) ⟨302648, by rfl⟩ : syracuseStep 403531 = 605297) B605297
theorem B403543 : Blo 401768 403543 := bstep (se 1 (by rfl) ⟨302657, by rfl⟩ : syracuseStep 403543 = 605315) B605315
theorem B403563 : Blo 401768 403563 := bstep (se 1 (by rfl) ⟨302672, by rfl⟩ : syracuseStep 403563 = 605345) B605345
theorem B403575 : Blo 401768 403575 := bstep (se 1 (by rfl) ⟨302681, by rfl⟩ : syracuseStep 403575 = 605363) B605363
theorem B403595 : Blo 401768 403595 := bstep (se 1 (by rfl) ⟨302696, by rfl⟩ : syracuseStep 403595 = 605393) B605393
theorem B403607 : Blo 401768 403607 := bstep (se 1 (by rfl) ⟨302705, by rfl⟩ : syracuseStep 403607 = 605411) B605411
theorem B403627 : Blo 401768 403627 := bstep (se 1 (by rfl) ⟨302720, by rfl⟩ : syracuseStep 403627 = 605441) B605441
theorem B764083 : Blo 401768 764083 := bstep (se 1 (by rfl) ⟨573062, by rfl⟩ : syracuseStep 764083 = 1146125) B1146125
theorem B403639 : Blo 401768 403639 := bstep (se 1 (by rfl) ⟨302729, by rfl⟩ : syracuseStep 403639 = 605459) B605459
theorem B403659 : Blo 401768 403659 := bstep (se 1 (by rfl) ⟨302744, by rfl⟩ : syracuseStep 403659 = 605489) B605489
theorem B403671 : Blo 401768 403671 := bstep (se 1 (by rfl) ⟨302753, by rfl⟩ : syracuseStep 403671 = 605507) B605507
theorem B2074841 : Blo 401768 2074841 := bstep (se 2 (by rfl) ⟨778065, by rfl⟩ : syracuseStep 2074841 = 1556131) B1556131
theorem B403691 : Blo 401768 403691 := bstep (se 1 (by rfl) ⟨302768, by rfl⟩ : syracuseStep 403691 = 605537) B605537
theorem B403703 : Blo 401768 403703 := bstep (se 1 (by rfl) ⟨302777, by rfl⟩ : syracuseStep 403703 = 605555) B605555
theorem B403723 : Blo 401768 403723 := bstep (se 1 (by rfl) ⟨302792, by rfl⟩ : syracuseStep 403723 = 605585) B605585
theorem B403735 : Blo 401768 403735 := bstep (se 1 (by rfl) ⟨302801, by rfl⟩ : syracuseStep 403735 = 605603) B605603
theorem B403755 : Blo 401768 403755 := bstep (se 1 (by rfl) ⟨302816, by rfl⟩ : syracuseStep 403755 = 605633) B605633
theorem B403767 : Blo 401768 403767 := bstep (se 1 (by rfl) ⟨302825, by rfl⟩ : syracuseStep 403767 = 605651) B605651
theorem B403787 : Blo 401768 403787 := bstep (se 1 (by rfl) ⟨302840, by rfl⟩ : syracuseStep 403787 = 605681) B605681
theorem B403799 : Blo 401768 403799 := bstep (se 1 (by rfl) ⟨302849, by rfl⟩ : syracuseStep 403799 = 605699) B605699
theorem B403819 : Blo 401768 403819 := bstep (se 1 (by rfl) ⟨302864, by rfl⟩ : syracuseStep 403819 = 605729) B605729
theorem B403831 : Blo 401768 403831 := bstep (se 1 (by rfl) ⟨302873, by rfl⟩ : syracuseStep 403831 = 605747) B605747
theorem B403851 : Blo 401768 403851 := bstep (se 1 (by rfl) ⟨302888, by rfl⟩ : syracuseStep 403851 = 605777) B605777
theorem B764311 : Blo 401768 764311 := bstep (se 1 (by rfl) ⟨573233, by rfl⟩ : syracuseStep 764311 = 1146467) B1146467
theorem B403863 : Blo 401768 403863 := bstep (se 1 (by rfl) ⟨302897, by rfl⟩ : syracuseStep 403863 = 605795) B605795
theorem B403883 : Blo 401768 403883 := bstep (se 1 (by rfl) ⟨302912, by rfl⟩ : syracuseStep 403883 = 605825) B605825
theorem B403895 : Blo 401768 403895 := bstep (se 1 (by rfl) ⟨302921, by rfl⟩ : syracuseStep 403895 = 605843) B605843
theorem B403915 : Blo 401768 403915 := bstep (se 1 (by rfl) ⟨302936, by rfl⟩ : syracuseStep 403915 = 605873) B605873
theorem B403927 : Blo 401768 403927 := bstep (se 1 (by rfl) ⟨302945, by rfl⟩ : syracuseStep 403927 = 605891) B605891
theorem B403947 : Blo 401768 403947 := bstep (se 1 (by rfl) ⟨302960, by rfl⟩ : syracuseStep 403947 = 605921) B605921
theorem B403959 : Blo 401768 403959 := bstep (se 1 (by rfl) ⟨302969, by rfl⟩ : syracuseStep 403959 = 605939) B605939
theorem B764417 : Blo 401768 764417 := bstep (se 2 (by rfl) ⟨286656, by rfl⟩ : syracuseStep 764417 = 573313) B573313
theorem B862721 : Blo 401768 862721 := bstep (se 2 (by rfl) ⟨323520, by rfl⟩ : syracuseStep 862721 = 647041) B647041
theorem B403979 : Blo 401768 403979 := bstep (se 1 (by rfl) ⟨302984, by rfl⟩ : syracuseStep 403979 = 605969) B605969
theorem B403991 : Blo 401768 403991 := bstep (se 1 (by rfl) ⟨302993, by rfl⟩ : syracuseStep 403991 = 605987) B605987
theorem B404011 : Blo 401768 404011 := bstep (se 1 (by rfl) ⟨303008, by rfl⟩ : syracuseStep 404011 = 606017) B606017
theorem B404023 : Blo 401768 404023 := bstep (se 1 (by rfl) ⟨303017, by rfl⟩ : syracuseStep 404023 = 606035) B606035
theorem B404043 : Blo 401768 404043 := bstep (se 1 (by rfl) ⟨303032, by rfl⟩ : syracuseStep 404043 = 606065) B606065
theorem B404055 : Blo 401768 404055 := bstep (se 1 (by rfl) ⟨303041, by rfl⟩ : syracuseStep 404055 = 606083) B606083
theorem B404075 : Blo 401768 404075 := bstep (se 1 (by rfl) ⟨303056, by rfl⟩ : syracuseStep 404075 = 606113) B606113
theorem B404087 : Blo 401768 404087 := bstep (se 1 (by rfl) ⟨303065, by rfl⟩ : syracuseStep 404087 = 606131) B606131
theorem B2960003 : Blo 401768 2960003 := bstep (se 1 (by rfl) ⟨2220002, by rfl⟩ : syracuseStep 2960003 = 4440005) B4440005
theorem B404107 : Blo 401768 404107 := bstep (se 1 (by rfl) ⟨303080, by rfl⟩ : syracuseStep 404107 = 606161) B606161
theorem B404119 : Blo 401768 404119 := bstep (se 1 (by rfl) ⟨303089, by rfl⟩ : syracuseStep 404119 = 606179) B606179
theorem B764569 : Blo 401768 764569 := bstep (se 2 (by rfl) ⟨286713, by rfl⟩ : syracuseStep 764569 = 573427) B573427
theorem B404139 : Blo 401768 404139 := bstep (se 1 (by rfl) ⟨303104, by rfl⟩ : syracuseStep 404139 = 606209) B606209
theorem B404151 : Blo 401768 404151 := bstep (se 1 (by rfl) ⟨303113, by rfl⟩ : syracuseStep 404151 = 606227) B606227
theorem B404171 : Blo 401768 404171 := bstep (se 1 (by rfl) ⟨303128, by rfl⟩ : syracuseStep 404171 = 606257) B606257
theorem B404183 : Blo 401768 404183 := bstep (se 1 (by rfl) ⟨303137, by rfl⟩ : syracuseStep 404183 = 606275) B606275
theorem B404203 : Blo 401768 404203 := bstep (se 1 (by rfl) ⟨303152, by rfl⟩ : syracuseStep 404203 = 606305) B606305
theorem B404215 : Blo 401768 404215 := bstep (se 1 (by rfl) ⟨303161, by rfl⟩ : syracuseStep 404215 = 606323) B606323
theorem B404235 : Blo 401768 404235 := bstep (se 1 (by rfl) ⟨303176, by rfl⟩ : syracuseStep 404235 = 606353) B606353
theorem B404247 : Blo 401768 404247 := bstep (se 1 (by rfl) ⟨303185, by rfl⟩ : syracuseStep 404247 = 606371) B606371
theorem B404267 : Blo 401768 404267 := bstep (se 1 (by rfl) ⟨303200, by rfl⟩ : syracuseStep 404267 = 606401) B606401
theorem B404279 : Blo 401768 404279 := bstep (se 1 (by rfl) ⟨303209, by rfl⟩ : syracuseStep 404279 = 606419) B606419
theorem B404299 : Blo 401768 404299 := bstep (se 1 (by rfl) ⟨303224, by rfl⟩ : syracuseStep 404299 = 606449) B606449
theorem B404311 : Blo 401768 404311 := bstep (se 1 (by rfl) ⟨303233, by rfl⟩ : syracuseStep 404311 = 606467) B606467
theorem B404331 : Blo 401768 404331 := bstep (se 1 (by rfl) ⟨303248, by rfl⟩ : syracuseStep 404331 = 606497) B606497
theorem B404343 : Blo 401768 404343 := bstep (se 1 (by rfl) ⟨303257, by rfl⟩ : syracuseStep 404343 = 606515) B606515
theorem B1846147 : Blo 401768 1846147 := bstep (se 1 (by rfl) ⟨1384610, by rfl⟩ : syracuseStep 1846147 = 2769221) B2769221
theorem B404363 : Blo 401768 404363 := bstep (se 1 (by rfl) ⟨303272, by rfl⟩ : syracuseStep 404363 = 606545) B606545
theorem B404375 : Blo 401768 404375 := bstep (se 1 (by rfl) ⟨303281, by rfl⟩ : syracuseStep 404375 = 606563) B606563
theorem B404395 : Blo 401768 404395 := bstep (se 1 (by rfl) ⟨303296, by rfl⟩ : syracuseStep 404395 = 606593) B606593
theorem B404407 : Blo 401768 404407 := bstep (se 1 (by rfl) ⟨303305, by rfl⟩ : syracuseStep 404407 = 606611) B606611
theorem B404427 : Blo 401768 404427 := bstep (se 1 (by rfl) ⟨303320, by rfl⟩ : syracuseStep 404427 = 606641) B606641
theorem B1027019 : Blo 401768 1027019 := bstep (se 1 (by rfl) ⟨770264, by rfl⟩ : syracuseStep 1027019 = 1540529) B1540529
theorem B404439 : Blo 401768 404439 := bstep (se 1 (by rfl) ⟨303329, by rfl⟩ : syracuseStep 404439 = 606659) B606659
theorem B404459 : Blo 401768 404459 := bstep (se 1 (by rfl) ⟨303344, by rfl⟩ : syracuseStep 404459 = 606689) B606689
theorem B404471 : Blo 401768 404471 := bstep (se 1 (by rfl) ⟨303353, by rfl⟩ : syracuseStep 404471 = 606707) B606707
theorem B404491 : Blo 401768 404491 := bstep (se 1 (by rfl) ⟨303368, by rfl⟩ : syracuseStep 404491 = 606737) B606737
theorem B404503 : Blo 401768 404503 := bstep (se 1 (by rfl) ⟨303377, by rfl⟩ : syracuseStep 404503 = 606755) B606755
theorem B404523 : Blo 401768 404523 := bstep (se 1 (by rfl) ⟨303392, by rfl⟩ : syracuseStep 404523 = 606785) B606785
theorem B404535 : Blo 401768 404535 := bstep (se 1 (by rfl) ⟨303401, by rfl⟩ : syracuseStep 404535 = 606803) B606803
theorem B404555 : Blo 401768 404555 := bstep (se 1 (by rfl) ⟨303416, by rfl⟩ : syracuseStep 404555 = 606833) B606833
theorem B404567 : Blo 401768 404567 := bstep (se 1 (by rfl) ⟨303425, by rfl⟩ : syracuseStep 404567 = 606851) B606851
theorem B404587 : Blo 401768 404587 := bstep (se 1 (by rfl) ⟨303440, by rfl⟩ : syracuseStep 404587 = 606881) B606881
theorem B404599 : Blo 401768 404599 := bstep (se 1 (by rfl) ⟨303449, by rfl⟩ : syracuseStep 404599 = 606899) B606899
theorem B404619 : Blo 401768 404619 := bstep (se 1 (by rfl) ⟨303464, by rfl⟩ : syracuseStep 404619 = 606929) B606929
theorem B404631 : Blo 401768 404631 := bstep (se 1 (by rfl) ⟨303473, by rfl⟩ : syracuseStep 404631 = 606947) B606947
theorem B404651 : Blo 401768 404651 := bstep (se 1 (by rfl) ⟨303488, by rfl⟩ : syracuseStep 404651 = 606977) B606977
theorem B404663 : Blo 401768 404663 := bstep (se 1 (by rfl) ⟨303497, by rfl⟩ : syracuseStep 404663 = 606995) B606995
theorem B404683 : Blo 401768 404683 := bstep (se 1 (by rfl) ⟨303512, by rfl⟩ : syracuseStep 404683 = 607025) B607025
theorem B404695 : Blo 401768 404695 := bstep (se 1 (by rfl) ⟨303521, by rfl⟩ : syracuseStep 404695 = 607043) B607043
theorem B404715 : Blo 401768 404715 := bstep (se 1 (by rfl) ⟨303536, by rfl⟩ : syracuseStep 404715 = 607073) B607073
theorem B404727 : Blo 401768 404727 := bstep (se 1 (by rfl) ⟨303545, by rfl⟩ : syracuseStep 404727 = 607091) B607091
theorem B6991109 : Blo 401768 6991109 := bstep (se 4 (by rfl) ⟨655416, by rfl⟩ : syracuseStep 6991109 = 1310833) B1310833
theorem B404747 : Blo 401768 404747 := bstep (se 1 (by rfl) ⟨303560, by rfl⟩ : syracuseStep 404747 = 607121) B607121
theorem B404759 : Blo 401768 404759 := bstep (se 1 (by rfl) ⟨303569, by rfl⟩ : syracuseStep 404759 = 607139) B607139
theorem B404779 : Blo 401768 404779 := bstep (se 1 (by rfl) ⟨303584, by rfl⟩ : syracuseStep 404779 = 607169) B607169
theorem B404791 : Blo 401768 404791 := bstep (se 1 (by rfl) ⟨303593, by rfl⟩ : syracuseStep 404791 = 607187) B607187
theorem B404811 : Blo 401768 404811 := bstep (se 1 (by rfl) ⟨303608, by rfl⟩ : syracuseStep 404811 = 607217) B607217
theorem B404823 : Blo 401768 404823 := bstep (se 1 (by rfl) ⟨303617, by rfl⟩ : syracuseStep 404823 = 607235) B607235
theorem B404843 : Blo 401768 404843 := bstep (se 1 (by rfl) ⟨303632, by rfl⟩ : syracuseStep 404843 = 607265) B607265
theorem B404855 : Blo 401768 404855 := bstep (se 1 (by rfl) ⟨303641, by rfl⟩ : syracuseStep 404855 = 607283) B607283
theorem B404875 : Blo 401768 404875 := bstep (se 1 (by rfl) ⟨303656, by rfl⟩ : syracuseStep 404875 = 607313) B607313
theorem B404887 : Blo 401768 404887 := bstep (se 1 (by rfl) ⟨303665, by rfl⟩ : syracuseStep 404887 = 607331) B607331
theorem B404907 : Blo 401768 404907 := bstep (se 1 (by rfl) ⟨303680, by rfl⟩ : syracuseStep 404907 = 607361) B607361
theorem B404919 : Blo 401768 404919 := bstep (se 1 (by rfl) ⟨303689, by rfl⟩ : syracuseStep 404919 = 607379) B607379
theorem B404939 : Blo 401768 404939 := bstep (se 1 (by rfl) ⟨303704, by rfl⟩ : syracuseStep 404939 = 607409) B607409
theorem B404951 : Blo 401768 404951 := bstep (se 1 (by rfl) ⟨303713, by rfl⟩ : syracuseStep 404951 = 607427) B607427
theorem B404971 : Blo 401768 404971 := bstep (se 1 (by rfl) ⟨303728, by rfl⟩ : syracuseStep 404971 = 607457) B607457
theorem B404983 : Blo 401768 404983 := bstep (se 1 (by rfl) ⟨303737, by rfl⟩ : syracuseStep 404983 = 607475) B607475
theorem B405003 : Blo 401768 405003 := bstep (se 1 (by rfl) ⟨303752, by rfl⟩ : syracuseStep 405003 = 607505) B607505
theorem B405015 : Blo 401768 405015 := bstep (se 1 (by rfl) ⟨303761, by rfl⟩ : syracuseStep 405015 = 607523) B607523
theorem B405035 : Blo 401768 405035 := bstep (se 1 (by rfl) ⟨303776, by rfl⟩ : syracuseStep 405035 = 607553) B607553
theorem B405047 : Blo 401768 405047 := bstep (se 1 (by rfl) ⟨303785, by rfl⟩ : syracuseStep 405047 = 607571) B607571
theorem B2043467 : Blo 401768 2043467 := bstep (se 1 (by rfl) ⟨1532600, by rfl⟩ : syracuseStep 2043467 = 3065201) B3065201
theorem B405067 : Blo 401768 405067 := bstep (se 1 (by rfl) ⟨303800, by rfl⟩ : syracuseStep 405067 = 607601) B607601
theorem B863831 : Blo 401768 863831 := bstep (se 1 (by rfl) ⟨647873, by rfl⟩ : syracuseStep 863831 = 1295747) B1295747
theorem B405079 : Blo 401768 405079 := bstep (se 1 (by rfl) ⟨303809, by rfl⟩ : syracuseStep 405079 = 607619) B607619
theorem B405099 : Blo 401768 405099 := bstep (se 1 (by rfl) ⟨303824, by rfl⟩ : syracuseStep 405099 = 607649) B607649
theorem B405111 : Blo 401768 405111 := bstep (se 1 (by rfl) ⟨303833, by rfl⟩ : syracuseStep 405111 = 607667) B607667
theorem B405131 : Blo 401768 405131 := bstep (se 1 (by rfl) ⟨303848, by rfl⟩ : syracuseStep 405131 = 607697) B607697
theorem B405143 : Blo 401768 405143 := bstep (se 1 (by rfl) ⟨303857, by rfl⟩ : syracuseStep 405143 = 607715) B607715
theorem B405163 : Blo 401768 405163 := bstep (se 1 (by rfl) ⟨303872, by rfl⟩ : syracuseStep 405163 = 607745) B607745
theorem B405175 : Blo 401768 405175 := bstep (se 1 (by rfl) ⟨303881, by rfl⟩ : syracuseStep 405175 = 607763) B607763
theorem B405195 : Blo 401768 405195 := bstep (se 1 (by rfl) ⟨303896, by rfl⟩ : syracuseStep 405195 = 607793) B607793
theorem B405207 : Blo 401768 405207 := bstep (se 1 (by rfl) ⟨303905, by rfl⟩ : syracuseStep 405207 = 607811) B607811
theorem B405227 : Blo 401768 405227 := bstep (se 1 (by rfl) ⟨303920, by rfl⟩ : syracuseStep 405227 = 607841) B607841
theorem B405239 : Blo 401768 405239 := bstep (se 1 (by rfl) ⟨303929, by rfl⟩ : syracuseStep 405239 = 607859) B607859
theorem B405259 : Blo 401768 405259 := bstep (se 1 (by rfl) ⟨303944, by rfl⟩ : syracuseStep 405259 = 607889) B607889
theorem B405271 : Blo 401768 405271 := bstep (se 1 (by rfl) ⟨303953, by rfl⟩ : syracuseStep 405271 = 607907) B607907
theorem B405291 : Blo 401768 405291 := bstep (se 1 (by rfl) ⟨303968, by rfl⟩ : syracuseStep 405291 = 607937) B607937
theorem B405303 : Blo 401768 405303 := bstep (se 1 (by rfl) ⟨303977, by rfl⟩ : syracuseStep 405303 = 607955) B607955
theorem B405323 : Blo 401768 405323 := bstep (se 1 (by rfl) ⟨303992, by rfl⟩ : syracuseStep 405323 = 607985) B607985
theorem B405335 : Blo 401768 405335 := bstep (se 1 (by rfl) ⟨304001, by rfl⟩ : syracuseStep 405335 = 608003) B608003
theorem B405355 : Blo 401768 405355 := bstep (se 1 (by rfl) ⟨304016, by rfl⟩ : syracuseStep 405355 = 608033) B608033
theorem B405367 : Blo 401768 405367 := bstep (se 1 (by rfl) ⟨304025, by rfl⟩ : syracuseStep 405367 = 608051) B608051
theorem B405387 : Blo 401768 405387 := bstep (se 1 (by rfl) ⟨304040, by rfl⟩ : syracuseStep 405387 = 608081) B608081
theorem B405399 : Blo 401768 405399 := bstep (se 1 (by rfl) ⟨304049, by rfl⟩ : syracuseStep 405399 = 608099) B608099
theorem B405419 : Blo 401768 405419 := bstep (se 1 (by rfl) ⟨304064, by rfl⟩ : syracuseStep 405419 = 608129) B608129
theorem B765875 : Blo 401768 765875 := bstep (se 1 (by rfl) ⟨574406, by rfl⟩ : syracuseStep 765875 = 1148813) B1148813
theorem B405431 : Blo 401768 405431 := bstep (se 1 (by rfl) ⟨304073, by rfl⟩ : syracuseStep 405431 = 608147) B608147
theorem B405451 : Blo 401768 405451 := bstep (se 1 (by rfl) ⟨304088, by rfl⟩ : syracuseStep 405451 = 608177) B608177
theorem B405463 : Blo 401768 405463 := bstep (se 1 (by rfl) ⟨304097, by rfl⟩ : syracuseStep 405463 = 608195) B608195
theorem B2306009 : Blo 401768 2306009 := bstep (se 2 (by rfl) ⟨864753, by rfl⟩ : syracuseStep 2306009 = 1729507) B1729507
theorem B405483 : Blo 401768 405483 := bstep (se 1 (by rfl) ⟨304112, by rfl⟩ : syracuseStep 405483 = 608225) B608225
theorem B405495 : Blo 401768 405495 := bstep (se 1 (by rfl) ⟨304121, by rfl⟩ : syracuseStep 405495 = 608243) B608243
theorem B405515 : Blo 401768 405515 := bstep (se 1 (by rfl) ⟨304136, by rfl⟩ : syracuseStep 405515 = 608273) B608273
theorem B405527 : Blo 401768 405527 := bstep (se 1 (by rfl) ⟨304145, by rfl⟩ : syracuseStep 405527 = 608291) B608291
theorem B405547 : Blo 401768 405547 := bstep (se 1 (by rfl) ⟨304160, by rfl⟩ : syracuseStep 405547 = 608321) B608321
theorem B405559 : Blo 401768 405559 := bstep (se 1 (by rfl) ⟨304169, by rfl⟩ : syracuseStep 405559 = 608339) B608339
theorem B766027 : Blo 401768 766027 := bstep (se 1 (by rfl) ⟨574520, by rfl⟩ : syracuseStep 766027 = 1149041) B1149041
theorem B405579 : Blo 401768 405579 := bstep (se 1 (by rfl) ⟨304184, by rfl⟩ : syracuseStep 405579 = 608369) B608369
theorem B405591 : Blo 401768 405591 := bstep (se 1 (by rfl) ⟨304193, by rfl⟩ : syracuseStep 405591 = 608387) B608387
theorem B405611 : Blo 401768 405611 := bstep (se 1 (by rfl) ⟨304208, by rfl⟩ : syracuseStep 405611 = 608417) B608417
theorem B405623 : Blo 401768 405623 := bstep (se 1 (by rfl) ⟨304217, by rfl⟩ : syracuseStep 405623 = 608435) B608435
theorem B405643 : Blo 401768 405643 := bstep (se 1 (by rfl) ⟨304232, by rfl⟩ : syracuseStep 405643 = 608465) B608465
theorem B405655 : Blo 401768 405655 := bstep (se 1 (by rfl) ⟨304241, by rfl⟩ : syracuseStep 405655 = 608483) B608483
theorem B405675 : Blo 401768 405675 := bstep (se 1 (by rfl) ⟨304256, by rfl⟩ : syracuseStep 405675 = 608513) B608513
theorem B405687 : Blo 401768 405687 := bstep (se 1 (by rfl) ⟨304265, by rfl⟩ : syracuseStep 405687 = 608531) B608531
theorem B405707 : Blo 401768 405707 := bstep (se 1 (by rfl) ⟨304280, by rfl⟩ : syracuseStep 405707 = 608561) B608561
theorem B405719 : Blo 401768 405719 := bstep (se 1 (by rfl) ⟨304289, by rfl⟩ : syracuseStep 405719 = 608579) B608579
theorem B1355993 : Blo 401768 1355993 := bstep (se 2 (by rfl) ⟨508497, by rfl⟩ : syracuseStep 1355993 = 1016995) B1016995
theorem B405739 : Blo 401768 405739 := bstep (se 1 (by rfl) ⟨304304, by rfl⟩ : syracuseStep 405739 = 608609) B608609
theorem B405751 : Blo 401768 405751 := bstep (se 1 (by rfl) ⟨304313, by rfl⟩ : syracuseStep 405751 = 608627) B608627
theorem B9318773 : Blo 401768 9318773 := bstep (se 5 (by rfl) ⟨436817, by rfl⟩ : syracuseStep 9318773 = 873635) B873635
theorem B766361 : Blo 401768 766361 := bstep (se 2 (by rfl) ⟨287385, by rfl⟩ : syracuseStep 766361 = 574771) B574771
theorem B1716659 : Blo 401768 1716659 := bstep (se 1 (by rfl) ⟨1287494, by rfl⟩ : syracuseStep 1716659 = 2574989) B2574989
theorem B1290775 : Blo 401768 1290775 := bstep (se 1 (by rfl) ⟨968081, by rfl⟩ : syracuseStep 1290775 = 1936163) B1936163
theorem B3551779 : Blo 401768 3551779 := bstep (se 1 (by rfl) ⟨2663834, by rfl⟩ : syracuseStep 3551779 = 5327669) B5327669
theorem B1094195 : Blo 401768 1094195 := bstep (se 1 (by rfl) ⟨820646, by rfl⟩ : syracuseStep 1094195 = 1641293) B1641293
theorem B602699 : Blo 401768 602699 := bstep (se 1 (by rfl) ⟨452024, by rfl⟩ : syracuseStep 602699 = 904049) B904049
theorem B3453515 : Blo 401768 3453515 := bstep (se 1 (by rfl) ⟨2590136, by rfl⟩ : syracuseStep 3453515 = 5180273) B5180273
theorem B1094219 : Blo 401768 1094219 := bstep (se 1 (by rfl) ⟨820664, by rfl⟩ : syracuseStep 1094219 = 1641329) B1641329
theorem B602711 : Blo 401768 602711 := bstep (se 1 (by rfl) ⟨452033, by rfl⟩ : syracuseStep 602711 = 904067) B904067
theorem B864857 : Blo 401768 864857 := bstep (se 2 (by rfl) ⟨324321, by rfl⟩ : syracuseStep 864857 = 648643) B648643
theorem B602777 : Blo 401768 602777 := bstep (se 2 (by rfl) ⟨226041, by rfl⟩ : syracuseStep 602777 = 452083) B452083
theorem B766657 : Blo 401768 766657 := bstep (se 2 (by rfl) ⟨287496, by rfl⟩ : syracuseStep 766657 = 574993) B574993
theorem B602891 : Blo 401768 602891 := bstep (se 1 (by rfl) ⟨452168, by rfl⟩ : syracuseStep 602891 = 904337) B904337
theorem B2175761 : Blo 401768 2175761 := bstep (se 2 (by rfl) ⟨815910, by rfl⟩ : syracuseStep 2175761 = 1631821) B1631821
theorem B602903 : Blo 401768 602903 := bstep (se 1 (by rfl) ⟨452177, by rfl⟩ : syracuseStep 602903 = 904355) B904355
theorem B4371245 : Blo 401768 4371245 := bstep (se 3 (by rfl) ⟨819608, by rfl⟩ : syracuseStep 4371245 = 1639217) B1639217
theorem B602969 : Blo 401768 602969 := bstep (se 2 (by rfl) ⟨226113, by rfl⟩ : syracuseStep 602969 = 452227) B452227
theorem B2274149 : Blo 401768 2274149 := bstep (se 4 (by rfl) ⟨213201, by rfl⟩ : syracuseStep 2274149 = 426403) B426403
theorem B1454993 : Blo 401768 1454993 := bstep (se 2 (by rfl) ⟨545622, by rfl⟩ : syracuseStep 1454993 = 1091245) B1091245
theorem B1356695 : Blo 401768 1356695 := bstep (se 1 (by rfl) ⟨1017521, by rfl⟩ : syracuseStep 1356695 = 2035043) B2035043
theorem B3879859 : Blo 401768 3879859 := bstep (se 1 (by rfl) ⟨2909894, by rfl⟩ : syracuseStep 3879859 = 5819789) B5819789
theorem B603083 : Blo 401768 603083 := bstep (se 1 (by rfl) ⟨452312, by rfl⟩ : syracuseStep 603083 = 904625) B904625
theorem B1291211 : Blo 401768 1291211 := bstep (se 1 (by rfl) ⟨968408, by rfl⟩ : syracuseStep 1291211 = 1936817) B1936817
theorem B603095 : Blo 401768 603095 := bstep (se 1 (by rfl) ⟨452321, by rfl⟩ : syracuseStep 603095 = 904643) B904643
theorem B766999 : Blo 401768 766999 := bstep (se 1 (by rfl) ⟨575249, by rfl⟩ : syracuseStep 766999 = 1150499) B1150499
theorem B603161 : Blo 401768 603161 := bstep (se 2 (by rfl) ⟨226185, by rfl⟩ : syracuseStep 603161 = 452371) B452371
theorem B603275 : Blo 401768 603275 := bstep (se 1 (by rfl) ⟨452456, by rfl⟩ : syracuseStep 603275 = 904913) B904913
theorem B603287 : Blo 401768 603287 := bstep (se 1 (by rfl) ⟨452465, by rfl⟩ : syracuseStep 603287 = 904931) B904931
theorem B603353 : Blo 401768 603353 := bstep (se 2 (by rfl) ⟨226257, by rfl⟩ : syracuseStep 603353 = 452515) B452515
theorem B2045249 : Blo 401768 2045249 := bstep (se 2 (by rfl) ⟨766968, by rfl⟩ : syracuseStep 2045249 = 1533937) B1533937
theorem B1750337 : Blo 401768 1750337 := bstep (se 2 (by rfl) ⟨656376, by rfl⟩ : syracuseStep 1750337 = 1312753) B1312753
theorem B603467 : Blo 401768 603467 := bstep (se 1 (by rfl) ⟨452600, by rfl⟩ : syracuseStep 603467 = 905201) B905201
theorem B603479 : Blo 401768 603479 := bstep (se 1 (by rfl) ⟨452609, by rfl⟩ : syracuseStep 603479 = 905219) B905219
theorem B603545 : Blo 401768 603545 := bstep (se 2 (by rfl) ⟨226329, by rfl⟩ : syracuseStep 603545 = 452659) B452659
theorem B1357235 : Blo 401768 1357235 := bstep (se 1 (by rfl) ⟨1017926, by rfl⟩ : syracuseStep 1357235 = 2035853) B2035853
theorem B7386547 : Blo 401768 7386547 := bstep (se 1 (by rfl) ⟨5539910, by rfl⟩ : syracuseStep 7386547 = 11079821) B11079821
theorem B603659 : Blo 401768 603659 := bstep (se 1 (by rfl) ⟨452744, by rfl⟩ : syracuseStep 603659 = 905489) B905489
theorem B603671 : Blo 401768 603671 := bstep (se 1 (by rfl) ⟨452753, by rfl⟩ : syracuseStep 603671 = 905507) B905507
theorem B3061313 : Blo 401768 3061313 := bstep (se 2 (by rfl) ⟨1147992, by rfl⟩ : syracuseStep 3061313 = 2295985) B2295985
theorem B2307649 : Blo 401768 2307649 := bstep (se 2 (by rfl) ⟨865368, by rfl⟩ : syracuseStep 2307649 = 1730737) B1730737
theorem B603737 : Blo 401768 603737 := bstep (se 2 (by rfl) ⟨226401, by rfl⟩ : syracuseStep 603737 = 452803) B452803
theorem B9942659 : Blo 401768 9942659 := bstep (se 1 (by rfl) ⟨7456994, by rfl⟩ : syracuseStep 9942659 = 14913989) B14913989
theorem B1357505 : Blo 401768 1357505 := bstep (se 2 (by rfl) ⟨509064, by rfl⟩ : syracuseStep 1357505 = 1018129) B1018129
theorem B603851 : Blo 401768 603851 := bstep (se 1 (by rfl) ⟨452888, by rfl⟩ : syracuseStep 603851 = 905777) B905777
theorem B603863 : Blo 401768 603863 := bstep (se 1 (by rfl) ⟨452897, by rfl⟩ : syracuseStep 603863 = 905795) B905795
theorem B3880709 : Blo 401768 3880709 := bstep (se 4 (by rfl) ⟨363816, by rfl⟩ : syracuseStep 3880709 = 727633) B727633
theorem B603929 : Blo 401768 603929 := bstep (se 2 (by rfl) ⟨226473, by rfl⟩ : syracuseStep 603929 = 452947) B452947
theorem B1292107 : Blo 401768 1292107 := bstep (se 1 (by rfl) ⟨969080, by rfl⟩ : syracuseStep 1292107 = 1938161) B1938161
theorem B767819 : Blo 401768 767819 := bstep (se 1 (by rfl) ⟨575864, by rfl⟩ : syracuseStep 767819 = 1151729) B1151729
theorem B767873 : Blo 401768 767873 := bstep (se 2 (by rfl) ⟨287952, by rfl⟩ : syracuseStep 767873 = 575905) B575905
theorem B604043 : Blo 401768 604043 := bstep (se 1 (by rfl) ⟨453032, by rfl⟩ : syracuseStep 604043 = 906065) B906065
theorem B604055 : Blo 401768 604055 := bstep (se 1 (by rfl) ⟨453041, by rfl⟩ : syracuseStep 604055 = 906083) B906083
theorem B604121 : Blo 401768 604121 := bstep (se 2 (by rfl) ⟨226545, by rfl⟩ : syracuseStep 604121 = 453091) B453091
theorem B604235 : Blo 401768 604235 := bstep (se 1 (by rfl) ⟨453176, by rfl⟩ : syracuseStep 604235 = 906353) B906353
theorem B604247 : Blo 401768 604247 := bstep (se 1 (by rfl) ⟨453185, by rfl⟩ : syracuseStep 604247 = 906371) B906371
theorem B604313 : Blo 401768 604313 := bstep (se 2 (by rfl) ⟨226617, by rfl⟩ : syracuseStep 604313 = 453235) B453235
theorem B866497 : Blo 401768 866497 := bstep (se 2 (by rfl) ⟨324936, by rfl⟩ : syracuseStep 866497 = 649873) B649873
theorem B1358045 : Blo 401768 1358045 := bstep (se 3 (by rfl) ⟨254633, by rfl⟩ : syracuseStep 1358045 = 509267) B509267
theorem B604427 : Blo 401768 604427 := bstep (se 1 (by rfl) ⟨453320, by rfl⟩ : syracuseStep 604427 = 906641) B906641
theorem B604439 : Blo 401768 604439 := bstep (se 1 (by rfl) ⟨453329, by rfl⟩ : syracuseStep 604439 = 906659) B906659
theorem B604505 : Blo 401768 604505 := bstep (se 2 (by rfl) ⟨226689, by rfl⟩ : syracuseStep 604505 = 453379) B453379
theorem B1456535 : Blo 401768 1456535 := bstep (se 1 (by rfl) ⟨1092401, by rfl⟩ : syracuseStep 1456535 = 2184803) B2184803
theorem B1292723 : Blo 401768 1292723 := bstep (se 1 (by rfl) ⟨969542, by rfl⟩ : syracuseStep 1292723 = 1939085) B1939085
theorem B604619 : Blo 401768 604619 := bstep (se 1 (by rfl) ⟨453464, by rfl⟩ : syracuseStep 604619 = 906929) B906929
theorem B604631 : Blo 401768 604631 := bstep (se 1 (by rfl) ⟨453473, by rfl⟩ : syracuseStep 604631 = 906947) B906947
theorem B604697 : Blo 401768 604697 := bstep (se 2 (by rfl) ⟨226761, by rfl⟩ : syracuseStep 604697 = 453523) B453523
theorem B1292851 : Blo 401768 1292851 := bstep (se 1 (by rfl) ⟨969638, by rfl⟩ : syracuseStep 1292851 = 1939277) B1939277
theorem B604811 : Blo 401768 604811 := bstep (se 1 (by rfl) ⟨453608, by rfl⟩ : syracuseStep 604811 = 907217) B907217
theorem B604823 : Blo 401768 604823 := bstep (se 1 (by rfl) ⟨453617, by rfl⟩ : syracuseStep 604823 = 907235) B907235
theorem B604889 : Blo 401768 604889 := bstep (se 2 (by rfl) ⟨226833, by rfl⟩ : syracuseStep 604889 = 453667) B453667
theorem B768791 : Blo 401768 768791 := bstep (se 1 (by rfl) ⟨576593, by rfl⟩ : syracuseStep 768791 = 1153187) B1153187
theorem B2177837 : Blo 401768 2177837 := bstep (se 3 (by rfl) ⟨408344, by rfl⟩ : syracuseStep 2177837 = 816689) B816689
theorem B1850177 : Blo 401768 1850177 := bstep (se 2 (by rfl) ⟨693816, by rfl⟩ : syracuseStep 1850177 = 1387633) B1387633
theorem B605003 : Blo 401768 605003 := bstep (se 1 (by rfl) ⟨453752, by rfl⟩ : syracuseStep 605003 = 907505) B907505
theorem B605015 : Blo 401768 605015 := bstep (se 1 (by rfl) ⟨453761, by rfl⟩ : syracuseStep 605015 = 907523) B907523
theorem B605081 : Blo 401768 605081 := bstep (se 2 (by rfl) ⟨226905, by rfl⟩ : syracuseStep 605081 = 453811) B453811
theorem B605195 : Blo 401768 605195 := bstep (se 1 (by rfl) ⟨453896, by rfl⟩ : syracuseStep 605195 = 907793) B907793
theorem B605207 : Blo 401768 605207 := bstep (se 1 (by rfl) ⟨453905, by rfl⟩ : syracuseStep 605207 = 907811) B907811
theorem B605273 : Blo 401768 605273 := bstep (se 2 (by rfl) ⟨226977, by rfl⟩ : syracuseStep 605273 = 453955) B453955
theorem B1719427 : Blo 401768 1719427 := bstep (se 1 (by rfl) ⟨1289570, by rfl⟩ : syracuseStep 1719427 = 2579141) B2579141
theorem B605387 : Blo 401768 605387 := bstep (se 1 (by rfl) ⟨454040, by rfl⟩ : syracuseStep 605387 = 908081) B908081
theorem B605399 : Blo 401768 605399 := bstep (se 1 (by rfl) ⟨454049, by rfl⟩ : syracuseStep 605399 = 908099) B908099
theorem B2047193 : Blo 401768 2047193 := bstep (se 2 (by rfl) ⟨767697, by rfl⟩ : syracuseStep 2047193 = 1535395) B1535395
theorem B6208753 : Blo 401768 6208753 := bstep (se 2 (by rfl) ⟨2328282, by rfl⟩ : syracuseStep 6208753 = 4656565) B4656565
theorem B605465 : Blo 401768 605465 := bstep (se 2 (by rfl) ⟨227049, by rfl⟩ : syracuseStep 605465 = 454099) B454099
theorem B1457459 : Blo 401768 1457459 := bstep (se 1 (by rfl) ⟨1093094, by rfl⟩ : syracuseStep 1457459 = 2186189) B2186189
theorem B769331 : Blo 401768 769331 := bstep (se 1 (by rfl) ⟨576998, by rfl⟩ : syracuseStep 769331 = 1153997) B1153997
theorem B1359179 : Blo 401768 1359179 := bstep (se 1 (by rfl) ⟨1019384, by rfl⟩ : syracuseStep 1359179 = 2038769) B2038769
theorem B572761 : Blo 401768 572761 := bstep (se 2 (by rfl) ⟨214785, by rfl⟩ : syracuseStep 572761 = 429571) B429571
theorem B605579 : Blo 401768 605579 := bstep (se 1 (by rfl) ⟨454184, by rfl⟩ : syracuseStep 605579 = 908369) B908369
theorem B605591 : Blo 401768 605591 := bstep (se 1 (by rfl) ⟨454193, by rfl⟩ : syracuseStep 605591 = 908387) B908387
theorem B3063257 : Blo 401768 3063257 := bstep (se 2 (by rfl) ⟨1148721, by rfl⟩ : syracuseStep 3063257 = 2297443) B2297443
theorem B605657 : Blo 401768 605657 := bstep (se 2 (by rfl) ⟨227121, by rfl⟩ : syracuseStep 605657 = 454243) B454243
theorem B605771 : Blo 401768 605771 := bstep (se 1 (by rfl) ⟨454328, by rfl⟩ : syracuseStep 605771 = 908657) B908657
theorem B605783 : Blo 401768 605783 := bstep (se 1 (by rfl) ⟨454337, by rfl⟩ : syracuseStep 605783 = 908675) B908675
theorem B1359449 : Blo 401768 1359449 := bstep (se 2 (by rfl) ⟨509793, by rfl⟩ : syracuseStep 1359449 = 1019587) B1019587
theorem B605849 : Blo 401768 605849 := bstep (se 2 (by rfl) ⟨227193, by rfl⟩ : syracuseStep 605849 = 454387) B454387
theorem B605963 : Blo 401768 605963 := bstep (se 1 (by rfl) ⟨454472, by rfl⟩ : syracuseStep 605963 = 908945) B908945
theorem B1326871 : Blo 401768 1326871 := bstep (se 1 (by rfl) ⟨995153, by rfl⟩ : syracuseStep 1326871 = 1990307) B1990307
theorem B605975 : Blo 401768 605975 := bstep (se 1 (by rfl) ⟨454481, by rfl⟩ : syracuseStep 605975 = 908963) B908963
theorem B769817 : Blo 401768 769817 := bstep (se 2 (by rfl) ⟨288681, by rfl⟩ : syracuseStep 769817 = 577363) B577363
theorem B606041 : Blo 401768 606041 := bstep (se 2 (by rfl) ⟨227265, by rfl⟩ : syracuseStep 606041 = 454531) B454531
theorem B606155 : Blo 401768 606155 := bstep (se 1 (by rfl) ⟨454616, by rfl⟩ : syracuseStep 606155 = 909233) B909233
theorem B606167 : Blo 401768 606167 := bstep (se 1 (by rfl) ⟨454625, by rfl⟩ : syracuseStep 606167 = 909251) B909251
theorem B606233 : Blo 401768 606233 := bstep (se 2 (by rfl) ⟨227337, by rfl⟩ : syracuseStep 606233 = 454675) B454675
theorem B1720385 : Blo 401768 1720385 := bstep (se 2 (by rfl) ⟨645144, by rfl⟩ : syracuseStep 1720385 = 1290289) B1290289
theorem B1949771 : Blo 401768 1949771 := bstep (se 1 (by rfl) ⟨1462328, by rfl⟩ : syracuseStep 1949771 = 2924657) B2924657
theorem B606347 : Blo 401768 606347 := bstep (se 1 (by rfl) ⟨454760, by rfl⟩ : syracuseStep 606347 = 909521) B909521
theorem B606359 : Blo 401768 606359 := bstep (se 1 (by rfl) ⟨454769, by rfl⟩ : syracuseStep 606359 = 909539) B909539
theorem B573655 : Blo 401768 573655 := bstep (se 1 (by rfl) ⟨430241, by rfl⟩ : syracuseStep 573655 = 860483) B860483
theorem B606425 : Blo 401768 606425 := bstep (se 2 (by rfl) ⟨227409, by rfl⟩ : syracuseStep 606425 = 454819) B454819
theorem B1360151 : Blo 401768 1360151 := bstep (se 1 (by rfl) ⟨1020113, by rfl⟩ : syracuseStep 1360151 = 2040227) B2040227
theorem B606539 : Blo 401768 606539 := bstep (se 1 (by rfl) ⟨454904, by rfl⟩ : syracuseStep 606539 = 909809) B909809
theorem B606551 : Blo 401768 606551 := bstep (se 1 (by rfl) ⟨454913, by rfl⟩ : syracuseStep 606551 = 909827) B909827
theorem B606617 : Blo 401768 606617 := bstep (se 2 (by rfl) ⟨227481, by rfl⟩ : syracuseStep 606617 = 454963) B454963
theorem B1458611 : Blo 401768 1458611 := bstep (se 1 (by rfl) ⟨1093958, by rfl⟩ : syracuseStep 1458611 = 2187917) B2187917
theorem B606731 : Blo 401768 606731 := bstep (se 1 (by rfl) ⟨455048, by rfl⟩ : syracuseStep 606731 = 910097) B910097
theorem B606743 : Blo 401768 606743 := bstep (se 1 (by rfl) ⟨455057, by rfl⟩ : syracuseStep 606743 = 910115) B910115
theorem B2900555 : Blo 401768 2900555 := bstep (se 1 (by rfl) ⟨2175416, by rfl⟩ : syracuseStep 2900555 = 4350833) B4350833
theorem B606809 : Blo 401768 606809 := bstep (se 2 (by rfl) ⟨227553, by rfl⟩ : syracuseStep 606809 = 455107) B455107
theorem B508619 : Blo 401768 508619 := bstep (se 1 (by rfl) ⟨381464, by rfl⟩ : syracuseStep 508619 = 762929) B762929
theorem B606923 : Blo 401768 606923 := bstep (se 1 (by rfl) ⟨455192, by rfl⟩ : syracuseStep 606923 = 910385) B910385
theorem B606935 : Blo 401768 606935 := bstep (se 1 (by rfl) ⟨455201, by rfl⟩ : syracuseStep 606935 = 910403) B910403
theorem B574219 : Blo 401768 574219 := bstep (se 1 (by rfl) ⟨430664, by rfl⟩ : syracuseStep 574219 = 861329) B861329
theorem B607001 : Blo 401768 607001 := bstep (se 2 (by rfl) ⟨227625, by rfl⟩ : syracuseStep 607001 = 455251) B455251
theorem B2048813 : Blo 401768 2048813 := bstep (se 3 (by rfl) ⟨384152, by rfl⟩ : syracuseStep 2048813 = 768305) B768305
theorem B1360691 : Blo 401768 1360691 := bstep (se 1 (by rfl) ⟨1020518, by rfl⟩ : syracuseStep 1360691 = 2041037) B2041037
theorem B607115 : Blo 401768 607115 := bstep (se 1 (by rfl) ⟨455336, by rfl⟩ : syracuseStep 607115 = 910673) B910673
theorem B607127 : Blo 401768 607127 := bstep (se 1 (by rfl) ⟨455345, by rfl⟩ : syracuseStep 607127 = 910691) B910691
theorem B607193 : Blo 401768 607193 := bstep (se 2 (by rfl) ⟨227697, by rfl⟩ : syracuseStep 607193 = 455395) B455395
theorem B1557521 : Blo 401768 1557521 := bstep (se 2 (by rfl) ⟨584070, by rfl⟩ : syracuseStep 1557521 = 1168141) B1168141
theorem B1360961 : Blo 401768 1360961 := bstep (se 2 (by rfl) ⟨510360, by rfl⟩ : syracuseStep 1360961 = 1020721) B1020721
theorem B607307 : Blo 401768 607307 := bstep (se 1 (by rfl) ⟨455480, by rfl⟩ : syracuseStep 607307 = 910961) B910961
theorem B607319 : Blo 401768 607319 := bstep (se 1 (by rfl) ⟨455489, by rfl⟩ : syracuseStep 607319 = 910979) B910979
theorem B607385 : Blo 401768 607385 := bstep (se 2 (by rfl) ⟨227769, by rfl⟩ : syracuseStep 607385 = 455539) B455539
theorem B607499 : Blo 401768 607499 := bstep (se 1 (by rfl) ⟨455624, by rfl⟩ : syracuseStep 607499 = 911249) B911249
theorem B607511 : Blo 401768 607511 := bstep (se 1 (by rfl) ⟨455633, by rfl⟩ : syracuseStep 607511 = 911267) B911267
theorem B607577 : Blo 401768 607577 := bstep (se 2 (by rfl) ⟨227841, by rfl⟩ : syracuseStep 607577 = 455683) B455683
theorem B509323 : Blo 401768 509323 := bstep (se 1 (by rfl) ⟨381992, by rfl⟩ : syracuseStep 509323 = 763985) B763985
theorem B1754561 : Blo 401768 1754561 := bstep (se 2 (by rfl) ⟨657960, by rfl⟩ : syracuseStep 1754561 = 1315921) B1315921
theorem B607691 : Blo 401768 607691 := bstep (se 1 (by rfl) ⟨455768, by rfl⟩ : syracuseStep 607691 = 911537) B911537
theorem B607703 : Blo 401768 607703 := bstep (se 1 (by rfl) ⟨455777, by rfl⟩ : syracuseStep 607703 = 911555) B911555
theorem B607769 : Blo 401768 607769 := bstep (se 2 (by rfl) ⟨227913, by rfl⟩ : syracuseStep 607769 = 455827) B455827
theorem B1361501 : Blo 401768 1361501 := bstep (se 3 (by rfl) ⟨255281, by rfl⟩ : syracuseStep 1361501 = 510563) B510563
theorem B607883 : Blo 401768 607883 := bstep (se 1 (by rfl) ⟨455912, by rfl⟩ : syracuseStep 607883 = 911825) B911825
theorem B509591 : Blo 401768 509591 := bstep (se 1 (by rfl) ⟨382193, by rfl⟩ : syracuseStep 509591 = 764387) B764387
theorem B607895 : Blo 401768 607895 := bstep (se 1 (by rfl) ⟨455921, by rfl⟩ : syracuseStep 607895 = 911843) B911843
theorem B1722059 : Blo 401768 1722059 := bstep (se 1 (by rfl) ⟨1291544, by rfl⟩ : syracuseStep 1722059 = 2583089) B2583089
theorem B4933325 : Blo 401768 4933325 := bstep (se 3 (by rfl) ⟨924998, by rfl⟩ : syracuseStep 4933325 = 1849997) B1849997
theorem B607961 : Blo 401768 607961 := bstep (se 2 (by rfl) ⟨227985, by rfl⟩ : syracuseStep 607961 = 455971) B455971
theorem B608075 : Blo 401768 608075 := bstep (se 1 (by rfl) ⟨456056, by rfl⟩ : syracuseStep 608075 = 912113) B912113
theorem B608087 : Blo 401768 608087 := bstep (se 1 (by rfl) ⟨456065, by rfl⟩ : syracuseStep 608087 = 912131) B912131
theorem B608153 : Blo 401768 608153 := bstep (se 2 (by rfl) ⟨228057, by rfl⟩ : syracuseStep 608153 = 456115) B456115
theorem B608267 : Blo 401768 608267 := bstep (se 1 (by rfl) ⟨456200, by rfl⟩ : syracuseStep 608267 = 912401) B912401
theorem B608279 : Blo 401768 608279 := bstep (se 1 (by rfl) ⟨456209, by rfl⟩ : syracuseStep 608279 = 912419) B912419
theorem B608345 : Blo 401768 608345 := bstep (se 2 (by rfl) ⟨228129, by rfl⟩ : syracuseStep 608345 = 456259) B456259
theorem B1460369 : Blo 401768 1460369 := bstep (se 2 (by rfl) ⟨547638, by rfl⟩ : syracuseStep 1460369 = 1095277) B1095277
theorem B608459 : Blo 401768 608459 := bstep (se 1 (by rfl) ⟨456344, by rfl⟩ : syracuseStep 608459 = 912689) B912689
theorem B608471 : Blo 401768 608471 := bstep (se 1 (by rfl) ⟨456353, by rfl⟩ : syracuseStep 608471 = 912707) B912707
theorem B575705 : Blo 401768 575705 := bstep (se 2 (by rfl) ⟨215889, by rfl⟩ : syracuseStep 575705 = 431779) B431779
theorem B608537 : Blo 401768 608537 := bstep (se 2 (by rfl) ⟨228201, by rfl⟩ : syracuseStep 608537 = 456403) B456403
theorem B510295 : Blo 401768 510295 := bstep (se 1 (by rfl) ⟨382721, by rfl⟩ : syracuseStep 510295 = 765443) B765443
theorem B1526147 : Blo 401768 1526147 := bstep (se 1 (by rfl) ⟨1144610, by rfl⟩ : syracuseStep 1526147 = 2289221) B2289221
theorem B608651 : Blo 401768 608651 := bstep (se 1 (by rfl) ⟨456488, by rfl⟩ : syracuseStep 608651 = 912977) B912977
theorem B1526161 : Blo 401768 1526161 := bstep (se 2 (by rfl) ⟨572310, by rfl⟩ : syracuseStep 1526161 = 1144621) B1144621
theorem B2443841 : Blo 401768 2443841 := bstep (se 2 (by rfl) ⟨916440, by rfl⟩ : syracuseStep 2443841 = 1832881) B1832881
theorem B3492503 : Blo 401768 3492503 := bstep (se 1 (by rfl) ⟨2619377, by rfl⟩ : syracuseStep 3492503 = 5238755) B5238755
theorem B1526465 : Blo 401768 1526465 := bstep (se 2 (by rfl) ⟨572424, by rfl⟩ : syracuseStep 1526465 = 1144849) B1144849
theorem B1231553 : Blo 401768 1231553 := bstep (se 2 (by rfl) ⟨461832, by rfl⟩ : syracuseStep 1231553 = 923665) B923665
theorem B1362635 : Blo 401768 1362635 := bstep (se 1 (by rfl) ⟨1021976, by rfl⟩ : syracuseStep 1362635 = 2043953) B2043953
theorem B19942129 : Blo 401768 19942129 := bstep (se 2 (by rfl) ⟨7478298, by rfl⟩ : syracuseStep 19942129 = 14956597) B14956597
theorem B3066659 : Blo 401768 3066659 := bstep (se 1 (by rfl) ⟨2299994, by rfl⟩ : syracuseStep 3066659 = 4599989) B4599989
theorem B576343 : Blo 401768 576343 := bstep (se 1 (by rfl) ⟨432257, by rfl⟩ : syracuseStep 576343 = 864515) B864515
theorem B904139 : Blo 401768 904139 := bstep (se 1 (by rfl) ⟨678104, by rfl⟩ : syracuseStep 904139 = 1356209) B1356209
theorem B1362905 : Blo 401768 1362905 := bstep (se 2 (by rfl) ⟨511089, by rfl⟩ : syracuseStep 1362905 = 1022179) B1022179
theorem B904193 : Blo 401768 904193 := bstep (se 2 (by rfl) ⟨339072, by rfl⟩ : syracuseStep 904193 = 678145) B678145
theorem B937099 : Blo 401768 937099 := bstep (se 1 (by rfl) ⟨702824, by rfl⟩ : syracuseStep 937099 = 1405649) B1405649
theorem B904409 : Blo 401768 904409 := bstep (se 2 (by rfl) ⟨339153, by rfl⟩ : syracuseStep 904409 = 678307) B678307
theorem B904499 : Blo 401768 904499 := bstep (se 1 (by rfl) ⟨678374, by rfl⟩ : syracuseStep 904499 = 1356749) B1356749
theorem B904535 : Blo 401768 904535 := bstep (se 1 (by rfl) ⟨678401, by rfl⟩ : syracuseStep 904535 = 1356803) B1356803
theorem B1527133 : Blo 401768 1527133 := bstep (se 3 (by rfl) ⟨286337, by rfl⟩ : syracuseStep 1527133 = 572675) B572675
theorem B904715 : Blo 401768 904715 := bstep (se 1 (by rfl) ⟨678536, by rfl⟩ : syracuseStep 904715 = 1357073) B1357073
theorem B577049 : Blo 401768 577049 := bstep (se 2 (by rfl) ⟨216393, by rfl⟩ : syracuseStep 577049 = 432787) B432787
theorem B904769 : Blo 401768 904769 := bstep (se 2 (by rfl) ⟨339288, by rfl⟩ : syracuseStep 904769 = 678577) B678577
theorem B1035841 : Blo 401768 1035841 := bstep (se 2 (by rfl) ⟨388440, by rfl⟩ : syracuseStep 1035841 = 776881) B776881
theorem B577163 : Blo 401768 577163 := bstep (se 1 (by rfl) ⟨432872, by rfl⟩ : syracuseStep 577163 = 865745) B865745
theorem B1363607 : Blo 401768 1363607 := bstep (se 1 (by rfl) ⟨1022705, by rfl⟩ : syracuseStep 1363607 = 2045411) B2045411
theorem B1560323 : Blo 401768 1560323 := bstep (se 1 (by rfl) ⟨1170242, by rfl⟩ : syracuseStep 1560323 = 2340485) B2340485
theorem B904985 : Blo 401768 904985 := bstep (se 2 (by rfl) ⟨339369, by rfl⟩ : syracuseStep 904985 = 678739) B678739
theorem B16568165 : Blo 401768 16568165 := bstep (se 4 (by rfl) ⟨1553265, by rfl⟩ : syracuseStep 16568165 = 3106531) B3106531
theorem B905075 : Blo 401768 905075 := bstep (se 1 (by rfl) ⟨678806, by rfl⟩ : syracuseStep 905075 = 1357613) B1357613
theorem B905111 : Blo 401768 905111 := bstep (se 1 (by rfl) ⟨678833, by rfl⟩ : syracuseStep 905111 = 1357667) B1357667
theorem B512011 : Blo 401768 512011 := bstep (se 1 (by rfl) ⟨384008, by rfl⟩ : syracuseStep 512011 = 768017) B768017
theorem B905291 : Blo 401768 905291 := bstep (se 1 (by rfl) ⟨678968, by rfl⟩ : syracuseStep 905291 = 1357937) B1357937
theorem B970841 : Blo 401768 970841 := bstep (se 2 (by rfl) ⟨364065, by rfl⟩ : syracuseStep 970841 = 728131) B728131
theorem B905345 : Blo 401768 905345 := bstep (se 2 (by rfl) ⟨339504, by rfl⟩ : syracuseStep 905345 = 679009) B679009
theorem B577687 : Blo 401768 577687 := bstep (se 1 (by rfl) ⟨433265, by rfl⟩ : syracuseStep 577687 = 866531) B866531
theorem B1364147 : Blo 401768 1364147 := bstep (se 1 (by rfl) ⟨1023110, by rfl⟩ : syracuseStep 1364147 = 2046221) B2046221
theorem B1724723 : Blo 401768 1724723 := bstep (se 1 (by rfl) ⟨1293542, by rfl⟩ : syracuseStep 1724723 = 2587085) B2587085
theorem B905561 : Blo 401768 905561 := bstep (se 2 (by rfl) ⟨339585, by rfl⟩ : syracuseStep 905561 = 679171) B679171
theorem B905651 : Blo 401768 905651 := bstep (se 1 (by rfl) ⟨679238, by rfl⟩ : syracuseStep 905651 = 1358477) B1358477
theorem B1364417 : Blo 401768 1364417 := bstep (se 2 (by rfl) ⟨511656, by rfl⟩ : syracuseStep 1364417 = 1023313) B1023313
theorem B905687 : Blo 401768 905687 := bstep (se 1 (by rfl) ⟨679265, by rfl⟩ : syracuseStep 905687 = 1358531) B1358531
theorem B1528409 : Blo 401768 1528409 := bstep (se 2 (by rfl) ⟨573153, by rfl⟩ : syracuseStep 1528409 = 1146307) B1146307
theorem B2052701 : Blo 401768 2052701 := bstep (se 3 (by rfl) ⟨384881, by rfl⟩ : syracuseStep 2052701 = 769763) B769763
theorem B905867 : Blo 401768 905867 := bstep (se 1 (by rfl) ⟨679400, by rfl⟩ : syracuseStep 905867 = 1358801) B1358801
theorem B905921 : Blo 401768 905921 := bstep (se 2 (by rfl) ⟨339720, by rfl⟩ : syracuseStep 905921 = 679441) B679441
theorem B545497 : Blo 401768 545497 := bstep (se 2 (by rfl) ⟨204561, by rfl⟩ : syracuseStep 545497 = 409123) B409123
theorem B906137 : Blo 401768 906137 := bstep (se 2 (by rfl) ⟨339801, by rfl⟩ : syracuseStep 906137 = 679603) B679603
theorem B512983 : Blo 401768 512983 := bstep (se 1 (by rfl) ⟨384737, by rfl⟩ : syracuseStep 512983 = 769475) B769475
theorem B1364957 : Blo 401768 1364957 := bstep (se 3 (by rfl) ⟨255929, by rfl⟩ : syracuseStep 1364957 = 511859) B511859
theorem B906227 : Blo 401768 906227 := bstep (se 1 (by rfl) ⟨679670, by rfl⟩ : syracuseStep 906227 = 1359341) B1359341
theorem B906263 : Blo 401768 906263 := bstep (se 1 (by rfl) ⟨679697, by rfl⟩ : syracuseStep 906263 = 1359395) B1359395
theorem B3265687 : Blo 401768 3265687 := bstep (se 1 (by rfl) ⟨2449265, by rfl⟩ : syracuseStep 3265687 = 4898531) B4898531
theorem B906443 : Blo 401768 906443 := bstep (se 1 (by rfl) ⟨679832, by rfl⟩ : syracuseStep 906443 = 1359665) B1359665
theorem B644311 : Blo 401768 644311 := bstep (se 1 (by rfl) ⟨483233, by rfl⟩ : syracuseStep 644311 = 966467) B966467
theorem B906497 : Blo 401768 906497 := bstep (se 2 (by rfl) ⟨339936, by rfl⟩ : syracuseStep 906497 = 679873) B679873
theorem B7853429 : Blo 401768 7853429 := bstep (se 5 (by rfl) ⟨368129, by rfl⟩ : syracuseStep 7853429 = 736259) B736259
theorem B906713 : Blo 401768 906713 := bstep (se 2 (by rfl) ⟨340017, by rfl⟩ : syracuseStep 906713 = 680035) B680035
theorem B906803 : Blo 401768 906803 := bstep (se 1 (by rfl) ⟨680102, by rfl⟩ : syracuseStep 906803 = 1360205) B1360205
theorem B906839 : Blo 401768 906839 := bstep (se 1 (by rfl) ⟨680129, by rfl⟩ : syracuseStep 906839 = 1360259) B1360259
theorem B1726211 : Blo 401768 1726211 := bstep (se 1 (by rfl) ⟨1294658, by rfl⟩ : syracuseStep 1726211 = 2589317) B2589317
theorem B907019 : Blo 401768 907019 := bstep (se 1 (by rfl) ⟨680264, by rfl⟩ : syracuseStep 907019 = 1360529) B1360529
theorem B907073 : Blo 401768 907073 := bstep (se 2 (by rfl) ⟨340152, by rfl⟩ : syracuseStep 907073 = 680305) B680305
theorem B645131 : Blo 401768 645131 := bstep (se 1 (by rfl) ⟨483848, by rfl⟩ : syracuseStep 645131 = 967697) B967697
theorem B907289 : Blo 401768 907289 := bstep (se 2 (by rfl) ⟨340233, by rfl⟩ : syracuseStep 907289 = 680467) B680467
theorem B1366091 : Blo 401768 1366091 := bstep (se 1 (by rfl) ⟨1024568, by rfl⟩ : syracuseStep 1366091 = 2049137) B2049137
theorem B1038425 : Blo 401768 1038425 := bstep (se 2 (by rfl) ⟨389409, by rfl⟩ : syracuseStep 1038425 = 778819) B778819
theorem B907379 : Blo 401768 907379 := bstep (se 1 (by rfl) ⟨680534, by rfl⟩ : syracuseStep 907379 = 1361069) B1361069
theorem B907415 : Blo 401768 907415 := bstep (se 1 (by rfl) ⟨680561, by rfl⟩ : syracuseStep 907415 = 1361123) B1361123
theorem B1530035 : Blo 401768 1530035 := bstep (se 1 (by rfl) ⟨1147526, by rfl⟩ : syracuseStep 1530035 = 2295053) B2295053
theorem B1530049 : Blo 401768 1530049 := bstep (se 2 (by rfl) ⟨573768, by rfl⟩ : syracuseStep 1530049 = 1147537) B1147537
theorem B678091 : Blo 401768 678091 := bstep (se 1 (by rfl) ⟨508568, by rfl⟩ : syracuseStep 678091 = 1017137) B1017137
theorem B1038539 : Blo 401768 1038539 := bstep (se 1 (by rfl) ⟨778904, by rfl⟩ : syracuseStep 1038539 = 1557809) B1557809
theorem B645401 : Blo 401768 645401 := bstep (se 2 (by rfl) ⟨242025, by rfl⟩ : syracuseStep 645401 = 484051) B484051
theorem B907595 : Blo 401768 907595 := bstep (se 1 (by rfl) ⟨680696, by rfl⟩ : syracuseStep 907595 = 1361393) B1361393
theorem B678233 : Blo 401768 678233 := bstep (se 2 (by rfl) ⟨254337, by rfl⟩ : syracuseStep 678233 = 508675) B508675
theorem B1366361 : Blo 401768 1366361 := bstep (se 2 (by rfl) ⟨512385, by rfl⟩ : syracuseStep 1366361 = 1024771) B1024771
theorem B907649 : Blo 401768 907649 := bstep (se 2 (by rfl) ⟨340368, by rfl⟩ : syracuseStep 907649 = 680737) B680737
theorem B678361 : Blo 401768 678361 := bstep (se 2 (by rfl) ⟨254385, by rfl⟩ : syracuseStep 678361 = 508771) B508771
theorem B907865 : Blo 401768 907865 := bstep (se 2 (by rfl) ⟨340449, by rfl⟩ : syracuseStep 907865 = 680899) B680899
theorem B2775653 : Blo 401768 2775653 := bstep (se 4 (by rfl) ⟨260217, by rfl⟩ : syracuseStep 2775653 = 520435) B520435
theorem B973463 : Blo 401768 973463 := bstep (se 1 (by rfl) ⟨730097, by rfl⟩ : syracuseStep 973463 = 1460195) B1460195
theorem B907955 : Blo 401768 907955 := bstep (se 1 (by rfl) ⟨680966, by rfl⟩ : syracuseStep 907955 = 1361933) B1361933
theorem B907991 : Blo 401768 907991 := bstep (se 1 (by rfl) ⟨680993, by rfl⟩ : syracuseStep 907991 = 1361987) B1361987
theorem B2579293 : Blo 401768 2579293 := bstep (se 3 (by rfl) ⟨483617, by rfl⟩ : syracuseStep 2579293 = 967235) B967235
theorem B908171 : Blo 401768 908171 := bstep (se 1 (by rfl) ⟨681128, by rfl⟩ : syracuseStep 908171 = 1362257) B1362257
theorem B908225 : Blo 401768 908225 := bstep (se 2 (by rfl) ⟨340584, by rfl⟩ : syracuseStep 908225 = 681169) B681169
theorem B3267533 : Blo 401768 3267533 := bstep (se 3 (by rfl) ⟨612662, by rfl⟩ : syracuseStep 3267533 = 1225325) B1225325
theorem B646105 : Blo 401768 646105 := bstep (se 2 (by rfl) ⟨242289, by rfl⟩ : syracuseStep 646105 = 484579) B484579
theorem B678935 : Blo 401768 678935 := bstep (se 1 (by rfl) ⟨509201, by rfl⟩ : syracuseStep 678935 = 1018403) B1018403
theorem B1367063 : Blo 401768 1367063 := bstep (se 1 (by rfl) ⟨1025297, by rfl⟩ : syracuseStep 1367063 = 2050595) B2050595
theorem B679063 : Blo 401768 679063 := bstep (se 1 (by rfl) ⟨509297, by rfl⟩ : syracuseStep 679063 = 1018595) B1018595
theorem B908441 : Blo 401768 908441 := bstep (se 2 (by rfl) ⟨340665, by rfl⟩ : syracuseStep 908441 = 681331) B681331
theorem B908531 : Blo 401768 908531 := bstep (se 1 (by rfl) ⟨681398, by rfl⟩ : syracuseStep 908531 = 1362797) B1362797
theorem B908567 : Blo 401768 908567 := bstep (se 1 (by rfl) ⟨681425, by rfl⟩ : syracuseStep 908567 = 1362851) B1362851
theorem B974155 : Blo 401768 974155 := bstep (se 1 (by rfl) ⟨730616, by rfl⟩ : syracuseStep 974155 = 1461233) B1461233
theorem B875929 : Blo 401768 875929 := bstep (se 2 (by rfl) ⟨328473, by rfl⟩ : syracuseStep 875929 = 656947) B656947
theorem B908747 : Blo 401768 908747 := bstep (se 1 (by rfl) ⟨681560, by rfl⟩ : syracuseStep 908747 = 1363121) B1363121
theorem B908801 : Blo 401768 908801 := bstep (se 2 (by rfl) ⟨340800, by rfl⟩ : syracuseStep 908801 = 681601) B681601
theorem B7790093 : Blo 401768 7790093 := bstep (se 3 (by rfl) ⟨1460642, by rfl⟩ : syracuseStep 7790093 = 2921285) B2921285
theorem B1367603 : Blo 401768 1367603 := bstep (se 1 (by rfl) ⟨1025702, by rfl⟩ : syracuseStep 1367603 = 2051405) B2051405
theorem B974425 : Blo 401768 974425 := bstep (se 2 (by rfl) ⟨365409, by rfl⟩ : syracuseStep 974425 = 730819) B730819
theorem B4349533 : Blo 401768 4349533 := bstep (se 3 (by rfl) ⟨815537, by rfl⟩ : syracuseStep 4349533 = 1631075) B1631075
theorem B2449075 : Blo 401768 2449075 := bstep (se 1 (by rfl) ⟨1836806, by rfl⟩ : syracuseStep 2449075 = 3673613) B3673613
theorem B909017 : Blo 401768 909017 := bstep (se 2 (by rfl) ⟨340881, by rfl⟩ : syracuseStep 909017 = 681763) B681763
theorem B679691 : Blo 401768 679691 := bstep (se 1 (by rfl) ⟨509768, by rfl⟩ : syracuseStep 679691 = 1019537) B1019537
theorem B1171223 : Blo 401768 1171223 := bstep (se 1 (by rfl) ⟨878417, by rfl⟩ : syracuseStep 1171223 = 1756835) B1756835
theorem B909107 : Blo 401768 909107 := bstep (se 1 (by rfl) ⟨681830, by rfl⟩ : syracuseStep 909107 = 1363661) B1363661
theorem B1367873 : Blo 401768 1367873 := bstep (se 2 (by rfl) ⟨512952, by rfl⟩ : syracuseStep 1367873 = 1025905) B1025905
theorem B909143 : Blo 401768 909143 := bstep (se 1 (by rfl) ⟨681857, by rfl⟩ : syracuseStep 909143 = 1363715) B1363715
theorem B679819 : Blo 401768 679819 := bstep (se 1 (by rfl) ⟨509864, by rfl⟩ : syracuseStep 679819 = 1019729) B1019729
theorem B974771 : Blo 401768 974771 := bstep (se 1 (by rfl) ⟨731078, by rfl⟩ : syracuseStep 974771 = 1462157) B1462157
theorem B1728449 : Blo 401768 1728449 := bstep (se 2 (by rfl) ⟨648168, by rfl⟩ : syracuseStep 1728449 = 1296337) B1296337
theorem B3072005 : Blo 401768 3072005 := bstep (se 4 (by rfl) ⟨288000, by rfl⟩ : syracuseStep 3072005 = 576001) B576001
theorem B909323 : Blo 401768 909323 := bstep (se 1 (by rfl) ⟨681992, by rfl⟩ : syracuseStep 909323 = 1363985) B1363985
theorem B679961 : Blo 401768 679961 := bstep (se 2 (by rfl) ⟨254985, by rfl⟩ : syracuseStep 679961 = 509971) B509971
theorem B909377 : Blo 401768 909377 := bstep (se 2 (by rfl) ⟨341016, by rfl⟩ : syracuseStep 909377 = 682033) B682033
theorem B11952197 : Blo 401768 11952197 := bstep (se 4 (by rfl) ⟨1120518, by rfl⟩ : syracuseStep 11952197 = 2241037) B2241037
theorem B1531979 : Blo 401768 1531979 := bstep (se 1 (by rfl) ⟨1148984, by rfl⟩ : syracuseStep 1531979 = 2297969) B2297969
theorem B1531993 : Blo 401768 1531993 := bstep (se 2 (by rfl) ⟨574497, by rfl⟩ : syracuseStep 1531993 = 1148995) B1148995
theorem B5267587 : Blo 401768 5267587 := bstep (se 1 (by rfl) ⟨3950690, by rfl⟩ : syracuseStep 5267587 = 7901381) B7901381
theorem B18735245 : Blo 401768 18735245 := bstep (se 3 (by rfl) ⟨3512858, by rfl⟩ : syracuseStep 18735245 = 7025717) B7025717
theorem B680089 : Blo 401768 680089 := bstep (se 2 (by rfl) ⟨255033, by rfl⟩ : syracuseStep 680089 = 510067) B510067
theorem B26665237 : Blo 401768 26665237 := bstep (se 6 (by rfl) ⟨624966, by rfl⟩ : syracuseStep 26665237 = 1249933) B1249933
theorem B909593 : Blo 401768 909593 := bstep (se 2 (by rfl) ⟨341097, by rfl⟩ : syracuseStep 909593 = 682195) B682195
theorem B2580781 : Blo 401768 2580781 := bstep (se 3 (by rfl) ⟨483896, by rfl⟩ : syracuseStep 2580781 = 967793) B967793
theorem B1368413 : Blo 401768 1368413 := bstep (se 3 (by rfl) ⟨256577, by rfl⟩ : syracuseStep 1368413 = 513155) B513155
theorem B909683 : Blo 401768 909683 := bstep (se 1 (by rfl) ⟨682262, by rfl⟩ : syracuseStep 909683 = 1364525) B1364525
theorem B909719 : Blo 401768 909719 := bstep (se 1 (by rfl) ⟨682289, by rfl⟩ : syracuseStep 909719 = 1364579) B1364579
theorem B909899 : Blo 401768 909899 := bstep (se 1 (by rfl) ⟨682424, by rfl⟩ : syracuseStep 909899 = 1364849) B1364849
theorem B909953 : Blo 401768 909953 := bstep (se 2 (by rfl) ⟨341232, by rfl⟩ : syracuseStep 909953 = 682465) B682465
theorem B680663 : Blo 401768 680663 := bstep (se 1 (by rfl) ⟨510497, by rfl⟩ : syracuseStep 680663 = 1020995) B1020995
theorem B2908973 : Blo 401768 2908973 := bstep (se 3 (by rfl) ⟨545432, by rfl⟩ : syracuseStep 2908973 = 1090865) B1090865
theorem B680791 : Blo 401768 680791 := bstep (se 1 (by rfl) ⟨510593, by rfl⟩ : syracuseStep 680791 = 1021187) B1021187
theorem B910169 : Blo 401768 910169 := bstep (se 2 (by rfl) ⟨341313, by rfl⟩ : syracuseStep 910169 = 682627) B682627
theorem B910259 : Blo 401768 910259 := bstep (se 1 (by rfl) ⟨682694, by rfl⟩ : syracuseStep 910259 = 1365389) B1365389
theorem B910295 : Blo 401768 910295 := bstep (se 1 (by rfl) ⟨682721, by rfl⟩ : syracuseStep 910295 = 1365443) B1365443
theorem B1532951 : Blo 401768 1532951 := bstep (se 1 (by rfl) ⟨1149713, by rfl⟩ : syracuseStep 1532951 = 2299427) B2299427
theorem B910475 : Blo 401768 910475 := bstep (se 1 (by rfl) ⟨682856, by rfl⟩ : syracuseStep 910475 = 1365713) B1365713
theorem B910529 : Blo 401768 910529 := bstep (se 2 (by rfl) ⟨341448, by rfl⟩ : syracuseStep 910529 = 682897) B682897
theorem B910745 : Blo 401768 910745 := bstep (se 2 (by rfl) ⟨341529, by rfl⟩ : syracuseStep 910745 = 683059) B683059
theorem B452011 : Blo 401768 452011 := bstep (se 1 (by rfl) ⟨339008, by rfl⟩ : syracuseStep 452011 = 678017) B678017
theorem B681419 : Blo 401768 681419 := bstep (se 1 (by rfl) ⟨511064, by rfl⟩ : syracuseStep 681419 = 1022129) B1022129
theorem B910835 : Blo 401768 910835 := bstep (se 1 (by rfl) ⟨683126, by rfl⟩ : syracuseStep 910835 = 1366253) B1366253
theorem B452119 : Blo 401768 452119 := bstep (se 1 (by rfl) ⟨339089, by rfl⟩ : syracuseStep 452119 = 678179) B678179
theorem B910871 : Blo 401768 910871 := bstep (se 1 (by rfl) ⟨683153, by rfl⟩ : syracuseStep 910871 = 1366307) B1366307
theorem B681547 : Blo 401768 681547 := bstep (se 1 (by rfl) ⟨511160, by rfl⟩ : syracuseStep 681547 = 1022321) B1022321
theorem B1730123 : Blo 401768 1730123 := bstep (se 1 (by rfl) ⟨1297592, by rfl⟩ : syracuseStep 1730123 = 2595185) B2595185
theorem B452299 : Blo 401768 452299 := bstep (se 1 (by rfl) ⟨339224, by rfl⟩ : syracuseStep 452299 = 678449) B678449
theorem B911051 : Blo 401768 911051 := bstep (se 1 (by rfl) ⟨683288, by rfl⟩ : syracuseStep 911051 = 1366577) B1366577
theorem B681689 : Blo 401768 681689 := bstep (se 2 (by rfl) ⟨255633, by rfl⟩ : syracuseStep 681689 = 511267) B511267
theorem B911105 : Blo 401768 911105 := bstep (se 2 (by rfl) ⟨341664, by rfl⟩ : syracuseStep 911105 = 683329) B683329
theorem B452407 : Blo 401768 452407 := bstep (se 1 (by rfl) ⟨339305, by rfl⟩ : syracuseStep 452407 = 678611) B678611
theorem B681817 : Blo 401768 681817 := bstep (se 2 (by rfl) ⟨255681, by rfl⟩ : syracuseStep 681817 = 511363) B511363
theorem B911321 : Blo 401768 911321 := bstep (se 2 (by rfl) ⟨341745, by rfl⟩ : syracuseStep 911321 = 683491) B683491
theorem B452587 : Blo 401768 452587 := bstep (se 1 (by rfl) ⟨339440, by rfl⟩ : syracuseStep 452587 = 678881) B678881
theorem B911411 : Blo 401768 911411 := bstep (se 1 (by rfl) ⟨683558, by rfl⟩ : syracuseStep 911411 = 1367117) B1367117
theorem B452695 : Blo 401768 452695 := bstep (se 1 (by rfl) ⟨339521, by rfl⟩ : syracuseStep 452695 = 679043) B679043
theorem B911447 : Blo 401768 911447 := bstep (se 1 (by rfl) ⟨683585, by rfl⟩ : syracuseStep 911447 = 1367171) B1367171
theorem B1534211 : Blo 401768 1534211 := bstep (se 1 (by rfl) ⟨1150658, by rfl⟩ : syracuseStep 1534211 = 2301317) B2301317
theorem B452875 : Blo 401768 452875 := bstep (se 1 (by rfl) ⟨339656, by rfl⟩ : syracuseStep 452875 = 679313) B679313
theorem B911627 : Blo 401768 911627 := bstep (se 1 (by rfl) ⟨683720, by rfl⟩ : syracuseStep 911627 = 1367441) B1367441
theorem B911681 : Blo 401768 911681 := bstep (se 2 (by rfl) ⟨341880, by rfl⟩ : syracuseStep 911681 = 683761) B683761
theorem B1730909 : Blo 401768 1730909 := bstep (se 3 (by rfl) ⟨324545, by rfl⟩ : syracuseStep 1730909 = 649091) B649091
theorem B452983 : Blo 401768 452983 := bstep (se 1 (by rfl) ⟨339737, by rfl⟩ : syracuseStep 452983 = 679475) B679475
theorem B3074435 : Blo 401768 3074435 := bstep (se 1 (by rfl) ⟨2305826, by rfl⟩ : syracuseStep 3074435 = 4611653) B4611653
theorem B682391 : Blo 401768 682391 := bstep (se 1 (by rfl) ⟨511793, by rfl⟩ : syracuseStep 682391 = 1023587) B1023587
theorem B3434957 : Blo 401768 3434957 := bstep (se 3 (by rfl) ⟨644054, by rfl⟩ : syracuseStep 3434957 = 1288109) B1288109
theorem B682519 : Blo 401768 682519 := bstep (se 1 (by rfl) ⟨511889, by rfl⟩ : syracuseStep 682519 = 1023779) B1023779
theorem B911897 : Blo 401768 911897 := bstep (se 2 (by rfl) ⟨341961, by rfl⟩ : syracuseStep 911897 = 683923) B683923
theorem B453163 : Blo 401768 453163 := bstep (se 1 (by rfl) ⟨339872, by rfl⟩ : syracuseStep 453163 = 679745) B679745
theorem B911987 : Blo 401768 911987 := bstep (se 1 (by rfl) ⟨683990, by rfl⟩ : syracuseStep 911987 = 1367981) B1367981
theorem B453271 : Blo 401768 453271 := bstep (se 1 (by rfl) ⟨339953, by rfl⟩ : syracuseStep 453271 = 679907) B679907
theorem B912023 : Blo 401768 912023 := bstep (se 1 (by rfl) ⟨684017, by rfl⟩ : syracuseStep 912023 = 1368035) B1368035
theorem B486155 : Blo 401768 486155 := bstep (se 1 (by rfl) ⟨364616, by rfl⟩ : syracuseStep 486155 = 729233) B729233
theorem B453451 : Blo 401768 453451 := bstep (se 1 (by rfl) ⟨340088, by rfl⟩ : syracuseStep 453451 = 680177) B680177
theorem B912203 : Blo 401768 912203 := bstep (se 1 (by rfl) ⟨684152, by rfl⟩ : syracuseStep 912203 = 1368305) B1368305
theorem B912257 : Blo 401768 912257 := bstep (se 2 (by rfl) ⟨342096, by rfl⟩ : syracuseStep 912257 = 684193) B684193
theorem B453559 : Blo 401768 453559 := bstep (se 1 (by rfl) ⟨340169, by rfl⟩ : syracuseStep 453559 = 680339) B680339
theorem B912473 : Blo 401768 912473 := bstep (se 2 (by rfl) ⟨342177, by rfl⟩ : syracuseStep 912473 = 684355) B684355
theorem B4582493 : Blo 401768 4582493 := bstep (se 3 (by rfl) ⟨859217, by rfl⟩ : syracuseStep 4582493 = 1718435) B1718435
theorem B453739 : Blo 401768 453739 := bstep (se 1 (by rfl) ⟨340304, by rfl⟩ : syracuseStep 453739 = 680609) B680609
theorem B683147 : Blo 401768 683147 := bstep (se 1 (by rfl) ⟨512360, by rfl⟩ : syracuseStep 683147 = 1024721) B1024721
theorem B912563 : Blo 401768 912563 := bstep (se 1 (by rfl) ⟨684422, by rfl⟩ : syracuseStep 912563 = 1368845) B1368845
theorem B453847 : Blo 401768 453847 := bstep (se 1 (by rfl) ⟨340385, by rfl⟩ : syracuseStep 453847 = 680771) B680771
theorem B912599 : Blo 401768 912599 := bstep (se 1 (by rfl) ⟨684449, by rfl⟩ : syracuseStep 912599 = 1368899) B1368899
theorem B683275 : Blo 401768 683275 := bstep (se 1 (by rfl) ⟨512456, by rfl⟩ : syracuseStep 683275 = 1024913) B1024913
theorem B13036913 : Blo 401768 13036913 := bstep (se 2 (by rfl) ⟨4888842, by rfl⟩ : syracuseStep 13036913 = 9777685) B9777685
theorem B454027 : Blo 401768 454027 := bstep (se 1 (by rfl) ⟨340520, by rfl⟩ : syracuseStep 454027 = 681041) B681041
theorem B912779 : Blo 401768 912779 := bstep (se 1 (by rfl) ⟨684584, by rfl⟩ : syracuseStep 912779 = 1369169) B1369169
theorem B683417 : Blo 401768 683417 := bstep (se 2 (by rfl) ⟨256281, by rfl⟩ : syracuseStep 683417 = 512563) B512563
theorem B912833 : Blo 401768 912833 := bstep (se 2 (by rfl) ⟨342312, by rfl⟩ : syracuseStep 912833 = 684625) B684625
theorem B454135 : Blo 401768 454135 := bstep (se 1 (by rfl) ⟨340601, by rfl⟩ : syracuseStep 454135 = 681203) B681203
theorem B683545 : Blo 401768 683545 := bstep (se 2 (by rfl) ⟨256329, by rfl⟩ : syracuseStep 683545 = 512659) B512659
theorem B1732241 : Blo 401768 1732241 := bstep (se 2 (by rfl) ⟨649590, by rfl⟩ : syracuseStep 1732241 = 1299181) B1299181
theorem B454315 : Blo 401768 454315 := bstep (se 1 (by rfl) ⟨340736, by rfl⟩ : syracuseStep 454315 = 681473) B681473
theorem B1994419 : Blo 401768 1994419 := bstep (se 1 (by rfl) ⟨1495814, by rfl⟩ : syracuseStep 1994419 = 2991629) B2991629
theorem B454423 : Blo 401768 454423 := bstep (se 1 (by rfl) ⟨340817, by rfl⟩ : syracuseStep 454423 = 681635) B681635
theorem B454603 : Blo 401768 454603 := bstep (se 1 (by rfl) ⟨340952, by rfl⟩ : syracuseStep 454603 = 681905) B681905
theorem B454711 : Blo 401768 454711 := bstep (se 1 (by rfl) ⟨341033, by rfl⟩ : syracuseStep 454711 = 682067) B682067
theorem B684119 : Blo 401768 684119 := bstep (se 1 (by rfl) ⟨513089, by rfl⟩ : syracuseStep 684119 = 1026179) B1026179
theorem B4124803 : Blo 401768 4124803 := bstep (se 1 (by rfl) ⟨3093602, by rfl⟩ : syracuseStep 4124803 = 6187205) B6187205
theorem B684247 : Blo 401768 684247 := bstep (se 1 (by rfl) ⟨513185, by rfl⟩ : syracuseStep 684247 = 1026371) B1026371
theorem B815321 : Blo 401768 815321 := bstep (se 2 (by rfl) ⟨305745, by rfl⟩ : syracuseStep 815321 = 611491) B611491
theorem B454891 : Blo 401768 454891 := bstep (se 1 (by rfl) ⟨341168, by rfl⟩ : syracuseStep 454891 = 682337) B682337
theorem B454999 : Blo 401768 454999 := bstep (se 1 (by rfl) ⟨341249, by rfl⟩ : syracuseStep 454999 = 682499) B682499
theorem B455179 : Blo 401768 455179 := bstep (se 1 (by rfl) ⟨341384, by rfl⟩ : syracuseStep 455179 = 682769) B682769
theorem B455287 : Blo 401768 455287 := bstep (se 1 (by rfl) ⟨341465, by rfl⟩ : syracuseStep 455287 = 682931) B682931
theorem B455467 : Blo 401768 455467 := bstep (se 1 (by rfl) ⟨341600, by rfl⟩ : syracuseStep 455467 = 683201) B683201
theorem B455575 : Blo 401768 455575 := bstep (se 1 (by rfl) ⟨341681, by rfl⟩ : syracuseStep 455575 = 683363) B683363
theorem B1307585 : Blo 401768 1307585 := bstep (se 2 (by rfl) ⟨490344, by rfl⟩ : syracuseStep 1307585 = 980689) B980689
theorem B455755 : Blo 401768 455755 := bstep (se 1 (by rfl) ⟨341816, by rfl⟩ : syracuseStep 455755 = 683633) B683633
theorem B2946179 : Blo 401768 2946179 := bstep (se 1 (by rfl) ⟨2209634, by rfl⟩ : syracuseStep 2946179 = 4419269) B4419269
theorem B455863 : Blo 401768 455863 := bstep (se 1 (by rfl) ⟨341897, by rfl⟩ : syracuseStep 455863 = 683795) B683795
theorem B1537325 : Blo 401768 1537325 := bstep (se 3 (by rfl) ⟨288248, by rfl⟩ : syracuseStep 1537325 = 576497) B576497
theorem B980299 : Blo 401768 980299 := bstep (se 1 (by rfl) ⟨735224, by rfl⟩ : syracuseStep 980299 = 1470449) B1470449
theorem B456043 : Blo 401768 456043 := bstep (se 1 (by rfl) ⟨342032, by rfl⟩ : syracuseStep 456043 = 684065) B684065
theorem B456151 : Blo 401768 456151 := bstep (se 1 (by rfl) ⟨342113, by rfl⟩ : syracuseStep 456151 = 684227) B684227
theorem B456331 : Blo 401768 456331 := bstep (se 1 (by rfl) ⟨342248, by rfl⟩ : syracuseStep 456331 = 684497) B684497
theorem B3077837 : Blo 401768 3077837 := bstep (se 3 (by rfl) ⟨577094, by rfl⟩ : syracuseStep 3077837 = 1154189) B1154189
theorem B456439 : Blo 401768 456439 := bstep (se 1 (by rfl) ⟨342329, by rfl⟩ : syracuseStep 456439 = 684659) B684659
theorem B1144793 : Blo 401768 1144793 := bstep (se 2 (by rfl) ⟨429297, by rfl⟩ : syracuseStep 1144793 = 858595) B858595
theorem B1538099 : Blo 401768 1538099 := bstep (se 1 (by rfl) ⟨1153574, by rfl⟩ : syracuseStep 1538099 = 2307149) B2307149
theorem B1833025 : Blo 401768 1833025 := bstep (se 2 (by rfl) ⟨687384, by rfl⟩ : syracuseStep 1833025 = 1374769) B1374769
theorem B22181957 : Blo 401768 22181957 := bstep (se 4 (by rfl) ⟨2079558, by rfl⟩ : syracuseStep 22181957 = 4159117) B4159117
theorem B3078323 : Blo 401768 3078323 := bstep (se 1 (by rfl) ⟨2308742, by rfl⟩ : syracuseStep 3078323 = 4617485) B4617485
theorem B2750851 : Blo 401768 2750851 := bstep (se 1 (by rfl) ⟨2063138, by rfl⟩ : syracuseStep 2750851 = 4126277) B4126277
theorem B1636787 : Blo 401768 1636787 := bstep (se 1 (by rfl) ⟨1227590, by rfl⟩ : syracuseStep 1636787 = 2455181) B2455181
theorem B7436893 : Blo 401768 7436893 := bstep (se 3 (by rfl) ⟨1394417, by rfl⟩ : syracuseStep 7436893 = 2788835) B2788835
theorem B3668753 : Blo 401768 3668753 := bstep (se 2 (by rfl) ⟨1375782, by rfl⟩ : syracuseStep 3668753 = 2751565) B2751565
theorem B3373841 : Blo 401768 3373841 := bstep (se 2 (by rfl) ⟨1265190, by rfl⟩ : syracuseStep 3373841 = 2530381) B2530381
theorem B818263 : Blo 401768 818263 := bstep (se 1 (by rfl) ⟨613697, by rfl⟩ : syracuseStep 818263 = 1227395) B1227395
theorem B2292887 : Blo 401768 2292887 := bstep (se 1 (by rfl) ⟨1719665, by rfl⟩ : syracuseStep 2292887 = 3439331) B3439331
theorem B785857 : Blo 401768 785857 := bstep (se 2 (by rfl) ⟨294696, by rfl⟩ : syracuseStep 785857 = 589393) B589393
theorem B687577 : Blo 401768 687577 := bstep (se 2 (by rfl) ⟨257841, by rfl⟩ : syracuseStep 687577 = 515683) B515683
theorem B1932761 : Blo 401768 1932761 := bstep (se 2 (by rfl) ⟨724785, by rfl⟩ : syracuseStep 1932761 = 1449571) B1449571
theorem B1539587 : Blo 401768 1539587 := bstep (se 1 (by rfl) ⟨1154690, by rfl⟩ : syracuseStep 1539587 = 2309381) B2309381
theorem B2883077 : Blo 401768 2883077 := bstep (se 4 (by rfl) ⟨270288, by rfl⟩ : syracuseStep 2883077 = 540577) B540577
theorem B1146433 : Blo 401768 1146433 := bstep (se 2 (by rfl) ⟨429912, by rfl⟩ : syracuseStep 1146433 = 859825) B859825
theorem B3079781 : Blo 401768 3079781 := bstep (se 4 (by rfl) ⟨288729, by rfl⟩ : syracuseStep 3079781 = 577459) B577459
theorem B458603 : Blo 401768 458603 := bstep (se 1 (by rfl) ⟨343952, by rfl⟩ : syracuseStep 458603 = 687905) B687905
theorem B1540043 : Blo 401768 1540043 := bstep (se 1 (by rfl) ⟨1155032, by rfl⟩ : syracuseStep 1540043 = 2310065) B2310065
theorem B1146923 : Blo 401768 1146923 := bstep (se 1 (by rfl) ⟨860192, by rfl⟩ : syracuseStep 1146923 = 1720385) B1720385
theorem B35553649 : Blo 401768 35553649 := bstep (se 2 (by rfl) ⟨13332618, by rfl⟩ : syracuseStep 35553649 = 26665237) B26665237
theorem B1933703 : Blo 401768 1933703 := bstep (se 1 (by rfl) ⟨1450277, by rfl⟩ : syracuseStep 1933703 = 2900555) B2900555
theorem B3441041 : Blo 401768 3441041 := bstep (se 2 (by rfl) ⟨1290390, by rfl⟩ : syracuseStep 3441041 = 2580781) B2580781
theorem B3670721 : Blo 401768 3670721 := bstep (se 2 (by rfl) ⟨1376520, by rfl⟩ : syracuseStep 3670721 = 2753041) B2753041
theorem B4588325 : Blo 401768 4588325 := bstep (se 4 (by rfl) ⟨430155, by rfl⟩ : syracuseStep 4588325 = 860311) B860311
theorem B1147709 : Blo 401768 1147709 := bstep (se 3 (by rfl) ⟨215195, by rfl⟩ : syracuseStep 1147709 = 430391) B430391
theorem B3277721 : Blo 401768 3277721 := bstep (se 2 (by rfl) ⟨1229145, by rfl⟩ : syracuseStep 3277721 = 2458291) B2458291
theorem B11076533 : Blo 401768 11076533 := bstep (se 5 (by rfl) ⟨519212, by rfl⟩ : syracuseStep 11076533 = 1038425) B1038425
theorem B3081239 : Blo 401768 3081239 := bstep (se 1 (by rfl) ⟨2310929, by rfl⟩ : syracuseStep 3081239 = 4621859) B4621859
theorem B1148039 : Blo 401768 1148039 := bstep (se 1 (by rfl) ⟨861029, by rfl⟩ : syracuseStep 1148039 = 1722059) B1722059
theorem B2917853 : Blo 401768 2917853 := bstep (se 3 (by rfl) ⟨547097, by rfl⟩ : syracuseStep 2917853 = 1094195) B1094195
theorem B1017431 : Blo 401768 1017431 := bstep (se 1 (by rfl) ⟨763073, by rfl⟩ : syracuseStep 1017431 = 1526147) B1526147
theorem B1935085 : Blo 401768 1935085 := bstep (se 3 (by rfl) ⟨362828, by rfl⟩ : syracuseStep 1935085 = 725657) B725657
theorem B2328335 : Blo 401768 2328335 := bstep (se 1 (by rfl) ⟨1746251, by rfl⟩ : syracuseStep 2328335 = 3492503) B3492503
theorem B1017643 : Blo 401768 1017643 := bstep (se 1 (by rfl) ⟨763232, by rfl⟩ : syracuseStep 1017643 = 1526465) B1526465
theorem B821035 : Blo 401768 821035 := bstep (se 1 (by rfl) ⟨615776, by rfl⟩ : syracuseStep 821035 = 1231553) B1231553
theorem B1017785 : Blo 401768 1017785 := bstep (se 2 (by rfl) ⟨381669, by rfl⟩ : syracuseStep 1017785 = 763339) B763339
theorem B5802029 : Blo 401768 5802029 := bstep (se 3 (by rfl) ⟨1087880, by rfl⟩ : syracuseStep 5802029 = 2175761) B2175761
theorem B5507345 : Blo 401768 5507345 := bstep (se 2 (by rfl) ⟨2065254, by rfl⟩ : syracuseStep 5507345 = 4130509) B4130509
theorem B2591185 : Blo 401768 2591185 := bstep (se 2 (by rfl) ⟨971694, by rfl⟩ : syracuseStep 2591185 = 1943389) B1943389
theorem B11045443 : Blo 401768 11045443 := bstep (se 1 (by rfl) ⟨8284082, by rfl⟩ : syracuseStep 11045443 = 16568165) B16568165
theorem B1149815 : Blo 401768 1149815 := bstep (se 1 (by rfl) ⟨862361, by rfl⟩ : syracuseStep 1149815 = 1724723) B1724723
theorem B1018777 : Blo 401768 1018777 := bstep (se 2 (by rfl) ⟨382041, by rfl⟩ : syracuseStep 1018777 = 764083) B764083
theorem B1018939 : Blo 401768 1018939 := bstep (se 1 (by rfl) ⟨764204, by rfl⟩ : syracuseStep 1018939 = 1528409) B1528409
theorem B2034881 : Blo 401768 2034881 := bstep (se 2 (by rfl) ⟨763080, by rfl⟩ : syracuseStep 2034881 = 1526161) B1526161
theorem B1019081 : Blo 401768 1019081 := bstep (se 2 (by rfl) ⟨382155, by rfl⟩ : syracuseStep 1019081 = 764311) B764311
theorem B1019425 : Blo 401768 1019425 := bstep (se 2 (by rfl) ⟨382284, by rfl⟩ : syracuseStep 1019425 = 764569) B764569
theorem B921223 : Blo 401768 921223 := bstep (se 1 (by rfl) ⟨690917, by rfl⟩ : syracuseStep 921223 = 1381835) B1381835
theorem B1150807 : Blo 401768 1150807 := bstep (se 1 (by rfl) ⟨863105, by rfl⟩ : syracuseStep 1150807 = 1726211) B1726211
theorem B2461529 : Blo 401768 2461529 := bstep (se 2 (by rfl) ⟨923073, by rfl⟩ : syracuseStep 2461529 = 1846147) B1846147
theorem B2101277 : Blo 401768 2101277 := bstep (se 3 (by rfl) ⟨393989, by rfl⟩ : syracuseStep 2101277 = 787979) B787979
theorem B1020023 : Blo 401768 1020023 := bstep (se 1 (by rfl) ⟨765017, by rfl⟩ : syracuseStep 1020023 = 1530035) B1530035
theorem B430267 : Blo 401768 430267 := bstep (se 1 (by rfl) ⟨322700, by rfl⟩ : syracuseStep 430267 = 645401) B645401
theorem B15470837 : Blo 401768 15470837 := bstep (se 5 (by rfl) ⟨725195, by rfl⟩ : syracuseStep 15470837 = 1450391) B1450391
theorem B2036177 : Blo 401768 2036177 := bstep (se 2 (by rfl) ⟨763566, by rfl⟩ : syracuseStep 2036177 = 1527133) B1527133
theorem B11637269 : Blo 401768 11637269 := bstep (se 6 (by rfl) ⟨272748, by rfl⟩ : syracuseStep 11637269 = 545497) B545497
theorem B1381121 : Blo 401768 1381121 := bstep (se 2 (by rfl) ⟨517920, by rfl⟩ : syracuseStep 1381121 = 1035841) B1035841
theorem B9966341 : Blo 401768 9966341 := bstep (se 4 (by rfl) ⟨934344, by rfl⟩ : syracuseStep 9966341 = 1868689) B1868689
theorem B2659225 : Blo 401768 2659225 := bstep (se 2 (by rfl) ⟨997209, by rfl⟩ : syracuseStep 2659225 = 1994419) B1994419
theorem B1152299 : Blo 401768 1152299 := bstep (se 1 (by rfl) ⟨864224, by rfl⟩ : syracuseStep 1152299 = 1728449) B1728449
theorem B7968131 : Blo 401768 7968131 := bstep (se 1 (by rfl) ⟨5976098, by rfl⟩ : syracuseStep 7968131 = 11952197) B11952197
theorem B1021319 : Blo 401768 1021319 := bstep (se 1 (by rfl) ⟨765989, by rfl⟩ : syracuseStep 1021319 = 1531979) B1531979
theorem B12490163 : Blo 401768 12490163 := bstep (se 1 (by rfl) ⟨9367622, by rfl⟩ : syracuseStep 12490163 = 18735245) B18735245
theorem B1021369 : Blo 401768 1021369 := bstep (se 2 (by rfl) ⟨383013, by rfl⟩ : syracuseStep 1021369 = 766027) B766027
theorem B923081 : Blo 401768 923081 := bstep (se 2 (by rfl) ⟨346155, by rfl⟩ : syracuseStep 923081 = 692311) B692311
theorem B1939315 : Blo 401768 1939315 := bstep (se 1 (by rfl) ⟨1454486, by rfl⟩ : syracuseStep 1939315 = 2908973) B2908973
theorem B1021967 : Blo 401768 1021967 := bstep (se 1 (by rfl) ⟨766475, by rfl⟩ : syracuseStep 1021967 = 1532951) B1532951
theorem B1022209 : Blo 401768 1022209 := bstep (se 2 (by rfl) ⟨383328, by rfl⟩ : syracuseStep 1022209 = 766657) B766657
theorem B924023 : Blo 401768 924023 := bstep (se 1 (by rfl) ⟨693017, by rfl⟩ : syracuseStep 924023 = 1386035) B1386035
theorem B1153415 : Blo 401768 1153415 := bstep (se 1 (by rfl) ⟨865061, by rfl⟩ : syracuseStep 1153415 = 1730123) B1730123
theorem B2038283 : Blo 401768 2038283 := bstep (se 1 (by rfl) ⟨1528712, by rfl⟩ : syracuseStep 2038283 = 3057425) B3057425
theorem B1153597 : Blo 401768 1153597 := bstep (se 3 (by rfl) ⟨216299, by rfl⟩ : syracuseStep 1153597 = 432599) B432599
theorem B2038445 : Blo 401768 2038445 := bstep (se 3 (by rfl) ⟨382208, by rfl⟩ : syracuseStep 2038445 = 764417) B764417
theorem B1022665 : Blo 401768 1022665 := bstep (se 2 (by rfl) ⟨383499, by rfl⟩ : syracuseStep 1022665 = 766999) B766999
theorem B1383227 : Blo 401768 1383227 := bstep (se 1 (by rfl) ⟨1037420, by rfl⟩ : syracuseStep 1383227 = 2074841) B2074841
theorem B1022807 : Blo 401768 1022807 := bstep (se 1 (by rfl) ⟨767105, by rfl⟩ : syracuseStep 1022807 = 1534211) B1534211
theorem B1153939 : Blo 401768 1153939 := bstep (se 1 (by rfl) ⟨865454, by rfl⟩ : syracuseStep 1153939 = 1730909) B1730909
theorem B859081 : Blo 401768 859081 := bstep (se 2 (by rfl) ⟨322155, by rfl⟩ : syracuseStep 859081 = 644311) B644311
theorem B15735869 : Blo 401768 15735869 := bstep (se 3 (by rfl) ⟨2950475, by rfl⟩ : syracuseStep 15735869 = 5900951) B5900951
theorem B2595901 : Blo 401768 2595901 := bstep (se 3 (by rfl) ⟨486731, by rfl⟩ : syracuseStep 2595901 = 973463) B973463
theorem B1973335 : Blo 401768 1973335 := bstep (se 1 (by rfl) ⟨1480001, by rfl⟩ : syracuseStep 1973335 = 2960003) B2960003
theorem B3054995 : Blo 401768 3054995 := bstep (se 1 (by rfl) ⟨2291246, by rfl⟩ : syracuseStep 3054995 = 4582493) B4582493
theorem B4660739 : Blo 401768 4660739 := bstep (se 1 (by rfl) ⟨3495554, by rfl⟩ : syracuseStep 4660739 = 6991109) B6991109
theorem B8691275 : Blo 401768 8691275 := bstep (se 1 (by rfl) ⟨6518456, by rfl⟩ : syracuseStep 8691275 = 13036913) B13036913
theorem B1154827 : Blo 401768 1154827 := bstep (se 1 (by rfl) ⟨866120, by rfl⟩ : syracuseStep 1154827 = 1732241) B1732241
theorem B2040065 : Blo 401768 2040065 := bstep (se 2 (by rfl) ⟨765024, by rfl⟩ : syracuseStep 2040065 = 1530049) B1530049
theorem B1155329 : Blo 401768 1155329 := bstep (se 2 (by rfl) ⟨433248, by rfl⟩ : syracuseStep 1155329 = 866497) B866497
theorem B729479 : Blo 401768 729479 := bstep (se 1 (by rfl) ⟨547109, by rfl⟩ : syracuseStep 729479 = 1094219) B1094219
theorem B401799 : Blo 401768 401799 := bstep (se 1 (by rfl) ⟨301349, by rfl⟩ : syracuseStep 401799 = 602699) B602699
theorem B2302343 : Blo 401768 2302343 := bstep (se 1 (by rfl) ⟨1726757, by rfl⟩ : syracuseStep 2302343 = 3453515) B3453515
theorem B401807 : Blo 401768 401807 := bstep (se 1 (by rfl) ⟨301355, by rfl⟩ : syracuseStep 401807 = 602711) B602711
theorem B401851 : Blo 401768 401851 := bstep (se 1 (by rfl) ⟨301388, by rfl⟩ : syracuseStep 401851 = 602777) B602777
theorem B401927 : Blo 401768 401927 := bstep (se 1 (by rfl) ⟨301445, by rfl⟩ : syracuseStep 401927 = 602891) B602891
theorem B401935 : Blo 401768 401935 := bstep (se 1 (by rfl) ⟨301451, by rfl⟩ : syracuseStep 401935 = 602903) B602903
theorem B401979 : Blo 401768 401979 := bstep (se 1 (by rfl) ⟨301484, by rfl⟩ : syracuseStep 401979 = 602969) B602969
theorem B1516099 : Blo 401768 1516099 := bstep (se 1 (by rfl) ⟨1137074, by rfl⟩ : syracuseStep 1516099 = 2274149) B2274149
theorem B402055 : Blo 401768 402055 := bstep (se 1 (by rfl) ⟨301541, by rfl⟩ : syracuseStep 402055 = 603083) B603083
theorem B860807 : Blo 401768 860807 := bstep (se 1 (by rfl) ⟨645605, by rfl⟩ : syracuseStep 860807 = 1291211) B1291211
theorem B402063 : Blo 401768 402063 := bstep (se 1 (by rfl) ⟨301547, by rfl⟩ : syracuseStep 402063 = 603095) B603095
theorem B402107 : Blo 401768 402107 := bstep (se 1 (by rfl) ⟨301580, by rfl⟩ : syracuseStep 402107 = 603161) B603161
theorem B402183 : Blo 401768 402183 := bstep (se 1 (by rfl) ⟨301637, by rfl⟩ : syracuseStep 402183 = 603275) B603275
theorem B402191 : Blo 401768 402191 := bstep (se 1 (by rfl) ⟨301643, by rfl⟩ : syracuseStep 402191 = 603287) B603287
theorem B402235 : Blo 401768 402235 := bstep (se 1 (by rfl) ⟨301676, by rfl⟩ : syracuseStep 402235 = 603353) B603353
theorem B1024883 : Blo 401768 1024883 := bstep (se 1 (by rfl) ⟨768662, by rfl⟩ : syracuseStep 1024883 = 1537325) B1537325
theorem B402311 : Blo 401768 402311 := bstep (se 1 (by rfl) ⟨301733, by rfl⟩ : syracuseStep 402311 = 603467) B603467
theorem B402319 : Blo 401768 402319 := bstep (se 1 (by rfl) ⟨301739, by rfl⟩ : syracuseStep 402319 = 603479) B603479
theorem B402363 : Blo 401768 402363 := bstep (se 1 (by rfl) ⟨301772, by rfl⟩ : syracuseStep 402363 = 603545) B603545
theorem B402439 : Blo 401768 402439 := bstep (se 1 (by rfl) ⟨301829, by rfl⟩ : syracuseStep 402439 = 603659) B603659
theorem B402447 : Blo 401768 402447 := bstep (se 1 (by rfl) ⟨301835, by rfl⟩ : syracuseStep 402447 = 603671) B603671
theorem B2040875 : Blo 401768 2040875 := bstep (se 1 (by rfl) ⟨1530656, by rfl⟩ : syracuseStep 2040875 = 3061313) B3061313
theorem B402491 : Blo 401768 402491 := bstep (se 1 (by rfl) ⟨301868, by rfl⟩ : syracuseStep 402491 = 603737) B603737
theorem B6628439 : Blo 401768 6628439 := bstep (se 1 (by rfl) ⟨4971329, by rfl⟩ : syracuseStep 6628439 = 9942659) B9942659
theorem B4891765 : Blo 401768 4891765 := bstep (se 5 (by rfl) ⟨229301, by rfl⟩ : syracuseStep 4891765 = 458603) B458603
theorem B402567 : Blo 401768 402567 := bstep (se 1 (by rfl) ⟨301925, by rfl⟩ : syracuseStep 402567 = 603851) B603851
theorem B402575 : Blo 401768 402575 := bstep (se 1 (by rfl) ⟨301931, by rfl⟩ : syracuseStep 402575 = 603863) B603863
theorem B402619 : Blo 401768 402619 := bstep (se 1 (by rfl) ⟨301964, by rfl⟩ : syracuseStep 402619 = 603929) B603929
theorem B5154029 : Blo 401768 5154029 := bstep (se 3 (by rfl) ⟨966380, by rfl⟩ : syracuseStep 5154029 = 1932761) B1932761
theorem B402695 : Blo 401768 402695 := bstep (se 1 (by rfl) ⟨302021, by rfl⟩ : syracuseStep 402695 = 604043) B604043
theorem B402703 : Blo 401768 402703 := bstep (se 1 (by rfl) ⟨302027, by rfl⟩ : syracuseStep 402703 = 604055) B604055
theorem B861473 : Blo 401768 861473 := bstep (se 2 (by rfl) ⟨323052, by rfl⟩ : syracuseStep 861473 = 646105) B646105
theorem B763195 : Blo 401768 763195 := bstep (se 1 (by rfl) ⟨572396, by rfl⟩ : syracuseStep 763195 = 1144793) B1144793
theorem B402747 : Blo 401768 402747 := bstep (se 1 (by rfl) ⟨302060, by rfl⟩ : syracuseStep 402747 = 604121) B604121
theorem B1025399 : Blo 401768 1025399 := bstep (se 1 (by rfl) ⟨769049, by rfl⟩ : syracuseStep 1025399 = 1538099) B1538099
theorem B14787971 : Blo 401768 14787971 := bstep (se 1 (by rfl) ⟨11090978, by rfl⟩ : syracuseStep 14787971 = 22181957) B22181957
theorem B402823 : Blo 401768 402823 := bstep (se 1 (by rfl) ⟨302117, by rfl⟩ : syracuseStep 402823 = 604235) B604235
theorem B402831 : Blo 401768 402831 := bstep (se 1 (by rfl) ⟨302123, by rfl⟩ : syracuseStep 402831 = 604247) B604247
theorem B402875 : Blo 401768 402875 := bstep (se 1 (by rfl) ⟨302156, by rfl⟩ : syracuseStep 402875 = 604313) B604313
theorem B1091017 : Blo 401768 1091017 := bstep (se 2 (by rfl) ⟨409131, by rfl⟩ : syracuseStep 1091017 = 818263) B818263
theorem B402951 : Blo 401768 402951 := bstep (se 1 (by rfl) ⟨302213, by rfl⟩ : syracuseStep 402951 = 604427) B604427
theorem B402959 : Blo 401768 402959 := bstep (se 1 (by rfl) ⟨302219, by rfl⟩ : syracuseStep 402959 = 604439) B604439
theorem B403003 : Blo 401768 403003 := bstep (se 1 (by rfl) ⟨302252, by rfl⟩ : syracuseStep 403003 = 604505) B604505
theorem B2303549 : Blo 401768 2303549 := bstep (se 3 (by rfl) ⟨431915, by rfl⟩ : syracuseStep 2303549 = 863831) B863831
theorem B861815 : Blo 401768 861815 := bstep (se 1 (by rfl) ⟨646361, by rfl⟩ : syracuseStep 861815 = 1292723) B1292723
theorem B1091191 : Blo 401768 1091191 := bstep (se 1 (by rfl) ⟨818393, by rfl⟩ : syracuseStep 1091191 = 1636787) B1636787
theorem B403079 : Blo 401768 403079 := bstep (se 1 (by rfl) ⟨302309, by rfl⟩ : syracuseStep 403079 = 604619) B604619
theorem B403087 : Blo 401768 403087 := bstep (se 1 (by rfl) ⟨302315, by rfl⟩ : syracuseStep 403087 = 604631) B604631
theorem B403131 : Blo 401768 403131 := bstep (se 1 (by rfl) ⟨302348, by rfl⟩ : syracuseStep 403131 = 604697) B604697
theorem B403207 : Blo 401768 403207 := bstep (se 1 (by rfl) ⟨302405, by rfl⟩ : syracuseStep 403207 = 604811) B604811
theorem B403215 : Blo 401768 403215 := bstep (se 1 (by rfl) ⟨302411, by rfl⟩ : syracuseStep 403215 = 604823) B604823
theorem B763681 : Blo 401768 763681 := bstep (se 2 (by rfl) ⟨286380, by rfl⟩ : syracuseStep 763681 = 572761) B572761
theorem B403259 : Blo 401768 403259 := bstep (se 1 (by rfl) ⟨302444, by rfl⟩ : syracuseStep 403259 = 604889) B604889
theorem B1451891 : Blo 401768 1451891 := bstep (se 1 (by rfl) ⟨1088918, by rfl⟩ : syracuseStep 1451891 = 2177837) B2177837
theorem B403335 : Blo 401768 403335 := bstep (se 1 (by rfl) ⟨302501, by rfl⟩ : syracuseStep 403335 = 605003) B605003
theorem B403343 : Blo 401768 403343 := bstep (se 1 (by rfl) ⟨302507, by rfl⟩ : syracuseStep 403343 = 605015) B605015
theorem B403387 : Blo 401768 403387 := bstep (se 1 (by rfl) ⟨302540, by rfl⟩ : syracuseStep 403387 = 605081) B605081
theorem B403463 : Blo 401768 403463 := bstep (se 1 (by rfl) ⟨302597, by rfl⟩ : syracuseStep 403463 = 605195) B605195
theorem B403471 : Blo 401768 403471 := bstep (se 1 (by rfl) ⟨302603, by rfl⟩ : syracuseStep 403471 = 605207) B605207
theorem B403515 : Blo 401768 403515 := bstep (se 1 (by rfl) ⟨302636, by rfl⟩ : syracuseStep 403515 = 605273) B605273
theorem B403591 : Blo 401768 403591 := bstep (se 1 (by rfl) ⟨302693, by rfl⟩ : syracuseStep 403591 = 605387) B605387
theorem B403599 : Blo 401768 403599 := bstep (se 1 (by rfl) ⟨302699, by rfl⟩ : syracuseStep 403599 = 605399) B605399
theorem B403643 : Blo 401768 403643 := bstep (se 1 (by rfl) ⟨302732, by rfl⟩ : syracuseStep 403643 = 605465) B605465
theorem B403719 : Blo 401768 403719 := bstep (se 1 (by rfl) ⟨302789, by rfl⟩ : syracuseStep 403719 = 605579) B605579
theorem B403727 : Blo 401768 403727 := bstep (se 1 (by rfl) ⟨302795, by rfl⟩ : syracuseStep 403727 = 605591) B605591
theorem B2042171 : Blo 401768 2042171 := bstep (se 1 (by rfl) ⟨1531628, by rfl⟩ : syracuseStep 2042171 = 3063257) B3063257
theorem B403771 : Blo 401768 403771 := bstep (se 1 (by rfl) ⟨302828, by rfl⟩ : syracuseStep 403771 = 605657) B605657
theorem B1026391 : Blo 401768 1026391 := bstep (se 1 (by rfl) ⟨769793, by rfl⟩ : syracuseStep 1026391 = 1539587) B1539587
theorem B403847 : Blo 401768 403847 := bstep (se 1 (by rfl) ⟨302885, by rfl⟩ : syracuseStep 403847 = 605771) B605771
theorem B403855 : Blo 401768 403855 := bstep (se 1 (by rfl) ⟨302891, by rfl⟩ : syracuseStep 403855 = 605783) B605783
theorem B403899 : Blo 401768 403899 := bstep (se 1 (by rfl) ⟨302924, by rfl⟩ : syracuseStep 403899 = 605849) B605849
theorem B2042333 : Blo 401768 2042333 := bstep (se 3 (by rfl) ⟨382937, by rfl⟩ : syracuseStep 2042333 = 765875) B765875
theorem B403975 : Blo 401768 403975 := bstep (se 1 (by rfl) ⟨302981, by rfl⟩ : syracuseStep 403975 = 605963) B605963
theorem B403983 : Blo 401768 403983 := bstep (se 1 (by rfl) ⟨302987, by rfl⟩ : syracuseStep 403983 = 605975) B605975
theorem B404027 : Blo 401768 404027 := bstep (se 1 (by rfl) ⟨303020, by rfl⟩ : syracuseStep 404027 = 606041) B606041
theorem B404103 : Blo 401768 404103 := bstep (se 1 (by rfl) ⟨303077, by rfl⟩ : syracuseStep 404103 = 606155) B606155
theorem B1026695 : Blo 401768 1026695 := bstep (se 1 (by rfl) ⟨770021, by rfl⟩ : syracuseStep 1026695 = 1540043) B1540043
theorem B404111 : Blo 401768 404111 := bstep (se 1 (by rfl) ⟨303083, by rfl⟩ : syracuseStep 404111 = 606167) B606167
theorem B404155 : Blo 401768 404155 := bstep (se 1 (by rfl) ⟨303116, by rfl⟩ : syracuseStep 404155 = 606233) B606233
theorem B404231 : Blo 401768 404231 := bstep (se 1 (by rfl) ⟨303173, by rfl⟩ : syracuseStep 404231 = 606347) B606347
theorem B1026827 : Blo 401768 1026827 := bstep (se 1 (by rfl) ⟨770120, by rfl⟩ : syracuseStep 1026827 = 1540241) B1540241
theorem B404239 : Blo 401768 404239 := bstep (se 1 (by rfl) ⟨303179, by rfl⟩ : syracuseStep 404239 = 606359) B606359
theorem B2042657 : Blo 401768 2042657 := bstep (se 2 (by rfl) ⟨765996, by rfl⟩ : syracuseStep 2042657 = 1531993) B1531993
theorem B404283 : Blo 401768 404283 := bstep (se 1 (by rfl) ⟨303212, by rfl⟩ : syracuseStep 404283 = 606425) B606425
theorem B7023449 : Blo 401768 7023449 := bstep (se 2 (by rfl) ⟨2633793, by rfl⟩ : syracuseStep 7023449 = 5267587) B5267587
theorem B404359 : Blo 401768 404359 := bstep (se 1 (by rfl) ⟨303269, by rfl⟩ : syracuseStep 404359 = 606539) B606539
theorem B404367 : Blo 401768 404367 := bstep (se 1 (by rfl) ⟨303275, by rfl⟩ : syracuseStep 404367 = 606551) B606551
theorem B404411 : Blo 401768 404411 := bstep (se 1 (by rfl) ⟨303308, by rfl⟩ : syracuseStep 404411 = 606617) B606617
theorem B764873 : Blo 401768 764873 := bstep (se 2 (by rfl) ⟨286827, by rfl⟩ : syracuseStep 764873 = 573655) B573655
theorem B404487 : Blo 401768 404487 := bstep (se 1 (by rfl) ⟨303365, by rfl⟩ : syracuseStep 404487 = 606731) B606731
theorem B404495 : Blo 401768 404495 := bstep (se 1 (by rfl) ⟨303371, by rfl⟩ : syracuseStep 404495 = 606743) B606743
theorem B404539 : Blo 401768 404539 := bstep (se 1 (by rfl) ⟨303404, by rfl⟩ : syracuseStep 404539 = 606809) B606809
theorem B404615 : Blo 401768 404615 := bstep (se 1 (by rfl) ⟨303461, by rfl⟩ : syracuseStep 404615 = 606923) B606923
theorem B404623 : Blo 401768 404623 := bstep (se 1 (by rfl) ⟨303467, by rfl⟩ : syracuseStep 404623 = 606935) B606935
theorem B404667 : Blo 401768 404667 := bstep (se 1 (by rfl) ⟨303500, by rfl⟩ : syracuseStep 404667 = 607001) B607001
theorem B404743 : Blo 401768 404743 := bstep (se 1 (by rfl) ⟨303557, by rfl⟩ : syracuseStep 404743 = 607115) B607115
theorem B404751 : Blo 401768 404751 := bstep (se 1 (by rfl) ⟨303563, by rfl⟩ : syracuseStep 404751 = 607127) B607127
theorem B404795 : Blo 401768 404795 := bstep (se 1 (by rfl) ⟨303596, by rfl⟩ : syracuseStep 404795 = 607193) B607193
theorem B404871 : Blo 401768 404871 := bstep (se 1 (by rfl) ⟨303653, by rfl⟩ : syracuseStep 404871 = 607307) B607307
theorem B404879 : Blo 401768 404879 := bstep (se 1 (by rfl) ⟨303659, by rfl⟩ : syracuseStep 404879 = 607319) B607319
theorem B1060249 : Blo 401768 1060249 := bstep (se 2 (by rfl) ⟨397593, by rfl⟩ : syracuseStep 1060249 = 795187) B795187
theorem B404923 : Blo 401768 404923 := bstep (se 1 (by rfl) ⟨303692, by rfl⟩ : syracuseStep 404923 = 607385) B607385
theorem B404999 : Blo 401768 404999 := bstep (se 1 (by rfl) ⟨303749, by rfl⟩ : syracuseStep 404999 = 607499) B607499
theorem B405007 : Blo 401768 405007 := bstep (se 1 (by rfl) ⟨303755, by rfl⟩ : syracuseStep 405007 = 607511) B607511
theorem B405051 : Blo 401768 405051 := bstep (se 1 (by rfl) ⟨303788, by rfl⟩ : syracuseStep 405051 = 607577) B607577
theorem B405127 : Blo 401768 405127 := bstep (se 1 (by rfl) ⟨303845, by rfl⟩ : syracuseStep 405127 = 607691) B607691
theorem B24850061 : Blo 401768 24850061 := bstep (se 3 (by rfl) ⟨4659386, by rfl⟩ : syracuseStep 24850061 = 9318773) B9318773
theorem B405135 : Blo 401768 405135 := bstep (se 1 (by rfl) ⟨303851, by rfl⟩ : syracuseStep 405135 = 607703) B607703
theorem B765587 : Blo 401768 765587 := bstep (se 1 (by rfl) ⟨574190, by rfl⟩ : syracuseStep 765587 = 1148381) B1148381
theorem B765625 : Blo 401768 765625 := bstep (se 2 (by rfl) ⟨287109, by rfl⟩ : syracuseStep 765625 = 574219) B574219
theorem B405179 : Blo 401768 405179 := bstep (se 1 (by rfl) ⟨303884, by rfl⟩ : syracuseStep 405179 = 607769) B607769
theorem B2043629 : Blo 401768 2043629 := bstep (se 3 (by rfl) ⟨383180, by rfl⟩ : syracuseStep 2043629 = 766361) B766361
theorem B405255 : Blo 401768 405255 := bstep (se 1 (by rfl) ⟨303941, by rfl⟩ : syracuseStep 405255 = 607883) B607883
theorem B405263 : Blo 401768 405263 := bstep (se 1 (by rfl) ⟨303947, by rfl⟩ : syracuseStep 405263 = 607895) B607895
theorem B3288883 : Blo 401768 3288883 := bstep (se 1 (by rfl) ⟨2466662, by rfl⟩ : syracuseStep 3288883 = 4933325) B4933325
theorem B405307 : Blo 401768 405307 := bstep (se 1 (by rfl) ⟨303980, by rfl⟩ : syracuseStep 405307 = 607961) B607961
theorem B405383 : Blo 401768 405383 := bstep (se 1 (by rfl) ⟨304037, by rfl⟩ : syracuseStep 405383 = 608075) B608075
theorem B405391 : Blo 401768 405391 := bstep (se 1 (by rfl) ⟨304043, by rfl⟩ : syracuseStep 405391 = 608087) B608087
theorem B405435 : Blo 401768 405435 := bstep (se 1 (by rfl) ⟨304076, by rfl⟩ : syracuseStep 405435 = 608153) B608153
theorem B405511 : Blo 401768 405511 := bstep (se 1 (by rfl) ⟨304133, by rfl⟩ : syracuseStep 405511 = 608267) B608267
theorem B405519 : Blo 401768 405519 := bstep (se 1 (by rfl) ⟨304139, by rfl⟩ : syracuseStep 405519 = 608279) B608279
theorem B405563 : Blo 401768 405563 := bstep (se 1 (by rfl) ⟨304172, by rfl⟩ : syracuseStep 405563 = 608345) B608345
theorem B405639 : Blo 401768 405639 := bstep (se 1 (by rfl) ⟨304229, by rfl⟩ : syracuseStep 405639 = 608459) B608459
theorem B405647 : Blo 401768 405647 := bstep (se 1 (by rfl) ⟨304235, by rfl⟩ : syracuseStep 405647 = 608471) B608471
theorem B405691 : Blo 401768 405691 := bstep (se 1 (by rfl) ⟨304268, by rfl⟩ : syracuseStep 405691 = 608537) B608537
theorem B405767 : Blo 401768 405767 := bstep (se 1 (by rfl) ⟨304325, by rfl⟩ : syracuseStep 405767 = 608651) B608651
theorem B1356047 : Blo 401768 1356047 := bstep (se 1 (by rfl) ⟨1017035, by rfl⟩ : syracuseStep 1356047 = 2034071) B2034071
theorem B2044439 : Blo 401768 2044439 := bstep (se 1 (by rfl) ⟨1533329, by rfl⟩ : syracuseStep 2044439 = 3066659) B3066659
theorem B1356317 : Blo 401768 1356317 := bstep (se 3 (by rfl) ⟨254309, by rfl⟩ : syracuseStep 1356317 = 508619) B508619
theorem B602681 : Blo 401768 602681 := bstep (se 2 (by rfl) ⟨226005, by rfl⟩ : syracuseStep 602681 = 452011) B452011
theorem B602759 : Blo 401768 602759 := bstep (se 1 (by rfl) ⟨452069, by rfl⟩ : syracuseStep 602759 = 904139) B904139
theorem B602795 : Blo 401768 602795 := bstep (se 1 (by rfl) ⟨452096, by rfl⟩ : syracuseStep 602795 = 904193) B904193
theorem B602825 : Blo 401768 602825 := bstep (se 2 (by rfl) ⟨226059, by rfl⟩ : syracuseStep 602825 = 452119) B452119
theorem B602939 : Blo 401768 602939 := bstep (se 1 (by rfl) ⟨452204, by rfl⟩ : syracuseStep 602939 = 904409) B904409
theorem B602999 : Blo 401768 602999 := bstep (se 1 (by rfl) ⟨452249, by rfl⟩ : syracuseStep 602999 = 904499) B904499
theorem B603023 : Blo 401768 603023 := bstep (se 1 (by rfl) ⟨452267, by rfl⟩ : syracuseStep 603023 = 904535) B904535
theorem B603065 : Blo 401768 603065 := bstep (se 2 (by rfl) ⟨226149, by rfl⟩ : syracuseStep 603065 = 452299) B452299
theorem B603143 : Blo 401768 603143 := bstep (se 1 (by rfl) ⟨452357, by rfl⟩ : syracuseStep 603143 = 904715) B904715
theorem B1094671 : Blo 401768 1094671 := bstep (se 1 (by rfl) ⟨821003, by rfl⟩ : syracuseStep 1094671 = 1642007) B1642007
theorem B603179 : Blo 401768 603179 := bstep (se 1 (by rfl) ⟨452384, by rfl⟩ : syracuseStep 603179 = 904769) B904769
theorem B603209 : Blo 401768 603209 := bstep (se 2 (by rfl) ⟨226203, by rfl⟩ : syracuseStep 603209 = 452407) B452407
theorem B1094791 : Blo 401768 1094791 := bstep (se 1 (by rfl) ⟨821093, by rfl⟩ : syracuseStep 1094791 = 1642187) B1642187
theorem B603323 : Blo 401768 603323 := bstep (se 1 (by rfl) ⟨452492, by rfl⟩ : syracuseStep 603323 = 904985) B904985
theorem B603383 : Blo 401768 603383 := bstep (se 1 (by rfl) ⟨452537, by rfl⟩ : syracuseStep 603383 = 905075) B905075
theorem B603407 : Blo 401768 603407 := bstep (se 1 (by rfl) ⟨452555, by rfl⟩ : syracuseStep 603407 = 905111) B905111
theorem B603449 : Blo 401768 603449 := bstep (se 2 (by rfl) ⟨226293, by rfl⟩ : syracuseStep 603449 = 452587) B452587
theorem B603527 : Blo 401768 603527 := bstep (se 1 (by rfl) ⟨452645, by rfl⟩ : syracuseStep 603527 = 905291) B905291
theorem B603563 : Blo 401768 603563 := bstep (se 1 (by rfl) ⟨452672, by rfl⟩ : syracuseStep 603563 = 905345) B905345
theorem B603593 : Blo 401768 603593 := bstep (se 2 (by rfl) ⟨226347, by rfl⟩ : syracuseStep 603593 = 452695) B452695
theorem B767531 : Blo 401768 767531 := bstep (se 1 (by rfl) ⟨575648, by rfl⟩ : syracuseStep 767531 = 1151297) B1151297
theorem B603707 : Blo 401768 603707 := bstep (se 1 (by rfl) ⟨452780, by rfl⟩ : syracuseStep 603707 = 905561) B905561
theorem B603767 : Blo 401768 603767 := bstep (se 1 (by rfl) ⟨452825, by rfl⟩ : syracuseStep 603767 = 905651) B905651
theorem B603791 : Blo 401768 603791 := bstep (se 1 (by rfl) ⟨452843, by rfl⟩ : syracuseStep 603791 = 905687) B905687
theorem B603833 : Blo 401768 603833 := bstep (se 2 (by rfl) ⟨226437, by rfl⟩ : syracuseStep 603833 = 452875) B452875
theorem B603911 : Blo 401768 603911 := bstep (se 1 (by rfl) ⟨452933, by rfl⟩ : syracuseStep 603911 = 905867) B905867
theorem B603947 : Blo 401768 603947 := bstep (se 1 (by rfl) ⟨452960, by rfl⟩ : syracuseStep 603947 = 905921) B905921
theorem B603977 : Blo 401768 603977 := bstep (se 2 (by rfl) ⟨226491, by rfl⟩ : syracuseStep 603977 = 452983) B452983
theorem B1357721 : Blo 401768 1357721 := bstep (se 2 (by rfl) ⟨509145, by rfl⟩ : syracuseStep 1357721 = 1018291) B1018291
theorem B604091 : Blo 401768 604091 := bstep (se 1 (by rfl) ⟨453068, by rfl⟩ : syracuseStep 604091 = 906137) B906137
theorem B604151 : Blo 401768 604151 := bstep (se 1 (by rfl) ⟨453113, by rfl⟩ : syracuseStep 604151 = 906227) B906227
theorem B604175 : Blo 401768 604175 := bstep (se 1 (by rfl) ⟨453131, by rfl⟩ : syracuseStep 604175 = 906263) B906263
theorem B604217 : Blo 401768 604217 := bstep (se 2 (by rfl) ⟨226581, by rfl⟩ : syracuseStep 604217 = 453163) B453163
theorem B2275415 : Blo 401768 2275415 := bstep (se 1 (by rfl) ⟨1706561, by rfl⟩ : syracuseStep 2275415 = 3413123) B3413123
theorem B604295 : Blo 401768 604295 := bstep (se 1 (by rfl) ⟨453221, by rfl⟩ : syracuseStep 604295 = 906443) B906443
theorem B604331 : Blo 401768 604331 := bstep (se 1 (by rfl) ⟨453248, by rfl⟩ : syracuseStep 604331 = 906497) B906497
theorem B604361 : Blo 401768 604361 := bstep (se 2 (by rfl) ⟨226635, by rfl⟩ : syracuseStep 604361 = 453271) B453271
theorem B604475 : Blo 401768 604475 := bstep (se 1 (by rfl) ⟨453356, by rfl⟩ : syracuseStep 604475 = 906713) B906713
theorem B26589505 : Blo 401768 26589505 := bstep (se 2 (by rfl) ⟨9971064, by rfl⟩ : syracuseStep 26589505 = 19942129) B19942129
theorem B604535 : Blo 401768 604535 := bstep (se 1 (by rfl) ⟨453401, by rfl⟩ : syracuseStep 604535 = 906803) B906803
theorem B604559 : Blo 401768 604559 := bstep (se 1 (by rfl) ⟨453419, by rfl⟩ : syracuseStep 604559 = 906839) B906839
theorem B604601 : Blo 401768 604601 := bstep (se 2 (by rfl) ⟨226725, by rfl⟩ : syracuseStep 604601 = 453451) B453451
theorem B768457 : Blo 401768 768457 := bstep (se 2 (by rfl) ⟨288171, by rfl⟩ : syracuseStep 768457 = 576343) B576343
theorem B604679 : Blo 401768 604679 := bstep (se 1 (by rfl) ⟨453509, by rfl⟩ : syracuseStep 604679 = 907019) B907019
theorem B604715 : Blo 401768 604715 := bstep (se 1 (by rfl) ⟨453536, by rfl⟩ : syracuseStep 604715 = 907073) B907073
theorem B604745 : Blo 401768 604745 := bstep (se 2 (by rfl) ⟨226779, by rfl⟩ : syracuseStep 604745 = 453559) B453559
theorem B1358423 : Blo 401768 1358423 := bstep (se 1 (by rfl) ⟨1018817, by rfl⟩ : syracuseStep 1358423 = 2037635) B2037635
theorem B604859 : Blo 401768 604859 := bstep (se 1 (by rfl) ⟨453644, by rfl⟩ : syracuseStep 604859 = 907289) B907289
theorem B604919 : Blo 401768 604919 := bstep (se 1 (by rfl) ⟨453689, by rfl⟩ : syracuseStep 604919 = 907379) B907379
theorem B604943 : Blo 401768 604943 := bstep (se 1 (by rfl) ⟨453707, by rfl⟩ : syracuseStep 604943 = 907415) B907415
theorem B604985 : Blo 401768 604985 := bstep (se 2 (by rfl) ⟨226869, by rfl⟩ : syracuseStep 604985 = 453739) B453739
theorem B605063 : Blo 401768 605063 := bstep (se 1 (by rfl) ⟨453797, by rfl⟩ : syracuseStep 605063 = 907595) B907595
theorem B605099 : Blo 401768 605099 := bstep (se 1 (by rfl) ⟨453824, by rfl⟩ : syracuseStep 605099 = 907649) B907649
theorem B605129 : Blo 401768 605129 := bstep (se 2 (by rfl) ⟨226923, by rfl⟩ : syracuseStep 605129 = 453847) B453847
theorem B1031183 : Blo 401768 1031183 := bstep (se 1 (by rfl) ⟨773387, by rfl⟩ : syracuseStep 1031183 = 1546775) B1546775
theorem B605243 : Blo 401768 605243 := bstep (se 1 (by rfl) ⟨453932, by rfl⟩ : syracuseStep 605243 = 907865) B907865
theorem B1358909 : Blo 401768 1358909 := bstep (se 3 (by rfl) ⟨254795, by rfl⟩ : syracuseStep 1358909 = 509591) B509591
theorem B1850435 : Blo 401768 1850435 := bstep (se 1 (by rfl) ⟨1387826, by rfl⟩ : syracuseStep 1850435 = 2775653) B2775653
theorem B5160023 : Blo 401768 5160023 := bstep (se 1 (by rfl) ⟨3870017, by rfl⟩ : syracuseStep 5160023 = 7740035) B7740035
theorem B605303 : Blo 401768 605303 := bstep (se 1 (by rfl) ⟨453977, by rfl⟩ : syracuseStep 605303 = 907955) B907955
theorem B605327 : Blo 401768 605327 := bstep (se 1 (by rfl) ⟨453995, by rfl⟩ : syracuseStep 605327 = 907991) B907991
theorem B769171 : Blo 401768 769171 := bstep (se 1 (by rfl) ⟨576878, by rfl⟩ : syracuseStep 769171 = 1153757) B1153757
theorem B605369 : Blo 401768 605369 := bstep (se 2 (by rfl) ⟨227013, by rfl⟩ : syracuseStep 605369 = 454027) B454027
theorem B605447 : Blo 401768 605447 := bstep (se 1 (by rfl) ⟨454085, by rfl⟩ : syracuseStep 605447 = 908171) B908171
theorem B605483 : Blo 401768 605483 := bstep (se 1 (by rfl) ⟨454112, by rfl⟩ : syracuseStep 605483 = 908225) B908225
theorem B2178355 : Blo 401768 2178355 := bstep (se 1 (by rfl) ⟨1633766, by rfl⟩ : syracuseStep 2178355 = 3267533) B3267533
theorem B605513 : Blo 401768 605513 := bstep (se 2 (by rfl) ⟨227067, by rfl⟩ : syracuseStep 605513 = 454135) B454135
theorem B605627 : Blo 401768 605627 := bstep (se 1 (by rfl) ⟨454220, by rfl⟩ : syracuseStep 605627 = 908441) B908441
theorem B605687 : Blo 401768 605687 := bstep (se 1 (by rfl) ⟨454265, by rfl⟩ : syracuseStep 605687 = 908531) B908531
theorem B605711 : Blo 401768 605711 := bstep (se 1 (by rfl) ⟨454283, by rfl⟩ : syracuseStep 605711 = 908567) B908567
theorem B2047517 : Blo 401768 2047517 := bstep (se 3 (by rfl) ⟨383909, by rfl⟩ : syracuseStep 2047517 = 767819) B767819
theorem B605753 : Blo 401768 605753 := bstep (se 2 (by rfl) ⟨227157, by rfl⟩ : syracuseStep 605753 = 454315) B454315
theorem B605831 : Blo 401768 605831 := bstep (se 1 (by rfl) ⟨454373, by rfl⟩ : syracuseStep 605831 = 908747) B908747
theorem B605867 : Blo 401768 605867 := bstep (se 1 (by rfl) ⟨454400, by rfl⟩ : syracuseStep 605867 = 908801) B908801
theorem B5193395 : Blo 401768 5193395 := bstep (se 1 (by rfl) ⟨3895046, by rfl⟩ : syracuseStep 5193395 = 7790093) B7790093
theorem B605897 : Blo 401768 605897 := bstep (se 2 (by rfl) ⟨227211, by rfl⟩ : syracuseStep 605897 = 454423) B454423
theorem B606011 : Blo 401768 606011 := bstep (se 1 (by rfl) ⟨454508, by rfl⟩ : syracuseStep 606011 = 909017) B909017
theorem B966487 : Blo 401768 966487 := bstep (se 1 (by rfl) ⟨724865, by rfl⟩ : syracuseStep 966487 = 1449731) B1449731
theorem B606071 : Blo 401768 606071 := bstep (se 1 (by rfl) ⟨454553, by rfl⟩ : syracuseStep 606071 = 909107) B909107
theorem B606095 : Blo 401768 606095 := bstep (se 1 (by rfl) ⟨454571, by rfl⟩ : syracuseStep 606095 = 909143) B909143
theorem B606137 : Blo 401768 606137 := bstep (se 2 (by rfl) ⟨227301, by rfl⟩ : syracuseStep 606137 = 454603) B454603
theorem B2048003 : Blo 401768 2048003 := bstep (se 1 (by rfl) ⟨1536002, by rfl⟩ : syracuseStep 2048003 = 3072005) B3072005
theorem B606215 : Blo 401768 606215 := bstep (se 1 (by rfl) ⟨454661, by rfl⟩ : syracuseStep 606215 = 909323) B909323
theorem B1720349 : Blo 401768 1720349 := bstep (se 3 (by rfl) ⟨322565, by rfl⟩ : syracuseStep 1720349 = 645131) B645131
theorem B606251 : Blo 401768 606251 := bstep (se 1 (by rfl) ⟨454688, by rfl⟩ : syracuseStep 606251 = 909377) B909377
theorem B606281 : Blo 401768 606281 := bstep (se 2 (by rfl) ⟨227355, by rfl⟩ : syracuseStep 606281 = 454711) B454711
theorem B606395 : Blo 401768 606395 := bstep (se 1 (by rfl) ⟨454796, by rfl⟩ : syracuseStep 606395 = 909593) B909593
theorem B770249 : Blo 401768 770249 := bstep (se 2 (by rfl) ⟨288843, by rfl⟩ : syracuseStep 770249 = 577687) B577687
theorem B606455 : Blo 401768 606455 := bstep (se 1 (by rfl) ⟨454841, by rfl⟩ : syracuseStep 606455 = 909683) B909683
theorem B606479 : Blo 401768 606479 := bstep (se 1 (by rfl) ⟨454859, by rfl⟩ : syracuseStep 606479 = 909719) B909719
theorem B606521 : Blo 401768 606521 := bstep (se 2 (by rfl) ⟨227445, by rfl⟩ : syracuseStep 606521 = 454891) B454891
theorem B606599 : Blo 401768 606599 := bstep (se 1 (by rfl) ⟨454949, by rfl⟩ : syracuseStep 606599 = 909899) B909899
theorem B606635 : Blo 401768 606635 := bstep (se 1 (by rfl) ⟨454976, by rfl⟩ : syracuseStep 606635 = 909953) B909953
theorem B1360313 : Blo 401768 1360313 := bstep (se 2 (by rfl) ⟨510117, by rfl⟩ : syracuseStep 1360313 = 1020235) B1020235
theorem B606665 : Blo 401768 606665 := bstep (se 2 (by rfl) ⟨227499, by rfl⟩ : syracuseStep 606665 = 454999) B454999
theorem B2769437 : Blo 401768 2769437 := bstep (se 3 (by rfl) ⟨519269, by rfl⟩ : syracuseStep 2769437 = 1038539) B1038539
theorem B606779 : Blo 401768 606779 := bstep (se 1 (by rfl) ⟨455084, by rfl⟩ : syracuseStep 606779 = 910169) B910169
theorem B1294967 : Blo 401768 1294967 := bstep (se 1 (by rfl) ⟨971225, by rfl⟩ : syracuseStep 1294967 = 1942451) B1942451
theorem B606839 : Blo 401768 606839 := bstep (se 1 (by rfl) ⟨455129, by rfl⟩ : syracuseStep 606839 = 910259) B910259
theorem B606863 : Blo 401768 606863 := bstep (se 1 (by rfl) ⟨455147, by rfl⟩ : syracuseStep 606863 = 910295) B910295
theorem B606905 : Blo 401768 606905 := bstep (se 2 (by rfl) ⟨227589, by rfl⟩ : syracuseStep 606905 = 455179) B455179
theorem B1721033 : Blo 401768 1721033 := bstep (se 2 (by rfl) ⟨645387, by rfl⟩ : syracuseStep 1721033 = 1290775) B1290775
theorem B4735705 : Blo 401768 4735705 := bstep (se 2 (by rfl) ⟨1775889, by rfl⟩ : syracuseStep 4735705 = 3551779) B3551779
theorem B4997861 : Blo 401768 4997861 := bstep (se 4 (by rfl) ⟨468549, by rfl⟩ : syracuseStep 4997861 = 937099) B937099
theorem B606983 : Blo 401768 606983 := bstep (se 1 (by rfl) ⟨455237, by rfl⟩ : syracuseStep 606983 = 910475) B910475
theorem B607019 : Blo 401768 607019 := bstep (se 1 (by rfl) ⟨455264, by rfl⟩ : syracuseStep 607019 = 910529) B910529
theorem B607049 : Blo 401768 607049 := bstep (se 2 (by rfl) ⟨227643, by rfl⟩ : syracuseStep 607049 = 455287) B455287
theorem B574327 : Blo 401768 574327 := bstep (se 1 (by rfl) ⟨430745, by rfl⟩ : syracuseStep 574327 = 861491) B861491
theorem B607163 : Blo 401768 607163 := bstep (se 1 (by rfl) ⟨455372, by rfl⟩ : syracuseStep 607163 = 910745) B910745
theorem B607223 : Blo 401768 607223 := bstep (se 1 (by rfl) ⟨455417, by rfl⟩ : syracuseStep 607223 = 910835) B910835
theorem B1360907 : Blo 401768 1360907 := bstep (se 1 (by rfl) ⟨1020680, by rfl⟩ : syracuseStep 1360907 = 2041361) B2041361
theorem B9815051 : Blo 401768 9815051 := bstep (se 1 (by rfl) ⟨7361288, by rfl⟩ : syracuseStep 9815051 = 14722577) B14722577
theorem B508943 : Blo 401768 508943 := bstep (se 1 (by rfl) ⟨381707, by rfl⟩ : syracuseStep 508943 = 763415) B763415
theorem B607247 : Blo 401768 607247 := bstep (se 1 (by rfl) ⟨455435, by rfl⟩ : syracuseStep 607247 = 910871) B910871
theorem B607289 : Blo 401768 607289 := bstep (se 2 (by rfl) ⟨227733, by rfl⟩ : syracuseStep 607289 = 455467) B455467
theorem B1361015 : Blo 401768 1361015 := bstep (se 1 (by rfl) ⟨1020761, by rfl⟩ : syracuseStep 1361015 = 2041523) B2041523
theorem B607367 : Blo 401768 607367 := bstep (se 1 (by rfl) ⟨455525, by rfl⟩ : syracuseStep 607367 = 911051) B911051
theorem B607403 : Blo 401768 607403 := bstep (se 1 (by rfl) ⟨455552, by rfl⟩ : syracuseStep 607403 = 911105) B911105
theorem B607433 : Blo 401768 607433 := bstep (se 2 (by rfl) ⟨227787, by rfl⟩ : syracuseStep 607433 = 455575) B455575
theorem B607547 : Blo 401768 607547 := bstep (se 1 (by rfl) ⟨455660, by rfl⟩ : syracuseStep 607547 = 911321) B911321
theorem B607607 : Blo 401768 607607 := bstep (se 1 (by rfl) ⟨455705, by rfl⟩ : syracuseStep 607607 = 911411) B911411
theorem B607631 : Blo 401768 607631 := bstep (se 1 (by rfl) ⟨455723, by rfl⟩ : syracuseStep 607631 = 911447) B911447
theorem B607673 : Blo 401768 607673 := bstep (se 2 (by rfl) ⟨227877, by rfl⟩ : syracuseStep 607673 = 455755) B455755
theorem B607751 : Blo 401768 607751 := bstep (se 1 (by rfl) ⟨455813, by rfl⟩ : syracuseStep 607751 = 911627) B911627
theorem B607787 : Blo 401768 607787 := bstep (se 1 (by rfl) ⟨455840, by rfl⟩ : syracuseStep 607787 = 911681) B911681
theorem B607817 : Blo 401768 607817 := bstep (se 2 (by rfl) ⟨227931, by rfl⟩ : syracuseStep 607817 = 455863) B455863
theorem B2049623 : Blo 401768 2049623 := bstep (se 1 (by rfl) ⟨1537217, by rfl⟩ : syracuseStep 2049623 = 3074435) B3074435
theorem B575147 : Blo 401768 575147 := bstep (se 1 (by rfl) ⟨431360, by rfl⟩ : syracuseStep 575147 = 862721) B862721
theorem B607931 : Blo 401768 607931 := bstep (se 1 (by rfl) ⟨455948, by rfl⟩ : syracuseStep 607931 = 911897) B911897
theorem B1361609 : Blo 401768 1361609 := bstep (se 2 (by rfl) ⟨510603, by rfl⟩ : syracuseStep 1361609 = 1021207) B1021207
theorem B607991 : Blo 401768 607991 := bstep (se 1 (by rfl) ⟨455993, by rfl⟩ : syracuseStep 607991 = 911987) B911987
theorem B608015 : Blo 401768 608015 := bstep (se 1 (by rfl) ⟨456011, by rfl⟩ : syracuseStep 608015 = 912023) B912023
theorem B608057 : Blo 401768 608057 := bstep (se 2 (by rfl) ⟨228021, by rfl⟩ : syracuseStep 608057 = 456043) B456043
theorem B608135 : Blo 401768 608135 := bstep (se 1 (by rfl) ⟨456101, by rfl⟩ : syracuseStep 608135 = 912203) B912203
theorem B9848729 : Blo 401768 9848729 := bstep (se 2 (by rfl) ⟨3693273, by rfl⟩ : syracuseStep 9848729 = 7386547) B7386547
theorem B608171 : Blo 401768 608171 := bstep (se 1 (by rfl) ⟨456128, by rfl⟩ : syracuseStep 608171 = 912257) B912257
theorem B608201 : Blo 401768 608201 := bstep (se 2 (by rfl) ⟨228075, by rfl⟩ : syracuseStep 608201 = 456151) B456151
theorem B1296413 : Blo 401768 1296413 := bstep (se 3 (by rfl) ⟨243077, by rfl⟩ : syracuseStep 1296413 = 486155) B486155
theorem B9783341 : Blo 401768 9783341 := bstep (se 3 (by rfl) ⟨1834376, by rfl⟩ : syracuseStep 9783341 = 3668753) B3668753
theorem B608315 : Blo 401768 608315 := bstep (se 1 (by rfl) ⟨456236, by rfl⟩ : syracuseStep 608315 = 912473) B912473
theorem B2050109 : Blo 401768 2050109 := bstep (se 3 (by rfl) ⟨384395, by rfl⟩ : syracuseStep 2050109 = 768791) B768791
theorem B608375 : Blo 401768 608375 := bstep (se 1 (by rfl) ⟨456281, by rfl⟩ : syracuseStep 608375 = 912563) B912563
theorem B608399 : Blo 401768 608399 := bstep (se 1 (by rfl) ⟨456299, by rfl⟩ : syracuseStep 608399 = 912599) B912599
theorem B608441 : Blo 401768 608441 := bstep (se 2 (by rfl) ⟨228165, by rfl⟩ : syracuseStep 608441 = 456331) B456331
theorem B608519 : Blo 401768 608519 := bstep (se 1 (by rfl) ⟨456389, by rfl⟩ : syracuseStep 608519 = 912779) B912779
theorem B608555 : Blo 401768 608555 := bstep (se 1 (by rfl) ⟨456416, by rfl⟩ : syracuseStep 608555 = 912833) B912833
theorem B608585 : Blo 401768 608585 := bstep (se 2 (by rfl) ⟨228219, by rfl⟩ : syracuseStep 608585 = 456439) B456439
theorem B1362311 : Blo 401768 1362311 := bstep (se 1 (by rfl) ⟨1021733, by rfl⟩ : syracuseStep 1362311 = 2043467) B2043467
theorem B1722809 : Blo 401768 1722809 := bstep (se 2 (by rfl) ⟨646053, by rfl⟩ : syracuseStep 1722809 = 1292107) B1292107
theorem B2444033 : Blo 401768 2444033 := bstep (se 2 (by rfl) ⟨916512, by rfl⟩ : syracuseStep 2444033 = 1833025) B1833025
theorem B1362689 : Blo 401768 1362689 := bstep (se 2 (by rfl) ⟨511008, by rfl⟩ : syracuseStep 1362689 = 1022017) B1022017
theorem B903995 : Blo 401768 903995 := bstep (se 1 (by rfl) ⟨677996, by rfl⟩ : syracuseStep 903995 = 1355993) B1355993
theorem B543547 : Blo 401768 543547 := bstep (se 1 (by rfl) ⟨407660, by rfl⟩ : syracuseStep 543547 = 815321) B815321
theorem B904121 : Blo 401768 904121 := bstep (se 2 (by rfl) ⟨339045, by rfl⟩ : syracuseStep 904121 = 678091) B678091
theorem B576571 : Blo 401768 576571 := bstep (se 1 (by rfl) ⟨432428, by rfl⟩ : syracuseStep 576571 = 864857) B864857
theorem B969995 : Blo 401768 969995 := bstep (se 1 (by rfl) ⟨727496, by rfl⟩ : syracuseStep 969995 = 1454993) B1454993
theorem B904463 : Blo 401768 904463 := bstep (se 1 (by rfl) ⟨678347, by rfl⟩ : syracuseStep 904463 = 1356695) B1356695
theorem B904481 : Blo 401768 904481 := bstep (se 2 (by rfl) ⟨339180, by rfl⟩ : syracuseStep 904481 = 678361) B678361
theorem B871723 : Blo 401768 871723 := bstep (se 1 (by rfl) ⟨653792, by rfl⟩ : syracuseStep 871723 = 1307585) B1307585
theorem B1723801 : Blo 401768 1723801 := bstep (se 2 (by rfl) ⟨646425, by rfl⟩ : syracuseStep 1723801 = 1292851) B1292851
theorem B9915857 : Blo 401768 9915857 := bstep (se 2 (by rfl) ⟨3718446, by rfl⟩ : syracuseStep 9915857 = 7436893) B7436893
theorem B1363499 : Blo 401768 1363499 := bstep (se 1 (by rfl) ⟨1022624, by rfl⟩ : syracuseStep 1363499 = 2045249) B2045249
theorem B1166891 : Blo 401768 1166891 := bstep (se 1 (by rfl) ⟨875168, by rfl⟩ : syracuseStep 1166891 = 1750337) B1750337
theorem B904823 : Blo 401768 904823 := bstep (se 1 (by rfl) ⟨678617, by rfl⟩ : syracuseStep 904823 = 1357235) B1357235
theorem B905003 : Blo 401768 905003 := bstep (se 1 (by rfl) ⟨678752, by rfl⟩ : syracuseStep 905003 = 1357505) B1357505
theorem B2051891 : Blo 401768 2051891 := bstep (se 1 (by rfl) ⟨1538918, by rfl⟩ : syracuseStep 2051891 = 3077837) B3077837
theorem B511915 : Blo 401768 511915 := bstep (se 1 (by rfl) ⟨383936, by rfl⟩ : syracuseStep 511915 = 767873) B767873
theorem B2052215 : Blo 401768 2052215 := bstep (se 1 (by rfl) ⟨1539161, by rfl⟩ : syracuseStep 2052215 = 3078323) B3078323
theorem B905363 : Blo 401768 905363 := bstep (se 1 (by rfl) ⟨679022, by rfl⟩ : syracuseStep 905363 = 1358045) B1358045
theorem B905417 : Blo 401768 905417 := bstep (se 2 (by rfl) ⟨339531, by rfl⟩ : syracuseStep 905417 = 679063) B679063
theorem B971023 : Blo 401768 971023 := bstep (se 1 (by rfl) ⟨728267, by rfl⟩ : syracuseStep 971023 = 1456535) B1456535
theorem B8278337 : Blo 401768 8278337 := bstep (se 2 (by rfl) ⟨3104376, by rfl⟩ : syracuseStep 8278337 = 6208753) B6208753
theorem B1298873 : Blo 401768 1298873 := bstep (se 2 (by rfl) ⟨487077, by rfl⟩ : syracuseStep 1298873 = 974155) B974155
theorem B2249227 : Blo 401768 2249227 := bstep (se 1 (by rfl) ⟨1686920, by rfl⟩ : syracuseStep 2249227 = 3373841) B3373841
theorem B1167905 : Blo 401768 1167905 := bstep (se 2 (by rfl) ⟨437964, by rfl⟩ : syracuseStep 1167905 = 875929) B875929
theorem B1233451 : Blo 401768 1233451 := bstep (se 1 (by rfl) ⟨925088, by rfl⟩ : syracuseStep 1233451 = 1850177) B1850177
theorem B1528577 : Blo 401768 1528577 := bstep (se 2 (by rfl) ⟨573216, by rfl⟩ : syracuseStep 1528577 = 1146433) B1146433
theorem B1528591 : Blo 401768 1528591 := bstep (se 1 (by rfl) ⟨1146443, by rfl⟩ : syracuseStep 1528591 = 2292887) B2292887
theorem B1299233 : Blo 401768 1299233 := bstep (se 2 (by rfl) ⟨487212, by rfl⟩ : syracuseStep 1299233 = 974425) B974425
theorem B1364795 : Blo 401768 1364795 := bstep (se 1 (by rfl) ⟨1023596, by rfl⟩ : syracuseStep 1364795 = 2047193) B2047193
theorem B971639 : Blo 401768 971639 := bstep (se 1 (by rfl) ⟨728729, by rfl⟩ : syracuseStep 971639 = 1457459) B1457459
theorem B512887 : Blo 401768 512887 := bstep (se 1 (by rfl) ⟨384665, by rfl⟩ : syracuseStep 512887 = 769331) B769331
theorem B906119 : Blo 401768 906119 := bstep (se 1 (by rfl) ⟨679589, by rfl⟩ : syracuseStep 906119 = 1359179) B1359179
theorem B3265433 : Blo 401768 3265433 := bstep (se 2 (by rfl) ⟨1224537, by rfl⟩ : syracuseStep 3265433 = 2449075) B2449075
theorem B1922051 : Blo 401768 1922051 := bstep (se 1 (by rfl) ⟨1441538, by rfl⟩ : syracuseStep 1922051 = 2883077) B2883077
theorem B906299 : Blo 401768 906299 := bstep (se 1 (by rfl) ⟨679724, by rfl⟩ : syracuseStep 906299 = 1359449) B1359449
theorem B2053187 : Blo 401768 2053187 := bstep (se 1 (by rfl) ⟨1539890, by rfl⟩ : syracuseStep 2053187 = 3079781) B3079781
theorem B906425 : Blo 401768 906425 := bstep (se 2 (by rfl) ⟨339909, by rfl⟩ : syracuseStep 906425 = 679819) B679819
theorem B513211 : Blo 401768 513211 := bstep (se 1 (by rfl) ⟨384908, by rfl⟩ : syracuseStep 513211 = 769817) B769817
theorem B4904225 : Blo 401768 4904225 := bstep (se 2 (by rfl) ⟨1839084, by rfl⟩ : syracuseStep 4904225 = 3678169) B3678169
theorem B1365281 : Blo 401768 1365281 := bstep (se 2 (by rfl) ⟨511980, by rfl⟩ : syracuseStep 1365281 = 1023961) B1023961
theorem B2184583 : Blo 401768 2184583 := bstep (se 1 (by rfl) ⟨1638437, by rfl⟩ : syracuseStep 2184583 = 3276875) B3276875
theorem B2053511 : Blo 401768 2053511 := bstep (se 1 (by rfl) ⟨1540133, by rfl⟩ : syracuseStep 2053511 = 3080267) B3080267
theorem B906767 : Blo 401768 906767 := bstep (se 1 (by rfl) ⟨680075, by rfl⟩ : syracuseStep 906767 = 1360151) B1360151
theorem B546319 : Blo 401768 546319 := bstep (se 1 (by rfl) ⟨409739, by rfl⟩ : syracuseStep 546319 = 819479) B819479
theorem B5199389 : Blo 401768 5199389 := bstep (se 3 (by rfl) ⟨974885, by rfl⟩ : syracuseStep 5199389 = 1949771) B1949771
theorem B906785 : Blo 401768 906785 := bstep (se 2 (by rfl) ⟨340044, by rfl⟩ : syracuseStep 906785 = 680089) B680089
theorem B972407 : Blo 401768 972407 := bstep (se 1 (by rfl) ⟨729305, by rfl⟩ : syracuseStep 972407 = 1458611) B1458611
theorem B3888931 : Blo 401768 3888931 := bstep (se 1 (by rfl) ⟨2916698, by rfl⟩ : syracuseStep 3888931 = 5833397) B5833397
theorem B2185019 : Blo 401768 2185019 := bstep (se 1 (by rfl) ⟨1638764, by rfl⟩ : syracuseStep 2185019 = 3277529) B3277529
theorem B1365875 : Blo 401768 1365875 := bstep (se 1 (by rfl) ⟨1024406, by rfl⟩ : syracuseStep 1365875 = 2048813) B2048813
theorem B907127 : Blo 401768 907127 := bstep (se 1 (by rfl) ⟨680345, by rfl⟩ : syracuseStep 907127 = 1360691) B1360691
theorem B1529867 : Blo 401768 1529867 := bstep (se 1 (by rfl) ⟨1147400, by rfl⟩ : syracuseStep 1529867 = 2294801) B2294801
theorem B1038347 : Blo 401768 1038347 := bstep (se 1 (by rfl) ⟨778760, by rfl⟩ : syracuseStep 1038347 = 1557521) B1557521
theorem B907307 : Blo 401768 907307 := bstep (se 1 (by rfl) ⟨680480, by rfl⟩ : syracuseStep 907307 = 1360961) B1360961
theorem B907667 : Blo 401768 907667 := bstep (se 1 (by rfl) ⟨680750, by rfl⟩ : syracuseStep 907667 = 1361501) B1361501
theorem B907721 : Blo 401768 907721 := bstep (se 2 (by rfl) ⟨340395, by rfl⟩ : syracuseStep 907721 = 680791) B680791
theorem B678415 : Blo 401768 678415 := bstep (se 1 (by rfl) ⟨508811, by rfl⟩ : syracuseStep 678415 = 1017623) B1017623
theorem B1530809 : Blo 401768 1530809 := bstep (se 2 (by rfl) ⟨574053, by rfl⟩ : syracuseStep 1530809 = 1148107) B1148107
theorem B1629227 : Blo 401768 1629227 := bstep (se 1 (by rfl) ⟨1221920, by rfl⟩ : syracuseStep 1629227 = 2443841) B2443841
theorem B678955 : Blo 401768 678955 := bstep (se 1 (by rfl) ⟨509216, by rfl⟩ : syracuseStep 678955 = 1018433) B1018433
theorem B908423 : Blo 401768 908423 := bstep (se 1 (by rfl) ⟨681317, by rfl⟩ : syracuseStep 908423 = 1362635) B1362635
theorem B679097 : Blo 401768 679097 := bstep (se 2 (by rfl) ⟨254661, by rfl⟩ : syracuseStep 679097 = 509323) B509323
theorem B908603 : Blo 401768 908603 := bstep (se 1 (by rfl) ⟨681452, by rfl⟩ : syracuseStep 908603 = 1362905) B1362905
theorem B908729 : Blo 401768 908729 := bstep (se 2 (by rfl) ⟨340773, by rfl⟩ : syracuseStep 908729 = 681547) B681547
theorem B2186813 : Blo 401768 2186813 := bstep (se 3 (by rfl) ⟨410027, by rfl⟩ : syracuseStep 2186813 = 820055) B820055
theorem B909071 : Blo 401768 909071 := bstep (se 1 (by rfl) ⟨681803, by rfl⟩ : syracuseStep 909071 = 1363607) B1363607
theorem B909089 : Blo 401768 909089 := bstep (se 2 (by rfl) ⟨340908, by rfl⟩ : syracuseStep 909089 = 681817) B681817
theorem B1040215 : Blo 401768 1040215 := bstep (se 1 (by rfl) ⟨780161, by rfl⟩ : syracuseStep 1040215 = 1560323) B1560323
theorem B679799 : Blo 401768 679799 := bstep (se 1 (by rfl) ⟨509849, by rfl⟩ : syracuseStep 679799 = 1019699) B1019699
theorem B2187161 : Blo 401768 2187161 := bstep (se 2 (by rfl) ⟨820185, by rfl⟩ : syracuseStep 2187161 = 1640371) B1640371
theorem B647227 : Blo 401768 647227 := bstep (se 1 (by rfl) ⟨485420, by rfl⟩ : syracuseStep 647227 = 970841) B970841
theorem B909431 : Blo 401768 909431 := bstep (se 1 (by rfl) ⟨682073, by rfl⟩ : syracuseStep 909431 = 1364147) B1364147
theorem B614585 : Blo 401768 614585 := bstep (se 2 (by rfl) ⟨230469, by rfl⟩ : syracuseStep 614585 = 460939) B460939
theorem B483575 : Blo 401768 483575 := bstep (se 1 (by rfl) ⟨362681, by rfl⟩ : syracuseStep 483575 = 725363) B725363
theorem B909611 : Blo 401768 909611 := bstep (se 1 (by rfl) ⟨682208, by rfl⟩ : syracuseStep 909611 = 1364417) B1364417
theorem B680251 : Blo 401768 680251 := bstep (se 1 (by rfl) ⟨510188, by rfl⟩ : syracuseStep 680251 = 1020377) B1020377
theorem B1368467 : Blo 401768 1368467 := bstep (se 1 (by rfl) ⟨1026350, by rfl⟩ : syracuseStep 1368467 = 2052701) B2052701
theorem B680393 : Blo 401768 680393 := bstep (se 2 (by rfl) ⟨255147, by rfl⟩ : syracuseStep 680393 = 510295) B510295
theorem B615047 : Blo 401768 615047 := bstep (se 1 (by rfl) ⟨461285, by rfl⟩ : syracuseStep 615047 = 922571) B922571
theorem B909971 : Blo 401768 909971 := bstep (se 1 (by rfl) ⟨682478, by rfl⟩ : syracuseStep 909971 = 1364957) B1364957
theorem B910025 : Blo 401768 910025 := bstep (se 2 (by rfl) ⟨341259, by rfl⟩ : syracuseStep 910025 = 682519) B682519
theorem B5235619 : Blo 401768 5235619 := bstep (se 1 (by rfl) ⟨3926714, by rfl⟩ : syracuseStep 5235619 = 7853429) B7853429
theorem B484267 : Blo 401768 484267 := bstep (se 1 (by rfl) ⟨363200, by rfl⟩ : syracuseStep 484267 = 726401) B726401
theorem B681095 : Blo 401768 681095 := bstep (se 1 (by rfl) ⟨510821, by rfl⟩ : syracuseStep 681095 = 1021643) B1021643
theorem B4678829 : Blo 401768 4678829 := bstep (se 3 (by rfl) ⟨877280, by rfl⟩ : syracuseStep 4678829 = 1754561) B1754561
theorem B32531717 : Blo 401768 32531717 := bstep (se 4 (by rfl) ⟨3049848, by rfl⟩ : syracuseStep 32531717 = 6099697) B6099697
theorem B910727 : Blo 401768 910727 := bstep (se 1 (by rfl) ⟨683045, by rfl⟩ : syracuseStep 910727 = 1366091) B1366091
theorem B1533451 : Blo 401768 1533451 := bstep (se 1 (by rfl) ⟨1150088, by rfl⟩ : syracuseStep 1533451 = 2300177) B2300177
theorem B452155 : Blo 401768 452155 := bstep (se 1 (by rfl) ⟨339116, by rfl⟩ : syracuseStep 452155 = 678233) B678233
theorem B910907 : Blo 401768 910907 := bstep (se 1 (by rfl) ⟨683180, by rfl⟩ : syracuseStep 910907 = 1366361) B1366361
theorem B911033 : Blo 401768 911033 := bstep (se 2 (by rfl) ⟨341637, by rfl⟩ : syracuseStep 911033 = 683275) B683275
theorem B1402625 : Blo 401768 1402625 := bstep (se 2 (by rfl) ⟨525984, by rfl⟩ : syracuseStep 1402625 = 1051969) B1051969
theorem B681743 : Blo 401768 681743 := bstep (se 1 (by rfl) ⟨511307, by rfl⟩ : syracuseStep 681743 = 1022615) B1022615
theorem B1533755 : Blo 401768 1533755 := bstep (se 1 (by rfl) ⟨1150316, by rfl⟩ : syracuseStep 1533755 = 2300633) B2300633
theorem B452623 : Blo 401768 452623 := bstep (se 1 (by rfl) ⟨339467, by rfl⟩ : syracuseStep 452623 = 678935) B678935
theorem B911375 : Blo 401768 911375 := bstep (se 1 (by rfl) ⟨683531, by rfl⟩ : syracuseStep 911375 = 1367063) B1367063
theorem B911393 : Blo 401768 911393 := bstep (se 2 (by rfl) ⟨341772, by rfl⟩ : syracuseStep 911393 = 683545) B683545
theorem B1534241 : Blo 401768 1534241 := bstep (se 2 (by rfl) ⟨575340, by rfl⟩ : syracuseStep 1534241 = 1150681) B1150681
theorem B682283 : Blo 401768 682283 := bstep (se 1 (by rfl) ⟨511712, by rfl⟩ : syracuseStep 682283 = 1023425) B1023425
theorem B911735 : Blo 401768 911735 := bstep (se 1 (by rfl) ⟨683801, by rfl⟩ : syracuseStep 911735 = 1367603) B1367603
theorem B453127 : Blo 401768 453127 := bstep (se 1 (by rfl) ⟨339845, by rfl⟩ : syracuseStep 453127 = 679691) B679691
theorem B780815 : Blo 401768 780815 := bstep (se 1 (by rfl) ⟨585611, by rfl⟩ : syracuseStep 780815 = 1171223) B1171223
theorem B911915 : Blo 401768 911915 := bstep (se 1 (by rfl) ⟨683936, by rfl⟩ : syracuseStep 911915 = 1367873) B1367873
theorem B649847 : Blo 401768 649847 := bstep (se 1 (by rfl) ⟨487385, by rfl⟩ : syracuseStep 649847 = 974771) B974771
theorem B486059 : Blo 401768 486059 := bstep (se 1 (by rfl) ⟨364544, by rfl⟩ : syracuseStep 486059 = 729089) B729089
theorem B682681 : Blo 401768 682681 := bstep (se 2 (by rfl) ⟨256005, by rfl⟩ : syracuseStep 682681 = 512011) B512011
theorem B453307 : Blo 401768 453307 := bstep (se 1 (by rfl) ⟨339980, by rfl⟩ : syracuseStep 453307 = 679961) B679961
theorem B5499737 : Blo 401768 5499737 := bstep (se 2 (by rfl) ⟨2062401, by rfl⟩ : syracuseStep 5499737 = 4124803) B4124803
theorem B912275 : Blo 401768 912275 := bstep (se 1 (by rfl) ⟨684206, by rfl⟩ : syracuseStep 912275 = 1368413) B1368413
theorem B2911139 : Blo 401768 2911139 := bstep (se 1 (by rfl) ⟨2183354, by rfl⟩ : syracuseStep 2911139 = 4366709) B4366709
theorem B912329 : Blo 401768 912329 := bstep (se 2 (by rfl) ⟨342123, by rfl⟩ : syracuseStep 912329 = 684247) B684247
theorem B3894317 : Blo 401768 3894317 := bstep (se 3 (by rfl) ⟨730184, by rfl⟩ : syracuseStep 3894317 = 1460369) B1460369
theorem B453775 : Blo 401768 453775 := bstep (se 1 (by rfl) ⟨340331, by rfl⟩ : syracuseStep 453775 = 680663) B680663
theorem B1535213 : Blo 401768 1535213 := bstep (se 3 (by rfl) ⟨287852, by rfl⟩ : syracuseStep 1535213 = 575705) B575705
theorem B683383 : Blo 401768 683383 := bstep (se 1 (by rfl) ⟨512537, by rfl⟩ : syracuseStep 683383 = 1025075) B1025075
theorem B814607 : Blo 401768 814607 := bstep (se 1 (by rfl) ⟨610955, by rfl⟩ : syracuseStep 814607 = 1221911) B1221911
theorem B683579 : Blo 401768 683579 := bstep (se 1 (by rfl) ⟨512684, by rfl⟩ : syracuseStep 683579 = 1025369) B1025369
theorem B454279 : Blo 401768 454279 := bstep (se 1 (by rfl) ⟨340709, by rfl⟩ : syracuseStep 454279 = 681419) B681419
theorem B454459 : Blo 401768 454459 := bstep (se 1 (by rfl) ⟨340844, by rfl⟩ : syracuseStep 454459 = 681689) B681689
theorem B1732499 : Blo 401768 1732499 := bstep (se 1 (by rfl) ⟨1299374, by rfl⟩ : syracuseStep 1732499 = 2598749) B2598749
theorem B5173145 : Blo 401768 5173145 := bstep (se 2 (by rfl) ⟨1939929, by rfl⟩ : syracuseStep 5173145 = 3879859) B3879859
theorem B683977 : Blo 401768 683977 := bstep (se 2 (by rfl) ⟨256491, by rfl⟩ : syracuseStep 683977 = 512983) B512983
theorem B2191313 : Blo 401768 2191313 := bstep (se 2 (by rfl) ⟨821742, by rfl⟩ : syracuseStep 2191313 = 1643485) B1643485
theorem B4354249 : Blo 401768 4354249 := bstep (se 2 (by rfl) ⟨1632843, by rfl⟩ : syracuseStep 4354249 = 3265687) B3265687
theorem B454927 : Blo 401768 454927 := bstep (se 1 (by rfl) ⟨341195, by rfl⟩ : syracuseStep 454927 = 682391) B682391
theorem B2289971 : Blo 401768 2289971 := bstep (se 1 (by rfl) ⟨1717478, by rfl⟩ : syracuseStep 2289971 = 3434957) B3434957
theorem B1307065 : Blo 401768 1307065 := bstep (se 2 (by rfl) ⟨490149, by rfl⟩ : syracuseStep 1307065 = 980299) B980299
theorem B684679 : Blo 401768 684679 := bstep (se 1 (by rfl) ⟨513509, by rfl⟩ : syracuseStep 684679 = 1027019) B1027019
theorem B2454209 : Blo 401768 2454209 := bstep (se 2 (by rfl) ⟨920328, by rfl⟩ : syracuseStep 2454209 = 1840657) B1840657
theorem B3076865 : Blo 401768 3076865 := bstep (se 2 (by rfl) ⟨1153824, by rfl⟩ : syracuseStep 3076865 = 2307649) B2307649
theorem B455431 : Blo 401768 455431 := bstep (se 1 (by rfl) ⟨341573, by rfl⟩ : syracuseStep 455431 = 683147) B683147
theorem B455611 : Blo 401768 455611 := bstep (se 1 (by rfl) ⟨341708, by rfl⟩ : syracuseStep 455611 = 683417) B683417
theorem B1537339 : Blo 401768 1537339 := bstep (se 1 (by rfl) ⟨1153004, by rfl⟩ : syracuseStep 1537339 = 2306009) B2306009
theorem B456079 : Blo 401768 456079 := bstep (se 1 (by rfl) ⟨342059, by rfl⟩ : syracuseStep 456079 = 684119) B684119
theorem B1144439 : Blo 401768 1144439 := bstep (se 1 (by rfl) ⟨858329, by rfl⟩ : syracuseStep 1144439 = 1716659) B1716659
theorem B3864293 : Blo 401768 3864293 := bstep (se 4 (by rfl) ⟨362277, by rfl⟩ : syracuseStep 3864293 = 724555) B724555
theorem B2291429 : Blo 401768 2291429 := bstep (se 4 (by rfl) ⟨214821, by rfl⟩ : syracuseStep 2291429 = 429643) B429643
theorem B1537825 : Blo 401768 1537825 := bstep (se 2 (by rfl) ⟨576684, by rfl⟩ : syracuseStep 1537825 = 1153369) B1153369
theorem B3667801 : Blo 401768 3667801 := bstep (se 2 (by rfl) ⟨1375425, by rfl⟩ : syracuseStep 3667801 = 2750851) B2750851
theorem B2914163 : Blo 401768 2914163 := bstep (se 1 (by rfl) ⟨2185622, by rfl⟩ : syracuseStep 2914163 = 4371245) B4371245
theorem B1964119 : Blo 401768 1964119 := bstep (se 1 (by rfl) ⟨1473089, by rfl⟩ : syracuseStep 1964119 = 2946179) B2946179
theorem B2291885 : Blo 401768 2291885 := bstep (se 3 (by rfl) ⟨429728, by rfl⟩ : syracuseStep 2291885 = 859457) B859457
theorem B3439057 : Blo 401768 3439057 := bstep (se 2 (by rfl) ⟨1289646, by rfl⟩ : syracuseStep 3439057 = 2579293) B2579293
theorem B2587139 : Blo 401768 2587139 := bstep (se 1 (by rfl) ⟨1940354, by rfl⟩ : syracuseStep 2587139 = 3880709) B3880709
theorem B1538797 : Blo 401768 1538797 := bstep (se 3 (by rfl) ⟨288524, by rfl⟩ : syracuseStep 1538797 = 577049) B577049
theorem B2292569 : Blo 401768 2292569 := bstep (se 2 (by rfl) ⟨859713, by rfl⟩ : syracuseStep 2292569 = 1719427) B1719427
theorem B1539101 : Blo 401768 1539101 := bstep (se 3 (by rfl) ⟨288581, by rfl⟩ : syracuseStep 1539101 = 577163) B577163
theorem B1047809 : Blo 401768 1047809 := bstep (se 2 (by rfl) ⟨392928, by rfl⟩ : syracuseStep 1047809 = 785857) B785857
theorem B916769 : Blo 401768 916769 := bstep (se 2 (by rfl) ⟨343788, by rfl⟩ : syracuseStep 916769 = 687577) B687577
theorem B5799377 : Blo 401768 5799377 := bstep (se 2 (by rfl) ⟨2174766, by rfl⟩ : syracuseStep 5799377 = 4349533) B4349533
theorem B1769161 : Blo 401768 1769161 := bstep (se 2 (by rfl) ⟨663435, by rfl⟩ : syracuseStep 1769161 = 1326871) B1326871
theorem B1146899 : Blo 401768 1146899 := bstep (se 1 (by rfl) ⟨860174, by rfl⟩ : syracuseStep 1146899 = 1720349) B1720349
theorem B2294027 : Blo 401768 2294027 := bstep (se 1 (by rfl) ⟨1720520, by rfl⟩ : syracuseStep 2294027 = 3441041) B3441041
theorem B1147355 : Blo 401768 1147355 := bstep (se 1 (by rfl) ⟨860516, by rfl⟩ : syracuseStep 1147355 = 1721033) B1721033
theorem B1638893 : Blo 401768 1638893 := bstep (se 3 (by rfl) ⟨307292, by rfl⟩ : syracuseStep 1638893 = 614585) B614585
theorem B6980825 : Blo 401768 6980825 := bstep (se 2 (by rfl) ⟨2617809, by rfl⟩ : syracuseStep 6980825 = 5235619) B5235619
theorem B6522227 : Blo 401768 6522227 := bstep (se 1 (by rfl) ⟨4891670, by rfl⟩ : syracuseStep 6522227 = 9783341) B9783341
theorem B3868019 : Blo 401768 3868019 := bstep (se 1 (by rfl) ⟨2901014, by rfl⟩ : syracuseStep 3868019 = 5802029) B5802029
theorem B6522353 : Blo 401768 6522353 := bstep (se 2 (by rfl) ⟨2445882, by rfl⟩ : syracuseStep 6522353 = 4891765) B4891765
theorem B3671563 : Blo 401768 3671563 := bstep (se 1 (by rfl) ⟨2753672, by rfl⟩ : syracuseStep 3671563 = 5507345) B5507345
theorem B2295485 : Blo 401768 2295485 := bstep (se 3 (by rfl) ⟨430403, by rfl⟩ : syracuseStep 2295485 = 860807) B860807
theorem B1640125 : Blo 401768 1640125 := bstep (se 3 (by rfl) ⟨307523, by rfl⟩ : syracuseStep 1640125 = 615047) B615047
theorem B1017593 : Blo 401768 1017593 := bstep (se 2 (by rfl) ⟨381597, by rfl⟩ : syracuseStep 1017593 = 763195) B763195
theorem B1018241 : Blo 401768 1018241 := bstep (se 2 (by rfl) ⟨381840, by rfl⟩ : syracuseStep 1018241 = 763681) B763681
theorem B11995877 : Blo 401768 11995877 := bstep (se 4 (by rfl) ⟨1124613, by rfl⟩ : syracuseStep 11995877 = 2249227) B2249227
theorem B1019051 : Blo 401768 1019051 := bstep (se 1 (by rfl) ⟨764288, by rfl⟩ : syracuseStep 1019051 = 1528577) B1528577
theorem B920747 : Blo 401768 920747 := bstep (se 1 (by rfl) ⟨690560, by rfl⟩ : syracuseStep 920747 = 1381121) B1381121
theorem B1281367 : Blo 401768 1281367 := bstep (se 1 (by rfl) ⟨961025, by rfl⟩ : syracuseStep 1281367 = 1922051) B1922051
theorem B2297261 : Blo 401768 2297261 := bstep (se 3 (by rfl) ⟨430736, by rfl⟩ : syracuseStep 2297261 = 861473) B861473
theorem B5312087 : Blo 401768 5312087 := bstep (se 1 (by rfl) ⟨3984065, by rfl⟩ : syracuseStep 5312087 = 7968131) B7968131
theorem B8326775 : Blo 401768 8326775 := bstep (se 1 (by rfl) ⟨6245081, by rfl⟩ : syracuseStep 8326775 = 12490163) B12490163
theorem B724729 : Blo 401768 724729 := bstep (se 2 (by rfl) ⟨271773, by rfl⟩ : syracuseStep 724729 = 543547) B543547
theorem B2461549 : Blo 401768 2461549 := bstep (se 3 (by rfl) ⟨461540, by rfl⟩ : syracuseStep 2461549 = 923081) B923081
theorem B1019911 : Blo 401768 1019911 := bstep (se 1 (by rfl) ⟨764933, by rfl⟩ : syracuseStep 1019911 = 1529867) B1529867
theorem B692231 : Blo 401768 692231 := bstep (se 1 (by rfl) ⟨519173, by rfl⟩ : syracuseStep 692231 = 1038347) B1038347
theorem B1413665 : Blo 401768 1413665 := bstep (se 2 (by rfl) ⟨530124, by rfl⟩ : syracuseStep 1413665 = 1060249) B1060249
theorem B2298401 : Blo 401768 2298401 := bstep (se 2 (by rfl) ⟨861900, by rfl⟩ : syracuseStep 2298401 = 1723801) B1723801
theorem B922151 : Blo 401768 922151 := bstep (se 1 (by rfl) ⟨691613, by rfl⟩ : syracuseStep 922151 = 1383227) B1383227
theorem B1020539 : Blo 401768 1020539 := bstep (se 1 (by rfl) ⟨765404, by rfl⟩ : syracuseStep 1020539 = 1530809) B1530809
theorem B1086151 : Blo 401768 1086151 := bstep (se 1 (by rfl) ⟨814613, by rfl⟩ : syracuseStep 1086151 = 1629227) B1629227
theorem B10490579 : Blo 401768 10490579 := bstep (se 1 (by rfl) ⟨7867934, by rfl⟩ : syracuseStep 10490579 = 15735869) B15735869
theorem B1020833 : Blo 401768 1020833 := bstep (se 2 (by rfl) ⟨382812, by rfl⟩ : syracuseStep 1020833 = 765625) B765625
theorem B2036663 : Blo 401768 2036663 := bstep (se 1 (by rfl) ⟨1527497, by rfl⟩ : syracuseStep 2036663 = 3054995) B3054995
theorem B3871709 : Blo 401768 3871709 := bstep (se 3 (by rfl) ⟨725945, by rfl⟩ : syracuseStep 3871709 = 1451891) B1451891
theorem B5805665 : Blo 401768 5805665 := bstep (se 2 (by rfl) ⟨2177124, by rfl⟩ : syracuseStep 5805665 = 4354249) B4354249
theorem B1742753 : Blo 401768 1742753 := bstep (se 2 (by rfl) ⟨653532, by rfl⟩ : syracuseStep 1742753 = 1307065) B1307065
theorem B3119219 : Blo 401768 3119219 := bstep (se 1 (by rfl) ⟨2339414, by rfl⟩ : syracuseStep 3119219 = 4678829) B4678829
theorem B2038121 : Blo 401768 2038121 := bstep (se 2 (by rfl) ⟨764295, by rfl⟩ : syracuseStep 2038121 = 1528591) B1528591
theorem B4594157 : Blo 401768 4594157 := bstep (se 3 (by rfl) ⟨861404, by rfl⟩ : syracuseStep 4594157 = 1722809) B1722809
theorem B3545633 : Blo 401768 3545633 := bstep (se 2 (by rfl) ⟨1329612, by rfl⟩ : syracuseStep 3545633 = 2659225) B2659225
theorem B1022503 : Blo 401768 1022503 := bstep (se 1 (by rfl) ⟨766877, by rfl⟩ : syracuseStep 1022503 = 1533755) B1533755
theorem B1022827 : Blo 401768 1022827 := bstep (se 1 (by rfl) ⟨767120, by rfl⟩ : syracuseStep 1022827 = 1534241) B1534241
theorem B433231 : Blo 401768 433231 := bstep (se 1 (by rfl) ⟨324923, by rfl⟩ : syracuseStep 433231 = 649847) B649847
theorem B1940759 : Blo 401768 1940759 := bstep (se 1 (by rfl) ⟨1455569, by rfl⟩ : syracuseStep 1940759 = 2911139) B2911139
theorem B728425 : Blo 401768 728425 := bstep (se 2 (by rfl) ⟨273159, by rfl⟩ : syracuseStep 728425 = 546319) B546319
theorem B2596211 : Blo 401768 2596211 := bstep (se 1 (by rfl) ⟨1947158, by rfl⟩ : syracuseStep 2596211 = 3894317) B3894317
theorem B1023475 : Blo 401768 1023475 := bstep (se 1 (by rfl) ⟨767606, by rfl⟩ : syracuseStep 1023475 = 1535213) B1535213
theorem B5185241 : Blo 401768 5185241 := bstep (se 2 (by rfl) ⟨1944465, by rfl⟩ : syracuseStep 5185241 = 3888931) B3888931
theorem B4890401 : Blo 401768 4890401 := bstep (se 2 (by rfl) ⟨1833900, by rfl⟩ : syracuseStep 4890401 = 3667801) B3667801
theorem B1154999 : Blo 401768 1154999 := bstep (se 1 (by rfl) ⟨866249, by rfl⟩ : syracuseStep 1154999 = 1732499) B1732499
theorem B3448763 : Blo 401768 3448763 := bstep (se 1 (by rfl) ⟨2586572, by rfl⟩ : syracuseStep 3448763 = 5173145) B5173145
theorem B401787 : Blo 401768 401787 := bstep (se 1 (by rfl) ⟨301340, by rfl⟩ : syracuseStep 401787 = 602681) B602681
theorem B401839 : Blo 401768 401839 := bstep (se 1 (by rfl) ⟨301379, by rfl⟩ : syracuseStep 401839 = 602759) B602759
theorem B401863 : Blo 401768 401863 := bstep (se 1 (by rfl) ⟨301397, by rfl⟩ : syracuseStep 401863 = 602795) B602795
theorem B401883 : Blo 401768 401883 := bstep (se 1 (by rfl) ⟨301412, by rfl⟩ : syracuseStep 401883 = 602825) B602825
theorem B401959 : Blo 401768 401959 := bstep (se 1 (by rfl) ⟨301469, by rfl⟩ : syracuseStep 401959 = 602939) B602939
theorem B401999 : Blo 401768 401999 := bstep (se 1 (by rfl) ⟨301499, by rfl⟩ : syracuseStep 401999 = 602999) B602999
theorem B402015 : Blo 401768 402015 := bstep (se 1 (by rfl) ⟨301511, by rfl⟩ : syracuseStep 402015 = 603023) B603023
theorem B1024609 : Blo 401768 1024609 := bstep (se 2 (by rfl) ⟨384228, by rfl⟩ : syracuseStep 1024609 = 768457) B768457
theorem B402043 : Blo 401768 402043 := bstep (se 1 (by rfl) ⟨301532, by rfl⟩ : syracuseStep 402043 = 603065) B603065
theorem B402095 : Blo 401768 402095 := bstep (se 1 (by rfl) ⟨301571, by rfl⟩ : syracuseStep 402095 = 603143) B603143
theorem B402119 : Blo 401768 402119 := bstep (se 1 (by rfl) ⟨301589, by rfl⟩ : syracuseStep 402119 = 603179) B603179
theorem B402139 : Blo 401768 402139 := bstep (se 1 (by rfl) ⟨301604, by rfl⟩ : syracuseStep 402139 = 603209) B603209
theorem B402215 : Blo 401768 402215 := bstep (se 1 (by rfl) ⟨301661, by rfl⟩ : syracuseStep 402215 = 603323) B603323
theorem B402255 : Blo 401768 402255 := bstep (se 1 (by rfl) ⟨301691, by rfl⟩ : syracuseStep 402255 = 603383) B603383
theorem B402271 : Blo 401768 402271 := bstep (se 1 (by rfl) ⟨301703, by rfl⟩ : syracuseStep 402271 = 603407) B603407
theorem B402299 : Blo 401768 402299 := bstep (se 1 (by rfl) ⟨301724, by rfl⟩ : syracuseStep 402299 = 603449) B603449
theorem B402351 : Blo 401768 402351 := bstep (se 1 (by rfl) ⟨301763, by rfl⟩ : syracuseStep 402351 = 603527) B603527
theorem B402375 : Blo 401768 402375 := bstep (se 1 (by rfl) ⟨301781, by rfl⟩ : syracuseStep 402375 = 603563) B603563
theorem B402395 : Blo 401768 402395 := bstep (se 1 (by rfl) ⟨301796, by rfl⟩ : syracuseStep 402395 = 603593) B603593
theorem B402471 : Blo 401768 402471 := bstep (se 1 (by rfl) ⟨301853, by rfl⟩ : syracuseStep 402471 = 603707) B603707
theorem B762959 : Blo 401768 762959 := bstep (se 1 (by rfl) ⟨572219, by rfl⟩ : syracuseStep 762959 = 1144439) B1144439
theorem B402511 : Blo 401768 402511 := bstep (se 1 (by rfl) ⟨301883, by rfl⟩ : syracuseStep 402511 = 603767) B603767
theorem B402527 : Blo 401768 402527 := bstep (se 1 (by rfl) ⟨301895, by rfl⟩ : syracuseStep 402527 = 603791) B603791
theorem B402555 : Blo 401768 402555 := bstep (se 1 (by rfl) ⟨301916, by rfl⟩ : syracuseStep 402555 = 603833) B603833
theorem B402607 : Blo 401768 402607 := bstep (se 1 (by rfl) ⟨301955, by rfl⟩ : syracuseStep 402607 = 603911) B603911
theorem B402631 : Blo 401768 402631 := bstep (se 1 (by rfl) ⟨301973, by rfl⟩ : syracuseStep 402631 = 603947) B603947
theorem B402651 : Blo 401768 402651 := bstep (se 1 (by rfl) ⟨301988, by rfl⟩ : syracuseStep 402651 = 603977) B603977
theorem B1942775 : Blo 401768 1942775 := bstep (se 1 (by rfl) ⟨1457081, by rfl⟩ : syracuseStep 1942775 = 2914163) B2914163
theorem B402727 : Blo 401768 402727 := bstep (se 1 (by rfl) ⟨302045, by rfl⟩ : syracuseStep 402727 = 604091) B604091
theorem B402767 : Blo 401768 402767 := bstep (se 1 (by rfl) ⟨302075, by rfl⟩ : syracuseStep 402767 = 604151) B604151
theorem B402783 : Blo 401768 402783 := bstep (se 1 (by rfl) ⟨302087, by rfl⟩ : syracuseStep 402783 = 604175) B604175
theorem B402811 : Blo 401768 402811 := bstep (se 1 (by rfl) ⟨302108, by rfl⟩ : syracuseStep 402811 = 604217) B604217
theorem B1516943 : Blo 401768 1516943 := bstep (se 1 (by rfl) ⟨1137707, by rfl⟩ : syracuseStep 1516943 = 2275415) B2275415
theorem B402863 : Blo 401768 402863 := bstep (se 1 (by rfl) ⟨302147, by rfl⟩ : syracuseStep 402863 = 604295) B604295
theorem B402887 : Blo 401768 402887 := bstep (se 1 (by rfl) ⟨302165, by rfl⟩ : syracuseStep 402887 = 604331) B604331
theorem B2631113 : Blo 401768 2631113 := bstep (se 2 (by rfl) ⟨986667, by rfl⟩ : syracuseStep 2631113 = 1973335) B1973335
theorem B402907 : Blo 401768 402907 := bstep (se 1 (by rfl) ⟨302180, by rfl⟩ : syracuseStep 402907 = 604361) B604361
theorem B1025561 : Blo 401768 1025561 := bstep (se 2 (by rfl) ⟨384585, by rfl⟩ : syracuseStep 1025561 = 769171) B769171
theorem B402983 : Blo 401768 402983 := bstep (se 1 (by rfl) ⟨302237, by rfl⟩ : syracuseStep 402983 = 604475) B604475
theorem B403023 : Blo 401768 403023 := bstep (se 1 (by rfl) ⟨302267, by rfl⟩ : syracuseStep 403023 = 604535) B604535
theorem B403039 : Blo 401768 403039 := bstep (se 1 (by rfl) ⟨302279, by rfl⟩ : syracuseStep 403039 = 604559) B604559
theorem B403067 : Blo 401768 403067 := bstep (se 1 (by rfl) ⟨302300, by rfl⟩ : syracuseStep 403067 = 604601) B604601
theorem B403119 : Blo 401768 403119 := bstep (se 1 (by rfl) ⟨302339, by rfl⟩ : syracuseStep 403119 = 604679) B604679
theorem B403143 : Blo 401768 403143 := bstep (se 1 (by rfl) ⟨302357, by rfl⟩ : syracuseStep 403143 = 604715) B604715
theorem B403163 : Blo 401768 403163 := bstep (se 1 (by rfl) ⟨302372, by rfl⟩ : syracuseStep 403163 = 604745) B604745
theorem B403239 : Blo 401768 403239 := bstep (se 1 (by rfl) ⟨302429, by rfl⟩ : syracuseStep 403239 = 604859) B604859
theorem B403279 : Blo 401768 403279 := bstep (se 1 (by rfl) ⟨302459, by rfl⟩ : syracuseStep 403279 = 604919) B604919
theorem B403295 : Blo 401768 403295 := bstep (se 1 (by rfl) ⟨302471, by rfl⟩ : syracuseStep 403295 = 604943) B604943
theorem B403323 : Blo 401768 403323 := bstep (se 1 (by rfl) ⟨302492, by rfl⟩ : syracuseStep 403323 = 604985) B604985
theorem B403375 : Blo 401768 403375 := bstep (se 1 (by rfl) ⟨302531, by rfl⟩ : syracuseStep 403375 = 605063) B605063
theorem B403399 : Blo 401768 403399 := bstep (se 1 (by rfl) ⟨302549, by rfl⟩ : syracuseStep 403399 = 605099) B605099
theorem B403419 : Blo 401768 403419 := bstep (se 1 (by rfl) ⟨302564, by rfl⟩ : syracuseStep 403419 = 605129) B605129
theorem B1026067 : Blo 401768 1026067 := bstep (se 1 (by rfl) ⟨769550, by rfl⟩ : syracuseStep 1026067 = 1539101) B1539101
theorem B403495 : Blo 401768 403495 := bstep (se 1 (by rfl) ⟨302621, by rfl⟩ : syracuseStep 403495 = 605243) B605243
theorem B403535 : Blo 401768 403535 := bstep (se 1 (by rfl) ⟨302651, by rfl⟩ : syracuseStep 403535 = 605303) B605303
theorem B403551 : Blo 401768 403551 := bstep (se 1 (by rfl) ⟨302663, by rfl⟩ : syracuseStep 403551 = 605327) B605327
theorem B403579 : Blo 401768 403579 := bstep (se 1 (by rfl) ⟨302684, by rfl⟩ : syracuseStep 403579 = 605369) B605369
theorem B698539 : Blo 401768 698539 := bstep (se 1 (by rfl) ⟨523904, by rfl⟩ : syracuseStep 698539 = 1047809) B1047809
theorem B403631 : Blo 401768 403631 := bstep (se 1 (by rfl) ⟨302723, by rfl⟩ : syracuseStep 403631 = 605447) B605447
theorem B403655 : Blo 401768 403655 := bstep (se 1 (by rfl) ⟨302741, by rfl⟩ : syracuseStep 403655 = 605483) B605483
theorem B403675 : Blo 401768 403675 := bstep (se 1 (by rfl) ⟨302756, by rfl⟩ : syracuseStep 403675 = 605513) B605513
theorem B6564077 : Blo 401768 6564077 := bstep (se 3 (by rfl) ⟨1230764, by rfl⟩ : syracuseStep 6564077 = 2461529) B2461529
theorem B403751 : Blo 401768 403751 := bstep (se 1 (by rfl) ⟨302813, by rfl⟩ : syracuseStep 403751 = 605627) B605627
theorem B403791 : Blo 401768 403791 := bstep (se 1 (by rfl) ⟨302843, by rfl⟩ : syracuseStep 403791 = 605687) B605687
theorem B403807 : Blo 401768 403807 := bstep (se 1 (by rfl) ⟨302855, by rfl⟩ : syracuseStep 403807 = 605711) B605711
theorem B403835 : Blo 401768 403835 := bstep (se 1 (by rfl) ⟨302876, by rfl⟩ : syracuseStep 403835 = 605753) B605753
theorem B403887 : Blo 401768 403887 := bstep (se 1 (by rfl) ⟨302915, by rfl⟩ : syracuseStep 403887 = 605831) B605831
theorem B403911 : Blo 401768 403911 := bstep (se 1 (by rfl) ⟨302933, by rfl⟩ : syracuseStep 403911 = 605867) B605867
theorem B1288649 : Blo 401768 1288649 := bstep (se 2 (by rfl) ⟨483243, by rfl⟩ : syracuseStep 1288649 = 966487) B966487
theorem B1386953 : Blo 401768 1386953 := bstep (se 2 (by rfl) ⟨520107, by rfl⟩ : syracuseStep 1386953 = 1040215) B1040215
theorem B403931 : Blo 401768 403931 := bstep (se 1 (by rfl) ⟨302948, by rfl⟩ : syracuseStep 403931 = 605897) B605897
theorem B404007 : Blo 401768 404007 := bstep (se 1 (by rfl) ⟨303005, by rfl⟩ : syracuseStep 404007 = 606011) B606011
theorem B404047 : Blo 401768 404047 := bstep (se 1 (by rfl) ⟨303035, by rfl⟩ : syracuseStep 404047 = 606071) B606071
theorem B404063 : Blo 401768 404063 := bstep (se 1 (by rfl) ⟨303047, by rfl⟩ : syracuseStep 404063 = 606095) B606095
theorem B404091 : Blo 401768 404091 := bstep (se 1 (by rfl) ⟨303068, by rfl⟩ : syracuseStep 404091 = 606137) B606137
theorem B404143 : Blo 401768 404143 := bstep (se 1 (by rfl) ⟨303107, by rfl⟩ : syracuseStep 404143 = 606215) B606215
theorem B764615 : Blo 401768 764615 := bstep (se 1 (by rfl) ⟨573461, by rfl⟩ : syracuseStep 764615 = 1146923) B1146923
theorem B404167 : Blo 401768 404167 := bstep (se 1 (by rfl) ⟨303125, by rfl⟩ : syracuseStep 404167 = 606251) B606251
theorem B404187 : Blo 401768 404187 := bstep (se 1 (by rfl) ⟨303140, by rfl⟩ : syracuseStep 404187 = 606281) B606281
theorem B862969 : Blo 401768 862969 := bstep (se 2 (by rfl) ⟨323613, by rfl⟩ : syracuseStep 862969 = 647227) B647227
theorem B404263 : Blo 401768 404263 := bstep (se 1 (by rfl) ⟨303197, by rfl⟩ : syracuseStep 404263 = 606395) B606395
theorem B404303 : Blo 401768 404303 := bstep (se 1 (by rfl) ⟨303227, by rfl⟩ : syracuseStep 404303 = 606455) B606455
theorem B404319 : Blo 401768 404319 := bstep (se 1 (by rfl) ⟨303239, by rfl⟩ : syracuseStep 404319 = 606479) B606479
theorem B404347 : Blo 401768 404347 := bstep (se 1 (by rfl) ⟨303260, by rfl⟩ : syracuseStep 404347 = 606521) B606521
theorem B1289135 : Blo 401768 1289135 := bstep (se 1 (by rfl) ⟨966851, by rfl⟩ : syracuseStep 1289135 = 1933703) B1933703
theorem B404399 : Blo 401768 404399 := bstep (se 1 (by rfl) ⟨303299, by rfl⟩ : syracuseStep 404399 = 606599) B606599
theorem B404423 : Blo 401768 404423 := bstep (se 1 (by rfl) ⟨303317, by rfl⟩ : syracuseStep 404423 = 606635) B606635
theorem B404443 : Blo 401768 404443 := bstep (se 1 (by rfl) ⟨303332, by rfl⟩ : syracuseStep 404443 = 606665) B606665
theorem B404519 : Blo 401768 404519 := bstep (se 1 (by rfl) ⟨303389, by rfl⟩ : syracuseStep 404519 = 606779) B606779
theorem B863311 : Blo 401768 863311 := bstep (se 1 (by rfl) ⟨647483, by rfl⟩ : syracuseStep 863311 = 1294967) B1294967
theorem B404559 : Blo 401768 404559 := bstep (se 1 (by rfl) ⟨303419, by rfl⟩ : syracuseStep 404559 = 606839) B606839
theorem B404575 : Blo 401768 404575 := bstep (se 1 (by rfl) ⟨303431, by rfl⟩ : syracuseStep 404575 = 606863) B606863
theorem B404603 : Blo 401768 404603 := bstep (se 1 (by rfl) ⟨303452, by rfl⟩ : syracuseStep 404603 = 606905) B606905
theorem B404655 : Blo 401768 404655 := bstep (se 1 (by rfl) ⟨303491, by rfl⟩ : syracuseStep 404655 = 606983) B606983
theorem B3058883 : Blo 401768 3058883 := bstep (se 1 (by rfl) ⟨2294162, by rfl⟩ : syracuseStep 3058883 = 4588325) B4588325
theorem B404679 : Blo 401768 404679 := bstep (se 1 (by rfl) ⟨303509, by rfl⟩ : syracuseStep 404679 = 607019) B607019
theorem B765139 : Blo 401768 765139 := bstep (se 1 (by rfl) ⟨573854, by rfl⟩ : syracuseStep 765139 = 1147709) B1147709
theorem B404699 : Blo 401768 404699 := bstep (se 1 (by rfl) ⟨303524, by rfl⟩ : syracuseStep 404699 = 607049) B607049
theorem B7384355 : Blo 401768 7384355 := bstep (se 1 (by rfl) ⟨5538266, by rfl⟩ : syracuseStep 7384355 = 11076533) B11076533
theorem B404775 : Blo 401768 404775 := bstep (se 1 (by rfl) ⟨303581, by rfl⟩ : syracuseStep 404775 = 607163) B607163
theorem B1289533 : Blo 401768 1289533 := bstep (se 3 (by rfl) ⟨241787, by rfl⟩ : syracuseStep 1289533 = 483575) B483575
theorem B404815 : Blo 401768 404815 := bstep (se 1 (by rfl) ⟨303611, by rfl⟩ : syracuseStep 404815 = 607223) B607223
theorem B404831 : Blo 401768 404831 := bstep (se 1 (by rfl) ⟨303623, by rfl⟩ : syracuseStep 404831 = 607247) B607247
theorem B404859 : Blo 401768 404859 := bstep (se 1 (by rfl) ⟨303644, by rfl⟩ : syracuseStep 404859 = 607289) B607289
theorem B765359 : Blo 401768 765359 := bstep (se 1 (by rfl) ⟨574019, by rfl⟩ : syracuseStep 765359 = 1148039) B1148039
theorem B404911 : Blo 401768 404911 := bstep (se 1 (by rfl) ⟨303683, by rfl⟩ : syracuseStep 404911 = 607367) B607367
theorem B404935 : Blo 401768 404935 := bstep (se 1 (by rfl) ⟨303701, by rfl⟩ : syracuseStep 404935 = 607403) B607403
theorem B404955 : Blo 401768 404955 := bstep (se 1 (by rfl) ⟨303716, by rfl⟩ : syracuseStep 404955 = 607433) B607433
theorem B405031 : Blo 401768 405031 := bstep (se 1 (by rfl) ⟨303773, by rfl⟩ : syracuseStep 405031 = 607547) B607547
theorem B405071 : Blo 401768 405071 := bstep (se 1 (by rfl) ⟨303803, by rfl⟩ : syracuseStep 405071 = 607607) B607607
theorem B405087 : Blo 401768 405087 := bstep (se 1 (by rfl) ⟨303815, by rfl⟩ : syracuseStep 405087 = 607631) B607631
theorem B405115 : Blo 401768 405115 := bstep (se 1 (by rfl) ⟨303836, by rfl⟩ : syracuseStep 405115 = 607673) B607673
theorem B1945235 : Blo 401768 1945235 := bstep (se 1 (by rfl) ⟨1458926, by rfl⟩ : syracuseStep 1945235 = 2917853) B2917853
theorem B405167 : Blo 401768 405167 := bstep (se 1 (by rfl) ⟨303875, by rfl⟩ : syracuseStep 405167 = 607751) B607751
theorem B405191 : Blo 401768 405191 := bstep (se 1 (by rfl) ⟨303893, by rfl⟩ : syracuseStep 405191 = 607787) B607787
theorem B405211 : Blo 401768 405211 := bstep (se 1 (by rfl) ⟨303908, by rfl⟩ : syracuseStep 405211 = 607817) B607817
theorem B405287 : Blo 401768 405287 := bstep (se 1 (by rfl) ⟨303965, by rfl⟩ : syracuseStep 405287 = 607931) B607931
theorem B765769 : Blo 401768 765769 := bstep (se 2 (by rfl) ⟨287163, by rfl⟩ : syracuseStep 765769 = 574327) B574327
theorem B405327 : Blo 401768 405327 := bstep (se 1 (by rfl) ⟨303995, by rfl⟩ : syracuseStep 405327 = 607991) B607991
theorem B1552223 : Blo 401768 1552223 := bstep (se 1 (by rfl) ⟨1164167, by rfl⟩ : syracuseStep 1552223 = 2328335) B2328335
theorem B405343 : Blo 401768 405343 := bstep (se 1 (by rfl) ⟨304007, by rfl⟩ : syracuseStep 405343 = 608015) B608015
theorem B405371 : Blo 401768 405371 := bstep (se 1 (by rfl) ⟨304028, by rfl⟩ : syracuseStep 405371 = 608057) B608057
theorem B405423 : Blo 401768 405423 := bstep (se 1 (by rfl) ⟨304067, by rfl⟩ : syracuseStep 405423 = 608135) B608135
theorem B6565819 : Blo 401768 6565819 := bstep (se 1 (by rfl) ⟨4924364, by rfl⟩ : syracuseStep 6565819 = 9848729) B9848729
theorem B405447 : Blo 401768 405447 := bstep (se 1 (by rfl) ⟨304085, by rfl⟩ : syracuseStep 405447 = 608171) B608171
theorem B405467 : Blo 401768 405467 := bstep (se 1 (by rfl) ⟨304100, by rfl⟩ : syracuseStep 405467 = 608201) B608201
theorem B5451781 : Blo 401768 5451781 := bstep (se 4 (by rfl) ⟨511104, by rfl⟩ : syracuseStep 5451781 = 1022209) B1022209
theorem B864275 : Blo 401768 864275 := bstep (se 1 (by rfl) ⟨648206, by rfl⟩ : syracuseStep 864275 = 1296413) B1296413
theorem B405543 : Blo 401768 405543 := bstep (se 1 (by rfl) ⟨304157, by rfl⟩ : syracuseStep 405543 = 608315) B608315
theorem B7385165 : Blo 401768 7385165 := bstep (se 3 (by rfl) ⟨1384718, by rfl⟩ : syracuseStep 7385165 = 2769437) B2769437
theorem B405583 : Blo 401768 405583 := bstep (se 1 (by rfl) ⟨304187, by rfl⟩ : syracuseStep 405583 = 608375) B608375
theorem B405599 : Blo 401768 405599 := bstep (se 1 (by rfl) ⟨304199, by rfl⟩ : syracuseStep 405599 = 608399) B608399
theorem B405627 : Blo 401768 405627 := bstep (se 1 (by rfl) ⟨304220, by rfl⟩ : syracuseStep 405627 = 608441) B608441
theorem B405679 : Blo 401768 405679 := bstep (se 1 (by rfl) ⟨304259, by rfl⟩ : syracuseStep 405679 = 608519) B608519
theorem B405703 : Blo 401768 405703 := bstep (se 1 (by rfl) ⟨304277, by rfl⟩ : syracuseStep 405703 = 608555) B608555
theorem B405723 : Blo 401768 405723 := bstep (se 1 (by rfl) ⟨304292, by rfl⟩ : syracuseStep 405723 = 608585) B608585
theorem B602663 : Blo 401768 602663 := bstep (se 1 (by rfl) ⟨451997, by rfl⟩ : syracuseStep 602663 = 903995) B903995
theorem B1454689 : Blo 401768 1454689 := bstep (se 2 (by rfl) ⟨545508, by rfl⟩ : syracuseStep 1454689 = 1091017) B1091017
theorem B602747 : Blo 401768 602747 := bstep (se 1 (by rfl) ⟨452060, by rfl⟩ : syracuseStep 602747 = 904121) B904121
theorem B2044601 : Blo 401768 2044601 := bstep (se 2 (by rfl) ⟨766725, by rfl⟩ : syracuseStep 2044601 = 1533451) B1533451
theorem B602873 : Blo 401768 602873 := bstep (se 2 (by rfl) ⟨226077, by rfl⟩ : syracuseStep 602873 = 452155) B452155
theorem B1356587 : Blo 401768 1356587 := bstep (se 1 (by rfl) ⟨1017440, by rfl⟩ : syracuseStep 1356587 = 2034881) B2034881
theorem B1454921 : Blo 401768 1454921 := bstep (se 2 (by rfl) ⟨545595, by rfl⟩ : syracuseStep 1454921 = 1091191) B1091191
theorem B602975 : Blo 401768 602975 := bstep (se 1 (by rfl) ⟨452231, by rfl⟩ : syracuseStep 602975 = 904463) B904463
theorem B602987 : Blo 401768 602987 := bstep (se 1 (by rfl) ⟨452240, by rfl⟩ : syracuseStep 602987 = 904481) B904481
theorem B1356857 : Blo 401768 1356857 := bstep (se 2 (by rfl) ⟨508821, by rfl⟩ : syracuseStep 1356857 = 1017643) B1017643
theorem B603215 : Blo 401768 603215 := bstep (se 1 (by rfl) ⟨452411, by rfl⟩ : syracuseStep 603215 = 904823) B904823
theorem B603335 : Blo 401768 603335 := bstep (se 1 (by rfl) ⟨452501, by rfl⟩ : syracuseStep 603335 = 905003) B905003
theorem B603497 : Blo 401768 603497 := bstep (se 2 (by rfl) ⟨226311, by rfl⟩ : syracuseStep 603497 = 452623) B452623
theorem B1357181 : Blo 401768 1357181 := bstep (se 3 (by rfl) ⟨254471, by rfl⟩ : syracuseStep 1357181 = 508943) B508943
theorem B603575 : Blo 401768 603575 := bstep (se 1 (by rfl) ⟨452681, by rfl⟩ : syracuseStep 603575 = 905363) B905363
theorem B603611 : Blo 401768 603611 := bstep (se 1 (by rfl) ⟨452708, by rfl⟩ : syracuseStep 603611 = 905417) B905417
theorem B5518891 : Blo 401768 5518891 := bstep (se 1 (by rfl) ⟨4139168, by rfl⟩ : syracuseStep 5518891 = 8278337) B8278337
theorem B1357451 : Blo 401768 1357451 := bstep (se 1 (by rfl) ⟨1018088, by rfl⟩ : syracuseStep 1357451 = 2036177) B2036177
theorem B866155 : Blo 401768 866155 := bstep (se 1 (by rfl) ⟨649616, by rfl⟩ : syracuseStep 866155 = 1299233) B1299233
theorem B604079 : Blo 401768 604079 := bstep (se 1 (by rfl) ⟨453059, by rfl⟩ : syracuseStep 604079 = 906119) B906119
theorem B2176955 : Blo 401768 2176955 := bstep (se 1 (by rfl) ⟨1632716, by rfl⟩ : syracuseStep 2176955 = 3265433) B3265433
theorem B3454913 : Blo 401768 3454913 := bstep (se 2 (by rfl) ⟨1295592, by rfl⟩ : syracuseStep 3454913 = 2591185) B2591185
theorem B604169 : Blo 401768 604169 := bstep (se 2 (by rfl) ⟨226563, by rfl⟩ : syracuseStep 604169 = 453127) B453127
theorem B86751245 : Blo 401768 86751245 := bstep (se 3 (by rfl) ⟨16265858, by rfl⟩ : syracuseStep 86751245 = 32531717) B32531717
theorem B604199 : Blo 401768 604199 := bstep (se 1 (by rfl) ⟨453149, by rfl⟩ : syracuseStep 604199 = 906299) B906299
theorem B14727257 : Blo 401768 14727257 := bstep (se 2 (by rfl) ⟨5522721, by rfl⟩ : syracuseStep 14727257 = 11045443) B11045443
theorem B604283 : Blo 401768 604283 := bstep (se 1 (by rfl) ⟨453212, by rfl⟩ : syracuseStep 604283 = 906425) B906425
theorem B768199 : Blo 401768 768199 := bstep (se 1 (by rfl) ⟨576149, by rfl⟩ : syracuseStep 768199 = 1152299) B1152299
theorem B604409 : Blo 401768 604409 := bstep (se 2 (by rfl) ⟨226653, by rfl⟩ : syracuseStep 604409 = 453307) B453307
theorem B604511 : Blo 401768 604511 := bstep (se 1 (by rfl) ⟨453383, by rfl⟩ : syracuseStep 604511 = 906767) B906767
theorem B604523 : Blo 401768 604523 := bstep (se 1 (by rfl) ⟨453392, by rfl⟩ : syracuseStep 604523 = 906785) B906785
theorem B1358369 : Blo 401768 1358369 := bstep (se 2 (by rfl) ⟨509388, by rfl⟩ : syracuseStep 1358369 = 1018777) B1018777
theorem B1456679 : Blo 401768 1456679 := bstep (se 1 (by rfl) ⟨1092509, by rfl⟩ : syracuseStep 1456679 = 2185019) B2185019
theorem B604751 : Blo 401768 604751 := bstep (se 1 (by rfl) ⟨453563, by rfl⟩ : syracuseStep 604751 = 907127) B907127
theorem B604871 : Blo 401768 604871 := bstep (se 1 (by rfl) ⟨453653, by rfl⟩ : syracuseStep 604871 = 907307) B907307
theorem B1358585 : Blo 401768 1358585 := bstep (se 2 (by rfl) ⟨509469, by rfl⟩ : syracuseStep 1358585 = 1018939) B1018939
theorem B768761 : Blo 401768 768761 := bstep (se 2 (by rfl) ⟨288285, by rfl⟩ : syracuseStep 768761 = 576571) B576571
theorem B605033 : Blo 401768 605033 := bstep (se 2 (by rfl) ⟨226887, by rfl⟩ : syracuseStep 605033 = 453775) B453775
theorem B768943 : Blo 401768 768943 := bstep (se 1 (by rfl) ⟨576707, by rfl⟩ : syracuseStep 768943 = 1153415) B1153415
theorem B605111 : Blo 401768 605111 := bstep (se 1 (by rfl) ⟨453833, by rfl⟩ : syracuseStep 605111 = 907667) B907667
theorem B605147 : Blo 401768 605147 := bstep (se 1 (by rfl) ⟨453860, by rfl⟩ : syracuseStep 605147 = 907721) B907721
theorem B1358855 : Blo 401768 1358855 := bstep (se 1 (by rfl) ⟨1019141, by rfl⟩ : syracuseStep 1358855 = 2038283) B2038283
theorem B1162297 : Blo 401768 1162297 := bstep (se 2 (by rfl) ⟨435861, by rfl⟩ : syracuseStep 1162297 = 871723) B871723
theorem B1358963 : Blo 401768 1358963 := bstep (se 1 (by rfl) ⟨1019222, by rfl⟩ : syracuseStep 1358963 = 2038445) B2038445
theorem B1359233 : Blo 401768 1359233 := bstep (se 2 (by rfl) ⟨509712, by rfl⟩ : syracuseStep 1359233 = 1019425) B1019425
theorem B605615 : Blo 401768 605615 := bstep (se 1 (by rfl) ⟨454211, by rfl⟩ : syracuseStep 605615 = 908423) B908423
theorem B605705 : Blo 401768 605705 := bstep (se 2 (by rfl) ⟨227139, by rfl⟩ : syracuseStep 605705 = 454279) B454279
theorem B1228297 : Blo 401768 1228297 := bstep (se 2 (by rfl) ⟨460611, by rfl⟩ : syracuseStep 1228297 = 921223) B921223
theorem B605735 : Blo 401768 605735 := bstep (se 1 (by rfl) ⟨454301, by rfl⟩ : syracuseStep 605735 = 908603) B908603
theorem B605819 : Blo 401768 605819 := bstep (se 1 (by rfl) ⟨454364, by rfl⟩ : syracuseStep 605819 = 908729) B908729
theorem B1457875 : Blo 401768 1457875 := bstep (se 1 (by rfl) ⟨1093406, by rfl⟩ : syracuseStep 1457875 = 2186813) B2186813
theorem B605945 : Blo 401768 605945 := bstep (se 2 (by rfl) ⟨227229, by rfl⟩ : syracuseStep 605945 = 454459) B454459
theorem B606047 : Blo 401768 606047 := bstep (se 1 (by rfl) ⟨454535, by rfl⟩ : syracuseStep 606047 = 909071) B909071
theorem B606059 : Blo 401768 606059 := bstep (se 1 (by rfl) ⟨454544, by rfl⟩ : syracuseStep 606059 = 909089) B909089
theorem B1458107 : Blo 401768 1458107 := bstep (se 1 (by rfl) ⟨1093580, by rfl⟩ : syracuseStep 1458107 = 2187161) B2187161
theorem B606287 : Blo 401768 606287 := bstep (se 1 (by rfl) ⟨454715, by rfl⟩ : syracuseStep 606287 = 909431) B909431
theorem B1360043 : Blo 401768 1360043 := bstep (se 1 (by rfl) ⟨1020032, by rfl⟩ : syracuseStep 1360043 = 2040065) B2040065
theorem B770219 : Blo 401768 770219 := bstep (se 1 (by rfl) ⟨577664, by rfl⟩ : syracuseStep 770219 = 1155329) B1155329
theorem B606407 : Blo 401768 606407 := bstep (se 1 (by rfl) ⟨454805, by rfl⟩ : syracuseStep 606407 = 909611) B909611
theorem B573689 : Blo 401768 573689 := bstep (se 2 (by rfl) ⟨215133, by rfl⟩ : syracuseStep 573689 = 430267) B430267
theorem B1294697 : Blo 401768 1294697 := bstep (se 2 (by rfl) ⟨485511, by rfl⟩ : syracuseStep 1294697 = 971023) B971023
theorem B606569 : Blo 401768 606569 := bstep (se 2 (by rfl) ⟨227463, by rfl⟩ : syracuseStep 606569 = 454927) B454927
theorem B606647 : Blo 401768 606647 := bstep (se 1 (by rfl) ⟨454985, by rfl⟩ : syracuseStep 606647 = 909971) B909971
theorem B606683 : Blo 401768 606683 := bstep (se 1 (by rfl) ⟨455012, by rfl⟩ : syracuseStep 606683 = 910025) B910025
theorem B1360583 : Blo 401768 1360583 := bstep (se 1 (by rfl) ⟨1020437, by rfl⟩ : syracuseStep 1360583 = 2040875) B2040875
theorem B607151 : Blo 401768 607151 := bstep (se 1 (by rfl) ⟨455363, by rfl⟩ : syracuseStep 607151 = 910727) B910727
theorem B607241 : Blo 401768 607241 := bstep (se 2 (by rfl) ⟨227715, by rfl⟩ : syracuseStep 607241 = 455431) B455431
theorem B607271 : Blo 401768 607271 := bstep (se 1 (by rfl) ⟨455453, by rfl⟩ : syracuseStep 607271 = 910907) B910907
theorem B574543 : Blo 401768 574543 := bstep (se 1 (by rfl) ⟨430907, by rfl⟩ : syracuseStep 574543 = 861815) B861815
theorem B607355 : Blo 401768 607355 := bstep (se 1 (by rfl) ⟨455516, by rfl⟩ : syracuseStep 607355 = 911033) B911033
theorem B935083 : Blo 401768 935083 := bstep (se 1 (by rfl) ⟨701312, by rfl⟩ : syracuseStep 935083 = 1402625) B1402625
theorem B607481 : Blo 401768 607481 := bstep (se 2 (by rfl) ⟨227805, by rfl⟩ : syracuseStep 607481 = 455611) B455611
theorem B607583 : Blo 401768 607583 := bstep (se 1 (by rfl) ⟨455687, by rfl⟩ : syracuseStep 607583 = 911375) B911375
theorem B1459561 : Blo 401768 1459561 := bstep (se 2 (by rfl) ⟨547335, by rfl⟩ : syracuseStep 1459561 = 1094671) B1094671
theorem B607595 : Blo 401768 607595 := bstep (se 1 (by rfl) ⟨455696, by rfl⟩ : syracuseStep 607595 = 911393) B911393
theorem B1459721 : Blo 401768 1459721 := bstep (se 2 (by rfl) ⟨547395, by rfl⟩ : syracuseStep 1459721 = 1094791) B1094791
theorem B1361447 : Blo 401768 1361447 := bstep (se 1 (by rfl) ⟨1021085, by rfl⟩ : syracuseStep 1361447 = 2042171) B2042171
theorem B607823 : Blo 401768 607823 := bstep (se 1 (by rfl) ⟨455867, by rfl⟩ : syracuseStep 607823 = 911735) B911735
theorem B1361555 : Blo 401768 1361555 := bstep (se 1 (by rfl) ⟨1021166, by rfl⟩ : syracuseStep 1361555 = 2042333) B2042333
theorem B607943 : Blo 401768 607943 := bstep (se 1 (by rfl) ⟨455957, by rfl⟩ : syracuseStep 607943 = 911915) B911915
theorem B2049785 : Blo 401768 2049785 := bstep (se 2 (by rfl) ⟨768669, by rfl⟩ : syracuseStep 2049785 = 1537339) B1537339
theorem B1296157 : Blo 401768 1296157 := bstep (se 3 (by rfl) ⟨243029, by rfl⟩ : syracuseStep 1296157 = 486059) B486059
theorem B608105 : Blo 401768 608105 := bstep (se 2 (by rfl) ⟨228039, by rfl⟩ : syracuseStep 608105 = 456079) B456079
theorem B1361771 : Blo 401768 1361771 := bstep (se 1 (by rfl) ⟨1021328, by rfl⟩ : syracuseStep 1361771 = 2042657) B2042657
theorem B1361825 : Blo 401768 1361825 := bstep (se 2 (by rfl) ⟨510684, by rfl⟩ : syracuseStep 1361825 = 1021369) B1021369
theorem B608183 : Blo 401768 608183 := bstep (se 1 (by rfl) ⟨456137, by rfl⟩ : syracuseStep 608183 = 912275) B912275
theorem B509915 : Blo 401768 509915 := bstep (se 1 (by rfl) ⟨382436, by rfl⟩ : syracuseStep 509915 = 764873) B764873
theorem B608219 : Blo 401768 608219 := bstep (se 1 (by rfl) ⟨456164, by rfl⟩ : syracuseStep 608219 = 912329) B912329
theorem B3066173 : Blo 401768 3066173 := bstep (se 3 (by rfl) ⟨574907, by rfl⟩ : syracuseStep 3066173 = 1149815) B1149815
theorem B543071 : Blo 401768 543071 := bstep (se 1 (by rfl) ⟨407303, by rfl⟩ : syracuseStep 543071 = 814607) B814607
theorem B2050433 : Blo 401768 2050433 := bstep (se 2 (by rfl) ⟨768912, by rfl⟩ : syracuseStep 2050433 = 1537825) B1537825
theorem B16566707 : Blo 401768 16566707 := bstep (se 1 (by rfl) ⟨12425030, by rfl⟩ : syracuseStep 16566707 = 24850061) B24850061
theorem B510391 : Blo 401768 510391 := bstep (se 1 (by rfl) ⟨382793, by rfl⟩ : syracuseStep 510391 = 765587) B765587
theorem B1362419 : Blo 401768 1362419 := bstep (se 1 (by rfl) ⟨1021814, by rfl⟩ : syracuseStep 1362419 = 2043629) B2043629
theorem B1460875 : Blo 401768 1460875 := bstep (se 1 (by rfl) ⟨1095656, by rfl⟩ : syracuseStep 1460875 = 2191313) B2191313
theorem B904031 : Blo 401768 904031 := bstep (se 1 (by rfl) ⟨678023, by rfl⟩ : syracuseStep 904031 = 1356047) B1356047
theorem B1526647 : Blo 401768 1526647 := bstep (se 1 (by rfl) ⟨1144985, by rfl⟩ : syracuseStep 1526647 = 2289971) B2289971
theorem B1362959 : Blo 401768 1362959 := bstep (se 1 (by rfl) ⟨1022219, by rfl⟩ : syracuseStep 1362959 = 2044439) B2044439
theorem B904211 : Blo 401768 904211 := bstep (se 1 (by rfl) ⟨678158, by rfl⟩ : syracuseStep 904211 = 1356317) B1356317
theorem B2051243 : Blo 401768 2051243 := bstep (se 1 (by rfl) ⟨1538432, by rfl⟩ : syracuseStep 2051243 = 3076865) B3076865
theorem B904553 : Blo 401768 904553 := bstep (se 2 (by rfl) ⟨339207, by rfl⟩ : syracuseStep 904553 = 678415) B678415
theorem B2444717 : Blo 401768 2444717 := bstep (se 3 (by rfl) ⟨458384, by rfl⟩ : syracuseStep 2444717 = 916769) B916769
theorem B1363553 : Blo 401768 1363553 := bstep (se 2 (by rfl) ⟨511332, by rfl⟩ : syracuseStep 1363553 = 1022665) B1022665
theorem B2051729 : Blo 401768 2051729 := bstep (se 2 (by rfl) ⟨769398, by rfl⟩ : syracuseStep 2051729 = 1538797) B1538797
theorem B511687 : Blo 401768 511687 := bstep (se 1 (by rfl) ⟨383765, by rfl⟩ : syracuseStep 511687 = 767531) B767531
theorem B2576195 : Blo 401768 2576195 := bstep (se 1 (by rfl) ⟨1932146, by rfl⟩ : syracuseStep 2576195 = 3864293) B3864293
theorem B1527619 : Blo 401768 1527619 := bstep (se 1 (by rfl) ⟨1145714, by rfl⟩ : syracuseStep 1527619 = 2291429) B2291429
theorem B905147 : Blo 401768 905147 := bstep (se 1 (by rfl) ⟨678860, by rfl⟩ : syracuseStep 905147 = 1357721) B1357721
theorem B905273 : Blo 401768 905273 := bstep (se 2 (by rfl) ⟨339477, by rfl⟩ : syracuseStep 905273 = 678955) B678955
theorem B3461201 : Blo 401768 3461201 := bstep (se 2 (by rfl) ⟨1297950, by rfl⟩ : syracuseStep 3461201 = 2595901) B2595901
theorem B1527923 : Blo 401768 1527923 := bstep (se 1 (by rfl) ⟨1145942, by rfl⟩ : syracuseStep 1527923 = 2291885) B2291885
theorem B4378853 : Blo 401768 4378853 := bstep (se 4 (by rfl) ⟨410517, by rfl⟩ : syracuseStep 4378853 = 821035) B821035
theorem B1724759 : Blo 401768 1724759 := bstep (se 1 (by rfl) ⟨1293569, by rfl⟩ : syracuseStep 1724759 = 2587139) B2587139
theorem B905615 : Blo 401768 905615 := bstep (se 1 (by rfl) ⟨679211, by rfl⟩ : syracuseStep 905615 = 1358423) B1358423
theorem B2904473 : Blo 401768 2904473 := bstep (se 2 (by rfl) ⟨1089177, by rfl⟩ : syracuseStep 2904473 = 2178355) B2178355
theorem B1528379 : Blo 401768 1528379 := bstep (se 1 (by rfl) ⟨1146284, by rfl⟩ : syracuseStep 1528379 = 2292569) B2292569
theorem B905939 : Blo 401768 905939 := bstep (se 1 (by rfl) ⟨679454, by rfl⟩ : syracuseStep 905939 = 1358909) B1358909
theorem B1233623 : Blo 401768 1233623 := bstep (se 1 (by rfl) ⟨925217, by rfl⟩ : syracuseStep 1233623 = 1850435) B1850435
theorem B1365011 : Blo 401768 1365011 := bstep (se 1 (by rfl) ⟨1023758, by rfl⟩ : syracuseStep 1365011 = 2047517) B2047517
theorem B3462263 : Blo 401768 3462263 := bstep (se 1 (by rfl) ⟨2596697, by rfl⟩ : syracuseStep 3462263 = 5193395) B5193395
theorem B1365335 : Blo 401768 1365335 := bstep (se 1 (by rfl) ⟨1024001, by rfl⟩ : syracuseStep 1365335 = 2048003) B2048003
theorem B906875 : Blo 401768 906875 := bstep (se 1 (by rfl) ⟨680156, by rfl⟩ : syracuseStep 906875 = 1360313) B1360313
theorem B907001 : Blo 401768 907001 := bstep (se 2 (by rfl) ⟨340125, by rfl⟩ : syracuseStep 907001 = 680251) B680251
theorem B2447147 : Blo 401768 2447147 := bstep (se 1 (by rfl) ⟨1835360, by rfl⟩ : syracuseStep 2447147 = 3670721) B3670721
theorem B47404865 : Blo 401768 47404865 := bstep (se 2 (by rfl) ⟨17776824, by rfl⟩ : syracuseStep 47404865 = 35553649) B35553649
theorem B2053997 : Blo 401768 2053997 := bstep (se 3 (by rfl) ⟨385124, by rfl⟩ : syracuseStep 2053997 = 770249) B770249
theorem B2185147 : Blo 401768 2185147 := bstep (se 1 (by rfl) ⟨1638860, by rfl⟩ : syracuseStep 2185147 = 3277721) B3277721
theorem B907271 : Blo 401768 907271 := bstep (se 1 (by rfl) ⟨680453, by rfl⟩ : syracuseStep 907271 = 1360907) B1360907
theorem B2054159 : Blo 401768 2054159 := bstep (se 1 (by rfl) ⟨1540619, by rfl⟩ : syracuseStep 2054159 = 3081239) B3081239
theorem B907343 : Blo 401768 907343 := bstep (se 1 (by rfl) ⟨680507, by rfl⟩ : syracuseStep 907343 = 1361015) B1361015
theorem B2021465 : Blo 401768 2021465 := bstep (se 2 (by rfl) ⟨758049, by rfl⟩ : syracuseStep 2021465 = 1516099) B1516099
theorem B6314273 : Blo 401768 6314273 := bstep (se 2 (by rfl) ⟨2367852, by rfl⟩ : syracuseStep 6314273 = 4735705) B4735705
theorem B678287 : Blo 401768 678287 := bstep (se 1 (by rfl) ⟨508715, by rfl⟩ : syracuseStep 678287 = 1017431) B1017431
theorem B1366415 : Blo 401768 1366415 := bstep (se 1 (by rfl) ⟨1024811, by rfl⟩ : syracuseStep 1366415 = 2049623) B2049623
theorem B907739 : Blo 401768 907739 := bstep (se 1 (by rfl) ⟨680804, by rfl⟩ : syracuseStep 907739 = 1361609) B1361609
theorem B3463661 : Blo 401768 3463661 := bstep (se 3 (by rfl) ⟨649436, by rfl⟩ : syracuseStep 3463661 = 1298873) B1298873
theorem B645689 : Blo 401768 645689 := bstep (se 2 (by rfl) ⟨242133, by rfl⟩ : syracuseStep 645689 = 484267) B484267
theorem B678523 : Blo 401768 678523 := bstep (se 1 (by rfl) ⟨508892, by rfl⟩ : syracuseStep 678523 = 1017785) B1017785
theorem B1366739 : Blo 401768 1366739 := bstep (se 1 (by rfl) ⟨1025054, by rfl⟩ : syracuseStep 1366739 = 2050109) B2050109
theorem B908207 : Blo 401768 908207 := bstep (se 1 (by rfl) ⟨681155, by rfl⟩ : syracuseStep 908207 = 1362311) B1362311
theorem B908459 : Blo 401768 908459 := bstep (se 1 (by rfl) ⟨681344, by rfl⟩ : syracuseStep 908459 = 1362689) B1362689
theorem B679387 : Blo 401768 679387 := bstep (se 1 (by rfl) ⟨509540, by rfl⟩ : syracuseStep 679387 = 1019081) B1019081
theorem B6610571 : Blo 401768 6610571 := bstep (se 1 (by rfl) ⟨4957928, by rfl⟩ : syracuseStep 6610571 = 9915857) B9915857
theorem B2580113 : Blo 401768 2580113 := bstep (se 2 (by rfl) ⟨967542, by rfl⟩ : syracuseStep 2580113 = 1935085) B1935085
theorem B908999 : Blo 401768 908999 := bstep (se 1 (by rfl) ⟨681749, by rfl⟩ : syracuseStep 908999 = 1363499) B1363499
theorem B1367927 : Blo 401768 1367927 := bstep (se 1 (by rfl) ⟨1025945, by rfl⟩ : syracuseStep 1367927 = 2051891) B2051891
theorem B1400851 : Blo 401768 1400851 := bstep (se 1 (by rfl) ⟨1050638, by rfl⟩ : syracuseStep 1400851 = 2101277) B2101277
theorem B26173469 : Blo 401768 26173469 := bstep (se 3 (by rfl) ⟨4907525, by rfl⟩ : syracuseStep 26173469 = 9815051) B9815051
theorem B680015 : Blo 401768 680015 := bstep (se 1 (by rfl) ⟨510011, by rfl⟩ : syracuseStep 680015 = 1020023) B1020023
theorem B1368143 : Blo 401768 1368143 := bstep (se 1 (by rfl) ⟨1026107, by rfl⟩ : syracuseStep 1368143 = 2052215) B2052215
theorem B10313891 : Blo 401768 10313891 := bstep (se 1 (by rfl) ⟨7735418, by rfl⟩ : syracuseStep 10313891 = 15470837) B15470837
theorem B6578405 : Blo 401768 6578405 := bstep (se 4 (by rfl) ⟨616725, by rfl⟩ : syracuseStep 6578405 = 1233451) B1233451
theorem B7758179 : Blo 401768 7758179 := bstep (se 1 (by rfl) ⟨5818634, by rfl⟩ : syracuseStep 7758179 = 11637269) B11637269
theorem B778603 : Blo 401768 778603 := bstep (se 1 (by rfl) ⟨583952, by rfl⟩ : syracuseStep 778603 = 1167905) B1167905
theorem B1368521 : Blo 401768 1368521 := bstep (se 2 (by rfl) ⟨513195, by rfl⟩ : syracuseStep 1368521 = 1026391) B1026391
theorem B6644227 : Blo 401768 6644227 := bstep (se 1 (by rfl) ⟨4983170, by rfl⟩ : syracuseStep 6644227 = 9966341) B9966341
theorem B909863 : Blo 401768 909863 := bstep (se 1 (by rfl) ⟨682397, by rfl⟩ : syracuseStep 909863 = 1364795) B1364795
theorem B647759 : Blo 401768 647759 := bstep (se 1 (by rfl) ⟨485819, by rfl⟩ : syracuseStep 647759 = 971639) B971639
theorem B1368791 : Blo 401768 1368791 := bstep (se 1 (by rfl) ⟨1026593, by rfl⟩ : syracuseStep 1368791 = 2053187) B2053187
theorem B3269483 : Blo 401768 3269483 := bstep (se 1 (by rfl) ⟨2452112, by rfl⟩ : syracuseStep 3269483 = 4904225) B4904225
theorem B910187 : Blo 401768 910187 := bstep (se 1 (by rfl) ⟨682640, by rfl⟩ : syracuseStep 910187 = 1365281) B1365281
theorem B910241 : Blo 401768 910241 := bstep (se 2 (by rfl) ⟨341340, by rfl⟩ : syracuseStep 910241 = 682681) B682681
theorem B680879 : Blo 401768 680879 := bstep (se 1 (by rfl) ⟨510659, by rfl⟩ : syracuseStep 680879 = 1021319) B1021319
theorem B1369007 : Blo 401768 1369007 := bstep (se 1 (by rfl) ⟨1026755, by rfl⟩ : syracuseStep 1369007 = 2053511) B2053511
theorem B3466259 : Blo 401768 3466259 := bstep (se 1 (by rfl) ⟨2599694, by rfl⟩ : syracuseStep 3466259 = 5199389) B5199389
theorem B648271 : Blo 401768 648271 := bstep (se 1 (by rfl) ⟨486203, by rfl⟩ : syracuseStep 648271 = 972407) B972407
theorem B910583 : Blo 401768 910583 := bstep (se 1 (by rfl) ⟨682937, by rfl⟩ : syracuseStep 910583 = 1365875) B1365875
theorem B681311 : Blo 401768 681311 := bstep (se 1 (by rfl) ⟨510983, by rfl⟩ : syracuseStep 681311 = 1021967) B1021967
theorem B616015 : Blo 401768 616015 := bstep (se 1 (by rfl) ⟨462011, by rfl⟩ : syracuseStep 616015 = 924023) B924023
theorem B1533725 : Blo 401768 1533725 := bstep (se 3 (by rfl) ⟨287573, by rfl⟩ : syracuseStep 1533725 = 575147) B575147
theorem B911177 : Blo 401768 911177 := bstep (se 2 (by rfl) ⟨341691, by rfl⟩ : syracuseStep 911177 = 683383) B683383
theorem B681871 : Blo 401768 681871 := bstep (se 1 (by rfl) ⟨511403, by rfl⟩ : syracuseStep 681871 = 1022807) B1022807
theorem B452731 : Blo 401768 452731 := bstep (se 1 (by rfl) ⟨339548, by rfl⟩ : syracuseStep 452731 = 679097) B679097
theorem B3107159 : Blo 401768 3107159 := bstep (se 1 (by rfl) ⟨2330369, by rfl⟩ : syracuseStep 3107159 = 4660739) B4660739
theorem B5794183 : Blo 401768 5794183 := bstep (se 1 (by rfl) ⟨4345637, by rfl⟩ : syracuseStep 5794183 = 8691275) B8691275
theorem B4385177 : Blo 401768 4385177 := bstep (se 2 (by rfl) ⟨1644441, by rfl⟩ : syracuseStep 4385177 = 3288883) B3288883
theorem B1534409 : Blo 401768 1534409 := bstep (se 2 (by rfl) ⟨575403, by rfl⟩ : syracuseStep 1534409 = 1150807) B1150807
theorem B682553 : Blo 401768 682553 := bstep (se 2 (by rfl) ⟨255957, by rfl⟩ : syracuseStep 682553 = 511915) B511915
theorem B453199 : Blo 401768 453199 := bstep (se 1 (by rfl) ⟨339899, by rfl⟩ : syracuseStep 453199 = 679799) B679799
theorem B911969 : Blo 401768 911969 := bstep (se 2 (by rfl) ⟨341988, by rfl⟩ : syracuseStep 911969 = 683977) B683977
theorem B1534895 : Blo 401768 1534895 := bstep (se 1 (by rfl) ⟨1151171, by rfl⟩ : syracuseStep 1534895 = 2302343) B2302343
theorem B486319 : Blo 401768 486319 := bstep (se 1 (by rfl) ⟨364739, by rfl⟩ : syracuseStep 486319 = 729479) B729479
theorem B912311 : Blo 401768 912311 := bstep (se 1 (by rfl) ⟨684233, by rfl⟩ : syracuseStep 912311 = 1368467) B1368467
theorem B453595 : Blo 401768 453595 := bstep (se 1 (by rfl) ⟨340196, by rfl⟩ : syracuseStep 453595 = 680393) B680393
theorem B683255 : Blo 401768 683255 := bstep (se 1 (by rfl) ⟨512441, by rfl⟩ : syracuseStep 683255 = 1024883) B1024883
theorem B4418959 : Blo 401768 4418959 := bstep (se 1 (by rfl) ⟨3314219, by rfl⟩ : syracuseStep 4418959 = 6628439) B6628439
theorem B454063 : Blo 401768 454063 := bstep (se 1 (by rfl) ⟨340547, by rfl⟩ : syracuseStep 454063 = 681095) B681095
theorem B3436019 : Blo 401768 3436019 := bstep (se 1 (by rfl) ⟨2577014, by rfl⟩ : syracuseStep 3436019 = 5154029) B5154029
theorem B912905 : Blo 401768 912905 := bstep (se 2 (by rfl) ⟨342339, by rfl⟩ : syracuseStep 912905 = 684679) B684679
theorem B683599 : Blo 401768 683599 := bstep (se 1 (by rfl) ⟨512699, by rfl⟩ : syracuseStep 683599 = 1025399) B1025399
theorem B9858647 : Blo 401768 9858647 := bstep (se 1 (by rfl) ⟨7393985, by rfl⟩ : syracuseStep 9858647 = 14787971) B14787971
theorem B1535699 : Blo 401768 1535699 := bstep (se 1 (by rfl) ⟨1151774, by rfl⟩ : syracuseStep 1535699 = 2303549) B2303549
theorem B683849 : Blo 401768 683849 := bstep (se 2 (by rfl) ⟨256443, by rfl⟩ : syracuseStep 683849 = 512887) B512887
theorem B454495 : Blo 401768 454495 := bstep (se 1 (by rfl) ⟨340871, by rfl⟩ : syracuseStep 454495 = 681743) B681743
theorem B454855 : Blo 401768 454855 := bstep (se 1 (by rfl) ⟨341141, by rfl⟩ : syracuseStep 454855 = 682283) B682283
theorem B684281 : Blo 401768 684281 := bstep (se 2 (by rfl) ⟨256605, by rfl⟩ : syracuseStep 684281 = 513211) B513211
theorem B520543 : Blo 401768 520543 := bstep (se 1 (by rfl) ⟨390407, by rfl⟩ : syracuseStep 520543 = 780815) B780815
theorem B684463 : Blo 401768 684463 := bstep (se 1 (by rfl) ⟨513347, by rfl⟩ : syracuseStep 684463 = 1026695) B1026695
theorem B684551 : Blo 401768 684551 := bstep (se 1 (by rfl) ⟨513413, by rfl⟩ : syracuseStep 684551 = 1026827) B1026827
theorem B2912777 : Blo 401768 2912777 := bstep (se 2 (by rfl) ⟨1092291, by rfl⟩ : syracuseStep 2912777 = 2184583) B2184583
theorem B3666491 : Blo 401768 3666491 := bstep (se 1 (by rfl) ⟨2749868, by rfl⟩ : syracuseStep 3666491 = 5499737) B5499737
theorem B4682299 : Blo 401768 4682299 := bstep (se 1 (by rfl) ⟨3511724, by rfl⟩ : syracuseStep 4682299 = 7023449) B7023449
theorem B6517421 : Blo 401768 6517421 := bstep (se 3 (by rfl) ⟨1222016, by rfl⟩ : syracuseStep 6517421 = 2444033) B2444033
theorem B455719 : Blo 401768 455719 := bstep (se 1 (by rfl) ⟨341789, by rfl⟩ : syracuseStep 455719 = 683579) B683579
theorem B53310517 : Blo 401768 53310517 := bstep (se 5 (by rfl) ⟨2498930, by rfl⟩ : syracuseStep 53310517 = 4997861) B4997861
theorem B2585753 : Blo 401768 2585753 := bstep (se 2 (by rfl) ⟨969657, by rfl⟩ : syracuseStep 2585753 = 1939315) B1939315
theorem B2618825 : Blo 401768 2618825 := bstep (se 2 (by rfl) ⟨982059, by rfl⟩ : syracuseStep 2618825 = 1964119) B1964119
theorem B35452673 : Blo 401768 35452673 := bstep (se 2 (by rfl) ⟨13294752, by rfl⟩ : syracuseStep 35452673 = 26589505) B26589505
theorem B1636139 : Blo 401768 1636139 := bstep (se 1 (by rfl) ⟨1227104, by rfl⟩ : syracuseStep 1636139 = 2454209) B2454209
theorem B4585409 : Blo 401768 4585409 := bstep (se 2 (by rfl) ⟨1719528, by rfl⟩ : syracuseStep 4585409 = 3439057) B3439057
theorem B2586653 : Blo 401768 2586653 := bstep (se 3 (by rfl) ⟨484997, by rfl⟩ : syracuseStep 2586653 = 969995) B969995
theorem B1538129 : Blo 401768 1538129 := bstep (se 2 (by rfl) ⟨576798, by rfl⟩ : syracuseStep 1538129 = 1153597) B1153597
theorem B1538585 : Blo 401768 1538585 := bstep (se 2 (by rfl) ⟨576969, by rfl⟩ : syracuseStep 1538585 = 1153939) B1153939
theorem B1145441 : Blo 401768 1145441 := bstep (se 2 (by rfl) ⟨429540, by rfl⟩ : syracuseStep 1145441 = 859081) B859081
theorem B3111709 : Blo 401768 3111709 := bstep (se 3 (by rfl) ⟨583445, by rfl⟩ : syracuseStep 3111709 = 1166891) B1166891
theorem B687455 : Blo 401768 687455 := bstep (se 1 (by rfl) ⟨515591, by rfl⟩ : syracuseStep 687455 = 1031183) B1031183
theorem B3440015 : Blo 401768 3440015 := bstep (se 1 (by rfl) ⟨2580011, by rfl⟩ : syracuseStep 3440015 = 5160023) B5160023
theorem B2358881 : Blo 401768 2358881 := bstep (se 2 (by rfl) ⟨884580, by rfl⟩ : syracuseStep 2358881 = 1769161) B1769161
theorem B3866251 : Blo 401768 3866251 := bstep (se 1 (by rfl) ⟨2899688, by rfl⟩ : syracuseStep 3866251 = 5799377) B5799377
theorem B1539769 : Blo 401768 1539769 := bstep (se 2 (by rfl) ⟨577413, by rfl⟩ : syracuseStep 1539769 = 1154827) B1154827
theorem B1867801 : Blo 401768 1867801 := bstep (se 2 (by rfl) ⟨700425, by rfl⟩ : syracuseStep 1867801 = 1400851) B1400851
theorem B4653883 : Blo 401768 4653883 := bstep (se 1 (by rfl) ⟨3490412, by rfl⟩ : syracuseStep 4653883 = 6980825) B6980825
theorem B2459069 : Blo 401768 2459069 := bstep (se 3 (by rfl) ⟨461075, by rfl⟩ : syracuseStep 2459069 = 922151) B922151
theorem B11044471 : Blo 401768 11044471 := bstep (se 1 (by rfl) ⟨8283353, by rfl⟩ : syracuseStep 11044471 = 16566707) B16566707
theorem B7997251 : Blo 401768 7997251 := bstep (se 1 (by rfl) ⟨5997938, by rfl⟩ : syracuseStep 7997251 = 11995877) B11995877
theorem B821353 : Blo 401768 821353 := bstep (se 2 (by rfl) ⟨308007, by rfl⟩ : syracuseStep 821353 = 616015) B616015
theorem B3541391 : Blo 401768 3541391 := bstep (se 1 (by rfl) ⟨2656043, by rfl⟩ : syracuseStep 3541391 = 5312087) B5312087
theorem B1018615 : Blo 401768 1018615 := bstep (se 1 (by rfl) ⟨763961, by rfl⟩ : syracuseStep 1018615 = 1527923) B1527923
theorem B2919235 : Blo 401768 2919235 := bstep (se 1 (by rfl) ⟨2189426, by rfl⟩ : syracuseStep 2919235 = 4378853) B4378853
theorem B2034557 : Blo 401768 2034557 := bstep (se 3 (by rfl) ⟨381479, by rfl⟩ : syracuseStep 2034557 = 762959) B762959
theorem B1149839 : Blo 401768 1149839 := bstep (se 1 (by rfl) ⟨862379, by rfl⟩ : syracuseStep 1149839 = 1724759) B1724759
theorem B1936315 : Blo 401768 1936315 := bstep (se 1 (by rfl) ⟨1452236, by rfl⟩ : syracuseStep 1936315 = 2904473) B2904473
theorem B1018919 : Blo 401768 1018919 := bstep (se 1 (by rfl) ⟨764189, by rfl⟩ : syracuseStep 1018919 = 1528379) B1528379
theorem B822415 : Blo 401768 822415 := bstep (se 1 (by rfl) ⟨616811, by rfl⟩ : syracuseStep 822415 = 1233623) B1233623
theorem B1150625 : Blo 401768 1150625 := bstep (se 2 (by rfl) ⟨431484, by rfl⟩ : syracuseStep 1150625 = 862969) B862969
theorem B3870443 : Blo 401768 3870443 := bstep (se 1 (by rfl) ⟨2902832, by rfl⟩ : syracuseStep 3870443 = 5805665) B5805665
theorem B2035529 : Blo 401768 2035529 := bstep (se 2 (by rfl) ⟨763323, by rfl⟩ : syracuseStep 2035529 = 1526647) B1526647
theorem B6983533 : Blo 401768 6983533 := bstep (se 3 (by rfl) ⟨1309412, by rfl⟩ : syracuseStep 6983533 = 2618825) B2618825
theorem B1347643 : Blo 401768 1347643 := bstep (se 1 (by rfl) ⟨1010732, by rfl⟩ : syracuseStep 1347643 = 2021465) B2021465
theorem B1151081 : Blo 401768 1151081 := bstep (se 2 (by rfl) ⟨431655, by rfl⟩ : syracuseStep 1151081 = 863311) B863311
theorem B1020185 : Blo 401768 1020185 := bstep (se 2 (by rfl) ⟨382569, by rfl⟩ : syracuseStep 1020185 = 765139) B765139
theorem B2363755 : Blo 401768 2363755 := bstep (se 1 (by rfl) ⟨1772816, by rfl⟩ : syracuseStep 2363755 = 3545633) B3545633
theorem B1708489 : Blo 401768 1708489 := bstep (se 2 (by rfl) ⟨640683, by rfl⟩ : syracuseStep 1708489 = 1281367) B1281367
theorem B2036825 : Blo 401768 2036825 := bstep (se 2 (by rfl) ⟨763809, by rfl⟩ : syracuseStep 2036825 = 1527619) B1527619
theorem B1021025 : Blo 401768 1021025 := bstep (se 2 (by rfl) ⟨382884, by rfl⟩ : syracuseStep 1021025 = 765769) B765769
theorem B3282065 : Blo 401768 3282065 := bstep (se 2 (by rfl) ⟨1230774, by rfl⟩ : syracuseStep 3282065 = 2461549) B2461549
theorem B8754425 : Blo 401768 8754425 := bstep (se 2 (by rfl) ⟨3282909, by rfl⟩ : syracuseStep 8754425 = 6565819) B6565819
theorem B2299175 : Blo 401768 2299175 := bstep (se 1 (by rfl) ⟨1724381, by rfl⟩ : syracuseStep 2299175 = 3448763) B3448763
theorem B431839 : Blo 401768 431839 := bstep (se 1 (by rfl) ⟨323879, by rfl⟩ : syracuseStep 431839 = 647759) B647759
theorem B694057 : Blo 401768 694057 := bstep (se 2 (by rfl) ⟨260271, by rfl⟩ : syracuseStep 694057 = 520543) B520543
theorem B1939585 : Blo 401768 1939585 := bstep (se 2 (by rfl) ⟨727344, by rfl⟩ : syracuseStep 1939585 = 1454689) B1454689
theorem B4987109 : Blo 401768 4987109 := bstep (se 4 (by rfl) ⟨467541, by rfl⟩ : syracuseStep 4987109 = 935083) B935083
theorem B1448189 : Blo 401768 1448189 := bstep (se 3 (by rfl) ⟨271535, by rfl⟩ : syracuseStep 1448189 = 543071) B543071
theorem B1448201 : Blo 401768 1448201 := bstep (se 2 (by rfl) ⟨543075, by rfl⟩ : syracuseStep 1448201 = 1086151) B1086151
theorem B1022483 : Blo 401768 1022483 := bstep (se 1 (by rfl) ⟨766862, by rfl⟩ : syracuseStep 1022483 = 1533725) B1533725
theorem B2071439 : Blo 401768 2071439 := bstep (se 1 (by rfl) ⟨1553579, by rfl⟩ : syracuseStep 2071439 = 3107159) B3107159
theorem B3054509 : Blo 401768 3054509 := bstep (se 3 (by rfl) ⟨572720, by rfl⟩ : syracuseStep 3054509 = 1145441) B1145441
theorem B2923451 : Blo 401768 2923451 := bstep (se 1 (by rfl) ⟨2192588, by rfl⟩ : syracuseStep 2923451 = 4385177) B4385177
theorem B859099 : Blo 401768 859099 := bstep (se 1 (by rfl) ⟨644324, by rfl⟩ : syracuseStep 859099 = 1288649) B1288649
theorem B1022939 : Blo 401768 1022939 := bstep (se 1 (by rfl) ⟨767204, by rfl⟩ : syracuseStep 1022939 = 1534409) B1534409
theorem B924635 : Blo 401768 924635 := bstep (se 1 (by rfl) ⟨693476, by rfl⟩ : syracuseStep 924635 = 1386953) B1386953
theorem B859423 : Blo 401768 859423 := bstep (se 1 (by rfl) ⟨644567, by rfl⟩ : syracuseStep 859423 = 1289135) B1289135
theorem B1023263 : Blo 401768 1023263 := bstep (se 1 (by rfl) ⟨767447, by rfl⟩ : syracuseStep 1023263 = 1534895) B1534895
theorem B2039255 : Blo 401768 2039255 := bstep (se 1 (by rfl) ⟨1529441, by rfl⟩ : syracuseStep 2039255 = 3058883) B3058883
theorem B4922903 : Blo 401768 4922903 := bstep (se 1 (by rfl) ⟨3692177, by rfl⟩ : syracuseStep 4922903 = 7384355) B7384355
theorem B1023799 : Blo 401768 1023799 := bstep (se 1 (by rfl) ⟨767849, by rfl⟩ : syracuseStep 1023799 = 1535699) B1535699
theorem B1154873 : Blo 401768 1154873 := bstep (se 2 (by rfl) ⟨433077, by rfl⟩ : syracuseStep 1154873 = 866155) B866155
theorem B4923443 : Blo 401768 4923443 := bstep (se 1 (by rfl) ⟨3692582, by rfl⟩ : syracuseStep 4923443 = 7385165) B7385165
theorem B1024265 : Blo 401768 1024265 := bstep (se 2 (by rfl) ⟨384099, by rfl⟩ : syracuseStep 1024265 = 768199) B768199
theorem B1941851 : Blo 401768 1941851 := bstep (se 1 (by rfl) ⟨1456388, by rfl⟩ : syracuseStep 1941851 = 2912777) B2912777
theorem B401775 : Blo 401768 401775 := bstep (se 1 (by rfl) ⟨301331, by rfl⟩ : syracuseStep 401775 = 602663) B602663
theorem B401831 : Blo 401768 401831 := bstep (se 1 (by rfl) ⟨301373, by rfl⟩ : syracuseStep 401831 = 602747) B602747
theorem B401915 : Blo 401768 401915 := bstep (se 1 (by rfl) ⟨301436, by rfl⟩ : syracuseStep 401915 = 602873) B602873
theorem B401983 : Blo 401768 401983 := bstep (se 1 (by rfl) ⟨301487, by rfl⟩ : syracuseStep 401983 = 602975) B602975
theorem B401991 : Blo 401768 401991 := bstep (se 1 (by rfl) ⟨301493, by rfl⟩ : syracuseStep 401991 = 602987) B602987
theorem B402143 : Blo 401768 402143 := bstep (se 1 (by rfl) ⟨301607, by rfl⟩ : syracuseStep 402143 = 603215) B603215
theorem B402223 : Blo 401768 402223 := bstep (se 1 (by rfl) ⟨301667, by rfl⟩ : syracuseStep 402223 = 603335) B603335
theorem B402331 : Blo 401768 402331 := bstep (se 1 (by rfl) ⟨301748, by rfl⟩ : syracuseStep 402331 = 603497) B603497
theorem B402383 : Blo 401768 402383 := bstep (se 1 (by rfl) ⟨301787, by rfl⟩ : syracuseStep 402383 = 603575) B603575
theorem B402407 : Blo 401768 402407 := bstep (se 1 (by rfl) ⟨301805, by rfl⟩ : syracuseStep 402407 = 603611) B603611
theorem B23635115 : Blo 401768 23635115 := bstep (se 1 (by rfl) ⟨17726336, by rfl⟩ : syracuseStep 23635115 = 35452673) B35452673
theorem B1090759 : Blo 401768 1090759 := bstep (se 1 (by rfl) ⟨818069, by rfl⟩ : syracuseStep 1090759 = 1636139) B1636139
theorem B1025257 : Blo 401768 1025257 := bstep (se 2 (by rfl) ⟨384471, by rfl⟩ : syracuseStep 1025257 = 768943) B768943
theorem B402719 : Blo 401768 402719 := bstep (se 1 (by rfl) ⟨302039, by rfl⟩ : syracuseStep 402719 = 604079) B604079
theorem B1451303 : Blo 401768 1451303 := bstep (se 1 (by rfl) ⟨1088477, by rfl⟩ : syracuseStep 1451303 = 2176955) B2176955
theorem B3056939 : Blo 401768 3056939 := bstep (se 1 (by rfl) ⟨2292704, by rfl⟩ : syracuseStep 3056939 = 4585409) B4585409
theorem B2303275 : Blo 401768 2303275 := bstep (se 1 (by rfl) ⟨1727456, by rfl⟩ : syracuseStep 2303275 = 3454913) B3454913
theorem B402779 : Blo 401768 402779 := bstep (se 1 (by rfl) ⟨302084, by rfl⟩ : syracuseStep 402779 = 604169) B604169
theorem B402799 : Blo 401768 402799 := bstep (se 1 (by rfl) ⟨302099, by rfl⟩ : syracuseStep 402799 = 604199) B604199
theorem B1025419 : Blo 401768 1025419 := bstep (se 1 (by rfl) ⟨769064, by rfl⟩ : syracuseStep 1025419 = 1538129) B1538129
theorem B1549729 : Blo 401768 1549729 := bstep (se 2 (by rfl) ⟨581148, by rfl⟩ : syracuseStep 1549729 = 1162297) B1162297
theorem B402855 : Blo 401768 402855 := bstep (se 1 (by rfl) ⟨302141, by rfl⟩ : syracuseStep 402855 = 604283) B604283
theorem B402939 : Blo 401768 402939 := bstep (se 1 (by rfl) ⟨302204, by rfl⟩ : syracuseStep 402939 = 604409) B604409
theorem B403007 : Blo 401768 403007 := bstep (se 1 (by rfl) ⟨302255, by rfl⟩ : syracuseStep 403007 = 604511) B604511
theorem B403015 : Blo 401768 403015 := bstep (se 1 (by rfl) ⟨302261, by rfl⟩ : syracuseStep 403015 = 604523) B604523
theorem B1025723 : Blo 401768 1025723 := bstep (se 1 (by rfl) ⟨769292, by rfl⟩ : syracuseStep 1025723 = 1538585) B1538585
theorem B403167 : Blo 401768 403167 := bstep (se 1 (by rfl) ⟨302375, by rfl⟩ : syracuseStep 403167 = 604751) B604751
theorem B403247 : Blo 401768 403247 := bstep (se 1 (by rfl) ⟨302435, by rfl⟩ : syracuseStep 403247 = 604871) B604871
theorem B403355 : Blo 401768 403355 := bstep (se 1 (by rfl) ⟨302516, by rfl⟩ : syracuseStep 403355 = 605033) B605033
theorem B403407 : Blo 401768 403407 := bstep (se 1 (by rfl) ⟨302555, by rfl⟩ : syracuseStep 403407 = 605111) B605111
theorem B403431 : Blo 401768 403431 := bstep (se 1 (by rfl) ⟨302573, by rfl⟩ : syracuseStep 403431 = 605147) B605147
theorem B5155001 : Blo 401768 5155001 := bstep (se 2 (by rfl) ⟨1933125, by rfl⟩ : syracuseStep 5155001 = 3866251) B3866251
theorem B4139261 : Blo 401768 4139261 := bstep (se 3 (by rfl) ⟨776111, by rfl⟩ : syracuseStep 4139261 = 1552223) B1552223
theorem B1943833 : Blo 401768 1943833 := bstep (se 2 (by rfl) ⟨728937, by rfl⟩ : syracuseStep 1943833 = 1457875) B1457875
theorem B403743 : Blo 401768 403743 := bstep (se 1 (by rfl) ⟨302807, by rfl⟩ : syracuseStep 403743 = 605615) B605615
theorem B403803 : Blo 401768 403803 := bstep (se 1 (by rfl) ⟨302852, by rfl⟩ : syracuseStep 403803 = 605705) B605705
theorem B403823 : Blo 401768 403823 := bstep (se 1 (by rfl) ⟨302867, by rfl⟩ : syracuseStep 403823 = 605735) B605735
theorem B403879 : Blo 401768 403879 := bstep (se 1 (by rfl) ⟨302909, by rfl⟩ : syracuseStep 403879 = 605819) B605819
theorem B403963 : Blo 401768 403963 := bstep (se 1 (by rfl) ⟨302972, by rfl⟩ : syracuseStep 403963 = 605945) B605945
theorem B404031 : Blo 401768 404031 := bstep (se 1 (by rfl) ⟨303023, by rfl⟩ : syracuseStep 404031 = 606047) B606047
theorem B404039 : Blo 401768 404039 := bstep (se 1 (by rfl) ⟨303029, by rfl⟩ : syracuseStep 404039 = 606059) B606059
theorem B1845949 : Blo 401768 1845949 := bstep (se 3 (by rfl) ⟨346115, by rfl⟩ : syracuseStep 1845949 = 692231) B692231
theorem B3058397 : Blo 401768 3058397 := bstep (se 3 (by rfl) ⟨573449, by rfl⟩ : syracuseStep 3058397 = 1146899) B1146899
theorem B2304733 : Blo 401768 2304733 := bstep (se 3 (by rfl) ⟨432137, by rfl⟩ : syracuseStep 2304733 = 864275) B864275
theorem B404191 : Blo 401768 404191 := bstep (se 1 (by rfl) ⟨303143, by rfl⟩ : syracuseStep 404191 = 606287) B606287
theorem B404271 : Blo 401768 404271 := bstep (se 1 (by rfl) ⟨303203, by rfl⟩ : syracuseStep 404271 = 606407) B606407
theorem B863131 : Blo 401768 863131 := bstep (se 1 (by rfl) ⟨647348, by rfl⟩ : syracuseStep 863131 = 1294697) B1294697
theorem B404379 : Blo 401768 404379 := bstep (se 1 (by rfl) ⟨303284, by rfl⟩ : syracuseStep 404379 = 606569) B606569
theorem B404431 : Blo 401768 404431 := bstep (se 1 (by rfl) ⟨303323, by rfl⟩ : syracuseStep 404431 = 606647) B606647
theorem B764903 : Blo 401768 764903 := bstep (se 1 (by rfl) ⟨573677, by rfl⟩ : syracuseStep 764903 = 1147355) B1147355
theorem B404455 : Blo 401768 404455 := bstep (se 1 (by rfl) ⟨303341, by rfl⟩ : syracuseStep 404455 = 606683) B606683
theorem B1092595 : Blo 401768 1092595 := bstep (se 1 (by rfl) ⟨819446, by rfl⟩ : syracuseStep 1092595 = 1638893) B1638893
theorem B404767 : Blo 401768 404767 := bstep (se 1 (by rfl) ⟨303575, by rfl⟩ : syracuseStep 404767 = 607151) B607151
theorem B8858969 : Blo 401768 8858969 := bstep (se 2 (by rfl) ⟨3322113, by rfl⟩ : syracuseStep 8858969 = 6644227) B6644227
theorem B404827 : Blo 401768 404827 := bstep (se 1 (by rfl) ⟨303620, by rfl⟩ : syracuseStep 404827 = 607241) B607241
theorem B404847 : Blo 401768 404847 := bstep (se 1 (by rfl) ⟨303635, by rfl⟩ : syracuseStep 404847 = 607271) B607271
theorem B404903 : Blo 401768 404903 := bstep (se 1 (by rfl) ⟨303677, by rfl⟩ : syracuseStep 404903 = 607355) B607355
theorem B404987 : Blo 401768 404987 := bstep (se 1 (by rfl) ⟨303740, by rfl⟩ : syracuseStep 404987 = 607481) B607481
theorem B405055 : Blo 401768 405055 := bstep (se 1 (by rfl) ⟨303791, by rfl⟩ : syracuseStep 405055 = 607583) B607583
theorem B405063 : Blo 401768 405063 := bstep (se 1 (by rfl) ⟨303797, by rfl⟩ : syracuseStep 405063 = 607595) B607595
theorem B405215 : Blo 401768 405215 := bstep (se 1 (by rfl) ⟨303911, by rfl⟩ : syracuseStep 405215 = 607823) B607823
theorem B405295 : Blo 401768 405295 := bstep (se 1 (by rfl) ⟨303971, by rfl⟩ : syracuseStep 405295 = 607943) B607943
theorem B405403 : Blo 401768 405403 := bstep (se 1 (by rfl) ⟨304052, by rfl⟩ : syracuseStep 405403 = 608105) B608105
theorem B405455 : Blo 401768 405455 := bstep (se 1 (by rfl) ⟨304091, by rfl⟩ : syracuseStep 405455 = 608183) B608183
theorem B405479 : Blo 401768 405479 := bstep (se 1 (by rfl) ⟨304109, by rfl⟩ : syracuseStep 405479 = 608219) B608219
theorem B864361 : Blo 401768 864361 := bstep (se 2 (by rfl) ⟨324135, by rfl⟩ : syracuseStep 864361 = 648271) B648271
theorem B2044115 : Blo 401768 2044115 := bstep (se 1 (by rfl) ⟨1533086, by rfl⟩ : syracuseStep 2044115 = 3066173) B3066173
theorem B1946081 : Blo 401768 1946081 := bstep (se 2 (by rfl) ⟨729780, by rfl⟩ : syracuseStep 1946081 = 1459561) B1459561
theorem B602687 : Blo 401768 602687 := bstep (se 1 (by rfl) ⟨452015, by rfl⟩ : syracuseStep 602687 = 904031) B904031
theorem B602807 : Blo 401768 602807 := bstep (se 1 (by rfl) ⟨452105, by rfl⟩ : syracuseStep 602807 = 904211) B904211
theorem B4895417 : Blo 401768 4895417 := bstep (se 2 (by rfl) ⟨1835781, by rfl⟩ : syracuseStep 4895417 = 3671563) B3671563
theorem B603035 : Blo 401768 603035 := bstep (se 1 (by rfl) ⟨452276, by rfl⟩ : syracuseStep 603035 = 904553) B904553
theorem B5551183 : Blo 401768 5551183 := bstep (se 1 (by rfl) ⟨4163387, by rfl⟩ : syracuseStep 5551183 = 8326775) B8326775
theorem B1717463 : Blo 401768 1717463 := bstep (se 1 (by rfl) ⟨1288097, by rfl⟩ : syracuseStep 1717463 = 2576195) B2576195
theorem B603431 : Blo 401768 603431 := bstep (se 1 (by rfl) ⟨452573, by rfl⟩ : syracuseStep 603431 = 905147) B905147
theorem B603515 : Blo 401768 603515 := bstep (se 1 (by rfl) ⟨452636, by rfl⟩ : syracuseStep 603515 = 905273) B905273
theorem B2307467 : Blo 401768 2307467 := bstep (se 1 (by rfl) ⟨1730600, by rfl⟩ : syracuseStep 2307467 = 3461201) B3461201
theorem B603641 : Blo 401768 603641 := bstep (se 2 (by rfl) ⟨226365, by rfl⟩ : syracuseStep 603641 = 452731) B452731
theorem B931385 : Blo 401768 931385 := bstep (se 2 (by rfl) ⟨349269, by rfl⟩ : syracuseStep 931385 = 698539) B698539
theorem B603743 : Blo 401768 603743 := bstep (se 1 (by rfl) ⟨452807, by rfl⟩ : syracuseStep 603743 = 905615) B905615
theorem B603959 : Blo 401768 603959 := bstep (se 1 (by rfl) ⟨452969, by rfl⟩ : syracuseStep 603959 = 905939) B905939
theorem B6993719 : Blo 401768 6993719 := bstep (se 1 (by rfl) ⟨5245289, by rfl⟩ : syracuseStep 6993719 = 10490579) B10490579
theorem B1357775 : Blo 401768 1357775 := bstep (se 1 (by rfl) ⟨1018331, by rfl⟩ : syracuseStep 1357775 = 2036663) B2036663
theorem B2308175 : Blo 401768 2308175 := bstep (se 1 (by rfl) ⟨1731131, by rfl⟩ : syracuseStep 2308175 = 3462263) B3462263
theorem B604265 : Blo 401768 604265 := bstep (se 2 (by rfl) ⟨226599, by rfl⟩ : syracuseStep 604265 = 453199) B453199
theorem B1947833 : Blo 401768 1947833 := bstep (se 2 (by rfl) ⟨730437, by rfl⟩ : syracuseStep 1947833 = 1460875) B1460875
theorem B604583 : Blo 401768 604583 := bstep (se 1 (by rfl) ⟨453437, by rfl⟩ : syracuseStep 604583 = 906875) B906875
theorem B604667 : Blo 401768 604667 := bstep (se 1 (by rfl) ⟨453500, by rfl⟩ : syracuseStep 604667 = 907001) B907001
theorem B604793 : Blo 401768 604793 := bstep (se 2 (by rfl) ⟨226797, by rfl⟩ : syracuseStep 604793 = 453595) B453595
theorem B604847 : Blo 401768 604847 := bstep (se 1 (by rfl) ⟨453635, by rfl⟩ : syracuseStep 604847 = 907271) B907271
theorem B604895 : Blo 401768 604895 := bstep (se 1 (by rfl) ⟨453671, by rfl⟩ : syracuseStep 604895 = 907343) B907343
theorem B2079479 : Blo 401768 2079479 := bstep (se 1 (by rfl) ⟨1559609, by rfl⟩ : syracuseStep 2079479 = 3119219) B3119219
theorem B4209515 : Blo 401768 4209515 := bstep (se 1 (by rfl) ⟨3157136, by rfl⟩ : syracuseStep 4209515 = 6314273) B6314273
theorem B1358747 : Blo 401768 1358747 := bstep (se 1 (by rfl) ⟨1019060, by rfl⟩ : syracuseStep 1358747 = 2038121) B2038121
theorem B605159 : Blo 401768 605159 := bstep (se 1 (by rfl) ⟨453869, by rfl⟩ : syracuseStep 605159 = 907739) B907739
theorem B3062771 : Blo 401768 3062771 := bstep (se 1 (by rfl) ⟨2297078, by rfl⟩ : syracuseStep 3062771 = 4594157) B4594157
theorem B2309107 : Blo 401768 2309107 := bstep (se 1 (by rfl) ⟨1731830, by rfl⟩ : syracuseStep 2309107 = 3463661) B3463661
theorem B1719377 : Blo 401768 1719377 := bstep (se 2 (by rfl) ⟨644766, by rfl⟩ : syracuseStep 1719377 = 1289533) B1289533
theorem B605417 : Blo 401768 605417 := bstep (se 2 (by rfl) ⟨227031, by rfl⟩ : syracuseStep 605417 = 454063) B454063
theorem B605471 : Blo 401768 605471 := bstep (se 1 (by rfl) ⟨454103, by rfl⟩ : syracuseStep 605471 = 908207) B908207
theorem B605639 : Blo 401768 605639 := bstep (se 1 (by rfl) ⟨454229, by rfl⟩ : syracuseStep 605639 = 908459) B908459
theorem B1293839 : Blo 401768 1293839 := bstep (se 1 (by rfl) ⟨970379, by rfl⟩ : syracuseStep 1293839 = 1940759) B1940759
theorem B966305 : Blo 401768 966305 := bstep (se 2 (by rfl) ⟨362364, by rfl⟩ : syracuseStep 966305 = 724729) B724729
theorem B4407047 : Blo 401768 4407047 := bstep (se 1 (by rfl) ⟨3305285, by rfl⟩ : syracuseStep 4407047 = 6610571) B6610571
theorem B605993 : Blo 401768 605993 := bstep (se 2 (by rfl) ⟨227247, by rfl⟩ : syracuseStep 605993 = 454495) B454495
theorem B605999 : Blo 401768 605999 := bstep (se 1 (by rfl) ⟨454499, by rfl⟩ : syracuseStep 605999 = 908999) B908999
theorem B3456827 : Blo 401768 3456827 := bstep (se 1 (by rfl) ⟨2592620, by rfl⟩ : syracuseStep 3456827 = 5185241) B5185241
theorem B3260267 : Blo 401768 3260267 := bstep (se 1 (by rfl) ⟨2445200, by rfl⟩ : syracuseStep 3260267 = 4890401) B4890401
theorem B1359773 : Blo 401768 1359773 := bstep (se 3 (by rfl) ⟨254957, by rfl⟩ : syracuseStep 1359773 = 509915) B509915
theorem B769999 : Blo 401768 769999 := bstep (se 1 (by rfl) ⟨577499, by rfl⟩ : syracuseStep 769999 = 1154999) B1154999
theorem B1359881 : Blo 401768 1359881 := bstep (se 2 (by rfl) ⟨509955, by rfl⟩ : syracuseStep 1359881 = 1019911) B1019911
theorem B17448979 : Blo 401768 17448979 := bstep (se 1 (by rfl) ⟨13086734, by rfl⟩ : syracuseStep 17448979 = 26173469) B26173469
theorem B606473 : Blo 401768 606473 := bstep (se 2 (by rfl) ⟨227427, by rfl⟩ : syracuseStep 606473 = 454855) B454855
theorem B606575 : Blo 401768 606575 := bstep (se 1 (by rfl) ⟨454931, by rfl⟩ : syracuseStep 606575 = 909863) B909863
theorem B3064229 : Blo 401768 3064229 := bstep (se 4 (by rfl) ⟨287271, by rfl⟩ : syracuseStep 3064229 = 574543) B574543
theorem B2310565 : Blo 401768 2310565 := bstep (se 4 (by rfl) ⟨216615, by rfl⟩ : syracuseStep 2310565 = 433231) B433231
theorem B2179655 : Blo 401768 2179655 := bstep (se 1 (by rfl) ⟨1634741, by rfl⟩ : syracuseStep 2179655 = 3269483) B3269483
theorem B606791 : Blo 401768 606791 := bstep (se 1 (by rfl) ⟨455093, by rfl⟩ : syracuseStep 606791 = 910187) B910187
theorem B606827 : Blo 401768 606827 := bstep (se 1 (by rfl) ⟨455120, by rfl⟩ : syracuseStep 606827 = 910241) B910241
theorem B2310839 : Blo 401768 2310839 := bstep (se 1 (by rfl) ⟨1733129, by rfl⟩ : syracuseStep 2310839 = 3466259) B3466259
theorem B6243065 : Blo 401768 6243065 := bstep (se 2 (by rfl) ⟨2341149, by rfl⟩ : syracuseStep 6243065 = 4682299) B4682299
theorem B1295183 : Blo 401768 1295183 := bstep (se 1 (by rfl) ⟨971387, by rfl⟩ : syracuseStep 1295183 = 1942775) B1942775
theorem B607055 : Blo 401768 607055 := bstep (se 1 (by rfl) ⟨455291, by rfl⟩ : syracuseStep 607055 = 910583) B910583
theorem B1754075 : Blo 401768 1754075 := bstep (se 1 (by rfl) ⟨1315556, by rfl⟩ : syracuseStep 1754075 = 2631113) B2631113
theorem B607451 : Blo 401768 607451 := bstep (se 1 (by rfl) ⟨455588, by rfl⟩ : syracuseStep 607451 = 911177) B911177
theorem B607625 : Blo 401768 607625 := bstep (se 2 (by rfl) ⟨227859, by rfl⟩ : syracuseStep 607625 = 455719) B455719
theorem B1721837 : Blo 401768 1721837 := bstep (se 3 (by rfl) ⟨322844, by rfl⟩ : syracuseStep 1721837 = 645689) B645689
theorem B4376051 : Blo 401768 4376051 := bstep (se 1 (by rfl) ⟨3282038, by rfl⟩ : syracuseStep 4376051 = 6564077) B6564077
theorem B607979 : Blo 401768 607979 := bstep (se 1 (by rfl) ⟨455984, by rfl⟩ : syracuseStep 607979 = 911969) B911969
theorem B509743 : Blo 401768 509743 := bstep (se 1 (by rfl) ⟨382307, by rfl⟩ : syracuseStep 509743 = 764615) B764615
theorem B608207 : Blo 401768 608207 := bstep (se 1 (by rfl) ⟨456155, by rfl⟩ : syracuseStep 608207 = 912311) B912311
theorem B7358521 : Blo 401768 7358521 := bstep (se 2 (by rfl) ⟨2759445, by rfl⟩ : syracuseStep 7358521 = 5518891) B5518891
theorem B510239 : Blo 401768 510239 := bstep (se 1 (by rfl) ⟨382679, by rfl⟩ : syracuseStep 510239 = 765359) B765359
theorem B608603 : Blo 401768 608603 := bstep (se 1 (by rfl) ⟨456452, by rfl⟩ : syracuseStep 608603 = 912905) B912905
theorem B6572431 : Blo 401768 6572431 := bstep (se 1 (by rfl) ⟨4929323, by rfl⟩ : syracuseStep 6572431 = 9858647) B9858647
theorem B1296823 : Blo 401768 1296823 := bstep (se 1 (by rfl) ⟨972617, by rfl⟩ : syracuseStep 1296823 = 1945235) B1945235
theorem B2444327 : Blo 401768 2444327 := bstep (se 1 (by rfl) ⟨1833245, by rfl⟩ : syracuseStep 2444327 = 3666491) B3666491
theorem B4344947 : Blo 401768 4344947 := bstep (se 1 (by rfl) ⟨3258710, by rfl⟩ : syracuseStep 4344947 = 6517421) B6517421
theorem B1363067 : Blo 401768 1363067 := bstep (se 1 (by rfl) ⟨1022300, by rfl⟩ : syracuseStep 1363067 = 2044601) B2044601
theorem B904391 : Blo 401768 904391 := bstep (se 1 (by rfl) ⟨678293, by rfl⟩ : syracuseStep 904391 = 1356587) B1356587
theorem B969947 : Blo 401768 969947 := bstep (se 1 (by rfl) ⟨727460, by rfl⟩ : syracuseStep 969947 = 1454921) B1454921
theorem B904571 : Blo 401768 904571 := bstep (se 1 (by rfl) ⟨678428, by rfl⟩ : syracuseStep 904571 = 1356857) B1356857
theorem B1363337 : Blo 401768 1363337 := bstep (se 2 (by rfl) ⟨511251, by rfl⟩ : syracuseStep 1363337 = 1022503) B1022503
theorem B1723835 : Blo 401768 1723835 := bstep (se 1 (by rfl) ⟨1292876, by rfl⟩ : syracuseStep 1723835 = 2585753) B2585753
theorem B904697 : Blo 401768 904697 := bstep (se 2 (by rfl) ⟨339261, by rfl⟩ : syracuseStep 904697 = 678523) B678523
theorem B904787 : Blo 401768 904787 := bstep (se 1 (by rfl) ⟨678590, by rfl⟩ : syracuseStep 904787 = 1357181) B1357181
theorem B4148945 : Blo 401768 4148945 := bstep (se 2 (by rfl) ⟨1555854, by rfl⟩ : syracuseStep 4148945 = 3111709) B3111709
theorem B904967 : Blo 401768 904967 := bstep (se 1 (by rfl) ⟨678725, by rfl⟩ : syracuseStep 904967 = 1357451) B1357451
theorem B1363769 : Blo 401768 1363769 := bstep (se 2 (by rfl) ⟨511413, by rfl⟩ : syracuseStep 1363769 = 1022827) B1022827
theorem B1724435 : Blo 401768 1724435 := bstep (se 1 (by rfl) ⟨1293326, by rfl⟩ : syracuseStep 1724435 = 2586653) B2586653
theorem B9818171 : Blo 401768 9818171 := bstep (se 1 (by rfl) ⟨7363628, by rfl⟩ : syracuseStep 9818171 = 14727257) B14727257
theorem B905579 : Blo 401768 905579 := bstep (se 1 (by rfl) ⟨679184, by rfl⟩ : syracuseStep 905579 = 1358369) B1358369
theorem B971119 : Blo 401768 971119 := bstep (se 1 (by rfl) ⟨728339, by rfl⟩ : syracuseStep 971119 = 1456679) B1456679
theorem B971233 : Blo 401768 971233 := bstep (se 2 (by rfl) ⟨364212, by rfl⟩ : syracuseStep 971233 = 728425) B728425
theorem B905723 : Blo 401768 905723 := bstep (se 1 (by rfl) ⟨679292, by rfl⟩ : syracuseStep 905723 = 1358585) B1358585
theorem B512507 : Blo 401768 512507 := bstep (se 1 (by rfl) ⟨384380, by rfl⟩ : syracuseStep 512507 = 768761) B768761
theorem B905849 : Blo 401768 905849 := bstep (se 2 (by rfl) ⟨339693, by rfl⟩ : syracuseStep 905849 = 679387) B679387
theorem B1364633 : Blo 401768 1364633 := bstep (se 2 (by rfl) ⟨511737, by rfl⟩ : syracuseStep 1364633 = 1023475) B1023475
theorem B905903 : Blo 401768 905903 := bstep (se 1 (by rfl) ⟨679427, by rfl⟩ : syracuseStep 905903 = 1358855) B1358855
theorem B905975 : Blo 401768 905975 := bstep (se 1 (by rfl) ⟨679481, by rfl⟩ : syracuseStep 905975 = 1358963) B1358963
theorem B2053025 : Blo 401768 2053025 := bstep (se 2 (by rfl) ⟨769884, by rfl⟩ : syracuseStep 2053025 = 1539769) B1539769
theorem B906155 : Blo 401768 906155 := bstep (se 1 (by rfl) ⟨679616, by rfl⟩ : syracuseStep 906155 = 1359233) B1359233
theorem B972071 : Blo 401768 972071 := bstep (se 1 (by rfl) ⟨729053, by rfl⟩ : syracuseStep 972071 = 1458107) B1458107
theorem B906695 : Blo 401768 906695 := bstep (se 1 (by rfl) ⟨680021, by rfl⟩ : syracuseStep 906695 = 1360043) B1360043
theorem B513479 : Blo 401768 513479 := bstep (se 1 (by rfl) ⟨385109, by rfl⟩ : syracuseStep 513479 = 770219) B770219
theorem B1529351 : Blo 401768 1529351 := bstep (se 1 (by rfl) ⟨1147013, by rfl⟩ : syracuseStep 1529351 = 2294027) B2294027
theorem B907055 : Blo 401768 907055 := bstep (se 1 (by rfl) ⟨680291, by rfl⟩ : syracuseStep 907055 = 1360583) B1360583
theorem B1529837 : Blo 401768 1529837 := bstep (se 3 (by rfl) ⟨286844, by rfl⟩ : syracuseStep 1529837 = 573689) B573689
theorem B1366145 : Blo 401768 1366145 := bstep (se 2 (by rfl) ⟨512304, by rfl⟩ : syracuseStep 1366145 = 1024609) B1024609
theorem B4348151 : Blo 401768 4348151 := bstep (se 1 (by rfl) ⟨3261113, by rfl⟩ : syracuseStep 4348151 = 6522227) B6522227
theorem B2578679 : Blo 401768 2578679 := bstep (se 1 (by rfl) ⟨1934009, by rfl⟩ : syracuseStep 2578679 = 3868019) B3868019
theorem B4348235 : Blo 401768 4348235 := bstep (se 1 (by rfl) ⟨3261176, by rfl⟩ : syracuseStep 4348235 = 6522353) B6522353
theorem B973147 : Blo 401768 973147 := bstep (se 1 (by rfl) ⟨729860, by rfl⟩ : syracuseStep 973147 = 1459721) B1459721
theorem B907631 : Blo 401768 907631 := bstep (se 1 (by rfl) ⟨680723, by rfl⟩ : syracuseStep 907631 = 1361447) B1361447
theorem B907703 : Blo 401768 907703 := bstep (se 1 (by rfl) ⟨680777, by rfl⟩ : syracuseStep 907703 = 1361555) B1361555
theorem B1530323 : Blo 401768 1530323 := bstep (se 1 (by rfl) ⟨1147742, by rfl⟩ : syracuseStep 1530323 = 2295485) B2295485
theorem B678395 : Blo 401768 678395 := bstep (se 1 (by rfl) ⟨508796, by rfl⟩ : syracuseStep 678395 = 1017593) B1017593
theorem B1366523 : Blo 401768 1366523 := bstep (se 1 (by rfl) ⟨1024892, by rfl⟩ : syracuseStep 1366523 = 2049785) B2049785
theorem B907847 : Blo 401768 907847 := bstep (se 1 (by rfl) ⟨680885, by rfl⟩ : syracuseStep 907847 = 1361771) B1361771
theorem B907883 : Blo 401768 907883 := bstep (se 1 (by rfl) ⟨680912, by rfl⟩ : syracuseStep 907883 = 1361825) B1361825
theorem B678827 : Blo 401768 678827 := bstep (se 1 (by rfl) ⟨509120, by rfl⟩ : syracuseStep 678827 = 1018241) B1018241
theorem B1366955 : Blo 401768 1366955 := bstep (se 1 (by rfl) ⟨1025216, by rfl⟩ : syracuseStep 1366955 = 2050433) B2050433
theorem B908279 : Blo 401768 908279 := bstep (se 1 (by rfl) ⟨681209, by rfl⟩ : syracuseStep 908279 = 1362419) B1362419
theorem B908639 : Blo 401768 908639 := bstep (se 1 (by rfl) ⟨681479, by rfl⟩ : syracuseStep 908639 = 1362959) B1362959
theorem B679367 : Blo 401768 679367 := bstep (se 1 (by rfl) ⟨509525, by rfl⟩ : syracuseStep 679367 = 1019051) B1019051
theorem B613831 : Blo 401768 613831 := bstep (se 1 (by rfl) ⟨460373, by rfl⟩ : syracuseStep 613831 = 920747) B920747
theorem B1367495 : Blo 401768 1367495 := bstep (se 1 (by rfl) ⟨1025621, by rfl⟩ : syracuseStep 1367495 = 2051243) B2051243
theorem B2186833 : Blo 401768 2186833 := bstep (se 2 (by rfl) ⟨820062, by rfl⟩ : syracuseStep 2186833 = 1640125) B1640125
theorem B1629811 : Blo 401768 1629811 := bstep (se 1 (by rfl) ⟨1222358, by rfl⟩ : syracuseStep 1629811 = 2444717) B2444717
theorem B1531507 : Blo 401768 1531507 := bstep (se 1 (by rfl) ⟨1148630, by rfl⟩ : syracuseStep 1531507 = 2297261) B2297261
theorem B1728209 : Blo 401768 1728209 := bstep (se 2 (by rfl) ⟨648078, by rfl⟩ : syracuseStep 1728209 = 1296157) B1296157
theorem B909035 : Blo 401768 909035 := bstep (se 1 (by rfl) ⟨681776, by rfl⟩ : syracuseStep 909035 = 1363553) B1363553
theorem B1367819 : Blo 401768 1367819 := bstep (se 1 (by rfl) ⟨1025864, by rfl⟩ : syracuseStep 1367819 = 2051729) B2051729
theorem B909161 : Blo 401768 909161 := bstep (se 2 (by rfl) ⟨340935, by rfl⟩ : syracuseStep 909161 = 681871) B681871
theorem B1368089 : Blo 401768 1368089 := bstep (se 2 (by rfl) ⟨513033, by rfl⟩ : syracuseStep 1368089 = 1026067) B1026067
theorem B942443 : Blo 401768 942443 := bstep (se 1 (by rfl) ⟨706832, by rfl⟩ : syracuseStep 942443 = 1413665) B1413665
theorem B1532267 : Blo 401768 1532267 := bstep (se 1 (by rfl) ⟨1149200, by rfl⟩ : syracuseStep 1532267 = 2298401) B2298401
theorem B680359 : Blo 401768 680359 := bstep (se 1 (by rfl) ⟨510269, by rfl⟩ : syracuseStep 680359 = 1020539) B1020539
theorem B7725577 : Blo 401768 7725577 := bstep (se 2 (by rfl) ⟨2897091, by rfl⟩ : syracuseStep 7725577 = 5794183) B5794183
theorem B680521 : Blo 401768 680521 := bstep (se 2 (by rfl) ⟨255195, by rfl⟩ : syracuseStep 680521 = 510391) B510391
theorem B680555 : Blo 401768 680555 := bstep (se 1 (by rfl) ⟨510416, by rfl⟩ : syracuseStep 680555 = 1020833) B1020833
theorem B2581139 : Blo 401768 2581139 := bstep (se 1 (by rfl) ⟨1935854, by rfl⟩ : syracuseStep 2581139 = 3871709) B3871709
theorem B910007 : Blo 401768 910007 := bstep (se 1 (by rfl) ⟨682505, by rfl⟩ : syracuseStep 910007 = 1365011) B1365011
theorem B910223 : Blo 401768 910223 := bstep (se 1 (by rfl) ⟨682667, by rfl⟩ : syracuseStep 910223 = 1365335) B1365335
theorem B1631431 : Blo 401768 1631431 := bstep (se 1 (by rfl) ⟨1223573, by rfl⟩ : syracuseStep 1631431 = 2447147) B2447147
theorem B648425 : Blo 401768 648425 := bstep (se 2 (by rfl) ⟨243159, by rfl⟩ : syracuseStep 648425 = 486319) B486319
theorem B1369331 : Blo 401768 1369331 := bstep (se 1 (by rfl) ⟨1026998, by rfl⟩ : syracuseStep 1369331 = 2053997) B2053997
theorem B1369439 : Blo 401768 1369439 := bstep (se 1 (by rfl) ⟨1027079, by rfl⟩ : syracuseStep 1369439 = 2054159) B2054159
theorem B452191 : Blo 401768 452191 := bstep (se 1 (by rfl) ⟨339143, by rfl⟩ : syracuseStep 452191 = 678287) B678287
theorem B910943 : Blo 401768 910943 := bstep (se 1 (by rfl) ⟨683207, by rfl⟩ : syracuseStep 910943 = 1366415) B1366415
theorem B911159 : Blo 401768 911159 := bstep (se 1 (by rfl) ⟨683369, by rfl⟩ : syracuseStep 911159 = 1366739) B1366739
theorem B5891945 : Blo 401768 5891945 := bstep (se 2 (by rfl) ⟨2209479, by rfl⟩ : syracuseStep 5891945 = 4418959) B4418959
theorem B911465 : Blo 401768 911465 := bstep (se 2 (by rfl) ⟨341799, by rfl⟩ : syracuseStep 911465 = 683599) B683599
theorem B126412973 : Blo 401768 126412973 := bstep (se 3 (by rfl) ⟨23702432, by rfl⟩ : syracuseStep 126412973 = 47404865) B47404865
theorem B1730807 : Blo 401768 1730807 := bstep (se 1 (by rfl) ⟨1298105, by rfl⟩ : syracuseStep 1730807 = 2596211) B2596211
theorem B682249 : Blo 401768 682249 := bstep (se 2 (by rfl) ⟨255843, by rfl⟩ : syracuseStep 682249 = 511687) B511687
theorem B4647341 : Blo 401768 4647341 := bstep (se 3 (by rfl) ⟨871376, by rfl⟩ : syracuseStep 4647341 = 1742753) B1742753
theorem B911951 : Blo 401768 911951 := bstep (se 1 (by rfl) ⟨683963, by rfl⟩ : syracuseStep 911951 = 1367927) B1367927
theorem B7269041 : Blo 401768 7269041 := bstep (se 2 (by rfl) ⟨2725890, by rfl⟩ : syracuseStep 7269041 = 5451781) B5451781
theorem B453343 : Blo 401768 453343 := bstep (se 1 (by rfl) ⟨340007, by rfl⟩ : syracuseStep 453343 = 680015) B680015
theorem B912095 : Blo 401768 912095 := bstep (se 1 (by rfl) ⟨684071, by rfl⟩ : syracuseStep 912095 = 1368143) B1368143
theorem B6875927 : Blo 401768 6875927 := bstep (se 1 (by rfl) ⟨5156945, by rfl⟩ : syracuseStep 6875927 = 10313891) B10313891
theorem B4385603 : Blo 401768 4385603 := bstep (se 1 (by rfl) ⟨3289202, by rfl⟩ : syracuseStep 4385603 = 6578405) B6578405
theorem B5172119 : Blo 401768 5172119 := bstep (se 1 (by rfl) ⟨3879089, by rfl⟩ : syracuseStep 5172119 = 7758179) B7758179
theorem B284322757 : Blo 401768 284322757 := bstep (se 4 (by rfl) ⟨26655258, by rfl⟩ : syracuseStep 284322757 = 53310517) B53310517
theorem B912347 : Blo 401768 912347 := bstep (se 1 (by rfl) ⟨684260, by rfl⟩ : syracuseStep 912347 = 1368521) B1368521
theorem B912527 : Blo 401768 912527 := bstep (se 1 (by rfl) ⟨684395, by rfl⟩ : syracuseStep 912527 = 1368791) B1368791
theorem B912617 : Blo 401768 912617 := bstep (se 2 (by rfl) ⟨342231, by rfl⟩ : syracuseStep 912617 = 684463) B684463
theorem B453919 : Blo 401768 453919 := bstep (se 1 (by rfl) ⟨340439, by rfl⟩ : syracuseStep 453919 = 680879) B680879
theorem B912671 : Blo 401768 912671 := bstep (se 1 (by rfl) ⟨684503, by rfl⟩ : syracuseStep 912671 = 1369007) B1369007
theorem B454207 : Blo 401768 454207 := bstep (se 1 (by rfl) ⟨340655, by rfl⟩ : syracuseStep 454207 = 681311) B681311
theorem B1011295 : Blo 401768 1011295 := bstep (se 1 (by rfl) ⟨758471, by rfl⟩ : syracuseStep 1011295 = 1516943) B1516943
theorem B683707 : Blo 401768 683707 := bstep (se 1 (by rfl) ⟨512780, by rfl⟩ : syracuseStep 683707 = 1025561) B1025561
theorem B455035 : Blo 401768 455035 := bstep (se 1 (by rfl) ⟨341276, by rfl⟩ : syracuseStep 455035 = 682553) B682553
theorem B455503 : Blo 401768 455503 := bstep (se 1 (by rfl) ⟨341627, by rfl⟩ : syracuseStep 455503 = 683255) B683255
theorem B16610197 : Blo 401768 16610197 := bstep (se 6 (by rfl) ⟨389301, by rfl⟩ : syracuseStep 16610197 = 778603) B778603
theorem B2290679 : Blo 401768 2290679 := bstep (se 1 (by rfl) ⟨1718009, by rfl⟩ : syracuseStep 2290679 = 3436019) B3436019
theorem B455899 : Blo 401768 455899 := bstep (se 1 (by rfl) ⟨341924, by rfl⟩ : syracuseStep 455899 = 683849) B683849
theorem B2913529 : Blo 401768 2913529 := bstep (se 2 (by rfl) ⟨1092573, by rfl⟩ : syracuseStep 2913529 = 2185147) B2185147
theorem B456187 : Blo 401768 456187 := bstep (se 1 (by rfl) ⟨342140, by rfl⟩ : syracuseStep 456187 = 684281) B684281
theorem B456367 : Blo 401768 456367 := bstep (se 1 (by rfl) ⟨342275, by rfl⟩ : syracuseStep 456367 = 684551) B684551
theorem B57834163 : Blo 401768 57834163 := bstep (se 1 (by rfl) ⟨43375622, by rfl⟩ : syracuseStep 57834163 = 86751245) B86751245
theorem B6880301 : Blo 401768 6880301 := bstep (se 3 (by rfl) ⟨1290056, by rfl⟩ : syracuseStep 6880301 = 2580113) B2580113
theorem B1637729 : Blo 401768 1637729 := bstep (se 2 (by rfl) ⟨614148, by rfl⟩ : syracuseStep 1637729 = 1228297) B1228297
theorem B458303 : Blo 401768 458303 := bstep (se 1 (by rfl) ⟨343727, by rfl⟩ : syracuseStep 458303 = 687455) B687455
theorem B2293343 : Blo 401768 2293343 := bstep (se 1 (by rfl) ⟨1720007, by rfl⟩ : syracuseStep 2293343 = 3440015) B3440015
theorem B1572587 : Blo 401768 1572587 := bstep (se 1 (by rfl) ⟨1179440, by rfl⟩ : syracuseStep 1572587 = 2358881) B2358881
theorem B23265305 : Blo 401768 23265305 := bstep (se 2 (by rfl) ⟨8724489, by rfl⟩ : syracuseStep 23265305 = 17448979) B17448979
theorem B2490401 : Blo 401768 2490401 := bstep (se 2 (by rfl) ⟨933900, by rfl⟩ : syracuseStep 2490401 = 1867801) B1867801
theorem B1540559 : Blo 401768 1540559 := bstep (se 1 (by rfl) ⟨1155419, by rfl⟩ : syracuseStep 1540559 = 2310839) B2310839
theorem B4162043 : Blo 401768 4162043 := bstep (se 1 (by rfl) ⟨3121532, by rfl⟩ : syracuseStep 4162043 = 6243065) B6243065
theorem B3080753 : Blo 401768 3080753 := bstep (se 2 (by rfl) ⟨1155282, by rfl⟩ : syracuseStep 3080753 = 2310565) B2310565
theorem B5178269 : Blo 401768 5178269 := bstep (se 3 (by rfl) ⟨970925, by rfl⟩ : syracuseStep 5178269 = 1941851) B1941851
theorem B1639379 : Blo 401768 1639379 := bstep (se 1 (by rfl) ⟨1229534, by rfl⟩ : syracuseStep 1639379 = 2459069) B2459069
theorem B1147891 : Blo 401768 1147891 := bstep (se 1 (by rfl) ⟨860918, by rfl⟩ : syracuseStep 1147891 = 1721837) B1721837
theorem B2917367 : Blo 401768 2917367 := bstep (se 1 (by rfl) ⟨2188025, by rfl⟩ : syracuseStep 2917367 = 4376051) B4376051
theorem B2360927 : Blo 401768 2360927 := bstep (se 1 (by rfl) ⟨1770695, by rfl⟩ : syracuseStep 2360927 = 3541391) B3541391
theorem B2066305 : Blo 401768 2066305 := bstep (se 2 (by rfl) ⟨774864, by rfl⟩ : syracuseStep 2066305 = 1549729) B1549729
theorem B1149223 : Blo 401768 1149223 := bstep (se 1 (by rfl) ⟨861917, by rfl⟩ : syracuseStep 1149223 = 1723835) B1723835
theorem B5179909 : Blo 401768 5179909 := bstep (se 4 (by rfl) ⟨485616, by rfl⟩ : syracuseStep 5179909 = 971233) B971233
theorem B1149623 : Blo 401768 1149623 := bstep (se 1 (by rfl) ⟨862217, by rfl⟩ : syracuseStep 1149623 = 1724435) B1724435
theorem B2591777 : Blo 401768 2591777 := bstep (se 2 (by rfl) ⟨971916, by rfl⟩ : syracuseStep 2591777 = 1943833) B1943833
theorem B5836283 : Blo 401768 5836283 := bstep (se 1 (by rfl) ⟨4377212, by rfl⟩ : syracuseStep 5836283 = 8754425) B8754425
theorem B2461265 : Blo 401768 2461265 := bstep (se 2 (by rfl) ⟨922974, by rfl⟩ : syracuseStep 2461265 = 1845949) B1845949
theorem B1019567 : Blo 401768 1019567 := bstep (se 1 (by rfl) ⟨764675, by rfl⟩ : syracuseStep 1019567 = 1529351) B1529351
theorem B1150841 : Blo 401768 1150841 := bstep (se 2 (by rfl) ⟨431565, by rfl⟩ : syracuseStep 1150841 = 863131) B863131
theorem B379097009 : Blo 401768 379097009 := bstep (se 2 (by rfl) ⟨142161378, by rfl⟩ : syracuseStep 379097009 = 284322757) B284322757
theorem B1019891 : Blo 401768 1019891 := bstep (se 1 (by rfl) ⟨764918, by rfl⟩ : syracuseStep 1019891 = 1529837) B1529837
theorem B1020215 : Blo 401768 1020215 := bstep (se 1 (by rfl) ⟨765161, by rfl⟩ : syracuseStep 1020215 = 1530323) B1530323
theorem B1380959 : Blo 401768 1380959 := bstep (se 1 (by rfl) ⟨1035719, by rfl⟩ : syracuseStep 1380959 = 2071439) B2071439
theorem B2036339 : Blo 401768 2036339 := bstep (se 1 (by rfl) ⟨1527254, by rfl⟩ : syracuseStep 2036339 = 3054509) B3054509
theorem B1348393 : Blo 401768 1348393 := bstep (se 2 (by rfl) ⟨505647, by rfl⟩ : syracuseStep 1348393 = 1011295) B1011295
theorem B10327013 : Blo 401768 10327013 := bstep (se 4 (by rfl) ⟨968157, by rfl⟩ : syracuseStep 10327013 = 1936315) B1936315
theorem B1152139 : Blo 401768 1152139 := bstep (se 1 (by rfl) ⟨864104, by rfl⟩ : syracuseStep 1152139 = 1728209) B1728209
theorem B9311377 : Blo 401768 9311377 := bstep (se 2 (by rfl) ⟨3491766, by rfl⟩ : syracuseStep 9311377 = 6983533) B6983533
theorem B3282295 : Blo 401768 3282295 := bstep (se 1 (by rfl) ⟨2461721, by rfl⟩ : syracuseStep 3282295 = 4923443) B4923443
theorem B1152481 : Blo 401768 1152481 := bstep (se 2 (by rfl) ⟨432180, by rfl⟩ : syracuseStep 1152481 = 864361) B864361
theorem B628295 : Blo 401768 628295 := bstep (se 1 (by rfl) ⟨471221, by rfl⟩ : syracuseStep 628295 = 942443) B942443
theorem B1021511 : Blo 401768 1021511 := bstep (se 1 (by rfl) ⟨766133, by rfl⟩ : syracuseStep 1021511 = 1532267) B1532267
theorem B3151673 : Blo 401768 3151673 := bstep (se 2 (by rfl) ⟨1181877, by rfl⟩ : syracuseStep 3151673 = 2363755) B2363755
theorem B2037959 : Blo 401768 2037959 := bstep (se 1 (by rfl) ⟨1528469, by rfl⟩ : syracuseStep 2037959 = 3056939) B3056939
theorem B12392909 : Blo 401768 12392909 := bstep (se 3 (by rfl) ⟨2323670, by rfl⟩ : syracuseStep 12392909 = 4647341) B4647341
theorem B1153871 : Blo 401768 1153871 := bstep (se 1 (by rfl) ⟨865403, by rfl⟩ : syracuseStep 1153871 = 1730807) B1730807
theorem B2759507 : Blo 401768 2759507 := bstep (se 1 (by rfl) ⟨2069630, by rfl⟩ : syracuseStep 2759507 = 4139261) B4139261
theorem B2038931 : Blo 401768 2038931 := bstep (se 1 (by rfl) ⟨1529198, by rfl⟩ : syracuseStep 2038931 = 3058397) B3058397
theorem B2923735 : Blo 401768 2923735 := bstep (se 1 (by rfl) ⟨2192801, by rfl⟩ : syracuseStep 2923735 = 4385603) B4385603
theorem B3448079 : Blo 401768 3448079 := bstep (se 1 (by rfl) ⟨2586059, by rfl⟩ : syracuseStep 3448079 = 5172119) B5172119
theorem B5905979 : Blo 401768 5905979 := bstep (se 1 (by rfl) ⟨4429484, by rfl⟩ : syracuseStep 5905979 = 8858969) B8858969
theorem B925409 : Blo 401768 925409 := bstep (se 2 (by rfl) ⟨347028, by rfl⟩ : syracuseStep 925409 = 694057) B694057
theorem B2039741 : Blo 401768 2039741 := bstep (se 3 (by rfl) ⟨382451, by rfl⟩ : syracuseStep 2039741 = 764903) B764903
theorem B401791 : Blo 401768 401791 := bstep (se 1 (by rfl) ⟨301343, by rfl⟩ : syracuseStep 401791 = 602687) B602687
theorem B401871 : Blo 401768 401871 := bstep (se 1 (by rfl) ⟨301403, by rfl⟩ : syracuseStep 401871 = 602807) B602807
theorem B402023 : Blo 401768 402023 := bstep (se 1 (by rfl) ⟨301517, by rfl⟩ : syracuseStep 402023 = 603035) B603035
theorem B402287 : Blo 401768 402287 := bstep (se 1 (by rfl) ⟨301715, by rfl⟩ : syracuseStep 402287 = 603431) B603431
theorem B77112217 : Blo 401768 77112217 := bstep (se 2 (by rfl) ⟨28917081, by rfl⟩ : syracuseStep 77112217 = 57834163) B57834163
theorem B402343 : Blo 401768 402343 := bstep (se 1 (by rfl) ⟨301757, by rfl⟩ : syracuseStep 402343 = 603515) B603515
theorem B402427 : Blo 401768 402427 := bstep (se 1 (by rfl) ⟨301820, by rfl⟩ : syracuseStep 402427 = 603641) B603641
theorem B402495 : Blo 401768 402495 := bstep (se 1 (by rfl) ⟨301871, by rfl⟩ : syracuseStep 402495 = 603743) B603743
theorem B402639 : Blo 401768 402639 := bstep (se 1 (by rfl) ⟨301979, by rfl⟩ : syracuseStep 402639 = 603959) B603959
theorem B4662479 : Blo 401768 4662479 := bstep (se 1 (by rfl) ⟨3496859, by rfl⟩ : syracuseStep 4662479 = 6993719) B6993719
theorem B402843 : Blo 401768 402843 := bstep (se 1 (by rfl) ⟨302132, by rfl⟩ : syracuseStep 402843 = 604265) B604265
theorem B1222141 : Blo 401768 1222141 := bstep (se 3 (by rfl) ⟨229151, by rfl⟩ : syracuseStep 1222141 = 458303) B458303
theorem B403055 : Blo 401768 403055 := bstep (se 1 (by rfl) ⟨302291, by rfl⟩ : syracuseStep 403055 = 604583) B604583
theorem B403111 : Blo 401768 403111 := bstep (se 1 (by rfl) ⟨302333, by rfl⟩ : syracuseStep 403111 = 604667) B604667
theorem B403195 : Blo 401768 403195 := bstep (se 1 (by rfl) ⟨302396, by rfl⟩ : syracuseStep 403195 = 604793) B604793
theorem B403231 : Blo 401768 403231 := bstep (se 1 (by rfl) ⟨302423, by rfl⟩ : syracuseStep 403231 = 604847) B604847
theorem B403263 : Blo 401768 403263 := bstep (se 1 (by rfl) ⟨302447, by rfl⟩ : syracuseStep 403263 = 604895) B604895
theorem B1386319 : Blo 401768 1386319 := bstep (se 1 (by rfl) ⟨1039739, by rfl⟩ : syracuseStep 1386319 = 2079479) B2079479
theorem B403439 : Blo 401768 403439 := bstep (se 1 (by rfl) ⟨302579, by rfl⟩ : syracuseStep 403439 = 605159) B605159
theorem B2041847 : Blo 401768 2041847 := bstep (se 1 (by rfl) ⟨1531385, by rfl⟩ : syracuseStep 2041847 = 3062771) B3062771
theorem B2173081 : Blo 401768 2173081 := bstep (se 2 (by rfl) ⟨814905, by rfl⟩ : syracuseStep 2173081 = 1629811) B1629811
theorem B2042009 : Blo 401768 2042009 := bstep (se 2 (by rfl) ⟨765753, by rfl⟩ : syracuseStep 2042009 = 1531507) B1531507
theorem B403611 : Blo 401768 403611 := bstep (se 1 (by rfl) ⟨302708, by rfl⟩ : syracuseStep 403611 = 605417) B605417
theorem B403647 : Blo 401768 403647 := bstep (se 1 (by rfl) ⟨302735, by rfl⟩ : syracuseStep 403647 = 605471) B605471
theorem B1091819 : Blo 401768 1091819 := bstep (se 1 (by rfl) ⟨818864, by rfl⟩ : syracuseStep 1091819 = 1637729) B1637729
theorem B403759 : Blo 401768 403759 := bstep (se 1 (by rfl) ⟨302819, by rfl⟩ : syracuseStep 403759 = 605639) B605639
theorem B862559 : Blo 401768 862559 := bstep (se 1 (by rfl) ⟨646919, by rfl⟩ : syracuseStep 862559 = 1293839) B1293839
theorem B403995 : Blo 401768 403995 := bstep (se 1 (by rfl) ⟨302996, by rfl⟩ : syracuseStep 403995 = 605993) B605993
theorem B403999 : Blo 401768 403999 := bstep (se 1 (by rfl) ⟨302999, by rfl⟩ : syracuseStep 403999 = 605999) B605999
theorem B2304551 : Blo 401768 2304551 := bstep (se 1 (by rfl) ⟨1728413, by rfl⟩ : syracuseStep 2304551 = 3456827) B3456827
theorem B2173511 : Blo 401768 2173511 := bstep (se 1 (by rfl) ⟨1630133, by rfl⟩ : syracuseStep 2173511 = 3260267) B3260267
theorem B1026665 : Blo 401768 1026665 := bstep (se 2 (by rfl) ⟨384999, by rfl⟩ : syracuseStep 1026665 = 769999) B769999
theorem B404315 : Blo 401768 404315 := bstep (se 1 (by rfl) ⟨303236, by rfl⟩ : syracuseStep 404315 = 606473) B606473
theorem B404383 : Blo 401768 404383 := bstep (se 1 (by rfl) ⟨303287, by rfl⟩ : syracuseStep 404383 = 606575) B606575
theorem B2042819 : Blo 401768 2042819 := bstep (se 1 (by rfl) ⟨1532114, by rfl⟩ : syracuseStep 2042819 = 3064229) B3064229
theorem B7187429 : Blo 401768 7187429 := bstep (se 4 (by rfl) ⟨673821, by rfl⟩ : syracuseStep 7187429 = 1347643) B1347643
theorem B1453103 : Blo 401768 1453103 := bstep (se 1 (by rfl) ⟨1089827, by rfl⟩ : syracuseStep 1453103 = 2179655) B2179655
theorem B404527 : Blo 401768 404527 := bstep (se 1 (by rfl) ⟨303395, by rfl⟩ : syracuseStep 404527 = 606791) B606791
theorem B404551 : Blo 401768 404551 := bstep (se 1 (by rfl) ⟨303413, by rfl⟩ : syracuseStep 404551 = 606827) B606827
theorem B863455 : Blo 401768 863455 := bstep (se 1 (by rfl) ⟨647591, by rfl⟩ : syracuseStep 863455 = 1295183) B1295183
theorem B404703 : Blo 401768 404703 := bstep (se 1 (by rfl) ⟨303527, by rfl⟩ : syracuseStep 404703 = 607055) B607055
theorem B10300769 : Blo 401768 10300769 := bstep (se 2 (by rfl) ⟨3862788, by rfl⟩ : syracuseStep 10300769 = 7725577) B7725577
theorem B404967 : Blo 401768 404967 := bstep (se 1 (by rfl) ⟨303725, by rfl⟩ : syracuseStep 404967 = 607451) B607451
theorem B405083 : Blo 401768 405083 := bstep (se 1 (by rfl) ⟨303812, by rfl⟩ : syracuseStep 405083 = 607625) B607625
theorem B6205177 : Blo 401768 6205177 := bstep (se 2 (by rfl) ⟨2326941, by rfl⟩ : syracuseStep 6205177 = 4653883) B4653883
theorem B405319 : Blo 401768 405319 := bstep (se 1 (by rfl) ⟨303989, by rfl⟩ : syracuseStep 405319 = 607979) B607979
theorem B405471 : Blo 401768 405471 := bstep (se 1 (by rfl) ⟨304103, by rfl⟩ : syracuseStep 405471 = 608207) B608207
theorem B405735 : Blo 401768 405735 := bstep (se 1 (by rfl) ⟨304301, by rfl⟩ : syracuseStep 405735 = 608603) B608603
theorem B1454345 : Blo 401768 1454345 := bstep (se 2 (by rfl) ⟨545379, by rfl⟩ : syracuseStep 1454345 = 1090759) B1090759
theorem B13054445 : Blo 401768 13054445 := bstep (se 3 (by rfl) ⟨2447708, by rfl⟩ : syracuseStep 13054445 = 4895417) B4895417
theorem B1356371 : Blo 401768 1356371 := bstep (se 1 (by rfl) ⟨1017278, by rfl⟩ : syracuseStep 1356371 = 2034557) B2034557
theorem B766559 : Blo 401768 766559 := bstep (se 1 (by rfl) ⟨574919, by rfl⟩ : syracuseStep 766559 = 1149839) B1149839
theorem B2896631 : Blo 401768 2896631 := bstep (se 1 (by rfl) ⟨2172473, by rfl⟩ : syracuseStep 2896631 = 4344947) B4344947
theorem B602921 : Blo 401768 602921 := bstep (se 2 (by rfl) ⟨226095, by rfl⟩ : syracuseStep 602921 = 452191) B452191
theorem B602927 : Blo 401768 602927 := bstep (se 1 (by rfl) ⟨452195, by rfl⟩ : syracuseStep 602927 = 904391) B904391
theorem B14725961 : Blo 401768 14725961 := bstep (se 2 (by rfl) ⟨5522235, by rfl⟩ : syracuseStep 14725961 = 11044471) B11044471
theorem B603047 : Blo 401768 603047 := bstep (se 1 (by rfl) ⟨452285, by rfl⟩ : syracuseStep 603047 = 904571) B904571
theorem B603131 : Blo 401768 603131 := bstep (se 1 (by rfl) ⟨452348, by rfl⟩ : syracuseStep 603131 = 904697) B904697
theorem B603191 : Blo 401768 603191 := bstep (se 1 (by rfl) ⟨452393, by rfl⟩ : syracuseStep 603191 = 904787) B904787
theorem B10663001 : Blo 401768 10663001 := bstep (se 2 (by rfl) ⟨3998625, by rfl⟩ : syracuseStep 10663001 = 7997251) B7997251
theorem B767083 : Blo 401768 767083 := bstep (se 1 (by rfl) ⟨575312, by rfl⟩ : syracuseStep 767083 = 1150625) B1150625
theorem B2765963 : Blo 401768 2765963 := bstep (se 1 (by rfl) ⟨2074472, by rfl⟩ : syracuseStep 2765963 = 4148945) B4148945
theorem B603311 : Blo 401768 603311 := bstep (se 1 (by rfl) ⟨452483, by rfl⟩ : syracuseStep 603311 = 904967) B904967
theorem B1357019 : Blo 401768 1357019 := bstep (se 1 (by rfl) ⟨1017764, by rfl⟩ : syracuseStep 1357019 = 2035529) B2035529
theorem B767387 : Blo 401768 767387 := bstep (se 1 (by rfl) ⟨575540, by rfl⟩ : syracuseStep 767387 = 1151081) B1151081
theorem B9811361 : Blo 401768 9811361 := bstep (se 2 (by rfl) ⟨3679260, by rfl⟩ : syracuseStep 9811361 = 7358521) B7358521
theorem B1095137 : Blo 401768 1095137 := bstep (se 2 (by rfl) ⟨410676, by rfl⟩ : syracuseStep 1095137 = 821353) B821353
theorem B603719 : Blo 401768 603719 := bstep (se 1 (by rfl) ⟨452789, by rfl⟩ : syracuseStep 603719 = 905579) B905579
theorem B603815 : Blo 401768 603815 := bstep (se 1 (by rfl) ⟨452861, by rfl⟩ : syracuseStep 603815 = 905723) B905723
theorem B603899 : Blo 401768 603899 := bstep (se 1 (by rfl) ⟨452924, by rfl⟩ : syracuseStep 603899 = 905849) B905849
theorem B603935 : Blo 401768 603935 := bstep (se 1 (by rfl) ⟨452951, by rfl⟩ : syracuseStep 603935 = 905903) B905903
theorem B603983 : Blo 401768 603983 := bstep (se 1 (by rfl) ⟨452987, by rfl⟩ : syracuseStep 603983 = 905975) B905975
theorem B8763241 : Blo 401768 8763241 := bstep (se 2 (by rfl) ⟨3286215, by rfl⟩ : syracuseStep 8763241 = 6572431) B6572431
theorem B604103 : Blo 401768 604103 := bstep (se 1 (by rfl) ⟨453077, by rfl⟩ : syracuseStep 604103 = 906155) B906155
theorem B1357883 : Blo 401768 1357883 := bstep (se 1 (by rfl) ⟨1018412, by rfl⟩ : syracuseStep 1357883 = 2036825) B2036825
theorem B604457 : Blo 401768 604457 := bstep (se 2 (by rfl) ⟨226671, by rfl⟩ : syracuseStep 604457 = 453343) B453343
theorem B604463 : Blo 401768 604463 := bstep (se 1 (by rfl) ⟨453347, by rfl⟩ : syracuseStep 604463 = 906695) B906695
theorem B1358153 : Blo 401768 1358153 := bstep (se 2 (by rfl) ⟨509307, by rfl⟩ : syracuseStep 1358153 = 1018615) B1018615
theorem B604703 : Blo 401768 604703 := bstep (se 1 (by rfl) ⟨453527, by rfl⟩ : syracuseStep 604703 = 907055) B907055
theorem B1456793 : Blo 401768 1456793 := bstep (se 2 (by rfl) ⟨546297, by rfl⟩ : syracuseStep 1456793 = 1092595) B1092595
theorem B3324739 : Blo 401768 3324739 := bstep (se 1 (by rfl) ⟨2493554, by rfl⟩ : syracuseStep 3324739 = 4987109) B4987109
theorem B2898767 : Blo 401768 2898767 := bstep (se 1 (by rfl) ⟨2174075, by rfl⟩ : syracuseStep 2898767 = 4348151) B4348151
theorem B1719119 : Blo 401768 1719119 := bstep (se 1 (by rfl) ⟨1289339, by rfl⟩ : syracuseStep 1719119 = 2578679) B2578679
theorem B965459 : Blo 401768 965459 := bstep (se 1 (by rfl) ⟨724094, by rfl⟩ : syracuseStep 965459 = 1448189) B1448189
theorem B965467 : Blo 401768 965467 := bstep (se 1 (by rfl) ⟨724100, by rfl⟩ : syracuseStep 965467 = 1448201) B1448201
theorem B1096553 : Blo 401768 1096553 := bstep (se 2 (by rfl) ⟨411207, by rfl⟩ : syracuseStep 1096553 = 822415) B822415
theorem B2898823 : Blo 401768 2898823 := bstep (se 1 (by rfl) ⟨2174117, by rfl⟩ : syracuseStep 2898823 = 4348235) B4348235
theorem B605087 : Blo 401768 605087 := bstep (se 1 (by rfl) ⟨453815, by rfl⟩ : syracuseStep 605087 = 907631) B907631
theorem B605135 : Blo 401768 605135 := bstep (se 1 (by rfl) ⟨453851, by rfl⟩ : syracuseStep 605135 = 907703) B907703
theorem B605225 : Blo 401768 605225 := bstep (se 2 (by rfl) ⟨226959, by rfl⟩ : syracuseStep 605225 = 453919) B453919
theorem B605231 : Blo 401768 605231 := bstep (se 1 (by rfl) ⟨453923, by rfl⟩ : syracuseStep 605231 = 907847) B907847
theorem B605255 : Blo 401768 605255 := bstep (se 1 (by rfl) ⟨453941, by rfl⟩ : syracuseStep 605255 = 907883) B907883
theorem B1948967 : Blo 401768 1948967 := bstep (se 1 (by rfl) ⟨1461725, by rfl⟩ : syracuseStep 1948967 = 2923451) B2923451
theorem B605519 : Blo 401768 605519 := bstep (se 1 (by rfl) ⟨454139, by rfl⟩ : syracuseStep 605519 = 908279) B908279
theorem B605609 : Blo 401768 605609 := bstep (se 2 (by rfl) ⟨227103, by rfl⟩ : syracuseStep 605609 = 454207) B454207
theorem B605759 : Blo 401768 605759 := bstep (se 1 (by rfl) ⟨454319, by rfl⟩ : syracuseStep 605759 = 908639) B908639
theorem B15711853 : Blo 401768 15711853 := bstep (se 3 (by rfl) ⟨2945972, by rfl⟩ : syracuseStep 15711853 = 5891945) B5891945
theorem B1359503 : Blo 401768 1359503 := bstep (se 1 (by rfl) ⟨1019627, by rfl⟩ : syracuseStep 1359503 = 2039255) B2039255
theorem B606023 : Blo 401768 606023 := bstep (se 1 (by rfl) ⟨454517, by rfl⟩ : syracuseStep 606023 = 909035) B909035
theorem B769915 : Blo 401768 769915 := bstep (se 1 (by rfl) ⟨577436, by rfl⟩ : syracuseStep 769915 = 1154873) B1154873
theorem B606107 : Blo 401768 606107 := bstep (se 1 (by rfl) ⟨454580, by rfl⟩ : syracuseStep 606107 = 909161) B909161
theorem B29606309 : Blo 401768 29606309 := bstep (se 4 (by rfl) ⟨2775591, by rfl⟩ : syracuseStep 29606309 = 5551183) B5551183
theorem B1720759 : Blo 401768 1720759 := bstep (se 1 (by rfl) ⟨1290569, by rfl⟩ : syracuseStep 1720759 = 2581139) B2581139
theorem B606671 : Blo 401768 606671 := bstep (se 1 (by rfl) ⟨455003, by rfl⟩ : syracuseStep 606671 = 910007) B910007
theorem B1294825 : Blo 401768 1294825 := bstep (se 2 (by rfl) ⟨485559, by rfl⟩ : syracuseStep 1294825 = 971119) B971119
theorem B606713 : Blo 401768 606713 := bstep (se 2 (by rfl) ⟨227517, by rfl⟩ : syracuseStep 606713 = 455035) B455035
theorem B606815 : Blo 401768 606815 := bstep (se 1 (by rfl) ⟨455111, by rfl⟩ : syracuseStep 606815 = 910223) B910223
theorem B2277985 : Blo 401768 2277985 := bstep (se 2 (by rfl) ⟨854244, by rfl⟩ : syracuseStep 2277985 = 1708489) B1708489
theorem B1360637 : Blo 401768 1360637 := bstep (se 3 (by rfl) ⟨255119, by rfl⟩ : syracuseStep 1360637 = 510239) B510239
theorem B967535 : Blo 401768 967535 := bstep (se 1 (by rfl) ⟨725651, by rfl⟩ : syracuseStep 967535 = 1451303) B1451303
theorem B8700965 : Blo 401768 8700965 := bstep (se 4 (by rfl) ⟨815715, by rfl⟩ : syracuseStep 8700965 = 1631431) B1631431
theorem B607295 : Blo 401768 607295 := bstep (se 1 (by rfl) ⟨455471, by rfl⟩ : syracuseStep 607295 = 910943) B910943
theorem B607337 : Blo 401768 607337 := bstep (se 2 (by rfl) ⟨227751, by rfl⟩ : syracuseStep 607337 = 455503) B455503
theorem B607439 : Blo 401768 607439 := bstep (se 1 (by rfl) ⟨455579, by rfl⟩ : syracuseStep 607439 = 911159) B911159
theorem B607643 : Blo 401768 607643 := bstep (se 1 (by rfl) ⟨455732, by rfl⟩ : syracuseStep 607643 = 911465) B911465
theorem B607865 : Blo 401768 607865 := bstep (se 2 (by rfl) ⟨227949, by rfl⟩ : syracuseStep 607865 = 455899) B455899
theorem B3884705 : Blo 401768 3884705 := bstep (se 2 (by rfl) ⟨1456764, by rfl⟩ : syracuseStep 3884705 = 2913529) B2913529
theorem B607967 : Blo 401768 607967 := bstep (se 1 (by rfl) ⟨455975, by rfl⟩ : syracuseStep 607967 = 911951) B911951
theorem B19384109 : Blo 401768 19384109 := bstep (se 3 (by rfl) ⟨3634520, by rfl⟩ : syracuseStep 19384109 = 7269041) B7269041
theorem B608063 : Blo 401768 608063 := bstep (se 1 (by rfl) ⟨456047, by rfl⟩ : syracuseStep 608063 = 912095) B912095
theorem B608231 : Blo 401768 608231 := bstep (se 1 (by rfl) ⟨456173, by rfl⟩ : syracuseStep 608231 = 912347) B912347
theorem B608249 : Blo 401768 608249 := bstep (se 2 (by rfl) ⟨228093, by rfl⟩ : syracuseStep 608249 = 456187) B456187
theorem B608351 : Blo 401768 608351 := bstep (se 1 (by rfl) ⟨456263, by rfl⟩ : syracuseStep 608351 = 912527) B912527
theorem B608411 : Blo 401768 608411 := bstep (se 1 (by rfl) ⟨456308, by rfl⟩ : syracuseStep 608411 = 912617) B912617
theorem B608447 : Blo 401768 608447 := bstep (se 1 (by rfl) ⟨456335, by rfl⟩ : syracuseStep 608447 = 912671) B912671
theorem B608489 : Blo 401768 608489 := bstep (se 2 (by rfl) ⟨228183, by rfl⟩ : syracuseStep 608489 = 456367) B456367
theorem B575785 : Blo 401768 575785 := bstep (se 2 (by rfl) ⟨215919, by rfl⟩ : syracuseStep 575785 = 431839) B431839
theorem B1362743 : Blo 401768 1362743 := bstep (se 1 (by rfl) ⟨1022057, by rfl⟩ : syracuseStep 1362743 = 2044115) B2044115
theorem B1297387 : Blo 401768 1297387 := bstep (se 1 (by rfl) ⟨973040, by rfl⟩ : syracuseStep 1297387 = 1946081) B1946081
theorem B1297529 : Blo 401768 1297529 := bstep (se 2 (by rfl) ⟨486573, by rfl⟩ : syracuseStep 1297529 = 973147) B973147
theorem B1527119 : Blo 401768 1527119 := bstep (se 1 (by rfl) ⟨1145339, by rfl⟩ : syracuseStep 1527119 = 2290679) B2290679
theorem B905183 : Blo 401768 905183 := bstep (se 1 (by rfl) ⟨678887, by rfl⟩ : syracuseStep 905183 = 1357775) B1357775
theorem B13127741 : Blo 401768 13127741 := bstep (se 3 (by rfl) ⟨2461451, by rfl⟩ : syracuseStep 13127741 = 4922903) B4922903
theorem B1298555 : Blo 401768 1298555 := bstep (se 1 (by rfl) ⟨973916, by rfl⟩ : syracuseStep 1298555 = 1947833) B1947833
theorem B2806343 : Blo 401768 2806343 := bstep (se 1 (by rfl) ⟨2104757, by rfl⟩ : syracuseStep 2806343 = 4209515) B4209515
theorem B905831 : Blo 401768 905831 := bstep (se 1 (by rfl) ⟨679373, by rfl⟩ : syracuseStep 905831 = 1358747) B1358747
theorem B1528895 : Blo 401768 1528895 := bstep (se 1 (by rfl) ⟨1146671, by rfl⟩ : syracuseStep 1528895 = 2293343) B2293343
theorem B1365065 : Blo 401768 1365065 := bstep (se 2 (by rfl) ⟨511899, by rfl⟩ : syracuseStep 1365065 = 1023799) B1023799
theorem B644203 : Blo 401768 644203 := bstep (se 1 (by rfl) ⟨483152, by rfl⟩ : syracuseStep 644203 = 966305) B966305
theorem B2938031 : Blo 401768 2938031 := bstep (se 1 (by rfl) ⟨2203523, by rfl⟩ : syracuseStep 2938031 = 4407047) B4407047
theorem B906515 : Blo 401768 906515 := bstep (se 1 (by rfl) ⟨679886, by rfl⟩ : syracuseStep 906515 = 1359773) B1359773
theorem B906587 : Blo 401768 906587 := bstep (se 1 (by rfl) ⟨679940, by rfl⟩ : syracuseStep 906587 = 1359881) B1359881
theorem B907145 : Blo 401768 907145 := bstep (se 2 (by rfl) ⟨340179, by rfl⟩ : syracuseStep 907145 = 680359) B680359
theorem B1169383 : Blo 401768 1169383 := bstep (se 1 (by rfl) ⟨877037, by rfl⟩ : syracuseStep 1169383 = 1754075) B1754075
theorem B907361 : Blo 401768 907361 := bstep (se 2 (by rfl) ⟨340260, by rfl⟩ : syracuseStep 907361 = 680521) B680521
theorem B1366685 : Blo 401768 1366685 := bstep (se 3 (by rfl) ⟨256253, by rfl⟩ : syracuseStep 1366685 = 512507) B512507
theorem B1367009 : Blo 401768 1367009 := bstep (se 2 (by rfl) ⟨512628, by rfl⟩ : syracuseStep 1367009 = 1025257) B1025257
theorem B3071033 : Blo 401768 3071033 := bstep (se 2 (by rfl) ⟨1151637, by rfl⟩ : syracuseStep 3071033 = 2303275) B2303275
theorem B1367225 : Blo 401768 1367225 := bstep (se 2 (by rfl) ⟨512709, by rfl⟩ : syracuseStep 1367225 = 1025419) B1025419
theorem B1629551 : Blo 401768 1629551 := bstep (se 1 (by rfl) ⟨1222163, by rfl⟩ : syracuseStep 1629551 = 2444327) B2444327
theorem B679279 : Blo 401768 679279 := bstep (se 1 (by rfl) ⟨509459, by rfl⟩ : syracuseStep 679279 = 1018919) B1018919
theorem B908711 : Blo 401768 908711 := bstep (se 1 (by rfl) ⟨681533, by rfl⟩ : syracuseStep 908711 = 1363067) B1363067
theorem B646631 : Blo 401768 646631 := bstep (se 1 (by rfl) ⟨484973, by rfl⟩ : syracuseStep 646631 = 969947) B969947
theorem B908891 : Blo 401768 908891 := bstep (se 1 (by rfl) ⟨681668, by rfl⟩ : syracuseStep 908891 = 1363337) B1363337
theorem B679657 : Blo 401768 679657 := bstep (se 2 (by rfl) ⟨254871, by rfl⟩ : syracuseStep 679657 = 509743) B509743
theorem B2580295 : Blo 401768 2580295 := bstep (se 1 (by rfl) ⟨1935221, by rfl⟩ : syracuseStep 2580295 = 3870443) B3870443
theorem B909179 : Blo 401768 909179 := bstep (se 1 (by rfl) ⟨681884, by rfl⟩ : syracuseStep 909179 = 1363769) B1363769
theorem B6545447 : Blo 401768 6545447 := bstep (se 1 (by rfl) ⟨4909085, by rfl⟩ : syracuseStep 6545447 = 9818171) B9818171
theorem B680123 : Blo 401768 680123 := bstep (se 1 (by rfl) ⟨510092, by rfl⟩ : syracuseStep 680123 = 1020185) B1020185
theorem B909665 : Blo 401768 909665 := bstep (se 2 (by rfl) ⟨341124, by rfl⟩ : syracuseStep 909665 = 682249) B682249
theorem B909755 : Blo 401768 909755 := bstep (se 1 (by rfl) ⟨682316, by rfl⟩ : syracuseStep 909755 = 1364633) B1364633
theorem B1729097 : Blo 401768 1729097 := bstep (se 2 (by rfl) ⟨648411, by rfl⟩ : syracuseStep 1729097 = 1296823) B1296823
theorem B1368683 : Blo 401768 1368683 := bstep (se 1 (by rfl) ⟨1026512, by rfl⟩ : syracuseStep 1368683 = 2053025) B2053025
theorem B1729133 : Blo 401768 1729133 := bstep (se 3 (by rfl) ⟨324212, by rfl⟩ : syracuseStep 1729133 = 648425) B648425
theorem B680683 : Blo 401768 680683 := bstep (se 1 (by rfl) ⟨510512, by rfl⟩ : syracuseStep 680683 = 1021025) B1021025
theorem B2188043 : Blo 401768 2188043 := bstep (se 1 (by rfl) ⟨1641032, by rfl⟩ : syracuseStep 2188043 = 3282065) B3282065
theorem B1532783 : Blo 401768 1532783 := bstep (se 1 (by rfl) ⟨1149587, by rfl⟩ : syracuseStep 1532783 = 2299175) B2299175
theorem B648047 : Blo 401768 648047 := bstep (se 1 (by rfl) ⟨486035, by rfl⟩ : syracuseStep 648047 = 972071) B972071
theorem B3072977 : Blo 401768 3072977 := bstep (se 2 (by rfl) ⟨1152366, by rfl⟩ : syracuseStep 3072977 = 2304733) B2304733
theorem B3892313 : Blo 401768 3892313 := bstep (se 2 (by rfl) ⟨1459617, by rfl⟩ : syracuseStep 3892313 = 2919235) B2919235
theorem B1369277 : Blo 401768 1369277 := bstep (se 3 (by rfl) ⟨256739, by rfl⟩ : syracuseStep 1369277 = 513479) B513479
theorem B910763 : Blo 401768 910763 := bstep (se 1 (by rfl) ⟨683072, by rfl⟩ : syracuseStep 910763 = 1366145) B1366145
theorem B2483693 : Blo 401768 2483693 := bstep (se 3 (by rfl) ⟨465692, by rfl⟩ : syracuseStep 2483693 = 931385) B931385
theorem B452263 : Blo 401768 452263 := bstep (se 1 (by rfl) ⟨339197, by rfl⟩ : syracuseStep 452263 = 678395) B678395
theorem B911015 : Blo 401768 911015 := bstep (se 1 (by rfl) ⟨683261, by rfl⟩ : syracuseStep 911015 = 1366523) B1366523
theorem B681655 : Blo 401768 681655 := bstep (se 1 (by rfl) ⟨511241, by rfl⟩ : syracuseStep 681655 = 1022483) B1022483
theorem B452551 : Blo 401768 452551 := bstep (se 1 (by rfl) ⟨339413, by rfl⟩ : syracuseStep 452551 = 678827) B678827
theorem B911303 : Blo 401768 911303 := bstep (se 1 (by rfl) ⟨683477, by rfl⟩ : syracuseStep 911303 = 1366955) B1366955
theorem B681959 : Blo 401768 681959 := bstep (se 1 (by rfl) ⟨511469, by rfl⟩ : syracuseStep 681959 = 1022939) B1022939
theorem B616423 : Blo 401768 616423 := bstep (se 1 (by rfl) ⟨462317, by rfl⟩ : syracuseStep 616423 = 924635) B924635
theorem B682175 : Blo 401768 682175 := bstep (se 1 (by rfl) ⟨511631, by rfl⟩ : syracuseStep 682175 = 1023263) B1023263
theorem B911609 : Blo 401768 911609 := bstep (se 2 (by rfl) ⟨341853, by rfl⟩ : syracuseStep 911609 = 683707) B683707
theorem B452911 : Blo 401768 452911 := bstep (se 1 (by rfl) ⟨339683, by rfl⟩ : syracuseStep 452911 = 679367) B679367
theorem B911663 : Blo 401768 911663 := bstep (se 1 (by rfl) ⟨683747, by rfl⟩ : syracuseStep 911663 = 1367495) B1367495
theorem B911879 : Blo 401768 911879 := bstep (se 1 (by rfl) ⟨683909, by rfl⟩ : syracuseStep 911879 = 1367819) B1367819
theorem B912059 : Blo 401768 912059 := bstep (se 1 (by rfl) ⟨684044, by rfl⟩ : syracuseStep 912059 = 1368089) B1368089
theorem B682843 : Blo 401768 682843 := bstep (se 1 (by rfl) ⟨512132, by rfl⟩ : syracuseStep 682843 = 1024265) B1024265
theorem B453703 : Blo 401768 453703 := bstep (se 1 (by rfl) ⟨340277, by rfl⟩ : syracuseStep 453703 = 680555) B680555
theorem B15756743 : Blo 401768 15756743 := bstep (se 1 (by rfl) ⟨11817557, by rfl⟩ : syracuseStep 15756743 = 23635115) B23635115
theorem B912887 : Blo 401768 912887 := bstep (se 1 (by rfl) ⟨684665, by rfl⟩ : syracuseStep 912887 = 1369331) B1369331
theorem B912959 : Blo 401768 912959 := bstep (se 1 (by rfl) ⟨684719, by rfl⟩ : syracuseStep 912959 = 1369439) B1369439
theorem B683815 : Blo 401768 683815 := bstep (se 1 (by rfl) ⟨512861, by rfl⟩ : syracuseStep 683815 = 1025723) B1025723
theorem B22146929 : Blo 401768 22146929 := bstep (se 2 (by rfl) ⟨8305098, by rfl⟩ : syracuseStep 22146929 = 16610197) B16610197
theorem B84275315 : Blo 401768 84275315 := bstep (se 1 (by rfl) ⟨63206486, by rfl⟩ : syracuseStep 84275315 = 126412973) B126412973
theorem B3436667 : Blo 401768 3436667 := bstep (se 1 (by rfl) ⟨2577500, by rfl⟩ : syracuseStep 3436667 = 5155001) B5155001
theorem B4583951 : Blo 401768 4583951 := bstep (se 1 (by rfl) ⟨3437963, by rfl⟩ : syracuseStep 4583951 = 6875927) B6875927
theorem B2586113 : Blo 401768 2586113 := bstep (se 2 (by rfl) ⟨969792, by rfl⟩ : syracuseStep 2586113 = 1939585) B1939585
theorem B1144975 : Blo 401768 1144975 := bstep (se 1 (by rfl) ⟨858731, by rfl⟩ : syracuseStep 1144975 = 1717463) B1717463
theorem B1538311 : Blo 401768 1538311 := bstep (se 1 (by rfl) ⟨1153733, by rfl⟩ : syracuseStep 1538311 = 2307467) B2307467
theorem B1145465 : Blo 401768 1145465 := bstep (se 2 (by rfl) ⟨429549, by rfl⟩ : syracuseStep 1145465 = 859099) B859099
theorem B3078809 : Blo 401768 3078809 := bstep (se 2 (by rfl) ⟨1154553, by rfl⟩ : syracuseStep 3078809 = 2309107) B2309107
theorem B1538783 : Blo 401768 1538783 := bstep (se 1 (by rfl) ⟨1154087, by rfl⟩ : syracuseStep 1538783 = 2308175) B2308175
theorem B1145897 : Blo 401768 1145897 := bstep (se 2 (by rfl) ⟨429711, by rfl⟩ : syracuseStep 1145897 = 859423) B859423
theorem B818441 : Blo 401768 818441 := bstep (se 2 (by rfl) ⟨306915, by rfl⟩ : syracuseStep 818441 = 613831) B613831
theorem B4586867 : Blo 401768 4586867 := bstep (se 1 (by rfl) ⟨3440150, by rfl⟩ : syracuseStep 4586867 = 6880301) B6880301
theorem B1146251 : Blo 401768 1146251 := bstep (se 1 (by rfl) ⟨859688, by rfl⟩ : syracuseStep 1146251 = 1719377) B1719377
theorem B2915777 : Blo 401768 2915777 := bstep (se 2 (by rfl) ⟨1093416, by rfl⟩ : syracuseStep 2915777 = 2186833) B2186833
theorem B1048391 : Blo 401768 1048391 := bstep (se 1 (by rfl) ⟨786293, by rfl⟩ : syracuseStep 1048391 = 1572587) B1572587
theorem B2294345 : Blo 401768 2294345 := bstep (se 2 (by rfl) ⟨860379, by rfl⟩ : syracuseStep 2294345 = 1720759) B1720759
theorem B5800643 : Blo 401768 5800643 := bstep (se 1 (by rfl) ⟨4350482, by rfl⟩ : syracuseStep 5800643 = 8700965) B8700965
theorem B2589803 : Blo 401768 2589803 := bstep (se 1 (by rfl) ⟨1942352, by rfl⟩ : syracuseStep 2589803 = 3884705) B3884705
theorem B1018079 : Blo 401768 1018079 := bstep (se 1 (by rfl) ⟨763559, by rfl⟩ : syracuseStep 1018079 = 1527119) B1527119
theorem B1640843 : Blo 401768 1640843 := bstep (se 1 (by rfl) ⟨1230632, by rfl⟩ : syracuseStep 1640843 = 2461265) B2461265
theorem B2755073 : Blo 401768 2755073 := bstep (se 2 (by rfl) ⟨1033152, by rfl⟩ : syracuseStep 2755073 = 2066305) B2066305
theorem B821897 : Blo 401768 821897 := bstep (se 2 (by rfl) ⟨308211, by rfl⟩ : syracuseStep 821897 = 616423) B616423
theorem B8751827 : Blo 401768 8751827 := bstep (se 1 (by rfl) ⟨6563870, by rfl⟩ : syracuseStep 8751827 = 13127741) B13127741
theorem B1870895 : Blo 401768 1870895 := bstep (se 1 (by rfl) ⟨1403171, by rfl⟩ : syracuseStep 1870895 = 2806343) B2806343
theorem B920639 : Blo 401768 920639 := bstep (se 1 (by rfl) ⟨690479, by rfl⟩ : syracuseStep 920639 = 1380959) B1380959
theorem B6884675 : Blo 401768 6884675 := bstep (se 1 (by rfl) ⟨5163506, by rfl⟩ : syracuseStep 6884675 = 10327013) B10327013
theorem B1019263 : Blo 401768 1019263 := bstep (se 1 (by rfl) ⟨764447, by rfl⟩ : syracuseStep 1019263 = 1528895) B1528895
theorem B2101115 : Blo 401768 2101115 := bstep (se 1 (by rfl) ⟨1575836, by rfl⟩ : syracuseStep 2101115 = 3151673) B3151673
theorem B1675453 : Blo 401768 1675453 := bstep (se 3 (by rfl) ⟨314147, by rfl⟩ : syracuseStep 1675453 = 628295) B628295
theorem B6295805 : Blo 401768 6295805 := bstep (se 3 (by rfl) ⟨1180463, by rfl⟩ : syracuseStep 6295805 = 2360927) B2360927
theorem B1151273 : Blo 401768 1151273 := bstep (se 2 (by rfl) ⟨431727, by rfl⟩ : syracuseStep 1151273 = 863455) B863455
theorem B8261939 : Blo 401768 8261939 := bstep (se 1 (by rfl) ⟨6196454, by rfl⟩ : syracuseStep 8261939 = 12392909) B12392909
theorem B1839671 : Blo 401768 1839671 := bstep (se 1 (by rfl) ⟨1379753, by rfl⟩ : syracuseStep 1839671 = 2759507) B2759507
theorem B2298719 : Blo 401768 2298719 := bstep (se 1 (by rfl) ⟨1724039, by rfl⟩ : syracuseStep 2298719 = 3448079) B3448079
theorem B1086367 : Blo 401768 1086367 := bstep (se 1 (by rfl) ⟨814775, by rfl⟩ : syracuseStep 1086367 = 1629551) B1629551
theorem B431087 : Blo 401768 431087 := bstep (se 1 (by rfl) ⟨323315, by rfl⟩ : syracuseStep 431087 = 646631) B646631
theorem B3937319 : Blo 401768 3937319 := bstep (se 1 (by rfl) ⟨2952989, by rfl⟩ : syracuseStep 3937319 = 5905979) B5905979
theorem B4363631 : Blo 401768 4363631 := bstep (se 1 (by rfl) ⟨3272723, by rfl⟩ : syracuseStep 4363631 = 6545447) B6545447
theorem B1152731 : Blo 401768 1152731 := bstep (se 1 (by rfl) ⟨864548, by rfl⟩ : syracuseStep 1152731 = 1729097) B1729097
theorem B1152755 : Blo 401768 1152755 := bstep (se 1 (by rfl) ⟨864566, by rfl⟩ : syracuseStep 1152755 = 1729133) B1729133
theorem B1021855 : Blo 401768 1021855 := bstep (se 1 (by rfl) ⟨766391, by rfl⟩ : syracuseStep 1021855 = 1532783) B1532783
theorem B858937 : Blo 401768 858937 := bstep (se 2 (by rfl) ⟨322101, by rfl⟩ : syracuseStep 858937 = 644203) B644203
theorem B1022777 : Blo 401768 1022777 := bstep (se 2 (by rfl) ⟨383541, by rfl⟩ : syracuseStep 1022777 = 767083) B767083
theorem B727879 : Blo 401768 727879 := bstep (se 1 (by rfl) ⟨545909, by rfl⟩ : syracuseStep 727879 = 1091819) B1091819
theorem B4791619 : Blo 401768 4791619 := bstep (se 1 (by rfl) ⟨3593714, by rfl⟩ : syracuseStep 4791619 = 7187429) B7187429
theorem B3055967 : Blo 401768 3055967 := bstep (se 1 (by rfl) ⟨2291975, by rfl⟩ : syracuseStep 3055967 = 4583951) B4583951
theorem B401947 : Blo 401768 401947 := bstep (se 1 (by rfl) ⟨301460, by rfl⟩ : syracuseStep 401947 = 602921) B602921
theorem B401951 : Blo 401768 401951 := bstep (se 1 (by rfl) ⟨301463, by rfl⟩ : syracuseStep 401951 = 602927) B602927
theorem B402031 : Blo 401768 402031 := bstep (se 1 (by rfl) ⟨301523, by rfl⟩ : syracuseStep 402031 = 603047) B603047
theorem B402087 : Blo 401768 402087 := bstep (se 1 (by rfl) ⟨301565, by rfl⟩ : syracuseStep 402087 = 603131) B603131
theorem B402127 : Blo 401768 402127 := bstep (se 1 (by rfl) ⟨301595, by rfl⟩ : syracuseStep 402127 = 603191) B603191
theorem B1843975 : Blo 401768 1843975 := bstep (se 1 (by rfl) ⟨1382981, by rfl⟩ : syracuseStep 1843975 = 2765963) B2765963
theorem B402207 : Blo 401768 402207 := bstep (se 1 (by rfl) ⟨301655, by rfl⟩ : syracuseStep 402207 = 603311) B603311
theorem B730091 : Blo 401768 730091 := bstep (se 1 (by rfl) ⟨547568, by rfl⟩ : syracuseStep 730091 = 1095137) B1095137
theorem B402479 : Blo 401768 402479 := bstep (se 1 (by rfl) ⟨301859, by rfl⟩ : syracuseStep 402479 = 603719) B603719
theorem B4432985 : Blo 401768 4432985 := bstep (se 2 (by rfl) ⟨1662369, by rfl⟩ : syracuseStep 4432985 = 3324739) B3324739
theorem B402543 : Blo 401768 402543 := bstep (se 1 (by rfl) ⟨301907, by rfl⟩ : syracuseStep 402543 = 603815) B603815
theorem B1287289 : Blo 401768 1287289 := bstep (se 2 (by rfl) ⟨482733, by rfl⟩ : syracuseStep 1287289 = 965467) B965467
theorem B402599 : Blo 401768 402599 := bstep (se 1 (by rfl) ⟨301949, by rfl⟩ : syracuseStep 402599 = 603899) B603899
theorem B402623 : Blo 401768 402623 := bstep (se 1 (by rfl) ⟨301967, by rfl⟩ : syracuseStep 402623 = 603935) B603935
theorem B402655 : Blo 401768 402655 := bstep (se 1 (by rfl) ⟨301991, by rfl⟩ : syracuseStep 402655 = 603983) B603983
theorem B402735 : Blo 401768 402735 := bstep (se 1 (by rfl) ⟨302051, by rfl⟩ : syracuseStep 402735 = 604103) B604103
theorem B402971 : Blo 401768 402971 := bstep (se 1 (by rfl) ⟨302228, by rfl⟩ : syracuseStep 402971 = 604457) B604457
theorem B402975 : Blo 401768 402975 := bstep (se 1 (by rfl) ⟨302231, by rfl⟩ : syracuseStep 402975 = 604463) B604463
theorem B403135 : Blo 401768 403135 := bstep (se 1 (by rfl) ⟨302351, by rfl⟩ : syracuseStep 403135 = 604703) B604703
theorem B763643 : Blo 401768 763643 := bstep (se 1 (by rfl) ⟨572732, by rfl⟩ : syracuseStep 763643 = 1145465) B1145465
theorem B1025855 : Blo 401768 1025855 := bstep (se 1 (by rfl) ⟨769391, by rfl⟩ : syracuseStep 1025855 = 1538783) B1538783
theorem B731035 : Blo 401768 731035 := bstep (se 1 (by rfl) ⟨548276, by rfl⟩ : syracuseStep 731035 = 1096553) B1096553
theorem B403391 : Blo 401768 403391 := bstep (se 1 (by rfl) ⟨302543, by rfl⟩ : syracuseStep 403391 = 605087) B605087
theorem B403423 : Blo 401768 403423 := bstep (se 1 (by rfl) ⟨302567, by rfl⟩ : syracuseStep 403423 = 605135) B605135
theorem B763931 : Blo 401768 763931 := bstep (se 1 (by rfl) ⟨572948, by rfl⟩ : syracuseStep 763931 = 1145897) B1145897
theorem B403483 : Blo 401768 403483 := bstep (se 1 (by rfl) ⟨302612, by rfl⟩ : syracuseStep 403483 = 605225) B605225
theorem B403487 : Blo 401768 403487 := bstep (se 1 (by rfl) ⟨302615, by rfl⟩ : syracuseStep 403487 = 605231) B605231
theorem B403503 : Blo 401768 403503 := bstep (se 1 (by rfl) ⟨302627, by rfl⟩ : syracuseStep 403503 = 605255) B605255
theorem B20949137 : Blo 401768 20949137 := bstep (se 2 (by rfl) ⟨7855926, by rfl⟩ : syracuseStep 20949137 = 15711853) B15711853
theorem B403679 : Blo 401768 403679 := bstep (se 1 (by rfl) ⟨302759, by rfl⟩ : syracuseStep 403679 = 605519) B605519
theorem B3057911 : Blo 401768 3057911 := bstep (se 1 (by rfl) ⟨2293433, by rfl⟩ : syracuseStep 3057911 = 4586867) B4586867
theorem B764167 : Blo 401768 764167 := bstep (se 1 (by rfl) ⟨573125, by rfl⟩ : syracuseStep 764167 = 1146251) B1146251
theorem B403739 : Blo 401768 403739 := bstep (se 1 (by rfl) ⟨302804, by rfl⟩ : syracuseStep 403739 = 605609) B605609
theorem B1943851 : Blo 401768 1943851 := bstep (se 1 (by rfl) ⟨1457888, by rfl⟩ : syracuseStep 1943851 = 2915777) B2915777
theorem B403839 : Blo 401768 403839 := bstep (se 1 (by rfl) ⟨302879, by rfl⟩ : syracuseStep 403839 = 605759) B605759
theorem B1026553 : Blo 401768 1026553 := bstep (se 2 (by rfl) ⟨384957, by rfl⟩ : syracuseStep 1026553 = 769915) B769915
theorem B698927 : Blo 401768 698927 := bstep (se 1 (by rfl) ⟨524195, by rfl⟩ : syracuseStep 698927 = 1048391) B1048391
theorem B404015 : Blo 401768 404015 := bstep (se 1 (by rfl) ⟨303011, by rfl⟩ : syracuseStep 404015 = 606023) B606023
theorem B404071 : Blo 401768 404071 := bstep (se 1 (by rfl) ⟨303053, by rfl⟩ : syracuseStep 404071 = 606107) B606107
theorem B15510203 : Blo 401768 15510203 := bstep (se 1 (by rfl) ⟨11632652, by rfl⟩ : syracuseStep 15510203 = 23265305) B23265305
theorem B19737539 : Blo 401768 19737539 := bstep (se 1 (by rfl) ⟨14803154, by rfl⟩ : syracuseStep 19737539 = 29606309) B29606309
theorem B404447 : Blo 401768 404447 := bstep (se 1 (by rfl) ⟨303335, by rfl⟩ : syracuseStep 404447 = 606671) B606671
theorem B1027039 : Blo 401768 1027039 := bstep (se 1 (by rfl) ⟨770279, by rfl⟩ : syracuseStep 1027039 = 1540559) B1540559
theorem B404475 : Blo 401768 404475 := bstep (se 1 (by rfl) ⟨303356, by rfl⟩ : syracuseStep 404475 = 606713) B606713
theorem B404543 : Blo 401768 404543 := bstep (se 1 (by rfl) ⟨303407, by rfl⟩ : syracuseStep 404543 = 606815) B606815
theorem B3452179 : Blo 401768 3452179 := bstep (se 1 (by rfl) ⟨2589134, by rfl⟩ : syracuseStep 3452179 = 5178269) B5178269
theorem B1944911 : Blo 401768 1944911 := bstep (se 1 (by rfl) ⟨1458683, by rfl⟩ : syracuseStep 1944911 = 2917367) B2917367
theorem B404863 : Blo 401768 404863 := bstep (se 1 (by rfl) ⟨303647, by rfl⟩ : syracuseStep 404863 = 607295) B607295
theorem B404891 : Blo 401768 404891 := bstep (se 1 (by rfl) ⟨303668, by rfl⟩ : syracuseStep 404891 = 607337) B607337
theorem B404959 : Blo 401768 404959 := bstep (se 1 (by rfl) ⟨303719, by rfl⟩ : syracuseStep 404959 = 607439) B607439
theorem B405095 : Blo 401768 405095 := bstep (se 1 (by rfl) ⟨303821, by rfl⟩ : syracuseStep 405095 = 607643) B607643
theorem B405243 : Blo 401768 405243 := bstep (se 1 (by rfl) ⟨303932, by rfl⟩ : syracuseStep 405243 = 607865) B607865
theorem B405311 : Blo 401768 405311 := bstep (se 1 (by rfl) ⟨303983, by rfl⟩ : syracuseStep 405311 = 607967) B607967
theorem B12922739 : Blo 401768 12922739 := bstep (se 1 (by rfl) ⟨9692054, by rfl⟩ : syracuseStep 12922739 = 19384109) B19384109
theorem B405375 : Blo 401768 405375 := bstep (se 1 (by rfl) ⟨304031, by rfl⟩ : syracuseStep 405375 = 608063) B608063
theorem B405487 : Blo 401768 405487 := bstep (se 1 (by rfl) ⟨304115, by rfl⟩ : syracuseStep 405487 = 608231) B608231
theorem B405499 : Blo 401768 405499 := bstep (se 1 (by rfl) ⟨304124, by rfl⟩ : syracuseStep 405499 = 608249) B608249
theorem B405567 : Blo 401768 405567 := bstep (se 1 (by rfl) ⟨304175, by rfl⟩ : syracuseStep 405567 = 608351) B608351
theorem B405607 : Blo 401768 405607 := bstep (se 1 (by rfl) ⟨304205, by rfl⟩ : syracuseStep 405607 = 608411) B608411
theorem B405631 : Blo 401768 405631 := bstep (se 1 (by rfl) ⟨304223, by rfl⟩ : syracuseStep 405631 = 608447) B608447
theorem B405659 : Blo 401768 405659 := bstep (se 1 (by rfl) ⟨304244, by rfl⟩ : syracuseStep 405659 = 608489) B608489
theorem B766415 : Blo 401768 766415 := bstep (se 1 (by rfl) ⟨574811, by rfl⟩ : syracuseStep 766415 = 1149623) B1149623
theorem B865019 : Blo 401768 865019 := bstep (se 1 (by rfl) ⟨648764, by rfl⟩ : syracuseStep 865019 = 1297529) B1297529
theorem B603017 : Blo 401768 603017 := bstep (se 2 (by rfl) ⟨226131, by rfl⟩ : syracuseStep 603017 = 452263) B452263
theorem B1848425 : Blo 401768 1848425 := bstep (se 2 (by rfl) ⟨693159, by rfl⟩ : syracuseStep 1848425 = 1386319) B1386319
theorem B4371677 : Blo 401768 4371677 := bstep (se 3 (by rfl) ⟨819689, by rfl⟩ : syracuseStep 4371677 = 1639379) B1639379
theorem B767227 : Blo 401768 767227 := bstep (se 1 (by rfl) ⟨575420, by rfl⟩ : syracuseStep 767227 = 1150841) B1150841
theorem B603401 : Blo 401768 603401 := bstep (se 2 (by rfl) ⟨226275, by rfl⟩ : syracuseStep 603401 = 452551) B452551
theorem B603455 : Blo 401768 603455 := bstep (se 1 (by rfl) ⟨452591, by rfl⟩ : syracuseStep 603455 = 905183) B905183
theorem B865703 : Blo 401768 865703 := bstep (se 1 (by rfl) ⟨649277, by rfl⟩ : syracuseStep 865703 = 1298555) B1298555
theorem B2897441 : Blo 401768 2897441 := bstep (se 2 (by rfl) ⟨1086540, by rfl⟩ : syracuseStep 2897441 = 2173081) B2173081
theorem B767713 : Blo 401768 767713 := bstep (se 2 (by rfl) ⟨287892, by rfl⟩ : syracuseStep 767713 = 575785) B575785
theorem B603881 : Blo 401768 603881 := bstep (se 2 (by rfl) ⟨226455, by rfl⟩ : syracuseStep 603881 = 452911) B452911
theorem B603887 : Blo 401768 603887 := bstep (se 1 (by rfl) ⟨452915, by rfl⟩ : syracuseStep 603887 = 905831) B905831
theorem B1357559 : Blo 401768 1357559 := bstep (se 1 (by rfl) ⟨1018169, by rfl⟩ : syracuseStep 1357559 = 2036339) B2036339
theorem B12433277 : Blo 401768 12433277 := bstep (se 3 (by rfl) ⟨2331239, by rfl⟩ : syracuseStep 12433277 = 4662479) B4662479
theorem B604343 : Blo 401768 604343 := bstep (se 1 (by rfl) ⟨453257, by rfl⟩ : syracuseStep 604343 = 906515) B906515
theorem B604391 : Blo 401768 604391 := bstep (se 1 (by rfl) ⟨453293, by rfl⟩ : syracuseStep 604391 = 906587) B906587
theorem B604763 : Blo 401768 604763 := bstep (se 1 (by rfl) ⟨453572, by rfl⟩ : syracuseStep 604763 = 907145) B907145
theorem B604907 : Blo 401768 604907 := bstep (se 1 (by rfl) ⟨453680, by rfl⟩ : syracuseStep 604907 = 907361) B907361
theorem B604937 : Blo 401768 604937 := bstep (se 2 (by rfl) ⟨226851, by rfl⟩ : syracuseStep 604937 = 453703) B453703
theorem B1358639 : Blo 401768 1358639 := bstep (se 1 (by rfl) ⟨1018979, by rfl⟩ : syracuseStep 1358639 = 2037959) B2037959
theorem B769247 : Blo 401768 769247 := bstep (se 1 (by rfl) ⟨576935, by rfl⟩ : syracuseStep 769247 = 1153871) B1153871
theorem B2047355 : Blo 401768 2047355 := bstep (se 1 (by rfl) ⟨1535516, by rfl⟩ : syracuseStep 2047355 = 3071033) B3071033
theorem B1359287 : Blo 401768 1359287 := bstep (se 1 (by rfl) ⟨1019465, by rfl⟩ : syracuseStep 1359287 = 2038931) B2038931
theorem B605807 : Blo 401768 605807 := bstep (se 1 (by rfl) ⟨454355, by rfl⟩ : syracuseStep 605807 = 908711) B908711
theorem B605927 : Blo 401768 605927 := bstep (se 1 (by rfl) ⟨454445, by rfl⟩ : syracuseStep 605927 = 908891) B908891
theorem B606119 : Blo 401768 606119 := bstep (se 1 (by rfl) ⟨454589, by rfl⟩ : syracuseStep 606119 = 909179) B909179
theorem B1359827 : Blo 401768 1359827 := bstep (se 1 (by rfl) ⟨1019870, by rfl⟩ : syracuseStep 1359827 = 2039741) B2039741
theorem B606443 : Blo 401768 606443 := bstep (se 1 (by rfl) ⟨454832, by rfl⟩ : syracuseStep 606443 = 909665) B909665
theorem B606503 : Blo 401768 606503 := bstep (se 1 (by rfl) ⟨454877, by rfl⟩ : syracuseStep 606503 = 909755) B909755
theorem B1458695 : Blo 401768 1458695 := bstep (se 1 (by rfl) ⟨1094021, by rfl⟩ : syracuseStep 1458695 = 2188043) B2188043
theorem B2048651 : Blo 401768 2048651 := bstep (se 1 (by rfl) ⟨1536488, by rfl⟩ : syracuseStep 2048651 = 3072977) B3072977
theorem B607175 : Blo 401768 607175 := bstep (se 1 (by rfl) ⟨455381, by rfl⟩ : syracuseStep 607175 = 910763) B910763
theorem B1655795 : Blo 401768 1655795 := bstep (se 1 (by rfl) ⟨1241846, by rfl⟩ : syracuseStep 1655795 = 2483693) B2483693
theorem B607343 : Blo 401768 607343 := bstep (se 1 (by rfl) ⟨455507, by rfl⟩ : syracuseStep 607343 = 911015) B911015
theorem B607535 : Blo 401768 607535 := bstep (se 1 (by rfl) ⟨455651, by rfl⟩ : syracuseStep 607535 = 911303) B911303
theorem B1361231 : Blo 401768 1361231 := bstep (se 1 (by rfl) ⟨1020923, by rfl⟩ : syracuseStep 1361231 = 2041847) B2041847
theorem B1361339 : Blo 401768 1361339 := bstep (se 1 (by rfl) ⟨1021004, by rfl⟩ : syracuseStep 1361339 = 2042009) B2042009
theorem B607739 : Blo 401768 607739 := bstep (se 1 (by rfl) ⟨455804, by rfl⟩ : syracuseStep 607739 = 911609) B911609
theorem B607775 : Blo 401768 607775 := bstep (se 1 (by rfl) ⟨455831, by rfl⟩ : syracuseStep 607775 = 911663) B911663
theorem B575039 : Blo 401768 575039 := bstep (se 1 (by rfl) ⟨431279, by rfl⟩ : syracuseStep 575039 = 862559) B862559
theorem B607919 : Blo 401768 607919 := bstep (se 1 (by rfl) ⟨455939, by rfl⟩ : syracuseStep 607919 = 911879) B911879
theorem B608039 : Blo 401768 608039 := bstep (se 1 (by rfl) ⟨456029, by rfl⟩ : syracuseStep 608039 = 912059) B912059
theorem B4376393 : Blo 401768 4376393 := bstep (se 2 (by rfl) ⟨1641147, by rfl⟩ : syracuseStep 4376393 = 3282295) B3282295
theorem B1361879 : Blo 401768 1361879 := bstep (se 1 (by rfl) ⟨1021409, by rfl⟩ : syracuseStep 1361879 = 2042819) B2042819
theorem B968735 : Blo 401768 968735 := bstep (se 1 (by rfl) ⟨726551, by rfl⟩ : syracuseStep 968735 = 1453103) B1453103
theorem B6867179 : Blo 401768 6867179 := bstep (se 1 (by rfl) ⟨5150384, by rfl⟩ : syracuseStep 6867179 = 10300769) B10300769
theorem B10504495 : Blo 401768 10504495 := bstep (se 1 (by rfl) ⟨7878371, by rfl⟩ : syracuseStep 10504495 = 15756743) B15756743
theorem B608591 : Blo 401768 608591 := bstep (se 1 (by rfl) ⟨456443, by rfl⟩ : syracuseStep 608591 = 912887) B912887
theorem B608639 : Blo 401768 608639 := bstep (se 1 (by rfl) ⟨456479, by rfl⟩ : syracuseStep 608639 = 912959) B912959
theorem B11684321 : Blo 401768 11684321 := bstep (se 2 (by rfl) ⟨4381620, by rfl⟩ : syracuseStep 11684321 = 8763241) B8763241
theorem B14764619 : Blo 401768 14764619 := bstep (se 1 (by rfl) ⟨11073464, by rfl⟩ : syracuseStep 14764619 = 22146929) B22146929
theorem B1559177 : Blo 401768 1559177 := bstep (se 2 (by rfl) ⟨584691, by rfl⟩ : syracuseStep 1559177 = 1169383) B1169383
theorem B56183543 : Blo 401768 56183543 := bstep (se 1 (by rfl) ⟨42137657, by rfl⟩ : syracuseStep 56183543 = 84275315) B84275315
theorem B969563 : Blo 401768 969563 := bstep (se 1 (by rfl) ⟨727172, by rfl⟩ : syracuseStep 969563 = 1454345) B1454345
theorem B1526633 : Blo 401768 1526633 := bstep (se 2 (by rfl) ⟨572487, by rfl⟩ : syracuseStep 1526633 = 1144975) B1144975
theorem B8702963 : Blo 401768 8702963 := bstep (se 1 (by rfl) ⟨6527222, by rfl⟩ : syracuseStep 8702963 = 13054445) B13054445
theorem B2051081 : Blo 401768 2051081 := bstep (se 2 (by rfl) ⟨769155, by rfl⟩ : syracuseStep 2051081 = 1538311) B1538311
theorem B904247 : Blo 401768 904247 := bstep (se 1 (by rfl) ⟨678185, by rfl⟩ : syracuseStep 904247 = 1356371) B1356371
theorem B511039 : Blo 401768 511039 := bstep (se 1 (by rfl) ⟨383279, by rfl⟩ : syracuseStep 511039 = 766559) B766559
theorem B9817307 : Blo 401768 9817307 := bstep (se 1 (by rfl) ⟨7362980, by rfl⟩ : syracuseStep 9817307 = 14725961) B14725961
theorem B904679 : Blo 401768 904679 := bstep (se 1 (by rfl) ⟨678509, by rfl⟩ : syracuseStep 904679 = 1357019) B1357019
theorem B511591 : Blo 401768 511591 := bstep (se 1 (by rfl) ⟨383693, by rfl⟩ : syracuseStep 511591 = 767387) B767387
theorem B6540907 : Blo 401768 6540907 := bstep (se 1 (by rfl) ⟨4905680, by rfl⟩ : syracuseStep 6540907 = 9811361) B9811361
theorem B1724075 : Blo 401768 1724075 := bstep (se 1 (by rfl) ⟨1293056, by rfl⟩ : syracuseStep 1724075 = 2586113) B2586113
theorem B905255 : Blo 401768 905255 := bstep (se 1 (by rfl) ⟨678941, by rfl⟩ : syracuseStep 905255 = 1357883) B1357883
theorem B905435 : Blo 401768 905435 := bstep (se 1 (by rfl) ⟨679076, by rfl⟩ : syracuseStep 905435 = 1358153) B1358153
theorem B971195 : Blo 401768 971195 := bstep (se 1 (by rfl) ⟨728396, by rfl⟩ : syracuseStep 971195 = 1456793) B1456793
theorem B2052539 : Blo 401768 2052539 := bstep (se 1 (by rfl) ⟨1539404, by rfl⟩ : syracuseStep 2052539 = 3078809) B3078809
theorem B905705 : Blo 401768 905705 := bstep (se 2 (by rfl) ⟨339639, by rfl⟩ : syracuseStep 905705 = 679279) B679279
theorem B643639 : Blo 401768 643639 := bstep (se 1 (by rfl) ⟨482729, by rfl⟩ : syracuseStep 643639 = 965459) B965459
theorem B545627 : Blo 401768 545627 := bstep (se 1 (by rfl) ⟨409220, by rfl⟩ : syracuseStep 545627 = 818441) B818441
theorem B1299311 : Blo 401768 1299311 := bstep (se 1 (by rfl) ⟨974483, by rfl⟩ : syracuseStep 1299311 = 1948967) B1948967
theorem B906209 : Blo 401768 906209 := bstep (se 2 (by rfl) ⟨339828, by rfl⟩ : syracuseStep 906209 = 679657) B679657
theorem B906335 : Blo 401768 906335 := bstep (se 1 (by rfl) ⟨679751, by rfl⟩ : syracuseStep 906335 = 1359503) B1359503
theorem B1660267 : Blo 401768 1660267 := bstep (se 1 (by rfl) ⟨1245200, by rfl⟩ : syracuseStep 1660267 = 2490401) B2490401
theorem B2774695 : Blo 401768 2774695 := bstep (se 1 (by rfl) ⟨2081021, by rfl⟩ : syracuseStep 2774695 = 4162043) B4162043
theorem B2053835 : Blo 401768 2053835 := bstep (se 1 (by rfl) ⟨1540376, by rfl⟩ : syracuseStep 2053835 = 3080753) B3080753
theorem B907091 : Blo 401768 907091 := bstep (se 1 (by rfl) ⟨680318, by rfl⟩ : syracuseStep 907091 = 1360637) B1360637
theorem B645023 : Blo 401768 645023 := bstep (se 1 (by rfl) ⟨483767, by rfl⟩ : syracuseStep 645023 = 967535) B967535
theorem B1726433 : Blo 401768 1726433 := bstep (se 2 (by rfl) ⟨647412, by rfl⟩ : syracuseStep 1726433 = 1294825) B1294825
theorem B3037313 : Blo 401768 3037313 := bstep (se 2 (by rfl) ⟨1138992, by rfl⟩ : syracuseStep 3037313 = 2277985) B2277985
theorem B907577 : Blo 401768 907577 := bstep (se 2 (by rfl) ⟨340341, by rfl⟩ : syracuseStep 907577 = 680683) B680683
theorem B102816289 : Blo 401768 102816289 := bstep (se 2 (by rfl) ⟨38556108, by rfl⟩ : syracuseStep 102816289 = 77112217) B77112217
theorem B1530521 : Blo 401768 1530521 := bstep (se 2 (by rfl) ⟨573945, by rfl⟩ : syracuseStep 1530521 = 1147891) B1147891
theorem B908495 : Blo 401768 908495 := bstep (se 1 (by rfl) ⟨681371, by rfl⟩ : syracuseStep 908495 = 1362743) B1362743
theorem B1629521 : Blo 401768 1629521 := bstep (se 2 (by rfl) ⟨611070, by rfl⟩ : syracuseStep 1629521 = 1222141) B1222141
theorem B1727851 : Blo 401768 1727851 := bstep (se 1 (by rfl) ⟨1295888, by rfl⟩ : syracuseStep 1727851 = 2591777) B2591777
theorem B908873 : Blo 401768 908873 := bstep (se 2 (by rfl) ⟨340827, by rfl⟩ : syracuseStep 908873 = 681655) B681655
theorem B1728125 : Blo 401768 1728125 := bstep (se 3 (by rfl) ⟨324023, by rfl⟩ : syracuseStep 1728125 = 648047) B648047
theorem B3890855 : Blo 401768 3890855 := bstep (se 1 (by rfl) ⟨2918141, by rfl⟩ : syracuseStep 3890855 = 5836283) B5836283
theorem B679711 : Blo 401768 679711 := bstep (se 1 (by rfl) ⟨509783, by rfl⟩ : syracuseStep 679711 = 1019567) B1019567
theorem B252731339 : Blo 401768 252731339 := bstep (se 1 (by rfl) ⟨189548504, by rfl⟩ : syracuseStep 252731339 = 379097009) B379097009
theorem B679927 : Blo 401768 679927 := bstep (se 1 (by rfl) ⟨509945, by rfl⟩ : syracuseStep 679927 = 1019891) B1019891
theorem B680143 : Blo 401768 680143 := bstep (se 1 (by rfl) ⟨510107, by rfl⟩ : syracuseStep 680143 = 1020215) B1020215
theorem B10379501 : Blo 401768 10379501 := bstep (se 3 (by rfl) ⟨1946156, by rfl⟩ : syracuseStep 10379501 = 3892313) B3892313
theorem B1532297 : Blo 401768 1532297 := bstep (se 2 (by rfl) ⟨574611, by rfl⟩ : syracuseStep 1532297 = 1149223) B1149223
theorem B6906545 : Blo 401768 6906545 := bstep (se 2 (by rfl) ⟨2589954, by rfl⟩ : syracuseStep 6906545 = 5179909) B5179909
theorem B910043 : Blo 401768 910043 := bstep (se 1 (by rfl) ⟨682532, by rfl⟩ : syracuseStep 910043 = 1365065) B1365065
theorem B1958687 : Blo 401768 1958687 := bstep (se 1 (by rfl) ⟨1469015, by rfl⟩ : syracuseStep 1958687 = 2938031) B2938031
theorem B681007 : Blo 401768 681007 := bstep (se 1 (by rfl) ⟨510755, by rfl⟩ : syracuseStep 681007 = 1021511) B1021511
theorem B910457 : Blo 401768 910457 := bstep (se 2 (by rfl) ⟨341421, by rfl⟩ : syracuseStep 910457 = 682843) B682843
theorem B1729849 : Blo 401768 1729849 := bstep (se 2 (by rfl) ⟨648693, by rfl⟩ : syracuseStep 1729849 = 1297387) B1297387
theorem B911123 : Blo 401768 911123 := bstep (se 1 (by rfl) ⟨683342, by rfl⟩ : syracuseStep 911123 = 1366685) B1366685
theorem B911339 : Blo 401768 911339 := bstep (se 1 (by rfl) ⟨683504, by rfl⟩ : syracuseStep 911339 = 1367009) B1367009
theorem B911483 : Blo 401768 911483 := bstep (se 1 (by rfl) ⟨683612, by rfl⟩ : syracuseStep 911483 = 1367225) B1367225
theorem B911753 : Blo 401768 911753 := bstep (se 2 (by rfl) ⟨341907, by rfl⟩ : syracuseStep 911753 = 683815) B683815
theorem B616939 : Blo 401768 616939 := bstep (se 1 (by rfl) ⟨462704, by rfl⟩ : syracuseStep 616939 = 925409) B925409
theorem B453415 : Blo 401768 453415 := bstep (se 1 (by rfl) ⟨340061, by rfl⟩ : syracuseStep 453415 = 680123) B680123
theorem B912455 : Blo 401768 912455 := bstep (se 1 (by rfl) ⟨684341, by rfl⟩ : syracuseStep 912455 = 1368683) B1368683
theorem B912851 : Blo 401768 912851 := bstep (se 1 (by rfl) ⟨684638, by rfl⟩ : syracuseStep 912851 = 1369277) B1369277
theorem B1797857 : Blo 401768 1797857 := bstep (se 2 (by rfl) ⟨674196, by rfl⟩ : syracuseStep 1797857 = 1348393) B1348393
theorem B454639 : Blo 401768 454639 := bstep (se 1 (by rfl) ⟨340979, by rfl⟩ : syracuseStep 454639 = 681959) B681959
theorem B454783 : Blo 401768 454783 := bstep (se 1 (by rfl) ⟨341087, by rfl⟩ : syracuseStep 454783 = 682175) B682175
theorem B1536185 : Blo 401768 1536185 := bstep (se 2 (by rfl) ⟨576069, by rfl⟩ : syracuseStep 1536185 = 1152139) B1152139
theorem B5796029 : Blo 401768 5796029 := bstep (se 3 (by rfl) ⟨1086755, by rfl⟩ : syracuseStep 5796029 = 2173511) B2173511
theorem B12415169 : Blo 401768 12415169 := bstep (se 2 (by rfl) ⟨4655688, by rfl⟩ : syracuseStep 12415169 = 9311377) B9311377
theorem B1536367 : Blo 401768 1536367 := bstep (se 1 (by rfl) ⟨1152275, by rfl⟩ : syracuseStep 1536367 = 2304551) B2304551
theorem B684443 : Blo 401768 684443 := bstep (se 1 (by rfl) ⟨513332, by rfl⟩ : syracuseStep 684443 = 1026665) B1026665
theorem B1536641 : Blo 401768 1536641 := bstep (se 2 (by rfl) ⟨576240, by rfl⟩ : syracuseStep 1536641 = 1152481) B1152481
theorem B2291111 : Blo 401768 2291111 := bstep (se 1 (by rfl) ⟨1718333, by rfl⟩ : syracuseStep 2291111 = 3436667) B3436667
theorem B1931087 : Blo 401768 1931087 := bstep (se 1 (by rfl) ⟨1448315, by rfl⟩ : syracuseStep 1931087 = 2896631) B2896631
theorem B7108667 : Blo 401768 7108667 := bstep (se 1 (by rfl) ⟨5331500, by rfl⟩ : syracuseStep 7108667 = 10663001) B10663001
theorem B3865097 : Blo 401768 3865097 := bstep (se 2 (by rfl) ⟨1449411, by rfl⟩ : syracuseStep 3865097 = 2898823) B2898823
theorem B33094277 : Blo 401768 33094277 := bstep (se 4 (by rfl) ⟨3102588, by rfl⟩ : syracuseStep 33094277 = 6205177) B6205177
theorem B3898313 : Blo 401768 3898313 := bstep (se 2 (by rfl) ⟨1461867, by rfl⟩ : syracuseStep 3898313 = 2923735) B2923735
theorem B1932511 : Blo 401768 1932511 := bstep (se 1 (by rfl) ⟨1449383, by rfl⟩ : syracuseStep 1932511 = 2898767) B2898767
theorem B1146079 : Blo 401768 1146079 := bstep (se 1 (by rfl) ⟨859559, by rfl⟩ : syracuseStep 1146079 = 1719119) B1719119
theorem B3440393 : Blo 401768 3440393 := bstep (se 2 (by rfl) ⟨1290147, by rfl⟩ : syracuseStep 3440393 = 2580295) B2580295
theorem B3867095 : Blo 401768 3867095 := bstep (se 1 (by rfl) ⟨2900321, by rfl⟩ : syracuseStep 3867095 = 5800643) B5800643
theorem B2458633 : Blo 401768 2458633 := bstep (se 2 (by rfl) ⟨921987, by rfl⟩ : syracuseStep 2458633 = 1843975) B1843975
theorem B2589853 : Blo 401768 2589853 := bstep (se 3 (by rfl) ⟨485597, by rfl⟩ : syracuseStep 2589853 = 971195) B971195
theorem B2917595 : Blo 401768 2917595 := bstep (se 1 (by rfl) ⟨2188196, by rfl⟩ : syracuseStep 2917595 = 4376393) B4376393
theorem B1836715 : Blo 401768 1836715 := bstep (se 1 (by rfl) ⟨1377536, by rfl⟩ : syracuseStep 1836715 = 2755073) B2755073
theorem B5834551 : Blo 401768 5834551 := bstep (se 1 (by rfl) ⟨4375913, by rfl⟩ : syracuseStep 5834551 = 8751827) B8751827
theorem B37455695 : Blo 401768 37455695 := bstep (se 1 (by rfl) ⟨28091771, by rfl⟩ : syracuseStep 37455695 = 56183543) B56183543
theorem B1017755 : Blo 401768 1017755 := bstep (se 1 (by rfl) ⟨763316, by rfl⟩ : syracuseStep 1017755 = 1526633) B1526633
theorem B5801975 : Blo 401768 5801975 := bstep (se 1 (by rfl) ⟨4351481, by rfl⟩ : syracuseStep 5801975 = 8702963) B8702963
theorem B4589783 : Blo 401768 4589783 := bstep (se 1 (by rfl) ⟨3442337, by rfl⟩ : syracuseStep 4589783 = 6884675) B6884675
theorem B1149383 : Blo 401768 1149383 := bstep (se 1 (by rfl) ⟨862037, by rfl⟩ : syracuseStep 1149383 = 1724075) B1724075
theorem B1149565 : Blo 401768 1149565 := bstep (se 3 (by rfl) ⟨215543, by rfl⟩ : syracuseStep 1149565 = 431087) B431087
theorem B4197203 : Blo 401768 4197203 := bstep (se 1 (by rfl) ⟨3147902, by rfl⟩ : syracuseStep 4197203 = 6295805) B6295805
theorem B5507959 : Blo 401768 5507959 := bstep (se 1 (by rfl) ⟨4130969, by rfl⟩ : syracuseStep 5507959 = 8261939) B8261939
theorem B1018889 : Blo 401768 1018889 := bstep (se 2 (by rfl) ⟨382083, by rfl⟩ : syracuseStep 1018889 = 764167) B764167
theorem B2591801 : Blo 401768 2591801 := bstep (se 2 (by rfl) ⟨971925, by rfl⟩ : syracuseStep 2591801 = 1943851) B1943851
theorem B2624879 : Blo 401768 2624879 := bstep (se 1 (by rfl) ⟨1968659, by rfl⟩ : syracuseStep 2624879 = 3937319) B3937319
theorem B1150955 : Blo 401768 1150955 := bstep (se 1 (by rfl) ⟨863216, by rfl⟩ : syracuseStep 1150955 = 1726433) B1726433
theorem B1020347 : Blo 401768 1020347 := bstep (se 1 (by rfl) ⟨765260, by rfl⟩ : syracuseStep 1020347 = 1530521) B1530521
theorem B8721209 : Blo 401768 8721209 := bstep (se 2 (by rfl) ⟨3270453, by rfl⟩ : syracuseStep 8721209 = 6540907) B6540907
theorem B5149565 : Blo 401768 5149565 := bstep (se 3 (by rfl) ⟨965543, by rfl⟩ : syracuseStep 5149565 = 1931087) B1931087
theorem B1086347 : Blo 401768 1086347 := bstep (se 1 (by rfl) ⟨814760, by rfl⟩ : syracuseStep 1086347 = 1629521) B1629521
theorem B1152083 : Blo 401768 1152083 := bstep (se 1 (by rfl) ⟨864062, by rfl⟩ : syracuseStep 1152083 = 1728125) B1728125
theorem B2593903 : Blo 401768 2593903 := bstep (se 1 (by rfl) ⟨1945427, by rfl⟩ : syracuseStep 2593903 = 3890855) B3890855
theorem B2037149 : Blo 401768 2037149 := bstep (se 3 (by rfl) ⟨381965, by rfl⟩ : syracuseStep 2037149 = 763931) B763931
theorem B6919667 : Blo 401768 6919667 := bstep (se 1 (by rfl) ⟨5189750, by rfl⟩ : syracuseStep 6919667 = 10379501) B10379501
theorem B2037311 : Blo 401768 2037311 := bstep (se 1 (by rfl) ⟨1527983, by rfl⟩ : syracuseStep 2037311 = 3055967) B3055967
theorem B2233937 : Blo 401768 2233937 := bstep (se 2 (by rfl) ⟨837726, by rfl⟩ : syracuseStep 2233937 = 1675453) B1675453
theorem B1021531 : Blo 401768 1021531 := bstep (se 1 (by rfl) ⟨766148, by rfl⟩ : syracuseStep 1021531 = 1532297) B1532297
theorem B2955323 : Blo 401768 2955323 := bstep (se 1 (by rfl) ⟨2216492, by rfl⟩ : syracuseStep 2955323 = 4432985) B4432985
theorem B858185 : Blo 401768 858185 := bstep (se 2 (by rfl) ⟨321819, by rfl⟩ : syracuseStep 858185 = 643639) B643639
theorem B1448489 : Blo 401768 1448489 := bstep (se 2 (by rfl) ⟨543183, by rfl⟩ : syracuseStep 1448489 = 1086367) B1086367
theorem B13966091 : Blo 401768 13966091 := bstep (se 1 (by rfl) ⟨10474568, by rfl⟩ : syracuseStep 13966091 = 20949137) B20949137
theorem B2038607 : Blo 401768 2038607 := bstep (se 1 (by rfl) ⟨1528955, by rfl⟩ : syracuseStep 2038607 = 3057911) B3057911
theorem B1022969 : Blo 401768 1022969 := bstep (se 2 (by rfl) ⟨383613, by rfl⟩ : syracuseStep 1022969 = 767227) B767227
theorem B1023617 : Blo 401768 1023617 := bstep (se 2 (by rfl) ⟨383856, by rfl⟩ : syracuseStep 1023617 = 767713) B767713
theorem B1024123 : Blo 401768 1024123 := bstep (se 1 (by rfl) ⟨768092, by rfl⟩ : syracuseStep 1024123 = 1536185) B1536185
theorem B4989053 : Blo 401768 4989053 := bstep (se 3 (by rfl) ⟨935447, by rfl⟩ : syracuseStep 4989053 = 1870895) B1870895
theorem B1024427 : Blo 401768 1024427 := bstep (se 1 (by rfl) ⟨768320, by rfl⟩ : syracuseStep 1024427 = 1536641) B1536641
theorem B402011 : Blo 401768 402011 := bstep (se 1 (by rfl) ⟨301508, by rfl⟩ : syracuseStep 402011 = 603017) B603017
theorem B402267 : Blo 401768 402267 := bstep (se 1 (by rfl) ⟨301700, by rfl⟩ : syracuseStep 402267 = 603401) B603401
theorem B402303 : Blo 401768 402303 := bstep (se 1 (by rfl) ⟨301727, by rfl⟩ : syracuseStep 402303 = 603455) B603455
theorem B402587 : Blo 401768 402587 := bstep (se 1 (by rfl) ⟨301940, by rfl⟩ : syracuseStep 402587 = 603881) B603881
theorem B402591 : Blo 401768 402591 := bstep (se 1 (by rfl) ⟨301943, by rfl⟩ : syracuseStep 402591 = 603887) B603887
theorem B402895 : Blo 401768 402895 := bstep (se 1 (by rfl) ⟨302171, by rfl⟩ : syracuseStep 402895 = 604343) B604343
theorem B402927 : Blo 401768 402927 := bstep (se 1 (by rfl) ⟨302195, by rfl⟩ : syracuseStep 402927 = 604391) B604391
theorem B403175 : Blo 401768 403175 := bstep (se 1 (by rfl) ⟨302381, by rfl⟩ : syracuseStep 403175 = 604763) B604763
theorem B22062851 : Blo 401768 22062851 := bstep (se 1 (by rfl) ⟨16547138, by rfl⟩ : syracuseStep 22062851 = 33094277) B33094277
theorem B2303801 : Blo 401768 2303801 := bstep (se 2 (by rfl) ⟨863925, by rfl⟩ : syracuseStep 2303801 = 1727851) B1727851
theorem B403271 : Blo 401768 403271 := bstep (se 1 (by rfl) ⟨302453, by rfl⟩ : syracuseStep 403271 = 604907) B604907
theorem B403291 : Blo 401768 403291 := bstep (se 1 (by rfl) ⟨302468, by rfl⟩ : syracuseStep 403291 = 604937) B604937
theorem B2598875 : Blo 401768 2598875 := bstep (se 1 (by rfl) ⟨1949156, by rfl⟩ : syracuseStep 2598875 = 3898313) B3898313
theorem B403871 : Blo 401768 403871 := bstep (se 1 (by rfl) ⟨302903, by rfl⟩ : syracuseStep 403871 = 605807) B605807
theorem B403951 : Blo 401768 403951 := bstep (se 1 (by rfl) ⟨302963, by rfl⟩ : syracuseStep 403951 = 605927) B605927
theorem B404079 : Blo 401768 404079 := bstep (se 1 (by rfl) ⟨303059, by rfl⟩ : syracuseStep 404079 = 606119) B606119
theorem B404295 : Blo 401768 404295 := bstep (se 1 (by rfl) ⟨303221, by rfl⟩ : syracuseStep 404295 = 606443) B606443
theorem B404335 : Blo 401768 404335 := bstep (se 1 (by rfl) ⟨303251, by rfl⟩ : syracuseStep 404335 = 606503) B606503
theorem B404783 : Blo 401768 404783 := bstep (se 1 (by rfl) ⟨303587, by rfl⟩ : syracuseStep 404783 = 607175) B607175
theorem B404895 : Blo 401768 404895 := bstep (se 1 (by rfl) ⟨303671, by rfl⟩ : syracuseStep 404895 = 607343) B607343
theorem B405023 : Blo 401768 405023 := bstep (se 1 (by rfl) ⟨303767, by rfl⟩ : syracuseStep 405023 = 607535) B607535
theorem B405159 : Blo 401768 405159 := bstep (se 1 (by rfl) ⟨303869, by rfl⟩ : syracuseStep 405159 = 607739) B607739
theorem B405183 : Blo 401768 405183 := bstep (se 1 (by rfl) ⟨303887, by rfl⟩ : syracuseStep 405183 = 607775) B607775
theorem B405279 : Blo 401768 405279 := bstep (se 1 (by rfl) ⟨303959, by rfl⟩ : syracuseStep 405279 = 607919) B607919
theorem B405359 : Blo 401768 405359 := bstep (se 1 (by rfl) ⟨304019, by rfl⟩ : syracuseStep 405359 = 608039) B608039
theorem B1716385 : Blo 401768 1716385 := bstep (se 2 (by rfl) ⟨643644, by rfl⟩ : syracuseStep 1716385 = 1287289) B1287289
theorem B405727 : Blo 401768 405727 := bstep (se 1 (by rfl) ⟨304295, by rfl⟩ : syracuseStep 405727 = 608591) B608591
theorem B405759 : Blo 401768 405759 := bstep (se 1 (by rfl) ⟨304319, by rfl⟩ : syracuseStep 405759 = 608639) B608639
theorem B1093895 : Blo 401768 1093895 := bstep (se 1 (by rfl) ⟨820421, by rfl⟩ : syracuseStep 1093895 = 1640843) B1640843
theorem B9843079 : Blo 401768 9843079 := bstep (se 1 (by rfl) ⟨7382309, by rfl⟩ : syracuseStep 9843079 = 14764619) B14764619
theorem B2306465 : Blo 401768 2306465 := bstep (se 2 (by rfl) ⟨864924, by rfl⟩ : syracuseStep 2306465 = 1729849) B1729849
theorem B2306717 : Blo 401768 2306717 := bstep (se 3 (by rfl) ⟨432509, by rfl⟩ : syracuseStep 2306717 = 865019) B865019
theorem B602831 : Blo 401768 602831 := bstep (se 1 (by rfl) ⟨452123, by rfl⟩ : syracuseStep 602831 = 904247) B904247
theorem B1455005 : Blo 401768 1455005 := bstep (se 3 (by rfl) ⟨272813, by rfl⟩ : syracuseStep 1455005 = 545627) B545627
theorem B603119 : Blo 401768 603119 := bstep (se 1 (by rfl) ⟨452339, by rfl⟩ : syracuseStep 603119 = 904679) B904679
theorem B1946909 : Blo 401768 1946909 := bstep (se 3 (by rfl) ⟨365045, by rfl⟩ : syracuseStep 1946909 = 730091) B730091
theorem B603503 : Blo 401768 603503 := bstep (se 1 (by rfl) ⟨452627, by rfl⟩ : syracuseStep 603503 = 905255) B905255
theorem B603623 : Blo 401768 603623 := bstep (se 1 (by rfl) ⟨452717, by rfl⟩ : syracuseStep 603623 = 905435) B905435
theorem B4929133 : Blo 401768 4929133 := bstep (se 3 (by rfl) ⟨924212, by rfl⟩ : syracuseStep 4929133 = 1848425) B1848425
theorem B603803 : Blo 401768 603803 := bstep (se 1 (by rfl) ⟨452852, by rfl⟩ : syracuseStep 603803 = 905705) B905705
theorem B1226447 : Blo 401768 1226447 := bstep (se 1 (by rfl) ⟨919835, by rfl⟩ : syracuseStep 1226447 = 1839671) B1839671
theorem B14005993 : Blo 401768 14005993 := bstep (se 2 (by rfl) ⟨5252247, by rfl⟩ : syracuseStep 14005993 = 10504495) B10504495
theorem B866207 : Blo 401768 866207 := bstep (se 1 (by rfl) ⟨649655, by rfl⟩ : syracuseStep 866207 = 1299311) B1299311
theorem B604139 : Blo 401768 604139 := bstep (se 1 (by rfl) ⟨453104, by rfl⟩ : syracuseStep 604139 = 906209) B906209
theorem B604223 : Blo 401768 604223 := bstep (se 1 (by rfl) ⟨453167, by rfl⟩ : syracuseStep 604223 = 906335) B906335
theorem B604553 : Blo 401768 604553 := bstep (se 2 (by rfl) ⟨226707, by rfl⟩ : syracuseStep 604553 = 453415) B453415
theorem B768503 : Blo 401768 768503 := bstep (se 1 (by rfl) ⟨576377, by rfl⟩ : syracuseStep 768503 = 1152755) B1152755
theorem B604727 : Blo 401768 604727 := bstep (se 1 (by rfl) ⟨453545, by rfl⟩ : syracuseStep 604727 = 907091) B907091
theorem B605051 : Blo 401768 605051 := bstep (se 1 (by rfl) ⟨453788, by rfl⟩ : syracuseStep 605051 = 907577) B907577
theorem B4602905 : Blo 401768 4602905 := bstep (se 2 (by rfl) ⟨1726089, by rfl⟩ : syracuseStep 4602905 = 3452179) B3452179
theorem B1359017 : Blo 401768 1359017 := bstep (se 2 (by rfl) ⟨509631, by rfl⟩ : syracuseStep 1359017 = 1019263) B1019263
theorem B605663 : Blo 401768 605663 := bstep (se 1 (by rfl) ⟨454247, by rfl⟩ : syracuseStep 605663 = 908495) B908495
theorem B605915 : Blo 401768 605915 := bstep (se 1 (by rfl) ⟨454436, by rfl⟩ : syracuseStep 605915 = 908873) B908873
theorem B1720061 : Blo 401768 1720061 := bstep (se 3 (by rfl) ⟨322511, by rfl⟩ : syracuseStep 1720061 = 645023) B645023
theorem B606185 : Blo 401768 606185 := bstep (se 2 (by rfl) ⟨227319, by rfl⟩ : syracuseStep 606185 = 454639) B454639
theorem B606377 : Blo 401768 606377 := bstep (se 2 (by rfl) ⟨227391, by rfl⟩ : syracuseStep 606377 = 454783) B454783
theorem B4604363 : Blo 401768 4604363 := bstep (se 1 (by rfl) ⟨3453272, by rfl⟩ : syracuseStep 4604363 = 6906545) B6906545
theorem B606695 : Blo 401768 606695 := bstep (se 1 (by rfl) ⟨455021, by rfl⟩ : syracuseStep 606695 = 910043) B910043
theorem B2048489 : Blo 401768 2048489 := bstep (se 2 (by rfl) ⟨768183, by rfl⟩ : syracuseStep 2048489 = 1536367) B1536367
theorem B606971 : Blo 401768 606971 := bstep (se 1 (by rfl) ⟨455228, by rfl⟩ : syracuseStep 606971 = 910457) B910457
theorem B509095 : Blo 401768 509095 := bstep (se 1 (by rfl) ⟨381821, by rfl⟩ : syracuseStep 509095 = 763643) B763643
theorem B607415 : Blo 401768 607415 := bstep (se 1 (by rfl) ⟨455561, by rfl⟩ : syracuseStep 607415 = 911123) B911123
theorem B607559 : Blo 401768 607559 := bstep (se 1 (by rfl) ⟨455669, by rfl⟩ : syracuseStep 607559 = 911339) B911339
theorem B607655 : Blo 401768 607655 := bstep (se 1 (by rfl) ⟨455741, by rfl⟩ : syracuseStep 607655 = 911483) B911483
theorem B607835 : Blo 401768 607835 := bstep (se 1 (by rfl) ⟨455876, by rfl⟩ : syracuseStep 607835 = 911753) B911753
theorem B10340135 : Blo 401768 10340135 := bstep (se 1 (by rfl) ⟨7755101, by rfl⟩ : syracuseStep 10340135 = 15510203) B15510203
theorem B2213689 : Blo 401768 2213689 := bstep (se 2 (by rfl) ⟨830133, by rfl⟩ : syracuseStep 2213689 = 1660267) B1660267
theorem B13158359 : Blo 401768 13158359 := bstep (se 1 (by rfl) ⟨9868769, by rfl⟩ : syracuseStep 13158359 = 19737539) B19737539
theorem B608303 : Blo 401768 608303 := bstep (se 1 (by rfl) ⟨456227, by rfl⟩ : syracuseStep 608303 = 912455) B912455
theorem B1296607 : Blo 401768 1296607 := bstep (se 1 (by rfl) ⟨972455, by rfl⟩ : syracuseStep 1296607 = 1944911) B1944911
theorem B608567 : Blo 401768 608567 := bstep (se 1 (by rfl) ⟨456425, by rfl⟩ : syracuseStep 608567 = 912851) B912851
theorem B1198571 : Blo 401768 1198571 := bstep (se 1 (by rfl) ⟨898928, by rfl⟩ : syracuseStep 1198571 = 1797857) B1797857
theorem B1362473 : Blo 401768 1362473 := bstep (se 2 (by rfl) ⟨510927, by rfl⟩ : syracuseStep 1362473 = 1021855) B1021855
theorem B8276779 : Blo 401768 8276779 := bstep (se 1 (by rfl) ⟨6207584, by rfl⟩ : syracuseStep 8276779 = 12415169) B12415169
theorem B510943 : Blo 401768 510943 := bstep (se 1 (by rfl) ⟨383207, by rfl⟩ : syracuseStep 510943 = 766415) B766415
theorem B137088385 : Blo 401768 137088385 := bstep (se 2 (by rfl) ⟨51408144, by rfl⟩ : syracuseStep 137088385 = 102816289) B102816289
theorem B1527407 : Blo 401768 1527407 := bstep (se 1 (by rfl) ⟨1145555, by rfl⟩ : syracuseStep 1527407 = 2291111) B2291111
theorem B577135 : Blo 401768 577135 := bstep (se 1 (by rfl) ⟨432851, by rfl⟩ : syracuseStep 577135 = 865703) B865703
theorem B970505 : Blo 401768 970505 := bstep (se 2 (by rfl) ⟨363939, by rfl⟩ : syracuseStep 970505 = 727879) B727879
theorem B905039 : Blo 401768 905039 := bstep (se 1 (by rfl) ⟨678779, by rfl⟩ : syracuseStep 905039 = 1357559) B1357559
theorem B4739111 : Blo 401768 4739111 := bstep (se 1 (by rfl) ⟨3554333, by rfl⟩ : syracuseStep 4739111 = 7108667) B7108667
theorem B2576681 : Blo 401768 2576681 := bstep (se 2 (by rfl) ⟨966255, by rfl⟩ : syracuseStep 2576681 = 1932511) B1932511
theorem B1528105 : Blo 401768 1528105 := bstep (se 2 (by rfl) ⟨573039, by rfl⟩ : syracuseStep 1528105 = 1146079) B1146079
theorem B2576731 : Blo 401768 2576731 := bstep (se 1 (by rfl) ⟨1932548, by rfl⟩ : syracuseStep 2576731 = 3865097) B3865097
theorem B905759 : Blo 401768 905759 := bstep (se 1 (by rfl) ⟨679319, by rfl⟩ : syracuseStep 905759 = 1358639) B1358639
theorem B512831 : Blo 401768 512831 := bstep (se 1 (by rfl) ⟨384623, by rfl⟩ : syracuseStep 512831 = 769247) B769247
theorem B13161365 : Blo 401768 13161365 := bstep (se 6 (by rfl) ⟨308469, by rfl⟩ : syracuseStep 13161365 = 616939) B616939
theorem B1364903 : Blo 401768 1364903 := bstep (se 1 (by rfl) ⟨1023677, by rfl⟩ : syracuseStep 1364903 = 2047355) B2047355
theorem B906191 : Blo 401768 906191 := bstep (se 1 (by rfl) ⟨679643, by rfl⟩ : syracuseStep 906191 = 1359287) B1359287
theorem B906281 : Blo 401768 906281 := bstep (se 2 (by rfl) ⟨339855, by rfl⟩ : syracuseStep 906281 = 679711) B679711
theorem B906551 : Blo 401768 906551 := bstep (se 1 (by rfl) ⟨679913, by rfl⟩ : syracuseStep 906551 = 1359827) B1359827
theorem B906569 : Blo 401768 906569 := bstep (se 2 (by rfl) ⟨339963, by rfl⟩ : syracuseStep 906569 = 679927) B679927
theorem B906857 : Blo 401768 906857 := bstep (se 2 (by rfl) ⟨340071, by rfl⟩ : syracuseStep 906857 = 680143) B680143
theorem B1529563 : Blo 401768 1529563 := bstep (se 1 (by rfl) ⟨1147172, by rfl⟩ : syracuseStep 1529563 = 2294345) B2294345
theorem B1365767 : Blo 401768 1365767 := bstep (se 1 (by rfl) ⟨1024325, by rfl⟩ : syracuseStep 1365767 = 2048651) B2048651
theorem B1103863 : Blo 401768 1103863 := bstep (se 1 (by rfl) ⟨827897, by rfl⟩ : syracuseStep 1103863 = 1655795) B1655795
theorem B1726535 : Blo 401768 1726535 := bstep (se 1 (by rfl) ⟨1294901, by rfl⟩ : syracuseStep 1726535 = 2589803) B2589803
theorem B3070061 : Blo 401768 3070061 := bstep (se 3 (by rfl) ⟨575636, by rfl⟩ : syracuseStep 3070061 = 1151273) B1151273
theorem B907487 : Blo 401768 907487 := bstep (se 1 (by rfl) ⟨680615, by rfl⟩ : syracuseStep 907487 = 1361231) B1361231
theorem B907559 : Blo 401768 907559 := bstep (se 1 (by rfl) ⟨680669, by rfl⟩ : syracuseStep 907559 = 1361339) B1361339
theorem B907919 : Blo 401768 907919 := bstep (se 1 (by rfl) ⟨680939, by rfl⟩ : syracuseStep 907919 = 1361879) B1361879
theorem B3889853 : Blo 401768 3889853 := bstep (se 3 (by rfl) ⟨729347, by rfl⟩ : syracuseStep 3889853 = 1458695) B1458695
theorem B645823 : Blo 401768 645823 := bstep (se 1 (by rfl) ⟨484367, by rfl⟩ : syracuseStep 645823 = 968735) B968735
theorem B908009 : Blo 401768 908009 := bstep (se 2 (by rfl) ⟨340503, by rfl⟩ : syracuseStep 908009 = 681007) B681007
theorem B678719 : Blo 401768 678719 := bstep (se 1 (by rfl) ⟨509039, by rfl⟩ : syracuseStep 678719 = 1018079) B1018079
theorem B4578119 : Blo 401768 4578119 := bstep (se 1 (by rfl) ⟨3433589, by rfl⟩ : syracuseStep 4578119 = 6867179) B6867179
theorem B7789547 : Blo 401768 7789547 := bstep (se 1 (by rfl) ⟨5842160, by rfl⟩ : syracuseStep 7789547 = 11684321) B11684321
theorem B1039451 : Blo 401768 1039451 := bstep (se 1 (by rfl) ⟨779588, by rfl⟩ : syracuseStep 1039451 = 1559177) B1559177
theorem B547931 : Blo 401768 547931 := bstep (se 1 (by rfl) ⟨410948, by rfl⟩ : syracuseStep 547931 = 821897) B821897
theorem B646375 : Blo 401768 646375 := bstep (se 1 (by rfl) ⟨484781, by rfl⟩ : syracuseStep 646375 = 969563) B969563
theorem B1367387 : Blo 401768 1367387 := bstep (se 1 (by rfl) ⟨1025540, by rfl⟩ : syracuseStep 1367387 = 2051081) B2051081
theorem B613759 : Blo 401768 613759 := bstep (se 1 (by rfl) ⟨460319, by rfl⟩ : syracuseStep 613759 = 920639) B920639
theorem B6544871 : Blo 401768 6544871 := bstep (se 1 (by rfl) ⟨4908653, by rfl⟩ : syracuseStep 6544871 = 9817307) B9817307
theorem B1400743 : Blo 401768 1400743 := bstep (se 1 (by rfl) ⟨1050557, by rfl⟩ : syracuseStep 1400743 = 2101115) B2101115
theorem B1368359 : Blo 401768 1368359 := bstep (se 1 (by rfl) ⟨1026269, by rfl⟩ : syracuseStep 1368359 = 2052539) B2052539
theorem B1532479 : Blo 401768 1532479 := bstep (se 1 (by rfl) ⟨1149359, by rfl⟩ : syracuseStep 1532479 = 2298719) B2298719
theorem B1368737 : Blo 401768 1368737 := bstep (se 2 (by rfl) ⟨513276, by rfl⟩ : syracuseStep 1368737 = 1026553) B1026553
theorem B2909087 : Blo 401768 2909087 := bstep (se 1 (by rfl) ⟨2181815, by rfl⟩ : syracuseStep 2909087 = 4363631) B4363631
theorem B1369223 : Blo 401768 1369223 := bstep (se 1 (by rfl) ⟨1026917, by rfl⟩ : syracuseStep 1369223 = 2053835) B2053835
theorem B1369385 : Blo 401768 1369385 := bstep (se 2 (by rfl) ⟨513519, by rfl⟩ : syracuseStep 1369385 = 1027039) B1027039
theorem B681385 : Blo 401768 681385 := bstep (se 2 (by rfl) ⟨255519, by rfl⟩ : syracuseStep 681385 = 511039) B511039
theorem B2024875 : Blo 401768 2024875 := bstep (se 1 (by rfl) ⟨1518656, by rfl⟩ : syracuseStep 2024875 = 3037313) B3037313
theorem B1533437 : Blo 401768 1533437 := bstep (se 3 (by rfl) ⟨287519, by rfl⟩ : syracuseStep 1533437 = 575039) B575039
theorem B681851 : Blo 401768 681851 := bstep (se 1 (by rfl) ⟨511388, by rfl⟩ : syracuseStep 681851 = 1022777) B1022777
theorem B3073949 : Blo 401768 3073949 := bstep (se 3 (by rfl) ⟨576365, by rfl⟩ : syracuseStep 3073949 = 1152731) B1152731
theorem B682121 : Blo 401768 682121 := bstep (se 2 (by rfl) ⟨255795, by rfl⟩ : syracuseStep 682121 = 511591) B511591
theorem B168487559 : Blo 401768 168487559 := bstep (se 1 (by rfl) ⟨126365669, by rfl⟩ : syracuseStep 168487559 = 252731339) B252731339
theorem B1305791 : Blo 401768 1305791 := bstep (se 1 (by rfl) ⟨979343, by rfl⟩ : syracuseStep 1305791 = 1958687) B1958687
theorem B683903 : Blo 401768 683903 := bstep (se 1 (by rfl) ⟨512927, by rfl⟩ : syracuseStep 683903 = 1025855) B1025855
theorem B1863805 : Blo 401768 1863805 := bstep (se 3 (by rfl) ⟨349463, by rfl⟩ : syracuseStep 1863805 = 698927) B698927
theorem B25555301 : Blo 401768 25555301 := bstep (se 4 (by rfl) ⟨2395809, by rfl⟩ : syracuseStep 25555301 = 4791619) B4791619
theorem B3699593 : Blo 401768 3699593 := bstep (se 2 (by rfl) ⟨1387347, by rfl⟩ : syracuseStep 3699593 = 2774695) B2774695
theorem B8615159 : Blo 401768 8615159 := bstep (se 1 (by rfl) ⟨6461369, by rfl⟩ : syracuseStep 8615159 = 12922739) B12922739
theorem B3864019 : Blo 401768 3864019 := bstep (se 1 (by rfl) ⟨2898014, by rfl⟩ : syracuseStep 3864019 = 5796029) B5796029
theorem B456295 : Blo 401768 456295 := bstep (se 1 (by rfl) ⟨342221, by rfl⟩ : syracuseStep 456295 = 684443) B684443
theorem B2914451 : Blo 401768 2914451 := bstep (se 1 (by rfl) ⟨2185838, by rfl⟩ : syracuseStep 2914451 = 4371677) B4371677
theorem B1931627 : Blo 401768 1931627 := bstep (se 1 (by rfl) ⟨1448720, by rfl⟩ : syracuseStep 1931627 = 2897441) B2897441
theorem B1145249 : Blo 401768 1145249 := bstep (se 2 (by rfl) ⟨429468, by rfl⟩ : syracuseStep 1145249 = 858937) B858937
theorem B8288851 : Blo 401768 8288851 := bstep (se 1 (by rfl) ⟨6216638, by rfl⟩ : syracuseStep 8288851 = 12433277) B12433277
theorem B3898853 : Blo 401768 3898853 := bstep (se 4 (by rfl) ⟨365517, by rfl⟩ : syracuseStep 3898853 = 731035) B731035
theorem B2293595 : Blo 401768 2293595 := bstep (se 1 (by rfl) ⟨1720196, by rfl⟩ : syracuseStep 2293595 = 3440393) B3440393
theorem B24970463 : Blo 401768 24970463 := bstep (se 1 (by rfl) ⟨18727847, by rfl⟩ : syracuseStep 24970463 = 37455695) B37455695
theorem B3867983 : Blo 401768 3867983 := bstep (se 1 (by rfl) ⟨2900987, by rfl⟩ : syracuseStep 3867983 = 5801975) B5801975
theorem B3278177 : Blo 401768 3278177 := bstep (se 2 (by rfl) ⟨1229316, by rfl⟩ : syracuseStep 3278177 = 2458633) B2458633
theorem B1018271 : Blo 401768 1018271 := bstep (se 1 (by rfl) ⟨763703, by rfl⟩ : syracuseStep 1018271 = 1527407) B1527407
theorem B2951585 : Blo 401768 2951585 := bstep (se 2 (by rfl) ⟨1106844, by rfl⟩ : syracuseStep 2951585 = 2213689) B2213689
theorem B724231 : Blo 401768 724231 := bstep (se 1 (by rfl) ⟨543173, by rfl⟩ : syracuseStep 724231 = 1086347) B1086347
theorem B3444389 : Blo 401768 3444389 := bstep (se 4 (by rfl) ⟨322911, by rfl⟩ : syracuseStep 3444389 = 645823) B645823
theorem B7343945 : Blo 401768 7343945 := bstep (se 2 (by rfl) ⟨2753979, by rfl⟩ : syracuseStep 7343945 = 5507959) B5507959
theorem B1151023 : Blo 401768 1151023 := bstep (se 1 (by rfl) ⟨863267, by rfl⟩ : syracuseStep 1151023 = 1726535) B1726535
theorem B2593235 : Blo 401768 2593235 := bstep (se 1 (by rfl) ⟨1944926, by rfl⟩ : syracuseStep 2593235 = 3889853) B3889853
theorem B9310727 : Blo 401768 9310727 := bstep (se 1 (by rfl) ⟨6983045, by rfl⟩ : syracuseStep 9310727 = 13966091) B13966091
theorem B3052079 : Blo 401768 3052079 := bstep (se 1 (by rfl) ⟨2289059, by rfl⟩ : syracuseStep 3052079 = 4578119) B4578119
theorem B4363247 : Blo 401768 4363247 := bstep (se 1 (by rfl) ⟨3272435, by rfl⟩ : syracuseStep 4363247 = 6544871) B6544871
theorem B2037473 : Blo 401768 2037473 := bstep (se 2 (by rfl) ⟨764052, by rfl⟩ : syracuseStep 2037473 = 1528105) B1528105
theorem B1939391 : Blo 401768 1939391 := bstep (se 1 (by rfl) ⟨1454543, by rfl⟩ : syracuseStep 1939391 = 2909087) B2909087
theorem B1022291 : Blo 401768 1022291 := bstep (se 1 (by rfl) ⟨766718, by rfl⟩ : syracuseStep 1022291 = 1533437) B1533437
theorem B5152025 : Blo 401768 5152025 := bstep (se 2 (by rfl) ⟨1932009, by rfl⟩ : syracuseStep 5152025 = 3864019) B3864019
theorem B2039417 : Blo 401768 2039417 := bstep (se 2 (by rfl) ⟨764781, by rfl⟩ : syracuseStep 2039417 = 1529563) B1529563
theorem B2924552213 : Blo 401768 2924552213 := bstep (se 6 (by rfl) ⟨68544192, by rfl⟩ : syracuseStep 2924552213 = 137088385) B137088385
theorem B729263 : Blo 401768 729263 := bstep (se 1 (by rfl) ⟨546947, by rfl⟩ : syracuseStep 729263 = 1093895) B1093895
theorem B401887 : Blo 401768 401887 := bstep (se 1 (by rfl) ⟨301415, by rfl⟩ : syracuseStep 401887 = 602831) B602831
theorem B2466395 : Blo 401768 2466395 := bstep (se 1 (by rfl) ⟨1849796, by rfl⟩ : syracuseStep 2466395 = 3699593) B3699593
theorem B402079 : Blo 401768 402079 := bstep (se 1 (by rfl) ⟨301559, by rfl⟩ : syracuseStep 402079 = 603119) B603119
theorem B11051801 : Blo 401768 11051801 := bstep (se 2 (by rfl) ⟨4144425, by rfl⟩ : syracuseStep 11051801 = 8288851) B8288851
theorem B5743439 : Blo 401768 5743439 := bstep (se 1 (by rfl) ⟨4307579, by rfl⟩ : syracuseStep 5743439 = 8615159) B8615159
theorem B402335 : Blo 401768 402335 := bstep (se 1 (by rfl) ⟨301751, by rfl⟩ : syracuseStep 402335 = 603503) B603503
theorem B402415 : Blo 401768 402415 := bstep (se 1 (by rfl) ⟨301811, by rfl⟩ : syracuseStep 402415 = 603623) B603623
theorem B402535 : Blo 401768 402535 := bstep (se 1 (by rfl) ⟨301901, by rfl⟩ : syracuseStep 402535 = 603803) B603803
theorem B402759 : Blo 401768 402759 := bstep (se 1 (by rfl) ⟨302069, by rfl⟩ : syracuseStep 402759 = 604139) B604139
theorem B402815 : Blo 401768 402815 := bstep (se 1 (by rfl) ⟨302111, by rfl⟩ : syracuseStep 402815 = 604223) B604223
theorem B1942967 : Blo 401768 1942967 := bstep (se 1 (by rfl) ⟨1457225, by rfl⟩ : syracuseStep 1942967 = 2914451) B2914451
theorem B1287751 : Blo 401768 1287751 := bstep (se 1 (by rfl) ⟨965813, by rfl⟩ : syracuseStep 1287751 = 1931627) B1931627
theorem B403035 : Blo 401768 403035 := bstep (se 1 (by rfl) ⟨302276, by rfl⟩ : syracuseStep 403035 = 604553) B604553
theorem B763499 : Blo 401768 763499 := bstep (se 1 (by rfl) ⟨572624, by rfl⟩ : syracuseStep 763499 = 1145249) B1145249
theorem B861833 : Blo 401768 861833 := bstep (se 2 (by rfl) ⟨323187, by rfl⟩ : syracuseStep 861833 = 646375) B646375
theorem B403151 : Blo 401768 403151 := bstep (se 1 (by rfl) ⟨302363, by rfl⟩ : syracuseStep 403151 = 604727) B604727
theorem B403367 : Blo 401768 403367 := bstep (se 1 (by rfl) ⟨302525, by rfl⟩ : syracuseStep 403367 = 605051) B605051
theorem B403775 : Blo 401768 403775 := bstep (se 1 (by rfl) ⟨302831, by rfl⟩ : syracuseStep 403775 = 605663) B605663
theorem B2599235 : Blo 401768 2599235 := bstep (se 1 (by rfl) ⟨1949426, by rfl⟩ : syracuseStep 2599235 = 3898853) B3898853
theorem B403943 : Blo 401768 403943 := bstep (se 1 (by rfl) ⟨302957, by rfl⟩ : syracuseStep 403943 = 605915) B605915
theorem B404123 : Blo 401768 404123 := bstep (se 1 (by rfl) ⟨303092, by rfl⟩ : syracuseStep 404123 = 606185) B606185
theorem B404251 : Blo 401768 404251 := bstep (se 1 (by rfl) ⟨303188, by rfl⟩ : syracuseStep 404251 = 606377) B606377
theorem B404463 : Blo 401768 404463 := bstep (se 1 (by rfl) ⟨303347, by rfl⟩ : syracuseStep 404463 = 606695) B606695
theorem B404647 : Blo 401768 404647 := bstep (se 1 (by rfl) ⟨303485, by rfl⟩ : syracuseStep 404647 = 606971) B606971
theorem B2043305 : Blo 401768 2043305 := bstep (se 2 (by rfl) ⟨766239, by rfl⟩ : syracuseStep 2043305 = 1532479) B1532479
theorem B404943 : Blo 401768 404943 := bstep (se 1 (by rfl) ⟨303707, by rfl⟩ : syracuseStep 404943 = 607415) B607415
theorem B1945063 : Blo 401768 1945063 := bstep (se 1 (by rfl) ⟨1458797, by rfl⟩ : syracuseStep 1945063 = 2917595) B2917595
theorem B405039 : Blo 401768 405039 := bstep (se 1 (by rfl) ⟨303779, by rfl⟩ : syracuseStep 405039 = 607559) B607559
theorem B405103 : Blo 401768 405103 := bstep (se 1 (by rfl) ⟨303827, by rfl⟩ : syracuseStep 405103 = 607655) B607655
theorem B405223 : Blo 401768 405223 := bstep (se 1 (by rfl) ⟨303917, by rfl⟩ : syracuseStep 405223 = 607835) B607835
theorem B6893423 : Blo 401768 6893423 := bstep (se 1 (by rfl) ⟨5170067, by rfl⟩ : syracuseStep 6893423 = 10340135) B10340135
theorem B405535 : Blo 401768 405535 := bstep (se 1 (by rfl) ⟨304151, by rfl⟩ : syracuseStep 405535 = 608303) B608303
theorem B3059855 : Blo 401768 3059855 := bstep (se 1 (by rfl) ⟨2294891, by rfl⟩ : syracuseStep 3059855 = 4589783) B4589783
theorem B405711 : Blo 401768 405711 := bstep (se 1 (by rfl) ⟨304283, by rfl⟩ : syracuseStep 405711 = 608567) B608567
theorem B3453137 : Blo 401768 3453137 := bstep (se 2 (by rfl) ⟨1294926, by rfl⟩ : syracuseStep 3453137 = 2589853) B2589853
theorem B766255 : Blo 401768 766255 := bstep (se 1 (by rfl) ⟨574691, by rfl⟩ : syracuseStep 766255 = 1149383) B1149383
theorem B2798135 : Blo 401768 2798135 := bstep (se 1 (by rfl) ⟨2098601, by rfl⟩ : syracuseStep 2798135 = 4197203) B4197203
theorem B2699833 : Blo 401768 2699833 := bstep (se 2 (by rfl) ⟨1012437, by rfl⟩ : syracuseStep 2699833 = 2024875) B2024875
theorem B1749919 : Blo 401768 1749919 := bstep (se 1 (by rfl) ⟨1312439, by rfl⟩ : syracuseStep 1749919 = 2624879) B2624879
theorem B7779401 : Blo 401768 7779401 := bstep (se 2 (by rfl) ⟨2917275, by rfl⟩ : syracuseStep 7779401 = 5834551) B5834551
theorem B603359 : Blo 401768 603359 := bstep (se 1 (by rfl) ⟨452519, by rfl⟩ : syracuseStep 603359 = 905039) B905039
theorem B767303 : Blo 401768 767303 := bstep (se 1 (by rfl) ⟨575477, by rfl⟩ : syracuseStep 767303 = 1150955) B1150955
theorem B3159407 : Blo 401768 3159407 := bstep (se 1 (by rfl) ⟨2369555, by rfl⟩ : syracuseStep 3159407 = 4739111) B4739111
theorem B1717787 : Blo 401768 1717787 := bstep (se 1 (by rfl) ⟨1288340, by rfl⟩ : syracuseStep 1717787 = 2576681) B2576681
theorem B603839 : Blo 401768 603839 := bstep (se 1 (by rfl) ⟨452879, by rfl⟩ : syracuseStep 603839 = 905759) B905759
theorem B5814139 : Blo 401768 5814139 := bstep (se 1 (by rfl) ⟨4360604, by rfl⟩ : syracuseStep 5814139 = 8721209) B8721209
theorem B604127 : Blo 401768 604127 := bstep (se 1 (by rfl) ⟨453095, by rfl⟩ : syracuseStep 604127 = 906191) B906191
theorem B604187 : Blo 401768 604187 := bstep (se 1 (by rfl) ⟨453140, by rfl⟩ : syracuseStep 604187 = 906281) B906281
theorem B768055 : Blo 401768 768055 := bstep (se 1 (by rfl) ⟨576041, by rfl⟩ : syracuseStep 768055 = 1152083) B1152083
theorem B604367 : Blo 401768 604367 := bstep (se 1 (by rfl) ⟨453275, by rfl⟩ : syracuseStep 604367 = 906551) B906551
theorem B604379 : Blo 401768 604379 := bstep (se 1 (by rfl) ⟨453284, by rfl⟩ : syracuseStep 604379 = 906569) B906569
theorem B1358099 : Blo 401768 1358099 := bstep (se 1 (by rfl) ⟨1018574, by rfl⟩ : syracuseStep 1358099 = 2037149) B2037149
theorem B1358207 : Blo 401768 1358207 := bstep (se 1 (by rfl) ⟨1018655, by rfl⟩ : syracuseStep 1358207 = 2037311) B2037311
theorem B1489291 : Blo 401768 1489291 := bstep (se 1 (by rfl) ⟨1116968, by rfl⟩ : syracuseStep 1489291 = 2233937) B2233937
theorem B604571 : Blo 401768 604571 := bstep (se 1 (by rfl) ⟨453428, by rfl⟩ : syracuseStep 604571 = 906857) B906857
theorem B572123 : Blo 401768 572123 := bstep (se 1 (by rfl) ⟨429092, by rfl⟩ : syracuseStep 572123 = 858185) B858185
theorem B2046707 : Blo 401768 2046707 := bstep (se 1 (by rfl) ⟨1535030, by rfl⟩ : syracuseStep 2046707 = 3070061) B3070061
theorem B604991 : Blo 401768 604991 := bstep (se 1 (by rfl) ⟨453743, by rfl⟩ : syracuseStep 604991 = 907487) B907487
theorem B605039 : Blo 401768 605039 := bstep (se 1 (by rfl) ⟨453779, by rfl⟩ : syracuseStep 605039 = 907559) B907559
theorem B605279 : Blo 401768 605279 := bstep (se 1 (by rfl) ⟨453959, by rfl⟩ : syracuseStep 605279 = 907919) B907919
theorem B605339 : Blo 401768 605339 := bstep (se 1 (by rfl) ⟨454004, by rfl⟩ : syracuseStep 605339 = 908009) B908009
theorem B1359071 : Blo 401768 1359071 := bstep (se 1 (by rfl) ⟨1019303, by rfl⟩ : syracuseStep 1359071 = 2038607) B2038607
theorem B5193031 : Blo 401768 5193031 := bstep (se 1 (by rfl) ⟨3894773, by rfl⟩ : syracuseStep 5193031 = 7789547) B7789547
theorem B769513 : Blo 401768 769513 := bstep (se 2 (by rfl) ⟨288567, by rfl⟩ : syracuseStep 769513 = 577135) B577135
theorem B3326035 : Blo 401768 3326035 := bstep (se 1 (by rfl) ⟨2494526, by rfl⟩ : syracuseStep 3326035 = 4989053) B4989053
theorem B7880861 : Blo 401768 7880861 := bstep (se 3 (by rfl) ⟨1477661, by rfl⟩ : syracuseStep 7880861 = 2955323) B2955323
theorem B13124105 : Blo 401768 13124105 := bstep (se 2 (by rfl) ⟨4921539, by rfl⟩ : syracuseStep 13124105 = 9843079) B9843079
theorem B2049299 : Blo 401768 2049299 := bstep (se 1 (by rfl) ⟨1536974, by rfl⟩ : syracuseStep 2049299 = 3073949) B3073949
theorem B3196189 : Blo 401768 3196189 := bstep (se 3 (by rfl) ⟨599285, by rfl⟩ : syracuseStep 3196189 = 1198571) B1198571
theorem B3458537 : Blo 401768 3458537 := bstep (se 2 (by rfl) ⟨1296951, by rfl⟩ : syracuseStep 3458537 = 2593903) B2593903
theorem B1362041 : Blo 401768 1362041 := bstep (se 2 (by rfl) ⟨510765, by rfl⟩ : syracuseStep 1362041 = 1021531) B1021531
theorem B870527 : Blo 401768 870527 := bstep (se 1 (by rfl) ⟨652895, by rfl⟩ : syracuseStep 870527 = 1305791) B1305791
theorem B608393 : Blo 401768 608393 := bstep (se 2 (by rfl) ⟨228147, by rfl⟩ : syracuseStep 608393 = 456295) B456295
theorem B6572177 : Blo 401768 6572177 := bstep (se 2 (by rfl) ⟨2464566, by rfl⟩ : syracuseStep 6572177 = 4929133) B4929133
theorem B2771869 : Blo 401768 2771869 := bstep (se 3 (by rfl) ⟨519725, by rfl⟩ : syracuseStep 2771869 = 1039451) B1039451
theorem B1461149 : Blo 401768 1461149 := bstep (se 3 (by rfl) ⟨273965, by rfl⟩ : syracuseStep 1461149 = 547931) B547931
theorem B970003 : Blo 401768 970003 := bstep (se 1 (by rfl) ⟨727502, by rfl⟩ : syracuseStep 970003 = 1455005) B1455005
theorem B1297939 : Blo 401768 1297939 := bstep (se 1 (by rfl) ⟨973454, by rfl⟩ : syracuseStep 1297939 = 1946909) B1946909
theorem B577471 : Blo 401768 577471 := bstep (se 1 (by rfl) ⟨433103, by rfl⟩ : syracuseStep 577471 = 866207) B866207
theorem B512335 : Blo 401768 512335 := bstep (se 1 (by rfl) ⟨384251, by rfl⟩ : syracuseStep 512335 = 768503) B768503
theorem B3068603 : Blo 401768 3068603 := bstep (se 1 (by rfl) ⟨2301452, by rfl⟩ : syracuseStep 3068603 = 4602905) B4602905
theorem B906011 : Blo 401768 906011 := bstep (se 1 (by rfl) ⟨679508, by rfl⟩ : syracuseStep 906011 = 1359017) B1359017
theorem B1529063 : Blo 401768 1529063 := bstep (se 1 (by rfl) ⟨1146797, by rfl⟩ : syracuseStep 1529063 = 2293595) B2293595
theorem B1365497 : Blo 401768 1365497 := bstep (se 2 (by rfl) ⟨512061, by rfl⟩ : syracuseStep 1365497 = 1024123) B1024123
theorem B3069575 : Blo 401768 3069575 := bstep (se 1 (by rfl) ⟨2302181, by rfl⟩ : syracuseStep 3069575 = 4604363) B4604363
theorem B2578063 : Blo 401768 2578063 := bstep (se 1 (by rfl) ⟨1933547, by rfl⟩ : syracuseStep 2578063 = 3867095) B3867095
theorem B1365659 : Blo 401768 1365659 := bstep (se 1 (by rfl) ⟨1024244, by rfl⟩ : syracuseStep 1365659 = 2048489) B2048489
theorem B678503 : Blo 401768 678503 := bstep (se 1 (by rfl) ⟨508877, by rfl⟩ : syracuseStep 678503 = 1017755) B1017755
theorem B8772239 : Blo 401768 8772239 := bstep (se 1 (by rfl) ⟨6579179, by rfl⟩ : syracuseStep 8772239 = 13158359) B13158359
theorem B678793 : Blo 401768 678793 := bstep (se 2 (by rfl) ⟨254547, by rfl⟩ : syracuseStep 678793 = 509095) B509095
theorem B908315 : Blo 401768 908315 := bstep (se 1 (by rfl) ⟨681236, by rfl⟩ : syracuseStep 908315 = 1362473) B1362473
theorem B908513 : Blo 401768 908513 := bstep (se 2 (by rfl) ⟨340692, by rfl⟩ : syracuseStep 908513 = 681385) B681385
theorem B679259 : Blo 401768 679259 := bstep (se 1 (by rfl) ⟨509444, by rfl⟩ : syracuseStep 679259 = 1018889) B1018889
theorem B1727867 : Blo 401768 1727867 := bstep (se 1 (by rfl) ⟨1295900, by rfl⟩ : syracuseStep 1727867 = 2591801) B2591801
theorem B1367549 : Blo 401768 1367549 := bstep (se 3 (by rfl) ⟨256415, by rfl⟩ : syracuseStep 1367549 = 512831) B512831
theorem B2448953 : Blo 401768 2448953 := bstep (se 2 (by rfl) ⟨918357, by rfl⟩ : syracuseStep 2448953 = 1836715) B1836715
theorem B647003 : Blo 401768 647003 := bstep (se 1 (by rfl) ⟨485252, by rfl⟩ : syracuseStep 647003 = 970505) B970505
theorem B680231 : Blo 401768 680231 := bstep (se 1 (by rfl) ⟨510173, by rfl⟩ : syracuseStep 680231 = 1020347) B1020347
theorem B1728809 : Blo 401768 1728809 := bstep (se 2 (by rfl) ⟨648303, by rfl⟩ : syracuseStep 1728809 = 1296607) B1296607
theorem B3433043 : Blo 401768 3433043 := bstep (se 1 (by rfl) ⟨2574782, by rfl⟩ : syracuseStep 3433043 = 5149565) B5149565
theorem B8774243 : Blo 401768 8774243 := bstep (se 1 (by rfl) ⟨6580682, by rfl⟩ : syracuseStep 8774243 = 13161365) B13161365
theorem B909935 : Blo 401768 909935 := bstep (se 1 (by rfl) ⟨682451, by rfl⟩ : syracuseStep 909935 = 1364903) B1364903
theorem B1532753 : Blo 401768 1532753 := bstep (se 2 (by rfl) ⟨574782, by rfl⟩ : syracuseStep 1532753 = 1149565) B1149565
theorem B4613111 : Blo 401768 4613111 := bstep (se 1 (by rfl) ⟨3459833, by rfl⟩ : syracuseStep 4613111 = 6919667) B6919667
theorem B11035705 : Blo 401768 11035705 := bstep (se 2 (by rfl) ⟨4138389, by rfl⟩ : syracuseStep 11035705 = 8276779) B8276779
theorem B910511 : Blo 401768 910511 := bstep (se 1 (by rfl) ⟨682883, by rfl⟩ : syracuseStep 910511 = 1365767) B1365767
theorem B681257 : Blo 401768 681257 := bstep (se 2 (by rfl) ⟨255471, by rfl⟩ : syracuseStep 681257 = 510943) B510943
theorem B452479 : Blo 401768 452479 := bstep (se 1 (by rfl) ⟨339359, by rfl⟩ : syracuseStep 452479 = 678719) B678719
theorem B681979 : Blo 401768 681979 := bstep (se 1 (by rfl) ⟨511484, by rfl⟩ : syracuseStep 681979 = 1022969) B1022969
theorem B911591 : Blo 401768 911591 := bstep (se 1 (by rfl) ⟨683693, by rfl⟩ : syracuseStep 911591 = 1367387) B1367387
theorem B682411 : Blo 401768 682411 := bstep (se 1 (by rfl) ⟨511808, by rfl⟩ : syracuseStep 682411 = 1023617) B1023617
theorem B2485073 : Blo 401768 2485073 := bstep (se 2 (by rfl) ⟨931902, by rfl⟩ : syracuseStep 2485073 = 1863805) B1863805
theorem B912239 : Blo 401768 912239 := bstep (se 1 (by rfl) ⟨684179, by rfl⟩ : syracuseStep 912239 = 1368359) B1368359
theorem B2288513 : Blo 401768 2288513 := bstep (se 2 (by rfl) ⟨858192, by rfl⟩ : syracuseStep 2288513 = 1716385) B1716385
theorem B682951 : Blo 401768 682951 := bstep (se 1 (by rfl) ⟨512213, by rfl⟩ : syracuseStep 682951 = 1024427) B1024427
theorem B912491 : Blo 401768 912491 := bstep (se 1 (by rfl) ⟨684368, by rfl⟩ : syracuseStep 912491 = 1368737) B1368737
theorem B3435641 : Blo 401768 3435641 := bstep (se 2 (by rfl) ⟨1288365, by rfl⟩ : syracuseStep 3435641 = 2576731) B2576731
theorem B912815 : Blo 401768 912815 := bstep (se 1 (by rfl) ⟨684611, by rfl⟩ : syracuseStep 912815 = 1369223) B1369223
theorem B912923 : Blo 401768 912923 := bstep (se 1 (by rfl) ⟨684692, by rfl⟩ : syracuseStep 912923 = 1369385) B1369385
theorem B14708567 : Blo 401768 14708567 := bstep (se 1 (by rfl) ⟨11031425, by rfl⟩ : syracuseStep 14708567 = 22062851) B22062851
theorem B1535867 : Blo 401768 1535867 := bstep (se 1 (by rfl) ⟨1151900, by rfl⟩ : syracuseStep 1535867 = 2303801) B2303801
theorem B454567 : Blo 401768 454567 := bstep (se 1 (by rfl) ⟨340925, by rfl⟩ : syracuseStep 454567 = 681851) B681851
theorem B1732583 : Blo 401768 1732583 := bstep (se 1 (by rfl) ⟨1299437, by rfl⟩ : syracuseStep 1732583 = 2598875) B2598875
theorem B454747 : Blo 401768 454747 := bstep (se 1 (by rfl) ⟨341060, by rfl⟩ : syracuseStep 454747 = 682121) B682121
theorem B3862637 : Blo 401768 3862637 := bstep (se 3 (by rfl) ⟨724244, by rfl⟩ : syracuseStep 3862637 = 1448489) B1448489
theorem B112325039 : Blo 401768 112325039 := bstep (se 1 (by rfl) ⟨84243779, by rfl⟩ : syracuseStep 112325039 = 168487559) B168487559
theorem B18674657 : Blo 401768 18674657 := bstep (se 2 (by rfl) ⟨7002996, by rfl⟩ : syracuseStep 18674657 = 14005993) B14005993
theorem B455935 : Blo 401768 455935 := bstep (se 1 (by rfl) ⟨341951, by rfl⟩ : syracuseStep 455935 = 683903) B683903
theorem B1471817 : Blo 401768 1471817 := bstep (se 2 (by rfl) ⟨551931, by rfl⟩ : syracuseStep 1471817 = 1103863) B1103863
theorem B17036867 : Blo 401768 17036867 := bstep (se 1 (by rfl) ⟨12777650, by rfl⟩ : syracuseStep 17036867 = 25555301) B25555301
theorem B1537643 : Blo 401768 1537643 := bstep (se 1 (by rfl) ⟨1153232, by rfl⟩ : syracuseStep 1537643 = 2306465) B2306465
theorem B1537811 : Blo 401768 1537811 := bstep (se 1 (by rfl) ⟨1153358, by rfl⟩ : syracuseStep 1537811 = 2306717) B2306717
theorem B817631 : Blo 401768 817631 := bstep (se 1 (by rfl) ⟨613223, by rfl⟩ : syracuseStep 817631 = 1226447) B1226447
theorem B818345 : Blo 401768 818345 := bstep (se 2 (by rfl) ⟨306879, by rfl⟩ : syracuseStep 818345 = 613759) B613759
theorem B1146707 : Blo 401768 1146707 := bstep (se 1 (by rfl) ⟨860030, by rfl⟩ : syracuseStep 1146707 = 1720061) B1720061
theorem B1867657 : Blo 401768 1867657 := bstep (se 2 (by rfl) ⟨700371, by rfl⟩ : syracuseStep 1867657 = 1400743) B1400743
theorem B8749403 : Blo 401768 8749403 := bstep (se 1 (by rfl) ⟨6562052, by rfl⟩ : syracuseStep 8749403 = 13124105) B13124105
theorem B16646975 : Blo 401768 16646975 := bstep (se 1 (by rfl) ⟨12485231, by rfl⟩ : syracuseStep 16646975 = 24970463) B24970463
theorem B6915293 : Blo 401768 6915293 := bstep (se 3 (by rfl) ⟨1296617, by rfl⟩ : syracuseStep 6915293 = 2593235) B2593235
theorem B14714273 : Blo 401768 14714273 := bstep (se 2 (by rfl) ⟨5517852, by rfl⟩ : syracuseStep 14714273 = 11035705) B11035705
theorem B1967723 : Blo 401768 1967723 := bstep (se 1 (by rfl) ⟨1475792, by rfl⟩ : syracuseStep 1967723 = 2951585) B2951585
theorem B4261585 : Blo 401768 4261585 := bstep (se 2 (by rfl) ⟨1598094, by rfl⟩ : syracuseStep 4261585 = 3196189) B3196189
theorem B2296259 : Blo 401768 2296259 := bstep (se 1 (by rfl) ⟨1722194, by rfl⟩ : syracuseStep 2296259 = 3444389) B3444389
theorem B2034719 : Blo 401768 2034719 := bstep (se 1 (by rfl) ⟨1526039, by rfl⟩ : syracuseStep 2034719 = 3052079) B3052079
theorem B1019375 : Blo 401768 1019375 := bstep (se 1 (by rfl) ⟨764531, by rfl⟩ : syracuseStep 1019375 = 1529063) B1529063
theorem B5181245 : Blo 401768 5181245 := bstep (se 3 (by rfl) ⟨971483, by rfl⟩ : syracuseStep 5181245 = 1942967) B1942967
theorem B2593417 : Blo 401768 2593417 := bstep (se 2 (by rfl) ⟨972531, by rfl⟩ : syracuseStep 2593417 = 1945063) B1945063
theorem B1151911 : Blo 401768 1151911 := bstep (se 1 (by rfl) ⟨863933, by rfl⟩ : syracuseStep 1151911 = 1727867) B1727867
theorem B431335 : Blo 401768 431335 := bstep (se 1 (by rfl) ⟨323501, by rfl⟩ : syracuseStep 431335 = 647003) B647003
theorem B1949701475 : Blo 401768 1949701475 := bstep (se 1 (by rfl) ⟨1462276106, by rfl⟩ : syracuseStep 1949701475 = 2924552213) B2924552213
theorem B1152539 : Blo 401768 1152539 := bstep (se 1 (by rfl) ⟨864404, by rfl⟩ : syracuseStep 1152539 = 1728809) B1728809
theorem B1644263 : Blo 401768 1644263 := bstep (se 1 (by rfl) ⟨1233197, by rfl⟩ : syracuseStep 1644263 = 2466395) B2466395
theorem B1021673 : Blo 401768 1021673 := bstep (se 2 (by rfl) ⟨383127, by rfl⟩ : syracuseStep 1021673 = 766255) B766255
theorem B1021835 : Blo 401768 1021835 := bstep (se 1 (by rfl) ⟨766376, by rfl⟩ : syracuseStep 1021835 = 1532753) B1532753
theorem B2333225 : Blo 401768 2333225 := bstep (se 2 (by rfl) ⟨874959, by rfl⟩ : syracuseStep 2333225 = 1749919) B1749919
theorem B6626861 : Blo 401768 6626861 := bstep (se 3 (by rfl) ⟨1242536, by rfl⟩ : syracuseStep 6626861 = 2485073) B2485073
theorem B9805711 : Blo 401768 9805711 := bstep (se 1 (by rfl) ⟨7354283, by rfl⟩ : syracuseStep 9805711 = 14708567) B14708567
theorem B4595615 : Blo 401768 4595615 := bstep (se 1 (by rfl) ⟨3446711, by rfl⟩ : syracuseStep 4595615 = 6893423) B6893423
theorem B1023911 : Blo 401768 1023911 := bstep (se 1 (by rfl) ⟨767933, by rfl⟩ : syracuseStep 1023911 = 1535867) B1535867
theorem B1155055 : Blo 401768 1155055 := bstep (se 1 (by rfl) ⟨866291, by rfl⟩ : syracuseStep 1155055 = 1732583) B1732583
theorem B1024073 : Blo 401768 1024073 := bstep (se 2 (by rfl) ⟨384027, by rfl⟩ : syracuseStep 1024073 = 768055) B768055
theorem B2039903 : Blo 401768 2039903 := bstep (se 1 (by rfl) ⟨1529927, by rfl⟩ : syracuseStep 2039903 = 3059855) B3059855
theorem B2302091 : Blo 401768 2302091 := bstep (se 1 (by rfl) ⟨1726568, by rfl⟩ : syracuseStep 2302091 = 3453137) B3453137
theorem B74883359 : Blo 401768 74883359 := bstep (se 1 (by rfl) ⟨56162519, by rfl⟩ : syracuseStep 74883359 = 112325039) B112325039
theorem B5186267 : Blo 401768 5186267 := bstep (se 1 (by rfl) ⟨3889700, by rfl⟩ : syracuseStep 5186267 = 7779401) B7779401
theorem B402239 : Blo 401768 402239 := bstep (se 1 (by rfl) ⟨301679, by rfl⟩ : syracuseStep 402239 = 603359) B603359
theorem B2106271 : Blo 401768 2106271 := bstep (se 1 (by rfl) ⟨1579703, by rfl⟩ : syracuseStep 2106271 = 3159407) B3159407
theorem B1025095 : Blo 401768 1025095 := bstep (se 1 (by rfl) ⟨768821, by rfl⟩ : syracuseStep 1025095 = 1537643) B1537643
theorem B402559 : Blo 401768 402559 := bstep (se 1 (by rfl) ⟨301919, by rfl⟩ : syracuseStep 402559 = 603839) B603839
theorem B1025207 : Blo 401768 1025207 := bstep (se 1 (by rfl) ⟨768905, by rfl⟩ : syracuseStep 1025207 = 1537811) B1537811
theorem B402751 : Blo 401768 402751 := bstep (se 1 (by rfl) ⟨302063, by rfl⟩ : syracuseStep 402751 = 604127) B604127
theorem B402791 : Blo 401768 402791 := bstep (se 1 (by rfl) ⟨302093, by rfl⟩ : syracuseStep 402791 = 604187) B604187
theorem B402911 : Blo 401768 402911 := bstep (se 1 (by rfl) ⟨302183, by rfl⟩ : syracuseStep 402911 = 604367) B604367
theorem B402919 : Blo 401768 402919 := bstep (se 1 (by rfl) ⟨302189, by rfl⟩ : syracuseStep 402919 = 604379) B604379
theorem B403047 : Blo 401768 403047 := bstep (se 1 (by rfl) ⟨302285, by rfl⟩ : syracuseStep 403047 = 604571) B604571
theorem B6924041 : Blo 401768 6924041 := bstep (se 2 (by rfl) ⟨2596515, by rfl⟩ : syracuseStep 6924041 = 5193031) B5193031
theorem B403327 : Blo 401768 403327 := bstep (se 1 (by rfl) ⟨302495, by rfl⟩ : syracuseStep 403327 = 604991) B604991
theorem B403359 : Blo 401768 403359 := bstep (se 1 (by rfl) ⟨302519, by rfl⟩ : syracuseStep 403359 = 605039) B605039
theorem B1026017 : Blo 401768 1026017 := bstep (se 2 (by rfl) ⟨384756, by rfl⟩ : syracuseStep 1026017 = 769513) B769513
theorem B403519 : Blo 401768 403519 := bstep (se 1 (by rfl) ⟨302639, by rfl⟩ : syracuseStep 403519 = 605279) B605279
theorem B403559 : Blo 401768 403559 := bstep (se 1 (by rfl) ⟨302669, by rfl⟩ : syracuseStep 403559 = 605339) B605339
theorem B764471 : Blo 401768 764471 := bstep (se 1 (by rfl) ⟨573353, by rfl⟩ : syracuseStep 764471 = 1146707) B1146707
theorem B5253907 : Blo 401768 5253907 := bstep (se 1 (by rfl) ⟨3940430, by rfl⟩ : syracuseStep 5253907 = 7880861) B7880861
theorem B4434713 : Blo 401768 4434713 := bstep (se 2 (by rfl) ⟨1663017, by rfl⟩ : syracuseStep 4434713 = 3326035) B3326035
theorem B2305691 : Blo 401768 2305691 := bstep (se 1 (by rfl) ⟨1729268, by rfl⟩ : syracuseStep 2305691 = 3458537) B3458537
theorem B405595 : Blo 401768 405595 := bstep (se 1 (by rfl) ⟨304196, by rfl⟩ : syracuseStep 405595 = 608393) B608393
theorem B1717001 : Blo 401768 1717001 := bstep (se 2 (by rfl) ⟨643875, by rfl⟩ : syracuseStep 1717001 = 1287751) B1287751
theorem B603305 : Blo 401768 603305 := bstep (se 2 (by rfl) ⟨226239, by rfl⟩ : syracuseStep 603305 = 452479) B452479
theorem B4895963 : Blo 401768 4895963 := bstep (se 1 (by rfl) ⟨3671972, by rfl⟩ : syracuseStep 4895963 = 7343945) B7343945
theorem B6207151 : Blo 401768 6207151 := bstep (se 1 (by rfl) ⟨4655363, by rfl⟩ : syracuseStep 6207151 = 9310727) B9310727
theorem B2045735 : Blo 401768 2045735 := bstep (se 1 (by rfl) ⟨1534301, by rfl⟩ : syracuseStep 2045735 = 3068603) B3068603
theorem B604007 : Blo 401768 604007 := bstep (se 1 (by rfl) ⟨453005, by rfl⟩ : syracuseStep 604007 = 906011) B906011
theorem B2046383 : Blo 401768 2046383 := bstep (se 1 (by rfl) ⟨1534787, by rfl⟩ : syracuseStep 2046383 = 3069575) B3069575
theorem B1358315 : Blo 401768 1358315 := bstep (se 1 (by rfl) ⟨1018736, by rfl⟩ : syracuseStep 1358315 = 2037473) B2037473
theorem B1292927 : Blo 401768 1292927 := bstep (se 1 (by rfl) ⟨969695, by rfl⟩ : syracuseStep 1292927 = 1939391) B1939391
theorem B965641 : Blo 401768 965641 := bstep (se 2 (by rfl) ⟨362115, by rfl⟩ : syracuseStep 965641 = 724231) B724231
theorem B1293337 : Blo 401768 1293337 := bstep (se 2 (by rfl) ⟨485001, by rfl⟩ : syracuseStep 1293337 = 970003) B970003
theorem B5848159 : Blo 401768 5848159 := bstep (se 1 (by rfl) ⟨4386119, by rfl⟩ : syracuseStep 5848159 = 8772239) B8772239
theorem B605543 : Blo 401768 605543 := bstep (se 1 (by rfl) ⟨454157, by rfl⟩ : syracuseStep 605543 = 908315) B908315
theorem B605675 : Blo 401768 605675 := bstep (se 1 (by rfl) ⟨454256, by rfl⟩ : syracuseStep 605675 = 908513) B908513
theorem B1359611 : Blo 401768 1359611 := bstep (se 1 (by rfl) ⟨1019708, by rfl⟩ : syracuseStep 1359611 = 2039417) B2039417
theorem B606089 : Blo 401768 606089 := bstep (se 2 (by rfl) ⟨227283, by rfl⟩ : syracuseStep 606089 = 454567) B454567
theorem B769961 : Blo 401768 769961 := bstep (se 2 (by rfl) ⟨288735, by rfl⟩ : syracuseStep 769961 = 577471) B577471
theorem B606329 : Blo 401768 606329 := bstep (se 2 (by rfl) ⟨227373, by rfl⟩ : syracuseStep 606329 = 454747) B454747
theorem B5849495 : Blo 401768 5849495 := bstep (se 1 (by rfl) ⟨4387121, by rfl⟩ : syracuseStep 5849495 = 8774243) B8774243
theorem B606623 : Blo 401768 606623 := bstep (se 1 (by rfl) ⟨454967, by rfl⟩ : syracuseStep 606623 = 909935) B909935
theorem B607007 : Blo 401768 607007 := bstep (se 1 (by rfl) ⟨455255, by rfl⟩ : syracuseStep 607007 = 910511) B910511
theorem B508999 : Blo 401768 508999 := bstep (se 1 (by rfl) ⟨381749, by rfl⟩ : syracuseStep 508999 = 763499) B763499
theorem B574555 : Blo 401768 574555 := bstep (se 1 (by rfl) ⟨430916, by rfl⟩ : syracuseStep 574555 = 861833) B861833
theorem B607727 : Blo 401768 607727 := bstep (se 1 (by rfl) ⟨455795, by rfl⟩ : syracuseStep 607727 = 911591) B911591
theorem B607913 : Blo 401768 607913 := bstep (se 2 (by rfl) ⟨227967, by rfl⟩ : syracuseStep 607913 = 455935) B455935
theorem B1525661 : Blo 401768 1525661 := bstep (se 3 (by rfl) ⟨286061, by rfl⟩ : syracuseStep 1525661 = 572123) B572123
theorem B608159 : Blo 401768 608159 := bstep (se 1 (by rfl) ⟨456119, by rfl⟩ : syracuseStep 608159 = 912239) B912239
theorem B1525675 : Blo 401768 1525675 := bstep (se 1 (by rfl) ⟨1144256, by rfl⟩ : syracuseStep 1525675 = 2288513) B2288513
theorem B608327 : Blo 401768 608327 := bstep (se 1 (by rfl) ⟨456245, by rfl⟩ : syracuseStep 608327 = 912491) B912491
theorem B1362203 : Blo 401768 1362203 := bstep (se 1 (by rfl) ⟨1021652, by rfl⟩ : syracuseStep 1362203 = 2043305) B2043305
theorem B608543 : Blo 401768 608543 := bstep (se 1 (by rfl) ⟨456407, by rfl⟩ : syracuseStep 608543 = 912815) B912815
theorem B608615 : Blo 401768 608615 := bstep (se 1 (by rfl) ⟨456461, by rfl⟩ : syracuseStep 608615 = 912923) B912923
theorem B7752185 : Blo 401768 7752185 := bstep (se 2 (by rfl) ⟨2907069, by rfl⟩ : syracuseStep 7752185 = 5814139) B5814139
theorem B2575091 : Blo 401768 2575091 := bstep (se 1 (by rfl) ⟨1931318, by rfl⟩ : syracuseStep 2575091 = 3862637) B3862637
theorem B31771541 : Blo 401768 31771541 := bstep (se 6 (by rfl) ⟨744645, by rfl⟩ : syracuseStep 31771541 = 1489291) B1489291
theorem B511535 : Blo 401768 511535 := bstep (se 1 (by rfl) ⟨383651, by rfl⟩ : syracuseStep 511535 = 767303) B767303
theorem B11357911 : Blo 401768 11357911 := bstep (se 1 (by rfl) ⟨8518433, by rfl⟩ : syracuseStep 11357911 = 17036867) B17036867
theorem B905057 : Blo 401768 905057 := bstep (se 2 (by rfl) ⟨339396, by rfl⟩ : syracuseStep 905057 = 678793) B678793
theorem B905399 : Blo 401768 905399 := bstep (se 1 (by rfl) ⟨679049, by rfl⟩ : syracuseStep 905399 = 1358099) B1358099
theorem B905471 : Blo 401768 905471 := bstep (se 1 (by rfl) ⟨679103, by rfl⟩ : syracuseStep 905471 = 1358207) B1358207
theorem B545087 : Blo 401768 545087 := bstep (se 1 (by rfl) ⟨408815, by rfl⟩ : syracuseStep 545087 = 817631) B817631
theorem B1364471 : Blo 401768 1364471 := bstep (se 1 (by rfl) ⟨1023353, by rfl⟩ : syracuseStep 1364471 = 2046707) B2046707
theorem B545563 : Blo 401768 545563 := bstep (se 1 (by rfl) ⟨409172, by rfl⟩ : syracuseStep 545563 = 818345) B818345
theorem B906047 : Blo 401768 906047 := bstep (se 1 (by rfl) ⟨679535, by rfl⟩ : syracuseStep 906047 = 1359071) B1359071
theorem B1366199 : Blo 401768 1366199 := bstep (se 1 (by rfl) ⟨1024649, by rfl⟩ : syracuseStep 1366199 = 2049299) B2049299
theorem B2578655 : Blo 401768 2578655 := bstep (se 1 (by rfl) ⟨1933991, by rfl⟩ : syracuseStep 2578655 = 3867983) B3867983
theorem B2185451 : Blo 401768 2185451 := bstep (se 1 (by rfl) ⟨1639088, by rfl⟩ : syracuseStep 2185451 = 3278177) B3278177
theorem B908027 : Blo 401768 908027 := bstep (se 1 (by rfl) ⟨681020, by rfl⟩ : syracuseStep 908027 = 1362041) B1362041
theorem B580351 : Blo 401768 580351 := bstep (se 1 (by rfl) ⟨435263, by rfl⟩ : syracuseStep 580351 = 870527) B870527
theorem B4381451 : Blo 401768 4381451 := bstep (se 1 (by rfl) ⟨3286088, by rfl⟩ : syracuseStep 4381451 = 6572177) B6572177
theorem B678847 : Blo 401768 678847 := bstep (se 1 (by rfl) ⟨509135, by rfl⟩ : syracuseStep 678847 = 1018271) B1018271
theorem B974099 : Blo 401768 974099 := bstep (se 1 (by rfl) ⟨730574, by rfl⟩ : syracuseStep 974099 = 1461149) B1461149
theorem B909305 : Blo 401768 909305 := bstep (se 2 (by rfl) ⟨340989, by rfl⟩ : syracuseStep 909305 = 681979) B681979
theorem B909881 : Blo 401768 909881 := bstep (se 2 (by rfl) ⟨341205, by rfl⟩ : syracuseStep 909881 = 682411) B682411
theorem B2908831 : Blo 401768 2908831 := bstep (se 1 (by rfl) ⟨2181623, by rfl⟩ : syracuseStep 2908831 = 4363247) B4363247
theorem B3924845 : Blo 401768 3924845 := bstep (se 3 (by rfl) ⟨735908, by rfl⟩ : syracuseStep 3924845 = 1471817) B1471817
theorem B910331 : Blo 401768 910331 := bstep (se 1 (by rfl) ⟨682748, by rfl⟩ : syracuseStep 910331 = 1365497) B1365497
theorem B910439 : Blo 401768 910439 := bstep (se 1 (by rfl) ⟨682829, by rfl⟩ : syracuseStep 910439 = 1365659) B1365659
theorem B3695825 : Blo 401768 3695825 := bstep (se 2 (by rfl) ⟨1385934, by rfl⟩ : syracuseStep 3695825 = 2771869) B2771869
theorem B910601 : Blo 401768 910601 := bstep (se 2 (by rfl) ⟨341475, by rfl⟩ : syracuseStep 910601 = 682951) B682951
theorem B681527 : Blo 401768 681527 := bstep (se 1 (by rfl) ⟨511145, by rfl⟩ : syracuseStep 681527 = 1022291) B1022291
theorem B452335 : Blo 401768 452335 := bstep (se 1 (by rfl) ⟨339251, by rfl⟩ : syracuseStep 452335 = 678503) B678503
theorem B1730585 : Blo 401768 1730585 := bstep (se 2 (by rfl) ⟨648969, by rfl⟩ : syracuseStep 1730585 = 1297939) B1297939
theorem B3434683 : Blo 401768 3434683 := bstep (se 1 (by rfl) ⟨2576012, by rfl⟩ : syracuseStep 3434683 = 5152025) B5152025
theorem B452839 : Blo 401768 452839 := bstep (se 1 (by rfl) ⟨339629, by rfl⟩ : syracuseStep 452839 = 679259) B679259
theorem B911699 : Blo 401768 911699 := bstep (se 1 (by rfl) ⟨683774, by rfl⟩ : syracuseStep 911699 = 1367549) B1367549
theorem B1632635 : Blo 401768 1632635 := bstep (se 1 (by rfl) ⟨1224476, by rfl⟩ : syracuseStep 1632635 = 2448953) B2448953
theorem B1534697 : Blo 401768 1534697 := bstep (se 2 (by rfl) ⟨575511, by rfl⟩ : syracuseStep 1534697 = 1151023) B1151023
theorem B486175 : Blo 401768 486175 := bstep (se 1 (by rfl) ⟨364631, by rfl⟩ : syracuseStep 486175 = 729263) B729263
theorem B453487 : Blo 401768 453487 := bstep (se 1 (by rfl) ⟨340115, by rfl⟩ : syracuseStep 453487 = 680231) B680231
theorem B2288695 : Blo 401768 2288695 := bstep (se 1 (by rfl) ⟨1716521, by rfl⟩ : syracuseStep 2288695 = 3433043) B3433043
theorem B683113 : Blo 401768 683113 := bstep (se 2 (by rfl) ⟨256167, by rfl⟩ : syracuseStep 683113 = 512335) B512335
theorem B7367867 : Blo 401768 7367867 := bstep (se 1 (by rfl) ⟨5525900, by rfl⟩ : syracuseStep 7367867 = 11051801) B11051801
theorem B3828959 : Blo 401768 3828959 := bstep (se 1 (by rfl) ⟨2871719, by rfl⟩ : syracuseStep 3828959 = 5743439) B5743439
theorem B3075407 : Blo 401768 3075407 := bstep (se 1 (by rfl) ⟨2306555, by rfl⟩ : syracuseStep 3075407 = 4613111) B4613111
theorem B3599777 : Blo 401768 3599777 := bstep (se 2 (by rfl) ⟨1349916, by rfl⟩ : syracuseStep 3599777 = 2699833) B2699833
theorem B454171 : Blo 401768 454171 := bstep (se 1 (by rfl) ⟨340628, by rfl⟩ : syracuseStep 454171 = 681257) B681257
theorem B1732823 : Blo 401768 1732823 := bstep (se 1 (by rfl) ⟨1299617, by rfl⟩ : syracuseStep 1732823 = 2599235) B2599235
theorem B2290427 : Blo 401768 2290427 := bstep (se 1 (by rfl) ⟨1717820, by rfl⟩ : syracuseStep 2290427 = 3435641) B3435641
theorem B3437417 : Blo 401768 3437417 := bstep (se 2 (by rfl) ⟨1289031, by rfl⟩ : syracuseStep 3437417 = 2578063) B2578063
theorem B1865423 : Blo 401768 1865423 := bstep (se 1 (by rfl) ⟨1399067, by rfl⟩ : syracuseStep 1865423 = 2798135) B2798135
theorem B12449771 : Blo 401768 12449771 := bstep (se 1 (by rfl) ⟨9337328, by rfl⟩ : syracuseStep 12449771 = 18674657) B18674657
theorem B1145191 : Blo 401768 1145191 := bstep (se 1 (by rfl) ⟨858893, by rfl⟩ : syracuseStep 1145191 = 1717787) B1717787
theorem B2490209 : Blo 401768 2490209 := bstep (se 2 (by rfl) ⟨933828, by rfl⟩ : syracuseStep 2490209 = 1867657) B1867657
theorem B5832935 : Blo 401768 5832935 := bstep (se 1 (by rfl) ⟨4374701, by rfl⟩ : syracuseStep 5832935 = 8749403) B8749403
theorem B3899663 : Blo 401768 3899663 := bstep (se 1 (by rfl) ⟨2924747, by rfl⟩ : syracuseStep 3899663 = 5849495) B5849495
theorem B1311815 : Blo 401768 1311815 := bstep (se 1 (by rfl) ⟨983861, by rfl⟩ : syracuseStep 1311815 = 1967723) B1967723
theorem B1017107 : Blo 401768 1017107 := bstep (se 1 (by rfl) ⟨762830, by rfl⟩ : syracuseStep 1017107 = 1525661) B1525661
theorem B2034233 : Blo 401768 2034233 := bstep (se 2 (by rfl) ⟨762837, by rfl⟩ : syracuseStep 2034233 = 1525675) B1525675
theorem B5199203933 : Blo 401768 5199203933 := bstep (se 3 (by rfl) ⟨974850737, by rfl⟩ : syracuseStep 5199203933 = 1949701475) B1949701475
theorem B3051593 : Blo 401768 3051593 := bstep (se 2 (by rfl) ⟨1144347, by rfl⟩ : syracuseStep 3051593 = 2288695) B2288695
theorem B2920967 : Blo 401768 2920967 := bstep (se 1 (by rfl) ⟨2190725, by rfl⟩ : syracuseStep 2920967 = 4381451) B4381451
theorem B15143881 : Blo 401768 15143881 := bstep (se 2 (by rfl) ⟨5678955, by rfl⟩ : syracuseStep 15143881 = 11357911) B11357911
theorem B727417 : Blo 401768 727417 := bstep (se 2 (by rfl) ⟨272781, by rfl⟩ : syracuseStep 727417 = 545563) B545563
theorem B1153723 : Blo 401768 1153723 := bstep (se 1 (by rfl) ⟨865292, by rfl⟩ : syracuseStep 1153723 = 1730585) B1730585
theorem B1088423 : Blo 401768 1088423 := bstep (se 1 (by rfl) ⟨816317, by rfl⟩ : syracuseStep 1088423 = 1632635) B1632635
theorem B3447805 : Blo 401768 3447805 := bstep (se 3 (by rfl) ⟨646463, by rfl⟩ : syracuseStep 3447805 = 1292927) B1292927
theorem B1023131 : Blo 401768 1023131 := bstep (se 1 (by rfl) ⟨767348, by rfl⟩ : syracuseStep 1023131 = 1534697) B1534697
theorem B2956475 : Blo 401768 2956475 := bstep (se 1 (by rfl) ⟨2217356, by rfl⟩ : syracuseStep 2956475 = 4434713) B4434713
theorem B2399851 : Blo 401768 2399851 := bstep (se 1 (by rfl) ⟨1799888, by rfl⟩ : syracuseStep 2399851 = 3599777) B3599777
theorem B1155215 : Blo 401768 1155215 := bstep (se 1 (by rfl) ⟨866411, by rfl⟩ : syracuseStep 1155215 = 1732823) B1732823
theorem B402203 : Blo 401768 402203 := bstep (se 1 (by rfl) ⟨301652, by rfl⟩ : syracuseStep 402203 = 603305) B603305
theorem B402671 : Blo 401768 402671 := bstep (se 1 (by rfl) ⟨302003, by rfl⟩ : syracuseStep 402671 = 604007) B604007
theorem B8299847 : Blo 401768 8299847 := bstep (se 1 (by rfl) ⟨6224885, by rfl⟩ : syracuseStep 8299847 = 12449771) B12449771
theorem B1287521 : Blo 401768 1287521 := bstep (se 2 (by rfl) ⟨482820, by rfl⟩ : syracuseStep 1287521 = 965641) B965641
theorem B403695 : Blo 401768 403695 := bstep (se 1 (by rfl) ⟨302771, by rfl⟩ : syracuseStep 403695 = 605543) B605543
theorem B403783 : Blo 401768 403783 := bstep (se 1 (by rfl) ⟨302837, by rfl⟩ : syracuseStep 403783 = 605675) B605675
theorem B404059 : Blo 401768 404059 := bstep (se 1 (by rfl) ⟨303044, by rfl⟩ : syracuseStep 404059 = 606089) B606089
theorem B404219 : Blo 401768 404219 := bstep (se 1 (by rfl) ⟨303164, by rfl⟩ : syracuseStep 404219 = 606329) B606329
theorem B404415 : Blo 401768 404415 := bstep (se 1 (by rfl) ⟨303311, by rfl⟩ : syracuseStep 404415 = 606623) B606623
theorem B404671 : Blo 401768 404671 := bstep (se 1 (by rfl) ⟨303503, by rfl⟩ : syracuseStep 404671 = 607007) B607007
theorem B1453565 : Blo 401768 1453565 := bstep (se 3 (by rfl) ⟨272543, by rfl⟩ : syracuseStep 1453565 = 545087) B545087
theorem B3878441 : Blo 401768 3878441 := bstep (se 2 (by rfl) ⟨1454415, by rfl⟩ : syracuseStep 3878441 = 2908831) B2908831
theorem B9809515 : Blo 401768 9809515 := bstep (se 1 (by rfl) ⟨7357136, by rfl⟩ : syracuseStep 9809515 = 14714273) B14714273
theorem B405151 : Blo 401768 405151 := bstep (se 1 (by rfl) ⟨303863, by rfl⟩ : syracuseStep 405151 = 607727) B607727
theorem B405275 : Blo 401768 405275 := bstep (se 1 (by rfl) ⟨303956, by rfl⟩ : syracuseStep 405275 = 607913) B607913
theorem B405439 : Blo 401768 405439 := bstep (se 1 (by rfl) ⟨304079, by rfl⟩ : syracuseStep 405439 = 608159) B608159
theorem B405551 : Blo 401768 405551 := bstep (se 1 (by rfl) ⟨304163, by rfl⟩ : syracuseStep 405551 = 608327) B608327
theorem B766073 : Blo 401768 766073 := bstep (se 2 (by rfl) ⟨287277, by rfl⟩ : syracuseStep 766073 = 574555) B574555
theorem B405695 : Blo 401768 405695 := bstep (se 1 (by rfl) ⟨304271, by rfl⟩ : syracuseStep 405695 = 608543) B608543
theorem B405743 : Blo 401768 405743 := bstep (se 1 (by rfl) ⟨304307, by rfl⟩ : syracuseStep 405743 = 608615) B608615
theorem B1716727 : Blo 401768 1716727 := bstep (se 1 (by rfl) ⟨1287545, by rfl⟩ : syracuseStep 1716727 = 2575091) B2575091
theorem B21181027 : Blo 401768 21181027 := bstep (se 1 (by rfl) ⟨15885770, by rfl⟩ : syracuseStep 21181027 = 31771541) B31771541
theorem B1356479 : Blo 401768 1356479 := bstep (se 1 (by rfl) ⟨1017359, by rfl⟩ : syracuseStep 1356479 = 2034719) B2034719
theorem B5682113 : Blo 401768 5682113 := bstep (se 2 (by rfl) ⟨2130792, by rfl⟩ : syracuseStep 5682113 = 4261585) B4261585
theorem B603113 : Blo 401768 603113 := bstep (se 2 (by rfl) ⟨226167, by rfl⟩ : syracuseStep 603113 = 452335) B452335
theorem B3454163 : Blo 401768 3454163 := bstep (se 1 (by rfl) ⟨2590622, by rfl⟩ : syracuseStep 3454163 = 5181245) B5181245
theorem B603371 : Blo 401768 603371 := bstep (se 1 (by rfl) ⟨452528, by rfl⟩ : syracuseStep 603371 = 905057) B905057
theorem B603599 : Blo 401768 603599 := bstep (se 1 (by rfl) ⟨452699, by rfl⟩ : syracuseStep 603599 = 905399) B905399
theorem B603647 : Blo 401768 603647 := bstep (se 1 (by rfl) ⟨452735, by rfl⟩ : syracuseStep 603647 = 905471) B905471
theorem B603785 : Blo 401768 603785 := bstep (se 2 (by rfl) ⟨226419, by rfl⟩ : syracuseStep 603785 = 452839) B452839
theorem B604031 : Blo 401768 604031 := bstep (se 1 (by rfl) ⟨453023, by rfl⟩ : syracuseStep 604031 = 906047) B906047
theorem B768359 : Blo 401768 768359 := bstep (se 1 (by rfl) ⟨576269, by rfl⟩ : syracuseStep 768359 = 1152539) B1152539
theorem B604649 : Blo 401768 604649 := bstep (se 2 (by rfl) ⟨226743, by rfl⟩ : syracuseStep 604649 = 453487) B453487
theorem B1096175 : Blo 401768 1096175 := bstep (se 1 (by rfl) ⟨822131, by rfl⟩ : syracuseStep 1096175 = 1644263) B1644263
theorem B1719103 : Blo 401768 1719103 := bstep (se 1 (by rfl) ⟨1289327, by rfl⟩ : syracuseStep 1719103 = 2578655) B2578655
theorem B1456967 : Blo 401768 1456967 := bstep (se 1 (by rfl) ⟨1092725, by rfl⟩ : syracuseStep 1456967 = 2185451) B2185451
theorem B605351 : Blo 401768 605351 := bstep (se 1 (by rfl) ⟨454013, by rfl⟩ : syracuseStep 605351 = 908027) B908027
theorem B605561 : Blo 401768 605561 := bstep (se 2 (by rfl) ⟨227085, by rfl⟩ : syracuseStep 605561 = 454171) B454171
theorem B3063743 : Blo 401768 3063743 := bstep (se 1 (by rfl) ⟨2297807, by rfl⟩ : syracuseStep 3063743 = 4595615) B4595615
theorem B606203 : Blo 401768 606203 := bstep (se 1 (by rfl) ⟨454652, by rfl⟩ : syracuseStep 606203 = 909305) B909305
theorem B1359935 : Blo 401768 1359935 := bstep (se 1 (by rfl) ⟨1019951, by rfl⟩ : syracuseStep 1359935 = 2039903) B2039903
theorem B6897797 : Blo 401768 6897797 := bstep (se 4 (by rfl) ⟨646668, by rfl⟩ : syracuseStep 6897797 = 1293337) B1293337
theorem B49922239 : Blo 401768 49922239 := bstep (se 1 (by rfl) ⟨37441679, by rfl⟩ : syracuseStep 49922239 = 74883359) B74883359
theorem B606587 : Blo 401768 606587 := bstep (se 1 (by rfl) ⟨454940, by rfl⟩ : syracuseStep 606587 = 909881) B909881
theorem B3457511 : Blo 401768 3457511 := bstep (se 1 (by rfl) ⟨2593133, by rfl⟩ : syracuseStep 3457511 = 5186267) B5186267
theorem B606887 : Blo 401768 606887 := bstep (se 1 (by rfl) ⟨455165, by rfl⟩ : syracuseStep 606887 = 910331) B910331
theorem B606959 : Blo 401768 606959 := bstep (se 1 (by rfl) ⟨455219, by rfl⟩ : syracuseStep 606959 = 910439) B910439
theorem B607067 : Blo 401768 607067 := bstep (se 1 (by rfl) ⟨455300, by rfl⟩ : syracuseStep 607067 = 910601) B910601
theorem B3457889 : Blo 401768 3457889 := bstep (se 2 (by rfl) ⟨1296708, by rfl⟩ : syracuseStep 3457889 = 2593417) B2593417
theorem B607799 : Blo 401768 607799 := bstep (se 1 (by rfl) ⟨455849, by rfl⟩ : syracuseStep 607799 = 911699) B911699
theorem B575113 : Blo 401768 575113 := bstep (se 2 (by rfl) ⟨215667, by rfl⟩ : syracuseStep 575113 = 431335) B431335
theorem B509647 : Blo 401768 509647 := bstep (se 1 (by rfl) ⟨382235, by rfl⟩ : syracuseStep 509647 = 764471) B764471
theorem B2050271 : Blo 401768 2050271 := bstep (se 1 (by rfl) ⟨1537703, by rfl⟩ : syracuseStep 2050271 = 3075407) B3075407
theorem B8276201 : Blo 401768 8276201 := bstep (se 2 (by rfl) ⟨3103575, by rfl⟩ : syracuseStep 8276201 = 6207151) B6207151
theorem B1526921 : Blo 401768 1526921 := bstep (se 2 (by rfl) ⟨572595, by rfl⟩ : syracuseStep 1526921 = 1145191) B1145191
theorem B1526951 : Blo 401768 1526951 := bstep (se 1 (by rfl) ⟨1145213, by rfl⟩ : syracuseStep 1526951 = 2290427) B2290427
theorem B3263975 : Blo 401768 3263975 := bstep (se 1 (by rfl) ⟨2447981, by rfl⟩ : syracuseStep 3263975 = 4895963) B4895963
theorem B773801 : Blo 401768 773801 := bstep (se 2 (by rfl) ⟨290175, by rfl⟩ : syracuseStep 773801 = 580351) B580351
theorem B1363823 : Blo 401768 1363823 := bstep (se 1 (by rfl) ⟨1022867, by rfl⟩ : syracuseStep 1363823 = 2045735) B2045735
theorem B905129 : Blo 401768 905129 := bstep (se 2 (by rfl) ⟨339423, by rfl⟩ : syracuseStep 905129 = 678847) B678847
theorem B1364093 : Blo 401768 1364093 := bstep (se 3 (by rfl) ⟨255767, by rfl⟩ : syracuseStep 1364093 = 511535) B511535
theorem B1364255 : Blo 401768 1364255 := bstep (se 1 (by rfl) ⟨1023191, by rfl⟩ : syracuseStep 1364255 = 2046383) B2046383
theorem B905543 : Blo 401768 905543 := bstep (se 1 (by rfl) ⟨679157, by rfl⟩ : syracuseStep 905543 = 1358315) B1358315
theorem B906407 : Blo 401768 906407 := bstep (se 1 (by rfl) ⟨679805, by rfl⟩ : syracuseStep 906407 = 1359611) B1359611
theorem B1660139 : Blo 401768 1660139 := bstep (se 1 (by rfl) ⟨1245104, by rfl⟩ : syracuseStep 1660139 = 2490209) B2490209
theorem B513307 : Blo 401768 513307 := bstep (se 1 (by rfl) ⟨384980, by rfl⟩ : syracuseStep 513307 = 769961) B769961
theorem B11097983 : Blo 401768 11097983 := bstep (se 1 (by rfl) ⟨8323487, by rfl⟩ : syracuseStep 11097983 = 16646975) B16646975
theorem B4610195 : Blo 401768 4610195 := bstep (se 1 (by rfl) ⟨3457646, by rfl⟩ : syracuseStep 4610195 = 6915293) B6915293
theorem B2808361 : Blo 401768 2808361 := bstep (se 2 (by rfl) ⟨1053135, by rfl⟩ : syracuseStep 2808361 = 2106271) B2106271
theorem B678665 : Blo 401768 678665 := bstep (se 2 (by rfl) ⟨254499, by rfl⟩ : syracuseStep 678665 = 508999) B508999
theorem B1366793 : Blo 401768 1366793 := bstep (se 2 (by rfl) ⟨512547, by rfl⟩ : syracuseStep 1366793 = 1025095) B1025095
theorem B908135 : Blo 401768 908135 := bstep (se 1 (by rfl) ⟨681101, by rfl⟩ : syracuseStep 908135 = 1362203) B1362203
theorem B1530839 : Blo 401768 1530839 := bstep (se 1 (by rfl) ⟨1148129, by rfl⟩ : syracuseStep 1530839 = 2296259) B2296259
theorem B5168123 : Blo 401768 5168123 := bstep (se 1 (by rfl) ⟨3876092, by rfl⟩ : syracuseStep 5168123 = 7752185) B7752185
theorem B679583 : Blo 401768 679583 := bstep (se 1 (by rfl) ⟨509687, by rfl⟩ : syracuseStep 679583 = 1019375) B1019375
theorem B4579577 : Blo 401768 4579577 := bstep (se 2 (by rfl) ⟨1717341, by rfl⟩ : syracuseStep 4579577 = 3434683) B3434683
theorem B909647 : Blo 401768 909647 := bstep (se 1 (by rfl) ⟨682235, by rfl⟩ : syracuseStep 909647 = 1364471) B1364471
theorem B9855533 : Blo 401768 9855533 := bstep (se 3 (by rfl) ⟨1847912, by rfl⟩ : syracuseStep 9855533 = 3695825) B3695825
theorem B7005209 : Blo 401768 7005209 := bstep (se 2 (by rfl) ⟨2626953, by rfl⟩ : syracuseStep 7005209 = 5253907) B5253907
theorem B648233 : Blo 401768 648233 := bstep (se 2 (by rfl) ⟨243087, by rfl⟩ : syracuseStep 648233 = 486175) B486175
theorem B681115 : Blo 401768 681115 := bstep (se 1 (by rfl) ⟨510836, by rfl⟩ : syracuseStep 681115 = 1021673) B1021673
theorem B681223 : Blo 401768 681223 := bstep (se 1 (by rfl) ⟨510917, by rfl⟩ : syracuseStep 681223 = 1021835) B1021835
theorem B910799 : Blo 401768 910799 := bstep (se 1 (by rfl) ⟨683099, by rfl⟩ : syracuseStep 910799 = 1366199) B1366199
theorem B910817 : Blo 401768 910817 := bstep (se 2 (by rfl) ⟨341556, by rfl⟩ : syracuseStep 910817 = 683113) B683113
theorem B649399 : Blo 401768 649399 := bstep (se 1 (by rfl) ⟨487049, by rfl⟩ : syracuseStep 649399 = 974099) B974099
theorem B4417907 : Blo 401768 4417907 := bstep (se 1 (by rfl) ⟨3313430, by rfl⟩ : syracuseStep 4417907 = 6626861) B6626861
theorem B682607 : Blo 401768 682607 := bstep (se 1 (by rfl) ⟨511955, by rfl⟩ : syracuseStep 682607 = 1023911) B1023911
theorem B682715 : Blo 401768 682715 := bstep (se 1 (by rfl) ⟨512036, by rfl⟩ : syracuseStep 682715 = 1024073) B1024073
theorem B1534727 : Blo 401768 1534727 := bstep (se 1 (by rfl) ⟨1151045, by rfl⟩ : syracuseStep 1534727 = 2302091) B2302091
theorem B2616563 : Blo 401768 2616563 := bstep (se 1 (by rfl) ⟨1962422, by rfl⟩ : syracuseStep 2616563 = 3924845) B3924845
theorem B683471 : Blo 401768 683471 := bstep (se 1 (by rfl) ⟨512603, by rfl⟩ : syracuseStep 683471 = 1025207) B1025207
theorem B454351 : Blo 401768 454351 := bstep (se 1 (by rfl) ⟨340763, by rfl⟩ : syracuseStep 454351 = 681527) B681527
theorem B4616027 : Blo 401768 4616027 := bstep (se 1 (by rfl) ⟨3462020, by rfl⟩ : syracuseStep 4616027 = 6924041) B6924041
theorem B1535881 : Blo 401768 1535881 := bstep (se 2 (by rfl) ⟨575955, by rfl⟩ : syracuseStep 1535881 = 1151911) B1151911
theorem B684011 : Blo 401768 684011 := bstep (se 1 (by rfl) ⟨513008, by rfl⟩ : syracuseStep 684011 = 1026017) B1026017
theorem B6221933 : Blo 401768 6221933 := bstep (se 3 (by rfl) ⟨1166612, by rfl⟩ : syracuseStep 6221933 = 2333225) B2333225
theorem B4911911 : Blo 401768 4911911 := bstep (se 1 (by rfl) ⟨3683933, by rfl⟩ : syracuseStep 4911911 = 7367867) B7367867
theorem B2552639 : Blo 401768 2552639 := bstep (se 1 (by rfl) ⟨1914479, by rfl⟩ : syracuseStep 2552639 = 3828959) B3828959
theorem B1537127 : Blo 401768 1537127 := bstep (se 1 (by rfl) ⟨1152845, by rfl⟩ : syracuseStep 1537127 = 2305691) B2305691
theorem B1144667 : Blo 401768 1144667 := bstep (se 1 (by rfl) ⟨858500, by rfl⟩ : syracuseStep 1144667 = 1717001) B1717001
theorem B2291611 : Blo 401768 2291611 := bstep (se 1 (by rfl) ⟨1718708, by rfl⟩ : syracuseStep 2291611 = 3437417) B3437417
theorem B1243615 : Blo 401768 1243615 := bstep (se 1 (by rfl) ⟨932711, by rfl⟩ : syracuseStep 1243615 = 1865423) B1865423
theorem B7797545 : Blo 401768 7797545 := bstep (se 2 (by rfl) ⟨2924079, by rfl⟩ : syracuseStep 7797545 = 5848159) B5848159
theorem B13074281 : Blo 401768 13074281 := bstep (se 2 (by rfl) ⟨4902855, by rfl⟩ : syracuseStep 13074281 = 9805711) B9805711
theorem B1540073 : Blo 401768 1540073 := bstep (se 2 (by rfl) ⟨577527, by rfl⟩ : syracuseStep 1540073 = 1155055) B1155055
theorem B26281421 : Blo 401768 26281421 := bstep (se 3 (by rfl) ⟨4927766, by rfl⟩ : syracuseStep 26281421 = 9855533) B9855533
theorem B1017947 : Blo 401768 1017947 := bstep (se 1 (by rfl) ⟨763460, by rfl⟩ : syracuseStep 1017947 = 1526921) B1526921
theorem B1017967 : Blo 401768 1017967 := bstep (se 1 (by rfl) ⟨763475, by rfl⟩ : syracuseStep 1017967 = 1526951) B1526951
theorem B3466135955 : Blo 401768 3466135955 := bstep (se 1 (by rfl) ⟨2599601966, by rfl⟩ : syracuseStep 3466135955 = 5199203933) B5199203933
theorem B2034395 : Blo 401768 2034395 := bstep (se 1 (by rfl) ⟨1525796, by rfl⟩ : syracuseStep 2034395 = 3051593) B3051593
theorem B18680557 : Blo 401768 18680557 := bstep (se 3 (by rfl) ⟨3502604, by rfl⟩ : syracuseStep 18680557 = 7005209) B7005209
theorem B725615 : Blo 401768 725615 := bstep (se 1 (by rfl) ⟨544211, by rfl⟩ : syracuseStep 725615 = 1088423) B1088423
theorem B1020559 : Blo 401768 1020559 := bstep (se 1 (by rfl) ⟨765419, by rfl⟩ : syracuseStep 1020559 = 1530839) B1530839
theorem B3445415 : Blo 401768 3445415 := bstep (se 1 (by rfl) ⟨2584061, by rfl⟩ : syracuseStep 3445415 = 5168123) B5168123
theorem B1970983 : Blo 401768 1970983 := bstep (se 1 (by rfl) ⟨1478237, by rfl⟩ : syracuseStep 1970983 = 2956475) B2956475
theorem B13079353 : Blo 401768 13079353 := bstep (se 2 (by rfl) ⟨4904757, by rfl⟩ : syracuseStep 13079353 = 9809515) B9809515
theorem B29594621 : Blo 401768 29594621 := bstep (se 3 (by rfl) ⟨5548991, by rfl⟩ : syracuseStep 29594621 = 11097983) B11097983
theorem B3053051 : Blo 401768 3053051 := bstep (se 1 (by rfl) ⟨2289788, by rfl⟩ : syracuseStep 3053051 = 4579577) B4579577
theorem B432155 : Blo 401768 432155 := bstep (se 1 (by rfl) ⟨324116, by rfl⟩ : syracuseStep 432155 = 648233) B648233
theorem B858347 : Blo 401768 858347 := bstep (se 1 (by rfl) ⟨643760, by rfl⟩ : syracuseStep 858347 = 1287521) B1287521
theorem B20191841 : Blo 401768 20191841 := bstep (se 2 (by rfl) ⟨7571940, by rfl⟩ : syracuseStep 20191841 = 15143881) B15143881
theorem B1023151 : Blo 401768 1023151 := bstep (se 1 (by rfl) ⟨767363, by rfl⟩ : syracuseStep 1023151 = 1534727) B1534727
theorem B3055481 : Blo 401768 3055481 := bstep (se 2 (by rfl) ⟨1145805, by rfl⟩ : syracuseStep 3055481 = 2291611) B2291611
theorem B402075 : Blo 401768 402075 := bstep (se 1 (by rfl) ⟨301556, by rfl⟩ : syracuseStep 402075 = 603113) B603113
theorem B3744481 : Blo 401768 3744481 := bstep (se 2 (by rfl) ⟨1404180, by rfl⟩ : syracuseStep 3744481 = 2808361) B2808361
theorem B1024751 : Blo 401768 1024751 := bstep (se 1 (by rfl) ⟨768563, by rfl⟩ : syracuseStep 1024751 = 1537127) B1537127
theorem B2302775 : Blo 401768 2302775 := bstep (se 1 (by rfl) ⟨1727081, by rfl⟩ : syracuseStep 2302775 = 3454163) B3454163
theorem B402247 : Blo 401768 402247 := bstep (se 1 (by rfl) ⟨301685, by rfl⟩ : syracuseStep 402247 = 603371) B603371
theorem B402399 : Blo 401768 402399 := bstep (se 1 (by rfl) ⟨301799, by rfl⟩ : syracuseStep 402399 = 603599) B603599
theorem B402431 : Blo 401768 402431 := bstep (se 1 (by rfl) ⟨301823, by rfl⟩ : syracuseStep 402431 = 603647) B603647
theorem B402523 : Blo 401768 402523 := bstep (se 1 (by rfl) ⟨301892, by rfl⟩ : syracuseStep 402523 = 603785) B603785
theorem B763111 : Blo 401768 763111 := bstep (se 1 (by rfl) ⟨572333, by rfl⟩ : syracuseStep 763111 = 1144667) B1144667
theorem B402687 : Blo 401768 402687 := bstep (se 1 (by rfl) ⟨302015, by rfl⟩ : syracuseStep 402687 = 604031) B604031
theorem B4597073 : Blo 401768 4597073 := bstep (se 2 (by rfl) ⟨1723902, by rfl⟩ : syracuseStep 4597073 = 3447805) B3447805
theorem B403099 : Blo 401768 403099 := bstep (se 1 (by rfl) ⟨302324, by rfl⟩ : syracuseStep 403099 = 604649) B604649
theorem B730783 : Blo 401768 730783 := bstep (se 1 (by rfl) ⟨548087, by rfl⟩ : syracuseStep 730783 = 1096175) B1096175
theorem B403567 : Blo 401768 403567 := bstep (se 1 (by rfl) ⟨302675, by rfl⟩ : syracuseStep 403567 = 605351) B605351
theorem B403707 : Blo 401768 403707 := bstep (se 1 (by rfl) ⟨302780, by rfl⟩ : syracuseStep 403707 = 605561) B605561
theorem B2042495 : Blo 401768 2042495 := bstep (se 1 (by rfl) ⟨1531871, by rfl⟩ : syracuseStep 2042495 = 3063743) B3063743
theorem B1026715 : Blo 401768 1026715 := bstep (se 1 (by rfl) ⟨770036, by rfl⟩ : syracuseStep 1026715 = 1540073) B1540073
theorem B404135 : Blo 401768 404135 := bstep (se 1 (by rfl) ⟨303101, by rfl⟩ : syracuseStep 404135 = 606203) B606203
theorem B4598531 : Blo 401768 4598531 := bstep (se 1 (by rfl) ⟨3448898, by rfl⟩ : syracuseStep 4598531 = 6897797) B6897797
theorem B2599775 : Blo 401768 2599775 := bstep (se 1 (by rfl) ⟨1949831, by rfl⟩ : syracuseStep 2599775 = 3899663) B3899663
theorem B404391 : Blo 401768 404391 := bstep (se 1 (by rfl) ⟨303293, by rfl⟩ : syracuseStep 404391 = 606587) B606587
theorem B66562985 : Blo 401768 66562985 := bstep (se 2 (by rfl) ⟨24961119, by rfl⟩ : syracuseStep 66562985 = 49922239) B49922239
theorem B2305007 : Blo 401768 2305007 := bstep (se 1 (by rfl) ⟨1728755, by rfl⟩ : syracuseStep 2305007 = 3457511) B3457511
theorem B404591 : Blo 401768 404591 := bstep (se 1 (by rfl) ⟨303443, by rfl⟩ : syracuseStep 404591 = 606887) B606887
theorem B404639 : Blo 401768 404639 := bstep (se 1 (by rfl) ⟨303479, by rfl⟩ : syracuseStep 404639 = 606959) B606959
theorem B404711 : Blo 401768 404711 := bstep (se 1 (by rfl) ⟨303533, by rfl⟩ : syracuseStep 404711 = 607067) B607067
theorem B2305259 : Blo 401768 2305259 := bstep (se 1 (by rfl) ⟨1728944, by rfl⟩ : syracuseStep 2305259 = 3457889) B3457889
theorem B405199 : Blo 401768 405199 := bstep (se 1 (by rfl) ⟨303899, by rfl⟩ : syracuseStep 405199 = 607799) B607799
theorem B5517467 : Blo 401768 5517467 := bstep (se 1 (by rfl) ⟨4138100, by rfl⟩ : syracuseStep 5517467 = 8276201) B8276201
theorem B1356155 : Blo 401768 1356155 := bstep (se 1 (by rfl) ⟨1017116, by rfl⟩ : syracuseStep 1356155 = 2034233) B2034233
theorem B766817 : Blo 401768 766817 := bstep (se 2 (by rfl) ⟨287556, by rfl⟩ : syracuseStep 766817 = 575113) B575113
theorem B2175983 : Blo 401768 2175983 := bstep (se 1 (by rfl) ⟨1631987, by rfl⟩ : syracuseStep 2175983 = 3263975) B3263975
theorem B603419 : Blo 401768 603419 := bstep (se 1 (by rfl) ⟨452564, by rfl⟩ : syracuseStep 603419 = 905129) B905129
theorem B603695 : Blo 401768 603695 := bstep (se 1 (by rfl) ⟨452771, by rfl⟩ : syracuseStep 603695 = 905543) B905543
theorem B865865 : Blo 401768 865865 := bstep (se 2 (by rfl) ⟨324699, by rfl⟩ : syracuseStep 865865 = 649399) B649399
theorem B1947311 : Blo 401768 1947311 := bstep (se 1 (by rfl) ⟨1460483, by rfl⟩ : syracuseStep 1947311 = 2920967) B2920967
theorem B604271 : Blo 401768 604271 := bstep (se 1 (by rfl) ⟨453203, by rfl⟩ : syracuseStep 604271 = 906407) B906407
theorem B605423 : Blo 401768 605423 := bstep (se 1 (by rfl) ⟨454067, by rfl⟩ : syracuseStep 605423 = 908135) B908135
theorem B605801 : Blo 401768 605801 := bstep (se 2 (by rfl) ⟨227175, by rfl⟩ : syracuseStep 605801 = 454351) B454351
theorem B2047841 : Blo 401768 2047841 := bstep (se 2 (by rfl) ⟨767940, by rfl⟩ : syracuseStep 2047841 = 1535881) B1535881
theorem B770143 : Blo 401768 770143 := bstep (se 1 (by rfl) ⟨577607, by rfl⟩ : syracuseStep 770143 = 1155215) B1155215
theorem B606431 : Blo 401768 606431 := bstep (se 1 (by rfl) ⟨454823, by rfl⟩ : syracuseStep 606431 = 909647) B909647
theorem B11781085 : Blo 401768 11781085 := bstep (se 3 (by rfl) ⟨2208953, by rfl⟩ : syracuseStep 11781085 = 4417907) B4417907
theorem B607199 : Blo 401768 607199 := bstep (se 1 (by rfl) ⟨455399, by rfl⟩ : syracuseStep 607199 = 910799) B910799
theorem B607211 : Blo 401768 607211 := bstep (se 1 (by rfl) ⟨455408, by rfl⟩ : syracuseStep 607211 = 910817) B910817
theorem B969043 : Blo 401768 969043 := bstep (se 1 (by rfl) ⟨726782, by rfl⟩ : syracuseStep 969043 = 1453565) B1453565
theorem B4147955 : Blo 401768 4147955 := bstep (se 1 (by rfl) ⟨3110966, by rfl⟩ : syracuseStep 4147955 = 6221933) B6221933
theorem B510715 : Blo 401768 510715 := bstep (se 1 (by rfl) ⟨383036, by rfl⟩ : syracuseStep 510715 = 766073) B766073
theorem B904319 : Blo 401768 904319 := bstep (se 1 (by rfl) ⟨678239, by rfl⟩ : syracuseStep 904319 = 1356479) B1356479
theorem B969889 : Blo 401768 969889 := bstep (se 2 (by rfl) ⟨363708, by rfl⟩ : syracuseStep 969889 = 727417) B727417
theorem B12799205 : Blo 401768 12799205 := bstep (se 4 (by rfl) ⟨1199925, by rfl⟩ : syracuseStep 12799205 = 2399851) B2399851
theorem B1658153 : Blo 401768 1658153 := bstep (se 2 (by rfl) ⟨621807, by rfl⟩ : syracuseStep 1658153 = 1243615) B1243615
theorem B3788075 : Blo 401768 3788075 := bstep (se 1 (by rfl) ⟨2841056, by rfl⟩ : syracuseStep 3788075 = 5682113) B5682113
theorem B512239 : Blo 401768 512239 := bstep (se 1 (by rfl) ⟨384179, by rfl⟩ : syracuseStep 512239 = 768359) B768359
theorem B5198363 : Blo 401768 5198363 := bstep (se 1 (by rfl) ⟨3898772, by rfl⟩ : syracuseStep 5198363 = 7797545) B7797545
theorem B971311 : Blo 401768 971311 := bstep (se 1 (by rfl) ⟨728483, by rfl⟩ : syracuseStep 971311 = 1456967) B1456967
theorem B906623 : Blo 401768 906623 := bstep (se 1 (by rfl) ⟨679967, by rfl⟩ : syracuseStep 906623 = 1359935) B1359935
theorem B3888623 : Blo 401768 3888623 := bstep (se 1 (by rfl) ⟨2916467, by rfl⟩ : syracuseStep 3888623 = 5832935) B5832935
theorem B678071 : Blo 401768 678071 := bstep (se 1 (by rfl) ⟨508553, by rfl⟩ : syracuseStep 678071 = 1017107) B1017107
theorem B1366847 : Blo 401768 1366847 := bstep (se 1 (by rfl) ⟨1025135, by rfl⟩ : syracuseStep 1366847 = 2050271) B2050271
theorem B908153 : Blo 401768 908153 := bstep (se 2 (by rfl) ⟨340557, by rfl⟩ : syracuseStep 908153 = 681115) B681115
theorem B908297 : Blo 401768 908297 := bstep (se 2 (by rfl) ⟨340611, by rfl⟩ : syracuseStep 908297 = 681223) B681223
theorem B679529 : Blo 401768 679529 := bstep (se 2 (by rfl) ⟨254823, by rfl⟩ : syracuseStep 679529 = 509647) B509647
theorem B515867 : Blo 401768 515867 := bstep (se 1 (by rfl) ⟨386900, by rfl⟩ : syracuseStep 515867 = 773801) B773801
theorem B909215 : Blo 401768 909215 := bstep (se 1 (by rfl) ⟨681911, by rfl⟩ : syracuseStep 909215 = 1363823) B1363823
theorem B909395 : Blo 401768 909395 := bstep (se 1 (by rfl) ⟨682046, by rfl⟩ : syracuseStep 909395 = 1364093) B1364093
theorem B3498173 : Blo 401768 3498173 := bstep (se 3 (by rfl) ⟨655907, by rfl⟩ : syracuseStep 3498173 = 1311815) B1311815
theorem B909503 : Blo 401768 909503 := bstep (se 1 (by rfl) ⟨682127, by rfl⟩ : syracuseStep 909503 = 1364255) B1364255
theorem B1106759 : Blo 401768 1106759 := bstep (se 1 (by rfl) ⟨830069, by rfl⟩ : syracuseStep 1106759 = 1660139) B1660139
theorem B3073463 : Blo 401768 3073463 := bstep (se 1 (by rfl) ⟨2305097, by rfl⟩ : syracuseStep 3073463 = 4610195) B4610195
theorem B452443 : Blo 401768 452443 := bstep (se 1 (by rfl) ⟨339332, by rfl⟩ : syracuseStep 452443 = 678665) B678665
theorem B911195 : Blo 401768 911195 := bstep (se 1 (by rfl) ⟨683396, by rfl⟩ : syracuseStep 911195 = 1366793) B1366793
theorem B682087 : Blo 401768 682087 := bstep (se 1 (by rfl) ⟨511565, by rfl⟩ : syracuseStep 682087 = 1023131) B1023131
theorem B453055 : Blo 401768 453055 := bstep (se 1 (by rfl) ⟨339791, by rfl⟩ : syracuseStep 453055 = 679583) B679583
theorem B2288969 : Blo 401768 2288969 := bstep (se 2 (by rfl) ⟨858363, by rfl⟩ : syracuseStep 2288969 = 1716727) B1716727
theorem B28241369 : Blo 401768 28241369 := bstep (se 2 (by rfl) ⟨10590513, by rfl⟩ : syracuseStep 28241369 = 21181027) B21181027
theorem B5533231 : Blo 401768 5533231 := bstep (se 1 (by rfl) ⟨4149923, by rfl⟩ : syracuseStep 5533231 = 8299847) B8299847
theorem B684409 : Blo 401768 684409 := bstep (se 2 (by rfl) ⟨256653, by rfl⟩ : syracuseStep 684409 = 513307) B513307
theorem B455071 : Blo 401768 455071 := bstep (se 1 (by rfl) ⟨341303, by rfl⟩ : syracuseStep 455071 = 682607) B682607
theorem B455143 : Blo 401768 455143 := bstep (se 1 (by rfl) ⟨341357, by rfl⟩ : syracuseStep 455143 = 682715) B682715
theorem B455647 : Blo 401768 455647 := bstep (se 1 (by rfl) ⟨341735, by rfl⟩ : syracuseStep 455647 = 683471) B683471
theorem B2585627 : Blo 401768 2585627 := bstep (se 1 (by rfl) ⟨1939220, by rfl⟩ : syracuseStep 2585627 = 3878441) B3878441
theorem B3077351 : Blo 401768 3077351 := bstep (se 1 (by rfl) ⟨2308013, by rfl⟩ : syracuseStep 3077351 = 4616027) B4616027
theorem B456007 : Blo 401768 456007 := bstep (se 1 (by rfl) ⟨342005, by rfl⟩ : syracuseStep 456007 = 684011) B684011
theorem B3274607 : Blo 401768 3274607 := bstep (se 1 (by rfl) ⟨2455955, by rfl⟩ : syracuseStep 3274607 = 4911911) B4911911
theorem B6977501 : Blo 401768 6977501 := bstep (se 3 (by rfl) ⟨1308281, by rfl⟩ : syracuseStep 6977501 = 2616563) B2616563
theorem B27228149 : Blo 401768 27228149 := bstep (se 5 (by rfl) ⟨1276319, by rfl⟩ : syracuseStep 27228149 = 2552639) B2552639
theorem B1538297 : Blo 401768 1538297 := bstep (se 2 (by rfl) ⟨576861, by rfl⟩ : syracuseStep 1538297 = 1153723) B1153723
theorem B2292137 : Blo 401768 2292137 := bstep (se 2 (by rfl) ⟨859551, by rfl⟩ : syracuseStep 2292137 = 1719103) B1719103
theorem B8716187 : Blo 401768 8716187 := bstep (se 1 (by rfl) ⟨6537140, by rfl⟩ : syracuseStep 8716187 = 13074281) B13074281
theorem B1017481 : Blo 401768 1017481 := bstep (se 2 (by rfl) ⟨381555, by rfl⟩ : syracuseStep 1017481 = 763111) B763111
theorem B2525383 : Blo 401768 2525383 := bstep (se 1 (by rfl) ⟨1894037, by rfl⟩ : syracuseStep 2525383 = 3788075) B3788075
theorem B2296943 : Blo 401768 2296943 := bstep (se 1 (by rfl) ⟨1722707, by rfl⟩ : syracuseStep 2296943 = 3445415) B3445415
theorem B19729747 : Blo 401768 19729747 := bstep (se 1 (by rfl) ⟨14797310, by rfl⟩ : syracuseStep 19729747 = 29594621) B29594621
theorem B24907409 : Blo 401768 24907409 := bstep (se 2 (by rfl) ⟨9340278, by rfl⟩ : syracuseStep 24907409 = 18680557) B18680557
theorem B2592415 : Blo 401768 2592415 := bstep (se 1 (by rfl) ⟨1944311, by rfl⟩ : syracuseStep 2592415 = 3888623) B3888623
theorem B2035367 : Blo 401768 2035367 := bstep (se 1 (by rfl) ⟨1526525, by rfl⟩ : syracuseStep 2035367 = 3053051) B3053051
theorem B7377641 : Blo 401768 7377641 := bstep (se 2 (by rfl) ⟨2766615, by rfl⟩ : syracuseStep 7377641 = 5533231) B5533231
theorem B2036987 : Blo 401768 2036987 := bstep (se 1 (by rfl) ⟨1527740, by rfl⟩ : syracuseStep 2036987 = 3055481) B3055481
theorem B1152413 : Blo 401768 1152413 := bstep (se 3 (by rfl) ⟨216077, by rfl⟩ : syracuseStep 1152413 = 432155) B432155
theorem B2332115 : Blo 401768 2332115 := bstep (se 1 (by rfl) ⟨1749086, by rfl⟩ : syracuseStep 2332115 = 3498173) B3498173
theorem B2627977 : Blo 401768 2627977 := bstep (se 2 (by rfl) ⟨985491, by rfl⟩ : syracuseStep 2627977 = 1970983) B1970983
theorem B17439137 : Blo 401768 17439137 := bstep (se 2 (by rfl) ⟨6539676, by rfl⟩ : syracuseStep 17439137 = 13079353) B13079353
theorem B44375323 : Blo 401768 44375323 := bstep (se 1 (by rfl) ⟨33281492, by rfl⟩ : syracuseStep 44375323 = 66562985) B66562985
theorem B3678311 : Blo 401768 3678311 := bstep (se 1 (by rfl) ⟨2758733, by rfl⟩ : syracuseStep 3678311 = 5517467) B5517467
theorem B1450655 : Blo 401768 1450655 := bstep (se 1 (by rfl) ⟨1087991, by rfl⟩ : syracuseStep 1450655 = 2175983) B2175983
theorem B402279 : Blo 401768 402279 := bstep (se 1 (by rfl) ⟨301709, by rfl⟩ : syracuseStep 402279 = 603419) B603419
theorem B402463 : Blo 401768 402463 := bstep (se 1 (by rfl) ⟨301847, by rfl⟩ : syracuseStep 402463 = 603695) B603695
theorem B402847 : Blo 401768 402847 := bstep (se 1 (by rfl) ⟨302135, by rfl⟩ : syracuseStep 402847 = 604271) B604271
theorem B1025531 : Blo 401768 1025531 := bstep (se 1 (by rfl) ⟨769148, by rfl⟩ : syracuseStep 1025531 = 1538297) B1538297
theorem B403615 : Blo 401768 403615 := bstep (se 1 (by rfl) ⟨302711, by rfl⟩ : syracuseStep 403615 = 605423) B605423
theorem B403867 : Blo 401768 403867 := bstep (se 1 (by rfl) ⟨302900, by rfl⟩ : syracuseStep 403867 = 605801) B605801
theorem B5810791 : Blo 401768 5810791 := bstep (se 1 (by rfl) ⟨4358093, by rfl⟩ : syracuseStep 5810791 = 8716187) B8716187
theorem B1026857 : Blo 401768 1026857 := bstep (se 2 (by rfl) ⟨385071, by rfl⟩ : syracuseStep 1026857 = 770143) B770143
theorem B404287 : Blo 401768 404287 := bstep (se 1 (by rfl) ⟨303215, by rfl⟩ : syracuseStep 404287 = 606431) B606431
theorem B404799 : Blo 401768 404799 := bstep (se 1 (by rfl) ⟨303599, by rfl⟩ : syracuseStep 404799 = 607199) B607199
theorem B404807 : Blo 401768 404807 := bstep (se 1 (by rfl) ⟨303605, by rfl⟩ : syracuseStep 404807 = 607211) B607211
theorem B4992641 : Blo 401768 4992641 := bstep (se 2 (by rfl) ⟨1872240, by rfl⟩ : syracuseStep 4992641 = 3744481) B3744481
theorem B15708113 : Blo 401768 15708113 := bstep (se 2 (by rfl) ⟨5890542, by rfl⟩ : syracuseStep 15708113 = 11781085) B11781085
theorem B1356263 : Blo 401768 1356263 := bstep (se 1 (by rfl) ⟨1017197, by rfl⟩ : syracuseStep 1356263 = 2034395) B2034395
theorem B2765303 : Blo 401768 2765303 := bstep (se 1 (by rfl) ⟨2073977, by rfl⟩ : syracuseStep 2765303 = 4147955) B4147955
theorem B602879 : Blo 401768 602879 := bstep (se 1 (by rfl) ⟨452159, by rfl⟩ : syracuseStep 602879 = 904319) B904319
theorem B8532803 : Blo 401768 8532803 := bstep (se 1 (by rfl) ⟨6399602, by rfl⟩ : syracuseStep 8532803 = 12799205) B12799205
theorem B603257 : Blo 401768 603257 := bstep (se 2 (by rfl) ⟨226221, by rfl⟩ : syracuseStep 603257 = 452443) B452443
theorem B1357289 : Blo 401768 1357289 := bstep (se 2 (by rfl) ⟨508983, by rfl⟩ : syracuseStep 1357289 = 1017967) B1017967
theorem B1292057 : Blo 401768 1292057 := bstep (se 2 (by rfl) ⟨484521, by rfl⟩ : syracuseStep 1292057 = 969043) B969043
theorem B604073 : Blo 401768 604073 := bstep (se 2 (by rfl) ⟨226527, by rfl⟩ : syracuseStep 604073 = 453055) B453055
theorem B604415 : Blo 401768 604415 := bstep (se 1 (by rfl) ⟨453311, by rfl⟩ : syracuseStep 604415 = 906623) B906623
theorem B572231 : Blo 401768 572231 := bstep (se 1 (by rfl) ⟨429173, by rfl⟩ : syracuseStep 572231 = 858347) B858347
theorem B1293185 : Blo 401768 1293185 := bstep (se 2 (by rfl) ⟨484944, by rfl⟩ : syracuseStep 1293185 = 969889) B969889
theorem B605435 : Blo 401768 605435 := bstep (se 1 (by rfl) ⟨454076, by rfl⟩ : syracuseStep 605435 = 908153) B908153
theorem B605531 : Blo 401768 605531 := bstep (se 1 (by rfl) ⟨454148, by rfl⟩ : syracuseStep 605531 = 908297) B908297
theorem B606143 : Blo 401768 606143 := bstep (se 1 (by rfl) ⟨454607, by rfl⟩ : syracuseStep 606143 = 909215) B909215
theorem B606263 : Blo 401768 606263 := bstep (se 1 (by rfl) ⟨454697, by rfl⟩ : syracuseStep 606263 = 909395) B909395
theorem B606335 : Blo 401768 606335 := bstep (se 1 (by rfl) ⟨454751, by rfl⟩ : syracuseStep 606335 = 909503) B909503
theorem B606761 : Blo 401768 606761 := bstep (se 2 (by rfl) ⟨227535, by rfl⟩ : syracuseStep 606761 = 455071) B455071
theorem B737839 : Blo 401768 737839 := bstep (se 1 (by rfl) ⟨553379, by rfl⟩ : syracuseStep 737839 = 1106759) B1106759
theorem B606857 : Blo 401768 606857 := bstep (se 2 (by rfl) ⟨227571, by rfl⟩ : syracuseStep 606857 = 455143) B455143
theorem B1295081 : Blo 401768 1295081 := bstep (se 2 (by rfl) ⟨485655, by rfl⟩ : syracuseStep 1295081 = 971311) B971311
theorem B1360745 : Blo 401768 1360745 := bstep (se 2 (by rfl) ⟨510279, by rfl⟩ : syracuseStep 1360745 = 1020559) B1020559
theorem B3064715 : Blo 401768 3064715 := bstep (se 1 (by rfl) ⟨2298536, by rfl⟩ : syracuseStep 3064715 = 4597073) B4597073
theorem B2048975 : Blo 401768 2048975 := bstep (se 1 (by rfl) ⟨1536731, by rfl⟩ : syracuseStep 2048975 = 3073463) B3073463
theorem B607463 : Blo 401768 607463 := bstep (se 1 (by rfl) ⟨455597, by rfl⟩ : syracuseStep 607463 = 911195) B911195
theorem B607529 : Blo 401768 607529 := bstep (se 2 (by rfl) ⟨227823, by rfl⟩ : syracuseStep 607529 = 455647) B455647
theorem B1361663 : Blo 401768 1361663 := bstep (se 1 (by rfl) ⟨1021247, by rfl⟩ : syracuseStep 1361663 = 2042495) B2042495
theorem B608009 : Blo 401768 608009 := bstep (se 2 (by rfl) ⟨228003, by rfl⟩ : syracuseStep 608009 = 456007) B456007
theorem B3065687 : Blo 401768 3065687 := bstep (se 1 (by rfl) ⟨2299265, by rfl⟩ : syracuseStep 3065687 = 4598531) B4598531
theorem B1525979 : Blo 401768 1525979 := bstep (se 1 (by rfl) ⟨1144484, by rfl⟩ : syracuseStep 1525979 = 2288969) B2288969
theorem B18827579 : Blo 401768 18827579 := bstep (se 1 (by rfl) ⟨14120684, by rfl⟩ : syracuseStep 18827579 = 28241369) B28241369
theorem B904103 : Blo 401768 904103 := bstep (se 1 (by rfl) ⟨678077, by rfl⟩ : syracuseStep 904103 = 1356155) B1356155
theorem B511211 : Blo 401768 511211 := bstep (se 1 (by rfl) ⟨383408, by rfl⟩ : syracuseStep 511211 = 766817) B766817
theorem B1723751 : Blo 401768 1723751 := bstep (se 1 (by rfl) ⟨1292813, by rfl⟩ : syracuseStep 1723751 = 2585627) B2585627
theorem B2051567 : Blo 401768 2051567 := bstep (se 1 (by rfl) ⟨1538675, by rfl⟩ : syracuseStep 2051567 = 3077351) B3077351
theorem B577243 : Blo 401768 577243 := bstep (se 1 (by rfl) ⟨432932, by rfl⟩ : syracuseStep 577243 = 865865) B865865
theorem B1298207 : Blo 401768 1298207 := bstep (se 1 (by rfl) ⟨973655, by rfl⟩ : syracuseStep 1298207 = 1947311) B1947311
theorem B2183071 : Blo 401768 2183071 := bstep (se 1 (by rfl) ⟨1637303, by rfl⟩ : syracuseStep 2183071 = 3274607) B3274607
theorem B1364201 : Blo 401768 1364201 := bstep (se 2 (by rfl) ⟨511575, by rfl⟩ : syracuseStep 1364201 = 1023151) B1023151
theorem B1528091 : Blo 401768 1528091 := bstep (se 1 (by rfl) ⟨1146068, by rfl⟩ : syracuseStep 1528091 = 2292137) B2292137
theorem B1365227 : Blo 401768 1365227 := bstep (se 1 (by rfl) ⟨1023920, by rfl⟩ : syracuseStep 1365227 = 2047841) B2047841
theorem B17520947 : Blo 401768 17520947 := bstep (se 1 (by rfl) ⟨13140710, by rfl⟩ : syracuseStep 17520947 = 26281421) B26281421
theorem B678631 : Blo 401768 678631 := bstep (se 1 (by rfl) ⟨508973, by rfl⟩ : syracuseStep 678631 = 1017947) B1017947
theorem B2310757303 : Blo 401768 2310757303 := bstep (se 1 (by rfl) ⟨1733067977, by rfl⟩ : syracuseStep 2310757303 = 3466135955) B3466135955
theorem B1105435 : Blo 401768 1105435 := bstep (se 1 (by rfl) ⟨829076, by rfl⟩ : syracuseStep 1105435 = 1658153) B1658153
theorem B974377 : Blo 401768 974377 := bstep (se 2 (by rfl) ⟨365391, by rfl⟩ : syracuseStep 974377 = 730783) B730783
theorem B909449 : Blo 401768 909449 := bstep (se 2 (by rfl) ⟨341043, by rfl⟩ : syracuseStep 909449 = 682087) B682087
theorem B3465575 : Blo 401768 3465575 := bstep (se 1 (by rfl) ⟨2599181, by rfl⟩ : syracuseStep 3465575 = 5198363) B5198363
theorem B483743 : Blo 401768 483743 := bstep (se 1 (by rfl) ⟨362807, by rfl⟩ : syracuseStep 483743 = 725615) B725615
theorem B1368953 : Blo 401768 1368953 := bstep (se 2 (by rfl) ⟨513357, by rfl⟩ : syracuseStep 1368953 = 1026715) B1026715
theorem B680953 : Blo 401768 680953 := bstep (se 2 (by rfl) ⟨255357, by rfl⟩ : syracuseStep 680953 = 510715) B510715
theorem B452047 : Blo 401768 452047 := bstep (se 1 (by rfl) ⟨339035, by rfl⟩ : syracuseStep 452047 = 678071) B678071
theorem B13461227 : Blo 401768 13461227 := bstep (se 1 (by rfl) ⟨10095920, by rfl⟩ : syracuseStep 13461227 = 20191841) B20191841
theorem B911231 : Blo 401768 911231 := bstep (se 1 (by rfl) ⟨683423, by rfl⟩ : syracuseStep 911231 = 1366847) B1366847
theorem B453019 : Blo 401768 453019 := bstep (se 1 (by rfl) ⟨339764, by rfl⟩ : syracuseStep 453019 = 679529) B679529
theorem B682985 : Blo 401768 682985 := bstep (se 2 (by rfl) ⟨256119, by rfl⟩ : syracuseStep 682985 = 512239) B512239
theorem B683167 : Blo 401768 683167 := bstep (se 1 (by rfl) ⟨512375, by rfl⟩ : syracuseStep 683167 = 1024751) B1024751
theorem B912545 : Blo 401768 912545 := bstep (se 2 (by rfl) ⟨342204, by rfl⟩ : syracuseStep 912545 = 684409) B684409
theorem B1535183 : Blo 401768 1535183 := bstep (se 1 (by rfl) ⟨1151387, by rfl⟩ : syracuseStep 1535183 = 2302775) B2302775
theorem B1733183 : Blo 401768 1733183 := bstep (se 1 (by rfl) ⟨1299887, by rfl⟩ : syracuseStep 1733183 = 2599775) B2599775
theorem B1536671 : Blo 401768 1536671 := bstep (se 1 (by rfl) ⟨1152503, by rfl⟩ : syracuseStep 1536671 = 2305007) B2305007
theorem B1536839 : Blo 401768 1536839 := bstep (se 1 (by rfl) ⟨1152629, by rfl⟩ : syracuseStep 1536839 = 2305259) B2305259
theorem B4651667 : Blo 401768 4651667 := bstep (se 1 (by rfl) ⟨3488750, by rfl⟩ : syracuseStep 4651667 = 6977501) B6977501
theorem B18152099 : Blo 401768 18152099 := bstep (se 1 (by rfl) ⟨13614074, by rfl⟩ : syracuseStep 18152099 = 27228149) B27228149
theorem B1375645 : Blo 401768 1375645 := bstep (se 3 (by rfl) ⟨257933, by rfl⟩ : syracuseStep 1375645 = 515867) B515867
theorem B1017319 : Blo 401768 1017319 := bstep (se 1 (by rfl) ⟨762989, by rfl⟩ : syracuseStep 1017319 = 1525979) B1525979
theorem B1149167 : Blo 401768 1149167 := bstep (se 1 (by rfl) ⟨861875, by rfl⟩ : syracuseStep 1149167 = 1723751) B1723751
theorem B1018727 : Blo 401768 1018727 := bstep (se 1 (by rfl) ⟨764045, by rfl⟩ : syracuseStep 1018727 = 1528091) B1528091
theorem B3935141 : Blo 401768 3935141 := bstep (se 4 (by rfl) ⟨368919, by rfl⟩ : syracuseStep 3935141 = 737839) B737839
theorem B4918427 : Blo 401768 4918427 := bstep (se 1 (by rfl) ⟨3688820, by rfl⟩ : syracuseStep 4918427 = 7377641) B7377641
theorem B50206877 : Blo 401768 50206877 := bstep (se 3 (by rfl) ⟨9413789, by rfl⟩ : syracuseStep 50206877 = 18827579) B18827579
theorem B1023455 : Blo 401768 1023455 := bstep (se 1 (by rfl) ⟨767591, by rfl⟩ : syracuseStep 1023455 = 1535183) B1535183
theorem B1843535 : Blo 401768 1843535 := bstep (se 1 (by rfl) ⟨1382651, by rfl⟩ : syracuseStep 1843535 = 2765303) B2765303
theorem B1155455 : Blo 401768 1155455 := bstep (se 1 (by rfl) ⟨866591, by rfl⟩ : syracuseStep 1155455 = 1733183) B1733183
theorem B1024447 : Blo 401768 1024447 := bstep (se 1 (by rfl) ⟨768335, by rfl⟩ : syracuseStep 1024447 = 1536671) B1536671
theorem B401919 : Blo 401768 401919 := bstep (se 1 (by rfl) ⟨301439, by rfl⟩ : syracuseStep 401919 = 602879) B602879
theorem B1024559 : Blo 401768 1024559 := bstep (se 1 (by rfl) ⟨768419, by rfl⟩ : syracuseStep 1024559 = 1536839) B1536839
theorem B402171 : Blo 401768 402171 := bstep (se 1 (by rfl) ⟨301628, by rfl⟩ : syracuseStep 402171 = 603257) B603257
theorem B861371 : Blo 401768 861371 := bstep (se 1 (by rfl) ⟨646028, by rfl⟩ : syracuseStep 861371 = 1292057) B1292057
theorem B402715 : Blo 401768 402715 := bstep (se 1 (by rfl) ⟨302036, by rfl⟩ : syracuseStep 402715 = 604073) B604073
theorem B402943 : Blo 401768 402943 := bstep (se 1 (by rfl) ⟨302207, by rfl⟩ : syracuseStep 402943 = 604415) B604415
theorem B12101399 : Blo 401768 12101399 := bstep (se 1 (by rfl) ⟨9076049, by rfl⟩ : syracuseStep 12101399 = 18152099) B18152099
theorem B862123 : Blo 401768 862123 := bstep (se 1 (by rfl) ⟨646592, by rfl⟩ : syracuseStep 862123 = 1293185) B1293185
theorem B403623 : Blo 401768 403623 := bstep (se 1 (by rfl) ⟨302717, by rfl⟩ : syracuseStep 403623 = 605435) B605435
theorem B403687 : Blo 401768 403687 := bstep (se 1 (by rfl) ⟨302765, by rfl⟩ : syracuseStep 403687 = 605531) B605531
theorem B404095 : Blo 401768 404095 := bstep (se 1 (by rfl) ⟨303071, by rfl⟩ : syracuseStep 404095 = 606143) B606143
theorem B404175 : Blo 401768 404175 := bstep (se 1 (by rfl) ⟨303131, by rfl⟩ : syracuseStep 404175 = 606263) B606263
theorem B404223 : Blo 401768 404223 := bstep (se 1 (by rfl) ⟨303167, by rfl⟩ : syracuseStep 404223 = 606335) B606335
theorem B404507 : Blo 401768 404507 := bstep (se 1 (by rfl) ⟨303380, by rfl⟩ : syracuseStep 404507 = 606761) B606761
theorem B404571 : Blo 401768 404571 := bstep (se 1 (by rfl) ⟨303428, by rfl⟩ : syracuseStep 404571 = 606857) B606857
theorem B863387 : Blo 401768 863387 := bstep (se 1 (by rfl) ⟨647540, by rfl⟩ : syracuseStep 863387 = 1295081) B1295081
theorem B2043143 : Blo 401768 2043143 := bstep (se 1 (by rfl) ⟨1532357, by rfl⟩ : syracuseStep 2043143 = 3064715) B3064715
theorem B404975 : Blo 401768 404975 := bstep (se 1 (by rfl) ⟨303731, by rfl⟩ : syracuseStep 404975 = 607463) B607463
theorem B405019 : Blo 401768 405019 := bstep (se 1 (by rfl) ⟨303764, by rfl⟩ : syracuseStep 405019 = 607529) B607529
theorem B1289981 : Blo 401768 1289981 := bstep (se 3 (by rfl) ⟨241871, by rfl⟩ : syracuseStep 1289981 = 483743) B483743
theorem B405339 : Blo 401768 405339 := bstep (se 1 (by rfl) ⟨304004, by rfl⟩ : syracuseStep 405339 = 608009) B608009
theorem B2043791 : Blo 401768 2043791 := bstep (se 1 (by rfl) ⟨1532843, by rfl⟩ : syracuseStep 2043791 = 3065687) B3065687
theorem B602729 : Blo 401768 602729 := bstep (se 2 (by rfl) ⟨226023, by rfl⟩ : syracuseStep 602729 = 452047) B452047
theorem B602735 : Blo 401768 602735 := bstep (se 1 (by rfl) ⟨452051, by rfl⟩ : syracuseStep 602735 = 904103) B904103
theorem B22754141 : Blo 401768 22754141 := bstep (se 3 (by rfl) ⟨4266401, by rfl⟩ : syracuseStep 22754141 = 8532803) B8532803
theorem B1356641 : Blo 401768 1356641 := bstep (se 2 (by rfl) ⟨508740, by rfl⟩ : syracuseStep 1356641 = 1017481) B1017481
theorem B1356911 : Blo 401768 1356911 := bstep (se 1 (by rfl) ⟨1017683, by rfl⟩ : syracuseStep 1356911 = 2035367) B2035367
theorem B604025 : Blo 401768 604025 := bstep (se 2 (by rfl) ⟨226509, by rfl⟩ : syracuseStep 604025 = 453019) B453019
theorem B7747721 : Blo 401768 7747721 := bstep (se 2 (by rfl) ⟨2905395, by rfl⟩ : syracuseStep 7747721 = 5810791) B5810791
theorem B1357991 : Blo 401768 1357991 := bstep (se 1 (by rfl) ⟨1018493, by rfl⟩ : syracuseStep 1357991 = 2036987) B2036987
theorem B768275 : Blo 401768 768275 := bstep (se 1 (by rfl) ⟨576206, by rfl⟩ : syracuseStep 768275 = 1152413) B1152413
theorem B1554743 : Blo 401768 1554743 := bstep (se 1 (by rfl) ⟨1166057, by rfl⟩ : syracuseStep 1554743 = 2332115) B2332115
theorem B11680631 : Blo 401768 11680631 := bstep (se 1 (by rfl) ⟨8760473, by rfl⟩ : syracuseStep 11680631 = 17520947) B17520947
theorem B3456553 : Blo 401768 3456553 := bstep (se 2 (by rfl) ⟨1296207, by rfl⟩ : syracuseStep 3456553 = 2592415) B2592415
theorem B769657 : Blo 401768 769657 := bstep (se 2 (by rfl) ⟨288621, by rfl⟩ : syracuseStep 769657 = 577243) B577243
theorem B606299 : Blo 401768 606299 := bstep (se 1 (by rfl) ⟨454724, by rfl⟩ : syracuseStep 606299 = 909449) B909449
theorem B2310383 : Blo 401768 2310383 := bstep (se 1 (by rfl) ⟨1732787, by rfl⟩ : syracuseStep 2310383 = 3465575) B3465575
theorem B967103 : Blo 401768 967103 := bstep (se 1 (by rfl) ⟨725327, by rfl⟩ : syracuseStep 967103 = 1450655) B1450655
theorem B607487 : Blo 401768 607487 := bstep (se 1 (by rfl) ⟨455615, by rfl⟩ : syracuseStep 607487 = 911231) B911231
theorem B608363 : Blo 401768 608363 := bstep (se 1 (by rfl) ⟨456272, by rfl⟩ : syracuseStep 608363 = 912545) B912545
theorem B1525949 : Blo 401768 1525949 := bstep (se 3 (by rfl) ⟨286115, by rfl⟩ : syracuseStep 1525949 = 572231) B572231
theorem B3328427 : Blo 401768 3328427 := bstep (se 1 (by rfl) ⟨2496320, by rfl⟩ : syracuseStep 3328427 = 4992641) B4992641
theorem B10472075 : Blo 401768 10472075 := bstep (se 1 (by rfl) ⟨7854056, by rfl⟩ : syracuseStep 10472075 = 15708113) B15708113
theorem B904175 : Blo 401768 904175 := bstep (se 1 (by rfl) ⟨678131, by rfl⟩ : syracuseStep 904175 = 1356263) B1356263
theorem B1363229 : Blo 401768 1363229 := bstep (se 3 (by rfl) ⟨255605, by rfl⟩ : syracuseStep 1363229 = 511211) B511211
theorem B904841 : Blo 401768 904841 := bstep (se 2 (by rfl) ⟨339315, by rfl⟩ : syracuseStep 904841 = 678631) B678631
theorem B904859 : Blo 401768 904859 := bstep (se 1 (by rfl) ⟨678644, by rfl⟩ : syracuseStep 904859 = 1357289) B1357289
theorem B59167097 : Blo 401768 59167097 := bstep (se 2 (by rfl) ⟨22187661, by rfl⟩ : syracuseStep 59167097 = 44375323) B44375323
theorem B3101111 : Blo 401768 3101111 := bstep (se 1 (by rfl) ⟨2325833, by rfl⟩ : syracuseStep 3101111 = 4651667) B4651667
theorem B1299169 : Blo 401768 1299169 := bstep (se 2 (by rfl) ⟨487188, by rfl⟩ : syracuseStep 1299169 = 974377) B974377
theorem B3461885 : Blo 401768 3461885 := bstep (se 3 (by rfl) ⟨649103, by rfl⟩ : syracuseStep 3461885 = 1298207) B1298207
theorem B907163 : Blo 401768 907163 := bstep (se 1 (by rfl) ⟨680372, by rfl⟩ : syracuseStep 907163 = 1360745) B1360745
theorem B1365983 : Blo 401768 1365983 := bstep (se 1 (by rfl) ⟨1024487, by rfl⟩ : syracuseStep 1365983 = 2048975) B2048975
theorem B907775 : Blo 401768 907775 := bstep (se 1 (by rfl) ⟨680831, by rfl⟩ : syracuseStep 907775 = 1361663) B1361663
theorem B907937 : Blo 401768 907937 := bstep (se 2 (by rfl) ⟨340476, by rfl⟩ : syracuseStep 907937 = 680953) B680953
theorem B1531295 : Blo 401768 1531295 := bstep (se 1 (by rfl) ⟨1148471, by rfl⟩ : syracuseStep 1531295 = 2296943) B2296943
theorem B1367711 : Blo 401768 1367711 := bstep (se 1 (by rfl) ⟨1025783, by rfl⟩ : syracuseStep 1367711 = 2051567) B2051567
theorem B16604939 : Blo 401768 16604939 := bstep (se 1 (by rfl) ⟨12453704, by rfl⟩ : syracuseStep 16604939 = 24907409) B24907409
theorem B909467 : Blo 401768 909467 := bstep (se 1 (by rfl) ⟨682100, by rfl⟩ : syracuseStep 909467 = 1364201) B1364201
theorem B3367177 : Blo 401768 3367177 := bstep (se 2 (by rfl) ⟨1262691, by rfl⟩ : syracuseStep 3367177 = 2525383) B2525383
theorem B910151 : Blo 401768 910151 := bstep (se 1 (by rfl) ⟨682613, by rfl⟩ : syracuseStep 910151 = 1365227) B1365227
theorem B910889 : Blo 401768 910889 := bstep (se 2 (by rfl) ⟨341583, by rfl⟩ : syracuseStep 910889 = 683167) B683167
theorem B11626091 : Blo 401768 11626091 := bstep (se 1 (by rfl) ⟨8719568, by rfl⟩ : syracuseStep 11626091 = 17439137) B17439137
theorem B26306329 : Blo 401768 26306329 := bstep (se 2 (by rfl) ⟨9864873, by rfl⟩ : syracuseStep 26306329 = 19729747) B19729747
theorem B2910761 : Blo 401768 2910761 := bstep (se 2 (by rfl) ⟨1091535, by rfl⟩ : syracuseStep 2910761 = 2183071) B2183071
theorem B2452207 : Blo 401768 2452207 := bstep (se 1 (by rfl) ⟨1839155, by rfl⟩ : syracuseStep 2452207 = 3678311) B3678311
theorem B912635 : Blo 401768 912635 := bstep (se 1 (by rfl) ⟨684476, by rfl⟩ : syracuseStep 912635 = 1368953) B1368953
theorem B683687 : Blo 401768 683687 := bstep (se 1 (by rfl) ⟨512765, by rfl⟩ : syracuseStep 683687 = 1025531) B1025531
theorem B8974151 : Blo 401768 8974151 := bstep (se 1 (by rfl) ⟨6730613, by rfl⟩ : syracuseStep 8974151 = 13461227) B13461227
theorem B684571 : Blo 401768 684571 := bstep (se 1 (by rfl) ⟨513428, by rfl⟩ : syracuseStep 684571 = 1026857) B1026857
theorem B455323 : Blo 401768 455323 := bstep (se 1 (by rfl) ⟨341492, by rfl⟩ : syracuseStep 455323 = 682985) B682985
theorem B3503969 : Blo 401768 3503969 := bstep (se 2 (by rfl) ⟨1313988, by rfl⟩ : syracuseStep 3503969 = 2627977) B2627977
theorem B3081009737 : Blo 401768 3081009737 := bstep (se 2 (by rfl) ⟨1155378651, by rfl⟩ : syracuseStep 3081009737 = 2310757303) B2310757303
theorem B1834193 : Blo 401768 1834193 := bstep (se 2 (by rfl) ⟨687822, by rfl⟩ : syracuseStep 1834193 = 1375645) B1375645
theorem B1473913 : Blo 401768 1473913 := bstep (se 2 (by rfl) ⟨552717, by rfl⟩ : syracuseStep 1473913 = 1105435) B1105435
theorem B1540255 : Blo 401768 1540255 := bstep (se 1 (by rfl) ⟨1155191, by rfl⟩ : syracuseStep 1540255 = 2310383) B2310383
theorem B17958277 : Blo 401768 17958277 := bstep (se 4 (by rfl) ⟨1683588, by rfl⟩ : syracuseStep 17958277 = 3367177) B3367177
theorem B1017299 : Blo 401768 1017299 := bstep (se 1 (by rfl) ⟨762974, by rfl⟩ : syracuseStep 1017299 = 1525949) B1525949
theorem B6981383 : Blo 401768 6981383 := bstep (se 1 (by rfl) ⟨5236037, by rfl⟩ : syracuseStep 6981383 = 10472075) B10472075
theorem B2623427 : Blo 401768 2623427 := bstep (se 1 (by rfl) ⟨1967570, by rfl⟩ : syracuseStep 2623427 = 3935141) B3935141
theorem B3278951 : Blo 401768 3278951 := bstep (se 1 (by rfl) ⟨2459213, by rfl⟩ : syracuseStep 3278951 = 4918427) B4918427
theorem B1149497 : Blo 401768 1149497 := bstep (se 2 (by rfl) ⟨431061, by rfl⟩ : syracuseStep 1149497 = 862123) B862123
theorem B2067407 : Blo 401768 2067407 := bstep (se 1 (by rfl) ⟨1550555, by rfl⟩ : syracuseStep 2067407 = 3101111) B3101111
theorem B1020863 : Blo 401768 1020863 := bstep (se 1 (by rfl) ⟨765647, by rfl⟩ : syracuseStep 1020863 = 1531295) B1531295
theorem B8067599 : Blo 401768 8067599 := bstep (se 1 (by rfl) ⟨6050699, by rfl⟩ : syracuseStep 8067599 = 12101399) B12101399
theorem B8216025965 : Blo 401768 8216025965 := bstep (se 3 (by rfl) ⟨1540504868, by rfl⟩ : syracuseStep 8216025965 = 3081009737) B3081009737
theorem B1940507 : Blo 401768 1940507 := bstep (se 1 (by rfl) ⟨1455380, by rfl⟩ : syracuseStep 1940507 = 2910761) B2910761
theorem B859987 : Blo 401768 859987 := bstep (se 1 (by rfl) ⟨644990, by rfl⟩ : syracuseStep 859987 = 1289981) B1289981
theorem B401819 : Blo 401768 401819 := bstep (se 1 (by rfl) ⟨301364, by rfl⟩ : syracuseStep 401819 = 602729) B602729
theorem B401823 : Blo 401768 401823 := bstep (se 1 (by rfl) ⟨301367, by rfl⟩ : syracuseStep 401823 = 602735) B602735
theorem B2335979 : Blo 401768 2335979 := bstep (se 1 (by rfl) ⟨1751984, by rfl⟩ : syracuseStep 2335979 = 3503969) B3503969
theorem B402683 : Blo 401768 402683 := bstep (se 1 (by rfl) ⟨302012, by rfl⟩ : syracuseStep 402683 = 604025) B604025
theorem B1222795 : Blo 401768 1222795 := bstep (se 1 (by rfl) ⟨917096, by rfl⟩ : syracuseStep 1222795 = 1834193) B1834193
theorem B1026209 : Blo 401768 1026209 := bstep (se 2 (by rfl) ⟨384828, by rfl⟩ : syracuseStep 1026209 = 769657) B769657
theorem B404199 : Blo 401768 404199 := bstep (se 1 (by rfl) ⟨303149, by rfl⟩ : syracuseStep 404199 = 606299) B606299
theorem B404991 : Blo 401768 404991 := bstep (se 1 (by rfl) ⟨303743, by rfl⟩ : syracuseStep 404991 = 607487) B607487
theorem B405575 : Blo 401768 405575 := bstep (se 1 (by rfl) ⟨304181, by rfl⟩ : syracuseStep 405575 = 608363) B608363
theorem B766111 : Blo 401768 766111 := bstep (se 1 (by rfl) ⟨574583, by rfl⟩ : syracuseStep 766111 = 1149167) B1149167
theorem B1356425 : Blo 401768 1356425 := bstep (se 2 (by rfl) ⟨508659, by rfl⟩ : syracuseStep 1356425 = 1017319) B1017319
theorem B602783 : Blo 401768 602783 := bstep (se 1 (by rfl) ⟨452087, by rfl⟩ : syracuseStep 602783 = 904175) B904175
theorem B35075105 : Blo 401768 35075105 := bstep (se 2 (by rfl) ⟨13153164, by rfl⟩ : syracuseStep 35075105 = 26306329) B26306329
theorem B603227 : Blo 401768 603227 := bstep (se 1 (by rfl) ⟨452420, by rfl⟩ : syracuseStep 603227 = 904841) B904841
theorem B603239 : Blo 401768 603239 := bstep (se 1 (by rfl) ⟨452429, by rfl⟩ : syracuseStep 603239 = 904859) B904859
theorem B2307923 : Blo 401768 2307923 := bstep (se 1 (by rfl) ⟨1730942, by rfl⟩ : syracuseStep 2307923 = 3461885) B3461885
theorem B604775 : Blo 401768 604775 := bstep (se 1 (by rfl) ⟨453581, by rfl⟩ : syracuseStep 604775 = 907163) B907163
theorem B33471251 : Blo 401768 33471251 := bstep (se 1 (by rfl) ⟨25103438, by rfl⟩ : syracuseStep 33471251 = 50206877) B50206877
theorem B605183 : Blo 401768 605183 := bstep (se 1 (by rfl) ⟨453887, by rfl⟩ : syracuseStep 605183 = 907775) B907775
theorem B605291 : Blo 401768 605291 := bstep (se 1 (by rfl) ⟨453968, by rfl⟩ : syracuseStep 605291 = 907937) B907937
theorem B606311 : Blo 401768 606311 := bstep (se 1 (by rfl) ⟨454733, by rfl⟩ : syracuseStep 606311 = 909467) B909467
theorem B1229023 : Blo 401768 1229023 := bstep (se 1 (by rfl) ⟨921767, by rfl⟩ : syracuseStep 1229023 = 1843535) B1843535
theorem B770303 : Blo 401768 770303 := bstep (se 1 (by rfl) ⟨577727, by rfl⟩ : syracuseStep 770303 = 1155455) B1155455
theorem B606767 : Blo 401768 606767 := bstep (se 1 (by rfl) ⟨455075, by rfl⟩ : syracuseStep 606767 = 910151) B910151
theorem B574247 : Blo 401768 574247 := bstep (se 1 (by rfl) ⟨430685, by rfl⟩ : syracuseStep 574247 = 861371) B861371
theorem B607097 : Blo 401768 607097 := bstep (se 2 (by rfl) ⟨227661, by rfl⟩ : syracuseStep 607097 = 455323) B455323
theorem B607259 : Blo 401768 607259 := bstep (se 1 (by rfl) ⟨455444, by rfl⟩ : syracuseStep 607259 = 910889) B910889
theorem B7750727 : Blo 401768 7750727 := bstep (se 1 (by rfl) ⟨5813045, by rfl⟩ : syracuseStep 7750727 = 11626091) B11626091
theorem B575591 : Blo 401768 575591 := bstep (se 1 (by rfl) ⟨431693, by rfl⟩ : syracuseStep 575591 = 863387) B863387
theorem B608423 : Blo 401768 608423 := bstep (se 1 (by rfl) ⟨456317, by rfl⟩ : syracuseStep 608423 = 912635) B912635
theorem B1362095 : Blo 401768 1362095 := bstep (se 1 (by rfl) ⟨1021571, by rfl⟩ : syracuseStep 1362095 = 2043143) B2043143
theorem B5982767 : Blo 401768 5982767 := bstep (se 1 (by rfl) ⟨4487075, by rfl⟩ : syracuseStep 5982767 = 8974151) B8974151
theorem B1362527 : Blo 401768 1362527 := bstep (se 1 (by rfl) ⟨1021895, by rfl⟩ : syracuseStep 1362527 = 2043791) B2043791
theorem B904427 : Blo 401768 904427 := bstep (se 1 (by rfl) ⟨678320, by rfl⟩ : syracuseStep 904427 = 1356641) B1356641
theorem B904607 : Blo 401768 904607 := bstep (se 1 (by rfl) ⟨678455, by rfl⟩ : syracuseStep 904607 = 1356911) B1356911
theorem B5165147 : Blo 401768 5165147 := bstep (se 1 (by rfl) ⟨3873860, by rfl⟩ : syracuseStep 5165147 = 7747721) B7747721
theorem B905327 : Blo 401768 905327 := bstep (se 1 (by rfl) ⟨678995, by rfl⟩ : syracuseStep 905327 = 1357991) B1357991
theorem B512183 : Blo 401768 512183 := bstep (se 1 (by rfl) ⟨384137, by rfl⟩ : syracuseStep 512183 = 768275) B768275
theorem B1036495 : Blo 401768 1036495 := bstep (se 1 (by rfl) ⟨777371, by rfl⟩ : syracuseStep 1036495 = 1554743) B1554743
theorem B7787087 : Blo 401768 7787087 := bstep (se 1 (by rfl) ⟨5840315, by rfl⟩ : syracuseStep 7787087 = 11680631) B11680631
theorem B4608737 : Blo 401768 4608737 := bstep (se 2 (by rfl) ⟨1728276, by rfl⟩ : syracuseStep 4608737 = 3456553) B3456553
theorem B644735 : Blo 401768 644735 := bstep (se 1 (by rfl) ⟨483551, by rfl⟩ : syracuseStep 644735 = 967103) B967103
theorem B1365929 : Blo 401768 1365929 := bstep (se 2 (by rfl) ⟨512223, by rfl⟩ : syracuseStep 1365929 = 1024447) B1024447
theorem B2218951 : Blo 401768 2218951 := bstep (se 1 (by rfl) ⟨1664213, by rfl⟩ : syracuseStep 2218951 = 3328427) B3328427
theorem B679151 : Blo 401768 679151 := bstep (se 1 (by rfl) ⟨509363, by rfl⟩ : syracuseStep 679151 = 1018727) B1018727
theorem B908819 : Blo 401768 908819 := bstep (se 1 (by rfl) ⟨681614, by rfl⟩ : syracuseStep 908819 = 1363229) B1363229
theorem B39444731 : Blo 401768 39444731 := bstep (se 1 (by rfl) ⟨29583548, by rfl⟩ : syracuseStep 39444731 = 59167097) B59167097
theorem B3269609 : Blo 401768 3269609 := bstep (se 2 (by rfl) ⟨1226103, by rfl⟩ : syracuseStep 3269609 = 2452207) B2452207
theorem B910655 : Blo 401768 910655 := bstep (se 1 (by rfl) ⟨682991, by rfl⟩ : syracuseStep 910655 = 1365983) B1365983
theorem B682303 : Blo 401768 682303 := bstep (se 1 (by rfl) ⟨511727, by rfl⟩ : syracuseStep 682303 = 1023455) B1023455
theorem B911807 : Blo 401768 911807 := bstep (se 1 (by rfl) ⟨683855, by rfl⟩ : syracuseStep 911807 = 1367711) B1367711
theorem B11069959 : Blo 401768 11069959 := bstep (se 1 (by rfl) ⟨8302469, by rfl⟩ : syracuseStep 11069959 = 16604939) B16604939
theorem B683039 : Blo 401768 683039 := bstep (se 1 (by rfl) ⟨512279, by rfl⟩ : syracuseStep 683039 = 1024559) B1024559
theorem B912761 : Blo 401768 912761 := bstep (se 2 (by rfl) ⟨342285, by rfl⟩ : syracuseStep 912761 = 684571) B684571
theorem B1732225 : Blo 401768 1732225 := bstep (se 2 (by rfl) ⟨649584, by rfl⟩ : syracuseStep 1732225 = 1299169) B1299169
theorem B455791 : Blo 401768 455791 := bstep (se 1 (by rfl) ⟨341843, by rfl⟩ : syracuseStep 455791 = 683687) B683687
theorem B15169427 : Blo 401768 15169427 := bstep (se 1 (by rfl) ⟨11377070, by rfl⟩ : syracuseStep 15169427 = 22754141) B22754141
theorem B1965217 : Blo 401768 1965217 := bstep (se 2 (by rfl) ⟨736956, by rfl⟩ : syracuseStep 1965217 = 1473913) B1473913
theorem B6521573 : Blo 401768 6521573 := bstep (se 4 (by rfl) ⟨611397, by rfl⟩ : syracuseStep 6521573 = 1222795) B1222795
theorem B6554789 : Blo 401768 6554789 := bstep (se 4 (by rfl) ⟨614511, by rfl⟩ : syracuseStep 6554789 = 1229023) B1229023
theorem B4654255 : Blo 401768 4654255 := bstep (se 1 (by rfl) ⟨3490691, by rfl⟩ : syracuseStep 4654255 = 6981383) B6981383
theorem B3443431 : Blo 401768 3443431 := bstep (se 1 (by rfl) ⟨2582573, by rfl⟩ : syracuseStep 3443431 = 5165147) B5165147
theorem B429823 : Blo 401768 429823 := bstep (se 1 (by rfl) ⟨322367, by rfl⟩ : syracuseStep 429823 = 644735) B644735
theorem B5378399 : Blo 401768 5378399 := bstep (se 1 (by rfl) ⟨4033799, by rfl⟩ : syracuseStep 5378399 = 8067599) B8067599
theorem B1021481 : Blo 401768 1021481 := bstep (se 2 (by rfl) ⟨383055, by rfl⟩ : syracuseStep 1021481 = 766111) B766111
theorem B401855 : Blo 401768 401855 := bstep (se 1 (by rfl) ⟨301391, by rfl⟩ : syracuseStep 401855 = 602783) B602783
theorem B402151 : Blo 401768 402151 := bstep (se 1 (by rfl) ⟨301613, by rfl⟩ : syracuseStep 402151 = 603227) B603227
theorem B402159 : Blo 401768 402159 := bstep (se 1 (by rfl) ⟨301619, by rfl⟩ : syracuseStep 402159 = 603239) B603239
theorem B2958601 : Blo 401768 2958601 := bstep (se 2 (by rfl) ⟨1109475, by rfl⟩ : syracuseStep 2958601 = 2218951) B2218951
theorem B403183 : Blo 401768 403183 := bstep (se 1 (by rfl) ⟨302387, by rfl⟩ : syracuseStep 403183 = 604775) B604775
theorem B403455 : Blo 401768 403455 := bstep (se 1 (by rfl) ⟨302591, by rfl⟩ : syracuseStep 403455 = 605183) B605183
theorem B403527 : Blo 401768 403527 := bstep (se 1 (by rfl) ⟨302645, by rfl⟩ : syracuseStep 403527 = 605291) B605291
theorem B404207 : Blo 401768 404207 := bstep (se 1 (by rfl) ⟨303155, by rfl⟩ : syracuseStep 404207 = 606311) B606311
theorem B404511 : Blo 401768 404511 := bstep (se 1 (by rfl) ⟨303383, by rfl⟩ : syracuseStep 404511 = 606767) B606767
theorem B404731 : Blo 401768 404731 := bstep (se 1 (by rfl) ⟨303548, by rfl⟩ : syracuseStep 404731 = 607097) B607097
theorem B404839 : Blo 401768 404839 := bstep (se 1 (by rfl) ⟨303629, by rfl⟩ : syracuseStep 404839 = 607259) B607259
theorem B1748951 : Blo 401768 1748951 := bstep (se 1 (by rfl) ⟨1311713, by rfl⟩ : syracuseStep 1748951 = 2623427) B2623427
theorem B405615 : Blo 401768 405615 := bstep (se 1 (by rfl) ⟨304211, by rfl⟩ : syracuseStep 405615 = 608423) B608423
theorem B766331 : Blo 401768 766331 := bstep (se 1 (by rfl) ⟨574748, by rfl⟩ : syracuseStep 766331 = 1149497) B1149497
theorem B602951 : Blo 401768 602951 := bstep (se 1 (by rfl) ⟨452213, by rfl⟩ : syracuseStep 602951 = 904427) B904427
theorem B603071 : Blo 401768 603071 := bstep (se 1 (by rfl) ⟨452303, by rfl⟩ : syracuseStep 603071 = 904607) B904607
theorem B603551 : Blo 401768 603551 := bstep (se 1 (by rfl) ⟨452663, by rfl⟩ : syracuseStep 603551 = 905327) B905327
theorem B5191391 : Blo 401768 5191391 := bstep (se 1 (by rfl) ⟨3893543, by rfl⟩ : syracuseStep 5191391 = 7787087) B7787087
theorem B14759945 : Blo 401768 14759945 := bstep (se 2 (by rfl) ⟨5534979, by rfl⟩ : syracuseStep 14759945 = 11069959) B11069959
theorem B5477350643 : Blo 401768 5477350643 := bstep (se 1 (by rfl) ⟨4108012982, by rfl⟩ : syracuseStep 5477350643 = 8216025965) B8216025965
theorem B1293671 : Blo 401768 1293671 := bstep (se 1 (by rfl) ⟨970253, by rfl⟩ : syracuseStep 1293671 = 1940507) B1940507
theorem B2309633 : Blo 401768 2309633 := bstep (se 2 (by rfl) ⟨866112, by rfl⟩ : syracuseStep 2309633 = 1732225) B1732225
theorem B605879 : Blo 401768 605879 := bstep (se 1 (by rfl) ⟨454409, by rfl⟩ : syracuseStep 605879 = 908819) B908819
theorem B26296487 : Blo 401768 26296487 := bstep (se 1 (by rfl) ⟨19722365, by rfl⟩ : syracuseStep 26296487 = 39444731) B39444731
theorem B2179739 : Blo 401768 2179739 := bstep (se 1 (by rfl) ⟨1634804, by rfl⟩ : syracuseStep 2179739 = 3269609) B3269609
theorem B1557319 : Blo 401768 1557319 := bstep (se 1 (by rfl) ⟨1167989, by rfl⟩ : syracuseStep 1557319 = 2335979) B2335979
theorem B607103 : Blo 401768 607103 := bstep (se 1 (by rfl) ⟨455327, by rfl⟩ : syracuseStep 607103 = 910655) B910655
theorem B607721 : Blo 401768 607721 := bstep (se 2 (by rfl) ⟨227895, by rfl⟩ : syracuseStep 607721 = 455791) B455791
theorem B607871 : Blo 401768 607871 := bstep (se 1 (by rfl) ⟨455903, by rfl⟩ : syracuseStep 607871 = 911807) B911807
theorem B608507 : Blo 401768 608507 := bstep (se 1 (by rfl) ⟨456380, by rfl⟩ : syracuseStep 608507 = 912761) B912761
theorem B904283 : Blo 401768 904283 := bstep (se 1 (by rfl) ⟨678212, by rfl⟩ : syracuseStep 904283 = 1356425) B1356425
theorem B23383403 : Blo 401768 23383403 := bstep (se 1 (by rfl) ⟨17537552, by rfl⟩ : syracuseStep 23383403 = 35075105) B35075105
theorem B10112951 : Blo 401768 10112951 := bstep (se 1 (by rfl) ⟨7584713, by rfl⟩ : syracuseStep 10112951 = 15169427) B15169427
theorem B513535 : Blo 401768 513535 := bstep (se 1 (by rfl) ⟨385151, by rfl⟩ : syracuseStep 513535 = 770303) B770303
theorem B2053673 : Blo 401768 2053673 := bstep (se 2 (by rfl) ⟨770127, by rfl⟩ : syracuseStep 2053673 = 1540255) B1540255
theorem B1365821 : Blo 401768 1365821 := bstep (se 3 (by rfl) ⟨256091, by rfl⟩ : syracuseStep 1365821 = 512183) B512183
theorem B5167151 : Blo 401768 5167151 := bstep (se 1 (by rfl) ⟨3875363, by rfl⟩ : syracuseStep 5167151 = 7750727) B7750727
theorem B678199 : Blo 401768 678199 := bstep (se 1 (by rfl) ⟨508649, by rfl⟩ : syracuseStep 678199 = 1017299) B1017299
theorem B5527973 : Blo 401768 5527973 := bstep (se 4 (by rfl) ⟨518247, by rfl⟩ : syracuseStep 5527973 = 1036495) B1036495
theorem B2185967 : Blo 401768 2185967 := bstep (se 1 (by rfl) ⟨1639475, by rfl⟩ : syracuseStep 2185967 = 3278951) B3278951
theorem B908063 : Blo 401768 908063 := bstep (se 1 (by rfl) ⟨681047, by rfl⟩ : syracuseStep 908063 = 1362095) B1362095
theorem B3988511 : Blo 401768 3988511 := bstep (se 1 (by rfl) ⟨2991383, by rfl⟩ : syracuseStep 3988511 = 5982767) B5982767
theorem B908351 : Blo 401768 908351 := bstep (se 1 (by rfl) ⟨681263, by rfl⟩ : syracuseStep 908351 = 1362527) B1362527
theorem B1531325 : Blo 401768 1531325 := bstep (se 3 (by rfl) ⟨287123, by rfl⟩ : syracuseStep 1531325 = 574247) B574247
theorem B909737 : Blo 401768 909737 := bstep (se 2 (by rfl) ⟨341151, by rfl⟩ : syracuseStep 909737 = 682303) B682303
theorem B3072491 : Blo 401768 3072491 := bstep (se 1 (by rfl) ⟨2304368, by rfl⟩ : syracuseStep 3072491 = 4608737) B4608737
theorem B680575 : Blo 401768 680575 := bstep (se 1 (by rfl) ⟨510431, by rfl⟩ : syracuseStep 680575 = 1020863) B1020863
theorem B910619 : Blo 401768 910619 := bstep (se 1 (by rfl) ⟨682964, by rfl⟩ : syracuseStep 910619 = 1365929) B1365929
theorem B452767 : Blo 401768 452767 := bstep (se 1 (by rfl) ⟨339575, by rfl⟩ : syracuseStep 452767 = 679151) B679151
theorem B1534909 : Blo 401768 1534909 := bstep (se 3 (by rfl) ⟨287795, by rfl⟩ : syracuseStep 1534909 = 575591) B575591
theorem B684139 : Blo 401768 684139 := bstep (se 1 (by rfl) ⟨513104, by rfl⟩ : syracuseStep 684139 = 1026209) B1026209
theorem B455359 : Blo 401768 455359 := bstep (se 1 (by rfl) ⟨341519, by rfl⟩ : syracuseStep 455359 = 683039) B683039
theorem B95777477 : Blo 401768 95777477 := bstep (se 4 (by rfl) ⟨8979138, by rfl⟩ : syracuseStep 95777477 = 17958277) B17958277
theorem B1538615 : Blo 401768 1538615 := bstep (se 1 (by rfl) ⟨1153961, by rfl⟩ : syracuseStep 1538615 = 2307923) B2307923
theorem B2620289 : Blo 401768 2620289 := bstep (se 2 (by rfl) ⟨982608, by rfl⟩ : syracuseStep 2620289 = 1965217) B1965217
theorem B22314167 : Blo 401768 22314167 := bstep (se 1 (by rfl) ⟨16735625, by rfl⟩ : syracuseStep 22314167 = 33471251) B33471251
theorem B22052341 : Blo 401768 22052341 := bstep (se 5 (by rfl) ⟨1033703, by rfl⟩ : syracuseStep 22052341 = 2067407) B2067407
theorem B1146649 : Blo 401768 1146649 := bstep (se 2 (by rfl) ⟨429993, by rfl⟩ : syracuseStep 1146649 = 859987) B859987
theorem B17530991 : Blo 401768 17530991 := bstep (se 1 (by rfl) ⟨13148243, by rfl⟩ : syracuseStep 17530991 = 26296487) B26296487
theorem B4591241 : Blo 401768 4591241 := bstep (se 2 (by rfl) ⟨1721715, by rfl⟩ : syracuseStep 4591241 = 3443431) B3443431
theorem B3444767 : Blo 401768 3444767 := bstep (se 1 (by rfl) ⟨2583575, by rfl⟩ : syracuseStep 3444767 = 5167151) B5167151
theorem B2659007 : Blo 401768 2659007 := bstep (se 1 (by rfl) ⟨1994255, by rfl⟩ : syracuseStep 2659007 = 3988511) B3988511
theorem B1020883 : Blo 401768 1020883 := bstep (se 1 (by rfl) ⟨765662, by rfl⟩ : syracuseStep 1020883 = 1531325) B1531325
theorem B401967 : Blo 401768 401967 := bstep (se 1 (by rfl) ⟨301475, by rfl⟩ : syracuseStep 401967 = 602951) B602951
theorem B402047 : Blo 401768 402047 := bstep (se 1 (by rfl) ⟨301535, by rfl⟩ : syracuseStep 402047 = 603071) B603071
theorem B3449789 : Blo 401768 3449789 := bstep (se 3 (by rfl) ⟨646835, by rfl⟩ : syracuseStep 3449789 = 1293671) B1293671
theorem B402367 : Blo 401768 402367 := bstep (se 1 (by rfl) ⟨301775, by rfl⟩ : syracuseStep 402367 = 603551) B603551
theorem B9839963 : Blo 401768 9839963 := bstep (se 1 (by rfl) ⟨7379972, by rfl⟩ : syracuseStep 9839963 = 14759945) B14759945
theorem B1025743 : Blo 401768 1025743 := bstep (se 1 (by rfl) ⟨769307, by rfl⟩ : syracuseStep 1025743 = 1538615) B1538615
theorem B1746859 : Blo 401768 1746859 := bstep (se 1 (by rfl) ⟨1310144, by rfl⟩ : syracuseStep 1746859 = 2620289) B2620289
theorem B29403121 : Blo 401768 29403121 := bstep (se 2 (by rfl) ⟨11026170, by rfl⟩ : syracuseStep 29403121 = 22052341) B22052341
theorem B403919 : Blo 401768 403919 := bstep (se 1 (by rfl) ⟨302939, by rfl⟩ : syracuseStep 403919 = 605879) B605879
theorem B1453159 : Blo 401768 1453159 := bstep (se 1 (by rfl) ⟨1089869, by rfl⟩ : syracuseStep 1453159 = 2179739) B2179739
theorem B404735 : Blo 401768 404735 := bstep (se 1 (by rfl) ⟨303551, by rfl⟩ : syracuseStep 404735 = 607103) B607103
theorem B4369859 : Blo 401768 4369859 := bstep (se 1 (by rfl) ⟨3277394, by rfl⟩ : syracuseStep 4369859 = 6554789) B6554789
theorem B405147 : Blo 401768 405147 := bstep (se 1 (by rfl) ⟨303860, by rfl⟩ : syracuseStep 405147 = 607721) B607721
theorem B405247 : Blo 401768 405247 := bstep (se 1 (by rfl) ⟨303935, by rfl⟩ : syracuseStep 405247 = 607871) B607871
theorem B2076425 : Blo 401768 2076425 := bstep (se 2 (by rfl) ⟨778659, by rfl⟩ : syracuseStep 2076425 = 1557319) B1557319
theorem B405671 : Blo 401768 405671 := bstep (se 1 (by rfl) ⟨304253, by rfl⟩ : syracuseStep 405671 = 608507) B608507
theorem B6205673 : Blo 401768 6205673 := bstep (se 2 (by rfl) ⟨2327127, by rfl⟩ : syracuseStep 6205673 = 4654255) B4654255
theorem B3944801 : Blo 401768 3944801 := bstep (se 2 (by rfl) ⟨1479300, by rfl⟩ : syracuseStep 3944801 = 2958601) B2958601
theorem B602855 : Blo 401768 602855 := bstep (se 1 (by rfl) ⟨452141, by rfl⟩ : syracuseStep 602855 = 904283) B904283
theorem B603689 : Blo 401768 603689 := bstep (se 2 (by rfl) ⟨226383, by rfl⟩ : syracuseStep 603689 = 452767) B452767
theorem B3585599 : Blo 401768 3585599 := bstep (se 1 (by rfl) ⟨2689199, by rfl⟩ : syracuseStep 3585599 = 5378399) B5378399
theorem B2046545 : Blo 401768 2046545 := bstep (se 2 (by rfl) ⟨767454, by rfl⟩ : syracuseStep 2046545 = 1534909) B1534909
theorem B605375 : Blo 401768 605375 := bstep (se 1 (by rfl) ⟨454031, by rfl⟩ : syracuseStep 605375 = 908063) B908063
theorem B605567 : Blo 401768 605567 := bstep (se 1 (by rfl) ⟨454175, by rfl⟩ : syracuseStep 605567 = 908351) B908351
theorem B573097 : Blo 401768 573097 := bstep (se 2 (by rfl) ⟨214911, by rfl⟩ : syracuseStep 573097 = 429823) B429823
theorem B606491 : Blo 401768 606491 := bstep (se 1 (by rfl) ⟨454868, by rfl⟩ : syracuseStep 606491 = 909737) B909737
theorem B2048327 : Blo 401768 2048327 := bstep (se 1 (by rfl) ⟨1536245, by rfl⟩ : syracuseStep 2048327 = 3072491) B3072491
theorem B607079 : Blo 401768 607079 := bstep (se 1 (by rfl) ⟨455309, by rfl⟩ : syracuseStep 607079 = 910619) B910619
theorem B607145 : Blo 401768 607145 := bstep (se 2 (by rfl) ⟨227679, by rfl⟩ : syracuseStep 607145 = 455359) B455359
theorem B1165967 : Blo 401768 1165967 := bstep (se 1 (by rfl) ⟨874475, by rfl⟩ : syracuseStep 1165967 = 1748951) B1748951
theorem B510887 : Blo 401768 510887 := bstep (se 1 (by rfl) ⟨383165, by rfl⟩ : syracuseStep 510887 = 766331) B766331
theorem B904265 : Blo 401768 904265 := bstep (se 2 (by rfl) ⟨339099, by rfl⟩ : syracuseStep 904265 = 678199) B678199
theorem B63851651 : Blo 401768 63851651 := bstep (se 1 (by rfl) ⟨47888738, by rfl⟩ : syracuseStep 63851651 = 95777477) B95777477
theorem B3460927 : Blo 401768 3460927 := bstep (se 1 (by rfl) ⟨2595695, by rfl⟩ : syracuseStep 3460927 = 5191391) B5191391
theorem B1528865 : Blo 401768 1528865 := bstep (se 2 (by rfl) ⟨573324, by rfl⟩ : syracuseStep 1528865 = 1146649) B1146649
theorem B4347715 : Blo 401768 4347715 := bstep (se 1 (by rfl) ⟨3260786, by rfl⟩ : syracuseStep 4347715 = 6521573) B6521573
theorem B907433 : Blo 401768 907433 := bstep (se 2 (by rfl) ⟨340287, by rfl⟩ : syracuseStep 907433 = 680575) B680575
theorem B15588935 : Blo 401768 15588935 := bstep (se 1 (by rfl) ⟨11691701, by rfl⟩ : syracuseStep 15588935 = 23383403) B23383403
theorem B6741967 : Blo 401768 6741967 := bstep (se 1 (by rfl) ⟨5056475, by rfl⟩ : syracuseStep 6741967 = 10112951) B10112951
theorem B680987 : Blo 401768 680987 := bstep (se 1 (by rfl) ⟨510740, by rfl⟩ : syracuseStep 680987 = 1021481) B1021481
theorem B1369115 : Blo 401768 1369115 := bstep (se 1 (by rfl) ⟨1026836, by rfl⟩ : syracuseStep 1369115 = 2053673) B2053673
theorem B910547 : Blo 401768 910547 := bstep (se 1 (by rfl) ⟨682910, by rfl⟩ : syracuseStep 910547 = 1365821) B1365821
theorem B912185 : Blo 401768 912185 := bstep (se 2 (by rfl) ⟨342069, by rfl⟩ : syracuseStep 912185 = 684139) B684139
theorem B14741261 : Blo 401768 14741261 := bstep (se 3 (by rfl) ⟨2763986, by rfl⟩ : syracuseStep 14741261 = 5527973) B5527973
theorem B5829245 : Blo 401768 5829245 := bstep (se 3 (by rfl) ⟨1092983, by rfl⟩ : syracuseStep 5829245 = 2185967) B2185967
theorem B684713 : Blo 401768 684713 := bstep (se 2 (by rfl) ⟨256767, by rfl⟩ : syracuseStep 684713 = 513535) B513535
theorem B14876111 : Blo 401768 14876111 := bstep (se 1 (by rfl) ⟨11157083, by rfl⟩ : syracuseStep 14876111 = 22314167) B22314167
theorem B3651567095 : Blo 401768 3651567095 := bstep (se 1 (by rfl) ⟨2738675321, by rfl⟩ : syracuseStep 3651567095 = 5477350643) B5477350643
theorem B1539755 : Blo 401768 1539755 := bstep (se 1 (by rfl) ⟨1154816, by rfl⟩ : syracuseStep 1539755 = 2309633) B2309633
theorem B16548461 : Blo 401768 16548461 := bstep (se 3 (by rfl) ⟨3102836, by rfl⟩ : syracuseStep 16548461 = 6205673) B6205673
theorem B10519469 : Blo 401768 10519469 := bstep (se 3 (by rfl) ⟨1972400, by rfl⟩ : syracuseStep 10519469 = 3944801) B3944801
theorem B42567767 : Blo 401768 42567767 := bstep (se 1 (by rfl) ⟨31925825, by rfl⟩ : syracuseStep 42567767 = 63851651) B63851651
theorem B2329145 : Blo 401768 2329145 := bstep (se 2 (by rfl) ⟨873429, by rfl⟩ : syracuseStep 2329145 = 1746859) B1746859
theorem B2296511 : Blo 401768 2296511 := bstep (se 1 (by rfl) ⟨1722383, by rfl⟩ : syracuseStep 2296511 = 3444767) B3444767
theorem B1772671 : Blo 401768 1772671 := bstep (se 1 (by rfl) ⟨1329503, by rfl⟩ : syracuseStep 1772671 = 2659007) B2659007
theorem B1019243 : Blo 401768 1019243 := bstep (se 1 (by rfl) ⟨764432, by rfl⟩ : syracuseStep 1019243 = 1528865) B1528865
theorem B10392623 : Blo 401768 10392623 := bstep (se 1 (by rfl) ⟨7794467, by rfl⟩ : syracuseStep 10392623 = 15588935) B15588935
theorem B2299859 : Blo 401768 2299859 := bstep (se 1 (by rfl) ⟨1724894, by rfl⟩ : syracuseStep 2299859 = 3449789) B3449789
theorem B6559975 : Blo 401768 6559975 := bstep (se 1 (by rfl) ⟨4919981, by rfl⟩ : syracuseStep 6559975 = 9839963) B9839963
theorem B1384283 : Blo 401768 1384283 := bstep (se 1 (by rfl) ⟨1038212, by rfl⟩ : syracuseStep 1384283 = 2076425) B2076425
theorem B401903 : Blo 401768 401903 := bstep (se 1 (by rfl) ⟨301427, by rfl⟩ : syracuseStep 401903 = 602855) B602855
theorem B402459 : Blo 401768 402459 := bstep (se 1 (by rfl) ⟨301844, by rfl⟩ : syracuseStep 402459 = 603689) B603689
theorem B403583 : Blo 401768 403583 := bstep (se 1 (by rfl) ⟨302687, by rfl⟩ : syracuseStep 403583 = 605375) B605375
theorem B764129 : Blo 401768 764129 := bstep (se 2 (by rfl) ⟨286548, by rfl⟩ : syracuseStep 764129 = 573097) B573097
theorem B403711 : Blo 401768 403711 := bstep (se 1 (by rfl) ⟨302783, by rfl⟩ : syracuseStep 403711 = 605567) B605567
theorem B2434378063 : Blo 401768 2434378063 := bstep (se 1 (by rfl) ⟨1825783547, by rfl⟩ : syracuseStep 2434378063 = 3651567095) B3651567095
theorem B1026503 : Blo 401768 1026503 := bstep (se 1 (by rfl) ⟨769877, by rfl⟩ : syracuseStep 1026503 = 1539755) B1539755
theorem B8989289 : Blo 401768 8989289 := bstep (se 2 (by rfl) ⟨3370983, by rfl⟩ : syracuseStep 8989289 = 6741967) B6741967
theorem B404327 : Blo 401768 404327 := bstep (se 1 (by rfl) ⟨303245, by rfl⟩ : syracuseStep 404327 = 606491) B606491
theorem B404719 : Blo 401768 404719 := bstep (se 1 (by rfl) ⟨303539, by rfl⟩ : syracuseStep 404719 = 607079) B607079
theorem B404763 : Blo 401768 404763 := bstep (se 1 (by rfl) ⟨303572, by rfl⟩ : syracuseStep 404763 = 607145) B607145
theorem B602843 : Blo 401768 602843 := bstep (se 1 (by rfl) ⟨452132, by rfl⟩ : syracuseStep 602843 = 904265) B904265
theorem B3060827 : Blo 401768 3060827 := bstep (se 1 (by rfl) ⟨2295620, by rfl⟩ : syracuseStep 3060827 = 4591241) B4591241
theorem B39204161 : Blo 401768 39204161 := bstep (se 2 (by rfl) ⟨14701560, by rfl⟩ : syracuseStep 39204161 = 29403121) B29403121
theorem B604955 : Blo 401768 604955 := bstep (se 1 (by rfl) ⟨453716, by rfl⟩ : syracuseStep 604955 = 907433) B907433
theorem B7750181 : Blo 401768 7750181 := bstep (se 4 (by rfl) ⟨726579, by rfl⟩ : syracuseStep 7750181 = 1453159) B1453159
theorem B607031 : Blo 401768 607031 := bstep (se 1 (by rfl) ⟨455273, by rfl⟩ : syracuseStep 607031 = 910547) B910547
theorem B1361177 : Blo 401768 1361177 := bstep (se 2 (by rfl) ⟨510441, by rfl⟩ : syracuseStep 1361177 = 1020883) B1020883
theorem B608123 : Blo 401768 608123 := bstep (se 1 (by rfl) ⟨456092, by rfl⟩ : syracuseStep 608123 = 912185) B912185
theorem B1362365 : Blo 401768 1362365 := bstep (se 3 (by rfl) ⟨255443, by rfl⟩ : syracuseStep 1362365 = 510887) B510887
theorem B3886163 : Blo 401768 3886163 := bstep (se 1 (by rfl) ⟨2914622, by rfl⟩ : syracuseStep 3886163 = 5829245) B5829245
theorem B1364363 : Blo 401768 1364363 := bstep (se 1 (by rfl) ⟨1023272, by rfl⟩ : syracuseStep 1364363 = 2046545) B2046545
theorem B9917407 : Blo 401768 9917407 := bstep (se 1 (by rfl) ⟨7438055, by rfl⟩ : syracuseStep 9917407 = 14876111) B14876111
theorem B11687327 : Blo 401768 11687327 := bstep (se 1 (by rfl) ⟨8765495, by rfl⟩ : syracuseStep 11687327 = 17530991) B17530991
theorem B1365551 : Blo 401768 1365551 := bstep (se 1 (by rfl) ⟨1024163, by rfl⟩ : syracuseStep 1365551 = 2048327) B2048327
theorem B777311 : Blo 401768 777311 := bstep (se 1 (by rfl) ⟨582983, by rfl⟩ : syracuseStep 777311 = 1165967) B1165967
theorem B1367657 : Blo 401768 1367657 := bstep (se 2 (by rfl) ⟨512871, by rfl⟩ : syracuseStep 1367657 = 1025743) B1025743
theorem B4614569 : Blo 401768 4614569 := bstep (se 2 (by rfl) ⟨1730463, by rfl⟩ : syracuseStep 4614569 = 3460927) B3460927
theorem B453991 : Blo 401768 453991 := bstep (se 1 (by rfl) ⟨340493, by rfl⟩ : syracuseStep 453991 = 680987) B680987
theorem B912743 : Blo 401768 912743 := bstep (se 1 (by rfl) ⟨684557, by rfl⟩ : syracuseStep 912743 = 1369115) B1369115
theorem B2913239 : Blo 401768 2913239 := bstep (se 1 (by rfl) ⟨2184929, by rfl⟩ : syracuseStep 2913239 = 4369859) B4369859
theorem B5796953 : Blo 401768 5796953 := bstep (se 2 (by rfl) ⟨2173857, by rfl⟩ : syracuseStep 5796953 = 4347715) B4347715
theorem B9827507 : Blo 401768 9827507 := bstep (se 1 (by rfl) ⟨7370630, by rfl⟩ : syracuseStep 9827507 = 14741261) B14741261
theorem B456475 : Blo 401768 456475 := bstep (se 1 (by rfl) ⟨342356, by rfl⟩ : syracuseStep 456475 = 684713) B684713
theorem B2390399 : Blo 401768 2390399 := bstep (se 1 (by rfl) ⟨1792799, by rfl⟩ : syracuseStep 2390399 = 3585599) B3585599
theorem B7012979 : Blo 401768 7012979 := bstep (se 1 (by rfl) ⟨5259734, by rfl⟩ : syracuseStep 7012979 = 10519469) B10519469
theorem B28378511 : Blo 401768 28378511 := bstep (se 1 (by rfl) ⟨21283883, by rfl⟩ : syracuseStep 28378511 = 42567767) B42567767
theorem B2590775 : Blo 401768 2590775 := bstep (se 1 (by rfl) ⟨1943081, by rfl⟩ : syracuseStep 2590775 = 3886163) B3886163
theorem B3245837417 : Blo 401768 3245837417 := bstep (se 2 (by rfl) ⟨1217189031, by rfl⟩ : syracuseStep 3245837417 = 2434378063) B2434378063
theorem B2363561 : Blo 401768 2363561 := bstep (se 2 (by rfl) ⟨886335, by rfl⟩ : syracuseStep 2363561 = 1772671) B1772671
theorem B52892837 : Blo 401768 52892837 := bstep (se 4 (by rfl) ⟨4958703, by rfl⟩ : syracuseStep 52892837 = 9917407) B9917407
theorem B922855 : Blo 401768 922855 := bstep (se 1 (by rfl) ⟨692141, by rfl⟩ : syracuseStep 922855 = 1384283) B1384283
theorem B401895 : Blo 401768 401895 := bstep (se 1 (by rfl) ⟨301421, by rfl⟩ : syracuseStep 401895 = 602843) B602843
theorem B1942159 : Blo 401768 1942159 := bstep (se 1 (by rfl) ⟨1456619, by rfl⟩ : syracuseStep 1942159 = 2913239) B2913239
theorem B2040551 : Blo 401768 2040551 := bstep (se 1 (by rfl) ⟨1530413, by rfl⟩ : syracuseStep 2040551 = 3060827) B3060827
theorem B403303 : Blo 401768 403303 := bstep (se 1 (by rfl) ⟨302477, by rfl⟩ : syracuseStep 403303 = 604955) B604955
theorem B404687 : Blo 401768 404687 := bstep (se 1 (by rfl) ⟨303515, by rfl⟩ : syracuseStep 404687 = 607031) B607031
theorem B405415 : Blo 401768 405415 := bstep (se 1 (by rfl) ⟨304061, by rfl⟩ : syracuseStep 405415 = 608123) B608123
theorem B1552763 : Blo 401768 1552763 := bstep (se 1 (by rfl) ⟨1164572, by rfl⟩ : syracuseStep 1552763 = 2329145) B2329145
theorem B6928415 : Blo 401768 6928415 := bstep (se 1 (by rfl) ⟨5196311, by rfl⟩ : syracuseStep 6928415 = 10392623) B10392623
theorem B605321 : Blo 401768 605321 := bstep (se 2 (by rfl) ⟨226995, by rfl⟩ : syracuseStep 605321 = 453991) B453991
theorem B509419 : Blo 401768 509419 := bstep (se 1 (by rfl) ⟨382064, by rfl⟩ : syracuseStep 509419 = 764129) B764129
theorem B608495 : Blo 401768 608495 := bstep (se 1 (by rfl) ⟨456371, by rfl⟩ : syracuseStep 608495 = 912743) B912743
theorem B608633 : Blo 401768 608633 := bstep (se 2 (by rfl) ⟨228237, by rfl⟩ : syracuseStep 608633 = 456475) B456475
theorem B26136107 : Blo 401768 26136107 := bstep (se 1 (by rfl) ⟨19602080, by rfl⟩ : syracuseStep 26136107 = 39204161) B39204161
theorem B1593599 : Blo 401768 1593599 := bstep (se 1 (by rfl) ⟨1195199, by rfl⟩ : syracuseStep 1593599 = 2390399) B2390399
theorem B5166787 : Blo 401768 5166787 := bstep (se 1 (by rfl) ⟨3875090, by rfl⟩ : syracuseStep 5166787 = 7750181) B7750181
theorem B11032307 : Blo 401768 11032307 := bstep (se 1 (by rfl) ⟨8274230, by rfl⟩ : syracuseStep 11032307 = 16548461) B16548461
theorem B907451 : Blo 401768 907451 := bstep (se 1 (by rfl) ⟨680588, by rfl⟩ : syracuseStep 907451 = 1361177) B1361177
theorem B908243 : Blo 401768 908243 := bstep (se 1 (by rfl) ⟨681182, by rfl⟩ : syracuseStep 908243 = 1362365) B1362365
theorem B1531007 : Blo 401768 1531007 := bstep (se 1 (by rfl) ⟨1148255, by rfl⟩ : syracuseStep 1531007 = 2296511) B2296511
theorem B679495 : Blo 401768 679495 := bstep (se 1 (by rfl) ⟨509621, by rfl⟩ : syracuseStep 679495 = 1019243) B1019243
theorem B909575 : Blo 401768 909575 := bstep (se 1 (by rfl) ⟨682181, by rfl⟩ : syracuseStep 909575 = 1364363) B1364363
theorem B26206685 : Blo 401768 26206685 := bstep (se 3 (by rfl) ⟨4913753, by rfl⟩ : syracuseStep 26206685 = 9827507) B9827507
theorem B7791551 : Blo 401768 7791551 := bstep (se 1 (by rfl) ⟨5843663, by rfl⟩ : syracuseStep 7791551 = 11687327) B11687327
theorem B910367 : Blo 401768 910367 := bstep (se 1 (by rfl) ⟨682775, by rfl⟩ : syracuseStep 910367 = 1365551) B1365551
theorem B1533239 : Blo 401768 1533239 := bstep (se 1 (by rfl) ⟨1149929, by rfl⟩ : syracuseStep 1533239 = 2299859) B2299859
theorem B518207 : Blo 401768 518207 := bstep (se 1 (by rfl) ⟨388655, by rfl⟩ : syracuseStep 518207 = 777311) B777311
theorem B911771 : Blo 401768 911771 := bstep (se 1 (by rfl) ⟨683828, by rfl⟩ : syracuseStep 911771 = 1367657) B1367657
theorem B3076379 : Blo 401768 3076379 := bstep (se 1 (by rfl) ⟨2307284, by rfl⟩ : syracuseStep 3076379 = 4614569) B4614569
theorem B684335 : Blo 401768 684335 := bstep (se 1 (by rfl) ⟨513251, by rfl⟩ : syracuseStep 684335 = 1026503) B1026503
theorem B5992859 : Blo 401768 5992859 := bstep (se 1 (by rfl) ⟨4494644, by rfl⟩ : syracuseStep 5992859 = 8989289) B8989289
theorem B8746633 : Blo 401768 8746633 := bstep (se 2 (by rfl) ⟨3279987, by rfl⟩ : syracuseStep 8746633 = 6559975) B6559975
theorem B3864635 : Blo 401768 3864635 := bstep (se 1 (by rfl) ⟨2898476, by rfl⟩ : syracuseStep 3864635 = 5796953) B5796953
theorem B2589545 : Blo 401768 2589545 := bstep (se 2 (by rfl) ⟨971079, by rfl⟩ : syracuseStep 2589545 = 1942159) B1942159
theorem B1575707 : Blo 401768 1575707 := bstep (se 1 (by rfl) ⟨1181780, by rfl⟩ : syracuseStep 1575707 = 2363561) B2363561
theorem B35261891 : Blo 401768 35261891 := bstep (se 1 (by rfl) ⟨26446418, by rfl⟩ : syracuseStep 35261891 = 52892837) B52892837
theorem B1020671 : Blo 401768 1020671 := bstep (se 1 (by rfl) ⟨765503, by rfl⟩ : syracuseStep 1020671 = 1531007) B1531007
theorem B17471123 : Blo 401768 17471123 := bstep (se 1 (by rfl) ⟨13103342, by rfl⟩ : syracuseStep 17471123 = 26206685) B26206685
theorem B1022159 : Blo 401768 1022159 := bstep (se 1 (by rfl) ⟨766619, by rfl⟩ : syracuseStep 1022159 = 1533239) B1533239
theorem B6889049 : Blo 401768 6889049 := bstep (se 2 (by rfl) ⟨2583393, by rfl⟩ : syracuseStep 6889049 = 5166787) B5166787
theorem B403547 : Blo 401768 403547 := bstep (se 1 (by rfl) ⟨302660, by rfl⟩ : syracuseStep 403547 = 605321) B605321
theorem B18919007 : Blo 401768 18919007 := bstep (se 1 (by rfl) ⟨14189255, by rfl⟩ : syracuseStep 18919007 = 28378511) B28378511
theorem B405663 : Blo 401768 405663 := bstep (se 1 (by rfl) ⟨304247, by rfl⟩ : syracuseStep 405663 = 608495) B608495
theorem B405755 : Blo 401768 405755 := bstep (se 1 (by rfl) ⟨304316, by rfl⟩ : syracuseStep 405755 = 608633) B608633
theorem B7354871 : Blo 401768 7354871 := bstep (se 1 (by rfl) ⟨5516153, by rfl⟩ : syracuseStep 7354871 = 11032307) B11032307
theorem B604967 : Blo 401768 604967 := bstep (se 1 (by rfl) ⟨453725, by rfl⟩ : syracuseStep 604967 = 907451) B907451
theorem B605495 : Blo 401768 605495 := bstep (se 1 (by rfl) ⟨454121, by rfl⟩ : syracuseStep 605495 = 908243) B908243
theorem B606383 : Blo 401768 606383 := bstep (se 1 (by rfl) ⟨454787, by rfl⟩ : syracuseStep 606383 = 909575) B909575
theorem B1360367 : Blo 401768 1360367 := bstep (se 1 (by rfl) ⟨1020275, by rfl⟩ : syracuseStep 1360367 = 2040551) B2040551
theorem B5194367 : Blo 401768 5194367 := bstep (se 1 (by rfl) ⟨3895775, by rfl⟩ : syracuseStep 5194367 = 7791551) B7791551
theorem B606911 : Blo 401768 606911 := bstep (se 1 (by rfl) ⟨455183, by rfl⟩ : syracuseStep 606911 = 910367) B910367
theorem B607847 : Blo 401768 607847 := bstep (se 1 (by rfl) ⟨455885, by rfl⟩ : syracuseStep 607847 = 911771) B911771
theorem B1230473 : Blo 401768 1230473 := bstep (se 2 (by rfl) ⟨461427, by rfl⟩ : syracuseStep 1230473 = 922855) B922855
theorem B2050919 : Blo 401768 2050919 := bstep (se 1 (by rfl) ⟨1538189, by rfl⟩ : syracuseStep 2050919 = 3076379) B3076379
theorem B1035175 : Blo 401768 1035175 := bstep (se 1 (by rfl) ⟨776381, by rfl⟩ : syracuseStep 1035175 = 1552763) B1552763
theorem B2576423 : Blo 401768 2576423 := bstep (se 1 (by rfl) ⟨1932317, by rfl⟩ : syracuseStep 2576423 = 3864635) B3864635
theorem B905993 : Blo 401768 905993 := bstep (se 2 (by rfl) ⟨339747, by rfl⟩ : syracuseStep 905993 = 679495) B679495
theorem B4675319 : Blo 401768 4675319 := bstep (se 1 (by rfl) ⟨3506489, by rfl⟩ : syracuseStep 4675319 = 7012979) B7012979
theorem B5527541 : Blo 401768 5527541 := bstep (se 5 (by rfl) ⟨259103, by rfl⟩ : syracuseStep 5527541 = 518207) B518207
theorem B4249597 : Blo 401768 4249597 := bstep (se 3 (by rfl) ⟨796799, by rfl⟩ : syracuseStep 4249597 = 1593599) B1593599
theorem B1727183 : Blo 401768 1727183 := bstep (se 1 (by rfl) ⟨1295387, by rfl⟩ : syracuseStep 1727183 = 2590775) B2590775
theorem B679225 : Blo 401768 679225 := bstep (se 2 (by rfl) ⟨254709, by rfl⟩ : syracuseStep 679225 = 509419) B509419
theorem B2163891611 : Blo 401768 2163891611 := bstep (se 1 (by rfl) ⟨1622918708, by rfl⟩ : syracuseStep 2163891611 = 3245837417) B3245837417
theorem B17424071 : Blo 401768 17424071 := bstep (se 1 (by rfl) ⟨13068053, by rfl⟩ : syracuseStep 17424071 = 26136107) B26136107
theorem B11662177 : Blo 401768 11662177 := bstep (se 2 (by rfl) ⟨4373316, by rfl⟩ : syracuseStep 11662177 = 8746633) B8746633
theorem B456223 : Blo 401768 456223 := bstep (se 1 (by rfl) ⟨342167, by rfl⟩ : syracuseStep 456223 = 684335) B684335
theorem B3995239 : Blo 401768 3995239 := bstep (se 1 (by rfl) ⟨2996429, by rfl⟩ : syracuseStep 3995239 = 5992859) B5992859
theorem B4618943 : Blo 401768 4618943 := bstep (se 1 (by rfl) ⟨3464207, by rfl⟩ : syracuseStep 4618943 = 6928415) B6928415
theorem B820315 : Blo 401768 820315 := bstep (se 1 (by rfl) ⟨615236, by rfl⟩ : syracuseStep 820315 = 1230473) B1230473
theorem B3116879 : Blo 401768 3116879 := bstep (se 1 (by rfl) ⟨2337659, by rfl⟩ : syracuseStep 3116879 = 4675319) B4675319
theorem B1380233 : Blo 401768 1380233 := bstep (se 2 (by rfl) ⟨517587, by rfl⟩ : syracuseStep 1380233 = 1035175) B1035175
theorem B4592699 : Blo 401768 4592699 := bstep (se 1 (by rfl) ⟨3444524, by rfl⟩ : syracuseStep 4592699 = 6889049) B6889049
theorem B4201885 : Blo 401768 4201885 := bstep (se 3 (by rfl) ⟨787853, by rfl⟩ : syracuseStep 4201885 = 1575707) B1575707
theorem B403311 : Blo 401768 403311 := bstep (se 1 (by rfl) ⟨302483, by rfl⟩ : syracuseStep 403311 = 604967) B604967
theorem B403663 : Blo 401768 403663 := bstep (se 1 (by rfl) ⟨302747, by rfl⟩ : syracuseStep 403663 = 605495) B605495
theorem B404255 : Blo 401768 404255 := bstep (se 1 (by rfl) ⟨303191, by rfl⟩ : syracuseStep 404255 = 606383) B606383
theorem B404607 : Blo 401768 404607 := bstep (se 1 (by rfl) ⟨303455, by rfl⟩ : syracuseStep 404607 = 606911) B606911
theorem B405231 : Blo 401768 405231 := bstep (se 1 (by rfl) ⟨303923, by rfl⟩ : syracuseStep 405231 = 607847) B607847
theorem B23507927 : Blo 401768 23507927 := bstep (se 1 (by rfl) ⟨17630945, by rfl⟩ : syracuseStep 23507927 = 35261891) B35261891
theorem B1717615 : Blo 401768 1717615 := bstep (se 1 (by rfl) ⟨1288211, by rfl⟩ : syracuseStep 1717615 = 2576423) B2576423
theorem B603995 : Blo 401768 603995 := bstep (se 1 (by rfl) ⟨452996, by rfl⟩ : syracuseStep 603995 = 905993) B905993
theorem B11647415 : Blo 401768 11647415 := bstep (se 1 (by rfl) ⟨8735561, by rfl⟩ : syracuseStep 11647415 = 17471123) B17471123
theorem B3685027 : Blo 401768 3685027 := bstep (se 1 (by rfl) ⟨2763770, by rfl⟩ : syracuseStep 3685027 = 5527541) B5527541
theorem B1442594407 : Blo 401768 1442594407 := bstep (se 1 (by rfl) ⟨1081945805, by rfl⟩ : syracuseStep 1442594407 = 2163891611) B2163891611
theorem B11616047 : Blo 401768 11616047 := bstep (se 1 (by rfl) ⟨8712035, by rfl⟩ : syracuseStep 11616047 = 17424071) B17424071
theorem B15549569 : Blo 401768 15549569 := bstep (se 2 (by rfl) ⟨5831088, by rfl⟩ : syracuseStep 15549569 = 11662177) B11662177
theorem B4605821 : Blo 401768 4605821 := bstep (se 3 (by rfl) ⟨863591, by rfl⟩ : syracuseStep 4605821 = 1727183) B1727183
theorem B608297 : Blo 401768 608297 := bstep (se 2 (by rfl) ⟨228111, by rfl⟩ : syracuseStep 608297 = 456223) B456223
theorem B5326985 : Blo 401768 5326985 := bstep (se 2 (by rfl) ⟨1997619, by rfl⟩ : syracuseStep 5326985 = 3995239) B3995239
theorem B4903247 : Blo 401768 4903247 := bstep (se 1 (by rfl) ⟨3677435, by rfl⟩ : syracuseStep 4903247 = 7354871) B7354871
theorem B905633 : Blo 401768 905633 := bstep (se 2 (by rfl) ⟨339612, by rfl⟩ : syracuseStep 905633 = 679225) B679225
theorem B906911 : Blo 401768 906911 := bstep (se 1 (by rfl) ⟨680183, by rfl⟩ : syracuseStep 906911 = 1360367) B1360367
theorem B3462911 : Blo 401768 3462911 := bstep (se 1 (by rfl) ⟨2597183, by rfl⟩ : syracuseStep 3462911 = 5194367) B5194367
theorem B1726363 : Blo 401768 1726363 := bstep (se 1 (by rfl) ⟨1294772, by rfl⟩ : syracuseStep 1726363 = 2589545) B2589545
theorem B1367279 : Blo 401768 1367279 := bstep (se 1 (by rfl) ⟨1025459, by rfl⟩ : syracuseStep 1367279 = 2050919) B2050919
theorem B680447 : Blo 401768 680447 := bstep (se 1 (by rfl) ⟨510335, by rfl⟩ : syracuseStep 680447 = 1020671) B1020671
theorem B681439 : Blo 401768 681439 := bstep (se 1 (by rfl) ⟨511079, by rfl⟩ : syracuseStep 681439 = 1022159) B1022159
theorem B12612671 : Blo 401768 12612671 := bstep (se 1 (by rfl) ⟨9459503, by rfl⟩ : syracuseStep 12612671 = 18919007) B18919007
theorem B5666129 : Blo 401768 5666129 := bstep (se 2 (by rfl) ⟨2124798, by rfl⟩ : syracuseStep 5666129 = 4249597) B4249597
theorem B3079295 : Blo 401768 3079295 := bstep (se 1 (by rfl) ⟨2309471, by rfl⟩ : syracuseStep 3079295 = 4618943) B4618943
theorem B920155 : Blo 401768 920155 := bstep (se 1 (by rfl) ⟨690116, by rfl⟩ : syracuseStep 920155 = 1380233) B1380233
theorem B2301817 : Blo 401768 2301817 := bstep (se 2 (by rfl) ⟨863181, by rfl⟩ : syracuseStep 2301817 = 1726363) B1726363
theorem B15671951 : Blo 401768 15671951 := bstep (se 1 (by rfl) ⟨11753963, by rfl⟩ : syracuseStep 15671951 = 23507927) B23507927
theorem B3777419 : Blo 401768 3777419 := bstep (se 1 (by rfl) ⟨2833064, by rfl⟩ : syracuseStep 3777419 = 5666129) B5666129
theorem B402663 : Blo 401768 402663 := bstep (se 1 (by rfl) ⟨301997, by rfl⟩ : syracuseStep 402663 = 603995) B603995
theorem B1923459209 : Blo 401768 1923459209 := bstep (se 2 (by rfl) ⟨721297203, by rfl⟩ : syracuseStep 1923459209 = 1442594407) B1442594407
theorem B7744031 : Blo 401768 7744031 := bstep (se 1 (by rfl) ⟨5808023, by rfl⟩ : syracuseStep 7744031 = 11616047) B11616047
theorem B10366379 : Blo 401768 10366379 := bstep (se 1 (by rfl) ⟨7774784, by rfl⟩ : syracuseStep 10366379 = 15549569) B15549569
theorem B405531 : Blo 401768 405531 := bstep (se 1 (by rfl) ⟨304148, by rfl⟩ : syracuseStep 405531 = 608297) B608297
theorem B3551323 : Blo 401768 3551323 := bstep (se 1 (by rfl) ⟨2663492, by rfl⟩ : syracuseStep 3551323 = 5326985) B5326985
theorem B1093753 : Blo 401768 1093753 := bstep (se 2 (by rfl) ⟨410157, by rfl⟩ : syracuseStep 1093753 = 820315) B820315
theorem B2077919 : Blo 401768 2077919 := bstep (se 1 (by rfl) ⟨1558439, by rfl⟩ : syracuseStep 2077919 = 3116879) B3116879
theorem B603755 : Blo 401768 603755 := bstep (se 1 (by rfl) ⟨452816, by rfl⟩ : syracuseStep 603755 = 905633) B905633
theorem B3061799 : Blo 401768 3061799 := bstep (se 1 (by rfl) ⟨2296349, by rfl⟩ : syracuseStep 3061799 = 4592699) B4592699
theorem B604607 : Blo 401768 604607 := bstep (se 1 (by rfl) ⟨453455, by rfl⟩ : syracuseStep 604607 = 906911) B906911
theorem B2308607 : Blo 401768 2308607 := bstep (se 1 (by rfl) ⟨1731455, by rfl⟩ : syracuseStep 2308607 = 3462911) B3462911
theorem B8408447 : Blo 401768 8408447 := bstep (se 1 (by rfl) ⟨6306335, by rfl⟩ : syracuseStep 8408447 = 12612671) B12612671
theorem B2052863 : Blo 401768 2052863 := bstep (se 1 (by rfl) ⟨1539647, by rfl⟩ : syracuseStep 2052863 = 3079295) B3079295
theorem B3070547 : Blo 401768 3070547 := bstep (se 1 (by rfl) ⟨2302910, by rfl⟩ : syracuseStep 3070547 = 4605821) B4605821
theorem B908585 : Blo 401768 908585 := bstep (se 2 (by rfl) ⟨340719, by rfl⟩ : syracuseStep 908585 = 681439) B681439
theorem B3268831 : Blo 401768 3268831 := bstep (se 1 (by rfl) ⟨2451623, by rfl⟩ : syracuseStep 3268831 = 4903247) B4903247
theorem B911519 : Blo 401768 911519 := bstep (se 1 (by rfl) ⟨683639, by rfl⟩ : syracuseStep 911519 = 1367279) B1367279
theorem B453631 : Blo 401768 453631 := bstep (se 1 (by rfl) ⟨340223, by rfl⟩ : syracuseStep 453631 = 680447) B680447
theorem B2290153 : Blo 401768 2290153 := bstep (se 2 (by rfl) ⟨858807, by rfl⟩ : syracuseStep 2290153 = 1717615) B1717615
theorem B22410053 : Blo 401768 22410053 := bstep (se 4 (by rfl) ⟨2100942, by rfl⟩ : syracuseStep 22410053 = 4201885) B4201885
theorem B4913369 : Blo 401768 4913369 := bstep (se 2 (by rfl) ⟨1842513, by rfl⟩ : syracuseStep 4913369 = 3685027) B3685027
theorem B7764943 : Blo 401768 7764943 := bstep (se 1 (by rfl) ⟨5823707, by rfl⟩ : syracuseStep 7764943 = 11647415) B11647415
theorem B4358441 : Blo 401768 4358441 := bstep (se 2 (by rfl) ⟨1634415, by rfl⟩ : syracuseStep 4358441 = 3268831) B3268831
theorem B5605631 : Blo 401768 5605631 := bstep (se 1 (by rfl) ⟨4204223, by rfl⟩ : syracuseStep 5605631 = 8408447) B8408447
theorem B3053537 : Blo 401768 3053537 := bstep (se 2 (by rfl) ⟨1145076, by rfl⟩ : syracuseStep 3053537 = 2290153) B2290153
theorem B1385279 : Blo 401768 1385279 := bstep (se 1 (by rfl) ⟨1038959, by rfl⟩ : syracuseStep 1385279 = 2077919) B2077919
theorem B402503 : Blo 401768 402503 := bstep (se 1 (by rfl) ⟨301877, by rfl⟩ : syracuseStep 402503 = 603755) B603755
theorem B2041199 : Blo 401768 2041199 := bstep (se 1 (by rfl) ⟨1530899, by rfl⟩ : syracuseStep 2041199 = 3061799) B3061799
theorem B403071 : Blo 401768 403071 := bstep (se 1 (by rfl) ⟨302303, by rfl⟩ : syracuseStep 403071 = 604607) B604607
theorem B10073117 : Blo 401768 10073117 := bstep (se 3 (by rfl) ⟨1888709, by rfl⟩ : syracuseStep 10073117 = 3777419) B3777419
theorem B1226873 : Blo 401768 1226873 := bstep (se 2 (by rfl) ⟨460077, by rfl⟩ : syracuseStep 1226873 = 920155) B920155
theorem B604841 : Blo 401768 604841 := bstep (se 2 (by rfl) ⟨226815, by rfl⟩ : syracuseStep 604841 = 453631) B453631
theorem B2047031 : Blo 401768 2047031 := bstep (se 1 (by rfl) ⟨1535273, by rfl⟩ : syracuseStep 2047031 = 3070547) B3070547
theorem B605723 : Blo 401768 605723 := bstep (se 1 (by rfl) ⟨454292, by rfl⟩ : syracuseStep 605723 = 908585) B908585
theorem B4735097 : Blo 401768 4735097 := bstep (se 2 (by rfl) ⟨1775661, by rfl⟩ : syracuseStep 4735097 = 3551323) B3551323
theorem B1458337 : Blo 401768 1458337 := bstep (se 2 (by rfl) ⟨546876, by rfl⟩ : syracuseStep 1458337 = 1093753) B1093753
theorem B607679 : Blo 401768 607679 := bstep (se 1 (by rfl) ⟨455759, by rfl⟩ : syracuseStep 607679 = 911519) B911519
theorem B5162687 : Blo 401768 5162687 := bstep (se 1 (by rfl) ⟨3872015, by rfl⟩ : syracuseStep 5162687 = 7744031) B7744031
theorem B3069089 : Blo 401768 3069089 := bstep (se 2 (by rfl) ⟨1150908, by rfl⟩ : syracuseStep 3069089 = 2301817) B2301817
theorem B1368575 : Blo 401768 1368575 := bstep (se 1 (by rfl) ⟨1026431, by rfl⟩ : syracuseStep 1368575 = 2052863) B2052863
theorem B10447967 : Blo 401768 10447967 := bstep (se 1 (by rfl) ⟨7835975, by rfl⟩ : syracuseStep 10447967 = 15671951) B15671951
theorem B1282306139 : Blo 401768 1282306139 := bstep (se 1 (by rfl) ⟨961729604, by rfl⟩ : syracuseStep 1282306139 = 1923459209) B1923459209
theorem B6910919 : Blo 401768 6910919 := bstep (se 1 (by rfl) ⟨5183189, by rfl⟩ : syracuseStep 6910919 = 10366379) B10366379
theorem B14940035 : Blo 401768 14940035 := bstep (se 1 (by rfl) ⟨11205026, by rfl⟩ : syracuseStep 14940035 = 22410053) B22410053
theorem B10353257 : Blo 401768 10353257 := bstep (se 2 (by rfl) ⟨3882471, by rfl⟩ : syracuseStep 10353257 = 7764943) B7764943
theorem B3275579 : Blo 401768 3275579 := bstep (se 1 (by rfl) ⟨2456684, by rfl⟩ : syracuseStep 3275579 = 4913369) B4913369
theorem B1539071 : Blo 401768 1539071 := bstep (se 1 (by rfl) ⟨1154303, by rfl⟩ : syracuseStep 1539071 = 2308607) B2308607
theorem B3441791 : Blo 401768 3441791 := bstep (se 1 (by rfl) ⟨2581343, by rfl⟩ : syracuseStep 3441791 = 5162687) B5162687
theorem B3737087 : Blo 401768 3737087 := bstep (se 1 (by rfl) ⟨2802815, by rfl⟩ : syracuseStep 3737087 = 5605631) B5605631
theorem B2035691 : Blo 401768 2035691 := bstep (se 1 (by rfl) ⟨1526768, by rfl⟩ : syracuseStep 2035691 = 3053537) B3053537
theorem B923519 : Blo 401768 923519 := bstep (se 1 (by rfl) ⟨692639, by rfl⟩ : syracuseStep 923519 = 1385279) B1385279
theorem B403227 : Blo 401768 403227 := bstep (se 1 (by rfl) ⟨302420, by rfl⟩ : syracuseStep 403227 = 604841) B604841
theorem B1026047 : Blo 401768 1026047 := bstep (se 1 (by rfl) ⟨769535, by rfl⟩ : syracuseStep 1026047 = 1539071) B1539071
theorem B403815 : Blo 401768 403815 := bstep (se 1 (by rfl) ⟨302861, by rfl⟩ : syracuseStep 403815 = 605723) B605723
theorem B3156731 : Blo 401768 3156731 := bstep (se 1 (by rfl) ⟨2367548, by rfl⟩ : syracuseStep 3156731 = 4735097) B4735097
theorem B1944449 : Blo 401768 1944449 := bstep (se 2 (by rfl) ⟨729168, by rfl⟩ : syracuseStep 1944449 = 1458337) B1458337
theorem B405119 : Blo 401768 405119 := bstep (se 1 (by rfl) ⟨303839, by rfl⟩ : syracuseStep 405119 = 607679) B607679
theorem B2046059 : Blo 401768 2046059 := bstep (se 1 (by rfl) ⟨1534544, by rfl⟩ : syracuseStep 2046059 = 3069089) B3069089
theorem B1360799 : Blo 401768 1360799 := bstep (se 1 (by rfl) ⟨1020599, by rfl⟩ : syracuseStep 1360799 = 2041199) B2041199
theorem B6965311 : Blo 401768 6965311 := bstep (se 1 (by rfl) ⟨5223983, by rfl⟩ : syracuseStep 6965311 = 10447967) B10447967
theorem B8734877 : Blo 401768 8734877 := bstep (se 3 (by rfl) ⟨1637789, by rfl⟩ : syracuseStep 8734877 = 3275579) B3275579
theorem B854870759 : Blo 401768 854870759 := bstep (se 1 (by rfl) ⟨641153069, by rfl⟩ : syracuseStep 854870759 = 1282306139) B1282306139
theorem B4607279 : Blo 401768 4607279 := bstep (se 1 (by rfl) ⟨3455459, by rfl⟩ : syracuseStep 4607279 = 6910919) B6910919
theorem B6902171 : Blo 401768 6902171 := bstep (se 1 (by rfl) ⟨5176628, by rfl⟩ : syracuseStep 6902171 = 10353257) B10353257
theorem B1364687 : Blo 401768 1364687 := bstep (se 1 (by rfl) ⟨1023515, by rfl⟩ : syracuseStep 1364687 = 2047031) B2047031
theorem B2905627 : Blo 401768 2905627 := bstep (se 1 (by rfl) ⟨2179220, by rfl⟩ : syracuseStep 2905627 = 4358441) B4358441
theorem B26861645 : Blo 401768 26861645 := bstep (se 3 (by rfl) ⟨5036558, by rfl⟩ : syracuseStep 26861645 = 10073117) B10073117
theorem B3271661 : Blo 401768 3271661 := bstep (se 3 (by rfl) ⟨613436, by rfl⟩ : syracuseStep 3271661 = 1226873) B1226873
theorem B912383 : Blo 401768 912383 := bstep (se 1 (by rfl) ⟨684287, by rfl⟩ : syracuseStep 912383 = 1368575) B1368575
theorem B9960023 : Blo 401768 9960023 := bstep (se 1 (by rfl) ⟨7470017, by rfl⟩ : syracuseStep 9960023 = 14940035) B14940035
theorem B71631053 : Blo 401768 71631053 := bstep (se 3 (by rfl) ⟨13430822, by rfl⟩ : syracuseStep 71631053 = 26861645) B26861645
theorem B2294527 : Blo 401768 2294527 := bstep (se 1 (by rfl) ⟨1720895, by rfl⟩ : syracuseStep 2294527 = 3441791) B3441791
theorem B2491391 : Blo 401768 2491391 := bstep (se 1 (by rfl) ⟨1868543, by rfl⟩ : syracuseStep 2491391 = 3737087) B3737087
theorem B2462717 : Blo 401768 2462717 := bstep (se 3 (by rfl) ⟨461759, by rfl⟩ : syracuseStep 2462717 = 923519) B923519
theorem B2104487 : Blo 401768 2104487 := bstep (se 1 (by rfl) ⟨1578365, by rfl⟩ : syracuseStep 2104487 = 3156731) B3156731
theorem B3874169 : Blo 401768 3874169 := bstep (se 2 (by rfl) ⟨1452813, by rfl⟩ : syracuseStep 3874169 = 2905627) B2905627
theorem B569913839 : Blo 401768 569913839 := bstep (se 1 (by rfl) ⟨427435379, by rfl⟩ : syracuseStep 569913839 = 854870759) B854870759
theorem B1357127 : Blo 401768 1357127 := bstep (se 1 (by rfl) ⟨1017845, by rfl⟩ : syracuseStep 1357127 = 2035691) B2035691
theorem B9287081 : Blo 401768 9287081 := bstep (se 2 (by rfl) ⟨3482655, by rfl⟩ : syracuseStep 9287081 = 6965311) B6965311
theorem B4601447 : Blo 401768 4601447 := bstep (se 1 (by rfl) ⟨3451085, by rfl⟩ : syracuseStep 4601447 = 6902171) B6902171
theorem B1296299 : Blo 401768 1296299 := bstep (se 1 (by rfl) ⟨972224, by rfl⟩ : syracuseStep 1296299 = 1944449) B1944449
theorem B2181107 : Blo 401768 2181107 := bstep (se 1 (by rfl) ⟨1635830, by rfl⟩ : syracuseStep 2181107 = 3271661) B3271661
theorem B608255 : Blo 401768 608255 := bstep (se 1 (by rfl) ⟨456191, by rfl⟩ : syracuseStep 608255 = 912383) B912383
theorem B1364039 : Blo 401768 1364039 := bstep (se 1 (by rfl) ⟨1023029, by rfl⟩ : syracuseStep 1364039 = 2046059) B2046059
theorem B6640015 : Blo 401768 6640015 := bstep (se 1 (by rfl) ⟨4980011, by rfl⟩ : syracuseStep 6640015 = 9960023) B9960023
theorem B907199 : Blo 401768 907199 := bstep (se 1 (by rfl) ⟨680399, by rfl⟩ : syracuseStep 907199 = 1360799) B1360799
theorem B5823251 : Blo 401768 5823251 := bstep (se 1 (by rfl) ⟨4367438, by rfl⟩ : syracuseStep 5823251 = 8734877) B8734877
theorem B3071519 : Blo 401768 3071519 := bstep (se 1 (by rfl) ⟨2303639, by rfl⟩ : syracuseStep 3071519 = 4607279) B4607279
theorem B909791 : Blo 401768 909791 := bstep (se 1 (by rfl) ⟨682343, by rfl⟩ : syracuseStep 909791 = 1364687) B1364687
theorem B684031 : Blo 401768 684031 := bstep (se 1 (by rfl) ⟨513023, by rfl⟩ : syracuseStep 684031 = 1026047) B1026047
theorem B1641811 : Blo 401768 1641811 := bstep (se 1 (by rfl) ⟨1231358, by rfl⟩ : syracuseStep 1641811 = 2462717) B2462717
theorem B8853353 : Blo 401768 8853353 := bstep (se 2 (by rfl) ⟨3320007, by rfl⟩ : syracuseStep 8853353 = 6640015) B6640015
theorem B47754035 : Blo 401768 47754035 := bstep (se 1 (by rfl) ⟨35815526, by rfl⟩ : syracuseStep 47754035 = 71631053) B71631053
theorem B3059369 : Blo 401768 3059369 := bstep (se 2 (by rfl) ⟨1147263, by rfl⟩ : syracuseStep 3059369 = 2294527) B2294527
theorem B864199 : Blo 401768 864199 := bstep (se 1 (by rfl) ⟨648149, by rfl⟩ : syracuseStep 864199 = 1296299) B1296299
theorem B1454071 : Blo 401768 1454071 := bstep (se 1 (by rfl) ⟨1090553, by rfl⟩ : syracuseStep 1454071 = 2181107) B2181107
theorem B405503 : Blo 401768 405503 := bstep (se 1 (by rfl) ⟨304127, by rfl⟩ : syracuseStep 405503 = 608255) B608255
theorem B604799 : Blo 401768 604799 := bstep (se 1 (by rfl) ⟨453599, by rfl⟩ : syracuseStep 604799 = 907199) B907199
theorem B3882167 : Blo 401768 3882167 := bstep (se 1 (by rfl) ⟨2911625, by rfl⟩ : syracuseStep 3882167 = 5823251) B5823251
theorem B2047679 : Blo 401768 2047679 := bstep (se 1 (by rfl) ⟨1535759, by rfl⟩ : syracuseStep 2047679 = 3071519) B3071519
theorem B606527 : Blo 401768 606527 := bstep (se 1 (by rfl) ⟨454895, by rfl⟩ : syracuseStep 606527 = 909791) B909791
theorem B904751 : Blo 401768 904751 := bstep (se 1 (by rfl) ⟨678563, by rfl⟩ : syracuseStep 904751 = 1357127) B1357127
theorem B3067631 : Blo 401768 3067631 := bstep (se 1 (by rfl) ⟨2300723, by rfl⟩ : syracuseStep 3067631 = 4601447) B4601447
theorem B1660927 : Blo 401768 1660927 := bstep (se 1 (by rfl) ⟨1245695, by rfl⟩ : syracuseStep 1660927 = 2491391) B2491391
theorem B909359 : Blo 401768 909359 := bstep (se 1 (by rfl) ⟨682019, by rfl⟩ : syracuseStep 909359 = 1364039) B1364039
theorem B1402991 : Blo 401768 1402991 := bstep (se 1 (by rfl) ⟨1052243, by rfl⟩ : syracuseStep 1402991 = 2104487) B2104487
theorem B2582779 : Blo 401768 2582779 := bstep (se 1 (by rfl) ⟨1937084, by rfl⟩ : syracuseStep 2582779 = 3874169) B3874169
theorem B912041 : Blo 401768 912041 := bstep (se 2 (by rfl) ⟨342015, by rfl⟩ : syracuseStep 912041 = 684031) B684031
theorem B379942559 : Blo 401768 379942559 := bstep (se 1 (by rfl) ⟨284956919, by rfl⟩ : syracuseStep 379942559 = 569913839) B569913839
theorem B6191387 : Blo 401768 6191387 := bstep (se 1 (by rfl) ⟨4643540, by rfl⟩ : syracuseStep 6191387 = 9287081) B9287081
theorem B3443705 : Blo 401768 3443705 := bstep (se 2 (by rfl) ⟨1291389, by rfl⟩ : syracuseStep 3443705 = 2582779) B2582779
theorem B5902235 : Blo 401768 5902235 := bstep (se 1 (by rfl) ⟨4426676, by rfl⟩ : syracuseStep 5902235 = 8853353) B8853353
theorem B1152265 : Blo 401768 1152265 := bstep (se 2 (by rfl) ⟨432099, by rfl⟩ : syracuseStep 1152265 = 864199) B864199
theorem B1938761 : Blo 401768 1938761 := bstep (se 2 (by rfl) ⟨727035, by rfl⟩ : syracuseStep 1938761 = 1454071) B1454071
theorem B2039579 : Blo 401768 2039579 := bstep (se 1 (by rfl) ⟨1529684, by rfl⟩ : syracuseStep 2039579 = 3059369) B3059369
theorem B403199 : Blo 401768 403199 := bstep (se 1 (by rfl) ⟨302399, by rfl⟩ : syracuseStep 403199 = 604799) B604799
theorem B404351 : Blo 401768 404351 := bstep (se 1 (by rfl) ⟨303263, by rfl⟩ : syracuseStep 404351 = 606527) B606527
theorem B603167 : Blo 401768 603167 := bstep (se 1 (by rfl) ⟨452375, by rfl⟩ : syracuseStep 603167 = 904751) B904751
theorem B2045087 : Blo 401768 2045087 := bstep (se 1 (by rfl) ⟨1533815, by rfl⟩ : syracuseStep 2045087 = 3067631) B3067631
theorem B606239 : Blo 401768 606239 := bstep (se 1 (by rfl) ⟨454679, by rfl⟩ : syracuseStep 606239 = 909359) B909359
theorem B935327 : Blo 401768 935327 := bstep (se 1 (by rfl) ⟨701495, by rfl⟩ : syracuseStep 935327 = 1402991) B1402991
theorem B608027 : Blo 401768 608027 := bstep (se 1 (by rfl) ⟨456020, by rfl⟩ : syracuseStep 608027 = 912041) B912041
theorem B31836023 : Blo 401768 31836023 := bstep (se 1 (by rfl) ⟨23877017, by rfl⟩ : syracuseStep 31836023 = 47754035) B47754035
theorem B2214569 : Blo 401768 2214569 := bstep (se 2 (by rfl) ⟨830463, by rfl⟩ : syracuseStep 2214569 = 1660927) B1660927
theorem B1365119 : Blo 401768 1365119 := bstep (se 1 (by rfl) ⟨1023839, by rfl⟩ : syracuseStep 1365119 = 2047679) B2047679
theorem B2189081 : Blo 401768 2189081 := bstep (se 2 (by rfl) ⟨820905, by rfl⟩ : syracuseStep 2189081 = 1641811) B1641811
theorem B253295039 : Blo 401768 253295039 := bstep (se 1 (by rfl) ⟨189971279, by rfl⟩ : syracuseStep 253295039 = 379942559) B379942559
theorem B4127591 : Blo 401768 4127591 := bstep (se 1 (by rfl) ⟨3095693, by rfl⟩ : syracuseStep 4127591 = 6191387) B6191387
theorem B2588111 : Blo 401768 2588111 := bstep (se 1 (by rfl) ⟨1941083, by rfl⟩ : syracuseStep 2588111 = 3882167) B3882167
theorem B623551 : Blo 401768 623551 := bstep (se 1 (by rfl) ⟨467663, by rfl⟩ : syracuseStep 623551 = 935327) B935327
theorem B1476379 : Blo 401768 1476379 := bstep (se 1 (by rfl) ⟨1107284, by rfl⟩ : syracuseStep 1476379 = 2214569) B2214569
theorem B2295803 : Blo 401768 2295803 := bstep (se 1 (by rfl) ⟨1721852, by rfl⟩ : syracuseStep 2295803 = 3443705) B3443705
theorem B3934823 : Blo 401768 3934823 := bstep (se 1 (by rfl) ⟨2951117, by rfl⟩ : syracuseStep 3934823 = 5902235) B5902235
theorem B402111 : Blo 401768 402111 := bstep (se 1 (by rfl) ⟨301583, by rfl⟩ : syracuseStep 402111 = 603167) B603167
theorem B168863359 : Blo 401768 168863359 := bstep (se 1 (by rfl) ⟨126647519, by rfl⟩ : syracuseStep 168863359 = 253295039) B253295039
theorem B404159 : Blo 401768 404159 := bstep (se 1 (by rfl) ⟨303119, by rfl⟩ : syracuseStep 404159 = 606239) B606239
theorem B405351 : Blo 401768 405351 := bstep (se 1 (by rfl) ⟨304013, by rfl⟩ : syracuseStep 405351 = 608027) B608027
theorem B1292507 : Blo 401768 1292507 := bstep (se 1 (by rfl) ⟨969380, by rfl⟩ : syracuseStep 1292507 = 1938761) B1938761
theorem B1359719 : Blo 401768 1359719 := bstep (se 1 (by rfl) ⟨1019789, by rfl⟩ : syracuseStep 1359719 = 2039579) B2039579
theorem B1459387 : Blo 401768 1459387 := bstep (se 1 (by rfl) ⟨1094540, by rfl⟩ : syracuseStep 1459387 = 2189081) B2189081
theorem B1363391 : Blo 401768 1363391 := bstep (se 1 (by rfl) ⟨1022543, by rfl⟩ : syracuseStep 1363391 = 2045087) B2045087
theorem B1725407 : Blo 401768 1725407 := bstep (se 1 (by rfl) ⟨1294055, by rfl⟩ : syracuseStep 1725407 = 2588111) B2588111
theorem B21224015 : Blo 401768 21224015 := bstep (se 1 (by rfl) ⟨15918011, by rfl⟩ : syracuseStep 21224015 = 31836023) B31836023
theorem B910079 : Blo 401768 910079 := bstep (se 1 (by rfl) ⟨682559, by rfl⟩ : syracuseStep 910079 = 1365119) B1365119
theorem B1536353 : Blo 401768 1536353 := bstep (se 2 (by rfl) ⟨576132, by rfl⟩ : syracuseStep 1536353 = 1152265) B1152265
theorem B2751727 : Blo 401768 2751727 := bstep (se 1 (by rfl) ⟨2063795, by rfl⟩ : syracuseStep 2751727 = 4127591) B4127591
theorem B225151145 : Blo 401768 225151145 := bstep (se 2 (by rfl) ⟨84431679, by rfl⟩ : syracuseStep 225151145 = 168863359) B168863359
theorem B1968505 : Blo 401768 1968505 := bstep (se 2 (by rfl) ⟨738189, by rfl⟩ : syracuseStep 1968505 = 1476379) B1476379
theorem B1150271 : Blo 401768 1150271 := bstep (se 1 (by rfl) ⟨862703, by rfl⟩ : syracuseStep 1150271 = 1725407) B1725407
theorem B10492861 : Blo 401768 10492861 := bstep (se 3 (by rfl) ⟨1967411, by rfl⟩ : syracuseStep 10492861 = 3934823) B3934823
theorem B1024235 : Blo 401768 1024235 := bstep (se 1 (by rfl) ⟨768176, by rfl⟩ : syracuseStep 1024235 = 1536353) B1536353
theorem B861671 : Blo 401768 861671 := bstep (se 1 (by rfl) ⟨646253, by rfl⟩ : syracuseStep 861671 = 1292507) B1292507
theorem B831401 : Blo 401768 831401 := bstep (se 2 (by rfl) ⟨311775, by rfl⟩ : syracuseStep 831401 = 623551) B623551
theorem B606719 : Blo 401768 606719 := bstep (se 1 (by rfl) ⟨455039, by rfl⟩ : syracuseStep 606719 = 910079) B910079
theorem B7783397 : Blo 401768 7783397 := bstep (se 4 (by rfl) ⟨729693, by rfl⟩ : syracuseStep 7783397 = 1459387) B1459387
theorem B906479 : Blo 401768 906479 := bstep (se 1 (by rfl) ⟨679859, by rfl⟩ : syracuseStep 906479 = 1359719) B1359719
theorem B1530535 : Blo 401768 1530535 := bstep (se 1 (by rfl) ⟨1147901, by rfl⟩ : syracuseStep 1530535 = 2295803) B2295803
theorem B908927 : Blo 401768 908927 := bstep (se 1 (by rfl) ⟨681695, by rfl⟩ : syracuseStep 908927 = 1363391) B1363391
theorem B14149343 : Blo 401768 14149343 := bstep (se 1 (by rfl) ⟨10612007, by rfl⟩ : syracuseStep 14149343 = 21224015) B21224015
theorem B3668969 : Blo 401768 3668969 := bstep (se 2 (by rfl) ⟨1375863, by rfl⟩ : syracuseStep 3668969 = 2751727) B2751727
theorem B2040713 : Blo 401768 2040713 := bstep (se 2 (by rfl) ⟨765267, by rfl⟩ : syracuseStep 2040713 = 1530535) B1530535
theorem B404479 : Blo 401768 404479 := bstep (se 1 (by rfl) ⟨303359, by rfl⟩ : syracuseStep 404479 = 606719) B606719
theorem B5188931 : Blo 401768 5188931 := bstep (se 1 (by rfl) ⟨3891698, by rfl⟩ : syracuseStep 5188931 = 7783397) B7783397
theorem B2401612213 : Blo 401768 2401612213 := bstep (se 5 (by rfl) ⟨112575572, by rfl⟩ : syracuseStep 2401612213 = 225151145) B225151145
theorem B10498693 : Blo 401768 10498693 := bstep (se 4 (by rfl) ⟨984252, by rfl⟩ : syracuseStep 10498693 = 1968505) B1968505
theorem B766847 : Blo 401768 766847 := bstep (se 1 (by rfl) ⟨575135, by rfl⟩ : syracuseStep 766847 = 1150271) B1150271
theorem B604319 : Blo 401768 604319 := bstep (se 1 (by rfl) ⟨453239, by rfl⟩ : syracuseStep 604319 = 906479) B906479
theorem B605951 : Blo 401768 605951 := bstep (se 1 (by rfl) ⟨454463, by rfl⟩ : syracuseStep 605951 = 908927) B908927
theorem B574447 : Blo 401768 574447 := bstep (se 1 (by rfl) ⟨430835, by rfl⟩ : syracuseStep 574447 = 861671) B861671
theorem B2445979 : Blo 401768 2445979 := bstep (se 1 (by rfl) ⟨1834484, by rfl⟩ : syracuseStep 2445979 = 3668969) B3668969
theorem B682823 : Blo 401768 682823 := bstep (se 1 (by rfl) ⟨512117, by rfl⟩ : syracuseStep 682823 = 1024235) B1024235
theorem B9432895 : Blo 401768 9432895 := bstep (se 1 (by rfl) ⟨7074671, by rfl⟩ : syracuseStep 9432895 = 14149343) B14149343
theorem B554267 : Blo 401768 554267 := bstep (se 1 (by rfl) ⟨415700, by rfl⟩ : syracuseStep 554267 = 831401) B831401
theorem B13990481 : Blo 401768 13990481 := bstep (se 2 (by rfl) ⟨5246430, by rfl⟩ : syracuseStep 13990481 = 10492861) B10492861
theorem B1478045 : Blo 401768 1478045 := bstep (se 3 (by rfl) ⟨277133, by rfl⟩ : syracuseStep 1478045 = 554267) B554267
theorem B13998257 : Blo 401768 13998257 := bstep (se 2 (by rfl) ⟨5249346, by rfl⟩ : syracuseStep 13998257 = 10498693) B10498693
theorem B402879 : Blo 401768 402879 := bstep (se 1 (by rfl) ⟨302159, by rfl⟩ : syracuseStep 402879 = 604319) B604319
theorem B403967 : Blo 401768 403967 := bstep (se 1 (by rfl) ⟨302975, by rfl⟩ : syracuseStep 403967 = 605951) B605951
theorem B765929 : Blo 401768 765929 := bstep (se 2 (by rfl) ⟨287223, by rfl⟩ : syracuseStep 765929 = 574447) B574447
theorem B2044925 : Blo 401768 2044925 := bstep (se 3 (by rfl) ⟨383423, by rfl⟩ : syracuseStep 2044925 = 766847) B766847
theorem B1360475 : Blo 401768 1360475 := bstep (se 1 (by rfl) ⟨1020356, by rfl⟩ : syracuseStep 1360475 = 2040713) B2040713
theorem B3261305 : Blo 401768 3261305 := bstep (se 2 (by rfl) ⟨1222989, by rfl⟩ : syracuseStep 3261305 = 2445979) B2445979
theorem B3459287 : Blo 401768 3459287 := bstep (se 1 (by rfl) ⟨2594465, by rfl⟩ : syracuseStep 3459287 = 5188931) B5188931
theorem B9326987 : Blo 401768 9326987 := bstep (se 1 (by rfl) ⟨6995240, by rfl⟩ : syracuseStep 9326987 = 13990481) B13990481
theorem B12577193 : Blo 401768 12577193 := bstep (se 2 (by rfl) ⟨4716447, by rfl⟩ : syracuseStep 12577193 = 9432895) B9432895
theorem B3202149617 : Blo 401768 3202149617 := bstep (se 2 (by rfl) ⟨1200806106, by rfl⟩ : syracuseStep 3202149617 = 2401612213) B2401612213
theorem B455215 : Blo 401768 455215 := bstep (se 1 (by rfl) ⟨341411, by rfl⟩ : syracuseStep 455215 = 682823) B682823
theorem B3941453 : Blo 401768 3941453 := bstep (se 3 (by rfl) ⟨739022, by rfl⟩ : syracuseStep 3941453 = 1478045) B1478045
theorem B2174203 : Blo 401768 2174203 := bstep (se 1 (by rfl) ⟨1630652, by rfl⟩ : syracuseStep 2174203 = 3261305) B3261305
theorem B2306191 : Blo 401768 2306191 := bstep (se 1 (by rfl) ⟨1729643, by rfl⟩ : syracuseStep 2306191 = 3459287) B3459287
theorem B606953 : Blo 401768 606953 := bstep (se 2 (by rfl) ⟨227607, by rfl⟩ : syracuseStep 606953 = 455215) B455215
theorem B510619 : Blo 401768 510619 := bstep (se 1 (by rfl) ⟨382964, by rfl⟩ : syracuseStep 510619 = 765929) B765929
theorem B1363283 : Blo 401768 1363283 := bstep (se 1 (by rfl) ⟨1022462, by rfl⟩ : syracuseStep 1363283 = 2044925) B2044925
theorem B906983 : Blo 401768 906983 := bstep (se 1 (by rfl) ⟨680237, by rfl⟩ : syracuseStep 906983 = 1360475) B1360475
theorem B6217991 : Blo 401768 6217991 := bstep (se 1 (by rfl) ⟨4663493, by rfl⟩ : syracuseStep 6217991 = 9326987) B9326987
theorem B9332171 : Blo 401768 9332171 := bstep (se 1 (by rfl) ⟨6999128, by rfl⟩ : syracuseStep 9332171 = 13998257) B13998257
theorem B8384795 : Blo 401768 8384795 := bstep (se 1 (by rfl) ⟨6288596, by rfl⟩ : syracuseStep 8384795 = 12577193) B12577193
theorem B2134766411 : Blo 401768 2134766411 := bstep (se 1 (by rfl) ⟨1601074808, by rfl⟩ : syracuseStep 2134766411 = 3202149617) B3202149617
theorem B2627635 : Blo 401768 2627635 := bstep (se 1 (by rfl) ⟨1970726, by rfl⟩ : syracuseStep 2627635 = 3941453) B3941453
theorem B404635 : Blo 401768 404635 := bstep (se 1 (by rfl) ⟨303476, by rfl⟩ : syracuseStep 404635 = 606953) B606953
theorem B604655 : Blo 401768 604655 := bstep (se 1 (by rfl) ⟨453491, by rfl⟩ : syracuseStep 604655 = 906983) B906983
theorem B2898937 : Blo 401768 2898937 := bstep (se 2 (by rfl) ⟨1087101, by rfl⟩ : syracuseStep 2898937 = 2174203) B2174203
theorem B4145327 : Blo 401768 4145327 := bstep (se 1 (by rfl) ⟨3108995, by rfl⟩ : syracuseStep 4145327 = 6217991) B6217991
theorem B5589863 : Blo 401768 5589863 := bstep (se 1 (by rfl) ⟨4192397, by rfl⟩ : syracuseStep 5589863 = 8384795) B8384795
theorem B908855 : Blo 401768 908855 := bstep (se 1 (by rfl) ⟨681641, by rfl⟩ : syracuseStep 908855 = 1363283) B1363283
theorem B680825 : Blo 401768 680825 := bstep (se 2 (by rfl) ⟨255309, by rfl⟩ : syracuseStep 680825 = 510619) B510619
theorem B3074921 : Blo 401768 3074921 := bstep (se 2 (by rfl) ⟨1153095, by rfl⟩ : syracuseStep 3074921 = 2306191) B2306191
theorem B6221447 : Blo 401768 6221447 := bstep (se 1 (by rfl) ⟨4666085, by rfl⟩ : syracuseStep 6221447 = 9332171) B9332171
theorem B1423177607 : Blo 401768 1423177607 := bstep (se 1 (by rfl) ⟨1067383205, by rfl⟩ : syracuseStep 1423177607 = 2134766411) B2134766411
theorem B403103 : Blo 401768 403103 := bstep (se 1 (by rfl) ⟨302327, by rfl⟩ : syracuseStep 403103 = 604655) B604655
theorem B2763551 : Blo 401768 2763551 := bstep (se 1 (by rfl) ⟨2072663, by rfl⟩ : syracuseStep 2763551 = 4145327) B4145327
theorem B605903 : Blo 401768 605903 := bstep (se 1 (by rfl) ⟨454427, by rfl⟩ : syracuseStep 605903 = 908855) B908855
theorem B2049947 : Blo 401768 2049947 := bstep (se 1 (by rfl) ⟨1537460, by rfl⟩ : syracuseStep 2049947 = 3074921) B3074921
theorem B4147631 : Blo 401768 4147631 := bstep (se 1 (by rfl) ⟨3110723, by rfl⟩ : syracuseStep 4147631 = 6221447) B6221447
theorem B948785071 : Blo 401768 948785071 := bstep (se 1 (by rfl) ⟨711588803, by rfl⟩ : syracuseStep 948785071 = 1423177607) B1423177607
theorem B3726575 : Blo 401768 3726575 := bstep (se 1 (by rfl) ⟨2794931, by rfl⟩ : syracuseStep 3726575 = 5589863) B5589863
theorem B453883 : Blo 401768 453883 := bstep (se 1 (by rfl) ⟨340412, by rfl⟩ : syracuseStep 453883 = 680825) B680825
theorem B3503513 : Blo 401768 3503513 := bstep (se 2 (by rfl) ⟨1313817, by rfl⟩ : syracuseStep 3503513 = 2627635) B2627635
theorem B3865249 : Blo 401768 3865249 := bstep (se 2 (by rfl) ⟨1449468, by rfl⟩ : syracuseStep 3865249 = 2898937) B2898937
theorem B1265046761 : Blo 401768 1265046761 := bstep (se 2 (by rfl) ⟨474392535, by rfl⟩ : syracuseStep 1265046761 = 948785071) B948785071
theorem B1842367 : Blo 401768 1842367 := bstep (se 1 (by rfl) ⟨1381775, by rfl⟩ : syracuseStep 1842367 = 2763551) B2763551
theorem B5153665 : Blo 401768 5153665 := bstep (se 2 (by rfl) ⟨1932624, by rfl⟩ : syracuseStep 5153665 = 3865249) B3865249
theorem B2335675 : Blo 401768 2335675 := bstep (se 1 (by rfl) ⟨1751756, by rfl⟩ : syracuseStep 2335675 = 3503513) B3503513
theorem B403935 : Blo 401768 403935 := bstep (se 1 (by rfl) ⟨302951, by rfl⟩ : syracuseStep 403935 = 605903) B605903
theorem B2765087 : Blo 401768 2765087 := bstep (se 1 (by rfl) ⟨2073815, by rfl⟩ : syracuseStep 2765087 = 4147631) B4147631
theorem B605177 : Blo 401768 605177 := bstep (se 2 (by rfl) ⟨226941, by rfl⟩ : syracuseStep 605177 = 453883) B453883
theorem B1366631 : Blo 401768 1366631 := bstep (se 1 (by rfl) ⟨1024973, by rfl⟩ : syracuseStep 1366631 = 2049947) B2049947
theorem B2484383 : Blo 401768 2484383 := bstep (se 1 (by rfl) ⟨1863287, by rfl⟩ : syracuseStep 2484383 = 3726575) B3726575
theorem B3114233 : Blo 401768 3114233 := bstep (se 2 (by rfl) ⟨1167837, by rfl⟩ : syracuseStep 3114233 = 2335675) B2335675
theorem B6625021 : Blo 401768 6625021 := bstep (se 3 (by rfl) ⟨1242191, by rfl⟩ : syracuseStep 6625021 = 2484383) B2484383
theorem B1843391 : Blo 401768 1843391 := bstep (se 1 (by rfl) ⟨1382543, by rfl⟩ : syracuseStep 1843391 = 2765087) B2765087
theorem B403451 : Blo 401768 403451 := bstep (se 1 (by rfl) ⟨302588, by rfl⟩ : syracuseStep 403451 = 605177) B605177
theorem B843364507 : Blo 401768 843364507 := bstep (se 1 (by rfl) ⟨632523380, by rfl⟩ : syracuseStep 843364507 = 1265046761) B1265046761
theorem B6871553 : Blo 401768 6871553 := bstep (se 2 (by rfl) ⟨2576832, by rfl⟩ : syracuseStep 6871553 = 5153665) B5153665
theorem B911087 : Blo 401768 911087 := bstep (se 1 (by rfl) ⟨683315, by rfl⟩ : syracuseStep 911087 = 1366631) B1366631
theorem B2456489 : Blo 401768 2456489 := bstep (se 2 (by rfl) ⟨921183, by rfl⟩ : syracuseStep 2456489 = 1842367) B1842367
theorem B141333781 : Blo 401768 141333781 := bstep (se 6 (by rfl) ⟨3312510, by rfl⟩ : syracuseStep 141333781 = 6625021) B6625021
theorem B2076155 : Blo 401768 2076155 := bstep (se 1 (by rfl) ⟨1557116, by rfl⟩ : syracuseStep 2076155 = 3114233) B3114233
theorem B1228927 : Blo 401768 1228927 := bstep (se 1 (by rfl) ⟨921695, by rfl⟩ : syracuseStep 1228927 = 1843391) B1843391
theorem B607391 : Blo 401768 607391 := bstep (se 1 (by rfl) ⟨455543, by rfl⟩ : syracuseStep 607391 = 911087) B911087
theorem B1124486009 : Blo 401768 1124486009 := bstep (se 2 (by rfl) ⟨421682253, by rfl⟩ : syracuseStep 1124486009 = 843364507) B843364507
theorem B4581035 : Blo 401768 4581035 := bstep (se 1 (by rfl) ⟨3435776, by rfl⟩ : syracuseStep 4581035 = 6871553) B6871553
theorem B1637659 : Blo 401768 1637659 := bstep (se 1 (by rfl) ⟨1228244, by rfl⟩ : syracuseStep 1637659 = 2456489) B2456489
theorem B1638569 : Blo 401768 1638569 := bstep (se 2 (by rfl) ⟨614463, by rfl⟩ : syracuseStep 1638569 = 1228927) B1228927
theorem B3054023 : Blo 401768 3054023 := bstep (se 1 (by rfl) ⟨2290517, by rfl⟩ : syracuseStep 3054023 = 4581035) B4581035
theorem B1384103 : Blo 401768 1384103 := bstep (se 1 (by rfl) ⟨1038077, by rfl⟩ : syracuseStep 1384103 = 2076155) B2076155
theorem B404927 : Blo 401768 404927 := bstep (se 1 (by rfl) ⟨303695, by rfl⟩ : syracuseStep 404927 = 607391) B607391
theorem B2183545 : Blo 401768 2183545 := bstep (se 2 (by rfl) ⟨818829, by rfl⟩ : syracuseStep 2183545 = 1637659) B1637659
theorem B749657339 : Blo 401768 749657339 := bstep (se 1 (by rfl) ⟨562243004, by rfl⟩ : syracuseStep 749657339 = 1124486009) B1124486009
theorem B188445041 : Blo 401768 188445041 := bstep (se 2 (by rfl) ⟨70666890, by rfl⟩ : syracuseStep 188445041 = 141333781) B141333781
theorem B2036015 : Blo 401768 2036015 := bstep (se 1 (by rfl) ⟨1527011, by rfl⟩ : syracuseStep 2036015 = 3054023) B3054023
theorem B922735 : Blo 401768 922735 := bstep (se 1 (by rfl) ⟨692051, by rfl⟩ : syracuseStep 922735 = 1384103) B1384103
theorem B1092379 : Blo 401768 1092379 := bstep (se 1 (by rfl) ⟨819284, by rfl⟩ : syracuseStep 1092379 = 1638569) B1638569
theorem B499771559 : Blo 401768 499771559 := bstep (se 1 (by rfl) ⟨374828669, by rfl⟩ : syracuseStep 499771559 = 749657339) B749657339
theorem B2911393 : Blo 401768 2911393 := bstep (se 2 (by rfl) ⟨1091772, by rfl⟩ : syracuseStep 2911393 = 2183545) B2183545
theorem B125630027 : Blo 401768 125630027 := bstep (se 1 (by rfl) ⟨94222520, by rfl⟩ : syracuseStep 125630027 = 188445041) B188445041
theorem B1357343 : Blo 401768 1357343 := bstep (se 1 (by rfl) ⟨1018007, by rfl⟩ : syracuseStep 1357343 = 2036015) B2036015
theorem B1456505 : Blo 401768 1456505 := bstep (se 2 (by rfl) ⟨546189, by rfl⟩ : syracuseStep 1456505 = 1092379) B1092379
theorem B3881857 : Blo 401768 3881857 := bstep (se 2 (by rfl) ⟨1455696, by rfl⟩ : syracuseStep 3881857 = 2911393) B2911393
theorem B1230313 : Blo 401768 1230313 := bstep (se 2 (by rfl) ⟨461367, by rfl⟩ : syracuseStep 1230313 = 922735) B922735
theorem B333181039 : Blo 401768 333181039 := bstep (se 1 (by rfl) ⟨249885779, by rfl⟩ : syracuseStep 333181039 = 499771559) B499771559
theorem B83753351 : Blo 401768 83753351 := bstep (se 1 (by rfl) ⟨62815013, by rfl⟩ : syracuseStep 83753351 = 125630027) B125630027
theorem B1640417 : Blo 401768 1640417 := bstep (se 2 (by rfl) ⟨615156, by rfl⟩ : syracuseStep 1640417 = 1230313) B1230313
theorem B444241385 : Blo 401768 444241385 := bstep (se 2 (by rfl) ⟨166590519, by rfl⟩ : syracuseStep 444241385 = 333181039) B333181039
theorem B904895 : Blo 401768 904895 := bstep (se 1 (by rfl) ⟨678671, by rfl⟩ : syracuseStep 904895 = 1357343) B1357343
theorem B971003 : Blo 401768 971003 := bstep (se 1 (by rfl) ⟨728252, by rfl⟩ : syracuseStep 971003 = 1456505) B1456505
theorem B5175809 : Blo 401768 5175809 := bstep (se 2 (by rfl) ⟨1940928, by rfl⟩ : syracuseStep 5175809 = 3881857) B3881857
theorem B55835567 : Blo 401768 55835567 := bstep (se 1 (by rfl) ⟨41876675, by rfl⟩ : syracuseStep 55835567 = 83753351) B83753351
theorem B296160923 : Blo 401768 296160923 := bstep (se 1 (by rfl) ⟨222120692, by rfl⟩ : syracuseStep 296160923 = 444241385) B444241385
theorem B3450539 : Blo 401768 3450539 := bstep (se 1 (by rfl) ⟨2587904, by rfl⟩ : syracuseStep 3450539 = 5175809) B5175809
theorem B603263 : Blo 401768 603263 := bstep (se 1 (by rfl) ⟨452447, by rfl⟩ : syracuseStep 603263 = 904895) B904895
theorem B4374445 : Blo 401768 4374445 := bstep (se 3 (by rfl) ⟨820208, by rfl⟩ : syracuseStep 4374445 = 1640417) B1640417
theorem B647335 : Blo 401768 647335 := bstep (se 1 (by rfl) ⟨485501, by rfl⟩ : syracuseStep 647335 = 971003) B971003
theorem B37223711 : Blo 401768 37223711 := bstep (se 1 (by rfl) ⟨27917783, by rfl⟩ : syracuseStep 37223711 = 55835567) B55835567
theorem B2300359 : Blo 401768 2300359 := bstep (se 1 (by rfl) ⟨1725269, by rfl⟩ : syracuseStep 2300359 = 3450539) B3450539
theorem B402175 : Blo 401768 402175 := bstep (se 1 (by rfl) ⟨301631, by rfl⟩ : syracuseStep 402175 = 603263) B603263
theorem B24815807 : Blo 401768 24815807 := bstep (se 1 (by rfl) ⟨18611855, by rfl⟩ : syracuseStep 24815807 = 37223711) B37223711
theorem B3452453 : Blo 401768 3452453 := bstep (se 4 (by rfl) ⟨323667, by rfl⟩ : syracuseStep 3452453 = 647335) B647335
theorem B197440615 : Blo 401768 197440615 := bstep (se 1 (by rfl) ⟨148080461, by rfl⟩ : syracuseStep 197440615 = 296160923) B296160923
theorem B5832593 : Blo 401768 5832593 := bstep (se 2 (by rfl) ⟨2187222, by rfl⟩ : syracuseStep 5832593 = 4374445) B4374445
theorem B2301635 : Blo 401768 2301635 := bstep (se 1 (by rfl) ⟨1726226, by rfl⟩ : syracuseStep 2301635 = 3452453) B3452453
theorem B3067145 : Blo 401768 3067145 := bstep (se 2 (by rfl) ⟨1150179, by rfl⟩ : syracuseStep 3067145 = 2300359) B2300359
theorem B3888395 : Blo 401768 3888395 := bstep (se 1 (by rfl) ⟨2916296, by rfl⟩ : syracuseStep 3888395 = 5832593) B5832593
theorem B16543871 : Blo 401768 16543871 := bstep (se 1 (by rfl) ⟨12407903, by rfl⟩ : syracuseStep 16543871 = 24815807) B24815807
theorem B263254153 : Blo 401768 263254153 := bstep (se 2 (by rfl) ⟨98720307, by rfl⟩ : syracuseStep 263254153 = 197440615) B197440615
theorem B2592263 : Blo 401768 2592263 := bstep (se 1 (by rfl) ⟨1944197, by rfl⟩ : syracuseStep 2592263 = 3888395) B3888395
theorem B2044763 : Blo 401768 2044763 := bstep (se 1 (by rfl) ⟨1533572, by rfl⟩ : syracuseStep 2044763 = 3067145) B3067145
theorem B11029247 : Blo 401768 11029247 := bstep (se 1 (by rfl) ⟨8271935, by rfl⟩ : syracuseStep 11029247 = 16543871) B16543871
theorem B1534423 : Blo 401768 1534423 := bstep (se 1 (by rfl) ⟨1150817, by rfl⟩ : syracuseStep 1534423 = 2301635) B2301635
theorem B351005537 : Blo 401768 351005537 := bstep (se 2 (by rfl) ⟨131627076, by rfl⟩ : syracuseStep 351005537 = 263254153) B263254153
theorem B234003691 : Blo 401768 234003691 := bstep (se 1 (by rfl) ⟨175502768, by rfl⟩ : syracuseStep 234003691 = 351005537) B351005537
theorem B7352831 : Blo 401768 7352831 := bstep (se 1 (by rfl) ⟨5514623, by rfl⟩ : syracuseStep 7352831 = 11029247) B11029247
theorem B2045897 : Blo 401768 2045897 := bstep (se 2 (by rfl) ⟨767211, by rfl⟩ : syracuseStep 2045897 = 1534423) B1534423
theorem B1363175 : Blo 401768 1363175 := bstep (se 1 (by rfl) ⟨1022381, by rfl⟩ : syracuseStep 1363175 = 2044763) B2044763
theorem B1728175 : Blo 401768 1728175 := bstep (se 1 (by rfl) ⟨1296131, by rfl⟩ : syracuseStep 1728175 = 2592263) B2592263
theorem B2304233 : Blo 401768 2304233 := bstep (se 2 (by rfl) ⟨864087, by rfl⟩ : syracuseStep 2304233 = 1728175) B1728175
theorem B4901887 : Blo 401768 4901887 := bstep (se 1 (by rfl) ⟨3676415, by rfl⟩ : syracuseStep 4901887 = 7352831) B7352831
theorem B1363931 : Blo 401768 1363931 := bstep (se 1 (by rfl) ⟨1022948, by rfl⟩ : syracuseStep 1363931 = 2045897) B2045897
theorem B312004921 : Blo 401768 312004921 := bstep (se 2 (by rfl) ⟨117001845, by rfl⟩ : syracuseStep 312004921 = 234003691) B234003691
theorem B908783 : Blo 401768 908783 := bstep (se 1 (by rfl) ⟨681587, by rfl⟩ : syracuseStep 908783 = 1363175) B1363175
theorem B6535849 : Blo 401768 6535849 := bstep (se 2 (by rfl) ⟨2450943, by rfl⟩ : syracuseStep 6535849 = 4901887) B4901887
theorem B605855 : Blo 401768 605855 := bstep (se 1 (by rfl) ⟨454391, by rfl⟩ : syracuseStep 605855 = 908783) B908783
theorem B416006561 : Blo 401768 416006561 := bstep (se 2 (by rfl) ⟨156002460, by rfl⟩ : syracuseStep 416006561 = 312004921) B312004921
theorem B909287 : Blo 401768 909287 := bstep (se 1 (by rfl) ⟨681965, by rfl⟩ : syracuseStep 909287 = 1363931) B1363931
theorem B1536155 : Blo 401768 1536155 := bstep (se 1 (by rfl) ⟨1152116, by rfl⟩ : syracuseStep 1536155 = 2304233) B2304233
theorem B1024103 : Blo 401768 1024103 := bstep (se 1 (by rfl) ⟨768077, by rfl⟩ : syracuseStep 1024103 = 1536155) B1536155
theorem B403903 : Blo 401768 403903 := bstep (se 1 (by rfl) ⟨302927, by rfl⟩ : syracuseStep 403903 = 605855) B605855
theorem B606191 : Blo 401768 606191 := bstep (se 1 (by rfl) ⟨454643, by rfl⟩ : syracuseStep 606191 = 909287) B909287
theorem B1109350829 : Blo 401768 1109350829 := bstep (se 3 (by rfl) ⟨208003280, by rfl⟩ : syracuseStep 1109350829 = 416006561) B416006561
theorem B8714465 : Blo 401768 8714465 := bstep (se 2 (by rfl) ⟨3267924, by rfl⟩ : syracuseStep 8714465 = 6535849) B6535849
theorem B5809643 : Blo 401768 5809643 := bstep (se 1 (by rfl) ⟨4357232, by rfl⟩ : syracuseStep 5809643 = 8714465) B8714465
theorem B404127 : Blo 401768 404127 := bstep (se 1 (by rfl) ⟨303095, by rfl⟩ : syracuseStep 404127 = 606191) B606191
theorem B739567219 : Blo 401768 739567219 := bstep (se 1 (by rfl) ⟨554675414, by rfl⟩ : syracuseStep 739567219 = 1109350829) B1109350829
theorem B682735 : Blo 401768 682735 := bstep (se 1 (by rfl) ⟨512051, by rfl⟩ : syracuseStep 682735 = 1024103) B1024103
theorem B986089625 : Blo 401768 986089625 := bstep (se 2 (by rfl) ⟨369783609, by rfl⟩ : syracuseStep 986089625 = 739567219) B739567219
theorem B3873095 : Blo 401768 3873095 := bstep (se 1 (by rfl) ⟨2904821, by rfl⟩ : syracuseStep 3873095 = 5809643) B5809643
theorem B910313 : Blo 401768 910313 := bstep (se 2 (by rfl) ⟨341367, by rfl⟩ : syracuseStep 910313 = 682735) B682735
theorem B657393083 : Blo 401768 657393083 := bstep (se 1 (by rfl) ⟨493044812, by rfl⟩ : syracuseStep 657393083 = 986089625) B986089625
theorem B606875 : Blo 401768 606875 := bstep (se 1 (by rfl) ⟨455156, by rfl⟩ : syracuseStep 606875 = 910313) B910313
theorem B2582063 : Blo 401768 2582063 := bstep (se 1 (by rfl) ⟨1936547, by rfl⟩ : syracuseStep 2582063 = 3873095) B3873095
theorem B404583 : Blo 401768 404583 := bstep (se 1 (by rfl) ⟨303437, by rfl⟩ : syracuseStep 404583 = 606875) B606875
theorem B1721375 : Blo 401768 1721375 := bstep (se 1 (by rfl) ⟨1291031, by rfl⟩ : syracuseStep 1721375 = 2582063) B2582063
theorem B438262055 : Blo 401768 438262055 := bstep (se 1 (by rfl) ⟨328696541, by rfl⟩ : syracuseStep 438262055 = 657393083) B657393083
theorem B1147583 : Blo 401768 1147583 := bstep (se 1 (by rfl) ⟨860687, by rfl⟩ : syracuseStep 1147583 = 1721375) B1721375
theorem B292174703 : Blo 401768 292174703 := bstep (se 1 (by rfl) ⟨219131027, by rfl⟩ : syracuseStep 292174703 = 438262055) B438262055
theorem B194783135 : Blo 401768 194783135 := bstep (se 1 (by rfl) ⟨146087351, by rfl⟩ : syracuseStep 194783135 = 292174703) B292174703
theorem B765055 : Blo 401768 765055 := bstep (se 1 (by rfl) ⟨573791, by rfl⟩ : syracuseStep 765055 = 1147583) B1147583
theorem B1020073 : Blo 401768 1020073 := bstep (se 2 (by rfl) ⟨382527, by rfl⟩ : syracuseStep 1020073 = 765055) B765055
theorem B519421693 : Blo 401768 519421693 := bstep (se 3 (by rfl) ⟨97391567, by rfl⟩ : syracuseStep 519421693 = 194783135) B194783135
theorem B692562257 : Blo 401768 692562257 := bstep (se 2 (by rfl) ⟨259710846, by rfl⟩ : syracuseStep 692562257 = 519421693) B519421693
theorem B1360097 : Blo 401768 1360097 := bstep (se 2 (by rfl) ⟨510036, by rfl⟩ : syracuseStep 1360097 = 1020073) B1020073
theorem B461708171 : Blo 401768 461708171 := bstep (se 1 (by rfl) ⟨346281128, by rfl⟩ : syracuseStep 461708171 = 692562257) B692562257
theorem B906731 : Blo 401768 906731 := bstep (se 1 (by rfl) ⟨680048, by rfl⟩ : syracuseStep 906731 = 1360097) B1360097
theorem B604487 : Blo 401768 604487 := bstep (se 1 (by rfl) ⟨453365, by rfl⟩ : syracuseStep 604487 = 906731) B906731
theorem B307805447 : Blo 401768 307805447 := bstep (se 1 (by rfl) ⟨230854085, by rfl⟩ : syracuseStep 307805447 = 461708171) B461708171
theorem B402991 : Blo 401768 402991 := bstep (se 1 (by rfl) ⟨302243, by rfl⟩ : syracuseStep 402991 = 604487) B604487
theorem B205203631 : Blo 401768 205203631 := bstep (se 1 (by rfl) ⟨153902723, by rfl⟩ : syracuseStep 205203631 = 307805447) B307805447
theorem B273604841 : Blo 401768 273604841 := bstep (se 2 (by rfl) ⟨102601815, by rfl⟩ : syracuseStep 273604841 = 205203631) B205203631
theorem B182403227 : Blo 401768 182403227 := bstep (se 1 (by rfl) ⟨136802420, by rfl⟩ : syracuseStep 182403227 = 273604841) B273604841
theorem B121602151 : Blo 401768 121602151 := bstep (se 1 (by rfl) ⟨91201613, by rfl⟩ : syracuseStep 121602151 = 182403227) B182403227
theorem B648544805 : Blo 401768 648544805 := bstep (se 4 (by rfl) ⟨60801075, by rfl⟩ : syracuseStep 648544805 = 121602151) B121602151
theorem B432363203 : Blo 401768 432363203 := bstep (se 1 (by rfl) ⟨324272402, by rfl⟩ : syracuseStep 432363203 = 648544805) B648544805
theorem B288242135 : Blo 401768 288242135 := bstep (se 1 (by rfl) ⟨216181601, by rfl⟩ : syracuseStep 288242135 = 432363203) B432363203
theorem B192161423 : Blo 401768 192161423 := bstep (se 1 (by rfl) ⟨144121067, by rfl⟩ : syracuseStep 192161423 = 288242135) B288242135
theorem B128107615 : Blo 401768 128107615 := bstep (se 1 (by rfl) ⟨96080711, by rfl⟩ : syracuseStep 128107615 = 192161423) B192161423
theorem B170810153 : Blo 401768 170810153 := bstep (se 2 (by rfl) ⟨64053807, by rfl⟩ : syracuseStep 170810153 = 128107615) B128107615
theorem B113873435 : Blo 401768 113873435 := bstep (se 1 (by rfl) ⟨85405076, by rfl⟩ : syracuseStep 113873435 = 170810153) B170810153
theorem B75915623 : Blo 401768 75915623 := bstep (se 1 (by rfl) ⟨56936717, by rfl⟩ : syracuseStep 75915623 = 113873435) B113873435
theorem B50610415 : Blo 401768 50610415 := bstep (se 1 (by rfl) ⟨37957811, by rfl⟩ : syracuseStep 50610415 = 75915623) B75915623
theorem B67480553 : Blo 401768 67480553 := bstep (se 2 (by rfl) ⟨25305207, by rfl⟩ : syracuseStep 67480553 = 50610415) B50610415
theorem B44987035 : Blo 401768 44987035 := bstep (se 1 (by rfl) ⟨33740276, by rfl⟩ : syracuseStep 44987035 = 67480553) B67480553
theorem B59982713 : Blo 401768 59982713 := bstep (se 2 (by rfl) ⟨22493517, by rfl⟩ : syracuseStep 59982713 = 44987035) B44987035
theorem B39988475 : Blo 401768 39988475 := bstep (se 1 (by rfl) ⟨29991356, by rfl⟩ : syracuseStep 39988475 = 59982713) B59982713
theorem B26658983 : Blo 401768 26658983 := bstep (se 1 (by rfl) ⟨19994237, by rfl⟩ : syracuseStep 26658983 = 39988475) B39988475
theorem B71090621 : Blo 401768 71090621 := bstep (se 3 (by rfl) ⟨13329491, by rfl⟩ : syracuseStep 71090621 = 26658983) B26658983
theorem B47393747 : Blo 401768 47393747 := bstep (se 1 (by rfl) ⟨35545310, by rfl⟩ : syracuseStep 47393747 = 71090621) B71090621
theorem B31595831 : Blo 401768 31595831 := bstep (se 1 (by rfl) ⟨23696873, by rfl⟩ : syracuseStep 31595831 = 47393747) B47393747
theorem B21063887 : Blo 401768 21063887 := bstep (se 1 (by rfl) ⟨15797915, by rfl⟩ : syracuseStep 21063887 = 31595831) B31595831
theorem B14042591 : Blo 401768 14042591 := bstep (se 1 (by rfl) ⟨10531943, by rfl⟩ : syracuseStep 14042591 = 21063887) B21063887
theorem B9361727 : Blo 401768 9361727 := bstep (se 1 (by rfl) ⟨7021295, by rfl⟩ : syracuseStep 9361727 = 14042591) B14042591
theorem B6241151 : Blo 401768 6241151 := bstep (se 1 (by rfl) ⟨4680863, by rfl⟩ : syracuseStep 6241151 = 9361727) B9361727
theorem B4160767 : Blo 401768 4160767 := bstep (se 1 (by rfl) ⟨3120575, by rfl⟩ : syracuseStep 4160767 = 6241151) B6241151
theorem B5547689 : Blo 401768 5547689 := bstep (se 2 (by rfl) ⟨2080383, by rfl⟩ : syracuseStep 5547689 = 4160767) B4160767
theorem B3698459 : Blo 401768 3698459 := bstep (se 1 (by rfl) ⟨2773844, by rfl⟩ : syracuseStep 3698459 = 5547689) B5547689
theorem B2465639 : Blo 401768 2465639 := bstep (se 1 (by rfl) ⟨1849229, by rfl⟩ : syracuseStep 2465639 = 3698459) B3698459
theorem B1643759 : Blo 401768 1643759 := bstep (se 1 (by rfl) ⟨1232819, by rfl⟩ : syracuseStep 1643759 = 2465639) B2465639
theorem B1095839 : Blo 401768 1095839 := bstep (se 1 (by rfl) ⟨821879, by rfl⟩ : syracuseStep 1095839 = 1643759) B1643759
theorem B730559 : Blo 401768 730559 := bstep (se 1 (by rfl) ⟨547919, by rfl⟩ : syracuseStep 730559 = 1095839) B1095839
theorem B1948157 : Blo 401768 1948157 := bstep (se 3 (by rfl) ⟨365279, by rfl⟩ : syracuseStep 1948157 = 730559) B730559
theorem B1298771 : Blo 401768 1298771 := bstep (se 1 (by rfl) ⟨974078, by rfl⟩ : syracuseStep 1298771 = 1948157) B1948157
theorem B865847 : Blo 401768 865847 := bstep (se 1 (by rfl) ⟨649385, by rfl⟩ : syracuseStep 865847 = 1298771) B1298771
theorem B2308925 : Blo 401768 2308925 := bstep (se 3 (by rfl) ⟨432923, by rfl⟩ : syracuseStep 2308925 = 865847) B865847
theorem B1539283 : Blo 401768 1539283 := bstep (se 1 (by rfl) ⟨1154462, by rfl⟩ : syracuseStep 1539283 = 2308925) B2308925
theorem B2052377 : Blo 401768 2052377 := bstep (se 2 (by rfl) ⟨769641, by rfl⟩ : syracuseStep 2052377 = 1539283) B1539283
theorem B1368251 : Blo 401768 1368251 := bstep (se 1 (by rfl) ⟨1026188, by rfl⟩ : syracuseStep 1368251 = 2052377) B2052377
theorem B912167 : Blo 401768 912167 := bstep (se 1 (by rfl) ⟨684125, by rfl⟩ : syracuseStep 912167 = 1368251) B1368251
theorem B608111 : Blo 401768 608111 := bstep (se 1 (by rfl) ⟨456083, by rfl⟩ : syracuseStep 608111 = 912167) B912167
theorem B405407 : Blo 401768 405407 := bstep (se 1 (by rfl) ⟨304055, by rfl⟩ : syracuseStep 405407 = 608111) B608111

theorem C0 (j : ℕ) (h1 : 100442 ≤ j) (h2 : j ≤ 101141) : Blo 401768 (4 * j + 3) := by
  interval_cases j
  · exact B401771
  · exact B401775
  · exact B401779
  · exact B401783
  · exact B401787
  · exact B401791
  · exact B401795
  · exact B401799
  · exact B401803
  · exact B401807
  · exact B401811
  · exact B401815
  · exact B401819
  · exact B401823
  · exact B401827
  · exact B401831
  · exact B401835
  · exact B401839
  · exact B401843
  · exact B401847
  · exact B401851
  · exact B401855
  · exact B401859
  · exact B401863
  · exact B401867
  · exact B401871
  · exact B401875
  · exact B401879
  · exact B401883
  · exact B401887
  · exact B401891
  · exact B401895
  · exact B401899
  · exact B401903
  · exact B401907
  · exact B401911
  · exact B401915
  · exact B401919
  · exact B401923
  · exact B401927
  · exact B401931
  · exact B401935
  · exact B401939
  · exact B401943
  · exact B401947
  · exact B401951
  · exact B401955
  · exact B401959
  · exact B401963
  · exact B401967
  · exact B401971
  · exact B401975
  · exact B401979
  · exact B401983
  · exact B401987
  · exact B401991
  · exact B401995
  · exact B401999
  · exact B402003
  · exact B402007
  · exact B402011
  · exact B402015
  · exact B402019
  · exact B402023
  · exact B402027
  · exact B402031
  · exact B402035
  · exact B402039
  · exact B402043
  · exact B402047
  · exact B402051
  · exact B402055
  · exact B402059
  · exact B402063
  · exact B402067
  · exact B402071
  · exact B402075
  · exact B402079
  · exact B402083
  · exact B402087
  · exact B402091
  · exact B402095
  · exact B402099
  · exact B402103
  · exact B402107
  · exact B402111
  · exact B402115
  · exact B402119
  · exact B402123
  · exact B402127
  · exact B402131
  · exact B402135
  · exact B402139
  · exact B402143
  · exact B402147
  · exact B402151
  · exact B402155
  · exact B402159
  · exact B402163
  · exact B402167
  · exact B402171
  · exact B402175
  · exact B402179
  · exact B402183
  · exact B402187
  · exact B402191
  · exact B402195
  · exact B402199
  · exact B402203
  · exact B402207
  · exact B402211
  · exact B402215
  · exact B402219
  · exact B402223
  · exact B402227
  · exact B402231
  · exact B402235
  · exact B402239
  · exact B402243
  · exact B402247
  · exact B402251
  · exact B402255
  · exact B402259
  · exact B402263
  · exact B402267
  · exact B402271
  · exact B402275
  · exact B402279
  · exact B402283
  · exact B402287
  · exact B402291
  · exact B402295
  · exact B402299
  · exact B402303
  · exact B402307
  · exact B402311
  · exact B402315
  · exact B402319
  · exact B402323
  · exact B402327
  · exact B402331
  · exact B402335
  · exact B402339
  · exact B402343
  · exact B402347
  · exact B402351
  · exact B402355
  · exact B402359
  · exact B402363
  · exact B402367
  · exact B402371
  · exact B402375
  · exact B402379
  · exact B402383
  · exact B402387
  · exact B402391
  · exact B402395
  · exact B402399
  · exact B402403
  · exact B402407
  · exact B402411
  · exact B402415
  · exact B402419
  · exact B402423
  · exact B402427
  · exact B402431
  · exact B402435
  · exact B402439
  · exact B402443
  · exact B402447
  · exact B402451
  · exact B402455
  · exact B402459
  · exact B402463
  · exact B402467
  · exact B402471
  · exact B402475
  · exact B402479
  · exact B402483
  · exact B402487
  · exact B402491
  · exact B402495
  · exact B402499
  · exact B402503
  · exact B402507
  · exact B402511
  · exact B402515
  · exact B402519
  · exact B402523
  · exact B402527
  · exact B402531
  · exact B402535
  · exact B402539
  · exact B402543
  · exact B402547
  · exact B402551
  · exact B402555
  · exact B402559
  · exact B402563
  · exact B402567
  · exact B402571
  · exact B402575
  · exact B402579
  · exact B402583
  · exact B402587
  · exact B402591
  · exact B402595
  · exact B402599
  · exact B402603
  · exact B402607
  · exact B402611
  · exact B402615
  · exact B402619
  · exact B402623
  · exact B402627
  · exact B402631
  · exact B402635
  · exact B402639
  · exact B402643
  · exact B402647
  · exact B402651
  · exact B402655
  · exact B402659
  · exact B402663
  · exact B402667
  · exact B402671
  · exact B402675
  · exact B402679
  · exact B402683
  · exact B402687
  · exact B402691
  · exact B402695
  · exact B402699
  · exact B402703
  · exact B402707
  · exact B402711
  · exact B402715
  · exact B402719
  · exact B402723
  · exact B402727
  · exact B402731
  · exact B402735
  · exact B402739
  · exact B402743
  · exact B402747
  · exact B402751
  · exact B402755
  · exact B402759
  · exact B402763
  · exact B402767
  · exact B402771
  · exact B402775
  · exact B402779
  · exact B402783
  · exact B402787
  · exact B402791
  · exact B402795
  · exact B402799
  · exact B402803
  · exact B402807
  · exact B402811
  · exact B402815
  · exact B402819
  · exact B402823
  · exact B402827
  · exact B402831
  · exact B402835
  · exact B402839
  · exact B402843
  · exact B402847
  · exact B402851
  · exact B402855
  · exact B402859
  · exact B402863
  · exact B402867
  · exact B402871
  · exact B402875
  · exact B402879
  · exact B402883
  · exact B402887
  · exact B402891
  · exact B402895
  · exact B402899
  · exact B402903
  · exact B402907
  · exact B402911
  · exact B402915
  · exact B402919
  · exact B402923
  · exact B402927
  · exact B402931
  · exact B402935
  · exact B402939
  · exact B402943
  · exact B402947
  · exact B402951
  · exact B402955
  · exact B402959
  · exact B402963
  · exact B402967
  · exact B402971
  · exact B402975
  · exact B402979
  · exact B402983
  · exact B402987
  · exact B402991
  · exact B402995
  · exact B402999
  · exact B403003
  · exact B403007
  · exact B403011
  · exact B403015
  · exact B403019
  · exact B403023
  · exact B403027
  · exact B403031
  · exact B403035
  · exact B403039
  · exact B403043
  · exact B403047
  · exact B403051
  · exact B403055
  · exact B403059
  · exact B403063
  · exact B403067
  · exact B403071
  · exact B403075
  · exact B403079
  · exact B403083
  · exact B403087
  · exact B403091
  · exact B403095
  · exact B403099
  · exact B403103
  · exact B403107
  · exact B403111
  · exact B403115
  · exact B403119
  · exact B403123
  · exact B403127
  · exact B403131
  · exact B403135
  · exact B403139
  · exact B403143
  · exact B403147
  · exact B403151
  · exact B403155
  · exact B403159
  · exact B403163
  · exact B403167
  · exact B403171
  · exact B403175
  · exact B403179
  · exact B403183
  · exact B403187
  · exact B403191
  · exact B403195
  · exact B403199
  · exact B403203
  · exact B403207
  · exact B403211
  · exact B403215
  · exact B403219
  · exact B403223
  · exact B403227
  · exact B403231
  · exact B403235
  · exact B403239
  · exact B403243
  · exact B403247
  · exact B403251
  · exact B403255
  · exact B403259
  · exact B403263
  · exact B403267
  · exact B403271
  · exact B403275
  · exact B403279
  · exact B403283
  · exact B403287
  · exact B403291
  · exact B403295
  · exact B403299
  · exact B403303
  · exact B403307
  · exact B403311
  · exact B403315
  · exact B403319
  · exact B403323
  · exact B403327
  · exact B403331
  · exact B403335
  · exact B403339
  · exact B403343
  · exact B403347
  · exact B403351
  · exact B403355
  · exact B403359
  · exact B403363
  · exact B403367
  · exact B403371
  · exact B403375
  · exact B403379
  · exact B403383
  · exact B403387
  · exact B403391
  · exact B403395
  · exact B403399
  · exact B403403
  · exact B403407
  · exact B403411
  · exact B403415
  · exact B403419
  · exact B403423
  · exact B403427
  · exact B403431
  · exact B403435
  · exact B403439
  · exact B403443
  · exact B403447
  · exact B403451
  · exact B403455
  · exact B403459
  · exact B403463
  · exact B403467
  · exact B403471
  · exact B403475
  · exact B403479
  · exact B403483
  · exact B403487
  · exact B403491
  · exact B403495
  · exact B403499
  · exact B403503
  · exact B403507
  · exact B403511
  · exact B403515
  · exact B403519
  · exact B403523
  · exact B403527
  · exact B403531
  · exact B403535
  · exact B403539
  · exact B403543
  · exact B403547
  · exact B403551
  · exact B403555
  · exact B403559
  · exact B403563
  · exact B403567
  · exact B403571
  · exact B403575
  · exact B403579
  · exact B403583
  · exact B403587
  · exact B403591
  · exact B403595
  · exact B403599
  · exact B403603
  · exact B403607
  · exact B403611
  · exact B403615
  · exact B403619
  · exact B403623
  · exact B403627
  · exact B403631
  · exact B403635
  · exact B403639
  · exact B403643
  · exact B403647
  · exact B403651
  · exact B403655
  · exact B403659
  · exact B403663
  · exact B403667
  · exact B403671
  · exact B403675
  · exact B403679
  · exact B403683
  · exact B403687
  · exact B403691
  · exact B403695
  · exact B403699
  · exact B403703
  · exact B403707
  · exact B403711
  · exact B403715
  · exact B403719
  · exact B403723
  · exact B403727
  · exact B403731
  · exact B403735
  · exact B403739
  · exact B403743
  · exact B403747
  · exact B403751
  · exact B403755
  · exact B403759
  · exact B403763
  · exact B403767
  · exact B403771
  · exact B403775
  · exact B403779
  · exact B403783
  · exact B403787
  · exact B403791
  · exact B403795
  · exact B403799
  · exact B403803
  · exact B403807
  · exact B403811
  · exact B403815
  · exact B403819
  · exact B403823
  · exact B403827
  · exact B403831
  · exact B403835
  · exact B403839
  · exact B403843
  · exact B403847
  · exact B403851
  · exact B403855
  · exact B403859
  · exact B403863
  · exact B403867
  · exact B403871
  · exact B403875
  · exact B403879
  · exact B403883
  · exact B403887
  · exact B403891
  · exact B403895
  · exact B403899
  · exact B403903
  · exact B403907
  · exact B403911
  · exact B403915
  · exact B403919
  · exact B403923
  · exact B403927
  · exact B403931
  · exact B403935
  · exact B403939
  · exact B403943
  · exact B403947
  · exact B403951
  · exact B403955
  · exact B403959
  · exact B403963
  · exact B403967
  · exact B403971
  · exact B403975
  · exact B403979
  · exact B403983
  · exact B403987
  · exact B403991
  · exact B403995
  · exact B403999
  · exact B404003
  · exact B404007
  · exact B404011
  · exact B404015
  · exact B404019
  · exact B404023
  · exact B404027
  · exact B404031
  · exact B404035
  · exact B404039
  · exact B404043
  · exact B404047
  · exact B404051
  · exact B404055
  · exact B404059
  · exact B404063
  · exact B404067
  · exact B404071
  · exact B404075
  · exact B404079
  · exact B404083
  · exact B404087
  · exact B404091
  · exact B404095
  · exact B404099
  · exact B404103
  · exact B404107
  · exact B404111
  · exact B404115
  · exact B404119
  · exact B404123
  · exact B404127
  · exact B404131
  · exact B404135
  · exact B404139
  · exact B404143
  · exact B404147
  · exact B404151
  · exact B404155
  · exact B404159
  · exact B404163
  · exact B404167
  · exact B404171
  · exact B404175
  · exact B404179
  · exact B404183
  · exact B404187
  · exact B404191
  · exact B404195
  · exact B404199
  · exact B404203
  · exact B404207
  · exact B404211
  · exact B404215
  · exact B404219
  · exact B404223
  · exact B404227
  · exact B404231
  · exact B404235
  · exact B404239
  · exact B404243
  · exact B404247
  · exact B404251
  · exact B404255
  · exact B404259
  · exact B404263
  · exact B404267
  · exact B404271
  · exact B404275
  · exact B404279
  · exact B404283
  · exact B404287
  · exact B404291
  · exact B404295
  · exact B404299
  · exact B404303
  · exact B404307
  · exact B404311
  · exact B404315
  · exact B404319
  · exact B404323
  · exact B404327
  · exact B404331
  · exact B404335
  · exact B404339
  · exact B404343
  · exact B404347
  · exact B404351
  · exact B404355
  · exact B404359
  · exact B404363
  · exact B404367
  · exact B404371
  · exact B404375
  · exact B404379
  · exact B404383
  · exact B404387
  · exact B404391
  · exact B404395
  · exact B404399
  · exact B404403
  · exact B404407
  · exact B404411
  · exact B404415
  · exact B404419
  · exact B404423
  · exact B404427
  · exact B404431
  · exact B404435
  · exact B404439
  · exact B404443
  · exact B404447
  · exact B404451
  · exact B404455
  · exact B404459
  · exact B404463
  · exact B404467
  · exact B404471
  · exact B404475
  · exact B404479
  · exact B404483
  · exact B404487
  · exact B404491
  · exact B404495
  · exact B404499
  · exact B404503
  · exact B404507
  · exact B404511
  · exact B404515
  · exact B404519
  · exact B404523
  · exact B404527
  · exact B404531
  · exact B404535
  · exact B404539
  · exact B404543
  · exact B404547
  · exact B404551
  · exact B404555
  · exact B404559
  · exact B404563
  · exact B404567

theorem C1 (j : ℕ) (h1 : 101142 ≤ j) (h2 : j ≤ 101441) : Blo 401768 (4 * j + 3) := by
  interval_cases j
  · exact B404571
  · exact B404575
  · exact B404579
  · exact B404583
  · exact B404587
  · exact B404591
  · exact B404595
  · exact B404599
  · exact B404603
  · exact B404607
  · exact B404611
  · exact B404615
  · exact B404619
  · exact B404623
  · exact B404627
  · exact B404631
  · exact B404635
  · exact B404639
  · exact B404643
  · exact B404647
  · exact B404651
  · exact B404655
  · exact B404659
  · exact B404663
  · exact B404667
  · exact B404671
  · exact B404675
  · exact B404679
  · exact B404683
  · exact B404687
  · exact B404691
  · exact B404695
  · exact B404699
  · exact B404703
  · exact B404707
  · exact B404711
  · exact B404715
  · exact B404719
  · exact B404723
  · exact B404727
  · exact B404731
  · exact B404735
  · exact B404739
  · exact B404743
  · exact B404747
  · exact B404751
  · exact B404755
  · exact B404759
  · exact B404763
  · exact B404767
  · exact B404771
  · exact B404775
  · exact B404779
  · exact B404783
  · exact B404787
  · exact B404791
  · exact B404795
  · exact B404799
  · exact B404803
  · exact B404807
  · exact B404811
  · exact B404815
  · exact B404819
  · exact B404823
  · exact B404827
  · exact B404831
  · exact B404835
  · exact B404839
  · exact B404843
  · exact B404847
  · exact B404851
  · exact B404855
  · exact B404859
  · exact B404863
  · exact B404867
  · exact B404871
  · exact B404875
  · exact B404879
  · exact B404883
  · exact B404887
  · exact B404891
  · exact B404895
  · exact B404899
  · exact B404903
  · exact B404907
  · exact B404911
  · exact B404915
  · exact B404919
  · exact B404923
  · exact B404927
  · exact B404931
  · exact B404935
  · exact B404939
  · exact B404943
  · exact B404947
  · exact B404951
  · exact B404955
  · exact B404959
  · exact B404963
  · exact B404967
  · exact B404971
  · exact B404975
  · exact B404979
  · exact B404983
  · exact B404987
  · exact B404991
  · exact B404995
  · exact B404999
  · exact B405003
  · exact B405007
  · exact B405011
  · exact B405015
  · exact B405019
  · exact B405023
  · exact B405027
  · exact B405031
  · exact B405035
  · exact B405039
  · exact B405043
  · exact B405047
  · exact B405051
  · exact B405055
  · exact B405059
  · exact B405063
  · exact B405067
  · exact B405071
  · exact B405075
  · exact B405079
  · exact B405083
  · exact B405087
  · exact B405091
  · exact B405095
  · exact B405099
  · exact B405103
  · exact B405107
  · exact B405111
  · exact B405115
  · exact B405119
  · exact B405123
  · exact B405127
  · exact B405131
  · exact B405135
  · exact B405139
  · exact B405143
  · exact B405147
  · exact B405151
  · exact B405155
  · exact B405159
  · exact B405163
  · exact B405167
  · exact B405171
  · exact B405175
  · exact B405179
  · exact B405183
  · exact B405187
  · exact B405191
  · exact B405195
  · exact B405199
  · exact B405203
  · exact B405207
  · exact B405211
  · exact B405215
  · exact B405219
  · exact B405223
  · exact B405227
  · exact B405231
  · exact B405235
  · exact B405239
  · exact B405243
  · exact B405247
  · exact B405251
  · exact B405255
  · exact B405259
  · exact B405263
  · exact B405267
  · exact B405271
  · exact B405275
  · exact B405279
  · exact B405283
  · exact B405287
  · exact B405291
  · exact B405295
  · exact B405299
  · exact B405303
  · exact B405307
  · exact B405311
  · exact B405315
  · exact B405319
  · exact B405323
  · exact B405327
  · exact B405331
  · exact B405335
  · exact B405339
  · exact B405343
  · exact B405347
  · exact B405351
  · exact B405355
  · exact B405359
  · exact B405363
  · exact B405367
  · exact B405371
  · exact B405375
  · exact B405379
  · exact B405383
  · exact B405387
  · exact B405391
  · exact B405395
  · exact B405399
  · exact B405403
  · exact B405407
  · exact B405411
  · exact B405415
  · exact B405419
  · exact B405423
  · exact B405427
  · exact B405431
  · exact B405435
  · exact B405439
  · exact B405443
  · exact B405447
  · exact B405451
  · exact B405455
  · exact B405459
  · exact B405463
  · exact B405467
  · exact B405471
  · exact B405475
  · exact B405479
  · exact B405483
  · exact B405487
  · exact B405491
  · exact B405495
  · exact B405499
  · exact B405503
  · exact B405507
  · exact B405511
  · exact B405515
  · exact B405519
  · exact B405523
  · exact B405527
  · exact B405531
  · exact B405535
  · exact B405539
  · exact B405543
  · exact B405547
  · exact B405551
  · exact B405555
  · exact B405559
  · exact B405563
  · exact B405567
  · exact B405571
  · exact B405575
  · exact B405579
  · exact B405583
  · exact B405587
  · exact B405591
  · exact B405595
  · exact B405599
  · exact B405603
  · exact B405607
  · exact B405611
  · exact B405615
  · exact B405619
  · exact B405623
  · exact B405627
  · exact B405631
  · exact B405635
  · exact B405639
  · exact B405643
  · exact B405647
  · exact B405651
  · exact B405655
  · exact B405659
  · exact B405663
  · exact B405667
  · exact B405671
  · exact B405675
  · exact B405679
  · exact B405683
  · exact B405687
  · exact B405691
  · exact B405695
  · exact B405699
  · exact B405703
  · exact B405707
  · exact B405711
  · exact B405715
  · exact B405719
  · exact B405723
  · exact B405727
  · exact B405731
  · exact B405735
  · exact B405739
  · exact B405743
  · exact B405747
  · exact B405751
  · exact B405755
  · exact B405759
  · exact B405763
  · exact B405767

theorem solution (m : ℕ) (hlo : 401768 ≤ m) (hhi : m ≤ 405768) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 100442 ≤ j := by omega
    have hj2 : j ≤ 101441 := by omega
    have hb : Blo 401768 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 101142 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
