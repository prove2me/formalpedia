-- Prove2me | solution 1 for syracuse_descends_range_1240438_1242438
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:11:08.82981+00:00
-- url     : https://prove2.me/submissions/8b99e36f-6698-4d53-87e3-eae30c437159

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


theorem B2793509 : Blo 1240438 2793509 := bbase (se 4 (by rfl) ⟨261891, by rfl⟩ : syracuseStep 2793509 = 523783) (by norm_num)
theorem B2793581 : Blo 1240438 2793581 := bbase (se 3 (by rfl) ⟨523796, by rfl⟩ : syracuseStep 2793581 = 1047593) (by norm_num)
theorem B8953973 : Blo 1240438 8953973 := bbase (se 5 (by rfl) ⟨419717, by rfl⟩ : syracuseStep 8953973 = 839435) (by norm_num)
theorem B1310857 : Blo 1240438 1310857 := bbase (se 2 (by rfl) ⟨491571, by rfl⟩ : syracuseStep 1310857 = 983143) (by norm_num)
theorem B2793653 : Blo 1240438 2793653 := bbase (se 5 (by rfl) ⟨130952, by rfl⟩ : syracuseStep 2793653 = 261905) (by norm_num)
theorem B6283493 : Blo 1240438 6283493 := bbase (se 4 (by rfl) ⟨589077, by rfl⟩ : syracuseStep 6283493 = 1178155) (by norm_num)
theorem B2793725 : Blo 1240438 2793725 := bbase (se 3 (by rfl) ⟨523823, by rfl⟩ : syracuseStep 2793725 = 1047647) (by norm_num)
theorem B9421109 : Blo 1240438 9421109 := bbase (se 5 (by rfl) ⟨441614, by rfl⟩ : syracuseStep 9421109 = 883229) (by norm_num)
theorem B2982197 : Blo 1240438 2982197 := bbase (se 5 (by rfl) ⟨139790, by rfl⟩ : syracuseStep 2982197 = 279581) (by norm_num)
theorem B1491257 : Blo 1240438 1491257 := bbase (se 2 (by rfl) ⟨559221, by rfl⟩ : syracuseStep 1491257 = 1118443) (by norm_num)
theorem B2793797 : Blo 1240438 2793797 := bbase (se 4 (by rfl) ⟨261918, by rfl⟩ : syracuseStep 2793797 = 523837) (by norm_num)
theorem B2687357 : Blo 1240438 2687357 := bbase (se 3 (by rfl) ⟨503879, by rfl⟩ : syracuseStep 2687357 = 1007759) (by norm_num)
theorem B1491329 : Blo 1240438 1491329 := bbase (se 2 (by rfl) ⟨559248, by rfl⟩ : syracuseStep 1491329 = 1118497) (by norm_num)
theorem B2793869 : Blo 1240438 2793869 := bbase (se 3 (by rfl) ⟨523850, by rfl⟩ : syracuseStep 2793869 = 1047701) (by norm_num)
theorem B7553429 : Blo 1240438 7553429 := bbase (se 6 (by rfl) ⟨177033, by rfl⟩ : syracuseStep 7553429 = 354067) (by norm_num)
theorem B4186565 : Blo 1240438 4186565 := bbase (se 4 (by rfl) ⟨392490, by rfl⟩ : syracuseStep 4186565 = 784981) (by norm_num)
theorem B2793941 : Blo 1240438 2793941 := bbase (se 7 (by rfl) ⟨32741, by rfl⟩ : syracuseStep 2793941 = 65483) (by norm_num)
theorem B5300741 : Blo 1240438 5300741 := bbase (se 4 (by rfl) ⟨496944, by rfl⟩ : syracuseStep 5300741 = 993889) (by norm_num)
theorem B2794013 : Blo 1240438 2794013 := bbase (se 3 (by rfl) ⟨523877, by rfl⟩ : syracuseStep 2794013 = 1047755) (by norm_num)
theorem B2982437 : Blo 1240438 2982437 := bbase (se 4 (by rfl) ⟨279603, by rfl⟩ : syracuseStep 2982437 = 559207) (by norm_num)
theorem B2122309 : Blo 1240438 2122309 := bbase (se 4 (by rfl) ⟨198966, by rfl⟩ : syracuseStep 2122309 = 397933) (by norm_num)
theorem B1344097 : Blo 1240438 1344097 := bbase (se 2 (by rfl) ⟨504036, by rfl⟩ : syracuseStep 1344097 = 1008073) (by norm_num)
theorem B4244069 : Blo 1240438 4244069 := bbase (se 4 (by rfl) ⟨397881, by rfl⟩ : syracuseStep 4244069 = 795763) (by norm_num)
theorem B2794085 : Blo 1240438 2794085 := bbase (se 4 (by rfl) ⟨261945, by rfl⟩ : syracuseStep 2794085 = 523891) (by norm_num)
theorem B2794157 : Blo 1240438 2794157 := bbase (se 3 (by rfl) ⟨523904, by rfl⟩ : syracuseStep 2794157 = 1047809) (by norm_num)
theorem B1491637 : Blo 1240438 1491637 := bbase (se 5 (by rfl) ⟨69920, by rfl⟩ : syracuseStep 1491637 = 139841) (by norm_num)
theorem B2794229 : Blo 1240438 2794229 := bbase (se 5 (by rfl) ⟨130979, by rfl⟩ : syracuseStep 2794229 = 261959) (by norm_num)
theorem B5030693 : Blo 1240438 5030693 := bbase (se 4 (by rfl) ⟨471627, by rfl⟩ : syracuseStep 5030693 = 943255) (by norm_num)
theorem B2794301 : Blo 1240438 2794301 := bbase (se 3 (by rfl) ⟨523931, by rfl⟩ : syracuseStep 2794301 = 1047863) (by norm_num)
theorem B1491805 : Blo 1240438 1491805 := bbase (se 3 (by rfl) ⟨279713, by rfl⟩ : syracuseStep 1491805 = 559427) (by norm_num)
theorem B4186997 : Blo 1240438 4186997 := bbase (se 5 (by rfl) ⟨196265, by rfl⟩ : syracuseStep 4186997 = 392531) (by norm_num)
theorem B2794373 : Blo 1240438 2794373 := bbase (se 4 (by rfl) ⟨261972, by rfl⟩ : syracuseStep 2794373 = 523945) (by norm_num)
theorem B1491853 : Blo 1240438 1491853 := bbase (se 3 (by rfl) ⟨279722, by rfl⟩ : syracuseStep 1491853 = 559445) (by norm_num)
theorem B2794445 : Blo 1240438 2794445 := bbase (se 3 (by rfl) ⟨523958, by rfl⟩ : syracuseStep 2794445 = 1047917) (by norm_num)
theorem B22668245 : Blo 1240438 22668245 := bbase (se 7 (by rfl) ⟨265643, by rfl⟩ : syracuseStep 22668245 = 531287) (by norm_num)
theorem B1491949 : Blo 1240438 1491949 := bbase (se 3 (by rfl) ⟨279740, by rfl⟩ : syracuseStep 1491949 = 559481) (by norm_num)
theorem B2794517 : Blo 1240438 2794517 := bbase (se 6 (by rfl) ⟨65496, by rfl⟩ : syracuseStep 2794517 = 130993) (by norm_num)
theorem B1860677 : Blo 1240438 1860677 := bbase (se 4 (by rfl) ⟨174438, by rfl⟩ : syracuseStep 1860677 = 348877) (by norm_num)
theorem B5030981 : Blo 1240438 5030981 := bbase (se 4 (by rfl) ⟨471654, by rfl⟩ : syracuseStep 5030981 = 943309) (by norm_num)
theorem B1860701 : Blo 1240438 1860701 := bbase (se 3 (by rfl) ⟨348881, by rfl⟩ : syracuseStep 1860701 = 697763) (by norm_num)
theorem B2794589 : Blo 1240438 2794589 := bbase (se 3 (by rfl) ⟨523985, by rfl⟩ : syracuseStep 2794589 = 1047971) (by norm_num)
theorem B1860725 : Blo 1240438 1860725 := bbase (se 5 (by rfl) ⟨87221, by rfl⟩ : syracuseStep 1860725 = 174443) (by norm_num)
theorem B1860749 : Blo 1240438 1860749 := bbase (se 3 (by rfl) ⟨348890, by rfl⟩ : syracuseStep 1860749 = 697781) (by norm_num)
theorem B1860773 : Blo 1240438 1860773 := bbase (se 4 (by rfl) ⟨174447, by rfl⟩ : syracuseStep 1860773 = 348895) (by norm_num)
theorem B2794661 : Blo 1240438 2794661 := bbase (se 4 (by rfl) ⟨261999, by rfl⟩ : syracuseStep 2794661 = 523999) (by norm_num)
theorem B1860797 : Blo 1240438 1860797 := bbase (se 3 (by rfl) ⟨348899, by rfl⟩ : syracuseStep 1860797 = 697799) (by norm_num)
theorem B1860821 : Blo 1240438 1860821 := bbase (se 7 (by rfl) ⟨21806, by rfl⟩ : syracuseStep 1860821 = 43613) (by norm_num)
theorem B2516189 : Blo 1240438 2516189 := bbase (se 3 (by rfl) ⟨471785, by rfl⟩ : syracuseStep 2516189 = 943571) (by norm_num)
theorem B1860845 : Blo 1240438 1860845 := bbase (se 3 (by rfl) ⟨348908, by rfl⟩ : syracuseStep 1860845 = 697817) (by norm_num)
theorem B2794733 : Blo 1240438 2794733 := bbase (se 3 (by rfl) ⟨524012, by rfl⟩ : syracuseStep 2794733 = 1048025) (by norm_num)
theorem B1860869 : Blo 1240438 1860869 := bbase (se 4 (by rfl) ⟨174456, by rfl⟩ : syracuseStep 1860869 = 348913) (by norm_num)
theorem B1860893 : Blo 1240438 1860893 := bbase (se 3 (by rfl) ⟨348917, by rfl⟩ : syracuseStep 1860893 = 697835) (by norm_num)
theorem B4187429 : Blo 1240438 4187429 := bbase (se 4 (by rfl) ⟨392571, by rfl⟩ : syracuseStep 4187429 = 785143) (by norm_num)
theorem B2516269 : Blo 1240438 2516269 := bbase (se 3 (by rfl) ⟨471800, by rfl⟩ : syracuseStep 2516269 = 943601) (by norm_num)
theorem B1860917 : Blo 1240438 1860917 := bbase (se 5 (by rfl) ⟨87230, by rfl⟩ : syracuseStep 1860917 = 174461) (by norm_num)
theorem B2794805 : Blo 1240438 2794805 := bbase (se 5 (by rfl) ⟨131006, by rfl⟩ : syracuseStep 2794805 = 262013) (by norm_num)
theorem B1860941 : Blo 1240438 1860941 := bbase (se 3 (by rfl) ⟨348926, by rfl⟩ : syracuseStep 1860941 = 697853) (by norm_num)
theorem B12739925 : Blo 1240438 12739925 := bbase (se 12 (by rfl) ⟨4665, by rfl⟩ : syracuseStep 12739925 = 9331) (by norm_num)
theorem B1860965 : Blo 1240438 1860965 := bbase (se 4 (by rfl) ⟨174465, by rfl⟩ : syracuseStep 1860965 = 348931) (by norm_num)
theorem B1860989 : Blo 1240438 1860989 := bbase (se 3 (by rfl) ⟨348935, by rfl⟩ : syracuseStep 1860989 = 697871) (by norm_num)
theorem B2794877 : Blo 1240438 2794877 := bbase (se 3 (by rfl) ⟨524039, by rfl⟩ : syracuseStep 2794877 = 1048079) (by norm_num)
theorem B1861013 : Blo 1240438 1861013 := bbase (se 6 (by rfl) ⟨43617, by rfl⟩ : syracuseStep 1861013 = 87235) (by norm_num)
theorem B1861037 : Blo 1240438 1861037 := bbase (se 3 (by rfl) ⟨348944, by rfl⟩ : syracuseStep 1861037 = 697889) (by norm_num)
theorem B1861061 : Blo 1240438 1861061 := bbase (se 4 (by rfl) ⟨174474, by rfl⟩ : syracuseStep 1861061 = 348949) (by norm_num)
theorem B4711877 : Blo 1240438 4711877 := bbase (se 4 (by rfl) ⟨441738, by rfl⟩ : syracuseStep 4711877 = 883477) (by norm_num)
theorem B2794949 : Blo 1240438 2794949 := bbase (se 4 (by rfl) ⟨262026, by rfl⟩ : syracuseStep 2794949 = 524053) (by norm_num)
theorem B1861085 : Blo 1240438 1861085 := bbase (se 3 (by rfl) ⟨348953, by rfl⟩ : syracuseStep 1861085 = 697907) (by norm_num)
theorem B5301733 : Blo 1240438 5301733 := bbase (se 4 (by rfl) ⟨497037, by rfl⟩ : syracuseStep 5301733 = 994075) (by norm_num)
theorem B1861109 : Blo 1240438 1861109 := bbase (se 5 (by rfl) ⟨87239, by rfl⟩ : syracuseStep 1861109 = 174479) (by norm_num)
theorem B6284789 : Blo 1240438 6284789 := bbase (se 5 (by rfl) ⟨294599, by rfl⟩ : syracuseStep 6284789 = 589199) (by norm_num)
theorem B1861133 : Blo 1240438 1861133 := bbase (se 3 (by rfl) ⟨348962, by rfl⟩ : syracuseStep 1861133 = 697925) (by norm_num)
theorem B2795021 : Blo 1240438 2795021 := bbase (se 3 (by rfl) ⟨524066, by rfl⟩ : syracuseStep 2795021 = 1048133) (by norm_num)
theorem B8488469 : Blo 1240438 8488469 := bbase (se 6 (by rfl) ⟨198948, by rfl⟩ : syracuseStep 8488469 = 397897) (by norm_num)
theorem B1861157 : Blo 1240438 1861157 := bbase (se 4 (by rfl) ⟨174483, by rfl⟩ : syracuseStep 1861157 = 348967) (by norm_num)
theorem B1361453 : Blo 1240438 1361453 := bbase (se 3 (by rfl) ⟨255272, by rfl⟩ : syracuseStep 1361453 = 510545) (by norm_num)
theorem B1492525 : Blo 1240438 1492525 := bbase (se 3 (by rfl) ⟨279848, by rfl⟩ : syracuseStep 1492525 = 559697) (by norm_num)
theorem B1861181 : Blo 1240438 1861181 := bbase (se 3 (by rfl) ⟨348971, by rfl⟩ : syracuseStep 1861181 = 697943) (by norm_num)
theorem B1861205 : Blo 1240438 1861205 := bbase (se 8 (by rfl) ⟨10905, by rfl⟩ : syracuseStep 1861205 = 21811) (by norm_num)
theorem B2795093 : Blo 1240438 2795093 := bbase (se 8 (by rfl) ⟨16377, by rfl⟩ : syracuseStep 2795093 = 32755) (by norm_num)
theorem B1861229 : Blo 1240438 1861229 := bbase (se 3 (by rfl) ⟨348980, by rfl⟩ : syracuseStep 1861229 = 697961) (by norm_num)
theorem B1861253 : Blo 1240438 1861253 := bbase (se 4 (by rfl) ⟨174492, by rfl⟩ : syracuseStep 1861253 = 348985) (by norm_num)
theorem B1861277 : Blo 1240438 1861277 := bbase (se 3 (by rfl) ⟨348989, by rfl⟩ : syracuseStep 1861277 = 697979) (by norm_num)
theorem B2795165 : Blo 1240438 2795165 := bbase (se 3 (by rfl) ⟨524093, by rfl⟩ : syracuseStep 2795165 = 1048187) (by norm_num)
theorem B1861301 : Blo 1240438 1861301 := bbase (se 5 (by rfl) ⟨87248, by rfl⟩ : syracuseStep 1861301 = 174497) (by norm_num)
theorem B1861325 : Blo 1240438 1861325 := bbase (se 3 (by rfl) ⟨348998, by rfl⟩ : syracuseStep 1861325 = 697997) (by norm_num)
theorem B4187861 : Blo 1240438 4187861 := bbase (se 7 (by rfl) ⟨49076, by rfl⟩ : syracuseStep 4187861 = 98153) (by norm_num)
theorem B14141141 : Blo 1240438 14141141 := bbase (se 7 (by rfl) ⟨165716, by rfl⟩ : syracuseStep 14141141 = 331433) (by norm_num)
theorem B1861349 : Blo 1240438 1861349 := bbase (se 4 (by rfl) ⟨174501, by rfl⟩ : syracuseStep 1861349 = 349003) (by norm_num)
theorem B4712165 : Blo 1240438 4712165 := bbase (se 4 (by rfl) ⟨441765, by rfl⟩ : syracuseStep 4712165 = 883531) (by norm_num)
theorem B2795237 : Blo 1240438 2795237 := bbase (se 4 (by rfl) ⟨262053, by rfl⟩ : syracuseStep 2795237 = 524107) (by norm_num)
theorem B1861373 : Blo 1240438 1861373 := bbase (se 3 (by rfl) ⟨349007, by rfl⟩ : syracuseStep 1861373 = 698015) (by norm_num)
theorem B1861397 : Blo 1240438 1861397 := bbase (se 6 (by rfl) ⟨43626, by rfl⟩ : syracuseStep 1861397 = 87253) (by norm_num)
theorem B1861421 : Blo 1240438 1861421 := bbase (se 3 (by rfl) ⟨349016, by rfl⟩ : syracuseStep 1861421 = 698033) (by norm_num)
theorem B2795309 : Blo 1240438 2795309 := bbase (se 3 (by rfl) ⟨524120, by rfl⟩ : syracuseStep 2795309 = 1048241) (by norm_num)
theorem B1861445 : Blo 1240438 1861445 := bbase (se 4 (by rfl) ⟨174510, by rfl⟩ : syracuseStep 1861445 = 349021) (by norm_num)
theorem B4474693 : Blo 1240438 4474693 := bbase (se 4 (by rfl) ⟨419502, by rfl⟩ : syracuseStep 4474693 = 839005) (by norm_num)
theorem B1861469 : Blo 1240438 1861469 := bbase (se 3 (by rfl) ⟨349025, by rfl⟩ : syracuseStep 1861469 = 698051) (by norm_num)
theorem B1861493 : Blo 1240438 1861493 := bbase (se 5 (by rfl) ⟨87257, by rfl⟩ : syracuseStep 1861493 = 174515) (by norm_num)
theorem B2795381 : Blo 1240438 2795381 := bbase (se 5 (by rfl) ⟨131033, by rfl⟩ : syracuseStep 2795381 = 262067) (by norm_num)
theorem B1861517 : Blo 1240438 1861517 := bbase (se 3 (by rfl) ⟨349034, by rfl⟩ : syracuseStep 1861517 = 698069) (by norm_num)
theorem B1861541 : Blo 1240438 1861541 := bbase (se 4 (by rfl) ⟨174519, by rfl⟩ : syracuseStep 1861541 = 349039) (by norm_num)
theorem B1861565 : Blo 1240438 1861565 := bbase (se 3 (by rfl) ⟨349043, by rfl⟩ : syracuseStep 1861565 = 698087) (by norm_num)
theorem B2795453 : Blo 1240438 2795453 := bbase (se 3 (by rfl) ⟨524147, by rfl⟩ : syracuseStep 2795453 = 1048295) (by norm_num)
theorem B5105605 : Blo 1240438 5105605 := bbase (se 4 (by rfl) ⟨478650, by rfl⟩ : syracuseStep 5105605 = 957301) (by norm_num)
theorem B1861589 : Blo 1240438 1861589 := bbase (se 7 (by rfl) ⟨21815, by rfl⟩ : syracuseStep 1861589 = 43631) (by norm_num)
theorem B1861613 : Blo 1240438 1861613 := bbase (se 3 (by rfl) ⟨349052, by rfl⟩ : syracuseStep 1861613 = 698105) (by norm_num)
theorem B1861637 : Blo 1240438 1861637 := bbase (se 4 (by rfl) ⟨174528, by rfl⟩ : syracuseStep 1861637 = 349057) (by norm_num)
theorem B1861661 : Blo 1240438 1861661 := bbase (se 3 (by rfl) ⟨349061, by rfl⟩ : syracuseStep 1861661 = 698123) (by norm_num)
theorem B1861685 : Blo 1240438 1861685 := bbase (se 5 (by rfl) ⟨87266, by rfl⟩ : syracuseStep 1861685 = 174533) (by norm_num)
theorem B1861709 : Blo 1240438 1861709 := bbase (se 3 (by rfl) ⟨349070, by rfl⟩ : syracuseStep 1861709 = 698141) (by norm_num)
theorem B2238557 : Blo 1240438 2238557 := bbase (se 3 (by rfl) ⟨419729, by rfl⟩ : syracuseStep 2238557 = 839459) (by norm_num)
theorem B1861733 : Blo 1240438 1861733 := bbase (se 4 (by rfl) ⟨174537, by rfl⟩ : syracuseStep 1861733 = 349075) (by norm_num)
theorem B1861757 : Blo 1240438 1861757 := bbase (se 3 (by rfl) ⟨349079, by rfl⟩ : syracuseStep 1861757 = 698159) (by norm_num)
theorem B4188293 : Blo 1240438 4188293 := bbase (se 4 (by rfl) ⟨392652, by rfl⟩ : syracuseStep 4188293 = 785305) (by norm_num)
theorem B20400277 : Blo 1240438 20400277 := bbase (se 6 (by rfl) ⟨478131, by rfl⟩ : syracuseStep 20400277 = 956263) (by norm_num)
theorem B1861781 : Blo 1240438 1861781 := bbase (se 6 (by rfl) ⟨43635, by rfl⟩ : syracuseStep 1861781 = 87271) (by norm_num)
theorem B7071893 : Blo 1240438 7071893 := bbase (se 6 (by rfl) ⟨165747, by rfl⟩ : syracuseStep 7071893 = 331495) (by norm_num)
theorem B1861805 : Blo 1240438 1861805 := bbase (se 3 (by rfl) ⟨349088, by rfl⟩ : syracuseStep 1861805 = 698177) (by norm_num)
theorem B3532997 : Blo 1240438 3532997 := bbase (se 4 (by rfl) ⟨331218, by rfl⟩ : syracuseStep 3532997 = 662437) (by norm_num)
theorem B1861829 : Blo 1240438 1861829 := bbase (se 4 (by rfl) ⟨174546, by rfl⟩ : syracuseStep 1861829 = 349093) (by norm_num)
theorem B1861853 : Blo 1240438 1861853 := bbase (se 3 (by rfl) ⟨349097, by rfl⟩ : syracuseStep 1861853 = 698195) (by norm_num)
theorem B1861877 : Blo 1240438 1861877 := bbase (se 5 (by rfl) ⟨87275, by rfl⟩ : syracuseStep 1861877 = 174551) (by norm_num)
theorem B1861901 : Blo 1240438 1861901 := bbase (se 3 (by rfl) ⟨349106, by rfl⟩ : syracuseStep 1861901 = 698213) (by norm_num)
theorem B1861925 : Blo 1240438 1861925 := bbase (se 4 (by rfl) ⟨174555, by rfl⟩ : syracuseStep 1861925 = 349111) (by norm_num)
theorem B1861949 : Blo 1240438 1861949 := bbase (se 3 (by rfl) ⟨349115, by rfl⟩ : syracuseStep 1861949 = 698231) (by norm_num)
theorem B1861973 : Blo 1240438 1861973 := bbase (se 10 (by rfl) ⟨2727, by rfl⟩ : syracuseStep 1861973 = 5455) (by norm_num)
theorem B1861997 : Blo 1240438 1861997 := bbase (se 3 (by rfl) ⟨349124, by rfl⟩ : syracuseStep 1861997 = 698249) (by norm_num)
theorem B1862021 : Blo 1240438 1862021 := bbase (se 4 (by rfl) ⟨174564, by rfl⟩ : syracuseStep 1862021 = 349129) (by norm_num)
theorem B1862045 : Blo 1240438 1862045 := bbase (se 3 (by rfl) ⟨349133, by rfl⟩ : syracuseStep 1862045 = 698267) (by norm_num)
theorem B3140005 : Blo 1240438 3140005 := bbase (se 4 (by rfl) ⟨294375, by rfl⟩ : syracuseStep 3140005 = 588751) (by norm_num)
theorem B1862069 : Blo 1240438 1862069 := bbase (se 5 (by rfl) ⟨87284, by rfl⟩ : syracuseStep 1862069 = 174569) (by norm_num)
theorem B1862093 : Blo 1240438 1862093 := bbase (se 3 (by rfl) ⟨349142, by rfl⟩ : syracuseStep 1862093 = 698285) (by norm_num)
theorem B1862117 : Blo 1240438 1862117 := bbase (se 4 (by rfl) ⟨174573, by rfl⟩ : syracuseStep 1862117 = 349147) (by norm_num)
theorem B1862141 : Blo 1240438 1862141 := bbase (se 3 (by rfl) ⟨349151, by rfl⟩ : syracuseStep 1862141 = 698303) (by norm_num)
theorem B1591825 : Blo 1240438 1591825 := bbase (se 2 (by rfl) ⟨596934, by rfl⟩ : syracuseStep 1591825 = 1193869) (by norm_num)
theorem B3140117 : Blo 1240438 3140117 := bbase (se 6 (by rfl) ⟨73596, by rfl⟩ : syracuseStep 3140117 = 147193) (by norm_num)
theorem B16116245 : Blo 1240438 16116245 := bbase (se 6 (by rfl) ⟨377724, by rfl⟩ : syracuseStep 16116245 = 755449) (by norm_num)
theorem B1862165 : Blo 1240438 1862165 := bbase (se 6 (by rfl) ⟨43644, by rfl⟩ : syracuseStep 1862165 = 87289) (by norm_num)
theorem B1862189 : Blo 1240438 1862189 := bbase (se 3 (by rfl) ⟨349160, by rfl⟩ : syracuseStep 1862189 = 698321) (by norm_num)
theorem B4188725 : Blo 1240438 4188725 := bbase (se 5 (by rfl) ⟨196346, by rfl⟩ : syracuseStep 4188725 = 392693) (by norm_num)
theorem B1862213 : Blo 1240438 1862213 := bbase (se 4 (by rfl) ⟨174582, by rfl⟩ : syracuseStep 1862213 = 349165) (by norm_num)
theorem B1591897 : Blo 1240438 1591897 := bbase (se 2 (by rfl) ⟨596961, by rfl⟩ : syracuseStep 1591897 = 1193923) (by norm_num)
theorem B1862237 : Blo 1240438 1862237 := bbase (se 3 (by rfl) ⟨349169, by rfl⟩ : syracuseStep 1862237 = 698339) (by norm_num)
theorem B1862261 : Blo 1240438 1862261 := bbase (se 5 (by rfl) ⟨87293, by rfl⟩ : syracuseStep 1862261 = 174587) (by norm_num)
theorem B1862285 : Blo 1240438 1862285 := bbase (se 3 (by rfl) ⟨349178, by rfl⟩ : syracuseStep 1862285 = 698357) (by norm_num)
theorem B1862309 : Blo 1240438 1862309 := bbase (se 4 (by rfl) ⟨174591, by rfl⟩ : syracuseStep 1862309 = 349183) (by norm_num)
theorem B1862333 : Blo 1240438 1862333 := bbase (se 3 (by rfl) ⟨349187, by rfl⟩ : syracuseStep 1862333 = 698375) (by norm_num)
theorem B5663429 : Blo 1240438 5663429 := bbase (se 4 (by rfl) ⟨530946, by rfl⟩ : syracuseStep 5663429 = 1061893) (by norm_num)
theorem B3140309 : Blo 1240438 3140309 := bbase (se 7 (by rfl) ⟨36800, by rfl⟩ : syracuseStep 3140309 = 73601) (by norm_num)
theorem B1862357 : Blo 1240438 1862357 := bbase (se 7 (by rfl) ⟨21824, by rfl⟩ : syracuseStep 1862357 = 43649) (by norm_num)
theorem B1862381 : Blo 1240438 1862381 := bbase (se 3 (by rfl) ⟨349196, by rfl⟩ : syracuseStep 1862381 = 698393) (by norm_num)
theorem B1862405 : Blo 1240438 1862405 := bbase (se 4 (by rfl) ⟨174600, by rfl⟩ : syracuseStep 1862405 = 349201) (by norm_num)
theorem B6286085 : Blo 1240438 6286085 := bbase (se 4 (by rfl) ⟨589320, by rfl⟩ : syracuseStep 6286085 = 1178641) (by norm_num)
theorem B6712085 : Blo 1240438 6712085 := bbase (se 6 (by rfl) ⟨157314, by rfl⟩ : syracuseStep 6712085 = 314629) (by norm_num)
theorem B1862429 : Blo 1240438 1862429 := bbase (se 3 (by rfl) ⟨349205, by rfl⟩ : syracuseStep 1862429 = 698411) (by norm_num)
theorem B1862453 : Blo 1240438 1862453 := bbase (se 5 (by rfl) ⟨87302, by rfl⟩ : syracuseStep 1862453 = 174605) (by norm_num)
theorem B1395517 : Blo 1240438 1395517 := bbase (se 3 (by rfl) ⟨261659, by rfl⟩ : syracuseStep 1395517 = 523319) (by norm_num)
theorem B1862477 : Blo 1240438 1862477 := bbase (se 3 (by rfl) ⟨349214, by rfl⟩ : syracuseStep 1862477 = 698429) (by norm_num)
theorem B1395553 : Blo 1240438 1395553 := bbase (se 2 (by rfl) ⟨523332, by rfl⟩ : syracuseStep 1395553 = 1046665) (by norm_num)
theorem B3533669 : Blo 1240438 3533669 := bbase (se 4 (by rfl) ⟨331281, by rfl⟩ : syracuseStep 3533669 = 662563) (by norm_num)
theorem B1862501 : Blo 1240438 1862501 := bbase (se 4 (by rfl) ⟨174609, by rfl⟩ : syracuseStep 1862501 = 349219) (by norm_num)
theorem B1862525 : Blo 1240438 1862525 := bbase (se 3 (by rfl) ⟨349223, by rfl⟩ : syracuseStep 1862525 = 698447) (by norm_num)
theorem B1395589 : Blo 1240438 1395589 := bbase (se 4 (by rfl) ⟨130836, by rfl⟩ : syracuseStep 1395589 = 261673) (by norm_num)
theorem B3976069 : Blo 1240438 3976069 := bbase (se 4 (by rfl) ⟨372756, by rfl⟩ : syracuseStep 3976069 = 745513) (by norm_num)
theorem B4713349 : Blo 1240438 4713349 := bbase (se 4 (by rfl) ⟨441876, by rfl⟩ : syracuseStep 4713349 = 883753) (by norm_num)
theorem B1862549 : Blo 1240438 1862549 := bbase (se 6 (by rfl) ⟨43653, by rfl⟩ : syracuseStep 1862549 = 87307) (by norm_num)
theorem B4533157 : Blo 1240438 4533157 := bbase (se 4 (by rfl) ⟨424983, by rfl⟩ : syracuseStep 4533157 = 849967) (by norm_num)
theorem B1395625 : Blo 1240438 1395625 := bbase (se 2 (by rfl) ⟨523359, by rfl⟩ : syracuseStep 1395625 = 1046719) (by norm_num)
theorem B1862573 : Blo 1240438 1862573 := bbase (se 3 (by rfl) ⟨349232, by rfl⟩ : syracuseStep 1862573 = 698465) (by norm_num)
theorem B1862597 : Blo 1240438 1862597 := bbase (se 4 (by rfl) ⟨174618, by rfl⟩ : syracuseStep 1862597 = 349237) (by norm_num)
theorem B1395661 : Blo 1240438 1395661 := bbase (se 3 (by rfl) ⟨261686, by rfl⟩ : syracuseStep 1395661 = 523373) (by norm_num)
theorem B1862621 : Blo 1240438 1862621 := bbase (se 3 (by rfl) ⟨349241, by rfl⟩ : syracuseStep 1862621 = 698483) (by norm_num)
theorem B4189157 : Blo 1240438 4189157 := bbase (se 4 (by rfl) ⟨392733, by rfl⟩ : syracuseStep 4189157 = 785467) (by norm_num)
theorem B1395697 : Blo 1240438 1395697 := bbase (se 2 (by rfl) ⟨523386, by rfl⟩ : syracuseStep 1395697 = 1046773) (by norm_num)
theorem B1862645 : Blo 1240438 1862645 := bbase (se 5 (by rfl) ⟨87311, by rfl⟩ : syracuseStep 1862645 = 174623) (by norm_num)
theorem B1862669 : Blo 1240438 1862669 := bbase (se 3 (by rfl) ⟨349250, by rfl⟩ : syracuseStep 1862669 = 698501) (by norm_num)
theorem B1395733 : Blo 1240438 1395733 := bbase (se 6 (by rfl) ⟨32712, by rfl⟩ : syracuseStep 1395733 = 65425) (by norm_num)
theorem B1862693 : Blo 1240438 1862693 := bbase (se 4 (by rfl) ⟨174627, by rfl⟩ : syracuseStep 1862693 = 349255) (by norm_num)
theorem B3140653 : Blo 1240438 3140653 := bbase (se 3 (by rfl) ⟨588872, by rfl⟩ : syracuseStep 3140653 = 1177745) (by norm_num)
theorem B1395769 : Blo 1240438 1395769 := bbase (se 2 (by rfl) ⟨523413, by rfl⟩ : syracuseStep 1395769 = 1046827) (by norm_num)
theorem B1862717 : Blo 1240438 1862717 := bbase (se 3 (by rfl) ⟨349259, by rfl⟩ : syracuseStep 1862717 = 698519) (by norm_num)
theorem B1862741 : Blo 1240438 1862741 := bbase (se 8 (by rfl) ⟨10914, by rfl⟩ : syracuseStep 1862741 = 21829) (by norm_num)
theorem B1395805 : Blo 1240438 1395805 := bbase (se 3 (by rfl) ⟨261713, by rfl⟩ : syracuseStep 1395805 = 523427) (by norm_num)
theorem B2518117 : Blo 1240438 2518117 := bbase (se 4 (by rfl) ⟨236073, by rfl⟩ : syracuseStep 2518117 = 472147) (by norm_num)
theorem B1862765 : Blo 1240438 1862765 := bbase (se 3 (by rfl) ⟨349268, by rfl⟩ : syracuseStep 1862765 = 698537) (by norm_num)
theorem B1395841 : Blo 1240438 1395841 := bbase (se 2 (by rfl) ⟨523440, by rfl⟩ : syracuseStep 1395841 = 1046881) (by norm_num)
theorem B1862789 : Blo 1240438 1862789 := bbase (se 4 (by rfl) ⟨174636, by rfl⟩ : syracuseStep 1862789 = 349273) (by norm_num)
theorem B10603669 : Blo 1240438 10603669 := bbase (se 6 (by rfl) ⟨248523, by rfl⟩ : syracuseStep 10603669 = 497047) (by norm_num)
theorem B3140765 : Blo 1240438 3140765 := bbase (se 3 (by rfl) ⟨588893, by rfl⟩ : syracuseStep 3140765 = 1177787) (by norm_num)
theorem B1862813 : Blo 1240438 1862813 := bbase (se 3 (by rfl) ⟨349277, by rfl⟩ : syracuseStep 1862813 = 698555) (by norm_num)
theorem B1395877 : Blo 1240438 1395877 := bbase (se 4 (by rfl) ⟨130863, by rfl⟩ : syracuseStep 1395877 = 261727) (by norm_num)
theorem B4713653 : Blo 1240438 4713653 := bbase (se 5 (by rfl) ⟨220952, by rfl⟩ : syracuseStep 4713653 = 441905) (by norm_num)
theorem B1862837 : Blo 1240438 1862837 := bbase (se 5 (by rfl) ⟨87320, by rfl⟩ : syracuseStep 1862837 = 174641) (by norm_num)
theorem B2649277 : Blo 1240438 2649277 := bbase (se 3 (by rfl) ⟨496739, by rfl⟩ : syracuseStep 2649277 = 993479) (by norm_num)
theorem B1395913 : Blo 1240438 1395913 := bbase (se 2 (by rfl) ⟨523467, by rfl⟩ : syracuseStep 1395913 = 1046935) (by norm_num)
theorem B1862861 : Blo 1240438 1862861 := bbase (se 3 (by rfl) ⟨349286, by rfl⟩ : syracuseStep 1862861 = 698573) (by norm_num)
theorem B1862885 : Blo 1240438 1862885 := bbase (se 4 (by rfl) ⟨174645, by rfl⟩ : syracuseStep 1862885 = 349291) (by norm_num)
theorem B1395949 : Blo 1240438 1395949 := bbase (se 3 (by rfl) ⟨261740, by rfl⟩ : syracuseStep 1395949 = 523481) (by norm_num)
theorem B1862909 : Blo 1240438 1862909 := bbase (se 3 (by rfl) ⟨349295, by rfl⟩ : syracuseStep 1862909 = 698591) (by norm_num)
theorem B1395985 : Blo 1240438 1395985 := bbase (se 2 (by rfl) ⟨523494, by rfl⟩ : syracuseStep 1395985 = 1046989) (by norm_num)
theorem B3534101 : Blo 1240438 3534101 := bbase (se 6 (by rfl) ⟨82830, by rfl⟩ : syracuseStep 3534101 = 165661) (by norm_num)
theorem B1862933 : Blo 1240438 1862933 := bbase (se 6 (by rfl) ⟨43662, by rfl⟩ : syracuseStep 1862933 = 87325) (by norm_num)
theorem B1862957 : Blo 1240438 1862957 := bbase (se 3 (by rfl) ⟨349304, by rfl⟩ : syracuseStep 1862957 = 698609) (by norm_num)
theorem B1396021 : Blo 1240438 1396021 := bbase (se 5 (by rfl) ⟨65438, by rfl⟩ : syracuseStep 1396021 = 130877) (by norm_num)
theorem B1862981 : Blo 1240438 1862981 := bbase (se 4 (by rfl) ⟨174654, by rfl⟩ : syracuseStep 1862981 = 349309) (by norm_num)
theorem B1396057 : Blo 1240438 1396057 := bbase (se 2 (by rfl) ⟨523521, by rfl⟩ : syracuseStep 1396057 = 1047043) (by norm_num)
theorem B3140957 : Blo 1240438 3140957 := bbase (se 3 (by rfl) ⟨588929, by rfl⟩ : syracuseStep 3140957 = 1177859) (by norm_num)
theorem B1863005 : Blo 1240438 1863005 := bbase (se 3 (by rfl) ⟨349313, by rfl⟩ : syracuseStep 1863005 = 698627) (by norm_num)
theorem B1863029 : Blo 1240438 1863029 := bbase (se 5 (by rfl) ⟨87329, by rfl⟩ : syracuseStep 1863029 = 174659) (by norm_num)
theorem B1396093 : Blo 1240438 1396093 := bbase (se 3 (by rfl) ⟨261767, by rfl⟩ : syracuseStep 1396093 = 523535) (by norm_num)
theorem B1592717 : Blo 1240438 1592717 := bbase (se 3 (by rfl) ⟨298634, by rfl⟩ : syracuseStep 1592717 = 597269) (by norm_num)
theorem B1863053 : Blo 1240438 1863053 := bbase (se 3 (by rfl) ⟨349322, by rfl⟩ : syracuseStep 1863053 = 698645) (by norm_num)
theorem B4189589 : Blo 1240438 4189589 := bbase (se 6 (by rfl) ⟨98193, by rfl⟩ : syracuseStep 4189589 = 196387) (by norm_num)
theorem B1396129 : Blo 1240438 1396129 := bbase (se 2 (by rfl) ⟨523548, by rfl⟩ : syracuseStep 1396129 = 1047097) (by norm_num)
theorem B1863077 : Blo 1240438 1863077 := bbase (se 4 (by rfl) ⟨174663, by rfl⟩ : syracuseStep 1863077 = 349327) (by norm_num)
theorem B4779445 : Blo 1240438 4779445 := bbase (se 5 (by rfl) ⟨224036, by rfl⟩ : syracuseStep 4779445 = 448073) (by norm_num)
theorem B1863101 : Blo 1240438 1863101 := bbase (se 3 (by rfl) ⟨349331, by rfl⟩ : syracuseStep 1863101 = 698663) (by norm_num)
theorem B1396165 : Blo 1240438 1396165 := bbase (se 4 (by rfl) ⟨130890, by rfl⟩ : syracuseStep 1396165 = 261781) (by norm_num)
theorem B1863125 : Blo 1240438 1863125 := bbase (se 7 (by rfl) ⟨21833, by rfl⟩ : syracuseStep 1863125 = 43667) (by norm_num)
theorem B1396201 : Blo 1240438 1396201 := bbase (se 2 (by rfl) ⟨523575, by rfl⟩ : syracuseStep 1396201 = 1047151) (by norm_num)
theorem B1863149 : Blo 1240438 1863149 := bbase (se 3 (by rfl) ⟨349340, by rfl⟩ : syracuseStep 1863149 = 698681) (by norm_num)
theorem B1863173 : Blo 1240438 1863173 := bbase (se 4 (by rfl) ⟨174672, by rfl⟩ : syracuseStep 1863173 = 349345) (by norm_num)
theorem B1396237 : Blo 1240438 1396237 := bbase (se 3 (by rfl) ⟨261794, by rfl⟩ : syracuseStep 1396237 = 523589) (by norm_num)
theorem B1863197 : Blo 1240438 1863197 := bbase (se 3 (by rfl) ⟨349349, by rfl⟩ : syracuseStep 1863197 = 698699) (by norm_num)
theorem B1379885 : Blo 1240438 1379885 := bbase (se 3 (by rfl) ⟨258728, by rfl⟩ : syracuseStep 1379885 = 517457) (by norm_num)
theorem B1396273 : Blo 1240438 1396273 := bbase (se 2 (by rfl) ⟨523602, by rfl⟩ : syracuseStep 1396273 = 1047205) (by norm_num)
theorem B1863221 : Blo 1240438 1863221 := bbase (se 5 (by rfl) ⟨87338, by rfl⟩ : syracuseStep 1863221 = 174677) (by norm_num)
theorem B2518589 : Blo 1240438 2518589 := bbase (se 3 (by rfl) ⟨472235, by rfl⟩ : syracuseStep 2518589 = 944471) (by norm_num)
theorem B1863245 : Blo 1240438 1863245 := bbase (se 3 (by rfl) ⟨349358, by rfl⟩ : syracuseStep 1863245 = 698717) (by norm_num)
theorem B1396309 : Blo 1240438 1396309 := bbase (se 8 (by rfl) ⟨8181, by rfl⟩ : syracuseStep 1396309 = 16363) (by norm_num)
theorem B1863269 : Blo 1240438 1863269 := bbase (se 4 (by rfl) ⟨174681, by rfl⟩ : syracuseStep 1863269 = 349363) (by norm_num)
theorem B1396345 : Blo 1240438 1396345 := bbase (se 2 (by rfl) ⟨523629, by rfl⟩ : syracuseStep 1396345 = 1047259) (by norm_num)
theorem B1863293 : Blo 1240438 1863293 := bbase (se 3 (by rfl) ⟨349367, by rfl⟩ : syracuseStep 1863293 = 698735) (by norm_num)
theorem B1863317 : Blo 1240438 1863317 := bbase (se 6 (by rfl) ⟨43671, by rfl⟩ : syracuseStep 1863317 = 87343) (by norm_num)
theorem B1396381 : Blo 1240438 1396381 := bbase (se 3 (by rfl) ⟨261821, by rfl⟩ : syracuseStep 1396381 = 523643) (by norm_num)
theorem B2649773 : Blo 1240438 2649773 := bbase (se 3 (by rfl) ⟨496832, by rfl⟩ : syracuseStep 2649773 = 993665) (by norm_num)
theorem B1863341 : Blo 1240438 1863341 := bbase (se 3 (by rfl) ⟨349376, by rfl⟩ : syracuseStep 1863341 = 698753) (by norm_num)
theorem B3141301 : Blo 1240438 3141301 := bbase (se 5 (by rfl) ⟨147248, by rfl⟩ : syracuseStep 3141301 = 294497) (by norm_num)
theorem B1396417 : Blo 1240438 1396417 := bbase (se 2 (by rfl) ⟨523656, by rfl⟩ : syracuseStep 1396417 = 1047313) (by norm_num)
theorem B1863365 : Blo 1240438 1863365 := bbase (se 4 (by rfl) ⟨174690, by rfl⟩ : syracuseStep 1863365 = 349381) (by norm_num)
theorem B1863389 : Blo 1240438 1863389 := bbase (se 3 (by rfl) ⟨349385, by rfl⟩ : syracuseStep 1863389 = 698771) (by norm_num)
theorem B1396453 : Blo 1240438 1396453 := bbase (se 4 (by rfl) ⟨130917, by rfl⟩ : syracuseStep 1396453 = 261835) (by norm_num)
theorem B6713077 : Blo 1240438 6713077 := bbase (se 5 (by rfl) ⟨314675, by rfl⟩ : syracuseStep 6713077 = 629351) (by norm_num)
theorem B1863413 : Blo 1240438 1863413 := bbase (se 5 (by rfl) ⟨87347, by rfl⟩ : syracuseStep 1863413 = 174695) (by norm_num)
theorem B1396489 : Blo 1240438 1396489 := bbase (se 2 (by rfl) ⟨523683, by rfl⟩ : syracuseStep 1396489 = 1047367) (by norm_num)
theorem B1863437 : Blo 1240438 1863437 := bbase (se 3 (by rfl) ⟨349394, by rfl⟩ : syracuseStep 1863437 = 698789) (by norm_num)
theorem B3141413 : Blo 1240438 3141413 := bbase (se 4 (by rfl) ⟨294507, by rfl⟩ : syracuseStep 3141413 = 589015) (by norm_num)
theorem B1863461 : Blo 1240438 1863461 := bbase (se 4 (by rfl) ⟨174699, by rfl⟩ : syracuseStep 1863461 = 349399) (by norm_num)
theorem B2354989 : Blo 1240438 2354989 := bbase (se 3 (by rfl) ⟨441560, by rfl⟩ : syracuseStep 2354989 = 883121) (by norm_num)
theorem B1396525 : Blo 1240438 1396525 := bbase (se 3 (by rfl) ⟨261848, by rfl⟩ : syracuseStep 1396525 = 523697) (by norm_num)
theorem B1863485 : Blo 1240438 1863485 := bbase (se 3 (by rfl) ⟨349403, by rfl⟩ : syracuseStep 1863485 = 698807) (by norm_num)
theorem B4190021 : Blo 1240438 4190021 := bbase (se 4 (by rfl) ⟨392814, by rfl⟩ : syracuseStep 4190021 = 785629) (by norm_num)
theorem B1396561 : Blo 1240438 1396561 := bbase (se 2 (by rfl) ⟨523710, by rfl⟩ : syracuseStep 1396561 = 1047421) (by norm_num)
theorem B15109973 : Blo 1240438 15109973 := bbase (se 9 (by rfl) ⟨44267, by rfl⟩ : syracuseStep 15109973 = 88535) (by norm_num)
theorem B1863509 : Blo 1240438 1863509 := bbase (se 9 (by rfl) ⟨5459, by rfl⟩ : syracuseStep 1863509 = 10919) (by norm_num)
theorem B1863533 : Blo 1240438 1863533 := bbase (se 3 (by rfl) ⟨349412, by rfl⟩ : syracuseStep 1863533 = 698825) (by norm_num)
theorem B1396597 : Blo 1240438 1396597 := bbase (se 5 (by rfl) ⟨65465, by rfl⟩ : syracuseStep 1396597 = 130931) (by norm_num)
theorem B1863557 : Blo 1240438 1863557 := bbase (se 4 (by rfl) ⟨174708, by rfl⟩ : syracuseStep 1863557 = 349417) (by norm_num)
theorem B1396633 : Blo 1240438 1396633 := bbase (se 2 (by rfl) ⟨523737, by rfl⟩ : syracuseStep 1396633 = 1047475) (by norm_num)
theorem B1863581 : Blo 1240438 1863581 := bbase (se 3 (by rfl) ⟨349421, by rfl⟩ : syracuseStep 1863581 = 698843) (by norm_num)
theorem B1863605 : Blo 1240438 1863605 := bbase (se 5 (by rfl) ⟨87356, by rfl⟩ : syracuseStep 1863605 = 174713) (by norm_num)
theorem B1396669 : Blo 1240438 1396669 := bbase (se 3 (by rfl) ⟨261875, by rfl⟩ : syracuseStep 1396669 = 523751) (by norm_num)
theorem B4599749 : Blo 1240438 4599749 := bbase (se 4 (by rfl) ⟨431226, by rfl⟩ : syracuseStep 4599749 = 862453) (by norm_num)
theorem B2355149 : Blo 1240438 2355149 := bbase (se 3 (by rfl) ⟨441590, by rfl⟩ : syracuseStep 2355149 = 883181) (by norm_num)
theorem B1863629 : Blo 1240438 1863629 := bbase (se 3 (by rfl) ⟨349430, by rfl⟩ : syracuseStep 1863629 = 698861) (by norm_num)
theorem B1257437 : Blo 1240438 1257437 := bbase (se 3 (by rfl) ⟨235769, by rfl⟩ : syracuseStep 1257437 = 471539) (by norm_num)
theorem B1396705 : Blo 1240438 1396705 := bbase (se 2 (by rfl) ⟨523764, by rfl⟩ : syracuseStep 1396705 = 1047529) (by norm_num)
theorem B3141605 : Blo 1240438 3141605 := bbase (se 4 (by rfl) ⟨294525, by rfl⟩ : syracuseStep 3141605 = 589051) (by norm_num)
theorem B1863653 : Blo 1240438 1863653 := bbase (se 4 (by rfl) ⟨174717, by rfl⟩ : syracuseStep 1863653 = 349435) (by norm_num)
theorem B3534853 : Blo 1240438 3534853 := bbase (se 4 (by rfl) ⟨331392, by rfl⟩ : syracuseStep 3534853 = 662785) (by norm_num)
theorem B1396741 : Blo 1240438 1396741 := bbase (se 4 (by rfl) ⟨130944, by rfl⟩ : syracuseStep 1396741 = 261889) (by norm_num)
theorem B6287381 : Blo 1240438 6287381 := bbase (se 6 (by rfl) ⟨147360, by rfl⟩ : syracuseStep 6287381 = 294721) (by norm_num)
theorem B1396777 : Blo 1240438 1396777 := bbase (se 2 (by rfl) ⟨523791, by rfl⟩ : syracuseStep 1396777 = 1047583) (by norm_num)
theorem B1396813 : Blo 1240438 1396813 := bbase (se 3 (by rfl) ⟨261902, by rfl⟩ : syracuseStep 1396813 = 523805) (by norm_num)
theorem B2355293 : Blo 1240438 2355293 := bbase (se 3 (by rfl) ⟨441617, by rfl⟩ : syracuseStep 2355293 = 883235) (by norm_num)
theorem B1396849 : Blo 1240438 1396849 := bbase (se 2 (by rfl) ⟨523818, by rfl⟩ : syracuseStep 1396849 = 1047637) (by norm_num)
theorem B5967989 : Blo 1240438 5967989 := bbase (se 5 (by rfl) ⟨279749, by rfl⟩ : syracuseStep 5967989 = 559499) (by norm_num)
theorem B1396885 : Blo 1240438 1396885 := bbase (se 6 (by rfl) ⟨32739, by rfl⟩ : syracuseStep 1396885 = 65479) (by norm_num)
theorem B1396921 : Blo 1240438 1396921 := bbase (se 2 (by rfl) ⟨523845, by rfl⟩ : syracuseStep 1396921 = 1047691) (by norm_num)
theorem B2093269 : Blo 1240438 2093269 := bbase (se 7 (by rfl) ⟨24530, by rfl⟩ : syracuseStep 2093269 = 49061) (by norm_num)
theorem B1396957 : Blo 1240438 1396957 := bbase (se 3 (by rfl) ⟨261929, by rfl⟩ : syracuseStep 1396957 = 523859) (by norm_num)
theorem B1257697 : Blo 1240438 1257697 := bbase (se 2 (by rfl) ⟨471636, by rfl⟩ : syracuseStep 1257697 = 943273) (by norm_num)
theorem B3354853 : Blo 1240438 3354853 := bbase (se 4 (by rfl) ⟨314517, by rfl⟩ : syracuseStep 3354853 = 629035) (by norm_num)
theorem B4190453 : Blo 1240438 4190453 := bbase (se 5 (by rfl) ⟨196427, by rfl⟩ : syracuseStep 4190453 = 392855) (by norm_num)
theorem B1396993 : Blo 1240438 1396993 := bbase (se 2 (by rfl) ⟨523872, by rfl⟩ : syracuseStep 1396993 = 1047745) (by norm_num)
theorem B1397029 : Blo 1240438 1397029 := bbase (se 4 (by rfl) ⟨130971, by rfl⟩ : syracuseStep 1397029 = 261943) (by norm_num)
theorem B2093357 : Blo 1240438 2093357 := bbase (se 3 (by rfl) ⟨392504, by rfl⟩ : syracuseStep 2093357 = 785009) (by norm_num)
theorem B3141949 : Blo 1240438 3141949 := bbase (se 3 (by rfl) ⟨589115, by rfl⟩ : syracuseStep 3141949 = 1178231) (by norm_num)
theorem B1397065 : Blo 1240438 1397065 := bbase (se 2 (by rfl) ⟨523899, by rfl⟩ : syracuseStep 1397065 = 1047799) (by norm_num)
theorem B3584341 : Blo 1240438 3584341 := bbase (se 10 (by rfl) ⟨5250, by rfl⟩ : syracuseStep 3584341 = 10501) (by norm_num)
theorem B2298221 : Blo 1240438 2298221 := bbase (se 3 (by rfl) ⟨430916, by rfl⟩ : syracuseStep 2298221 = 861833) (by norm_num)
theorem B1397101 : Blo 1240438 1397101 := bbase (se 3 (by rfl) ⟨261956, by rfl⟩ : syracuseStep 1397101 = 523913) (by norm_num)
theorem B2355581 : Blo 1240438 2355581 := bbase (se 3 (by rfl) ⟨441671, by rfl⟩ : syracuseStep 2355581 = 883343) (by norm_num)
theorem B1888637 : Blo 1240438 1888637 := bbase (se 3 (by rfl) ⟨354119, by rfl⟩ : syracuseStep 1888637 = 708239) (by norm_num)
theorem B1397137 : Blo 1240438 1397137 := bbase (se 2 (by rfl) ⟨523926, by rfl⟩ : syracuseStep 1397137 = 1047853) (by norm_num)
theorem B2093485 : Blo 1240438 2093485 := bbase (se 3 (by rfl) ⟨392528, by rfl⟩ : syracuseStep 2093485 = 785057) (by norm_num)
theorem B3142061 : Blo 1240438 3142061 := bbase (se 3 (by rfl) ⟨589136, by rfl⟩ : syracuseStep 3142061 = 1178273) (by norm_num)
theorem B1397173 : Blo 1240438 1397173 := bbase (se 5 (by rfl) ⟨65492, by rfl⟩ : syracuseStep 1397173 = 130985) (by norm_num)
theorem B1397209 : Blo 1240438 1397209 := bbase (se 2 (by rfl) ⟨523953, by rfl⟩ : syracuseStep 1397209 = 1047907) (by norm_num)
theorem B1397245 : Blo 1240438 1397245 := bbase (se 3 (by rfl) ⟨261983, by rfl⟩ : syracuseStep 1397245 = 523967) (by norm_num)
theorem B2093573 : Blo 1240438 2093573 := bbase (se 4 (by rfl) ⟨196272, by rfl⟩ : syracuseStep 2093573 = 392545) (by norm_num)
theorem B2650637 : Blo 1240438 2650637 := bbase (se 3 (by rfl) ⟨496994, by rfl⟩ : syracuseStep 2650637 = 993989) (by norm_num)
theorem B2355733 : Blo 1240438 2355733 := bbase (se 6 (by rfl) ⟨55212, by rfl⟩ : syracuseStep 2355733 = 110425) (by norm_num)
theorem B1397281 : Blo 1240438 1397281 := bbase (se 2 (by rfl) ⟨523980, by rfl⟩ : syracuseStep 1397281 = 1047961) (by norm_num)
theorem B1397317 : Blo 1240438 1397317 := bbase (se 4 (by rfl) ⟨130998, by rfl⟩ : syracuseStep 1397317 = 261997) (by norm_num)
theorem B1397353 : Blo 1240438 1397353 := bbase (se 2 (by rfl) ⟨524007, by rfl⟩ : syracuseStep 1397353 = 1048015) (by norm_num)
theorem B3142253 : Blo 1240438 3142253 := bbase (se 3 (by rfl) ⟨589172, by rfl⟩ : syracuseStep 3142253 = 1178345) (by norm_num)
theorem B2093701 : Blo 1240438 2093701 := bbase (se 4 (by rfl) ⟨196284, by rfl⟩ : syracuseStep 2093701 = 392569) (by norm_num)
theorem B1397389 : Blo 1240438 1397389 := bbase (se 3 (by rfl) ⟨262010, by rfl⟩ : syracuseStep 1397389 = 524021) (by norm_num)
theorem B2650781 : Blo 1240438 2650781 := bbase (se 3 (by rfl) ⟨497021, by rfl⟩ : syracuseStep 2650781 = 994043) (by norm_num)
theorem B4190885 : Blo 1240438 4190885 := bbase (se 4 (by rfl) ⟨392895, by rfl⟩ : syracuseStep 4190885 = 785791) (by norm_num)
theorem B4248229 : Blo 1240438 4248229 := bbase (se 4 (by rfl) ⟨398271, by rfl⟩ : syracuseStep 4248229 = 796543) (by norm_num)
theorem B1397425 : Blo 1240438 1397425 := bbase (se 2 (by rfl) ⟨524034, by rfl⟩ : syracuseStep 1397425 = 1048069) (by norm_num)
theorem B1397461 : Blo 1240438 1397461 := bbase (se 7 (by rfl) ⟨16376, by rfl⟩ : syracuseStep 1397461 = 32753) (by norm_num)
theorem B2093789 : Blo 1240438 2093789 := bbase (se 3 (by rfl) ⟨392585, by rfl⟩ : syracuseStep 2093789 = 785171) (by norm_num)
theorem B7549685 : Blo 1240438 7549685 := bbase (se 5 (by rfl) ⟨353891, by rfl⟩ : syracuseStep 7549685 = 707783) (by norm_num)
theorem B1397497 : Blo 1240438 1397497 := bbase (se 2 (by rfl) ⟨524061, by rfl⟩ : syracuseStep 1397497 = 1048123) (by norm_num)
theorem B1397533 : Blo 1240438 1397533 := bbase (se 3 (by rfl) ⟨262037, by rfl⟩ : syracuseStep 1397533 = 524075) (by norm_num)
theorem B1397569 : Blo 1240438 1397569 := bbase (se 2 (by rfl) ⟨524088, by rfl⟩ : syracuseStep 1397569 = 1048177) (by norm_num)
theorem B2356037 : Blo 1240438 2356037 := bbase (se 4 (by rfl) ⟨220878, by rfl⟩ : syracuseStep 2356037 = 441757) (by norm_num)
theorem B67982165 : Blo 1240438 67982165 := bbase (se 9 (by rfl) ⟨199166, by rfl⟩ : syracuseStep 67982165 = 398333) (by norm_num)
theorem B5665621 : Blo 1240438 5665621 := bbase (se 9 (by rfl) ⟨16598, by rfl⟩ : syracuseStep 5665621 = 33197) (by norm_num)
theorem B2093917 : Blo 1240438 2093917 := bbase (se 3 (by rfl) ⟨392609, by rfl⟩ : syracuseStep 2093917 = 785219) (by norm_num)
theorem B1397605 : Blo 1240438 1397605 := bbase (se 4 (by rfl) ⟨131025, by rfl⟩ : syracuseStep 1397605 = 262051) (by norm_num)
theorem B1397641 : Blo 1240438 1397641 := bbase (se 2 (by rfl) ⟨524115, by rfl⟩ : syracuseStep 1397641 = 1048231) (by norm_num)
theorem B1397677 : Blo 1240438 1397677 := bbase (se 3 (by rfl) ⟨262064, by rfl⟩ : syracuseStep 1397677 = 524129) (by norm_num)
theorem B2094005 : Blo 1240438 2094005 := bbase (se 5 (by rfl) ⟨98156, by rfl⟩ : syracuseStep 2094005 = 196313) (by norm_num)
theorem B1766333 : Blo 1240438 1766333 := bbase (se 3 (by rfl) ⟨331187, by rfl⟩ : syracuseStep 1766333 = 662375) (by norm_num)
theorem B3142597 : Blo 1240438 3142597 := bbase (se 4 (by rfl) ⟨294618, by rfl⟩ : syracuseStep 3142597 = 589237) (by norm_num)
theorem B1397713 : Blo 1240438 1397713 := bbase (se 2 (by rfl) ⟨524142, by rfl⟩ : syracuseStep 1397713 = 1048285) (by norm_num)
theorem B2094133 : Blo 1240438 2094133 := bbase (se 5 (by rfl) ⟨98162, by rfl⟩ : syracuseStep 2094133 = 196325) (by norm_num)
theorem B3142709 : Blo 1240438 3142709 := bbase (se 5 (by rfl) ⟨147314, by rfl⟩ : syracuseStep 3142709 = 294629) (by norm_num)
theorem B6370373 : Blo 1240438 6370373 := bbase (se 4 (by rfl) ⟨597222, by rfl⟩ : syracuseStep 6370373 = 1194445) (by norm_num)
theorem B1258573 : Blo 1240438 1258573 := bbase (se 3 (by rfl) ⟨235982, by rfl⟩ : syracuseStep 1258573 = 471965) (by norm_num)
theorem B10605653 : Blo 1240438 10605653 := bbase (se 8 (by rfl) ⟨62142, by rfl⟩ : syracuseStep 10605653 = 124285) (by norm_num)
theorem B4191317 : Blo 1240438 4191317 := bbase (se 8 (by rfl) ⟨24558, by rfl⟩ : syracuseStep 4191317 = 49117) (by norm_num)
theorem B15914069 : Blo 1240438 15914069 := bbase (se 8 (by rfl) ⟨93246, by rfl⟩ : syracuseStep 15914069 = 186493) (by norm_num)
theorem B1258589 : Blo 1240438 1258589 := bbase (se 3 (by rfl) ⟨235985, by rfl⟩ : syracuseStep 1258589 = 471971) (by norm_num)
theorem B2094221 : Blo 1240438 2094221 := bbase (se 3 (by rfl) ⟨392666, by rfl⟩ : syracuseStep 2094221 = 785333) (by norm_num)
theorem B1569937 : Blo 1240438 1569937 := bbase (se 2 (by rfl) ⟨588726, by rfl⟩ : syracuseStep 1569937 = 1177453) (by norm_num)
theorem B1938637 : Blo 1240438 1938637 := bbase (se 3 (by rfl) ⟨363494, by rfl⟩ : syracuseStep 1938637 = 726989) (by norm_num)
theorem B2389229 : Blo 1240438 2389229 := bbase (se 3 (by rfl) ⟨447980, by rfl⟩ : syracuseStep 2389229 = 895961) (by norm_num)
theorem B1570033 : Blo 1240438 1570033 := bbase (se 2 (by rfl) ⟨588762, by rfl⟩ : syracuseStep 1570033 = 1177525) (by norm_num)
theorem B6706421 : Blo 1240438 6706421 := bbase (se 5 (by rfl) ⟨314363, by rfl⟩ : syracuseStep 6706421 = 628727) (by norm_num)
theorem B3142901 : Blo 1240438 3142901 := bbase (se 5 (by rfl) ⟨147323, by rfl⟩ : syracuseStep 3142901 = 294647) (by norm_num)
theorem B4715765 : Blo 1240438 4715765 := bbase (se 5 (by rfl) ⟨221051, by rfl⟩ : syracuseStep 4715765 = 442103) (by norm_num)
theorem B2094349 : Blo 1240438 2094349 := bbase (se 3 (by rfl) ⟨392690, by rfl⟩ : syracuseStep 2094349 = 785381) (by norm_num)
theorem B2553101 : Blo 1240438 2553101 := bbase (se 3 (by rfl) ⟨478706, by rfl⟩ : syracuseStep 2553101 = 957413) (by norm_num)
theorem B6288677 : Blo 1240438 6288677 := bbase (se 4 (by rfl) ⟨589563, by rfl⟩ : syracuseStep 6288677 = 1179127) (by norm_num)
theorem B2094437 : Blo 1240438 2094437 := bbase (se 4 (by rfl) ⟨196353, by rfl⟩ : syracuseStep 2094437 = 392707) (by norm_num)
theorem B2651525 : Blo 1240438 2651525 := bbase (se 4 (by rfl) ⟨248580, by rfl⟩ : syracuseStep 2651525 = 497161) (by norm_num)
theorem B1570205 : Blo 1240438 1570205 := bbase (se 3 (by rfl) ⟨294413, by rfl⟩ : syracuseStep 1570205 = 588827) (by norm_num)
theorem B2487709 : Blo 1240438 2487709 := bbase (se 3 (by rfl) ⟨466445, by rfl⟩ : syracuseStep 2487709 = 932891) (by norm_num)
theorem B1570261 : Blo 1240438 1570261 := bbase (se 7 (by rfl) ⟨18401, by rfl⟩ : syracuseStep 1570261 = 36803) (by norm_num)
theorem B2094565 : Blo 1240438 2094565 := bbase (se 4 (by rfl) ⟨196365, by rfl⟩ : syracuseStep 2094565 = 392731) (by norm_num)
theorem B11924981 : Blo 1240438 11924981 := bbase (se 5 (by rfl) ⟨558983, by rfl⟩ : syracuseStep 11924981 = 1117967) (by norm_num)
theorem B4191749 : Blo 1240438 4191749 := bbase (se 4 (by rfl) ⟨392976, by rfl⟩ : syracuseStep 4191749 = 785953) (by norm_num)
theorem B4716053 : Blo 1240438 4716053 := bbase (se 6 (by rfl) ⟨110532, by rfl⟩ : syracuseStep 4716053 = 221065) (by norm_num)
theorem B1570357 : Blo 1240438 1570357 := bbase (se 5 (by rfl) ⟨73610, by rfl⟩ : syracuseStep 1570357 = 147221) (by norm_num)
theorem B2356789 : Blo 1240438 2356789 := bbase (se 5 (by rfl) ⟨110474, by rfl⟩ : syracuseStep 2356789 = 220949) (by norm_num)
theorem B2094653 : Blo 1240438 2094653 := bbase (se 3 (by rfl) ⟨392747, by rfl⟩ : syracuseStep 2094653 = 785495) (by norm_num)
theorem B2790989 : Blo 1240438 2790989 := bbase (se 3 (by rfl) ⟨523310, by rfl⟩ : syracuseStep 2790989 = 1046621) (by norm_num)
theorem B3143245 : Blo 1240438 3143245 := bbase (se 3 (by rfl) ⟨589358, by rfl⟩ : syracuseStep 3143245 = 1178717) (by norm_num)
theorem B1324669 : Blo 1240438 1324669 := bbase (se 3 (by rfl) ⟨248375, by rfl⟩ : syracuseStep 1324669 = 496751) (by norm_num)
theorem B2791061 : Blo 1240438 2791061 := bbase (se 6 (by rfl) ⟨65415, by rfl⟩ : syracuseStep 2791061 = 130831) (by norm_num)
theorem B10753685 : Blo 1240438 10753685 := bbase (se 6 (by rfl) ⟨252039, by rfl⟩ : syracuseStep 10753685 = 504079) (by norm_num)
theorem B1259173 : Blo 1240438 1259173 := bbase (se 4 (by rfl) ⟨118047, by rfl⟩ : syracuseStep 1259173 = 236095) (by norm_num)
theorem B2094781 : Blo 1240438 2094781 := bbase (se 3 (by rfl) ⟨392771, by rfl⟩ : syracuseStep 2094781 = 785543) (by norm_num)
theorem B3143357 : Blo 1240438 3143357 := bbase (se 3 (by rfl) ⟨589379, by rfl⟩ : syracuseStep 3143357 = 1178759) (by norm_num)
theorem B5961413 : Blo 1240438 5961413 := bbase (se 4 (by rfl) ⟨558882, by rfl⟩ : syracuseStep 5961413 = 1117765) (by norm_num)
theorem B6280901 : Blo 1240438 6280901 := bbase (se 4 (by rfl) ⟨588834, by rfl⟩ : syracuseStep 6280901 = 1177669) (by norm_num)
theorem B2356933 : Blo 1240438 2356933 := bbase (se 4 (by rfl) ⟨220962, by rfl⟩ : syracuseStep 2356933 = 441925) (by norm_num)
theorem B2791133 : Blo 1240438 2791133 := bbase (se 3 (by rfl) ⟨523337, by rfl⟩ : syracuseStep 2791133 = 1046675) (by norm_num)
theorem B1988317 : Blo 1240438 1988317 := bbase (se 3 (by rfl) ⟨372809, by rfl⟩ : syracuseStep 1988317 = 745619) (by norm_num)
theorem B1570529 : Blo 1240438 1570529 := bbase (se 2 (by rfl) ⟨588948, by rfl⟩ : syracuseStep 1570529 = 1177897) (by norm_num)
theorem B2094869 : Blo 1240438 2094869 := bbase (se 6 (by rfl) ⟨49098, by rfl⟩ : syracuseStep 2094869 = 98197) (by norm_num)
theorem B1570585 : Blo 1240438 1570585 := bbase (se 2 (by rfl) ⟨588969, by rfl⟩ : syracuseStep 1570585 = 1177939) (by norm_num)
theorem B2791205 : Blo 1240438 2791205 := bbase (se 4 (by rfl) ⟨261675, by rfl⟩ : syracuseStep 2791205 = 523351) (by norm_num)
theorem B2357093 : Blo 1240438 2357093 := bbase (se 4 (by rfl) ⟨220977, by rfl⟩ : syracuseStep 2357093 = 441955) (by norm_num)
theorem B1914725 : Blo 1240438 1914725 := bbase (se 4 (by rfl) ⟨179505, by rfl⟩ : syracuseStep 1914725 = 359011) (by norm_num)
theorem B2791277 : Blo 1240438 2791277 := bbase (se 3 (by rfl) ⟨523364, by rfl⟩ : syracuseStep 2791277 = 1046729) (by norm_num)
theorem B1570681 : Blo 1240438 1570681 := bbase (se 2 (by rfl) ⟨589005, by rfl⟩ : syracuseStep 1570681 = 1178011) (by norm_num)
theorem B3143549 : Blo 1240438 3143549 := bbase (se 3 (by rfl) ⟨589415, by rfl⟩ : syracuseStep 3143549 = 1178831) (by norm_num)
theorem B2094997 : Blo 1240438 2094997 := bbase (se 6 (by rfl) ⟨49101, by rfl⟩ : syracuseStep 2094997 = 98203) (by norm_num)
theorem B2791349 : Blo 1240438 2791349 := bbase (se 5 (by rfl) ⟨130844, by rfl⟩ : syracuseStep 2791349 = 261689) (by norm_num)
theorem B4192181 : Blo 1240438 4192181 := bbase (se 5 (by rfl) ⟨196508, by rfl⟩ : syracuseStep 4192181 = 393017) (by norm_num)
theorem B2095085 : Blo 1240438 2095085 := bbase (se 3 (by rfl) ⟨392828, by rfl⟩ : syracuseStep 2095085 = 785657) (by norm_num)
theorem B1325045 : Blo 1240438 1325045 := bbase (se 5 (by rfl) ⟨62111, by rfl⟩ : syracuseStep 1325045 = 124223) (by norm_num)
theorem B2357237 : Blo 1240438 2357237 := bbase (se 5 (by rfl) ⟨110495, by rfl⟩ : syracuseStep 2357237 = 220991) (by norm_num)
theorem B2791421 : Blo 1240438 2791421 := bbase (se 3 (by rfl) ⟨523391, by rfl⟩ : syracuseStep 2791421 = 1046783) (by norm_num)
theorem B1570853 : Blo 1240438 1570853 := bbase (se 4 (by rfl) ⟨147267, by rfl⟩ : syracuseStep 1570853 = 294535) (by norm_num)
theorem B1325117 : Blo 1240438 1325117 := bbase (se 3 (by rfl) ⟨248459, by rfl⟩ : syracuseStep 1325117 = 496919) (by norm_num)
theorem B2791493 : Blo 1240438 2791493 := bbase (se 4 (by rfl) ⟨261702, by rfl⟩ : syracuseStep 2791493 = 523405) (by norm_num)
theorem B6707285 : Blo 1240438 6707285 := bbase (se 8 (by rfl) ⟨39300, by rfl⟩ : syracuseStep 6707285 = 78601) (by norm_num)
theorem B1570909 : Blo 1240438 1570909 := bbase (se 3 (by rfl) ⟨294545, by rfl⟩ : syracuseStep 1570909 = 589091) (by norm_num)
theorem B3446885 : Blo 1240438 3446885 := bbase (se 4 (by rfl) ⟨323145, by rfl⟩ : syracuseStep 3446885 = 646291) (by norm_num)
theorem B2095213 : Blo 1240438 2095213 := bbase (se 3 (by rfl) ⟨392852, by rfl⟩ : syracuseStep 2095213 = 785705) (by norm_num)
theorem B2652277 : Blo 1240438 2652277 := bbase (se 5 (by rfl) ⟨124325, by rfl⟩ : syracuseStep 2652277 = 248651) (by norm_num)
theorem B2791565 : Blo 1240438 2791565 := bbase (se 3 (by rfl) ⟨523418, by rfl⟩ : syracuseStep 2791565 = 1046837) (by norm_num)
theorem B10074293 : Blo 1240438 10074293 := bbase (se 5 (by rfl) ⟨472232, by rfl⟩ : syracuseStep 10074293 = 944465) (by norm_num)
theorem B1571005 : Blo 1240438 1571005 := bbase (se 3 (by rfl) ⟨294563, by rfl⟩ : syracuseStep 1571005 = 589127) (by norm_num)
theorem B2095301 : Blo 1240438 2095301 := bbase (se 4 (by rfl) ⟨196434, by rfl⟩ : syracuseStep 2095301 = 392869) (by norm_num)
theorem B2791637 : Blo 1240438 2791637 := bbase (se 7 (by rfl) ⟨32714, by rfl⟩ : syracuseStep 2791637 = 65429) (by norm_num)
theorem B3143893 : Blo 1240438 3143893 := bbase (se 7 (by rfl) ⟨36842, by rfl⟩ : syracuseStep 3143893 = 73685) (by norm_num)
theorem B1325305 : Blo 1240438 1325305 := bbase (se 2 (by rfl) ⟨496989, by rfl⟩ : syracuseStep 1325305 = 993979) (by norm_num)
theorem B2652421 : Blo 1240438 2652421 := bbase (se 4 (by rfl) ⟨248664, by rfl⟩ : syracuseStep 2652421 = 497329) (by norm_num)
theorem B2357525 : Blo 1240438 2357525 := bbase (se 6 (by rfl) ⟨55254, by rfl⟩ : syracuseStep 2357525 = 110509) (by norm_num)
theorem B2791709 : Blo 1240438 2791709 := bbase (se 3 (by rfl) ⟨523445, by rfl⟩ : syracuseStep 2791709 = 1046891) (by norm_num)
theorem B2095429 : Blo 1240438 2095429 := bbase (se 4 (by rfl) ⟨196446, by rfl⟩ : syracuseStep 2095429 = 392893) (by norm_num)
theorem B3144005 : Blo 1240438 3144005 := bbase (se 4 (by rfl) ⟨294750, by rfl⟩ : syracuseStep 3144005 = 589501) (by norm_num)
theorem B1767757 : Blo 1240438 1767757 := bbase (se 3 (by rfl) ⟨331454, by rfl⟩ : syracuseStep 1767757 = 662909) (by norm_num)
theorem B2791781 : Blo 1240438 2791781 := bbase (se 4 (by rfl) ⟨261729, by rfl⟩ : syracuseStep 2791781 = 523459) (by norm_num)
theorem B4192613 : Blo 1240438 4192613 := bbase (se 4 (by rfl) ⟨393057, by rfl⟩ : syracuseStep 4192613 = 786115) (by norm_num)
theorem B1571177 : Blo 1240438 1571177 := bbase (se 2 (by rfl) ⟨589191, by rfl⟩ : syracuseStep 1571177 = 1178383) (by norm_num)
theorem B5306741 : Blo 1240438 5306741 := bbase (se 5 (by rfl) ⟨248753, by rfl⟩ : syracuseStep 5306741 = 497507) (by norm_num)
theorem B2095517 : Blo 1240438 2095517 := bbase (se 3 (by rfl) ⟨392909, by rfl⟩ : syracuseStep 2095517 = 785819) (by norm_num)
theorem B1571233 : Blo 1240438 1571233 := bbase (se 2 (by rfl) ⟨589212, by rfl⟩ : syracuseStep 1571233 = 1178425) (by norm_num)
theorem B2791853 : Blo 1240438 2791853 := bbase (se 3 (by rfl) ⟨523472, by rfl⟩ : syracuseStep 2791853 = 1046945) (by norm_num)
theorem B2357677 : Blo 1240438 2357677 := bbase (se 3 (by rfl) ⟨442064, by rfl⟩ : syracuseStep 2357677 = 884129) (by norm_num)
theorem B1325489 : Blo 1240438 1325489 := bbase (se 2 (by rfl) ⟨497058, by rfl⟩ : syracuseStep 1325489 = 994117) (by norm_num)
theorem B1677773 : Blo 1240438 1677773 := bbase (se 3 (by rfl) ⟨314582, by rfl⟩ : syracuseStep 1677773 = 629165) (by norm_num)
theorem B2791925 : Blo 1240438 2791925 := bbase (se 5 (by rfl) ⟨130871, by rfl⟩ : syracuseStep 2791925 = 261743) (by norm_num)
theorem B1571329 : Blo 1240438 1571329 := bbase (se 2 (by rfl) ⟨589248, by rfl⟩ : syracuseStep 1571329 = 1178497) (by norm_num)
theorem B3144197 : Blo 1240438 3144197 := bbase (se 4 (by rfl) ⟨294768, by rfl⟩ : syracuseStep 3144197 = 589537) (by norm_num)
theorem B2095645 : Blo 1240438 2095645 := bbase (se 3 (by rfl) ⟨392933, by rfl⟩ : syracuseStep 2095645 = 785867) (by norm_num)
theorem B2791997 : Blo 1240438 2791997 := bbase (se 3 (by rfl) ⟨523499, by rfl⟩ : syracuseStep 2791997 = 1046999) (by norm_num)
theorem B1415785 : Blo 1240438 1415785 := bbase (se 2 (by rfl) ⟨530919, by rfl⟩ : syracuseStep 1415785 = 1061839) (by norm_num)
theorem B2095733 : Blo 1240438 2095733 := bbase (se 5 (by rfl) ⟨98237, by rfl⟩ : syracuseStep 2095733 = 196475) (by norm_num)
theorem B2652797 : Blo 1240438 2652797 := bbase (se 3 (by rfl) ⟨497399, by rfl⟩ : syracuseStep 2652797 = 994799) (by norm_num)
theorem B2792069 : Blo 1240438 2792069 := bbase (se 4 (by rfl) ⟨261756, by rfl⟩ : syracuseStep 2792069 = 523513) (by norm_num)
theorem B3357317 : Blo 1240438 3357317 := bbase (se 4 (by rfl) ⟨314748, by rfl⟩ : syracuseStep 3357317 = 629497) (by norm_num)
theorem B5307029 : Blo 1240438 5307029 := bbase (se 6 (by rfl) ⟨124383, by rfl⟩ : syracuseStep 5307029 = 248767) (by norm_num)
theorem B1571501 : Blo 1240438 1571501 := bbase (se 3 (by rfl) ⟨294656, by rfl⟩ : syracuseStep 1571501 = 589313) (by norm_num)
theorem B4717237 : Blo 1240438 4717237 := bbase (se 5 (by rfl) ⟨221120, by rfl⟩ : syracuseStep 4717237 = 442241) (by norm_num)
theorem B2792141 : Blo 1240438 2792141 := bbase (se 3 (by rfl) ⟨523526, by rfl⟩ : syracuseStep 2792141 = 1047053) (by norm_num)
theorem B2357981 : Blo 1240438 2357981 := bbase (se 3 (by rfl) ⟨442121, by rfl⟩ : syracuseStep 2357981 = 884243) (by norm_num)
theorem B1571557 : Blo 1240438 1571557 := bbase (se 4 (by rfl) ⟨147333, by rfl⟩ : syracuseStep 1571557 = 294667) (by norm_num)
theorem B2095861 : Blo 1240438 2095861 := bbase (se 5 (by rfl) ⟨98243, by rfl⟩ : syracuseStep 2095861 = 196487) (by norm_num)
theorem B5298965 : Blo 1240438 5298965 := bbase (se 6 (by rfl) ⟨124194, by rfl⟩ : syracuseStep 5298965 = 248389) (by norm_num)
theorem B2792213 : Blo 1240438 2792213 := bbase (se 6 (by rfl) ⟨65442, by rfl⟩ : syracuseStep 2792213 = 130885) (by norm_num)
theorem B4193045 : Blo 1240438 4193045 := bbase (se 6 (by rfl) ⟨98274, by rfl⟩ : syracuseStep 4193045 = 196549) (by norm_num)
theorem B3537701 : Blo 1240438 3537701 := bbase (se 4 (by rfl) ⟨331659, by rfl⟩ : syracuseStep 3537701 = 663319) (by norm_num)
theorem B1571653 : Blo 1240438 1571653 := bbase (se 4 (by rfl) ⟨147342, by rfl⟩ : syracuseStep 1571653 = 294685) (by norm_num)
theorem B2685773 : Blo 1240438 2685773 := bbase (se 3 (by rfl) ⟨503582, by rfl⟩ : syracuseStep 2685773 = 1007165) (by norm_num)
theorem B2095949 : Blo 1240438 2095949 := bbase (se 3 (by rfl) ⟨392990, by rfl⟩ : syracuseStep 2095949 = 785981) (by norm_num)
theorem B2792285 : Blo 1240438 2792285 := bbase (se 3 (by rfl) ⟨523553, by rfl⟩ : syracuseStep 2792285 = 1047107) (by norm_num)
theorem B3144541 : Blo 1240438 3144541 := bbase (se 3 (by rfl) ⟨589601, by rfl⟩ : syracuseStep 3144541 = 1179203) (by norm_num)
theorem B1678205 : Blo 1240438 1678205 := bbase (se 3 (by rfl) ⟨314663, by rfl⟩ : syracuseStep 1678205 = 629327) (by norm_num)
theorem B1768349 : Blo 1240438 1768349 := bbase (se 3 (by rfl) ⟨331565, by rfl⟩ : syracuseStep 1768349 = 663131) (by norm_num)
theorem B2792357 : Blo 1240438 2792357 := bbase (se 4 (by rfl) ⟨261783, by rfl⟩ : syracuseStep 2792357 = 523567) (by norm_num)
theorem B7650229 : Blo 1240438 7650229 := bbase (se 5 (by rfl) ⟨358604, by rfl⟩ : syracuseStep 7650229 = 717209) (by norm_num)
theorem B2980813 : Blo 1240438 2980813 := bbase (se 3 (by rfl) ⟨558902, by rfl⟩ : syracuseStep 2980813 = 1117805) (by norm_num)
theorem B2096077 : Blo 1240438 2096077 := bbase (se 3 (by rfl) ⟨393014, by rfl⟩ : syracuseStep 2096077 = 786029) (by norm_num)
theorem B3144653 : Blo 1240438 3144653 := bbase (se 3 (by rfl) ⟨589622, by rfl⟩ : syracuseStep 3144653 = 1179245) (by norm_num)
theorem B6282197 : Blo 1240438 6282197 := bbase (se 7 (by rfl) ⟨73619, by rfl⟩ : syracuseStep 6282197 = 147239) (by norm_num)
theorem B2792429 : Blo 1240438 2792429 := bbase (se 3 (by rfl) ⟨523580, by rfl⟩ : syracuseStep 2792429 = 1047161) (by norm_num)
theorem B1768429 : Blo 1240438 1768429 := bbase (se 3 (by rfl) ⟨331580, by rfl⟩ : syracuseStep 1768429 = 663161) (by norm_num)
theorem B2653165 : Blo 1240438 2653165 := bbase (se 3 (by rfl) ⟨497468, by rfl⟩ : syracuseStep 2653165 = 994937) (by norm_num)
theorem B1571825 : Blo 1240438 1571825 := bbase (se 2 (by rfl) ⟨589434, by rfl⟩ : syracuseStep 1571825 = 1178869) (by norm_num)
theorem B2096165 : Blo 1240438 2096165 := bbase (se 4 (by rfl) ⟨196515, by rfl⟩ : syracuseStep 2096165 = 393031) (by norm_num)
theorem B1571881 : Blo 1240438 1571881 := bbase (se 2 (by rfl) ⟨589455, by rfl⟩ : syracuseStep 1571881 = 1178911) (by norm_num)
theorem B2792501 : Blo 1240438 2792501 := bbase (se 5 (by rfl) ⟨130898, by rfl⟩ : syracuseStep 2792501 = 261797) (by norm_num)
theorem B1989701 : Blo 1240438 1989701 := bbase (se 4 (by rfl) ⟨186534, by rfl⟩ : syracuseStep 1989701 = 373069) (by norm_num)
theorem B1768549 : Blo 1240438 1768549 := bbase (se 4 (by rfl) ⟨165801, by rfl⟩ : syracuseStep 1768549 = 331603) (by norm_num)
theorem B2792573 : Blo 1240438 2792573 := bbase (se 3 (by rfl) ⟨523607, by rfl⟩ : syracuseStep 2792573 = 1047215) (by norm_num)
theorem B1571977 : Blo 1240438 1571977 := bbase (se 2 (by rfl) ⟨589491, by rfl⟩ : syracuseStep 1571977 = 1178983) (by norm_num)
theorem B3144845 : Blo 1240438 3144845 := bbase (se 3 (by rfl) ⟨589658, by rfl⟩ : syracuseStep 3144845 = 1179317) (by norm_num)
theorem B1326241 : Blo 1240438 1326241 := bbase (se 2 (by rfl) ⟨497340, by rfl⟩ : syracuseStep 1326241 = 994681) (by norm_num)
theorem B2096293 : Blo 1240438 2096293 := bbase (se 4 (by rfl) ⟨196527, by rfl⟩ : syracuseStep 2096293 = 393055) (by norm_num)
theorem B2792645 : Blo 1240438 2792645 := bbase (se 4 (by rfl) ⟨261810, by rfl⟩ : syracuseStep 2792645 = 523621) (by norm_num)
theorem B1768645 : Blo 1240438 1768645 := bbase (se 4 (by rfl) ⟨165810, by rfl⟩ : syracuseStep 1768645 = 331621) (by norm_num)
theorem B1326313 : Blo 1240438 1326313 := bbase (se 2 (by rfl) ⟨497367, by rfl⟩ : syracuseStep 1326313 = 994735) (by norm_num)
theorem B2268397 : Blo 1240438 2268397 := bbase (se 3 (by rfl) ⟨425324, by rfl⟩ : syracuseStep 2268397 = 850649) (by norm_num)
theorem B2096381 : Blo 1240438 2096381 := bbase (se 3 (by rfl) ⟨393071, by rfl⟩ : syracuseStep 2096381 = 786143) (by norm_num)
theorem B1989893 : Blo 1240438 1989893 := bbase (se 4 (by rfl) ⟨186552, by rfl⟩ : syracuseStep 1989893 = 373105) (by norm_num)
theorem B2792717 : Blo 1240438 2792717 := bbase (se 3 (by rfl) ⟨523634, by rfl⟩ : syracuseStep 2792717 = 1047269) (by norm_num)
theorem B1572149 : Blo 1240438 1572149 := bbase (se 5 (by rfl) ⟨73694, by rfl⟩ : syracuseStep 1572149 = 147389) (by norm_num)
theorem B1490257 : Blo 1240438 1490257 := bbase (se 2 (by rfl) ⟨558846, by rfl⟩ : syracuseStep 1490257 = 1117693) (by norm_num)
theorem B2792789 : Blo 1240438 2792789 := bbase (se 11 (by rfl) ⟨2045, by rfl⟩ : syracuseStep 2792789 = 4091) (by norm_num)
theorem B1572205 : Blo 1240438 1572205 := bbase (se 3 (by rfl) ⟨294788, by rfl⟩ : syracuseStep 1572205 = 589577) (by norm_num)
theorem B2096509 : Blo 1240438 2096509 := bbase (se 3 (by rfl) ⟨393095, by rfl⟩ : syracuseStep 2096509 = 786191) (by norm_num)
theorem B2792861 : Blo 1240438 2792861 := bbase (se 3 (by rfl) ⟨523661, by rfl⟩ : syracuseStep 2792861 = 1047323) (by norm_num)
theorem B1326493 : Blo 1240438 1326493 := bbase (se 3 (by rfl) ⟨248717, by rfl⟩ : syracuseStep 1326493 = 497435) (by norm_num)
theorem B1572301 : Blo 1240438 1572301 := bbase (se 3 (by rfl) ⟨294806, by rfl⟩ : syracuseStep 1572301 = 589613) (by norm_num)
theorem B2096597 : Blo 1240438 2096597 := bbase (se 7 (by rfl) ⟨24569, by rfl⟩ : syracuseStep 2096597 = 49139) (by norm_num)
theorem B2792933 : Blo 1240438 2792933 := bbase (se 4 (by rfl) ⟨261837, by rfl⟩ : syracuseStep 2792933 = 523675) (by norm_num)
theorem B2793005 : Blo 1240438 2793005 := bbase (se 3 (by rfl) ⟨523688, by rfl⟩ : syracuseStep 2793005 = 1047377) (by norm_num)
theorem B2793077 : Blo 1240438 2793077 := bbase (se 5 (by rfl) ⟨130925, by rfl⟩ : syracuseStep 2793077 = 261851) (by norm_num)
theorem B7954037 : Blo 1240438 7954037 := bbase (se 5 (by rfl) ⟨372845, by rfl⟩ : syracuseStep 7954037 = 745691) (by norm_num)
theorem B1679005 : Blo 1240438 1679005 := bbase (se 3 (by rfl) ⟨314813, by rfl⟩ : syracuseStep 1679005 = 629627) (by norm_num)
theorem B2793149 : Blo 1240438 2793149 := bbase (se 3 (by rfl) ⟨523715, by rfl⟩ : syracuseStep 2793149 = 1047431) (by norm_num)
theorem B2793221 : Blo 1240438 2793221 := bbase (se 4 (by rfl) ⟨261864, by rfl⟩ : syracuseStep 2793221 = 523729) (by norm_num)
theorem B6045461 : Blo 1240438 6045461 := bbase (se 6 (by rfl) ⟨141690, by rfl⟩ : syracuseStep 6045461 = 283381) (by norm_num)
theorem B2793293 : Blo 1240438 2793293 := bbase (se 3 (by rfl) ⟨523742, by rfl⟩ : syracuseStep 2793293 = 1047485) (by norm_num)
theorem B2981765 : Blo 1240438 2981765 := bbase (se 4 (by rfl) ⟨279540, by rfl⟩ : syracuseStep 2981765 = 559081) (by norm_num)
theorem B2793365 : Blo 1240438 2793365 := bbase (se 6 (by rfl) ⟨65469, by rfl⟩ : syracuseStep 2793365 = 130939) (by norm_num)
theorem B9428885 : Blo 1240438 9428885 := bbase (se 6 (by rfl) ⟨220989, by rfl⟩ : syracuseStep 9428885 = 441979) (by norm_num)
theorem B2981821 : Blo 1240438 2981821 := bbase (se 3 (by rfl) ⟨559091, by rfl⟩ : syracuseStep 2981821 = 1118183) (by norm_num)
theorem B16981973 : Blo 1240438 16981973 := bbase (se 7 (by rfl) ⟨199007, by rfl⟩ : syracuseStep 16981973 = 398015) (by norm_num)
theorem B2793437 : Blo 1240438 2793437 := bbase (se 3 (by rfl) ⟨523769, by rfl⟩ : syracuseStep 2793437 = 1047539) (by norm_num)
theorem B2793617 : Blo 1240438 2793617 := bstep (se 2 (by rfl) ⟨1047606, by rfl⟩ : syracuseStep 2793617 = 2095213) B2095213
theorem B2793635 : Blo 1240438 2793635 := bstep (se 1 (by rfl) ⟨2095226, by rfl⟩ : syracuseStep 2793635 = 4190453) B4190453
theorem B1532147 : Blo 1240438 1532147 := bstep (se 1 (by rfl) ⟨1149110, by rfl⟩ : syracuseStep 1532147 = 2298221) B2298221
theorem B9191693 : Blo 1240438 9191693 := bstep (se 3 (by rfl) ⟨1723442, by rfl⟩ : syracuseStep 9191693 = 3446885) B3446885
theorem B4473137 : Blo 1240438 4473137 := bstep (se 2 (by rfl) ⟨1677426, by rfl⟩ : syracuseStep 4473137 = 3354853) B3354853
theorem B2793905 : Blo 1240438 2793905 := bstep (se 2 (by rfl) ⟨1047714, by rfl⟩ : syracuseStep 2793905 = 2095429) B2095429
theorem B2793923 : Blo 1240438 2793923 := bstep (se 1 (by rfl) ⟨2095442, by rfl⟩ : syracuseStep 2793923 = 4190885) B4190885
theorem B7168517 : Blo 1240438 7168517 := bstep (se 4 (by rfl) ⟨672048, by rfl⟩ : syracuseStep 7168517 = 1344097) B1344097
theorem B4186673 : Blo 1240438 4186673 := bstep (se 2 (by rfl) ⟨1570002, by rfl⟩ : syracuseStep 4186673 = 3140005) B3140005
theorem B6709837 : Blo 1240438 6709837 := bstep (se 3 (by rfl) ⟨1258094, by rfl⟩ : syracuseStep 6709837 = 2516189) B2516189
theorem B2122433 : Blo 1240438 2122433 := bstep (se 2 (by rfl) ⟨795912, by rfl⟩ : syracuseStep 2122433 = 1591825) B1591825
theorem B2794193 : Blo 1240438 2794193 := bstep (se 2 (by rfl) ⟨1047822, by rfl⟩ : syracuseStep 2794193 = 2095645) B2095645
theorem B7070435 : Blo 1240438 7070435 := bstep (se 1 (by rfl) ⟨5302826, by rfl⟩ : syracuseStep 7070435 = 10605653) B10605653
theorem B2794211 : Blo 1240438 2794211 := bstep (se 1 (by rfl) ⟨2095658, by rfl⟩ : syracuseStep 2794211 = 4191317) B4191317
theorem B10609379 : Blo 1240438 10609379 := bstep (se 1 (by rfl) ⟨7957034, by rfl⟩ : syracuseStep 10609379 = 15914069) B15914069
theorem B2122529 : Blo 1240438 2122529 := bstep (se 2 (by rfl) ⟨795948, by rfl⟩ : syracuseStep 2122529 = 1591897) B1591897
theorem B2794481 : Blo 1240438 2794481 := bstep (se 2 (by rfl) ⟨1047930, by rfl⟩ : syracuseStep 2794481 = 2095861) B2095861
theorem B2794499 : Blo 1240438 2794499 := bstep (se 1 (by rfl) ⟨2095874, by rfl⟩ : syracuseStep 2794499 = 4191749) B4191749
theorem B1860659 : Blo 1240438 1860659 := bstep (se 1 (by rfl) ⟨1395494, by rfl⟩ : syracuseStep 1860659 = 2790989) B2790989
theorem B10339397 : Blo 1240438 10339397 := bstep (se 4 (by rfl) ⟨969318, by rfl⟩ : syracuseStep 10339397 = 1938637) B1938637
theorem B4187213 : Blo 1240438 4187213 := bstep (se 3 (by rfl) ⟨785102, by rfl⟩ : syracuseStep 4187213 = 1570205) B1570205
theorem B1860689 : Blo 1240438 1860689 := bstep (se 2 (by rfl) ⟨697758, by rfl⟩ : syracuseStep 1860689 = 1395517) B1395517
theorem B1860707 : Blo 1240438 1860707 := bstep (se 1 (by rfl) ⟨1395530, by rfl⟩ : syracuseStep 1860707 = 2791061) B2791061
theorem B7169123 : Blo 1240438 7169123 := bstep (se 1 (by rfl) ⟨5376842, by rfl⟩ : syracuseStep 7169123 = 10753685) B10753685
theorem B7554161 : Blo 1240438 7554161 := bstep (se 2 (by rfl) ⟨2832810, by rfl⟩ : syracuseStep 7554161 = 5665621) B5665621
theorem B1860737 : Blo 1240438 1860737 := bstep (se 2 (by rfl) ⟨697776, by rfl⟩ : syracuseStep 1860737 = 1395553) B1395553
theorem B3974275 : Blo 1240438 3974275 := bstep (se 1 (by rfl) ⟨2980706, by rfl⟩ : syracuseStep 3974275 = 5961413) B5961413
theorem B4187267 : Blo 1240438 4187267 := bstep (se 1 (by rfl) ⟨3140450, by rfl⟩ : syracuseStep 4187267 = 6280901) B6280901
theorem B1860755 : Blo 1240438 1860755 := bstep (se 1 (by rfl) ⟨1395566, by rfl⟩ : syracuseStep 1860755 = 2791133) B2791133
theorem B1860785 : Blo 1240438 1860785 := bstep (se 2 (by rfl) ⟨697794, by rfl⟩ : syracuseStep 1860785 = 1395589) B1395589
theorem B5301425 : Blo 1240438 5301425 := bstep (se 2 (by rfl) ⟨1988034, by rfl⟩ : syracuseStep 5301425 = 3976069) B3976069
theorem B6284465 : Blo 1240438 6284465 := bstep (se 2 (by rfl) ⟨2356674, by rfl⟩ : syracuseStep 6284465 = 4713349) B4713349
theorem B1860803 : Blo 1240438 1860803 := bstep (se 1 (by rfl) ⟨1395602, by rfl⟩ : syracuseStep 1860803 = 2791205) B2791205
theorem B4474061 : Blo 1240438 4474061 := bstep (se 3 (by rfl) ⟨838886, by rfl⟩ : syracuseStep 4474061 = 1677773) B1677773
theorem B1860833 : Blo 1240438 1860833 := bstep (se 2 (by rfl) ⟨697812, by rfl⟩ : syracuseStep 1860833 = 1395625) B1395625
theorem B10200305 : Blo 1240438 10200305 := bstep (se 2 (by rfl) ⟨3825114, by rfl⟩ : syracuseStep 10200305 = 7650229) B7650229
theorem B1860851 : Blo 1240438 1860851 := bstep (se 1 (by rfl) ⟨1395638, by rfl⟩ : syracuseStep 1860851 = 2791277) B2791277
theorem B1860881 : Blo 1240438 1860881 := bstep (se 2 (by rfl) ⟨697830, by rfl⟩ : syracuseStep 1860881 = 1395661) B1395661
theorem B3974417 : Blo 1240438 3974417 := bstep (se 2 (by rfl) ⟨1490406, by rfl⟩ : syracuseStep 3974417 = 2980813) B2980813
theorem B2794769 : Blo 1240438 2794769 := bstep (se 2 (by rfl) ⟨1048038, by rfl⟩ : syracuseStep 2794769 = 2096077) B2096077
theorem B1860899 : Blo 1240438 1860899 := bstep (se 1 (by rfl) ⟨1395674, by rfl⟩ : syracuseStep 1860899 = 2791349) B2791349
theorem B2794787 : Blo 1240438 2794787 := bstep (se 1 (by rfl) ⟨2096090, by rfl⟩ : syracuseStep 2794787 = 4192181) B4192181
theorem B1860929 : Blo 1240438 1860929 := bstep (se 2 (by rfl) ⟨697848, by rfl⟩ : syracuseStep 1860929 = 1395697) B1395697
theorem B1860947 : Blo 1240438 1860947 := bstep (se 1 (by rfl) ⟨1395710, by rfl⟩ : syracuseStep 1860947 = 2791421) B2791421
theorem B1860977 : Blo 1240438 1860977 := bstep (se 2 (by rfl) ⟨697866, by rfl⟩ : syracuseStep 1860977 = 1395733) B1395733
theorem B1860995 : Blo 1240438 1860995 := bstep (se 1 (by rfl) ⟨1395746, by rfl⟩ : syracuseStep 1860995 = 2791493) B2791493
theorem B4187537 : Blo 1240438 4187537 := bstep (se 2 (by rfl) ⟨1570326, by rfl⟩ : syracuseStep 4187537 = 3140653) B3140653
theorem B1861025 : Blo 1240438 1861025 := bstep (se 2 (by rfl) ⟨697884, by rfl⟩ : syracuseStep 1861025 = 1395769) B1395769
theorem B1861043 : Blo 1240438 1861043 := bstep (se 1 (by rfl) ⟨1395782, by rfl⟩ : syracuseStep 1861043 = 2791565) B2791565
theorem B3630541 : Blo 1240438 3630541 := bstep (se 3 (by rfl) ⟨680726, by rfl⟩ : syracuseStep 3630541 = 1361453) B1361453
theorem B1861073 : Blo 1240438 1861073 := bstep (se 2 (by rfl) ⟨697902, by rfl⟩ : syracuseStep 1861073 = 1395805) B1395805
theorem B1861091 : Blo 1240438 1861091 := bstep (se 1 (by rfl) ⟨1395818, by rfl⟩ : syracuseStep 1861091 = 2791637) B2791637
theorem B1861121 : Blo 1240438 1861121 := bstep (se 2 (by rfl) ⟨697920, by rfl⟩ : syracuseStep 1861121 = 1395841) B1395841
theorem B1861139 : Blo 1240438 1861139 := bstep (se 1 (by rfl) ⟨1395854, by rfl⟩ : syracuseStep 1861139 = 2791709) B2791709
theorem B1861169 : Blo 1240438 1861169 := bstep (se 2 (by rfl) ⟨697938, by rfl⟩ : syracuseStep 1861169 = 1395877) B1395877
theorem B2795057 : Blo 1240438 2795057 := bstep (se 2 (by rfl) ⟨1048146, by rfl⟩ : syracuseStep 2795057 = 2096293) B2096293
theorem B1861187 : Blo 1240438 1861187 := bstep (se 1 (by rfl) ⟨1395890, by rfl⟩ : syracuseStep 1861187 = 2791781) B2791781
theorem B2795075 : Blo 1240438 2795075 := bstep (se 1 (by rfl) ⟨2096306, by rfl⟩ : syracuseStep 2795075 = 4192613) B4192613
theorem B1861217 : Blo 1240438 1861217 := bstep (se 2 (by rfl) ⟨697956, by rfl⟩ : syracuseStep 1861217 = 1395913) B1395913
theorem B1861235 : Blo 1240438 1861235 := bstep (se 1 (by rfl) ⟨1395926, by rfl⟩ : syracuseStep 1861235 = 2791853) B2791853
theorem B1861265 : Blo 1240438 1861265 := bstep (se 2 (by rfl) ⟨697974, by rfl⟩ : syracuseStep 1861265 = 1395949) B1395949
theorem B1861283 : Blo 1240438 1861283 := bstep (se 1 (by rfl) ⟨1395962, by rfl⟩ : syracuseStep 1861283 = 2791925) B2791925
theorem B1861313 : Blo 1240438 1861313 := bstep (se 2 (by rfl) ⟨697992, by rfl⟩ : syracuseStep 1861313 = 1395985) B1395985
theorem B1861331 : Blo 1240438 1861331 := bstep (se 1 (by rfl) ⟨1395998, by rfl⟩ : syracuseStep 1861331 = 2791997) B2791997
theorem B1861361 : Blo 1240438 1861361 := bstep (se 2 (by rfl) ⟨698010, by rfl⟩ : syracuseStep 1861361 = 1396021) B1396021
theorem B1861379 : Blo 1240438 1861379 := bstep (se 1 (by rfl) ⟨1396034, by rfl⟩ : syracuseStep 1861379 = 2792069) B2792069
theorem B7948037 : Blo 1240438 7948037 := bstep (se 4 (by rfl) ⟨745128, by rfl⟩ : syracuseStep 7948037 = 1490257) B1490257
theorem B2238211 : Blo 1240438 2238211 := bstep (se 1 (by rfl) ⟨1678658, by rfl⟩ : syracuseStep 2238211 = 3357317) B3357317
theorem B1861409 : Blo 1240438 1861409 := bstep (se 2 (by rfl) ⟨698028, by rfl⟩ : syracuseStep 1861409 = 1396057) B1396057
theorem B1861427 : Blo 1240438 1861427 := bstep (se 1 (by rfl) ⟨1396070, by rfl⟩ : syracuseStep 1861427 = 2792141) B2792141
theorem B1861457 : Blo 1240438 1861457 := bstep (se 2 (by rfl) ⟨698046, by rfl⟩ : syracuseStep 1861457 = 1396093) B1396093
theorem B2795345 : Blo 1240438 2795345 := bstep (se 2 (by rfl) ⟨1048254, by rfl⟩ : syracuseStep 2795345 = 2096509) B2096509
theorem B3532643 : Blo 1240438 3532643 := bstep (se 1 (by rfl) ⟨2649482, by rfl⟩ : syracuseStep 3532643 = 5298965) B5298965
theorem B1861475 : Blo 1240438 1861475 := bstep (se 1 (by rfl) ⟨1396106, by rfl⟩ : syracuseStep 1861475 = 2792213) B2792213
theorem B4474723 : Blo 1240438 4474723 := bstep (se 1 (by rfl) ⟨3356042, by rfl⟩ : syracuseStep 4474723 = 6712085) B6712085
theorem B2795363 : Blo 1240438 2795363 := bstep (se 1 (by rfl) ⟨2096522, by rfl⟩ : syracuseStep 2795363 = 4193045) B4193045
theorem B1861505 : Blo 1240438 1861505 := bstep (se 2 (by rfl) ⟨698064, by rfl⟩ : syracuseStep 1861505 = 1396129) B1396129
theorem B1861523 : Blo 1240438 1861523 := bstep (se 1 (by rfl) ⟨1396142, by rfl⟩ : syracuseStep 1861523 = 2792285) B2792285
theorem B4188077 : Blo 1240438 4188077 := bstep (se 3 (by rfl) ⟨785264, by rfl⟩ : syracuseStep 4188077 = 1570529) B1570529
theorem B1861553 : Blo 1240438 1861553 := bstep (se 2 (by rfl) ⟨698082, by rfl⟩ : syracuseStep 1861553 = 1396165) B1396165
theorem B1861571 : Blo 1240438 1861571 := bstep (se 1 (by rfl) ⟨1396178, by rfl⟩ : syracuseStep 1861571 = 2792357) B2792357
theorem B1861601 : Blo 1240438 1861601 := bstep (se 2 (by rfl) ⟨698100, by rfl⟩ : syracuseStep 1861601 = 1396201) B1396201
theorem B4188131 : Blo 1240438 4188131 := bstep (se 1 (by rfl) ⟨3141098, by rfl⟩ : syracuseStep 4188131 = 6282197) B6282197
theorem B1861619 : Blo 1240438 1861619 := bstep (se 1 (by rfl) ⟨1396214, by rfl⟩ : syracuseStep 1861619 = 2792429) B2792429
theorem B1861649 : Blo 1240438 1861649 := bstep (se 2 (by rfl) ⟨698118, by rfl⟩ : syracuseStep 1861649 = 1396237) B1396237
theorem B1861667 : Blo 1240438 1861667 := bstep (se 1 (by rfl) ⟨1396250, by rfl⟩ : syracuseStep 1861667 = 2792501) B2792501
theorem B1861697 : Blo 1240438 1861697 := bstep (se 2 (by rfl) ⟨698136, by rfl⟩ : syracuseStep 1861697 = 1396273) B1396273
theorem B1861715 : Blo 1240438 1861715 := bstep (se 1 (by rfl) ⟨1396286, by rfl⟩ : syracuseStep 1861715 = 2792573) B2792573
theorem B1861745 : Blo 1240438 1861745 := bstep (se 2 (by rfl) ⟨698154, by rfl⟩ : syracuseStep 1861745 = 1396309) B1396309
theorem B1861763 : Blo 1240438 1861763 := bstep (se 1 (by rfl) ⟨1396322, by rfl⟩ : syracuseStep 1861763 = 2792645) B2792645
theorem B1861793 : Blo 1240438 1861793 := bstep (se 2 (by rfl) ⟨698172, by rfl⟩ : syracuseStep 1861793 = 1396345) B1396345
theorem B1861811 : Blo 1240438 1861811 := bstep (se 1 (by rfl) ⟨1396358, by rfl⟩ : syracuseStep 1861811 = 2792717) B2792717
theorem B24176837 : Blo 1240438 24176837 := bstep (se 4 (by rfl) ⟨2266578, by rfl⟩ : syracuseStep 24176837 = 4533157) B4533157
theorem B1861841 : Blo 1240438 1861841 := bstep (se 2 (by rfl) ⟨698190, by rfl⟩ : syracuseStep 1861841 = 1396381) B1396381
theorem B2238673 : Blo 1240438 2238673 := bstep (se 2 (by rfl) ⟨839502, by rfl⟩ : syracuseStep 2238673 = 1679005) B1679005
theorem B1861859 : Blo 1240438 1861859 := bstep (se 1 (by rfl) ⟨1396394, by rfl⟩ : syracuseStep 1861859 = 2792789) B2792789
theorem B4188401 : Blo 1240438 4188401 := bstep (se 2 (by rfl) ⟨1570650, by rfl⟩ : syracuseStep 4188401 = 3141301) B3141301
theorem B1861889 : Blo 1240438 1861889 := bstep (se 2 (by rfl) ⟨698208, by rfl⟩ : syracuseStep 1861889 = 1396417) B1396417
theorem B5105933 : Blo 1240438 5105933 := bstep (se 3 (by rfl) ⟨957362, by rfl⟩ : syracuseStep 5105933 = 1914725) B1914725
theorem B1861907 : Blo 1240438 1861907 := bstep (se 1 (by rfl) ⟨1396430, by rfl⟩ : syracuseStep 1861907 = 2792861) B2792861
theorem B1861937 : Blo 1240438 1861937 := bstep (se 2 (by rfl) ⟨698226, by rfl⟩ : syracuseStep 1861937 = 1396453) B1396453
theorem B1861955 : Blo 1240438 1861955 := bstep (se 1 (by rfl) ⟨1396466, by rfl⟩ : syracuseStep 1861955 = 2792933) B2792933
theorem B4475213 : Blo 1240438 4475213 := bstep (se 3 (by rfl) ⟨839102, by rfl⟩ : syracuseStep 4475213 = 1678205) B1678205
theorem B1861985 : Blo 1240438 1861985 := bstep (se 2 (by rfl) ⟨698244, by rfl⟩ : syracuseStep 1861985 = 1396489) B1396489
theorem B1862003 : Blo 1240438 1862003 := bstep (se 1 (by rfl) ⟨1396502, by rfl⟩ : syracuseStep 1862003 = 2793005) B2793005
theorem B3139985 : Blo 1240438 3139985 := bstep (se 2 (by rfl) ⟨1177494, by rfl⟩ : syracuseStep 3139985 = 2354989) B2354989
theorem B1862033 : Blo 1240438 1862033 := bstep (se 2 (by rfl) ⟨698262, by rfl⟩ : syracuseStep 1862033 = 1396525) B1396525
theorem B1862051 : Blo 1240438 1862051 := bstep (se 1 (by rfl) ⟨1396538, by rfl⟩ : syracuseStep 1862051 = 2793077) B2793077
theorem B5302691 : Blo 1240438 5302691 := bstep (se 1 (by rfl) ⟨3977018, by rfl⟩ : syracuseStep 5302691 = 7954037) B7954037
theorem B5966257 : Blo 1240438 5966257 := bstep (se 2 (by rfl) ⟨2237346, by rfl⟩ : syracuseStep 5966257 = 4474693) B4474693
theorem B1862081 : Blo 1240438 1862081 := bstep (se 2 (by rfl) ⟨698280, by rfl⟩ : syracuseStep 1862081 = 1396561) B1396561
theorem B1862099 : Blo 1240438 1862099 := bstep (se 1 (by rfl) ⟨1396574, by rfl⟩ : syracuseStep 1862099 = 2793149) B2793149
theorem B1862129 : Blo 1240438 1862129 := bstep (se 2 (by rfl) ⟨698298, by rfl⟩ : syracuseStep 1862129 = 1396597) B1396597
theorem B1862147 : Blo 1240438 1862147 := bstep (se 1 (by rfl) ⟨1396610, by rfl⟩ : syracuseStep 1862147 = 2793221) B2793221
theorem B1862177 : Blo 1240438 1862177 := bstep (se 2 (by rfl) ⟨698316, by rfl⟩ : syracuseStep 1862177 = 1396633) B1396633
theorem B1862195 : Blo 1240438 1862195 := bstep (se 1 (by rfl) ⟨1396646, by rfl⟩ : syracuseStep 1862195 = 2793293) B2793293
theorem B3353165 : Blo 1240438 3353165 := bstep (se 3 (by rfl) ⟨628718, by rfl⟩ : syracuseStep 3353165 = 1257437) B1257437
theorem B3975761 : Blo 1240438 3975761 := bstep (se 2 (by rfl) ⟨1490910, by rfl⟩ : syracuseStep 3975761 = 2981821) B2981821
theorem B1862225 : Blo 1240438 1862225 := bstep (se 2 (by rfl) ⟨698334, by rfl⟩ : syracuseStep 1862225 = 1396669) B1396669
theorem B1862243 : Blo 1240438 1862243 := bstep (se 1 (by rfl) ⟨1396682, by rfl⟩ : syracuseStep 1862243 = 2793365) B2793365
theorem B6285923 : Blo 1240438 6285923 := bstep (se 1 (by rfl) ⟨4714442, by rfl⟩ : syracuseStep 6285923 = 9428885) B9428885
theorem B1862273 : Blo 1240438 1862273 := bstep (se 2 (by rfl) ⟨698352, by rfl⟩ : syracuseStep 1862273 = 1396705) B1396705
theorem B3066499 : Blo 1240438 3066499 := bstep (se 1 (by rfl) ⟨2299874, by rfl⟩ : syracuseStep 3066499 = 4599749) B4599749
theorem B3533453 : Blo 1240438 3533453 := bstep (se 3 (by rfl) ⟨662522, by rfl⟩ : syracuseStep 3533453 = 1325045) B1325045
theorem B1862291 : Blo 1240438 1862291 := bstep (se 1 (by rfl) ⟨1396718, by rfl⟩ : syracuseStep 1862291 = 2793437) B2793437
theorem B4713137 : Blo 1240438 4713137 := bstep (se 2 (by rfl) ⟨1767426, by rfl⟩ : syracuseStep 4713137 = 3534853) B3534853
theorem B1862321 : Blo 1240438 1862321 := bstep (se 2 (by rfl) ⟨698370, by rfl⟩ : syracuseStep 1862321 = 1396741) B1396741
theorem B1862339 : Blo 1240438 1862339 := bstep (se 1 (by rfl) ⟨1396754, by rfl⟩ : syracuseStep 1862339 = 2793509) B2793509
theorem B1862369 : Blo 1240438 1862369 := bstep (se 2 (by rfl) ⟨698388, by rfl⟩ : syracuseStep 1862369 = 1396777) B1396777
theorem B1862387 : Blo 1240438 1862387 := bstep (se 1 (by rfl) ⟨1396790, by rfl⟩ : syracuseStep 1862387 = 2793581) B2793581
theorem B4188941 : Blo 1240438 4188941 := bstep (se 3 (by rfl) ⟨785426, by rfl⟩ : syracuseStep 4188941 = 1570853) B1570853
theorem B1862417 : Blo 1240438 1862417 := bstep (se 2 (by rfl) ⟨698406, by rfl⟩ : syracuseStep 1862417 = 1396813) B1396813
theorem B1862435 : Blo 1240438 1862435 := bstep (se 1 (by rfl) ⟨1396826, by rfl⟩ : syracuseStep 1862435 = 2793653) B2793653
theorem B1862465 : Blo 1240438 1862465 := bstep (se 2 (by rfl) ⟨698424, by rfl⟩ : syracuseStep 1862465 = 1396849) B1396849
theorem B4188995 : Blo 1240438 4188995 := bstep (se 1 (by rfl) ⟨3141746, by rfl⟩ : syracuseStep 4188995 = 6283493) B6283493
theorem B3533645 : Blo 1240438 3533645 := bstep (se 3 (by rfl) ⟨662558, by rfl⟩ : syracuseStep 3533645 = 1325117) B1325117
theorem B1862483 : Blo 1240438 1862483 := bstep (se 1 (by rfl) ⟨1396862, by rfl⟩ : syracuseStep 1862483 = 2793725) B2793725
theorem B27200369 : Blo 1240438 27200369 := bstep (se 2 (by rfl) ⟨10200138, by rfl⟩ : syracuseStep 27200369 = 20400277) B20400277
theorem B1862513 : Blo 1240438 1862513 := bstep (se 2 (by rfl) ⟨698442, by rfl⟩ : syracuseStep 1862513 = 1396885) B1396885
theorem B1395571 : Blo 1240438 1395571 := bstep (se 1 (by rfl) ⟨1046678, by rfl⟩ : syracuseStep 1395571 = 2093357) B2093357
theorem B1862531 : Blo 1240438 1862531 := bstep (se 1 (by rfl) ⟨1396898, by rfl⟩ : syracuseStep 1862531 = 2793797) B2793797
theorem B1862561 : Blo 1240438 1862561 := bstep (se 2 (by rfl) ⟨698460, by rfl⟩ : syracuseStep 1862561 = 1396921) B1396921
theorem B1862579 : Blo 1240438 1862579 := bstep (se 1 (by rfl) ⟨1396934, by rfl⟩ : syracuseStep 1862579 = 2793869) B2793869
theorem B1862609 : Blo 1240438 1862609 := bstep (se 2 (by rfl) ⟨698478, by rfl⟩ : syracuseStep 1862609 = 1396957) B1396957
theorem B1862627 : Blo 1240438 1862627 := bstep (se 1 (by rfl) ⟨1396970, by rfl⟩ : syracuseStep 1862627 = 2793941) B2793941
theorem B1862657 : Blo 1240438 1862657 := bstep (se 2 (by rfl) ⟨698496, by rfl⟩ : syracuseStep 1862657 = 1396993) B1396993
theorem B1395715 : Blo 1240438 1395715 := bstep (se 1 (by rfl) ⟨1046786, by rfl⟩ : syracuseStep 1395715 = 2093573) B2093573
theorem B1862675 : Blo 1240438 1862675 := bstep (se 1 (by rfl) ⟨1397006, by rfl⟩ : syracuseStep 1862675 = 2794013) B2794013
theorem B1862705 : Blo 1240438 1862705 := bstep (se 2 (by rfl) ⟨698514, by rfl⟩ : syracuseStep 1862705 = 1397029) B1397029
theorem B2829379 : Blo 1240438 2829379 := bstep (se 1 (by rfl) ⟨2122034, by rfl⟩ : syracuseStep 2829379 = 4244069) B4244069
theorem B1862723 : Blo 1240438 1862723 := bstep (se 1 (by rfl) ⟨1397042, by rfl⟩ : syracuseStep 1862723 = 2794085) B2794085
theorem B4189265 : Blo 1240438 4189265 := bstep (se 2 (by rfl) ⟨1570974, by rfl⟩ : syracuseStep 4189265 = 3141949) B3141949
theorem B1862753 : Blo 1240438 1862753 := bstep (se 2 (by rfl) ⟨698532, by rfl⟩ : syracuseStep 1862753 = 1397065) B1397065
theorem B1862771 : Blo 1240438 1862771 := bstep (se 1 (by rfl) ⟨1397078, by rfl⟩ : syracuseStep 1862771 = 2794157) B2794157
theorem B1862801 : Blo 1240438 1862801 := bstep (se 2 (by rfl) ⟨698550, by rfl⟩ : syracuseStep 1862801 = 1397101) B1397101
theorem B1395859 : Blo 1240438 1395859 := bstep (se 1 (by rfl) ⟨1046894, by rfl⟩ : syracuseStep 1395859 = 2093789) B2093789
theorem B5033123 : Blo 1240438 5033123 := bstep (se 1 (by rfl) ⟨3774842, by rfl⟩ : syracuseStep 5033123 = 7549685) B7549685
theorem B1862819 : Blo 1240438 1862819 := bstep (se 1 (by rfl) ⟨1397114, by rfl⟩ : syracuseStep 1862819 = 2794229) B2794229
theorem B1862849 : Blo 1240438 1862849 := bstep (se 2 (by rfl) ⟨698568, by rfl⟩ : syracuseStep 1862849 = 1397137) B1397137
theorem B3353795 : Blo 1240438 3353795 := bstep (se 1 (by rfl) ⟨2515346, by rfl⟩ : syracuseStep 3353795 = 5030693) B5030693
theorem B13429957 : Blo 1240438 13429957 := bstep (se 4 (by rfl) ⟨1259058, by rfl⟩ : syracuseStep 13429957 = 2518117) B2518117
theorem B1862867 : Blo 1240438 1862867 := bstep (se 1 (by rfl) ⟨1397150, by rfl⟩ : syracuseStep 1862867 = 2794301) B2794301
theorem B45321443 : Blo 1240438 45321443 := bstep (se 1 (by rfl) ⟨33991082, by rfl⟩ : syracuseStep 45321443 = 67982165) B67982165
theorem B1862897 : Blo 1240438 1862897 := bstep (se 2 (by rfl) ⟨698586, by rfl⟩ : syracuseStep 1862897 = 1397173) B1397173
theorem B1862915 : Blo 1240438 1862915 := bstep (se 1 (by rfl) ⟨1397186, by rfl⟩ : syracuseStep 1862915 = 2794373) B2794373
theorem B1862945 : Blo 1240438 1862945 := bstep (se 2 (by rfl) ⟨698604, by rfl⟩ : syracuseStep 1862945 = 1397209) B1397209
theorem B1396003 : Blo 1240438 1396003 := bstep (se 1 (by rfl) ⟨1047002, by rfl⟩ : syracuseStep 1396003 = 2094005) B2094005
theorem B1862963 : Blo 1240438 1862963 := bstep (se 1 (by rfl) ⟨1397222, by rfl⟩ : syracuseStep 1862963 = 2794445) B2794445
theorem B1862993 : Blo 1240438 1862993 := bstep (se 2 (by rfl) ⟨698622, by rfl⟩ : syracuseStep 1862993 = 1397245) B1397245
theorem B1863011 : Blo 1240438 1863011 := bstep (se 1 (by rfl) ⟨1397258, by rfl⟩ : syracuseStep 1863011 = 2794517) B2794517
theorem B3140977 : Blo 1240438 3140977 := bstep (se 2 (by rfl) ⟨1177866, by rfl⟩ : syracuseStep 3140977 = 2355733) B2355733
theorem B1863041 : Blo 1240438 1863041 := bstep (se 2 (by rfl) ⟨698640, by rfl⟩ : syracuseStep 1863041 = 1397281) B1397281
theorem B1240451 : Blo 1240438 1240451 := bstep (se 1 (by rfl) ⟨930338, by rfl⟩ : syracuseStep 1240451 = 1860677) B1860677
theorem B3353987 : Blo 1240438 3353987 := bstep (se 1 (by rfl) ⟨2515490, by rfl⟩ : syracuseStep 3353987 = 5030981) B5030981
theorem B4246915 : Blo 1240438 4246915 := bstep (se 1 (by rfl) ⟨3185186, by rfl⟩ : syracuseStep 4246915 = 6370373) B6370373
theorem B6991237 : Blo 1240438 6991237 := bstep (se 4 (by rfl) ⟨655428, by rfl⟩ : syracuseStep 6991237 = 1310857) B1310857
theorem B6286733 : Blo 1240438 6286733 := bstep (se 3 (by rfl) ⟨1178762, by rfl⟩ : syracuseStep 6286733 = 2357525) B2357525
theorem B1240467 : Blo 1240438 1240467 := bstep (se 1 (by rfl) ⟨930350, by rfl⟩ : syracuseStep 1240467 = 1860701) B1860701
theorem B1863059 : Blo 1240438 1863059 := bstep (se 1 (by rfl) ⟨1397294, by rfl⟩ : syracuseStep 1863059 = 2794589) B2794589
theorem B1240483 : Blo 1240438 1240483 := bstep (se 1 (by rfl) ⟨930362, by rfl⟩ : syracuseStep 1240483 = 1860725) B1860725
theorem B2829745 : Blo 1240438 2829745 := bstep (se 2 (by rfl) ⟨1061154, by rfl⟩ : syracuseStep 2829745 = 2122309) B2122309
theorem B1863089 : Blo 1240438 1863089 := bstep (se 2 (by rfl) ⟨698658, by rfl⟩ : syracuseStep 1863089 = 1397317) B1397317
theorem B1240499 : Blo 1240438 1240499 := bstep (se 1 (by rfl) ⟨930374, by rfl⟩ : syracuseStep 1240499 = 1860749) B1860749
theorem B1396147 : Blo 1240438 1396147 := bstep (se 1 (by rfl) ⟨1047110, by rfl⟩ : syracuseStep 1396147 = 2094221) B2094221
theorem B1240515 : Blo 1240438 1240515 := bstep (se 1 (by rfl) ⟨930386, by rfl⟩ : syracuseStep 1240515 = 1860773) B1860773
theorem B1863107 : Blo 1240438 1863107 := bstep (se 1 (by rfl) ⟨1397330, by rfl⟩ : syracuseStep 1863107 = 2794661) B2794661
theorem B1240531 : Blo 1240438 1240531 := bstep (se 1 (by rfl) ⟨930398, by rfl⟩ : syracuseStep 1240531 = 1860797) B1860797
theorem B1887713 : Blo 1240438 1887713 := bstep (se 2 (by rfl) ⟨707892, by rfl⟩ : syracuseStep 1887713 = 1415785) B1415785
theorem B1240547 : Blo 1240438 1240547 := bstep (se 1 (by rfl) ⟨930410, by rfl⟩ : syracuseStep 1240547 = 1860821) B1860821
theorem B1863137 : Blo 1240438 1863137 := bstep (se 2 (by rfl) ⟨698676, by rfl⟩ : syracuseStep 1863137 = 1397353) B1397353
theorem B3976685 : Blo 1240438 3976685 := bstep (se 3 (by rfl) ⟨745628, by rfl⟩ : syracuseStep 3976685 = 1491257) B1491257
theorem B1240563 : Blo 1240438 1240563 := bstep (se 1 (by rfl) ⟨930422, by rfl⟩ : syracuseStep 1240563 = 1860845) B1860845
theorem B1592819 : Blo 1240438 1592819 := bstep (se 1 (by rfl) ⟨1194614, by rfl⟩ : syracuseStep 1592819 = 2389229) B2389229
theorem B1863155 : Blo 1240438 1863155 := bstep (se 1 (by rfl) ⟨1397366, by rfl⟩ : syracuseStep 1863155 = 2794733) B2794733
theorem B1240579 : Blo 1240438 1240579 := bstep (se 1 (by rfl) ⟨930434, by rfl⟩ : syracuseStep 1240579 = 1860869) B1860869
theorem B1863185 : Blo 1240438 1863185 := bstep (se 2 (by rfl) ⟨698694, by rfl⟩ : syracuseStep 1863185 = 1397389) B1397389
theorem B1240595 : Blo 1240438 1240595 := bstep (se 1 (by rfl) ⟨930446, by rfl⟩ : syracuseStep 1240595 = 1860893) B1860893
theorem B1240611 : Blo 1240438 1240611 := bstep (se 1 (by rfl) ⟨930458, by rfl⟩ : syracuseStep 1240611 = 1860917) B1860917
theorem B1863203 : Blo 1240438 1863203 := bstep (se 1 (by rfl) ⟨1397402, by rfl⟩ : syracuseStep 1863203 = 2794805) B2794805
theorem B5664305 : Blo 1240438 5664305 := bstep (se 2 (by rfl) ⟨2124114, by rfl⟩ : syracuseStep 5664305 = 4248229) B4248229
theorem B1240627 : Blo 1240438 1240627 := bstep (se 1 (by rfl) ⟨930470, by rfl⟩ : syracuseStep 1240627 = 1860941) B1860941
theorem B1863233 : Blo 1240438 1863233 := bstep (se 2 (by rfl) ⟨698712, by rfl⟩ : syracuseStep 1863233 = 1397425) B1397425
theorem B1240643 : Blo 1240438 1240643 := bstep (se 1 (by rfl) ⟨930482, by rfl⟩ : syracuseStep 1240643 = 1860965) B1860965
theorem B1396291 : Blo 1240438 1396291 := bstep (se 1 (by rfl) ⟨1047218, by rfl⟩ : syracuseStep 1396291 = 2094437) B2094437
theorem B1240659 : Blo 1240438 1240659 := bstep (se 1 (by rfl) ⟨930494, by rfl⟩ : syracuseStep 1240659 = 1860989) B1860989
theorem B1863251 : Blo 1240438 1863251 := bstep (se 1 (by rfl) ⟨1397438, by rfl⟩ : syracuseStep 1863251 = 2794877) B2794877
theorem B1240675 : Blo 1240438 1240675 := bstep (se 1 (by rfl) ⟨930506, by rfl⟩ : syracuseStep 1240675 = 1861013) B1861013
theorem B4189805 : Blo 1240438 4189805 := bstep (se 3 (by rfl) ⟨785588, by rfl⟩ : syracuseStep 4189805 = 1571177) B1571177
theorem B1863281 : Blo 1240438 1863281 := bstep (se 2 (by rfl) ⟨698730, by rfl⟩ : syracuseStep 1863281 = 1397461) B1397461
theorem B1240691 : Blo 1240438 1240691 := bstep (se 1 (by rfl) ⟨930518, by rfl⟩ : syracuseStep 1240691 = 1861037) B1861037
theorem B1240707 : Blo 1240438 1240707 := bstep (se 1 (by rfl) ⟨930530, by rfl⟩ : syracuseStep 1240707 = 1861061) B1861061
theorem B3141251 : Blo 1240438 3141251 := bstep (se 1 (by rfl) ⟨2355938, by rfl⟩ : syracuseStep 3141251 = 4711877) B4711877
theorem B1863299 : Blo 1240438 1863299 := bstep (se 1 (by rfl) ⟨1397474, by rfl⟩ : syracuseStep 1863299 = 2794949) B2794949
theorem B1240723 : Blo 1240438 1240723 := bstep (se 1 (by rfl) ⟨930542, by rfl⟩ : syracuseStep 1240723 = 1861085) B1861085
theorem B1863329 : Blo 1240438 1863329 := bstep (se 2 (by rfl) ⟨698748, by rfl⟩ : syracuseStep 1863329 = 1397497) B1397497
theorem B1240739 : Blo 1240438 1240739 := bstep (se 1 (by rfl) ⟨930554, by rfl⟩ : syracuseStep 1240739 = 1861109) B1861109
theorem B7949987 : Blo 1240438 7949987 := bstep (se 1 (by rfl) ⟨5962490, by rfl⟩ : syracuseStep 7949987 = 11924981) B11924981
theorem B4189859 : Blo 1240438 4189859 := bstep (se 1 (by rfl) ⟨3142394, by rfl⟩ : syracuseStep 4189859 = 6284789) B6284789
theorem B3976877 : Blo 1240438 3976877 := bstep (se 3 (by rfl) ⟨745664, by rfl⟩ : syracuseStep 3976877 = 1491329) B1491329
theorem B1240755 : Blo 1240438 1240755 := bstep (se 1 (by rfl) ⟨930566, by rfl⟩ : syracuseStep 1240755 = 1861133) B1861133
theorem B1863347 : Blo 1240438 1863347 := bstep (se 1 (by rfl) ⟨1397510, by rfl⟩ : syracuseStep 1863347 = 2795021) B2795021
theorem B1240771 : Blo 1240438 1240771 := bstep (se 1 (by rfl) ⟨930578, by rfl⟩ : syracuseStep 1240771 = 1861157) B1861157
theorem B9432773 : Blo 1240438 9432773 := bstep (se 4 (by rfl) ⟨884322, by rfl⟩ : syracuseStep 9432773 = 1768645) B1768645
theorem B4247245 : Blo 1240438 4247245 := bstep (se 3 (by rfl) ⟨796358, by rfl⟩ : syracuseStep 4247245 = 1592717) B1592717
theorem B1863377 : Blo 1240438 1863377 := bstep (se 2 (by rfl) ⟨698766, by rfl⟩ : syracuseStep 1863377 = 1397533) B1397533
theorem B1240787 : Blo 1240438 1240787 := bstep (se 1 (by rfl) ⟨930590, by rfl⟩ : syracuseStep 1240787 = 1861181) B1861181
theorem B1396435 : Blo 1240438 1396435 := bstep (se 1 (by rfl) ⟨1047326, by rfl⟩ : syracuseStep 1396435 = 2094653) B2094653
theorem B1240803 : Blo 1240438 1240803 := bstep (se 1 (by rfl) ⟨930602, by rfl⟩ : syracuseStep 1240803 = 1861205) B1861205
theorem B1863395 : Blo 1240438 1863395 := bstep (se 1 (by rfl) ⟨1397546, by rfl⟩ : syracuseStep 1863395 = 2795093) B2795093
theorem B1240819 : Blo 1240438 1240819 := bstep (se 1 (by rfl) ⟨930614, by rfl⟩ : syracuseStep 1240819 = 1861229) B1861229
theorem B1863425 : Blo 1240438 1863425 := bstep (se 2 (by rfl) ⟨698784, by rfl⟩ : syracuseStep 1863425 = 1397569) B1397569
theorem B1240835 : Blo 1240438 1240835 := bstep (se 1 (by rfl) ⟨930626, by rfl⟩ : syracuseStep 1240835 = 1861253) B1861253
theorem B1240851 : Blo 1240438 1240851 := bstep (se 1 (by rfl) ⟨930638, by rfl⟩ : syracuseStep 1240851 = 1861277) B1861277
theorem B1863443 : Blo 1240438 1863443 := bstep (se 1 (by rfl) ⟨1397582, by rfl⟩ : syracuseStep 1863443 = 2795165) B2795165
theorem B1240867 : Blo 1240438 1240867 := bstep (se 1 (by rfl) ⟨930650, by rfl⟩ : syracuseStep 1240867 = 1861301) B1861301
theorem B3534637 : Blo 1240438 3534637 := bstep (se 3 (by rfl) ⟨662744, by rfl⟩ : syracuseStep 3534637 = 1325489) B1325489
theorem B1863473 : Blo 1240438 1863473 := bstep (se 2 (by rfl) ⟨698802, by rfl⟩ : syracuseStep 1863473 = 1397605) B1397605
theorem B1240883 : Blo 1240438 1240883 := bstep (se 1 (by rfl) ⟨930662, by rfl⟩ : syracuseStep 1240883 = 1861325) B1861325
theorem B1240899 : Blo 1240438 1240899 := bstep (se 1 (by rfl) ⟨930674, by rfl⟩ : syracuseStep 1240899 = 1861349) B1861349
theorem B3141443 : Blo 1240438 3141443 := bstep (se 1 (by rfl) ⟨2356082, by rfl⟩ : syracuseStep 3141443 = 4712165) B4712165
theorem B1863491 : Blo 1240438 1863491 := bstep (se 1 (by rfl) ⟨1397618, by rfl⟩ : syracuseStep 1863491 = 2795237) B2795237
theorem B1240915 : Blo 1240438 1240915 := bstep (se 1 (by rfl) ⟨930686, by rfl⟩ : syracuseStep 1240915 = 1861373) B1861373
theorem B1863521 : Blo 1240438 1863521 := bstep (se 2 (by rfl) ⟨698820, by rfl⟩ : syracuseStep 1863521 = 1397641) B1397641
theorem B1240931 : Blo 1240438 1240931 := bstep (se 1 (by rfl) ⟨930698, by rfl⟩ : syracuseStep 1240931 = 1861397) B1861397
theorem B1396579 : Blo 1240438 1396579 := bstep (se 1 (by rfl) ⟨1047434, by rfl⟩ : syracuseStep 1396579 = 2094869) B2094869
theorem B1240947 : Blo 1240438 1240947 := bstep (se 1 (by rfl) ⟨930710, by rfl⟩ : syracuseStep 1240947 = 1861421) B1861421
theorem B1863539 : Blo 1240438 1863539 := bstep (se 1 (by rfl) ⟨1397654, by rfl⟩ : syracuseStep 1863539 = 2795309) B2795309
theorem B1240963 : Blo 1240438 1240963 := bstep (se 1 (by rfl) ⟨930722, by rfl⟩ : syracuseStep 1240963 = 1861445) B1861445
theorem B7073669 : Blo 1240438 7073669 := bstep (se 4 (by rfl) ⟨663156, by rfl⟩ : syracuseStep 7073669 = 1326313) B1326313
theorem B1863569 : Blo 1240438 1863569 := bstep (se 2 (by rfl) ⟨698838, by rfl⟩ : syracuseStep 1863569 = 1397677) B1397677
theorem B1240979 : Blo 1240438 1240979 := bstep (se 1 (by rfl) ⟨930734, by rfl⟩ : syracuseStep 1240979 = 1861469) B1861469
theorem B1240995 : Blo 1240438 1240995 := bstep (se 1 (by rfl) ⟨930746, by rfl⟩ : syracuseStep 1240995 = 1861493) B1861493
theorem B1863587 : Blo 1240438 1863587 := bstep (se 1 (by rfl) ⟨1397690, by rfl⟩ : syracuseStep 1863587 = 2795381) B2795381
theorem B4190129 : Blo 1240438 4190129 := bstep (se 2 (by rfl) ⟨1571298, by rfl⟩ : syracuseStep 4190129 = 3142597) B3142597
theorem B1241011 : Blo 1240438 1241011 := bstep (se 1 (by rfl) ⟨930758, by rfl⟩ : syracuseStep 1241011 = 1861517) B1861517
theorem B1863617 : Blo 1240438 1863617 := bstep (se 2 (by rfl) ⟨698856, by rfl⟩ : syracuseStep 1863617 = 1397713) B1397713
theorem B1241027 : Blo 1240438 1241027 := bstep (se 1 (by rfl) ⟨930770, by rfl⟩ : syracuseStep 1241027 = 1861541) B1861541
theorem B1241043 : Blo 1240438 1241043 := bstep (se 1 (by rfl) ⟨930782, by rfl⟩ : syracuseStep 1241043 = 1861565) B1861565
theorem B1863635 : Blo 1240438 1863635 := bstep (se 1 (by rfl) ⟨1397726, by rfl⟩ : syracuseStep 1863635 = 2795453) B2795453
theorem B1241059 : Blo 1240438 1241059 := bstep (se 1 (by rfl) ⟨930794, by rfl⟩ : syracuseStep 1241059 = 1861589) B1861589
theorem B1241075 : Blo 1240438 1241075 := bstep (se 1 (by rfl) ⟨930806, by rfl⟩ : syracuseStep 1241075 = 1861613) B1861613
theorem B1396723 : Blo 1240438 1396723 := bstep (se 1 (by rfl) ⟨1047542, by rfl⟩ : syracuseStep 1396723 = 2095085) B2095085
theorem B1241091 : Blo 1240438 1241091 := bstep (se 1 (by rfl) ⟨930818, by rfl⟩ : syracuseStep 1241091 = 1861637) B1861637
theorem B14135309 : Blo 1240438 14135309 := bstep (se 3 (by rfl) ⟨2650370, by rfl⟩ : syracuseStep 14135309 = 5300741) B5300741
theorem B1241107 : Blo 1240438 1241107 := bstep (se 1 (by rfl) ⟨930830, by rfl⟩ : syracuseStep 1241107 = 1861661) B1861661
theorem B1241123 : Blo 1240438 1241123 := bstep (se 1 (by rfl) ⟨930842, by rfl⟩ : syracuseStep 1241123 = 1861685) B1861685
theorem B1241139 : Blo 1240438 1241139 := bstep (se 1 (by rfl) ⟨930854, by rfl⟩ : syracuseStep 1241139 = 1861709) B1861709
theorem B1241155 : Blo 1240438 1241155 := bstep (se 1 (by rfl) ⟨930866, by rfl⟩ : syracuseStep 1241155 = 1861733) B1861733
theorem B1241171 : Blo 1240438 1241171 := bstep (se 1 (by rfl) ⟨930878, by rfl⟩ : syracuseStep 1241171 = 1861757) B1861757
theorem B1241187 : Blo 1240438 1241187 := bstep (se 1 (by rfl) ⟨930890, by rfl⟩ : syracuseStep 1241187 = 1861781) B1861781
theorem B4714595 : Blo 1240438 4714595 := bstep (se 1 (by rfl) ⟨3535946, by rfl⟩ : syracuseStep 4714595 = 7071893) B7071893
theorem B1241203 : Blo 1240438 1241203 := bstep (se 1 (by rfl) ⟨930902, by rfl⟩ : syracuseStep 1241203 = 1861805) B1861805
theorem B2355331 : Blo 1240438 2355331 := bstep (se 1 (by rfl) ⟨1766498, by rfl⟩ : syracuseStep 2355331 = 3532997) B3532997
theorem B1241219 : Blo 1240438 1241219 := bstep (se 1 (by rfl) ⟨930914, by rfl⟩ : syracuseStep 1241219 = 1861829) B1861829
theorem B1396867 : Blo 1240438 1396867 := bstep (se 1 (by rfl) ⟨1047650, by rfl⟩ : syracuseStep 1396867 = 2095301) B2095301
theorem B1241235 : Blo 1240438 1241235 := bstep (se 1 (by rfl) ⟨930926, by rfl⟩ : syracuseStep 1241235 = 1861853) B1861853
theorem B1241251 : Blo 1240438 1241251 := bstep (se 1 (by rfl) ⟨930938, by rfl⟩ : syracuseStep 1241251 = 1861877) B1861877
theorem B1241267 : Blo 1240438 1241267 := bstep (se 1 (by rfl) ⟨930950, by rfl⟩ : syracuseStep 1241267 = 1861901) B1861901
theorem B2093249 : Blo 1240438 2093249 := bstep (se 2 (by rfl) ⟨784968, by rfl⟩ : syracuseStep 2093249 = 1569937) B1569937
theorem B1241283 : Blo 1240438 1241283 := bstep (se 1 (by rfl) ⟨930962, by rfl⟩ : syracuseStep 1241283 = 1861925) B1861925
theorem B1241299 : Blo 1240438 1241299 := bstep (se 1 (by rfl) ⟨930974, by rfl⟩ : syracuseStep 1241299 = 1861949) B1861949
theorem B1241315 : Blo 1240438 1241315 := bstep (se 1 (by rfl) ⟨930986, by rfl⟩ : syracuseStep 1241315 = 1861973) B1861973
theorem B1241331 : Blo 1240438 1241331 := bstep (se 1 (by rfl) ⟨930998, by rfl⟩ : syracuseStep 1241331 = 1861997) B1861997
theorem B1241347 : Blo 1240438 1241347 := bstep (se 1 (by rfl) ⟨931010, by rfl⟩ : syracuseStep 1241347 = 1862021) B1862021
theorem B1241363 : Blo 1240438 1241363 := bstep (se 1 (by rfl) ⟨931022, by rfl⟩ : syracuseStep 1241363 = 1862045) B1862045
theorem B1397011 : Blo 1240438 1397011 := bstep (se 1 (by rfl) ⟨1047758, by rfl⟩ : syracuseStep 1397011 = 2095517) B2095517
theorem B1241379 : Blo 1240438 1241379 := bstep (se 1 (by rfl) ⟨931034, by rfl⟩ : syracuseStep 1241379 = 1862069) B1862069
theorem B1241395 : Blo 1240438 1241395 := bstep (se 1 (by rfl) ⟨931046, by rfl⟩ : syracuseStep 1241395 = 1862093) B1862093
theorem B2093377 : Blo 1240438 2093377 := bstep (se 2 (by rfl) ⟨785016, by rfl⟩ : syracuseStep 2093377 = 1570033) B1570033
theorem B1241411 : Blo 1240438 1241411 := bstep (se 1 (by rfl) ⟨931058, by rfl⟩ : syracuseStep 1241411 = 1862117) B1862117
theorem B7074125 : Blo 1240438 7074125 := bstep (se 3 (by rfl) ⟨1326398, by rfl⟩ : syracuseStep 7074125 = 2652797) B2652797
theorem B1241427 : Blo 1240438 1241427 := bstep (se 1 (by rfl) ⟨931070, by rfl⟩ : syracuseStep 1241427 = 1862141) B1862141
theorem B2093411 : Blo 1240438 2093411 := bstep (se 1 (by rfl) ⟨1570058, by rfl⟩ : syracuseStep 2093411 = 3140117) B3140117
theorem B10744163 : Blo 1240438 10744163 := bstep (se 1 (by rfl) ⟨8058122, by rfl⟩ : syracuseStep 10744163 = 16116245) B16116245
theorem B1241443 : Blo 1240438 1241443 := bstep (se 1 (by rfl) ⟨931082, by rfl⟩ : syracuseStep 1241443 = 1862165) B1862165
theorem B1241459 : Blo 1240438 1241459 := bstep (se 1 (by rfl) ⟨931094, by rfl⟩ : syracuseStep 1241459 = 1862189) B1862189
theorem B1241475 : Blo 1240438 1241475 := bstep (se 1 (by rfl) ⟨931106, by rfl⟩ : syracuseStep 1241475 = 1862213) B1862213
theorem B3355025 : Blo 1240438 3355025 := bstep (se 2 (by rfl) ⟨1258134, by rfl⟩ : syracuseStep 3355025 = 2516269) B2516269
theorem B1241491 : Blo 1240438 1241491 := bstep (se 1 (by rfl) ⟨931118, by rfl⟩ : syracuseStep 1241491 = 1862237) B1862237
theorem B1241507 : Blo 1240438 1241507 := bstep (se 1 (by rfl) ⟨931130, by rfl⟩ : syracuseStep 1241507 = 1862261) B1862261
theorem B1397155 : Blo 1240438 1397155 := bstep (se 1 (by rfl) ⟨1047866, by rfl⟩ : syracuseStep 1397155 = 2095733) B2095733
theorem B1241523 : Blo 1240438 1241523 := bstep (se 1 (by rfl) ⟨931142, by rfl⟩ : syracuseStep 1241523 = 1862285) B1862285
theorem B1241539 : Blo 1240438 1241539 := bstep (se 1 (by rfl) ⟨931154, by rfl⟩ : syracuseStep 1241539 = 1862309) B1862309
theorem B19116485 : Blo 1240438 19116485 := bstep (se 4 (by rfl) ⟨1792170, by rfl⟩ : syracuseStep 19116485 = 3584341) B3584341
theorem B7066061 : Blo 1240438 7066061 := bstep (se 3 (by rfl) ⟨1324886, by rfl⟩ : syracuseStep 7066061 = 2649773) B2649773
theorem B4190669 : Blo 1240438 4190669 := bstep (se 3 (by rfl) ⟨785750, by rfl⟩ : syracuseStep 4190669 = 1571501) B1571501
theorem B1241555 : Blo 1240438 1241555 := bstep (se 1 (by rfl) ⟨931166, by rfl⟩ : syracuseStep 1241555 = 1862333) B1862333
theorem B2093539 : Blo 1240438 2093539 := bstep (se 1 (by rfl) ⟨1570154, by rfl⟩ : syracuseStep 2093539 = 3140309) B3140309
theorem B1241571 : Blo 1240438 1241571 := bstep (se 1 (by rfl) ⟨931178, by rfl⟩ : syracuseStep 1241571 = 1862357) B1862357
theorem B1241587 : Blo 1240438 1241587 := bstep (se 1 (by rfl) ⟨931190, by rfl⟩ : syracuseStep 1241587 = 1862381) B1862381
theorem B1241603 : Blo 1240438 1241603 := bstep (se 1 (by rfl) ⟨931202, by rfl⟩ : syracuseStep 1241603 = 1862405) B1862405
theorem B4190723 : Blo 1240438 4190723 := bstep (se 1 (by rfl) ⟨3143042, by rfl⟩ : syracuseStep 4190723 = 6286085) B6286085
theorem B1241619 : Blo 1240438 1241619 := bstep (se 1 (by rfl) ⟨931214, by rfl⟩ : syracuseStep 1241619 = 1862429) B1862429
theorem B1241635 : Blo 1240438 1241635 := bstep (se 1 (by rfl) ⟨931226, by rfl⟩ : syracuseStep 1241635 = 1862453) B1862453
theorem B1790515 : Blo 1240438 1790515 := bstep (se 1 (by rfl) ⟨1342886, by rfl⟩ : syracuseStep 1790515 = 2685773) B2685773
theorem B1241651 : Blo 1240438 1241651 := bstep (se 1 (by rfl) ⟨931238, by rfl⟩ : syracuseStep 1241651 = 1862477) B1862477
theorem B1397299 : Blo 1240438 1397299 := bstep (se 1 (by rfl) ⟨1047974, by rfl⟩ : syracuseStep 1397299 = 2095949) B2095949
theorem B2355779 : Blo 1240438 2355779 := bstep (se 1 (by rfl) ⟨1766834, by rfl⟩ : syracuseStep 2355779 = 3533669) B3533669
theorem B1241667 : Blo 1240438 1241667 := bstep (se 1 (by rfl) ⟨931250, by rfl⟩ : syracuseStep 1241667 = 1862501) B1862501
theorem B1241683 : Blo 1240438 1241683 := bstep (se 1 (by rfl) ⟨931262, by rfl⟩ : syracuseStep 1241683 = 1862525) B1862525
theorem B1241699 : Blo 1240438 1241699 := bstep (se 1 (by rfl) ⟨931274, by rfl⟩ : syracuseStep 1241699 = 1862549) B1862549
theorem B2093681 : Blo 1240438 2093681 := bstep (se 2 (by rfl) ⟨785130, by rfl⟩ : syracuseStep 2093681 = 1570261) B1570261
theorem B1241715 : Blo 1240438 1241715 := bstep (se 1 (by rfl) ⟨931286, by rfl⟩ : syracuseStep 1241715 = 1862573) B1862573
theorem B1241731 : Blo 1240438 1241731 := bstep (se 1 (by rfl) ⟨931298, by rfl⟩ : syracuseStep 1241731 = 1862597) B1862597
theorem B1241747 : Blo 1240438 1241747 := bstep (se 1 (by rfl) ⟨931310, by rfl⟩ : syracuseStep 1241747 = 1862621) B1862621
theorem B1241763 : Blo 1240438 1241763 := bstep (se 1 (by rfl) ⟨931322, by rfl⟩ : syracuseStep 1241763 = 1862645) B1862645
theorem B1241779 : Blo 1240438 1241779 := bstep (se 1 (by rfl) ⟨931334, by rfl⟩ : syracuseStep 1241779 = 1862669) B1862669
theorem B1241795 : Blo 1240438 1241795 := bstep (se 1 (by rfl) ⟨931346, by rfl⟩ : syracuseStep 1241795 = 1862693) B1862693
theorem B1397443 : Blo 1240438 1397443 := bstep (se 1 (by rfl) ⟨1048082, by rfl⟩ : syracuseStep 1397443 = 2096165) B2096165
theorem B1241811 : Blo 1240438 1241811 := bstep (se 1 (by rfl) ⟨931358, by rfl⟩ : syracuseStep 1241811 = 1862717) B1862717
theorem B1241827 : Blo 1240438 1241827 := bstep (se 1 (by rfl) ⟨931370, by rfl⟩ : syracuseStep 1241827 = 1862741) B1862741
theorem B2093809 : Blo 1240438 2093809 := bstep (se 2 (by rfl) ⟨785178, by rfl⟩ : syracuseStep 2093809 = 1570357) B1570357
theorem B3142385 : Blo 1240438 3142385 := bstep (se 2 (by rfl) ⟨1178394, by rfl⟩ : syracuseStep 3142385 = 2356789) B2356789
theorem B1241843 : Blo 1240438 1241843 := bstep (se 1 (by rfl) ⟨931382, by rfl⟩ : syracuseStep 1241843 = 1862765) B1862765
theorem B1241859 : Blo 1240438 1241859 := bstep (se 1 (by rfl) ⟨931394, by rfl⟩ : syracuseStep 1241859 = 1862789) B1862789
theorem B4190993 : Blo 1240438 4190993 := bstep (se 2 (by rfl) ⟨1571622, by rfl⟩ : syracuseStep 4190993 = 3143245) B3143245
theorem B2093843 : Blo 1240438 2093843 := bstep (se 1 (by rfl) ⟨1570382, by rfl⟩ : syracuseStep 2093843 = 3140765) B3140765
theorem B1241875 : Blo 1240438 1241875 := bstep (se 1 (by rfl) ⟨931406, by rfl⟩ : syracuseStep 1241875 = 1862813) B1862813
theorem B3142435 : Blo 1240438 3142435 := bstep (se 1 (by rfl) ⟨2356826, by rfl⟩ : syracuseStep 3142435 = 4713653) B4713653
theorem B1241891 : Blo 1240438 1241891 := bstep (se 1 (by rfl) ⟨931418, by rfl⟩ : syracuseStep 1241891 = 1862837) B1862837
theorem B1241907 : Blo 1240438 1241907 := bstep (se 1 (by rfl) ⟨931430, by rfl⟩ : syracuseStep 1241907 = 1862861) B1862861
theorem B1241923 : Blo 1240438 1241923 := bstep (se 1 (by rfl) ⟨931442, by rfl⟩ : syracuseStep 1241923 = 1862885) B1862885
theorem B1766225 : Blo 1240438 1766225 := bstep (se 2 (by rfl) ⟨662334, by rfl⟩ : syracuseStep 1766225 = 1324669) B1324669
theorem B1241939 : Blo 1240438 1241939 := bstep (se 1 (by rfl) ⟨931454, by rfl⟩ : syracuseStep 1241939 = 1862909) B1862909
theorem B1397587 : Blo 1240438 1397587 := bstep (se 1 (by rfl) ⟨1048190, by rfl⟩ : syracuseStep 1397587 = 2096381) B2096381
theorem B2356067 : Blo 1240438 2356067 := bstep (se 1 (by rfl) ⟨1767050, by rfl⟩ : syracuseStep 2356067 = 3534101) B3534101
theorem B1241955 : Blo 1240438 1241955 := bstep (se 1 (by rfl) ⟨931466, by rfl⟩ : syracuseStep 1241955 = 1862933) B1862933
theorem B1241971 : Blo 1240438 1241971 := bstep (se 1 (by rfl) ⟨931478, by rfl⟩ : syracuseStep 1241971 = 1862957) B1862957
theorem B1241987 : Blo 1240438 1241987 := bstep (se 1 (by rfl) ⟨931490, by rfl⟩ : syracuseStep 1241987 = 1862981) B1862981
theorem B2093971 : Blo 1240438 2093971 := bstep (se 1 (by rfl) ⟨1570478, by rfl⟩ : syracuseStep 2093971 = 3140957) B3140957
theorem B1242003 : Blo 1240438 1242003 := bstep (se 1 (by rfl) ⟨931502, by rfl⟩ : syracuseStep 1242003 = 1863005) B1863005
theorem B1242019 : Blo 1240438 1242019 := bstep (se 1 (by rfl) ⟨931514, by rfl⟩ : syracuseStep 1242019 = 1863029) B1863029
theorem B3142577 : Blo 1240438 3142577 := bstep (se 2 (by rfl) ⟨1178466, by rfl⟩ : syracuseStep 3142577 = 2356933) B2356933
theorem B1242035 : Blo 1240438 1242035 := bstep (se 1 (by rfl) ⟨931526, by rfl⟩ : syracuseStep 1242035 = 1863053) B1863053
theorem B1242051 : Blo 1240438 1242051 := bstep (se 1 (by rfl) ⟨931538, by rfl⟩ : syracuseStep 1242051 = 1863077) B1863077
theorem B2651089 : Blo 1240438 2651089 := bstep (se 2 (by rfl) ⟨994158, by rfl⟩ : syracuseStep 2651089 = 1988317) B1988317
theorem B1242067 : Blo 1240438 1242067 := bstep (se 1 (by rfl) ⟨931550, by rfl⟩ : syracuseStep 1242067 = 1863101) B1863101
theorem B1242083 : Blo 1240438 1242083 := bstep (se 1 (by rfl) ⟨931562, by rfl⟩ : syracuseStep 1242083 = 1863125) B1863125
theorem B1397731 : Blo 1240438 1397731 := bstep (se 1 (by rfl) ⟨1048298, by rfl⟩ : syracuseStep 1397731 = 2096597) B2096597
theorem B8950769 : Blo 1240438 8950769 := bstep (se 2 (by rfl) ⟨3356538, by rfl⟩ : syracuseStep 8950769 = 6713077) B6713077
theorem B1242099 : Blo 1240438 1242099 := bstep (se 1 (by rfl) ⟨931574, by rfl⟩ : syracuseStep 1242099 = 1863149) B1863149
theorem B1242115 : Blo 1240438 1242115 := bstep (se 1 (by rfl) ⟨931586, by rfl⟩ : syracuseStep 1242115 = 1863173) B1863173
theorem B1242131 : Blo 1240438 1242131 := bstep (se 1 (by rfl) ⟨931598, by rfl⟩ : syracuseStep 1242131 = 1863197) B1863197
theorem B2094113 : Blo 1240438 2094113 := bstep (se 2 (by rfl) ⟨785292, by rfl⟩ : syracuseStep 2094113 = 1570585) B1570585
theorem B1242147 : Blo 1240438 1242147 := bstep (se 1 (by rfl) ⟨931610, by rfl⟩ : syracuseStep 1242147 = 1863221) B1863221
theorem B1242163 : Blo 1240438 1242163 := bstep (se 1 (by rfl) ⟨931622, by rfl⟩ : syracuseStep 1242163 = 1863245) B1863245
theorem B1242179 : Blo 1240438 1242179 := bstep (se 1 (by rfl) ⟨931634, by rfl⟩ : syracuseStep 1242179 = 1863269) B1863269
theorem B4715597 : Blo 1240438 4715597 := bstep (se 3 (by rfl) ⟨884174, by rfl⟩ : syracuseStep 4715597 = 1768349) B1768349
theorem B1242195 : Blo 1240438 1242195 := bstep (se 1 (by rfl) ⟨931646, by rfl⟩ : syracuseStep 1242195 = 1863293) B1863293
theorem B1242211 : Blo 1240438 1242211 := bstep (se 1 (by rfl) ⟨931658, by rfl⟩ : syracuseStep 1242211 = 1863317) B1863317
theorem B1242227 : Blo 1240438 1242227 := bstep (se 1 (by rfl) ⟨931670, by rfl⟩ : syracuseStep 1242227 = 1863341) B1863341
theorem B1242243 : Blo 1240438 1242243 := bstep (se 1 (by rfl) ⟨931682, by rfl⟩ : syracuseStep 1242243 = 1863365) B1863365
theorem B1242259 : Blo 1240438 1242259 := bstep (se 1 (by rfl) ⟨931694, by rfl⟩ : syracuseStep 1242259 = 1863389) B1863389
theorem B2094241 : Blo 1240438 2094241 := bstep (se 2 (by rfl) ⟨785340, by rfl⟩ : syracuseStep 2094241 = 1570681) B1570681
theorem B1242275 : Blo 1240438 1242275 := bstep (se 1 (by rfl) ⟨931706, by rfl⟩ : syracuseStep 1242275 = 1863413) B1863413
theorem B1242291 : Blo 1240438 1242291 := bstep (se 1 (by rfl) ⟨931718, by rfl⟩ : syracuseStep 1242291 = 1863437) B1863437
theorem B2094275 : Blo 1240438 2094275 := bstep (se 1 (by rfl) ⟨1570706, by rfl⟩ : syracuseStep 2094275 = 3141413) B3141413
theorem B1242307 : Blo 1240438 1242307 := bstep (se 1 (by rfl) ⟨931730, by rfl⟩ : syracuseStep 1242307 = 1863461) B1863461
theorem B1242323 : Blo 1240438 1242323 := bstep (se 1 (by rfl) ⟨931742, by rfl⟩ : syracuseStep 1242323 = 1863485) B1863485
theorem B10073315 : Blo 1240438 10073315 := bstep (se 1 (by rfl) ⟨7554986, by rfl⟩ : syracuseStep 10073315 = 15109973) B15109973
theorem B1242339 : Blo 1240438 1242339 := bstep (se 1 (by rfl) ⟨931754, by rfl⟩ : syracuseStep 1242339 = 1863509) B1863509
theorem B1242355 : Blo 1240438 1242355 := bstep (se 1 (by rfl) ⟨931766, by rfl⟩ : syracuseStep 1242355 = 1863533) B1863533
theorem B1987843 : Blo 1240438 1987843 := bstep (se 1 (by rfl) ⟨1490882, by rfl⟩ : syracuseStep 1987843 = 2981765) B2981765
theorem B1242371 : Blo 1240438 1242371 := bstep (se 1 (by rfl) ⟨931778, by rfl⟩ : syracuseStep 1242371 = 1863557) B1863557
theorem B1242387 : Blo 1240438 1242387 := bstep (se 1 (by rfl) ⟨931790, by rfl⟩ : syracuseStep 1242387 = 1863581) B1863581
theorem B1242403 : Blo 1240438 1242403 := bstep (se 1 (by rfl) ⟨931802, by rfl⟩ : syracuseStep 1242403 = 1863605) B1863605
theorem B4191533 : Blo 1240438 4191533 := bstep (se 3 (by rfl) ⟨785912, by rfl⟩ : syracuseStep 4191533 = 1571825) B1571825
theorem B1570099 : Blo 1240438 1570099 := bstep (se 1 (by rfl) ⟨1177574, by rfl⟩ : syracuseStep 1570099 = 2355149) B2355149
theorem B1242419 : Blo 1240438 1242419 := bstep (se 1 (by rfl) ⟨931814, by rfl⟩ : syracuseStep 1242419 = 1863629) B1863629
theorem B2094403 : Blo 1240438 2094403 := bstep (se 1 (by rfl) ⟨1570802, by rfl⟩ : syracuseStep 2094403 = 3141605) B3141605
theorem B1242435 : Blo 1240438 1242435 := bstep (se 1 (by rfl) ⟨931826, by rfl⟩ : syracuseStep 1242435 = 1863653) B1863653
theorem B4191587 : Blo 1240438 4191587 := bstep (se 1 (by rfl) ⟨3143690, by rfl⟩ : syracuseStep 4191587 = 6287381) B6287381
theorem B1570195 : Blo 1240438 1570195 := bstep (se 1 (by rfl) ⟨1177646, by rfl⟩ : syracuseStep 1570195 = 2355293) B2355293
theorem B3978659 : Blo 1240438 3978659 := bstep (se 1 (by rfl) ⟨2983994, by rfl⟩ : syracuseStep 3978659 = 5967989) B5967989
theorem B5969315 : Blo 1240438 5969315 := bstep (se 1 (by rfl) ⟨4476986, by rfl⟩ : syracuseStep 5969315 = 8953973) B8953973
theorem B2094545 : Blo 1240438 2094545 := bstep (se 2 (by rfl) ⟨785454, by rfl⟩ : syracuseStep 2094545 = 1570909) B1570909
theorem B3536369 : Blo 1240438 3536369 := bstep (se 2 (by rfl) ⟨1326138, by rfl⟩ : syracuseStep 3536369 = 2652277) B2652277
theorem B6280739 : Blo 1240438 6280739 := bstep (se 1 (by rfl) ⟨4710554, by rfl⟩ : syracuseStep 6280739 = 9421109) B9421109
theorem B7960133 : Blo 1240438 7960133 := bstep (se 4 (by rfl) ⟨746262, by rfl⟩ : syracuseStep 7960133 = 1492525) B1492525
theorem B3356237 : Blo 1240438 3356237 := bstep (se 3 (by rfl) ⟨629294, by rfl⟩ : syracuseStep 3356237 = 1258589) B1258589
theorem B5969485 : Blo 1240438 5969485 := bstep (se 3 (by rfl) ⟨1119278, by rfl⟩ : syracuseStep 5969485 = 2238557) B2238557
theorem B2094673 : Blo 1240438 2094673 := bstep (se 2 (by rfl) ⟨785502, by rfl⟩ : syracuseStep 2094673 = 1571005) B1571005
theorem B1791571 : Blo 1240438 1791571 := bstep (se 1 (by rfl) ⟨1343678, by rfl⟩ : syracuseStep 1791571 = 2687357) B2687357
theorem B5035619 : Blo 1240438 5035619 := bstep (se 1 (by rfl) ⟨3776714, by rfl⟩ : syracuseStep 5035619 = 7553429) B7553429
theorem B2791025 : Blo 1240438 2791025 := bstep (se 2 (by rfl) ⟨1046634, by rfl⟩ : syracuseStep 2791025 = 2093269) B2093269
theorem B4191857 : Blo 1240438 4191857 := bstep (se 2 (by rfl) ⟨1571946, by rfl⟩ : syracuseStep 4191857 = 3143893) B3143893
theorem B2094707 : Blo 1240438 2094707 := bstep (se 1 (by rfl) ⟨1571030, by rfl⟩ : syracuseStep 2094707 = 3142061) B3142061
theorem B1676929 : Blo 1240438 1676929 := bstep (se 2 (by rfl) ⟨628848, by rfl⟩ : syracuseStep 1676929 = 1257697) B1257697
theorem B2791043 : Blo 1240438 2791043 := bstep (se 1 (by rfl) ⟨2093282, by rfl⟩ : syracuseStep 2791043 = 4186565) B4186565
theorem B3536561 : Blo 1240438 3536561 := bstep (se 2 (by rfl) ⟨1326210, by rfl⟩ : syracuseStep 3536561 = 2652421) B2652421
theorem B1767091 : Blo 1240438 1767091 := bstep (se 1 (by rfl) ⟨1325318, by rfl⟩ : syracuseStep 1767091 = 2650637) B2650637
theorem B1988291 : Blo 1240438 1988291 := bstep (se 1 (by rfl) ⟨1491218, by rfl⟩ : syracuseStep 1988291 = 2982437) B2982437
theorem B2094835 : Blo 1240438 2094835 := bstep (se 1 (by rfl) ⟨1571126, by rfl⟩ : syracuseStep 2094835 = 3142253) B3142253
theorem B2357009 : Blo 1240438 2357009 := bstep (se 2 (by rfl) ⟨883878, by rfl⟩ : syracuseStep 2357009 = 1767757) B1767757
theorem B1767187 : Blo 1240438 1767187 := bstep (se 1 (by rfl) ⟨1325390, by rfl⟩ : syracuseStep 1767187 = 2650781) B2650781
theorem B14718773 : Blo 1240438 14718773 := bstep (se 5 (by rfl) ⟨689942, by rfl⟩ : syracuseStep 14718773 = 1379885) B1379885
theorem B2094977 : Blo 1240438 2094977 := bstep (se 2 (by rfl) ⟨785616, by rfl⟩ : syracuseStep 2094977 = 1571233) B1571233
theorem B1570691 : Blo 1240438 1570691 := bstep (se 1 (by rfl) ⟨1178018, by rfl⟩ : syracuseStep 1570691 = 2356037) B2356037
theorem B2791313 : Blo 1240438 2791313 := bstep (se 2 (by rfl) ⟨1046742, by rfl⟩ : syracuseStep 2791313 = 2093485) B2093485
theorem B3143569 : Blo 1240438 3143569 := bstep (se 2 (by rfl) ⟨1178838, by rfl⟩ : syracuseStep 3143569 = 2357677) B2357677
theorem B2791331 : Blo 1240438 2791331 := bstep (se 1 (by rfl) ⟨2093498, by rfl⟩ : syracuseStep 2791331 = 4186997) B4186997
theorem B15112163 : Blo 1240438 15112163 := bstep (se 1 (by rfl) ⟨11334122, by rfl⟩ : syracuseStep 15112163 = 22668245) B22668245
theorem B2095105 : Blo 1240438 2095105 := bstep (se 2 (by rfl) ⟨785664, by rfl⟩ : syracuseStep 2095105 = 1571329) B1571329
theorem B5306381 : Blo 1240438 5306381 := bstep (se 3 (by rfl) ⟨994946, by rfl⟩ : syracuseStep 5306381 = 1989893) B1989893
theorem B2095139 : Blo 1240438 2095139 := bstep (se 1 (by rfl) ⟨1571354, by rfl⟩ : syracuseStep 2095139 = 3142709) B3142709
theorem B7952525 : Blo 1240438 7952525 := bstep (se 3 (by rfl) ⟨1491098, by rfl⟩ : syracuseStep 7952525 = 2982197) B2982197
theorem B4192397 : Blo 1240438 4192397 := bstep (se 3 (by rfl) ⟨786074, by rfl⟩ : syracuseStep 4192397 = 1572149) B1572149
theorem B4470947 : Blo 1240438 4470947 := bstep (se 1 (by rfl) ⟨3353210, by rfl⟩ : syracuseStep 4470947 = 6706421) B6706421
theorem B2095267 : Blo 1240438 2095267 := bstep (se 1 (by rfl) ⟨1571450, by rfl⟩ : syracuseStep 2095267 = 3142901) B3142901
theorem B3143843 : Blo 1240438 3143843 := bstep (se 1 (by rfl) ⟨2357882, by rfl⟩ : syracuseStep 3143843 = 4715765) B4715765
theorem B2791601 : Blo 1240438 2791601 := bstep (se 2 (by rfl) ⟨1046850, by rfl⟩ : syracuseStep 2791601 = 2093701) B2093701
theorem B1702067 : Blo 1240438 1702067 := bstep (se 1 (by rfl) ⟨1276550, by rfl⟩ : syracuseStep 1702067 = 2553101) B2553101
theorem B2791619 : Blo 1240438 2791619 := bstep (se 1 (by rfl) ⟨2093714, by rfl⟩ : syracuseStep 2791619 = 4187429) B4187429
theorem B4192451 : Blo 1240438 4192451 := bstep (se 1 (by rfl) ⟨3144338, by rfl⟩ : syracuseStep 4192451 = 6288677) B6288677
theorem B8493283 : Blo 1240438 8493283 := bstep (se 1 (by rfl) ⟨6369962, by rfl⟩ : syracuseStep 8493283 = 12739925) B12739925
theorem B1988849 : Blo 1240438 1988849 := bstep (se 2 (by rfl) ⟨745818, by rfl⟩ : syracuseStep 1988849 = 1491637) B1491637
theorem B6289649 : Blo 1240438 6289649 := bstep (se 2 (by rfl) ⟨2358618, by rfl⟩ : syracuseStep 6289649 = 4717237) B4717237
theorem B1767683 : Blo 1240438 1767683 := bstep (se 1 (by rfl) ⟨1325762, by rfl⟩ : syracuseStep 1767683 = 2651525) B2651525
theorem B2095409 : Blo 1240438 2095409 := bstep (se 2 (by rfl) ⟨785778, by rfl⟩ : syracuseStep 2095409 = 1571557) B1571557
theorem B14129477 : Blo 1240438 14129477 := bstep (se 4 (by rfl) ⟨1324638, by rfl⟩ : syracuseStep 14129477 = 2649277) B2649277
theorem B6281549 : Blo 1240438 6281549 := bstep (se 3 (by rfl) ⟨1177790, by rfl⟩ : syracuseStep 6281549 = 2355581) B2355581
theorem B5036365 : Blo 1240438 5036365 := bstep (se 3 (by rfl) ⟨944318, by rfl⟩ : syracuseStep 5036365 = 1888637) B1888637
theorem B5658979 : Blo 1240438 5658979 := bstep (se 1 (by rfl) ⟨4244234, by rfl⟩ : syracuseStep 5658979 = 8488469) B8488469
theorem B3144035 : Blo 1240438 3144035 := bstep (se 1 (by rfl) ⟨2358026, by rfl⟩ : syracuseStep 3144035 = 4716053) B4716053
theorem B2095537 : Blo 1240438 2095537 := bstep (se 2 (by rfl) ⟨785826, by rfl⟩ : syracuseStep 2095537 = 1571653) B1571653
theorem B2791889 : Blo 1240438 2791889 := bstep (se 2 (by rfl) ⟨1046958, by rfl⟩ : syracuseStep 2791889 = 2093917) B2093917
theorem B1989073 : Blo 1240438 1989073 := bstep (se 2 (by rfl) ⟨745902, by rfl⟩ : syracuseStep 1989073 = 1491805) B1491805
theorem B2095571 : Blo 1240438 2095571 := bstep (se 1 (by rfl) ⟨1571678, by rfl⟩ : syracuseStep 2095571 = 3143357) B3143357
theorem B4192721 : Blo 1240438 4192721 := bstep (se 2 (by rfl) ⟨1572270, by rfl⟩ : syracuseStep 4192721 = 3144541) B3144541
theorem B2791907 : Blo 1240438 2791907 := bstep (se 1 (by rfl) ⟨2093930, by rfl⟩ : syracuseStep 2791907 = 4187861) B4187861
theorem B9427427 : Blo 1240438 9427427 := bstep (se 1 (by rfl) ⟨7070570, by rfl⟩ : syracuseStep 9427427 = 14141141) B14141141
theorem B1989137 : Blo 1240438 1989137 := bstep (se 2 (by rfl) ⟨745926, by rfl⟩ : syracuseStep 1989137 = 1491853) B1491853
theorem B1571395 : Blo 1240438 1571395 := bstep (se 1 (by rfl) ⟨1178546, by rfl⟩ : syracuseStep 1571395 = 2357093) B2357093
theorem B12098117 : Blo 1240438 12098117 := bstep (se 4 (by rfl) ⟨1134198, by rfl⟩ : syracuseStep 12098117 = 2268397) B2268397
theorem B2095699 : Blo 1240438 2095699 := bstep (se 1 (by rfl) ⟨1571774, by rfl⟩ : syracuseStep 2095699 = 3143549) B3143549
theorem B7068293 : Blo 1240438 7068293 := bstep (se 4 (by rfl) ⟨662652, by rfl⟩ : syracuseStep 7068293 = 1325305) B1325305
theorem B1989265 : Blo 1240438 1989265 := bstep (se 2 (by rfl) ⟨745974, by rfl⟩ : syracuseStep 1989265 = 1491949) B1491949
theorem B2357905 : Blo 1240438 2357905 := bstep (se 2 (by rfl) ⟨884214, by rfl⟩ : syracuseStep 2357905 = 1768429) B1768429
theorem B3537553 : Blo 1240438 3537553 := bstep (se 2 (by rfl) ⟨1326582, by rfl⟩ : syracuseStep 3537553 = 2653165) B2653165
theorem B1571491 : Blo 1240438 1571491 := bstep (se 1 (by rfl) ⟨1178618, by rfl⟩ : syracuseStep 1571491 = 2357237) B2357237
theorem B2095841 : Blo 1240438 2095841 := bstep (se 2 (by rfl) ⟨785940, by rfl⟩ : syracuseStep 2095841 = 1571881) B1571881
theorem B4471523 : Blo 1240438 4471523 := bstep (se 1 (by rfl) ⟨3353642, by rfl⟩ : syracuseStep 4471523 = 6707285) B6707285
theorem B2792177 : Blo 1240438 2792177 := bstep (se 2 (by rfl) ⟨1047066, by rfl⟩ : syracuseStep 2792177 = 2094133) B2094133
theorem B2792195 : Blo 1240438 2792195 := bstep (se 1 (by rfl) ⟨2094146, by rfl⟩ : syracuseStep 2792195 = 4188293) B4188293
theorem B1678097 : Blo 1240438 1678097 := bstep (se 2 (by rfl) ⟨629286, by rfl⟩ : syracuseStep 1678097 = 1258573) B1258573
theorem B6716195 : Blo 1240438 6716195 := bstep (se 1 (by rfl) ⟨5037146, by rfl⟩ : syracuseStep 6716195 = 10074293) B10074293
theorem B2358065 : Blo 1240438 2358065 := bstep (se 2 (by rfl) ⟨884274, by rfl⟩ : syracuseStep 2358065 = 1768549) B1768549
theorem B2095969 : Blo 1240438 2095969 := bstep (se 2 (by rfl) ⟨785988, by rfl⟩ : syracuseStep 2095969 = 1571977) B1571977
theorem B14138225 : Blo 1240438 14138225 := bstep (se 2 (by rfl) ⟨5301834, by rfl⟩ : syracuseStep 14138225 = 10603669) B10603669
theorem B1768321 : Blo 1240438 1768321 := bstep (se 2 (by rfl) ⟨663120, by rfl⟩ : syracuseStep 1768321 = 1326241) B1326241
theorem B2096003 : Blo 1240438 2096003 := bstep (se 1 (by rfl) ⟨1572002, by rfl⟩ : syracuseStep 2096003 = 3144005) B3144005
theorem B3537827 : Blo 1240438 3537827 := bstep (se 1 (by rfl) ⟨2653370, by rfl⟩ : syracuseStep 3537827 = 5306741) B5306741
theorem B2096131 : Blo 1240438 2096131 := bstep (se 1 (by rfl) ⟨1572098, by rfl⟩ : syracuseStep 2096131 = 3144197) B3144197
theorem B2792465 : Blo 1240438 2792465 := bstep (se 2 (by rfl) ⟨1047174, by rfl⟩ : syracuseStep 2792465 = 2094349) B2094349
theorem B2792483 : Blo 1240438 2792483 := bstep (se 1 (by rfl) ⟨2094362, by rfl⟩ : syracuseStep 2792483 = 4188725) B4188725
theorem B3538019 : Blo 1240438 3538019 := bstep (se 1 (by rfl) ⟨2653514, by rfl⟩ : syracuseStep 3538019 = 5307029) B5307029
theorem B3775619 : Blo 1240438 3775619 := bstep (se 1 (by rfl) ⟨2831714, by rfl⟩ : syracuseStep 3775619 = 5663429) B5663429
theorem B2096273 : Blo 1240438 2096273 := bstep (se 2 (by rfl) ⟨786102, by rfl⟩ : syracuseStep 2096273 = 1572205) B1572205
theorem B1571987 : Blo 1240438 1571987 := bstep (se 1 (by rfl) ⟨1178990, by rfl⟩ : syracuseStep 1571987 = 2357981) B2357981
theorem B2358467 : Blo 1240438 2358467 := bstep (se 1 (by rfl) ⟨1768850, by rfl⟩ : syracuseStep 2358467 = 3537701) B3537701
theorem B3316945 : Blo 1240438 3316945 := bstep (se 2 (by rfl) ⟨1243854, by rfl⟩ : syracuseStep 3316945 = 2487709) B2487709
theorem B1768657 : Blo 1240438 1768657 := bstep (se 2 (by rfl) ⟨663246, by rfl⟩ : syracuseStep 1768657 = 1326493) B1326493
theorem B6372593 : Blo 1240438 6372593 := bstep (se 2 (by rfl) ⟨2389722, by rfl⟩ : syracuseStep 6372593 = 4779445) B4779445
theorem B2096401 : Blo 1240438 2096401 := bstep (se 2 (by rfl) ⟨786150, by rfl⟩ : syracuseStep 2096401 = 1572301) B1572301
theorem B7068977 : Blo 1240438 7068977 := bstep (se 2 (by rfl) ⟨2650866, by rfl⟩ : syracuseStep 7068977 = 5301733) B5301733
theorem B2792753 : Blo 1240438 2792753 := bstep (se 2 (by rfl) ⟨1047282, by rfl⟩ : syracuseStep 2792753 = 2094565) B2094565
theorem B2096435 : Blo 1240438 2096435 := bstep (se 1 (by rfl) ⟨1572326, by rfl⟩ : syracuseStep 2096435 = 3144653) B3144653
theorem B2792771 : Blo 1240438 2792771 := bstep (se 1 (by rfl) ⟨2094578, by rfl⟩ : syracuseStep 2792771 = 4189157) B4189157
theorem B1326467 : Blo 1240438 1326467 := bstep (se 1 (by rfl) ⟨994850, by rfl⟩ : syracuseStep 1326467 = 1989701) B1989701
theorem B2096563 : Blo 1240438 2096563 := bstep (se 1 (by rfl) ⟨1572422, by rfl⟩ : syracuseStep 2096563 = 3144845) B3144845
theorem B1678897 : Blo 1240438 1678897 := bstep (se 2 (by rfl) ⟨629586, by rfl⟩ : syracuseStep 1678897 = 1259173) B1259173
theorem B2793041 : Blo 1240438 2793041 := bstep (se 2 (by rfl) ⟨1047390, by rfl⟩ : syracuseStep 2793041 = 2094781) B2094781
theorem B2793059 : Blo 1240438 2793059 := bstep (se 1 (by rfl) ⟨2094794, by rfl⟩ : syracuseStep 2793059 = 4189589) B4189589
theorem B1679059 : Blo 1240438 1679059 := bstep (se 1 (by rfl) ⟨1259294, by rfl⟩ : syracuseStep 1679059 = 2518589) B2518589
theorem B4710221 : Blo 1240438 4710221 := bstep (se 3 (by rfl) ⟨883166, by rfl⟩ : syracuseStep 4710221 = 1766333) B1766333
theorem B4030307 : Blo 1240438 4030307 := bstep (se 1 (by rfl) ⟨3022730, by rfl⟩ : syracuseStep 4030307 = 6045461) B6045461
theorem B2793329 : Blo 1240438 2793329 := bstep (se 2 (by rfl) ⟨1047498, by rfl⟩ : syracuseStep 2793329 = 2094997) B2094997
theorem B2793347 : Blo 1240438 2793347 := bstep (se 1 (by rfl) ⟨2095010, by rfl⟩ : syracuseStep 2793347 = 4190021) B4190021
theorem B6807473 : Blo 1240438 6807473 := bstep (se 2 (by rfl) ⟨2552802, by rfl⟩ : syracuseStep 6807473 = 5105605) B5105605
theorem B11321315 : Blo 1240438 11321315 := bstep (se 1 (by rfl) ⟨8490986, by rfl⟩ : syracuseStep 11321315 = 16981973) B16981973
theorem B2793473 : Blo 1240438 2793473 := bstep (se 2 (by rfl) ⟨1047552, by rfl⟩ : syracuseStep 2793473 = 2095105) B2095105
theorem B6127795 : Blo 1240438 6127795 := bstep (se 1 (by rfl) ⟨4595846, by rfl⟩ : syracuseStep 6127795 = 9191693) B9191693
theorem B2982091 : Blo 1240438 2982091 := bstep (se 1 (by rfl) ⟨2236568, by rfl⟩ : syracuseStep 2982091 = 4473137) B4473137
theorem B2793689 : Blo 1240438 2793689 := bstep (se 2 (by rfl) ⟨1047633, by rfl⟩ : syracuseStep 2793689 = 2095267) B2095267
theorem B4710707 : Blo 1240438 4710707 := bstep (se 1 (by rfl) ⟨3533030, by rfl⟩ : syracuseStep 4710707 = 7066061) B7066061
theorem B2793779 : Blo 1240438 2793779 := bstep (se 1 (by rfl) ⟨2095334, by rfl⟩ : syracuseStep 2793779 = 4190669) B4190669
theorem B2793815 : Blo 1240438 2793815 := bstep (se 1 (by rfl) ⟨2095361, by rfl⟩ : syracuseStep 2793815 = 4190723) B4190723
theorem B10068317 : Blo 1240438 10068317 := bstep (se 3 (by rfl) ⟨1887809, by rfl⟩ : syracuseStep 10068317 = 3775619) B3775619
theorem B7545305 : Blo 1240438 7545305 := bstep (se 2 (by rfl) ⟨2829489, by rfl⟩ : syracuseStep 7545305 = 5658979) B5658979
theorem B4538845 : Blo 1240438 4538845 := bstep (se 3 (by rfl) ⟨851033, by rfl⟩ : syracuseStep 4538845 = 1702067) B1702067
theorem B2793995 : Blo 1240438 2793995 := bstep (se 1 (by rfl) ⟨2095496, by rfl⟩ : syracuseStep 2793995 = 4190993) B4190993
theorem B64471565 : Blo 1240438 64471565 := bstep (se 3 (by rfl) ⟨12088418, by rfl⟩ : syracuseStep 64471565 = 24176837) B24176837
theorem B7955009 : Blo 1240438 7955009 := bstep (se 2 (by rfl) ⟨2983128, by rfl⟩ : syracuseStep 7955009 = 5966257) B5966257
theorem B2794049 : Blo 1240438 2794049 := bstep (se 2 (by rfl) ⟨1047768, by rfl⟩ : syracuseStep 2794049 = 2095537) B2095537
theorem B8946449 : Blo 1240438 8946449 := bstep (se 2 (by rfl) ⟨3354918, by rfl⟩ : syracuseStep 8946449 = 6709837) B6709837
theorem B2794265 : Blo 1240438 2794265 := bstep (se 2 (by rfl) ⟨1047849, by rfl⟩ : syracuseStep 2794265 = 2095699) B2095699
theorem B2982707 : Blo 1240438 2982707 := bstep (se 1 (by rfl) ⟨2237030, by rfl⟩ : syracuseStep 2982707 = 4474061) B4474061
theorem B6800203 : Blo 1240438 6800203 := bstep (se 1 (by rfl) ⟨5100152, by rfl⟩ : syracuseStep 6800203 = 10200305) B10200305
theorem B4088665 : Blo 1240438 4088665 := bstep (se 2 (by rfl) ⟨1533249, by rfl⟩ : syracuseStep 4088665 = 3066499) B3066499
theorem B2794355 : Blo 1240438 2794355 := bstep (se 1 (by rfl) ⟨2095766, by rfl⟩ : syracuseStep 2794355 = 4191533) B4191533
theorem B2794391 : Blo 1240438 2794391 := bstep (se 1 (by rfl) ⟨2095793, by rfl⟩ : syracuseStep 2794391 = 4191587) B4191587
theorem B4187159 : Blo 1240438 4187159 := bstep (se 1 (by rfl) ⟨3140369, by rfl⟩ : syracuseStep 4187159 = 6280739) B6280739
theorem B8946733 : Blo 1240438 8946733 := bstep (se 3 (by rfl) ⟨1677512, by rfl⟩ : syracuseStep 8946733 = 3355025) B3355025
theorem B2237491 : Blo 1240438 2237491 := bstep (se 1 (by rfl) ⟨1678118, by rfl⟩ : syracuseStep 2237491 = 3356237) B3356237
theorem B1860683 : Blo 1240438 1860683 := bstep (se 1 (by rfl) ⟨1395512, by rfl⟩ : syracuseStep 1860683 = 2791025) B2791025
theorem B2794571 : Blo 1240438 2794571 := bstep (se 1 (by rfl) ⟨2095928, by rfl⟩ : syracuseStep 2794571 = 4191857) B4191857
theorem B1860695 : Blo 1240438 1860695 := bstep (se 1 (by rfl) ⟨1395521, by rfl⟩ : syracuseStep 1860695 = 2791043) B2791043
theorem B8954981 : Blo 1240438 8954981 := bstep (se 4 (by rfl) ⟨839529, by rfl⟩ : syracuseStep 8954981 = 1679059) B1679059
theorem B2794625 : Blo 1240438 2794625 := bstep (se 2 (by rfl) ⟨1047984, by rfl⟩ : syracuseStep 2794625 = 2095969) B2095969
theorem B1860761 : Blo 1240438 1860761 := bstep (se 2 (by rfl) ⟨697785, by rfl⟩ : syracuseStep 1860761 = 1395571) B1395571
theorem B1860875 : Blo 1240438 1860875 := bstep (se 1 (by rfl) ⟨1395656, by rfl⟩ : syracuseStep 1860875 = 2791313) B2791313
theorem B1860887 : Blo 1240438 1860887 := bstep (se 1 (by rfl) ⟨1395665, by rfl⟩ : syracuseStep 1860887 = 2791331) B2791331
theorem B1860953 : Blo 1240438 1860953 := bstep (se 2 (by rfl) ⟨697857, by rfl⟩ : syracuseStep 1860953 = 1395715) B1395715
theorem B2794841 : Blo 1240438 2794841 := bstep (se 2 (by rfl) ⟨1048065, by rfl⟩ : syracuseStep 2794841 = 2096131) B2096131
theorem B11937125 : Blo 1240438 11937125 := bstep (se 4 (by rfl) ⟨1119105, by rfl⟩ : syracuseStep 11937125 = 2238211) B2238211
theorem B5301683 : Blo 1240438 5301683 := bstep (se 1 (by rfl) ⟨3976262, by rfl⟩ : syracuseStep 5301683 = 7952525) B7952525
theorem B2794931 : Blo 1240438 2794931 := bstep (se 1 (by rfl) ⟨2096198, by rfl⟩ : syracuseStep 2794931 = 4192397) B4192397
theorem B1861067 : Blo 1240438 1861067 := bstep (se 1 (by rfl) ⟨1395800, by rfl⟩ : syracuseStep 1861067 = 2791601) B2791601
theorem B1861079 : Blo 1240438 1861079 := bstep (se 1 (by rfl) ⟨1395809, by rfl⟩ : syracuseStep 1861079 = 2791619) B2791619
theorem B2794967 : Blo 1240438 2794967 := bstep (se 1 (by rfl) ⟨2096225, by rfl⟩ : syracuseStep 2794967 = 4192451) B4192451
theorem B32261645 : Blo 1240438 32261645 := bstep (se 3 (by rfl) ⟨6049058, by rfl⟩ : syracuseStep 32261645 = 12098117) B12098117
theorem B21227021 : Blo 1240438 21227021 := bstep (se 3 (by rfl) ⟨3980066, by rfl⟩ : syracuseStep 21227021 = 7960133) B7960133
theorem B1861145 : Blo 1240438 1861145 := bstep (se 2 (by rfl) ⟨697929, by rfl⟩ : syracuseStep 1861145 = 1395859) B1395859
theorem B10602029 : Blo 1240438 10602029 := bstep (se 3 (by rfl) ⟨1987880, by rfl⟩ : syracuseStep 10602029 = 3975761) B3975761
theorem B4187699 : Blo 1240438 4187699 := bstep (se 1 (by rfl) ⟨3140774, by rfl⟩ : syracuseStep 4187699 = 6281549) B6281549
theorem B2983475 : Blo 1240438 2983475 := bstep (se 1 (by rfl) ⟨2237606, by rfl⟩ : syracuseStep 2983475 = 4475213) B4475213
theorem B13428317 : Blo 1240438 13428317 := bstep (se 3 (by rfl) ⟨2517809, by rfl⟩ : syracuseStep 13428317 = 5035619) B5035619
theorem B1861259 : Blo 1240438 1861259 := bstep (se 1 (by rfl) ⟨1395944, by rfl⟩ : syracuseStep 1861259 = 2791889) B2791889
theorem B2795147 : Blo 1240438 2795147 := bstep (se 1 (by rfl) ⟨2096360, by rfl⟩ : syracuseStep 2795147 = 4192721) B4192721
theorem B1861271 : Blo 1240438 1861271 := bstep (se 1 (by rfl) ⟨1395953, by rfl⟩ : syracuseStep 1861271 = 2791907) B2791907
theorem B6284951 : Blo 1240438 6284951 := bstep (se 1 (by rfl) ⟨4713713, by rfl⟩ : syracuseStep 6284951 = 9427427) B9427427
theorem B2795201 : Blo 1240438 2795201 := bstep (se 2 (by rfl) ⟨1048200, by rfl⟩ : syracuseStep 2795201 = 2096401) B2096401
theorem B1861337 : Blo 1240438 1861337 := bstep (se 2 (by rfl) ⟨698001, by rfl⟩ : syracuseStep 1861337 = 1396003) B1396003
theorem B4712195 : Blo 1240438 4712195 := bstep (se 1 (by rfl) ⟨3534146, by rfl⟩ : syracuseStep 4712195 = 7068293) B7068293
theorem B9430829 : Blo 1240438 9430829 := bstep (se 3 (by rfl) ⟨1768280, by rfl⟩ : syracuseStep 9430829 = 3536561) B3536561
theorem B4187969 : Blo 1240438 4187969 := bstep (se 2 (by rfl) ⟨1570488, by rfl⟩ : syracuseStep 4187969 = 3140977) B3140977
theorem B1861451 : Blo 1240438 1861451 := bstep (se 1 (by rfl) ⟨1396088, by rfl⟩ : syracuseStep 1861451 = 2792177) B2792177
theorem B1861463 : Blo 1240438 1861463 := bstep (se 1 (by rfl) ⟨1396097, by rfl⟩ : syracuseStep 1861463 = 2792195) B2792195
theorem B5662553 : Blo 1240438 5662553 := bstep (se 2 (by rfl) ⟨2123457, by rfl⟩ : syracuseStep 5662553 = 4246915) B4246915
theorem B1861529 : Blo 1240438 1861529 := bstep (se 2 (by rfl) ⟨698073, by rfl⟩ : syracuseStep 1861529 = 1396147) B1396147
theorem B2795417 : Blo 1240438 2795417 := bstep (se 2 (by rfl) ⟨1048281, by rfl⟩ : syracuseStep 2795417 = 2096563) B2096563
theorem B1861643 : Blo 1240438 1861643 := bstep (se 1 (by rfl) ⟨1396232, by rfl⟩ : syracuseStep 1861643 = 2792465) B2792465
theorem B1861655 : Blo 1240438 1861655 := bstep (se 1 (by rfl) ⟨1396241, by rfl⟩ : syracuseStep 1861655 = 2792483) B2792483
theorem B4474925 : Blo 1240438 4474925 := bstep (se 3 (by rfl) ⟨839048, by rfl⟩ : syracuseStep 4474925 = 1678097) B1678097
theorem B2238529 : Blo 1240438 2238529 := bstep (se 2 (by rfl) ⟨839448, by rfl⟩ : syracuseStep 2238529 = 1678897) B1678897
theorem B1861721 : Blo 1240438 1861721 := bstep (se 2 (by rfl) ⟨698145, by rfl⟩ : syracuseStep 1861721 = 1396291) B1396291
theorem B30214295 : Blo 1240438 30214295 := bstep (se 1 (by rfl) ⟨22660721, by rfl⟩ : syracuseStep 30214295 = 45321443) B45321443
theorem B4712651 : Blo 1240438 4712651 := bstep (se 1 (by rfl) ⟨3534488, by rfl⟩ : syracuseStep 4712651 = 7068977) B7068977
theorem B1861835 : Blo 1240438 1861835 := bstep (se 1 (by rfl) ⟨1396376, by rfl⟩ : syracuseStep 1861835 = 2792753) B2792753
theorem B9423053 : Blo 1240438 9423053 := bstep (se 3 (by rfl) ⟨1766822, by rfl⟩ : syracuseStep 9423053 = 3533645) B3533645
theorem B1861847 : Blo 1240438 1861847 := bstep (se 1 (by rfl) ⟨1396385, by rfl⟩ : syracuseStep 1861847 = 2792771) B2792771
theorem B5662993 : Blo 1240438 5662993 := bstep (se 2 (by rfl) ⟨2123622, by rfl⟩ : syracuseStep 5662993 = 4247245) B4247245
theorem B1861913 : Blo 1240438 1861913 := bstep (se 2 (by rfl) ⟨698217, by rfl⟩ : syracuseStep 1861913 = 1396435) B1396435
theorem B4188509 : Blo 1240438 4188509 := bstep (se 3 (by rfl) ⟨785345, by rfl⟩ : syracuseStep 4188509 = 1570691) B1570691
theorem B1862027 : Blo 1240438 1862027 := bstep (se 1 (by rfl) ⟨1396520, by rfl⟩ : syracuseStep 1862027 = 2793041) B2793041
theorem B4712849 : Blo 1240438 4712849 := bstep (se 2 (by rfl) ⟨1767318, by rfl⟩ : syracuseStep 4712849 = 3534637) B3534637
theorem B1862039 : Blo 1240438 1862039 := bstep (se 1 (by rfl) ⟨1396529, by rfl⟩ : syracuseStep 1862039 = 2793059) B2793059
theorem B1862105 : Blo 1240438 1862105 := bstep (se 2 (by rfl) ⟨698289, by rfl⟩ : syracuseStep 1862105 = 1396579) B1396579
theorem B5966297 : Blo 1240438 5966297 := bstep (se 2 (by rfl) ⟨2237361, by rfl⟩ : syracuseStep 5966297 = 4474723) B4474723
theorem B3140147 : Blo 1240438 3140147 := bstep (se 1 (by rfl) ⟨2355110, by rfl⟩ : syracuseStep 3140147 = 4710221) B4710221
theorem B1862219 : Blo 1240438 1862219 := bstep (se 1 (by rfl) ⟨1396664, by rfl⟩ : syracuseStep 1862219 = 2793329) B2793329
theorem B1862231 : Blo 1240438 1862231 := bstep (se 1 (by rfl) ⟨1396673, by rfl⟩ : syracuseStep 1862231 = 2793347) B2793347
theorem B7547543 : Blo 1240438 7547543 := bstep (se 1 (by rfl) ⟨5660657, by rfl⟩ : syracuseStep 7547543 = 11321315) B11321315
theorem B1862297 : Blo 1240438 1862297 := bstep (se 2 (by rfl) ⟨698361, by rfl⟩ : syracuseStep 1862297 = 1396723) B1396723
theorem B9423539 : Blo 1240438 9423539 := bstep (se 1 (by rfl) ⟨7067654, by rfl⟩ : syracuseStep 9423539 = 14135309) B14135309
theorem B1862411 : Blo 1240438 1862411 := bstep (se 1 (by rfl) ⟨1396808, by rfl⟩ : syracuseStep 1862411 = 2793617) B2793617
theorem B1862423 : Blo 1240438 1862423 := bstep (se 1 (by rfl) ⟨1396817, by rfl⟩ : syracuseStep 1862423 = 2793635) B2793635
theorem B1395499 : Blo 1240438 1395499 := bstep (se 1 (by rfl) ⟨1046624, by rfl⟩ : syracuseStep 1395499 = 2093249) B2093249
theorem B3140441 : Blo 1240438 3140441 := bstep (se 2 (by rfl) ⟨1177665, by rfl⟩ : syracuseStep 3140441 = 2355331) B2355331
theorem B1862489 : Blo 1240438 1862489 := bstep (se 2 (by rfl) ⟨698433, by rfl⟩ : syracuseStep 1862489 = 1396867) B1396867
theorem B1395607 : Blo 1240438 1395607 := bstep (se 1 (by rfl) ⟨1046705, by rfl⟩ : syracuseStep 1395607 = 2093411) B2093411
theorem B7162775 : Blo 1240438 7162775 := bstep (se 1 (by rfl) ⟨5372081, by rfl⟩ : syracuseStep 7162775 = 10744163) B10744163
theorem B2984897 : Blo 1240438 2984897 := bstep (se 2 (by rfl) ⟨1119336, by rfl⟩ : syracuseStep 2984897 = 2238673) B2238673
theorem B1862603 : Blo 1240438 1862603 := bstep (se 1 (by rfl) ⟨1396952, by rfl⟩ : syracuseStep 1862603 = 2793905) B2793905
theorem B1862615 : Blo 1240438 1862615 := bstep (se 1 (by rfl) ⟨1396961, by rfl⟩ : syracuseStep 1862615 = 2793923) B2793923
theorem B11324377 : Blo 1240438 11324377 := bstep (se 2 (by rfl) ⟨4246641, by rfl⟩ : syracuseStep 11324377 = 8493283) B8493283
theorem B4779011 : Blo 1240438 4779011 := bstep (se 1 (by rfl) ⟨3584258, by rfl⟩ : syracuseStep 4779011 = 7168517) B7168517
theorem B1862681 : Blo 1240438 1862681 := bstep (se 2 (by rfl) ⟨698505, by rfl⟩ : syracuseStep 1862681 = 1397011) B1397011
theorem B1395787 : Blo 1240438 1395787 := bstep (se 1 (by rfl) ⟨1046840, by rfl⟩ : syracuseStep 1395787 = 2093681) B2093681
theorem B1862795 : Blo 1240438 1862795 := bstep (se 1 (by rfl) ⟨1397096, by rfl⟩ : syracuseStep 1862795 = 2794193) B2794193
theorem B4713623 : Blo 1240438 4713623 := bstep (se 1 (by rfl) ⟨3535217, by rfl⟩ : syracuseStep 4713623 = 7070435) B7070435
theorem B1862807 : Blo 1240438 1862807 := bstep (se 1 (by rfl) ⟨1397105, by rfl⟩ : syracuseStep 1862807 = 2794211) B2794211
theorem B7072919 : Blo 1240438 7072919 := bstep (se 1 (by rfl) ⟨5304689, by rfl⟩ : syracuseStep 7072919 = 10609379) B10609379
theorem B1395895 : Blo 1240438 1395895 := bstep (se 1 (by rfl) ⟨1046921, by rfl⟩ : syracuseStep 1395895 = 2093843) B2093843
theorem B1862873 : Blo 1240438 1862873 := bstep (se 2 (by rfl) ⟨698577, by rfl⟩ : syracuseStep 1862873 = 1397155) B1397155
theorem B5967179 : Blo 1240438 5967179 := bstep (se 1 (by rfl) ⟨4475384, by rfl⟩ : syracuseStep 5967179 = 8950769) B8950769
theorem B1862987 : Blo 1240438 1862987 := bstep (se 1 (by rfl) ⟨1397240, by rfl⟩ : syracuseStep 1862987 = 2794481) B2794481
theorem B1862999 : Blo 1240438 1862999 := bstep (se 1 (by rfl) ⟨1397249, by rfl⟩ : syracuseStep 1862999 = 2794499) B2794499
theorem B4713821 : Blo 1240438 4713821 := bstep (se 3 (by rfl) ⟨883841, by rfl⟩ : syracuseStep 4713821 = 1767683) B1767683
theorem B1396075 : Blo 1240438 1396075 := bstep (se 1 (by rfl) ⟨1047056, by rfl⟩ : syracuseStep 1396075 = 2094113) B2094113
theorem B1240439 : Blo 1240438 1240439 := bstep (se 1 (by rfl) ⟨930329, by rfl⟩ : syracuseStep 1240439 = 1860659) B1860659
theorem B6892931 : Blo 1240438 6892931 := bstep (se 1 (by rfl) ⟨5169698, by rfl⟩ : syracuseStep 6892931 = 10339397) B10339397
theorem B1240459 : Blo 1240438 1240459 := bstep (se 1 (by rfl) ⟨930344, by rfl⟩ : syracuseStep 1240459 = 1860689) B1860689
theorem B1240471 : Blo 1240438 1240471 := bstep (se 1 (by rfl) ⟨930353, by rfl⟩ : syracuseStep 1240471 = 1860707) B1860707
theorem B4779415 : Blo 1240438 4779415 := bstep (se 1 (by rfl) ⟨3584561, by rfl⟩ : syracuseStep 4779415 = 7169123) B7169123
theorem B1863065 : Blo 1240438 1863065 := bstep (se 2 (by rfl) ⟨698649, by rfl⟩ : syracuseStep 1863065 = 1397299) B1397299
theorem B1240491 : Blo 1240438 1240491 := bstep (se 1 (by rfl) ⟨930368, by rfl⟩ : syracuseStep 1240491 = 1860737) B1860737
theorem B1240503 : Blo 1240438 1240503 := bstep (se 1 (by rfl) ⟨930377, by rfl⟩ : syracuseStep 1240503 = 1860755) B1860755
theorem B3534283 : Blo 1240438 3534283 := bstep (se 1 (by rfl) ⟨2650712, by rfl⟩ : syracuseStep 3534283 = 5301425) B5301425
theorem B1240523 : Blo 1240438 1240523 := bstep (se 1 (by rfl) ⟨930392, by rfl⟩ : syracuseStep 1240523 = 1860785) B1860785
theorem B4189643 : Blo 1240438 4189643 := bstep (se 1 (by rfl) ⟨3142232, by rfl⟩ : syracuseStep 4189643 = 6284465) B6284465
theorem B1240535 : Blo 1240438 1240535 := bstep (se 1 (by rfl) ⟨930401, by rfl⟩ : syracuseStep 1240535 = 1860803) B1860803
theorem B1396183 : Blo 1240438 1396183 := bstep (se 1 (by rfl) ⟨1047137, by rfl⟩ : syracuseStep 1396183 = 2094275) B2094275
theorem B1240555 : Blo 1240438 1240555 := bstep (se 1 (by rfl) ⟨930416, by rfl⟩ : syracuseStep 1240555 = 1860833) B1860833
theorem B1240567 : Blo 1240438 1240567 := bstep (se 1 (by rfl) ⟨930425, by rfl⟩ : syracuseStep 1240567 = 1860851) B1860851
theorem B1240587 : Blo 1240438 1240587 := bstep (se 1 (by rfl) ⟨930440, by rfl⟩ : syracuseStep 1240587 = 1860881) B1860881
theorem B2649611 : Blo 1240438 2649611 := bstep (se 1 (by rfl) ⟨1987208, by rfl⟩ : syracuseStep 2649611 = 3974417) B3974417
theorem B1863179 : Blo 1240438 1863179 := bstep (se 1 (by rfl) ⟨1397384, by rfl⟩ : syracuseStep 1863179 = 2794769) B2794769
theorem B1240599 : Blo 1240438 1240599 := bstep (se 1 (by rfl) ⟨930449, by rfl⟩ : syracuseStep 1240599 = 1860899) B1860899
theorem B1863191 : Blo 1240438 1863191 := bstep (se 1 (by rfl) ⟨1397393, by rfl⟩ : syracuseStep 1863191 = 2794787) B2794787
theorem B1240619 : Blo 1240438 1240619 := bstep (se 1 (by rfl) ⟨930464, by rfl⟩ : syracuseStep 1240619 = 1860929) B1860929
theorem B1240631 : Blo 1240438 1240631 := bstep (se 1 (by rfl) ⟨930473, by rfl⟩ : syracuseStep 1240631 = 1860947) B1860947
theorem B1240651 : Blo 1240438 1240651 := bstep (se 1 (by rfl) ⟨930488, by rfl⟩ : syracuseStep 1240651 = 1860977) B1860977
theorem B1240663 : Blo 1240438 1240663 := bstep (se 1 (by rfl) ⟨930497, by rfl⟩ : syracuseStep 1240663 = 1860995) B1860995
theorem B1863257 : Blo 1240438 1863257 := bstep (se 2 (by rfl) ⟨698721, by rfl⟩ : syracuseStep 1863257 = 1397443) B1397443
theorem B1240683 : Blo 1240438 1240683 := bstep (se 1 (by rfl) ⟨930512, by rfl⟩ : syracuseStep 1240683 = 1861025) B1861025
theorem B1240695 : Blo 1240438 1240695 := bstep (se 1 (by rfl) ⟨930521, by rfl⟩ : syracuseStep 1240695 = 1861043) B1861043
theorem B1240715 : Blo 1240438 1240715 := bstep (se 1 (by rfl) ⟨930536, by rfl⟩ : syracuseStep 1240715 = 1861073) B1861073
theorem B1396363 : Blo 1240438 1396363 := bstep (se 1 (by rfl) ⟨1047272, by rfl⟩ : syracuseStep 1396363 = 2094545) B2094545
theorem B1240727 : Blo 1240438 1240727 := bstep (se 1 (by rfl) ⟨930545, by rfl⟩ : syracuseStep 1240727 = 1861091) B1861091
theorem B1240747 : Blo 1240438 1240747 := bstep (se 1 (by rfl) ⟨930560, by rfl⟩ : syracuseStep 1240747 = 1861121) B1861121
theorem B1240759 : Blo 1240438 1240759 := bstep (se 1 (by rfl) ⟨930569, by rfl⟩ : syracuseStep 1240759 = 1861139) B1861139
theorem B1240779 : Blo 1240438 1240779 := bstep (se 1 (by rfl) ⟨930584, by rfl⟩ : syracuseStep 1240779 = 1861169) B1861169
theorem B1863371 : Blo 1240438 1863371 := bstep (se 1 (by rfl) ⟨1397528, by rfl⟩ : syracuseStep 1863371 = 2795057) B2795057
theorem B1240791 : Blo 1240438 1240791 := bstep (se 1 (by rfl) ⟨930593, by rfl⟩ : syracuseStep 1240791 = 1861187) B1861187
theorem B1863383 : Blo 1240438 1863383 := bstep (se 1 (by rfl) ⟨1397537, by rfl⟩ : syracuseStep 1863383 = 2795075) B2795075
theorem B4189913 : Blo 1240438 4189913 := bstep (se 2 (by rfl) ⟨1571217, by rfl⟩ : syracuseStep 4189913 = 3142435) B3142435
theorem B1240811 : Blo 1240438 1240811 := bstep (se 1 (by rfl) ⟨930608, by rfl⟩ : syracuseStep 1240811 = 1861217) B1861217
theorem B1240823 : Blo 1240438 1240823 := bstep (se 1 (by rfl) ⟨930617, by rfl⟩ : syracuseStep 1240823 = 1861235) B1861235
theorem B1396471 : Blo 1240438 1396471 := bstep (se 1 (by rfl) ⟨1047353, by rfl⟩ : syracuseStep 1396471 = 2094707) B2094707
theorem B1240843 : Blo 1240438 1240843 := bstep (se 1 (by rfl) ⟨930632, by rfl⟩ : syracuseStep 1240843 = 1861265) B1861265
theorem B1240855 : Blo 1240438 1240855 := bstep (se 1 (by rfl) ⟨930641, by rfl⟩ : syracuseStep 1240855 = 1861283) B1861283
theorem B1863449 : Blo 1240438 1863449 := bstep (se 2 (by rfl) ⟨698793, by rfl⟩ : syracuseStep 1863449 = 1397587) B1397587
theorem B1240875 : Blo 1240438 1240875 := bstep (se 1 (by rfl) ⟨930656, by rfl⟩ : syracuseStep 1240875 = 1861313) B1861313
theorem B1240887 : Blo 1240438 1240887 := bstep (se 1 (by rfl) ⟨930665, by rfl⟩ : syracuseStep 1240887 = 1861331) B1861331
theorem B1240907 : Blo 1240438 1240907 := bstep (se 1 (by rfl) ⟨930680, by rfl⟩ : syracuseStep 1240907 = 1861361) B1861361
theorem B1240919 : Blo 1240438 1240919 := bstep (se 1 (by rfl) ⟨930689, by rfl⟩ : syracuseStep 1240919 = 1861379) B1861379
theorem B1240939 : Blo 1240438 1240939 := bstep (se 1 (by rfl) ⟨930704, by rfl⟩ : syracuseStep 1240939 = 1861409) B1861409
theorem B1240951 : Blo 1240438 1240951 := bstep (se 1 (by rfl) ⟨930713, by rfl⟩ : syracuseStep 1240951 = 1861427) B1861427
theorem B1240971 : Blo 1240438 1240971 := bstep (se 1 (by rfl) ⟨930728, by rfl⟩ : syracuseStep 1240971 = 1861457) B1861457
theorem B1863563 : Blo 1240438 1863563 := bstep (se 1 (by rfl) ⟨1397672, by rfl⟩ : syracuseStep 1863563 = 2795345) B2795345
theorem B2355095 : Blo 1240438 2355095 := bstep (se 1 (by rfl) ⟨1766321, by rfl⟩ : syracuseStep 2355095 = 3532643) B3532643
theorem B1240983 : Blo 1240438 1240983 := bstep (se 1 (by rfl) ⟨930737, by rfl⟩ : syracuseStep 1240983 = 1861475) B1861475
theorem B1863575 : Blo 1240438 1863575 := bstep (se 1 (by rfl) ⟨1397681, by rfl⟩ : syracuseStep 1863575 = 2795363) B2795363
theorem B1241003 : Blo 1240438 1241003 := bstep (se 1 (by rfl) ⟨930752, by rfl⟩ : syracuseStep 1241003 = 1861505) B1861505
theorem B1396651 : Blo 1240438 1396651 := bstep (se 1 (by rfl) ⟨1047488, by rfl⟩ : syracuseStep 1396651 = 2094977) B2094977
theorem B1241015 : Blo 1240438 1241015 := bstep (se 1 (by rfl) ⟨930761, by rfl⟩ : syracuseStep 1241015 = 1861523) B1861523
theorem B3534785 : Blo 1240438 3534785 := bstep (se 2 (by rfl) ⟨1325544, by rfl⟩ : syracuseStep 3534785 = 2651089) B2651089
theorem B1241035 : Blo 1240438 1241035 := bstep (se 1 (by rfl) ⟨930776, by rfl⟩ : syracuseStep 1241035 = 1861553) B1861553
theorem B1241047 : Blo 1240438 1241047 := bstep (se 1 (by rfl) ⟨930785, by rfl⟩ : syracuseStep 1241047 = 1861571) B1861571
theorem B1863641 : Blo 1240438 1863641 := bstep (se 2 (by rfl) ⟨698865, by rfl⟩ : syracuseStep 1863641 = 1397731) B1397731
theorem B1241067 : Blo 1240438 1241067 := bstep (se 1 (by rfl) ⟨930800, by rfl⟩ : syracuseStep 1241067 = 1861601) B1861601
theorem B1241079 : Blo 1240438 1241079 := bstep (se 1 (by rfl) ⟨930809, by rfl⟩ : syracuseStep 1241079 = 1861619) B1861619
theorem B1241099 : Blo 1240438 1241099 := bstep (se 1 (by rfl) ⟨930824, by rfl⟩ : syracuseStep 1241099 = 1861649) B1861649
theorem B1241111 : Blo 1240438 1241111 := bstep (se 1 (by rfl) ⟨930833, by rfl⟩ : syracuseStep 1241111 = 1861667) B1861667
theorem B1396759 : Blo 1240438 1396759 := bstep (se 1 (by rfl) ⟨1047569, by rfl⟩ : syracuseStep 1396759 = 2095139) B2095139
theorem B1241131 : Blo 1240438 1241131 := bstep (se 1 (by rfl) ⟨930848, by rfl⟩ : syracuseStep 1241131 = 1861697) B1861697
theorem B5304365 : Blo 1240438 5304365 := bstep (se 3 (by rfl) ⟨994568, by rfl⟩ : syracuseStep 5304365 = 1989137) B1989137
theorem B1241143 : Blo 1240438 1241143 := bstep (se 1 (by rfl) ⟨930857, by rfl⟩ : syracuseStep 1241143 = 1861715) B1861715
theorem B1241163 : Blo 1240438 1241163 := bstep (se 1 (by rfl) ⟨930872, by rfl⟩ : syracuseStep 1241163 = 1861745) B1861745
theorem B1241175 : Blo 1240438 1241175 := bstep (se 1 (by rfl) ⟨930881, by rfl⟩ : syracuseStep 1241175 = 1861763) B1861763
theorem B3772505 : Blo 1240438 3772505 := bstep (se 2 (by rfl) ⟨1414689, by rfl⟩ : syracuseStep 3772505 = 2829379) B2829379
theorem B9424997 : Blo 1240438 9424997 := bstep (se 4 (by rfl) ⟨883593, by rfl⟩ : syracuseStep 9424997 = 1767187) B1767187
theorem B1241195 : Blo 1240438 1241195 := bstep (se 1 (by rfl) ⟨930896, by rfl⟩ : syracuseStep 1241195 = 1861793) B1861793
theorem B1241207 : Blo 1240438 1241207 := bstep (se 1 (by rfl) ⟨930905, by rfl⟩ : syracuseStep 1241207 = 1861811) B1861811
theorem B1241227 : Blo 1240438 1241227 := bstep (se 1 (by rfl) ⟨930920, by rfl⟩ : syracuseStep 1241227 = 1861841) B1861841
theorem B1241239 : Blo 1240438 1241239 := bstep (se 1 (by rfl) ⟨930929, by rfl⟩ : syracuseStep 1241239 = 1861859) B1861859
theorem B1241259 : Blo 1240438 1241259 := bstep (se 1 (by rfl) ⟨930944, by rfl⟩ : syracuseStep 1241259 = 1861889) B1861889
theorem B3403955 : Blo 1240438 3403955 := bstep (se 1 (by rfl) ⟨2552966, by rfl⟩ : syracuseStep 3403955 = 5105933) B5105933
theorem B1241271 : Blo 1240438 1241271 := bstep (se 1 (by rfl) ⟨930953, by rfl⟩ : syracuseStep 1241271 = 1861907) B1861907
theorem B1241291 : Blo 1240438 1241291 := bstep (se 1 (by rfl) ⟨930968, by rfl⟩ : syracuseStep 1241291 = 1861937) B1861937
theorem B1396939 : Blo 1240438 1396939 := bstep (se 1 (by rfl) ⟨1047704, by rfl⟩ : syracuseStep 1396939 = 2095409) B2095409
theorem B1241303 : Blo 1240438 1241303 := bstep (se 1 (by rfl) ⟨930977, by rfl⟩ : syracuseStep 1241303 = 1861955) B1861955
theorem B1241323 : Blo 1240438 1241323 := bstep (se 1 (by rfl) ⟨930992, by rfl⟩ : syracuseStep 1241323 = 1861985) B1861985
theorem B1241335 : Blo 1240438 1241335 := bstep (se 1 (by rfl) ⟨931001, by rfl⟩ : syracuseStep 1241335 = 1862003) B1862003
theorem B2093323 : Blo 1240438 2093323 := bstep (se 1 (by rfl) ⟨1569992, by rfl⟩ : syracuseStep 2093323 = 3139985) B3139985
theorem B1241355 : Blo 1240438 1241355 := bstep (se 1 (by rfl) ⟨931016, by rfl⟩ : syracuseStep 1241355 = 1862033) B1862033
theorem B1241367 : Blo 1240438 1241367 := bstep (se 1 (by rfl) ⟨931025, by rfl⟩ : syracuseStep 1241367 = 1862051) B1862051
theorem B3535127 : Blo 1240438 3535127 := bstep (se 1 (by rfl) ⟨2651345, by rfl⟩ : syracuseStep 3535127 = 5302691) B5302691
theorem B1241387 : Blo 1240438 1241387 := bstep (se 1 (by rfl) ⟨931040, by rfl⟩ : syracuseStep 1241387 = 1862081) B1862081
theorem B1241399 : Blo 1240438 1241399 := bstep (se 1 (by rfl) ⟨931049, by rfl⟩ : syracuseStep 1241399 = 1862099) B1862099
theorem B1397047 : Blo 1240438 1397047 := bstep (se 1 (by rfl) ⟨1047785, by rfl⟩ : syracuseStep 1397047 = 2095571) B2095571
theorem B1241419 : Blo 1240438 1241419 := bstep (se 1 (by rfl) ⟨931064, by rfl⟩ : syracuseStep 1241419 = 1862129) B1862129
theorem B1241431 : Blo 1240438 1241431 := bstep (se 1 (by rfl) ⟨931073, by rfl⟩ : syracuseStep 1241431 = 1862147) B1862147
theorem B2650457 : Blo 1240438 2650457 := bstep (se 2 (by rfl) ⟨993921, by rfl⟩ : syracuseStep 2650457 = 1987843) B1987843
theorem B1241451 : Blo 1240438 1241451 := bstep (se 1 (by rfl) ⟨931088, by rfl⟩ : syracuseStep 1241451 = 1862177) B1862177
theorem B1241463 : Blo 1240438 1241463 := bstep (se 1 (by rfl) ⟨931097, by rfl⟩ : syracuseStep 1241463 = 1862195) B1862195
theorem B1241483 : Blo 1240438 1241483 := bstep (se 1 (by rfl) ⟨931112, by rfl⟩ : syracuseStep 1241483 = 1862225) B1862225
theorem B1241495 : Blo 1240438 1241495 := bstep (se 1 (by rfl) ⟨931121, by rfl⟩ : syracuseStep 1241495 = 1862243) B1862243
theorem B4190615 : Blo 1240438 4190615 := bstep (se 1 (by rfl) ⟨3142961, by rfl⟩ : syracuseStep 4190615 = 6285923) B6285923
theorem B2093465 : Blo 1240438 2093465 := bstep (se 2 (by rfl) ⟨785049, by rfl⟩ : syracuseStep 2093465 = 1570099) B1570099
theorem B1241515 : Blo 1240438 1241515 := bstep (se 1 (by rfl) ⟨931136, by rfl⟩ : syracuseStep 1241515 = 1862273) B1862273
theorem B2355635 : Blo 1240438 2355635 := bstep (se 1 (by rfl) ⟨1766726, by rfl⟩ : syracuseStep 2355635 = 3533453) B3533453
theorem B1241527 : Blo 1240438 1241527 := bstep (se 1 (by rfl) ⟨931145, by rfl⟩ : syracuseStep 1241527 = 1862291) B1862291
theorem B3142091 : Blo 1240438 3142091 := bstep (se 1 (by rfl) ⟨2356568, by rfl⟩ : syracuseStep 3142091 = 4713137) B4713137
theorem B1241547 : Blo 1240438 1241547 := bstep (se 1 (by rfl) ⟨931160, by rfl⟩ : syracuseStep 1241547 = 1862321) B1862321
theorem B10605005 : Blo 1240438 10605005 := bstep (se 3 (by rfl) ⟨1988438, by rfl⟩ : syracuseStep 10605005 = 3976877) B3976877
theorem B1241559 : Blo 1240438 1241559 := bstep (se 1 (by rfl) ⟨931169, by rfl⟩ : syracuseStep 1241559 = 1862339) B1862339
theorem B1241579 : Blo 1240438 1241579 := bstep (se 1 (by rfl) ⟨931184, by rfl⟩ : syracuseStep 1241579 = 1862369) B1862369
theorem B1397227 : Blo 1240438 1397227 := bstep (se 1 (by rfl) ⟨1047920, by rfl⟩ : syracuseStep 1397227 = 2095841) B2095841
theorem B1241591 : Blo 1240438 1241591 := bstep (se 1 (by rfl) ⟨931193, by rfl⟩ : syracuseStep 1241591 = 1862387) B1862387
theorem B1241611 : Blo 1240438 1241611 := bstep (se 1 (by rfl) ⟨931208, by rfl⟩ : syracuseStep 1241611 = 1862417) B1862417
theorem B1241623 : Blo 1240438 1241623 := bstep (se 1 (by rfl) ⟨931217, by rfl⟩ : syracuseStep 1241623 = 1862435) B1862435
theorem B4477463 : Blo 1240438 4477463 := bstep (se 1 (by rfl) ⟨3358097, by rfl⟩ : syracuseStep 4477463 = 6716195) B6716195
theorem B2093593 : Blo 1240438 2093593 := bstep (se 2 (by rfl) ⟨785097, by rfl⟩ : syracuseStep 2093593 = 1570195) B1570195
theorem B1241643 : Blo 1240438 1241643 := bstep (se 1 (by rfl) ⟨931232, by rfl⟩ : syracuseStep 1241643 = 1862465) B1862465
theorem B1241655 : Blo 1240438 1241655 := bstep (se 1 (by rfl) ⟨931241, by rfl⟩ : syracuseStep 1241655 = 1862483) B1862483
theorem B3772993 : Blo 1240438 3772993 := bstep (se 2 (by rfl) ⟨1414872, by rfl⟩ : syracuseStep 3772993 = 2829745) B2829745
theorem B18133579 : Blo 1240438 18133579 := bstep (se 1 (by rfl) ⟨13600184, by rfl⟩ : syracuseStep 18133579 = 27200369) B27200369
theorem B9425483 : Blo 1240438 9425483 := bstep (se 1 (by rfl) ⟨7069112, by rfl⟩ : syracuseStep 9425483 = 14138225) B14138225
theorem B1241675 : Blo 1240438 1241675 := bstep (se 1 (by rfl) ⟨931256, by rfl⟩ : syracuseStep 1241675 = 1862513) B1862513
theorem B1241687 : Blo 1240438 1241687 := bstep (se 1 (by rfl) ⟨931265, by rfl⟩ : syracuseStep 1241687 = 1862531) B1862531
theorem B1397335 : Blo 1240438 1397335 := bstep (se 1 (by rfl) ⟨1048001, by rfl⟩ : syracuseStep 1397335 = 2096003) B2096003
theorem B1241707 : Blo 1240438 1241707 := bstep (se 1 (by rfl) ⟨931280, by rfl⟩ : syracuseStep 1241707 = 1862561) B1862561
theorem B1241719 : Blo 1240438 1241719 := bstep (se 1 (by rfl) ⟨931289, by rfl⟩ : syracuseStep 1241719 = 1862579) B1862579
theorem B1241739 : Blo 1240438 1241739 := bstep (se 1 (by rfl) ⟨931304, by rfl⟩ : syracuseStep 1241739 = 1862609) B1862609
theorem B1241751 : Blo 1240438 1241751 := bstep (se 1 (by rfl) ⟨931313, by rfl⟩ : syracuseStep 1241751 = 1862627) B1862627
theorem B1241771 : Blo 1240438 1241771 := bstep (se 1 (by rfl) ⟨931328, by rfl⟩ : syracuseStep 1241771 = 1862657) B1862657
theorem B1241783 : Blo 1240438 1241783 := bstep (se 1 (by rfl) ⟨931337, by rfl⟩ : syracuseStep 1241783 = 1862675) B1862675
theorem B1241803 : Blo 1240438 1241803 := bstep (se 1 (by rfl) ⟨931352, by rfl⟩ : syracuseStep 1241803 = 1862705) B1862705
theorem B1241815 : Blo 1240438 1241815 := bstep (se 1 (by rfl) ⟨931361, by rfl⟩ : syracuseStep 1241815 = 1862723) B1862723
theorem B1241835 : Blo 1240438 1241835 := bstep (se 1 (by rfl) ⟨931376, by rfl⟩ : syracuseStep 1241835 = 1862753) B1862753
theorem B1241847 : Blo 1240438 1241847 := bstep (se 1 (by rfl) ⟨931385, by rfl⟩ : syracuseStep 1241847 = 1862771) B1862771
theorem B1241867 : Blo 1240438 1241867 := bstep (se 1 (by rfl) ⟨931400, by rfl⟩ : syracuseStep 1241867 = 1862801) B1862801
theorem B1397515 : Blo 1240438 1397515 := bstep (se 1 (by rfl) ⟨1048136, by rfl⟩ : syracuseStep 1397515 = 2096273) B2096273
theorem B3355415 : Blo 1240438 3355415 := bstep (se 1 (by rfl) ⟨2516561, by rfl⟩ : syracuseStep 3355415 = 5033123) B5033123
theorem B1241879 : Blo 1240438 1241879 := bstep (se 1 (by rfl) ⟨931409, by rfl⟩ : syracuseStep 1241879 = 1862819) B1862819
theorem B2388761 : Blo 1240438 2388761 := bstep (se 2 (by rfl) ⟨895785, by rfl⟩ : syracuseStep 2388761 = 1791571) B1791571
theorem B7959313 : Blo 1240438 7959313 := bstep (se 2 (by rfl) ⟨2984742, by rfl⟩ : syracuseStep 7959313 = 5969485) B5969485
theorem B1241899 : Blo 1240438 1241899 := bstep (se 1 (by rfl) ⟨931424, by rfl⟩ : syracuseStep 1241899 = 1862849) B1862849
theorem B1241911 : Blo 1240438 1241911 := bstep (se 1 (by rfl) ⟨931433, by rfl⟩ : syracuseStep 1241911 = 1862867) B1862867
theorem B4248395 : Blo 1240438 4248395 := bstep (se 1 (by rfl) ⟨3186296, by rfl⟩ : syracuseStep 4248395 = 6372593) B6372593
theorem B1241931 : Blo 1240438 1241931 := bstep (se 1 (by rfl) ⟨931448, by rfl⟩ : syracuseStep 1241931 = 1862897) B1862897
theorem B1241943 : Blo 1240438 1241943 := bstep (se 1 (by rfl) ⟨931457, by rfl⟩ : syracuseStep 1241943 = 1862915) B1862915
theorem B1241963 : Blo 1240438 1241963 := bstep (se 1 (by rfl) ⟨931472, by rfl⟩ : syracuseStep 1241963 = 1862945) B1862945
theorem B1241975 : Blo 1240438 1241975 := bstep (se 1 (by rfl) ⟨931481, by rfl⟩ : syracuseStep 1241975 = 1862963) B1862963
theorem B1397623 : Blo 1240438 1397623 := bstep (se 1 (by rfl) ⟨1048217, by rfl⟩ : syracuseStep 1397623 = 2096435) B2096435
theorem B1241995 : Blo 1240438 1241995 := bstep (se 1 (by rfl) ⟨931496, by rfl⟩ : syracuseStep 1241995 = 1862993) B1862993
theorem B1242007 : Blo 1240438 1242007 := bstep (se 1 (by rfl) ⟨931505, by rfl⟩ : syracuseStep 1242007 = 1863011) B1863011
theorem B2356121 : Blo 1240438 2356121 := bstep (se 2 (by rfl) ⟨883545, by rfl⟩ : syracuseStep 2356121 = 1767091) B1767091
theorem B1242027 : Blo 1240438 1242027 := bstep (se 1 (by rfl) ⟨931520, by rfl⟩ : syracuseStep 1242027 = 1863041) B1863041
theorem B4191155 : Blo 1240438 4191155 := bstep (se 1 (by rfl) ⟨3143366, by rfl⟩ : syracuseStep 4191155 = 6286733) B6286733
theorem B1242039 : Blo 1240438 1242039 := bstep (se 1 (by rfl) ⟨931529, by rfl⟩ : syracuseStep 1242039 = 1863059) B1863059
theorem B1242059 : Blo 1240438 1242059 := bstep (se 1 (by rfl) ⟨931544, by rfl⟩ : syracuseStep 1242059 = 1863089) B1863089
theorem B1242071 : Blo 1240438 1242071 := bstep (se 1 (by rfl) ⟨931553, by rfl⟩ : syracuseStep 1242071 = 1863107) B1863107
theorem B1258475 : Blo 1240438 1258475 := bstep (se 1 (by rfl) ⟨943856, by rfl⟩ : syracuseStep 1258475 = 1887713) B1887713
theorem B1242091 : Blo 1240438 1242091 := bstep (se 1 (by rfl) ⟨931568, by rfl⟩ : syracuseStep 1242091 = 1863137) B1863137
theorem B2651123 : Blo 1240438 2651123 := bstep (se 1 (by rfl) ⟨1988342, by rfl⟩ : syracuseStep 2651123 = 3976685) B3976685
theorem B1242103 : Blo 1240438 1242103 := bstep (se 1 (by rfl) ⟨931577, by rfl⟩ : syracuseStep 1242103 = 1863155) B1863155
theorem B1242123 : Blo 1240438 1242123 := bstep (se 1 (by rfl) ⟨931592, by rfl⟩ : syracuseStep 1242123 = 1863185) B1863185
theorem B1242135 : Blo 1240438 1242135 := bstep (se 1 (by rfl) ⟨931601, by rfl⟩ : syracuseStep 1242135 = 1863203) B1863203
theorem B1242155 : Blo 1240438 1242155 := bstep (se 1 (by rfl) ⟨931616, by rfl⟩ : syracuseStep 1242155 = 1863233) B1863233
theorem B1242167 : Blo 1240438 1242167 := bstep (se 1 (by rfl) ⟨931625, by rfl⟩ : syracuseStep 1242167 = 1863251) B1863251
theorem B1242187 : Blo 1240438 1242187 := bstep (se 1 (by rfl) ⟨931640, by rfl⟩ : syracuseStep 1242187 = 1863281) B1863281
theorem B2094167 : Blo 1240438 2094167 := bstep (se 1 (by rfl) ⟨1570625, by rfl⟩ : syracuseStep 2094167 = 3141251) B3141251
theorem B1242199 : Blo 1240438 1242199 := bstep (se 1 (by rfl) ⟨931649, by rfl⟩ : syracuseStep 1242199 = 1863299) B1863299
theorem B1242219 : Blo 1240438 1242219 := bstep (se 1 (by rfl) ⟨931664, by rfl⟩ : syracuseStep 1242219 = 1863329) B1863329
theorem B1242231 : Blo 1240438 1242231 := bstep (se 1 (by rfl) ⟨931673, by rfl⟩ : syracuseStep 1242231 = 1863347) B1863347
theorem B6288515 : Blo 1240438 6288515 := bstep (se 1 (by rfl) ⟨4716386, by rfl⟩ : syracuseStep 6288515 = 9432773) B9432773
theorem B1242251 : Blo 1240438 1242251 := bstep (se 1 (by rfl) ⟨931688, by rfl⟩ : syracuseStep 1242251 = 1863377) B1863377
theorem B1242263 : Blo 1240438 1242263 := bstep (se 1 (by rfl) ⟨931697, by rfl⟩ : syracuseStep 1242263 = 1863395) B1863395
theorem B1242283 : Blo 1240438 1242283 := bstep (se 1 (by rfl) ⟨931712, by rfl⟩ : syracuseStep 1242283 = 1863425) B1863425
theorem B1242295 : Blo 1240438 1242295 := bstep (se 1 (by rfl) ⟨931721, by rfl⟩ : syracuseStep 1242295 = 1863443) B1863443
theorem B4191425 : Blo 1240438 4191425 := bstep (se 2 (by rfl) ⟨1571784, by rfl⟩ : syracuseStep 4191425 = 3143569) B3143569
theorem B1242315 : Blo 1240438 1242315 := bstep (se 1 (by rfl) ⟨931736, by rfl⟩ : syracuseStep 1242315 = 1863473) B1863473
theorem B2094295 : Blo 1240438 2094295 := bstep (se 1 (by rfl) ⟨1570721, by rfl⟩ : syracuseStep 2094295 = 3141443) B3141443
theorem B1242327 : Blo 1240438 1242327 := bstep (se 1 (by rfl) ⟨931745, by rfl⟩ : syracuseStep 1242327 = 1863491) B1863491
theorem B1242347 : Blo 1240438 1242347 := bstep (se 1 (by rfl) ⟨931760, by rfl⟩ : syracuseStep 1242347 = 1863521) B1863521
theorem B1242359 : Blo 1240438 1242359 := bstep (se 1 (by rfl) ⟨931769, by rfl⟩ : syracuseStep 1242359 = 1863539) B1863539
theorem B4715779 : Blo 1240438 4715779 := bstep (se 1 (by rfl) ⟨3536834, by rfl⟩ : syracuseStep 4715779 = 7073669) B7073669
theorem B1242379 : Blo 1240438 1242379 := bstep (se 1 (by rfl) ⟨931784, by rfl⟩ : syracuseStep 1242379 = 1863569) B1863569
theorem B1242391 : Blo 1240438 1242391 := bstep (se 1 (by rfl) ⟨931793, by rfl⟩ : syracuseStep 1242391 = 1863587) B1863587
theorem B1242411 : Blo 1240438 1242411 := bstep (se 1 (by rfl) ⟨931808, by rfl⟩ : syracuseStep 1242411 = 1863617) B1863617
theorem B1242423 : Blo 1240438 1242423 := bstep (se 1 (by rfl) ⟨931817, by rfl⟩ : syracuseStep 1242423 = 1863635) B1863635
theorem B3143063 : Blo 1240438 3143063 := bstep (se 1 (by rfl) ⟨2357297, by rfl⟩ : syracuseStep 3143063 = 4714595) B4714595
theorem B4716083 : Blo 1240438 4716083 := bstep (se 1 (by rfl) ⟨3537062, by rfl⟩ : syracuseStep 4716083 = 7074125) B7074125
theorem B9434717 : Blo 1240438 9434717 := bstep (se 3 (by rfl) ⟨1769009, by rfl⟩ : syracuseStep 9434717 = 3538019) B3538019
theorem B9549413 : Blo 1240438 9549413 := bstep (se 4 (by rfl) ⟨895257, by rfl⟩ : syracuseStep 9549413 = 1790515) B1790515
theorem B12744323 : Blo 1240438 12744323 := bstep (se 1 (by rfl) ⟨9558242, by rfl⟩ : syracuseStep 12744323 = 19116485) B19116485
theorem B2791115 : Blo 1240438 2791115 := bstep (se 1 (by rfl) ⟨2093336, by rfl⟩ : syracuseStep 2791115 = 4186673) B4186673
theorem B1570519 : Blo 1240438 1570519 := bstep (se 1 (by rfl) ⟨1177889, by rfl⟩ : syracuseStep 1570519 = 2355779) B2355779
theorem B4191965 : Blo 1240438 4191965 := bstep (se 3 (by rfl) ⟨785993, by rfl⟩ : syracuseStep 4191965 = 1571987) B1571987
theorem B2791169 : Blo 1240438 2791169 := bstep (se 2 (by rfl) ⟨1046688, by rfl⟩ : syracuseStep 2791169 = 2093377) B2093377
theorem B6715153 : Blo 1240438 6715153 := bstep (se 2 (by rfl) ⟨2518182, by rfl⟩ : syracuseStep 6715153 = 5036365) B5036365
theorem B1414955 : Blo 1240438 1414955 := bstep (se 1 (by rfl) ⟨1061216, by rfl⟩ : syracuseStep 1414955 = 2122433) B2122433
theorem B2094923 : Blo 1240438 2094923 := bstep (se 1 (by rfl) ⟨1571192, by rfl⟩ : syracuseStep 2094923 = 3142385) B3142385
theorem B2652097 : Blo 1240438 2652097 := bstep (se 2 (by rfl) ⟨994536, by rfl⟩ : syracuseStep 2652097 = 1989073) B1989073
theorem B2095051 : Blo 1240438 2095051 := bstep (se 1 (by rfl) ⟨1571288, by rfl⟩ : syracuseStep 2095051 = 3142577) B3142577
theorem B2791385 : Blo 1240438 2791385 := bstep (se 2 (by rfl) ⟨1046769, by rfl⟩ : syracuseStep 2791385 = 2093539) B2093539
theorem B2791475 : Blo 1240438 2791475 := bstep (se 1 (by rfl) ⟨2093606, by rfl⟩ : syracuseStep 2791475 = 4187213) B4187213
theorem B3143731 : Blo 1240438 3143731 := bstep (se 1 (by rfl) ⟨2357798, by rfl⟩ : syracuseStep 3143731 = 4715597) B4715597
theorem B5036107 : Blo 1240438 5036107 := bstep (se 1 (by rfl) ⟨3777080, by rfl⟩ : syracuseStep 5036107 = 7554161) B7554161
theorem B2791511 : Blo 1240438 2791511 := bstep (se 1 (by rfl) ⟨2093633, by rfl⟩ : syracuseStep 2791511 = 4187267) B4187267
theorem B2095193 : Blo 1240438 2095193 := bstep (se 2 (by rfl) ⟨785697, by rfl⟩ : syracuseStep 2095193 = 1571395) B1571395
theorem B6715543 : Blo 1240438 6715543 := bstep (se 1 (by rfl) ⟨5036657, by rfl⟩ : syracuseStep 6715543 = 10073315) B10073315
theorem B2652353 : Blo 1240438 2652353 := bstep (se 2 (by rfl) ⟨994632, by rfl⟩ : syracuseStep 2652353 = 1989265) B1989265
theorem B3143873 : Blo 1240438 3143873 := bstep (se 2 (by rfl) ⟨1178952, by rfl⟩ : syracuseStep 3143873 = 2357905) B2357905
theorem B4716737 : Blo 1240438 4716737 := bstep (se 2 (by rfl) ⟨1768776, by rfl⟩ : syracuseStep 4716737 = 3537553) B3537553
theorem B2095321 : Blo 1240438 2095321 := bstep (se 2 (by rfl) ⟨785745, by rfl⟩ : syracuseStep 2095321 = 1571491) B1571491
theorem B2791691 : Blo 1240438 2791691 := bstep (se 1 (by rfl) ⟨2093768, by rfl⟩ : syracuseStep 2791691 = 4187537) B4187537
theorem B2652439 : Blo 1240438 2652439 := bstep (se 1 (by rfl) ⟨1989329, by rfl⟩ : syracuseStep 2652439 = 3978659) B3978659
theorem B3979543 : Blo 1240438 3979543 := bstep (se 1 (by rfl) ⟨2984657, by rfl⟩ : syracuseStep 3979543 = 5969315) B5969315
theorem B2791745 : Blo 1240438 2791745 := bstep (se 2 (by rfl) ⟨1046904, by rfl⟩ : syracuseStep 2791745 = 2093809) B2093809
theorem B2357579 : Blo 1240438 2357579 := bstep (se 1 (by rfl) ⟨1768184, by rfl⟩ : syracuseStep 2357579 = 3536369) B3536369
theorem B8943965 : Blo 1240438 8943965 := bstep (se 3 (by rfl) ⟨1676993, by rfl⟩ : syracuseStep 8943965 = 3353987) B3353987
theorem B3537245 : Blo 1240438 3537245 := bstep (se 3 (by rfl) ⟨663233, by rfl⟩ : syracuseStep 3537245 = 1326467) B1326467
theorem B1325527 : Blo 1240438 1325527 := bstep (se 1 (by rfl) ⟨994145, by rfl⟩ : syracuseStep 1325527 = 1988291) B1988291
theorem B5298691 : Blo 1240438 5298691 := bstep (se 1 (by rfl) ⟨3974018, by rfl⟩ : syracuseStep 5298691 = 7948037) B7948037
theorem B2357761 : Blo 1240438 2357761 := bstep (se 2 (by rfl) ⟨884160, by rfl⟩ : syracuseStep 2357761 = 1768321) B1768321
theorem B1571339 : Blo 1240438 1571339 := bstep (se 1 (by rfl) ⟨1178504, by rfl⟩ : syracuseStep 1571339 = 2357009) B2357009
theorem B2791961 : Blo 1240438 2791961 := bstep (se 2 (by rfl) ⟨1046985, by rfl⟩ : syracuseStep 2791961 = 2093971) B2093971
theorem B9812515 : Blo 1240438 9812515 := bstep (se 1 (by rfl) ⟨7359386, by rfl⟩ : syracuseStep 9812515 = 14718773) B14718773
theorem B2792051 : Blo 1240438 2792051 := bstep (se 1 (by rfl) ⟨2094038, by rfl⟩ : syracuseStep 2792051 = 4188077) B4188077
theorem B2792087 : Blo 1240438 2792087 := bstep (se 1 (by rfl) ⟨2094065, by rfl⟩ : syracuseStep 2792087 = 4188131) B4188131
theorem B10074775 : Blo 1240438 10074775 := bstep (se 1 (by rfl) ⟨7556081, by rfl⟩ : syracuseStep 10074775 = 15112163) B15112163
theorem B3537587 : Blo 1240438 3537587 := bstep (se 1 (by rfl) ⟨2653190, by rfl⟩ : syracuseStep 3537587 = 5306381) B5306381
theorem B2980631 : Blo 1240438 2980631 := bstep (se 1 (by rfl) ⟨2235473, by rfl⟩ : syracuseStep 2980631 = 4470947) B4470947
theorem B2095895 : Blo 1240438 2095895 := bstep (se 1 (by rfl) ⟨1571921, by rfl⟩ : syracuseStep 2095895 = 3143843) B3143843
theorem B2792267 : Blo 1240438 2792267 := bstep (se 1 (by rfl) ⟨2094200, by rfl⟩ : syracuseStep 2792267 = 4188401) B4188401
theorem B1325899 : Blo 1240438 1325899 := bstep (se 1 (by rfl) ⟨994424, by rfl⟩ : syracuseStep 1325899 = 1988849) B1988849
theorem B4193099 : Blo 1240438 4193099 := bstep (se 1 (by rfl) ⟨3144824, by rfl⟩ : syracuseStep 4193099 = 6289649) B6289649
theorem B5299033 : Blo 1240438 5299033 := bstep (se 2 (by rfl) ⟨1987137, by rfl⟩ : syracuseStep 5299033 = 3974275) B3974275
theorem B2792321 : Blo 1240438 2792321 := bstep (se 2 (by rfl) ⟨1047120, by rfl⟩ : syracuseStep 2792321 = 2094241) B2094241
theorem B9419651 : Blo 1240438 9419651 := bstep (se 1 (by rfl) ⟨7064738, by rfl⟩ : syracuseStep 9419651 = 14129477) B14129477
theorem B2096023 : Blo 1240438 2096023 := bstep (se 1 (by rfl) ⟨1572017, by rfl⟩ : syracuseStep 2096023 = 3144035) B3144035
theorem B17906609 : Blo 1240438 17906609 := bstep (se 2 (by rfl) ⟨6714978, by rfl⟩ : syracuseStep 17906609 = 13429957) B13429957
theorem B4422593 : Blo 1240438 4422593 := bstep (se 2 (by rfl) ⟨1658472, by rfl⟩ : syracuseStep 4422593 = 3316945) B3316945
theorem B2358209 : Blo 1240438 2358209 := bstep (se 2 (by rfl) ⟨884328, by rfl⟩ : syracuseStep 2358209 = 1768657) B1768657
theorem B2235443 : Blo 1240438 2235443 := bstep (se 1 (by rfl) ⟨1676582, by rfl⟩ : syracuseStep 2235443 = 3353165) B3353165
theorem B2792537 : Blo 1240438 2792537 := bstep (se 2 (by rfl) ⟨1047201, by rfl⟩ : syracuseStep 2792537 = 2094403) B2094403
theorem B2981015 : Blo 1240438 2981015 := bstep (se 1 (by rfl) ⟨2235761, by rfl⟩ : syracuseStep 2981015 = 4471523) B4471523
theorem B9321649 : Blo 1240438 9321649 := bstep (se 2 (by rfl) ⟨3495618, by rfl⟩ : syracuseStep 9321649 = 6991237) B6991237
theorem B2792627 : Blo 1240438 2792627 := bstep (se 1 (by rfl) ⟨2094470, by rfl⟩ : syracuseStep 2792627 = 4188941) B4188941
theorem B1572043 : Blo 1240438 1572043 := bstep (se 1 (by rfl) ⟨1179032, by rfl⟩ : syracuseStep 1572043 = 2358065) B2358065
theorem B2792663 : Blo 1240438 2792663 := bstep (se 1 (by rfl) ⟨2094497, by rfl⟩ : syracuseStep 2792663 = 4188995) B4188995
theorem B4840721 : Blo 1240438 4840721 := bstep (se 2 (by rfl) ⟨1815270, by rfl⟩ : syracuseStep 4840721 = 3630541) B3630541
theorem B2358551 : Blo 1240438 2358551 := bstep (se 1 (by rfl) ⟨1768913, by rfl⟩ : syracuseStep 2358551 = 3537827) B3537827
theorem B2792843 : Blo 1240438 2792843 := bstep (se 1 (by rfl) ⟨2094632, by rfl⟩ : syracuseStep 2792843 = 4189265) B4189265
theorem B5660077 : Blo 1240438 5660077 := bstep (se 3 (by rfl) ⟨1061264, by rfl⟩ : syracuseStep 5660077 = 2122529) B2122529
theorem B2792897 : Blo 1240438 2792897 := bstep (se 2 (by rfl) ⟨1047336, by rfl⟩ : syracuseStep 2792897 = 2094673) B2094673
theorem B2235863 : Blo 1240438 2235863 := bstep (se 1 (by rfl) ⟨1676897, by rfl⟩ : syracuseStep 2235863 = 3353795) B3353795
theorem B1572311 : Blo 1240438 1572311 := bstep (se 1 (by rfl) ⟨1179233, by rfl⟩ : syracuseStep 1572311 = 2358467) B2358467
theorem B2235905 : Blo 1240438 2235905 := bstep (se 2 (by rfl) ⟨838464, by rfl⟩ : syracuseStep 2235905 = 1676929) B1676929
theorem B4709933 : Blo 1240438 4709933 := bstep (se 3 (by rfl) ⟨883112, by rfl⟩ : syracuseStep 4709933 = 1766225) B1766225
theorem B6282845 : Blo 1240438 6282845 := bstep (se 3 (by rfl) ⟨1178033, by rfl⟩ : syracuseStep 6282845 = 2356067) B2356067
theorem B2793113 : Blo 1240438 2793113 := bstep (se 2 (by rfl) ⟨1047417, by rfl⟩ : syracuseStep 2793113 = 2094835) B2094835
theorem B3776203 : Blo 1240438 3776203 := bstep (se 1 (by rfl) ⟨2832152, by rfl⟩ : syracuseStep 3776203 = 5664305) B5664305
theorem B2793203 : Blo 1240438 2793203 := bstep (se 1 (by rfl) ⟨2094902, by rfl⟩ : syracuseStep 2793203 = 4189805) B4189805
theorem B5299991 : Blo 1240438 5299991 := bstep (se 1 (by rfl) ⟨3974993, by rfl⟩ : syracuseStep 5299991 = 7949987) B7949987
theorem B2793239 : Blo 1240438 2793239 := bstep (se 1 (by rfl) ⟨2094929, by rfl⟩ : syracuseStep 2793239 = 4189859) B4189859
theorem B16342901 : Blo 1240438 16342901 := bstep (se 5 (by rfl) ⟨766073, by rfl⟩ : syracuseStep 16342901 = 1532147) B1532147
theorem B16990069 : Blo 1240438 16990069 := bstep (se 5 (by rfl) ⟨796409, by rfl⟩ : syracuseStep 16990069 = 1592819) B1592819
theorem B2686871 : Blo 1240438 2686871 := bstep (se 1 (by rfl) ⟨2015153, by rfl⟩ : syracuseStep 2686871 = 4030307) B4030307
theorem B2793419 : Blo 1240438 2793419 := bstep (se 1 (by rfl) ⟨2095064, by rfl⟩ : syracuseStep 2793419 = 4190129) B4190129
theorem B4538315 : Blo 1240438 4538315 := bstep (se 1 (by rfl) ⟨3403736, by rfl⟩ : syracuseStep 4538315 = 6807473) B6807473
theorem B6283331 : Blo 1240438 6283331 := bstep (se 1 (by rfl) ⟨4712498, by rfl⟩ : syracuseStep 6283331 = 9424997) B9424997
theorem B8954057 : Blo 1240438 8954057 := bstep (se 2 (by rfl) ⟨3357771, by rfl⟩ : syracuseStep 8954057 = 6715543) B6715543
theorem B10060013 : Blo 1240438 10060013 := bstep (se 3 (by rfl) ⟨1886252, by rfl⟩ : syracuseStep 10060013 = 3772505) B3772505
theorem B2793743 : Blo 1240438 2793743 := bstep (se 1 (by rfl) ⟨2095307, by rfl⟩ : syracuseStep 2793743 = 4190615) B4190615
theorem B2793761 : Blo 1240438 2793761 := bstep (se 2 (by rfl) ⟨1047660, by rfl⟩ : syracuseStep 2793761 = 2095321) B2095321
theorem B7070003 : Blo 1240438 7070003 := bstep (se 1 (by rfl) ⟨5302502, by rfl⟩ : syracuseStep 7070003 = 10605005) B10605005
theorem B5030203 : Blo 1240438 5030203 := bstep (se 1 (by rfl) ⟨3772652, by rfl⟩ : syracuseStep 5030203 = 7545305) B7545305
theorem B6283655 : Blo 1240438 6283655 := bstep (se 1 (by rfl) ⟨4712741, by rfl⟩ : syracuseStep 6283655 = 9425483) B9425483
theorem B9077213 : Blo 1240438 9077213 := bstep (se 3 (by rfl) ⟨1701977, by rfl⟩ : syracuseStep 9077213 = 3403955) B3403955
theorem B5964299 : Blo 1240438 5964299 := bstep (se 1 (by rfl) ⟨4473224, by rfl⟩ : syracuseStep 5964299 = 8946449) B8946449
theorem B2236943 : Blo 1240438 2236943 := bstep (se 1 (by rfl) ⟨1677707, by rfl⟩ : syracuseStep 2236943 = 3355415) B3355415
theorem B2794103 : Blo 1240438 2794103 := bstep (se 1 (by rfl) ⟨2095577, by rfl⟩ : syracuseStep 2794103 = 4191155) B4191155
theorem B13083353 : Blo 1240438 13083353 := bstep (se 2 (by rfl) ⟨4906257, by rfl⟩ : syracuseStep 13083353 = 9812515) B9812515
theorem B5030657 : Blo 1240438 5030657 := bstep (se 2 (by rfl) ⟨1886496, by rfl⟩ : syracuseStep 5030657 = 3772993) B3772993
theorem B2794283 : Blo 1240438 2794283 := bstep (se 1 (by rfl) ⟨2095712, by rfl⟩ : syracuseStep 2794283 = 4191425) B4191425
theorem B60400565 : Blo 1240438 60400565 := bstep (se 5 (by rfl) ⟨2831276, by rfl⟩ : syracuseStep 60400565 = 5662553) B5662553
theorem B1860665 : Blo 1240438 1860665 := bstep (se 2 (by rfl) ⟨697749, by rfl⟩ : syracuseStep 1860665 = 1395499) B1395499
theorem B6366275 : Blo 1240438 6366275 := bstep (se 1 (by rfl) ⟨4774706, by rfl⟩ : syracuseStep 6366275 = 9549413) B9549413
theorem B8496215 : Blo 1240438 8496215 := bstep (se 1 (by rfl) ⟨6372161, by rfl⟩ : syracuseStep 8496215 = 12744323) B12744323
theorem B1860743 : Blo 1240438 1860743 := bstep (se 1 (by rfl) ⟨1395557, by rfl⟩ : syracuseStep 1860743 = 2791115) B2791115
theorem B2794643 : Blo 1240438 2794643 := bstep (se 1 (by rfl) ⟨2095982, by rfl⟩ : syracuseStep 2794643 = 4191965) B4191965
theorem B1860779 : Blo 1240438 1860779 := bstep (se 1 (by rfl) ⟨1395584, by rfl⟩ : syracuseStep 1860779 = 2791169) B2791169
theorem B1860809 : Blo 1240438 1860809 := bstep (se 2 (by rfl) ⟨697803, by rfl⟩ : syracuseStep 1860809 = 1395607) B1395607
theorem B2794697 : Blo 1240438 2794697 := bstep (se 2 (by rfl) ⟨1048011, by rfl⟩ : syracuseStep 2794697 = 2096023) B2096023
theorem B15099169 : Blo 1240438 15099169 := bstep (se 2 (by rfl) ⟨5662188, by rfl⟩ : syracuseStep 15099169 = 11324377) B11324377
theorem B1860923 : Blo 1240438 1860923 := bstep (se 1 (by rfl) ⟨1395692, by rfl⟩ : syracuseStep 1860923 = 2791385) B2791385
theorem B2983283 : Blo 1240438 2983283 := bstep (se 1 (by rfl) ⟨2237462, by rfl⟩ : syracuseStep 2983283 = 4474925) B4474925
theorem B1860983 : Blo 1240438 1860983 := bstep (se 1 (by rfl) ⟨1395737, by rfl⟩ : syracuseStep 1860983 = 2791475) B2791475
theorem B1861007 : Blo 1240438 1861007 := bstep (se 1 (by rfl) ⟨1395755, by rfl⟩ : syracuseStep 1861007 = 2791511) B2791511
theorem B11928977 : Blo 1240438 11928977 := bstep (se 2 (by rfl) ⟨4473366, by rfl⟩ : syracuseStep 11928977 = 8946733) B8946733
theorem B2983321 : Blo 1240438 2983321 := bstep (se 2 (by rfl) ⟨1118745, by rfl⟩ : syracuseStep 2983321 = 2237491) B2237491
theorem B1861049 : Blo 1240438 1861049 := bstep (se 2 (by rfl) ⟨697893, by rfl⟩ : syracuseStep 1861049 = 1395787) B1395787
theorem B1861127 : Blo 1240438 1861127 := bstep (se 1 (by rfl) ⟨1395845, by rfl⟩ : syracuseStep 1861127 = 2791691) B2791691
theorem B1861163 : Blo 1240438 1861163 := bstep (se 1 (by rfl) ⟨1395872, by rfl⟩ : syracuseStep 1861163 = 2791745) B2791745
theorem B1861193 : Blo 1240438 1861193 := bstep (se 2 (by rfl) ⟨697947, by rfl⟩ : syracuseStep 1861193 = 1395895) B1395895
theorem B1861307 : Blo 1240438 1861307 := bstep (se 1 (by rfl) ⟨1395980, by rfl⟩ : syracuseStep 1861307 = 2791961) B2791961
theorem B7071461 : Blo 1240438 7071461 := bstep (se 4 (by rfl) ⟨662949, by rfl⟩ : syracuseStep 7071461 = 1325899) B1325899
theorem B1861367 : Blo 1240438 1861367 := bstep (se 1 (by rfl) ⟨1396025, by rfl⟩ : syracuseStep 1861367 = 2792051) B2792051
theorem B1861391 : Blo 1240438 1861391 := bstep (se 1 (by rfl) ⟨1396043, by rfl⟩ : syracuseStep 1861391 = 2792087) B2792087
theorem B5031695 : Blo 1240438 5031695 := bstep (se 1 (by rfl) ⟨3773771, by rfl⟩ : syracuseStep 5031695 = 7547543) B7547543
theorem B1861433 : Blo 1240438 1861433 := bstep (se 2 (by rfl) ⟨698037, by rfl⟩ : syracuseStep 1861433 = 1396075) B1396075
theorem B1861511 : Blo 1240438 1861511 := bstep (se 1 (by rfl) ⟨1396133, by rfl⟩ : syracuseStep 1861511 = 2792267) B2792267
theorem B2795399 : Blo 1240438 2795399 := bstep (se 1 (by rfl) ⟨2096549, by rfl⟩ : syracuseStep 2795399 = 4193099) B4193099
theorem B7546769 : Blo 1240438 7546769 := bstep (se 2 (by rfl) ⟨2830038, by rfl⟩ : syracuseStep 7546769 = 5660077) B5660077
theorem B1861547 : Blo 1240438 1861547 := bstep (se 1 (by rfl) ⟨1396160, by rfl⟩ : syracuseStep 1861547 = 2792321) B2792321
theorem B4712377 : Blo 1240438 4712377 := bstep (se 2 (by rfl) ⟨1767141, by rfl⟩ : syracuseStep 4712377 = 3534283) B3534283
theorem B1861577 : Blo 1240438 1861577 := bstep (se 2 (by rfl) ⟨698091, by rfl⟩ : syracuseStep 1861577 = 1396183) B1396183
theorem B1861691 : Blo 1240438 1861691 := bstep (se 1 (by rfl) ⟨1396268, by rfl⟩ : syracuseStep 1861691 = 2792537) B2792537
theorem B1861751 : Blo 1240438 1861751 := bstep (se 1 (by rfl) ⟨1396313, by rfl⟩ : syracuseStep 1861751 = 2792627) B2792627
theorem B1861775 : Blo 1240438 1861775 := bstep (se 1 (by rfl) ⟨1396331, by rfl⟩ : syracuseStep 1861775 = 2792663) B2792663
theorem B1861817 : Blo 1240438 1861817 := bstep (se 2 (by rfl) ⟨698181, by rfl⟩ : syracuseStep 1861817 = 1396363) B1396363
theorem B14151347 : Blo 1240438 14151347 := bstep (se 1 (by rfl) ⟨10613510, by rfl⟩ : syracuseStep 14151347 = 21227021) B21227021
theorem B1861895 : Blo 1240438 1861895 := bstep (se 1 (by rfl) ⟨1396421, by rfl⟩ : syracuseStep 1861895 = 2792843) B2792843
theorem B1861931 : Blo 1240438 1861931 := bstep (se 1 (by rfl) ⟨1396448, by rfl⟩ : syracuseStep 1861931 = 2792897) B2792897
theorem B1861961 : Blo 1240438 1861961 := bstep (se 2 (by rfl) ⟨698235, by rfl⟩ : syracuseStep 1861961 = 1396471) B1396471
theorem B3139955 : Blo 1240438 3139955 := bstep (se 1 (by rfl) ⟨2354966, by rfl⟩ : syracuseStep 3139955 = 4709933) B4709933
theorem B4188563 : Blo 1240438 4188563 := bstep (se 1 (by rfl) ⟨3141422, by rfl⟩ : syracuseStep 4188563 = 6282845) B6282845
theorem B1862075 : Blo 1240438 1862075 := bstep (se 1 (by rfl) ⟨1396556, by rfl⟩ : syracuseStep 1862075 = 2793113) B2793113
theorem B22653425 : Blo 1240438 22653425 := bstep (se 2 (by rfl) ⟨8495034, by rfl⟩ : syracuseStep 22653425 = 16990069) B16990069
theorem B1862135 : Blo 1240438 1862135 := bstep (se 1 (by rfl) ⟨1396601, by rfl⟩ : syracuseStep 1862135 = 2793203) B2793203
theorem B3533327 : Blo 1240438 3533327 := bstep (se 1 (by rfl) ⟨2649995, by rfl⟩ : syracuseStep 3533327 = 5299991) B5299991
theorem B1862159 : Blo 1240438 1862159 := bstep (se 1 (by rfl) ⟨1396619, by rfl⟩ : syracuseStep 1862159 = 2793239) B2793239
theorem B12102173 : Blo 1240438 12102173 := bstep (se 3 (by rfl) ⟨2269157, by rfl⟩ : syracuseStep 12102173 = 4538315) B4538315
theorem B1862201 : Blo 1240438 1862201 := bstep (se 2 (by rfl) ⟨698325, by rfl⟩ : syracuseStep 1862201 = 1396651) B1396651
theorem B1862279 : Blo 1240438 1862279 := bstep (se 1 (by rfl) ⟨1396709, by rfl⟩ : syracuseStep 1862279 = 2793419) B2793419
theorem B1862315 : Blo 1240438 1862315 := bstep (se 1 (by rfl) ⟨1396736, by rfl⟩ : syracuseStep 1862315 = 2793473) B2793473
theorem B1862345 : Blo 1240438 1862345 := bstep (se 2 (by rfl) ⟨698379, by rfl⟩ : syracuseStep 1862345 = 1396759) B1396759
theorem B2984705 : Blo 1240438 2984705 := bstep (se 2 (by rfl) ⟨1119264, by rfl⟩ : syracuseStep 2984705 = 2238529) B2238529
theorem B1862459 : Blo 1240438 1862459 := bstep (se 1 (by rfl) ⟨1396844, by rfl⟩ : syracuseStep 1862459 = 2793689) B2793689
theorem B3140471 : Blo 1240438 3140471 := bstep (se 1 (by rfl) ⟨2355353, by rfl⟩ : syracuseStep 3140471 = 4710707) B4710707
theorem B1862519 : Blo 1240438 1862519 := bstep (se 1 (by rfl) ⟨1396889, by rfl⟩ : syracuseStep 1862519 = 2793779) B2793779
theorem B1862543 : Blo 1240438 1862543 := bstep (se 1 (by rfl) ⟨1396907, by rfl⟩ : syracuseStep 1862543 = 2793815) B2793815
theorem B6712211 : Blo 1240438 6712211 := bstep (se 1 (by rfl) ⟨5034158, by rfl⟩ : syracuseStep 6712211 = 10068317) B10068317
theorem B3976121 : Blo 1240438 3976121 := bstep (se 2 (by rfl) ⟨1491045, by rfl⟩ : syracuseStep 3976121 = 2982091) B2982091
theorem B1862585 : Blo 1240438 1862585 := bstep (se 2 (by rfl) ⟨698469, by rfl⟩ : syracuseStep 1862585 = 1396939) B1396939
theorem B1395643 : Blo 1240438 1395643 := bstep (se 1 (by rfl) ⟨1046732, by rfl⟩ : syracuseStep 1395643 = 2093465) B2093465
theorem B1862663 : Blo 1240438 1862663 := bstep (se 1 (by rfl) ⟨1396997, by rfl⟩ : syracuseStep 1862663 = 2793995) B2793995
theorem B2984975 : Blo 1240438 2984975 := bstep (se 1 (by rfl) ⟨2238731, by rfl⟩ : syracuseStep 2984975 = 4477463) B4477463
theorem B5303339 : Blo 1240438 5303339 := bstep (se 1 (by rfl) ⟨3977504, by rfl⟩ : syracuseStep 5303339 = 7955009) B7955009
theorem B1862699 : Blo 1240438 1862699 := bstep (se 1 (by rfl) ⟨1397024, by rfl⟩ : syracuseStep 1862699 = 2794049) B2794049
theorem B1862729 : Blo 1240438 1862729 := bstep (se 2 (by rfl) ⟨698523, by rfl⟩ : syracuseStep 1862729 = 1397047) B1397047
theorem B1592507 : Blo 1240438 1592507 := bstep (se 1 (by rfl) ⟨1194380, by rfl⟩ : syracuseStep 1592507 = 2388761) B2388761
theorem B1862843 : Blo 1240438 1862843 := bstep (se 1 (by rfl) ⟨1397132, by rfl⟩ : syracuseStep 1862843 = 2794265) B2794265
theorem B1862903 : Blo 1240438 1862903 := bstep (se 1 (by rfl) ⟨1397177, by rfl⟩ : syracuseStep 1862903 = 2794355) B2794355
theorem B1862927 : Blo 1240438 1862927 := bstep (se 1 (by rfl) ⟨1397195, by rfl⟩ : syracuseStep 1862927 = 2794391) B2794391
theorem B1862969 : Blo 1240438 1862969 := bstep (se 2 (by rfl) ⟨698613, by rfl⟩ : syracuseStep 1862969 = 1397227) B1397227
theorem B7064921 : Blo 1240438 7064921 := bstep (se 2 (by rfl) ⟨2649345, by rfl⟩ : syracuseStep 7064921 = 5298691) B5298691
theorem B1240455 : Blo 1240438 1240455 := bstep (se 1 (by rfl) ⟨930341, by rfl⟩ : syracuseStep 1240455 = 1860683) B1860683
theorem B1863047 : Blo 1240438 1863047 := bstep (se 1 (by rfl) ⟨1397285, by rfl⟩ : syracuseStep 1863047 = 2794571) B2794571
theorem B1240463 : Blo 1240438 1240463 := bstep (se 1 (by rfl) ⟨930347, by rfl⟩ : syracuseStep 1240463 = 1860695) B1860695
theorem B1396111 : Blo 1240438 1396111 := bstep (se 1 (by rfl) ⟨1047083, by rfl⟩ : syracuseStep 1396111 = 2094167) B2094167
theorem B1863083 : Blo 1240438 1863083 := bstep (se 1 (by rfl) ⟨1397312, by rfl⟩ : syracuseStep 1863083 = 2794625) B2794625
theorem B24178105 : Blo 1240438 24178105 := bstep (se 2 (by rfl) ⟨9066789, by rfl⟩ : syracuseStep 24178105 = 18133579) B18133579
theorem B1240507 : Blo 1240438 1240507 := bstep (se 1 (by rfl) ⟨930380, by rfl⟩ : syracuseStep 1240507 = 1860761) B1860761
theorem B1863113 : Blo 1240438 1863113 := bstep (se 2 (by rfl) ⟨698667, by rfl⟩ : syracuseStep 1863113 = 1397335) B1397335
theorem B1240583 : Blo 1240438 1240583 := bstep (se 1 (by rfl) ⟨930437, by rfl⟩ : syracuseStep 1240583 = 1860875) B1860875
theorem B1240591 : Blo 1240438 1240591 := bstep (se 1 (by rfl) ⟨930443, by rfl⟩ : syracuseStep 1240591 = 1860887) B1860887
theorem B1240635 : Blo 1240438 1240635 := bstep (se 1 (by rfl) ⟨930476, by rfl⟩ : syracuseStep 1240635 = 1860953) B1860953
theorem B1863227 : Blo 1240438 1863227 := bstep (se 1 (by rfl) ⟨1397420, by rfl⟩ : syracuseStep 1863227 = 2794841) B2794841
theorem B7958083 : Blo 1240438 7958083 := bstep (se 1 (by rfl) ⟨5968562, by rfl⟩ : syracuseStep 7958083 = 11937125) B11937125
theorem B32681573 : Blo 1240438 32681573 := bstep (se 4 (by rfl) ⟨3063897, by rfl⟩ : syracuseStep 32681573 = 6127795) B6127795
theorem B3534455 : Blo 1240438 3534455 := bstep (se 1 (by rfl) ⟨2650841, by rfl⟩ : syracuseStep 3534455 = 5301683) B5301683
theorem B1863287 : Blo 1240438 1863287 := bstep (se 1 (by rfl) ⟨1397465, by rfl⟩ : syracuseStep 1863287 = 2794931) B2794931
theorem B1240711 : Blo 1240438 1240711 := bstep (se 1 (by rfl) ⟨930533, by rfl⟩ : syracuseStep 1240711 = 1861067) B1861067
theorem B1240719 : Blo 1240438 1240719 := bstep (se 1 (by rfl) ⟨930539, by rfl⟩ : syracuseStep 1240719 = 1861079) B1861079
theorem B1863311 : Blo 1240438 1863311 := bstep (se 1 (by rfl) ⟨1397483, by rfl⟩ : syracuseStep 1863311 = 2794967) B2794967
theorem B21507763 : Blo 1240438 21507763 := bstep (se 1 (by rfl) ⟨16130822, by rfl⟩ : syracuseStep 21507763 = 32261645) B32261645
theorem B1240763 : Blo 1240438 1240763 := bstep (se 1 (by rfl) ⟨930572, by rfl⟩ : syracuseStep 1240763 = 1861145) B1861145
theorem B1863353 : Blo 1240438 1863353 := bstep (se 2 (by rfl) ⟨698757, by rfl⟩ : syracuseStep 1863353 = 1397515) B1397515
theorem B10612417 : Blo 1240438 10612417 := bstep (se 2 (by rfl) ⟨3979656, by rfl⟩ : syracuseStep 10612417 = 7959313) B7959313
theorem B20139749 : Blo 1240438 20139749 := bstep (se 4 (by rfl) ⟨1888101, by rfl⟩ : syracuseStep 20139749 = 3776203) B3776203
theorem B1240839 : Blo 1240438 1240839 := bstep (se 1 (by rfl) ⟨930629, by rfl⟩ : syracuseStep 1240839 = 1861259) B1861259
theorem B1863431 : Blo 1240438 1863431 := bstep (se 1 (by rfl) ⟨1397573, by rfl⟩ : syracuseStep 1863431 = 2795147) B2795147
theorem B1240847 : Blo 1240438 1240847 := bstep (se 1 (by rfl) ⟨930635, by rfl⟩ : syracuseStep 1240847 = 1861271) B1861271
theorem B4189967 : Blo 1240438 4189967 := bstep (se 1 (by rfl) ⟨3142475, by rfl⟩ : syracuseStep 4189967 = 6284951) B6284951
theorem B7065377 : Blo 1240438 7065377 := bstep (se 2 (by rfl) ⟨2649516, by rfl⟩ : syracuseStep 7065377 = 5299033) B5299033
theorem B5451553 : Blo 1240438 5451553 := bstep (se 2 (by rfl) ⟨2044332, by rfl⟩ : syracuseStep 5451553 = 4088665) B4088665
theorem B1863467 : Blo 1240438 1863467 := bstep (se 1 (by rfl) ⟨1397600, by rfl⟩ : syracuseStep 1863467 = 2795201) B2795201
theorem B1240891 : Blo 1240438 1240891 := bstep (se 1 (by rfl) ⟨930668, by rfl⟩ : syracuseStep 1240891 = 1861337) B1861337
theorem B1863497 : Blo 1240438 1863497 := bstep (se 2 (by rfl) ⟨698811, by rfl⟩ : syracuseStep 1863497 = 1397623) B1397623
theorem B3141463 : Blo 1240438 3141463 := bstep (se 1 (by rfl) ⟨2356097, by rfl⟩ : syracuseStep 3141463 = 4712195) B4712195
theorem B6287219 : Blo 1240438 6287219 := bstep (se 1 (by rfl) ⟨4715414, by rfl⟩ : syracuseStep 6287219 = 9430829) B9430829
theorem B1240967 : Blo 1240438 1240967 := bstep (se 1 (by rfl) ⟨930725, by rfl⟩ : syracuseStep 1240967 = 1861451) B1861451
theorem B1396615 : Blo 1240438 1396615 := bstep (se 1 (by rfl) ⟨1047461, by rfl⟩ : syracuseStep 1396615 = 2094923) B2094923
theorem B1240975 : Blo 1240438 1240975 := bstep (se 1 (by rfl) ⟨930731, by rfl⟩ : syracuseStep 1240975 = 1861463) B1861463
theorem B1241019 : Blo 1240438 1241019 := bstep (se 1 (by rfl) ⟨930764, by rfl⟩ : syracuseStep 1241019 = 1861529) B1861529
theorem B1863611 : Blo 1240438 1863611 := bstep (se 1 (by rfl) ⟨1397708, by rfl⟩ : syracuseStep 1863611 = 2795417) B2795417
theorem B1241095 : Blo 1240438 1241095 := bstep (se 1 (by rfl) ⟨930821, by rfl⟩ : syracuseStep 1241095 = 1861643) B1861643
theorem B1241103 : Blo 1240438 1241103 := bstep (se 1 (by rfl) ⟨930827, by rfl⟩ : syracuseStep 1241103 = 1861655) B1861655
theorem B7065629 : Blo 1240438 7065629 := bstep (se 3 (by rfl) ⟨1324805, by rfl⟩ : syracuseStep 7065629 = 2649611) B2649611
theorem B4190237 : Blo 1240438 4190237 := bstep (se 3 (by rfl) ⟨785669, by rfl⟩ : syracuseStep 4190237 = 1571339) B1571339
theorem B1241147 : Blo 1240438 1241147 := bstep (se 1 (by rfl) ⟨930860, by rfl⟩ : syracuseStep 1241147 = 1861721) B1861721
theorem B1396795 : Blo 1240438 1396795 := bstep (se 1 (by rfl) ⟨1047596, by rfl⟩ : syracuseStep 1396795 = 2095193) B2095193
theorem B3141767 : Blo 1240438 3141767 := bstep (se 1 (by rfl) ⟨2356325, by rfl⟩ : syracuseStep 3141767 = 4712651) B4712651
theorem B1241223 : Blo 1240438 1241223 := bstep (se 1 (by rfl) ⟨930917, by rfl⟩ : syracuseStep 1241223 = 1861835) B1861835
theorem B1241231 : Blo 1240438 1241231 := bstep (se 1 (by rfl) ⟨930923, by rfl⟩ : syracuseStep 1241231 = 1861847) B1861847
theorem B1241275 : Blo 1240438 1241275 := bstep (se 1 (by rfl) ⟨930956, by rfl⟩ : syracuseStep 1241275 = 1861913) B1861913
theorem B1241351 : Blo 1240438 1241351 := bstep (se 1 (by rfl) ⟨931013, by rfl⟩ : syracuseStep 1241351 = 1862027) B1862027
theorem B3141899 : Blo 1240438 3141899 := bstep (se 1 (by rfl) ⟨2356424, by rfl⟩ : syracuseStep 3141899 = 4712849) B4712849
theorem B1241359 : Blo 1240438 1241359 := bstep (se 1 (by rfl) ⟨931019, by rfl⟩ : syracuseStep 1241359 = 1862039) B1862039
theorem B1241403 : Blo 1240438 1241403 := bstep (se 1 (by rfl) ⟨931052, by rfl⟩ : syracuseStep 1241403 = 1862105) B1862105
theorem B3977531 : Blo 1240438 3977531 := bstep (se 1 (by rfl) ⟨2983148, by rfl⟩ : syracuseStep 3977531 = 5966297) B5966297
theorem B6287705 : Blo 1240438 6287705 := bstep (se 2 (by rfl) ⟨2357889, by rfl⟩ : syracuseStep 6287705 = 4715779) B4715779
theorem B2093431 : Blo 1240438 2093431 := bstep (se 1 (by rfl) ⟨1570073, by rfl⟩ : syracuseStep 2093431 = 3140147) B3140147
theorem B1241479 : Blo 1240438 1241479 := bstep (se 1 (by rfl) ⟨931109, by rfl⟩ : syracuseStep 1241479 = 1862219) B1862219
theorem B1241487 : Blo 1240438 1241487 := bstep (se 1 (by rfl) ⟨931115, by rfl⟩ : syracuseStep 1241487 = 1862231) B1862231
theorem B1241531 : Blo 1240438 1241531 := bstep (se 1 (by rfl) ⟨931148, by rfl⟩ : syracuseStep 1241531 = 1862297) B1862297
theorem B1241607 : Blo 1240438 1241607 := bstep (se 1 (by rfl) ⟨931205, by rfl⟩ : syracuseStep 1241607 = 1862411) B1862411
theorem B1987087 : Blo 1240438 1987087 := bstep (se 1 (by rfl) ⟨1490315, by rfl⟩ : syracuseStep 1987087 = 2980631) B2980631
theorem B1241615 : Blo 1240438 1241615 := bstep (se 1 (by rfl) ⟨931211, by rfl⟩ : syracuseStep 1241615 = 1862423) B1862423
theorem B1397263 : Blo 1240438 1397263 := bstep (se 1 (by rfl) ⟨1047947, by rfl⟩ : syracuseStep 1397263 = 2095895) B2095895
theorem B2093627 : Blo 1240438 2093627 := bstep (se 1 (by rfl) ⟨1570220, by rfl⟩ : syracuseStep 2093627 = 3140441) B3140441
theorem B1241659 : Blo 1240438 1241659 := bstep (se 1 (by rfl) ⟨931244, by rfl⟩ : syracuseStep 1241659 = 1862489) B1862489
theorem B6279767 : Blo 1240438 6279767 := bstep (se 1 (by rfl) ⟨4709825, by rfl⟩ : syracuseStep 6279767 = 9419651) B9419651
theorem B1241735 : Blo 1240438 1241735 := bstep (se 1 (by rfl) ⟨931301, by rfl⟩ : syracuseStep 1241735 = 1862603) B1862603
theorem B1241743 : Blo 1240438 1241743 := bstep (se 1 (by rfl) ⟨931307, by rfl⟩ : syracuseStep 1241743 = 1862615) B1862615
theorem B1241787 : Blo 1240438 1241787 := bstep (se 1 (by rfl) ⟨931340, by rfl⟩ : syracuseStep 1241787 = 1862681) B1862681
theorem B1241863 : Blo 1240438 1241863 := bstep (se 1 (by rfl) ⟨931397, by rfl⟩ : syracuseStep 1241863 = 1862795) B1862795
theorem B1987343 : Blo 1240438 1987343 := bstep (se 1 (by rfl) ⟨1490507, by rfl⟩ : syracuseStep 1987343 = 2981015) B2981015
theorem B3142415 : Blo 1240438 3142415 := bstep (se 1 (by rfl) ⟨2356811, by rfl⟩ : syracuseStep 3142415 = 4713623) B4713623
theorem B1241871 : Blo 1240438 1241871 := bstep (se 1 (by rfl) ⟨931403, by rfl⟩ : syracuseStep 1241871 = 1862807) B1862807
theorem B4715279 : Blo 1240438 4715279 := bstep (se 1 (by rfl) ⟨3536459, by rfl⟩ : syracuseStep 4715279 = 7072919) B7072919
theorem B3773213 : Blo 1240438 3773213 := bstep (se 3 (by rfl) ⟨707477, by rfl⟩ : syracuseStep 3773213 = 1414955) B1414955
theorem B1241915 : Blo 1240438 1241915 := bstep (se 1 (by rfl) ⟨931436, by rfl⟩ : syracuseStep 1241915 = 1862873) B1862873
theorem B3978119 : Blo 1240438 3978119 := bstep (se 1 (by rfl) ⟨2983589, by rfl⟩ : syracuseStep 3978119 = 5967179) B5967179
theorem B1241991 : Blo 1240438 1241991 := bstep (se 1 (by rfl) ⟨931493, by rfl⟩ : syracuseStep 1241991 = 1862987) B1862987
theorem B1241999 : Blo 1240438 1241999 := bstep (se 1 (by rfl) ⟨931499, by rfl⟩ : syracuseStep 1241999 = 1862999) B1862999
theorem B3142547 : Blo 1240438 3142547 := bstep (se 1 (by rfl) ⟨2356910, by rfl⟩ : syracuseStep 3142547 = 4713821) B4713821
theorem B1242043 : Blo 1240438 1242043 := bstep (se 1 (by rfl) ⟨931532, by rfl⟩ : syracuseStep 1242043 = 1863065) B1863065
theorem B2094025 : Blo 1240438 2094025 := bstep (se 2 (by rfl) ⟨785259, by rfl⟩ : syracuseStep 2094025 = 1570519) B1570519
theorem B1242119 : Blo 1240438 1242119 := bstep (se 1 (by rfl) ⟨931589, by rfl⟩ : syracuseStep 1242119 = 1863179) B1863179
theorem B1242127 : Blo 1240438 1242127 := bstep (se 1 (by rfl) ⟨931595, by rfl⟩ : syracuseStep 1242127 = 1863191) B1863191
theorem B1242171 : Blo 1240438 1242171 := bstep (se 1 (by rfl) ⟨931628, by rfl⟩ : syracuseStep 1242171 = 1863257) B1863257
theorem B6280253 : Blo 1240438 6280253 := bstep (se 3 (by rfl) ⟨1177547, by rfl⟩ : syracuseStep 6280253 = 2355095) B2355095
theorem B7164989 : Blo 1240438 7164989 := bstep (se 3 (by rfl) ⟨1343435, by rfl⟩ : syracuseStep 7164989 = 2686871) B2686871
theorem B1242247 : Blo 1240438 1242247 := bstep (se 1 (by rfl) ⟨931685, by rfl⟩ : syracuseStep 1242247 = 1863371) B1863371
theorem B1242255 : Blo 1240438 1242255 := bstep (se 1 (by rfl) ⟨931691, by rfl⟩ : syracuseStep 1242255 = 1863383) B1863383
theorem B1242299 : Blo 1240438 1242299 := bstep (se 1 (by rfl) ⟨931724, by rfl⟩ : syracuseStep 1242299 = 1863449) B1863449
theorem B3536129 : Blo 1240438 3536129 := bstep (se 2 (by rfl) ⟨1326048, by rfl⟩ : syracuseStep 3536129 = 2652097) B2652097
theorem B1242375 : Blo 1240438 1242375 := bstep (se 1 (by rfl) ⟨931781, by rfl⟩ : syracuseStep 1242375 = 1863563) B1863563
theorem B1242383 : Blo 1240438 1242383 := bstep (se 1 (by rfl) ⟨931787, by rfl⟩ : syracuseStep 1242383 = 1863575) B1863575
theorem B3355933 : Blo 1240438 3355933 := bstep (se 3 (by rfl) ⟨629237, by rfl⟩ : syracuseStep 3355933 = 1258475) B1258475
theorem B2356523 : Blo 1240438 2356523 := bstep (se 1 (by rfl) ⟨1767392, by rfl⟩ : syracuseStep 2356523 = 3534785) B3534785
theorem B1242427 : Blo 1240438 1242427 := bstep (se 1 (by rfl) ⟨931820, by rfl⟩ : syracuseStep 1242427 = 1863641) B1863641
theorem B12744029 : Blo 1240438 12744029 := bstep (se 3 (by rfl) ⟨2389505, by rfl⟩ : syracuseStep 12744029 = 4779011) B4779011
theorem B3536243 : Blo 1240438 3536243 := bstep (se 1 (by rfl) ⟨2652182, by rfl⟩ : syracuseStep 3536243 = 5304365) B5304365
theorem B4191641 : Blo 1240438 4191641 := bstep (se 2 (by rfl) ⟨1571865, by rfl⟩ : syracuseStep 4191641 = 3143731) B3143731
theorem B6714809 : Blo 1240438 6714809 := bstep (se 2 (by rfl) ⟨2518053, by rfl⟩ : syracuseStep 6714809 = 5036107) B5036107
theorem B2356751 : Blo 1240438 2356751 := bstep (se 1 (by rfl) ⟨1767563, by rfl⟩ : syracuseStep 2356751 = 3535127) B3535127
theorem B1766971 : Blo 1240438 1766971 := bstep (se 1 (by rfl) ⟨1325228, by rfl⟩ : syracuseStep 1766971 = 2650457) B2650457
theorem B1570423 : Blo 1240438 1570423 := bstep (se 1 (by rfl) ⟨1177817, by rfl⟩ : syracuseStep 1570423 = 2355635) B2355635
theorem B2094727 : Blo 1240438 2094727 := bstep (se 1 (by rfl) ⟨1571045, by rfl⟩ : syracuseStep 2094727 = 3142091) B3142091
theorem B42981043 : Blo 1240438 42981043 := bstep (se 1 (by rfl) ⟨32235782, by rfl⟩ : syracuseStep 42981043 = 64471565) B64471565
theorem B2791097 : Blo 1240438 2791097 := bstep (se 2 (by rfl) ⟨1046661, by rfl⟩ : syracuseStep 2791097 = 2093323) B2093323
theorem B7550657 : Blo 1240438 7550657 := bstep (se 2 (by rfl) ⟨2831496, by rfl⟩ : syracuseStep 7550657 = 5662993) B5662993
theorem B3536585 : Blo 1240438 3536585 := bstep (se 2 (by rfl) ⟨1326219, by rfl⟩ : syracuseStep 3536585 = 2652439) B2652439
theorem B5306057 : Blo 1240438 5306057 := bstep (se 2 (by rfl) ⟨1989771, by rfl⟩ : syracuseStep 5306057 = 3979543) B3979543
theorem B23844725 : Blo 1240438 23844725 := bstep (se 5 (by rfl) ⟨1117721, by rfl⟩ : syracuseStep 23844725 = 2235443) B2235443
theorem B1988471 : Blo 1240438 1988471 := bstep (se 1 (by rfl) ⟨1491353, by rfl⟩ : syracuseStep 1988471 = 2982707) B2982707
theorem B2832263 : Blo 1240438 2832263 := bstep (se 1 (by rfl) ⟨2124197, by rfl⟩ : syracuseStep 2832263 = 4248395) B4248395
theorem B1570747 : Blo 1240438 1570747 := bstep (se 1 (by rfl) ⟨1178060, by rfl⟩ : syracuseStep 1570747 = 2356121) B2356121
theorem B1767415 : Blo 1240438 1767415 := bstep (se 1 (by rfl) ⟨1325561, by rfl⟩ : syracuseStep 1767415 = 2651123) B2651123
theorem B3143681 : Blo 1240438 3143681 := bstep (se 2 (by rfl) ⟨1178880, by rfl⟩ : syracuseStep 3143681 = 2357761) B2357761
theorem B2791439 : Blo 1240438 2791439 := bstep (se 1 (by rfl) ⟨2093579, by rfl⟩ : syracuseStep 2791439 = 4187159) B4187159
theorem B2791457 : Blo 1240438 2791457 := bstep (se 2 (by rfl) ⟨1046796, by rfl⟩ : syracuseStep 2791457 = 2093593) B2093593
theorem B5969987 : Blo 1240438 5969987 := bstep (se 1 (by rfl) ⟨4477490, by rfl⟩ : syracuseStep 5969987 = 8954981) B8954981
theorem B4192343 : Blo 1240438 4192343 := bstep (se 1 (by rfl) ⟨3144257, by rfl⟩ : syracuseStep 4192343 = 6288515) B6288515
theorem B13433033 : Blo 1240438 13433033 := bstep (se 2 (by rfl) ⟨5037387, by rfl⟩ : syracuseStep 13433033 = 10074775) B10074775
theorem B49715461 : Blo 1240438 49715461 := bstep (se 4 (by rfl) ⟨4660824, by rfl⟩ : syracuseStep 49715461 = 9321649) B9321649
theorem B2095375 : Blo 1240438 2095375 := bstep (se 1 (by rfl) ⟨1571531, by rfl⟩ : syracuseStep 2095375 = 3143063) B3143063
theorem B7068019 : Blo 1240438 7068019 := bstep (se 1 (by rfl) ⟨5301014, by rfl⟩ : syracuseStep 7068019 = 10602029) B10602029
theorem B2791799 : Blo 1240438 2791799 := bstep (se 1 (by rfl) ⟨2093849, by rfl⟩ : syracuseStep 2791799 = 4187699) B4187699
theorem B1988983 : Blo 1240438 1988983 := bstep (se 1 (by rfl) ⟨1491737, by rfl⟩ : syracuseStep 1988983 = 2983475) B2983475
theorem B3144055 : Blo 1240438 3144055 := bstep (se 1 (by rfl) ⟨2358041, by rfl⟩ : syracuseStep 3144055 = 4716083) B4716083
theorem B8952211 : Blo 1240438 8952211 := bstep (se 1 (by rfl) ⟨6714158, by rfl⟩ : syracuseStep 8952211 = 13428317) B13428317
theorem B6289811 : Blo 1240438 6289811 := bstep (se 1 (by rfl) ⟨4717358, by rfl⟩ : syracuseStep 6289811 = 9434717) B9434717
theorem B9066937 : Blo 1240438 9066937 := bstep (se 2 (by rfl) ⟨3400101, by rfl⟩ : syracuseStep 9066937 = 6800203) B6800203
theorem B2791979 : Blo 1240438 2791979 := bstep (se 1 (by rfl) ⟨2093984, by rfl⟩ : syracuseStep 2791979 = 4187969) B4187969
theorem B4192829 : Blo 1240438 4192829 := bstep (se 3 (by rfl) ⟨786155, by rfl⟩ : syracuseStep 4192829 = 1572311) B1572311
theorem B20142863 : Blo 1240438 20142863 := bstep (se 1 (by rfl) ⟨15107147, by rfl⟩ : syracuseStep 20142863 = 30214295) B30214295
theorem B1768235 : Blo 1240438 1768235 := bstep (se 1 (by rfl) ⟨1326176, by rfl⟩ : syracuseStep 1768235 = 2652353) B2652353
theorem B2095915 : Blo 1240438 2095915 := bstep (se 1 (by rfl) ⟨1571936, by rfl⟩ : syracuseStep 2095915 = 3143873) B3143873
theorem B3144491 : Blo 1240438 3144491 := bstep (se 1 (by rfl) ⟨2358368, by rfl⟩ : syracuseStep 3144491 = 4716737) B4716737
theorem B6282035 : Blo 1240438 6282035 := bstep (se 1 (by rfl) ⟨4711526, by rfl⟩ : syracuseStep 6282035 = 9423053) B9423053
theorem B1571719 : Blo 1240438 1571719 := bstep (se 1 (by rfl) ⟨1178789, by rfl⟩ : syracuseStep 1571719 = 2357579) B2357579
theorem B5962643 : Blo 1240438 5962643 := bstep (se 1 (by rfl) ⟨4471982, by rfl⟩ : syracuseStep 5962643 = 8943965) B8943965
theorem B2792339 : Blo 1240438 2792339 := bstep (se 1 (by rfl) ⟨2094254, by rfl⟩ : syracuseStep 2792339 = 4188509) B4188509
theorem B2358163 : Blo 1240438 2358163 := bstep (se 1 (by rfl) ⟨1768622, by rfl⟩ : syracuseStep 2358163 = 3537245) B3537245
theorem B2096057 : Blo 1240438 2096057 := bstep (se 2 (by rfl) ⟨786021, by rfl⟩ : syracuseStep 2096057 = 1572043) B1572043
theorem B2792393 : Blo 1240438 2792393 := bstep (se 2 (by rfl) ⟨1047147, by rfl⟩ : syracuseStep 2792393 = 2094295) B2094295
theorem B6282359 : Blo 1240438 6282359 := bstep (se 1 (by rfl) ⟨4711769, by rfl⟩ : syracuseStep 6282359 = 9423539) B9423539
theorem B2358391 : Blo 1240438 2358391 := bstep (se 1 (by rfl) ⟨1768793, by rfl⟩ : syracuseStep 2358391 = 3537587) B3537587
theorem B6372553 : Blo 1240438 6372553 := bstep (se 2 (by rfl) ⟨2389707, by rfl⟩ : syracuseStep 6372553 = 4779415) B4779415
theorem B4775183 : Blo 1240438 4775183 := bstep (se 1 (by rfl) ⟨3581387, by rfl⟩ : syracuseStep 4775183 = 7162775) B7162775
theorem B2948395 : Blo 1240438 2948395 := bstep (se 1 (by rfl) ⟨2211296, by rfl⟩ : syracuseStep 2948395 = 4422593) B4422593
theorem B1572139 : Blo 1240438 1572139 := bstep (se 1 (by rfl) ⟨1179104, by rfl⟩ : syracuseStep 1572139 = 2358209) B2358209
theorem B1989931 : Blo 1240438 1989931 := bstep (se 1 (by rfl) ⟨1492448, by rfl⟩ : syracuseStep 1989931 = 2984897) B2984897
theorem B3227147 : Blo 1240438 3227147 := bstep (se 1 (by rfl) ⟨2420360, by rfl⟩ : syracuseStep 3227147 = 4840721) B4840721
theorem B1572367 : Blo 1240438 1572367 := bstep (se 1 (by rfl) ⟨1179275, by rfl⟩ : syracuseStep 1572367 = 2358551) B2358551
theorem B4595287 : Blo 1240438 4595287 := bstep (se 1 (by rfl) ⟨3446465, by rfl⟩ : syracuseStep 4595287 = 6892931) B6892931
theorem B2793095 : Blo 1240438 2793095 := bstep (se 1 (by rfl) ⟨2094821, by rfl⟩ : syracuseStep 2793095 = 4189643) B4189643
theorem B1490575 : Blo 1240438 1490575 := bstep (se 1 (by rfl) ⟨1117931, by rfl⟩ : syracuseStep 1490575 = 2235863) B2235863
theorem B1490603 : Blo 1240438 1490603 := bstep (se 1 (by rfl) ⟨1117952, by rfl⟩ : syracuseStep 1490603 = 2235905) B2235905
theorem B8953537 : Blo 1240438 8953537 := bstep (se 2 (by rfl) ⟨3357576, by rfl⟩ : syracuseStep 8953537 = 6715153) B6715153
theorem B7069477 : Blo 1240438 7069477 := bstep (se 4 (by rfl) ⟨662763, by rfl⟩ : syracuseStep 7069477 = 1325527) B1325527
theorem B47750957 : Blo 1240438 47750957 := bstep (se 3 (by rfl) ⟨8953304, by rfl⟩ : syracuseStep 47750957 = 17906609) B17906609
theorem B2793275 : Blo 1240438 2793275 := bstep (se 1 (by rfl) ⟨2094956, by rfl⟩ : syracuseStep 2793275 = 4189913) B4189913
theorem B24207173 : Blo 1240438 24207173 := bstep (se 4 (by rfl) ⟨2269422, by rfl⟩ : syracuseStep 24207173 = 4538845) B4538845
theorem B10895267 : Blo 1240438 10895267 := bstep (se 1 (by rfl) ⟨8171450, by rfl⟩ : syracuseStep 10895267 = 16342901) B16342901
theorem B2793401 : Blo 1240438 2793401 := bstep (se 2 (by rfl) ⟨1047525, by rfl⟩ : syracuseStep 2793401 = 2095051) B2095051
theorem B4710419 : Blo 1240438 4710419 := bstep (se 1 (by rfl) ⟨3532814, by rfl⟩ : syracuseStep 4710419 = 7065629) B7065629
theorem B2793491 : Blo 1240438 2793491 := bstep (se 1 (by rfl) ⟨2095118, by rfl⟩ : syracuseStep 2793491 = 4190237) B4190237
theorem B1491295 : Blo 1240438 1491295 := bstep (se 1 (by rfl) ⟨1118471, by rfl⟩ : syracuseStep 1491295 = 2236943) B2236943
theorem B2793833 : Blo 1240438 2793833 := bstep (se 2 (by rfl) ⟨1047687, by rfl⟩ : syracuseStep 2793833 = 2095375) B2095375
theorem B4186511 : Blo 1240438 4186511 := bstep (se 1 (by rfl) ⟨3139883, by rfl⟩ : syracuseStep 4186511 = 6279767) B6279767
theorem B2515475 : Blo 1240438 2515475 := bstep (se 1 (by rfl) ⟨1886606, by rfl⟩ : syracuseStep 2515475 = 3773213) B3773213
theorem B11936281 : Blo 1240438 11936281 := bstep (se 2 (by rfl) ⟨4476105, by rfl⟩ : syracuseStep 11936281 = 8952211) B8952211
theorem B4186835 : Blo 1240438 4186835 := bstep (se 1 (by rfl) ⟨3140126, by rfl⟩ : syracuseStep 4186835 = 6280253) B6280253
theorem B4776659 : Blo 1240438 4776659 := bstep (se 1 (by rfl) ⟨3582494, by rfl⟩ : syracuseStep 4776659 = 7164989) B7164989
theorem B4244183 : Blo 1240438 4244183 := bstep (se 1 (by rfl) ⟨3183137, by rfl⟩ : syracuseStep 4244183 = 6366275) B6366275
theorem B8496019 : Blo 1240438 8496019 := bstep (se 1 (by rfl) ⟨6372014, by rfl⟩ : syracuseStep 8496019 = 12744029) B12744029
theorem B2794427 : Blo 1240438 2794427 := bstep (se 1 (by rfl) ⟨2095820, by rfl⟩ : syracuseStep 2794427 = 4191641) B4191641
theorem B2794553 : Blo 1240438 2794553 := bstep (se 2 (by rfl) ⟨1047957, by rfl⟩ : syracuseStep 2794553 = 2095915) B2095915
theorem B1860731 : Blo 1240438 1860731 := bstep (se 1 (by rfl) ⟨1395548, by rfl⟩ : syracuseStep 1860731 = 2791097) B2791097
theorem B1860857 : Blo 1240438 1860857 := bstep (se 2 (by rfl) ⟨697821, by rfl⟩ : syracuseStep 1860857 = 1395643) B1395643
theorem B5031179 : Blo 1240438 5031179 := bstep (se 1 (by rfl) ⟨3773384, by rfl⟩ : syracuseStep 5031179 = 7546769) B7546769
theorem B1860959 : Blo 1240438 1860959 := bstep (se 1 (by rfl) ⟨1395719, by rfl⟩ : syracuseStep 1860959 = 2791439) B2791439
theorem B1860971 : Blo 1240438 1860971 := bstep (se 1 (by rfl) ⟨1395728, by rfl⟩ : syracuseStep 1860971 = 2791457) B2791457
theorem B2794895 : Blo 1240438 2794895 := bstep (se 1 (by rfl) ⟨2096171, by rfl⟩ : syracuseStep 2794895 = 4192343) B4192343
theorem B8955355 : Blo 1240438 8955355 := bstep (se 1 (by rfl) ⟨6716516, by rfl⟩ : syracuseStep 8955355 = 13433033) B13433033
theorem B1861199 : Blo 1240438 1861199 := bstep (se 1 (by rfl) ⟨1395899, by rfl⟩ : syracuseStep 1861199 = 2791799) B2791799
theorem B8496737 : Blo 1240438 8496737 := bstep (se 2 (by rfl) ⟨3186276, by rfl⟩ : syracuseStep 8496737 = 6372553) B6372553
theorem B1861319 : Blo 1240438 1861319 := bstep (se 1 (by rfl) ⟨1395989, by rfl⟩ : syracuseStep 1861319 = 2791979) B2791979
theorem B4474577 : Blo 1240438 4474577 := bstep (se 2 (by rfl) ⟨1677966, by rfl⟩ : syracuseStep 4474577 = 3355933) B3355933
theorem B2795219 : Blo 1240438 2795219 := bstep (se 1 (by rfl) ⟨2096414, by rfl⟩ : syracuseStep 2795219 = 4192829) B4192829
theorem B3974941 : Blo 1240438 3974941 := bstep (se 3 (by rfl) ⟨745301, by rfl⟩ : syracuseStep 3974941 = 1490603) B1490603
theorem B13428575 : Blo 1240438 13428575 := bstep (se 1 (by rfl) ⟨10071431, by rfl⟩ : syracuseStep 13428575 = 20142863) B20142863
theorem B1861481 : Blo 1240438 1861481 := bstep (se 2 (by rfl) ⟨698055, by rfl⟩ : syracuseStep 1861481 = 1396111) B1396111
theorem B4188023 : Blo 1240438 4188023 := bstep (se 1 (by rfl) ⟨3141017, by rfl⟩ : syracuseStep 4188023 = 6282035) B6282035
theorem B32237473 : Blo 1240438 32237473 := bstep (se 2 (by rfl) ⟨12089052, by rfl⟩ : syracuseStep 32237473 = 24178105) B24178105
theorem B3975095 : Blo 1240438 3975095 := bstep (se 1 (by rfl) ⟨2981321, by rfl⟩ : syracuseStep 3975095 = 5962643) B5962643
theorem B1861559 : Blo 1240438 1861559 := bstep (se 1 (by rfl) ⟨1396169, by rfl⟩ : syracuseStep 1861559 = 2792339) B2792339
theorem B4474807 : Blo 1240438 4474807 := bstep (se 1 (by rfl) ⟨3356105, by rfl⟩ : syracuseStep 4474807 = 6712211) B6712211
theorem B1861595 : Blo 1240438 1861595 := bstep (se 1 (by rfl) ⟨1396196, by rfl⟩ : syracuseStep 1861595 = 2792393) B2792393
theorem B4188239 : Blo 1240438 4188239 := bstep (se 1 (by rfl) ⟨3141179, by rfl⟩ : syracuseStep 4188239 = 6282359) B6282359
theorem B10610777 : Blo 1240438 10610777 := bstep (se 2 (by rfl) ⟨3979041, by rfl⟩ : syracuseStep 10610777 = 7958083) B7958083
theorem B11938049 : Blo 1240438 11938049 := bstep (se 2 (by rfl) ⟨4476768, by rfl⟩ : syracuseStep 11938049 = 8953537) B8953537
theorem B14149889 : Blo 1240438 14149889 := bstep (se 2 (by rfl) ⟨5306208, by rfl⟩ : syracuseStep 14149889 = 10612417) B10612417
theorem B7268737 : Blo 1240438 7268737 := bstep (se 2 (by rfl) ⟨2725776, by rfl⟩ : syracuseStep 7268737 = 5451553) B5451553
theorem B1862063 : Blo 1240438 1862063 := bstep (se 1 (by rfl) ⟨1396547, by rfl⟩ : syracuseStep 1862063 = 2793095) B2793095
theorem B4188617 : Blo 1240438 4188617 := bstep (se 2 (by rfl) ⟨1570731, by rfl⟩ : syracuseStep 4188617 = 3141463) B3141463
theorem B1862153 : Blo 1240438 1862153 := bstep (se 2 (by rfl) ⟨698307, by rfl⟩ : syracuseStep 1862153 = 1396615) B1396615
theorem B1862183 : Blo 1240438 1862183 := bstep (se 1 (by rfl) ⟨1396637, by rfl⟩ : syracuseStep 1862183 = 2793275) B2793275
theorem B1862267 : Blo 1240438 1862267 := bstep (se 1 (by rfl) ⟨1396700, by rfl⟩ : syracuseStep 1862267 = 2793401) B2793401
theorem B4188887 : Blo 1240438 4188887 := bstep (se 1 (by rfl) ⟨3141665, by rfl⟩ : syracuseStep 4188887 = 6283331) B6283331
theorem B1862393 : Blo 1240438 1862393 := bstep (se 2 (by rfl) ⟨698397, by rfl⟩ : syracuseStep 1862393 = 1396795) B1396795
theorem B1862495 : Blo 1240438 1862495 := bstep (se 1 (by rfl) ⟨1396871, by rfl⟩ : syracuseStep 1862495 = 2793743) B2793743
theorem B1862507 : Blo 1240438 1862507 := bstep (se 1 (by rfl) ⟨1396880, by rfl⟩ : syracuseStep 1862507 = 2793761) B2793761
theorem B4713335 : Blo 1240438 4713335 := bstep (se 1 (by rfl) ⟨3535001, by rfl⟩ : syracuseStep 4713335 = 7070003) B7070003
theorem B4189103 : Blo 1240438 4189103 := bstep (se 1 (by rfl) ⟨3141827, by rfl⟩ : syracuseStep 4189103 = 6283655) B6283655
theorem B3976199 : Blo 1240438 3976199 := bstep (se 1 (by rfl) ⟨2982149, by rfl⟩ : syracuseStep 3976199 = 5964299) B5964299
theorem B1395751 : Blo 1240438 1395751 := bstep (se 1 (by rfl) ⟨1046813, by rfl⟩ : syracuseStep 1395751 = 2093627) B2093627
theorem B1862735 : Blo 1240438 1862735 := bstep (se 1 (by rfl) ⟨1397051, by rfl⟩ : syracuseStep 1862735 = 2794103) B2794103
theorem B9424025 : Blo 1240438 9424025 := bstep (se 2 (by rfl) ⟨3534009, by rfl⟩ : syracuseStep 9424025 = 7068019) B7068019
theorem B4246685 : Blo 1240438 4246685 := bstep (se 3 (by rfl) ⟨796253, by rfl⟩ : syracuseStep 4246685 = 1592507) B1592507
theorem B3353771 : Blo 1240438 3353771 := bstep (se 1 (by rfl) ⟨2515328, by rfl⟩ : syracuseStep 3353771 = 5030657) B5030657
theorem B1862855 : Blo 1240438 1862855 := bstep (se 1 (by rfl) ⟨1397141, by rfl⟩ : syracuseStep 1862855 = 2794283) B2794283
theorem B40267043 : Blo 1240438 40267043 := bstep (se 1 (by rfl) ⟨30200282, by rfl⟩ : syracuseStep 40267043 = 60400565) B60400565
theorem B2649449 : Blo 1240438 2649449 := bstep (se 2 (by rfl) ⟨993543, by rfl⟩ : syracuseStep 2649449 = 1987087) B1987087
theorem B1863017 : Blo 1240438 1863017 := bstep (se 2 (by rfl) ⟨698631, by rfl⟩ : syracuseStep 1863017 = 1397263) B1397263
theorem B1240443 : Blo 1240438 1240443 := bstep (se 1 (by rfl) ⟨930332, by rfl⟩ : syracuseStep 1240443 = 1860665) B1860665
theorem B5664143 : Blo 1240438 5664143 := bstep (se 1 (by rfl) ⟨4248107, by rfl⟩ : syracuseStep 5664143 = 8496215) B8496215
theorem B1240495 : Blo 1240438 1240495 := bstep (se 1 (by rfl) ⟨930371, by rfl⟩ : syracuseStep 1240495 = 1860743) B1860743
theorem B1863095 : Blo 1240438 1863095 := bstep (se 1 (by rfl) ⟨1397321, by rfl⟩ : syracuseStep 1863095 = 2794643) B2794643
theorem B1240519 : Blo 1240438 1240519 := bstep (se 1 (by rfl) ⟨930389, by rfl⟩ : syracuseStep 1240519 = 1860779) B1860779
theorem B1240539 : Blo 1240438 1240539 := bstep (se 1 (by rfl) ⟨930404, by rfl⟩ : syracuseStep 1240539 = 1860809) B1860809
theorem B1863131 : Blo 1240438 1863131 := bstep (se 1 (by rfl) ⟨1397348, by rfl⟩ : syracuseStep 1863131 = 2794697) B2794697
theorem B1240615 : Blo 1240438 1240615 := bstep (se 1 (by rfl) ⟨930461, by rfl⟩ : syracuseStep 1240615 = 1860923) B1860923
theorem B1240655 : Blo 1240438 1240655 := bstep (se 1 (by rfl) ⟨930491, by rfl⟩ : syracuseStep 1240655 = 1860983) B1860983
theorem B1240671 : Blo 1240438 1240671 := bstep (se 1 (by rfl) ⟨930503, by rfl⟩ : syracuseStep 1240671 = 1861007) B1861007
theorem B1240699 : Blo 1240438 1240699 := bstep (se 1 (by rfl) ⟨930524, by rfl⟩ : syracuseStep 1240699 = 1861049) B1861049
theorem B4476539 : Blo 1240438 4476539 := bstep (se 1 (by rfl) ⟨3357404, by rfl⟩ : syracuseStep 4476539 = 6714809) B6714809
theorem B1240751 : Blo 1240438 1240751 := bstep (se 1 (by rfl) ⟨930563, by rfl⟩ : syracuseStep 1240751 = 1861127) B1861127
theorem B1240775 : Blo 1240438 1240775 := bstep (se 1 (by rfl) ⟨930581, by rfl⟩ : syracuseStep 1240775 = 1861163) B1861163
theorem B1240795 : Blo 1240438 1240795 := bstep (se 1 (by rfl) ⟨930596, by rfl⟩ : syracuseStep 1240795 = 1861193) B1861193
theorem B1240871 : Blo 1240438 1240871 := bstep (se 1 (by rfl) ⟨930653, by rfl⟩ : syracuseStep 1240871 = 1861307) B1861307
theorem B5033771 : Blo 1240438 5033771 := bstep (se 1 (by rfl) ⟨3775328, by rfl⟩ : syracuseStep 5033771 = 7550657) B7550657
theorem B4714307 : Blo 1240438 4714307 := bstep (se 1 (by rfl) ⟨3535730, by rfl⟩ : syracuseStep 4714307 = 7071461) B7071461
theorem B1240911 : Blo 1240438 1240911 := bstep (se 1 (by rfl) ⟨930683, by rfl⟩ : syracuseStep 1240911 = 1861367) B1861367
theorem B1240927 : Blo 1240438 1240927 := bstep (se 1 (by rfl) ⟨930695, by rfl⟩ : syracuseStep 1240927 = 1861391) B1861391
theorem B3354463 : Blo 1240438 3354463 := bstep (se 1 (by rfl) ⟨2515847, by rfl⟩ : syracuseStep 3354463 = 5031695) B5031695
theorem B1240955 : Blo 1240438 1240955 := bstep (se 1 (by rfl) ⟨930716, by rfl⟩ : syracuseStep 1240955 = 1861433) B1861433
theorem B15896483 : Blo 1240438 15896483 := bstep (se 1 (by rfl) ⟨11922362, by rfl⟩ : syracuseStep 15896483 = 23844725) B23844725
theorem B1241007 : Blo 1240438 1241007 := bstep (se 1 (by rfl) ⟨930755, by rfl⟩ : syracuseStep 1241007 = 1861511) B1861511
theorem B1888175 : Blo 1240438 1888175 := bstep (se 1 (by rfl) ⟨1416131, by rfl⟩ : syracuseStep 1888175 = 2832263) B2832263
theorem B1863599 : Blo 1240438 1863599 := bstep (se 1 (by rfl) ⟨1397699, by rfl⟩ : syracuseStep 1863599 = 2795399) B2795399
theorem B1241031 : Blo 1240438 1241031 := bstep (se 1 (by rfl) ⟨930773, by rfl⟩ : syracuseStep 1241031 = 1861547) B1861547
theorem B1241051 : Blo 1240438 1241051 := bstep (se 1 (by rfl) ⟨930788, by rfl⟩ : syracuseStep 1241051 = 1861577) B1861577
theorem B1241127 : Blo 1240438 1241127 := bstep (se 1 (by rfl) ⟨930845, by rfl⟩ : syracuseStep 1241127 = 1861691) B1861691
theorem B1241167 : Blo 1240438 1241167 := bstep (se 1 (by rfl) ⟨930875, by rfl⟩ : syracuseStep 1241167 = 1861751) B1861751
theorem B1241183 : Blo 1240438 1241183 := bstep (se 1 (by rfl) ⟨930887, by rfl⟩ : syracuseStep 1241183 = 1861775) B1861775
theorem B1241211 : Blo 1240438 1241211 := bstep (se 1 (by rfl) ⟨930908, by rfl⟩ : syracuseStep 1241211 = 1861817) B1861817
theorem B1241263 : Blo 1240438 1241263 := bstep (se 1 (by rfl) ⟨930947, by rfl⟩ : syracuseStep 1241263 = 1861895) B1861895
theorem B1241287 : Blo 1240438 1241287 := bstep (se 1 (by rfl) ⟨930965, by rfl⟩ : syracuseStep 1241287 = 1861931) B1861931
theorem B1241307 : Blo 1240438 1241307 := bstep (se 1 (by rfl) ⟨930980, by rfl⟩ : syracuseStep 1241307 = 1861961) B1861961
theorem B2093303 : Blo 1240438 2093303 := bstep (se 1 (by rfl) ⟨1569977, by rfl⟩ : syracuseStep 2093303 = 3139955) B3139955
theorem B1241383 : Blo 1240438 1241383 := bstep (se 1 (by rfl) ⟨931037, by rfl⟩ : syracuseStep 1241383 = 1862075) B1862075
theorem B15102283 : Blo 1240438 15102283 := bstep (se 1 (by rfl) ⟨11326712, by rfl⟩ : syracuseStep 15102283 = 22653425) B22653425
theorem B1241423 : Blo 1240438 1241423 := bstep (se 1 (by rfl) ⟨931067, by rfl⟩ : syracuseStep 1241423 = 1862135) B1862135
theorem B2355551 : Blo 1240438 2355551 := bstep (se 1 (by rfl) ⟨1766663, by rfl⟩ : syracuseStep 2355551 = 3533327) B3533327
theorem B1241439 : Blo 1240438 1241439 := bstep (se 1 (by rfl) ⟨931079, by rfl⟩ : syracuseStep 1241439 = 1862159) B1862159
theorem B1241467 : Blo 1240438 1241467 := bstep (se 1 (by rfl) ⟨931100, by rfl⟩ : syracuseStep 1241467 = 1862201) B1862201
theorem B20132225 : Blo 1240438 20132225 := bstep (se 2 (by rfl) ⟨7549584, by rfl⟩ : syracuseStep 20132225 = 15099169) B15099169
theorem B1241519 : Blo 1240438 1241519 := bstep (se 1 (by rfl) ⟨931139, by rfl⟩ : syracuseStep 1241519 = 1862279) B1862279
theorem B1241543 : Blo 1240438 1241543 := bstep (se 1 (by rfl) ⟨931157, by rfl⟩ : syracuseStep 1241543 = 1862315) B1862315
theorem B1241563 : Blo 1240438 1241563 := bstep (se 1 (by rfl) ⟨931172, by rfl⟩ : syracuseStep 1241563 = 1862345) B1862345
theorem B3977761 : Blo 1240438 3977761 := bstep (se 2 (by rfl) ⟨1491660, by rfl⟩ : syracuseStep 3977761 = 2983321) B2983321
theorem B1241639 : Blo 1240438 1241639 := bstep (se 1 (by rfl) ⟨931229, by rfl⟩ : syracuseStep 1241639 = 1862459) B1862459
theorem B2093647 : Blo 1240438 2093647 := bstep (se 1 (by rfl) ⟨1570235, by rfl⟩ : syracuseStep 2093647 = 3140471) B3140471
theorem B1241679 : Blo 1240438 1241679 := bstep (se 1 (by rfl) ⟨931259, by rfl⟩ : syracuseStep 1241679 = 1862519) B1862519
theorem B1241695 : Blo 1240438 1241695 := bstep (se 1 (by rfl) ⟨931271, by rfl⟩ : syracuseStep 1241695 = 1862543) B1862543
theorem B2650747 : Blo 1240438 2650747 := bstep (se 1 (by rfl) ⟨1988060, by rfl⟩ : syracuseStep 2650747 = 3976121) B3976121
theorem B1241723 : Blo 1240438 1241723 := bstep (se 1 (by rfl) ⟨931292, by rfl⟩ : syracuseStep 1241723 = 1862585) B1862585
theorem B1397371 : Blo 1240438 1397371 := bstep (se 1 (by rfl) ⟨1048028, by rfl⟩ : syracuseStep 1397371 = 2096057) B2096057
theorem B1241775 : Blo 1240438 1241775 := bstep (se 1 (by rfl) ⟨931331, by rfl⟩ : syracuseStep 1241775 = 1862663) B1862663
theorem B3535559 : Blo 1240438 3535559 := bstep (se 1 (by rfl) ⟨2651669, by rfl⟩ : syracuseStep 3535559 = 5303339) B5303339
theorem B1241799 : Blo 1240438 1241799 := bstep (se 1 (by rfl) ⟨931349, by rfl⟩ : syracuseStep 1241799 = 1862699) B1862699
theorem B1241819 : Blo 1240438 1241819 := bstep (se 1 (by rfl) ⟨931364, by rfl⟩ : syracuseStep 1241819 = 1862729) B1862729
theorem B2355961 : Blo 1240438 2355961 := bstep (se 2 (by rfl) ⟨883485, by rfl⟩ : syracuseStep 2355961 = 1766971) B1766971
theorem B4715293 : Blo 1240438 4715293 := bstep (se 3 (by rfl) ⟨884117, by rfl⟩ : syracuseStep 4715293 = 1768235) B1768235
theorem B1241895 : Blo 1240438 1241895 := bstep (se 1 (by rfl) ⟨931421, by rfl⟩ : syracuseStep 1241895 = 1862843) B1862843
theorem B2093897 : Blo 1240438 2093897 := bstep (se 2 (by rfl) ⟨785211, by rfl⟩ : syracuseStep 2093897 = 1570423) B1570423
theorem B1241935 : Blo 1240438 1241935 := bstep (se 1 (by rfl) ⟨931451, by rfl⟩ : syracuseStep 1241935 = 1862903) B1862903
theorem B3183455 : Blo 1240438 3183455 := bstep (se 1 (by rfl) ⟨2387591, by rfl⟩ : syracuseStep 3183455 = 4775183) B4775183
theorem B1241951 : Blo 1240438 1241951 := bstep (se 1 (by rfl) ⟨931463, by rfl⟩ : syracuseStep 1241951 = 1862927) B1862927
theorem B1987433 : Blo 1240438 1987433 := bstep (se 2 (by rfl) ⟨745287, by rfl⟩ : syracuseStep 1987433 = 1490575) B1490575
theorem B1241979 : Blo 1240438 1241979 := bstep (se 1 (by rfl) ⟨931484, by rfl⟩ : syracuseStep 1241979 = 1862969) B1862969
theorem B57308057 : Blo 1240438 57308057 := bstep (se 2 (by rfl) ⟨21490521, by rfl⟩ : syracuseStep 57308057 = 42981043) B42981043
theorem B28677017 : Blo 1240438 28677017 := bstep (se 2 (by rfl) ⟨10753881, by rfl⟩ : syracuseStep 28677017 = 21507763) B21507763
theorem B1242031 : Blo 1240438 1242031 := bstep (se 1 (by rfl) ⟨931523, by rfl⟩ : syracuseStep 1242031 = 1863047) B1863047
theorem B1242055 : Blo 1240438 1242055 := bstep (se 1 (by rfl) ⟨931541, by rfl⟩ : syracuseStep 1242055 = 1863083) B1863083
theorem B1242075 : Blo 1240438 1242075 := bstep (se 1 (by rfl) ⟨931556, by rfl⟩ : syracuseStep 1242075 = 1863113) B1863113
theorem B2151431 : Blo 1240438 2151431 := bstep (se 1 (by rfl) ⟨1613573, by rfl⟩ : syracuseStep 2151431 = 3227147) B3227147
theorem B1242151 : Blo 1240438 1242151 := bstep (se 1 (by rfl) ⟨931613, by rfl⟩ : syracuseStep 1242151 = 1863227) B1863227
theorem B9425969 : Blo 1240438 9425969 := bstep (se 2 (by rfl) ⟨3534738, by rfl⟩ : syracuseStep 9425969 = 7069477) B7069477
theorem B21787715 : Blo 1240438 21787715 := bstep (se 1 (by rfl) ⟨16340786, by rfl⟩ : syracuseStep 21787715 = 32681573) B32681573
theorem B2356303 : Blo 1240438 2356303 := bstep (se 1 (by rfl) ⟨1767227, by rfl⟩ : syracuseStep 2356303 = 3534455) B3534455
theorem B1242191 : Blo 1240438 1242191 := bstep (se 1 (by rfl) ⟨931643, by rfl⟩ : syracuseStep 1242191 = 1863287) B1863287
theorem B29054045 : Blo 1240438 29054045 := bstep (se 3 (by rfl) ⟨5447633, by rfl⟩ : syracuseStep 29054045 = 10895267) B10895267
theorem B1242207 : Blo 1240438 1242207 := bstep (se 1 (by rfl) ⟨931655, by rfl⟩ : syracuseStep 1242207 = 1863311) B1863311
theorem B9434231 : Blo 1240438 9434231 := bstep (se 1 (by rfl) ⟨7075673, by rfl⟩ : syracuseStep 9434231 = 14151347) B14151347
theorem B1242235 : Blo 1240438 1242235 := bstep (se 1 (by rfl) ⟨931676, by rfl⟩ : syracuseStep 1242235 = 1863353) B1863353
theorem B1242287 : Blo 1240438 1242287 := bstep (se 1 (by rfl) ⟨931715, by rfl⟩ : syracuseStep 1242287 = 1863431) B1863431
theorem B1242311 : Blo 1240438 1242311 := bstep (se 1 (by rfl) ⟨931733, by rfl⟩ : syracuseStep 1242311 = 1863467) B1863467
theorem B1242331 : Blo 1240438 1242331 := bstep (se 1 (by rfl) ⟨931748, by rfl⟩ : syracuseStep 1242331 = 1863497) B1863497
theorem B4191479 : Blo 1240438 4191479 := bstep (se 1 (by rfl) ⟨3143609, by rfl⟩ : syracuseStep 4191479 = 6287219) B6287219
theorem B2094329 : Blo 1240438 2094329 := bstep (se 2 (by rfl) ⟨785373, by rfl⟩ : syracuseStep 2094329 = 1570747) B1570747
theorem B1242407 : Blo 1240438 1242407 := bstep (se 1 (by rfl) ⟨931805, by rfl⟩ : syracuseStep 1242407 = 1863611) B1863611
theorem B2356553 : Blo 1240438 2356553 := bstep (se 2 (by rfl) ⟨883707, by rfl⟩ : syracuseStep 2356553 = 1767415) B1767415
theorem B2094511 : Blo 1240438 2094511 := bstep (se 1 (by rfl) ⟨1570883, by rfl⟩ : syracuseStep 2094511 = 3141767) B3141767
theorem B5969371 : Blo 1240438 5969371 := bstep (se 1 (by rfl) ⟨4477028, by rfl⟩ : syracuseStep 5969371 = 8954057) B8954057
theorem B6706675 : Blo 1240438 6706675 := bstep (se 1 (by rfl) ⟨5030006, by rfl⟩ : syracuseStep 6706675 = 10060013) B10060013
theorem B2094599 : Blo 1240438 2094599 := bstep (se 1 (by rfl) ⟨1570949, by rfl⟩ : syracuseStep 2094599 = 3141899) B3141899
theorem B2651687 : Blo 1240438 2651687 := bstep (se 1 (by rfl) ⟨1988765, by rfl⟩ : syracuseStep 2651687 = 3977531) B3977531
theorem B4191803 : Blo 1240438 4191803 := bstep (se 1 (by rfl) ⟨3143852, by rfl⟩ : syracuseStep 4191803 = 6287705) B6287705
theorem B6051475 : Blo 1240438 6051475 := bstep (se 1 (by rfl) ⟨4538606, by rfl⟩ : syracuseStep 6051475 = 9077213) B9077213
theorem B6706937 : Blo 1240438 6706937 := bstep (se 2 (by rfl) ⟨2515101, by rfl⟩ : syracuseStep 6706937 = 5030203) B5030203
theorem B8722235 : Blo 1240438 8722235 := bstep (se 1 (by rfl) ⟨6541676, by rfl⟩ : syracuseStep 8722235 = 13083353) B13083353
theorem B2791241 : Blo 1240438 2791241 := bstep (se 2 (by rfl) ⟨1046715, by rfl⟩ : syracuseStep 2791241 = 2093431) B2093431
theorem B2651977 : Blo 1240438 2651977 := bstep (se 2 (by rfl) ⟨994491, by rfl⟩ : syracuseStep 2651977 = 1988983) B1988983
theorem B4192073 : Blo 1240438 4192073 := bstep (se 2 (by rfl) ⟨1572027, by rfl⟩ : syracuseStep 4192073 = 3144055) B3144055
theorem B1324895 : Blo 1240438 1324895 := bstep (se 1 (by rfl) ⟨993671, by rfl⟩ : syracuseStep 1324895 = 1987343) B1987343
theorem B2094943 : Blo 1240438 2094943 := bstep (se 1 (by rfl) ⟨1571207, by rfl⟩ : syracuseStep 2094943 = 3142415) B3142415
theorem B3143519 : Blo 1240438 3143519 := bstep (se 1 (by rfl) ⟨2357639, by rfl⟩ : syracuseStep 3143519 = 4715279) B4715279
theorem B12089249 : Blo 1240438 12089249 := bstep (se 2 (by rfl) ⟨4533468, by rfl⟩ : syracuseStep 12089249 = 9066937) B9066937
theorem B2095031 : Blo 1240438 2095031 := bstep (se 1 (by rfl) ⟨1571273, by rfl⟩ : syracuseStep 2095031 = 3142547) B3142547
theorem B2357419 : Blo 1240438 2357419 := bstep (se 1 (by rfl) ⟨1768064, by rfl⟩ : syracuseStep 2357419 = 3536129) B3536129
theorem B1571015 : Blo 1240438 1571015 := bstep (se 1 (by rfl) ⟨1178261, by rfl⟩ : syracuseStep 1571015 = 2356523) B2356523
theorem B1988855 : Blo 1240438 1988855 := bstep (se 1 (by rfl) ⟨1491641, by rfl⟩ : syracuseStep 1988855 = 2983283) B2983283
theorem B2357495 : Blo 1240438 2357495 := bstep (se 1 (by rfl) ⟨1768121, by rfl⟩ : syracuseStep 2357495 = 3536243) B3536243
theorem B7952651 : Blo 1240438 7952651 := bstep (se 1 (by rfl) ⟨5964488, by rfl⟩ : syracuseStep 7952651 = 11928977) B11928977
theorem B1571167 : Blo 1240438 1571167 := bstep (se 1 (by rfl) ⟨1178375, by rfl⟩ : syracuseStep 1571167 = 2356751) B2356751
theorem B2357723 : Blo 1240438 2357723 := bstep (se 1 (by rfl) ⟨1768292, by rfl⟩ : syracuseStep 2357723 = 3536585) B3536585
theorem B3537371 : Blo 1240438 3537371 := bstep (se 1 (by rfl) ⟨2653028, by rfl⟩ : syracuseStep 3537371 = 5306057) B5306057
theorem B2095625 : Blo 1240438 2095625 := bstep (se 2 (by rfl) ⟨785859, by rfl⟩ : syracuseStep 2095625 = 1571719) B1571719
theorem B3144217 : Blo 1240438 3144217 := bstep (se 2 (by rfl) ⟨1179081, by rfl⟩ : syracuseStep 3144217 = 2358163) B2358163
theorem B1325647 : Blo 1240438 1325647 := bstep (se 1 (by rfl) ⟨994235, by rfl⟩ : syracuseStep 1325647 = 1988471) B1988471
theorem B2792033 : Blo 1240438 2792033 := bstep (se 2 (by rfl) ⟨1047012, by rfl⟩ : syracuseStep 2792033 = 2094025) B2094025
theorem B2095787 : Blo 1240438 2095787 := bstep (se 1 (by rfl) ⟨1571840, by rfl⟩ : syracuseStep 2095787 = 3143681) B3143681
theorem B265149125 : Blo 1240438 265149125 := bstep (se 4 (by rfl) ⟨24857730, by rfl⟩ : syracuseStep 265149125 = 49715461) B49715461
theorem B3979991 : Blo 1240438 3979991 := bstep (se 1 (by rfl) ⟨2984993, by rfl⟩ : syracuseStep 3979991 = 5969987) B5969987
theorem B3144521 : Blo 1240438 3144521 := bstep (se 2 (by rfl) ⟨1179195, by rfl⟩ : syracuseStep 3144521 = 2358391) B2358391
theorem B2792375 : Blo 1240438 2792375 := bstep (se 1 (by rfl) ⟨2094281, by rfl⟩ : syracuseStep 2792375 = 4188563) B4188563
theorem B4193207 : Blo 1240438 4193207 := bstep (se 1 (by rfl) ⟨3144905, by rfl⟩ : syracuseStep 4193207 = 6289811) B6289811
theorem B8068115 : Blo 1240438 8068115 := bstep (se 1 (by rfl) ⟨6051086, by rfl⟩ : syracuseStep 8068115 = 12102173) B12102173
theorem B3931193 : Blo 1240438 3931193 := bstep (se 2 (by rfl) ⟨1474197, by rfl⟩ : syracuseStep 3931193 = 2948395) B2948395
theorem B2096185 : Blo 1240438 2096185 := bstep (se 2 (by rfl) ⟨786069, by rfl⟩ : syracuseStep 2096185 = 1572139) B1572139
theorem B2653241 : Blo 1240438 2653241 := bstep (se 2 (by rfl) ⟨994965, by rfl⟩ : syracuseStep 2653241 = 1989931) B1989931
theorem B1989803 : Blo 1240438 1989803 := bstep (se 1 (by rfl) ⟨1492352, by rfl⟩ : syracuseStep 1989803 = 2984705) B2984705
theorem B2096327 : Blo 1240438 2096327 := bstep (se 1 (by rfl) ⟨1572245, by rfl⟩ : syracuseStep 2096327 = 3144491) B3144491
theorem B1989983 : Blo 1240438 1989983 := bstep (se 1 (by rfl) ⟨1492487, by rfl⟩ : syracuseStep 1989983 = 2984975) B2984975
theorem B2096489 : Blo 1240438 2096489 := bstep (se 2 (by rfl) ⟨786183, by rfl⟩ : syracuseStep 2096489 = 1572367) B1572367
theorem B6127049 : Blo 1240438 6127049 := bstep (se 2 (by rfl) ⟨2297643, by rfl⟩ : syracuseStep 6127049 = 4595287) B4595287
theorem B2792969 : Blo 1240438 2792969 := bstep (se 2 (by rfl) ⟨1047363, by rfl⟩ : syracuseStep 2792969 = 2094727) B2094727
theorem B4709947 : Blo 1240438 4709947 := bstep (se 1 (by rfl) ⟨3532460, by rfl⟩ : syracuseStep 4709947 = 7064921) B7064921
theorem B10608317 : Blo 1240438 10608317 := bstep (se 3 (by rfl) ⟨1989059, by rfl⟩ : syracuseStep 10608317 = 3978119) B3978119
theorem B13426499 : Blo 1240438 13426499 := bstep (se 1 (by rfl) ⟨10069874, by rfl⟩ : syracuseStep 13426499 = 20139749) B20139749
theorem B2793311 : Blo 1240438 2793311 := bstep (se 1 (by rfl) ⟨2094983, by rfl⟩ : syracuseStep 2793311 = 4189967) B4189967
theorem B4710251 : Blo 1240438 4710251 := bstep (se 1 (by rfl) ⟨3532688, by rfl⟩ : syracuseStep 4710251 = 7065377) B7065377
theorem B31833971 : Blo 1240438 31833971 := bstep (se 1 (by rfl) ⟨23875478, by rfl⟩ : syracuseStep 31833971 = 47750957) B47750957
theorem B16138115 : Blo 1240438 16138115 := bstep (se 1 (by rfl) ⟨12103586, by rfl⟩ : syracuseStep 16138115 = 24207173) B24207173
theorem B6283169 : Blo 1240438 6283169 := bstep (se 2 (by rfl) ⟨2356188, by rfl⟩ : syracuseStep 6283169 = 4712377) B4712377
theorem B20136377 : Blo 1240438 20136377 := bstep (se 2 (by rfl) ⟨7551141, by rfl⟩ : syracuseStep 20136377 = 15102283) B15102283
theorem B9691649 : Blo 1240438 9691649 := bstep (se 2 (by rfl) ⟨3634368, by rfl⟩ : syracuseStep 9691649 = 7268737) B7268737
theorem B2122303 : Blo 1240438 2122303 := bstep (se 1 (by rfl) ⟨1591727, by rfl⟩ : syracuseStep 2122303 = 3183455) B3183455
theorem B1434287 : Blo 1240438 1434287 := bstep (se 1 (by rfl) ⟨1075715, by rfl⟩ : syracuseStep 1434287 = 2151431) B2151431
theorem B6283979 : Blo 1240438 6283979 := bstep (se 1 (by rfl) ⟨4712984, by rfl⟩ : syracuseStep 6283979 = 9425969) B9425969
theorem B2794319 : Blo 1240438 2794319 := bstep (se 1 (by rfl) ⟨2095739, by rfl⟩ : syracuseStep 2794319 = 4191479) B4191479
theorem B6284141 : Blo 1240438 6284141 := bstep (se 3 (by rfl) ⟨1178276, by rfl⟩ : syracuseStep 6284141 = 2356553) B2356553
theorem B2794535 : Blo 1240438 2794535 := bstep (se 1 (by rfl) ⟨2095901, by rfl⟩ : syracuseStep 2794535 = 4191803) B4191803
theorem B2983051 : Blo 1240438 2983051 := bstep (se 1 (by rfl) ⟨2237288, by rfl⟩ : syracuseStep 2983051 = 4474577) B4474577
theorem B1860827 : Blo 1240438 1860827 := bstep (se 1 (by rfl) ⟨1395620, by rfl⟩ : syracuseStep 1860827 = 2791241) B2791241
theorem B2794715 : Blo 1240438 2794715 := bstep (se 1 (by rfl) ⟨2096036, by rfl⟩ : syracuseStep 2794715 = 4192073) B4192073
theorem B1861001 : Blo 1240438 1861001 := bstep (se 2 (by rfl) ⟨697875, by rfl⟩ : syracuseStep 1861001 = 1395751) B1395751
theorem B2794913 : Blo 1240438 2794913 := bstep (se 2 (by rfl) ⟨1048092, by rfl⟩ : syracuseStep 2794913 = 2096185) B2096185
theorem B5301767 : Blo 1240438 5301767 := bstep (se 1 (by rfl) ⟨3976325, by rfl⟩ : syracuseStep 5301767 = 7952651) B7952651
theorem B1861355 : Blo 1240438 1861355 := bstep (se 1 (by rfl) ⟨1396016, by rfl⟩ : syracuseStep 1861355 = 2792033) B2792033
theorem B1861583 : Blo 1240438 1861583 := bstep (se 1 (by rfl) ⟨1396187, by rfl⟩ : syracuseStep 1861583 = 2792375) B2792375
theorem B2795471 : Blo 1240438 2795471 := bstep (se 1 (by rfl) ⟨2096603, by rfl⟩ : syracuseStep 2795471 = 4193207) B4193207
theorem B3533053 : Blo 1240438 3533053 := bstep (se 3 (by rfl) ⟨662447, by rfl⟩ : syracuseStep 3533053 = 1324895) B1324895
theorem B23865637 : Blo 1240438 23865637 := bstep (se 4 (by rfl) ⟨2237403, by rfl⟩ : syracuseStep 23865637 = 4474807) B4474807
theorem B1861979 : Blo 1240438 1861979 := bstep (se 1 (by rfl) ⟨1396484, by rfl⟩ : syracuseStep 1861979 = 2792969) B2792969
theorem B2984359 : Blo 1240438 2984359 := bstep (se 1 (by rfl) ⟨2238269, by rfl⟩ : syracuseStep 2984359 = 4476539) B4476539
theorem B7072211 : Blo 1240438 7072211 := bstep (se 1 (by rfl) ⟨5304158, by rfl⟩ : syracuseStep 7072211 = 10608317) B10608317
theorem B1862207 : Blo 1240438 1862207 := bstep (se 1 (by rfl) ⟨1396655, by rfl⟩ : syracuseStep 1862207 = 2793311) B2793311
theorem B3140167 : Blo 1240438 3140167 := bstep (se 1 (by rfl) ⟨2355125, by rfl⟩ : syracuseStep 3140167 = 4710251) B4710251
theorem B10758743 : Blo 1240438 10758743 := bstep (se 1 (by rfl) ⟨8069057, by rfl⟩ : syracuseStep 10758743 = 16138115) B16138115
theorem B4188779 : Blo 1240438 4188779 := bstep (se 1 (by rfl) ⟨3141584, by rfl⟩ : syracuseStep 4188779 = 6283169) B6283169
theorem B3140279 : Blo 1240438 3140279 := bstep (se 1 (by rfl) ⟨2355209, by rfl⟩ : syracuseStep 3140279 = 4710419) B4710419
theorem B1862327 : Blo 1240438 1862327 := bstep (se 1 (by rfl) ⟨1396745, by rfl⟩ : syracuseStep 1862327 = 2793491) B2793491
theorem B1395535 : Blo 1240438 1395535 := bstep (se 1 (by rfl) ⟨1046651, by rfl⟩ : syracuseStep 1395535 = 2093303) B2093303
theorem B58100573 : Blo 1240438 58100573 := bstep (se 3 (by rfl) ⟨10893857, by rfl⟩ : syracuseStep 58100573 = 21787715) B21787715
theorem B1862555 : Blo 1240438 1862555 := bstep (se 1 (by rfl) ⟨1396916, by rfl⟩ : syracuseStep 1862555 = 2793833) B2793833
theorem B13421483 : Blo 1240438 13421483 := bstep (se 1 (by rfl) ⟨10066112, by rfl⟩ : syracuseStep 13421483 = 20132225) B20132225
theorem B2829455 : Blo 1240438 2829455 := bstep (se 1 (by rfl) ⟨2122091, by rfl⟩ : syracuseStep 2829455 = 4244183) B4244183
theorem B4189373 : Blo 1240438 4189373 := bstep (se 3 (by rfl) ⟨785507, by rfl⟩ : syracuseStep 4189373 = 1571015) B1571015
theorem B1395931 : Blo 1240438 1395931 := bstep (se 1 (by rfl) ⟨1046948, by rfl⟩ : syracuseStep 1395931 = 2093897) B2093897
theorem B1862951 : Blo 1240438 1862951 := bstep (se 1 (by rfl) ⟨1397213, by rfl⟩ : syracuseStep 1862951 = 2794427) B2794427
theorem B1863035 : Blo 1240438 1863035 := bstep (se 1 (by rfl) ⟨1397276, by rfl⟩ : syracuseStep 1863035 = 2794553) B2794553
theorem B5303681 : Blo 1240438 5303681 := bstep (se 2 (by rfl) ⟨1988880, by rfl⟩ : syracuseStep 5303681 = 3977761) B3977761
theorem B19369363 : Blo 1240438 19369363 := bstep (se 1 (by rfl) ⟨14527022, by rfl⟩ : syracuseStep 19369363 = 29054045) B29054045
theorem B1240487 : Blo 1240438 1240487 := bstep (se 1 (by rfl) ⟨930365, by rfl⟩ : syracuseStep 1240487 = 1860731) B1860731
theorem B3534329 : Blo 1240438 3534329 := bstep (se 2 (by rfl) ⟨1325373, by rfl⟩ : syracuseStep 3534329 = 2650747) B2650747
theorem B1863161 : Blo 1240438 1863161 := bstep (se 2 (by rfl) ⟨698685, by rfl⟩ : syracuseStep 1863161 = 1397371) B1397371
theorem B1240571 : Blo 1240438 1240571 := bstep (se 1 (by rfl) ⟨930428, by rfl⟩ : syracuseStep 1240571 = 1860857) B1860857
theorem B1396219 : Blo 1240438 1396219 := bstep (se 1 (by rfl) ⟨1047164, by rfl⟩ : syracuseStep 1396219 = 2094329) B2094329
theorem B3354119 : Blo 1240438 3354119 := bstep (se 1 (by rfl) ⟨2515589, by rfl⟩ : syracuseStep 3354119 = 5031179) B5031179
theorem B1240639 : Blo 1240438 1240639 := bstep (se 1 (by rfl) ⟨930479, by rfl⟩ : syracuseStep 1240639 = 1860959) B1860959
theorem B1240647 : Blo 1240438 1240647 := bstep (se 1 (by rfl) ⟨930485, by rfl⟩ : syracuseStep 1240647 = 1860971) B1860971
theorem B1863263 : Blo 1240438 1863263 := bstep (se 1 (by rfl) ⟨1397447, by rfl⟩ : syracuseStep 1863263 = 2794895) B2794895
theorem B3141281 : Blo 1240438 3141281 := bstep (se 2 (by rfl) ⟨1177980, by rfl⟩ : syracuseStep 3141281 = 2355961) B2355961
theorem B1396399 : Blo 1240438 1396399 := bstep (se 1 (by rfl) ⟨1047299, by rfl⟩ : syracuseStep 1396399 = 2094599) B2094599
theorem B6287057 : Blo 1240438 6287057 := bstep (se 2 (by rfl) ⟨2357646, by rfl⟩ : syracuseStep 6287057 = 4715293) B4715293
theorem B1240799 : Blo 1240438 1240799 := bstep (se 1 (by rfl) ⟨930599, by rfl⟩ : syracuseStep 1240799 = 1861199) B1861199
theorem B5664491 : Blo 1240438 5664491 := bstep (se 1 (by rfl) ⟨4248368, by rfl⟩ : syracuseStep 5664491 = 8496737) B8496737
theorem B1240879 : Blo 1240438 1240879 := bstep (se 1 (by rfl) ⟨930659, by rfl⟩ : syracuseStep 1240879 = 1861319) B1861319
theorem B1863479 : Blo 1240438 1863479 := bstep (se 1 (by rfl) ⟨1397609, by rfl⟩ : syracuseStep 1863479 = 2795219) B2795219
theorem B16338797 : Blo 1240438 16338797 := bstep (se 3 (by rfl) ⟨3063524, by rfl⟩ : syracuseStep 16338797 = 6127049) B6127049
theorem B1240987 : Blo 1240438 1240987 := bstep (se 1 (by rfl) ⟨930740, by rfl⟩ : syracuseStep 1240987 = 1861481) B1861481
theorem B1241039 : Blo 1240438 1241039 := bstep (se 1 (by rfl) ⟨930779, by rfl⟩ : syracuseStep 1241039 = 1861559) B1861559
theorem B1396687 : Blo 1240438 1396687 := bstep (se 1 (by rfl) ⟨1047515, by rfl⟩ : syracuseStep 1396687 = 2095031) B2095031
theorem B1241063 : Blo 1240438 1241063 := bstep (se 1 (by rfl) ⟨930797, by rfl⟩ : syracuseStep 1241063 = 1861595) B1861595
theorem B7073851 : Blo 1240438 7073851 := bstep (se 1 (by rfl) ⟨5305388, by rfl⟩ : syracuseStep 7073851 = 10610777) B10610777
theorem B3141737 : Blo 1240438 3141737 := bstep (se 2 (by rfl) ⟨1178151, by rfl⟩ : syracuseStep 3141737 = 2356303) B2356303
theorem B7958699 : Blo 1240438 7958699 := bstep (se 1 (by rfl) ⟨5969024, by rfl⟩ : syracuseStep 7958699 = 11938049) B11938049
theorem B9433259 : Blo 1240438 9433259 := bstep (se 1 (by rfl) ⟨7074944, by rfl⟩ : syracuseStep 9433259 = 14149889) B14149889
theorem B1241375 : Blo 1240438 1241375 := bstep (se 1 (by rfl) ⟨931031, by rfl⟩ : syracuseStep 1241375 = 1862063) B1862063
theorem B1241435 : Blo 1240438 1241435 := bstep (se 1 (by rfl) ⟨931076, by rfl⟩ : syracuseStep 1241435 = 1862153) B1862153
theorem B1397083 : Blo 1240438 1397083 := bstep (se 1 (by rfl) ⟨1047812, by rfl⟩ : syracuseStep 1397083 = 2095625) B2095625
theorem B1241455 : Blo 1240438 1241455 := bstep (se 1 (by rfl) ⟨931091, by rfl⟩ : syracuseStep 1241455 = 1862183) B1862183
theorem B1241511 : Blo 1240438 1241511 := bstep (se 1 (by rfl) ⟨931133, by rfl⟩ : syracuseStep 1241511 = 1862267) B1862267
theorem B1397191 : Blo 1240438 1397191 := bstep (se 1 (by rfl) ⟨1047893, by rfl⟩ : syracuseStep 1397191 = 2095787) B2095787
theorem B1241595 : Blo 1240438 1241595 := bstep (se 1 (by rfl) ⟨931196, by rfl⟩ : syracuseStep 1241595 = 1862393) B1862393
theorem B1241663 : Blo 1240438 1241663 := bstep (se 1 (by rfl) ⟨931247, by rfl⟩ : syracuseStep 1241663 = 1862495) B1862495
theorem B1241671 : Blo 1240438 1241671 := bstep (se 1 (by rfl) ⟨931253, by rfl⟩ : syracuseStep 1241671 = 1862507) B1862507
theorem B3142223 : Blo 1240438 3142223 := bstep (se 1 (by rfl) ⟨2356667, by rfl⟩ : syracuseStep 3142223 = 4713335) B4713335
theorem B7959161 : Blo 1240438 7959161 := bstep (se 2 (by rfl) ⟨2984685, by rfl⟩ : syracuseStep 7959161 = 5969371) B5969371
theorem B11940473 : Blo 1240438 11940473 := bstep (se 2 (by rfl) ⟨4477677, by rfl⟩ : syracuseStep 11940473 = 8955355) B8955355
theorem B8942233 : Blo 1240438 8942233 := bstep (se 2 (by rfl) ⟨3353337, by rfl⟩ : syracuseStep 8942233 = 6706675) B6706675
theorem B2650799 : Blo 1240438 2650799 := bstep (se 1 (by rfl) ⟨1988099, by rfl⟩ : syracuseStep 2650799 = 3976199) B3976199
theorem B5378743 : Blo 1240438 5378743 := bstep (se 1 (by rfl) ⟨4034057, by rfl⟩ : syracuseStep 5378743 = 8068115) B8068115
theorem B1241823 : Blo 1240438 1241823 := bstep (se 1 (by rfl) ⟨931367, by rfl⟩ : syracuseStep 1241823 = 1862735) B1862735
theorem B6279929 : Blo 1240438 6279929 := bstep (se 2 (by rfl) ⟨2354973, by rfl⟩ : syracuseStep 6279929 = 4709947) B4709947
theorem B2831123 : Blo 1240438 2831123 := bstep (se 1 (by rfl) ⟨2123342, by rfl⟩ : syracuseStep 2831123 = 4246685) B4246685
theorem B1241903 : Blo 1240438 1241903 := bstep (se 1 (by rfl) ⟨931427, by rfl⟩ : syracuseStep 1241903 = 1862855) B1862855
theorem B1397551 : Blo 1240438 1397551 := bstep (se 1 (by rfl) ⟨1048163, by rfl⟩ : syracuseStep 1397551 = 2096327) B2096327
theorem B1766299 : Blo 1240438 1766299 := bstep (se 1 (by rfl) ⟨1324724, by rfl⟩ : syracuseStep 1766299 = 2649449) B2649449
theorem B1242011 : Blo 1240438 1242011 := bstep (se 1 (by rfl) ⟨931508, by rfl⟩ : syracuseStep 1242011 = 1863017) B1863017
theorem B1397659 : Blo 1240438 1397659 := bstep (se 1 (by rfl) ⟨1048244, by rfl⟩ : syracuseStep 1397659 = 2096489) B2096489
theorem B1242063 : Blo 1240438 1242063 := bstep (se 1 (by rfl) ⟨931547, by rfl⟩ : syracuseStep 1242063 = 1863095) B1863095
theorem B1242087 : Blo 1240438 1242087 := bstep (se 1 (by rfl) ⟨931565, by rfl⟩ : syracuseStep 1242087 = 1863131) B1863131
theorem B3535969 : Blo 1240438 3535969 := bstep (se 2 (by rfl) ⟨1325988, by rfl⟩ : syracuseStep 3535969 = 2651977) B2651977
theorem B3355847 : Blo 1240438 3355847 := bstep (se 1 (by rfl) ⟨2516885, by rfl⟩ : syracuseStep 3355847 = 5033771) B5033771
theorem B3142871 : Blo 1240438 3142871 := bstep (se 1 (by rfl) ⟨2357153, by rfl⟩ : syracuseStep 3142871 = 4714307) B4714307
theorem B8950999 : Blo 1240438 8950999 := bstep (se 1 (by rfl) ⟨6713249, by rfl⟩ : syracuseStep 8950999 = 13426499) B13426499
theorem B21222647 : Blo 1240438 21222647 := bstep (se 1 (by rfl) ⟨15916985, by rfl⟩ : syracuseStep 21222647 = 31833971) B31833971
theorem B10597655 : Blo 1240438 10597655 := bstep (se 1 (by rfl) ⟨7948241, by rfl⟩ : syracuseStep 10597655 = 15896483) B15896483
theorem B1258783 : Blo 1240438 1258783 := bstep (se 1 (by rfl) ⟨944087, by rfl⟩ : syracuseStep 1258783 = 1888175) B1888175
theorem B1242399 : Blo 1240438 1242399 := bstep (se 1 (by rfl) ⟨931799, by rfl⟩ : syracuseStep 1242399 = 1863599) B1863599
theorem B10483181 : Blo 1240438 10483181 := bstep (se 3 (by rfl) ⟨1965596, by rfl⟩ : syracuseStep 10483181 = 3931193) B3931193
theorem B7075309 : Blo 1240438 7075309 := bstep (se 3 (by rfl) ⟨1326620, by rfl⟩ : syracuseStep 7075309 = 2653241) B2653241
theorem B3143225 : Blo 1240438 3143225 := bstep (se 2 (by rfl) ⟨1178709, by rfl⟩ : syracuseStep 3143225 = 2357419) B2357419
theorem B1570367 : Blo 1240438 1570367 := bstep (se 1 (by rfl) ⟨1177775, by rfl⟩ : syracuseStep 1570367 = 2355551) B2355551
theorem B2791007 : Blo 1240438 2791007 := bstep (se 1 (by rfl) ⟨2093255, by rfl⟩ : syracuseStep 2791007 = 4186511) B4186511
theorem B5306141 : Blo 1240438 5306141 := bstep (se 3 (by rfl) ⟨994901, by rfl⟩ : syracuseStep 5306141 = 1989803) B1989803
theorem B1988393 : Blo 1240438 1988393 := bstep (se 2 (by rfl) ⟨745647, by rfl⟩ : syracuseStep 1988393 = 1491295) B1491295
theorem B2094889 : Blo 1240438 2094889 := bstep (se 2 (by rfl) ⟨785583, by rfl⟩ : syracuseStep 2094889 = 1571167) B1571167
theorem B2357039 : Blo 1240438 2357039 := bstep (se 1 (by rfl) ⟨1767779, by rfl⟩ : syracuseStep 2357039 = 3535559) B3535559
theorem B3184439 : Blo 1240438 3184439 := bstep (se 1 (by rfl) ⟨2388329, by rfl⟩ : syracuseStep 3184439 = 4776659) B4776659
theorem B2791223 : Blo 1240438 2791223 := bstep (se 1 (by rfl) ⟨2093417, by rfl⟩ : syracuseStep 2791223 = 4186835) B4186835
theorem B1324955 : Blo 1240438 1324955 := bstep (se 1 (by rfl) ⟨993716, by rfl⟩ : syracuseStep 1324955 = 1987433) B1987433
theorem B38205371 : Blo 1240438 38205371 := bstep (se 1 (by rfl) ⟨28654028, by rfl⟩ : syracuseStep 38205371 = 57308057) B57308057
theorem B15915041 : Blo 1240438 15915041 := bstep (se 2 (by rfl) ⟨5968140, by rfl⟩ : syracuseStep 15915041 = 11936281) B11936281
theorem B4192289 : Blo 1240438 4192289 := bstep (se 2 (by rfl) ⟨1572108, by rfl⟩ : syracuseStep 4192289 = 3144217) B3144217
theorem B6289487 : Blo 1240438 6289487 := bstep (se 1 (by rfl) ⟨4717115, by rfl⟩ : syracuseStep 6289487 = 9434231) B9434231
theorem B2791529 : Blo 1240438 2791529 := bstep (se 2 (by rfl) ⟨1046823, by rfl⟩ : syracuseStep 2791529 = 2093647) B2093647
theorem B1767529 : Blo 1240438 1767529 := bstep (se 2 (by rfl) ⟨662823, by rfl⟩ : syracuseStep 1767529 = 1325647) B1325647
theorem B1767791 : Blo 1240438 1767791 := bstep (se 1 (by rfl) ⟨1325843, by rfl⟩ : syracuseStep 1767791 = 2651687) B2651687
theorem B4471291 : Blo 1240438 4471291 := bstep (se 1 (by rfl) ⟨3353468, by rfl⟩ : syracuseStep 4471291 = 6706937) B6706937
theorem B11328025 : Blo 1240438 11328025 := bstep (se 2 (by rfl) ⟨4248009, by rfl⟩ : syracuseStep 11328025 = 8496019) B8496019
theorem B5814823 : Blo 1240438 5814823 := bstep (se 1 (by rfl) ⟨4361117, by rfl⟩ : syracuseStep 5814823 = 8722235) B8722235
theorem B2095679 : Blo 1240438 2095679 := bstep (se 1 (by rfl) ⟨1571759, by rfl⟩ : syracuseStep 2095679 = 3143519) B3143519
theorem B8952383 : Blo 1240438 8952383 := bstep (se 1 (by rfl) ⟨6714287, by rfl⟩ : syracuseStep 8952383 = 13428575) B13428575
theorem B2792015 : Blo 1240438 2792015 := bstep (se 1 (by rfl) ⟨2094011, by rfl⟩ : syracuseStep 2792015 = 4188023) B4188023
theorem B8059499 : Blo 1240438 8059499 := bstep (se 1 (by rfl) ⟨6044624, by rfl⟩ : syracuseStep 8059499 = 12089249) B12089249
theorem B6707933 : Blo 1240438 6707933 := bstep (se 3 (by rfl) ⟨1257737, by rfl⟩ : syracuseStep 6707933 = 2515475) B2515475
theorem B2792159 : Blo 1240438 2792159 := bstep (se 1 (by rfl) ⟨2094119, by rfl⟩ : syracuseStep 2792159 = 4188239) B4188239
theorem B1325903 : Blo 1240438 1325903 := bstep (se 1 (by rfl) ⟨994427, by rfl⟩ : syracuseStep 1325903 = 1988855) B1988855
theorem B1571663 : Blo 1240438 1571663 := bstep (se 1 (by rfl) ⟨1178747, by rfl⟩ : syracuseStep 1571663 = 2357495) B2357495
theorem B2792411 : Blo 1240438 2792411 := bstep (se 1 (by rfl) ⟨2094308, by rfl⟩ : syracuseStep 2792411 = 4188617) B4188617
theorem B1571815 : Blo 1240438 1571815 := bstep (se 1 (by rfl) ⟨1178861, by rfl⟩ : syracuseStep 1571815 = 2357723) B2357723
theorem B2358247 : Blo 1240438 2358247 := bstep (se 1 (by rfl) ⟨1768685, by rfl⟩ : syracuseStep 2358247 = 3537371) B3537371
theorem B176766083 : Blo 1240438 176766083 := bstep (se 1 (by rfl) ⟨132574562, by rfl⟩ : syracuseStep 176766083 = 265149125) B265149125
theorem B2792591 : Blo 1240438 2792591 := bstep (se 1 (by rfl) ⟨2094443, by rfl⟩ : syracuseStep 2792591 = 4188887) B4188887
theorem B2653327 : Blo 1240438 2653327 := bstep (se 1 (by rfl) ⟨1989995, by rfl⟩ : syracuseStep 2653327 = 3979991) B3979991
theorem B2096347 : Blo 1240438 2096347 := bstep (se 1 (by rfl) ⟨1572260, by rfl⟩ : syracuseStep 2096347 = 3144521) B3144521
theorem B2792681 : Blo 1240438 2792681 := bstep (se 2 (by rfl) ⟨1047255, by rfl⟩ : syracuseStep 2792681 = 2094511) B2094511
theorem B2792735 : Blo 1240438 2792735 := bstep (se 1 (by rfl) ⟨2094551, by rfl⟩ : syracuseStep 2792735 = 4189103) B4189103
theorem B6282683 : Blo 1240438 6282683 := bstep (se 1 (by rfl) ⟨4712012, by rfl⟩ : syracuseStep 6282683 = 9424025) B9424025
theorem B2235847 : Blo 1240438 2235847 := bstep (se 1 (by rfl) ⟨1676885, by rfl⟩ : syracuseStep 2235847 = 3353771) B3353771
theorem B26844695 : Blo 1240438 26844695 := bstep (se 1 (by rfl) ⟨20133521, by rfl⟩ : syracuseStep 26844695 = 40267043) B40267043
theorem B8068633 : Blo 1240438 8068633 := bstep (se 2 (by rfl) ⟨3025737, by rfl⟩ : syracuseStep 8068633 = 6051475) B6051475
theorem B1326655 : Blo 1240438 1326655 := bstep (se 1 (by rfl) ⟨994991, by rfl⟩ : syracuseStep 1326655 = 1989983) B1989983
theorem B3776095 : Blo 1240438 3776095 := bstep (se 1 (by rfl) ⟨2832071, by rfl⟩ : syracuseStep 3776095 = 5664143) B5664143
theorem B5299921 : Blo 1240438 5299921 := bstep (se 2 (by rfl) ⟨1987470, by rfl⟩ : syracuseStep 5299921 = 3974941) B3974941
theorem B76472045 : Blo 1240438 76472045 := bstep (se 3 (by rfl) ⟨14338508, by rfl⟩ : syracuseStep 76472045 = 28677017) B28677017
theorem B4472617 : Blo 1240438 4472617 := bstep (se 2 (by rfl) ⟨1677231, by rfl⟩ : syracuseStep 4472617 = 3354463) B3354463
theorem B2793257 : Blo 1240438 2793257 := bstep (se 2 (by rfl) ⟨1047471, by rfl⟩ : syracuseStep 2793257 = 2094943) B2094943
theorem B10600253 : Blo 1240438 10600253 := bstep (se 3 (by rfl) ⟨1987547, by rfl⟩ : syracuseStep 10600253 = 3975095) B3975095
theorem B42983297 : Blo 1240438 42983297 := bstep (se 2 (by rfl) ⟨16118736, by rfl⟩ : syracuseStep 42983297 = 32237473) B32237473
theorem B43032709 : Blo 1240438 43032709 := bstep (se 4 (by rfl) ⟨4034316, by rfl⟩ : syracuseStep 43032709 = 8068633) B8068633
theorem B4710737 : Blo 1240438 4710737 := bstep (se 2 (by rfl) ⟨1766526, by rfl⟩ : syracuseStep 4710737 = 3533053) B3533053
theorem B21209525 : Blo 1240438 21209525 := bstep (se 5 (by rfl) ⟨994196, by rfl⟩ : syracuseStep 21209525 = 1988393) B1988393
theorem B4186619 : Blo 1240438 4186619 := bstep (se 1 (by rfl) ⟨3139964, by rfl⟩ : syracuseStep 4186619 = 6279929) B6279929
theorem B26854037 : Blo 1240438 26854037 := bstep (se 6 (by rfl) ⟨629391, by rfl⟩ : syracuseStep 26854037 = 1258783) B1258783
theorem B15909605 : Blo 1240438 15909605 := bstep (se 4 (by rfl) ⟨1491525, by rfl⟩ : syracuseStep 15909605 = 2983051) B2983051
theorem B4186889 : Blo 1240438 4186889 := bstep (se 2 (by rfl) ⟨1570083, by rfl⟩ : syracuseStep 4186889 = 3140167) B3140167
theorem B2237231 : Blo 1240438 2237231 := bstep (se 1 (by rfl) ⟨1677923, by rfl⟩ : syracuseStep 2237231 = 3355847) B3355847
theorem B14148431 : Blo 1240438 14148431 := bstep (se 1 (by rfl) ⟨10611323, by rfl⟩ : syracuseStep 14148431 = 21222647) B21222647
theorem B6988787 : Blo 1240438 6988787 := bstep (se 1 (by rfl) ⟨5241590, by rfl⟩ : syracuseStep 6988787 = 10483181) B10483181
theorem B1860671 : Blo 1240438 1860671 := bstep (se 1 (by rfl) ⟨1395503, by rfl⟩ : syracuseStep 1860671 = 2791007) B2791007
theorem B1860713 : Blo 1240438 1860713 := bstep (se 2 (by rfl) ⟨697767, by rfl⟩ : syracuseStep 1860713 = 1395535) B1395535
theorem B1860815 : Blo 1240438 1860815 := bstep (se 1 (by rfl) ⟨1395611, by rfl⟩ : syracuseStep 1860815 = 2791223) B2791223
theorem B25470247 : Blo 1240438 25470247 := bstep (se 1 (by rfl) ⟨19102685, by rfl⟩ : syracuseStep 25470247 = 38205371) B38205371
theorem B10610027 : Blo 1240438 10610027 := bstep (se 1 (by rfl) ⟨7957520, by rfl⟩ : syracuseStep 10610027 = 15915041) B15915041
theorem B2794859 : Blo 1240438 2794859 := bstep (se 1 (by rfl) ⟨2096144, by rfl⟩ : syracuseStep 2794859 = 4192289) B4192289
theorem B1861019 : Blo 1240438 1861019 := bstep (se 1 (by rfl) ⟨1395764, by rfl⟩ : syracuseStep 1861019 = 2791529) B2791529
theorem B4187645 : Blo 1240438 4187645 := bstep (se 3 (by rfl) ⟨785183, by rfl⟩ : syracuseStep 4187645 = 1570367) B1570367
theorem B1861241 : Blo 1240438 1861241 := bstep (se 2 (by rfl) ⟨697965, by rfl⟩ : syracuseStep 1861241 = 1395931) B1395931
theorem B2795129 : Blo 1240438 2795129 := bstep (se 2 (by rfl) ⟨1048173, by rfl⟩ : syracuseStep 2795129 = 2096347) B2096347
theorem B1861343 : Blo 1240438 1861343 := bstep (se 1 (by rfl) ⟨1396007, by rfl⟩ : syracuseStep 1861343 = 2792015) B2792015
theorem B1861439 : Blo 1240438 1861439 := bstep (se 1 (by rfl) ⟨1396079, by rfl⟩ : syracuseStep 1861439 = 2792159) B2792159
theorem B38733715 : Blo 1240438 38733715 := bstep (se 1 (by rfl) ⟨29050286, by rfl⟩ : syracuseStep 38733715 = 58100573) B58100573
theorem B8947655 : Blo 1240438 8947655 := bstep (se 1 (by rfl) ⟨6710741, by rfl⟩ : syracuseStep 8947655 = 13421483) B13421483
theorem B1861607 : Blo 1240438 1861607 := bstep (se 1 (by rfl) ⟨1396205, by rfl⟩ : syracuseStep 1861607 = 2792411) B2792411
theorem B1861625 : Blo 1240438 1861625 := bstep (se 2 (by rfl) ⟨698109, by rfl⟩ : syracuseStep 1861625 = 1396219) B1396219
theorem B117844055 : Blo 1240438 117844055 := bstep (se 1 (by rfl) ⟨88383041, by rfl⟩ : syracuseStep 117844055 = 176766083) B176766083
theorem B1886303 : Blo 1240438 1886303 := bstep (se 1 (by rfl) ⟨1414727, by rfl⟩ : syracuseStep 1886303 = 2829455) B2829455
theorem B1861727 : Blo 1240438 1861727 := bstep (se 1 (by rfl) ⟨1396295, by rfl⟩ : syracuseStep 1861727 = 2792591) B2792591
theorem B6285437 : Blo 1240438 6285437 := bstep (se 3 (by rfl) ⟨1178519, by rfl⟩ : syracuseStep 6285437 = 2357039) B2357039
theorem B1861787 : Blo 1240438 1861787 := bstep (se 1 (by rfl) ⟨1396340, by rfl⟩ : syracuseStep 1861787 = 2792681) B2792681
theorem B1861823 : Blo 1240438 1861823 := bstep (se 1 (by rfl) ⟨1396367, by rfl⟩ : syracuseStep 1861823 = 2792735) B2792735
theorem B1861865 : Blo 1240438 1861865 := bstep (se 2 (by rfl) ⟨698199, by rfl⟩ : syracuseStep 1861865 = 1396399) B1396399
theorem B4188455 : Blo 1240438 4188455 := bstep (se 1 (by rfl) ⟨3141341, by rfl⟩ : syracuseStep 4188455 = 6282683) B6282683
theorem B3533213 : Blo 1240438 3533213 := bstep (se 3 (by rfl) ⟨662477, by rfl⟩ : syracuseStep 3533213 = 1324955) B1324955
theorem B50981363 : Blo 1240438 50981363 := bstep (se 1 (by rfl) ⟨38236022, by rfl⟩ : syracuseStep 50981363 = 76472045) B76472045
theorem B1862171 : Blo 1240438 1862171 := bstep (se 1 (by rfl) ⟨1396628, by rfl⟩ : syracuseStep 1862171 = 2793257) B2793257
theorem B1862249 : Blo 1240438 1862249 := bstep (se 2 (by rfl) ⟨698343, by rfl⟩ : syracuseStep 1862249 = 1396687) B1396687
theorem B9431801 : Blo 1240438 9431801 := bstep (se 2 (by rfl) ⟨3536925, by rfl⟩ : syracuseStep 9431801 = 7073851) B7073851
theorem B31820849 : Blo 1240438 31820849 := bstep (se 2 (by rfl) ⟨11932818, by rfl⟩ : syracuseStep 31820849 = 23865637) B23865637
theorem B1862777 : Blo 1240438 1862777 := bstep (se 2 (by rfl) ⟨698541, by rfl⟩ : syracuseStep 1862777 = 1397083) B1397083
theorem B4189319 : Blo 1240438 4189319 := bstep (se 1 (by rfl) ⟨3141989, by rfl⟩ : syracuseStep 4189319 = 6283979) B6283979
theorem B1862879 : Blo 1240438 1862879 := bstep (se 1 (by rfl) ⟨1397159, by rfl⟩ : syracuseStep 1862879 = 2794319) B2794319
theorem B4189427 : Blo 1240438 4189427 := bstep (se 1 (by rfl) ⟨3142070, by rfl⟩ : syracuseStep 4189427 = 6284141) B6284141
theorem B1862921 : Blo 1240438 1862921 := bstep (se 2 (by rfl) ⟨698595, by rfl⟩ : syracuseStep 1862921 = 1397191) B1397191
theorem B1863023 : Blo 1240438 1863023 := bstep (se 1 (by rfl) ⟨1397267, by rfl⟩ : syracuseStep 1863023 = 2794535) B2794535
theorem B7753097 : Blo 1240438 7753097 := bstep (se 2 (by rfl) ⟨2907411, by rfl⟩ : syracuseStep 7753097 = 5814823) B5814823
theorem B2829737 : Blo 1240438 2829737 := bstep (se 2 (by rfl) ⟨1061151, by rfl⟩ : syracuseStep 2829737 = 2122303) B2122303
theorem B1240551 : Blo 1240438 1240551 := bstep (se 1 (by rfl) ⟨930413, by rfl⟩ : syracuseStep 1240551 = 1860827) B1860827
theorem B1863143 : Blo 1240438 1863143 := bstep (se 1 (by rfl) ⟨1397357, by rfl⟩ : syracuseStep 1863143 = 2794715) B2794715
theorem B7065103 : Blo 1240438 7065103 := bstep (se 1 (by rfl) ⟨5298827, by rfl⟩ : syracuseStep 7065103 = 10597655) B10597655
theorem B11922977 : Blo 1240438 11922977 := bstep (se 2 (by rfl) ⟨4471116, by rfl⟩ : syracuseStep 11922977 = 8942233) B8942233
theorem B1240667 : Blo 1240438 1240667 := bstep (se 1 (by rfl) ⟨930500, by rfl⟩ : syracuseStep 1240667 = 1861001) B1861001
theorem B1863275 : Blo 1240438 1863275 := bstep (se 1 (by rfl) ⟨1397456, by rfl⟩ : syracuseStep 1863275 = 2794913) B2794913
theorem B4714109 : Blo 1240438 4714109 := bstep (se 3 (by rfl) ⟨883895, by rfl⟩ : syracuseStep 4714109 = 1767791) B1767791
theorem B3534511 : Blo 1240438 3534511 := bstep (se 1 (by rfl) ⟨2650883, by rfl⟩ : syracuseStep 3534511 = 5301767) B5301767
theorem B1863401 : Blo 1240438 1863401 := bstep (se 2 (by rfl) ⟨698775, by rfl⟩ : syracuseStep 1863401 = 1397551) B1397551
theorem B1240903 : Blo 1240438 1240903 := bstep (se 1 (by rfl) ⟨930677, by rfl⟩ : syracuseStep 1240903 = 1861355) B1861355
theorem B2355065 : Blo 1240438 2355065 := bstep (se 2 (by rfl) ⟨883149, by rfl⟩ : syracuseStep 2355065 = 1766299) B1766299
theorem B1863545 : Blo 1240438 1863545 := bstep (se 2 (by rfl) ⟨698829, by rfl⟩ : syracuseStep 1863545 = 1397659) B1397659
theorem B1241055 : Blo 1240438 1241055 := bstep (se 1 (by rfl) ⟨930791, by rfl⟩ : syracuseStep 1241055 = 1861583) B1861583
theorem B1863647 : Blo 1240438 1863647 := bstep (se 1 (by rfl) ⟨1397735, by rfl⟩ : syracuseStep 1863647 = 2795471) B2795471
theorem B4714625 : Blo 1240438 4714625 := bstep (se 2 (by rfl) ⟨1767984, by rfl⟩ : syracuseStep 4714625 = 3535969) B3535969
theorem B1241319 : Blo 1240438 1241319 := bstep (se 1 (by rfl) ⟨930989, by rfl⟩ : syracuseStep 1241319 = 1861979) B1861979
theorem B4714807 : Blo 1240438 4714807 := bstep (se 1 (by rfl) ⟨3536105, by rfl⟩ : syracuseStep 4714807 = 7072211) B7072211
theorem B1241471 : Blo 1240438 1241471 := bstep (se 1 (by rfl) ⟨931103, by rfl⟩ : syracuseStep 1241471 = 1862207) B1862207
theorem B1397119 : Blo 1240438 1397119 := bstep (se 1 (by rfl) ⟨1047839, by rfl⟩ : syracuseStep 1397119 = 2095679) B2095679
theorem B5968255 : Blo 1240438 5968255 := bstep (se 1 (by rfl) ⟨4476191, by rfl⟩ : syracuseStep 5968255 = 8952383) B8952383
theorem B7172495 : Blo 1240438 7172495 := bstep (se 1 (by rfl) ⟨5379371, by rfl⟩ : syracuseStep 7172495 = 10758743) B10758743
theorem B2093519 : Blo 1240438 2093519 := bstep (se 1 (by rfl) ⟨1570139, by rfl⟩ : syracuseStep 2093519 = 3140279) B3140279
theorem B1241551 : Blo 1240438 1241551 := bstep (se 1 (by rfl) ⟨931163, by rfl⟩ : syracuseStep 1241551 = 1862327) B1862327
theorem B25825817 : Blo 1240438 25825817 := bstep (se 2 (by rfl) ⟨9684681, by rfl⟩ : syracuseStep 25825817 = 19369363) B19369363
theorem B1241703 : Blo 1240438 1241703 := bstep (se 1 (by rfl) ⟨931277, by rfl⟩ : syracuseStep 1241703 = 1862555) B1862555
theorem B9433745 : Blo 1240438 9433745 := bstep (se 2 (by rfl) ⟨3537654, by rfl⟩ : syracuseStep 9433745 = 7075309) B7075309
theorem B7549661 : Blo 1240438 7549661 := bstep (se 3 (by rfl) ⟨1415561, by rfl⟩ : syracuseStep 7549661 = 2831123) B2831123
theorem B5034793 : Blo 1240438 5034793 := bstep (se 2 (by rfl) ⟨1888047, by rfl⟩ : syracuseStep 5034793 = 3776095) B3776095
theorem B8491837 : Blo 1240438 8491837 := bstep (se 3 (by rfl) ⟨1592219, by rfl⟩ : syracuseStep 8491837 = 3184439) B3184439
theorem B1241967 : Blo 1240438 1241967 := bstep (se 1 (by rfl) ⟨931475, by rfl⟩ : syracuseStep 1241967 = 1862951) B1862951
theorem B3535741 : Blo 1240438 3535741 := bstep (se 3 (by rfl) ⟨662951, by rfl⟩ : syracuseStep 3535741 = 1325903) B1325903
theorem B4191101 : Blo 1240438 4191101 := bstep (se 3 (by rfl) ⟨785831, by rfl⟩ : syracuseStep 4191101 = 1571663) B1571663
theorem B1242023 : Blo 1240438 1242023 := bstep (se 1 (by rfl) ⟨931517, by rfl⟩ : syracuseStep 1242023 = 1863035) B1863035
theorem B3535787 : Blo 1240438 3535787 := bstep (se 1 (by rfl) ⟨2651840, by rfl⟩ : syracuseStep 3535787 = 5303681) B5303681
theorem B7066561 : Blo 1240438 7066561 := bstep (se 2 (by rfl) ⟨2649960, by rfl⟩ : syracuseStep 7066561 = 5299921) B5299921
theorem B2356219 : Blo 1240438 2356219 := bstep (se 1 (by rfl) ⟨1767164, by rfl⟩ : syracuseStep 2356219 = 3534329) B3534329
theorem B1242107 : Blo 1240438 1242107 := bstep (se 1 (by rfl) ⟨931580, by rfl⟩ : syracuseStep 1242107 = 1863161) B1863161
theorem B17896463 : Blo 1240438 17896463 := bstep (se 1 (by rfl) ⟨13422347, by rfl⟩ : syracuseStep 17896463 = 26844695) B26844695
theorem B1242175 : Blo 1240438 1242175 := bstep (se 1 (by rfl) ⟨931631, by rfl⟩ : syracuseStep 1242175 = 1863263) B1863263
theorem B2094187 : Blo 1240438 2094187 := bstep (se 1 (by rfl) ⟨1570640, by rfl⟩ : syracuseStep 2094187 = 3141281) B3141281
theorem B4191371 : Blo 1240438 4191371 := bstep (se 1 (by rfl) ⟨3143528, by rfl⟩ : syracuseStep 4191371 = 6287057) B6287057
theorem B1242319 : Blo 1240438 1242319 := bstep (se 1 (by rfl) ⟨931739, by rfl⟩ : syracuseStep 1242319 = 1863479) B1863479
theorem B7066835 : Blo 1240438 7066835 := bstep (se 1 (by rfl) ⟨5300126, by rfl⟩ : syracuseStep 7066835 = 10600253) B10600253
theorem B10892531 : Blo 1240438 10892531 := bstep (se 1 (by rfl) ⟨8169398, by rfl⟩ : syracuseStep 10892531 = 16338797) B16338797
theorem B2094491 : Blo 1240438 2094491 := bstep (se 1 (by rfl) ⟨1570868, by rfl⟩ : syracuseStep 2094491 = 3141737) B3141737
theorem B5305799 : Blo 1240438 5305799 := bstep (se 1 (by rfl) ⟨3979349, by rfl⟩ : syracuseStep 5305799 = 7958699) B7958699
theorem B6288839 : Blo 1240438 6288839 := bstep (se 1 (by rfl) ⟨4716629, by rfl⟩ : syracuseStep 6288839 = 9433259) B9433259
theorem B2356705 : Blo 1240438 2356705 := bstep (se 2 (by rfl) ⟨883764, by rfl⟩ : syracuseStep 2356705 = 1767529) B1767529
theorem B13424251 : Blo 1240438 13424251 := bstep (se 1 (by rfl) ⟨10068188, by rfl⟩ : syracuseStep 13424251 = 20136377) B20136377
theorem B6461099 : Blo 1240438 6461099 := bstep (se 1 (by rfl) ⟨4845824, by rfl⟩ : syracuseStep 6461099 = 9691649) B9691649
theorem B2094815 : Blo 1240438 2094815 := bstep (se 1 (by rfl) ⟨1571111, by rfl⟩ : syracuseStep 2094815 = 3142223) B3142223
theorem B5306107 : Blo 1240438 5306107 := bstep (se 1 (by rfl) ⟨3979580, by rfl⟩ : syracuseStep 5306107 = 7959161) B7959161
theorem B7960315 : Blo 1240438 7960315 := bstep (se 1 (by rfl) ⟨5970236, by rfl⟩ : syracuseStep 7960315 = 11940473) B11940473
theorem B1767199 : Blo 1240438 1767199 := bstep (se 1 (by rfl) ⟨1325399, by rfl⟩ : syracuseStep 1767199 = 2650799) B2650799
theorem B3979145 : Blo 1240438 3979145 := bstep (se 2 (by rfl) ⟨1492179, by rfl⟩ : syracuseStep 3979145 = 2984359) B2984359
theorem B5961721 : Blo 1240438 5961721 := bstep (se 2 (by rfl) ⟨2235645, by rfl⟩ : syracuseStep 5961721 = 4471291) B4471291
theorem B15104033 : Blo 1240438 15104033 := bstep (se 2 (by rfl) ⟨5664012, by rfl⟩ : syracuseStep 15104033 = 11328025) B11328025
theorem B2095247 : Blo 1240438 2095247 := bstep (se 1 (by rfl) ⟨1571435, by rfl⟩ : syracuseStep 2095247 = 3142871) B3142871
theorem B28686629 : Blo 1240438 28686629 := bstep (se 4 (by rfl) ⟨2689371, by rfl⟩ : syracuseStep 28686629 = 5378743) B5378743
theorem B2095483 : Blo 1240438 2095483 := bstep (se 1 (by rfl) ⟨1571612, by rfl⟩ : syracuseStep 2095483 = 3143225) B3143225
theorem B3537427 : Blo 1240438 3537427 := bstep (se 1 (by rfl) ⟨2653070, by rfl⟩ : syracuseStep 3537427 = 5306141) B5306141
theorem B2095753 : Blo 1240438 2095753 := bstep (se 2 (by rfl) ⟨785907, by rfl⟩ : syracuseStep 2095753 = 1571815) B1571815
theorem B3144329 : Blo 1240438 3144329 := bstep (se 2 (by rfl) ⟨1179123, by rfl⟩ : syracuseStep 3144329 = 2358247) B2358247
theorem B4192991 : Blo 1240438 4192991 := bstep (se 1 (by rfl) ⟨3144743, by rfl⟩ : syracuseStep 4192991 = 6289487) B6289487
theorem B3537769 : Blo 1240438 3537769 := bstep (se 2 (by rfl) ⟨1326663, by rfl⟩ : syracuseStep 3537769 = 2653327) B2653327
theorem B11934665 : Blo 1240438 11934665 := bstep (se 2 (by rfl) ⟨4475499, by rfl⟩ : syracuseStep 11934665 = 8950999) B8950999
theorem B5372999 : Blo 1240438 5372999 := bstep (se 1 (by rfl) ⟨4029749, by rfl⟩ : syracuseStep 5372999 = 8059499) B8059499
theorem B2792519 : Blo 1240438 2792519 := bstep (se 1 (by rfl) ⟨2094389, by rfl⟩ : syracuseStep 2792519 = 4188779) B4188779
theorem B3824765 : Blo 1240438 3824765 := bstep (se 3 (by rfl) ⟨717143, by rfl⟩ : syracuseStep 3824765 = 1434287) B1434287
theorem B4471955 : Blo 1240438 4471955 := bstep (se 1 (by rfl) ⟨3353966, by rfl⟩ : syracuseStep 4471955 = 6707933) B6707933
theorem B2981129 : Blo 1240438 2981129 := bstep (se 2 (by rfl) ⟨1117923, by rfl⟩ : syracuseStep 2981129 = 2235847) B2235847
theorem B1768873 : Blo 1240438 1768873 := bstep (se 2 (by rfl) ⟨663327, by rfl⟩ : syracuseStep 1768873 = 1326655) B1326655
theorem B2792915 : Blo 1240438 2792915 := bstep (se 1 (by rfl) ⟨2094686, by rfl⟩ : syracuseStep 2792915 = 4189373) B4189373
theorem B2236079 : Blo 1240438 2236079 := bstep (se 1 (by rfl) ⟨1677059, by rfl⟩ : syracuseStep 2236079 = 3354119) B3354119
theorem B5963489 : Blo 1240438 5963489 := bstep (se 2 (by rfl) ⟨2236308, by rfl⟩ : syracuseStep 5963489 = 4472617) B4472617
theorem B2793185 : Blo 1240438 2793185 := bstep (se 2 (by rfl) ⟨1047444, by rfl⟩ : syracuseStep 2793185 = 2094889) B2094889
theorem B3776327 : Blo 1240438 3776327 := bstep (se 1 (by rfl) ⟨2832245, by rfl⟩ : syracuseStep 3776327 = 5664491) B5664491
theorem B28655531 : Blo 1240438 28655531 := bstep (se 1 (by rfl) ⟨21491648, by rfl⟩ : syracuseStep 28655531 = 42983297) B42983297
theorem B57376945 : Blo 1240438 57376945 := bstep (se 2 (by rfl) ⟨21516354, by rfl⟩ : syracuseStep 57376945 = 43032709) B43032709
theorem B14139683 : Blo 1240438 14139683 := bstep (se 1 (by rfl) ⟨10604762, by rfl⟩ : syracuseStep 14139683 = 21209525) B21209525
theorem B2793977 : Blo 1240438 2793977 := bstep (se 2 (by rfl) ⟨1047741, by rfl⟩ : syracuseStep 2793977 = 2095483) B2095483
theorem B2794067 : Blo 1240438 2794067 := bstep (se 1 (by rfl) ⟨2095550, by rfl⟩ : syracuseStep 2794067 = 4191101) B4191101
theorem B2794247 : Blo 1240438 2794247 := bstep (se 1 (by rfl) ⟨2095685, by rfl⟩ : syracuseStep 2794247 = 4191371) B4191371
theorem B4711223 : Blo 1240438 4711223 := bstep (se 1 (by rfl) ⟨3533417, by rfl⟩ : syracuseStep 4711223 = 7066835) B7066835
theorem B2794337 : Blo 1240438 2794337 := bstep (se 2 (by rfl) ⟨1047876, by rfl⟩ : syracuseStep 2794337 = 2095753) B2095753
theorem B11322449 : Blo 1240438 11322449 := bstep (se 2 (by rfl) ⟨4245918, by rfl⟩ : syracuseStep 11322449 = 8491837) B8491837
theorem B9422081 : Blo 1240438 9422081 := bstep (se 2 (by rfl) ⟨3533280, by rfl⟩ : syracuseStep 9422081 = 7066561) B7066561
theorem B5965103 : Blo 1240438 5965103 := bstep (se 1 (by rfl) ⟨4473827, by rfl⟩ : syracuseStep 5965103 = 8947655) B8947655
theorem B10069355 : Blo 1240438 10069355 := bstep (se 1 (by rfl) ⟨7552016, by rfl⟩ : syracuseStep 10069355 = 15104033) B15104033
theorem B78562703 : Blo 1240438 78562703 := bstep (se 1 (by rfl) ⟨58922027, by rfl⟩ : syracuseStep 78562703 = 117844055) B117844055
theorem B31794605 : Blo 1240438 31794605 := bstep (se 3 (by rfl) ⟨5961488, by rfl⟩ : syracuseStep 31794605 = 11922977) B11922977
theorem B2795327 : Blo 1240438 2795327 := bstep (se 1 (by rfl) ⟨2096495, by rfl⟩ : syracuseStep 2795327 = 4192991) B4192991
theorem B7956443 : Blo 1240438 7956443 := bstep (se 1 (by rfl) ⟨5967332, by rfl⟩ : syracuseStep 7956443 = 11934665) B11934665
theorem B3581999 : Blo 1240438 3581999 := bstep (se 1 (by rfl) ⟨2686499, by rfl⟩ : syracuseStep 3581999 = 5372999) B5372999
theorem B1861679 : Blo 1240438 1861679 := bstep (se 1 (by rfl) ⟨1396259, by rfl⟩ : syracuseStep 1861679 = 2792519) B2792519
theorem B2549843 : Blo 1240438 2549843 := bstep (se 1 (by rfl) ⟨1912382, by rfl⟩ : syracuseStep 2549843 = 3824765) B3824765
theorem B206579813 : Blo 1240438 206579813 := bstep (se 4 (by rfl) ⟨19366857, by rfl⟩ : syracuseStep 206579813 = 38733715) B38733715
theorem B5965949 : Blo 1240438 5965949 := bstep (se 3 (by rfl) ⟨1118615, by rfl⟩ : syracuseStep 5965949 = 2237231) B2237231
theorem B4712681 : Blo 1240438 4712681 := bstep (se 2 (by rfl) ⟨1767255, by rfl⟩ : syracuseStep 4712681 = 3534511) B3534511
theorem B1886491 : Blo 1240438 1886491 := bstep (se 1 (by rfl) ⟨1414868, by rfl⟩ : syracuseStep 1886491 = 2829737) B2829737
theorem B1861943 : Blo 1240438 1861943 := bstep (se 1 (by rfl) ⟨1396457, by rfl⟩ : syracuseStep 1861943 = 2792915) B2792915
theorem B3975659 : Blo 1240438 3975659 := bstep (se 1 (by rfl) ⟨2981744, by rfl⟩ : syracuseStep 3975659 = 5963489) B5963489
theorem B1862123 : Blo 1240438 1862123 := bstep (se 1 (by rfl) ⟨1396592, by rfl⟩ : syracuseStep 1862123 = 2793185) B2793185
theorem B2517551 : Blo 1240438 2517551 := bstep (se 1 (by rfl) ⟨1888163, by rfl⟩ : syracuseStep 2517551 = 3776327) B3776327
theorem B7948961 : Blo 1240438 7948961 := bstep (se 2 (by rfl) ⟨2980860, by rfl⟩ : syracuseStep 7948961 = 5961721) B5961721
theorem B3140491 : Blo 1240438 3140491 := bstep (se 1 (by rfl) ⟨2355368, by rfl⟩ : syracuseStep 3140491 = 4710737) B4710737
theorem B1395679 : Blo 1240438 1395679 := bstep (se 1 (by rfl) ⟨1046759, by rfl⟩ : syracuseStep 1395679 = 2093519) B2093519
theorem B6286409 : Blo 1240438 6286409 := bstep (se 2 (by rfl) ⟨2357403, by rfl⟩ : syracuseStep 6286409 = 4714807) B4714807
theorem B17902691 : Blo 1240438 17902691 := bstep (se 1 (by rfl) ⟨13427018, by rfl⟩ : syracuseStep 17902691 = 26854037) B26854037
theorem B5033107 : Blo 1240438 5033107 := bstep (se 1 (by rfl) ⟨3774830, by rfl⟩ : syracuseStep 5033107 = 7549661) B7549661
theorem B1862825 : Blo 1240438 1862825 := bstep (se 2 (by rfl) ⟨698559, by rfl⟩ : syracuseStep 1862825 = 1397119) B1397119
theorem B7957673 : Blo 1240438 7957673 := bstep (se 2 (by rfl) ⟨2984127, by rfl⟩ : syracuseStep 7957673 = 5968255) B5968255
theorem B9432287 : Blo 1240438 9432287 := bstep (se 1 (by rfl) ⟨7074215, by rfl⟩ : syracuseStep 9432287 = 14148431) B14148431
theorem B11930975 : Blo 1240438 11930975 := bstep (se 1 (by rfl) ⟨8948231, by rfl⟩ : syracuseStep 11930975 = 17896463) B17896463
theorem B7949677 : Blo 1240438 7949677 := bstep (se 3 (by rfl) ⟨1490564, by rfl⟩ : syracuseStep 7949677 = 2981129) B2981129
theorem B1240447 : Blo 1240438 1240447 := bstep (se 1 (by rfl) ⟨930335, by rfl⟩ : syracuseStep 1240447 = 1860671) B1860671
theorem B1240475 : Blo 1240438 1240475 := bstep (se 1 (by rfl) ⟨930356, by rfl⟩ : syracuseStep 1240475 = 1860713) B1860713
theorem B1240543 : Blo 1240438 1240543 := bstep (se 1 (by rfl) ⟨930407, by rfl⟩ : syracuseStep 1240543 = 1860815) B1860815
theorem B7261687 : Blo 1240438 7261687 := bstep (se 1 (by rfl) ⟨5446265, by rfl⟩ : syracuseStep 7261687 = 10892531) B10892531
theorem B7073351 : Blo 1240438 7073351 := bstep (se 1 (by rfl) ⟨5305013, by rfl⟩ : syracuseStep 7073351 = 10610027) B10610027
theorem B1863239 : Blo 1240438 1863239 := bstep (se 1 (by rfl) ⟨1397429, by rfl⟩ : syracuseStep 1863239 = 2794859) B2794859
theorem B1240679 : Blo 1240438 1240679 := bstep (se 1 (by rfl) ⟨930509, by rfl⟩ : syracuseStep 1240679 = 1861019) B1861019
theorem B1396327 : Blo 1240438 1396327 := bstep (se 1 (by rfl) ⟨1047245, by rfl⟩ : syracuseStep 1396327 = 2094491) B2094491
theorem B6713057 : Blo 1240438 6713057 := bstep (se 2 (by rfl) ⟨2517396, by rfl⟩ : syracuseStep 6713057 = 5034793) B5034793
theorem B1240827 : Blo 1240438 1240827 := bstep (se 1 (by rfl) ⟨930620, by rfl⟩ : syracuseStep 1240827 = 1861241) B1861241
theorem B1863419 : Blo 1240438 1863419 := bstep (se 1 (by rfl) ⟨1397564, by rfl⟩ : syracuseStep 1863419 = 2795129) B2795129
theorem B1240895 : Blo 1240438 1240895 := bstep (se 1 (by rfl) ⟨930671, by rfl⟩ : syracuseStep 1240895 = 1861343) B1861343
theorem B1396543 : Blo 1240438 1396543 := bstep (se 1 (by rfl) ⟨1047407, by rfl⟩ : syracuseStep 1396543 = 2094815) B2094815
theorem B4714321 : Blo 1240438 4714321 := bstep (se 2 (by rfl) ⟨1767870, by rfl⟩ : syracuseStep 4714321 = 3535741) B3535741
theorem B1240959 : Blo 1240438 1240959 := bstep (se 1 (by rfl) ⟨930719, by rfl⟩ : syracuseStep 1240959 = 1861439) B1861439
theorem B1241071 : Blo 1240438 1241071 := bstep (se 1 (by rfl) ⟨930803, by rfl⟩ : syracuseStep 1241071 = 1861607) B1861607
theorem B3141625 : Blo 1240438 3141625 := bstep (se 2 (by rfl) ⟨1178109, by rfl⟩ : syracuseStep 3141625 = 2356219) B2356219
theorem B1241083 : Blo 1240438 1241083 := bstep (se 1 (by rfl) ⟨930812, by rfl⟩ : syracuseStep 1241083 = 1861625) B1861625
theorem B1257535 : Blo 1240438 1257535 := bstep (se 1 (by rfl) ⟨943151, by rfl⟩ : syracuseStep 1257535 = 1886303) B1886303
theorem B1241151 : Blo 1240438 1241151 := bstep (se 1 (by rfl) ⟨930863, by rfl⟩ : syracuseStep 1241151 = 1861727) B1861727
theorem B4190291 : Blo 1240438 4190291 := bstep (se 1 (by rfl) ⟨3142718, by rfl⟩ : syracuseStep 4190291 = 6285437) B6285437
theorem B1396831 : Blo 1240438 1396831 := bstep (se 1 (by rfl) ⟨1047623, by rfl⟩ : syracuseStep 1396831 = 2095247) B2095247
theorem B1241191 : Blo 1240438 1241191 := bstep (se 1 (by rfl) ⟨930893, by rfl⟩ : syracuseStep 1241191 = 1861787) B1861787
theorem B1241215 : Blo 1240438 1241215 := bstep (se 1 (by rfl) ⟨930911, by rfl⟩ : syracuseStep 1241215 = 1861823) B1861823
theorem B1241243 : Blo 1240438 1241243 := bstep (se 1 (by rfl) ⟨930932, by rfl⟩ : syracuseStep 1241243 = 1861865) B1861865
theorem B19124419 : Blo 1240438 19124419 := bstep (se 1 (by rfl) ⟨14343314, by rfl⟩ : syracuseStep 19124419 = 28686629) B28686629
theorem B2355475 : Blo 1240438 2355475 := bstep (se 1 (by rfl) ⟨1766606, by rfl⟩ : syracuseStep 2355475 = 3533213) B3533213
theorem B1241447 : Blo 1240438 1241447 := bstep (se 1 (by rfl) ⟨931085, by rfl⟩ : syracuseStep 1241447 = 1862171) B1862171
theorem B33960329 : Blo 1240438 33960329 := bstep (se 2 (by rfl) ⟨12735123, by rfl⟩ : syracuseStep 33960329 = 25470247) B25470247
theorem B1241499 : Blo 1240438 1241499 := bstep (se 1 (by rfl) ⟨931124, by rfl⟩ : syracuseStep 1241499 = 1862249) B1862249
theorem B6287867 : Blo 1240438 6287867 := bstep (se 1 (by rfl) ⟨4715900, by rfl⟩ : syracuseStep 6287867 = 9431801) B9431801
theorem B3142273 : Blo 1240438 3142273 := bstep (se 2 (by rfl) ⟨1178352, by rfl⟩ : syracuseStep 3142273 = 2356705) B2356705
theorem B21213899 : Blo 1240438 21213899 := bstep (se 1 (by rfl) ⟨15910424, by rfl⟩ : syracuseStep 21213899 = 31820849) B31820849
theorem B1241851 : Blo 1240438 1241851 := bstep (se 1 (by rfl) ⟨931388, by rfl⟩ : syracuseStep 1241851 = 1862777) B1862777
theorem B1241919 : Blo 1240438 1241919 := bstep (se 1 (by rfl) ⟨931439, by rfl⟩ : syracuseStep 1241919 = 1862879) B1862879
theorem B1241947 : Blo 1240438 1241947 := bstep (se 1 (by rfl) ⟨931460, by rfl⟩ : syracuseStep 1241947 = 1862921) B1862921
theorem B1242015 : Blo 1240438 1242015 := bstep (se 1 (by rfl) ⟨931511, by rfl⟩ : syracuseStep 1242015 = 1863023) B1863023
theorem B1242095 : Blo 1240438 1242095 := bstep (se 1 (by rfl) ⟨931571, by rfl⟩ : syracuseStep 1242095 = 1863143) B1863143
theorem B7074809 : Blo 1240438 7074809 := bstep (se 2 (by rfl) ⟨2653053, by rfl⟩ : syracuseStep 7074809 = 5306107) B5306107
theorem B10613753 : Blo 1240438 10613753 := bstep (se 2 (by rfl) ⟨3980157, by rfl⟩ : syracuseStep 10613753 = 7960315) B7960315
theorem B2356265 : Blo 1240438 2356265 := bstep (se 2 (by rfl) ⟨883599, by rfl⟩ : syracuseStep 2356265 = 1767199) B1767199
theorem B1242183 : Blo 1240438 1242183 := bstep (se 1 (by rfl) ⟨931637, by rfl⟩ : syracuseStep 1242183 = 1863275) B1863275
theorem B3142739 : Blo 1240438 3142739 := bstep (se 1 (by rfl) ⟨2357054, by rfl⟩ : syracuseStep 3142739 = 4714109) B4714109
theorem B1242267 : Blo 1240438 1242267 := bstep (se 1 (by rfl) ⟨931700, by rfl⟩ : syracuseStep 1242267 = 1863401) B1863401
theorem B1570043 : Blo 1240438 1570043 := bstep (se 1 (by rfl) ⟨1177532, by rfl⟩ : syracuseStep 1570043 = 2355065) B2355065
theorem B1242363 : Blo 1240438 1242363 := bstep (se 1 (by rfl) ⟨931772, by rfl⟩ : syracuseStep 1242363 = 1863545) B1863545
theorem B1242431 : Blo 1240438 1242431 := bstep (se 1 (by rfl) ⟨931823, by rfl⟩ : syracuseStep 1242431 = 1863647) B1863647
theorem B3143083 : Blo 1240438 3143083 := bstep (se 1 (by rfl) ⟨2357312, by rfl⟩ : syracuseStep 3143083 = 4714625) B4714625
theorem B4781663 : Blo 1240438 4781663 := bstep (se 1 (by rfl) ⟨3586247, by rfl⟩ : syracuseStep 4781663 = 7172495) B7172495
theorem B2791079 : Blo 1240438 2791079 := bstep (se 1 (by rfl) ⟨2093309, by rfl⟩ : syracuseStep 2791079 = 4186619) B4186619
theorem B17217211 : Blo 1240438 17217211 := bstep (se 1 (by rfl) ⟨12912908, by rfl⟩ : syracuseStep 17217211 = 25825817) B25825817
theorem B6289163 : Blo 1240438 6289163 := bstep (se 1 (by rfl) ⟨4716872, by rfl⟩ : syracuseStep 6289163 = 9433745) B9433745
theorem B10606403 : Blo 1240438 10606403 := bstep (se 1 (by rfl) ⟨7954802, by rfl⟩ : syracuseStep 10606403 = 15909605) B15909605
theorem B2791259 : Blo 1240438 2791259 := bstep (se 1 (by rfl) ⟨2093444, by rfl⟩ : syracuseStep 2791259 = 4186889) B4186889
theorem B2357191 : Blo 1240438 2357191 := bstep (se 1 (by rfl) ⟨1767893, by rfl⟩ : syracuseStep 2357191 = 3535787) B3535787
theorem B4659191 : Blo 1240438 4659191 := bstep (se 1 (by rfl) ⟨3494393, by rfl⟩ : syracuseStep 4659191 = 6988787) B6988787
theorem B4716569 : Blo 1240438 4716569 := bstep (se 2 (by rfl) ⟨1768713, by rfl⟩ : syracuseStep 4716569 = 3537427) B3537427
theorem B3537199 : Blo 1240438 3537199 := bstep (se 1 (by rfl) ⟨2652899, by rfl⟩ : syracuseStep 3537199 = 5305799) B5305799
theorem B4192559 : Blo 1240438 4192559 := bstep (se 1 (by rfl) ⟨3144419, by rfl⟩ : syracuseStep 4192559 = 6288839) B6288839
theorem B2791763 : Blo 1240438 2791763 := bstep (se 1 (by rfl) ⟨2093822, by rfl⟩ : syracuseStep 2791763 = 4187645) B4187645
theorem B4307399 : Blo 1240438 4307399 := bstep (se 1 (by rfl) ⟨3230549, by rfl⟩ : syracuseStep 4307399 = 6461099) B6461099
theorem B4717025 : Blo 1240438 4717025 := bstep (se 2 (by rfl) ⟨1768884, by rfl⟩ : syracuseStep 4717025 = 3537769) B3537769
theorem B2652763 : Blo 1240438 2652763 := bstep (se 1 (by rfl) ⟨1989572, by rfl⟩ : syracuseStep 2652763 = 3979145) B3979145
theorem B2792249 : Blo 1240438 2792249 := bstep (se 2 (by rfl) ⟨1047093, by rfl⟩ : syracuseStep 2792249 = 2094187) B2094187
theorem B2792303 : Blo 1240438 2792303 := bstep (se 1 (by rfl) ⟨2094227, by rfl⟩ : syracuseStep 2792303 = 4188455) B4188455
theorem B33987575 : Blo 1240438 33987575 := bstep (se 1 (by rfl) ⟨25490681, by rfl⟩ : syracuseStep 33987575 = 50981363) B50981363
theorem B2096219 : Blo 1240438 2096219 := bstep (se 1 (by rfl) ⟨1572164, by rfl⟩ : syracuseStep 2096219 = 3144329) B3144329
theorem B2358497 : Blo 1240438 2358497 := bstep (se 2 (by rfl) ⟨884436, by rfl⟩ : syracuseStep 2358497 = 1768873) B1768873
theorem B9420137 : Blo 1240438 9420137 := bstep (se 2 (by rfl) ⟨3532551, by rfl⟩ : syracuseStep 9420137 = 7065103) B7065103
theorem B2792879 : Blo 1240438 2792879 := bstep (se 1 (by rfl) ⟨2094659, by rfl⟩ : syracuseStep 2792879 = 4189319) B4189319
theorem B2981303 : Blo 1240438 2981303 := bstep (se 1 (by rfl) ⟨2235977, by rfl⟩ : syracuseStep 2981303 = 4471955) B4471955
theorem B2792951 : Blo 1240438 2792951 := bstep (se 1 (by rfl) ⟨2094713, by rfl⟩ : syracuseStep 2792951 = 4189427) B4189427
theorem B17899001 : Blo 1240438 17899001 := bstep (se 2 (by rfl) ⟨6712125, by rfl⟩ : syracuseStep 17899001 = 13424251) B13424251
theorem B5168731 : Blo 1240438 5168731 := bstep (se 1 (by rfl) ⟨3876548, by rfl⟩ : syracuseStep 5168731 = 7753097) B7753097
theorem B1490719 : Blo 1240438 1490719 := bstep (se 1 (by rfl) ⟨1118039, by rfl⟩ : syracuseStep 1490719 = 2236079) B2236079
theorem B19103687 : Blo 1240438 19103687 := bstep (se 1 (by rfl) ⟨14327765, by rfl⟩ : syracuseStep 19103687 = 28655531) B28655531
theorem B2793527 : Blo 1240438 2793527 := bstep (se 1 (by rfl) ⟨2095145, by rfl⟩ : syracuseStep 2793527 = 4190291) B4190291
theorem B550879501 : Blo 1240438 550879501 := bstep (se 3 (by rfl) ⟨103289906, by rfl⟩ : syracuseStep 550879501 = 206579813) B206579813
theorem B2515321 : Blo 1240438 2515321 := bstep (se 2 (by rfl) ⟨943245, by rfl⟩ : syracuseStep 2515321 = 1886491) B1886491
theorem B4186781 : Blo 1240438 4186781 := bstep (se 3 (by rfl) ⟨785021, by rfl⟩ : syracuseStep 4186781 = 1570043) B1570043
theorem B3187775 : Blo 1240438 3187775 := bstep (se 1 (by rfl) ⟨2390831, by rfl⟩ : syracuseStep 3187775 = 4781663) B4781663
theorem B1860719 : Blo 1240438 1860719 := bstep (se 1 (by rfl) ⟨1395539, by rfl⟩ : syracuseStep 1860719 = 2791079) B2791079
theorem B4187321 : Blo 1240438 4187321 := bstep (se 2 (by rfl) ⟨1570245, by rfl⟩ : syracuseStep 4187321 = 3140491) B3140491
theorem B7070935 : Blo 1240438 7070935 := bstep (se 1 (by rfl) ⟨5303201, by rfl⟩ : syracuseStep 7070935 = 10606403) B10606403
theorem B1860839 : Blo 1240438 1860839 := bstep (se 1 (by rfl) ⟨1395629, by rfl⟩ : syracuseStep 1860839 = 2791259) B2791259
theorem B1860905 : Blo 1240438 1860905 := bstep (se 2 (by rfl) ⟨697839, by rfl⟩ : syracuseStep 1860905 = 1395679) B1395679
theorem B3106127 : Blo 1240438 3106127 := bstep (se 1 (by rfl) ⟨2329595, by rfl⟩ : syracuseStep 3106127 = 4659191) B4659191
theorem B2795039 : Blo 1240438 2795039 := bstep (se 1 (by rfl) ⟨2096279, by rfl⟩ : syracuseStep 2795039 = 4192559) B4192559
theorem B1861175 : Blo 1240438 1861175 := bstep (se 1 (by rfl) ⟨1395881, by rfl⟩ : syracuseStep 1861175 = 2791763) B2791763
theorem B1861499 : Blo 1240438 1861499 := bstep (se 1 (by rfl) ⟨1396124, by rfl⟩ : syracuseStep 1861499 = 2792249) B2792249
theorem B1861535 : Blo 1240438 1861535 := bstep (se 1 (by rfl) ⟨1396151, by rfl⟩ : syracuseStep 1861535 = 2792303) B2792303
theorem B17901485 : Blo 1240438 17901485 := bstep (se 3 (by rfl) ⟨3356528, by rfl⟩ : syracuseStep 17901485 = 6713057) B6713057
theorem B6891641 : Blo 1240438 6891641 := bstep (se 2 (by rfl) ⟨2584365, by rfl⟩ : syracuseStep 6891641 = 5168731) B5168731
theorem B1861769 : Blo 1240438 1861769 := bstep (se 2 (by rfl) ⟨698163, by rfl⟩ : syracuseStep 1861769 = 1396327) B1396327
theorem B22956281 : Blo 1240438 22956281 := bstep (se 2 (by rfl) ⟨8608605, by rfl⟩ : syracuseStep 22956281 = 17217211) B17217211
theorem B1861919 : Blo 1240438 1861919 := bstep (se 1 (by rfl) ⟨1396439, by rfl⟩ : syracuseStep 1861919 = 2792879) B2792879
theorem B1861967 : Blo 1240438 1861967 := bstep (se 1 (by rfl) ⟨1396475, by rfl⟩ : syracuseStep 1861967 = 2792951) B2792951
theorem B1862057 : Blo 1240438 1862057 := bstep (se 2 (by rfl) ⟨698271, by rfl⟩ : syracuseStep 1862057 = 1396543) B1396543
theorem B6285761 : Blo 1240438 6285761 := bstep (se 2 (by rfl) ⟨2357160, by rfl⟩ : syracuseStep 6285761 = 4714321) B4714321
theorem B4188833 : Blo 1240438 4188833 := bstep (se 2 (by rfl) ⟨1570812, by rfl⟩ : syracuseStep 4188833 = 3141625) B3141625
theorem B1862441 : Blo 1240438 1862441 := bstep (se 2 (by rfl) ⟨698415, by rfl⟩ : syracuseStep 1862441 = 1396831) B1396831
theorem B1862651 : Blo 1240438 1862651 := bstep (se 1 (by rfl) ⟨1396988, by rfl⟩ : syracuseStep 1862651 = 2793977) B2793977
theorem B3140633 : Blo 1240438 3140633 := bstep (se 2 (by rfl) ⟨1177737, by rfl⟩ : syracuseStep 3140633 = 2355475) B2355475
theorem B1862711 : Blo 1240438 1862711 := bstep (se 1 (by rfl) ⟨1397033, by rfl⟩ : syracuseStep 1862711 = 2794067) B2794067
theorem B14142599 : Blo 1240438 14142599 := bstep (se 1 (by rfl) ⟨10606949, by rfl⟩ : syracuseStep 14142599 = 21213899) B21213899
theorem B1862831 : Blo 1240438 1862831 := bstep (se 1 (by rfl) ⟨1397123, by rfl⟩ : syracuseStep 1862831 = 2794247) B2794247
theorem B3140815 : Blo 1240438 3140815 := bstep (se 1 (by rfl) ⟨2355611, by rfl⟩ : syracuseStep 3140815 = 4711223) B4711223
theorem B1862891 : Blo 1240438 1862891 := bstep (se 1 (by rfl) ⟨1397168, by rfl⟩ : syracuseStep 1862891 = 2794337) B2794337
theorem B7548299 : Blo 1240438 7548299 := bstep (se 1 (by rfl) ⟨5661224, by rfl⟩ : syracuseStep 7548299 = 11322449) B11322449
theorem B4189697 : Blo 1240438 4189697 := bstep (se 2 (by rfl) ⟨1571136, by rfl⟩ : syracuseStep 4189697 = 3142273) B3142273
theorem B6712903 : Blo 1240438 6712903 := bstep (se 1 (by rfl) ⟨5034677, by rfl⟩ : syracuseStep 6712903 = 10069355) B10069355
theorem B52375135 : Blo 1240438 52375135 := bstep (se 1 (by rfl) ⟨39281351, by rfl⟩ : syracuseStep 52375135 = 78562703) B78562703
theorem B21196403 : Blo 1240438 21196403 := bstep (se 1 (by rfl) ⟨15897302, by rfl⟩ : syracuseStep 21196403 = 31794605) B31794605
theorem B1863551 : Blo 1240438 1863551 := bstep (se 1 (by rfl) ⟨1397663, by rfl⟩ : syracuseStep 1863551 = 2795327) B2795327
theorem B5304295 : Blo 1240438 5304295 := bstep (se 1 (by rfl) ⟨3978221, by rfl⟩ : syracuseStep 5304295 = 7956443) B7956443
theorem B2387999 : Blo 1240438 2387999 := bstep (se 1 (by rfl) ⟨1790999, by rfl⟩ : syracuseStep 2387999 = 3581999) B3581999
theorem B1241119 : Blo 1240438 1241119 := bstep (se 1 (by rfl) ⟨930839, by rfl⟩ : syracuseStep 1241119 = 1861679) B1861679
theorem B1699895 : Blo 1240438 1699895 := bstep (se 1 (by rfl) ⟨1274921, by rfl⟩ : syracuseStep 1699895 = 2549843) B2549843
theorem B3977299 : Blo 1240438 3977299 := bstep (se 1 (by rfl) ⟨2982974, by rfl⟩ : syracuseStep 3977299 = 5965949) B5965949
theorem B3141787 : Blo 1240438 3141787 := bstep (se 1 (by rfl) ⟨2356340, by rfl⟩ : syracuseStep 3141787 = 4712681) B4712681
theorem B1241295 : Blo 1240438 1241295 := bstep (se 1 (by rfl) ⟨930971, by rfl⟩ : syracuseStep 1241295 = 1861943) B1861943
theorem B2871599 : Blo 1240438 2871599 := bstep (se 1 (by rfl) ⟨2153699, by rfl⟩ : syracuseStep 2871599 = 4307399) B4307399
theorem B2650439 : Blo 1240438 2650439 := bstep (se 1 (by rfl) ⟨1987829, by rfl⟩ : syracuseStep 2650439 = 3975659) B3975659
theorem B1241415 : Blo 1240438 1241415 := bstep (se 1 (by rfl) ⟨931061, by rfl⟩ : syracuseStep 1241415 = 1862123) B1862123
theorem B4190777 : Blo 1240438 4190777 := bstep (se 2 (by rfl) ⟨1571541, by rfl⟩ : syracuseStep 4190777 = 3143083) B3143083
theorem B4190939 : Blo 1240438 4190939 := bstep (se 1 (by rfl) ⟨3143204, by rfl⟩ : syracuseStep 4190939 = 6286409) B6286409
theorem B1397479 : Blo 1240438 1397479 := bstep (se 1 (by rfl) ⟨1048109, by rfl⟩ : syracuseStep 1397479 = 2096219) B2096219
theorem B1241883 : Blo 1240438 1241883 := bstep (se 1 (by rfl) ⟨931412, by rfl⟩ : syracuseStep 1241883 = 1862825) B1862825
theorem B5305115 : Blo 1240438 5305115 := bstep (se 1 (by rfl) ⟨3978836, by rfl⟩ : syracuseStep 5305115 = 7957673) B7957673
theorem B6288191 : Blo 1240438 6288191 := bstep (se 1 (by rfl) ⟨4716143, by rfl⟩ : syracuseStep 6288191 = 9432287) B9432287
theorem B6280091 : Blo 1240438 6280091 := bstep (se 1 (by rfl) ⟨4710068, by rfl⟩ : syracuseStep 6280091 = 9420137) B9420137
theorem B1987535 : Blo 1240438 1987535 := bstep (se 1 (by rfl) ⟨1490651, by rfl⟩ : syracuseStep 1987535 = 2981303) B2981303
theorem B11932667 : Blo 1240438 11932667 := bstep (se 1 (by rfl) ⟨8949500, by rfl⟩ : syracuseStep 11932667 = 17899001) B17899001
theorem B1987625 : Blo 1240438 1987625 := bstep (se 2 (by rfl) ⟨745359, by rfl⟩ : syracuseStep 1987625 = 1490719) B1490719
theorem B4715567 : Blo 1240438 4715567 := bstep (se 1 (by rfl) ⟨3536675, by rfl⟩ : syracuseStep 4715567 = 7073351) B7073351
theorem B1242159 : Blo 1240438 1242159 := bstep (se 1 (by rfl) ⟨931619, by rfl⟩ : syracuseStep 1242159 = 1863239) B1863239
theorem B1242279 : Blo 1240438 1242279 := bstep (se 1 (by rfl) ⟨931709, by rfl⟩ : syracuseStep 1242279 = 1863419) B1863419
theorem B3142921 : Blo 1240438 3142921 := bstep (se 2 (by rfl) ⟨1178595, by rfl⟩ : syracuseStep 3142921 = 2357191) B2357191
theorem B12735791 : Blo 1240438 12735791 := bstep (se 1 (by rfl) ⟨9551843, by rfl⟩ : syracuseStep 12735791 = 19103687) B19103687
theorem B1676713 : Blo 1240438 1676713 := bstep (se 2 (by rfl) ⟨628767, by rfl⟩ : syracuseStep 1676713 = 1257535) B1257535
theorem B9426455 : Blo 1240438 9426455 := bstep (se 1 (by rfl) ⟨7069841, by rfl⟩ : syracuseStep 9426455 = 14139683) B14139683
theorem B76502593 : Blo 1240438 76502593 := bstep (se 2 (by rfl) ⟨28688472, by rfl⟩ : syracuseStep 76502593 = 57376945) B57376945
theorem B25499225 : Blo 1240438 25499225 := bstep (se 2 (by rfl) ⟨9562209, by rfl⟩ : syracuseStep 25499225 = 19124419) B19124419
theorem B22640219 : Blo 1240438 22640219 := bstep (se 1 (by rfl) ⟨16980164, by rfl⟩ : syracuseStep 22640219 = 33960329) B33960329
theorem B4191911 : Blo 1240438 4191911 := bstep (se 1 (by rfl) ⟨3143933, by rfl⟩ : syracuseStep 4191911 = 6287867) B6287867
theorem B4716265 : Blo 1240438 4716265 := bstep (se 2 (by rfl) ⟨1768599, by rfl⟩ : syracuseStep 4716265 = 3537199) B3537199
theorem B6289325 : Blo 1240438 6289325 := bstep (se 3 (by rfl) ⟨1179248, by rfl⟩ : syracuseStep 6289325 = 2358497) B2358497
theorem B4716539 : Blo 1240438 4716539 := bstep (se 1 (by rfl) ⟨3537404, by rfl⟩ : syracuseStep 4716539 = 7074809) B7074809
theorem B7075835 : Blo 1240438 7075835 := bstep (se 1 (by rfl) ⟨5306876, by rfl⟩ : syracuseStep 7075835 = 10613753) B10613753
theorem B1570843 : Blo 1240438 1570843 := bstep (se 1 (by rfl) ⟨1178132, by rfl⟩ : syracuseStep 1570843 = 2356265) B2356265
theorem B2095159 : Blo 1240438 2095159 := bstep (se 1 (by rfl) ⟨1571369, by rfl⟩ : syracuseStep 2095159 = 3142739) B3142739
theorem B26843237 : Blo 1240438 26843237 := bstep (se 4 (by rfl) ⟨2516553, by rfl⟩ : syracuseStep 26843237 = 5033107) B5033107
theorem B3537017 : Blo 1240438 3537017 := bstep (se 2 (by rfl) ⟨1326381, by rfl⟩ : syracuseStep 3537017 = 2652763) B2652763
theorem B15906941 : Blo 1240438 15906941 := bstep (se 3 (by rfl) ⟨2982551, by rfl⟩ : syracuseStep 15906941 = 5965103) B5965103
theorem B6281387 : Blo 1240438 6281387 := bstep (se 1 (by rfl) ⟨4711040, by rfl⟩ : syracuseStep 6281387 = 9422081) B9422081
theorem B4192775 : Blo 1240438 4192775 := bstep (se 1 (by rfl) ⟨3144581, by rfl⟩ : syracuseStep 4192775 = 6289163) B6289163
theorem B3144379 : Blo 1240438 3144379 := bstep (se 1 (by rfl) ⟨2358284, by rfl⟩ : syracuseStep 3144379 = 4716569) B4716569
theorem B3144683 : Blo 1240438 3144683 := bstep (se 1 (by rfl) ⟨2358512, by rfl⟩ : syracuseStep 3144683 = 4717025) B4717025
theorem B1678367 : Blo 1240438 1678367 := bstep (se 1 (by rfl) ⟨1258775, by rfl⟩ : syracuseStep 1678367 = 2517551) B2517551
theorem B5299307 : Blo 1240438 5299307 := bstep (se 1 (by rfl) ⟨3974480, by rfl⟩ : syracuseStep 5299307 = 7948961) B7948961
theorem B10599569 : Blo 1240438 10599569 := bstep (se 2 (by rfl) ⟨3974838, by rfl⟩ : syracuseStep 10599569 = 7949677) B7949677
theorem B9682249 : Blo 1240438 9682249 := bstep (se 2 (by rfl) ⟨3630843, by rfl⟩ : syracuseStep 9682249 = 7261687) B7261687
theorem B22658383 : Blo 1240438 22658383 := bstep (se 1 (by rfl) ⟨16993787, by rfl⟩ : syracuseStep 22658383 = 33987575) B33987575
theorem B11935127 : Blo 1240438 11935127 := bstep (se 1 (by rfl) ⟨8951345, by rfl⟩ : syracuseStep 11935127 = 17902691) B17902691
theorem B7953983 : Blo 1240438 7953983 := bstep (se 1 (by rfl) ⟨5965487, by rfl⟩ : syracuseStep 7953983 = 11930975) B11930975
theorem B2793545 : Blo 1240438 2793545 := bstep (se 2 (by rfl) ⟨1047579, by rfl⟩ : syracuseStep 2793545 = 2095159) B2095159
theorem B2793851 : Blo 1240438 2793851 := bstep (se 1 (by rfl) ⟨2095388, by rfl⟩ : syracuseStep 2793851 = 4190777) B4190777
theorem B2793959 : Blo 1240438 2793959 := bstep (se 1 (by rfl) ⟨2095469, by rfl⟩ : syracuseStep 2793959 = 4190939) B4190939
theorem B4186727 : Blo 1240438 4186727 := bstep (se 1 (by rfl) ⟨3140045, by rfl⟩ : syracuseStep 4186727 = 6280091) B6280091
theorem B7955111 : Blo 1240438 7955111 := bstep (se 1 (by rfl) ⟨5966333, by rfl⟩ : syracuseStep 7955111 = 11932667) B11932667
theorem B8283005 : Blo 1240438 8283005 := bstep (se 3 (by rfl) ⟨1553063, by rfl⟩ : syracuseStep 8283005 = 3106127) B3106127
theorem B6284303 : Blo 1240438 6284303 := bstep (se 1 (by rfl) ⟨4713227, by rfl⟩ : syracuseStep 6284303 = 9426455) B9426455
theorem B16999483 : Blo 1240438 16999483 := bstep (se 1 (by rfl) ⟨12749612, by rfl⟩ : syracuseStep 16999483 = 25499225) B25499225
theorem B2794607 : Blo 1240438 2794607 := bstep (se 1 (by rfl) ⟨2095955, by rfl⟩ : syracuseStep 2794607 = 4191911) B4191911
theorem B4187591 : Blo 1240438 4187591 := bstep (se 1 (by rfl) ⟨3140693, by rfl⟩ : syracuseStep 4187591 = 6281387) B6281387
theorem B15304187 : Blo 1240438 15304187 := bstep (se 1 (by rfl) ⟨11478140, by rfl⟩ : syracuseStep 15304187 = 22956281) B22956281
theorem B4187753 : Blo 1240438 4187753 := bstep (se 2 (by rfl) ⟨1570407, by rfl⟩ : syracuseStep 4187753 = 3140815) B3140815
theorem B2795183 : Blo 1240438 2795183 := bstep (se 1 (by rfl) ⟨2096387, by rfl⟩ : syracuseStep 2795183 = 4192775) B4192775
theorem B3532871 : Blo 1240438 3532871 := bstep (se 1 (by rfl) ⟨2649653, by rfl⟩ : syracuseStep 3532871 = 5299307) B5299307
theorem B5032199 : Blo 1240438 5032199 := bstep (se 1 (by rfl) ⟨3774149, by rfl⟩ : syracuseStep 5032199 = 7548299) B7548299
theorem B7956751 : Blo 1240438 7956751 := bstep (se 1 (by rfl) ⟨5967563, by rfl⟩ : syracuseStep 7956751 = 11935127) B11935127
theorem B5302655 : Blo 1240438 5302655 := bstep (se 1 (by rfl) ⟨3976991, by rfl⟩ : syracuseStep 5302655 = 7953983) B7953983
theorem B7072393 : Blo 1240438 7072393 := bstep (se 2 (by rfl) ⟨2652147, by rfl⟩ : syracuseStep 7072393 = 5304295) B5304295
theorem B1862351 : Blo 1240438 1862351 := bstep (se 1 (by rfl) ⟨1396763, by rfl⟩ : syracuseStep 1862351 = 2793527) B2793527
theorem B6367997 : Blo 1240438 6367997 := bstep (se 3 (by rfl) ⟨1193999, by rfl⟩ : syracuseStep 6367997 = 2387999) B2387999
theorem B4475645 : Blo 1240438 4475645 := bstep (se 3 (by rfl) ⟨839183, by rfl⟩ : syracuseStep 4475645 = 1678367) B1678367
theorem B5303065 : Blo 1240438 5303065 := bstep (se 2 (by rfl) ⟨1988649, by rfl⟩ : syracuseStep 5303065 = 3977299) B3977299
theorem B4533053 : Blo 1240438 4533053 := bstep (se 3 (by rfl) ⟨849947, by rfl⟩ : syracuseStep 4533053 = 1699895) B1699895
theorem B4189049 : Blo 1240438 4189049 := bstep (se 2 (by rfl) ⟨1570893, by rfl⟩ : syracuseStep 4189049 = 3141787) B3141787
theorem B734506001 : Blo 1240438 734506001 := bstep (se 2 (by rfl) ⟨275439750, by rfl⟩ : syracuseStep 734506001 = 550879501) B550879501
theorem B3353761 : Blo 1240438 3353761 := bstep (se 2 (by rfl) ⟨1257660, by rfl⟩ : syracuseStep 3353761 = 2515321) B2515321
theorem B1240479 : Blo 1240438 1240479 := bstep (se 1 (by rfl) ⟨930359, by rfl⟩ : syracuseStep 1240479 = 1860719) B1860719
theorem B1240559 : Blo 1240438 1240559 := bstep (se 1 (by rfl) ⟨930419, by rfl⟩ : syracuseStep 1240559 = 1860839) B1860839
theorem B1240603 : Blo 1240438 1240603 := bstep (se 1 (by rfl) ⟨930452, by rfl⟩ : syracuseStep 1240603 = 1860905) B1860905
theorem B8490527 : Blo 1240438 8490527 := bstep (se 1 (by rfl) ⟨6367895, by rfl⟩ : syracuseStep 8490527 = 12735791) B12735791
theorem B1863305 : Blo 1240438 1863305 := bstep (se 2 (by rfl) ⟨698739, by rfl⟩ : syracuseStep 1863305 = 1397479) B1397479
theorem B1863359 : Blo 1240438 1863359 := bstep (se 1 (by rfl) ⟨1397519, by rfl⟩ : syracuseStep 1863359 = 2795039) B2795039
theorem B1240783 : Blo 1240438 1240783 := bstep (se 1 (by rfl) ⟨930587, by rfl⟩ : syracuseStep 1240783 = 1861175) B1861175
theorem B15093479 : Blo 1240438 15093479 := bstep (se 1 (by rfl) ⟨11320109, by rfl⟩ : syracuseStep 15093479 = 22640219) B22640219
theorem B1240999 : Blo 1240438 1240999 := bstep (se 1 (by rfl) ⟨930749, by rfl⟩ : syracuseStep 1240999 = 1861499) B1861499
theorem B1241023 : Blo 1240438 1241023 := bstep (se 1 (by rfl) ⟨930767, by rfl⟩ : syracuseStep 1241023 = 1861535) B1861535
theorem B17895491 : Blo 1240438 17895491 := bstep (se 1 (by rfl) ⟨13421618, by rfl⟩ : syracuseStep 17895491 = 26843237) B26843237
theorem B10604627 : Blo 1240438 10604627 := bstep (se 1 (by rfl) ⟨7953470, by rfl⟩ : syracuseStep 10604627 = 15906941) B15906941
theorem B1241179 : Blo 1240438 1241179 := bstep (se 1 (by rfl) ⟨930884, by rfl⟩ : syracuseStep 1241179 = 1861769) B1861769
theorem B1241279 : Blo 1240438 1241279 := bstep (se 1 (by rfl) ⟨930959, by rfl⟩ : syracuseStep 1241279 = 1861919) B1861919
theorem B1241311 : Blo 1240438 1241311 := bstep (se 1 (by rfl) ⟨930983, by rfl⟩ : syracuseStep 1241311 = 1861967) B1861967
theorem B1241371 : Blo 1240438 1241371 := bstep (se 1 (by rfl) ⟨931028, by rfl⟩ : syracuseStep 1241371 = 1862057) B1862057
theorem B4190507 : Blo 1240438 4190507 := bstep (se 1 (by rfl) ⟨3142880, by rfl⟩ : syracuseStep 4190507 = 6285761) B6285761
theorem B4190561 : Blo 1240438 4190561 := bstep (se 2 (by rfl) ⟨1571460, by rfl⟩ : syracuseStep 4190561 = 3142921) B3142921
theorem B1241627 : Blo 1240438 1241627 := bstep (se 1 (by rfl) ⟨931220, by rfl⟩ : syracuseStep 1241627 = 1862441) B1862441
theorem B1241767 : Blo 1240438 1241767 := bstep (se 1 (by rfl) ⟨931325, by rfl⟩ : syracuseStep 1241767 = 1862651) B1862651
theorem B2093755 : Blo 1240438 2093755 := bstep (se 1 (by rfl) ⟨1570316, by rfl⟩ : syracuseStep 2093755 = 3140633) B3140633
theorem B1241807 : Blo 1240438 1241807 := bstep (se 1 (by rfl) ⟨931355, by rfl⟩ : syracuseStep 1241807 = 1862711) B1862711
theorem B102003457 : Blo 1240438 102003457 := bstep (se 2 (by rfl) ⟨38251296, by rfl⟩ : syracuseStep 102003457 = 76502593) B76502593
theorem B8950537 : Blo 1240438 8950537 := bstep (se 2 (by rfl) ⟨3356451, by rfl⟩ : syracuseStep 8950537 = 6712903) B6712903
theorem B7066379 : Blo 1240438 7066379 := bstep (se 1 (by rfl) ⟨5299784, by rfl⟩ : syracuseStep 7066379 = 10599569) B10599569
theorem B1241887 : Blo 1240438 1241887 := bstep (se 1 (by rfl) ⟨931415, by rfl⟩ : syracuseStep 1241887 = 1862831) B1862831
theorem B69833513 : Blo 1240438 69833513 := bstep (se 2 (by rfl) ⟨26187567, by rfl⟩ : syracuseStep 69833513 = 52375135) B52375135
theorem B1241927 : Blo 1240438 1241927 := bstep (se 1 (by rfl) ⟨931445, by rfl⟩ : syracuseStep 1241927 = 1862891) B1862891
theorem B6288353 : Blo 1240438 6288353 := bstep (se 2 (by rfl) ⟨2358132, by rfl⟩ : syracuseStep 6288353 = 4716265) B4716265
theorem B1242367 : Blo 1240438 1242367 := bstep (se 1 (by rfl) ⟨931775, by rfl⟩ : syracuseStep 1242367 = 1863551) B1863551
theorem B2094457 : Blo 1240438 2094457 := bstep (se 2 (by rfl) ⟨785421, by rfl⟩ : syracuseStep 2094457 = 1570843) B1570843
theorem B8500733 : Blo 1240438 8500733 := bstep (se 3 (by rfl) ⟨1593887, by rfl⟩ : syracuseStep 8500733 = 3187775) B3187775
theorem B2791187 : Blo 1240438 2791187 := bstep (se 1 (by rfl) ⟨2093390, by rfl⟩ : syracuseStep 2791187 = 4186781) B4186781
theorem B4192127 : Blo 1240438 4192127 := bstep (se 1 (by rfl) ⟨3144095, by rfl⟩ : syracuseStep 4192127 = 6288191) B6288191
theorem B1325083 : Blo 1240438 1325083 := bstep (se 1 (by rfl) ⟨993812, by rfl⟩ : syracuseStep 1325083 = 1987625) B1987625
theorem B3143711 : Blo 1240438 3143711 := bstep (se 1 (by rfl) ⟨2357783, by rfl⟩ : syracuseStep 3143711 = 4715567) B4715567
theorem B2791547 : Blo 1240438 2791547 := bstep (se 1 (by rfl) ⟨2093660, by rfl⟩ : syracuseStep 2791547 = 4187321) B4187321
theorem B7657597 : Blo 1240438 7657597 := bstep (se 3 (by rfl) ⟨1435799, by rfl⟩ : syracuseStep 7657597 = 2871599) B2871599
theorem B7067837 : Blo 1240438 7067837 := bstep (se 3 (by rfl) ⟨1325219, by rfl⟩ : syracuseStep 7067837 = 2650439) B2650439
theorem B4192505 : Blo 1240438 4192505 := bstep (se 2 (by rfl) ⟨1572189, by rfl⟩ : syracuseStep 4192505 = 3144379) B3144379
theorem B11934323 : Blo 1240438 11934323 := bstep (se 1 (by rfl) ⟨8950742, by rfl⟩ : syracuseStep 11934323 = 17901485) B17901485
theorem B4192883 : Blo 1240438 4192883 := bstep (se 1 (by rfl) ⟨3144662, by rfl⟩ : syracuseStep 4192883 = 6289325) B6289325
theorem B3144359 : Blo 1240438 3144359 := bstep (se 1 (by rfl) ⟨2358269, by rfl⟩ : syracuseStep 3144359 = 4716539) B4716539
theorem B4717223 : Blo 1240438 4717223 := bstep (se 1 (by rfl) ⟨3537917, by rfl⟩ : syracuseStep 4717223 = 7075835) B7075835
theorem B4594427 : Blo 1240438 4594427 := bstep (se 1 (by rfl) ⟨3445820, by rfl⟩ : syracuseStep 4594427 = 6891641) B6891641
theorem B2358011 : Blo 1240438 2358011 := bstep (se 1 (by rfl) ⟨1768508, by rfl⟩ : syracuseStep 2358011 = 3537017) B3537017
theorem B9427913 : Blo 1240438 9427913 := bstep (se 2 (by rfl) ⟨3535467, by rfl⟩ : syracuseStep 9427913 = 7070935) B7070935
theorem B12909665 : Blo 1240438 12909665 := bstep (se 2 (by rfl) ⟨4841124, by rfl⟩ : syracuseStep 12909665 = 9682249) B9682249
theorem B30211177 : Blo 1240438 30211177 := bstep (se 2 (by rfl) ⟨11329191, by rfl⟩ : syracuseStep 30211177 = 22658383) B22658383
theorem B2792555 : Blo 1240438 2792555 := bstep (se 1 (by rfl) ⟨2094416, by rfl⟩ : syracuseStep 2792555 = 4188833) B4188833
theorem B2235617 : Blo 1240438 2235617 := bstep (se 2 (by rfl) ⟨838356, by rfl⟩ : syracuseStep 2235617 = 1676713) B1676713
theorem B2096455 : Blo 1240438 2096455 := bstep (se 1 (by rfl) ⟨1572341, by rfl⟩ : syracuseStep 2096455 = 3144683) B3144683
theorem B14146973 : Blo 1240438 14146973 := bstep (se 3 (by rfl) ⟨2652557, by rfl⟩ : syracuseStep 14146973 = 5305115) B5305115
theorem B9428399 : Blo 1240438 9428399 := bstep (se 1 (by rfl) ⟨7071299, by rfl⟩ : syracuseStep 9428399 = 14142599) B14142599
theorem B2793131 : Blo 1240438 2793131 := bstep (se 1 (by rfl) ⟨2094848, by rfl⟩ : syracuseStep 2793131 = 4189697) B4189697
theorem B14130935 : Blo 1240438 14130935 := bstep (se 1 (by rfl) ⟨10598201, by rfl⟩ : syracuseStep 14130935 = 21196403) B21196403
theorem B5300093 : Blo 1240438 5300093 := bstep (se 3 (by rfl) ⟨993767, by rfl⟩ : syracuseStep 5300093 = 1987535) B1987535
theorem B7069751 : Blo 1240438 7069751 := bstep (se 1 (by rfl) ⟨5302313, by rfl⟩ : syracuseStep 7069751 = 10604627) B10604627
theorem B2793671 : Blo 1240438 2793671 := bstep (se 1 (by rfl) ⟨2095253, by rfl⟩ : syracuseStep 2793671 = 4190507) B4190507
theorem B2793707 : Blo 1240438 2793707 := bstep (se 1 (by rfl) ⟨2095280, by rfl⟩ : syracuseStep 2793707 = 4190561) B4190561
theorem B10609001 : Blo 1240438 10609001 := bstep (se 2 (by rfl) ⟨3978375, by rfl⟩ : syracuseStep 10609001 = 7956751) B7956751
theorem B4710919 : Blo 1240438 4710919 := bstep (se 1 (by rfl) ⟨3533189, by rfl⟩ : syracuseStep 4710919 = 7066379) B7066379
theorem B5522003 : Blo 1240438 5522003 := bstep (se 1 (by rfl) ⟨4141502, by rfl⟩ : syracuseStep 5522003 = 8283005) B8283005
theorem B9429857 : Blo 1240438 9429857 := bstep (se 2 (by rfl) ⟨3536196, by rfl⟩ : syracuseStep 9429857 = 7072393) B7072393
theorem B136004609 : Blo 1240438 136004609 := bstep (se 2 (by rfl) ⟨51001728, by rfl⟩ : syracuseStep 136004609 = 102003457) B102003457
theorem B7070753 : Blo 1240438 7070753 := bstep (se 2 (by rfl) ⟨2651532, by rfl⟩ : syracuseStep 7070753 = 5303065) B5303065
theorem B1860791 : Blo 1240438 1860791 := bstep (se 1 (by rfl) ⟨1395593, by rfl⟩ : syracuseStep 1860791 = 2791187) B2791187
theorem B2794751 : Blo 1240438 2794751 := bstep (se 1 (by rfl) ⟨2096063, by rfl⟩ : syracuseStep 2794751 = 4192127) B4192127
theorem B1861031 : Blo 1240438 1861031 := bstep (se 1 (by rfl) ⟨1395773, by rfl⟩ : syracuseStep 1861031 = 2791547) B2791547
theorem B4711891 : Blo 1240438 4711891 := bstep (se 1 (by rfl) ⟨3533918, by rfl⟩ : syracuseStep 4711891 = 7067837) B7067837
theorem B40281569 : Blo 1240438 40281569 := bstep (se 2 (by rfl) ⟨15105588, by rfl⟩ : syracuseStep 40281569 = 30211177) B30211177
theorem B2795003 : Blo 1240438 2795003 := bstep (se 1 (by rfl) ⟨2096252, by rfl⟩ : syracuseStep 2795003 = 4192505) B4192505
theorem B7956215 : Blo 1240438 7956215 := bstep (se 1 (by rfl) ⟨5967161, by rfl⟩ : syracuseStep 7956215 = 11934323) B11934323
theorem B2795255 : Blo 1240438 2795255 := bstep (se 1 (by rfl) ⟨2096441, by rfl⟩ : syracuseStep 2795255 = 4192883) B4192883
theorem B2795273 : Blo 1240438 2795273 := bstep (se 2 (by rfl) ⟨1048227, by rfl⟩ : syracuseStep 2795273 = 2096455) B2096455
theorem B2983763 : Blo 1240438 2983763 := bstep (se 1 (by rfl) ⟨2237822, by rfl⟩ : syracuseStep 2983763 = 4475645) B4475645
theorem B6285275 : Blo 1240438 6285275 := bstep (se 1 (by rfl) ⟨4713956, by rfl⟩ : syracuseStep 6285275 = 9427913) B9427913
theorem B489670667 : Blo 1240438 489670667 := bstep (se 1 (by rfl) ⟨367253000, by rfl⟩ : syracuseStep 489670667 = 734506001) B734506001
theorem B1861703 : Blo 1240438 1861703 := bstep (se 1 (by rfl) ⟨1396277, by rfl⟩ : syracuseStep 1861703 = 2792555) B2792555
theorem B186222701 : Blo 1240438 186222701 := bstep (se 3 (by rfl) ⟨34916756, by rfl⟩ : syracuseStep 186222701 = 69833513) B69833513
theorem B9431315 : Blo 1240438 9431315 := bstep (se 1 (by rfl) ⟨7073486, by rfl⟩ : syracuseStep 9431315 = 14146973) B14146973
theorem B6285599 : Blo 1240438 6285599 := bstep (se 1 (by rfl) ⟨4714199, by rfl⟩ : syracuseStep 6285599 = 9428399) B9428399
theorem B1862087 : Blo 1240438 1862087 := bstep (se 1 (by rfl) ⟨1396565, by rfl⟩ : syracuseStep 1862087 = 2793131) B2793131
theorem B10062319 : Blo 1240438 10062319 := bstep (se 1 (by rfl) ⟨7546739, by rfl⟩ : syracuseStep 10062319 = 15093479) B15093479
theorem B3533395 : Blo 1240438 3533395 := bstep (se 1 (by rfl) ⟨2650046, by rfl⟩ : syracuseStep 3533395 = 5300093) B5300093
theorem B11930327 : Blo 1240438 11930327 := bstep (se 1 (by rfl) ⟨8947745, by rfl⟩ : syracuseStep 11930327 = 17895491) B17895491
theorem B1862363 : Blo 1240438 1862363 := bstep (se 1 (by rfl) ⟨1396772, by rfl⟩ : syracuseStep 1862363 = 2793545) B2793545
theorem B1862567 : Blo 1240438 1862567 := bstep (se 1 (by rfl) ⟨1396925, by rfl⟩ : syracuseStep 1862567 = 2793851) B2793851
theorem B34425773 : Blo 1240438 34425773 := bstep (se 3 (by rfl) ⟨6454832, by rfl⟩ : syracuseStep 34425773 = 12909665) B12909665
theorem B1862639 : Blo 1240438 1862639 := bstep (se 1 (by rfl) ⟨1396979, by rfl⟩ : syracuseStep 1862639 = 2793959) B2793959
theorem B5303407 : Blo 1240438 5303407 := bstep (se 1 (by rfl) ⟨3977555, by rfl⟩ : syracuseStep 5303407 = 7955111) B7955111
theorem B48352565 : Blo 1240438 48352565 := bstep (se 5 (by rfl) ⟨2266526, by rfl⟩ : syracuseStep 48352565 = 4533053) B4533053
theorem B40840517 : Blo 1240438 40840517 := bstep (se 4 (by rfl) ⟨3828798, by rfl⟩ : syracuseStep 40840517 = 7657597) B7657597
theorem B4189535 : Blo 1240438 4189535 := bstep (se 1 (by rfl) ⟨3142151, by rfl⟩ : syracuseStep 4189535 = 6284303) B6284303
theorem B1863071 : Blo 1240438 1863071 := bstep (se 1 (by rfl) ⟨1397303, by rfl⟩ : syracuseStep 1863071 = 2794607) B2794607
theorem B10202791 : Blo 1240438 10202791 := bstep (se 1 (by rfl) ⟨7652093, by rfl⟩ : syracuseStep 10202791 = 15304187) B15304187
theorem B1863455 : Blo 1240438 1863455 := bstep (se 1 (by rfl) ⟨1397591, by rfl⟩ : syracuseStep 1863455 = 2795183) B2795183
theorem B2355247 : Blo 1240438 2355247 := bstep (se 1 (by rfl) ⟨1766435, by rfl⟩ : syracuseStep 2355247 = 3532871) B3532871
theorem B3354799 : Blo 1240438 3354799 := bstep (se 1 (by rfl) ⟨2516099, by rfl⟩ : syracuseStep 3354799 = 5032199) B5032199
theorem B3535103 : Blo 1240438 3535103 := bstep (se 1 (by rfl) ⟨2651327, by rfl⟩ : syracuseStep 3535103 = 5302655) B5302655
theorem B1241567 : Blo 1240438 1241567 := bstep (se 1 (by rfl) ⟨931175, by rfl⟩ : syracuseStep 1241567 = 1862351) B1862351
theorem B6288029 : Blo 1240438 6288029 := bstep (se 3 (by rfl) ⟨1179005, by rfl⟩ : syracuseStep 6288029 = 2358011) B2358011
theorem B1242203 : Blo 1240438 1242203 := bstep (se 1 (by rfl) ⟨931652, by rfl⟩ : syracuseStep 1242203 = 1863305) B1863305
theorem B1242239 : Blo 1240438 1242239 := bstep (se 1 (by rfl) ⟨931679, by rfl⟩ : syracuseStep 1242239 = 1863359) B1863359
theorem B1766777 : Blo 1240438 1766777 := bstep (se 2 (by rfl) ⟨662541, by rfl⟩ : syracuseStep 1766777 = 1325083) B1325083
theorem B2791151 : Blo 1240438 2791151 := bstep (se 1 (by rfl) ⟨2093363, by rfl⟩ : syracuseStep 2791151 = 4186727) B4186727
theorem B4192235 : Blo 1240438 4192235 := bstep (se 1 (by rfl) ⟨3144176, by rfl⟩ : syracuseStep 4192235 = 6288353) B6288353
theorem B2791673 : Blo 1240438 2791673 := bstep (se 2 (by rfl) ⟨1046877, by rfl⟩ : syracuseStep 2791673 = 2093755) B2093755
theorem B2791727 : Blo 1240438 2791727 := bstep (se 1 (by rfl) ⟨2093795, by rfl⟩ : syracuseStep 2791727 = 4187591) B4187591
theorem B5667155 : Blo 1240438 5667155 := bstep (se 1 (by rfl) ⟨4250366, by rfl⟩ : syracuseStep 5667155 = 8500733) B8500733
theorem B11934049 : Blo 1240438 11934049 := bstep (se 2 (by rfl) ⟨4475268, by rfl⟩ : syracuseStep 11934049 = 8950537) B8950537
theorem B2791835 : Blo 1240438 2791835 := bstep (se 1 (by rfl) ⟨2093876, by rfl⟩ : syracuseStep 2791835 = 4187753) B4187753
theorem B2095807 : Blo 1240438 2095807 := bstep (se 1 (by rfl) ⟨1571855, by rfl⟩ : syracuseStep 2095807 = 3143711) B3143711
theorem B22665977 : Blo 1240438 22665977 := bstep (se 2 (by rfl) ⟨8499741, by rfl⟩ : syracuseStep 22665977 = 16999483) B16999483
theorem B4471681 : Blo 1240438 4471681 := bstep (se 2 (by rfl) ⟨1676880, by rfl⟩ : syracuseStep 4471681 = 3353761) B3353761
theorem B2096239 : Blo 1240438 2096239 := bstep (se 1 (by rfl) ⟨1572179, by rfl⟩ : syracuseStep 2096239 = 3144359) B3144359
theorem B3144815 : Blo 1240438 3144815 := bstep (se 1 (by rfl) ⟨2358611, by rfl⟩ : syracuseStep 3144815 = 4717223) B4717223
theorem B2792609 : Blo 1240438 2792609 := bstep (se 2 (by rfl) ⟨1047228, by rfl⟩ : syracuseStep 2792609 = 2094457) B2094457
theorem B3062951 : Blo 1240438 3062951 := bstep (se 1 (by rfl) ⟨2297213, by rfl⟩ : syracuseStep 3062951 = 4594427) B4594427
theorem B2792699 : Blo 1240438 2792699 := bstep (se 1 (by rfl) ⟨2094524, by rfl⟩ : syracuseStep 2792699 = 4189049) B4189049
theorem B16981325 : Blo 1240438 16981325 := bstep (se 3 (by rfl) ⟨3183998, by rfl⟩ : syracuseStep 16981325 = 6367997) B6367997
theorem B1490411 : Blo 1240438 1490411 := bstep (se 1 (by rfl) ⟨1117808, by rfl⟩ : syracuseStep 1490411 = 2235617) B2235617
theorem B5660351 : Blo 1240438 5660351 := bstep (se 1 (by rfl) ⟨4245263, by rfl⟩ : syracuseStep 5660351 = 8490527) B8490527
theorem B9420623 : Blo 1240438 9420623 := bstep (se 1 (by rfl) ⟨7065467, by rfl⟩ : syracuseStep 9420623 = 14130935) B14130935
theorem B4473065 : Blo 1240438 4473065 := bstep (se 2 (by rfl) ⟨1677399, by rfl⟩ : syracuseStep 4473065 = 3354799) B3354799
theorem B90669739 : Blo 1240438 90669739 := bstep (se 1 (by rfl) ⟨68002304, by rfl⟩ : syracuseStep 90669739 = 136004609) B136004609
theorem B4711193 : Blo 1240438 4711193 := bstep (se 2 (by rfl) ⟨1766697, by rfl⟩ : syracuseStep 4711193 = 3533395) B3533395
theorem B2794409 : Blo 1240438 2794409 := bstep (se 2 (by rfl) ⟨1047903, by rfl⟩ : syracuseStep 2794409 = 2095807) B2095807
theorem B26854379 : Blo 1240438 26854379 := bstep (se 1 (by rfl) ⟨20140784, by rfl⟩ : syracuseStep 26854379 = 40281569) B40281569
theorem B4711405 : Blo 1240438 4711405 := bstep (se 3 (by rfl) ⟨883388, by rfl⟩ : syracuseStep 4711405 = 1766777) B1766777
theorem B1860767 : Blo 1240438 1860767 := bstep (se 1 (by rfl) ⟨1395575, by rfl⟩ : syracuseStep 1860767 = 2791151) B2791151
theorem B3974429 : Blo 1240438 3974429 := bstep (se 3 (by rfl) ⟨745205, by rfl⟩ : syracuseStep 3974429 = 1490411) B1490411
theorem B2794823 : Blo 1240438 2794823 := bstep (se 1 (by rfl) ⟨2096117, by rfl⟩ : syracuseStep 2794823 = 4192235) B4192235
theorem B7071209 : Blo 1240438 7071209 := bstep (se 2 (by rfl) ⟨2651703, by rfl⟩ : syracuseStep 7071209 = 5303407) B5303407
theorem B2794985 : Blo 1240438 2794985 := bstep (se 2 (by rfl) ⟨1048119, by rfl⟩ : syracuseStep 2794985 = 2096239) B2096239
theorem B1861115 : Blo 1240438 1861115 := bstep (se 1 (by rfl) ⟨1395836, by rfl⟩ : syracuseStep 1861115 = 2791673) B2791673
theorem B1861151 : Blo 1240438 1861151 := bstep (se 1 (by rfl) ⟨1395863, by rfl⟩ : syracuseStep 1861151 = 2791727) B2791727
theorem B3778103 : Blo 1240438 3778103 := bstep (se 1 (by rfl) ⟨2833577, by rfl⟩ : syracuseStep 3778103 = 5667155) B5667155
theorem B1861223 : Blo 1240438 1861223 := bstep (se 1 (by rfl) ⟨1395917, by rfl⟩ : syracuseStep 1861223 = 2791835) B2791835
theorem B1861739 : Blo 1240438 1861739 := bstep (se 1 (by rfl) ⟨1396304, by rfl⟩ : syracuseStep 1861739 = 2792609) B2792609
theorem B2041967 : Blo 1240438 2041967 := bstep (se 1 (by rfl) ⟨1531475, by rfl⟩ : syracuseStep 2041967 = 3062951) B3062951
theorem B1861799 : Blo 1240438 1861799 := bstep (se 1 (by rfl) ⟨1396349, by rfl⟩ : syracuseStep 1861799 = 2792699) B2792699
theorem B7956701 : Blo 1240438 7956701 := bstep (se 3 (by rfl) ⟨1491881, by rfl⟩ : syracuseStep 7956701 = 2983763) B2983763
theorem B4713167 : Blo 1240438 4713167 := bstep (se 1 (by rfl) ⟨3534875, by rfl⟩ : syracuseStep 4713167 = 7069751) B7069751
theorem B3140329 : Blo 1240438 3140329 := bstep (se 2 (by rfl) ⟨1177623, by rfl⟩ : syracuseStep 3140329 = 2355247) B2355247
theorem B1862447 : Blo 1240438 1862447 := bstep (se 1 (by rfl) ⟨1396835, by rfl⟩ : syracuseStep 1862447 = 2793671) B2793671
theorem B1862471 : Blo 1240438 1862471 := bstep (se 1 (by rfl) ⟨1396853, by rfl⟩ : syracuseStep 1862471 = 2793707) B2793707
theorem B7072667 : Blo 1240438 7072667 := bstep (se 1 (by rfl) ⟨5304500, by rfl⟩ : syracuseStep 7072667 = 10609001) B10609001
theorem B3681335 : Blo 1240438 3681335 := bstep (se 1 (by rfl) ⟨2761001, by rfl⟩ : syracuseStep 3681335 = 5522003) B5522003
theorem B15912065 : Blo 1240438 15912065 := bstep (se 2 (by rfl) ⟨5967024, by rfl⟩ : syracuseStep 15912065 = 11934049) B11934049
theorem B6286571 : Blo 1240438 6286571 := bstep (se 1 (by rfl) ⟨4714928, by rfl⟩ : syracuseStep 6286571 = 9429857) B9429857
theorem B4713835 : Blo 1240438 4713835 := bstep (se 1 (by rfl) ⟨3535376, by rfl⟩ : syracuseStep 4713835 = 7070753) B7070753
theorem B1240527 : Blo 1240438 1240527 := bstep (se 1 (by rfl) ⟨930395, by rfl⟩ : syracuseStep 1240527 = 1860791) B1860791
theorem B1863167 : Blo 1240438 1863167 := bstep (se 1 (by rfl) ⟨1397375, by rfl⟩ : syracuseStep 1863167 = 2794751) B2794751
theorem B1240687 : Blo 1240438 1240687 := bstep (se 1 (by rfl) ⟨930515, by rfl⟩ : syracuseStep 1240687 = 1861031) B1861031
theorem B1863335 : Blo 1240438 1863335 := bstep (se 1 (by rfl) ⟨1397501, by rfl⟩ : syracuseStep 1863335 = 2795003) B2795003
theorem B5304143 : Blo 1240438 5304143 := bstep (se 1 (by rfl) ⟨3978107, by rfl⟩ : syracuseStep 5304143 = 7956215) B7956215
theorem B1863515 : Blo 1240438 1863515 := bstep (se 1 (by rfl) ⟨1397636, by rfl⟩ : syracuseStep 1863515 = 2795273) B2795273
theorem B4190183 : Blo 1240438 4190183 := bstep (se 1 (by rfl) ⟨3142637, by rfl⟩ : syracuseStep 4190183 = 6285275) B6285275
theorem B326447111 : Blo 1240438 326447111 := bstep (se 1 (by rfl) ⟨244835333, by rfl⟩ : syracuseStep 326447111 = 489670667) B489670667
theorem B1863503 : Blo 1240438 1863503 := bstep (se 1 (by rfl) ⟨1397627, by rfl⟩ : syracuseStep 1863503 = 2795255) B2795255
theorem B1241135 : Blo 1240438 1241135 := bstep (se 1 (by rfl) ⟨930851, by rfl⟩ : syracuseStep 1241135 = 1861703) B1861703
theorem B6287543 : Blo 1240438 6287543 := bstep (se 1 (by rfl) ⟨4715657, by rfl⟩ : syracuseStep 6287543 = 9431315) B9431315
theorem B4190399 : Blo 1240438 4190399 := bstep (se 1 (by rfl) ⟨3142799, by rfl⟩ : syracuseStep 4190399 = 6285599) B6285599
theorem B1241391 : Blo 1240438 1241391 := bstep (se 1 (by rfl) ⟨931043, by rfl⟩ : syracuseStep 1241391 = 1862087) B1862087
theorem B1241575 : Blo 1240438 1241575 := bstep (se 1 (by rfl) ⟨931181, by rfl⟩ : syracuseStep 1241575 = 1862363) B1862363
theorem B15110651 : Blo 1240438 15110651 := bstep (se 1 (by rfl) ⟨11332988, by rfl⟩ : syracuseStep 15110651 = 22665977) B22665977
theorem B1241711 : Blo 1240438 1241711 := bstep (se 1 (by rfl) ⟨931283, by rfl⟩ : syracuseStep 1241711 = 1862567) B1862567
theorem B22950515 : Blo 1240438 22950515 := bstep (se 1 (by rfl) ⟨17212886, by rfl⟩ : syracuseStep 22950515 = 34425773) B34425773
theorem B1241759 : Blo 1240438 1241759 := bstep (se 1 (by rfl) ⟨931319, by rfl⟩ : syracuseStep 1241759 = 1862639) B1862639
theorem B27227011 : Blo 1240438 27227011 := bstep (se 1 (by rfl) ⟨20420258, by rfl⟩ : syracuseStep 27227011 = 40840517) B40840517
theorem B13603721 : Blo 1240438 13603721 := bstep (se 2 (by rfl) ⟨5101395, by rfl⟩ : syracuseStep 13603721 = 10202791) B10202791
theorem B1242047 : Blo 1240438 1242047 := bstep (se 1 (by rfl) ⟨931535, by rfl⟩ : syracuseStep 1242047 = 1863071) B1863071
theorem B3773567 : Blo 1240438 3773567 := bstep (se 1 (by rfl) ⟨2830175, by rfl⟩ : syracuseStep 3773567 = 5660351) B5660351
theorem B1242303 : Blo 1240438 1242303 := bstep (se 1 (by rfl) ⟨931727, by rfl⟩ : syracuseStep 1242303 = 1863455) B1863455
theorem B6280415 : Blo 1240438 6280415 := bstep (se 1 (by rfl) ⟨4710311, by rfl⟩ : syracuseStep 6280415 = 9420623) B9420623
theorem B4192019 : Blo 1240438 4192019 := bstep (se 1 (by rfl) ⟨3144014, by rfl⟩ : syracuseStep 4192019 = 6288029) B6288029
theorem B13416425 : Blo 1240438 13416425 := bstep (se 2 (by rfl) ⟨5031159, by rfl⟩ : syracuseStep 13416425 = 10062319) B10062319
theorem B9426941 : Blo 1240438 9426941 := bstep (se 3 (by rfl) ⟨1767551, by rfl⟩ : syracuseStep 9426941 = 3535103) B3535103
theorem B6281225 : Blo 1240438 6281225 := bstep (se 2 (by rfl) ⟨2355459, by rfl⟩ : syracuseStep 6281225 = 4710919) B4710919
theorem B5962241 : Blo 1240438 5962241 := bstep (se 2 (by rfl) ⟨2235840, by rfl⟩ : syracuseStep 5962241 = 4471681) B4471681
theorem B124148467 : Blo 1240438 124148467 := bstep (se 1 (by rfl) ⟨93111350, by rfl⟩ : syracuseStep 124148467 = 186222701) B186222701
theorem B7953551 : Blo 1240438 7953551 := bstep (se 1 (by rfl) ⟨5965163, by rfl⟩ : syracuseStep 7953551 = 11930327) B11930327
theorem B6282521 : Blo 1240438 6282521 := bstep (se 2 (by rfl) ⟨2355945, by rfl⟩ : syracuseStep 6282521 = 4711891) B4711891
theorem B2096543 : Blo 1240438 2096543 := bstep (se 1 (by rfl) ⟨1572407, by rfl⟩ : syracuseStep 2096543 = 3144815) B3144815
theorem B32235043 : Blo 1240438 32235043 := bstep (se 1 (by rfl) ⟨24176282, by rfl⟩ : syracuseStep 32235043 = 48352565) B48352565
theorem B11320883 : Blo 1240438 11320883 := bstep (se 1 (by rfl) ⟨8490662, by rfl⟩ : syracuseStep 11320883 = 16981325) B16981325
theorem B2793023 : Blo 1240438 2793023 := bstep (se 1 (by rfl) ⟨2094767, by rfl⟩ : syracuseStep 2793023 = 4189535) B4189535
theorem B2793599 : Blo 1240438 2793599 := bstep (se 1 (by rfl) ⟨2095199, by rfl⟩ : syracuseStep 2793599 = 4190399) B4190399
theorem B2982043 : Blo 1240438 2982043 := bstep (se 1 (by rfl) ⟨2236532, by rfl⟩ : syracuseStep 2982043 = 4473065) B4473065
theorem B2515711 : Blo 1240438 2515711 := bstep (se 1 (by rfl) ⟨1886783, by rfl⟩ : syracuseStep 2515711 = 3773567) B3773567
theorem B4186943 : Blo 1240438 4186943 := bstep (se 1 (by rfl) ⟨3140207, by rfl⟩ : syracuseStep 4186943 = 6280415) B6280415
theorem B4187105 : Blo 1240438 4187105 := bstep (se 2 (by rfl) ⟨1570164, by rfl⟩ : syracuseStep 4187105 = 3140329) B3140329
theorem B2794679 : Blo 1240438 2794679 := bstep (se 1 (by rfl) ⟨2096009, by rfl⟩ : syracuseStep 2794679 = 4192019) B4192019
theorem B6284627 : Blo 1240438 6284627 := bstep (se 1 (by rfl) ⟨4713470, by rfl⟩ : syracuseStep 6284627 = 9426941) B9426941
theorem B4187483 : Blo 1240438 4187483 := bstep (se 1 (by rfl) ⟨3140612, by rfl⟩ : syracuseStep 4187483 = 6281225) B6281225
theorem B3974827 : Blo 1240438 3974827 := bstep (se 1 (by rfl) ⟨2981120, by rfl⟩ : syracuseStep 3974827 = 5962241) B5962241
theorem B6285113 : Blo 1240438 6285113 := bstep (se 2 (by rfl) ⟨2356917, by rfl⟩ : syracuseStep 6285113 = 4713835) B4713835
theorem B5302367 : Blo 1240438 5302367 := bstep (se 1 (by rfl) ⟨3976775, by rfl⟩ : syracuseStep 5302367 = 7953551) B7953551
theorem B4188347 : Blo 1240438 4188347 := bstep (se 1 (by rfl) ⟨3141260, by rfl⟩ : syracuseStep 4188347 = 6282521) B6282521
theorem B36276589 : Blo 1240438 36276589 := bstep (se 3 (by rfl) ⟨6801860, by rfl⟩ : syracuseStep 36276589 = 13603721) B13603721
theorem B7547255 : Blo 1240438 7547255 := bstep (se 1 (by rfl) ⟨5660441, by rfl⟩ : syracuseStep 7547255 = 11320883) B11320883
theorem B1862015 : Blo 1240438 1862015 := bstep (se 1 (by rfl) ⟨1396511, by rfl⟩ : syracuseStep 1862015 = 2793023) B2793023
theorem B217631407 : Blo 1240438 217631407 := bstep (se 1 (by rfl) ⟨163223555, by rfl⟩ : syracuseStep 217631407 = 326447111) B326447111
theorem B3140795 : Blo 1240438 3140795 := bstep (se 1 (by rfl) ⟨2355596, by rfl⟩ : syracuseStep 3140795 = 4711193) B4711193
theorem B1862939 : Blo 1240438 1862939 := bstep (se 1 (by rfl) ⟨1397204, by rfl⟩ : syracuseStep 1862939 = 2794409) B2794409
theorem B17902919 : Blo 1240438 17902919 := bstep (se 1 (by rfl) ⟨13427189, by rfl⟩ : syracuseStep 17902919 = 26854379) B26854379
theorem B1240511 : Blo 1240438 1240511 := bstep (se 1 (by rfl) ⟨930383, by rfl⟩ : syracuseStep 1240511 = 1860767) B1860767
theorem B2649619 : Blo 1240438 2649619 := bstep (se 1 (by rfl) ⟨1987214, by rfl⟩ : syracuseStep 2649619 = 3974429) B3974429
theorem B1863215 : Blo 1240438 1863215 := bstep (se 1 (by rfl) ⟨1397411, by rfl⟩ : syracuseStep 1863215 = 2794823) B2794823
theorem B120892985 : Blo 1240438 120892985 := bstep (se 2 (by rfl) ⟨45334869, by rfl⟩ : syracuseStep 120892985 = 90669739) B90669739
theorem B165531289 : Blo 1240438 165531289 := bstep (se 2 (by rfl) ⟨62074233, by rfl⟩ : syracuseStep 165531289 = 124148467) B124148467
theorem B4714139 : Blo 1240438 4714139 := bstep (se 1 (by rfl) ⟨3535604, by rfl⟩ : syracuseStep 4714139 = 7071209) B7071209
theorem B1863323 : Blo 1240438 1863323 := bstep (se 1 (by rfl) ⟨1397492, by rfl⟩ : syracuseStep 1863323 = 2794985) B2794985
theorem B1240743 : Blo 1240438 1240743 := bstep (se 1 (by rfl) ⟨930557, by rfl⟩ : syracuseStep 1240743 = 1861115) B1861115
theorem B1240767 : Blo 1240438 1240767 := bstep (se 1 (by rfl) ⟨930575, by rfl⟩ : syracuseStep 1240767 = 1861151) B1861151
theorem B1240815 : Blo 1240438 1240815 := bstep (se 1 (by rfl) ⟨930611, by rfl⟩ : syracuseStep 1240815 = 1861223) B1861223
theorem B36302681 : Blo 1240438 36302681 := bstep (se 2 (by rfl) ⟨13613505, by rfl⟩ : syracuseStep 36302681 = 27227011) B27227011
theorem B1241159 : Blo 1240438 1241159 := bstep (se 1 (by rfl) ⟨930869, by rfl⟩ : syracuseStep 1241159 = 1861739) B1861739
theorem B1241199 : Blo 1240438 1241199 := bstep (se 1 (by rfl) ⟨930899, by rfl⟩ : syracuseStep 1241199 = 1861799) B1861799
theorem B5304467 : Blo 1240438 5304467 := bstep (se 1 (by rfl) ⟨3978350, by rfl⟩ : syracuseStep 5304467 = 7956701) B7956701
theorem B3142111 : Blo 1240438 3142111 := bstep (se 1 (by rfl) ⟨2356583, by rfl⟩ : syracuseStep 3142111 = 4713167) B4713167
theorem B1241631 : Blo 1240438 1241631 := bstep (se 1 (by rfl) ⟨931223, by rfl⟩ : syracuseStep 1241631 = 1862447) B1862447
theorem B1241647 : Blo 1240438 1241647 := bstep (se 1 (by rfl) ⟨931235, by rfl⟩ : syracuseStep 1241647 = 1862471) B1862471
theorem B4715111 : Blo 1240438 4715111 := bstep (se 1 (by rfl) ⟨3536333, by rfl⟩ : syracuseStep 4715111 = 7072667) B7072667
theorem B2454223 : Blo 1240438 2454223 := bstep (se 1 (by rfl) ⟨1840667, by rfl⟩ : syracuseStep 2454223 = 3681335) B3681335
theorem B42980057 : Blo 1240438 42980057 := bstep (se 2 (by rfl) ⟨16117521, by rfl⟩ : syracuseStep 42980057 = 32235043) B32235043
theorem B4191047 : Blo 1240438 4191047 := bstep (se 1 (by rfl) ⟨3143285, by rfl⟩ : syracuseStep 4191047 = 6286571) B6286571
theorem B1397695 : Blo 1240438 1397695 := bstep (se 1 (by rfl) ⟨1048271, by rfl⟩ : syracuseStep 1397695 = 2096543) B2096543
theorem B1242111 : Blo 1240438 1242111 := bstep (se 1 (by rfl) ⟨931583, by rfl⟩ : syracuseStep 1242111 = 1863167) B1863167
theorem B1242223 : Blo 1240438 1242223 := bstep (se 1 (by rfl) ⟨931667, by rfl⟩ : syracuseStep 1242223 = 1863335) B1863335
theorem B3536095 : Blo 1240438 3536095 := bstep (se 1 (by rfl) ⟨2652071, by rfl⟩ : syracuseStep 3536095 = 5304143) B5304143
theorem B1242335 : Blo 1240438 1242335 := bstep (se 1 (by rfl) ⟨931751, by rfl⟩ : syracuseStep 1242335 = 1863503) B1863503
theorem B1242343 : Blo 1240438 1242343 := bstep (se 1 (by rfl) ⟨931757, by rfl⟩ : syracuseStep 1242343 = 1863515) B1863515
theorem B4191695 : Blo 1240438 4191695 := bstep (se 1 (by rfl) ⟨3143771, by rfl⟩ : syracuseStep 4191695 = 6287543) B6287543
theorem B5445245 : Blo 1240438 5445245 := bstep (se 3 (by rfl) ⟨1020983, by rfl⟩ : syracuseStep 5445245 = 2041967) B2041967
theorem B10073767 : Blo 1240438 10073767 := bstep (se 1 (by rfl) ⟨7555325, by rfl⟩ : syracuseStep 10073767 = 15110651) B15110651
theorem B15300343 : Blo 1240438 15300343 := bstep (se 1 (by rfl) ⟨11475257, by rfl⟩ : syracuseStep 15300343 = 22950515) B22950515
theorem B6281873 : Blo 1240438 6281873 := bstep (se 2 (by rfl) ⟨2355702, by rfl⟩ : syracuseStep 6281873 = 4711405) B4711405
theorem B8944283 : Blo 1240438 8944283 := bstep (se 1 (by rfl) ⟨6708212, by rfl⟩ : syracuseStep 8944283 = 13416425) B13416425
theorem B10074941 : Blo 1240438 10074941 := bstep (se 3 (by rfl) ⟨1889051, by rfl⟩ : syracuseStep 10074941 = 3778103) B3778103
theorem B10608043 : Blo 1240438 10608043 := bstep (se 1 (by rfl) ⟨7956032, by rfl⟩ : syracuseStep 10608043 = 15912065) B15912065
theorem B2793455 : Blo 1240438 2793455 := bstep (se 1 (by rfl) ⟨2095091, by rfl⟩ : syracuseStep 2793455 = 4190183) B4190183
theorem B2794031 : Blo 1240438 2794031 := bstep (se 1 (by rfl) ⟨2095523, by rfl⟩ : syracuseStep 2794031 = 4191047) B4191047
theorem B2794463 : Blo 1240438 2794463 := bstep (se 1 (by rfl) ⟨2095847, by rfl⟩ : syracuseStep 2794463 = 4191695) B4191695
theorem B5031503 : Blo 1240438 5031503 := bstep (se 1 (by rfl) ⟨3773627, by rfl⟩ : syracuseStep 5031503 = 7547255) B7547255
theorem B4187915 : Blo 1240438 4187915 := bstep (se 1 (by rfl) ⟨3140936, by rfl⟩ : syracuseStep 4187915 = 6281873) B6281873
theorem B3532825 : Blo 1240438 3532825 := bstep (se 2 (by rfl) ⟨1324809, by rfl⟩ : syracuseStep 3532825 = 2649619) B2649619
theorem B20400457 : Blo 1240438 20400457 := bstep (se 2 (by rfl) ⟨7650171, by rfl⟩ : syracuseStep 20400457 = 15300343) B15300343
theorem B80595323 : Blo 1240438 80595323 := bstep (se 1 (by rfl) ⟨60446492, by rfl⟩ : syracuseStep 80595323 = 120892985) B120892985
theorem B24201787 : Blo 1240438 24201787 := bstep (se 1 (by rfl) ⟨18151340, by rfl⟩ : syracuseStep 24201787 = 36302681) B36302681
theorem B1862303 : Blo 1240438 1862303 := bstep (se 1 (by rfl) ⟨1396727, by rfl⟩ : syracuseStep 1862303 = 2793455) B2793455
theorem B1862399 : Blo 1240438 1862399 := bstep (se 1 (by rfl) ⟨1396799, by rfl⟩ : syracuseStep 1862399 = 2793599) B2793599
theorem B3976057 : Blo 1240438 3976057 := bstep (se 2 (by rfl) ⟨1491021, by rfl⟩ : syracuseStep 3976057 = 2982043) B2982043
theorem B48368785 : Blo 1240438 48368785 := bstep (se 2 (by rfl) ⟨18138294, by rfl⟩ : syracuseStep 48368785 = 36276589) B36276589
theorem B4189481 : Blo 1240438 4189481 := bstep (se 2 (by rfl) ⟨1571055, by rfl⟩ : syracuseStep 4189481 = 3142111) B3142111
theorem B1863119 : Blo 1240438 1863119 := bstep (se 1 (by rfl) ⟨1397339, by rfl⟩ : syracuseStep 1863119 = 2794679) B2794679
theorem B4189751 : Blo 1240438 4189751 := bstep (se 1 (by rfl) ⟨3142313, by rfl⟩ : syracuseStep 4189751 = 6284627) B6284627
theorem B3272297 : Blo 1240438 3272297 := bstep (se 2 (by rfl) ⟨1227111, by rfl⟩ : syracuseStep 3272297 = 2454223) B2454223
theorem B3354281 : Blo 1240438 3354281 := bstep (se 2 (by rfl) ⟨1257855, by rfl⟩ : syracuseStep 3354281 = 2515711) B2515711
theorem B4190075 : Blo 1240438 4190075 := bstep (se 1 (by rfl) ⟨3142556, by rfl⟩ : syracuseStep 4190075 = 6285113) B6285113
theorem B1863593 : Blo 1240438 1863593 := bstep (se 2 (by rfl) ⟨698847, by rfl⟩ : syracuseStep 1863593 = 1397695) B1397695
theorem B3534911 : Blo 1240438 3534911 := bstep (se 1 (by rfl) ⟨2651183, by rfl⟩ : syracuseStep 3534911 = 5302367) B5302367
theorem B1241343 : Blo 1240438 1241343 := bstep (se 1 (by rfl) ⟨931007, by rfl⟩ : syracuseStep 1241343 = 1862015) B1862015
theorem B4714793 : Blo 1240438 4714793 := bstep (se 2 (by rfl) ⟨1768047, by rfl⟩ : syracuseStep 4714793 = 3536095) B3536095
theorem B14520653 : Blo 1240438 14520653 := bstep (se 3 (by rfl) ⟨2722622, by rfl⟩ : syracuseStep 14520653 = 5445245) B5445245
theorem B23851421 : Blo 1240438 23851421 := bstep (se 3 (by rfl) ⟨4472141, by rfl⟩ : syracuseStep 23851421 = 8944283) B8944283
theorem B14144057 : Blo 1240438 14144057 := bstep (se 2 (by rfl) ⟨5304021, by rfl⟩ : syracuseStep 14144057 = 10608043) B10608043
theorem B2093863 : Blo 1240438 2093863 := bstep (se 1 (by rfl) ⟨1570397, by rfl⟩ : syracuseStep 2093863 = 3140795) B3140795
theorem B1241959 : Blo 1240438 1241959 := bstep (se 1 (by rfl) ⟨931469, by rfl⟩ : syracuseStep 1241959 = 1862939) B1862939
theorem B13431689 : Blo 1240438 13431689 := bstep (se 2 (by rfl) ⟨5036883, by rfl⟩ : syracuseStep 13431689 = 10073767) B10073767
theorem B1242143 : Blo 1240438 1242143 := bstep (se 1 (by rfl) ⟨931607, by rfl⟩ : syracuseStep 1242143 = 1863215) B1863215
theorem B3142759 : Blo 1240438 3142759 := bstep (se 1 (by rfl) ⟨2357069, by rfl⟩ : syracuseStep 3142759 = 4714139) B4714139
theorem B1242215 : Blo 1240438 1242215 := bstep (se 1 (by rfl) ⟨931661, by rfl⟩ : syracuseStep 1242215 = 1863323) B1863323
theorem B3536311 : Blo 1240438 3536311 := bstep (se 1 (by rfl) ⟨2652233, by rfl⟩ : syracuseStep 3536311 = 5304467) B5304467
theorem B3143407 : Blo 1240438 3143407 := bstep (se 1 (by rfl) ⟨2357555, by rfl⟩ : syracuseStep 3143407 = 4715111) B4715111
theorem B28653371 : Blo 1240438 28653371 := bstep (se 1 (by rfl) ⟨21490028, by rfl⟩ : syracuseStep 28653371 = 42980057) B42980057
theorem B2791295 : Blo 1240438 2791295 := bstep (se 1 (by rfl) ⟨2093471, by rfl⟩ : syracuseStep 2791295 = 4186943) B4186943
theorem B2791403 : Blo 1240438 2791403 := bstep (se 1 (by rfl) ⟨2093552, by rfl⟩ : syracuseStep 2791403 = 4187105) B4187105
theorem B2791655 : Blo 1240438 2791655 := bstep (se 1 (by rfl) ⟨2093741, by rfl⟩ : syracuseStep 2791655 = 4187483) B4187483
theorem B290175209 : Blo 1240438 290175209 := bstep (se 2 (by rfl) ⟨108815703, by rfl⟩ : syracuseStep 290175209 = 217631407) B217631407
theorem B2792231 : Blo 1240438 2792231 := bstep (se 1 (by rfl) ⟨2094173, by rfl⟩ : syracuseStep 2792231 = 4188347) B4188347
theorem B6716627 : Blo 1240438 6716627 := bstep (se 1 (by rfl) ⟨5037470, by rfl⟩ : syracuseStep 6716627 = 10074941) B10074941
theorem B220708385 : Blo 1240438 220708385 := bstep (se 2 (by rfl) ⟨82765644, by rfl⟩ : syracuseStep 220708385 = 165531289) B165531289
theorem B11935279 : Blo 1240438 11935279 := bstep (se 1 (by rfl) ⟨8951459, by rfl⟩ : syracuseStep 11935279 = 17902919) B17902919
theorem B5299769 : Blo 1240438 5299769 := bstep (se 2 (by rfl) ⟨1987413, by rfl⟩ : syracuseStep 5299769 = 3974827) B3974827
theorem B4710433 : Blo 1240438 4710433 := bstep (se 2 (by rfl) ⟨1766412, by rfl⟩ : syracuseStep 4710433 = 3532825) B3532825
theorem B15900947 : Blo 1240438 15900947 := bstep (se 1 (by rfl) ⟨11925710, by rfl⟩ : syracuseStep 15900947 = 23851421) B23851421
theorem B9429371 : Blo 1240438 9429371 := bstep (se 1 (by rfl) ⟨7072028, by rfl⟩ : syracuseStep 9429371 = 14144057) B14144057
theorem B8954459 : Blo 1240438 8954459 := bstep (se 1 (by rfl) ⟨6715844, by rfl⟩ : syracuseStep 8954459 = 13431689) B13431689
theorem B32269049 : Blo 1240438 32269049 := bstep (se 2 (by rfl) ⟨12100893, by rfl⟩ : syracuseStep 32269049 = 24201787) B24201787
theorem B5301409 : Blo 1240438 5301409 := bstep (se 2 (by rfl) ⟨1988028, by rfl⟩ : syracuseStep 5301409 = 3976057) B3976057
theorem B1860863 : Blo 1240438 1860863 := bstep (se 1 (by rfl) ⟨1395647, by rfl⟩ : syracuseStep 1860863 = 2791295) B2791295
theorem B1860935 : Blo 1240438 1860935 := bstep (se 1 (by rfl) ⟨1395701, by rfl⟩ : syracuseStep 1860935 = 2791403) B2791403
theorem B1861103 : Blo 1240438 1861103 := bstep (se 1 (by rfl) ⟨1395827, by rfl⟩ : syracuseStep 1861103 = 2791655) B2791655
theorem B8726125 : Blo 1240438 8726125 := bstep (se 3 (by rfl) ⟨1636148, by rfl⟩ : syracuseStep 8726125 = 3272297) B3272297
theorem B1861487 : Blo 1240438 1861487 := bstep (se 1 (by rfl) ⟨1396115, by rfl⟩ : syracuseStep 1861487 = 2792231) B2792231
theorem B147138923 : Blo 1240438 147138923 := bstep (se 1 (by rfl) ⟨110354192, by rfl⟩ : syracuseStep 147138923 = 220708385) B220708385
theorem B3533179 : Blo 1240438 3533179 := bstep (se 1 (by rfl) ⟨2649884, by rfl⟩ : syracuseStep 3533179 = 5299769) B5299769
theorem B1862687 : Blo 1240438 1862687 := bstep (se 1 (by rfl) ⟨1397015, by rfl⟩ : syracuseStep 1862687 = 2794031) B2794031
theorem B27200609 : Blo 1240438 27200609 := bstep (se 2 (by rfl) ⟨10200228, by rfl⟩ : syracuseStep 27200609 = 20400457) B20400457
theorem B1862975 : Blo 1240438 1862975 := bstep (se 1 (by rfl) ⟨1397231, by rfl⟩ : syracuseStep 1862975 = 2794463) B2794463
theorem B3354335 : Blo 1240438 3354335 := bstep (se 1 (by rfl) ⟨2515751, by rfl⟩ : syracuseStep 3354335 = 5031503) B5031503
theorem B4190345 : Blo 1240438 4190345 := bstep (se 2 (by rfl) ⟨1571379, by rfl⟩ : syracuseStep 4190345 = 3142759) B3142759
theorem B193450139 : Blo 1240438 193450139 := bstep (se 1 (by rfl) ⟨145087604, by rfl⟩ : syracuseStep 193450139 = 290175209) B290175209
theorem B64491713 : Blo 1240438 64491713 := bstep (se 2 (by rfl) ⟨24184392, by rfl⟩ : syracuseStep 64491713 = 48368785) B48368785
theorem B1241535 : Blo 1240438 1241535 := bstep (se 1 (by rfl) ⟨931151, by rfl⟩ : syracuseStep 1241535 = 1862303) B1862303
theorem B1241599 : Blo 1240438 1241599 := bstep (se 1 (by rfl) ⟨931199, by rfl⟩ : syracuseStep 1241599 = 1862399) B1862399
theorem B4715081 : Blo 1240438 4715081 := bstep (se 2 (by rfl) ⟨1768155, by rfl⟩ : syracuseStep 4715081 = 3536311) B3536311
theorem B15913705 : Blo 1240438 15913705 := bstep (se 2 (by rfl) ⟨5967639, by rfl⟩ : syracuseStep 15913705 = 11935279) B11935279
theorem B4477751 : Blo 1240438 4477751 := bstep (se 1 (by rfl) ⟨3358313, by rfl⟩ : syracuseStep 4477751 = 6716627) B6716627
theorem B1242079 : Blo 1240438 1242079 := bstep (se 1 (by rfl) ⟨931559, by rfl⟩ : syracuseStep 1242079 = 1863119) B1863119
theorem B4191209 : Blo 1240438 4191209 := bstep (se 2 (by rfl) ⟨1571703, by rfl⟩ : syracuseStep 4191209 = 3143407) B3143407
theorem B1242395 : Blo 1240438 1242395 := bstep (se 1 (by rfl) ⟨931796, by rfl⟩ : syracuseStep 1242395 = 1863593) B1863593
theorem B2356607 : Blo 1240438 2356607 := bstep (se 1 (by rfl) ⟨1767455, by rfl⟩ : syracuseStep 2356607 = 3534911) B3534911
theorem B3143195 : Blo 1240438 3143195 := bstep (se 1 (by rfl) ⟨2357396, by rfl⟩ : syracuseStep 3143195 = 4714793) B4714793
theorem B9680435 : Blo 1240438 9680435 := bstep (se 1 (by rfl) ⟨7260326, by rfl⟩ : syracuseStep 9680435 = 14520653) B14520653
theorem B2791817 : Blo 1240438 2791817 := bstep (se 2 (by rfl) ⟨1046931, by rfl⟩ : syracuseStep 2791817 = 2093863) B2093863
theorem B2791943 : Blo 1240438 2791943 := bstep (se 1 (by rfl) ⟨2093957, by rfl⟩ : syracuseStep 2791943 = 4187915) B4187915
theorem B19102247 : Blo 1240438 19102247 := bstep (se 1 (by rfl) ⟨14326685, by rfl⟩ : syracuseStep 19102247 = 28653371) B28653371
theorem B53730215 : Blo 1240438 53730215 := bstep (se 1 (by rfl) ⟨40297661, by rfl⟩ : syracuseStep 53730215 = 80595323) B80595323
theorem B2792987 : Blo 1240438 2792987 := bstep (se 1 (by rfl) ⟨2094740, by rfl⟩ : syracuseStep 2792987 = 4189481) B4189481
theorem B2793167 : Blo 1240438 2793167 := bstep (se 1 (by rfl) ⟨2094875, by rfl⟩ : syracuseStep 2793167 = 4189751) B4189751
theorem B2236187 : Blo 1240438 2236187 := bstep (se 1 (by rfl) ⟨1677140, by rfl⟩ : syracuseStep 2236187 = 3354281) B3354281
theorem B2793383 : Blo 1240438 2793383 := bstep (se 1 (by rfl) ⟨2095037, by rfl⟩ : syracuseStep 2793383 = 4190075) B4190075
theorem B2793563 : Blo 1240438 2793563 := bstep (se 1 (by rfl) ⟨2095172, by rfl⟩ : syracuseStep 2793563 = 4190345) B4190345
theorem B128966759 : Blo 1240438 128966759 := bstep (se 1 (by rfl) ⟨96725069, by rfl⟩ : syracuseStep 128966759 = 193450139) B193450139
theorem B10600631 : Blo 1240438 10600631 := bstep (se 1 (by rfl) ⟨7950473, by rfl⟩ : syracuseStep 10600631 = 15900947) B15900947
theorem B4710905 : Blo 1240438 4710905 := bstep (se 2 (by rfl) ⟨1766589, by rfl⟩ : syracuseStep 4710905 = 3533179) B3533179
theorem B21512699 : Blo 1240438 21512699 := bstep (se 1 (by rfl) ⟨16134524, by rfl⟩ : syracuseStep 21512699 = 32269049) B32269049
theorem B2794139 : Blo 1240438 2794139 := bstep (se 1 (by rfl) ⟨2095604, by rfl⟩ : syracuseStep 2794139 = 4191209) B4191209
theorem B21218273 : Blo 1240438 21218273 := bstep (se 2 (by rfl) ⟨7956852, by rfl⟩ : syracuseStep 21218273 = 15913705) B15913705
theorem B98092615 : Blo 1240438 98092615 := bstep (se 1 (by rfl) ⟨73569461, by rfl⟩ : syracuseStep 98092615 = 147138923) B147138923
theorem B1861211 : Blo 1240438 1861211 := bstep (se 1 (by rfl) ⟨1395908, by rfl⟩ : syracuseStep 1861211 = 2791817) B2791817
theorem B1861295 : Blo 1240438 1861295 := bstep (se 1 (by rfl) ⟨1395971, by rfl⟩ : syracuseStep 1861295 = 2791943) B2791943
theorem B11634833 : Blo 1240438 11634833 := bstep (se 2 (by rfl) ⟨4363062, by rfl⟩ : syracuseStep 11634833 = 8726125) B8726125
theorem B1861991 : Blo 1240438 1861991 := bstep (se 1 (by rfl) ⟨1396493, by rfl⟩ : syracuseStep 1861991 = 2792987) B2792987
theorem B1862111 : Blo 1240438 1862111 := bstep (se 1 (by rfl) ⟨1396583, by rfl⟩ : syracuseStep 1862111 = 2793167) B2793167
theorem B1862255 : Blo 1240438 1862255 := bstep (se 1 (by rfl) ⟨1396691, by rfl⟩ : syracuseStep 1862255 = 2793383) B2793383
theorem B42994475 : Blo 1240438 42994475 := bstep (se 1 (by rfl) ⟨32245856, by rfl⟩ : syracuseStep 42994475 = 64491713) B64491713
theorem B6286247 : Blo 1240438 6286247 := bstep (se 1 (by rfl) ⟨4714685, by rfl⟩ : syracuseStep 6286247 = 9429371) B9429371
theorem B2985167 : Blo 1240438 2985167 := bstep (se 1 (by rfl) ⟨2238875, by rfl⟩ : syracuseStep 2985167 = 4477751) B4477751
theorem B1240575 : Blo 1240438 1240575 := bstep (se 1 (by rfl) ⟨930431, by rfl⟩ : syracuseStep 1240575 = 1860863) B1860863
theorem B1240623 : Blo 1240438 1240623 := bstep (se 1 (by rfl) ⟨930467, by rfl⟩ : syracuseStep 1240623 = 1860935) B1860935
theorem B1240735 : Blo 1240438 1240735 := bstep (se 1 (by rfl) ⟨930551, by rfl⟩ : syracuseStep 1240735 = 1861103) B1861103
theorem B1240991 : Blo 1240438 1240991 := bstep (se 1 (by rfl) ⟨930743, by rfl⟩ : syracuseStep 1240991 = 1861487) B1861487
theorem B12734831 : Blo 1240438 12734831 := bstep (se 1 (by rfl) ⟨9551123, by rfl⟩ : syracuseStep 12734831 = 19102247) B19102247
theorem B35820143 : Blo 1240438 35820143 := bstep (se 1 (by rfl) ⟨26865107, by rfl⟩ : syracuseStep 35820143 = 53730215) B53730215
theorem B1241791 : Blo 1240438 1241791 := bstep (se 1 (by rfl) ⟨931343, by rfl⟩ : syracuseStep 1241791 = 1862687) B1862687
theorem B18133739 : Blo 1240438 18133739 := bstep (se 1 (by rfl) ⟨13600304, by rfl⟩ : syracuseStep 18133739 = 27200609) B27200609
theorem B1241983 : Blo 1240438 1241983 := bstep (se 1 (by rfl) ⟨931487, by rfl⟩ : syracuseStep 1241983 = 1862975) B1862975
theorem B6280577 : Blo 1240438 6280577 := bstep (se 2 (by rfl) ⟨2355216, by rfl⟩ : syracuseStep 6280577 = 4710433) B4710433
theorem B3143387 : Blo 1240438 3143387 := bstep (se 1 (by rfl) ⟨2357540, by rfl⟩ : syracuseStep 3143387 = 4715081) B4715081
theorem B5969639 : Blo 1240438 5969639 := bstep (se 1 (by rfl) ⟨4477229, by rfl⟩ : syracuseStep 5969639 = 8954459) B8954459
theorem B1571071 : Blo 1240438 1571071 := bstep (se 1 (by rfl) ⟨1178303, by rfl⟩ : syracuseStep 1571071 = 2356607) B2356607
theorem B2095463 : Blo 1240438 2095463 := bstep (se 1 (by rfl) ⟨1571597, by rfl⟩ : syracuseStep 2095463 = 3143195) B3143195
theorem B6453623 : Blo 1240438 6453623 := bstep (se 1 (by rfl) ⟨4840217, by rfl⟩ : syracuseStep 6453623 = 9680435) B9680435
theorem B7068545 : Blo 1240438 7068545 := bstep (se 2 (by rfl) ⟨2650704, by rfl⟩ : syracuseStep 7068545 = 5301409) B5301409
theorem B5963165 : Blo 1240438 5963165 := bstep (se 3 (by rfl) ⟨1118093, by rfl⟩ : syracuseStep 5963165 = 2236187) B2236187
theorem B2236223 : Blo 1240438 2236223 := bstep (se 1 (by rfl) ⟨1677167, by rfl⟩ : syracuseStep 2236223 = 3354335) B3354335
theorem B23880095 : Blo 1240438 23880095 := bstep (se 1 (by rfl) ⟨17910071, by rfl⟩ : syracuseStep 23880095 = 35820143) B35820143
theorem B4187051 : Blo 1240438 4187051 := bstep (se 1 (by rfl) ⟨3140288, by rfl⟩ : syracuseStep 4187051 = 6280577) B6280577
theorem B4302415 : Blo 1240438 4302415 := bstep (se 1 (by rfl) ⟨3226811, by rfl⟩ : syracuseStep 4302415 = 6453623) B6453623
theorem B4712363 : Blo 1240438 4712363 := bstep (se 1 (by rfl) ⟨3534272, by rfl⟩ : syracuseStep 4712363 = 7068545) B7068545
theorem B15919037 : Blo 1240438 15919037 := bstep (se 3 (by rfl) ⟨2984819, by rfl⟩ : syracuseStep 15919037 = 5969639) B5969639
theorem B3975443 : Blo 1240438 3975443 := bstep (se 1 (by rfl) ⟨2981582, by rfl⟩ : syracuseStep 3975443 = 5963165) B5963165
theorem B1862375 : Blo 1240438 1862375 := bstep (se 1 (by rfl) ⟨1396781, by rfl⟩ : syracuseStep 1862375 = 2793563) B2793563
theorem B85977839 : Blo 1240438 85977839 := bstep (se 1 (by rfl) ⟨64483379, by rfl⟩ : syracuseStep 85977839 = 128966759) B128966759
theorem B3140603 : Blo 1240438 3140603 := bstep (se 1 (by rfl) ⟨2355452, by rfl⟩ : syracuseStep 3140603 = 4710905) B4710905
theorem B1862759 : Blo 1240438 1862759 := bstep (se 1 (by rfl) ⟨1397069, by rfl⟩ : syracuseStep 1862759 = 2794139) B2794139
theorem B33959549 : Blo 1240438 33959549 := bstep (se 3 (by rfl) ⟨6367415, by rfl⟩ : syracuseStep 33959549 = 12734831) B12734831
theorem B1240807 : Blo 1240438 1240807 := bstep (se 1 (by rfl) ⟨930605, by rfl⟩ : syracuseStep 1240807 = 1861211) B1861211
theorem B1240863 : Blo 1240438 1240863 := bstep (se 1 (by rfl) ⟨930647, by rfl⟩ : syracuseStep 1240863 = 1861295) B1861295
theorem B1241327 : Blo 1240438 1241327 := bstep (se 1 (by rfl) ⟨930995, by rfl⟩ : syracuseStep 1241327 = 1861991) B1861991
theorem B1396975 : Blo 1240438 1396975 := bstep (se 1 (by rfl) ⟨1047731, by rfl⟩ : syracuseStep 1396975 = 2095463) B2095463
theorem B1241407 : Blo 1240438 1241407 := bstep (se 1 (by rfl) ⟨931055, by rfl⟩ : syracuseStep 1241407 = 1862111) B1862111
theorem B1241503 : Blo 1240438 1241503 := bstep (se 1 (by rfl) ⟨931127, by rfl⟩ : syracuseStep 1241503 = 1862255) B1862255
theorem B4190831 : Blo 1240438 4190831 := bstep (se 1 (by rfl) ⟨3143123, by rfl⟩ : syracuseStep 4190831 = 6286247) B6286247
theorem B130790153 : Blo 1240438 130790153 := bstep (se 2 (by rfl) ⟨49046307, by rfl⟩ : syracuseStep 130790153 = 98092615) B98092615
theorem B7067087 : Blo 1240438 7067087 := bstep (se 1 (by rfl) ⟨5300315, by rfl⟩ : syracuseStep 7067087 = 10600631) B10600631
theorem B2094761 : Blo 1240438 2094761 := bstep (se 2 (by rfl) ⟨785535, by rfl⟩ : syracuseStep 2094761 = 1571071) B1571071
theorem B14341799 : Blo 1240438 14341799 := bstep (se 1 (by rfl) ⟨10756349, by rfl⟩ : syracuseStep 14341799 = 21512699) B21512699
theorem B12089159 : Blo 1240438 12089159 := bstep (se 1 (by rfl) ⟨9066869, by rfl⟩ : syracuseStep 12089159 = 18133739) B18133739
theorem B14145515 : Blo 1240438 14145515 := bstep (se 1 (by rfl) ⟨10609136, by rfl⟩ : syracuseStep 14145515 = 21218273) B21218273
theorem B2095591 : Blo 1240438 2095591 := bstep (se 1 (by rfl) ⟨1571693, by rfl⟩ : syracuseStep 2095591 = 3143387) B3143387
theorem B7756555 : Blo 1240438 7756555 := bstep (se 1 (by rfl) ⟨5817416, by rfl⟩ : syracuseStep 7756555 = 11634833) B11634833
theorem B28662983 : Blo 1240438 28662983 := bstep (se 1 (by rfl) ⟨21497237, by rfl⟩ : syracuseStep 28662983 = 42994475) B42994475
theorem B1990111 : Blo 1240438 1990111 := bstep (se 1 (by rfl) ⟨1492583, by rfl⟩ : syracuseStep 1990111 = 2985167) B2985167
theorem B1490815 : Blo 1240438 1490815 := bstep (se 1 (by rfl) ⟨1118111, by rfl⟩ : syracuseStep 1490815 = 2236223) B2236223
theorem B2793887 : Blo 1240438 2793887 := bstep (se 1 (by rfl) ⟨2095415, by rfl⟩ : syracuseStep 2793887 = 4190831) B4190831
theorem B2794121 : Blo 1240438 2794121 := bstep (se 2 (by rfl) ⟨1047795, by rfl⟩ : syracuseStep 2794121 = 2095591) B2095591
theorem B4711391 : Blo 1240438 4711391 := bstep (se 1 (by rfl) ⟨3533543, by rfl⟩ : syracuseStep 4711391 = 7067087) B7067087
theorem B9561199 : Blo 1240438 9561199 := bstep (se 1 (by rfl) ⟨7170899, by rfl⟩ : syracuseStep 9561199 = 14341799) B14341799
theorem B9430343 : Blo 1240438 9430343 := bstep (se 1 (by rfl) ⟨7072757, by rfl⟩ : syracuseStep 9430343 = 14145515) B14145515
theorem B5736553 : Blo 1240438 5736553 := bstep (se 2 (by rfl) ⟨2151207, by rfl⟩ : syracuseStep 5736553 = 4302415) B4302415
theorem B15920063 : Blo 1240438 15920063 := bstep (se 1 (by rfl) ⟨11940047, by rfl⟩ : syracuseStep 15920063 = 23880095) B23880095
theorem B1862633 : Blo 1240438 1862633 := bstep (se 2 (by rfl) ⟨698487, by rfl⟩ : syracuseStep 1862633 = 1396975) B1396975
theorem B10342073 : Blo 1240438 10342073 := bstep (se 2 (by rfl) ⟨3878277, by rfl⟩ : syracuseStep 10342073 = 7756555) B7756555
theorem B1396507 : Blo 1240438 1396507 := bstep (se 1 (by rfl) ⟨1047380, by rfl⟩ : syracuseStep 1396507 = 2094761) B2094761
theorem B3141575 : Blo 1240438 3141575 := bstep (se 1 (by rfl) ⟨2356181, by rfl⟩ : syracuseStep 3141575 = 4712363) B4712363
theorem B10612691 : Blo 1240438 10612691 := bstep (se 1 (by rfl) ⟨7959518, by rfl⟩ : syracuseStep 10612691 = 15919037) B15919037
theorem B2650295 : Blo 1240438 2650295 := bstep (se 1 (by rfl) ⟨1987721, by rfl⟩ : syracuseStep 2650295 = 3975443) B3975443
theorem B1241583 : Blo 1240438 1241583 := bstep (se 1 (by rfl) ⟨931187, by rfl⟩ : syracuseStep 1241583 = 1862375) B1862375
theorem B2093735 : Blo 1240438 2093735 := bstep (se 1 (by rfl) ⟨1570301, by rfl⟩ : syracuseStep 2093735 = 3140603) B3140603
theorem B1241839 : Blo 1240438 1241839 := bstep (se 1 (by rfl) ⟨931379, by rfl⟩ : syracuseStep 1241839 = 1862759) B1862759
theorem B19108655 : Blo 1240438 19108655 := bstep (se 1 (by rfl) ⟨14331491, by rfl⟩ : syracuseStep 19108655 = 28662983) B28662983
theorem B22639699 : Blo 1240438 22639699 := bstep (se 1 (by rfl) ⟨16979774, by rfl⟩ : syracuseStep 22639699 = 33959549) B33959549
theorem B1987753 : Blo 1240438 1987753 := bstep (se 2 (by rfl) ⟨745407, by rfl⟩ : syracuseStep 1987753 = 1490815) B1490815
theorem B87193435 : Blo 1240438 87193435 := bstep (se 1 (by rfl) ⟨65395076, by rfl⟩ : syracuseStep 87193435 = 130790153) B130790153
theorem B2791367 : Blo 1240438 2791367 := bstep (se 1 (by rfl) ⟨2093525, by rfl⟩ : syracuseStep 2791367 = 4187051) B4187051
theorem B8059439 : Blo 1240438 8059439 := bstep (se 1 (by rfl) ⟨6044579, by rfl⟩ : syracuseStep 8059439 = 12089159) B12089159
theorem B57318559 : Blo 1240438 57318559 := bstep (se 1 (by rfl) ⟨42988919, by rfl⟩ : syracuseStep 57318559 = 85977839) B85977839
theorem B2653481 : Blo 1240438 2653481 := bstep (se 2 (by rfl) ⟨995055, by rfl⟩ : syracuseStep 2653481 = 1990111) B1990111
theorem B12739103 : Blo 1240438 12739103 := bstep (se 1 (by rfl) ⟨9554327, by rfl⟩ : syracuseStep 12739103 = 19108655) B19108655
theorem B1860911 : Blo 1240438 1860911 := bstep (se 1 (by rfl) ⟨1395683, by rfl⟩ : syracuseStep 1860911 = 2791367) B2791367
theorem B12748265 : Blo 1240438 12748265 := bstep (se 2 (by rfl) ⟨4780599, by rfl⟩ : syracuseStep 12748265 = 9561199) B9561199
theorem B1862009 : Blo 1240438 1862009 := bstep (se 2 (by rfl) ⟨698253, by rfl⟩ : syracuseStep 1862009 = 1396507) B1396507
theorem B1862591 : Blo 1240438 1862591 := bstep (se 1 (by rfl) ⟨1396943, by rfl⟩ : syracuseStep 1862591 = 2793887) B2793887
theorem B1862747 : Blo 1240438 1862747 := bstep (se 1 (by rfl) ⟨1397060, by rfl⟩ : syracuseStep 1862747 = 2794121) B2794121
theorem B1395823 : Blo 1240438 1395823 := bstep (se 1 (by rfl) ⟨1046867, by rfl⟩ : syracuseStep 1395823 = 2093735) B2093735
theorem B3140927 : Blo 1240438 3140927 := bstep (se 1 (by rfl) ⟨2355695, by rfl⟩ : syracuseStep 3140927 = 4711391) B4711391
theorem B6286895 : Blo 1240438 6286895 := bstep (se 1 (by rfl) ⟨4715171, by rfl⟩ : syracuseStep 6286895 = 9430343) B9430343
theorem B2650337 : Blo 1240438 2650337 := bstep (se 2 (by rfl) ⟨993876, by rfl⟩ : syracuseStep 2650337 = 1987753) B1987753
theorem B10613375 : Blo 1240438 10613375 := bstep (se 1 (by rfl) ⟨7960031, by rfl⟩ : syracuseStep 10613375 = 15920063) B15920063
theorem B1241755 : Blo 1240438 1241755 := bstep (se 1 (by rfl) ⟨931316, by rfl⟩ : syracuseStep 1241755 = 1862633) B1862633
theorem B116257913 : Blo 1240438 116257913 := bstep (se 2 (by rfl) ⟨43596717, by rfl⟩ : syracuseStep 116257913 = 87193435) B87193435
theorem B6894715 : Blo 1240438 6894715 := bstep (se 1 (by rfl) ⟨5171036, by rfl⟩ : syracuseStep 6894715 = 10342073) B10342073
theorem B2094383 : Blo 1240438 2094383 := bstep (se 1 (by rfl) ⟨1570787, by rfl⟩ : syracuseStep 2094383 = 3141575) B3141575
theorem B7075127 : Blo 1240438 7075127 := bstep (se 1 (by rfl) ⟨5306345, by rfl⟩ : syracuseStep 7075127 = 10612691) B10612691
theorem B1766863 : Blo 1240438 1766863 := bstep (se 1 (by rfl) ⟨1325147, by rfl⟩ : syracuseStep 1766863 = 2650295) B2650295
theorem B305698981 : Blo 1240438 305698981 := bstep (se 4 (by rfl) ⟨28659279, by rfl⟩ : syracuseStep 305698981 = 57318559) B57318559
theorem B30186265 : Blo 1240438 30186265 := bstep (se 2 (by rfl) ⟨11319849, by rfl⟩ : syracuseStep 30186265 = 22639699) B22639699
theorem B5372959 : Blo 1240438 5372959 := bstep (se 1 (by rfl) ⟨4029719, by rfl⟩ : syracuseStep 5372959 = 8059439) B8059439
theorem B122379797 : Blo 1240438 122379797 := bstep (se 6 (by rfl) ⟨2868276, by rfl⟩ : syracuseStep 122379797 = 5736553) B5736553
theorem B1768987 : Blo 1240438 1768987 := bstep (se 1 (by rfl) ⟨1326740, by rfl⟩ : syracuseStep 1768987 = 2653481) B2653481
theorem B77505275 : Blo 1240438 77505275 := bstep (se 1 (by rfl) ⟨58128956, by rfl⟩ : syracuseStep 77505275 = 116257913) B116257913
theorem B40248353 : Blo 1240438 40248353 := bstep (se 2 (by rfl) ⟨15093132, by rfl⟩ : syracuseStep 40248353 = 30186265) B30186265
theorem B1861097 : Blo 1240438 1861097 := bstep (se 2 (by rfl) ⟨697911, by rfl⟩ : syracuseStep 1861097 = 1395823) B1395823
theorem B9192953 : Blo 1240438 9192953 := bstep (se 2 (by rfl) ⟨3447357, by rfl⟩ : syracuseStep 9192953 = 6894715) B6894715
theorem B81586531 : Blo 1240438 81586531 := bstep (se 1 (by rfl) ⟨61189898, by rfl⟩ : syracuseStep 81586531 = 122379797) B122379797
theorem B1240607 : Blo 1240438 1240607 := bstep (se 1 (by rfl) ⟨930455, by rfl⟩ : syracuseStep 1240607 = 1860911) B1860911
theorem B1396255 : Blo 1240438 1396255 := bstep (se 1 (by rfl) ⟨1047191, by rfl⟩ : syracuseStep 1396255 = 2094383) B2094383
theorem B8498843 : Blo 1240438 8498843 := bstep (se 1 (by rfl) ⟨6374132, by rfl⟩ : syracuseStep 8498843 = 12748265) B12748265
theorem B7163945 : Blo 1240438 7163945 := bstep (se 2 (by rfl) ⟨2686479, by rfl⟩ : syracuseStep 7163945 = 5372959) B5372959
theorem B1241339 : Blo 1240438 1241339 := bstep (se 1 (by rfl) ⟨931004, by rfl⟩ : syracuseStep 1241339 = 1862009) B1862009
theorem B2355817 : Blo 1240438 2355817 := bstep (se 2 (by rfl) ⟨883431, by rfl⟩ : syracuseStep 2355817 = 1766863) B1766863
theorem B1241727 : Blo 1240438 1241727 := bstep (se 1 (by rfl) ⟨931295, by rfl⟩ : syracuseStep 1241727 = 1862591) B1862591
theorem B1241831 : Blo 1240438 1241831 := bstep (se 1 (by rfl) ⟨931373, by rfl⟩ : syracuseStep 1241831 = 1862747) B1862747
theorem B2093951 : Blo 1240438 2093951 := bstep (se 1 (by rfl) ⟨1570463, by rfl⟩ : syracuseStep 2093951 = 3140927) B3140927
theorem B4191263 : Blo 1240438 4191263 := bstep (se 1 (by rfl) ⟨3143447, by rfl⟩ : syracuseStep 4191263 = 6286895) B6286895
theorem B1766891 : Blo 1240438 1766891 := bstep (se 1 (by rfl) ⟨1325168, by rfl⟩ : syracuseStep 1766891 = 2650337) B2650337
theorem B407598641 : Blo 1240438 407598641 := bstep (se 2 (by rfl) ⟨152849490, by rfl⟩ : syracuseStep 407598641 = 305698981) B305698981
theorem B8492735 : Blo 1240438 8492735 := bstep (se 1 (by rfl) ⟨6369551, by rfl⟩ : syracuseStep 8492735 = 12739103) B12739103
theorem B7075583 : Blo 1240438 7075583 := bstep (se 1 (by rfl) ⟨5306687, by rfl⟩ : syracuseStep 7075583 = 10613375) B10613375
theorem B4716751 : Blo 1240438 4716751 := bstep (se 1 (by rfl) ⟨3537563, by rfl⟩ : syracuseStep 4716751 = 7075127) B7075127
theorem B2358649 : Blo 1240438 2358649 := bstep (se 2 (by rfl) ⟨884493, by rfl⟩ : syracuseStep 2358649 = 1768987) B1768987
theorem B4775963 : Blo 1240438 4775963 := bstep (se 1 (by rfl) ⟨3581972, by rfl⟩ : syracuseStep 4775963 = 7163945) B7163945
theorem B108782041 : Blo 1240438 108782041 := bstep (se 2 (by rfl) ⟨40793265, by rfl⟩ : syracuseStep 108782041 = 81586531) B81586531
theorem B2794175 : Blo 1240438 2794175 := bstep (se 1 (by rfl) ⟨2095631, by rfl⟩ : syracuseStep 2794175 = 4191263) B4191263
theorem B6128635 : Blo 1240438 6128635 := bstep (se 1 (by rfl) ⟨4596476, by rfl⟩ : syracuseStep 6128635 = 9192953) B9192953
theorem B5661823 : Blo 1240438 5661823 := bstep (se 1 (by rfl) ⟨4246367, by rfl⟩ : syracuseStep 5661823 = 8492735) B8492735
theorem B4711709 : Blo 1240438 4711709 := bstep (se 3 (by rfl) ⟨883445, by rfl⟩ : syracuseStep 4711709 = 1766891) B1766891
theorem B1861673 : Blo 1240438 1861673 := bstep (se 2 (by rfl) ⟨698127, by rfl⟩ : syracuseStep 1861673 = 1396255) B1396255
theorem B51670183 : Blo 1240438 51670183 := bstep (se 1 (by rfl) ⟨38752637, by rfl⟩ : syracuseStep 51670183 = 77505275) B77505275
theorem B1395967 : Blo 1240438 1395967 := bstep (se 1 (by rfl) ⟨1046975, by rfl⟩ : syracuseStep 1395967 = 2093951) B2093951
theorem B26832235 : Blo 1240438 26832235 := bstep (se 1 (by rfl) ⟨20124176, by rfl⟩ : syracuseStep 26832235 = 40248353) B40248353
theorem B3141089 : Blo 1240438 3141089 := bstep (se 2 (by rfl) ⟨1177908, by rfl⟩ : syracuseStep 3141089 = 2355817) B2355817
theorem B1240731 : Blo 1240438 1240731 := bstep (se 1 (by rfl) ⟨930548, by rfl⟩ : syracuseStep 1240731 = 1861097) B1861097
theorem B271732427 : Blo 1240438 271732427 := bstep (se 1 (by rfl) ⟨203799320, by rfl⟩ : syracuseStep 271732427 = 407598641) B407598641
theorem B5665895 : Blo 1240438 5665895 := bstep (se 1 (by rfl) ⟨4249421, by rfl⟩ : syracuseStep 5665895 = 8498843) B8498843
theorem B6289001 : Blo 1240438 6289001 := bstep (se 2 (by rfl) ⟨2358375, by rfl⟩ : syracuseStep 6289001 = 4716751) B4716751
theorem B4717055 : Blo 1240438 4717055 := bstep (se 1 (by rfl) ⟨3537791, by rfl⟩ : syracuseStep 4717055 = 7075583) B7075583
theorem B3144865 : Blo 1240438 3144865 := bstep (se 2 (by rfl) ⟨1179324, by rfl⟩ : syracuseStep 3144865 = 2358649) B2358649
theorem B3777263 : Blo 1240438 3777263 := bstep (se 1 (by rfl) ⟨2832947, by rfl⟩ : syracuseStep 3777263 = 5665895) B5665895
theorem B1861289 : Blo 1240438 1861289 := bstep (se 2 (by rfl) ⟨697983, by rfl⟩ : syracuseStep 1861289 = 1395967) B1395967
theorem B35776313 : Blo 1240438 35776313 := bstep (se 2 (by rfl) ⟨13416117, by rfl⟩ : syracuseStep 35776313 = 26832235) B26832235
theorem B1862783 : Blo 1240438 1862783 := bstep (se 1 (by rfl) ⟨1397087, by rfl⟩ : syracuseStep 1862783 = 2794175) B2794175
theorem B145042721 : Blo 1240438 145042721 := bstep (se 2 (by rfl) ⟨54391020, by rfl⟩ : syracuseStep 145042721 = 108782041) B108782041
theorem B3141139 : Blo 1240438 3141139 := bstep (se 1 (by rfl) ⟨2355854, by rfl⟩ : syracuseStep 3141139 = 4711709) B4711709
theorem B8171513 : Blo 1240438 8171513 := bstep (se 2 (by rfl) ⟨3064317, by rfl⟩ : syracuseStep 8171513 = 6128635) B6128635
theorem B1241115 : Blo 1240438 1241115 := bstep (se 1 (by rfl) ⟨930836, by rfl⟩ : syracuseStep 1241115 = 1861673) B1861673
theorem B7549097 : Blo 1240438 7549097 := bstep (se 2 (by rfl) ⟨2830911, by rfl⟩ : syracuseStep 7549097 = 5661823) B5661823
theorem B2094059 : Blo 1240438 2094059 := bstep (se 1 (by rfl) ⟨1570544, by rfl⟩ : syracuseStep 2094059 = 3141089) B3141089
theorem B181154951 : Blo 1240438 181154951 := bstep (se 1 (by rfl) ⟨135866213, by rfl⟩ : syracuseStep 181154951 = 271732427) B271732427
theorem B12735901 : Blo 1240438 12735901 := bstep (se 3 (by rfl) ⟨2387981, by rfl⟩ : syracuseStep 12735901 = 4775963) B4775963
theorem B4192667 : Blo 1240438 4192667 := bstep (se 1 (by rfl) ⟨3144500, by rfl⟩ : syracuseStep 4192667 = 6289001) B6289001
theorem B4193153 : Blo 1240438 4193153 := bstep (se 2 (by rfl) ⟨1572432, by rfl⟩ : syracuseStep 4193153 = 3144865) B3144865
theorem B68893577 : Blo 1240438 68893577 := bstep (se 2 (by rfl) ⟨25835091, by rfl⟩ : syracuseStep 68893577 = 51670183) B51670183
theorem B3144703 : Blo 1240438 3144703 := bstep (se 1 (by rfl) ⟨2358527, by rfl⟩ : syracuseStep 3144703 = 4717055) B4717055
theorem B2795111 : Blo 1240438 2795111 := bstep (se 1 (by rfl) ⟨2096333, by rfl⟩ : syracuseStep 2795111 = 4192667) B4192667
theorem B2795435 : Blo 1240438 2795435 := bstep (se 1 (by rfl) ⟨2096576, by rfl⟩ : syracuseStep 2795435 = 4193153) B4193153
theorem B4188185 : Blo 1240438 4188185 := bstep (se 2 (by rfl) ⟨1570569, by rfl⟩ : syracuseStep 4188185 = 3141139) B3141139
theorem B20130925 : Blo 1240438 20130925 := bstep (se 3 (by rfl) ⟨3774548, by rfl⟩ : syracuseStep 20130925 = 7549097) B7549097
theorem B2518175 : Blo 1240438 2518175 := bstep (se 1 (by rfl) ⟨1888631, by rfl⟩ : syracuseStep 2518175 = 3777263) B3777263
theorem B1396039 : Blo 1240438 1396039 := bstep (se 1 (by rfl) ⟨1047029, by rfl⟩ : syracuseStep 1396039 = 2094059) B2094059
theorem B120769967 : Blo 1240438 120769967 := bstep (se 1 (by rfl) ⟨90577475, by rfl⟩ : syracuseStep 120769967 = 181154951) B181154951
theorem B1240859 : Blo 1240438 1240859 := bstep (se 1 (by rfl) ⟨930644, by rfl⟩ : syracuseStep 1240859 = 1861289) B1861289
theorem B23850875 : Blo 1240438 23850875 := bstep (se 1 (by rfl) ⟨17888156, by rfl⟩ : syracuseStep 23850875 = 35776313) B35776313
theorem B45929051 : Blo 1240438 45929051 := bstep (se 1 (by rfl) ⟨34446788, by rfl⟩ : syracuseStep 45929051 = 68893577) B68893577
theorem B1241855 : Blo 1240438 1241855 := bstep (se 1 (by rfl) ⟨931391, by rfl⟩ : syracuseStep 1241855 = 1862783) B1862783
theorem B96695147 : Blo 1240438 96695147 := bstep (se 1 (by rfl) ⟨72521360, by rfl⟩ : syracuseStep 96695147 = 145042721) B145042721
theorem B4192937 : Blo 1240438 4192937 := bstep (se 2 (by rfl) ⟨1572351, by rfl⟩ : syracuseStep 4192937 = 3144703) B3144703
theorem B16981201 : Blo 1240438 16981201 := bstep (se 2 (by rfl) ⟨6367950, by rfl⟩ : syracuseStep 16981201 = 12735901) B12735901
theorem B5447675 : Blo 1240438 5447675 := bstep (se 1 (by rfl) ⟨4085756, by rfl⟩ : syracuseStep 5447675 = 8171513) B8171513
theorem B1861385 : Blo 1240438 1861385 := bstep (se 2 (by rfl) ⟨698019, by rfl⟩ : syracuseStep 1861385 = 1396039) B1396039
theorem B2795291 : Blo 1240438 2795291 := bstep (se 1 (by rfl) ⟨2096468, by rfl⟩ : syracuseStep 2795291 = 4192937) B4192937
theorem B257853725 : Blo 1240438 257853725 := bstep (se 3 (by rfl) ⟨48347573, by rfl⟩ : syracuseStep 257853725 = 96695147) B96695147
theorem B80513311 : Blo 1240438 80513311 := bstep (se 1 (by rfl) ⟨60384983, by rfl⟩ : syracuseStep 80513311 = 120769967) B120769967
theorem B14527133 : Blo 1240438 14527133 := bstep (se 3 (by rfl) ⟨2723837, by rfl⟩ : syracuseStep 14527133 = 5447675) B5447675
theorem B1863407 : Blo 1240438 1863407 := bstep (se 1 (by rfl) ⟨1397555, by rfl⟩ : syracuseStep 1863407 = 2795111) B2795111
theorem B1863623 : Blo 1240438 1863623 := bstep (se 1 (by rfl) ⟨1397717, by rfl⟩ : syracuseStep 1863623 = 2795435) B2795435
theorem B26841233 : Blo 1240438 26841233 := bstep (se 2 (by rfl) ⟨10065462, by rfl⟩ : syracuseStep 26841233 = 20130925) B20130925
theorem B30619367 : Blo 1240438 30619367 := bstep (se 1 (by rfl) ⟨22964525, by rfl⟩ : syracuseStep 30619367 = 45929051) B45929051
theorem B6715133 : Blo 1240438 6715133 := bstep (se 3 (by rfl) ⟨1259087, by rfl⟩ : syracuseStep 6715133 = 2518175) B2518175
theorem B2792123 : Blo 1240438 2792123 := bstep (se 1 (by rfl) ⟨2094092, by rfl⟩ : syracuseStep 2792123 = 4188185) B4188185
theorem B22641601 : Blo 1240438 22641601 := bstep (se 2 (by rfl) ⟨8490600, by rfl⟩ : syracuseStep 22641601 = 16981201) B16981201
theorem B15900583 : Blo 1240438 15900583 := bstep (se 1 (by rfl) ⟨11925437, by rfl⟩ : syracuseStep 15900583 = 23850875) B23850875
theorem B30188801 : Blo 1240438 30188801 := bstep (se 2 (by rfl) ⟨11320800, by rfl⟩ : syracuseStep 30188801 = 22641601) B22641601
theorem B171902483 : Blo 1240438 171902483 := bstep (se 1 (by rfl) ⟨128926862, by rfl⟩ : syracuseStep 171902483 = 257853725) B257853725
theorem B9684755 : Blo 1240438 9684755 := bstep (se 1 (by rfl) ⟨7263566, by rfl⟩ : syracuseStep 9684755 = 14527133) B14527133
theorem B1861415 : Blo 1240438 1861415 := bstep (se 1 (by rfl) ⟨1396061, by rfl⟩ : syracuseStep 1861415 = 2792123) B2792123
theorem B17894155 : Blo 1240438 17894155 := bstep (se 1 (by rfl) ⟨13420616, by rfl⟩ : syracuseStep 17894155 = 26841233) B26841233
theorem B107351081 : Blo 1240438 107351081 := bstep (se 2 (by rfl) ⟨40256655, by rfl⟩ : syracuseStep 107351081 = 80513311) B80513311
theorem B4476755 : Blo 1240438 4476755 := bstep (se 1 (by rfl) ⟨3357566, by rfl⟩ : syracuseStep 4476755 = 6715133) B6715133
theorem B1240923 : Blo 1240438 1240923 := bstep (se 1 (by rfl) ⟨930692, by rfl⟩ : syracuseStep 1240923 = 1861385) B1861385
theorem B1863527 : Blo 1240438 1863527 := bstep (se 1 (by rfl) ⟨1397645, by rfl⟩ : syracuseStep 1863527 = 2795291) B2795291
theorem B1242271 : Blo 1240438 1242271 := bstep (se 1 (by rfl) ⟨931703, by rfl⟩ : syracuseStep 1242271 = 1863407) B1863407
theorem B1242415 : Blo 1240438 1242415 := bstep (se 1 (by rfl) ⟨931811, by rfl⟩ : syracuseStep 1242415 = 1863623) B1863623
theorem B20412911 : Blo 1240438 20412911 := bstep (se 1 (by rfl) ⟨15309683, by rfl⟩ : syracuseStep 20412911 = 30619367) B30619367
theorem B21200777 : Blo 1240438 21200777 := bstep (se 2 (by rfl) ⟨7950291, by rfl⟩ : syracuseStep 21200777 = 15900583) B15900583
theorem B80503469 : Blo 1240438 80503469 := bstep (se 3 (by rfl) ⟨15094400, by rfl⟩ : syracuseStep 80503469 = 30188801) B30188801
theorem B6456503 : Blo 1240438 6456503 := bstep (se 1 (by rfl) ⟨4842377, by rfl⟩ : syracuseStep 6456503 = 9684755) B9684755
theorem B13608607 : Blo 1240438 13608607 := bstep (se 1 (by rfl) ⟨10206455, by rfl⟩ : syracuseStep 13608607 = 20412911) B20412911
theorem B71567387 : Blo 1240438 71567387 := bstep (se 1 (by rfl) ⟨53675540, by rfl⟩ : syracuseStep 71567387 = 107351081) B107351081
theorem B11938013 : Blo 1240438 11938013 := bstep (se 3 (by rfl) ⟨2238377, by rfl⟩ : syracuseStep 11938013 = 4476755) B4476755
theorem B14133851 : Blo 1240438 14133851 := bstep (se 1 (by rfl) ⟨10600388, by rfl⟩ : syracuseStep 14133851 = 21200777) B21200777
theorem B114601655 : Blo 1240438 114601655 := bstep (se 1 (by rfl) ⟨85951241, by rfl⟩ : syracuseStep 114601655 = 171902483) B171902483
theorem B23858873 : Blo 1240438 23858873 := bstep (se 2 (by rfl) ⟨8947077, by rfl⟩ : syracuseStep 23858873 = 17894155) B17894155
theorem B1240943 : Blo 1240438 1240943 := bstep (se 1 (by rfl) ⟨930707, by rfl⟩ : syracuseStep 1240943 = 1861415) B1861415
theorem B1242351 : Blo 1240438 1242351 := bstep (se 1 (by rfl) ⟨931763, by rfl⟩ : syracuseStep 1242351 = 1863527) B1863527
theorem B47711591 : Blo 1240438 47711591 := bstep (se 1 (by rfl) ⟨35783693, by rfl⟩ : syracuseStep 47711591 = 71567387) B71567387
theorem B9422567 : Blo 1240438 9422567 := bstep (se 1 (by rfl) ⟨7066925, by rfl⟩ : syracuseStep 9422567 = 14133851) B14133851
theorem B76401103 : Blo 1240438 76401103 := bstep (se 1 (by rfl) ⟨57300827, by rfl⟩ : syracuseStep 76401103 = 114601655) B114601655
theorem B53668979 : Blo 1240438 53668979 := bstep (se 1 (by rfl) ⟨40251734, by rfl⟩ : syracuseStep 53668979 = 80503469) B80503469
theorem B4304335 : Blo 1240438 4304335 := bstep (se 1 (by rfl) ⟨3228251, by rfl⟩ : syracuseStep 4304335 = 6456503) B6456503
theorem B7958675 : Blo 1240438 7958675 := bstep (se 1 (by rfl) ⟨5969006, by rfl⟩ : syracuseStep 7958675 = 11938013) B11938013
theorem B15905915 : Blo 1240438 15905915 := bstep (se 1 (by rfl) ⟨11929436, by rfl⟩ : syracuseStep 15905915 = 23858873) B23858873
theorem B18144809 : Blo 1240438 18144809 := bstep (se 2 (by rfl) ⟨6804303, by rfl⟩ : syracuseStep 18144809 = 13608607) B13608607
theorem B101868137 : Blo 1240438 101868137 := bstep (se 2 (by rfl) ⟨38200551, by rfl⟩ : syracuseStep 101868137 = 76401103) B76401103
theorem B10603943 : Blo 1240438 10603943 := bstep (se 1 (by rfl) ⟨7952957, by rfl⟩ : syracuseStep 10603943 = 15905915) B15905915
theorem B5739113 : Blo 1240438 5739113 := bstep (se 2 (by rfl) ⟨2152167, by rfl⟩ : syracuseStep 5739113 = 4304335) B4304335
theorem B35779319 : Blo 1240438 35779319 := bstep (se 1 (by rfl) ⟨26834489, by rfl⟩ : syracuseStep 35779319 = 53668979) B53668979
theorem B12096539 : Blo 1240438 12096539 := bstep (se 1 (by rfl) ⟨9072404, by rfl⟩ : syracuseStep 12096539 = 18144809) B18144809
theorem B5305783 : Blo 1240438 5305783 := bstep (se 1 (by rfl) ⟨3979337, by rfl⟩ : syracuseStep 5305783 = 7958675) B7958675
theorem B31807727 : Blo 1240438 31807727 := bstep (se 1 (by rfl) ⟨23855795, by rfl⟩ : syracuseStep 31807727 = 47711591) B47711591
theorem B6281711 : Blo 1240438 6281711 := bstep (se 1 (by rfl) ⟨4711283, by rfl⟩ : syracuseStep 6281711 = 9422567) B9422567
theorem B67912091 : Blo 1240438 67912091 := bstep (se 1 (by rfl) ⟨50934068, by rfl⟩ : syracuseStep 67912091 = 101868137) B101868137
theorem B3826075 : Blo 1240438 3826075 := bstep (se 1 (by rfl) ⟨2869556, by rfl⟩ : syracuseStep 3826075 = 5739113) B5739113
theorem B4187807 : Blo 1240438 4187807 := bstep (se 1 (by rfl) ⟨3140855, by rfl⟩ : syracuseStep 4187807 = 6281711) B6281711
theorem B8064359 : Blo 1240438 8064359 := bstep (se 1 (by rfl) ⟨6048269, by rfl⟩ : syracuseStep 8064359 = 12096539) B12096539
theorem B21205151 : Blo 1240438 21205151 := bstep (se 1 (by rfl) ⟨15903863, by rfl⟩ : syracuseStep 21205151 = 31807727) B31807727
theorem B7074377 : Blo 1240438 7074377 := bstep (se 2 (by rfl) ⟨2652891, by rfl⟩ : syracuseStep 7074377 = 5305783) B5305783
theorem B23852879 : Blo 1240438 23852879 := bstep (se 1 (by rfl) ⟨17889659, by rfl⟩ : syracuseStep 23852879 = 35779319) B35779319
theorem B7069295 : Blo 1240438 7069295 := bstep (se 1 (by rfl) ⟨5301971, by rfl⟩ : syracuseStep 7069295 = 10603943) B10603943
theorem B15901919 : Blo 1240438 15901919 := bstep (se 1 (by rfl) ⟨11926439, by rfl⟩ : syracuseStep 15901919 = 23852879) B23852879
theorem B5376239 : Blo 1240438 5376239 := bstep (se 1 (by rfl) ⟨4032179, by rfl⟩ : syracuseStep 5376239 = 8064359) B8064359
theorem B4712863 : Blo 1240438 4712863 := bstep (se 1 (by rfl) ⟨3534647, by rfl⟩ : syracuseStep 4712863 = 7069295) B7069295
theorem B14136767 : Blo 1240438 14136767 := bstep (se 1 (by rfl) ⟨10602575, by rfl⟩ : syracuseStep 14136767 = 21205151) B21205151
theorem B45274727 : Blo 1240438 45274727 := bstep (se 1 (by rfl) ⟨33956045, by rfl⟩ : syracuseStep 45274727 = 67912091) B67912091
theorem B4716251 : Blo 1240438 4716251 := bstep (se 1 (by rfl) ⟨3537188, by rfl⟩ : syracuseStep 4716251 = 7074377) B7074377
theorem B5101433 : Blo 1240438 5101433 := bstep (se 2 (by rfl) ⟨1913037, by rfl⟩ : syracuseStep 5101433 = 3826075) B3826075
theorem B2791871 : Blo 1240438 2791871 := bstep (se 1 (by rfl) ⟨2093903, by rfl⟩ : syracuseStep 2791871 = 4187807) B4187807
theorem B6283817 : Blo 1240438 6283817 := bstep (se 2 (by rfl) ⟨2356431, by rfl⟩ : syracuseStep 6283817 = 4712863) B4712863
theorem B10601279 : Blo 1240438 10601279 := bstep (se 1 (by rfl) ⟨7950959, by rfl⟩ : syracuseStep 10601279 = 15901919) B15901919
theorem B3400955 : Blo 1240438 3400955 := bstep (se 1 (by rfl) ⟨2550716, by rfl⟩ : syracuseStep 3400955 = 5101433) B5101433
theorem B1861247 : Blo 1240438 1861247 := bstep (se 1 (by rfl) ⟨1395935, by rfl⟩ : syracuseStep 1861247 = 2791871) B2791871
theorem B9424511 : Blo 1240438 9424511 := bstep (se 1 (by rfl) ⟨7068383, by rfl⟩ : syracuseStep 9424511 = 14136767) B14136767
theorem B3584159 : Blo 1240438 3584159 := bstep (se 1 (by rfl) ⟨2688119, by rfl⟩ : syracuseStep 3584159 = 5376239) B5376239
theorem B3144167 : Blo 1240438 3144167 := bstep (se 1 (by rfl) ⟨2358125, by rfl⟩ : syracuseStep 3144167 = 4716251) B4716251
theorem B120732605 : Blo 1240438 120732605 := bstep (se 3 (by rfl) ⟨22637363, by rfl⟩ : syracuseStep 120732605 = 45274727) B45274727
theorem B80488403 : Blo 1240438 80488403 := bstep (se 1 (by rfl) ⟨60366302, by rfl⟩ : syracuseStep 80488403 = 120732605) B120732605
theorem B4189211 : Blo 1240438 4189211 := bstep (se 1 (by rfl) ⟨3141908, by rfl⟩ : syracuseStep 4189211 = 6283817) B6283817
theorem B1240831 : Blo 1240438 1240831 := bstep (se 1 (by rfl) ⟨930623, by rfl⟩ : syracuseStep 1240831 = 1861247) B1861247
theorem B2389439 : Blo 1240438 2389439 := bstep (se 1 (by rfl) ⟨1792079, by rfl⟩ : syracuseStep 2389439 = 3584159) B3584159
theorem B7067519 : Blo 1240438 7067519 := bstep (se 1 (by rfl) ⟨5300639, by rfl⟩ : syracuseStep 7067519 = 10601279) B10601279
theorem B2267303 : Blo 1240438 2267303 := bstep (se 1 (by rfl) ⟨1700477, by rfl⟩ : syracuseStep 2267303 = 3400955) B3400955
theorem B2096111 : Blo 1240438 2096111 := bstep (se 1 (by rfl) ⟨1572083, by rfl⟩ : syracuseStep 2096111 = 3144167) B3144167
theorem B6283007 : Blo 1240438 6283007 := bstep (se 1 (by rfl) ⟨4712255, by rfl⟩ : syracuseStep 6283007 = 9424511) B9424511
theorem B4711679 : Blo 1240438 4711679 := bstep (se 1 (by rfl) ⟨3533759, by rfl⟩ : syracuseStep 4711679 = 7067519) B7067519
theorem B53658935 : Blo 1240438 53658935 := bstep (se 1 (by rfl) ⟨40244201, by rfl⟩ : syracuseStep 53658935 = 80488403) B80488403
theorem B24184565 : Blo 1240438 24184565 := bstep (se 5 (by rfl) ⟨1133651, by rfl⟩ : syracuseStep 24184565 = 2267303) B2267303
theorem B4188671 : Blo 1240438 4188671 := bstep (se 1 (by rfl) ⟨3141503, by rfl⟩ : syracuseStep 4188671 = 6283007) B6283007
theorem B1592959 : Blo 1240438 1592959 := bstep (se 1 (by rfl) ⟨1194719, by rfl⟩ : syracuseStep 1592959 = 2389439) B2389439
theorem B1397407 : Blo 1240438 1397407 := bstep (se 1 (by rfl) ⟨1048055, by rfl⟩ : syracuseStep 1397407 = 2096111) B2096111
theorem B2792807 : Blo 1240438 2792807 := bstep (se 1 (by rfl) ⟨2094605, by rfl⟩ : syracuseStep 2792807 = 4189211) B4189211
theorem B16123043 : Blo 1240438 16123043 := bstep (se 1 (by rfl) ⟨12092282, by rfl⟩ : syracuseStep 16123043 = 24184565) B24184565
theorem B2123945 : Blo 1240438 2123945 := bstep (se 2 (by rfl) ⟨796479, by rfl⟩ : syracuseStep 2123945 = 1592959) B1592959
theorem B1861871 : Blo 1240438 1861871 := bstep (se 1 (by rfl) ⟨1396403, by rfl⟩ : syracuseStep 1861871 = 2792807) B2792807
theorem B3141119 : Blo 1240438 3141119 := bstep (se 1 (by rfl) ⟨2355839, by rfl⟩ : syracuseStep 3141119 = 4711679) B4711679
theorem B1863209 : Blo 1240438 1863209 := bstep (se 2 (by rfl) ⟨698703, by rfl⟩ : syracuseStep 1863209 = 1397407) B1397407
theorem B35772623 : Blo 1240438 35772623 := bstep (se 1 (by rfl) ⟨26829467, by rfl⟩ : syracuseStep 35772623 = 53658935) B53658935
theorem B2792447 : Blo 1240438 2792447 := bstep (se 1 (by rfl) ⟨2094335, by rfl⟩ : syracuseStep 2792447 = 4188671) B4188671
theorem B10748695 : Blo 1240438 10748695 := bstep (se 1 (by rfl) ⟨8061521, by rfl⟩ : syracuseStep 10748695 = 16123043) B16123043
theorem B23848415 : Blo 1240438 23848415 := bstep (se 1 (by rfl) ⟨17886311, by rfl⟩ : syracuseStep 23848415 = 35772623) B35772623
theorem B1861631 : Blo 1240438 1861631 := bstep (se 1 (by rfl) ⟨1396223, by rfl⟩ : syracuseStep 1861631 = 2792447) B2792447
theorem B1241247 : Blo 1240438 1241247 := bstep (se 1 (by rfl) ⟨930935, by rfl⟩ : syracuseStep 1241247 = 1861871) B1861871
theorem B2094079 : Blo 1240438 2094079 := bstep (se 1 (by rfl) ⟨1570559, by rfl⟩ : syracuseStep 2094079 = 3141119) B3141119
theorem B1242139 : Blo 1240438 1242139 := bstep (se 1 (by rfl) ⟨931604, by rfl⟩ : syracuseStep 1242139 = 1863209) B1863209
theorem B1415963 : Blo 1240438 1415963 := bstep (se 1 (by rfl) ⟨1061972, by rfl⟩ : syracuseStep 1415963 = 2123945) B2123945
theorem B14331593 : Blo 1240438 14331593 := bstep (se 2 (by rfl) ⟨5374347, by rfl⟩ : syracuseStep 14331593 = 10748695) B10748695
theorem B1241087 : Blo 1240438 1241087 := bstep (se 1 (by rfl) ⟨930815, by rfl⟩ : syracuseStep 1241087 = 1861631) B1861631
theorem B15898943 : Blo 1240438 15898943 := bstep (se 1 (by rfl) ⟨11924207, by rfl⟩ : syracuseStep 15898943 = 23848415) B23848415
theorem B2792105 : Blo 1240438 2792105 := bstep (se 2 (by rfl) ⟨1047039, by rfl⟩ : syracuseStep 2792105 = 2094079) B2094079
theorem B3775901 : Blo 1240438 3775901 := bstep (se 3 (by rfl) ⟨707981, by rfl⟩ : syracuseStep 3775901 = 1415963) B1415963
theorem B10069069 : Blo 1240438 10069069 := bstep (se 3 (by rfl) ⟨1887950, by rfl⟩ : syracuseStep 10069069 = 3775901) B3775901
theorem B1861403 : Blo 1240438 1861403 := bstep (se 1 (by rfl) ⟨1396052, by rfl⟩ : syracuseStep 1861403 = 2792105) B2792105
theorem B9554395 : Blo 1240438 9554395 := bstep (se 1 (by rfl) ⟨7165796, by rfl⟩ : syracuseStep 9554395 = 14331593) B14331593
theorem B10599295 : Blo 1240438 10599295 := bstep (se 1 (by rfl) ⟨7949471, by rfl⟩ : syracuseStep 10599295 = 15898943) B15898943
theorem B12739193 : Blo 1240438 12739193 := bstep (se 2 (by rfl) ⟨4777197, by rfl⟩ : syracuseStep 12739193 = 9554395) B9554395
theorem B14132393 : Blo 1240438 14132393 := bstep (se 2 (by rfl) ⟨5299647, by rfl⟩ : syracuseStep 14132393 = 10599295) B10599295
theorem B1240935 : Blo 1240438 1240935 := bstep (se 1 (by rfl) ⟨930701, by rfl⟩ : syracuseStep 1240935 = 1861403) B1861403
theorem B13425425 : Blo 1240438 13425425 := bstep (se 2 (by rfl) ⟨5034534, by rfl⟩ : syracuseStep 13425425 = 10069069) B10069069
theorem B9421595 : Blo 1240438 9421595 := bstep (se 1 (by rfl) ⟨7066196, by rfl⟩ : syracuseStep 9421595 = 14132393) B14132393
theorem B8950283 : Blo 1240438 8950283 := bstep (se 1 (by rfl) ⟨6712712, by rfl⟩ : syracuseStep 8950283 = 13425425) B13425425
theorem B8492795 : Blo 1240438 8492795 := bstep (se 1 (by rfl) ⟨6369596, by rfl⟩ : syracuseStep 8492795 = 12739193) B12739193
theorem B5661863 : Blo 1240438 5661863 := bstep (se 1 (by rfl) ⟨4246397, by rfl⟩ : syracuseStep 5661863 = 8492795) B8492795
theorem B5966855 : Blo 1240438 5966855 := bstep (se 1 (by rfl) ⟨4475141, by rfl⟩ : syracuseStep 5966855 = 8950283) B8950283
theorem B6281063 : Blo 1240438 6281063 := bstep (se 1 (by rfl) ⟨4710797, by rfl⟩ : syracuseStep 6281063 = 9421595) B9421595
theorem B4187375 : Blo 1240438 4187375 := bstep (se 1 (by rfl) ⟨3140531, by rfl⟩ : syracuseStep 4187375 = 6281063) B6281063
theorem B3977903 : Blo 1240438 3977903 := bstep (se 1 (by rfl) ⟨2983427, by rfl⟩ : syracuseStep 3977903 = 5966855) B5966855
theorem B3774575 : Blo 1240438 3774575 := bstep (se 1 (by rfl) ⟨2830931, by rfl⟩ : syracuseStep 3774575 = 5661863) B5661863
theorem B2516383 : Blo 1240438 2516383 := bstep (se 1 (by rfl) ⟨1887287, by rfl⟩ : syracuseStep 2516383 = 3774575) B3774575
theorem B2651935 : Blo 1240438 2651935 := bstep (se 1 (by rfl) ⟨1988951, by rfl⟩ : syracuseStep 2651935 = 3977903) B3977903
theorem B2791583 : Blo 1240438 2791583 := bstep (se 1 (by rfl) ⟨2093687, by rfl⟩ : syracuseStep 2791583 = 4187375) B4187375
theorem B1861055 : Blo 1240438 1861055 := bstep (se 1 (by rfl) ⟨1395791, by rfl⟩ : syracuseStep 1861055 = 2791583) B2791583
theorem B3355177 : Blo 1240438 3355177 := bstep (se 2 (by rfl) ⟨1258191, by rfl⟩ : syracuseStep 3355177 = 2516383) B2516383
theorem B3535913 : Blo 1240438 3535913 := bstep (se 2 (by rfl) ⟨1325967, by rfl⟩ : syracuseStep 3535913 = 2651935) B2651935
theorem B4473569 : Blo 1240438 4473569 := bstep (se 2 (by rfl) ⟨1677588, by rfl⟩ : syracuseStep 4473569 = 3355177) B3355177
theorem B1240703 : Blo 1240438 1240703 := bstep (se 1 (by rfl) ⟨930527, by rfl⟩ : syracuseStep 1240703 = 1861055) B1861055
theorem B2357275 : Blo 1240438 2357275 := bstep (se 1 (by rfl) ⟨1767956, by rfl⟩ : syracuseStep 2357275 = 3535913) B3535913
theorem B11929517 : Blo 1240438 11929517 := bstep (se 3 (by rfl) ⟨2236784, by rfl⟩ : syracuseStep 11929517 = 4473569) B4473569
theorem B3143033 : Blo 1240438 3143033 := bstep (se 2 (by rfl) ⟨1178637, by rfl⟩ : syracuseStep 3143033 = 2357275) B2357275
theorem B2095355 : Blo 1240438 2095355 := bstep (se 1 (by rfl) ⟨1571516, by rfl⟩ : syracuseStep 2095355 = 3143033) B3143033
theorem B7953011 : Blo 1240438 7953011 := bstep (se 1 (by rfl) ⟨5964758, by rfl⟩ : syracuseStep 7953011 = 11929517) B11929517
theorem B5302007 : Blo 1240438 5302007 := bstep (se 1 (by rfl) ⟨3976505, by rfl⟩ : syracuseStep 5302007 = 7953011) B7953011
theorem B1396903 : Blo 1240438 1396903 := bstep (se 1 (by rfl) ⟨1047677, by rfl⟩ : syracuseStep 1396903 = 2095355) B2095355
theorem B1862537 : Blo 1240438 1862537 := bstep (se 2 (by rfl) ⟨698451, by rfl⟩ : syracuseStep 1862537 = 1396903) B1396903
theorem B3534671 : Blo 1240438 3534671 := bstep (se 1 (by rfl) ⟨2651003, by rfl⟩ : syracuseStep 3534671 = 5302007) B5302007
theorem B1241691 : Blo 1240438 1241691 := bstep (se 1 (by rfl) ⟨931268, by rfl⟩ : syracuseStep 1241691 = 1862537) B1862537
theorem B2356447 : Blo 1240438 2356447 := bstep (se 1 (by rfl) ⟨1767335, by rfl⟩ : syracuseStep 2356447 = 3534671) B3534671
theorem B3141929 : Blo 1240438 3141929 := bstep (se 2 (by rfl) ⟨1178223, by rfl⟩ : syracuseStep 3141929 = 2356447) B2356447
theorem B2094619 : Blo 1240438 2094619 := bstep (se 1 (by rfl) ⟨1570964, by rfl⟩ : syracuseStep 2094619 = 3141929) B3141929
theorem B2792825 : Blo 1240438 2792825 := bstep (se 2 (by rfl) ⟨1047309, by rfl⟩ : syracuseStep 2792825 = 2094619) B2094619
theorem B1861883 : Blo 1240438 1861883 := bstep (se 1 (by rfl) ⟨1396412, by rfl⟩ : syracuseStep 1861883 = 2792825) B2792825
theorem B1241255 : Blo 1240438 1241255 := bstep (se 1 (by rfl) ⟨930941, by rfl⟩ : syracuseStep 1241255 = 1861883) B1861883

theorem C0 (j : ℕ) (h1 : 310109 ≤ j) (h2 : j ≤ 310608) : Blo 1240438 (4 * j + 3) := by
  interval_cases j
  · exact B1240439
  · exact B1240443
  · exact B1240447
  · exact B1240451
  · exact B1240455
  · exact B1240459
  · exact B1240463
  · exact B1240467
  · exact B1240471
  · exact B1240475
  · exact B1240479
  · exact B1240483
  · exact B1240487
  · exact B1240491
  · exact B1240495
  · exact B1240499
  · exact B1240503
  · exact B1240507
  · exact B1240511
  · exact B1240515
  · exact B1240519
  · exact B1240523
  · exact B1240527
  · exact B1240531
  · exact B1240535
  · exact B1240539
  · exact B1240543
  · exact B1240547
  · exact B1240551
  · exact B1240555
  · exact B1240559
  · exact B1240563
  · exact B1240567
  · exact B1240571
  · exact B1240575
  · exact B1240579
  · exact B1240583
  · exact B1240587
  · exact B1240591
  · exact B1240595
  · exact B1240599
  · exact B1240603
  · exact B1240607
  · exact B1240611
  · exact B1240615
  · exact B1240619
  · exact B1240623
  · exact B1240627
  · exact B1240631
  · exact B1240635
  · exact B1240639
  · exact B1240643
  · exact B1240647
  · exact B1240651
  · exact B1240655
  · exact B1240659
  · exact B1240663
  · exact B1240667
  · exact B1240671
  · exact B1240675
  · exact B1240679
  · exact B1240683
  · exact B1240687
  · exact B1240691
  · exact B1240695
  · exact B1240699
  · exact B1240703
  · exact B1240707
  · exact B1240711
  · exact B1240715
  · exact B1240719
  · exact B1240723
  · exact B1240727
  · exact B1240731
  · exact B1240735
  · exact B1240739
  · exact B1240743
  · exact B1240747
  · exact B1240751
  · exact B1240755
  · exact B1240759
  · exact B1240763
  · exact B1240767
  · exact B1240771
  · exact B1240775
  · exact B1240779
  · exact B1240783
  · exact B1240787
  · exact B1240791
  · exact B1240795
  · exact B1240799
  · exact B1240803
  · exact B1240807
  · exact B1240811
  · exact B1240815
  · exact B1240819
  · exact B1240823
  · exact B1240827
  · exact B1240831
  · exact B1240835
  · exact B1240839
  · exact B1240843
  · exact B1240847
  · exact B1240851
  · exact B1240855
  · exact B1240859
  · exact B1240863
  · exact B1240867
  · exact B1240871
  · exact B1240875
  · exact B1240879
  · exact B1240883
  · exact B1240887
  · exact B1240891
  · exact B1240895
  · exact B1240899
  · exact B1240903
  · exact B1240907
  · exact B1240911
  · exact B1240915
  · exact B1240919
  · exact B1240923
  · exact B1240927
  · exact B1240931
  · exact B1240935
  · exact B1240939
  · exact B1240943
  · exact B1240947
  · exact B1240951
  · exact B1240955
  · exact B1240959
  · exact B1240963
  · exact B1240967
  · exact B1240971
  · exact B1240975
  · exact B1240979
  · exact B1240983
  · exact B1240987
  · exact B1240991
  · exact B1240995
  · exact B1240999
  · exact B1241003
  · exact B1241007
  · exact B1241011
  · exact B1241015
  · exact B1241019
  · exact B1241023
  · exact B1241027
  · exact B1241031
  · exact B1241035
  · exact B1241039
  · exact B1241043
  · exact B1241047
  · exact B1241051
  · exact B1241055
  · exact B1241059
  · exact B1241063
  · exact B1241067
  · exact B1241071
  · exact B1241075
  · exact B1241079
  · exact B1241083
  · exact B1241087
  · exact B1241091
  · exact B1241095
  · exact B1241099
  · exact B1241103
  · exact B1241107
  · exact B1241111
  · exact B1241115
  · exact B1241119
  · exact B1241123
  · exact B1241127
  · exact B1241131
  · exact B1241135
  · exact B1241139
  · exact B1241143
  · exact B1241147
  · exact B1241151
  · exact B1241155
  · exact B1241159
  · exact B1241163
  · exact B1241167
  · exact B1241171
  · exact B1241175
  · exact B1241179
  · exact B1241183
  · exact B1241187
  · exact B1241191
  · exact B1241195
  · exact B1241199
  · exact B1241203
  · exact B1241207
  · exact B1241211
  · exact B1241215
  · exact B1241219
  · exact B1241223
  · exact B1241227
  · exact B1241231
  · exact B1241235
  · exact B1241239
  · exact B1241243
  · exact B1241247
  · exact B1241251
  · exact B1241255
  · exact B1241259
  · exact B1241263
  · exact B1241267
  · exact B1241271
  · exact B1241275
  · exact B1241279
  · exact B1241283
  · exact B1241287
  · exact B1241291
  · exact B1241295
  · exact B1241299
  · exact B1241303
  · exact B1241307
  · exact B1241311
  · exact B1241315
  · exact B1241319
  · exact B1241323
  · exact B1241327
  · exact B1241331
  · exact B1241335
  · exact B1241339
  · exact B1241343
  · exact B1241347
  · exact B1241351
  · exact B1241355
  · exact B1241359
  · exact B1241363
  · exact B1241367
  · exact B1241371
  · exact B1241375
  · exact B1241379
  · exact B1241383
  · exact B1241387
  · exact B1241391
  · exact B1241395
  · exact B1241399
  · exact B1241403
  · exact B1241407
  · exact B1241411
  · exact B1241415
  · exact B1241419
  · exact B1241423
  · exact B1241427
  · exact B1241431
  · exact B1241435
  · exact B1241439
  · exact B1241443
  · exact B1241447
  · exact B1241451
  · exact B1241455
  · exact B1241459
  · exact B1241463
  · exact B1241467
  · exact B1241471
  · exact B1241475
  · exact B1241479
  · exact B1241483
  · exact B1241487
  · exact B1241491
  · exact B1241495
  · exact B1241499
  · exact B1241503
  · exact B1241507
  · exact B1241511
  · exact B1241515
  · exact B1241519
  · exact B1241523
  · exact B1241527
  · exact B1241531
  · exact B1241535
  · exact B1241539
  · exact B1241543
  · exact B1241547
  · exact B1241551
  · exact B1241555
  · exact B1241559
  · exact B1241563
  · exact B1241567
  · exact B1241571
  · exact B1241575
  · exact B1241579
  · exact B1241583
  · exact B1241587
  · exact B1241591
  · exact B1241595
  · exact B1241599
  · exact B1241603
  · exact B1241607
  · exact B1241611
  · exact B1241615
  · exact B1241619
  · exact B1241623
  · exact B1241627
  · exact B1241631
  · exact B1241635
  · exact B1241639
  · exact B1241643
  · exact B1241647
  · exact B1241651
  · exact B1241655
  · exact B1241659
  · exact B1241663
  · exact B1241667
  · exact B1241671
  · exact B1241675
  · exact B1241679
  · exact B1241683
  · exact B1241687
  · exact B1241691
  · exact B1241695
  · exact B1241699
  · exact B1241703
  · exact B1241707
  · exact B1241711
  · exact B1241715
  · exact B1241719
  · exact B1241723
  · exact B1241727
  · exact B1241731
  · exact B1241735
  · exact B1241739
  · exact B1241743
  · exact B1241747
  · exact B1241751
  · exact B1241755
  · exact B1241759
  · exact B1241763
  · exact B1241767
  · exact B1241771
  · exact B1241775
  · exact B1241779
  · exact B1241783
  · exact B1241787
  · exact B1241791
  · exact B1241795
  · exact B1241799
  · exact B1241803
  · exact B1241807
  · exact B1241811
  · exact B1241815
  · exact B1241819
  · exact B1241823
  · exact B1241827
  · exact B1241831
  · exact B1241835
  · exact B1241839
  · exact B1241843
  · exact B1241847
  · exact B1241851
  · exact B1241855
  · exact B1241859
  · exact B1241863
  · exact B1241867
  · exact B1241871
  · exact B1241875
  · exact B1241879
  · exact B1241883
  · exact B1241887
  · exact B1241891
  · exact B1241895
  · exact B1241899
  · exact B1241903
  · exact B1241907
  · exact B1241911
  · exact B1241915
  · exact B1241919
  · exact B1241923
  · exact B1241927
  · exact B1241931
  · exact B1241935
  · exact B1241939
  · exact B1241943
  · exact B1241947
  · exact B1241951
  · exact B1241955
  · exact B1241959
  · exact B1241963
  · exact B1241967
  · exact B1241971
  · exact B1241975
  · exact B1241979
  · exact B1241983
  · exact B1241987
  · exact B1241991
  · exact B1241995
  · exact B1241999
  · exact B1242003
  · exact B1242007
  · exact B1242011
  · exact B1242015
  · exact B1242019
  · exact B1242023
  · exact B1242027
  · exact B1242031
  · exact B1242035
  · exact B1242039
  · exact B1242043
  · exact B1242047
  · exact B1242051
  · exact B1242055
  · exact B1242059
  · exact B1242063
  · exact B1242067
  · exact B1242071
  · exact B1242075
  · exact B1242079
  · exact B1242083
  · exact B1242087
  · exact B1242091
  · exact B1242095
  · exact B1242099
  · exact B1242103
  · exact B1242107
  · exact B1242111
  · exact B1242115
  · exact B1242119
  · exact B1242123
  · exact B1242127
  · exact B1242131
  · exact B1242135
  · exact B1242139
  · exact B1242143
  · exact B1242147
  · exact B1242151
  · exact B1242155
  · exact B1242159
  · exact B1242163
  · exact B1242167
  · exact B1242171
  · exact B1242175
  · exact B1242179
  · exact B1242183
  · exact B1242187
  · exact B1242191
  · exact B1242195
  · exact B1242199
  · exact B1242203
  · exact B1242207
  · exact B1242211
  · exact B1242215
  · exact B1242219
  · exact B1242223
  · exact B1242227
  · exact B1242231
  · exact B1242235
  · exact B1242239
  · exact B1242243
  · exact B1242247
  · exact B1242251
  · exact B1242255
  · exact B1242259
  · exact B1242263
  · exact B1242267
  · exact B1242271
  · exact B1242275
  · exact B1242279
  · exact B1242283
  · exact B1242287
  · exact B1242291
  · exact B1242295
  · exact B1242299
  · exact B1242303
  · exact B1242307
  · exact B1242311
  · exact B1242315
  · exact B1242319
  · exact B1242323
  · exact B1242327
  · exact B1242331
  · exact B1242335
  · exact B1242339
  · exact B1242343
  · exact B1242347
  · exact B1242351
  · exact B1242355
  · exact B1242359
  · exact B1242363
  · exact B1242367
  · exact B1242371
  · exact B1242375
  · exact B1242379
  · exact B1242383
  · exact B1242387
  · exact B1242391
  · exact B1242395
  · exact B1242399
  · exact B1242403
  · exact B1242407
  · exact B1242411
  · exact B1242415
  · exact B1242419
  · exact B1242423
  · exact B1242427
  · exact B1242431
  · exact B1242435

theorem solution (m : ℕ) (hlo : 1240438 ≤ m) (hhi : m ≤ 1242438) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 310109 ≤ j := by omega
    have hj2 : j ≤ 310608 := by omega
    have hb : Blo 1240438 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
