-- Prove2me | solution 1 for syracuse_descends_range_1668034_1670034
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:20:31.65932+00:00
-- url     : https://prove2.me/submissions/71bbe27b-bd14-4fbf-ab74-75e715d2728f

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


theorem B3612685 : Blo 1668034 3612685 := bbase (se 3 (by rfl) ⟨677378, by rfl⟩ : syracuseStep 3612685 = 1354757) (by norm_num)
theorem B2113553 : Blo 1668034 2113553 := bbase (se 2 (by rfl) ⟨792582, by rfl⟩ : syracuseStep 2113553 = 1585165) (by norm_num)
theorem B2031689 : Blo 1668034 2031689 := bbase (se 2 (by rfl) ⟨761883, by rfl⟩ : syracuseStep 2031689 = 1523767) (by norm_num)
theorem B2113609 : Blo 1668034 2113609 := bbase (se 2 (by rfl) ⟨792603, by rfl⟩ : syracuseStep 2113609 = 1585207) (by norm_num)
theorem B3612757 : Blo 1668034 3612757 := bbase (se 8 (by rfl) ⟨21168, by rfl⟩ : syracuseStep 3612757 = 42337) (by norm_num)
theorem B4513877 : Blo 1668034 4513877 := bbase (se 8 (by rfl) ⟨26448, by rfl⟩ : syracuseStep 4513877 = 52897) (by norm_num)
theorem B2818165 : Blo 1668034 2818165 := bbase (se 5 (by rfl) ⟨132101, by rfl⟩ : syracuseStep 2818165 = 264203) (by norm_num)
theorem B8454293 : Blo 1668034 8454293 := bbase (se 6 (by rfl) ⟨198147, by rfl⟩ : syracuseStep 8454293 = 396295) (by norm_num)
theorem B8020133 : Blo 1668034 8020133 := bbase (se 4 (by rfl) ⟨751887, by rfl⟩ : syracuseStep 8020133 = 1503775) (by norm_num)
theorem B5636357 : Blo 1668034 5636357 := bbase (se 4 (by rfl) ⟨528408, by rfl⟩ : syracuseStep 5636357 = 1056817) (by norm_num)
theorem B7127365 : Blo 1668034 7127365 := bbase (se 4 (by rfl) ⟨668190, by rfl⟩ : syracuseStep 7127365 = 1336381) (by norm_num)
theorem B3006829 : Blo 1668034 3006829 := bbase (se 3 (by rfl) ⟨563780, by rfl⟩ : syracuseStep 3006829 = 1127561) (by norm_num)
theorem B3211661 : Blo 1668034 3211661 := bbase (se 3 (by rfl) ⟨602186, by rfl⟩ : syracuseStep 3211661 = 1204373) (by norm_num)
theorem B3006973 : Blo 1668034 3006973 := bbase (se 3 (by rfl) ⟨563807, by rfl⟩ : syracuseStep 3006973 = 1127615) (by norm_num)
theorem B2376221 : Blo 1668034 2376221 := bbase (se 3 (by rfl) ⟨445541, by rfl⟩ : syracuseStep 2376221 = 891083) (by norm_num)
theorem B8446517 : Blo 1668034 8446517 := bbase (se 5 (by rfl) ⟨395930, by rfl⟩ : syracuseStep 8446517 = 791861) (by norm_num)
theorem B1876549 : Blo 1668034 1876549 := bbase (se 4 (by rfl) ⟨175926, by rfl⟩ : syracuseStep 1876549 = 351853) (by norm_num)
theorem B4751941 : Blo 1668034 4751941 := bbase (se 4 (by rfl) ⟨445494, by rfl⟩ : syracuseStep 4751941 = 890989) (by norm_num)
theorem B1876585 : Blo 1668034 1876585 := bbase (se 2 (by rfl) ⟨703719, by rfl⟩ : syracuseStep 1876585 = 1407439) (by norm_num)
theorem B1876621 : Blo 1668034 1876621 := bbase (se 3 (by rfl) ⟨351866, by rfl⟩ : syracuseStep 1876621 = 703733) (by norm_num)
theorem B1876657 : Blo 1668034 1876657 := bbase (se 2 (by rfl) ⟨703746, by rfl⟩ : syracuseStep 1876657 = 1407493) (by norm_num)
theorem B3384013 : Blo 1668034 3384013 := bbase (se 3 (by rfl) ⟨634502, by rfl⟩ : syracuseStep 3384013 = 1269005) (by norm_num)
theorem B1876693 : Blo 1668034 1876693 := bbase (se 7 (by rfl) ⟨21992, by rfl⟩ : syracuseStep 1876693 = 43985) (by norm_num)
theorem B4752101 : Blo 1668034 4752101 := bbase (se 4 (by rfl) ⟨445509, by rfl⟩ : syracuseStep 4752101 = 891019) (by norm_num)
theorem B1876729 : Blo 1668034 1876729 := bbase (se 2 (by rfl) ⟨703773, by rfl⟩ : syracuseStep 1876729 = 1407547) (by norm_num)
theorem B1876765 : Blo 1668034 1876765 := bbase (se 3 (by rfl) ⟨351893, by rfl⟩ : syracuseStep 1876765 = 703787) (by norm_num)
theorem B1876801 : Blo 1668034 1876801 := bbase (se 2 (by rfl) ⟨703800, by rfl⟩ : syracuseStep 1876801 = 1407601) (by norm_num)
theorem B1876837 : Blo 1668034 1876837 := bbase (se 4 (by rfl) ⟨175953, by rfl⟩ : syracuseStep 1876837 = 351907) (by norm_num)
theorem B1876873 : Blo 1668034 1876873 := bbase (se 2 (by rfl) ⟨703827, by rfl⟩ : syracuseStep 1876873 = 1407655) (by norm_num)
theorem B1876909 : Blo 1668034 1876909 := bbase (se 3 (by rfl) ⟨351920, by rfl⟩ : syracuseStep 1876909 = 703841) (by norm_num)
theorem B3564461 : Blo 1668034 3564461 := bbase (se 3 (by rfl) ⟨668336, by rfl⟩ : syracuseStep 3564461 = 1336673) (by norm_num)
theorem B1876945 : Blo 1668034 1876945 := bbase (se 2 (by rfl) ⟨703854, by rfl⟩ : syracuseStep 1876945 = 1407709) (by norm_num)
theorem B4752341 : Blo 1668034 4752341 := bbase (se 7 (by rfl) ⟨55691, by rfl⟩ : syracuseStep 4752341 = 111383) (by norm_num)
theorem B1876981 : Blo 1668034 1876981 := bbase (se 5 (by rfl) ⟨87983, by rfl⟩ : syracuseStep 1876981 = 175967) (by norm_num)
theorem B6333461 : Blo 1668034 6333461 := bbase (se 6 (by rfl) ⟨148440, by rfl⟩ : syracuseStep 6333461 = 296881) (by norm_num)
theorem B1877017 : Blo 1668034 1877017 := bbase (se 2 (by rfl) ⟨703881, by rfl⟩ : syracuseStep 1877017 = 1407763) (by norm_num)
theorem B7128101 : Blo 1668034 7128101 := bbase (se 4 (by rfl) ⟨668259, by rfl⟩ : syracuseStep 7128101 = 1336519) (by norm_num)
theorem B1877053 : Blo 1668034 1877053 := bbase (se 3 (by rfl) ⟨351947, by rfl⟩ : syracuseStep 1877053 = 703895) (by norm_num)
theorem B3564605 : Blo 1668034 3564605 := bbase (se 3 (by rfl) ⟨668363, by rfl⟩ : syracuseStep 3564605 = 1336727) (by norm_num)
theorem B9143381 : Blo 1668034 9143381 := bbase (se 8 (by rfl) ⟨53574, by rfl⟩ : syracuseStep 9143381 = 107149) (by norm_num)
theorem B1877089 : Blo 1668034 1877089 := bbase (se 2 (by rfl) ⟨703908, by rfl⟩ : syracuseStep 1877089 = 1407817) (by norm_num)
theorem B1877125 : Blo 1668034 1877125 := bbase (se 4 (by rfl) ⟨175980, by rfl⟩ : syracuseStep 1877125 = 351961) (by norm_num)
theorem B4752533 : Blo 1668034 4752533 := bbase (se 6 (by rfl) ⟨111387, by rfl⟩ : syracuseStep 4752533 = 222775) (by norm_num)
theorem B3753125 : Blo 1668034 3753125 := bbase (se 4 (by rfl) ⟨351855, by rfl⟩ : syracuseStep 3753125 = 703711) (by norm_num)
theorem B1877161 : Blo 1668034 1877161 := bbase (se 2 (by rfl) ⟨703935, by rfl⟩ : syracuseStep 1877161 = 1407871) (by norm_num)
theorem B1877197 : Blo 1668034 1877197 := bbase (se 3 (by rfl) ⟨351974, by rfl⟩ : syracuseStep 1877197 = 703949) (by norm_num)
theorem B3753197 : Blo 1668034 3753197 := bbase (se 3 (by rfl) ⟨703724, by rfl⟩ : syracuseStep 3753197 = 1407449) (by norm_num)
theorem B1877233 : Blo 1668034 1877233 := bbase (se 2 (by rfl) ⟨703962, by rfl⟩ : syracuseStep 1877233 = 1407925) (by norm_num)
theorem B2376973 : Blo 1668034 2376973 := bbase (se 3 (by rfl) ⟨445682, by rfl⟩ : syracuseStep 2376973 = 891365) (by norm_num)
theorem B1877269 : Blo 1668034 1877269 := bbase (se 6 (by rfl) ⟨43998, by rfl⟩ : syracuseStep 1877269 = 87997) (by norm_num)
theorem B4818197 : Blo 1668034 4818197 := bbase (se 6 (by rfl) ⟨112926, by rfl⟩ : syracuseStep 4818197 = 225853) (by norm_num)
theorem B3753269 : Blo 1668034 3753269 := bbase (se 5 (by rfl) ⟨175934, by rfl⟩ : syracuseStep 3753269 = 351869) (by norm_num)
theorem B1877305 : Blo 1668034 1877305 := bbase (se 2 (by rfl) ⟨703989, by rfl⟩ : syracuseStep 1877305 = 1407979) (by norm_num)
theorem B1877341 : Blo 1668034 1877341 := bbase (se 3 (by rfl) ⟨352001, by rfl⟩ : syracuseStep 1877341 = 704003) (by norm_num)
theorem B3753341 : Blo 1668034 3753341 := bbase (se 3 (by rfl) ⟨703751, by rfl⟩ : syracuseStep 3753341 = 1407503) (by norm_num)
theorem B1877377 : Blo 1668034 1877377 := bbase (se 2 (by rfl) ⟨704016, by rfl⟩ : syracuseStep 1877377 = 1408033) (by norm_num)
theorem B1877413 : Blo 1668034 1877413 := bbase (se 4 (by rfl) ⟨176007, by rfl⟩ : syracuseStep 1877413 = 352015) (by norm_num)
theorem B6096293 : Blo 1668034 6096293 := bbase (se 4 (by rfl) ⟨571527, by rfl⟩ : syracuseStep 6096293 = 1143055) (by norm_num)
theorem B3564965 : Blo 1668034 3564965 := bbase (se 4 (by rfl) ⟨334215, by rfl⟩ : syracuseStep 3564965 = 668431) (by norm_num)
theorem B2672045 : Blo 1668034 2672045 := bbase (se 3 (by rfl) ⟨501008, by rfl⟩ : syracuseStep 2672045 = 1002017) (by norm_num)
theorem B3007925 : Blo 1668034 3007925 := bbase (se 5 (by rfl) ⟨140996, by rfl⟩ : syracuseStep 3007925 = 281993) (by norm_num)
theorem B3753413 : Blo 1668034 3753413 := bbase (se 4 (by rfl) ⟨351882, by rfl⟩ : syracuseStep 3753413 = 703765) (by norm_num)
theorem B1877449 : Blo 1668034 1877449 := bbase (se 2 (by rfl) ⟨704043, by rfl⟩ : syracuseStep 1877449 = 1408087) (by norm_num)
theorem B1877485 : Blo 1668034 1877485 := bbase (se 3 (by rfl) ⟨352028, by rfl⟩ : syracuseStep 1877485 = 704057) (by norm_num)
theorem B3007997 : Blo 1668034 3007997 := bbase (se 3 (by rfl) ⟨563999, by rfl⟩ : syracuseStep 3007997 = 1127999) (by norm_num)
theorem B3753485 : Blo 1668034 3753485 := bbase (se 3 (by rfl) ⟨703778, by rfl⟩ : syracuseStep 3753485 = 1407557) (by norm_num)
theorem B1877521 : Blo 1668034 1877521 := bbase (se 2 (by rfl) ⟨704070, by rfl⟩ : syracuseStep 1877521 = 1408141) (by norm_num)
theorem B1877557 : Blo 1668034 1877557 := bbase (se 5 (by rfl) ⟨88010, by rfl⟩ : syracuseStep 1877557 = 176021) (by norm_num)
theorem B3753557 : Blo 1668034 3753557 := bbase (se 8 (by rfl) ⟨21993, by rfl⟩ : syracuseStep 3753557 = 43987) (by norm_num)
theorem B32507477 : Blo 1668034 32507477 := bbase (se 8 (by rfl) ⟨190473, by rfl⟩ : syracuseStep 32507477 = 380947) (by norm_num)
theorem B1877593 : Blo 1668034 1877593 := bbase (se 2 (by rfl) ⟨704097, by rfl⟩ : syracuseStep 1877593 = 1408195) (by norm_num)
theorem B2672237 : Blo 1668034 2672237 := bbase (se 3 (by rfl) ⟨501044, by rfl⟩ : syracuseStep 2672237 = 1002089) (by norm_num)
theorem B1877629 : Blo 1668034 1877629 := bbase (se 3 (by rfl) ⟨352055, by rfl⟩ : syracuseStep 1877629 = 704111) (by norm_num)
theorem B3753629 : Blo 1668034 3753629 := bbase (se 3 (by rfl) ⟨703805, by rfl⟩ : syracuseStep 3753629 = 1407611) (by norm_num)
theorem B1877665 : Blo 1668034 1877665 := bbase (se 2 (by rfl) ⟨704124, by rfl⟩ : syracuseStep 1877665 = 1408249) (by norm_num)
theorem B1877701 : Blo 1668034 1877701 := bbase (se 4 (by rfl) ⟨176034, by rfl⟩ : syracuseStep 1877701 = 352069) (by norm_num)
theorem B3753701 : Blo 1668034 3753701 := bbase (se 4 (by rfl) ⟨351909, by rfl⟩ : syracuseStep 3753701 = 703819) (by norm_num)
theorem B1877737 : Blo 1668034 1877737 := bbase (se 2 (by rfl) ⟨704151, by rfl⟩ : syracuseStep 1877737 = 1408303) (by norm_num)
theorem B1902317 : Blo 1668034 1902317 := bbase (se 3 (by rfl) ⟨356684, by rfl⟩ : syracuseStep 1902317 = 713369) (by norm_num)
theorem B1877773 : Blo 1668034 1877773 := bbase (se 3 (by rfl) ⟨352082, by rfl⟩ : syracuseStep 1877773 = 704165) (by norm_num)
theorem B3753773 : Blo 1668034 3753773 := bbase (se 3 (by rfl) ⟨703832, by rfl⟩ : syracuseStep 3753773 = 1407665) (by norm_num)
theorem B1877809 : Blo 1668034 1877809 := bbase (se 2 (by rfl) ⟨704178, by rfl⟩ : syracuseStep 1877809 = 1408357) (by norm_num)
theorem B8447813 : Blo 1668034 8447813 := bbase (se 4 (by rfl) ⟨791982, by rfl⟩ : syracuseStep 8447813 = 1583965) (by norm_num)
theorem B3385165 : Blo 1668034 3385165 := bbase (se 3 (by rfl) ⟨634718, by rfl⟩ : syracuseStep 3385165 = 1269437) (by norm_num)
theorem B1877845 : Blo 1668034 1877845 := bbase (se 9 (by rfl) ⟨5501, by rfl⟩ : syracuseStep 1877845 = 11003) (by norm_num)
theorem B3614557 : Blo 1668034 3614557 := bbase (se 3 (by rfl) ⟨677729, by rfl⟩ : syracuseStep 3614557 = 1355459) (by norm_num)
theorem B3753845 : Blo 1668034 3753845 := bbase (se 5 (by rfl) ⟨175961, by rfl⟩ : syracuseStep 3753845 = 351923) (by norm_num)
theorem B2140025 : Blo 1668034 2140025 := bbase (se 2 (by rfl) ⟨802509, by rfl⟩ : syracuseStep 2140025 = 1605019) (by norm_num)
theorem B1877881 : Blo 1668034 1877881 := bbase (se 2 (by rfl) ⟨704205, by rfl⟩ : syracuseStep 1877881 = 1408411) (by norm_num)
theorem B1877917 : Blo 1668034 1877917 := bbase (se 3 (by rfl) ⟨352109, by rfl⟩ : syracuseStep 1877917 = 704219) (by norm_num)
theorem B5629877 : Blo 1668034 5629877 := bbase (se 5 (by rfl) ⟨263900, by rfl⟩ : syracuseStep 5629877 = 527801) (by norm_num)
theorem B3753917 : Blo 1668034 3753917 := bbase (se 3 (by rfl) ⟨703859, by rfl⟩ : syracuseStep 3753917 = 1407719) (by norm_num)
theorem B1877953 : Blo 1668034 1877953 := bbase (se 2 (by rfl) ⟨704232, by rfl⟩ : syracuseStep 1877953 = 1408465) (by norm_num)
theorem B12036053 : Blo 1668034 12036053 := bbase (se 7 (by rfl) ⟨141047, by rfl⟩ : syracuseStep 12036053 = 282095) (by norm_num)
theorem B1877989 : Blo 1668034 1877989 := bbase (se 4 (by rfl) ⟨176061, by rfl⟩ : syracuseStep 1877989 = 352123) (by norm_num)
theorem B3753989 : Blo 1668034 3753989 := bbase (se 4 (by rfl) ⟨351936, by rfl⟩ : syracuseStep 3753989 = 703873) (by norm_num)
theorem B1878025 : Blo 1668034 1878025 := bbase (se 2 (by rfl) ⟨704259, by rfl⟩ : syracuseStep 1878025 = 1408519) (by norm_num)
theorem B8022037 : Blo 1668034 8022037 := bbase (se 6 (by rfl) ⟨188016, by rfl⟩ : syracuseStep 8022037 = 376033) (by norm_num)
theorem B3213341 : Blo 1668034 3213341 := bbase (se 3 (by rfl) ⟨602501, by rfl⟩ : syracuseStep 3213341 = 1205003) (by norm_num)
theorem B8022053 : Blo 1668034 8022053 := bbase (se 4 (by rfl) ⟨752067, by rfl⟩ : syracuseStep 8022053 = 1504135) (by norm_num)
theorem B2377765 : Blo 1668034 2377765 := bbase (se 4 (by rfl) ⟨222915, by rfl⟩ : syracuseStep 2377765 = 445831) (by norm_num)
theorem B1878061 : Blo 1668034 1878061 := bbase (se 3 (by rfl) ⟨352136, by rfl⟩ : syracuseStep 1878061 = 704273) (by norm_num)
theorem B3754061 : Blo 1668034 3754061 := bbase (se 3 (by rfl) ⟨703886, by rfl⟩ : syracuseStep 3754061 = 1407773) (by norm_num)
theorem B1878097 : Blo 1668034 1878097 := bbase (se 2 (by rfl) ⟨704286, by rfl⟩ : syracuseStep 1878097 = 1408573) (by norm_num)
theorem B4753525 : Blo 1668034 4753525 := bbase (se 5 (by rfl) ⟨222821, by rfl⟩ : syracuseStep 4753525 = 445643) (by norm_num)
theorem B1878133 : Blo 1668034 1878133 := bbase (se 5 (by rfl) ⟨88037, by rfl⟩ : syracuseStep 1878133 = 176075) (by norm_num)
theorem B3754133 : Blo 1668034 3754133 := bbase (se 6 (by rfl) ⟨87987, by rfl⟩ : syracuseStep 3754133 = 175975) (by norm_num)
theorem B1878169 : Blo 1668034 1878169 := bbase (se 2 (by rfl) ⟨704313, by rfl⟩ : syracuseStep 1878169 = 1408627) (by norm_num)
theorem B6334645 : Blo 1668034 6334645 := bbase (se 5 (by rfl) ⟨296936, by rfl⟩ : syracuseStep 6334645 = 593873) (by norm_num)
theorem B1878205 : Blo 1668034 1878205 := bbase (se 3 (by rfl) ⟨352163, by rfl⟩ : syracuseStep 1878205 = 704327) (by norm_num)
theorem B3754205 : Blo 1668034 3754205 := bbase (se 3 (by rfl) ⟨703913, by rfl⟩ : syracuseStep 3754205 = 1407827) (by norm_num)
theorem B1878241 : Blo 1668034 1878241 := bbase (se 2 (by rfl) ⟨704340, by rfl⟩ : syracuseStep 1878241 = 1408681) (by norm_num)
theorem B1878277 : Blo 1668034 1878277 := bbase (se 4 (by rfl) ⟨176088, by rfl⟩ : syracuseStep 1878277 = 352177) (by norm_num)
theorem B4008221 : Blo 1668034 4008221 := bbase (se 3 (by rfl) ⟨751541, by rfl⟩ : syracuseStep 4008221 = 1503083) (by norm_num)
theorem B3565853 : Blo 1668034 3565853 := bbase (se 3 (by rfl) ⟨668597, by rfl⟩ : syracuseStep 3565853 = 1337195) (by norm_num)
theorem B3754277 : Blo 1668034 3754277 := bbase (se 4 (by rfl) ⟨351963, by rfl⟩ : syracuseStep 3754277 = 703927) (by norm_num)
theorem B1878313 : Blo 1668034 1878313 := bbase (se 2 (by rfl) ⟨704367, by rfl⟩ : syracuseStep 1878313 = 1408735) (by norm_num)
theorem B1878349 : Blo 1668034 1878349 := bbase (se 3 (by rfl) ⟨352190, by rfl⟩ : syracuseStep 1878349 = 704381) (by norm_num)
theorem B5630309 : Blo 1668034 5630309 := bbase (se 4 (by rfl) ⟨527841, by rfl⟩ : syracuseStep 5630309 = 1055683) (by norm_num)
theorem B3754349 : Blo 1668034 3754349 := bbase (se 3 (by rfl) ⟨703940, by rfl⟩ : syracuseStep 3754349 = 1407881) (by norm_num)
theorem B1878385 : Blo 1668034 1878385 := bbase (se 2 (by rfl) ⟨704394, by rfl⟩ : syracuseStep 1878385 = 1408789) (by norm_num)
theorem B4065677 : Blo 1668034 4065677 := bbase (se 3 (by rfl) ⟨762314, by rfl⟩ : syracuseStep 4065677 = 1524629) (by norm_num)
theorem B1878421 : Blo 1668034 1878421 := bbase (se 6 (by rfl) ⟨44025, by rfl⟩ : syracuseStep 1878421 = 88051) (by norm_num)
theorem B3754421 : Blo 1668034 3754421 := bbase (se 5 (by rfl) ⟨175988, by rfl⟩ : syracuseStep 3754421 = 351977) (by norm_num)
theorem B1878457 : Blo 1668034 1878457 := bbase (se 2 (by rfl) ⟨704421, by rfl⟩ : syracuseStep 1878457 = 1408843) (by norm_num)
theorem B2853317 : Blo 1668034 2853317 := bbase (se 4 (by rfl) ⟨267498, by rfl⟩ : syracuseStep 2853317 = 534997) (by norm_num)
theorem B4008413 : Blo 1668034 4008413 := bbase (se 3 (by rfl) ⟨751577, by rfl⟩ : syracuseStep 4008413 = 1503155) (by norm_num)
theorem B1878493 : Blo 1668034 1878493 := bbase (se 3 (by rfl) ⟨352217, by rfl⟩ : syracuseStep 1878493 = 704435) (by norm_num)
theorem B6334949 : Blo 1668034 6334949 := bbase (se 4 (by rfl) ⟨593901, by rfl⟩ : syracuseStep 6334949 = 1187803) (by norm_num)
theorem B3754493 : Blo 1668034 3754493 := bbase (se 3 (by rfl) ⟨703967, by rfl⟩ : syracuseStep 3754493 = 1407935) (by norm_num)
theorem B1878529 : Blo 1668034 1878529 := bbase (se 2 (by rfl) ⟨704448, by rfl⟩ : syracuseStep 1878529 = 1408897) (by norm_num)
theorem B17132053 : Blo 1668034 17132053 := bbase (se 6 (by rfl) ⟨401532, by rfl⟩ : syracuseStep 17132053 = 803065) (by norm_num)
theorem B3566101 : Blo 1668034 3566101 := bbase (se 6 (by rfl) ⟨83580, by rfl⟩ : syracuseStep 3566101 = 167161) (by norm_num)
theorem B1878565 : Blo 1668034 1878565 := bbase (se 4 (by rfl) ⟨176115, by rfl⟩ : syracuseStep 1878565 = 352231) (by norm_num)
theorem B3754565 : Blo 1668034 3754565 := bbase (se 4 (by rfl) ⟨351990, by rfl⟩ : syracuseStep 3754565 = 703981) (by norm_num)
theorem B1878601 : Blo 1668034 1878601 := bbase (se 2 (by rfl) ⟨704475, by rfl⟩ : syracuseStep 1878601 = 1408951) (by norm_num)
theorem B1878637 : Blo 1668034 1878637 := bbase (se 3 (by rfl) ⟨352244, by rfl⟩ : syracuseStep 1878637 = 704489) (by norm_num)
theorem B3754637 : Blo 1668034 3754637 := bbase (se 3 (by rfl) ⟨703994, by rfl⟩ : syracuseStep 3754637 = 1407989) (by norm_num)
theorem B1878673 : Blo 1668034 1878673 := bbase (se 2 (by rfl) ⟨704502, by rfl⟩ : syracuseStep 1878673 = 1409005) (by norm_num)
theorem B14264981 : Blo 1668034 14264981 := bbase (se 6 (by rfl) ⟨334335, by rfl⟩ : syracuseStep 14264981 = 668671) (by norm_num)
theorem B1878709 : Blo 1668034 1878709 := bbase (se 5 (by rfl) ⟨88064, by rfl⟩ : syracuseStep 1878709 = 176129) (by norm_num)
theorem B3754709 : Blo 1668034 3754709 := bbase (se 7 (by rfl) ⟨44000, by rfl⟩ : syracuseStep 3754709 = 88001) (by norm_num)
theorem B1878745 : Blo 1668034 1878745 := bbase (se 2 (by rfl) ⟨704529, by rfl⟩ : syracuseStep 1878745 = 1409059) (by norm_num)
theorem B1878781 : Blo 1668034 1878781 := bbase (se 3 (by rfl) ⟨352271, by rfl⟩ : syracuseStep 1878781 = 704543) (by norm_num)
theorem B5630741 : Blo 1668034 5630741 := bbase (se 6 (by rfl) ⟨131970, by rfl⟩ : syracuseStep 5630741 = 263941) (by norm_num)
theorem B14256917 : Blo 1668034 14256917 := bbase (se 6 (by rfl) ⟨334146, by rfl⟩ : syracuseStep 14256917 = 668293) (by norm_num)
theorem B3754781 : Blo 1668034 3754781 := bbase (se 3 (by rfl) ⟨704021, by rfl⟩ : syracuseStep 3754781 = 1408043) (by norm_num)
theorem B3754853 : Blo 1668034 3754853 := bbase (se 4 (by rfl) ⟨352017, by rfl⟩ : syracuseStep 3754853 = 704035) (by norm_num)
theorem B2673557 : Blo 1668034 2673557 := bbase (se 6 (by rfl) ⟨62661, by rfl⟩ : syracuseStep 2673557 = 125323) (by norm_num)
theorem B3754925 : Blo 1668034 3754925 := bbase (se 3 (by rfl) ⟨704048, by rfl⟩ : syracuseStep 3754925 = 1408097) (by norm_num)
theorem B3754997 : Blo 1668034 3754997 := bbase (se 5 (by rfl) ⟨176015, by rfl⟩ : syracuseStep 3754997 = 352031) (by norm_num)
theorem B2673653 : Blo 1668034 2673653 := bbase (se 5 (by rfl) ⟨125327, by rfl⟩ : syracuseStep 2673653 = 250655) (by norm_num)
theorem B3566605 : Blo 1668034 3566605 := bbase (se 3 (by rfl) ⟨668738, by rfl⟩ : syracuseStep 3566605 = 1337477) (by norm_num)
theorem B2673685 : Blo 1668034 2673685 := bbase (se 6 (by rfl) ⟨62664, by rfl⟩ : syracuseStep 2673685 = 125329) (by norm_num)
theorem B3755069 : Blo 1668034 3755069 := bbase (se 3 (by rfl) ⟨704075, by rfl⟩ : syracuseStep 3755069 = 1408151) (by norm_num)
theorem B8449109 : Blo 1668034 8449109 := bbase (se 8 (by rfl) ⟨49506, by rfl⟩ : syracuseStep 8449109 = 99013) (by norm_num)
theorem B3755141 : Blo 1668034 3755141 := bbase (se 4 (by rfl) ⟨352044, by rfl⟩ : syracuseStep 3755141 = 704089) (by norm_num)
theorem B5631173 : Blo 1668034 5631173 := bbase (se 4 (by rfl) ⟨527922, by rfl⟩ : syracuseStep 5631173 = 1055845) (by norm_num)
theorem B4754629 : Blo 1668034 4754629 := bbase (se 4 (by rfl) ⟨445746, by rfl⟩ : syracuseStep 4754629 = 891493) (by norm_num)
theorem B3755213 : Blo 1668034 3755213 := bbase (se 3 (by rfl) ⟨704102, by rfl⟩ : syracuseStep 3755213 = 1408205) (by norm_num)
theorem B5418197 : Blo 1668034 5418197 := bbase (se 7 (by rfl) ⟨63494, by rfl⟩ : syracuseStep 5418197 = 126989) (by norm_num)
theorem B4009181 : Blo 1668034 4009181 := bbase (se 3 (by rfl) ⟨751721, by rfl⟩ : syracuseStep 4009181 = 1503443) (by norm_num)
theorem B12201205 : Blo 1668034 12201205 := bbase (se 5 (by rfl) ⟨571931, by rfl⟩ : syracuseStep 12201205 = 1143863) (by norm_num)
theorem B3755285 : Blo 1668034 3755285 := bbase (se 6 (by rfl) ⟨88014, by rfl⟩ : syracuseStep 3755285 = 176029) (by norm_num)
theorem B9506069 : Blo 1668034 9506069 := bbase (se 6 (by rfl) ⟨222798, by rfl⟩ : syracuseStep 9506069 = 445597) (by norm_num)
theorem B2256181 : Blo 1668034 2256181 := bbase (se 5 (by rfl) ⟨105758, by rfl⟩ : syracuseStep 2256181 = 211517) (by norm_num)
theorem B4222277 : Blo 1668034 4222277 := bbase (se 4 (by rfl) ⟨395838, by rfl⟩ : syracuseStep 4222277 = 791677) (by norm_num)
theorem B3755357 : Blo 1668034 3755357 := bbase (se 3 (by rfl) ⟨704129, by rfl⟩ : syracuseStep 3755357 = 1408259) (by norm_num)
theorem B2502053 : Blo 1668034 2502053 := bbase (se 4 (by rfl) ⟨234567, by rfl⟩ : syracuseStep 2502053 = 469135) (by norm_num)
theorem B3755429 : Blo 1668034 3755429 := bbase (se 4 (by rfl) ⟨352071, by rfl⟩ : syracuseStep 3755429 = 704143) (by norm_num)
theorem B2502077 : Blo 1668034 2502077 := bbase (se 3 (by rfl) ⟨469139, by rfl⟩ : syracuseStep 2502077 = 938279) (by norm_num)
theorem B2502101 : Blo 1668034 2502101 := bbase (se 7 (by rfl) ⟨29321, by rfl⟩ : syracuseStep 2502101 = 58643) (by norm_num)
theorem B2502125 : Blo 1668034 2502125 := bbase (se 3 (by rfl) ⟨469148, by rfl⟩ : syracuseStep 2502125 = 938297) (by norm_num)
theorem B3755501 : Blo 1668034 3755501 := bbase (se 3 (by rfl) ⟨704156, by rfl⟩ : syracuseStep 3755501 = 1408313) (by norm_num)
theorem B3804661 : Blo 1668034 3804661 := bbase (se 5 (by rfl) ⟨178343, by rfl⟩ : syracuseStep 3804661 = 356687) (by norm_num)
theorem B2502149 : Blo 1668034 2502149 := bbase (se 4 (by rfl) ⟨234576, by rfl⟩ : syracuseStep 2502149 = 469153) (by norm_num)
theorem B4222469 : Blo 1668034 4222469 := bbase (se 4 (by rfl) ⟨395856, by rfl⟩ : syracuseStep 4222469 = 791713) (by norm_num)
theorem B2502173 : Blo 1668034 2502173 := bbase (se 3 (by rfl) ⟨469157, by rfl⟩ : syracuseStep 2502173 = 938315) (by norm_num)
theorem B2502197 : Blo 1668034 2502197 := bbase (se 5 (by rfl) ⟨117290, by rfl⟩ : syracuseStep 2502197 = 234581) (by norm_num)
theorem B3755573 : Blo 1668034 3755573 := bbase (se 5 (by rfl) ⟨176042, by rfl⟩ : syracuseStep 3755573 = 352085) (by norm_num)
theorem B4951621 : Blo 1668034 4951621 := bbase (se 4 (by rfl) ⟨464214, by rfl⟩ : syracuseStep 4951621 = 928429) (by norm_num)
theorem B2502221 : Blo 1668034 2502221 := bbase (se 3 (by rfl) ⟨469166, by rfl⟩ : syracuseStep 2502221 = 938333) (by norm_num)
theorem B2502245 : Blo 1668034 2502245 := bbase (se 4 (by rfl) ⟨234585, by rfl⟩ : syracuseStep 2502245 = 469171) (by norm_num)
theorem B5631605 : Blo 1668034 5631605 := bbase (se 5 (by rfl) ⟨263981, by rfl⟩ : syracuseStep 5631605 = 527963) (by norm_num)
theorem B2502269 : Blo 1668034 2502269 := bbase (se 3 (by rfl) ⟨469175, by rfl⟩ : syracuseStep 2502269 = 938351) (by norm_num)
theorem B3755645 : Blo 1668034 3755645 := bbase (se 3 (by rfl) ⟨704183, by rfl⟩ : syracuseStep 3755645 = 1408367) (by norm_num)
theorem B1781389 : Blo 1668034 1781389 := bbase (se 3 (by rfl) ⟨334010, by rfl⟩ : syracuseStep 1781389 = 668021) (by norm_num)
theorem B2502293 : Blo 1668034 2502293 := bbase (se 6 (by rfl) ⟨58647, by rfl⟩ : syracuseStep 2502293 = 117295) (by norm_num)
theorem B7614101 : Blo 1668034 7614101 := bbase (se 6 (by rfl) ⟨178455, by rfl⟩ : syracuseStep 7614101 = 356911) (by norm_num)
theorem B2502317 : Blo 1668034 2502317 := bbase (se 3 (by rfl) ⟨469184, by rfl⟩ : syracuseStep 2502317 = 938369) (by norm_num)
theorem B2502341 : Blo 1668034 2502341 := bbase (se 4 (by rfl) ⟨234594, by rfl⟩ : syracuseStep 2502341 = 469189) (by norm_num)
theorem B3755717 : Blo 1668034 3755717 := bbase (se 4 (by rfl) ⟨352098, by rfl⟩ : syracuseStep 3755717 = 704197) (by norm_num)
theorem B2502365 : Blo 1668034 2502365 := bbase (se 3 (by rfl) ⟨469193, by rfl⟩ : syracuseStep 2502365 = 938387) (by norm_num)
theorem B2502389 : Blo 1668034 2502389 := bbase (se 5 (by rfl) ⟨117299, by rfl⟩ : syracuseStep 2502389 = 234599) (by norm_num)
theorem B2502413 : Blo 1668034 2502413 := bbase (se 3 (by rfl) ⟨469202, by rfl⟩ : syracuseStep 2502413 = 938405) (by norm_num)
theorem B3755789 : Blo 1668034 3755789 := bbase (se 3 (by rfl) ⟨704210, by rfl⟩ : syracuseStep 3755789 = 1408421) (by norm_num)
theorem B1904401 : Blo 1668034 1904401 := bbase (se 2 (by rfl) ⟨714150, by rfl⟩ : syracuseStep 1904401 = 1428301) (by norm_num)
theorem B2502437 : Blo 1668034 2502437 := bbase (se 4 (by rfl) ⟨234603, by rfl⟩ : syracuseStep 2502437 = 469207) (by norm_num)
theorem B2502461 : Blo 1668034 2502461 := bbase (se 3 (by rfl) ⟨469211, by rfl⟩ : syracuseStep 2502461 = 938423) (by norm_num)
theorem B2502485 : Blo 1668034 2502485 := bbase (se 9 (by rfl) ⟨7331, by rfl⟩ : syracuseStep 2502485 = 14663) (by norm_num)
theorem B3755861 : Blo 1668034 3755861 := bbase (se 9 (by rfl) ⟨11003, by rfl⟩ : syracuseStep 3755861 = 22007) (by norm_num)
theorem B4222813 : Blo 1668034 4222813 := bbase (se 3 (by rfl) ⟨791777, by rfl⟩ : syracuseStep 4222813 = 1583555) (by norm_num)
theorem B1929053 : Blo 1668034 1929053 := bbase (se 3 (by rfl) ⟨361697, by rfl⟩ : syracuseStep 1929053 = 723395) (by norm_num)
theorem B2502509 : Blo 1668034 2502509 := bbase (se 3 (by rfl) ⟨469220, by rfl⟩ : syracuseStep 2502509 = 938441) (by norm_num)
theorem B1929085 : Blo 1668034 1929085 := bbase (se 3 (by rfl) ⟨361703, by rfl⟩ : syracuseStep 1929085 = 723407) (by norm_num)
theorem B2502533 : Blo 1668034 2502533 := bbase (se 4 (by rfl) ⟨234612, by rfl⟩ : syracuseStep 2502533 = 469225) (by norm_num)
theorem B2502557 : Blo 1668034 2502557 := bbase (se 3 (by rfl) ⟨469229, by rfl⟩ : syracuseStep 2502557 = 938459) (by norm_num)
theorem B3755933 : Blo 1668034 3755933 := bbase (se 3 (by rfl) ⟨704237, by rfl⟩ : syracuseStep 3755933 = 1408475) (by norm_num)
theorem B2502581 : Blo 1668034 2502581 := bbase (se 5 (by rfl) ⟨117308, by rfl⟩ : syracuseStep 2502581 = 234617) (by norm_num)
theorem B4222925 : Blo 1668034 4222925 := bbase (se 3 (by rfl) ⟨791798, by rfl⟩ : syracuseStep 4222925 = 1583597) (by norm_num)
theorem B2502605 : Blo 1668034 2502605 := bbase (se 3 (by rfl) ⟨469238, by rfl⟩ : syracuseStep 2502605 = 938477) (by norm_num)
theorem B1691609 : Blo 1668034 1691609 := bbase (se 2 (by rfl) ⟨634353, by rfl⟩ : syracuseStep 1691609 = 1268707) (by norm_num)
theorem B2502629 : Blo 1668034 2502629 := bbase (se 4 (by rfl) ⟨234621, by rfl⟩ : syracuseStep 2502629 = 469243) (by norm_num)
theorem B3756005 : Blo 1668034 3756005 := bbase (se 4 (by rfl) ⟨352125, by rfl⟩ : syracuseStep 3756005 = 704251) (by norm_num)
theorem B2502653 : Blo 1668034 2502653 := bbase (se 3 (by rfl) ⟨469247, by rfl⟩ : syracuseStep 2502653 = 938495) (by norm_num)
theorem B2502677 : Blo 1668034 2502677 := bbase (se 6 (by rfl) ⟨58656, by rfl⟩ : syracuseStep 2502677 = 117313) (by norm_num)
theorem B5632037 : Blo 1668034 5632037 := bbase (se 4 (by rfl) ⟨528003, by rfl⟩ : syracuseStep 5632037 = 1056007) (by norm_num)
theorem B2502701 : Blo 1668034 2502701 := bbase (se 3 (by rfl) ⟨469256, by rfl⟩ : syracuseStep 2502701 = 938513) (by norm_num)
theorem B3756077 : Blo 1668034 3756077 := bbase (se 3 (by rfl) ⟨704264, by rfl⟩ : syracuseStep 3756077 = 1408529) (by norm_num)
theorem B2502725 : Blo 1668034 2502725 := bbase (se 4 (by rfl) ⟨234630, by rfl⟩ : syracuseStep 2502725 = 469261) (by norm_num)
theorem B1781833 : Blo 1668034 1781833 := bbase (se 2 (by rfl) ⟨668187, by rfl⟩ : syracuseStep 1781833 = 1336375) (by norm_num)
theorem B2502749 : Blo 1668034 2502749 := bbase (se 3 (by rfl) ⟨469265, by rfl⟩ : syracuseStep 2502749 = 938531) (by norm_num)
theorem B2502773 : Blo 1668034 2502773 := bbase (se 5 (by rfl) ⟨117317, by rfl⟩ : syracuseStep 2502773 = 234635) (by norm_num)
theorem B3756149 : Blo 1668034 3756149 := bbase (se 5 (by rfl) ⟨176069, by rfl⟩ : syracuseStep 3756149 = 352139) (by norm_num)
theorem B4223117 : Blo 1668034 4223117 := bbase (se 3 (by rfl) ⟨791834, by rfl⟩ : syracuseStep 4223117 = 1583669) (by norm_num)
theorem B2502797 : Blo 1668034 2502797 := bbase (se 3 (by rfl) ⟨469274, by rfl⟩ : syracuseStep 2502797 = 938549) (by norm_num)
theorem B2855069 : Blo 1668034 2855069 := bbase (se 3 (by rfl) ⟨535325, by rfl⟩ : syracuseStep 2855069 = 1070651) (by norm_num)
theorem B2502821 : Blo 1668034 2502821 := bbase (se 4 (by rfl) ⟨234639, by rfl⟩ : syracuseStep 2502821 = 469279) (by norm_num)
theorem B2502845 : Blo 1668034 2502845 := bbase (se 3 (by rfl) ⟨469283, by rfl⟩ : syracuseStep 2502845 = 938567) (by norm_num)
theorem B3756221 : Blo 1668034 3756221 := bbase (se 3 (by rfl) ⟨704291, by rfl⟩ : syracuseStep 3756221 = 1408583) (by norm_num)
theorem B1781957 : Blo 1668034 1781957 := bbase (se 4 (by rfl) ⟨167058, by rfl⟩ : syracuseStep 1781957 = 334117) (by norm_num)
theorem B2502869 : Blo 1668034 2502869 := bbase (se 7 (by rfl) ⟨29330, by rfl⟩ : syracuseStep 2502869 = 58661) (by norm_num)
theorem B2855125 : Blo 1668034 2855125 := bbase (se 7 (by rfl) ⟨33458, by rfl⟩ : syracuseStep 2855125 = 66917) (by norm_num)
theorem B2502893 : Blo 1668034 2502893 := bbase (se 3 (by rfl) ⟨469292, by rfl⟩ : syracuseStep 2502893 = 938585) (by norm_num)
theorem B4280573 : Blo 1668034 4280573 := bbase (se 3 (by rfl) ⟨802607, by rfl⟩ : syracuseStep 4280573 = 1605215) (by norm_num)
theorem B2502917 : Blo 1668034 2502917 := bbase (se 4 (by rfl) ⟨234648, by rfl⟩ : syracuseStep 2502917 = 469297) (by norm_num)
theorem B3756293 : Blo 1668034 3756293 := bbase (se 4 (by rfl) ⟨352152, by rfl⟩ : syracuseStep 3756293 = 704305) (by norm_num)
theorem B7131397 : Blo 1668034 7131397 := bbase (se 4 (by rfl) ⟨668568, by rfl⟩ : syracuseStep 7131397 = 1337137) (by norm_num)
theorem B2502941 : Blo 1668034 2502941 := bbase (se 3 (by rfl) ⟨469301, by rfl⟩ : syracuseStep 2502941 = 938603) (by norm_num)
theorem B2502965 : Blo 1668034 2502965 := bbase (se 5 (by rfl) ⟨117326, by rfl⟩ : syracuseStep 2502965 = 234653) (by norm_num)
theorem B2502989 : Blo 1668034 2502989 := bbase (se 3 (by rfl) ⟨469310, by rfl⟩ : syracuseStep 2502989 = 938621) (by norm_num)
theorem B3756365 : Blo 1668034 3756365 := bbase (se 3 (by rfl) ⟨704318, by rfl⟩ : syracuseStep 3756365 = 1408637) (by norm_num)
theorem B2503013 : Blo 1668034 2503013 := bbase (se 4 (by rfl) ⟨234657, by rfl⟩ : syracuseStep 2503013 = 469315) (by norm_num)
theorem B8450405 : Blo 1668034 8450405 := bbase (se 4 (by rfl) ⟨792225, by rfl⟩ : syracuseStep 8450405 = 1584451) (by norm_num)
theorem B8024437 : Blo 1668034 8024437 := bbase (se 5 (by rfl) ⟨376145, by rfl⟩ : syracuseStep 8024437 = 752291) (by norm_num)
theorem B2503037 : Blo 1668034 2503037 := bbase (se 3 (by rfl) ⟨469319, by rfl⟩ : syracuseStep 2503037 = 938639) (by norm_num)
theorem B2503061 : Blo 1668034 2503061 := bbase (se 6 (by rfl) ⟨58665, by rfl⟩ : syracuseStep 2503061 = 117331) (by norm_num)
theorem B3756437 : Blo 1668034 3756437 := bbase (se 6 (by rfl) ⟨88041, by rfl⟩ : syracuseStep 3756437 = 176083) (by norm_num)
theorem B2503085 : Blo 1668034 2503085 := bbase (se 3 (by rfl) ⟨469328, by rfl⟩ : syracuseStep 2503085 = 938657) (by norm_num)
theorem B9507253 : Blo 1668034 9507253 := bbase (se 5 (by rfl) ⟨445652, by rfl⟩ : syracuseStep 9507253 = 891305) (by norm_num)
theorem B1782209 : Blo 1668034 1782209 := bbase (se 2 (by rfl) ⟨668328, by rfl⟩ : syracuseStep 1782209 = 1336657) (by norm_num)
theorem B2503109 : Blo 1668034 2503109 := bbase (se 4 (by rfl) ⟨234666, by rfl⟩ : syracuseStep 2503109 = 469333) (by norm_num)
theorem B5632469 : Blo 1668034 5632469 := bbase (se 7 (by rfl) ⟨66005, by rfl⟩ : syracuseStep 5632469 = 132011) (by norm_num)
theorem B3166685 : Blo 1668034 3166685 := bbase (se 3 (by rfl) ⟨593753, by rfl⟩ : syracuseStep 3166685 = 1187507) (by norm_num)
theorem B2503133 : Blo 1668034 2503133 := bbase (se 3 (by rfl) ⟨469337, by rfl⟩ : syracuseStep 2503133 = 938675) (by norm_num)
theorem B3756509 : Blo 1668034 3756509 := bbase (se 3 (by rfl) ⟨704345, by rfl⟩ : syracuseStep 3756509 = 1408691) (by norm_num)
theorem B4223461 : Blo 1668034 4223461 := bbase (se 4 (by rfl) ⟨395949, by rfl⟩ : syracuseStep 4223461 = 791899) (by norm_num)
theorem B2503157 : Blo 1668034 2503157 := bbase (se 5 (by rfl) ⟨117335, by rfl⟩ : syracuseStep 2503157 = 234671) (by norm_num)
theorem B2503181 : Blo 1668034 2503181 := bbase (se 3 (by rfl) ⟨469346, by rfl⟩ : syracuseStep 2503181 = 938693) (by norm_num)
theorem B1692181 : Blo 1668034 1692181 := bbase (se 6 (by rfl) ⟨39660, by rfl⟩ : syracuseStep 1692181 = 79321) (by norm_num)
theorem B2503205 : Blo 1668034 2503205 := bbase (se 4 (by rfl) ⟨234675, by rfl⟩ : syracuseStep 2503205 = 469351) (by norm_num)
theorem B6337061 : Blo 1668034 6337061 := bbase (se 4 (by rfl) ⟨594099, by rfl⟩ : syracuseStep 6337061 = 1188199) (by norm_num)
theorem B3756581 : Blo 1668034 3756581 := bbase (se 4 (by rfl) ⟨352179, by rfl⟩ : syracuseStep 3756581 = 704359) (by norm_num)
theorem B1692217 : Blo 1668034 1692217 := bbase (se 2 (by rfl) ⟨634581, by rfl⟩ : syracuseStep 1692217 = 1269163) (by norm_num)
theorem B2503229 : Blo 1668034 2503229 := bbase (se 3 (by rfl) ⟨469355, by rfl⟩ : syracuseStep 2503229 = 938711) (by norm_num)
theorem B1929793 : Blo 1668034 1929793 := bbase (se 2 (by rfl) ⟨723672, by rfl⟩ : syracuseStep 1929793 = 1447345) (by norm_num)
theorem B4223573 : Blo 1668034 4223573 := bbase (se 8 (by rfl) ⟨24747, by rfl⟩ : syracuseStep 4223573 = 49495) (by norm_num)
theorem B2503253 : Blo 1668034 2503253 := bbase (se 8 (by rfl) ⟨14667, by rfl⟩ : syracuseStep 2503253 = 29335) (by norm_num)
theorem B2503277 : Blo 1668034 2503277 := bbase (se 3 (by rfl) ⟨469364, by rfl⟩ : syracuseStep 2503277 = 938729) (by norm_num)
theorem B3756653 : Blo 1668034 3756653 := bbase (se 3 (by rfl) ⟨704372, by rfl⟩ : syracuseStep 3756653 = 1408745) (by norm_num)
theorem B7713397 : Blo 1668034 7713397 := bbase (se 5 (by rfl) ⟨361565, by rfl⟩ : syracuseStep 7713397 = 723131) (by norm_num)
theorem B5345909 : Blo 1668034 5345909 := bbase (se 5 (by rfl) ⟨250589, by rfl⟩ : syracuseStep 5345909 = 501179) (by norm_num)
theorem B8016517 : Blo 1668034 8016517 := bbase (se 4 (by rfl) ⟨751548, by rfl⟩ : syracuseStep 8016517 = 1503097) (by norm_num)
theorem B2503301 : Blo 1668034 2503301 := bbase (se 4 (by rfl) ⟨234684, by rfl⟩ : syracuseStep 2503301 = 469369) (by norm_num)
theorem B2503325 : Blo 1668034 2503325 := bbase (se 3 (by rfl) ⟨469373, by rfl⟩ : syracuseStep 2503325 = 938747) (by norm_num)
theorem B2503349 : Blo 1668034 2503349 := bbase (se 5 (by rfl) ⟨117344, by rfl⟩ : syracuseStep 2503349 = 234689) (by norm_num)
theorem B3756725 : Blo 1668034 3756725 := bbase (se 5 (by rfl) ⟨176096, by rfl⟩ : syracuseStep 3756725 = 352193) (by norm_num)
theorem B2503373 : Blo 1668034 2503373 := bbase (se 3 (by rfl) ⟨469382, by rfl⟩ : syracuseStep 2503373 = 938765) (by norm_num)
theorem B2503397 : Blo 1668034 2503397 := bbase (se 4 (by rfl) ⟨234693, by rfl⟩ : syracuseStep 2503397 = 469387) (by norm_num)
theorem B2503421 : Blo 1668034 2503421 := bbase (se 3 (by rfl) ⟨469391, by rfl⟩ : syracuseStep 2503421 = 938783) (by norm_num)
theorem B3756797 : Blo 1668034 3756797 := bbase (se 3 (by rfl) ⟨704399, by rfl⟩ : syracuseStep 3756797 = 1408799) (by norm_num)
theorem B4223765 : Blo 1668034 4223765 := bbase (se 6 (by rfl) ⟨98994, by rfl⟩ : syracuseStep 4223765 = 197989) (by norm_num)
theorem B2503445 : Blo 1668034 2503445 := bbase (se 6 (by rfl) ⟨58674, by rfl⟩ : syracuseStep 2503445 = 117349) (by norm_num)
theorem B2503469 : Blo 1668034 2503469 := bbase (se 3 (by rfl) ⟨469400, by rfl⟩ : syracuseStep 2503469 = 938801) (by norm_num)
theorem B1692461 : Blo 1668034 1692461 := bbase (se 3 (by rfl) ⟨317336, by rfl⟩ : syracuseStep 1692461 = 634673) (by norm_num)
theorem B2503493 : Blo 1668034 2503493 := bbase (se 4 (by rfl) ⟨234702, by rfl⟩ : syracuseStep 2503493 = 469405) (by norm_num)
theorem B6337349 : Blo 1668034 6337349 := bbase (se 4 (by rfl) ⟨594126, by rfl⟩ : syracuseStep 6337349 = 1188253) (by norm_num)
theorem B3756869 : Blo 1668034 3756869 := bbase (se 4 (by rfl) ⟨352206, by rfl⟩ : syracuseStep 3756869 = 704413) (by norm_num)
theorem B10695509 : Blo 1668034 10695509 := bbase (se 9 (by rfl) ⟨31334, by rfl⟩ : syracuseStep 10695509 = 62669) (by norm_num)
theorem B2503517 : Blo 1668034 2503517 := bbase (se 3 (by rfl) ⟨469409, by rfl⟩ : syracuseStep 2503517 = 938819) (by norm_num)
theorem B2503541 : Blo 1668034 2503541 := bbase (se 5 (by rfl) ⟨117353, by rfl⟩ : syracuseStep 2503541 = 234707) (by norm_num)
theorem B1782653 : Blo 1668034 1782653 := bbase (se 3 (by rfl) ⟨334247, by rfl⟩ : syracuseStep 1782653 = 668495) (by norm_num)
theorem B5632901 : Blo 1668034 5632901 := bbase (se 4 (by rfl) ⟨528084, by rfl⟩ : syracuseStep 5632901 = 1056169) (by norm_num)
theorem B2503565 : Blo 1668034 2503565 := bbase (se 3 (by rfl) ⟨469418, by rfl⟩ : syracuseStep 2503565 = 938837) (by norm_num)
theorem B3756941 : Blo 1668034 3756941 := bbase (se 3 (by rfl) ⟨704426, by rfl⟩ : syracuseStep 3756941 = 1408853) (by norm_num)
theorem B2503589 : Blo 1668034 2503589 := bbase (se 4 (by rfl) ⟨234711, by rfl⟩ : syracuseStep 2503589 = 469423) (by norm_num)
theorem B2503613 : Blo 1668034 2503613 := bbase (se 3 (by rfl) ⟨469427, by rfl⟩ : syracuseStep 2503613 = 938855) (by norm_num)
theorem B2814925 : Blo 1668034 2814925 := bbase (se 3 (by rfl) ⟨527798, by rfl⟩ : syracuseStep 2814925 = 1055597) (by norm_num)
theorem B2503637 : Blo 1668034 2503637 := bbase (se 7 (by rfl) ⟨29339, by rfl⟩ : syracuseStep 2503637 = 58679) (by norm_num)
theorem B3757013 : Blo 1668034 3757013 := bbase (se 7 (by rfl) ⟨44027, by rfl⟩ : syracuseStep 3757013 = 88055) (by norm_num)
theorem B2503661 : Blo 1668034 2503661 := bbase (se 3 (by rfl) ⟨469436, by rfl⟩ : syracuseStep 2503661 = 938873) (by norm_num)
theorem B2503685 : Blo 1668034 2503685 := bbase (se 4 (by rfl) ⟨234720, by rfl⟩ : syracuseStep 2503685 = 469441) (by norm_num)
theorem B2503709 : Blo 1668034 2503709 := bbase (se 3 (by rfl) ⟨469445, by rfl⟩ : syracuseStep 2503709 = 938891) (by norm_num)
theorem B3757085 : Blo 1668034 3757085 := bbase (se 3 (by rfl) ⟨704453, by rfl⟩ : syracuseStep 3757085 = 1408907) (by norm_num)
theorem B2815013 : Blo 1668034 2815013 := bbase (se 4 (by rfl) ⟨263907, by rfl⟩ : syracuseStep 2815013 = 527815) (by norm_num)
theorem B2503733 : Blo 1668034 2503733 := bbase (se 5 (by rfl) ⟨117362, by rfl⟩ : syracuseStep 2503733 = 234725) (by norm_num)
theorem B2503757 : Blo 1668034 2503757 := bbase (se 3 (by rfl) ⟨469454, by rfl⟩ : syracuseStep 2503757 = 938909) (by norm_num)
theorem B2503781 : Blo 1668034 2503781 := bbase (se 4 (by rfl) ⟨234729, by rfl⟩ : syracuseStep 2503781 = 469459) (by norm_num)
theorem B3757157 : Blo 1668034 3757157 := bbase (se 4 (by rfl) ⟨352233, by rfl⟩ : syracuseStep 3757157 = 704467) (by norm_num)
theorem B4224109 : Blo 1668034 4224109 := bbase (se 3 (by rfl) ⟨792020, by rfl⟩ : syracuseStep 4224109 = 1584041) (by norm_num)
theorem B1782901 : Blo 1668034 1782901 := bbase (se 5 (by rfl) ⟨83573, by rfl⟩ : syracuseStep 1782901 = 167147) (by norm_num)
theorem B2503805 : Blo 1668034 2503805 := bbase (se 3 (by rfl) ⟨469463, by rfl⟩ : syracuseStep 2503805 = 938927) (by norm_num)
theorem B2503829 : Blo 1668034 2503829 := bbase (se 6 (by rfl) ⟨58683, by rfl⟩ : syracuseStep 2503829 = 117367) (by norm_num)
theorem B2815141 : Blo 1668034 2815141 := bbase (se 4 (by rfl) ⟨263919, by rfl⟩ : syracuseStep 2815141 = 527839) (by norm_num)
theorem B2503853 : Blo 1668034 2503853 := bbase (se 3 (by rfl) ⟨469472, by rfl⟩ : syracuseStep 2503853 = 938945) (by norm_num)
theorem B3757229 : Blo 1668034 3757229 := bbase (se 3 (by rfl) ⟨704480, by rfl⟩ : syracuseStep 3757229 = 1408961) (by norm_num)
theorem B2503877 : Blo 1668034 2503877 := bbase (se 4 (by rfl) ⟨234738, by rfl⟩ : syracuseStep 2503877 = 469477) (by norm_num)
theorem B3167437 : Blo 1668034 3167437 := bbase (se 3 (by rfl) ⟨593894, by rfl⟩ : syracuseStep 3167437 = 1187789) (by norm_num)
theorem B4224221 : Blo 1668034 4224221 := bbase (se 3 (by rfl) ⟨792041, by rfl⟩ : syracuseStep 4224221 = 1584083) (by norm_num)
theorem B2503901 : Blo 1668034 2503901 := bbase (se 3 (by rfl) ⟨469481, by rfl⟩ : syracuseStep 2503901 = 938963) (by norm_num)
theorem B2503925 : Blo 1668034 2503925 := bbase (se 5 (by rfl) ⟨117371, by rfl⟩ : syracuseStep 2503925 = 234743) (by norm_num)
theorem B3757301 : Blo 1668034 3757301 := bbase (se 5 (by rfl) ⟨176123, by rfl⟩ : syracuseStep 3757301 = 352247) (by norm_num)
theorem B2815229 : Blo 1668034 2815229 := bbase (se 3 (by rfl) ⟨527855, by rfl⟩ : syracuseStep 2815229 = 1055711) (by norm_num)
theorem B2503949 : Blo 1668034 2503949 := bbase (se 3 (by rfl) ⟨469490, by rfl⟩ : syracuseStep 2503949 = 938981) (by norm_num)
theorem B4011277 : Blo 1668034 4011277 := bbase (se 3 (by rfl) ⟨752114, by rfl⟩ : syracuseStep 4011277 = 1504229) (by norm_num)
theorem B2503973 : Blo 1668034 2503973 := bbase (se 4 (by rfl) ⟨234747, by rfl⟩ : syracuseStep 2503973 = 469495) (by norm_num)
theorem B5633333 : Blo 1668034 5633333 := bbase (se 5 (by rfl) ⟨264062, by rfl⟩ : syracuseStep 5633333 = 528125) (by norm_num)
theorem B2503997 : Blo 1668034 2503997 := bbase (se 3 (by rfl) ⟨469499, by rfl⟩ : syracuseStep 2503997 = 938999) (by norm_num)
theorem B3757373 : Blo 1668034 3757373 := bbase (se 3 (by rfl) ⟨704507, by rfl⟩ : syracuseStep 3757373 = 1409015) (by norm_num)
theorem B2504021 : Blo 1668034 2504021 := bbase (se 13 (by rfl) ⟨458, by rfl⟩ : syracuseStep 2504021 = 917) (by norm_num)
theorem B3167581 : Blo 1668034 3167581 := bbase (se 3 (by rfl) ⟨593921, by rfl⟩ : syracuseStep 3167581 = 1187843) (by norm_num)
theorem B2504045 : Blo 1668034 2504045 := bbase (se 3 (by rfl) ⟨469508, by rfl⟩ : syracuseStep 2504045 = 939017) (by norm_num)
theorem B2815357 : Blo 1668034 2815357 := bbase (se 3 (by rfl) ⟨527879, by rfl⟩ : syracuseStep 2815357 = 1055759) (by norm_num)
theorem B2504069 : Blo 1668034 2504069 := bbase (se 4 (by rfl) ⟨234756, by rfl⟩ : syracuseStep 2504069 = 469513) (by norm_num)
theorem B3757445 : Blo 1668034 3757445 := bbase (se 4 (by rfl) ⟨352260, by rfl⟩ : syracuseStep 3757445 = 704521) (by norm_num)
theorem B4224413 : Blo 1668034 4224413 := bbase (se 3 (by rfl) ⟨792077, by rfl⟩ : syracuseStep 4224413 = 1584155) (by norm_num)
theorem B2504093 : Blo 1668034 2504093 := bbase (se 3 (by rfl) ⟨469517, by rfl⟩ : syracuseStep 2504093 = 939035) (by norm_num)
theorem B4339109 : Blo 1668034 4339109 := bbase (se 4 (by rfl) ⟨406791, by rfl⟩ : syracuseStep 4339109 = 813583) (by norm_num)
theorem B2504117 : Blo 1668034 2504117 := bbase (se 5 (by rfl) ⟨117380, by rfl⟩ : syracuseStep 2504117 = 234761) (by norm_num)
theorem B2504141 : Blo 1668034 2504141 := bbase (se 3 (by rfl) ⟨469526, by rfl⟩ : syracuseStep 2504141 = 939053) (by norm_num)
theorem B3757517 : Blo 1668034 3757517 := bbase (se 3 (by rfl) ⟨704534, by rfl⟩ : syracuseStep 3757517 = 1409069) (by norm_num)
theorem B2815445 : Blo 1668034 2815445 := bbase (se 7 (by rfl) ⟨32993, by rfl⟩ : syracuseStep 2815445 = 65987) (by norm_num)
theorem B2004437 : Blo 1668034 2004437 := bbase (se 7 (by rfl) ⟨23489, by rfl⟩ : syracuseStep 2004437 = 46979) (by norm_num)
theorem B2504165 : Blo 1668034 2504165 := bbase (se 4 (by rfl) ⟨234765, by rfl⟩ : syracuseStep 2504165 = 469531) (by norm_num)
theorem B5346805 : Blo 1668034 5346805 := bbase (se 5 (by rfl) ⟨250631, by rfl⟩ : syracuseStep 5346805 = 501263) (by norm_num)
theorem B3167741 : Blo 1668034 3167741 := bbase (se 3 (by rfl) ⟨593951, by rfl⟩ : syracuseStep 3167741 = 1187903) (by norm_num)
theorem B2504189 : Blo 1668034 2504189 := bbase (se 3 (by rfl) ⟨469535, by rfl⟩ : syracuseStep 2504189 = 939071) (by norm_num)
theorem B2504213 : Blo 1668034 2504213 := bbase (se 6 (by rfl) ⟨58692, by rfl⟩ : syracuseStep 2504213 = 117385) (by norm_num)
theorem B2504237 : Blo 1668034 2504237 := bbase (se 3 (by rfl) ⟨469544, by rfl⟩ : syracuseStep 2504237 = 939089) (by norm_num)
theorem B2856493 : Blo 1668034 2856493 := bbase (se 3 (by rfl) ⟨535592, by rfl⟩ : syracuseStep 2856493 = 1071185) (by norm_num)
theorem B1783345 : Blo 1668034 1783345 := bbase (se 2 (by rfl) ⟨668754, by rfl⟩ : syracuseStep 1783345 = 1337509) (by norm_num)
theorem B2504261 : Blo 1668034 2504261 := bbase (se 4 (by rfl) ⟨234774, by rfl⟩ : syracuseStep 2504261 = 469549) (by norm_num)
theorem B2815573 : Blo 1668034 2815573 := bbase (se 8 (by rfl) ⟨16497, by rfl⟩ : syracuseStep 2815573 = 32995) (by norm_num)
theorem B2504285 : Blo 1668034 2504285 := bbase (se 3 (by rfl) ⟨469553, by rfl⟩ : syracuseStep 2504285 = 939107) (by norm_num)
theorem B8451701 : Blo 1668034 8451701 := bbase (se 5 (by rfl) ⟨396173, by rfl⟩ : syracuseStep 8451701 = 792347) (by norm_num)
theorem B2504309 : Blo 1668034 2504309 := bbase (se 5 (by rfl) ⟨117389, by rfl⟩ : syracuseStep 2504309 = 234779) (by norm_num)
theorem B2111113 : Blo 1668034 2111113 := bbase (se 2 (by rfl) ⟨791667, by rfl⟩ : syracuseStep 2111113 = 1583335) (by norm_num)
theorem B3167885 : Blo 1668034 3167885 := bbase (se 3 (by rfl) ⟨593978, by rfl⟩ : syracuseStep 3167885 = 1187957) (by norm_num)
theorem B2504333 : Blo 1668034 2504333 := bbase (se 3 (by rfl) ⟨469562, by rfl⟩ : syracuseStep 2504333 = 939125) (by norm_num)
theorem B2004625 : Blo 1668034 2004625 := bbase (se 2 (by rfl) ⟨751734, by rfl⟩ : syracuseStep 2004625 = 1503469) (by norm_num)
theorem B2504357 : Blo 1668034 2504357 := bbase (se 4 (by rfl) ⟨234783, by rfl⟩ : syracuseStep 2504357 = 469567) (by norm_num)
theorem B2815661 : Blo 1668034 2815661 := bbase (se 3 (by rfl) ⟨527936, by rfl⟩ : syracuseStep 2815661 = 1055873) (by norm_num)
theorem B2504381 : Blo 1668034 2504381 := bbase (se 3 (by rfl) ⟨469571, by rfl⟩ : syracuseStep 2504381 = 939143) (by norm_num)
theorem B5076677 : Blo 1668034 5076677 := bbase (se 4 (by rfl) ⟨475938, by rfl⟩ : syracuseStep 5076677 = 951877) (by norm_num)
theorem B2504405 : Blo 1668034 2504405 := bbase (se 7 (by rfl) ⟨29348, by rfl⟩ : syracuseStep 2504405 = 58697) (by norm_num)
theorem B27080405 : Blo 1668034 27080405 := bbase (se 7 (by rfl) ⟨317348, by rfl⟩ : syracuseStep 27080405 = 634697) (by norm_num)
theorem B5633765 : Blo 1668034 5633765 := bbase (se 4 (by rfl) ⟨528165, by rfl⟩ : syracuseStep 5633765 = 1056331) (by norm_num)
theorem B2504429 : Blo 1668034 2504429 := bbase (se 3 (by rfl) ⟨469580, by rfl⟩ : syracuseStep 2504429 = 939161) (by norm_num)
theorem B4511477 : Blo 1668034 4511477 := bbase (se 5 (by rfl) ⟨211475, by rfl⟩ : syracuseStep 4511477 = 422951) (by norm_num)
theorem B4224757 : Blo 1668034 4224757 := bbase (se 5 (by rfl) ⟨198035, by rfl⟩ : syracuseStep 4224757 = 396071) (by norm_num)
theorem B2504453 : Blo 1668034 2504453 := bbase (se 4 (by rfl) ⟨234792, by rfl⟩ : syracuseStep 2504453 = 469585) (by norm_num)
theorem B2504477 : Blo 1668034 2504477 := bbase (se 3 (by rfl) ⟨469589, by rfl⟩ : syracuseStep 2504477 = 939179) (by norm_num)
theorem B2815789 : Blo 1668034 2815789 := bbase (se 3 (by rfl) ⟨527960, by rfl⟩ : syracuseStep 2815789 = 1055921) (by norm_num)
theorem B2111285 : Blo 1668034 2111285 := bbase (se 5 (by rfl) ⟨98966, by rfl⟩ : syracuseStep 2111285 = 197933) (by norm_num)
theorem B2504501 : Blo 1668034 2504501 := bbase (se 5 (by rfl) ⟨117398, by rfl⟩ : syracuseStep 2504501 = 234797) (by norm_num)
theorem B2504525 : Blo 1668034 2504525 := bbase (se 3 (by rfl) ⟨469598, by rfl⟩ : syracuseStep 2504525 = 939197) (by norm_num)
theorem B4224869 : Blo 1668034 4224869 := bbase (se 4 (by rfl) ⟨396081, by rfl⟩ : syracuseStep 4224869 = 792163) (by norm_num)
theorem B2504549 : Blo 1668034 2504549 := bbase (se 4 (by rfl) ⟨234801, by rfl⟩ : syracuseStep 2504549 = 469603) (by norm_num)
theorem B2004841 : Blo 1668034 2004841 := bbase (se 2 (by rfl) ⟨751815, by rfl⟩ : syracuseStep 2004841 = 1503631) (by norm_num)
theorem B2111341 : Blo 1668034 2111341 := bbase (se 3 (by rfl) ⟨395876, by rfl⟩ : syracuseStep 2111341 = 791753) (by norm_num)
theorem B4011893 : Blo 1668034 4011893 := bbase (se 5 (by rfl) ⟨188057, by rfl⟩ : syracuseStep 4011893 = 376115) (by norm_num)
theorem B2504573 : Blo 1668034 2504573 := bbase (se 3 (by rfl) ⟨469607, by rfl⟩ : syracuseStep 2504573 = 939215) (by norm_num)
theorem B2815877 : Blo 1668034 2815877 := bbase (se 4 (by rfl) ⟨263988, by rfl⟩ : syracuseStep 2815877 = 527977) (by norm_num)
theorem B5347205 : Blo 1668034 5347205 := bbase (se 4 (by rfl) ⟨501300, by rfl⟩ : syracuseStep 5347205 = 1002601) (by norm_num)
theorem B2504597 : Blo 1668034 2504597 := bbase (se 6 (by rfl) ⟨58701, by rfl⟩ : syracuseStep 2504597 = 117403) (by norm_num)
theorem B3168173 : Blo 1668034 3168173 := bbase (se 3 (by rfl) ⟨594032, by rfl⟩ : syracuseStep 3168173 = 1188065) (by norm_num)
theorem B2504621 : Blo 1668034 2504621 := bbase (se 3 (by rfl) ⟨469616, by rfl⟩ : syracuseStep 2504621 = 939233) (by norm_num)
theorem B4011949 : Blo 1668034 4011949 := bbase (se 3 (by rfl) ⟨752240, by rfl⟩ : syracuseStep 4011949 = 1504481) (by norm_num)
theorem B2504645 : Blo 1668034 2504645 := bbase (se 4 (by rfl) ⟨234810, by rfl⟩ : syracuseStep 2504645 = 469621) (by norm_num)
theorem B2111437 : Blo 1668034 2111437 := bbase (se 3 (by rfl) ⟨395894, by rfl⟩ : syracuseStep 2111437 = 791789) (by norm_num)
theorem B2504669 : Blo 1668034 2504669 := bbase (se 3 (by rfl) ⟨469625, by rfl⟩ : syracuseStep 2504669 = 939251) (by norm_num)
theorem B6338533 : Blo 1668034 6338533 := bbase (se 4 (by rfl) ⟨594237, by rfl⟩ : syracuseStep 6338533 = 1188475) (by norm_num)
theorem B2504693 : Blo 1668034 2504693 := bbase (se 5 (by rfl) ⟨117407, by rfl⟩ : syracuseStep 2504693 = 234815) (by norm_num)
theorem B2816005 : Blo 1668034 2816005 := bbase (se 4 (by rfl) ⟨264000, by rfl⟩ : syracuseStep 2816005 = 528001) (by norm_num)
theorem B2504717 : Blo 1668034 2504717 := bbase (se 3 (by rfl) ⟨469634, by rfl⟩ : syracuseStep 2504717 = 939269) (by norm_num)
theorem B4225061 : Blo 1668034 4225061 := bbase (se 4 (by rfl) ⟨396099, by rfl⟩ : syracuseStep 4225061 = 792199) (by norm_num)
theorem B2504741 : Blo 1668034 2504741 := bbase (se 4 (by rfl) ⟨234819, by rfl⟩ : syracuseStep 2504741 = 469639) (by norm_num)
theorem B2504765 : Blo 1668034 2504765 := bbase (se 3 (by rfl) ⟨469643, by rfl⟩ : syracuseStep 2504765 = 939287) (by norm_num)
theorem B3168325 : Blo 1668034 3168325 := bbase (se 4 (by rfl) ⟨297030, by rfl⟩ : syracuseStep 3168325 = 594061) (by norm_num)
theorem B12679253 : Blo 1668034 12679253 := bbase (se 8 (by rfl) ⟨74292, by rfl⟩ : syracuseStep 12679253 = 148585) (by norm_num)
theorem B2504789 : Blo 1668034 2504789 := bbase (se 8 (by rfl) ⟨14676, by rfl⟩ : syracuseStep 2504789 = 29353) (by norm_num)
theorem B2816093 : Blo 1668034 2816093 := bbase (se 3 (by rfl) ⟨528017, by rfl⟩ : syracuseStep 2816093 = 1056035) (by norm_num)
theorem B2504813 : Blo 1668034 2504813 := bbase (se 3 (by rfl) ⟨469652, by rfl⟩ : syracuseStep 2504813 = 939305) (by norm_num)
theorem B2111609 : Blo 1668034 2111609 := bbase (se 2 (by rfl) ⟨791853, by rfl⟩ : syracuseStep 2111609 = 1583707) (by norm_num)
theorem B2504837 : Blo 1668034 2504837 := bbase (se 4 (by rfl) ⟨234828, by rfl⟩ : syracuseStep 2504837 = 469657) (by norm_num)
theorem B2005129 : Blo 1668034 2005129 := bbase (se 2 (by rfl) ⟨751923, by rfl⟩ : syracuseStep 2005129 = 1503847) (by norm_num)
theorem B5634197 : Blo 1668034 5634197 := bbase (se 6 (by rfl) ⟨132051, by rfl⟩ : syracuseStep 5634197 = 264103) (by norm_num)
theorem B2504861 : Blo 1668034 2504861 := bbase (se 3 (by rfl) ⟨469661, by rfl⟩ : syracuseStep 2504861 = 939323) (by norm_num)
theorem B2111665 : Blo 1668034 2111665 := bbase (se 2 (by rfl) ⟨791874, by rfl⟩ : syracuseStep 2111665 = 1583749) (by norm_num)
theorem B16046261 : Blo 1668034 16046261 := bbase (se 5 (by rfl) ⟨752168, by rfl⟩ : syracuseStep 16046261 = 1504337) (by norm_num)
theorem B2504885 : Blo 1668034 2504885 := bbase (se 5 (by rfl) ⟨117416, by rfl⟩ : syracuseStep 2504885 = 234833) (by norm_num)
theorem B2504909 : Blo 1668034 2504909 := bbase (se 3 (by rfl) ⟨469670, by rfl⟩ : syracuseStep 2504909 = 939341) (by norm_num)
theorem B2816221 : Blo 1668034 2816221 := bbase (se 3 (by rfl) ⟨528041, by rfl⟩ : syracuseStep 2816221 = 1056083) (by norm_num)
theorem B2504933 : Blo 1668034 2504933 := bbase (se 4 (by rfl) ⟨234837, by rfl⟩ : syracuseStep 2504933 = 469675) (by norm_num)
theorem B2504957 : Blo 1668034 2504957 := bbase (se 3 (by rfl) ⟨469679, by rfl⟩ : syracuseStep 2504957 = 939359) (by norm_num)
theorem B2111761 : Blo 1668034 2111761 := bbase (se 2 (by rfl) ⟨791910, by rfl⟩ : syracuseStep 2111761 = 1583821) (by norm_num)
theorem B12024085 : Blo 1668034 12024085 := bbase (se 6 (by rfl) ⟨281814, by rfl⟩ : syracuseStep 12024085 = 563629) (by norm_num)
theorem B6338837 : Blo 1668034 6338837 := bbase (se 6 (by rfl) ⟨148566, by rfl⟩ : syracuseStep 6338837 = 297133) (by norm_num)
theorem B2504981 : Blo 1668034 2504981 := bbase (se 6 (by rfl) ⟨58710, by rfl⟩ : syracuseStep 2504981 = 117421) (by norm_num)
theorem B2505005 : Blo 1668034 2505005 := bbase (se 3 (by rfl) ⟨469688, by rfl⟩ : syracuseStep 2505005 = 939377) (by norm_num)
theorem B2816309 : Blo 1668034 2816309 := bbase (se 5 (by rfl) ⟨132014, by rfl⟩ : syracuseStep 2816309 = 264029) (by norm_num)
theorem B2505029 : Blo 1668034 2505029 := bbase (se 4 (by rfl) ⟨234846, by rfl⟩ : syracuseStep 2505029 = 469693) (by norm_num)
theorem B3168629 : Blo 1668034 3168629 := bbase (se 5 (by rfl) ⟨148529, by rfl⟩ : syracuseStep 3168629 = 297059) (by norm_num)
theorem B9509237 : Blo 1668034 9509237 := bbase (se 5 (by rfl) ⟨445745, by rfl⟩ : syracuseStep 9509237 = 891491) (by norm_num)
theorem B4225405 : Blo 1668034 4225405 := bbase (se 3 (by rfl) ⟨792263, by rfl⟩ : syracuseStep 4225405 = 1584527) (by norm_num)
theorem B2816437 : Blo 1668034 2816437 := bbase (se 5 (by rfl) ⟨132020, by rfl⟩ : syracuseStep 2816437 = 264041) (by norm_num)
theorem B2111933 : Blo 1668034 2111933 := bbase (se 3 (by rfl) ⟨395987, by rfl⟩ : syracuseStep 2111933 = 791975) (by norm_num)
theorem B3807701 : Blo 1668034 3807701 := bbase (se 7 (by rfl) ⟨44621, by rfl⟩ : syracuseStep 3807701 = 89243) (by norm_num)
theorem B4225517 : Blo 1668034 4225517 := bbase (se 3 (by rfl) ⟨792284, by rfl⟩ : syracuseStep 4225517 = 1584569) (by norm_num)
theorem B12671477 : Blo 1668034 12671477 := bbase (se 5 (by rfl) ⟨593975, by rfl⟩ : syracuseStep 12671477 = 1187951) (by norm_num)
theorem B2111989 : Blo 1668034 2111989 := bbase (se 5 (by rfl) ⟨98999, by rfl⟩ : syracuseStep 2111989 = 197999) (by norm_num)
theorem B2816525 : Blo 1668034 2816525 := bbase (se 3 (by rfl) ⟨528098, by rfl⟩ : syracuseStep 2816525 = 1056197) (by norm_num)
theorem B4512277 : Blo 1668034 4512277 := bbase (se 6 (by rfl) ⟨105756, by rfl⟩ : syracuseStep 4512277 = 211513) (by norm_num)
theorem B5634629 : Blo 1668034 5634629 := bbase (se 4 (by rfl) ⟨528246, by rfl⟩ : syracuseStep 5634629 = 1056493) (by norm_num)
theorem B2112085 : Blo 1668034 2112085 := bbase (se 8 (by rfl) ⟨12375, by rfl⟩ : syracuseStep 2112085 = 24751) (by norm_num)
theorem B10156661 : Blo 1668034 10156661 := bbase (se 5 (by rfl) ⟨476093, by rfl⟩ : syracuseStep 10156661 = 952187) (by norm_num)
theorem B2816653 : Blo 1668034 2816653 := bbase (se 3 (by rfl) ⟨528122, by rfl⟩ : syracuseStep 2816653 = 1056245) (by norm_num)
theorem B4225709 : Blo 1668034 4225709 := bbase (se 3 (by rfl) ⟨792320, by rfl⟩ : syracuseStep 4225709 = 1584641) (by norm_num)
theorem B5421781 : Blo 1668034 5421781 := bbase (se 7 (by rfl) ⟨63536, by rfl⟩ : syracuseStep 5421781 = 127073) (by norm_num)
theorem B2816741 : Blo 1668034 2816741 := bbase (se 4 (by rfl) ⟨264069, by rfl⟩ : syracuseStep 2816741 = 528139) (by norm_num)
theorem B2112257 : Blo 1668034 2112257 := bbase (se 2 (by rfl) ⟨792096, by rfl⟩ : syracuseStep 2112257 = 1584193) (by norm_num)
theorem B2112313 : Blo 1668034 2112313 := bbase (se 2 (by rfl) ⟨792117, by rfl⟩ : syracuseStep 2112313 = 1584235) (by norm_num)
theorem B2816869 : Blo 1668034 2816869 := bbase (se 4 (by rfl) ⟨264081, by rfl⟩ : syracuseStep 2816869 = 528163) (by norm_num)
theorem B8452997 : Blo 1668034 8452997 := bbase (se 4 (by rfl) ⟨792468, by rfl⟩ : syracuseStep 8452997 = 1584937) (by norm_num)
theorem B3382165 : Blo 1668034 3382165 := bbase (se 6 (by rfl) ⟨79269, by rfl⟩ : syracuseStep 3382165 = 158539) (by norm_num)
theorem B2112409 : Blo 1668034 2112409 := bbase (se 2 (by rfl) ⟨792153, by rfl⟩ : syracuseStep 2112409 = 1584307) (by norm_num)
theorem B6011813 : Blo 1668034 6011813 := bbase (se 4 (by rfl) ⟨563607, by rfl⟩ : syracuseStep 6011813 = 1127215) (by norm_num)
theorem B2816957 : Blo 1668034 2816957 := bbase (se 3 (by rfl) ⟨528179, by rfl⟩ : syracuseStep 2816957 = 1056359) (by norm_num)
theorem B3382229 : Blo 1668034 3382229 := bbase (se 7 (by rfl) ⟨39635, by rfl⟩ : syracuseStep 3382229 = 79271) (by norm_num)
theorem B7322581 : Blo 1668034 7322581 := bbase (se 7 (by rfl) ⟨85811, by rfl⟩ : syracuseStep 7322581 = 171623) (by norm_num)
theorem B5635061 : Blo 1668034 5635061 := bbase (se 5 (by rfl) ⟨264143, by rfl⟩ : syracuseStep 5635061 = 528287) (by norm_num)
theorem B10845173 : Blo 1668034 10845173 := bbase (se 5 (by rfl) ⟨508367, by rfl⟩ : syracuseStep 10845173 = 1016735) (by norm_num)
theorem B5790709 : Blo 1668034 5790709 := bbase (se 5 (by rfl) ⟨271439, by rfl⟩ : syracuseStep 5790709 = 542879) (by norm_num)
theorem B4226053 : Blo 1668034 4226053 := bbase (se 4 (by rfl) ⟨396192, by rfl⟩ : syracuseStep 4226053 = 792385) (by norm_num)
theorem B2817085 : Blo 1668034 2817085 := bbase (se 3 (by rfl) ⟨528203, by rfl⟩ : syracuseStep 2817085 = 1056407) (by norm_num)
theorem B2112581 : Blo 1668034 2112581 := bbase (se 4 (by rfl) ⟨198054, by rfl⟩ : syracuseStep 2112581 = 396109) (by norm_num)
theorem B3562589 : Blo 1668034 3562589 := bbase (se 3 (by rfl) ⟨667985, by rfl⟩ : syracuseStep 3562589 = 1335971) (by norm_num)
theorem B3169381 : Blo 1668034 3169381 := bbase (se 4 (by rfl) ⟨297129, by rfl⟩ : syracuseStep 3169381 = 594259) (by norm_num)
theorem B4226165 : Blo 1668034 4226165 := bbase (se 5 (by rfl) ⟨198101, by rfl⟩ : syracuseStep 4226165 = 396203) (by norm_num)
theorem B2112637 : Blo 1668034 2112637 := bbase (se 3 (by rfl) ⟨396119, by rfl⟩ : syracuseStep 2112637 = 792239) (by norm_num)
theorem B2817173 : Blo 1668034 2817173 := bbase (se 6 (by rfl) ⟨66027, by rfl⟩ : syracuseStep 2817173 = 132055) (by norm_num)
theorem B2112733 : Blo 1668034 2112733 := bbase (se 3 (by rfl) ⟨396137, by rfl⟩ : syracuseStep 2112733 = 792275) (by norm_num)
theorem B3169525 : Blo 1668034 3169525 := bbase (se 5 (by rfl) ⟨148571, by rfl⟩ : syracuseStep 3169525 = 297143) (by norm_num)
theorem B2817301 : Blo 1668034 2817301 := bbase (se 6 (by rfl) ⟨66030, by rfl⟩ : syracuseStep 2817301 = 132061) (by norm_num)
theorem B8445221 : Blo 1668034 8445221 := bbase (se 4 (by rfl) ⟨791739, by rfl⟩ : syracuseStep 8445221 = 1583479) (by norm_num)
theorem B7126325 : Blo 1668034 7126325 := bbase (se 5 (by rfl) ⟨334046, by rfl⟩ : syracuseStep 7126325 = 668093) (by norm_num)
theorem B4226357 : Blo 1668034 4226357 := bbase (se 5 (by rfl) ⟨198110, by rfl⟩ : syracuseStep 4226357 = 396221) (by norm_num)
theorem B2817389 : Blo 1668034 2817389 := bbase (se 3 (by rfl) ⟨528260, by rfl⟩ : syracuseStep 2817389 = 1056521) (by norm_num)
theorem B2112905 : Blo 1668034 2112905 := bbase (se 2 (by rfl) ⟨792339, by rfl⟩ : syracuseStep 2112905 = 1584679) (by norm_num)
theorem B3169685 : Blo 1668034 3169685 := bbase (se 6 (by rfl) ⟨74289, by rfl⟩ : syracuseStep 3169685 = 148579) (by norm_num)
theorem B2375077 : Blo 1668034 2375077 := bbase (se 4 (by rfl) ⟨222663, by rfl⟩ : syracuseStep 2375077 = 445327) (by norm_num)
theorem B4750757 : Blo 1668034 4750757 := bbase (se 4 (by rfl) ⟨445383, by rfl⟩ : syracuseStep 4750757 = 890767) (by norm_num)
theorem B5635493 : Blo 1668034 5635493 := bbase (se 4 (by rfl) ⟨528327, by rfl⟩ : syracuseStep 5635493 = 1056655) (by norm_num)
theorem B2112961 : Blo 1668034 2112961 := bbase (se 2 (by rfl) ⟨792360, by rfl⟩ : syracuseStep 2112961 = 1584721) (by norm_num)
theorem B3562957 : Blo 1668034 3562957 := bbase (se 3 (by rfl) ⟨668054, by rfl⟩ : syracuseStep 3562957 = 1336109) (by norm_num)
theorem B2817517 : Blo 1668034 2817517 := bbase (se 3 (by rfl) ⟨528284, by rfl⟩ : syracuseStep 2817517 = 1056569) (by norm_num)
theorem B2375173 : Blo 1668034 2375173 := bbase (se 4 (by rfl) ⟨222672, by rfl⟩ : syracuseStep 2375173 = 445345) (by norm_num)
theorem B3382813 : Blo 1668034 3382813 := bbase (se 3 (by rfl) ⟨634277, by rfl⟩ : syracuseStep 3382813 = 1268555) (by norm_num)
theorem B2113057 : Blo 1668034 2113057 := bbase (se 2 (by rfl) ⟨792396, by rfl⟩ : syracuseStep 2113057 = 1584793) (by norm_num)
theorem B3169829 : Blo 1668034 3169829 := bbase (se 4 (by rfl) ⟨297171, by rfl⟩ : syracuseStep 3169829 = 594343) (by norm_num)
theorem B2817605 : Blo 1668034 2817605 := bbase (se 4 (by rfl) ⟨264150, by rfl⟩ : syracuseStep 2817605 = 528301) (by norm_num)
theorem B7126613 : Blo 1668034 7126613 := bbase (se 8 (by rfl) ⟨41757, by rfl⟩ : syracuseStep 7126613 = 83515) (by norm_num)
theorem B3210877 : Blo 1668034 3210877 := bbase (se 3 (by rfl) ⟨602039, by rfl⟩ : syracuseStep 3210877 = 1204079) (by norm_num)
theorem B4226701 : Blo 1668034 4226701 := bbase (se 3 (by rfl) ⟨792506, by rfl⟩ : syracuseStep 4226701 = 1585013) (by norm_num)
theorem B2817733 : Blo 1668034 2817733 := bbase (se 4 (by rfl) ⟨264162, by rfl⟩ : syracuseStep 2817733 = 528325) (by norm_num)
theorem B2113229 : Blo 1668034 2113229 := bbase (se 3 (by rfl) ⟨396230, by rfl⟩ : syracuseStep 2113229 = 792461) (by norm_num)
theorem B4226813 : Blo 1668034 4226813 := bbase (se 3 (by rfl) ⟨792527, by rfl⟩ : syracuseStep 4226813 = 1585055) (by norm_num)
theorem B2113285 : Blo 1668034 2113285 := bbase (se 4 (by rfl) ⟨198120, by rfl⟩ : syracuseStep 2113285 = 396241) (by norm_num)
theorem B2817821 : Blo 1668034 2817821 := bbase (se 3 (by rfl) ⟨528341, by rfl⟩ : syracuseStep 2817821 = 1056683) (by norm_num)
theorem B3170117 : Blo 1668034 3170117 := bbase (se 4 (by rfl) ⟨297198, by rfl⟩ : syracuseStep 3170117 = 594397) (by norm_num)
theorem B5635925 : Blo 1668034 5635925 := bbase (se 9 (by rfl) ⟨16511, by rfl⟩ : syracuseStep 5635925 = 33023) (by norm_num)
theorem B2113381 : Blo 1668034 2113381 := bbase (se 4 (by rfl) ⟨198129, by rfl⟩ : syracuseStep 2113381 = 396259) (by norm_num)
theorem B2817949 : Blo 1668034 2817949 := bbase (se 3 (by rfl) ⟨528365, by rfl⟩ : syracuseStep 2817949 = 1056731) (by norm_num)
theorem B4227005 : Blo 1668034 4227005 := bbase (se 3 (by rfl) ⟨792563, by rfl⟩ : syracuseStep 4227005 = 1585127) (by norm_num)
theorem B12189653 : Blo 1668034 12189653 := bbase (se 7 (by rfl) ⟨142847, by rfl⟩ : syracuseStep 12189653 = 285695) (by norm_num)
theorem B3170269 : Blo 1668034 3170269 := bbase (se 3 (by rfl) ⟨594425, by rfl⟩ : syracuseStep 3170269 = 1188851) (by norm_num)
theorem B2375669 : Blo 1668034 2375669 := bbase (se 5 (by rfl) ⟨111359, by rfl⟩ : syracuseStep 2375669 = 222719) (by norm_num)
theorem B8568821 : Blo 1668034 8568821 := bbase (se 5 (by rfl) ⟨401663, by rfl⟩ : syracuseStep 8568821 = 803327) (by norm_num)
theorem B4513781 : Blo 1668034 4513781 := bbase (se 5 (by rfl) ⟨211583, by rfl⟩ : syracuseStep 4513781 = 423167) (by norm_num)
theorem B2818037 : Blo 1668034 2818037 := bbase (se 5 (by rfl) ⟨132095, by rfl⟩ : syracuseStep 2818037 = 264191) (by norm_num)
theorem B4816913 : Blo 1668034 4816913 := bstep (se 2 (by rfl) ⟨1806342, by rfl⟩ : syracuseStep 4816913 = 3612685) B3612685
theorem B5636141 : Blo 1668034 5636141 := bstep (se 3 (by rfl) ⟨1056776, by rfl⟩ : syracuseStep 5636141 = 2113553) B2113553
theorem B3170353 : Blo 1668034 3170353 := bstep (se 2 (by rfl) ⟨1188882, by rfl⟩ : syracuseStep 3170353 = 2377765) B2377765
theorem B2375777 : Blo 1668034 2375777 := bstep (se 2 (by rfl) ⟨890916, by rfl⟩ : syracuseStep 2375777 = 1781833) B1781833
theorem B5636195 : Blo 1668034 5636195 := bstep (se 1 (by rfl) ⟨4227146, by rfl⟩ : syracuseStep 5636195 = 8454293) B8454293
theorem B2818145 : Blo 1668034 2818145 := bstep (se 2 (by rfl) ⟨1056804, by rfl⟩ : syracuseStep 2818145 = 2113609) B2113609
theorem B4817009 : Blo 1668034 4817009 := bstep (se 2 (by rfl) ⟨1806378, by rfl⟩ : syracuseStep 4817009 = 3612757) B3612757
theorem B8446193 : Blo 1668034 8446193 := bstep (se 2 (by rfl) ⟨3167322, by rfl⟩ : syracuseStep 8446193 = 6334645) B6334645
theorem B16032113 : Blo 1668034 16032113 := bstep (se 2 (by rfl) ⟨6012042, by rfl⟩ : syracuseStep 16032113 = 12024085) B12024085
theorem B12673421 : Blo 1668034 12673421 := bstep (se 3 (by rfl) ⟨2376266, by rfl⟩ : syracuseStep 12673421 = 4752533) B4752533
theorem B3563939 : Blo 1668034 3563939 := bstep (se 1 (by rfl) ⟨2672954, by rfl⟩ : syracuseStep 3563939 = 5345909) B5345909
theorem B9503153 : Blo 1668034 9503153 := bstep (se 2 (by rfl) ⟨3563682, by rfl⟩ : syracuseStep 9503153 = 7127365) B7127365
theorem B10699249 : Blo 1668034 10699249 := bstep (se 2 (by rfl) ⟨4012218, by rfl⟩ : syracuseStep 10699249 = 8024437) B8024437
theorem B4751885 : Blo 1668034 4751885 := bstep (se 3 (by rfl) ⟨890978, by rfl⟩ : syracuseStep 4751885 = 1781957) B1781957
theorem B2376307 : Blo 1668034 2376307 := bstep (se 1 (by rfl) ⟨1782230, by rfl⟩ : syracuseStep 2376307 = 3564461) B3564461
theorem B1876675 : Blo 1668034 1876675 := bstep (se 1 (by rfl) ⟨1407506, by rfl⟩ : syracuseStep 1876675 = 2815013) B2815013
theorem B4752067 : Blo 1668034 4752067 := bstep (se 1 (by rfl) ⟨3564050, by rfl⟩ : syracuseStep 4752067 = 7128101) B7128101
theorem B6095587 : Blo 1668034 6095587 := bstep (se 1 (by rfl) ⟨4571690, by rfl⟩ : syracuseStep 6095587 = 9143381) B9143381
theorem B2573057 : Blo 1668034 2573057 := bstep (se 2 (by rfl) ⟨964896, by rfl⟩ : syracuseStep 2573057 = 1929793) B1929793
theorem B1876819 : Blo 1668034 1876819 := bstep (se 1 (by rfl) ⟨1407614, by rfl⟩ : syracuseStep 1876819 = 2815229) B2815229
theorem B3212131 : Blo 1668034 3212131 := bstep (se 1 (by rfl) ⟨2409098, by rfl⟩ : syracuseStep 3212131 = 4818197) B4818197
theorem B4064195 : Blo 1668034 4064195 := bstep (se 1 (by rfl) ⟨3048146, by rfl⟩ : syracuseStep 4064195 = 6096293) B6096293
theorem B2376643 : Blo 1668034 2376643 := bstep (se 1 (by rfl) ⟨1782482, by rfl⟩ : syracuseStep 2376643 = 3564965) B3564965
theorem B1876963 : Blo 1668034 1876963 := bstep (se 1 (by rfl) ⟨1407722, by rfl⟩ : syracuseStep 1876963 = 2815445) B2815445
theorem B1877107 : Blo 1668034 1877107 := bstep (se 1 (by rfl) ⟨1407830, by rfl⟩ : syracuseStep 1877107 = 2815661) B2815661
theorem B3384451 : Blo 1668034 3384451 := bstep (se 1 (by rfl) ⟨2538338, by rfl⟩ : syracuseStep 3384451 = 5076677) B5076677
theorem B4752557 : Blo 1668034 4752557 := bstep (se 3 (by rfl) ⟨891104, by rfl⟩ : syracuseStep 4752557 = 1782209) B1782209
theorem B1877251 : Blo 1668034 1877251 := bstep (se 1 (by rfl) ⟨1407938, by rfl⟩ : syracuseStep 1877251 = 2815877) B2815877
theorem B3564803 : Blo 1668034 3564803 := bstep (se 1 (by rfl) ⟨2673602, by rfl⟩ : syracuseStep 3564803 = 5347205) B5347205
theorem B3753233 : Blo 1668034 3753233 := bstep (se 2 (by rfl) ⟨1407462, by rfl⟩ : syracuseStep 3753233 = 2814925) B2814925
theorem B3753251 : Blo 1668034 3753251 := bstep (se 1 (by rfl) ⟨2814938, by rfl⟩ : syracuseStep 3753251 = 5629877) B5629877
theorem B3564913 : Blo 1668034 3564913 := bstep (se 2 (by rfl) ⟨1336842, by rfl⟩ : syracuseStep 3564913 = 2673685) B2673685
theorem B1877395 : Blo 1668034 1877395 := bstep (se 1 (by rfl) ⟨1408046, by rfl⟩ : syracuseStep 1877395 = 2816093) B2816093
theorem B2377201 : Blo 1668034 2377201 := bstep (se 2 (by rfl) ⟨891450, by rfl⟩ : syracuseStep 2377201 = 1782901) B1782901
theorem B2672147 : Blo 1668034 2672147 := bstep (se 1 (by rfl) ⟨2004110, by rfl⟩ : syracuseStep 2672147 = 4008221) B4008221
theorem B2377235 : Blo 1668034 2377235 := bstep (se 1 (by rfl) ⟨1782926, by rfl⟩ : syracuseStep 2377235 = 3565853) B3565853
theorem B1877539 : Blo 1668034 1877539 := bstep (se 1 (by rfl) ⟨1408154, by rfl⟩ : syracuseStep 1877539 = 2816309) B2816309
theorem B3753521 : Blo 1668034 3753521 := bstep (se 2 (by rfl) ⟨1407570, by rfl⟩ : syracuseStep 3753521 = 2815141) B2815141
theorem B3753539 : Blo 1668034 3753539 := bstep (se 1 (by rfl) ⟨2815154, by rfl⟩ : syracuseStep 3753539 = 5630309) B5630309
theorem B2672275 : Blo 1668034 2672275 := bstep (se 1 (by rfl) ⟨2004206, by rfl⟩ : syracuseStep 2672275 = 4008413) B4008413
theorem B8447651 : Blo 1668034 8447651 := bstep (se 1 (by rfl) ⟨6335738, by rfl⟩ : syracuseStep 8447651 = 12671477) B12671477
theorem B1877683 : Blo 1668034 1877683 := bstep (se 1 (by rfl) ⟨1408262, by rfl⟩ : syracuseStep 1877683 = 2816525) B2816525
theorem B1877827 : Blo 1668034 1877827 := bstep (se 1 (by rfl) ⟨1408370, by rfl⟩ : syracuseStep 1877827 = 2816741) B2816741
theorem B3753809 : Blo 1668034 3753809 := bstep (se 2 (by rfl) ⟨1407678, by rfl⟩ : syracuseStep 3753809 = 2815357) B2815357
theorem B3753827 : Blo 1668034 3753827 := bstep (se 1 (by rfl) ⟨2815370, by rfl⟩ : syracuseStep 3753827 = 5630741) B5630741
theorem B9504611 : Blo 1668034 9504611 := bstep (se 1 (by rfl) ⟨7128458, by rfl⟩ : syracuseStep 9504611 = 14256917) B14256917
theorem B10692485 : Blo 1668034 10692485 := bstep (se 4 (by rfl) ⟨1002420, by rfl⟩ : syracuseStep 10692485 = 2004841) B2004841
theorem B4007875 : Blo 1668034 4007875 := bstep (se 1 (by rfl) ⟨3005906, by rfl⟩ : syracuseStep 4007875 = 6011813) B6011813
theorem B1877971 : Blo 1668034 1877971 := bstep (se 1 (by rfl) ⟨1408478, by rfl⟩ : syracuseStep 1877971 = 2816957) B2816957
theorem B2254819 : Blo 1668034 2254819 := bstep (se 1 (by rfl) ⟨1691114, by rfl⟩ : syracuseStep 2254819 = 3382229) B3382229
theorem B5072881 : Blo 1668034 5072881 := bstep (se 2 (by rfl) ⟨1902330, by rfl⟩ : syracuseStep 5072881 = 3804661) B3804661
theorem B7129073 : Blo 1668034 7129073 := bstep (se 2 (by rfl) ⟨2673402, by rfl⟩ : syracuseStep 7129073 = 5346805) B5346805
theorem B2377793 : Blo 1668034 2377793 := bstep (se 2 (by rfl) ⟨891672, by rfl⟩ : syracuseStep 2377793 = 1783345) B1783345
theorem B1878115 : Blo 1668034 1878115 := bstep (se 1 (by rfl) ⟨1408586, by rfl⟩ : syracuseStep 1878115 = 2817173) B2817173
theorem B3754097 : Blo 1668034 3754097 := bstep (se 2 (by rfl) ⟨1407786, by rfl⟩ : syracuseStep 3754097 = 2815573) B2815573
theorem B3754115 : Blo 1668034 3754115 := bstep (se 1 (by rfl) ⟨2815586, by rfl⟩ : syracuseStep 3754115 = 5631173) B5631173
theorem B5630093 : Blo 1668034 5630093 := bstep (se 3 (by rfl) ⟨1055642, by rfl⟩ : syracuseStep 5630093 = 2111285) B2111285
theorem B2672833 : Blo 1668034 2672833 := bstep (se 2 (by rfl) ⟨1002312, by rfl⟩ : syracuseStep 2672833 = 2004625) B2004625
theorem B5630147 : Blo 1668034 5630147 := bstep (se 1 (by rfl) ⟨4222610, by rfl⟩ : syracuseStep 5630147 = 8445221) B8445221
theorem B1878259 : Blo 1668034 1878259 := bstep (se 1 (by rfl) ⟨1408694, by rfl⟩ : syracuseStep 1878259 = 2817389) B2817389
theorem B42764597 : Blo 1668034 42764597 := bstep (se 5 (by rfl) ⟨2004590, by rfl⟩ : syracuseStep 42764597 = 4009181) B4009181
theorem B4753741 : Blo 1668034 4753741 := bstep (se 3 (by rfl) ⟨891326, by rfl⟩ : syracuseStep 4753741 = 1782653) B1782653
theorem B1878403 : Blo 1668034 1878403 := bstep (se 1 (by rfl) ⟨1408802, by rfl⟩ : syracuseStep 1878403 = 2817605) B2817605
theorem B3754385 : Blo 1668034 3754385 := bstep (se 2 (by rfl) ⟨1407894, by rfl⟩ : syracuseStep 3754385 = 2815789) B2815789
theorem B3754403 : Blo 1668034 3754403 := bstep (se 1 (by rfl) ⟨2815802, by rfl⟩ : syracuseStep 3754403 = 5631605) B5631605
theorem B39053765 : Blo 1668034 39053765 := bstep (se 4 (by rfl) ⟨3661290, by rfl⟩ : syracuseStep 39053765 = 7322581) B7322581
theorem B8448461 : Blo 1668034 8448461 := bstep (se 3 (by rfl) ⟨1584086, by rfl⟩ : syracuseStep 8448461 = 3168173) B3168173
theorem B5630417 : Blo 1668034 5630417 := bstep (se 2 (by rfl) ⟨2111406, by rfl⟩ : syracuseStep 5630417 = 4222813) B4222813
theorem B4819409 : Blo 1668034 4819409 := bstep (se 2 (by rfl) ⟨1807278, by rfl⟩ : syracuseStep 4819409 = 3614557) B3614557
theorem B1878547 : Blo 1668034 1878547 := bstep (se 1 (by rfl) ⟨1408910, by rfl⟩ : syracuseStep 1878547 = 2817821) B2817821
theorem B6335117 : Blo 1668034 6335117 := bstep (se 3 (by rfl) ⟨1187834, by rfl⟩ : syracuseStep 6335117 = 2375669) B2375669
theorem B7129741 : Blo 1668034 7129741 := bstep (se 3 (by rfl) ⟨1336826, by rfl⟩ : syracuseStep 7129741 = 2673653) B2673653
theorem B5712547 : Blo 1668034 5712547 := bstep (se 1 (by rfl) ⟨4284410, by rfl⟩ : syracuseStep 5712547 = 8568821) B8568821
theorem B3009187 : Blo 1668034 3009187 := bstep (se 1 (by rfl) ⟨2256890, by rfl⟩ : syracuseStep 3009187 = 4513781) B4513781
theorem B1878691 : Blo 1668034 1878691 := bstep (se 1 (by rfl) ⟨1409018, by rfl⟩ : syracuseStep 1878691 = 2818037) B2818037
theorem B3754673 : Blo 1668034 3754673 := bstep (se 2 (by rfl) ⟨1408002, by rfl⟩ : syracuseStep 3754673 = 2816005) B2816005
theorem B3754691 : Blo 1668034 3754691 := bstep (se 1 (by rfl) ⟨2816018, by rfl⟩ : syracuseStep 3754691 = 5632037) B5632037
theorem B12667589 : Blo 1668034 12667589 := bstep (se 4 (by rfl) ⟨1187586, by rfl⟩ : syracuseStep 12667589 = 2375173) B2375173
theorem B3009251 : Blo 1668034 3009251 := bstep (se 1 (by rfl) ⟨2256938, by rfl⟩ : syracuseStep 3009251 = 4513877) B4513877
theorem B1903379 : Blo 1668034 1903379 := bstep (se 1 (by rfl) ⟨1427534, by rfl⟩ : syracuseStep 1903379 = 2855069) B2855069
theorem B9505613 : Blo 1668034 9505613 := bstep (se 3 (by rfl) ⟨1782302, by rfl⟩ : syracuseStep 9505613 = 3564605) B3564605
theorem B2853715 : Blo 1668034 2853715 := bstep (se 1 (by rfl) ⟨2140286, by rfl⟩ : syracuseStep 2853715 = 4280573) B4280573
theorem B2673505 : Blo 1668034 2673505 := bstep (se 2 (by rfl) ⟨1002564, by rfl⟩ : syracuseStep 2673505 = 2005129) B2005129
theorem B5417837 : Blo 1668034 5417837 := bstep (se 3 (by rfl) ⟨1015844, by rfl⟩ : syracuseStep 5417837 = 2031689) B2031689
theorem B3754961 : Blo 1668034 3754961 := bstep (se 2 (by rfl) ⟨1408110, by rfl⟩ : syracuseStep 3754961 = 2816221) B2816221
theorem B3754979 : Blo 1668034 3754979 := bstep (se 1 (by rfl) ⟨2816234, by rfl⟩ : syracuseStep 3754979 = 5632469) B5632469
theorem B5630957 : Blo 1668034 5630957 := bstep (se 3 (by rfl) ⟨1055804, by rfl⟩ : syracuseStep 5630957 = 2111609) B2111609
theorem B5631011 : Blo 1668034 5631011 := bstep (se 1 (by rfl) ⟨4223258, by rfl⟩ : syracuseStep 5631011 = 8446517) B8446517
theorem B4009105 : Blo 1668034 4009105 := bstep (se 2 (by rfl) ⟨1503414, by rfl⟩ : syracuseStep 4009105 = 3006829) B3006829
theorem B7130339 : Blo 1668034 7130339 := bstep (se 1 (by rfl) ⟨5347754, by rfl⟩ : syracuseStep 7130339 = 10695509) B10695509
theorem B3755249 : Blo 1668034 3755249 := bstep (se 2 (by rfl) ⟨1408218, by rfl⟩ : syracuseStep 3755249 = 2816437) B2816437
theorem B12676337 : Blo 1668034 12676337 := bstep (se 2 (by rfl) ⟨4753626, by rfl⟩ : syracuseStep 12676337 = 9507253) B9507253
theorem B3755267 : Blo 1668034 3755267 := bstep (se 1 (by rfl) ⟨2816450, by rfl⟩ : syracuseStep 3755267 = 5632901) B5632901
theorem B5631281 : Blo 1668034 5631281 := bstep (se 2 (by rfl) ⟨2111730, by rfl⟩ : syracuseStep 5631281 = 4223461) B4223461
theorem B4222307 : Blo 1668034 4222307 := bstep (se 1 (by rfl) ⟨3166730, by rfl⟩ : syracuseStep 4222307 = 6333461) B6333461
theorem B22842737 : Blo 1668034 22842737 := bstep (se 2 (by rfl) ⟨8566026, by rfl⟩ : syracuseStep 22842737 = 17132053) B17132053
theorem B6016369 : Blo 1668034 6016369 := bstep (se 2 (by rfl) ⟨2256138, by rfl⟩ : syracuseStep 6016369 = 4512277) B4512277
theorem B4754801 : Blo 1668034 4754801 := bstep (se 2 (by rfl) ⟨1783050, by rfl⟩ : syracuseStep 4754801 = 3566101) B3566101
theorem B2502065 : Blo 1668034 2502065 := bstep (se 2 (by rfl) ⟨938274, by rfl⟩ : syracuseStep 2502065 = 1876549) B1876549
theorem B6335921 : Blo 1668034 6335921 := bstep (se 2 (by rfl) ⟨2375970, by rfl⟩ : syracuseStep 6335921 = 4751941) B4751941
theorem B2502083 : Blo 1668034 2502083 := bstep (se 1 (by rfl) ⟨1876562, by rfl⟩ : syracuseStep 2502083 = 3753125) B3753125
theorem B2502113 : Blo 1668034 2502113 := bstep (se 2 (by rfl) ⟨938292, by rfl⟩ : syracuseStep 2502113 = 1876585) B1876585
theorem B10284529 : Blo 1668034 10284529 := bstep (se 2 (by rfl) ⟨3856698, by rfl⟩ : syracuseStep 10284529 = 7713397) B7713397
theorem B2502131 : Blo 1668034 2502131 := bstep (se 1 (by rfl) ⟨1876598, by rfl⟩ : syracuseStep 2502131 = 3753197) B3753197
theorem B2502161 : Blo 1668034 2502161 := bstep (se 2 (by rfl) ⟨938310, by rfl⟩ : syracuseStep 2502161 = 1876621) B1876621
theorem B3755537 : Blo 1668034 3755537 := bstep (se 2 (by rfl) ⟨1408326, by rfl⟩ : syracuseStep 3755537 = 2816653) B2816653
theorem B2502179 : Blo 1668034 2502179 := bstep (se 1 (by rfl) ⟨1876634, by rfl⟩ : syracuseStep 2502179 = 3753269) B3753269
theorem B3755555 : Blo 1668034 3755555 := bstep (se 1 (by rfl) ⟨2816666, by rfl⟩ : syracuseStep 3755555 = 5633333) B5633333
theorem B2502209 : Blo 1668034 2502209 := bstep (se 2 (by rfl) ⟨938328, by rfl⟩ : syracuseStep 2502209 = 1876657) B1876657
theorem B2502227 : Blo 1668034 2502227 := bstep (se 1 (by rfl) ⟨1876670, by rfl⟩ : syracuseStep 2502227 = 3753341) B3753341
theorem B2502257 : Blo 1668034 2502257 := bstep (se 2 (by rfl) ⟨938346, by rfl⟩ : syracuseStep 2502257 = 1876693) B1876693
theorem B1781363 : Blo 1668034 1781363 := bstep (se 1 (by rfl) ⟨1336022, by rfl⟩ : syracuseStep 1781363 = 2672045) B2672045
theorem B2502275 : Blo 1668034 2502275 := bstep (se 1 (by rfl) ⟨1876706, by rfl⟩ : syracuseStep 2502275 = 3753413) B3753413
theorem B2502305 : Blo 1668034 2502305 := bstep (se 2 (by rfl) ⟨938364, by rfl⟩ : syracuseStep 2502305 = 1876729) B1876729
theorem B2502323 : Blo 1668034 2502323 := bstep (se 1 (by rfl) ⟨1876742, by rfl⟩ : syracuseStep 2502323 = 3753485) B3753485
theorem B8564429 : Blo 1668034 8564429 := bstep (se 3 (by rfl) ⟨1605830, by rfl⟩ : syracuseStep 8564429 = 3211661) B3211661
theorem B2502353 : Blo 1668034 2502353 := bstep (se 2 (by rfl) ⟨938382, by rfl⟩ : syracuseStep 2502353 = 1876765) B1876765
theorem B2502371 : Blo 1668034 2502371 := bstep (se 1 (by rfl) ⟨1876778, by rfl⟩ : syracuseStep 2502371 = 3753557) B3753557
theorem B21671651 : Blo 1668034 21671651 := bstep (se 1 (by rfl) ⟨16253738, by rfl⟩ : syracuseStep 21671651 = 32507477) B32507477
theorem B2502401 : Blo 1668034 2502401 := bstep (se 2 (by rfl) ⟨938400, by rfl⟩ : syracuseStep 2502401 = 1876801) B1876801
theorem B11570957 : Blo 1668034 11570957 := bstep (se 3 (by rfl) ⟨2169554, by rfl⟩ : syracuseStep 11570957 = 4339109) B4339109
theorem B2502419 : Blo 1668034 2502419 := bstep (se 1 (by rfl) ⟨1876814, by rfl⟩ : syracuseStep 2502419 = 3753629) B3753629
theorem B2502449 : Blo 1668034 2502449 := bstep (se 2 (by rfl) ⟨938418, by rfl⟩ : syracuseStep 2502449 = 1876837) B1876837
theorem B3755825 : Blo 1668034 3755825 := bstep (se 2 (by rfl) ⟨1408434, by rfl⟩ : syracuseStep 3755825 = 2816869) B2816869
theorem B2502467 : Blo 1668034 2502467 := bstep (se 1 (by rfl) ⟨1876850, by rfl⟩ : syracuseStep 2502467 = 3753701) B3753701
theorem B3755843 : Blo 1668034 3755843 := bstep (se 1 (by rfl) ⟨2816882, by rfl⟩ : syracuseStep 3755843 = 5633765) B5633765
theorem B5631821 : Blo 1668034 5631821 := bstep (se 3 (by rfl) ⟨1055966, by rfl⟩ : syracuseStep 5631821 = 2111933) B2111933
theorem B2502497 : Blo 1668034 2502497 := bstep (se 2 (by rfl) ⟨938436, by rfl⟩ : syracuseStep 2502497 = 1876873) B1876873
theorem B4509553 : Blo 1668034 4509553 := bstep (se 2 (by rfl) ⟨1691082, by rfl⟩ : syracuseStep 4509553 = 3382165) B3382165
theorem B2502515 : Blo 1668034 2502515 := bstep (se 1 (by rfl) ⟨1876886, by rfl⟩ : syracuseStep 2502515 = 3753773) B3753773
theorem B5631875 : Blo 1668034 5631875 := bstep (se 1 (by rfl) ⟨4223906, by rfl⟩ : syracuseStep 5631875 = 8447813) B8447813
theorem B5345165 : Blo 1668034 5345165 := bstep (se 3 (by rfl) ⟨1002218, by rfl⟩ : syracuseStep 5345165 = 2004437) B2004437
theorem B2502545 : Blo 1668034 2502545 := bstep (se 2 (by rfl) ⟨938454, by rfl⟩ : syracuseStep 2502545 = 1876909) B1876909
theorem B2502563 : Blo 1668034 2502563 := bstep (se 1 (by rfl) ⟨1876922, by rfl⟩ : syracuseStep 2502563 = 3753845) B3753845
theorem B2674595 : Blo 1668034 2674595 := bstep (se 1 (by rfl) ⟨2005946, by rfl⟩ : syracuseStep 2674595 = 4011893) B4011893
theorem B2502593 : Blo 1668034 2502593 := bstep (se 2 (by rfl) ⟨938472, by rfl⟩ : syracuseStep 2502593 = 1876945) B1876945
theorem B2502611 : Blo 1668034 2502611 := bstep (se 1 (by rfl) ⟨1876958, by rfl⟩ : syracuseStep 2502611 = 3753917) B3753917
theorem B8024035 : Blo 1668034 8024035 := bstep (se 1 (by rfl) ⟨6018026, by rfl⟩ : syracuseStep 8024035 = 12036053) B12036053
theorem B2502641 : Blo 1668034 2502641 := bstep (se 2 (by rfl) ⟨938490, by rfl⟩ : syracuseStep 2502641 = 1876981) B1876981
theorem B2502659 : Blo 1668034 2502659 := bstep (se 1 (by rfl) ⟨1876994, by rfl⟩ : syracuseStep 2502659 = 3753989) B3753989
theorem B4755473 : Blo 1668034 4755473 := bstep (se 2 (by rfl) ⟨1783302, by rfl⟩ : syracuseStep 4755473 = 3566605) B3566605
theorem B2142227 : Blo 1668034 2142227 := bstep (se 1 (by rfl) ⟨1606670, by rfl⟩ : syracuseStep 2142227 = 3213341) B3213341
theorem B2502689 : Blo 1668034 2502689 := bstep (se 2 (by rfl) ⟨938508, by rfl⟩ : syracuseStep 2502689 = 1877017) B1877017
theorem B2502707 : Blo 1668034 2502707 := bstep (se 1 (by rfl) ⟨1877030, by rfl⟩ : syracuseStep 2502707 = 3754061) B3754061
theorem B6336589 : Blo 1668034 6336589 := bstep (se 3 (by rfl) ⟨1188110, by rfl⟩ : syracuseStep 6336589 = 2376221) B2376221
theorem B2502737 : Blo 1668034 2502737 := bstep (se 2 (by rfl) ⟨938526, by rfl⟩ : syracuseStep 2502737 = 1877053) B1877053
theorem B3756113 : Blo 1668034 3756113 := bstep (se 2 (by rfl) ⟨1408542, by rfl⟩ : syracuseStep 3756113 = 2817085) B2817085
theorem B2502755 : Blo 1668034 2502755 := bstep (se 1 (by rfl) ⟨1877066, by rfl⟩ : syracuseStep 2502755 = 3754133) B3754133
theorem B3756131 : Blo 1668034 3756131 := bstep (se 1 (by rfl) ⟨2817098, by rfl⟩ : syracuseStep 3756131 = 5634197) B5634197
theorem B2502785 : Blo 1668034 2502785 := bstep (se 2 (by rfl) ⟨938544, by rfl⟩ : syracuseStep 2502785 = 1877089) B1877089
theorem B5632145 : Blo 1668034 5632145 := bstep (se 2 (by rfl) ⟨2112054, by rfl⟩ : syracuseStep 5632145 = 4224109) B4224109
theorem B2502803 : Blo 1668034 2502803 := bstep (se 1 (by rfl) ⟨1877102, by rfl⟩ : syracuseStep 2502803 = 3754205) B3754205
theorem B2502833 : Blo 1668034 2502833 := bstep (se 2 (by rfl) ⟨938562, by rfl⟩ : syracuseStep 2502833 = 1877125) B1877125
theorem B2502851 : Blo 1668034 2502851 := bstep (se 1 (by rfl) ⟨1877138, by rfl⟩ : syracuseStep 2502851 = 3754277) B3754277
theorem B2502881 : Blo 1668034 2502881 := bstep (se 2 (by rfl) ⟨938580, by rfl⟩ : syracuseStep 2502881 = 1877161) B1877161
theorem B2502899 : Blo 1668034 2502899 := bstep (se 1 (by rfl) ⟨1877174, by rfl⟩ : syracuseStep 2502899 = 3754349) B3754349
theorem B4223249 : Blo 1668034 4223249 := bstep (se 2 (by rfl) ⟨1583718, by rfl⟩ : syracuseStep 4223249 = 3167437) B3167437
theorem B2502929 : Blo 1668034 2502929 := bstep (se 2 (by rfl) ⟨938598, by rfl⟩ : syracuseStep 2502929 = 1877197) B1877197
theorem B2502947 : Blo 1668034 2502947 := bstep (se 1 (by rfl) ⟨1877210, by rfl⟩ : syracuseStep 2502947 = 3754421) B3754421
theorem B2502977 : Blo 1668034 2502977 := bstep (se 2 (by rfl) ⟨938616, by rfl⟩ : syracuseStep 2502977 = 1877233) B1877233
theorem B4223299 : Blo 1668034 4223299 := bstep (se 1 (by rfl) ⟨3167474, by rfl⟩ : syracuseStep 4223299 = 6334949) B6334949
theorem B2502995 : Blo 1668034 2502995 := bstep (se 1 (by rfl) ⟨1877246, by rfl⟩ : syracuseStep 2502995 = 3754493) B3754493
theorem B2503025 : Blo 1668034 2503025 := bstep (se 2 (by rfl) ⟨938634, by rfl⟩ : syracuseStep 2503025 = 1877269) B1877269
theorem B3756401 : Blo 1668034 3756401 := bstep (se 2 (by rfl) ⟨1408650, by rfl⟩ : syracuseStep 3756401 = 2817301) B2817301
theorem B2503043 : Blo 1668034 2503043 := bstep (se 1 (by rfl) ⟨1877282, by rfl⟩ : syracuseStep 2503043 = 3754565) B3754565
theorem B3756419 : Blo 1668034 3756419 := bstep (se 1 (by rfl) ⟨2817314, by rfl⟩ : syracuseStep 3756419 = 5634629) B5634629
theorem B20304269 : Blo 1668034 20304269 := bstep (se 3 (by rfl) ⟨3807050, by rfl⟩ : syracuseStep 20304269 = 7614101) B7614101
theorem B2503073 : Blo 1668034 2503073 := bstep (se 2 (by rfl) ⟨938652, by rfl⟩ : syracuseStep 2503073 = 1877305) B1877305
theorem B6771107 : Blo 1668034 6771107 := bstep (se 1 (by rfl) ⟨5078330, by rfl⟩ : syracuseStep 6771107 = 10156661) B10156661
theorem B2503091 : Blo 1668034 2503091 := bstep (se 1 (by rfl) ⟨1877318, by rfl⟩ : syracuseStep 2503091 = 3754637) B3754637
theorem B4223441 : Blo 1668034 4223441 := bstep (se 2 (by rfl) ⟨1583790, by rfl⟩ : syracuseStep 4223441 = 3167581) B3167581
theorem B2503121 : Blo 1668034 2503121 := bstep (se 2 (by rfl) ⟨938670, by rfl⟩ : syracuseStep 2503121 = 1877341) B1877341
theorem B2503139 : Blo 1668034 2503139 := bstep (se 1 (by rfl) ⟨1877354, by rfl⟩ : syracuseStep 2503139 = 3754709) B3754709
theorem B2503169 : Blo 1668034 2503169 := bstep (se 2 (by rfl) ⟨938688, by rfl⟩ : syracuseStep 2503169 = 1877377) B1877377
theorem B2503187 : Blo 1668034 2503187 := bstep (se 1 (by rfl) ⟨1877390, by rfl⟩ : syracuseStep 2503187 = 3754781) B3754781
theorem B3166769 : Blo 1668034 3166769 := bstep (se 2 (by rfl) ⟨1187538, by rfl⟩ : syracuseStep 3166769 = 2375077) B2375077
theorem B2503217 : Blo 1668034 2503217 := bstep (se 2 (by rfl) ⟨938706, by rfl⟩ : syracuseStep 2503217 = 1877413) B1877413
theorem B2503235 : Blo 1668034 2503235 := bstep (se 1 (by rfl) ⟨1877426, by rfl⟩ : syracuseStep 2503235 = 3754853) B3754853
theorem B2503265 : Blo 1668034 2503265 := bstep (se 2 (by rfl) ⟨938724, by rfl⟩ : syracuseStep 2503265 = 1877449) B1877449
theorem B1782371 : Blo 1668034 1782371 := bstep (se 1 (by rfl) ⟨1336778, by rfl⟩ : syracuseStep 1782371 = 2673557) B2673557
theorem B2503283 : Blo 1668034 2503283 := bstep (se 1 (by rfl) ⟨1877462, by rfl⟩ : syracuseStep 2503283 = 3754925) B3754925
theorem B12030605 : Blo 1668034 12030605 := bstep (se 3 (by rfl) ⟨2255738, by rfl⟩ : syracuseStep 12030605 = 4511477) B4511477
theorem B2503313 : Blo 1668034 2503313 := bstep (se 2 (by rfl) ⟨938742, by rfl⟩ : syracuseStep 2503313 = 1877485) B1877485
theorem B3756689 : Blo 1668034 3756689 := bstep (se 2 (by rfl) ⟨1408758, by rfl⟩ : syracuseStep 3756689 = 2817517) B2817517
theorem B2503331 : Blo 1668034 2503331 := bstep (se 1 (by rfl) ⟨1877498, by rfl⟩ : syracuseStep 2503331 = 3754997) B3754997
theorem B3756707 : Blo 1668034 3756707 := bstep (se 1 (by rfl) ⟨2817530, by rfl⟩ : syracuseStep 3756707 = 5635061) B5635061
theorem B7230115 : Blo 1668034 7230115 := bstep (se 1 (by rfl) ⟨5422586, by rfl⟩ : syracuseStep 7230115 = 10845173) B10845173
theorem B5632685 : Blo 1668034 5632685 := bstep (se 3 (by rfl) ⟨1056128, by rfl⟩ : syracuseStep 5632685 = 2112257) B2112257
theorem B2503361 : Blo 1668034 2503361 := bstep (se 2 (by rfl) ⟨938760, by rfl⟩ : syracuseStep 2503361 = 1877521) B1877521
theorem B4510417 : Blo 1668034 4510417 := bstep (se 2 (by rfl) ⟨1691406, by rfl⟩ : syracuseStep 4510417 = 3382813) B3382813
theorem B2503379 : Blo 1668034 2503379 := bstep (se 1 (by rfl) ⟨1877534, by rfl⟩ : syracuseStep 2503379 = 3755069) B3755069
theorem B5632739 : Blo 1668034 5632739 := bstep (se 1 (by rfl) ⟨4224554, by rfl⟩ : syracuseStep 5632739 = 8449109) B8449109
theorem B2503409 : Blo 1668034 2503409 := bstep (se 2 (by rfl) ⟨938778, by rfl⟩ : syracuseStep 2503409 = 1877557) B1877557
theorem B2503427 : Blo 1668034 2503427 := bstep (se 1 (by rfl) ⟨1877570, by rfl⟩ : syracuseStep 2503427 = 3755141) B3755141
theorem B2503457 : Blo 1668034 2503457 := bstep (se 2 (by rfl) ⟨938796, by rfl⟩ : syracuseStep 2503457 = 1877593) B1877593
theorem B2503475 : Blo 1668034 2503475 := bstep (se 1 (by rfl) ⟨1877606, by rfl⟩ : syracuseStep 2503475 = 3755213) B3755213
theorem B4281169 : Blo 1668034 4281169 := bstep (se 2 (by rfl) ⟨1605438, by rfl⟩ : syracuseStep 4281169 = 3210877) B3210877
theorem B2503505 : Blo 1668034 2503505 := bstep (se 2 (by rfl) ⟨938814, by rfl⟩ : syracuseStep 2503505 = 1877629) B1877629
theorem B2814817 : Blo 1668034 2814817 := bstep (se 2 (by rfl) ⟨1055556, by rfl⟩ : syracuseStep 2814817 = 2111113) B2111113
theorem B2503523 : Blo 1668034 2503523 := bstep (se 1 (by rfl) ⟨1877642, by rfl⟩ : syracuseStep 2503523 = 3755285) B3755285
theorem B6337379 : Blo 1668034 6337379 := bstep (se 1 (by rfl) ⟨4753034, by rfl⟩ : syracuseStep 6337379 = 9506069) B9506069
theorem B2503553 : Blo 1668034 2503553 := bstep (se 2 (by rfl) ⟨938832, by rfl⟩ : syracuseStep 2503553 = 1877665) B1877665
theorem B2814851 : Blo 1668034 2814851 := bstep (se 1 (by rfl) ⟨2111138, by rfl⟩ : syracuseStep 2814851 = 4222277) B4222277
theorem B2503571 : Blo 1668034 2503571 := bstep (se 1 (by rfl) ⟨1877678, by rfl⟩ : syracuseStep 2503571 = 3755357) B3755357
theorem B2503601 : Blo 1668034 2503601 := bstep (se 2 (by rfl) ⟨938850, by rfl⟩ : syracuseStep 2503601 = 1877701) B1877701
theorem B3756977 : Blo 1668034 3756977 := bstep (se 2 (by rfl) ⟨1408866, by rfl⟩ : syracuseStep 3756977 = 2817733) B2817733
theorem B18043829 : Blo 1668034 18043829 := bstep (se 5 (by rfl) ⟨845804, by rfl⟩ : syracuseStep 18043829 = 1691609) B1691609
theorem B1668035 : Blo 1668034 1668035 := bstep (se 1 (by rfl) ⟨1251026, by rfl⟩ : syracuseStep 1668035 = 2502053) B2502053
theorem B3167171 : Blo 1668034 3167171 := bstep (se 1 (by rfl) ⟨2375378, by rfl⟩ : syracuseStep 3167171 = 4750757) B4750757
theorem B2503619 : Blo 1668034 2503619 := bstep (se 1 (by rfl) ⟨1877714, by rfl⟩ : syracuseStep 2503619 = 3755429) B3755429
theorem B3756995 : Blo 1668034 3756995 := bstep (se 1 (by rfl) ⟨2817746, by rfl⟩ : syracuseStep 3756995 = 5635493) B5635493
theorem B1668051 : Blo 1668034 1668051 := bstep (se 1 (by rfl) ⟨1251038, by rfl⟩ : syracuseStep 1668051 = 2502077) B2502077
theorem B2503649 : Blo 1668034 2503649 := bstep (se 2 (by rfl) ⟨938868, by rfl⟩ : syracuseStep 2503649 = 1877737) B1877737
theorem B1668067 : Blo 1668034 1668067 := bstep (se 1 (by rfl) ⟨1251050, by rfl⟩ : syracuseStep 1668067 = 2502101) B2502101
theorem B5706733 : Blo 1668034 5706733 := bstep (se 3 (by rfl) ⟨1070012, by rfl⟩ : syracuseStep 5706733 = 2140025) B2140025
theorem B5633009 : Blo 1668034 5633009 := bstep (se 2 (by rfl) ⟨2112378, by rfl⟩ : syracuseStep 5633009 = 4224757) B4224757
theorem B1668083 : Blo 1668034 1668083 := bstep (se 1 (by rfl) ⟨1251062, by rfl⟩ : syracuseStep 1668083 = 2502125) B2502125
theorem B2503667 : Blo 1668034 2503667 := bstep (se 1 (by rfl) ⟨1877750, by rfl⟩ : syracuseStep 2503667 = 3755501) B3755501
theorem B1668099 : Blo 1668034 1668099 := bstep (se 1 (by rfl) ⟨1251074, by rfl⟩ : syracuseStep 1668099 = 2502149) B2502149
theorem B2814979 : Blo 1668034 2814979 := bstep (se 1 (by rfl) ⟨2111234, by rfl⟩ : syracuseStep 2814979 = 4222469) B4222469
theorem B2503697 : Blo 1668034 2503697 := bstep (se 2 (by rfl) ⟨938886, by rfl⟩ : syracuseStep 2503697 = 1877773) B1877773
theorem B1668115 : Blo 1668034 1668115 := bstep (se 1 (by rfl) ⟨1251086, by rfl⟩ : syracuseStep 1668115 = 2502173) B2502173
theorem B1668131 : Blo 1668034 1668131 := bstep (se 1 (by rfl) ⟨1251098, by rfl⟩ : syracuseStep 1668131 = 2502197) B2502197
theorem B2503715 : Blo 1668034 2503715 := bstep (se 1 (by rfl) ⟨1877786, by rfl⟩ : syracuseStep 2503715 = 3755573) B3755573
theorem B1668147 : Blo 1668034 1668147 := bstep (se 1 (by rfl) ⟨1251110, by rfl⟩ : syracuseStep 1668147 = 2502221) B2502221
theorem B2503745 : Blo 1668034 2503745 := bstep (se 2 (by rfl) ⟨938904, by rfl⟩ : syracuseStep 2503745 = 1877809) B1877809
theorem B1668163 : Blo 1668034 1668163 := bstep (se 1 (by rfl) ⟨1251122, by rfl⟩ : syracuseStep 1668163 = 2502245) B2502245
theorem B1668179 : Blo 1668034 1668179 := bstep (se 1 (by rfl) ⟨1251134, by rfl⟩ : syracuseStep 1668179 = 2502269) B2502269
theorem B2503763 : Blo 1668034 2503763 := bstep (se 1 (by rfl) ⟨1877822, by rfl⟩ : syracuseStep 2503763 = 3755645) B3755645
theorem B1668195 : Blo 1668034 1668195 := bstep (se 1 (by rfl) ⟨1251146, by rfl⟩ : syracuseStep 1668195 = 2502293) B2502293
theorem B2503793 : Blo 1668034 2503793 := bstep (se 2 (by rfl) ⟨938922, by rfl⟩ : syracuseStep 2503793 = 1877845) B1877845
theorem B1668211 : Blo 1668034 1668211 := bstep (se 1 (by rfl) ⟨1251158, by rfl⟩ : syracuseStep 1668211 = 2502317) B2502317
theorem B1668227 : Blo 1668034 1668227 := bstep (se 1 (by rfl) ⟨1251170, by rfl⟩ : syracuseStep 1668227 = 2502341) B2502341
theorem B2503811 : Blo 1668034 2503811 := bstep (se 1 (by rfl) ⟨1877858, by rfl⟩ : syracuseStep 2503811 = 3755717) B3755717
theorem B2815121 : Blo 1668034 2815121 := bstep (se 2 (by rfl) ⟨1055670, by rfl⟩ : syracuseStep 2815121 = 2111341) B2111341
theorem B1668243 : Blo 1668034 1668243 := bstep (se 1 (by rfl) ⟨1251182, by rfl⟩ : syracuseStep 1668243 = 2502365) B2502365
theorem B2503841 : Blo 1668034 2503841 := bstep (se 2 (by rfl) ⟨938940, by rfl⟩ : syracuseStep 2503841 = 1877881) B1877881
theorem B1668259 : Blo 1668034 1668259 := bstep (se 1 (by rfl) ⟨1251194, by rfl⟩ : syracuseStep 1668259 = 2502389) B2502389
theorem B1668275 : Blo 1668034 1668275 := bstep (se 1 (by rfl) ⟨1251206, by rfl⟩ : syracuseStep 1668275 = 2502413) B2502413
theorem B2503859 : Blo 1668034 2503859 := bstep (se 1 (by rfl) ⟨1877894, by rfl⟩ : syracuseStep 2503859 = 3755789) B3755789
theorem B1668291 : Blo 1668034 1668291 := bstep (se 1 (by rfl) ⟨1251218, by rfl⟩ : syracuseStep 1668291 = 2502437) B2502437
theorem B2503889 : Blo 1668034 2503889 := bstep (se 2 (by rfl) ⟨938958, by rfl⟩ : syracuseStep 2503889 = 1877917) B1877917
theorem B3757265 : Blo 1668034 3757265 := bstep (se 2 (by rfl) ⟨1408974, by rfl⟩ : syracuseStep 3757265 = 2817949) B2817949
theorem B1668307 : Blo 1668034 1668307 := bstep (se 1 (by rfl) ⟨1251230, by rfl⟩ : syracuseStep 1668307 = 2502461) B2502461
theorem B1668323 : Blo 1668034 1668323 := bstep (se 1 (by rfl) ⟨1251242, by rfl⟩ : syracuseStep 1668323 = 2502485) B2502485
theorem B2503907 : Blo 1668034 2503907 := bstep (se 1 (by rfl) ⟨1877930, by rfl⟩ : syracuseStep 2503907 = 3755861) B3755861
theorem B3757283 : Blo 1668034 3757283 := bstep (se 1 (by rfl) ⟨2817962, by rfl⟩ : syracuseStep 3757283 = 5635925) B5635925
theorem B1668339 : Blo 1668034 1668339 := bstep (se 1 (by rfl) ⟨1251254, by rfl⟩ : syracuseStep 1668339 = 2502509) B2502509
theorem B2503937 : Blo 1668034 2503937 := bstep (se 2 (by rfl) ⟨938976, by rfl⟩ : syracuseStep 2503937 = 1877953) B1877953
theorem B1668355 : Blo 1668034 1668355 := bstep (se 1 (by rfl) ⟨1251266, by rfl⟩ : syracuseStep 1668355 = 2502533) B2502533
theorem B2815249 : Blo 1668034 2815249 := bstep (se 2 (by rfl) ⟨1055718, by rfl⟩ : syracuseStep 2815249 = 2111437) B2111437
theorem B1668371 : Blo 1668034 1668371 := bstep (se 1 (by rfl) ⟨1251278, by rfl⟩ : syracuseStep 1668371 = 2502557) B2502557
theorem B2503955 : Blo 1668034 2503955 := bstep (se 1 (by rfl) ⟨1877966, by rfl⟩ : syracuseStep 2503955 = 3755933) B3755933
theorem B1668387 : Blo 1668034 1668387 := bstep (se 1 (by rfl) ⟨1251290, by rfl⟩ : syracuseStep 1668387 = 2502581) B2502581
theorem B2503985 : Blo 1668034 2503985 := bstep (se 2 (by rfl) ⟨938994, by rfl⟩ : syracuseStep 2503985 = 1877989) B1877989
theorem B8451377 : Blo 1668034 8451377 := bstep (se 2 (by rfl) ⟨3169266, by rfl⟩ : syracuseStep 8451377 = 6338533) B6338533
theorem B2815283 : Blo 1668034 2815283 := bstep (se 1 (by rfl) ⟨2111462, by rfl⟩ : syracuseStep 2815283 = 4222925) B4222925
theorem B1668403 : Blo 1668034 1668403 := bstep (se 1 (by rfl) ⟨1251302, by rfl⟩ : syracuseStep 1668403 = 2502605) B2502605
theorem B1668419 : Blo 1668034 1668419 := bstep (se 1 (by rfl) ⟨1251314, by rfl⟩ : syracuseStep 1668419 = 2502629) B2502629
theorem B2504003 : Blo 1668034 2504003 := bstep (se 1 (by rfl) ⟨1878002, by rfl⟩ : syracuseStep 2504003 = 3756005) B3756005
theorem B16037189 : Blo 1668034 16037189 := bstep (se 4 (by rfl) ⟨1503486, by rfl⟩ : syracuseStep 16037189 = 3006973) B3006973
theorem B1668435 : Blo 1668034 1668435 := bstep (se 1 (by rfl) ⟨1251326, by rfl⟩ : syracuseStep 1668435 = 2502653) B2502653
theorem B2504033 : Blo 1668034 2504033 := bstep (se 2 (by rfl) ⟨939012, by rfl⟩ : syracuseStep 2504033 = 1878025) B1878025
theorem B1668451 : Blo 1668034 1668451 := bstep (se 1 (by rfl) ⟨1251338, by rfl⟩ : syracuseStep 1668451 = 2502677) B2502677
theorem B10696049 : Blo 1668034 10696049 := bstep (se 2 (by rfl) ⟨4011018, by rfl⟩ : syracuseStep 10696049 = 8022037) B8022037
theorem B1668467 : Blo 1668034 1668467 := bstep (se 1 (by rfl) ⟨1251350, by rfl⟩ : syracuseStep 1668467 = 2502701) B2502701
theorem B2504051 : Blo 1668034 2504051 := bstep (se 1 (by rfl) ⟨1878038, by rfl⟩ : syracuseStep 2504051 = 3756077) B3756077
theorem B1668483 : Blo 1668034 1668483 := bstep (se 1 (by rfl) ⟨1251362, by rfl⟩ : syracuseStep 1668483 = 2502725) B2502725
theorem B2504081 : Blo 1668034 2504081 := bstep (se 2 (by rfl) ⟨939030, by rfl⟩ : syracuseStep 2504081 = 1878061) B1878061
theorem B1668499 : Blo 1668034 1668499 := bstep (se 1 (by rfl) ⟨1251374, by rfl⟩ : syracuseStep 1668499 = 2502749) B2502749
theorem B1668515 : Blo 1668034 1668515 := bstep (se 1 (by rfl) ⟨1251386, by rfl⟩ : syracuseStep 1668515 = 2502773) B2502773
theorem B2504099 : Blo 1668034 2504099 := bstep (se 1 (by rfl) ⟨1878074, by rfl⟩ : syracuseStep 2504099 = 3756149) B3756149
theorem B4224433 : Blo 1668034 4224433 := bstep (se 2 (by rfl) ⟨1584162, by rfl⟩ : syracuseStep 4224433 = 3168325) B3168325
theorem B2815411 : Blo 1668034 2815411 := bstep (se 1 (by rfl) ⟨2111558, by rfl⟩ : syracuseStep 2815411 = 4223117) B4223117
theorem B1668531 : Blo 1668034 1668531 := bstep (se 1 (by rfl) ⟨1251398, by rfl⟩ : syracuseStep 1668531 = 2502797) B2502797
theorem B2504129 : Blo 1668034 2504129 := bstep (se 2 (by rfl) ⟨939048, by rfl⟩ : syracuseStep 2504129 = 1878097) B1878097
theorem B1668547 : Blo 1668034 1668547 := bstep (se 1 (by rfl) ⟨1251410, by rfl⟩ : syracuseStep 1668547 = 2502821) B2502821
theorem B5346755 : Blo 1668034 5346755 := bstep (se 1 (by rfl) ⟨4010066, by rfl⟩ : syracuseStep 5346755 = 8020133) B8020133
theorem B9024965 : Blo 1668034 9024965 := bstep (se 4 (by rfl) ⟨846090, by rfl⟩ : syracuseStep 9024965 = 1692181) B1692181
theorem B1668563 : Blo 1668034 1668563 := bstep (se 1 (by rfl) ⟨1251422, by rfl⟩ : syracuseStep 1668563 = 2502845) B2502845
theorem B2504147 : Blo 1668034 2504147 := bstep (se 1 (by rfl) ⟨1878110, by rfl⟩ : syracuseStep 2504147 = 3756221) B3756221
theorem B1668579 : Blo 1668034 1668579 := bstep (se 1 (by rfl) ⟨1251434, by rfl⟩ : syracuseStep 1668579 = 2502869) B2502869
theorem B6338033 : Blo 1668034 6338033 := bstep (se 2 (by rfl) ⟨2376762, by rfl⟩ : syracuseStep 6338033 = 4753525) B4753525
theorem B2504177 : Blo 1668034 2504177 := bstep (se 2 (by rfl) ⟨939066, by rfl⟩ : syracuseStep 2504177 = 1878133) B1878133
theorem B1668595 : Blo 1668034 1668595 := bstep (se 1 (by rfl) ⟨1251446, by rfl⟩ : syracuseStep 1668595 = 2502893) B2502893
theorem B3757553 : Blo 1668034 3757553 := bstep (se 2 (by rfl) ⟨1409082, by rfl⟩ : syracuseStep 3757553 = 2818165) B2818165
theorem B1668611 : Blo 1668034 1668611 := bstep (se 1 (by rfl) ⟨1251458, by rfl⟩ : syracuseStep 1668611 = 2502917) B2502917
theorem B2504195 : Blo 1668034 2504195 := bstep (se 1 (by rfl) ⟨1878146, by rfl⟩ : syracuseStep 2504195 = 3756293) B3756293
theorem B3757571 : Blo 1668034 3757571 := bstep (se 1 (by rfl) ⟨2818178, by rfl⟩ : syracuseStep 3757571 = 5636357) B5636357
theorem B5633549 : Blo 1668034 5633549 := bstep (se 3 (by rfl) ⟨1056290, by rfl⟩ : syracuseStep 5633549 = 2112581) B2112581
theorem B1668627 : Blo 1668034 1668627 := bstep (se 1 (by rfl) ⟨1251470, by rfl⟩ : syracuseStep 1668627 = 2502941) B2502941
theorem B2504225 : Blo 1668034 2504225 := bstep (se 2 (by rfl) ⟨939084, by rfl⟩ : syracuseStep 2504225 = 1878169) B1878169
theorem B1668643 : Blo 1668034 1668643 := bstep (se 1 (by rfl) ⟨1251482, by rfl⟩ : syracuseStep 1668643 = 2502965) B2502965
theorem B1668659 : Blo 1668034 1668659 := bstep (se 1 (by rfl) ⟨1251494, by rfl⟩ : syracuseStep 1668659 = 2502989) B2502989
theorem B2504243 : Blo 1668034 2504243 := bstep (se 1 (by rfl) ⟨1878182, by rfl⟩ : syracuseStep 2504243 = 3756365) B3756365
theorem B2815553 : Blo 1668034 2815553 := bstep (se 2 (by rfl) ⟨1055832, by rfl⟩ : syracuseStep 2815553 = 2111665) B2111665
theorem B1668675 : Blo 1668034 1668675 := bstep (se 1 (by rfl) ⟨1251506, by rfl⟩ : syracuseStep 1668675 = 2503013) B2503013
theorem B5633603 : Blo 1668034 5633603 := bstep (se 1 (by rfl) ⟨4225202, by rfl⟩ : syracuseStep 5633603 = 8450405) B8450405
theorem B9500237 : Blo 1668034 9500237 := bstep (se 3 (by rfl) ⟨1781294, by rfl⟩ : syracuseStep 9500237 = 3562589) B3562589
theorem B2504273 : Blo 1668034 2504273 := bstep (se 2 (by rfl) ⟨939102, by rfl⟩ : syracuseStep 2504273 = 1878205) B1878205
theorem B1668691 : Blo 1668034 1668691 := bstep (se 1 (by rfl) ⟨1251518, by rfl⟩ : syracuseStep 1668691 = 2503037) B2503037
theorem B1668707 : Blo 1668034 1668707 := bstep (se 1 (by rfl) ⟨1251530, by rfl⟩ : syracuseStep 1668707 = 2503061) B2503061
theorem B2504291 : Blo 1668034 2504291 := bstep (se 1 (by rfl) ⟨1878218, by rfl⟩ : syracuseStep 2504291 = 3756437) B3756437
theorem B3806833 : Blo 1668034 3806833 := bstep (se 2 (by rfl) ⟨1427562, by rfl⟩ : syracuseStep 3806833 = 2855125) B2855125
theorem B1668723 : Blo 1668034 1668723 := bstep (se 1 (by rfl) ⟨1251542, by rfl⟩ : syracuseStep 1668723 = 2503085) B2503085
theorem B2504321 : Blo 1668034 2504321 := bstep (se 2 (by rfl) ⟨939120, by rfl⟩ : syracuseStep 2504321 = 1878241) B1878241
theorem B1668739 : Blo 1668034 1668739 := bstep (se 1 (by rfl) ⟨1251554, by rfl⟩ : syracuseStep 1668739 = 2503109) B2503109
theorem B9025157 : Blo 1668034 9025157 := bstep (se 4 (by rfl) ⟨846108, by rfl⟩ : syracuseStep 9025157 = 1692217) B1692217
theorem B2111123 : Blo 1668034 2111123 := bstep (se 1 (by rfl) ⟨1583342, by rfl⟩ : syracuseStep 2111123 = 3166685) B3166685
theorem B1668755 : Blo 1668034 1668755 := bstep (se 1 (by rfl) ⟨1251566, by rfl⟩ : syracuseStep 1668755 = 2503133) B2503133
theorem B2504339 : Blo 1668034 2504339 := bstep (se 1 (by rfl) ⟨1878254, by rfl⟩ : syracuseStep 2504339 = 3756509) B3756509
theorem B1668771 : Blo 1668034 1668771 := bstep (se 1 (by rfl) ⟨1251578, by rfl⟩ : syracuseStep 1668771 = 2503157) B2503157
theorem B9508529 : Blo 1668034 9508529 := bstep (se 2 (by rfl) ⟨3565698, by rfl⟩ : syracuseStep 9508529 = 7131397) B7131397
theorem B2504369 : Blo 1668034 2504369 := bstep (se 2 (by rfl) ⟨939138, by rfl⟩ : syracuseStep 2504369 = 1878277) B1878277
theorem B1668787 : Blo 1668034 1668787 := bstep (se 1 (by rfl) ⟨1251590, by rfl⟩ : syracuseStep 1668787 = 2503181) B2503181
theorem B2815681 : Blo 1668034 2815681 := bstep (se 2 (by rfl) ⟨1055880, by rfl⟩ : syracuseStep 2815681 = 2111761) B2111761
theorem B1668803 : Blo 1668034 1668803 := bstep (se 1 (by rfl) ⟨1251602, by rfl⟩ : syracuseStep 1668803 = 2503205) B2503205
theorem B4224707 : Blo 1668034 4224707 := bstep (se 1 (by rfl) ⟨3168530, by rfl⟩ : syracuseStep 4224707 = 6337061) B6337061
theorem B2504387 : Blo 1668034 2504387 := bstep (se 1 (by rfl) ⟨1878290, by rfl⟩ : syracuseStep 2504387 = 3756581) B3756581
theorem B1668819 : Blo 1668034 1668819 := bstep (se 1 (by rfl) ⟨1251614, by rfl⟩ : syracuseStep 1668819 = 2503229) B2503229
theorem B2815715 : Blo 1668034 2815715 := bstep (se 1 (by rfl) ⟨2111786, by rfl⟩ : syracuseStep 2815715 = 4223573) B4223573
theorem B1668835 : Blo 1668034 1668835 := bstep (se 1 (by rfl) ⟨1251626, by rfl⟩ : syracuseStep 1668835 = 2503253) B2503253
theorem B2504417 : Blo 1668034 2504417 := bstep (se 2 (by rfl) ⟨939156, by rfl⟩ : syracuseStep 2504417 = 1878313) B1878313
theorem B1668851 : Blo 1668034 1668851 := bstep (se 1 (by rfl) ⟨1251638, by rfl⟩ : syracuseStep 1668851 = 2503277) B2503277
theorem B2504435 : Blo 1668034 2504435 := bstep (se 1 (by rfl) ⟨1878326, by rfl⟩ : syracuseStep 2504435 = 3756653) B3756653
theorem B1668867 : Blo 1668034 1668867 := bstep (se 1 (by rfl) ⟨1251650, by rfl⟩ : syracuseStep 1668867 = 2503301) B2503301
theorem B2504465 : Blo 1668034 2504465 := bstep (se 2 (by rfl) ⟨939174, by rfl⟩ : syracuseStep 2504465 = 1878349) B1878349
theorem B1668883 : Blo 1668034 1668883 := bstep (se 1 (by rfl) ⟨1251662, by rfl⟩ : syracuseStep 1668883 = 2503325) B2503325
theorem B1668899 : Blo 1668034 1668899 := bstep (se 1 (by rfl) ⟨1251674, by rfl⟩ : syracuseStep 1668899 = 2503349) B2503349
theorem B2504483 : Blo 1668034 2504483 := bstep (se 1 (by rfl) ⟨1878362, by rfl⟩ : syracuseStep 2504483 = 3756725) B3756725
theorem B1668915 : Blo 1668034 1668915 := bstep (se 1 (by rfl) ⟨1251686, by rfl⟩ : syracuseStep 1668915 = 2503373) B2503373
theorem B2504513 : Blo 1668034 2504513 := bstep (se 2 (by rfl) ⟨939192, by rfl⟩ : syracuseStep 2504513 = 1878385) B1878385
theorem B3168067 : Blo 1668034 3168067 := bstep (se 1 (by rfl) ⟨2376050, by rfl⟩ : syracuseStep 3168067 = 4752101) B4752101
theorem B1668931 : Blo 1668034 1668931 := bstep (se 1 (by rfl) ⟨1251698, by rfl⟩ : syracuseStep 1668931 = 2503397) B2503397
theorem B5633873 : Blo 1668034 5633873 := bstep (se 2 (by rfl) ⟨2112702, by rfl⟩ : syracuseStep 5633873 = 4225405) B4225405
theorem B1668947 : Blo 1668034 1668947 := bstep (se 1 (by rfl) ⟨1251710, by rfl⟩ : syracuseStep 1668947 = 2503421) B2503421
theorem B2504531 : Blo 1668034 2504531 := bstep (se 1 (by rfl) ⟨1878398, by rfl⟩ : syracuseStep 2504531 = 3756797) B3756797
theorem B2815843 : Blo 1668034 2815843 := bstep (se 1 (by rfl) ⟨2111882, by rfl⟩ : syracuseStep 2815843 = 4223765) B4223765
theorem B1668963 : Blo 1668034 1668963 := bstep (se 1 (by rfl) ⟨1251722, by rfl⟩ : syracuseStep 1668963 = 2503445) B2503445
theorem B2504561 : Blo 1668034 2504561 := bstep (se 2 (by rfl) ⟨939210, by rfl⟩ : syracuseStep 2504561 = 1878421) B1878421
theorem B1668979 : Blo 1668034 1668979 := bstep (se 1 (by rfl) ⟨1251734, by rfl⟩ : syracuseStep 1668979 = 2503469) B2503469
theorem B1668995 : Blo 1668034 1668995 := bstep (se 1 (by rfl) ⟨1251746, by rfl⟩ : syracuseStep 1668995 = 2503493) B2503493
theorem B4224899 : Blo 1668034 4224899 := bstep (se 1 (by rfl) ⟨3168674, by rfl⟩ : syracuseStep 4224899 = 6337349) B6337349
theorem B2504579 : Blo 1668034 2504579 := bstep (se 1 (by rfl) ⟨1878434, by rfl⟩ : syracuseStep 2504579 = 3756869) B3756869
theorem B1669011 : Blo 1668034 1669011 := bstep (se 1 (by rfl) ⟨1251758, by rfl⟩ : syracuseStep 1669011 = 2503517) B2503517
theorem B2504609 : Blo 1668034 2504609 := bstep (se 2 (by rfl) ⟨939228, by rfl⟩ : syracuseStep 2504609 = 1878457) B1878457
theorem B1669027 : Blo 1668034 1669027 := bstep (se 1 (by rfl) ⟨1251770, by rfl⟩ : syracuseStep 1669027 = 2503541) B2503541
theorem B1669043 : Blo 1668034 1669043 := bstep (se 1 (by rfl) ⟨1251782, by rfl⟩ : syracuseStep 1669043 = 2503565) B2503565
theorem B2504627 : Blo 1668034 2504627 := bstep (se 1 (by rfl) ⟨1878470, by rfl⟩ : syracuseStep 2504627 = 3756941) B3756941
theorem B1669059 : Blo 1668034 1669059 := bstep (se 1 (by rfl) ⟨1251794, by rfl⟩ : syracuseStep 1669059 = 2503589) B2503589
theorem B2504657 : Blo 1668034 2504657 := bstep (se 2 (by rfl) ⟨939246, by rfl⟩ : syracuseStep 2504657 = 1878493) B1878493
theorem B1669075 : Blo 1668034 1669075 := bstep (se 1 (by rfl) ⟨1251806, by rfl⟩ : syracuseStep 1669075 = 2503613) B2503613
theorem B3168227 : Blo 1668034 3168227 := bstep (se 1 (by rfl) ⟨2376170, by rfl⟩ : syracuseStep 3168227 = 4752341) B4752341
theorem B1669091 : Blo 1668034 1669091 := bstep (se 1 (by rfl) ⟨1251818, by rfl⟩ : syracuseStep 1669091 = 2503637) B2503637
theorem B2504675 : Blo 1668034 2504675 := bstep (se 1 (by rfl) ⟨1878506, by rfl⟩ : syracuseStep 2504675 = 3757013) B3757013
theorem B2815985 : Blo 1668034 2815985 := bstep (se 2 (by rfl) ⟨1055994, by rfl⟩ : syracuseStep 2815985 = 2111989) B2111989
theorem B1669107 : Blo 1668034 1669107 := bstep (se 1 (by rfl) ⟨1251830, by rfl⟩ : syracuseStep 1669107 = 2503661) B2503661
theorem B2504705 : Blo 1668034 2504705 := bstep (se 2 (by rfl) ⟨939264, by rfl⟩ : syracuseStep 2504705 = 1878529) B1878529
theorem B1669123 : Blo 1668034 1669123 := bstep (se 1 (by rfl) ⟨1251842, by rfl⟩ : syracuseStep 1669123 = 2503685) B2503685
theorem B1669139 : Blo 1668034 1669139 := bstep (se 1 (by rfl) ⟨1251854, by rfl⟩ : syracuseStep 1669139 = 2503709) B2503709
theorem B2504723 : Blo 1668034 2504723 := bstep (se 1 (by rfl) ⟨1878542, by rfl⟩ : syracuseStep 2504723 = 3757085) B3757085
theorem B1669155 : Blo 1668034 1669155 := bstep (se 1 (by rfl) ⟨1251866, by rfl⟩ : syracuseStep 1669155 = 2503733) B2503733
theorem B2504753 : Blo 1668034 2504753 := bstep (se 2 (by rfl) ⟨939282, by rfl⟩ : syracuseStep 2504753 = 1878565) B1878565
theorem B1669171 : Blo 1668034 1669171 := bstep (se 1 (by rfl) ⟨1251878, by rfl⟩ : syracuseStep 1669171 = 2503757) B2503757
theorem B1669187 : Blo 1668034 1669187 := bstep (se 1 (by rfl) ⟨1251890, by rfl⟩ : syracuseStep 1669187 = 2503781) B2503781
theorem B2504771 : Blo 1668034 2504771 := bstep (se 1 (by rfl) ⟨1878578, by rfl⟩ : syracuseStep 2504771 = 3757157) B3757157
theorem B1669203 : Blo 1668034 1669203 := bstep (se 1 (by rfl) ⟨1251902, by rfl⟩ : syracuseStep 1669203 = 2503805) B2503805
theorem B2504801 : Blo 1668034 2504801 := bstep (se 2 (by rfl) ⟨939300, by rfl⟩ : syracuseStep 2504801 = 1878601) B1878601
theorem B1669219 : Blo 1668034 1669219 := bstep (se 1 (by rfl) ⟨1251914, by rfl⟩ : syracuseStep 1669219 = 2503829) B2503829
theorem B2816113 : Blo 1668034 2816113 := bstep (se 2 (by rfl) ⟨1056042, by rfl⟩ : syracuseStep 2816113 = 2112085) B2112085
theorem B1669235 : Blo 1668034 1669235 := bstep (se 1 (by rfl) ⟨1251926, by rfl⟩ : syracuseStep 1669235 = 2503853) B2503853
theorem B2504819 : Blo 1668034 2504819 := bstep (se 1 (by rfl) ⟨1878614, by rfl⟩ : syracuseStep 2504819 = 3757229) B3757229
theorem B1669251 : Blo 1668034 1669251 := bstep (se 1 (by rfl) ⟨1251938, by rfl⟩ : syracuseStep 1669251 = 2503877) B2503877
theorem B2504849 : Blo 1668034 2504849 := bstep (se 2 (by rfl) ⟨939318, by rfl⟩ : syracuseStep 2504849 = 1878637) B1878637
theorem B2816147 : Blo 1668034 2816147 := bstep (se 1 (by rfl) ⟨2112110, by rfl⟩ : syracuseStep 2816147 = 4224221) B4224221
theorem B1669267 : Blo 1668034 1669267 := bstep (se 1 (by rfl) ⟨1251950, by rfl⟩ : syracuseStep 1669267 = 2503901) B2503901
theorem B1669283 : Blo 1668034 1669283 := bstep (se 1 (by rfl) ⟨1251962, by rfl⟩ : syracuseStep 1669283 = 2503925) B2503925
theorem B2504867 : Blo 1668034 2504867 := bstep (se 1 (by rfl) ⟨1878650, by rfl⟩ : syracuseStep 2504867 = 3757301) B3757301
theorem B10688689 : Blo 1668034 10688689 := bstep (se 2 (by rfl) ⟨4008258, by rfl⟩ : syracuseStep 10688689 = 8016517) B8016517
theorem B1669299 : Blo 1668034 1669299 := bstep (se 1 (by rfl) ⟨1251974, by rfl⟩ : syracuseStep 1669299 = 2503949) B2503949
theorem B2504897 : Blo 1668034 2504897 := bstep (se 2 (by rfl) ⟨939336, by rfl⟩ : syracuseStep 2504897 = 1878673) B1878673
theorem B1669315 : Blo 1668034 1669315 := bstep (se 1 (by rfl) ⟨1251986, by rfl⟩ : syracuseStep 1669315 = 2503973) B2503973
theorem B1669331 : Blo 1668034 1669331 := bstep (se 1 (by rfl) ⟨1251998, by rfl⟩ : syracuseStep 1669331 = 2503997) B2503997
theorem B2504915 : Blo 1668034 2504915 := bstep (se 1 (by rfl) ⟨1878686, by rfl⟩ : syracuseStep 2504915 = 3757373) B3757373
theorem B1669347 : Blo 1668034 1669347 := bstep (se 1 (by rfl) ⟨1252010, by rfl⟩ : syracuseStep 1669347 = 2504021) B2504021
theorem B2504945 : Blo 1668034 2504945 := bstep (se 2 (by rfl) ⟨939354, by rfl⟩ : syracuseStep 2504945 = 1878709) B1878709
theorem B1669363 : Blo 1668034 1669363 := bstep (se 1 (by rfl) ⟨1252022, by rfl⟩ : syracuseStep 1669363 = 2504045) B2504045
theorem B1669379 : Blo 1668034 1669379 := bstep (se 1 (by rfl) ⟨1252034, by rfl⟩ : syracuseStep 1669379 = 2504069) B2504069
theorem B2504963 : Blo 1668034 2504963 := bstep (se 1 (by rfl) ⟨1878722, by rfl⟩ : syracuseStep 2504963 = 3757445) B3757445
theorem B4512017 : Blo 1668034 4512017 := bstep (se 2 (by rfl) ⟨1692006, by rfl⟩ : syracuseStep 4512017 = 3384013) B3384013
theorem B2816275 : Blo 1668034 2816275 := bstep (se 1 (by rfl) ⟨2112206, by rfl⟩ : syracuseStep 2816275 = 4224413) B4224413
theorem B1669395 : Blo 1668034 1669395 := bstep (se 1 (by rfl) ⟨1252046, by rfl⟩ : syracuseStep 1669395 = 2504093) B2504093
theorem B2504993 : Blo 1668034 2504993 := bstep (se 2 (by rfl) ⟨939372, by rfl⟩ : syracuseStep 2504993 = 1878745) B1878745
theorem B2005283 : Blo 1668034 2005283 := bstep (se 1 (by rfl) ⟨1503962, by rfl⟩ : syracuseStep 2005283 = 3007925) B3007925
theorem B1669411 : Blo 1668034 1669411 := bstep (se 1 (by rfl) ⟨1252058, by rfl⟩ : syracuseStep 1669411 = 2504117) B2504117
theorem B1669427 : Blo 1668034 1669427 := bstep (se 1 (by rfl) ⟨1252070, by rfl⟩ : syracuseStep 1669427 = 2504141) B2504141
theorem B2505011 : Blo 1668034 2505011 := bstep (se 1 (by rfl) ⟨1878758, by rfl⟩ : syracuseStep 2505011 = 3757517) B3757517
theorem B1669443 : Blo 1668034 1669443 := bstep (se 1 (by rfl) ⟨1252082, by rfl⟩ : syracuseStep 1669443 = 2504165) B2504165
theorem B2505041 : Blo 1668034 2505041 := bstep (se 2 (by rfl) ⟨939390, by rfl⟩ : syracuseStep 2505041 = 1878781) B1878781
theorem B2111827 : Blo 1668034 2111827 := bstep (se 1 (by rfl) ⟨1583870, by rfl⟩ : syracuseStep 2111827 = 3167741) B3167741
theorem B2005331 : Blo 1668034 2005331 := bstep (se 1 (by rfl) ⟨1503998, by rfl⟩ : syracuseStep 2005331 = 3007997) B3007997
theorem B1669459 : Blo 1668034 1669459 := bstep (se 1 (by rfl) ⟨1252094, by rfl⟩ : syracuseStep 1669459 = 2504189) B2504189
theorem B1669475 : Blo 1668034 1669475 := bstep (se 1 (by rfl) ⟨1252106, by rfl⟩ : syracuseStep 1669475 = 2504213) B2504213
theorem B5634413 : Blo 1668034 5634413 := bstep (se 3 (by rfl) ⟨1056452, by rfl⟩ : syracuseStep 5634413 = 2112905) B2112905
theorem B1669491 : Blo 1668034 1669491 := bstep (se 1 (by rfl) ⟨1252118, by rfl⟩ : syracuseStep 1669491 = 2504237) B2504237
theorem B1669507 : Blo 1668034 1669507 := bstep (se 1 (by rfl) ⟨1252130, by rfl⟩ : syracuseStep 1669507 = 2504261) B2504261
theorem B1669523 : Blo 1668034 1669523 := bstep (se 1 (by rfl) ⟨1252142, by rfl⟩ : syracuseStep 1669523 = 2504285) B2504285
theorem B2816417 : Blo 1668034 2816417 := bstep (se 2 (by rfl) ⟨1056156, by rfl⟩ : syracuseStep 2816417 = 2112313) B2112313
theorem B5634467 : Blo 1668034 5634467 := bstep (se 1 (by rfl) ⟨4225850, by rfl⟩ : syracuseStep 5634467 = 8451701) B8451701
theorem B1669539 : Blo 1668034 1669539 := bstep (se 1 (by rfl) ⟨1252154, by rfl⟩ : syracuseStep 1669539 = 2504309) B2504309
theorem B2111923 : Blo 1668034 2111923 := bstep (se 1 (by rfl) ⟨1583942, by rfl⟩ : syracuseStep 2111923 = 3167885) B3167885
theorem B1669555 : Blo 1668034 1669555 := bstep (se 1 (by rfl) ⟨1252166, by rfl⟩ : syracuseStep 1669555 = 2504333) B2504333
theorem B1669571 : Blo 1668034 1669571 := bstep (se 1 (by rfl) ⟨1252178, by rfl⟩ : syracuseStep 1669571 = 2504357) B2504357
theorem B28916165 : Blo 1668034 28916165 := bstep (se 4 (by rfl) ⟨2710890, by rfl⟩ : syracuseStep 28916165 = 5421781) B5421781
theorem B1669587 : Blo 1668034 1669587 := bstep (se 1 (by rfl) ⟨1252190, by rfl⟩ : syracuseStep 1669587 = 2504381) B2504381
theorem B1669603 : Blo 1668034 1669603 := bstep (se 1 (by rfl) ⟨1252202, by rfl⟩ : syracuseStep 1669603 = 2504405) B2504405
theorem B18053603 : Blo 1668034 18053603 := bstep (se 1 (by rfl) ⟨13540202, by rfl⟩ : syracuseStep 18053603 = 27080405) B27080405
theorem B1669619 : Blo 1668034 1669619 := bstep (se 1 (by rfl) ⟨1252214, by rfl⟩ : syracuseStep 1669619 = 2504429) B2504429
theorem B1669635 : Blo 1668034 1669635 := bstep (se 1 (by rfl) ⟨1252226, by rfl⟩ : syracuseStep 1669635 = 2504453) B2504453
theorem B7608845 : Blo 1668034 7608845 := bstep (se 3 (by rfl) ⟨1426658, by rfl⟩ : syracuseStep 7608845 = 2853317) B2853317
theorem B1669651 : Blo 1668034 1669651 := bstep (se 1 (by rfl) ⟨1252238, by rfl⟩ : syracuseStep 1669651 = 2504477) B2504477
theorem B2816545 : Blo 1668034 2816545 := bstep (se 2 (by rfl) ⟨1056204, by rfl⟩ : syracuseStep 2816545 = 2112409) B2112409
theorem B1669667 : Blo 1668034 1669667 := bstep (se 1 (by rfl) ⟨1252250, by rfl⟩ : syracuseStep 1669667 = 2504501) B2504501
theorem B1669683 : Blo 1668034 1669683 := bstep (se 1 (by rfl) ⟨1252262, by rfl⟩ : syracuseStep 1669683 = 2504525) B2504525
theorem B2816579 : Blo 1668034 2816579 := bstep (se 1 (by rfl) ⟨2112434, by rfl⟩ : syracuseStep 2816579 = 4224869) B4224869
theorem B1669699 : Blo 1668034 1669699 := bstep (se 1 (by rfl) ⟨1252274, by rfl⟩ : syracuseStep 1669699 = 2504549) B2504549
theorem B1669715 : Blo 1668034 1669715 := bstep (se 1 (by rfl) ⟨1252286, by rfl⟩ : syracuseStep 1669715 = 2504573) B2504573
theorem B1669731 : Blo 1668034 1669731 := bstep (se 1 (by rfl) ⟨1252298, by rfl⟩ : syracuseStep 1669731 = 2504597) B2504597
theorem B1669747 : Blo 1668034 1669747 := bstep (se 1 (by rfl) ⟨1252310, by rfl⟩ : syracuseStep 1669747 = 2504621) B2504621
theorem B1669763 : Blo 1668034 1669763 := bstep (se 1 (by rfl) ⟨1252322, by rfl⟩ : syracuseStep 1669763 = 2504645) B2504645
theorem B1669779 : Blo 1668034 1669779 := bstep (se 1 (by rfl) ⟨1252334, by rfl⟩ : syracuseStep 1669779 = 2504669) B2504669
theorem B1669795 : Blo 1668034 1669795 := bstep (se 1 (by rfl) ⟨1252346, by rfl⟩ : syracuseStep 1669795 = 2504693) B2504693
theorem B5634737 : Blo 1668034 5634737 := bstep (se 2 (by rfl) ⟨2113026, by rfl⟩ : syracuseStep 5634737 = 4226053) B4226053
theorem B1669811 : Blo 1668034 1669811 := bstep (se 1 (by rfl) ⟨1252358, by rfl⟩ : syracuseStep 1669811 = 2504717) B2504717
theorem B2816707 : Blo 1668034 2816707 := bstep (se 1 (by rfl) ⟨2112530, by rfl⟩ : syracuseStep 2816707 = 4225061) B4225061
theorem B5348035 : Blo 1668034 5348035 := bstep (se 1 (by rfl) ⟨4011026, by rfl⟩ : syracuseStep 5348035 = 8022053) B8022053
theorem B1669827 : Blo 1668034 1669827 := bstep (se 1 (by rfl) ⟨1252370, by rfl⟩ : syracuseStep 1669827 = 2504741) B2504741
theorem B1669843 : Blo 1668034 1669843 := bstep (se 1 (by rfl) ⟨1252382, by rfl⟩ : syracuseStep 1669843 = 2504765) B2504765
theorem B8452835 : Blo 1668034 8452835 := bstep (se 1 (by rfl) ⟨6339626, by rfl⟩ : syracuseStep 8452835 = 12679253) B12679253
theorem B1669859 : Blo 1668034 1669859 := bstep (se 1 (by rfl) ⟨1252394, by rfl⟩ : syracuseStep 1669859 = 2504789) B2504789
theorem B1669875 : Blo 1668034 1669875 := bstep (se 1 (by rfl) ⟨1252406, by rfl⟩ : syracuseStep 1669875 = 2504813) B2504813
theorem B1669891 : Blo 1668034 1669891 := bstep (se 1 (by rfl) ⟨1252418, by rfl⟩ : syracuseStep 1669891 = 2504837) B2504837
theorem B10156805 : Blo 1668034 10156805 := bstep (se 4 (by rfl) ⟨952200, by rfl⟩ : syracuseStep 10156805 = 1904401) B1904401
theorem B1669907 : Blo 1668034 1669907 := bstep (se 1 (by rfl) ⟨1252430, by rfl⟩ : syracuseStep 1669907 = 2504861) B2504861
theorem B10697507 : Blo 1668034 10697507 := bstep (se 1 (by rfl) ⟨8023130, by rfl⟩ : syracuseStep 10697507 = 16046261) B16046261
theorem B1669923 : Blo 1668034 1669923 := bstep (se 1 (by rfl) ⟨1252442, by rfl⟩ : syracuseStep 1669923 = 2504885) B2504885
theorem B4225841 : Blo 1668034 4225841 := bstep (se 2 (by rfl) ⟨1584690, by rfl⟩ : syracuseStep 4225841 = 3169381) B3169381
theorem B1669939 : Blo 1668034 1669939 := bstep (se 1 (by rfl) ⟨1252454, by rfl⟩ : syracuseStep 1669939 = 2504909) B2504909
theorem B1669955 : Blo 1668034 1669955 := bstep (se 1 (by rfl) ⟨1252466, by rfl⟩ : syracuseStep 1669955 = 2504933) B2504933
theorem B2816849 : Blo 1668034 2816849 := bstep (se 2 (by rfl) ⟨1056318, by rfl⟩ : syracuseStep 2816849 = 2112637) B2112637
theorem B1669971 : Blo 1668034 1669971 := bstep (se 1 (by rfl) ⟨1252478, by rfl⟩ : syracuseStep 1669971 = 2504957) B2504957
theorem B4225891 : Blo 1668034 4225891 := bstep (se 1 (by rfl) ⟨3169418, by rfl⟩ : syracuseStep 4225891 = 6338837) B6338837
theorem B1669987 : Blo 1668034 1669987 := bstep (se 1 (by rfl) ⟨1252490, by rfl⟩ : syracuseStep 1669987 = 2504981) B2504981
theorem B1670003 : Blo 1668034 1670003 := bstep (se 1 (by rfl) ⟨1252502, by rfl⟩ : syracuseStep 1670003 = 2505005) B2505005
theorem B1670019 : Blo 1668034 1670019 := bstep (se 1 (by rfl) ⟨1252514, by rfl⟩ : syracuseStep 1670019 = 2505029) B2505029
theorem B2112419 : Blo 1668034 2112419 := bstep (se 1 (by rfl) ⟨1584314, by rfl⟩ : syracuseStep 2112419 = 3168629) B3168629
theorem B6339491 : Blo 1668034 6339491 := bstep (se 1 (by rfl) ⟨4754618, by rfl⟩ : syracuseStep 6339491 = 9509237) B9509237
theorem B6339505 : Blo 1668034 6339505 := bstep (se 2 (by rfl) ⟨2377314, by rfl⟩ : syracuseStep 6339505 = 4754629) B4754629
theorem B2710451 : Blo 1668034 2710451 := bstep (se 1 (by rfl) ⟨2032838, by rfl⟩ : syracuseStep 2710451 = 4065677) B4065677
theorem B12032965 : Blo 1668034 12032965 := bstep (se 4 (by rfl) ⟨1128090, by rfl⟩ : syracuseStep 12032965 = 2256181) B2256181
theorem B7125965 : Blo 1668034 7125965 := bstep (se 3 (by rfl) ⟨1336118, by rfl⟩ : syracuseStep 7125965 = 2672237) B2672237
theorem B2816977 : Blo 1668034 2816977 := bstep (se 2 (by rfl) ⟨1056366, by rfl⟩ : syracuseStep 2816977 = 2112733) B2112733
theorem B2538467 : Blo 1668034 2538467 := bstep (se 1 (by rfl) ⟨1903850, by rfl⟩ : syracuseStep 2538467 = 3807701) B3807701
theorem B4226033 : Blo 1668034 4226033 := bstep (se 2 (by rfl) ⟨1584762, by rfl⟩ : syracuseStep 4226033 = 3169525) B3169525
theorem B16268273 : Blo 1668034 16268273 := bstep (se 2 (by rfl) ⟨6100602, by rfl⟩ : syracuseStep 16268273 = 12201205) B12201205
theorem B2817011 : Blo 1668034 2817011 := bstep (se 1 (by rfl) ⟨2112758, by rfl⟩ : syracuseStep 2817011 = 4225517) B4225517
theorem B3169297 : Blo 1668034 3169297 := bstep (se 2 (by rfl) ⟨1188486, by rfl⟩ : syracuseStep 3169297 = 2376973) B2376973
theorem B5348369 : Blo 1668034 5348369 := bstep (se 2 (by rfl) ⟨2005638, by rfl⟩ : syracuseStep 5348369 = 4011277) B4011277
theorem B9509987 : Blo 1668034 9509987 := bstep (se 1 (by rfl) ⟨7132490, by rfl⟩ : syracuseStep 9509987 = 14264981) B14264981
theorem B2817139 : Blo 1668034 2817139 := bstep (se 1 (by rfl) ⟨2112854, by rfl⟩ : syracuseStep 2817139 = 4225709) B4225709
theorem B5635277 : Blo 1668034 5635277 := bstep (se 3 (by rfl) ⟨1056614, by rfl⟩ : syracuseStep 5635277 = 2113229) B2113229
theorem B2817281 : Blo 1668034 2817281 := bstep (se 2 (by rfl) ⟨1056480, by rfl⟩ : syracuseStep 2817281 = 2112961) B2112961
theorem B5635331 : Blo 1668034 5635331 := bstep (se 1 (by rfl) ⟨4226498, by rfl⟩ : syracuseStep 5635331 = 8452997) B8452997
theorem B4750609 : Blo 1668034 4750609 := bstep (se 2 (by rfl) ⟨1781478, by rfl⟩ : syracuseStep 4750609 = 3562957) B3562957
theorem B10288453 : Blo 1668034 10288453 := bstep (se 4 (by rfl) ⟨964542, by rfl⟩ : syracuseStep 10288453 = 1929085) B1929085
theorem B2817409 : Blo 1668034 2817409 := bstep (se 2 (by rfl) ⟨1056528, by rfl⟩ : syracuseStep 2817409 = 2113057) B2113057
theorem B3808657 : Blo 1668034 3808657 := bstep (se 2 (by rfl) ⟨1428246, by rfl⟩ : syracuseStep 3808657 = 2856493) B2856493
theorem B2817443 : Blo 1668034 2817443 := bstep (se 1 (by rfl) ⟨2113082, by rfl⟩ : syracuseStep 2817443 = 4226165) B4226165
theorem B6602161 : Blo 1668034 6602161 := bstep (se 2 (by rfl) ⟨2475810, by rfl⟩ : syracuseStep 6602161 = 4951621) B4951621
theorem B4513229 : Blo 1668034 4513229 := bstep (se 3 (by rfl) ⟨846230, by rfl⟩ : syracuseStep 4513229 = 1692461) B1692461
theorem B3612131 : Blo 1668034 3612131 := bstep (se 1 (by rfl) ⟨2709098, by rfl⟩ : syracuseStep 3612131 = 5418197) B5418197
theorem B8453645 : Blo 1668034 8453645 := bstep (se 3 (by rfl) ⟨1585058, by rfl⟩ : syracuseStep 8453645 = 3170117) B3170117
theorem B2375185 : Blo 1668034 2375185 := bstep (se 2 (by rfl) ⟨890694, by rfl⟩ : syracuseStep 2375185 = 1781389) B1781389
theorem B5635601 : Blo 1668034 5635601 := bstep (se 2 (by rfl) ⟨2113350, by rfl⟩ : syracuseStep 5635601 = 4226701) B4226701
theorem B4750883 : Blo 1668034 4750883 := bstep (se 1 (by rfl) ⟨3563162, by rfl⟩ : syracuseStep 4750883 = 7126325) B7126325
theorem B2817571 : Blo 1668034 2817571 := bstep (se 1 (by rfl) ⟨2113178, by rfl⟩ : syracuseStep 2817571 = 4226357) B4226357
theorem B21397061 : Blo 1668034 21397061 := bstep (se 4 (by rfl) ⟨2005974, by rfl⟩ : syracuseStep 21397061 = 4011949) B4011949
theorem B5144141 : Blo 1668034 5144141 := bstep (se 3 (by rfl) ⟨964526, by rfl⟩ : syracuseStep 5144141 = 1929053) B1929053
theorem B2113123 : Blo 1668034 2113123 := bstep (se 1 (by rfl) ⟨1584842, by rfl⟩ : syracuseStep 2113123 = 3169685) B3169685
theorem B2817713 : Blo 1668034 2817713 := bstep (se 2 (by rfl) ⟨1056642, by rfl⟩ : syracuseStep 2817713 = 2113285) B2113285
theorem B2113219 : Blo 1668034 2113219 := bstep (se 1 (by rfl) ⟨1584914, by rfl⟩ : syracuseStep 2113219 = 3169829) B3169829
theorem B4751075 : Blo 1668034 4751075 := bstep (se 1 (by rfl) ⟨3563306, by rfl⟩ : syracuseStep 4751075 = 7126613) B7126613
theorem B4513553 : Blo 1668034 4513553 := bstep (se 2 (by rfl) ⟨1692582, by rfl⟩ : syracuseStep 4513553 = 3385165) B3385165
theorem B2817841 : Blo 1668034 2817841 := bstep (se 2 (by rfl) ⟨1056690, by rfl⟩ : syracuseStep 2817841 = 2113381) B2113381
theorem B20291381 : Blo 1668034 20291381 := bstep (se 5 (by rfl) ⟨951158, by rfl⟩ : syracuseStep 20291381 = 1902317) B1902317
theorem B2817875 : Blo 1668034 2817875 := bstep (se 1 (by rfl) ⟨2113406, by rfl⟩ : syracuseStep 2817875 = 4226813) B4226813
theorem B30883781 : Blo 1668034 30883781 := bstep (se 4 (by rfl) ⟨2895354, by rfl⟩ : syracuseStep 30883781 = 5790709) B5790709
theorem B4227025 : Blo 1668034 4227025 := bstep (se 2 (by rfl) ⟨1585134, by rfl⟩ : syracuseStep 4227025 = 3170269) B3170269
theorem B2818003 : Blo 1668034 2818003 := bstep (se 1 (by rfl) ⟨2113502, by rfl⟩ : syracuseStep 2818003 = 4227005) B4227005
theorem B8126435 : Blo 1668034 8126435 := bstep (se 1 (by rfl) ⟨6094826, by rfl⟩ : syracuseStep 8126435 = 12189653) B12189653
theorem B3170315 : Blo 1668034 3170315 := bstep (se 1 (by rfl) ⟨2377736, by rfl⟩ : syracuseStep 3170315 = 4755473) B4755473
theorem B12845101 : Blo 1668034 12845101 := bstep (se 3 (by rfl) ⟨2408456, by rfl⟩ : syracuseStep 12845101 = 4816913) B4816913
theorem B14262317 : Blo 1668034 14262317 := bstep (se 3 (by rfl) ⟨2674184, by rfl⟩ : syracuseStep 14262317 = 5348369) B5348369
theorem B4227137 : Blo 1668034 4227137 := bstep (se 2 (by rfl) ⟨1585176, by rfl⟩ : syracuseStep 4227137 = 3170353) B3170353
theorem B3211339 : Blo 1668034 3211339 := bstep (se 1 (by rfl) ⟨2408504, by rfl⟩ : syracuseStep 3211339 = 4817009) B4817009
theorem B6340781 : Blo 1668034 6340781 := bstep (se 3 (by rfl) ⟨1188896, by rfl⟩ : syracuseStep 6340781 = 2377793) B2377793
theorem B3563777 : Blo 1668034 3563777 := bstep (se 2 (by rfl) ⟨1336416, by rfl⟩ : syracuseStep 3563777 = 2672833) B2672833
theorem B4514071 : Blo 1668034 4514071 := bstep (se 1 (by rfl) ⟨3385553, by rfl⟩ : syracuseStep 4514071 = 6771107) B6771107
theorem B8020403 : Blo 1668034 8020403 := bstep (se 1 (by rfl) ⟨6015302, by rfl⟩ : syracuseStep 8020403 = 12030605) B12030605
theorem B1876567 : Blo 1668034 1876567 := bstep (se 1 (by rfl) ⟨1407425, by rfl⟩ : syracuseStep 1876567 = 2814851) B2814851
theorem B1876747 : Blo 1668034 1876747 := bstep (se 1 (by rfl) ⟨1407560, by rfl⟩ : syracuseStep 1876747 = 2815121) B2815121
theorem B2376535 : Blo 1668034 2376535 := bstep (se 1 (by rfl) ⟨1782401, by rfl⟩ : syracuseStep 2376535 = 3564803) B3564803
theorem B1876855 : Blo 1668034 1876855 := bstep (se 1 (by rfl) ⟨1407641, by rfl⟩ : syracuseStep 1876855 = 2815283) B2815283
theorem B10691459 : Blo 1668034 10691459 := bstep (se 1 (by rfl) ⟨8018594, by rfl⟩ : syracuseStep 10691459 = 16037189) B16037189
theorem B6013889 : Blo 1668034 6013889 := bstep (se 2 (by rfl) ⟨2255208, by rfl⟩ : syracuseStep 6013889 = 4510417) B4510417
theorem B3564503 : Blo 1668034 3564503 := bstep (se 1 (by rfl) ⟨2673377, by rfl⟩ : syracuseStep 3564503 = 5346755) B5346755
theorem B8127449 : Blo 1668034 8127449 := bstep (se 2 (by rfl) ⟨3047793, by rfl⟩ : syracuseStep 8127449 = 6095587) B6095587
theorem B1877035 : Blo 1668034 1877035 := bstep (se 1 (by rfl) ⟨1407776, by rfl⟩ : syracuseStep 1877035 = 2815553) B2815553
theorem B6333491 : Blo 1668034 6333491 := bstep (se 1 (by rfl) ⟨4750118, by rfl⟩ : syracuseStep 6333491 = 9500237) B9500237
theorem B9503837 : Blo 1668034 9503837 := bstep (se 3 (by rfl) ⟨1781969, by rfl⟩ : syracuseStep 9503837 = 3563939) B3563939
theorem B3753089 : Blo 1668034 3753089 := bstep (se 2 (by rfl) ⟨1407408, by rfl⟩ : syracuseStep 3753089 = 2814817) B2814817
theorem B1877143 : Blo 1668034 1877143 := bstep (se 1 (by rfl) ⟨1407857, by rfl⟩ : syracuseStep 1877143 = 2815715) B2815715
theorem B7128323 : Blo 1668034 7128323 := bstep (se 1 (by rfl) ⟨5346242, by rfl⟩ : syracuseStep 7128323 = 10692485) B10692485
theorem B1877323 : Blo 1668034 1877323 := bstep (se 1 (by rfl) ⟨1407992, by rfl⟩ : syracuseStep 1877323 = 2815985) B2815985
theorem B3753305 : Blo 1668034 3753305 := bstep (se 2 (by rfl) ⟨1407489, by rfl⟩ : syracuseStep 3753305 = 2814979) B2814979
theorem B3753395 : Blo 1668034 3753395 := bstep (se 1 (by rfl) ⟨2815046, by rfl⟩ : syracuseStep 3753395 = 5630093) B5630093
theorem B1877431 : Blo 1668034 1877431 := bstep (se 1 (by rfl) ⟨1408073, by rfl⟩ : syracuseStep 1877431 = 2816147) B2816147
theorem B3753431 : Blo 1668034 3753431 := bstep (se 1 (by rfl) ⟨2815073, by rfl⟩ : syracuseStep 3753431 = 5630147) B5630147
theorem B3008011 : Blo 1668034 3008011 := bstep (se 1 (by rfl) ⟨2256008, by rfl⟩ : syracuseStep 3008011 = 4512017) B4512017
theorem B28509731 : Blo 1668034 28509731 := bstep (se 1 (by rfl) ⟨21382298, by rfl⟩ : syracuseStep 28509731 = 42764597) B42764597
theorem B4752989 : Blo 1668034 4752989 := bstep (se 3 (by rfl) ⟨891185, by rfl⟩ : syracuseStep 4752989 = 1782371) B1782371
theorem B1877611 : Blo 1668034 1877611 := bstep (se 1 (by rfl) ⟨1408208, by rfl⟩ : syracuseStep 1877611 = 2816417) B2816417
theorem B26035843 : Blo 1668034 26035843 := bstep (se 1 (by rfl) ⟨19526882, by rfl⟩ : syracuseStep 26035843 = 39053765) B39053765
theorem B19277443 : Blo 1668034 19277443 := bstep (se 1 (by rfl) ⟨14458082, by rfl⟩ : syracuseStep 19277443 = 28916165) B28916165
theorem B3753611 : Blo 1668034 3753611 := bstep (se 1 (by rfl) ⟨2815208, by rfl⟩ : syracuseStep 3753611 = 5630417) B5630417
theorem B3212939 : Blo 1668034 3212939 := bstep (se 1 (by rfl) ⟨2409704, by rfl⟩ : syracuseStep 3212939 = 4819409) B4819409
theorem B12035735 : Blo 1668034 12035735 := bstep (se 1 (by rfl) ⟨9026801, by rfl⟩ : syracuseStep 12035735 = 18053603) B18053603
theorem B5072563 : Blo 1668034 5072563 := bstep (se 1 (by rfl) ⟨3804422, by rfl⟩ : syracuseStep 5072563 = 7608845) B7608845
theorem B6334145 : Blo 1668034 6334145 := bstep (se 2 (by rfl) ⟨2375304, by rfl⟩ : syracuseStep 6334145 = 4750609) B4750609
theorem B3753665 : Blo 1668034 3753665 := bstep (se 2 (by rfl) ⟨1407624, by rfl⟩ : syracuseStep 3753665 = 2815249) B2815249
theorem B1877719 : Blo 1668034 1877719 := bstep (se 1 (by rfl) ⟨1408289, by rfl⟩ : syracuseStep 1877719 = 2816579) B2816579
theorem B5629661 : Blo 1668034 5629661 := bstep (se 3 (by rfl) ⟨1055561, by rfl⟩ : syracuseStep 5629661 = 2111123) B2111123
theorem B4753217 : Blo 1668034 4753217 := bstep (se 2 (by rfl) ⟨1782456, by rfl⟩ : syracuseStep 4753217 = 3564913) B3564913
theorem B8021825 : Blo 1668034 8021825 := bstep (se 2 (by rfl) ⟨3008184, by rfl⟩ : syracuseStep 8021825 = 6016369) B6016369
theorem B1877899 : Blo 1668034 1877899 := bstep (se 1 (by rfl) ⟨1408424, by rfl⟩ : syracuseStep 1877899 = 2816849) B2816849
theorem B3753881 : Blo 1668034 3753881 := bstep (se 2 (by rfl) ⟨1407705, by rfl⟩ : syracuseStep 3753881 = 2815411) B2815411
theorem B3753971 : Blo 1668034 3753971 := bstep (se 1 (by rfl) ⟨2815478, by rfl⟩ : syracuseStep 3753971 = 5630957) B5630957
theorem B1878007 : Blo 1668034 1878007 := bstep (se 1 (by rfl) ⟨1408505, by rfl⟩ : syracuseStep 1878007 = 2817011) B2817011
theorem B3754007 : Blo 1668034 3754007 := bstep (se 1 (by rfl) ⟨2815505, by rfl⟩ : syracuseStep 3754007 = 5631011) B5631011
theorem B4753559 : Blo 1668034 4753559 := bstep (se 1 (by rfl) ⟨3565169, by rfl⟩ : syracuseStep 4753559 = 7130339) B7130339
theorem B1878187 : Blo 1668034 1878187 := bstep (se 1 (by rfl) ⟨1408640, by rfl⟩ : syracuseStep 1878187 = 2817281) B2817281
theorem B3754187 : Blo 1668034 3754187 := bstep (se 1 (by rfl) ⟨2815640, by rfl⟩ : syracuseStep 3754187 = 5631281) B5631281
theorem B3754241 : Blo 1668034 3754241 := bstep (se 2 (by rfl) ⟨1407840, by rfl⟩ : syracuseStep 3754241 = 2815681) B2815681
theorem B1878295 : Blo 1668034 1878295 := bstep (se 1 (by rfl) ⟨1408721, by rfl⟩ : syracuseStep 1878295 = 2817443) B2817443
theorem B3008819 : Blo 1668034 3008819 := bstep (se 1 (by rfl) ⟨2256614, by rfl⟩ : syracuseStep 3008819 = 4513229) B4513229
theorem B14264707 : Blo 1668034 14264707 := bstep (se 1 (by rfl) ⟨10698530, by rfl⟩ : syracuseStep 14264707 = 21397061) B21397061
theorem B1878475 : Blo 1668034 1878475 := bstep (se 1 (by rfl) ⟨1408856, by rfl⟩ : syracuseStep 1878475 = 2817713) B2817713
theorem B3754457 : Blo 1668034 3754457 := bstep (se 2 (by rfl) ⟨1407921, by rfl⟩ : syracuseStep 3754457 = 2815843) B2815843
theorem B3009035 : Blo 1668034 3009035 := bstep (se 1 (by rfl) ⟨2256776, by rfl⟩ : syracuseStep 3009035 = 4513553) B4513553
theorem B82356749 : Blo 1668034 82356749 := bstep (se 3 (by rfl) ⟨15441890, by rfl⟩ : syracuseStep 82356749 = 30883781) B30883781
theorem B13527587 : Blo 1668034 13527587 := bstep (se 1 (by rfl) ⟨10145690, by rfl⟩ : syracuseStep 13527587 = 20291381) B20291381
theorem B3754547 : Blo 1668034 3754547 := bstep (se 1 (by rfl) ⟨2815910, by rfl⟩ : syracuseStep 3754547 = 5631821) B5631821
theorem B1878583 : Blo 1668034 1878583 := bstep (se 1 (by rfl) ⟨1408937, by rfl⟩ : syracuseStep 1878583 = 2817875) B2817875
theorem B3754583 : Blo 1668034 3754583 := bstep (se 1 (by rfl) ⟨2815937, by rfl⟩ : syracuseStep 3754583 = 5631875) B5631875
theorem B5343833 : Blo 1668034 5343833 := bstep (se 2 (by rfl) ⟨2003937, by rfl⟩ : syracuseStep 5343833 = 4007875) B4007875
theorem B21670493 : Blo 1668034 21670493 := bstep (se 3 (by rfl) ⟨4063217, by rfl⟩ : syracuseStep 21670493 = 8126435) B8126435
theorem B5712605 : Blo 1668034 5712605 := bstep (se 3 (by rfl) ⟨1071113, by rfl⟩ : syracuseStep 5712605 = 2142227) B2142227
theorem B1878763 : Blo 1668034 1878763 := bstep (se 1 (by rfl) ⟨1409072, by rfl⟩ : syracuseStep 1878763 = 2818145) B2818145
theorem B3754763 : Blo 1668034 3754763 := bstep (se 1 (by rfl) ⟨2816072, by rfl⟩ : syracuseStep 3754763 = 5632145) B5632145
theorem B8448785 : Blo 1668034 8448785 := bstep (se 2 (by rfl) ⟨3168294, by rfl⟩ : syracuseStep 8448785 = 6336589) B6336589
theorem B3754817 : Blo 1668034 3754817 := bstep (se 2 (by rfl) ⟨1408056, by rfl⟩ : syracuseStep 3754817 = 2816113) B2816113
theorem B5630795 : Blo 1668034 5630795 := bstep (se 1 (by rfl) ⟨4223096, by rfl⟩ : syracuseStep 5630795 = 8446193) B8446193
theorem B6335405 : Blo 1668034 6335405 := bstep (se 3 (by rfl) ⟨1187888, by rfl⟩ : syracuseStep 6335405 = 2375777) B2375777
theorem B8448947 : Blo 1668034 8448947 := bstep (se 1 (by rfl) ⟨6336710, by rfl⟩ : syracuseStep 8448947 = 12673421) B12673421
theorem B13536179 : Blo 1668034 13536179 := bstep (se 1 (by rfl) ⟨10152134, by rfl⟩ : syracuseStep 13536179 = 20304269) B20304269
theorem B6335435 : Blo 1668034 6335435 := bstep (se 1 (by rfl) ⟨4751576, by rfl⟩ : syracuseStep 6335435 = 9503153) B9503153
theorem B3755033 : Blo 1668034 3755033 := bstep (se 2 (by rfl) ⟨1408137, by rfl⟩ : syracuseStep 3755033 = 2816275) B2816275
theorem B5631065 : Blo 1668034 5631065 := bstep (se 2 (by rfl) ⟨2111649, by rfl⟩ : syracuseStep 5631065 = 4223299) B4223299
theorem B3755123 : Blo 1668034 3755123 := bstep (se 1 (by rfl) ⟨2816342, by rfl⟩ : syracuseStep 3755123 = 5632685) B5632685
theorem B3755159 : Blo 1668034 3755159 := bstep (se 1 (by rfl) ⟨2816369, by rfl⟩ : syracuseStep 3755159 = 5632739) B5632739
theorem B12029219 : Blo 1668034 12029219 := bstep (se 1 (by rfl) ⟨9021914, by rfl⟩ : syracuseStep 12029219 = 18043829) B18043829
theorem B14265665 : Blo 1668034 14265665 := bstep (se 2 (by rfl) ⟨5349624, by rfl⟩ : syracuseStep 14265665 = 10699249) B10699249
theorem B3755339 : Blo 1668034 3755339 := bstep (se 1 (by rfl) ⟨2816504, by rfl⟩ : syracuseStep 3755339 = 5633009) B5633009
theorem B3755393 : Blo 1668034 3755393 := bstep (se 2 (by rfl) ⟨1408272, by rfl⟩ : syracuseStep 3755393 = 2816545) B2816545
theorem B2502155 : Blo 1668034 2502155 := bstep (se 1 (by rfl) ⟨1876616, by rfl⟩ : syracuseStep 2502155 = 3753233) B3753233
theorem B9506321 : Blo 1668034 9506321 := bstep (se 2 (by rfl) ⟨3564870, by rfl⟩ : syracuseStep 9506321 = 7129741) B7129741
theorem B2502167 : Blo 1668034 2502167 := bstep (se 1 (by rfl) ⟨1876625, by rfl⟩ : syracuseStep 2502167 = 3753251) B3753251
theorem B7130699 : Blo 1668034 7130699 := bstep (se 1 (by rfl) ⟨5348024, by rfl⟩ : syracuseStep 7130699 = 10696049) B10696049
theorem B2502233 : Blo 1668034 2502233 := bstep (se 2 (by rfl) ⟨938337, by rfl⟩ : syracuseStep 2502233 = 1876675) B1876675
theorem B6336089 : Blo 1668034 6336089 := bstep (se 2 (by rfl) ⟨2376033, by rfl⟩ : syracuseStep 6336089 = 4752067) B4752067
theorem B3755609 : Blo 1668034 3755609 := bstep (se 2 (by rfl) ⟨1408353, by rfl⟩ : syracuseStep 3755609 = 2816707) B2816707
theorem B6016643 : Blo 1668034 6016643 := bstep (se 1 (by rfl) ⟨4512482, by rfl⟩ : syracuseStep 6016643 = 9024965) B9024965
theorem B3755699 : Blo 1668034 3755699 := bstep (se 1 (by rfl) ⟨2816774, by rfl⟩ : syracuseStep 3755699 = 5633549) B5633549
theorem B2502347 : Blo 1668034 2502347 := bstep (se 1 (by rfl) ⟨1876760, by rfl⟩ : syracuseStep 2502347 = 3753521) B3753521
theorem B2502359 : Blo 1668034 2502359 := bstep (se 1 (by rfl) ⟨1876769, by rfl⟩ : syracuseStep 2502359 = 3753539) B3753539
theorem B3755735 : Blo 1668034 3755735 := bstep (se 1 (by rfl) ⟨2816801, by rfl⟩ : syracuseStep 3755735 = 5633603) B5633603
theorem B6016771 : Blo 1668034 6016771 := bstep (se 1 (by rfl) ⟨4512578, by rfl⟩ : syracuseStep 6016771 = 9025157) B9025157
theorem B5631767 : Blo 1668034 5631767 := bstep (se 1 (by rfl) ⟨4223825, by rfl⟩ : syracuseStep 5631767 = 8447651) B8447651
theorem B2502425 : Blo 1668034 2502425 := bstep (se 2 (by rfl) ⟨938409, by rfl⟩ : syracuseStep 2502425 = 1876819) B1876819
theorem B3804953 : Blo 1668034 3804953 := bstep (se 2 (by rfl) ⟨1426857, by rfl⟩ : syracuseStep 3804953 = 2853715) B2853715
theorem B2502539 : Blo 1668034 2502539 := bstep (se 1 (by rfl) ⟨1876904, by rfl⟩ : syracuseStep 2502539 = 3753809) B3753809
theorem B3755915 : Blo 1668034 3755915 := bstep (se 1 (by rfl) ⟨2816936, by rfl⟩ : syracuseStep 3755915 = 5633873) B5633873
theorem B2502551 : Blo 1668034 2502551 := bstep (se 1 (by rfl) ⟨1876913, by rfl⟩ : syracuseStep 2502551 = 3753827) B3753827
theorem B6336407 : Blo 1668034 6336407 := bstep (se 1 (by rfl) ⟨4752305, by rfl⟩ : syracuseStep 6336407 = 9504611) B9504611
theorem B16043953 : Blo 1668034 16043953 := bstep (se 2 (by rfl) ⟨6016482, by rfl⟩ : syracuseStep 16043953 = 12032965) B12032965
theorem B3755969 : Blo 1668034 3755969 := bstep (se 2 (by rfl) ⟨1408488, by rfl⟩ : syracuseStep 3755969 = 2816977) B2816977
theorem B2502617 : Blo 1668034 2502617 := bstep (se 2 (by rfl) ⟨938481, by rfl⟩ : syracuseStep 2502617 = 1876963) B1876963
theorem B2502731 : Blo 1668034 2502731 := bstep (se 1 (by rfl) ⟨1877048, by rfl⟩ : syracuseStep 2502731 = 3754097) B3754097
theorem B2502743 : Blo 1668034 2502743 := bstep (se 1 (by rfl) ⟨1877057, by rfl⟩ : syracuseStep 2502743 = 3754115) B3754115
theorem B2502809 : Blo 1668034 2502809 := bstep (se 2 (by rfl) ⟨938553, by rfl⟩ : syracuseStep 2502809 = 1877107) B1877107
theorem B3756185 : Blo 1668034 3756185 := bstep (se 2 (by rfl) ⟨1408569, by rfl⟩ : syracuseStep 3756185 = 2817139) B2817139
theorem B5345473 : Blo 1668034 5345473 := bstep (se 2 (by rfl) ⟨2004552, by rfl⟩ : syracuseStep 5345473 = 4009105) B4009105
theorem B3756275 : Blo 1668034 3756275 := bstep (se 1 (by rfl) ⟨2817206, by rfl⟩ : syracuseStep 3756275 = 5634413) B5634413
theorem B2502923 : Blo 1668034 2502923 := bstep (se 1 (by rfl) ⟨1877192, by rfl⟩ : syracuseStep 2502923 = 3754385) B3754385
theorem B2502935 : Blo 1668034 2502935 := bstep (se 1 (by rfl) ⟨1877201, by rfl⟩ : syracuseStep 2502935 = 3754403) B3754403
theorem B3756311 : Blo 1668034 3756311 := bstep (se 1 (by rfl) ⟨2817233, by rfl⟩ : syracuseStep 3756311 = 5634467) B5634467
theorem B5632307 : Blo 1668034 5632307 := bstep (se 1 (by rfl) ⟨4224230, by rfl⟩ : syracuseStep 5632307 = 8448461) B8448461
theorem B2503001 : Blo 1668034 2503001 := bstep (se 2 (by rfl) ⟨938625, by rfl⟩ : syracuseStep 2503001 = 1877251) B1877251
theorem B13717937 : Blo 1668034 13717937 := bstep (se 2 (by rfl) ⟨5144226, by rfl⟩ : syracuseStep 13717937 = 10288453) B10288453
theorem B4223411 : Blo 1668034 4223411 := bstep (se 1 (by rfl) ⟨3167558, by rfl⟩ : syracuseStep 4223411 = 6335117) B6335117
theorem B2503115 : Blo 1668034 2503115 := bstep (se 1 (by rfl) ⟨1877336, by rfl⟩ : syracuseStep 2503115 = 3754673) B3754673
theorem B3756491 : Blo 1668034 3756491 := bstep (se 1 (by rfl) ⟨2817368, by rfl⟩ : syracuseStep 3756491 = 5634737) B5634737
theorem B2503127 : Blo 1668034 2503127 := bstep (se 1 (by rfl) ⟨1877345, by rfl⟩ : syracuseStep 2503127 = 3754691) B3754691
theorem B3756545 : Blo 1668034 3756545 := bstep (se 2 (by rfl) ⟨1408704, by rfl⟩ : syracuseStep 3756545 = 2817409) B2817409
theorem B6771203 : Blo 1668034 6771203 := bstep (se 1 (by rfl) ⟨5078402, by rfl⟩ : syracuseStep 6771203 = 10156805) B10156805
theorem B14258693 : Blo 1668034 14258693 := bstep (se 4 (by rfl) ⟨1336752, by rfl⟩ : syracuseStep 14258693 = 2673505) B2673505
theorem B7131671 : Blo 1668034 7131671 := bstep (se 1 (by rfl) ⟨5348753, by rfl⟩ : syracuseStep 7131671 = 10697507) B10697507
theorem B2503193 : Blo 1668034 2503193 := bstep (se 2 (by rfl) ⟨938697, by rfl⟩ : syracuseStep 2503193 = 1877395) B1877395
theorem B6337075 : Blo 1668034 6337075 := bstep (se 1 (by rfl) ⟨4752806, by rfl⟩ : syracuseStep 6337075 = 9505613) B9505613
theorem B5632577 : Blo 1668034 5632577 := bstep (se 2 (by rfl) ⟨2112216, by rfl⟩ : syracuseStep 5632577 = 4224433) B4224433
theorem B8802881 : Blo 1668034 8802881 := bstep (se 2 (by rfl) ⟨3301080, by rfl⟩ : syracuseStep 8802881 = 6602161) B6602161
theorem B12669533 : Blo 1668034 12669533 := bstep (se 3 (by rfl) ⟨2375537, by rfl⟩ : syracuseStep 12669533 = 4751075) B4751075
theorem B8024669 : Blo 1668034 8024669 := bstep (se 3 (by rfl) ⟨1504625, by rfl⟩ : syracuseStep 8024669 = 3009251) B3009251
theorem B1806967 : Blo 1668034 1806967 := bstep (se 1 (by rfl) ⟨1355225, by rfl⟩ : syracuseStep 1806967 = 2710451) B2710451
theorem B2503307 : Blo 1668034 2503307 := bstep (se 1 (by rfl) ⟨1877480, by rfl⟩ : syracuseStep 2503307 = 3754961) B3754961
theorem B2503319 : Blo 1668034 2503319 := bstep (se 1 (by rfl) ⟨1877489, by rfl⟩ : syracuseStep 2503319 = 3754979) B3754979
theorem B1692311 : Blo 1668034 1692311 := bstep (se 1 (by rfl) ⟨1269233, by rfl⟩ : syracuseStep 1692311 = 2538467) B2538467
theorem B6861485 : Blo 1668034 6861485 := bstep (se 3 (by rfl) ⟨1286528, by rfl⟩ : syracuseStep 6861485 = 2573057) B2573057
theorem B3166913 : Blo 1668034 3166913 := bstep (se 2 (by rfl) ⟨1187592, by rfl⟩ : syracuseStep 3166913 = 2375185) B2375185
theorem B2503385 : Blo 1668034 2503385 := bstep (se 2 (by rfl) ⟨938769, by rfl⟩ : syracuseStep 2503385 = 1877539) B1877539
theorem B3756761 : Blo 1668034 3756761 := bstep (se 2 (by rfl) ⟨1408785, by rfl⟩ : syracuseStep 3756761 = 2817571) B2817571
theorem B5075677 : Blo 1668034 5075677 := bstep (se 3 (by rfl) ⟨951689, by rfl⟩ : syracuseStep 5075677 = 1903379) B1903379
theorem B3756851 : Blo 1668034 3756851 := bstep (se 1 (by rfl) ⟨2817638, by rfl⟩ : syracuseStep 3756851 = 5635277) B5635277
theorem B5075777 : Blo 1668034 5075777 := bstep (se 2 (by rfl) ⟨1903416, by rfl⟩ : syracuseStep 5075777 = 3806833) B3806833
theorem B2503499 : Blo 1668034 2503499 := bstep (se 1 (by rfl) ⟨1877624, by rfl⟩ : syracuseStep 2503499 = 3755249) B3755249
theorem B8450891 : Blo 1668034 8450891 := bstep (se 1 (by rfl) ⟨6338168, by rfl⟩ : syracuseStep 8450891 = 12676337) B12676337
theorem B2503511 : Blo 1668034 2503511 := bstep (se 1 (by rfl) ⟨1877633, by rfl⟩ : syracuseStep 2503511 = 3755267) B3755267
theorem B3756887 : Blo 1668034 3756887 := bstep (se 1 (by rfl) ⟨2817665, by rfl⟩ : syracuseStep 3756887 = 5635331) B5635331
theorem B2814871 : Blo 1668034 2814871 := bstep (se 1 (by rfl) ⟨2111153, by rfl⟩ : syracuseStep 2814871 = 4222307) B4222307
theorem B2503577 : Blo 1668034 2503577 := bstep (se 2 (by rfl) ⟨938841, by rfl⟩ : syracuseStep 2503577 = 1877683) B1877683
theorem B1668043 : Blo 1668034 1668043 := bstep (se 1 (by rfl) ⟨1251032, by rfl⟩ : syracuseStep 1668043 = 2502065) B2502065
theorem B4223947 : Blo 1668034 4223947 := bstep (se 1 (by rfl) ⟨3167960, by rfl⟩ : syracuseStep 4223947 = 6335921) B6335921
theorem B1668055 : Blo 1668034 1668055 := bstep (se 1 (by rfl) ⟨1251041, by rfl⟩ : syracuseStep 1668055 = 2502083) B2502083
theorem B1668075 : Blo 1668034 1668075 := bstep (se 1 (by rfl) ⟨1251056, by rfl⟩ : syracuseStep 1668075 = 2502113) B2502113
theorem B1668087 : Blo 1668034 1668087 := bstep (se 1 (by rfl) ⟨1251065, by rfl⟩ : syracuseStep 1668087 = 2502131) B2502131
theorem B1668107 : Blo 1668034 1668107 := bstep (se 1 (by rfl) ⟨1251080, by rfl⟩ : syracuseStep 1668107 = 2502161) B2502161
theorem B2503691 : Blo 1668034 2503691 := bstep (se 1 (by rfl) ⟨1877768, by rfl⟩ : syracuseStep 2503691 = 3755537) B3755537
theorem B3757067 : Blo 1668034 3757067 := bstep (se 1 (by rfl) ⟨2817800, by rfl⟩ : syracuseStep 3757067 = 5635601) B5635601
theorem B1668119 : Blo 1668034 1668119 := bstep (se 1 (by rfl) ⟨1251089, by rfl⟩ : syracuseStep 1668119 = 2502179) B2502179
theorem B3167255 : Blo 1668034 3167255 := bstep (se 1 (by rfl) ⟨2375441, by rfl⟩ : syracuseStep 3167255 = 4750883) B4750883
theorem B2503703 : Blo 1668034 2503703 := bstep (se 1 (by rfl) ⟨1877777, by rfl⟩ : syracuseStep 2503703 = 3755555) B3755555
theorem B1668139 : Blo 1668034 1668139 := bstep (se 1 (by rfl) ⟨1251104, by rfl⟩ : syracuseStep 1668139 = 2502209) B2502209
theorem B3429427 : Blo 1668034 3429427 := bstep (se 1 (by rfl) ⟨2572070, by rfl⟩ : syracuseStep 3429427 = 5144141) B5144141
theorem B1668151 : Blo 1668034 1668151 := bstep (se 1 (by rfl) ⟨1251113, by rfl⟩ : syracuseStep 1668151 = 2502227) B2502227
theorem B3757121 : Blo 1668034 3757121 := bstep (se 2 (by rfl) ⟨1408920, by rfl⟩ : syracuseStep 3757121 = 2817841) B2817841
theorem B1668171 : Blo 1668034 1668171 := bstep (se 1 (by rfl) ⟨1251128, by rfl⟩ : syracuseStep 1668171 = 2502257) B2502257
theorem B1668183 : Blo 1668034 1668183 := bstep (se 1 (by rfl) ⟨1251137, by rfl⟩ : syracuseStep 1668183 = 2502275) B2502275
theorem B4224089 : Blo 1668034 4224089 := bstep (se 2 (by rfl) ⟨1584033, by rfl⟩ : syracuseStep 4224089 = 3168067) B3168067
theorem B2503769 : Blo 1668034 2503769 := bstep (se 2 (by rfl) ⟨938913, by rfl⟩ : syracuseStep 2503769 = 1877827) B1877827
theorem B5633117 : Blo 1668034 5633117 := bstep (se 3 (by rfl) ⟨1056209, by rfl⟩ : syracuseStep 5633117 = 2112419) B2112419
theorem B1668203 : Blo 1668034 1668203 := bstep (se 1 (by rfl) ⟨1251152, by rfl⟩ : syracuseStep 1668203 = 2502305) B2502305
theorem B1668215 : Blo 1668034 1668215 := bstep (se 1 (by rfl) ⟨1251161, by rfl⟩ : syracuseStep 1668215 = 2502323) B2502323
theorem B1668235 : Blo 1668034 1668235 := bstep (se 1 (by rfl) ⟨1251176, by rfl⟩ : syracuseStep 1668235 = 2502353) B2502353
theorem B1668247 : Blo 1668034 1668247 := bstep (se 1 (by rfl) ⟨1251185, by rfl⟩ : syracuseStep 1668247 = 2502371) B2502371
theorem B14447767 : Blo 1668034 14447767 := bstep (se 1 (by rfl) ⟨10835825, by rfl⟩ : syracuseStep 14447767 = 21671651) B21671651
theorem B1668267 : Blo 1668034 1668267 := bstep (se 1 (by rfl) ⟨1251200, by rfl⟩ : syracuseStep 1668267 = 2502401) B2502401
theorem B7713971 : Blo 1668034 7713971 := bstep (se 1 (by rfl) ⟨5785478, by rfl⟩ : syracuseStep 7713971 = 11570957) B11570957
theorem B1668279 : Blo 1668034 1668279 := bstep (se 1 (by rfl) ⟨1251209, by rfl⟩ : syracuseStep 1668279 = 2502419) B2502419
theorem B1668299 : Blo 1668034 1668299 := bstep (se 1 (by rfl) ⟨1251224, by rfl⟩ : syracuseStep 1668299 = 2502449) B2502449
theorem B2503883 : Blo 1668034 2503883 := bstep (se 1 (by rfl) ⟨1877912, by rfl⟩ : syracuseStep 2503883 = 3755825) B3755825
theorem B1668311 : Blo 1668034 1668311 := bstep (se 1 (by rfl) ⟨1251233, by rfl⟩ : syracuseStep 1668311 = 2502467) B2502467
theorem B2503895 : Blo 1668034 2503895 := bstep (se 1 (by rfl) ⟨1877921, by rfl⟩ : syracuseStep 2503895 = 3755843) B3755843
theorem B1668331 : Blo 1668034 1668331 := bstep (se 1 (by rfl) ⟨1251248, by rfl⟩ : syracuseStep 1668331 = 2502497) B2502497
theorem B1668343 : Blo 1668034 1668343 := bstep (se 1 (by rfl) ⟨1251257, by rfl⟩ : syracuseStep 1668343 = 2502515) B2502515
theorem B1668363 : Blo 1668034 1668363 := bstep (se 1 (by rfl) ⟨1251272, by rfl⟩ : syracuseStep 1668363 = 2502545) B2502545
theorem B1668375 : Blo 1668034 1668375 := bstep (se 1 (by rfl) ⟨1251281, by rfl⟩ : syracuseStep 1668375 = 2502563) B2502563
theorem B1783063 : Blo 1668034 1783063 := bstep (se 1 (by rfl) ⟨1337297, by rfl⟩ : syracuseStep 1783063 = 2674595) B2674595
theorem B2503961 : Blo 1668034 2503961 := bstep (se 2 (by rfl) ⟨938985, by rfl⟩ : syracuseStep 2503961 = 1877971) B1877971
theorem B3757337 : Blo 1668034 3757337 := bstep (se 2 (by rfl) ⟨1409001, by rfl⟩ : syracuseStep 3757337 = 2818003) B2818003
theorem B1668395 : Blo 1668034 1668395 := bstep (se 1 (by rfl) ⟨1251296, by rfl⟩ : syracuseStep 1668395 = 2502593) B2502593
theorem B19010861 : Blo 1668034 19010861 := bstep (se 3 (by rfl) ⟨3564536, by rfl⟩ : syracuseStep 19010861 = 7129073) B7129073
theorem B1668407 : Blo 1668034 1668407 := bstep (se 1 (by rfl) ⟨1251305, by rfl⟩ : syracuseStep 1668407 = 2502611) B2502611
theorem B6763841 : Blo 1668034 6763841 := bstep (se 2 (by rfl) ⟨2536440, by rfl⟩ : syracuseStep 6763841 = 5072881) B5072881
theorem B1668427 : Blo 1668034 1668427 := bstep (se 1 (by rfl) ⟨1251320, by rfl⟩ : syracuseStep 1668427 = 2502641) B2502641
theorem B1668439 : Blo 1668034 1668439 := bstep (se 1 (by rfl) ⟨1251329, by rfl⟩ : syracuseStep 1668439 = 2502659) B2502659
theorem B1668459 : Blo 1668034 1668459 := bstep (se 1 (by rfl) ⟨1251344, by rfl⟩ : syracuseStep 1668459 = 2502689) B2502689
theorem B3757427 : Blo 1668034 3757427 := bstep (se 1 (by rfl) ⟨2818070, by rfl⟩ : syracuseStep 3757427 = 5636141) B5636141
theorem B1668471 : Blo 1668034 1668471 := bstep (se 1 (by rfl) ⟨1251353, by rfl⟩ : syracuseStep 1668471 = 2502707) B2502707
theorem B1668491 : Blo 1668034 1668491 := bstep (se 1 (by rfl) ⟨1251368, by rfl⟩ : syracuseStep 1668491 = 2502737) B2502737
theorem B2504075 : Blo 1668034 2504075 := bstep (se 1 (by rfl) ⟨1878056, by rfl⟩ : syracuseStep 2504075 = 3756113) B3756113
theorem B1668503 : Blo 1668034 1668503 := bstep (se 1 (by rfl) ⟨1251377, by rfl⟩ : syracuseStep 1668503 = 2502755) B2502755
theorem B2504087 : Blo 1668034 2504087 := bstep (se 1 (by rfl) ⟨1878065, by rfl⟩ : syracuseStep 2504087 = 3756131) B3756131
theorem B3757463 : Blo 1668034 3757463 := bstep (se 1 (by rfl) ⟨2818097, by rfl⟩ : syracuseStep 3757463 = 5636195) B5636195
theorem B1668523 : Blo 1668034 1668523 := bstep (se 1 (by rfl) ⟨1251392, by rfl⟩ : syracuseStep 1668523 = 2502785) B2502785
theorem B1668535 : Blo 1668034 1668535 := bstep (se 1 (by rfl) ⟨1251401, by rfl⟩ : syracuseStep 1668535 = 2502803) B2502803
theorem B1668555 : Blo 1668034 1668555 := bstep (se 1 (by rfl) ⟨1251416, by rfl⟩ : syracuseStep 1668555 = 2502833) B2502833
theorem B1668567 : Blo 1668034 1668567 := bstep (se 1 (by rfl) ⟨1251425, by rfl⟩ : syracuseStep 1668567 = 2502851) B2502851
theorem B2504153 : Blo 1668034 2504153 := bstep (se 2 (by rfl) ⟨939057, by rfl⟩ : syracuseStep 2504153 = 1878115) B1878115
theorem B1668587 : Blo 1668034 1668587 := bstep (se 1 (by rfl) ⟨1251440, by rfl⟩ : syracuseStep 1668587 = 2502881) B2502881
theorem B1668599 : Blo 1668034 1668599 := bstep (se 1 (by rfl) ⟨1251449, by rfl⟩ : syracuseStep 1668599 = 2502899) B2502899
theorem B2815499 : Blo 1668034 2815499 := bstep (se 1 (by rfl) ⟨2111624, by rfl⟩ : syracuseStep 2815499 = 4223249) B4223249
theorem B1668619 : Blo 1668034 1668619 := bstep (se 1 (by rfl) ⟨1251464, by rfl⟩ : syracuseStep 1668619 = 2502929) B2502929
theorem B1668631 : Blo 1668034 1668631 := bstep (se 1 (by rfl) ⟨1251473, by rfl⟩ : syracuseStep 1668631 = 2502947) B2502947
theorem B1668651 : Blo 1668034 1668651 := bstep (se 1 (by rfl) ⟨1251488, by rfl⟩ : syracuseStep 1668651 = 2502977) B2502977
theorem B1668663 : Blo 1668034 1668663 := bstep (se 1 (by rfl) ⟨1251497, by rfl⟩ : syracuseStep 1668663 = 2502995) B2502995
theorem B14251585 : Blo 1668034 14251585 := bstep (se 2 (by rfl) ⟨5344344, by rfl⟩ : syracuseStep 14251585 = 10688689) B10688689
theorem B10688075 : Blo 1668034 10688075 := bstep (se 1 (by rfl) ⟨8016056, by rfl⟩ : syracuseStep 10688075 = 16032113) B16032113
theorem B1668683 : Blo 1668034 1668683 := bstep (se 1 (by rfl) ⟨1251512, by rfl⟩ : syracuseStep 1668683 = 2503025) B2503025
theorem B2504267 : Blo 1668034 2504267 := bstep (se 1 (by rfl) ⟨1878200, by rfl⟩ : syracuseStep 2504267 = 3756401) B3756401
theorem B1668695 : Blo 1668034 1668695 := bstep (se 1 (by rfl) ⟨1251521, by rfl⟩ : syracuseStep 1668695 = 2503043) B2503043
theorem B2504279 : Blo 1668034 2504279 := bstep (se 1 (by rfl) ⟨1878209, by rfl⟩ : syracuseStep 2504279 = 3756419) B3756419
theorem B1668715 : Blo 1668034 1668715 := bstep (se 1 (by rfl) ⟨1251536, by rfl⟩ : syracuseStep 1668715 = 2503073) B2503073
theorem B1668727 : Blo 1668034 1668727 := bstep (se 1 (by rfl) ⟨1251545, by rfl⟩ : syracuseStep 1668727 = 2503091) B2503091
theorem B1668747 : Blo 1668034 1668747 := bstep (se 1 (by rfl) ⟨1251560, by rfl⟩ : syracuseStep 1668747 = 2503121) B2503121
theorem B2815627 : Blo 1668034 2815627 := bstep (se 1 (by rfl) ⟨2111720, by rfl⟩ : syracuseStep 2815627 = 4223441) B4223441
theorem B1668759 : Blo 1668034 1668759 := bstep (se 1 (by rfl) ⟨1251569, by rfl⟩ : syracuseStep 1668759 = 2503139) B2503139
theorem B2504345 : Blo 1668034 2504345 := bstep (se 2 (by rfl) ⟨939129, by rfl⟩ : syracuseStep 2504345 = 1878259) B1878259
theorem B1668779 : Blo 1668034 1668779 := bstep (se 1 (by rfl) ⟨1251584, by rfl⟩ : syracuseStep 1668779 = 2503169) B2503169
theorem B3167923 : Blo 1668034 3167923 := bstep (se 1 (by rfl) ⟨2375942, by rfl⟩ : syracuseStep 3167923 = 4751885) B4751885
theorem B1668791 : Blo 1668034 1668791 := bstep (se 1 (by rfl) ⟨1251593, by rfl⟩ : syracuseStep 1668791 = 2503187) B2503187
theorem B2111179 : Blo 1668034 2111179 := bstep (se 1 (by rfl) ⟨1583384, by rfl⟩ : syracuseStep 2111179 = 3166769) B3166769
theorem B1668811 : Blo 1668034 1668811 := bstep (se 1 (by rfl) ⟨1251608, by rfl⟩ : syracuseStep 1668811 = 2503217) B2503217
theorem B1668823 : Blo 1668034 1668823 := bstep (se 1 (by rfl) ⟨1251617, by rfl⟩ : syracuseStep 1668823 = 2503235) B2503235
theorem B1668843 : Blo 1668034 1668843 := bstep (se 1 (by rfl) ⟨1251632, by rfl⟩ : syracuseStep 1668843 = 2503265) B2503265
theorem B1668855 : Blo 1668034 1668855 := bstep (se 1 (by rfl) ⟨1251641, by rfl⟩ : syracuseStep 1668855 = 2503283) B2503283
theorem B1668875 : Blo 1668034 1668875 := bstep (se 1 (by rfl) ⟨1251656, by rfl⟩ : syracuseStep 1668875 = 2503313) B2503313
theorem B2504459 : Blo 1668034 2504459 := bstep (se 1 (by rfl) ⟨1878344, by rfl⟩ : syracuseStep 2504459 = 3756689) B3756689
theorem B6338321 : Blo 1668034 6338321 := bstep (se 2 (by rfl) ⟨2376870, by rfl⟩ : syracuseStep 6338321 = 4753741) B4753741
theorem B1668887 : Blo 1668034 1668887 := bstep (se 1 (by rfl) ⟨1251665, by rfl⟩ : syracuseStep 1668887 = 2503331) B2503331
theorem B2815769 : Blo 1668034 2815769 := bstep (se 2 (by rfl) ⟨1055913, by rfl⟩ : syracuseStep 2815769 = 2111827) B2111827
theorem B2504471 : Blo 1668034 2504471 := bstep (se 1 (by rfl) ⟨1878353, by rfl⟩ : syracuseStep 2504471 = 3756707) B3756707
theorem B1668907 : Blo 1668034 1668907 := bstep (se 1 (by rfl) ⟨1251680, by rfl⟩ : syracuseStep 1668907 = 2503361) B2503361
theorem B1668919 : Blo 1668034 1668919 := bstep (se 1 (by rfl) ⟨1251689, by rfl⟩ : syracuseStep 1668919 = 2503379) B2503379
theorem B1668939 : Blo 1668034 1668939 := bstep (se 1 (by rfl) ⟨1251704, by rfl⟩ : syracuseStep 1668939 = 2503409) B2503409
theorem B1668951 : Blo 1668034 1668951 := bstep (se 1 (by rfl) ⟨1251713, by rfl⟩ : syracuseStep 1668951 = 2503427) B2503427
theorem B2504537 : Blo 1668034 2504537 := bstep (se 2 (by rfl) ⟨939201, by rfl⟩ : syracuseStep 2504537 = 1878403) B1878403
theorem B1668971 : Blo 1668034 1668971 := bstep (se 1 (by rfl) ⟨1251728, by rfl⟩ : syracuseStep 1668971 = 2503457) B2503457
theorem B1668983 : Blo 1668034 1668983 := bstep (se 1 (by rfl) ⟨1251737, by rfl⟩ : syracuseStep 1668983 = 2503475) B2503475
theorem B1669003 : Blo 1668034 1669003 := bstep (se 1 (by rfl) ⟨1251752, by rfl⟩ : syracuseStep 1669003 = 2503505) B2503505
theorem B1669015 : Blo 1668034 1669015 := bstep (se 1 (by rfl) ⟨1251761, by rfl⟩ : syracuseStep 1669015 = 2503523) B2503523
theorem B4224919 : Blo 1668034 4224919 := bstep (se 1 (by rfl) ⟨3168689, by rfl⟩ : syracuseStep 4224919 = 6337379) B6337379
theorem B2815897 : Blo 1668034 2815897 := bstep (se 2 (by rfl) ⟨1055961, by rfl⟩ : syracuseStep 2815897 = 2111923) B2111923
theorem B1669035 : Blo 1668034 1669035 := bstep (se 1 (by rfl) ⟨1251776, by rfl⟩ : syracuseStep 1669035 = 2503553) B2503553
theorem B1669047 : Blo 1668034 1669047 := bstep (se 1 (by rfl) ⟨1251785, by rfl⟩ : syracuseStep 1669047 = 2503571) B2503571
theorem B1669067 : Blo 1668034 1669067 := bstep (se 1 (by rfl) ⟨1251800, by rfl⟩ : syracuseStep 1669067 = 2503601) B2503601
theorem B2504651 : Blo 1668034 2504651 := bstep (se 1 (by rfl) ⟨1878488, by rfl⟩ : syracuseStep 2504651 = 3756977) B3756977
theorem B2111447 : Blo 1668034 2111447 := bstep (se 1 (by rfl) ⟨1583585, by rfl⟩ : syracuseStep 2111447 = 3167171) B3167171
theorem B2709463 : Blo 1668034 2709463 := bstep (se 1 (by rfl) ⟨2032097, by rfl⟩ : syracuseStep 2709463 = 4064195) B4064195
theorem B1669079 : Blo 1668034 1669079 := bstep (se 1 (by rfl) ⟨1251809, by rfl⟩ : syracuseStep 1669079 = 2503619) B2503619
theorem B2504663 : Blo 1668034 2504663 := bstep (se 1 (by rfl) ⟨1878497, by rfl⟩ : syracuseStep 2504663 = 3756995) B3756995
theorem B1669099 : Blo 1668034 1669099 := bstep (se 1 (by rfl) ⟨1251824, by rfl⟩ : syracuseStep 1669099 = 2503649) B2503649
theorem B1669111 : Blo 1668034 1669111 := bstep (se 1 (by rfl) ⟨1251833, by rfl⟩ : syracuseStep 1669111 = 2503667) B2503667
theorem B1669131 : Blo 1668034 1669131 := bstep (se 1 (by rfl) ⟨1251848, by rfl⟩ : syracuseStep 1669131 = 2503697) B2503697
theorem B1669143 : Blo 1668034 1669143 := bstep (se 1 (by rfl) ⟨1251857, by rfl⟩ : syracuseStep 1669143 = 2503715) B2503715
theorem B2504729 : Blo 1668034 2504729 := bstep (se 2 (by rfl) ⟨939273, by rfl⟩ : syracuseStep 2504729 = 1878547) B1878547
theorem B1669163 : Blo 1668034 1669163 := bstep (se 1 (by rfl) ⟨1251872, by rfl⟩ : syracuseStep 1669163 = 2503745) B2503745
theorem B1669175 : Blo 1668034 1669175 := bstep (se 1 (by rfl) ⟨1251881, by rfl⟩ : syracuseStep 1669175 = 2503763) B2503763
theorem B1669195 : Blo 1668034 1669195 := bstep (se 1 (by rfl) ⟨1251896, by rfl⟩ : syracuseStep 1669195 = 2503793) B2503793
theorem B1669207 : Blo 1668034 1669207 := bstep (se 1 (by rfl) ⟨1251905, by rfl⟩ : syracuseStep 1669207 = 2503811) B2503811
theorem B5347421 : Blo 1668034 5347421 := bstep (se 3 (by rfl) ⟨1002641, by rfl⟩ : syracuseStep 5347421 = 2005283) B2005283
theorem B1669227 : Blo 1668034 1669227 := bstep (se 1 (by rfl) ⟨1251920, by rfl⟩ : syracuseStep 1669227 = 2503841) B2503841
theorem B3168371 : Blo 1668034 3168371 := bstep (se 1 (by rfl) ⟨2376278, by rfl⟩ : syracuseStep 3168371 = 4752557) B4752557
theorem B1669239 : Blo 1668034 1669239 := bstep (se 1 (by rfl) ⟨1251929, by rfl⟩ : syracuseStep 1669239 = 2503859) B2503859
theorem B1669259 : Blo 1668034 1669259 := bstep (se 1 (by rfl) ⟨1251944, by rfl⟩ : syracuseStep 1669259 = 2503889) B2503889
theorem B2504843 : Blo 1668034 2504843 := bstep (se 1 (by rfl) ⟨1878632, by rfl⟩ : syracuseStep 2504843 = 3757265) B3757265
theorem B1669271 : Blo 1668034 1669271 := bstep (se 1 (by rfl) ⟨1251953, by rfl⟩ : syracuseStep 1669271 = 2503907) B2503907
theorem B2504855 : Blo 1668034 2504855 := bstep (se 1 (by rfl) ⟨1878641, by rfl⟩ : syracuseStep 2504855 = 3757283) B3757283
theorem B3168409 : Blo 1668034 3168409 := bstep (se 2 (by rfl) ⟨1188153, by rfl⟩ : syracuseStep 3168409 = 2376307) B2376307
theorem B1669291 : Blo 1668034 1669291 := bstep (se 1 (by rfl) ⟨1251968, by rfl⟩ : syracuseStep 1669291 = 2503937) B2503937
theorem B1669303 : Blo 1668034 1669303 := bstep (se 1 (by rfl) ⟨1251977, by rfl⟩ : syracuseStep 1669303 = 2503955) B2503955
theorem B1669323 : Blo 1668034 1669323 := bstep (se 1 (by rfl) ⟨1251992, by rfl⟩ : syracuseStep 1669323 = 2503985) B2503985
theorem B5634251 : Blo 1668034 5634251 := bstep (se 1 (by rfl) ⟨4225688, by rfl⟩ : syracuseStep 5634251 = 8451377) B8451377
theorem B1669335 : Blo 1668034 1669335 := bstep (se 1 (by rfl) ⟨1252001, by rfl⟩ : syracuseStep 1669335 = 2504003) B2504003
theorem B7616729 : Blo 1668034 7616729 := bstep (se 2 (by rfl) ⟨2856273, by rfl⟩ : syracuseStep 7616729 = 5712547) B5712547
theorem B9640153 : Blo 1668034 9640153 := bstep (se 2 (by rfl) ⟨3615057, by rfl⟩ : syracuseStep 9640153 = 7230115) B7230115
theorem B5347549 : Blo 1668034 5347549 := bstep (se 3 (by rfl) ⟨1002665, by rfl⟩ : syracuseStep 5347549 = 2005331) B2005331
theorem B4012249 : Blo 1668034 4012249 := bstep (se 2 (by rfl) ⟨1504593, by rfl⟩ : syracuseStep 4012249 = 3009187) B3009187
theorem B2504921 : Blo 1668034 2504921 := bstep (se 2 (by rfl) ⟨939345, by rfl⟩ : syracuseStep 2504921 = 1878691) B1878691
theorem B1669355 : Blo 1668034 1669355 := bstep (se 1 (by rfl) ⟨1252016, by rfl⟩ : syracuseStep 1669355 = 2504033) B2504033
theorem B1669367 : Blo 1668034 1669367 := bstep (se 1 (by rfl) ⟨1252025, by rfl⟩ : syracuseStep 1669367 = 2504051) B2504051
theorem B1669387 : Blo 1668034 1669387 := bstep (se 1 (by rfl) ⟨1252040, by rfl⟩ : syracuseStep 1669387 = 2504081) B2504081
theorem B1669399 : Blo 1668034 1669399 := bstep (se 1 (by rfl) ⟨1252049, by rfl⟩ : syracuseStep 1669399 = 2504099) B2504099
theorem B1669419 : Blo 1668034 1669419 := bstep (se 1 (by rfl) ⟨1252064, by rfl⟩ : syracuseStep 1669419 = 2504129) B2504129
theorem B1669431 : Blo 1668034 1669431 := bstep (se 1 (by rfl) ⟨1252073, by rfl⟩ : syracuseStep 1669431 = 2504147) B2504147
theorem B4225355 : Blo 1668034 4225355 := bstep (se 1 (by rfl) ⟨3169016, by rfl⟩ : syracuseStep 4225355 = 6338033) B6338033
theorem B1669451 : Blo 1668034 1669451 := bstep (se 1 (by rfl) ⟨1252088, by rfl⟩ : syracuseStep 1669451 = 2504177) B2504177
theorem B2505035 : Blo 1668034 2505035 := bstep (se 1 (by rfl) ⟨1878776, by rfl⟩ : syracuseStep 2505035 = 3757553) B3757553
theorem B1669463 : Blo 1668034 1669463 := bstep (se 1 (by rfl) ⟨1252097, by rfl⟩ : syracuseStep 1669463 = 2504195) B2504195
theorem B2505047 : Blo 1668034 2505047 := bstep (se 1 (by rfl) ⟨1878785, by rfl⟩ : syracuseStep 2505047 = 3757571) B3757571
theorem B28522853 : Blo 1668034 28522853 := bstep (se 4 (by rfl) ⟨2674017, by rfl⟩ : syracuseStep 28522853 = 5348035) B5348035
theorem B1669483 : Blo 1668034 1669483 := bstep (se 1 (by rfl) ⟨1252112, by rfl⟩ : syracuseStep 1669483 = 2504225) B2504225
theorem B1669495 : Blo 1668034 1669495 := bstep (se 1 (by rfl) ⟨1252121, by rfl⟩ : syracuseStep 1669495 = 2504243) B2504243
theorem B1669515 : Blo 1668034 1669515 := bstep (se 1 (by rfl) ⟨1252136, by rfl⟩ : syracuseStep 1669515 = 2504273) B2504273
theorem B1669527 : Blo 1668034 1669527 := bstep (se 1 (by rfl) ⟨1252145, by rfl⟩ : syracuseStep 1669527 = 2504291) B2504291
theorem B1669547 : Blo 1668034 1669547 := bstep (se 1 (by rfl) ⟨1252160, by rfl⟩ : syracuseStep 1669547 = 2504321) B2504321
theorem B1669559 : Blo 1668034 1669559 := bstep (se 1 (by rfl) ⟨1252169, by rfl⟩ : syracuseStep 1669559 = 2504339) B2504339
theorem B5708225 : Blo 1668034 5708225 := bstep (se 2 (by rfl) ⟨2140584, by rfl⟩ : syracuseStep 5708225 = 4281169) B4281169
theorem B6339019 : Blo 1668034 6339019 := bstep (se 1 (by rfl) ⟨4754264, by rfl⟩ : syracuseStep 6339019 = 9508529) B9508529
theorem B1669579 : Blo 1668034 1669579 := bstep (se 1 (by rfl) ⟨1252184, by rfl⟩ : syracuseStep 1669579 = 2504369) B2504369
theorem B2816471 : Blo 1668034 2816471 := bstep (se 1 (by rfl) ⟨2112353, by rfl⟩ : syracuseStep 2816471 = 4224707) B4224707
theorem B1669591 : Blo 1668034 1669591 := bstep (se 1 (by rfl) ⟨1252193, by rfl⟩ : syracuseStep 1669591 = 2504387) B2504387
theorem B4282841 : Blo 1668034 4282841 := bstep (se 2 (by rfl) ⟨1606065, by rfl⟩ : syracuseStep 4282841 = 3212131) B3212131
theorem B5634521 : Blo 1668034 5634521 := bstep (se 2 (by rfl) ⟨2112945, by rfl⟩ : syracuseStep 5634521 = 4225891) B4225891
theorem B1669611 : Blo 1668034 1669611 := bstep (se 1 (by rfl) ⟨1252208, by rfl⟩ : syracuseStep 1669611 = 2504417) B2504417
theorem B1669623 : Blo 1668034 1669623 := bstep (se 1 (by rfl) ⟨1252217, by rfl⟩ : syracuseStep 1669623 = 2504435) B2504435
theorem B1669643 : Blo 1668034 1669643 := bstep (se 1 (by rfl) ⟨1252232, by rfl⟩ : syracuseStep 1669643 = 2504465) B2504465
theorem B1669655 : Blo 1668034 1669655 := bstep (se 1 (by rfl) ⟨1252241, by rfl⟩ : syracuseStep 1669655 = 2504483) B2504483
theorem B1669675 : Blo 1668034 1669675 := bstep (se 1 (by rfl) ⟨1252256, by rfl⟩ : syracuseStep 1669675 = 2504513) B2504513
theorem B1669687 : Blo 1668034 1669687 := bstep (se 1 (by rfl) ⟨1252265, by rfl⟩ : syracuseStep 1669687 = 2504531) B2504531
theorem B8452673 : Blo 1668034 8452673 := bstep (se 2 (by rfl) ⟨3169752, by rfl⟩ : syracuseStep 8452673 = 6339505) B6339505
theorem B1669707 : Blo 1668034 1669707 := bstep (se 1 (by rfl) ⟨1252280, by rfl⟩ : syracuseStep 1669707 = 2504561) B2504561
theorem B2816599 : Blo 1668034 2816599 := bstep (se 1 (by rfl) ⟨2112449, by rfl⟩ : syracuseStep 2816599 = 4224899) B4224899
theorem B1669719 : Blo 1668034 1669719 := bstep (se 1 (by rfl) ⟨1252289, by rfl⟩ : syracuseStep 1669719 = 2504579) B2504579
theorem B3168857 : Blo 1668034 3168857 := bstep (se 2 (by rfl) ⟨1188321, by rfl⟩ : syracuseStep 3168857 = 2376643) B2376643
theorem B1669739 : Blo 1668034 1669739 := bstep (se 1 (by rfl) ⟨1252304, by rfl⟩ : syracuseStep 1669739 = 2504609) B2504609
theorem B1669751 : Blo 1668034 1669751 := bstep (se 1 (by rfl) ⟨1252313, by rfl⟩ : syracuseStep 1669751 = 2504627) B2504627
theorem B1669771 : Blo 1668034 1669771 := bstep (se 1 (by rfl) ⟨1252328, by rfl⟩ : syracuseStep 1669771 = 2504657) B2504657
theorem B7608977 : Blo 1668034 7608977 := bstep (se 2 (by rfl) ⟨2853366, by rfl⟩ : syracuseStep 7608977 = 5706733) B5706733
theorem B2112151 : Blo 1668034 2112151 := bstep (se 1 (by rfl) ⟨1584113, by rfl⟩ : syracuseStep 2112151 = 3168227) B3168227
theorem B1669783 : Blo 1668034 1669783 := bstep (se 1 (by rfl) ⟨1252337, by rfl⟩ : syracuseStep 1669783 = 2504675) B2504675
theorem B1669803 : Blo 1668034 1669803 := bstep (se 1 (by rfl) ⟨1252352, by rfl⟩ : syracuseStep 1669803 = 2504705) B2504705
theorem B1669815 : Blo 1668034 1669815 := bstep (se 1 (by rfl) ⟨1252361, by rfl⟩ : syracuseStep 1669815 = 2504723) B2504723
theorem B4225729 : Blo 1668034 4225729 := bstep (se 2 (by rfl) ⟨1584648, by rfl⟩ : syracuseStep 4225729 = 3169297) B3169297
theorem B1669835 : Blo 1668034 1669835 := bstep (se 1 (by rfl) ⟨1252376, by rfl⟩ : syracuseStep 1669835 = 2504753) B2504753
theorem B1669847 : Blo 1668034 1669847 := bstep (se 1 (by rfl) ⟨1252385, by rfl⟩ : syracuseStep 1669847 = 2504771) B2504771
theorem B7125725 : Blo 1668034 7125725 := bstep (se 3 (by rfl) ⟨1336073, by rfl⟩ : syracuseStep 7125725 = 2672147) B2672147
theorem B6339293 : Blo 1668034 6339293 := bstep (se 3 (by rfl) ⟨1188617, by rfl⟩ : syracuseStep 6339293 = 2377235) B2377235
theorem B1669867 : Blo 1668034 1669867 := bstep (se 1 (by rfl) ⟨1252400, by rfl⟩ : syracuseStep 1669867 = 2504801) B2504801
theorem B1669879 : Blo 1668034 1669879 := bstep (se 1 (by rfl) ⟨1252409, by rfl⟩ : syracuseStep 1669879 = 2504819) B2504819
theorem B1669899 : Blo 1668034 1669899 := bstep (se 1 (by rfl) ⟨1252424, by rfl⟩ : syracuseStep 1669899 = 2504849) B2504849
theorem B1669911 : Blo 1668034 1669911 := bstep (se 1 (by rfl) ⟨1252433, by rfl⟩ : syracuseStep 1669911 = 2504867) B2504867
theorem B1669931 : Blo 1668034 1669931 := bstep (se 1 (by rfl) ⟨1252448, by rfl⟩ : syracuseStep 1669931 = 2504897) B2504897
theorem B1669943 : Blo 1668034 1669943 := bstep (se 1 (by rfl) ⟨1252457, by rfl⟩ : syracuseStep 1669943 = 2504915) B2504915
theorem B1669963 : Blo 1668034 1669963 := bstep (se 1 (by rfl) ⟨1252472, by rfl⟩ : syracuseStep 1669963 = 2504945) B2504945
theorem B1669975 : Blo 1668034 1669975 := bstep (se 1 (by rfl) ⟨1252481, by rfl⟩ : syracuseStep 1669975 = 2504963) B2504963
theorem B4512601 : Blo 1668034 4512601 := bstep (se 2 (by rfl) ⟨1692225, by rfl⟩ : syracuseStep 4512601 = 3384451) B3384451
theorem B1669995 : Blo 1668034 1669995 := bstep (se 1 (by rfl) ⟨1252496, by rfl⟩ : syracuseStep 1669995 = 2504993) B2504993
theorem B1670007 : Blo 1668034 1670007 := bstep (se 1 (by rfl) ⟨1252505, by rfl⟩ : syracuseStep 1670007 = 2505011) B2505011
theorem B1670027 : Blo 1668034 1670027 := bstep (se 1 (by rfl) ⟨1252520, by rfl⟩ : syracuseStep 1670027 = 2505041) B2505041
theorem B4750301 : Blo 1668034 4750301 := bstep (se 3 (by rfl) ⟨890681, by rfl⟩ : syracuseStep 4750301 = 1781363) B1781363
theorem B8445059 : Blo 1668034 8445059 := bstep (se 1 (by rfl) ⟨6333794, by rfl⟩ : syracuseStep 8445059 = 12667589) B12667589
theorem B5635223 : Blo 1668034 5635223 := bstep (se 1 (by rfl) ⟨4226417, by rfl⟩ : syracuseStep 5635223 = 8452835) B8452835
theorem B5078209 : Blo 1668034 5078209 := bstep (se 2 (by rfl) ⟨1904328, by rfl⟩ : syracuseStep 5078209 = 3808657) B3808657
theorem B2817227 : Blo 1668034 2817227 := bstep (se 1 (by rfl) ⟨2112920, by rfl⟩ : syracuseStep 2817227 = 4225841) B4225841
theorem B3611891 : Blo 1668034 3611891 := bstep (se 1 (by rfl) ⟨2708918, by rfl⟩ : syracuseStep 3611891 = 5417837) B5417837
theorem B4226327 : Blo 1668034 4226327 := bstep (se 1 (by rfl) ⟨3169745, by rfl⟩ : syracuseStep 4226327 = 6339491) B6339491
theorem B4750643 : Blo 1668034 4750643 := bstep (se 1 (by rfl) ⟨3562982, by rfl⟩ : syracuseStep 4750643 = 7125965) B7125965
theorem B13712705 : Blo 1668034 13712705 := bstep (se 2 (by rfl) ⟨5142264, by rfl⟩ : syracuseStep 13712705 = 10284529) B10284529
theorem B3169601 : Blo 1668034 3169601 := bstep (se 2 (by rfl) ⟨1188600, by rfl⟩ : syracuseStep 3169601 = 2377201) B2377201
theorem B2817355 : Blo 1668034 2817355 := bstep (se 1 (by rfl) ⟨2113016, by rfl⟩ : syracuseStep 2817355 = 4226033) B4226033
theorem B10845515 : Blo 1668034 10845515 := bstep (se 1 (by rfl) ⟨8134136, by rfl⟩ : syracuseStep 10845515 = 16268273) B16268273
theorem B6339991 : Blo 1668034 6339991 := bstep (se 1 (by rfl) ⟨4754993, by rfl⟩ : syracuseStep 6339991 = 9509987) B9509987
theorem B2817497 : Blo 1668034 2817497 := bstep (se 2 (by rfl) ⟨1056561, by rfl⟩ : syracuseStep 2817497 = 2113123) B2113123
theorem B3563033 : Blo 1668034 3563033 := bstep (se 2 (by rfl) ⟨1336137, by rfl⟩ : syracuseStep 3563033 = 2672275) B2672275
theorem B15228491 : Blo 1668034 15228491 := bstep (se 1 (by rfl) ⟨11421368, by rfl⟩ : syracuseStep 15228491 = 22842737) B22842737
theorem B3169867 : Blo 1668034 3169867 := bstep (se 1 (by rfl) ⟨2377400, by rfl⟩ : syracuseStep 3169867 = 4754801) B4754801
theorem B2817625 : Blo 1668034 2817625 := bstep (se 2 (by rfl) ⟨1056609, by rfl⟩ : syracuseStep 2817625 = 2113219) B2113219
theorem B2408087 : Blo 1668034 2408087 := bstep (se 1 (by rfl) ⟨1806065, by rfl⟩ : syracuseStep 2408087 = 3612131) B3612131
theorem B5635763 : Blo 1668034 5635763 := bstep (se 1 (by rfl) ⟨4226822, by rfl⟩ : syracuseStep 5635763 = 8453645) B8453645
theorem B5709619 : Blo 1668034 5709619 := bstep (se 1 (by rfl) ⟨4282214, by rfl⟩ : syracuseStep 5709619 = 8564429) B8564429
theorem B6012737 : Blo 1668034 6012737 := bstep (se 2 (by rfl) ⟨2254776, by rfl⟩ : syracuseStep 6012737 = 4509553) B4509553
theorem B3563443 : Blo 1668034 3563443 := bstep (se 1 (by rfl) ⟨2672582, by rfl⟩ : syracuseStep 3563443 = 5345165) B5345165
theorem B5636033 : Blo 1668034 5636033 := bstep (se 2 (by rfl) ⟨2113512, by rfl⟩ : syracuseStep 5636033 = 4227025) B4227025
theorem B3006425 : Blo 1668034 3006425 := bstep (se 2 (by rfl) ⟨1127409, by rfl⟩ : syracuseStep 3006425 = 2254819) B2254819
theorem B10698713 : Blo 1668034 10698713 := bstep (se 2 (by rfl) ⟨4012017, by rfl⟩ : syracuseStep 10698713 = 8024035) B8024035
theorem B2113543 : Blo 1668034 2113543 := bstep (se 1 (by rfl) ⟨1585157, by rfl⟩ : syracuseStep 2113543 = 3170315) B3170315
theorem B2818091 : Blo 1668034 2818091 := bstep (se 1 (by rfl) ⟨2113568, by rfl⟩ : syracuseStep 2818091 = 4227137) B4227137
theorem B4227187 : Blo 1668034 4227187 := bstep (se 1 (by rfl) ⟨3170390, by rfl⟩ : syracuseStep 4227187 = 6340781) B6340781
theorem B7127297 : Blo 1668034 7127297 := bstep (se 2 (by rfl) ⟨2672736, by rfl⟩ : syracuseStep 7127297 = 5345473) B5345473
theorem B5349665 : Blo 1668034 5349665 := bstep (se 2 (by rfl) ⟨2006124, by rfl⟩ : syracuseStep 5349665 = 4012249) B4012249
theorem B4514135 : Blo 1668034 4514135 := bstep (se 1 (by rfl) ⟨3385601, by rfl⟩ : syracuseStep 4514135 = 6771203) B6771203
theorem B8446355 : Blo 1668034 8446355 := bstep (se 1 (by rfl) ⟨6334766, by rfl⟩ : syracuseStep 8446355 = 12669533) B12669533
theorem B5349779 : Blo 1668034 5349779 := bstep (se 1 (by rfl) ⟨4012334, by rfl⟩ : syracuseStep 5349779 = 8024669) B8024669
theorem B3383851 : Blo 1668034 3383851 := bstep (se 1 (by rfl) ⟨2537888, by rfl⟩ : syracuseStep 3383851 = 5075777) B5075777
theorem B7127639 : Blo 1668034 7127639 := bstep (se 1 (by rfl) ⟨5345729, by rfl⟩ : syracuseStep 7127639 = 10691459) B10691459
theorem B2376335 : Blo 1668034 2376335 := bstep (se 1 (by rfl) ⟨1782251, by rfl⟩ : syracuseStep 2376335 = 3564503) B3564503
theorem B9503405 : Blo 1668034 9503405 := bstep (se 3 (by rfl) ⟨1781888, by rfl⟩ : syracuseStep 9503405 = 3563777) B3563777
theorem B4752215 : Blo 1668034 4752215 := bstep (se 1 (by rfl) ⟨3564161, by rfl⟩ : syracuseStep 4752215 = 7128323) B7128323
theorem B12673907 : Blo 1668034 12673907 := bstep (se 1 (by rfl) ⟨9505430, by rfl⟩ : syracuseStep 12673907 = 19010861) B19010861
theorem B6767569 : Blo 1668034 6767569 := bstep (se 2 (by rfl) ⟨2537838, by rfl⟩ : syracuseStep 6767569 = 5075677) B5075677
theorem B1876999 : Blo 1668034 1876999 := bstep (se 1 (by rfl) ⟨1407749, by rfl⟩ : syracuseStep 1876999 = 2815499) B2815499
theorem B19006487 : Blo 1668034 19006487 := bstep (se 1 (by rfl) ⟨14254865, by rfl⟩ : syracuseStep 19006487 = 28509731) B28509731
theorem B51414149 : Blo 1668034 51414149 := bstep (se 4 (by rfl) ⟨4820076, by rfl⟩ : syracuseStep 51414149 = 9640153) B9640153
theorem B3753107 : Blo 1668034 3753107 := bstep (se 1 (by rfl) ⟨2814830, by rfl⟩ : syracuseStep 3753107 = 5629661) B5629661
theorem B1877179 : Blo 1668034 1877179 := bstep (se 1 (by rfl) ⟨1407884, by rfl⟩ : syracuseStep 1877179 = 2815769) B2815769
theorem B3753161 : Blo 1668034 3753161 := bstep (se 2 (by rfl) ⟨1407435, by rfl⟩ : syracuseStep 3753161 = 2814871) B2814871
theorem B3564947 : Blo 1668034 3564947 := bstep (se 1 (by rfl) ⟨2673710, by rfl⟩ : syracuseStep 3564947 = 5347421) B5347421
theorem B4572569 : Blo 1668034 4572569 := bstep (se 2 (by rfl) ⟨1714713, by rfl⟩ : syracuseStep 4572569 = 3429427) B3429427
theorem B19015235 : Blo 1668034 19015235 := bstep (se 1 (by rfl) ⟨14261426, by rfl⟩ : syracuseStep 19015235 = 28522853) B28522853
theorem B57787981 : Blo 1668034 57787981 := bstep (se 3 (by rfl) ⟨10835246, by rfl⟩ : syracuseStep 57787981 = 21670493) B21670493
theorem B1877647 : Blo 1668034 1877647 := bstep (se 1 (by rfl) ⟨1408235, by rfl⟩ : syracuseStep 1877647 = 2816471) B2816471
theorem B54904499 : Blo 1668034 54904499 := bstep (se 1 (by rfl) ⟨41178374, by rfl⟩ : syracuseStep 54904499 = 82356749) B82356749
theorem B5072651 : Blo 1668034 5072651 := bstep (se 1 (by rfl) ⟨3804488, by rfl⟩ : syracuseStep 5072651 = 7608977) B7608977
theorem B3753863 : Blo 1668034 3753863 := bstep (se 1 (by rfl) ⟨2815397, by rfl⟩ : syracuseStep 3753863 = 5630795) B5630795
theorem B3754043 : Blo 1668034 3754043 := bstep (se 1 (by rfl) ⟨2815532, by rfl⟩ : syracuseStep 3754043 = 5631065) B5631065
theorem B5630039 : Blo 1668034 5630039 := bstep (se 1 (by rfl) ⟨4222529, by rfl⟩ : syracuseStep 5630039 = 8445059) B8445059
theorem B1878151 : Blo 1668034 1878151 := bstep (se 1 (by rfl) ⟨1408613, by rfl⟩ : syracuseStep 1878151 = 2817227) B2817227
theorem B3754169 : Blo 1668034 3754169 := bstep (se 2 (by rfl) ⟨1407813, by rfl⟩ : syracuseStep 3754169 = 2815627) B2815627
theorem B1878331 : Blo 1668034 1878331 := bstep (se 1 (by rfl) ⟨1408748, by rfl⟩ : syracuseStep 1878331 = 2817497) B2817497
theorem B8022361 : Blo 1668034 8022361 := bstep (se 2 (by rfl) ⟨3008385, by rfl⟩ : syracuseStep 8022361 = 6016771) B6016771
theorem B4753799 : Blo 1668034 4753799 := bstep (se 1 (by rfl) ⟨3565349, by rfl⟩ : syracuseStep 4753799 = 7130699) B7130699
theorem B7612825 : Blo 1668034 7612825 := bstep (se 2 (by rfl) ⟨2854809, by rfl⟩ : syracuseStep 7612825 = 5709619) B5709619
theorem B3754511 : Blo 1668034 3754511 := bstep (se 1 (by rfl) ⟨2815883, by rfl⟩ : syracuseStep 3754511 = 5631767) B5631767
theorem B3754529 : Blo 1668034 3754529 := bstep (se 2 (by rfl) ⟨1407948, by rfl⟩ : syracuseStep 3754529 = 2815897) B2815897
theorem B4008491 : Blo 1668034 4008491 := bstep (se 1 (by rfl) ⟨3006368, by rfl⟩ : syracuseStep 4008491 = 6012737) B6012737
theorem B5630525 : Blo 1668034 5630525 := bstep (se 3 (by rfl) ⟨1055723, by rfl⟩ : syracuseStep 5630525 = 2111447) B2111447
theorem B21391937 : Blo 1668034 21391937 := bstep (se 2 (by rfl) ⟨8021976, by rfl⟩ : syracuseStep 21391937 = 16043953) B16043953
theorem B3754871 : Blo 1668034 3754871 := bstep (se 1 (by rfl) ⟨2816153, by rfl⟩ : syracuseStep 3754871 = 5632307) B5632307
theorem B7130065 : Blo 1668034 7130065 := bstep (se 2 (by rfl) ⟨2673774, by rfl⟩ : syracuseStep 7130065 = 5347549) B5347549
theorem B9505795 : Blo 1668034 9505795 := bstep (se 1 (by rfl) ⟨7129346, by rfl⟩ : syracuseStep 9505795 = 14258693) B14258693
theorem B4754447 : Blo 1668034 4754447 := bstep (se 1 (by rfl) ⟨3565835, by rfl⟩ : syracuseStep 4754447 = 7131671) B7131671
theorem B3755051 : Blo 1668034 3755051 := bstep (se 1 (by rfl) ⟨2816288, by rfl⟩ : syracuseStep 3755051 = 5632577) B5632577
theorem B5868587 : Blo 1668034 5868587 := bstep (se 1 (by rfl) ⟨4401440, by rfl⟩ : syracuseStep 5868587 = 8802881) B8802881
theorem B4574323 : Blo 1668034 4574323 := bstep (se 1 (by rfl) ⟨3430742, by rfl⟩ : syracuseStep 4574323 = 6861485) B6861485
theorem B9637157 : Blo 1668034 9637157 := bstep (se 4 (by rfl) ⟨903483, by rfl⟩ : syracuseStep 9637157 = 1806967) B1806967
theorem B4009259 : Blo 1668034 4009259 := bstep (se 1 (by rfl) ⟨3006944, by rfl⟩ : syracuseStep 4009259 = 6013889) B6013889
theorem B5418299 : Blo 1668034 5418299 := bstep (se 1 (by rfl) ⟨4063724, by rfl⟩ : syracuseStep 5418299 = 8127449) B8127449
theorem B4222327 : Blo 1668034 4222327 := bstep (se 1 (by rfl) ⟨3166745, by rfl⟩ : syracuseStep 4222327 = 6333491) B6333491
theorem B6335891 : Blo 1668034 6335891 := bstep (se 1 (by rfl) ⟨4751918, by rfl⟩ : syracuseStep 6335891 = 9503837) B9503837
theorem B3755411 : Blo 1668034 3755411 := bstep (se 1 (by rfl) ⟨2816558, by rfl⟩ : syracuseStep 3755411 = 5633117) B5633117
theorem B8449433 : Blo 1668034 8449433 := bstep (se 2 (by rfl) ⟨3168537, by rfl⟩ : syracuseStep 8449433 = 6337075) B6337075
theorem B2502059 : Blo 1668034 2502059 := bstep (se 1 (by rfl) ⟨1876544, by rfl⟩ : syracuseStep 2502059 = 3753089) B3753089
theorem B2502089 : Blo 1668034 2502089 := bstep (se 2 (by rfl) ⟨938283, by rfl⟩ : syracuseStep 2502089 = 1876567) B1876567
theorem B3755465 : Blo 1668034 3755465 := bstep (se 2 (by rfl) ⟨1408299, by rfl⟩ : syracuseStep 3755465 = 2816599) B2816599
theorem B4509227 : Blo 1668034 4509227 := bstep (se 1 (by rfl) ⟨3381920, by rfl⟩ : syracuseStep 4509227 = 6763841) B6763841
theorem B2502203 : Blo 1668034 2502203 := bstep (se 1 (by rfl) ⟨1876652, by rfl⟩ : syracuseStep 2502203 = 3753305) B3753305
theorem B27053669 : Blo 1668034 27053669 := bstep (se 4 (by rfl) ⟨2536281, by rfl⟩ : syracuseStep 27053669 = 5072563) B5072563
theorem B2502263 : Blo 1668034 2502263 := bstep (se 1 (by rfl) ⟨1876697, by rfl⟩ : syracuseStep 2502263 = 3753395) B3753395
theorem B2502287 : Blo 1668034 2502287 := bstep (se 1 (by rfl) ⟨1876715, by rfl⟩ : syracuseStep 2502287 = 3753431) B3753431
theorem B2502329 : Blo 1668034 2502329 := bstep (se 2 (by rfl) ⟨938373, by rfl⟩ : syracuseStep 2502329 = 1876747) B1876747
theorem B2502407 : Blo 1668034 2502407 := bstep (se 1 (by rfl) ⟨1876805, by rfl⟩ : syracuseStep 2502407 = 3753611) B3753611
theorem B2141959 : Blo 1668034 2141959 := bstep (se 1 (by rfl) ⟨1606469, by rfl⟩ : syracuseStep 2141959 = 3212939) B3212939
theorem B8023823 : Blo 1668034 8023823 := bstep (se 1 (by rfl) ⟨6017867, by rfl⟩ : syracuseStep 8023823 = 12035735) B12035735
theorem B4222763 : Blo 1668034 4222763 := bstep (se 1 (by rfl) ⟨3167072, by rfl⟩ : syracuseStep 4222763 = 6334145) B6334145
theorem B2502443 : Blo 1668034 2502443 := bstep (se 1 (by rfl) ⟨1876832, by rfl⟩ : syracuseStep 2502443 = 3753665) B3753665
theorem B36581165 : Blo 1668034 36581165 := bstep (se 3 (by rfl) ⟨6858968, by rfl⟩ : syracuseStep 36581165 = 13717937) B13717937
theorem B2502473 : Blo 1668034 2502473 := bstep (se 2 (by rfl) ⟨938427, by rfl⟩ : syracuseStep 2502473 = 1876855) B1876855
theorem B5631929 : Blo 1668034 5631929 := bstep (se 2 (by rfl) ⟨2111973, by rfl⟩ : syracuseStep 5631929 = 4223947) B4223947
theorem B2502587 : Blo 1668034 2502587 := bstep (se 1 (by rfl) ⟨1876940, by rfl⟩ : syracuseStep 2502587 = 3753881) B3753881
theorem B2502647 : Blo 1668034 2502647 := bstep (se 1 (by rfl) ⟨1876985, by rfl⟩ : syracuseStep 2502647 = 3753971) B3753971
theorem B2502671 : Blo 1668034 2502671 := bstep (se 1 (by rfl) ⟨1877003, by rfl⟩ : syracuseStep 2502671 = 3754007) B3754007
theorem B8024093 : Blo 1668034 8024093 := bstep (se 3 (by rfl) ⟨1504517, by rfl⟩ : syracuseStep 8024093 = 3009035) B3009035
theorem B2502713 : Blo 1668034 2502713 := bstep (se 2 (by rfl) ⟨938517, by rfl⟩ : syracuseStep 2502713 = 1877035) B1877035
theorem B2502791 : Blo 1668034 2502791 := bstep (se 1 (by rfl) ⟨1877093, by rfl⟩ : syracuseStep 2502791 = 3754187) B3754187
theorem B3756167 : Blo 1668034 3756167 := bstep (se 1 (by rfl) ⟨2817125, by rfl⟩ : syracuseStep 3756167 = 5634251) B5634251
theorem B2502827 : Blo 1668034 2502827 := bstep (se 1 (by rfl) ⟨1877120, by rfl⟩ : syracuseStep 2502827 = 3754241) B3754241
theorem B19263689 : Blo 1668034 19263689 := bstep (se 2 (by rfl) ⟨7223883, by rfl⟩ : syracuseStep 19263689 = 14447767) B14447767
theorem B2502857 : Blo 1668034 2502857 := bstep (se 2 (by rfl) ⟨938571, by rfl⟩ : syracuseStep 2502857 = 1877143) B1877143
theorem B6770945 : Blo 1668034 6770945 := bstep (se 2 (by rfl) ⟨2539104, by rfl⟩ : syracuseStep 6770945 = 5078209) B5078209
theorem B3805483 : Blo 1668034 3805483 := bstep (se 1 (by rfl) ⟨2854112, by rfl⟩ : syracuseStep 3805483 = 5708225) B5708225
theorem B2502971 : Blo 1668034 2502971 := bstep (se 1 (by rfl) ⟨1877228, by rfl⟩ : syracuseStep 2502971 = 3754457) B3754457
theorem B2855227 : Blo 1668034 2855227 := bstep (se 1 (by rfl) ⟨2141420, by rfl⟩ : syracuseStep 2855227 = 4282841) B4282841
theorem B3756347 : Blo 1668034 3756347 := bstep (se 1 (by rfl) ⟨2817260, by rfl⟩ : syracuseStep 3756347 = 5634521) B5634521
theorem B2503031 : Blo 1668034 2503031 := bstep (se 1 (by rfl) ⟨1877273, by rfl⟩ : syracuseStep 2503031 = 3754547) B3754547
theorem B2503055 : Blo 1668034 2503055 := bstep (se 1 (by rfl) ⟨1877291, by rfl⟩ : syracuseStep 2503055 = 3754583) B3754583
theorem B2503097 : Blo 1668034 2503097 := bstep (se 2 (by rfl) ⟨938661, by rfl⟩ : syracuseStep 2503097 = 1877323) B1877323
theorem B3756473 : Blo 1668034 3756473 := bstep (se 2 (by rfl) ⟨1408677, by rfl⟩ : syracuseStep 3756473 = 2817355) B2817355
theorem B2503175 : Blo 1668034 2503175 := bstep (se 1 (by rfl) ⟨1877381, by rfl⟩ : syracuseStep 2503175 = 3754763) B3754763
theorem B5632523 : Blo 1668034 5632523 := bstep (se 1 (by rfl) ⟨4224392, by rfl⟩ : syracuseStep 5632523 = 8448785) B8448785
theorem B2503211 : Blo 1668034 2503211 := bstep (se 1 (by rfl) ⟨1877408, by rfl⟩ : syracuseStep 2503211 = 3754817) B3754817
theorem B2503241 : Blo 1668034 2503241 := bstep (se 2 (by rfl) ⟨938715, by rfl⟩ : syracuseStep 2503241 = 1877431) B1877431
theorem B4223603 : Blo 1668034 4223603 := bstep (se 1 (by rfl) ⟨3167702, by rfl⟩ : syracuseStep 4223603 = 6335405) B6335405
theorem B5632631 : Blo 1668034 5632631 := bstep (se 1 (by rfl) ⟨4224473, by rfl⟩ : syracuseStep 5632631 = 8448947) B8448947
theorem B9024119 : Blo 1668034 9024119 := bstep (se 1 (by rfl) ⟨6768089, by rfl⟩ : syracuseStep 9024119 = 13536179) B13536179
theorem B4223623 : Blo 1668034 4223623 := bstep (se 1 (by rfl) ⟨3167717, by rfl⟩ : syracuseStep 4223623 = 6335435) B6335435
theorem B3166867 : Blo 1668034 3166867 := bstep (se 1 (by rfl) ⟨2375150, by rfl⟩ : syracuseStep 3166867 = 4750301) B4750301
theorem B4010681 : Blo 1668034 4010681 := bstep (se 2 (by rfl) ⟨1504005, by rfl⟩ : syracuseStep 4010681 = 3008011) B3008011
theorem B2503355 : Blo 1668034 2503355 := bstep (se 1 (by rfl) ⟨1877516, by rfl⟩ : syracuseStep 2503355 = 3755033) B3755033
theorem B10146541 : Blo 1668034 10146541 := bstep (se 3 (by rfl) ⟨1902476, by rfl⟩ : syracuseStep 10146541 = 3804953) B3804953
theorem B2503415 : Blo 1668034 2503415 := bstep (se 1 (by rfl) ⟨1877561, by rfl⟩ : syracuseStep 2503415 = 3755123) B3755123
theorem B19002113 : Blo 1668034 19002113 := bstep (se 2 (by rfl) ⟨7125792, by rfl⟩ : syracuseStep 19002113 = 14251585) B14251585
theorem B2503439 : Blo 1668034 2503439 := bstep (se 1 (by rfl) ⟨1877579, by rfl⟩ : syracuseStep 2503439 = 3755159) B3755159
theorem B3756815 : Blo 1668034 3756815 := bstep (se 1 (by rfl) ⟨2817611, by rfl⟩ : syracuseStep 3756815 = 5635223) B5635223
theorem B3756833 : Blo 1668034 3756833 := bstep (se 2 (by rfl) ⟨1408812, by rfl⟩ : syracuseStep 3756833 = 2817625) B2817625
theorem B2503481 : Blo 1668034 2503481 := bstep (se 2 (by rfl) ⟨938805, by rfl⟩ : syracuseStep 2503481 = 1877611) B1877611
theorem B34714457 : Blo 1668034 34714457 := bstep (se 2 (by rfl) ⟨13017921, by rfl⟩ : syracuseStep 34714457 = 26035843) B26035843
theorem B25703257 : Blo 1668034 25703257 := bstep (se 2 (by rfl) ⟨9638721, by rfl⟩ : syracuseStep 25703257 = 19277443) B19277443
theorem B3167095 : Blo 1668034 3167095 := bstep (se 1 (by rfl) ⟨2375321, by rfl⟩ : syracuseStep 3167095 = 4750643) B4750643
theorem B2503559 : Blo 1668034 2503559 := bstep (se 1 (by rfl) ⟨1877669, by rfl⟩ : syracuseStep 2503559 = 3755339) B3755339
theorem B7230343 : Blo 1668034 7230343 := bstep (se 1 (by rfl) ⟨5422757, by rfl⟩ : syracuseStep 7230343 = 10845515) B10845515
theorem B4223897 : Blo 1668034 4223897 := bstep (se 2 (by rfl) ⟨1583961, by rfl⟩ : syracuseStep 4223897 = 3167923) B3167923
theorem B2503595 : Blo 1668034 2503595 := bstep (se 1 (by rfl) ⟨1877696, by rfl⟩ : syracuseStep 2503595 = 3755393) B3755393
theorem B2814905 : Blo 1668034 2814905 := bstep (se 2 (by rfl) ⟨1055589, by rfl⟩ : syracuseStep 2814905 = 2111179) B2111179
theorem B2503625 : Blo 1668034 2503625 := bstep (se 2 (by rfl) ⟨938859, by rfl⟩ : syracuseStep 2503625 = 1877719) B1877719
theorem B1668103 : Blo 1668034 1668103 := bstep (se 1 (by rfl) ⟨1251077, by rfl⟩ : syracuseStep 1668103 = 2502155) B2502155
theorem B6337547 : Blo 1668034 6337547 := bstep (se 1 (by rfl) ⟨4753160, by rfl⟩ : syracuseStep 6337547 = 9506321) B9506321
theorem B1668111 : Blo 1668034 1668111 := bstep (se 1 (by rfl) ⟨1251083, by rfl⟩ : syracuseStep 1668111 = 2502167) B2502167
theorem B1668155 : Blo 1668034 1668155 := bstep (se 1 (by rfl) ⟨1251116, by rfl⟩ : syracuseStep 1668155 = 2502233) B2502233
theorem B4224059 : Blo 1668034 4224059 := bstep (se 1 (by rfl) ⟨3168044, by rfl⟩ : syracuseStep 4224059 = 6336089) B6336089
theorem B2503739 : Blo 1668034 2503739 := bstep (se 1 (by rfl) ⟨1877804, by rfl⟩ : syracuseStep 2503739 = 3755609) B3755609
theorem B4011095 : Blo 1668034 4011095 := bstep (se 1 (by rfl) ⟨3008321, by rfl⟩ : syracuseStep 4011095 = 6016643) B6016643
theorem B2503799 : Blo 1668034 2503799 := bstep (se 1 (by rfl) ⟨1877849, by rfl⟩ : syracuseStep 2503799 = 3755699) B3755699
theorem B3757175 : Blo 1668034 3757175 := bstep (se 1 (by rfl) ⟨2817881, by rfl⟩ : syracuseStep 3757175 = 5635763) B5635763
theorem B1668231 : Blo 1668034 1668231 := bstep (se 1 (by rfl) ⟨1251173, by rfl⟩ : syracuseStep 1668231 = 2502347) B2502347
theorem B1668239 : Blo 1668034 1668239 := bstep (se 1 (by rfl) ⟨1251179, by rfl⟩ : syracuseStep 1668239 = 2502359) B2502359
theorem B2503823 : Blo 1668034 2503823 := bstep (se 1 (by rfl) ⟨1877867, by rfl⟩ : syracuseStep 2503823 = 3755735) B3755735
theorem B2503865 : Blo 1668034 2503865 := bstep (se 2 (by rfl) ⟨938949, by rfl⟩ : syracuseStep 2503865 = 1877899) B1877899
theorem B1668283 : Blo 1668034 1668283 := bstep (se 1 (by rfl) ⟨1251212, by rfl⟩ : syracuseStep 1668283 = 2502425) B2502425
theorem B5633225 : Blo 1668034 5633225 := bstep (se 2 (by rfl) ⟨2112459, by rfl⟩ : syracuseStep 5633225 = 4224919) B4224919
theorem B1668359 : Blo 1668034 1668359 := bstep (se 1 (by rfl) ⟨1251269, by rfl⟩ : syracuseStep 1668359 = 2502539) B2502539
theorem B2503943 : Blo 1668034 2503943 := bstep (se 1 (by rfl) ⟨1877957, by rfl⟩ : syracuseStep 2503943 = 3755915) B3755915
theorem B1668367 : Blo 1668034 1668367 := bstep (se 1 (by rfl) ⟨1251275, by rfl⟩ : syracuseStep 1668367 = 2502551) B2502551
theorem B4224271 : Blo 1668034 4224271 := bstep (se 1 (by rfl) ⟨3168203, by rfl⟩ : syracuseStep 4224271 = 6336407) B6336407
theorem B2503979 : Blo 1668034 2503979 := bstep (se 1 (by rfl) ⟨1877984, by rfl⟩ : syracuseStep 2503979 = 3755969) B3755969
theorem B3757355 : Blo 1668034 3757355 := bstep (se 1 (by rfl) ⟨2818016, by rfl⟩ : syracuseStep 3757355 = 5636033) B5636033
theorem B2004283 : Blo 1668034 2004283 := bstep (se 1 (by rfl) ⟨1503212, by rfl⟩ : syracuseStep 2004283 = 3006425) B3006425
theorem B1668411 : Blo 1668034 1668411 := bstep (se 1 (by rfl) ⟨1251308, by rfl⟩ : syracuseStep 1668411 = 2502617) B2502617
theorem B7132475 : Blo 1668034 7132475 := bstep (se 1 (by rfl) ⟨5349356, by rfl⟩ : syracuseStep 7132475 = 10698713) B10698713
theorem B2504009 : Blo 1668034 2504009 := bstep (se 2 (by rfl) ⟨939003, by rfl⟩ : syracuseStep 2504009 = 1878007) B1878007
theorem B9508211 : Blo 1668034 9508211 := bstep (se 1 (by rfl) ⟨7131158, by rfl⟩ : syracuseStep 9508211 = 14262317) B14262317
theorem B1668487 : Blo 1668034 1668487 := bstep (se 1 (by rfl) ⟨1251365, by rfl⟩ : syracuseStep 1668487 = 2502731) B2502731
theorem B1668495 : Blo 1668034 1668495 := bstep (se 1 (by rfl) ⟨1251371, by rfl⟩ : syracuseStep 1668495 = 2502743) B2502743
theorem B17126801 : Blo 1668034 17126801 := bstep (se 2 (by rfl) ⟨6422550, by rfl⟩ : syracuseStep 17126801 = 12845101) B12845101
theorem B4281785 : Blo 1668034 4281785 := bstep (se 2 (by rfl) ⟨1605669, by rfl⟩ : syracuseStep 4281785 = 3211339) B3211339
theorem B1668539 : Blo 1668034 1668539 := bstep (se 1 (by rfl) ⟨1251404, by rfl⟩ : syracuseStep 1668539 = 2502809) B2502809
theorem B2504123 : Blo 1668034 2504123 := bstep (se 1 (by rfl) ⟨1878092, by rfl⟩ : syracuseStep 2504123 = 3756185) B3756185
theorem B2504183 : Blo 1668034 2504183 := bstep (se 1 (by rfl) ⟨1878137, by rfl⟩ : syracuseStep 2504183 = 3756275) B3756275
theorem B1668615 : Blo 1668034 1668615 := bstep (se 1 (by rfl) ⟨1251461, by rfl⟩ : syracuseStep 1668615 = 2502923) B2502923
theorem B1668623 : Blo 1668034 1668623 := bstep (se 1 (by rfl) ⟨1251467, by rfl⟩ : syracuseStep 1668623 = 2502935) B2502935
theorem B2504207 : Blo 1668034 2504207 := bstep (se 1 (by rfl) ⟨1878155, by rfl⟩ : syracuseStep 2504207 = 3756311) B3756311
theorem B4224545 : Blo 1668034 4224545 := bstep (se 2 (by rfl) ⟨1584204, by rfl⟩ : syracuseStep 4224545 = 3168409) B3168409
theorem B2504249 : Blo 1668034 2504249 := bstep (se 2 (by rfl) ⟨939093, by rfl⟩ : syracuseStep 2504249 = 1878187) B1878187
theorem B1668667 : Blo 1668034 1668667 := bstep (se 1 (by rfl) ⟨1251500, by rfl⟩ : syracuseStep 1668667 = 2503001) B2503001
theorem B2815607 : Blo 1668034 2815607 := bstep (se 1 (by rfl) ⟨2111705, by rfl⟩ : syracuseStep 2815607 = 4223411) B4223411
theorem B5346935 : Blo 1668034 5346935 := bstep (se 1 (by rfl) ⟨4010201, by rfl⟩ : syracuseStep 5346935 = 8020403) B8020403
theorem B1668743 : Blo 1668034 1668743 := bstep (se 1 (by rfl) ⟨1251557, by rfl⟩ : syracuseStep 1668743 = 2503115) B2503115
theorem B2504327 : Blo 1668034 2504327 := bstep (se 1 (by rfl) ⟨1878245, by rfl⟩ : syracuseStep 2504327 = 3756491) B3756491
theorem B1668751 : Blo 1668034 1668751 := bstep (se 1 (by rfl) ⟨1251563, by rfl⟩ : syracuseStep 1668751 = 2503127) B2503127
theorem B2504363 : Blo 1668034 2504363 := bstep (se 1 (by rfl) ⟨1878272, by rfl⟩ : syracuseStep 2504363 = 3756545) B3756545
theorem B1668795 : Blo 1668034 1668795 := bstep (se 1 (by rfl) ⟨1251596, by rfl⟩ : syracuseStep 1668795 = 2503193) B2503193
theorem B2504393 : Blo 1668034 2504393 := bstep (se 2 (by rfl) ⟨939147, by rfl⟩ : syracuseStep 2504393 = 1878295) B1878295
theorem B6018761 : Blo 1668034 6018761 := bstep (se 2 (by rfl) ⟨2257035, by rfl⟩ : syracuseStep 6018761 = 4514071) B4514071
theorem B1668871 : Blo 1668034 1668871 := bstep (se 1 (by rfl) ⟨1251653, by rfl⟩ : syracuseStep 1668871 = 2503307) B2503307
theorem B1668879 : Blo 1668034 1668879 := bstep (se 1 (by rfl) ⟨1251659, by rfl⟩ : syracuseStep 1668879 = 2503319) B2503319
theorem B2111275 : Blo 1668034 2111275 := bstep (se 1 (by rfl) ⟨1583456, by rfl⟩ : syracuseStep 2111275 = 3166913) B3166913
theorem B1668923 : Blo 1668034 1668923 := bstep (se 1 (by rfl) ⟨1251692, by rfl⟩ : syracuseStep 1668923 = 2503385) B2503385
theorem B2504507 : Blo 1668034 2504507 := bstep (se 1 (by rfl) ⟨1878380, by rfl⟩ : syracuseStep 2504507 = 3756761) B3756761
theorem B19019609 : Blo 1668034 19019609 := bstep (se 2 (by rfl) ⟨7132353, by rfl⟩ : syracuseStep 19019609 = 14264707) B14264707
theorem B2504567 : Blo 1668034 2504567 := bstep (se 1 (by rfl) ⟨1878425, by rfl⟩ : syracuseStep 2504567 = 3756851) B3756851
theorem B1668999 : Blo 1668034 1668999 := bstep (se 1 (by rfl) ⟨1251749, by rfl⟩ : syracuseStep 1668999 = 2503499) B2503499
theorem B5633927 : Blo 1668034 5633927 := bstep (se 1 (by rfl) ⟨4225445, by rfl⟩ : syracuseStep 5633927 = 8450891) B8450891
theorem B1669007 : Blo 1668034 1669007 := bstep (se 1 (by rfl) ⟨1251755, by rfl⟩ : syracuseStep 1669007 = 2503511) B2503511
theorem B2504591 : Blo 1668034 2504591 := bstep (se 1 (by rfl) ⟨1878443, by rfl⟩ : syracuseStep 2504591 = 3756887) B3756887
theorem B8452025 : Blo 1668034 8452025 := bstep (se 2 (by rfl) ⟨3169509, by rfl⟩ : syracuseStep 8452025 = 6339019) B6339019
theorem B2504633 : Blo 1668034 2504633 := bstep (se 2 (by rfl) ⟨939237, by rfl⟩ : syracuseStep 2504633 = 1878475) B1878475
theorem B1669051 : Blo 1668034 1669051 := bstep (se 1 (by rfl) ⟨1251788, by rfl⟩ : syracuseStep 1669051 = 2503577) B2503577
theorem B9631709 : Blo 1668034 9631709 := bstep (se 3 (by rfl) ⟨1805945, by rfl⟩ : syracuseStep 9631709 = 3611891) B3611891
theorem B1669127 : Blo 1668034 1669127 := bstep (se 1 (by rfl) ⟨1251845, by rfl⟩ : syracuseStep 1669127 = 2503691) B2503691
theorem B2504711 : Blo 1668034 2504711 := bstep (se 1 (by rfl) ⟨1878533, by rfl⟩ : syracuseStep 2504711 = 3757067) B3757067
theorem B2111503 : Blo 1668034 2111503 := bstep (se 1 (by rfl) ⟨1583627, by rfl⟩ : syracuseStep 2111503 = 3167255) B3167255
theorem B1669135 : Blo 1668034 1669135 := bstep (se 1 (by rfl) ⟨1251851, by rfl⟩ : syracuseStep 1669135 = 2503703) B2503703
theorem B2504747 : Blo 1668034 2504747 := bstep (se 1 (by rfl) ⟨1878560, by rfl⟩ : syracuseStep 2504747 = 3757121) B3757121
theorem B2816059 : Blo 1668034 2816059 := bstep (se 1 (by rfl) ⟨2112044, by rfl⟩ : syracuseStep 2816059 = 4224089) B4224089
theorem B1669179 : Blo 1668034 1669179 := bstep (se 1 (by rfl) ⟨1251884, by rfl⟩ : syracuseStep 1669179 = 2503769) B2503769
theorem B2504777 : Blo 1668034 2504777 := bstep (se 2 (by rfl) ⟨939291, by rfl⟩ : syracuseStep 2504777 = 1878583) B1878583
theorem B162437237 : Blo 1668034 162437237 := bstep (se 5 (by rfl) ⟨7614245, by rfl⟩ : syracuseStep 162437237 = 15228491) B15228491
theorem B5142647 : Blo 1668034 5142647 := bstep (se 1 (by rfl) ⟨3856985, by rfl⟩ : syracuseStep 5142647 = 7713971) B7713971
theorem B1669255 : Blo 1668034 1669255 := bstep (se 1 (by rfl) ⟨1251941, by rfl⟩ : syracuseStep 1669255 = 2503883) B2503883
theorem B1669263 : Blo 1668034 1669263 := bstep (se 1 (by rfl) ⟨1251947, by rfl⟩ : syracuseStep 1669263 = 2503895) B2503895
theorem B1669307 : Blo 1668034 1669307 := bstep (se 1 (by rfl) ⟨1251980, by rfl⟩ : syracuseStep 1669307 = 2503961) B2503961
theorem B2504891 : Blo 1668034 2504891 := bstep (se 1 (by rfl) ⟨1878668, by rfl⟩ : syracuseStep 2504891 = 3757337) B3757337
theorem B2816201 : Blo 1668034 2816201 := bstep (se 2 (by rfl) ⟨1056075, by rfl⟩ : syracuseStep 2816201 = 2112151) B2112151
theorem B2504951 : Blo 1668034 2504951 := bstep (se 1 (by rfl) ⟨1878713, by rfl⟩ : syracuseStep 2504951 = 3757427) B3757427
theorem B5634305 : Blo 1668034 5634305 := bstep (se 2 (by rfl) ⟨2112864, by rfl⟩ : syracuseStep 5634305 = 4225729) B4225729
theorem B1669383 : Blo 1668034 1669383 := bstep (se 1 (by rfl) ⟨1252037, by rfl⟩ : syracuseStep 1669383 = 2504075) B2504075
theorem B1669391 : Blo 1668034 1669391 := bstep (se 1 (by rfl) ⟨1252043, by rfl⟩ : syracuseStep 1669391 = 2504087) B2504087
theorem B2504975 : Blo 1668034 2504975 := bstep (se 1 (by rfl) ⟨1878731, by rfl⟩ : syracuseStep 2504975 = 3757463) B3757463
theorem B2505017 : Blo 1668034 2505017 := bstep (se 2 (by rfl) ⟨939381, by rfl⟩ : syracuseStep 2505017 = 1878763) B1878763
theorem B1669435 : Blo 1668034 1669435 := bstep (se 1 (by rfl) ⟨1252076, by rfl⟩ : syracuseStep 1669435 = 2504153) B2504153
theorem B7125383 : Blo 1668034 7125383 := bstep (se 1 (by rfl) ⟨5344037, by rfl⟩ : syracuseStep 7125383 = 10688075) B10688075
theorem B1669511 : Blo 1668034 1669511 := bstep (se 1 (by rfl) ⟨1252133, by rfl⟩ : syracuseStep 1669511 = 2504267) B2504267
theorem B1669519 : Blo 1668034 1669519 := bstep (se 1 (by rfl) ⟨1252139, by rfl⟩ : syracuseStep 1669519 = 2504279) B2504279
theorem B3168659 : Blo 1668034 3168659 := bstep (se 1 (by rfl) ⟨2376494, by rfl⟩ : syracuseStep 3168659 = 4752989) B4752989
theorem B1669563 : Blo 1668034 1669563 := bstep (se 1 (by rfl) ⟨1252172, by rfl⟩ : syracuseStep 1669563 = 2504345) B2504345
theorem B3168713 : Blo 1668034 3168713 := bstep (se 2 (by rfl) ⟨1188267, by rfl⟩ : syracuseStep 3168713 = 2376535) B2376535
theorem B1669639 : Blo 1668034 1669639 := bstep (se 1 (by rfl) ⟨1252229, by rfl⟩ : syracuseStep 1669639 = 2504459) B2504459
theorem B4225547 : Blo 1668034 4225547 := bstep (se 1 (by rfl) ⟨3169160, by rfl⟩ : syracuseStep 4225547 = 6338321) B6338321
theorem B1669647 : Blo 1668034 1669647 := bstep (se 1 (by rfl) ⟨1252235, by rfl⟩ : syracuseStep 1669647 = 2504471) B2504471
theorem B3168811 : Blo 1668034 3168811 := bstep (se 1 (by rfl) ⟨2376608, by rfl⟩ : syracuseStep 3168811 = 4753217) B4753217
theorem B5347883 : Blo 1668034 5347883 := bstep (se 1 (by rfl) ⟨4010912, by rfl⟩ : syracuseStep 5347883 = 8021825) B8021825
theorem B1669691 : Blo 1668034 1669691 := bstep (se 1 (by rfl) ⟨1252268, by rfl⟩ : syracuseStep 1669691 = 2504537) B2504537
theorem B1669767 : Blo 1668034 1669767 := bstep (se 1 (by rfl) ⟨1252325, by rfl⟩ : syracuseStep 1669767 = 2504651) B2504651
theorem B1669775 : Blo 1668034 1669775 := bstep (se 1 (by rfl) ⟨1252331, by rfl⟩ : syracuseStep 1669775 = 2504663) B2504663
theorem B1669819 : Blo 1668034 1669819 := bstep (se 1 (by rfl) ⟨1252364, by rfl⟩ : syracuseStep 1669819 = 2504729) B2504729
theorem B9501421 : Blo 1668034 9501421 := bstep (se 3 (by rfl) ⟨1781516, by rfl⟩ : syracuseStep 9501421 = 3563033) B3563033
theorem B2112247 : Blo 1668034 2112247 := bstep (se 1 (by rfl) ⟨1584185, by rfl⟩ : syracuseStep 2112247 = 3168371) B3168371
theorem B1669895 : Blo 1668034 1669895 := bstep (se 1 (by rfl) ⟨1252421, by rfl⟩ : syracuseStep 1669895 = 2504843) B2504843
theorem B3169039 : Blo 1668034 3169039 := bstep (se 1 (by rfl) ⟨2376779, by rfl⟩ : syracuseStep 3169039 = 4753559) B4753559
theorem B1669903 : Blo 1668034 1669903 := bstep (se 1 (by rfl) ⟨1252427, by rfl⟩ : syracuseStep 1669903 = 2504855) B2504855
theorem B9509669 : Blo 1668034 9509669 := bstep (se 4 (by rfl) ⟨891531, by rfl⟩ : syracuseStep 9509669 = 1783063) B1783063
theorem B5077819 : Blo 1668034 5077819 := bstep (se 1 (by rfl) ⟨3808364, by rfl⟩ : syracuseStep 5077819 = 7616729) B7616729
theorem B1669947 : Blo 1668034 1669947 := bstep (se 1 (by rfl) ⟨1252460, by rfl⟩ : syracuseStep 1669947 = 2504921) B2504921
theorem B2005879 : Blo 1668034 2005879 := bstep (se 1 (by rfl) ⟨1504409, by rfl⟩ : syracuseStep 2005879 = 3008819) B3008819
theorem B2816903 : Blo 1668034 2816903 := bstep (se 1 (by rfl) ⟨2112677, by rfl⟩ : syracuseStep 2816903 = 4225355) B4225355
theorem B1670023 : Blo 1668034 1670023 := bstep (se 1 (by rfl) ⟨1252517, by rfl⟩ : syracuseStep 1670023 = 2505035) B2505035
theorem B1670031 : Blo 1668034 1670031 := bstep (se 1 (by rfl) ⟨1252523, by rfl⟩ : syracuseStep 1670031 = 2505047) B2505047
theorem B9018391 : Blo 1668034 9018391 := bstep (se 1 (by rfl) ⟨6763793, by rfl⟩ : syracuseStep 9018391 = 13527587) B13527587
theorem B5635115 : Blo 1668034 5635115 := bstep (se 1 (by rfl) ⟨4226336, by rfl⟩ : syracuseStep 5635115 = 8452673) B8452673
theorem B3562555 : Blo 1668034 3562555 := bstep (se 1 (by rfl) ⟨2671916, by rfl⟩ : syracuseStep 3562555 = 5343833) B5343833
theorem B2112571 : Blo 1668034 2112571 := bstep (se 1 (by rfl) ⟨1584428, by rfl⟩ : syracuseStep 2112571 = 3168857) B3168857
theorem B6421565 : Blo 1668034 6421565 := bstep (se 3 (by rfl) ⟨1204043, by rfl⟩ : syracuseStep 6421565 = 2408087) B2408087
theorem B4512829 : Blo 1668034 4512829 := bstep (se 3 (by rfl) ⟨846155, by rfl⟩ : syracuseStep 4512829 = 1692311) B1692311
theorem B24067205 : Blo 1668034 24067205 := bstep (se 4 (by rfl) ⟨2256300, by rfl⟩ : syracuseStep 24067205 = 4512601) B4512601
theorem B4750483 : Blo 1668034 4750483 := bstep (se 1 (by rfl) ⟨3562862, by rfl⟩ : syracuseStep 4750483 = 7125725) B7125725
theorem B4226195 : Blo 1668034 4226195 := bstep (se 1 (by rfl) ⟨3169646, by rfl⟩ : syracuseStep 4226195 = 6339293) B6339293
theorem B3808403 : Blo 1668034 3808403 := bstep (se 1 (by rfl) ⟨2856302, by rfl⟩ : syracuseStep 3808403 = 5712605) B5712605
theorem B8453321 : Blo 1668034 8453321 := bstep (se 2 (by rfl) ⟨3169995, by rfl⟩ : syracuseStep 8453321 = 6339991) B6339991
theorem B4226489 : Blo 1668034 4226489 := bstep (se 2 (by rfl) ⟨1584933, by rfl⟩ : syracuseStep 4226489 = 3169867) B3169867
theorem B2817551 : Blo 1668034 2817551 := bstep (se 1 (by rfl) ⟨2113163, by rfl⟩ : syracuseStep 2817551 = 4226327) B4226327
theorem B8019479 : Blo 1668034 8019479 := bstep (se 1 (by rfl) ⟨6014609, by rfl⟩ : syracuseStep 8019479 = 12029219) B12029219
theorem B9141803 : Blo 1668034 9141803 := bstep (se 1 (by rfl) ⟨6856352, by rfl⟩ : syracuseStep 9141803 = 13712705) B13712705
theorem B2113067 : Blo 1668034 2113067 := bstep (se 1 (by rfl) ⟨1584800, by rfl⟩ : syracuseStep 2113067 = 3169601) B3169601
theorem B9510443 : Blo 1668034 9510443 := bstep (se 1 (by rfl) ⟨7132832, by rfl⟩ : syracuseStep 9510443 = 14265665) B14265665
theorem B19005029 : Blo 1668034 19005029 := bstep (se 4 (by rfl) ⟨1781721, by rfl⟩ : syracuseStep 19005029 = 3563443) B3563443
theorem B3612617 : Blo 1668034 3612617 := bstep (se 2 (by rfl) ⟨1354731, by rfl⟩ : syracuseStep 3612617 = 2709463) B2709463
theorem B2818057 : Blo 1668034 2818057 := bstep (se 2 (by rfl) ⟨1056771, by rfl⟩ : syracuseStep 2818057 = 2113543) B2113543
theorem B5349395 : Blo 1668034 5349395 := bstep (se 1 (by rfl) ⟨4012046, by rfl⟩ : syracuseStep 5349395 = 8024093) B8024093
theorem B5636249 : Blo 1668034 5636249 := bstep (se 2 (by rfl) ⟨2113593, by rfl⟩ : syracuseStep 5636249 = 4227187) B4227187
theorem B4751531 : Blo 1668034 4751531 := bstep (se 1 (by rfl) ⟨3563648, by rfl⟩ : syracuseStep 4751531 = 7127297) B7127297
theorem B4513963 : Blo 1668034 4513963 := bstep (se 1 (by rfl) ⟨3385472, by rfl⟩ : syracuseStep 4513963 = 6770945) B6770945
theorem B13713725 : Blo 1668034 13713725 := bstep (se 3 (by rfl) ⟨2571323, by rfl⟩ : syracuseStep 13713725 = 5142647) B5142647
theorem B4751759 : Blo 1668034 4751759 := bstep (se 1 (by rfl) ⟨3563819, by rfl⟩ : syracuseStep 4751759 = 7127639) B7127639
theorem B10150433 : Blo 1668034 10150433 := bstep (se 2 (by rfl) ⟨3806412, by rfl⟩ : syracuseStep 10150433 = 7612825) B7612825
theorem B23142971 : Blo 1668034 23142971 := bstep (se 1 (by rfl) ⟨17357228, by rfl⟩ : syracuseStep 23142971 = 34714457) B34714457
theorem B24396389 : Blo 1668034 24396389 := bstep (se 4 (by rfl) ⟨2287161, by rfl⟩ : syracuseStep 24396389 = 4574323) B4574323
theorem B1876603 : Blo 1668034 1876603 := bstep (se 1 (by rfl) ⟨1407452, by rfl⟩ : syracuseStep 1876603 = 2814905) B2814905
theorem B2376631 : Blo 1668034 2376631 := bstep (se 1 (by rfl) ⟨1782473, by rfl⟩ : syracuseStep 2376631 = 3564947) B3564947
theorem B1877071 : Blo 1668034 1877071 := bstep (se 1 (by rfl) ⟨1407803, by rfl⟩ : syracuseStep 1877071 = 2815607) B2815607
theorem B3564623 : Blo 1668034 3564623 := bstep (se 1 (by rfl) ⟨2673467, by rfl⟩ : syracuseStep 3564623 = 5346935) B5346935
theorem B36602999 : Blo 1668034 36602999 := bstep (se 1 (by rfl) ⟨27452249, by rfl⟩ : syracuseStep 36602999 = 54904499) B54904499
theorem B12674393 : Blo 1668034 12674393 := bstep (se 2 (by rfl) ⟨4752897, by rfl⟩ : syracuseStep 12674393 = 9505795) B9505795
theorem B3753359 : Blo 1668034 3753359 := bstep (se 1 (by rfl) ⟨2815019, by rfl⟩ : syracuseStep 3753359 = 5630039) B5630039
theorem B108291491 : Blo 1668034 108291491 := bstep (se 1 (by rfl) ⟨81218618, by rfl⟩ : syracuseStep 108291491 = 162437237) B162437237
theorem B1877467 : Blo 1668034 1877467 := bstep (se 1 (by rfl) ⟨1408100, by rfl⟩ : syracuseStep 1877467 = 2816201) B2816201
theorem B6333977 : Blo 1668034 6333977 := bstep (se 2 (by rfl) ⟨2375241, by rfl⟩ : syracuseStep 6333977 = 4750483) B4750483
theorem B2672327 : Blo 1668034 2672327 := bstep (se 1 (by rfl) ⟨2004245, by rfl⟩ : syracuseStep 2672327 = 4008491) B4008491
theorem B3565255 : Blo 1668034 3565255 := bstep (se 1 (by rfl) ⟨2673941, by rfl⟩ : syracuseStep 3565255 = 5347883) B5347883
theorem B3753683 : Blo 1668034 3753683 := bstep (se 1 (by rfl) ⟨2815262, by rfl⟩ : syracuseStep 3753683 = 5630525) B5630525
theorem B5629769 : Blo 1668034 5629769 := bstep (se 2 (by rfl) ⟨2111163, by rfl⟩ : syracuseStep 5629769 = 4222327) B4222327
theorem B1877935 : Blo 1668034 1877935 := bstep (se 1 (by rfl) ⟨1408451, by rfl⟩ : syracuseStep 1877935 = 2816903) B2816903
theorem B6424771 : Blo 1668034 6424771 := bstep (se 1 (by rfl) ⟨4818578, by rfl⟩ : syracuseStep 6424771 = 9637157) B9637157
theorem B2672839 : Blo 1668034 2672839 := bstep (se 1 (by rfl) ⟨2004629, by rfl⟩ : syracuseStep 2672839 = 4009259) B4009259
theorem B1878367 : Blo 1668034 1878367 := bstep (se 1 (by rfl) ⟨1408775, by rfl⟩ : syracuseStep 1878367 = 2817551) B2817551
theorem B3754619 : Blo 1668034 3754619 := bstep (se 1 (by rfl) ⟨2815964, by rfl⟩ : syracuseStep 3754619 = 5631929) B5631929
theorem B1878727 : Blo 1668034 1878727 := bstep (se 1 (by rfl) ⟨1409045, by rfl⟩ : syracuseStep 1878727 = 2818091) B2818091
theorem B3754745 : Blo 1668034 3754745 := bstep (se 2 (by rfl) ⟨1408029, by rfl⟩ : syracuseStep 3754745 = 2816059) B2816059
theorem B17124173 : Blo 1668034 17124173 := bstep (se 3 (by rfl) ⟨3210782, by rfl⟩ : syracuseStep 17124173 = 6421565) B6421565
theorem B3566443 : Blo 1668034 3566443 := bstep (se 1 (by rfl) ⟨2674832, by rfl⟩ : syracuseStep 3566443 = 5349665) B5349665
theorem B5630903 : Blo 1668034 5630903 := bstep (se 1 (by rfl) ⟨4223177, by rfl⟩ : syracuseStep 5630903 = 8446355) B8446355
theorem B3566519 : Blo 1668034 3566519 := bstep (se 1 (by rfl) ⟨2674889, by rfl⟩ : syracuseStep 3566519 = 5349779) B5349779
theorem B3755015 : Blo 1668034 3755015 := bstep (se 1 (by rfl) ⟨2816261, by rfl⟩ : syracuseStep 3755015 = 5632523) B5632523
theorem B137104397 : Blo 1668034 137104397 := bstep (se 3 (by rfl) ⟨25707074, by rfl⟩ : syracuseStep 137104397 = 51414149) B51414149
theorem B5073977 : Blo 1668034 5073977 := bstep (se 2 (by rfl) ⟨1902741, by rfl⟩ : syracuseStep 5073977 = 3805483) B3805483
theorem B308202565 : Blo 1668034 308202565 := bstep (se 4 (by rfl) ⟨28893990, by rfl⟩ : syracuseStep 308202565 = 57787981) B57787981
theorem B3755087 : Blo 1668034 3755087 := bstep (se 1 (by rfl) ⟨2816315, by rfl⟩ : syracuseStep 3755087 = 5632631) B5632631
theorem B6016079 : Blo 1668034 6016079 := bstep (se 1 (by rfl) ⟨4512059, by rfl⟩ : syracuseStep 6016079 = 9024119) B9024119
theorem B6335603 : Blo 1668034 6335603 := bstep (se 1 (by rfl) ⟨4751702, by rfl⟩ : syracuseStep 6335603 = 9503405) B9503405
theorem B12668075 : Blo 1668034 12668075 := bstep (se 1 (by rfl) ⟨9501056, by rfl⟩ : syracuseStep 12668075 = 19002113) B19002113
theorem B8449271 : Blo 1668034 8449271 := bstep (se 1 (by rfl) ⟨6336953, by rfl⟩ : syracuseStep 8449271 = 12673907) B12673907
theorem B2674063 : Blo 1668034 2674063 := bstep (se 1 (by rfl) ⟨2005547, by rfl⟩ : syracuseStep 2674063 = 4011095) B4011095
theorem B2502071 : Blo 1668034 2502071 := bstep (se 1 (by rfl) ⟨1876553, by rfl⟩ : syracuseStep 2502071 = 3753107) B3753107
theorem B2502107 : Blo 1668034 2502107 := bstep (se 1 (by rfl) ⟨1876580, by rfl⟩ : syracuseStep 2502107 = 3753161) B3753161
theorem B3755483 : Blo 1668034 3755483 := bstep (se 1 (by rfl) ⟨2816612, by rfl⟩ : syracuseStep 3755483 = 5633225) B5633225
theorem B5631497 : Blo 1668034 5631497 := bstep (se 2 (by rfl) ⟨2111811, by rfl⟩ : syracuseStep 5631497 = 4223623) B4223623
theorem B4222489 : Blo 1668034 4222489 := bstep (se 2 (by rfl) ⟨1583433, by rfl⟩ : syracuseStep 4222489 = 3166867) B3166867
theorem B4754983 : Blo 1668034 4754983 := bstep (se 1 (by rfl) ⟨3566237, by rfl⟩ : syracuseStep 4754983 = 7132475) B7132475
theorem B12037693 : Blo 1668034 12037693 := bstep (se 3 (by rfl) ⟨2257067, by rfl⟩ : syracuseStep 12037693 = 4514135) B4514135
theorem B2854523 : Blo 1668034 2854523 := bstep (se 1 (by rfl) ⟨2140892, by rfl⟩ : syracuseStep 2854523 = 4281785) B4281785
theorem B12668561 : Blo 1668034 12668561 := bstep (se 2 (by rfl) ⟨4750710, by rfl⟩ : syracuseStep 12668561 = 9501421) B9501421
theorem B13528721 : Blo 1668034 13528721 := bstep (se 2 (by rfl) ⟨5073270, by rfl⟩ : syracuseStep 13528721 = 10146541) B10146541
theorem B12676823 : Blo 1668034 12676823 := bstep (se 1 (by rfl) ⟨9507617, by rfl⟩ : syracuseStep 12676823 = 19015235) B19015235
theorem B8449757 : Blo 1668034 8449757 := bstep (se 3 (by rfl) ⟨1584329, by rfl⟩ : syracuseStep 8449757 = 3168659) B3168659
theorem B12193517 : Blo 1668034 12193517 := bstep (se 3 (by rfl) ⟨2286284, by rfl⟩ : syracuseStep 12193517 = 4572569) B4572569
theorem B6770425 : Blo 1668034 6770425 := bstep (se 2 (by rfl) ⟨2538909, by rfl⟩ : syracuseStep 6770425 = 5077819) B5077819
theorem B34271009 : Blo 1668034 34271009 := bstep (se 2 (by rfl) ⟨12851628, by rfl⟩ : syracuseStep 34271009 = 25703257) B25703257
theorem B4222793 : Blo 1668034 4222793 := bstep (se 2 (by rfl) ⟨1583547, by rfl⟩ : syracuseStep 4222793 = 3167095) B3167095
theorem B2674505 : Blo 1668034 2674505 := bstep (se 2 (by rfl) ⟨1002939, by rfl⟩ : syracuseStep 2674505 = 2005879) B2005879
theorem B2502575 : Blo 1668034 2502575 := bstep (se 1 (by rfl) ⟨1876931, by rfl⟩ : syracuseStep 2502575 = 3753863) B3753863
theorem B3755951 : Blo 1668034 3755951 := bstep (se 1 (by rfl) ⟨2816963, by rfl⟩ : syracuseStep 3755951 = 5633927) B5633927
theorem B9506753 : Blo 1668034 9506753 := bstep (se 2 (by rfl) ⟨3565032, by rfl⟩ : syracuseStep 9506753 = 7130065) B7130065
theorem B2502665 : Blo 1668034 2502665 := bstep (se 2 (by rfl) ⟨938499, by rfl⟩ : syracuseStep 2502665 = 1876999) B1876999
theorem B2502695 : Blo 1668034 2502695 := bstep (se 1 (by rfl) ⟨1877021, by rfl⟩ : syracuseStep 2502695 = 3754043) B3754043
theorem B6017105 : Blo 1668034 6017105 := bstep (se 2 (by rfl) ⟨2256414, by rfl⟩ : syracuseStep 6017105 = 4512829) B4512829
theorem B2502779 : Blo 1668034 2502779 := bstep (se 1 (by rfl) ⟨1877084, by rfl⟩ : syracuseStep 2502779 = 3754169) B3754169
theorem B3756203 : Blo 1668034 3756203 := bstep (se 1 (by rfl) ⟨2817152, by rfl⟩ : syracuseStep 3756203 = 5634305) B5634305
theorem B2502905 : Blo 1668034 2502905 := bstep (se 2 (by rfl) ⟨938589, by rfl⟩ : syracuseStep 2502905 = 1877179) B1877179
theorem B2503007 : Blo 1668034 2503007 := bstep (se 1 (by rfl) ⟨1877255, by rfl⟩ : syracuseStep 2503007 = 3754511) B3754511
theorem B5632361 : Blo 1668034 5632361 := bstep (se 2 (by rfl) ⟨2112135, by rfl⟩ : syracuseStep 5632361 = 4224271) B4224271
theorem B2503019 : Blo 1668034 2503019 := bstep (se 1 (by rfl) ⟨1877264, by rfl⟩ : syracuseStep 2503019 = 3754529) B3754529
theorem B6336893 : Blo 1668034 6336893 := bstep (se 3 (by rfl) ⟨1188167, by rfl⟩ : syracuseStep 6336893 = 2376335) B2376335
theorem B10695149 : Blo 1668034 10695149 := bstep (se 3 (by rfl) ⟨2005340, by rfl⟩ : syracuseStep 10695149 = 4010681) B4010681
theorem B2503247 : Blo 1668034 2503247 := bstep (se 1 (by rfl) ⟨1877435, by rfl⟩ : syracuseStep 2503247 = 3754871) B3754871
theorem B2503367 : Blo 1668034 2503367 := bstep (se 1 (by rfl) ⟨1877525, by rfl⟩ : syracuseStep 2503367 = 3755051) B3755051
theorem B3912391 : Blo 1668034 3912391 := bstep (se 1 (by rfl) ⟨2934293, by rfl⟩ : syracuseStep 3912391 = 5868587) B5868587
theorem B3756743 : Blo 1668034 3756743 := bstep (se 1 (by rfl) ⟨2817557, by rfl⟩ : syracuseStep 3756743 = 5635115) B5635115
theorem B16044803 : Blo 1668034 16044803 := bstep (se 1 (by rfl) ⟨12033602, by rfl⟩ : syracuseStep 16044803 = 24067205) B24067205
theorem B2503529 : Blo 1668034 2503529 := bstep (se 2 (by rfl) ⟨938823, by rfl⟩ : syracuseStep 2503529 = 1877647) B1877647
theorem B4223927 : Blo 1668034 4223927 := bstep (se 1 (by rfl) ⟨3167945, by rfl⟩ : syracuseStep 4223927 = 6335891) B6335891
theorem B2503607 : Blo 1668034 2503607 := bstep (se 1 (by rfl) ⟨1877705, by rfl⟩ : syracuseStep 2503607 = 3755411) B3755411
theorem B5632955 : Blo 1668034 5632955 := bstep (se 1 (by rfl) ⟨4224716, by rfl⟩ : syracuseStep 5632955 = 8449433) B8449433
theorem B1668039 : Blo 1668034 1668039 := bstep (se 1 (by rfl) ⟨1251029, by rfl⟩ : syracuseStep 1668039 = 2502059) B2502059
theorem B1668059 : Blo 1668034 1668059 := bstep (se 1 (by rfl) ⟨1251044, by rfl⟩ : syracuseStep 1668059 = 2502089) B2502089
theorem B2503643 : Blo 1668034 2503643 := bstep (se 1 (by rfl) ⟨1877732, by rfl⟩ : syracuseStep 2503643 = 3755465) B3755465
theorem B2855945 : Blo 1668034 2855945 := bstep (se 2 (by rfl) ⟨1070979, by rfl⟩ : syracuseStep 2855945 = 2141959) B2141959
theorem B5346319 : Blo 1668034 5346319 := bstep (se 1 (by rfl) ⟨4009739, by rfl⟩ : syracuseStep 5346319 = 8019479) B8019479
theorem B1668135 : Blo 1668034 1668135 := bstep (se 1 (by rfl) ⟨1251101, by rfl⟩ : syracuseStep 1668135 = 2502203) B2502203
theorem B2815033 : Blo 1668034 2815033 := bstep (se 2 (by rfl) ⟨1055637, by rfl⟩ : syracuseStep 2815033 = 2111275) B2111275
theorem B18035779 : Blo 1668034 18035779 := bstep (se 1 (by rfl) ⟨13526834, by rfl⟩ : syracuseStep 18035779 = 27053669) B27053669
theorem B12670019 : Blo 1668034 12670019 := bstep (se 1 (by rfl) ⟨9502514, by rfl⟩ : syracuseStep 12670019 = 19005029) B19005029
theorem B1668175 : Blo 1668034 1668175 := bstep (se 1 (by rfl) ⟨1251131, by rfl⟩ : syracuseStep 1668175 = 2502263) B2502263
theorem B1668191 : Blo 1668034 1668191 := bstep (se 1 (by rfl) ⟨1251143, by rfl⟩ : syracuseStep 1668191 = 2502287) B2502287
theorem B1668219 : Blo 1668034 1668219 := bstep (se 1 (by rfl) ⟨1251164, by rfl⟩ : syracuseStep 1668219 = 2502329) B2502329
theorem B1668271 : Blo 1668034 1668271 := bstep (se 1 (by rfl) ⟨1251203, by rfl⟩ : syracuseStep 1668271 = 2502407) B2502407
theorem B2815175 : Blo 1668034 2815175 := bstep (se 1 (by rfl) ⟨2111381, by rfl⟩ : syracuseStep 2815175 = 4222763) B4222763
theorem B1668295 : Blo 1668034 1668295 := bstep (se 1 (by rfl) ⟨1251221, by rfl⟩ : syracuseStep 1668295 = 2502443) B2502443
theorem B1668315 : Blo 1668034 1668315 := bstep (se 1 (by rfl) ⟨1251236, by rfl⟩ : syracuseStep 1668315 = 2502473) B2502473
theorem B1668391 : Blo 1668034 1668391 := bstep (se 1 (by rfl) ⟨1251293, by rfl⟩ : syracuseStep 1668391 = 2502587) B2502587
theorem B1668431 : Blo 1668034 1668431 := bstep (se 1 (by rfl) ⟨1251323, by rfl⟩ : syracuseStep 1668431 = 2502647) B2502647
theorem B1668447 : Blo 1668034 1668447 := bstep (se 1 (by rfl) ⟨1251335, by rfl⟩ : syracuseStep 1668447 = 2502671) B2502671
theorem B2815337 : Blo 1668034 2815337 := bstep (se 2 (by rfl) ⟨1055751, by rfl⟩ : syracuseStep 2815337 = 2111503) B2111503
theorem B1668475 : Blo 1668034 1668475 := bstep (se 1 (by rfl) ⟨1251356, by rfl⟩ : syracuseStep 1668475 = 2502713) B2502713
theorem B1668527 : Blo 1668034 1668527 := bstep (se 1 (by rfl) ⟨1251395, by rfl⟩ : syracuseStep 1668527 = 2502791) B2502791
theorem B2504111 : Blo 1668034 2504111 := bstep (se 1 (by rfl) ⟨1878083, by rfl⟩ : syracuseStep 2504111 = 3756167) B3756167
theorem B1668551 : Blo 1668034 1668551 := bstep (se 1 (by rfl) ⟨1251413, by rfl⟩ : syracuseStep 1668551 = 2502827) B2502827
theorem B12842459 : Blo 1668034 12842459 := bstep (se 1 (by rfl) ⟨9631844, by rfl⟩ : syracuseStep 12842459 = 19263689) B19263689
theorem B1668571 : Blo 1668034 1668571 := bstep (se 1 (by rfl) ⟨1251428, by rfl⟩ : syracuseStep 1668571 = 2502857) B2502857
theorem B2504201 : Blo 1668034 2504201 := bstep (se 2 (by rfl) ⟨939075, by rfl⟩ : syracuseStep 2504201 = 1878151) B1878151
theorem B1668647 : Blo 1668034 1668647 := bstep (se 1 (by rfl) ⟨1251485, by rfl⟩ : syracuseStep 1668647 = 2502971) B2502971
theorem B2504231 : Blo 1668034 2504231 := bstep (se 1 (by rfl) ⟨1878173, by rfl⟩ : syracuseStep 2504231 = 3756347) B3756347
theorem B1668687 : Blo 1668034 1668687 := bstep (se 1 (by rfl) ⟨1251515, by rfl⟩ : syracuseStep 1668687 = 2503031) B2503031
theorem B1668703 : Blo 1668034 1668703 := bstep (se 1 (by rfl) ⟨1251527, by rfl⟩ : syracuseStep 1668703 = 2503055) B2503055
theorem B1668731 : Blo 1668034 1668731 := bstep (se 1 (by rfl) ⟨1251548, by rfl⟩ : syracuseStep 1668731 = 2503097) B2503097
theorem B2504315 : Blo 1668034 2504315 := bstep (se 1 (by rfl) ⟨1878236, by rfl⟩ : syracuseStep 2504315 = 3756473) B3756473
theorem B1668783 : Blo 1668034 1668783 := bstep (se 1 (by rfl) ⟨1251587, by rfl⟩ : syracuseStep 1668783 = 2503175) B2503175
theorem B1668807 : Blo 1668034 1668807 := bstep (se 1 (by rfl) ⟨1251605, by rfl⟩ : syracuseStep 1668807 = 2503211) B2503211
theorem B1668827 : Blo 1668034 1668827 := bstep (se 1 (by rfl) ⟨1251620, by rfl⟩ : syracuseStep 1668827 = 2503241) B2503241
theorem B2815735 : Blo 1668034 2815735 := bstep (se 1 (by rfl) ⟨2111801, by rfl⟩ : syracuseStep 2815735 = 4223603) B4223603
theorem B3806969 : Blo 1668034 3806969 := bstep (se 2 (by rfl) ⟨1427613, by rfl⟩ : syracuseStep 3806969 = 2855227) B2855227
theorem B2504441 : Blo 1668034 2504441 := bstep (se 2 (by rfl) ⟨939165, by rfl⟩ : syracuseStep 2504441 = 1878331) B1878331
theorem B10696481 : Blo 1668034 10696481 := bstep (se 2 (by rfl) ⟨4011180, by rfl⟩ : syracuseStep 10696481 = 8022361) B8022361
theorem B1668903 : Blo 1668034 1668903 := bstep (se 1 (by rfl) ⟨1251677, by rfl⟩ : syracuseStep 1668903 = 2503355) B2503355
theorem B1668943 : Blo 1668034 1668943 := bstep (se 1 (by rfl) ⟨1251707, by rfl⟩ : syracuseStep 1668943 = 2503415) B2503415
theorem B1668959 : Blo 1668034 1668959 := bstep (se 1 (by rfl) ⟨1251719, by rfl⟩ : syracuseStep 1668959 = 2503439) B2503439
theorem B2504543 : Blo 1668034 2504543 := bstep (se 1 (by rfl) ⟨1878407, by rfl⟩ : syracuseStep 2504543 = 3756815) B3756815
theorem B2504555 : Blo 1668034 2504555 := bstep (se 1 (by rfl) ⟨1878416, by rfl⟩ : syracuseStep 2504555 = 3756833) B3756833
theorem B1668987 : Blo 1668034 1668987 := bstep (se 1 (by rfl) ⟨1251740, by rfl⟩ : syracuseStep 1668987 = 2503481) B2503481
theorem B3168143 : Blo 1668034 3168143 := bstep (se 1 (by rfl) ⟨2376107, by rfl⟩ : syracuseStep 3168143 = 4752215) B4752215
theorem B1669039 : Blo 1668034 1669039 := bstep (se 1 (by rfl) ⟨1251779, by rfl⟩ : syracuseStep 1669039 = 2503559) B2503559
theorem B2815931 : Blo 1668034 2815931 := bstep (se 1 (by rfl) ⟨2111948, by rfl⟩ : syracuseStep 2815931 = 4223897) B4223897
theorem B1669063 : Blo 1668034 1669063 := bstep (se 1 (by rfl) ⟨1251797, by rfl⟩ : syracuseStep 1669063 = 2503595) B2503595
theorem B1669083 : Blo 1668034 1669083 := bstep (se 1 (by rfl) ⟨1251812, by rfl⟩ : syracuseStep 1669083 = 2503625) B2503625
theorem B4225031 : Blo 1668034 4225031 := bstep (se 1 (by rfl) ⟨3168773, by rfl⟩ : syracuseStep 4225031 = 6337547) B6337547
theorem B12670991 : Blo 1668034 12670991 := bstep (se 1 (by rfl) ⟨9503243, by rfl⟩ : syracuseStep 12670991 = 19006487) B19006487
theorem B2816039 : Blo 1668034 2816039 := bstep (se 1 (by rfl) ⟨2112029, by rfl⟩ : syracuseStep 2816039 = 4224059) B4224059
theorem B1669159 : Blo 1668034 1669159 := bstep (se 1 (by rfl) ⟨1251869, by rfl⟩ : syracuseStep 1669159 = 2503739) B2503739
theorem B4511801 : Blo 1668034 4511801 := bstep (se 2 (by rfl) ⟨1691925, by rfl⟩ : syracuseStep 4511801 = 3383851) B3383851
theorem B4225081 : Blo 1668034 4225081 := bstep (se 2 (by rfl) ⟨1584405, by rfl⟩ : syracuseStep 4225081 = 3168811) B3168811
theorem B1669199 : Blo 1668034 1669199 := bstep (se 1 (by rfl) ⟨1251899, by rfl⟩ : syracuseStep 1669199 = 2503799) B2503799
theorem B2504783 : Blo 1668034 2504783 := bstep (se 1 (by rfl) ⟨1878587, by rfl⟩ : syracuseStep 2504783 = 3757175) B3757175
theorem B1669215 : Blo 1668034 1669215 := bstep (se 1 (by rfl) ⟨1251911, by rfl⟩ : syracuseStep 1669215 = 2503823) B2503823
theorem B1669243 : Blo 1668034 1669243 := bstep (se 1 (by rfl) ⟨1251932, by rfl⟩ : syracuseStep 1669243 = 2503865) B2503865
theorem B14448797 : Blo 1668034 14448797 := bstep (se 3 (by rfl) ⟨2709149, by rfl⟩ : syracuseStep 14448797 = 5418299) B5418299
theorem B1669295 : Blo 1668034 1669295 := bstep (se 1 (by rfl) ⟨1251971, by rfl⟩ : syracuseStep 1669295 = 2503943) B2503943
theorem B1669319 : Blo 1668034 1669319 := bstep (se 1 (by rfl) ⟨1251989, by rfl⟩ : syracuseStep 1669319 = 2503979) B2503979
theorem B2504903 : Blo 1668034 2504903 := bstep (se 1 (by rfl) ⟨1878677, by rfl⟩ : syracuseStep 2504903 = 3757355) B3757355
theorem B1669339 : Blo 1668034 1669339 := bstep (se 1 (by rfl) ⟨1252004, by rfl⟩ : syracuseStep 1669339 = 2504009) B2504009
theorem B6338807 : Blo 1668034 6338807 := bstep (se 1 (by rfl) ⟨4754105, by rfl⟩ : syracuseStep 6338807 = 9508211) B9508211
theorem B11417867 : Blo 1668034 11417867 := bstep (se 1 (by rfl) ⟨8563400, by rfl⟩ : syracuseStep 11417867 = 17126801) B17126801
theorem B1669415 : Blo 1668034 1669415 := bstep (se 1 (by rfl) ⟨1252061, by rfl⟩ : syracuseStep 1669415 = 2504123) B2504123
theorem B2816329 : Blo 1668034 2816329 := bstep (se 2 (by rfl) ⟨1056123, by rfl⟩ : syracuseStep 2816329 = 2112247) B2112247
theorem B1669455 : Blo 1668034 1669455 := bstep (se 1 (by rfl) ⟨1252091, by rfl⟩ : syracuseStep 1669455 = 2504183) B2504183
theorem B1669471 : Blo 1668034 1669471 := bstep (se 1 (by rfl) ⟨1252103, by rfl⟩ : syracuseStep 1669471 = 2504207) B2504207
theorem B4225385 : Blo 1668034 4225385 := bstep (se 2 (by rfl) ⟨1584519, by rfl⟩ : syracuseStep 4225385 = 3169039) B3169039
theorem B2816363 : Blo 1668034 2816363 := bstep (se 1 (by rfl) ⟨2112272, by rfl⟩ : syracuseStep 2816363 = 4224545) B4224545
theorem B1669499 : Blo 1668034 1669499 := bstep (se 1 (by rfl) ⟨1252124, by rfl⟩ : syracuseStep 1669499 = 2504249) B2504249
theorem B1669551 : Blo 1668034 1669551 := bstep (se 1 (by rfl) ⟨1252163, by rfl⟩ : syracuseStep 1669551 = 2504327) B2504327
theorem B1669575 : Blo 1668034 1669575 := bstep (se 1 (by rfl) ⟨1252181, by rfl⟩ : syracuseStep 1669575 = 2504363) B2504363
theorem B1669595 : Blo 1668034 1669595 := bstep (se 1 (by rfl) ⟨1252196, by rfl⟩ : syracuseStep 1669595 = 2504393) B2504393
theorem B4012507 : Blo 1668034 4012507 := bstep (se 1 (by rfl) ⟨3009380, by rfl⟩ : syracuseStep 4012507 = 6018761) B6018761
theorem B3381767 : Blo 1668034 3381767 := bstep (se 1 (by rfl) ⟨2536325, by rfl⟩ : syracuseStep 3381767 = 5072651) B5072651
theorem B9640457 : Blo 1668034 9640457 := bstep (se 2 (by rfl) ⟨3615171, by rfl⟩ : syracuseStep 9640457 = 7230343) B7230343
theorem B1669671 : Blo 1668034 1669671 := bstep (se 1 (by rfl) ⟨1252253, by rfl⟩ : syracuseStep 1669671 = 2504507) B2504507
theorem B12679739 : Blo 1668034 12679739 := bstep (se 1 (by rfl) ⟨9509804, by rfl⟩ : syracuseStep 12679739 = 19019609) B19019609
theorem B1669711 : Blo 1668034 1669711 := bstep (se 1 (by rfl) ⟨1252283, by rfl⟩ : syracuseStep 1669711 = 2504567) B2504567
theorem B1669727 : Blo 1668034 1669727 := bstep (se 1 (by rfl) ⟨1252295, by rfl⟩ : syracuseStep 1669727 = 2504591) B2504591
theorem B5634683 : Blo 1668034 5634683 := bstep (se 1 (by rfl) ⟨4226012, by rfl⟩ : syracuseStep 5634683 = 8452025) B8452025
theorem B1669755 : Blo 1668034 1669755 := bstep (se 1 (by rfl) ⟨1252316, by rfl⟩ : syracuseStep 1669755 = 2504633) B2504633
theorem B6421139 : Blo 1668034 6421139 := bstep (se 1 (by rfl) ⟨4815854, by rfl⟩ : syracuseStep 6421139 = 9631709) B9631709
theorem B1669807 : Blo 1668034 1669807 := bstep (se 1 (by rfl) ⟨1252355, by rfl⟩ : syracuseStep 1669807 = 2504711) B2504711
theorem B1669831 : Blo 1668034 1669831 := bstep (se 1 (by rfl) ⟨1252373, by rfl⟩ : syracuseStep 1669831 = 2504747) B2504747
theorem B12024521 : Blo 1668034 12024521 := bstep (se 2 (by rfl) ⟨4509195, by rfl⟩ : syracuseStep 12024521 = 9018391) B9018391
theorem B1669851 : Blo 1668034 1669851 := bstep (se 1 (by rfl) ⟨1252388, by rfl⟩ : syracuseStep 1669851 = 2504777) B2504777
theorem B4750073 : Blo 1668034 4750073 := bstep (se 2 (by rfl) ⟨1781277, by rfl⟩ : syracuseStep 4750073 = 3562555) B3562555
theorem B2816761 : Blo 1668034 2816761 := bstep (se 2 (by rfl) ⟨1056285, by rfl⟩ : syracuseStep 2816761 = 2112571) B2112571
theorem B12024605 : Blo 1668034 12024605 := bstep (se 3 (by rfl) ⟨2254613, by rfl⟩ : syracuseStep 12024605 = 4509227) B4509227
theorem B5634845 : Blo 1668034 5634845 := bstep (se 3 (by rfl) ⟨1056533, by rfl⟩ : syracuseStep 5634845 = 2113067) B2113067
theorem B1669927 : Blo 1668034 1669927 := bstep (se 1 (by rfl) ⟨1252445, by rfl⟩ : syracuseStep 1669927 = 2504891) B2504891
theorem B1669967 : Blo 1668034 1669967 := bstep (se 1 (by rfl) ⟨1252475, by rfl⟩ : syracuseStep 1669967 = 2504951) B2504951
theorem B1669983 : Blo 1668034 1669983 := bstep (se 1 (by rfl) ⟨1252487, by rfl⟩ : syracuseStep 1669983 = 2504975) B2504975
theorem B1670011 : Blo 1668034 1670011 := bstep (se 1 (by rfl) ⟨1252508, by rfl⟩ : syracuseStep 1670011 = 2505017) B2505017
theorem B4750255 : Blo 1668034 4750255 := bstep (se 1 (by rfl) ⟨3562691, by rfl⟩ : syracuseStep 4750255 = 7125383) B7125383
theorem B3169199 : Blo 1668034 3169199 := bstep (se 1 (by rfl) ⟨2376899, by rfl⟩ : syracuseStep 3169199 = 4753799) B4753799
theorem B2112475 : Blo 1668034 2112475 := bstep (se 1 (by rfl) ⟨1584356, by rfl⟩ : syracuseStep 2112475 = 3168713) B3168713
theorem B10689509 : Blo 1668034 10689509 := bstep (se 4 (by rfl) ⟨1002141, by rfl⟩ : syracuseStep 10689509 = 2004283) B2004283
theorem B2817031 : Blo 1668034 2817031 := bstep (se 1 (by rfl) ⟨2112773, by rfl⟩ : syracuseStep 2817031 = 4225547) B4225547
theorem B14261291 : Blo 1668034 14261291 := bstep (se 1 (by rfl) ⟨10695968, by rfl⟩ : syracuseStep 14261291 = 21391937) B21391937
theorem B6339779 : Blo 1668034 6339779 := bstep (se 1 (by rfl) ⟨4754834, by rfl⟩ : syracuseStep 6339779 = 9509669) B9509669
theorem B3169631 : Blo 1668034 3169631 := bstep (se 1 (by rfl) ⟨2377223, by rfl⟩ : syracuseStep 3169631 = 4754447) B4754447
theorem B2817463 : Blo 1668034 2817463 := bstep (se 1 (by rfl) ⟨2113097, by rfl⟩ : syracuseStep 2817463 = 4226195) B4226195
theorem B2538935 : Blo 1668034 2538935 := bstep (se 1 (by rfl) ⟨1904201, by rfl⟩ : syracuseStep 2538935 = 3808403) B3808403
theorem B5635547 : Blo 1668034 5635547 := bstep (se 1 (by rfl) ⟨4226660, by rfl⟩ : syracuseStep 5635547 = 8453321) B8453321
theorem B2817659 : Blo 1668034 2817659 := bstep (se 1 (by rfl) ⟨2113244, by rfl⟩ : syracuseStep 2817659 = 4226489) B4226489
theorem B6094535 : Blo 1668034 6094535 := bstep (se 1 (by rfl) ⟨4570901, by rfl⟩ : syracuseStep 6094535 = 9141803) B9141803
theorem B6340295 : Blo 1668034 6340295 := bstep (se 1 (by rfl) ⟨4755221, by rfl⟩ : syracuseStep 6340295 = 9510443) B9510443
theorem B36093701 : Blo 1668034 36093701 := bstep (se 4 (by rfl) ⟨3383784, by rfl⟩ : syracuseStep 36093701 = 6767569) B6767569
theorem B5349215 : Blo 1668034 5349215 := bstep (se 1 (by rfl) ⟨4011911, by rfl⟩ : syracuseStep 5349215 = 8023823) B8023823
theorem B24387443 : Blo 1668034 24387443 := bstep (se 1 (by rfl) ⟨18290582, by rfl⟩ : syracuseStep 24387443 = 36581165) B36581165
theorem B2408411 : Blo 1668034 2408411 := bstep (se 1 (by rfl) ⟨1806308, by rfl⟩ : syracuseStep 2408411 = 3612617) B3612617
theorem B3563785 : Blo 1668034 3563785 := bstep (se 2 (by rfl) ⟨1336419, by rfl⟩ : syracuseStep 3563785 = 2672839) B2672839
theorem B6766955 : Blo 1668034 6766955 := bstep (se 1 (by rfl) ⟨5075216, by rfl⟩ : syracuseStep 6766955 = 10150433) B10150433
theorem B8446679 : Blo 1668034 8446679 := bstep (se 1 (by rfl) ⟨6335009, by rfl⟩ : syracuseStep 8446679 = 12670019) B12670019
theorem B2376415 : Blo 1668034 2376415 := bstep (se 1 (by rfl) ⟨1782311, by rfl⟩ : syracuseStep 2376415 = 3564623) B3564623
theorem B1876783 : Blo 1668034 1876783 := bstep (se 1 (by rfl) ⟨1407587, by rfl⟩ : syracuseStep 1876783 = 2815175) B2815175
theorem B36569933 : Blo 1668034 36569933 := bstep (se 3 (by rfl) ⟨6856862, by rfl⟩ : syracuseStep 36569933 = 13713725) B13713725
theorem B1876891 : Blo 1668034 1876891 := bstep (se 1 (by rfl) ⟨1407668, by rfl⟩ : syracuseStep 1876891 = 2815337) B2815337
theorem B8561639 : Blo 1668034 8561639 := bstep (se 1 (by rfl) ⟨6421229, by rfl⟩ : syracuseStep 8561639 = 12842459) B12842459
theorem B20866085 : Blo 1668034 20866085 := bstep (se 4 (by rfl) ⟨1956195, by rfl⟩ : syracuseStep 20866085 = 3912391) B3912391
theorem B3753179 : Blo 1668034 3753179 := bstep (se 1 (by rfl) ⟨2814884, by rfl⟩ : syracuseStep 3753179 = 5629769) B5629769
theorem B6333673 : Blo 1668034 6333673 := bstep (se 2 (by rfl) ⟨2375127, by rfl⟩ : syracuseStep 6333673 = 4750255) B4750255
theorem B1877287 : Blo 1668034 1877287 := bstep (se 1 (by rfl) ⟨1407965, by rfl⟩ : syracuseStep 1877287 = 2815931) B2815931
theorem B8447327 : Blo 1668034 8447327 := bstep (se 1 (by rfl) ⟨6335495, by rfl⟩ : syracuseStep 8447327 = 12670991) B12670991
theorem B7128425 : Blo 1668034 7128425 := bstep (se 2 (by rfl) ⟨2673159, by rfl⟩ : syracuseStep 7128425 = 5346319) B5346319
theorem B1877359 : Blo 1668034 1877359 := bstep (se 1 (by rfl) ⟨1408019, by rfl⟩ : syracuseStep 1877359 = 2816039) B2816039
theorem B3007867 : Blo 1668034 3007867 := bstep (se 1 (by rfl) ⟨2255900, by rfl⟩ : syracuseStep 3007867 = 4511801) B4511801
theorem B3753377 : Blo 1668034 3753377 := bstep (se 2 (by rfl) ⟨1407516, by rfl⟩ : syracuseStep 3753377 = 2815033) B2815033
theorem B410936753 : Blo 1668034 410936753 := bstep (se 2 (by rfl) ⟨154101282, by rfl⟩ : syracuseStep 410936753 = 308202565) B308202565
theorem B7611911 : Blo 1668034 7611911 := bstep (se 1 (by rfl) ⟨5708933, by rfl⟩ : syracuseStep 7611911 = 11417867) B11417867
theorem B1877575 : Blo 1668034 1877575 := bstep (se 1 (by rfl) ⟨1408181, by rfl⟩ : syracuseStep 1877575 = 2816363) B2816363
theorem B2254511 : Blo 1668034 2254511 := bstep (se 1 (by rfl) ⟨1690883, by rfl⟩ : syracuseStep 2254511 = 3381767) B3381767
theorem B3753935 : Blo 1668034 3753935 := bstep (se 1 (by rfl) ⟨2815451, by rfl⟩ : syracuseStep 3753935 = 5630903) B5630903
theorem B2377679 : Blo 1668034 2377679 := bstep (se 1 (by rfl) ⟨1783259, by rfl⟩ : syracuseStep 2377679 = 3566519) B3566519
theorem B96249869 : Blo 1668034 96249869 := bstep (se 3 (by rfl) ⟨18046850, by rfl⟩ : syracuseStep 96249869 = 36093701) B36093701
theorem B5629985 : Blo 1668034 5629985 := bstep (se 2 (by rfl) ⟨2111244, by rfl⟩ : syracuseStep 5629985 = 4222489) B4222489
theorem B16050257 : Blo 1668034 16050257 := bstep (se 2 (by rfl) ⟨6018846, by rfl⟩ : syracuseStep 16050257 = 12037693) B12037693
theorem B4753673 : Blo 1668034 4753673 := bstep (se 2 (by rfl) ⟨1782627, by rfl⟩ : syracuseStep 4753673 = 3565255) B3565255
theorem B12675365 : Blo 1668034 12675365 := bstep (se 4 (by rfl) ⟨1188315, by rfl⟩ : syracuseStep 12675365 = 2376631) B2376631
theorem B3754313 : Blo 1668034 3754313 := bstep (se 2 (by rfl) ⟨1407867, by rfl⟩ : syracuseStep 3754313 = 2815735) B2815735
theorem B3754331 : Blo 1668034 3754331 := bstep (se 1 (by rfl) ⟨2815748, by rfl⟩ : syracuseStep 3754331 = 5631497) B5631497
theorem B1903015 : Blo 1668034 1903015 := bstep (se 1 (by rfl) ⟨1427261, by rfl⟩ : syracuseStep 1903015 = 2854523) B2854523
theorem B1878439 : Blo 1668034 1878439 := bstep (se 1 (by rfl) ⟨1408829, by rfl⟩ : syracuseStep 1878439 = 2817659) B2817659
theorem B21400037 : Blo 1668034 21400037 := bstep (se 4 (by rfl) ⟨2006253, by rfl⟩ : syracuseStep 21400037 = 4012507) B4012507
theorem B8129011 : Blo 1668034 8129011 := bstep (se 1 (by rfl) ⟨6096758, by rfl⟩ : syracuseStep 8129011 = 12193517) B12193517
theorem B3566143 : Blo 1668034 3566143 := bstep (se 1 (by rfl) ⟨2674607, by rfl⟩ : syracuseStep 3566143 = 5349215) B5349215
theorem B3566263 : Blo 1668034 3566263 := bstep (se 1 (by rfl) ⟨2674697, by rfl⟩ : syracuseStep 3566263 = 5349395) B5349395
theorem B3754907 : Blo 1668034 3754907 := bstep (se 1 (by rfl) ⟨2816180, by rfl⟩ : syracuseStep 3754907 = 5632361) B5632361
theorem B7130099 : Blo 1668034 7130099 := bstep (se 1 (by rfl) ⟨5347574, by rfl⟩ : syracuseStep 7130099 = 10695149) B10695149
theorem B15428647 : Blo 1668034 15428647 := bstep (se 1 (by rfl) ⟨11571485, by rfl⟩ : syracuseStep 15428647 = 23142971) B23142971
theorem B16264259 : Blo 1668034 16264259 := bstep (se 1 (by rfl) ⟨12198194, by rfl⟩ : syracuseStep 16264259 = 24396389) B24396389
theorem B3755105 : Blo 1668034 3755105 := bstep (se 2 (by rfl) ⟨1408164, by rfl⟩ : syracuseStep 3755105 = 2816329) B2816329
theorem B3755303 : Blo 1668034 3755303 := bstep (se 1 (by rfl) ⟨2816477, by rfl⟩ : syracuseStep 3755303 = 5632955) B5632955
theorem B1903963 : Blo 1668034 1903963 := bstep (se 1 (by rfl) ⟨1427972, by rfl⟩ : syracuseStep 1903963 = 2855945) B2855945
theorem B2502137 : Blo 1668034 2502137 := bstep (se 2 (by rfl) ⟨938301, by rfl⟩ : syracuseStep 2502137 = 1876603) B1876603
theorem B8449595 : Blo 1668034 8449595 := bstep (se 1 (by rfl) ⟨6337196, by rfl⟩ : syracuseStep 8449595 = 12674393) B12674393
theorem B2502239 : Blo 1668034 2502239 := bstep (se 1 (by rfl) ⟨1876679, by rfl⟩ : syracuseStep 2502239 = 3753359) B3753359
theorem B3755681 : Blo 1668034 3755681 := bstep (se 2 (by rfl) ⟨1408380, by rfl⟩ : syracuseStep 3755681 = 2816761) B2816761
theorem B4222651 : Blo 1668034 4222651 := bstep (se 1 (by rfl) ⟨3166988, by rfl⟩ : syracuseStep 4222651 = 6333977) B6333977
theorem B1781551 : Blo 1668034 1781551 := bstep (se 1 (by rfl) ⟨1336163, by rfl⟩ : syracuseStep 1781551 = 2672327) B2672327
theorem B2502455 : Blo 1668034 2502455 := bstep (se 1 (by rfl) ⟨1876841, by rfl⟩ : syracuseStep 2502455 = 3753683) B3753683
theorem B4755257 : Blo 1668034 4755257 := bstep (se 2 (by rfl) ⟨1783221, by rfl⟩ : syracuseStep 4755257 = 3566443) B3566443
theorem B7130987 : Blo 1668034 7130987 := bstep (se 1 (by rfl) ⟨5348240, by rfl⟩ : syracuseStep 7130987 = 10696481) B10696481
theorem B3756041 : Blo 1668034 3756041 := bstep (se 2 (by rfl) ⟨1408515, by rfl⟩ : syracuseStep 3756041 = 2817031) B2817031
theorem B24047705 : Blo 1668034 24047705 := bstep (se 2 (by rfl) ⟨9017889, by rfl⟩ : syracuseStep 24047705 = 18035779) B18035779
theorem B2502761 : Blo 1668034 2502761 := bstep (se 2 (by rfl) ⟨938535, by rfl⟩ : syracuseStep 2502761 = 1877071) B1877071
theorem B6426971 : Blo 1668034 6426971 := bstep (se 1 (by rfl) ⟨4820228, by rfl⟩ : syracuseStep 6426971 = 9640457) B9640457
theorem B2503079 : Blo 1668034 2503079 := bstep (se 1 (by rfl) ⟨1877309, by rfl⟩ : syracuseStep 2503079 = 3754619) B3754619
theorem B3756455 : Blo 1668034 3756455 := bstep (se 1 (by rfl) ⟨2817341, by rfl⟩ : syracuseStep 3756455 = 5634683) B5634683
theorem B4280759 : Blo 1668034 4280759 := bstep (se 1 (by rfl) ⟨3210569, by rfl⟩ : syracuseStep 4280759 = 6421139) B6421139
theorem B8016347 : Blo 1668034 8016347 := bstep (se 1 (by rfl) ⟨6012260, by rfl⟩ : syracuseStep 8016347 = 12024521) B12024521
theorem B3166715 : Blo 1668034 3166715 := bstep (se 1 (by rfl) ⟨2375036, by rfl⟩ : syracuseStep 3166715 = 4750073) B4750073
theorem B2503163 : Blo 1668034 2503163 := bstep (se 1 (by rfl) ⟨1877372, by rfl⟩ : syracuseStep 2503163 = 3754745) B3754745
theorem B8016403 : Blo 1668034 8016403 := bstep (se 1 (by rfl) ⟨6012302, by rfl⟩ : syracuseStep 8016403 = 12024605) B12024605
theorem B3756563 : Blo 1668034 3756563 := bstep (se 1 (by rfl) ⟨2817422, by rfl⟩ : syracuseStep 3756563 = 5634845) B5634845
theorem B11416115 : Blo 1668034 11416115 := bstep (se 1 (by rfl) ⟨8562086, by rfl⟩ : syracuseStep 11416115 = 17124173) B17124173
theorem B3756617 : Blo 1668034 3756617 := bstep (se 2 (by rfl) ⟨1408731, by rfl⟩ : syracuseStep 3756617 = 2817463) B2817463
theorem B2503289 : Blo 1668034 2503289 := bstep (se 2 (by rfl) ⟨938733, by rfl⟩ : syracuseStep 2503289 = 1877467) B1877467
theorem B2503343 : Blo 1668034 2503343 := bstep (se 1 (by rfl) ⟨1877507, by rfl⟩ : syracuseStep 2503343 = 3755015) B3755015
theorem B91402931 : Blo 1668034 91402931 := bstep (se 1 (by rfl) ⟨68552198, by rfl⟩ : syracuseStep 91402931 = 137104397) B137104397
theorem B9507527 : Blo 1668034 9507527 := bstep (se 1 (by rfl) ⟨7130645, by rfl⟩ : syracuseStep 9507527 = 14261291) B14261291
theorem B2503391 : Blo 1668034 2503391 := bstep (se 1 (by rfl) ⟨1877543, by rfl⟩ : syracuseStep 2503391 = 3755087) B3755087
theorem B4010719 : Blo 1668034 4010719 := bstep (se 1 (by rfl) ⟨3008039, by rfl⟩ : syracuseStep 4010719 = 6016079) B6016079
theorem B4223735 : Blo 1668034 4223735 := bstep (se 1 (by rfl) ⟨3167801, by rfl⟩ : syracuseStep 4223735 = 6335603) B6335603
theorem B5632847 : Blo 1668034 5632847 := bstep (se 1 (by rfl) ⟨4224635, by rfl⟩ : syracuseStep 5632847 = 8449271) B8449271
theorem B7132013 : Blo 1668034 7132013 := bstep (se 3 (by rfl) ⟨1337252, by rfl⟩ : syracuseStep 7132013 = 2674505) B2674505
theorem B1668047 : Blo 1668034 1668047 := bstep (se 1 (by rfl) ⟨1251035, by rfl⟩ : syracuseStep 1668047 = 2502071) B2502071
theorem B1692623 : Blo 1668034 1692623 := bstep (se 1 (by rfl) ⟨1269467, by rfl⟩ : syracuseStep 1692623 = 2538935) B2538935
theorem B1668071 : Blo 1668034 1668071 := bstep (se 1 (by rfl) ⟨1251053, by rfl⟩ : syracuseStep 1668071 = 2502107) B2502107
theorem B2503655 : Blo 1668034 2503655 := bstep (se 1 (by rfl) ⟨1877741, by rfl⟩ : syracuseStep 2503655 = 3755483) B3755483
theorem B3757031 : Blo 1668034 3757031 := bstep (se 1 (by rfl) ⟨2817773, by rfl⟩ : syracuseStep 3757031 = 5635547) B5635547
theorem B8451215 : Blo 1668034 8451215 := bstep (se 1 (by rfl) ⟨6338411, by rfl⟩ : syracuseStep 8451215 = 12676823) B12676823
theorem B5633171 : Blo 1668034 5633171 := bstep (se 1 (by rfl) ⟨4224878, by rfl⟩ : syracuseStep 5633171 = 8449757) B8449757
theorem B2815195 : Blo 1668034 2815195 := bstep (se 1 (by rfl) ⟨2111396, by rfl⟩ : syracuseStep 2815195 = 4222793) B4222793
theorem B2503913 : Blo 1668034 2503913 := bstep (se 2 (by rfl) ⟨938967, by rfl⟩ : syracuseStep 2503913 = 1877935) B1877935
theorem B16258295 : Blo 1668034 16258295 := bstep (se 1 (by rfl) ⟨12193721, by rfl⟩ : syracuseStep 16258295 = 24387443) B24387443
theorem B28505357 : Blo 1668034 28505357 := bstep (se 3 (by rfl) ⟨5344754, by rfl⟩ : syracuseStep 28505357 = 10689509) B10689509
theorem B1668383 : Blo 1668034 1668383 := bstep (se 1 (by rfl) ⟨1251287, by rfl⟩ : syracuseStep 1668383 = 2502575) B2502575
theorem B2503967 : Blo 1668034 2503967 := bstep (se 1 (by rfl) ⟨1877975, by rfl⟩ : syracuseStep 2503967 = 3755951) B3755951
theorem B6337835 : Blo 1668034 6337835 := bstep (se 1 (by rfl) ⟨4753376, by rfl⟩ : syracuseStep 6337835 = 9506753) B9506753
theorem B1668443 : Blo 1668034 1668443 := bstep (se 1 (by rfl) ⟨1251332, by rfl⟩ : syracuseStep 1668443 = 2502665) B2502665
theorem B3757409 : Blo 1668034 3757409 := bstep (se 2 (by rfl) ⟨1409028, by rfl⟩ : syracuseStep 3757409 = 2818057) B2818057
theorem B1668463 : Blo 1668034 1668463 := bstep (se 1 (by rfl) ⟨1251347, by rfl⟩ : syracuseStep 1668463 = 2502695) B2502695
theorem B4011403 : Blo 1668034 4011403 := bstep (se 1 (by rfl) ⟨3008552, by rfl⟩ : syracuseStep 4011403 = 6017105) B6017105
theorem B5633441 : Blo 1668034 5633441 := bstep (se 2 (by rfl) ⟨2112540, by rfl⟩ : syracuseStep 5633441 = 4225081) B4225081
theorem B1668519 : Blo 1668034 1668519 := bstep (se 1 (by rfl) ⟨1251389, by rfl⟩ : syracuseStep 1668519 = 2502779) B2502779
theorem B3757499 : Blo 1668034 3757499 := bstep (se 1 (by rfl) ⟨2818124, by rfl⟩ : syracuseStep 3757499 = 5636249) B5636249
theorem B3167687 : Blo 1668034 3167687 := bstep (se 1 (by rfl) ⟨2375765, by rfl⟩ : syracuseStep 3167687 = 4751531) B4751531
theorem B2504135 : Blo 1668034 2504135 := bstep (se 1 (by rfl) ⟨1878101, by rfl⟩ : syracuseStep 2504135 = 3756203) B3756203
theorem B1668603 : Blo 1668034 1668603 := bstep (se 1 (by rfl) ⟨1251452, by rfl⟩ : syracuseStep 1668603 = 2502905) B2502905
theorem B6018617 : Blo 1668034 6018617 := bstep (se 2 (by rfl) ⟨2256981, by rfl⟩ : syracuseStep 6018617 = 4513963) B4513963
theorem B1668671 : Blo 1668034 1668671 := bstep (se 1 (by rfl) ⟨1251503, by rfl⟩ : syracuseStep 1668671 = 2503007) B2503007
theorem B1668679 : Blo 1668034 1668679 := bstep (se 1 (by rfl) ⟨1251509, by rfl⟩ : syracuseStep 1668679 = 2503019) B2503019
theorem B4224595 : Blo 1668034 4224595 := bstep (se 1 (by rfl) ⟨3168446, by rfl⟩ : syracuseStep 4224595 = 6336893) B6336893
theorem B8566361 : Blo 1668034 8566361 := bstep (se 2 (by rfl) ⟨3212385, by rfl⟩ : syracuseStep 8566361 = 6424771) B6424771
theorem B3167839 : Blo 1668034 3167839 := bstep (se 1 (by rfl) ⟨2375879, by rfl⟩ : syracuseStep 3167839 = 4751759) B4751759
theorem B1668831 : Blo 1668034 1668831 := bstep (se 1 (by rfl) ⟨1251623, by rfl⟩ : syracuseStep 1668831 = 2503247) B2503247
theorem B2504489 : Blo 1668034 2504489 := bstep (se 2 (by rfl) ⟨939183, by rfl⟩ : syracuseStep 2504489 = 1878367) B1878367
theorem B1668911 : Blo 1668034 1668911 := bstep (se 1 (by rfl) ⟨1251683, by rfl⟩ : syracuseStep 1668911 = 2503367) B2503367
theorem B2504495 : Blo 1668034 2504495 := bstep (se 1 (by rfl) ⟨1878371, by rfl⟩ : syracuseStep 2504495 = 3756743) B3756743
theorem B10696535 : Blo 1668034 10696535 := bstep (se 1 (by rfl) ⟨8022401, by rfl⟩ : syracuseStep 10696535 = 16044803) B16044803
theorem B1669019 : Blo 1668034 1669019 := bstep (se 1 (by rfl) ⟨1251764, by rfl⟩ : syracuseStep 1669019 = 2503529) B2503529
theorem B2815951 : Blo 1668034 2815951 := bstep (se 1 (by rfl) ⟨2111963, by rfl⟩ : syracuseStep 2815951 = 4223927) B4223927
theorem B1669071 : Blo 1668034 1669071 := bstep (se 1 (by rfl) ⟨1251803, by rfl⟩ : syracuseStep 1669071 = 2503607) B2503607
theorem B1669095 : Blo 1668034 1669095 := bstep (se 1 (by rfl) ⟨1251821, by rfl⟩ : syracuseStep 1669095 = 2503643) B2503643
theorem B24401999 : Blo 1668034 24401999 := bstep (se 1 (by rfl) ⟨18301499, by rfl⟩ : syracuseStep 24401999 = 36602999) B36602999
theorem B8452349 : Blo 1668034 8452349 := bstep (se 3 (by rfl) ⟨1584815, by rfl⟩ : syracuseStep 8452349 = 3169631) B3169631
theorem B2504969 : Blo 1668034 2504969 := bstep (se 2 (by rfl) ⟨939363, by rfl⟩ : syracuseStep 2504969 = 1878727) B1878727
theorem B72194327 : Blo 1668034 72194327 := bstep (se 1 (by rfl) ⟨54145745, by rfl⟩ : syracuseStep 72194327 = 108291491) B108291491
theorem B1669407 : Blo 1668034 1669407 := bstep (se 1 (by rfl) ⟨1252055, by rfl⟩ : syracuseStep 1669407 = 2504111) B2504111
theorem B1669467 : Blo 1668034 1669467 := bstep (se 1 (by rfl) ⟨1252100, by rfl⟩ : syracuseStep 1669467 = 2504201) B2504201
theorem B1669487 : Blo 1668034 1669487 := bstep (se 1 (by rfl) ⟨1252115, by rfl⟩ : syracuseStep 1669487 = 2504231) B2504231
theorem B1669543 : Blo 1668034 1669543 := bstep (se 1 (by rfl) ⟨1252157, by rfl⟩ : syracuseStep 1669543 = 2504315) B2504315
theorem B1669627 : Blo 1668034 1669627 := bstep (se 1 (by rfl) ⟨1252220, by rfl⟩ : syracuseStep 1669627 = 2504441) B2504441
theorem B1669695 : Blo 1668034 1669695 := bstep (se 1 (by rfl) ⟨1252271, by rfl⟩ : syracuseStep 1669695 = 2504543) B2504543
theorem B1669703 : Blo 1668034 1669703 := bstep (se 1 (by rfl) ⟨1252277, by rfl⟩ : syracuseStep 1669703 = 2504555) B2504555
theorem B2112095 : Blo 1668034 2112095 := bstep (se 1 (by rfl) ⟨1584071, by rfl⟩ : syracuseStep 2112095 = 3168143) B3168143
theorem B2816633 : Blo 1668034 2816633 := bstep (se 2 (by rfl) ⟨1056237, by rfl⟩ : syracuseStep 2816633 = 2112475) B2112475
theorem B2816687 : Blo 1668034 2816687 := bstep (se 1 (by rfl) ⟨2112515, by rfl⟩ : syracuseStep 2816687 = 4225031) B4225031
theorem B1669855 : Blo 1668034 1669855 := bstep (se 1 (by rfl) ⟨1252391, by rfl⟩ : syracuseStep 1669855 = 2504783) B2504783
theorem B9632531 : Blo 1668034 9632531 := bstep (se 1 (by rfl) ⟨7224398, by rfl⟩ : syracuseStep 9632531 = 14448797) B14448797
theorem B1669935 : Blo 1668034 1669935 := bstep (se 1 (by rfl) ⟨1252451, by rfl⟩ : syracuseStep 1669935 = 2504903) B2504903
theorem B4225871 : Blo 1668034 4225871 := bstep (se 1 (by rfl) ⟨3169403, by rfl⟩ : syracuseStep 4225871 = 6338807) B6338807
theorem B2816923 : Blo 1668034 2816923 := bstep (se 1 (by rfl) ⟨2112692, by rfl⟩ : syracuseStep 2816923 = 4225385) B4225385
theorem B8453159 : Blo 1668034 8453159 := bstep (se 1 (by rfl) ⟨6339869, by rfl⟩ : syracuseStep 8453159 = 12679739) B12679739
theorem B16252093 : Blo 1668034 16252093 := bstep (se 3 (by rfl) ⟨3047267, by rfl⟩ : syracuseStep 16252093 = 6094535) B6094535
theorem B2112799 : Blo 1668034 2112799 := bstep (se 1 (by rfl) ⟨1584599, by rfl⟩ : syracuseStep 2112799 = 3169199) B3169199
theorem B3382651 : Blo 1668034 3382651 := bstep (se 1 (by rfl) ⟨2536988, by rfl⟩ : syracuseStep 3382651 = 5073977) B5073977
theorem B6339977 : Blo 1668034 6339977 := bstep (se 2 (by rfl) ⟨2377491, by rfl⟩ : syracuseStep 6339977 = 4754983) B4754983
theorem B14261669 : Blo 1668034 14261669 := bstep (se 4 (by rfl) ⟨1337031, by rfl⟩ : syracuseStep 14261669 = 2674063) B2674063
theorem B8445383 : Blo 1668034 8445383 := bstep (se 1 (by rfl) ⟨6334037, by rfl⟩ : syracuseStep 8445383 = 12668075) B12668075
theorem B4226519 : Blo 1668034 4226519 := bstep (se 1 (by rfl) ⟨3169889, by rfl⟩ : syracuseStep 4226519 = 6339779) B6339779
theorem B9027233 : Blo 1668034 9027233 := bstep (se 2 (by rfl) ⟨3385212, by rfl⟩ : syracuseStep 9027233 = 6770425) B6770425
theorem B8445707 : Blo 1668034 8445707 := bstep (se 1 (by rfl) ⟨6334280, by rfl⟩ : syracuseStep 8445707 = 12668561) B12668561
theorem B9019147 : Blo 1668034 9019147 := bstep (se 1 (by rfl) ⟨6764360, by rfl⟩ : syracuseStep 9019147 = 13528721) B13528721
theorem B4226863 : Blo 1668034 4226863 := bstep (se 1 (by rfl) ⟨3170147, by rfl⟩ : syracuseStep 4226863 = 6340295) B6340295
theorem B22847339 : Blo 1668034 22847339 := bstep (se 1 (by rfl) ⟨17135504, by rfl⟩ : syracuseStep 22847339 = 34271009) B34271009
theorem B6422429 : Blo 1668034 6422429 := bstep (se 3 (by rfl) ⟨1204205, by rfl⟩ : syracuseStep 6422429 = 2408411) B2408411
theorem B40607669 : Blo 1668034 40607669 := bstep (se 5 (by rfl) ⟨1903484, by rfl⟩ : syracuseStep 40607669 = 3806969) B3806969
theorem B4284647 : Blo 1668034 4284647 := bstep (se 1 (by rfl) ⟨3213485, by rfl⟩ : syracuseStep 4284647 = 6426971) B6426971
theorem B64127213 : Blo 1668034 64127213 := bstep (se 3 (by rfl) ⟨12023852, by rfl⟩ : syracuseStep 64127213 = 24047705) B24047705
theorem B4751713 : Blo 1668034 4751713 := bstep (se 2 (by rfl) ⟨1781892, by rfl⟩ : syracuseStep 4751713 = 3563785) B3563785
theorem B7610743 : Blo 1668034 7610743 := bstep (se 1 (by rfl) ⟨5708057, by rfl⟩ : syracuseStep 7610743 = 11416115) B11416115
theorem B24379955 : Blo 1668034 24379955 := bstep (se 1 (by rfl) ⟨18284966, by rfl⟩ : syracuseStep 24379955 = 36569933) B36569933
theorem B10838681 : Blo 1668034 10838681 := bstep (se 2 (by rfl) ⟨4064505, by rfl⟩ : syracuseStep 10838681 = 8129011) B8129011
theorem B13910723 : Blo 1668034 13910723 := bstep (se 1 (by rfl) ⟨10433042, by rfl⟩ : syracuseStep 13910723 = 20866085) B20866085
theorem B10838863 : Blo 1668034 10838863 := bstep (se 1 (by rfl) ⟨8129147, by rfl⟩ : syracuseStep 10838863 = 16258295) B16258295
theorem B4752283 : Blo 1668034 4752283 := bstep (se 1 (by rfl) ⟨3564212, by rfl⟩ : syracuseStep 4752283 = 7128425) B7128425
theorem B273957835 : Blo 1668034 273957835 := bstep (se 1 (by rfl) ⟨205468376, by rfl⟩ : syracuseStep 273957835 = 410936753) B410936753
theorem B5710907 : Blo 1668034 5710907 := bstep (se 1 (by rfl) ⟨4283180, by rfl⟩ : syracuseStep 5710907 = 8566361) B8566361
theorem B8447165 : Blo 1668034 8447165 := bstep (se 3 (by rfl) ⟨1583843, by rfl⟩ : syracuseStep 8447165 = 3167687) B3167687
theorem B3753323 : Blo 1668034 3753323 := bstep (se 1 (by rfl) ⟨2814992, by rfl⟩ : syracuseStep 3753323 = 5629985) B5629985
theorem B10700171 : Blo 1668034 10700171 := bstep (se 1 (by rfl) ⟨8025128, by rfl⟩ : syracuseStep 10700171 = 16050257) B16050257
theorem B48129551 : Blo 1668034 48129551 := bstep (se 1 (by rfl) ⟨36097163, by rfl⟩ : syracuseStep 48129551 = 72194327) B72194327
theorem B21669457 : Blo 1668034 21669457 := bstep (se 2 (by rfl) ⟨8126046, by rfl⟩ : syracuseStep 21669457 = 16252093) B16252093
theorem B3753593 : Blo 1668034 3753593 := bstep (se 2 (by rfl) ⟨1407597, by rfl⟩ : syracuseStep 3753593 = 2815195) B2815195
theorem B1877755 : Blo 1668034 1877755 := bstep (se 1 (by rfl) ⟨1408316, by rfl⟩ : syracuseStep 1877755 = 2816633) B2816633
theorem B1877791 : Blo 1668034 1877791 := bstep (se 1 (by rfl) ⟨1408343, by rfl⟩ : syracuseStep 1877791 = 2816687) B2816687
theorem B18040805 : Blo 1668034 18040805 := bstep (se 4 (by rfl) ⟨1691325, by rfl⟩ : syracuseStep 18040805 = 3382651) B3382651
theorem B4753399 : Blo 1668034 4753399 := bstep (se 1 (by rfl) ⟨3565049, by rfl⟩ : syracuseStep 4753399 = 7130099) B7130099
theorem B5630201 : Blo 1668034 5630201 := bstep (se 2 (by rfl) ⟨2111325, by rfl⟩ : syracuseStep 5630201 = 4222651) B4222651
theorem B5630255 : Blo 1668034 5630255 := bstep (se 1 (by rfl) ⟨4222691, by rfl⟩ : syracuseStep 5630255 = 8445383) B8445383
theorem B5630471 : Blo 1668034 5630471 := bstep (se 1 (by rfl) ⟨4222853, by rfl⟩ : syracuseStep 5630471 = 8445707) B8445707
theorem B4753991 : Blo 1668034 4753991 := bstep (se 1 (by rfl) ⟨3565493, by rfl⟩ : syracuseStep 4753991 = 7130987) B7130987
theorem B15231559 : Blo 1668034 15231559 := bstep (se 1 (by rfl) ⟨11423669, by rfl⟩ : syracuseStep 15231559 = 22847339) B22847339
theorem B3754601 : Blo 1668034 3754601 := bstep (se 2 (by rfl) ⟨1407975, by rfl⟩ : syracuseStep 3754601 = 2815951) B2815951
theorem B65071997 : Blo 1668034 65071997 := bstep (se 3 (by rfl) ⟨12200999, by rfl⟩ : syracuseStep 65071997 = 24401999) B24401999
theorem B2853839 : Blo 1668034 2853839 := bstep (se 1 (by rfl) ⟨2140379, by rfl⟩ : syracuseStep 2853839 = 4280759) B4280759
theorem B5344231 : Blo 1668034 5344231 := bstep (se 1 (by rfl) ⟨4008173, by rfl⟩ : syracuseStep 5344231 = 8016347) B8016347
theorem B60935287 : Blo 1668034 60935287 := bstep (se 1 (by rfl) ⟨45701465, by rfl⟩ : syracuseStep 60935287 = 91402931) B91402931
theorem B5631119 : Blo 1668034 5631119 := bstep (se 1 (by rfl) ⟨4223339, by rfl⟩ : syracuseStep 5631119 = 8446679) B8446679
theorem B3755231 : Blo 1668034 3755231 := bstep (se 1 (by rfl) ⟨2816423, by rfl⟩ : syracuseStep 3755231 = 5632847) B5632847
theorem B4754675 : Blo 1668034 4754675 := bstep (se 1 (by rfl) ⟨3566006, by rfl⟩ : syracuseStep 4754675 = 7132013) B7132013
theorem B4754857 : Blo 1668034 4754857 := bstep (se 2 (by rfl) ⟨1783071, by rfl⟩ : syracuseStep 4754857 = 3566143) B3566143
theorem B3755447 : Blo 1668034 3755447 := bstep (se 1 (by rfl) ⟨2816585, by rfl⟩ : syracuseStep 3755447 = 5633171) B5633171
theorem B2502119 : Blo 1668034 2502119 := bstep (se 1 (by rfl) ⟨1876589, by rfl⟩ : syracuseStep 2502119 = 3753179) B3753179
theorem B5631551 : Blo 1668034 5631551 := bstep (se 1 (by rfl) ⟨4223663, by rfl⟩ : syracuseStep 5631551 = 8447327) B8447327
theorem B4755017 : Blo 1668034 4755017 := bstep (se 2 (by rfl) ⟨1783131, by rfl⟩ : syracuseStep 4755017 = 3566263) B3566263
theorem B2502251 : Blo 1668034 2502251 := bstep (se 1 (by rfl) ⟨1876688, by rfl⟩ : syracuseStep 2502251 = 3753377) B3753377
theorem B3755627 : Blo 1668034 3755627 := bstep (se 1 (by rfl) ⟨2816720, by rfl⟩ : syracuseStep 3755627 = 5633441) B5633441
theorem B5074607 : Blo 1668034 5074607 := bstep (se 1 (by rfl) ⟨3805955, by rfl⟩ : syracuseStep 5074607 = 7611911) B7611911
theorem B2502377 : Blo 1668034 2502377 := bstep (se 2 (by rfl) ⟨938391, by rfl⟩ : syracuseStep 2502377 = 1876783) B1876783
theorem B2502521 : Blo 1668034 2502521 := bstep (se 2 (by rfl) ⟨938445, by rfl⟩ : syracuseStep 2502521 = 1876891) B1876891
theorem B3755897 : Blo 1668034 3755897 := bstep (se 2 (by rfl) ⟨1408461, by rfl⟩ : syracuseStep 3755897 = 2816923) B2816923
theorem B7131023 : Blo 1668034 7131023 := bstep (se 1 (by rfl) ⟨5348267, by rfl⟩ : syracuseStep 7131023 = 10696535) B10696535
theorem B2502623 : Blo 1668034 2502623 := bstep (se 1 (by rfl) ⟨1876967, by rfl⟩ : syracuseStep 2502623 = 3753935) B3753935
theorem B8450243 : Blo 1668034 8450243 := bstep (se 1 (by rfl) ⟨6337682, by rfl⟩ : syracuseStep 8450243 = 12675365) B12675365
theorem B2502875 : Blo 1668034 2502875 := bstep (se 1 (by rfl) ⟨1877156, by rfl⟩ : syracuseStep 2502875 = 3754313) B3754313
theorem B2502887 : Blo 1668034 2502887 := bstep (se 1 (by rfl) ⟨1877165, by rfl⟩ : syracuseStep 2502887 = 3754331) B3754331
theorem B5632253 : Blo 1668034 5632253 := bstep (se 3 (by rfl) ⟨1056047, by rfl⟩ : syracuseStep 5632253 = 2112095) B2112095
theorem B14266691 : Blo 1668034 14266691 := bstep (se 1 (by rfl) ⟨10700018, by rfl⟩ : syracuseStep 14266691 = 21400037) B21400037
theorem B2503049 : Blo 1668034 2503049 := bstep (se 2 (by rfl) ⟨938643, by rfl⟩ : syracuseStep 2503049 = 1877287) B1877287
theorem B2503145 : Blo 1668034 2503145 := bstep (se 2 (by rfl) ⟨938679, by rfl⟩ : syracuseStep 2503145 = 1877359) B1877359
theorem B4010489 : Blo 1668034 4010489 := bstep (se 2 (by rfl) ⟨1503933, by rfl⟩ : syracuseStep 4010489 = 3007867) B3007867
theorem B2503271 : Blo 1668034 2503271 := bstep (se 1 (by rfl) ⟨1877453, by rfl⟩ : syracuseStep 2503271 = 3754907) B3754907
theorem B10842839 : Blo 1668034 10842839 := bstep (se 1 (by rfl) ⟨8132129, by rfl⟩ : syracuseStep 10842839 = 16264259) B16264259
theorem B2503403 : Blo 1668034 2503403 := bstep (se 1 (by rfl) ⟨1877552, by rfl⟩ : syracuseStep 2503403 = 3755105) B3755105
theorem B2503433 : Blo 1668034 2503433 := bstep (se 2 (by rfl) ⟨938787, by rfl⟩ : syracuseStep 2503433 = 1877575) B1877575
theorem B5632793 : Blo 1668034 5632793 := bstep (se 2 (by rfl) ⟨2112297, by rfl⟩ : syracuseStep 5632793 = 4224595) B4224595
theorem B4223785 : Blo 1668034 4223785 := bstep (se 2 (by rfl) ⟨1583919, by rfl⟩ : syracuseStep 4223785 = 3167839) B3167839
theorem B2503535 : Blo 1668034 2503535 := bstep (se 1 (by rfl) ⟨1877651, by rfl⟩ : syracuseStep 2503535 = 3755303) B3755303
theorem B9507779 : Blo 1668034 9507779 := bstep (se 1 (by rfl) ⟨7130834, by rfl⟩ : syracuseStep 9507779 = 14261669) B14261669
theorem B1668091 : Blo 1668034 1668091 := bstep (se 1 (by rfl) ⟨1251068, by rfl⟩ : syracuseStep 1668091 = 2502137) B2502137
theorem B5633063 : Blo 1668034 5633063 := bstep (se 1 (by rfl) ⟨4224797, by rfl⟩ : syracuseStep 5633063 = 8449595) B8449595
theorem B1668159 : Blo 1668034 1668159 := bstep (se 1 (by rfl) ⟨1251119, by rfl⟩ : syracuseStep 1668159 = 2502239) B2502239
theorem B2503787 : Blo 1668034 2503787 := bstep (se 1 (by rfl) ⟨1877840, by rfl⟩ : syracuseStep 2503787 = 3755681) B3755681
theorem B6018155 : Blo 1668034 6018155 := bstep (se 1 (by rfl) ⟨4513616, by rfl⟩ : syracuseStep 6018155 = 9027233) B9027233
theorem B1668303 : Blo 1668034 1668303 := bstep (se 1 (by rfl) ⟨1251227, by rfl⟩ : syracuseStep 1668303 = 2502455) B2502455
theorem B4281619 : Blo 1668034 4281619 := bstep (se 1 (by rfl) ⟨3211214, by rfl⟩ : syracuseStep 4281619 = 6422429) B6422429
theorem B27071779 : Blo 1668034 27071779 := bstep (se 1 (by rfl) ⟨20303834, by rfl⟩ : syracuseStep 27071779 = 40607669) B40607669
theorem B2504027 : Blo 1668034 2504027 := bstep (se 1 (by rfl) ⟨1878020, by rfl⟩ : syracuseStep 2504027 = 3756041) B3756041
theorem B1668507 : Blo 1668034 1668507 := bstep (se 1 (by rfl) ⟨1251380, by rfl⟩ : syracuseStep 1668507 = 2502761) B2502761
theorem B82286117 : Blo 1668034 82286117 := bstep (se 4 (by rfl) ⟨7714323, by rfl⟩ : syracuseStep 82286117 = 15428647) B15428647
theorem B4511303 : Blo 1668034 4511303 := bstep (se 1 (by rfl) ⟨3383477, by rfl⟩ : syracuseStep 4511303 = 6766955) B6766955
theorem B1668719 : Blo 1668034 1668719 := bstep (se 1 (by rfl) ⟨1251539, by rfl⟩ : syracuseStep 1668719 = 2503079) B2503079
theorem B2504303 : Blo 1668034 2504303 := bstep (se 1 (by rfl) ⟨1878227, by rfl⟩ : syracuseStep 2504303 = 3756455) B3756455
theorem B1668775 : Blo 1668034 1668775 := bstep (se 1 (by rfl) ⟨1251581, by rfl⟩ : syracuseStep 1668775 = 2503163) B2503163
theorem B2504375 : Blo 1668034 2504375 := bstep (se 1 (by rfl) ⟨1878281, by rfl⟩ : syracuseStep 2504375 = 3756563) B3756563
theorem B2504411 : Blo 1668034 2504411 := bstep (se 1 (by rfl) ⟨1878308, by rfl⟩ : syracuseStep 2504411 = 3756617) B3756617
theorem B1668859 : Blo 1668034 1668859 := bstep (se 1 (by rfl) ⟨1251644, by rfl⟩ : syracuseStep 1668859 = 2503289) B2503289
theorem B1668895 : Blo 1668034 1668895 := bstep (se 1 (by rfl) ⟨1251671, by rfl⟩ : syracuseStep 1668895 = 2503343) B2503343
theorem B6338351 : Blo 1668034 6338351 := bstep (se 1 (by rfl) ⟨4753763, by rfl⟩ : syracuseStep 6338351 = 9507527) B9507527
theorem B1668927 : Blo 1668034 1668927 := bstep (se 1 (by rfl) ⟨1251695, by rfl⟩ : syracuseStep 1668927 = 2503391) B2503391
theorem B2815823 : Blo 1668034 2815823 := bstep (se 1 (by rfl) ⟨2111867, by rfl⟩ : syracuseStep 2815823 = 4223735) B4223735
theorem B2537353 : Blo 1668034 2537353 := bstep (se 2 (by rfl) ⟨951507, by rfl⟩ : syracuseStep 2537353 = 1903015) B1903015
theorem B2504585 : Blo 1668034 2504585 := bstep (se 2 (by rfl) ⟨939219, by rfl⟩ : syracuseStep 2504585 = 1878439) B1878439
theorem B5707759 : Blo 1668034 5707759 := bstep (se 1 (by rfl) ⟨4280819, by rfl⟩ : syracuseStep 5707759 = 8561639) B8561639
theorem B1669103 : Blo 1668034 1669103 := bstep (se 1 (by rfl) ⟨1251827, by rfl⟩ : syracuseStep 1669103 = 2503655) B2503655
theorem B2504687 : Blo 1668034 2504687 := bstep (se 1 (by rfl) ⟨1878515, by rfl⟩ : syracuseStep 2504687 = 3757031) B3757031
theorem B10688537 : Blo 1668034 10688537 := bstep (se 2 (by rfl) ⟨4008201, by rfl⟩ : syracuseStep 10688537 = 8016403) B8016403
theorem B5634143 : Blo 1668034 5634143 := bstep (se 1 (by rfl) ⟨4225607, by rfl⟩ : syracuseStep 5634143 = 8451215) B8451215
theorem B1669275 : Blo 1668034 1669275 := bstep (se 1 (by rfl) ⟨1251956, by rfl⟩ : syracuseStep 1669275 = 2503913) B2503913
theorem B19003571 : Blo 1668034 19003571 := bstep (se 1 (by rfl) ⟨14252678, by rfl⟩ : syracuseStep 19003571 = 28505357) B28505357
theorem B1669311 : Blo 1668034 1669311 := bstep (se 1 (by rfl) ⟨1251983, by rfl⟩ : syracuseStep 1669311 = 2503967) B2503967
theorem B4225223 : Blo 1668034 4225223 := bstep (se 1 (by rfl) ⟨3168917, by rfl⟩ : syracuseStep 4225223 = 6337835) B6337835
theorem B2504939 : Blo 1668034 2504939 := bstep (se 1 (by rfl) ⟨1878704, by rfl⟩ : syracuseStep 2504939 = 3757409) B3757409
theorem B2504999 : Blo 1668034 2504999 := bstep (se 1 (by rfl) ⟨1878749, by rfl⟩ : syracuseStep 2504999 = 3757499) B3757499
theorem B3168553 : Blo 1668034 3168553 := bstep (se 2 (by rfl) ⟨1188207, by rfl⟩ : syracuseStep 3168553 = 2376415) B2376415
theorem B5347625 : Blo 1668034 5347625 := bstep (se 2 (by rfl) ⟨2005359, by rfl⟩ : syracuseStep 5347625 = 4010719) B4010719
theorem B1669423 : Blo 1668034 1669423 := bstep (se 1 (by rfl) ⟨1252067, by rfl⟩ : syracuseStep 1669423 = 2504135) B2504135
theorem B4012411 : Blo 1668034 4012411 := bstep (se 1 (by rfl) ⟨3009308, by rfl⟩ : syracuseStep 4012411 = 6018617) B6018617
theorem B1669659 : Blo 1668034 1669659 := bstep (se 1 (by rfl) ⟨1252244, by rfl⟩ : syracuseStep 1669659 = 2504489) B2504489
theorem B1669663 : Blo 1668034 1669663 := bstep (se 1 (by rfl) ⟨1252247, by rfl⟩ : syracuseStep 1669663 = 2504495) B2504495
theorem B8444573 : Blo 1668034 8444573 := bstep (se 3 (by rfl) ⟨1583357, by rfl⟩ : syracuseStep 8444573 = 3166715) B3166715
theorem B64166579 : Blo 1668034 64166579 := bstep (se 1 (by rfl) ⟨48124934, by rfl⟩ : syracuseStep 64166579 = 96249869) B96249869
theorem B5634899 : Blo 1668034 5634899 := bstep (se 1 (by rfl) ⟨4226174, by rfl⟩ : syracuseStep 5634899 = 8452349) B8452349
theorem B3169115 : Blo 1668034 3169115 := bstep (se 1 (by rfl) ⟨2376836, by rfl⟩ : syracuseStep 3169115 = 4753673) B4753673
theorem B1669979 : Blo 1668034 1669979 := bstep (se 1 (by rfl) ⟨1252484, by rfl⟩ : syracuseStep 1669979 = 2504969) B2504969
theorem B8444897 : Blo 1668034 8444897 := bstep (se 2 (by rfl) ⟨3166836, by rfl⟩ : syracuseStep 8444897 = 6333673) B6333673
theorem B2817065 : Blo 1668034 2817065 := bstep (se 2 (by rfl) ⟨1056399, by rfl⟩ : syracuseStep 2817065 = 2112799) B2112799
theorem B2538617 : Blo 1668034 2538617 := bstep (se 2 (by rfl) ⟨951981, by rfl⟩ : syracuseStep 2538617 = 1903963) B1903963
theorem B6012029 : Blo 1668034 6012029 := bstep (se 3 (by rfl) ⟨1127255, by rfl⟩ : syracuseStep 6012029 = 2254511) B2254511
theorem B6421687 : Blo 1668034 6421687 := bstep (se 1 (by rfl) ⟨4816265, by rfl⟩ : syracuseStep 6421687 = 9632531) B9632531
theorem B5348537 : Blo 1668034 5348537 := bstep (se 2 (by rfl) ⟨2005701, by rfl⟩ : syracuseStep 5348537 = 4011403) B4011403
theorem B2817247 : Blo 1668034 2817247 := bstep (se 1 (by rfl) ⟨2112935, by rfl⟩ : syracuseStep 2817247 = 4225871) B4225871
theorem B5635439 : Blo 1668034 5635439 := bstep (se 1 (by rfl) ⟨4226579, by rfl⟩ : syracuseStep 5635439 = 8453159) B8453159
theorem B4226651 : Blo 1668034 4226651 := bstep (se 1 (by rfl) ⟨3169988, by rfl⟩ : syracuseStep 4226651 = 6339977) B6339977
theorem B2817679 : Blo 1668034 2817679 := bstep (se 1 (by rfl) ⟨2113259, by rfl⟩ : syracuseStep 2817679 = 4226519) B4226519
theorem B12025529 : Blo 1668034 12025529 := bstep (se 2 (by rfl) ⟨4509573, by rfl⟩ : syracuseStep 12025529 = 9019147) B9019147
theorem B2375401 : Blo 1668034 2375401 := bstep (se 2 (by rfl) ⟨890775, by rfl⟩ : syracuseStep 2375401 = 1781551) B1781551
theorem B5635817 : Blo 1668034 5635817 := bstep (se 2 (by rfl) ⟨2113431, by rfl⟩ : syracuseStep 5635817 = 4226863) B4226863
theorem B3170171 : Blo 1668034 3170171 := bstep (se 1 (by rfl) ⟨2377628, by rfl⟩ : syracuseStep 3170171 = 4755257) B4755257
theorem B4513661 : Blo 1668034 4513661 := bstep (se 3 (by rfl) ⟨846311, by rfl⟩ : syracuseStep 4513661 = 1692623) B1692623
theorem B6340477 : Blo 1668034 6340477 := bstep (se 3 (by rfl) ⟨1188839, by rfl⟩ : syracuseStep 6340477 = 2377679) B2377679
theorem B9511127 : Blo 1668034 9511127 := bstep (se 1 (by rfl) ⟨7133345, by rfl⟩ : syracuseStep 9511127 = 14266691) B14266691
theorem B16032077 : Blo 1668034 16032077 := bstep (se 3 (by rfl) ⟨3006014, by rfl⟩ : syracuseStep 16032077 = 6012029) B6012029
theorem B16253303 : Blo 1668034 16253303 := bstep (se 1 (by rfl) ⟨12189977, by rfl⟩ : syracuseStep 16253303 = 24379955) B24379955
theorem B7225787 : Blo 1668034 7225787 := bstep (se 1 (by rfl) ⟨5419340, by rfl⟩ : syracuseStep 7225787 = 10838681) B10838681
theorem B9273815 : Blo 1668034 9273815 := bstep (se 1 (by rfl) ⟨6955361, by rfl⟩ : syracuseStep 9273815 = 13910723) B13910723
theorem B5349881 : Blo 1668034 5349881 := bstep (se 2 (by rfl) ⟨2006205, by rfl⟩ : syracuseStep 5349881 = 4012411) B4012411
theorem B20308745 : Blo 1668034 20308745 := bstep (se 2 (by rfl) ⟨7615779, by rfl⟩ : syracuseStep 20308745 = 15231559) B15231559
theorem B3007535 : Blo 1668034 3007535 := bstep (se 1 (by rfl) ⟨2255651, by rfl⟩ : syracuseStep 3007535 = 4511303) B4511303
theorem B14451817 : Blo 1668034 14451817 := bstep (se 2 (by rfl) ⟨5419431, by rfl⟩ : syracuseStep 14451817 = 10838863) B10838863
theorem B1877215 : Blo 1668034 1877215 := bstep (se 1 (by rfl) ⟨1407911, by rfl⟩ : syracuseStep 1877215 = 2815823) B2815823
theorem B12027203 : Blo 1668034 12027203 := bstep (se 1 (by rfl) ⟨9020402, by rfl⟩ : syracuseStep 12027203 = 18040805) B18040805
theorem B3753467 : Blo 1668034 3753467 := bstep (se 1 (by rfl) ⟨2815100, by rfl⟩ : syracuseStep 3753467 = 5630201) B5630201
theorem B3753503 : Blo 1668034 3753503 := bstep (se 1 (by rfl) ⟨2815127, by rfl⟩ : syracuseStep 3753503 = 5630255) B5630255
theorem B3753647 : Blo 1668034 3753647 := bstep (se 1 (by rfl) ⟨2815235, by rfl⟩ : syracuseStep 3753647 = 5630471) B5630471
theorem B36095705 : Blo 1668034 36095705 := bstep (se 2 (by rfl) ⟨13535889, by rfl⟩ : syracuseStep 36095705 = 27071779) B27071779
theorem B5629715 : Blo 1668034 5629715 := bstep (se 1 (by rfl) ⟨4222286, by rfl⟩ : syracuseStep 5629715 = 8444573) B8444573
theorem B5629931 : Blo 1668034 5629931 := bstep (se 1 (by rfl) ⟨4222448, by rfl⟩ : syracuseStep 5629931 = 8444897) B8444897
theorem B1878043 : Blo 1668034 1878043 := bstep (se 1 (by rfl) ⟨1408532, by rfl⟩ : syracuseStep 1878043 = 2817065) B2817065
theorem B3754079 : Blo 1668034 3754079 := bstep (se 1 (by rfl) ⟨2815559, by rfl⟩ : syracuseStep 3754079 = 5631119) B5631119
theorem B3565691 : Blo 1668034 3565691 := bstep (se 1 (by rfl) ⟨2674268, by rfl⟩ : syracuseStep 3565691 = 5348537) B5348537
theorem B3754367 : Blo 1668034 3754367 := bstep (se 1 (by rfl) ⟨2815775, by rfl⟩ : syracuseStep 3754367 = 5631551) B5631551
theorem B3009107 : Blo 1668034 3009107 := bstep (se 1 (by rfl) ⟨2256830, by rfl⟩ : syracuseStep 3009107 = 4513661) B4513661
theorem B4754015 : Blo 1668034 4754015 := bstep (se 1 (by rfl) ⟨3565511, by rfl⟩ : syracuseStep 4754015 = 7131023) B7131023
theorem B3754835 : Blo 1668034 3754835 := bstep (se 1 (by rfl) ⟨2816126, by rfl⟩ : syracuseStep 3754835 = 5632253) B5632253
theorem B6769645 : Blo 1668034 6769645 := bstep (se 3 (by rfl) ⟨1269308, by rfl⟩ : syracuseStep 6769645 = 2538617) B2538617
theorem B2673659 : Blo 1668034 2673659 := bstep (se 1 (by rfl) ⟨2005244, by rfl⟩ : syracuseStep 2673659 = 4010489) B4010489
theorem B6335617 : Blo 1668034 6335617 := bstep (se 2 (by rfl) ⟨2375856, by rfl⟩ : syracuseStep 6335617 = 4751713) B4751713
theorem B7228559 : Blo 1668034 7228559 := bstep (se 1 (by rfl) ⟨5421419, by rfl⟩ : syracuseStep 7228559 = 10842839) B10842839
theorem B3755195 : Blo 1668034 3755195 := bstep (se 1 (by rfl) ⟨2816396, by rfl⟩ : syracuseStep 3755195 = 5632793) B5632793
theorem B3755375 : Blo 1668034 3755375 := bstep (se 1 (by rfl) ⟨2816531, by rfl⟩ : syracuseStep 3755375 = 5633063) B5633063
theorem B5631443 : Blo 1668034 5631443 := bstep (se 1 (by rfl) ⟨4223582, by rfl⟩ : syracuseStep 5631443 = 8447165) B8447165
theorem B2502215 : Blo 1668034 2502215 := bstep (se 1 (by rfl) ⟨1876661, by rfl⟩ : syracuseStep 2502215 = 3753323) B3753323
theorem B54857411 : Blo 1668034 54857411 := bstep (se 1 (by rfl) ⟨41143058, by rfl⟩ : syracuseStep 54857411 = 82286117) B82286117
theorem B5631713 : Blo 1668034 5631713 := bstep (se 2 (by rfl) ⟨2111892, by rfl⟩ : syracuseStep 5631713 = 4223785) B4223785
theorem B2502395 : Blo 1668034 2502395 := bstep (se 1 (by rfl) ⟨1876796, by rfl⟩ : syracuseStep 2502395 = 3753593) B3753593
theorem B6336377 : Blo 1668034 6336377 := bstep (se 2 (by rfl) ⟨2376141, by rfl⟩ : syracuseStep 6336377 = 4752283) B4752283
theorem B365277113 : Blo 1668034 365277113 := bstep (se 2 (by rfl) ⟨136978917, by rfl⟩ : syracuseStep 365277113 = 273957835) B273957835
theorem B3756095 : Blo 1668034 3756095 := bstep (se 1 (by rfl) ⟨2817071, by rfl⟩ : syracuseStep 3756095 = 5634143) B5634143
theorem B12669047 : Blo 1668034 12669047 := bstep (se 1 (by rfl) ⟨9501785, by rfl⟩ : syracuseStep 12669047 = 19003571) B19003571
theorem B12677309 : Blo 1668034 12677309 := bstep (se 3 (by rfl) ⟨2376995, by rfl⟩ : syracuseStep 12677309 = 4753991) B4753991
theorem B3756329 : Blo 1668034 3756329 := bstep (se 2 (by rfl) ⟨1408623, by rfl⟩ : syracuseStep 3756329 = 2817247) B2817247
theorem B2503067 : Blo 1668034 2503067 := bstep (se 1 (by rfl) ⟨1877300, by rfl⟩ : syracuseStep 2503067 = 3754601) B3754601
theorem B3756599 : Blo 1668034 3756599 := bstep (se 1 (by rfl) ⟨2817449, by rfl⟩ : syracuseStep 3756599 = 5634899) B5634899
theorem B43381331 : Blo 1668034 43381331 := bstep (se 1 (by rfl) ⟨32535998, by rfl⟩ : syracuseStep 43381331 = 65071997) B65071997
theorem B2503487 : Blo 1668034 2503487 := bstep (se 1 (by rfl) ⟨1877615, by rfl⟩ : syracuseStep 2503487 = 3755231) B3755231
theorem B3756905 : Blo 1668034 3756905 := bstep (se 2 (by rfl) ⟨1408839, by rfl⟩ : syracuseStep 3756905 = 2817679) B2817679
theorem B3756959 : Blo 1668034 3756959 := bstep (se 1 (by rfl) ⟨2817719, by rfl⟩ : syracuseStep 3756959 = 5635439) B5635439
theorem B2503631 : Blo 1668034 2503631 := bstep (se 1 (by rfl) ⟨1877723, by rfl⟩ : syracuseStep 2503631 = 3755447) B3755447
theorem B3167201 : Blo 1668034 3167201 := bstep (se 2 (by rfl) ⟨1187700, by rfl⟩ : syracuseStep 3167201 = 2375401) B2375401
theorem B1668079 : Blo 1668034 1668079 := bstep (se 1 (by rfl) ⟨1251059, by rfl⟩ : syracuseStep 1668079 = 2502119) B2502119
theorem B2503673 : Blo 1668034 2503673 := bstep (se 2 (by rfl) ⟨938877, by rfl⟩ : syracuseStep 2503673 = 1877755) B1877755
theorem B2503721 : Blo 1668034 2503721 := bstep (se 2 (by rfl) ⟨938895, by rfl⟩ : syracuseStep 2503721 = 1877791) B1877791
theorem B1668167 : Blo 1668034 1668167 := bstep (se 1 (by rfl) ⟨1251125, by rfl⟩ : syracuseStep 1668167 = 2502251) B2502251
theorem B2503751 : Blo 1668034 2503751 := bstep (se 1 (by rfl) ⟨1877813, by rfl⟩ : syracuseStep 2503751 = 3755627) B3755627
theorem B8017019 : Blo 1668034 8017019 := bstep (se 1 (by rfl) ⟨6012764, by rfl⟩ : syracuseStep 8017019 = 12025529) B12025529
theorem B1668251 : Blo 1668034 1668251 := bstep (se 1 (by rfl) ⟨1251188, by rfl⟩ : syracuseStep 1668251 = 2502377) B2502377
theorem B3757211 : Blo 1668034 3757211 := bstep (se 1 (by rfl) ⟨2817908, by rfl⟩ : syracuseStep 3757211 = 5635817) B5635817
theorem B1668347 : Blo 1668034 1668347 := bstep (se 1 (by rfl) ⟨1251260, by rfl⟩ : syracuseStep 1668347 = 2502521) B2502521
theorem B2503931 : Blo 1668034 2503931 := bstep (se 1 (by rfl) ⟨1877948, by rfl⟩ : syracuseStep 2503931 = 3755897) B3755897
theorem B1668415 : Blo 1668034 1668415 := bstep (se 1 (by rfl) ⟨1251311, by rfl⟩ : syracuseStep 1668415 = 2502623) B2502623
theorem B6337865 : Blo 1668034 6337865 := bstep (se 2 (by rfl) ⟨2376699, by rfl⟩ : syracuseStep 6337865 = 4753399) B4753399
theorem B5633495 : Blo 1668034 5633495 := bstep (se 1 (by rfl) ⟨4225121, by rfl⟩ : syracuseStep 5633495 = 8450243) B8450243
theorem B1668583 : Blo 1668034 1668583 := bstep (se 1 (by rfl) ⟨1251437, by rfl⟩ : syracuseStep 1668583 = 2502875) B2502875
theorem B1668591 : Blo 1668034 1668591 := bstep (se 1 (by rfl) ⟨1251443, by rfl⟩ : syracuseStep 1668591 = 2502887) B2502887
theorem B2856431 : Blo 1668034 2856431 := bstep (se 1 (by rfl) ⟨2142323, by rfl⟩ : syracuseStep 2856431 = 4284647) B4284647
theorem B42751475 : Blo 1668034 42751475 := bstep (se 1 (by rfl) ⟨32063606, by rfl⟩ : syracuseStep 42751475 = 64127213) B64127213
theorem B1668699 : Blo 1668034 1668699 := bstep (se 1 (by rfl) ⟨1251524, by rfl⟩ : syracuseStep 1668699 = 2503049) B2503049
theorem B1668763 : Blo 1668034 1668763 := bstep (se 1 (by rfl) ⟨1251572, by rfl⟩ : syracuseStep 1668763 = 2503145) B2503145
theorem B4224737 : Blo 1668034 4224737 := bstep (se 2 (by rfl) ⟨1584276, by rfl⟩ : syracuseStep 4224737 = 3168553) B3168553
theorem B1668847 : Blo 1668034 1668847 := bstep (se 1 (by rfl) ⟨1251635, by rfl⟩ : syracuseStep 1668847 = 2503271) B2503271
theorem B1668935 : Blo 1668034 1668935 := bstep (se 1 (by rfl) ⟨1251701, by rfl⟩ : syracuseStep 1668935 = 2503403) B2503403
theorem B1668955 : Blo 1668034 1668955 := bstep (se 1 (by rfl) ⟨1251716, by rfl⟩ : syracuseStep 1668955 = 2503433) B2503433
theorem B1669023 : Blo 1668034 1669023 := bstep (se 1 (by rfl) ⟨1251767, by rfl⟩ : syracuseStep 1669023 = 2503535) B2503535
theorem B6338519 : Blo 1668034 6338519 := bstep (se 1 (by rfl) ⟨4753889, by rfl⟩ : syracuseStep 6338519 = 9507779) B9507779
theorem B3807271 : Blo 1668034 3807271 := bstep (se 1 (by rfl) ⟨2855453, by rfl⟩ : syracuseStep 3807271 = 5710907) B5710907
theorem B1669191 : Blo 1668034 1669191 := bstep (se 1 (by rfl) ⟨1251893, by rfl⟩ : syracuseStep 1669191 = 2503787) B2503787
theorem B4012103 : Blo 1668034 4012103 := bstep (se 1 (by rfl) ⟨3009077, by rfl⟩ : syracuseStep 4012103 = 6018155) B6018155
theorem B14260333 : Blo 1668034 14260333 := bstep (se 3 (by rfl) ⟨2673812, by rfl⟩ : syracuseStep 14260333 = 5347625) B5347625
theorem B1669351 : Blo 1668034 1669351 := bstep (se 1 (by rfl) ⟨1252013, by rfl⟩ : syracuseStep 1669351 = 2504027) B2504027
theorem B7133447 : Blo 1668034 7133447 := bstep (se 1 (by rfl) ⟨5350085, by rfl⟩ : syracuseStep 7133447 = 10700171) B10700171
theorem B34248997 : Blo 1668034 34248997 := bstep (se 4 (by rfl) ⟨3210843, by rfl⟩ : syracuseStep 34248997 = 6421687) B6421687
theorem B32086367 : Blo 1668034 32086367 := bstep (se 1 (by rfl) ⟨24064775, by rfl⟩ : syracuseStep 32086367 = 48129551) B48129551
theorem B1669535 : Blo 1668034 1669535 := bstep (se 1 (by rfl) ⟨1252151, by rfl⟩ : syracuseStep 1669535 = 2504303) B2504303
theorem B1669583 : Blo 1668034 1669583 := bstep (se 1 (by rfl) ⟨1252187, by rfl⟩ : syracuseStep 1669583 = 2504375) B2504375
theorem B1669607 : Blo 1668034 1669607 := bstep (se 1 (by rfl) ⟨1252205, by rfl⟩ : syracuseStep 1669607 = 2504411) B2504411
theorem B4225567 : Blo 1668034 4225567 := bstep (se 1 (by rfl) ⟨3169175, by rfl⟩ : syracuseStep 4225567 = 6338351) B6338351
theorem B1669723 : Blo 1668034 1669723 := bstep (se 1 (by rfl) ⟨1252292, by rfl⟩ : syracuseStep 1669723 = 2504585) B2504585
theorem B7125641 : Blo 1668034 7125641 := bstep (se 2 (by rfl) ⟨2672115, by rfl⟩ : syracuseStep 7125641 = 5344231) B5344231
theorem B1669791 : Blo 1668034 1669791 := bstep (se 1 (by rfl) ⟨1252343, by rfl⟩ : syracuseStep 1669791 = 2504687) B2504687
theorem B7125691 : Blo 1668034 7125691 := bstep (se 1 (by rfl) ⟨5344268, by rfl⟩ : syracuseStep 7125691 = 10688537) B10688537
theorem B2816815 : Blo 1668034 2816815 := bstep (se 1 (by rfl) ⟨2112611, by rfl⟩ : syracuseStep 2816815 = 4225223) B4225223
theorem B1669959 : Blo 1668034 1669959 := bstep (se 1 (by rfl) ⟨1252469, by rfl⟩ : syracuseStep 1669959 = 2504939) B2504939
theorem B81247049 : Blo 1668034 81247049 := bstep (se 2 (by rfl) ⟨30467643, by rfl⟩ : syracuseStep 81247049 = 60935287) B60935287
theorem B1669999 : Blo 1668034 1669999 := bstep (se 1 (by rfl) ⟨1252499, by rfl⟩ : syracuseStep 1669999 = 2504999) B2504999
theorem B5708825 : Blo 1668034 5708825 := bstep (se 2 (by rfl) ⟨2140809, by rfl⟩ : syracuseStep 5708825 = 4281619) B4281619
theorem B42777719 : Blo 1668034 42777719 := bstep (se 1 (by rfl) ⟨32083289, by rfl⟩ : syracuseStep 42777719 = 64166579) B64166579
theorem B13532285 : Blo 1668034 13532285 := bstep (se 3 (by rfl) ⟨2537303, by rfl⟩ : syracuseStep 13532285 = 5074607) B5074607
theorem B6339809 : Blo 1668034 6339809 := bstep (se 2 (by rfl) ⟨2377428, by rfl⟩ : syracuseStep 6339809 = 4754857) B4754857
theorem B2112743 : Blo 1668034 2112743 := bstep (se 1 (by rfl) ⟨1584557, by rfl⟩ : syracuseStep 2112743 = 3169115) B3169115
theorem B40590629 : Blo 1668034 40590629 := bstep (se 4 (by rfl) ⟨3805371, by rfl⟩ : syracuseStep 40590629 = 7610743) B7610743
theorem B28892609 : Blo 1668034 28892609 := bstep (se 2 (by rfl) ⟨10834728, by rfl⟩ : syracuseStep 28892609 = 21669457) B21669457
theorem B3169783 : Blo 1668034 3169783 := bstep (se 1 (by rfl) ⟨2377337, by rfl⟩ : syracuseStep 3169783 = 4754675) B4754675
theorem B3170011 : Blo 1668034 3170011 := bstep (se 1 (by rfl) ⟨2377508, by rfl⟩ : syracuseStep 3170011 = 4755017) B4755017
theorem B2817767 : Blo 1668034 2817767 := bstep (se 1 (by rfl) ⟨2113325, by rfl⟩ : syracuseStep 2817767 = 4226651) B4226651
theorem B8453969 : Blo 1668034 8453969 := bstep (se 2 (by rfl) ⟨3170238, by rfl⟩ : syracuseStep 8453969 = 6340477) B6340477
theorem B3383137 : Blo 1668034 3383137 := bstep (se 2 (by rfl) ⟨1268676, by rfl⟩ : syracuseStep 3383137 = 2537353) B2537353
theorem B7610237 : Blo 1668034 7610237 := bstep (se 3 (by rfl) ⟨1426919, by rfl⟩ : syracuseStep 7610237 = 2853839) B2853839
theorem B2113447 : Blo 1668034 2113447 := bstep (se 1 (by rfl) ⟨1585085, by rfl⟩ : syracuseStep 2113447 = 3170171) B3170171
theorem B7610345 : Blo 1668034 7610345 := bstep (se 2 (by rfl) ⟨2853879, by rfl⟩ : syracuseStep 7610345 = 5707759) B5707759
theorem B8446031 : Blo 1668034 8446031 := bstep (se 1 (by rfl) ⟨6334523, by rfl⟩ : syracuseStep 8446031 = 12669047) B12669047
theorem B6340751 : Blo 1668034 6340751 := bstep (se 1 (by rfl) ⟨4755563, by rfl⟩ : syracuseStep 6340751 = 9511127) B9511127
theorem B19013777 : Blo 1668034 19013777 := bstep (se 2 (by rfl) ⟨7130166, by rfl⟩ : syracuseStep 19013777 = 14260333) B14260333
theorem B10698941 : Blo 1668034 10698941 := bstep (se 3 (by rfl) ⟨2006051, by rfl⟩ : syracuseStep 10698941 = 4012103) B4012103
theorem B4817191 : Blo 1668034 4817191 := bstep (se 1 (by rfl) ⟨3612893, by rfl⟩ : syracuseStep 4817191 = 7225787) B7225787
theorem B36086093 : Blo 1668034 36086093 := bstep (se 3 (by rfl) ⟨6766142, by rfl⟩ : syracuseStep 36086093 = 13532285) B13532285
theorem B19276157 : Blo 1668034 19276157 := bstep (se 3 (by rfl) ⟨3614279, by rfl⟩ : syracuseStep 19276157 = 7228559) B7228559
theorem B32080373 : Blo 1668034 32080373 := bstep (se 5 (by rfl) ⟨1503767, by rfl⟩ : syracuseStep 32080373 = 3007535) B3007535
theorem B19022525 : Blo 1668034 19022525 := bstep (se 3 (by rfl) ⟨3566723, by rfl⟩ : syracuseStep 19022525 = 7133447) B7133447
theorem B28500983 : Blo 1668034 28500983 := bstep (se 1 (by rfl) ⟨21375737, by rfl⟩ : syracuseStep 28500983 = 42751475) B42751475
theorem B3753143 : Blo 1668034 3753143 := bstep (se 1 (by rfl) ⟨2814857, by rfl⟩ : syracuseStep 3753143 = 5629715) B5629715
theorem B3753287 : Blo 1668034 3753287 := bstep (se 1 (by rfl) ⟨2814965, by rfl⟩ : syracuseStep 3753287 = 5629931) B5629931
theorem B2377127 : Blo 1668034 2377127 := bstep (se 1 (by rfl) ⟨1782845, by rfl⟩ : syracuseStep 2377127 = 3565691) B3565691
theorem B19269089 : Blo 1668034 19269089 := bstep (se 2 (by rfl) ⟨7225908, by rfl⟩ : syracuseStep 19269089 = 14451817) B14451817
theorem B8447489 : Blo 1668034 8447489 := bstep (se 2 (by rfl) ⟨3167808, by rfl⟩ : syracuseStep 8447489 = 6335617) B6335617
theorem B21390911 : Blo 1668034 21390911 := bstep (se 1 (by rfl) ⟨16043183, by rfl⟩ : syracuseStep 21390911 = 32086367) B32086367
theorem B28518479 : Blo 1668034 28518479 := bstep (se 1 (by rfl) ⟨21388859, by rfl⟩ : syracuseStep 28518479 = 42777719) B42777719
theorem B27060419 : Blo 1668034 27060419 := bstep (se 1 (by rfl) ⟨20295314, by rfl⟩ : syracuseStep 27060419 = 40590629) B40590629
theorem B19261739 : Blo 1668034 19261739 := bstep (se 1 (by rfl) ⟨14446304, by rfl⟩ : syracuseStep 19261739 = 28892609) B28892609
theorem B3754295 : Blo 1668034 3754295 := bstep (se 1 (by rfl) ⟨2815721, by rfl⟩ : syracuseStep 3754295 = 5631443) B5631443
theorem B36571607 : Blo 1668034 36571607 := bstep (se 1 (by rfl) ⟨27428705, by rfl⟩ : syracuseStep 36571607 = 54857411) B54857411
theorem B3754475 : Blo 1668034 3754475 := bstep (se 1 (by rfl) ⟨2815856, by rfl⟩ : syracuseStep 3754475 = 5631713) B5631713
theorem B1878511 : Blo 1668034 1878511 := bstep (se 1 (by rfl) ⟨1408883, by rfl⟩ : syracuseStep 1878511 = 2817767) B2817767
theorem B36104773 : Blo 1668034 36104773 := bstep (se 4 (by rfl) ⟨3384822, by rfl⟩ : syracuseStep 36104773 = 6769645) B6769645
theorem B5073491 : Blo 1668034 5073491 := bstep (se 1 (by rfl) ⟨3805118, by rfl⟩ : syracuseStep 5073491 = 7610237) B7610237
theorem B243518075 : Blo 1668034 243518075 := bstep (se 1 (by rfl) ⟨182638556, by rfl⟩ : syracuseStep 243518075 = 365277113) B365277113
theorem B5073563 : Blo 1668034 5073563 := bstep (se 1 (by rfl) ⟨3805172, by rfl⟩ : syracuseStep 5073563 = 7610345) B7610345
theorem B7129757 : Blo 1668034 7129757 := bstep (se 3 (by rfl) ⟨1336829, by rfl⟩ : syracuseStep 7129757 = 2673659) B2673659
theorem B3566587 : Blo 1668034 3566587 := bstep (se 1 (by rfl) ⟨2674940, by rfl⟩ : syracuseStep 3566587 = 5349881) B5349881
theorem B28920887 : Blo 1668034 28920887 := bstep (se 1 (by rfl) ⟨21690665, by rfl⟩ : syracuseStep 28920887 = 43381331) B43381331
theorem B5344679 : Blo 1668034 5344679 := bstep (se 1 (by rfl) ⟨4008509, by rfl⟩ : syracuseStep 5344679 = 8017019) B8017019
theorem B3755663 : Blo 1668034 3755663 := bstep (se 1 (by rfl) ⟨2816747, by rfl⟩ : syracuseStep 3755663 = 5633495) B5633495
theorem B2502311 : Blo 1668034 2502311 := bstep (se 1 (by rfl) ⟨1876733, by rfl⟩ : syracuseStep 2502311 = 3753467) B3753467
theorem B2502335 : Blo 1668034 2502335 := bstep (se 1 (by rfl) ⟨1876751, by rfl⟩ : syracuseStep 2502335 = 3753503) B3753503
theorem B3755753 : Blo 1668034 3755753 := bstep (se 2 (by rfl) ⟨1408407, by rfl⟩ : syracuseStep 3755753 = 2816815) B2816815
theorem B2502431 : Blo 1668034 2502431 := bstep (se 1 (by rfl) ⟨1876823, by rfl⟩ : syracuseStep 2502431 = 3753647) B3753647
theorem B24063803 : Blo 1668034 24063803 := bstep (se 1 (by rfl) ⟨18047852, by rfl⟩ : syracuseStep 24063803 = 36095705) B36095705
theorem B2502719 : Blo 1668034 2502719 := bstep (se 1 (by rfl) ⟨1877039, by rfl⟩ : syracuseStep 2502719 = 3754079) B3754079
theorem B182661317 : Blo 1668034 182661317 := bstep (se 4 (by rfl) ⟨17124498, by rfl⟩ : syracuseStep 182661317 = 34248997) B34248997
theorem B8024285 : Blo 1668034 8024285 := bstep (se 3 (by rfl) ⟨1504553, by rfl⟩ : syracuseStep 8024285 = 3009107) B3009107
theorem B2502911 : Blo 1668034 2502911 := bstep (se 1 (by rfl) ⟨1877183, by rfl⟩ : syracuseStep 2502911 = 3754367) B3754367
theorem B2502953 : Blo 1668034 2502953 := bstep (se 2 (by rfl) ⟨938607, by rfl⟩ : syracuseStep 2502953 = 1877215) B1877215
theorem B2503223 : Blo 1668034 2503223 := bstep (se 1 (by rfl) ⟨1877417, by rfl⟩ : syracuseStep 2503223 = 3754835) B3754835
theorem B3805883 : Blo 1668034 3805883 := bstep (se 1 (by rfl) ⟨2854412, by rfl⟩ : syracuseStep 3805883 = 5708825) B5708825
theorem B2503463 : Blo 1668034 2503463 := bstep (se 1 (by rfl) ⟨1877597, by rfl⟩ : syracuseStep 2503463 = 3755195) B3755195
theorem B2503583 : Blo 1668034 2503583 := bstep (se 1 (by rfl) ⟨1877687, by rfl⟩ : syracuseStep 2503583 = 3755375) B3755375
theorem B1668143 : Blo 1668034 1668143 := bstep (se 1 (by rfl) ⟨1251107, by rfl⟩ : syracuseStep 1668143 = 2502215) B2502215
theorem B4510849 : Blo 1668034 4510849 := bstep (se 2 (by rfl) ⟨1691568, by rfl⟩ : syracuseStep 4510849 = 3383137) B3383137
theorem B1668263 : Blo 1668034 1668263 := bstep (se 1 (by rfl) ⟨1251197, by rfl⟩ : syracuseStep 1668263 = 2502395) B2502395
theorem B4224251 : Blo 1668034 4224251 := bstep (se 1 (by rfl) ⟨3168188, by rfl⟩ : syracuseStep 4224251 = 6336377) B6336377
theorem B2504057 : Blo 1668034 2504057 := bstep (se 2 (by rfl) ⟨939021, by rfl⟩ : syracuseStep 2504057 = 1878043) B1878043
theorem B2504063 : Blo 1668034 2504063 := bstep (se 1 (by rfl) ⟨1878047, by rfl⟩ : syracuseStep 2504063 = 3756095) B3756095
theorem B5076361 : Blo 1668034 5076361 := bstep (se 2 (by rfl) ⟨1903635, by rfl⟩ : syracuseStep 5076361 = 3807271) B3807271
theorem B8451539 : Blo 1668034 8451539 := bstep (se 1 (by rfl) ⟨6338654, by rfl⟩ : syracuseStep 8451539 = 12677309) B12677309
theorem B2504219 : Blo 1668034 2504219 := bstep (se 1 (by rfl) ⟨1878164, by rfl⟩ : syracuseStep 2504219 = 3756329) B3756329
theorem B10688051 : Blo 1668034 10688051 := bstep (se 1 (by rfl) ⟨8016038, by rfl⟩ : syracuseStep 10688051 = 16032077) B16032077
theorem B1668711 : Blo 1668034 1668711 := bstep (se 1 (by rfl) ⟨1251533, by rfl⟩ : syracuseStep 1668711 = 2503067) B2503067
theorem B6182543 : Blo 1668034 6182543 := bstep (se 1 (by rfl) ⟨4636907, by rfl⟩ : syracuseStep 6182543 = 9273815) B9273815
theorem B2504399 : Blo 1668034 2504399 := bstep (se 1 (by rfl) ⟨1878299, by rfl⟩ : syracuseStep 2504399 = 3756599) B3756599
theorem B13539163 : Blo 1668034 13539163 := bstep (se 1 (by rfl) ⟨10154372, by rfl⟩ : syracuseStep 13539163 = 20308745) B20308745
theorem B1668991 : Blo 1668034 1668991 := bstep (se 1 (by rfl) ⟨1251743, by rfl⟩ : syracuseStep 1668991 = 2503487) B2503487
theorem B2504603 : Blo 1668034 2504603 := bstep (se 1 (by rfl) ⟨1878452, by rfl⟩ : syracuseStep 2504603 = 3756905) B3756905
theorem B5633981 : Blo 1668034 5633981 := bstep (se 3 (by rfl) ⟨1056371, by rfl⟩ : syracuseStep 5633981 = 2112743) B2112743
theorem B2504639 : Blo 1668034 2504639 := bstep (se 1 (by rfl) ⟨1878479, by rfl⟩ : syracuseStep 2504639 = 3756959) B3756959
theorem B1669087 : Blo 1668034 1669087 := bstep (se 1 (by rfl) ⟨1251815, by rfl⟩ : syracuseStep 1669087 = 2503631) B2503631
theorem B1669115 : Blo 1668034 1669115 := bstep (se 1 (by rfl) ⟨1251836, by rfl⟩ : syracuseStep 1669115 = 2503673) B2503673
theorem B1669147 : Blo 1668034 1669147 := bstep (se 1 (by rfl) ⟨1251860, by rfl⟩ : syracuseStep 1669147 = 2503721) B2503721
theorem B5634089 : Blo 1668034 5634089 := bstep (se 2 (by rfl) ⟨2112783, by rfl⟩ : syracuseStep 5634089 = 4225567) B4225567
theorem B1669167 : Blo 1668034 1669167 := bstep (se 1 (by rfl) ⟨1251875, by rfl⟩ : syracuseStep 1669167 = 2503751) B2503751
theorem B2504807 : Blo 1668034 2504807 := bstep (se 1 (by rfl) ⟨1878605, by rfl⟩ : syracuseStep 2504807 = 3757211) B3757211
theorem B1669287 : Blo 1668034 1669287 := bstep (se 1 (by rfl) ⟨1251965, by rfl⟩ : syracuseStep 1669287 = 2503931) B2503931
theorem B8018135 : Blo 1668034 8018135 := bstep (se 1 (by rfl) ⟨6013601, by rfl⟩ : syracuseStep 8018135 = 12027203) B12027203
theorem B4225243 : Blo 1668034 4225243 := bstep (se 1 (by rfl) ⟨3168932, by rfl⟩ : syracuseStep 4225243 = 6337865) B6337865
theorem B9500921 : Blo 1668034 9500921 := bstep (se 2 (by rfl) ⟨3562845, by rfl⟩ : syracuseStep 9500921 = 7125691) B7125691
theorem B43342141 : Blo 1668034 43342141 := bstep (se 3 (by rfl) ⟨8126651, by rfl⟩ : syracuseStep 43342141 = 16253303) B16253303
theorem B2816491 : Blo 1668034 2816491 := bstep (se 1 (by rfl) ⟨2112368, by rfl⟩ : syracuseStep 2816491 = 4224737) B4224737
theorem B7617149 : Blo 1668034 7617149 := bstep (se 3 (by rfl) ⟨1428215, by rfl⟩ : syracuseStep 7617149 = 2856431) B2856431
theorem B4225679 : Blo 1668034 4225679 := bstep (se 1 (by rfl) ⟨3169259, by rfl⟩ : syracuseStep 4225679 = 6338519) B6338519
theorem B3169343 : Blo 1668034 3169343 := bstep (se 1 (by rfl) ⟨2377007, by rfl⟩ : syracuseStep 3169343 = 4754015) B4754015
theorem B4750427 : Blo 1668034 4750427 := bstep (se 1 (by rfl) ⟨3562820, by rfl⟩ : syracuseStep 4750427 = 7125641) B7125641
theorem B54164699 : Blo 1668034 54164699 := bstep (se 1 (by rfl) ⟨40623524, by rfl⟩ : syracuseStep 54164699 = 81247049) B81247049
theorem B4226377 : Blo 1668034 4226377 := bstep (se 2 (by rfl) ⟨1584891, by rfl⟩ : syracuseStep 4226377 = 3169783) B3169783
theorem B4226539 : Blo 1668034 4226539 := bstep (se 1 (by rfl) ⟨3169904, by rfl⟩ : syracuseStep 4226539 = 6339809) B6339809
theorem B4226681 : Blo 1668034 4226681 := bstep (se 2 (by rfl) ⟨1585005, by rfl⟩ : syracuseStep 4226681 = 3170011) B3170011
theorem B2817929 : Blo 1668034 2817929 := bstep (se 2 (by rfl) ⟨1056723, by rfl⟩ : syracuseStep 2817929 = 2113447) B2113447
theorem B5635979 : Blo 1668034 5635979 := bstep (se 1 (by rfl) ⟨4226984, by rfl⟩ : syracuseStep 5635979 = 8453969) B8453969
theorem B8445869 : Blo 1668034 8445869 := bstep (se 3 (by rfl) ⟨1583600, by rfl⟩ : syracuseStep 8445869 = 3167201) B3167201
theorem B4227167 : Blo 1668034 4227167 := bstep (se 1 (by rfl) ⟨3170375, by rfl⟩ : syracuseStep 4227167 = 6340751) B6340751
theorem B121774211 : Blo 1668034 121774211 := bstep (se 1 (by rfl) ⟨91330658, by rfl⟩ : syracuseStep 121774211 = 182661317) B182661317
theorem B5349523 : Blo 1668034 5349523 := bstep (se 1 (by rfl) ⟨4012142, by rfl⟩ : syracuseStep 5349523 = 8024285) B8024285
theorem B6422921 : Blo 1668034 6422921 := bstep (se 2 (by rfl) ⟨2408595, by rfl⟩ : syracuseStep 6422921 = 4817191) B4817191
theorem B12681683 : Blo 1668034 12681683 := bstep (se 1 (by rfl) ⟨9511262, by rfl⟩ : syracuseStep 12681683 = 19022525) B19022525
theorem B12846059 : Blo 1668034 12846059 := bstep (se 1 (by rfl) ⟨9634544, by rfl⟩ : syracuseStep 12846059 = 19269089) B19269089
theorem B4121695 : Blo 1668034 4121695 := bstep (se 1 (by rfl) ⟨3091271, by rfl⟩ : syracuseStep 4121695 = 6182543) B6182543
theorem B18040279 : Blo 1668034 18040279 := bstep (se 1 (by rfl) ⟨13530209, by rfl⟩ : syracuseStep 18040279 = 27060419) B27060419
theorem B6333947 : Blo 1668034 6333947 := bstep (se 1 (by rfl) ⟨4750460, by rfl⟩ : syracuseStep 6333947 = 9500921) B9500921
theorem B6014465 : Blo 1668034 6014465 := bstep (se 2 (by rfl) ⟨2255424, by rfl⟩ : syracuseStep 6014465 = 4510849) B4510849
theorem B24381071 : Blo 1668034 24381071 := bstep (se 1 (by rfl) ⟨18285803, by rfl⟩ : syracuseStep 24381071 = 36571607) B36571607
theorem B4753171 : Blo 1668034 4753171 := bstep (se 1 (by rfl) ⟨3564878, by rfl⟩ : syracuseStep 4753171 = 7129757) B7129757
theorem B6768481 : Blo 1668034 6768481 := bstep (se 2 (by rfl) ⟨2538180, by rfl⟩ : syracuseStep 6768481 = 5076361) B5076361
theorem B16042535 : Blo 1668034 16042535 := bstep (se 1 (by rfl) ⟨12031901, by rfl⟩ : syracuseStep 16042535 = 24063803) B24063803
theorem B1878619 : Blo 1668034 1878619 := bstep (se 1 (by rfl) ⟨1408964, by rfl⟩ : syracuseStep 1878619 = 2817929) B2817929
theorem B5630579 : Blo 1668034 5630579 := bstep (se 1 (by rfl) ⟨4222934, by rfl⟩ : syracuseStep 5630579 = 8445869) B8445869
theorem B5630687 : Blo 1668034 5630687 := bstep (se 1 (by rfl) ⟨4223015, by rfl⟩ : syracuseStep 5630687 = 8446031) B8446031
theorem B12675851 : Blo 1668034 12675851 := bstep (se 1 (by rfl) ⟨9506888, by rfl⟩ : syracuseStep 12675851 = 19013777) B19013777
theorem B57789521 : Blo 1668034 57789521 := bstep (se 2 (by rfl) ⟨21671070, by rfl⟩ : syracuseStep 57789521 = 43342141) B43342141
theorem B3755321 : Blo 1668034 3755321 := bstep (se 2 (by rfl) ⟨1408245, by rfl⟩ : syracuseStep 3755321 = 2816491) B2816491
theorem B19000655 : Blo 1668034 19000655 := bstep (se 1 (by rfl) ⟨14250491, by rfl⟩ : syracuseStep 19000655 = 28500983) B28500983
theorem B48139697 : Blo 1668034 48139697 := bstep (se 2 (by rfl) ⟨18052386, by rfl⟩ : syracuseStep 48139697 = 36104773) B36104773
theorem B2502095 : Blo 1668034 2502095 := bstep (se 1 (by rfl) ⟨1876571, by rfl⟩ : syracuseStep 2502095 = 3753143) B3753143
theorem B2502191 : Blo 1668034 2502191 := bstep (se 1 (by rfl) ⟨1876643, by rfl⟩ : syracuseStep 2502191 = 3753287) B3753287
theorem B5631659 : Blo 1668034 5631659 := bstep (se 1 (by rfl) ⟨4223744, by rfl⟩ : syracuseStep 5631659 = 8447489) B8447489
theorem B3755987 : Blo 1668034 3755987 := bstep (se 1 (by rfl) ⟨2816990, by rfl⟩ : syracuseStep 3755987 = 5633981) B5633981
theorem B4755449 : Blo 1668034 4755449 := bstep (se 2 (by rfl) ⟨1783293, by rfl⟩ : syracuseStep 4755449 = 3566587) B3566587
theorem B3756059 : Blo 1668034 3756059 := bstep (se 1 (by rfl) ⟨2817044, by rfl⟩ : syracuseStep 3756059 = 5634089) B5634089
theorem B5345423 : Blo 1668034 5345423 := bstep (se 1 (by rfl) ⟨4009067, by rfl⟩ : syracuseStep 5345423 = 8018135) B8018135
theorem B12841159 : Blo 1668034 12841159 := bstep (se 1 (by rfl) ⟨9630869, by rfl⟩ : syracuseStep 12841159 = 19261739) B19261739
theorem B2502863 : Blo 1668034 2502863 := bstep (se 1 (by rfl) ⟨1877147, by rfl⟩ : syracuseStep 2502863 = 3754295) B3754295
theorem B2502983 : Blo 1668034 2502983 := bstep (se 1 (by rfl) ⟨1877237, by rfl⟩ : syracuseStep 2502983 = 3754475) B3754475
theorem B13529501 : Blo 1668034 13529501 := bstep (se 3 (by rfl) ⟨2536781, by rfl⟩ : syracuseStep 13529501 = 5073563) B5073563
theorem B162345383 : Blo 1668034 162345383 := bstep (se 1 (by rfl) ⟨121759037, by rfl⟩ : syracuseStep 162345383 = 243518075) B243518075
theorem B19280591 : Blo 1668034 19280591 := bstep (se 1 (by rfl) ⟨14460443, by rfl⟩ : syracuseStep 19280591 = 28920887) B28920887
theorem B3166951 : Blo 1668034 3166951 := bstep (se 1 (by rfl) ⟨2375213, by rfl⟩ : syracuseStep 3166951 = 4750427) B4750427
theorem B7132627 : Blo 1668034 7132627 := bstep (se 1 (by rfl) ⟨5349470, by rfl⟩ : syracuseStep 7132627 = 10698941) B10698941
theorem B2503775 : Blo 1668034 2503775 := bstep (se 1 (by rfl) ⟨1877831, by rfl⟩ : syracuseStep 2503775 = 3755663) B3755663
theorem B1668207 : Blo 1668034 1668207 := bstep (se 1 (by rfl) ⟨1251155, by rfl⟩ : syracuseStep 1668207 = 2502311) B2502311
theorem B18052217 : Blo 1668034 18052217 := bstep (se 2 (by rfl) ⟨6769581, by rfl⟩ : syracuseStep 18052217 = 13539163) B13539163
theorem B1668223 : Blo 1668034 1668223 := bstep (se 1 (by rfl) ⟨1251167, by rfl⟩ : syracuseStep 1668223 = 2502335) B2502335
theorem B2503835 : Blo 1668034 2503835 := bstep (se 1 (by rfl) ⟨1877876, by rfl⟩ : syracuseStep 2503835 = 3755753) B3755753
theorem B1668287 : Blo 1668034 1668287 := bstep (se 1 (by rfl) ⟨1251215, by rfl⟩ : syracuseStep 1668287 = 2502431) B2502431
theorem B3757319 : Blo 1668034 3757319 := bstep (se 1 (by rfl) ⟨2817989, by rfl⟩ : syracuseStep 3757319 = 5635979) B5635979
theorem B1668479 : Blo 1668034 1668479 := bstep (se 1 (by rfl) ⟨1251359, by rfl⟩ : syracuseStep 1668479 = 2502719) B2502719
theorem B1668607 : Blo 1668034 1668607 := bstep (se 1 (by rfl) ⟨1251455, by rfl⟩ : syracuseStep 1668607 = 2502911) B2502911
theorem B1668635 : Blo 1668034 1668635 := bstep (se 1 (by rfl) ⟨1251476, by rfl⟩ : syracuseStep 1668635 = 2502953) B2502953
theorem B24057395 : Blo 1668034 24057395 := bstep (se 1 (by rfl) ⟨18043046, by rfl⟩ : syracuseStep 24057395 = 36086093) B36086093
theorem B12850771 : Blo 1668034 12850771 := bstep (se 1 (by rfl) ⟨9638078, by rfl⟩ : syracuseStep 12850771 = 19276157) B19276157
theorem B5633657 : Blo 1668034 5633657 := bstep (se 2 (by rfl) ⟨2112621, by rfl⟩ : syracuseStep 5633657 = 4225243) B4225243
theorem B21386915 : Blo 1668034 21386915 := bstep (se 1 (by rfl) ⟨16040186, by rfl⟩ : syracuseStep 21386915 = 32080373) B32080373
theorem B1668815 : Blo 1668034 1668815 := bstep (se 1 (by rfl) ⟨1251611, by rfl⟩ : syracuseStep 1668815 = 2503223) B2503223
theorem B2537255 : Blo 1668034 2537255 := bstep (se 1 (by rfl) ⟨1902941, by rfl⟩ : syracuseStep 2537255 = 3805883) B3805883
theorem B1668975 : Blo 1668034 1668975 := bstep (se 1 (by rfl) ⟨1251731, by rfl⟩ : syracuseStep 1668975 = 2503463) B2503463
theorem B1669055 : Blo 1668034 1669055 := bstep (se 1 (by rfl) ⟨1251791, by rfl⟩ : syracuseStep 1669055 = 2503583) B2503583
theorem B2504681 : Blo 1668034 2504681 := bstep (se 2 (by rfl) ⟨939255, by rfl⟩ : syracuseStep 2504681 = 1878511) B1878511
theorem B2816167 : Blo 1668034 2816167 := bstep (se 1 (by rfl) ⟨2112125, by rfl⟩ : syracuseStep 2816167 = 4224251) B4224251
theorem B1669371 : Blo 1668034 1669371 := bstep (se 1 (by rfl) ⟨1252028, by rfl⟩ : syracuseStep 1669371 = 2504057) B2504057
theorem B1669375 : Blo 1668034 1669375 := bstep (se 1 (by rfl) ⟨1252031, by rfl⟩ : syracuseStep 1669375 = 2504063) B2504063
theorem B5634359 : Blo 1668034 5634359 := bstep (se 1 (by rfl) ⟨4225769, by rfl⟩ : syracuseStep 5634359 = 8451539) B8451539
theorem B1669479 : Blo 1668034 1669479 := bstep (se 1 (by rfl) ⟨1252109, by rfl⟩ : syracuseStep 1669479 = 2504219) B2504219
theorem B7125367 : Blo 1668034 7125367 := bstep (se 1 (by rfl) ⟨5344025, by rfl⟩ : syracuseStep 7125367 = 10688051) B10688051
theorem B14260607 : Blo 1668034 14260607 := bstep (se 1 (by rfl) ⟨10695455, by rfl⟩ : syracuseStep 14260607 = 21390911) B21390911
theorem B6339005 : Blo 1668034 6339005 := bstep (se 3 (by rfl) ⟨1188563, by rfl⟩ : syracuseStep 6339005 = 2377127) B2377127
theorem B1669599 : Blo 1668034 1669599 := bstep (se 1 (by rfl) ⟨1252199, by rfl⟩ : syracuseStep 1669599 = 2504399) B2504399
theorem B1669735 : Blo 1668034 1669735 := bstep (se 1 (by rfl) ⟨1252301, by rfl⟩ : syracuseStep 1669735 = 2504603) B2504603
theorem B1669759 : Blo 1668034 1669759 := bstep (se 1 (by rfl) ⟨1252319, by rfl⟩ : syracuseStep 1669759 = 2504639) B2504639
theorem B19012319 : Blo 1668034 19012319 := bstep (se 1 (by rfl) ⟨14259239, by rfl⟩ : syracuseStep 19012319 = 28518479) B28518479
theorem B1669871 : Blo 1668034 1669871 := bstep (se 1 (by rfl) ⟨1252403, by rfl⟩ : syracuseStep 1669871 = 2504807) B2504807
theorem B3382327 : Blo 1668034 3382327 := bstep (se 1 (by rfl) ⟨2536745, by rfl⟩ : syracuseStep 3382327 = 5073491) B5073491
theorem B5078099 : Blo 1668034 5078099 := bstep (se 1 (by rfl) ⟨3808574, by rfl⟩ : syracuseStep 5078099 = 7617149) B7617149
theorem B2817119 : Blo 1668034 2817119 := bstep (se 1 (by rfl) ⟨2112839, by rfl⟩ : syracuseStep 2817119 = 4225679) B4225679
theorem B5635169 : Blo 1668034 5635169 := bstep (se 2 (by rfl) ⟨2113188, by rfl⟩ : syracuseStep 5635169 = 4226377) B4226377
theorem B5635385 : Blo 1668034 5635385 := bstep (se 2 (by rfl) ⟨2113269, by rfl⟩ : syracuseStep 5635385 = 4226539) B4226539
theorem B2112895 : Blo 1668034 2112895 := bstep (se 1 (by rfl) ⟨1584671, by rfl⟩ : syracuseStep 2112895 = 3169343) B3169343
theorem B36109799 : Blo 1668034 36109799 := bstep (se 1 (by rfl) ⟨27082349, by rfl⟩ : syracuseStep 36109799 = 54164699) B54164699
theorem B3563119 : Blo 1668034 3563119 := bstep (se 1 (by rfl) ⟨2672339, by rfl⟩ : syracuseStep 3563119 = 5344679) B5344679
theorem B2817787 : Blo 1668034 2817787 := bstep (se 1 (by rfl) ⟨2113340, by rfl⟩ : syracuseStep 2817787 = 4226681) B4226681
theorem B2818111 : Blo 1668034 2818111 := bstep (se 1 (by rfl) ⟨2113583, by rfl⟩ : syracuseStep 2818111 = 4227167) B4227167
theorem B81182807 : Blo 1668034 81182807 := bstep (se 1 (by rfl) ⟨60887105, by rfl⟩ : syracuseStep 81182807 = 121774211) B121774211
theorem B3563615 : Blo 1668034 3563615 := bstep (se 1 (by rfl) ⟨2672711, by rfl⟩ : syracuseStep 3563615 = 5345423) B5345423
theorem B13541597 : Blo 1668034 13541597 := bstep (se 3 (by rfl) ⟨2539049, by rfl⟩ : syracuseStep 13541597 = 5078099) B5078099
theorem B17121545 : Blo 1668034 17121545 := bstep (se 2 (by rfl) ⟨6420579, by rfl⟩ : syracuseStep 17121545 = 12841159) B12841159
theorem B9019667 : Blo 1668034 9019667 := bstep (se 1 (by rfl) ⟨6764750, by rfl⟩ : syracuseStep 9019667 = 13529501) B13529501
theorem B8454455 : Blo 1668034 8454455 := bstep (se 1 (by rfl) ⟨6340841, by rfl⟩ : syracuseStep 8454455 = 12681683) B12681683
theorem B12853727 : Blo 1668034 12853727 := bstep (se 1 (by rfl) ⟨9640295, by rfl⟩ : syracuseStep 12853727 = 19280591) B19280591
theorem B12034811 : Blo 1668034 12034811 := bstep (se 1 (by rfl) ⟨9026108, by rfl⟩ : syracuseStep 12034811 = 18052217) B18052217
theorem B16254047 : Blo 1668034 16254047 := bstep (se 1 (by rfl) ⟨12190535, by rfl⟩ : syracuseStep 16254047 = 24381071) B24381071
theorem B3753719 : Blo 1668034 3753719 := bstep (se 1 (by rfl) ⟨2815289, by rfl⟩ : syracuseStep 3753719 = 5630579) B5630579
theorem B3753791 : Blo 1668034 3753791 := bstep (se 1 (by rfl) ⟨2815343, by rfl⟩ : syracuseStep 3753791 = 5630687) B5630687
theorem B12674879 : Blo 1668034 12674879 := bstep (se 1 (by rfl) ⟨9506159, by rfl⟩ : syracuseStep 12674879 = 19012319) B19012319
theorem B24053705 : Blo 1668034 24053705 := bstep (se 2 (by rfl) ⟨9020139, by rfl⟩ : syracuseStep 24053705 = 18040279) B18040279
theorem B1878079 : Blo 1668034 1878079 := bstep (se 1 (by rfl) ⟨1408559, by rfl⟩ : syracuseStep 1878079 = 2817119) B2817119
theorem B12667103 : Blo 1668034 12667103 := bstep (se 1 (by rfl) ⟨9500327, by rfl⟩ : syracuseStep 12667103 = 19000655) B19000655
theorem B3754439 : Blo 1668034 3754439 := bstep (se 1 (by rfl) ⟨2815829, by rfl⟩ : syracuseStep 3754439 = 5631659) B5631659
theorem B3754889 : Blo 1668034 3754889 := bstep (se 2 (by rfl) ⟨1408083, by rfl⟩ : syracuseStep 3754889 = 2816167) B2816167
theorem B21982373 : Blo 1668034 21982373 := bstep (se 4 (by rfl) ⟨2060847, by rfl⟩ : syracuseStep 21982373 = 4121695) B4121695
theorem B8564039 : Blo 1668034 8564039 := bstep (se 1 (by rfl) ⟨6423029, by rfl⟩ : syracuseStep 8564039 = 12846059) B12846059
theorem B4222601 : Blo 1668034 4222601 := bstep (se 2 (by rfl) ⟨1583475, by rfl⟩ : syracuseStep 4222601 = 3166951) B3166951
theorem B4222631 : Blo 1668034 4222631 := bstep (se 1 (by rfl) ⟨3166973, by rfl⟩ : syracuseStep 4222631 = 6333947) B6333947
theorem B4009643 : Blo 1668034 4009643 := bstep (se 1 (by rfl) ⟨3007232, by rfl⟩ : syracuseStep 4009643 = 6014465) B6014465
theorem B3755771 : Blo 1668034 3755771 := bstep (se 1 (by rfl) ⟨2816828, by rfl⟩ : syracuseStep 3755771 = 5633657) B5633657
theorem B14257943 : Blo 1668034 14257943 := bstep (se 1 (by rfl) ⟨10693457, by rfl⟩ : syracuseStep 14257943 = 21386915) B21386915
theorem B4509769 : Blo 1668034 4509769 := bstep (se 2 (by rfl) ⟨1691163, by rfl⟩ : syracuseStep 4509769 = 3382327) B3382327
theorem B3756239 : Blo 1668034 3756239 := bstep (se 1 (by rfl) ⟨2817179, by rfl⟩ : syracuseStep 3756239 = 5634359) B5634359
theorem B9507071 : Blo 1668034 9507071 := bstep (se 1 (by rfl) ⟨7130303, by rfl⟩ : syracuseStep 9507071 = 14260607) B14260607
theorem B10695023 : Blo 1668034 10695023 := bstep (se 1 (by rfl) ⟨8021267, by rfl⟩ : syracuseStep 10695023 = 16042535) B16042535
theorem B8450567 : Blo 1668034 8450567 := bstep (se 1 (by rfl) ⟨6337925, by rfl⟩ : syracuseStep 8450567 = 12675851) B12675851
theorem B3756779 : Blo 1668034 3756779 := bstep (se 1 (by rfl) ⟨2817584, by rfl⟩ : syracuseStep 3756779 = 5635169) B5635169
theorem B17134361 : Blo 1668034 17134361 := bstep (se 2 (by rfl) ⟨6425385, by rfl⟩ : syracuseStep 17134361 = 12850771) B12850771
theorem B2503547 : Blo 1668034 2503547 := bstep (se 1 (by rfl) ⟨1877660, by rfl⟩ : syracuseStep 2503547 = 3755321) B3755321
theorem B3756923 : Blo 1668034 3756923 := bstep (se 1 (by rfl) ⟨2817692, by rfl⟩ : syracuseStep 3756923 = 5635385) B5635385
theorem B32093131 : Blo 1668034 32093131 := bstep (se 1 (by rfl) ⟨24069848, by rfl⟩ : syracuseStep 32093131 = 48139697) B48139697
theorem B1668063 : Blo 1668034 1668063 := bstep (se 1 (by rfl) ⟨1251047, by rfl⟩ : syracuseStep 1668063 = 2502095) B2502095
theorem B24073199 : Blo 1668034 24073199 := bstep (se 1 (by rfl) ⟨18054899, by rfl⟩ : syracuseStep 24073199 = 36109799) B36109799
theorem B3757049 : Blo 1668034 3757049 := bstep (se 2 (by rfl) ⟨1408893, by rfl⟩ : syracuseStep 3757049 = 2817787) B2817787
theorem B6337561 : Blo 1668034 6337561 := bstep (se 2 (by rfl) ⟨2376585, by rfl⟩ : syracuseStep 6337561 = 4753171) B4753171
theorem B1668127 : Blo 1668034 1668127 := bstep (se 1 (by rfl) ⟨1251095, by rfl⟩ : syracuseStep 1668127 = 2502191) B2502191
theorem B9024641 : Blo 1668034 9024641 := bstep (se 2 (by rfl) ⟨3384240, by rfl⟩ : syracuseStep 9024641 = 6768481) B6768481
theorem B2503991 : Blo 1668034 2503991 := bstep (se 1 (by rfl) ⟨1877993, by rfl⟩ : syracuseStep 2503991 = 3755987) B3755987
theorem B2504039 : Blo 1668034 2504039 := bstep (se 1 (by rfl) ⟨1878029, by rfl⟩ : syracuseStep 2504039 = 3756059) B3756059
theorem B1668575 : Blo 1668034 1668575 := bstep (se 1 (by rfl) ⟨1251431, by rfl⟩ : syracuseStep 1668575 = 2502863) B2502863
theorem B7132697 : Blo 1668034 7132697 := bstep (se 2 (by rfl) ⟨2674761, by rfl⟩ : syracuseStep 7132697 = 5349523) B5349523
theorem B1668655 : Blo 1668034 1668655 := bstep (se 1 (by rfl) ⟨1251491, by rfl⟩ : syracuseStep 1668655 = 2502983) B2502983
theorem B4281947 : Blo 1668034 4281947 := bstep (se 1 (by rfl) ⟨3211460, by rfl⟩ : syracuseStep 4281947 = 6422921) B6422921
theorem B108230255 : Blo 1668034 108230255 := bstep (se 1 (by rfl) ⟨81172691, by rfl⟩ : syracuseStep 108230255 = 162345383) B162345383
theorem B9500489 : Blo 1668034 9500489 := bstep (se 2 (by rfl) ⟨3562683, by rfl⟩ : syracuseStep 9500489 = 7125367) B7125367
theorem B1669183 : Blo 1668034 1669183 := bstep (se 1 (by rfl) ⟨1251887, by rfl⟩ : syracuseStep 1669183 = 2503775) B2503775
theorem B1669223 : Blo 1668034 1669223 := bstep (se 1 (by rfl) ⟨1251917, by rfl⟩ : syracuseStep 1669223 = 2503835) B2503835
theorem B2504825 : Blo 1668034 2504825 := bstep (se 2 (by rfl) ⟨939309, by rfl⟩ : syracuseStep 2504825 = 1878619) B1878619
theorem B2504879 : Blo 1668034 2504879 := bstep (se 1 (by rfl) ⟨1878659, by rfl⟩ : syracuseStep 2504879 = 3757319) B3757319
theorem B16038263 : Blo 1668034 16038263 := bstep (se 1 (by rfl) ⟨12028697, by rfl⟩ : syracuseStep 16038263 = 24057395) B24057395
theorem B1669787 : Blo 1668034 1669787 := bstep (se 1 (by rfl) ⟨1252340, by rfl⟩ : syracuseStep 1669787 = 2504681) B2504681
theorem B4226003 : Blo 1668034 4226003 := bstep (se 1 (by rfl) ⟨3169502, by rfl⟩ : syracuseStep 4226003 = 6339005) B6339005
theorem B2817193 : Blo 1668034 2817193 := bstep (se 2 (by rfl) ⟨1056447, by rfl⟩ : syracuseStep 2817193 = 2112895) B2112895
theorem B9510169 : Blo 1668034 9510169 := bstep (se 2 (by rfl) ⟨3566313, by rfl⟩ : syracuseStep 9510169 = 7132627) B7132627
theorem B38526347 : Blo 1668034 38526347 := bstep (se 1 (by rfl) ⟨28894760, by rfl⟩ : syracuseStep 38526347 = 57789521) B57789521
theorem B6766013 : Blo 1668034 6766013 := bstep (se 3 (by rfl) ⟨1268627, by rfl⟩ : syracuseStep 6766013 = 2537255) B2537255
theorem B4750825 : Blo 1668034 4750825 := bstep (se 2 (by rfl) ⟨1781559, by rfl⟩ : syracuseStep 4750825 = 3563119) B3563119
theorem B12681197 : Blo 1668034 12681197 := bstep (se 3 (by rfl) ⟨2377724, by rfl⟩ : syracuseStep 12681197 = 4755449) B4755449
theorem B2375743 : Blo 1668034 2375743 := bstep (se 1 (by rfl) ⟨1781807, by rfl⟩ : syracuseStep 2375743 = 3563615) B3563615
theorem B6013025 : Blo 1668034 6013025 := bstep (se 2 (by rfl) ⟨2254884, by rfl⟩ : syracuseStep 6013025 = 4509769) B4509769
theorem B9027731 : Blo 1668034 9027731 := bstep (se 1 (by rfl) ⟨6770798, by rfl⟩ : syracuseStep 9027731 = 13541597) B13541597
theorem B6013111 : Blo 1668034 6013111 := bstep (se 1 (by rfl) ⟨4509833, by rfl⟩ : syracuseStep 6013111 = 9019667) B9019667
theorem B5636303 : Blo 1668034 5636303 := bstep (se 1 (by rfl) ⟨4227227, by rfl⟩ : syracuseStep 5636303 = 8454455) B8454455
theorem B8569151 : Blo 1668034 8569151 := bstep (se 1 (by rfl) ⟨6426863, by rfl⟩ : syracuseStep 8569151 = 12853727) B12853727
theorem B16048799 : Blo 1668034 16048799 := bstep (se 1 (by rfl) ⟨12036599, by rfl⟩ : syracuseStep 16048799 = 24073199) B24073199
theorem B6333659 : Blo 1668034 6333659 := bstep (se 1 (by rfl) ⟨4750244, by rfl⟩ : syracuseStep 6333659 = 9500489) B9500489
theorem B10692175 : Blo 1668034 10692175 := bstep (se 1 (by rfl) ⟨8019131, by rfl⟩ : syracuseStep 10692175 = 16038263) B16038263
theorem B6334433 : Blo 1668034 6334433 := bstep (se 2 (by rfl) ⟨2375412, by rfl⟩ : syracuseStep 6334433 = 4750825) B4750825
theorem B25684231 : Blo 1668034 25684231 := bstep (se 1 (by rfl) ⟨19263173, by rfl⟩ : syracuseStep 25684231 = 38526347) B38526347
theorem B2673095 : Blo 1668034 2673095 := bstep (se 1 (by rfl) ⟨2004821, by rfl⟩ : syracuseStep 2673095 = 4009643) B4009643
theorem B9505295 : Blo 1668034 9505295 := bstep (se 1 (by rfl) ⟨7128971, by rfl⟩ : syracuseStep 9505295 = 14257943) B14257943
theorem B11414363 : Blo 1668034 11414363 := bstep (se 1 (by rfl) ⟨8560772, by rfl⟩ : syracuseStep 11414363 = 17121545) B17121545
theorem B7130015 : Blo 1668034 7130015 := bstep (se 1 (by rfl) ⟨5347511, by rfl⟩ : syracuseStep 7130015 = 10695023) B10695023
theorem B8023207 : Blo 1668034 8023207 := bstep (se 1 (by rfl) ⟨6017405, by rfl⟩ : syracuseStep 8023207 = 12034811) B12034811
theorem B11422907 : Blo 1668034 11422907 := bstep (se 1 (by rfl) ⟨8567180, by rfl⟩ : syracuseStep 11422907 = 17134361) B17134361
theorem B6016427 : Blo 1668034 6016427 := bstep (se 1 (by rfl) ⟨4512320, by rfl⟩ : syracuseStep 6016427 = 9024641) B9024641
theorem B4755131 : Blo 1668034 4755131 := bstep (se 1 (by rfl) ⟨3566348, by rfl⟩ : syracuseStep 4755131 = 7132697) B7132697
theorem B2854631 : Blo 1668034 2854631 := bstep (se 1 (by rfl) ⟨2140973, by rfl⟩ : syracuseStep 2854631 = 4281947) B4281947
theorem B2502479 : Blo 1668034 2502479 := bstep (se 1 (by rfl) ⟨1876859, by rfl⟩ : syracuseStep 2502479 = 3753719) B3753719
theorem B2502527 : Blo 1668034 2502527 := bstep (se 1 (by rfl) ⟨1876895, by rfl⟩ : syracuseStep 2502527 = 3753791) B3753791
theorem B8449919 : Blo 1668034 8449919 := bstep (se 1 (by rfl) ⟨6337439, by rfl⟩ : syracuseStep 8449919 = 12674879) B12674879
theorem B42790841 : Blo 1668034 42790841 := bstep (se 2 (by rfl) ⟨16046565, by rfl⟩ : syracuseStep 42790841 = 32093131) B32093131
theorem B16035803 : Blo 1668034 16035803 := bstep (se 1 (by rfl) ⟨12026852, by rfl⟩ : syracuseStep 16035803 = 24053705) B24053705
theorem B8450081 : Blo 1668034 8450081 := bstep (se 2 (by rfl) ⟨3168780, by rfl⟩ : syracuseStep 8450081 = 6337561) B6337561
theorem B3756257 : Blo 1668034 3756257 := bstep (se 2 (by rfl) ⟨1408596, by rfl⟩ : syracuseStep 3756257 = 2817193) B2817193
theorem B2502959 : Blo 1668034 2502959 := bstep (se 1 (by rfl) ⟨1877219, by rfl⟩ : syracuseStep 2502959 = 3754439) B3754439
theorem B2503259 : Blo 1668034 2503259 := bstep (se 1 (by rfl) ⟨1877444, by rfl⟩ : syracuseStep 2503259 = 3754889) B3754889
theorem B4510675 : Blo 1668034 4510675 := bstep (se 1 (by rfl) ⟨3383006, by rfl⟩ : syracuseStep 4510675 = 6766013) B6766013
theorem B2815067 : Blo 1668034 2815067 := bstep (se 1 (by rfl) ⟨2111300, by rfl⟩ : syracuseStep 2815067 = 4222601) B4222601
theorem B2815087 : Blo 1668034 2815087 := bstep (se 1 (by rfl) ⟨2111315, by rfl⟩ : syracuseStep 2815087 = 4222631) B4222631
theorem B2503847 : Blo 1668034 2503847 := bstep (se 1 (by rfl) ⟨1877885, by rfl⟩ : syracuseStep 2503847 = 3755771) B3755771
theorem B54121871 : Blo 1668034 54121871 := bstep (se 1 (by rfl) ⟨40591403, by rfl⟩ : syracuseStep 54121871 = 81182807) B81182807
theorem B2504105 : Blo 1668034 2504105 := bstep (se 2 (by rfl) ⟨939039, by rfl⟩ : syracuseStep 2504105 = 1878079) B1878079
theorem B3757481 : Blo 1668034 3757481 := bstep (se 2 (by rfl) ⟨1409055, by rfl⟩ : syracuseStep 3757481 = 2818111) B2818111
theorem B2504159 : Blo 1668034 2504159 := bstep (se 1 (by rfl) ⟨1878119, by rfl⟩ : syracuseStep 2504159 = 3756239) B3756239
theorem B6338047 : Blo 1668034 6338047 := bstep (se 1 (by rfl) ⟨4753535, by rfl⟩ : syracuseStep 6338047 = 9507071) B9507071
theorem B5633711 : Blo 1668034 5633711 := bstep (se 1 (by rfl) ⟨4225283, by rfl⟩ : syracuseStep 5633711 = 8450567) B8450567
theorem B2504519 : Blo 1668034 2504519 := bstep (se 1 (by rfl) ⟨1878389, by rfl⟩ : syracuseStep 2504519 = 3756779) B3756779
theorem B1669031 : Blo 1668034 1669031 := bstep (se 1 (by rfl) ⟨1251773, by rfl⟩ : syracuseStep 1669031 = 2503547) B2503547
theorem B2504615 : Blo 1668034 2504615 := bstep (se 1 (by rfl) ⟨1878461, by rfl⟩ : syracuseStep 2504615 = 3756923) B3756923
theorem B2504699 : Blo 1668034 2504699 := bstep (se 1 (by rfl) ⟨1878524, by rfl⟩ : syracuseStep 2504699 = 3757049) B3757049
theorem B10836031 : Blo 1668034 10836031 := bstep (se 1 (by rfl) ⟨8127023, by rfl⟩ : syracuseStep 10836031 = 16254047) B16254047
theorem B1669327 : Blo 1668034 1669327 := bstep (se 1 (by rfl) ⟨1251995, by rfl⟩ : syracuseStep 1669327 = 2503991) B2503991
theorem B1669359 : Blo 1668034 1669359 := bstep (se 1 (by rfl) ⟨1252019, by rfl⟩ : syracuseStep 1669359 = 2504039) B2504039
theorem B72153503 : Blo 1668034 72153503 := bstep (se 1 (by rfl) ⟨54115127, by rfl⟩ : syracuseStep 72153503 = 108230255) B108230255
theorem B1669883 : Blo 1668034 1669883 := bstep (se 1 (by rfl) ⟨1252412, by rfl⟩ : syracuseStep 1669883 = 2504825) B2504825
theorem B1669919 : Blo 1668034 1669919 := bstep (se 1 (by rfl) ⟨1252439, by rfl⟩ : syracuseStep 1669919 = 2504879) B2504879
theorem B8444735 : Blo 1668034 8444735 := bstep (se 1 (by rfl) ⟨6333551, by rfl⟩ : syracuseStep 8444735 = 12667103) B12667103
theorem B12680225 : Blo 1668034 12680225 := bstep (se 2 (by rfl) ⟨4755084, by rfl⟩ : syracuseStep 12680225 = 9510169) B9510169
theorem B2817335 : Blo 1668034 2817335 := bstep (se 1 (by rfl) ⟨2113001, by rfl⟩ : syracuseStep 2817335 = 4226003) B4226003
theorem B14654915 : Blo 1668034 14654915 := bstep (se 1 (by rfl) ⟨10991186, by rfl⟩ : syracuseStep 14654915 = 21982373) B21982373
theorem B5709359 : Blo 1668034 5709359 := bstep (se 1 (by rfl) ⟨4282019, by rfl⟩ : syracuseStep 5709359 = 8564039) B8564039
theorem B8454131 : Blo 1668034 8454131 := bstep (se 1 (by rfl) ⟨6340598, by rfl⟩ : syracuseStep 8454131 = 12681197) B12681197
theorem B10699199 : Blo 1668034 10699199 := bstep (se 1 (by rfl) ⟨8024399, by rfl⟩ : syracuseStep 10699199 = 16048799) B16048799
theorem B1876711 : Blo 1668034 1876711 := bstep (se 1 (by rfl) ⟨1407533, by rfl⟩ : syracuseStep 1876711 = 2815067) B2815067
theorem B7128253 : Blo 1668034 7128253 := bstep (se 3 (by rfl) ⟨1336547, by rfl⟩ : syracuseStep 7128253 = 2673095) B2673095
theorem B6014233 : Blo 1668034 6014233 := bstep (se 2 (by rfl) ⟨2255337, by rfl⟩ : syracuseStep 6014233 = 4510675) B4510675
theorem B3753449 : Blo 1668034 3753449 := bstep (se 2 (by rfl) ⟨1407543, by rfl⟩ : syracuseStep 3753449 = 2815087) B2815087
theorem B5629823 : Blo 1668034 5629823 := bstep (se 1 (by rfl) ⟨4222367, by rfl⟩ : syracuseStep 5629823 = 8444735) B8444735
theorem B4753343 : Blo 1668034 4753343 := bstep (se 1 (by rfl) ⟨3565007, by rfl⟩ : syracuseStep 4753343 = 7130015) B7130015
theorem B14256233 : Blo 1668034 14256233 := bstep (se 2 (by rfl) ⟨5346087, by rfl⟩ : syracuseStep 14256233 = 10692175) B10692175
theorem B1878223 : Blo 1668034 1878223 := bstep (se 1 (by rfl) ⟨1408667, by rfl⟩ : syracuseStep 1878223 = 2817335) B2817335
theorem B1903087 : Blo 1668034 1903087 := bstep (se 1 (by rfl) ⟨1427315, by rfl⟩ : syracuseStep 1903087 = 2854631) B2854631
theorem B28527227 : Blo 1668034 28527227 := bstep (se 1 (by rfl) ⟨21395420, by rfl⟩ : syracuseStep 28527227 = 42790841) B42790841
theorem B4008683 : Blo 1668034 4008683 := bstep (se 1 (by rfl) ⟨3006512, by rfl⟩ : syracuseStep 4008683 = 6013025) B6013025
theorem B5712767 : Blo 1668034 5712767 := bstep (se 1 (by rfl) ⟨4284575, by rfl⟩ : syracuseStep 5712767 = 8569151) B8569151
theorem B34245641 : Blo 1668034 34245641 := bstep (se 2 (by rfl) ⟨12842115, by rfl⟩ : syracuseStep 34245641 = 25684231) B25684231
theorem B4222439 : Blo 1668034 4222439 := bstep (se 1 (by rfl) ⟨3166829, by rfl⟩ : syracuseStep 4222439 = 6333659) B6333659
theorem B36081247 : Blo 1668034 36081247 := bstep (se 1 (by rfl) ⟨27060935, by rfl⟩ : syracuseStep 36081247 = 54121871) B54121871
theorem B3755807 : Blo 1668034 3755807 := bstep (se 1 (by rfl) ⟨2816855, by rfl⟩ : syracuseStep 3755807 = 5633711) B5633711
theorem B5636087 : Blo 1668034 5636087 := bstep (se 1 (by rfl) ⟨4227065, by rfl⟩ : syracuseStep 5636087 = 8454131) B8454131
theorem B4222955 : Blo 1668034 4222955 := bstep (se 1 (by rfl) ⟨3167216, by rfl⟩ : syracuseStep 4222955 = 6334433) B6334433
theorem B6336863 : Blo 1668034 6336863 := bstep (se 1 (by rfl) ⟨4752647, by rfl⟩ : syracuseStep 6336863 = 9505295) B9505295
theorem B8450729 : Blo 1668034 8450729 := bstep (se 2 (by rfl) ⟨3169023, by rfl⟩ : syracuseStep 8450729 = 6338047) B6338047
theorem B7615271 : Blo 1668034 7615271 := bstep (se 1 (by rfl) ⟨5711453, by rfl⟩ : syracuseStep 7615271 = 11422907) B11422907
theorem B30438301 : Blo 1668034 30438301 := bstep (se 3 (by rfl) ⟨5707181, by rfl⟩ : syracuseStep 30438301 = 11414363) B11414363
theorem B4010951 : Blo 1668034 4010951 := bstep (se 1 (by rfl) ⟨3008213, by rfl⟩ : syracuseStep 4010951 = 6016427) B6016427
theorem B9769943 : Blo 1668034 9769943 := bstep (se 1 (by rfl) ⟨7327457, by rfl⟩ : syracuseStep 9769943 = 14654915) B14654915
theorem B3806239 : Blo 1668034 3806239 := bstep (se 1 (by rfl) ⟨2854679, by rfl⟩ : syracuseStep 3806239 = 5709359) B5709359
theorem B1668319 : Blo 1668034 1668319 := bstep (se 1 (by rfl) ⟨1251239, by rfl⟩ : syracuseStep 1668319 = 2502479) B2502479
theorem B1668351 : Blo 1668034 1668351 := bstep (se 1 (by rfl) ⟨1251263, by rfl⟩ : syracuseStep 1668351 = 2502527) B2502527
theorem B5633279 : Blo 1668034 5633279 := bstep (se 1 (by rfl) ⟨4224959, by rfl⟩ : syracuseStep 5633279 = 8449919) B8449919
theorem B5633387 : Blo 1668034 5633387 := bstep (se 1 (by rfl) ⟨4225040, by rfl⟩ : syracuseStep 5633387 = 8450081) B8450081
theorem B14448041 : Blo 1668034 14448041 := bstep (se 2 (by rfl) ⟨5418015, by rfl⟩ : syracuseStep 14448041 = 10836031) B10836031
theorem B3167657 : Blo 1668034 3167657 := bstep (se 2 (by rfl) ⟨1187871, by rfl⟩ : syracuseStep 3167657 = 2375743) B2375743
theorem B3757535 : Blo 1668034 3757535 := bstep (se 1 (by rfl) ⟨2818151, by rfl⟩ : syracuseStep 3757535 = 5636303) B5636303
theorem B2504171 : Blo 1668034 2504171 := bstep (se 1 (by rfl) ⟨1878128, by rfl⟩ : syracuseStep 2504171 = 3756257) B3756257
theorem B1668639 : Blo 1668034 1668639 := bstep (se 1 (by rfl) ⟨1251479, by rfl⟩ : syracuseStep 1668639 = 2502959) B2502959
theorem B8017481 : Blo 1668034 8017481 := bstep (se 2 (by rfl) ⟨3006555, by rfl⟩ : syracuseStep 8017481 = 6013111) B6013111
theorem B24073949 : Blo 1668034 24073949 := bstep (se 3 (by rfl) ⟨4513865, by rfl⟩ : syracuseStep 24073949 = 9027731) B9027731
theorem B1668839 : Blo 1668034 1668839 := bstep (se 1 (by rfl) ⟨1251629, by rfl⟩ : syracuseStep 1668839 = 2503259) B2503259
theorem B1669231 : Blo 1668034 1669231 := bstep (se 1 (by rfl) ⟨1251923, by rfl⟩ : syracuseStep 1669231 = 2503847) B2503847
theorem B1669403 : Blo 1668034 1669403 := bstep (se 1 (by rfl) ⟨1252052, by rfl⟩ : syracuseStep 1669403 = 2504105) B2504105
theorem B2504987 : Blo 1668034 2504987 := bstep (se 1 (by rfl) ⟨1878740, by rfl⟩ : syracuseStep 2504987 = 3757481) B3757481
theorem B1669439 : Blo 1668034 1669439 := bstep (se 1 (by rfl) ⟨1252079, by rfl⟩ : syracuseStep 1669439 = 2504159) B2504159
theorem B1669679 : Blo 1668034 1669679 := bstep (se 1 (by rfl) ⟨1252259, by rfl⟩ : syracuseStep 1669679 = 2504519) B2504519
theorem B1669743 : Blo 1668034 1669743 := bstep (se 1 (by rfl) ⟨1252307, by rfl⟩ : syracuseStep 1669743 = 2504615) B2504615
theorem B1669799 : Blo 1668034 1669799 := bstep (se 1 (by rfl) ⟨1252349, by rfl⟩ : syracuseStep 1669799 = 2504699) B2504699
theorem B10697609 : Blo 1668034 10697609 := bstep (se 2 (by rfl) ⟨4011603, by rfl⟩ : syracuseStep 10697609 = 8023207) B8023207
theorem B48102335 : Blo 1668034 48102335 := bstep (se 1 (by rfl) ⟨36076751, by rfl⟩ : syracuseStep 48102335 = 72153503) B72153503
theorem B8453483 : Blo 1668034 8453483 := bstep (se 1 (by rfl) ⟨6340112, by rfl⟩ : syracuseStep 8453483 = 12680225) B12680225
theorem B3170087 : Blo 1668034 3170087 := bstep (se 1 (by rfl) ⟨2377565, by rfl⟩ : syracuseStep 3170087 = 4755131) B4755131
theorem B10690535 : Blo 1668034 10690535 := bstep (se 1 (by rfl) ⟨8017901, by rfl⟩ : syracuseStep 10690535 = 16035803) B16035803
theorem B6513295 : Blo 1668034 6513295 := bstep (se 1 (by rfl) ⟨4884971, by rfl⟩ : syracuseStep 6513295 = 9769943) B9769943
theorem B16049299 : Blo 1668034 16049299 := bstep (se 1 (by rfl) ⟨12036974, by rfl⟩ : syracuseStep 16049299 = 24073949) B24073949
theorem B40584401 : Blo 1668034 40584401 := bstep (se 2 (by rfl) ⟨15219150, by rfl⟩ : syracuseStep 40584401 = 30438301) B30438301
theorem B3753215 : Blo 1668034 3753215 := bstep (se 1 (by rfl) ⟨2814911, by rfl⟩ : syracuseStep 3753215 = 5629823) B5629823
theorem B9504155 : Blo 1668034 9504155 := bstep (se 1 (by rfl) ⟨7128116, by rfl⟩ : syracuseStep 9504155 = 14256233) B14256233
theorem B9504337 : Blo 1668034 9504337 := bstep (se 2 (by rfl) ⟨3564126, by rfl⟩ : syracuseStep 9504337 = 7128253) B7128253
theorem B2672455 : Blo 1668034 2672455 := bstep (se 1 (by rfl) ⟨2004341, by rfl⟩ : syracuseStep 2672455 = 4008683) B4008683
theorem B2673967 : Blo 1668034 2673967 := bstep (se 1 (by rfl) ⟨2005475, by rfl⟩ : syracuseStep 2673967 = 4010951) B4010951
theorem B3755519 : Blo 1668034 3755519 := bstep (se 1 (by rfl) ⟨2816639, by rfl⟩ : syracuseStep 3755519 = 5633279) B5633279
theorem B3755591 : Blo 1668034 3755591 := bstep (se 1 (by rfl) ⟨2816693, by rfl⟩ : syracuseStep 3755591 = 5633387) B5633387
theorem B2502281 : Blo 1668034 2502281 := bstep (se 2 (by rfl) ⟨938355, by rfl⟩ : syracuseStep 2502281 = 1876711) B1876711
theorem B2502299 : Blo 1668034 2502299 := bstep (se 1 (by rfl) ⟨1876724, by rfl⟩ : syracuseStep 2502299 = 3753449) B3753449
theorem B5344987 : Blo 1668034 5344987 := bstep (se 1 (by rfl) ⟨4008740, by rfl⟩ : syracuseStep 5344987 = 8017481) B8017481
theorem B5074985 : Blo 1668034 5074985 := bstep (se 2 (by rfl) ⟨1903119, by rfl⟩ : syracuseStep 5074985 = 3806239) B3806239
theorem B32075909 : Blo 1668034 32075909 := bstep (se 4 (by rfl) ⟨3007116, by rfl⟩ : syracuseStep 32075909 = 6014233) B6014233
theorem B19018151 : Blo 1668034 19018151 := bstep (se 1 (by rfl) ⟨14263613, by rfl⟩ : syracuseStep 19018151 = 28527227) B28527227
theorem B7131739 : Blo 1668034 7131739 := bstep (se 1 (by rfl) ⟨5348804, by rfl⟩ : syracuseStep 7131739 = 10697609) B10697609
theorem B32068223 : Blo 1668034 32068223 := bstep (se 1 (by rfl) ⟨24051167, by rfl⟩ : syracuseStep 32068223 = 48102335) B48102335
theorem B48108329 : Blo 1668034 48108329 := bstep (se 2 (by rfl) ⟨18040623, by rfl⟩ : syracuseStep 48108329 = 36081247) B36081247
theorem B2814959 : Blo 1668034 2814959 := bstep (se 1 (by rfl) ⟨2111219, by rfl⟩ : syracuseStep 2814959 = 4222439) B4222439
theorem B2503871 : Blo 1668034 2503871 := bstep (se 1 (by rfl) ⟨1877903, by rfl⟩ : syracuseStep 2503871 = 3755807) B3755807
theorem B2815303 : Blo 1668034 2815303 := bstep (se 1 (by rfl) ⟨2111477, by rfl⟩ : syracuseStep 2815303 = 4222955) B4222955
theorem B3757391 : Blo 1668034 3757391 := bstep (se 1 (by rfl) ⟨2818043, by rfl⟩ : syracuseStep 3757391 = 5636087) B5636087
theorem B4224575 : Blo 1668034 4224575 := bstep (se 1 (by rfl) ⟨3168431, by rfl⟩ : syracuseStep 4224575 = 6336863) B6336863
theorem B2504297 : Blo 1668034 2504297 := bstep (se 2 (by rfl) ⟨939111, by rfl⟩ : syracuseStep 2504297 = 1878223) B1878223
theorem B7132799 : Blo 1668034 7132799 := bstep (se 1 (by rfl) ⟨5349599, by rfl⟩ : syracuseStep 7132799 = 10699199) B10699199
theorem B5633819 : Blo 1668034 5633819 := bstep (se 1 (by rfl) ⟨4225364, by rfl⟩ : syracuseStep 5633819 = 8450729) B8450729
theorem B5076847 : Blo 1668034 5076847 := bstep (se 1 (by rfl) ⟨3807635, by rfl⟩ : syracuseStep 5076847 = 7615271) B7615271
theorem B9632027 : Blo 1668034 9632027 := bstep (se 1 (by rfl) ⟨7224020, by rfl⟩ : syracuseStep 9632027 = 14448041) B14448041
theorem B2111771 : Blo 1668034 2111771 := bstep (se 1 (by rfl) ⟨1583828, by rfl⟩ : syracuseStep 2111771 = 3167657) B3167657
theorem B2505023 : Blo 1668034 2505023 := bstep (se 1 (by rfl) ⟨1878767, by rfl⟩ : syracuseStep 2505023 = 3757535) B3757535
theorem B1669447 : Blo 1668034 1669447 := bstep (se 1 (by rfl) ⟨1252085, by rfl⟩ : syracuseStep 1669447 = 2504171) B2504171
theorem B3168895 : Blo 1668034 3168895 := bstep (se 1 (by rfl) ⟨2376671, by rfl⟩ : syracuseStep 3168895 = 4753343) B4753343
theorem B1669991 : Blo 1668034 1669991 := bstep (se 1 (by rfl) ⟨1252493, by rfl⟩ : syracuseStep 1669991 = 2504987) B2504987
theorem B3808511 : Blo 1668034 3808511 := bstep (se 1 (by rfl) ⟨2856383, by rfl⟩ : syracuseStep 3808511 = 5712767) B5712767
theorem B22830427 : Blo 1668034 22830427 := bstep (se 1 (by rfl) ⟨17122820, by rfl⟩ : syracuseStep 22830427 = 34245641) B34245641
theorem B5635655 : Blo 1668034 5635655 := bstep (se 1 (by rfl) ⟨4226741, by rfl⟩ : syracuseStep 5635655 = 8453483) B8453483
theorem B2113391 : Blo 1668034 2113391 := bstep (se 1 (by rfl) ⟨1585043, by rfl⟩ : syracuseStep 2113391 = 3170087) B3170087
theorem B10149797 : Blo 1668034 10149797 := bstep (se 4 (by rfl) ⟨951543, by rfl⟩ : syracuseStep 10149797 = 1903087) B1903087
theorem B7127023 : Blo 1668034 7127023 := bstep (se 1 (by rfl) ⟨5345267, by rfl⟩ : syracuseStep 7127023 = 10690535) B10690535
theorem B13533293 : Blo 1668034 13533293 := bstep (se 3 (by rfl) ⟨2537492, by rfl⟩ : syracuseStep 13533293 = 5074985) B5074985
theorem B32072219 : Blo 1668034 32072219 := bstep (se 1 (by rfl) ⟨24054164, by rfl⟩ : syracuseStep 32072219 = 48108329) B48108329
theorem B1876639 : Blo 1668034 1876639 := bstep (se 1 (by rfl) ⟨1407479, by rfl⟩ : syracuseStep 1876639 = 2814959) B2814959
theorem B21399065 : Blo 1668034 21399065 := bstep (se 2 (by rfl) ⟨8024649, by rfl⟩ : syracuseStep 21399065 = 16049299) B16049299
theorem B3565289 : Blo 1668034 3565289 := bstep (se 2 (by rfl) ⟨1336983, by rfl⟩ : syracuseStep 3565289 = 2673967) B2673967
theorem B3753737 : Blo 1668034 3753737 := bstep (se 2 (by rfl) ⟨1407651, by rfl⟩ : syracuseStep 3753737 = 2815303) B2815303
theorem B6769129 : Blo 1668034 6769129 := bstep (se 2 (by rfl) ⟨2538423, by rfl⟩ : syracuseStep 6769129 = 5076847) B5076847
theorem B21383939 : Blo 1668034 21383939 := bstep (se 1 (by rfl) ⟨16037954, by rfl⟩ : syracuseStep 21383939 = 32075909) B32075909
theorem B5631389 : Blo 1668034 5631389 := bstep (se 3 (by rfl) ⟨1055885, by rfl⟩ : syracuseStep 5631389 = 2111771) B2111771
theorem B2502143 : Blo 1668034 2502143 := bstep (se 1 (by rfl) ⟨1876607, by rfl⟩ : syracuseStep 2502143 = 3753215) B3753215
theorem B6336103 : Blo 1668034 6336103 := bstep (se 1 (by rfl) ⟨4752077, by rfl⟩ : syracuseStep 6336103 = 9504155) B9504155
theorem B4755199 : Blo 1668034 4755199 := bstep (se 1 (by rfl) ⟨3566399, by rfl⟩ : syracuseStep 4755199 = 7132799) B7132799
theorem B3755879 : Blo 1668034 3755879 := bstep (se 1 (by rfl) ⟨2816909, by rfl⟩ : syracuseStep 3755879 = 5633819) B5633819
theorem B2503679 : Blo 1668034 2503679 := bstep (se 1 (by rfl) ⟨1877759, by rfl⟩ : syracuseStep 2503679 = 3755519) B3755519
theorem B2503727 : Blo 1668034 2503727 := bstep (se 1 (by rfl) ⟨1877795, by rfl⟩ : syracuseStep 2503727 = 3755591) B3755591
theorem B3757103 : Blo 1668034 3757103 := bstep (se 1 (by rfl) ⟨2817827, by rfl⟩ : syracuseStep 3757103 = 5635655) B5635655
theorem B1668187 : Blo 1668034 1668187 := bstep (se 1 (by rfl) ⟨1251140, by rfl⟩ : syracuseStep 1668187 = 2502281) B2502281
theorem B1668199 : Blo 1668034 1668199 := bstep (se 1 (by rfl) ⟨1251149, by rfl⟩ : syracuseStep 1668199 = 2502299) B2502299
theorem B12678767 : Blo 1668034 12678767 := bstep (se 1 (by rfl) ⟨9509075, by rfl⟩ : syracuseStep 12678767 = 19018151) B19018151
theorem B21378815 : Blo 1668034 21378815 := bstep (se 1 (by rfl) ⟨16034111, by rfl⟩ : syracuseStep 21378815 = 32068223) B32068223
theorem B9508985 : Blo 1668034 9508985 := bstep (se 2 (by rfl) ⟨3565869, by rfl⟩ : syracuseStep 9508985 = 7131739) B7131739
theorem B1669247 : Blo 1668034 1669247 := bstep (se 1 (by rfl) ⟨1251935, by rfl⟩ : syracuseStep 1669247 = 2503871) B2503871
theorem B27056267 : Blo 1668034 27056267 := bstep (se 1 (by rfl) ⟨20292200, by rfl⟩ : syracuseStep 27056267 = 40584401) B40584401
theorem B4225193 : Blo 1668034 4225193 := bstep (se 2 (by rfl) ⟨1584447, by rfl⟩ : syracuseStep 4225193 = 3168895) B3168895
theorem B2504927 : Blo 1668034 2504927 := bstep (se 1 (by rfl) ⟨1878695, by rfl⟩ : syracuseStep 2504927 = 3757391) B3757391
theorem B2816383 : Blo 1668034 2816383 := bstep (se 1 (by rfl) ⟨2112287, by rfl⟩ : syracuseStep 2816383 = 4224575) B4224575
theorem B1669531 : Blo 1668034 1669531 := bstep (se 1 (by rfl) ⟨1252148, by rfl⟩ : syracuseStep 1669531 = 2504297) B2504297
theorem B555801173 : Blo 1668034 555801173 := bstep (se 8 (by rfl) ⟨3256647, by rfl⟩ : syracuseStep 555801173 = 6513295) B6513295
theorem B6421351 : Blo 1668034 6421351 := bstep (se 1 (by rfl) ⟨4816013, by rfl⟩ : syracuseStep 6421351 = 9632027) B9632027
theorem B1670015 : Blo 1668034 1670015 := bstep (se 1 (by rfl) ⟨1252511, by rfl⟩ : syracuseStep 1670015 = 2505023) B2505023
theorem B30440569 : Blo 1668034 30440569 := bstep (se 2 (by rfl) ⟨11415213, by rfl⟩ : syracuseStep 30440569 = 22830427) B22830427
theorem B12672449 : Blo 1668034 12672449 := bstep (se 2 (by rfl) ⟨4752168, by rfl⟩ : syracuseStep 12672449 = 9504337) B9504337
theorem B2539007 : Blo 1668034 2539007 := bstep (se 1 (by rfl) ⟨1904255, by rfl⟩ : syracuseStep 2539007 = 3808511) B3808511
theorem B7126649 : Blo 1668034 7126649 := bstep (se 2 (by rfl) ⟨2672493, by rfl⟩ : syracuseStep 7126649 = 5344987) B5344987
theorem B5635709 : Blo 1668034 5635709 := bstep (se 3 (by rfl) ⟨1056695, by rfl⟩ : syracuseStep 5635709 = 2113391) B2113391
theorem B3563273 : Blo 1668034 3563273 := bstep (se 2 (by rfl) ⟨1336227, by rfl⟩ : syracuseStep 3563273 = 2672455) B2672455
theorem B27066125 : Blo 1668034 27066125 := bstep (se 3 (by rfl) ⟨5074898, by rfl⟩ : syracuseStep 27066125 = 10149797) B10149797
theorem B9502697 : Blo 1668034 9502697 := bstep (se 2 (by rfl) ⟨3563511, by rfl⟩ : syracuseStep 9502697 = 7127023) B7127023
theorem B21381479 : Blo 1668034 21381479 := bstep (se 1 (by rfl) ⟨16036109, by rfl⟩ : syracuseStep 21381479 = 32072219) B32072219
theorem B8561801 : Blo 1668034 8561801 := bstep (se 2 (by rfl) ⟨3210675, by rfl⟩ : syracuseStep 8561801 = 6421351) B6421351
theorem B2376859 : Blo 1668034 2376859 := bstep (se 1 (by rfl) ⟨1782644, by rfl⟩ : syracuseStep 2376859 = 3565289) B3565289
theorem B370534115 : Blo 1668034 370534115 := bstep (se 1 (by rfl) ⟨277900586, by rfl⟩ : syracuseStep 370534115 = 555801173) B555801173
theorem B14255959 : Blo 1668034 14255959 := bstep (se 1 (by rfl) ⟨10691969, by rfl⟩ : syracuseStep 14255959 = 21383939) B21383939
theorem B8448137 : Blo 1668034 8448137 := bstep (se 2 (by rfl) ⟨3168051, by rfl⟩ : syracuseStep 8448137 = 6336103) B6336103
theorem B3754259 : Blo 1668034 3754259 := bstep (se 1 (by rfl) ⟨2815694, by rfl⟩ : syracuseStep 3754259 = 5631389) B5631389
theorem B8448299 : Blo 1668034 8448299 := bstep (se 1 (by rfl) ⟨6336224, by rfl⟩ : syracuseStep 8448299 = 12672449) B12672449
theorem B6335131 : Blo 1668034 6335131 := bstep (se 1 (by rfl) ⟨4751348, by rfl⟩ : syracuseStep 6335131 = 9502697) B9502697
theorem B9022195 : Blo 1668034 9022195 := bstep (se 1 (by rfl) ⟨6766646, by rfl⟩ : syracuseStep 9022195 = 13533293) B13533293
theorem B3755177 : Blo 1668034 3755177 := bstep (se 2 (by rfl) ⟨1408191, by rfl⟩ : syracuseStep 3755177 = 2816383) B2816383
theorem B2502185 : Blo 1668034 2502185 := bstep (se 2 (by rfl) ⟨938319, by rfl⟩ : syracuseStep 2502185 = 1876639) B1876639
theorem B14266043 : Blo 1668034 14266043 := bstep (se 1 (by rfl) ⟨10699532, by rfl⟩ : syracuseStep 14266043 = 21399065) B21399065
theorem B2502491 : Blo 1668034 2502491 := bstep (se 1 (by rfl) ⟨1876868, by rfl⟩ : syracuseStep 2502491 = 3753737) B3753737
theorem B40587425 : Blo 1668034 40587425 := bstep (se 2 (by rfl) ⟨15220284, by rfl⟩ : syracuseStep 40587425 = 30440569) B30440569
theorem B1668095 : Blo 1668034 1668095 := bstep (se 1 (by rfl) ⟨1251071, by rfl⟩ : syracuseStep 1668095 = 2502143) B2502143
theorem B1692671 : Blo 1668034 1692671 := bstep (se 1 (by rfl) ⟨1269503, by rfl⟩ : syracuseStep 1692671 = 2539007) B2539007
theorem B3757139 : Blo 1668034 3757139 := bstep (se 1 (by rfl) ⟨2817854, by rfl⟩ : syracuseStep 3757139 = 5635709) B5635709
theorem B18044083 : Blo 1668034 18044083 := bstep (se 1 (by rfl) ⟨13533062, by rfl⟩ : syracuseStep 18044083 = 27066125) B27066125
theorem B2503919 : Blo 1668034 2503919 := bstep (se 1 (by rfl) ⟨1877939, by rfl⟩ : syracuseStep 2503919 = 3755879) B3755879
theorem B9025505 : Blo 1668034 9025505 := bstep (se 2 (by rfl) ⟨3384564, by rfl⟩ : syracuseStep 9025505 = 6769129) B6769129
theorem B1669119 : Blo 1668034 1669119 := bstep (se 1 (by rfl) ⟨1251839, by rfl⟩ : syracuseStep 1669119 = 2503679) B2503679
theorem B1669151 : Blo 1668034 1669151 := bstep (se 1 (by rfl) ⟨1251863, by rfl⟩ : syracuseStep 1669151 = 2503727) B2503727
theorem B2504735 : Blo 1668034 2504735 := bstep (se 1 (by rfl) ⟨1878551, by rfl⟩ : syracuseStep 2504735 = 3757103) B3757103
theorem B8452511 : Blo 1668034 8452511 := bstep (se 1 (by rfl) ⟨6339383, by rfl⟩ : syracuseStep 8452511 = 12678767) B12678767
theorem B14252543 : Blo 1668034 14252543 := bstep (se 1 (by rfl) ⟨10689407, by rfl⟩ : syracuseStep 14252543 = 21378815) B21378815
theorem B6339323 : Blo 1668034 6339323 := bstep (se 1 (by rfl) ⟨4754492, by rfl⟩ : syracuseStep 6339323 = 9508985) B9508985
theorem B18037511 : Blo 1668034 18037511 := bstep (se 1 (by rfl) ⟨13528133, by rfl⟩ : syracuseStep 18037511 = 27056267) B27056267
theorem B2816795 : Blo 1668034 2816795 := bstep (se 1 (by rfl) ⟨2112596, by rfl⟩ : syracuseStep 2816795 = 4225193) B4225193
theorem B1669951 : Blo 1668034 1669951 := bstep (se 1 (by rfl) ⟨1252463, by rfl⟩ : syracuseStep 1669951 = 2504927) B2504927
theorem B6340265 : Blo 1668034 6340265 := bstep (se 2 (by rfl) ⟨2377599, by rfl⟩ : syracuseStep 6340265 = 4755199) B4755199
theorem B4751099 : Blo 1668034 4751099 := bstep (se 1 (by rfl) ⟨3563324, by rfl⟩ : syracuseStep 4751099 = 7126649) B7126649
theorem B2375515 : Blo 1668034 2375515 := bstep (se 1 (by rfl) ⟨1781636, by rfl⟩ : syracuseStep 2375515 = 3563273) B3563273
theorem B27058283 : Blo 1668034 27058283 := bstep (se 1 (by rfl) ⟨20293712, by rfl⟩ : syracuseStep 27058283 = 40587425) B40587425
theorem B14254319 : Blo 1668034 14254319 := bstep (se 1 (by rfl) ⟨10690739, by rfl⟩ : syracuseStep 14254319 = 21381479) B21381479
theorem B22831469 : Blo 1668034 22831469 := bstep (se 3 (by rfl) ⟨4280900, by rfl⟩ : syracuseStep 22831469 = 8561801) B8561801
theorem B8446841 : Blo 1668034 8446841 := bstep (se 2 (by rfl) ⟨3167565, by rfl⟩ : syracuseStep 8446841 = 6335131) B6335131
theorem B247022743 : Blo 1668034 247022743 := bstep (se 1 (by rfl) ⟨185267057, by rfl⟩ : syracuseStep 247022743 = 370534115) B370534115
theorem B1877863 : Blo 1668034 1877863 := bstep (se 1 (by rfl) ⟨1408397, by rfl⟩ : syracuseStep 1877863 = 2816795) B2816795
theorem B19007945 : Blo 1668034 19007945 := bstep (se 2 (by rfl) ⟨7127979, by rfl⟩ : syracuseStep 19007945 = 14255959) B14255959
theorem B6017003 : Blo 1668034 6017003 := bstep (se 1 (by rfl) ⟨4512752, by rfl⟩ : syracuseStep 6017003 = 9025505) B9025505
theorem B5632091 : Blo 1668034 5632091 := bstep (se 1 (by rfl) ⟨4224068, by rfl⟩ : syracuseStep 5632091 = 8448137) B8448137
theorem B2502839 : Blo 1668034 2502839 := bstep (se 1 (by rfl) ⟨1877129, by rfl⟩ : syracuseStep 2502839 = 3754259) B3754259
theorem B5632199 : Blo 1668034 5632199 := bstep (se 1 (by rfl) ⟨4224149, by rfl⟩ : syracuseStep 5632199 = 8448299) B8448299
theorem B2503451 : Blo 1668034 2503451 := bstep (se 1 (by rfl) ⟨1877588, by rfl⟩ : syracuseStep 2503451 = 3755177) B3755177
theorem B1668123 : Blo 1668034 1668123 := bstep (se 1 (by rfl) ⟨1251092, by rfl⟩ : syracuseStep 1668123 = 2502185) B2502185
theorem B3167353 : Blo 1668034 3167353 := bstep (se 2 (by rfl) ⟨1187757, by rfl⟩ : syracuseStep 3167353 = 2375515) B2375515
theorem B3167399 : Blo 1668034 3167399 := bstep (se 1 (by rfl) ⟨2375549, by rfl⟩ : syracuseStep 3167399 = 4751099) B4751099
theorem B1668327 : Blo 1668034 1668327 := bstep (se 1 (by rfl) ⟨1251245, by rfl⟩ : syracuseStep 1668327 = 2502491) B2502491
theorem B2504759 : Blo 1668034 2504759 := bstep (se 1 (by rfl) ⟨1878569, by rfl⟩ : syracuseStep 2504759 = 3757139) B3757139
theorem B1669279 : Blo 1668034 1669279 := bstep (se 1 (by rfl) ⟨1251959, by rfl⟩ : syracuseStep 1669279 = 2503919) B2503919
theorem B48118373 : Blo 1668034 48118373 := bstep (se 4 (by rfl) ⟨4511097, by rfl⟩ : syracuseStep 48118373 = 9022195) B9022195
theorem B1669823 : Blo 1668034 1669823 := bstep (se 1 (by rfl) ⟨1252367, by rfl⟩ : syracuseStep 1669823 = 2504735) B2504735
theorem B3169145 : Blo 1668034 3169145 := bstep (se 2 (by rfl) ⟨1188429, by rfl⟩ : syracuseStep 3169145 = 2376859) B2376859
theorem B24058777 : Blo 1668034 24058777 := bstep (se 2 (by rfl) ⟨9022041, by rfl⟩ : syracuseStep 24058777 = 18044083) B18044083
theorem B5635007 : Blo 1668034 5635007 := bstep (se 1 (by rfl) ⟨4226255, by rfl⟩ : syracuseStep 5635007 = 8452511) B8452511
theorem B9501695 : Blo 1668034 9501695 := bstep (se 1 (by rfl) ⟨7126271, by rfl⟩ : syracuseStep 9501695 = 14252543) B14252543
theorem B4226215 : Blo 1668034 4226215 := bstep (se 1 (by rfl) ⟨3169661, by rfl⟩ : syracuseStep 4226215 = 6339323) B6339323
theorem B12025007 : Blo 1668034 12025007 := bstep (se 1 (by rfl) ⟨9018755, by rfl⟩ : syracuseStep 12025007 = 18037511) B18037511
theorem B4226843 : Blo 1668034 4226843 := bstep (se 1 (by rfl) ⟨3170132, by rfl⟩ : syracuseStep 4226843 = 6340265) B6340265
theorem B9510695 : Blo 1668034 9510695 := bstep (se 1 (by rfl) ⟨7133021, by rfl⟩ : syracuseStep 9510695 = 14266043) B14266043
theorem B4513789 : Blo 1668034 4513789 := bstep (se 3 (by rfl) ⟨846335, by rfl⟩ : syracuseStep 4513789 = 1692671) B1692671
theorem B18038855 : Blo 1668034 18038855 := bstep (se 1 (by rfl) ⟨13529141, by rfl⟩ : syracuseStep 18038855 = 27058283) B27058283
theorem B9502879 : Blo 1668034 9502879 := bstep (se 1 (by rfl) ⟨7127159, by rfl⟩ : syracuseStep 9502879 = 14254319) B14254319
theorem B15220979 : Blo 1668034 15220979 := bstep (se 1 (by rfl) ⟨11415734, by rfl⟩ : syracuseStep 15220979 = 22831469) B22831469
theorem B6334463 : Blo 1668034 6334463 := bstep (se 1 (by rfl) ⟨4750847, by rfl⟩ : syracuseStep 6334463 = 9501695) B9501695
theorem B3754727 : Blo 1668034 3754727 := bstep (se 1 (by rfl) ⟨2816045, by rfl⟩ : syracuseStep 3754727 = 5632091) B5632091
theorem B3754799 : Blo 1668034 3754799 := bstep (se 1 (by rfl) ⟨2816099, by rfl⟩ : syracuseStep 3754799 = 5632199) B5632199
theorem B5631227 : Blo 1668034 5631227 := bstep (se 1 (by rfl) ⟨4223420, by rfl⟩ : syracuseStep 5631227 = 8446841) B8446841
theorem B4223137 : Blo 1668034 4223137 := bstep (se 2 (by rfl) ⟨1583676, by rfl⟩ : syracuseStep 4223137 = 3167353) B3167353
theorem B329363657 : Blo 1668034 329363657 := bstep (se 2 (by rfl) ⟨123511371, by rfl⟩ : syracuseStep 329363657 = 247022743) B247022743
theorem B3756671 : Blo 1668034 3756671 := bstep (se 1 (by rfl) ⟨2817503, by rfl⟩ : syracuseStep 3756671 = 5635007) B5635007
theorem B8016671 : Blo 1668034 8016671 := bstep (se 1 (by rfl) ⟨6012503, by rfl⟩ : syracuseStep 8016671 = 12025007) B12025007
theorem B8451053 : Blo 1668034 8451053 := bstep (se 3 (by rfl) ⟨1584572, by rfl⟩ : syracuseStep 8451053 = 3169145) B3169145
theorem B2503817 : Blo 1668034 2503817 := bstep (se 2 (by rfl) ⟨938931, by rfl⟩ : syracuseStep 2503817 = 1877863) B1877863
theorem B4011335 : Blo 1668034 4011335 := bstep (se 1 (by rfl) ⟨3008501, by rfl⟩ : syracuseStep 4011335 = 6017003) B6017003
theorem B6018385 : Blo 1668034 6018385 := bstep (se 2 (by rfl) ⟨2256894, by rfl⟩ : syracuseStep 6018385 = 4513789) B4513789
theorem B1668559 : Blo 1668034 1668559 := bstep (se 1 (by rfl) ⟨1251419, by rfl⟩ : syracuseStep 1668559 = 2502839) B2502839
theorem B1668967 : Blo 1668034 1668967 := bstep (se 1 (by rfl) ⟨1251725, by rfl⟩ : syracuseStep 1668967 = 2503451) B2503451
theorem B2111599 : Blo 1668034 2111599 := bstep (se 1 (by rfl) ⟨1583699, by rfl⟩ : syracuseStep 2111599 = 3167399) B3167399
theorem B32078369 : Blo 1668034 32078369 := bstep (se 2 (by rfl) ⟨12029388, by rfl⟩ : syracuseStep 32078369 = 24058777) B24058777
theorem B1669839 : Blo 1668034 1669839 := bstep (se 1 (by rfl) ⟨1252379, by rfl⟩ : syracuseStep 1669839 = 2504759) B2504759
theorem B5634953 : Blo 1668034 5634953 := bstep (se 2 (by rfl) ⟨2113107, by rfl⟩ : syracuseStep 5634953 = 4226215) B4226215
theorem B12671963 : Blo 1668034 12671963 := bstep (se 1 (by rfl) ⟨9503972, by rfl⟩ : syracuseStep 12671963 = 19007945) B19007945
theorem B32078915 : Blo 1668034 32078915 := bstep (se 1 (by rfl) ⟨24059186, by rfl⟩ : syracuseStep 32078915 = 48118373) B48118373
theorem B2817895 : Blo 1668034 2817895 := bstep (se 1 (by rfl) ⟨2113421, by rfl⟩ : syracuseStep 2817895 = 4226843) B4226843
theorem B6340463 : Blo 1668034 6340463 := bstep (se 1 (by rfl) ⟨4755347, by rfl⟩ : syracuseStep 6340463 = 9510695) B9510695
theorem B12025903 : Blo 1668034 12025903 := bstep (se 1 (by rfl) ⟨9019427, by rfl⟩ : syracuseStep 12025903 = 18038855) B18038855
theorem B8447975 : Blo 1668034 8447975 := bstep (se 1 (by rfl) ⟨6335981, by rfl⟩ : syracuseStep 8447975 = 12671963) B12671963
theorem B3754151 : Blo 1668034 3754151 := bstep (se 1 (by rfl) ⟨2815613, by rfl⟩ : syracuseStep 3754151 = 5631227) B5631227
theorem B5630849 : Blo 1668034 5630849 := bstep (se 2 (by rfl) ⟨2111568, by rfl⟩ : syracuseStep 5630849 = 4223137) B4223137
theorem B2674223 : Blo 1668034 2674223 := bstep (se 1 (by rfl) ⟨2005667, by rfl⟩ : syracuseStep 2674223 = 4011335) B4011335
theorem B4222975 : Blo 1668034 4222975 := bstep (se 1 (by rfl) ⟨3167231, by rfl⟩ : syracuseStep 4222975 = 6334463) B6334463
theorem B21385579 : Blo 1668034 21385579 := bstep (se 1 (by rfl) ⟨16039184, by rfl⟩ : syracuseStep 21385579 = 32078369) B32078369
theorem B8024513 : Blo 1668034 8024513 := bstep (se 2 (by rfl) ⟨3009192, by rfl⟩ : syracuseStep 8024513 = 6018385) B6018385
theorem B2503151 : Blo 1668034 2503151 := bstep (se 1 (by rfl) ⟨1877363, by rfl⟩ : syracuseStep 2503151 = 3754727) B3754727
theorem B2503199 : Blo 1668034 2503199 := bstep (se 1 (by rfl) ⟨1877399, by rfl⟩ : syracuseStep 2503199 = 3754799) B3754799
theorem B3756635 : Blo 1668034 3756635 := bstep (se 1 (by rfl) ⟨2817476, by rfl⟩ : syracuseStep 3756635 = 5634953) B5634953
theorem B21385943 : Blo 1668034 21385943 := bstep (se 1 (by rfl) ⟨16039457, by rfl⟩ : syracuseStep 21385943 = 32078915) B32078915
theorem B21377789 : Blo 1668034 21377789 := bstep (se 3 (by rfl) ⟨4008335, by rfl⟩ : syracuseStep 21377789 = 8016671) B8016671
theorem B3757193 : Blo 1668034 3757193 := bstep (se 2 (by rfl) ⟨1408947, by rfl⟩ : syracuseStep 3757193 = 2817895) B2817895
theorem B219575771 : Blo 1668034 219575771 := bstep (se 1 (by rfl) ⟨164681828, by rfl⟩ : syracuseStep 219575771 = 329363657) B329363657
theorem B2815465 : Blo 1668034 2815465 := bstep (se 2 (by rfl) ⟨1055799, by rfl⟩ : syracuseStep 2815465 = 2111599) B2111599
theorem B10147319 : Blo 1668034 10147319 := bstep (se 1 (by rfl) ⟨7610489, by rfl⟩ : syracuseStep 10147319 = 15220979) B15220979
theorem B12670505 : Blo 1668034 12670505 := bstep (se 2 (by rfl) ⟨4751439, by rfl⟩ : syracuseStep 12670505 = 9502879) B9502879
theorem B2504447 : Blo 1668034 2504447 := bstep (se 1 (by rfl) ⟨1878335, by rfl⟩ : syracuseStep 2504447 = 3756671) B3756671
theorem B5634035 : Blo 1668034 5634035 := bstep (se 1 (by rfl) ⟨4225526, by rfl⟩ : syracuseStep 5634035 = 8451053) B8451053
theorem B1669211 : Blo 1668034 1669211 := bstep (se 1 (by rfl) ⟨1251908, by rfl⟩ : syracuseStep 1669211 = 2503817) B2503817
theorem B4226975 : Blo 1668034 4226975 := bstep (se 1 (by rfl) ⟨3170231, by rfl⟩ : syracuseStep 4226975 = 6340463) B6340463
theorem B146383847 : Blo 1668034 146383847 := bstep (se 1 (by rfl) ⟨109787885, by rfl⟩ : syracuseStep 146383847 = 219575771) B219575771
theorem B8447003 : Blo 1668034 8447003 := bstep (se 1 (by rfl) ⟨6335252, by rfl⟩ : syracuseStep 8447003 = 12670505) B12670505
theorem B21398701 : Blo 1668034 21398701 := bstep (se 3 (by rfl) ⟨4012256, by rfl⟩ : syracuseStep 21398701 = 8024513) B8024513
theorem B3753899 : Blo 1668034 3753899 := bstep (se 1 (by rfl) ⟨2815424, by rfl⟩ : syracuseStep 3753899 = 5630849) B5630849
theorem B3753953 : Blo 1668034 3753953 := bstep (se 2 (by rfl) ⟨1407732, by rfl⟩ : syracuseStep 3753953 = 2815465) B2815465
theorem B5630633 : Blo 1668034 5630633 := bstep (se 2 (by rfl) ⟨2111487, by rfl⟩ : syracuseStep 5630633 = 4222975) B4222975
theorem B16034537 : Blo 1668034 16034537 := bstep (se 2 (by rfl) ⟨6012951, by rfl⟩ : syracuseStep 16034537 = 12025903) B12025903
theorem B14257295 : Blo 1668034 14257295 := bstep (se 1 (by rfl) ⟨10692971, by rfl⟩ : syracuseStep 14257295 = 21385943) B21385943
theorem B5631983 : Blo 1668034 5631983 := bstep (se 1 (by rfl) ⟨4223987, by rfl⟩ : syracuseStep 5631983 = 8447975) B8447975
theorem B3756023 : Blo 1668034 3756023 := bstep (se 1 (by rfl) ⟨2817017, by rfl⟩ : syracuseStep 3756023 = 5634035) B5634035
theorem B2502767 : Blo 1668034 2502767 := bstep (se 1 (by rfl) ⟨1877075, by rfl⟩ : syracuseStep 2502767 = 3754151) B3754151
theorem B1782815 : Blo 1668034 1782815 := bstep (se 1 (by rfl) ⟨1337111, by rfl⟩ : syracuseStep 1782815 = 2674223) B2674223
theorem B1668767 : Blo 1668034 1668767 := bstep (se 1 (by rfl) ⟨1251575, by rfl⟩ : syracuseStep 1668767 = 2503151) B2503151
theorem B1668799 : Blo 1668034 1668799 := bstep (se 1 (by rfl) ⟨1251599, by rfl⟩ : syracuseStep 1668799 = 2503199) B2503199
theorem B2504423 : Blo 1668034 2504423 := bstep (se 1 (by rfl) ⟨1878317, by rfl⟩ : syracuseStep 2504423 = 3756635) B3756635
theorem B28514105 : Blo 1668034 28514105 := bstep (se 2 (by rfl) ⟨10692789, by rfl⟩ : syracuseStep 28514105 = 21385579) B21385579
theorem B14251859 : Blo 1668034 14251859 := bstep (se 1 (by rfl) ⟨10688894, by rfl⟩ : syracuseStep 14251859 = 21377789) B21377789
theorem B2504795 : Blo 1668034 2504795 := bstep (se 1 (by rfl) ⟨1878596, by rfl⟩ : syracuseStep 2504795 = 3757193) B3757193
theorem B6764879 : Blo 1668034 6764879 := bstep (se 1 (by rfl) ⟨5073659, by rfl⟩ : syracuseStep 6764879 = 10147319) B10147319
theorem B1669631 : Blo 1668034 1669631 := bstep (se 1 (by rfl) ⟨1252223, by rfl⟩ : syracuseStep 1669631 = 2504447) B2504447
theorem B2817983 : Blo 1668034 2817983 := bstep (se 1 (by rfl) ⟨2113487, by rfl⟩ : syracuseStep 2817983 = 4226975) B4226975
theorem B3753755 : Blo 1668034 3753755 := bstep (se 1 (by rfl) ⟨2815316, by rfl⟩ : syracuseStep 3753755 = 5630633) B5630633
theorem B9504863 : Blo 1668034 9504863 := bstep (se 1 (by rfl) ⟨7128647, by rfl⟩ : syracuseStep 9504863 = 14257295) B14257295
theorem B1878655 : Blo 1668034 1878655 := bstep (se 1 (by rfl) ⟨1408991, by rfl⟩ : syracuseStep 1878655 = 2817983) B2817983
theorem B3754655 : Blo 1668034 3754655 := bstep (se 1 (by rfl) ⟨2815991, by rfl⟩ : syracuseStep 3754655 = 5631983) B5631983
theorem B19016693 : Blo 1668034 19016693 := bstep (se 5 (by rfl) ⟨891407, by rfl⟩ : syracuseStep 19016693 = 1782815) B1782815
theorem B5631335 : Blo 1668034 5631335 := bstep (se 1 (by rfl) ⟨4223501, by rfl⟩ : syracuseStep 5631335 = 8447003) B8447003
theorem B19009403 : Blo 1668034 19009403 := bstep (se 1 (by rfl) ⟨14257052, by rfl⟩ : syracuseStep 19009403 = 28514105) B28514105
theorem B2502599 : Blo 1668034 2502599 := bstep (se 1 (by rfl) ⟨1876949, by rfl⟩ : syracuseStep 2502599 = 3753899) B3753899
theorem B2502635 : Blo 1668034 2502635 := bstep (se 1 (by rfl) ⟨1876976, by rfl⟩ : syracuseStep 2502635 = 3753953) B3753953
theorem B4509919 : Blo 1668034 4509919 := bstep (se 1 (by rfl) ⟨3382439, by rfl⟩ : syracuseStep 4509919 = 6764879) B6764879
theorem B2504015 : Blo 1668034 2504015 := bstep (se 1 (by rfl) ⟨1878011, by rfl⟩ : syracuseStep 2504015 = 3756023) B3756023
theorem B1668511 : Blo 1668034 1668511 := bstep (se 1 (by rfl) ⟨1251383, by rfl⟩ : syracuseStep 1668511 = 2502767) B2502767
theorem B97589231 : Blo 1668034 97589231 := bstep (se 1 (by rfl) ⟨73191923, by rfl⟩ : syracuseStep 97589231 = 146383847) B146383847
theorem B1669615 : Blo 1668034 1669615 := bstep (se 1 (by rfl) ⟨1252211, by rfl⟩ : syracuseStep 1669615 = 2504423) B2504423
theorem B9501239 : Blo 1668034 9501239 := bstep (se 1 (by rfl) ⟨7125929, by rfl⟩ : syracuseStep 9501239 = 14251859) B14251859
theorem B1669863 : Blo 1668034 1669863 := bstep (se 1 (by rfl) ⟨1252397, by rfl⟩ : syracuseStep 1669863 = 2504795) B2504795
theorem B28531601 : Blo 1668034 28531601 := bstep (se 2 (by rfl) ⟨10699350, by rfl⟩ : syracuseStep 28531601 = 21398701) B21398701
theorem B10689691 : Blo 1668034 10689691 := bstep (se 1 (by rfl) ⟨8017268, by rfl⟩ : syracuseStep 10689691 = 16034537) B16034537
theorem B6013225 : Blo 1668034 6013225 := bstep (se 2 (by rfl) ⟨2254959, by rfl⟩ : syracuseStep 6013225 = 4509919) B4509919
theorem B6334159 : Blo 1668034 6334159 := bstep (se 1 (by rfl) ⟨4750619, by rfl⟩ : syracuseStep 6334159 = 9501239) B9501239
theorem B3754223 : Blo 1668034 3754223 := bstep (se 1 (by rfl) ⟨2815667, by rfl⟩ : syracuseStep 3754223 = 5631335) B5631335
theorem B2502503 : Blo 1668034 2502503 := bstep (se 1 (by rfl) ⟨1876877, by rfl⟩ : syracuseStep 2502503 = 3753755) B3753755
theorem B6336575 : Blo 1668034 6336575 := bstep (se 1 (by rfl) ⟨4752431, by rfl⟩ : syracuseStep 6336575 = 9504863) B9504863
theorem B2503103 : Blo 1668034 2503103 := bstep (se 1 (by rfl) ⟨1877327, by rfl⟩ : syracuseStep 2503103 = 3754655) B3754655
theorem B12677795 : Blo 1668034 12677795 := bstep (se 1 (by rfl) ⟨9508346, by rfl⟩ : syracuseStep 12677795 = 19016693) B19016693
theorem B1668399 : Blo 1668034 1668399 := bstep (se 1 (by rfl) ⟨1251299, by rfl⟩ : syracuseStep 1668399 = 2502599) B2502599
theorem B1668423 : Blo 1668034 1668423 := bstep (se 1 (by rfl) ⟨1251317, by rfl⟩ : syracuseStep 1668423 = 2502635) B2502635
theorem B2504873 : Blo 1668034 2504873 := bstep (se 2 (by rfl) ⟨939327, by rfl⟩ : syracuseStep 2504873 = 1878655) B1878655
theorem B1669343 : Blo 1668034 1669343 := bstep (se 1 (by rfl) ⟨1252007, by rfl⟩ : syracuseStep 1669343 = 2504015) B2504015
theorem B65059487 : Blo 1668034 65059487 := bstep (se 1 (by rfl) ⟨48794615, by rfl⟩ : syracuseStep 65059487 = 97589231) B97589231
theorem B14252921 : Blo 1668034 14252921 := bstep (se 2 (by rfl) ⟨5344845, by rfl⟩ : syracuseStep 14252921 = 10689691) B10689691
theorem B19021067 : Blo 1668034 19021067 := bstep (se 1 (by rfl) ⟨14265800, by rfl⟩ : syracuseStep 19021067 = 28531601) B28531601
theorem B12672935 : Blo 1668034 12672935 := bstep (se 1 (by rfl) ⟨9504701, by rfl⟩ : syracuseStep 12672935 = 19009403) B19009403
theorem B8448623 : Blo 1668034 8448623 := bstep (se 1 (by rfl) ⟨6336467, by rfl⟩ : syracuseStep 8448623 = 12672935) B12672935
theorem B2502815 : Blo 1668034 2502815 := bstep (se 1 (by rfl) ⟨1877111, by rfl⟩ : syracuseStep 2502815 = 3754223) B3754223
theorem B43372991 : Blo 1668034 43372991 := bstep (se 1 (by rfl) ⟨32529743, by rfl⟩ : syracuseStep 43372991 = 65059487) B65059487
theorem B1668335 : Blo 1668034 1668335 := bstep (se 1 (by rfl) ⟨1251251, by rfl⟩ : syracuseStep 1668335 = 2502503) B2502503
theorem B4224383 : Blo 1668034 4224383 := bstep (se 1 (by rfl) ⟨3168287, by rfl⟩ : syracuseStep 4224383 = 6336575) B6336575
theorem B1668735 : Blo 1668034 1668735 := bstep (se 1 (by rfl) ⟨1251551, by rfl⟩ : syracuseStep 1668735 = 2503103) B2503103
theorem B8017633 : Blo 1668034 8017633 := bstep (se 2 (by rfl) ⟨3006612, by rfl⟩ : syracuseStep 8017633 = 6013225) B6013225
theorem B8451863 : Blo 1668034 8451863 := bstep (se 1 (by rfl) ⟨6338897, by rfl⟩ : syracuseStep 8451863 = 12677795) B12677795
theorem B1669915 : Blo 1668034 1669915 := bstep (se 1 (by rfl) ⟨1252436, by rfl⟩ : syracuseStep 1669915 = 2504873) B2504873
theorem B9501947 : Blo 1668034 9501947 := bstep (se 1 (by rfl) ⟨7126460, by rfl⟩ : syracuseStep 9501947 = 14252921) B14252921
theorem B12680711 : Blo 1668034 12680711 := bstep (se 1 (by rfl) ⟨9510533, by rfl⟩ : syracuseStep 12680711 = 19021067) B19021067
theorem B8445545 : Blo 1668034 8445545 := bstep (se 2 (by rfl) ⟨3167079, by rfl⟩ : syracuseStep 8445545 = 6334159) B6334159
theorem B6334631 : Blo 1668034 6334631 := bstep (se 1 (by rfl) ⟨4750973, by rfl⟩ : syracuseStep 6334631 = 9501947) B9501947
theorem B5630363 : Blo 1668034 5630363 := bstep (se 1 (by rfl) ⟨4222772, by rfl⟩ : syracuseStep 5630363 = 8445545) B8445545
theorem B5632415 : Blo 1668034 5632415 := bstep (se 1 (by rfl) ⟨4224311, by rfl⟩ : syracuseStep 5632415 = 8448623) B8448623
theorem B1668543 : Blo 1668034 1668543 := bstep (se 1 (by rfl) ⟨1251407, by rfl⟩ : syracuseStep 1668543 = 2502815) B2502815
theorem B28915327 : Blo 1668034 28915327 := bstep (se 1 (by rfl) ⟨21686495, by rfl⟩ : syracuseStep 28915327 = 43372991) B43372991
theorem B2816255 : Blo 1668034 2816255 := bstep (se 1 (by rfl) ⟨2112191, by rfl⟩ : syracuseStep 2816255 = 4224383) B4224383
theorem B5634575 : Blo 1668034 5634575 := bstep (se 1 (by rfl) ⟨4225931, by rfl⟩ : syracuseStep 5634575 = 8451863) B8451863
theorem B10690177 : Blo 1668034 10690177 := bstep (se 2 (by rfl) ⟨4008816, by rfl⟩ : syracuseStep 10690177 = 8017633) B8017633
theorem B8453807 : Blo 1668034 8453807 := bstep (se 1 (by rfl) ⟨6340355, by rfl⟩ : syracuseStep 8453807 = 12680711) B12680711
theorem B1877503 : Blo 1668034 1877503 := bstep (se 1 (by rfl) ⟨1408127, by rfl⟩ : syracuseStep 1877503 = 2816255) B2816255
theorem B3753575 : Blo 1668034 3753575 := bstep (se 1 (by rfl) ⟨2815181, by rfl⟩ : syracuseStep 3753575 = 5630363) B5630363
theorem B38553769 : Blo 1668034 38553769 := bstep (se 2 (by rfl) ⟨14457663, by rfl⟩ : syracuseStep 38553769 = 28915327) B28915327
theorem B3754943 : Blo 1668034 3754943 := bstep (se 1 (by rfl) ⟨2816207, by rfl⟩ : syracuseStep 3754943 = 5632415) B5632415
theorem B4223087 : Blo 1668034 4223087 := bstep (se 1 (by rfl) ⟨3167315, by rfl⟩ : syracuseStep 4223087 = 6334631) B6334631
theorem B3756383 : Blo 1668034 3756383 := bstep (se 1 (by rfl) ⟨2817287, by rfl⟩ : syracuseStep 3756383 = 5634575) B5634575
theorem B14253569 : Blo 1668034 14253569 := bstep (se 2 (by rfl) ⟨5345088, by rfl⟩ : syracuseStep 14253569 = 10690177) B10690177
theorem B5635871 : Blo 1668034 5635871 := bstep (se 1 (by rfl) ⟨4226903, by rfl⟩ : syracuseStep 5635871 = 8453807) B8453807
theorem B51405025 : Blo 1668034 51405025 := bstep (se 2 (by rfl) ⟨19276884, by rfl⟩ : syracuseStep 51405025 = 38553769) B38553769
theorem B2502383 : Blo 1668034 2502383 := bstep (se 1 (by rfl) ⟨1876787, by rfl⟩ : syracuseStep 2502383 = 3753575) B3753575
theorem B2503295 : Blo 1668034 2503295 := bstep (se 1 (by rfl) ⟨1877471, by rfl⟩ : syracuseStep 2503295 = 3754943) B3754943
theorem B2503337 : Blo 1668034 2503337 := bstep (se 2 (by rfl) ⟨938751, by rfl⟩ : syracuseStep 2503337 = 1877503) B1877503
theorem B3757247 : Blo 1668034 3757247 := bstep (se 1 (by rfl) ⟨2817935, by rfl⟩ : syracuseStep 3757247 = 5635871) B5635871
theorem B2815391 : Blo 1668034 2815391 := bstep (se 1 (by rfl) ⟨2111543, by rfl⟩ : syracuseStep 2815391 = 4223087) B4223087
theorem B2504255 : Blo 1668034 2504255 := bstep (se 1 (by rfl) ⟨1878191, by rfl⟩ : syracuseStep 2504255 = 3756383) B3756383
theorem B9502379 : Blo 1668034 9502379 := bstep (se 1 (by rfl) ⟨7126784, by rfl⟩ : syracuseStep 9502379 = 14253569) B14253569
theorem B1876927 : Blo 1668034 1876927 := bstep (se 1 (by rfl) ⟨1407695, by rfl⟩ : syracuseStep 1876927 = 2815391) B2815391
theorem B6334919 : Blo 1668034 6334919 := bstep (se 1 (by rfl) ⟨4751189, by rfl⟩ : syracuseStep 6334919 = 9502379) B9502379
theorem B1668255 : Blo 1668034 1668255 := bstep (se 1 (by rfl) ⟨1251191, by rfl⟩ : syracuseStep 1668255 = 2502383) B2502383
theorem B68540033 : Blo 1668034 68540033 := bstep (se 2 (by rfl) ⟨25702512, by rfl⟩ : syracuseStep 68540033 = 51405025) B51405025
theorem B1668863 : Blo 1668034 1668863 := bstep (se 1 (by rfl) ⟨1251647, by rfl⟩ : syracuseStep 1668863 = 2503295) B2503295
theorem B1668891 : Blo 1668034 1668891 := bstep (se 1 (by rfl) ⟨1251668, by rfl⟩ : syracuseStep 1668891 = 2503337) B2503337
theorem B2504831 : Blo 1668034 2504831 := bstep (se 1 (by rfl) ⟨1878623, by rfl⟩ : syracuseStep 2504831 = 3757247) B3757247
theorem B1669503 : Blo 1668034 1669503 := bstep (se 1 (by rfl) ⟨1252127, by rfl⟩ : syracuseStep 1669503 = 2504255) B2504255
theorem B182773421 : Blo 1668034 182773421 := bstep (se 3 (by rfl) ⟨34270016, by rfl⟩ : syracuseStep 182773421 = 68540033) B68540033
theorem B2502569 : Blo 1668034 2502569 := bstep (se 2 (by rfl) ⟨938463, by rfl⟩ : syracuseStep 2502569 = 1876927) B1876927
theorem B4223279 : Blo 1668034 4223279 := bstep (se 1 (by rfl) ⟨3167459, by rfl⟩ : syracuseStep 4223279 = 6334919) B6334919
theorem B1669887 : Blo 1668034 1669887 := bstep (se 1 (by rfl) ⟨1252415, by rfl⟩ : syracuseStep 1669887 = 2504831) B2504831
theorem B121848947 : Blo 1668034 121848947 := bstep (se 1 (by rfl) ⟨91386710, by rfl⟩ : syracuseStep 121848947 = 182773421) B182773421
theorem B1668379 : Blo 1668034 1668379 := bstep (se 1 (by rfl) ⟨1251284, by rfl⟩ : syracuseStep 1668379 = 2502569) B2502569
theorem B2815519 : Blo 1668034 2815519 := bstep (se 1 (by rfl) ⟨2111639, by rfl⟩ : syracuseStep 2815519 = 4223279) B4223279
theorem B81232631 : Blo 1668034 81232631 := bstep (se 1 (by rfl) ⟨60924473, by rfl⟩ : syracuseStep 81232631 = 121848947) B121848947
theorem B3754025 : Blo 1668034 3754025 := bstep (se 2 (by rfl) ⟨1407759, by rfl⟩ : syracuseStep 3754025 = 2815519) B2815519
theorem B2502683 : Blo 1668034 2502683 := bstep (se 1 (by rfl) ⟨1877012, by rfl⟩ : syracuseStep 2502683 = 3754025) B3754025
theorem B54155087 : Blo 1668034 54155087 := bstep (se 1 (by rfl) ⟨40616315, by rfl⟩ : syracuseStep 54155087 = 81232631) B81232631
theorem B36103391 : Blo 1668034 36103391 := bstep (se 1 (by rfl) ⟨27077543, by rfl⟩ : syracuseStep 36103391 = 54155087) B54155087
theorem B1668455 : Blo 1668034 1668455 := bstep (se 1 (by rfl) ⟨1251341, by rfl⟩ : syracuseStep 1668455 = 2502683) B2502683
theorem B24068927 : Blo 1668034 24068927 := bstep (se 1 (by rfl) ⟨18051695, by rfl⟩ : syracuseStep 24068927 = 36103391) B36103391
theorem B16045951 : Blo 1668034 16045951 := bstep (se 1 (by rfl) ⟨12034463, by rfl⟩ : syracuseStep 16045951 = 24068927) B24068927
theorem B21394601 : Blo 1668034 21394601 := bstep (se 2 (by rfl) ⟨8022975, by rfl⟩ : syracuseStep 21394601 = 16045951) B16045951
theorem B14263067 : Blo 1668034 14263067 := bstep (se 1 (by rfl) ⟨10697300, by rfl⟩ : syracuseStep 14263067 = 21394601) B21394601
theorem B9508711 : Blo 1668034 9508711 := bstep (se 1 (by rfl) ⟨7131533, by rfl⟩ : syracuseStep 9508711 = 14263067) B14263067
theorem B12678281 : Blo 1668034 12678281 := bstep (se 2 (by rfl) ⟨4754355, by rfl⟩ : syracuseStep 12678281 = 9508711) B9508711
theorem B8452187 : Blo 1668034 8452187 := bstep (se 1 (by rfl) ⟨6339140, by rfl⟩ : syracuseStep 8452187 = 12678281) B12678281
theorem B5634791 : Blo 1668034 5634791 := bstep (se 1 (by rfl) ⟨4226093, by rfl⟩ : syracuseStep 5634791 = 8452187) B8452187
theorem B3756527 : Blo 1668034 3756527 := bstep (se 1 (by rfl) ⟨2817395, by rfl⟩ : syracuseStep 3756527 = 5634791) B5634791
theorem B2504351 : Blo 1668034 2504351 := bstep (se 1 (by rfl) ⟨1878263, by rfl⟩ : syracuseStep 2504351 = 3756527) B3756527
theorem B1669567 : Blo 1668034 1669567 := bstep (se 1 (by rfl) ⟨1252175, by rfl⟩ : syracuseStep 1669567 = 2504351) B2504351

theorem C0 (j : ℕ) (h1 : 417008 ≤ j) (h2 : j ≤ 417507) : Blo 1668034 (4 * j + 3) := by
  interval_cases j
  · exact B1668035
  · exact B1668039
  · exact B1668043
  · exact B1668047
  · exact B1668051
  · exact B1668055
  · exact B1668059
  · exact B1668063
  · exact B1668067
  · exact B1668071
  · exact B1668075
  · exact B1668079
  · exact B1668083
  · exact B1668087
  · exact B1668091
  · exact B1668095
  · exact B1668099
  · exact B1668103
  · exact B1668107
  · exact B1668111
  · exact B1668115
  · exact B1668119
  · exact B1668123
  · exact B1668127
  · exact B1668131
  · exact B1668135
  · exact B1668139
  · exact B1668143
  · exact B1668147
  · exact B1668151
  · exact B1668155
  · exact B1668159
  · exact B1668163
  · exact B1668167
  · exact B1668171
  · exact B1668175
  · exact B1668179
  · exact B1668183
  · exact B1668187
  · exact B1668191
  · exact B1668195
  · exact B1668199
  · exact B1668203
  · exact B1668207
  · exact B1668211
  · exact B1668215
  · exact B1668219
  · exact B1668223
  · exact B1668227
  · exact B1668231
  · exact B1668235
  · exact B1668239
  · exact B1668243
  · exact B1668247
  · exact B1668251
  · exact B1668255
  · exact B1668259
  · exact B1668263
  · exact B1668267
  · exact B1668271
  · exact B1668275
  · exact B1668279
  · exact B1668283
  · exact B1668287
  · exact B1668291
  · exact B1668295
  · exact B1668299
  · exact B1668303
  · exact B1668307
  · exact B1668311
  · exact B1668315
  · exact B1668319
  · exact B1668323
  · exact B1668327
  · exact B1668331
  · exact B1668335
  · exact B1668339
  · exact B1668343
  · exact B1668347
  · exact B1668351
  · exact B1668355
  · exact B1668359
  · exact B1668363
  · exact B1668367
  · exact B1668371
  · exact B1668375
  · exact B1668379
  · exact B1668383
  · exact B1668387
  · exact B1668391
  · exact B1668395
  · exact B1668399
  · exact B1668403
  · exact B1668407
  · exact B1668411
  · exact B1668415
  · exact B1668419
  · exact B1668423
  · exact B1668427
  · exact B1668431
  · exact B1668435
  · exact B1668439
  · exact B1668443
  · exact B1668447
  · exact B1668451
  · exact B1668455
  · exact B1668459
  · exact B1668463
  · exact B1668467
  · exact B1668471
  · exact B1668475
  · exact B1668479
  · exact B1668483
  · exact B1668487
  · exact B1668491
  · exact B1668495
  · exact B1668499
  · exact B1668503
  · exact B1668507
  · exact B1668511
  · exact B1668515
  · exact B1668519
  · exact B1668523
  · exact B1668527
  · exact B1668531
  · exact B1668535
  · exact B1668539
  · exact B1668543
  · exact B1668547
  · exact B1668551
  · exact B1668555
  · exact B1668559
  · exact B1668563
  · exact B1668567
  · exact B1668571
  · exact B1668575
  · exact B1668579
  · exact B1668583
  · exact B1668587
  · exact B1668591
  · exact B1668595
  · exact B1668599
  · exact B1668603
  · exact B1668607
  · exact B1668611
  · exact B1668615
  · exact B1668619
  · exact B1668623
  · exact B1668627
  · exact B1668631
  · exact B1668635
  · exact B1668639
  · exact B1668643
  · exact B1668647
  · exact B1668651
  · exact B1668655
  · exact B1668659
  · exact B1668663
  · exact B1668667
  · exact B1668671
  · exact B1668675
  · exact B1668679
  · exact B1668683
  · exact B1668687
  · exact B1668691
  · exact B1668695
  · exact B1668699
  · exact B1668703
  · exact B1668707
  · exact B1668711
  · exact B1668715
  · exact B1668719
  · exact B1668723
  · exact B1668727
  · exact B1668731
  · exact B1668735
  · exact B1668739
  · exact B1668743
  · exact B1668747
  · exact B1668751
  · exact B1668755
  · exact B1668759
  · exact B1668763
  · exact B1668767
  · exact B1668771
  · exact B1668775
  · exact B1668779
  · exact B1668783
  · exact B1668787
  · exact B1668791
  · exact B1668795
  · exact B1668799
  · exact B1668803
  · exact B1668807
  · exact B1668811
  · exact B1668815
  · exact B1668819
  · exact B1668823
  · exact B1668827
  · exact B1668831
  · exact B1668835
  · exact B1668839
  · exact B1668843
  · exact B1668847
  · exact B1668851
  · exact B1668855
  · exact B1668859
  · exact B1668863
  · exact B1668867
  · exact B1668871
  · exact B1668875
  · exact B1668879
  · exact B1668883
  · exact B1668887
  · exact B1668891
  · exact B1668895
  · exact B1668899
  · exact B1668903
  · exact B1668907
  · exact B1668911
  · exact B1668915
  · exact B1668919
  · exact B1668923
  · exact B1668927
  · exact B1668931
  · exact B1668935
  · exact B1668939
  · exact B1668943
  · exact B1668947
  · exact B1668951
  · exact B1668955
  · exact B1668959
  · exact B1668963
  · exact B1668967
  · exact B1668971
  · exact B1668975
  · exact B1668979
  · exact B1668983
  · exact B1668987
  · exact B1668991
  · exact B1668995
  · exact B1668999
  · exact B1669003
  · exact B1669007
  · exact B1669011
  · exact B1669015
  · exact B1669019
  · exact B1669023
  · exact B1669027
  · exact B1669031
  · exact B1669035
  · exact B1669039
  · exact B1669043
  · exact B1669047
  · exact B1669051
  · exact B1669055
  · exact B1669059
  · exact B1669063
  · exact B1669067
  · exact B1669071
  · exact B1669075
  · exact B1669079
  · exact B1669083
  · exact B1669087
  · exact B1669091
  · exact B1669095
  · exact B1669099
  · exact B1669103
  · exact B1669107
  · exact B1669111
  · exact B1669115
  · exact B1669119
  · exact B1669123
  · exact B1669127
  · exact B1669131
  · exact B1669135
  · exact B1669139
  · exact B1669143
  · exact B1669147
  · exact B1669151
  · exact B1669155
  · exact B1669159
  · exact B1669163
  · exact B1669167
  · exact B1669171
  · exact B1669175
  · exact B1669179
  · exact B1669183
  · exact B1669187
  · exact B1669191
  · exact B1669195
  · exact B1669199
  · exact B1669203
  · exact B1669207
  · exact B1669211
  · exact B1669215
  · exact B1669219
  · exact B1669223
  · exact B1669227
  · exact B1669231
  · exact B1669235
  · exact B1669239
  · exact B1669243
  · exact B1669247
  · exact B1669251
  · exact B1669255
  · exact B1669259
  · exact B1669263
  · exact B1669267
  · exact B1669271
  · exact B1669275
  · exact B1669279
  · exact B1669283
  · exact B1669287
  · exact B1669291
  · exact B1669295
  · exact B1669299
  · exact B1669303
  · exact B1669307
  · exact B1669311
  · exact B1669315
  · exact B1669319
  · exact B1669323
  · exact B1669327
  · exact B1669331
  · exact B1669335
  · exact B1669339
  · exact B1669343
  · exact B1669347
  · exact B1669351
  · exact B1669355
  · exact B1669359
  · exact B1669363
  · exact B1669367
  · exact B1669371
  · exact B1669375
  · exact B1669379
  · exact B1669383
  · exact B1669387
  · exact B1669391
  · exact B1669395
  · exact B1669399
  · exact B1669403
  · exact B1669407
  · exact B1669411
  · exact B1669415
  · exact B1669419
  · exact B1669423
  · exact B1669427
  · exact B1669431
  · exact B1669435
  · exact B1669439
  · exact B1669443
  · exact B1669447
  · exact B1669451
  · exact B1669455
  · exact B1669459
  · exact B1669463
  · exact B1669467
  · exact B1669471
  · exact B1669475
  · exact B1669479
  · exact B1669483
  · exact B1669487
  · exact B1669491
  · exact B1669495
  · exact B1669499
  · exact B1669503
  · exact B1669507
  · exact B1669511
  · exact B1669515
  · exact B1669519
  · exact B1669523
  · exact B1669527
  · exact B1669531
  · exact B1669535
  · exact B1669539
  · exact B1669543
  · exact B1669547
  · exact B1669551
  · exact B1669555
  · exact B1669559
  · exact B1669563
  · exact B1669567
  · exact B1669571
  · exact B1669575
  · exact B1669579
  · exact B1669583
  · exact B1669587
  · exact B1669591
  · exact B1669595
  · exact B1669599
  · exact B1669603
  · exact B1669607
  · exact B1669611
  · exact B1669615
  · exact B1669619
  · exact B1669623
  · exact B1669627
  · exact B1669631
  · exact B1669635
  · exact B1669639
  · exact B1669643
  · exact B1669647
  · exact B1669651
  · exact B1669655
  · exact B1669659
  · exact B1669663
  · exact B1669667
  · exact B1669671
  · exact B1669675
  · exact B1669679
  · exact B1669683
  · exact B1669687
  · exact B1669691
  · exact B1669695
  · exact B1669699
  · exact B1669703
  · exact B1669707
  · exact B1669711
  · exact B1669715
  · exact B1669719
  · exact B1669723
  · exact B1669727
  · exact B1669731
  · exact B1669735
  · exact B1669739
  · exact B1669743
  · exact B1669747
  · exact B1669751
  · exact B1669755
  · exact B1669759
  · exact B1669763
  · exact B1669767
  · exact B1669771
  · exact B1669775
  · exact B1669779
  · exact B1669783
  · exact B1669787
  · exact B1669791
  · exact B1669795
  · exact B1669799
  · exact B1669803
  · exact B1669807
  · exact B1669811
  · exact B1669815
  · exact B1669819
  · exact B1669823
  · exact B1669827
  · exact B1669831
  · exact B1669835
  · exact B1669839
  · exact B1669843
  · exact B1669847
  · exact B1669851
  · exact B1669855
  · exact B1669859
  · exact B1669863
  · exact B1669867
  · exact B1669871
  · exact B1669875
  · exact B1669879
  · exact B1669883
  · exact B1669887
  · exact B1669891
  · exact B1669895
  · exact B1669899
  · exact B1669903
  · exact B1669907
  · exact B1669911
  · exact B1669915
  · exact B1669919
  · exact B1669923
  · exact B1669927
  · exact B1669931
  · exact B1669935
  · exact B1669939
  · exact B1669943
  · exact B1669947
  · exact B1669951
  · exact B1669955
  · exact B1669959
  · exact B1669963
  · exact B1669967
  · exact B1669971
  · exact B1669975
  · exact B1669979
  · exact B1669983
  · exact B1669987
  · exact B1669991
  · exact B1669995
  · exact B1669999
  · exact B1670003
  · exact B1670007
  · exact B1670011
  · exact B1670015
  · exact B1670019
  · exact B1670023
  · exact B1670027
  · exact B1670031

theorem solution (m : ℕ) (hlo : 1668034 ≤ m) (hhi : m ≤ 1670034) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 417008 ≤ j := by omega
    have hj2 : j ≤ 417507 := by omega
    have hb : Blo 1668034 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
