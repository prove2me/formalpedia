-- Prove2me | solution 1 for syracuse_descends_range_1459549_1461049
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:44:02.917407+00:00
-- url     : https://prove2.me/submissions/e786da58-d378-4c2a-afd9-98cfc0d33575

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


theorem B2498597 : Blo 1459549 2498597 := bbase (se 4 (by rfl) ⟨234243, by rfl⟩ : syracuseStep 2498597 = 468487) (by norm_num)
theorem B3285053 : Blo 1459549 3285053 := bbase (se 3 (by rfl) ⟨615947, by rfl⟩ : syracuseStep 3285053 = 1231895) (by norm_num)
theorem B3694693 : Blo 1459549 3694693 := bbase (se 4 (by rfl) ⟨346377, by rfl⟩ : syracuseStep 3694693 = 692755) (by norm_num)
theorem B3285125 : Blo 1459549 3285125 := bbase (se 4 (by rfl) ⟨307980, by rfl⟩ : syracuseStep 3285125 = 615961) (by norm_num)
theorem B3285197 : Blo 1459549 3285197 := bbase (se 3 (by rfl) ⟨615974, by rfl⟩ : syracuseStep 3285197 = 1231949) (by norm_num)
theorem B3694805 : Blo 1459549 3694805 := bbase (se 7 (by rfl) ⟨43298, by rfl⟩ : syracuseStep 3694805 = 86597) (by norm_num)
theorem B3285269 : Blo 1459549 3285269 := bbase (se 6 (by rfl) ⟨76998, by rfl⟩ : syracuseStep 3285269 = 153997) (by norm_num)
theorem B3285341 : Blo 1459549 3285341 := bbase (se 3 (by rfl) ⟨616001, by rfl⟩ : syracuseStep 3285341 = 1232003) (by norm_num)
theorem B3694997 : Blo 1459549 3694997 := bbase (se 6 (by rfl) ⟨86601, by rfl⟩ : syracuseStep 3694997 = 173203) (by norm_num)
theorem B3285413 : Blo 1459549 3285413 := bbase (se 4 (by rfl) ⟨308007, by rfl⟩ : syracuseStep 3285413 = 616015) (by norm_num)
theorem B3285485 : Blo 1459549 3285485 := bbase (se 3 (by rfl) ⟨616028, by rfl⟩ : syracuseStep 3285485 = 1232057) (by norm_num)
theorem B4940293 : Blo 1459549 4940293 := bbase (se 4 (by rfl) ⟨463152, by rfl⟩ : syracuseStep 4940293 = 926305) (by norm_num)
theorem B3285557 : Blo 1459549 3285557 := bbase (se 5 (by rfl) ⟨154010, by rfl⟩ : syracuseStep 3285557 = 308021) (by norm_num)
theorem B2220605 : Blo 1459549 2220605 := bbase (se 3 (by rfl) ⟨416363, by rfl⟩ : syracuseStep 2220605 = 832727) (by norm_num)
theorem B3285629 : Blo 1459549 3285629 := bbase (se 3 (by rfl) ⟨616055, by rfl⟩ : syracuseStep 3285629 = 1232111) (by norm_num)
theorem B12477077 : Blo 1459549 12477077 := bbase (se 6 (by rfl) ⟨292431, by rfl⟩ : syracuseStep 12477077 = 584863) (by norm_num)
theorem B4440757 : Blo 1459549 4440757 := bbase (se 5 (by rfl) ⟨208160, by rfl⟩ : syracuseStep 4440757 = 416321) (by norm_num)
theorem B3285701 : Blo 1459549 3285701 := bbase (se 4 (by rfl) ⟨308034, by rfl⟩ : syracuseStep 3285701 = 616069) (by norm_num)
theorem B1778377 : Blo 1459549 1778377 := bbase (se 2 (by rfl) ⟨666891, by rfl⟩ : syracuseStep 1778377 = 1333783) (by norm_num)
theorem B3695341 : Blo 1459549 3695341 := bbase (se 3 (by rfl) ⟨692876, by rfl⟩ : syracuseStep 3695341 = 1385753) (by norm_num)
theorem B3285773 : Blo 1459549 3285773 := bbase (se 3 (by rfl) ⟨616082, by rfl⟩ : syracuseStep 3285773 = 1232165) (by norm_num)
theorem B3556133 : Blo 1459549 3556133 := bbase (se 4 (by rfl) ⟨333387, by rfl⟩ : syracuseStep 3556133 = 666775) (by norm_num)
theorem B2220853 : Blo 1459549 2220853 := bbase (se 5 (by rfl) ⟨104102, by rfl⟩ : syracuseStep 2220853 = 208205) (by norm_num)
theorem B5923637 : Blo 1459549 5923637 := bbase (se 5 (by rfl) ⟨277670, by rfl⟩ : syracuseStep 5923637 = 555341) (by norm_num)
theorem B1753921 : Blo 1459549 1753921 := bbase (se 2 (by rfl) ⟨657720, by rfl⟩ : syracuseStep 1753921 = 1315441) (by norm_num)
theorem B3285845 : Blo 1459549 3285845 := bbase (se 9 (by rfl) ⟨9626, by rfl⟩ : syracuseStep 3285845 = 19253) (by norm_num)
theorem B3695453 : Blo 1459549 3695453 := bbase (se 3 (by rfl) ⟨692897, by rfl⟩ : syracuseStep 3695453 = 1385795) (by norm_num)
theorem B3285917 : Blo 1459549 3285917 := bbase (se 3 (by rfl) ⟨616109, by rfl⟩ : syracuseStep 3285917 = 1232219) (by norm_num)
theorem B11092949 : Blo 1459549 11092949 := bbase (se 7 (by rfl) ⟨129995, by rfl⟩ : syracuseStep 11092949 = 259991) (by norm_num)
theorem B3285989 : Blo 1459549 3285989 := bbase (se 4 (by rfl) ⟨308061, by rfl⟩ : syracuseStep 3285989 = 616123) (by norm_num)
theorem B4678661 : Blo 1459549 4678661 := bbase (se 4 (by rfl) ⟨438624, by rfl⟩ : syracuseStep 4678661 = 877249) (by norm_num)
theorem B3695645 : Blo 1459549 3695645 := bbase (se 3 (by rfl) ⟨692933, by rfl⟩ : syracuseStep 3695645 = 1385867) (by norm_num)
theorem B3286061 : Blo 1459549 3286061 := bbase (se 3 (by rfl) ⟨616136, by rfl⟩ : syracuseStep 3286061 = 1232273) (by norm_num)
theorem B7390277 : Blo 1459549 7390277 := bbase (se 4 (by rfl) ⟨692838, by rfl⟩ : syracuseStep 7390277 = 1385677) (by norm_num)
theorem B3286133 : Blo 1459549 3286133 := bbase (se 5 (by rfl) ⟨154037, by rfl⟩ : syracuseStep 3286133 = 308075) (by norm_num)
theorem B3286205 : Blo 1459549 3286205 := bbase (se 3 (by rfl) ⟨616163, by rfl⟩ : syracuseStep 3286205 = 1232327) (by norm_num)
theorem B3286277 : Blo 1459549 3286277 := bbase (se 4 (by rfl) ⟨308088, by rfl⟩ : syracuseStep 3286277 = 616177) (by norm_num)
theorem B3286349 : Blo 1459549 3286349 := bbase (se 3 (by rfl) ⟨616190, by rfl⟩ : syracuseStep 3286349 = 1232381) (by norm_num)
theorem B11085173 : Blo 1459549 11085173 := bbase (se 5 (by rfl) ⟨519617, by rfl⟩ : syracuseStep 11085173 = 1039235) (by norm_num)
theorem B3695989 : Blo 1459549 3695989 := bbase (se 5 (by rfl) ⟨173249, by rfl⟩ : syracuseStep 3695989 = 346499) (by norm_num)
theorem B3286421 : Blo 1459549 3286421 := bbase (se 6 (by rfl) ⟨77025, by rfl⟩ : syracuseStep 3286421 = 154051) (by norm_num)
theorem B8316341 : Blo 1459549 8316341 := bbase (se 5 (by rfl) ⟨389828, by rfl⟩ : syracuseStep 8316341 = 779657) (by norm_num)
theorem B2704853 : Blo 1459549 2704853 := bbase (se 7 (by rfl) ⟨31697, by rfl⟩ : syracuseStep 2704853 = 63395) (by norm_num)
theorem B3286493 : Blo 1459549 3286493 := bbase (se 3 (by rfl) ⟨616217, by rfl⟩ : syracuseStep 3286493 = 1232435) (by norm_num)
theorem B3696101 : Blo 1459549 3696101 := bbase (se 4 (by rfl) ⟨346509, by rfl⟩ : syracuseStep 3696101 = 693019) (by norm_num)
theorem B3286565 : Blo 1459549 3286565 := bbase (se 4 (by rfl) ⟨308115, by rfl⟩ : syracuseStep 3286565 = 616231) (by norm_num)
theorem B3286637 : Blo 1459549 3286637 := bbase (se 3 (by rfl) ⟨616244, by rfl⟩ : syracuseStep 3286637 = 1232489) (by norm_num)
theorem B3696293 : Blo 1459549 3696293 := bbase (se 4 (by rfl) ⟨346527, by rfl⟩ : syracuseStep 3696293 = 693055) (by norm_num)
theorem B3286709 : Blo 1459549 3286709 := bbase (se 5 (by rfl) ⟨154064, by rfl⟩ : syracuseStep 3286709 = 308129) (by norm_num)
theorem B2164429 : Blo 1459549 2164429 := bbase (se 3 (by rfl) ⟨405830, by rfl⟩ : syracuseStep 2164429 = 811661) (by norm_num)
theorem B3286781 : Blo 1459549 3286781 := bbase (se 3 (by rfl) ⟨616271, by rfl⟩ : syracuseStep 3286781 = 1232543) (by norm_num)
theorem B6235957 : Blo 1459549 6235957 := bbase (se 5 (by rfl) ⟨292310, by rfl⟩ : syracuseStep 6235957 = 584621) (by norm_num)
theorem B3286853 : Blo 1459549 3286853 := bbase (se 4 (by rfl) ⟨308142, by rfl⟩ : syracuseStep 3286853 = 616285) (by norm_num)
theorem B1664905 : Blo 1459549 1664905 := bbase (se 2 (by rfl) ⟨624339, by rfl⟩ : syracuseStep 1664905 = 1248679) (by norm_num)
theorem B3286925 : Blo 1459549 3286925 := bbase (se 3 (by rfl) ⟨616298, by rfl⟩ : syracuseStep 3286925 = 1232597) (by norm_num)
theorem B14034869 : Blo 1459549 14034869 := bbase (se 5 (by rfl) ⟨657884, by rfl⟩ : syracuseStep 14034869 = 1315769) (by norm_num)
theorem B1755065 : Blo 1459549 1755065 := bbase (se 2 (by rfl) ⟨658149, by rfl⟩ : syracuseStep 1755065 = 1316299) (by norm_num)
theorem B3286997 : Blo 1459549 3286997 := bbase (se 7 (by rfl) ⟨38519, by rfl⟩ : syracuseStep 3286997 = 77039) (by norm_num)
theorem B1755113 : Blo 1459549 1755113 := bbase (se 2 (by rfl) ⟨658167, by rfl⟩ : syracuseStep 1755113 = 1316335) (by norm_num)
theorem B3696637 : Blo 1459549 3696637 := bbase (se 3 (by rfl) ⟨693119, by rfl⟩ : syracuseStep 3696637 = 1386239) (by norm_num)
theorem B2189333 : Blo 1459549 2189333 := bbase (se 6 (by rfl) ⟨51312, by rfl⟩ : syracuseStep 2189333 = 102625) (by norm_num)
theorem B3287069 : Blo 1459549 3287069 := bbase (se 3 (by rfl) ⟨616325, by rfl⟩ : syracuseStep 3287069 = 1232651) (by norm_num)
theorem B2189357 : Blo 1459549 2189357 := bbase (se 3 (by rfl) ⟨410504, by rfl⟩ : syracuseStep 2189357 = 821009) (by norm_num)
theorem B2771005 : Blo 1459549 2771005 := bbase (se 3 (by rfl) ⟨519563, by rfl⟩ : syracuseStep 2771005 = 1039127) (by norm_num)
theorem B3508285 : Blo 1459549 3508285 := bbase (se 3 (by rfl) ⟨657803, by rfl⟩ : syracuseStep 3508285 = 1315607) (by norm_num)
theorem B2189381 : Blo 1459549 2189381 := bbase (se 4 (by rfl) ⟨205254, by rfl⟩ : syracuseStep 2189381 = 410509) (by norm_num)
theorem B1755209 : Blo 1459549 1755209 := bbase (se 2 (by rfl) ⟨658203, by rfl⟩ : syracuseStep 1755209 = 1316407) (by norm_num)
theorem B2189405 : Blo 1459549 2189405 := bbase (se 3 (by rfl) ⟨410513, by rfl⟩ : syracuseStep 2189405 = 821027) (by norm_num)
theorem B3287141 : Blo 1459549 3287141 := bbase (se 4 (by rfl) ⟨308169, by rfl⟩ : syracuseStep 3287141 = 616339) (by norm_num)
theorem B3696749 : Blo 1459549 3696749 := bbase (se 3 (by rfl) ⟨693140, by rfl⟩ : syracuseStep 3696749 = 1386281) (by norm_num)
theorem B2189429 : Blo 1459549 2189429 := bbase (se 5 (by rfl) ⟨102629, by rfl⟩ : syracuseStep 2189429 = 205259) (by norm_num)
theorem B2189453 : Blo 1459549 2189453 := bbase (se 3 (by rfl) ⟨410522, by rfl⟩ : syracuseStep 2189453 = 821045) (by norm_num)
theorem B2189477 : Blo 1459549 2189477 := bbase (se 4 (by rfl) ⟨205263, by rfl⟩ : syracuseStep 2189477 = 410527) (by norm_num)
theorem B3287213 : Blo 1459549 3287213 := bbase (se 3 (by rfl) ⟨616352, by rfl⟩ : syracuseStep 3287213 = 1232705) (by norm_num)
theorem B2189501 : Blo 1459549 2189501 := bbase (se 3 (by rfl) ⟨410531, by rfl⟩ : syracuseStep 2189501 = 821063) (by norm_num)
theorem B2189525 : Blo 1459549 2189525 := bbase (se 7 (by rfl) ⟨25658, by rfl⟩ : syracuseStep 2189525 = 51317) (by norm_num)
theorem B2959573 : Blo 1459549 2959573 := bbase (se 7 (by rfl) ⟨34682, by rfl⟩ : syracuseStep 2959573 = 69365) (by norm_num)
theorem B2771165 : Blo 1459549 2771165 := bbase (se 3 (by rfl) ⟨519593, by rfl⟩ : syracuseStep 2771165 = 1039187) (by norm_num)
theorem B7407845 : Blo 1459549 7407845 := bbase (se 4 (by rfl) ⟨694485, by rfl⟩ : syracuseStep 7407845 = 1388971) (by norm_num)
theorem B2189549 : Blo 1459549 2189549 := bbase (se 3 (by rfl) ⟨410540, by rfl⟩ : syracuseStep 2189549 = 821081) (by norm_num)
theorem B3287285 : Blo 1459549 3287285 := bbase (se 5 (by rfl) ⟨154091, by rfl⟩ : syracuseStep 3287285 = 308183) (by norm_num)
theorem B2189573 : Blo 1459549 2189573 := bbase (se 4 (by rfl) ⟨205272, by rfl⟩ : syracuseStep 2189573 = 410545) (by norm_num)
theorem B1665293 : Blo 1459549 1665293 := bbase (se 3 (by rfl) ⟨312242, by rfl⟩ : syracuseStep 1665293 = 624485) (by norm_num)
theorem B2189597 : Blo 1459549 2189597 := bbase (se 3 (by rfl) ⟨410549, by rfl⟩ : syracuseStep 2189597 = 821099) (by norm_num)
theorem B3696941 : Blo 1459549 3696941 := bbase (se 3 (by rfl) ⟨693176, by rfl⟩ : syracuseStep 3696941 = 1386353) (by norm_num)
theorem B2189621 : Blo 1459549 2189621 := bbase (se 5 (by rfl) ⟨102638, by rfl⟩ : syracuseStep 2189621 = 205277) (by norm_num)
theorem B3287357 : Blo 1459549 3287357 := bbase (se 3 (by rfl) ⟨616379, by rfl⟩ : syracuseStep 3287357 = 1232759) (by norm_num)
theorem B2189645 : Blo 1459549 2189645 := bbase (se 3 (by rfl) ⟨410558, by rfl⟩ : syracuseStep 2189645 = 821117) (by norm_num)
theorem B7391573 : Blo 1459549 7391573 := bbase (se 10 (by rfl) ⟨10827, by rfl⟩ : syracuseStep 7391573 = 21655) (by norm_num)
theorem B2189669 : Blo 1459549 2189669 := bbase (se 4 (by rfl) ⟨205281, by rfl⟩ : syracuseStep 2189669 = 410563) (by norm_num)
theorem B2771309 : Blo 1459549 2771309 := bbase (se 3 (by rfl) ⟨519620, by rfl⟩ : syracuseStep 2771309 = 1039241) (by norm_num)
theorem B4442485 : Blo 1459549 4442485 := bbase (se 5 (by rfl) ⟨208241, by rfl⟩ : syracuseStep 4442485 = 416483) (by norm_num)
theorem B2189693 : Blo 1459549 2189693 := bbase (se 3 (by rfl) ⟨410567, by rfl⟩ : syracuseStep 2189693 = 821135) (by norm_num)
theorem B6752645 : Blo 1459549 6752645 := bbase (se 4 (by rfl) ⟨633060, by rfl⟩ : syracuseStep 6752645 = 1266121) (by norm_num)
theorem B2189717 : Blo 1459549 2189717 := bbase (se 6 (by rfl) ⟨51321, by rfl⟩ : syracuseStep 2189717 = 102643) (by norm_num)
theorem B2189741 : Blo 1459549 2189741 := bbase (se 3 (by rfl) ⟨410576, by rfl⟩ : syracuseStep 2189741 = 821153) (by norm_num)
theorem B2189765 : Blo 1459549 2189765 := bbase (se 4 (by rfl) ⟨205290, by rfl⟩ : syracuseStep 2189765 = 410581) (by norm_num)
theorem B2189789 : Blo 1459549 2189789 := bbase (se 3 (by rfl) ⟨410585, by rfl⟩ : syracuseStep 2189789 = 821171) (by norm_num)
theorem B2189813 : Blo 1459549 2189813 := bbase (se 5 (by rfl) ⟨102647, by rfl⟩ : syracuseStep 2189813 = 205295) (by norm_num)
theorem B2189837 : Blo 1459549 2189837 := bbase (se 3 (by rfl) ⟨410594, by rfl⟩ : syracuseStep 2189837 = 821189) (by norm_num)
theorem B2189861 : Blo 1459549 2189861 := bbase (se 4 (by rfl) ⟨205299, by rfl⟩ : syracuseStep 2189861 = 410599) (by norm_num)
theorem B2107949 : Blo 1459549 2107949 := bbase (se 3 (by rfl) ⟨395240, by rfl⟩ : syracuseStep 2107949 = 790481) (by norm_num)
theorem B2189885 : Blo 1459549 2189885 := bbase (se 3 (by rfl) ⟨410603, by rfl⟩ : syracuseStep 2189885 = 821207) (by norm_num)
theorem B2189909 : Blo 1459549 2189909 := bbase (se 8 (by rfl) ⟨12831, by rfl⟩ : syracuseStep 2189909 = 25663) (by norm_num)
theorem B8317525 : Blo 1459549 8317525 := bbase (se 8 (by rfl) ⟨48735, by rfl⟩ : syracuseStep 8317525 = 97471) (by norm_num)
theorem B2189933 : Blo 1459549 2189933 := bbase (se 3 (by rfl) ⟨410612, by rfl⟩ : syracuseStep 2189933 = 821225) (by norm_num)
theorem B2189957 : Blo 1459549 2189957 := bbase (se 4 (by rfl) ⟨205308, by rfl⟩ : syracuseStep 2189957 = 410617) (by norm_num)
theorem B3697285 : Blo 1459549 3697285 := bbase (se 4 (by rfl) ⟨346620, by rfl⟩ : syracuseStep 3697285 = 693241) (by norm_num)
theorem B2771597 : Blo 1459549 2771597 := bbase (se 3 (by rfl) ⟨519674, by rfl⟩ : syracuseStep 2771597 = 1039349) (by norm_num)
theorem B2189981 : Blo 1459549 2189981 := bbase (se 3 (by rfl) ⟨410621, by rfl⟩ : syracuseStep 2189981 = 821243) (by norm_num)
theorem B2190005 : Blo 1459549 2190005 := bbase (se 5 (by rfl) ⟨102656, by rfl⟩ : syracuseStep 2190005 = 205313) (by norm_num)
theorem B4926149 : Blo 1459549 4926149 := bbase (se 4 (by rfl) ⟨461826, by rfl⟩ : syracuseStep 4926149 = 923653) (by norm_num)
theorem B2190029 : Blo 1459549 2190029 := bbase (se 3 (by rfl) ⟨410630, by rfl⟩ : syracuseStep 2190029 = 821261) (by norm_num)
theorem B9358037 : Blo 1459549 9358037 := bbase (se 7 (by rfl) ⟨109664, by rfl⟩ : syracuseStep 9358037 = 219329) (by norm_num)
theorem B2190053 : Blo 1459549 2190053 := bbase (se 4 (by rfl) ⟨205317, by rfl⟩ : syracuseStep 2190053 = 410635) (by norm_num)
theorem B3697397 : Blo 1459549 3697397 := bbase (se 5 (by rfl) ⟨173315, by rfl⟩ : syracuseStep 3697397 = 346631) (by norm_num)
theorem B2190077 : Blo 1459549 2190077 := bbase (se 3 (by rfl) ⟨410639, by rfl⟩ : syracuseStep 2190077 = 821279) (by norm_num)
theorem B1559297 : Blo 1459549 1559297 := bbase (se 2 (by rfl) ⟨584736, by rfl⟩ : syracuseStep 1559297 = 1169473) (by norm_num)
theorem B26995477 : Blo 1459549 26995477 := bbase (se 6 (by rfl) ⟨632706, by rfl⟩ : syracuseStep 26995477 = 1265413) (by norm_num)
theorem B2190101 : Blo 1459549 2190101 := bbase (se 6 (by rfl) ⟨51330, by rfl⟩ : syracuseStep 2190101 = 102661) (by norm_num)
theorem B2771749 : Blo 1459549 2771749 := bbase (se 4 (by rfl) ⟨259851, by rfl⟩ : syracuseStep 2771749 = 519703) (by norm_num)
theorem B2190125 : Blo 1459549 2190125 := bbase (se 3 (by rfl) ⟨410648, by rfl⟩ : syracuseStep 2190125 = 821297) (by norm_num)
theorem B2190149 : Blo 1459549 2190149 := bbase (se 4 (by rfl) ⟨205326, by rfl⟩ : syracuseStep 2190149 = 410653) (by norm_num)
theorem B2190173 : Blo 1459549 2190173 := bbase (se 3 (by rfl) ⟨410657, by rfl⟩ : syracuseStep 2190173 = 821315) (by norm_num)
theorem B2190197 : Blo 1459549 2190197 := bbase (se 5 (by rfl) ⟨102665, by rfl⟩ : syracuseStep 2190197 = 205331) (by norm_num)
theorem B2190221 : Blo 1459549 2190221 := bbase (se 3 (by rfl) ⟨410666, by rfl⟩ : syracuseStep 2190221 = 821333) (by norm_num)
theorem B2190245 : Blo 1459549 2190245 := bbase (se 4 (by rfl) ⟨205335, by rfl⟩ : syracuseStep 2190245 = 410671) (by norm_num)
theorem B9481141 : Blo 1459549 9481141 := bbase (se 5 (by rfl) ⟨444428, by rfl⟩ : syracuseStep 9481141 = 888857) (by norm_num)
theorem B3697589 : Blo 1459549 3697589 := bbase (se 5 (by rfl) ⟨173324, by rfl⟩ : syracuseStep 3697589 = 346649) (by norm_num)
theorem B2190269 : Blo 1459549 2190269 := bbase (se 3 (by rfl) ⟨410675, by rfl⟩ : syracuseStep 2190269 = 821351) (by norm_num)
theorem B9989077 : Blo 1459549 9989077 := bbase (se 7 (by rfl) ⟨117059, by rfl⟩ : syracuseStep 9989077 = 234119) (by norm_num)
theorem B2190293 : Blo 1459549 2190293 := bbase (se 7 (by rfl) ⟨25667, by rfl⟩ : syracuseStep 2190293 = 51335) (by norm_num)
theorem B2190317 : Blo 1459549 2190317 := bbase (se 3 (by rfl) ⟨410684, by rfl⟩ : syracuseStep 2190317 = 821369) (by norm_num)
theorem B2190341 : Blo 1459549 2190341 := bbase (se 4 (by rfl) ⟨205344, by rfl⟩ : syracuseStep 2190341 = 410689) (by norm_num)
theorem B18721813 : Blo 1459549 18721813 := bbase (se 6 (by rfl) ⟨438792, by rfl⟩ : syracuseStep 18721813 = 877585) (by norm_num)
theorem B1666073 : Blo 1459549 1666073 := bbase (se 2 (by rfl) ⟨624777, by rfl⟩ : syracuseStep 1666073 = 1249555) (by norm_num)
theorem B2190365 : Blo 1459549 2190365 := bbase (se 3 (by rfl) ⟨410693, by rfl⟩ : syracuseStep 2190365 = 821387) (by norm_num)
theorem B2190389 : Blo 1459549 2190389 := bbase (se 5 (by rfl) ⟨102674, by rfl⟩ : syracuseStep 2190389 = 205349) (by norm_num)
theorem B2190413 : Blo 1459549 2190413 := bbase (se 3 (by rfl) ⟨410702, by rfl⟩ : syracuseStep 2190413 = 821405) (by norm_num)
theorem B2772053 : Blo 1459549 2772053 := bbase (se 8 (by rfl) ⟨16242, by rfl⟩ : syracuseStep 2772053 = 32485) (by norm_num)
theorem B2190437 : Blo 1459549 2190437 := bbase (se 4 (by rfl) ⟨205353, by rfl⟩ : syracuseStep 2190437 = 410707) (by norm_num)
theorem B4926581 : Blo 1459549 4926581 := bbase (se 5 (by rfl) ⟨230933, by rfl⟩ : syracuseStep 4926581 = 461867) (by norm_num)
theorem B9989237 : Blo 1459549 9989237 := bbase (se 5 (by rfl) ⟨468245, by rfl⟩ : syracuseStep 9989237 = 936491) (by norm_num)
theorem B2190461 : Blo 1459549 2190461 := bbase (se 3 (by rfl) ⟨410711, by rfl⟩ : syracuseStep 2190461 = 821423) (by norm_num)
theorem B2190485 : Blo 1459549 2190485 := bbase (se 6 (by rfl) ⟨51339, by rfl⟩ : syracuseStep 2190485 = 102679) (by norm_num)
theorem B2190509 : Blo 1459549 2190509 := bbase (se 3 (by rfl) ⟨410720, by rfl⟩ : syracuseStep 2190509 = 821441) (by norm_num)
theorem B1559741 : Blo 1459549 1559741 := bbase (se 3 (by rfl) ⟨292451, by rfl⟩ : syracuseStep 1559741 = 584903) (by norm_num)
theorem B2190533 : Blo 1459549 2190533 := bbase (se 4 (by rfl) ⟨205362, by rfl⟩ : syracuseStep 2190533 = 410725) (by norm_num)
theorem B2190557 : Blo 1459549 2190557 := bbase (se 3 (by rfl) ⟨410729, by rfl⟩ : syracuseStep 2190557 = 821459) (by norm_num)
theorem B2190581 : Blo 1459549 2190581 := bbase (se 5 (by rfl) ⟨102683, by rfl⟩ : syracuseStep 2190581 = 205367) (by norm_num)
theorem B6237445 : Blo 1459549 6237445 := bbase (se 4 (by rfl) ⟨584760, by rfl⟩ : syracuseStep 6237445 = 1169521) (by norm_num)
theorem B2190605 : Blo 1459549 2190605 := bbase (se 3 (by rfl) ⟨410738, by rfl⟩ : syracuseStep 2190605 = 821477) (by norm_num)
theorem B3697933 : Blo 1459549 3697933 := bbase (se 3 (by rfl) ⟨693362, by rfl⟩ : syracuseStep 3697933 = 1386725) (by norm_num)
theorem B6237461 : Blo 1459549 6237461 := bbase (se 6 (by rfl) ⟨146190, by rfl⟩ : syracuseStep 6237461 = 292381) (by norm_num)
theorem B2190629 : Blo 1459549 2190629 := bbase (se 4 (by rfl) ⟨205371, by rfl⟩ : syracuseStep 2190629 = 410743) (by norm_num)
theorem B2190653 : Blo 1459549 2190653 := bbase (se 3 (by rfl) ⟨410747, by rfl⟩ : syracuseStep 2190653 = 821495) (by norm_num)
theorem B2190677 : Blo 1459549 2190677 := bbase (se 11 (by rfl) ⟨1604, by rfl⟩ : syracuseStep 2190677 = 3209) (by norm_num)
theorem B6663509 : Blo 1459549 6663509 := bbase (se 11 (by rfl) ⟨4880, by rfl⟩ : syracuseStep 6663509 = 9761) (by norm_num)
theorem B3796325 : Blo 1459549 3796325 := bbase (se 4 (by rfl) ⟨355905, by rfl⟩ : syracuseStep 3796325 = 711811) (by norm_num)
theorem B2190701 : Blo 1459549 2190701 := bbase (se 3 (by rfl) ⟨410756, by rfl⟩ : syracuseStep 2190701 = 821513) (by norm_num)
theorem B3698045 : Blo 1459549 3698045 := bbase (se 3 (by rfl) ⟨693383, by rfl⟩ : syracuseStep 3698045 = 1386767) (by norm_num)
theorem B2190725 : Blo 1459549 2190725 := bbase (se 4 (by rfl) ⟨205380, by rfl⟩ : syracuseStep 2190725 = 410761) (by norm_num)
theorem B2190749 : Blo 1459549 2190749 := bbase (se 3 (by rfl) ⟨410765, by rfl⟩ : syracuseStep 2190749 = 821531) (by norm_num)
theorem B3509669 : Blo 1459549 3509669 := bbase (se 4 (by rfl) ⟨329031, by rfl⟩ : syracuseStep 3509669 = 658063) (by norm_num)
theorem B2960813 : Blo 1459549 2960813 := bbase (se 3 (by rfl) ⟨555152, by rfl⟩ : syracuseStep 2960813 = 1110305) (by norm_num)
theorem B2190773 : Blo 1459549 2190773 := bbase (se 5 (by rfl) ⟨102692, by rfl⟩ : syracuseStep 2190773 = 205385) (by norm_num)
theorem B1559989 : Blo 1459549 1559989 := bbase (se 5 (by rfl) ⟨73124, by rfl⟩ : syracuseStep 1559989 = 146249) (by norm_num)
theorem B2190797 : Blo 1459549 2190797 := bbase (se 3 (by rfl) ⟨410774, by rfl⟩ : syracuseStep 2190797 = 821549) (by norm_num)
theorem B2190821 : Blo 1459549 2190821 := bbase (se 4 (by rfl) ⟨205389, by rfl⟩ : syracuseStep 2190821 = 410779) (by norm_num)
theorem B2190845 : Blo 1459549 2190845 := bbase (se 3 (by rfl) ⟨410783, by rfl⟩ : syracuseStep 2190845 = 821567) (by norm_num)
theorem B2338325 : Blo 1459549 2338325 := bbase (se 6 (by rfl) ⟨54804, by rfl⟩ : syracuseStep 2338325 = 109609) (by norm_num)
theorem B2190869 : Blo 1459549 2190869 := bbase (se 6 (by rfl) ⟨51348, by rfl⟩ : syracuseStep 2190869 = 102697) (by norm_num)
theorem B1642009 : Blo 1459549 1642009 := bbase (se 2 (by rfl) ⟨615753, by rfl⟩ : syracuseStep 1642009 = 1231507) (by norm_num)
theorem B4927013 : Blo 1459549 4927013 := bbase (se 4 (by rfl) ⟨461907, by rfl⟩ : syracuseStep 4927013 = 923815) (by norm_num)
theorem B2190893 : Blo 1459549 2190893 := bbase (se 3 (by rfl) ⟨410792, by rfl⟩ : syracuseStep 2190893 = 821585) (by norm_num)
theorem B1642045 : Blo 1459549 1642045 := bbase (se 3 (by rfl) ⟨307883, by rfl⟩ : syracuseStep 1642045 = 615767) (by norm_num)
theorem B3698237 : Blo 1459549 3698237 := bbase (se 3 (by rfl) ⟨693419, by rfl⟩ : syracuseStep 3698237 = 1386839) (by norm_num)
theorem B2190917 : Blo 1459549 2190917 := bbase (se 4 (by rfl) ⟨205398, by rfl⟩ : syracuseStep 2190917 = 410797) (by norm_num)
theorem B2190941 : Blo 1459549 2190941 := bbase (se 3 (by rfl) ⟨410801, by rfl⟩ : syracuseStep 2190941 = 821603) (by norm_num)
theorem B1642081 : Blo 1459549 1642081 := bbase (se 2 (by rfl) ⟨615780, by rfl⟩ : syracuseStep 1642081 = 1231561) (by norm_num)
theorem B7392869 : Blo 1459549 7392869 := bbase (se 4 (by rfl) ⟨693081, by rfl⟩ : syracuseStep 7392869 = 1386163) (by norm_num)
theorem B2190965 : Blo 1459549 2190965 := bbase (se 5 (by rfl) ⟨102701, by rfl⟩ : syracuseStep 2190965 = 205403) (by norm_num)
theorem B1642117 : Blo 1459549 1642117 := bbase (se 4 (by rfl) ⟨153948, by rfl⟩ : syracuseStep 1642117 = 307897) (by norm_num)
theorem B2190989 : Blo 1459549 2190989 := bbase (se 3 (by rfl) ⟨410810, by rfl⟩ : syracuseStep 2190989 = 821621) (by norm_num)
theorem B4157077 : Blo 1459549 4157077 := bbase (se 6 (by rfl) ⟨97431, by rfl⟩ : syracuseStep 4157077 = 194863) (by norm_num)
theorem B2191013 : Blo 1459549 2191013 := bbase (se 4 (by rfl) ⟨205407, by rfl⟩ : syracuseStep 2191013 = 410815) (by norm_num)
theorem B1642153 : Blo 1459549 1642153 := bbase (se 2 (by rfl) ⟨615807, by rfl⟩ : syracuseStep 1642153 = 1231615) (by norm_num)
theorem B2191037 : Blo 1459549 2191037 := bbase (se 3 (by rfl) ⟨410819, by rfl⟩ : syracuseStep 2191037 = 821639) (by norm_num)
theorem B1642189 : Blo 1459549 1642189 := bbase (se 3 (by rfl) ⟨307910, by rfl⟩ : syracuseStep 1642189 = 615821) (by norm_num)
theorem B2191061 : Blo 1459549 2191061 := bbase (se 7 (by rfl) ⟨25676, by rfl⟩ : syracuseStep 2191061 = 51353) (by norm_num)
theorem B2191085 : Blo 1459549 2191085 := bbase (se 3 (by rfl) ⟨410828, by rfl⟩ : syracuseStep 2191085 = 821657) (by norm_num)
theorem B1642225 : Blo 1459549 1642225 := bbase (se 2 (by rfl) ⟨615834, by rfl⟩ : syracuseStep 1642225 = 1231669) (by norm_num)
theorem B2191109 : Blo 1459549 2191109 := bbase (se 4 (by rfl) ⟨205416, by rfl⟩ : syracuseStep 2191109 = 410833) (by norm_num)
theorem B1642261 : Blo 1459549 1642261 := bbase (se 6 (by rfl) ⟨38490, by rfl⟩ : syracuseStep 1642261 = 76981) (by norm_num)
theorem B2191133 : Blo 1459549 2191133 := bbase (se 3 (by rfl) ⟨410837, by rfl⟩ : syracuseStep 2191133 = 821675) (by norm_num)
theorem B4157237 : Blo 1459549 4157237 := bbase (se 5 (by rfl) ⟨194870, by rfl⟩ : syracuseStep 4157237 = 389741) (by norm_num)
theorem B2191157 : Blo 1459549 2191157 := bbase (se 5 (by rfl) ⟨102710, by rfl⟩ : syracuseStep 2191157 = 205421) (by norm_num)
theorem B1642297 : Blo 1459549 1642297 := bbase (se 2 (by rfl) ⟨615861, by rfl⟩ : syracuseStep 1642297 = 1231723) (by norm_num)
theorem B2666309 : Blo 1459549 2666309 := bbase (se 4 (by rfl) ⟨249966, by rfl⟩ : syracuseStep 2666309 = 499933) (by norm_num)
theorem B2772805 : Blo 1459549 2772805 := bbase (se 4 (by rfl) ⟨259950, by rfl⟩ : syracuseStep 2772805 = 519901) (by norm_num)
theorem B2191181 : Blo 1459549 2191181 := bbase (se 3 (by rfl) ⟨410846, by rfl⟩ : syracuseStep 2191181 = 821693) (by norm_num)
theorem B3510101 : Blo 1459549 3510101 := bbase (se 9 (by rfl) ⟨10283, by rfl⟩ : syracuseStep 3510101 = 20567) (by norm_num)
theorem B1642333 : Blo 1459549 1642333 := bbase (se 3 (by rfl) ⟨307937, by rfl⟩ : syracuseStep 1642333 = 615875) (by norm_num)
theorem B2191205 : Blo 1459549 2191205 := bbase (se 4 (by rfl) ⟨205425, by rfl⟩ : syracuseStep 2191205 = 410851) (by norm_num)
theorem B2191229 : Blo 1459549 2191229 := bbase (se 3 (by rfl) ⟨410855, by rfl⟩ : syracuseStep 2191229 = 821711) (by norm_num)
theorem B1642369 : Blo 1459549 1642369 := bbase (se 2 (by rfl) ⟨615888, by rfl⟩ : syracuseStep 1642369 = 1231777) (by norm_num)
theorem B2191253 : Blo 1459549 2191253 := bbase (se 6 (by rfl) ⟨51357, by rfl⟩ : syracuseStep 2191253 = 102715) (by norm_num)
theorem B5541797 : Blo 1459549 5541797 := bbase (se 4 (by rfl) ⟨519543, by rfl⟩ : syracuseStep 5541797 = 1039087) (by norm_num)
theorem B1642405 : Blo 1459549 1642405 := bbase (se 4 (by rfl) ⟨153975, by rfl⟩ : syracuseStep 1642405 = 307951) (by norm_num)
theorem B2191277 : Blo 1459549 2191277 := bbase (se 3 (by rfl) ⟨410864, by rfl⟩ : syracuseStep 2191277 = 821729) (by norm_num)
theorem B2191301 : Blo 1459549 2191301 := bbase (se 4 (by rfl) ⟨205434, by rfl⟩ : syracuseStep 2191301 = 410869) (by norm_num)
theorem B1642441 : Blo 1459549 1642441 := bbase (se 2 (by rfl) ⟨615915, by rfl⟩ : syracuseStep 1642441 = 1231831) (by norm_num)
theorem B17756117 : Blo 1459549 17756117 := bbase (se 7 (by rfl) ⟨208079, by rfl⟩ : syracuseStep 17756117 = 416159) (by norm_num)
theorem B4927445 : Blo 1459549 4927445 := bbase (se 7 (by rfl) ⟨57743, by rfl⟩ : syracuseStep 4927445 = 115487) (by norm_num)
theorem B2772949 : Blo 1459549 2772949 := bbase (se 7 (by rfl) ⟨32495, by rfl⟩ : syracuseStep 2772949 = 64991) (by norm_num)
theorem B2191325 : Blo 1459549 2191325 := bbase (se 3 (by rfl) ⟨410873, by rfl⟩ : syracuseStep 2191325 = 821747) (by norm_num)
theorem B1642477 : Blo 1459549 1642477 := bbase (se 3 (by rfl) ⟨307964, by rfl⟩ : syracuseStep 1642477 = 615929) (by norm_num)
theorem B1847281 : Blo 1459549 1847281 := bbase (se 2 (by rfl) ⟨692730, by rfl⟩ : syracuseStep 1847281 = 1385461) (by norm_num)
theorem B2191349 : Blo 1459549 2191349 := bbase (se 5 (by rfl) ⟨102719, by rfl⟩ : syracuseStep 2191349 = 205439) (by norm_num)
theorem B2191373 : Blo 1459549 2191373 := bbase (se 3 (by rfl) ⟨410882, by rfl⟩ : syracuseStep 2191373 = 821765) (by norm_num)
theorem B1642513 : Blo 1459549 1642513 := bbase (se 2 (by rfl) ⟨615942, by rfl⟩ : syracuseStep 1642513 = 1231885) (by norm_num)
theorem B4157477 : Blo 1459549 4157477 := bbase (se 4 (by rfl) ⟨389763, by rfl⟩ : syracuseStep 4157477 = 779527) (by norm_num)
theorem B2191397 : Blo 1459549 2191397 := bbase (se 4 (by rfl) ⟨205443, by rfl⟩ : syracuseStep 2191397 = 410887) (by norm_num)
theorem B1642549 : Blo 1459549 1642549 := bbase (se 5 (by rfl) ⟨76994, by rfl⟩ : syracuseStep 1642549 = 153989) (by norm_num)
theorem B2191421 : Blo 1459549 2191421 := bbase (se 3 (by rfl) ⟨410891, by rfl⟩ : syracuseStep 2191421 = 821783) (by norm_num)
theorem B1847377 : Blo 1459549 1847377 := bbase (se 2 (by rfl) ⟨692766, by rfl⟩ : syracuseStep 1847377 = 1385533) (by norm_num)
theorem B2191445 : Blo 1459549 2191445 := bbase (se 8 (by rfl) ⟨12840, by rfl⟩ : syracuseStep 2191445 = 25681) (by norm_num)
theorem B1642585 : Blo 1459549 1642585 := bbase (se 2 (by rfl) ⟨615969, by rfl⟩ : syracuseStep 1642585 = 1231939) (by norm_num)
theorem B7491685 : Blo 1459549 7491685 := bbase (se 4 (by rfl) ⟨702345, by rfl⟩ : syracuseStep 7491685 = 1404691) (by norm_num)
theorem B2191469 : Blo 1459549 2191469 := bbase (se 3 (by rfl) ⟨410900, by rfl⟩ : syracuseStep 2191469 = 821801) (by norm_num)
theorem B2773109 : Blo 1459549 2773109 := bbase (se 5 (by rfl) ⟨129989, by rfl⟩ : syracuseStep 2773109 = 259979) (by norm_num)
theorem B1642621 : Blo 1459549 1642621 := bbase (se 3 (by rfl) ⟨307991, by rfl⟩ : syracuseStep 1642621 = 615983) (by norm_num)
theorem B2191493 : Blo 1459549 2191493 := bbase (se 4 (by rfl) ⟨205452, by rfl⟩ : syracuseStep 2191493 = 410905) (by norm_num)
theorem B2191517 : Blo 1459549 2191517 := bbase (se 3 (by rfl) ⟨410909, by rfl⟩ : syracuseStep 2191517 = 821819) (by norm_num)
theorem B1642657 : Blo 1459549 1642657 := bbase (se 2 (by rfl) ⟨615996, by rfl⟩ : syracuseStep 1642657 = 1231993) (by norm_num)
theorem B2191541 : Blo 1459549 2191541 := bbase (se 5 (by rfl) ⟨102728, by rfl⟩ : syracuseStep 2191541 = 205457) (by norm_num)
theorem B1642693 : Blo 1459549 1642693 := bbase (se 4 (by rfl) ⟨154002, by rfl⟩ : syracuseStep 1642693 = 308005) (by norm_num)
theorem B2887877 : Blo 1459549 2887877 := bbase (se 4 (by rfl) ⟨270738, by rfl⟩ : syracuseStep 2887877 = 541477) (by norm_num)
theorem B2191565 : Blo 1459549 2191565 := bbase (se 3 (by rfl) ⟨410918, by rfl⟩ : syracuseStep 2191565 = 821837) (by norm_num)
theorem B5918933 : Blo 1459549 5918933 := bbase (se 7 (by rfl) ⟨69362, by rfl⟩ : syracuseStep 5918933 = 138725) (by norm_num)
theorem B4157669 : Blo 1459549 4157669 := bbase (se 4 (by rfl) ⟨389781, by rfl⟩ : syracuseStep 4157669 = 779563) (by norm_num)
theorem B1642729 : Blo 1459549 1642729 := bbase (se 2 (by rfl) ⟨616023, by rfl⟩ : syracuseStep 1642729 = 1232047) (by norm_num)
theorem B1847549 : Blo 1459549 1847549 := bbase (se 3 (by rfl) ⟨346415, by rfl⟩ : syracuseStep 1847549 = 692831) (by norm_num)
theorem B2773253 : Blo 1459549 2773253 := bbase (se 4 (by rfl) ⟨259992, by rfl⟩ : syracuseStep 2773253 = 519985) (by norm_num)
theorem B1642765 : Blo 1459549 1642765 := bbase (se 3 (by rfl) ⟨308018, by rfl⟩ : syracuseStep 1642765 = 616037) (by norm_num)
theorem B1642801 : Blo 1459549 1642801 := bbase (se 2 (by rfl) ⟨616050, by rfl⟩ : syracuseStep 1642801 = 1232101) (by norm_num)
theorem B1847605 : Blo 1459549 1847605 := bbase (se 5 (by rfl) ⟨86606, by rfl⟩ : syracuseStep 1847605 = 173213) (by norm_num)
theorem B1642837 : Blo 1459549 1642837 := bbase (se 10 (by rfl) ⟨2406, by rfl⟩ : syracuseStep 1642837 = 4813) (by norm_num)
theorem B1642873 : Blo 1459549 1642873 := bbase (se 2 (by rfl) ⟨616077, by rfl⟩ : syracuseStep 1642873 = 1232155) (by norm_num)
theorem B4927877 : Blo 1459549 4927877 := bbase (se 4 (by rfl) ⟨461988, by rfl⟩ : syracuseStep 4927877 = 923977) (by norm_num)
theorem B1847701 : Blo 1459549 1847701 := bbase (se 6 (by rfl) ⟨43305, by rfl⟩ : syracuseStep 1847701 = 86611) (by norm_num)
theorem B1642909 : Blo 1459549 1642909 := bbase (se 3 (by rfl) ⟨308045, by rfl⟩ : syracuseStep 1642909 = 616091) (by norm_num)
theorem B1642945 : Blo 1459549 1642945 := bbase (se 2 (by rfl) ⟨616104, by rfl⟩ : syracuseStep 1642945 = 1232209) (by norm_num)
theorem B1642981 : Blo 1459549 1642981 := bbase (se 4 (by rfl) ⟨154029, by rfl⟩ : syracuseStep 1642981 = 308059) (by norm_num)
theorem B1643017 : Blo 1459549 1643017 := bbase (se 2 (by rfl) ⟨616131, by rfl⟩ : syracuseStep 1643017 = 1232263) (by norm_num)
theorem B8319509 : Blo 1459549 8319509 := bbase (se 6 (by rfl) ⟨194988, by rfl⟩ : syracuseStep 8319509 = 389977) (by norm_num)
theorem B2773541 : Blo 1459549 2773541 := bbase (se 4 (by rfl) ⟨260019, by rfl⟩ : syracuseStep 2773541 = 520039) (by norm_num)
theorem B1643053 : Blo 1459549 1643053 := bbase (se 3 (by rfl) ⟨308072, by rfl⟩ : syracuseStep 1643053 = 616145) (by norm_num)
theorem B9351733 : Blo 1459549 9351733 := bbase (se 5 (by rfl) ⟨438362, by rfl⟩ : syracuseStep 9351733 = 876725) (by norm_num)
theorem B3117629 : Blo 1459549 3117629 := bbase (se 3 (by rfl) ⟨584555, by rfl⟩ : syracuseStep 3117629 = 1169111) (by norm_num)
theorem B1847873 : Blo 1459549 1847873 := bbase (se 2 (by rfl) ⟨692952, by rfl⟩ : syracuseStep 1847873 = 1385905) (by norm_num)
theorem B3117637 : Blo 1459549 3117637 := bbase (se 4 (by rfl) ⟨292278, by rfl⟩ : syracuseStep 3117637 = 584557) (by norm_num)
theorem B1643089 : Blo 1459549 1643089 := bbase (se 2 (by rfl) ⟨616158, by rfl⟩ : syracuseStep 1643089 = 1232317) (by norm_num)
theorem B1643125 : Blo 1459549 1643125 := bbase (se 5 (by rfl) ⟨77021, by rfl⟩ : syracuseStep 1643125 = 154043) (by norm_num)
theorem B1847929 : Blo 1459549 1847929 := bbase (se 2 (by rfl) ⟨692973, by rfl⟩ : syracuseStep 1847929 = 1385947) (by norm_num)
theorem B1643161 : Blo 1459549 1643161 := bbase (se 2 (by rfl) ⟨616185, by rfl⟩ : syracuseStep 1643161 = 1232371) (by norm_num)
theorem B1643197 : Blo 1459549 1643197 := bbase (se 3 (by rfl) ⟨308099, by rfl⟩ : syracuseStep 1643197 = 616199) (by norm_num)
theorem B2773693 : Blo 1459549 2773693 := bbase (se 3 (by rfl) ⟨520067, by rfl⟩ : syracuseStep 2773693 = 1040135) (by norm_num)
theorem B1848025 : Blo 1459549 1848025 := bbase (se 2 (by rfl) ⟨693009, by rfl⟩ : syracuseStep 1848025 = 1386019) (by norm_num)
theorem B1643233 : Blo 1459549 1643233 := bbase (se 2 (by rfl) ⟨616212, by rfl⟩ : syracuseStep 1643233 = 1232425) (by norm_num)
theorem B1872625 : Blo 1459549 1872625 := bbase (se 2 (by rfl) ⟨702234, by rfl⟩ : syracuseStep 1872625 = 1404469) (by norm_num)
theorem B2667269 : Blo 1459549 2667269 := bbase (se 4 (by rfl) ⟨250056, by rfl⟩ : syracuseStep 2667269 = 500113) (by norm_num)
theorem B1643269 : Blo 1459549 1643269 := bbase (se 4 (by rfl) ⟨154056, by rfl⟩ : syracuseStep 1643269 = 308113) (by norm_num)
theorem B1643305 : Blo 1459549 1643305 := bbase (se 2 (by rfl) ⟨616239, by rfl⟩ : syracuseStep 1643305 = 1232479) (by norm_num)
theorem B4928309 : Blo 1459549 4928309 := bbase (se 5 (by rfl) ⟨231014, by rfl⟩ : syracuseStep 4928309 = 462029) (by norm_num)
theorem B1643341 : Blo 1459549 1643341 := bbase (se 3 (by rfl) ⟨308126, by rfl⟩ : syracuseStep 1643341 = 616253) (by norm_num)
theorem B1643377 : Blo 1459549 1643377 := bbase (se 2 (by rfl) ⟨616266, by rfl⟩ : syracuseStep 1643377 = 1232533) (by norm_num)
theorem B7394165 : Blo 1459549 7394165 := bbase (se 5 (by rfl) ⟨346601, by rfl⟩ : syracuseStep 7394165 = 693203) (by norm_num)
theorem B1848197 : Blo 1459549 1848197 := bbase (se 4 (by rfl) ⟨173268, by rfl⟩ : syracuseStep 1848197 = 346537) (by norm_num)
theorem B8426389 : Blo 1459549 8426389 := bbase (se 6 (by rfl) ⟨197493, by rfl⟩ : syracuseStep 8426389 = 394987) (by norm_num)
theorem B1643413 : Blo 1459549 1643413 := bbase (se 6 (by rfl) ⟨38517, by rfl⟩ : syracuseStep 1643413 = 77035) (by norm_num)
theorem B2339741 : Blo 1459549 2339741 := bbase (se 3 (by rfl) ⟨438701, by rfl⟩ : syracuseStep 2339741 = 877403) (by norm_num)
theorem B1643449 : Blo 1459549 1643449 := bbase (se 2 (by rfl) ⟨616293, by rfl⟩ : syracuseStep 1643449 = 1232587) (by norm_num)
theorem B1848253 : Blo 1459549 1848253 := bbase (se 3 (by rfl) ⟨346547, by rfl⟩ : syracuseStep 1848253 = 693095) (by norm_num)
theorem B1643485 : Blo 1459549 1643485 := bbase (se 3 (by rfl) ⟨308153, by rfl⟩ : syracuseStep 1643485 = 616307) (by norm_num)
theorem B5264357 : Blo 1459549 5264357 := bbase (se 4 (by rfl) ⟨493533, by rfl⟩ : syracuseStep 5264357 = 987067) (by norm_num)
theorem B2888677 : Blo 1459549 2888677 := bbase (se 4 (by rfl) ⟨270813, by rfl⟩ : syracuseStep 2888677 = 541627) (by norm_num)
theorem B1643521 : Blo 1459549 1643521 := bbase (se 2 (by rfl) ⟨616320, by rfl⟩ : syracuseStep 1643521 = 1232641) (by norm_num)
theorem B1848349 : Blo 1459549 1848349 := bbase (se 3 (by rfl) ⟨346565, by rfl⟩ : syracuseStep 1848349 = 693131) (by norm_num)
theorem B1643557 : Blo 1459549 1643557 := bbase (se 4 (by rfl) ⟨154083, by rfl⟩ : syracuseStep 1643557 = 308167) (by norm_num)
theorem B1643593 : Blo 1459549 1643593 := bbase (se 2 (by rfl) ⟨616347, by rfl⟩ : syracuseStep 1643593 = 1232695) (by norm_num)
theorem B1643629 : Blo 1459549 1643629 := bbase (se 3 (by rfl) ⟨308180, by rfl⟩ : syracuseStep 1643629 = 616361) (by norm_num)
theorem B2339965 : Blo 1459549 2339965 := bbase (se 3 (by rfl) ⟨438743, by rfl⟩ : syracuseStep 2339965 = 877487) (by norm_num)
theorem B7017605 : Blo 1459549 7017605 := bbase (se 4 (by rfl) ⟨657900, by rfl⟩ : syracuseStep 7017605 = 1315801) (by norm_num)
theorem B1643665 : Blo 1459549 1643665 := bbase (se 2 (by rfl) ⟨616374, by rfl⟩ : syracuseStep 1643665 = 1232749) (by norm_num)
theorem B5919925 : Blo 1459549 5919925 := bbase (se 5 (by rfl) ⟨277496, by rfl⟩ : syracuseStep 5919925 = 554993) (by norm_num)
theorem B4158661 : Blo 1459549 4158661 := bbase (se 4 (by rfl) ⟨389874, by rfl⟩ : syracuseStep 4158661 = 779749) (by norm_num)
theorem B1848521 : Blo 1459549 1848521 := bbase (se 2 (by rfl) ⟨693195, by rfl⟩ : syracuseStep 1848521 = 1386391) (by norm_num)
theorem B4928741 : Blo 1459549 4928741 := bbase (se 4 (by rfl) ⟨462069, by rfl⟩ : syracuseStep 4928741 = 924139) (by norm_num)
theorem B1848577 : Blo 1459549 1848577 := bbase (se 2 (by rfl) ⟨693216, by rfl⟩ : syracuseStep 1848577 = 1386433) (by norm_num)
theorem B1479961 : Blo 1459549 1479961 := bbase (se 2 (by rfl) ⟨554985, by rfl⟩ : syracuseStep 1479961 = 1109971) (by norm_num)
theorem B2463061 : Blo 1459549 2463061 := bbase (se 14 (by rfl) ⟨225, by rfl⟩ : syracuseStep 2463061 = 451) (by norm_num)
theorem B1848673 : Blo 1459549 1848673 := bbase (se 2 (by rfl) ⟨693252, by rfl⟩ : syracuseStep 1848673 = 1386505) (by norm_num)
theorem B2463149 : Blo 1459549 2463149 := bbase (se 3 (by rfl) ⟨461840, by rfl⟩ : syracuseStep 2463149 = 923681) (by norm_num)
theorem B6239717 : Blo 1459549 6239717 := bbase (se 4 (by rfl) ⟨584973, by rfl⟩ : syracuseStep 6239717 = 1169947) (by norm_num)
theorem B1873405 : Blo 1459549 1873405 := bbase (se 3 (by rfl) ⟨351263, by rfl⟩ : syracuseStep 1873405 = 702527) (by norm_num)
theorem B1848845 : Blo 1459549 1848845 := bbase (se 3 (by rfl) ⟨346658, by rfl⟩ : syracuseStep 1848845 = 693317) (by norm_num)
theorem B2078237 : Blo 1459549 2078237 := bbase (se 3 (by rfl) ⟨389669, by rfl⟩ : syracuseStep 2078237 = 779339) (by norm_num)
theorem B2463277 : Blo 1459549 2463277 := bbase (se 3 (by rfl) ⟨461864, by rfl⟩ : syracuseStep 2463277 = 923729) (by norm_num)
theorem B1848901 : Blo 1459549 1848901 := bbase (se 4 (by rfl) ⟨173334, by rfl⟩ : syracuseStep 1848901 = 346669) (by norm_num)
theorem B2250317 : Blo 1459549 2250317 := bbase (se 3 (by rfl) ⟨421934, by rfl⟩ : syracuseStep 2250317 = 843869) (by norm_num)
theorem B2463365 : Blo 1459549 2463365 := bbase (se 4 (by rfl) ⟨230940, by rfl⟩ : syracuseStep 2463365 = 461881) (by norm_num)
theorem B14227093 : Blo 1459549 14227093 := bbase (se 6 (by rfl) ⟨333447, by rfl⟩ : syracuseStep 14227093 = 666895) (by norm_num)
theorem B4929173 : Blo 1459549 4929173 := bbase (se 6 (by rfl) ⟨115527, by rfl⟩ : syracuseStep 4929173 = 231055) (by norm_num)
theorem B1848997 : Blo 1459549 1848997 := bbase (se 4 (by rfl) ⟨173343, by rfl⟩ : syracuseStep 1848997 = 346687) (by norm_num)
theorem B3118765 : Blo 1459549 3118765 := bbase (se 3 (by rfl) ⟨584768, by rfl⟩ : syracuseStep 3118765 = 1169537) (by norm_num)
theorem B12474101 : Blo 1459549 12474101 := bbase (se 5 (by rfl) ⟨584723, by rfl⟩ : syracuseStep 12474101 = 1169447) (by norm_num)
theorem B2463493 : Blo 1459549 2463493 := bbase (se 4 (by rfl) ⟨230952, by rfl⟩ : syracuseStep 2463493 = 461905) (by norm_num)
theorem B2463581 : Blo 1459549 2463581 := bbase (se 3 (by rfl) ⟨461921, by rfl⟩ : syracuseStep 2463581 = 923843) (by norm_num)
theorem B1480565 : Blo 1459549 1480565 := bbase (se 5 (by rfl) ⟨69401, by rfl⟩ : syracuseStep 1480565 = 138803) (by norm_num)
theorem B7493573 : Blo 1459549 7493573 := bbase (se 4 (by rfl) ⟨702522, by rfl⟩ : syracuseStep 7493573 = 1405045) (by norm_num)
theorem B2463709 : Blo 1459549 2463709 := bbase (se 3 (by rfl) ⟨461945, by rfl⟩ : syracuseStep 2463709 = 923891) (by norm_num)
theorem B5543909 : Blo 1459549 5543909 := bbase (se 4 (by rfl) ⟨519741, by rfl⟩ : syracuseStep 5543909 = 1039483) (by norm_num)
theorem B3119141 : Blo 1459549 3119141 := bbase (se 4 (by rfl) ⟨292419, by rfl⟩ : syracuseStep 3119141 = 584839) (by norm_num)
theorem B2463797 : Blo 1459549 2463797 := bbase (se 5 (by rfl) ⟨115490, by rfl⟩ : syracuseStep 2463797 = 230981) (by norm_num)
theorem B2078789 : Blo 1459549 2078789 := bbase (se 4 (by rfl) ⟨194886, by rfl⟩ : syracuseStep 2078789 = 389773) (by norm_num)
theorem B4929605 : Blo 1459549 4929605 := bbase (se 4 (by rfl) ⟨462150, by rfl⟩ : syracuseStep 4929605 = 924301) (by norm_num)
theorem B5617781 : Blo 1459549 5617781 := bbase (se 5 (by rfl) ⟨263333, by rfl⟩ : syracuseStep 5617781 = 526667) (by norm_num)
theorem B7395461 : Blo 1459549 7395461 := bbase (se 4 (by rfl) ⟨693324, by rfl⟩ : syracuseStep 7395461 = 1386649) (by norm_num)
theorem B2463925 : Blo 1459549 2463925 := bbase (se 5 (by rfl) ⟨115496, by rfl⟩ : syracuseStep 2463925 = 230993) (by norm_num)
theorem B1480901 : Blo 1459549 1480901 := bbase (se 4 (by rfl) ⟨138834, by rfl⟩ : syracuseStep 1480901 = 277669) (by norm_num)
theorem B5544197 : Blo 1459549 5544197 := bbase (se 4 (by rfl) ⟨519768, by rfl⟩ : syracuseStep 5544197 = 1039537) (by norm_num)
theorem B2464013 : Blo 1459549 2464013 := bbase (se 3 (by rfl) ⟨462002, by rfl⟩ : syracuseStep 2464013 = 924005) (by norm_num)
theorem B6658325 : Blo 1459549 6658325 := bbase (se 6 (by rfl) ⟨156054, by rfl⟩ : syracuseStep 6658325 = 312109) (by norm_num)
theorem B4159765 : Blo 1459549 4159765 := bbase (se 6 (by rfl) ⟨97494, by rfl⟩ : syracuseStep 4159765 = 194989) (by norm_num)
theorem B2464141 : Blo 1459549 2464141 := bbase (se 3 (by rfl) ⟨462026, by rfl⟩ : syracuseStep 2464141 = 924053) (by norm_num)
theorem B2464229 : Blo 1459549 2464229 := bbase (se 4 (by rfl) ⟨231021, by rfl⟩ : syracuseStep 2464229 = 462043) (by norm_num)
theorem B4930037 : Blo 1459549 4930037 := bbase (se 5 (by rfl) ⟨231095, by rfl⟩ : syracuseStep 4930037 = 462191) (by norm_num)
theorem B2464357 : Blo 1459549 2464357 := bbase (se 4 (by rfl) ⟨231033, by rfl⟩ : syracuseStep 2464357 = 462067) (by norm_num)
theorem B1899173 : Blo 1459549 1899173 := bbase (se 4 (by rfl) ⟨178047, by rfl⟩ : syracuseStep 1899173 = 356095) (by norm_num)
theorem B2464445 : Blo 1459549 2464445 := bbase (se 3 (by rfl) ⟨462083, by rfl⟩ : syracuseStep 2464445 = 924167) (by norm_num)
theorem B2079541 : Blo 1459549 2079541 := bbase (se 5 (by rfl) ⟨97478, by rfl⟩ : syracuseStep 2079541 = 194957) (by norm_num)
theorem B1973053 : Blo 1459549 1973053 := bbase (se 3 (by rfl) ⟨369947, by rfl⟩ : syracuseStep 1973053 = 739895) (by norm_num)
theorem B2464573 : Blo 1459549 2464573 := bbase (se 3 (by rfl) ⟨462107, by rfl⟩ : syracuseStep 2464573 = 924215) (by norm_num)
theorem B2464661 : Blo 1459549 2464661 := bbase (se 6 (by rfl) ⟨57765, by rfl⟩ : syracuseStep 2464661 = 115531) (by norm_num)
theorem B4930469 : Blo 1459549 4930469 := bbase (se 4 (by rfl) ⟨462231, by rfl⟩ : syracuseStep 4930469 = 924463) (by norm_num)
theorem B2464789 : Blo 1459549 2464789 := bbase (se 6 (by rfl) ⟨57768, by rfl⟩ : syracuseStep 2464789 = 115537) (by norm_num)
theorem B3284045 : Blo 1459549 3284045 := bbase (se 3 (by rfl) ⟨615758, by rfl⟩ : syracuseStep 3284045 = 1231517) (by norm_num)
theorem B2464877 : Blo 1459549 2464877 := bbase (se 3 (by rfl) ⟨462164, by rfl⟩ : syracuseStep 2464877 = 924329) (by norm_num)
theorem B3284117 : Blo 1459549 3284117 := bbase (se 6 (by rfl) ⟨76971, by rfl⟩ : syracuseStep 3284117 = 153943) (by norm_num)
theorem B3284189 : Blo 1459549 3284189 := bbase (se 3 (by rfl) ⟨615785, by rfl⟩ : syracuseStep 3284189 = 1231571) (by norm_num)
theorem B2465005 : Blo 1459549 2465005 := bbase (se 3 (by rfl) ⟨462188, by rfl⟩ : syracuseStep 2465005 = 924377) (by norm_num)
theorem B3284261 : Blo 1459549 3284261 := bbase (se 4 (by rfl) ⟨307899, by rfl⟩ : syracuseStep 3284261 = 615799) (by norm_num)
theorem B2465093 : Blo 1459549 2465093 := bbase (se 4 (by rfl) ⟨231102, by rfl⟩ : syracuseStep 2465093 = 462205) (by norm_num)
theorem B4930901 : Blo 1459549 4930901 := bbase (se 11 (by rfl) ⟨3611, by rfl⟩ : syracuseStep 4930901 = 7223) (by norm_num)
theorem B3284333 : Blo 1459549 3284333 := bbase (se 3 (by rfl) ⟨615812, by rfl⟩ : syracuseStep 3284333 = 1231625) (by norm_num)
theorem B5545381 : Blo 1459549 5545381 := bbase (se 4 (by rfl) ⟨519879, by rfl⟩ : syracuseStep 5545381 = 1039759) (by norm_num)
theorem B3284405 : Blo 1459549 3284405 := bbase (se 5 (by rfl) ⟨153956, by rfl⟩ : syracuseStep 3284405 = 307913) (by norm_num)
theorem B2465221 : Blo 1459549 2465221 := bbase (se 4 (by rfl) ⟨231114, by rfl⟩ : syracuseStep 2465221 = 462229) (by norm_num)
theorem B3284477 : Blo 1459549 3284477 := bbase (se 3 (by rfl) ⟨615839, by rfl⟩ : syracuseStep 3284477 = 1231679) (by norm_num)
theorem B2465309 : Blo 1459549 2465309 := bbase (se 3 (by rfl) ⟨462245, by rfl⟩ : syracuseStep 2465309 = 924491) (by norm_num)
theorem B3284549 : Blo 1459549 3284549 := bbase (se 4 (by rfl) ⟨307926, by rfl⟩ : syracuseStep 3284549 = 615853) (by norm_num)
theorem B3284621 : Blo 1459549 3284621 := bbase (se 3 (by rfl) ⟨615866, by rfl⟩ : syracuseStep 3284621 = 1231733) (by norm_num)
theorem B2465437 : Blo 1459549 2465437 := bbase (se 3 (by rfl) ⟨462269, by rfl⟩ : syracuseStep 2465437 = 924539) (by norm_num)
theorem B3284693 : Blo 1459549 3284693 := bbase (se 7 (by rfl) ⟨38492, by rfl⟩ : syracuseStep 3284693 = 76985) (by norm_num)
theorem B5545685 : Blo 1459549 5545685 := bbase (se 7 (by rfl) ⟨64988, by rfl⟩ : syracuseStep 5545685 = 129977) (by norm_num)
theorem B5922533 : Blo 1459549 5922533 := bbase (se 4 (by rfl) ⟨555237, by rfl⟩ : syracuseStep 5922533 = 1110475) (by norm_num)
theorem B3284765 : Blo 1459549 3284765 := bbase (se 3 (by rfl) ⟨615893, by rfl⟩ : syracuseStep 3284765 = 1231787) (by norm_num)
theorem B7388981 : Blo 1459549 7388981 := bbase (se 5 (by rfl) ⟨346358, by rfl⟩ : syracuseStep 7388981 = 692717) (by norm_num)
theorem B7020373 : Blo 1459549 7020373 := bbase (se 9 (by rfl) ⟨20567, by rfl⟩ : syracuseStep 7020373 = 41135) (by norm_num)
theorem B3284837 : Blo 1459549 3284837 := bbase (se 4 (by rfl) ⟨307953, by rfl⟩ : syracuseStep 3284837 = 615907) (by norm_num)
theorem B3284909 : Blo 1459549 3284909 := bbase (se 3 (by rfl) ⟨615920, by rfl⟩ : syracuseStep 3284909 = 1231841) (by norm_num)
theorem B4440005 : Blo 1459549 4440005 := bbase (se 4 (by rfl) ⟨416250, by rfl⟩ : syracuseStep 4440005 = 832501) (by norm_num)
theorem B2219989 : Blo 1459549 2219989 := bbase (se 7 (by rfl) ⟨26015, by rfl⟩ : syracuseStep 2219989 = 52031) (by norm_num)
theorem B3284981 : Blo 1459549 3284981 := bbase (se 5 (by rfl) ⟨153983, by rfl⟩ : syracuseStep 3284981 = 307967) (by norm_num)
theorem B3694673 : Blo 1459549 3694673 := bstep (se 2 (by rfl) ⟨1385502, by rfl⟩ : syracuseStep 3694673 = 2771005) B2771005
theorem B4677713 : Blo 1459549 4677713 := bstep (se 2 (by rfl) ⟨1754142, by rfl⟩ : syracuseStep 4677713 = 3508285) B3508285
theorem B1925251 : Blo 1459549 1925251 := bstep (se 1 (by rfl) ⟨1443938, by rfl⟩ : syracuseStep 1925251 = 2887877) B2887877
theorem B3285233 : Blo 1459549 3285233 := bstep (se 2 (by rfl) ⟨1231962, by rfl⟩ : syracuseStep 3285233 = 2463925) B2463925
theorem B3285251 : Blo 1459549 3285251 := bstep (se 1 (by rfl) ⟨2463938, by rfl⟩ : syracuseStep 3285251 = 4927877) B4927877
theorem B5546339 : Blo 1459549 5546339 := bstep (se 1 (by rfl) ⟨4159754, by rfl⟩ : syracuseStep 5546339 = 8319509) B8319509
theorem B5546353 : Blo 1459549 5546353 := bstep (se 2 (by rfl) ⟨2079882, by rfl⟩ : syracuseStep 5546353 = 4159765) B4159765
theorem B5923313 : Blo 1459549 5923313 := bstep (se 2 (by rfl) ⟨2221242, by rfl⟩ : syracuseStep 5923313 = 4442485) B4442485
theorem B3949069 : Blo 1459549 3949069 := bstep (se 3 (by rfl) ⟨740450, by rfl⟩ : syracuseStep 3949069 = 1480901) B1480901
theorem B3285521 : Blo 1459549 3285521 := bstep (se 2 (by rfl) ⟨1232070, by rfl⟩ : syracuseStep 3285521 = 2464141) B2464141
theorem B3285539 : Blo 1459549 3285539 := bstep (se 1 (by rfl) ⟨2464154, by rfl⟩ : syracuseStep 3285539 = 4928309) B4928309
theorem B3949091 : Blo 1459549 3949091 := bstep (se 1 (by rfl) ⟨2961818, by rfl⟩ : syracuseStep 3949091 = 5923637) B5923637
theorem B6587057 : Blo 1459549 6587057 := bstep (se 2 (by rfl) ⟨2470146, by rfl⟩ : syracuseStep 6587057 = 4940293) B4940293
theorem B4440781 : Blo 1459549 4440781 := bstep (se 3 (by rfl) ⟨832646, by rfl⟩ : syracuseStep 4440781 = 1665293) B1665293
theorem B12468977 : Blo 1459549 12468977 := bstep (se 2 (by rfl) ⟨4675866, by rfl⟩ : syracuseStep 12468977 = 9351733) B9351733
theorem B4678403 : Blo 1459549 4678403 := bstep (se 1 (by rfl) ⟨3508802, by rfl⟩ : syracuseStep 4678403 = 7017605) B7017605
theorem B3285809 : Blo 1459549 3285809 := bstep (se 2 (by rfl) ⟨1232178, by rfl⟩ : syracuseStep 3285809 = 2464357) B2464357
theorem B3285827 : Blo 1459549 3285827 := bstep (se 1 (by rfl) ⟨2464370, by rfl⟩ : syracuseStep 3285827 = 4928741) B4928741
theorem B7390115 : Blo 1459549 7390115 := bstep (se 1 (by rfl) ⟨5542586, by rfl⟩ : syracuseStep 7390115 = 11085173) B11085173
theorem B1803235 : Blo 1459549 1803235 := bstep (se 1 (by rfl) ⟨1352426, by rfl⟩ : syracuseStep 1803235 = 2704853) B2704853
theorem B3695665 : Blo 1459549 3695665 := bstep (se 2 (by rfl) ⟨1385874, by rfl⟩ : syracuseStep 3695665 = 2771749) B2771749
theorem B1500211 : Blo 1459549 1500211 := bstep (se 1 (by rfl) ⟨1125158, by rfl⟩ : syracuseStep 1500211 = 2250317) B2250317
theorem B2630737 : Blo 1459549 2630737 := bstep (se 2 (by rfl) ⟨986526, by rfl⟩ : syracuseStep 2630737 = 1973053) B1973053
theorem B3286097 : Blo 1459549 3286097 := bstep (se 2 (by rfl) ⟨1232286, by rfl⟩ : syracuseStep 3286097 = 2464573) B2464573
theorem B3286115 : Blo 1459549 3286115 := bstep (se 1 (by rfl) ⟨2464586, by rfl⟩ : syracuseStep 3286115 = 4929173) B4929173
theorem B8316067 : Blo 1459549 8316067 := bstep (se 1 (by rfl) ⟨6237050, by rfl⟩ : syracuseStep 8316067 = 12474101) B12474101
theorem B12641521 : Blo 1459549 12641521 := bstep (se 2 (by rfl) ⟨4740570, by rfl⟩ : syracuseStep 12641521 = 9481141) B9481141
theorem B9356579 : Blo 1459549 9356579 := bstep (se 1 (by rfl) ⟨7017434, by rfl⟩ : syracuseStep 9356579 = 14034869) B14034869
theorem B3851569 : Blo 1459549 3851569 := bstep (se 2 (by rfl) ⟨1444338, by rfl⟩ : syracuseStep 3851569 = 2888677) B2888677
theorem B3695939 : Blo 1459549 3695939 := bstep (se 1 (by rfl) ⟨2771954, by rfl⟩ : syracuseStep 3695939 = 5543909) B5543909
theorem B1459555 : Blo 1459549 1459555 := bstep (se 1 (by rfl) ⟨1094666, by rfl⟩ : syracuseStep 1459555 = 2189333) B2189333
theorem B3286385 : Blo 1459549 3286385 := bstep (se 2 (by rfl) ⟨1232394, by rfl⟩ : syracuseStep 3286385 = 2464789) B2464789
theorem B24962417 : Blo 1459549 24962417 := bstep (se 2 (by rfl) ⟨9360906, by rfl⟩ : syracuseStep 24962417 = 18721813) B18721813
theorem B1459571 : Blo 1459549 1459571 := bstep (se 1 (by rfl) ⟨1094678, by rfl⟩ : syracuseStep 1459571 = 2189357) B2189357
theorem B1459587 : Blo 1459549 1459587 := bstep (se 1 (by rfl) ⟨1094690, by rfl⟩ : syracuseStep 1459587 = 2189381) B2189381
theorem B3286403 : Blo 1459549 3286403 := bstep (se 1 (by rfl) ⟨2464802, by rfl⟩ : syracuseStep 3286403 = 4929605) B4929605
theorem B1459603 : Blo 1459549 1459603 := bstep (se 1 (by rfl) ⟨1094702, by rfl⟩ : syracuseStep 1459603 = 2189405) B2189405
theorem B1459619 : Blo 1459549 1459619 := bstep (se 1 (by rfl) ⟨1094714, by rfl⟩ : syracuseStep 1459619 = 2189429) B2189429
theorem B3745187 : Blo 1459549 3745187 := bstep (se 1 (by rfl) ⟨2808890, by rfl⟩ : syracuseStep 3745187 = 5617781) B5617781
theorem B1459635 : Blo 1459549 1459635 := bstep (se 1 (by rfl) ⟨1094726, by rfl⟩ : syracuseStep 1459635 = 2189453) B2189453
theorem B1459651 : Blo 1459549 1459651 := bstep (se 1 (by rfl) ⟨1094738, by rfl⟩ : syracuseStep 1459651 = 2189477) B2189477
theorem B1459667 : Blo 1459549 1459667 := bstep (se 1 (by rfl) ⟨1094750, by rfl⟩ : syracuseStep 1459667 = 2189501) B2189501
theorem B1459683 : Blo 1459549 1459683 := bstep (se 1 (by rfl) ⟨1094762, by rfl⟩ : syracuseStep 1459683 = 2189525) B2189525
theorem B1459699 : Blo 1459549 1459699 := bstep (se 1 (by rfl) ⟨1094774, by rfl⟩ : syracuseStep 1459699 = 2189549) B2189549
theorem B1459715 : Blo 1459549 1459715 := bstep (se 1 (by rfl) ⟨1094786, by rfl⟩ : syracuseStep 1459715 = 2189573) B2189573
theorem B3696131 : Blo 1459549 3696131 := bstep (se 1 (by rfl) ⟨2772098, by rfl⟩ : syracuseStep 3696131 = 5544197) B5544197
theorem B1459731 : Blo 1459549 1459731 := bstep (se 1 (by rfl) ⟨1094798, by rfl⟩ : syracuseStep 1459731 = 2189597) B2189597
theorem B1459747 : Blo 1459549 1459747 := bstep (se 1 (by rfl) ⟨1094810, by rfl⟩ : syracuseStep 1459747 = 2189621) B2189621
theorem B1459763 : Blo 1459549 1459763 := bstep (se 1 (by rfl) ⟨1094822, by rfl⟩ : syracuseStep 1459763 = 2189645) B2189645
theorem B1459779 : Blo 1459549 1459779 := bstep (se 1 (by rfl) ⟨1094834, by rfl⟩ : syracuseStep 1459779 = 2189669) B2189669
theorem B1459795 : Blo 1459549 1459795 := bstep (se 1 (by rfl) ⟨1094846, by rfl⟩ : syracuseStep 1459795 = 2189693) B2189693
theorem B1459811 : Blo 1459549 1459811 := bstep (se 1 (by rfl) ⟨1094858, by rfl⟩ : syracuseStep 1459811 = 2189717) B2189717
theorem B1459827 : Blo 1459549 1459827 := bstep (se 1 (by rfl) ⟨1094870, by rfl⟩ : syracuseStep 1459827 = 2189741) B2189741
theorem B1459843 : Blo 1459549 1459843 := bstep (se 1 (by rfl) ⟨1094882, by rfl⟩ : syracuseStep 1459843 = 2189765) B2189765
theorem B3286673 : Blo 1459549 3286673 := bstep (se 2 (by rfl) ⟨1232502, by rfl⟩ : syracuseStep 3286673 = 2465005) B2465005
theorem B1459859 : Blo 1459549 1459859 := bstep (se 1 (by rfl) ⟨1094894, by rfl⟩ : syracuseStep 1459859 = 2189789) B2189789
theorem B1459875 : Blo 1459549 1459875 := bstep (se 1 (by rfl) ⟨1094906, by rfl⟩ : syracuseStep 1459875 = 2189813) B2189813
theorem B3286691 : Blo 1459549 3286691 := bstep (se 1 (by rfl) ⟨2465018, by rfl⟩ : syracuseStep 3286691 = 4930037) B4930037
theorem B8316593 : Blo 1459549 8316593 := bstep (se 2 (by rfl) ⟨3118722, by rfl⟩ : syracuseStep 8316593 = 6237445) B6237445
theorem B1459891 : Blo 1459549 1459891 := bstep (se 1 (by rfl) ⟨1094918, by rfl⟩ : syracuseStep 1459891 = 2189837) B2189837
theorem B1459907 : Blo 1459549 1459907 := bstep (se 1 (by rfl) ⟨1094930, by rfl⟩ : syracuseStep 1459907 = 2189861) B2189861
theorem B7390925 : Blo 1459549 7390925 := bstep (se 3 (by rfl) ⟨1385798, by rfl⟩ : syracuseStep 7390925 = 2771597) B2771597
theorem B1459923 : Blo 1459549 1459923 := bstep (se 1 (by rfl) ⟨1094942, by rfl⟩ : syracuseStep 1459923 = 2189885) B2189885
theorem B1459939 : Blo 1459549 1459939 := bstep (se 1 (by rfl) ⟨1094954, by rfl⟩ : syracuseStep 1459939 = 2189909) B2189909
theorem B1459955 : Blo 1459549 1459955 := bstep (se 1 (by rfl) ⟨1094966, by rfl⟩ : syracuseStep 1459955 = 2189933) B2189933
theorem B1459971 : Blo 1459549 1459971 := bstep (se 1 (by rfl) ⟨1094978, by rfl⟩ : syracuseStep 1459971 = 2189957) B2189957
theorem B5064461 : Blo 1459549 5064461 := bstep (se 3 (by rfl) ⟨949586, by rfl⟩ : syracuseStep 5064461 = 1899173) B1899173
theorem B1459987 : Blo 1459549 1459987 := bstep (se 1 (by rfl) ⟨1094990, by rfl⟩ : syracuseStep 1459987 = 2189981) B2189981
theorem B1460003 : Blo 1459549 1460003 := bstep (se 1 (by rfl) ⟨1095002, by rfl⟩ : syracuseStep 1460003 = 2190005) B2190005
theorem B1460019 : Blo 1459549 1460019 := bstep (se 1 (by rfl) ⟨1095014, by rfl⟩ : syracuseStep 1460019 = 2190029) B2190029
theorem B1460035 : Blo 1459549 1460035 := bstep (se 1 (by rfl) ⟨1095026, by rfl⟩ : syracuseStep 1460035 = 2190053) B2190053
theorem B1460051 : Blo 1459549 1460051 := bstep (se 1 (by rfl) ⟨1095038, by rfl⟩ : syracuseStep 1460051 = 2190077) B2190077
theorem B1460067 : Blo 1459549 1460067 := bstep (se 1 (by rfl) ⟨1095050, by rfl⟩ : syracuseStep 1460067 = 2190101) B2190101
theorem B1460083 : Blo 1459549 1460083 := bstep (se 1 (by rfl) ⟨1095062, by rfl⟩ : syracuseStep 1460083 = 2190125) B2190125
theorem B1460099 : Blo 1459549 1460099 := bstep (se 1 (by rfl) ⟨1095074, by rfl⟩ : syracuseStep 1460099 = 2190149) B2190149
theorem B1460115 : Blo 1459549 1460115 := bstep (se 1 (by rfl) ⟨1095086, by rfl⟩ : syracuseStep 1460115 = 2190173) B2190173
theorem B1460131 : Blo 1459549 1460131 := bstep (se 1 (by rfl) ⟨1095098, by rfl⟩ : syracuseStep 1460131 = 2190197) B2190197
theorem B3286961 : Blo 1459549 3286961 := bstep (se 2 (by rfl) ⟨1232610, by rfl⟩ : syracuseStep 3286961 = 2465221) B2465221
theorem B1460147 : Blo 1459549 1460147 := bstep (se 1 (by rfl) ⟨1095110, by rfl⟩ : syracuseStep 1460147 = 2190221) B2190221
theorem B1460163 : Blo 1459549 1460163 := bstep (se 1 (by rfl) ⟨1095122, by rfl⟩ : syracuseStep 1460163 = 2190245) B2190245
theorem B3286979 : Blo 1459549 3286979 := bstep (se 1 (by rfl) ⟨2465234, by rfl⟩ : syracuseStep 3286979 = 4930469) B4930469
theorem B1460179 : Blo 1459549 1460179 := bstep (se 1 (by rfl) ⟨1095134, by rfl⟩ : syracuseStep 1460179 = 2190269) B2190269
theorem B1460195 : Blo 1459549 1460195 := bstep (se 1 (by rfl) ⟨1095146, by rfl⟩ : syracuseStep 1460195 = 2190293) B2190293
theorem B1460211 : Blo 1459549 1460211 := bstep (se 1 (by rfl) ⟨1095158, by rfl⟩ : syracuseStep 1460211 = 2190317) B2190317
theorem B1460227 : Blo 1459549 1460227 := bstep (se 1 (by rfl) ⟨1095170, by rfl⟩ : syracuseStep 1460227 = 2190341) B2190341
theorem B7112717 : Blo 1459549 7112717 := bstep (se 3 (by rfl) ⟨1333634, by rfl⟩ : syracuseStep 7112717 = 2667269) B2667269
theorem B1460243 : Blo 1459549 1460243 := bstep (se 1 (by rfl) ⟨1095182, by rfl⟩ : syracuseStep 1460243 = 2190365) B2190365
theorem B2189345 : Blo 1459549 2189345 := bstep (se 2 (by rfl) ⟨821004, by rfl⟩ : syracuseStep 2189345 = 1642009) B1642009
theorem B1460259 : Blo 1459549 1460259 := bstep (se 1 (by rfl) ⟨1095194, by rfl⟩ : syracuseStep 1460259 = 2190389) B2190389
theorem B2189363 : Blo 1459549 2189363 := bstep (se 1 (by rfl) ⟨1642022, by rfl⟩ : syracuseStep 2189363 = 3284045) B3284045
theorem B1460275 : Blo 1459549 1460275 := bstep (se 1 (by rfl) ⟨1095206, by rfl⟩ : syracuseStep 1460275 = 2190413) B2190413
theorem B1460291 : Blo 1459549 1460291 := bstep (se 1 (by rfl) ⟨1095218, by rfl⟩ : syracuseStep 1460291 = 2190437) B2190437
theorem B2189393 : Blo 1459549 2189393 := bstep (se 2 (by rfl) ⟨821022, by rfl⟩ : syracuseStep 2189393 = 1642045) B1642045
theorem B1460307 : Blo 1459549 1460307 := bstep (se 1 (by rfl) ⟨1095230, by rfl⟩ : syracuseStep 1460307 = 2190461) B2190461
theorem B2189411 : Blo 1459549 2189411 := bstep (se 1 (by rfl) ⟨1642058, by rfl⟩ : syracuseStep 2189411 = 3284117) B3284117
theorem B1460323 : Blo 1459549 1460323 := bstep (se 1 (by rfl) ⟨1095242, by rfl⟩ : syracuseStep 1460323 = 2190485) B2190485
theorem B1460339 : Blo 1459549 1460339 := bstep (se 1 (by rfl) ⟨1095254, by rfl⟩ : syracuseStep 1460339 = 2190509) B2190509
theorem B2189441 : Blo 1459549 2189441 := bstep (se 2 (by rfl) ⟨821040, by rfl⟩ : syracuseStep 2189441 = 1642081) B1642081
theorem B1460355 : Blo 1459549 1460355 := bstep (se 1 (by rfl) ⟨1095266, by rfl⟩ : syracuseStep 1460355 = 2190533) B2190533
theorem B2189459 : Blo 1459549 2189459 := bstep (se 1 (by rfl) ⟨1642094, by rfl⟩ : syracuseStep 2189459 = 3284189) B3284189
theorem B1460371 : Blo 1459549 1460371 := bstep (se 1 (by rfl) ⟨1095278, by rfl⟩ : syracuseStep 1460371 = 2190557) B2190557
theorem B1460387 : Blo 1459549 1460387 := bstep (se 1 (by rfl) ⟨1095290, by rfl⟩ : syracuseStep 1460387 = 2190581) B2190581
theorem B2189489 : Blo 1459549 2189489 := bstep (se 2 (by rfl) ⟨821058, by rfl⟩ : syracuseStep 2189489 = 1642117) B1642117
theorem B1460403 : Blo 1459549 1460403 := bstep (se 1 (by rfl) ⟨1095302, by rfl⟩ : syracuseStep 1460403 = 2190605) B2190605
theorem B2189507 : Blo 1459549 2189507 := bstep (se 1 (by rfl) ⟨1642130, by rfl⟩ : syracuseStep 2189507 = 3284261) B3284261
theorem B1460419 : Blo 1459549 1460419 := bstep (se 1 (by rfl) ⟨1095314, by rfl⟩ : syracuseStep 1460419 = 2190629) B2190629
theorem B3287249 : Blo 1459549 3287249 := bstep (se 2 (by rfl) ⟨1232718, by rfl⟩ : syracuseStep 3287249 = 2465437) B2465437
theorem B1460435 : Blo 1459549 1460435 := bstep (se 1 (by rfl) ⟨1095326, by rfl⟩ : syracuseStep 1460435 = 2190653) B2190653
theorem B2189537 : Blo 1459549 2189537 := bstep (se 2 (by rfl) ⟨821076, by rfl⟩ : syracuseStep 2189537 = 1642153) B1642153
theorem B1460451 : Blo 1459549 1460451 := bstep (se 1 (by rfl) ⟨1095338, by rfl⟩ : syracuseStep 1460451 = 2190677) B2190677
theorem B4442339 : Blo 1459549 4442339 := bstep (se 1 (by rfl) ⟨3331754, by rfl⟩ : syracuseStep 4442339 = 6663509) B6663509
theorem B3287267 : Blo 1459549 3287267 := bstep (se 1 (by rfl) ⟨2465450, by rfl⟩ : syracuseStep 3287267 = 4930901) B4930901
theorem B2189555 : Blo 1459549 2189555 := bstep (se 1 (by rfl) ⟨1642166, by rfl⟩ : syracuseStep 2189555 = 3284333) B3284333
theorem B1460467 : Blo 1459549 1460467 := bstep (se 1 (by rfl) ⟨1095350, by rfl⟩ : syracuseStep 1460467 = 2190701) B2190701
theorem B1460483 : Blo 1459549 1460483 := bstep (se 1 (by rfl) ⟨1095362, by rfl⟩ : syracuseStep 1460483 = 2190725) B2190725
theorem B2885905 : Blo 1459549 2885905 := bstep (se 2 (by rfl) ⟨1082214, by rfl⟩ : syracuseStep 2885905 = 2164429) B2164429
theorem B2189585 : Blo 1459549 2189585 := bstep (se 2 (by rfl) ⟨821094, by rfl⟩ : syracuseStep 2189585 = 1642189) B1642189
theorem B1460499 : Blo 1459549 1460499 := bstep (se 1 (by rfl) ⟨1095374, by rfl⟩ : syracuseStep 1460499 = 2190749) B2190749
theorem B2189603 : Blo 1459549 2189603 := bstep (se 1 (by rfl) ⟨1642202, by rfl⟩ : syracuseStep 2189603 = 3284405) B3284405
theorem B1460515 : Blo 1459549 1460515 := bstep (se 1 (by rfl) ⟨1095386, by rfl⟩ : syracuseStep 1460515 = 2190773) B2190773
theorem B1460531 : Blo 1459549 1460531 := bstep (se 1 (by rfl) ⟨1095398, by rfl⟩ : syracuseStep 1460531 = 2190797) B2190797
theorem B2189633 : Blo 1459549 2189633 := bstep (se 2 (by rfl) ⟨821112, by rfl⟩ : syracuseStep 2189633 = 1642225) B1642225
theorem B1460547 : Blo 1459549 1460547 := bstep (se 1 (by rfl) ⟨1095410, by rfl⟩ : syracuseStep 1460547 = 2190821) B2190821
theorem B2189651 : Blo 1459549 2189651 := bstep (se 1 (by rfl) ⟨1642238, by rfl⟩ : syracuseStep 2189651 = 3284477) B3284477
theorem B1460563 : Blo 1459549 1460563 := bstep (se 1 (by rfl) ⟨1095422, by rfl⟩ : syracuseStep 1460563 = 2190845) B2190845
theorem B1558883 : Blo 1459549 1558883 := bstep (se 1 (by rfl) ⟨1169162, by rfl⟩ : syracuseStep 1558883 = 2338325) B2338325
theorem B1460579 : Blo 1459549 1460579 := bstep (se 1 (by rfl) ⟨1095434, by rfl⟩ : syracuseStep 1460579 = 2190869) B2190869
theorem B2189681 : Blo 1459549 2189681 := bstep (se 2 (by rfl) ⟨821130, by rfl⟩ : syracuseStep 2189681 = 1642261) B1642261
theorem B1460595 : Blo 1459549 1460595 := bstep (se 1 (by rfl) ⟨1095446, by rfl⟩ : syracuseStep 1460595 = 2190893) B2190893
theorem B2189699 : Blo 1459549 2189699 := bstep (se 1 (by rfl) ⟨1642274, by rfl⟩ : syracuseStep 2189699 = 3284549) B3284549
theorem B1460611 : Blo 1459549 1460611 := bstep (se 1 (by rfl) ⟨1095458, by rfl⟩ : syracuseStep 1460611 = 2190917) B2190917
theorem B1460627 : Blo 1459549 1460627 := bstep (se 1 (by rfl) ⟨1095470, by rfl⟩ : syracuseStep 1460627 = 2190941) B2190941
theorem B2189729 : Blo 1459549 2189729 := bstep (se 2 (by rfl) ⟨821148, by rfl⟩ : syracuseStep 2189729 = 1642297) B1642297
theorem B1460643 : Blo 1459549 1460643 := bstep (se 1 (by rfl) ⟨1095482, by rfl⟩ : syracuseStep 1460643 = 2190965) B2190965
theorem B3697073 : Blo 1459549 3697073 := bstep (se 2 (by rfl) ⟨1386402, by rfl⟩ : syracuseStep 3697073 = 2772805) B2772805
theorem B2189747 : Blo 1459549 2189747 := bstep (se 1 (by rfl) ⟨1642310, by rfl⟩ : syracuseStep 2189747 = 3284621) B3284621
theorem B1460659 : Blo 1459549 1460659 := bstep (se 1 (by rfl) ⟨1095494, by rfl⟩ : syracuseStep 1460659 = 2190989) B2190989
theorem B1460675 : Blo 1459549 1460675 := bstep (se 1 (by rfl) ⟨1095506, by rfl⟩ : syracuseStep 1460675 = 2191013) B2191013
theorem B2189777 : Blo 1459549 2189777 := bstep (se 2 (by rfl) ⟨821166, by rfl⟩ : syracuseStep 2189777 = 1642333) B1642333
theorem B1460691 : Blo 1459549 1460691 := bstep (se 1 (by rfl) ⟨1095518, by rfl⟩ : syracuseStep 1460691 = 2191037) B2191037
theorem B2189795 : Blo 1459549 2189795 := bstep (se 1 (by rfl) ⟨1642346, by rfl⟩ : syracuseStep 2189795 = 3284693) B3284693
theorem B3697123 : Blo 1459549 3697123 := bstep (se 1 (by rfl) ⟨2772842, by rfl⟩ : syracuseStep 3697123 = 5545685) B5545685
theorem B1460707 : Blo 1459549 1460707 := bstep (se 1 (by rfl) ⟨1095530, by rfl⟩ : syracuseStep 1460707 = 2191061) B2191061
theorem B4680173 : Blo 1459549 4680173 := bstep (se 3 (by rfl) ⟨877532, by rfl⟩ : syracuseStep 4680173 = 1755065) B1755065
theorem B1460723 : Blo 1459549 1460723 := bstep (se 1 (by rfl) ⟨1095542, by rfl⟩ : syracuseStep 1460723 = 2191085) B2191085
theorem B2189825 : Blo 1459549 2189825 := bstep (se 2 (by rfl) ⟨821184, by rfl⟩ : syracuseStep 2189825 = 1642369) B1642369
theorem B1460739 : Blo 1459549 1460739 := bstep (se 1 (by rfl) ⟨1095554, by rfl⟩ : syracuseStep 1460739 = 2191109) B2191109
theorem B19982861 : Blo 1459549 19982861 := bstep (se 3 (by rfl) ⟨3746786, by rfl⟩ : syracuseStep 19982861 = 7493573) B7493573
theorem B2189843 : Blo 1459549 2189843 := bstep (se 1 (by rfl) ⟨1642382, by rfl⟩ : syracuseStep 2189843 = 3284765) B3284765
theorem B1460755 : Blo 1459549 1460755 := bstep (se 1 (by rfl) ⟨1095566, by rfl⟩ : syracuseStep 1460755 = 2191133) B2191133
theorem B4925987 : Blo 1459549 4925987 := bstep (se 1 (by rfl) ⟨3694490, by rfl⟩ : syracuseStep 4925987 = 7388981) B7388981
theorem B2771491 : Blo 1459549 2771491 := bstep (se 1 (by rfl) ⟨2078618, by rfl⟩ : syracuseStep 2771491 = 4157237) B4157237
theorem B1460771 : Blo 1459549 1460771 := bstep (se 1 (by rfl) ⟨1095578, by rfl⟩ : syracuseStep 1460771 = 2191157) B2191157
theorem B2189873 : Blo 1459549 2189873 := bstep (se 2 (by rfl) ⟨821202, by rfl⟩ : syracuseStep 2189873 = 1642405) B1642405
theorem B1460787 : Blo 1459549 1460787 := bstep (se 1 (by rfl) ⟨1095590, by rfl⟩ : syracuseStep 1460787 = 2191181) B2191181
theorem B2189891 : Blo 1459549 2189891 := bstep (se 1 (by rfl) ⟨1642418, by rfl⟩ : syracuseStep 2189891 = 3284837) B3284837
theorem B1460803 : Blo 1459549 1460803 := bstep (se 1 (by rfl) ⟨1095602, by rfl⟩ : syracuseStep 1460803 = 2191205) B2191205
theorem B1460819 : Blo 1459549 1460819 := bstep (se 1 (by rfl) ⟨1095614, by rfl⟩ : syracuseStep 1460819 = 2191229) B2191229
theorem B2189921 : Blo 1459549 2189921 := bstep (se 2 (by rfl) ⟨821220, by rfl⟩ : syracuseStep 2189921 = 1642441) B1642441
theorem B1460835 : Blo 1459549 1460835 := bstep (se 1 (by rfl) ⟨1095626, by rfl⟩ : syracuseStep 1460835 = 2191253) B2191253
theorem B2959985 : Blo 1459549 2959985 := bstep (se 2 (by rfl) ⟨1109994, by rfl⟩ : syracuseStep 2959985 = 2219989) B2219989
theorem B3697265 : Blo 1459549 3697265 := bstep (se 2 (by rfl) ⟨1386474, by rfl⟩ : syracuseStep 3697265 = 2772949) B2772949
theorem B2189939 : Blo 1459549 2189939 := bstep (se 1 (by rfl) ⟨1642454, by rfl⟩ : syracuseStep 2189939 = 3284909) B3284909
theorem B1460851 : Blo 1459549 1460851 := bstep (se 1 (by rfl) ⟨1095638, by rfl⟩ : syracuseStep 1460851 = 2191277) B2191277
theorem B4680301 : Blo 1459549 4680301 := bstep (se 3 (by rfl) ⟨877556, by rfl⟩ : syracuseStep 4680301 = 1755113) B1755113
theorem B2960003 : Blo 1459549 2960003 := bstep (se 1 (by rfl) ⟨2220002, by rfl⟩ : syracuseStep 2960003 = 4440005) B4440005
theorem B1460867 : Blo 1459549 1460867 := bstep (se 1 (by rfl) ⟨1095650, by rfl⟩ : syracuseStep 1460867 = 2191301) B2191301
theorem B2189969 : Blo 1459549 2189969 := bstep (se 2 (by rfl) ⟨821238, by rfl⟩ : syracuseStep 2189969 = 1642477) B1642477
theorem B1460883 : Blo 1459549 1460883 := bstep (se 1 (by rfl) ⟨1095662, by rfl⟩ : syracuseStep 1460883 = 2191325) B2191325
theorem B2189987 : Blo 1459549 2189987 := bstep (se 1 (by rfl) ⟨1642490, by rfl⟩ : syracuseStep 2189987 = 3284981) B3284981
theorem B1460899 : Blo 1459549 1460899 := bstep (se 1 (by rfl) ⟨1095674, by rfl⟩ : syracuseStep 1460899 = 2191349) B2191349
theorem B1460915 : Blo 1459549 1460915 := bstep (se 1 (by rfl) ⟨1095686, by rfl⟩ : syracuseStep 1460915 = 2191373) B2191373
theorem B2190017 : Blo 1459549 2190017 := bstep (se 2 (by rfl) ⟨821256, by rfl⟩ : syracuseStep 2190017 = 1642513) B1642513
theorem B2771651 : Blo 1459549 2771651 := bstep (se 1 (by rfl) ⟨2078738, by rfl⟩ : syracuseStep 2771651 = 4157477) B4157477
theorem B1665731 : Blo 1459549 1665731 := bstep (se 1 (by rfl) ⟨1249298, by rfl⟩ : syracuseStep 1665731 = 2498597) B2498597
theorem B1460931 : Blo 1459549 1460931 := bstep (se 1 (by rfl) ⟨1095698, by rfl⟩ : syracuseStep 1460931 = 2191397) B2191397
theorem B2190035 : Blo 1459549 2190035 := bstep (se 1 (by rfl) ⟨1642526, by rfl⟩ : syracuseStep 2190035 = 3285053) B3285053
theorem B1460947 : Blo 1459549 1460947 := bstep (se 1 (by rfl) ⟨1095710, by rfl⟩ : syracuseStep 1460947 = 2191421) B2191421
theorem B1460963 : Blo 1459549 1460963 := bstep (se 1 (by rfl) ⟨1095722, by rfl⟩ : syracuseStep 1460963 = 2191445) B2191445
theorem B4442861 : Blo 1459549 4442861 := bstep (se 3 (by rfl) ⟨833036, by rfl⟩ : syracuseStep 4442861 = 1666073) B1666073
theorem B2190065 : Blo 1459549 2190065 := bstep (se 2 (by rfl) ⟨821274, by rfl⟩ : syracuseStep 2190065 = 1642549) B1642549
theorem B1460979 : Blo 1459549 1460979 := bstep (se 1 (by rfl) ⟨1095734, by rfl⟩ : syracuseStep 1460979 = 2191469) B2191469
theorem B2190083 : Blo 1459549 2190083 := bstep (se 1 (by rfl) ⟨1642562, by rfl⟩ : syracuseStep 2190083 = 3285125) B3285125
theorem B1460995 : Blo 1459549 1460995 := bstep (se 1 (by rfl) ⟨1095746, by rfl⟩ : syracuseStep 1460995 = 2191493) B2191493
theorem B1461011 : Blo 1459549 1461011 := bstep (se 1 (by rfl) ⟨1095758, by rfl⟩ : syracuseStep 1461011 = 2191517) B2191517
theorem B2190113 : Blo 1459549 2190113 := bstep (se 2 (by rfl) ⟨821292, by rfl⟩ : syracuseStep 2190113 = 1642585) B1642585
theorem B1461027 : Blo 1459549 1461027 := bstep (se 1 (by rfl) ⟨1095770, by rfl⟩ : syracuseStep 1461027 = 2191541) B2191541
theorem B4926257 : Blo 1459549 4926257 := bstep (se 2 (by rfl) ⟨1847346, by rfl⟩ : syracuseStep 4926257 = 3694693) B3694693
theorem B9988913 : Blo 1459549 9988913 := bstep (se 2 (by rfl) ⟨3745842, by rfl⟩ : syracuseStep 9988913 = 7491685) B7491685
theorem B2190131 : Blo 1459549 2190131 := bstep (se 1 (by rfl) ⟨1642598, by rfl⟩ : syracuseStep 2190131 = 3285197) B3285197
theorem B1461043 : Blo 1459549 1461043 := bstep (se 1 (by rfl) ⟨1095782, by rfl⟩ : syracuseStep 1461043 = 2191565) B2191565
theorem B2190161 : Blo 1459549 2190161 := bstep (se 2 (by rfl) ⟨821310, by rfl⟩ : syracuseStep 2190161 = 1642621) B1642621
theorem B2190179 : Blo 1459549 2190179 := bstep (se 1 (by rfl) ⟨1642634, by rfl⟩ : syracuseStep 2190179 = 3285269) B3285269
theorem B4680557 : Blo 1459549 4680557 := bstep (se 3 (by rfl) ⟨877604, by rfl⟩ : syracuseStep 4680557 = 1755209) B1755209
theorem B2190209 : Blo 1459549 2190209 := bstep (se 2 (by rfl) ⟨821328, by rfl⟩ : syracuseStep 2190209 = 1642657) B1642657
theorem B2190227 : Blo 1459549 2190227 := bstep (se 1 (by rfl) ⟨1642670, by rfl⟩ : syracuseStep 2190227 = 3285341) B3285341
theorem B2190257 : Blo 1459549 2190257 := bstep (se 2 (by rfl) ⟨821346, by rfl⟩ : syracuseStep 2190257 = 1642693) B1642693
theorem B2190275 : Blo 1459549 2190275 := bstep (se 1 (by rfl) ⟨1642706, by rfl⟩ : syracuseStep 2190275 = 3285413) B3285413
theorem B2190305 : Blo 1459549 2190305 := bstep (se 2 (by rfl) ⟨821364, by rfl⟩ : syracuseStep 2190305 = 1642729) B1642729
theorem B2190323 : Blo 1459549 2190323 := bstep (se 1 (by rfl) ⟨1642742, by rfl⟩ : syracuseStep 2190323 = 3285485) B3285485
theorem B2190353 : Blo 1459549 2190353 := bstep (se 2 (by rfl) ⟨821382, by rfl⟩ : syracuseStep 2190353 = 1642765) B1642765
theorem B2190371 : Blo 1459549 2190371 := bstep (se 1 (by rfl) ⟨1642778, by rfl⟩ : syracuseStep 2190371 = 3285557) B3285557
theorem B2190401 : Blo 1459549 2190401 := bstep (se 2 (by rfl) ⟨821400, by rfl⟩ : syracuseStep 2190401 = 1642801) B1642801
theorem B2190419 : Blo 1459549 2190419 := bstep (se 1 (by rfl) ⟨1642814, by rfl⟩ : syracuseStep 2190419 = 3285629) B3285629
theorem B8318051 : Blo 1459549 8318051 := bstep (se 1 (by rfl) ⟨6238538, by rfl⟩ : syracuseStep 8318051 = 12477077) B12477077
theorem B2190449 : Blo 1459549 2190449 := bstep (se 2 (by rfl) ⟨821418, by rfl⟩ : syracuseStep 2190449 = 1642837) B1642837
theorem B2190467 : Blo 1459549 2190467 := bstep (se 1 (by rfl) ⟨1642850, by rfl⟩ : syracuseStep 2190467 = 3285701) B3285701
theorem B2190497 : Blo 1459549 2190497 := bstep (se 2 (by rfl) ⟨821436, by rfl⟩ : syracuseStep 2190497 = 1642873) B1642873
theorem B2190515 : Blo 1459549 2190515 := bstep (se 1 (by rfl) ⟨1642886, by rfl⟩ : syracuseStep 2190515 = 3285773) B3285773
theorem B2370755 : Blo 1459549 2370755 := bstep (se 1 (by rfl) ⟨1778066, by rfl⟩ : syracuseStep 2370755 = 3556133) B3556133
theorem B2190545 : Blo 1459549 2190545 := bstep (se 2 (by rfl) ⟨821454, by rfl⟩ : syracuseStep 2190545 = 1642909) B1642909
theorem B2190563 : Blo 1459549 2190563 := bstep (se 1 (by rfl) ⟨1642922, by rfl⟩ : syracuseStep 2190563 = 3285845) B3285845
theorem B2190593 : Blo 1459549 2190593 := bstep (se 2 (by rfl) ⟨821472, by rfl⟩ : syracuseStep 2190593 = 1642945) B1642945
theorem B11087117 : Blo 1459549 11087117 := bstep (se 3 (by rfl) ⟨2078834, by rfl⟩ : syracuseStep 11087117 = 4157669) B4157669
theorem B2190611 : Blo 1459549 2190611 := bstep (se 1 (by rfl) ⟨1642958, by rfl⟩ : syracuseStep 2190611 = 3285917) B3285917
theorem B1559827 : Blo 1459549 1559827 := bstep (se 1 (by rfl) ⟨1169870, by rfl⟩ : syracuseStep 1559827 = 2339741) B2339741
theorem B2190641 : Blo 1459549 2190641 := bstep (se 2 (by rfl) ⟨821490, by rfl⟩ : syracuseStep 2190641 = 1642981) B1642981
theorem B2190659 : Blo 1459549 2190659 := bstep (se 1 (by rfl) ⟨1642994, by rfl⟩ : syracuseStep 2190659 = 3285989) B3285989
theorem B4926797 : Blo 1459549 4926797 := bstep (se 3 (by rfl) ⟨923774, by rfl⟩ : syracuseStep 4926797 = 1847549) B1847549
theorem B2190689 : Blo 1459549 2190689 := bstep (se 2 (by rfl) ⟨821508, by rfl⟩ : syracuseStep 2190689 = 1643017) B1643017
theorem B2190707 : Blo 1459549 2190707 := bstep (se 1 (by rfl) ⟨1643030, by rfl⟩ : syracuseStep 2190707 = 3286061) B3286061
theorem B4926851 : Blo 1459549 4926851 := bstep (se 1 (by rfl) ⟨3695138, by rfl⟩ : syracuseStep 4926851 = 7390277) B7390277
theorem B2190737 : Blo 1459549 2190737 := bstep (se 2 (by rfl) ⟨821526, by rfl⟩ : syracuseStep 2190737 = 1643053) B1643053
theorem B2190755 : Blo 1459549 2190755 := bstep (se 1 (by rfl) ⟨1643066, by rfl⟩ : syracuseStep 2190755 = 3286133) B3286133
theorem B4156849 : Blo 1459549 4156849 := bstep (se 2 (by rfl) ⟨1558818, by rfl⟩ : syracuseStep 4156849 = 3117637) B3117637
theorem B2190785 : Blo 1459549 2190785 := bstep (se 2 (by rfl) ⟨821544, by rfl⟩ : syracuseStep 2190785 = 1643089) B1643089
theorem B75877829 : Blo 1459549 75877829 := bstep (se 4 (by rfl) ⟨7113546, by rfl⟩ : syracuseStep 75877829 = 14227093) B14227093
theorem B2190803 : Blo 1459549 2190803 := bstep (se 1 (by rfl) ⟨1643102, by rfl⟩ : syracuseStep 2190803 = 3286205) B3286205
theorem B2190833 : Blo 1459549 2190833 := bstep (se 2 (by rfl) ⟨821562, by rfl⟩ : syracuseStep 2190833 = 1643125) B1643125
theorem B2190851 : Blo 1459549 2190851 := bstep (se 1 (by rfl) ⟨1643138, by rfl⟩ : syracuseStep 2190851 = 3286277) B3286277
theorem B2190881 : Blo 1459549 2190881 := bstep (se 2 (by rfl) ⟨821580, by rfl⟩ : syracuseStep 2190881 = 1643161) B1643161
theorem B2190899 : Blo 1459549 2190899 := bstep (se 1 (by rfl) ⟨1643174, by rfl⟩ : syracuseStep 2190899 = 3286349) B3286349
theorem B2190929 : Blo 1459549 2190929 := bstep (se 2 (by rfl) ⟨821598, by rfl⟩ : syracuseStep 2190929 = 1643197) B1643197
theorem B3698257 : Blo 1459549 3698257 := bstep (se 2 (by rfl) ⟨1386846, by rfl⟩ : syracuseStep 3698257 = 2773693) B2773693
theorem B2371169 : Blo 1459549 2371169 := bstep (se 2 (by rfl) ⟨889188, by rfl⟩ : syracuseStep 2371169 = 1778377) B1778377
theorem B2190947 : Blo 1459549 2190947 := bstep (se 1 (by rfl) ⟨1643210, by rfl⟩ : syracuseStep 2190947 = 3286421) B3286421
theorem B1642099 : Blo 1459549 1642099 := bstep (se 1 (by rfl) ⟨1231574, by rfl⟩ : syracuseStep 1642099 = 2463149) B2463149
theorem B2190977 : Blo 1459549 2190977 := bstep (se 2 (by rfl) ⟨821616, by rfl⟩ : syracuseStep 2190977 = 1643233) B1643233
theorem B4927121 : Blo 1459549 4927121 := bstep (se 2 (by rfl) ⟨1847670, by rfl⟩ : syracuseStep 4927121 = 3695341) B3695341
theorem B2190995 : Blo 1459549 2190995 := bstep (se 1 (by rfl) ⟨1643246, by rfl⟩ : syracuseStep 2190995 = 3286493) B3286493
theorem B2191025 : Blo 1459549 2191025 := bstep (se 2 (by rfl) ⟨821634, by rfl⟩ : syracuseStep 2191025 = 1643269) B1643269
theorem B2191043 : Blo 1459549 2191043 := bstep (se 1 (by rfl) ⟨1643282, by rfl⟩ : syracuseStep 2191043 = 3286565) B3286565
theorem B2191073 : Blo 1459549 2191073 := bstep (se 2 (by rfl) ⟨821652, by rfl⟩ : syracuseStep 2191073 = 1643305) B1643305
theorem B2772721 : Blo 1459549 2772721 := bstep (se 2 (by rfl) ⟨1039770, by rfl⟩ : syracuseStep 2772721 = 2079541) B2079541
theorem B2961137 : Blo 1459549 2961137 := bstep (se 2 (by rfl) ⟨1110426, by rfl⟩ : syracuseStep 2961137 = 2220853) B2220853
theorem B2191091 : Blo 1459549 2191091 := bstep (se 1 (by rfl) ⟨1643318, by rfl⟩ : syracuseStep 2191091 = 3286637) B3286637
theorem B2338561 : Blo 1459549 2338561 := bstep (se 2 (by rfl) ⟨876960, by rfl⟩ : syracuseStep 2338561 = 1753921) B1753921
theorem B1642243 : Blo 1459549 1642243 := bstep (se 1 (by rfl) ⟨1231682, by rfl⟩ : syracuseStep 1642243 = 2463365) B2463365
theorem B2191121 : Blo 1459549 2191121 := bstep (se 2 (by rfl) ⟨821670, by rfl⟩ : syracuseStep 2191121 = 1643341) B1643341
theorem B2191139 : Blo 1459549 2191139 := bstep (se 1 (by rfl) ⟨1643354, by rfl⟩ : syracuseStep 2191139 = 3286709) B3286709
theorem B2191169 : Blo 1459549 2191169 := bstep (se 2 (by rfl) ⟨821688, by rfl⟩ : syracuseStep 2191169 = 1643377) B1643377
theorem B2191187 : Blo 1459549 2191187 := bstep (se 1 (by rfl) ⟨1643390, by rfl⟩ : syracuseStep 2191187 = 3286781) B3286781
theorem B11235185 : Blo 1459549 11235185 := bstep (se 2 (by rfl) ⟨4213194, by rfl⟩ : syracuseStep 11235185 = 8426389) B8426389
theorem B2191217 : Blo 1459549 2191217 := bstep (se 2 (by rfl) ⟨821706, by rfl⟩ : syracuseStep 2191217 = 1643413) B1643413
theorem B2191235 : Blo 1459549 2191235 := bstep (se 1 (by rfl) ⟨1643426, by rfl⟩ : syracuseStep 2191235 = 3286853) B3286853
theorem B1642387 : Blo 1459549 1642387 := bstep (se 1 (by rfl) ⟨1231790, by rfl⟩ : syracuseStep 1642387 = 2463581) B2463581
theorem B2191265 : Blo 1459549 2191265 := bstep (se 2 (by rfl) ⟨821724, by rfl⟩ : syracuseStep 2191265 = 1643449) B1643449
theorem B2191283 : Blo 1459549 2191283 := bstep (se 1 (by rfl) ⟨1643462, by rfl⟩ : syracuseStep 2191283 = 3286925) B3286925
theorem B2191313 : Blo 1459549 2191313 := bstep (se 2 (by rfl) ⟨821742, by rfl⟩ : syracuseStep 2191313 = 1643485) B1643485
theorem B2191331 : Blo 1459549 2191331 := bstep (se 1 (by rfl) ⟨1643498, by rfl⟩ : syracuseStep 2191331 = 3286997) B3286997
theorem B2191361 : Blo 1459549 2191361 := bstep (se 2 (by rfl) ⟨821760, by rfl⟩ : syracuseStep 2191361 = 1643521) B1643521
theorem B2191379 : Blo 1459549 2191379 := bstep (se 1 (by rfl) ⟨1643534, by rfl⟩ : syracuseStep 2191379 = 3287069) B3287069
theorem B1642531 : Blo 1459549 1642531 := bstep (se 1 (by rfl) ⟨1231898, by rfl⟩ : syracuseStep 1642531 = 2463797) B2463797
theorem B2191409 : Blo 1459549 2191409 := bstep (se 2 (by rfl) ⟨821778, by rfl⟩ : syracuseStep 2191409 = 1643557) B1643557
theorem B2191427 : Blo 1459549 2191427 := bstep (se 1 (by rfl) ⟨1643570, by rfl⟩ : syracuseStep 2191427 = 3287141) B3287141
theorem B5541965 : Blo 1459549 5541965 := bstep (se 3 (by rfl) ⟨1039118, by rfl⟩ : syracuseStep 5541965 = 2078237) B2078237
theorem B2191457 : Blo 1459549 2191457 := bstep (se 2 (by rfl) ⟨821796, by rfl⟩ : syracuseStep 2191457 = 1643593) B1643593
theorem B2191475 : Blo 1459549 2191475 := bstep (se 1 (by rfl) ⟨1643606, by rfl⟩ : syracuseStep 2191475 = 3287213) B3287213
theorem B7893125 : Blo 1459549 7893125 := bstep (se 4 (by rfl) ⟨739980, by rfl⟩ : syracuseStep 7893125 = 1479961) B1479961
theorem B2191505 : Blo 1459549 2191505 := bstep (se 2 (by rfl) ⟨821814, by rfl⟩ : syracuseStep 2191505 = 1643629) B1643629
theorem B1847443 : Blo 1459549 1847443 := bstep (se 1 (by rfl) ⟨1385582, by rfl⟩ : syracuseStep 1847443 = 2771165) B2771165
theorem B2191523 : Blo 1459549 2191523 := bstep (se 1 (by rfl) ⟨1643642, by rfl⟩ : syracuseStep 2191523 = 3287285) B3287285
theorem B4927661 : Blo 1459549 4927661 := bstep (se 3 (by rfl) ⟨923936, by rfl⟩ : syracuseStep 4927661 = 1847873) B1847873
theorem B1642675 : Blo 1459549 1642675 := bstep (se 1 (by rfl) ⟨1232006, by rfl⟩ : syracuseStep 1642675 = 2464013) B2464013
theorem B2191553 : Blo 1459549 2191553 := bstep (se 2 (by rfl) ⟨821832, by rfl⟩ : syracuseStep 2191553 = 1643665) B1643665
theorem B2191571 : Blo 1459549 2191571 := bstep (se 1 (by rfl) ⟨1643678, by rfl⟩ : syracuseStep 2191571 = 3287357) B3287357
theorem B4927715 : Blo 1459549 4927715 := bstep (se 1 (by rfl) ⟨3695786, by rfl⟩ : syracuseStep 4927715 = 7391573) B7391573
theorem B7893233 : Blo 1459549 7893233 := bstep (se 2 (by rfl) ⟨2959962, by rfl⟩ : syracuseStep 7893233 = 5919925) B5919925
theorem B1847539 : Blo 1459549 1847539 := bstep (se 1 (by rfl) ⟨1385654, by rfl⟩ : syracuseStep 1847539 = 2771309) B2771309
theorem B4501763 : Blo 1459549 4501763 := bstep (se 1 (by rfl) ⟨3376322, by rfl⟩ : syracuseStep 4501763 = 6752645) B6752645
theorem B1642819 : Blo 1459549 1642819 := bstep (se 1 (by rfl) ⟨1232114, by rfl⟩ : syracuseStep 1642819 = 2464229) B2464229
theorem B1642963 : Blo 1459549 1642963 := bstep (se 1 (by rfl) ⟨1232222, by rfl⟩ : syracuseStep 1642963 = 2464445) B2464445
theorem B6238691 : Blo 1459549 6238691 := bstep (se 1 (by rfl) ⟨4679018, by rfl⟩ : syracuseStep 6238691 = 9358037) B9358037
theorem B4927985 : Blo 1459549 4927985 := bstep (se 2 (by rfl) ⟨1847994, by rfl⟩ : syracuseStep 4927985 = 3695989) B3695989
theorem B7393841 : Blo 1459549 7393841 := bstep (se 2 (by rfl) ⟨2772690, by rfl⟩ : syracuseStep 7393841 = 5545381) B5545381
theorem B1643107 : Blo 1459549 1643107 := bstep (se 1 (by rfl) ⟨1232330, by rfl⟩ : syracuseStep 1643107 = 2464661) B2464661
theorem B4158125 : Blo 1459549 4158125 := bstep (se 3 (by rfl) ⟨779648, by rfl⟩ : syracuseStep 4158125 = 1559297) B1559297
theorem B1848035 : Blo 1459549 1848035 := bstep (se 1 (by rfl) ⟨1386026, by rfl⟩ : syracuseStep 1848035 = 2772053) B2772053
theorem B1643251 : Blo 1459549 1643251 := bstep (se 1 (by rfl) ⟨1232438, by rfl⟩ : syracuseStep 1643251 = 2464877) B2464877
theorem B4158307 : Blo 1459549 4158307 := bstep (se 1 (by rfl) ⟨3118730, by rfl⟩ : syracuseStep 4158307 = 6237461) B6237461
theorem B5542769 : Blo 1459549 5542769 := bstep (se 2 (by rfl) ⟨2078538, by rfl⟩ : syracuseStep 5542769 = 4157077) B4157077
theorem B1643395 : Blo 1459549 1643395 := bstep (se 1 (by rfl) ⟨1232546, by rfl⟩ : syracuseStep 1643395 = 2465093) B2465093
theorem B9360269 : Blo 1459549 9360269 := bstep (se 3 (by rfl) ⟨1755050, by rfl⟩ : syracuseStep 9360269 = 3510101) B3510101
theorem B4158353 : Blo 1459549 4158353 := bstep (se 2 (by rfl) ⟨1559382, by rfl⟩ : syracuseStep 4158353 = 3118765) B3118765
theorem B2339779 : Blo 1459549 2339779 := bstep (se 1 (by rfl) ⟨1754834, by rfl⟩ : syracuseStep 2339779 = 3509669) B3509669
theorem B8319941 : Blo 1459549 8319941 := bstep (se 4 (by rfl) ⟨779994, by rfl⟩ : syracuseStep 8319941 = 1559989) B1559989
theorem B4928525 : Blo 1459549 4928525 := bstep (se 3 (by rfl) ⟨924098, by rfl⟩ : syracuseStep 4928525 = 1848197) B1848197
theorem B1643539 : Blo 1459549 1643539 := bstep (se 1 (by rfl) ⟨1232654, by rfl⟩ : syracuseStep 1643539 = 2465309) B2465309
theorem B4928579 : Blo 1459549 4928579 := bstep (se 1 (by rfl) ⟨3696434, by rfl⟩ : syracuseStep 4928579 = 7392869) B7392869
theorem B9360497 : Blo 1459549 9360497 := bstep (se 2 (by rfl) ⟨3510186, by rfl⟩ : syracuseStep 9360497 = 7020373) B7020373
theorem B14038285 : Blo 1459549 14038285 := bstep (se 3 (by rfl) ⟨2632178, by rfl⟩ : syracuseStep 14038285 = 5264357) B5264357
theorem B2463041 : Blo 1459549 2463041 := bstep (se 2 (by rfl) ⟨923640, by rfl⟩ : syracuseStep 2463041 = 1847281) B1847281
theorem B4928849 : Blo 1459549 4928849 := bstep (se 2 (by rfl) ⟨1848318, by rfl⟩ : syracuseStep 4928849 = 3696637) B3696637
theorem B1848739 : Blo 1459549 1848739 := bstep (se 1 (by rfl) ⟨1386554, by rfl⟩ : syracuseStep 1848739 = 2773109) B2773109
theorem B2463169 : Blo 1459549 2463169 := bstep (se 2 (by rfl) ⟨923688, by rfl⟩ : syracuseStep 2463169 = 1847377) B1847377
theorem B2463203 : Blo 1459549 2463203 := bstep (se 1 (by rfl) ⟨1847402, by rfl⟩ : syracuseStep 2463203 = 3694805) B3694805
theorem B1848835 : Blo 1459549 1848835 := bstep (se 1 (by rfl) ⟨1386626, by rfl⟩ : syracuseStep 1848835 = 2773253) B2773253
theorem B5543437 : Blo 1459549 5543437 := bstep (se 3 (by rfl) ⟨1039394, by rfl⟩ : syracuseStep 5543437 = 2078789) B2078789
theorem B2463331 : Blo 1459549 2463331 := bstep (se 1 (by rfl) ⟨1847498, by rfl⟩ : syracuseStep 2463331 = 3694997) B3694997
theorem B3946097 : Blo 1459549 3946097 := bstep (se 2 (by rfl) ⟨1479786, by rfl⟩ : syracuseStep 3946097 = 2959573) B2959573
theorem B1480403 : Blo 1459549 1480403 := bstep (se 1 (by rfl) ⟨1110302, by rfl⟩ : syracuseStep 1480403 = 2220605) B2220605
theorem B2463473 : Blo 1459549 2463473 := bstep (se 2 (by rfl) ⟨923802, by rfl⟩ : syracuseStep 2463473 = 1847605) B1847605
theorem B22484789 : Blo 1459549 22484789 := bstep (se 5 (by rfl) ⟨1053974, by rfl⟩ : syracuseStep 22484789 = 2107949) B2107949
theorem B4929389 : Blo 1459549 4929389 := bstep (se 3 (by rfl) ⟨924260, by rfl⟩ : syracuseStep 4929389 = 1848521) B1848521
theorem B2463601 : Blo 1459549 2463601 := bstep (se 2 (by rfl) ⟨923850, by rfl⟩ : syracuseStep 2463601 = 1847701) B1847701
theorem B15783821 : Blo 1459549 15783821 := bstep (se 3 (by rfl) ⟨2959466, by rfl⟩ : syracuseStep 15783821 = 5918933) B5918933
theorem B2463635 : Blo 1459549 2463635 := bstep (se 1 (by rfl) ⟨1847726, by rfl⟩ : syracuseStep 2463635 = 3695453) B3695453
theorem B4929443 : Blo 1459549 4929443 := bstep (se 1 (by rfl) ⟨3697082, by rfl⟩ : syracuseStep 4929443 = 7394165) B7394165
theorem B7395299 : Blo 1459549 7395299 := bstep (se 1 (by rfl) ⟨5546474, by rfl⟩ : syracuseStep 7395299 = 11092949) B11092949
theorem B3119107 : Blo 1459549 3119107 := bstep (se 1 (by rfl) ⟨2339330, by rfl⟩ : syracuseStep 3119107 = 4678661) B4678661
theorem B2463763 : Blo 1459549 2463763 := bstep (se 1 (by rfl) ⟨1847822, by rfl⟩ : syracuseStep 2463763 = 3695645) B3695645
theorem B28440629 : Blo 1459549 28440629 := bstep (se 5 (by rfl) ⟨1333154, by rfl⟩ : syracuseStep 28440629 = 2666309) B2666309
theorem B142071893 : Blo 1459549 142071893 := bstep (se 8 (by rfl) ⟨832452, by rfl⟩ : syracuseStep 142071893 = 1664905) B1664905
theorem B11090033 : Blo 1459549 11090033 := bstep (se 2 (by rfl) ⟨4158762, by rfl⟩ : syracuseStep 11090033 = 8317525) B8317525
theorem B2463905 : Blo 1459549 2463905 := bstep (se 2 (by rfl) ⟨923964, by rfl⟩ : syracuseStep 2463905 = 1847929) B1847929
theorem B4929713 : Blo 1459549 4929713 := bstep (se 2 (by rfl) ⟨1848642, by rfl⟩ : syracuseStep 4929713 = 3697285) B3697285
theorem B5921009 : Blo 1459549 5921009 := bstep (se 2 (by rfl) ⟨2220378, by rfl⟩ : syracuseStep 5921009 = 4440757) B4440757
theorem B2464033 : Blo 1459549 2464033 := bstep (se 2 (by rfl) ⟨924012, by rfl⟩ : syracuseStep 2464033 = 1848025) B1848025
theorem B5544227 : Blo 1459549 5544227 := bstep (se 1 (by rfl) ⟨4158170, by rfl⟩ : syracuseStep 5544227 = 8316341) B8316341
theorem B2496833 : Blo 1459549 2496833 := bstep (se 2 (by rfl) ⟨936312, by rfl⟩ : syracuseStep 2496833 = 1872625) B1872625
theorem B2464067 : Blo 1459549 2464067 := bstep (se 1 (by rfl) ⟨1848050, by rfl⟩ : syracuseStep 2464067 = 3696101) B3696101
theorem B4159811 : Blo 1459549 4159811 := bstep (se 1 (by rfl) ⟨3119858, by rfl⟩ : syracuseStep 4159811 = 6239717) B6239717
theorem B35993969 : Blo 1459549 35993969 := bstep (se 2 (by rfl) ⟨13497738, by rfl⟩ : syracuseStep 35993969 = 26995477) B26995477
theorem B2464195 : Blo 1459549 2464195 := bstep (se 1 (by rfl) ⟨1848146, by rfl⟩ : syracuseStep 2464195 = 3696293) B3696293
theorem B2464337 : Blo 1459549 2464337 := bstep (se 2 (by rfl) ⟨924126, by rfl⟩ : syracuseStep 2464337 = 1848253) B1848253
theorem B13318769 : Blo 1459549 13318769 := bstep (se 2 (by rfl) ⟨4994538, by rfl⟩ : syracuseStep 13318769 = 9989077) B9989077
theorem B2079427 : Blo 1459549 2079427 := bstep (se 1 (by rfl) ⟨1559570, by rfl⟩ : syracuseStep 2079427 = 3119141) B3119141
theorem B4930253 : Blo 1459549 4930253 := bstep (se 3 (by rfl) ⟨924422, by rfl⟩ : syracuseStep 4930253 = 1848845) B1848845
theorem B2464465 : Blo 1459549 2464465 := bstep (se 2 (by rfl) ⟨924174, by rfl⟩ : syracuseStep 2464465 = 1848349) B1848349
theorem B2464499 : Blo 1459549 2464499 := bstep (se 1 (by rfl) ⟨1848374, by rfl⟩ : syracuseStep 2464499 = 3696749) B3696749
theorem B4930307 : Blo 1459549 4930307 := bstep (se 1 (by rfl) ⟨3697730, by rfl⟩ : syracuseStep 4930307 = 7395461) B7395461
theorem B7396109 : Blo 1459549 7396109 := bstep (se 3 (by rfl) ⟨1386770, by rfl⟩ : syracuseStep 7396109 = 2773541) B2773541
theorem B4938563 : Blo 1459549 4938563 := bstep (se 1 (by rfl) ⟨3703922, by rfl⟩ : syracuseStep 4938563 = 7407845) B7407845
theorem B8313677 : Blo 1459549 8313677 := bstep (se 3 (by rfl) ⟨1558814, by rfl⟩ : syracuseStep 8313677 = 3117629) B3117629
theorem B3119953 : Blo 1459549 3119953 := bstep (se 2 (by rfl) ⟨1169982, by rfl⟩ : syracuseStep 3119953 = 2339965) B2339965
theorem B4438883 : Blo 1459549 4438883 := bstep (se 1 (by rfl) ⟨3329162, by rfl⟩ : syracuseStep 4438883 = 6658325) B6658325
theorem B2464627 : Blo 1459549 2464627 := bstep (se 1 (by rfl) ⟨1848470, by rfl⟩ : syracuseStep 2464627 = 3696941) B3696941
theorem B5544881 : Blo 1459549 5544881 := bstep (se 2 (by rfl) ⟨2079330, by rfl⟩ : syracuseStep 5544881 = 4158661) B4158661
theorem B2464769 : Blo 1459549 2464769 := bstep (se 2 (by rfl) ⟨924288, by rfl⟩ : syracuseStep 2464769 = 1848577) B1848577
theorem B4930577 : Blo 1459549 4930577 := bstep (se 2 (by rfl) ⟨1848966, by rfl⟩ : syracuseStep 4930577 = 3697933) B3697933
theorem B3284081 : Blo 1459549 3284081 := bstep (se 2 (by rfl) ⟨1231530, by rfl⟩ : syracuseStep 3284081 = 2463061) B2463061
theorem B2464897 : Blo 1459549 2464897 := bstep (se 2 (by rfl) ⟨924336, by rfl⟩ : syracuseStep 2464897 = 1848673) B1848673
theorem B3284099 : Blo 1459549 3284099 := bstep (se 1 (by rfl) ⟨2463074, by rfl⟩ : syracuseStep 3284099 = 4926149) B4926149
theorem B2464931 : Blo 1459549 2464931 := bstep (se 1 (by rfl) ⟨1848698, by rfl⟩ : syracuseStep 2464931 = 3697397) B3697397
theorem B2465059 : Blo 1459549 2465059 := bstep (se 1 (by rfl) ⟨1848794, by rfl⟩ : syracuseStep 2465059 = 3697589) B3697589
theorem B16637237 : Blo 1459549 16637237 := bstep (se 5 (by rfl) ⟨779870, by rfl⟩ : syracuseStep 16637237 = 1559741) B1559741
theorem B2497873 : Blo 1459549 2497873 := bstep (se 2 (by rfl) ⟨936702, by rfl⟩ : syracuseStep 2497873 = 1873405) B1873405
theorem B3284369 : Blo 1459549 3284369 := bstep (se 2 (by rfl) ⟨1231638, by rfl⟩ : syracuseStep 3284369 = 2463277) B2463277
theorem B3284387 : Blo 1459549 3284387 := bstep (se 1 (by rfl) ⟨2463290, by rfl⟩ : syracuseStep 3284387 = 4926581) B4926581
theorem B6659491 : Blo 1459549 6659491 := bstep (se 1 (by rfl) ⟨4994618, by rfl⟩ : syracuseStep 6659491 = 9989237) B9989237
theorem B2465201 : Blo 1459549 2465201 := bstep (se 2 (by rfl) ⟨924450, by rfl⟩ : syracuseStep 2465201 = 1848901) B1848901
theorem B2465329 : Blo 1459549 2465329 := bstep (se 2 (by rfl) ⟨924498, by rfl⟩ : syracuseStep 2465329 = 1848997) B1848997
theorem B2530883 : Blo 1459549 2530883 := bstep (se 1 (by rfl) ⟨1898162, by rfl⟩ : syracuseStep 2530883 = 3796325) B3796325
theorem B2465363 : Blo 1459549 2465363 := bstep (se 1 (by rfl) ⟨1849022, by rfl⟩ : syracuseStep 2465363 = 3698045) B3698045
theorem B1973875 : Blo 1459549 1973875 := bstep (se 1 (by rfl) ⟨1480406, by rfl⟩ : syracuseStep 1973875 = 2960813) B2960813
theorem B3948173 : Blo 1459549 3948173 := bstep (se 3 (by rfl) ⟨740282, by rfl⟩ : syracuseStep 3948173 = 1480565) B1480565
theorem B3284657 : Blo 1459549 3284657 := bstep (se 2 (by rfl) ⟨1231746, by rfl⟩ : syracuseStep 3284657 = 2463493) B2463493
theorem B3284675 : Blo 1459549 3284675 := bstep (se 1 (by rfl) ⟨2463506, by rfl⟩ : syracuseStep 3284675 = 4927013) B4927013
theorem B2465491 : Blo 1459549 2465491 := bstep (se 1 (by rfl) ⟨1849118, by rfl⟩ : syracuseStep 2465491 = 3698237) B3698237
theorem B8314609 : Blo 1459549 8314609 := bstep (se 2 (by rfl) ⟨3117978, by rfl⟩ : syracuseStep 8314609 = 6235957) B6235957
theorem B3948355 : Blo 1459549 3948355 := bstep (se 1 (by rfl) ⟨2961266, by rfl⟩ : syracuseStep 3948355 = 5922533) B5922533
theorem B3694531 : Blo 1459549 3694531 := bstep (se 1 (by rfl) ⟨2770898, by rfl⟩ : syracuseStep 3694531 = 5541797) B5541797
theorem B3284945 : Blo 1459549 3284945 := bstep (se 2 (by rfl) ⟨1231854, by rfl⟩ : syracuseStep 3284945 = 2463709) B2463709
theorem B11837411 : Blo 1459549 11837411 := bstep (se 1 (by rfl) ⟨8878058, by rfl⟩ : syracuseStep 11837411 = 17756117) B17756117
theorem B3284963 : Blo 1459549 3284963 := bstep (se 1 (by rfl) ⟨2463722, by rfl⟩ : syracuseStep 3284963 = 4927445) B4927445
theorem B3285017 : Blo 1459549 3285017 := bstep (se 2 (by rfl) ⟨1231881, by rfl⟩ : syracuseStep 3285017 = 2463763) B2463763
theorem B3694643 : Blo 1459549 3694643 := bstep (se 1 (by rfl) ⟨2770982, by rfl⟩ : syracuseStep 3694643 = 5541965) B5541965
theorem B3285107 : Blo 1459549 3285107 := bstep (se 1 (by rfl) ⟨2463830, by rfl⟩ : syracuseStep 3285107 = 4927661) B4927661
theorem B3285143 : Blo 1459549 3285143 := bstep (se 1 (by rfl) ⟨2463857, by rfl⟩ : syracuseStep 3285143 = 4927715) B4927715
theorem B3285323 : Blo 1459549 3285323 := bstep (se 1 (by rfl) ⟨2463992, by rfl⟩ : syracuseStep 3285323 = 4927985) B4927985
theorem B3948875 : Blo 1459549 3948875 := bstep (se 1 (by rfl) ⟨2961656, by rfl⟩ : syracuseStep 3948875 = 5923313) B5923313
theorem B3285377 : Blo 1459549 3285377 := bstep (se 2 (by rfl) ⟨1232016, by rfl⟩ : syracuseStep 3285377 = 2464033) B2464033
theorem B4391371 : Blo 1459549 4391371 := bstep (se 1 (by rfl) ⟨3293528, by rfl⟩ : syracuseStep 4391371 = 6587057) B6587057
theorem B3695179 : Blo 1459549 3695179 := bstep (se 1 (by rfl) ⟨2771384, by rfl⟩ : syracuseStep 3695179 = 5542769) B5542769
theorem B3285593 : Blo 1459549 3285593 := bstep (se 2 (by rfl) ⟨1232097, by rfl⟩ : syracuseStep 3285593 = 2464195) B2464195
theorem B5546627 : Blo 1459549 5546627 := bstep (se 1 (by rfl) ⟨4159970, by rfl⟩ : syracuseStep 5546627 = 8319941) B8319941
theorem B3285683 : Blo 1459549 3285683 := bstep (se 1 (by rfl) ⟨2464262, by rfl⟩ : syracuseStep 3285683 = 4928525) B4928525
theorem B3285719 : Blo 1459549 3285719 := bstep (se 1 (by rfl) ⟨2464289, by rfl⟩ : syracuseStep 3285719 = 4928579) B4928579
theorem B3695321 : Blo 1459549 3695321 := bstep (se 2 (by rfl) ⟨1385745, by rfl⟩ : syracuseStep 3695321 = 2771491) B2771491
theorem B3285899 : Blo 1459549 3285899 := bstep (se 1 (by rfl) ⟨2464424, by rfl⟩ : syracuseStep 3285899 = 4928849) B4928849
theorem B3285953 : Blo 1459549 3285953 := bstep (se 2 (by rfl) ⟨1232232, by rfl⟩ : syracuseStep 3285953 = 2464465) B2464465
theorem B2630731 : Blo 1459549 2630731 := bstep (se 1 (by rfl) ⟨1973048, by rfl⟩ : syracuseStep 2630731 = 3946097) B3946097
theorem B3286169 : Blo 1459549 3286169 := bstep (se 2 (by rfl) ⟨1232313, by rfl⟩ : syracuseStep 3286169 = 2464627) B2464627
theorem B3376307 : Blo 1459549 3376307 := bstep (se 1 (by rfl) ⟨2532230, by rfl⟩ : syracuseStep 3376307 = 5064461) B5064461
theorem B3286259 : Blo 1459549 3286259 := bstep (se 1 (by rfl) ⟨2464694, by rfl⟩ : syracuseStep 3286259 = 4929389) B4929389
theorem B3286295 : Blo 1459549 3286295 := bstep (se 1 (by rfl) ⟨2464721, by rfl⟩ : syracuseStep 3286295 = 4929443) B4929443
theorem B1459563 : Blo 1459549 1459563 := bstep (se 1 (by rfl) ⟨1094672, by rfl⟩ : syracuseStep 1459563 = 2189345) B2189345
theorem B1459575 : Blo 1459549 1459575 := bstep (se 1 (by rfl) ⟨1094681, by rfl⟩ : syracuseStep 1459575 = 2189363) B2189363
theorem B1459595 : Blo 1459549 1459595 := bstep (se 1 (by rfl) ⟨1094696, by rfl⟩ : syracuseStep 1459595 = 2189393) B2189393
theorem B1459607 : Blo 1459549 1459607 := bstep (se 1 (by rfl) ⟨1094705, by rfl⟩ : syracuseStep 1459607 = 2189411) B2189411
theorem B1459627 : Blo 1459549 1459627 := bstep (se 1 (by rfl) ⟨1094720, by rfl⟩ : syracuseStep 1459627 = 2189441) B2189441
theorem B1459639 : Blo 1459549 1459639 := bstep (se 1 (by rfl) ⟨1094729, by rfl⟩ : syracuseStep 1459639 = 2189459) B2189459
theorem B1459659 : Blo 1459549 1459659 := bstep (se 1 (by rfl) ⟨1094744, by rfl⟩ : syracuseStep 1459659 = 2189489) B2189489
theorem B3286475 : Blo 1459549 3286475 := bstep (se 1 (by rfl) ⟨2464856, by rfl⟩ : syracuseStep 3286475 = 4929713) B4929713
theorem B1459671 : Blo 1459549 1459671 := bstep (se 1 (by rfl) ⟨1094753, by rfl⟩ : syracuseStep 1459671 = 2189507) B2189507
theorem B1459691 : Blo 1459549 1459691 := bstep (se 1 (by rfl) ⟨1094768, by rfl⟩ : syracuseStep 1459691 = 2189537) B2189537
theorem B1459703 : Blo 1459549 1459703 := bstep (se 1 (by rfl) ⟨1094777, by rfl⟩ : syracuseStep 1459703 = 2189555) B2189555
theorem B3286529 : Blo 1459549 3286529 := bstep (se 2 (by rfl) ⟨1232448, by rfl⟩ : syracuseStep 3286529 = 2464897) B2464897
theorem B1459723 : Blo 1459549 1459723 := bstep (se 1 (by rfl) ⟨1094792, by rfl⟩ : syracuseStep 1459723 = 2189585) B2189585
theorem B1459735 : Blo 1459549 1459735 := bstep (se 1 (by rfl) ⟨1094801, by rfl⟩ : syracuseStep 1459735 = 2189603) B2189603
theorem B3696151 : Blo 1459549 3696151 := bstep (se 1 (by rfl) ⟨2772113, by rfl⟩ : syracuseStep 3696151 = 5544227) B5544227
theorem B1664555 : Blo 1459549 1664555 := bstep (se 1 (by rfl) ⟨1248416, by rfl⟩ : syracuseStep 1664555 = 2496833) B2496833
theorem B1459755 : Blo 1459549 1459755 := bstep (se 1 (by rfl) ⟨1094816, by rfl⟩ : syracuseStep 1459755 = 2189633) B2189633
theorem B1459767 : Blo 1459549 1459767 := bstep (se 1 (by rfl) ⟨1094825, by rfl⟩ : syracuseStep 1459767 = 2189651) B2189651
theorem B23995979 : Blo 1459549 23995979 := bstep (se 1 (by rfl) ⟨17996984, by rfl⟩ : syracuseStep 23995979 = 35993969) B35993969
theorem B1459787 : Blo 1459549 1459787 := bstep (se 1 (by rfl) ⟨1094840, by rfl⟩ : syracuseStep 1459787 = 2189681) B2189681
theorem B1459799 : Blo 1459549 1459799 := bstep (se 1 (by rfl) ⟨1094849, by rfl⟩ : syracuseStep 1459799 = 2189699) B2189699
theorem B1459819 : Blo 1459549 1459819 := bstep (se 1 (by rfl) ⟨1094864, by rfl⟩ : syracuseStep 1459819 = 2189729) B2189729
theorem B1459831 : Blo 1459549 1459831 := bstep (se 1 (by rfl) ⟨1094873, by rfl⟩ : syracuseStep 1459831 = 2189747) B2189747
theorem B1459851 : Blo 1459549 1459851 := bstep (se 1 (by rfl) ⟨1094888, by rfl⟩ : syracuseStep 1459851 = 2189777) B2189777
theorem B1459863 : Blo 1459549 1459863 := bstep (se 1 (by rfl) ⟨1094897, by rfl⟩ : syracuseStep 1459863 = 2189795) B2189795
theorem B1459883 : Blo 1459549 1459883 := bstep (se 1 (by rfl) ⟨1094912, by rfl⟩ : syracuseStep 1459883 = 2189825) B2189825
theorem B13321907 : Blo 1459549 13321907 := bstep (se 1 (by rfl) ⟨9991430, by rfl⟩ : syracuseStep 13321907 = 19982861) B19982861
theorem B1459895 : Blo 1459549 1459895 := bstep (se 1 (by rfl) ⟨1094921, by rfl⟩ : syracuseStep 1459895 = 2189843) B2189843
theorem B1459915 : Blo 1459549 1459915 := bstep (se 1 (by rfl) ⟨1094936, by rfl⟩ : syracuseStep 1459915 = 2189873) B2189873
theorem B1459927 : Blo 1459549 1459927 := bstep (se 1 (by rfl) ⟨1094945, by rfl⟩ : syracuseStep 1459927 = 2189891) B2189891
theorem B3286745 : Blo 1459549 3286745 := bstep (se 2 (by rfl) ⟨1232529, by rfl⟩ : syracuseStep 3286745 = 2465059) B2465059
theorem B1459947 : Blo 1459549 1459947 := bstep (se 1 (by rfl) ⟨1094960, by rfl⟩ : syracuseStep 1459947 = 2189921) B2189921
theorem B1459959 : Blo 1459549 1459959 := bstep (se 1 (by rfl) ⟨1094969, by rfl⟩ : syracuseStep 1459959 = 2189939) B2189939
theorem B1459979 : Blo 1459549 1459979 := bstep (se 1 (by rfl) ⟨1094984, by rfl⟩ : syracuseStep 1459979 = 2189969) B2189969
theorem B1459991 : Blo 1459549 1459991 := bstep (se 1 (by rfl) ⟨1094993, by rfl⟩ : syracuseStep 1459991 = 2189987) B2189987
theorem B1460011 : Blo 1459549 1460011 := bstep (se 1 (by rfl) ⟨1095008, by rfl⟩ : syracuseStep 1460011 = 2190017) B2190017
theorem B3286835 : Blo 1459549 3286835 := bstep (se 1 (by rfl) ⟨2465126, by rfl⟩ : syracuseStep 3286835 = 4930253) B4930253
theorem B1460023 : Blo 1459549 1460023 := bstep (se 1 (by rfl) ⟨1095017, by rfl⟩ : syracuseStep 1460023 = 2190035) B2190035
theorem B1460043 : Blo 1459549 1460043 := bstep (se 1 (by rfl) ⟨1095032, by rfl⟩ : syracuseStep 1460043 = 2190065) B2190065
theorem B1460055 : Blo 1459549 1460055 := bstep (se 1 (by rfl) ⟨1095041, by rfl⟩ : syracuseStep 1460055 = 2190083) B2190083
theorem B3286871 : Blo 1459549 3286871 := bstep (se 1 (by rfl) ⟨2465153, by rfl⟩ : syracuseStep 3286871 = 4930307) B4930307
theorem B4441949 : Blo 1459549 4441949 := bstep (se 3 (by rfl) ⟨832865, by rfl⟩ : syracuseStep 4441949 = 1665731) B1665731
theorem B1460075 : Blo 1459549 1460075 := bstep (se 1 (by rfl) ⟨1095056, by rfl⟩ : syracuseStep 1460075 = 2190113) B2190113
theorem B1460087 : Blo 1459549 1460087 := bstep (se 1 (by rfl) ⟨1095065, by rfl⟩ : syracuseStep 1460087 = 2190131) B2190131
theorem B1460107 : Blo 1459549 1460107 := bstep (se 1 (by rfl) ⟨1095080, by rfl⟩ : syracuseStep 1460107 = 2190161) B2190161
theorem B2959255 : Blo 1459549 2959255 := bstep (se 1 (by rfl) ⟨2219441, by rfl⟩ : syracuseStep 2959255 = 4438883) B4438883
theorem B1460119 : Blo 1459549 1460119 := bstep (se 1 (by rfl) ⟨1095089, by rfl⟩ : syracuseStep 1460119 = 2190179) B2190179
theorem B1460139 : Blo 1459549 1460139 := bstep (se 1 (by rfl) ⟨1095104, by rfl⟩ : syracuseStep 1460139 = 2190209) B2190209
theorem B1460151 : Blo 1459549 1460151 := bstep (se 1 (by rfl) ⟨1095113, by rfl⟩ : syracuseStep 1460151 = 2190227) B2190227
theorem B1460171 : Blo 1459549 1460171 := bstep (se 1 (by rfl) ⟨1095128, by rfl⟩ : syracuseStep 1460171 = 2190257) B2190257
theorem B3696587 : Blo 1459549 3696587 := bstep (se 1 (by rfl) ⟨2772440, by rfl⟩ : syracuseStep 3696587 = 5544881) B5544881
theorem B11847629 : Blo 1459549 11847629 := bstep (se 3 (by rfl) ⟨2221430, by rfl⟩ : syracuseStep 11847629 = 4442861) B4442861
theorem B1460183 : Blo 1459549 1460183 := bstep (se 1 (by rfl) ⟨1095137, by rfl⟩ : syracuseStep 1460183 = 2190275) B2190275
theorem B1460203 : Blo 1459549 1460203 := bstep (se 1 (by rfl) ⟨1095152, by rfl⟩ : syracuseStep 1460203 = 2190305) B2190305
theorem B1460215 : Blo 1459549 1460215 := bstep (se 1 (by rfl) ⟨1095161, by rfl⟩ : syracuseStep 1460215 = 2190323) B2190323
theorem B1460235 : Blo 1459549 1460235 := bstep (se 1 (by rfl) ⟨1095176, by rfl⟩ : syracuseStep 1460235 = 2190353) B2190353
theorem B3287051 : Blo 1459549 3287051 := bstep (se 1 (by rfl) ⟨2465288, by rfl⟩ : syracuseStep 3287051 = 4930577) B4930577
theorem B7391249 : Blo 1459549 7391249 := bstep (se 2 (by rfl) ⟨2771718, by rfl⟩ : syracuseStep 7391249 = 5543437) B5543437
theorem B1460247 : Blo 1459549 1460247 := bstep (se 1 (by rfl) ⟨1095185, by rfl⟩ : syracuseStep 1460247 = 2190371) B2190371
theorem B1460267 : Blo 1459549 1460267 := bstep (se 1 (by rfl) ⟨1095200, by rfl⟩ : syracuseStep 1460267 = 2190401) B2190401
theorem B1460279 : Blo 1459549 1460279 := bstep (se 1 (by rfl) ⟨1095209, by rfl⟩ : syracuseStep 1460279 = 2190419) B2190419
theorem B3287105 : Blo 1459549 3287105 := bstep (se 2 (by rfl) ⟨1232664, by rfl⟩ : syracuseStep 3287105 = 2465329) B2465329
theorem B2189387 : Blo 1459549 2189387 := bstep (se 1 (by rfl) ⟨1642040, by rfl⟩ : syracuseStep 2189387 = 3284081) B3284081
theorem B1460299 : Blo 1459549 1460299 := bstep (se 1 (by rfl) ⟨1095224, by rfl⟩ : syracuseStep 1460299 = 2190449) B2190449
theorem B2189399 : Blo 1459549 2189399 := bstep (se 1 (by rfl) ⟨1642049, by rfl⟩ : syracuseStep 2189399 = 3284099) B3284099
theorem B1460311 : Blo 1459549 1460311 := bstep (se 1 (by rfl) ⟨1095233, by rfl⟩ : syracuseStep 1460311 = 2190467) B2190467
theorem B1460331 : Blo 1459549 1460331 := bstep (se 1 (by rfl) ⟨1095248, by rfl⟩ : syracuseStep 1460331 = 2190497) B2190497
theorem B1460343 : Blo 1459549 1460343 := bstep (se 1 (by rfl) ⟨1095257, by rfl⟩ : syracuseStep 1460343 = 2190515) B2190515
theorem B1460363 : Blo 1459549 1460363 := bstep (se 1 (by rfl) ⟨1095272, by rfl⟩ : syracuseStep 1460363 = 2190545) B2190545
theorem B1460375 : Blo 1459549 1460375 := bstep (se 1 (by rfl) ⟨1095281, by rfl⟩ : syracuseStep 1460375 = 2190563) B2190563
theorem B2189465 : Blo 1459549 2189465 := bstep (se 2 (by rfl) ⟨821049, by rfl⟩ : syracuseStep 2189465 = 1642099) B1642099
theorem B2631833 : Blo 1459549 2631833 := bstep (se 2 (by rfl) ⟨986937, by rfl⟩ : syracuseStep 2631833 = 1973875) B1973875
theorem B1460395 : Blo 1459549 1460395 := bstep (se 1 (by rfl) ⟨1095296, by rfl⟩ : syracuseStep 1460395 = 2190593) B2190593
theorem B7391411 : Blo 1459549 7391411 := bstep (se 1 (by rfl) ⟨5543558, by rfl⟩ : syracuseStep 7391411 = 11087117) B11087117
theorem B1460407 : Blo 1459549 1460407 := bstep (se 1 (by rfl) ⟨1095305, by rfl⟩ : syracuseStep 1460407 = 2190611) B2190611
theorem B1460427 : Blo 1459549 1460427 := bstep (se 1 (by rfl) ⟨1095320, by rfl⟩ : syracuseStep 1460427 = 2190641) B2190641
theorem B1460439 : Blo 1459549 1460439 := bstep (se 1 (by rfl) ⟨1095329, by rfl⟩ : syracuseStep 1460439 = 2190659) B2190659
theorem B1460459 : Blo 1459549 1460459 := bstep (se 1 (by rfl) ⟨1095344, by rfl⟩ : syracuseStep 1460459 = 2190689) B2190689
theorem B1460471 : Blo 1459549 1460471 := bstep (se 1 (by rfl) ⟨1095353, by rfl⟩ : syracuseStep 1460471 = 2190707) B2190707
theorem B2189579 : Blo 1459549 2189579 := bstep (se 1 (by rfl) ⟨1642184, by rfl⟩ : syracuseStep 2189579 = 3284369) B3284369
theorem B1460491 : Blo 1459549 1460491 := bstep (se 1 (by rfl) ⟨1095368, by rfl⟩ : syracuseStep 1460491 = 2190737) B2190737
theorem B2189591 : Blo 1459549 2189591 := bstep (se 1 (by rfl) ⟨1642193, by rfl⟩ : syracuseStep 2189591 = 3284387) B3284387
theorem B1460503 : Blo 1459549 1460503 := bstep (se 1 (by rfl) ⟨1095377, by rfl⟩ : syracuseStep 1460503 = 2190755) B2190755
theorem B3287321 : Blo 1459549 3287321 := bstep (se 2 (by rfl) ⟨1232745, by rfl⟩ : syracuseStep 3287321 = 2465491) B2465491
theorem B1460523 : Blo 1459549 1460523 := bstep (se 1 (by rfl) ⟨1095392, by rfl⟩ : syracuseStep 1460523 = 2190785) B2190785
theorem B1460535 : Blo 1459549 1460535 := bstep (se 1 (by rfl) ⟨1095401, by rfl⟩ : syracuseStep 1460535 = 2190803) B2190803
theorem B11086145 : Blo 1459549 11086145 := bstep (se 2 (by rfl) ⟨4157304, by rfl⟩ : syracuseStep 11086145 = 8314609) B8314609
theorem B3696961 : Blo 1459549 3696961 := bstep (se 2 (by rfl) ⟨1386360, by rfl⟩ : syracuseStep 3696961 = 2772721) B2772721
theorem B1460555 : Blo 1459549 1460555 := bstep (se 1 (by rfl) ⟨1095416, by rfl⟩ : syracuseStep 1460555 = 2190833) B2190833
theorem B1460567 : Blo 1459549 1460567 := bstep (se 1 (by rfl) ⟨1095425, by rfl⟩ : syracuseStep 1460567 = 2190851) B2190851
theorem B2189657 : Blo 1459549 2189657 := bstep (se 2 (by rfl) ⟨821121, by rfl⟩ : syracuseStep 2189657 = 1642243) B1642243
theorem B1460587 : Blo 1459549 1460587 := bstep (se 1 (by rfl) ⟨1095440, by rfl⟩ : syracuseStep 1460587 = 2190881) B2190881
theorem B1460599 : Blo 1459549 1460599 := bstep (se 1 (by rfl) ⟨1095449, by rfl⟩ : syracuseStep 1460599 = 2190899) B2190899
theorem B1460619 : Blo 1459549 1460619 := bstep (se 1 (by rfl) ⟨1095464, by rfl⟩ : syracuseStep 1460619 = 2190929) B2190929
theorem B1460631 : Blo 1459549 1460631 := bstep (se 1 (by rfl) ⟨1095473, by rfl⟩ : syracuseStep 1460631 = 2190947) B2190947
theorem B1460651 : Blo 1459549 1460651 := bstep (se 1 (by rfl) ⟨1095488, by rfl⟩ : syracuseStep 1460651 = 2190977) B2190977
theorem B2632115 : Blo 1459549 2632115 := bstep (se 1 (by rfl) ⟨1974086, by rfl⟩ : syracuseStep 2632115 = 3948173) B3948173
theorem B1460663 : Blo 1459549 1460663 := bstep (se 1 (by rfl) ⟨1095497, by rfl⟩ : syracuseStep 1460663 = 2190995) B2190995
theorem B2189771 : Blo 1459549 2189771 := bstep (se 1 (by rfl) ⟨1642328, by rfl⟩ : syracuseStep 2189771 = 3284657) B3284657
theorem B1460683 : Blo 1459549 1460683 := bstep (se 1 (by rfl) ⟨1095512, by rfl⟩ : syracuseStep 1460683 = 2191025) B2191025
theorem B2189783 : Blo 1459549 2189783 := bstep (se 1 (by rfl) ⟨1642337, by rfl⟩ : syracuseStep 2189783 = 3284675) B3284675
theorem B1460695 : Blo 1459549 1460695 := bstep (se 1 (by rfl) ⟨1095521, by rfl⟩ : syracuseStep 1460695 = 2191043) B2191043
theorem B1460715 : Blo 1459549 1460715 := bstep (se 1 (by rfl) ⟨1095536, by rfl⟩ : syracuseStep 1460715 = 2191073) B2191073
theorem B1460727 : Blo 1459549 1460727 := bstep (se 1 (by rfl) ⟨1095545, by rfl⟩ : syracuseStep 1460727 = 2191091) B2191091
theorem B1460747 : Blo 1459549 1460747 := bstep (se 1 (by rfl) ⟨1095560, by rfl⟩ : syracuseStep 1460747 = 2191121) B2191121
theorem B1460759 : Blo 1459549 1460759 := bstep (se 1 (by rfl) ⟨1095569, by rfl⟩ : syracuseStep 1460759 = 2191139) B2191139
theorem B2189849 : Blo 1459549 2189849 := bstep (se 2 (by rfl) ⟨821193, by rfl⟩ : syracuseStep 2189849 = 1642387) B1642387
theorem B1460779 : Blo 1459549 1460779 := bstep (se 1 (by rfl) ⟨1095584, by rfl⟩ : syracuseStep 1460779 = 2191169) B2191169
theorem B1460791 : Blo 1459549 1460791 := bstep (se 1 (by rfl) ⟨1095593, by rfl⟩ : syracuseStep 1460791 = 2191187) B2191187
theorem B7490123 : Blo 1459549 7490123 := bstep (se 1 (by rfl) ⟨5617592, by rfl⟩ : syracuseStep 7490123 = 11235185) B11235185
theorem B1460811 : Blo 1459549 1460811 := bstep (se 1 (by rfl) ⟨1095608, by rfl⟩ : syracuseStep 1460811 = 2191217) B2191217
theorem B1460823 : Blo 1459549 1460823 := bstep (se 1 (by rfl) ⟨1095617, by rfl⟩ : syracuseStep 1460823 = 2191235) B2191235
theorem B4926041 : Blo 1459549 4926041 := bstep (se 2 (by rfl) ⟨1847265, by rfl⟩ : syracuseStep 4926041 = 3694531) B3694531
theorem B1460843 : Blo 1459549 1460843 := bstep (se 1 (by rfl) ⟨1095632, by rfl⟩ : syracuseStep 1460843 = 2191265) B2191265
theorem B1460855 : Blo 1459549 1460855 := bstep (se 1 (by rfl) ⟨1095641, by rfl⟩ : syracuseStep 1460855 = 2191283) B2191283
theorem B2189963 : Blo 1459549 2189963 := bstep (se 1 (by rfl) ⟨1642472, by rfl⟩ : syracuseStep 2189963 = 3284945) B3284945
theorem B1460875 : Blo 1459549 1460875 := bstep (se 1 (by rfl) ⟨1095656, by rfl⟩ : syracuseStep 1460875 = 2191313) B2191313
theorem B7891607 : Blo 1459549 7891607 := bstep (se 1 (by rfl) ⟨5918705, by rfl⟩ : syracuseStep 7891607 = 11837411) B11837411
theorem B2189975 : Blo 1459549 2189975 := bstep (se 1 (by rfl) ⟨1642481, by rfl⟩ : syracuseStep 2189975 = 3284963) B3284963
theorem B1460887 : Blo 1459549 1460887 := bstep (se 1 (by rfl) ⟨1095665, by rfl⟩ : syracuseStep 1460887 = 2191331) B2191331
theorem B1460907 : Blo 1459549 1460907 := bstep (se 1 (by rfl) ⟨1095680, by rfl⟩ : syracuseStep 1460907 = 2191361) B2191361
theorem B1460919 : Blo 1459549 1460919 := bstep (se 1 (by rfl) ⟨1095689, by rfl⟩ : syracuseStep 1460919 = 2191379) B2191379
theorem B1460939 : Blo 1459549 1460939 := bstep (se 1 (by rfl) ⟨1095704, by rfl⟩ : syracuseStep 1460939 = 2191409) B2191409
theorem B1460951 : Blo 1459549 1460951 := bstep (se 1 (by rfl) ⟨1095713, by rfl⟩ : syracuseStep 1460951 = 2191427) B2191427
theorem B2190041 : Blo 1459549 2190041 := bstep (se 2 (by rfl) ⟨821265, by rfl⟩ : syracuseStep 2190041 = 1642531) B1642531
theorem B1460971 : Blo 1459549 1460971 := bstep (se 1 (by rfl) ⟨1095728, by rfl⟩ : syracuseStep 1460971 = 2191457) B2191457
theorem B1460983 : Blo 1459549 1460983 := bstep (se 1 (by rfl) ⟨1095737, by rfl⟩ : syracuseStep 1460983 = 2191475) B2191475
theorem B5262083 : Blo 1459549 5262083 := bstep (se 1 (by rfl) ⟨3946562, by rfl⟩ : syracuseStep 5262083 = 7893125) B7893125
theorem B1461003 : Blo 1459549 1461003 := bstep (se 1 (by rfl) ⟨1095752, by rfl⟩ : syracuseStep 1461003 = 2191505) B2191505
theorem B1461015 : Blo 1459549 1461015 := bstep (se 1 (by rfl) ⟨1095761, by rfl⟩ : syracuseStep 1461015 = 2191523) B2191523
theorem B1461035 : Blo 1459549 1461035 := bstep (se 1 (by rfl) ⟨1095776, by rfl⟩ : syracuseStep 1461035 = 2191553) B2191553
theorem B1461047 : Blo 1459549 1461047 := bstep (se 1 (by rfl) ⟨1095785, by rfl⟩ : syracuseStep 1461047 = 2191571) B2191571
theorem B5262155 : Blo 1459549 5262155 := bstep (se 1 (by rfl) ⟨3946616, by rfl⟩ : syracuseStep 5262155 = 7893233) B7893233
theorem B2190155 : Blo 1459549 2190155 := bstep (se 1 (by rfl) ⟨1642616, by rfl⟩ : syracuseStep 2190155 = 3285233) B3285233
theorem B2190167 : Blo 1459549 2190167 := bstep (se 1 (by rfl) ⟨1642625, by rfl⟩ : syracuseStep 2190167 = 3285251) B3285251
theorem B3001175 : Blo 1459549 3001175 := bstep (se 1 (by rfl) ⟨2250881, by rfl⟩ : syracuseStep 3001175 = 4501763) B4501763
theorem B3697559 : Blo 1459549 3697559 := bstep (se 1 (by rfl) ⟨2773169, by rfl⟩ : syracuseStep 3697559 = 5546339) B5546339
theorem B2190233 : Blo 1459549 2190233 := bstep (se 2 (by rfl) ⟨821337, by rfl⟩ : syracuseStep 2190233 = 1642675) B1642675
theorem B2190347 : Blo 1459549 2190347 := bstep (se 1 (by rfl) ⟨1642760, by rfl⟩ : syracuseStep 2190347 = 3285521) B3285521
theorem B2190359 : Blo 1459549 2190359 := bstep (se 1 (by rfl) ⟨1642769, by rfl⟩ : syracuseStep 2190359 = 3285539) B3285539
theorem B2632727 : Blo 1459549 2632727 := bstep (se 1 (by rfl) ⟨1974545, by rfl⟩ : syracuseStep 2632727 = 3949091) B3949091
theorem B2190425 : Blo 1459549 2190425 := bstep (se 2 (by rfl) ⟨821409, by rfl⟩ : syracuseStep 2190425 = 1642819) B1642819
theorem B2772083 : Blo 1459549 2772083 := bstep (se 1 (by rfl) ⟨2079062, by rfl⟩ : syracuseStep 2772083 = 4158125) B4158125
theorem B2190539 : Blo 1459549 2190539 := bstep (se 1 (by rfl) ⟨1642904, by rfl⟩ : syracuseStep 2190539 = 3285809) B3285809
theorem B2190551 : Blo 1459549 2190551 := bstep (se 1 (by rfl) ⟨1642913, by rfl⟩ : syracuseStep 2190551 = 3285827) B3285827
theorem B2772235 : Blo 1459549 2772235 := bstep (se 1 (by rfl) ⟨2079176, by rfl⟩ : syracuseStep 2772235 = 4158353) B4158353
theorem B4926743 : Blo 1459549 4926743 := bstep (se 1 (by rfl) ⟨3695057, by rfl⟩ : syracuseStep 4926743 = 7390115) B7390115
theorem B2190617 : Blo 1459549 2190617 := bstep (se 2 (by rfl) ⟨821481, by rfl⟩ : syracuseStep 2190617 = 1642963) B1642963
theorem B10268005 : Blo 1459549 10268005 := bstep (se 4 (by rfl) ⟨962625, by rfl⟩ : syracuseStep 10268005 = 1925251) B1925251
theorem B2190731 : Blo 1459549 2190731 := bstep (se 1 (by rfl) ⟨1643048, by rfl⟩ : syracuseStep 2190731 = 3286097) B3286097
theorem B2190743 : Blo 1459549 2190743 := bstep (se 1 (by rfl) ⟨1643057, by rfl⟩ : syracuseStep 2190743 = 3286115) B3286115
theorem B2190809 : Blo 1459549 2190809 := bstep (se 2 (by rfl) ⟨821553, by rfl⟩ : syracuseStep 2190809 = 1643107) B1643107
theorem B6237719 : Blo 1459549 6237719 := bstep (se 1 (by rfl) ⟨4678289, by rfl⟩ : syracuseStep 6237719 = 9356579) B9356579
theorem B1642027 : Blo 1459549 1642027 := bstep (se 1 (by rfl) ⟨1231520, by rfl⟩ : syracuseStep 1642027 = 2463041) B2463041
theorem B2190923 : Blo 1459549 2190923 := bstep (se 1 (by rfl) ⟨1643192, by rfl⟩ : syracuseStep 2190923 = 3286385) B3286385
theorem B16641611 : Blo 1459549 16641611 := bstep (se 1 (by rfl) ⟨12481208, by rfl⟩ : syracuseStep 16641611 = 24962417) B24962417
theorem B2190935 : Blo 1459549 2190935 := bstep (se 1 (by rfl) ⟨1643201, by rfl⟩ : syracuseStep 2190935 = 3286403) B3286403
theorem B2772569 : Blo 1459549 2772569 := bstep (se 2 (by rfl) ⟨1039713, by rfl⟩ : syracuseStep 2772569 = 2079427) B2079427
theorem B4157021 : Blo 1459549 4157021 := bstep (se 3 (by rfl) ⟨779441, by rfl⟩ : syracuseStep 4157021 = 1558883) B1558883
theorem B1642135 : Blo 1459549 1642135 := bstep (se 1 (by rfl) ⟨1231601, by rfl⟩ : syracuseStep 1642135 = 2463203) B2463203
theorem B2191001 : Blo 1459549 2191001 := bstep (se 2 (by rfl) ⟨821625, by rfl⟩ : syracuseStep 2191001 = 1643251) B1643251
theorem B2191115 : Blo 1459549 2191115 := bstep (se 1 (by rfl) ⟨1643336, by rfl⟩ : syracuseStep 2191115 = 3286673) B3286673
theorem B2191127 : Blo 1459549 2191127 := bstep (se 1 (by rfl) ⟨1643345, by rfl⟩ : syracuseStep 2191127 = 3286691) B3286691
theorem B4927283 : Blo 1459549 4927283 := bstep (se 1 (by rfl) ⟨3695462, by rfl⟩ : syracuseStep 4927283 = 7390925) B7390925
theorem B1642315 : Blo 1459549 1642315 := bstep (se 1 (by rfl) ⟨1231736, by rfl⟩ : syracuseStep 1642315 = 2463473) B2463473
theorem B2191193 : Blo 1459549 2191193 := bstep (se 2 (by rfl) ⟨821697, by rfl⟩ : syracuseStep 2191193 = 1643395) B1643395
theorem B10522547 : Blo 1459549 10522547 := bstep (se 1 (by rfl) ⟨7891910, by rfl⟩ : syracuseStep 10522547 = 15783821) B15783821
theorem B1642423 : Blo 1459549 1642423 := bstep (se 1 (by rfl) ⟨1231817, by rfl⟩ : syracuseStep 1642423 = 2463635) B2463635
theorem B2191307 : Blo 1459549 2191307 := bstep (se 1 (by rfl) ⟨1643480, by rfl⟩ : syracuseStep 2191307 = 3286961) B3286961
theorem B2191319 : Blo 1459549 2191319 := bstep (se 1 (by rfl) ⟨1643489, by rfl⟩ : syracuseStep 2191319 = 3286979) B3286979
theorem B2404313 : Blo 1459549 2404313 := bstep (se 2 (by rfl) ⟨901617, by rfl⟩ : syracuseStep 2404313 = 1803235) B1803235
theorem B12472325 : Blo 1459549 12472325 := bstep (se 4 (by rfl) ⟨1169280, by rfl⟩ : syracuseStep 12472325 = 2338561) B2338561
theorem B2191385 : Blo 1459549 2191385 := bstep (se 2 (by rfl) ⟨821769, by rfl⟩ : syracuseStep 2191385 = 1643539) B1643539
theorem B18960419 : Blo 1459549 18960419 := bstep (se 1 (by rfl) ⟨14220314, by rfl⟩ : syracuseStep 18960419 = 28440629) B28440629
theorem B4927553 : Blo 1459549 4927553 := bstep (se 2 (by rfl) ⟨1847832, by rfl⟩ : syracuseStep 4927553 = 3695665) B3695665
theorem B7393355 : Blo 1459549 7393355 := bstep (se 1 (by rfl) ⟨5545016, by rfl⟩ : syracuseStep 7393355 = 11090033) B11090033
theorem B1642603 : Blo 1459549 1642603 := bstep (se 1 (by rfl) ⟨1231952, by rfl⟩ : syracuseStep 1642603 = 2463905) B2463905
theorem B2191499 : Blo 1459549 2191499 := bstep (se 1 (by rfl) ⟨1643624, by rfl⟩ : syracuseStep 2191499 = 3287249) B3287249
theorem B2961559 : Blo 1459549 2961559 := bstep (se 1 (by rfl) ⟨2221169, by rfl⟩ : syracuseStep 2961559 = 4442339) B4442339
theorem B2191511 : Blo 1459549 2191511 := bstep (se 1 (by rfl) ⟨1643633, by rfl⟩ : syracuseStep 2191511 = 3287267) B3287267
theorem B1642711 : Blo 1459549 1642711 := bstep (se 1 (by rfl) ⟨1232033, by rfl⟩ : syracuseStep 1642711 = 2464067) B2464067
theorem B2773207 : Blo 1459549 2773207 := bstep (se 1 (by rfl) ⟨2079905, by rfl⟩ : syracuseStep 2773207 = 4159811) B4159811
theorem B11088089 : Blo 1459549 11088089 := bstep (se 2 (by rfl) ⟨4158033, by rfl⟩ : syracuseStep 11088089 = 8316067) B8316067
theorem B7893293 : Blo 1459549 7893293 := bstep (se 3 (by rfl) ⟨1479992, by rfl⟩ : syracuseStep 7893293 = 2959985) B2959985
theorem B16855361 : Blo 1459549 16855361 := bstep (se 2 (by rfl) ⟨6320760, by rfl⟩ : syracuseStep 16855361 = 12641521) B12641521
theorem B21057893 : Blo 1459549 21057893 := bstep (se 4 (by rfl) ⟨1974177, by rfl⟩ : syracuseStep 21057893 = 3948355) B3948355
theorem B1642891 : Blo 1459549 1642891 := bstep (se 1 (by rfl) ⟨1232168, by rfl⟩ : syracuseStep 1642891 = 2464337) B2464337
theorem B3330497 : Blo 1459549 3330497 := bstep (se 2 (by rfl) ⟨1248936, by rfl⟩ : syracuseStep 3330497 = 2497873) B2497873
theorem B1847767 : Blo 1459549 1847767 := bstep (se 1 (by rfl) ⟨1385825, by rfl⟩ : syracuseStep 1847767 = 2771651) B2771651
theorem B1642999 : Blo 1459549 1642999 := bstep (se 1 (by rfl) ⟨1232249, by rfl⟩ : syracuseStep 1642999 = 2464499) B2464499
theorem B5542451 : Blo 1459549 5542451 := bstep (se 1 (by rfl) ⟨4156838, by rfl⟩ : syracuseStep 5542451 = 8313677) B8313677
theorem B5542465 : Blo 1459549 5542465 := bstep (se 2 (by rfl) ⟨2078424, by rfl⟩ : syracuseStep 5542465 = 4156849) B4156849
theorem B4928093 : Blo 1459549 4928093 := bstep (se 3 (by rfl) ⟨924017, by rfl⟩ : syracuseStep 4928093 = 1848035) B1848035
theorem B1643179 : Blo 1459549 1643179 := bstep (se 1 (by rfl) ⟨1232384, by rfl⟩ : syracuseStep 1643179 = 2464769) B2464769
theorem B1643287 : Blo 1459549 1643287 := bstep (se 1 (by rfl) ⟨1232465, by rfl⟩ : syracuseStep 1643287 = 2464931) B2464931
theorem B1643467 : Blo 1459549 1643467 := bstep (se 1 (by rfl) ⟨1232600, by rfl⟩ : syracuseStep 1643467 = 2465201) B2465201
theorem B1643575 : Blo 1459549 1643575 := bstep (se 1 (by rfl) ⟨1232681, by rfl⟩ : syracuseStep 1643575 = 2465363) B2465363
theorem B4158809 : Blo 1459549 4158809 := bstep (se 2 (by rfl) ⟨1559553, by rfl⟩ : syracuseStep 4158809 = 3119107) B3119107
theorem B2463115 : Blo 1459549 2463115 := bstep (se 1 (by rfl) ⟨1847336, by rfl⟩ : syracuseStep 2463115 = 3694673) B3694673
theorem B3118475 : Blo 1459549 3118475 := bstep (se 1 (by rfl) ⟨2338856, by rfl⟩ : syracuseStep 3118475 = 4677713) B4677713
theorem B2463257 : Blo 1459549 2463257 := bstep (se 2 (by rfl) ⟨923721, by rfl⟩ : syracuseStep 2463257 = 1847443) B1847443
theorem B8001125 : Blo 1459549 8001125 := bstep (se 4 (by rfl) ⟨750105, by rfl⟩ : syracuseStep 8001125 = 1500211) B1500211
theorem B4159127 : Blo 1459549 4159127 := bstep (se 1 (by rfl) ⟨3119345, by rfl⟩ : syracuseStep 4159127 = 6238691) B6238691
theorem B2463385 : Blo 1459549 2463385 := bstep (se 2 (by rfl) ⟨923769, by rfl⟩ : syracuseStep 2463385 = 1847539) B1847539
theorem B3847873 : Blo 1459549 3847873 := bstep (se 2 (by rfl) ⟨1442952, by rfl⟩ : syracuseStep 3847873 = 2885905) B2885905
theorem B4929227 : Blo 1459549 4929227 := bstep (se 1 (by rfl) ⟨3696920, by rfl⟩ : syracuseStep 4929227 = 7393841) B7393841
theorem B14030597 : Blo 1459549 14030597 := bstep (se 4 (by rfl) ⟨1315368, by rfl⟩ : syracuseStep 14030597 = 2630737) B2630737
theorem B7395137 : Blo 1459549 7395137 := bstep (se 2 (by rfl) ⟨2773176, by rfl⟩ : syracuseStep 7395137 = 5546353) B5546353
theorem B8312651 : Blo 1459549 8312651 := bstep (se 1 (by rfl) ⟨6234488, by rfl⟩ : syracuseStep 8312651 = 12468977) B12468977
theorem B6240179 : Blo 1459549 6240179 := bstep (se 1 (by rfl) ⟨4680134, by rfl⟩ : syracuseStep 6240179 = 9360269) B9360269
theorem B4929497 : Blo 1459549 4929497 := bstep (se 2 (by rfl) ⟨1848561, by rfl⟩ : syracuseStep 4929497 = 3697123) B3697123
theorem B5265425 : Blo 1459549 5265425 := bstep (se 2 (by rfl) ⟨1974534, by rfl⟩ : syracuseStep 5265425 = 3949069) B3949069
theorem B6240331 : Blo 1459549 6240331 := bstep (se 1 (by rfl) ⟨4680248, by rfl⟩ : syracuseStep 6240331 = 9360497) B9360497
theorem B6240401 : Blo 1459549 6240401 := bstep (se 2 (by rfl) ⟨2340150, by rfl⟩ : syracuseStep 6240401 = 4680301) B4680301
theorem B2463959 : Blo 1459549 2463959 := bstep (se 1 (by rfl) ⟨1847969, by rfl⟩ : syracuseStep 2463959 = 3695939) B3695939
theorem B5921041 : Blo 1459549 5921041 := bstep (se 2 (by rfl) ⟨2220390, by rfl⟩ : syracuseStep 5921041 = 4440781) B4440781
theorem B2496791 : Blo 1459549 2496791 := bstep (se 1 (by rfl) ⟨1872593, by rfl⟩ : syracuseStep 2496791 = 3745187) B3745187
theorem B2464087 : Blo 1459549 2464087 := bstep (se 1 (by rfl) ⟨1848065, by rfl⟩ : syracuseStep 2464087 = 3696131) B3696131
theorem B4159937 : Blo 1459549 4159937 := bstep (se 2 (by rfl) ⟨1559976, by rfl⟩ : syracuseStep 4159937 = 3119953) B3119953
theorem B5544395 : Blo 1459549 5544395 := bstep (se 1 (by rfl) ⟨4158296, by rfl⟩ : syracuseStep 5544395 = 8316593) B8316593
theorem B5544409 : Blo 1459549 5544409 := bstep (se 2 (by rfl) ⟨2079153, by rfl⟩ : syracuseStep 5544409 = 4158307) B4158307
theorem B14989859 : Blo 1459549 14989859 := bstep (se 1 (by rfl) ⟨11242394, by rfl⟩ : syracuseStep 14989859 = 22484789) B22484789
theorem B3119705 : Blo 1459549 3119705 := bstep (se 2 (by rfl) ⟨1169889, by rfl⟩ : syracuseStep 3119705 = 2339779) B2339779
theorem B4930199 : Blo 1459549 4930199 := bstep (se 1 (by rfl) ⟨3697649, by rfl⟩ : syracuseStep 4930199 = 7395299) B7395299
theorem B4741811 : Blo 1459549 4741811 := bstep (se 1 (by rfl) ⟨3556358, by rfl⟩ : syracuseStep 4741811 = 7112717) B7112717
theorem B94714595 : Blo 1459549 94714595 := bstep (se 1 (by rfl) ⟨71035946, by rfl⟩ : syracuseStep 94714595 = 142071893) B142071893
theorem B3947339 : Blo 1459549 3947339 := bstep (se 1 (by rfl) ⟨2960504, by rfl⟩ : syracuseStep 3947339 = 5921009) B5921009
theorem B6749021 : Blo 1459549 6749021 := bstep (se 3 (by rfl) ⟨1265441, by rfl⟩ : syracuseStep 6749021 = 2530883) B2530883
theorem B2464715 : Blo 1459549 2464715 := bstep (se 1 (by rfl) ⟨1848536, by rfl⟩ : syracuseStep 2464715 = 3697073) B3697073
theorem B3120115 : Blo 1459549 3120115 := bstep (se 1 (by rfl) ⟨2340086, by rfl⟩ : syracuseStep 3120115 = 4680173) B4680173
theorem B18717713 : Blo 1459549 18717713 := bstep (se 2 (by rfl) ⟨7019142, by rfl⟩ : syracuseStep 18717713 = 14038285) B14038285
theorem B3283991 : Blo 1459549 3283991 := bstep (se 1 (by rfl) ⟨2462993, by rfl⟩ : syracuseStep 3283991 = 4925987) B4925987
theorem B2079769 : Blo 1459549 2079769 := bstep (se 2 (by rfl) ⟨779913, by rfl⟩ : syracuseStep 2079769 = 1559827) B1559827
theorem B5135425 : Blo 1459549 5135425 := bstep (se 2 (by rfl) ⟨1925784, by rfl⟩ : syracuseStep 5135425 = 3851569) B3851569
theorem B8879179 : Blo 1459549 8879179 := bstep (se 1 (by rfl) ⟨6659384, by rfl⟩ : syracuseStep 8879179 = 13318769) B13318769
theorem B2464843 : Blo 1459549 2464843 := bstep (se 1 (by rfl) ⟨1848632, by rfl⟩ : syracuseStep 2464843 = 3697265) B3697265
theorem B1973335 : Blo 1459549 1973335 := bstep (se 1 (by rfl) ⟨1480001, by rfl⟩ : syracuseStep 1973335 = 2960003) B2960003
theorem B4930739 : Blo 1459549 4930739 := bstep (se 1 (by rfl) ⟨3698054, by rfl⟩ : syracuseStep 4930739 = 7396109) B7396109
theorem B3284171 : Blo 1459549 3284171 := bstep (se 1 (by rfl) ⟨2463128, by rfl⟩ : syracuseStep 3284171 = 4926257) B4926257
theorem B6659275 : Blo 1459549 6659275 := bstep (se 1 (by rfl) ⟨4994456, by rfl⟩ : syracuseStep 6659275 = 9988913) B9988913
theorem B3292375 : Blo 1459549 3292375 := bstep (se 1 (by rfl) ⟨2469281, by rfl⟩ : syracuseStep 3292375 = 4938563) B4938563
theorem B8879321 : Blo 1459549 8879321 := bstep (se 2 (by rfl) ⟨3329745, by rfl⟩ : syracuseStep 8879321 = 6659491) B6659491
theorem B2464985 : Blo 1459549 2464985 := bstep (se 2 (by rfl) ⟨924369, by rfl⟩ : syracuseStep 2464985 = 1848739) B1848739
theorem B3947741 : Blo 1459549 3947741 := bstep (se 3 (by rfl) ⟨740201, by rfl⟩ : syracuseStep 3947741 = 1480403) B1480403
theorem B3120371 : Blo 1459549 3120371 := bstep (se 1 (by rfl) ⟨2340278, by rfl⟩ : syracuseStep 3120371 = 4680557) B4680557
theorem B3284225 : Blo 1459549 3284225 := bstep (se 2 (by rfl) ⟨1231584, by rfl⟩ : syracuseStep 3284225 = 2463169) B2463169
theorem B7896365 : Blo 1459549 7896365 := bstep (se 3 (by rfl) ⟨1480568, by rfl⟩ : syracuseStep 7896365 = 2961137) B2961137
theorem B2465113 : Blo 1459549 2465113 := bstep (se 2 (by rfl) ⟨924417, by rfl⟩ : syracuseStep 2465113 = 1848835) B1848835
theorem B12475741 : Blo 1459549 12475741 := bstep (se 3 (by rfl) ⟨2339201, by rfl⟩ : syracuseStep 12475741 = 4678403) B4678403
theorem B5545367 : Blo 1459549 5545367 := bstep (se 1 (by rfl) ⟨4159025, by rfl⟩ : syracuseStep 5545367 = 8318051) B8318051
theorem B4931009 : Blo 1459549 4931009 := bstep (se 2 (by rfl) ⟨1849128, by rfl⟩ : syracuseStep 4931009 = 3698257) B3698257
theorem B1580503 : Blo 1459549 1580503 := bstep (se 1 (by rfl) ⟨1185377, by rfl⟩ : syracuseStep 1580503 = 2370755) B2370755
theorem B3284441 : Blo 1459549 3284441 := bstep (se 2 (by rfl) ⟨1231665, by rfl⟩ : syracuseStep 3284441 = 2463331) B2463331
theorem B11091491 : Blo 1459549 11091491 := bstep (se 1 (by rfl) ⟨8318618, by rfl⟩ : syracuseStep 11091491 = 16637237) B16637237
theorem B3284531 : Blo 1459549 3284531 := bstep (se 1 (by rfl) ⟨2463398, by rfl⟩ : syracuseStep 3284531 = 4926797) B4926797
theorem B3284567 : Blo 1459549 3284567 := bstep (se 1 (by rfl) ⟨2463425, by rfl⟩ : syracuseStep 3284567 = 4926851) B4926851
theorem B50585219 : Blo 1459549 50585219 := bstep (se 1 (by rfl) ⟨37938914, by rfl⟩ : syracuseStep 50585219 = 75877829) B75877829
theorem B1580779 : Blo 1459549 1580779 := bstep (se 1 (by rfl) ⟨1185584, by rfl⟩ : syracuseStep 1580779 = 2371169) B2371169
theorem B3284747 : Blo 1459549 3284747 := bstep (se 1 (by rfl) ⟨2463560, by rfl⟩ : syracuseStep 3284747 = 4927121) B4927121
theorem B3284801 : Blo 1459549 3284801 := bstep (se 2 (by rfl) ⟨1231800, by rfl⟩ : syracuseStep 3284801 = 2463601) B2463601
theorem B8314883 : Blo 1459549 8314883 := bstep (se 1 (by rfl) ⟨6236162, by rfl⟩ : syracuseStep 8314883 = 12472325) B12472325
theorem B3285035 : Blo 1459549 3285035 := bstep (se 1 (by rfl) ⟨2463776, by rfl⟩ : syracuseStep 3285035 = 4927553) B4927553
theorem B14041133 : Blo 1459549 14041133 := bstep (se 3 (by rfl) ⟨2632712, by rfl⟩ : syracuseStep 14041133 = 5265425) B5265425
theorem B50561117 : Blo 1459549 50561117 := bstep (se 3 (by rfl) ⟨9480209, by rfl⟩ : syracuseStep 50561117 = 18960419) B18960419
theorem B3948745 : Blo 1459549 3948745 := bstep (se 2 (by rfl) ⟨1480779, by rfl⟩ : syracuseStep 3948745 = 2961559) B2961559
theorem B3694967 : Blo 1459549 3694967 := bstep (se 1 (by rfl) ⟨2771225, by rfl⟩ : syracuseStep 3694967 = 5542451) B5542451
theorem B3285395 : Blo 1459549 3285395 := bstep (se 1 (by rfl) ⟨2464046, by rfl⟩ : syracuseStep 3285395 = 4928093) B4928093
theorem B3285449 : Blo 1459549 3285449 := bstep (se 2 (by rfl) ⟨1232043, by rfl⟩ : syracuseStep 3285449 = 2464087) B2464087
theorem B7389953 : Blo 1459549 7389953 := bstep (se 2 (by rfl) ⟨2771232, by rfl⟩ : syracuseStep 7389953 = 5542465) B5542465
theorem B5334083 : Blo 1459549 5334083 := bstep (se 1 (by rfl) ⟨4000562, by rfl⟩ : syracuseStep 5334083 = 8001125) B8001125
theorem B8881271 : Blo 1459549 8881271 := bstep (se 1 (by rfl) ⟨6660953, by rfl⟩ : syracuseStep 8881271 = 13321907) B13321907
theorem B3286151 : Blo 1459549 3286151 := bstep (se 1 (by rfl) ⟨2464613, by rfl⟩ : syracuseStep 3286151 = 4929227) B4929227
theorem B8881325 : Blo 1459549 8881325 := bstep (se 3 (by rfl) ⟨1665248, by rfl⟩ : syracuseStep 8881325 = 3330497) B3330497
theorem B8430821 : Blo 1459549 8430821 := bstep (se 4 (by rfl) ⟨790389, by rfl⟩ : syracuseStep 8430821 = 1580779) B1580779
theorem B7898419 : Blo 1459549 7898419 := bstep (se 1 (by rfl) ⟨5923814, by rfl⟩ : syracuseStep 7898419 = 11847629) B11847629
theorem B3286331 : Blo 1459549 3286331 := bstep (se 1 (by rfl) ⟨2464748, by rfl⟩ : syracuseStep 3286331 = 4929497) B4929497
theorem B1459591 : Blo 1459549 1459591 := bstep (se 1 (by rfl) ⟨1094693, by rfl⟩ : syracuseStep 1459591 = 2189387) B2189387
theorem B1459599 : Blo 1459549 1459599 := bstep (se 1 (by rfl) ⟨1094699, by rfl⟩ : syracuseStep 1459599 = 2189399) B2189399
theorem B3507641 : Blo 1459549 3507641 := bstep (se 2 (by rfl) ⟨1315365, by rfl⟩ : syracuseStep 3507641 = 2630731) B2630731
theorem B11838905 : Blo 1459549 11838905 := bstep (se 2 (by rfl) ⟨4439589, by rfl⟩ : syracuseStep 11838905 = 8879179) B8879179
theorem B1459643 : Blo 1459549 1459643 := bstep (se 1 (by rfl) ⟨1094732, by rfl⟩ : syracuseStep 1459643 = 2189465) B2189465
theorem B1754555 : Blo 1459549 1754555 := bstep (se 1 (by rfl) ⟨1315916, by rfl⟩ : syracuseStep 1754555 = 2631833) B2631833
theorem B3286457 : Blo 1459549 3286457 := bstep (se 2 (by rfl) ⟨1232421, by rfl⟩ : syracuseStep 3286457 = 2464843) B2464843
theorem B2631113 : Blo 1459549 2631113 := bstep (se 2 (by rfl) ⟨986667, by rfl⟩ : syracuseStep 2631113 = 1973335) B1973335
theorem B1459719 : Blo 1459549 1459719 := bstep (se 1 (by rfl) ⟨1094789, by rfl⟩ : syracuseStep 1459719 = 2189579) B2189579
theorem B1459727 : Blo 1459549 1459727 := bstep (se 1 (by rfl) ⟨1094795, by rfl⟩ : syracuseStep 1459727 = 2189591) B2189591
theorem B7390763 : Blo 1459549 7390763 := bstep (se 1 (by rfl) ⟨5543072, by rfl⟩ : syracuseStep 7390763 = 11086145) B11086145
theorem B1459771 : Blo 1459549 1459771 := bstep (se 1 (by rfl) ⟨1094828, by rfl⟩ : syracuseStep 1459771 = 2189657) B2189657
theorem B1459847 : Blo 1459549 1459847 := bstep (se 1 (by rfl) ⟨1094885, by rfl⟩ : syracuseStep 1459847 = 2189771) B2189771
theorem B3696263 : Blo 1459549 3696263 := bstep (se 1 (by rfl) ⟨2772197, by rfl⟩ : syracuseStep 3696263 = 5544395) B5544395
theorem B1459855 : Blo 1459549 1459855 := bstep (se 1 (by rfl) ⟨1094891, by rfl⟩ : syracuseStep 1459855 = 2189783) B2189783
theorem B3696313 : Blo 1459549 3696313 := bstep (se 2 (by rfl) ⟨1386117, by rfl⟩ : syracuseStep 3696313 = 2772235) B2772235
theorem B1459899 : Blo 1459549 1459899 := bstep (se 1 (by rfl) ⟨1094924, by rfl⟩ : syracuseStep 1459899 = 2189849) B2189849
theorem B1459975 : Blo 1459549 1459975 := bstep (se 1 (by rfl) ⟨1094981, by rfl⟩ : syracuseStep 1459975 = 2189963) B2189963
theorem B1459983 : Blo 1459549 1459983 := bstep (se 1 (by rfl) ⟨1094987, by rfl⟩ : syracuseStep 1459983 = 2189975) B2189975
theorem B3286799 : Blo 1459549 3286799 := bstep (se 1 (by rfl) ⟨2465099, by rfl⟩ : syracuseStep 3286799 = 4930199) B4930199
theorem B3286817 : Blo 1459549 3286817 := bstep (se 2 (by rfl) ⟨1232556, by rfl⟩ : syracuseStep 3286817 = 2465113) B2465113
theorem B13690673 : Blo 1459549 13690673 := bstep (se 2 (by rfl) ⟨5134002, by rfl⟩ : syracuseStep 13690673 = 10268005) B10268005
theorem B1460027 : Blo 1459549 1460027 := bstep (se 1 (by rfl) ⟨1095020, by rfl⟩ : syracuseStep 1460027 = 2190041) B2190041
theorem B3508055 : Blo 1459549 3508055 := bstep (se 1 (by rfl) ⟨2631041, by rfl⟩ : syracuseStep 3508055 = 5262083) B5262083
theorem B3508103 : Blo 1459549 3508103 := bstep (se 1 (by rfl) ⟨2631077, by rfl⟩ : syracuseStep 3508103 = 5262155) B5262155
theorem B1460103 : Blo 1459549 1460103 := bstep (se 1 (by rfl) ⟨1095077, by rfl⟩ : syracuseStep 1460103 = 2190155) B2190155
theorem B1460111 : Blo 1459549 1460111 := bstep (se 1 (by rfl) ⟨1095083, by rfl⟩ : syracuseStep 1460111 = 2190167) B2190167
theorem B2000783 : Blo 1459549 2000783 := bstep (se 1 (by rfl) ⟨1500587, by rfl⟩ : syracuseStep 2000783 = 3001175) B3001175
theorem B1460155 : Blo 1459549 1460155 := bstep (se 1 (by rfl) ⟨1095116, by rfl⟩ : syracuseStep 1460155 = 2190233) B2190233
theorem B2107337 : Blo 1459549 2107337 := bstep (se 2 (by rfl) ⟨790251, by rfl⟩ : syracuseStep 2107337 = 1580503) B1580503
theorem B1460231 : Blo 1459549 1460231 := bstep (se 1 (by rfl) ⟨1095173, by rfl⟩ : syracuseStep 1460231 = 2190347) B2190347
theorem B12478475 : Blo 1459549 12478475 := bstep (se 1 (by rfl) ⟨9358856, by rfl⟩ : syracuseStep 12478475 = 18717713) B18717713
theorem B2189327 : Blo 1459549 2189327 := bstep (se 1 (by rfl) ⟨1641995, by rfl⟩ : syracuseStep 2189327 = 3283991) B3283991
theorem B1460239 : Blo 1459549 1460239 := bstep (se 1 (by rfl) ⟨1095179, by rfl⟩ : syracuseStep 1460239 = 2190359) B2190359
theorem B1755151 : Blo 1459549 1755151 := bstep (se 1 (by rfl) ⟨1316363, by rfl⟩ : syracuseStep 1755151 = 2632727) B2632727
theorem B2189369 : Blo 1459549 2189369 := bstep (se 2 (by rfl) ⟨821013, by rfl⟩ : syracuseStep 2189369 = 1642027) B1642027
theorem B1460283 : Blo 1459549 1460283 := bstep (se 1 (by rfl) ⟨1095212, by rfl⟩ : syracuseStep 1460283 = 2190425) B2190425
theorem B3287159 : Blo 1459549 3287159 := bstep (se 1 (by rfl) ⟨2465369, by rfl⟩ : syracuseStep 3287159 = 4930739) B4930739
theorem B2189447 : Blo 1459549 2189447 := bstep (se 1 (by rfl) ⟨1642085, by rfl⟩ : syracuseStep 2189447 = 3284171) B3284171
theorem B1460359 : Blo 1459549 1460359 := bstep (se 1 (by rfl) ⟨1095269, by rfl⟩ : syracuseStep 1460359 = 2190539) B2190539
theorem B1460367 : Blo 1459549 1460367 := bstep (se 1 (by rfl) ⟨1095275, by rfl⟩ : syracuseStep 1460367 = 2190551) B2190551
theorem B2631827 : Blo 1459549 2631827 := bstep (se 1 (by rfl) ⟨1973870, by rfl⟩ : syracuseStep 2631827 = 3947741) B3947741
theorem B2189483 : Blo 1459549 2189483 := bstep (se 1 (by rfl) ⟨1642112, by rfl⟩ : syracuseStep 2189483 = 3284225) B3284225
theorem B1460411 : Blo 1459549 1460411 := bstep (se 1 (by rfl) ⟨1095308, by rfl⟩ : syracuseStep 1460411 = 2190617) B2190617
theorem B2189513 : Blo 1459549 2189513 := bstep (se 2 (by rfl) ⟨821067, by rfl⟩ : syracuseStep 2189513 = 1642135) B1642135
theorem B5130497 : Blo 1459549 5130497 := bstep (se 2 (by rfl) ⟨1923936, by rfl⟩ : syracuseStep 5130497 = 3847873) B3847873
theorem B1460487 : Blo 1459549 1460487 := bstep (se 1 (by rfl) ⟨1095365, by rfl⟩ : syracuseStep 1460487 = 2190731) B2190731
theorem B1460495 : Blo 1459549 1460495 := bstep (se 1 (by rfl) ⟨1095371, by rfl⟩ : syracuseStep 1460495 = 2190743) B2190743
theorem B3696911 : Blo 1459549 3696911 := bstep (se 1 (by rfl) ⟨2772683, by rfl⟩ : syracuseStep 3696911 = 5545367) B5545367
theorem B3287339 : Blo 1459549 3287339 := bstep (se 1 (by rfl) ⟨2465504, by rfl⟩ : syracuseStep 3287339 = 4931009) B4931009
theorem B2189627 : Blo 1459549 2189627 := bstep (se 1 (by rfl) ⟨1642220, by rfl⟩ : syracuseStep 2189627 = 3284441) B3284441
theorem B1460539 : Blo 1459549 1460539 := bstep (se 1 (by rfl) ⟨1095404, by rfl⟩ : syracuseStep 1460539 = 2190809) B2190809
theorem B2189687 : Blo 1459549 2189687 := bstep (se 1 (by rfl) ⟨1642265, by rfl⟩ : syracuseStep 2189687 = 3284531) B3284531
theorem B1460615 : Blo 1459549 1460615 := bstep (se 1 (by rfl) ⟨1095461, by rfl⟩ : syracuseStep 1460615 = 2190923) B2190923
theorem B11094407 : Blo 1459549 11094407 := bstep (se 1 (by rfl) ⟨8320805, by rfl⟩ : syracuseStep 11094407 = 16641611) B16641611
theorem B2189711 : Blo 1459549 2189711 := bstep (se 1 (by rfl) ⟨1642283, by rfl⟩ : syracuseStep 2189711 = 3284567) B3284567
theorem B1460623 : Blo 1459549 1460623 := bstep (se 1 (by rfl) ⟨1095467, by rfl⟩ : syracuseStep 1460623 = 2190935) B2190935
theorem B2771347 : Blo 1459549 2771347 := bstep (se 1 (by rfl) ⟨2078510, by rfl⟩ : syracuseStep 2771347 = 4157021) B4157021
theorem B2189753 : Blo 1459549 2189753 := bstep (se 2 (by rfl) ⟨821157, by rfl⟩ : syracuseStep 2189753 = 1642315) B1642315
theorem B1460667 : Blo 1459549 1460667 := bstep (se 1 (by rfl) ⟨1095500, by rfl⟩ : syracuseStep 1460667 = 2191001) B2191001
theorem B2189831 : Blo 1459549 2189831 := bstep (se 1 (by rfl) ⟨1642373, by rfl⟩ : syracuseStep 2189831 = 3284747) B3284747
theorem B1460743 : Blo 1459549 1460743 := bstep (se 1 (by rfl) ⟨1095557, by rfl⟩ : syracuseStep 1460743 = 2191115) B2191115
theorem B1460751 : Blo 1459549 1460751 := bstep (se 1 (by rfl) ⟨1095563, by rfl⟩ : syracuseStep 1460751 = 2191127) B2191127
theorem B2189867 : Blo 1459549 2189867 := bstep (se 1 (by rfl) ⟨1642400, by rfl⟩ : syracuseStep 2189867 = 3284801) B3284801
theorem B1460795 : Blo 1459549 1460795 := bstep (se 1 (by rfl) ⟨1095596, by rfl⟩ : syracuseStep 1460795 = 2191193) B2191193
theorem B2189897 : Blo 1459549 2189897 := bstep (se 2 (by rfl) ⟨821211, by rfl⟩ : syracuseStep 2189897 = 1642423) B1642423
theorem B7015031 : Blo 1459549 7015031 := bstep (se 1 (by rfl) ⟨5261273, by rfl⟩ : syracuseStep 7015031 = 10522547) B10522547
theorem B1460871 : Blo 1459549 1460871 := bstep (se 1 (by rfl) ⟨1095653, by rfl⟩ : syracuseStep 1460871 = 2191307) B2191307
theorem B1460879 : Blo 1459549 1460879 := bstep (se 1 (by rfl) ⟨1095659, by rfl⟩ : syracuseStep 1460879 = 2191319) B2191319
theorem B2190011 : Blo 1459549 2190011 := bstep (se 1 (by rfl) ⟨1642508, by rfl⟩ : syracuseStep 2190011 = 3285017) B3285017
theorem B1460923 : Blo 1459549 1460923 := bstep (se 1 (by rfl) ⟨1095692, by rfl⟩ : syracuseStep 1460923 = 2191385) B2191385
theorem B2190071 : Blo 1459549 2190071 := bstep (se 1 (by rfl) ⟨1642553, by rfl⟩ : syracuseStep 2190071 = 3285107) B3285107
theorem B1460999 : Blo 1459549 1460999 := bstep (se 1 (by rfl) ⟨1095749, by rfl⟩ : syracuseStep 1460999 = 2191499) B2191499
theorem B2190095 : Blo 1459549 2190095 := bstep (se 1 (by rfl) ⟨1642571, by rfl⟩ : syracuseStep 2190095 = 3285143) B3285143
theorem B1461007 : Blo 1459549 1461007 := bstep (se 1 (by rfl) ⟨1095755, by rfl⟩ : syracuseStep 1461007 = 2191511) B2191511
theorem B2190137 : Blo 1459549 2190137 := bstep (se 2 (by rfl) ⟨821301, by rfl⟩ : syracuseStep 2190137 = 1642603) B1642603
theorem B7392059 : Blo 1459549 7392059 := bstep (se 1 (by rfl) ⟨5544044, by rfl⟩ : syracuseStep 7392059 = 11088089) B11088089
theorem B2190215 : Blo 1459549 2190215 := bstep (se 1 (by rfl) ⟨1642661, by rfl⟩ : syracuseStep 2190215 = 3285323) B3285323
theorem B2632583 : Blo 1459549 2632583 := bstep (se 1 (by rfl) ⟨1974437, by rfl⟩ : syracuseStep 2632583 = 3948875) B3948875
theorem B2190251 : Blo 1459549 2190251 := bstep (se 1 (by rfl) ⟨1642688, by rfl⟩ : syracuseStep 2190251 = 3285377) B3285377
theorem B2190281 : Blo 1459549 2190281 := bstep (se 2 (by rfl) ⟨821355, by rfl⟩ : syracuseStep 2190281 = 1642711) B1642711
theorem B3697609 : Blo 1459549 3697609 := bstep (se 2 (by rfl) ⟨1386603, by rfl⟩ : syracuseStep 3697609 = 2773207) B2773207
theorem B7392221 : Blo 1459549 7392221 := bstep (se 3 (by rfl) ⟨1386041, by rfl⟩ : syracuseStep 7392221 = 2772083) B2772083
theorem B2190395 : Blo 1459549 2190395 := bstep (se 1 (by rfl) ⟨1642796, by rfl⟩ : syracuseStep 2190395 = 3285593) B3285593
theorem B3697751 : Blo 1459549 3697751 := bstep (se 1 (by rfl) ⟨2773313, by rfl⟩ : syracuseStep 3697751 = 5546627) B5546627
theorem B2190455 : Blo 1459549 2190455 := bstep (se 1 (by rfl) ⟨1642841, by rfl⟩ : syracuseStep 2190455 = 3285683) B3285683
theorem B2190479 : Blo 1459549 2190479 := bstep (se 1 (by rfl) ⟨1642859, by rfl⟩ : syracuseStep 2190479 = 3285719) B3285719
theorem B2190521 : Blo 1459549 2190521 := bstep (se 2 (by rfl) ⟨821445, by rfl⟩ : syracuseStep 2190521 = 1642891) B1642891
theorem B23678189 : Blo 1459549 23678189 := bstep (se 3 (by rfl) ⟨4439660, by rfl⟩ : syracuseStep 23678189 = 8879321) B8879321
theorem B2190599 : Blo 1459549 2190599 := bstep (se 1 (by rfl) ⟨1642949, by rfl⟩ : syracuseStep 2190599 = 3285899) B3285899
theorem B7392545 : Blo 1459549 7392545 := bstep (se 2 (by rfl) ⟨2772204, by rfl⟩ : syracuseStep 7392545 = 5544409) B5544409
theorem B2190635 : Blo 1459549 2190635 := bstep (se 1 (by rfl) ⟨1642976, by rfl⟩ : syracuseStep 2190635 = 3285953) B3285953
theorem B2190665 : Blo 1459549 2190665 := bstep (se 2 (by rfl) ⟨821499, by rfl⟩ : syracuseStep 2190665 = 1642999) B1642999
theorem B4926905 : Blo 1459549 4926905 := bstep (se 2 (by rfl) ⟨1847589, by rfl⟩ : syracuseStep 4926905 = 3695179) B3695179
theorem B2190779 : Blo 1459549 2190779 := bstep (se 1 (by rfl) ⟨1643084, by rfl⟩ : syracuseStep 2190779 = 3286169) B3286169
theorem B21048781 : Blo 1459549 21048781 := bstep (se 3 (by rfl) ⟨3946646, by rfl⟩ : syracuseStep 21048781 = 7893293) B7893293
theorem B2190839 : Blo 1459549 2190839 := bstep (se 1 (by rfl) ⟨1643129, by rfl⟩ : syracuseStep 2190839 = 3286259) B3286259
theorem B2190863 : Blo 1459549 2190863 := bstep (se 1 (by rfl) ⟨1643147, by rfl⟩ : syracuseStep 2190863 = 3286295) B3286295
theorem B2190905 : Blo 1459549 2190905 := bstep (se 2 (by rfl) ⟨821589, by rfl⟩ : syracuseStep 2190905 = 1643179) B1643179
theorem B2772539 : Blo 1459549 2772539 := bstep (se 1 (by rfl) ⟨2079404, by rfl⟩ : syracuseStep 2772539 = 4158809) B4158809
theorem B2190983 : Blo 1459549 2190983 := bstep (se 1 (by rfl) ⟨1643237, by rfl⟩ : syracuseStep 2190983 = 3286475) B3286475
theorem B2191019 : Blo 1459549 2191019 := bstep (se 1 (by rfl) ⟨1643264, by rfl⟩ : syracuseStep 2191019 = 3286529) B3286529
theorem B1642171 : Blo 1459549 1642171 := bstep (se 1 (by rfl) ⟨1231628, by rfl⟩ : syracuseStep 1642171 = 2463257) B2463257
theorem B2191049 : Blo 1459549 2191049 := bstep (se 2 (by rfl) ⟨821643, by rfl⟩ : syracuseStep 2191049 = 1643287) B1643287
theorem B2191163 : Blo 1459549 2191163 := bstep (se 1 (by rfl) ⟨1643372, by rfl⟩ : syracuseStep 2191163 = 3286745) B3286745
theorem B2191223 : Blo 1459549 2191223 := bstep (se 1 (by rfl) ⟨1643417, by rfl⟩ : syracuseStep 2191223 = 3286835) B3286835
theorem B5541767 : Blo 1459549 5541767 := bstep (se 1 (by rfl) ⟨4156325, by rfl⟩ : syracuseStep 5541767 = 8312651) B8312651
theorem B2191247 : Blo 1459549 2191247 := bstep (se 1 (by rfl) ⟨1643435, by rfl⟩ : syracuseStep 2191247 = 3286871) B3286871
theorem B2961299 : Blo 1459549 2961299 := bstep (se 1 (by rfl) ⟨2220974, by rfl⟩ : syracuseStep 2961299 = 4441949) B4441949
theorem B2191289 : Blo 1459549 2191289 := bstep (se 2 (by rfl) ⟨821733, by rfl⟩ : syracuseStep 2191289 = 1643467) B1643467
theorem B2191367 : Blo 1459549 2191367 := bstep (se 1 (by rfl) ⟨1643525, by rfl⟩ : syracuseStep 2191367 = 3287051) B3287051
theorem B4927499 : Blo 1459549 4927499 := bstep (se 1 (by rfl) ⟨3695624, by rfl⟩ : syracuseStep 4927499 = 7391249) B7391249
theorem B109555733 : Blo 1459549 109555733 := bstep (se 6 (by rfl) ⟨2567712, by rfl⟩ : syracuseStep 109555733 = 5135425) B5135425
theorem B2773025 : Blo 1459549 2773025 := bstep (se 2 (by rfl) ⟨1039884, by rfl⟩ : syracuseStep 2773025 = 2079769) B2079769
theorem B2191403 : Blo 1459549 2191403 := bstep (se 1 (by rfl) ⟨1643552, by rfl⟩ : syracuseStep 2191403 = 3287105) B3287105
theorem B2191433 : Blo 1459549 2191433 := bstep (se 2 (by rfl) ⟨821787, by rfl⟩ : syracuseStep 2191433 = 1643575) B1643575
theorem B4927607 : Blo 1459549 4927607 := bstep (se 1 (by rfl) ⟨3695705, by rfl⟩ : syracuseStep 4927607 = 7391411) B7391411
theorem B1642639 : Blo 1459549 1642639 := bstep (se 1 (by rfl) ⟨1231979, by rfl⟩ : syracuseStep 1642639 = 2463959) B2463959
theorem B2191547 : Blo 1459549 2191547 := bstep (se 1 (by rfl) ⟨1643660, by rfl⟩ : syracuseStep 2191547 = 3287321) B3287321
theorem B7393517 : Blo 1459549 7393517 := bstep (se 3 (by rfl) ⟨1386284, by rfl⟩ : syracuseStep 7393517 = 2772569) B2772569
theorem B2773291 : Blo 1459549 2773291 := bstep (se 1 (by rfl) ⟨2079968, by rfl⟩ : syracuseStep 2773291 = 4159937) B4159937
theorem B4993415 : Blo 1459549 4993415 := bstep (se 1 (by rfl) ⟨3745061, by rfl⟩ : syracuseStep 4993415 = 7490123) B7490123
theorem B16634321 : Blo 1459549 16634321 := bstep (se 2 (by rfl) ⟨6237870, by rfl⟩ : syracuseStep 16634321 = 12475741) B12475741
theorem B1643143 : Blo 1459549 1643143 := bstep (se 1 (by rfl) ⟨1232357, by rfl⟩ : syracuseStep 1643143 = 2464715) B2464715
theorem B4928201 : Blo 1459549 4928201 := bstep (se 2 (by rfl) ⟨1848075, by rfl⟩ : syracuseStep 4928201 = 3696151) B3696151
theorem B1643323 : Blo 1459549 1643323 := bstep (se 1 (by rfl) ⟨1232492, by rfl⟩ : syracuseStep 1643323 = 2464985) B2464985
theorem B5264243 : Blo 1459549 5264243 := bstep (se 1 (by rfl) ⟨3948182, by rfl⟩ : syracuseStep 5264243 = 7896365) B7896365
theorem B4158479 : Blo 1459549 4158479 := bstep (se 1 (by rfl) ⟨3118859, by rfl⟩ : syracuseStep 4158479 = 6237719) B6237719
theorem B7394327 : Blo 1459549 7394327 := bstep (se 1 (by rfl) ⟨5545745, by rfl⟩ : syracuseStep 7394327 = 11091491) B11091491
theorem B33723479 : Blo 1459549 33723479 := bstep (se 1 (by rfl) ⟨25292609, by rfl⟩ : syracuseStep 33723479 = 50585219) B50585219
theorem B3945673 : Blo 1459549 3945673 := bstep (se 2 (by rfl) ⟨1479627, by rfl⟩ : syracuseStep 3945673 = 2959255) B2959255
theorem B1602875 : Blo 1459549 1602875 := bstep (se 1 (by rfl) ⟨1202156, by rfl⟩ : syracuseStep 1602875 = 2404313) B2404313
theorem B2463095 : Blo 1459549 2463095 := bstep (se 1 (by rfl) ⟨1847321, by rfl⟩ : syracuseStep 2463095 = 3694643) B3694643
theorem B4928903 : Blo 1459549 4928903 := bstep (se 1 (by rfl) ⟨3696677, by rfl⟩ : syracuseStep 4928903 = 7393355) B7393355
theorem B8320441 : Blo 1459549 8320441 := bstep (se 2 (by rfl) ⟨3120165, by rfl⟩ : syracuseStep 8320441 = 6240331) B6240331
theorem B11236907 : Blo 1459549 11236907 := bstep (se 1 (by rfl) ⟨8427680, by rfl⟩ : syracuseStep 11236907 = 16855361) B16855361
theorem B14038595 : Blo 1459549 14038595 := bstep (se 1 (by rfl) ⟨10528946, by rfl⟩ : syracuseStep 14038595 = 21057893) B21057893
theorem B7894721 : Blo 1459549 7894721 := bstep (se 2 (by rfl) ⟨2960520, by rfl⟩ : syracuseStep 7894721 = 5921041) B5921041
theorem B4929281 : Blo 1459549 4929281 := bstep (se 2 (by rfl) ⟨1848480, by rfl⟩ : syracuseStep 4929281 = 3696961) B3696961
theorem B2463547 : Blo 1459549 2463547 := bstep (se 1 (by rfl) ⟨1847660, by rfl⟩ : syracuseStep 2463547 = 3695321) B3695321
theorem B5855161 : Blo 1459549 5855161 := bstep (se 2 (by rfl) ⟨2195685, by rfl⟩ : syracuseStep 5855161 = 4391371) B4391371
theorem B2463689 : Blo 1459549 2463689 := bstep (se 2 (by rfl) ⟨923883, by rfl⟩ : syracuseStep 2463689 = 1847767) B1847767
theorem B6658109 : Blo 1459549 6658109 := bstep (se 3 (by rfl) ⟨1248395, by rfl⟩ : syracuseStep 6658109 = 2496791) B2496791
theorem B2250871 : Blo 1459549 2250871 := bstep (se 1 (by rfl) ⟨1688153, by rfl⟩ : syracuseStep 2250871 = 3376307) B3376307
theorem B2078983 : Blo 1459549 2078983 := bstep (se 1 (by rfl) ⟨1559237, by rfl⟩ : syracuseStep 2078983 = 3118475) B3118475
theorem B15997319 : Blo 1459549 15997319 := bstep (se 1 (by rfl) ⟨11997989, by rfl⟩ : syracuseStep 15997319 = 23995979) B23995979
theorem B7018973 : Blo 1459549 7018973 := bstep (se 3 (by rfl) ⟨1316057, by rfl⟩ : syracuseStep 7018973 = 2632115) B2632115
theorem B9353731 : Blo 1459549 9353731 := bstep (se 1 (by rfl) ⟨7015298, by rfl⟩ : syracuseStep 9353731 = 14030597) B14030597
theorem B4930091 : Blo 1459549 4930091 := bstep (se 1 (by rfl) ⟨3697568, by rfl⟩ : syracuseStep 4930091 = 7395137) B7395137
theorem B4160119 : Blo 1459549 4160119 := bstep (se 1 (by rfl) ⟨3120089, by rfl⟩ : syracuseStep 4160119 = 6240179) B6240179
theorem B2464391 : Blo 1459549 2464391 := bstep (se 1 (by rfl) ⟨1848293, by rfl⟩ : syracuseStep 2464391 = 3696587) B3696587
theorem B4160153 : Blo 1459549 4160153 := bstep (se 2 (by rfl) ⟨1560057, by rfl⟩ : syracuseStep 4160153 = 3120115) B3120115
theorem B4160267 : Blo 1459549 4160267 := bstep (se 1 (by rfl) ⟨3120200, by rfl⟩ : syracuseStep 4160267 = 6240401) B6240401
theorem B4438813 : Blo 1459549 4438813 := bstep (se 3 (by rfl) ⟨832277, by rfl⟩ : syracuseStep 4438813 = 1664555) B1664555
theorem B8879033 : Blo 1459549 8879033 := bstep (se 2 (by rfl) ⟨3329637, by rfl⟩ : syracuseStep 8879033 = 6659275) B6659275
theorem B4389833 : Blo 1459549 4389833 := bstep (se 2 (by rfl) ⟨1646187, by rfl⟩ : syracuseStep 4389833 = 3292375) B3292375
theorem B9993239 : Blo 1459549 9993239 := bstep (se 1 (by rfl) ⟨7494929, by rfl⟩ : syracuseStep 9993239 = 14989859) B14989859
theorem B3284027 : Blo 1459549 3284027 := bstep (se 1 (by rfl) ⟨2463020, by rfl⟩ : syracuseStep 3284027 = 4926041) B4926041
theorem B2079803 : Blo 1459549 2079803 := bstep (se 1 (by rfl) ⟨1559852, by rfl⟩ : syracuseStep 2079803 = 3119705) B3119705
theorem B21044285 : Blo 1459549 21044285 := bstep (se 3 (by rfl) ⟨3945803, by rfl⟩ : syracuseStep 21044285 = 7891607) B7891607
theorem B11091005 : Blo 1459549 11091005 := bstep (se 3 (by rfl) ⟨2079563, by rfl⟩ : syracuseStep 11091005 = 4159127) B4159127
theorem B3161207 : Blo 1459549 3161207 := bstep (se 1 (by rfl) ⟨2370905, by rfl⟩ : syracuseStep 3161207 = 4741811) B4741811
theorem B63143063 : Blo 1459549 63143063 := bstep (se 1 (by rfl) ⟨47357297, by rfl⟩ : syracuseStep 63143063 = 94714595) B94714595
theorem B3284153 : Blo 1459549 3284153 := bstep (se 2 (by rfl) ⟨1231557, by rfl⟩ : syracuseStep 3284153 = 2463115) B2463115
theorem B2465039 : Blo 1459549 2465039 := bstep (se 1 (by rfl) ⟨1848779, by rfl⟩ : syracuseStep 2465039 = 3697559) B3697559
theorem B2080247 : Blo 1459549 2080247 := bstep (se 1 (by rfl) ⟨1560185, by rfl⟩ : syracuseStep 2080247 = 3120371) B3120371
theorem B3284495 : Blo 1459549 3284495 := bstep (se 1 (by rfl) ⟨2463371, by rfl⟩ : syracuseStep 3284495 = 4926743) B4926743
theorem B10526237 : Blo 1459549 10526237 := bstep (se 3 (by rfl) ⟨1973669, by rfl⟩ : syracuseStep 10526237 = 3947339) B3947339
theorem B3284513 : Blo 1459549 3284513 := bstep (se 2 (by rfl) ⟨1231692, by rfl⟩ : syracuseStep 3284513 = 2463385) B2463385
theorem B17997389 : Blo 1459549 17997389 := bstep (se 3 (by rfl) ⟨3374510, by rfl⟩ : syracuseStep 17997389 = 6749021) B6749021
theorem B3284855 : Blo 1459549 3284855 := bstep (se 1 (by rfl) ⟨2463641, by rfl⟩ : syracuseStep 3284855 = 4927283) B4927283
theorem B3284999 : Blo 1459549 3284999 := bstep (se 1 (by rfl) ⟨2463749, by rfl⟩ : syracuseStep 3284999 = 4927499) B4927499
theorem B3285071 : Blo 1459549 3285071 := bstep (se 1 (by rfl) ⟨2463803, by rfl⟩ : syracuseStep 3285071 = 4927607) B4927607
theorem B5546141 : Blo 1459549 5546141 := bstep (se 3 (by rfl) ⟨1039901, by rfl⟩ : syracuseStep 5546141 = 2079803) B2079803
theorem B3285467 : Blo 1459549 3285467 := bstep (se 1 (by rfl) ⟨2464100, by rfl⟩ : syracuseStep 3285467 = 4928201) B4928201
theorem B3695129 : Blo 1459549 3695129 := bstep (se 2 (by rfl) ⟨1385673, by rfl⟩ : syracuseStep 3695129 = 2771347) B2771347
theorem B13681325 : Blo 1459549 13681325 := bstep (se 3 (by rfl) ⟨2565248, by rfl⟩ : syracuseStep 13681325 = 5130497) B5130497
theorem B3556055 : Blo 1459549 3556055 := bstep (se 1 (by rfl) ⟨2667041, by rfl⟩ : syracuseStep 3556055 = 5334083) B5334083
theorem B5620547 : Blo 1459549 5620547 := bstep (se 1 (by rfl) ⟨4215410, by rfl⟩ : syracuseStep 5620547 = 8430821) B8430821
theorem B5546825 : Blo 1459549 5546825 := bstep (se 2 (by rfl) ⟨2080059, by rfl⟩ : syracuseStep 5546825 = 4160119) B4160119
theorem B3285935 : Blo 1459549 3285935 := bstep (se 1 (by rfl) ⟨2464451, by rfl⟩ : syracuseStep 3285935 = 4928903) B4928903
theorem B1754075 : Blo 1459549 1754075 := bstep (se 1 (by rfl) ⟨1315556, by rfl⟩ : syracuseStep 1754075 = 2631113) B2631113
theorem B4678813 : Blo 1459549 4678813 := bstep (se 3 (by rfl) ⟨877277, by rfl⟩ : syracuseStep 4678813 = 1754555) B1754555
theorem B3286187 : Blo 1459549 3286187 := bstep (se 1 (by rfl) ⟨2464640, by rfl⟩ : syracuseStep 3286187 = 4929281) B4929281
theorem B9127115 : Blo 1459549 9127115 := bstep (se 1 (by rfl) ⟨6845336, by rfl⟩ : syracuseStep 9127115 = 13690673) B13690673
theorem B5547325 : Blo 1459549 5547325 := bstep (se 3 (by rfl) ⟨1040123, by rfl⟩ : syracuseStep 5547325 = 2080247) B2080247
theorem B1459551 : Blo 1459549 1459551 := bstep (se 1 (by rfl) ⟨1094663, by rfl⟩ : syracuseStep 1459551 = 2189327) B2189327
theorem B1459579 : Blo 1459549 1459579 := bstep (se 1 (by rfl) ⟨1094684, by rfl⟩ : syracuseStep 1459579 = 2189369) B2189369
theorem B1459631 : Blo 1459549 1459631 := bstep (se 1 (by rfl) ⟨1094723, by rfl⟩ : syracuseStep 1459631 = 2189447) B2189447
theorem B1754551 : Blo 1459549 1754551 := bstep (se 1 (by rfl) ⟨1315913, by rfl⟩ : syracuseStep 1754551 = 2631827) B2631827
theorem B1459655 : Blo 1459549 1459655 := bstep (se 1 (by rfl) ⟨1094741, by rfl⟩ : syracuseStep 1459655 = 2189483) B2189483
theorem B1459675 : Blo 1459549 1459675 := bstep (se 1 (by rfl) ⟨1094756, by rfl⟩ : syracuseStep 1459675 = 2189513) B2189513
theorem B1459751 : Blo 1459549 1459751 := bstep (se 1 (by rfl) ⟨1094813, by rfl⟩ : syracuseStep 1459751 = 2189627) B2189627
theorem B1459791 : Blo 1459549 1459791 := bstep (se 1 (by rfl) ⟨1094843, by rfl⟩ : syracuseStep 1459791 = 2189687) B2189687
theorem B1459807 : Blo 1459549 1459807 := bstep (se 1 (by rfl) ⟨1094855, by rfl⟩ : syracuseStep 1459807 = 2189711) B2189711
theorem B5260897 : Blo 1459549 5260897 := bstep (se 2 (by rfl) ⟨1972836, by rfl⟩ : syracuseStep 5260897 = 3945673) B3945673
theorem B1459835 : Blo 1459549 1459835 := bstep (se 1 (by rfl) ⟨1094876, by rfl⟩ : syracuseStep 1459835 = 2189753) B2189753
theorem B4679315 : Blo 1459549 4679315 := bstep (se 1 (by rfl) ⟨3509486, by rfl⟩ : syracuseStep 4679315 = 7018973) B7018973
theorem B1459887 : Blo 1459549 1459887 := bstep (se 1 (by rfl) ⟨1094915, by rfl⟩ : syracuseStep 1459887 = 2189831) B2189831
theorem B1459911 : Blo 1459549 1459911 := bstep (se 1 (by rfl) ⟨1094933, by rfl⟩ : syracuseStep 1459911 = 2189867) B2189867
theorem B3286727 : Blo 1459549 3286727 := bstep (se 1 (by rfl) ⟨2465045, by rfl⟩ : syracuseStep 3286727 = 4930091) B4930091
theorem B1459931 : Blo 1459549 1459931 := bstep (se 1 (by rfl) ⟨1094948, by rfl⟩ : syracuseStep 1459931 = 2189897) B2189897
theorem B1460007 : Blo 1459549 1460007 := bstep (se 1 (by rfl) ⟨1095005, by rfl⟩ : syracuseStep 1460007 = 2190011) B2190011
theorem B1460047 : Blo 1459549 1460047 := bstep (se 1 (by rfl) ⟨1095035, by rfl⟩ : syracuseStep 1460047 = 2190071) B2190071
theorem B1460063 : Blo 1459549 1460063 := bstep (se 1 (by rfl) ⟨1095047, by rfl⟩ : syracuseStep 1460063 = 2190095) B2190095
theorem B1460091 : Blo 1459549 1460091 := bstep (se 1 (by rfl) ⟨1095068, by rfl⟩ : syracuseStep 1460091 = 2190137) B2190137
theorem B11093921 : Blo 1459549 11093921 := bstep (se 2 (by rfl) ⟨4160220, by rfl⟩ : syracuseStep 11093921 = 8320441) B8320441
theorem B1460143 : Blo 1459549 1460143 := bstep (se 1 (by rfl) ⟨1095107, by rfl⟩ : syracuseStep 1460143 = 2190215) B2190215
theorem B1755055 : Blo 1459549 1755055 := bstep (se 1 (by rfl) ⟨1316291, by rfl⟩ : syracuseStep 1755055 = 2632583) B2632583
theorem B1460167 : Blo 1459549 1460167 := bstep (se 1 (by rfl) ⟨1095125, by rfl⟩ : syracuseStep 1460167 = 2190251) B2190251
theorem B1460187 : Blo 1459549 1460187 := bstep (se 1 (by rfl) ⟨1095140, by rfl⟩ : syracuseStep 1460187 = 2190281) B2190281
theorem B6662159 : Blo 1459549 6662159 := bstep (se 1 (by rfl) ⟨4996619, by rfl⟩ : syracuseStep 6662159 = 9993239) B9993239
theorem B2189351 : Blo 1459549 2189351 := bstep (se 1 (by rfl) ⟨1642013, by rfl⟩ : syracuseStep 2189351 = 3284027) B3284027
theorem B1460263 : Blo 1459549 1460263 := bstep (se 1 (by rfl) ⟨1095197, by rfl⟩ : syracuseStep 1460263 = 2190395) B2190395
theorem B2107471 : Blo 1459549 2107471 := bstep (se 1 (by rfl) ⟨1580603, by rfl⟩ : syracuseStep 2107471 = 3161207) B3161207
theorem B1460303 : Blo 1459549 1460303 := bstep (se 1 (by rfl) ⟨1095227, by rfl⟩ : syracuseStep 1460303 = 2190455) B2190455
theorem B1460319 : Blo 1459549 1460319 := bstep (se 1 (by rfl) ⟨1095239, by rfl⟩ : syracuseStep 1460319 = 2190479) B2190479
theorem B2189435 : Blo 1459549 2189435 := bstep (se 1 (by rfl) ⟨1642076, by rfl⟩ : syracuseStep 2189435 = 3284153) B3284153
theorem B1460347 : Blo 1459549 1460347 := bstep (se 1 (by rfl) ⟨1095260, by rfl⟩ : syracuseStep 1460347 = 2190521) B2190521
theorem B1460399 : Blo 1459549 1460399 := bstep (se 1 (by rfl) ⟨1095299, by rfl⟩ : syracuseStep 1460399 = 2190599) B2190599
theorem B1460423 : Blo 1459549 1460423 := bstep (se 1 (by rfl) ⟨1095317, by rfl⟩ : syracuseStep 1460423 = 2190635) B2190635
theorem B1460443 : Blo 1459549 1460443 := bstep (se 1 (by rfl) ⟨1095332, by rfl⟩ : syracuseStep 1460443 = 2190665) B2190665
theorem B2189561 : Blo 1459549 2189561 := bstep (se 2 (by rfl) ⟨821085, by rfl⟩ : syracuseStep 2189561 = 1642171) B1642171
theorem B1460519 : Blo 1459549 1460519 := bstep (se 1 (by rfl) ⟨1095389, by rfl⟩ : syracuseStep 1460519 = 2190779) B2190779
theorem B1460559 : Blo 1459549 1460559 := bstep (se 1 (by rfl) ⟨1095419, by rfl⟩ : syracuseStep 1460559 = 2190839) B2190839
theorem B2189663 : Blo 1459549 2189663 := bstep (se 1 (by rfl) ⟨1642247, by rfl⟩ : syracuseStep 2189663 = 3284495) B3284495
theorem B1460575 : Blo 1459549 1460575 := bstep (se 1 (by rfl) ⟨1095431, by rfl⟩ : syracuseStep 1460575 = 2190863) B2190863
theorem B2189675 : Blo 1459549 2189675 := bstep (se 1 (by rfl) ⟨1642256, by rfl⟩ : syracuseStep 2189675 = 3284513) B3284513
theorem B1460603 : Blo 1459549 1460603 := bstep (se 1 (by rfl) ⟨1095452, by rfl⟩ : syracuseStep 1460603 = 2190905) B2190905
theorem B5335421 : Blo 1459549 5335421 := bstep (se 3 (by rfl) ⟨1000391, by rfl⟩ : syracuseStep 5335421 = 2000783) B2000783
theorem B1460655 : Blo 1459549 1460655 := bstep (se 1 (by rfl) ⟨1095491, by rfl⟩ : syracuseStep 1460655 = 2190983) B2190983
theorem B1460679 : Blo 1459549 1460679 := bstep (se 1 (by rfl) ⟨1095509, by rfl⟩ : syracuseStep 1460679 = 2191019) B2191019
theorem B1460699 : Blo 1459549 1460699 := bstep (se 1 (by rfl) ⟨1095524, by rfl⟩ : syracuseStep 1460699 = 2191049) B2191049
theorem B1460775 : Blo 1459549 1460775 := bstep (se 1 (by rfl) ⟨1095581, by rfl⟩ : syracuseStep 1460775 = 2191163) B2191163
theorem B2189903 : Blo 1459549 2189903 := bstep (se 1 (by rfl) ⟨1642427, by rfl⟩ : syracuseStep 2189903 = 3284855) B3284855
theorem B1460815 : Blo 1459549 1460815 := bstep (se 1 (by rfl) ⟨1095611, by rfl⟩ : syracuseStep 1460815 = 2191223) B2191223
theorem B1460831 : Blo 1459549 1460831 := bstep (se 1 (by rfl) ⟨1095623, by rfl⟩ : syracuseStep 1460831 = 2191247) B2191247
theorem B1460859 : Blo 1459549 1460859 := bstep (se 1 (by rfl) ⟨1095644, by rfl⟩ : syracuseStep 1460859 = 2191289) B2191289
theorem B1460911 : Blo 1459549 1460911 := bstep (se 1 (by rfl) ⟨1095683, by rfl⟩ : syracuseStep 1460911 = 2191367) B2191367
theorem B2190023 : Blo 1459549 2190023 := bstep (se 1 (by rfl) ⟨1642517, by rfl⟩ : syracuseStep 2190023 = 3285035) B3285035
theorem B1460935 : Blo 1459549 1460935 := bstep (se 1 (by rfl) ⟨1095701, by rfl⟩ : syracuseStep 1460935 = 2191403) B2191403
theorem B1460955 : Blo 1459549 1460955 := bstep (se 1 (by rfl) ⟨1095716, by rfl⟩ : syracuseStep 1460955 = 2191433) B2191433
theorem B1461031 : Blo 1459549 1461031 := bstep (se 1 (by rfl) ⟨1095773, by rfl⟩ : syracuseStep 1461031 = 2191547) B2191547
theorem B2190185 : Blo 1459549 2190185 := bstep (se 2 (by rfl) ⟨821319, by rfl⟩ : syracuseStep 2190185 = 1642639) B1642639
theorem B3328943 : Blo 1459549 3328943 := bstep (se 1 (by rfl) ⟨2496707, by rfl⟩ : syracuseStep 3328943 = 4993415) B4993415
theorem B2190263 : Blo 1459549 2190263 := bstep (se 1 (by rfl) ⟨1642697, by rfl⟩ : syracuseStep 2190263 = 3285395) B3285395
theorem B2190299 : Blo 1459549 2190299 := bstep (se 1 (by rfl) ⟨1642724, by rfl⟩ : syracuseStep 2190299 = 3285449) B3285449
theorem B2771977 : Blo 1459549 2771977 := bstep (se 2 (by rfl) ⟨1039491, by rfl⟩ : syracuseStep 2771977 = 2078983) B2078983
theorem B3697721 : Blo 1459549 3697721 := bstep (se 2 (by rfl) ⟨1386645, by rfl⟩ : syracuseStep 3697721 = 2773291) B2773291
theorem B4926635 : Blo 1459549 4926635 := bstep (se 1 (by rfl) ⟨3694976, by rfl⟩ : syracuseStep 4926635 = 7389953) B7389953
theorem B3509495 : Blo 1459549 3509495 := bstep (se 1 (by rfl) ⟨2632121, by rfl⟩ : syracuseStep 3509495 = 5264243) B5264243
theorem B12004645 : Blo 1459549 12004645 := bstep (se 4 (by rfl) ⟨1125435, by rfl⟩ : syracuseStep 12004645 = 2250871) B2250871
theorem B12471641 : Blo 1459549 12471641 := bstep (se 2 (by rfl) ⟨4676865, by rfl⟩ : syracuseStep 12471641 = 9353731) B9353731
theorem B2772319 : Blo 1459549 2772319 := bstep (se 1 (by rfl) ⟨2079239, by rfl⟩ : syracuseStep 2772319 = 4158479) B4158479
theorem B22482319 : Blo 1459549 22482319 := bstep (se 1 (by rfl) ⟨16861739, by rfl⟩ : syracuseStep 22482319 = 33723479) B33723479
theorem B2190767 : Blo 1459549 2190767 := bstep (se 1 (by rfl) ⟨1643075, by rfl⟩ : syracuseStep 2190767 = 3286151) B3286151
theorem B2190857 : Blo 1459549 2190857 := bstep (se 2 (by rfl) ⟨821571, by rfl⟩ : syracuseStep 2190857 = 1643143) B1643143
theorem B2190887 : Blo 1459549 2190887 := bstep (se 1 (by rfl) ⟨1643165, by rfl⟩ : syracuseStep 2190887 = 3286331) B3286331
theorem B1642063 : Blo 1459549 1642063 := bstep (se 1 (by rfl) ⟨1231547, by rfl⟩ : syracuseStep 1642063 = 2463095) B2463095
theorem B2338427 : Blo 1459549 2338427 := bstep (se 1 (by rfl) ⟨1753820, by rfl⟩ : syracuseStep 2338427 = 3507641) B3507641
theorem B7892603 : Blo 1459549 7892603 := bstep (se 1 (by rfl) ⟨5919452, by rfl⟩ : syracuseStep 7892603 = 11838905) B11838905
theorem B2190971 : Blo 1459549 2190971 := bstep (se 1 (by rfl) ⟨1643228, by rfl⟩ : syracuseStep 2190971 = 3286457) B3286457
theorem B7491271 : Blo 1459549 7491271 := bstep (se 1 (by rfl) ⟨5618453, by rfl⟩ : syracuseStep 7491271 = 11236907) B11236907
theorem B4927175 : Blo 1459549 4927175 := bstep (se 1 (by rfl) ⟨3695381, by rfl⟩ : syracuseStep 4927175 = 7390763) B7390763
theorem B5918417 : Blo 1459549 5918417 := bstep (se 2 (by rfl) ⟨2219406, by rfl⟩ : syracuseStep 5918417 = 4438813) B4438813
theorem B9359063 : Blo 1459549 9359063 := bstep (se 1 (by rfl) ⟨7019297, by rfl⟩ : syracuseStep 9359063 = 14038595) B14038595
theorem B2191097 : Blo 1459549 2191097 := bstep (se 2 (by rfl) ⟨821661, by rfl⟩ : syracuseStep 2191097 = 1643323) B1643323
theorem B5263147 : Blo 1459549 5263147 := bstep (se 1 (by rfl) ⟨3947360, by rfl⟩ : syracuseStep 5263147 = 7894721) B7894721
theorem B2191199 : Blo 1459549 2191199 := bstep (se 1 (by rfl) ⟨1643399, by rfl⟩ : syracuseStep 2191199 = 3286799) B3286799
theorem B2191211 : Blo 1459549 2191211 := bstep (se 1 (by rfl) ⟨1643408, by rfl⟩ : syracuseStep 2191211 = 3286817) B3286817
theorem B2338703 : Blo 1459549 2338703 := bstep (se 1 (by rfl) ⟨1754027, by rfl⟩ : syracuseStep 2338703 = 3508055) B3508055
theorem B2338735 : Blo 1459549 2338735 := bstep (se 1 (by rfl) ⟨1754051, by rfl⟩ : syracuseStep 2338735 = 3508103) B3508103
theorem B1642459 : Blo 1459549 1642459 := bstep (se 1 (by rfl) ⟨1231844, by rfl⟩ : syracuseStep 1642459 = 2463689) B2463689
theorem B8318983 : Blo 1459549 8318983 := bstep (se 1 (by rfl) ⟨6239237, by rfl⟩ : syracuseStep 8318983 = 12478475) B12478475
theorem B2191439 : Blo 1459549 2191439 := bstep (se 1 (by rfl) ⟨1643579, by rfl⟩ : syracuseStep 2191439 = 3287159) B3287159
theorem B2191559 : Blo 1459549 2191559 := bstep (se 1 (by rfl) ⟨1643669, by rfl⟩ : syracuseStep 2191559 = 3287339) B3287339
theorem B10531225 : Blo 1459549 10531225 := bstep (se 2 (by rfl) ⟨3949209, by rfl⟩ : syracuseStep 10531225 = 7898419) B7898419
theorem B1642927 : Blo 1459549 1642927 := bstep (se 1 (by rfl) ⟨1232195, by rfl⟩ : syracuseStep 1642927 = 2464391) B2464391
theorem B2773435 : Blo 1459549 2773435 := bstep (se 1 (by rfl) ⟨2080076, by rfl⟩ : syracuseStep 2773435 = 4160153) B4160153
theorem B2773511 : Blo 1459549 2773511 := bstep (se 1 (by rfl) ⟨2080133, by rfl⟩ : syracuseStep 2773511 = 4160267) B4160267
theorem B4928039 : Blo 1459549 4928039 := bstep (se 1 (by rfl) ⟨3696029, by rfl⟩ : syracuseStep 4928039 = 7392059) B7392059
theorem B5919355 : Blo 1459549 5919355 := bstep (se 1 (by rfl) ⟨4439516, by rfl⟩ : syracuseStep 5919355 = 8879033) B8879033
theorem B4928147 : Blo 1459549 4928147 := bstep (se 1 (by rfl) ⟨3696110, by rfl⟩ : syracuseStep 4928147 = 7392221) B7392221
theorem B14029523 : Blo 1459549 14029523 := bstep (se 1 (by rfl) ⟨10522142, by rfl⟩ : syracuseStep 14029523 = 21044285) B21044285
theorem B7394003 : Blo 1459549 7394003 := bstep (se 1 (by rfl) ⟨5545502, by rfl⟩ : syracuseStep 7394003 = 11091005) B11091005
theorem B42095375 : Blo 1459549 42095375 := bstep (se 1 (by rfl) ⟨31571531, by rfl⟩ : syracuseStep 42095375 = 63143063) B63143063
theorem B1643359 : Blo 1459549 1643359 := bstep (se 1 (by rfl) ⟨1232519, by rfl⟩ : syracuseStep 1643359 = 2465039) B2465039
theorem B4928363 : Blo 1459549 4928363 := bstep (se 1 (by rfl) ⟨3696272, by rfl⟩ : syracuseStep 4928363 = 7392545) B7392545
theorem B4928417 : Blo 1459549 4928417 := bstep (se 2 (by rfl) ⟨1848156, by rfl⟩ : syracuseStep 4928417 = 3696313) B3696313
theorem B7017491 : Blo 1459549 7017491 := bstep (se 1 (by rfl) ⟨5263118, by rfl⟩ : syracuseStep 7017491 = 10526237) B10526237
theorem B1848359 : Blo 1459549 1848359 := bstep (se 1 (by rfl) ⟨1386269, by rfl⟩ : syracuseStep 1848359 = 2772539) B2772539
theorem B11998259 : Blo 1459549 11998259 := bstep (se 1 (by rfl) ⟨8998694, by rfl⟩ : syracuseStep 11998259 = 17997389) B17997389
theorem B5543255 : Blo 1459549 5543255 := bstep (se 1 (by rfl) ⟨4157441, by rfl⟩ : syracuseStep 5543255 = 8314883) B8314883
theorem B73037155 : Blo 1459549 73037155 := bstep (se 1 (by rfl) ⟨54777866, by rfl⟩ : syracuseStep 73037155 = 109555733) B109555733
theorem B1848683 : Blo 1459549 1848683 := bstep (se 1 (by rfl) ⟨1386512, by rfl⟩ : syracuseStep 1848683 = 2773025) B2773025
theorem B9360755 : Blo 1459549 9360755 := bstep (se 1 (by rfl) ⟨7020566, by rfl⟩ : syracuseStep 9360755 = 14041133) B14041133
theorem B33707411 : Blo 1459549 33707411 := bstep (se 1 (by rfl) ⟨25280558, by rfl⟩ : syracuseStep 33707411 = 50561117) B50561117
theorem B9360805 : Blo 1459549 9360805 := bstep (se 4 (by rfl) ⟨877575, by rfl⟩ : syracuseStep 9360805 = 1755151) B1755151
theorem B4929011 : Blo 1459549 4929011 := bstep (se 1 (by rfl) ⟨3696758, by rfl⟩ : syracuseStep 4929011 = 7393517) B7393517
theorem B2463311 : Blo 1459549 2463311 := bstep (se 1 (by rfl) ⟨1847483, by rfl⟩ : syracuseStep 2463311 = 3694967) B3694967
theorem B5264993 : Blo 1459549 5264993 := bstep (se 2 (by rfl) ⟨1974372, by rfl⟩ : syracuseStep 5264993 = 3948745) B3948745
theorem B11089547 : Blo 1459549 11089547 := bstep (se 1 (by rfl) ⟨8317160, by rfl⟩ : syracuseStep 11089547 = 16634321) B16634321
theorem B4929551 : Blo 1459549 4929551 := bstep (se 1 (by rfl) ⟨3697163, by rfl⟩ : syracuseStep 4929551 = 7394327) B7394327
theorem B5920847 : Blo 1459549 5920847 := bstep (se 1 (by rfl) ⟨4440635, by rfl⟩ : syracuseStep 5920847 = 8881271) B8881271
theorem B5920883 : Blo 1459549 5920883 := bstep (se 1 (by rfl) ⟨4440662, by rfl⟩ : syracuseStep 5920883 = 8881325) B8881325
theorem B4274333 : Blo 1459549 4274333 := bstep (se 3 (by rfl) ⟨801437, by rfl⟩ : syracuseStep 4274333 = 1602875) B1602875
theorem B2464175 : Blo 1459549 2464175 := bstep (se 1 (by rfl) ⟨1848131, by rfl⟩ : syracuseStep 2464175 = 3696263) B3696263
theorem B4930145 : Blo 1459549 4930145 := bstep (se 2 (by rfl) ⟨1848804, by rfl⟩ : syracuseStep 4930145 = 3697609) B3697609
theorem B4438739 : Blo 1459549 4438739 := bstep (se 1 (by rfl) ⟨3329054, by rfl⟩ : syracuseStep 4438739 = 6658109) B6658109
theorem B2464607 : Blo 1459549 2464607 := bstep (se 1 (by rfl) ⟨1848455, by rfl⟩ : syracuseStep 2464607 = 3696911) B3696911
theorem B10664879 : Blo 1459549 10664879 := bstep (se 1 (by rfl) ⟨7998659, by rfl⟩ : syracuseStep 10664879 = 15997319) B15997319
theorem B7396271 : Blo 1459549 7396271 := bstep (se 1 (by rfl) ⟨5547203, by rfl⟩ : syracuseStep 7396271 = 11094407) B11094407
theorem B4676687 : Blo 1459549 4676687 := bstep (se 1 (by rfl) ⟨3507515, by rfl⟩ : syracuseStep 4676687 = 7015031) B7015031
theorem B28065041 : Blo 1459549 28065041 := bstep (se 2 (by rfl) ⟨10524390, by rfl⟩ : syracuseStep 28065041 = 21048781) B21048781
theorem B2465167 : Blo 1459549 2465167 := bstep (se 1 (by rfl) ⟨1848875, by rfl⟩ : syracuseStep 2465167 = 3697751) B3697751
theorem B15785459 : Blo 1459549 15785459 := bstep (se 1 (by rfl) ⟨11839094, by rfl⟩ : syracuseStep 15785459 = 23678189) B23678189
theorem B3284603 : Blo 1459549 3284603 := bstep (se 1 (by rfl) ⟨2463452, by rfl⟩ : syracuseStep 3284603 = 4926905) B4926905
theorem B7896797 : Blo 1459549 7896797 := bstep (se 3 (by rfl) ⟨1480649, by rfl⟩ : syracuseStep 7896797 = 2961299) B2961299
theorem B3284729 : Blo 1459549 3284729 := bstep (se 2 (by rfl) ⟨1231773, by rfl⟩ : syracuseStep 3284729 = 2463547) B2463547
theorem B5619565 : Blo 1459549 5619565 := bstep (se 3 (by rfl) ⟨1053668, by rfl⟩ : syracuseStep 5619565 = 2107337) B2107337
theorem B11706221 : Blo 1459549 11706221 := bstep (se 3 (by rfl) ⟨2194916, by rfl⟩ : syracuseStep 11706221 = 4389833) B4389833
theorem B7806881 : Blo 1459549 7806881 := bstep (se 2 (by rfl) ⟨2927580, by rfl⟩ : syracuseStep 7806881 = 5855161) B5855161
theorem B3694511 : Blo 1459549 3694511 := bstep (se 1 (by rfl) ⟨2770883, by rfl⟩ : syracuseStep 3694511 = 5541767) B5541767
theorem B11091977 : Blo 1459549 11091977 := bstep (se 2 (by rfl) ⟨4159491, by rfl⟩ : syracuseStep 11091977 = 8318983) B8318983
theorem B2809961 : Blo 1459549 2809961 := bstep (se 2 (by rfl) ⟨1053735, by rfl⟩ : syracuseStep 2809961 = 2107471) B2107471
theorem B3285359 : Blo 1459549 3285359 := bstep (se 1 (by rfl) ⟨2464019, by rfl⟩ : syracuseStep 3285359 = 4928039) B4928039
theorem B3285431 : Blo 1459549 3285431 := bstep (se 1 (by rfl) ⟨2464073, by rfl⟩ : syracuseStep 3285431 = 4928147) B4928147
theorem B14041633 : Blo 1459549 14041633 := bstep (se 2 (by rfl) ⟨5265612, by rfl⟩ : syracuseStep 14041633 = 10531225) B10531225
theorem B3285575 : Blo 1459549 3285575 := bstep (se 1 (by rfl) ⟨2464181, by rfl⟩ : syracuseStep 3285575 = 4928363) B4928363
theorem B3285611 : Blo 1459549 3285611 := bstep (se 1 (by rfl) ⟨2464208, by rfl⟩ : syracuseStep 3285611 = 4928417) B4928417
theorem B4678327 : Blo 1459549 4678327 := bstep (se 1 (by rfl) ⟨3508745, by rfl⟩ : syracuseStep 4678327 = 7017491) B7017491
theorem B24953669 : Blo 1459549 24953669 := bstep (se 4 (by rfl) ⟨2339406, by rfl⟩ : syracuseStep 24953669 = 4678813) B4678813
theorem B3695503 : Blo 1459549 3695503 := bstep (se 1 (by rfl) ⟨2771627, by rfl⟩ : syracuseStep 3695503 = 5543255) B5543255
theorem B22471607 : Blo 1459549 22471607 := bstep (se 1 (by rfl) ⟨16853705, by rfl⟩ : syracuseStep 22471607 = 33707411) B33707411
theorem B3286007 : Blo 1459549 3286007 := bstep (se 1 (by rfl) ⟨2464505, by rfl⟩ : syracuseStep 3286007 = 4929011) B4929011
theorem B56911157 : Blo 1459549 56911157 := bstep (se 5 (by rfl) ⟨2667710, by rfl⟩ : syracuseStep 56911157 = 5335421) B5335421
theorem B4441439 : Blo 1459549 4441439 := bstep (se 1 (by rfl) ⟨3331079, by rfl⟩ : syracuseStep 4441439 = 6662159) B6662159
theorem B3695969 : Blo 1459549 3695969 := bstep (se 2 (by rfl) ⟨1385988, by rfl⟩ : syracuseStep 3695969 = 2771977) B2771977
theorem B3286367 : Blo 1459549 3286367 := bstep (se 1 (by rfl) ⟨2464775, by rfl⟩ : syracuseStep 3286367 = 4929551) B4929551
theorem B1459567 : Blo 1459549 1459567 := bstep (se 1 (by rfl) ⟨1094675, by rfl⟩ : syracuseStep 1459567 = 2189351) B2189351
theorem B1459623 : Blo 1459549 1459623 := bstep (se 1 (by rfl) ⟨1094717, by rfl⟩ : syracuseStep 1459623 = 2189435) B2189435
theorem B1459707 : Blo 1459549 1459707 := bstep (se 1 (by rfl) ⟨1094780, by rfl⟩ : syracuseStep 1459707 = 2189561) B2189561
theorem B1459775 : Blo 1459549 1459775 := bstep (se 1 (by rfl) ⟨1094831, by rfl⟩ : syracuseStep 1459775 = 2189663) B2189663
theorem B1459783 : Blo 1459549 1459783 := bstep (se 1 (by rfl) ⟨1094837, by rfl⟩ : syracuseStep 1459783 = 2189675) B2189675
theorem B6235805 : Blo 1459549 6235805 := bstep (se 3 (by rfl) ⟨1169213, by rfl⟩ : syracuseStep 6235805 = 2338427) B2338427
theorem B1459935 : Blo 1459549 1459935 := bstep (se 1 (by rfl) ⟨1094951, by rfl⟩ : syracuseStep 1459935 = 2189903) B2189903
theorem B3286763 : Blo 1459549 3286763 := bstep (se 1 (by rfl) ⟨2465072, by rfl⟩ : syracuseStep 3286763 = 4930145) B4930145
theorem B3696425 : Blo 1459549 3696425 := bstep (se 2 (by rfl) ⟨1386159, by rfl⟩ : syracuseStep 3696425 = 2772319) B2772319
theorem B1460015 : Blo 1459549 1460015 := bstep (se 1 (by rfl) ⟨1095011, by rfl⟩ : syracuseStep 1460015 = 2190023) B2190023
theorem B29976425 : Blo 1459549 29976425 := bstep (se 2 (by rfl) ⟨11241159, by rfl⟩ : syracuseStep 29976425 = 22482319) B22482319
theorem B3286889 : Blo 1459549 3286889 := bstep (se 2 (by rfl) ⟨1232583, by rfl⟩ : syracuseStep 3286889 = 2465167) B2465167
theorem B1460123 : Blo 1459549 1460123 := bstep (se 1 (by rfl) ⟨1095092, by rfl⟩ : syracuseStep 1460123 = 2190185) B2190185
theorem B1460175 : Blo 1459549 1460175 := bstep (se 1 (by rfl) ⟨1095131, by rfl⟩ : syracuseStep 1460175 = 2190263) B2190263
theorem B1460199 : Blo 1459549 1460199 := bstep (se 1 (by rfl) ⟨1095149, by rfl⟩ : syracuseStep 1460199 = 2190299) B2190299
theorem B2189417 : Blo 1459549 2189417 := bstep (se 2 (by rfl) ⟨821031, by rfl⟩ : syracuseStep 2189417 = 1642063) B1642063
theorem B7014529 : Blo 1459549 7014529 := bstep (se 2 (by rfl) ⟨2630448, by rfl⟩ : syracuseStep 7014529 = 5260897) B5260897
theorem B9988361 : Blo 1459549 9988361 := bstep (se 2 (by rfl) ⟨3745635, by rfl⟩ : syracuseStep 9988361 = 7491271) B7491271
theorem B1460511 : Blo 1459549 1460511 := bstep (se 1 (by rfl) ⟨1095383, by rfl⟩ : syracuseStep 1460511 = 2190767) B2190767
theorem B9357605 : Blo 1459549 9357605 := bstep (se 4 (by rfl) ⟨877275, by rfl⟩ : syracuseStep 9357605 = 1754551) B1754551
theorem B1460571 : Blo 1459549 1460571 := bstep (se 1 (by rfl) ⟨1095428, by rfl⟩ : syracuseStep 1460571 = 2190857) B2190857
theorem B1460591 : Blo 1459549 1460591 := bstep (se 1 (by rfl) ⟨1095443, by rfl⟩ : syracuseStep 1460591 = 2190887) B2190887
theorem B2189735 : Blo 1459549 2189735 := bstep (se 1 (by rfl) ⟨1642301, by rfl⟩ : syracuseStep 2189735 = 3284603) B3284603
theorem B5261735 : Blo 1459549 5261735 := bstep (se 1 (by rfl) ⟨3946301, by rfl⟩ : syracuseStep 5261735 = 7892603) B7892603
theorem B1460647 : Blo 1459549 1460647 := bstep (se 1 (by rfl) ⟨1095485, by rfl⟩ : syracuseStep 1460647 = 2190971) B2190971
theorem B2189819 : Blo 1459549 2189819 := bstep (se 1 (by rfl) ⟨1642364, by rfl⟩ : syracuseStep 2189819 = 3284729) B3284729
theorem B1460731 : Blo 1459549 1460731 := bstep (se 1 (by rfl) ⟨1095548, by rfl⟩ : syracuseStep 1460731 = 2191097) B2191097
theorem B1460799 : Blo 1459549 1460799 := bstep (se 1 (by rfl) ⟨1095599, by rfl⟩ : syracuseStep 1460799 = 2191199) B2191199
theorem B1460807 : Blo 1459549 1460807 := bstep (se 1 (by rfl) ⟨1095605, by rfl⟩ : syracuseStep 1460807 = 2191211) B2191211
theorem B1559135 : Blo 1459549 1559135 := bstep (se 1 (by rfl) ⟨1169351, by rfl⟩ : syracuseStep 1559135 = 2338703) B2338703
theorem B5204587 : Blo 1459549 5204587 := bstep (se 1 (by rfl) ⟨3903440, by rfl⟩ : syracuseStep 5204587 = 7806881) B7806881
theorem B2189945 : Blo 1459549 2189945 := bstep (se 2 (by rfl) ⟨821229, by rfl⟩ : syracuseStep 2189945 = 1642459) B1642459
theorem B2189999 : Blo 1459549 2189999 := bstep (se 1 (by rfl) ⟨1642499, by rfl⟩ : syracuseStep 2189999 = 3284999) B3284999
theorem B2190047 : Blo 1459549 2190047 := bstep (se 1 (by rfl) ⟨1642535, by rfl⟩ : syracuseStep 2190047 = 3285071) B3285071
theorem B1460959 : Blo 1459549 1460959 := bstep (se 1 (by rfl) ⟨1095719, by rfl⟩ : syracuseStep 1460959 = 2191439) B2191439
theorem B3697427 : Blo 1459549 3697427 := bstep (se 1 (by rfl) ⟨2773070, by rfl⟩ : syracuseStep 3697427 = 5546141) B5546141
theorem B1461039 : Blo 1459549 1461039 := bstep (se 1 (by rfl) ⟨1095779, by rfl⟩ : syracuseStep 1461039 = 2191559) B2191559
theorem B2190311 : Blo 1459549 2190311 := bstep (se 1 (by rfl) ⟨1642733, by rfl⟩ : syracuseStep 2190311 = 3285467) B3285467
theorem B9120883 : Blo 1459549 9120883 := bstep (se 1 (by rfl) ⟨6840662, by rfl⟩ : syracuseStep 9120883 = 13681325) B13681325
theorem B2370703 : Blo 1459549 2370703 := bstep (se 1 (by rfl) ⟨1778027, by rfl⟩ : syracuseStep 2370703 = 3556055) B3556055
theorem B3697883 : Blo 1459549 3697883 := bstep (se 1 (by rfl) ⟨2773412, by rfl⟩ : syracuseStep 3697883 = 5546825) B5546825
theorem B2190569 : Blo 1459549 2190569 := bstep (se 2 (by rfl) ⟨821463, by rfl⟩ : syracuseStep 2190569 = 1642927) B1642927
theorem B3697913 : Blo 1459549 3697913 := bstep (se 2 (by rfl) ⟨1386717, by rfl⟩ : syracuseStep 3697913 = 2773435) B2773435
theorem B2190623 : Blo 1459549 2190623 := bstep (se 1 (by rfl) ⟨1642967, by rfl⟩ : syracuseStep 2190623 = 3285935) B3285935
theorem B7998839 : Blo 1459549 7998839 := bstep (se 1 (by rfl) ⟨5999129, by rfl⟩ : syracuseStep 7998839 = 11998259) B11998259
theorem B2190791 : Blo 1459549 2190791 := bstep (se 1 (by rfl) ⟨1643093, by rfl⟩ : syracuseStep 2190791 = 3286187) B3286187
theorem B7892473 : Blo 1459549 7892473 := bstep (se 2 (by rfl) ⟨2959677, by rfl⟩ : syracuseStep 7892473 = 5919355) B5919355
theorem B1642207 : Blo 1459549 1642207 := bstep (se 1 (by rfl) ⟨1231655, by rfl⟩ : syracuseStep 1642207 = 2463311) B2463311
theorem B3509995 : Blo 1459549 3509995 := bstep (se 1 (by rfl) ⟨2632496, by rfl⟩ : syracuseStep 3509995 = 5264993) B5264993
theorem B7393031 : Blo 1459549 7393031 := bstep (se 1 (by rfl) ⟨5544773, by rfl⟩ : syracuseStep 7393031 = 11089547) B11089547
theorem B2191145 : Blo 1459549 2191145 := bstep (se 2 (by rfl) ⟨821679, by rfl⟩ : syracuseStep 2191145 = 1643359) B1643359
theorem B2191151 : Blo 1459549 2191151 := bstep (se 1 (by rfl) ⟨1643363, by rfl⟩ : syracuseStep 2191151 = 3286727) B3286727
theorem B1642783 : Blo 1459549 1642783 := bstep (se 1 (by rfl) ⟨1232087, by rfl⟩ : syracuseStep 1642783 = 2464175) B2464175
theorem B97382873 : Blo 1459549 97382873 := bstep (se 2 (by rfl) ⟨36518577, by rfl⟩ : syracuseStep 97382873 = 73037155) B73037155
theorem B35508725 : Blo 1459549 35508725 := bstep (se 5 (by rfl) ⟨1664471, by rfl⟩ : syracuseStep 35508725 = 3328943) B3328943
theorem B12481073 : Blo 1459549 12481073 := bstep (se 2 (by rfl) ⟨4680402, by rfl⟩ : syracuseStep 12481073 = 9360805) B9360805
theorem B1643071 : Blo 1459549 1643071 := bstep (se 1 (by rfl) ⟨1232303, by rfl⟩ : syracuseStep 1643071 = 2464607) B2464607
theorem B3117791 : Blo 1459549 3117791 := bstep (se 1 (by rfl) ⟨2338343, by rfl⟩ : syracuseStep 3117791 = 4676687) B4676687
theorem B2339663 : Blo 1459549 2339663 := bstep (se 1 (by rfl) ⟨1754747, by rfl⟩ : syracuseStep 2339663 = 3509495) B3509495
theorem B14988125 : Blo 1459549 14988125 := bstep (se 3 (by rfl) ⟨2810273, by rfl⟩ : syracuseStep 14988125 = 5620547) B5620547
theorem B10523639 : Blo 1459549 10523639 := bstep (se 1 (by rfl) ⟨7892729, by rfl⟩ : syracuseStep 10523639 = 15785459) B15785459
theorem B7017529 : Blo 1459549 7017529 := bstep (se 2 (by rfl) ⟨2631573, by rfl⟩ : syracuseStep 7017529 = 5263147) B5263147
theorem B28439677 : Blo 1459549 28439677 := bstep (se 3 (by rfl) ⟨5332439, by rfl⟩ : syracuseStep 28439677 = 10664879) B10664879
theorem B3945611 : Blo 1459549 3945611 := bstep (se 1 (by rfl) ⟨2959208, by rfl⟩ : syracuseStep 3945611 = 5918417) B5918417
theorem B6239375 : Blo 1459549 6239375 := bstep (se 1 (by rfl) ⟨4679531, by rfl⟩ : syracuseStep 6239375 = 9359063) B9359063
theorem B7492753 : Blo 1459549 7492753 := bstep (se 2 (by rfl) ⟨2809782, by rfl⟩ : syracuseStep 7492753 = 5619565) B5619565
theorem B5264531 : Blo 1459549 5264531 := bstep (se 1 (by rfl) ⟨3948398, by rfl⟩ : syracuseStep 5264531 = 7896797) B7896797
theorem B3118313 : Blo 1459549 3118313 := bstep (se 2 (by rfl) ⟨1169367, by rfl⟩ : syracuseStep 3118313 = 2338735) B2338735
theorem B2340073 : Blo 1459549 2340073 := bstep (se 2 (by rfl) ⟨877527, by rfl⟩ : syracuseStep 2340073 = 1755055) B1755055
theorem B7804147 : Blo 1459549 7804147 := bstep (se 1 (by rfl) ⟨5853110, by rfl⟩ : syracuseStep 7804147 = 11706221) B11706221
theorem B2463007 : Blo 1459549 2463007 := bstep (se 1 (by rfl) ⟨1847255, by rfl⟩ : syracuseStep 2463007 = 3694511) B3694511
theorem B4928957 : Blo 1459549 4928957 := bstep (se 3 (by rfl) ⟨924179, by rfl⟩ : syracuseStep 4928957 = 1848359) B1848359
theorem B1849007 : Blo 1459549 1849007 := bstep (se 1 (by rfl) ⟨1386755, by rfl⟩ : syracuseStep 1849007 = 2773511) B2773511
theorem B2463419 : Blo 1459549 2463419 := bstep (se 1 (by rfl) ⟨1847564, by rfl⟩ : syracuseStep 2463419 = 3695129) B3695129
theorem B9353015 : Blo 1459549 9353015 := bstep (se 1 (by rfl) ⟨7014761, by rfl⟩ : syracuseStep 9353015 = 14029523) B14029523
theorem B4929335 : Blo 1459549 4929335 := bstep (se 1 (by rfl) ⟨3697001, by rfl⟩ : syracuseStep 4929335 = 7394003) B7394003
theorem B28063583 : Blo 1459549 28063583 := bstep (se 1 (by rfl) ⟨21047687, by rfl⟩ : syracuseStep 28063583 = 42095375) B42095375
theorem B6084743 : Blo 1459549 6084743 := bstep (se 1 (by rfl) ⟨4563557, by rfl⟩ : syracuseStep 6084743 = 9127115) B9127115
theorem B6240503 : Blo 1459549 6240503 := bstep (se 1 (by rfl) ⟨4680377, by rfl⟩ : syracuseStep 6240503 = 9360755) B9360755
theorem B4929821 : Blo 1459549 4929821 := bstep (se 3 (by rfl) ⟨924341, by rfl⟩ : syracuseStep 4929821 = 1848683) B1848683
theorem B3119543 : Blo 1459549 3119543 := bstep (se 1 (by rfl) ⟨2339657, by rfl⟩ : syracuseStep 3119543 = 4679315) B4679315
theorem B7395947 : Blo 1459549 7395947 := bstep (se 1 (by rfl) ⟨5546960, by rfl⟩ : syracuseStep 7395947 = 11093921) B11093921
theorem B3947231 : Blo 1459549 3947231 := bstep (se 1 (by rfl) ⟨2960423, by rfl⟩ : syracuseStep 3947231 = 5920847) B5920847
theorem B3947255 : Blo 1459549 3947255 := bstep (se 1 (by rfl) ⟨2960441, by rfl⟩ : syracuseStep 3947255 = 5920883) B5920883
theorem B2849555 : Blo 1459549 2849555 := bstep (se 1 (by rfl) ⟨2137166, by rfl⟩ : syracuseStep 2849555 = 4274333) B4274333
theorem B16006193 : Blo 1459549 16006193 := bstep (se 2 (by rfl) ⟨6002322, by rfl⟩ : syracuseStep 16006193 = 12004645) B12004645
theorem B7396433 : Blo 1459549 7396433 := bstep (se 2 (by rfl) ⟨2773662, by rfl⟩ : syracuseStep 7396433 = 5547325) B5547325
theorem B11836637 : Blo 1459549 11836637 := bstep (se 3 (by rfl) ⟨2219369, by rfl⟩ : syracuseStep 11836637 = 4438739) B4438739
theorem B4930847 : Blo 1459549 4930847 := bstep (se 1 (by rfl) ⟨3698135, by rfl⟩ : syracuseStep 4930847 = 7396271) B7396271
theorem B2465147 : Blo 1459549 2465147 := bstep (se 1 (by rfl) ⟨1848860, by rfl⟩ : syracuseStep 2465147 = 3697721) B3697721
theorem B3284423 : Blo 1459549 3284423 := bstep (se 1 (by rfl) ⟨2463317, by rfl⟩ : syracuseStep 3284423 = 4926635) B4926635
theorem B18710027 : Blo 1459549 18710027 := bstep (se 1 (by rfl) ⟨14032520, by rfl⟩ : syracuseStep 18710027 = 28065041) B28065041
theorem B8314427 : Blo 1459549 8314427 := bstep (se 1 (by rfl) ⟨6235820, by rfl⟩ : syracuseStep 8314427 = 12471641) B12471641
theorem B3284783 : Blo 1459549 3284783 := bstep (se 1 (by rfl) ⟨2463587, by rfl⟩ : syracuseStep 3284783 = 4927175) B4927175
theorem B4677533 : Blo 1459549 4677533 := bstep (se 3 (by rfl) ⟨877037, by rfl⟩ : syracuseStep 4677533 = 1754075) B1754075
theorem B64921915 : Blo 1459549 64921915 := bstep (se 1 (by rfl) ⟨48691436, by rfl⟩ : syracuseStep 64921915 = 97382873) B97382873
theorem B2630407 : Blo 1459549 2630407 := bstep (se 1 (by rfl) ⟨1972805, by rfl⟩ : syracuseStep 2630407 = 3945611) B3945611
theorem B6939449 : Blo 1459549 6939449 := bstep (se 2 (by rfl) ⟨2602293, by rfl⟩ : syracuseStep 6939449 = 5204587) B5204587
theorem B3285971 : Blo 1459549 3285971 := bstep (se 1 (by rfl) ⟨2464478, by rfl⟩ : syracuseStep 3285971 = 4928957) B4928957
theorem B6235343 : Blo 1459549 6235343 := bstep (se 1 (by rfl) ⟨4676507, by rfl⟩ : syracuseStep 6235343 = 9353015) B9353015
theorem B3286223 : Blo 1459549 3286223 := bstep (se 1 (by rfl) ⟨2464667, by rfl⟩ : syracuseStep 3286223 = 4929335) B4929335
theorem B1459611 : Blo 1459549 1459611 := bstep (se 1 (by rfl) ⟨1094708, by rfl⟩ : syracuseStep 1459611 = 2189417) B2189417
theorem B9356705 : Blo 1459549 9356705 := bstep (se 2 (by rfl) ⟨3508764, by rfl⟩ : syracuseStep 9356705 = 7017529) B7017529
theorem B3286547 : Blo 1459549 3286547 := bstep (se 1 (by rfl) ⟨2464910, by rfl⟩ : syracuseStep 3286547 = 4929821) B4929821
theorem B1459823 : Blo 1459549 1459823 := bstep (se 1 (by rfl) ⟨1094867, by rfl⟩ : syracuseStep 1459823 = 2189735) B2189735
theorem B3507823 : Blo 1459549 3507823 := bstep (se 1 (by rfl) ⟨2630867, by rfl⟩ : syracuseStep 3507823 = 5261735) B5261735
theorem B10405529 : Blo 1459549 10405529 := bstep (se 2 (by rfl) ⟨3902073, by rfl⟩ : syracuseStep 10405529 = 7804147) B7804147
theorem B1459879 : Blo 1459549 1459879 := bstep (se 1 (by rfl) ⟨1094909, by rfl⟩ : syracuseStep 1459879 = 2189819) B2189819
theorem B1459963 : Blo 1459549 1459963 := bstep (se 1 (by rfl) ⟨1094972, by rfl⟩ : syracuseStep 1459963 = 2189945) B2189945
theorem B1459999 : Blo 1459549 1459999 := bstep (se 1 (by rfl) ⟨1094999, by rfl⟩ : syracuseStep 1459999 = 2189999) B2189999
theorem B1460031 : Blo 1459549 1460031 := bstep (se 1 (by rfl) ⟨1095023, by rfl⟩ : syracuseStep 1460031 = 2190047) B2190047
theorem B2631503 : Blo 1459549 2631503 := bstep (se 1 (by rfl) ⟨1973627, by rfl⟩ : syracuseStep 2631503 = 3947255) B3947255
theorem B1460207 : Blo 1459549 1460207 := bstep (se 1 (by rfl) ⟨1095155, by rfl⟩ : syracuseStep 1460207 = 2190311) B2190311
theorem B7891091 : Blo 1459549 7891091 := bstep (se 1 (by rfl) ⟨5918318, by rfl⟩ : syracuseStep 7891091 = 11836637) B11836637
theorem B1460379 : Blo 1459549 1460379 := bstep (se 1 (by rfl) ⟨1095284, by rfl⟩ : syracuseStep 1460379 = 2190569) B2190569
theorem B1460415 : Blo 1459549 1460415 := bstep (se 1 (by rfl) ⟨1095311, by rfl⟩ : syracuseStep 1460415 = 2190623) B2190623
theorem B3287231 : Blo 1459549 3287231 := bstep (se 1 (by rfl) ⟨2465423, by rfl⟩ : syracuseStep 3287231 = 4930847) B4930847
theorem B2189609 : Blo 1459549 2189609 := bstep (se 2 (by rfl) ⟨821103, by rfl⟩ : syracuseStep 2189609 = 1642207) B1642207
theorem B2189615 : Blo 1459549 2189615 := bstep (se 1 (by rfl) ⟨1642211, by rfl⟩ : syracuseStep 2189615 = 3284423) B3284423
theorem B1460527 : Blo 1459549 1460527 := bstep (se 1 (by rfl) ⟨1095395, by rfl⟩ : syracuseStep 1460527 = 2190791) B2190791
theorem B4679993 : Blo 1459549 4679993 := bstep (se 2 (by rfl) ⟨1754997, by rfl⟩ : syracuseStep 4679993 = 3509995) B3509995
theorem B1460763 : Blo 1459549 1460763 := bstep (se 1 (by rfl) ⟨1095572, by rfl⟩ : syracuseStep 1460763 = 2191145) B2191145
theorem B2189855 : Blo 1459549 2189855 := bstep (se 1 (by rfl) ⟨1642391, by rfl⟩ : syracuseStep 2189855 = 3284783) B3284783
theorem B1460767 : Blo 1459549 1460767 := bstep (se 1 (by rfl) ⟨1095575, by rfl⟩ : syracuseStep 1460767 = 2191151) B2191151
theorem B2190239 : Blo 1459549 2190239 := bstep (se 1 (by rfl) ⟨1642679, by rfl⟩ : syracuseStep 2190239 = 3285359) B3285359
theorem B2190287 : Blo 1459549 2190287 := bstep (se 1 (by rfl) ⟨1642715, by rfl⟩ : syracuseStep 2190287 = 3285431) B3285431
theorem B2190377 : Blo 1459549 2190377 := bstep (se 2 (by rfl) ⟨821391, by rfl⟩ : syracuseStep 2190377 = 1642783) B1642783
theorem B2190383 : Blo 1459549 2190383 := bstep (se 1 (by rfl) ⟨1642787, by rfl⟩ : syracuseStep 2190383 = 3285575) B3285575
theorem B2190407 : Blo 1459549 2190407 := bstep (se 1 (by rfl) ⟨1642805, by rfl⟩ : syracuseStep 2190407 = 3285611) B3285611
theorem B151678277 : Blo 1459549 151678277 := bstep (se 4 (by rfl) ⟨14219838, by rfl⟩ : syracuseStep 151678277 = 28439677) B28439677
theorem B2190671 : Blo 1459549 2190671 := bstep (se 1 (by rfl) ⟨1643003, by rfl⟩ : syracuseStep 2190671 = 3286007) B3286007
theorem B18722177 : Blo 1459549 18722177 := bstep (se 2 (by rfl) ⟨7020816, by rfl⟩ : syracuseStep 18722177 = 14041633) B14041633
theorem B2190761 : Blo 1459549 2190761 := bstep (se 2 (by rfl) ⟨821535, by rfl⟩ : syracuseStep 2190761 = 1643071) B1643071
theorem B3509687 : Blo 1459549 3509687 := bstep (se 1 (by rfl) ⟨2632265, by rfl⟩ : syracuseStep 3509687 = 5264531) B5264531
theorem B37940771 : Blo 1459549 37940771 := bstep (se 1 (by rfl) ⟨28455578, by rfl⟩ : syracuseStep 37940771 = 56911157) B56911157
theorem B2960959 : Blo 1459549 2960959 := bstep (se 1 (by rfl) ⟨2220719, by rfl⟩ : syracuseStep 2960959 = 4441439) B4441439
theorem B2190911 : Blo 1459549 2190911 := bstep (se 1 (by rfl) ⟨1643183, by rfl⟩ : syracuseStep 2190911 = 3286367) B3286367
theorem B6237769 : Blo 1459549 6237769 := bstep (se 2 (by rfl) ⟨2339163, by rfl⟩ : syracuseStep 6237769 = 4678327) B4678327
theorem B4157203 : Blo 1459549 4157203 := bstep (se 1 (by rfl) ⟨3117902, by rfl⟩ : syracuseStep 4157203 = 6235805) B6235805
theorem B1642279 : Blo 1459549 1642279 := bstep (se 1 (by rfl) ⟨1231709, by rfl⟩ : syracuseStep 1642279 = 2463419) B2463419
theorem B2191175 : Blo 1459549 2191175 := bstep (se 1 (by rfl) ⟨1643381, by rfl⟩ : syracuseStep 2191175 = 3286763) B3286763
theorem B4927337 : Blo 1459549 4927337 := bstep (se 2 (by rfl) ⟨1847751, by rfl⟩ : syracuseStep 4927337 = 3695503) B3695503
theorem B12480389 : Blo 1459549 12480389 := bstep (se 4 (by rfl) ⟨1170036, by rfl⟩ : syracuseStep 12480389 = 2340073) B2340073
theorem B19984283 : Blo 1459549 19984283 := bstep (se 1 (by rfl) ⟨14988212, by rfl⟩ : syracuseStep 19984283 = 29976425) B29976425
theorem B2191259 : Blo 1459549 2191259 := bstep (se 1 (by rfl) ⟨1643444, by rfl⟩ : syracuseStep 2191259 = 3286889) B3286889
theorem B12161177 : Blo 1459549 12161177 := bstep (se 2 (by rfl) ⟨4560441, by rfl⟩ : syracuseStep 12161177 = 9120883) B9120883
theorem B9990337 : Blo 1459549 9990337 := bstep (se 2 (by rfl) ⟨3746376, by rfl⟩ : syracuseStep 9990337 = 7492753) B7492753
theorem B6238403 : Blo 1459549 6238403 := bstep (se 1 (by rfl) ⟨4678802, by rfl⟩ : syracuseStep 6238403 = 9357605) B9357605
theorem B4157693 : Blo 1459549 4157693 := bstep (se 3 (by rfl) ⟨779567, by rfl⟩ : syracuseStep 4157693 = 1559135) B1559135
theorem B10523297 : Blo 1459549 10523297 := bstep (se 2 (by rfl) ⟨3946236, by rfl⟩ : syracuseStep 10523297 = 7892473) B7892473
theorem B10670795 : Blo 1459549 10670795 := bstep (se 1 (by rfl) ⟨8003096, by rfl⟩ : syracuseStep 10670795 = 16006193) B16006193
theorem B6239101 : Blo 1459549 6239101 := bstep (se 3 (by rfl) ⟨1169831, by rfl⟩ : syracuseStep 6239101 = 2339663) B2339663
theorem B1643431 : Blo 1459549 1643431 := bstep (se 1 (by rfl) ⟨1232573, by rfl⟩ : syracuseStep 1643431 = 2465147) B2465147
theorem B12473351 : Blo 1459549 12473351 := bstep (se 1 (by rfl) ⟨9355013, by rfl⟩ : syracuseStep 12473351 = 18710027) B18710027
theorem B5542951 : Blo 1459549 5542951 := bstep (se 1 (by rfl) ⟨4157213, by rfl⟩ : syracuseStep 5542951 = 8314427) B8314427
theorem B4928687 : Blo 1459549 4928687 := bstep (se 1 (by rfl) ⟨3696515, by rfl⟩ : syracuseStep 4928687 = 7393031) B7393031
theorem B3118355 : Blo 1459549 3118355 := bstep (se 1 (by rfl) ⟨2338766, by rfl⟩ : syracuseStep 3118355 = 4677533) B4677533
theorem B28063037 : Blo 1459549 28063037 := bstep (se 3 (by rfl) ⟨5261819, by rfl⟩ : syracuseStep 28063037 = 10523639) B10523639
theorem B7394651 : Blo 1459549 7394651 := bstep (se 1 (by rfl) ⟨5545988, by rfl⟩ : syracuseStep 7394651 = 11091977) B11091977
theorem B1873307 : Blo 1459549 1873307 := bstep (se 1 (by rfl) ⟨1404980, by rfl⟩ : syracuseStep 1873307 = 2809961) B2809961
theorem B23672483 : Blo 1459549 23672483 := bstep (se 1 (by rfl) ⟨17754362, by rfl⟩ : syracuseStep 23672483 = 35508725) B35508725
theorem B16225981 : Blo 1459549 16225981 := bstep (se 3 (by rfl) ⟨3042371, by rfl⟩ : syracuseStep 16225981 = 6084743) B6084743
theorem B8320715 : Blo 1459549 8320715 := bstep (se 1 (by rfl) ⟨6240536, by rfl⟩ : syracuseStep 8320715 = 12481073) B12481073
theorem B16635779 : Blo 1459549 16635779 := bstep (se 1 (by rfl) ⟨12476834, by rfl⟩ : syracuseStep 16635779 = 24953669) B24953669
theorem B9992083 : Blo 1459549 9992083 := bstep (se 1 (by rfl) ⟨7494062, by rfl⟩ : syracuseStep 9992083 = 14988125) B14988125
theorem B14981071 : Blo 1459549 14981071 := bstep (se 1 (by rfl) ⟨11235803, by rfl⟩ : syracuseStep 14981071 = 22471607) B22471607
theorem B37410821 : Blo 1459549 37410821 := bstep (se 4 (by rfl) ⟨3507264, by rfl⟩ : syracuseStep 37410821 = 7014529) B7014529
theorem B4159583 : Blo 1459549 4159583 := bstep (se 1 (by rfl) ⟨3119687, by rfl⟩ : syracuseStep 4159583 = 6239375) B6239375
theorem B2078875 : Blo 1459549 2078875 := bstep (se 1 (by rfl) ⟨1559156, by rfl⟩ : syracuseStep 2078875 = 3118313) B3118313
theorem B2463979 : Blo 1459549 2463979 := bstep (se 1 (by rfl) ⟨1847984, by rfl⟩ : syracuseStep 2463979 = 3695969) B3695969
theorem B2464283 : Blo 1459549 2464283 := bstep (se 1 (by rfl) ⟨1848212, by rfl⟩ : syracuseStep 2464283 = 3696425) B3696425
theorem B18709055 : Blo 1459549 18709055 := bstep (se 1 (by rfl) ⟨14031791, by rfl⟩ : syracuseStep 18709055 = 28063583) B28063583
theorem B4160335 : Blo 1459549 4160335 := bstep (se 1 (by rfl) ⟨3120251, by rfl⟩ : syracuseStep 4160335 = 6240503) B6240503
theorem B6658907 : Blo 1459549 6658907 := bstep (se 1 (by rfl) ⟨4994180, by rfl⟩ : syracuseStep 6658907 = 9988361) B9988361
theorem B3160937 : Blo 1459549 3160937 := bstep (se 2 (by rfl) ⟨1185351, by rfl⟩ : syracuseStep 3160937 = 2370703) B2370703
theorem B2079695 : Blo 1459549 2079695 := bstep (se 1 (by rfl) ⟨1559771, by rfl⟩ : syracuseStep 2079695 = 3119543) B3119543
theorem B3284009 : Blo 1459549 3284009 := bstep (se 2 (by rfl) ⟨1231503, by rfl⟩ : syracuseStep 3284009 = 2463007) B2463007
theorem B4930631 : Blo 1459549 4930631 := bstep (se 1 (by rfl) ⟨3697973, by rfl⟩ : syracuseStep 4930631 = 7395947) B7395947
theorem B4930685 : Blo 1459549 4930685 := bstep (se 3 (by rfl) ⟨924503, by rfl⟩ : syracuseStep 4930685 = 1849007) B1849007
theorem B2464951 : Blo 1459549 2464951 := bstep (se 1 (by rfl) ⟨1848713, by rfl⟩ : syracuseStep 2464951 = 3697427) B3697427
theorem B1899703 : Blo 1459549 1899703 := bstep (se 1 (by rfl) ⟨1424777, by rfl⟩ : syracuseStep 1899703 = 2849555) B2849555
theorem B8314109 : Blo 1459549 8314109 := bstep (se 3 (by rfl) ⟨1558895, by rfl⟩ : syracuseStep 8314109 = 3117791) B3117791
theorem B10525949 : Blo 1459549 10525949 := bstep (se 3 (by rfl) ⟨1973615, by rfl⟩ : syracuseStep 10525949 = 3947231) B3947231
theorem B4930955 : Blo 1459549 4930955 := bstep (se 1 (by rfl) ⟨3698216, by rfl⟩ : syracuseStep 4930955 = 7396433) B7396433
theorem B2465255 : Blo 1459549 2465255 := bstep (se 1 (by rfl) ⟨1848941, by rfl⟩ : syracuseStep 2465255 = 3697883) B3697883
theorem B2465275 : Blo 1459549 2465275 := bstep (se 1 (by rfl) ⟨1848956, by rfl⟩ : syracuseStep 2465275 = 3697913) B3697913
theorem B5332559 : Blo 1459549 5332559 := bstep (se 1 (by rfl) ⟨3999419, by rfl⟩ : syracuseStep 5332559 = 7998839) B7998839
theorem B13320449 : Blo 1459549 13320449 := bstep (se 2 (by rfl) ⟨4995168, by rfl⟩ : syracuseStep 13320449 = 9990337) B9990337
theorem B3285305 : Blo 1459549 3285305 := bstep (se 2 (by rfl) ⟨1231989, by rfl⟩ : syracuseStep 3285305 = 2463979) B2463979
theorem B8315567 : Blo 1459549 8315567 := bstep (se 1 (by rfl) ⟨6236675, by rfl⟩ : syracuseStep 8315567 = 12473351) B12473351
theorem B3285791 : Blo 1459549 3285791 := bstep (se 1 (by rfl) ⟨2464343, by rfl⟩ : syracuseStep 3285791 = 4928687) B4928687
theorem B3507209 : Blo 1459549 3507209 := bstep (se 2 (by rfl) ⟨1315203, by rfl⟩ : syracuseStep 3507209 = 2630407) B2630407
theorem B5547113 : Blo 1459549 5547113 := bstep (se 2 (by rfl) ⟨2080167, by rfl⟩ : syracuseStep 5547113 = 4160335) B4160335
theorem B5547143 : Blo 1459549 5547143 := bstep (se 1 (by rfl) ⟨4160357, by rfl⟩ : syracuseStep 5547143 = 8320715) B8320715
theorem B1754335 : Blo 1459549 1754335 := bstep (se 1 (by rfl) ⟨1315751, by rfl⟩ : syracuseStep 1754335 = 2631503) B2631503
theorem B7390601 : Blo 1459549 7390601 := bstep (se 2 (by rfl) ⟨2771475, by rfl⟩ : syracuseStep 7390601 = 5542951) B5542951
theorem B5260727 : Blo 1459549 5260727 := bstep (se 1 (by rfl) ⟨3945545, by rfl⟩ : syracuseStep 5260727 = 7891091) B7891091
theorem B1459739 : Blo 1459549 1459739 := bstep (se 1 (by rfl) ⟨1094804, by rfl⟩ : syracuseStep 1459739 = 2189609) B2189609
theorem B1459743 : Blo 1459549 1459743 := bstep (se 1 (by rfl) ⟨1094807, by rfl⟩ : syracuseStep 1459743 = 2189615) B2189615
theorem B3286601 : Blo 1459549 3286601 := bstep (se 2 (by rfl) ⟨1232475, by rfl⟩ : syracuseStep 3286601 = 2464951) B2464951
theorem B1459903 : Blo 1459549 1459903 := bstep (se 1 (by rfl) ⟨1094927, by rfl⟩ : syracuseStep 1459903 = 2189855) B2189855
theorem B2107291 : Blo 1459549 2107291 := bstep (se 1 (by rfl) ⟨1580468, by rfl⟩ : syracuseStep 2107291 = 3160937) B3160937
theorem B1460159 : Blo 1459549 1460159 := bstep (se 1 (by rfl) ⟨1095119, by rfl⟩ : syracuseStep 1460159 = 2190239) B2190239
theorem B1460191 : Blo 1459549 1460191 := bstep (se 1 (by rfl) ⟨1095143, by rfl⟩ : syracuseStep 1460191 = 2190287) B2190287
theorem B3287033 : Blo 1459549 3287033 := bstep (se 2 (by rfl) ⟨1232637, by rfl⟩ : syracuseStep 3287033 = 2465275) B2465275
theorem B2189339 : Blo 1459549 2189339 := bstep (se 1 (by rfl) ⟨1642004, by rfl⟩ : syracuseStep 2189339 = 3284009) B3284009
theorem B1460251 : Blo 1459549 1460251 := bstep (se 1 (by rfl) ⟨1095188, by rfl⟩ : syracuseStep 1460251 = 2190377) B2190377
theorem B1460255 : Blo 1459549 1460255 := bstep (se 1 (by rfl) ⟨1095191, by rfl⟩ : syracuseStep 1460255 = 2190383) B2190383
theorem B1460271 : Blo 1459549 1460271 := bstep (se 1 (by rfl) ⟨1095203, by rfl⟩ : syracuseStep 1460271 = 2190407) B2190407
theorem B3287087 : Blo 1459549 3287087 := bstep (se 1 (by rfl) ⟨2465315, by rfl⟩ : syracuseStep 3287087 = 4930631) B4930631
theorem B3287123 : Blo 1459549 3287123 := bstep (se 1 (by rfl) ⟨2465342, by rfl⟩ : syracuseStep 3287123 = 4930685) B4930685
theorem B8317025 : Blo 1459549 8317025 := bstep (se 2 (by rfl) ⟨3118884, by rfl⟩ : syracuseStep 8317025 = 6237769) B6237769
theorem B1460447 : Blo 1459549 1460447 := bstep (se 1 (by rfl) ⟨1095335, by rfl⟩ : syracuseStep 1460447 = 2190671) B2190671
theorem B3287303 : Blo 1459549 3287303 := bstep (se 1 (by rfl) ⟨2465477, by rfl⟩ : syracuseStep 3287303 = 4930955) B4930955
theorem B1460507 : Blo 1459549 1460507 := bstep (se 1 (by rfl) ⟨1095380, by rfl⟩ : syracuseStep 1460507 = 2190761) B2190761
theorem B1460607 : Blo 1459549 1460607 := bstep (se 1 (by rfl) ⟨1095455, by rfl⟩ : syracuseStep 1460607 = 2190911) B2190911
theorem B2189705 : Blo 1459549 2189705 := bstep (se 2 (by rfl) ⟨821139, by rfl⟩ : syracuseStep 2189705 = 1642279) B1642279
theorem B13322777 : Blo 1459549 13322777 := bstep (se 2 (by rfl) ⟨4996041, by rfl⟩ : syracuseStep 13322777 = 9992083) B9992083
theorem B1460783 : Blo 1459549 1460783 := bstep (se 1 (by rfl) ⟨1095587, by rfl⟩ : syracuseStep 1460783 = 2191175) B2191175
theorem B13322855 : Blo 1459549 13322855 := bstep (se 1 (by rfl) ⟨9992141, by rfl⟩ : syracuseStep 13322855 = 19984283) B19984283
theorem B19974761 : Blo 1459549 19974761 := bstep (se 2 (by rfl) ⟨7490535, by rfl⟩ : syracuseStep 19974761 = 14981071) B14981071
theorem B1460839 : Blo 1459549 1460839 := bstep (se 1 (by rfl) ⟨1095629, by rfl⟩ : syracuseStep 1460839 = 2191259) B2191259
theorem B2771795 : Blo 1459549 2771795 := bstep (se 1 (by rfl) ⟨2078846, by rfl⟩ : syracuseStep 2771795 = 4157693) B4157693
theorem B2771833 : Blo 1459549 2771833 := bstep (se 2 (by rfl) ⟨1039437, by rfl⟩ : syracuseStep 2771833 = 2078875) B2078875
theorem B7015531 : Blo 1459549 7015531 := bstep (se 1 (by rfl) ⟨5261648, by rfl⟩ : syracuseStep 7015531 = 10523297) B10523297
theorem B7113863 : Blo 1459549 7113863 := bstep (se 1 (by rfl) ⟨5335397, by rfl⟩ : syracuseStep 7113863 = 10670795) B10670795
theorem B2190647 : Blo 1459549 2190647 := bstep (se 1 (by rfl) ⟨1642985, by rfl⟩ : syracuseStep 2190647 = 3285971) B3285971
theorem B4156895 : Blo 1459549 4156895 := bstep (se 1 (by rfl) ⟨3117671, by rfl⟩ : syracuseStep 4156895 = 6235343) B6235343
theorem B2190815 : Blo 1459549 2190815 := bstep (se 1 (by rfl) ⟨1643111, by rfl⟩ : syracuseStep 2190815 = 3286223) B3286223
theorem B6237803 : Blo 1459549 6237803 := bstep (se 1 (by rfl) ⟨4678352, by rfl⟩ : syracuseStep 6237803 = 9356705) B9356705
theorem B2191031 : Blo 1459549 2191031 := bstep (se 1 (by rfl) ⟨1643273, by rfl⟩ : syracuseStep 2191031 = 3286547) B3286547
theorem B15781655 : Blo 1459549 15781655 := bstep (se 1 (by rfl) ⟨11836241, by rfl⟩ : syracuseStep 15781655 = 23672483) B23672483
theorem B9359165 : Blo 1459549 9359165 := bstep (se 3 (by rfl) ⟨1754843, by rfl⟩ : syracuseStep 9359165 = 3509687) B3509687
theorem B8318801 : Blo 1459549 8318801 := bstep (se 2 (by rfl) ⟨3119550, by rfl⟩ : syracuseStep 8318801 = 6239101) B6239101
theorem B2191241 : Blo 1459549 2191241 := bstep (se 2 (by rfl) ⟨821715, by rfl⟩ : syracuseStep 2191241 = 1643431) B1643431
theorem B24940547 : Blo 1459549 24940547 := bstep (se 1 (by rfl) ⟨18705410, by rfl⟩ : syracuseStep 24940547 = 37410821) B37410821
theorem B2773055 : Blo 1459549 2773055 := bstep (se 1 (by rfl) ⟨2079791, by rfl⟩ : syracuseStep 2773055 = 4159583) B4159583
theorem B101175389 : Blo 1459549 101175389 := bstep (se 3 (by rfl) ⟨18970385, by rfl⟩ : syracuseStep 101175389 = 37940771) B37940771
theorem B2191487 : Blo 1459549 2191487 := bstep (se 1 (by rfl) ⟨1643615, by rfl⟩ : syracuseStep 2191487 = 3287231) B3287231
theorem B1642855 : Blo 1459549 1642855 := bstep (se 1 (by rfl) ⟨1232141, by rfl⟩ : syracuseStep 1642855 = 2464283) B2464283
theorem B12472703 : Blo 1459549 12472703 := bstep (se 1 (by rfl) ⟨9354527, by rfl⟩ : syracuseStep 12472703 = 18709055) B18709055
theorem B5542739 : Blo 1459549 5542739 := bstep (se 1 (by rfl) ⟨4157054, by rfl⟩ : syracuseStep 5542739 = 8314109) B8314109
theorem B7017299 : Blo 1459549 7017299 := bstep (se 1 (by rfl) ⟨5262974, by rfl⟩ : syracuseStep 7017299 = 10525949) B10525949
theorem B101118851 : Blo 1459549 101118851 := bstep (se 1 (by rfl) ⟨75839138, by rfl⟩ : syracuseStep 101118851 = 151678277) B151678277
theorem B17757085 : Blo 1459549 17757085 := bstep (se 3 (by rfl) ⟨3329453, by rfl⟩ : syracuseStep 17757085 = 6658907) B6658907
theorem B12481451 : Blo 1459549 12481451 := bstep (se 1 (by rfl) ⟨9361088, by rfl⟩ : syracuseStep 12481451 = 18722177) B18722177
theorem B1643503 : Blo 1459549 1643503 := bstep (se 1 (by rfl) ⟨1232627, by rfl⟩ : syracuseStep 1643503 = 2465255) B2465255
theorem B5542937 : Blo 1459549 5542937 := bstep (se 2 (by rfl) ⟨2078601, by rfl⟩ : syracuseStep 5542937 = 4157203) B4157203
theorem B8320259 : Blo 1459549 8320259 := bstep (se 1 (by rfl) ⟨6240194, by rfl⟩ : syracuseStep 8320259 = 12480389) B12480389
theorem B8107451 : Blo 1459549 8107451 := bstep (se 1 (by rfl) ⟨6080588, by rfl⟩ : syracuseStep 8107451 = 12161177) B12161177
theorem B4158935 : Blo 1459549 4158935 := bstep (se 1 (by rfl) ⟨3119201, by rfl⟩ : syracuseStep 4158935 = 6238403) B6238403
theorem B86562553 : Blo 1459549 86562553 := bstep (se 2 (by rfl) ⟨32460957, by rfl⟩ : syracuseStep 86562553 = 64921915) B64921915
theorem B4626299 : Blo 1459549 4626299 := bstep (se 1 (by rfl) ⟨3469724, by rfl⟩ : syracuseStep 4626299 = 6939449) B6939449
theorem B2078903 : Blo 1459549 2078903 := bstep (se 1 (by rfl) ⟨1559177, by rfl⟩ : syracuseStep 2078903 = 3118355) B3118355
theorem B18708691 : Blo 1459549 18708691 := bstep (se 1 (by rfl) ⟨14031518, by rfl⟩ : syracuseStep 18708691 = 28063037) B28063037
theorem B4929767 : Blo 1459549 4929767 := bstep (se 1 (by rfl) ⟨3697325, by rfl⟩ : syracuseStep 4929767 = 7394651) B7394651
theorem B10131749 : Blo 1459549 10131749 := bstep (se 4 (by rfl) ⟨949851, by rfl⟩ : syracuseStep 10131749 = 1899703) B1899703
theorem B86538565 : Blo 1459549 86538565 := bstep (se 4 (by rfl) ⟨8112990, by rfl⟩ : syracuseStep 86538565 = 16225981) B16225981
theorem B4995485 : Blo 1459549 4995485 := bstep (se 3 (by rfl) ⟨936653, by rfl⟩ : syracuseStep 4995485 = 1873307) B1873307
theorem B6937019 : Blo 1459549 6937019 := bstep (se 1 (by rfl) ⟨5202764, by rfl⟩ : syracuseStep 6937019 = 10405529) B10405529
theorem B11090519 : Blo 1459549 11090519 := bstep (se 1 (by rfl) ⟨8317889, by rfl⟩ : syracuseStep 11090519 = 16635779) B16635779
theorem B3119995 : Blo 1459549 3119995 := bstep (se 1 (by rfl) ⟨2339996, by rfl⟩ : syracuseStep 3119995 = 4679993) B4679993
theorem B14220157 : Blo 1459549 14220157 := bstep (se 3 (by rfl) ⟨2666279, by rfl⟩ : syracuseStep 14220157 = 5332559) B5332559
theorem B3947945 : Blo 1459549 3947945 := bstep (se 2 (by rfl) ⟨1480479, by rfl⟩ : syracuseStep 3947945 = 2960959) B2960959
theorem B4677097 : Blo 1459549 4677097 := bstep (se 2 (by rfl) ⟨1753911, by rfl⟩ : syracuseStep 4677097 = 3507823) B3507823
theorem B5545853 : Blo 1459549 5545853 := bstep (se 3 (by rfl) ⟨1039847, by rfl⟩ : syracuseStep 5545853 = 2079695) B2079695
theorem B3284891 : Blo 1459549 3284891 := bstep (se 1 (by rfl) ⟨2463668, by rfl⟩ : syracuseStep 3284891 = 4927337) B4927337
theorem B8880299 : Blo 1459549 8880299 := bstep (se 1 (by rfl) ⟨6660224, by rfl⟩ : syracuseStep 8880299 = 13320449) B13320449
theorem B8315135 : Blo 1459549 8315135 := bstep (se 1 (by rfl) ⟨6236351, by rfl⟩ : syracuseStep 8315135 = 12472703) B12472703
theorem B24944921 : Blo 1459549 24944921 := bstep (se 2 (by rfl) ⟨9354345, by rfl⟩ : syracuseStep 24944921 = 18708691) B18708691
theorem B115384753 : Blo 1459549 115384753 := bstep (se 2 (by rfl) ⟨43269282, by rfl⟩ : syracuseStep 115384753 = 86538565) B86538565
theorem B3695159 : Blo 1459549 3695159 := bstep (se 1 (by rfl) ⟨2771369, by rfl⟩ : syracuseStep 3695159 = 5542739) B5542739
theorem B4678199 : Blo 1459549 4678199 := bstep (se 1 (by rfl) ⟨3508649, by rfl⟩ : syracuseStep 4678199 = 7017299) B7017299
theorem B67412567 : Blo 1459549 67412567 := bstep (se 1 (by rfl) ⟨50559425, by rfl⟩ : syracuseStep 67412567 = 101118851) B101118851
theorem B3695291 : Blo 1459549 3695291 := bstep (se 1 (by rfl) ⟨2771468, by rfl⟩ : syracuseStep 3695291 = 5542937) B5542937
theorem B5546839 : Blo 1459549 5546839 := bstep (se 1 (by rfl) ⟨4160129, by rfl⟩ : syracuseStep 5546839 = 8320259) B8320259
theorem B3507151 : Blo 1459549 3507151 := bstep (se 1 (by rfl) ⟨2630363, by rfl⟩ : syracuseStep 3507151 = 5260727) B5260727
theorem B10527853 : Blo 1459549 10527853 := bstep (se 3 (by rfl) ⟨1973972, by rfl⟩ : syracuseStep 10527853 = 3947945) B3947945
theorem B3695777 : Blo 1459549 3695777 := bstep (se 2 (by rfl) ⟨1385916, by rfl⟩ : syracuseStep 3695777 = 2771833) B2771833
theorem B23676113 : Blo 1459549 23676113 := bstep (se 2 (by rfl) ⟨8878542, by rfl⟩ : syracuseStep 23676113 = 17757085) B17757085
theorem B1459559 : Blo 1459549 1459559 := bstep (se 1 (by rfl) ⟨1094669, by rfl⟩ : syracuseStep 1459559 = 2189339) B2189339
theorem B3286511 : Blo 1459549 3286511 := bstep (se 1 (by rfl) ⟨2464883, by rfl⟩ : syracuseStep 3286511 = 4929767) B4929767
theorem B1459803 : Blo 1459549 1459803 := bstep (se 1 (by rfl) ⟨1094852, by rfl⟩ : syracuseStep 1459803 = 2189705) B2189705
theorem B8881903 : Blo 1459549 8881903 := bstep (se 1 (by rfl) ⟨6661427, by rfl⟩ : syracuseStep 8881903 = 13322855) B13322855
theorem B6236129 : Blo 1459549 6236129 := bstep (se 2 (by rfl) ⟨2338548, by rfl⟩ : syracuseStep 6236129 = 4677097) B4677097
theorem B1460431 : Blo 1459549 1460431 := bstep (se 1 (by rfl) ⟨1095323, by rfl⟩ : syracuseStep 1460431 = 2190647) B2190647
theorem B2771263 : Blo 1459549 2771263 := bstep (se 1 (by rfl) ⟨2078447, by rfl⟩ : syracuseStep 2771263 = 4156895) B4156895
theorem B1460543 : Blo 1459549 1460543 := bstep (se 1 (by rfl) ⟨1095407, by rfl⟩ : syracuseStep 1460543 = 2190815) B2190815
theorem B1460687 : Blo 1459549 1460687 := bstep (se 1 (by rfl) ⟨1095515, by rfl⟩ : syracuseStep 1460687 = 2191031) B2191031
theorem B10521103 : Blo 1459549 10521103 := bstep (se 1 (by rfl) ⟨7890827, by rfl⟩ : syracuseStep 10521103 = 15781655) B15781655
theorem B3697235 : Blo 1459549 3697235 := bstep (se 1 (by rfl) ⟨2772926, by rfl⟩ : syracuseStep 3697235 = 5545853) B5545853
theorem B1460827 : Blo 1459549 1460827 := bstep (se 1 (by rfl) ⟨1095620, by rfl⟩ : syracuseStep 1460827 = 2191241) B2191241
theorem B2189927 : Blo 1459549 2189927 := bstep (se 1 (by rfl) ⟨1642445, by rfl⟩ : syracuseStep 2189927 = 3284891) B3284891
theorem B1460991 : Blo 1459549 1460991 := bstep (se 1 (by rfl) ⟨1095743, by rfl⟩ : syracuseStep 1460991 = 2191487) B2191487
theorem B2190203 : Blo 1459549 2190203 := bstep (se 1 (by rfl) ⟨1642652, by rfl⟩ : syracuseStep 2190203 = 3285305) B3285305
theorem B2190473 : Blo 1459549 2190473 := bstep (se 2 (by rfl) ⟨821427, by rfl⟩ : syracuseStep 2190473 = 1642855) B1642855
theorem B2190527 : Blo 1459549 2190527 := bstep (se 1 (by rfl) ⟨1642895, by rfl⟩ : syracuseStep 2190527 = 3285791) B3285791
theorem B2338139 : Blo 1459549 2338139 := bstep (se 1 (by rfl) ⟨1753604, by rfl⟩ : syracuseStep 2338139 = 3507209) B3507209
theorem B3698075 : Blo 1459549 3698075 := bstep (se 1 (by rfl) ⟨2773556, by rfl⟩ : syracuseStep 3698075 = 5547113) B5547113
theorem B3698095 : Blo 1459549 3698095 := bstep (se 1 (by rfl) ⟨2773571, by rfl⟩ : syracuseStep 3698095 = 5547143) B5547143
theorem B4927067 : Blo 1459549 4927067 := bstep (se 1 (by rfl) ⟨3695300, by rfl⟩ : syracuseStep 4927067 = 7390601) B7390601
theorem B2772623 : Blo 1459549 2772623 := bstep (se 1 (by rfl) ⟨2079467, by rfl⟩ : syracuseStep 2772623 = 4158935) B4158935
theorem B2191067 : Blo 1459549 2191067 := bstep (se 1 (by rfl) ⟨1643300, by rfl⟩ : syracuseStep 2191067 = 3286601) B3286601
theorem B18960209 : Blo 1459549 18960209 := bstep (se 2 (by rfl) ⟨7110078, by rfl⟩ : syracuseStep 18960209 = 14220157) B14220157
theorem B3084199 : Blo 1459549 3084199 := bstep (se 1 (by rfl) ⟨2313149, by rfl⟩ : syracuseStep 3084199 = 4626299) B4626299
theorem B2191337 : Blo 1459549 2191337 := bstep (se 2 (by rfl) ⟨821751, by rfl⟩ : syracuseStep 2191337 = 1643503) B1643503
theorem B2191355 : Blo 1459549 2191355 := bstep (se 1 (by rfl) ⟨1643516, by rfl⟩ : syracuseStep 2191355 = 3287033) B3287033
theorem B2191391 : Blo 1459549 2191391 := bstep (se 1 (by rfl) ⟨1643543, by rfl⟩ : syracuseStep 2191391 = 3287087) B3287087
theorem B2191415 : Blo 1459549 2191415 := bstep (se 1 (by rfl) ⟨1643561, by rfl⟩ : syracuseStep 2191415 = 3287123) B3287123
theorem B2191535 : Blo 1459549 2191535 := bstep (se 1 (by rfl) ⟨1643651, by rfl⟩ : syracuseStep 2191535 = 3287303) B3287303
theorem B6754499 : Blo 1459549 6754499 := bstep (se 1 (by rfl) ⟨5065874, by rfl⟩ : syracuseStep 6754499 = 10131749) B10131749
theorem B3330323 : Blo 1459549 3330323 := bstep (se 1 (by rfl) ⟨2497742, by rfl⟩ : syracuseStep 3330323 = 4995485) B4995485
theorem B4624679 : Blo 1459549 4624679 := bstep (se 1 (by rfl) ⟨3468509, by rfl⟩ : syracuseStep 4624679 = 6937019) B6937019
theorem B2339113 : Blo 1459549 2339113 := bstep (se 2 (by rfl) ⟨877167, by rfl⟩ : syracuseStep 2339113 = 1754335) B1754335
theorem B7393679 : Blo 1459549 7393679 := bstep (se 1 (by rfl) ⟨5545259, by rfl⟩ : syracuseStep 7393679 = 11090519) B11090519
theorem B13316507 : Blo 1459549 13316507 := bstep (se 1 (by rfl) ⟨9987380, by rfl⟩ : syracuseStep 13316507 = 19974761) B19974761
theorem B1847863 : Blo 1459549 1847863 := bstep (se 1 (by rfl) ⟨1385897, by rfl⟩ : syracuseStep 1847863 = 2771795) B2771795
theorem B4158535 : Blo 1459549 4158535 := bstep (se 1 (by rfl) ⟨3118901, by rfl⟩ : syracuseStep 4158535 = 6237803) B6237803
theorem B6239443 : Blo 1459549 6239443 := bstep (se 1 (by rfl) ⟨4679582, by rfl⟩ : syracuseStep 6239443 = 9359165) B9359165
theorem B16627031 : Blo 1459549 16627031 := bstep (se 1 (by rfl) ⟨12470273, by rfl⟩ : syracuseStep 16627031 = 24940547) B24940547
theorem B67450259 : Blo 1459549 67450259 := bstep (se 1 (by rfl) ⟨50587694, by rfl⟩ : syracuseStep 67450259 = 101175389) B101175389
theorem B7394813 : Blo 1459549 7394813 := bstep (se 3 (by rfl) ⟨1386527, by rfl⟩ : syracuseStep 7394813 = 2773055) B2773055
theorem B18970301 : Blo 1459549 18970301 := bstep (se 3 (by rfl) ⟨3556931, by rfl⟩ : syracuseStep 18970301 = 7113863) B7113863
theorem B5543711 : Blo 1459549 5543711 := bstep (se 1 (by rfl) ⟨4157783, by rfl⟩ : syracuseStep 5543711 = 8315567) B8315567
theorem B5543741 : Blo 1459549 5543741 := bstep (se 3 (by rfl) ⟨1039451, by rfl⟩ : syracuseStep 5543741 = 2078903) B2078903
theorem B8320967 : Blo 1459549 8320967 := bstep (se 1 (by rfl) ⟨6240725, by rfl⟩ : syracuseStep 8320967 = 12481451) B12481451
theorem B5404967 : Blo 1459549 5404967 := bstep (se 1 (by rfl) ⟨4053725, by rfl⟩ : syracuseStep 5404967 = 8107451) B8107451
theorem B4159993 : Blo 1459549 4159993 := bstep (se 2 (by rfl) ⟨1559997, by rfl⟩ : syracuseStep 4159993 = 3119995) B3119995
theorem B5544683 : Blo 1459549 5544683 := bstep (se 1 (by rfl) ⟨4158512, by rfl⟩ : syracuseStep 5544683 = 8317025) B8317025
theorem B35527405 : Blo 1459549 35527405 := bstep (se 3 (by rfl) ⟨6661388, by rfl⟩ : syracuseStep 35527405 = 13322777) B13322777
theorem B9354041 : Blo 1459549 9354041 := bstep (se 2 (by rfl) ⟨3507765, by rfl⟩ : syracuseStep 9354041 = 7015531) B7015531
theorem B115416737 : Blo 1459549 115416737 := bstep (se 2 (by rfl) ⟨43281276, by rfl⟩ : syracuseStep 115416737 = 86562553) B86562553
theorem B2809721 : Blo 1459549 2809721 := bstep (se 2 (by rfl) ⟨1053645, by rfl⟩ : syracuseStep 2809721 = 2107291) B2107291
theorem B5545867 : Blo 1459549 5545867 := bstep (se 1 (by rfl) ⟨4159400, by rfl⟩ : syracuseStep 5545867 = 8318801) B8318801
theorem B2220215 : Blo 1459549 2220215 := bstep (se 1 (by rfl) ⟨1665161, by rfl⟩ : syracuseStep 2220215 = 3330323) B3330323
theorem B16629947 : Blo 1459549 16629947 := bstep (se 1 (by rfl) ⟨12472460, by rfl⟩ : syracuseStep 16629947 = 24944921) B24944921
theorem B44941711 : Blo 1459549 44941711 := bstep (se 1 (by rfl) ⟨33706283, by rfl⟩ : syracuseStep 44941711 = 67412567) B67412567
theorem B3695017 : Blo 1459549 3695017 := bstep (se 2 (by rfl) ⟨1385631, by rfl⟩ : syracuseStep 3695017 = 2771263) B2771263
theorem B153846337 : Blo 1459549 153846337 := bstep (se 2 (by rfl) ⟨57692376, by rfl⟩ : syracuseStep 153846337 = 115384753) B115384753
theorem B5546657 : Blo 1459549 5546657 := bstep (se 2 (by rfl) ⟨2079996, by rfl⟩ : syracuseStep 5546657 = 4159993) B4159993
theorem B11084687 : Blo 1459549 11084687 := bstep (se 1 (by rfl) ⟨8313515, by rfl⟩ : syracuseStep 11084687 = 16627031) B16627031
theorem B44966839 : Blo 1459549 44966839 := bstep (se 1 (by rfl) ⟨33725129, by rfl⟩ : syracuseStep 44966839 = 67450259) B67450259
theorem B3695807 : Blo 1459549 3695807 := bstep (se 1 (by rfl) ⟨2771855, by rfl⟩ : syracuseStep 3695807 = 5543711) B5543711
theorem B3695827 : Blo 1459549 3695827 := bstep (se 1 (by rfl) ⟨2771870, by rfl⟩ : syracuseStep 3695827 = 5543741) B5543741
theorem B5547311 : Blo 1459549 5547311 := bstep (se 1 (by rfl) ⟨4160483, by rfl⟩ : syracuseStep 5547311 = 8320967) B8320967
theorem B1459951 : Blo 1459549 1459951 := bstep (se 1 (by rfl) ⟨1094963, by rfl⟩ : syracuseStep 1459951 = 2189927) B2189927
theorem B3696455 : Blo 1459549 3696455 := bstep (se 1 (by rfl) ⟨2772341, by rfl⟩ : syracuseStep 3696455 = 5544683) B5544683
theorem B6236027 : Blo 1459549 6236027 := bstep (se 1 (by rfl) ⟨4677020, by rfl⟩ : syracuseStep 6236027 = 9354041) B9354041
theorem B1460135 : Blo 1459549 1460135 := bstep (se 1 (by rfl) ⟨1095101, by rfl⟩ : syracuseStep 1460135 = 2190203) B2190203
theorem B1460315 : Blo 1459549 1460315 := bstep (se 1 (by rfl) ⟨1095236, by rfl⟩ : syracuseStep 1460315 = 2190473) B2190473
theorem B1460351 : Blo 1459549 1460351 := bstep (se 1 (by rfl) ⟨1095263, by rfl⟩ : syracuseStep 1460351 = 2190527) B2190527
theorem B1558759 : Blo 1459549 1558759 := bstep (se 1 (by rfl) ⟨1169069, by rfl⟩ : syracuseStep 1558759 = 2338139) B2338139
theorem B1460711 : Blo 1459549 1460711 := bstep (se 1 (by rfl) ⟨1095533, by rfl⟩ : syracuseStep 1460711 = 2191067) B2191067
theorem B1460891 : Blo 1459549 1460891 := bstep (se 1 (by rfl) ⟨1095668, by rfl⟩ : syracuseStep 1460891 = 2191337) B2191337
theorem B1460903 : Blo 1459549 1460903 := bstep (se 1 (by rfl) ⟨1095677, by rfl⟩ : syracuseStep 1460903 = 2191355) B2191355
theorem B1460927 : Blo 1459549 1460927 := bstep (se 1 (by rfl) ⟨1095695, by rfl⟩ : syracuseStep 1460927 = 2191391) B2191391
theorem B1460943 : Blo 1459549 1460943 := bstep (se 1 (by rfl) ⟨1095707, by rfl⟩ : syracuseStep 1460943 = 2191415) B2191415
theorem B1461023 : Blo 1459549 1461023 := bstep (se 1 (by rfl) ⟨1095767, by rfl⟩ : syracuseStep 1461023 = 2191535) B2191535
theorem B3083119 : Blo 1459549 3083119 := bstep (se 1 (by rfl) ⟨2312339, by rfl⟩ : syracuseStep 3083119 = 4624679) B4624679
theorem B14028137 : Blo 1459549 14028137 := bstep (se 2 (by rfl) ⟨5260551, by rfl⟩ : syracuseStep 14028137 = 10521103) B10521103
theorem B47369873 : Blo 1459549 47369873 := bstep (se 2 (by rfl) ⟨17763702, by rfl⟩ : syracuseStep 47369873 = 35527405) B35527405
theorem B2191007 : Blo 1459549 2191007 := bstep (se 1 (by rfl) ⟨1643255, by rfl⟩ : syracuseStep 2191007 = 3286511) B3286511
theorem B4157419 : Blo 1459549 4157419 := bstep (se 1 (by rfl) ⟨3118064, by rfl⟩ : syracuseStep 4157419 = 6236129) B6236129
theorem B14037137 : Blo 1459549 14037137 := bstep (se 2 (by rfl) ⟨5263926, by rfl⟩ : syracuseStep 14037137 = 10527853) B10527853
theorem B8319257 : Blo 1459549 8319257 := bstep (se 2 (by rfl) ⟨3119721, by rfl⟩ : syracuseStep 8319257 = 6239443) B6239443
theorem B11842537 : Blo 1459549 11842537 := bstep (se 2 (by rfl) ⟨4440951, by rfl⟩ : syracuseStep 11842537 = 8881903) B8881903
theorem B1848415 : Blo 1459549 1848415 := bstep (se 1 (by rfl) ⟨1386311, by rfl⟩ : syracuseStep 1848415 = 2772623) B2772623
theorem B76944491 : Blo 1459549 76944491 := bstep (se 1 (by rfl) ⟨57708368, by rfl⟩ : syracuseStep 76944491 = 115416737) B115416737
theorem B7394489 : Blo 1459549 7394489 := bstep (se 2 (by rfl) ⟨2772933, by rfl⟩ : syracuseStep 7394489 = 5545867) B5545867
theorem B1873147 : Blo 1459549 1873147 := bstep (se 1 (by rfl) ⟨1404860, by rfl⟩ : syracuseStep 1873147 = 2809721) B2809721
theorem B5920199 : Blo 1459549 5920199 := bstep (se 1 (by rfl) ⟨4440149, by rfl⟩ : syracuseStep 5920199 = 8880299) B8880299
theorem B4502999 : Blo 1459549 4502999 := bstep (se 1 (by rfl) ⟨3377249, by rfl⟩ : syracuseStep 4502999 = 6754499) B6754499
theorem B5543423 : Blo 1459549 5543423 := bstep (se 1 (by rfl) ⟨4157567, by rfl⟩ : syracuseStep 5543423 = 8315135) B8315135
theorem B4929119 : Blo 1459549 4929119 := bstep (se 1 (by rfl) ⟨3696839, by rfl⟩ : syracuseStep 4929119 = 7393679) B7393679
theorem B8877671 : Blo 1459549 8877671 := bstep (se 1 (by rfl) ⟨6658253, by rfl⟩ : syracuseStep 8877671 = 13316507) B13316507
theorem B2463439 : Blo 1459549 2463439 := bstep (se 1 (by rfl) ⟨1847579, by rfl⟩ : syracuseStep 2463439 = 3695159) B3695159
theorem B3118799 : Blo 1459549 3118799 := bstep (se 1 (by rfl) ⟨2339099, by rfl⟩ : syracuseStep 3118799 = 4678199) B4678199
theorem B3118817 : Blo 1459549 3118817 := bstep (se 2 (by rfl) ⟨1169556, by rfl⟩ : syracuseStep 3118817 = 2339113) B2339113
theorem B2463527 : Blo 1459549 2463527 := bstep (se 1 (by rfl) ⟨1847645, by rfl⟩ : syracuseStep 2463527 = 3695291) B3695291
theorem B2463817 : Blo 1459549 2463817 := bstep (se 2 (by rfl) ⟨923931, by rfl⟩ : syracuseStep 2463817 = 1847863) B1847863
theorem B2463851 : Blo 1459549 2463851 := bstep (se 1 (by rfl) ⟨1847888, by rfl⟩ : syracuseStep 2463851 = 3695777) B3695777
theorem B15784075 : Blo 1459549 15784075 := bstep (se 1 (by rfl) ⟨11838056, by rfl⟩ : syracuseStep 15784075 = 23676113) B23676113
theorem B65796245 : Blo 1459549 65796245 := bstep (se 6 (by rfl) ⟨1542099, by rfl⟩ : syracuseStep 65796245 = 3084199) B3084199
theorem B4929875 : Blo 1459549 4929875 := bstep (se 1 (by rfl) ⟨3697406, by rfl⟩ : syracuseStep 4929875 = 7394813) B7394813
theorem B7395785 : Blo 1459549 7395785 := bstep (se 2 (by rfl) ⟨2773419, by rfl⟩ : syracuseStep 7395785 = 5546839) B5546839
theorem B12646867 : Blo 1459549 12646867 := bstep (se 1 (by rfl) ⟨9485150, by rfl⟩ : syracuseStep 12646867 = 18970301) B18970301
theorem B4676201 : Blo 1459549 4676201 := bstep (se 2 (by rfl) ⟨1753575, by rfl⟩ : syracuseStep 4676201 = 3507151) B3507151
theorem B5544713 : Blo 1459549 5544713 := bstep (se 2 (by rfl) ⟨2079267, by rfl⟩ : syracuseStep 5544713 = 4158535) B4158535
theorem B3603311 : Blo 1459549 3603311 := bstep (se 1 (by rfl) ⟨2702483, by rfl⟩ : syracuseStep 3603311 = 5404967) B5404967
theorem B2464823 : Blo 1459549 2464823 := bstep (se 1 (by rfl) ⟨1848617, by rfl⟩ : syracuseStep 2464823 = 3697235) B3697235
theorem B4930793 : Blo 1459549 4930793 := bstep (se 2 (by rfl) ⟨1849047, by rfl⟩ : syracuseStep 4930793 = 3698095) B3698095
theorem B2465383 : Blo 1459549 2465383 := bstep (se 1 (by rfl) ⟨1849037, by rfl⟩ : syracuseStep 2465383 = 3698075) B3698075
theorem B3284711 : Blo 1459549 3284711 := bstep (se 1 (by rfl) ⟨2463533, by rfl⟩ : syracuseStep 3284711 = 4927067) B4927067
theorem B12640139 : Blo 1459549 12640139 := bstep (se 1 (by rfl) ⟨9480104, by rfl⟩ : syracuseStep 12640139 = 18960209) B18960209
theorem B3285089 : Blo 1459549 3285089 := bstep (se 2 (by rfl) ⟨1231908, by rfl⟩ : syracuseStep 3285089 = 2463817) B2463817
theorem B21045433 : Blo 1459549 21045433 := bstep (se 2 (by rfl) ⟨7892037, by rfl⟩ : syracuseStep 21045433 = 15784075) B15784075
theorem B5546171 : Blo 1459549 5546171 := bstep (se 1 (by rfl) ⟨4159628, by rfl⟩ : syracuseStep 5546171 = 8319257) B8319257
theorem B7389791 : Blo 1459549 7389791 := bstep (se 1 (by rfl) ⟨5542343, by rfl⟩ : syracuseStep 7389791 = 11084687) B11084687
theorem B205128449 : Blo 1459549 205128449 := bstep (se 2 (by rfl) ⟨76923168, by rfl⟩ : syracuseStep 205128449 = 153846337) B153846337
theorem B3695615 : Blo 1459549 3695615 := bstep (se 1 (by rfl) ⟨2771711, by rfl⟩ : syracuseStep 3695615 = 5543423) B5543423
theorem B3286079 : Blo 1459549 3286079 := bstep (se 1 (by rfl) ⟨2464559, by rfl⟩ : syracuseStep 3286079 = 4929119) B4929119
theorem B3286583 : Blo 1459549 3286583 := bstep (se 1 (by rfl) ⟨2464937, by rfl⟩ : syracuseStep 3286583 = 4929875) B4929875
theorem B3696475 : Blo 1459549 3696475 := bstep (se 1 (by rfl) ⟨2772356, by rfl⟩ : syracuseStep 3696475 = 5544713) B5544713
theorem B2402207 : Blo 1459549 2402207 := bstep (se 1 (by rfl) ⟨1801655, by rfl⟩ : syracuseStep 2402207 = 3603311) B3603311
theorem B3287177 : Blo 1459549 3287177 := bstep (se 2 (by rfl) ⟨1232691, by rfl⟩ : syracuseStep 3287177 = 2465383) B2465383
theorem B3287195 : Blo 1459549 3287195 := bstep (se 1 (by rfl) ⟨2465396, by rfl⟩ : syracuseStep 3287195 = 4930793) B4930793
theorem B1460671 : Blo 1459549 1460671 := bstep (se 1 (by rfl) ⟨1095503, by rfl⟩ : syracuseStep 1460671 = 2191007) B2191007
theorem B2189807 : Blo 1459549 2189807 := bstep (se 1 (by rfl) ⟨1642355, by rfl⟩ : syracuseStep 2189807 = 3284711) B3284711
theorem B9358091 : Blo 1459549 9358091 := bstep (se 1 (by rfl) ⟨7018568, by rfl⟩ : syracuseStep 9358091 = 14037137) B14037137
theorem B11086631 : Blo 1459549 11086631 := bstep (se 1 (by rfl) ⟨8314973, by rfl⟩ : syracuseStep 11086631 = 16629947) B16629947
theorem B3697771 : Blo 1459549 3697771 := bstep (se 1 (by rfl) ⟨2773328, by rfl⟩ : syracuseStep 3697771 = 5546657) B5546657
theorem B4926689 : Blo 1459549 4926689 := bstep (se 2 (by rfl) ⟨1847508, by rfl⟩ : syracuseStep 4926689 = 3695017) B3695017
theorem B16862489 : Blo 1459549 16862489 := bstep (se 2 (by rfl) ⟨6323433, by rfl⟩ : syracuseStep 16862489 = 12646867) B12646867
theorem B3698207 : Blo 1459549 3698207 := bstep (se 1 (by rfl) ⟨2773655, by rfl⟩ : syracuseStep 3698207 = 5547311) B5547311
theorem B5918447 : Blo 1459549 5918447 := bstep (se 1 (by rfl) ⟨4438835, by rfl⟩ : syracuseStep 5918447 = 8877671) B8877671
theorem B1642351 : Blo 1459549 1642351 := bstep (se 1 (by rfl) ⟨1231763, by rfl⟩ : syracuseStep 1642351 = 2463527) B2463527
theorem B4157351 : Blo 1459549 4157351 := bstep (se 1 (by rfl) ⟨3118013, by rfl⟩ : syracuseStep 4157351 = 6236027) B6236027
theorem B15790049 : Blo 1459549 15790049 := bstep (se 2 (by rfl) ⟨5921268, by rfl⟩ : syracuseStep 15790049 = 11842537) B11842537
theorem B1642567 : Blo 1459549 1642567 := bstep (se 1 (by rfl) ⟨1231925, by rfl⟩ : syracuseStep 1642567 = 2463851) B2463851
theorem B43864163 : Blo 1459549 43864163 := bstep (se 1 (by rfl) ⟨32898122, by rfl⟩ : syracuseStep 43864163 = 65796245) B65796245
theorem B4927769 : Blo 1459549 4927769 := bstep (se 2 (by rfl) ⟨1847913, by rfl⟩ : syracuseStep 4927769 = 3695827) B3695827
theorem B3117467 : Blo 1459549 3117467 := bstep (se 1 (by rfl) ⟨2338100, by rfl⟩ : syracuseStep 3117467 = 4676201) B4676201
theorem B1643215 : Blo 1459549 1643215 := bstep (se 1 (by rfl) ⟨1232411, by rfl⟩ : syracuseStep 1643215 = 2464823) B2464823
theorem B9352091 : Blo 1459549 9352091 := bstep (se 1 (by rfl) ⟨7014068, by rfl⟩ : syracuseStep 9352091 = 14028137) B14028137
theorem B8426759 : Blo 1459549 8426759 := bstep (se 1 (by rfl) ⟨6320069, by rfl⟩ : syracuseStep 8426759 = 12640139) B12640139
theorem B5543225 : Blo 1459549 5543225 := bstep (se 2 (by rfl) ⟨2078709, by rfl⟩ : syracuseStep 5543225 = 4157419) B4157419
theorem B2078345 : Blo 1459549 2078345 := bstep (se 2 (by rfl) ⟨779379, by rfl⟩ : syracuseStep 2078345 = 1558759) B1558759
theorem B59922281 : Blo 1459549 59922281 := bstep (se 2 (by rfl) ⟨22470855, by rfl⟩ : syracuseStep 59922281 = 44941711) B44941711
theorem B51296327 : Blo 1459549 51296327 := bstep (se 1 (by rfl) ⟨38472245, by rfl⟩ : syracuseStep 51296327 = 76944491) B76944491
theorem B4929659 : Blo 1459549 4929659 := bstep (se 1 (by rfl) ⟨3697244, by rfl⟩ : syracuseStep 4929659 = 7394489) B7394489
theorem B2463871 : Blo 1459549 2463871 := bstep (se 1 (by rfl) ⟨1847903, by rfl⟩ : syracuseStep 2463871 = 3695807) B3695807
theorem B3946799 : Blo 1459549 3946799 := bstep (se 1 (by rfl) ⟨2960099, by rfl⟩ : syracuseStep 3946799 = 5920199) B5920199
theorem B2079199 : Blo 1459549 2079199 := bstep (se 1 (by rfl) ⟨1559399, by rfl⟩ : syracuseStep 2079199 = 3118799) B3118799
theorem B2079211 : Blo 1459549 2079211 := bstep (se 1 (by rfl) ⟨1559408, by rfl⟩ : syracuseStep 2079211 = 3118817) B3118817
theorem B2464303 : Blo 1459549 2464303 := bstep (se 1 (by rfl) ⟨1848227, by rfl⟩ : syracuseStep 2464303 = 3696455) B3696455
theorem B12007997 : Blo 1459549 12007997 := bstep (se 3 (by rfl) ⟨2251499, by rfl⟩ : syracuseStep 12007997 = 4502999) B4502999
theorem B59955785 : Blo 1459549 59955785 := bstep (se 2 (by rfl) ⟨22483419, by rfl⟩ : syracuseStep 59955785 = 44966839) B44966839
theorem B2464553 : Blo 1459549 2464553 := bstep (se 2 (by rfl) ⟨924207, by rfl⟩ : syracuseStep 2464553 = 1848415) B1848415
theorem B4930523 : Blo 1459549 4930523 := bstep (se 1 (by rfl) ⟨3697892, by rfl⟩ : syracuseStep 4930523 = 7395785) B7395785
theorem B2497529 : Blo 1459549 2497529 := bstep (se 2 (by rfl) ⟨936573, by rfl⟩ : syracuseStep 2497529 = 1873147) B1873147
theorem B23682293 : Blo 1459549 23682293 := bstep (se 5 (by rfl) ⟨1110107, by rfl⟩ : syracuseStep 23682293 = 2220215) B2220215
theorem B3284585 : Blo 1459549 3284585 := bstep (se 2 (by rfl) ⟨1231719, by rfl⟩ : syracuseStep 3284585 = 2463439) B2463439
theorem B65773205 : Blo 1459549 65773205 := bstep (se 6 (by rfl) ⟨1541559, by rfl⟩ : syracuseStep 65773205 = 3083119) B3083119
theorem B31579915 : Blo 1459549 31579915 := bstep (se 1 (by rfl) ⟨23684936, by rfl⟩ : syracuseStep 31579915 = 47369873) B47369873
theorem B3285161 : Blo 1459549 3285161 := bstep (se 2 (by rfl) ⟨1231935, by rfl⟩ : syracuseStep 3285161 = 2463871) B2463871
theorem B3285179 : Blo 1459549 3285179 := bstep (se 1 (by rfl) ⟨2463884, by rfl⟩ : syracuseStep 3285179 = 4927769) B4927769
theorem B6234727 : Blo 1459549 6234727 := bstep (se 1 (by rfl) ⟨4676045, by rfl⟩ : syracuseStep 6234727 = 9352091) B9352091
theorem B22471357 : Blo 1459549 22471357 := bstep (se 3 (by rfl) ⟨4213379, by rfl⟩ : syracuseStep 22471357 = 8426759) B8426759
theorem B3285737 : Blo 1459549 3285737 := bstep (se 2 (by rfl) ⟨1232151, by rfl⟩ : syracuseStep 3285737 = 2464303) B2464303
theorem B3695483 : Blo 1459549 3695483 := bstep (se 1 (by rfl) ⟨2771612, by rfl⟩ : syracuseStep 3695483 = 5543225) B5543225
theorem B3286439 : Blo 1459549 3286439 := bstep (se 1 (by rfl) ⟨2464829, by rfl⟩ : syracuseStep 3286439 = 4929659) B4929659
theorem B2631199 : Blo 1459549 2631199 := bstep (se 1 (by rfl) ⟨1973399, by rfl⟩ : syracuseStep 2631199 = 3946799) B3946799
theorem B1459871 : Blo 1459549 1459871 := bstep (se 1 (by rfl) ⟨1094903, by rfl⟩ : syracuseStep 1459871 = 2189807) B2189807
theorem B8005331 : Blo 1459549 8005331 := bstep (se 1 (by rfl) ⟨6003998, by rfl⟩ : syracuseStep 8005331 = 12007997) B12007997
theorem B39970523 : Blo 1459549 39970523 := bstep (se 1 (by rfl) ⟨29977892, by rfl⟩ : syracuseStep 39970523 = 59955785) B59955785
theorem B7391087 : Blo 1459549 7391087 := bstep (se 1 (by rfl) ⟨5543315, by rfl⟩ : syracuseStep 7391087 = 11086631) B11086631
theorem B3287015 : Blo 1459549 3287015 := bstep (se 1 (by rfl) ⟨2465261, by rfl⟩ : syracuseStep 3287015 = 4930523) B4930523
theorem B1665019 : Blo 1459549 1665019 := bstep (se 1 (by rfl) ⟨1248764, by rfl⟩ : syracuseStep 1665019 = 2497529) B2497529
theorem B15788195 : Blo 1459549 15788195 := bstep (se 1 (by rfl) ⟨11841146, by rfl⟩ : syracuseStep 15788195 = 23682293) B23682293
theorem B11241659 : Blo 1459549 11241659 := bstep (se 1 (by rfl) ⟨8431244, by rfl⟩ : syracuseStep 11241659 = 16862489) B16862489
theorem B2189723 : Blo 1459549 2189723 := bstep (se 1 (by rfl) ⟨1642292, by rfl⟩ : syracuseStep 2189723 = 3284585) B3284585
theorem B2189801 : Blo 1459549 2189801 := bstep (se 2 (by rfl) ⟨821175, by rfl⟩ : syracuseStep 2189801 = 1642351) B1642351
theorem B2771567 : Blo 1459549 2771567 := bstep (se 1 (by rfl) ⟨2078675, by rfl⟩ : syracuseStep 2771567 = 4157351) B4157351
theorem B2190059 : Blo 1459549 2190059 := bstep (se 1 (by rfl) ⟨1642544, by rfl⟩ : syracuseStep 2190059 = 3285089) B3285089
theorem B2190089 : Blo 1459549 2190089 := bstep (se 2 (by rfl) ⟨821283, by rfl⟩ : syracuseStep 2190089 = 1642567) B1642567
theorem B3697447 : Blo 1459549 3697447 := bstep (se 1 (by rfl) ⟨2773085, by rfl⟩ : syracuseStep 3697447 = 5546171) B5546171
theorem B28060577 : Blo 1459549 28060577 := bstep (se 2 (by rfl) ⟨10522716, by rfl⟩ : syracuseStep 28060577 = 21045433) B21045433
theorem B4926527 : Blo 1459549 4926527 := bstep (se 1 (by rfl) ⟨3694895, by rfl⟩ : syracuseStep 4926527 = 7389791) B7389791
theorem B136752299 : Blo 1459549 136752299 := bstep (se 1 (by rfl) ⟨102564224, by rfl⟩ : syracuseStep 136752299 = 205128449) B205128449
theorem B2772281 : Blo 1459549 2772281 := bstep (se 2 (by rfl) ⟨1039605, by rfl⟩ : syracuseStep 2772281 = 2079211) B2079211
theorem B2190719 : Blo 1459549 2190719 := bstep (se 1 (by rfl) ⟨1643039, by rfl⟩ : syracuseStep 2190719 = 3286079) B3286079
theorem B2190953 : Blo 1459549 2190953 := bstep (se 2 (by rfl) ⟨821607, by rfl⟩ : syracuseStep 2190953 = 1643215) B1643215
theorem B2191055 : Blo 1459549 2191055 := bstep (se 1 (by rfl) ⟨1643291, by rfl⟩ : syracuseStep 2191055 = 3286583) B3286583
theorem B39948187 : Blo 1459549 39948187 := bstep (se 1 (by rfl) ⟨29961140, by rfl⟩ : syracuseStep 39948187 = 59922281) B59922281
theorem B1601471 : Blo 1459549 1601471 := bstep (se 1 (by rfl) ⟨1201103, by rfl⟩ : syracuseStep 1601471 = 2402207) B2402207
theorem B34197551 : Blo 1459549 34197551 := bstep (se 1 (by rfl) ⟨25648163, by rfl⟩ : syracuseStep 34197551 = 51296327) B51296327
theorem B2191451 : Blo 1459549 2191451 := bstep (se 1 (by rfl) ⟨1643588, by rfl⟩ : syracuseStep 2191451 = 3287177) B3287177
theorem B2191463 : Blo 1459549 2191463 := bstep (se 1 (by rfl) ⟨1643597, by rfl⟩ : syracuseStep 2191463 = 3287195) B3287195
theorem B5542253 : Blo 1459549 5542253 := bstep (se 3 (by rfl) ⟨1039172, by rfl⟩ : syracuseStep 5542253 = 2078345) B2078345
theorem B6238727 : Blo 1459549 6238727 := bstep (se 1 (by rfl) ⟨4679045, by rfl⟩ : syracuseStep 6238727 = 9358091) B9358091
theorem B1643035 : Blo 1459549 1643035 := bstep (se 1 (by rfl) ⟨1232276, by rfl⟩ : syracuseStep 1643035 = 2464553) B2464553
theorem B43848803 : Blo 1459549 43848803 := bstep (se 1 (by rfl) ⟨32886602, by rfl⟩ : syracuseStep 43848803 = 65773205) B65773205
theorem B4928633 : Blo 1459549 4928633 := bstep (se 2 (by rfl) ⟨1848237, by rfl⟩ : syracuseStep 4928633 = 3696475) B3696475
theorem B3945631 : Blo 1459549 3945631 := bstep (se 1 (by rfl) ⟨2959223, by rfl⟩ : syracuseStep 3945631 = 5918447) B5918447
theorem B11089061 : Blo 1459549 11089061 := bstep (se 4 (by rfl) ⟨1039599, by rfl⟩ : syracuseStep 11089061 = 2079199) B2079199
theorem B29242775 : Blo 1459549 29242775 := bstep (se 1 (by rfl) ⟨21932081, by rfl⟩ : syracuseStep 29242775 = 43864163) B43864163
theorem B2078311 : Blo 1459549 2078311 := bstep (se 1 (by rfl) ⟨1558733, by rfl⟩ : syracuseStep 2078311 = 3117467) B3117467
theorem B2463743 : Blo 1459549 2463743 := bstep (se 1 (by rfl) ⟨1847807, by rfl⟩ : syracuseStep 2463743 = 3695615) B3695615
theorem B4930361 : Blo 1459549 4930361 := bstep (se 2 (by rfl) ⟨1848885, by rfl⟩ : syracuseStep 4930361 = 3697771) B3697771
theorem B3284459 : Blo 1459549 3284459 := bstep (se 1 (by rfl) ⟨2463344, by rfl⟩ : syracuseStep 3284459 = 4926689) B4926689
theorem B42106553 : Blo 1459549 42106553 := bstep (se 2 (by rfl) ⟨15789957, by rfl⟩ : syracuseStep 42106553 = 31579915) B31579915
theorem B2465471 : Blo 1459549 2465471 := bstep (se 1 (by rfl) ⟨1849103, by rfl⟩ : syracuseStep 2465471 = 3698207) B3698207
theorem B10526699 : Blo 1459549 10526699 := bstep (se 1 (by rfl) ⟨7895024, by rfl⟩ : syracuseStep 10526699 = 15790049) B15790049
theorem B22798367 : Blo 1459549 22798367 := bstep (se 1 (by rfl) ⟨17098775, by rfl⟩ : syracuseStep 22798367 = 34197551) B34197551
theorem B3694835 : Blo 1459549 3694835 := bstep (se 1 (by rfl) ⟨2771126, by rfl⟩ : syracuseStep 3694835 = 5542253) B5542253
theorem B3285755 : Blo 1459549 3285755 := bstep (se 1 (by rfl) ⟨2464316, by rfl⟩ : syracuseStep 3285755 = 4928633) B4928633
theorem B5260841 : Blo 1459549 5260841 := bstep (se 2 (by rfl) ⟨1972815, by rfl⟩ : syracuseStep 5260841 = 3945631) B3945631
theorem B1459815 : Blo 1459549 1459815 := bstep (se 1 (by rfl) ⟨1094861, by rfl⟩ : syracuseStep 1459815 = 2189723) B2189723
theorem B1459867 : Blo 1459549 1459867 := bstep (se 1 (by rfl) ⟨1094900, by rfl⟩ : syracuseStep 1459867 = 2189801) B2189801
theorem B1460039 : Blo 1459549 1460039 := bstep (se 1 (by rfl) ⟨1095029, by rfl⟩ : syracuseStep 1460039 = 2190059) B2190059
theorem B1460059 : Blo 1459549 1460059 := bstep (se 1 (by rfl) ⟨1095044, by rfl⟩ : syracuseStep 1460059 = 2190089) B2190089
theorem B3286907 : Blo 1459549 3286907 := bstep (se 1 (by rfl) ⟨2465180, by rfl⟩ : syracuseStep 3286907 = 4930361) B4930361
theorem B106588061 : Blo 1459549 106588061 := bstep (se 3 (by rfl) ⟨19985261, by rfl⟩ : syracuseStep 106588061 = 39970523) B39970523
theorem B3508265 : Blo 1459549 3508265 := bstep (se 2 (by rfl) ⟨1315599, by rfl⟩ : syracuseStep 3508265 = 2631199) B2631199
theorem B2771081 : Blo 1459549 2771081 := bstep (se 2 (by rfl) ⟨1039155, by rfl⟩ : syracuseStep 2771081 = 2078311) B2078311
theorem B1460479 : Blo 1459549 1460479 := bstep (se 1 (by rfl) ⟨1095359, by rfl⟩ : syracuseStep 1460479 = 2190719) B2190719
theorem B2189639 : Blo 1459549 2189639 := bstep (se 1 (by rfl) ⟨1642229, by rfl⟩ : syracuseStep 2189639 = 3284459) B3284459
theorem B1460635 : Blo 1459549 1460635 := bstep (se 1 (by rfl) ⟨1095476, by rfl⟩ : syracuseStep 1460635 = 2190953) B2190953
theorem B1460703 : Blo 1459549 1460703 := bstep (se 1 (by rfl) ⟨1095527, by rfl⟩ : syracuseStep 1460703 = 2191055) B2191055
theorem B4270589 : Blo 1459549 4270589 := bstep (se 3 (by rfl) ⟨800735, by rfl⟩ : syracuseStep 4270589 = 1601471) B1601471
theorem B1460967 : Blo 1459549 1460967 := bstep (se 1 (by rfl) ⟨1095725, by rfl⟩ : syracuseStep 1460967 = 2191451) B2191451
theorem B1460975 : Blo 1459549 1460975 := bstep (se 1 (by rfl) ⟨1095731, by rfl⟩ : syracuseStep 1460975 = 2191463) B2191463
theorem B2190107 : Blo 1459549 2190107 := bstep (se 1 (by rfl) ⟨1642580, by rfl⟩ : syracuseStep 2190107 = 3285161) B3285161
theorem B2190119 : Blo 1459549 2190119 := bstep (se 1 (by rfl) ⟨1642589, by rfl⟩ : syracuseStep 2190119 = 3285179) B3285179
theorem B2190491 : Blo 1459549 2190491 := bstep (se 1 (by rfl) ⟨1642868, by rfl⟩ : syracuseStep 2190491 = 3285737) B3285737
theorem B2190713 : Blo 1459549 2190713 := bstep (se 2 (by rfl) ⟨821517, by rfl⟩ : syracuseStep 2190713 = 1643035) B1643035
theorem B29232535 : Blo 1459549 29232535 := bstep (se 1 (by rfl) ⟨21924401, by rfl⟩ : syracuseStep 29232535 = 43848803) B43848803
theorem B7392707 : Blo 1459549 7392707 := bstep (se 1 (by rfl) ⟨5544530, by rfl⟩ : syracuseStep 7392707 = 11089061) B11089061
theorem B29961809 : Blo 1459549 29961809 := bstep (se 2 (by rfl) ⟨11235678, by rfl⟩ : syracuseStep 29961809 = 22471357) B22471357
theorem B2190959 : Blo 1459549 2190959 := bstep (se 1 (by rfl) ⟨1643219, by rfl⟩ : syracuseStep 2190959 = 3286439) B3286439
theorem B4927391 : Blo 1459549 4927391 := bstep (se 1 (by rfl) ⟨3695543, by rfl⟩ : syracuseStep 4927391 = 7391087) B7391087
theorem B2191343 : Blo 1459549 2191343 := bstep (se 1 (by rfl) ⟨1643507, by rfl⟩ : syracuseStep 2191343 = 3287015) B3287015
theorem B1642495 : Blo 1459549 1642495 := bstep (se 1 (by rfl) ⟨1231871, by rfl⟩ : syracuseStep 1642495 = 2463743) B2463743
theorem B1847711 : Blo 1459549 1847711 := bstep (se 1 (by rfl) ⟨1385783, by rfl⟩ : syracuseStep 1847711 = 2771567) B2771567
theorem B18707051 : Blo 1459549 18707051 := bstep (se 1 (by rfl) ⟨14030288, by rfl⟩ : syracuseStep 18707051 = 28060577) B28060577
theorem B1848187 : Blo 1459549 1848187 := bstep (se 1 (by rfl) ⟨1386140, by rfl⟩ : syracuseStep 1848187 = 2772281) B2772281
theorem B28071035 : Blo 1459549 28071035 := bstep (se 1 (by rfl) ⟨21053276, by rfl⟩ : syracuseStep 28071035 = 42106553) B42106553
theorem B1643647 : Blo 1459549 1643647 := bstep (se 1 (by rfl) ⟨1232735, by rfl⟩ : syracuseStep 1643647 = 2465471) B2465471
theorem B7017799 : Blo 1459549 7017799 := bstep (se 1 (by rfl) ⟨5263349, by rfl⟩ : syracuseStep 7017799 = 10526699) B10526699
theorem B4159151 : Blo 1459549 4159151 := bstep (se 1 (by rfl) ⟨3119363, by rfl⟩ : syracuseStep 4159151 = 6238727) B6238727
theorem B2463655 : Blo 1459549 2463655 := bstep (se 1 (by rfl) ⟨1847741, by rfl⟩ : syracuseStep 2463655 = 3695483) B3695483
theorem B8312969 : Blo 1459549 8312969 := bstep (se 2 (by rfl) ⟨3117363, by rfl⟩ : syracuseStep 8312969 = 6234727) B6234727
theorem B19495183 : Blo 1459549 19495183 := bstep (se 1 (by rfl) ⟨14621387, by rfl⟩ : syracuseStep 19495183 = 29242775) B29242775
theorem B4929929 : Blo 1459549 4929929 := bstep (se 2 (by rfl) ⟨1848723, by rfl⟩ : syracuseStep 4929929 = 3697447) B3697447
theorem B10525463 : Blo 1459549 10525463 := bstep (se 1 (by rfl) ⟨7894097, by rfl⟩ : syracuseStep 10525463 = 15788195) B15788195
theorem B7494439 : Blo 1459549 7494439 := bstep (se 1 (by rfl) ⟨5620829, by rfl⟩ : syracuseStep 7494439 = 11241659) B11241659
theorem B21347549 : Blo 1459549 21347549 := bstep (se 3 (by rfl) ⟨4002665, by rfl⟩ : syracuseStep 21347549 = 8005331) B8005331
theorem B3284351 : Blo 1459549 3284351 := bstep (se 1 (by rfl) ⟨2463263, by rfl⟩ : syracuseStep 3284351 = 4926527) B4926527
theorem B91168199 : Blo 1459549 91168199 := bstep (se 1 (by rfl) ⟨68376149, by rfl⟩ : syracuseStep 91168199 = 136752299) B136752299
theorem B53264249 : Blo 1459549 53264249 := bstep (se 2 (by rfl) ⟨19974093, by rfl⟩ : syracuseStep 53264249 = 39948187) B39948187
theorem B8880101 : Blo 1459549 8880101 := bstep (se 4 (by rfl) ⟨832509, by rfl⟩ : syracuseStep 8880101 = 1665019) B1665019
theorem B25993577 : Blo 1459549 25993577 := bstep (se 2 (by rfl) ⟨9747591, by rfl⟩ : syracuseStep 25993577 = 19495183) B19495183
theorem B3507227 : Blo 1459549 3507227 := bstep (se 1 (by rfl) ⟨2630420, by rfl⟩ : syracuseStep 3507227 = 5260841) B5260841
theorem B71058707 : Blo 1459549 71058707 := bstep (se 1 (by rfl) ⟨53294030, by rfl⟩ : syracuseStep 71058707 = 106588061) B106588061
theorem B1459759 : Blo 1459549 1459759 := bstep (se 1 (by rfl) ⟨1094819, by rfl⟩ : syracuseStep 1459759 = 2189639) B2189639
theorem B3286619 : Blo 1459549 3286619 := bstep (se 1 (by rfl) ⟨2464964, by rfl⟩ : syracuseStep 3286619 = 4929929) B4929929
theorem B9357065 : Blo 1459549 9357065 := bstep (se 2 (by rfl) ⟨3508899, by rfl⟩ : syracuseStep 9357065 = 7017799) B7017799
theorem B1460071 : Blo 1459549 1460071 := bstep (se 1 (by rfl) ⟨1095053, by rfl⟩ : syracuseStep 1460071 = 2190107) B2190107
theorem B1460079 : Blo 1459549 1460079 := bstep (se 1 (by rfl) ⟨1095059, by rfl⟩ : syracuseStep 1460079 = 2190119) B2190119
theorem B1460327 : Blo 1459549 1460327 := bstep (se 1 (by rfl) ⟨1095245, by rfl⟩ : syracuseStep 1460327 = 2190491) B2190491
theorem B14231699 : Blo 1459549 14231699 := bstep (se 1 (by rfl) ⟨10673774, by rfl⟩ : syracuseStep 14231699 = 21347549) B21347549
theorem B1460475 : Blo 1459549 1460475 := bstep (se 1 (by rfl) ⟨1095356, by rfl⟩ : syracuseStep 1460475 = 2190713) B2190713
theorem B2189567 : Blo 1459549 2189567 := bstep (se 1 (by rfl) ⟨1642175, by rfl⟩ : syracuseStep 2189567 = 3284351) B3284351
theorem B60778799 : Blo 1459549 60778799 := bstep (se 1 (by rfl) ⟨45584099, by rfl⟩ : syracuseStep 60778799 = 91168199) B91168199
theorem B19974539 : Blo 1459549 19974539 := bstep (se 1 (by rfl) ⟨14980904, by rfl⟩ : syracuseStep 19974539 = 29961809) B29961809
theorem B1460639 : Blo 1459549 1460639 := bstep (se 1 (by rfl) ⟨1095479, by rfl⟩ : syracuseStep 1460639 = 2190959) B2190959
theorem B1460895 : Blo 1459549 1460895 := bstep (se 1 (by rfl) ⟨1095671, by rfl⟩ : syracuseStep 1460895 = 2191343) B2191343
theorem B2189993 : Blo 1459549 2189993 := bstep (se 2 (by rfl) ⟨821247, by rfl⟩ : syracuseStep 2189993 = 1642495) B1642495
theorem B15198911 : Blo 1459549 15198911 := bstep (se 1 (by rfl) ⟨11399183, by rfl⟩ : syracuseStep 15198911 = 22798367) B22798367
theorem B12471367 : Blo 1459549 12471367 := bstep (se 1 (by rfl) ⟨9353525, by rfl⟩ : syracuseStep 12471367 = 18707051) B18707051
theorem B2190503 : Blo 1459549 2190503 := bstep (se 1 (by rfl) ⟨1642877, by rfl⟩ : syracuseStep 2190503 = 3285755) B3285755
theorem B18714023 : Blo 1459549 18714023 := bstep (se 1 (by rfl) ⟨14035517, by rfl⟩ : syracuseStep 18714023 = 28071035) B28071035
theorem B4927229 : Blo 1459549 4927229 := bstep (se 3 (by rfl) ⟨923855, by rfl⟩ : syracuseStep 4927229 = 1847711) B1847711
theorem B2772767 : Blo 1459549 2772767 := bstep (se 1 (by rfl) ⟨2079575, by rfl⟩ : syracuseStep 2772767 = 4159151) B4159151
theorem B2191271 : Blo 1459549 2191271 := bstep (se 1 (by rfl) ⟨1643453, by rfl⟩ : syracuseStep 2191271 = 3286907) B3286907
theorem B2338843 : Blo 1459549 2338843 := bstep (se 1 (by rfl) ⟨1754132, by rfl⟩ : syracuseStep 2338843 = 3508265) B3508265
theorem B5541979 : Blo 1459549 5541979 := bstep (se 1 (by rfl) ⟨4156484, by rfl⟩ : syracuseStep 5541979 = 8312969) B8312969
theorem B1847387 : Blo 1459549 1847387 := bstep (se 1 (by rfl) ⟨1385540, by rfl⟩ : syracuseStep 1847387 = 2771081) B2771081
theorem B2191529 : Blo 1459549 2191529 := bstep (se 2 (by rfl) ⟨821823, by rfl⟩ : syracuseStep 2191529 = 1643647) B1643647
theorem B2847059 : Blo 1459549 2847059 := bstep (se 1 (by rfl) ⟨2135294, by rfl⟩ : syracuseStep 2847059 = 4270589) B4270589
theorem B7016975 : Blo 1459549 7016975 := bstep (se 1 (by rfl) ⟨5262731, by rfl⟩ : syracuseStep 7016975 = 10525463) B10525463
theorem B4928471 : Blo 1459549 4928471 := bstep (se 1 (by rfl) ⟨3696353, by rfl⟩ : syracuseStep 4928471 = 7392707) B7392707
theorem B35509499 : Blo 1459549 35509499 := bstep (se 1 (by rfl) ⟨26632124, by rfl⟩ : syracuseStep 35509499 = 53264249) B53264249
theorem B5920067 : Blo 1459549 5920067 := bstep (se 1 (by rfl) ⟨4440050, by rfl⟩ : syracuseStep 5920067 = 8880101) B8880101
theorem B2463223 : Blo 1459549 2463223 := bstep (se 1 (by rfl) ⟨1847417, by rfl⟩ : syracuseStep 2463223 = 3694835) B3694835
theorem B9992585 : Blo 1459549 9992585 := bstep (se 2 (by rfl) ⟨3747219, by rfl⟩ : syracuseStep 9992585 = 7494439) B7494439
theorem B2464249 : Blo 1459549 2464249 := bstep (se 2 (by rfl) ⟨924093, by rfl⟩ : syracuseStep 2464249 = 1848187) B1848187
theorem B38976713 : Blo 1459549 38976713 := bstep (se 2 (by rfl) ⟨14616267, by rfl⟩ : syracuseStep 38976713 = 29232535) B29232535
theorem B3284873 : Blo 1459549 3284873 := bstep (se 2 (by rfl) ⟨1231827, by rfl⟩ : syracuseStep 3284873 = 2463655) B2463655
theorem B3284927 : Blo 1459549 3284927 := bstep (se 1 (by rfl) ⟨2463695, by rfl⟩ : syracuseStep 3284927 = 4927391) B4927391
theorem B7389305 : Blo 1459549 7389305 := bstep (se 2 (by rfl) ⟨2770989, by rfl⟩ : syracuseStep 7389305 = 5541979) B5541979
theorem B4677983 : Blo 1459549 4677983 := bstep (se 1 (by rfl) ⟨3508487, by rfl⟩ : syracuseStep 4677983 = 7016975) B7016975
theorem B3285647 : Blo 1459549 3285647 := bstep (se 1 (by rfl) ⟨2464235, by rfl⟩ : syracuseStep 3285647 = 4928471) B4928471
theorem B3285665 : Blo 1459549 3285665 := bstep (se 2 (by rfl) ⟨1232124, by rfl⟩ : syracuseStep 3285665 = 2464249) B2464249
theorem B9487799 : Blo 1459549 9487799 := bstep (se 1 (by rfl) ⟨7115849, by rfl⟩ : syracuseStep 9487799 = 14231699) B14231699
theorem B15786845 : Blo 1459549 15786845 := bstep (se 3 (by rfl) ⟨2960033, by rfl⟩ : syracuseStep 15786845 = 5920067) B5920067
theorem B1459711 : Blo 1459549 1459711 := bstep (se 1 (by rfl) ⟨1094783, by rfl⟩ : syracuseStep 1459711 = 2189567) B2189567
theorem B40519199 : Blo 1459549 40519199 := bstep (se 1 (by rfl) ⟨30389399, by rfl⟩ : syracuseStep 40519199 = 60778799) B60778799
theorem B6661723 : Blo 1459549 6661723 := bstep (se 1 (by rfl) ⟨4996292, by rfl⟩ : syracuseStep 6661723 = 9992585) B9992585
theorem B1459995 : Blo 1459549 1459995 := bstep (se 1 (by rfl) ⟨1094996, by rfl⟩ : syracuseStep 1459995 = 2189993) B2189993
theorem B1460335 : Blo 1459549 1460335 := bstep (se 1 (by rfl) ⟨1095251, by rfl⟩ : syracuseStep 1460335 = 2190503) B2190503
theorem B2189915 : Blo 1459549 2189915 := bstep (se 1 (by rfl) ⟨1642436, by rfl⟩ : syracuseStep 2189915 = 3284873) B3284873
theorem B1460847 : Blo 1459549 1460847 := bstep (se 1 (by rfl) ⟨1095635, by rfl⟩ : syracuseStep 1460847 = 2191271) B2191271
theorem B2189951 : Blo 1459549 2189951 := bstep (se 1 (by rfl) ⟨1642463, by rfl⟩ : syracuseStep 2189951 = 3284927) B3284927
theorem B1461019 : Blo 1459549 1461019 := bstep (se 1 (by rfl) ⟨1095764, by rfl⟩ : syracuseStep 1461019 = 2191529) B2191529
theorem B17329051 : Blo 1459549 17329051 := bstep (se 1 (by rfl) ⟨12996788, by rfl⟩ : syracuseStep 17329051 = 25993577) B25993577
theorem B4926365 : Blo 1459549 4926365 := bstep (se 3 (by rfl) ⟨923693, by rfl⟩ : syracuseStep 4926365 = 1847387) B1847387
theorem B2338151 : Blo 1459549 2338151 := bstep (se 1 (by rfl) ⟨1753613, by rfl⟩ : syracuseStep 2338151 = 3507227) B3507227
theorem B2191079 : Blo 1459549 2191079 := bstep (se 1 (by rfl) ⟨1643309, by rfl⟩ : syracuseStep 2191079 = 3286619) B3286619
theorem B6238043 : Blo 1459549 6238043 := bstep (se 1 (by rfl) ⟨4678532, by rfl⟩ : syracuseStep 6238043 = 9357065) B9357065
theorem B13316359 : Blo 1459549 13316359 := bstep (se 1 (by rfl) ⟨9987269, by rfl⟩ : syracuseStep 13316359 = 19974539) B19974539
theorem B1848511 : Blo 1459549 1848511 := bstep (se 1 (by rfl) ⟨1386383, by rfl⟩ : syracuseStep 1848511 = 2772767) B2772767
theorem B3118457 : Blo 1459549 3118457 := bstep (se 2 (by rfl) ⟨1169421, by rfl⟩ : syracuseStep 3118457 = 2338843) B2338843
theorem B1898039 : Blo 1459549 1898039 := bstep (se 1 (by rfl) ⟨1423529, by rfl⟩ : syracuseStep 1898039 = 2847059) B2847059
theorem B23672999 : Blo 1459549 23672999 := bstep (se 1 (by rfl) ⟨17754749, by rfl⟩ : syracuseStep 23672999 = 35509499) B35509499
theorem B47372471 : Blo 1459549 47372471 := bstep (se 1 (by rfl) ⟨35529353, by rfl⟩ : syracuseStep 47372471 = 71058707) B71058707
theorem B16628489 : Blo 1459549 16628489 := bstep (se 2 (by rfl) ⟨6235683, by rfl⟩ : syracuseStep 16628489 = 12471367) B12471367
theorem B10132607 : Blo 1459549 10132607 := bstep (se 1 (by rfl) ⟨7599455, by rfl⟩ : syracuseStep 10132607 = 15198911) B15198911
theorem B3284297 : Blo 1459549 3284297 := bstep (se 2 (by rfl) ⟨1231611, by rfl⟩ : syracuseStep 3284297 = 2463223) B2463223
theorem B25984475 : Blo 1459549 25984475 := bstep (se 1 (by rfl) ⟨19488356, by rfl⟩ : syracuseStep 25984475 = 38976713) B38976713
theorem B12476015 : Blo 1459549 12476015 := bstep (se 1 (by rfl) ⟨9357011, by rfl⟩ : syracuseStep 12476015 = 18714023) B18714023
theorem B3284819 : Blo 1459549 3284819 := bstep (se 1 (by rfl) ⟨2463614, by rfl⟩ : syracuseStep 3284819 = 4927229) B4927229
theorem B63127997 : Blo 1459549 63127997 := bstep (se 3 (by rfl) ⟨11836499, by rfl⟩ : syracuseStep 63127997 = 23672999) B23672999
theorem B6235069 : Blo 1459549 6235069 := bstep (se 3 (by rfl) ⟨1169075, by rfl⟩ : syracuseStep 6235069 = 2338151) B2338151
theorem B6325199 : Blo 1459549 6325199 := bstep (se 1 (by rfl) ⟨4743899, by rfl⟩ : syracuseStep 6325199 = 9487799) B9487799
theorem B8315885 : Blo 1459549 8315885 := bstep (se 3 (by rfl) ⟨1559228, by rfl⟩ : syracuseStep 8315885 = 3118457) B3118457
theorem B31581647 : Blo 1459549 31581647 := bstep (se 1 (by rfl) ⟨23686235, by rfl⟩ : syracuseStep 31581647 = 47372471) B47372471
theorem B1459943 : Blo 1459549 1459943 := bstep (se 1 (by rfl) ⟨1094957, by rfl⟩ : syracuseStep 1459943 = 2189915) B2189915
theorem B1459967 : Blo 1459549 1459967 := bstep (se 1 (by rfl) ⟨1094975, by rfl⟩ : syracuseStep 1459967 = 2189951) B2189951
theorem B11085659 : Blo 1459549 11085659 := bstep (se 1 (by rfl) ⟨8314244, by rfl⟩ : syracuseStep 11085659 = 16628489) B16628489
theorem B8882297 : Blo 1459549 8882297 := bstep (se 2 (by rfl) ⟨3330861, by rfl⟩ : syracuseStep 8882297 = 6661723) B6661723
theorem B2189531 : Blo 1459549 2189531 := bstep (se 1 (by rfl) ⟨1642148, by rfl⟩ : syracuseStep 2189531 = 3284297) B3284297
theorem B8317343 : Blo 1459549 8317343 := bstep (se 1 (by rfl) ⟨6238007, by rfl⟩ : syracuseStep 8317343 = 12476015) B12476015
theorem B1460719 : Blo 1459549 1460719 := bstep (se 1 (by rfl) ⟨1095539, by rfl⟩ : syracuseStep 1460719 = 2191079) B2191079
theorem B2189879 : Blo 1459549 2189879 := bstep (se 1 (by rfl) ⟨1642409, by rfl⟩ : syracuseStep 2189879 = 3284819) B3284819
theorem B4926203 : Blo 1459549 4926203 := bstep (se 1 (by rfl) ⟨3694652, by rfl⟩ : syracuseStep 4926203 = 7389305) B7389305
theorem B17755145 : Blo 1459549 17755145 := bstep (se 2 (by rfl) ⟨6658179, by rfl⟩ : syracuseStep 17755145 = 13316359) B13316359
theorem B2190431 : Blo 1459549 2190431 := bstep (se 1 (by rfl) ⟨1642823, by rfl⟩ : syracuseStep 2190431 = 3285647) B3285647
theorem B2190443 : Blo 1459549 2190443 := bstep (se 1 (by rfl) ⟨1642832, by rfl⟩ : syracuseStep 2190443 = 3285665) B3285665
theorem B27012799 : Blo 1459549 27012799 := bstep (se 1 (by rfl) ⟨20259599, by rfl⟩ : syracuseStep 27012799 = 40519199) B40519199
theorem B23105401 : Blo 1459549 23105401 := bstep (se 2 (by rfl) ⟨8664525, by rfl⟩ : syracuseStep 23105401 = 17329051) B17329051
theorem B6755071 : Blo 1459549 6755071 := bstep (se 1 (by rfl) ⟨5066303, by rfl⟩ : syracuseStep 6755071 = 10132607) B10132607
theorem B17322983 : Blo 1459549 17322983 := bstep (se 1 (by rfl) ⟨12992237, by rfl⟩ : syracuseStep 17322983 = 25984475) B25984475
theorem B4158695 : Blo 1459549 4158695 := bstep (se 1 (by rfl) ⟨3119021, by rfl⟩ : syracuseStep 4158695 = 6238043) B6238043
theorem B3118655 : Blo 1459549 3118655 := bstep (se 1 (by rfl) ⟨2338991, by rfl⟩ : syracuseStep 3118655 = 4677983) B4677983
theorem B10524563 : Blo 1459549 10524563 := bstep (se 1 (by rfl) ⟨7893422, by rfl⟩ : syracuseStep 10524563 = 15786845) B15786845
theorem B5061437 : Blo 1459549 5061437 := bstep (se 3 (by rfl) ⟨949019, by rfl⟩ : syracuseStep 5061437 = 1898039) B1898039
theorem B2464681 : Blo 1459549 2464681 := bstep (se 2 (by rfl) ⟨924255, by rfl⟩ : syracuseStep 2464681 = 1848511) B1848511
theorem B3284243 : Blo 1459549 3284243 := bstep (se 1 (by rfl) ⟨2463182, by rfl⟩ : syracuseStep 3284243 = 4926365) B4926365
theorem B21054431 : Blo 1459549 21054431 := bstep (se 1 (by rfl) ⟨15790823, by rfl⟩ : syracuseStep 21054431 = 31581647) B31581647
theorem B3286241 : Blo 1459549 3286241 := bstep (se 2 (by rfl) ⟨1232340, by rfl⟩ : syracuseStep 3286241 = 2464681) B2464681
theorem B7390439 : Blo 1459549 7390439 := bstep (se 1 (by rfl) ⟨5542829, by rfl⟩ : syracuseStep 7390439 = 11085659) B11085659
theorem B1459687 : Blo 1459549 1459687 := bstep (se 1 (by rfl) ⟨1094765, by rfl⟩ : syracuseStep 1459687 = 2189531) B2189531
theorem B1459919 : Blo 1459549 1459919 := bstep (se 1 (by rfl) ⟨1094939, by rfl⟩ : syracuseStep 1459919 = 2189879) B2189879
theorem B1460287 : Blo 1459549 1460287 := bstep (se 1 (by rfl) ⟨1095215, by rfl⟩ : syracuseStep 1460287 = 2190431) B2190431
theorem B1460295 : Blo 1459549 1460295 := bstep (se 1 (by rfl) ⟨1095221, by rfl⟩ : syracuseStep 1460295 = 2190443) B2190443
theorem B2189495 : Blo 1459549 2189495 := bstep (se 1 (by rfl) ⟨1642121, by rfl⟩ : syracuseStep 2189495 = 3284243) B3284243
theorem B42085331 : Blo 1459549 42085331 := bstep (se 1 (by rfl) ⟨31563998, by rfl⟩ : syracuseStep 42085331 = 63127997) B63127997
theorem B2772463 : Blo 1459549 2772463 := bstep (se 1 (by rfl) ⟨2079347, by rfl⟩ : syracuseStep 2772463 = 4158695) B4158695
theorem B9006761 : Blo 1459549 9006761 := bstep (se 2 (by rfl) ⟨3377535, by rfl⟩ : syracuseStep 9006761 = 6755071) B6755071
theorem B7016375 : Blo 1459549 7016375 := bstep (se 1 (by rfl) ⟨5262281, by rfl⟩ : syracuseStep 7016375 = 10524563) B10524563
theorem B123228805 : Blo 1459549 123228805 := bstep (se 4 (by rfl) ⟨11552700, by rfl⟩ : syracuseStep 123228805 = 23105401) B23105401
theorem B36017065 : Blo 1459549 36017065 := bstep (se 2 (by rfl) ⟨13506399, by rfl⟩ : syracuseStep 36017065 = 27012799) B27012799
theorem B4216799 : Blo 1459549 4216799 := bstep (se 1 (by rfl) ⟨3162599, by rfl⟩ : syracuseStep 4216799 = 6325199) B6325199
theorem B11548655 : Blo 1459549 11548655 := bstep (se 1 (by rfl) ⟨8661491, by rfl⟩ : syracuseStep 11548655 = 17322983) B17322983
theorem B5543923 : Blo 1459549 5543923 := bstep (se 1 (by rfl) ⟨4157942, by rfl⟩ : syracuseStep 5543923 = 8315885) B8315885
theorem B2079103 : Blo 1459549 2079103 := bstep (se 1 (by rfl) ⟨1559327, by rfl⟩ : syracuseStep 2079103 = 3118655) B3118655
theorem B8313425 : Blo 1459549 8313425 := bstep (se 2 (by rfl) ⟨3117534, by rfl⟩ : syracuseStep 8313425 = 6235069) B6235069
theorem B5921531 : Blo 1459549 5921531 := bstep (se 1 (by rfl) ⟨4441148, by rfl⟩ : syracuseStep 5921531 = 8882297) B8882297
theorem B5544895 : Blo 1459549 5544895 := bstep (se 1 (by rfl) ⟨4158671, by rfl⟩ : syracuseStep 5544895 = 8317343) B8317343
theorem B3284135 : Blo 1459549 3284135 := bstep (se 1 (by rfl) ⟨2463101, by rfl⟩ : syracuseStep 3284135 = 4926203) B4926203
theorem B3374291 : Blo 1459549 3374291 := bstep (se 1 (by rfl) ⟨2530718, by rfl⟩ : syracuseStep 3374291 = 5061437) B5061437
theorem B11836763 : Blo 1459549 11836763 := bstep (se 1 (by rfl) ⟨8877572, by rfl⟩ : syracuseStep 11836763 = 17755145) B17755145
theorem B2811199 : Blo 1459549 2811199 := bstep (se 1 (by rfl) ⟨2108399, by rfl⟩ : syracuseStep 2811199 = 4216799) B4216799
theorem B1459663 : Blo 1459549 1459663 := bstep (se 1 (by rfl) ⟨1094747, by rfl⟩ : syracuseStep 1459663 = 2189495) B2189495
theorem B3696617 : Blo 1459549 3696617 := bstep (se 2 (by rfl) ⟨1386231, by rfl⟩ : syracuseStep 3696617 = 2772463) B2772463
theorem B2189423 : Blo 1459549 2189423 := bstep (se 1 (by rfl) ⟨1642067, by rfl⟩ : syracuseStep 2189423 = 3284135) B3284135
theorem B7891175 : Blo 1459549 7891175 := bstep (se 1 (by rfl) ⟨5918381, by rfl⟩ : syracuseStep 7891175 = 11836763) B11836763
theorem B7391897 : Blo 1459549 7391897 := bstep (se 2 (by rfl) ⟨2771961, by rfl⟩ : syracuseStep 7391897 = 5543923) B5543923
theorem B2772137 : Blo 1459549 2772137 := bstep (se 2 (by rfl) ⟨1039551, by rfl⟩ : syracuseStep 2772137 = 2079103) B2079103
theorem B14036287 : Blo 1459549 14036287 := bstep (se 1 (by rfl) ⟨10527215, by rfl⟩ : syracuseStep 14036287 = 21054431) B21054431
theorem B2190827 : Blo 1459549 2190827 := bstep (se 1 (by rfl) ⟨1643120, by rfl⟩ : syracuseStep 2190827 = 3286241) B3286241
theorem B4926959 : Blo 1459549 4926959 := bstep (se 1 (by rfl) ⟨3695219, by rfl⟩ : syracuseStep 4926959 = 7390439) B7390439
theorem B7393193 : Blo 1459549 7393193 := bstep (se 2 (by rfl) ⟨2772447, by rfl⟩ : syracuseStep 7393193 = 5544895) B5544895
theorem B5542283 : Blo 1459549 5542283 := bstep (se 1 (by rfl) ⟨4156712, by rfl⟩ : syracuseStep 5542283 = 8313425) B8313425
theorem B2249527 : Blo 1459549 2249527 := bstep (se 1 (by rfl) ⟨1687145, by rfl⟩ : syracuseStep 2249527 = 3374291) B3374291
theorem B192091013 : Blo 1459549 192091013 := bstep (se 4 (by rfl) ⟨18008532, by rfl⟩ : syracuseStep 192091013 = 36017065) B36017065
theorem B164305073 : Blo 1459549 164305073 := bstep (se 2 (by rfl) ⟨61614402, by rfl⟩ : syracuseStep 164305073 = 123228805) B123228805
theorem B7699103 : Blo 1459549 7699103 := bstep (se 1 (by rfl) ⟨5774327, by rfl⟩ : syracuseStep 7699103 = 11548655) B11548655
theorem B3947687 : Blo 1459549 3947687 := bstep (se 1 (by rfl) ⟨2960765, by rfl⟩ : syracuseStep 3947687 = 5921531) B5921531
theorem B28056887 : Blo 1459549 28056887 := bstep (se 1 (by rfl) ⟨21042665, by rfl⟩ : syracuseStep 28056887 = 42085331) B42085331
theorem B6004507 : Blo 1459549 6004507 := bstep (se 1 (by rfl) ⟨4503380, by rfl⟩ : syracuseStep 6004507 = 9006761) B9006761
theorem B4677583 : Blo 1459549 4677583 := bstep (se 1 (by rfl) ⟨3508187, by rfl⟩ : syracuseStep 4677583 = 7016375) B7016375
theorem B3694855 : Blo 1459549 3694855 := bstep (se 1 (by rfl) ⟨2771141, by rfl⟩ : syracuseStep 3694855 = 5542283) B5542283
theorem B2999369 : Blo 1459549 2999369 := bstep (se 2 (by rfl) ⟨1124763, by rfl⟩ : syracuseStep 2999369 = 2249527) B2249527
theorem B1459615 : Blo 1459549 1459615 := bstep (se 1 (by rfl) ⟨1094711, by rfl⟩ : syracuseStep 1459615 = 2189423) B2189423
theorem B109536715 : Blo 1459549 109536715 := bstep (se 1 (by rfl) ⟨82152536, by rfl⟩ : syracuseStep 109536715 = 164305073) B164305073
theorem B5260783 : Blo 1459549 5260783 := bstep (se 1 (by rfl) ⟨3945587, by rfl⟩ : syracuseStep 5260783 = 7891175) B7891175
theorem B2631791 : Blo 1459549 2631791 := bstep (se 1 (by rfl) ⟨1973843, by rfl⟩ : syracuseStep 2631791 = 3947687) B3947687
theorem B18704591 : Blo 1459549 18704591 := bstep (se 1 (by rfl) ⟨14028443, by rfl⟩ : syracuseStep 18704591 = 28056887) B28056887
theorem B1460551 : Blo 1459549 1460551 := bstep (se 1 (by rfl) ⟨1095413, by rfl⟩ : syracuseStep 1460551 = 2190827) B2190827
theorem B8006009 : Blo 1459549 8006009 := bstep (se 2 (by rfl) ⟨3002253, by rfl⟩ : syracuseStep 8006009 = 6004507) B6004507
theorem B6236777 : Blo 1459549 6236777 := bstep (se 2 (by rfl) ⟨2338791, by rfl⟩ : syracuseStep 6236777 = 4677583) B4677583
theorem B128060675 : Blo 1459549 128060675 := bstep (se 1 (by rfl) ⟨96045506, by rfl⟩ : syracuseStep 128060675 = 192091013) B192091013
theorem B18715049 : Blo 1459549 18715049 := bstep (se 2 (by rfl) ⟨7018143, by rfl⟩ : syracuseStep 18715049 = 14036287) B14036287
theorem B3748265 : Blo 1459549 3748265 := bstep (se 2 (by rfl) ⟨1405599, by rfl⟩ : syracuseStep 3748265 = 2811199) B2811199
theorem B4927931 : Blo 1459549 4927931 := bstep (se 1 (by rfl) ⟨3695948, by rfl⟩ : syracuseStep 4927931 = 7391897) B7391897
theorem B5132735 : Blo 1459549 5132735 := bstep (se 1 (by rfl) ⟨3849551, by rfl⟩ : syracuseStep 5132735 = 7699103) B7699103
theorem B1848091 : Blo 1459549 1848091 := bstep (se 1 (by rfl) ⟨1386068, by rfl⟩ : syracuseStep 1848091 = 2772137) B2772137
theorem B4928795 : Blo 1459549 4928795 := bstep (se 1 (by rfl) ⟨3696596, by rfl⟩ : syracuseStep 4928795 = 7393193) B7393193
theorem B2464411 : Blo 1459549 2464411 := bstep (se 1 (by rfl) ⟨1848308, by rfl⟩ : syracuseStep 2464411 = 3696617) B3696617
theorem B3284639 : Blo 1459549 3284639 := bstep (se 1 (by rfl) ⟨2463479, by rfl⟩ : syracuseStep 3284639 = 4926959) B4926959
theorem B12476699 : Blo 1459549 12476699 := bstep (se 1 (by rfl) ⟨9357524, by rfl⟩ : syracuseStep 12476699 = 18715049) B18715049
theorem B2498843 : Blo 1459549 2498843 := bstep (se 1 (by rfl) ⟨1874132, by rfl⟩ : syracuseStep 2498843 = 3748265) B3748265
theorem B3285287 : Blo 1459549 3285287 := bstep (se 1 (by rfl) ⟨2463965, by rfl⟩ : syracuseStep 3285287 = 4927931) B4927931
theorem B1999579 : Blo 1459549 1999579 := bstep (se 1 (by rfl) ⟨1499684, by rfl⟩ : syracuseStep 1999579 = 2999369) B2999369
theorem B3285863 : Blo 1459549 3285863 := bstep (se 1 (by rfl) ⟨2464397, by rfl⟩ : syracuseStep 3285863 = 4928795) B4928795
theorem B3285881 : Blo 1459549 3285881 := bstep (se 2 (by rfl) ⟨1232205, by rfl⟩ : syracuseStep 3285881 = 2464411) B2464411
theorem B1754527 : Blo 1459549 1754527 := bstep (se 1 (by rfl) ⟨1315895, by rfl⟩ : syracuseStep 1754527 = 2631791) B2631791
theorem B12469727 : Blo 1459549 12469727 := bstep (se 1 (by rfl) ⟨9352295, by rfl⟩ : syracuseStep 12469727 = 18704591) B18704591
theorem B16631405 : Blo 1459549 16631405 := bstep (se 3 (by rfl) ⟨3118388, by rfl⟩ : syracuseStep 16631405 = 6236777) B6236777
theorem B146048953 : Blo 1459549 146048953 := bstep (se 2 (by rfl) ⟨54768357, by rfl⟩ : syracuseStep 146048953 = 109536715) B109536715
theorem B7014377 : Blo 1459549 7014377 := bstep (se 2 (by rfl) ⟨2630391, by rfl⟩ : syracuseStep 7014377 = 5260783) B5260783
theorem B2189759 : Blo 1459549 2189759 := bstep (se 1 (by rfl) ⟨1642319, by rfl⟩ : syracuseStep 2189759 = 3284639) B3284639
theorem B4926473 : Blo 1459549 4926473 := bstep (se 2 (by rfl) ⟨1847427, by rfl⟩ : syracuseStep 4926473 = 3694855) B3694855
theorem B85397429 : Blo 1459549 85397429 := bstep (se 5 (by rfl) ⟨4003004, by rfl⟩ : syracuseStep 85397429 = 8006009) B8006009
theorem B85373783 : Blo 1459549 85373783 := bstep (se 1 (by rfl) ⟨64030337, by rfl⟩ : syracuseStep 85373783 = 128060675) B128060675
theorem B3421823 : Blo 1459549 3421823 := bstep (se 1 (by rfl) ⟨2566367, by rfl⟩ : syracuseStep 3421823 = 5132735) B5132735
theorem B2464121 : Blo 1459549 2464121 := bstep (se 2 (by rfl) ⟨924045, by rfl⟩ : syracuseStep 2464121 = 1848091) B1848091
theorem B1459839 : Blo 1459549 1459839 := bstep (se 1 (by rfl) ⟨1094879, by rfl⟩ : syracuseStep 1459839 = 2189759) B2189759
theorem B8317799 : Blo 1459549 8317799 := bstep (se 1 (by rfl) ⟨6238349, by rfl⟩ : syracuseStep 8317799 = 12476699) B12476699
theorem B1665895 : Blo 1459549 1665895 := bstep (se 1 (by rfl) ⟨1249421, by rfl⟩ : syracuseStep 1665895 = 2498843) B2498843
theorem B2190191 : Blo 1459549 2190191 := bstep (se 1 (by rfl) ⟨1642643, by rfl⟩ : syracuseStep 2190191 = 3285287) B3285287
theorem B2190575 : Blo 1459549 2190575 := bstep (se 1 (by rfl) ⟨1642931, by rfl⟩ : syracuseStep 2190575 = 3285863) B3285863
theorem B2190587 : Blo 1459549 2190587 := bstep (se 1 (by rfl) ⟨1642940, by rfl⟩ : syracuseStep 2190587 = 3285881) B3285881
theorem B2666105 : Blo 1459549 2666105 := bstep (se 2 (by rfl) ⟨999789, by rfl⟩ : syracuseStep 2666105 = 1999579) B1999579
theorem B11087603 : Blo 1459549 11087603 := bstep (se 1 (by rfl) ⟨8315702, by rfl⟩ : syracuseStep 11087603 = 16631405) B16631405
theorem B1642747 : Blo 1459549 1642747 := bstep (se 1 (by rfl) ⟨1232060, by rfl⟩ : syracuseStep 1642747 = 2464121) B2464121
theorem B2339369 : Blo 1459549 2339369 := bstep (se 2 (by rfl) ⟨877263, by rfl⟩ : syracuseStep 2339369 = 1754527) B1754527
theorem B56931619 : Blo 1459549 56931619 := bstep (se 1 (by rfl) ⟨42698714, by rfl⟩ : syracuseStep 56931619 = 85397429) B85397429
theorem B56915855 : Blo 1459549 56915855 := bstep (se 1 (by rfl) ⟨42686891, by rfl⟩ : syracuseStep 56915855 = 85373783) B85373783
theorem B8313151 : Blo 1459549 8313151 := bstep (se 1 (by rfl) ⟨6234863, by rfl⟩ : syracuseStep 8313151 = 12469727) B12469727
theorem B4676251 : Blo 1459549 4676251 := bstep (se 1 (by rfl) ⟨3507188, by rfl⟩ : syracuseStep 4676251 = 7014377) B7014377
theorem B9124861 : Blo 1459549 9124861 := bstep (se 3 (by rfl) ⟨1710911, by rfl⟩ : syracuseStep 9124861 = 3421823) B3421823
theorem B3284315 : Blo 1459549 3284315 := bstep (se 1 (by rfl) ⟨2463236, by rfl⟩ : syracuseStep 3284315 = 4926473) B4926473
theorem B194731937 : Blo 1459549 194731937 := bstep (se 2 (by rfl) ⟨73024476, by rfl⟩ : syracuseStep 194731937 = 146048953) B146048953
theorem B11084201 : Blo 1459549 11084201 := bstep (se 2 (by rfl) ⟨4156575, by rfl⟩ : syracuseStep 11084201 = 8313151) B8313151
theorem B6235001 : Blo 1459549 6235001 := bstep (se 2 (by rfl) ⟨2338125, by rfl⟩ : syracuseStep 6235001 = 4676251) B4676251
theorem B2221193 : Blo 1459549 2221193 := bstep (se 2 (by rfl) ⟨832947, by rfl⟩ : syracuseStep 2221193 = 1665895) B1665895
theorem B12166481 : Blo 1459549 12166481 := bstep (se 2 (by rfl) ⟨4562430, by rfl⟩ : syracuseStep 12166481 = 9124861) B9124861
theorem B75908825 : Blo 1459549 75908825 := bstep (se 2 (by rfl) ⟨28465809, by rfl⟩ : syracuseStep 75908825 = 56931619) B56931619
theorem B1460127 : Blo 1459549 1460127 := bstep (se 1 (by rfl) ⟨1095095, by rfl⟩ : syracuseStep 1460127 = 2190191) B2190191
theorem B1460383 : Blo 1459549 1460383 := bstep (se 1 (by rfl) ⟨1095287, by rfl⟩ : syracuseStep 1460383 = 2190575) B2190575
theorem B1460391 : Blo 1459549 1460391 := bstep (se 1 (by rfl) ⟨1095293, by rfl⟩ : syracuseStep 1460391 = 2190587) B2190587
theorem B2189543 : Blo 1459549 2189543 := bstep (se 1 (by rfl) ⟨1642157, by rfl⟩ : syracuseStep 2189543 = 3284315) B3284315
theorem B7391735 : Blo 1459549 7391735 := bstep (se 1 (by rfl) ⟨5543801, by rfl⟩ : syracuseStep 7391735 = 11087603) B11087603
theorem B129821291 : Blo 1459549 129821291 := bstep (se 1 (by rfl) ⟨97365968, by rfl⟩ : syracuseStep 129821291 = 194731937) B194731937
theorem B2190329 : Blo 1459549 2190329 := bstep (se 2 (by rfl) ⟨821373, by rfl⟩ : syracuseStep 2190329 = 1642747) B1642747
theorem B1559579 : Blo 1459549 1559579 := bstep (se 1 (by rfl) ⟨1169684, by rfl⟩ : syracuseStep 1559579 = 2339369) B2339369
theorem B37943903 : Blo 1459549 37943903 := bstep (se 1 (by rfl) ⟨28457927, by rfl⟩ : syracuseStep 37943903 = 56915855) B56915855
theorem B5545199 : Blo 1459549 5545199 := bstep (se 1 (by rfl) ⟨4158899, by rfl⟩ : syracuseStep 5545199 = 8317799) B8317799
theorem B1777403 : Blo 1459549 1777403 := bstep (se 1 (by rfl) ⟨1333052, by rfl⟩ : syracuseStep 1777403 = 2666105) B2666105
theorem B7389467 : Blo 1459549 7389467 := bstep (se 1 (by rfl) ⟨5542100, by rfl⟩ : syracuseStep 7389467 = 11084201) B11084201
theorem B5923181 : Blo 1459549 5923181 := bstep (se 3 (by rfl) ⟨1110596, by rfl⟩ : syracuseStep 5923181 = 2221193) B2221193
theorem B1459695 : Blo 1459549 1459695 := bstep (se 1 (by rfl) ⟨1094771, by rfl⟩ : syracuseStep 1459695 = 2189543) B2189543
theorem B1460219 : Blo 1459549 1460219 := bstep (se 1 (by rfl) ⟨1095164, by rfl⟩ : syracuseStep 1460219 = 2190329) B2190329
theorem B3696799 : Blo 1459549 3696799 := bstep (se 1 (by rfl) ⟨2772599, by rfl⟩ : syracuseStep 3696799 = 5545199) B5545199
theorem B4156667 : Blo 1459549 4156667 := bstep (se 1 (by rfl) ⟨3117500, by rfl⟩ : syracuseStep 4156667 = 6235001) B6235001
theorem B32443949 : Blo 1459549 32443949 := bstep (se 3 (by rfl) ⟨6083240, by rfl⟩ : syracuseStep 32443949 = 12166481) B12166481
theorem B50605883 : Blo 1459549 50605883 := bstep (se 1 (by rfl) ⟨37954412, by rfl⟩ : syracuseStep 50605883 = 75908825) B75908825
theorem B101183741 : Blo 1459549 101183741 := bstep (se 3 (by rfl) ⟨18971951, by rfl⟩ : syracuseStep 101183741 = 37943903) B37943903
theorem B4927823 : Blo 1459549 4927823 := bstep (se 1 (by rfl) ⟨3695867, by rfl⟩ : syracuseStep 4927823 = 7391735) B7391735
theorem B4739741 : Blo 1459549 4739741 := bstep (se 3 (by rfl) ⟨888701, by rfl⟩ : syracuseStep 4739741 = 1777403) B1777403
theorem B4158877 : Blo 1459549 4158877 := bstep (se 3 (by rfl) ⟨779789, by rfl⟩ : syracuseStep 4158877 = 1559579) B1559579
theorem B86547527 : Blo 1459549 86547527 := bstep (se 1 (by rfl) ⟨64910645, by rfl⟩ : syracuseStep 86547527 = 129821291) B129821291
theorem B3285215 : Blo 1459549 3285215 := bstep (se 1 (by rfl) ⟨2463911, by rfl⟩ : syracuseStep 3285215 = 4927823) B4927823
theorem B3948787 : Blo 1459549 3948787 := bstep (se 1 (by rfl) ⟨2961590, by rfl⟩ : syracuseStep 3948787 = 5923181) B5923181
theorem B86517197 : Blo 1459549 86517197 := bstep (se 3 (by rfl) ⟨16221974, by rfl⟩ : syracuseStep 86517197 = 32443949) B32443949
theorem B57698351 : Blo 1459549 57698351 := bstep (se 1 (by rfl) ⟨43273763, by rfl⟩ : syracuseStep 57698351 = 86547527) B86547527
theorem B2771111 : Blo 1459549 2771111 := bstep (se 1 (by rfl) ⟨2078333, by rfl⟩ : syracuseStep 2771111 = 4156667) B4156667
theorem B33737255 : Blo 1459549 33737255 := bstep (se 1 (by rfl) ⟨25302941, by rfl⟩ : syracuseStep 33737255 = 50605883) B50605883
theorem B67455827 : Blo 1459549 67455827 := bstep (se 1 (by rfl) ⟨50591870, by rfl⟩ : syracuseStep 67455827 = 101183741) B101183741
theorem B4926311 : Blo 1459549 4926311 := bstep (se 1 (by rfl) ⟨3694733, by rfl⟩ : syracuseStep 4926311 = 7389467) B7389467
theorem B4929065 : Blo 1459549 4929065 := bstep (se 2 (by rfl) ⟨1848399, by rfl⟩ : syracuseStep 4929065 = 3696799) B3696799
theorem B3159827 : Blo 1459549 3159827 := bstep (se 1 (by rfl) ⟨2369870, by rfl⟩ : syracuseStep 3159827 = 4739741) B4739741
theorem B5545169 : Blo 1459549 5545169 := bstep (se 2 (by rfl) ⟨2079438, by rfl⟩ : syracuseStep 5545169 = 4158877) B4158877
theorem B7389629 : Blo 1459549 7389629 := bstep (se 3 (by rfl) ⟨1385555, by rfl⟩ : syracuseStep 7389629 = 2771111) B2771111
theorem B3286043 : Blo 1459549 3286043 := bstep (se 1 (by rfl) ⟨2464532, by rfl⟩ : syracuseStep 3286043 = 4929065) B4929065
theorem B2106551 : Blo 1459549 2106551 := bstep (se 1 (by rfl) ⟨1579913, by rfl⟩ : syracuseStep 2106551 = 3159827) B3159827
theorem B3696779 : Blo 1459549 3696779 := bstep (se 1 (by rfl) ⟨2772584, by rfl⟩ : syracuseStep 3696779 = 5545169) B5545169
theorem B2190143 : Blo 1459549 2190143 := bstep (se 1 (by rfl) ⟨1642607, by rfl⟩ : syracuseStep 2190143 = 3285215) B3285215
theorem B38465567 : Blo 1459549 38465567 := bstep (se 1 (by rfl) ⟨28849175, by rfl⟩ : syracuseStep 38465567 = 57698351) B57698351
theorem B22491503 : Blo 1459549 22491503 := bstep (se 1 (by rfl) ⟨16868627, by rfl⟩ : syracuseStep 22491503 = 33737255) B33737255
theorem B44970551 : Blo 1459549 44970551 := bstep (se 1 (by rfl) ⟨33727913, by rfl⟩ : syracuseStep 44970551 = 67455827) B67455827
theorem B5265049 : Blo 1459549 5265049 := bstep (se 2 (by rfl) ⟨1974393, by rfl⟩ : syracuseStep 5265049 = 3948787) B3948787
theorem B57678131 : Blo 1459549 57678131 := bstep (se 1 (by rfl) ⟨43258598, by rfl⟩ : syracuseStep 57678131 = 86517197) B86517197
theorem B3284207 : Blo 1459549 3284207 := bstep (se 1 (by rfl) ⟨2463155, by rfl⟩ : syracuseStep 3284207 = 4926311) B4926311
theorem B1460095 : Blo 1459549 1460095 := bstep (se 1 (by rfl) ⟨1095071, by rfl⟩ : syracuseStep 1460095 = 2190143) B2190143
theorem B2189471 : Blo 1459549 2189471 := bstep (se 1 (by rfl) ⟨1642103, by rfl⟩ : syracuseStep 2189471 = 3284207) B3284207
theorem B25643711 : Blo 1459549 25643711 := bstep (se 1 (by rfl) ⟨19232783, by rfl⟩ : syracuseStep 25643711 = 38465567) B38465567
theorem B14994335 : Blo 1459549 14994335 := bstep (se 1 (by rfl) ⟨11245751, by rfl⟩ : syracuseStep 14994335 = 22491503) B22491503
theorem B4926419 : Blo 1459549 4926419 := bstep (se 1 (by rfl) ⟨3694814, by rfl⟩ : syracuseStep 4926419 = 7389629) B7389629
theorem B2190695 : Blo 1459549 2190695 := bstep (se 1 (by rfl) ⟨1643021, by rfl⟩ : syracuseStep 2190695 = 3286043) B3286043
theorem B29980367 : Blo 1459549 29980367 := bstep (se 1 (by rfl) ⟨22485275, by rfl⟩ : syracuseStep 29980367 = 44970551) B44970551
theorem B5617469 : Blo 1459549 5617469 := bstep (se 3 (by rfl) ⟨1053275, by rfl⟩ : syracuseStep 5617469 = 2106551) B2106551
theorem B2464519 : Blo 1459549 2464519 := bstep (se 1 (by rfl) ⟨1848389, by rfl⟩ : syracuseStep 2464519 = 3696779) B3696779
theorem B38452087 : Blo 1459549 38452087 := bstep (se 1 (by rfl) ⟨28839065, by rfl⟩ : syracuseStep 38452087 = 57678131) B57678131
theorem B7020065 : Blo 1459549 7020065 := bstep (se 2 (by rfl) ⟨2632524, by rfl⟩ : syracuseStep 7020065 = 5265049) B5265049
theorem B3286025 : Blo 1459549 3286025 := bstep (se 2 (by rfl) ⟨1232259, by rfl⟩ : syracuseStep 3286025 = 2464519) B2464519
theorem B18720173 : Blo 1459549 18720173 := bstep (se 3 (by rfl) ⟨3510032, by rfl⟩ : syracuseStep 18720173 = 7020065) B7020065
theorem B1459647 : Blo 1459549 1459647 := bstep (se 1 (by rfl) ⟨1094735, by rfl⟩ : syracuseStep 1459647 = 2189471) B2189471
theorem B9996223 : Blo 1459549 9996223 := bstep (se 1 (by rfl) ⟨7497167, by rfl⟩ : syracuseStep 9996223 = 14994335) B14994335
theorem B1460463 : Blo 1459549 1460463 := bstep (se 1 (by rfl) ⟨1095347, by rfl⟩ : syracuseStep 1460463 = 2190695) B2190695
theorem B51269449 : Blo 1459549 51269449 := bstep (se 2 (by rfl) ⟨19226043, by rfl⟩ : syracuseStep 51269449 = 38452087) B38452087
theorem B14979917 : Blo 1459549 14979917 := bstep (se 3 (by rfl) ⟨2808734, by rfl⟩ : syracuseStep 14979917 = 5617469) B5617469
theorem B19986911 : Blo 1459549 19986911 := bstep (se 1 (by rfl) ⟨14990183, by rfl⟩ : syracuseStep 19986911 = 29980367) B29980367
theorem B17095807 : Blo 1459549 17095807 := bstep (se 1 (by rfl) ⟨12821855, by rfl⟩ : syracuseStep 17095807 = 25643711) B25643711
theorem B3284279 : Blo 1459549 3284279 := bstep (se 1 (by rfl) ⟨2463209, by rfl⟩ : syracuseStep 3284279 = 4926419) B4926419
theorem B39946445 : Blo 1459549 39946445 := bstep (se 3 (by rfl) ⟨7489958, by rfl⟩ : syracuseStep 39946445 = 14979917) B14979917
theorem B2189519 : Blo 1459549 2189519 := bstep (se 1 (by rfl) ⟨1642139, by rfl⟩ : syracuseStep 2189519 = 3284279) B3284279
theorem B2190683 : Blo 1459549 2190683 := bstep (se 1 (by rfl) ⟨1643012, by rfl⟩ : syracuseStep 2190683 = 3286025) B3286025
theorem B12480115 : Blo 1459549 12480115 := bstep (se 1 (by rfl) ⟨9360086, by rfl⟩ : syracuseStep 12480115 = 18720173) B18720173
theorem B22794409 : Blo 1459549 22794409 := bstep (se 2 (by rfl) ⟨8547903, by rfl⟩ : syracuseStep 22794409 = 17095807) B17095807
theorem B13324607 : Blo 1459549 13324607 := bstep (se 1 (by rfl) ⟨9993455, by rfl⟩ : syracuseStep 13324607 = 19986911) B19986911
theorem B68359265 : Blo 1459549 68359265 := bstep (se 2 (by rfl) ⟨25634724, by rfl⟩ : syracuseStep 68359265 = 51269449) B51269449
theorem B13328297 : Blo 1459549 13328297 := bstep (se 2 (by rfl) ⟨4998111, by rfl⟩ : syracuseStep 13328297 = 9996223) B9996223
theorem B30392545 : Blo 1459549 30392545 := bstep (se 2 (by rfl) ⟨11397204, by rfl⟩ : syracuseStep 30392545 = 22794409) B22794409
theorem B45572843 : Blo 1459549 45572843 := bstep (se 1 (by rfl) ⟨34179632, by rfl⟩ : syracuseStep 45572843 = 68359265) B68359265
theorem B1459679 : Blo 1459549 1459679 := bstep (se 1 (by rfl) ⟨1094759, by rfl⟩ : syracuseStep 1459679 = 2189519) B2189519
theorem B16640153 : Blo 1459549 16640153 := bstep (se 2 (by rfl) ⟨6240057, by rfl⟩ : syracuseStep 16640153 = 12480115) B12480115
theorem B1460455 : Blo 1459549 1460455 := bstep (se 1 (by rfl) ⟨1095341, by rfl⟩ : syracuseStep 1460455 = 2190683) B2190683
theorem B8883071 : Blo 1459549 8883071 := bstep (se 1 (by rfl) ⟨6662303, by rfl⟩ : syracuseStep 8883071 = 13324607) B13324607
theorem B8885531 : Blo 1459549 8885531 := bstep (se 1 (by rfl) ⟨6664148, by rfl⟩ : syracuseStep 8885531 = 13328297) B13328297
theorem B26630963 : Blo 1459549 26630963 := bstep (se 1 (by rfl) ⟨19973222, by rfl⟩ : syracuseStep 26630963 = 39946445) B39946445
theorem B5923687 : Blo 1459549 5923687 := bstep (se 1 (by rfl) ⟨4442765, by rfl⟩ : syracuseStep 5923687 = 8885531) B8885531
theorem B11093435 : Blo 1459549 11093435 := bstep (se 1 (by rfl) ⟨8320076, by rfl⟩ : syracuseStep 11093435 = 16640153) B16640153
theorem B17753975 : Blo 1459549 17753975 := bstep (se 1 (by rfl) ⟨13315481, by rfl⟩ : syracuseStep 17753975 = 26630963) B26630963
theorem B40523393 : Blo 1459549 40523393 := bstep (se 2 (by rfl) ⟨15196272, by rfl⟩ : syracuseStep 40523393 = 30392545) B30392545
theorem B30381895 : Blo 1459549 30381895 := bstep (se 1 (by rfl) ⟨22786421, by rfl⟩ : syracuseStep 30381895 = 45572843) B45572843
theorem B5922047 : Blo 1459549 5922047 := bstep (se 1 (by rfl) ⟨4441535, by rfl⟩ : syracuseStep 5922047 = 8883071) B8883071
theorem B7898249 : Blo 1459549 7898249 := bstep (se 2 (by rfl) ⟨2961843, by rfl⟩ : syracuseStep 7898249 = 5923687) B5923687
theorem B108062381 : Blo 1459549 108062381 := bstep (se 3 (by rfl) ⟨20261696, by rfl⟩ : syracuseStep 108062381 = 40523393) B40523393
theorem B7395623 : Blo 1459549 7395623 := bstep (se 1 (by rfl) ⟨5546717, by rfl⟩ : syracuseStep 7395623 = 11093435) B11093435
theorem B11835983 : Blo 1459549 11835983 := bstep (se 1 (by rfl) ⟨8876987, by rfl⟩ : syracuseStep 11835983 = 17753975) B17753975
theorem B3948031 : Blo 1459549 3948031 := bstep (se 1 (by rfl) ⟨2961023, by rfl⟩ : syracuseStep 3948031 = 5922047) B5922047
theorem B40509193 : Blo 1459549 40509193 := bstep (se 2 (by rfl) ⟨15190947, by rfl⟩ : syracuseStep 40509193 = 30381895) B30381895
theorem B7890655 : Blo 1459549 7890655 := bstep (se 1 (by rfl) ⟨5917991, by rfl⟩ : syracuseStep 7890655 = 11835983) B11835983
theorem B54012257 : Blo 1459549 54012257 := bstep (se 2 (by rfl) ⟨20254596, by rfl⟩ : syracuseStep 54012257 = 40509193) B40509193
theorem B288166349 : Blo 1459549 288166349 := bstep (se 3 (by rfl) ⟨54031190, by rfl⟩ : syracuseStep 288166349 = 108062381) B108062381
theorem B5264041 : Blo 1459549 5264041 := bstep (se 2 (by rfl) ⟨1974015, by rfl⟩ : syracuseStep 5264041 = 3948031) B3948031
theorem B5265499 : Blo 1459549 5265499 := bstep (se 1 (by rfl) ⟨3949124, by rfl⟩ : syracuseStep 5265499 = 7898249) B7898249
theorem B4930415 : Blo 1459549 4930415 := bstep (se 1 (by rfl) ⟨3697811, by rfl⟩ : syracuseStep 4930415 = 7395623) B7395623
theorem B7020665 : Blo 1459549 7020665 := bstep (se 2 (by rfl) ⟨2632749, by rfl⟩ : syracuseStep 7020665 = 5265499) B5265499
theorem B192110899 : Blo 1459549 192110899 := bstep (se 1 (by rfl) ⟨144083174, by rfl⟩ : syracuseStep 192110899 = 288166349) B288166349
theorem B3286943 : Blo 1459549 3286943 := bstep (se 1 (by rfl) ⟨2465207, by rfl⟩ : syracuseStep 3286943 = 4930415) B4930415
theorem B10520873 : Blo 1459549 10520873 := bstep (se 2 (by rfl) ⟨3945327, by rfl⟩ : syracuseStep 10520873 = 7890655) B7890655
theorem B36008171 : Blo 1459549 36008171 := bstep (se 1 (by rfl) ⟨27006128, by rfl⟩ : syracuseStep 36008171 = 54012257) B54012257
theorem B7018721 : Blo 1459549 7018721 := bstep (se 2 (by rfl) ⟨2632020, by rfl⟩ : syracuseStep 7018721 = 5264041) B5264041
theorem B256147865 : Blo 1459549 256147865 := bstep (se 2 (by rfl) ⟨96055449, by rfl⟩ : syracuseStep 256147865 = 192110899) B192110899
theorem B4679147 : Blo 1459549 4679147 := bstep (se 1 (by rfl) ⟨3509360, by rfl⟩ : syracuseStep 4679147 = 7018721) B7018721
theorem B7013915 : Blo 1459549 7013915 := bstep (se 1 (by rfl) ⟨5260436, by rfl⟩ : syracuseStep 7013915 = 10520873) B10520873
theorem B4680443 : Blo 1459549 4680443 := bstep (se 1 (by rfl) ⟨3510332, by rfl⟩ : syracuseStep 4680443 = 7020665) B7020665
theorem B24005447 : Blo 1459549 24005447 := bstep (se 1 (by rfl) ⟨18004085, by rfl⟩ : syracuseStep 24005447 = 36008171) B36008171
theorem B2191295 : Blo 1459549 2191295 := bstep (se 1 (by rfl) ⟨1643471, by rfl⟩ : syracuseStep 2191295 = 3286943) B3286943
theorem B12477725 : Blo 1459549 12477725 := bstep (se 3 (by rfl) ⟨2339573, by rfl⟩ : syracuseStep 12477725 = 4679147) B4679147
theorem B1460863 : Blo 1459549 1460863 := bstep (se 1 (by rfl) ⟨1095647, by rfl⟩ : syracuseStep 1460863 = 2191295) B2191295
theorem B170765243 : Blo 1459549 170765243 := bstep (se 1 (by rfl) ⟨128073932, by rfl⟩ : syracuseStep 170765243 = 256147865) B256147865
theorem B16003631 : Blo 1459549 16003631 := bstep (se 1 (by rfl) ⟨12002723, by rfl⟩ : syracuseStep 16003631 = 24005447) B24005447
theorem B4675943 : Blo 1459549 4675943 := bstep (se 1 (by rfl) ⟨3506957, by rfl⟩ : syracuseStep 4675943 = 7013915) B7013915
theorem B3120295 : Blo 1459549 3120295 := bstep (se 1 (by rfl) ⟨2340221, by rfl⟩ : syracuseStep 3120295 = 4680443) B4680443
theorem B10669087 : Blo 1459549 10669087 := bstep (se 1 (by rfl) ⟨8001815, by rfl⟩ : syracuseStep 10669087 = 16003631) B16003631
theorem B8318483 : Blo 1459549 8318483 := bstep (se 1 (by rfl) ⟨6238862, by rfl⟩ : syracuseStep 8318483 = 12477725) B12477725
theorem B3117295 : Blo 1459549 3117295 := bstep (se 1 (by rfl) ⟨2337971, by rfl⟩ : syracuseStep 3117295 = 4675943) B4675943
theorem B4160393 : Blo 1459549 4160393 := bstep (se 2 (by rfl) ⟨1560147, by rfl⟩ : syracuseStep 4160393 = 3120295) B3120295
theorem B113843495 : Blo 1459549 113843495 := bstep (se 1 (by rfl) ⟨85382621, by rfl⟩ : syracuseStep 113843495 = 170765243) B170765243
theorem B56901797 : Blo 1459549 56901797 := bstep (se 4 (by rfl) ⟨5334543, by rfl⟩ : syracuseStep 56901797 = 10669087) B10669087
theorem B16625573 : Blo 1459549 16625573 := bstep (se 4 (by rfl) ⟨1558647, by rfl⟩ : syracuseStep 16625573 = 3117295) B3117295
theorem B2773595 : Blo 1459549 2773595 := bstep (se 1 (by rfl) ⟨2080196, by rfl⟩ : syracuseStep 2773595 = 4160393) B4160393
theorem B75895663 : Blo 1459549 75895663 := bstep (se 1 (by rfl) ⟨56921747, by rfl⟩ : syracuseStep 75895663 = 113843495) B113843495
theorem B5545655 : Blo 1459549 5545655 := bstep (se 1 (by rfl) ⟨4159241, by rfl⟩ : syracuseStep 5545655 = 8318483) B8318483
theorem B3697103 : Blo 1459549 3697103 := bstep (se 1 (by rfl) ⟨2772827, by rfl⟩ : syracuseStep 3697103 = 5545655) B5545655
theorem B37934531 : Blo 1459549 37934531 := bstep (se 1 (by rfl) ⟨28450898, by rfl⟩ : syracuseStep 37934531 = 56901797) B56901797
theorem B1849063 : Blo 1459549 1849063 := bstep (se 1 (by rfl) ⟨1386797, by rfl⟩ : syracuseStep 1849063 = 2773595) B2773595
theorem B101194217 : Blo 1459549 101194217 := bstep (se 2 (by rfl) ⟨37947831, by rfl⟩ : syracuseStep 101194217 = 75895663) B75895663
theorem B11083715 : Blo 1459549 11083715 := bstep (se 1 (by rfl) ⟨8312786, by rfl⟩ : syracuseStep 11083715 = 16625573) B16625573
theorem B25289687 : Blo 1459549 25289687 := bstep (se 1 (by rfl) ⟨18967265, by rfl⟩ : syracuseStep 25289687 = 37934531) B37934531
theorem B67462811 : Blo 1459549 67462811 := bstep (se 1 (by rfl) ⟨50597108, by rfl⟩ : syracuseStep 67462811 = 101194217) B101194217
theorem B2464735 : Blo 1459549 2464735 := bstep (se 1 (by rfl) ⟨1848551, by rfl⟩ : syracuseStep 2464735 = 3697103) B3697103
theorem B2465417 : Blo 1459549 2465417 := bstep (se 2 (by rfl) ⟨924531, by rfl⟩ : syracuseStep 2465417 = 1849063) B1849063
theorem B7389143 : Blo 1459549 7389143 := bstep (se 1 (by rfl) ⟨5541857, by rfl⟩ : syracuseStep 7389143 = 11083715) B11083715
theorem B16859791 : Blo 1459549 16859791 := bstep (se 1 (by rfl) ⟨12644843, by rfl⟩ : syracuseStep 16859791 = 25289687) B25289687
theorem B44975207 : Blo 1459549 44975207 := bstep (se 1 (by rfl) ⟨33731405, by rfl⟩ : syracuseStep 44975207 = 67462811) B67462811
theorem B3286313 : Blo 1459549 3286313 := bstep (se 2 (by rfl) ⟨1232367, by rfl⟩ : syracuseStep 3286313 = 2464735) B2464735
theorem B4926095 : Blo 1459549 4926095 := bstep (se 1 (by rfl) ⟨3694571, by rfl⟩ : syracuseStep 4926095 = 7389143) B7389143
theorem B1643611 : Blo 1459549 1643611 := bstep (se 1 (by rfl) ⟨1232708, by rfl⟩ : syracuseStep 1643611 = 2465417) B2465417
theorem B119933885 : Blo 1459549 119933885 := bstep (se 3 (by rfl) ⟨22487603, by rfl⟩ : syracuseStep 119933885 = 44975207) B44975207
theorem B89918885 : Blo 1459549 89918885 := bstep (se 4 (by rfl) ⟨8429895, by rfl⟩ : syracuseStep 89918885 = 16859791) B16859791
theorem B2190875 : Blo 1459549 2190875 := bstep (se 1 (by rfl) ⟨1643156, by rfl⟩ : syracuseStep 2190875 = 3286313) B3286313
theorem B2191481 : Blo 1459549 2191481 := bstep (se 2 (by rfl) ⟨821805, by rfl⟩ : syracuseStep 2191481 = 1643611) B1643611
theorem B3284063 : Blo 1459549 3284063 := bstep (se 1 (by rfl) ⟨2463047, by rfl⟩ : syracuseStep 3284063 = 4926095) B4926095
theorem B79955923 : Blo 1459549 79955923 := bstep (se 1 (by rfl) ⟨59966942, by rfl⟩ : syracuseStep 79955923 = 119933885) B119933885
theorem B2189375 : Blo 1459549 2189375 := bstep (se 1 (by rfl) ⟨1642031, by rfl⟩ : syracuseStep 2189375 = 3284063) B3284063
theorem B1460583 : Blo 1459549 1460583 := bstep (se 1 (by rfl) ⟨1095437, by rfl⟩ : syracuseStep 1460583 = 2190875) B2190875
theorem B1460987 : Blo 1459549 1460987 := bstep (se 1 (by rfl) ⟨1095740, by rfl⟩ : syracuseStep 1460987 = 2191481) B2191481
theorem B59945923 : Blo 1459549 59945923 := bstep (se 1 (by rfl) ⟨44959442, by rfl⟩ : syracuseStep 59945923 = 89918885) B89918885
theorem B1459583 : Blo 1459549 1459583 := bstep (se 1 (by rfl) ⟨1094687, by rfl⟩ : syracuseStep 1459583 = 2189375) B2189375
theorem B106607897 : Blo 1459549 106607897 := bstep (se 2 (by rfl) ⟨39977961, by rfl⟩ : syracuseStep 106607897 = 79955923) B79955923
theorem B79927897 : Blo 1459549 79927897 := bstep (se 2 (by rfl) ⟨29972961, by rfl⟩ : syracuseStep 79927897 = 59945923) B59945923
theorem B106570529 : Blo 1459549 106570529 := bstep (se 2 (by rfl) ⟨39963948, by rfl⟩ : syracuseStep 106570529 = 79927897) B79927897
theorem B71071931 : Blo 1459549 71071931 := bstep (se 1 (by rfl) ⟨53303948, by rfl⟩ : syracuseStep 71071931 = 106607897) B106607897
theorem B71047019 : Blo 1459549 71047019 := bstep (se 1 (by rfl) ⟨53285264, by rfl⟩ : syracuseStep 71047019 = 106570529) B106570529
theorem B47381287 : Blo 1459549 47381287 := bstep (se 1 (by rfl) ⟨35535965, by rfl⟩ : syracuseStep 47381287 = 71071931) B71071931
theorem B63175049 : Blo 1459549 63175049 := bstep (se 2 (by rfl) ⟨23690643, by rfl⟩ : syracuseStep 63175049 = 47381287) B47381287
theorem B47364679 : Blo 1459549 47364679 := bstep (se 1 (by rfl) ⟨35523509, by rfl⟩ : syracuseStep 47364679 = 71047019) B71047019
theorem B63152905 : Blo 1459549 63152905 := bstep (se 2 (by rfl) ⟨23682339, by rfl⟩ : syracuseStep 63152905 = 47364679) B47364679
theorem B42116699 : Blo 1459549 42116699 := bstep (se 1 (by rfl) ⟨31587524, by rfl⟩ : syracuseStep 42116699 = 63175049) B63175049
theorem B28077799 : Blo 1459549 28077799 := bstep (se 1 (by rfl) ⟨21058349, by rfl⟩ : syracuseStep 28077799 = 42116699) B42116699
theorem B84203873 : Blo 1459549 84203873 := bstep (se 2 (by rfl) ⟨31576452, by rfl⟩ : syracuseStep 84203873 = 63152905) B63152905
theorem B56135915 : Blo 1459549 56135915 := bstep (se 1 (by rfl) ⟨42101936, by rfl⟩ : syracuseStep 56135915 = 84203873) B84203873
theorem B37437065 : Blo 1459549 37437065 := bstep (se 2 (by rfl) ⟨14038899, by rfl⟩ : syracuseStep 37437065 = 28077799) B28077799
theorem B37423943 : Blo 1459549 37423943 := bstep (se 1 (by rfl) ⟨28067957, by rfl⟩ : syracuseStep 37423943 = 56135915) B56135915
theorem B24958043 : Blo 1459549 24958043 := bstep (se 1 (by rfl) ⟨18718532, by rfl⟩ : syracuseStep 24958043 = 37437065) B37437065
theorem B16638695 : Blo 1459549 16638695 := bstep (se 1 (by rfl) ⟨12479021, by rfl⟩ : syracuseStep 16638695 = 24958043) B24958043
theorem B24949295 : Blo 1459549 24949295 := bstep (se 1 (by rfl) ⟨18711971, by rfl⟩ : syracuseStep 24949295 = 37423943) B37423943
theorem B11092463 : Blo 1459549 11092463 := bstep (se 1 (by rfl) ⟨8319347, by rfl⟩ : syracuseStep 11092463 = 16638695) B16638695
theorem B16632863 : Blo 1459549 16632863 := bstep (se 1 (by rfl) ⟨12474647, by rfl⟩ : syracuseStep 16632863 = 24949295) B24949295
theorem B11088575 : Blo 1459549 11088575 := bstep (se 1 (by rfl) ⟨8316431, by rfl⟩ : syracuseStep 11088575 = 16632863) B16632863
theorem B7394975 : Blo 1459549 7394975 := bstep (se 1 (by rfl) ⟨5546231, by rfl⟩ : syracuseStep 7394975 = 11092463) B11092463
theorem B7392383 : Blo 1459549 7392383 := bstep (se 1 (by rfl) ⟨5544287, by rfl⟩ : syracuseStep 7392383 = 11088575) B11088575
theorem B4929983 : Blo 1459549 4929983 := bstep (se 1 (by rfl) ⟨3697487, by rfl⟩ : syracuseStep 4929983 = 7394975) B7394975
theorem B3286655 : Blo 1459549 3286655 := bstep (se 1 (by rfl) ⟨2464991, by rfl⟩ : syracuseStep 3286655 = 4929983) B4929983
theorem B4928255 : Blo 1459549 4928255 := bstep (se 1 (by rfl) ⟨3696191, by rfl⟩ : syracuseStep 4928255 = 7392383) B7392383
theorem B3285503 : Blo 1459549 3285503 := bstep (se 1 (by rfl) ⟨2464127, by rfl⟩ : syracuseStep 3285503 = 4928255) B4928255
theorem B2191103 : Blo 1459549 2191103 := bstep (se 1 (by rfl) ⟨1643327, by rfl⟩ : syracuseStep 2191103 = 3286655) B3286655
theorem B1460735 : Blo 1459549 1460735 := bstep (se 1 (by rfl) ⟨1095551, by rfl⟩ : syracuseStep 1460735 = 2191103) B2191103
theorem B2190335 : Blo 1459549 2190335 := bstep (se 1 (by rfl) ⟨1642751, by rfl⟩ : syracuseStep 2190335 = 3285503) B3285503
theorem B1460223 : Blo 1459549 1460223 := bstep (se 1 (by rfl) ⟨1095167, by rfl⟩ : syracuseStep 1460223 = 2190335) B2190335

theorem C0 (j : ℕ) (h1 : 364887 ≤ j) (h2 : j ≤ 365261) : Blo 1459549 (4 * j + 3) := by
  interval_cases j
  · exact B1459551
  · exact B1459555
  · exact B1459559
  · exact B1459563
  · exact B1459567
  · exact B1459571
  · exact B1459575
  · exact B1459579
  · exact B1459583
  · exact B1459587
  · exact B1459591
  · exact B1459595
  · exact B1459599
  · exact B1459603
  · exact B1459607
  · exact B1459611
  · exact B1459615
  · exact B1459619
  · exact B1459623
  · exact B1459627
  · exact B1459631
  · exact B1459635
  · exact B1459639
  · exact B1459643
  · exact B1459647
  · exact B1459651
  · exact B1459655
  · exact B1459659
  · exact B1459663
  · exact B1459667
  · exact B1459671
  · exact B1459675
  · exact B1459679
  · exact B1459683
  · exact B1459687
  · exact B1459691
  · exact B1459695
  · exact B1459699
  · exact B1459703
  · exact B1459707
  · exact B1459711
  · exact B1459715
  · exact B1459719
  · exact B1459723
  · exact B1459727
  · exact B1459731
  · exact B1459735
  · exact B1459739
  · exact B1459743
  · exact B1459747
  · exact B1459751
  · exact B1459755
  · exact B1459759
  · exact B1459763
  · exact B1459767
  · exact B1459771
  · exact B1459775
  · exact B1459779
  · exact B1459783
  · exact B1459787
  · exact B1459791
  · exact B1459795
  · exact B1459799
  · exact B1459803
  · exact B1459807
  · exact B1459811
  · exact B1459815
  · exact B1459819
  · exact B1459823
  · exact B1459827
  · exact B1459831
  · exact B1459835
  · exact B1459839
  · exact B1459843
  · exact B1459847
  · exact B1459851
  · exact B1459855
  · exact B1459859
  · exact B1459863
  · exact B1459867
  · exact B1459871
  · exact B1459875
  · exact B1459879
  · exact B1459883
  · exact B1459887
  · exact B1459891
  · exact B1459895
  · exact B1459899
  · exact B1459903
  · exact B1459907
  · exact B1459911
  · exact B1459915
  · exact B1459919
  · exact B1459923
  · exact B1459927
  · exact B1459931
  · exact B1459935
  · exact B1459939
  · exact B1459943
  · exact B1459947
  · exact B1459951
  · exact B1459955
  · exact B1459959
  · exact B1459963
  · exact B1459967
  · exact B1459971
  · exact B1459975
  · exact B1459979
  · exact B1459983
  · exact B1459987
  · exact B1459991
  · exact B1459995
  · exact B1459999
  · exact B1460003
  · exact B1460007
  · exact B1460011
  · exact B1460015
  · exact B1460019
  · exact B1460023
  · exact B1460027
  · exact B1460031
  · exact B1460035
  · exact B1460039
  · exact B1460043
  · exact B1460047
  · exact B1460051
  · exact B1460055
  · exact B1460059
  · exact B1460063
  · exact B1460067
  · exact B1460071
  · exact B1460075
  · exact B1460079
  · exact B1460083
  · exact B1460087
  · exact B1460091
  · exact B1460095
  · exact B1460099
  · exact B1460103
  · exact B1460107
  · exact B1460111
  · exact B1460115
  · exact B1460119
  · exact B1460123
  · exact B1460127
  · exact B1460131
  · exact B1460135
  · exact B1460139
  · exact B1460143
  · exact B1460147
  · exact B1460151
  · exact B1460155
  · exact B1460159
  · exact B1460163
  · exact B1460167
  · exact B1460171
  · exact B1460175
  · exact B1460179
  · exact B1460183
  · exact B1460187
  · exact B1460191
  · exact B1460195
  · exact B1460199
  · exact B1460203
  · exact B1460207
  · exact B1460211
  · exact B1460215
  · exact B1460219
  · exact B1460223
  · exact B1460227
  · exact B1460231
  · exact B1460235
  · exact B1460239
  · exact B1460243
  · exact B1460247
  · exact B1460251
  · exact B1460255
  · exact B1460259
  · exact B1460263
  · exact B1460267
  · exact B1460271
  · exact B1460275
  · exact B1460279
  · exact B1460283
  · exact B1460287
  · exact B1460291
  · exact B1460295
  · exact B1460299
  · exact B1460303
  · exact B1460307
  · exact B1460311
  · exact B1460315
  · exact B1460319
  · exact B1460323
  · exact B1460327
  · exact B1460331
  · exact B1460335
  · exact B1460339
  · exact B1460343
  · exact B1460347
  · exact B1460351
  · exact B1460355
  · exact B1460359
  · exact B1460363
  · exact B1460367
  · exact B1460371
  · exact B1460375
  · exact B1460379
  · exact B1460383
  · exact B1460387
  · exact B1460391
  · exact B1460395
  · exact B1460399
  · exact B1460403
  · exact B1460407
  · exact B1460411
  · exact B1460415
  · exact B1460419
  · exact B1460423
  · exact B1460427
  · exact B1460431
  · exact B1460435
  · exact B1460439
  · exact B1460443
  · exact B1460447
  · exact B1460451
  · exact B1460455
  · exact B1460459
  · exact B1460463
  · exact B1460467
  · exact B1460471
  · exact B1460475
  · exact B1460479
  · exact B1460483
  · exact B1460487
  · exact B1460491
  · exact B1460495
  · exact B1460499
  · exact B1460503
  · exact B1460507
  · exact B1460511
  · exact B1460515
  · exact B1460519
  · exact B1460523
  · exact B1460527
  · exact B1460531
  · exact B1460535
  · exact B1460539
  · exact B1460543
  · exact B1460547
  · exact B1460551
  · exact B1460555
  · exact B1460559
  · exact B1460563
  · exact B1460567
  · exact B1460571
  · exact B1460575
  · exact B1460579
  · exact B1460583
  · exact B1460587
  · exact B1460591
  · exact B1460595
  · exact B1460599
  · exact B1460603
  · exact B1460607
  · exact B1460611
  · exact B1460615
  · exact B1460619
  · exact B1460623
  · exact B1460627
  · exact B1460631
  · exact B1460635
  · exact B1460639
  · exact B1460643
  · exact B1460647
  · exact B1460651
  · exact B1460655
  · exact B1460659
  · exact B1460663
  · exact B1460667
  · exact B1460671
  · exact B1460675
  · exact B1460679
  · exact B1460683
  · exact B1460687
  · exact B1460691
  · exact B1460695
  · exact B1460699
  · exact B1460703
  · exact B1460707
  · exact B1460711
  · exact B1460715
  · exact B1460719
  · exact B1460723
  · exact B1460727
  · exact B1460731
  · exact B1460735
  · exact B1460739
  · exact B1460743
  · exact B1460747
  · exact B1460751
  · exact B1460755
  · exact B1460759
  · exact B1460763
  · exact B1460767
  · exact B1460771
  · exact B1460775
  · exact B1460779
  · exact B1460783
  · exact B1460787
  · exact B1460791
  · exact B1460795
  · exact B1460799
  · exact B1460803
  · exact B1460807
  · exact B1460811
  · exact B1460815
  · exact B1460819
  · exact B1460823
  · exact B1460827
  · exact B1460831
  · exact B1460835
  · exact B1460839
  · exact B1460843
  · exact B1460847
  · exact B1460851
  · exact B1460855
  · exact B1460859
  · exact B1460863
  · exact B1460867
  · exact B1460871
  · exact B1460875
  · exact B1460879
  · exact B1460883
  · exact B1460887
  · exact B1460891
  · exact B1460895
  · exact B1460899
  · exact B1460903
  · exact B1460907
  · exact B1460911
  · exact B1460915
  · exact B1460919
  · exact B1460923
  · exact B1460927
  · exact B1460931
  · exact B1460935
  · exact B1460939
  · exact B1460943
  · exact B1460947
  · exact B1460951
  · exact B1460955
  · exact B1460959
  · exact B1460963
  · exact B1460967
  · exact B1460971
  · exact B1460975
  · exact B1460979
  · exact B1460983
  · exact B1460987
  · exact B1460991
  · exact B1460995
  · exact B1460999
  · exact B1461003
  · exact B1461007
  · exact B1461011
  · exact B1461015
  · exact B1461019
  · exact B1461023
  · exact B1461027
  · exact B1461031
  · exact B1461035
  · exact B1461039
  · exact B1461043
  · exact B1461047

theorem solution (m : ℕ) (hlo : 1459549 ≤ m) (hhi : m ≤ 1461049) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 364887 ≤ j := by omega
    have hj2 : j ≤ 365261 := by omega
    have hb : Blo 1459549 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
