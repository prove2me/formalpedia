-- Prove2me | solution 1 for syracuse_descends_range_428775_432775
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:47:54.32531+00:00
-- url     : https://prove2.me/submissions/fd8bc134-6a09-4223-9b6e-82062b79a1bf

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


theorem B1376261 : Blo 428775 1376261 := bbase (se 4 (by rfl) ⟨129024, by rfl⟩ : syracuseStep 1376261 = 258049) (by norm_num)
theorem B589853 : Blo 428775 589853 := bbase (se 3 (by rfl) ⟨110597, by rfl⟩ : syracuseStep 589853 = 221195) (by norm_num)
theorem B819229 : Blo 428775 819229 := bbase (se 3 (by rfl) ⟨153605, by rfl⟩ : syracuseStep 819229 = 307211) (by norm_num)
theorem B917669 : Blo 428775 917669 := bbase (se 4 (by rfl) ⟨86031, by rfl⟩ : syracuseStep 917669 = 172063) (by norm_num)
theorem B819389 : Blo 428775 819389 := bbase (se 3 (by rfl) ⟨153635, by rfl⟩ : syracuseStep 819389 = 307271) (by norm_num)
theorem B458993 : Blo 428775 458993 := bbase (se 2 (by rfl) ⟨172122, by rfl⟩ : syracuseStep 458993 = 344245) (by norm_num)
theorem B459065 : Blo 428775 459065 := bbase (se 2 (by rfl) ⟨172149, by rfl⟩ : syracuseStep 459065 = 344299) (by norm_num)
theorem B819533 : Blo 428775 819533 := bbase (se 3 (by rfl) ⟨153662, by rfl⟩ : syracuseStep 819533 = 307325) (by norm_num)
theorem B885109 : Blo 428775 885109 := bbase (se 5 (by rfl) ⟨41489, by rfl⟩ : syracuseStep 885109 = 82979) (by norm_num)
theorem B459253 : Blo 428775 459253 := bbase (se 5 (by rfl) ⟨21527, by rfl⟩ : syracuseStep 459253 = 43055) (by norm_num)
theorem B819821 : Blo 428775 819821 := bbase (se 3 (by rfl) ⟨153716, by rfl⟩ : syracuseStep 819821 = 307433) (by norm_num)
theorem B688765 : Blo 428775 688765 := bbase (se 3 (by rfl) ⟨129143, by rfl⟩ : syracuseStep 688765 = 258287) (by norm_num)
theorem B459437 : Blo 428775 459437 := bbase (se 3 (by rfl) ⟨86144, by rfl⟩ : syracuseStep 459437 = 172289) (by norm_num)
theorem B819973 : Blo 428775 819973 := bbase (se 4 (by rfl) ⟨76872, by rfl⟩ : syracuseStep 819973 = 153745) (by norm_num)
theorem B492313 : Blo 428775 492313 := bbase (se 2 (by rfl) ⟨184617, by rfl⟩ : syracuseStep 492313 = 369235) (by norm_num)
theorem B2753365 : Blo 428775 2753365 := bbase (se 9 (by rfl) ⟨8066, by rfl⟩ : syracuseStep 2753365 = 16133) (by norm_num)
theorem B17662805 : Blo 428775 17662805 := bbase (se 9 (by rfl) ⟨51746, by rfl⟩ : syracuseStep 17662805 = 103493) (by norm_num)
theorem B918533 : Blo 428775 918533 := bbase (se 4 (by rfl) ⟨86112, by rfl⟩ : syracuseStep 918533 = 172225) (by norm_num)
theorem B820277 : Blo 428775 820277 := bbase (se 5 (by rfl) ⟨38450, by rfl⟩ : syracuseStep 820277 = 76901) (by norm_num)
theorem B689213 : Blo 428775 689213 := bbase (se 3 (by rfl) ⟨129227, by rfl⟩ : syracuseStep 689213 = 258455) (by norm_num)
theorem B918677 : Blo 428775 918677 := bbase (se 6 (by rfl) ⟨21531, by rfl⟩ : syracuseStep 918677 = 43063) (by norm_num)
theorem B885997 : Blo 428775 885997 := bbase (se 3 (by rfl) ⟨166124, by rfl⟩ : syracuseStep 885997 = 332249) (by norm_num)
theorem B3278069 : Blo 428775 3278069 := bbase (se 5 (by rfl) ⟨153659, by rfl⟩ : syracuseStep 3278069 = 307319) (by norm_num)
theorem B1377605 : Blo 428775 1377605 := bbase (se 4 (by rfl) ⟨129150, by rfl⟩ : syracuseStep 1377605 = 258301) (by norm_num)
theorem B460189 : Blo 428775 460189 := bbase (se 3 (by rfl) ⟨86285, by rfl⟩ : syracuseStep 460189 = 172571) (by norm_num)
theorem B460261 : Blo 428775 460261 := bbase (se 4 (by rfl) ⟨43149, by rfl⟩ : syracuseStep 460261 = 86299) (by norm_num)
theorem B1836533 : Blo 428775 1836533 := bbase (se 5 (by rfl) ⟨86087, by rfl⟩ : syracuseStep 1836533 = 172175) (by norm_num)
theorem B460441 : Blo 428775 460441 := bbase (se 2 (by rfl) ⟨172665, by rfl⟩ : syracuseStep 460441 = 345331) (by norm_num)
theorem B5605141 : Blo 428775 5605141 := bbase (se 6 (by rfl) ⟨131370, by rfl⟩ : syracuseStep 5605141 = 262741) (by norm_num)
theorem B558881 : Blo 428775 558881 := bbase (se 2 (by rfl) ⟨209580, by rfl⟩ : syracuseStep 558881 = 419161) (by norm_num)
theorem B526117 : Blo 428775 526117 := bbase (se 4 (by rfl) ⟨49323, by rfl⟩ : syracuseStep 526117 = 98647) (by norm_num)
theorem B821029 : Blo 428775 821029 := bbase (se 4 (by rfl) ⟨76971, by rfl⟩ : syracuseStep 821029 = 153943) (by norm_num)
theorem B3508085 : Blo 428775 3508085 := bbase (se 5 (by rfl) ⟨164441, by rfl⟩ : syracuseStep 3508085 = 328883) (by norm_num)
theorem B919421 : Blo 428775 919421 := bbase (se 3 (by rfl) ⟨172391, by rfl⟩ : syracuseStep 919421 = 344783) (by norm_num)
theorem B1640357 : Blo 428775 1640357 := bbase (se 4 (by rfl) ⟨153783, by rfl⟩ : syracuseStep 1640357 = 307567) (by norm_num)
theorem B821173 : Blo 428775 821173 := bbase (se 5 (by rfl) ⟨38492, by rfl⟩ : syracuseStep 821173 = 76985) (by norm_num)
theorem B526417 : Blo 428775 526417 := bbase (se 2 (by rfl) ⟨197406, by rfl⟩ : syracuseStep 526417 = 394813) (by norm_num)
theorem B460885 : Blo 428775 460885 := bbase (se 8 (by rfl) ⟨2700, by rfl⟩ : syracuseStep 460885 = 5401) (by norm_num)
theorem B821333 : Blo 428775 821333 := bbase (se 8 (by rfl) ⟨4812, by rfl⟩ : syracuseStep 821333 = 9625) (by norm_num)
theorem B591997 : Blo 428775 591997 := bbase (se 3 (by rfl) ⟨110999, by rfl⟩ : syracuseStep 591997 = 221999) (by norm_num)
theorem B1640645 : Blo 428775 1640645 := bbase (se 4 (by rfl) ⟨153810, by rfl⟩ : syracuseStep 1640645 = 307621) (by norm_num)
theorem B461009 : Blo 428775 461009 := bbase (se 2 (by rfl) ⟨172878, by rfl⟩ : syracuseStep 461009 = 345757) (by norm_num)
theorem B821477 : Blo 428775 821477 := bbase (se 4 (by rfl) ⟨77013, by rfl⟩ : syracuseStep 821477 = 154027) (by norm_num)
theorem B461261 : Blo 428775 461261 := bbase (se 3 (by rfl) ⟨86486, by rfl⟩ : syracuseStep 461261 = 172973) (by norm_num)
theorem B1837525 : Blo 428775 1837525 := bbase (se 7 (by rfl) ⟨21533, by rfl⟩ : syracuseStep 1837525 = 43067) (by norm_num)
theorem B690725 : Blo 428775 690725 := bbase (se 4 (by rfl) ⟨64755, by rfl⟩ : syracuseStep 690725 = 129511) (by norm_num)
theorem B920173 : Blo 428775 920173 := bbase (se 3 (by rfl) ⟨172532, by rfl⟩ : syracuseStep 920173 = 345065) (by norm_num)
theorem B723613 : Blo 428775 723613 := bbase (se 3 (by rfl) ⟨135677, by rfl⟩ : syracuseStep 723613 = 271355) (by norm_num)
theorem B690853 : Blo 428775 690853 := bbase (se 4 (by rfl) ⟨64767, by rfl⟩ : syracuseStep 690853 = 129535) (by norm_num)
theorem B985765 : Blo 428775 985765 := bbase (se 4 (by rfl) ⟨92415, by rfl⟩ : syracuseStep 985765 = 184831) (by norm_num)
theorem B723701 : Blo 428775 723701 := bbase (se 5 (by rfl) ⟨33923, by rfl⟩ : syracuseStep 723701 = 67847) (by norm_num)
theorem B920317 : Blo 428775 920317 := bbase (se 3 (by rfl) ⟨172559, by rfl⟩ : syracuseStep 920317 = 345119) (by norm_num)
theorem B559921 : Blo 428775 559921 := bbase (se 2 (by rfl) ⟨209970, by rfl⟩ : syracuseStep 559921 = 419941) (by norm_num)
theorem B723829 : Blo 428775 723829 := bbase (se 5 (by rfl) ⟨33929, by rfl⟩ : syracuseStep 723829 = 67859) (by norm_num)
theorem B461705 : Blo 428775 461705 := bbase (se 2 (by rfl) ⟨173139, by rfl⟩ : syracuseStep 461705 = 346279) (by norm_num)
theorem B723917 : Blo 428775 723917 := bbase (se 3 (by rfl) ⟨135734, by rfl⟩ : syracuseStep 723917 = 271469) (by norm_num)
theorem B724045 : Blo 428775 724045 := bbase (se 3 (by rfl) ⟨135758, by rfl⟩ : syracuseStep 724045 = 271517) (by norm_num)
theorem B920693 : Blo 428775 920693 := bbase (se 5 (by rfl) ⟨43157, by rfl⟩ : syracuseStep 920693 = 86315) (by norm_num)
theorem B461953 : Blo 428775 461953 := bbase (se 2 (by rfl) ⟨173232, by rfl⟩ : syracuseStep 461953 = 346465) (by norm_num)
theorem B724133 : Blo 428775 724133 := bbase (se 4 (by rfl) ⟨67887, by rfl⟩ : syracuseStep 724133 = 135775) (by norm_num)
theorem B1379605 : Blo 428775 1379605 := bbase (se 6 (by rfl) ⟨32334, by rfl⟩ : syracuseStep 1379605 = 64669) (by norm_num)
theorem B724261 : Blo 428775 724261 := bbase (se 4 (by rfl) ⟨67899, by rfl⟩ : syracuseStep 724261 = 135799) (by norm_num)
theorem B2461013 : Blo 428775 2461013 := bbase (se 11 (by rfl) ⟨1802, by rfl⟩ : syracuseStep 2461013 = 3605) (by norm_num)
theorem B1641829 : Blo 428775 1641829 := bbase (se 4 (by rfl) ⟨153921, by rfl⟩ : syracuseStep 1641829 = 307843) (by norm_num)
theorem B724349 : Blo 428775 724349 := bbase (se 3 (by rfl) ⟨135815, by rfl⟩ : syracuseStep 724349 = 271631) (by norm_num)
theorem B921061 : Blo 428775 921061 := bbase (se 4 (by rfl) ⟨86349, by rfl⟩ : syracuseStep 921061 = 172699) (by norm_num)
theorem B2100725 : Blo 428775 2100725 := bbase (se 5 (by rfl) ⟨98471, by rfl⟩ : syracuseStep 2100725 = 196943) (by norm_num)
theorem B724477 : Blo 428775 724477 := bbase (se 3 (by rfl) ⟨135839, by rfl⟩ : syracuseStep 724477 = 271679) (by norm_num)
theorem B1248821 : Blo 428775 1248821 := bbase (se 5 (by rfl) ⟨58538, by rfl⟩ : syracuseStep 1248821 = 117077) (by norm_num)
theorem B1183301 : Blo 428775 1183301 := bbase (se 4 (by rfl) ⟨110934, by rfl⟩ : syracuseStep 1183301 = 221869) (by norm_num)
theorem B724565 : Blo 428775 724565 := bbase (se 8 (by rfl) ⟨4245, by rfl⟩ : syracuseStep 724565 = 8491) (by norm_num)
theorem B2756213 : Blo 428775 2756213 := bbase (se 5 (by rfl) ⟨129197, by rfl⟩ : syracuseStep 2756213 = 258395) (by norm_num)
theorem B1642133 : Blo 428775 1642133 := bbase (se 6 (by rfl) ⟨38487, by rfl⟩ : syracuseStep 1642133 = 76975) (by norm_num)
theorem B724693 : Blo 428775 724693 := bbase (se 7 (by rfl) ⟨8492, by rfl⟩ : syracuseStep 724693 = 16985) (by norm_num)
theorem B724781 : Blo 428775 724781 := bbase (se 3 (by rfl) ⟨135896, by rfl⟩ : syracuseStep 724781 = 271793) (by norm_num)
theorem B1740613 : Blo 428775 1740613 := bbase (se 4 (by rfl) ⟨163182, by rfl⟩ : syracuseStep 1740613 = 326365) (by norm_num)
theorem B757621 : Blo 428775 757621 := bbase (se 5 (by rfl) ⟨35513, by rfl⟩ : syracuseStep 757621 = 71027) (by norm_num)
theorem B724909 : Blo 428775 724909 := bbase (se 3 (by rfl) ⟨135920, by rfl⟩ : syracuseStep 724909 = 271841) (by norm_num)
theorem B724997 : Blo 428775 724997 := bbase (se 4 (by rfl) ⟨67968, by rfl⟩ : syracuseStep 724997 = 135937) (by norm_num)
theorem B692237 : Blo 428775 692237 := bbase (se 3 (by rfl) ⟨129794, by rfl⟩ : syracuseStep 692237 = 259589) (by norm_num)
theorem B3313685 : Blo 428775 3313685 := bbase (se 6 (by rfl) ⟨77664, by rfl⟩ : syracuseStep 3313685 = 155329) (by norm_num)
theorem B1085501 : Blo 428775 1085501 := bbase (se 3 (by rfl) ⟨203531, by rfl⟩ : syracuseStep 1085501 = 407063) (by norm_num)
theorem B725125 : Blo 428775 725125 := bbase (se 4 (by rfl) ⟨67980, by rfl⟩ : syracuseStep 725125 = 135961) (by norm_num)
theorem B725213 : Blo 428775 725213 := bbase (se 3 (by rfl) ⟨135977, by rfl⟩ : syracuseStep 725213 = 271955) (by norm_num)
theorem B1315045 : Blo 428775 1315045 := bbase (se 4 (by rfl) ⟨123285, by rfl⟩ : syracuseStep 1315045 = 246571) (by norm_num)
theorem B495877 : Blo 428775 495877 := bbase (se 4 (by rfl) ⟨46488, by rfl⟩ : syracuseStep 495877 = 92977) (by norm_num)
theorem B1970453 : Blo 428775 1970453 := bbase (se 6 (by rfl) ⟨46182, by rfl⟩ : syracuseStep 1970453 = 92365) (by norm_num)
theorem B725341 : Blo 428775 725341 := bbase (se 3 (by rfl) ⟨136001, by rfl⟩ : syracuseStep 725341 = 272003) (by norm_num)
theorem B1085845 : Blo 428775 1085845 := bbase (se 6 (by rfl) ⟨25449, by rfl⟩ : syracuseStep 1085845 = 50899) (by norm_num)
theorem B725429 : Blo 428775 725429 := bbase (se 5 (by rfl) ⟨34004, by rfl⟩ : syracuseStep 725429 = 68009) (by norm_num)
theorem B2462197 : Blo 428775 2462197 := bbase (se 5 (by rfl) ⟨115415, by rfl⟩ : syracuseStep 2462197 = 230831) (by norm_num)
theorem B1085957 : Blo 428775 1085957 := bbase (se 4 (by rfl) ⟨101808, by rfl⟩ : syracuseStep 1085957 = 203617) (by norm_num)
theorem B725557 : Blo 428775 725557 := bbase (se 5 (by rfl) ⟨34010, by rfl⟩ : syracuseStep 725557 = 68021) (by norm_num)
theorem B725645 : Blo 428775 725645 := bbase (se 3 (by rfl) ⟨136058, by rfl⟩ : syracuseStep 725645 = 272117) (by norm_num)
theorem B1086149 : Blo 428775 1086149 := bbase (se 4 (by rfl) ⟨101826, by rfl⟩ : syracuseStep 1086149 = 203653) (by norm_num)
theorem B725773 : Blo 428775 725773 := bbase (se 3 (by rfl) ⟨136082, by rfl⟩ : syracuseStep 725773 = 272165) (by norm_num)
theorem B8262485 : Blo 428775 8262485 := bbase (se 9 (by rfl) ⟨24206, by rfl⟩ : syracuseStep 8262485 = 48413) (by norm_num)
theorem B725861 : Blo 428775 725861 := bbase (se 4 (by rfl) ⟨68049, by rfl⟩ : syracuseStep 725861 = 136099) (by norm_num)
theorem B693173 : Blo 428775 693173 := bbase (se 5 (by rfl) ⟨32492, by rfl⟩ : syracuseStep 693173 = 64985) (by norm_num)
theorem B922565 : Blo 428775 922565 := bbase (se 4 (by rfl) ⟨86490, by rfl⟩ : syracuseStep 922565 = 172981) (by norm_num)
theorem B725989 : Blo 428775 725989 := bbase (se 4 (by rfl) ⟨68061, by rfl⟩ : syracuseStep 725989 = 136123) (by norm_num)
theorem B1086493 : Blo 428775 1086493 := bbase (se 3 (by rfl) ⟨203717, by rfl⟩ : syracuseStep 1086493 = 407435) (by norm_num)
theorem B726077 : Blo 428775 726077 := bbase (se 3 (by rfl) ⟨136139, by rfl⟩ : syracuseStep 726077 = 272279) (by norm_num)
theorem B922709 : Blo 428775 922709 := bbase (se 8 (by rfl) ⟨5406, by rfl⟩ : syracuseStep 922709 = 10813) (by norm_num)
theorem B3675253 : Blo 428775 3675253 := bbase (se 5 (by rfl) ⟨172277, by rfl⟩ : syracuseStep 3675253 = 344555) (by norm_num)
theorem B2069621 : Blo 428775 2069621 := bbase (se 5 (by rfl) ⟨97013, by rfl⟩ : syracuseStep 2069621 = 194027) (by norm_num)
theorem B1086605 : Blo 428775 1086605 := bbase (se 3 (by rfl) ⟨203738, by rfl⟩ : syracuseStep 1086605 = 407477) (by norm_num)
theorem B726205 : Blo 428775 726205 := bbase (se 3 (by rfl) ⟨136163, by rfl⟩ : syracuseStep 726205 = 272327) (by norm_num)
theorem B726293 : Blo 428775 726293 := bbase (se 6 (by rfl) ⟨17022, by rfl⟩ : syracuseStep 726293 = 34045) (by norm_num)
theorem B1086797 : Blo 428775 1086797 := bbase (se 3 (by rfl) ⟨203774, by rfl⟩ : syracuseStep 1086797 = 407549) (by norm_num)
theorem B1447253 : Blo 428775 1447253 := bbase (se 14 (by rfl) ⟨132, by rfl⟩ : syracuseStep 1447253 = 265) (by norm_num)
theorem B464221 : Blo 428775 464221 := bbase (se 3 (by rfl) ⟨87041, by rfl⟩ : syracuseStep 464221 = 174083) (by norm_num)
theorem B726421 : Blo 428775 726421 := bbase (se 6 (by rfl) ⟨17025, by rfl⟩ : syracuseStep 726421 = 34051) (by norm_num)
theorem B923069 : Blo 428775 923069 := bbase (se 3 (by rfl) ⟨173075, by rfl⟩ : syracuseStep 923069 = 346151) (by norm_num)
theorem B726509 : Blo 428775 726509 := bbase (se 3 (by rfl) ⟨136220, by rfl⟩ : syracuseStep 726509 = 272441) (by norm_num)
theorem B661069 : Blo 428775 661069 := bbase (se 3 (by rfl) ⟨123950, by rfl⟩ : syracuseStep 661069 = 247901) (by norm_num)
theorem B726637 : Blo 428775 726637 := bbase (se 3 (by rfl) ⟨136244, by rfl⟩ : syracuseStep 726637 = 272489) (by norm_num)
theorem B1087141 : Blo 428775 1087141 := bbase (se 4 (by rfl) ⟨101919, by rfl⟩ : syracuseStep 1087141 = 203839) (by norm_num)
theorem B1971877 : Blo 428775 1971877 := bbase (se 4 (by rfl) ⟨184863, by rfl⟩ : syracuseStep 1971877 = 369727) (by norm_num)
theorem B726725 : Blo 428775 726725 := bbase (se 4 (by rfl) ⟨68130, by rfl⟩ : syracuseStep 726725 = 136261) (by norm_num)
theorem B1447685 : Blo 428775 1447685 := bbase (se 4 (by rfl) ⟨135720, by rfl⟩ : syracuseStep 1447685 = 271441) (by norm_num)
theorem B1087253 : Blo 428775 1087253 := bbase (se 6 (by rfl) ⟨25482, by rfl⟩ : syracuseStep 1087253 = 50965) (by norm_num)
theorem B726853 : Blo 428775 726853 := bbase (se 4 (by rfl) ⟨68142, by rfl⟩ : syracuseStep 726853 = 136285) (by norm_num)
theorem B726941 : Blo 428775 726941 := bbase (se 3 (by rfl) ⟨136301, by rfl⟩ : syracuseStep 726941 = 272603) (by norm_num)
theorem B1087445 : Blo 428775 1087445 := bbase (se 7 (by rfl) ⟨12743, by rfl⟩ : syracuseStep 1087445 = 25487) (by norm_num)
theorem B727069 : Blo 428775 727069 := bbase (se 3 (by rfl) ⟨136325, by rfl⟩ : syracuseStep 727069 = 272651) (by norm_num)
theorem B727157 : Blo 428775 727157 := bbase (se 5 (by rfl) ⟨34085, by rfl⟩ : syracuseStep 727157 = 68171) (by norm_num)
theorem B1448117 : Blo 428775 1448117 := bbase (se 5 (by rfl) ⟨67880, by rfl⟩ : syracuseStep 1448117 = 135761) (by norm_num)
theorem B1382629 : Blo 428775 1382629 := bbase (se 4 (by rfl) ⟨129621, by rfl⟩ : syracuseStep 1382629 = 259243) (by norm_num)
theorem B727285 : Blo 428775 727285 := bbase (se 5 (by rfl) ⟨34091, by rfl⟩ : syracuseStep 727285 = 68183) (by norm_num)
theorem B1087789 : Blo 428775 1087789 := bbase (se 3 (by rfl) ⟨203960, by rfl⟩ : syracuseStep 1087789 = 407921) (by norm_num)
theorem B923957 : Blo 428775 923957 := bbase (se 5 (by rfl) ⟨43310, by rfl⟩ : syracuseStep 923957 = 86621) (by norm_num)
theorem B727373 : Blo 428775 727373 := bbase (se 3 (by rfl) ⟨136382, by rfl⟩ : syracuseStep 727373 = 272765) (by norm_num)
theorem B1087901 : Blo 428775 1087901 := bbase (se 3 (by rfl) ⟨203981, by rfl⟩ : syracuseStep 1087901 = 407963) (by norm_num)
theorem B2464181 : Blo 428775 2464181 := bbase (se 5 (by rfl) ⟨115508, by rfl⟩ : syracuseStep 2464181 = 231017) (by norm_num)
theorem B727501 : Blo 428775 727501 := bbase (se 3 (by rfl) ⟨136406, by rfl⟩ : syracuseStep 727501 = 272813) (by norm_num)
theorem B727589 : Blo 428775 727589 := bbase (se 4 (by rfl) ⟨68211, by rfl⟩ : syracuseStep 727589 = 136423) (by norm_num)
theorem B924205 : Blo 428775 924205 := bbase (se 3 (by rfl) ⟨173288, by rfl⟩ : syracuseStep 924205 = 346577) (by norm_num)
theorem B1088093 : Blo 428775 1088093 := bbase (se 3 (by rfl) ⟨204017, by rfl⟩ : syracuseStep 1088093 = 408035) (by norm_num)
theorem B1448549 : Blo 428775 1448549 := bbase (se 4 (by rfl) ⟨135801, by rfl⟩ : syracuseStep 1448549 = 271603) (by norm_num)
theorem B498317 : Blo 428775 498317 := bbase (se 3 (by rfl) ⟨93434, by rfl⟩ : syracuseStep 498317 = 186869) (by norm_num)
theorem B727717 : Blo 428775 727717 := bbase (se 4 (by rfl) ⟨68223, by rfl⟩ : syracuseStep 727717 = 136447) (by norm_num)
theorem B727805 : Blo 428775 727805 := bbase (se 3 (by rfl) ⟨136463, by rfl⟩ : syracuseStep 727805 = 272927) (by norm_num)
theorem B727933 : Blo 428775 727933 := bbase (se 3 (by rfl) ⟨136487, by rfl⟩ : syracuseStep 727933 = 272975) (by norm_num)
theorem B1088437 : Blo 428775 1088437 := bbase (se 5 (by rfl) ⟨51020, by rfl⟩ : syracuseStep 1088437 = 102041) (by norm_num)
theorem B728021 : Blo 428775 728021 := bbase (se 7 (by rfl) ⟨8531, by rfl⟩ : syracuseStep 728021 = 17063) (by norm_num)
theorem B1448981 : Blo 428775 1448981 := bbase (se 6 (by rfl) ⟨33960, by rfl⟩ : syracuseStep 1448981 = 67921) (by norm_num)
theorem B1088549 : Blo 428775 1088549 := bbase (se 4 (by rfl) ⟨102051, by rfl⟩ : syracuseStep 1088549 = 204103) (by norm_num)
theorem B3677237 : Blo 428775 3677237 := bbase (se 5 (by rfl) ⟨172370, by rfl⟩ : syracuseStep 3677237 = 344741) (by norm_num)
theorem B728149 : Blo 428775 728149 := bbase (se 8 (by rfl) ⟨4266, by rfl⟩ : syracuseStep 728149 = 8533) (by norm_num)
theorem B728237 : Blo 428775 728237 := bbase (se 3 (by rfl) ⟨136544, by rfl⟩ : syracuseStep 728237 = 273089) (by norm_num)
theorem B2202805 : Blo 428775 2202805 := bbase (se 5 (by rfl) ⟨103256, by rfl⟩ : syracuseStep 2202805 = 206513) (by norm_num)
theorem B1088741 : Blo 428775 1088741 := bbase (se 4 (by rfl) ⟨102069, by rfl⟩ : syracuseStep 1088741 = 204139) (by norm_num)
theorem B728365 : Blo 428775 728365 := bbase (se 3 (by rfl) ⟨136568, by rfl⟩ : syracuseStep 728365 = 273137) (by norm_num)
theorem B1842533 : Blo 428775 1842533 := bbase (se 4 (by rfl) ⟨172737, by rfl⟩ : syracuseStep 1842533 = 345475) (by norm_num)
theorem B728453 : Blo 428775 728453 := bbase (se 4 (by rfl) ⟨68292, by rfl⟩ : syracuseStep 728453 = 136585) (by norm_num)
theorem B1449413 : Blo 428775 1449413 := bbase (se 4 (by rfl) ⟨135882, by rfl⟩ : syracuseStep 1449413 = 271765) (by norm_num)
theorem B826853 : Blo 428775 826853 := bbase (se 4 (by rfl) ⟨77517, by rfl⟩ : syracuseStep 826853 = 155035) (by norm_num)
theorem B728581 : Blo 428775 728581 := bbase (se 4 (by rfl) ⟨68304, by rfl⟩ : syracuseStep 728581 = 136609) (by norm_num)
theorem B1089085 : Blo 428775 1089085 := bbase (se 3 (by rfl) ⟨204203, by rfl⟩ : syracuseStep 1089085 = 408407) (by norm_num)
theorem B728669 : Blo 428775 728669 := bbase (se 3 (by rfl) ⟨136625, by rfl⟩ : syracuseStep 728669 = 273251) (by norm_num)
theorem B1842821 : Blo 428775 1842821 := bbase (se 4 (by rfl) ⟨172764, by rfl⟩ : syracuseStep 1842821 = 345529) (by norm_num)
theorem B1089197 : Blo 428775 1089197 := bbase (se 3 (by rfl) ⟨204224, by rfl⟩ : syracuseStep 1089197 = 408449) (by norm_num)
theorem B5545685 : Blo 428775 5545685 := bbase (se 7 (by rfl) ⟨64988, by rfl⟩ : syracuseStep 5545685 = 129977) (by norm_num)
theorem B728797 : Blo 428775 728797 := bbase (se 3 (by rfl) ⟨136649, by rfl⟩ : syracuseStep 728797 = 273299) (by norm_num)
theorem B728885 : Blo 428775 728885 := bbase (se 5 (by rfl) ⟨34166, by rfl⟩ : syracuseStep 728885 = 68333) (by norm_num)
theorem B2072405 : Blo 428775 2072405 := bbase (se 9 (by rfl) ⟨6071, by rfl⟩ : syracuseStep 2072405 = 12143) (by norm_num)
theorem B1089389 : Blo 428775 1089389 := bbase (se 3 (by rfl) ⟨204260, by rfl⟩ : syracuseStep 1089389 = 408521) (by norm_num)
theorem B1449845 : Blo 428775 1449845 := bbase (se 5 (by rfl) ⟨67961, by rfl⟩ : syracuseStep 1449845 = 135923) (by norm_num)
theorem B729013 : Blo 428775 729013 := bbase (se 5 (by rfl) ⟨34172, by rfl⟩ : syracuseStep 729013 = 68345) (by norm_num)
theorem B729101 : Blo 428775 729101 := bbase (se 3 (by rfl) ⟨136706, by rfl⟩ : syracuseStep 729101 = 273413) (by norm_num)
theorem B729229 : Blo 428775 729229 := bbase (se 3 (by rfl) ⟨136730, by rfl⟩ : syracuseStep 729229 = 273461) (by norm_num)
theorem B1089733 : Blo 428775 1089733 := bbase (se 4 (by rfl) ⟨102162, by rfl⟩ : syracuseStep 1089733 = 204325) (by norm_num)
theorem B729317 : Blo 428775 729317 := bbase (se 4 (by rfl) ⟨68373, by rfl⟩ : syracuseStep 729317 = 136747) (by norm_num)
theorem B1450277 : Blo 428775 1450277 := bbase (se 4 (by rfl) ⟨135963, by rfl⟩ : syracuseStep 1450277 = 271927) (by norm_num)
theorem B1089845 : Blo 428775 1089845 := bbase (se 5 (by rfl) ⟨51086, by rfl⟩ : syracuseStep 1089845 = 102173) (by norm_num)
theorem B729445 : Blo 428775 729445 := bbase (se 4 (by rfl) ⟨68385, by rfl⟩ : syracuseStep 729445 = 136771) (by norm_num)
theorem B1843573 : Blo 428775 1843573 := bbase (se 5 (by rfl) ⟨86417, by rfl⟩ : syracuseStep 1843573 = 172835) (by norm_num)
theorem B2171285 : Blo 428775 2171285 := bbase (se 6 (by rfl) ⟨50889, by rfl⟩ : syracuseStep 2171285 = 101779) (by norm_num)
theorem B827837 : Blo 428775 827837 := bbase (se 3 (by rfl) ⟨155219, by rfl⟩ : syracuseStep 827837 = 310439) (by norm_num)
theorem B729533 : Blo 428775 729533 := bbase (se 3 (by rfl) ⟨136787, by rfl⟩ : syracuseStep 729533 = 273575) (by norm_num)
theorem B1090037 : Blo 428775 1090037 := bbase (se 5 (by rfl) ⟨51095, by rfl⟩ : syracuseStep 1090037 = 102191) (by norm_num)
theorem B729661 : Blo 428775 729661 := bbase (se 3 (by rfl) ⟨136811, by rfl⟩ : syracuseStep 729661 = 273623) (by norm_num)
theorem B434765 : Blo 428775 434765 := bbase (se 3 (by rfl) ⟨81518, by rfl⟩ : syracuseStep 434765 = 163037) (by norm_num)
theorem B4956821 : Blo 428775 4956821 := bbase (se 6 (by rfl) ⟨116175, by rfl⟩ : syracuseStep 4956821 = 232351) (by norm_num)
theorem B729749 : Blo 428775 729749 := bbase (se 6 (by rfl) ⟨17103, by rfl⟩ : syracuseStep 729749 = 34207) (by norm_num)
theorem B1450709 : Blo 428775 1450709 := bbase (se 7 (by rfl) ⟨17000, by rfl⟩ : syracuseStep 1450709 = 34001) (by norm_num)
theorem B729877 : Blo 428775 729877 := bbase (se 6 (by rfl) ⟨17106, by rfl⟩ : syracuseStep 729877 = 34213) (by norm_num)
theorem B1090381 : Blo 428775 1090381 := bbase (se 3 (by rfl) ⟨204446, by rfl⟩ : syracuseStep 1090381 = 408893) (by norm_num)
theorem B3285845 : Blo 428775 3285845 := bbase (se 9 (by rfl) ⟨9626, by rfl⟩ : syracuseStep 3285845 = 19253) (by norm_num)
theorem B729965 : Blo 428775 729965 := bbase (se 3 (by rfl) ⟨136868, by rfl⟩ : syracuseStep 729965 = 273737) (by norm_num)
theorem B1090493 : Blo 428775 1090493 := bbase (se 3 (by rfl) ⟨204467, by rfl⟩ : syracuseStep 1090493 = 408935) (by norm_num)
theorem B730093 : Blo 428775 730093 := bbase (se 3 (by rfl) ⟨136892, by rfl⟩ : syracuseStep 730093 = 273785) (by norm_num)
theorem B1385525 : Blo 428775 1385525 := bbase (se 5 (by rfl) ⟨64946, by rfl⟩ : syracuseStep 1385525 = 129893) (by norm_num)
theorem B730181 : Blo 428775 730181 := bbase (se 4 (by rfl) ⟨68454, by rfl⟩ : syracuseStep 730181 = 136909) (by norm_num)
theorem B5022805 : Blo 428775 5022805 := bbase (se 8 (by rfl) ⟨29430, by rfl⟩ : syracuseStep 5022805 = 58861) (by norm_num)
theorem B6202453 : Blo 428775 6202453 := bbase (se 8 (by rfl) ⟨36342, by rfl⟩ : syracuseStep 6202453 = 72685) (by norm_num)
theorem B1844309 : Blo 428775 1844309 := bbase (se 8 (by rfl) ⟨10806, by rfl⟩ : syracuseStep 1844309 = 21613) (by norm_num)
theorem B1090685 : Blo 428775 1090685 := bbase (se 3 (by rfl) ⟨204503, by rfl⟩ : syracuseStep 1090685 = 409007) (by norm_num)
theorem B1451141 : Blo 428775 1451141 := bbase (se 4 (by rfl) ⟨136044, by rfl⟩ : syracuseStep 1451141 = 272089) (by norm_num)
theorem B730309 : Blo 428775 730309 := bbase (se 4 (by rfl) ⟨68466, by rfl⟩ : syracuseStep 730309 = 136933) (by norm_num)
theorem B435413 : Blo 428775 435413 := bbase (se 7 (by rfl) ⟨5102, by rfl⟩ : syracuseStep 435413 = 10205) (by norm_num)
theorem B1221941 : Blo 428775 1221941 := bbase (se 5 (by rfl) ⟨57278, by rfl⟩ : syracuseStep 1221941 = 114557) (by norm_num)
theorem B435665 : Blo 428775 435665 := bbase (se 2 (by rfl) ⟨163374, by rfl⟩ : syracuseStep 435665 = 326749) (by norm_num)
theorem B1091029 : Blo 428775 1091029 := bbase (se 7 (by rfl) ⟨12785, by rfl⟩ : syracuseStep 1091029 = 25571) (by norm_num)
theorem B1123877 : Blo 428775 1123877 := bbase (se 4 (by rfl) ⟨105363, by rfl⟩ : syracuseStep 1123877 = 210727) (by norm_num)
theorem B1451573 : Blo 428775 1451573 := bbase (se 5 (by rfl) ⟨68042, by rfl⟩ : syracuseStep 1451573 = 136085) (by norm_num)
theorem B1091141 : Blo 428775 1091141 := bbase (se 4 (by rfl) ⟨102294, by rfl⟩ : syracuseStep 1091141 = 204589) (by norm_num)
theorem B1746517 : Blo 428775 1746517 := bbase (se 8 (by rfl) ⟨10233, by rfl⟩ : syracuseStep 1746517 = 20467) (by norm_num)
theorem B2172581 : Blo 428775 2172581 := bbase (se 4 (by rfl) ⟨203679, by rfl⟩ : syracuseStep 2172581 = 407359) (by norm_num)
theorem B1091333 : Blo 428775 1091333 := bbase (se 4 (by rfl) ⟨102312, by rfl⟩ : syracuseStep 1091333 = 204625) (by norm_num)
theorem B1452005 : Blo 428775 1452005 := bbase (se 4 (by rfl) ⟨136125, by rfl⟩ : syracuseStep 1452005 = 272251) (by norm_num)
theorem B1091677 : Blo 428775 1091677 := bbase (se 3 (by rfl) ⟨204689, by rfl⟩ : syracuseStep 1091677 = 409379) (by norm_num)
theorem B3582133 : Blo 428775 3582133 := bbase (se 5 (by rfl) ⟨167912, by rfl⟩ : syracuseStep 3582133 = 335825) (by norm_num)
theorem B1091789 : Blo 428775 1091789 := bbase (se 3 (by rfl) ⟨204710, by rfl⟩ : syracuseStep 1091789 = 409421) (by norm_num)
theorem B1091981 : Blo 428775 1091981 := bbase (se 3 (by rfl) ⟨204746, by rfl⟩ : syracuseStep 1091981 = 409493) (by norm_num)
theorem B1452437 : Blo 428775 1452437 := bbase (se 6 (by rfl) ⟨34041, by rfl⟩ : syracuseStep 1452437 = 68083) (by norm_num)
theorem B1550789 : Blo 428775 1550789 := bbase (se 4 (by rfl) ⟨145386, by rfl⟩ : syracuseStep 1550789 = 290773) (by norm_num)
theorem B436921 : Blo 428775 436921 := bbase (se 2 (by rfl) ⟨163845, by rfl⟩ : syracuseStep 436921 = 327691) (by norm_num)
theorem B2337493 : Blo 428775 2337493 := bbase (se 7 (by rfl) ⟨27392, by rfl⟩ : syracuseStep 2337493 = 54785) (by norm_num)
theorem B1092325 : Blo 428775 1092325 := bbase (se 4 (by rfl) ⟨102405, by rfl⟩ : syracuseStep 1092325 = 204811) (by norm_num)
theorem B1452869 : Blo 428775 1452869 := bbase (se 4 (by rfl) ⟨136206, by rfl⟩ : syracuseStep 1452869 = 272413) (by norm_num)
theorem B1092437 : Blo 428775 1092437 := bbase (se 9 (by rfl) ⟨3200, by rfl⟩ : syracuseStep 1092437 = 6401) (by norm_num)
theorem B1223525 : Blo 428775 1223525 := bbase (se 4 (by rfl) ⟨114705, by rfl⟩ : syracuseStep 1223525 = 229411) (by norm_num)
theorem B1551221 : Blo 428775 1551221 := bbase (se 5 (by rfl) ⟨72713, by rfl⟩ : syracuseStep 1551221 = 145427) (by norm_num)
theorem B2173877 : Blo 428775 2173877 := bbase (se 5 (by rfl) ⟨101900, by rfl⟩ : syracuseStep 2173877 = 203801) (by norm_num)
theorem B1092629 : Blo 428775 1092629 := bbase (se 6 (by rfl) ⟨25608, by rfl⟩ : syracuseStep 1092629 = 51217) (by norm_num)
theorem B1453301 : Blo 428775 1453301 := bbase (se 5 (by rfl) ⟨68123, by rfl⟩ : syracuseStep 1453301 = 136247) (by norm_num)
theorem B5680469 : Blo 428775 5680469 := bbase (se 11 (by rfl) ⟨4160, by rfl⟩ : syracuseStep 5680469 = 8321) (by norm_num)
theorem B1092973 : Blo 428775 1092973 := bbase (se 3 (by rfl) ⟨204932, by rfl⟩ : syracuseStep 1092973 = 409865) (by norm_num)
theorem B1093085 : Blo 428775 1093085 := bbase (se 3 (by rfl) ⟨204953, by rfl⟩ : syracuseStep 1093085 = 409907) (by norm_num)
theorem B1224197 : Blo 428775 1224197 := bbase (se 4 (by rfl) ⟨114768, by rfl⟩ : syracuseStep 1224197 = 229537) (by norm_num)
theorem B1093277 : Blo 428775 1093277 := bbase (se 3 (by rfl) ⟨204989, by rfl⟩ : syracuseStep 1093277 = 409979) (by norm_num)
theorem B1453733 : Blo 428775 1453733 := bbase (se 4 (by rfl) ⟨136287, by rfl⟩ : syracuseStep 1453733 = 272575) (by norm_num)
theorem B438053 : Blo 428775 438053 := bbase (se 4 (by rfl) ⟨41067, by rfl⟩ : syracuseStep 438053 = 82135) (by norm_num)
theorem B1224629 : Blo 428775 1224629 := bbase (se 5 (by rfl) ⟨57404, by rfl⟩ : syracuseStep 1224629 = 114809) (by norm_num)
theorem B1093621 : Blo 428775 1093621 := bbase (se 5 (by rfl) ⟨51263, by rfl⟩ : syracuseStep 1093621 = 102527) (by norm_num)
theorem B1454165 : Blo 428775 1454165 := bbase (se 8 (by rfl) ⟨8520, by rfl⟩ : syracuseStep 1454165 = 17041) (by norm_num)
theorem B1093733 : Blo 428775 1093733 := bbase (se 4 (by rfl) ⟨102537, by rfl⟩ : syracuseStep 1093733 = 205075) (by norm_num)
theorem B2175173 : Blo 428775 2175173 := bbase (se 4 (by rfl) ⟨203922, by rfl⟩ : syracuseStep 2175173 = 407845) (by norm_num)
theorem B1093925 : Blo 428775 1093925 := bbase (se 4 (by rfl) ⟨102555, by rfl⟩ : syracuseStep 1093925 = 205111) (by norm_num)
theorem B1847605 : Blo 428775 1847605 := bbase (se 5 (by rfl) ⟨86606, by rfl⟩ : syracuseStep 1847605 = 173213) (by norm_num)
theorem B537077 : Blo 428775 537077 := bbase (se 5 (by rfl) ⟨25175, by rfl⟩ : syracuseStep 537077 = 50351) (by norm_num)
theorem B1454597 : Blo 428775 1454597 := bbase (se 4 (by rfl) ⟨136368, by rfl⟩ : syracuseStep 1454597 = 272737) (by norm_num)
theorem B1094269 : Blo 428775 1094269 := bbase (se 3 (by rfl) ⟨205175, by rfl⟩ : syracuseStep 1094269 = 410351) (by norm_num)
theorem B1225381 : Blo 428775 1225381 := bbase (se 4 (by rfl) ⟨114879, by rfl⟩ : syracuseStep 1225381 = 229759) (by norm_num)
theorem B1094381 : Blo 428775 1094381 := bbase (se 3 (by rfl) ⟨205196, by rfl⟩ : syracuseStep 1094381 = 410393) (by norm_num)
theorem B4141813 : Blo 428775 4141813 := bbase (se 5 (by rfl) ⟨194147, by rfl⟩ : syracuseStep 4141813 = 388295) (by norm_num)
theorem B1094573 : Blo 428775 1094573 := bbase (se 3 (by rfl) ⟨205232, by rfl⟩ : syracuseStep 1094573 = 410465) (by norm_num)
theorem B1455029 : Blo 428775 1455029 := bbase (se 5 (by rfl) ⟨68204, by rfl⟩ : syracuseStep 1455029 = 136409) (by norm_num)
theorem B472153 : Blo 428775 472153 := bbase (se 2 (by rfl) ⟨177057, by rfl⟩ : syracuseStep 472153 = 354115) (by norm_num)
theorem B1094917 : Blo 428775 1094917 := bbase (se 4 (by rfl) ⟨102648, by rfl⟩ : syracuseStep 1094917 = 205297) (by norm_num)
theorem B1455461 : Blo 428775 1455461 := bbase (se 4 (by rfl) ⟨136449, by rfl⟩ : syracuseStep 1455461 = 272899) (by norm_num)
theorem B1095029 : Blo 428775 1095029 := bbase (se 5 (by rfl) ⟨51329, by rfl⟩ : syracuseStep 1095029 = 102659) (by norm_num)
theorem B3716533 : Blo 428775 3716533 := bbase (se 5 (by rfl) ⟨174212, by rfl⟩ : syracuseStep 3716533 = 348425) (by norm_num)
theorem B2176469 : Blo 428775 2176469 := bbase (se 7 (by rfl) ⟨25505, by rfl⟩ : syracuseStep 2176469 = 51011) (by norm_num)
theorem B1095221 : Blo 428775 1095221 := bbase (se 5 (by rfl) ⟨51338, by rfl⟩ : syracuseStep 1095221 = 102677) (by norm_num)
theorem B1160885 : Blo 428775 1160885 := bbase (se 5 (by rfl) ⟨54416, by rfl⟩ : syracuseStep 1160885 = 108833) (by norm_num)
theorem B1455893 : Blo 428775 1455893 := bbase (se 6 (by rfl) ⟨34122, by rfl⟩ : syracuseStep 1455893 = 68245) (by norm_num)
theorem B702437 : Blo 428775 702437 := bbase (se 4 (by rfl) ⟨65853, by rfl⟩ : syracuseStep 702437 = 131707) (by norm_num)
theorem B997469 : Blo 428775 997469 := bbase (se 3 (by rfl) ⟨187025, by rfl⟩ : syracuseStep 997469 = 374051) (by norm_num)
theorem B1554565 : Blo 428775 1554565 := bbase (se 4 (by rfl) ⟨145740, by rfl⟩ : syracuseStep 1554565 = 291481) (by norm_num)
theorem B964781 : Blo 428775 964781 := bbase (se 3 (by rfl) ⟨180896, by rfl⟩ : syracuseStep 964781 = 361793) (by norm_num)
theorem B1456325 : Blo 428775 1456325 := bbase (se 4 (by rfl) ⟨136530, by rfl⟩ : syracuseStep 1456325 = 273061) (by norm_num)
theorem B964853 : Blo 428775 964853 := bbase (se 5 (by rfl) ⟨45227, by rfl⟩ : syracuseStep 964853 = 90455) (by norm_num)
theorem B964925 : Blo 428775 964925 := bbase (se 3 (by rfl) ⟨180923, by rfl⟩ : syracuseStep 964925 = 361847) (by norm_num)
theorem B964997 : Blo 428775 964997 := bbase (se 4 (by rfl) ⟨90468, by rfl⟩ : syracuseStep 964997 = 180937) (by norm_num)
theorem B965069 : Blo 428775 965069 := bbase (se 3 (by rfl) ⟨180950, by rfl⟩ : syracuseStep 965069 = 361901) (by norm_num)
theorem B965141 : Blo 428775 965141 := bbase (se 6 (by rfl) ⟨22620, by rfl⟩ : syracuseStep 965141 = 45241) (by norm_num)
theorem B6404629 : Blo 428775 6404629 := bbase (se 6 (by rfl) ⟨150108, by rfl⟩ : syracuseStep 6404629 = 300217) (by norm_num)
theorem B965213 : Blo 428775 965213 := bbase (se 3 (by rfl) ⟨180977, by rfl⟩ : syracuseStep 965213 = 361955) (by norm_num)
theorem B1456757 : Blo 428775 1456757 := bbase (se 5 (by rfl) ⟨68285, by rfl⟩ : syracuseStep 1456757 = 136571) (by norm_num)
theorem B965285 : Blo 428775 965285 := bbase (se 4 (by rfl) ⟨90495, by rfl⟩ : syracuseStep 965285 = 180991) (by norm_num)
theorem B2177765 : Blo 428775 2177765 := bbase (se 4 (by rfl) ⟨204165, by rfl⟩ : syracuseStep 2177765 = 408331) (by norm_num)
theorem B965357 : Blo 428775 965357 := bbase (se 3 (by rfl) ⟨181004, by rfl⟩ : syracuseStep 965357 = 362009) (by norm_num)
theorem B441137 : Blo 428775 441137 := bbase (se 2 (by rfl) ⟨165426, by rfl⟩ : syracuseStep 441137 = 330853) (by norm_num)
theorem B965429 : Blo 428775 965429 := bbase (se 5 (by rfl) ⟨45254, by rfl⟩ : syracuseStep 965429 = 90509) (by norm_num)
theorem B2079557 : Blo 428775 2079557 := bbase (se 4 (by rfl) ⟨194958, by rfl⟩ : syracuseStep 2079557 = 389917) (by norm_num)
theorem B965501 : Blo 428775 965501 := bbase (se 3 (by rfl) ⟨181031, by rfl⟩ : syracuseStep 965501 = 362063) (by norm_num)
theorem B965573 : Blo 428775 965573 := bbase (se 4 (by rfl) ⟨90522, by rfl⟩ : syracuseStep 965573 = 181045) (by norm_num)
theorem B965645 : Blo 428775 965645 := bbase (se 3 (by rfl) ⟨181058, by rfl⟩ : syracuseStep 965645 = 362117) (by norm_num)
theorem B1457189 : Blo 428775 1457189 := bbase (se 4 (by rfl) ⟨136611, by rfl⟩ : syracuseStep 1457189 = 273223) (by norm_num)
theorem B965717 : Blo 428775 965717 := bbase (se 8 (by rfl) ⟨5658, by rfl⟩ : syracuseStep 965717 = 11317) (by norm_num)
theorem B965789 : Blo 428775 965789 := bbase (se 3 (by rfl) ⟨181085, by rfl⟩ : syracuseStep 965789 = 362171) (by norm_num)
theorem B965861 : Blo 428775 965861 := bbase (se 4 (by rfl) ⟨90549, by rfl⟩ : syracuseStep 965861 = 181099) (by norm_num)
theorem B1752293 : Blo 428775 1752293 := bbase (se 4 (by rfl) ⟨164277, by rfl⟩ : syracuseStep 1752293 = 328555) (by norm_num)
theorem B965933 : Blo 428775 965933 := bbase (se 3 (by rfl) ⟨181112, by rfl⟩ : syracuseStep 965933 = 362225) (by norm_num)
theorem B736589 : Blo 428775 736589 := bbase (se 3 (by rfl) ⟨138110, by rfl⟩ : syracuseStep 736589 = 276221) (by norm_num)
theorem B966005 : Blo 428775 966005 := bbase (se 5 (by rfl) ⟨45281, by rfl⟩ : syracuseStep 966005 = 90563) (by norm_num)
theorem B966077 : Blo 428775 966077 := bbase (se 3 (by rfl) ⟨181139, by rfl⟩ : syracuseStep 966077 = 362279) (by norm_num)
theorem B1228229 : Blo 428775 1228229 := bbase (se 4 (by rfl) ⟨115146, by rfl⟩ : syracuseStep 1228229 = 230293) (by norm_num)
theorem B1031629 : Blo 428775 1031629 := bbase (se 3 (by rfl) ⟨193430, by rfl⟩ : syracuseStep 1031629 = 386861) (by norm_num)
theorem B1457621 : Blo 428775 1457621 := bbase (se 7 (by rfl) ⟨17081, by rfl⟩ : syracuseStep 1457621 = 34163) (by norm_num)
theorem B966149 : Blo 428775 966149 := bbase (se 4 (by rfl) ⟨90576, by rfl⟩ : syracuseStep 966149 = 181153) (by norm_num)
theorem B966221 : Blo 428775 966221 := bbase (se 3 (by rfl) ⟨181166, by rfl⟩ : syracuseStep 966221 = 362333) (by norm_num)
theorem B966293 : Blo 428775 966293 := bbase (se 6 (by rfl) ⟨22647, by rfl⟩ : syracuseStep 966293 = 45295) (by norm_num)
theorem B736949 : Blo 428775 736949 := bbase (se 5 (by rfl) ⟨34544, by rfl⟩ : syracuseStep 736949 = 69089) (by norm_num)
theorem B966365 : Blo 428775 966365 := bbase (se 3 (by rfl) ⟨181193, by rfl⟩ : syracuseStep 966365 = 362387) (by norm_num)
theorem B2801429 : Blo 428775 2801429 := bbase (se 6 (by rfl) ⟨65658, by rfl⟩ : syracuseStep 2801429 = 131317) (by norm_num)
theorem B966437 : Blo 428775 966437 := bbase (se 4 (by rfl) ⟨90603, by rfl⟩ : syracuseStep 966437 = 181207) (by norm_num)
theorem B966509 : Blo 428775 966509 := bbase (se 3 (by rfl) ⟨181220, by rfl⟩ : syracuseStep 966509 = 362441) (by norm_num)
theorem B1458053 : Blo 428775 1458053 := bbase (se 4 (by rfl) ⟨136692, by rfl⟩ : syracuseStep 1458053 = 273385) (by norm_num)
theorem B966581 : Blo 428775 966581 := bbase (se 5 (by rfl) ⟨45308, by rfl⟩ : syracuseStep 966581 = 90617) (by norm_num)
theorem B2179061 : Blo 428775 2179061 := bbase (se 5 (by rfl) ⟨102143, by rfl⟩ : syracuseStep 2179061 = 204287) (by norm_num)
theorem B966653 : Blo 428775 966653 := bbase (se 3 (by rfl) ⟨181247, by rfl⟩ : syracuseStep 966653 = 362495) (by norm_num)
theorem B1032205 : Blo 428775 1032205 := bbase (se 3 (by rfl) ⟨193538, by rfl⟩ : syracuseStep 1032205 = 387077) (by norm_num)
theorem B966725 : Blo 428775 966725 := bbase (se 4 (by rfl) ⟨90630, by rfl⟩ : syracuseStep 966725 = 181261) (by norm_num)
theorem B966797 : Blo 428775 966797 := bbase (se 3 (by rfl) ⟨181274, by rfl⟩ : syracuseStep 966797 = 362549) (by norm_num)
theorem B966869 : Blo 428775 966869 := bbase (se 7 (by rfl) ⟨11330, by rfl⟩ : syracuseStep 966869 = 22661) (by norm_num)
theorem B966941 : Blo 428775 966941 := bbase (se 3 (by rfl) ⟨181301, by rfl⟩ : syracuseStep 966941 = 362603) (by norm_num)
theorem B1458485 : Blo 428775 1458485 := bbase (se 5 (by rfl) ⟨68366, by rfl⟩ : syracuseStep 1458485 = 136733) (by norm_num)
theorem B1032533 : Blo 428775 1032533 := bbase (se 10 (by rfl) ⟨1512, by rfl⟩ : syracuseStep 1032533 = 3025) (by norm_num)
theorem B967013 : Blo 428775 967013 := bbase (se 4 (by rfl) ⟨90657, by rfl⟩ : syracuseStep 967013 = 181315) (by norm_num)
theorem B1032589 : Blo 428775 1032589 := bbase (se 3 (by rfl) ⟨193610, by rfl⟩ : syracuseStep 1032589 = 387221) (by norm_num)
theorem B967085 : Blo 428775 967085 := bbase (se 3 (by rfl) ⟨181328, by rfl⟩ : syracuseStep 967085 = 362657) (by norm_num)
theorem B967157 : Blo 428775 967157 := bbase (se 5 (by rfl) ⟨45335, by rfl⟩ : syracuseStep 967157 = 90671) (by norm_num)
theorem B2769461 : Blo 428775 2769461 := bbase (se 5 (by rfl) ⟨129818, by rfl⟩ : syracuseStep 2769461 = 259637) (by norm_num)
theorem B967229 : Blo 428775 967229 := bbase (se 3 (by rfl) ⟨181355, by rfl⟩ : syracuseStep 967229 = 362711) (by norm_num)
theorem B1229413 : Blo 428775 1229413 := bbase (se 4 (by rfl) ⟨115257, by rfl⟩ : syracuseStep 1229413 = 230515) (by norm_num)
theorem B1032821 : Blo 428775 1032821 := bbase (se 5 (by rfl) ⟨48413, by rfl⟩ : syracuseStep 1032821 = 96827) (by norm_num)
theorem B967301 : Blo 428775 967301 := bbase (se 4 (by rfl) ⟨90684, by rfl⟩ : syracuseStep 967301 = 181369) (by norm_num)
theorem B967373 : Blo 428775 967373 := bbase (se 3 (by rfl) ⟨181382, by rfl⟩ : syracuseStep 967373 = 362765) (by norm_num)
theorem B1458917 : Blo 428775 1458917 := bbase (se 4 (by rfl) ⟨136773, by rfl⟩ : syracuseStep 1458917 = 273547) (by norm_num)
theorem B1229573 : Blo 428775 1229573 := bbase (se 4 (by rfl) ⟨115272, by rfl⟩ : syracuseStep 1229573 = 230545) (by norm_num)
theorem B967445 : Blo 428775 967445 := bbase (se 6 (by rfl) ⟨22674, by rfl⟩ : syracuseStep 967445 = 45349) (by norm_num)
theorem B1033013 : Blo 428775 1033013 := bbase (se 5 (by rfl) ⟨48422, by rfl⟩ : syracuseStep 1033013 = 96845) (by norm_num)
theorem B4146005 : Blo 428775 4146005 := bbase (se 9 (by rfl) ⟨12146, by rfl⟩ : syracuseStep 4146005 = 24293) (by norm_num)
theorem B967517 : Blo 428775 967517 := bbase (se 3 (by rfl) ⟨181409, by rfl⟩ : syracuseStep 967517 = 362819) (by norm_num)
theorem B967589 : Blo 428775 967589 := bbase (se 4 (by rfl) ⟨90711, by rfl⟩ : syracuseStep 967589 = 181423) (by norm_num)
theorem B967661 : Blo 428775 967661 := bbase (se 3 (by rfl) ⟨181436, by rfl⟩ : syracuseStep 967661 = 362873) (by norm_num)
theorem B1229813 : Blo 428775 1229813 := bbase (se 5 (by rfl) ⟨57647, by rfl⟩ : syracuseStep 1229813 = 115295) (by norm_num)
theorem B967733 : Blo 428775 967733 := bbase (se 5 (by rfl) ⟨45362, by rfl⟩ : syracuseStep 967733 = 90725) (by norm_num)
theorem B967805 : Blo 428775 967805 := bbase (se 3 (by rfl) ⟨181463, by rfl⟩ : syracuseStep 967805 = 362927) (by norm_num)
theorem B1459349 : Blo 428775 1459349 := bbase (se 6 (by rfl) ⟨34203, by rfl⟩ : syracuseStep 1459349 = 68407) (by norm_num)
theorem B1230005 : Blo 428775 1230005 := bbase (se 5 (by rfl) ⟨57656, by rfl⟩ : syracuseStep 1230005 = 115313) (by norm_num)
theorem B967877 : Blo 428775 967877 := bbase (se 4 (by rfl) ⟨90738, by rfl⟩ : syracuseStep 967877 = 181477) (by norm_num)
theorem B2180357 : Blo 428775 2180357 := bbase (se 4 (by rfl) ⟨204408, by rfl⟩ : syracuseStep 2180357 = 408817) (by norm_num)
theorem B967949 : Blo 428775 967949 := bbase (se 3 (by rfl) ⟨181490, by rfl⟩ : syracuseStep 967949 = 362981) (by norm_num)
theorem B968021 : Blo 428775 968021 := bbase (se 12 (by rfl) ⟨354, by rfl⟩ : syracuseStep 968021 = 709) (by norm_num)
theorem B968093 : Blo 428775 968093 := bbase (se 3 (by rfl) ⟨181517, by rfl⟩ : syracuseStep 968093 = 363035) (by norm_num)
theorem B1394117 : Blo 428775 1394117 := bbase (se 4 (by rfl) ⟨130698, by rfl⟩ : syracuseStep 1394117 = 261397) (by norm_num)
theorem B968165 : Blo 428775 968165 := bbase (se 4 (by rfl) ⟨90765, by rfl⟩ : syracuseStep 968165 = 181531) (by norm_num)
theorem B968237 : Blo 428775 968237 := bbase (se 3 (by rfl) ⟨181544, by rfl⟩ : syracuseStep 968237 = 363089) (by norm_num)
theorem B1459781 : Blo 428775 1459781 := bbase (se 4 (by rfl) ⟨136854, by rfl⟩ : syracuseStep 1459781 = 273709) (by norm_num)
theorem B968309 : Blo 428775 968309 := bbase (se 5 (by rfl) ⟨45389, by rfl⟩ : syracuseStep 968309 = 90779) (by norm_num)
theorem B968381 : Blo 428775 968381 := bbase (se 3 (by rfl) ⟨181571, by rfl⟩ : syracuseStep 968381 = 363143) (by norm_num)
theorem B1033973 : Blo 428775 1033973 := bbase (se 5 (by rfl) ⟨48467, by rfl⟩ : syracuseStep 1033973 = 96935) (by norm_num)
theorem B968453 : Blo 428775 968453 := bbase (se 4 (by rfl) ⟨90792, by rfl⟩ : syracuseStep 968453 = 181585) (by norm_num)
theorem B2443061 : Blo 428775 2443061 := bbase (se 5 (by rfl) ⟨114518, by rfl⟩ : syracuseStep 2443061 = 229037) (by norm_num)
theorem B968525 : Blo 428775 968525 := bbase (se 3 (by rfl) ⟨181598, by rfl⟩ : syracuseStep 968525 = 363197) (by norm_num)
theorem B968597 : Blo 428775 968597 := bbase (se 6 (by rfl) ⟨22701, by rfl⟩ : syracuseStep 968597 = 45403) (by norm_num)
theorem B739277 : Blo 428775 739277 := bbase (se 3 (by rfl) ⟨138614, by rfl⟩ : syracuseStep 739277 = 277229) (by norm_num)
theorem B968669 : Blo 428775 968669 := bbase (se 3 (by rfl) ⟨181625, by rfl⟩ : syracuseStep 968669 = 363251) (by norm_num)
theorem B1460213 : Blo 428775 1460213 := bbase (se 5 (by rfl) ⟨68447, by rfl⟩ : syracuseStep 1460213 = 136895) (by norm_num)
theorem B968741 : Blo 428775 968741 := bbase (se 4 (by rfl) ⟨90819, by rfl⟩ : syracuseStep 968741 = 181639) (by norm_num)
theorem B804917 : Blo 428775 804917 := bbase (se 5 (by rfl) ⟨37730, by rfl⟩ : syracuseStep 804917 = 75461) (by norm_num)
theorem B3262517 : Blo 428775 3262517 := bbase (se 5 (by rfl) ⟨152930, by rfl⟩ : syracuseStep 3262517 = 305861) (by norm_num)
theorem B542801 : Blo 428775 542801 := bbase (se 2 (by rfl) ⟨203550, by rfl⟩ : syracuseStep 542801 = 407101) (by norm_num)
theorem B936029 : Blo 428775 936029 := bbase (se 3 (by rfl) ⟨175505, by rfl⟩ : syracuseStep 936029 = 351011) (by norm_num)
theorem B968813 : Blo 428775 968813 := bbase (se 3 (by rfl) ⟨181652, by rfl⟩ : syracuseStep 968813 = 363305) (by norm_num)
theorem B542857 : Blo 428775 542857 := bbase (se 2 (by rfl) ⟨203571, by rfl⟩ : syracuseStep 542857 = 407143) (by norm_num)
theorem B4638869 : Blo 428775 4638869 := bbase (se 6 (by rfl) ⟨108723, by rfl⟩ : syracuseStep 4638869 = 217447) (by norm_num)
theorem B1230997 : Blo 428775 1230997 := bbase (se 6 (by rfl) ⟨28851, by rfl⟩ : syracuseStep 1230997 = 57703) (by norm_num)
theorem B968885 : Blo 428775 968885 := bbase (se 5 (by rfl) ⟨45416, by rfl⟩ : syracuseStep 968885 = 90833) (by norm_num)
theorem B542953 : Blo 428775 542953 := bbase (se 2 (by rfl) ⟨203607, by rfl⟩ : syracuseStep 542953 = 407215) (by norm_num)
theorem B968957 : Blo 428775 968957 := bbase (se 3 (by rfl) ⟨181679, by rfl⟩ : syracuseStep 968957 = 363359) (by norm_num)
theorem B969029 : Blo 428775 969029 := bbase (se 4 (by rfl) ⟨90846, by rfl⟩ : syracuseStep 969029 = 181693) (by norm_num)
theorem B969101 : Blo 428775 969101 := bbase (se 3 (by rfl) ⟨181706, by rfl⟩ : syracuseStep 969101 = 363413) (by norm_num)
theorem B543125 : Blo 428775 543125 := bbase (se 6 (by rfl) ⟨12729, by rfl⟩ : syracuseStep 543125 = 25459) (by norm_num)
theorem B543181 : Blo 428775 543181 := bbase (se 3 (by rfl) ⟨101846, by rfl⟩ : syracuseStep 543181 = 203693) (by norm_num)
theorem B969173 : Blo 428775 969173 := bbase (se 7 (by rfl) ⟨11357, by rfl⟩ : syracuseStep 969173 = 22715) (by norm_num)
theorem B707069 : Blo 428775 707069 := bbase (se 3 (by rfl) ⟨132575, by rfl⟩ : syracuseStep 707069 = 265151) (by norm_num)
theorem B2181653 : Blo 428775 2181653 := bbase (se 6 (by rfl) ⟨51132, by rfl⟩ : syracuseStep 2181653 = 102265) (by norm_num)
theorem B969245 : Blo 428775 969245 := bbase (se 3 (by rfl) ⟨181733, by rfl⟩ : syracuseStep 969245 = 363467) (by norm_num)
theorem B543277 : Blo 428775 543277 := bbase (se 3 (by rfl) ⟨101864, by rfl⟩ : syracuseStep 543277 = 203729) (by norm_num)
theorem B772669 : Blo 428775 772669 := bbase (se 3 (by rfl) ⟨144875, by rfl⟩ : syracuseStep 772669 = 289751) (by norm_num)
theorem B11061845 : Blo 428775 11061845 := bbase (se 8 (by rfl) ⟨64815, by rfl⟩ : syracuseStep 11061845 = 129631) (by norm_num)
theorem B969317 : Blo 428775 969317 := bbase (se 4 (by rfl) ⟨90873, by rfl⟩ : syracuseStep 969317 = 181747) (by norm_num)
theorem B969389 : Blo 428775 969389 := bbase (se 3 (by rfl) ⟨181760, by rfl⟩ : syracuseStep 969389 = 363521) (by norm_num)
theorem B1100477 : Blo 428775 1100477 := bbase (se 3 (by rfl) ⟨206339, by rfl⟩ : syracuseStep 1100477 = 412679) (by norm_num)
theorem B871117 : Blo 428775 871117 := bbase (se 3 (by rfl) ⟨163334, by rfl⟩ : syracuseStep 871117 = 326669) (by norm_num)
theorem B543449 : Blo 428775 543449 := bbase (se 2 (by rfl) ⟨203793, by rfl⟩ : syracuseStep 543449 = 407587) (by norm_num)
theorem B969461 : Blo 428775 969461 := bbase (se 5 (by rfl) ⟨45443, by rfl⟩ : syracuseStep 969461 = 90887) (by norm_num)
theorem B543505 : Blo 428775 543505 := bbase (se 2 (by rfl) ⟨203814, by rfl⟩ : syracuseStep 543505 = 407629) (by norm_num)
theorem B740125 : Blo 428775 740125 := bbase (se 3 (by rfl) ⟨138773, by rfl⟩ : syracuseStep 740125 = 277547) (by norm_num)
theorem B969533 : Blo 428775 969533 := bbase (se 3 (by rfl) ⟨181787, by rfl⟩ : syracuseStep 969533 = 363575) (by norm_num)
theorem B543601 : Blo 428775 543601 := bbase (se 2 (by rfl) ⟨203850, by rfl⟩ : syracuseStep 543601 = 407701) (by norm_num)
theorem B3689333 : Blo 428775 3689333 := bbase (se 5 (by rfl) ⟨172937, by rfl⟩ : syracuseStep 3689333 = 345875) (by norm_num)
theorem B969605 : Blo 428775 969605 := bbase (se 4 (by rfl) ⟨90900, by rfl⟩ : syracuseStep 969605 = 181801) (by norm_num)
theorem B969677 : Blo 428775 969677 := bbase (se 3 (by rfl) ⟨181814, by rfl⟩ : syracuseStep 969677 = 363629) (by norm_num)
theorem B4410325 : Blo 428775 4410325 := bbase (se 7 (by rfl) ⟨51683, by rfl⟩ : syracuseStep 4410325 = 103367) (by norm_num)
theorem B1657813 : Blo 428775 1657813 := bbase (se 7 (by rfl) ⟨19427, by rfl⟩ : syracuseStep 1657813 = 38855) (by norm_num)
theorem B969749 : Blo 428775 969749 := bbase (se 6 (by rfl) ⟨22728, by rfl⟩ : syracuseStep 969749 = 45457) (by norm_num)
theorem B543773 : Blo 428775 543773 := bbase (se 3 (by rfl) ⟨101957, by rfl⟩ : syracuseStep 543773 = 203915) (by norm_num)
theorem B543829 : Blo 428775 543829 := bbase (se 8 (by rfl) ⟨3186, by rfl⟩ : syracuseStep 543829 = 6373) (by norm_num)
theorem B969821 : Blo 428775 969821 := bbase (se 3 (by rfl) ⟨181841, by rfl⟩ : syracuseStep 969821 = 363683) (by norm_num)
theorem B871565 : Blo 428775 871565 := bbase (se 3 (by rfl) ⟨163418, by rfl⟩ : syracuseStep 871565 = 326837) (by norm_num)
theorem B969893 : Blo 428775 969893 := bbase (se 4 (by rfl) ⟨90927, by rfl⟩ : syracuseStep 969893 = 181855) (by norm_num)
theorem B543925 : Blo 428775 543925 := bbase (se 5 (by rfl) ⟨25496, by rfl⟩ : syracuseStep 543925 = 50993) (by norm_num)
theorem B1232101 : Blo 428775 1232101 := bbase (se 4 (by rfl) ⟨115509, by rfl⟩ : syracuseStep 1232101 = 231019) (by norm_num)
theorem B969965 : Blo 428775 969965 := bbase (se 3 (by rfl) ⟨181868, by rfl⟩ : syracuseStep 969965 = 363737) (by norm_num)
theorem B970037 : Blo 428775 970037 := bbase (se 5 (by rfl) ⟨45470, by rfl⟩ : syracuseStep 970037 = 90941) (by norm_num)
theorem B544097 : Blo 428775 544097 := bbase (se 2 (by rfl) ⟨204036, by rfl⟩ : syracuseStep 544097 = 408073) (by norm_num)
theorem B773477 : Blo 428775 773477 := bbase (se 4 (by rfl) ⟨72513, by rfl⟩ : syracuseStep 773477 = 145027) (by norm_num)
theorem B970109 : Blo 428775 970109 := bbase (se 3 (by rfl) ⟨181895, by rfl⟩ : syracuseStep 970109 = 363791) (by norm_num)
theorem B544153 : Blo 428775 544153 := bbase (se 2 (by rfl) ⟨204057, by rfl⟩ : syracuseStep 544153 = 408115) (by norm_num)
theorem B970181 : Blo 428775 970181 := bbase (se 4 (by rfl) ⟨90954, by rfl⟩ : syracuseStep 970181 = 181909) (by norm_num)
theorem B1101269 : Blo 428775 1101269 := bbase (se 7 (by rfl) ⟨12905, by rfl⟩ : syracuseStep 1101269 = 25811) (by norm_num)
theorem B544249 : Blo 428775 544249 := bbase (se 2 (by rfl) ⟨204093, by rfl⟩ : syracuseStep 544249 = 408187) (by norm_num)
theorem B970253 : Blo 428775 970253 := bbase (se 3 (by rfl) ⟨181922, by rfl⟩ : syracuseStep 970253 = 363845) (by norm_num)
theorem B970325 : Blo 428775 970325 := bbase (se 8 (by rfl) ⟨5685, by rfl⟩ : syracuseStep 970325 = 11371) (by norm_num)
theorem B970397 : Blo 428775 970397 := bbase (se 3 (by rfl) ⟨181949, by rfl⟩ : syracuseStep 970397 = 363899) (by norm_num)
theorem B544421 : Blo 428775 544421 := bbase (se 4 (by rfl) ⟨51039, by rfl⟩ : syracuseStep 544421 = 102079) (by norm_num)
theorem B544477 : Blo 428775 544477 := bbase (se 3 (by rfl) ⟨102089, by rfl⟩ : syracuseStep 544477 = 204179) (by norm_num)
theorem B970469 : Blo 428775 970469 := bbase (se 4 (by rfl) ⟨90981, by rfl⟩ : syracuseStep 970469 = 181963) (by norm_num)
theorem B2182949 : Blo 428775 2182949 := bbase (se 4 (by rfl) ⟨204651, by rfl⟩ : syracuseStep 2182949 = 409303) (by norm_num)
theorem B970541 : Blo 428775 970541 := bbase (se 3 (by rfl) ⟨181976, by rfl⟩ : syracuseStep 970541 = 363953) (by norm_num)
theorem B544573 : Blo 428775 544573 := bbase (se 3 (by rfl) ⟨102107, by rfl⟩ : syracuseStep 544573 = 204215) (by norm_num)
theorem B970613 : Blo 428775 970613 := bbase (se 5 (by rfl) ⟨45497, by rfl⟩ : syracuseStep 970613 = 90995) (by norm_num)
theorem B970685 : Blo 428775 970685 := bbase (se 3 (by rfl) ⟨182003, by rfl⟩ : syracuseStep 970685 = 364007) (by norm_num)
theorem B544745 : Blo 428775 544745 := bbase (se 2 (by rfl) ⟨204279, by rfl⟩ : syracuseStep 544745 = 408559) (by norm_num)
theorem B970757 : Blo 428775 970757 := bbase (se 4 (by rfl) ⟨91008, by rfl⟩ : syracuseStep 970757 = 182017) (by norm_num)
theorem B544801 : Blo 428775 544801 := bbase (se 2 (by rfl) ⟨204300, by rfl⟩ : syracuseStep 544801 = 408601) (by norm_num)
theorem B970829 : Blo 428775 970829 := bbase (se 3 (by rfl) ⟨182030, by rfl⟩ : syracuseStep 970829 = 364061) (by norm_num)
theorem B643181 : Blo 428775 643181 := bbase (se 3 (by rfl) ⟨120596, by rfl⟩ : syracuseStep 643181 = 241193) (by norm_num)
theorem B544897 : Blo 428775 544897 := bbase (se 2 (by rfl) ⟨204336, by rfl⟩ : syracuseStep 544897 = 408673) (by norm_num)
theorem B643205 : Blo 428775 643205 := bbase (se 4 (by rfl) ⟨60300, by rfl⟩ : syracuseStep 643205 = 120601) (by norm_num)
theorem B970901 : Blo 428775 970901 := bbase (se 6 (by rfl) ⟨22755, by rfl⟩ : syracuseStep 970901 = 45511) (by norm_num)
theorem B643229 : Blo 428775 643229 := bbase (se 3 (by rfl) ⟨120605, by rfl⟩ : syracuseStep 643229 = 241211) (by norm_num)
theorem B643253 : Blo 428775 643253 := bbase (se 5 (by rfl) ⟨30152, by rfl⟩ : syracuseStep 643253 = 60305) (by norm_num)
theorem B643277 : Blo 428775 643277 := bbase (se 3 (by rfl) ⟨120614, by rfl⟩ : syracuseStep 643277 = 241229) (by norm_num)
theorem B970973 : Blo 428775 970973 := bbase (se 3 (by rfl) ⟨182057, by rfl⟩ : syracuseStep 970973 = 364115) (by norm_num)
theorem B643301 : Blo 428775 643301 := bbase (se 4 (by rfl) ⟨60309, by rfl⟩ : syracuseStep 643301 = 120619) (by norm_num)
theorem B1102061 : Blo 428775 1102061 := bbase (se 3 (by rfl) ⟨206636, by rfl⟩ : syracuseStep 1102061 = 413273) (by norm_num)
theorem B643325 : Blo 428775 643325 := bbase (se 3 (by rfl) ⟨120623, by rfl⟩ : syracuseStep 643325 = 241247) (by norm_num)
theorem B643349 : Blo 428775 643349 := bbase (se 6 (by rfl) ⟨15078, by rfl⟩ : syracuseStep 643349 = 30157) (by norm_num)
theorem B971045 : Blo 428775 971045 := bbase (se 4 (by rfl) ⟨91035, by rfl⟩ : syracuseStep 971045 = 182071) (by norm_num)
theorem B1167653 : Blo 428775 1167653 := bbase (se 4 (by rfl) ⟨109467, by rfl⟩ : syracuseStep 1167653 = 218935) (by norm_num)
theorem B643373 : Blo 428775 643373 := bbase (se 3 (by rfl) ⟨120632, by rfl⟩ : syracuseStep 643373 = 241265) (by norm_num)
theorem B545069 : Blo 428775 545069 := bbase (se 3 (by rfl) ⟨102200, by rfl⟩ : syracuseStep 545069 = 204401) (by norm_num)
theorem B643397 : Blo 428775 643397 := bbase (se 4 (by rfl) ⟨60318, by rfl⟩ : syracuseStep 643397 = 120637) (by norm_num)
theorem B4903253 : Blo 428775 4903253 := bbase (se 10 (by rfl) ⟨7182, by rfl⟩ : syracuseStep 4903253 = 14365) (by norm_num)
theorem B643421 : Blo 428775 643421 := bbase (se 3 (by rfl) ⟨120641, by rfl⟩ : syracuseStep 643421 = 241283) (by norm_num)
theorem B545125 : Blo 428775 545125 := bbase (se 4 (by rfl) ⟨51105, by rfl⟩ : syracuseStep 545125 = 102211) (by norm_num)
theorem B610669 : Blo 428775 610669 := bbase (se 3 (by rfl) ⟨114500, by rfl⟩ : syracuseStep 610669 = 229001) (by norm_num)
theorem B971117 : Blo 428775 971117 := bbase (se 3 (by rfl) ⟨182084, by rfl⟩ : syracuseStep 971117 = 364169) (by norm_num)
theorem B643445 : Blo 428775 643445 := bbase (se 5 (by rfl) ⟨30161, by rfl⟩ : syracuseStep 643445 = 60323) (by norm_num)
theorem B643469 : Blo 428775 643469 := bbase (se 3 (by rfl) ⟨120650, by rfl⟩ : syracuseStep 643469 = 241301) (by norm_num)
theorem B643493 : Blo 428775 643493 := bbase (se 4 (by rfl) ⟨60327, by rfl⟩ : syracuseStep 643493 = 120655) (by norm_num)
theorem B971189 : Blo 428775 971189 := bbase (se 5 (by rfl) ⟨45524, by rfl⟩ : syracuseStep 971189 = 91049) (by norm_num)
theorem B643517 : Blo 428775 643517 := bbase (se 3 (by rfl) ⟨120659, by rfl⟩ : syracuseStep 643517 = 241319) (by norm_num)
theorem B545221 : Blo 428775 545221 := bbase (se 4 (by rfl) ⟨51114, by rfl⟩ : syracuseStep 545221 = 102229) (by norm_num)
theorem B1036741 : Blo 428775 1036741 := bbase (se 4 (by rfl) ⟨97194, by rfl⟩ : syracuseStep 1036741 = 194389) (by norm_num)
theorem B643541 : Blo 428775 643541 := bbase (se 7 (by rfl) ⟨7541, by rfl⟩ : syracuseStep 643541 = 15083) (by norm_num)
theorem B643565 : Blo 428775 643565 := bbase (se 3 (by rfl) ⟨120668, by rfl⟩ : syracuseStep 643565 = 241337) (by norm_num)
theorem B971261 : Blo 428775 971261 := bbase (se 3 (by rfl) ⟨182111, by rfl⟩ : syracuseStep 971261 = 364223) (by norm_num)
theorem B643589 : Blo 428775 643589 := bbase (se 4 (by rfl) ⟨60336, by rfl⟩ : syracuseStep 643589 = 120673) (by norm_num)
theorem B643613 : Blo 428775 643613 := bbase (se 3 (by rfl) ⟨120677, by rfl⟩ : syracuseStep 643613 = 241355) (by norm_num)
theorem B643637 : Blo 428775 643637 := bbase (se 5 (by rfl) ⟨30170, by rfl⟩ : syracuseStep 643637 = 60341) (by norm_num)
theorem B971333 : Blo 428775 971333 := bbase (se 4 (by rfl) ⟨91062, by rfl⟩ : syracuseStep 971333 = 182125) (by norm_num)
theorem B643661 : Blo 428775 643661 := bbase (se 3 (by rfl) ⟨120686, by rfl⟩ : syracuseStep 643661 = 241373) (by norm_num)
theorem B643685 : Blo 428775 643685 := bbase (se 4 (by rfl) ⟨60345, by rfl⟩ : syracuseStep 643685 = 120691) (by norm_num)
theorem B545393 : Blo 428775 545393 := bbase (se 2 (by rfl) ⟨204522, by rfl⟩ : syracuseStep 545393 = 409045) (by norm_num)
theorem B643709 : Blo 428775 643709 := bbase (se 3 (by rfl) ⟨120695, by rfl⟩ : syracuseStep 643709 = 241391) (by norm_num)
theorem B971405 : Blo 428775 971405 := bbase (se 3 (by rfl) ⟨182138, by rfl⟩ : syracuseStep 971405 = 364277) (by norm_num)
theorem B643733 : Blo 428775 643733 := bbase (se 6 (by rfl) ⟨15087, by rfl⟩ : syracuseStep 643733 = 30175) (by norm_num)
theorem B545449 : Blo 428775 545449 := bbase (se 2 (by rfl) ⟨204543, by rfl⟩ : syracuseStep 545449 = 409087) (by norm_num)
theorem B643757 : Blo 428775 643757 := bbase (se 3 (by rfl) ⟨120704, by rfl⟩ : syracuseStep 643757 = 241409) (by norm_num)
theorem B611005 : Blo 428775 611005 := bbase (se 3 (by rfl) ⟨114563, by rfl⟩ : syracuseStep 611005 = 229127) (by norm_num)
theorem B643781 : Blo 428775 643781 := bbase (se 4 (by rfl) ⟨60354, by rfl⟩ : syracuseStep 643781 = 120709) (by norm_num)
theorem B971477 : Blo 428775 971477 := bbase (se 7 (by rfl) ⟨11384, by rfl⟩ : syracuseStep 971477 = 22769) (by norm_num)
theorem B643805 : Blo 428775 643805 := bbase (se 3 (by rfl) ⟨120713, by rfl⟩ : syracuseStep 643805 = 241427) (by norm_num)
theorem B643829 : Blo 428775 643829 := bbase (se 5 (by rfl) ⟨30179, by rfl⟩ : syracuseStep 643829 = 60359) (by norm_num)
theorem B2249461 : Blo 428775 2249461 := bbase (se 5 (by rfl) ⟨105443, by rfl⟩ : syracuseStep 2249461 = 210887) (by norm_num)
theorem B545545 : Blo 428775 545545 := bbase (se 2 (by rfl) ⟨204579, by rfl⟩ : syracuseStep 545545 = 409159) (by norm_num)
theorem B643853 : Blo 428775 643853 := bbase (se 3 (by rfl) ⟨120722, by rfl⟩ : syracuseStep 643853 = 241445) (by norm_num)
theorem B971549 : Blo 428775 971549 := bbase (se 3 (by rfl) ⟨182165, by rfl⟩ : syracuseStep 971549 = 364331) (by norm_num)
theorem B643877 : Blo 428775 643877 := bbase (se 4 (by rfl) ⟨60363, by rfl⟩ : syracuseStep 643877 = 120727) (by norm_num)
theorem B643901 : Blo 428775 643901 := bbase (se 3 (by rfl) ⟨120731, by rfl⟩ : syracuseStep 643901 = 241463) (by norm_num)
theorem B1037117 : Blo 428775 1037117 := bbase (se 3 (by rfl) ⟨194459, by rfl⟩ : syracuseStep 1037117 = 388919) (by norm_num)
theorem B643925 : Blo 428775 643925 := bbase (se 9 (by rfl) ⟨1886, by rfl⟩ : syracuseStep 643925 = 3773) (by norm_num)
theorem B971621 : Blo 428775 971621 := bbase (se 4 (by rfl) ⟨91089, by rfl⟩ : syracuseStep 971621 = 182179) (by norm_num)
theorem B643949 : Blo 428775 643949 := bbase (se 3 (by rfl) ⟨120740, by rfl⟩ : syracuseStep 643949 = 241481) (by norm_num)
theorem B643973 : Blo 428775 643973 := bbase (se 4 (by rfl) ⟨60372, by rfl⟩ : syracuseStep 643973 = 120745) (by norm_num)
theorem B611221 : Blo 428775 611221 := bbase (se 6 (by rfl) ⟨14325, by rfl⟩ : syracuseStep 611221 = 28651) (by norm_num)
theorem B643997 : Blo 428775 643997 := bbase (se 3 (by rfl) ⟨120749, by rfl⟩ : syracuseStep 643997 = 241499) (by norm_num)
theorem B971693 : Blo 428775 971693 := bbase (se 3 (by rfl) ⟨182192, by rfl⟩ : syracuseStep 971693 = 364385) (by norm_num)
theorem B644021 : Blo 428775 644021 := bbase (se 5 (by rfl) ⟨30188, by rfl⟩ : syracuseStep 644021 = 60377) (by norm_num)
theorem B545717 : Blo 428775 545717 := bbase (se 5 (by rfl) ⟨25580, by rfl⟩ : syracuseStep 545717 = 51161) (by norm_num)
theorem B644045 : Blo 428775 644045 := bbase (se 3 (by rfl) ⟨120758, by rfl⟩ : syracuseStep 644045 = 241517) (by norm_num)
theorem B644069 : Blo 428775 644069 := bbase (se 4 (by rfl) ⟨60381, by rfl⟩ : syracuseStep 644069 = 120763) (by norm_num)
theorem B545773 : Blo 428775 545773 := bbase (se 3 (by rfl) ⟨102332, by rfl⟩ : syracuseStep 545773 = 204665) (by norm_num)
theorem B1102837 : Blo 428775 1102837 := bbase (se 5 (by rfl) ⟨51695, by rfl⟩ : syracuseStep 1102837 = 103391) (by norm_num)
theorem B971765 : Blo 428775 971765 := bbase (se 5 (by rfl) ⟨45551, by rfl⟩ : syracuseStep 971765 = 91103) (by norm_num)
theorem B644093 : Blo 428775 644093 := bbase (se 3 (by rfl) ⟨120767, by rfl⟩ : syracuseStep 644093 = 241535) (by norm_num)
theorem B644117 : Blo 428775 644117 := bbase (se 6 (by rfl) ⟨15096, by rfl⟩ : syracuseStep 644117 = 30193) (by norm_num)
theorem B644141 : Blo 428775 644141 := bbase (se 3 (by rfl) ⟨120776, by rfl⟩ : syracuseStep 644141 = 241553) (by norm_num)
theorem B2184245 : Blo 428775 2184245 := bbase (se 5 (by rfl) ⟨102386, by rfl⟩ : syracuseStep 2184245 = 204773) (by norm_num)
theorem B971837 : Blo 428775 971837 := bbase (se 3 (by rfl) ⟨182219, by rfl⟩ : syracuseStep 971837 = 364439) (by norm_num)
theorem B644165 : Blo 428775 644165 := bbase (se 4 (by rfl) ⟨60390, by rfl⟩ : syracuseStep 644165 = 120781) (by norm_num)
theorem B545869 : Blo 428775 545869 := bbase (se 3 (by rfl) ⟨102350, by rfl⟩ : syracuseStep 545869 = 204701) (by norm_num)
theorem B644189 : Blo 428775 644189 := bbase (se 3 (by rfl) ⟨120785, by rfl⟩ : syracuseStep 644189 = 241571) (by norm_num)
theorem B644213 : Blo 428775 644213 := bbase (se 5 (by rfl) ⟨30197, by rfl⟩ : syracuseStep 644213 = 60395) (by norm_num)
theorem B971909 : Blo 428775 971909 := bbase (se 4 (by rfl) ⟨91116, by rfl⟩ : syracuseStep 971909 = 182233) (by norm_num)
theorem B644237 : Blo 428775 644237 := bbase (se 3 (by rfl) ⟨120794, by rfl⟩ : syracuseStep 644237 = 241589) (by norm_num)
theorem B644261 : Blo 428775 644261 := bbase (se 4 (by rfl) ⟨60399, by rfl⟩ : syracuseStep 644261 = 120799) (by norm_num)
theorem B644285 : Blo 428775 644285 := bbase (se 3 (by rfl) ⟨120803, by rfl⟩ : syracuseStep 644285 = 241607) (by norm_num)
theorem B971981 : Blo 428775 971981 := bbase (se 3 (by rfl) ⟨182246, by rfl⟩ : syracuseStep 971981 = 364493) (by norm_num)
theorem B644309 : Blo 428775 644309 := bbase (se 7 (by rfl) ⟨7550, by rfl⟩ : syracuseStep 644309 = 15101) (by norm_num)
theorem B644333 : Blo 428775 644333 := bbase (se 3 (by rfl) ⟨120812, by rfl⟩ : syracuseStep 644333 = 241625) (by norm_num)
theorem B1037549 : Blo 428775 1037549 := bbase (se 3 (by rfl) ⟨194540, by rfl⟩ : syracuseStep 1037549 = 389081) (by norm_num)
theorem B546041 : Blo 428775 546041 := bbase (se 2 (by rfl) ⟨204765, by rfl⟩ : syracuseStep 546041 = 409531) (by norm_num)
theorem B644357 : Blo 428775 644357 := bbase (se 4 (by rfl) ⟨60408, by rfl⟩ : syracuseStep 644357 = 120817) (by norm_num)
theorem B611597 : Blo 428775 611597 := bbase (se 3 (by rfl) ⟨114674, by rfl⟩ : syracuseStep 611597 = 229349) (by norm_num)
theorem B972053 : Blo 428775 972053 := bbase (se 6 (by rfl) ⟨22782, by rfl⟩ : syracuseStep 972053 = 45565) (by norm_num)
theorem B644381 : Blo 428775 644381 := bbase (se 3 (by rfl) ⟨120821, by rfl⟩ : syracuseStep 644381 = 241643) (by norm_num)
theorem B546097 : Blo 428775 546097 := bbase (se 2 (by rfl) ⟨204786, by rfl⟩ : syracuseStep 546097 = 409573) (by norm_num)
theorem B644405 : Blo 428775 644405 := bbase (se 5 (by rfl) ⟨30206, by rfl⟩ : syracuseStep 644405 = 60413) (by norm_num)
theorem B644429 : Blo 428775 644429 := bbase (se 3 (by rfl) ⟨120830, by rfl⟩ : syracuseStep 644429 = 241661) (by norm_num)
theorem B972125 : Blo 428775 972125 := bbase (se 3 (by rfl) ⟨182273, by rfl⟩ : syracuseStep 972125 = 364547) (by norm_num)
theorem B644453 : Blo 428775 644453 := bbase (se 4 (by rfl) ⟨60417, by rfl⟩ : syracuseStep 644453 = 120835) (by norm_num)
theorem B644477 : Blo 428775 644477 := bbase (se 3 (by rfl) ⟨120839, by rfl⟩ : syracuseStep 644477 = 241679) (by norm_num)
theorem B546193 : Blo 428775 546193 := bbase (se 2 (by rfl) ⟨204822, by rfl⟩ : syracuseStep 546193 = 409645) (by norm_num)
theorem B644501 : Blo 428775 644501 := bbase (se 6 (by rfl) ⟨15105, by rfl⟩ : syracuseStep 644501 = 30211) (by norm_num)
theorem B972197 : Blo 428775 972197 := bbase (se 4 (by rfl) ⟨91143, by rfl⟩ : syracuseStep 972197 = 182287) (by norm_num)
theorem B644525 : Blo 428775 644525 := bbase (se 3 (by rfl) ⟨120848, by rfl⟩ : syracuseStep 644525 = 241697) (by norm_num)
theorem B644549 : Blo 428775 644549 := bbase (se 4 (by rfl) ⟨60426, by rfl⟩ : syracuseStep 644549 = 120853) (by norm_num)
theorem B644573 : Blo 428775 644573 := bbase (se 3 (by rfl) ⟨120857, by rfl⟩ : syracuseStep 644573 = 241715) (by norm_num)
theorem B972269 : Blo 428775 972269 := bbase (se 3 (by rfl) ⟨182300, by rfl⟩ : syracuseStep 972269 = 364601) (by norm_num)
theorem B644597 : Blo 428775 644597 := bbase (se 5 (by rfl) ⟨30215, by rfl⟩ : syracuseStep 644597 = 60431) (by norm_num)
theorem B644621 : Blo 428775 644621 := bbase (se 3 (by rfl) ⟨120866, by rfl⟩ : syracuseStep 644621 = 241733) (by norm_num)
theorem B644645 : Blo 428775 644645 := bbase (se 4 (by rfl) ⟨60435, by rfl⟩ : syracuseStep 644645 = 120871) (by norm_num)
theorem B874037 : Blo 428775 874037 := bbase (se 5 (by rfl) ⟨40970, by rfl⟩ : syracuseStep 874037 = 81941) (by norm_num)
theorem B972341 : Blo 428775 972341 := bbase (se 5 (by rfl) ⟨45578, by rfl⟩ : syracuseStep 972341 = 91157) (by norm_num)
theorem B644669 : Blo 428775 644669 := bbase (se 3 (by rfl) ⟨120875, by rfl⟩ : syracuseStep 644669 = 241751) (by norm_num)
theorem B546365 : Blo 428775 546365 := bbase (se 3 (by rfl) ⟨102443, by rfl⟩ : syracuseStep 546365 = 204887) (by norm_num)
theorem B644693 : Blo 428775 644693 := bbase (se 8 (by rfl) ⟨3777, by rfl⟩ : syracuseStep 644693 = 7555) (by norm_num)
theorem B644717 : Blo 428775 644717 := bbase (se 3 (by rfl) ⟨120884, by rfl⟩ : syracuseStep 644717 = 241769) (by norm_num)
theorem B546421 : Blo 428775 546421 := bbase (se 5 (by rfl) ⟨25613, by rfl⟩ : syracuseStep 546421 = 51227) (by norm_num)
theorem B972413 : Blo 428775 972413 := bbase (se 3 (by rfl) ⟨182327, by rfl⟩ : syracuseStep 972413 = 364655) (by norm_num)
theorem B644741 : Blo 428775 644741 := bbase (se 4 (by rfl) ⟨60444, by rfl⟩ : syracuseStep 644741 = 120889) (by norm_num)
theorem B644765 : Blo 428775 644765 := bbase (se 3 (by rfl) ⟨120893, by rfl⟩ : syracuseStep 644765 = 241787) (by norm_num)
theorem B644789 : Blo 428775 644789 := bbase (se 5 (by rfl) ⟨30224, by rfl⟩ : syracuseStep 644789 = 60449) (by norm_num)
theorem B972485 : Blo 428775 972485 := bbase (se 4 (by rfl) ⟨91170, by rfl⟩ : syracuseStep 972485 = 182341) (by norm_num)
theorem B644813 : Blo 428775 644813 := bbase (se 3 (by rfl) ⟨120902, by rfl⟩ : syracuseStep 644813 = 241805) (by norm_num)
theorem B546517 : Blo 428775 546517 := bbase (se 7 (by rfl) ⟨6404, by rfl⟩ : syracuseStep 546517 = 12809) (by norm_num)
theorem B644837 : Blo 428775 644837 := bbase (se 4 (by rfl) ⟨60453, by rfl⟩ : syracuseStep 644837 = 120907) (by norm_num)
theorem B644861 : Blo 428775 644861 := bbase (se 3 (by rfl) ⟨120911, by rfl⟩ : syracuseStep 644861 = 241823) (by norm_num)
theorem B972557 : Blo 428775 972557 := bbase (se 3 (by rfl) ⟨182354, by rfl⟩ : syracuseStep 972557 = 364709) (by norm_num)
theorem B644885 : Blo 428775 644885 := bbase (se 6 (by rfl) ⟨15114, by rfl⟩ : syracuseStep 644885 = 30229) (by norm_num)
theorem B644909 : Blo 428775 644909 := bbase (se 3 (by rfl) ⟨120920, by rfl⟩ : syracuseStep 644909 = 241841) (by norm_num)
theorem B1038125 : Blo 428775 1038125 := bbase (se 3 (by rfl) ⟨194648, by rfl⟩ : syracuseStep 1038125 = 389297) (by norm_num)
theorem B644933 : Blo 428775 644933 := bbase (se 4 (by rfl) ⟨60462, by rfl⟩ : syracuseStep 644933 = 120925) (by norm_num)
theorem B972629 : Blo 428775 972629 := bbase (se 9 (by rfl) ⟨2849, by rfl⟩ : syracuseStep 972629 = 5699) (by norm_num)
theorem B644957 : Blo 428775 644957 := bbase (se 3 (by rfl) ⟨120929, by rfl⟩ : syracuseStep 644957 = 241859) (by norm_num)
theorem B644981 : Blo 428775 644981 := bbase (se 5 (by rfl) ⟨30233, by rfl⟩ : syracuseStep 644981 = 60467) (by norm_num)
theorem B546689 : Blo 428775 546689 := bbase (se 2 (by rfl) ⟨205008, by rfl⟩ : syracuseStep 546689 = 410017) (by norm_num)
theorem B645005 : Blo 428775 645005 := bbase (se 3 (by rfl) ⟨120938, by rfl⟩ : syracuseStep 645005 = 241877) (by norm_num)
theorem B972701 : Blo 428775 972701 := bbase (se 3 (by rfl) ⟨182381, by rfl⟩ : syracuseStep 972701 = 364763) (by norm_num)
theorem B645029 : Blo 428775 645029 := bbase (se 4 (by rfl) ⟨60471, by rfl⟩ : syracuseStep 645029 = 120943) (by norm_num)
theorem B546745 : Blo 428775 546745 := bbase (se 2 (by rfl) ⟨205029, by rfl⟩ : syracuseStep 546745 = 410059) (by norm_num)
theorem B645053 : Blo 428775 645053 := bbase (se 3 (by rfl) ⟨120947, by rfl⟩ : syracuseStep 645053 = 241895) (by norm_num)
theorem B645077 : Blo 428775 645077 := bbase (se 7 (by rfl) ⟨7559, by rfl⟩ : syracuseStep 645077 = 15119) (by norm_num)
theorem B972773 : Blo 428775 972773 := bbase (se 4 (by rfl) ⟨91197, by rfl⟩ : syracuseStep 972773 = 182395) (by norm_num)
theorem B645101 : Blo 428775 645101 := bbase (se 3 (by rfl) ⟨120956, by rfl⟩ : syracuseStep 645101 = 241913) (by norm_num)
theorem B645125 : Blo 428775 645125 := bbase (se 4 (by rfl) ⟨60480, by rfl⟩ : syracuseStep 645125 = 120961) (by norm_num)
theorem B546841 : Blo 428775 546841 := bbase (se 2 (by rfl) ⟨205065, by rfl⟩ : syracuseStep 546841 = 410131) (by norm_num)
theorem B645149 : Blo 428775 645149 := bbase (se 3 (by rfl) ⟨120965, by rfl⟩ : syracuseStep 645149 = 241931) (by norm_num)
theorem B972845 : Blo 428775 972845 := bbase (se 3 (by rfl) ⟨182408, by rfl⟩ : syracuseStep 972845 = 364817) (by norm_num)
theorem B645173 : Blo 428775 645173 := bbase (se 5 (by rfl) ⟨30242, by rfl⟩ : syracuseStep 645173 = 60485) (by norm_num)
theorem B776245 : Blo 428775 776245 := bbase (se 5 (by rfl) ⟨36386, by rfl⟩ : syracuseStep 776245 = 72773) (by norm_num)
theorem B645197 : Blo 428775 645197 := bbase (se 3 (by rfl) ⟨120974, by rfl⟩ : syracuseStep 645197 = 241949) (by norm_num)
theorem B645221 : Blo 428775 645221 := bbase (se 4 (by rfl) ⟨60489, by rfl⟩ : syracuseStep 645221 = 120979) (by norm_num)
theorem B972917 : Blo 428775 972917 := bbase (se 5 (by rfl) ⟨45605, by rfl⟩ : syracuseStep 972917 = 91211) (by norm_num)
theorem B645245 : Blo 428775 645245 := bbase (se 3 (by rfl) ⟨120983, by rfl⟩ : syracuseStep 645245 = 241967) (by norm_num)
theorem B776317 : Blo 428775 776317 := bbase (se 3 (by rfl) ⟨145559, by rfl⟩ : syracuseStep 776317 = 291119) (by norm_num)
theorem B645269 : Blo 428775 645269 := bbase (se 6 (by rfl) ⟨15123, by rfl⟩ : syracuseStep 645269 = 30247) (by norm_num)
theorem B645293 : Blo 428775 645293 := bbase (se 3 (by rfl) ⟨120992, by rfl⟩ : syracuseStep 645293 = 241985) (by norm_num)
theorem B3496117 : Blo 428775 3496117 := bbase (se 5 (by rfl) ⟨163880, by rfl⟩ : syracuseStep 3496117 = 327761) (by norm_num)
theorem B972989 : Blo 428775 972989 := bbase (se 3 (by rfl) ⟨182435, by rfl⟩ : syracuseStep 972989 = 364871) (by norm_num)
theorem B645317 : Blo 428775 645317 := bbase (se 4 (by rfl) ⟨60498, by rfl⟩ : syracuseStep 645317 = 120997) (by norm_num)
theorem B547013 : Blo 428775 547013 := bbase (se 4 (by rfl) ⟨51282, by rfl⟩ : syracuseStep 547013 = 102565) (by norm_num)
theorem B645341 : Blo 428775 645341 := bbase (se 3 (by rfl) ⟨121001, by rfl⟩ : syracuseStep 645341 = 242003) (by norm_num)
theorem B645365 : Blo 428775 645365 := bbase (se 5 (by rfl) ⟨30251, by rfl⟩ : syracuseStep 645365 = 60503) (by norm_num)
theorem B547069 : Blo 428775 547069 := bbase (se 3 (by rfl) ⟨102575, by rfl⟩ : syracuseStep 547069 = 205151) (by norm_num)
theorem B973061 : Blo 428775 973061 := bbase (se 4 (by rfl) ⟨91224, by rfl⟩ : syracuseStep 973061 = 182449) (by norm_num)
theorem B645389 : Blo 428775 645389 := bbase (se 3 (by rfl) ⟨121010, by rfl⟩ : syracuseStep 645389 = 242021) (by norm_num)
theorem B776461 : Blo 428775 776461 := bbase (se 3 (by rfl) ⟨145586, by rfl⟩ : syracuseStep 776461 = 291173) (by norm_num)
theorem B645413 : Blo 428775 645413 := bbase (se 4 (by rfl) ⟨60507, by rfl⟩ : syracuseStep 645413 = 121015) (by norm_num)
theorem B645437 : Blo 428775 645437 := bbase (se 3 (by rfl) ⟨121019, by rfl⟩ : syracuseStep 645437 = 242039) (by norm_num)
theorem B2185541 : Blo 428775 2185541 := bbase (se 4 (by rfl) ⟨204894, by rfl⟩ : syracuseStep 2185541 = 409789) (by norm_num)
theorem B973133 : Blo 428775 973133 := bbase (se 3 (by rfl) ⟨182462, by rfl⟩ : syracuseStep 973133 = 364925) (by norm_num)
theorem B645461 : Blo 428775 645461 := bbase (se 10 (by rfl) ⟨945, by rfl⟩ : syracuseStep 645461 = 1891) (by norm_num)
theorem B547165 : Blo 428775 547165 := bbase (se 3 (by rfl) ⟨102593, by rfl⟩ : syracuseStep 547165 = 205187) (by norm_num)
theorem B645485 : Blo 428775 645485 := bbase (se 3 (by rfl) ⟨121028, by rfl⟩ : syracuseStep 645485 = 242057) (by norm_num)
theorem B645509 : Blo 428775 645509 := bbase (se 4 (by rfl) ⟨60516, by rfl⟩ : syracuseStep 645509 = 121033) (by norm_num)
theorem B973205 : Blo 428775 973205 := bbase (se 6 (by rfl) ⟨22809, by rfl⟩ : syracuseStep 973205 = 45619) (by norm_num)
theorem B645533 : Blo 428775 645533 := bbase (se 3 (by rfl) ⟨121037, by rfl⟩ : syracuseStep 645533 = 242075) (by norm_num)
theorem B645557 : Blo 428775 645557 := bbase (se 5 (by rfl) ⟨30260, by rfl⟩ : syracuseStep 645557 = 60521) (by norm_num)
theorem B645581 : Blo 428775 645581 := bbase (se 3 (by rfl) ⟨121046, by rfl⟩ : syracuseStep 645581 = 242093) (by norm_num)
theorem B973277 : Blo 428775 973277 := bbase (se 3 (by rfl) ⟨182489, by rfl⟩ : syracuseStep 973277 = 364979) (by norm_num)
theorem B645605 : Blo 428775 645605 := bbase (se 4 (by rfl) ⟨60525, by rfl⟩ : syracuseStep 645605 = 121051) (by norm_num)
theorem B645629 : Blo 428775 645629 := bbase (se 3 (by rfl) ⟨121055, by rfl⟩ : syracuseStep 645629 = 242111) (by norm_num)
theorem B547337 : Blo 428775 547337 := bbase (se 2 (by rfl) ⟨205251, by rfl⟩ : syracuseStep 547337 = 410503) (by norm_num)
theorem B1628693 : Blo 428775 1628693 := bbase (se 6 (by rfl) ⟨38172, by rfl⟩ : syracuseStep 1628693 = 76345) (by norm_num)
theorem B645653 : Blo 428775 645653 := bbase (se 6 (by rfl) ⟨15132, by rfl⟩ : syracuseStep 645653 = 30265) (by norm_num)
theorem B973349 : Blo 428775 973349 := bbase (se 4 (by rfl) ⟨91251, by rfl⟩ : syracuseStep 973349 = 182503) (by norm_num)
theorem B645677 : Blo 428775 645677 := bbase (se 3 (by rfl) ⟨121064, by rfl⟩ : syracuseStep 645677 = 242129) (by norm_num)
theorem B547393 : Blo 428775 547393 := bbase (se 2 (by rfl) ⟨205272, by rfl⟩ : syracuseStep 547393 = 410545) (by norm_num)
theorem B645701 : Blo 428775 645701 := bbase (se 4 (by rfl) ⟨60534, by rfl⟩ : syracuseStep 645701 = 121069) (by norm_num)
theorem B645725 : Blo 428775 645725 := bbase (se 3 (by rfl) ⟨121073, by rfl⟩ : syracuseStep 645725 = 242147) (by norm_num)
theorem B973421 : Blo 428775 973421 := bbase (se 3 (by rfl) ⟨182516, by rfl⟩ : syracuseStep 973421 = 365033) (by norm_num)
theorem B645749 : Blo 428775 645749 := bbase (se 5 (by rfl) ⟨30269, by rfl⟩ : syracuseStep 645749 = 60539) (by norm_num)
theorem B645773 : Blo 428775 645773 := bbase (se 3 (by rfl) ⟨121082, by rfl⟩ : syracuseStep 645773 = 242165) (by norm_num)
theorem B613021 : Blo 428775 613021 := bbase (se 3 (by rfl) ⟨114941, by rfl⟩ : syracuseStep 613021 = 229883) (by norm_num)
theorem B547489 : Blo 428775 547489 := bbase (se 2 (by rfl) ⟨205308, by rfl⟩ : syracuseStep 547489 = 410617) (by norm_num)
theorem B645797 : Blo 428775 645797 := bbase (se 4 (by rfl) ⟨60543, by rfl⟩ : syracuseStep 645797 = 121087) (by norm_num)
theorem B973493 : Blo 428775 973493 := bbase (se 5 (by rfl) ⟨45632, by rfl⟩ : syracuseStep 973493 = 91265) (by norm_num)
theorem B645821 : Blo 428775 645821 := bbase (se 3 (by rfl) ⟨121091, by rfl⟩ : syracuseStep 645821 = 242183) (by norm_num)
theorem B645845 : Blo 428775 645845 := bbase (se 7 (by rfl) ⟨7568, by rfl⟩ : syracuseStep 645845 = 15137) (by norm_num)
theorem B645869 : Blo 428775 645869 := bbase (se 3 (by rfl) ⟨121100, by rfl⟩ : syracuseStep 645869 = 242201) (by norm_num)
theorem B973565 : Blo 428775 973565 := bbase (se 3 (by rfl) ⟨182543, by rfl⟩ : syracuseStep 973565 = 365087) (by norm_num)
theorem B645893 : Blo 428775 645893 := bbase (se 4 (by rfl) ⟨60552, by rfl⟩ : syracuseStep 645893 = 121105) (by norm_num)
theorem B875269 : Blo 428775 875269 := bbase (se 4 (by rfl) ⟨82056, by rfl⟩ : syracuseStep 875269 = 164113) (by norm_num)
theorem B645917 : Blo 428775 645917 := bbase (se 3 (by rfl) ⟨121109, by rfl⟩ : syracuseStep 645917 = 242219) (by norm_num)
theorem B1628981 : Blo 428775 1628981 := bbase (se 5 (by rfl) ⟨76358, by rfl⟩ : syracuseStep 1628981 = 152717) (by norm_num)
theorem B645941 : Blo 428775 645941 := bbase (se 5 (by rfl) ⟨30278, by rfl⟩ : syracuseStep 645941 = 60557) (by norm_num)
theorem B973637 : Blo 428775 973637 := bbase (se 4 (by rfl) ⟨91278, by rfl⟩ : syracuseStep 973637 = 182557) (by norm_num)
theorem B645965 : Blo 428775 645965 := bbase (se 3 (by rfl) ⟨121118, by rfl⟩ : syracuseStep 645965 = 242237) (by norm_num)
theorem B547661 : Blo 428775 547661 := bbase (se 3 (by rfl) ⟨102686, by rfl⟩ : syracuseStep 547661 = 205373) (by norm_num)
theorem B1858405 : Blo 428775 1858405 := bbase (se 4 (by rfl) ⟨174225, by rfl⟩ : syracuseStep 1858405 = 348451) (by norm_num)
theorem B645989 : Blo 428775 645989 := bbase (se 4 (by rfl) ⟨60561, by rfl⟩ : syracuseStep 645989 = 121123) (by norm_num)
theorem B646013 : Blo 428775 646013 := bbase (se 3 (by rfl) ⟨121127, by rfl⟩ : syracuseStep 646013 = 242255) (by norm_num)
theorem B547717 : Blo 428775 547717 := bbase (se 4 (by rfl) ⟨51348, by rfl⟩ : syracuseStep 547717 = 102697) (by norm_num)
theorem B973709 : Blo 428775 973709 := bbase (se 3 (by rfl) ⟨182570, by rfl⟩ : syracuseStep 973709 = 365141) (by norm_num)
theorem B646037 : Blo 428775 646037 := bbase (se 6 (by rfl) ⟨15141, by rfl⟩ : syracuseStep 646037 = 30283) (by norm_num)
theorem B646061 : Blo 428775 646061 := bbase (se 3 (by rfl) ⟨121136, by rfl⟩ : syracuseStep 646061 = 242273) (by norm_num)
theorem B646085 : Blo 428775 646085 := bbase (se 4 (by rfl) ⟨60570, by rfl⟩ : syracuseStep 646085 = 121141) (by norm_num)
theorem B646109 : Blo 428775 646109 := bbase (se 3 (by rfl) ⟨121145, by rfl⟩ : syracuseStep 646109 = 242291) (by norm_num)
theorem B646133 : Blo 428775 646133 := bbase (se 5 (by rfl) ⟨30287, by rfl⟩ : syracuseStep 646133 = 60575) (by norm_num)
theorem B646157 : Blo 428775 646157 := bbase (se 3 (by rfl) ⟨121154, by rfl⟩ : syracuseStep 646157 = 242309) (by norm_num)
theorem B646181 : Blo 428775 646181 := bbase (se 4 (by rfl) ⟨60579, by rfl⟩ : syracuseStep 646181 = 121159) (by norm_num)
theorem B777269 : Blo 428775 777269 := bbase (se 5 (by rfl) ⟨36434, by rfl⟩ : syracuseStep 777269 = 72869) (by norm_num)
theorem B646205 : Blo 428775 646205 := bbase (se 3 (by rfl) ⟨121163, by rfl⟩ : syracuseStep 646205 = 242327) (by norm_num)
theorem B515141 : Blo 428775 515141 := bbase (se 4 (by rfl) ⟨48294, by rfl⟩ : syracuseStep 515141 = 96589) (by norm_num)
theorem B482377 : Blo 428775 482377 := bbase (se 2 (by rfl) ⟨180891, by rfl⟩ : syracuseStep 482377 = 361783) (by norm_num)
theorem B646229 : Blo 428775 646229 := bbase (se 8 (by rfl) ⟨3786, by rfl⟩ : syracuseStep 646229 = 7573) (by norm_num)
theorem B482413 : Blo 428775 482413 := bbase (se 3 (by rfl) ⟨90452, by rfl⟩ : syracuseStep 482413 = 180905) (by norm_num)
theorem B646253 : Blo 428775 646253 := bbase (se 3 (by rfl) ⟨121172, by rfl⟩ : syracuseStep 646253 = 242345) (by norm_num)
theorem B777325 : Blo 428775 777325 := bbase (se 3 (by rfl) ⟨145748, by rfl⟩ : syracuseStep 777325 = 291497) (by norm_num)
theorem B646277 : Blo 428775 646277 := bbase (se 4 (by rfl) ⟨60588, by rfl⟩ : syracuseStep 646277 = 121177) (by norm_num)
theorem B482449 : Blo 428775 482449 := bbase (se 2 (by rfl) ⟨180918, by rfl⟩ : syracuseStep 482449 = 361837) (by norm_num)
theorem B646301 : Blo 428775 646301 := bbase (se 3 (by rfl) ⟨121181, by rfl⟩ : syracuseStep 646301 = 242363) (by norm_num)
theorem B2022565 : Blo 428775 2022565 := bbase (se 4 (by rfl) ⟨189615, by rfl⟩ : syracuseStep 2022565 = 379231) (by norm_num)
theorem B482485 : Blo 428775 482485 := bbase (se 5 (by rfl) ⟨22616, by rfl⟩ : syracuseStep 482485 = 45233) (by norm_num)
theorem B646325 : Blo 428775 646325 := bbase (se 5 (by rfl) ⟨30296, by rfl⟩ : syracuseStep 646325 = 60593) (by norm_num)
theorem B777413 : Blo 428775 777413 := bbase (se 4 (by rfl) ⟨72882, by rfl⟩ : syracuseStep 777413 = 145765) (by norm_num)
theorem B646349 : Blo 428775 646349 := bbase (se 3 (by rfl) ⟨121190, by rfl⟩ : syracuseStep 646349 = 242381) (by norm_num)
theorem B482521 : Blo 428775 482521 := bbase (se 2 (by rfl) ⟨180945, by rfl⟩ : syracuseStep 482521 = 361891) (by norm_num)
theorem B646373 : Blo 428775 646373 := bbase (se 4 (by rfl) ⟨60597, by rfl⟩ : syracuseStep 646373 = 121195) (by norm_num)
theorem B613613 : Blo 428775 613613 := bbase (se 3 (by rfl) ⟨115052, by rfl⟩ : syracuseStep 613613 = 230105) (by norm_num)
theorem B482557 : Blo 428775 482557 := bbase (se 3 (by rfl) ⟨90479, by rfl⟩ : syracuseStep 482557 = 180959) (by norm_num)
theorem B646397 : Blo 428775 646397 := bbase (se 3 (by rfl) ⟨121199, by rfl⟩ : syracuseStep 646397 = 242399) (by norm_num)
theorem B875789 : Blo 428775 875789 := bbase (se 3 (by rfl) ⟨164210, by rfl⟩ : syracuseStep 875789 = 328421) (by norm_num)
theorem B646421 : Blo 428775 646421 := bbase (se 6 (by rfl) ⟨15150, by rfl⟩ : syracuseStep 646421 = 30301) (by norm_num)
theorem B482593 : Blo 428775 482593 := bbase (se 2 (by rfl) ⟨180972, by rfl⟩ : syracuseStep 482593 = 361945) (by norm_num)
theorem B646445 : Blo 428775 646445 := bbase (se 3 (by rfl) ⟨121208, by rfl⟩ : syracuseStep 646445 = 242417) (by norm_num)
theorem B613693 : Blo 428775 613693 := bbase (se 3 (by rfl) ⟨115067, by rfl⟩ : syracuseStep 613693 = 230135) (by norm_num)
theorem B482629 : Blo 428775 482629 := bbase (se 4 (by rfl) ⟨45246, by rfl⟩ : syracuseStep 482629 = 90493) (by norm_num)
theorem B646469 : Blo 428775 646469 := bbase (se 4 (by rfl) ⟨60606, by rfl⟩ : syracuseStep 646469 = 121213) (by norm_num)
theorem B646493 : Blo 428775 646493 := bbase (se 3 (by rfl) ⟨121217, by rfl⟩ : syracuseStep 646493 = 242435) (by norm_num)
theorem B482665 : Blo 428775 482665 := bbase (se 2 (by rfl) ⟨180999, by rfl⟩ : syracuseStep 482665 = 361999) (by norm_num)
theorem B646517 : Blo 428775 646517 := bbase (se 5 (by rfl) ⟨30305, by rfl⟩ : syracuseStep 646517 = 60611) (by norm_num)
theorem B482701 : Blo 428775 482701 := bbase (se 3 (by rfl) ⟨90506, by rfl⟩ : syracuseStep 482701 = 181013) (by norm_num)
theorem B646541 : Blo 428775 646541 := bbase (se 3 (by rfl) ⟨121226, by rfl⟩ : syracuseStep 646541 = 242453) (by norm_num)
theorem B1105301 : Blo 428775 1105301 := bbase (se 6 (by rfl) ⟨25905, by rfl⟩ : syracuseStep 1105301 = 51811) (by norm_num)
theorem B646565 : Blo 428775 646565 := bbase (se 4 (by rfl) ⟨60615, by rfl⟩ : syracuseStep 646565 = 121231) (by norm_num)
theorem B482737 : Blo 428775 482737 := bbase (se 2 (by rfl) ⟨181026, by rfl⟩ : syracuseStep 482737 = 362053) (by norm_num)
theorem B613813 : Blo 428775 613813 := bbase (se 5 (by rfl) ⟨28772, by rfl⟩ : syracuseStep 613813 = 57545) (by norm_num)
theorem B646589 : Blo 428775 646589 := bbase (se 3 (by rfl) ⟨121235, by rfl⟩ : syracuseStep 646589 = 242471) (by norm_num)
theorem B482773 : Blo 428775 482773 := bbase (se 7 (by rfl) ⟨5657, by rfl⟩ : syracuseStep 482773 = 11315) (by norm_num)
theorem B646613 : Blo 428775 646613 := bbase (se 7 (by rfl) ⟨7577, by rfl⟩ : syracuseStep 646613 = 15155) (by norm_num)
theorem B777701 : Blo 428775 777701 := bbase (se 4 (by rfl) ⟨72909, by rfl⟩ : syracuseStep 777701 = 145819) (by norm_num)
theorem B646637 : Blo 428775 646637 := bbase (se 3 (by rfl) ⟨121244, by rfl⟩ : syracuseStep 646637 = 242489) (by norm_num)
theorem B482809 : Blo 428775 482809 := bbase (se 2 (by rfl) ⟨181053, by rfl⟩ : syracuseStep 482809 = 362107) (by norm_num)
theorem B646661 : Blo 428775 646661 := bbase (se 4 (by rfl) ⟨60624, by rfl⟩ : syracuseStep 646661 = 121249) (by norm_num)
theorem B613909 : Blo 428775 613909 := bbase (se 6 (by rfl) ⟨14388, by rfl⟩ : syracuseStep 613909 = 28777) (by norm_num)
theorem B482845 : Blo 428775 482845 := bbase (se 3 (by rfl) ⟨90533, by rfl⟩ : syracuseStep 482845 = 181067) (by norm_num)
theorem B646685 : Blo 428775 646685 := bbase (se 3 (by rfl) ⟨121253, by rfl⟩ : syracuseStep 646685 = 242507) (by norm_num)
theorem B646709 : Blo 428775 646709 := bbase (se 5 (by rfl) ⟨30314, by rfl⟩ : syracuseStep 646709 = 60629) (by norm_num)
theorem B482881 : Blo 428775 482881 := bbase (se 2 (by rfl) ⟨181080, by rfl⟩ : syracuseStep 482881 = 362161) (by norm_num)
theorem B646733 : Blo 428775 646733 := bbase (se 3 (by rfl) ⟨121262, by rfl⟩ : syracuseStep 646733 = 242525) (by norm_num)
theorem B2186837 : Blo 428775 2186837 := bbase (se 8 (by rfl) ⟨12813, by rfl⟩ : syracuseStep 2186837 = 25627) (by norm_num)
theorem B482917 : Blo 428775 482917 := bbase (se 4 (by rfl) ⟨45273, by rfl⟩ : syracuseStep 482917 = 90547) (by norm_num)
theorem B646757 : Blo 428775 646757 := bbase (se 4 (by rfl) ⟨60633, by rfl⟩ : syracuseStep 646757 = 121267) (by norm_num)
theorem B777845 : Blo 428775 777845 := bbase (se 5 (by rfl) ⟨36461, by rfl⟩ : syracuseStep 777845 = 72923) (by norm_num)
theorem B646781 : Blo 428775 646781 := bbase (se 3 (by rfl) ⟨121271, by rfl⟩ : syracuseStep 646781 = 242543) (by norm_num)
theorem B482953 : Blo 428775 482953 := bbase (se 2 (by rfl) ⟨181107, by rfl⟩ : syracuseStep 482953 = 362215) (by norm_num)
theorem B646805 : Blo 428775 646805 := bbase (se 6 (by rfl) ⟨15159, by rfl⟩ : syracuseStep 646805 = 30319) (by norm_num)
theorem B482989 : Blo 428775 482989 := bbase (se 3 (by rfl) ⟨90560, by rfl⟩ : syracuseStep 482989 = 181121) (by norm_num)
theorem B646829 : Blo 428775 646829 := bbase (se 3 (by rfl) ⟨121280, by rfl⟩ : syracuseStep 646829 = 242561) (by norm_num)
theorem B646853 : Blo 428775 646853 := bbase (se 4 (by rfl) ⟨60642, by rfl⟩ : syracuseStep 646853 = 121285) (by norm_num)
theorem B483025 : Blo 428775 483025 := bbase (se 2 (by rfl) ⟨181134, by rfl⟩ : syracuseStep 483025 = 362269) (by norm_num)
theorem B646877 : Blo 428775 646877 := bbase (se 3 (by rfl) ⟨121289, by rfl⟩ : syracuseStep 646877 = 242579) (by norm_num)
theorem B483061 : Blo 428775 483061 := bbase (se 5 (by rfl) ⟨22643, by rfl⟩ : syracuseStep 483061 = 45287) (by norm_num)
theorem B646901 : Blo 428775 646901 := bbase (se 5 (by rfl) ⟨30323, by rfl⟩ : syracuseStep 646901 = 60647) (by norm_num)
theorem B646925 : Blo 428775 646925 := bbase (se 3 (by rfl) ⟨121298, by rfl⟩ : syracuseStep 646925 = 242597) (by norm_num)
theorem B483097 : Blo 428775 483097 := bbase (se 2 (by rfl) ⟨181161, by rfl⟩ : syracuseStep 483097 = 362323) (by norm_num)
theorem B646949 : Blo 428775 646949 := bbase (se 4 (by rfl) ⟨60651, by rfl⟩ : syracuseStep 646949 = 121303) (by norm_num)
theorem B483133 : Blo 428775 483133 := bbase (se 3 (by rfl) ⟨90587, by rfl⟩ : syracuseStep 483133 = 181175) (by norm_num)
theorem B646973 : Blo 428775 646973 := bbase (se 3 (by rfl) ⟨121307, by rfl⟩ : syracuseStep 646973 = 242615) (by norm_num)
theorem B646997 : Blo 428775 646997 := bbase (se 9 (by rfl) ⟨1895, by rfl⟩ : syracuseStep 646997 = 3791) (by norm_num)
theorem B483169 : Blo 428775 483169 := bbase (se 2 (by rfl) ⟨181188, by rfl⟩ : syracuseStep 483169 = 362377) (by norm_num)
theorem B647021 : Blo 428775 647021 := bbase (se 3 (by rfl) ⟨121316, by rfl⟩ : syracuseStep 647021 = 242633) (by norm_num)
theorem B483205 : Blo 428775 483205 := bbase (se 4 (by rfl) ⟨45300, by rfl⟩ : syracuseStep 483205 = 90601) (by norm_num)
theorem B647045 : Blo 428775 647045 := bbase (se 4 (by rfl) ⟨60660, by rfl⟩ : syracuseStep 647045 = 121321) (by norm_num)
theorem B778133 : Blo 428775 778133 := bbase (se 6 (by rfl) ⟨18237, by rfl⟩ : syracuseStep 778133 = 36475) (by norm_num)
theorem B647069 : Blo 428775 647069 := bbase (se 3 (by rfl) ⟨121325, by rfl⟩ : syracuseStep 647069 = 242651) (by norm_num)
theorem B483241 : Blo 428775 483241 := bbase (se 2 (by rfl) ⟨181215, by rfl⟩ : syracuseStep 483241 = 362431) (by norm_num)
theorem B647093 : Blo 428775 647093 := bbase (se 5 (by rfl) ⟨30332, by rfl⟩ : syracuseStep 647093 = 60665) (by norm_num)
theorem B483277 : Blo 428775 483277 := bbase (se 3 (by rfl) ⟨90614, by rfl⟩ : syracuseStep 483277 = 181229) (by norm_num)
theorem B647117 : Blo 428775 647117 := bbase (se 3 (by rfl) ⟨121334, by rfl⟩ : syracuseStep 647117 = 242669) (by norm_num)
theorem B1630165 : Blo 428775 1630165 := bbase (se 7 (by rfl) ⟨19103, by rfl⟩ : syracuseStep 1630165 = 38207) (by norm_num)
theorem B778205 : Blo 428775 778205 := bbase (se 3 (by rfl) ⟨145913, by rfl⟩ : syracuseStep 778205 = 291827) (by norm_num)
theorem B647141 : Blo 428775 647141 := bbase (se 4 (by rfl) ⟨60669, by rfl⟩ : syracuseStep 647141 = 121339) (by norm_num)
theorem B483313 : Blo 428775 483313 := bbase (se 2 (by rfl) ⟨181242, by rfl⟩ : syracuseStep 483313 = 362485) (by norm_num)
theorem B647165 : Blo 428775 647165 := bbase (se 3 (by rfl) ⟨121343, by rfl⟩ : syracuseStep 647165 = 242687) (by norm_num)
theorem B614405 : Blo 428775 614405 := bbase (se 4 (by rfl) ⟨57600, by rfl⟩ : syracuseStep 614405 = 115201) (by norm_num)
theorem B483349 : Blo 428775 483349 := bbase (se 6 (by rfl) ⟨11328, by rfl⟩ : syracuseStep 483349 = 22657) (by norm_num)
theorem B647189 : Blo 428775 647189 := bbase (se 6 (by rfl) ⟨15168, by rfl⟩ : syracuseStep 647189 = 30337) (by norm_num)
theorem B647213 : Blo 428775 647213 := bbase (se 3 (by rfl) ⟨121352, by rfl⟩ : syracuseStep 647213 = 242705) (by norm_num)
theorem B483385 : Blo 428775 483385 := bbase (se 2 (by rfl) ⟨181269, by rfl⟩ : syracuseStep 483385 = 362539) (by norm_num)
theorem B647237 : Blo 428775 647237 := bbase (se 4 (by rfl) ⟨60678, by rfl⟩ : syracuseStep 647237 = 121357) (by norm_num)
theorem B483421 : Blo 428775 483421 := bbase (se 3 (by rfl) ⟨90641, by rfl⟩ : syracuseStep 483421 = 181283) (by norm_num)
theorem B647261 : Blo 428775 647261 := bbase (se 3 (by rfl) ⟨121361, by rfl⟩ : syracuseStep 647261 = 242723) (by norm_num)
theorem B647285 : Blo 428775 647285 := bbase (se 5 (by rfl) ⟨30341, by rfl⟩ : syracuseStep 647285 = 60683) (by norm_num)
theorem B483457 : Blo 428775 483457 := bbase (se 2 (by rfl) ⟨181296, by rfl⟩ : syracuseStep 483457 = 362593) (by norm_num)
theorem B647309 : Blo 428775 647309 := bbase (se 3 (by rfl) ⟨121370, by rfl⟩ : syracuseStep 647309 = 242741) (by norm_num)
theorem B483493 : Blo 428775 483493 := bbase (se 4 (by rfl) ⟨45327, by rfl⟩ : syracuseStep 483493 = 90655) (by norm_num)
theorem B647333 : Blo 428775 647333 := bbase (se 4 (by rfl) ⟨60687, by rfl⟩ : syracuseStep 647333 = 121375) (by norm_num)
theorem B647357 : Blo 428775 647357 := bbase (se 3 (by rfl) ⟨121379, by rfl⟩ : syracuseStep 647357 = 242759) (by norm_num)
theorem B483529 : Blo 428775 483529 := bbase (se 2 (by rfl) ⟨181323, by rfl⟩ : syracuseStep 483529 = 362647) (by norm_num)
theorem B647381 : Blo 428775 647381 := bbase (se 7 (by rfl) ⟨7586, by rfl⟩ : syracuseStep 647381 = 15173) (by norm_num)
theorem B483565 : Blo 428775 483565 := bbase (se 3 (by rfl) ⟨90668, by rfl⟩ : syracuseStep 483565 = 181337) (by norm_num)
theorem B647405 : Blo 428775 647405 := bbase (se 3 (by rfl) ⟨121388, by rfl⟩ : syracuseStep 647405 = 242777) (by norm_num)
theorem B1630469 : Blo 428775 1630469 := bbase (se 4 (by rfl) ⟨152856, by rfl⟩ : syracuseStep 1630469 = 305713) (by norm_num)
theorem B647429 : Blo 428775 647429 := bbase (se 4 (by rfl) ⟨60696, by rfl⟩ : syracuseStep 647429 = 121393) (by norm_num)
theorem B483601 : Blo 428775 483601 := bbase (se 2 (by rfl) ⟨181350, by rfl⟩ : syracuseStep 483601 = 362701) (by norm_num)
theorem B647453 : Blo 428775 647453 := bbase (se 3 (by rfl) ⟨121397, by rfl⟩ : syracuseStep 647453 = 242795) (by norm_num)
theorem B483637 : Blo 428775 483637 := bbase (se 5 (by rfl) ⟨22670, by rfl⟩ : syracuseStep 483637 = 45341) (by norm_num)
theorem B647477 : Blo 428775 647477 := bbase (se 5 (by rfl) ⟨30350, by rfl⟩ : syracuseStep 647477 = 60701) (by norm_num)
theorem B647501 : Blo 428775 647501 := bbase (se 3 (by rfl) ⟨121406, by rfl⟩ : syracuseStep 647501 = 242813) (by norm_num)
theorem B483673 : Blo 428775 483673 := bbase (se 2 (by rfl) ⟨181377, by rfl⟩ : syracuseStep 483673 = 362755) (by norm_num)
theorem B647525 : Blo 428775 647525 := bbase (se 4 (by rfl) ⟨60705, by rfl⟩ : syracuseStep 647525 = 121411) (by norm_num)
theorem B483709 : Blo 428775 483709 := bbase (se 3 (by rfl) ⟨90695, by rfl⟩ : syracuseStep 483709 = 181391) (by norm_num)
theorem B647549 : Blo 428775 647549 := bbase (se 3 (by rfl) ⟨121415, by rfl⟩ : syracuseStep 647549 = 242831) (by norm_num)
theorem B647573 : Blo 428775 647573 := bbase (se 6 (by rfl) ⟨15177, by rfl⟩ : syracuseStep 647573 = 30355) (by norm_num)
theorem B483745 : Blo 428775 483745 := bbase (se 2 (by rfl) ⟨181404, by rfl⟩ : syracuseStep 483745 = 362809) (by norm_num)
theorem B647597 : Blo 428775 647597 := bbase (se 3 (by rfl) ⟨121424, by rfl⟩ : syracuseStep 647597 = 242849) (by norm_num)
theorem B483781 : Blo 428775 483781 := bbase (se 4 (by rfl) ⟨45354, by rfl⟩ : syracuseStep 483781 = 90709) (by norm_num)
theorem B647621 : Blo 428775 647621 := bbase (se 4 (by rfl) ⟨60714, by rfl⟩ : syracuseStep 647621 = 121429) (by norm_num)
theorem B1106389 : Blo 428775 1106389 := bbase (se 7 (by rfl) ⟨12965, by rfl⟩ : syracuseStep 1106389 = 25931) (by norm_num)
theorem B647645 : Blo 428775 647645 := bbase (se 3 (by rfl) ⟨121433, by rfl⟩ : syracuseStep 647645 = 242867) (by norm_num)
theorem B483817 : Blo 428775 483817 := bbase (se 2 (by rfl) ⟨181431, by rfl⟩ : syracuseStep 483817 = 362863) (by norm_num)
theorem B647669 : Blo 428775 647669 := bbase (se 5 (by rfl) ⟨30359, by rfl⟩ : syracuseStep 647669 = 60719) (by norm_num)
theorem B483853 : Blo 428775 483853 := bbase (se 3 (by rfl) ⟨90722, by rfl⟩ : syracuseStep 483853 = 181445) (by norm_num)
theorem B647693 : Blo 428775 647693 := bbase (se 3 (by rfl) ⟨121442, by rfl⟩ : syracuseStep 647693 = 242885) (by norm_num)
theorem B647717 : Blo 428775 647717 := bbase (se 4 (by rfl) ⟨60723, by rfl⟩ : syracuseStep 647717 = 121447) (by norm_num)
theorem B614957 : Blo 428775 614957 := bbase (se 3 (by rfl) ⟨115304, by rfl⟩ : syracuseStep 614957 = 230609) (by norm_num)
theorem B483889 : Blo 428775 483889 := bbase (se 2 (by rfl) ⟨181458, by rfl⟩ : syracuseStep 483889 = 362917) (by norm_num)
theorem B647741 : Blo 428775 647741 := bbase (se 3 (by rfl) ⟨121451, by rfl⟩ : syracuseStep 647741 = 242903) (by norm_num)
theorem B483925 : Blo 428775 483925 := bbase (se 8 (by rfl) ⟨2835, by rfl⟩ : syracuseStep 483925 = 5671) (by norm_num)
theorem B647765 : Blo 428775 647765 := bbase (se 8 (by rfl) ⟨3795, by rfl⟩ : syracuseStep 647765 = 7591) (by norm_num)
theorem B516713 : Blo 428775 516713 := bbase (se 2 (by rfl) ⟨193767, by rfl⟩ : syracuseStep 516713 = 387535) (by norm_num)
theorem B647789 : Blo 428775 647789 := bbase (se 3 (by rfl) ⟨121460, by rfl⟩ : syracuseStep 647789 = 242921) (by norm_num)
theorem B483961 : Blo 428775 483961 := bbase (se 2 (by rfl) ⟨181485, by rfl⟩ : syracuseStep 483961 = 362971) (by norm_num)
theorem B516737 : Blo 428775 516737 := bbase (se 2 (by rfl) ⟨193776, by rfl⟩ : syracuseStep 516737 = 387553) (by norm_num)
theorem B647813 : Blo 428775 647813 := bbase (se 4 (by rfl) ⟨60732, by rfl⟩ : syracuseStep 647813 = 121465) (by norm_num)
theorem B483997 : Blo 428775 483997 := bbase (se 3 (by rfl) ⟨90749, by rfl⟩ : syracuseStep 483997 = 181499) (by norm_num)
theorem B647837 : Blo 428775 647837 := bbase (se 3 (by rfl) ⟨121469, by rfl⟩ : syracuseStep 647837 = 242939) (by norm_num)
theorem B647861 : Blo 428775 647861 := bbase (se 5 (by rfl) ⟨30368, by rfl⟩ : syracuseStep 647861 = 60737) (by norm_num)
theorem B484033 : Blo 428775 484033 := bbase (se 2 (by rfl) ⟨181512, by rfl⟩ : syracuseStep 484033 = 363025) (by norm_num)
theorem B647885 : Blo 428775 647885 := bbase (se 3 (by rfl) ⟨121478, by rfl⟩ : syracuseStep 647885 = 242957) (by norm_num)
theorem B484069 : Blo 428775 484069 := bbase (se 4 (by rfl) ⟨45381, by rfl⟩ : syracuseStep 484069 = 90763) (by norm_num)
theorem B647909 : Blo 428775 647909 := bbase (se 4 (by rfl) ⟨60741, by rfl⟩ : syracuseStep 647909 = 121483) (by norm_num)
theorem B647933 : Blo 428775 647933 := bbase (se 3 (by rfl) ⟨121487, by rfl⟩ : syracuseStep 647933 = 242975) (by norm_num)
theorem B484105 : Blo 428775 484105 := bbase (se 2 (by rfl) ⟨181539, by rfl⟩ : syracuseStep 484105 = 363079) (by norm_num)
theorem B647957 : Blo 428775 647957 := bbase (se 6 (by rfl) ⟨15186, by rfl⟩ : syracuseStep 647957 = 30373) (by norm_num)
theorem B484141 : Blo 428775 484141 := bbase (se 3 (by rfl) ⟨90776, by rfl⟩ : syracuseStep 484141 = 181553) (by norm_num)
theorem B647981 : Blo 428775 647981 := bbase (se 3 (by rfl) ⟨121496, by rfl⟩ : syracuseStep 647981 = 242993) (by norm_num)
theorem B648005 : Blo 428775 648005 := bbase (se 4 (by rfl) ⟨60750, by rfl⟩ : syracuseStep 648005 = 121501) (by norm_num)
theorem B484177 : Blo 428775 484177 := bbase (se 2 (by rfl) ⟨181566, by rfl⟩ : syracuseStep 484177 = 363133) (by norm_num)
theorem B648029 : Blo 428775 648029 := bbase (se 3 (by rfl) ⟨121505, by rfl⟩ : syracuseStep 648029 = 243011) (by norm_num)
theorem B2188133 : Blo 428775 2188133 := bbase (se 4 (by rfl) ⟨205137, by rfl⟩ : syracuseStep 2188133 = 410275) (by norm_num)
theorem B484213 : Blo 428775 484213 := bbase (se 5 (by rfl) ⟨22697, by rfl⟩ : syracuseStep 484213 = 45395) (by norm_num)
theorem B648053 : Blo 428775 648053 := bbase (se 5 (by rfl) ⟨30377, by rfl⟩ : syracuseStep 648053 = 60755) (by norm_num)
theorem B648077 : Blo 428775 648077 := bbase (se 3 (by rfl) ⟨121514, by rfl⟩ : syracuseStep 648077 = 243029) (by norm_num)
theorem B484249 : Blo 428775 484249 := bbase (se 2 (by rfl) ⟨181593, by rfl⟩ : syracuseStep 484249 = 363187) (by norm_num)
theorem B648101 : Blo 428775 648101 := bbase (se 4 (by rfl) ⟨60759, by rfl⟩ : syracuseStep 648101 = 121519) (by norm_num)
theorem B517045 : Blo 428775 517045 := bbase (se 5 (by rfl) ⟨24236, by rfl⟩ : syracuseStep 517045 = 48473) (by norm_num)
theorem B484285 : Blo 428775 484285 := bbase (se 3 (by rfl) ⟨90803, by rfl⟩ : syracuseStep 484285 = 181607) (by norm_num)
theorem B648125 : Blo 428775 648125 := bbase (se 3 (by rfl) ⟨121523, by rfl⟩ : syracuseStep 648125 = 243047) (by norm_num)
theorem B648149 : Blo 428775 648149 := bbase (se 7 (by rfl) ⟨7595, by rfl⟩ : syracuseStep 648149 = 15191) (by norm_num)
theorem B484321 : Blo 428775 484321 := bbase (se 2 (by rfl) ⟨181620, by rfl⟩ : syracuseStep 484321 = 363241) (by norm_num)
theorem B648173 : Blo 428775 648173 := bbase (se 3 (by rfl) ⟨121532, by rfl⟩ : syracuseStep 648173 = 243065) (by norm_num)
theorem B484357 : Blo 428775 484357 := bbase (se 4 (by rfl) ⟨45408, by rfl⟩ : syracuseStep 484357 = 90817) (by norm_num)
theorem B648197 : Blo 428775 648197 := bbase (se 4 (by rfl) ⟨60768, by rfl⟩ : syracuseStep 648197 = 121537) (by norm_num)
theorem B648221 : Blo 428775 648221 := bbase (se 3 (by rfl) ⟨121541, by rfl⟩ : syracuseStep 648221 = 243083) (by norm_num)
theorem B484393 : Blo 428775 484393 := bbase (se 2 (by rfl) ⟨181647, by rfl⟩ : syracuseStep 484393 = 363295) (by norm_num)
theorem B648245 : Blo 428775 648245 := bbase (se 5 (by rfl) ⟨30386, by rfl⟩ : syracuseStep 648245 = 60773) (by norm_num)
theorem B484429 : Blo 428775 484429 := bbase (se 3 (by rfl) ⟨90830, by rfl⟩ : syracuseStep 484429 = 181661) (by norm_num)
theorem B648269 : Blo 428775 648269 := bbase (se 3 (by rfl) ⟨121550, by rfl⟩ : syracuseStep 648269 = 243101) (by norm_num)
theorem B517217 : Blo 428775 517217 := bbase (se 2 (by rfl) ⟨193956, by rfl⟩ : syracuseStep 517217 = 387913) (by norm_num)
theorem B648293 : Blo 428775 648293 := bbase (se 4 (by rfl) ⟨60777, by rfl⟩ : syracuseStep 648293 = 121555) (by norm_num)
theorem B484465 : Blo 428775 484465 := bbase (se 2 (by rfl) ⟨181674, by rfl⟩ : syracuseStep 484465 = 363349) (by norm_num)
theorem B582773 : Blo 428775 582773 := bbase (se 5 (by rfl) ⟨27317, by rfl⟩ : syracuseStep 582773 = 54635) (by norm_num)
theorem B648317 : Blo 428775 648317 := bbase (se 3 (by rfl) ⟨121559, by rfl⟩ : syracuseStep 648317 = 243119) (by norm_num)
theorem B484501 : Blo 428775 484501 := bbase (se 6 (by rfl) ⟨11355, by rfl⟩ : syracuseStep 484501 = 22711) (by norm_num)
theorem B648341 : Blo 428775 648341 := bbase (se 6 (by rfl) ⟨15195, by rfl⟩ : syracuseStep 648341 = 30391) (by norm_num)
theorem B648365 : Blo 428775 648365 := bbase (se 3 (by rfl) ⟨121568, by rfl⟩ : syracuseStep 648365 = 243137) (by norm_num)
theorem B484537 : Blo 428775 484537 := bbase (se 2 (by rfl) ⟨181701, by rfl⟩ : syracuseStep 484537 = 363403) (by norm_num)
theorem B779453 : Blo 428775 779453 := bbase (se 3 (by rfl) ⟨146147, by rfl⟩ : syracuseStep 779453 = 292295) (by norm_num)
theorem B648389 : Blo 428775 648389 := bbase (se 4 (by rfl) ⟨60786, by rfl⟩ : syracuseStep 648389 = 121573) (by norm_num)
theorem B517333 : Blo 428775 517333 := bbase (se 7 (by rfl) ⟨6062, by rfl⟩ : syracuseStep 517333 = 12125) (by norm_num)
theorem B484573 : Blo 428775 484573 := bbase (se 3 (by rfl) ⟨90857, by rfl⟩ : syracuseStep 484573 = 181715) (by norm_num)
theorem B648413 : Blo 428775 648413 := bbase (se 3 (by rfl) ⟨121577, by rfl⟩ : syracuseStep 648413 = 243155) (by norm_num)
theorem B648437 : Blo 428775 648437 := bbase (se 5 (by rfl) ⟨30395, by rfl⟩ : syracuseStep 648437 = 60791) (by norm_num)
theorem B550141 : Blo 428775 550141 := bbase (se 3 (by rfl) ⟨103151, by rfl⟩ : syracuseStep 550141 = 206303) (by norm_num)
theorem B484609 : Blo 428775 484609 := bbase (se 2 (by rfl) ⟨181728, by rfl⟩ : syracuseStep 484609 = 363457) (by norm_num)
theorem B648461 : Blo 428775 648461 := bbase (se 3 (by rfl) ⟨121586, by rfl⟩ : syracuseStep 648461 = 243173) (by norm_num)
theorem B615709 : Blo 428775 615709 := bbase (se 3 (by rfl) ⟨115445, by rfl⟩ : syracuseStep 615709 = 230891) (by norm_num)
theorem B484645 : Blo 428775 484645 := bbase (se 4 (by rfl) ⟨45435, by rfl⟩ : syracuseStep 484645 = 90871) (by norm_num)
theorem B648485 : Blo 428775 648485 := bbase (se 4 (by rfl) ⟨60795, by rfl⟩ : syracuseStep 648485 = 121591) (by norm_num)
theorem B517429 : Blo 428775 517429 := bbase (se 5 (by rfl) ⟨24254, by rfl⟩ : syracuseStep 517429 = 48509) (by norm_num)
theorem B648509 : Blo 428775 648509 := bbase (se 3 (by rfl) ⟨121595, by rfl⟩ : syracuseStep 648509 = 243191) (by norm_num)
theorem B484681 : Blo 428775 484681 := bbase (se 2 (by rfl) ⟨181755, by rfl⟩ : syracuseStep 484681 = 363511) (by norm_num)
theorem B3106133 : Blo 428775 3106133 := bbase (se 12 (by rfl) ⟨1137, by rfl⟩ : syracuseStep 3106133 = 2275) (by norm_num)
theorem B648533 : Blo 428775 648533 := bbase (se 12 (by rfl) ⟨237, by rfl⟩ : syracuseStep 648533 = 475) (by norm_num)
theorem B484717 : Blo 428775 484717 := bbase (se 3 (by rfl) ⟨90884, by rfl⟩ : syracuseStep 484717 = 181769) (by norm_num)
theorem B648557 : Blo 428775 648557 := bbase (se 3 (by rfl) ⟨121604, by rfl⟩ : syracuseStep 648557 = 243209) (by norm_num)
theorem B648581 : Blo 428775 648581 := bbase (se 4 (by rfl) ⟨60804, by rfl⟩ : syracuseStep 648581 = 121609) (by norm_num)
theorem B484753 : Blo 428775 484753 := bbase (se 2 (by rfl) ⟨181782, by rfl⟩ : syracuseStep 484753 = 363565) (by norm_num)
theorem B648605 : Blo 428775 648605 := bbase (se 3 (by rfl) ⟨121613, by rfl⟩ : syracuseStep 648605 = 243227) (by norm_num)
theorem B484789 : Blo 428775 484789 := bbase (se 5 (by rfl) ⟨22724, by rfl⟩ : syracuseStep 484789 = 45449) (by norm_num)
theorem B648629 : Blo 428775 648629 := bbase (se 5 (by rfl) ⟨30404, by rfl⟩ : syracuseStep 648629 = 60809) (by norm_num)
theorem B517573 : Blo 428775 517573 := bbase (se 4 (by rfl) ⟨48522, by rfl⟩ : syracuseStep 517573 = 97045) (by norm_num)
theorem B648653 : Blo 428775 648653 := bbase (se 3 (by rfl) ⟨121622, by rfl⟩ : syracuseStep 648653 = 243245) (by norm_num)
theorem B484825 : Blo 428775 484825 := bbase (se 2 (by rfl) ⟨181809, by rfl⟩ : syracuseStep 484825 = 363619) (by norm_num)
theorem B648677 : Blo 428775 648677 := bbase (se 4 (by rfl) ⟨60813, by rfl⟩ : syracuseStep 648677 = 121627) (by norm_num)
theorem B484861 : Blo 428775 484861 := bbase (se 3 (by rfl) ⟨90911, by rfl⟩ : syracuseStep 484861 = 181823) (by norm_num)
theorem B648701 : Blo 428775 648701 := bbase (se 3 (by rfl) ⟨121631, by rfl⟩ : syracuseStep 648701 = 243263) (by norm_num)
theorem B648725 : Blo 428775 648725 := bbase (se 6 (by rfl) ⟨15204, by rfl⟩ : syracuseStep 648725 = 30409) (by norm_num)
theorem B550433 : Blo 428775 550433 := bbase (se 2 (by rfl) ⟨206412, by rfl⟩ : syracuseStep 550433 = 412825) (by norm_num)
theorem B484897 : Blo 428775 484897 := bbase (se 2 (by rfl) ⟨181836, by rfl⟩ : syracuseStep 484897 = 363673) (by norm_num)
theorem B648749 : Blo 428775 648749 := bbase (se 3 (by rfl) ⟨121640, by rfl⟩ : syracuseStep 648749 = 243281) (by norm_num)
theorem B484933 : Blo 428775 484933 := bbase (se 4 (by rfl) ⟨45462, by rfl⟩ : syracuseStep 484933 = 90925) (by norm_num)
theorem B648773 : Blo 428775 648773 := bbase (se 4 (by rfl) ⟨60822, by rfl⟩ : syracuseStep 648773 = 121645) (by norm_num)
theorem B648797 : Blo 428775 648797 := bbase (se 3 (by rfl) ⟨121649, by rfl⟩ : syracuseStep 648797 = 243299) (by norm_num)
theorem B484969 : Blo 428775 484969 := bbase (se 2 (by rfl) ⟨181863, by rfl⟩ : syracuseStep 484969 = 363727) (by norm_num)
theorem B648821 : Blo 428775 648821 := bbase (se 5 (by rfl) ⟨30413, by rfl⟩ : syracuseStep 648821 = 60827) (by norm_num)
theorem B485005 : Blo 428775 485005 := bbase (se 3 (by rfl) ⟨90938, by rfl⟩ : syracuseStep 485005 = 181877) (by norm_num)
theorem B648845 : Blo 428775 648845 := bbase (se 3 (by rfl) ⟨121658, by rfl⟩ : syracuseStep 648845 = 243317) (by norm_num)
theorem B3270293 : Blo 428775 3270293 := bbase (se 6 (by rfl) ⟨76647, by rfl⟩ : syracuseStep 3270293 = 153295) (by norm_num)
theorem B648869 : Blo 428775 648869 := bbase (se 4 (by rfl) ⟨60831, by rfl⟩ : syracuseStep 648869 = 121663) (by norm_num)
theorem B485041 : Blo 428775 485041 := bbase (se 2 (by rfl) ⟨181890, by rfl⟩ : syracuseStep 485041 = 363781) (by norm_num)
theorem B648893 : Blo 428775 648893 := bbase (se 3 (by rfl) ⟨121667, by rfl⟩ : syracuseStep 648893 = 243335) (by norm_num)
theorem B485077 : Blo 428775 485077 := bbase (se 7 (by rfl) ⟨5684, by rfl⟩ : syracuseStep 485077 = 11369) (by norm_num)
theorem B648917 : Blo 428775 648917 := bbase (se 7 (by rfl) ⟨7604, by rfl⟩ : syracuseStep 648917 = 15209) (by norm_num)
theorem B583405 : Blo 428775 583405 := bbase (se 3 (by rfl) ⟨109388, by rfl⟩ : syracuseStep 583405 = 218777) (by norm_num)
theorem B648941 : Blo 428775 648941 := bbase (se 3 (by rfl) ⟨121676, by rfl⟩ : syracuseStep 648941 = 243353) (by norm_num)
theorem B485113 : Blo 428775 485113 := bbase (se 2 (by rfl) ⟨181917, by rfl⟩ : syracuseStep 485113 = 363835) (by norm_num)
theorem B648965 : Blo 428775 648965 := bbase (se 4 (by rfl) ⟨60840, by rfl⟩ : syracuseStep 648965 = 121681) (by norm_num)
theorem B485149 : Blo 428775 485149 := bbase (se 3 (by rfl) ⟨90965, by rfl⟩ : syracuseStep 485149 = 181931) (by norm_num)
theorem B648989 : Blo 428775 648989 := bbase (se 3 (by rfl) ⟨121685, by rfl⟩ : syracuseStep 648989 = 243371) (by norm_num)
theorem B649013 : Blo 428775 649013 := bbase (se 5 (by rfl) ⟨30422, by rfl⟩ : syracuseStep 649013 = 60845) (by norm_num)
theorem B485185 : Blo 428775 485185 := bbase (se 2 (by rfl) ⟨181944, by rfl⟩ : syracuseStep 485185 = 363889) (by norm_num)
theorem B649037 : Blo 428775 649037 := bbase (se 3 (by rfl) ⟨121694, by rfl⟩ : syracuseStep 649037 = 243389) (by norm_num)
theorem B485221 : Blo 428775 485221 := bbase (se 4 (by rfl) ⟨45489, by rfl⟩ : syracuseStep 485221 = 90979) (by norm_num)
theorem B649061 : Blo 428775 649061 := bbase (se 4 (by rfl) ⟨60849, by rfl⟩ : syracuseStep 649061 = 121699) (by norm_num)
theorem B649085 : Blo 428775 649085 := bbase (se 3 (by rfl) ⟨121703, by rfl⟩ : syracuseStep 649085 = 243407) (by norm_num)
theorem B485257 : Blo 428775 485257 := bbase (se 2 (by rfl) ⟨181971, by rfl⟩ : syracuseStep 485257 = 363943) (by norm_num)
theorem B649109 : Blo 428775 649109 := bbase (se 6 (by rfl) ⟨15213, by rfl⟩ : syracuseStep 649109 = 30427) (by norm_num)
theorem B485293 : Blo 428775 485293 := bbase (se 3 (by rfl) ⟨90992, by rfl⟩ : syracuseStep 485293 = 181985) (by norm_num)
theorem B649133 : Blo 428775 649133 := bbase (se 3 (by rfl) ⟨121712, by rfl⟩ : syracuseStep 649133 = 243425) (by norm_num)
theorem B649157 : Blo 428775 649157 := bbase (se 4 (by rfl) ⟨60858, by rfl⟩ : syracuseStep 649157 = 121717) (by norm_num)
theorem B485329 : Blo 428775 485329 := bbase (se 2 (by rfl) ⟨181998, by rfl⟩ : syracuseStep 485329 = 363997) (by norm_num)
theorem B485365 : Blo 428775 485365 := bbase (se 5 (by rfl) ⟨22751, by rfl⟩ : syracuseStep 485365 = 45503) (by norm_num)
theorem B485401 : Blo 428775 485401 := bbase (se 2 (by rfl) ⟨182025, by rfl⟩ : syracuseStep 485401 = 364051) (by norm_num)
theorem B485437 : Blo 428775 485437 := bbase (se 3 (by rfl) ⟨91019, by rfl⟩ : syracuseStep 485437 = 182039) (by norm_num)
theorem B485473 : Blo 428775 485473 := bbase (se 2 (by rfl) ⟨182052, by rfl⟩ : syracuseStep 485473 = 364105) (by norm_num)
theorem B2189429 : Blo 428775 2189429 := bbase (se 5 (by rfl) ⟨102629, by rfl⟩ : syracuseStep 2189429 = 205259) (by norm_num)
theorem B485509 : Blo 428775 485509 := bbase (se 4 (by rfl) ⟨45516, by rfl⟩ : syracuseStep 485509 = 91033) (by norm_num)
theorem B485545 : Blo 428775 485545 := bbase (se 2 (by rfl) ⟨182079, by rfl⟩ : syracuseStep 485545 = 364159) (by norm_num)
theorem B485581 : Blo 428775 485581 := bbase (se 3 (by rfl) ⟨91046, by rfl⟩ : syracuseStep 485581 = 182093) (by norm_num)
theorem B485617 : Blo 428775 485617 := bbase (se 2 (by rfl) ⟨182106, by rfl⟩ : syracuseStep 485617 = 364213) (by norm_num)
theorem B485653 : Blo 428775 485653 := bbase (se 6 (by rfl) ⟨11382, by rfl⟩ : syracuseStep 485653 = 22765) (by norm_num)
theorem B485689 : Blo 428775 485689 := bbase (se 2 (by rfl) ⟨182133, by rfl⟩ : syracuseStep 485689 = 364267) (by norm_num)
theorem B1632581 : Blo 428775 1632581 := bbase (se 4 (by rfl) ⟨153054, by rfl⟩ : syracuseStep 1632581 = 306109) (by norm_num)
theorem B485725 : Blo 428775 485725 := bbase (se 3 (by rfl) ⟨91073, by rfl⟩ : syracuseStep 485725 = 182147) (by norm_num)
theorem B485761 : Blo 428775 485761 := bbase (se 2 (by rfl) ⟨182160, by rfl⟩ : syracuseStep 485761 = 364321) (by norm_num)
theorem B485797 : Blo 428775 485797 := bbase (se 4 (by rfl) ⟨45543, by rfl⟩ : syracuseStep 485797 = 91087) (by norm_num)
theorem B485833 : Blo 428775 485833 := bbase (se 2 (by rfl) ⟨182187, by rfl⟩ : syracuseStep 485833 = 364375) (by norm_num)
theorem B485869 : Blo 428775 485869 := bbase (se 3 (by rfl) ⟨91100, by rfl⟩ : syracuseStep 485869 = 182201) (by norm_num)
theorem B584173 : Blo 428775 584173 := bbase (se 3 (by rfl) ⟨109532, by rfl⟩ : syracuseStep 584173 = 219065) (by norm_num)
theorem B485905 : Blo 428775 485905 := bbase (se 2 (by rfl) ⟨182214, by rfl⟩ : syracuseStep 485905 = 364429) (by norm_num)
theorem B485941 : Blo 428775 485941 := bbase (se 5 (by rfl) ⟨22778, by rfl⟩ : syracuseStep 485941 = 45557) (by norm_num)
theorem B485977 : Blo 428775 485977 := bbase (se 2 (by rfl) ⟨182241, by rfl⟩ : syracuseStep 485977 = 364483) (by norm_num)
theorem B1632869 : Blo 428775 1632869 := bbase (se 4 (by rfl) ⟨153081, by rfl⟩ : syracuseStep 1632869 = 306163) (by norm_num)
theorem B486013 : Blo 428775 486013 := bbase (se 3 (by rfl) ⟨91127, by rfl⟩ : syracuseStep 486013 = 182255) (by norm_num)
theorem B486049 : Blo 428775 486049 := bbase (se 2 (by rfl) ⟨182268, by rfl⟩ : syracuseStep 486049 = 364537) (by norm_num)
theorem B1108669 : Blo 428775 1108669 := bbase (se 3 (by rfl) ⟨207875, by rfl⟩ : syracuseStep 1108669 = 415751) (by norm_num)
theorem B486085 : Blo 428775 486085 := bbase (se 4 (by rfl) ⟨45570, by rfl⟩ : syracuseStep 486085 = 91141) (by norm_num)
theorem B486121 : Blo 428775 486121 := bbase (se 2 (by rfl) ⟨182295, by rfl⟩ : syracuseStep 486121 = 364591) (by norm_num)
theorem B486157 : Blo 428775 486157 := bbase (se 3 (by rfl) ⟨91154, by rfl⟩ : syracuseStep 486157 = 182309) (by norm_num)
theorem B486193 : Blo 428775 486193 := bbase (se 2 (by rfl) ⟨182322, by rfl⟩ : syracuseStep 486193 = 364645) (by norm_num)
theorem B486229 : Blo 428775 486229 := bbase (se 9 (by rfl) ⟨1424, by rfl⟩ : syracuseStep 486229 = 2849) (by norm_num)
theorem B486265 : Blo 428775 486265 := bbase (se 2 (by rfl) ⟨182349, by rfl⟩ : syracuseStep 486265 = 364699) (by norm_num)
theorem B486301 : Blo 428775 486301 := bbase (se 3 (by rfl) ⟨91181, by rfl⟩ : syracuseStep 486301 = 182363) (by norm_num)
theorem B2747317 : Blo 428775 2747317 := bbase (se 5 (by rfl) ⟨128780, by rfl⟩ : syracuseStep 2747317 = 257561) (by norm_num)
theorem B486337 : Blo 428775 486337 := bbase (se 2 (by rfl) ⟨182376, by rfl⟩ : syracuseStep 486337 = 364753) (by norm_num)
theorem B9989077 : Blo 428775 9989077 := bbase (se 7 (by rfl) ⟨117059, by rfl⟩ : syracuseStep 9989077 = 234119) (by norm_num)
theorem B486373 : Blo 428775 486373 := bbase (se 4 (by rfl) ⟨45597, by rfl⟩ : syracuseStep 486373 = 91195) (by norm_num)
theorem B486409 : Blo 428775 486409 := bbase (se 2 (by rfl) ⟨182403, by rfl⟩ : syracuseStep 486409 = 364807) (by norm_num)
theorem B486445 : Blo 428775 486445 := bbase (se 3 (by rfl) ⟨91208, by rfl⟩ : syracuseStep 486445 = 182417) (by norm_num)
theorem B814141 : Blo 428775 814141 := bbase (se 3 (by rfl) ⟨152651, by rfl⟩ : syracuseStep 814141 = 305303) (by norm_num)
theorem B486481 : Blo 428775 486481 := bbase (se 2 (by rfl) ⟨182430, by rfl⟩ : syracuseStep 486481 = 364861) (by norm_num)
theorem B1567829 : Blo 428775 1567829 := bbase (se 8 (by rfl) ⟨9186, by rfl⟩ : syracuseStep 1567829 = 18373) (by norm_num)
theorem B486517 : Blo 428775 486517 := bbase (se 5 (by rfl) ⟨22805, by rfl⟩ : syracuseStep 486517 = 45611) (by norm_num)
theorem B519293 : Blo 428775 519293 := bbase (se 3 (by rfl) ⟨97367, by rfl⟩ : syracuseStep 519293 = 194735) (by norm_num)
theorem B486553 : Blo 428775 486553 := bbase (se 2 (by rfl) ⟨182457, by rfl⟩ : syracuseStep 486553 = 364915) (by norm_num)
theorem B486589 : Blo 428775 486589 := bbase (se 3 (by rfl) ⟨91235, by rfl⟩ : syracuseStep 486589 = 182471) (by norm_num)
theorem B486625 : Blo 428775 486625 := bbase (se 2 (by rfl) ⟨182484, by rfl⟩ : syracuseStep 486625 = 364969) (by norm_num)
theorem B519409 : Blo 428775 519409 := bbase (se 2 (by rfl) ⟨194778, by rfl⟩ : syracuseStep 519409 = 389557) (by norm_num)
theorem B486661 : Blo 428775 486661 := bbase (se 4 (by rfl) ⟨45624, by rfl⟩ : syracuseStep 486661 = 91249) (by norm_num)
theorem B1109285 : Blo 428775 1109285 := bbase (se 4 (by rfl) ⟨103995, by rfl⟩ : syracuseStep 1109285 = 207991) (by norm_num)
theorem B486697 : Blo 428775 486697 := bbase (se 2 (by rfl) ⟨182511, by rfl⟩ : syracuseStep 486697 = 365023) (by norm_num)
theorem B519481 : Blo 428775 519481 := bbase (se 2 (by rfl) ⟨194805, by rfl⟩ : syracuseStep 519481 = 389611) (by norm_num)
theorem B486733 : Blo 428775 486733 := bbase (se 3 (by rfl) ⟨91262, by rfl⟩ : syracuseStep 486733 = 182525) (by norm_num)
theorem B814445 : Blo 428775 814445 := bbase (se 3 (by rfl) ⟨152708, by rfl⟩ : syracuseStep 814445 = 305417) (by norm_num)
theorem B486769 : Blo 428775 486769 := bbase (se 2 (by rfl) ⟨182538, by rfl⟩ : syracuseStep 486769 = 365077) (by norm_num)
theorem B2190725 : Blo 428775 2190725 := bbase (se 4 (by rfl) ⟨205380, by rfl⟩ : syracuseStep 2190725 = 410761) (by norm_num)
theorem B486805 : Blo 428775 486805 := bbase (se 6 (by rfl) ⟨11409, by rfl⟩ : syracuseStep 486805 = 22819) (by norm_num)
theorem B519601 : Blo 428775 519601 := bbase (se 2 (by rfl) ⟨194850, by rfl⟩ : syracuseStep 519601 = 389701) (by norm_num)
theorem B486841 : Blo 428775 486841 := bbase (se 2 (by rfl) ⟨182565, by rfl⟩ : syracuseStep 486841 = 365131) (by norm_num)
theorem B2452949 : Blo 428775 2452949 := bbase (se 7 (by rfl) ⟨28745, by rfl⟩ : syracuseStep 2452949 = 57491) (by norm_num)
theorem B2321941 : Blo 428775 2321941 := bbase (se 6 (by rfl) ⟨54420, by rfl⟩ : syracuseStep 2321941 = 108841) (by norm_num)
theorem B1634053 : Blo 428775 1634053 := bbase (se 4 (by rfl) ⟨153192, by rfl⟩ : syracuseStep 1634053 = 306385) (by norm_num)
theorem B3927989 : Blo 428775 3927989 := bbase (se 5 (by rfl) ⟨184124, by rfl⟩ : syracuseStep 3927989 = 368249) (by norm_num)
theorem B1634357 : Blo 428775 1634357 := bbase (se 5 (by rfl) ⟨76610, by rfl⟩ : syracuseStep 1634357 = 153221) (by norm_num)
theorem B815197 : Blo 428775 815197 := bbase (se 3 (by rfl) ⟨152849, by rfl⟩ : syracuseStep 815197 = 305699) (by norm_num)
theorem B815341 : Blo 428775 815341 := bbase (se 3 (by rfl) ⟨152876, by rfl⟩ : syracuseStep 815341 = 305753) (by norm_num)
theorem B2060549 : Blo 428775 2060549 := bbase (se 4 (by rfl) ⟨193176, by rfl⟩ : syracuseStep 2060549 = 386353) (by norm_num)
theorem B553225 : Blo 428775 553225 := bbase (se 2 (by rfl) ⟨207459, by rfl⟩ : syracuseStep 553225 = 414919) (by norm_num)
theorem B815501 : Blo 428775 815501 := bbase (se 3 (by rfl) ⟨152906, by rfl⟩ : syracuseStep 815501 = 305813) (by norm_num)
theorem B1470997 : Blo 428775 1470997 := bbase (se 6 (by rfl) ⟨34476, by rfl⟩ : syracuseStep 1470997 = 68953) (by norm_num)
theorem B815645 : Blo 428775 815645 := bbase (se 3 (by rfl) ⟨152933, by rfl⟩ : syracuseStep 815645 = 305867) (by norm_num)
theorem B815933 : Blo 428775 815933 := bbase (se 3 (by rfl) ⟨152987, by rfl⟩ : syracuseStep 815933 = 305975) (by norm_num)
theorem B5665621 : Blo 428775 5665621 := bbase (se 9 (by rfl) ⟨16598, by rfl⟩ : syracuseStep 5665621 = 33197) (by norm_num)
theorem B816085 : Blo 428775 816085 := bbase (se 7 (by rfl) ⟨9563, by rfl⟩ : syracuseStep 816085 = 19127) (by norm_num)
theorem B816389 : Blo 428775 816389 := bbase (se 4 (by rfl) ⟨76536, by rfl⟩ : syracuseStep 816389 = 153073) (by norm_num)
theorem B1373813 : Blo 428775 1373813 := bbase (se 5 (by rfl) ⟨64397, by rfl⟩ : syracuseStep 1373813 = 128795) (by norm_num)
theorem B980957 : Blo 428775 980957 := bbase (se 3 (by rfl) ⟨183929, by rfl⟩ : syracuseStep 980957 = 367859) (by norm_num)
theorem B817141 : Blo 428775 817141 := bbase (se 5 (by rfl) ⟨38303, by rfl⟩ : syracuseStep 817141 = 76607) (by norm_num)
theorem B587837 : Blo 428775 587837 := bbase (se 3 (by rfl) ⟨110219, by rfl⟩ : syracuseStep 587837 = 220439) (by norm_num)
theorem B1964101 : Blo 428775 1964101 := bbase (se 4 (by rfl) ⟨184134, by rfl⟩ : syracuseStep 1964101 = 368269) (by norm_num)
theorem B1636469 : Blo 428775 1636469 := bbase (se 5 (by rfl) ⟨76709, by rfl⟩ : syracuseStep 1636469 = 153419) (by norm_num)
theorem B817285 : Blo 428775 817285 := bbase (se 4 (by rfl) ⟨76620, by rfl⟩ : syracuseStep 817285 = 153241) (by norm_num)
theorem B489649 : Blo 428775 489649 := bbase (se 2 (by rfl) ⟨183618, by rfl⟩ : syracuseStep 489649 = 367237) (by norm_num)
theorem B653509 : Blo 428775 653509 := bbase (se 4 (by rfl) ⟨61266, by rfl⟩ : syracuseStep 653509 = 122533) (by norm_num)
theorem B489685 : Blo 428775 489685 := bbase (se 7 (by rfl) ⟨5738, by rfl⟩ : syracuseStep 489685 = 11477) (by norm_num)
theorem B555241 : Blo 428775 555241 := bbase (se 2 (by rfl) ⟨208215, by rfl⟩ : syracuseStep 555241 = 416431) (by norm_num)
theorem B522517 : Blo 428775 522517 := bbase (se 6 (by rfl) ⟨12246, by rfl⟩ : syracuseStep 522517 = 24493) (by norm_num)
theorem B620821 : Blo 428775 620821 := bbase (se 6 (by rfl) ⟨14550, by rfl⟩ : syracuseStep 620821 = 29101) (by norm_num)
theorem B817445 : Blo 428775 817445 := bbase (se 4 (by rfl) ⟨76635, by rfl⟩ : syracuseStep 817445 = 153271) (by norm_num)
theorem B1636757 : Blo 428775 1636757 := bbase (se 6 (by rfl) ⟨38361, by rfl⟩ : syracuseStep 1636757 = 76723) (by norm_num)
theorem B817589 : Blo 428775 817589 := bbase (se 5 (by rfl) ⟨38324, by rfl⟩ : syracuseStep 817589 = 76649) (by norm_num)
theorem B981533 : Blo 428775 981533 := bbase (se 3 (by rfl) ⟨184037, by rfl⟩ : syracuseStep 981533 = 368075) (by norm_num)
theorem B981613 : Blo 428775 981613 := bbase (se 3 (by rfl) ⟨184052, by rfl⟩ : syracuseStep 981613 = 368105) (by norm_num)
theorem B817877 : Blo 428775 817877 := bbase (se 7 (by rfl) ⟨9584, by rfl⟩ : syracuseStep 817877 = 19169) (by norm_num)
theorem B6224597 : Blo 428775 6224597 := bbase (se 7 (by rfl) ⟨72944, by rfl⟩ : syracuseStep 6224597 = 145889) (by norm_num)
theorem B1178389 : Blo 428775 1178389 := bbase (se 6 (by rfl) ⟨27618, by rfl⟩ : syracuseStep 1178389 = 55237) (by norm_num)
theorem B916285 : Blo 428775 916285 := bbase (se 3 (by rfl) ⟨171803, by rfl⟩ : syracuseStep 916285 = 343607) (by norm_num)
theorem B523105 : Blo 428775 523105 := bbase (se 2 (by rfl) ⟨196164, by rfl⟩ : syracuseStep 523105 = 392329) (by norm_num)
theorem B818029 : Blo 428775 818029 := bbase (se 3 (by rfl) ⟨153380, by rfl⟩ : syracuseStep 818029 = 306761) (by norm_num)
theorem B2063333 : Blo 428775 2063333 := bbase (se 4 (by rfl) ⟨193437, by rfl⟩ : syracuseStep 2063333 = 386875) (by norm_num)
theorem B687125 : Blo 428775 687125 := bbase (se 6 (by rfl) ⟨16104, by rfl⟩ : syracuseStep 687125 = 32209) (by norm_num)
theorem B818333 : Blo 428775 818333 := bbase (se 3 (by rfl) ⟨153437, by rfl⟩ : syracuseStep 818333 = 306875) (by norm_num)
theorem B1965269 : Blo 428775 1965269 := bbase (se 7 (by rfl) ⟨23030, by rfl⟩ : syracuseStep 1965269 = 46061) (by norm_num)
theorem B687413 : Blo 428775 687413 := bbase (se 5 (by rfl) ⟨32222, by rfl⟩ : syracuseStep 687413 = 64445) (by norm_num)
theorem B458173 : Blo 428775 458173 := bbase (se 3 (by rfl) ⟨85907, by rfl⟩ : syracuseStep 458173 = 171815) (by norm_num)
theorem B458245 : Blo 428775 458245 := bbase (se 4 (by rfl) ⟨42960, by rfl⟩ : syracuseStep 458245 = 85921) (by norm_num)
theorem B687637 : Blo 428775 687637 := bbase (se 6 (by rfl) ⟨16116, by rfl⟩ : syracuseStep 687637 = 32233) (by norm_num)
theorem B1637941 : Blo 428775 1637941 := bbase (se 5 (by rfl) ⟨76778, by rfl⟩ : syracuseStep 1637941 = 153557) (by norm_num)
theorem B917173 : Blo 428775 917173 := bbase (se 5 (by rfl) ⟨42992, by rfl⟩ : syracuseStep 917173 = 85985) (by norm_num)
theorem B1834757 : Blo 428775 1834757 := bbase (se 4 (by rfl) ⟨172008, by rfl⟩ : syracuseStep 1834757 = 344017) (by norm_num)
theorem B655133 : Blo 428775 655133 := bbase (se 3 (by rfl) ⟨122837, by rfl⟩ : syracuseStep 655133 = 245675) (by norm_num)
theorem B1638245 : Blo 428775 1638245 := bbase (se 4 (by rfl) ⟨153585, by rfl⟩ : syracuseStep 1638245 = 307171) (by norm_num)
theorem B458617 : Blo 428775 458617 := bbase (se 2 (by rfl) ⟨171981, by rfl⟩ : syracuseStep 458617 = 343963) (by norm_num)
theorem B819085 : Blo 428775 819085 := bbase (se 3 (by rfl) ⟨153578, by rfl⟩ : syracuseStep 819085 = 307157) (by norm_num)
theorem B2326421 : Blo 428775 2326421 := bbase (se 6 (by rfl) ⟨54525, by rfl⟩ : syracuseStep 2326421 = 109051) (by norm_num)
theorem B655285 : Blo 428775 655285 := bbase (se 5 (by rfl) ⟨30716, by rfl⟩ : syracuseStep 655285 = 61433) (by norm_num)
theorem B917507 : Blo 428775 917507 := bstep (se 1 (by rfl) ⟨688130, by rfl⟩ : syracuseStep 917507 = 1376261) B1376261
theorem B1638413 : Blo 428775 1638413 := bstep (se 3 (by rfl) ⟨307202, by rfl⟩ : syracuseStep 1638413 = 614405) B614405
theorem B1376273 : Blo 428775 1376273 := bstep (se 2 (by rfl) ⟨516102, by rfl⟩ : syracuseStep 1376273 = 1032205) B1032205
theorem B1572941 : Blo 428775 1572941 := bstep (se 3 (by rfl) ⟨294926, by rfl⟩ : syracuseStep 1572941 = 589853) B589853
theorem B688355 : Blo 428775 688355 := bstep (se 1 (by rfl) ⟨516266, by rfl⟩ : syracuseStep 688355 = 1032533) B1032533
theorem B688547 : Blo 428775 688547 := bstep (se 1 (by rfl) ⟨516410, by rfl⟩ : syracuseStep 688547 = 1032821) B1032821
theorem B1180145 : Blo 428775 1180145 := bstep (se 2 (by rfl) ⟨442554, by rfl⟩ : syracuseStep 1180145 = 885109) B885109
theorem B2458097 : Blo 428775 2458097 := bstep (se 2 (by rfl) ⟨921786, by rfl⟩ : syracuseStep 2458097 = 1843573) B1843573
theorem B819715 : Blo 428775 819715 := bstep (se 1 (by rfl) ⟨614786, by rfl⟩ : syracuseStep 819715 = 1229573) B1229573
theorem B1376785 : Blo 428775 1376785 := bstep (se 2 (by rfl) ⟨516294, by rfl⟩ : syracuseStep 1376785 = 1032589) B1032589
theorem B688675 : Blo 428775 688675 := bstep (se 1 (by rfl) ⟨516506, by rfl⟩ : syracuseStep 688675 = 1033013) B1033013
theorem B1475185 : Blo 428775 1475185 := bstep (se 2 (by rfl) ⟨553194, by rfl⟩ : syracuseStep 1475185 = 1106389) B1106389
theorem B819875 : Blo 428775 819875 := bstep (se 1 (by rfl) ⟨614906, by rfl⟩ : syracuseStep 819875 = 1229813) B1229813
theorem B459475 : Blo 428775 459475 := bstep (se 1 (by rfl) ⟨344606, by rfl⟩ : syracuseStep 459475 = 689213) B689213
theorem B3113741 : Blo 428775 3113741 := bstep (se 3 (by rfl) ⟨583826, by rfl⟩ : syracuseStep 3113741 = 1167653) B1167653
theorem B1639217 : Blo 428775 1639217 := bstep (se 2 (by rfl) ⟨614706, by rfl⟩ : syracuseStep 1639217 = 1229413) B1229413
theorem B918353 : Blo 428775 918353 := bstep (se 2 (by rfl) ⟨344382, by rfl⟩ : syracuseStep 918353 = 688765) B688765
theorem B19104709 : Blo 428775 19104709 := bstep (se 4 (by rfl) ⟨1791066, by rfl⟩ : syracuseStep 19104709 = 3582133) B3582133
theorem B656417 : Blo 428775 656417 := bstep (se 2 (by rfl) ⟨246156, by rfl⟩ : syracuseStep 656417 = 492313) B492313
theorem B3671153 : Blo 428775 3671153 := bstep (se 2 (by rfl) ⟨1376682, by rfl⟩ : syracuseStep 3671153 = 2753365) B2753365
theorem B689315 : Blo 428775 689315 := bstep (se 1 (by rfl) ⟨516986, by rfl⟩ : syracuseStep 689315 = 1033973) B1033973
theorem B7013573 : Blo 428775 7013573 := bstep (se 4 (by rfl) ⟨657522, by rfl⟩ : syracuseStep 7013573 = 1315045) B1315045
theorem B689393 : Blo 428775 689393 := bstep (se 2 (by rfl) ⟨258522, by rfl⟩ : syracuseStep 689393 = 517045) B517045
theorem B492851 : Blo 428775 492851 := bstep (se 1 (by rfl) ⟨369638, by rfl⟩ : syracuseStep 492851 = 739277) B739277
theorem B624019 : Blo 428775 624019 := bstep (se 1 (by rfl) ⟨468014, by rfl⟩ : syracuseStep 624019 = 936029) B936029
theorem B1639885 : Blo 428775 1639885 := bstep (se 3 (by rfl) ⟨307478, by rfl⟩ : syracuseStep 1639885 = 614957) B614957
theorem B1377901 : Blo 428775 1377901 := bstep (se 3 (by rfl) ⟨258356, by rfl⟩ : syracuseStep 1377901 = 516713) B516713
theorem B689777 : Blo 428775 689777 := bstep (se 2 (by rfl) ⟨258666, by rfl⟩ : syracuseStep 689777 = 517333) B517333
theorem B1377965 : Blo 428775 1377965 := bstep (se 3 (by rfl) ⟨258368, by rfl⟩ : syracuseStep 1377965 = 516737) B516737
theorem B820945 : Blo 428775 820945 := bstep (se 2 (by rfl) ⟨307854, by rfl⟩ : syracuseStep 820945 = 615709) B615709
theorem B7374563 : Blo 428775 7374563 := bstep (se 1 (by rfl) ⟨5530922, by rfl⟩ : syracuseStep 7374563 = 11061845) B11061845
theorem B689905 : Blo 428775 689905 := bstep (se 2 (by rfl) ⟨258714, by rfl⟩ : syracuseStep 689905 = 517429) B517429
theorem B2459555 : Blo 428775 2459555 := bstep (se 1 (by rfl) ⟨1844666, by rfl⟩ : syracuseStep 2459555 = 3689333) B3689333
theorem B2328689 : Blo 428775 2328689 := bstep (se 2 (by rfl) ⟨873258, by rfl⟩ : syracuseStep 2328689 = 1746517) B1746517
theorem B1640675 : Blo 428775 1640675 := bstep (se 1 (by rfl) ⟨1230506, by rfl⟩ : syracuseStep 1640675 = 2461013) B2461013
theorem B7473521 : Blo 428775 7473521 := bstep (se 2 (by rfl) ⟨2802570, by rfl⟩ : syracuseStep 7473521 = 5605141) B5605141
theorem B788867 : Blo 428775 788867 := bstep (se 1 (by rfl) ⟨591650, by rfl⟩ : syracuseStep 788867 = 1183301) B1183301
theorem B1837475 : Blo 428775 1837475 := bstep (se 1 (by rfl) ⟨1378106, by rfl⟩ : syracuseStep 1837475 = 2756213) B2756213
theorem B723667 : Blo 428775 723667 := bstep (se 1 (by rfl) ⟨542750, by rfl⟩ : syracuseStep 723667 = 1085501) B1085501
theorem B428787 : Blo 428775 428787 := bstep (se 1 (by rfl) ⟨321590, by rfl⟩ : syracuseStep 428787 = 643181) B643181
theorem B428803 : Blo 428775 428803 := bstep (se 1 (by rfl) ⟨321602, by rfl⟩ : syracuseStep 428803 = 643205) B643205
theorem B428819 : Blo 428775 428819 := bstep (se 1 (by rfl) ⟨321614, by rfl⟩ : syracuseStep 428819 = 643229) B643229
theorem B428835 : Blo 428775 428835 := bstep (se 1 (by rfl) ⟨321626, by rfl⟩ : syracuseStep 428835 = 643253) B643253
theorem B428851 : Blo 428775 428851 := bstep (se 1 (by rfl) ⟨321638, by rfl⟩ : syracuseStep 428851 = 643277) B643277
theorem B428867 : Blo 428775 428867 := bstep (se 1 (by rfl) ⟨321650, by rfl⟩ : syracuseStep 428867 = 643301) B643301
theorem B789329 : Blo 428775 789329 := bstep (se 2 (by rfl) ⟨295998, by rfl⟩ : syracuseStep 789329 = 591997) B591997
theorem B428883 : Blo 428775 428883 := bstep (se 1 (by rfl) ⟨321662, by rfl⟩ : syracuseStep 428883 = 643325) B643325
theorem B723809 : Blo 428775 723809 := bstep (se 2 (by rfl) ⟨271428, by rfl⟩ : syracuseStep 723809 = 542857) B542857
theorem B428899 : Blo 428775 428899 := bstep (se 1 (by rfl) ⟨321674, by rfl⟩ : syracuseStep 428899 = 643349) B643349
theorem B1641329 : Blo 428775 1641329 := bstep (se 2 (by rfl) ⟨615498, by rfl⟩ : syracuseStep 1641329 = 1230997) B1230997
theorem B428915 : Blo 428775 428915 := bstep (se 1 (by rfl) ⟨321686, by rfl⟩ : syracuseStep 428915 = 643373) B643373
theorem B428931 : Blo 428775 428931 := bstep (se 1 (by rfl) ⟨321698, by rfl⟩ : syracuseStep 428931 = 643397) B643397
theorem B2460557 : Blo 428775 2460557 := bstep (se 3 (by rfl) ⟨461354, by rfl⟩ : syracuseStep 2460557 = 922709) B922709
theorem B428947 : Blo 428775 428947 := bstep (se 1 (by rfl) ⟨321710, by rfl⟩ : syracuseStep 428947 = 643421) B643421
theorem B428963 : Blo 428775 428963 := bstep (se 1 (by rfl) ⟨321722, by rfl⟩ : syracuseStep 428963 = 643445) B643445
theorem B428979 : Blo 428775 428979 := bstep (se 1 (by rfl) ⟨321734, by rfl⟩ : syracuseStep 428979 = 643469) B643469
theorem B428995 : Blo 428775 428995 := bstep (se 1 (by rfl) ⟨321746, by rfl⟩ : syracuseStep 428995 = 643493) B643493
theorem B429011 : Blo 428775 429011 := bstep (se 1 (by rfl) ⟨321758, by rfl⟩ : syracuseStep 429011 = 643517) B643517
theorem B723937 : Blo 428775 723937 := bstep (se 2 (by rfl) ⟨271476, by rfl⟩ : syracuseStep 723937 = 542953) B542953
theorem B429027 : Blo 428775 429027 := bstep (se 1 (by rfl) ⟨321770, by rfl⟩ : syracuseStep 429027 = 643541) B643541
theorem B429043 : Blo 428775 429043 := bstep (se 1 (by rfl) ⟨321782, by rfl⟩ : syracuseStep 429043 = 643565) B643565
theorem B723971 : Blo 428775 723971 := bstep (se 1 (by rfl) ⟨542978, by rfl⟩ : syracuseStep 723971 = 1085957) B1085957
theorem B429059 : Blo 428775 429059 := bstep (se 1 (by rfl) ⟨321794, by rfl⟩ : syracuseStep 429059 = 643589) B643589
theorem B429075 : Blo 428775 429075 := bstep (se 1 (by rfl) ⟨321806, by rfl⟩ : syracuseStep 429075 = 643613) B643613
theorem B429091 : Blo 428775 429091 := bstep (se 1 (by rfl) ⟨321818, by rfl⟩ : syracuseStep 429091 = 643637) B643637
theorem B429107 : Blo 428775 429107 := bstep (se 1 (by rfl) ⟨321830, by rfl⟩ : syracuseStep 429107 = 643661) B643661
theorem B429123 : Blo 428775 429123 := bstep (se 1 (by rfl) ⟨321842, by rfl⟩ : syracuseStep 429123 = 643685) B643685
theorem B429139 : Blo 428775 429139 := bstep (se 1 (by rfl) ⟨321854, by rfl⟩ : syracuseStep 429139 = 643709) B643709
theorem B429155 : Blo 428775 429155 := bstep (se 1 (by rfl) ⟨321866, by rfl⟩ : syracuseStep 429155 = 643733) B643733
theorem B429171 : Blo 428775 429171 := bstep (se 1 (by rfl) ⟨321878, by rfl⟩ : syracuseStep 429171 = 643757) B643757
theorem B724099 : Blo 428775 724099 := bstep (se 1 (by rfl) ⟨543074, by rfl⟩ : syracuseStep 724099 = 1086149) B1086149
theorem B429187 : Blo 428775 429187 := bstep (se 1 (by rfl) ⟨321890, by rfl⟩ : syracuseStep 429187 = 643781) B643781
theorem B3280013 : Blo 428775 3280013 := bstep (se 3 (by rfl) ⟨615002, by rfl⟩ : syracuseStep 3280013 = 1230005) B1230005
theorem B429203 : Blo 428775 429203 := bstep (se 1 (by rfl) ⟨321902, by rfl⟩ : syracuseStep 429203 = 643805) B643805
theorem B429219 : Blo 428775 429219 := bstep (se 1 (by rfl) ⟨321914, by rfl⟩ : syracuseStep 429219 = 643829) B643829
theorem B429235 : Blo 428775 429235 := bstep (se 1 (by rfl) ⟨321926, by rfl⟩ : syracuseStep 429235 = 643853) B643853
theorem B429251 : Blo 428775 429251 := bstep (se 1 (by rfl) ⟨321938, by rfl⟩ : syracuseStep 429251 = 643877) B643877
theorem B429267 : Blo 428775 429267 := bstep (se 1 (by rfl) ⟨321950, by rfl⟩ : syracuseStep 429267 = 643901) B643901
theorem B691411 : Blo 428775 691411 := bstep (se 1 (by rfl) ⟨518558, by rfl⟩ : syracuseStep 691411 = 1037117) B1037117
theorem B429283 : Blo 428775 429283 := bstep (se 1 (by rfl) ⟨321962, by rfl⟩ : syracuseStep 429283 = 643925) B643925
theorem B5508323 : Blo 428775 5508323 := bstep (se 1 (by rfl) ⟨4131242, by rfl⟩ : syracuseStep 5508323 = 8262485) B8262485
theorem B429299 : Blo 428775 429299 := bstep (se 1 (by rfl) ⟨321974, by rfl⟩ : syracuseStep 429299 = 643949) B643949
theorem B429315 : Blo 428775 429315 := bstep (se 1 (by rfl) ⟨321986, by rfl⟩ : syracuseStep 429315 = 643973) B643973
theorem B724241 : Blo 428775 724241 := bstep (se 2 (by rfl) ⟨271590, by rfl⟩ : syracuseStep 724241 = 543181) B543181
theorem B429331 : Blo 428775 429331 := bstep (se 1 (by rfl) ⟨321998, by rfl⟩ : syracuseStep 429331 = 643997) B643997
theorem B429347 : Blo 428775 429347 := bstep (se 1 (by rfl) ⟨322010, by rfl⟩ : syracuseStep 429347 = 644021) B644021
theorem B462115 : Blo 428775 462115 := bstep (se 1 (by rfl) ⟨346586, by rfl⟩ : syracuseStep 462115 = 693173) B693173
theorem B429363 : Blo 428775 429363 := bstep (se 1 (by rfl) ⟨322022, by rfl⟩ : syracuseStep 429363 = 644045) B644045
theorem B429379 : Blo 428775 429379 := bstep (se 1 (by rfl) ⟨322034, by rfl⟩ : syracuseStep 429379 = 644069) B644069
theorem B429395 : Blo 428775 429395 := bstep (se 1 (by rfl) ⟨322046, by rfl⟩ : syracuseStep 429395 = 644093) B644093
theorem B429411 : Blo 428775 429411 := bstep (se 1 (by rfl) ⟨322058, by rfl⟩ : syracuseStep 429411 = 644117) B644117
theorem B429427 : Blo 428775 429427 := bstep (se 1 (by rfl) ⟨322070, by rfl⟩ : syracuseStep 429427 = 644141) B644141
theorem B429443 : Blo 428775 429443 := bstep (se 1 (by rfl) ⟨322082, by rfl⟩ : syracuseStep 429443 = 644165) B644165
theorem B724369 : Blo 428775 724369 := bstep (se 2 (by rfl) ⟨271638, by rfl⟩ : syracuseStep 724369 = 543277) B543277
theorem B429459 : Blo 428775 429459 := bstep (se 1 (by rfl) ⟨322094, by rfl⟩ : syracuseStep 429459 = 644189) B644189
theorem B429475 : Blo 428775 429475 := bstep (se 1 (by rfl) ⟨322106, by rfl⟩ : syracuseStep 429475 = 644213) B644213
theorem B1379747 : Blo 428775 1379747 := bstep (se 1 (by rfl) ⟨1034810, by rfl⟩ : syracuseStep 1379747 = 2069621) B2069621
theorem B724403 : Blo 428775 724403 := bstep (se 1 (by rfl) ⟨543302, by rfl⟩ : syracuseStep 724403 = 1086605) B1086605
theorem B429491 : Blo 428775 429491 := bstep (se 1 (by rfl) ⟨322118, by rfl⟩ : syracuseStep 429491 = 644237) B644237
theorem B429507 : Blo 428775 429507 := bstep (se 1 (by rfl) ⟨322130, by rfl⟩ : syracuseStep 429507 = 644261) B644261
theorem B429523 : Blo 428775 429523 := bstep (se 1 (by rfl) ⟨322142, by rfl⟩ : syracuseStep 429523 = 644285) B644285
theorem B429539 : Blo 428775 429539 := bstep (se 1 (by rfl) ⟨322154, by rfl⟩ : syracuseStep 429539 = 644309) B644309
theorem B429555 : Blo 428775 429555 := bstep (se 1 (by rfl) ⟨322166, by rfl⟩ : syracuseStep 429555 = 644333) B644333
theorem B429571 : Blo 428775 429571 := bstep (se 1 (by rfl) ⟨322178, by rfl⟩ : syracuseStep 429571 = 644357) B644357
theorem B3673613 : Blo 428775 3673613 := bstep (se 3 (by rfl) ⟨688802, by rfl⟩ : syracuseStep 3673613 = 1377605) B1377605
theorem B429587 : Blo 428775 429587 := bstep (se 1 (by rfl) ⟨322190, by rfl⟩ : syracuseStep 429587 = 644381) B644381
theorem B429603 : Blo 428775 429603 := bstep (se 1 (by rfl) ⟨322202, by rfl⟩ : syracuseStep 429603 = 644405) B644405
theorem B921137 : Blo 428775 921137 := bstep (se 2 (by rfl) ⟨345426, by rfl⟩ : syracuseStep 921137 = 690853) B690853
theorem B1314353 : Blo 428775 1314353 := bstep (se 2 (by rfl) ⟨492882, by rfl⟩ : syracuseStep 1314353 = 985765) B985765
theorem B724531 : Blo 428775 724531 := bstep (se 1 (by rfl) ⟨543398, by rfl⟩ : syracuseStep 724531 = 1086797) B1086797
theorem B429619 : Blo 428775 429619 := bstep (se 1 (by rfl) ⟨322214, by rfl⟩ : syracuseStep 429619 = 644429) B644429
theorem B429635 : Blo 428775 429635 := bstep (se 1 (by rfl) ⟨322226, by rfl⟩ : syracuseStep 429635 = 644453) B644453
theorem B1478225 : Blo 428775 1478225 := bstep (se 2 (by rfl) ⟨554334, by rfl⟩ : syracuseStep 1478225 = 1108669) B1108669
theorem B429651 : Blo 428775 429651 := bstep (se 1 (by rfl) ⟨322238, by rfl⟩ : syracuseStep 429651 = 644477) B644477
theorem B429667 : Blo 428775 429667 := bstep (se 1 (by rfl) ⟨322250, by rfl⟩ : syracuseStep 429667 = 644501) B644501
theorem B3116657 : Blo 428775 3116657 := bstep (se 2 (by rfl) ⟨1168746, by rfl⟩ : syracuseStep 3116657 = 2337493) B2337493
theorem B429683 : Blo 428775 429683 := bstep (se 1 (by rfl) ⟨322262, by rfl⟩ : syracuseStep 429683 = 644525) B644525
theorem B429699 : Blo 428775 429699 := bstep (se 1 (by rfl) ⟨322274, by rfl⟩ : syracuseStep 429699 = 644549) B644549
theorem B2330245 : Blo 428775 2330245 := bstep (se 4 (by rfl) ⟨218460, by rfl⟩ : syracuseStep 2330245 = 436921) B436921
theorem B429715 : Blo 428775 429715 := bstep (se 1 (by rfl) ⟨322286, by rfl⟩ : syracuseStep 429715 = 644573) B644573
theorem B429731 : Blo 428775 429731 := bstep (se 1 (by rfl) ⟨322298, by rfl⟩ : syracuseStep 429731 = 644597) B644597
theorem B429747 : Blo 428775 429747 := bstep (se 1 (by rfl) ⟨322310, by rfl⟩ : syracuseStep 429747 = 644621) B644621
theorem B724673 : Blo 428775 724673 := bstep (se 2 (by rfl) ⟨271752, by rfl⟩ : syracuseStep 724673 = 543505) B543505
theorem B429763 : Blo 428775 429763 := bstep (se 1 (by rfl) ⟨322322, by rfl⟩ : syracuseStep 429763 = 644645) B644645
theorem B986833 : Blo 428775 986833 := bstep (se 2 (by rfl) ⟨370062, by rfl⟩ : syracuseStep 986833 = 740125) B740125
theorem B429779 : Blo 428775 429779 := bstep (se 1 (by rfl) ⟨322334, by rfl⟩ : syracuseStep 429779 = 644669) B644669
theorem B429795 : Blo 428775 429795 := bstep (se 1 (by rfl) ⟨322346, by rfl⟩ : syracuseStep 429795 = 644693) B644693
theorem B429811 : Blo 428775 429811 := bstep (se 1 (by rfl) ⟨322358, by rfl⟩ : syracuseStep 429811 = 644717) B644717
theorem B429827 : Blo 428775 429827 := bstep (se 1 (by rfl) ⟨322370, by rfl⟩ : syracuseStep 429827 = 644741) B644741
theorem B429843 : Blo 428775 429843 := bstep (se 1 (by rfl) ⟨322382, by rfl⟩ : syracuseStep 429843 = 644765) B644765
theorem B429859 : Blo 428775 429859 := bstep (se 1 (by rfl) ⟨322394, by rfl⟩ : syracuseStep 429859 = 644789) B644789
theorem B429875 : Blo 428775 429875 := bstep (se 1 (by rfl) ⟨322406, by rfl⟩ : syracuseStep 429875 = 644813) B644813
theorem B724801 : Blo 428775 724801 := bstep (se 2 (by rfl) ⟨271800, by rfl⟩ : syracuseStep 724801 = 543601) B543601
theorem B429891 : Blo 428775 429891 := bstep (se 1 (by rfl) ⟨322418, by rfl⟩ : syracuseStep 429891 = 644837) B644837
theorem B429907 : Blo 428775 429907 := bstep (se 1 (by rfl) ⟨322430, by rfl⟩ : syracuseStep 429907 = 644861) B644861
theorem B724835 : Blo 428775 724835 := bstep (se 1 (by rfl) ⟨543626, by rfl⟩ : syracuseStep 724835 = 1087253) B1087253
theorem B429923 : Blo 428775 429923 := bstep (se 1 (by rfl) ⟨322442, by rfl⟩ : syracuseStep 429923 = 644885) B644885
theorem B692083 : Blo 428775 692083 := bstep (se 1 (by rfl) ⟨519062, by rfl⟩ : syracuseStep 692083 = 1038125) B1038125
theorem B429939 : Blo 428775 429939 := bstep (se 1 (by rfl) ⟨322454, by rfl⟩ : syracuseStep 429939 = 644909) B644909
theorem B429955 : Blo 428775 429955 := bstep (se 1 (by rfl) ⟨322466, by rfl⟩ : syracuseStep 429955 = 644933) B644933
theorem B429971 : Blo 428775 429971 := bstep (se 1 (by rfl) ⟨322478, by rfl⟩ : syracuseStep 429971 = 644957) B644957
theorem B429987 : Blo 428775 429987 := bstep (se 1 (by rfl) ⟨322490, by rfl⟩ : syracuseStep 429987 = 644981) B644981
theorem B430003 : Blo 428775 430003 := bstep (se 1 (by rfl) ⟨322502, by rfl⟩ : syracuseStep 430003 = 645005) B645005
theorem B430019 : Blo 428775 430019 := bstep (se 1 (by rfl) ⟨322514, by rfl⟩ : syracuseStep 430019 = 645029) B645029
theorem B430035 : Blo 428775 430035 := bstep (se 1 (by rfl) ⟨322526, by rfl⟩ : syracuseStep 430035 = 645053) B645053
theorem B724963 : Blo 428775 724963 := bstep (se 1 (by rfl) ⟨543722, by rfl⟩ : syracuseStep 724963 = 1087445) B1087445
theorem B430051 : Blo 428775 430051 := bstep (se 1 (by rfl) ⟨322538, by rfl⟩ : syracuseStep 430051 = 645077) B645077
theorem B430067 : Blo 428775 430067 := bstep (se 1 (by rfl) ⟨322550, by rfl⟩ : syracuseStep 430067 = 645101) B645101
theorem B430083 : Blo 428775 430083 := bstep (se 1 (by rfl) ⟨322562, by rfl⟩ : syracuseStep 430083 = 645125) B645125
theorem B430099 : Blo 428775 430099 := bstep (se 1 (by rfl) ⟨322574, by rfl⟩ : syracuseStep 430099 = 645149) B645149
theorem B430115 : Blo 428775 430115 := bstep (se 1 (by rfl) ⟨322586, by rfl⟩ : syracuseStep 430115 = 645173) B645173
theorem B430131 : Blo 428775 430131 := bstep (se 1 (by rfl) ⟨322598, by rfl⟩ : syracuseStep 430131 = 645197) B645197
theorem B430147 : Blo 428775 430147 := bstep (se 1 (by rfl) ⟨322610, by rfl⟩ : syracuseStep 430147 = 645221) B645221
theorem B1085521 : Blo 428775 1085521 := bstep (se 2 (by rfl) ⟨407070, by rfl⟩ : syracuseStep 1085521 = 814141) B814141
theorem B430163 : Blo 428775 430163 := bstep (se 1 (by rfl) ⟨322622, by rfl⟩ : syracuseStep 430163 = 645245) B645245
theorem B430179 : Blo 428775 430179 := bstep (se 1 (by rfl) ⟨322634, by rfl⟩ : syracuseStep 430179 = 645269) B645269
theorem B725105 : Blo 428775 725105 := bstep (se 2 (by rfl) ⟨271914, by rfl⟩ : syracuseStep 725105 = 543829) B543829
theorem B430195 : Blo 428775 430195 := bstep (se 1 (by rfl) ⟨322646, by rfl⟩ : syracuseStep 430195 = 645293) B645293
theorem B430211 : Blo 428775 430211 := bstep (se 1 (by rfl) ⟨322658, by rfl⟩ : syracuseStep 430211 = 645317) B645317
theorem B2330765 : Blo 428775 2330765 := bstep (se 3 (by rfl) ⟨437018, by rfl⟩ : syracuseStep 2330765 = 874037) B874037
theorem B430227 : Blo 428775 430227 := bstep (se 1 (by rfl) ⟨322670, by rfl⟩ : syracuseStep 430227 = 645341) B645341
theorem B430243 : Blo 428775 430243 := bstep (se 1 (by rfl) ⟨322682, by rfl⟩ : syracuseStep 430243 = 645365) B645365
theorem B430259 : Blo 428775 430259 := bstep (se 1 (by rfl) ⟨322694, by rfl⟩ : syracuseStep 430259 = 645389) B645389
theorem B430275 : Blo 428775 430275 := bstep (se 1 (by rfl) ⟨322706, by rfl⟩ : syracuseStep 430275 = 645413) B645413
theorem B430291 : Blo 428775 430291 := bstep (se 1 (by rfl) ⟨322718, by rfl⟩ : syracuseStep 430291 = 645437) B645437
theorem B430307 : Blo 428775 430307 := bstep (se 1 (by rfl) ⟨322730, by rfl⟩ : syracuseStep 430307 = 645461) B645461
theorem B725233 : Blo 428775 725233 := bstep (se 2 (by rfl) ⟨271962, by rfl⟩ : syracuseStep 725233 = 543925) B543925
theorem B430323 : Blo 428775 430323 := bstep (se 1 (by rfl) ⟨322742, by rfl⟩ : syracuseStep 430323 = 645485) B645485
theorem B430339 : Blo 428775 430339 := bstep (se 1 (by rfl) ⟨322754, by rfl⟩ : syracuseStep 430339 = 645509) B645509
theorem B725267 : Blo 428775 725267 := bstep (se 1 (by rfl) ⟨543950, by rfl⟩ : syracuseStep 725267 = 1087901) B1087901
theorem B430355 : Blo 428775 430355 := bstep (se 1 (by rfl) ⟨322766, by rfl⟩ : syracuseStep 430355 = 645533) B645533
theorem B18583829 : Blo 428775 18583829 := bstep (se 6 (by rfl) ⟨435558, by rfl⟩ : syracuseStep 18583829 = 871117) B871117
theorem B430371 : Blo 428775 430371 := bstep (se 1 (by rfl) ⟨322778, by rfl⟩ : syracuseStep 430371 = 645557) B645557
theorem B1642787 : Blo 428775 1642787 := bstep (se 1 (by rfl) ⟨1232090, by rfl⟩ : syracuseStep 1642787 = 2464181) B2464181
theorem B1642801 : Blo 428775 1642801 := bstep (se 2 (by rfl) ⟨616050, by rfl⟩ : syracuseStep 1642801 = 1232101) B1232101
theorem B430387 : Blo 428775 430387 := bstep (se 1 (by rfl) ⟨322790, by rfl⟩ : syracuseStep 430387 = 645581) B645581
theorem B692545 : Blo 428775 692545 := bstep (se 2 (by rfl) ⟨259704, by rfl⟩ : syracuseStep 692545 = 519409) B519409
theorem B430403 : Blo 428775 430403 := bstep (se 1 (by rfl) ⟨322802, by rfl⟩ : syracuseStep 430403 = 645605) B645605
theorem B430419 : Blo 428775 430419 := bstep (se 1 (by rfl) ⟨322814, by rfl⟩ : syracuseStep 430419 = 645629) B645629
theorem B1085795 : Blo 428775 1085795 := bstep (se 1 (by rfl) ⟨814346, by rfl⟩ : syracuseStep 1085795 = 1628693) B1628693
theorem B430435 : Blo 428775 430435 := bstep (se 1 (by rfl) ⟨322826, by rfl⟩ : syracuseStep 430435 = 645653) B645653
theorem B1839473 : Blo 428775 1839473 := bstep (se 2 (by rfl) ⟨689802, by rfl⟩ : syracuseStep 1839473 = 1379605) B1379605
theorem B430451 : Blo 428775 430451 := bstep (se 1 (by rfl) ⟨322838, by rfl⟩ : syracuseStep 430451 = 645677) B645677
theorem B430467 : Blo 428775 430467 := bstep (se 1 (by rfl) ⟨322850, by rfl⟩ : syracuseStep 430467 = 645701) B645701
theorem B725395 : Blo 428775 725395 := bstep (se 1 (by rfl) ⟨544046, by rfl⟩ : syracuseStep 725395 = 1088093) B1088093
theorem B430483 : Blo 428775 430483 := bstep (se 1 (by rfl) ⟨322862, by rfl⟩ : syracuseStep 430483 = 645725) B645725
theorem B692641 : Blo 428775 692641 := bstep (se 2 (by rfl) ⟨259740, by rfl⟩ : syracuseStep 692641 = 519481) B519481
theorem B430499 : Blo 428775 430499 := bstep (se 1 (by rfl) ⟨322874, by rfl⟩ : syracuseStep 430499 = 645749) B645749
theorem B430515 : Blo 428775 430515 := bstep (se 1 (by rfl) ⟨322886, by rfl⟩ : syracuseStep 430515 = 645773) B645773
theorem B430531 : Blo 428775 430531 := bstep (se 1 (by rfl) ⟨322898, by rfl⟩ : syracuseStep 430531 = 645797) B645797
theorem B430547 : Blo 428775 430547 := bstep (se 1 (by rfl) ⟨322910, by rfl⟩ : syracuseStep 430547 = 645821) B645821
theorem B430563 : Blo 428775 430563 := bstep (se 1 (by rfl) ⟨322922, by rfl⟩ : syracuseStep 430563 = 645845) B645845
theorem B430579 : Blo 428775 430579 := bstep (se 1 (by rfl) ⟨322934, by rfl⟩ : syracuseStep 430579 = 645869) B645869
theorem B430595 : Blo 428775 430595 := bstep (se 1 (by rfl) ⟨322946, by rfl⟩ : syracuseStep 430595 = 645893) B645893
theorem B2789893 : Blo 428775 2789893 := bstep (se 4 (by rfl) ⟨261552, by rfl⟩ : syracuseStep 2789893 = 523105) B523105
theorem B430611 : Blo 428775 430611 := bstep (se 1 (by rfl) ⟨322958, by rfl⟩ : syracuseStep 430611 = 645917) B645917
theorem B725537 : Blo 428775 725537 := bstep (se 2 (by rfl) ⟨272076, by rfl⟩ : syracuseStep 725537 = 544153) B544153
theorem B1085987 : Blo 428775 1085987 := bstep (se 1 (by rfl) ⟨814490, by rfl⟩ : syracuseStep 1085987 = 1628981) B1628981
theorem B430627 : Blo 428775 430627 := bstep (se 1 (by rfl) ⟨322970, by rfl⟩ : syracuseStep 430627 = 645941) B645941
theorem B430643 : Blo 428775 430643 := bstep (se 1 (by rfl) ⟨322982, by rfl⟩ : syracuseStep 430643 = 645965) B645965
theorem B692801 : Blo 428775 692801 := bstep (se 2 (by rfl) ⟨259800, by rfl⟩ : syracuseStep 692801 = 519601) B519601
theorem B430659 : Blo 428775 430659 := bstep (se 1 (by rfl) ⟨322994, by rfl⟩ : syracuseStep 430659 = 645989) B645989
theorem B430675 : Blo 428775 430675 := bstep (se 1 (by rfl) ⟨323006, by rfl⟩ : syracuseStep 430675 = 646013) B646013
theorem B430691 : Blo 428775 430691 := bstep (se 1 (by rfl) ⟨323018, by rfl⟩ : syracuseStep 430691 = 646037) B646037
theorem B430707 : Blo 428775 430707 := bstep (se 1 (by rfl) ⟨323030, by rfl⟩ : syracuseStep 430707 = 646061) B646061
theorem B430723 : Blo 428775 430723 := bstep (se 1 (by rfl) ⟨323042, by rfl⟩ : syracuseStep 430723 = 646085) B646085
theorem B430739 : Blo 428775 430739 := bstep (se 1 (by rfl) ⟨323054, by rfl⟩ : syracuseStep 430739 = 646109) B646109
theorem B725665 : Blo 428775 725665 := bstep (se 2 (by rfl) ⟨272124, by rfl⟩ : syracuseStep 725665 = 544249) B544249
theorem B430755 : Blo 428775 430755 := bstep (se 1 (by rfl) ⟨323066, by rfl⟩ : syracuseStep 430755 = 646133) B646133
theorem B430771 : Blo 428775 430771 := bstep (se 1 (by rfl) ⟨323078, by rfl⟩ : syracuseStep 430771 = 646157) B646157
theorem B725699 : Blo 428775 725699 := bstep (se 1 (by rfl) ⟨544274, by rfl⟩ : syracuseStep 725699 = 1088549) B1088549
theorem B430787 : Blo 428775 430787 := bstep (se 1 (by rfl) ⟨323090, by rfl⟩ : syracuseStep 430787 = 646181) B646181
theorem B430803 : Blo 428775 430803 := bstep (se 1 (by rfl) ⟨323102, by rfl⟩ : syracuseStep 430803 = 646205) B646205
theorem B430819 : Blo 428775 430819 := bstep (se 1 (by rfl) ⟨323114, by rfl⟩ : syracuseStep 430819 = 646229) B646229
theorem B430835 : Blo 428775 430835 := bstep (se 1 (by rfl) ⟨323126, by rfl⟩ : syracuseStep 430835 = 646253) B646253
theorem B430851 : Blo 428775 430851 := bstep (se 1 (by rfl) ⟨323138, by rfl⟩ : syracuseStep 430851 = 646277) B646277
theorem B430867 : Blo 428775 430867 := bstep (se 1 (by rfl) ⟨323150, by rfl⟩ : syracuseStep 430867 = 646301) B646301
theorem B430883 : Blo 428775 430883 := bstep (se 1 (by rfl) ⟨323162, by rfl⟩ : syracuseStep 430883 = 646325) B646325
theorem B430899 : Blo 428775 430899 := bstep (se 1 (by rfl) ⟨323174, by rfl⟩ : syracuseStep 430899 = 646349) B646349
theorem B725827 : Blo 428775 725827 := bstep (se 1 (by rfl) ⟨544370, by rfl⟩ : syracuseStep 725827 = 1088741) B1088741
theorem B430915 : Blo 428775 430915 := bstep (se 1 (by rfl) ⟨323186, by rfl⟩ : syracuseStep 430915 = 646373) B646373
theorem B430931 : Blo 428775 430931 := bstep (se 1 (by rfl) ⟨323198, by rfl⟩ : syracuseStep 430931 = 646397) B646397
theorem B430947 : Blo 428775 430947 := bstep (se 1 (by rfl) ⟨323210, by rfl⟩ : syracuseStep 430947 = 646421) B646421
theorem B430963 : Blo 428775 430963 := bstep (se 1 (by rfl) ⟨323222, by rfl⟩ : syracuseStep 430963 = 646445) B646445
theorem B430979 : Blo 428775 430979 := bstep (se 1 (by rfl) ⟨323234, by rfl⟩ : syracuseStep 430979 = 646469) B646469
theorem B430995 : Blo 428775 430995 := bstep (se 1 (by rfl) ⟨323246, by rfl⟩ : syracuseStep 430995 = 646493) B646493
theorem B431011 : Blo 428775 431011 := bstep (se 1 (by rfl) ⟨323258, by rfl⟩ : syracuseStep 431011 = 646517) B646517
theorem B431027 : Blo 428775 431027 := bstep (se 1 (by rfl) ⟨323270, by rfl⟩ : syracuseStep 431027 = 646541) B646541
theorem B431043 : Blo 428775 431043 := bstep (se 1 (by rfl) ⟨323282, by rfl⟩ : syracuseStep 431043 = 646565) B646565
theorem B725969 : Blo 428775 725969 := bstep (se 2 (by rfl) ⟨272238, by rfl⟩ : syracuseStep 725969 = 544477) B544477
theorem B431059 : Blo 428775 431059 := bstep (se 1 (by rfl) ⟨323294, by rfl⟩ : syracuseStep 431059 = 646589) B646589
theorem B431075 : Blo 428775 431075 := bstep (se 1 (by rfl) ⟨323306, by rfl⟩ : syracuseStep 431075 = 646613) B646613
theorem B431091 : Blo 428775 431091 := bstep (se 1 (by rfl) ⟨323318, by rfl⟩ : syracuseStep 431091 = 646637) B646637
theorem B431107 : Blo 428775 431107 := bstep (se 1 (by rfl) ⟨323330, by rfl⟩ : syracuseStep 431107 = 646661) B646661
theorem B431123 : Blo 428775 431123 := bstep (se 1 (by rfl) ⟨323342, by rfl⟩ : syracuseStep 431123 = 646685) B646685
theorem B431139 : Blo 428775 431139 := bstep (se 1 (by rfl) ⟨323354, by rfl⟩ : syracuseStep 431139 = 646709) B646709
theorem B431155 : Blo 428775 431155 := bstep (se 1 (by rfl) ⟨323366, by rfl⟩ : syracuseStep 431155 = 646733) B646733
theorem B431171 : Blo 428775 431171 := bstep (se 1 (by rfl) ⟨323378, by rfl⟩ : syracuseStep 431171 = 646757) B646757
theorem B726097 : Blo 428775 726097 := bstep (se 2 (by rfl) ⟨272286, by rfl⟩ : syracuseStep 726097 = 544573) B544573
theorem B431187 : Blo 428775 431187 := bstep (se 1 (by rfl) ⟨323390, by rfl⟩ : syracuseStep 431187 = 646781) B646781
theorem B431203 : Blo 428775 431203 := bstep (se 1 (by rfl) ⟨323402, by rfl⟩ : syracuseStep 431203 = 646805) B646805
theorem B726131 : Blo 428775 726131 := bstep (se 1 (by rfl) ⟨544598, by rfl⟩ : syracuseStep 726131 = 1089197) B1089197
theorem B431219 : Blo 428775 431219 := bstep (se 1 (by rfl) ⟨323414, by rfl⟩ : syracuseStep 431219 = 646829) B646829
theorem B431235 : Blo 428775 431235 := bstep (se 1 (by rfl) ⟨323426, by rfl⟩ : syracuseStep 431235 = 646853) B646853
theorem B431251 : Blo 428775 431251 := bstep (se 1 (by rfl) ⟨323438, by rfl⟩ : syracuseStep 431251 = 646877) B646877
theorem B431267 : Blo 428775 431267 := bstep (se 1 (by rfl) ⟨323450, by rfl⟩ : syracuseStep 431267 = 646901) B646901
theorem B431283 : Blo 428775 431283 := bstep (se 1 (by rfl) ⟨323462, by rfl⟩ : syracuseStep 431283 = 646925) B646925
theorem B431299 : Blo 428775 431299 := bstep (se 1 (by rfl) ⟨323474, by rfl⟩ : syracuseStep 431299 = 646949) B646949
theorem B431315 : Blo 428775 431315 := bstep (se 1 (by rfl) ⟨323486, by rfl⟩ : syracuseStep 431315 = 646973) B646973
theorem B431331 : Blo 428775 431331 := bstep (se 1 (by rfl) ⟨323498, by rfl⟩ : syracuseStep 431331 = 646997) B646997
theorem B726259 : Blo 428775 726259 := bstep (se 1 (by rfl) ⟨544694, by rfl⟩ : syracuseStep 726259 = 1089389) B1089389
theorem B431347 : Blo 428775 431347 := bstep (se 1 (by rfl) ⟨323510, by rfl⟩ : syracuseStep 431347 = 647021) B647021
theorem B431363 : Blo 428775 431363 := bstep (se 1 (by rfl) ⟨323522, by rfl⟩ : syracuseStep 431363 = 647045) B647045
theorem B431379 : Blo 428775 431379 := bstep (se 1 (by rfl) ⟨323534, by rfl⟩ : syracuseStep 431379 = 647069) B647069
theorem B431395 : Blo 428775 431395 := bstep (se 1 (by rfl) ⟨323546, by rfl⟩ : syracuseStep 431395 = 647093) B647093
theorem B431411 : Blo 428775 431411 := bstep (se 1 (by rfl) ⟨323558, by rfl⟩ : syracuseStep 431411 = 647117) B647117
theorem B431427 : Blo 428775 431427 := bstep (se 1 (by rfl) ⟨323570, by rfl⟩ : syracuseStep 431427 = 647141) B647141
theorem B431443 : Blo 428775 431443 := bstep (se 1 (by rfl) ⟨323582, by rfl⟩ : syracuseStep 431443 = 647165) B647165
theorem B431459 : Blo 428775 431459 := bstep (se 1 (by rfl) ⟨323594, by rfl⟩ : syracuseStep 431459 = 647189) B647189
theorem B431475 : Blo 428775 431475 := bstep (se 1 (by rfl) ⟨323606, by rfl⟩ : syracuseStep 431475 = 647213) B647213
theorem B726401 : Blo 428775 726401 := bstep (se 2 (by rfl) ⟨272400, by rfl⟩ : syracuseStep 726401 = 544801) B544801
theorem B431491 : Blo 428775 431491 := bstep (se 1 (by rfl) ⟨323618, by rfl⟩ : syracuseStep 431491 = 647237) B647237
theorem B431507 : Blo 428775 431507 := bstep (se 1 (by rfl) ⟨323630, by rfl⟩ : syracuseStep 431507 = 647261) B647261
theorem B431523 : Blo 428775 431523 := bstep (se 1 (by rfl) ⟨323642, by rfl⟩ : syracuseStep 431523 = 647285) B647285
theorem B431539 : Blo 428775 431539 := bstep (se 1 (by rfl) ⟨323654, by rfl⟩ : syracuseStep 431539 = 647309) B647309
theorem B431555 : Blo 428775 431555 := bstep (se 1 (by rfl) ⟨323666, by rfl⟩ : syracuseStep 431555 = 647333) B647333
theorem B1086929 : Blo 428775 1086929 := bstep (se 2 (by rfl) ⟨407598, by rfl⟩ : syracuseStep 1086929 = 815197) B815197
theorem B431571 : Blo 428775 431571 := bstep (se 1 (by rfl) ⟨323678, by rfl⟩ : syracuseStep 431571 = 647357) B647357
theorem B431587 : Blo 428775 431587 := bstep (se 1 (by rfl) ⟨323690, by rfl⟩ : syracuseStep 431587 = 647381) B647381
theorem B431603 : Blo 428775 431603 := bstep (se 1 (by rfl) ⟨323702, by rfl⟩ : syracuseStep 431603 = 647405) B647405
theorem B726529 : Blo 428775 726529 := bstep (se 2 (by rfl) ⟨272448, by rfl⟩ : syracuseStep 726529 = 544897) B544897
theorem B1086979 : Blo 428775 1086979 := bstep (se 1 (by rfl) ⟨815234, by rfl⟩ : syracuseStep 1086979 = 1630469) B1630469
theorem B431619 : Blo 428775 431619 := bstep (se 1 (by rfl) ⟨323714, by rfl⟩ : syracuseStep 431619 = 647429) B647429
theorem B431635 : Blo 428775 431635 := bstep (se 1 (by rfl) ⟨323726, by rfl⟩ : syracuseStep 431635 = 647453) B647453
theorem B726563 : Blo 428775 726563 := bstep (se 1 (by rfl) ⟨544922, by rfl⟩ : syracuseStep 726563 = 1089845) B1089845
theorem B431651 : Blo 428775 431651 := bstep (se 1 (by rfl) ⟨323738, by rfl⟩ : syracuseStep 431651 = 647477) B647477
theorem B1447469 : Blo 428775 1447469 := bstep (se 3 (by rfl) ⟨271400, by rfl⟩ : syracuseStep 1447469 = 542801) B542801
theorem B431667 : Blo 428775 431667 := bstep (se 1 (by rfl) ⟨323750, by rfl⟩ : syracuseStep 431667 = 647501) B647501
theorem B431683 : Blo 428775 431683 := bstep (se 1 (by rfl) ⟨323762, by rfl⟩ : syracuseStep 431683 = 647525) B647525
theorem B431699 : Blo 428775 431699 := bstep (se 1 (by rfl) ⟨323774, by rfl⟩ : syracuseStep 431699 = 647549) B647549
theorem B1447523 : Blo 428775 1447523 := bstep (se 1 (by rfl) ⟨1085642, by rfl⟩ : syracuseStep 1447523 = 2171285) B2171285
theorem B431715 : Blo 428775 431715 := bstep (se 1 (by rfl) ⟨323786, by rfl⟩ : syracuseStep 431715 = 647573) B647573
theorem B431731 : Blo 428775 431731 := bstep (se 1 (by rfl) ⟨323798, by rfl⟩ : syracuseStep 431731 = 647597) B647597
theorem B431747 : Blo 428775 431747 := bstep (se 1 (by rfl) ⟨323810, by rfl⟩ : syracuseStep 431747 = 647621) B647621
theorem B1087121 : Blo 428775 1087121 := bstep (se 2 (by rfl) ⟨407670, by rfl⟩ : syracuseStep 1087121 = 815341) B815341
theorem B431763 : Blo 428775 431763 := bstep (se 1 (by rfl) ⟨323822, by rfl⟩ : syracuseStep 431763 = 647645) B647645
theorem B726691 : Blo 428775 726691 := bstep (se 1 (by rfl) ⟨545018, by rfl⟩ : syracuseStep 726691 = 1090037) B1090037
theorem B431779 : Blo 428775 431779 := bstep (se 1 (by rfl) ⟨323834, by rfl⟩ : syracuseStep 431779 = 647669) B647669
theorem B661169 : Blo 428775 661169 := bstep (se 2 (by rfl) ⟨247938, by rfl⟩ : syracuseStep 661169 = 495877) B495877
theorem B431795 : Blo 428775 431795 := bstep (se 1 (by rfl) ⟨323846, by rfl⟩ : syracuseStep 431795 = 647693) B647693
theorem B431811 : Blo 428775 431811 := bstep (se 1 (by rfl) ⟨323858, by rfl⟩ : syracuseStep 431811 = 647717) B647717
theorem B431827 : Blo 428775 431827 := bstep (se 1 (by rfl) ⟨323870, by rfl⟩ : syracuseStep 431827 = 647741) B647741
theorem B431843 : Blo 428775 431843 := bstep (se 1 (by rfl) ⟨323882, by rfl⟩ : syracuseStep 431843 = 647765) B647765
theorem B2463473 : Blo 428775 2463473 := bstep (se 2 (by rfl) ⟨923802, by rfl⟩ : syracuseStep 2463473 = 1847605) B1847605
theorem B431859 : Blo 428775 431859 := bstep (se 1 (by rfl) ⟨323894, by rfl⟩ : syracuseStep 431859 = 647789) B647789
theorem B431875 : Blo 428775 431875 := bstep (se 1 (by rfl) ⟨323906, by rfl⟩ : syracuseStep 431875 = 647813) B647813
theorem B431891 : Blo 428775 431891 := bstep (se 1 (by rfl) ⟨323918, by rfl⟩ : syracuseStep 431891 = 647837) B647837
theorem B431907 : Blo 428775 431907 := bstep (se 1 (by rfl) ⟨323930, by rfl⟩ : syracuseStep 431907 = 647861) B647861
theorem B726833 : Blo 428775 726833 := bstep (se 2 (by rfl) ⟨272562, by rfl⟩ : syracuseStep 726833 = 545125) B545125
theorem B431923 : Blo 428775 431923 := bstep (se 1 (by rfl) ⟨323942, by rfl⟩ : syracuseStep 431923 = 647885) B647885
theorem B431939 : Blo 428775 431939 := bstep (se 1 (by rfl) ⟨323954, by rfl⟩ : syracuseStep 431939 = 647909) B647909
theorem B431955 : Blo 428775 431955 := bstep (se 1 (by rfl) ⟨323966, by rfl⟩ : syracuseStep 431955 = 647933) B647933
theorem B431971 : Blo 428775 431971 := bstep (se 1 (by rfl) ⟨323978, by rfl⟩ : syracuseStep 431971 = 647957) B647957
theorem B1447793 : Blo 428775 1447793 := bstep (se 2 (by rfl) ⟨542922, by rfl⟩ : syracuseStep 1447793 = 1085845) B1085845
theorem B431987 : Blo 428775 431987 := bstep (se 1 (by rfl) ⟨323990, by rfl⟩ : syracuseStep 431987 = 647981) B647981
theorem B432003 : Blo 428775 432003 := bstep (se 1 (by rfl) ⟨324002, by rfl⟩ : syracuseStep 432003 = 648005) B648005
theorem B432019 : Blo 428775 432019 := bstep (se 1 (by rfl) ⟨324014, by rfl⟩ : syracuseStep 432019 = 648029) B648029
theorem B432035 : Blo 428775 432035 := bstep (se 1 (by rfl) ⟨324026, by rfl⟩ : syracuseStep 432035 = 648053) B648053
theorem B726961 : Blo 428775 726961 := bstep (se 2 (by rfl) ⟨272610, by rfl⟩ : syracuseStep 726961 = 545221) B545221
theorem B1382321 : Blo 428775 1382321 := bstep (se 2 (by rfl) ⟨518370, by rfl⟩ : syracuseStep 1382321 = 1036741) B1036741
theorem B432051 : Blo 428775 432051 := bstep (se 1 (by rfl) ⟨324038, by rfl⟩ : syracuseStep 432051 = 648077) B648077
theorem B432067 : Blo 428775 432067 := bstep (se 1 (by rfl) ⟨324050, by rfl⟩ : syracuseStep 432067 = 648101) B648101
theorem B726995 : Blo 428775 726995 := bstep (se 1 (by rfl) ⟨545246, by rfl⟩ : syracuseStep 726995 = 1090493) B1090493
theorem B432083 : Blo 428775 432083 := bstep (se 1 (by rfl) ⟨324062, by rfl⟩ : syracuseStep 432083 = 648125) B648125
theorem B432099 : Blo 428775 432099 := bstep (se 1 (by rfl) ⟨324074, by rfl⟩ : syracuseStep 432099 = 648149) B648149
theorem B3282929 : Blo 428775 3282929 := bstep (se 2 (by rfl) ⟨1231098, by rfl⟩ : syracuseStep 3282929 = 2462197) B2462197
theorem B432115 : Blo 428775 432115 := bstep (se 1 (by rfl) ⟨324086, by rfl⟩ : syracuseStep 432115 = 648173) B648173
theorem B432131 : Blo 428775 432131 := bstep (se 1 (by rfl) ⟨324098, by rfl⟩ : syracuseStep 432131 = 648197) B648197
theorem B432147 : Blo 428775 432147 := bstep (se 1 (by rfl) ⟨324110, by rfl⟩ : syracuseStep 432147 = 648221) B648221
theorem B432163 : Blo 428775 432163 := bstep (se 1 (by rfl) ⟨324122, by rfl⟩ : syracuseStep 432163 = 648245) B648245
theorem B432179 : Blo 428775 432179 := bstep (se 1 (by rfl) ⟨324134, by rfl⟩ : syracuseStep 432179 = 648269) B648269
theorem B432195 : Blo 428775 432195 := bstep (se 1 (by rfl) ⟨324146, by rfl⟩ : syracuseStep 432195 = 648293) B648293
theorem B727123 : Blo 428775 727123 := bstep (se 1 (by rfl) ⟨545342, by rfl⟩ : syracuseStep 727123 = 1090685) B1090685
theorem B432211 : Blo 428775 432211 := bstep (se 1 (by rfl) ⟨324158, by rfl⟩ : syracuseStep 432211 = 648317) B648317
theorem B432227 : Blo 428775 432227 := bstep (se 1 (by rfl) ⟨324170, by rfl⟩ : syracuseStep 432227 = 648341) B648341
theorem B432243 : Blo 428775 432243 := bstep (se 1 (by rfl) ⟨324182, by rfl⟩ : syracuseStep 432243 = 648365) B648365
theorem B432259 : Blo 428775 432259 := bstep (se 1 (by rfl) ⟨324194, by rfl⟩ : syracuseStep 432259 = 648389) B648389
theorem B432275 : Blo 428775 432275 := bstep (se 1 (by rfl) ⟨324206, by rfl⟩ : syracuseStep 432275 = 648413) B648413
theorem B432291 : Blo 428775 432291 := bstep (se 1 (by rfl) ⟨324218, by rfl⟩ : syracuseStep 432291 = 648437) B648437
theorem B432307 : Blo 428775 432307 := bstep (se 1 (by rfl) ⟨324230, by rfl⟩ : syracuseStep 432307 = 648461) B648461
theorem B432323 : Blo 428775 432323 := bstep (se 1 (by rfl) ⟨324242, by rfl⟩ : syracuseStep 432323 = 648485) B648485
theorem B432339 : Blo 428775 432339 := bstep (se 1 (by rfl) ⟨324254, by rfl⟩ : syracuseStep 432339 = 648509) B648509
theorem B727265 : Blo 428775 727265 := bstep (se 2 (by rfl) ⟨272724, by rfl⟩ : syracuseStep 727265 = 545449) B545449
theorem B2070755 : Blo 428775 2070755 := bstep (se 1 (by rfl) ⟨1553066, by rfl⟩ : syracuseStep 2070755 = 3106133) B3106133
theorem B432355 : Blo 428775 432355 := bstep (se 1 (by rfl) ⟨324266, by rfl⟩ : syracuseStep 432355 = 648533) B648533
theorem B432371 : Blo 428775 432371 := bstep (se 1 (by rfl) ⟨324278, by rfl⟩ : syracuseStep 432371 = 648557) B648557
theorem B432387 : Blo 428775 432387 := bstep (se 1 (by rfl) ⟨324290, by rfl⟩ : syracuseStep 432387 = 648581) B648581
theorem B432403 : Blo 428775 432403 := bstep (se 1 (by rfl) ⟨324302, by rfl⟩ : syracuseStep 432403 = 648605) B648605
theorem B432419 : Blo 428775 432419 := bstep (se 1 (by rfl) ⟨324314, by rfl⟩ : syracuseStep 432419 = 648629) B648629
theorem B432435 : Blo 428775 432435 := bstep (se 1 (by rfl) ⟨324326, by rfl⟩ : syracuseStep 432435 = 648653) B648653
theorem B432451 : Blo 428775 432451 := bstep (se 1 (by rfl) ⟨324338, by rfl⟩ : syracuseStep 432451 = 648677) B648677
theorem B432467 : Blo 428775 432467 := bstep (se 1 (by rfl) ⟨324350, by rfl⟩ : syracuseStep 432467 = 648701) B648701
theorem B727393 : Blo 428775 727393 := bstep (se 2 (by rfl) ⟨272772, by rfl⟩ : syracuseStep 727393 = 545545) B545545
theorem B432483 : Blo 428775 432483 := bstep (se 1 (by rfl) ⟨324362, by rfl⟩ : syracuseStep 432483 = 648725) B648725
theorem B432499 : Blo 428775 432499 := bstep (se 1 (by rfl) ⟨324374, by rfl⟩ : syracuseStep 432499 = 648749) B648749
theorem B727427 : Blo 428775 727427 := bstep (se 1 (by rfl) ⟨545570, by rfl⟩ : syracuseStep 727427 = 1091141) B1091141
theorem B432515 : Blo 428775 432515 := bstep (se 1 (by rfl) ⟨324386, by rfl⟩ : syracuseStep 432515 = 648773) B648773
theorem B1448333 : Blo 428775 1448333 := bstep (se 3 (by rfl) ⟨271562, by rfl⟩ : syracuseStep 1448333 = 543125) B543125
theorem B432531 : Blo 428775 432531 := bstep (se 1 (by rfl) ⟨324398, by rfl⟩ : syracuseStep 432531 = 648797) B648797
theorem B432547 : Blo 428775 432547 := bstep (se 1 (by rfl) ⟨324410, by rfl⟩ : syracuseStep 432547 = 648821) B648821
theorem B432563 : Blo 428775 432563 := bstep (se 1 (by rfl) ⟨324422, by rfl⟩ : syracuseStep 432563 = 648845) B648845
theorem B1448387 : Blo 428775 1448387 := bstep (se 1 (by rfl) ⟨1086290, by rfl⟩ : syracuseStep 1448387 = 2172581) B2172581
theorem B432579 : Blo 428775 432579 := bstep (se 1 (by rfl) ⟨324434, by rfl⟩ : syracuseStep 432579 = 648869) B648869
theorem B432595 : Blo 428775 432595 := bstep (se 1 (by rfl) ⟨324446, by rfl⟩ : syracuseStep 432595 = 648893) B648893
theorem B432611 : Blo 428775 432611 := bstep (se 1 (by rfl) ⟨324458, by rfl⟩ : syracuseStep 432611 = 648917) B648917
theorem B432627 : Blo 428775 432627 := bstep (se 1 (by rfl) ⟨324470, by rfl⟩ : syracuseStep 432627 = 648941) B648941
theorem B727555 : Blo 428775 727555 := bstep (se 1 (by rfl) ⟨545666, by rfl⟩ : syracuseStep 727555 = 1091333) B1091333
theorem B432643 : Blo 428775 432643 := bstep (se 1 (by rfl) ⟨324482, by rfl⟩ : syracuseStep 432643 = 648965) B648965
theorem B432659 : Blo 428775 432659 := bstep (se 1 (by rfl) ⟨324494, by rfl⟩ : syracuseStep 432659 = 648989) B648989
theorem B432675 : Blo 428775 432675 := bstep (se 1 (by rfl) ⟨324506, by rfl⟩ : syracuseStep 432675 = 649013) B649013
theorem B432691 : Blo 428775 432691 := bstep (se 1 (by rfl) ⟨324518, by rfl⟩ : syracuseStep 432691 = 649037) B649037
theorem B432707 : Blo 428775 432707 := bstep (se 1 (by rfl) ⟨324530, by rfl⟩ : syracuseStep 432707 = 649061) B649061
theorem B4725317 : Blo 428775 4725317 := bstep (se 4 (by rfl) ⟨442998, by rfl⟩ : syracuseStep 4725317 = 885997) B885997
theorem B432723 : Blo 428775 432723 := bstep (se 1 (by rfl) ⟨324542, by rfl⟩ : syracuseStep 432723 = 649085) B649085
theorem B432739 : Blo 428775 432739 := bstep (se 1 (by rfl) ⟨324554, by rfl⟩ : syracuseStep 432739 = 649109) B649109
theorem B1088113 : Blo 428775 1088113 := bstep (se 2 (by rfl) ⟨408042, by rfl⟩ : syracuseStep 1088113 = 816085) B816085
theorem B432755 : Blo 428775 432755 := bstep (se 1 (by rfl) ⟨324566, by rfl⟩ : syracuseStep 432755 = 649133) B649133
theorem B432771 : Blo 428775 432771 := bstep (se 1 (by rfl) ⟨324578, by rfl⟩ : syracuseStep 432771 = 649157) B649157
theorem B727697 : Blo 428775 727697 := bstep (se 2 (by rfl) ⟨272886, by rfl⟩ : syracuseStep 727697 = 545773) B545773
theorem B1448657 : Blo 428775 1448657 := bstep (se 2 (by rfl) ⟨543246, by rfl⟩ : syracuseStep 1448657 = 1086493) B1086493
theorem B1841933 : Blo 428775 1841933 := bstep (se 3 (by rfl) ⟨345362, by rfl⟩ : syracuseStep 1841933 = 690725) B690725
theorem B727825 : Blo 428775 727825 := bstep (se 2 (by rfl) ⟨272934, by rfl⟩ : syracuseStep 727825 = 545869) B545869
theorem B629537 : Blo 428775 629537 := bstep (se 2 (by rfl) ⟨236076, by rfl⟩ : syracuseStep 629537 = 472153) B472153
theorem B727859 : Blo 428775 727859 := bstep (se 1 (by rfl) ⟨545894, by rfl⟩ : syracuseStep 727859 = 1091789) B1091789
theorem B5315381 : Blo 428775 5315381 := bstep (se 5 (by rfl) ⟨249158, by rfl⟩ : syracuseStep 5315381 = 498317) B498317
theorem B1088387 : Blo 428775 1088387 := bstep (se 1 (by rfl) ⟨816290, by rfl⟩ : syracuseStep 1088387 = 1632581) B1632581
theorem B727987 : Blo 428775 727987 := bstep (se 1 (by rfl) ⟨545990, by rfl⟩ : syracuseStep 727987 = 1091981) B1091981
theorem B728129 : Blo 428775 728129 := bstep (se 2 (by rfl) ⟨273048, by rfl⟩ : syracuseStep 728129 = 546097) B546097
theorem B1088579 : Blo 428775 1088579 := bstep (se 1 (by rfl) ⟨816434, by rfl⟩ : syracuseStep 1088579 = 1632869) B1632869
theorem B728257 : Blo 428775 728257 := bstep (se 2 (by rfl) ⟨273096, by rfl⟩ : syracuseStep 728257 = 546193) B546193
theorem B728291 : Blo 428775 728291 := bstep (se 1 (by rfl) ⟨546218, by rfl⟩ : syracuseStep 728291 = 1092437) B1092437
theorem B1449197 : Blo 428775 1449197 := bstep (se 3 (by rfl) ⟨271724, by rfl⟩ : syracuseStep 1449197 = 543449) B543449
theorem B4955377 : Blo 428775 4955377 := bstep (se 2 (by rfl) ⟨1858266, by rfl⟩ : syracuseStep 4955377 = 3716533) B3716533
theorem B1449251 : Blo 428775 1449251 := bstep (se 1 (by rfl) ⟨1086938, by rfl⟩ : syracuseStep 1449251 = 2173877) B2173877
theorem B728419 : Blo 428775 728419 := bstep (se 1 (by rfl) ⟨546314, by rfl⟩ : syracuseStep 728419 = 1092629) B1092629
theorem B728561 : Blo 428775 728561 := bstep (se 2 (by rfl) ⟨273210, by rfl⟩ : syracuseStep 728561 = 546421) B546421
theorem B1449521 : Blo 428775 1449521 := bstep (se 2 (by rfl) ⟨543570, by rfl⟩ : syracuseStep 1449521 = 1087141) B1087141
theorem B2629169 : Blo 428775 2629169 := bstep (se 2 (by rfl) ⟨985938, by rfl⟩ : syracuseStep 2629169 = 1971877) B1971877
theorem B728689 : Blo 428775 728689 := bstep (se 2 (by rfl) ⟨273258, by rfl⟩ : syracuseStep 728689 = 546517) B546517
theorem B728723 : Blo 428775 728723 := bstep (se 1 (by rfl) ⟨546542, by rfl⟩ : syracuseStep 728723 = 1093085) B1093085
theorem B2760389 : Blo 428775 2760389 := bstep (se 4 (by rfl) ⟨258786, by rfl⟩ : syracuseStep 2760389 = 517573) B517573
theorem B728851 : Blo 428775 728851 := bstep (se 1 (by rfl) ⟨546638, by rfl⟩ : syracuseStep 728851 = 1093277) B1093277
theorem B728993 : Blo 428775 728993 := bstep (se 2 (by rfl) ⟨273372, by rfl⟩ : syracuseStep 728993 = 546745) B546745
theorem B1089521 : Blo 428775 1089521 := bstep (se 2 (by rfl) ⟨408570, by rfl⟩ : syracuseStep 1089521 = 817141) B817141
theorem B729121 : Blo 428775 729121 := bstep (se 2 (by rfl) ⟨273420, by rfl⟩ : syracuseStep 729121 = 546841) B546841
theorem B1089571 : Blo 428775 1089571 := bstep (se 1 (by rfl) ⟨817178, by rfl⟩ : syracuseStep 1089571 = 1634357) B1634357
theorem B729155 : Blo 428775 729155 := bstep (se 1 (by rfl) ⟨546866, by rfl⟩ : syracuseStep 729155 = 1093733) B1093733
theorem B1450061 : Blo 428775 1450061 := bstep (se 3 (by rfl) ⟨271886, by rfl⟩ : syracuseStep 1450061 = 543773) B543773
theorem B1450115 : Blo 428775 1450115 := bstep (se 1 (by rfl) ⟨1087586, by rfl⟩ : syracuseStep 1450115 = 2175173) B2175173
theorem B1089713 : Blo 428775 1089713 := bstep (se 2 (by rfl) ⟨408642, by rfl⟩ : syracuseStep 1089713 = 817285) B817285
theorem B2072753 : Blo 428775 2072753 := bstep (se 2 (by rfl) ⟨777282, by rfl⟩ : syracuseStep 2072753 = 1554565) B1554565
theorem B729283 : Blo 428775 729283 := bstep (se 1 (by rfl) ⟨546962, by rfl⟩ : syracuseStep 729283 = 1093925) B1093925
theorem B4661489 : Blo 428775 4661489 := bstep (se 2 (by rfl) ⟨1748058, by rfl⟩ : syracuseStep 4661489 = 3496117) B3496117
theorem B1843505 : Blo 428775 1843505 := bstep (se 2 (by rfl) ⟨691314, by rfl⟩ : syracuseStep 1843505 = 1382629) B1382629
theorem B1384781 : Blo 428775 1384781 := bstep (se 3 (by rfl) ⟨259646, by rfl⟩ : syracuseStep 1384781 = 519293) B519293
theorem B729425 : Blo 428775 729425 := bstep (se 2 (by rfl) ⟨273534, by rfl⟩ : syracuseStep 729425 = 547069) B547069
theorem B696689 : Blo 428775 696689 := bstep (se 2 (by rfl) ⟨261258, by rfl⟩ : syracuseStep 696689 = 522517) B522517
theorem B827761 : Blo 428775 827761 := bstep (se 2 (by rfl) ⟨310410, by rfl⟩ : syracuseStep 827761 = 620821) B620821
theorem B1450385 : Blo 428775 1450385 := bstep (se 2 (by rfl) ⟨543894, by rfl⟩ : syracuseStep 1450385 = 1087789) B1087789
theorem B729553 : Blo 428775 729553 := bstep (se 2 (by rfl) ⟨273582, by rfl⟩ : syracuseStep 729553 = 547165) B547165
theorem B729587 : Blo 428775 729587 := bstep (se 1 (by rfl) ⟨547190, by rfl⟩ : syracuseStep 729587 = 1094381) B1094381
theorem B729715 : Blo 428775 729715 := bstep (se 1 (by rfl) ⟨547286, by rfl⟩ : syracuseStep 729715 = 1094573) B1094573
theorem B729857 : Blo 428775 729857 := bstep (se 2 (by rfl) ⟨273696, by rfl⟩ : syracuseStep 729857 = 547393) B547393
theorem B729985 : Blo 428775 729985 := bstep (se 2 (by rfl) ⟨273744, by rfl⟩ : syracuseStep 729985 = 547489) B547489
theorem B730019 : Blo 428775 730019 := bstep (se 1 (by rfl) ⟨547514, by rfl⟩ : syracuseStep 730019 = 1095029) B1095029
theorem B1450925 : Blo 428775 1450925 := bstep (se 3 (by rfl) ⟨272048, by rfl⟩ : syracuseStep 1450925 = 544097) B544097
theorem B4891589 : Blo 428775 4891589 := bstep (se 4 (by rfl) ⟨458586, by rfl⟩ : syracuseStep 4891589 = 917173) B917173
theorem B1450979 : Blo 428775 1450979 := bstep (se 1 (by rfl) ⟨1088234, by rfl⟩ : syracuseStep 1450979 = 2176469) B2176469
theorem B730147 : Blo 428775 730147 := bstep (se 1 (by rfl) ⟨547610, by rfl⟩ : syracuseStep 730147 = 1095221) B1095221
theorem B1221713 : Blo 428775 1221713 := bstep (se 2 (by rfl) ⟨458142, by rfl⟩ : syracuseStep 1221713 = 916285) B916285
theorem B1090705 : Blo 428775 1090705 := bstep (se 2 (by rfl) ⟨409014, by rfl⟩ : syracuseStep 1090705 = 818029) B818029
theorem B730289 : Blo 428775 730289 := bstep (se 2 (by rfl) ⟨273858, by rfl⟩ : syracuseStep 730289 = 547717) B547717
theorem B1451249 : Blo 428775 1451249 := bstep (se 2 (by rfl) ⟨544218, by rfl⟩ : syracuseStep 1451249 = 1088437) B1088437
theorem B2204941 : Blo 428775 2204941 := bstep (se 3 (by rfl) ⟨413426, by rfl⟩ : syracuseStep 2204941 = 826853) B826853
theorem B2073869 : Blo 428775 2073869 := bstep (se 3 (by rfl) ⟨388850, by rfl⟩ : syracuseStep 2073869 = 777701) B777701
theorem B664979 : Blo 428775 664979 := bstep (se 1 (by rfl) ⟨498734, by rfl⟩ : syracuseStep 664979 = 997469) B997469
theorem B1090979 : Blo 428775 1090979 := bstep (se 1 (by rfl) ⟨818234, by rfl⟩ : syracuseStep 1090979 = 1636469) B1636469
theorem B2696753 : Blo 428775 2696753 := bstep (se 2 (by rfl) ⟨1011282, by rfl⟩ : syracuseStep 2696753 = 2022565) B2022565
theorem B1091171 : Blo 428775 1091171 := bstep (se 1 (by rfl) ⟨818378, by rfl⟩ : syracuseStep 1091171 = 1636757) B1636757
theorem B1451789 : Blo 428775 1451789 := bstep (se 3 (by rfl) ⟨272210, by rfl⟩ : syracuseStep 1451789 = 544421) B544421
theorem B1451843 : Blo 428775 1451843 := bstep (se 1 (by rfl) ⟨1088882, by rfl⟩ : syracuseStep 1451843 = 2177765) B2177765
theorem B1386371 : Blo 428775 1386371 := bstep (se 1 (by rfl) ⟨1039778, by rfl⟩ : syracuseStep 1386371 = 2079557) B2079557
theorem B1747021 : Blo 428775 1747021 := bstep (se 3 (by rfl) ⟨327566, by rfl⟩ : syracuseStep 1747021 = 655133) B655133
theorem B1452113 : Blo 428775 1452113 := bstep (se 2 (by rfl) ⟨544542, by rfl⟩ : syracuseStep 1452113 = 1089085) B1089085
theorem B6203789 : Blo 428775 6203789 := bstep (se 3 (by rfl) ⟨1163210, by rfl⟩ : syracuseStep 6203789 = 2326421) B2326421
theorem B1223171 : Blo 428775 1223171 := bstep (se 1 (by rfl) ⟨917378, by rfl⟩ : syracuseStep 1223171 = 1834757) B1834757
theorem B1092113 : Blo 428775 1092113 := bstep (se 2 (by rfl) ⟨409542, by rfl⟩ : syracuseStep 1092113 = 819085) B819085
theorem B1092163 : Blo 428775 1092163 := bstep (se 1 (by rfl) ⟨819122, by rfl⟩ : syracuseStep 1092163 = 1638245) B1638245
theorem B2075213 : Blo 428775 2075213 := bstep (se 3 (by rfl) ⟨389102, by rfl⟩ : syracuseStep 2075213 = 778205) B778205
theorem B1452653 : Blo 428775 1452653 := bstep (se 3 (by rfl) ⟨272372, by rfl⟩ : syracuseStep 1452653 = 544745) B544745
theorem B2173553 : Blo 428775 2173553 := bstep (se 2 (by rfl) ⟨815082, by rfl⟩ : syracuseStep 2173553 = 1630165) B1630165
theorem B1452707 : Blo 428775 1452707 := bstep (se 1 (by rfl) ⟨1089530, by rfl⟩ : syracuseStep 1452707 = 2179061) B2179061
theorem B1845965 : Blo 428775 1845965 := bstep (se 3 (by rfl) ⟨346118, by rfl⟩ : syracuseStep 1845965 = 692237) B692237
theorem B1092305 : Blo 428775 1092305 := bstep (se 2 (by rfl) ⟨409614, by rfl⟩ : syracuseStep 1092305 = 819229) B819229
theorem B1452977 : Blo 428775 1452977 := bstep (se 2 (by rfl) ⟨544866, by rfl⟩ : syracuseStep 1452977 = 1089733) B1089733
theorem B1846307 : Blo 428775 1846307 := bstep (se 1 (by rfl) ⟨1384730, by rfl⟩ : syracuseStep 1846307 = 2769461) B2769461
theorem B11775203 : Blo 428775 11775203 := bstep (se 1 (by rfl) ⟨8831402, by rfl⟩ : syracuseStep 11775203 = 17662805) B17662805
theorem B2764003 : Blo 428775 2764003 := bstep (se 1 (by rfl) ⟨2073002, by rfl⟩ : syracuseStep 2764003 = 4146005) B4146005
theorem B1223981 : Blo 428775 1223981 := bstep (se 3 (by rfl) ⟨229496, by rfl⟩ : syracuseStep 1223981 = 458993) B458993
theorem B5254541 : Blo 428775 5254541 := bstep (se 3 (by rfl) ⟨985226, by rfl⟩ : syracuseStep 5254541 = 1970453) B1970453
theorem B1453517 : Blo 428775 1453517 := bstep (se 3 (by rfl) ⟨272534, by rfl⟩ : syracuseStep 1453517 = 545069) B545069
theorem B1224173 : Blo 428775 1224173 := bstep (se 3 (by rfl) ⟨229532, by rfl⟩ : syracuseStep 1224173 = 459065) B459065
theorem B1453571 : Blo 428775 1453571 := bstep (se 1 (by rfl) ⟨1090178, by rfl⟩ : syracuseStep 1453571 = 2180357) B2180357
theorem B929411 : Blo 428775 929411 := bstep (se 1 (by rfl) ⟨697058, by rfl⟩ : syracuseStep 929411 = 1394117) B1394117
theorem B1093297 : Blo 428775 1093297 := bstep (se 2 (by rfl) ⟨409986, by rfl⟩ : syracuseStep 1093297 = 819973) B819973
theorem B5516981 : Blo 428775 5516981 := bstep (se 5 (by rfl) ⟨258608, by rfl⟩ : syracuseStep 5516981 = 517217) B517217
theorem B1453841 : Blo 428775 1453841 := bstep (se 2 (by rfl) ⟨545190, by rfl⟩ : syracuseStep 1453841 = 1090381) B1090381
theorem B2338723 : Blo 428775 2338723 := bstep (se 1 (by rfl) ⟨1754042, by rfl⟩ : syracuseStep 2338723 = 3508085) B3508085
theorem B1093571 : Blo 428775 1093571 := bstep (se 1 (by rfl) ⟨820178, by rfl⟩ : syracuseStep 1093571 = 1640357) B1640357
theorem B536611 : Blo 428775 536611 := bstep (se 1 (by rfl) ⟨402458, by rfl⟩ : syracuseStep 536611 = 804917) B804917
theorem B2175011 : Blo 428775 2175011 := bstep (se 1 (by rfl) ⟨1631258, by rfl⟩ : syracuseStep 2175011 = 3262517) B3262517
theorem B3092579 : Blo 428775 3092579 := bstep (se 1 (by rfl) ⟨2319434, by rfl⟩ : syracuseStep 3092579 = 4638869) B4638869
theorem B6697073 : Blo 428775 6697073 := bstep (se 2 (by rfl) ⟨2511402, by rfl⟩ : syracuseStep 6697073 = 5022805) B5022805
theorem B8269937 : Blo 428775 8269937 := bstep (se 2 (by rfl) ⟨3101226, by rfl⟩ : syracuseStep 8269937 = 6202453) B6202453
theorem B1093763 : Blo 428775 1093763 := bstep (se 1 (by rfl) ⟨820322, by rfl⟩ : syracuseStep 1093763 = 1640645) B1640645
theorem B1159373 : Blo 428775 1159373 := bstep (se 3 (by rfl) ⟨217382, by rfl⟩ : syracuseStep 1159373 = 434765) B434765
theorem B1454381 : Blo 428775 1454381 := bstep (se 3 (by rfl) ⟨272696, by rfl⟩ : syracuseStep 1454381 = 545393) B545393
theorem B1454435 : Blo 428775 1454435 := bstep (se 1 (by rfl) ⟨1090826, by rfl⟩ : syracuseStep 1454435 = 2181653) B2181653
theorem B1225165 : Blo 428775 1225165 := bstep (se 3 (by rfl) ⟨229718, by rfl⟩ : syracuseStep 1225165 = 459437) B459437
theorem B1454705 : Blo 428775 1454705 := bstep (se 2 (by rfl) ⟨545514, by rfl⟩ : syracuseStep 1454705 = 1091029) B1091029
theorem B2175821 : Blo 428775 2175821 := bstep (se 3 (by rfl) ⟨407966, by rfl⟩ : syracuseStep 2175821 = 815933) B815933
theorem B734179 : Blo 428775 734179 := bstep (se 1 (by rfl) ⟨550634, by rfl⟩ : syracuseStep 734179 = 1101269) B1101269
theorem B832547 : Blo 428775 832547 := bstep (se 1 (by rfl) ⟨624410, by rfl⟩ : syracuseStep 832547 = 1248821) B1248821
theorem B701489 : Blo 428775 701489 := bstep (se 2 (by rfl) ⟨263058, by rfl⟩ : syracuseStep 701489 = 526117) B526117
theorem B1094705 : Blo 428775 1094705 := bstep (se 2 (by rfl) ⟨410514, by rfl⟩ : syracuseStep 1094705 = 821029) B821029
theorem B1094755 : Blo 428775 1094755 := bstep (se 1 (by rfl) ⟨821066, by rfl⟩ : syracuseStep 1094755 = 1642133) B1642133
theorem B1455245 : Blo 428775 1455245 := bstep (se 3 (by rfl) ⟨272858, by rfl⟩ : syracuseStep 1455245 = 545717) B545717
theorem B1455299 : Blo 428775 1455299 := bstep (se 1 (by rfl) ⟨1091474, by rfl⟩ : syracuseStep 1455299 = 2182949) B2182949
theorem B1094897 : Blo 428775 1094897 := bstep (se 2 (by rfl) ⟨410586, by rfl⟩ : syracuseStep 1094897 = 821173) B821173
theorem B2209123 : Blo 428775 2209123 := bstep (se 1 (by rfl) ⟨1656842, by rfl⟩ : syracuseStep 2209123 = 3313685) B3313685
theorem B1455569 : Blo 428775 1455569 := bstep (se 2 (by rfl) ⟨545838, by rfl⟩ : syracuseStep 1455569 = 1091677) B1091677
theorem B734707 : Blo 428775 734707 := bstep (se 1 (by rfl) ⟨551030, by rfl⟩ : syracuseStep 734707 = 1102061) B1102061
theorem B1554061 : Blo 428775 1554061 := bstep (se 3 (by rfl) ⟨291386, by rfl⟩ : syracuseStep 1554061 = 582773) B582773
theorem B1161101 : Blo 428775 1161101 := bstep (se 3 (by rfl) ⟨217706, by rfl⟩ : syracuseStep 1161101 = 435413) B435413
theorem B2766797 : Blo 428775 2766797 := bstep (se 3 (by rfl) ⟨518774, by rfl⟩ : syracuseStep 2766797 = 1037549) B1037549
theorem B1456109 : Blo 428775 1456109 := bstep (se 3 (by rfl) ⟨273020, by rfl⟩ : syracuseStep 1456109 = 546041) B546041
theorem B1456163 : Blo 428775 1456163 := bstep (se 1 (by rfl) ⟨1092122, by rfl⟩ : syracuseStep 1456163 = 2184245) B2184245
theorem B1226897 : Blo 428775 1226897 := bstep (se 2 (by rfl) ⟨460086, by rfl⟩ : syracuseStep 1226897 = 920173) B920173
theorem B964817 : Blo 428775 964817 := bstep (se 2 (by rfl) ⟨361806, by rfl⟩ : syracuseStep 964817 = 723613) B723613
theorem B964835 : Blo 428775 964835 := bstep (se 1 (by rfl) ⟨723626, by rfl⟩ : syracuseStep 964835 = 1447253) B1447253
theorem B1456433 : Blo 428775 1456433 := bstep (se 2 (by rfl) ⟨546162, by rfl⟩ : syracuseStep 1456433 = 1092325) B1092325
theorem B1227089 : Blo 428775 1227089 := bstep (se 2 (by rfl) ⟨460158, by rfl⟩ : syracuseStep 1227089 = 920317) B920317
theorem B965105 : Blo 428775 965105 := bstep (se 2 (by rfl) ⟨361914, by rfl⟩ : syracuseStep 965105 = 723829) B723829
theorem B965123 : Blo 428775 965123 := bstep (se 1 (by rfl) ⟨723842, by rfl⟩ : syracuseStep 965123 = 1447685) B1447685
theorem B1161773 : Blo 428775 1161773 := bstep (se 3 (by rfl) ⟨217832, by rfl⟩ : syracuseStep 1161773 = 435665) B435665
theorem B5880433 : Blo 428775 5880433 := bstep (se 2 (by rfl) ⟨2205162, by rfl⟩ : syracuseStep 5880433 = 4410325) B4410325
theorem B2210417 : Blo 428775 2210417 := bstep (se 2 (by rfl) ⟨828906, by rfl⟩ : syracuseStep 2210417 = 1657813) B1657813
theorem B13318769 : Blo 428775 13318769 := bstep (se 2 (by rfl) ⟨4994538, by rfl⟩ : syracuseStep 13318769 = 9989077) B9989077
theorem B4897421 : Blo 428775 4897421 := bstep (se 3 (by rfl) ⟨918266, by rfl⟩ : syracuseStep 4897421 = 1836533) B1836533
theorem B4668101 : Blo 428775 4668101 := bstep (se 4 (by rfl) ⟨437634, by rfl⟩ : syracuseStep 4668101 = 875269) B875269
theorem B965393 : Blo 428775 965393 := bstep (se 2 (by rfl) ⟨362022, by rfl⟩ : syracuseStep 965393 = 724045) B724045
theorem B965411 : Blo 428775 965411 := bstep (se 1 (by rfl) ⟨724058, by rfl⟩ : syracuseStep 965411 = 1448117) B1448117
theorem B1456973 : Blo 428775 1456973 := bstep (se 3 (by rfl) ⟨273182, by rfl⟩ : syracuseStep 1456973 = 546365) B546365
theorem B1457027 : Blo 428775 1457027 := bstep (se 1 (by rfl) ⟨1092770, by rfl⟩ : syracuseStep 1457027 = 2185541) B2185541
theorem B965681 : Blo 428775 965681 := bstep (se 2 (by rfl) ⟨362130, by rfl⟩ : syracuseStep 965681 = 724261) B724261
theorem B965699 : Blo 428775 965699 := bstep (se 1 (by rfl) ⟨724274, by rfl⟩ : syracuseStep 965699 = 1448549) B1448549
theorem B1457297 : Blo 428775 1457297 := bstep (se 2 (by rfl) ⟨546486, by rfl⟩ : syracuseStep 1457297 = 1092973) B1092973
theorem B1228081 : Blo 428775 1228081 := bstep (se 2 (by rfl) ⟨460530, by rfl⟩ : syracuseStep 1228081 = 921061) B921061
theorem B965969 : Blo 428775 965969 := bstep (se 2 (by rfl) ⟨362238, by rfl⟩ : syracuseStep 965969 = 724477) B724477
theorem B965987 : Blo 428775 965987 := bstep (se 1 (by rfl) ⟨724490, by rfl⟩ : syracuseStep 965987 = 1448981) B1448981
theorem B3095921 : Blo 428775 3095921 := bstep (se 2 (by rfl) ⟨1160970, by rfl⟩ : syracuseStep 3095921 = 2321941) B2321941
theorem B1228355 : Blo 428775 1228355 := bstep (se 1 (by rfl) ⟨921266, by rfl⟩ : syracuseStep 1228355 = 1842533) B1842533
theorem B736867 : Blo 428775 736867 := bstep (se 1 (by rfl) ⟨552650, by rfl⟩ : syracuseStep 736867 = 1105301) B1105301
theorem B966257 : Blo 428775 966257 := bstep (se 2 (by rfl) ⟨362346, by rfl⟩ : syracuseStep 966257 = 724693) B724693
theorem B966275 : Blo 428775 966275 := bstep (se 1 (by rfl) ⟨724706, by rfl⟩ : syracuseStep 966275 = 1449413) B1449413
theorem B1457837 : Blo 428775 1457837 := bstep (se 3 (by rfl) ⟨273344, by rfl⟩ : syracuseStep 1457837 = 546689) B546689
theorem B2178737 : Blo 428775 2178737 := bstep (se 2 (by rfl) ⟨817026, by rfl⟩ : syracuseStep 2178737 = 1634053) B1634053
theorem B1457891 : Blo 428775 1457891 := bstep (se 1 (by rfl) ⟨1093418, by rfl⟩ : syracuseStep 1457891 = 2186837) B2186837
theorem B1228547 : Blo 428775 1228547 := bstep (se 1 (by rfl) ⟨921410, by rfl⟩ : syracuseStep 1228547 = 1842821) B1842821
theorem B966545 : Blo 428775 966545 := bstep (se 2 (by rfl) ⟨362454, by rfl⟩ : syracuseStep 966545 = 724909) B724909
theorem B966563 : Blo 428775 966563 := bstep (se 1 (by rfl) ⟨724922, by rfl⟩ : syracuseStep 966563 = 1449845) B1449845
theorem B1458161 : Blo 428775 1458161 := bstep (se 2 (by rfl) ⟨546810, by rfl⟩ : syracuseStep 1458161 = 1093621) B1093621
theorem B966833 : Blo 428775 966833 := bstep (se 2 (by rfl) ⟨362562, by rfl⟩ : syracuseStep 966833 = 725125) B725125
theorem B966851 : Blo 428775 966851 := bstep (se 1 (by rfl) ⟨725138, by rfl⟩ : syracuseStep 966851 = 1450277) B1450277
theorem B737633 : Blo 428775 737633 := bstep (se 2 (by rfl) ⟨276612, by rfl⟩ : syracuseStep 737633 = 553225) B553225
theorem B967121 : Blo 428775 967121 := bstep (se 2 (by rfl) ⟨362670, by rfl⟩ : syracuseStep 967121 = 725341) B725341
theorem B967139 : Blo 428775 967139 := bstep (se 1 (by rfl) ⟨725354, by rfl⟩ : syracuseStep 967139 = 1450709) B1450709
theorem B1458701 : Blo 428775 1458701 := bstep (se 3 (by rfl) ⟨273506, by rfl⟩ : syracuseStep 1458701 = 547013) B547013
theorem B1229357 : Blo 428775 1229357 := bstep (se 3 (by rfl) ⟨230504, by rfl⟩ : syracuseStep 1229357 = 461009) B461009
theorem B1458755 : Blo 428775 1458755 := bstep (se 1 (by rfl) ⟨1094066, by rfl⟩ : syracuseStep 1458755 = 2188133) B2188133
theorem B1229539 : Blo 428775 1229539 := bstep (se 1 (by rfl) ⟨922154, by rfl⟩ : syracuseStep 1229539 = 1844309) B1844309
theorem B967409 : Blo 428775 967409 := bstep (se 2 (by rfl) ⟨362778, by rfl⟩ : syracuseStep 967409 = 725557) B725557
theorem B967427 : Blo 428775 967427 := bstep (se 1 (by rfl) ⟨725570, by rfl⟩ : syracuseStep 967427 = 1451141) B1451141
theorem B1459025 : Blo 428775 1459025 := bstep (se 2 (by rfl) ⟨547134, by rfl⟩ : syracuseStep 1459025 = 1094269) B1094269
theorem B5522417 : Blo 428775 5522417 := bstep (se 2 (by rfl) ⟨2070906, by rfl⟩ : syracuseStep 5522417 = 4141813) B4141813
theorem B2999281 : Blo 428775 2999281 := bstep (se 2 (by rfl) ⟨1124730, by rfl⟩ : syracuseStep 2999281 = 2249461) B2249461
theorem B967697 : Blo 428775 967697 := bstep (se 2 (by rfl) ⟨362886, by rfl⟩ : syracuseStep 967697 = 725773) B725773
theorem B967715 : Blo 428775 967715 := bstep (se 1 (by rfl) ⟨725786, by rfl⟩ : syracuseStep 967715 = 1451573) B1451573
theorem B2180195 : Blo 428775 2180195 := bstep (se 1 (by rfl) ⟨1635146, by rfl⟩ : syracuseStep 2180195 = 3270293) B3270293
theorem B7554161 : Blo 428775 7554161 := bstep (se 2 (by rfl) ⟨2832810, by rfl⟩ : syracuseStep 7554161 = 5665621) B5665621
theorem B1230029 : Blo 428775 1230029 := bstep (se 3 (by rfl) ⟨230630, by rfl⟩ : syracuseStep 1230029 = 461261) B461261
theorem B967985 : Blo 428775 967985 := bstep (se 2 (by rfl) ⟨362994, by rfl⟩ : syracuseStep 967985 = 725989) B725989
theorem B968003 : Blo 428775 968003 := bstep (se 1 (by rfl) ⟨726002, by rfl⟩ : syracuseStep 968003 = 1452005) B1452005
theorem B2934085 : Blo 428775 2934085 := bstep (se 4 (by rfl) ⟨275070, by rfl⟩ : syracuseStep 2934085 = 550141) B550141
theorem B1885517 : Blo 428775 1885517 := bstep (se 3 (by rfl) ⟨353534, by rfl⟩ : syracuseStep 1885517 = 707069) B707069
theorem B1459565 : Blo 428775 1459565 := bstep (se 3 (by rfl) ⟨273668, by rfl⟩ : syracuseStep 1459565 = 547337) B547337
theorem B1459619 : Blo 428775 1459619 := bstep (se 1 (by rfl) ⟨1094714, by rfl⟩ : syracuseStep 1459619 = 2189429) B2189429
theorem B4900337 : Blo 428775 4900337 := bstep (se 2 (by rfl) ⟨1837626, by rfl⟩ : syracuseStep 4900337 = 3675253) B3675253
theorem B968273 : Blo 428775 968273 := bstep (se 2 (by rfl) ⟨363102, by rfl⟩ : syracuseStep 968273 = 726205) B726205
theorem B968291 : Blo 428775 968291 := bstep (se 1 (by rfl) ⟨726218, by rfl⟩ : syracuseStep 968291 = 1452437) B1452437
theorem B1033859 : Blo 428775 1033859 := bstep (se 1 (by rfl) ⟨775394, by rfl⟩ : syracuseStep 1033859 = 1550789) B1550789
theorem B1459889 : Blo 428775 1459889 := bstep (se 2 (by rfl) ⟨547458, by rfl⟩ : syracuseStep 1459889 = 1094917) B1094917
theorem B2475845 : Blo 428775 2475845 := bstep (se 4 (by rfl) ⟨232110, by rfl⟩ : syracuseStep 2475845 = 464221) B464221
theorem B2934605 : Blo 428775 2934605 := bstep (se 3 (by rfl) ⟨550238, by rfl⟩ : syracuseStep 2934605 = 1100477) B1100477
theorem B968561 : Blo 428775 968561 := bstep (se 2 (by rfl) ⟨363210, by rfl⟩ : syracuseStep 968561 = 726421) B726421
theorem B968579 : Blo 428775 968579 := bstep (se 1 (by rfl) ⟨726434, by rfl⟩ : syracuseStep 968579 = 1452869) B1452869
theorem B2181005 : Blo 428775 2181005 := bstep (se 3 (by rfl) ⟨408938, by rfl⟩ : syracuseStep 2181005 = 817877) B817877
theorem B1034147 : Blo 428775 1034147 := bstep (se 1 (by rfl) ⟨775610, by rfl⟩ : syracuseStep 1034147 = 1551221) B1551221
theorem B968849 : Blo 428775 968849 := bstep (se 2 (by rfl) ⟨363318, by rfl⟩ : syracuseStep 968849 = 726637) B726637
theorem B968867 : Blo 428775 968867 := bstep (se 1 (by rfl) ⟨726650, by rfl⟩ : syracuseStep 968867 = 1453301) B1453301
theorem B739523 : Blo 428775 739523 := bstep (se 1 (by rfl) ⟨554642, by rfl⟩ : syracuseStep 739523 = 1109285) B1109285
theorem B1460429 : Blo 428775 1460429 := bstep (se 3 (by rfl) ⟨273830, by rfl⟩ : syracuseStep 1460429 = 547661) B547661
theorem B3786979 : Blo 428775 3786979 := bstep (se 1 (by rfl) ⟨2840234, by rfl⟩ : syracuseStep 3786979 = 5680469) B5680469
theorem B542963 : Blo 428775 542963 := bstep (se 1 (by rfl) ⟨407222, by rfl⟩ : syracuseStep 542963 = 814445) B814445
theorem B1460483 : Blo 428775 1460483 := bstep (se 1 (by rfl) ⟨1095362, by rfl⟩ : syracuseStep 1460483 = 2190725) B2190725
theorem B1231213 : Blo 428775 1231213 := bstep (se 3 (by rfl) ⟨230852, by rfl⟩ : syracuseStep 1231213 = 461705) B461705
theorem B969137 : Blo 428775 969137 := bstep (se 2 (by rfl) ⟨363426, by rfl⟩ : syracuseStep 969137 = 726853) B726853
theorem B969155 : Blo 428775 969155 := bstep (se 1 (by rfl) ⟨726866, by rfl⟩ : syracuseStep 969155 = 1453733) B1453733
theorem B969425 : Blo 428775 969425 := bstep (se 2 (by rfl) ⟨363534, by rfl⟩ : syracuseStep 969425 = 727069) B727069
theorem B969443 : Blo 428775 969443 := bstep (se 1 (by rfl) ⟨727082, by rfl⟩ : syracuseStep 969443 = 1454165) B1454165
theorem B1034993 : Blo 428775 1034993 := bstep (se 2 (by rfl) ⟨388122, by rfl⟩ : syracuseStep 1034993 = 776245) B776245
theorem B1035089 : Blo 428775 1035089 := bstep (se 2 (by rfl) ⟨388158, by rfl⟩ : syracuseStep 1035089 = 776317) B776317
theorem B871345 : Blo 428775 871345 := bstep (se 2 (by rfl) ⟨326754, by rfl⟩ : syracuseStep 871345 = 653509) B653509
theorem B543667 : Blo 428775 543667 := bstep (se 1 (by rfl) ⟨407750, by rfl⟩ : syracuseStep 543667 = 815501) B815501
theorem B740321 : Blo 428775 740321 := bstep (se 2 (by rfl) ⟨277620, by rfl⟩ : syracuseStep 740321 = 555241) B555241
theorem B969713 : Blo 428775 969713 := bstep (se 2 (by rfl) ⟨363642, by rfl⟩ : syracuseStep 969713 = 727285) B727285
theorem B969731 : Blo 428775 969731 := bstep (se 1 (by rfl) ⟨727298, by rfl⟩ : syracuseStep 969731 = 1454597) B1454597
theorem B1035281 : Blo 428775 1035281 := bstep (se 2 (by rfl) ⟨388230, by rfl⟩ : syracuseStep 1035281 = 776461) B776461
theorem B543763 : Blo 428775 543763 := bstep (se 1 (by rfl) ⟨407822, by rfl⟩ : syracuseStep 543763 = 815645) B815645
theorem B970001 : Blo 428775 970001 := bstep (se 2 (by rfl) ⟨363750, by rfl⟩ : syracuseStep 970001 = 727501) B727501
theorem B970019 : Blo 428775 970019 := bstep (se 1 (by rfl) ⟨727514, by rfl⟩ : syracuseStep 970019 = 1455029) B1455029
theorem B8539505 : Blo 428775 8539505 := bstep (se 2 (by rfl) ⟨3202314, by rfl⟩ : syracuseStep 8539505 = 6404629) B6404629
theorem B1232273 : Blo 428775 1232273 := bstep (se 2 (by rfl) ⟨462102, by rfl⟩ : syracuseStep 1232273 = 924205) B924205
theorem B544259 : Blo 428775 544259 := bstep (se 1 (by rfl) ⟨408194, by rfl⟩ : syracuseStep 544259 = 816389) B816389
theorem B970289 : Blo 428775 970289 := bstep (se 2 (by rfl) ⟨363858, by rfl⟩ : syracuseStep 970289 = 727717) B727717
theorem B970307 : Blo 428775 970307 := bstep (se 1 (by rfl) ⟨727730, by rfl⟩ : syracuseStep 970307 = 1455461) B1455461
theorem B773923 : Blo 428775 773923 := bstep (se 1 (by rfl) ⟨580442, by rfl⟩ : syracuseStep 773923 = 1160885) B1160885
theorem B2477873 : Blo 428775 2477873 := bstep (se 2 (by rfl) ⟨929202, by rfl⟩ : syracuseStep 2477873 = 1858405) B1858405
theorem B970577 : Blo 428775 970577 := bstep (se 2 (by rfl) ⟨363966, by rfl⟩ : syracuseStep 970577 = 727933) B727933
theorem B970595 : Blo 428775 970595 := bstep (se 1 (by rfl) ⟨727946, by rfl⟩ : syracuseStep 970595 = 1455893) B1455893
theorem B643169 : Blo 428775 643169 := bstep (se 2 (by rfl) ⟨241188, by rfl⟩ : syracuseStep 643169 = 482377) B482377
theorem B970865 : Blo 428775 970865 := bstep (se 2 (by rfl) ⟨364074, by rfl⟩ : syracuseStep 970865 = 728149) B728149
theorem B643187 : Blo 428775 643187 := bstep (se 1 (by rfl) ⟨482390, by rfl⟩ : syracuseStep 643187 = 964781) B964781
theorem B970883 : Blo 428775 970883 := bstep (se 1 (by rfl) ⟨728162, by rfl⟩ : syracuseStep 970883 = 1456325) B1456325
theorem B643217 : Blo 428775 643217 := bstep (se 2 (by rfl) ⟨241206, by rfl⟩ : syracuseStep 643217 = 482413) B482413
theorem B1036433 : Blo 428775 1036433 := bstep (se 2 (by rfl) ⟨388662, by rfl⟩ : syracuseStep 1036433 = 777325) B777325
theorem B643235 : Blo 428775 643235 := bstep (se 1 (by rfl) ⟨482426, by rfl⟩ : syracuseStep 643235 = 964853) B964853
theorem B643265 : Blo 428775 643265 := bstep (se 2 (by rfl) ⟨241224, by rfl⟩ : syracuseStep 643265 = 482449) B482449
theorem B544963 : Blo 428775 544963 := bstep (se 1 (by rfl) ⟨408722, by rfl⟩ : syracuseStep 544963 = 817445) B817445
theorem B643283 : Blo 428775 643283 := bstep (se 1 (by rfl) ⟨482462, by rfl⟩ : syracuseStep 643283 = 964925) B964925
theorem B643313 : Blo 428775 643313 := bstep (se 2 (by rfl) ⟨241242, by rfl⟩ : syracuseStep 643313 = 482485) B482485
theorem B2937073 : Blo 428775 2937073 := bstep (se 2 (by rfl) ⟨1101402, by rfl⟩ : syracuseStep 2937073 = 2202805) B2202805
theorem B643331 : Blo 428775 643331 := bstep (se 1 (by rfl) ⟨482498, by rfl⟩ : syracuseStep 643331 = 964997) B964997
theorem B643361 : Blo 428775 643361 := bstep (se 2 (by rfl) ⟨241260, by rfl⟩ : syracuseStep 643361 = 482521) B482521
theorem B545059 : Blo 428775 545059 := bstep (se 1 (by rfl) ⟨408794, by rfl⟩ : syracuseStep 545059 = 817589) B817589
theorem B643379 : Blo 428775 643379 := bstep (se 1 (by rfl) ⟨482534, by rfl⟩ : syracuseStep 643379 = 965069) B965069
theorem B643409 : Blo 428775 643409 := bstep (se 2 (by rfl) ⟨241278, by rfl⟩ : syracuseStep 643409 = 482557) B482557
theorem B643427 : Blo 428775 643427 := bstep (se 1 (by rfl) ⟨482570, by rfl⟩ : syracuseStep 643427 = 965141) B965141
theorem B643457 : Blo 428775 643457 := bstep (se 2 (by rfl) ⟨241296, by rfl⟩ : syracuseStep 643457 = 482593) B482593
theorem B971153 : Blo 428775 971153 := bstep (se 2 (by rfl) ⟨364182, by rfl⟩ : syracuseStep 971153 = 728365) B728365
theorem B643475 : Blo 428775 643475 := bstep (se 1 (by rfl) ⟨482606, by rfl⟩ : syracuseStep 643475 = 965213) B965213
theorem B971171 : Blo 428775 971171 := bstep (se 1 (by rfl) ⟨728378, by rfl⟩ : syracuseStep 971171 = 1456757) B1456757
theorem B643505 : Blo 428775 643505 := bstep (se 2 (by rfl) ⟨241314, by rfl⟩ : syracuseStep 643505 = 482629) B482629
theorem B643523 : Blo 428775 643523 := bstep (se 1 (by rfl) ⟨482642, by rfl⟩ : syracuseStep 643523 = 965285) B965285
theorem B643553 : Blo 428775 643553 := bstep (se 2 (by rfl) ⟨241332, by rfl⟩ : syracuseStep 643553 = 482665) B482665
theorem B4149731 : Blo 428775 4149731 := bstep (se 1 (by rfl) ⟨3112298, by rfl⟩ : syracuseStep 4149731 = 6224597) B6224597
theorem B643571 : Blo 428775 643571 := bstep (se 1 (by rfl) ⟨482678, by rfl⟩ : syracuseStep 643571 = 965357) B965357
theorem B643601 : Blo 428775 643601 := bstep (se 2 (by rfl) ⟨241350, by rfl⟩ : syracuseStep 643601 = 482701) B482701
theorem B643619 : Blo 428775 643619 := bstep (se 1 (by rfl) ⟨482714, by rfl⟩ : syracuseStep 643619 = 965429) B965429
theorem B643649 : Blo 428775 643649 := bstep (se 2 (by rfl) ⟨241368, by rfl⟩ : syracuseStep 643649 = 482737) B482737
theorem B610897 : Blo 428775 610897 := bstep (se 2 (by rfl) ⟨229086, by rfl⟩ : syracuseStep 610897 = 458173) B458173
theorem B643667 : Blo 428775 643667 := bstep (se 1 (by rfl) ⟨482750, by rfl⟩ : syracuseStep 643667 = 965501) B965501
theorem B643697 : Blo 428775 643697 := bstep (se 2 (by rfl) ⟨241386, by rfl⟩ : syracuseStep 643697 = 482773) B482773
theorem B643715 : Blo 428775 643715 := bstep (se 1 (by rfl) ⟨482786, by rfl⟩ : syracuseStep 643715 = 965573) B965573
theorem B643745 : Blo 428775 643745 := bstep (se 2 (by rfl) ⟨241404, by rfl⟩ : syracuseStep 643745 = 482809) B482809
theorem B610993 : Blo 428775 610993 := bstep (se 2 (by rfl) ⟨229122, by rfl⟩ : syracuseStep 610993 = 458245) B458245
theorem B971441 : Blo 428775 971441 := bstep (se 2 (by rfl) ⟨364290, by rfl⟩ : syracuseStep 971441 = 728581) B728581
theorem B643763 : Blo 428775 643763 := bstep (se 1 (by rfl) ⟨482822, by rfl⟩ : syracuseStep 643763 = 965645) B965645
theorem B971459 : Blo 428775 971459 := bstep (se 1 (by rfl) ⟨728594, by rfl⟩ : syracuseStep 971459 = 1457189) B1457189
theorem B643793 : Blo 428775 643793 := bstep (se 2 (by rfl) ⟨241422, by rfl⟩ : syracuseStep 643793 = 482845) B482845
theorem B643811 : Blo 428775 643811 := bstep (se 1 (by rfl) ⟨482858, by rfl⟩ : syracuseStep 643811 = 965717) B965717
theorem B2183921 : Blo 428775 2183921 := bstep (se 2 (by rfl) ⟨818970, by rfl⟩ : syracuseStep 2183921 = 1637941) B1637941
theorem B643841 : Blo 428775 643841 := bstep (se 2 (by rfl) ⟨241440, by rfl⟩ : syracuseStep 643841 = 482881) B482881
theorem B1168141 : Blo 428775 1168141 := bstep (se 3 (by rfl) ⟨219026, by rfl⟩ : syracuseStep 1168141 = 438053) B438053
theorem B643859 : Blo 428775 643859 := bstep (se 1 (by rfl) ⟨482894, by rfl⟩ : syracuseStep 643859 = 965789) B965789
theorem B545555 : Blo 428775 545555 := bstep (se 1 (by rfl) ⟨409166, by rfl⟩ : syracuseStep 545555 = 818333) B818333
theorem B643889 : Blo 428775 643889 := bstep (se 2 (by rfl) ⟨241458, by rfl⟩ : syracuseStep 643889 = 482917) B482917
theorem B643907 : Blo 428775 643907 := bstep (se 1 (by rfl) ⟨482930, by rfl⟩ : syracuseStep 643907 = 965861) B965861
theorem B1168195 : Blo 428775 1168195 := bstep (se 1 (by rfl) ⟨876146, by rfl⟩ : syracuseStep 1168195 = 1752293) B1752293
theorem B643937 : Blo 428775 643937 := bstep (se 2 (by rfl) ⟨241476, by rfl⟩ : syracuseStep 643937 = 482953) B482953
theorem B643955 : Blo 428775 643955 := bstep (se 1 (by rfl) ⟨482966, by rfl⟩ : syracuseStep 643955 = 965933) B965933
theorem B5526413 : Blo 428775 5526413 := bstep (se 3 (by rfl) ⟨1036202, by rfl⟩ : syracuseStep 5526413 = 2072405) B2072405
theorem B643985 : Blo 428775 643985 := bstep (se 2 (by rfl) ⟨241494, by rfl⟩ : syracuseStep 643985 = 482989) B482989
theorem B644003 : Blo 428775 644003 := bstep (se 1 (by rfl) ⟨483002, by rfl⟩ : syracuseStep 644003 = 966005) B966005
theorem B644033 : Blo 428775 644033 := bstep (se 2 (by rfl) ⟨241512, by rfl⟩ : syracuseStep 644033 = 483025) B483025
theorem B971729 : Blo 428775 971729 := bstep (se 2 (by rfl) ⟨364398, by rfl⟩ : syracuseStep 971729 = 728797) B728797
theorem B644051 : Blo 428775 644051 := bstep (se 1 (by rfl) ⟨483038, by rfl⟩ : syracuseStep 644051 = 966077) B966077
theorem B971747 : Blo 428775 971747 := bstep (se 1 (by rfl) ⟨728810, by rfl⟩ : syracuseStep 971747 = 1457621) B1457621
theorem B644081 : Blo 428775 644081 := bstep (se 2 (by rfl) ⟨241530, by rfl⟩ : syracuseStep 644081 = 483061) B483061
theorem B644099 : Blo 428775 644099 := bstep (se 1 (by rfl) ⟨483074, by rfl⟩ : syracuseStep 644099 = 966149) B966149
theorem B644129 : Blo 428775 644129 := bstep (se 2 (by rfl) ⟨241548, by rfl⟩ : syracuseStep 644129 = 483097) B483097
theorem B644147 : Blo 428775 644147 := bstep (se 1 (by rfl) ⟨483110, by rfl⟩ : syracuseStep 644147 = 966221) B966221
theorem B7492661 : Blo 428775 7492661 := bstep (se 5 (by rfl) ⟨351218, by rfl⟩ : syracuseStep 7492661 = 702437) B702437
theorem B644177 : Blo 428775 644177 := bstep (se 2 (by rfl) ⟨241566, by rfl⟩ : syracuseStep 644177 = 483133) B483133
theorem B644195 : Blo 428775 644195 := bstep (se 1 (by rfl) ⟨483146, by rfl⟩ : syracuseStep 644195 = 966293) B966293
theorem B644225 : Blo 428775 644225 := bstep (se 2 (by rfl) ⟨241584, by rfl⟩ : syracuseStep 644225 = 483169) B483169
theorem B644243 : Blo 428775 644243 := bstep (se 1 (by rfl) ⟨483182, by rfl⟩ : syracuseStep 644243 = 966365) B966365
theorem B611489 : Blo 428775 611489 := bstep (se 2 (by rfl) ⟨229308, by rfl⟩ : syracuseStep 611489 = 458617) B458617
theorem B644273 : Blo 428775 644273 := bstep (se 2 (by rfl) ⟨241602, by rfl⟩ : syracuseStep 644273 = 483205) B483205
theorem B644291 : Blo 428775 644291 := bstep (se 1 (by rfl) ⟨483218, by rfl⟩ : syracuseStep 644291 = 966437) B966437
theorem B644321 : Blo 428775 644321 := bstep (se 2 (by rfl) ⟨241620, by rfl⟩ : syracuseStep 644321 = 483241) B483241
theorem B873713 : Blo 428775 873713 := bstep (se 2 (by rfl) ⟨327642, by rfl⟩ : syracuseStep 873713 = 655285) B655285
theorem B972017 : Blo 428775 972017 := bstep (se 2 (by rfl) ⟨364506, by rfl⟩ : syracuseStep 972017 = 729013) B729013
theorem B644339 : Blo 428775 644339 := bstep (se 1 (by rfl) ⟨483254, by rfl⟩ : syracuseStep 644339 = 966509) B966509
theorem B972035 : Blo 428775 972035 := bstep (se 1 (by rfl) ⟨729026, by rfl⟩ : syracuseStep 972035 = 1458053) B1458053
theorem B644369 : Blo 428775 644369 := bstep (se 2 (by rfl) ⟨241638, by rfl⟩ : syracuseStep 644369 = 483277) B483277
theorem B644387 : Blo 428775 644387 := bstep (se 1 (by rfl) ⟨483290, by rfl⟩ : syracuseStep 644387 = 966581) B966581
theorem B644417 : Blo 428775 644417 := bstep (se 2 (by rfl) ⟨241656, by rfl⟩ : syracuseStep 644417 = 483313) B483313
theorem B644435 : Blo 428775 644435 := bstep (se 1 (by rfl) ⟨483326, by rfl⟩ : syracuseStep 644435 = 966653) B966653
theorem B644465 : Blo 428775 644465 := bstep (se 2 (by rfl) ⟨241674, by rfl⟩ : syracuseStep 644465 = 483349) B483349
theorem B644483 : Blo 428775 644483 := bstep (se 1 (by rfl) ⟨483362, by rfl⟩ : syracuseStep 644483 = 966725) B966725
theorem B644513 : Blo 428775 644513 := bstep (se 2 (by rfl) ⟨241692, by rfl⟩ : syracuseStep 644513 = 483385) B483385
theorem B644531 : Blo 428775 644531 := bstep (se 1 (by rfl) ⟨483398, by rfl⟩ : syracuseStep 644531 = 966797) B966797
theorem B644561 : Blo 428775 644561 := bstep (se 2 (by rfl) ⟨241710, by rfl⟩ : syracuseStep 644561 = 483421) B483421
theorem B546259 : Blo 428775 546259 := bstep (se 1 (by rfl) ⟨409694, by rfl⟩ : syracuseStep 546259 = 819389) B819389
theorem B644579 : Blo 428775 644579 := bstep (se 1 (by rfl) ⟨483434, by rfl⟩ : syracuseStep 644579 = 966869) B966869
theorem B644609 : Blo 428775 644609 := bstep (se 2 (by rfl) ⟨241728, by rfl⟩ : syracuseStep 644609 = 483457) B483457
theorem B972305 : Blo 428775 972305 := bstep (se 2 (by rfl) ⟨364614, by rfl⟩ : syracuseStep 972305 = 729229) B729229
theorem B644627 : Blo 428775 644627 := bstep (se 1 (by rfl) ⟨483470, by rfl⟩ : syracuseStep 644627 = 966941) B966941
theorem B972323 : Blo 428775 972323 := bstep (se 1 (by rfl) ⟨729242, by rfl⟩ : syracuseStep 972323 = 1458485) B1458485
theorem B644657 : Blo 428775 644657 := bstep (se 2 (by rfl) ⟨241746, by rfl⟩ : syracuseStep 644657 = 483493) B483493
theorem B546355 : Blo 428775 546355 := bstep (se 1 (by rfl) ⟨409766, by rfl⟩ : syracuseStep 546355 = 819533) B819533
theorem B644675 : Blo 428775 644675 := bstep (se 1 (by rfl) ⟨483506, by rfl⟩ : syracuseStep 644675 = 967013) B967013
theorem B644705 : Blo 428775 644705 := bstep (se 2 (by rfl) ⟨241764, by rfl⟩ : syracuseStep 644705 = 483529) B483529
theorem B644723 : Blo 428775 644723 := bstep (se 1 (by rfl) ⟨483542, by rfl⟩ : syracuseStep 644723 = 967085) B967085
theorem B644753 : Blo 428775 644753 := bstep (se 2 (by rfl) ⟨241782, by rfl⟩ : syracuseStep 644753 = 483565) B483565
theorem B644771 : Blo 428775 644771 := bstep (se 1 (by rfl) ⟨483578, by rfl⟩ : syracuseStep 644771 = 967157) B967157
theorem B644801 : Blo 428775 644801 := bstep (se 2 (by rfl) ⟨241800, by rfl⟩ : syracuseStep 644801 = 483601) B483601
theorem B644819 : Blo 428775 644819 := bstep (se 1 (by rfl) ⟨483614, by rfl⟩ : syracuseStep 644819 = 967229) B967229
theorem B644849 : Blo 428775 644849 := bstep (se 2 (by rfl) ⟨241818, by rfl⟩ : syracuseStep 644849 = 483637) B483637
theorem B644867 : Blo 428775 644867 := bstep (se 1 (by rfl) ⟨483650, by rfl⟩ : syracuseStep 644867 = 967301) B967301
theorem B2807557 : Blo 428775 2807557 := bstep (se 4 (by rfl) ⟨263208, by rfl⟩ : syracuseStep 2807557 = 526417) B526417
theorem B2447117 : Blo 428775 2447117 := bstep (se 3 (by rfl) ⟨458834, by rfl⟩ : syracuseStep 2447117 = 917669) B917669
theorem B644897 : Blo 428775 644897 := bstep (se 2 (by rfl) ⟨241836, by rfl⟩ : syracuseStep 644897 = 483673) B483673
theorem B972593 : Blo 428775 972593 := bstep (se 2 (by rfl) ⟨364722, by rfl⟩ : syracuseStep 972593 = 729445) B729445
theorem B644915 : Blo 428775 644915 := bstep (se 1 (by rfl) ⟨483686, by rfl⟩ : syracuseStep 644915 = 967373) B967373
theorem B972611 : Blo 428775 972611 := bstep (se 1 (by rfl) ⟨729458, by rfl⟩ : syracuseStep 972611 = 1458917) B1458917
theorem B644945 : Blo 428775 644945 := bstep (se 2 (by rfl) ⟨241854, by rfl⟩ : syracuseStep 644945 = 483709) B483709
theorem B644963 : Blo 428775 644963 := bstep (se 1 (by rfl) ⟨483722, by rfl⟩ : syracuseStep 644963 = 967445) B967445
theorem B644993 : Blo 428775 644993 := bstep (se 2 (by rfl) ⟨241872, by rfl⟩ : syracuseStep 644993 = 483745) B483745
theorem B645011 : Blo 428775 645011 := bstep (se 1 (by rfl) ⟨483758, by rfl⟩ : syracuseStep 645011 = 967517) B967517
theorem B645041 : Blo 428775 645041 := bstep (se 2 (by rfl) ⟨241890, by rfl⟩ : syracuseStep 645041 = 483781) B483781
theorem B645059 : Blo 428775 645059 := bstep (se 1 (by rfl) ⟨483794, by rfl⟩ : syracuseStep 645059 = 967589) B967589
theorem B645089 : Blo 428775 645089 := bstep (se 2 (by rfl) ⟨241908, by rfl⟩ : syracuseStep 645089 = 483817) B483817
theorem B645107 : Blo 428775 645107 := bstep (se 1 (by rfl) ⟨483830, by rfl⟩ : syracuseStep 645107 = 967661) B967661
theorem B612355 : Blo 428775 612355 := bstep (se 1 (by rfl) ⟨459266, by rfl⟩ : syracuseStep 612355 = 918533) B918533
theorem B645137 : Blo 428775 645137 := bstep (se 2 (by rfl) ⟨241926, by rfl⟩ : syracuseStep 645137 = 483853) B483853
theorem B645155 : Blo 428775 645155 := bstep (se 1 (by rfl) ⟨483866, by rfl⟩ : syracuseStep 645155 = 967733) B967733
theorem B546851 : Blo 428775 546851 := bstep (se 1 (by rfl) ⟨410138, by rfl⟩ : syracuseStep 546851 = 820277) B820277
theorem B5494837 : Blo 428775 5494837 := bstep (se 5 (by rfl) ⟨257570, by rfl⟩ : syracuseStep 5494837 = 515141) B515141
theorem B645185 : Blo 428775 645185 := bstep (se 2 (by rfl) ⟨241944, by rfl⟩ : syracuseStep 645185 = 483889) B483889
theorem B972881 : Blo 428775 972881 := bstep (se 2 (by rfl) ⟨364830, by rfl⟩ : syracuseStep 972881 = 729661) B729661
theorem B645203 : Blo 428775 645203 := bstep (se 1 (by rfl) ⟨483902, by rfl⟩ : syracuseStep 645203 = 967805) B967805
theorem B612451 : Blo 428775 612451 := bstep (se 1 (by rfl) ⟨459338, by rfl⟩ : syracuseStep 612451 = 918677) B918677
theorem B972899 : Blo 428775 972899 := bstep (se 1 (by rfl) ⟨729674, by rfl⟩ : syracuseStep 972899 = 1459349) B1459349
theorem B645233 : Blo 428775 645233 := bstep (se 2 (by rfl) ⟨241962, by rfl⟩ : syracuseStep 645233 = 483925) B483925
theorem B645251 : Blo 428775 645251 := bstep (se 1 (by rfl) ⟨483938, by rfl⟩ : syracuseStep 645251 = 967877) B967877
theorem B645281 : Blo 428775 645281 := bstep (se 2 (by rfl) ⟨241980, by rfl⟩ : syracuseStep 645281 = 483961) B483961
theorem B2185379 : Blo 428775 2185379 := bstep (se 1 (by rfl) ⟨1639034, by rfl⟩ : syracuseStep 2185379 = 3278069) B3278069
theorem B645299 : Blo 428775 645299 := bstep (se 1 (by rfl) ⟨483974, by rfl⟩ : syracuseStep 645299 = 967949) B967949
theorem B645329 : Blo 428775 645329 := bstep (se 2 (by rfl) ⟨241998, by rfl⟩ : syracuseStep 645329 = 483997) B483997
theorem B645347 : Blo 428775 645347 := bstep (se 1 (by rfl) ⟨484010, by rfl⟩ : syracuseStep 645347 = 968021) B968021
theorem B645377 : Blo 428775 645377 := bstep (se 2 (by rfl) ⟨242016, by rfl⟩ : syracuseStep 645377 = 484033) B484033
theorem B645395 : Blo 428775 645395 := bstep (se 1 (by rfl) ⟨484046, by rfl⟩ : syracuseStep 645395 = 968093) B968093
theorem B645425 : Blo 428775 645425 := bstep (se 2 (by rfl) ⟨242034, by rfl⟩ : syracuseStep 645425 = 484069) B484069
theorem B645443 : Blo 428775 645443 := bstep (se 1 (by rfl) ⟨484082, by rfl⟩ : syracuseStep 645443 = 968165) B968165
theorem B645473 : Blo 428775 645473 := bstep (se 2 (by rfl) ⟨242052, by rfl⟩ : syracuseStep 645473 = 484105) B484105
theorem B973169 : Blo 428775 973169 := bstep (se 2 (by rfl) ⟨364938, by rfl⟩ : syracuseStep 973169 = 729877) B729877
theorem B645491 : Blo 428775 645491 := bstep (se 1 (by rfl) ⟨484118, by rfl⟩ : syracuseStep 645491 = 968237) B968237
theorem B973187 : Blo 428775 973187 := bstep (se 1 (by rfl) ⟨729890, by rfl⟩ : syracuseStep 973187 = 1459781) B1459781
theorem B645521 : Blo 428775 645521 := bstep (se 2 (by rfl) ⟨242070, by rfl⟩ : syracuseStep 645521 = 484141) B484141
theorem B645539 : Blo 428775 645539 := bstep (se 1 (by rfl) ⟨484154, by rfl⟩ : syracuseStep 645539 = 968309) B968309
theorem B645569 : Blo 428775 645569 := bstep (se 2 (by rfl) ⟨242088, by rfl⟩ : syracuseStep 645569 = 484177) B484177
theorem B645587 : Blo 428775 645587 := bstep (se 1 (by rfl) ⟨484190, by rfl⟩ : syracuseStep 645587 = 968381) B968381
theorem B645617 : Blo 428775 645617 := bstep (se 2 (by rfl) ⟨242106, by rfl⟩ : syracuseStep 645617 = 484213) B484213
theorem B645635 : Blo 428775 645635 := bstep (se 1 (by rfl) ⟨484226, by rfl⟩ : syracuseStep 645635 = 968453) B968453
theorem B645665 : Blo 428775 645665 := bstep (se 2 (by rfl) ⟨242124, by rfl⟩ : syracuseStep 645665 = 484249) B484249
theorem B1628707 : Blo 428775 1628707 := bstep (se 1 (by rfl) ⟨1221530, by rfl⟩ : syracuseStep 1628707 = 2443061) B2443061
theorem B645683 : Blo 428775 645683 := bstep (se 1 (by rfl) ⟨484262, by rfl⟩ : syracuseStep 645683 = 968525) B968525
theorem B645713 : Blo 428775 645713 := bstep (se 2 (by rfl) ⟨242142, by rfl⟩ : syracuseStep 645713 = 484285) B484285
theorem B612947 : Blo 428775 612947 := bstep (se 1 (by rfl) ⟨459710, by rfl⟩ : syracuseStep 612947 = 919421) B919421
theorem B645731 : Blo 428775 645731 := bstep (se 1 (by rfl) ⟨484298, by rfl⟩ : syracuseStep 645731 = 968597) B968597
theorem B645761 : Blo 428775 645761 := bstep (se 2 (by rfl) ⟨242160, by rfl⟩ : syracuseStep 645761 = 484321) B484321
theorem B1432205 : Blo 428775 1432205 := bstep (se 3 (by rfl) ⟨268538, by rfl⟩ : syracuseStep 1432205 = 537077) B537077
theorem B973457 : Blo 428775 973457 := bstep (se 2 (by rfl) ⟨365046, by rfl⟩ : syracuseStep 973457 = 730093) B730093
theorem B645779 : Blo 428775 645779 := bstep (se 1 (by rfl) ⟨484334, by rfl⟩ : syracuseStep 645779 = 968669) B968669
theorem B973475 : Blo 428775 973475 := bstep (se 1 (by rfl) ⟨730106, by rfl⟩ : syracuseStep 973475 = 1460213) B1460213
theorem B645809 : Blo 428775 645809 := bstep (se 2 (by rfl) ⟨242178, by rfl⟩ : syracuseStep 645809 = 484357) B484357
theorem B645827 : Blo 428775 645827 := bstep (se 1 (by rfl) ⟨484370, by rfl⟩ : syracuseStep 645827 = 968741) B968741
theorem B645857 : Blo 428775 645857 := bstep (se 2 (by rfl) ⟨242196, by rfl⟩ : syracuseStep 645857 = 484393) B484393
theorem B547555 : Blo 428775 547555 := bstep (se 1 (by rfl) ⟨410666, by rfl⟩ : syracuseStep 547555 = 821333) B821333
theorem B645875 : Blo 428775 645875 := bstep (se 1 (by rfl) ⟨484406, by rfl⟩ : syracuseStep 645875 = 968813) B968813
theorem B645905 : Blo 428775 645905 := bstep (se 2 (by rfl) ⟨242214, by rfl⟩ : syracuseStep 645905 = 484429) B484429
theorem B645923 : Blo 428775 645923 := bstep (se 1 (by rfl) ⟨484442, by rfl⟩ : syracuseStep 645923 = 968885) B968885
theorem B645953 : Blo 428775 645953 := bstep (se 2 (by rfl) ⟨242232, by rfl⟩ : syracuseStep 645953 = 484465) B484465
theorem B547651 : Blo 428775 547651 := bstep (se 1 (by rfl) ⟨410738, by rfl⟩ : syracuseStep 547651 = 821477) B821477
theorem B645971 : Blo 428775 645971 := bstep (se 1 (by rfl) ⟨484478, by rfl⟩ : syracuseStep 645971 = 968957) B968957
theorem B646001 : Blo 428775 646001 := bstep (se 2 (by rfl) ⟨242250, by rfl⟩ : syracuseStep 646001 = 484501) B484501
theorem B646019 : Blo 428775 646019 := bstep (se 1 (by rfl) ⟨484514, by rfl⟩ : syracuseStep 646019 = 969029) B969029
theorem B646049 : Blo 428775 646049 := bstep (se 2 (by rfl) ⟨242268, by rfl⟩ : syracuseStep 646049 = 484537) B484537
theorem B973745 : Blo 428775 973745 := bstep (se 2 (by rfl) ⟨365154, by rfl⟩ : syracuseStep 973745 = 730309) B730309
theorem B646067 : Blo 428775 646067 := bstep (se 1 (by rfl) ⟨484550, by rfl⟩ : syracuseStep 646067 = 969101) B969101
theorem B2186189 : Blo 428775 2186189 := bstep (se 3 (by rfl) ⟨409910, by rfl⟩ : syracuseStep 2186189 = 819821) B819821
theorem B646097 : Blo 428775 646097 := bstep (se 2 (by rfl) ⟨242286, by rfl⟩ : syracuseStep 646097 = 484573) B484573
theorem B646115 : Blo 428775 646115 := bstep (se 1 (by rfl) ⟨484586, by rfl⟩ : syracuseStep 646115 = 969173) B969173
theorem B646145 : Blo 428775 646145 := bstep (se 2 (by rfl) ⟨242304, by rfl⟩ : syracuseStep 646145 = 484609) B484609
theorem B646163 : Blo 428775 646163 := bstep (se 1 (by rfl) ⟨484622, by rfl⟩ : syracuseStep 646163 = 969245) B969245
theorem B646193 : Blo 428775 646193 := bstep (se 2 (by rfl) ⟨242322, by rfl⟩ : syracuseStep 646193 = 484645) B484645
theorem B646211 : Blo 428775 646211 := bstep (se 1 (by rfl) ⟨484658, by rfl⟩ : syracuseStep 646211 = 969317) B969317
theorem B646241 : Blo 428775 646241 := bstep (se 2 (by rfl) ⟨242340, by rfl⟩ : syracuseStep 646241 = 484681) B484681
theorem B646259 : Blo 428775 646259 := bstep (se 1 (by rfl) ⟨484694, by rfl⟩ : syracuseStep 646259 = 969389) B969389
theorem B646289 : Blo 428775 646289 := bstep (se 2 (by rfl) ⟨242358, by rfl⟩ : syracuseStep 646289 = 484717) B484717
theorem B482467 : Blo 428775 482467 := bstep (se 1 (by rfl) ⟨361850, by rfl⟩ : syracuseStep 482467 = 723701) B723701
theorem B646307 : Blo 428775 646307 := bstep (se 1 (by rfl) ⟨484730, by rfl⟩ : syracuseStep 646307 = 969461) B969461
theorem B646337 : Blo 428775 646337 := bstep (se 2 (by rfl) ⟨242376, by rfl⟩ : syracuseStep 646337 = 484753) B484753
theorem B613585 : Blo 428775 613585 := bstep (se 2 (by rfl) ⟨230094, by rfl⟩ : syracuseStep 613585 = 460189) B460189
theorem B646355 : Blo 428775 646355 := bstep (se 1 (by rfl) ⟨484766, by rfl⟩ : syracuseStep 646355 = 969533) B969533
theorem B646385 : Blo 428775 646385 := bstep (se 2 (by rfl) ⟨242394, by rfl⟩ : syracuseStep 646385 = 484789) B484789
theorem B646403 : Blo 428775 646403 := bstep (se 1 (by rfl) ⟨484802, by rfl⟩ : syracuseStep 646403 = 969605) B969605
theorem B646433 : Blo 428775 646433 := bstep (se 2 (by rfl) ⟨242412, by rfl⟩ : syracuseStep 646433 = 484825) B484825
theorem B482611 : Blo 428775 482611 := bstep (se 1 (by rfl) ⟨361958, by rfl⟩ : syracuseStep 482611 = 723917) B723917
theorem B646451 : Blo 428775 646451 := bstep (se 1 (by rfl) ⟨484838, by rfl⟩ : syracuseStep 646451 = 969677) B969677
theorem B646481 : Blo 428775 646481 := bstep (se 2 (by rfl) ⟨242430, by rfl⟩ : syracuseStep 646481 = 484861) B484861
theorem B646499 : Blo 428775 646499 := bstep (se 1 (by rfl) ⟨484874, by rfl⟩ : syracuseStep 646499 = 969749) B969749
theorem B646529 : Blo 428775 646529 := bstep (se 2 (by rfl) ⟨242448, by rfl⟩ : syracuseStep 646529 = 484897) B484897
theorem B646547 : Blo 428775 646547 := bstep (se 1 (by rfl) ⟨484910, by rfl⟩ : syracuseStep 646547 = 969821) B969821
theorem B646577 : Blo 428775 646577 := bstep (se 2 (by rfl) ⟨242466, by rfl⟩ : syracuseStep 646577 = 484933) B484933
theorem B482755 : Blo 428775 482755 := bstep (se 1 (by rfl) ⟨362066, by rfl⟩ : syracuseStep 482755 = 724133) B724133
theorem B646595 : Blo 428775 646595 := bstep (se 1 (by rfl) ⟨484946, by rfl⟩ : syracuseStep 646595 = 969893) B969893
theorem B646625 : Blo 428775 646625 := bstep (se 2 (by rfl) ⟨242484, by rfl⟩ : syracuseStep 646625 = 484969) B484969
theorem B646643 : Blo 428775 646643 := bstep (se 1 (by rfl) ⟨484982, by rfl⟩ : syracuseStep 646643 = 969965) B969965
theorem B646673 : Blo 428775 646673 := bstep (se 2 (by rfl) ⟨242502, by rfl⟩ : syracuseStep 646673 = 485005) B485005
theorem B613921 : Blo 428775 613921 := bstep (se 2 (by rfl) ⟨230220, by rfl⟩ : syracuseStep 613921 = 460441) B460441
theorem B646691 : Blo 428775 646691 := bstep (se 1 (by rfl) ⟨485018, by rfl⟩ : syracuseStep 646691 = 970037) B970037
theorem B646721 : Blo 428775 646721 := bstep (se 2 (by rfl) ⟨242520, by rfl⟩ : syracuseStep 646721 = 485041) B485041
theorem B515651 : Blo 428775 515651 := bstep (se 1 (by rfl) ⟨386738, by rfl⟩ : syracuseStep 515651 = 773477) B773477
theorem B482899 : Blo 428775 482899 := bstep (se 1 (by rfl) ⟨362174, by rfl⟩ : syracuseStep 482899 = 724349) B724349
theorem B646739 : Blo 428775 646739 := bstep (se 1 (by rfl) ⟨485054, by rfl⟩ : syracuseStep 646739 = 970109) B970109
theorem B646769 : Blo 428775 646769 := bstep (se 2 (by rfl) ⟨242538, by rfl⟩ : syracuseStep 646769 = 485077) B485077
theorem B646787 : Blo 428775 646787 := bstep (se 1 (by rfl) ⟨485090, by rfl⟩ : syracuseStep 646787 = 970181) B970181
theorem B646817 : Blo 428775 646817 := bstep (se 2 (by rfl) ⟨242556, by rfl⟩ : syracuseStep 646817 = 485113) B485113
theorem B1400483 : Blo 428775 1400483 := bstep (se 1 (by rfl) ⟨1050362, by rfl⟩ : syracuseStep 1400483 = 2100725) B2100725
theorem B646835 : Blo 428775 646835 := bstep (se 1 (by rfl) ⟨485126, by rfl⟩ : syracuseStep 646835 = 970253) B970253
theorem B646865 : Blo 428775 646865 := bstep (se 2 (by rfl) ⟨242574, by rfl⟩ : syracuseStep 646865 = 485149) B485149
theorem B483043 : Blo 428775 483043 := bstep (se 1 (by rfl) ⟨362282, by rfl⟩ : syracuseStep 483043 = 724565) B724565
theorem B646883 : Blo 428775 646883 := bstep (se 1 (by rfl) ⟨485162, by rfl⟩ : syracuseStep 646883 = 970325) B970325
theorem B646913 : Blo 428775 646913 := bstep (se 2 (by rfl) ⟨242592, by rfl⟩ : syracuseStep 646913 = 485185) B485185
theorem B646931 : Blo 428775 646931 := bstep (se 1 (by rfl) ⟨485198, by rfl⟩ : syracuseStep 646931 = 970397) B970397
theorem B646961 : Blo 428775 646961 := bstep (se 2 (by rfl) ⟨242610, by rfl⟩ : syracuseStep 646961 = 485221) B485221
theorem B646979 : Blo 428775 646979 := bstep (se 1 (by rfl) ⟨485234, by rfl⟩ : syracuseStep 646979 = 970469) B970469
theorem B647009 : Blo 428775 647009 := bstep (se 2 (by rfl) ⟨242628, by rfl⟩ : syracuseStep 647009 = 485257) B485257
theorem B483187 : Blo 428775 483187 := bstep (se 1 (by rfl) ⟨362390, by rfl⟩ : syracuseStep 483187 = 724781) B724781
theorem B647027 : Blo 428775 647027 := bstep (se 1 (by rfl) ⟨485270, by rfl⟩ : syracuseStep 647027 = 970541) B970541
theorem B647057 : Blo 428775 647057 := bstep (se 2 (by rfl) ⟨242646, by rfl⟩ : syracuseStep 647057 = 485293) B485293
theorem B647075 : Blo 428775 647075 := bstep (se 1 (by rfl) ⟨485306, by rfl⟩ : syracuseStep 647075 = 970613) B970613
theorem B647105 : Blo 428775 647105 := bstep (se 2 (by rfl) ⟨242664, by rfl⟩ : syracuseStep 647105 = 485329) B485329
theorem B2449349 : Blo 428775 2449349 := bstep (se 4 (by rfl) ⟨229626, by rfl⟩ : syracuseStep 2449349 = 459253) B459253
theorem B647123 : Blo 428775 647123 := bstep (se 1 (by rfl) ⟨485342, by rfl⟩ : syracuseStep 647123 = 970685) B970685
theorem B647153 : Blo 428775 647153 := bstep (se 2 (by rfl) ⟨242682, by rfl⟩ : syracuseStep 647153 = 485365) B485365
theorem B483331 : Blo 428775 483331 := bstep (se 1 (by rfl) ⟨362498, by rfl⟩ : syracuseStep 483331 = 724997) B724997
theorem B647171 : Blo 428775 647171 := bstep (se 1 (by rfl) ⟨485378, by rfl⟩ : syracuseStep 647171 = 970757) B970757
theorem B647201 : Blo 428775 647201 := bstep (se 2 (by rfl) ⟨242700, by rfl⟩ : syracuseStep 647201 = 485401) B485401
theorem B647219 : Blo 428775 647219 := bstep (se 1 (by rfl) ⟨485414, by rfl⟩ : syracuseStep 647219 = 970829) B970829
theorem B647249 : Blo 428775 647249 := bstep (se 2 (by rfl) ⟨242718, by rfl⟩ : syracuseStep 647249 = 485437) B485437
theorem B647267 : Blo 428775 647267 := bstep (se 1 (by rfl) ⟨485450, by rfl⟩ : syracuseStep 647267 = 970901) B970901
theorem B614513 : Blo 428775 614513 := bstep (se 2 (by rfl) ⟨230442, by rfl⟩ : syracuseStep 614513 = 460885) B460885
theorem B647297 : Blo 428775 647297 := bstep (se 2 (by rfl) ⟨242736, by rfl⟩ : syracuseStep 647297 = 485473) B485473
theorem B3694733 : Blo 428775 3694733 := bstep (se 3 (by rfl) ⟨692762, by rfl⟩ : syracuseStep 3694733 = 1385525) B1385525
theorem B483475 : Blo 428775 483475 := bstep (se 1 (by rfl) ⟨362606, by rfl⟩ : syracuseStep 483475 = 725213) B725213
theorem B647315 : Blo 428775 647315 := bstep (se 1 (by rfl) ⟨485486, by rfl⟩ : syracuseStep 647315 = 970973) B970973
theorem B647345 : Blo 428775 647345 := bstep (se 2 (by rfl) ⟨242754, by rfl⟩ : syracuseStep 647345 = 485509) B485509
theorem B647363 : Blo 428775 647363 := bstep (se 1 (by rfl) ⟨485522, by rfl⟩ : syracuseStep 647363 = 971045) B971045
theorem B647393 : Blo 428775 647393 := bstep (se 2 (by rfl) ⟨242772, by rfl⟩ : syracuseStep 647393 = 485545) B485545
theorem B3268835 : Blo 428775 3268835 := bstep (se 1 (by rfl) ⟨2451626, by rfl⟩ : syracuseStep 3268835 = 4903253) B4903253
theorem B647411 : Blo 428775 647411 := bstep (se 1 (by rfl) ⟨485558, by rfl⟩ : syracuseStep 647411 = 971117) B971117
theorem B647441 : Blo 428775 647441 := bstep (se 2 (by rfl) ⟨242790, by rfl⟩ : syracuseStep 647441 = 485581) B485581
theorem B483619 : Blo 428775 483619 := bstep (se 1 (by rfl) ⟨362714, by rfl⟩ : syracuseStep 483619 = 725429) B725429
theorem B647459 : Blo 428775 647459 := bstep (se 1 (by rfl) ⟨485594, by rfl⟩ : syracuseStep 647459 = 971189) B971189
theorem B647489 : Blo 428775 647489 := bstep (se 2 (by rfl) ⟨242808, by rfl⟩ : syracuseStep 647489 = 485617) B485617
theorem B4120901 : Blo 428775 4120901 := bstep (se 4 (by rfl) ⟨386334, by rfl⟩ : syracuseStep 4120901 = 772669) B772669
theorem B647507 : Blo 428775 647507 := bstep (se 1 (by rfl) ⟨485630, by rfl⟩ : syracuseStep 647507 = 971261) B971261
theorem B647537 : Blo 428775 647537 := bstep (se 2 (by rfl) ⟨242826, by rfl⟩ : syracuseStep 647537 = 485653) B485653
theorem B647555 : Blo 428775 647555 := bstep (se 1 (by rfl) ⟨485666, by rfl⟩ : syracuseStep 647555 = 971333) B971333
theorem B647585 : Blo 428775 647585 := bstep (se 2 (by rfl) ⟨242844, by rfl⟩ : syracuseStep 647585 = 485689) B485689
theorem B483763 : Blo 428775 483763 := bstep (se 1 (by rfl) ⟨362822, by rfl⟩ : syracuseStep 483763 = 725645) B725645
theorem B647603 : Blo 428775 647603 := bstep (se 1 (by rfl) ⟨485702, by rfl⟩ : syracuseStep 647603 = 971405) B971405
theorem B647633 : Blo 428775 647633 := bstep (se 2 (by rfl) ⟨242862, by rfl⟩ : syracuseStep 647633 = 485725) B485725
theorem B647651 : Blo 428775 647651 := bstep (se 1 (by rfl) ⟨485738, by rfl⟩ : syracuseStep 647651 = 971477) B971477
theorem B647681 : Blo 428775 647681 := bstep (se 2 (by rfl) ⟨242880, by rfl⟩ : syracuseStep 647681 = 485761) B485761
theorem B647699 : Blo 428775 647699 := bstep (se 1 (by rfl) ⟨485774, by rfl⟩ : syracuseStep 647699 = 971549) B971549
theorem B647729 : Blo 428775 647729 := bstep (se 2 (by rfl) ⟨242898, by rfl⟩ : syracuseStep 647729 = 485797) B485797
theorem B483907 : Blo 428775 483907 := bstep (se 1 (by rfl) ⟨362930, by rfl⟩ : syracuseStep 483907 = 725861) B725861
theorem B647747 : Blo 428775 647747 := bstep (se 1 (by rfl) ⟨485810, by rfl⟩ : syracuseStep 647747 = 971621) B971621
theorem B647777 : Blo 428775 647777 := bstep (se 2 (by rfl) ⟨242916, by rfl⟩ : syracuseStep 647777 = 485833) B485833
theorem B2450033 : Blo 428775 2450033 := bstep (se 2 (by rfl) ⟨918762, by rfl⟩ : syracuseStep 2450033 = 1837525) B1837525
theorem B647795 : Blo 428775 647795 := bstep (se 1 (by rfl) ⟨485846, by rfl⟩ : syracuseStep 647795 = 971693) B971693
theorem B615043 : Blo 428775 615043 := bstep (se 1 (by rfl) ⟨461282, by rfl⟩ : syracuseStep 615043 = 922565) B922565
theorem B647825 : Blo 428775 647825 := bstep (se 2 (by rfl) ⟨242934, by rfl⟩ : syracuseStep 647825 = 485869) B485869
theorem B778897 : Blo 428775 778897 := bstep (se 2 (by rfl) ⟨292086, by rfl⟩ : syracuseStep 778897 = 584173) B584173
theorem B647843 : Blo 428775 647843 := bstep (se 1 (by rfl) ⟨485882, by rfl⟩ : syracuseStep 647843 = 971765) B971765
theorem B647873 : Blo 428775 647873 := bstep (se 2 (by rfl) ⟨242952, by rfl⟩ : syracuseStep 647873 = 485905) B485905
theorem B1630925 : Blo 428775 1630925 := bstep (se 3 (by rfl) ⟨305798, by rfl⟩ : syracuseStep 1630925 = 611597) B611597
theorem B484051 : Blo 428775 484051 := bstep (se 1 (by rfl) ⟨363038, by rfl⟩ : syracuseStep 484051 = 726077) B726077
theorem B647891 : Blo 428775 647891 := bstep (se 1 (by rfl) ⟨485918, by rfl⟩ : syracuseStep 647891 = 971837) B971837
theorem B647921 : Blo 428775 647921 := bstep (se 2 (by rfl) ⟨242970, by rfl⟩ : syracuseStep 647921 = 485941) B485941
theorem B647939 : Blo 428775 647939 := bstep (se 1 (by rfl) ⟨485954, by rfl⟩ : syracuseStep 647939 = 971909) B971909
theorem B647969 : Blo 428775 647969 := bstep (se 2 (by rfl) ⟨242988, by rfl⟩ : syracuseStep 647969 = 485977) B485977
theorem B647987 : Blo 428775 647987 := bstep (se 1 (by rfl) ⟨485990, by rfl⟩ : syracuseStep 647987 = 971981) B971981
theorem B648017 : Blo 428775 648017 := bstep (se 2 (by rfl) ⟨243006, by rfl⟩ : syracuseStep 648017 = 486013) B486013
theorem B484195 : Blo 428775 484195 := bstep (se 1 (by rfl) ⟨363146, by rfl⟩ : syracuseStep 484195 = 726293) B726293
theorem B648035 : Blo 428775 648035 := bstep (se 1 (by rfl) ⟨486026, by rfl⟩ : syracuseStep 648035 = 972053) B972053
theorem B648065 : Blo 428775 648065 := bstep (se 2 (by rfl) ⟨243024, by rfl⟩ : syracuseStep 648065 = 486049) B486049
theorem B648083 : Blo 428775 648083 := bstep (se 1 (by rfl) ⟨486062, by rfl⟩ : syracuseStep 648083 = 972125) B972125
theorem B648113 : Blo 428775 648113 := bstep (se 2 (by rfl) ⟨243042, by rfl⟩ : syracuseStep 648113 = 486085) B486085
theorem B648131 : Blo 428775 648131 := bstep (se 1 (by rfl) ⟨486098, by rfl⟩ : syracuseStep 648131 = 972197) B972197
theorem B615379 : Blo 428775 615379 := bstep (se 1 (by rfl) ⟨461534, by rfl⟩ : syracuseStep 615379 = 923069) B923069
theorem B648161 : Blo 428775 648161 := bstep (se 2 (by rfl) ⟨243060, by rfl⟩ : syracuseStep 648161 = 486121) B486121
theorem B484339 : Blo 428775 484339 := bstep (se 1 (by rfl) ⟨363254, by rfl⟩ : syracuseStep 484339 = 726509) B726509
theorem B648179 : Blo 428775 648179 := bstep (se 1 (by rfl) ⟨486134, by rfl⟩ : syracuseStep 648179 = 972269) B972269
theorem B648209 : Blo 428775 648209 := bstep (se 2 (by rfl) ⟨243078, by rfl⟩ : syracuseStep 648209 = 486157) B486157
theorem B648227 : Blo 428775 648227 := bstep (se 1 (by rfl) ⟨486170, by rfl⟩ : syracuseStep 648227 = 972341) B972341
theorem B746561 : Blo 428775 746561 := bstep (se 2 (by rfl) ⟨279960, by rfl⟩ : syracuseStep 746561 = 559921) B559921
theorem B648257 : Blo 428775 648257 := bstep (se 2 (by rfl) ⟨243096, by rfl⟩ : syracuseStep 648257 = 486193) B486193
theorem B648275 : Blo 428775 648275 := bstep (se 1 (by rfl) ⟨486206, by rfl⟩ : syracuseStep 648275 = 972413) B972413
theorem B648305 : Blo 428775 648305 := bstep (se 2 (by rfl) ⟨243114, by rfl⟩ : syracuseStep 648305 = 486229) B486229
theorem B484483 : Blo 428775 484483 := bstep (se 1 (by rfl) ⟨363362, by rfl⟩ : syracuseStep 484483 = 726725) B726725
theorem B648323 : Blo 428775 648323 := bstep (se 1 (by rfl) ⟨486242, by rfl⟩ : syracuseStep 648323 = 972485) B972485
theorem B648353 : Blo 428775 648353 := bstep (se 2 (by rfl) ⟨243132, by rfl⟩ : syracuseStep 648353 = 486265) B486265
theorem B648371 : Blo 428775 648371 := bstep (se 1 (by rfl) ⟨486278, by rfl⟩ : syracuseStep 648371 = 972557) B972557
theorem B648401 : Blo 428775 648401 := bstep (se 2 (by rfl) ⟨243150, by rfl⟩ : syracuseStep 648401 = 486301) B486301
theorem B648419 : Blo 428775 648419 := bstep (se 1 (by rfl) ⟨486314, by rfl⟩ : syracuseStep 648419 = 972629) B972629
theorem B3663089 : Blo 428775 3663089 := bstep (se 2 (by rfl) ⟨1373658, by rfl⟩ : syracuseStep 3663089 = 2747317) B2747317
theorem B648449 : Blo 428775 648449 := bstep (se 2 (by rfl) ⟨243168, by rfl⟩ : syracuseStep 648449 = 486337) B486337
theorem B484627 : Blo 428775 484627 := bstep (se 1 (by rfl) ⟨363470, by rfl⟩ : syracuseStep 484627 = 726941) B726941
theorem B648467 : Blo 428775 648467 := bstep (se 1 (by rfl) ⟨486350, by rfl⟩ : syracuseStep 648467 = 972701) B972701
theorem B648497 : Blo 428775 648497 := bstep (se 2 (by rfl) ⟨243186, by rfl⟩ : syracuseStep 648497 = 486373) B486373
theorem B648515 : Blo 428775 648515 := bstep (se 1 (by rfl) ⟨486386, by rfl⟩ : syracuseStep 648515 = 972773) B972773
theorem B648545 : Blo 428775 648545 := bstep (se 2 (by rfl) ⟨243204, by rfl⟩ : syracuseStep 648545 = 486409) B486409
theorem B648563 : Blo 428775 648563 := bstep (se 1 (by rfl) ⟨486422, by rfl⟩ : syracuseStep 648563 = 972845) B972845
theorem B648593 : Blo 428775 648593 := bstep (se 2 (by rfl) ⟨243222, by rfl⟩ : syracuseStep 648593 = 486445) B486445
theorem B484771 : Blo 428775 484771 := bstep (se 1 (by rfl) ⟨363578, by rfl⟩ : syracuseStep 484771 = 727157) B727157
theorem B648611 : Blo 428775 648611 := bstep (se 1 (by rfl) ⟨486458, by rfl⟩ : syracuseStep 648611 = 972917) B972917
theorem B1467821 : Blo 428775 1467821 := bstep (se 3 (by rfl) ⟨275216, by rfl⟩ : syracuseStep 1467821 = 550433) B550433
theorem B648641 : Blo 428775 648641 := bstep (se 2 (by rfl) ⟨243240, by rfl⟩ : syracuseStep 648641 = 486481) B486481
theorem B648659 : Blo 428775 648659 := bstep (se 1 (by rfl) ⟨486494, by rfl⟩ : syracuseStep 648659 = 972989) B972989
theorem B648689 : Blo 428775 648689 := bstep (se 2 (by rfl) ⟨243258, by rfl⟩ : syracuseStep 648689 = 486517) B486517
theorem B615937 : Blo 428775 615937 := bstep (se 2 (by rfl) ⟨230976, by rfl⟩ : syracuseStep 615937 = 461953) B461953
theorem B648707 : Blo 428775 648707 := bstep (se 1 (by rfl) ⟨486530, by rfl⟩ : syracuseStep 648707 = 973061) B973061
theorem B648737 : Blo 428775 648737 := bstep (se 2 (by rfl) ⟨243276, by rfl⟩ : syracuseStep 648737 = 486553) B486553
theorem B615971 : Blo 428775 615971 := bstep (se 1 (by rfl) ⟨461978, by rfl⟩ : syracuseStep 615971 = 923957) B923957
theorem B484915 : Blo 428775 484915 := bstep (se 1 (by rfl) ⟨363686, by rfl⟩ : syracuseStep 484915 = 727373) B727373
theorem B648755 : Blo 428775 648755 := bstep (se 1 (by rfl) ⟨486566, by rfl⟩ : syracuseStep 648755 = 973133) B973133
theorem B648785 : Blo 428775 648785 := bstep (se 2 (by rfl) ⟨243294, by rfl⟩ : syracuseStep 648785 = 486589) B486589
theorem B648803 : Blo 428775 648803 := bstep (se 1 (by rfl) ⟨486602, by rfl⟩ : syracuseStep 648803 = 973205) B973205
theorem B648833 : Blo 428775 648833 := bstep (se 2 (by rfl) ⟨243312, by rfl⟩ : syracuseStep 648833 = 486625) B486625
theorem B648851 : Blo 428775 648851 := bstep (se 1 (by rfl) ⟨486638, by rfl⟩ : syracuseStep 648851 = 973277) B973277
theorem B648881 : Blo 428775 648881 := bstep (se 2 (by rfl) ⟨243330, by rfl⟩ : syracuseStep 648881 = 486661) B486661
theorem B485059 : Blo 428775 485059 := bstep (se 1 (by rfl) ⟨363794, by rfl⟩ : syracuseStep 485059 = 727589) B727589
theorem B648899 : Blo 428775 648899 := bstep (se 1 (by rfl) ⟨486674, by rfl⟩ : syracuseStep 648899 = 973349) B973349
theorem B648929 : Blo 428775 648929 := bstep (se 2 (by rfl) ⟨243348, by rfl⟩ : syracuseStep 648929 = 486697) B486697
theorem B648947 : Blo 428775 648947 := bstep (se 1 (by rfl) ⟨486710, by rfl⟩ : syracuseStep 648947 = 973421) B973421
theorem B648977 : Blo 428775 648977 := bstep (se 2 (by rfl) ⟨243366, by rfl⟩ : syracuseStep 648977 = 486733) B486733
theorem B648995 : Blo 428775 648995 := bstep (se 1 (by rfl) ⟨486746, by rfl⟩ : syracuseStep 648995 = 973493) B973493
theorem B2189105 : Blo 428775 2189105 := bstep (se 2 (by rfl) ⟨820914, by rfl⟩ : syracuseStep 2189105 = 1641829) B1641829
theorem B649025 : Blo 428775 649025 := bstep (se 2 (by rfl) ⟨243384, by rfl⟩ : syracuseStep 649025 = 486769) B486769
theorem B485203 : Blo 428775 485203 := bstep (se 1 (by rfl) ⟨363902, by rfl⟩ : syracuseStep 485203 = 727805) B727805
theorem B649043 : Blo 428775 649043 := bstep (se 1 (by rfl) ⟨486782, by rfl⟩ : syracuseStep 649043 = 973565) B973565
theorem B649073 : Blo 428775 649073 := bstep (se 2 (by rfl) ⟨243402, by rfl⟩ : syracuseStep 649073 = 486805) B486805
theorem B649091 : Blo 428775 649091 := bstep (se 1 (by rfl) ⟨486818, by rfl⟩ : syracuseStep 649091 = 973637) B973637
theorem B649121 : Blo 428775 649121 := bstep (se 2 (by rfl) ⟨243420, by rfl⟩ : syracuseStep 649121 = 486841) B486841
theorem B649139 : Blo 428775 649139 := bstep (se 1 (by rfl) ⟨486854, by rfl⟩ : syracuseStep 649139 = 973709) B973709
theorem B485347 : Blo 428775 485347 := bstep (se 1 (by rfl) ⟨364010, by rfl⟩ : syracuseStep 485347 = 728021) B728021
theorem B2451491 : Blo 428775 2451491 := bstep (se 1 (by rfl) ⟨1838618, by rfl⟩ : syracuseStep 2451491 = 3677237) B3677237
theorem B518179 : Blo 428775 518179 := bstep (se 1 (by rfl) ⟨388634, by rfl⟩ : syracuseStep 518179 = 777269) B777269
theorem B485491 : Blo 428775 485491 := bstep (se 1 (by rfl) ⟨364118, by rfl⟩ : syracuseStep 485491 = 728237) B728237
theorem B518275 : Blo 428775 518275 := bstep (se 1 (by rfl) ⟨388706, by rfl⟩ : syracuseStep 518275 = 777413) B777413
theorem B583859 : Blo 428775 583859 := bstep (se 1 (by rfl) ⟨437894, by rfl⟩ : syracuseStep 583859 = 875789) B875789
theorem B485635 : Blo 428775 485635 := bstep (se 1 (by rfl) ⟨364226, by rfl⟩ : syracuseStep 485635 = 728453) B728453
theorem B485779 : Blo 428775 485779 := bstep (se 1 (by rfl) ⟨364334, by rfl⟩ : syracuseStep 485779 = 728669) B728669
theorem B518563 : Blo 428775 518563 := bstep (se 1 (by rfl) ⟨388922, by rfl⟩ : syracuseStep 518563 = 777845) B777845
theorem B2320817 : Blo 428775 2320817 := bstep (se 2 (by rfl) ⟨870306, by rfl⟩ : syracuseStep 2320817 = 1740613) B1740613
theorem B3697123 : Blo 428775 3697123 := bstep (se 1 (by rfl) ⟨2772842, by rfl⟩ : syracuseStep 3697123 = 5545685) B5545685
theorem B1010161 : Blo 428775 1010161 := bstep (se 2 (by rfl) ⟨378810, by rfl⟩ : syracuseStep 1010161 = 757621) B757621
theorem B485923 : Blo 428775 485923 := bstep (se 1 (by rfl) ⟨364442, by rfl⟩ : syracuseStep 485923 = 728885) B728885
theorem B2615885 : Blo 428775 2615885 := bstep (se 3 (by rfl) ⟨490478, by rfl⟩ : syracuseStep 2615885 = 980957) B980957
theorem B518755 : Blo 428775 518755 := bstep (se 1 (by rfl) ⟨389066, by rfl⟩ : syracuseStep 518755 = 778133) B778133
theorem B486067 : Blo 428775 486067 := bstep (se 1 (by rfl) ⟨364550, by rfl⟩ : syracuseStep 486067 = 729101) B729101
theorem B486211 : Blo 428775 486211 := bstep (se 1 (by rfl) ⟨364658, by rfl⟩ : syracuseStep 486211 = 729317) B729317
theorem B1567565 : Blo 428775 1567565 := bstep (se 3 (by rfl) ⟨293918, by rfl⟩ : syracuseStep 1567565 = 587837) B587837
theorem B551891 : Blo 428775 551891 := bstep (se 1 (by rfl) ⟨413918, by rfl⟩ : syracuseStep 551891 = 827837) B827837
theorem B486355 : Blo 428775 486355 := bstep (se 1 (by rfl) ⟨364766, by rfl⟩ : syracuseStep 486355 = 729533) B729533
theorem B3304547 : Blo 428775 3304547 := bstep (se 1 (by rfl) ⟨2478410, by rfl⟩ : syracuseStep 3304547 = 4956821) B4956821
theorem B486499 : Blo 428775 486499 := bstep (se 1 (by rfl) ⟨364874, by rfl⟩ : syracuseStep 486499 = 729749) B729749
theorem B814225 : Blo 428775 814225 := bstep (se 2 (by rfl) ⟨305334, by rfl⟩ : syracuseStep 814225 = 610669) B610669
theorem B2190563 : Blo 428775 2190563 := bstep (se 1 (by rfl) ⟨1642922, by rfl⟩ : syracuseStep 2190563 = 3285845) B3285845
theorem B486643 : Blo 428775 486643 := bstep (se 1 (by rfl) ⟨364982, by rfl⟩ : syracuseStep 486643 = 729965) B729965
theorem B1961329 : Blo 428775 1961329 := bstep (se 2 (by rfl) ⟨735498, by rfl⟩ : syracuseStep 1961329 = 1470997) B1470997
theorem B486787 : Blo 428775 486787 := bstep (se 1 (by rfl) ⟨365090, by rfl⟩ : syracuseStep 486787 = 730181) B730181
theorem B519635 : Blo 428775 519635 := bstep (se 1 (by rfl) ⟨389726, by rfl⟩ : syracuseStep 519635 = 779453) B779453
theorem B814627 : Blo 428775 814627 := bstep (se 1 (by rfl) ⟨610970, by rfl⟩ : syracuseStep 814627 = 1221941) B1221941
theorem B1633841 : Blo 428775 1633841 := bstep (se 2 (by rfl) ⟨612690, by rfl⟩ : syracuseStep 1633841 = 1225381) B1225381
theorem B814673 : Blo 428775 814673 := bstep (se 2 (by rfl) ⟨305502, by rfl⟩ : syracuseStep 814673 = 611005) B611005
theorem B749251 : Blo 428775 749251 := bstep (se 1 (by rfl) ⟨561938, by rfl⟩ : syracuseStep 749251 = 1123877) B1123877
theorem B814961 : Blo 428775 814961 := bstep (se 2 (by rfl) ⟨305610, by rfl⟩ : syracuseStep 814961 = 611221) B611221
theorem B1470449 : Blo 428775 1470449 := bstep (se 2 (by rfl) ⟨551418, by rfl⟩ : syracuseStep 1470449 = 1102837) B1102837
theorem B815683 : Blo 428775 815683 := bstep (se 1 (by rfl) ⟨611762, by rfl⟩ : syracuseStep 815683 = 1223525) B1223525
theorem B1045219 : Blo 428775 1045219 := bstep (se 1 (by rfl) ⟨783914, by rfl⟩ : syracuseStep 1045219 = 1567829) B1567829
theorem B881425 : Blo 428775 881425 := bstep (se 2 (by rfl) ⟨330534, by rfl⟩ : syracuseStep 881425 = 661069) B661069
theorem B1176365 : Blo 428775 1176365 := bstep (se 3 (by rfl) ⟨220568, by rfl⟩ : syracuseStep 1176365 = 441137) B441137
theorem B1635299 : Blo 428775 1635299 := bstep (se 1 (by rfl) ⟨1226474, by rfl⟩ : syracuseStep 1635299 = 2452949) B2452949
theorem B816131 : Blo 428775 816131 := bstep (se 1 (by rfl) ⟨612098, by rfl⟩ : syracuseStep 816131 = 1224197) B1224197
theorem B2454725 : Blo 428775 2454725 := bstep (se 4 (by rfl) ⟨230130, by rfl⟩ : syracuseStep 2454725 = 460261) B460261
theorem B816419 : Blo 428775 816419 := bstep (se 1 (by rfl) ⟨612314, by rfl⟩ : syracuseStep 816419 = 1224629) B1224629
theorem B2618659 : Blo 428775 2618659 := bstep (se 1 (by rfl) ⟨1963994, by rfl⟩ : syracuseStep 2618659 = 3927989) B3927989
theorem B2618801 : Blo 428775 2618801 := bstep (se 2 (by rfl) ⟨982050, by rfl⟩ : syracuseStep 2618801 = 1964101) B1964101
theorem B3274181 : Blo 428775 3274181 := bstep (se 4 (by rfl) ⟨306954, by rfl⟩ : syracuseStep 3274181 = 613909) B613909
theorem B1373699 : Blo 428775 1373699 := bstep (se 1 (by rfl) ⟨1030274, by rfl⟩ : syracuseStep 1373699 = 2060549) B2060549
theorem B652865 : Blo 428775 652865 := bstep (se 2 (by rfl) ⟨244824, by rfl⟩ : syracuseStep 652865 = 489649) B489649
theorem B652913 : Blo 428775 652913 := bstep (se 2 (by rfl) ⟨244842, by rfl⟩ : syracuseStep 652913 = 489685) B489685
theorem B2455181 : Blo 428775 2455181 := bstep (se 3 (by rfl) ⟨460346, by rfl⟩ : syracuseStep 2455181 = 920693) B920693
theorem B5961397 : Blo 428775 5961397 := bstep (se 5 (by rfl) ⟨279440, by rfl⟩ : syracuseStep 5961397 = 558881) B558881
theorem B2324173 : Blo 428775 2324173 := bstep (se 3 (by rfl) ⟨435782, by rfl⟩ : syracuseStep 2324173 = 871565) B871565
theorem B1636301 : Blo 428775 1636301 := bstep (se 3 (by rfl) ⟨306806, by rfl⟩ : syracuseStep 1636301 = 613613) B613613
theorem B1833101 : Blo 428775 1833101 := bstep (se 3 (by rfl) ⟨343706, by rfl⟩ : syracuseStep 1833101 = 687413) B687413
theorem B1308817 : Blo 428775 1308817 := bstep (se 2 (by rfl) ⟨490806, by rfl⟩ : syracuseStep 1308817 = 981613) B981613
theorem B817361 : Blo 428775 817361 := bstep (se 2 (by rfl) ⟨306510, by rfl⟩ : syracuseStep 817361 = 613021) B613021
theorem B1571185 : Blo 428775 1571185 := bstep (se 2 (by rfl) ⟨589194, by rfl⟩ : syracuseStep 1571185 = 1178389) B1178389
theorem B915875 : Blo 428775 915875 := bstep (se 1 (by rfl) ⟨686906, by rfl⟩ : syracuseStep 915875 = 1373813) B1373813
theorem B3111493 : Blo 428775 3111493 := bstep (se 4 (by rfl) ⟨291702, by rfl⟩ : syracuseStep 3111493 = 583405) B583405
theorem B654355 : Blo 428775 654355 := bstep (se 1 (by rfl) ⟨490766, by rfl⟩ : syracuseStep 654355 = 981533) B981533
theorem B818257 : Blo 428775 818257 := bstep (se 2 (by rfl) ⟨306846, by rfl⟩ : syracuseStep 818257 = 613693) B613693
theorem B1965197 : Blo 428775 1965197 := bstep (se 3 (by rfl) ⟨368474, by rfl⟩ : syracuseStep 1965197 = 736949) B736949
theorem B818417 : Blo 428775 818417 := bstep (se 2 (by rfl) ⟨306906, by rfl⟩ : syracuseStep 818417 = 613813) B613813
theorem B1375505 : Blo 428775 1375505 := bstep (se 2 (by rfl) ⟨515814, by rfl⟩ : syracuseStep 1375505 = 1031629) B1031629
theorem B1375555 : Blo 428775 1375555 := bstep (se 1 (by rfl) ⟨1031666, by rfl⟩ : syracuseStep 1375555 = 2063333) B2063333
theorem B458083 : Blo 428775 458083 := bstep (se 1 (by rfl) ⟨343562, by rfl⟩ : syracuseStep 458083 = 687125) B687125
theorem B916849 : Blo 428775 916849 := bstep (se 2 (by rfl) ⟨343818, by rfl⟩ : syracuseStep 916849 = 687637) B687637
theorem B1310179 : Blo 428775 1310179 := bstep (se 1 (by rfl) ⟨982634, by rfl⟩ : syracuseStep 1310179 = 1965269) B1965269
theorem B491059 : Blo 428775 491059 := bstep (se 1 (by rfl) ⟨368294, by rfl⟩ : syracuseStep 491059 = 736589) B736589
theorem B818819 : Blo 428775 818819 := bstep (se 1 (by rfl) ⟨614114, by rfl⟩ : syracuseStep 818819 = 1228229) B1228229
theorem B1867619 : Blo 428775 1867619 := bstep (se 1 (by rfl) ⟨1400714, by rfl⟩ : syracuseStep 1867619 = 2801429) B2801429
theorem B917515 : Blo 428775 917515 := bstep (se 1 (by rfl) ⟨688136, by rfl⟩ : syracuseStep 917515 = 1376273) B1376273
theorem B1048627 : Blo 428775 1048627 := bstep (se 1 (by rfl) ⟨786470, by rfl⟩ : syracuseStep 1048627 = 1572941) B1572941
theorem B458903 : Blo 428775 458903 := bstep (se 1 (by rfl) ⟨344177, by rfl⟩ : syracuseStep 458903 = 688355) B688355
theorem B459031 : Blo 428775 459031 := bstep (se 1 (by rfl) ⟨344273, by rfl⟩ : syracuseStep 459031 = 688547) B688547
theorem B1638701 : Blo 428775 1638701 := bstep (se 3 (by rfl) ⟨307256, by rfl⟩ : syracuseStep 1638701 = 614513) B614513
theorem B786763 : Blo 428775 786763 := bstep (se 1 (by rfl) ⟨590072, by rfl⟩ : syracuseStep 786763 = 1180145) B1180145
theorem B1638731 : Blo 428775 1638731 := bstep (se 1 (by rfl) ⟨1229048, by rfl⟩ : syracuseStep 1638731 = 2458097) B2458097
theorem B819571 : Blo 428775 819571 := bstep (se 1 (by rfl) ⟨614678, by rfl⟩ : syracuseStep 819571 = 1229357) B1229357
theorem B1835713 : Blo 428775 1835713 := bstep (se 2 (by rfl) ⟨688392, by rfl⟩ : syracuseStep 1835713 = 1376785) B1376785
theorem B918233 : Blo 428775 918233 := bstep (se 2 (by rfl) ⟨344337, by rfl⟩ : syracuseStep 918233 = 688675) B688675
theorem B6980357 : Blo 428775 6980357 := bstep (se 4 (by rfl) ⟨654408, by rfl⟩ : syracuseStep 6980357 = 1308817) B1308817
theorem B820019 : Blo 428775 820019 := bstep (se 1 (by rfl) ⟨615014, by rfl⟩ : syracuseStep 820019 = 1230029) B1230029
theorem B1966913 : Blo 428775 1966913 := bstep (se 2 (by rfl) ⟨737592, by rfl⟩ : syracuseStep 1966913 = 1475185) B1475185
theorem B459595 : Blo 428775 459595 := bstep (se 1 (by rfl) ⟨344696, by rfl⟩ : syracuseStep 459595 = 689393) B689393
theorem B820057 : Blo 428775 820057 := bstep (se 2 (by rfl) ⟨307521, by rfl⟩ : syracuseStep 820057 = 615043) B615043
theorem B1967021 : Blo 428775 1967021 := bstep (se 3 (by rfl) ⟨368816, by rfl⟩ : syracuseStep 1967021 = 737633) B737633
theorem B1639385 : Blo 428775 1639385 := bstep (se 2 (by rfl) ⟨614769, by rfl⟩ : syracuseStep 1639385 = 1229539) B1229539
theorem B459851 : Blo 428775 459851 := bstep (se 1 (by rfl) ⟨344888, by rfl⟩ : syracuseStep 459851 = 689777) B689777
theorem B689239 : Blo 428775 689239 := bstep (se 1 (by rfl) ⟨516929, by rfl⟩ : syracuseStep 689239 = 1033859) B1033859
theorem B918643 : Blo 428775 918643 := bstep (se 1 (by rfl) ⟨688982, by rfl⟩ : syracuseStep 918643 = 1377965) B1377965
theorem B4916375 : Blo 428775 4916375 := bstep (se 1 (by rfl) ⟨3687281, by rfl⟩ : syracuseStep 4916375 = 7374563) B7374563
theorem B1639703 : Blo 428775 1639703 := bstep (se 1 (by rfl) ⟨1229777, by rfl⟩ : syracuseStep 1639703 = 2459555) B2459555
theorem B820505 : Blo 428775 820505 := bstep (se 2 (by rfl) ⟨307689, by rfl⟩ : syracuseStep 820505 = 615379) B615379
theorem B3999041 : Blo 428775 3999041 := bstep (se 2 (by rfl) ⟨1499640, by rfl⟩ : syracuseStep 3999041 = 2999281) B2999281
theorem B493015 : Blo 428775 493015 := bstep (se 1 (by rfl) ⟨369761, by rfl⟩ : syracuseStep 493015 = 739523) B739523
theorem B4982347 : Blo 428775 4982347 := bstep (se 1 (by rfl) ⟨3736760, by rfl⟩ : syracuseStep 4982347 = 7473521) B7473521
theorem B525911 : Blo 428775 525911 := bstep (se 1 (by rfl) ⟨394433, by rfl⟩ : syracuseStep 525911 = 788867) B788867
theorem B689995 : Blo 428775 689995 := bstep (se 1 (by rfl) ⟨517496, by rfl⟩ : syracuseStep 689995 = 1034993) B1034993
theorem B690059 : Blo 428775 690059 := bstep (se 1 (by rfl) ⟨517544, by rfl⟩ : syracuseStep 690059 = 1035089) B1035089
theorem B526219 : Blo 428775 526219 := bstep (se 1 (by rfl) ⟨394664, by rfl⟩ : syracuseStep 526219 = 789329) B789329
theorem B1640371 : Blo 428775 1640371 := bstep (se 1 (by rfl) ⟨1230278, by rfl⟩ : syracuseStep 1640371 = 2460557) B2460557
theorem B493547 : Blo 428775 493547 := bstep (se 1 (by rfl) ⟨370160, by rfl⟩ : syracuseStep 493547 = 740321) B740321
theorem B821249 : Blo 428775 821249 := bstep (se 2 (by rfl) ⟨307968, by rfl⟩ : syracuseStep 821249 = 615937) B615937
theorem B690187 : Blo 428775 690187 := bstep (se 1 (by rfl) ⟨517640, by rfl⟩ : syracuseStep 690187 = 1035281) B1035281
theorem B1837201 : Blo 428775 1837201 := bstep (se 2 (by rfl) ⟨688950, by rfl⟩ : syracuseStep 1837201 = 1377901) B1377901
theorem B3672215 : Blo 428775 3672215 := bstep (se 1 (by rfl) ⟨2754161, by rfl⟩ : syracuseStep 3672215 = 5508323) B5508323
theorem B821515 : Blo 428775 821515 := bstep (se 1 (by rfl) ⟨616136, by rfl⟩ : syracuseStep 821515 = 1232273) B1232273
theorem B919831 : Blo 428775 919831 := bstep (se 1 (by rfl) ⟨689873, by rfl⟩ : syracuseStep 919831 = 1379747) B1379747
theorem B919873 : Blo 428775 919873 := bstep (se 2 (by rfl) ⟨344952, by rfl⟩ : syracuseStep 919873 = 689905) B689905
theorem B985483 : Blo 428775 985483 := bstep (se 1 (by rfl) ⟨739112, by rfl⟩ : syracuseStep 985483 = 1478225) B1478225
theorem B690905 : Blo 428775 690905 := bstep (se 2 (by rfl) ⟨259089, by rfl⟩ : syracuseStep 690905 = 518179) B518179
theorem B428779 : Blo 428775 428779 := bstep (se 1 (by rfl) ⟨321584, by rfl⟩ : syracuseStep 428779 = 643169) B643169
theorem B428791 : Blo 428775 428791 := bstep (se 1 (by rfl) ⟨321593, by rfl⟩ : syracuseStep 428791 = 643187) B643187
theorem B428811 : Blo 428775 428811 := bstep (se 1 (by rfl) ⟨321608, by rfl⟩ : syracuseStep 428811 = 643217) B643217
theorem B2329361 : Blo 428775 2329361 := bstep (se 2 (by rfl) ⟨873510, by rfl⟩ : syracuseStep 2329361 = 1747021) B1747021
theorem B428823 : Blo 428775 428823 := bstep (se 1 (by rfl) ⟨321617, by rfl⟩ : syracuseStep 428823 = 643235) B643235
theorem B428843 : Blo 428775 428843 := bstep (se 1 (by rfl) ⟨321632, by rfl⟩ : syracuseStep 428843 = 643265) B643265
theorem B428855 : Blo 428775 428855 := bstep (se 1 (by rfl) ⟨321641, by rfl⟩ : syracuseStep 428855 = 643283) B643283
theorem B428875 : Blo 428775 428875 := bstep (se 1 (by rfl) ⟨321656, by rfl⟩ : syracuseStep 428875 = 643313) B643313
theorem B428887 : Blo 428775 428887 := bstep (se 1 (by rfl) ⟨321665, by rfl⟩ : syracuseStep 428887 = 643331) B643331
theorem B691033 : Blo 428775 691033 := bstep (se 2 (by rfl) ⟨259137, by rfl⟩ : syracuseStep 691033 = 518275) B518275
theorem B12389219 : Blo 428775 12389219 := bstep (se 1 (by rfl) ⟨9291914, by rfl⟩ : syracuseStep 12389219 = 18583829) B18583829
theorem B428907 : Blo 428775 428907 := bstep (se 1 (by rfl) ⟨321680, by rfl⟩ : syracuseStep 428907 = 643361) B643361
theorem B428919 : Blo 428775 428919 := bstep (se 1 (by rfl) ⟨321689, by rfl⟩ : syracuseStep 428919 = 643379) B643379
theorem B428939 : Blo 428775 428939 := bstep (se 1 (by rfl) ⟨321704, by rfl⟩ : syracuseStep 428939 = 643409) B643409
theorem B428951 : Blo 428775 428951 := bstep (se 1 (by rfl) ⟨321713, by rfl⟩ : syracuseStep 428951 = 643427) B643427
theorem B723863 : Blo 428775 723863 := bstep (se 1 (by rfl) ⟨542897, by rfl⟩ : syracuseStep 723863 = 1085795) B1085795
theorem B428971 : Blo 428775 428971 := bstep (se 1 (by rfl) ⟨321728, by rfl⟩ : syracuseStep 428971 = 643457) B643457
theorem B428983 : Blo 428775 428983 := bstep (se 1 (by rfl) ⟨321737, by rfl⟩ : syracuseStep 428983 = 643475) B643475
theorem B429003 : Blo 428775 429003 := bstep (se 1 (by rfl) ⟨321752, by rfl⟩ : syracuseStep 429003 = 643505) B643505
theorem B429015 : Blo 428775 429015 := bstep (se 1 (by rfl) ⟨321761, by rfl⟩ : syracuseStep 429015 = 643523) B643523
theorem B5049305 : Blo 428775 5049305 := bstep (se 2 (by rfl) ⟨1893489, by rfl⟩ : syracuseStep 5049305 = 3786979) B3786979
theorem B429035 : Blo 428775 429035 := bstep (se 1 (by rfl) ⟨321776, by rfl⟩ : syracuseStep 429035 = 643553) B643553
theorem B429047 : Blo 428775 429047 := bstep (se 1 (by rfl) ⟨321785, by rfl⟩ : syracuseStep 429047 = 643571) B643571
theorem B429067 : Blo 428775 429067 := bstep (se 1 (by rfl) ⟨321800, by rfl⟩ : syracuseStep 429067 = 643601) B643601
theorem B723991 : Blo 428775 723991 := bstep (se 1 (by rfl) ⟨542993, by rfl⟩ : syracuseStep 723991 = 1085987) B1085987
theorem B429079 : Blo 428775 429079 := bstep (se 1 (by rfl) ⟨321809, by rfl⟩ : syracuseStep 429079 = 643619) B643619
theorem B429099 : Blo 428775 429099 := bstep (se 1 (by rfl) ⟨321824, by rfl⟩ : syracuseStep 429099 = 643649) B643649
theorem B461867 : Blo 428775 461867 := bstep (se 1 (by rfl) ⟨346400, by rfl⟩ : syracuseStep 461867 = 692801) B692801
theorem B429111 : Blo 428775 429111 := bstep (se 1 (by rfl) ⟨321833, by rfl⟩ : syracuseStep 429111 = 643667) B643667
theorem B429131 : Blo 428775 429131 := bstep (se 1 (by rfl) ⟨321848, by rfl⟩ : syracuseStep 429131 = 643697) B643697
theorem B429143 : Blo 428775 429143 := bstep (se 1 (by rfl) ⟨321857, by rfl⟩ : syracuseStep 429143 = 643715) B643715
theorem B429163 : Blo 428775 429163 := bstep (se 1 (by rfl) ⟨321872, by rfl⟩ : syracuseStep 429163 = 643745) B643745
theorem B429175 : Blo 428775 429175 := bstep (se 1 (by rfl) ⟨321881, by rfl⟩ : syracuseStep 429175 = 643763) B643763
theorem B429195 : Blo 428775 429195 := bstep (se 1 (by rfl) ⟨321896, by rfl⟩ : syracuseStep 429195 = 643793) B643793
theorem B1641617 : Blo 428775 1641617 := bstep (se 2 (by rfl) ⟨615606, by rfl⟩ : syracuseStep 1641617 = 1231213) B1231213
theorem B429207 : Blo 428775 429207 := bstep (se 1 (by rfl) ⟨321905, by rfl⟩ : syracuseStep 429207 = 643811) B643811
theorem B429227 : Blo 428775 429227 := bstep (se 1 (by rfl) ⟨321920, by rfl⟩ : syracuseStep 429227 = 643841) B643841
theorem B429239 : Blo 428775 429239 := bstep (se 1 (by rfl) ⟨321929, by rfl⟩ : syracuseStep 429239 = 643859) B643859
theorem B429259 : Blo 428775 429259 := bstep (se 1 (by rfl) ⟨321944, by rfl⟩ : syracuseStep 429259 = 643889) B643889
theorem B429271 : Blo 428775 429271 := bstep (se 1 (by rfl) ⟨321953, by rfl⟩ : syracuseStep 429271 = 643907) B643907
theorem B691417 : Blo 428775 691417 := bstep (se 2 (by rfl) ⟨259281, by rfl⟩ : syracuseStep 691417 = 518563) B518563
theorem B429291 : Blo 428775 429291 := bstep (se 1 (by rfl) ⟨321968, by rfl⟩ : syracuseStep 429291 = 643937) B643937
theorem B429303 : Blo 428775 429303 := bstep (se 1 (by rfl) ⟨321977, by rfl⟩ : syracuseStep 429303 = 643955) B643955
theorem B429323 : Blo 428775 429323 := bstep (se 1 (by rfl) ⟨321992, by rfl⟩ : syracuseStep 429323 = 643985) B643985
theorem B429335 : Blo 428775 429335 := bstep (se 1 (by rfl) ⟨322001, by rfl⟩ : syracuseStep 429335 = 644003) B644003
theorem B429355 : Blo 428775 429355 := bstep (se 1 (by rfl) ⟨322016, by rfl⟩ : syracuseStep 429355 = 644033) B644033
theorem B429367 : Blo 428775 429367 := bstep (se 1 (by rfl) ⟨322025, by rfl⟩ : syracuseStep 429367 = 644051) B644051
theorem B1346881 : Blo 428775 1346881 := bstep (se 2 (by rfl) ⟨505080, by rfl⟩ : syracuseStep 1346881 = 1010161) B1010161
theorem B429387 : Blo 428775 429387 := bstep (se 1 (by rfl) ⟨322040, by rfl⟩ : syracuseStep 429387 = 644081) B644081
theorem B429399 : Blo 428775 429399 := bstep (se 1 (by rfl) ⟨322049, by rfl⟩ : syracuseStep 429399 = 644099) B644099
theorem B429419 : Blo 428775 429419 := bstep (se 1 (by rfl) ⟨322064, by rfl⟩ : syracuseStep 429419 = 644129) B644129
theorem B429431 : Blo 428775 429431 := bstep (se 1 (by rfl) ⟨322073, by rfl⟩ : syracuseStep 429431 = 644147) B644147
theorem B429451 : Blo 428775 429451 := bstep (se 1 (by rfl) ⟨322088, by rfl⟩ : syracuseStep 429451 = 644177) B644177
theorem B429463 : Blo 428775 429463 := bstep (se 1 (by rfl) ⟨322097, by rfl⟩ : syracuseStep 429463 = 644195) B644195
theorem B429483 : Blo 428775 429483 := bstep (se 1 (by rfl) ⟨322112, by rfl⟩ : syracuseStep 429483 = 644225) B644225
theorem B429495 : Blo 428775 429495 := bstep (se 1 (by rfl) ⟨322121, by rfl⟩ : syracuseStep 429495 = 644243) B644243
theorem B429515 : Blo 428775 429515 := bstep (se 1 (by rfl) ⟨322136, by rfl⟩ : syracuseStep 429515 = 644273) B644273
theorem B429527 : Blo 428775 429527 := bstep (se 1 (by rfl) ⟨322145, by rfl⟩ : syracuseStep 429527 = 644291) B644291
theorem B691673 : Blo 428775 691673 := bstep (se 2 (by rfl) ⟨259377, by rfl⟩ : syracuseStep 691673 = 518755) B518755
theorem B1314269 : Blo 428775 1314269 := bstep (se 3 (by rfl) ⟨246425, by rfl⟩ : syracuseStep 1314269 = 492851) B492851
theorem B429547 : Blo 428775 429547 := bstep (se 1 (by rfl) ⟨322160, by rfl⟩ : syracuseStep 429547 = 644321) B644321
theorem B429559 : Blo 428775 429559 := bstep (se 1 (by rfl) ⟨322169, by rfl⟩ : syracuseStep 429559 = 644339) B644339
theorem B429579 : Blo 428775 429579 := bstep (se 1 (by rfl) ⟨322184, by rfl⟩ : syracuseStep 429579 = 644369) B644369
theorem B429591 : Blo 428775 429591 := bstep (se 1 (by rfl) ⟨322193, by rfl⟩ : syracuseStep 429591 = 644387) B644387
theorem B429611 : Blo 428775 429611 := bstep (se 1 (by rfl) ⟨322208, by rfl⟩ : syracuseStep 429611 = 644417) B644417
theorem B429623 : Blo 428775 429623 := bstep (se 1 (by rfl) ⟨322217, by rfl⟩ : syracuseStep 429623 = 644435) B644435
theorem B429643 : Blo 428775 429643 := bstep (se 1 (by rfl) ⟨322232, by rfl⟩ : syracuseStep 429643 = 644465) B644465
theorem B429655 : Blo 428775 429655 := bstep (se 1 (by rfl) ⟨322241, by rfl⟩ : syracuseStep 429655 = 644483) B644483
theorem B429675 : Blo 428775 429675 := bstep (se 1 (by rfl) ⟨322256, by rfl⟩ : syracuseStep 429675 = 644513) B644513
theorem B429687 : Blo 428775 429687 := bstep (se 1 (by rfl) ⟨322265, by rfl⟩ : syracuseStep 429687 = 644531) B644531
theorem B724619 : Blo 428775 724619 := bstep (se 1 (by rfl) ⟨543464, by rfl⟩ : syracuseStep 724619 = 1086929) B1086929
theorem B429707 : Blo 428775 429707 := bstep (se 1 (by rfl) ⟨322280, by rfl⟩ : syracuseStep 429707 = 644561) B644561
theorem B429719 : Blo 428775 429719 := bstep (se 1 (by rfl) ⟨322289, by rfl⟩ : syracuseStep 429719 = 644579) B644579
theorem B429739 : Blo 428775 429739 := bstep (se 1 (by rfl) ⟨322304, by rfl⟩ : syracuseStep 429739 = 644609) B644609
theorem B429751 : Blo 428775 429751 := bstep (se 1 (by rfl) ⟨322313, by rfl⟩ : syracuseStep 429751 = 644627) B644627
theorem B429771 : Blo 428775 429771 := bstep (se 1 (by rfl) ⟨322328, by rfl⟩ : syracuseStep 429771 = 644657) B644657
theorem B429783 : Blo 428775 429783 := bstep (se 1 (by rfl) ⟨322337, by rfl⟩ : syracuseStep 429783 = 644675) B644675
theorem B429803 : Blo 428775 429803 := bstep (se 1 (by rfl) ⟨322352, by rfl⟩ : syracuseStep 429803 = 644705) B644705
theorem B429815 : Blo 428775 429815 := bstep (se 1 (by rfl) ⟨322361, by rfl⟩ : syracuseStep 429815 = 644723) B644723
theorem B724747 : Blo 428775 724747 := bstep (se 1 (by rfl) ⟨543560, by rfl⟩ : syracuseStep 724747 = 1087121) B1087121
theorem B429835 : Blo 428775 429835 := bstep (se 1 (by rfl) ⟨322376, by rfl⟩ : syracuseStep 429835 = 644753) B644753
theorem B429847 : Blo 428775 429847 := bstep (se 1 (by rfl) ⟨322385, by rfl⟩ : syracuseStep 429847 = 644771) B644771
theorem B429867 : Blo 428775 429867 := bstep (se 1 (by rfl) ⟨322400, by rfl⟩ : syracuseStep 429867 = 644801) B644801
theorem B429879 : Blo 428775 429879 := bstep (se 1 (by rfl) ⟨322409, by rfl⟩ : syracuseStep 429879 = 644819) B644819
theorem B429899 : Blo 428775 429899 := bstep (se 1 (by rfl) ⟨322424, by rfl⟩ : syracuseStep 429899 = 644849) B644849
theorem B1642315 : Blo 428775 1642315 := bstep (se 1 (by rfl) ⟨1231736, by rfl⟩ : syracuseStep 1642315 = 2463473) B2463473
theorem B429911 : Blo 428775 429911 := bstep (se 1 (by rfl) ⟨322433, by rfl⟩ : syracuseStep 429911 = 644867) B644867
theorem B429931 : Blo 428775 429931 := bstep (se 1 (by rfl) ⟨322448, by rfl⟩ : syracuseStep 429931 = 644897) B644897
theorem B429943 : Blo 428775 429943 := bstep (se 1 (by rfl) ⟨322457, by rfl⟩ : syracuseStep 429943 = 644915) B644915
theorem B429963 : Blo 428775 429963 := bstep (se 1 (by rfl) ⟨322472, by rfl⟩ : syracuseStep 429963 = 644945) B644945
theorem B429975 : Blo 428775 429975 := bstep (se 1 (by rfl) ⟨322481, by rfl⟩ : syracuseStep 429975 = 644963) B644963
theorem B724889 : Blo 428775 724889 := bstep (se 2 (by rfl) ⟨271833, by rfl⟩ : syracuseStep 724889 = 543667) B543667
theorem B429995 : Blo 428775 429995 := bstep (se 1 (by rfl) ⟨322496, by rfl⟩ : syracuseStep 429995 = 644993) B644993
theorem B430007 : Blo 428775 430007 := bstep (se 1 (by rfl) ⟨322505, by rfl⟩ : syracuseStep 430007 = 645011) B645011
theorem B430027 : Blo 428775 430027 := bstep (se 1 (by rfl) ⟨322520, by rfl⟩ : syracuseStep 430027 = 645041) B645041
theorem B921547 : Blo 428775 921547 := bstep (se 1 (by rfl) ⟨691160, by rfl⟩ : syracuseStep 921547 = 1382321) B1382321
theorem B430039 : Blo 428775 430039 := bstep (se 1 (by rfl) ⟨322529, by rfl⟩ : syracuseStep 430039 = 645059) B645059
theorem B430059 : Blo 428775 430059 := bstep (se 1 (by rfl) ⟨322544, by rfl⟩ : syracuseStep 430059 = 645089) B645089
theorem B430071 : Blo 428775 430071 := bstep (se 1 (by rfl) ⟨322553, by rfl⟩ : syracuseStep 430071 = 645107) B645107
theorem B430091 : Blo 428775 430091 := bstep (se 1 (by rfl) ⟨322568, by rfl⟩ : syracuseStep 430091 = 645137) B645137
theorem B430103 : Blo 428775 430103 := bstep (se 1 (by rfl) ⟨322577, by rfl⟩ : syracuseStep 430103 = 645155) B645155
theorem B725017 : Blo 428775 725017 := bstep (se 2 (by rfl) ⟨271881, by rfl⟩ : syracuseStep 725017 = 543763) B543763
theorem B430123 : Blo 428775 430123 := bstep (se 1 (by rfl) ⟨322592, by rfl⟩ : syracuseStep 430123 = 645185) B645185
theorem B430135 : Blo 428775 430135 := bstep (se 1 (by rfl) ⟨322601, by rfl⟩ : syracuseStep 430135 = 645203) B645203
theorem B430155 : Blo 428775 430155 := bstep (se 1 (by rfl) ⟨322616, by rfl⟩ : syracuseStep 430155 = 645233) B645233
theorem B430167 : Blo 428775 430167 := bstep (se 1 (by rfl) ⟨322625, by rfl⟩ : syracuseStep 430167 = 645251) B645251
theorem B1642589 : Blo 428775 1642589 := bstep (se 3 (by rfl) ⟨307985, by rfl⟩ : syracuseStep 1642589 = 615971) B615971
theorem B430187 : Blo 428775 430187 := bstep (se 1 (by rfl) ⟨322640, by rfl⟩ : syracuseStep 430187 = 645281) B645281
theorem B430199 : Blo 428775 430199 := bstep (se 1 (by rfl) ⟨322649, by rfl⟩ : syracuseStep 430199 = 645299) B645299
theorem B430219 : Blo 428775 430219 := bstep (se 1 (by rfl) ⟨322664, by rfl⟩ : syracuseStep 430219 = 645329) B645329
theorem B430231 : Blo 428775 430231 := bstep (se 1 (by rfl) ⟨322673, by rfl⟩ : syracuseStep 430231 = 645347) B645347
theorem B1380503 : Blo 428775 1380503 := bstep (se 1 (by rfl) ⟨1035377, by rfl⟩ : syracuseStep 1380503 = 2070755) B2070755
theorem B430251 : Blo 428775 430251 := bstep (se 1 (by rfl) ⟨322688, by rfl⟩ : syracuseStep 430251 = 645377) B645377
theorem B1740973 : Blo 428775 1740973 := bstep (se 3 (by rfl) ⟨326432, by rfl⟩ : syracuseStep 1740973 = 652865) B652865
theorem B430263 : Blo 428775 430263 := bstep (se 1 (by rfl) ⟨322697, by rfl⟩ : syracuseStep 430263 = 645395) B645395
theorem B1085633 : Blo 428775 1085633 := bstep (se 2 (by rfl) ⟨407112, by rfl⟩ : syracuseStep 1085633 = 814225) B814225
theorem B430283 : Blo 428775 430283 := bstep (se 1 (by rfl) ⟨322712, by rfl⟩ : syracuseStep 430283 = 645425) B645425
theorem B430295 : Blo 428775 430295 := bstep (se 1 (by rfl) ⟨322721, by rfl⟩ : syracuseStep 430295 = 645443) B645443
theorem B430315 : Blo 428775 430315 := bstep (se 1 (by rfl) ⟨322736, by rfl⟩ : syracuseStep 430315 = 645473) B645473
theorem B430327 : Blo 428775 430327 := bstep (se 1 (by rfl) ⟨322745, by rfl⟩ : syracuseStep 430327 = 645491) B645491
theorem B430347 : Blo 428775 430347 := bstep (se 1 (by rfl) ⟨322760, by rfl⟩ : syracuseStep 430347 = 645521) B645521
theorem B430359 : Blo 428775 430359 := bstep (se 1 (by rfl) ⟨322769, by rfl⟩ : syracuseStep 430359 = 645539) B645539
theorem B921881 : Blo 428775 921881 := bstep (se 2 (by rfl) ⟨345705, by rfl⟩ : syracuseStep 921881 = 691411) B691411
theorem B430379 : Blo 428775 430379 := bstep (se 1 (by rfl) ⟨322784, by rfl⟩ : syracuseStep 430379 = 645569) B645569
theorem B430391 : Blo 428775 430391 := bstep (se 1 (by rfl) ⟨322793, by rfl⟩ : syracuseStep 430391 = 645587) B645587
theorem B430411 : Blo 428775 430411 := bstep (se 1 (by rfl) ⟨322808, by rfl⟩ : syracuseStep 430411 = 645617) B645617
theorem B430423 : Blo 428775 430423 := bstep (se 1 (by rfl) ⟨322817, by rfl⟩ : syracuseStep 430423 = 645635) B645635
theorem B430443 : Blo 428775 430443 := bstep (se 1 (by rfl) ⟨322832, by rfl⟩ : syracuseStep 430443 = 645665) B645665
theorem B430455 : Blo 428775 430455 := bstep (se 1 (by rfl) ⟨322841, by rfl⟩ : syracuseStep 430455 = 645683) B645683
theorem B3150211 : Blo 428775 3150211 := bstep (se 1 (by rfl) ⟨2362658, by rfl⟩ : syracuseStep 3150211 = 4725317) B4725317
theorem B430475 : Blo 428775 430475 := bstep (se 1 (by rfl) ⟨322856, by rfl⟩ : syracuseStep 430475 = 645713) B645713
theorem B430487 : Blo 428775 430487 := bstep (se 1 (by rfl) ⟨322865, by rfl⟩ : syracuseStep 430487 = 645731) B645731
theorem B430507 : Blo 428775 430507 := bstep (se 1 (by rfl) ⟨322880, by rfl⟩ : syracuseStep 430507 = 645761) B645761
theorem B430519 : Blo 428775 430519 := bstep (se 1 (by rfl) ⟨322889, by rfl⟩ : syracuseStep 430519 = 645779) B645779
theorem B430539 : Blo 428775 430539 := bstep (se 1 (by rfl) ⟨322904, by rfl⟩ : syracuseStep 430539 = 645809) B645809
theorem B430551 : Blo 428775 430551 := bstep (se 1 (by rfl) ⟨322913, by rfl⟩ : syracuseStep 430551 = 645827) B645827
theorem B430571 : Blo 428775 430571 := bstep (se 1 (by rfl) ⟨322928, by rfl⟩ : syracuseStep 430571 = 645857) B645857
theorem B430583 : Blo 428775 430583 := bstep (se 1 (by rfl) ⟨322937, by rfl⟩ : syracuseStep 430583 = 645875) B645875
theorem B430603 : Blo 428775 430603 := bstep (se 1 (by rfl) ⟨322952, by rfl⟩ : syracuseStep 430603 = 645905) B645905
theorem B430615 : Blo 428775 430615 := bstep (se 1 (by rfl) ⟨322961, by rfl⟩ : syracuseStep 430615 = 645923) B645923
theorem B3543587 : Blo 428775 3543587 := bstep (se 1 (by rfl) ⟨2657690, by rfl⟩ : syracuseStep 3543587 = 5315381) B5315381
theorem B430635 : Blo 428775 430635 := bstep (se 1 (by rfl) ⟨322976, by rfl⟩ : syracuseStep 430635 = 645953) B645953
theorem B430647 : Blo 428775 430647 := bstep (se 1 (by rfl) ⟨322985, by rfl⟩ : syracuseStep 430647 = 645971) B645971
theorem B430667 : Blo 428775 430667 := bstep (se 1 (by rfl) ⟨323000, by rfl⟩ : syracuseStep 430667 = 646001) B646001
theorem B725591 : Blo 428775 725591 := bstep (se 1 (by rfl) ⟨544193, by rfl⟩ : syracuseStep 725591 = 1088387) B1088387
theorem B430679 : Blo 428775 430679 := bstep (se 1 (by rfl) ⟨323009, by rfl⟩ : syracuseStep 430679 = 646019) B646019
theorem B430699 : Blo 428775 430699 := bstep (se 1 (by rfl) ⟨323024, by rfl⟩ : syracuseStep 430699 = 646049) B646049
theorem B430711 : Blo 428775 430711 := bstep (se 1 (by rfl) ⟨323033, by rfl⟩ : syracuseStep 430711 = 646067) B646067
theorem B430731 : Blo 428775 430731 := bstep (se 1 (by rfl) ⟨323048, by rfl⟩ : syracuseStep 430731 = 646097) B646097
theorem B430743 : Blo 428775 430743 := bstep (se 1 (by rfl) ⟨323057, by rfl⟩ : syracuseStep 430743 = 646115) B646115
theorem B430763 : Blo 428775 430763 := bstep (se 1 (by rfl) ⟨323072, by rfl⟩ : syracuseStep 430763 = 646145) B646145
theorem B430775 : Blo 428775 430775 := bstep (se 1 (by rfl) ⟨323081, by rfl⟩ : syracuseStep 430775 = 646163) B646163
theorem B430795 : Blo 428775 430795 := bstep (se 1 (by rfl) ⟨323096, by rfl⟩ : syracuseStep 430795 = 646193) B646193
theorem B725719 : Blo 428775 725719 := bstep (se 1 (by rfl) ⟨544289, by rfl⟩ : syracuseStep 725719 = 1088579) B1088579
theorem B430807 : Blo 428775 430807 := bstep (se 1 (by rfl) ⟨323105, by rfl⟩ : syracuseStep 430807 = 646211) B646211
theorem B1086169 : Blo 428775 1086169 := bstep (se 2 (by rfl) ⟨407313, by rfl⟩ : syracuseStep 1086169 = 814627) B814627
theorem B430827 : Blo 428775 430827 := bstep (se 1 (by rfl) ⟨323120, by rfl⟩ : syracuseStep 430827 = 646241) B646241
theorem B430839 : Blo 428775 430839 := bstep (se 1 (by rfl) ⟨323129, by rfl⟩ : syracuseStep 430839 = 646259) B646259
theorem B430859 : Blo 428775 430859 := bstep (se 1 (by rfl) ⟨323144, by rfl⟩ : syracuseStep 430859 = 646289) B646289
theorem B430871 : Blo 428775 430871 := bstep (se 1 (by rfl) ⟨323153, by rfl⟩ : syracuseStep 430871 = 646307) B646307
theorem B430891 : Blo 428775 430891 := bstep (se 1 (by rfl) ⟨323168, by rfl⟩ : syracuseStep 430891 = 646337) B646337
theorem B430903 : Blo 428775 430903 := bstep (se 1 (by rfl) ⟨323177, by rfl⟩ : syracuseStep 430903 = 646355) B646355
theorem B430923 : Blo 428775 430923 := bstep (se 1 (by rfl) ⟨323192, by rfl⟩ : syracuseStep 430923 = 646385) B646385
theorem B430935 : Blo 428775 430935 := bstep (se 1 (by rfl) ⟨323201, by rfl⟩ : syracuseStep 430935 = 646403) B646403
theorem B430955 : Blo 428775 430955 := bstep (se 1 (by rfl) ⟨323216, by rfl⟩ : syracuseStep 430955 = 646433) B646433
theorem B430967 : Blo 428775 430967 := bstep (se 1 (by rfl) ⟨323225, by rfl⟩ : syracuseStep 430967 = 646451) B646451
theorem B430987 : Blo 428775 430987 := bstep (se 1 (by rfl) ⟨323240, by rfl⟩ : syracuseStep 430987 = 646481) B646481
theorem B430999 : Blo 428775 430999 := bstep (se 1 (by rfl) ⟨323249, by rfl⟩ : syracuseStep 430999 = 646499) B646499
theorem B431019 : Blo 428775 431019 := bstep (se 1 (by rfl) ⟨323264, by rfl⟩ : syracuseStep 431019 = 646529) B646529
theorem B431031 : Blo 428775 431031 := bstep (se 1 (by rfl) ⟨323273, by rfl⟩ : syracuseStep 431031 = 646547) B646547
theorem B1315777 : Blo 428775 1315777 := bstep (se 2 (by rfl) ⟨493416, by rfl⟩ : syracuseStep 1315777 = 986833) B986833
theorem B431051 : Blo 428775 431051 := bstep (se 1 (by rfl) ⟨323288, by rfl⟩ : syracuseStep 431051 = 646577) B646577
theorem B431063 : Blo 428775 431063 := bstep (se 1 (by rfl) ⟨323297, by rfl⟩ : syracuseStep 431063 = 646595) B646595
theorem B431083 : Blo 428775 431083 := bstep (se 1 (by rfl) ⟨323312, by rfl⟩ : syracuseStep 431083 = 646625) B646625
theorem B431095 : Blo 428775 431095 := bstep (se 1 (by rfl) ⟨323321, by rfl⟩ : syracuseStep 431095 = 646643) B646643
theorem B431115 : Blo 428775 431115 := bstep (se 1 (by rfl) ⟨323336, by rfl⟩ : syracuseStep 431115 = 646673) B646673
theorem B431127 : Blo 428775 431127 := bstep (se 1 (by rfl) ⟨323345, by rfl⟩ : syracuseStep 431127 = 646691) B646691
theorem B431147 : Blo 428775 431147 := bstep (se 1 (by rfl) ⟨323360, by rfl⟩ : syracuseStep 431147 = 646721) B646721
theorem B431159 : Blo 428775 431159 := bstep (se 1 (by rfl) ⟨323369, by rfl⟩ : syracuseStep 431159 = 646739) B646739
theorem B431179 : Blo 428775 431179 := bstep (se 1 (by rfl) ⟨323384, by rfl⟩ : syracuseStep 431179 = 646769) B646769
theorem B431191 : Blo 428775 431191 := bstep (se 1 (by rfl) ⟨323393, by rfl⟩ : syracuseStep 431191 = 646787) B646787
theorem B2757725 : Blo 428775 2757725 := bstep (se 3 (by rfl) ⟨517073, by rfl⟩ : syracuseStep 2757725 = 1034147) B1034147
theorem B431211 : Blo 428775 431211 := bstep (se 1 (by rfl) ⟨323408, by rfl⟩ : syracuseStep 431211 = 646817) B646817
theorem B431223 : Blo 428775 431223 := bstep (se 1 (by rfl) ⟨323417, by rfl⟩ : syracuseStep 431223 = 646835) B646835
theorem B1840259 : Blo 428775 1840259 := bstep (se 1 (by rfl) ⟨1380194, by rfl⟩ : syracuseStep 1840259 = 2760389) B2760389
theorem B431243 : Blo 428775 431243 := bstep (se 1 (by rfl) ⟨323432, by rfl⟩ : syracuseStep 431243 = 646865) B646865
theorem B431255 : Blo 428775 431255 := bstep (se 1 (by rfl) ⟨323441, by rfl⟩ : syracuseStep 431255 = 646883) B646883
theorem B431275 : Blo 428775 431275 := bstep (se 1 (by rfl) ⟨323456, by rfl⟩ : syracuseStep 431275 = 646913) B646913
theorem B431287 : Blo 428775 431287 := bstep (se 1 (by rfl) ⟨323465, by rfl⟩ : syracuseStep 431287 = 646931) B646931
theorem B431307 : Blo 428775 431307 := bstep (se 1 (by rfl) ⟨323480, by rfl⟩ : syracuseStep 431307 = 646961) B646961
theorem B431319 : Blo 428775 431319 := bstep (se 1 (by rfl) ⟨323489, by rfl⟩ : syracuseStep 431319 = 646979) B646979
theorem B3118297 : Blo 428775 3118297 := bstep (se 2 (by rfl) ⟨1169361, by rfl⟩ : syracuseStep 3118297 = 2338723) B2338723
theorem B431339 : Blo 428775 431339 := bstep (se 1 (by rfl) ⟨323504, by rfl⟩ : syracuseStep 431339 = 647009) B647009
theorem B431351 : Blo 428775 431351 := bstep (se 1 (by rfl) ⟨323513, by rfl⟩ : syracuseStep 431351 = 647027) B647027
theorem B431371 : Blo 428775 431371 := bstep (se 1 (by rfl) ⟨323528, by rfl⟩ : syracuseStep 431371 = 647057) B647057
theorem B431383 : Blo 428775 431383 := bstep (se 1 (by rfl) ⟨323537, by rfl⟩ : syracuseStep 431383 = 647075) B647075
theorem B431403 : Blo 428775 431403 := bstep (se 1 (by rfl) ⟨323552, by rfl⟩ : syracuseStep 431403 = 647105) B647105
theorem B431415 : Blo 428775 431415 := bstep (se 1 (by rfl) ⟨323561, by rfl⟩ : syracuseStep 431415 = 647123) B647123
theorem B726347 : Blo 428775 726347 := bstep (se 1 (by rfl) ⟨544760, by rfl⟩ : syracuseStep 726347 = 1089521) B1089521
theorem B431435 : Blo 428775 431435 := bstep (se 1 (by rfl) ⟨323576, by rfl⟩ : syracuseStep 431435 = 647153) B647153
theorem B431447 : Blo 428775 431447 := bstep (se 1 (by rfl) ⟨323585, by rfl⟩ : syracuseStep 431447 = 647171) B647171
theorem B431467 : Blo 428775 431467 := bstep (se 1 (by rfl) ⟨323600, by rfl⟩ : syracuseStep 431467 = 647201) B647201
theorem B431479 : Blo 428775 431479 := bstep (se 1 (by rfl) ⟨323609, by rfl⟩ : syracuseStep 431479 = 647219) B647219
theorem B431499 : Blo 428775 431499 := bstep (se 1 (by rfl) ⟨323624, by rfl⟩ : syracuseStep 431499 = 647249) B647249
theorem B431511 : Blo 428775 431511 := bstep (se 1 (by rfl) ⟨323633, by rfl⟩ : syracuseStep 431511 = 647267) B647267
theorem B431531 : Blo 428775 431531 := bstep (se 1 (by rfl) ⟨323648, by rfl⟩ : syracuseStep 431531 = 647297) B647297
theorem B2463155 : Blo 428775 2463155 := bstep (se 1 (by rfl) ⟨1847366, by rfl⟩ : syracuseStep 2463155 = 3694733) B3694733
theorem B431543 : Blo 428775 431543 := bstep (se 1 (by rfl) ⟨323657, by rfl⟩ : syracuseStep 431543 = 647315) B647315
theorem B1447361 : Blo 428775 1447361 := bstep (se 2 (by rfl) ⟨542760, by rfl⟩ : syracuseStep 1447361 = 1085521) B1085521
theorem B726475 : Blo 428775 726475 := bstep (se 1 (by rfl) ⟨544856, by rfl⟩ : syracuseStep 726475 = 1089713) B1089713
theorem B1381835 : Blo 428775 1381835 := bstep (se 1 (by rfl) ⟨1036376, by rfl⟩ : syracuseStep 1381835 = 2072753) B2072753
theorem B431563 : Blo 428775 431563 := bstep (se 1 (by rfl) ⟨323672, by rfl⟩ : syracuseStep 431563 = 647345) B647345
theorem B431575 : Blo 428775 431575 := bstep (se 1 (by rfl) ⟨323681, by rfl⟩ : syracuseStep 431575 = 647363) B647363
theorem B431595 : Blo 428775 431595 := bstep (se 1 (by rfl) ⟨323696, by rfl⟩ : syracuseStep 431595 = 647393) B647393
theorem B431607 : Blo 428775 431607 := bstep (se 1 (by rfl) ⟨323705, by rfl⟩ : syracuseStep 431607 = 647411) B647411
theorem B431627 : Blo 428775 431627 := bstep (se 1 (by rfl) ⟨323720, by rfl⟩ : syracuseStep 431627 = 647441) B647441
theorem B431639 : Blo 428775 431639 := bstep (se 1 (by rfl) ⟨323729, by rfl⟩ : syracuseStep 431639 = 647459) B647459
theorem B431659 : Blo 428775 431659 := bstep (se 1 (by rfl) ⟨323744, by rfl⟩ : syracuseStep 431659 = 647489) B647489
theorem B431671 : Blo 428775 431671 := bstep (se 1 (by rfl) ⟨323753, by rfl⟩ : syracuseStep 431671 = 647507) B647507
theorem B464459 : Blo 428775 464459 := bstep (se 1 (by rfl) ⟨348344, by rfl⟩ : syracuseStep 464459 = 696689) B696689
theorem B431691 : Blo 428775 431691 := bstep (se 1 (by rfl) ⟨323768, by rfl⟩ : syracuseStep 431691 = 647537) B647537
theorem B431703 : Blo 428775 431703 := bstep (se 1 (by rfl) ⟨323777, by rfl⟩ : syracuseStep 431703 = 647555) B647555
theorem B726617 : Blo 428775 726617 := bstep (se 2 (by rfl) ⟨272481, by rfl⟩ : syracuseStep 726617 = 544963) B544963
theorem B431723 : Blo 428775 431723 := bstep (se 1 (by rfl) ⟨323792, by rfl⟩ : syracuseStep 431723 = 647585) B647585
theorem B431735 : Blo 428775 431735 := bstep (se 1 (by rfl) ⟨323801, by rfl⟩ : syracuseStep 431735 = 647603) B647603
theorem B431755 : Blo 428775 431755 := bstep (se 1 (by rfl) ⟨323816, by rfl⟩ : syracuseStep 431755 = 647633) B647633
theorem B431767 : Blo 428775 431767 := bstep (se 1 (by rfl) ⟨323825, by rfl⟩ : syracuseStep 431767 = 647651) B647651
theorem B431787 : Blo 428775 431787 := bstep (se 1 (by rfl) ⟨323840, by rfl⟩ : syracuseStep 431787 = 647681) B647681
theorem B431799 : Blo 428775 431799 := bstep (se 1 (by rfl) ⟨323849, by rfl⟩ : syracuseStep 431799 = 647699) B647699
theorem B431819 : Blo 428775 431819 := bstep (se 1 (by rfl) ⟨323864, by rfl⟩ : syracuseStep 431819 = 647729) B647729
theorem B431831 : Blo 428775 431831 := bstep (se 1 (by rfl) ⟨323873, by rfl⟩ : syracuseStep 431831 = 647747) B647747
theorem B726745 : Blo 428775 726745 := bstep (se 2 (by rfl) ⟨272529, by rfl⟩ : syracuseStep 726745 = 545059) B545059
theorem B431851 : Blo 428775 431851 := bstep (se 1 (by rfl) ⟨323888, by rfl⟩ : syracuseStep 431851 = 647777) B647777
theorem B431863 : Blo 428775 431863 := bstep (se 1 (by rfl) ⟨323897, by rfl⟩ : syracuseStep 431863 = 647795) B647795
theorem B923393 : Blo 428775 923393 := bstep (se 2 (by rfl) ⟨346272, by rfl⟩ : syracuseStep 923393 = 692545) B692545
theorem B431883 : Blo 428775 431883 := bstep (se 1 (by rfl) ⟨323912, by rfl⟩ : syracuseStep 431883 = 647825) B647825
theorem B431895 : Blo 428775 431895 := bstep (se 1 (by rfl) ⟨323921, by rfl⟩ : syracuseStep 431895 = 647843) B647843
theorem B431915 : Blo 428775 431915 := bstep (se 1 (by rfl) ⟨323936, by rfl⟩ : syracuseStep 431915 = 647873) B647873
theorem B1087283 : Blo 428775 1087283 := bstep (se 1 (by rfl) ⟨815462, by rfl⟩ : syracuseStep 1087283 = 1630925) B1630925
theorem B431927 : Blo 428775 431927 := bstep (se 1 (by rfl) ⟨323945, by rfl⟩ : syracuseStep 431927 = 647891) B647891
theorem B431947 : Blo 428775 431947 := bstep (se 1 (by rfl) ⟨323960, by rfl⟩ : syracuseStep 431947 = 647921) B647921
theorem B431959 : Blo 428775 431959 := bstep (se 1 (by rfl) ⟨323969, by rfl⟩ : syracuseStep 431959 = 647939) B647939
theorem B431979 : Blo 428775 431979 := bstep (se 1 (by rfl) ⟨323984, by rfl⟩ : syracuseStep 431979 = 647969) B647969
theorem B431991 : Blo 428775 431991 := bstep (se 1 (by rfl) ⟨323993, by rfl⟩ : syracuseStep 431991 = 647987) B647987
theorem B432011 : Blo 428775 432011 := bstep (se 1 (by rfl) ⟨324008, by rfl⟩ : syracuseStep 432011 = 648017) B648017
theorem B432023 : Blo 428775 432023 := bstep (se 1 (by rfl) ⟨324017, by rfl⟩ : syracuseStep 432023 = 648035) B648035
theorem B432043 : Blo 428775 432043 := bstep (se 1 (by rfl) ⟨324032, by rfl⟩ : syracuseStep 432043 = 648065) B648065
theorem B432055 : Blo 428775 432055 := bstep (se 1 (by rfl) ⟨324041, by rfl⟩ : syracuseStep 432055 = 648083) B648083
theorem B432075 : Blo 428775 432075 := bstep (se 1 (by rfl) ⟨324056, by rfl⟩ : syracuseStep 432075 = 648113) B648113
theorem B432087 : Blo 428775 432087 := bstep (se 1 (by rfl) ⟨324065, by rfl⟩ : syracuseStep 432087 = 648131) B648131
theorem B1447901 : Blo 428775 1447901 := bstep (se 3 (by rfl) ⟨271481, by rfl⟩ : syracuseStep 1447901 = 542963) B542963
theorem B432107 : Blo 428775 432107 := bstep (se 1 (by rfl) ⟨324080, by rfl⟩ : syracuseStep 432107 = 648161) B648161
theorem B432119 : Blo 428775 432119 := bstep (se 1 (by rfl) ⟨324089, by rfl⟩ : syracuseStep 432119 = 648179) B648179
theorem B432139 : Blo 428775 432139 := bstep (se 1 (by rfl) ⟨324104, by rfl⟩ : syracuseStep 432139 = 648209) B648209
theorem B432151 : Blo 428775 432151 := bstep (se 1 (by rfl) ⟨324113, by rfl⟩ : syracuseStep 432151 = 648227) B648227
theorem B497707 : Blo 428775 497707 := bstep (se 1 (by rfl) ⟨373280, by rfl⟩ : syracuseStep 497707 = 746561) B746561
theorem B432171 : Blo 428775 432171 := bstep (se 1 (by rfl) ⟨324128, by rfl⟩ : syracuseStep 432171 = 648257) B648257
theorem B432183 : Blo 428775 432183 := bstep (se 1 (by rfl) ⟨324137, by rfl⟩ : syracuseStep 432183 = 648275) B648275
theorem B432203 : Blo 428775 432203 := bstep (se 1 (by rfl) ⟨324152, by rfl⟩ : syracuseStep 432203 = 648305) B648305
theorem B432215 : Blo 428775 432215 := bstep (se 1 (by rfl) ⟨324161, by rfl⟩ : syracuseStep 432215 = 648323) B648323
theorem B1087577 : Blo 428775 1087577 := bstep (se 2 (by rfl) ⟨407841, by rfl⟩ : syracuseStep 1087577 = 815683) B815683
theorem B432235 : Blo 428775 432235 := bstep (se 1 (by rfl) ⟨324176, by rfl⟩ : syracuseStep 432235 = 648353) B648353
theorem B432247 : Blo 428775 432247 := bstep (se 1 (by rfl) ⟨324185, by rfl⟩ : syracuseStep 432247 = 648371) B648371
theorem B432267 : Blo 428775 432267 := bstep (se 1 (by rfl) ⟨324200, by rfl⟩ : syracuseStep 432267 = 648401) B648401
theorem B432279 : Blo 428775 432279 := bstep (se 1 (by rfl) ⟨324209, by rfl⟩ : syracuseStep 432279 = 648419) B648419
theorem B432299 : Blo 428775 432299 := bstep (se 1 (by rfl) ⟨324224, by rfl⟩ : syracuseStep 432299 = 648449) B648449
theorem B1382579 : Blo 428775 1382579 := bstep (se 1 (by rfl) ⟨1036934, by rfl⟩ : syracuseStep 1382579 = 2073869) B2073869
theorem B432311 : Blo 428775 432311 := bstep (se 1 (by rfl) ⟨324233, by rfl⟩ : syracuseStep 432311 = 648467) B648467
theorem B432331 : Blo 428775 432331 := bstep (se 1 (by rfl) ⟨324248, by rfl⟩ : syracuseStep 432331 = 648497) B648497
theorem B432343 : Blo 428775 432343 := bstep (se 1 (by rfl) ⟨324257, by rfl⟩ : syracuseStep 432343 = 648515) B648515
theorem B432363 : Blo 428775 432363 := bstep (se 1 (by rfl) ⟨324272, by rfl⟩ : syracuseStep 432363 = 648545) B648545
theorem B432375 : Blo 428775 432375 := bstep (se 1 (by rfl) ⟨324281, by rfl⟩ : syracuseStep 432375 = 648563) B648563
theorem B432395 : Blo 428775 432395 := bstep (se 1 (by rfl) ⟨324296, by rfl⟩ : syracuseStep 432395 = 648593) B648593
theorem B727319 : Blo 428775 727319 := bstep (se 1 (by rfl) ⟨545489, by rfl⟩ : syracuseStep 727319 = 1090979) B1090979
theorem B432407 : Blo 428775 432407 := bstep (se 1 (by rfl) ⟨324305, by rfl⟩ : syracuseStep 432407 = 648611) B648611
theorem B432427 : Blo 428775 432427 := bstep (se 1 (by rfl) ⟨324320, by rfl⟩ : syracuseStep 432427 = 648641) B648641
theorem B432439 : Blo 428775 432439 := bstep (se 1 (by rfl) ⟨324329, by rfl⟩ : syracuseStep 432439 = 648659) B648659
theorem B432459 : Blo 428775 432459 := bstep (se 1 (by rfl) ⟨324344, by rfl⟩ : syracuseStep 432459 = 648689) B648689
theorem B432471 : Blo 428775 432471 := bstep (se 1 (by rfl) ⟨324353, by rfl⟩ : syracuseStep 432471 = 648707) B648707
theorem B432491 : Blo 428775 432491 := bstep (se 1 (by rfl) ⟨324368, by rfl⟩ : syracuseStep 432491 = 648737) B648737
theorem B432503 : Blo 428775 432503 := bstep (se 1 (by rfl) ⟨324377, by rfl⟩ : syracuseStep 432503 = 648755) B648755
theorem B432523 : Blo 428775 432523 := bstep (se 1 (by rfl) ⟨324392, by rfl⟩ : syracuseStep 432523 = 648785) B648785
theorem B727447 : Blo 428775 727447 := bstep (se 1 (by rfl) ⟨545585, by rfl⟩ : syracuseStep 727447 = 1091171) B1091171
theorem B432535 : Blo 428775 432535 := bstep (se 1 (by rfl) ⟨324401, by rfl⟩ : syracuseStep 432535 = 648803) B648803
theorem B432555 : Blo 428775 432555 := bstep (se 1 (by rfl) ⟨324416, by rfl⟩ : syracuseStep 432555 = 648833) B648833
theorem B432567 : Blo 428775 432567 := bstep (se 1 (by rfl) ⟨324425, by rfl⟩ : syracuseStep 432567 = 648851) B648851
theorem B432587 : Blo 428775 432587 := bstep (se 1 (by rfl) ⟨324440, by rfl⟩ : syracuseStep 432587 = 648881) B648881
theorem B432599 : Blo 428775 432599 := bstep (se 1 (by rfl) ⟨324449, by rfl⟩ : syracuseStep 432599 = 648899) B648899
theorem B432619 : Blo 428775 432619 := bstep (se 1 (by rfl) ⟨324464, by rfl⟩ : syracuseStep 432619 = 648929) B648929
theorem B432631 : Blo 428775 432631 := bstep (se 1 (by rfl) ⟨324473, by rfl⟩ : syracuseStep 432631 = 648947) B648947
theorem B432651 : Blo 428775 432651 := bstep (se 1 (by rfl) ⟨324488, by rfl⟩ : syracuseStep 432651 = 648977) B648977
theorem B432663 : Blo 428775 432663 := bstep (se 1 (by rfl) ⟨324497, by rfl⟩ : syracuseStep 432663 = 648995) B648995
theorem B432683 : Blo 428775 432683 := bstep (se 1 (by rfl) ⟨324512, by rfl⟩ : syracuseStep 432683 = 649025) B649025
theorem B432695 : Blo 428775 432695 := bstep (se 1 (by rfl) ⟨324521, by rfl⟩ : syracuseStep 432695 = 649043) B649043
theorem B432715 : Blo 428775 432715 := bstep (se 1 (by rfl) ⟨324536, by rfl⟩ : syracuseStep 432715 = 649073) B649073
theorem B432727 : Blo 428775 432727 := bstep (se 1 (by rfl) ⟨324545, by rfl⟩ : syracuseStep 432727 = 649091) B649091
theorem B924247 : Blo 428775 924247 := bstep (se 1 (by rfl) ⟨693185, by rfl⟩ : syracuseStep 924247 = 1386371) B1386371
theorem B432747 : Blo 428775 432747 := bstep (se 1 (by rfl) ⟨324560, by rfl⟩ : syracuseStep 432747 = 649121) B649121
theorem B432759 : Blo 428775 432759 := bstep (se 1 (by rfl) ⟨324569, by rfl⟩ : syracuseStep 432759 = 649139) B649139
theorem B15276853 : Blo 428775 15276853 := bstep (se 5 (by rfl) ⟨716102, by rfl⟩ : syracuseStep 15276853 = 1432205) B1432205
theorem B2464613 : Blo 428775 2464613 := bstep (se 4 (by rfl) ⟨231057, by rfl⟩ : syracuseStep 2464613 = 462115) B462115
theorem B4135859 : Blo 428775 4135859 := bstep (se 1 (by rfl) ⟨3101894, by rfl⟩ : syracuseStep 4135859 = 6203789) B6203789
theorem B728075 : Blo 428775 728075 := bstep (se 1 (by rfl) ⟨546056, by rfl⟩ : syracuseStep 728075 = 1092113) B1092113
theorem B1743923 : Blo 428775 1743923 := bstep (se 1 (by rfl) ⟨1307942, by rfl⟩ : syracuseStep 1743923 = 2615885) B2615885
theorem B1383475 : Blo 428775 1383475 := bstep (se 1 (by rfl) ⟨1037606, by rfl⟩ : syracuseStep 1383475 = 2075213) B2075213
theorem B1449035 : Blo 428775 1449035 := bstep (se 1 (by rfl) ⟨1086776, by rfl⟩ : syracuseStep 1449035 = 2173553) B2173553
theorem B728203 : Blo 428775 728203 := bstep (se 1 (by rfl) ⟨546152, by rfl⟩ : syracuseStep 728203 = 1092305) B1092305
theorem B728345 : Blo 428775 728345 := bstep (se 2 (by rfl) ⟨273129, by rfl⟩ : syracuseStep 728345 = 546259) B546259
theorem B1449305 : Blo 428775 1449305 := bstep (se 2 (by rfl) ⟨543489, by rfl⟩ : syracuseStep 1449305 = 1086979) B1086979
theorem B2203031 : Blo 428775 2203031 := bstep (se 1 (by rfl) ⟨1652273, by rfl⟩ : syracuseStep 2203031 = 3304547) B3304547
theorem B728473 : Blo 428775 728473 := bstep (se 2 (by rfl) ⟨273177, by rfl⟩ : syracuseStep 728473 = 546355) B546355
theorem B2072081 : Blo 428775 2072081 := bstep (se 2 (by rfl) ⟨777030, by rfl⟩ : syracuseStep 2072081 = 1554061) B1554061
theorem B1089227 : Blo 428775 1089227 := bstep (se 1 (by rfl) ⟨816920, by rfl⟩ : syracuseStep 1089227 = 1633841) B1633841
theorem B3677987 : Blo 428775 3677987 := bstep (se 1 (by rfl) ⟨2758490, by rfl⟩ : syracuseStep 3677987 = 5516981) B5516981
theorem B729047 : Blo 428775 729047 := bstep (se 1 (by rfl) ⟨546785, by rfl⟩ : syracuseStep 729047 = 1093571) B1093571
theorem B1450007 : Blo 428775 1450007 := bstep (se 1 (by rfl) ⟨1087505, by rfl⟩ : syracuseStep 1450007 = 2175011) B2175011
theorem B4464715 : Blo 428775 4464715 := bstep (se 1 (by rfl) ⟨3348536, by rfl⟩ : syracuseStep 4464715 = 6697073) B6697073
theorem B5513291 : Blo 428775 5513291 := bstep (se 1 (by rfl) ⟨4134968, by rfl⟩ : syracuseStep 5513291 = 8269937) B8269937
theorem B729175 : Blo 428775 729175 := bstep (se 1 (by rfl) ⟨546881, by rfl⟩ : syracuseStep 729175 = 1093763) B1093763
theorem B1450547 : Blo 428775 1450547 := bstep (se 1 (by rfl) ⟨1087910, by rfl⟩ : syracuseStep 1450547 = 2175821) B2175821
theorem B1090199 : Blo 428775 1090199 := bstep (se 1 (by rfl) ⟨817649, by rfl⟩ : syracuseStep 1090199 = 1635299) B1635299
theorem B467659 : Blo 428775 467659 := bstep (se 1 (by rfl) ⟨350744, by rfl⟩ : syracuseStep 467659 = 701489) B701489
theorem B729803 : Blo 428775 729803 := bstep (se 1 (by rfl) ⟨547352, by rfl⟩ : syracuseStep 729803 = 1094705) B1094705
theorem B2171609 : Blo 428775 2171609 := bstep (se 2 (by rfl) ⟨814353, by rfl⟩ : syracuseStep 2171609 = 1628707) B1628707
theorem B7840577 : Blo 428775 7840577 := bstep (se 2 (by rfl) ⟨2940216, by rfl⟩ : syracuseStep 7840577 = 5880433) B5880433
theorem B1450817 : Blo 428775 1450817 := bstep (se 2 (by rfl) ⟨544056, by rfl⟩ : syracuseStep 1450817 = 1088113) B1088113
theorem B729931 : Blo 428775 729931 := bstep (se 1 (by rfl) ⟨547448, by rfl⟩ : syracuseStep 729931 = 1094897) B1094897
theorem B1745867 : Blo 428775 1745867 := bstep (se 1 (by rfl) ⟨1309400, by rfl⟩ : syracuseStep 1745867 = 2618801) B2618801
theorem B730073 : Blo 428775 730073 := bstep (se 2 (by rfl) ⟨273777, by rfl⟩ : syracuseStep 730073 = 547555) B547555
theorem B435275 : Blo 428775 435275 := bstep (se 1 (by rfl) ⟨326456, by rfl⟩ : syracuseStep 435275 = 652913) B652913
theorem B730201 : Blo 428775 730201 := bstep (se 2 (by rfl) ⟨273825, by rfl⟩ : syracuseStep 730201 = 547651) B547651
theorem B1385693 : Blo 428775 1385693 := bstep (se 3 (by rfl) ⟨259817, by rfl⟩ : syracuseStep 1385693 = 519635) B519635
theorem B1090867 : Blo 428775 1090867 := bstep (se 1 (by rfl) ⟨818150, by rfl⟩ : syracuseStep 1090867 = 1636301) B1636301
theorem B1844531 : Blo 428775 1844531 := bstep (se 1 (by rfl) ⟨1383398, by rfl⟩ : syracuseStep 1844531 = 2766797) B2766797
theorem B1451357 : Blo 428775 1451357 := bstep (se 3 (by rfl) ⟨272129, by rfl⟩ : syracuseStep 1451357 = 544259) B544259
theorem B1222067 : Blo 428775 1222067 := bstep (se 1 (by rfl) ⟨916550, by rfl⟩ : syracuseStep 1222067 = 1833101) B1833101
theorem B1091009 : Blo 428775 1091009 := bstep (se 2 (by rfl) ⟨409128, by rfl⟩ : syracuseStep 1091009 = 818257) B818257
theorem B1222465 : Blo 428775 1222465 := bstep (se 2 (by rfl) ⟨458424, by rfl⟩ : syracuseStep 1222465 = 916849) B916849
theorem B1746905 : Blo 428775 1746905 := bstep (se 2 (by rfl) ⟨655089, by rfl⟩ : syracuseStep 1746905 = 1310179) B1310179
theorem B2173229 : Blo 428775 2173229 := bstep (se 3 (by rfl) ⟨407480, by rfl⟩ : syracuseStep 2173229 = 814961) B814961
theorem B1452491 : Blo 428775 1452491 := bstep (se 1 (by rfl) ⟨1089368, by rfl⟩ : syracuseStep 1452491 = 2178737) B2178737
theorem B1092275 : Blo 428775 1092275 := bstep (se 1 (by rfl) ⟨819206, by rfl⟩ : syracuseStep 1092275 = 1638413) B1638413
theorem B1452761 : Blo 428775 1452761 := bstep (se 2 (by rfl) ⟨544785, by rfl⟩ : syracuseStep 1452761 = 1089571) B1089571
theorem B2763821 : Blo 428775 2763821 := bstep (se 3 (by rfl) ⟨518216, by rfl⟩ : syracuseStep 2763821 = 1036433) B1036433
theorem B1092811 : Blo 428775 1092811 := bstep (se 1 (by rfl) ⟨819608, by rfl⟩ : syracuseStep 1092811 = 1639217) B1639217
theorem B3681611 : Blo 428775 3681611 := bstep (se 1 (by rfl) ⟨2761208, by rfl⟩ : syracuseStep 3681611 = 5522417) B5522417
theorem B1092953 : Blo 428775 1092953 := bstep (se 2 (by rfl) ⟨409857, by rfl⟩ : syracuseStep 1092953 = 819715) B819715
theorem B437611 : Blo 428775 437611 := bstep (se 1 (by rfl) ⟨328208, by rfl⟩ : syracuseStep 437611 = 656417) B656417
theorem B1453463 : Blo 428775 1453463 := bstep (se 1 (by rfl) ⟨1090097, by rfl⟩ : syracuseStep 1453463 = 2180195) B2180195
theorem B1257011 : Blo 428775 1257011 := bstep (se 1 (by rfl) ⟨942758, by rfl⟩ : syracuseStep 1257011 = 1885517) B1885517
theorem B1650563 : Blo 428775 1650563 := bstep (se 1 (by rfl) ⟨1237922, by rfl⟩ : syracuseStep 1650563 = 2475845) B2475845
theorem B25472945 : Blo 428775 25472945 := bstep (se 2 (by rfl) ⟨9552354, by rfl⟩ : syracuseStep 25472945 = 19104709) B19104709
theorem B1454003 : Blo 428775 1454003 := bstep (se 1 (by rfl) ⟨1090502, by rfl⟩ : syracuseStep 1454003 = 2181005) B2181005
theorem B1552459 : Blo 428775 1552459 := bstep (se 1 (by rfl) ⟨1164344, by rfl⟩ : syracuseStep 1552459 = 2328689) B2328689
theorem B1093783 : Blo 428775 1093783 := bstep (se 1 (by rfl) ⟨820337, by rfl⟩ : syracuseStep 1093783 = 1640675) B1640675
theorem B1454273 : Blo 428775 1454273 := bstep (se 2 (by rfl) ⟨545352, by rfl⟩ : syracuseStep 1454273 = 1090705) B1090705
theorem B1224983 : Blo 428775 1224983 := bstep (se 1 (by rfl) ⟨918737, by rfl⟩ : syracuseStep 1224983 = 1837475) B1837475
theorem B7352693 : Blo 428775 7352693 := bstep (se 5 (by rfl) ⟨344657, by rfl⟩ : syracuseStep 7352693 = 689315) B689315
theorem B3912113 : Blo 428775 3912113 := bstep (se 2 (by rfl) ⟨1467042, by rfl⟩ : syracuseStep 3912113 = 2934085) B2934085
theorem B832025 : Blo 428775 832025 := bstep (se 2 (by rfl) ⟨312009, by rfl⟩ : syracuseStep 832025 = 624019) B624019
theorem B1094219 : Blo 428775 1094219 := bstep (se 1 (by rfl) ⟨820664, by rfl⟩ : syracuseStep 1094219 = 1641329) B1641329
theorem B8303309 : Blo 428775 8303309 := bstep (se 3 (by rfl) ⟨1556870, by rfl⟩ : syracuseStep 8303309 = 3113741) B3113741
theorem B1454813 : Blo 428775 1454813 := bstep (se 3 (by rfl) ⟨272777, by rfl⟩ : syracuseStep 1454813 = 545555) B545555
theorem B1094593 : Blo 428775 1094593 := bstep (se 2 (by rfl) ⟨410472, by rfl⟩ : syracuseStep 1094593 = 820945) B820945
theorem B2077771 : Blo 428775 2077771 := bstep (se 1 (by rfl) ⟨1558328, by rfl⟩ : syracuseStep 2077771 = 3116657) B3116657
theorem B1651915 : Blo 428775 1651915 := bstep (se 1 (by rfl) ⟨1238936, by rfl⟩ : syracuseStep 1651915 = 2477873) B2477873
theorem B1553843 : Blo 428775 1553843 := bstep (se 1 (by rfl) ⟨1165382, by rfl⟩ : syracuseStep 1553843 = 2330765) B2330765
theorem B1095191 : Blo 428775 1095191 := bstep (se 1 (by rfl) ⟨821393, by rfl⟩ : syracuseStep 1095191 = 1642787) B1642787
theorem B1226315 : Blo 428775 1226315 := bstep (se 1 (by rfl) ⟨919736, by rfl⟩ : syracuseStep 1226315 = 1839473) B1839473
theorem B2766487 : Blo 428775 2766487 := bstep (se 1 (by rfl) ⟨2074865, by rfl⟩ : syracuseStep 2766487 = 4149731) B4149731
theorem B1455947 : Blo 428775 1455947 := bstep (se 1 (by rfl) ⟨1091960, by rfl⟩ : syracuseStep 1455947 = 2183921) B2183921
theorem B3684275 : Blo 428775 3684275 := bstep (se 1 (by rfl) ⟨2763206, by rfl⟩ : syracuseStep 3684275 = 5526413) B5526413
theorem B4929497 : Blo 428775 4929497 := bstep (se 2 (by rfl) ⟨1848561, by rfl⟩ : syracuseStep 4929497 = 3697123) B3697123
theorem B4995107 : Blo 428775 4995107 := bstep (se 1 (by rfl) ⟨3746330, by rfl⟩ : syracuseStep 4995107 = 7492661) B7492661
theorem B1456217 : Blo 428775 1456217 := bstep (se 2 (by rfl) ⟨546081, by rfl⟩ : syracuseStep 1456217 = 1092163) B1092163
theorem B2177117 : Blo 428775 2177117 := bstep (se 3 (by rfl) ⟨408209, by rfl⟩ : syracuseStep 2177117 = 816419) B816419
theorem B3258629 : Blo 428775 3258629 := bstep (se 4 (by rfl) ⟨305496, by rfl⟩ : syracuseStep 3258629 = 610993) B610993
theorem B964889 : Blo 428775 964889 := bstep (se 2 (by rfl) ⟨361833, by rfl⟩ : syracuseStep 964889 = 723667) B723667
theorem B964979 : Blo 428775 964979 := bstep (se 1 (by rfl) ⟨723734, by rfl⟩ : syracuseStep 964979 = 1447469) B1447469
theorem B965015 : Blo 428775 965015 := bstep (se 1 (by rfl) ⟨723761, by rfl⟩ : syracuseStep 965015 = 1447523) B1447523
theorem B3914189 : Blo 428775 3914189 := bstep (se 3 (by rfl) ⟨733910, by rfl⟩ : syracuseStep 3914189 = 1467821) B1467821
theorem B1161793 : Blo 428775 1161793 := bstep (se 2 (by rfl) ⟨435672, by rfl⟩ : syracuseStep 1161793 = 871345) B871345
theorem B965195 : Blo 428775 965195 := bstep (se 1 (by rfl) ⟨723896, by rfl⟩ : syracuseStep 965195 = 1447793) B1447793
theorem B965249 : Blo 428775 965249 := bstep (se 2 (by rfl) ⟨361968, by rfl⟩ : syracuseStep 965249 = 723937) B723937
theorem B1456919 : Blo 428775 1456919 := bstep (se 1 (by rfl) ⟨1092689, by rfl⟩ : syracuseStep 1456919 = 2185379) B2185379
theorem B965465 : Blo 428775 965465 := bstep (se 2 (by rfl) ⟨362049, by rfl⟩ : syracuseStep 965465 = 724099) B724099
theorem B7093109 : Blo 428775 7093109 := bstep (se 5 (by rfl) ⟨332489, by rfl⟩ : syracuseStep 7093109 = 664979) B664979
theorem B965555 : Blo 428775 965555 := bstep (se 1 (by rfl) ⟨724166, by rfl⟩ : syracuseStep 965555 = 1448333) B1448333
theorem B965591 : Blo 428775 965591 := bstep (se 1 (by rfl) ⟨724193, by rfl⟩ : syracuseStep 965591 = 1448387) B1448387
theorem B3685337 : Blo 428775 3685337 := bstep (se 2 (by rfl) ⟨1382001, by rfl⟩ : syracuseStep 3685337 = 2764003) B2764003
theorem B965771 : Blo 428775 965771 := bstep (se 1 (by rfl) ⟨724328, by rfl⟩ : syracuseStep 965771 = 1448657) B1448657
theorem B1227955 : Blo 428775 1227955 := bstep (se 1 (by rfl) ⟨920966, by rfl⟩ : syracuseStep 1227955 = 1841933) B1841933
theorem B965825 : Blo 428775 965825 := bstep (se 2 (by rfl) ⟨362184, by rfl⟩ : syracuseStep 965825 = 724369) B724369
theorem B1457459 : Blo 428775 1457459 := bstep (se 1 (by rfl) ⟨1093094, by rfl⟩ : syracuseStep 1457459 = 2186189) B2186189
theorem B966041 : Blo 428775 966041 := bstep (se 2 (by rfl) ⟨362265, by rfl⟩ : syracuseStep 966041 = 724531) B724531
theorem B966131 : Blo 428775 966131 := bstep (se 1 (by rfl) ⟨724598, by rfl⟩ : syracuseStep 966131 = 1449197) B1449197
theorem B966167 : Blo 428775 966167 := bstep (se 1 (by rfl) ⟨724625, by rfl⟩ : syracuseStep 966167 = 1449251) B1449251
theorem B1457729 : Blo 428775 1457729 := bstep (se 2 (by rfl) ⟨546648, by rfl⟩ : syracuseStep 1457729 = 1093297) B1093297
theorem B999001 : Blo 428775 999001 := bstep (se 2 (by rfl) ⟨374625, by rfl⟩ : syracuseStep 999001 = 749251) B749251
theorem B966347 : Blo 428775 966347 := bstep (se 1 (by rfl) ⟨724760, by rfl⟩ : syracuseStep 966347 = 1449521) B1449521
theorem B1752779 : Blo 428775 1752779 := bstep (se 1 (by rfl) ⟨1314584, by rfl⟩ : syracuseStep 1752779 = 2629169) B2629169
theorem B3096269 : Blo 428775 3096269 := bstep (se 3 (by rfl) ⟨580550, by rfl⟩ : syracuseStep 3096269 = 1161101) B1161101
theorem B1031897 : Blo 428775 1031897 := bstep (se 2 (by rfl) ⟨386961, by rfl⟩ : syracuseStep 1031897 = 773923) B773923
theorem B966401 : Blo 428775 966401 := bstep (se 2 (by rfl) ⟨362400, by rfl⟩ : syracuseStep 966401 = 724801) B724801
theorem B933655 : Blo 428775 933655 := bstep (se 1 (by rfl) ⟨700241, by rfl⟩ : syracuseStep 933655 = 1400483) B1400483
theorem B966617 : Blo 428775 966617 := bstep (se 2 (by rfl) ⟨362481, by rfl⟩ : syracuseStep 966617 = 724963) B724963
theorem B966707 : Blo 428775 966707 := bstep (se 1 (by rfl) ⟨725030, by rfl⟩ : syracuseStep 966707 = 1450061) B1450061
theorem B966743 : Blo 428775 966743 := bstep (se 1 (by rfl) ⟨725057, by rfl⟩ : syracuseStep 966743 = 1450115) B1450115
theorem B1458269 : Blo 428775 1458269 := bstep (se 3 (by rfl) ⟨273425, by rfl⟩ : syracuseStep 1458269 = 546851) B546851
theorem B2179223 : Blo 428775 2179223 := bstep (se 1 (by rfl) ⟨1634417, by rfl⟩ : syracuseStep 2179223 = 3268835) B3268835
theorem B1229003 : Blo 428775 1229003 := bstep (se 1 (by rfl) ⟨921752, by rfl⟩ : syracuseStep 1229003 = 1843505) B1843505
theorem B966923 : Blo 428775 966923 := bstep (se 1 (by rfl) ⟨725192, by rfl⟩ : syracuseStep 966923 = 1450385) B1450385
theorem B3916097 : Blo 428775 3916097 := bstep (se 2 (by rfl) ⟨1468536, by rfl⟩ : syracuseStep 3916097 = 2937073) B2937073
theorem B966977 : Blo 428775 966977 := bstep (se 2 (by rfl) ⟨362616, by rfl⟩ : syracuseStep 966977 = 725233) B725233
theorem B1556957 : Blo 428775 1556957 := bstep (se 3 (by rfl) ⟨291929, by rfl⟩ : syracuseStep 1556957 = 583859) B583859
theorem B967193 : Blo 428775 967193 := bstep (se 2 (by rfl) ⟨362697, by rfl⟩ : syracuseStep 967193 = 725395) B725395
theorem B967283 : Blo 428775 967283 := bstep (se 1 (by rfl) ⟨725462, by rfl⟩ : syracuseStep 967283 = 1450925) B1450925
theorem B3261059 : Blo 428775 3261059 := bstep (se 1 (by rfl) ⟨2445794, by rfl⟩ : syracuseStep 3261059 = 4891589) B4891589
theorem B967319 : Blo 428775 967319 := bstep (se 1 (by rfl) ⟨725489, by rfl⟩ : syracuseStep 967319 = 1450979) B1450979
theorem B3719857 : Blo 428775 3719857 := bstep (se 2 (by rfl) ⟨1394946, by rfl⟩ : syracuseStep 3719857 = 2789893) B2789893
theorem B2442059 : Blo 428775 2442059 := bstep (se 1 (by rfl) ⟨1831544, by rfl⟩ : syracuseStep 2442059 = 3663089) B3663089
theorem B967499 : Blo 428775 967499 := bstep (se 1 (by rfl) ⟨725624, by rfl⟩ : syracuseStep 967499 = 1451249) B1451249
theorem B967553 : Blo 428775 967553 := bstep (se 2 (by rfl) ⟨362832, by rfl⟩ : syracuseStep 967553 = 725665) B725665
theorem B1393625 : Blo 428775 1393625 := bstep (se 2 (by rfl) ⟨522609, by rfl⟩ : syracuseStep 1393625 = 1045219) B1045219
theorem B1557521 : Blo 428775 1557521 := bstep (se 2 (by rfl) ⟨584070, by rfl⟩ : syracuseStep 1557521 = 1168141) B1168141
theorem B967769 : Blo 428775 967769 := bstep (se 2 (by rfl) ⟨362913, by rfl⟩ : syracuseStep 967769 = 725827) B725827
theorem B1557593 : Blo 428775 1557593 := bstep (se 2 (by rfl) ⟨584097, by rfl⟩ : syracuseStep 1557593 = 1168195) B1168195
theorem B967859 : Blo 428775 967859 := bstep (se 1 (by rfl) ⟨725894, by rfl⟩ : syracuseStep 967859 = 1451789) B1451789
theorem B1459403 : Blo 428775 1459403 := bstep (se 1 (by rfl) ⟨1094552, by rfl⟩ : syracuseStep 1459403 = 2189105) B2189105
theorem B967895 : Blo 428775 967895 := bstep (se 1 (by rfl) ⟨725921, by rfl⟩ : syracuseStep 967895 = 1451843) B1451843
theorem B968075 : Blo 428775 968075 := bstep (se 1 (by rfl) ⟨726056, by rfl⟩ : syracuseStep 968075 = 1452113) B1452113
theorem B968129 : Blo 428775 968129 := bstep (se 2 (by rfl) ⟨363048, by rfl⟩ : syracuseStep 968129 = 726097) B726097
theorem B1459673 : Blo 428775 1459673 := bstep (se 2 (by rfl) ⟨547377, by rfl⟩ : syracuseStep 1459673 = 1094755) B1094755
theorem B968345 : Blo 428775 968345 := bstep (se 2 (by rfl) ⟨363129, by rfl⟩ : syracuseStep 968345 = 726259) B726259
theorem B3491545 : Blo 428775 3491545 := bstep (se 2 (by rfl) ⟨1309329, by rfl⟩ : syracuseStep 3491545 = 2618659) B2618659
theorem B968435 : Blo 428775 968435 := bstep (se 1 (by rfl) ⟨726326, by rfl⟩ : syracuseStep 968435 = 1452653) B1452653
theorem B968471 : Blo 428775 968471 := bstep (se 1 (by rfl) ⟨726353, by rfl⟩ : syracuseStep 968471 = 1452707) B1452707
theorem B1230643 : Blo 428775 1230643 := bstep (se 1 (by rfl) ⟨922982, by rfl⟩ : syracuseStep 1230643 = 1845965) B1845965
theorem B968651 : Blo 428775 968651 := bstep (se 1 (by rfl) ⟨726488, by rfl⟩ : syracuseStep 968651 = 1452977) B1452977
theorem B968705 : Blo 428775 968705 := bstep (se 2 (by rfl) ⟨363264, by rfl⟩ : syracuseStep 968705 = 726529) B726529
theorem B1230871 : Blo 428775 1230871 := bstep (se 1 (by rfl) ⟨923153, by rfl⟩ : syracuseStep 1230871 = 1846307) B1846307
theorem B7850135 : Blo 428775 7850135 := bstep (se 1 (by rfl) ⟨5887601, by rfl⟩ : syracuseStep 7850135 = 11775203) B11775203
theorem B1460375 : Blo 428775 1460375 := bstep (se 1 (by rfl) ⟨1095281, by rfl⟩ : syracuseStep 1460375 = 2190563) B2190563
theorem B968921 : Blo 428775 968921 := bstep (se 2 (by rfl) ⟨363345, by rfl⟩ : syracuseStep 968921 = 726691) B726691
theorem B7948529 : Blo 428775 7948529 := bstep (se 2 (by rfl) ⟨2980698, by rfl⟩ : syracuseStep 7948529 = 5961397) B5961397
theorem B3098897 : Blo 428775 3098897 := bstep (se 2 (by rfl) ⟨1162086, by rfl⟩ : syracuseStep 3098897 = 2324173) B2324173
theorem B969011 : Blo 428775 969011 := bstep (se 1 (by rfl) ⟨726758, by rfl⟩ : syracuseStep 969011 = 1453517) B1453517
theorem B969047 : Blo 428775 969047 := bstep (se 1 (by rfl) ⟨726785, by rfl⟩ : syracuseStep 969047 = 1453571) B1453571
theorem B543115 : Blo 428775 543115 := bstep (se 1 (by rfl) ⟨407336, by rfl⟩ : syracuseStep 543115 = 814673) B814673
theorem B969227 : Blo 428775 969227 := bstep (se 1 (by rfl) ⟨726920, by rfl⟩ : syracuseStep 969227 = 1453841) B1453841
theorem B969281 : Blo 428775 969281 := bstep (se 2 (by rfl) ⟨363480, by rfl⟩ : syracuseStep 969281 = 726961) B726961
theorem B7326449 : Blo 428775 7326449 := bstep (se 2 (by rfl) ⟨2747418, by rfl⟩ : syracuseStep 7326449 = 5494837) B5494837
theorem B969497 : Blo 428775 969497 := bstep (se 2 (by rfl) ⟨363561, by rfl⟩ : syracuseStep 969497 = 727123) B727123
theorem B772915 : Blo 428775 772915 := bstep (se 1 (by rfl) ⟨579686, by rfl⟩ : syracuseStep 772915 = 1159373) B1159373
theorem B969587 : Blo 428775 969587 := bstep (se 1 (by rfl) ⟨727190, by rfl⟩ : syracuseStep 969587 = 1454381) B1454381
theorem B969623 : Blo 428775 969623 := bstep (se 1 (by rfl) ⟨727217, by rfl⟩ : syracuseStep 969623 = 1454435) B1454435
theorem B969803 : Blo 428775 969803 := bstep (se 1 (by rfl) ⟨727352, by rfl⟩ : syracuseStep 969803 = 1454705) B1454705
theorem B969857 : Blo 428775 969857 := bstep (se 2 (by rfl) ⟨363696, by rfl⟩ : syracuseStep 969857 = 727393) B727393
theorem B544087 : Blo 428775 544087 := bstep (se 1 (by rfl) ⟨408065, by rfl⟩ : syracuseStep 544087 = 816131) B816131
theorem B970073 : Blo 428775 970073 := bstep (se 2 (by rfl) ⟨363777, by rfl⟩ : syracuseStep 970073 = 727555) B727555
theorem B4148657 : Blo 428775 4148657 := bstep (se 2 (by rfl) ⟨1555746, by rfl⟩ : syracuseStep 4148657 = 3111493) B3111493
theorem B970163 : Blo 428775 970163 := bstep (se 1 (by rfl) ⟨727622, by rfl⟩ : syracuseStep 970163 = 1455245) B1455245
theorem B970199 : Blo 428775 970199 := bstep (se 1 (by rfl) ⟨727649, by rfl⟩ : syracuseStep 970199 = 1455299) B1455299
theorem B2182787 : Blo 428775 2182787 := bstep (se 1 (by rfl) ⟨1637090, by rfl⟩ : syracuseStep 2182787 = 3274181) B3274181
theorem B970379 : Blo 428775 970379 := bstep (se 1 (by rfl) ⟨727784, by rfl⟩ : syracuseStep 970379 = 1455569) B1455569
theorem B970433 : Blo 428775 970433 := bstep (se 2 (by rfl) ⟨363912, by rfl⟩ : syracuseStep 970433 = 727825) B727825
theorem B970649 : Blo 428775 970649 := bstep (se 2 (by rfl) ⟨363993, by rfl⟩ : syracuseStep 970649 = 727987) B727987
theorem B3264461 : Blo 428775 3264461 := bstep (se 3 (by rfl) ⟨612086, by rfl⟩ : syracuseStep 3264461 = 1224173) B1224173
theorem B970739 : Blo 428775 970739 := bstep (se 1 (by rfl) ⟨728054, by rfl⟩ : syracuseStep 970739 = 1456109) B1456109
theorem B970775 : Blo 428775 970775 := bstep (se 1 (by rfl) ⟨728081, by rfl⟩ : syracuseStep 970775 = 1456163) B1456163
theorem B872473 : Blo 428775 872473 := bstep (se 2 (by rfl) ⟨327177, by rfl⟩ : syracuseStep 872473 = 654355) B654355
theorem B643211 : Blo 428775 643211 := bstep (se 1 (by rfl) ⟨482408, by rfl⟩ : syracuseStep 643211 = 964817) B964817
theorem B544907 : Blo 428775 544907 := bstep (se 1 (by rfl) ⟨408680, by rfl⟩ : syracuseStep 544907 = 817361) B817361
theorem B643223 : Blo 428775 643223 := bstep (se 1 (by rfl) ⟨482417, by rfl⟩ : syracuseStep 643223 = 964835) B964835
theorem B970955 : Blo 428775 970955 := bstep (se 1 (by rfl) ⟨728216, by rfl⟩ : syracuseStep 970955 = 1456433) B1456433
theorem B643289 : Blo 428775 643289 := bstep (se 2 (by rfl) ⟨241233, by rfl⟩ : syracuseStep 643289 = 482467) B482467
theorem B971009 : Blo 428775 971009 := bstep (se 2 (by rfl) ⟨364128, by rfl⟩ : syracuseStep 971009 = 728257) B728257
theorem B610583 : Blo 428775 610583 := bstep (se 1 (by rfl) ⟨457937, by rfl⟩ : syracuseStep 610583 = 915875) B915875
theorem B6607169 : Blo 428775 6607169 := bstep (se 2 (by rfl) ⟨2477688, by rfl⟩ : syracuseStep 6607169 = 4955377) B4955377
theorem B643403 : Blo 428775 643403 := bstep (se 1 (by rfl) ⟨482552, by rfl⟩ : syracuseStep 643403 = 965105) B965105
theorem B643415 : Blo 428775 643415 := bstep (se 1 (by rfl) ⟨482561, by rfl⟩ : syracuseStep 643415 = 965123) B965123
theorem B774515 : Blo 428775 774515 := bstep (se 1 (by rfl) ⟨580886, by rfl⟩ : syracuseStep 774515 = 1161773) B1161773
theorem B643481 : Blo 428775 643481 := bstep (se 2 (by rfl) ⟨241305, by rfl⟩ : syracuseStep 643481 = 482611) B482611
theorem B3264947 : Blo 428775 3264947 := bstep (se 1 (by rfl) ⟨2448710, by rfl⟩ : syracuseStep 3264947 = 4897421) B4897421
theorem B610777 : Blo 428775 610777 := bstep (se 2 (by rfl) ⟨229041, by rfl⟩ : syracuseStep 610777 = 458083) B458083
theorem B971225 : Blo 428775 971225 := bstep (se 2 (by rfl) ⟨364209, by rfl⟩ : syracuseStep 971225 = 728419) B728419
theorem B643595 : Blo 428775 643595 := bstep (se 1 (by rfl) ⟨482696, by rfl⟩ : syracuseStep 643595 = 965393) B965393
theorem B643607 : Blo 428775 643607 := bstep (se 1 (by rfl) ⟨482705, by rfl⟩ : syracuseStep 643607 = 965411) B965411
theorem B971315 : Blo 428775 971315 := bstep (se 1 (by rfl) ⟨728486, by rfl⟩ : syracuseStep 971315 = 1456973) B1456973
theorem B971351 : Blo 428775 971351 := bstep (se 1 (by rfl) ⟨728513, by rfl⟩ : syracuseStep 971351 = 1457027) B1457027
theorem B643673 : Blo 428775 643673 := bstep (se 2 (by rfl) ⟨241377, by rfl⟩ : syracuseStep 643673 = 482755) B482755
theorem B3691109 : Blo 428775 3691109 := bstep (se 4 (by rfl) ⟨346041, by rfl⟩ : syracuseStep 3691109 = 692083) B692083
theorem B643787 : Blo 428775 643787 := bstep (se 1 (by rfl) ⟨482840, by rfl⟩ : syracuseStep 643787 = 965681) B965681
theorem B643799 : Blo 428775 643799 := bstep (se 1 (by rfl) ⟨482849, by rfl⟩ : syracuseStep 643799 = 965699) B965699
theorem B971531 : Blo 428775 971531 := bstep (se 1 (by rfl) ⟨728648, by rfl⟩ : syracuseStep 971531 = 1457297) B1457297
theorem B643865 : Blo 428775 643865 := bstep (se 2 (by rfl) ⟨241449, by rfl⟩ : syracuseStep 643865 = 482899) B482899
theorem B971585 : Blo 428775 971585 := bstep (se 2 (by rfl) ⟨364344, by rfl⟩ : syracuseStep 971585 = 728689) B728689
theorem B545611 : Blo 428775 545611 := bstep (se 1 (by rfl) ⟨409208, by rfl⟩ : syracuseStep 545611 = 818417) B818417
theorem B643979 : Blo 428775 643979 := bstep (se 1 (by rfl) ⟨482984, by rfl⟩ : syracuseStep 643979 = 965969) B965969
theorem B643991 : Blo 428775 643991 := bstep (se 1 (by rfl) ⟨482993, by rfl⟩ : syracuseStep 643991 = 965987) B965987
theorem B644057 : Blo 428775 644057 := bstep (se 2 (by rfl) ⟨241521, by rfl⟩ : syracuseStep 644057 = 483043) B483043
theorem B971801 : Blo 428775 971801 := bstep (se 2 (by rfl) ⟨364425, by rfl⟩ : syracuseStep 971801 = 728851) B728851
theorem B644171 : Blo 428775 644171 := bstep (se 1 (by rfl) ⟨483128, by rfl⟩ : syracuseStep 644171 = 966257) B966257
theorem B644183 : Blo 428775 644183 := bstep (se 1 (by rfl) ⟨483137, by rfl⟩ : syracuseStep 644183 = 966275) B966275
theorem B545879 : Blo 428775 545879 := bstep (se 1 (by rfl) ⟨409409, by rfl⟩ : syracuseStep 545879 = 818819) B818819
theorem B971891 : Blo 428775 971891 := bstep (se 1 (by rfl) ⟨728918, by rfl⟩ : syracuseStep 971891 = 1457837) B1457837
theorem B971927 : Blo 428775 971927 := bstep (se 1 (by rfl) ⟨728945, by rfl⟩ : syracuseStep 971927 = 1457891) B1457891
theorem B644249 : Blo 428775 644249 := bstep (se 2 (by rfl) ⟨241593, by rfl⟩ : syracuseStep 644249 = 483187) B483187
theorem B644363 : Blo 428775 644363 := bstep (se 1 (by rfl) ⟨483272, by rfl⟩ : syracuseStep 644363 = 966545) B966545
theorem B644375 : Blo 428775 644375 := bstep (se 1 (by rfl) ⟨483281, by rfl⟩ : syracuseStep 644375 = 966563) B966563
theorem B972107 : Blo 428775 972107 := bstep (se 1 (by rfl) ⟨729080, by rfl⟩ : syracuseStep 972107 = 1458161) B1458161
theorem B644441 : Blo 428775 644441 := bstep (se 2 (by rfl) ⟨241665, by rfl⟩ : syracuseStep 644441 = 483331) B483331
theorem B2446685 : Blo 428775 2446685 := bstep (se 3 (by rfl) ⟨458753, by rfl⟩ : syracuseStep 2446685 = 917507) B917507
theorem B972161 : Blo 428775 972161 := bstep (se 2 (by rfl) ⟨364560, by rfl⟩ : syracuseStep 972161 = 729121) B729121
theorem B644555 : Blo 428775 644555 := bstep (se 1 (by rfl) ⟨483416, by rfl⟩ : syracuseStep 644555 = 966833) B966833
theorem B644567 : Blo 428775 644567 := bstep (se 1 (by rfl) ⟨483425, by rfl⟩ : syracuseStep 644567 = 966851) B966851
theorem B644633 : Blo 428775 644633 := bstep (se 2 (by rfl) ⟨241737, by rfl⟩ : syracuseStep 644633 = 483475) B483475
theorem B972377 : Blo 428775 972377 := bstep (se 2 (by rfl) ⟨364641, by rfl⟩ : syracuseStep 972377 = 729283) B729283
theorem B644747 : Blo 428775 644747 := bstep (se 1 (by rfl) ⟨483560, by rfl⟩ : syracuseStep 644747 = 967121) B967121
theorem B644759 : Blo 428775 644759 := bstep (se 1 (by rfl) ⟨483569, by rfl⟩ : syracuseStep 644759 = 967139) B967139
theorem B972467 : Blo 428775 972467 := bstep (se 1 (by rfl) ⟨729350, by rfl⟩ : syracuseStep 972467 = 1458701) B1458701
theorem B972503 : Blo 428775 972503 := bstep (se 1 (by rfl) ⟨729377, by rfl⟩ : syracuseStep 972503 = 1458755) B1458755
theorem B644825 : Blo 428775 644825 := bstep (se 2 (by rfl) ⟨241809, by rfl⟩ : syracuseStep 644825 = 483619) B483619
theorem B546583 : Blo 428775 546583 := bstep (se 1 (by rfl) ⟨409937, by rfl⟩ : syracuseStep 546583 = 819875) B819875
theorem B1103681 : Blo 428775 1103681 := bstep (se 2 (by rfl) ⟨413880, by rfl⟩ : syracuseStep 1103681 = 827761) B827761
theorem B644939 : Blo 428775 644939 := bstep (se 1 (by rfl) ⟨483704, by rfl⟩ : syracuseStep 644939 = 967409) B967409
theorem B644951 : Blo 428775 644951 := bstep (se 1 (by rfl) ⟨483713, by rfl⟩ : syracuseStep 644951 = 967427) B967427
theorem B3266405 : Blo 428775 3266405 := bstep (se 4 (by rfl) ⟨306225, by rfl⟩ : syracuseStep 3266405 = 612451) B612451
theorem B612235 : Blo 428775 612235 := bstep (se 1 (by rfl) ⟨459176, by rfl⟩ : syracuseStep 612235 = 918353) B918353
theorem B972683 : Blo 428775 972683 := bstep (se 1 (by rfl) ⟨729512, by rfl⟩ : syracuseStep 972683 = 1459025) B1459025
theorem B645017 : Blo 428775 645017 := bstep (se 2 (by rfl) ⟨241881, by rfl⟩ : syracuseStep 645017 = 483763) B483763
theorem B972737 : Blo 428775 972737 := bstep (se 2 (by rfl) ⟨364776, by rfl⟩ : syracuseStep 972737 = 729553) B729553
theorem B645131 : Blo 428775 645131 := bstep (se 1 (by rfl) ⟨483848, by rfl⟩ : syracuseStep 645131 = 967697) B967697
theorem B645143 : Blo 428775 645143 := bstep (se 1 (by rfl) ⟨483857, by rfl⟩ : syracuseStep 645143 = 967715) B967715
theorem B2447435 : Blo 428775 2447435 := bstep (se 1 (by rfl) ⟨1835576, by rfl⟩ : syracuseStep 2447435 = 3671153) B3671153
theorem B5036107 : Blo 428775 5036107 := bstep (se 1 (by rfl) ⟨3777080, by rfl⟩ : syracuseStep 5036107 = 7554161) B7554161
theorem B645209 : Blo 428775 645209 := bstep (se 2 (by rfl) ⟨241953, by rfl⟩ : syracuseStep 645209 = 483907) B483907
theorem B4675715 : Blo 428775 4675715 := bstep (se 1 (by rfl) ⟨3506786, by rfl⟩ : syracuseStep 4675715 = 7013573) B7013573
theorem B972953 : Blo 428775 972953 := bstep (se 2 (by rfl) ⟨364857, by rfl⟩ : syracuseStep 972953 = 729715) B729715
theorem B1038529 : Blo 428775 1038529 := bstep (se 2 (by rfl) ⟨389448, by rfl⟩ : syracuseStep 1038529 = 778897) B778897
theorem B645323 : Blo 428775 645323 := bstep (se 1 (by rfl) ⟨483992, by rfl⟩ : syracuseStep 645323 = 967985) B967985
theorem B3692749 : Blo 428775 3692749 := bstep (se 3 (by rfl) ⟨692390, by rfl⟩ : syracuseStep 3692749 = 1384781) B1384781
theorem B645335 : Blo 428775 645335 := bstep (se 1 (by rfl) ⟨484001, by rfl⟩ : syracuseStep 645335 = 968003) B968003
theorem B973043 : Blo 428775 973043 := bstep (se 1 (by rfl) ⟨729782, by rfl⟩ : syracuseStep 973043 = 1459565) B1459565
theorem B973079 : Blo 428775 973079 := bstep (se 1 (by rfl) ⟨729809, by rfl⟩ : syracuseStep 973079 = 1459619) B1459619
theorem B645401 : Blo 428775 645401 := bstep (se 2 (by rfl) ⟨242025, by rfl⟩ : syracuseStep 645401 = 484051) B484051
theorem B3266891 : Blo 428775 3266891 := bstep (se 1 (by rfl) ⟨2450168, by rfl⟩ : syracuseStep 3266891 = 4900337) B4900337
theorem B645515 : Blo 428775 645515 := bstep (se 1 (by rfl) ⟨484136, by rfl⟩ : syracuseStep 645515 = 968273) B968273
theorem B645527 : Blo 428775 645527 := bstep (se 1 (by rfl) ⟨484145, by rfl⟩ : syracuseStep 645527 = 968291) B968291
theorem B973259 : Blo 428775 973259 := bstep (se 1 (by rfl) ⟨729944, by rfl⟩ : syracuseStep 973259 = 1459889) B1459889
theorem B645593 : Blo 428775 645593 := bstep (se 2 (by rfl) ⟨242097, by rfl⟩ : syracuseStep 645593 = 484195) B484195
theorem B973313 : Blo 428775 973313 := bstep (se 2 (by rfl) ⟨364992, by rfl⟩ : syracuseStep 973313 = 729985) B729985
theorem B1956403 : Blo 428775 1956403 := bstep (se 1 (by rfl) ⟨1467302, by rfl⟩ : syracuseStep 1956403 = 2934605) B2934605
theorem B645707 : Blo 428775 645707 := bstep (se 1 (by rfl) ⟨484280, by rfl⟩ : syracuseStep 645707 = 968561) B968561
theorem B645719 : Blo 428775 645719 := bstep (se 1 (by rfl) ⟨484289, by rfl⟩ : syracuseStep 645719 = 968579) B968579
theorem B645785 : Blo 428775 645785 := bstep (se 2 (by rfl) ⟨242169, by rfl⟩ : syracuseStep 645785 = 484339) B484339
theorem B973529 : Blo 428775 973529 := bstep (se 2 (by rfl) ⟨365073, by rfl⟩ : syracuseStep 973529 = 730147) B730147
theorem B645899 : Blo 428775 645899 := bstep (se 1 (by rfl) ⟨484424, by rfl⟩ : syracuseStep 645899 = 968849) B968849
theorem B645911 : Blo 428775 645911 := bstep (se 1 (by rfl) ⟨484433, by rfl⟩ : syracuseStep 645911 = 968867) B968867
theorem B973619 : Blo 428775 973619 := bstep (se 1 (by rfl) ⟨730214, by rfl⟩ : syracuseStep 973619 = 1460429) B1460429
theorem B973655 : Blo 428775 973655 := bstep (se 1 (by rfl) ⟨730241, by rfl⟩ : syracuseStep 973655 = 1460483) B1460483
theorem B645977 : Blo 428775 645977 := bstep (se 2 (by rfl) ⟨242241, by rfl⟩ : syracuseStep 645977 = 484483) B484483
theorem B646091 : Blo 428775 646091 := bstep (se 1 (by rfl) ⟨484568, by rfl⟩ : syracuseStep 646091 = 969137) B969137
theorem B646103 : Blo 428775 646103 := bstep (se 1 (by rfl) ⟨484577, by rfl⟩ : syracuseStep 646103 = 969155) B969155
theorem B2939921 : Blo 428775 2939921 := bstep (se 2 (by rfl) ⟨1102470, by rfl⟩ : syracuseStep 2939921 = 2204941) B2204941
theorem B646169 : Blo 428775 646169 := bstep (se 2 (by rfl) ⟨242313, by rfl⟩ : syracuseStep 646169 = 484627) B484627
theorem B646283 : Blo 428775 646283 := bstep (se 1 (by rfl) ⟨484712, by rfl⟩ : syracuseStep 646283 = 969425) B969425
theorem B646295 : Blo 428775 646295 := bstep (se 1 (by rfl) ⟨484721, by rfl⟩ : syracuseStep 646295 = 969443) B969443
theorem B646361 : Blo 428775 646361 := bstep (se 2 (by rfl) ⟨242385, by rfl⟩ : syracuseStep 646361 = 484771) B484771
theorem B482539 : Blo 428775 482539 := bstep (se 1 (by rfl) ⟨361904, by rfl⟩ : syracuseStep 482539 = 723809) B723809
theorem B2186513 : Blo 428775 2186513 := bstep (se 2 (by rfl) ⟨819942, by rfl⟩ : syracuseStep 2186513 = 1639885) B1639885
theorem B646475 : Blo 428775 646475 := bstep (se 1 (by rfl) ⟨484856, by rfl⟩ : syracuseStep 646475 = 969713) B969713
theorem B482647 : Blo 428775 482647 := bstep (se 1 (by rfl) ⟨361985, by rfl⟩ : syracuseStep 482647 = 723971) B723971
theorem B646487 : Blo 428775 646487 := bstep (se 1 (by rfl) ⟨484865, by rfl⟩ : syracuseStep 646487 = 969731) B969731
theorem B646553 : Blo 428775 646553 := bstep (se 2 (by rfl) ⟨242457, by rfl⟩ : syracuseStep 646553 = 484915) B484915
theorem B2186675 : Blo 428775 2186675 := bstep (se 1 (by rfl) ⟨1640006, by rfl⟩ : syracuseStep 2186675 = 3280013) B3280013
theorem B3694085 : Blo 428775 3694085 := bstep (se 4 (by rfl) ⟨346320, by rfl⟩ : syracuseStep 3694085 = 692641) B692641
theorem B482827 : Blo 428775 482827 := bstep (se 1 (by rfl) ⟨362120, by rfl⟩ : syracuseStep 482827 = 724241) B724241
theorem B646667 : Blo 428775 646667 := bstep (se 1 (by rfl) ⟨485000, by rfl⟩ : syracuseStep 646667 = 970001) B970001
theorem B646679 : Blo 428775 646679 := bstep (se 1 (by rfl) ⟨485009, by rfl⟩ : syracuseStep 646679 = 970019) B970019
theorem B5693003 : Blo 428775 5693003 := bstep (se 1 (by rfl) ⟨4269752, by rfl⟩ : syracuseStep 5693003 = 8539505) B8539505
theorem B646745 : Blo 428775 646745 := bstep (se 2 (by rfl) ⟨242529, by rfl⟩ : syracuseStep 646745 = 485059) B485059
theorem B482935 : Blo 428775 482935 := bstep (se 1 (by rfl) ⟨362201, by rfl⟩ : syracuseStep 482935 = 724403) B724403
theorem B2449075 : Blo 428775 2449075 := bstep (se 1 (by rfl) ⟨1836806, by rfl⟩ : syracuseStep 2449075 = 3673613) B3673613
theorem B646859 : Blo 428775 646859 := bstep (se 1 (by rfl) ⟨485144, by rfl⟩ : syracuseStep 646859 = 970289) B970289
theorem B646871 : Blo 428775 646871 := bstep (se 1 (by rfl) ⟨485153, by rfl⟩ : syracuseStep 646871 = 970307) B970307
theorem B646937 : Blo 428775 646937 := bstep (se 2 (by rfl) ⟨242601, by rfl⟩ : syracuseStep 646937 = 485203) B485203
theorem B483115 : Blo 428775 483115 := bstep (se 1 (by rfl) ⟨362336, by rfl⟩ : syracuseStep 483115 = 724673) B724673
theorem B647051 : Blo 428775 647051 := bstep (se 1 (by rfl) ⟨485288, by rfl⟩ : syracuseStep 647051 = 970577) B970577
theorem B483223 : Blo 428775 483223 := bstep (se 1 (by rfl) ⟨362417, by rfl⟩ : syracuseStep 483223 = 724835) B724835
theorem B647063 : Blo 428775 647063 := bstep (se 1 (by rfl) ⟨485297, by rfl⟩ : syracuseStep 647063 = 970595) B970595
theorem B647129 : Blo 428775 647129 := bstep (se 2 (by rfl) ⟨242673, by rfl⟩ : syracuseStep 647129 = 485347) B485347
theorem B483403 : Blo 428775 483403 := bstep (se 1 (by rfl) ⟨362552, by rfl⟩ : syracuseStep 483403 = 725105) B725105
theorem B647243 : Blo 428775 647243 := bstep (se 1 (by rfl) ⟨485432, by rfl⟩ : syracuseStep 647243 = 970865) B970865
theorem B647255 : Blo 428775 647255 := bstep (se 1 (by rfl) ⟨485441, by rfl⟩ : syracuseStep 647255 = 970883) B970883
theorem B647321 : Blo 428775 647321 := bstep (se 2 (by rfl) ⟨242745, by rfl⟩ : syracuseStep 647321 = 485491) B485491
theorem B483511 : Blo 428775 483511 := bstep (se 1 (by rfl) ⟨362633, by rfl⟩ : syracuseStep 483511 = 725267) B725267
theorem B647435 : Blo 428775 647435 := bstep (se 1 (by rfl) ⟨485576, by rfl⟩ : syracuseStep 647435 = 971153) B971153
theorem B647447 : Blo 428775 647447 := bstep (se 1 (by rfl) ⟨485585, by rfl⟩ : syracuseStep 647447 = 971171) B971171
theorem B647513 : Blo 428775 647513 := bstep (se 2 (by rfl) ⟨242817, by rfl⟩ : syracuseStep 647513 = 485635) B485635
theorem B483691 : Blo 428775 483691 := bstep (se 1 (by rfl) ⟨362768, by rfl⟩ : syracuseStep 483691 = 725537) B725537
theorem B1630637 : Blo 428775 1630637 := bstep (se 3 (by rfl) ⟨305744, by rfl⟩ : syracuseStep 1630637 = 611489) B611489
theorem B647627 : Blo 428775 647627 := bstep (se 1 (by rfl) ⟨485720, by rfl⟩ : syracuseStep 647627 = 971441) B971441
theorem B483799 : Blo 428775 483799 := bstep (se 1 (by rfl) ⟨362849, by rfl⟩ : syracuseStep 483799 = 725699) B725699
theorem B647639 : Blo 428775 647639 := bstep (se 1 (by rfl) ⟨485729, by rfl⟩ : syracuseStep 647639 = 971459) B971459
theorem B647705 : Blo 428775 647705 := bstep (se 2 (by rfl) ⟨242889, by rfl⟩ : syracuseStep 647705 = 485779) B485779
theorem B483979 : Blo 428775 483979 := bstep (se 1 (by rfl) ⟨362984, by rfl⟩ : syracuseStep 483979 = 725969) B725969
theorem B647819 : Blo 428775 647819 := bstep (se 1 (by rfl) ⟨485864, by rfl⟩ : syracuseStep 647819 = 971729) B971729
theorem B647831 : Blo 428775 647831 := bstep (se 1 (by rfl) ⟨485873, by rfl⟩ : syracuseStep 647831 = 971747) B971747
theorem B647897 : Blo 428775 647897 := bstep (se 2 (by rfl) ⟨242961, by rfl⟩ : syracuseStep 647897 = 485923) B485923
theorem B484087 : Blo 428775 484087 := bstep (se 1 (by rfl) ⟨363065, by rfl⟩ : syracuseStep 484087 = 726131) B726131
theorem B582475 : Blo 428775 582475 := bstep (se 1 (by rfl) ⟨436856, by rfl⟩ : syracuseStep 582475 = 873713) B873713
theorem B648011 : Blo 428775 648011 := bstep (se 1 (by rfl) ⟨486008, by rfl⟩ : syracuseStep 648011 = 972017) B972017
theorem B648023 : Blo 428775 648023 := bstep (se 1 (by rfl) ⟨486017, by rfl⟩ : syracuseStep 648023 = 972035) B972035
theorem B648089 : Blo 428775 648089 := bstep (se 2 (by rfl) ⟨243033, by rfl⟩ : syracuseStep 648089 = 486067) B486067
theorem B484267 : Blo 428775 484267 := bstep (se 1 (by rfl) ⟨363200, by rfl⟩ : syracuseStep 484267 = 726401) B726401
theorem B648203 : Blo 428775 648203 := bstep (se 1 (by rfl) ⟨486152, by rfl⟩ : syracuseStep 648203 = 972305) B972305
theorem B484375 : Blo 428775 484375 := bstep (se 1 (by rfl) ⟨363281, by rfl⟩ : syracuseStep 484375 = 726563) B726563
theorem B648215 : Blo 428775 648215 := bstep (se 1 (by rfl) ⟨486161, by rfl⟩ : syracuseStep 648215 = 972323) B972323
theorem B648281 : Blo 428775 648281 := bstep (se 2 (by rfl) ⟨243105, by rfl⟩ : syracuseStep 648281 = 486211) B486211
theorem B2450533 : Blo 428775 2450533 := bstep (se 4 (by rfl) ⟨229737, by rfl⟩ : syracuseStep 2450533 = 459475) B459475
theorem B1631411 : Blo 428775 1631411 := bstep (se 1 (by rfl) ⟨1223558, by rfl⟩ : syracuseStep 1631411 = 2447117) B2447117
theorem B484555 : Blo 428775 484555 := bstep (se 1 (by rfl) ⟨363416, by rfl⟩ : syracuseStep 484555 = 726833) B726833
theorem B648395 : Blo 428775 648395 := bstep (se 1 (by rfl) ⟨486296, by rfl⟩ : syracuseStep 648395 = 972593) B972593
theorem B648407 : Blo 428775 648407 := bstep (se 1 (by rfl) ⟨486305, by rfl⟩ : syracuseStep 648407 = 972611) B972611
theorem B648473 : Blo 428775 648473 := bstep (se 2 (by rfl) ⟨243177, by rfl⟩ : syracuseStep 648473 = 486355) B486355
theorem B484663 : Blo 428775 484663 := bstep (se 1 (by rfl) ⟨363497, by rfl⟩ : syracuseStep 484663 = 726995) B726995
theorem B2188619 : Blo 428775 2188619 := bstep (se 1 (by rfl) ⟨1641464, by rfl⟩ : syracuseStep 2188619 = 3282929) B3282929
theorem B648587 : Blo 428775 648587 := bstep (se 1 (by rfl) ⟨486440, by rfl⟩ : syracuseStep 648587 = 972881) B972881
theorem B648599 : Blo 428775 648599 := bstep (se 1 (by rfl) ⟨486449, by rfl⟩ : syracuseStep 648599 = 972899) B972899
theorem B648665 : Blo 428775 648665 := bstep (se 2 (by rfl) ⟨243249, by rfl⟩ : syracuseStep 648665 = 486499) B486499
theorem B484843 : Blo 428775 484843 := bstep (se 1 (by rfl) ⟨363632, by rfl⟩ : syracuseStep 484843 = 727265) B727265
theorem B648779 : Blo 428775 648779 := bstep (se 1 (by rfl) ⟨486584, by rfl⟩ : syracuseStep 648779 = 973169) B973169
theorem B484951 : Blo 428775 484951 := bstep (se 1 (by rfl) ⟨363713, by rfl⟩ : syracuseStep 484951 = 727427) B727427
theorem B648791 : Blo 428775 648791 := bstep (se 1 (by rfl) ⟨486593, by rfl⟩ : syracuseStep 648791 = 973187) B973187
theorem B648857 : Blo 428775 648857 := bstep (se 2 (by rfl) ⟨243321, by rfl⟩ : syracuseStep 648857 = 486643) B486643
theorem B485131 : Blo 428775 485131 := bstep (se 1 (by rfl) ⟨363848, by rfl⟩ : syracuseStep 485131 = 727697) B727697
theorem B648971 : Blo 428775 648971 := bstep (se 1 (by rfl) ⟨486728, by rfl⟩ : syracuseStep 648971 = 973457) B973457
theorem B648983 : Blo 428775 648983 := bstep (se 1 (by rfl) ⟨486737, by rfl⟩ : syracuseStep 648983 = 973475) B973475
theorem B1763117 : Blo 428775 1763117 := bstep (se 3 (by rfl) ⟨330584, by rfl⟩ : syracuseStep 1763117 = 661169) B661169
theorem B2615105 : Blo 428775 2615105 := bstep (se 2 (by rfl) ⟨980664, by rfl⟩ : syracuseStep 2615105 = 1961329) B1961329
theorem B649049 : Blo 428775 649049 := bstep (se 2 (by rfl) ⟨243393, by rfl⟩ : syracuseStep 649049 = 486787) B486787
theorem B485239 : Blo 428775 485239 := bstep (se 1 (by rfl) ⟨363929, by rfl⟩ : syracuseStep 485239 = 727859) B727859
theorem B649163 : Blo 428775 649163 := bstep (se 1 (by rfl) ⟨486872, by rfl⟩ : syracuseStep 649163 = 973745) B973745
theorem B485419 : Blo 428775 485419 := bstep (se 1 (by rfl) ⟨364064, by rfl⟩ : syracuseStep 485419 = 728129) B728129
theorem B485527 : Blo 428775 485527 := bstep (se 1 (by rfl) ⟨364145, by rfl⟩ : syracuseStep 485527 = 728291) B728291
theorem B3106993 : Blo 428775 3106993 := bstep (se 2 (by rfl) ⟨1165122, by rfl⟩ : syracuseStep 3106993 = 2330245) B2330245
theorem B485707 : Blo 428775 485707 := bstep (se 1 (by rfl) ⟨364280, by rfl⟩ : syracuseStep 485707 = 728561) B728561
theorem B485815 : Blo 428775 485815 := bstep (se 1 (by rfl) ⟨364361, by rfl⟩ : syracuseStep 485815 = 728723) B728723
theorem B485995 : Blo 428775 485995 := bstep (se 1 (by rfl) ⟨364496, by rfl⟩ : syracuseStep 485995 = 728993) B728993
theorem B1632899 : Blo 428775 1632899 := bstep (se 1 (by rfl) ⟨1224674, by rfl⟩ : syracuseStep 1632899 = 2449349) B2449349
theorem B486103 : Blo 428775 486103 := bstep (se 1 (by rfl) ⟨364577, by rfl⟩ : syracuseStep 486103 = 729155) B729155
theorem B715481 : Blo 428775 715481 := bstep (se 2 (by rfl) ⟨268305, by rfl⟩ : syracuseStep 715481 = 536611) B536611
theorem B59894549 : Blo 428775 59894549 := bstep (se 6 (by rfl) ⟨1403778, by rfl⟩ : syracuseStep 59894549 = 2807557) B2807557
theorem B3107659 : Blo 428775 3107659 := bstep (se 1 (by rfl) ⟨2330744, by rfl⟩ : syracuseStep 3107659 = 4661489) B4661489
theorem B2747267 : Blo 428775 2747267 := bstep (se 1 (by rfl) ⟨2060450, by rfl⟩ : syracuseStep 2747267 = 4120901) B4120901
theorem B486283 : Blo 428775 486283 := bstep (se 1 (by rfl) ⟨364712, by rfl⟩ : syracuseStep 486283 = 729425) B729425
theorem B486391 : Blo 428775 486391 := bstep (se 1 (by rfl) ⟨364793, by rfl⟩ : syracuseStep 486391 = 729587) B729587
theorem B2190401 : Blo 428775 2190401 := bstep (se 2 (by rfl) ⟨821400, by rfl⟩ : syracuseStep 2190401 = 1642801) B1642801
theorem B1633355 : Blo 428775 1633355 := bstep (se 1 (by rfl) ⟨1225016, by rfl⟩ : syracuseStep 1633355 = 2450033) B2450033
theorem B486571 : Blo 428775 486571 := bstep (se 1 (by rfl) ⟨364928, by rfl⟩ : syracuseStep 486571 = 729857) B729857
theorem B1633553 : Blo 428775 1633553 := bstep (se 2 (by rfl) ⟨612582, by rfl⟩ : syracuseStep 1633553 = 1225165) B1225165
theorem B486679 : Blo 428775 486679 := bstep (se 1 (by rfl) ⟨365009, by rfl⟩ : syracuseStep 486679 = 730019) B730019
theorem B814475 : Blo 428775 814475 := bstep (se 1 (by rfl) ⟨610856, by rfl⟩ : syracuseStep 814475 = 1221713) B1221713
theorem B814529 : Blo 428775 814529 := bstep (se 2 (by rfl) ⟨305448, by rfl⟩ : syracuseStep 814529 = 610897) B610897
theorem B486859 : Blo 428775 486859 := bstep (se 1 (by rfl) ⟨365144, by rfl⟩ : syracuseStep 486859 = 730289) B730289
theorem B3272237 : Blo 428775 3272237 := bstep (se 3 (by rfl) ⟨613544, by rfl⟩ : syracuseStep 3272237 = 1227089) B1227089
theorem B1175233 : Blo 428775 1175233 := bstep (se 2 (by rfl) ⟨440712, by rfl⟩ : syracuseStep 1175233 = 881425) B881425
theorem B1797835 : Blo 428775 1797835 := bstep (se 1 (by rfl) ⟨1348376, by rfl⟩ : syracuseStep 1797835 = 2696753) B2696753
theorem B6188845 : Blo 428775 6188845 := bstep (se 3 (by rfl) ⟨1160408, by rfl⟩ : syracuseStep 6188845 = 2320817) B2320817
theorem B978905 : Blo 428775 978905 := bstep (se 2 (by rfl) ⟨367089, by rfl⟩ : syracuseStep 978905 = 734179) B734179
theorem B1634327 : Blo 428775 1634327 := bstep (se 1 (by rfl) ⟨1225745, by rfl⟩ : syracuseStep 1634327 = 2451491) B2451491
theorem B1634525 : Blo 428775 1634525 := bstep (se 3 (by rfl) ⟨306473, by rfl⟩ : syracuseStep 1634525 = 612947) B612947
theorem B815447 : Blo 428775 815447 := bstep (se 1 (by rfl) ⟨611585, by rfl⟩ : syracuseStep 815447 = 1223171) B1223171
theorem B2945497 : Blo 428775 2945497 := bstep (se 2 (by rfl) ⟨1104561, by rfl⟩ : syracuseStep 2945497 = 2209123) B2209123
theorem B1045043 : Blo 428775 1045043 := bstep (se 1 (by rfl) ⟨783782, by rfl⟩ : syracuseStep 1045043 = 1567565) B1567565
theorem B979609 : Blo 428775 979609 := bstep (se 2 (by rfl) ⟨367353, by rfl⟩ : syracuseStep 979609 = 734707) B734707
theorem B815987 : Blo 428775 815987 := bstep (se 1 (by rfl) ⟨611990, by rfl⟩ : syracuseStep 815987 = 1223981) B1223981
theorem B3503027 : Blo 428775 3503027 := bstep (se 1 (by rfl) ⟨2627270, by rfl⟩ : syracuseStep 3503027 = 5254541) B5254541
theorem B619607 : Blo 428775 619607 := bstep (se 1 (by rfl) ⟨464705, by rfl⟩ : syracuseStep 619607 = 929411) B929411
theorem B1471709 : Blo 428775 1471709 := bstep (se 3 (by rfl) ⟨275945, by rfl⟩ : syracuseStep 1471709 = 551891) B551891
theorem B980299 : Blo 428775 980299 := bstep (se 1 (by rfl) ⟨735224, by rfl⟩ : syracuseStep 980299 = 1470449) B1470449
theorem B816473 : Blo 428775 816473 := bstep (se 2 (by rfl) ⟨306177, by rfl⟩ : syracuseStep 816473 = 612355) B612355
theorem B2061719 : Blo 428775 2061719 := bstep (se 1 (by rfl) ⟨1546289, by rfl⟩ : syracuseStep 2061719 = 3092579) B3092579
theorem B6715061 : Blo 428775 6715061 := bstep (se 5 (by rfl) ⟨314768, by rfl⟩ : syracuseStep 6715061 = 629537) B629537
theorem B2094913 : Blo 428775 2094913 := bstep (se 2 (by rfl) ⟨785592, by rfl⟩ : syracuseStep 2094913 = 1571185) B1571185
theorem B3929957 : Blo 428775 3929957 := bstep (se 4 (by rfl) ⟨368433, by rfl⟩ : syracuseStep 3929957 = 736867) B736867
theorem B784243 : Blo 428775 784243 := bstep (se 1 (by rfl) ⟨588182, by rfl⟩ : syracuseStep 784243 = 1176365) B1176365
theorem B555031 : Blo 428775 555031 := bstep (se 1 (by rfl) ⟨416273, by rfl⟩ : syracuseStep 555031 = 832547) B832547
theorem B1636483 : Blo 428775 1636483 := bstep (se 1 (by rfl) ⟨1227362, by rfl⟩ : syracuseStep 1636483 = 2454725) B2454725
theorem B8255789 : Blo 428775 8255789 := bstep (se 3 (by rfl) ⟨1547960, by rfl⟩ : syracuseStep 8255789 = 3095921) B3095921
theorem B915799 : Blo 428775 915799 := bstep (se 1 (by rfl) ⟨686849, by rfl⟩ : syracuseStep 915799 = 1373699) B1373699
theorem B1636787 : Blo 428775 1636787 := bstep (se 1 (by rfl) ⟨1227590, by rfl⟩ : syracuseStep 1636787 = 2455181) B2455181
theorem B817931 : Blo 428775 817931 := bstep (se 1 (by rfl) ⟨613448, by rfl⟩ : syracuseStep 817931 = 1226897) B1226897
theorem B2456365 : Blo 428775 2456365 := bstep (se 3 (by rfl) ⟨460568, by rfl⟩ : syracuseStep 2456365 = 921137) B921137
theorem B3504941 : Blo 428775 3504941 := bstep (se 3 (by rfl) ⟨657176, by rfl⟩ : syracuseStep 3504941 = 1314353) B1314353
theorem B1375069 : Blo 428775 1375069 := bstep (se 3 (by rfl) ⟨257825, by rfl⟩ : syracuseStep 1375069 = 515651) B515651
theorem B818113 : Blo 428775 818113 := bstep (se 2 (by rfl) ⟨306792, by rfl⟩ : syracuseStep 818113 = 613585) B613585
theorem B1637441 : Blo 428775 1637441 := bstep (se 2 (by rfl) ⟨614040, by rfl⟩ : syracuseStep 1637441 = 1228081) B1228081
theorem B1473611 : Blo 428775 1473611 := bstep (se 1 (by rfl) ⟨1105208, by rfl⟩ : syracuseStep 1473611 = 2210417) B2210417
theorem B8879179 : Blo 428775 8879179 := bstep (se 1 (by rfl) ⟨6659384, by rfl⟩ : syracuseStep 8879179 = 13318769) B13318769
theorem B1834073 : Blo 428775 1834073 := bstep (se 2 (by rfl) ⟨687777, by rfl⟩ : syracuseStep 1834073 = 1375555) B1375555
theorem B3112067 : Blo 428775 3112067 := bstep (se 1 (by rfl) ⟨2334050, by rfl⟩ : syracuseStep 3112067 = 4668101) B4668101
theorem B3276125 : Blo 428775 3276125 := bstep (se 3 (by rfl) ⟨614273, by rfl⟩ : syracuseStep 3276125 = 1228547) B1228547
theorem B818561 : Blo 428775 818561 := bstep (se 2 (by rfl) ⟨306960, by rfl⟩ : syracuseStep 818561 = 613921) B613921
theorem B654745 : Blo 428775 654745 := bstep (se 2 (by rfl) ⟨245529, by rfl⟩ : syracuseStep 654745 = 491059) B491059
theorem B1310131 : Blo 428775 1310131 := bstep (se 1 (by rfl) ⟨982598, by rfl⟩ : syracuseStep 1310131 = 1965197) B1965197
theorem B917003 : Blo 428775 917003 := bstep (se 1 (by rfl) ⟨687752, by rfl⟩ : syracuseStep 917003 = 1375505) B1375505
theorem B818903 : Blo 428775 818903 := bstep (se 1 (by rfl) ⟨614177, by rfl⟩ : syracuseStep 818903 = 1228355) B1228355
theorem B1245079 : Blo 428775 1245079 := bstep (se 1 (by rfl) ⟨933809, by rfl⟩ : syracuseStep 1245079 = 1867619) B1867619
theorem B819335 : Blo 428775 819335 := bstep (se 1 (by rfl) ⟨614501, by rfl⟩ : syracuseStep 819335 = 1229003) B1229003
theorem B4653571 : Blo 428775 4653571 := bstep (se 1 (by rfl) ⟨3490178, by rfl⟩ : syracuseStep 4653571 = 6980357) B6980357
theorem B1311275 : Blo 428775 1311275 := bstep (se 1 (by rfl) ⟨983456, by rfl⟩ : syracuseStep 1311275 = 1966913) B1966913
theorem B1311347 : Blo 428775 1311347 := bstep (se 1 (by rfl) ⟨983510, by rfl⟩ : syracuseStep 1311347 = 1967021) B1967021
theorem B2458349 : Blo 428775 2458349 := bstep (se 3 (by rfl) ⟨460940, by rfl⟩ : syracuseStep 2458349 = 921881) B921881
theorem B3277583 : Blo 428775 3277583 := bstep (se 1 (by rfl) ⟨2458187, by rfl⟩ : syracuseStep 3277583 = 4916375) B4916375
theorem B10617749 : Blo 428775 10617749 := bstep (se 6 (by rfl) ⟨248853, by rfl⟩ : syracuseStep 10617749 = 497707) B497707
theorem B623545 : Blo 428775 623545 := bstep (se 2 (by rfl) ⟨233829, by rfl⟩ : syracuseStep 623545 = 467659) B467659
theorem B918985 : Blo 428775 918985 := bstep (se 2 (by rfl) ⟨344619, by rfl⟩ : syracuseStep 918985 = 689239) B689239
theorem B2065931 : Blo 428775 2065931 := bstep (se 1 (by rfl) ⟨1549448, by rfl⟩ : syracuseStep 2065931 = 3098897) B3098897
theorem B4196069 : Blo 428775 4196069 := bstep (se 4 (by rfl) ⟨393381, by rfl⟩ : syracuseStep 4196069 = 786763) B786763
theorem B460603 : Blo 428775 460603 := bstep (se 1 (by rfl) ⟨345452, by rfl⟩ : syracuseStep 460603 = 690905) B690905
theorem B4884299 : Blo 428775 4884299 := bstep (se 1 (by rfl) ⟨3663224, by rfl⟩ : syracuseStep 4884299 = 7326449) B7326449
theorem B8259479 : Blo 428775 8259479 := bstep (se 1 (by rfl) ⟨6194609, by rfl⟩ : syracuseStep 8259479 = 12389219) B12389219
theorem B657353 : Blo 428775 657353 := bstep (se 2 (by rfl) ⟨246507, by rfl⟩ : syracuseStep 657353 = 493015) B493015
theorem B4655393 : Blo 428775 4655393 := bstep (se 2 (by rfl) ⟨1745772, by rfl⟩ : syracuseStep 4655393 = 3491545) B3491545
theorem B1640857 : Blo 428775 1640857 := bstep (se 2 (by rfl) ⟨615321, by rfl⟩ : syracuseStep 1640857 = 1230643) B1230643
theorem B919993 : Blo 428775 919993 := bstep (se 2 (by rfl) ⟨344997, by rfl⟩ : syracuseStep 919993 = 689995) B689995
theorem B4655645 : Blo 428775 4655645 := bstep (se 3 (by rfl) ⟨872933, by rfl⟩ : syracuseStep 4655645 = 1745867) B1745867
theorem B920249 : Blo 428775 920249 := bstep (se 2 (by rfl) ⟨345093, by rfl⟩ : syracuseStep 920249 = 690187) B690187
theorem B1641161 : Blo 428775 1641161 := bstep (se 2 (by rfl) ⟨615435, by rfl⟩ : syracuseStep 1641161 = 1230871) B1230871
theorem B428807 : Blo 428775 428807 := bstep (se 1 (by rfl) ⟨321605, by rfl⟩ : syracuseStep 428807 = 643211) B643211
theorem B428815 : Blo 428775 428815 := bstep (se 1 (by rfl) ⟨321611, by rfl⟩ : syracuseStep 428815 = 643223) B643223
theorem B920335 : Blo 428775 920335 := bstep (se 1 (by rfl) ⟨690251, by rfl⟩ : syracuseStep 920335 = 1380503) B1380503
theorem B723755 : Blo 428775 723755 := bstep (se 1 (by rfl) ⟨542816, by rfl⟩ : syracuseStep 723755 = 1085633) B1085633
theorem B428859 : Blo 428775 428859 := bstep (se 1 (by rfl) ⟨321644, by rfl⟩ : syracuseStep 428859 = 643289) B643289
theorem B428935 : Blo 428775 428935 := bstep (se 1 (by rfl) ⟨321701, by rfl⟩ : syracuseStep 428935 = 643403) B643403
theorem B428943 : Blo 428775 428943 := bstep (se 1 (by rfl) ⟨321707, by rfl⟩ : syracuseStep 428943 = 643415) B643415
theorem B428987 : Blo 428775 428987 := bstep (se 1 (by rfl) ⟨321740, by rfl⟩ : syracuseStep 428987 = 643481) B643481
theorem B429063 : Blo 428775 429063 := bstep (se 1 (by rfl) ⟨321797, by rfl⟩ : syracuseStep 429063 = 643595) B643595
theorem B429071 : Blo 428775 429071 := bstep (se 1 (by rfl) ⟨321803, by rfl⟩ : syracuseStep 429071 = 643607) B643607
theorem B2362391 : Blo 428775 2362391 := bstep (se 1 (by rfl) ⟨1771793, by rfl⟩ : syracuseStep 2362391 = 3543587) B3543587
theorem B429115 : Blo 428775 429115 := bstep (se 1 (by rfl) ⟨321836, by rfl⟩ : syracuseStep 429115 = 643673) B643673
theorem B2460739 : Blo 428775 2460739 := bstep (se 1 (by rfl) ⟨1845554, by rfl⟩ : syracuseStep 2460739 = 3691109) B3691109
theorem B429191 : Blo 428775 429191 := bstep (se 1 (by rfl) ⟨321893, by rfl⟩ : syracuseStep 429191 = 643787) B643787
theorem B429199 : Blo 428775 429199 := bstep (se 1 (by rfl) ⟨321899, by rfl⟩ : syracuseStep 429199 = 643799) B643799
theorem B724153 : Blo 428775 724153 := bstep (se 2 (by rfl) ⟨271557, by rfl⟩ : syracuseStep 724153 = 543115) B543115
theorem B1313977 : Blo 428775 1313977 := bstep (se 2 (by rfl) ⟨492741, by rfl⟩ : syracuseStep 1313977 = 985483) B985483
theorem B429243 : Blo 428775 429243 := bstep (se 1 (by rfl) ⟨321932, by rfl⟩ : syracuseStep 429243 = 643865) B643865
theorem B429319 : Blo 428775 429319 := bstep (se 1 (by rfl) ⟨321989, by rfl⟩ : syracuseStep 429319 = 643979) B643979
theorem B429327 : Blo 428775 429327 := bstep (se 1 (by rfl) ⟨321995, by rfl⟩ : syracuseStep 429327 = 643991) B643991
theorem B429371 : Blo 428775 429371 := bstep (se 1 (by rfl) ⟨322028, by rfl⟩ : syracuseStep 429371 = 644057) B644057
theorem B429447 : Blo 428775 429447 := bstep (se 1 (by rfl) ⟨322085, by rfl⟩ : syracuseStep 429447 = 644171) B644171
theorem B429455 : Blo 428775 429455 := bstep (se 1 (by rfl) ⟨322091, by rfl⟩ : syracuseStep 429455 = 644183) B644183
theorem B1838483 : Blo 428775 1838483 := bstep (se 1 (by rfl) ⟨1378862, by rfl⟩ : syracuseStep 1838483 = 2757725) B2757725
theorem B429499 : Blo 428775 429499 := bstep (se 1 (by rfl) ⟨322124, by rfl⟩ : syracuseStep 429499 = 644249) B644249
theorem B429575 : Blo 428775 429575 := bstep (se 1 (by rfl) ⟨322181, by rfl⟩ : syracuseStep 429575 = 644363) B644363
theorem B429583 : Blo 428775 429583 := bstep (se 1 (by rfl) ⟨322187, by rfl⟩ : syracuseStep 429583 = 644375) B644375
theorem B429627 : Blo 428775 429627 := bstep (se 1 (by rfl) ⟨322220, by rfl⟩ : syracuseStep 429627 = 644441) B644441
theorem B1642103 : Blo 428775 1642103 := bstep (se 1 (by rfl) ⟨1231577, by rfl⟩ : syracuseStep 1642103 = 2463155) B2463155
theorem B429703 : Blo 428775 429703 := bstep (se 1 (by rfl) ⟨322277, by rfl⟩ : syracuseStep 429703 = 644555) B644555
theorem B921223 : Blo 428775 921223 := bstep (se 1 (by rfl) ⟨690917, by rfl⟩ : syracuseStep 921223 = 1381835) B1381835
theorem B429711 : Blo 428775 429711 := bstep (se 1 (by rfl) ⟨322283, by rfl⟩ : syracuseStep 429711 = 644567) B644567
theorem B429755 : Blo 428775 429755 := bstep (se 1 (by rfl) ⟨322316, by rfl⟩ : syracuseStep 429755 = 644633) B644633
theorem B429831 : Blo 428775 429831 := bstep (se 1 (by rfl) ⟨322373, by rfl⟩ : syracuseStep 429831 = 644747) B644747
theorem B429839 : Blo 428775 429839 := bstep (se 1 (by rfl) ⟨322379, by rfl⟩ : syracuseStep 429839 = 644759) B644759
theorem B921377 : Blo 428775 921377 := bstep (se 2 (by rfl) ⟨345516, by rfl⟩ : syracuseStep 921377 = 691033) B691033
theorem B429883 : Blo 428775 429883 := bstep (se 1 (by rfl) ⟨322412, by rfl⟩ : syracuseStep 429883 = 644825) B644825
theorem B724855 : Blo 428775 724855 := bstep (se 1 (by rfl) ⟨543641, by rfl⟩ : syracuseStep 724855 = 1087283) B1087283
theorem B429959 : Blo 428775 429959 := bstep (se 1 (by rfl) ⟨322469, by rfl⟩ : syracuseStep 429959 = 644939) B644939
theorem B429967 : Blo 428775 429967 := bstep (se 1 (by rfl) ⟨322475, by rfl⟩ : syracuseStep 429967 = 644951) B644951
theorem B430011 : Blo 428775 430011 := bstep (se 1 (by rfl) ⟨322508, by rfl⟩ : syracuseStep 430011 = 645017) B645017
theorem B430087 : Blo 428775 430087 := bstep (se 1 (by rfl) ⟨322565, by rfl⟩ : syracuseStep 430087 = 645131) B645131
theorem B430095 : Blo 428775 430095 := bstep (se 1 (by rfl) ⟨322571, by rfl⟩ : syracuseStep 430095 = 645143) B645143
theorem B725051 : Blo 428775 725051 := bstep (se 1 (by rfl) ⟨543788, by rfl⟩ : syracuseStep 725051 = 1087577) B1087577
theorem B430139 : Blo 428775 430139 := bstep (se 1 (by rfl) ⟨322604, by rfl⟩ : syracuseStep 430139 = 645209) B645209
theorem B3117143 : Blo 428775 3117143 := bstep (se 1 (by rfl) ⟨2337857, by rfl⟩ : syracuseStep 3117143 = 4675715) B4675715
theorem B921719 : Blo 428775 921719 := bstep (se 1 (by rfl) ⟨691289, by rfl⟩ : syracuseStep 921719 = 1382579) B1382579
theorem B430215 : Blo 428775 430215 := bstep (se 1 (by rfl) ⟨322661, by rfl⟩ : syracuseStep 430215 = 645323) B645323
theorem B430223 : Blo 428775 430223 := bstep (se 1 (by rfl) ⟨322667, by rfl⟩ : syracuseStep 430223 = 645335) B645335
theorem B430267 : Blo 428775 430267 := bstep (se 1 (by rfl) ⟨322700, by rfl⟩ : syracuseStep 430267 = 645401) B645401
theorem B430343 : Blo 428775 430343 := bstep (se 1 (by rfl) ⟨322757, by rfl⟩ : syracuseStep 430343 = 645515) B645515
theorem B430351 : Blo 428775 430351 := bstep (se 1 (by rfl) ⟨322763, by rfl⟩ : syracuseStep 430351 = 645527) B645527
theorem B921889 : Blo 428775 921889 := bstep (se 2 (by rfl) ⟨345708, by rfl⟩ : syracuseStep 921889 = 691417) B691417
theorem B430395 : Blo 428775 430395 := bstep (se 1 (by rfl) ⟨322796, by rfl⟩ : syracuseStep 430395 = 645593) B645593
theorem B430471 : Blo 428775 430471 := bstep (se 1 (by rfl) ⟨322853, by rfl⟩ : syracuseStep 430471 = 645707) B645707
theorem B430479 : Blo 428775 430479 := bstep (se 1 (by rfl) ⟨322859, by rfl⟩ : syracuseStep 430479 = 645719) B645719
theorem B430523 : Blo 428775 430523 := bstep (se 1 (by rfl) ⟨322892, by rfl⟩ : syracuseStep 430523 = 645785) B645785
theorem B725449 : Blo 428775 725449 := bstep (se 2 (by rfl) ⟨272043, by rfl⟩ : syracuseStep 725449 = 544087) B544087
theorem B430599 : Blo 428775 430599 := bstep (se 1 (by rfl) ⟨322949, by rfl⟩ : syracuseStep 430599 = 645899) B645899
theorem B430607 : Blo 428775 430607 := bstep (se 1 (by rfl) ⟨322955, by rfl⟩ : syracuseStep 430607 = 645911) B645911
theorem B430651 : Blo 428775 430651 := bstep (se 1 (by rfl) ⟨322988, by rfl⟩ : syracuseStep 430651 = 645977) B645977
theorem B1643075 : Blo 428775 1643075 := bstep (se 1 (by rfl) ⟨1232306, by rfl⟩ : syracuseStep 1643075 = 2464613) B2464613
theorem B2757239 : Blo 428775 2757239 := bstep (se 1 (by rfl) ⟨2067929, by rfl⟩ : syracuseStep 2757239 = 4135859) B4135859
theorem B430727 : Blo 428775 430727 := bstep (se 1 (by rfl) ⟨323045, by rfl⟩ : syracuseStep 430727 = 646091) B646091
theorem B430735 : Blo 428775 430735 := bstep (se 1 (by rfl) ⟨323051, by rfl⟩ : syracuseStep 430735 = 646103) B646103
theorem B430779 : Blo 428775 430779 := bstep (se 1 (by rfl) ⟨323084, by rfl⟩ : syracuseStep 430779 = 646169) B646169
theorem B430855 : Blo 428775 430855 := bstep (se 1 (by rfl) ⟨323141, by rfl⟩ : syracuseStep 430855 = 646283) B646283
theorem B430863 : Blo 428775 430863 := bstep (se 1 (by rfl) ⟨323147, by rfl⟩ : syracuseStep 430863 = 646295) B646295
theorem B430907 : Blo 428775 430907 := bstep (se 1 (by rfl) ⟨323180, by rfl⟩ : syracuseStep 430907 = 646361) B646361
theorem B430983 : Blo 428775 430983 := bstep (se 1 (by rfl) ⟨323237, by rfl⟩ : syracuseStep 430983 = 646475) B646475
theorem B430991 : Blo 428775 430991 := bstep (se 1 (by rfl) ⟨323243, by rfl⟩ : syracuseStep 430991 = 646487) B646487
theorem B2397113 : Blo 428775 2397113 := bstep (se 2 (by rfl) ⟨898917, by rfl⟩ : syracuseStep 2397113 = 1797835) B1797835
theorem B431035 : Blo 428775 431035 := bstep (se 1 (by rfl) ⟨323276, by rfl⟩ : syracuseStep 431035 = 646553) B646553
theorem B2462723 : Blo 428775 2462723 := bstep (se 1 (by rfl) ⟨1847042, by rfl⟩ : syracuseStep 2462723 = 3694085) B3694085
theorem B431111 : Blo 428775 431111 := bstep (se 1 (by rfl) ⟨323333, by rfl⟩ : syracuseStep 431111 = 646667) B646667
theorem B1381387 : Blo 428775 1381387 := bstep (se 1 (by rfl) ⟨1036040, by rfl⟩ : syracuseStep 1381387 = 2072081) B2072081
theorem B431119 : Blo 428775 431119 := bstep (se 1 (by rfl) ⟨323339, by rfl⟩ : syracuseStep 431119 = 646679) B646679
theorem B1840157 : Blo 428775 1840157 := bstep (se 3 (by rfl) ⟨345029, by rfl⟩ : syracuseStep 1840157 = 690059) B690059
theorem B431163 : Blo 428775 431163 := bstep (se 1 (by rfl) ⟨323372, by rfl⟩ : syracuseStep 431163 = 646745) B646745
theorem B726151 : Blo 428775 726151 := bstep (se 1 (by rfl) ⟨544613, by rfl⟩ : syracuseStep 726151 = 1089227) B1089227
theorem B431239 : Blo 428775 431239 := bstep (se 1 (by rfl) ⟨323429, by rfl⟩ : syracuseStep 431239 = 646859) B646859
theorem B431247 : Blo 428775 431247 := bstep (se 1 (by rfl) ⟨323435, by rfl⟩ : syracuseStep 431247 = 646871) B646871
theorem B431291 : Blo 428775 431291 := bstep (se 1 (by rfl) ⟨323468, by rfl⟩ : syracuseStep 431291 = 646937) B646937
theorem B4658413 : Blo 428775 4658413 := bstep (se 3 (by rfl) ⟨873452, by rfl⟩ : syracuseStep 4658413 = 1746905) B1746905
theorem B431367 : Blo 428775 431367 := bstep (se 1 (by rfl) ⟨323525, by rfl⟩ : syracuseStep 431367 = 647051) B647051
theorem B431375 : Blo 428775 431375 := bstep (se 1 (by rfl) ⟨323531, by rfl⟩ : syracuseStep 431375 = 647063) B647063
theorem B1316125 : Blo 428775 1316125 := bstep (se 3 (by rfl) ⟨246773, by rfl⟩ : syracuseStep 1316125 = 493547) B493547
theorem B431419 : Blo 428775 431419 := bstep (se 1 (by rfl) ⟨323564, by rfl⟩ : syracuseStep 431419 = 647129) B647129
theorem B3675527 : Blo 428775 3675527 := bstep (se 1 (by rfl) ⟨2756645, by rfl⟩ : syracuseStep 3675527 = 5513291) B5513291
theorem B431495 : Blo 428775 431495 := bstep (se 1 (by rfl) ⟨323621, by rfl⟩ : syracuseStep 431495 = 647243) B647243
theorem B431503 : Blo 428775 431503 := bstep (se 1 (by rfl) ⟨323627, by rfl⟩ : syracuseStep 431503 = 647255) B647255
theorem B2069945 : Blo 428775 2069945 := bstep (se 2 (by rfl) ⟨776229, by rfl⟩ : syracuseStep 2069945 = 1552459) B1552459
theorem B431547 : Blo 428775 431547 := bstep (se 1 (by rfl) ⟨323660, by rfl⟩ : syracuseStep 431547 = 647321) B647321
theorem B431623 : Blo 428775 431623 := bstep (se 1 (by rfl) ⟨323717, by rfl⟩ : syracuseStep 431623 = 647435) B647435
theorem B431631 : Blo 428775 431631 := bstep (se 1 (by rfl) ⟨323723, by rfl⟩ : syracuseStep 431631 = 647447) B647447
theorem B431675 : Blo 428775 431675 := bstep (se 1 (by rfl) ⟨323756, by rfl⟩ : syracuseStep 431675 = 647513) B647513
theorem B1087091 : Blo 428775 1087091 := bstep (se 1 (by rfl) ⟨815318, by rfl⟩ : syracuseStep 1087091 = 1630637) B1630637
theorem B431751 : Blo 428775 431751 := bstep (se 1 (by rfl) ⟨323813, by rfl⟩ : syracuseStep 431751 = 647627) B647627
theorem B431759 : Blo 428775 431759 := bstep (se 1 (by rfl) ⟨323819, by rfl⟩ : syracuseStep 431759 = 647639) B647639
theorem B431803 : Blo 428775 431803 := bstep (se 1 (by rfl) ⟨323852, by rfl⟩ : syracuseStep 431803 = 647705) B647705
theorem B431879 : Blo 428775 431879 := bstep (se 1 (by rfl) ⟨323909, by rfl⟩ : syracuseStep 431879 = 647819) B647819
theorem B726799 : Blo 428775 726799 := bstep (se 1 (by rfl) ⟨545099, by rfl⟩ : syracuseStep 726799 = 1090199) B1090199
theorem B431887 : Blo 428775 431887 := bstep (se 1 (by rfl) ⟨323915, by rfl⟩ : syracuseStep 431887 = 647831) B647831
theorem B1447739 : Blo 428775 1447739 := bstep (se 1 (by rfl) ⟨1085804, by rfl⟩ : syracuseStep 1447739 = 2171609) B2171609
theorem B431931 : Blo 428775 431931 := bstep (se 1 (by rfl) ⟨323948, by rfl⟩ : syracuseStep 431931 = 647897) B647897
theorem B4200281 : Blo 428775 4200281 := bstep (se 2 (by rfl) ⟨1575105, by rfl⟩ : syracuseStep 4200281 = 3150211) B3150211
theorem B432007 : Blo 428775 432007 := bstep (se 1 (by rfl) ⟨324005, by rfl⟩ : syracuseStep 432007 = 648011) B648011
theorem B432015 : Blo 428775 432015 := bstep (se 1 (by rfl) ⟨324011, by rfl⟩ : syracuseStep 432015 = 648023) B648023
theorem B432059 : Blo 428775 432059 := bstep (se 1 (by rfl) ⟨324044, by rfl⟩ : syracuseStep 432059 = 648089) B648089
theorem B432135 : Blo 428775 432135 := bstep (se 1 (by rfl) ⟨324101, by rfl⟩ : syracuseStep 432135 = 648203) B648203
theorem B432143 : Blo 428775 432143 := bstep (se 1 (by rfl) ⟨324107, by rfl⟩ : syracuseStep 432143 = 648215) B648215
theorem B432187 : Blo 428775 432187 := bstep (se 1 (by rfl) ⟨324140, by rfl⟩ : syracuseStep 432187 = 648281) B648281
theorem B4954229 : Blo 428775 4954229 := bstep (se 5 (by rfl) ⟨232229, by rfl⟩ : syracuseStep 4954229 = 464459) B464459
theorem B1087607 : Blo 428775 1087607 := bstep (se 1 (by rfl) ⟨815705, by rfl⟩ : syracuseStep 1087607 = 1631411) B1631411
theorem B432263 : Blo 428775 432263 := bstep (se 1 (by rfl) ⟨324197, by rfl⟩ : syracuseStep 432263 = 648395) B648395
theorem B432271 : Blo 428775 432271 := bstep (se 1 (by rfl) ⟨324203, by rfl⟩ : syracuseStep 432271 = 648407) B648407
theorem B923795 : Blo 428775 923795 := bstep (se 1 (by rfl) ⟨692846, by rfl⟩ : syracuseStep 923795 = 1385693) B1385693
theorem B432315 : Blo 428775 432315 := bstep (se 1 (by rfl) ⟨324236, by rfl⟩ : syracuseStep 432315 = 648473) B648473
theorem B432391 : Blo 428775 432391 := bstep (se 1 (by rfl) ⟨324293, by rfl⟩ : syracuseStep 432391 = 648587) B648587
theorem B432399 : Blo 428775 432399 := bstep (se 1 (by rfl) ⟨324299, by rfl⟩ : syracuseStep 432399 = 648599) B648599
theorem B1448225 : Blo 428775 1448225 := bstep (se 2 (by rfl) ⟨543084, by rfl⟩ : syracuseStep 1448225 = 1086169) B1086169
theorem B727339 : Blo 428775 727339 := bstep (se 1 (by rfl) ⟨545504, by rfl⟩ : syracuseStep 727339 = 1091009) B1091009
theorem B432443 : Blo 428775 432443 := bstep (se 1 (by rfl) ⟨324332, by rfl⟩ : syracuseStep 432443 = 648665) B648665
theorem B432519 : Blo 428775 432519 := bstep (se 1 (by rfl) ⟨324389, by rfl⟩ : syracuseStep 432519 = 648779) B648779
theorem B432527 : Blo 428775 432527 := bstep (se 1 (by rfl) ⟨324395, by rfl⟩ : syracuseStep 432527 = 648791) B648791
theorem B727481 : Blo 428775 727481 := bstep (se 2 (by rfl) ⟨272805, by rfl⟩ : syracuseStep 727481 = 545611) B545611
theorem B432571 : Blo 428775 432571 := bstep (se 1 (by rfl) ⟨324428, by rfl⟩ : syracuseStep 432571 = 648857) B648857
theorem B432647 : Blo 428775 432647 := bstep (se 1 (by rfl) ⟨324485, by rfl⟩ : syracuseStep 432647 = 648971) B648971
theorem B432655 : Blo 428775 432655 := bstep (se 1 (by rfl) ⟨324491, by rfl⟩ : syracuseStep 432655 = 648983) B648983
theorem B432699 : Blo 428775 432699 := bstep (se 1 (by rfl) ⟨324524, by rfl⟩ : syracuseStep 432699 = 649049) B649049
theorem B432775 : Blo 428775 432775 := bstep (se 1 (by rfl) ⟨324581, by rfl⟩ : syracuseStep 432775 = 649163) B649163
theorem B1448819 : Blo 428775 1448819 := bstep (se 1 (by rfl) ⟨1086614, by rfl⟩ : syracuseStep 1448819 = 2173229) B2173229
theorem B2202553 : Blo 428775 2202553 := bstep (se 2 (by rfl) ⟨825957, by rfl⟩ : syracuseStep 2202553 = 1651915) B1651915
theorem B1088599 : Blo 428775 1088599 := bstep (se 1 (by rfl) ⟨816449, by rfl⟩ : syracuseStep 1088599 = 1632899) B1632899
theorem B728183 : Blo 428775 728183 := bstep (se 1 (by rfl) ⟨546137, by rfl⟩ : syracuseStep 728183 = 1092275) B1092275
theorem B1088903 : Blo 428775 1088903 := bstep (se 1 (by rfl) ⟨816677, by rfl⟩ : syracuseStep 1088903 = 1633355) B1633355
theorem B1089035 : Blo 428775 1089035 := bstep (se 1 (by rfl) ⟨816776, by rfl⟩ : syracuseStep 1089035 = 1633553) B1633553
theorem B728635 : Blo 428775 728635 := bstep (se 1 (by rfl) ⟨546476, by rfl⟩ : syracuseStep 728635 = 1092953) B1092953
theorem B728777 : Blo 428775 728777 := bstep (se 2 (by rfl) ⟨273291, by rfl⟩ : syracuseStep 728777 = 546583) B546583
theorem B2793217 : Blo 428775 2793217 := bstep (se 2 (by rfl) ⟨1047456, by rfl⟩ : syracuseStep 2793217 = 2094913) B2094913
theorem B1089551 : Blo 428775 1089551 := bstep (se 1 (by rfl) ⟨817163, by rfl⟩ : syracuseStep 1089551 = 1634327) B1634327
theorem B1089683 : Blo 428775 1089683 := bstep (se 1 (by rfl) ⟨817262, by rfl⟩ : syracuseStep 1089683 = 1634525) B1634525
theorem B1384705 : Blo 428775 1384705 := bstep (se 2 (by rfl) ⟨519264, by rfl⟩ : syracuseStep 1384705 = 1038529) B1038529
theorem B4923665 : Blo 428775 4923665 := bstep (se 2 (by rfl) ⟨1846374, by rfl⟩ : syracuseStep 4923665 = 3692749) B3692749
theorem B8298845 : Blo 428775 8298845 := bstep (se 3 (by rfl) ⟨1556033, by rfl⟩ : syracuseStep 8298845 = 3112067) B3112067
theorem B696695 : Blo 428775 696695 := bstep (se 1 (by rfl) ⟨522521, by rfl⟩ : syracuseStep 696695 = 1045043) B1045043
theorem B729479 : Blo 428775 729479 := bstep (se 1 (by rfl) ⟨547109, by rfl⟩ : syracuseStep 729479 = 1094219) B1094219
theorem B1221065 : Blo 428775 1221065 := bstep (se 2 (by rfl) ⟨457899, by rfl⟩ : syracuseStep 1221065 = 915799) B915799
theorem B2335351 : Blo 428775 2335351 := bstep (se 1 (by rfl) ⟨1751513, by rfl⟩ : syracuseStep 2335351 = 3503027) B3503027
theorem B1549057 : Blo 428775 1549057 := bstep (se 2 (by rfl) ⟨580896, by rfl⟩ : syracuseStep 1549057 = 1161793) B1161793
theorem B730127 : Blo 428775 730127 := bstep (se 1 (by rfl) ⟨547595, by rfl⟩ : syracuseStep 730127 = 1095191) B1095191
theorem B2171933 : Blo 428775 2171933 := bstep (se 3 (by rfl) ⟨407237, by rfl⟩ : syracuseStep 2171933 = 814475) B814475
theorem B1844461 : Blo 428775 1844461 := bstep (se 3 (by rfl) ⟨345836, by rfl⟩ : syracuseStep 1844461 = 691673) B691673
theorem B1090817 : Blo 428775 1090817 := bstep (se 2 (by rfl) ⟨409056, by rfl⟩ : syracuseStep 1090817 = 818113) B818113
theorem B3286331 : Blo 428775 3286331 := bstep (se 1 (by rfl) ⟨2464748, by rfl⟩ : syracuseStep 3286331 = 4929497) B4929497
theorem B1451411 : Blo 428775 1451411 := bstep (se 1 (by rfl) ⟨1088558, by rfl⟩ : syracuseStep 1451411 = 2177117) B2177117
theorem B1844633 : Blo 428775 1844633 := bstep (se 2 (by rfl) ⟨691737, by rfl⟩ : syracuseStep 1844633 = 1383475) B1383475
theorem B11838905 : Blo 428775 11838905 := bstep (se 2 (by rfl) ⟨4439589, by rfl⟩ : syracuseStep 11838905 = 8879179) B8879179
theorem B2172419 : Blo 428775 2172419 := bstep (se 1 (by rfl) ⟨1629314, by rfl⟩ : syracuseStep 2172419 = 3258629) B3258629
theorem B1091191 : Blo 428775 1091191 := bstep (se 1 (by rfl) ⟨818393, by rfl⟩ : syracuseStep 1091191 = 1636787) B1636787
theorem B2336627 : Blo 428775 2336627 := bstep (se 1 (by rfl) ⟨1752470, by rfl⟩ : syracuseStep 2336627 = 3504941) B3504941
theorem B1746841 : Blo 428775 1746841 := bstep (se 2 (by rfl) ⟨655065, by rfl⟩ : syracuseStep 1746841 = 1310131) B1310131
theorem B4728739 : Blo 428775 4728739 := bstep (se 1 (by rfl) ⟨3546554, by rfl⟩ : syracuseStep 4728739 = 7093109) B7093109
theorem B1091627 : Blo 428775 1091627 := bstep (se 1 (by rfl) ⟨818720, by rfl⟩ : syracuseStep 1091627 = 1637441) B1637441
theorem B1222715 : Blo 428775 1222715 := bstep (se 1 (by rfl) ⟨917036, by rfl⟩ : syracuseStep 1222715 = 1834073) B1834073
theorem B1223353 : Blo 428775 1223353 := bstep (se 2 (by rfl) ⟨458757, by rfl⟩ : syracuseStep 1223353 = 917515) B917515
theorem B1452815 : Blo 428775 1452815 := bstep (se 1 (by rfl) ⟨1089611, by rfl⟩ : syracuseStep 1452815 = 2179223) B2179223
theorem B2960165 : Blo 428775 2960165 := bstep (se 4 (by rfl) ⟨277515, by rfl⟩ : syracuseStep 2960165 = 555031) B555031
theorem B1092467 : Blo 428775 1092467 := bstep (se 1 (by rfl) ⟨819350, by rfl⟩ : syracuseStep 1092467 = 1638701) B1638701
theorem B1092487 : Blo 428775 1092487 := bstep (se 1 (by rfl) ⟨819365, by rfl⟩ : syracuseStep 1092487 = 1638731) B1638731
theorem B1453085 : Blo 428775 1453085 := bstep (se 3 (by rfl) ⟨272453, by rfl⟩ : syracuseStep 1453085 = 544907) B544907
theorem B1223741 : Blo 428775 1223741 := bstep (se 3 (by rfl) ⟨229451, by rfl⟩ : syracuseStep 1223741 = 458903) B458903
theorem B2174039 : Blo 428775 2174039 := bstep (se 1 (by rfl) ⟨1630529, by rfl⟩ : syracuseStep 2174039 = 3261059) B3261059
theorem B4926581 : Blo 428775 4926581 := bstep (se 5 (by rfl) ⟨230933, by rfl⟩ : syracuseStep 4926581 = 461867) B461867
theorem B1092761 : Blo 428775 1092761 := bstep (se 2 (by rfl) ⟨409785, by rfl⟩ : syracuseStep 1092761 = 819571) B819571
theorem B929083 : Blo 428775 929083 := bstep (se 1 (by rfl) ⟨696812, by rfl⟩ : syracuseStep 929083 = 1393625) B1393625
theorem B1092923 : Blo 428775 1092923 := bstep (se 1 (by rfl) ⟨819692, by rfl⟩ : syracuseStep 1092923 = 1639385) B1639385
theorem B1093135 : Blo 428775 1093135 := bstep (se 1 (by rfl) ⟨819851, by rfl⟩ : syracuseStep 1093135 = 1639703) B1639703
theorem B2666027 : Blo 428775 2666027 := bstep (se 1 (by rfl) ⟨1999520, by rfl⟩ : syracuseStep 2666027 = 3999041) B3999041
theorem B2174525 : Blo 428775 2174525 := bstep (se 3 (by rfl) ⟨407723, by rfl⟩ : syracuseStep 2174525 = 815447) B815447
theorem B4959809 : Blo 428775 4959809 := bstep (se 2 (by rfl) ⟨1859928, by rfl⟩ : syracuseStep 4959809 = 3719857) B3719857
theorem B1093409 : Blo 428775 1093409 := bstep (se 2 (by rfl) ⟨410028, by rfl⟩ : syracuseStep 1093409 = 820057) B820057
theorem B1224857 : Blo 428775 1224857 := bstep (se 2 (by rfl) ⟨459321, by rfl⟩ : syracuseStep 1224857 = 918643) B918643
theorem B1454489 : Blo 428775 1454489 := bstep (se 2 (by rfl) ⟨545433, by rfl⟩ : syracuseStep 1454489 = 1090867) B1090867
theorem B1552907 : Blo 428775 1552907 := bstep (se 1 (by rfl) ⟨1164680, by rfl⟩ : syracuseStep 1552907 = 2329361) B2329361
theorem B1094411 : Blo 428775 1094411 := bstep (se 1 (by rfl) ⟨820808, by rfl⟩ : syracuseStep 1094411 = 1641617) B1641617
theorem B2765771 : Blo 428775 2765771 := bstep (se 1 (by rfl) ⟨2074328, by rfl⟩ : syracuseStep 2765771 = 4148657) B4148657
theorem B1455191 : Blo 428775 1455191 := bstep (se 1 (by rfl) ⟨1091393, by rfl⟩ : syracuseStep 1455191 = 2182787) B2182787
theorem B2176307 : Blo 428775 2176307 := bstep (se 1 (by rfl) ⟨1632230, by rfl⟩ : syracuseStep 2176307 = 3264461) B3264461
theorem B1095059 : Blo 428775 1095059 := bstep (se 1 (by rfl) ⟨821294, by rfl⟩ : syracuseStep 1095059 = 1642589) B1642589
theorem B1226269 : Blo 428775 1226269 := bstep (se 3 (by rfl) ⟨229925, by rfl⟩ : syracuseStep 1226269 = 459851) B459851
theorem B4404779 : Blo 428775 4404779 := bstep (se 1 (by rfl) ⟨3303584, by rfl⟩ : syracuseStep 4404779 = 6607169) B6607169
theorem B1652285 : Blo 428775 1652285 := bstep (se 3 (by rfl) ⟨309803, by rfl⟩ : syracuseStep 1652285 = 619607) B619607
theorem B1455677 : Blo 428775 1455677 := bstep (se 3 (by rfl) ⟨272939, by rfl⟩ : syracuseStep 1455677 = 545879) B545879
theorem B4142657 : Blo 428775 4142657 := bstep (se 2 (by rfl) ⟨1553496, by rfl⟩ : syracuseStep 4142657 = 3106993) B3106993
theorem B2176631 : Blo 428775 2176631 := bstep (se 1 (by rfl) ⟨1632473, by rfl⟩ : syracuseStep 2176631 = 3264947) B3264947
theorem B1095353 : Blo 428775 1095353 := bstep (se 2 (by rfl) ⟨410757, by rfl⟩ : syracuseStep 1095353 = 821515) B821515
theorem B1226441 : Blo 428775 1226441 := bstep (se 2 (by rfl) ⟨459915, by rfl⟩ : syracuseStep 1226441 = 919831) B919831
theorem B1226497 : Blo 428775 1226497 := bstep (se 2 (by rfl) ⟨459936, by rfl⟩ : syracuseStep 1226497 = 919873) B919873
theorem B1226839 : Blo 428775 1226839 := bstep (se 1 (by rfl) ⟨920129, by rfl⟩ : syracuseStep 1226839 = 1840259) B1840259
theorem B964907 : Blo 428775 964907 := bstep (se 1 (by rfl) ⟨723680, by rfl⟩ : syracuseStep 964907 = 1447361) B1447361
theorem B1030553 : Blo 428775 1030553 := bstep (se 2 (by rfl) ⟨386457, by rfl⟩ : syracuseStep 1030553 = 772915) B772915
theorem B4143545 : Blo 428775 4143545 := bstep (se 2 (by rfl) ⟨1553829, by rfl⟩ : syracuseStep 4143545 = 3107659) B3107659
theorem B4143581 : Blo 428775 4143581 := bstep (se 3 (by rfl) ⟨776921, by rfl⟩ : syracuseStep 4143581 = 1553843) B1553843
theorem B735787 : Blo 428775 735787 := bstep (se 1 (by rfl) ⟨551840, by rfl⟩ : syracuseStep 735787 = 1103681) B1103681
theorem B2177603 : Blo 428775 2177603 := bstep (se 1 (by rfl) ⟨1633202, by rfl⟩ : syracuseStep 2177603 = 3266405) B3266405
theorem B965267 : Blo 428775 965267 := bstep (se 1 (by rfl) ⟨723950, by rfl⟩ : syracuseStep 965267 = 1447901) B1447901
theorem B965321 : Blo 428775 965321 := bstep (se 2 (by rfl) ⟨361995, by rfl⟩ : syracuseStep 965321 = 723991) B723991
theorem B2177927 : Blo 428775 2177927 := bstep (se 1 (by rfl) ⟨1633445, by rfl⟩ : syracuseStep 2177927 = 3266891) B3266891
theorem B1457081 : Blo 428775 1457081 := bstep (se 2 (by rfl) ⟨546405, by rfl⟩ : syracuseStep 1457081 = 1092811) B1092811
theorem B81476549 : Blo 428775 81476549 := bstep (se 4 (by rfl) ⟨7638426, by rfl⟩ : syracuseStep 81476549 = 15276853) B15276853
theorem B1162615 : Blo 428775 1162615 := bstep (se 1 (by rfl) ⟨871961, by rfl⟩ : syracuseStep 1162615 = 1743923) B1743923
theorem B966023 : Blo 428775 966023 := bstep (se 1 (by rfl) ⟨724517, by rfl⟩ : syracuseStep 966023 = 1449035) B1449035
theorem B1457675 : Blo 428775 1457675 := bstep (se 1 (by rfl) ⟨1093256, by rfl⟩ : syracuseStep 1457675 = 2186513) B2186513
theorem B966203 : Blo 428775 966203 := bstep (se 1 (by rfl) ⟨724652, by rfl⟩ : syracuseStep 966203 = 1449305) B1449305
theorem B1457783 : Blo 428775 1457783 := bstep (se 1 (by rfl) ⟨1093337, by rfl⟩ : syracuseStep 1457783 = 2186675) B2186675
theorem B966329 : Blo 428775 966329 := bstep (se 2 (by rfl) ⟨362373, by rfl⟩ : syracuseStep 966329 = 724747) B724747
theorem B966671 : Blo 428775 966671 := bstep (se 1 (by rfl) ⟨725003, by rfl⟩ : syracuseStep 966671 = 1450007) B1450007
theorem B966689 : Blo 428775 966689 := bstep (se 2 (by rfl) ⟨362508, by rfl⟩ : syracuseStep 966689 = 725017) B725017
theorem B1163297 : Blo 428775 1163297 := bstep (se 2 (by rfl) ⟨436236, by rfl⟩ : syracuseStep 1163297 = 872473) B872473
theorem B1458377 : Blo 428775 1458377 := bstep (se 2 (by rfl) ⟨546891, by rfl⟩ : syracuseStep 1458377 = 1093783) B1093783
theorem B967031 : Blo 428775 967031 := bstep (se 1 (by rfl) ⟨725273, by rfl⟩ : syracuseStep 967031 = 1450547) B1450547
theorem B5227051 : Blo 428775 5227051 := bstep (se 1 (by rfl) ⟨3920288, by rfl⟩ : syracuseStep 5227051 = 7840577) B7840577
theorem B967211 : Blo 428775 967211 := bstep (se 1 (by rfl) ⟨725408, by rfl⟩ : syracuseStep 967211 = 1450817) B1450817
theorem B1229687 : Blo 428775 1229687 := bstep (se 1 (by rfl) ⟨922265, by rfl⟩ : syracuseStep 1229687 = 1844531) B1844531
theorem B1459079 : Blo 428775 1459079 := bstep (se 1 (by rfl) ⟨1094309, by rfl⟩ : syracuseStep 1459079 = 2188619) B2188619
theorem B967571 : Blo 428775 967571 := bstep (se 1 (by rfl) ⟨725678, by rfl⟩ : syracuseStep 967571 = 1451357) B1451357
theorem B967625 : Blo 428775 967625 := bstep (se 2 (by rfl) ⟨362859, by rfl⟩ : syracuseStep 967625 = 725719) B725719
theorem B1459457 : Blo 428775 1459457 := bstep (se 2 (by rfl) ⟨547296, by rfl⟩ : syracuseStep 1459457 = 1094593) B1094593
theorem B1754369 : Blo 428775 1754369 := bstep (se 2 (by rfl) ⟨657888, by rfl⟩ : syracuseStep 1754369 = 1315777) B1315777
theorem B2770361 : Blo 428775 2770361 := bstep (se 2 (by rfl) ⟨1038885, by rfl⟩ : syracuseStep 2770361 = 2077771) B2077771
theorem B968327 : Blo 428775 968327 := bstep (se 1 (by rfl) ⟨726245, by rfl⟩ : syracuseStep 968327 = 1452491) B1452491
theorem B476987 : Blo 428775 476987 := bstep (se 1 (by rfl) ⟨357740, by rfl⟩ : syracuseStep 476987 = 715481) B715481
theorem B968507 : Blo 428775 968507 := bstep (se 1 (by rfl) ⟨726380, by rfl⟩ : syracuseStep 968507 = 1452761) B1452761
theorem B39929699 : Blo 428775 39929699 := bstep (se 1 (by rfl) ⟨29947274, by rfl⟩ : syracuseStep 39929699 = 59894549) B59894549
theorem B968633 : Blo 428775 968633 := bstep (se 2 (by rfl) ⟨363237, by rfl⟩ : syracuseStep 968633 = 726475) B726475
theorem B1460267 : Blo 428775 1460267 := bstep (se 1 (by rfl) ⟨1095200, by rfl⟩ : syracuseStep 1460267 = 2190401) B2190401
theorem B3688649 : Blo 428775 3688649 := bstep (se 2 (by rfl) ⟨1383243, by rfl⟩ : syracuseStep 3688649 = 2766487) B2766487
theorem B968975 : Blo 428775 968975 := bstep (se 1 (by rfl) ⟨726731, by rfl⟩ : syracuseStep 968975 = 1453463) B1453463
theorem B968993 : Blo 428775 968993 := bstep (se 2 (by rfl) ⟨363372, by rfl⟩ : syracuseStep 968993 = 726745) B726745
theorem B543019 : Blo 428775 543019 := bstep (se 1 (by rfl) ⟨407264, by rfl⟩ : syracuseStep 543019 = 814529) B814529
theorem B2181491 : Blo 428775 2181491 := bstep (se 1 (by rfl) ⟨1636118, by rfl⟩ : syracuseStep 2181491 = 3272237) B3272237
theorem B1100375 : Blo 428775 1100375 := bstep (se 1 (by rfl) ⟨825281, by rfl⟩ : syracuseStep 1100375 = 1650563) B1650563
theorem B969335 : Blo 428775 969335 := bstep (se 1 (by rfl) ⟨727001, by rfl⟩ : syracuseStep 969335 = 1454003) B1454003
theorem B969515 : Blo 428775 969515 := bstep (se 1 (by rfl) ⟨727136, by rfl⟩ : syracuseStep 969515 = 1454273) B1454273
theorem B2181977 : Blo 428775 2181977 := bstep (se 2 (by rfl) ⟨818241, by rfl⟩ : syracuseStep 2181977 = 1636483) B1636483
theorem B4901795 : Blo 428775 4901795 := bstep (se 1 (by rfl) ⟨3676346, by rfl⟩ : syracuseStep 4901795 = 7352693) B7352693
theorem B2608075 : Blo 428775 2608075 := bstep (se 1 (by rfl) ⟨1956056, by rfl⟩ : syracuseStep 2608075 = 3912113) B3912113
theorem B969875 : Blo 428775 969875 := bstep (se 1 (by rfl) ⟨727406, by rfl⟩ : syracuseStep 969875 = 1454813) B1454813
theorem B969929 : Blo 428775 969929 := bstep (se 2 (by rfl) ⟨363723, by rfl⟩ : syracuseStep 969929 = 727447) B727447
theorem B543991 : Blo 428775 543991 := bstep (se 1 (by rfl) ⟨407993, by rfl⟩ : syracuseStep 543991 = 815987) B815987
theorem B2608537 : Blo 428775 2608537 := bstep (se 2 (by rfl) ⟨978201, by rfl⟩ : syracuseStep 2608537 = 1956403) B1956403
theorem B1232329 : Blo 428775 1232329 := bstep (se 2 (by rfl) ⟨462123, by rfl⟩ : syracuseStep 1232329 = 924247) B924247
theorem B544315 : Blo 428775 544315 := bstep (se 1 (by rfl) ⟨408236, by rfl⟩ : syracuseStep 544315 = 816473) B816473
theorem B4476707 : Blo 428775 4476707 := bstep (se 1 (by rfl) ⟨3357530, by rfl⟩ : syracuseStep 4476707 = 6715061) B6715061
theorem B970631 : Blo 428775 970631 := bstep (se 1 (by rfl) ⟨727973, by rfl⟩ : syracuseStep 970631 = 1455947) B1455947
theorem B3330071 : Blo 428775 3330071 := bstep (se 1 (by rfl) ⟨2497553, by rfl⟩ : syracuseStep 3330071 = 4995107) B4995107
theorem B970811 : Blo 428775 970811 := bstep (se 1 (by rfl) ⟨728108, by rfl⟩ : syracuseStep 970811 = 1456217) B1456217
theorem B970937 : Blo 428775 970937 := bstep (se 2 (by rfl) ⟨364101, by rfl⟩ : syracuseStep 970937 = 728203) B728203
theorem B643259 : Blo 428775 643259 := bstep (se 1 (by rfl) ⟨482444, by rfl⟩ : syracuseStep 643259 = 964889) B964889
theorem B643319 : Blo 428775 643319 := bstep (se 1 (by rfl) ⟨482489, by rfl⟩ : syracuseStep 643319 = 964979) B964979
theorem B643343 : Blo 428775 643343 := bstep (se 1 (by rfl) ⟨482507, by rfl⟩ : syracuseStep 643343 = 965015) B965015
theorem B2609459 : Blo 428775 2609459 := bstep (se 1 (by rfl) ⟨1957094, by rfl⟩ : syracuseStep 2609459 = 3914189) B3914189
theorem B643385 : Blo 428775 643385 := bstep (se 2 (by rfl) ⟨241269, by rfl⟩ : syracuseStep 643385 = 482539) B482539
theorem B643463 : Blo 428775 643463 := bstep (se 1 (by rfl) ⟨482597, by rfl⟩ : syracuseStep 643463 = 965195) B965195
theorem B643499 : Blo 428775 643499 := bstep (se 1 (by rfl) ⟨482624, by rfl⟩ : syracuseStep 643499 = 965249) B965249
theorem B643529 : Blo 428775 643529 := bstep (se 2 (by rfl) ⟨241323, by rfl⟩ : syracuseStep 643529 = 482647) B482647
theorem B545287 : Blo 428775 545287 := bstep (se 1 (by rfl) ⟨408965, by rfl⟩ : syracuseStep 545287 = 817931) B817931
theorem B971279 : Blo 428775 971279 := bstep (se 1 (by rfl) ⟨728459, by rfl⟩ : syracuseStep 971279 = 1456919) B1456919
theorem B971297 : Blo 428775 971297 := bstep (se 2 (by rfl) ⟨364236, by rfl⟩ : syracuseStep 971297 = 728473) B728473
theorem B872993 : Blo 428775 872993 := bstep (se 2 (by rfl) ⟨327372, by rfl⟩ : syracuseStep 872993 = 654745) B654745
theorem B643643 : Blo 428775 643643 := bstep (se 1 (by rfl) ⟨482732, by rfl⟩ : syracuseStep 643643 = 965465) B965465
theorem B643703 : Blo 428775 643703 := bstep (se 1 (by rfl) ⟨482777, by rfl⟩ : syracuseStep 643703 = 965555) B965555
theorem B643727 : Blo 428775 643727 := bstep (se 1 (by rfl) ⟨482795, by rfl⟩ : syracuseStep 643727 = 965591) B965591
theorem B643769 : Blo 428775 643769 := bstep (se 2 (by rfl) ⟨241413, by rfl⟩ : syracuseStep 643769 = 482827) B482827
theorem B2806501 : Blo 428775 2806501 := bstep (se 4 (by rfl) ⟨263109, by rfl⟩ : syracuseStep 2806501 = 526219) B526219
theorem B643847 : Blo 428775 643847 := bstep (se 1 (by rfl) ⟨482885, by rfl⟩ : syracuseStep 643847 = 965771) B965771
theorem B1332001 : Blo 428775 1332001 := bstep (se 2 (by rfl) ⟨499500, by rfl⟩ : syracuseStep 1332001 = 999001) B999001
theorem B643883 : Blo 428775 643883 := bstep (se 1 (by rfl) ⟨482912, by rfl⟩ : syracuseStep 643883 = 965825) B965825
theorem B643913 : Blo 428775 643913 := bstep (se 2 (by rfl) ⟨241467, by rfl⟩ : syracuseStep 643913 = 482935) B482935
theorem B971639 : Blo 428775 971639 := bstep (se 1 (by rfl) ⟨728729, by rfl⟩ : syracuseStep 971639 = 1457459) B1457459
theorem B2184083 : Blo 428775 2184083 := bstep (se 1 (by rfl) ⟨1638062, by rfl⟩ : syracuseStep 2184083 = 3276125) B3276125
theorem B3265433 : Blo 428775 3265433 := bstep (se 2 (by rfl) ⟨1224537, by rfl⟩ : syracuseStep 3265433 = 2449075) B2449075
theorem B545707 : Blo 428775 545707 := bstep (se 1 (by rfl) ⟨409280, by rfl⟩ : syracuseStep 545707 = 818561) B818561
theorem B644027 : Blo 428775 644027 := bstep (se 1 (by rfl) ⟨483020, by rfl⟩ : syracuseStep 644027 = 966041) B966041
theorem B644087 : Blo 428775 644087 := bstep (se 1 (by rfl) ⟨483065, by rfl⟩ : syracuseStep 644087 = 966131) B966131
theorem B611335 : Blo 428775 611335 := bstep (se 1 (by rfl) ⟨458501, by rfl⟩ : syracuseStep 611335 = 917003) B917003
theorem B644111 : Blo 428775 644111 := bstep (se 1 (by rfl) ⟨483083, by rfl⟩ : syracuseStep 644111 = 966167) B966167
theorem B971819 : Blo 428775 971819 := bstep (se 1 (by rfl) ⟨728864, by rfl⟩ : syracuseStep 971819 = 1457729) B1457729
theorem B644153 : Blo 428775 644153 := bstep (se 2 (by rfl) ⟨241557, by rfl⟩ : syracuseStep 644153 = 483115) B483115
theorem B644231 : Blo 428775 644231 := bstep (se 1 (by rfl) ⟨483173, by rfl⟩ : syracuseStep 644231 = 966347) B966347
theorem B1168519 : Blo 428775 1168519 := bstep (se 1 (by rfl) ⟨876389, by rfl⟩ : syracuseStep 1168519 = 1752779) B1752779
theorem B545935 : Blo 428775 545935 := bstep (se 1 (by rfl) ⟨409451, by rfl⟩ : syracuseStep 545935 = 818903) B818903
theorem B644267 : Blo 428775 644267 := bstep (se 1 (by rfl) ⟨483200, by rfl⟩ : syracuseStep 644267 = 966401) B966401
theorem B644297 : Blo 428775 644297 := bstep (se 2 (by rfl) ⟨241611, by rfl⟩ : syracuseStep 644297 = 483223) B483223
theorem B1660105 : Blo 428775 1660105 := bstep (se 2 (by rfl) ⟨622539, by rfl⟩ : syracuseStep 1660105 = 1245079) B1245079
theorem B2610413 : Blo 428775 2610413 := bstep (se 3 (by rfl) ⟨489452, by rfl⟩ : syracuseStep 2610413 = 978905) B978905
theorem B644411 : Blo 428775 644411 := bstep (se 1 (by rfl) ⟨483308, by rfl⟩ : syracuseStep 644411 = 966617) B966617
theorem B644471 : Blo 428775 644471 := bstep (se 1 (by rfl) ⟨483353, by rfl⟩ : syracuseStep 644471 = 966707) B966707
theorem B644495 : Blo 428775 644495 := bstep (se 1 (by rfl) ⟨483371, by rfl⟩ : syracuseStep 644495 = 966743) B966743
theorem B972179 : Blo 428775 972179 := bstep (se 1 (by rfl) ⟨729134, by rfl⟩ : syracuseStep 972179 = 1458269) B1458269
theorem B1398169 : Blo 428775 1398169 := bstep (se 2 (by rfl) ⟨524313, by rfl⟩ : syracuseStep 1398169 = 1048627) B1048627
theorem B5952953 : Blo 428775 5952953 := bstep (se 2 (by rfl) ⟨2232357, by rfl⟩ : syracuseStep 5952953 = 4464715) B4464715
theorem B644537 : Blo 428775 644537 := bstep (se 2 (by rfl) ⟨241701, by rfl⟩ : syracuseStep 644537 = 483403) B483403
theorem B972233 : Blo 428775 972233 := bstep (se 2 (by rfl) ⟨364587, by rfl⟩ : syracuseStep 972233 = 729175) B729175
theorem B644615 : Blo 428775 644615 := bstep (se 1 (by rfl) ⟨483461, by rfl⟩ : syracuseStep 644615 = 966923) B966923
theorem B2610731 : Blo 428775 2610731 := bstep (se 1 (by rfl) ⟨1958048, by rfl⟩ : syracuseStep 2610731 = 3916097) B3916097
theorem B644651 : Blo 428775 644651 := bstep (se 1 (by rfl) ⟨483488, by rfl⟩ : syracuseStep 644651 = 966977) B966977
theorem B644681 : Blo 428775 644681 := bstep (se 2 (by rfl) ⟨241755, by rfl⟩ : syracuseStep 644681 = 483511) B483511
theorem B1037971 : Blo 428775 1037971 := bstep (se 1 (by rfl) ⟨778478, by rfl⟩ : syracuseStep 1037971 = 1556957) B1556957
theorem B644795 : Blo 428775 644795 := bstep (se 1 (by rfl) ⟨483596, by rfl⟩ : syracuseStep 644795 = 967193) B967193
theorem B612041 : Blo 428775 612041 := bstep (se 2 (by rfl) ⟨229515, by rfl⟩ : syracuseStep 612041 = 459031) B459031
theorem B644855 : Blo 428775 644855 := bstep (se 1 (by rfl) ⟨483641, by rfl⟩ : syracuseStep 644855 = 967283) B967283
theorem B644879 : Blo 428775 644879 := bstep (se 1 (by rfl) ⟨483659, by rfl⟩ : syracuseStep 644879 = 967319) B967319
theorem B644921 : Blo 428775 644921 := bstep (se 2 (by rfl) ⟨241845, by rfl⟩ : syracuseStep 644921 = 483691) B483691
theorem B612155 : Blo 428775 612155 := bstep (se 1 (by rfl) ⟨459116, by rfl⟩ : syracuseStep 612155 = 918233) B918233
theorem B546679 : Blo 428775 546679 := bstep (se 1 (by rfl) ⟨410009, by rfl⟩ : syracuseStep 546679 = 820019) B820019
theorem B1628039 : Blo 428775 1628039 := bstep (se 1 (by rfl) ⟨1221029, by rfl⟩ : syracuseStep 1628039 = 2442059) B2442059
theorem B644999 : Blo 428775 644999 := bstep (se 1 (by rfl) ⟨483749, by rfl⟩ : syracuseStep 644999 = 967499) B967499
theorem B645035 : Blo 428775 645035 := bstep (se 1 (by rfl) ⟨483776, by rfl⟩ : syracuseStep 645035 = 967553) B967553
theorem B645065 : Blo 428775 645065 := bstep (se 2 (by rfl) ⟨241899, by rfl⟩ : syracuseStep 645065 = 483799) B483799
theorem B1038347 : Blo 428775 1038347 := bstep (se 1 (by rfl) ⟨778760, by rfl⟩ : syracuseStep 1038347 = 1557521) B1557521
theorem B645179 : Blo 428775 645179 := bstep (se 1 (by rfl) ⟨483884, by rfl⟩ : syracuseStep 645179 = 967769) B967769
theorem B1038395 : Blo 428775 1038395 := bstep (se 1 (by rfl) ⟨778796, by rfl⟩ : syracuseStep 1038395 = 1557593) B1557593
theorem B1628221 : Blo 428775 1628221 := bstep (se 3 (by rfl) ⟨305291, by rfl⟩ : syracuseStep 1628221 = 610583) B610583
theorem B4642933 : Blo 428775 4642933 := bstep (se 5 (by rfl) ⟨217637, by rfl⟩ : syracuseStep 4642933 = 435275) B435275
theorem B645239 : Blo 428775 645239 := bstep (se 1 (by rfl) ⟨483929, by rfl⟩ : syracuseStep 645239 = 967859) B967859
theorem B972935 : Blo 428775 972935 := bstep (se 1 (by rfl) ⟨729701, by rfl⟩ : syracuseStep 972935 = 1459403) B1459403
theorem B645263 : Blo 428775 645263 := bstep (se 1 (by rfl) ⟨483947, by rfl⟩ : syracuseStep 645263 = 967895) B967895
theorem B645305 : Blo 428775 645305 := bstep (se 2 (by rfl) ⟨241989, by rfl⟩ : syracuseStep 645305 = 483979) B483979
theorem B547003 : Blo 428775 547003 := bstep (se 1 (by rfl) ⟨410252, by rfl⟩ : syracuseStep 547003 = 820505) B820505
theorem B2447617 : Blo 428775 2447617 := bstep (se 2 (by rfl) ⟨917856, by rfl⟩ : syracuseStep 2447617 = 1835713) B1835713
theorem B645383 : Blo 428775 645383 := bstep (se 1 (by rfl) ⟨484037, by rfl⟩ : syracuseStep 645383 = 968075) B968075
theorem B645419 : Blo 428775 645419 := bstep (se 1 (by rfl) ⟨484064, by rfl⟩ : syracuseStep 645419 = 968129) B968129
theorem B973115 : Blo 428775 973115 := bstep (se 1 (by rfl) ⟨729836, by rfl⟩ : syracuseStep 973115 = 1459673) B1459673
theorem B645449 : Blo 428775 645449 := bstep (se 2 (by rfl) ⟨242043, by rfl⟩ : syracuseStep 645449 = 484087) B484087
theorem B612793 : Blo 428775 612793 := bstep (se 2 (by rfl) ⟨229797, by rfl⟩ : syracuseStep 612793 = 459595) B459595
theorem B776633 : Blo 428775 776633 := bstep (se 2 (by rfl) ⟨291237, by rfl⟩ : syracuseStep 776633 = 582475) B582475
theorem B645563 : Blo 428775 645563 := bstep (se 1 (by rfl) ⟨484172, by rfl⟩ : syracuseStep 645563 = 968345) B968345
theorem B973241 : Blo 428775 973241 := bstep (se 2 (by rfl) ⟨364965, by rfl⟩ : syracuseStep 973241 = 729931) B729931
theorem B645623 : Blo 428775 645623 := bstep (se 1 (by rfl) ⟨484217, by rfl⟩ : syracuseStep 645623 = 968435) B968435
theorem B645647 : Blo 428775 645647 := bstep (se 1 (by rfl) ⟨484235, by rfl⟩ : syracuseStep 645647 = 968471) B968471
theorem B645689 : Blo 428775 645689 := bstep (se 2 (by rfl) ⟨242133, by rfl⟩ : syracuseStep 645689 = 484267) B484267
theorem B645767 : Blo 428775 645767 := bstep (se 1 (by rfl) ⟨484325, by rfl⟩ : syracuseStep 645767 = 968651) B968651
theorem B645803 : Blo 428775 645803 := bstep (se 1 (by rfl) ⟨484352, by rfl⟩ : syracuseStep 645803 = 968705) B968705
theorem B547499 : Blo 428775 547499 := bstep (se 1 (by rfl) ⟨410624, by rfl⟩ : syracuseStep 547499 = 821249) B821249
theorem B645833 : Blo 428775 645833 := bstep (se 2 (by rfl) ⟨242187, by rfl⟩ : syracuseStep 645833 = 484375) B484375
theorem B2448143 : Blo 428775 2448143 := bstep (se 1 (by rfl) ⟨1836107, by rfl⟩ : syracuseStep 2448143 = 3672215) B3672215
theorem B5233423 : Blo 428775 5233423 := bstep (se 1 (by rfl) ⟨3925067, by rfl⟩ : syracuseStep 5233423 = 7850135) B7850135
theorem B973583 : Blo 428775 973583 := bstep (se 1 (by rfl) ⟨730187, by rfl⟩ : syracuseStep 973583 = 1460375) B1460375
theorem B973601 : Blo 428775 973601 := bstep (se 2 (by rfl) ⟨365100, by rfl⟩ : syracuseStep 973601 = 730201) B730201
theorem B3267377 : Blo 428775 3267377 := bstep (se 2 (by rfl) ⟨1225266, by rfl⟩ : syracuseStep 3267377 = 2450533) B2450533
theorem B645947 : Blo 428775 645947 := bstep (se 1 (by rfl) ⟨484460, by rfl⟩ : syracuseStep 645947 = 968921) B968921
theorem B5299019 : Blo 428775 5299019 := bstep (se 1 (by rfl) ⟨3974264, by rfl⟩ : syracuseStep 5299019 = 7948529) B7948529
theorem B646007 : Blo 428775 646007 := bstep (se 1 (by rfl) ⟨484505, by rfl⟩ : syracuseStep 646007 = 969011) B969011
theorem B646031 : Blo 428775 646031 := bstep (se 1 (by rfl) ⟨484523, by rfl⟩ : syracuseStep 646031 = 969047) B969047
theorem B646073 : Blo 428775 646073 := bstep (se 2 (by rfl) ⟨242277, by rfl⟩ : syracuseStep 646073 = 484555) B484555
theorem B646151 : Blo 428775 646151 := bstep (se 1 (by rfl) ⟨484613, by rfl⟩ : syracuseStep 646151 = 969227) B969227
theorem B646187 : Blo 428775 646187 := bstep (se 1 (by rfl) ⟨484640, by rfl⟩ : syracuseStep 646187 = 969281) B969281
theorem B646217 : Blo 428775 646217 := bstep (se 2 (by rfl) ⟨242331, by rfl⟩ : syracuseStep 646217 = 484663) B484663
theorem B646331 : Blo 428775 646331 := bstep (se 1 (by rfl) ⟨484748, by rfl⟩ : syracuseStep 646331 = 969497) B969497
theorem B646391 : Blo 428775 646391 := bstep (se 1 (by rfl) ⟨484793, by rfl⟩ : syracuseStep 646391 = 969587) B969587
theorem B482575 : Blo 428775 482575 := bstep (se 1 (by rfl) ⟨361931, by rfl⟩ : syracuseStep 482575 = 723863) B723863
theorem B646415 : Blo 428775 646415 := bstep (se 1 (by rfl) ⟨484811, by rfl⟩ : syracuseStep 646415 = 969623) B969623
theorem B646457 : Blo 428775 646457 := bstep (se 2 (by rfl) ⟨242421, by rfl⟩ : syracuseStep 646457 = 484843) B484843
theorem B3366203 : Blo 428775 3366203 := bstep (se 1 (by rfl) ⟨2524652, by rfl⟩ : syracuseStep 3366203 = 5049305) B5049305
theorem B646535 : Blo 428775 646535 := bstep (se 1 (by rfl) ⟨484901, by rfl⟩ : syracuseStep 646535 = 969803) B969803
theorem B646571 : Blo 428775 646571 := bstep (se 1 (by rfl) ⟨484928, by rfl⟩ : syracuseStep 646571 = 969857) B969857
theorem B6643129 : Blo 428775 6643129 := bstep (se 2 (by rfl) ⟨2491173, by rfl⟩ : syracuseStep 6643129 = 4982347) B4982347
theorem B646601 : Blo 428775 646601 := bstep (se 2 (by rfl) ⟨242475, by rfl⟩ : syracuseStep 646601 = 484951) B484951
theorem B53632469 : Blo 428775 53632469 := bstep (se 7 (by rfl) ⟨628505, by rfl⟩ : syracuseStep 53632469 = 1257011) B1257011
theorem B646715 : Blo 428775 646715 := bstep (se 1 (by rfl) ⟨485036, by rfl⟩ : syracuseStep 646715 = 970073) B970073
theorem B646775 : Blo 428775 646775 := bstep (se 1 (by rfl) ⟨485081, by rfl⟩ : syracuseStep 646775 = 970163) B970163
theorem B646799 : Blo 428775 646799 := bstep (se 1 (by rfl) ⟨485099, by rfl⟩ : syracuseStep 646799 = 970199) B970199
theorem B876179 : Blo 428775 876179 := bstep (se 1 (by rfl) ⟨657134, by rfl⟩ : syracuseStep 876179 = 1314269) B1314269
theorem B646841 : Blo 428775 646841 := bstep (se 2 (by rfl) ⟨242565, by rfl⟩ : syracuseStep 646841 = 485131) B485131
theorem B1629953 : Blo 428775 1629953 := bstep (se 2 (by rfl) ⟨611232, by rfl⟩ : syracuseStep 1629953 = 1222465) B1222465
theorem B483079 : Blo 428775 483079 := bstep (se 1 (by rfl) ⟨362309, by rfl⟩ : syracuseStep 483079 = 724619) B724619
theorem B646919 : Blo 428775 646919 := bstep (se 1 (by rfl) ⟨485189, by rfl⟩ : syracuseStep 646919 = 970379) B970379
theorem B646955 : Blo 428775 646955 := bstep (se 1 (by rfl) ⟨485216, by rfl⟩ : syracuseStep 646955 = 970433) B970433
theorem B646985 : Blo 428775 646985 := bstep (se 2 (by rfl) ⟨242619, by rfl⟩ : syracuseStep 646985 = 485239) B485239
theorem B2187161 : Blo 428775 2187161 := bstep (se 2 (by rfl) ⟨820185, by rfl⟩ : syracuseStep 2187161 = 1640371) B1640371
theorem B483259 : Blo 428775 483259 := bstep (se 1 (by rfl) ⟨362444, by rfl⟩ : syracuseStep 483259 = 724889) B724889
theorem B647099 : Blo 428775 647099 := bstep (se 1 (by rfl) ⟨485324, by rfl⟩ : syracuseStep 647099 = 970649) B970649
theorem B647159 : Blo 428775 647159 := bstep (se 1 (by rfl) ⟨485369, by rfl⟩ : syracuseStep 647159 = 970739) B970739
theorem B647183 : Blo 428775 647183 := bstep (se 1 (by rfl) ⟨485387, by rfl⟩ : syracuseStep 647183 = 970775) B970775
theorem B647225 : Blo 428775 647225 := bstep (se 2 (by rfl) ⟨242709, by rfl⟩ : syracuseStep 647225 = 485419) B485419
theorem B647303 : Blo 428775 647303 := bstep (se 1 (by rfl) ⟨485477, by rfl⟩ : syracuseStep 647303 = 970955) B970955
theorem B647339 : Blo 428775 647339 := bstep (se 1 (by rfl) ⟨485504, by rfl⟩ : syracuseStep 647339 = 971009) B971009
theorem B2449601 : Blo 428775 2449601 := bstep (se 2 (by rfl) ⟨918600, by rfl⟩ : syracuseStep 2449601 = 1837201) B1837201
theorem B647369 : Blo 428775 647369 := bstep (se 2 (by rfl) ⟨242763, by rfl⟩ : syracuseStep 647369 = 485527) B485527
theorem B516343 : Blo 428775 516343 := bstep (se 1 (by rfl) ⟨387257, by rfl⟩ : syracuseStep 516343 = 774515) B774515
theorem B647483 : Blo 428775 647483 := bstep (se 1 (by rfl) ⟨485612, by rfl⟩ : syracuseStep 647483 = 971225) B971225
theorem B647543 : Blo 428775 647543 := bstep (se 1 (by rfl) ⟨485657, by rfl⟩ : syracuseStep 647543 = 971315) B971315
theorem B483727 : Blo 428775 483727 := bstep (se 1 (by rfl) ⟨362795, by rfl⟩ : syracuseStep 483727 = 725591) B725591
theorem B647567 : Blo 428775 647567 := bstep (se 1 (by rfl) ⟨485675, by rfl⟩ : syracuseStep 647567 = 971351) B971351
theorem B647609 : Blo 428775 647609 := bstep (se 2 (by rfl) ⟨242853, by rfl⟩ : syracuseStep 647609 = 485707) B485707
theorem B647687 : Blo 428775 647687 := bstep (se 1 (by rfl) ⟨485765, by rfl⟩ : syracuseStep 647687 = 971531) B971531
theorem B647723 : Blo 428775 647723 := bstep (se 1 (by rfl) ⟨485792, by rfl⟩ : syracuseStep 647723 = 971585) B971585
theorem B647753 : Blo 428775 647753 := bstep (se 2 (by rfl) ⟨242907, by rfl⟩ : syracuseStep 647753 = 485815) B485815
theorem B3924557 : Blo 428775 3924557 := bstep (se 3 (by rfl) ⟨735854, by rfl⟩ : syracuseStep 3924557 = 1471709) B1471709
theorem B647867 : Blo 428775 647867 := bstep (se 1 (by rfl) ⟨485900, by rfl⟩ : syracuseStep 647867 = 971801) B971801
theorem B647927 : Blo 428775 647927 := bstep (se 1 (by rfl) ⟨485945, by rfl⟩ : syracuseStep 647927 = 971891) B971891
theorem B647951 : Blo 428775 647951 := bstep (se 1 (by rfl) ⟨485963, by rfl⟩ : syracuseStep 647951 = 971927) B971927
theorem B647993 : Blo 428775 647993 := bstep (se 2 (by rfl) ⟨242997, by rfl⟩ : syracuseStep 647993 = 485995) B485995
theorem B484231 : Blo 428775 484231 := bstep (se 1 (by rfl) ⟨363173, by rfl⟩ : syracuseStep 484231 = 726347) B726347
theorem B648071 : Blo 428775 648071 := bstep (se 1 (by rfl) ⟨486053, by rfl⟩ : syracuseStep 648071 = 972107) B972107
theorem B1631123 : Blo 428775 1631123 := bstep (se 1 (by rfl) ⟨1223342, by rfl⟩ : syracuseStep 1631123 = 2446685) B2446685
theorem B648107 : Blo 428775 648107 := bstep (se 1 (by rfl) ⟨486080, by rfl⟩ : syracuseStep 648107 = 972161) B972161
theorem B648137 : Blo 428775 648137 := bstep (se 2 (by rfl) ⟨243051, by rfl⟩ : syracuseStep 648137 = 486103) B486103
theorem B484411 : Blo 428775 484411 := bstep (se 1 (by rfl) ⟨363308, by rfl⟩ : syracuseStep 484411 = 726617) B726617
theorem B648251 : Blo 428775 648251 := bstep (se 1 (by rfl) ⟨486188, by rfl⟩ : syracuseStep 648251 = 972377) B972377
theorem B648311 : Blo 428775 648311 := bstep (se 1 (by rfl) ⟨486233, by rfl⟩ : syracuseStep 648311 = 972467) B972467
theorem B648335 : Blo 428775 648335 := bstep (se 1 (by rfl) ⟨486251, by rfl⟩ : syracuseStep 648335 = 972503) B972503
theorem B615595 : Blo 428775 615595 := bstep (se 1 (by rfl) ⟨461696, by rfl⟩ : syracuseStep 615595 = 923393) B923393
theorem B648377 : Blo 428775 648377 := bstep (se 2 (by rfl) ⟨243141, by rfl⟩ : syracuseStep 648377 = 486283) B486283
theorem B648455 : Blo 428775 648455 := bstep (se 1 (by rfl) ⟨486341, by rfl⟩ : syracuseStep 648455 = 972683) B972683
theorem B648491 : Blo 428775 648491 := bstep (se 1 (by rfl) ⟨486368, by rfl⟩ : syracuseStep 648491 = 972737) B972737
theorem B648521 : Blo 428775 648521 := bstep (se 2 (by rfl) ⟨243195, by rfl⟩ : syracuseStep 648521 = 486391) B486391
theorem B1631623 : Blo 428775 1631623 := bstep (se 1 (by rfl) ⟨1223717, by rfl⟩ : syracuseStep 1631623 = 2447435) B2447435
theorem B648635 : Blo 428775 648635 := bstep (se 1 (by rfl) ⟨486476, by rfl⟩ : syracuseStep 648635 = 972953) B972953
theorem B648695 : Blo 428775 648695 := bstep (se 1 (by rfl) ⟨486521, by rfl⟩ : syracuseStep 648695 = 973043) B973043
theorem B484879 : Blo 428775 484879 := bstep (se 1 (by rfl) ⟨363659, by rfl⟩ : syracuseStep 484879 = 727319) B727319
theorem B648719 : Blo 428775 648719 := bstep (se 1 (by rfl) ⟨486539, by rfl⟩ : syracuseStep 648719 = 973079) B973079
theorem B648761 : Blo 428775 648761 := bstep (se 2 (by rfl) ⟨243285, by rfl⟩ : syracuseStep 648761 = 486571) B486571
theorem B1402429 : Blo 428775 1402429 := bstep (se 3 (by rfl) ⟨262955, by rfl⟩ : syracuseStep 1402429 = 525911) B525911
theorem B648839 : Blo 428775 648839 := bstep (se 1 (by rfl) ⟨486629, by rfl⟩ : syracuseStep 648839 = 973259) B973259
theorem B648875 : Blo 428775 648875 := bstep (se 1 (by rfl) ⟨486656, by rfl⟩ : syracuseStep 648875 = 973313) B973313
theorem B648905 : Blo 428775 648905 := bstep (se 2 (by rfl) ⟨243339, by rfl⟩ : syracuseStep 648905 = 486679) B486679
theorem B1795841 : Blo 428775 1795841 := bstep (se 2 (by rfl) ⟨673440, by rfl⟩ : syracuseStep 1795841 = 1346881) B1346881
theorem B583481 : Blo 428775 583481 := bstep (se 2 (by rfl) ⟨218805, by rfl⟩ : syracuseStep 583481 = 437611) B437611
theorem B649019 : Blo 428775 649019 := bstep (se 1 (by rfl) ⟨486764, by rfl⟩ : syracuseStep 649019 = 973529) B973529
theorem B649079 : Blo 428775 649079 := bstep (se 1 (by rfl) ⟨486809, by rfl⟩ : syracuseStep 649079 = 973619) B973619
theorem B649103 : Blo 428775 649103 := bstep (se 1 (by rfl) ⟨486827, by rfl⟩ : syracuseStep 649103 = 973655) B973655
theorem B649145 : Blo 428775 649145 := bstep (se 2 (by rfl) ⟨243429, by rfl⟩ : syracuseStep 649145 = 486859) B486859
theorem B485383 : Blo 428775 485383 := bstep (se 1 (by rfl) ⟨364037, by rfl⟩ : syracuseStep 485383 = 728075) B728075
theorem B1959947 : Blo 428775 1959947 := bstep (se 1 (by rfl) ⟨1469960, by rfl⟩ : syracuseStep 1959947 = 2939921) B2939921
theorem B6973613 : Blo 428775 6973613 := bstep (se 3 (by rfl) ⟨1307552, by rfl⟩ : syracuseStep 6973613 = 2615105) B2615105
theorem B485563 : Blo 428775 485563 := bstep (se 1 (by rfl) ⟨364172, by rfl⟩ : syracuseStep 485563 = 728345) B728345
theorem B1566977 : Blo 428775 1566977 := bstep (se 2 (by rfl) ⟨587616, by rfl⟩ : syracuseStep 1566977 = 1175233) B1175233
theorem B1468687 : Blo 428775 1468687 := bstep (se 1 (by rfl) ⟨1101515, by rfl⟩ : syracuseStep 1468687 = 2203031) B2203031
theorem B3795335 : Blo 428775 3795335 := bstep (se 1 (by rfl) ⟨2846501, by rfl⟩ : syracuseStep 3795335 = 5693003) B5693003
theorem B8251793 : Blo 428775 8251793 := bstep (se 2 (by rfl) ⟨3094422, by rfl⟩ : syracuseStep 8251793 = 6188845) B6188845
theorem B2189753 : Blo 428775 2189753 := bstep (se 2 (by rfl) ⟨821157, by rfl⟩ : syracuseStep 2189753 = 1642315) B1642315
theorem B2451991 : Blo 428775 2451991 := bstep (se 1 (by rfl) ⟨1838993, by rfl⟩ : syracuseStep 2451991 = 3677987) B3677987
theorem B486031 : Blo 428775 486031 := bstep (se 1 (by rfl) ⟨364523, by rfl⟩ : syracuseStep 486031 = 729047) B729047
theorem B2321297 : Blo 428775 2321297 := bstep (se 2 (by rfl) ⟨870486, by rfl⟩ : syracuseStep 2321297 = 1740973) B1740973
theorem B486535 : Blo 428775 486535 := bstep (se 1 (by rfl) ⟨364901, by rfl⟩ : syracuseStep 486535 = 729803) B729803
theorem B814369 : Blo 428775 814369 := bstep (se 2 (by rfl) ⟨305388, by rfl⟩ : syracuseStep 814369 = 610777) B610777
theorem B3927329 : Blo 428775 3927329 := bstep (se 2 (by rfl) ⟨1472748, by rfl⟩ : syracuseStep 3927329 = 2945497) B2945497
theorem B486715 : Blo 428775 486715 := bstep (se 1 (by rfl) ⟨365036, by rfl⟩ : syracuseStep 486715 = 730073) B730073
theorem B1306145 : Blo 428775 1306145 := bstep (se 2 (by rfl) ⟨489804, by rfl⟩ : syracuseStep 1306145 = 979609) B979609
theorem B814711 : Blo 428775 814711 := bstep (se 1 (by rfl) ⟨611033, by rfl⟩ : syracuseStep 814711 = 1222067) B1222067
theorem B1175411 : Blo 428775 1175411 := bstep (se 1 (by rfl) ⟨881558, by rfl⟩ : syracuseStep 1175411 = 1763117) B1763117
theorem B4157729 : Blo 428775 4157729 := bstep (se 2 (by rfl) ⟨1559148, by rfl⟩ : syracuseStep 4157729 = 3118297) B3118297
theorem B1307065 : Blo 428775 1307065 := bstep (se 2 (by rfl) ⟨490149, by rfl⟩ : syracuseStep 1307065 = 980299) B980299
theorem B1831511 : Blo 428775 1831511 := bstep (se 1 (by rfl) ⟨1373633, by rfl⟩ : syracuseStep 1831511 = 2747267) B2747267
theorem B2454407 : Blo 428775 2454407 := bstep (se 1 (by rfl) ⟨1840805, by rfl⟩ : syracuseStep 2454407 = 3681611) B3681611
theorem B1045657 : Blo 428775 1045657 := bstep (se 2 (by rfl) ⟨392121, by rfl⟩ : syracuseStep 1045657 = 784243) B784243
theorem B816313 : Blo 428775 816313 := bstep (se 2 (by rfl) ⟨306117, by rfl⟩ : syracuseStep 816313 = 612235) B612235
theorem B6714809 : Blo 428775 6714809 := bstep (se 2 (by rfl) ⟨2518053, by rfl⟩ : syracuseStep 6714809 = 5036107) B5036107
theorem B7370189 : Blo 428775 7370189 := bstep (se 3 (by rfl) ⟨1381910, by rfl⟩ : syracuseStep 7370189 = 2763821) B2763821
theorem B816655 : Blo 428775 816655 := bstep (se 1 (by rfl) ⟨612491, by rfl⟩ : syracuseStep 816655 = 1224983) B1224983
theorem B3929629 : Blo 428775 3929629 := bstep (se 3 (by rfl) ⟨736805, by rfl⟩ : syracuseStep 3929629 = 1473611) B1473611
theorem B554683 : Blo 428775 554683 := bstep (se 1 (by rfl) ⟨416012, by rfl⟩ : syracuseStep 554683 = 832025) B832025
theorem B5535539 : Blo 428775 5535539 := bstep (se 1 (by rfl) ⟨4151654, by rfl⟩ : syracuseStep 5535539 = 8303309) B8303309
theorem B1374479 : Blo 428775 1374479 := bstep (se 1 (by rfl) ⟨1030859, by rfl⟩ : syracuseStep 1374479 = 2061719) B2061719
theorem B817543 : Blo 428775 817543 := bstep (se 1 (by rfl) ⟨613157, by rfl⟩ : syracuseStep 817543 = 1226315) B1226315
theorem B3275153 : Blo 428775 3275153 := bstep (se 2 (by rfl) ⟨1228182, by rfl⟩ : syracuseStep 3275153 = 2456365) B2456365
theorem B1833425 : Blo 428775 1833425 := bstep (se 2 (by rfl) ⟨687534, by rfl⟩ : syracuseStep 1833425 = 1375069) B1375069
theorem B2619971 : Blo 428775 2619971 := bstep (se 1 (by rfl) ⟨1964978, by rfl⟩ : syracuseStep 2619971 = 3929957) B3929957
theorem B2456183 : Blo 428775 2456183 := bstep (se 1 (by rfl) ⟨1842137, by rfl⟩ : syracuseStep 2456183 = 3684275) B3684275
theorem B5503859 : Blo 428775 5503859 := bstep (se 1 (by rfl) ⟨4127894, by rfl⟩ : syracuseStep 5503859 = 8255789) B8255789
theorem B1637273 : Blo 428775 1637273 := bstep (se 2 (by rfl) ⟨613977, by rfl⟩ : syracuseStep 1637273 = 1227955) B1227955
theorem B2751725 : Blo 428775 2751725 := bstep (se 3 (by rfl) ⟨515948, by rfl⟩ : syracuseStep 2751725 = 1031897) B1031897
theorem B2456891 : Blo 428775 2456891 := bstep (se 1 (by rfl) ⟨1842668, by rfl⟩ : syracuseStep 2456891 = 3685337) B3685337
theorem B1244873 : Blo 428775 1244873 := bstep (se 2 (by rfl) ⟨466827, by rfl⟩ : syracuseStep 1244873 = 933655) B933655
theorem B4914917 : Blo 428775 4914917 := bstep (se 4 (by rfl) ⟨460773, by rfl⟩ : syracuseStep 4914917 = 921547) B921547
theorem B67927853 : Blo 428775 67927853 := bstep (se 3 (by rfl) ⟨12736472, by rfl⟩ : syracuseStep 67927853 = 25472945) B25472945
theorem B2064179 : Blo 428775 2064179 := bstep (se 1 (by rfl) ⟨1548134, by rfl⟩ : syracuseStep 2064179 = 3096269) B3096269
theorem B688457 : Blo 428775 688457 := bstep (se 2 (by rfl) ⟨258171, by rfl⟩ : syracuseStep 688457 = 516343) B516343
theorem B1638899 : Blo 428775 1638899 := bstep (se 1 (by rfl) ⟨1229174, by rfl⟩ : syracuseStep 1638899 = 2458349) B2458349
theorem B819791 : Blo 428775 819791 := bstep (se 1 (by rfl) ⟨614843, by rfl⟩ : syracuseStep 819791 = 1229687) B1229687
theorem B7078499 : Blo 428775 7078499 := bstep (se 1 (by rfl) ⟨5308874, by rfl⟩ : syracuseStep 7078499 = 10617749) B10617749
theorem B3113801 : Blo 428775 3113801 := bstep (se 2 (by rfl) ⟨1167675, by rfl⟩ : syracuseStep 3113801 = 2335351) B2335351
theorem B2065409 : Blo 428775 2065409 := bstep (se 2 (by rfl) ⟨774528, by rfl⟩ : syracuseStep 2065409 = 1549057) B1549057
theorem B1377287 : Blo 428775 1377287 := bstep (se 1 (by rfl) ⟨1032965, by rfl⟩ : syracuseStep 1377287 = 2065931) B2065931
theorem B5506319 : Blo 428775 5506319 := bstep (se 1 (by rfl) ⟨4129739, by rfl⟩ : syracuseStep 5506319 = 8259479) B8259479
theorem B2459099 : Blo 428775 2459099 := bstep (se 1 (by rfl) ⟨1844324, by rfl⟩ : syracuseStep 2459099 = 3688649) B3688649
theorem B820793 : Blo 428775 820793 := bstep (se 2 (by rfl) ⟨307797, by rfl⟩ : syracuseStep 820793 = 615595) B615595
theorem B2459281 : Blo 428775 2459281 := bstep (se 2 (by rfl) ⟨922230, by rfl⟩ : syracuseStep 2459281 = 1844461) B1844461
theorem B1574927 : Blo 428775 1574927 := bstep (se 1 (by rfl) ⟨1181195, by rfl⟩ : syracuseStep 1574927 = 2362391) B2362391
theorem B1869905 : Blo 428775 1869905 := bstep (se 2 (by rfl) ⟨701214, by rfl⟩ : syracuseStep 1869905 = 1402429) B1402429
theorem B2984471 : Blo 428775 2984471 := bstep (se 1 (by rfl) ⟨2238353, by rfl⟩ : syracuseStep 2984471 = 4476707) B4476707
theorem B2329121 : Blo 428775 2329121 := bstep (se 2 (by rfl) ⟨873420, by rfl⟩ : syracuseStep 2329121 = 1746841) B1746841
theorem B16714421 : Blo 428775 16714421 := bstep (se 5 (by rfl) ⟨783488, by rfl⟩ : syracuseStep 16714421 = 1566977) B1566977
theorem B428839 : Blo 428775 428839 := bstep (se 1 (by rfl) ⟨321629, by rfl⟩ : syracuseStep 428839 = 643259) B643259
theorem B428879 : Blo 428775 428879 := bstep (se 1 (by rfl) ⟨321659, by rfl⟩ : syracuseStep 428879 = 643319) B643319
theorem B428895 : Blo 428775 428895 := bstep (se 1 (by rfl) ⟨321671, by rfl⟩ : syracuseStep 428895 = 643343) B643343
theorem B1739639 : Blo 428775 1739639 := bstep (se 1 (by rfl) ⟨1304729, by rfl⟩ : syracuseStep 1739639 = 2609459) B2609459
theorem B428923 : Blo 428775 428923 := bstep (se 1 (by rfl) ⟨321692, by rfl⟩ : syracuseStep 428923 = 643385) B643385
theorem B428975 : Blo 428775 428975 := bstep (se 1 (by rfl) ⟨321731, by rfl⟩ : syracuseStep 428975 = 643463) B643463
theorem B428999 : Blo 428775 428999 := bstep (se 1 (by rfl) ⟨321749, by rfl⟩ : syracuseStep 428999 = 643499) B643499
theorem B429019 : Blo 428775 429019 := bstep (se 1 (by rfl) ⟨321764, by rfl⟩ : syracuseStep 429019 = 643529) B643529
theorem B429095 : Blo 428775 429095 := bstep (se 1 (by rfl) ⟨321821, by rfl⟩ : syracuseStep 429095 = 643643) B643643
theorem B724025 : Blo 428775 724025 := bstep (se 2 (by rfl) ⟨271509, by rfl⟩ : syracuseStep 724025 = 543019) B543019
theorem B429135 : Blo 428775 429135 := bstep (se 1 (by rfl) ⟨321851, by rfl⟩ : syracuseStep 429135 = 643703) B643703
theorem B1838159 : Blo 428775 1838159 := bstep (se 1 (by rfl) ⟨1378619, by rfl⟩ : syracuseStep 1838159 = 2757239) B2757239
theorem B429151 : Blo 428775 429151 := bstep (se 1 (by rfl) ⟨321863, by rfl⟩ : syracuseStep 429151 = 643727) B643727
theorem B429179 : Blo 428775 429179 := bstep (se 1 (by rfl) ⟨321884, by rfl⟩ : syracuseStep 429179 = 643769) B643769
theorem B429231 : Blo 428775 429231 := bstep (se 1 (by rfl) ⟨321923, by rfl⟩ : syracuseStep 429231 = 643847) B643847
theorem B429255 : Blo 428775 429255 := bstep (se 1 (by rfl) ⟨321941, by rfl⟩ : syracuseStep 429255 = 643883) B643883
theorem B429275 : Blo 428775 429275 := bstep (se 1 (by rfl) ⟨321956, by rfl⟩ : syracuseStep 429275 = 643913) B643913
theorem B429351 : Blo 428775 429351 := bstep (se 1 (by rfl) ⟨322013, by rfl⟩ : syracuseStep 429351 = 644027) B644027
theorem B429391 : Blo 428775 429391 := bstep (se 1 (by rfl) ⟨322043, by rfl⟩ : syracuseStep 429391 = 644087) B644087
theorem B1641815 : Blo 428775 1641815 := bstep (se 1 (by rfl) ⟨1231361, by rfl⟩ : syracuseStep 1641815 = 2462723) B2462723
theorem B429407 : Blo 428775 429407 := bstep (se 1 (by rfl) ⟨322055, by rfl⟩ : syracuseStep 429407 = 644111) B644111
theorem B429435 : Blo 428775 429435 := bstep (se 1 (by rfl) ⟨322076, by rfl⟩ : syracuseStep 429435 = 644153) B644153
theorem B429487 : Blo 428775 429487 := bstep (se 1 (by rfl) ⟨322115, by rfl⟩ : syracuseStep 429487 = 644231) B644231
theorem B429511 : Blo 428775 429511 := bstep (se 1 (by rfl) ⟨322133, by rfl⟩ : syracuseStep 429511 = 644267) B644267
theorem B429531 : Blo 428775 429531 := bstep (se 1 (by rfl) ⟨322148, by rfl⟩ : syracuseStep 429531 = 644297) B644297
theorem B1740275 : Blo 428775 1740275 := bstep (se 1 (by rfl) ⟨1305206, by rfl⟩ : syracuseStep 1740275 = 2610413) B2610413
theorem B429607 : Blo 428775 429607 := bstep (se 1 (by rfl) ⟨322205, by rfl⟩ : syracuseStep 429607 = 644411) B644411
theorem B429647 : Blo 428775 429647 := bstep (se 1 (by rfl) ⟨322235, by rfl⟩ : syracuseStep 429647 = 644471) B644471
theorem B429663 : Blo 428775 429663 := bstep (se 1 (by rfl) ⟨322247, by rfl⟩ : syracuseStep 429663 = 644495) B644495
theorem B3968635 : Blo 428775 3968635 := bstep (se 1 (by rfl) ⟨2976476, by rfl⟩ : syracuseStep 3968635 = 5952953) B5952953
theorem B429691 : Blo 428775 429691 := bstep (se 1 (by rfl) ⟨322268, by rfl⟩ : syracuseStep 429691 = 644537) B644537
theorem B1379963 : Blo 428775 1379963 := bstep (se 1 (by rfl) ⟨1034972, by rfl⟩ : syracuseStep 1379963 = 2069945) B2069945
theorem B429743 : Blo 428775 429743 := bstep (se 1 (by rfl) ⟨322307, by rfl⟩ : syracuseStep 429743 = 644615) B644615
theorem B1740487 : Blo 428775 1740487 := bstep (se 1 (by rfl) ⟨1305365, by rfl⟩ : syracuseStep 1740487 = 2610731) B2610731
theorem B429767 : Blo 428775 429767 := bstep (se 1 (by rfl) ⟨322325, by rfl⟩ : syracuseStep 429767 = 644651) B644651
theorem B429787 : Blo 428775 429787 := bstep (se 1 (by rfl) ⟨322340, by rfl⟩ : syracuseStep 429787 = 644681) B644681
theorem B724727 : Blo 428775 724727 := bstep (se 1 (by rfl) ⟨543545, by rfl⟩ : syracuseStep 724727 = 1087091) B1087091
theorem B429863 : Blo 428775 429863 := bstep (se 1 (by rfl) ⟨322397, by rfl⟩ : syracuseStep 429863 = 644795) B644795
theorem B429903 : Blo 428775 429903 := bstep (se 1 (by rfl) ⟨322427, by rfl⟩ : syracuseStep 429903 = 644855) B644855
theorem B429919 : Blo 428775 429919 := bstep (se 1 (by rfl) ⟨322439, by rfl⟩ : syracuseStep 429919 = 644879) B644879
theorem B429947 : Blo 428775 429947 := bstep (se 1 (by rfl) ⟨322460, by rfl⟩ : syracuseStep 429947 = 644921) B644921
theorem B1085359 : Blo 428775 1085359 := bstep (se 1 (by rfl) ⟨814019, by rfl⟩ : syracuseStep 1085359 = 1628039) B1628039
theorem B429999 : Blo 428775 429999 := bstep (se 1 (by rfl) ⟨322499, by rfl⟩ : syracuseStep 429999 = 644999) B644999
theorem B3477433 : Blo 428775 3477433 := bstep (se 2 (by rfl) ⟨1304037, by rfl⟩ : syracuseStep 3477433 = 2608075) B2608075
theorem B430023 : Blo 428775 430023 := bstep (se 1 (by rfl) ⟨322517, by rfl⟩ : syracuseStep 430023 = 645035) B645035
theorem B430043 : Blo 428775 430043 := bstep (se 1 (by rfl) ⟨322532, by rfl⟩ : syracuseStep 430043 = 645065) B645065
theorem B692231 : Blo 428775 692231 := bstep (se 1 (by rfl) ⟨519173, by rfl⟩ : syracuseStep 692231 = 1038347) B1038347
theorem B430119 : Blo 428775 430119 := bstep (se 1 (by rfl) ⟨322589, by rfl⟩ : syracuseStep 430119 = 645179) B645179
theorem B692263 : Blo 428775 692263 := bstep (se 1 (by rfl) ⟨519197, by rfl⟩ : syracuseStep 692263 = 1038395) B1038395
theorem B725071 : Blo 428775 725071 := bstep (se 1 (by rfl) ⟨543803, by rfl⟩ : syracuseStep 725071 = 1087607) B1087607
theorem B430159 : Blo 428775 430159 := bstep (se 1 (by rfl) ⟨322619, by rfl⟩ : syracuseStep 430159 = 645239) B645239
theorem B3280985 : Blo 428775 3280985 := bstep (se 2 (by rfl) ⟨1230369, by rfl⟩ : syracuseStep 3280985 = 2460739) B2460739
theorem B430175 : Blo 428775 430175 := bstep (se 1 (by rfl) ⟨322631, by rfl⟩ : syracuseStep 430175 = 645263) B645263
theorem B430203 : Blo 428775 430203 := bstep (se 1 (by rfl) ⟨322652, by rfl⟩ : syracuseStep 430203 = 645305) B645305
theorem B430255 : Blo 428775 430255 := bstep (se 1 (by rfl) ⟨322691, by rfl⟩ : syracuseStep 430255 = 645383) B645383
theorem B430279 : Blo 428775 430279 := bstep (se 1 (by rfl) ⟨322709, by rfl⟩ : syracuseStep 430279 = 645419) B645419
theorem B430299 : Blo 428775 430299 := bstep (se 1 (by rfl) ⟨322724, by rfl⟩ : syracuseStep 430299 = 645449) B645449
theorem B430375 : Blo 428775 430375 := bstep (se 1 (by rfl) ⟨322781, by rfl⟩ : syracuseStep 430375 = 645563) B645563
theorem B725321 : Blo 428775 725321 := bstep (se 2 (by rfl) ⟨271995, by rfl⟩ : syracuseStep 725321 = 543991) B543991
theorem B430415 : Blo 428775 430415 := bstep (se 1 (by rfl) ⟨322811, by rfl⟩ : syracuseStep 430415 = 645623) B645623
theorem B430431 : Blo 428775 430431 := bstep (se 1 (by rfl) ⟨322823, by rfl⟩ : syracuseStep 430431 = 645647) B645647
theorem B430459 : Blo 428775 430459 := bstep (se 1 (by rfl) ⟨322844, by rfl⟩ : syracuseStep 430459 = 645689) B645689
theorem B1085825 : Blo 428775 1085825 := bstep (se 2 (by rfl) ⟨407184, by rfl⟩ : syracuseStep 1085825 = 814369) B814369
theorem B430511 : Blo 428775 430511 := bstep (se 1 (by rfl) ⟨322883, by rfl⟩ : syracuseStep 430511 = 645767) B645767
theorem B430535 : Blo 428775 430535 := bstep (se 1 (by rfl) ⟨322901, by rfl⟩ : syracuseStep 430535 = 645803) B645803
theorem B430555 : Blo 428775 430555 := bstep (se 1 (by rfl) ⟨322916, by rfl⟩ : syracuseStep 430555 = 645833) B645833
theorem B3478049 : Blo 428775 3478049 := bstep (se 2 (by rfl) ⟨1304268, by rfl⟩ : syracuseStep 3478049 = 2608537) B2608537
theorem B430631 : Blo 428775 430631 := bstep (se 1 (by rfl) ⟨322973, by rfl⟩ : syracuseStep 430631 = 645947) B645947
theorem B430671 : Blo 428775 430671 := bstep (se 1 (by rfl) ⟨323003, by rfl⟩ : syracuseStep 430671 = 646007) B646007
theorem B430687 : Blo 428775 430687 := bstep (se 1 (by rfl) ⟨323015, by rfl⟩ : syracuseStep 430687 = 646031) B646031
theorem B1643105 : Blo 428775 1643105 := bstep (se 2 (by rfl) ⟨616164, by rfl⟩ : syracuseStep 1643105 = 1232329) B1232329
theorem B430715 : Blo 428775 430715 := bstep (se 1 (by rfl) ⟨323036, by rfl⟩ : syracuseStep 430715 = 646073) B646073
theorem B430767 : Blo 428775 430767 := bstep (se 1 (by rfl) ⟨323075, by rfl⟩ : syracuseStep 430767 = 646151) B646151
theorem B430791 : Blo 428775 430791 := bstep (se 1 (by rfl) ⟨323093, by rfl⟩ : syracuseStep 430791 = 646187) B646187
theorem B430811 : Blo 428775 430811 := bstep (se 1 (by rfl) ⟨323108, by rfl⟩ : syracuseStep 430811 = 646217) B646217
theorem B725753 : Blo 428775 725753 := bstep (se 2 (by rfl) ⟨272157, by rfl⟩ : syracuseStep 725753 = 544315) B544315
theorem B430887 : Blo 428775 430887 := bstep (se 1 (by rfl) ⟨323165, by rfl⟩ : syracuseStep 430887 = 646331) B646331
theorem B1086281 : Blo 428775 1086281 := bstep (se 2 (by rfl) ⟨407355, by rfl⟩ : syracuseStep 1086281 = 814711) B814711
theorem B430927 : Blo 428775 430927 := bstep (se 1 (by rfl) ⟨323195, by rfl⟩ : syracuseStep 430927 = 646391) B646391
theorem B430943 : Blo 428775 430943 := bstep (se 1 (by rfl) ⟨323207, by rfl⟩ : syracuseStep 430943 = 646415) B646415
theorem B430971 : Blo 428775 430971 := bstep (se 1 (by rfl) ⟨323228, by rfl⟩ : syracuseStep 430971 = 646457) B646457
theorem B725935 : Blo 428775 725935 := bstep (se 1 (by rfl) ⟨544451, by rfl⟩ : syracuseStep 725935 = 1088903) B1088903
theorem B431023 : Blo 428775 431023 := bstep (se 1 (by rfl) ⟨323267, by rfl⟩ : syracuseStep 431023 = 646535) B646535
theorem B431047 : Blo 428775 431047 := bstep (se 1 (by rfl) ⟨323285, by rfl⟩ : syracuseStep 431047 = 646571) B646571
theorem B431067 : Blo 428775 431067 := bstep (se 1 (by rfl) ⟨323300, by rfl⟩ : syracuseStep 431067 = 646601) B646601
theorem B6231005 : Blo 428775 6231005 := bstep (se 3 (by rfl) ⟨1168313, by rfl⟩ : syracuseStep 6231005 = 2336627) B2336627
theorem B35754979 : Blo 428775 35754979 := bstep (se 1 (by rfl) ⟨26816234, by rfl⟩ : syracuseStep 35754979 = 53632469) B53632469
theorem B726023 : Blo 428775 726023 := bstep (se 1 (by rfl) ⟨544517, by rfl⟩ : syracuseStep 726023 = 1089035) B1089035
theorem B431143 : Blo 428775 431143 := bstep (se 1 (by rfl) ⟨323357, by rfl⟩ : syracuseStep 431143 = 646715) B646715
theorem B431183 : Blo 428775 431183 := bstep (se 1 (by rfl) ⟨323387, by rfl⟩ : syracuseStep 431183 = 646775) B646775
theorem B431199 : Blo 428775 431199 := bstep (se 1 (by rfl) ⟨323399, by rfl⟩ : syracuseStep 431199 = 646799) B646799
theorem B431227 : Blo 428775 431227 := bstep (se 1 (by rfl) ⟨323420, by rfl⟩ : syracuseStep 431227 = 646841) B646841
theorem B1086635 : Blo 428775 1086635 := bstep (se 1 (by rfl) ⟨814976, by rfl⟩ : syracuseStep 1086635 = 1629953) B1629953
theorem B431279 : Blo 428775 431279 := bstep (se 1 (by rfl) ⟨323459, by rfl⟩ : syracuseStep 431279 = 646919) B646919
theorem B431303 : Blo 428775 431303 := bstep (se 1 (by rfl) ⟨323477, by rfl⟩ : syracuseStep 431303 = 646955) B646955
theorem B431323 : Blo 428775 431323 := bstep (se 1 (by rfl) ⟨323492, by rfl⟩ : syracuseStep 431323 = 646985) B646985
theorem B431399 : Blo 428775 431399 := bstep (se 1 (by rfl) ⟨323549, by rfl⟩ : syracuseStep 431399 = 647099) B647099
theorem B431439 : Blo 428775 431439 := bstep (se 1 (by rfl) ⟨323579, by rfl⟩ : syracuseStep 431439 = 647159) B647159
theorem B726367 : Blo 428775 726367 := bstep (se 1 (by rfl) ⟨544775, by rfl⟩ : syracuseStep 726367 = 1089551) B1089551
theorem B431455 : Blo 428775 431455 := bstep (se 1 (by rfl) ⟨323591, by rfl⟩ : syracuseStep 431455 = 647183) B647183
theorem B431483 : Blo 428775 431483 := bstep (se 1 (by rfl) ⟨323612, by rfl⟩ : syracuseStep 431483 = 647225) B647225
theorem B431535 : Blo 428775 431535 := bstep (se 1 (by rfl) ⟨323651, by rfl⟩ : syracuseStep 431535 = 647303) B647303
theorem B726455 : Blo 428775 726455 := bstep (se 1 (by rfl) ⟨544841, by rfl⟩ : syracuseStep 726455 = 1089683) B1089683
theorem B431559 : Blo 428775 431559 := bstep (se 1 (by rfl) ⟨323669, by rfl⟩ : syracuseStep 431559 = 647339) B647339
theorem B431579 : Blo 428775 431579 := bstep (se 1 (by rfl) ⟨323684, by rfl⟩ : syracuseStep 431579 = 647369) B647369
theorem B3282443 : Blo 428775 3282443 := bstep (se 1 (by rfl) ⟨2461832, by rfl⟩ : syracuseStep 3282443 = 4923665) B4923665
theorem B431655 : Blo 428775 431655 := bstep (se 1 (by rfl) ⟨323741, by rfl⟩ : syracuseStep 431655 = 647483) B647483
theorem B431695 : Blo 428775 431695 := bstep (se 1 (by rfl) ⟨323771, by rfl⟩ : syracuseStep 431695 = 647543) B647543
theorem B431711 : Blo 428775 431711 := bstep (se 1 (by rfl) ⟨323783, by rfl⟩ : syracuseStep 431711 = 647567) B647567
theorem B431739 : Blo 428775 431739 := bstep (se 1 (by rfl) ⟨323804, by rfl⟩ : syracuseStep 431739 = 647609) B647609
theorem B431791 : Blo 428775 431791 := bstep (se 1 (by rfl) ⟨323843, by rfl⟩ : syracuseStep 431791 = 647687) B647687
theorem B431815 : Blo 428775 431815 := bstep (se 1 (by rfl) ⟨323861, by rfl⟩ : syracuseStep 431815 = 647723) B647723
theorem B431835 : Blo 428775 431835 := bstep (se 1 (by rfl) ⟨323876, by rfl⟩ : syracuseStep 431835 = 647753) B647753
theorem B431911 : Blo 428775 431911 := bstep (se 1 (by rfl) ⟨323933, by rfl⟩ : syracuseStep 431911 = 647867) B647867
theorem B431951 : Blo 428775 431951 := bstep (se 1 (by rfl) ⟨323963, by rfl⟩ : syracuseStep 431951 = 647927) B647927
theorem B431967 : Blo 428775 431967 := bstep (se 1 (by rfl) ⟨323975, by rfl⟩ : syracuseStep 431967 = 647951) B647951
theorem B431995 : Blo 428775 431995 := bstep (se 1 (by rfl) ⟨323996, by rfl⟩ : syracuseStep 431995 = 647993) B647993
theorem B1742753 : Blo 428775 1742753 := bstep (se 2 (by rfl) ⟨653532, by rfl⟩ : syracuseStep 1742753 = 1307065) B1307065
theorem B432047 : Blo 428775 432047 := bstep (se 1 (by rfl) ⟨324035, by rfl⟩ : syracuseStep 432047 = 648071) B648071
theorem B1087415 : Blo 428775 1087415 := bstep (se 1 (by rfl) ⟨815561, by rfl⟩ : syracuseStep 1087415 = 1631123) B1631123
theorem B432071 : Blo 428775 432071 := bstep (se 1 (by rfl) ⟨324053, by rfl⟩ : syracuseStep 432071 = 648107) B648107
theorem B432091 : Blo 428775 432091 := bstep (se 1 (by rfl) ⟨324068, by rfl⟩ : syracuseStep 432091 = 648137) B648137
theorem B727049 : Blo 428775 727049 := bstep (se 2 (by rfl) ⟨272643, by rfl⟩ : syracuseStep 727049 = 545287) B545287
theorem B1447955 : Blo 428775 1447955 := bstep (se 1 (by rfl) ⟨1085966, by rfl⟩ : syracuseStep 1447955 = 2171933) B2171933
theorem B432167 : Blo 428775 432167 := bstep (se 1 (by rfl) ⟨324125, by rfl⟩ : syracuseStep 432167 = 648251) B648251
theorem B432207 : Blo 428775 432207 := bstep (se 1 (by rfl) ⟨324155, by rfl⟩ : syracuseStep 432207 = 648311) B648311
theorem B432223 : Blo 428775 432223 := bstep (se 1 (by rfl) ⟨324167, by rfl⟩ : syracuseStep 432223 = 648335) B648335
theorem B432251 : Blo 428775 432251 := bstep (se 1 (by rfl) ⟨324188, by rfl⟩ : syracuseStep 432251 = 648377) B648377
theorem B727211 : Blo 428775 727211 := bstep (se 1 (by rfl) ⟨545408, by rfl⟩ : syracuseStep 727211 = 1090817) B1090817
theorem B432303 : Blo 428775 432303 := bstep (se 1 (by rfl) ⟨324227, by rfl⟩ : syracuseStep 432303 = 648455) B648455
theorem B432327 : Blo 428775 432327 := bstep (se 1 (by rfl) ⟨324245, by rfl⟩ : syracuseStep 432327 = 648491) B648491
theorem B432347 : Blo 428775 432347 := bstep (se 1 (by rfl) ⟨324260, by rfl⟩ : syracuseStep 432347 = 648521) B648521
theorem B432423 : Blo 428775 432423 := bstep (se 1 (by rfl) ⟨324317, by rfl⟩ : syracuseStep 432423 = 648635) B648635
theorem B3742001 : Blo 428775 3742001 := bstep (se 2 (by rfl) ⟨1403250, by rfl⟩ : syracuseStep 3742001 = 2806501) B2806501
theorem B432463 : Blo 428775 432463 := bstep (se 1 (by rfl) ⟨324347, by rfl⟩ : syracuseStep 432463 = 648695) B648695
theorem B1448279 : Blo 428775 1448279 := bstep (se 1 (by rfl) ⟨1086209, by rfl⟩ : syracuseStep 1448279 = 2172419) B2172419
theorem B432479 : Blo 428775 432479 := bstep (se 1 (by rfl) ⟨324359, by rfl⟩ : syracuseStep 432479 = 648719) B648719
theorem B432507 : Blo 428775 432507 := bstep (se 1 (by rfl) ⟨324380, by rfl⟩ : syracuseStep 432507 = 648761) B648761
theorem B1776001 : Blo 428775 1776001 := bstep (se 2 (by rfl) ⟨666000, by rfl⟩ : syracuseStep 1776001 = 1332001) B1332001
theorem B8853893 : Blo 428775 8853893 := bstep (se 4 (by rfl) ⟨830052, by rfl⟩ : syracuseStep 8853893 = 1660105) B1660105
theorem B432559 : Blo 428775 432559 := bstep (se 1 (by rfl) ⟨324419, by rfl⟩ : syracuseStep 432559 = 648839) B648839
theorem B432583 : Blo 428775 432583 := bstep (se 1 (by rfl) ⟨324437, by rfl⟩ : syracuseStep 432583 = 648875) B648875
theorem B432603 : Blo 428775 432603 := bstep (se 1 (by rfl) ⟨324452, by rfl⟩ : syracuseStep 432603 = 648905) B648905
theorem B2071021 : Blo 428775 2071021 := bstep (se 3 (by rfl) ⟨388316, by rfl⟩ : syracuseStep 2071021 = 776633) B776633
theorem B432679 : Blo 428775 432679 := bstep (se 1 (by rfl) ⟨324509, by rfl⟩ : syracuseStep 432679 = 649019) B649019
theorem B727609 : Blo 428775 727609 := bstep (se 2 (by rfl) ⟨272853, by rfl⟩ : syracuseStep 727609 = 545707) B545707
theorem B432719 : Blo 428775 432719 := bstep (se 1 (by rfl) ⟨324539, by rfl⟩ : syracuseStep 432719 = 649079) B649079
theorem B432735 : Blo 428775 432735 := bstep (se 1 (by rfl) ⟨324551, by rfl⟩ : syracuseStep 432735 = 649103) B649103
theorem B432763 : Blo 428775 432763 := bstep (se 1 (by rfl) ⟨324572, by rfl⟩ : syracuseStep 432763 = 649145) B649145
theorem B1841849 : Blo 428775 1841849 := bstep (se 2 (by rfl) ⟨690693, by rfl⟩ : syracuseStep 1841849 = 1381387) B1381387
theorem B727751 : Blo 428775 727751 := bstep (se 1 (by rfl) ⟨545813, by rfl⟩ : syracuseStep 727751 = 1091627) B1091627
theorem B727913 : Blo 428775 727913 := bstep (se 2 (by rfl) ⟨272967, by rfl⟩ : syracuseStep 727913 = 545935) B545935
theorem B1088417 : Blo 428775 1088417 := bstep (se 2 (by rfl) ⟨408156, by rfl⟩ : syracuseStep 1088417 = 816313) B816313
theorem B2530223 : Blo 428775 2530223 := bstep (se 1 (by rfl) ⟨1897667, by rfl⟩ : syracuseStep 2530223 = 3795335) B3795335
theorem B1973443 : Blo 428775 1973443 := bstep (se 1 (by rfl) ⟨1480082, by rfl⟩ : syracuseStep 1973443 = 2960165) B2960165
theorem B728311 : Blo 428775 728311 := bstep (se 1 (by rfl) ⟨546233, by rfl⟩ : syracuseStep 728311 = 1092467) B1092467
theorem B1547531 : Blo 428775 1547531 := bstep (se 1 (by rfl) ⟨1160648, by rfl⟩ : syracuseStep 1547531 = 2321297) B2321297
theorem B1088873 : Blo 428775 1088873 := bstep (se 2 (by rfl) ⟨408327, by rfl⟩ : syracuseStep 1088873 = 816655) B816655
theorem B1449359 : Blo 428775 1449359 := bstep (se 1 (by rfl) ⟨1087019, by rfl⟩ : syracuseStep 1449359 = 2174039) B2174039
theorem B3284387 : Blo 428775 3284387 := bstep (se 1 (by rfl) ⟨2463290, by rfl⟩ : syracuseStep 3284387 = 4926581) B4926581
theorem B728507 : Blo 428775 728507 := bstep (se 1 (by rfl) ⟨546380, by rfl⟩ : syracuseStep 728507 = 1092761) B1092761
theorem B1383961 : Blo 428775 1383961 := bstep (se 2 (by rfl) ⟨518985, by rfl⟩ : syracuseStep 1383961 = 1037971) B1037971
theorem B728615 : Blo 428775 728615 := bstep (se 1 (by rfl) ⟨546461, by rfl⟩ : syracuseStep 728615 = 1092923) B1092923
theorem B1777351 : Blo 428775 1777351 := bstep (se 1 (by rfl) ⟨1333013, by rfl⟩ : syracuseStep 1777351 = 2666027) B2666027
theorem B1449683 : Blo 428775 1449683 := bstep (se 1 (by rfl) ⟨1087262, by rfl⟩ : syracuseStep 1449683 = 2174525) B2174525
theorem B728905 : Blo 428775 728905 := bstep (se 2 (by rfl) ⟨273339, by rfl⟩ : syracuseStep 728905 = 546679) B546679
theorem B728939 : Blo 428775 728939 := bstep (se 1 (by rfl) ⟨546704, by rfl⟩ : syracuseStep 728939 = 1093409) B1093409
theorem B2170961 : Blo 428775 2170961 := bstep (se 2 (by rfl) ⟨814110, by rfl⟩ : syracuseStep 2170961 = 1628221) B1628221
theorem B729337 : Blo 428775 729337 := bstep (se 2 (by rfl) ⟨273501, by rfl⟩ : syracuseStep 729337 = 547003) B547003
theorem B1221007 : Blo 428775 1221007 := bstep (se 1 (by rfl) ⟨915755, by rfl⟩ : syracuseStep 1221007 = 1831511) B1831511
theorem B729607 : Blo 428775 729607 := bstep (se 1 (by rfl) ⟨547205, by rfl⟩ : syracuseStep 729607 = 1094411) B1094411
theorem B1090057 : Blo 428775 1090057 := bstep (se 2 (by rfl) ⟨408771, by rfl⟩ : syracuseStep 1090057 = 817543) B817543
theorem B1843847 : Blo 428775 1843847 := bstep (se 1 (by rfl) ⟨1382885, by rfl⟩ : syracuseStep 1843847 = 2765771) B2765771
theorem B1450871 : Blo 428775 1450871 := bstep (se 1 (by rfl) ⟨1088153, by rfl⟩ : syracuseStep 1450871 = 2176307) B2176307
theorem B730039 : Blo 428775 730039 := bstep (se 1 (by rfl) ⟨547529, by rfl⟩ : syracuseStep 730039 = 1095059) B1095059
theorem B2761771 : Blo 428775 2761771 := bstep (se 1 (by rfl) ⟨2071328, by rfl⟩ : syracuseStep 2761771 = 4142657) B4142657
theorem B1451087 : Blo 428775 1451087 := bstep (se 1 (by rfl) ⟨1088315, by rfl⟩ : syracuseStep 1451087 = 2176631) B2176631
theorem B730235 : Blo 428775 730235 := bstep (se 1 (by rfl) ⟨547676, by rfl⟩ : syracuseStep 730235 = 1095353) B1095353
theorem B1451465 : Blo 428775 1451465 := bstep (se 2 (by rfl) ⟨544299, by rfl⟩ : syracuseStep 1451465 = 1088599) B1088599
theorem B2762363 : Blo 428775 2762363 := bstep (se 1 (by rfl) ⟨2071772, by rfl⟩ : syracuseStep 2762363 = 4143545) B4143545
theorem B1222283 : Blo 428775 1222283 := bstep (se 1 (by rfl) ⟨916712, by rfl⟩ : syracuseStep 1222283 = 1833425) B1833425
theorem B2762387 : Blo 428775 2762387 := bstep (se 1 (by rfl) ⟨2071790, by rfl⟩ : syracuseStep 2762387 = 4143581) B4143581
theorem B1451735 : Blo 428775 1451735 := bstep (se 1 (by rfl) ⟨1088801, by rfl⟩ : syracuseStep 1451735 = 2177603) B2177603
theorem B1746647 : Blo 428775 1746647 := bstep (se 1 (by rfl) ⟨1309985, by rfl⟩ : syracuseStep 1746647 = 2619971) B2619971
theorem B1550153 : Blo 428775 1550153 := bstep (se 2 (by rfl) ⟨581307, by rfl⟩ : syracuseStep 1550153 = 1162615) B1162615
theorem B3319661 : Blo 428775 3319661 := bstep (se 3 (by rfl) ⟨622436, by rfl⟩ : syracuseStep 3319661 = 1244873) B1244873
theorem B8857505 : Blo 428775 8857505 := bstep (se 2 (by rfl) ⟨3321564, by rfl⟩ : syracuseStep 8857505 = 6643129) B6643129
theorem B1451951 : Blo 428775 1451951 := bstep (se 1 (by rfl) ⟨1088963, by rfl⟩ : syracuseStep 1451951 = 2177927) B2177927
theorem B1091515 : Blo 428775 1091515 := bstep (se 1 (by rfl) ⟨818636, by rfl⟩ : syracuseStep 1091515 = 1637273) B1637273
theorem B1846273 : Blo 428775 1846273 := bstep (se 2 (by rfl) ⟨692352, by rfl⟩ : syracuseStep 1846273 = 1384705) B1384705
theorem B6204761 : Blo 428775 6204761 := bstep (se 2 (by rfl) ⟨2326785, by rfl⟩ : syracuseStep 6204761 = 4653571) B4653571
theorem B1846907 : Blo 428775 1846907 := bstep (se 1 (by rfl) ⟨1385180, by rfl⟩ : syracuseStep 1846907 = 2770361) B2770361
theorem B2797379 : Blo 428775 2797379 := bstep (se 1 (by rfl) ⟨2098034, by rfl⟩ : syracuseStep 2797379 = 4196069) B4196069
theorem B3256199 : Blo 428775 3256199 := bstep (se 1 (by rfl) ⟨2442149, by rfl⟩ : syracuseStep 3256199 = 4884299) B4884299
theorem B26619799 : Blo 428775 26619799 := bstep (se 1 (by rfl) ⟨19964849, by rfl⟩ : syracuseStep 26619799 = 39929699) B39929699
theorem B1454327 : Blo 428775 1454327 := bstep (se 1 (by rfl) ⟨1090745, by rfl⟩ : syracuseStep 1454327 = 2181491) B2181491
theorem B733583 : Blo 428775 733583 := bstep (se 1 (by rfl) ⟨550187, by rfl⟩ : syracuseStep 733583 = 1100375) B1100375
theorem B1094107 : Blo 428775 1094107 := bstep (se 1 (by rfl) ⟨820580, by rfl⟩ : syracuseStep 1094107 = 1641161) B1641161
theorem B2175497 : Blo 428775 2175497 := bstep (se 2 (by rfl) ⟨815811, by rfl⟩ : syracuseStep 2175497 = 1631623) B1631623
theorem B1454651 : Blo 428775 1454651 := bstep (se 1 (by rfl) ⟨1090988, by rfl⟩ : syracuseStep 1454651 = 2181977) B2181977
theorem B1225313 : Blo 428775 1225313 := bstep (se 2 (by rfl) ⟨459492, by rfl⟩ : syracuseStep 1225313 = 918985) B918985
theorem B1454921 : Blo 428775 1454921 := bstep (se 2 (by rfl) ⟨545595, by rfl⟩ : syracuseStep 1454921 = 1091191) B1091191
theorem B1225655 : Blo 428775 1225655 := bstep (se 1 (by rfl) ⟨919241, by rfl⟩ : syracuseStep 1225655 = 1838483) B1838483
theorem B1094735 : Blo 428775 1094735 := bstep (se 1 (by rfl) ⟨821051, by rfl⟩ : syracuseStep 1094735 = 1642103) B1642103
theorem B6304985 : Blo 428775 6304985 := bstep (se 2 (by rfl) ⟨2364369, by rfl⟩ : syracuseStep 6304985 = 4728739) B4728739
theorem B2078095 : Blo 428775 2078095 := bstep (se 1 (by rfl) ⟨1558571, by rfl⟩ : syracuseStep 2078095 = 3117143) B3117143
theorem B1095383 : Blo 428775 1095383 := bstep (se 1 (by rfl) ⟨821537, by rfl⟩ : syracuseStep 1095383 = 1643075) B1643075
theorem B1226657 : Blo 428775 1226657 := bstep (se 2 (by rfl) ⟨459996, by rfl⟩ : syracuseStep 1226657 = 919993) B919993
theorem B1456055 : Blo 428775 1456055 := bstep (se 1 (by rfl) ⟨1092041, by rfl⟩ : syracuseStep 1456055 = 2184083) B2184083
theorem B2176955 : Blo 428775 2176955 := bstep (se 1 (by rfl) ⟨1632716, by rfl⟩ : syracuseStep 2176955 = 3265433) B3265433
theorem B1226771 : Blo 428775 1226771 := bstep (se 1 (by rfl) ⟨920078, by rfl⟩ : syracuseStep 1226771 = 1840157) B1840157
theorem B1227113 : Blo 428775 1227113 := bstep (se 2 (by rfl) ⟨460167, by rfl⟩ : syracuseStep 1227113 = 920335) B920335
theorem B1456649 : Blo 428775 1456649 := bstep (se 2 (by rfl) ⟨546243, by rfl⟩ : syracuseStep 1456649 = 1092487) B1092487
theorem B965159 : Blo 428775 965159 := bstep (se 1 (by rfl) ⟨723869, by rfl⟩ : syracuseStep 965159 = 1447739) B1447739
theorem B2800187 : Blo 428775 2800187 := bstep (se 1 (by rfl) ⟨2100140, by rfl⟩ : syracuseStep 2800187 = 4200281) B4200281
theorem B965483 : Blo 428775 965483 := bstep (se 1 (by rfl) ⟨724112, by rfl⟩ : syracuseStep 965483 = 1448225) B1448225
theorem B965537 : Blo 428775 965537 := bstep (se 2 (by rfl) ⟨362076, by rfl⟩ : syracuseStep 965537 = 724153) B724153
theorem B1751969 : Blo 428775 1751969 := bstep (se 2 (by rfl) ⟨656988, by rfl⟩ : syracuseStep 1751969 = 1313977) B1313977
theorem B2178251 : Blo 428775 2178251 := bstep (se 1 (by rfl) ⟨1633688, by rfl⟩ : syracuseStep 2178251 = 3267377) B3267377
theorem B965879 : Blo 428775 965879 := bstep (se 1 (by rfl) ⟨724409, by rfl⟩ : syracuseStep 965879 = 1448819) B1448819
theorem B1457513 : Blo 428775 1457513 := bstep (se 2 (by rfl) ⟨546567, by rfl⟩ : syracuseStep 1457513 = 1093135) B1093135
theorem B1555949 : Blo 428775 1555949 := bstep (se 3 (by rfl) ⟨291740, by rfl⟩ : syracuseStep 1555949 = 583481) B583481
theorem B1228297 : Blo 428775 1228297 := bstep (se 2 (by rfl) ⟨460611, by rfl⟩ : syracuseStep 1228297 = 921223) B921223
theorem B3325573 : Blo 428775 3325573 := bstep (se 4 (by rfl) ⟨311772, by rfl⟩ : syracuseStep 3325573 = 623545) B623545
theorem B966473 : Blo 428775 966473 := bstep (se 2 (by rfl) ⟨362427, by rfl⟩ : syracuseStep 966473 = 724855) B724855
theorem B1752941 : Blo 428775 1752941 := bstep (se 3 (by rfl) ⟨328676, by rfl⟩ : syracuseStep 1752941 = 657353) B657353
theorem B1458107 : Blo 428775 1458107 := bstep (se 1 (by rfl) ⟨1093580, by rfl⟩ : syracuseStep 1458107 = 2187161) B2187161
theorem B3260573 : Blo 428775 3260573 := bstep (se 3 (by rfl) ⟨611357, by rfl⟩ : syracuseStep 3260573 = 1222715) B1222715
theorem B1229185 : Blo 428775 1229185 := bstep (se 2 (by rfl) ⟨460944, by rfl⟩ : syracuseStep 1229185 = 921889) B921889
theorem B967265 : Blo 428775 967265 := bstep (se 2 (by rfl) ⟨362724, by rfl⟩ : syracuseStep 967265 = 725449) B725449
theorem B967607 : Blo 428775 967607 := bstep (se 1 (by rfl) ⟨725705, by rfl⟩ : syracuseStep 967607 = 1451411) B1451411
theorem B1229755 : Blo 428775 1229755 := bstep (se 1 (by rfl) ⟨922316, by rfl⟩ : syracuseStep 1229755 = 1844633) B1844633
theorem B1197227 : Blo 428775 1197227 := bstep (se 1 (by rfl) ⟨897920, by rfl⟩ : syracuseStep 1197227 = 1795841) B1795841
theorem B968201 : Blo 428775 968201 := bstep (se 2 (by rfl) ⟨363075, by rfl⟩ : syracuseStep 968201 = 726151) B726151
theorem B1558025 : Blo 428775 1558025 := bstep (se 2 (by rfl) ⟨584259, by rfl⟩ : syracuseStep 1558025 = 1168519) B1168519
theorem B1394209 : Blo 428775 1394209 := bstep (se 2 (by rfl) ⟨522828, by rfl⟩ : syracuseStep 1394209 = 1045657) B1045657
theorem B1459835 : Blo 428775 1459835 := bstep (se 1 (by rfl) ⟨1094876, by rfl⟩ : syracuseStep 1459835 = 2189753) B2189753
theorem B6211217 : Blo 428775 6211217 := bstep (se 2 (by rfl) ⟨2329206, by rfl⟩ : syracuseStep 6211217 = 4658413) B4658413
theorem B1754833 : Blo 428775 1754833 := bstep (se 2 (by rfl) ⟨658062, by rfl⟩ : syracuseStep 1754833 = 1316125) B1316125
theorem B1459997 : Blo 428775 1459997 := bstep (se 3 (by rfl) ⟨273749, by rfl⟩ : syracuseStep 1459997 = 547499) B547499
theorem B968543 : Blo 428775 968543 := bstep (se 1 (by rfl) ⟨726407, by rfl⟩ : syracuseStep 968543 = 1452815) B1452815
theorem B968723 : Blo 428775 968723 := bstep (se 1 (by rfl) ⟨726542, by rfl⟩ : syracuseStep 968723 = 1453085) B1453085
theorem B739577 : Blo 428775 739577 := bstep (se 2 (by rfl) ⟨277341, by rfl⟩ : syracuseStep 739577 = 554683) B554683
theorem B969065 : Blo 428775 969065 := bstep (se 2 (by rfl) ⟨363399, by rfl⟩ : syracuseStep 969065 = 726799) B726799
theorem B870763 : Blo 428775 870763 := bstep (se 1 (by rfl) ⟨653072, by rfl⟩ : syracuseStep 870763 = 1306145) B1306145
theorem B2771819 : Blo 428775 2771819 := bstep (se 1 (by rfl) ⟨2078864, by rfl⟩ : syracuseStep 2771819 = 4157729) B4157729
theorem B969659 : Blo 428775 969659 := bstep (se 1 (by rfl) ⟨727244, by rfl⟩ : syracuseStep 969659 = 1454489) B1454489
theorem B3263489 : Blo 428775 3263489 := bstep (se 2 (by rfl) ⟨1223808, by rfl⟩ : syracuseStep 3263489 = 2447617) B2447617
theorem B1035271 : Blo 428775 1035271 := bstep (se 1 (by rfl) ⟨776453, by rfl⟩ : syracuseStep 1035271 = 1552907) B1552907
theorem B969785 : Blo 428775 969785 := bstep (se 2 (by rfl) ⟨363669, by rfl⟩ : syracuseStep 969785 = 727339) B727339
theorem B970127 : Blo 428775 970127 := bstep (se 1 (by rfl) ⟨727595, by rfl⟩ : syracuseStep 970127 = 1455191) B1455191
theorem B4476539 : Blo 428775 4476539 := bstep (se 1 (by rfl) ⟨3357404, by rfl⟩ : syracuseStep 4476539 = 6714809) B6714809
theorem B2936519 : Blo 428775 2936519 := bstep (se 1 (by rfl) ⟨2202389, by rfl⟩ : syracuseStep 2936519 = 4404779) B4404779
theorem B1101523 : Blo 428775 1101523 := bstep (se 1 (by rfl) ⟨826142, by rfl⟩ : syracuseStep 1101523 = 1652285) B1652285
theorem B970451 : Blo 428775 970451 := bstep (se 1 (by rfl) ⟨727838, by rfl⟩ : syracuseStep 970451 = 1455677) B1455677
theorem B3690359 : Blo 428775 3690359 := bstep (se 1 (by rfl) ⟨2767769, by rfl⟩ : syracuseStep 3690359 = 5535539) B5535539
theorem B2936737 : Blo 428775 2936737 := bstep (se 2 (by rfl) ⟨1101276, by rfl⟩ : syracuseStep 2936737 = 2202553) B2202553
theorem B643271 : Blo 428775 643271 := bstep (se 1 (by rfl) ⟨482453, by rfl⟩ : syracuseStep 643271 = 964907) B964907
theorem B2183435 : Blo 428775 2183435 := bstep (se 1 (by rfl) ⟨1637576, by rfl⟩ : syracuseStep 2183435 = 3275153) B3275153
theorem B643433 : Blo 428775 643433 := bstep (se 2 (by rfl) ⟨241287, by rfl⟩ : syracuseStep 643433 = 482575) B482575
theorem B643511 : Blo 428775 643511 := bstep (se 1 (by rfl) ⟨482633, by rfl⟩ : syracuseStep 643511 = 965267) B965267
theorem B643547 : Blo 428775 643547 := bstep (se 1 (by rfl) ⟨482660, by rfl⟩ : syracuseStep 643547 = 965321) B965321
theorem B971387 : Blo 428775 971387 := bstep (se 1 (by rfl) ⟨728540, by rfl⟩ : syracuseStep 971387 = 1457081) B1457081
theorem B54317699 : Blo 428775 54317699 := bstep (se 1 (by rfl) ⟨40738274, by rfl⟩ : syracuseStep 54317699 = 81476549) B81476549
theorem B971513 : Blo 428775 971513 := bstep (se 2 (by rfl) ⟨364317, by rfl⟩ : syracuseStep 971513 = 728635) B728635
theorem B644015 : Blo 428775 644015 := bstep (se 1 (by rfl) ⟨483011, by rfl⟩ : syracuseStep 644015 = 966023) B966023
theorem B3724289 : Blo 428775 3724289 := bstep (se 2 (by rfl) ⟨1396608, by rfl⟩ : syracuseStep 3724289 = 2793217) B2793217
theorem B971783 : Blo 428775 971783 := bstep (se 1 (by rfl) ⟨728837, by rfl⟩ : syracuseStep 971783 = 1457675) B1457675
theorem B644105 : Blo 428775 644105 := bstep (se 2 (by rfl) ⟨241539, by rfl⟩ : syracuseStep 644105 = 483079) B483079
theorem B644135 : Blo 428775 644135 := bstep (se 1 (by rfl) ⟨483101, by rfl⟩ : syracuseStep 644135 = 966203) B966203
theorem B971855 : Blo 428775 971855 := bstep (se 1 (by rfl) ⟨728891, by rfl⟩ : syracuseStep 971855 = 1457783) B1457783
theorem B644219 : Blo 428775 644219 := bstep (se 1 (by rfl) ⟨483164, by rfl⟩ : syracuseStep 644219 = 966329) B966329
theorem B644345 : Blo 428775 644345 := bstep (se 2 (by rfl) ⟨241629, by rfl⟩ : syracuseStep 644345 = 483259) B483259
theorem B644447 : Blo 428775 644447 := bstep (se 1 (by rfl) ⟨483335, by rfl⟩ : syracuseStep 644447 = 966671) B966671
theorem B644459 : Blo 428775 644459 := bstep (se 1 (by rfl) ⟨483344, by rfl⟩ : syracuseStep 644459 = 966689) B966689
theorem B775531 : Blo 428775 775531 := bstep (se 1 (by rfl) ⟨581648, by rfl⟩ : syracuseStep 775531 = 1163297) B1163297
theorem B972251 : Blo 428775 972251 := bstep (se 1 (by rfl) ⟨729188, by rfl⟩ : syracuseStep 972251 = 1458377) B1458377
theorem B644687 : Blo 428775 644687 := bstep (se 1 (by rfl) ⟨483515, by rfl⟩ : syracuseStep 644687 = 967031) B967031
theorem B2184893 : Blo 428775 2184893 := bstep (se 3 (by rfl) ⟨409667, by rfl⟩ : syracuseStep 2184893 = 819335) B819335
theorem B644807 : Blo 428775 644807 := bstep (se 1 (by rfl) ⟨483605, by rfl⟩ : syracuseStep 644807 = 967211) B967211
theorem B2185055 : Blo 428775 2185055 := bstep (se 1 (by rfl) ⟨1638791, by rfl⟩ : syracuseStep 2185055 = 3277583) B3277583
theorem B644969 : Blo 428775 644969 := bstep (se 2 (by rfl) ⟨241863, by rfl⟩ : syracuseStep 644969 = 483727) B483727
theorem B972719 : Blo 428775 972719 := bstep (se 1 (by rfl) ⟨729539, by rfl⟩ : syracuseStep 972719 = 1459079) B1459079
theorem B645047 : Blo 428775 645047 := bstep (se 1 (by rfl) ⟨483785, by rfl⟩ : syracuseStep 645047 = 967571) B967571
theorem B645083 : Blo 428775 645083 := bstep (se 1 (by rfl) ⟨483812, by rfl⟩ : syracuseStep 645083 = 967625) B967625
theorem B6969401 : Blo 428775 6969401 := bstep (se 2 (by rfl) ⟨2613525, by rfl⟩ : syracuseStep 6969401 = 5227051) B5227051
theorem B972971 : Blo 428775 972971 := bstep (se 1 (by rfl) ⟨729728, by rfl⟩ : syracuseStep 972971 = 1459457) B1459457
theorem B1169579 : Blo 428775 1169579 := bstep (se 1 (by rfl) ⟨877184, by rfl⟩ : syracuseStep 1169579 = 1754369) B1754369
theorem B1857853 : Blo 428775 1857853 := bstep (se 3 (by rfl) ⟨348347, by rfl⟩ : syracuseStep 1857853 = 696695) B696695
theorem B645551 : Blo 428775 645551 := bstep (se 1 (by rfl) ⟨484163, by rfl⟩ : syracuseStep 645551 = 968327) B968327
theorem B645641 : Blo 428775 645641 := bstep (se 2 (by rfl) ⟨242115, by rfl⟩ : syracuseStep 645641 = 484231) B484231
theorem B645671 : Blo 428775 645671 := bstep (se 1 (by rfl) ⟨484253, by rfl⟩ : syracuseStep 645671 = 968507) B968507
theorem B645755 : Blo 428775 645755 := bstep (se 1 (by rfl) ⟨484316, by rfl⟩ : syracuseStep 645755 = 968633) B968633
theorem B973511 : Blo 428775 973511 := bstep (se 1 (by rfl) ⟨730133, by rfl⟩ : syracuseStep 973511 = 1460267) B1460267
theorem B645881 : Blo 428775 645881 := bstep (se 2 (by rfl) ⟨242205, by rfl⟩ : syracuseStep 645881 = 484411) B484411
theorem B3496733 : Blo 428775 3496733 := bstep (se 3 (by rfl) ⟨655637, by rfl⟩ : syracuseStep 3496733 = 1311275) B1311275
theorem B645983 : Blo 428775 645983 := bstep (se 1 (by rfl) ⟨484487, by rfl⟩ : syracuseStep 645983 = 968975) B968975
theorem B3103595 : Blo 428775 3103595 := bstep (se 1 (by rfl) ⟨2327696, by rfl⟩ : syracuseStep 3103595 = 4655393) B4655393
theorem B645995 : Blo 428775 645995 := bstep (se 1 (by rfl) ⟨484496, by rfl⟩ : syracuseStep 645995 = 968993) B968993
theorem B3496925 : Blo 428775 3496925 := bstep (se 3 (by rfl) ⟨655673, by rfl⟩ : syracuseStep 3496925 = 1311347) B1311347
theorem B3103763 : Blo 428775 3103763 := bstep (se 1 (by rfl) ⟨2327822, by rfl⟩ : syracuseStep 3103763 = 4655645) B4655645
theorem B646223 : Blo 428775 646223 := bstep (se 1 (by rfl) ⟨484667, by rfl⟩ : syracuseStep 646223 = 969335) B969335
theorem B613499 : Blo 428775 613499 := bstep (se 1 (by rfl) ⟨460124, by rfl⟩ : syracuseStep 613499 = 920249) B920249
theorem B482503 : Blo 428775 482503 := bstep (se 1 (by rfl) ⟨361877, by rfl⟩ : syracuseStep 482503 = 723755) B723755
theorem B646343 : Blo 428775 646343 := bstep (se 1 (by rfl) ⟨484757, by rfl⟩ : syracuseStep 646343 = 969515) B969515
theorem B3267863 : Blo 428775 3267863 := bstep (se 1 (by rfl) ⟨2450897, by rfl⟩ : syracuseStep 3267863 = 4901795) B4901795
theorem B646505 : Blo 428775 646505 := bstep (se 2 (by rfl) ⟨242439, by rfl⟩ : syracuseStep 646505 = 484879) B484879
theorem B646583 : Blo 428775 646583 := bstep (se 1 (by rfl) ⟨484937, by rfl⟩ : syracuseStep 646583 = 969875) B969875
theorem B646619 : Blo 428775 646619 := bstep (se 1 (by rfl) ⟨484964, by rfl⟩ : syracuseStep 646619 = 969929) B969929
theorem B614137 : Blo 428775 614137 := bstep (se 2 (by rfl) ⟨230301, by rfl⟩ : syracuseStep 614137 = 460603) B460603
theorem B614251 : Blo 428775 614251 := bstep (se 1 (by rfl) ⟨460688, by rfl⟩ : syracuseStep 614251 = 921377) B921377
theorem B647087 : Blo 428775 647087 := bstep (se 1 (by rfl) ⟨485315, by rfl⟩ : syracuseStep 647087 = 970631) B970631
theorem B647177 : Blo 428775 647177 := bstep (se 2 (by rfl) ⟨242691, by rfl⟩ : syracuseStep 647177 = 485383) B485383
theorem B2220047 : Blo 428775 2220047 := bstep (se 1 (by rfl) ⟨1665035, by rfl⟩ : syracuseStep 2220047 = 3330071) B3330071
theorem B483367 : Blo 428775 483367 := bstep (se 1 (by rfl) ⟨362525, by rfl⟩ : syracuseStep 483367 = 725051) B725051
theorem B647207 : Blo 428775 647207 := bstep (se 1 (by rfl) ⟨485405, by rfl⟩ : syracuseStep 647207 = 970811) B970811
theorem B614479 : Blo 428775 614479 := bstep (se 1 (by rfl) ⟨460859, by rfl⟩ : syracuseStep 614479 = 921719) B921719
theorem B647291 : Blo 428775 647291 := bstep (se 1 (by rfl) ⟨485468, by rfl⟩ : syracuseStep 647291 = 970937) B970937
theorem B3924197 : Blo 428775 3924197 := bstep (se 4 (by rfl) ⟨367893, by rfl⟩ : syracuseStep 3924197 = 735787) B735787
theorem B647417 : Blo 428775 647417 := bstep (se 2 (by rfl) ⟨242781, by rfl⟩ : syracuseStep 647417 = 485563) B485563
theorem B647519 : Blo 428775 647519 := bstep (se 1 (by rfl) ⟨485639, by rfl⟩ : syracuseStep 647519 = 971279) B971279
theorem B1958249 : Blo 428775 1958249 := bstep (se 2 (by rfl) ⟨734343, by rfl⟩ : syracuseStep 1958249 = 1468687) B1468687
theorem B581995 : Blo 428775 581995 := bstep (se 1 (by rfl) ⟨436496, by rfl⟩ : syracuseStep 581995 = 872993) B872993
theorem B647531 : Blo 428775 647531 := bstep (se 1 (by rfl) ⟨485648, by rfl⟩ : syracuseStep 647531 = 971297) B971297
theorem B2187809 : Blo 428775 2187809 := bstep (se 2 (by rfl) ⟨820428, by rfl⟩ : syracuseStep 2187809 = 1640857) B1640857
theorem B647759 : Blo 428775 647759 := bstep (se 1 (by rfl) ⟨485819, by rfl⟩ : syracuseStep 647759 = 971639) B971639
theorem B1598075 : Blo 428775 1598075 := bstep (se 1 (by rfl) ⟨1198556, by rfl⟩ : syracuseStep 1598075 = 2397113) B2397113
theorem B647879 : Blo 428775 647879 := bstep (se 1 (by rfl) ⟨485909, by rfl⟩ : syracuseStep 647879 = 971819) B971819
theorem B3269321 : Blo 428775 3269321 := bstep (se 2 (by rfl) ⟨1225995, by rfl⟩ : syracuseStep 3269321 = 2451991) B2451991
theorem B648041 : Blo 428775 648041 := bstep (se 2 (by rfl) ⟨243015, by rfl⟩ : syracuseStep 648041 = 486031) B486031
theorem B1631137 : Blo 428775 1631137 := bstep (se 2 (by rfl) ⟨611676, by rfl⟩ : syracuseStep 1631137 = 1223353) B1223353
theorem B2450351 : Blo 428775 2450351 := bstep (se 1 (by rfl) ⟨1837763, by rfl⟩ : syracuseStep 2450351 = 3675527) B3675527
theorem B648119 : Blo 428775 648119 := bstep (se 1 (by rfl) ⟨486089, by rfl⟩ : syracuseStep 648119 = 972179) B972179
theorem B648155 : Blo 428775 648155 := bstep (se 1 (by rfl) ⟨486116, by rfl⟩ : syracuseStep 648155 = 972233) B972233
theorem B3302819 : Blo 428775 3302819 := bstep (se 1 (by rfl) ⟨2477114, by rfl⟩ : syracuseStep 3302819 = 4954229) B4954229
theorem B648623 : Blo 428775 648623 := bstep (se 1 (by rfl) ⟨486467, by rfl⟩ : syracuseStep 648623 = 972935) B972935
theorem B615863 : Blo 428775 615863 := bstep (se 1 (by rfl) ⟨461897, by rfl⟩ : syracuseStep 615863 = 923795) B923795
theorem B648713 : Blo 428775 648713 := bstep (se 2 (by rfl) ⟨243267, by rfl⟩ : syracuseStep 648713 = 486535) B486535
theorem B648743 : Blo 428775 648743 := bstep (se 1 (by rfl) ⟨486557, by rfl⟩ : syracuseStep 648743 = 973115) B973115
theorem B484987 : Blo 428775 484987 := bstep (se 1 (by rfl) ⟨363740, by rfl⟩ : syracuseStep 484987 = 727481) B727481
theorem B648827 : Blo 428775 648827 := bstep (se 1 (by rfl) ⟨486620, by rfl⟩ : syracuseStep 648827 = 973241) B973241
theorem B1238777 : Blo 428775 1238777 := bstep (se 2 (by rfl) ⟨464541, by rfl⟩ : syracuseStep 1238777 = 929083) B929083
theorem B648953 : Blo 428775 648953 := bstep (se 2 (by rfl) ⟨243357, by rfl⟩ : syracuseStep 648953 = 486715) B486715
theorem B1632095 : Blo 428775 1632095 := bstep (se 1 (by rfl) ⟨1224071, by rfl⟩ : syracuseStep 1632095 = 2448143) B2448143
theorem B649055 : Blo 428775 649055 := bstep (se 1 (by rfl) ⟨486791, by rfl⟩ : syracuseStep 649055 = 973583) B973583
theorem B649067 : Blo 428775 649067 := bstep (se 1 (by rfl) ⟨486800, by rfl⟩ : syracuseStep 649067 = 973601) B973601
theorem B1632109 : Blo 428775 1632109 := bstep (se 3 (by rfl) ⟨306020, by rfl⟩ : syracuseStep 1632109 = 612041) B612041
theorem B3532679 : Blo 428775 3532679 := bstep (se 1 (by rfl) ⟨2649509, by rfl⟩ : syracuseStep 3532679 = 5299019) B5299019
theorem B485455 : Blo 428775 485455 := bstep (se 1 (by rfl) ⟨364091, by rfl⟩ : syracuseStep 485455 = 728183) B728183
theorem B1271965 : Blo 428775 1271965 := bstep (se 3 (by rfl) ⟨238493, by rfl⟩ : syracuseStep 1271965 = 476987) B476987
theorem B1632413 : Blo 428775 1632413 := bstep (se 3 (by rfl) ⟨306077, by rfl⟩ : syracuseStep 1632413 = 612155) B612155
theorem B584119 : Blo 428775 584119 := bstep (se 1 (by rfl) ⟨438089, by rfl⟩ : syracuseStep 584119 = 876179) B876179
theorem B485851 : Blo 428775 485851 := bstep (se 1 (by rfl) ⟨364388, by rfl⟩ : syracuseStep 485851 = 728777) B728777
theorem B1633067 : Blo 428775 1633067 := bstep (se 1 (by rfl) ⟨1224800, by rfl⟩ : syracuseStep 1633067 = 2449601) B2449601
theorem B5532563 : Blo 428775 5532563 := bstep (se 1 (by rfl) ⟨4149422, by rfl⟩ : syracuseStep 5532563 = 8298845) B8298845
theorem B486319 : Blo 428775 486319 := bstep (se 1 (by rfl) ⟨364739, by rfl⟩ : syracuseStep 486319 = 729479) B729479
theorem B814043 : Blo 428775 814043 := bstep (se 1 (by rfl) ⟨610532, by rfl⟩ : syracuseStep 814043 = 1221065) B1221065
theorem B2616371 : Blo 428775 2616371 := bstep (se 1 (by rfl) ⟨1962278, by rfl⟩ : syracuseStep 2616371 = 3924557) B3924557
theorem B486751 : Blo 428775 486751 := bstep (se 1 (by rfl) ⟨365063, by rfl⟩ : syracuseStep 486751 = 730127) B730127
theorem B2190887 : Blo 428775 2190887 := bstep (se 1 (by rfl) ⟨1643165, by rfl⟩ : syracuseStep 2190887 = 3286331) B3286331
theorem B7892603 : Blo 428775 7892603 := bstep (se 1 (by rfl) ⟨5919452, by rfl⟩ : syracuseStep 7892603 = 11838905) B11838905
theorem B1306631 : Blo 428775 1306631 := bstep (se 1 (by rfl) ⟨979973, by rfl⟩ : syracuseStep 1306631 = 1959947) B1959947
theorem B815113 : Blo 428775 815113 := bstep (se 2 (by rfl) ⟨305667, by rfl⟩ : syracuseStep 815113 = 611335) B611335
theorem B4649075 : Blo 428775 4649075 := bstep (se 1 (by rfl) ⟨3486806, by rfl⟩ : syracuseStep 4649075 = 6973613) B6973613
theorem B5501195 : Blo 428775 5501195 := bstep (se 1 (by rfl) ⟨4125896, by rfl⟩ : syracuseStep 5501195 = 8251793) B8251793
theorem B1864225 : Blo 428775 1864225 := bstep (se 2 (by rfl) ⟨699084, by rfl⟩ : syracuseStep 1864225 = 1398169) B1398169
theorem B1635025 : Blo 428775 1635025 := bstep (se 2 (by rfl) ⟨613134, by rfl⟩ : syracuseStep 1635025 = 1226269) B1226269
theorem B5239505 : Blo 428775 5239505 := bstep (se 2 (by rfl) ⟨1964814, by rfl⟩ : syracuseStep 5239505 = 3929629) B3929629
theorem B815827 : Blo 428775 815827 := bstep (se 1 (by rfl) ⟨611870, by rfl⟩ : syracuseStep 815827 = 1223741) B1223741
theorem B2618219 : Blo 428775 2618219 := bstep (se 1 (by rfl) ⟨1963664, by rfl⟩ : syracuseStep 2618219 = 3927329) B3927329
theorem B1635329 : Blo 428775 1635329 := bstep (se 2 (by rfl) ⟨613248, by rfl⟩ : syracuseStep 1635329 = 1226497) B1226497
theorem B3306539 : Blo 428775 3306539 := bstep (se 1 (by rfl) ⟨2479904, by rfl⟩ : syracuseStep 3306539 = 4959809) B4959809
theorem B783607 : Blo 428775 783607 := bstep (se 1 (by rfl) ⟨587705, by rfl⟩ : syracuseStep 783607 = 1175411) B1175411
theorem B816571 : Blo 428775 816571 := bstep (se 1 (by rfl) ⟨612428, by rfl⟩ : syracuseStep 816571 = 1224857) B1224857
theorem B1635785 : Blo 428775 1635785 := bstep (se 2 (by rfl) ⟨613419, by rfl⟩ : syracuseStep 1635785 = 1226839) B1226839
theorem B6190577 : Blo 428775 6190577 := bstep (se 2 (by rfl) ⟨2321466, by rfl⟩ : syracuseStep 6190577 = 4642933) B4642933
theorem B817057 : Blo 428775 817057 := bstep (se 2 (by rfl) ⟨306396, by rfl⟩ : syracuseStep 817057 = 612793) B612793
theorem B1636271 : Blo 428775 1636271 := bstep (se 1 (by rfl) ⟨1227203, by rfl⟩ : syracuseStep 1636271 = 2454407) B2454407
theorem B8976541 : Blo 428775 8976541 := bstep (se 3 (by rfl) ⟨1683101, by rfl⟩ : syracuseStep 8976541 = 3366203) B3366203
theorem B4913459 : Blo 428775 4913459 := bstep (se 1 (by rfl) ⟨3685094, by rfl⟩ : syracuseStep 4913459 = 7370189) B7370189
theorem B6977897 : Blo 428775 6977897 := bstep (se 2 (by rfl) ⟨2616711, by rfl⟩ : syracuseStep 6977897 = 5233423) B5233423
theorem B817627 : Blo 428775 817627 := bstep (se 1 (by rfl) ⟨613220, by rfl⟩ : syracuseStep 817627 = 1226441) B1226441
theorem B916319 : Blo 428775 916319 := bstep (se 1 (by rfl) ⟨687239, by rfl⟩ : syracuseStep 916319 = 1374479) B1374479
theorem B687035 : Blo 428775 687035 := bstep (se 1 (by rfl) ⟨515276, by rfl⟩ : syracuseStep 687035 = 1030553) B1030553
theorem B1637455 : Blo 428775 1637455 := bstep (se 1 (by rfl) ⟨1228091, by rfl⟩ : syracuseStep 1637455 = 2456183) B2456183
theorem B3669239 : Blo 428775 3669239 := bstep (se 1 (by rfl) ⟨2751929, by rfl⟩ : syracuseStep 3669239 = 5503859) B5503859
theorem B181140941 : Blo 428775 181140941 := bstep (se 3 (by rfl) ⟨33963926, by rfl⟩ : syracuseStep 181140941 = 67927853) B67927853
theorem B1834483 : Blo 428775 1834483 := bstep (se 1 (by rfl) ⟨1375862, by rfl⟩ : syracuseStep 1834483 = 2751725) B2751725
theorem B1637927 : Blo 428775 1637927 := bstep (se 1 (by rfl) ⟨1228445, by rfl⟩ : syracuseStep 1637927 = 2456891) B2456891
theorem B3276611 : Blo 428775 3276611 := bstep (se 1 (by rfl) ⟨2457458, by rfl⟩ : syracuseStep 3276611 = 4914917) B4914917
theorem B1376119 : Blo 428775 1376119 := bstep (se 1 (by rfl) ⟨1032089, by rfl⟩ : syracuseStep 1376119 = 2064179) B2064179
theorem B819305 : Blo 428775 819305 := bstep (se 2 (by rfl) ⟨307239, by rfl⟩ : syracuseStep 819305 = 614479) B614479
theorem B4718999 : Blo 428775 4718999 := bstep (se 1 (by rfl) ⟨3539249, by rfl⟩ : syracuseStep 4718999 = 7078499) B7078499
theorem B1638913 : Blo 428775 1638913 := bstep (se 2 (by rfl) ⟨614592, by rfl⟩ : syracuseStep 1638913 = 1229185) B1229185
theorem B1376939 : Blo 428775 1376939 := bstep (se 1 (by rfl) ⟨1032704, by rfl⟩ : syracuseStep 1376939 = 2065409) B2065409
theorem B918191 : Blo 428775 918191 := bstep (se 1 (by rfl) ⟨688643, by rfl⟩ : syracuseStep 918191 = 1377287) B1377287
theorem B3670879 : Blo 428775 3670879 := bstep (se 1 (by rfl) ⟨2753159, by rfl⟩ : syracuseStep 3670879 = 5506319) B5506319
theorem B1835885 : Blo 428775 1835885 := bstep (se 3 (by rfl) ⟨344228, by rfl⟩ : syracuseStep 1835885 = 688457) B688457
theorem B1639399 : Blo 428775 1639399 := bstep (se 1 (by rfl) ⟨1229549, by rfl⟩ : syracuseStep 1639399 = 2459099) B2459099
theorem B1639673 : Blo 428775 1639673 := bstep (se 2 (by rfl) ⟨614877, by rfl⟩ : syracuseStep 1639673 = 1229755) B1229755
theorem B1049951 : Blo 428775 1049951 := bstep (se 1 (by rfl) ⟨787463, by rfl⟩ : syracuseStep 1049951 = 1574927) B1574927
theorem B1246603 : Blo 428775 1246603 := bstep (se 1 (by rfl) ⟨934952, by rfl⟩ : syracuseStep 1246603 = 1869905) B1869905
theorem B493051 : Blo 428775 493051 := bstep (se 1 (by rfl) ⟨369788, by rfl⟩ : syracuseStep 493051 = 739577) B739577
theorem B11142947 : Blo 428775 11142947 := bstep (se 1 (by rfl) ⟨8357210, by rfl⟩ : syracuseStep 11142947 = 16714421) B16714421
theorem B3279041 : Blo 428775 3279041 := bstep (se 2 (by rfl) ⟨1229640, by rfl⟩ : syracuseStep 3279041 = 2459281) B2459281
theorem B2984359 : Blo 428775 2984359 := bstep (se 1 (by rfl) ⟨2238269, by rfl⟩ : syracuseStep 2984359 = 4476539) B4476539
theorem B2460239 : Blo 428775 2460239 := bstep (se 1 (by rfl) ⟨1845179, by rfl⟩ : syracuseStep 2460239 = 3690359) B3690359
theorem B8817437 : Blo 428775 8817437 := bstep (se 3 (by rfl) ⟨1653269, by rfl⟩ : syracuseStep 8817437 = 3306539) B3306539
theorem B428847 : Blo 428775 428847 := bstep (se 1 (by rfl) ⟨321635, by rfl⟩ : syracuseStep 428847 = 643271) B643271
theorem B428955 : Blo 428775 428955 := bstep (se 1 (by rfl) ⟨321716, by rfl⟩ : syracuseStep 428955 = 643433) B643433
theorem B723883 : Blo 428775 723883 := bstep (se 1 (by rfl) ⟨542912, by rfl⟩ : syracuseStep 723883 = 1085825) B1085825
theorem B429007 : Blo 428775 429007 := bstep (se 1 (by rfl) ⟨321755, by rfl⟩ : syracuseStep 429007 = 643511) B643511
theorem B429031 : Blo 428775 429031 := bstep (se 1 (by rfl) ⟨321773, by rfl⟩ : syracuseStep 429031 = 643547) B643547
theorem B36211799 : Blo 428775 36211799 := bstep (se 1 (by rfl) ⟨27158849, by rfl⟩ : syracuseStep 36211799 = 54317699) B54317699
theorem B724187 : Blo 428775 724187 := bstep (se 1 (by rfl) ⟨543140, by rfl⟩ : syracuseStep 724187 = 1086281) B1086281
theorem B429343 : Blo 428775 429343 := bstep (se 1 (by rfl) ⟨322007, by rfl⟩ : syracuseStep 429343 = 644015) B644015
theorem B429403 : Blo 428775 429403 := bstep (se 1 (by rfl) ⟨322052, by rfl⟩ : syracuseStep 429403 = 644105) B644105
theorem B429423 : Blo 428775 429423 := bstep (se 1 (by rfl) ⟨322067, by rfl⟩ : syracuseStep 429423 = 644135) B644135
theorem B429479 : Blo 428775 429479 := bstep (se 1 (by rfl) ⟨322109, by rfl⟩ : syracuseStep 429479 = 644219) B644219
theorem B724423 : Blo 428775 724423 := bstep (se 1 (by rfl) ⟨543317, by rfl⟩ : syracuseStep 724423 = 1086635) B1086635
theorem B429563 : Blo 428775 429563 := bstep (se 1 (by rfl) ⟨322172, by rfl⟩ : syracuseStep 429563 = 644345) B644345
theorem B429631 : Blo 428775 429631 := bstep (se 1 (by rfl) ⟨322223, by rfl⟩ : syracuseStep 429631 = 644447) B644447
theorem B429639 : Blo 428775 429639 := bstep (se 1 (by rfl) ⟨322229, by rfl⟩ : syracuseStep 429639 = 644459) B644459
theorem B429791 : Blo 428775 429791 := bstep (se 1 (by rfl) ⟨322343, by rfl⟩ : syracuseStep 429791 = 644687) B644687
theorem B429871 : Blo 428775 429871 := bstep (se 1 (by rfl) ⟨322403, by rfl⟩ : syracuseStep 429871 = 644807) B644807
theorem B1642301 : Blo 428775 1642301 := bstep (se 3 (by rfl) ⟨307931, by rfl⟩ : syracuseStep 1642301 = 615863) B615863
theorem B429979 : Blo 428775 429979 := bstep (se 1 (by rfl) ⟨322484, by rfl⟩ : syracuseStep 429979 = 644969) B644969
theorem B724943 : Blo 428775 724943 := bstep (se 1 (by rfl) ⟨543707, by rfl⟩ : syracuseStep 724943 = 1087415) B1087415
theorem B430031 : Blo 428775 430031 := bstep (se 1 (by rfl) ⟨322523, by rfl⟩ : syracuseStep 430031 = 645047) B645047
theorem B430055 : Blo 428775 430055 := bstep (se 1 (by rfl) ⟨322541, by rfl⟩ : syracuseStep 430055 = 645083) B645083
theorem B2461697 : Blo 428775 2461697 := bstep (se 2 (by rfl) ⟨923136, by rfl⟩ : syracuseStep 2461697 = 1846273) B1846273
theorem B2494667 : Blo 428775 2494667 := bstep (se 1 (by rfl) ⟨1871000, by rfl⟩ : syracuseStep 2494667 = 3742001) B3742001
theorem B5902595 : Blo 428775 5902595 := bstep (se 1 (by rfl) ⟨4426946, by rfl⟩ : syracuseStep 5902595 = 8853893) B8853893
theorem B430367 : Blo 428775 430367 := bstep (se 1 (by rfl) ⟨322775, by rfl⟩ : syracuseStep 430367 = 645551) B645551
theorem B430427 : Blo 428775 430427 := bstep (se 1 (by rfl) ⟨322820, by rfl⟩ : syracuseStep 430427 = 645641) B645641
theorem B430447 : Blo 428775 430447 := bstep (se 1 (by rfl) ⟨322835, by rfl⟩ : syracuseStep 430447 = 645671) B645671
theorem B430503 : Blo 428775 430503 := bstep (se 1 (by rfl) ⟨322877, by rfl⟩ : syracuseStep 430503 = 645755) B645755
theorem B430587 : Blo 428775 430587 := bstep (se 1 (by rfl) ⟨322940, by rfl⟩ : syracuseStep 430587 = 645881) B645881
theorem B2331155 : Blo 428775 2331155 := bstep (se 1 (by rfl) ⟨1748366, by rfl⟩ : syracuseStep 2331155 = 3496733) B3496733
theorem B430655 : Blo 428775 430655 := bstep (se 1 (by rfl) ⟨322991, by rfl⟩ : syracuseStep 430655 = 645983) B645983
theorem B2069063 : Blo 428775 2069063 := bstep (se 1 (by rfl) ⟨1551797, by rfl⟩ : syracuseStep 2069063 = 3103595) B3103595
theorem B430663 : Blo 428775 430663 := bstep (se 1 (by rfl) ⟨322997, by rfl⟩ : syracuseStep 430663 = 645995) B645995
theorem B725611 : Blo 428775 725611 := bstep (se 1 (by rfl) ⟨544208, by rfl⟩ : syracuseStep 725611 = 1088417) B1088417
theorem B2331283 : Blo 428775 2331283 := bstep (se 1 (by rfl) ⟨1748462, by rfl⟩ : syracuseStep 2331283 = 3496925) B3496925
theorem B430815 : Blo 428775 430815 := bstep (se 1 (by rfl) ⟨323111, by rfl⟩ : syracuseStep 430815 = 646223) B646223
theorem B430895 : Blo 428775 430895 := bstep (se 1 (by rfl) ⟨323171, by rfl⟩ : syracuseStep 430895 = 646343) B646343
theorem B725915 : Blo 428775 725915 := bstep (se 1 (by rfl) ⟨544436, by rfl⟩ : syracuseStep 725915 = 1088873) B1088873
theorem B431003 : Blo 428775 431003 := bstep (se 1 (by rfl) ⟨323252, by rfl⟩ : syracuseStep 431003 = 646505) B646505
theorem B8852429 : Blo 428775 8852429 := bstep (se 3 (by rfl) ⟨1659830, by rfl⟩ : syracuseStep 8852429 = 3319661) B3319661
theorem B431055 : Blo 428775 431055 := bstep (se 1 (by rfl) ⟨323291, by rfl⟩ : syracuseStep 431055 = 646583) B646583
theorem B431079 : Blo 428775 431079 := bstep (se 1 (by rfl) ⟨323309, by rfl⟩ : syracuseStep 431079 = 646619) B646619
theorem B35493065 : Blo 428775 35493065 := bstep (se 2 (by rfl) ⟨13309899, by rfl⟩ : syracuseStep 35493065 = 26619799) B26619799
theorem B1447145 : Blo 428775 1447145 := bstep (se 2 (by rfl) ⟨542679, by rfl⟩ : syracuseStep 1447145 = 1085359) B1085359
theorem B431391 : Blo 428775 431391 := bstep (se 1 (by rfl) ⟨323543, by rfl⟩ : syracuseStep 431391 = 647087) B647087
theorem B431451 : Blo 428775 431451 := bstep (se 1 (by rfl) ⟨323588, by rfl⟩ : syracuseStep 431451 = 647177) B647177
theorem B1086817 : Blo 428775 1086817 := bstep (se 2 (by rfl) ⟨407556, by rfl⟩ : syracuseStep 1086817 = 815113) B815113
theorem B1480031 : Blo 428775 1480031 := bstep (se 1 (by rfl) ⟨1110023, by rfl⟩ : syracuseStep 1480031 = 2220047) B2220047
theorem B431471 : Blo 428775 431471 := bstep (se 1 (by rfl) ⟨323603, by rfl⟩ : syracuseStep 431471 = 647207) B647207
theorem B923017 : Blo 428775 923017 := bstep (se 2 (by rfl) ⟨346131, by rfl⟩ : syracuseStep 923017 = 692263) B692263
theorem B1447307 : Blo 428775 1447307 := bstep (se 1 (by rfl) ⟨1085480, by rfl⟩ : syracuseStep 1447307 = 2170961) B2170961
theorem B431527 : Blo 428775 431527 := bstep (se 1 (by rfl) ⟨323645, by rfl⟩ : syracuseStep 431527 = 647291) B647291
theorem B431611 : Blo 428775 431611 := bstep (se 1 (by rfl) ⟨323708, by rfl⟩ : syracuseStep 431611 = 647417) B647417
theorem B431679 : Blo 428775 431679 := bstep (se 1 (by rfl) ⟨323759, by rfl⟩ : syracuseStep 431679 = 647519) B647519
theorem B431687 : Blo 428775 431687 := bstep (se 1 (by rfl) ⟨323765, by rfl⟩ : syracuseStep 431687 = 647531) B647531
theorem B431839 : Blo 428775 431839 := bstep (se 1 (by rfl) ⟨323879, by rfl⟩ : syracuseStep 431839 = 647759) B647759
theorem B431919 : Blo 428775 431919 := bstep (se 1 (by rfl) ⟨323939, by rfl⟩ : syracuseStep 431919 = 647879) B647879
theorem B432027 : Blo 428775 432027 := bstep (se 1 (by rfl) ⟨324020, by rfl⟩ : syracuseStep 432027 = 648041) B648041
theorem B432079 : Blo 428775 432079 := bstep (se 1 (by rfl) ⟨324059, by rfl⟩ : syracuseStep 432079 = 648119) B648119
theorem B432103 : Blo 428775 432103 := bstep (se 1 (by rfl) ⟨324077, by rfl⟩ : syracuseStep 432103 = 648155) B648155
theorem B2201879 : Blo 428775 2201879 := bstep (se 1 (by rfl) ⟨1651409, by rfl⟩ : syracuseStep 2201879 = 3302819) B3302819
theorem B1087769 : Blo 428775 1087769 := bstep (se 2 (by rfl) ⟨407913, by rfl⟩ : syracuseStep 1087769 = 815827) B815827
theorem B432415 : Blo 428775 432415 := bstep (se 1 (by rfl) ⟨324311, by rfl⟩ : syracuseStep 432415 = 648623) B648623
theorem B432475 : Blo 428775 432475 := bstep (se 1 (by rfl) ⟨324356, by rfl⟩ : syracuseStep 432475 = 648713) B648713
theorem B432495 : Blo 428775 432495 := bstep (se 1 (by rfl) ⟨324371, by rfl⟩ : syracuseStep 432495 = 648743) B648743
theorem B1841575 : Blo 428775 1841575 := bstep (se 1 (by rfl) ⟨1381181, by rfl⟩ : syracuseStep 1841575 = 2762363) B2762363
theorem B432551 : Blo 428775 432551 := bstep (se 1 (by rfl) ⟨324413, by rfl⟩ : syracuseStep 432551 = 648827) B648827
theorem B1841591 : Blo 428775 1841591 := bstep (se 1 (by rfl) ⟨1381193, by rfl⟩ : syracuseStep 1841591 = 2762387) B2762387
theorem B825851 : Blo 428775 825851 := bstep (se 1 (by rfl) ⟨619388, by rfl⟩ : syracuseStep 825851 = 1238777) B1238777
theorem B432635 : Blo 428775 432635 := bstep (se 1 (by rfl) ⟨324476, by rfl⟩ : syracuseStep 432635 = 648953) B648953
theorem B1088063 : Blo 428775 1088063 := bstep (se 1 (by rfl) ⟨816047, by rfl⟩ : syracuseStep 1088063 = 1632095) B1632095
theorem B432703 : Blo 428775 432703 := bstep (se 1 (by rfl) ⟨324527, by rfl⟩ : syracuseStep 432703 = 649055) B649055
theorem B432711 : Blo 428775 432711 := bstep (se 1 (by rfl) ⟨324533, by rfl⟩ : syracuseStep 432711 = 649067) B649067
theorem B5905003 : Blo 428775 5905003 := bstep (se 1 (by rfl) ⟨4428752, by rfl⟩ : syracuseStep 5905003 = 8857505) B8857505
theorem B1088275 : Blo 428775 1088275 := bstep (se 1 (by rfl) ⟨816206, by rfl⟩ : syracuseStep 1088275 = 1632413) B1632413
theorem B1088711 : Blo 428775 1088711 := bstep (se 1 (by rfl) ⟨816533, by rfl⟩ : syracuseStep 1088711 = 1633067) B1633067
theorem B1088761 : Blo 428775 1088761 := bstep (se 2 (by rfl) ⟨408285, by rfl⟩ : syracuseStep 1088761 = 816571) B816571
theorem B1744247 : Blo 428775 1744247 := bstep (se 1 (by rfl) ⟨1308185, by rfl⟩ : syracuseStep 1744247 = 2616371) B2616371
theorem B4136507 : Blo 428775 4136507 := bstep (se 1 (by rfl) ⟨3102380, by rfl⟩ : syracuseStep 4136507 = 6204761) B6204761
theorem B1089409 : Blo 428775 1089409 := bstep (se 2 (by rfl) ⟨408528, by rfl⟩ : syracuseStep 1089409 = 817057) B817057
theorem B2170799 : Blo 428775 2170799 := bstep (se 1 (by rfl) ⟨1628099, by rfl⟩ : syracuseStep 2170799 = 3256199) B3256199
theorem B11968721 : Blo 428775 11968721 := bstep (se 2 (by rfl) ⟨4488270, by rfl⟩ : syracuseStep 11968721 = 8976541) B8976541
theorem B1450331 : Blo 428775 1450331 := bstep (se 1 (by rfl) ⟨1087748, by rfl⟩ : syracuseStep 1450331 = 2175497) B2175497
theorem B2368001 : Blo 428775 2368001 := bstep (se 2 (by rfl) ⟨888000, by rfl⟩ : syracuseStep 2368001 = 1776001) B1776001
theorem B1745479 : Blo 428775 1745479 := bstep (se 1 (by rfl) ⟨1309109, by rfl⟩ : syracuseStep 1745479 = 2618219) B2618219
theorem B1090169 : Blo 428775 1090169 := bstep (se 2 (by rfl) ⟨408813, by rfl⟩ : syracuseStep 1090169 = 817627) B817627
theorem B2761361 : Blo 428775 2761361 := bstep (se 2 (by rfl) ⟨1035510, by rfl⟩ : syracuseStep 2761361 = 2071021) B2071021
theorem B1090219 : Blo 428775 1090219 := bstep (se 1 (by rfl) ⟨817664, by rfl⟩ : syracuseStep 1090219 = 1635329) B1635329
theorem B729823 : Blo 428775 729823 := bstep (se 1 (by rfl) ⟨547367, by rfl⟩ : syracuseStep 729823 = 1094735) B1094735
theorem B4203323 : Blo 428775 4203323 := bstep (se 1 (by rfl) ⟨3152492, by rfl⟩ : syracuseStep 4203323 = 6304985) B6304985
theorem B1090523 : Blo 428775 1090523 := bstep (se 1 (by rfl) ⟨817892, by rfl⟩ : syracuseStep 1090523 = 1635785) B1635785
theorem B730255 : Blo 428775 730255 := bstep (se 1 (by rfl) ⟨547691, by rfl⟩ : syracuseStep 730255 = 1095383) B1095383
theorem B1090847 : Blo 428775 1090847 := bstep (se 1 (by rfl) ⟨818135, by rfl⟩ : syracuseStep 1090847 = 1636271) B1636271
theorem B1451303 : Blo 428775 1451303 := bstep (se 1 (by rfl) ⟨1088477, by rfl⟩ : syracuseStep 1451303 = 2176955) B2176955
theorem B2631257 : Blo 428775 2631257 := bstep (se 2 (by rfl) ⟨986721, by rfl⟩ : syracuseStep 2631257 = 1973443) B1973443
theorem B3679901 : Blo 428775 3679901 := bstep (se 3 (by rfl) ⟨689981, by rfl⟩ : syracuseStep 3679901 = 1379963) B1379963
theorem B1845281 : Blo 428775 1845281 := bstep (se 2 (by rfl) ⟨691980, by rfl⟩ : syracuseStep 1845281 = 1383961) B1383961
theorem B1452167 : Blo 428775 1452167 := bstep (se 1 (by rfl) ⟨1089125, by rfl⟩ : syracuseStep 1452167 = 2178251) B2178251
theorem B4434097 : Blo 428775 4434097 := bstep (se 2 (by rfl) ⟨1662786, by rfl⟩ : syracuseStep 4434097 = 3325573) B3325573
theorem B2369801 : Blo 428775 2369801 := bstep (se 2 (by rfl) ⟨888675, by rfl⟩ : syracuseStep 2369801 = 1777351) B1777351
theorem B120760627 : Blo 428775 120760627 := bstep (se 1 (by rfl) ⟨90570470, by rfl⟩ : syracuseStep 120760627 = 181140941) B181140941
theorem B1091951 : Blo 428775 1091951 := bstep (se 1 (by rfl) ⟨818963, by rfl⟩ : syracuseStep 1091951 = 1637927) B1637927
theorem B1845949 : Blo 428775 1845949 := bstep (se 3 (by rfl) ⟨346115, by rfl⟩ : syracuseStep 1845949 = 692231) B692231
theorem B2173715 : Blo 428775 2173715 := bstep (se 1 (by rfl) ⟨1630286, by rfl⟩ : syracuseStep 2173715 = 3260573) B3260573
theorem B1092599 : Blo 428775 1092599 := bstep (se 1 (by rfl) ⟨819449, by rfl⟩ : syracuseStep 1092599 = 1638899) B1638899
theorem B2075867 : Blo 428775 2075867 := bstep (se 1 (by rfl) ⟨1556900, by rfl⟩ : syracuseStep 2075867 = 3113801) B3113801
theorem B1453409 : Blo 428775 1453409 := bstep (se 2 (by rfl) ⟨545028, by rfl⟩ : syracuseStep 1453409 = 1090057) B1090057
theorem B4140811 : Blo 428775 4140811 := bstep (se 1 (by rfl) ⟨3105608, by rfl⟩ : syracuseStep 4140811 = 6211217) B6211217
theorem B2174849 : Blo 428775 2174849 := bstep (se 2 (by rfl) ⟨815568, by rfl⟩ : syracuseStep 2174849 = 1631137) B1631137
theorem B3682361 : Blo 428775 3682361 := bstep (se 2 (by rfl) ⟨1380885, by rfl⟩ : syracuseStep 3682361 = 2761771) B2761771
theorem B13972013 : Blo 428775 13972013 := bstep (se 3 (by rfl) ⟨2619752, by rfl⟩ : syracuseStep 13972013 = 5239505) B5239505
theorem B1847879 : Blo 428775 1847879 := bstep (se 1 (by rfl) ⟨1385909, by rfl⟩ : syracuseStep 1847879 = 2771819) B2771819
theorem B2175659 : Blo 428775 2175659 := bstep (se 1 (by rfl) ⟨1631744, by rfl⟩ : syracuseStep 2175659 = 3263489) B3263489
theorem B1225439 : Blo 428775 1225439 := bstep (se 1 (by rfl) ⟨919079, by rfl⟩ : syracuseStep 1225439 = 1838159) B1838159
theorem B1094543 : Blo 428775 1094543 := bstep (se 1 (by rfl) ⟨820907, by rfl⟩ : syracuseStep 1094543 = 1641815) B1641815
theorem B2339777 : Blo 428775 2339777 := bstep (se 2 (by rfl) ⟨877416, by rfl⟩ : syracuseStep 2339777 = 1754833) B1754833
theorem B1160183 : Blo 428775 1160183 := bstep (se 1 (by rfl) ⟨870137, by rfl⟩ : syracuseStep 1160183 = 1740275) B1740275
theorem B2176145 : Blo 428775 2176145 := bstep (se 2 (by rfl) ⟨816054, by rfl⟩ : syracuseStep 2176145 = 1632109) B1632109
theorem B1455353 : Blo 428775 1455353 := bstep (se 2 (by rfl) ⟨545757, by rfl⟩ : syracuseStep 1455353 = 1091515) B1091515
theorem B1455623 : Blo 428775 1455623 := bstep (se 1 (by rfl) ⟨1091717, by rfl⟩ : syracuseStep 1455623 = 2183435) B2183435
theorem B1095403 : Blo 428775 1095403 := bstep (se 1 (by rfl) ⟨821552, by rfl⟩ : syracuseStep 1095403 = 1643105) B1643105
theorem B3192605 : Blo 428775 3192605 := bstep (se 3 (by rfl) ⟨598613, by rfl⟩ : syracuseStep 3192605 = 1197227) B1197227
theorem B1161017 : Blo 428775 1161017 := bstep (se 2 (by rfl) ⟨435381, by rfl⟩ : syracuseStep 1161017 = 870763) B870763
theorem B1456595 : Blo 428775 1456595 := bstep (se 1 (by rfl) ⟨1092446, by rfl⟩ : syracuseStep 1456595 = 2184893) B2184893
theorem B1456703 : Blo 428775 1456703 := bstep (se 1 (by rfl) ⟨1092527, by rfl⟩ : syracuseStep 1456703 = 2185055) B2185055
theorem B965303 : Blo 428775 965303 := bstep (se 1 (by rfl) ⟨723977, by rfl⟩ : syracuseStep 965303 = 1447955) B1447955
theorem B965519 : Blo 428775 965519 := bstep (se 1 (by rfl) ⟨724139, by rfl⟩ : syracuseStep 965519 = 1448279) B1448279
theorem B1227899 : Blo 428775 1227899 := bstep (se 1 (by rfl) ⟨920924, by rfl⟩ : syracuseStep 1227899 = 1841849) B1841849
theorem B1686815 : Blo 428775 1686815 := bstep (se 1 (by rfl) ⟨1265111, by rfl⟩ : syracuseStep 1686815 = 2530223) B2530223
theorem B5291513 : Blo 428775 5291513 := bstep (se 2 (by rfl) ⟨1984317, by rfl⟩ : syracuseStep 5291513 = 3968635) B3968635
theorem B1031687 : Blo 428775 1031687 := bstep (se 1 (by rfl) ⟨773765, by rfl⟩ : syracuseStep 1031687 = 1547531) B1547531
theorem B2178575 : Blo 428775 2178575 := bstep (se 1 (by rfl) ⟨1633931, by rfl⟩ : syracuseStep 2178575 = 3267863) B3267863
theorem B966239 : Blo 428775 966239 := bstep (se 1 (by rfl) ⟨724679, by rfl⟩ : syracuseStep 966239 = 1449359) B1449359
theorem B966455 : Blo 428775 966455 := bstep (se 1 (by rfl) ⟨724841, by rfl⟩ : syracuseStep 966455 = 1449683) B1449683
theorem B3915649 : Blo 428775 3915649 := bstep (se 2 (by rfl) ⟨1468368, by rfl⟩ : syracuseStep 3915649 = 2936737) B2936737
theorem B4636577 : Blo 428775 4636577 := bstep (se 2 (by rfl) ⟨1738716, by rfl⟩ : syracuseStep 4636577 = 3477433) B3477433
theorem B5521445 : Blo 428775 5521445 := bstep (se 4 (by rfl) ⟨517635, by rfl⟩ : syracuseStep 5521445 = 1035271) B1035271
theorem B966761 : Blo 428775 966761 := bstep (se 2 (by rfl) ⟨362535, by rfl⟩ : syracuseStep 966761 = 725071) B725071
theorem B1458539 : Blo 428775 1458539 := bstep (se 1 (by rfl) ⟨1093904, by rfl⟩ : syracuseStep 1458539 = 2187809) B2187809
theorem B1065383 : Blo 428775 1065383 := bstep (se 1 (by rfl) ⟨799037, by rfl⟩ : syracuseStep 1065383 = 1598075) B1598075
theorem B1229231 : Blo 428775 1229231 := bstep (se 1 (by rfl) ⟨921923, by rfl⟩ : syracuseStep 1229231 = 1843847) B1843847
theorem B2179547 : Blo 428775 2179547 := bstep (se 1 (by rfl) ⟨1634660, by rfl⟩ : syracuseStep 2179547 = 3269321) B3269321
theorem B967247 : Blo 428775 967247 := bstep (se 1 (by rfl) ⟨725435, by rfl⟩ : syracuseStep 967247 = 1450871) B1450871
theorem B1458809 : Blo 428775 1458809 := bstep (se 2 (by rfl) ⟨547053, by rfl⟩ : syracuseStep 1458809 = 1094107) B1094107
theorem B967391 : Blo 428775 967391 := bstep (se 1 (by rfl) ⟨725543, by rfl⟩ : syracuseStep 967391 = 1451087) B1451087
theorem B2180033 : Blo 428775 2180033 := bstep (se 2 (by rfl) ⟨817512, by rfl⟩ : syracuseStep 2180033 = 1635025) B1635025
theorem B967643 : Blo 428775 967643 := bstep (se 1 (by rfl) ⟨725732, by rfl⟩ : syracuseStep 967643 = 1451465) B1451465
theorem B967823 : Blo 428775 967823 := bstep (se 1 (by rfl) ⟨725867, by rfl⟩ : syracuseStep 967823 = 1451735) B1451735
theorem B1164431 : Blo 428775 1164431 := bstep (se 1 (by rfl) ⟨873323, by rfl⟩ : syracuseStep 1164431 = 1746647) B1746647
theorem B1033435 : Blo 428775 1033435 := bstep (se 1 (by rfl) ⟨775076, by rfl⟩ : syracuseStep 1033435 = 1550153) B1550153
theorem B967913 : Blo 428775 967913 := bstep (se 2 (by rfl) ⟨362967, by rfl⟩ : syracuseStep 967913 = 725935) B725935
theorem B967967 : Blo 428775 967967 := bstep (se 1 (by rfl) ⟨725975, by rfl⟩ : syracuseStep 967967 = 1451951) B1451951
theorem B6210989 : Blo 428775 6210989 := bstep (se 3 (by rfl) ⟨1164560, by rfl⟩ : syracuseStep 6210989 = 2329121) B2329121
theorem B968489 : Blo 428775 968489 := bstep (se 2 (by rfl) ⟨363183, by rfl⟩ : syracuseStep 968489 = 726367) B726367
theorem B1034041 : Blo 428775 1034041 := bstep (se 2 (by rfl) ⟨387765, by rfl⟩ : syracuseStep 1034041 = 775531) B775531
theorem B2770793 : Blo 428775 2770793 := bstep (se 2 (by rfl) ⟨1039047, by rfl⟩ : syracuseStep 2770793 = 2078095) B2078095
theorem B3688375 : Blo 428775 3688375 := bstep (se 1 (by rfl) ⟨2766281, by rfl⟩ : syracuseStep 3688375 = 5532563) B5532563
theorem B542695 : Blo 428775 542695 := bstep (se 1 (by rfl) ⟨407021, by rfl⟩ : syracuseStep 542695 = 814043) B814043
theorem B2443517 : Blo 428775 2443517 := bstep (se 3 (by rfl) ⟨458159, by rfl⟩ : syracuseStep 2443517 = 916319) B916319
theorem B4639037 : Blo 428775 4639037 := bstep (se 3 (by rfl) ⟨869819, by rfl⟩ : syracuseStep 4639037 = 1739639) B1739639
theorem B1460591 : Blo 428775 1460591 := bstep (se 1 (by rfl) ⟨1095443, by rfl⟩ : syracuseStep 1460591 = 2190887) B2190887
theorem B1231271 : Blo 428775 1231271 := bstep (se 1 (by rfl) ⟨923453, by rfl⟩ : syracuseStep 1231271 = 1846907) B1846907
theorem B5261735 : Blo 428775 5261735 := bstep (se 1 (by rfl) ⟨3946301, by rfl⟩ : syracuseStep 5261735 = 7892603) B7892603
theorem B871087 : Blo 428775 871087 := bstep (se 1 (by rfl) ⟨653315, by rfl⟩ : syracuseStep 871087 = 1306631) B1306631
theorem B8276701 : Blo 428775 8276701 := bstep (se 3 (by rfl) ⟨1551881, by rfl⟩ : syracuseStep 8276701 = 3103763) B3103763
theorem B3099383 : Blo 428775 3099383 := bstep (se 1 (by rfl) ⟨2324537, by rfl⟩ : syracuseStep 3099383 = 4649075) B4649075
theorem B969551 : Blo 428775 969551 := bstep (se 1 (by rfl) ⟨727163, by rfl⟩ : syracuseStep 969551 = 1454327) B1454327
theorem B969767 : Blo 428775 969767 := bstep (se 1 (by rfl) ⟨727325, by rfl⟩ : syracuseStep 969767 = 1454651) B1454651
theorem B2477137 : Blo 428775 2477137 := bstep (se 2 (by rfl) ⟨928926, by rfl⟩ : syracuseStep 2477137 = 1857853) B1857853
theorem B969947 : Blo 428775 969947 := bstep (se 1 (by rfl) ⟨727460, by rfl⟩ : syracuseStep 969947 = 1454921) B1454921
theorem B970145 : Blo 428775 970145 := bstep (se 2 (by rfl) ⟨363804, by rfl⟩ : syracuseStep 970145 = 727609) B727609
theorem B970703 : Blo 428775 970703 := bstep (se 1 (by rfl) ⟨728027, by rfl⟩ : syracuseStep 970703 = 1456055) B1456055
theorem B2183273 : Blo 428775 2183273 := bstep (se 2 (by rfl) ⟨818727, by rfl⟩ : syracuseStep 2183273 = 1637455) B1637455
theorem B643337 : Blo 428775 643337 := bstep (se 2 (by rfl) ⟨241251, by rfl⟩ : syracuseStep 643337 = 482503) B482503
theorem B971081 : Blo 428775 971081 := bstep (se 2 (by rfl) ⟨364155, by rfl⟩ : syracuseStep 971081 = 728311) B728311
theorem B971099 : Blo 428775 971099 := bstep (se 1 (by rfl) ⟨728324, by rfl⟩ : syracuseStep 971099 = 1456649) B1456649
theorem B643439 : Blo 428775 643439 := bstep (se 1 (by rfl) ⟨482579, by rfl⟩ : syracuseStep 643439 = 965159) B965159
theorem B643655 : Blo 428775 643655 := bstep (se 1 (by rfl) ⟨482741, by rfl⟩ : syracuseStep 643655 = 965483) B965483
theorem B643691 : Blo 428775 643691 := bstep (se 1 (by rfl) ⟨482768, by rfl⟩ : syracuseStep 643691 = 965537) B965537
theorem B1167979 : Blo 428775 1167979 := bstep (se 1 (by rfl) ⟨875984, by rfl⟩ : syracuseStep 1167979 = 1751969) B1751969
theorem B2445977 : Blo 428775 2445977 := bstep (se 2 (by rfl) ⟨917241, by rfl⟩ : syracuseStep 2445977 = 1834483) B1834483
theorem B643919 : Blo 428775 643919 := bstep (se 1 (by rfl) ⟨482939, by rfl⟩ : syracuseStep 643919 = 965879) B965879
theorem B2446159 : Blo 428775 2446159 := bstep (se 1 (by rfl) ⟨1834619, by rfl⟩ : syracuseStep 2446159 = 3669239) B3669239
theorem B971675 : Blo 428775 971675 := bstep (se 1 (by rfl) ⟨728756, by rfl⟩ : syracuseStep 971675 = 1457513) B1457513
theorem B4674509 : Blo 428775 4674509 := bstep (se 3 (by rfl) ⟨876470, by rfl⟩ : syracuseStep 4674509 = 1752941) B1752941
theorem B1037299 : Blo 428775 1037299 := bstep (se 1 (by rfl) ⟨777974, by rfl⟩ : syracuseStep 1037299 = 1555949) B1555949
theorem B971873 : Blo 428775 971873 := bstep (se 2 (by rfl) ⟨364452, by rfl⟩ : syracuseStep 971873 = 728905) B728905
theorem B2184407 : Blo 428775 2184407 := bstep (se 1 (by rfl) ⟨1638305, by rfl⟩ : syracuseStep 2184407 = 3276611) B3276611
theorem B644315 : Blo 428775 644315 := bstep (se 1 (by rfl) ⟨483236, by rfl⟩ : syracuseStep 644315 = 966473) B966473
theorem B972071 : Blo 428775 972071 := bstep (se 1 (by rfl) ⟨729053, by rfl⟩ : syracuseStep 972071 = 1458107) B1458107
theorem B644489 : Blo 428775 644489 := bstep (se 2 (by rfl) ⟨241683, by rfl⟩ : syracuseStep 644489 = 483367) B483367
theorem B972449 : Blo 428775 972449 := bstep (se 2 (by rfl) ⟨364668, by rfl⟩ : syracuseStep 972449 = 729337) B729337
theorem B546527 : Blo 428775 546527 := bstep (se 1 (by rfl) ⟨409895, by rfl⟩ : syracuseStep 546527 = 819791) B819791
theorem B644843 : Blo 428775 644843 := bstep (se 1 (by rfl) ⟨483632, by rfl⟩ : syracuseStep 644843 = 967265) B967265
theorem B775993 : Blo 428775 775993 := bstep (se 2 (by rfl) ⟨290997, by rfl⟩ : syracuseStep 775993 = 581995) B581995
theorem B1628009 : Blo 428775 1628009 := bstep (se 2 (by rfl) ⟨610503, by rfl⟩ : syracuseStep 1628009 = 1221007) B1221007
theorem B645071 : Blo 428775 645071 := bstep (se 1 (by rfl) ⟨483803, by rfl⟩ : syracuseStep 645071 = 967607) B967607
theorem B972809 : Blo 428775 972809 := bstep (se 2 (by rfl) ⟨364803, by rfl⟩ : syracuseStep 972809 = 729607) B729607
theorem B645467 : Blo 428775 645467 := bstep (se 1 (by rfl) ⟨484100, by rfl⟩ : syracuseStep 645467 = 968201) B968201
theorem B1038683 : Blo 428775 1038683 := bstep (se 1 (by rfl) ⟨779012, by rfl⟩ : syracuseStep 1038683 = 1558025) B1558025
theorem B1956221 : Blo 428775 1956221 := bstep (se 3 (by rfl) ⟨366791, by rfl⟩ : syracuseStep 1956221 = 733583) B733583
theorem B973223 : Blo 428775 973223 := bstep (se 1 (by rfl) ⟨729917, by rfl⟩ : syracuseStep 973223 = 1459835) B1459835
theorem B973331 : Blo 428775 973331 := bstep (se 1 (by rfl) ⟨729998, by rfl⟩ : syracuseStep 973331 = 1459997) B1459997
theorem B645695 : Blo 428775 645695 := bstep (se 1 (by rfl) ⟨484271, by rfl⟩ : syracuseStep 645695 = 968543) B968543
theorem B973385 : Blo 428775 973385 := bstep (se 2 (by rfl) ⟨365019, by rfl⟩ : syracuseStep 973385 = 730039) B730039
theorem B645815 : Blo 428775 645815 := bstep (se 1 (by rfl) ⟨484361, by rfl⟩ : syracuseStep 645815 = 968723) B968723
theorem B646043 : Blo 428775 646043 := bstep (se 1 (by rfl) ⟨484532, by rfl⟩ : syracuseStep 646043 = 969065) B969065
theorem B1989647 : Blo 428775 1989647 := bstep (se 1 (by rfl) ⟨1492235, by rfl⟩ : syracuseStep 1989647 = 2984471) B2984471
theorem B646439 : Blo 428775 646439 := bstep (se 1 (by rfl) ⟨484829, by rfl⟩ : syracuseStep 646439 = 969659) B969659
theorem B482683 : Blo 428775 482683 := bstep (se 1 (by rfl) ⟨362012, by rfl⟩ : syracuseStep 482683 = 724025) B724025
theorem B646523 : Blo 428775 646523 := bstep (se 1 (by rfl) ⟨484892, by rfl⟩ : syracuseStep 646523 = 969785) B969785
theorem B1858945 : Blo 428775 1858945 := bstep (se 2 (by rfl) ⟨697104, by rfl⟩ : syracuseStep 1858945 = 1394209) B1394209
theorem B646649 : Blo 428775 646649 := bstep (se 2 (by rfl) ⟨242493, by rfl⟩ : syracuseStep 646649 = 484987) B484987
theorem B646751 : Blo 428775 646751 := bstep (se 1 (by rfl) ⟨485063, by rfl⟩ : syracuseStep 646751 = 970127) B970127
theorem B1957679 : Blo 428775 1957679 := bstep (se 1 (by rfl) ⟨1468259, by rfl⟩ : syracuseStep 1957679 = 2936519) B2936519
theorem B646967 : Blo 428775 646967 := bstep (se 1 (by rfl) ⟨485225, by rfl⟩ : syracuseStep 646967 = 970451) B970451
theorem B483151 : Blo 428775 483151 := bstep (se 1 (by rfl) ⟨362363, by rfl⟩ : syracuseStep 483151 = 724727) B724727
theorem B2187323 : Blo 428775 2187323 := bstep (se 1 (by rfl) ⟨1640492, by rfl⟩ : syracuseStep 2187323 = 3280985) B3280985
theorem B647273 : Blo 428775 647273 := bstep (se 2 (by rfl) ⟨242727, by rfl⟩ : syracuseStep 647273 = 485455) B485455
theorem B1695953 : Blo 428775 1695953 := bstep (se 2 (by rfl) ⟨635982, by rfl⟩ : syracuseStep 1695953 = 1271965) B1271965
theorem B483547 : Blo 428775 483547 := bstep (se 1 (by rfl) ⟨362660, by rfl⟩ : syracuseStep 483547 = 725321) B725321
theorem B2318699 : Blo 428775 2318699 := bstep (se 1 (by rfl) ⟨1739024, by rfl⟩ : syracuseStep 2318699 = 3478049) B3478049
theorem B647591 : Blo 428775 647591 := bstep (se 1 (by rfl) ⟨485693, by rfl⟩ : syracuseStep 647591 = 971387) B971387
theorem B483835 : Blo 428775 483835 := bstep (se 1 (by rfl) ⟨362876, by rfl⟩ : syracuseStep 483835 = 725753) B725753
theorem B647675 : Blo 428775 647675 := bstep (se 1 (by rfl) ⟨485756, by rfl⟩ : syracuseStep 647675 = 971513) B971513
theorem B778825 : Blo 428775 778825 := bstep (se 2 (by rfl) ⟨292059, by rfl⟩ : syracuseStep 778825 = 584119) B584119
theorem B647801 : Blo 428775 647801 := bstep (se 2 (by rfl) ⟨242925, by rfl⟩ : syracuseStep 647801 = 485851) B485851
theorem B4154003 : Blo 428775 4154003 := bstep (se 1 (by rfl) ⟨3115502, by rfl⟩ : syracuseStep 4154003 = 6231005) B6231005
theorem B2482859 : Blo 428775 2482859 := bstep (se 1 (by rfl) ⟨1862144, by rfl⟩ : syracuseStep 2482859 = 3724289) B3724289
theorem B484015 : Blo 428775 484015 := bstep (se 1 (by rfl) ⟨363011, by rfl⟩ : syracuseStep 484015 = 726023) B726023
theorem B647855 : Blo 428775 647855 := bstep (se 1 (by rfl) ⟨485891, by rfl⟩ : syracuseStep 647855 = 971783) B971783
theorem B647903 : Blo 428775 647903 := bstep (se 1 (by rfl) ⟨485927, by rfl⟩ : syracuseStep 647903 = 971855) B971855
theorem B484303 : Blo 428775 484303 := bstep (se 1 (by rfl) ⟨363227, by rfl⟩ : syracuseStep 484303 = 726455) B726455
theorem B648167 : Blo 428775 648167 := bstep (se 1 (by rfl) ⟨486125, by rfl⟩ : syracuseStep 648167 = 972251) B972251
theorem B2188295 : Blo 428775 2188295 := bstep (se 1 (by rfl) ⟨1641221, by rfl⟩ : syracuseStep 2188295 = 3282443) B3282443
theorem B648425 : Blo 428775 648425 := bstep (se 2 (by rfl) ⟨243159, by rfl⟩ : syracuseStep 648425 = 486319) B486319
theorem B648479 : Blo 428775 648479 := bstep (se 1 (by rfl) ⟨486359, by rfl⟩ : syracuseStep 648479 = 972719) B972719
theorem B484699 : Blo 428775 484699 := bstep (se 1 (by rfl) ⟨363524, by rfl⟩ : syracuseStep 484699 = 727049) B727049
theorem B4646267 : Blo 428775 4646267 := bstep (se 1 (by rfl) ⟨3484700, by rfl⟩ : syracuseStep 4646267 = 6969401) B6969401
theorem B484807 : Blo 428775 484807 := bstep (se 1 (by rfl) ⟨363605, by rfl⟩ : syracuseStep 484807 = 727211) B727211
theorem B648647 : Blo 428775 648647 := bstep (se 1 (by rfl) ⟨486485, by rfl⟩ : syracuseStep 648647 = 972971) B972971
theorem B779719 : Blo 428775 779719 := bstep (se 1 (by rfl) ⟨584789, by rfl⟩ : syracuseStep 779719 = 1169579) B1169579
theorem B2188781 : Blo 428775 2188781 := bstep (se 3 (by rfl) ⟨410396, by rfl⟩ : syracuseStep 2188781 = 820793) B820793
theorem B649001 : Blo 428775 649001 := bstep (se 2 (by rfl) ⟨243375, by rfl⟩ : syracuseStep 649001 = 486751) B486751
theorem B485167 : Blo 428775 485167 := bstep (se 1 (by rfl) ⟨363875, by rfl⟩ : syracuseStep 485167 = 727751) B727751
theorem B649007 : Blo 428775 649007 := bstep (se 1 (by rfl) ⟨486755, by rfl⟩ : syracuseStep 649007 = 973511) B973511
theorem B485275 : Blo 428775 485275 := bstep (se 1 (by rfl) ⟨363956, by rfl⟩ : syracuseStep 485275 = 727913) B727913
theorem B2320649 : Blo 428775 2320649 := bstep (se 2 (by rfl) ⟨870243, by rfl⟩ : syracuseStep 2320649 = 1740487) B1740487
theorem B2189591 : Blo 428775 2189591 := bstep (se 1 (by rfl) ⟨1642193, by rfl⟩ : syracuseStep 2189591 = 3284387) B3284387
theorem B1468697 : Blo 428775 1468697 := bstep (se 2 (by rfl) ⟨550761, by rfl⟩ : syracuseStep 1468697 = 1101523) B1101523
theorem B485671 : Blo 428775 485671 := bstep (se 1 (by rfl) ⟨364253, by rfl⟩ : syracuseStep 485671 = 728507) B728507
theorem B485743 : Blo 428775 485743 := bstep (se 1 (by rfl) ⟨364307, by rfl⟩ : syracuseStep 485743 = 728615) B728615
theorem B4647341 : Blo 428775 4647341 := bstep (se 3 (by rfl) ⟨871376, by rfl⟩ : syracuseStep 4647341 = 1742753) B1742753
theorem B485959 : Blo 428775 485959 := bstep (se 1 (by rfl) ⟨364469, by rfl⟩ : syracuseStep 485959 = 728939) B728939
theorem B2616131 : Blo 428775 2616131 := bstep (se 1 (by rfl) ⟨1962098, by rfl⟩ : syracuseStep 2616131 = 3924197) B3924197
theorem B1305499 : Blo 428775 1305499 := bstep (se 1 (by rfl) ⟨979124, by rfl⟩ : syracuseStep 1305499 = 1958249) B1958249
theorem B1633567 : Blo 428775 1633567 := bstep (se 1 (by rfl) ⟨1225175, by rfl⟩ : syracuseStep 1633567 = 2450351) B2450351
theorem B2485633 : Blo 428775 2485633 := bstep (se 2 (by rfl) ⟨932112, by rfl⟩ : syracuseStep 2485633 = 1864225) B1864225
theorem B486823 : Blo 428775 486823 := bstep (se 1 (by rfl) ⟨365117, by rfl⟩ : syracuseStep 486823 = 730235) B730235
theorem B814855 : Blo 428775 814855 := bstep (se 1 (by rfl) ⟨611141, by rfl⟩ : syracuseStep 814855 = 1222283) B1222283
theorem B2355119 : Blo 428775 2355119 := bstep (se 1 (by rfl) ⟨1766339, by rfl⟩ : syracuseStep 2355119 = 3532679) B3532679
theorem B47673305 : Blo 428775 47673305 := bstep (se 2 (by rfl) ⟨17877489, by rfl⟩ : syracuseStep 47673305 = 35754979) B35754979
theorem B1044809 : Blo 428775 1044809 := bstep (se 2 (by rfl) ⟨391803, by rfl⟩ : syracuseStep 1044809 = 783607) B783607
theorem B1864919 : Blo 428775 1864919 := bstep (se 1 (by rfl) ⟨1398689, by rfl⟩ : syracuseStep 1864919 = 2797379) B2797379
theorem B3667463 : Blo 428775 3667463 := bstep (se 1 (by rfl) ⟨2750597, by rfl⟩ : syracuseStep 3667463 = 5501195) B5501195
theorem B1635997 : Blo 428775 1635997 := bstep (se 3 (by rfl) ⟨306749, by rfl⟩ : syracuseStep 1635997 = 613499) B613499
theorem B816875 : Blo 428775 816875 := bstep (se 1 (by rfl) ⟨612656, by rfl⟩ : syracuseStep 816875 = 1225313) B1225313
theorem B817103 : Blo 428775 817103 := bstep (se 1 (by rfl) ⟨612827, by rfl⟩ : syracuseStep 817103 = 1225655) B1225655
theorem B4127051 : Blo 428775 4127051 := bstep (se 1 (by rfl) ⟨3095288, by rfl⟩ : syracuseStep 4127051 = 6190577) B6190577
theorem B817771 : Blo 428775 817771 := bstep (se 1 (by rfl) ⟨613328, by rfl⟩ : syracuseStep 817771 = 1226657) B1226657
theorem B817847 : Blo 428775 817847 := bstep (se 1 (by rfl) ⟨613385, by rfl⟩ : syracuseStep 817847 = 1226771) B1226771
theorem B3275639 : Blo 428775 3275639 := bstep (se 1 (by rfl) ⟨2456729, by rfl⟩ : syracuseStep 3275639 = 4913459) B4913459
theorem B4651931 : Blo 428775 4651931 := bstep (se 1 (by rfl) ⟨3488948, by rfl⟩ : syracuseStep 4651931 = 6977897) B6977897
theorem B818075 : Blo 428775 818075 := bstep (se 1 (by rfl) ⟨613556, by rfl⟩ : syracuseStep 818075 = 1227113) B1227113
theorem B1866791 : Blo 428775 1866791 := bstep (se 1 (by rfl) ⟨1400093, by rfl⟩ : syracuseStep 1866791 = 2800187) B2800187
theorem B458023 : Blo 428775 458023 := bstep (se 1 (by rfl) ⟨343517, by rfl⟩ : syracuseStep 458023 = 687035) B687035
theorem B1637729 : Blo 428775 1637729 := bstep (se 2 (by rfl) ⟨614148, by rfl⟩ : syracuseStep 1637729 = 1228297) B1228297
theorem B818849 : Blo 428775 818849 := bstep (se 2 (by rfl) ⟨307068, by rfl⟩ : syracuseStep 818849 = 614137) B614137
theorem B819001 : Blo 428775 819001 := bstep (se 2 (by rfl) ⟨307125, by rfl⟩ : syracuseStep 819001 = 614251) B614251
theorem B1834825 : Blo 428775 1834825 := bstep (se 2 (by rfl) ⟨688059, by rfl⟩ : syracuseStep 1834825 = 1376119) B1376119
theorem B819487 : Blo 428775 819487 := bstep (se 1 (by rfl) ⟨614615, by rfl⟩ : syracuseStep 819487 = 1229231) B1229231
theorem B2327305 : Blo 428775 2327305 := bstep (se 2 (by rfl) ⟨872739, by rfl⟩ : syracuseStep 2327305 = 1745479) B1745479
theorem B12583997 : Blo 428775 12583997 := bstep (se 3 (by rfl) ⟨2359499, by rfl⟩ : syracuseStep 12583997 = 4718999) B4718999
theorem B820847 : Blo 428775 820847 := bstep (se 1 (by rfl) ⟨615635, by rfl⟩ : syracuseStep 820847 = 1231271) B1231271
theorem B3507823 : Blo 428775 3507823 := bstep (se 1 (by rfl) ⟨2630867, by rfl⟩ : syracuseStep 3507823 = 5261735) B5261735
theorem B1377913 : Blo 428775 1377913 := bstep (se 2 (by rfl) ⟨516717, by rfl⟩ : syracuseStep 1377913 = 1033435) B1033435
theorem B1640159 : Blo 428775 1640159 := bstep (se 1 (by rfl) ⟨1230119, by rfl⟩ : syracuseStep 1640159 = 2460239) B2460239
theorem B3671837 : Blo 428775 3671837 := bstep (se 3 (by rfl) ⟨688469, by rfl⟩ : syracuseStep 3671837 = 1376939) B1376939
theorem B6620957 : Blo 428775 6620957 := bstep (se 3 (by rfl) ⟨1241429, by rfl⟩ : syracuseStep 6620957 = 2482859) B2482859
theorem B2066255 : Blo 428775 2066255 := bstep (se 1 (by rfl) ⟨1549691, by rfl⟩ : syracuseStep 2066255 = 3099383) B3099383
theorem B657401 : Blo 428775 657401 := bstep (se 2 (by rfl) ⟨246525, by rfl⟩ : syracuseStep 657401 = 493051) B493051
theorem B1378721 : Blo 428775 1378721 := bstep (se 2 (by rfl) ⟨517020, by rfl⟩ : syracuseStep 1378721 = 1034041) B1034041
theorem B4917833 : Blo 428775 4917833 := bstep (se 2 (by rfl) ⟨1844187, by rfl⟩ : syracuseStep 4917833 = 3688375) B3688375
theorem B723593 : Blo 428775 723593 := bstep (se 2 (by rfl) ⟨271347, by rfl⟩ : syracuseStep 723593 = 542695) B542695
theorem B1641131 : Blo 428775 1641131 := bstep (se 1 (by rfl) ⟨1230848, by rfl⟩ : syracuseStep 1641131 = 2461697) B2461697
theorem B3935063 : Blo 428775 3935063 := bstep (se 1 (by rfl) ⟨2951297, by rfl⟩ : syracuseStep 3935063 = 5902595) B5902595
theorem B428891 : Blo 428775 428891 := bstep (se 1 (by rfl) ⟨321668, by rfl⟩ : syracuseStep 428891 = 643337) B643337
theorem B428959 : Blo 428775 428959 := bstep (se 1 (by rfl) ⟨321719, by rfl⟩ : syracuseStep 428959 = 643439) B643439
theorem B429103 : Blo 428775 429103 := bstep (se 1 (by rfl) ⟨321827, by rfl⟩ : syracuseStep 429103 = 643655) B643655
theorem B1379375 : Blo 428775 1379375 := bstep (se 1 (by rfl) ⟨1034531, by rfl⟩ : syracuseStep 1379375 = 2069063) B2069063
theorem B429127 : Blo 428775 429127 := bstep (se 1 (by rfl) ⟨321845, by rfl⟩ : syracuseStep 429127 = 643691) B643691
theorem B429279 : Blo 428775 429279 := bstep (se 1 (by rfl) ⟨321959, by rfl⟩ : syracuseStep 429279 = 643919) B643919
theorem B5901619 : Blo 428775 5901619 := bstep (se 1 (by rfl) ⟨4426214, by rfl⟩ : syracuseStep 5901619 = 8852429) B8852429
theorem B3116339 : Blo 428775 3116339 := bstep (se 1 (by rfl) ⟨2337254, by rfl⟩ : syracuseStep 3116339 = 4674509) B4674509
theorem B23662043 : Blo 428775 23662043 := bstep (se 1 (by rfl) ⟨17746532, by rfl⟩ : syracuseStep 23662043 = 35493065) B35493065
theorem B429543 : Blo 428775 429543 := bstep (se 1 (by rfl) ⟨322157, by rfl⟩ : syracuseStep 429543 = 644315) B644315
theorem B986687 : Blo 428775 986687 := bstep (se 1 (by rfl) ⟨740015, by rfl⟩ : syracuseStep 986687 = 1480031) B1480031
theorem B2461265 : Blo 428775 2461265 := bstep (se 2 (by rfl) ⟨922974, by rfl⟩ : syracuseStep 2461265 = 1845949) B1845949
theorem B429659 : Blo 428775 429659 := bstep (se 1 (by rfl) ⟨322244, by rfl⟩ : syracuseStep 429659 = 644489) B644489
theorem B429895 : Blo 428775 429895 := bstep (se 1 (by rfl) ⟨322421, by rfl⟩ : syracuseStep 429895 = 644843) B644843
theorem B1740665 : Blo 428775 1740665 := bstep (se 2 (by rfl) ⟨652749, by rfl⟩ : syracuseStep 1740665 = 1305499) B1305499
theorem B1085339 : Blo 428775 1085339 := bstep (se 1 (by rfl) ⟨814004, by rfl⟩ : syracuseStep 1085339 = 1628009) B1628009
theorem B430047 : Blo 428775 430047 := bstep (se 1 (by rfl) ⟨322535, by rfl⟩ : syracuseStep 430047 = 645071) B645071
theorem B725179 : Blo 428775 725179 := bstep (se 1 (by rfl) ⟨543884, by rfl⟩ : syracuseStep 725179 = 1087769) B1087769
theorem B430311 : Blo 428775 430311 := bstep (se 1 (by rfl) ⟨322733, by rfl⟩ : syracuseStep 430311 = 645467) B645467
theorem B725375 : Blo 428775 725375 := bstep (se 1 (by rfl) ⟨544031, by rfl⟩ : syracuseStep 725375 = 1088063) B1088063
theorem B430463 : Blo 428775 430463 := bstep (se 1 (by rfl) ⟨322847, by rfl⟩ : syracuseStep 430463 = 645695) B645695
theorem B430543 : Blo 428775 430543 := bstep (se 1 (by rfl) ⟨322907, by rfl⟩ : syracuseStep 430543 = 645815) B645815
theorem B3314177 : Blo 428775 3314177 := bstep (se 2 (by rfl) ⟨1242816, by rfl⟩ : syracuseStep 3314177 = 2485633) B2485633
theorem B430695 : Blo 428775 430695 := bstep (se 1 (by rfl) ⟨323021, by rfl⟩ : syracuseStep 430695 = 646043) B646043
theorem B725807 : Blo 428775 725807 := bstep (se 1 (by rfl) ⟨544355, by rfl⟩ : syracuseStep 725807 = 1088711) B1088711
theorem B430959 : Blo 428775 430959 := bstep (se 1 (by rfl) ⟨323219, by rfl⟩ : syracuseStep 430959 = 646439) B646439
theorem B431015 : Blo 428775 431015 := bstep (se 1 (by rfl) ⟨323261, by rfl⟩ : syracuseStep 431015 = 646523) B646523
theorem B431099 : Blo 428775 431099 := bstep (se 1 (by rfl) ⟨323324, by rfl⟩ : syracuseStep 431099 = 646649) B646649
theorem B1086473 : Blo 428775 1086473 := bstep (se 2 (by rfl) ⟨407427, by rfl⟩ : syracuseStep 1086473 = 814855) B814855
theorem B2757671 : Blo 428775 2757671 := bstep (se 1 (by rfl) ⟨2068253, by rfl⟩ : syracuseStep 2757671 = 4136507) B4136507
theorem B431167 : Blo 428775 431167 := bstep (se 1 (by rfl) ⟨323375, by rfl⟩ : syracuseStep 431167 = 646751) B646751
theorem B431311 : Blo 428775 431311 := bstep (se 1 (by rfl) ⟨323483, by rfl⟩ : syracuseStep 431311 = 646967) B646967
theorem B1447199 : Blo 428775 1447199 := bstep (se 1 (by rfl) ⟨1085399, by rfl⟩ : syracuseStep 1447199 = 2170799) B2170799
theorem B431515 : Blo 428775 431515 := bstep (se 1 (by rfl) ⟨323636, by rfl⟩ : syracuseStep 431515 = 647273) B647273
theorem B4920749 : Blo 428775 4920749 := bstep (se 3 (by rfl) ⟨922640, by rfl⟩ : syracuseStep 4920749 = 1845281) B1845281
theorem B1545799 : Blo 428775 1545799 := bstep (se 1 (by rfl) ⟨1159349, by rfl⟩ : syracuseStep 1545799 = 2318699) B2318699
theorem B431727 : Blo 428775 431727 := bstep (se 1 (by rfl) ⟨323795, by rfl⟩ : syracuseStep 431727 = 647591) B647591
theorem B431783 : Blo 428775 431783 := bstep (se 1 (by rfl) ⟨323837, by rfl⟩ : syracuseStep 431783 = 647675) B647675
theorem B726779 : Blo 428775 726779 := bstep (se 1 (by rfl) ⟨545084, by rfl⟩ : syracuseStep 726779 = 1090169) B1090169
theorem B431867 : Blo 428775 431867 := bstep (se 1 (by rfl) ⟨323900, by rfl⟩ : syracuseStep 431867 = 647801) B647801
theorem B1840907 : Blo 428775 1840907 := bstep (se 1 (by rfl) ⟨1380680, by rfl⟩ : syracuseStep 1840907 = 2761361) B2761361
theorem B431903 : Blo 428775 431903 := bstep (se 1 (by rfl) ⟨323927, by rfl⟩ : syracuseStep 431903 = 647855) B647855
theorem B431935 : Blo 428775 431935 := bstep (se 1 (by rfl) ⟨323951, by rfl⟩ : syracuseStep 431935 = 647903) B647903
theorem B727015 : Blo 428775 727015 := bstep (se 1 (by rfl) ⟨545261, by rfl⟩ : syracuseStep 727015 = 1090523) B1090523
theorem B432111 : Blo 428775 432111 := bstep (se 1 (by rfl) ⟨324083, by rfl⟩ : syracuseStep 432111 = 648167) B648167
theorem B432283 : Blo 428775 432283 := bstep (se 1 (by rfl) ⟨324212, by rfl⟩ : syracuseStep 432283 = 648425) B648425
theorem B727231 : Blo 428775 727231 := bstep (se 1 (by rfl) ⟨545423, by rfl⟩ : syracuseStep 727231 = 1090847) B1090847
theorem B432319 : Blo 428775 432319 := bstep (se 1 (by rfl) ⟨324239, by rfl⟩ : syracuseStep 432319 = 648479) B648479
theorem B432431 : Blo 428775 432431 := bstep (se 1 (by rfl) ⟨324323, by rfl⟩ : syracuseStep 432431 = 648647) B648647
theorem B12392909 : Blo 428775 12392909 := bstep (se 3 (by rfl) ⟨2323670, by rfl⟩ : syracuseStep 12392909 = 4647341) B4647341
theorem B432667 : Blo 428775 432667 := bstep (se 1 (by rfl) ⟨324500, by rfl⟩ : syracuseStep 432667 = 649001) B649001
theorem B432671 : Blo 428775 432671 := bstep (se 1 (by rfl) ⟨324503, by rfl⟩ : syracuseStep 432671 = 649007) B649007
theorem B1383065 : Blo 428775 1383065 := bstep (se 2 (by rfl) ⟨518649, by rfl⟩ : syracuseStep 1383065 = 1037299) B1037299
theorem B1547099 : Blo 428775 1547099 := bstep (se 1 (by rfl) ⟨1160324, by rfl⟩ : syracuseStep 1547099 = 2320649) B2320649
theorem B1579867 : Blo 428775 1579867 := bstep (se 1 (by rfl) ⟨1184900, by rfl⟩ : syracuseStep 1579867 = 2369801) B2369801
theorem B727967 : Blo 428775 727967 := bstep (se 1 (by rfl) ⟨545975, by rfl⟩ : syracuseStep 727967 = 1091951) B1091951
theorem B1449089 : Blo 428775 1449089 := bstep (se 2 (by rfl) ⟨543408, by rfl⟩ : syracuseStep 1449089 = 1086817) B1086817
theorem B1449143 : Blo 428775 1449143 := bstep (se 1 (by rfl) ⟨1086857, by rfl⟩ : syracuseStep 1449143 = 2173715) B2173715
theorem B1744087 : Blo 428775 1744087 := bstep (se 1 (by rfl) ⟨1308065, by rfl⟩ : syracuseStep 1744087 = 2616131) B2616131
theorem B728399 : Blo 428775 728399 := bstep (se 1 (by rfl) ⟨546299, by rfl⟩ : syracuseStep 728399 = 1092599) B1092599
theorem B1383911 : Blo 428775 1383911 := bstep (se 1 (by rfl) ⟨1037933, by rfl⟩ : syracuseStep 1383911 = 2075867) B2075867
theorem B1449899 : Blo 428775 1449899 := bstep (se 1 (by rfl) ⟨1087424, by rfl⟩ : syracuseStep 1449899 = 2174849) B2174849
theorem B696539 : Blo 428775 696539 := bstep (se 1 (by rfl) ⟨522404, by rfl⟩ : syracuseStep 696539 = 1044809) B1044809
theorem B9314675 : Blo 428775 9314675 := bstep (se 1 (by rfl) ⟨6986006, by rfl⟩ : syracuseStep 9314675 = 13972013) B13972013
theorem B1450439 : Blo 428775 1450439 := bstep (se 1 (by rfl) ⟨1087829, by rfl⟩ : syracuseStep 1450439 = 2175659) B2175659
theorem B729695 : Blo 428775 729695 := bstep (se 1 (by rfl) ⟨547271, by rfl⟩ : syracuseStep 729695 = 1094543) B1094543
theorem B1450763 : Blo 428775 1450763 := bstep (se 1 (by rfl) ⟨1088072, by rfl⟩ : syracuseStep 1450763 = 2176145) B2176145
theorem B1090361 : Blo 428775 1090361 := bstep (se 2 (by rfl) ⟨408885, by rfl⟩ : syracuseStep 1090361 = 817771) B817771
theorem B7873337 : Blo 428775 7873337 := bstep (se 2 (by rfl) ⟨2952501, by rfl⟩ : syracuseStep 7873337 = 5905003) B5905003
theorem B1451033 : Blo 428775 1451033 := bstep (se 2 (by rfl) ⟨544137, by rfl⟩ : syracuseStep 1451033 = 1088275) B1088275
theorem B1451681 : Blo 428775 1451681 := bstep (se 2 (by rfl) ⟨544380, by rfl⟩ : syracuseStep 1451681 = 1088761) B1088761
theorem B1124543 : Blo 428775 1124543 := bstep (se 1 (by rfl) ⟨843407, by rfl⟩ : syracuseStep 1124543 = 1686815) B1686815
theorem B1091819 : Blo 428775 1091819 := bstep (se 1 (by rfl) ⟨818864, by rfl⟩ : syracuseStep 1091819 = 1637729) B1637729
theorem B1452383 : Blo 428775 1452383 := bstep (se 1 (by rfl) ⟨1089287, by rfl⟩ : syracuseStep 1452383 = 2178575) B2178575
theorem B1092001 : Blo 428775 1092001 := bstep (se 2 (by rfl) ⟨409500, by rfl⟩ : syracuseStep 1092001 = 819001) B819001
theorem B5220865 : Blo 428775 5220865 := bstep (se 2 (by rfl) ⟨1957824, by rfl⟩ : syracuseStep 5220865 = 3915649) B3915649
theorem B1452545 : Blo 428775 1452545 := bstep (se 2 (by rfl) ⟨544704, by rfl⟩ : syracuseStep 1452545 = 1089409) B1089409
theorem B3091051 : Blo 428775 3091051 := bstep (se 1 (by rfl) ⟨2318288, by rfl⟩ : syracuseStep 3091051 = 4636577) B4636577
theorem B3680963 : Blo 428775 3680963 := bstep (se 1 (by rfl) ⟨2760722, by rfl⟩ : syracuseStep 3680963 = 5521445) B5521445
theorem B1453031 : Blo 428775 1453031 := bstep (se 1 (by rfl) ⟨1089773, by rfl⟩ : syracuseStep 1453031 = 2179547) B2179547
theorem B1223923 : Blo 428775 1223923 := bstep (se 1 (by rfl) ⟨917942, by rfl⟩ : syracuseStep 1223923 = 1835885) B1835885
theorem B1453355 : Blo 428775 1453355 := bstep (se 1 (by rfl) ⟨1090016, by rfl⟩ : syracuseStep 1453355 = 2180033) B2180033
theorem B1093115 : Blo 428775 1093115 := bstep (se 1 (by rfl) ⟨819836, by rfl⟩ : syracuseStep 1093115 = 1639673) B1639673
theorem B1453625 : Blo 428775 1453625 := bstep (se 2 (by rfl) ⟨545109, by rfl⟩ : syracuseStep 1453625 = 1090219) B1090219
theorem B699967 : Blo 428775 699967 := bstep (se 1 (by rfl) ⟨524975, by rfl⟩ : syracuseStep 699967 = 1049951) B1049951
theorem B4140659 : Blo 428775 4140659 := bstep (se 1 (by rfl) ⟨3105494, by rfl⟩ : syracuseStep 4140659 = 6210989) B6210989
theorem B4894505 : Blo 428775 4894505 := bstep (se 2 (by rfl) ⟨1835439, by rfl⟩ : syracuseStep 4894505 = 3670879) B3670879
theorem B1847195 : Blo 428775 1847195 := bstep (se 1 (by rfl) ⟨1385396, by rfl⟩ : syracuseStep 1847195 = 2770793) B2770793
theorem B5878291 : Blo 428775 5878291 := bstep (se 1 (by rfl) ⟨4408718, by rfl⟩ : syracuseStep 5878291 = 8817437) B8817437
theorem B1094867 : Blo 428775 1094867 := bstep (se 1 (by rfl) ⟨821150, by rfl⟩ : syracuseStep 1094867 = 1642301) B1642301
theorem B3093821 : Blo 428775 3093821 := bstep (se 3 (by rfl) ⟨580091, by rfl⟩ : syracuseStep 3093821 = 1160183) B1160183
theorem B1455515 : Blo 428775 1455515 := bstep (se 1 (by rfl) ⟨1091636, by rfl⟩ : syracuseStep 1455515 = 2183273) B2183273
theorem B5912129 : Blo 428775 5912129 := bstep (se 2 (by rfl) ⟨2217048, by rfl⟩ : syracuseStep 5912129 = 4434097) B4434097
theorem B1554103 : Blo 428775 1554103 := bstep (se 1 (by rfl) ⟨1165577, by rfl⟩ : syracuseStep 1554103 = 2331155) B2331155
theorem B3979145 : Blo 428775 3979145 := bstep (se 2 (by rfl) ⟨1492179, by rfl⟩ : syracuseStep 3979145 = 2984359) B2984359
theorem B1456271 : Blo 428775 1456271 := bstep (se 1 (by rfl) ⟨1092203, by rfl⟩ : syracuseStep 1456271 = 2184407) B2184407
theorem B964763 : Blo 428775 964763 := bstep (se 1 (by rfl) ⟨723572, by rfl⟩ : syracuseStep 964763 = 1447145) B1447145
theorem B1161449 : Blo 428775 1161449 := bstep (se 2 (by rfl) ⟨435543, by rfl⟩ : syracuseStep 1161449 = 871087) B871087
theorem B964871 : Blo 428775 964871 := bstep (se 1 (by rfl) ⟨723653, by rfl⟩ : syracuseStep 964871 = 1447307) B1447307
theorem B965177 : Blo 428775 965177 := bstep (se 2 (by rfl) ⟨361941, by rfl⟩ : syracuseStep 965177 = 723883) B723883
theorem B1227727 : Blo 428775 1227727 := bstep (se 1 (by rfl) ⟨920795, by rfl⟩ : syracuseStep 1227727 = 1841591) B1841591
theorem B2178089 : Blo 428775 2178089 := bstep (se 2 (by rfl) ⟨816783, by rfl⟩ : syracuseStep 2178089 = 1633567) B1633567
theorem B1457405 : Blo 428775 1457405 := bstep (se 3 (by rfl) ⟨273263, by rfl⟩ : syracuseStep 1457405 = 546527) B546527
theorem B965897 : Blo 428775 965897 := bstep (se 2 (by rfl) ⟨362211, by rfl⟩ : syracuseStep 965897 = 724423) B724423
theorem B1326431 : Blo 428775 1326431 := bstep (se 1 (by rfl) ⟨994823, by rfl⟩ : syracuseStep 1326431 = 1989647) B1989647
theorem B1162831 : Blo 428775 1162831 := bstep (se 1 (by rfl) ⟨872123, by rfl⟩ : syracuseStep 1162831 = 1744247) B1744247
theorem B5521081 : Blo 428775 5521081 := bstep (se 2 (by rfl) ⟨2070405, by rfl⟩ : syracuseStep 5521081 = 4140811) B4140811
theorem B1458215 : Blo 428775 1458215 := bstep (se 1 (by rfl) ⟨1093661, by rfl⟩ : syracuseStep 1458215 = 2187323) B2187323
theorem B1130635 : Blo 428775 1130635 := bstep (se 1 (by rfl) ⟨847976, by rfl⟩ : syracuseStep 1130635 = 1695953) B1695953
theorem B7979147 : Blo 428775 7979147 := bstep (se 1 (by rfl) ⟨5984360, by rfl⟩ : syracuseStep 7979147 = 11968721) B11968721
theorem B966887 : Blo 428775 966887 := bstep (se 1 (by rfl) ⟨725165, by rfl⟩ : syracuseStep 966887 = 1450331) B1450331
theorem B2769335 : Blo 428775 2769335 := bstep (se 1 (by rfl) ⟨2077001, by rfl⟩ : syracuseStep 2769335 = 4154003) B4154003
theorem B2802215 : Blo 428775 2802215 := bstep (se 1 (by rfl) ⟨2101661, by rfl⟩ : syracuseStep 2802215 = 4203323) B4203323
theorem B1458863 : Blo 428775 1458863 := bstep (se 1 (by rfl) ⟨1094147, by rfl⟩ : syracuseStep 1458863 = 2188295) B2188295
theorem B3916525 : Blo 428775 3916525 := bstep (se 3 (by rfl) ⟨734348, by rfl⟩ : syracuseStep 3916525 = 1468697) B1468697
theorem B967481 : Blo 428775 967481 := bstep (se 2 (by rfl) ⟨362805, by rfl⟩ : syracuseStep 967481 = 725611) B725611
theorem B1557305 : Blo 428775 1557305 := bstep (se 2 (by rfl) ⟨583989, by rfl⟩ : syracuseStep 1557305 = 1167979) B1167979
theorem B12370765 : Blo 428775 12370765 := bstep (se 3 (by rfl) ⟨2319518, by rfl⟩ : syracuseStep 12370765 = 4639037) B4639037
theorem B967535 : Blo 428775 967535 := bstep (se 1 (by rfl) ⟨725651, by rfl⟩ : syracuseStep 967535 = 1451303) B1451303
theorem B2769821 : Blo 428775 2769821 := bstep (se 3 (by rfl) ⟨519341, by rfl⟩ : syracuseStep 2769821 = 1038683) B1038683
theorem B3097511 : Blo 428775 3097511 := bstep (se 1 (by rfl) ⟨2323133, by rfl⟩ : syracuseStep 3097511 = 4646267) B4646267
theorem B1459187 : Blo 428775 1459187 := bstep (se 1 (by rfl) ⟨1094390, by rfl⟩ : syracuseStep 1459187 = 2188781) B2188781
theorem B1754171 : Blo 428775 1754171 := bstep (se 1 (by rfl) ⟨1315628, by rfl⟩ : syracuseStep 1754171 = 2631257) B2631257
theorem B3261545 : Blo 428775 3261545 := bstep (se 2 (by rfl) ⟨1223079, by rfl⟩ : syracuseStep 3261545 = 2446159) B2446159
theorem B968111 : Blo 428775 968111 := bstep (se 1 (by rfl) ⟨726083, by rfl⟩ : syracuseStep 968111 = 1452167) B1452167
theorem B1459727 : Blo 428775 1459727 := bstep (se 1 (by rfl) ⟨1094795, by rfl⟩ : syracuseStep 1459727 = 2189591) B2189591
theorem B1230689 : Blo 428775 1230689 := bstep (se 2 (by rfl) ⟨461508, by rfl⟩ : syracuseStep 1230689 = 923017) B923017
theorem B2181329 : Blo 428775 2181329 := bstep (se 2 (by rfl) ⟨817998, by rfl⟩ : syracuseStep 2181329 = 1635997) B1635997
theorem B968939 : Blo 428775 968939 := bstep (se 1 (by rfl) ⟨726704, by rfl⟩ : syracuseStep 968939 = 1453409) B1453409
theorem B1460537 : Blo 428775 1460537 := bstep (se 2 (by rfl) ⟨547701, by rfl⟩ : syracuseStep 1460537 = 1095403) B1095403
theorem B1034657 : Blo 428775 1034657 := bstep (se 2 (by rfl) ⟨387996, by rfl⟩ : syracuseStep 1034657 = 775993) B775993
theorem B99830485 : Blo 428775 99830485 := bstep (se 7 (by rfl) ⟨1169888, by rfl⟩ : syracuseStep 99830485 = 2339777) B2339777
theorem B1231919 : Blo 428775 1231919 := bstep (se 1 (by rfl) ⟨923939, by rfl⟩ : syracuseStep 1231919 = 1847879) B1847879
theorem B970235 : Blo 428775 970235 := bstep (se 1 (by rfl) ⟨727676, by rfl⟩ : syracuseStep 970235 = 1455353) B1455353
theorem B2444975 : Blo 428775 2444975 := bstep (se 1 (by rfl) ⟨1833731, by rfl⟩ : syracuseStep 2444975 = 3667463) B3667463
theorem B970415 : Blo 428775 970415 := bstep (se 1 (by rfl) ⟨727811, by rfl⟩ : syracuseStep 970415 = 1455623) B1455623
theorem B544583 : Blo 428775 544583 := bstep (se 1 (by rfl) ⟨408437, by rfl⟩ : syracuseStep 544583 = 816875) B816875
theorem B774011 : Blo 428775 774011 := bstep (se 1 (by rfl) ⟨580508, by rfl⟩ : syracuseStep 774011 = 1161017) B1161017
theorem B544735 : Blo 428775 544735 := bstep (se 1 (by rfl) ⟨408551, by rfl⟩ : syracuseStep 544735 = 817103) B817103
theorem B971063 : Blo 428775 971063 := bstep (se 1 (by rfl) ⟨728297, by rfl⟩ : syracuseStep 971063 = 1456595) B1456595
theorem B971135 : Blo 428775 971135 := bstep (se 1 (by rfl) ⟨728351, by rfl⟩ : syracuseStep 971135 = 1456703) B1456703
theorem B610697 : Blo 428775 610697 := bstep (se 2 (by rfl) ⟨229011, by rfl⟩ : syracuseStep 610697 = 458023) B458023
theorem B2183597 : Blo 428775 2183597 := bstep (se 3 (by rfl) ⟨409424, by rfl⟩ : syracuseStep 2183597 = 818849) B818849
theorem B643535 : Blo 428775 643535 := bstep (se 1 (by rfl) ⟨482651, by rfl⟩ : syracuseStep 643535 = 965303) B965303
theorem B545231 : Blo 428775 545231 := bstep (se 1 (by rfl) ⟨408923, by rfl⟩ : syracuseStep 545231 = 817847) B817847
theorem B643577 : Blo 428775 643577 := bstep (se 2 (by rfl) ⟨241341, by rfl⟩ : syracuseStep 643577 = 482683) B482683
theorem B2478593 : Blo 428775 2478593 := bstep (se 2 (by rfl) ⟨929472, by rfl⟩ : syracuseStep 2478593 = 1858945) B1858945
theorem B2183759 : Blo 428775 2183759 := bstep (se 1 (by rfl) ⟨1637819, by rfl⟩ : syracuseStep 2183759 = 3275639) B3275639
theorem B643679 : Blo 428775 643679 := bstep (se 1 (by rfl) ⟨482759, by rfl⟩ : syracuseStep 643679 = 965519) B965519
theorem B3101287 : Blo 428775 3101287 := bstep (se 1 (by rfl) ⟨2325965, by rfl⟩ : syracuseStep 3101287 = 4651931) B4651931
theorem B545383 : Blo 428775 545383 := bstep (se 1 (by rfl) ⟨409037, by rfl⟩ : syracuseStep 545383 = 818075) B818075
theorem B3527675 : Blo 428775 3527675 := bstep (se 1 (by rfl) ⟨2645756, by rfl⟩ : syracuseStep 3527675 = 5291513) B5291513
theorem B644159 : Blo 428775 644159 := bstep (se 1 (by rfl) ⟨483119, by rfl⟩ : syracuseStep 644159 = 966239) B966239
theorem B2446433 : Blo 428775 2446433 := bstep (se 2 (by rfl) ⟨917412, by rfl⟩ : syracuseStep 2446433 = 1834825) B1834825
theorem B644201 : Blo 428775 644201 := bstep (se 2 (by rfl) ⟨241575, by rfl⟩ : syracuseStep 644201 = 483151) B483151
theorem B644303 : Blo 428775 644303 := bstep (se 1 (by rfl) ⟨483227, by rfl⟩ : syracuseStep 644303 = 966455) B966455
theorem B644507 : Blo 428775 644507 := bstep (se 1 (by rfl) ⟨483380, by rfl⟩ : syracuseStep 644507 = 966761) B966761
theorem B546203 : Blo 428775 546203 := bstep (se 1 (by rfl) ⟨409652, by rfl⟩ : syracuseStep 546203 = 819305) B819305
theorem B972359 : Blo 428775 972359 := bstep (se 1 (by rfl) ⟨729269, by rfl⟩ : syracuseStep 972359 = 1458539) B1458539
theorem B710255 : Blo 428775 710255 := bstep (se 1 (by rfl) ⟨532691, by rfl⟩ : syracuseStep 710255 = 1065383) B1065383
theorem B644729 : Blo 428775 644729 := bstep (se 2 (by rfl) ⟨241773, by rfl⟩ : syracuseStep 644729 = 483547) B483547
theorem B644831 : Blo 428775 644831 := bstep (se 1 (by rfl) ⟨483623, by rfl⟩ : syracuseStep 644831 = 967247) B967247
theorem B972539 : Blo 428775 972539 := bstep (se 1 (by rfl) ⟨729404, by rfl⟩ : syracuseStep 972539 = 1458809) B1458809
theorem B612127 : Blo 428775 612127 := bstep (se 1 (by rfl) ⟨459095, by rfl⟩ : syracuseStep 612127 = 918191) B918191
theorem B644927 : Blo 428775 644927 := bstep (se 1 (by rfl) ⟨483695, by rfl⟩ : syracuseStep 644927 = 967391) B967391
theorem B645095 : Blo 428775 645095 := bstep (se 1 (by rfl) ⟨483821, by rfl⟩ : syracuseStep 645095 = 967643) B967643
theorem B645113 : Blo 428775 645113 := bstep (se 2 (by rfl) ⟨241917, by rfl⟩ : syracuseStep 645113 = 483835) B483835
theorem B2185217 : Blo 428775 2185217 := bstep (se 2 (by rfl) ⟨819456, by rfl⟩ : syracuseStep 2185217 = 1638913) B1638913
theorem B645215 : Blo 428775 645215 := bstep (se 1 (by rfl) ⟨483911, by rfl⟩ : syracuseStep 645215 = 967823) B967823
theorem B776287 : Blo 428775 776287 := bstep (se 1 (by rfl) ⟨582215, by rfl⟩ : syracuseStep 776287 = 1164431) B1164431
theorem B1038433 : Blo 428775 1038433 := bstep (se 2 (by rfl) ⟨389412, by rfl⟩ : syracuseStep 1038433 = 778825) B778825
theorem B645275 : Blo 428775 645275 := bstep (se 1 (by rfl) ⟨483956, by rfl⟩ : syracuseStep 645275 = 967913) B967913
theorem B645311 : Blo 428775 645311 := bstep (se 1 (by rfl) ⟨483983, by rfl⟩ : syracuseStep 645311 = 967967) B967967
theorem B645353 : Blo 428775 645353 := bstep (se 2 (by rfl) ⟨242007, by rfl⟩ : syracuseStep 645353 = 484015) B484015
theorem B973097 : Blo 428775 973097 := bstep (se 2 (by rfl) ⟨364911, by rfl⟩ : syracuseStep 973097 = 729823) B729823
theorem B7428631 : Blo 428775 7428631 := bstep (se 1 (by rfl) ⟨5571473, by rfl⟩ : syracuseStep 7428631 = 11142947) B11142947
theorem B645659 : Blo 428775 645659 := bstep (se 1 (by rfl) ⟨484244, by rfl⟩ : syracuseStep 645659 = 968489) B968489
theorem B645737 : Blo 428775 645737 := bstep (se 2 (by rfl) ⟨242151, by rfl⟩ : syracuseStep 645737 = 484303) B484303
theorem B2185865 : Blo 428775 2185865 := bstep (se 2 (by rfl) ⟨819699, by rfl⟩ : syracuseStep 2185865 = 1639399) B1639399
theorem B6314669 : Blo 428775 6314669 := bstep (se 3 (by rfl) ⟨1184000, by rfl⟩ : syracuseStep 6314669 = 2368001) B2368001
theorem B2186027 : Blo 428775 2186027 := bstep (se 1 (by rfl) ⟨1639520, by rfl⟩ : syracuseStep 2186027 = 3279041) B3279041
theorem B1629011 : Blo 428775 1629011 := bstep (se 1 (by rfl) ⟨1221758, by rfl⟩ : syracuseStep 1629011 = 2443517) B2443517
theorem B973673 : Blo 428775 973673 := bstep (se 2 (by rfl) ⟨365127, by rfl⟩ : syracuseStep 973673 = 730255) B730255
theorem B973727 : Blo 428775 973727 := bstep (se 1 (by rfl) ⟨730295, by rfl⟩ : syracuseStep 973727 = 1460591) B1460591
theorem B646265 : Blo 428775 646265 := bstep (se 2 (by rfl) ⟨242349, by rfl⟩ : syracuseStep 646265 = 484699) B484699
theorem B1662137 : Blo 428775 1662137 := bstep (se 2 (by rfl) ⟨623301, by rfl⟩ : syracuseStep 1662137 = 1246603) B1246603
theorem B646367 : Blo 428775 646367 := bstep (se 1 (by rfl) ⟨484775, by rfl⟩ : syracuseStep 646367 = 969551) B969551
theorem B646409 : Blo 428775 646409 := bstep (se 2 (by rfl) ⟨242403, by rfl⟩ : syracuseStep 646409 = 484807) B484807
theorem B1039625 : Blo 428775 1039625 := bstep (se 2 (by rfl) ⟨389859, by rfl⟩ : syracuseStep 1039625 = 779719) B779719
theorem B646511 : Blo 428775 646511 := bstep (se 1 (by rfl) ⟨484883, by rfl⟩ : syracuseStep 646511 = 969767) B969767
theorem B24141199 : Blo 428775 24141199 := bstep (se 1 (by rfl) ⟨18105899, by rfl⟩ : syracuseStep 24141199 = 36211799) B36211799
theorem B482791 : Blo 428775 482791 := bstep (se 1 (by rfl) ⟨362093, by rfl⟩ : syracuseStep 482791 = 724187) B724187
theorem B646631 : Blo 428775 646631 := bstep (se 1 (by rfl) ⟨484973, by rfl⟩ : syracuseStep 646631 = 969947) B969947
theorem B646763 : Blo 428775 646763 := bstep (se 1 (by rfl) ⟨485072, by rfl⟩ : syracuseStep 646763 = 970145) B970145
theorem B646889 : Blo 428775 646889 := bstep (se 2 (by rfl) ⟨242583, by rfl⟩ : syracuseStep 646889 = 485167) B485167
theorem B647033 : Blo 428775 647033 := bstep (se 2 (by rfl) ⟨242637, by rfl⟩ : syracuseStep 647033 = 485275) B485275
theorem B483295 : Blo 428775 483295 := bstep (se 1 (by rfl) ⟨362471, by rfl⟩ : syracuseStep 483295 = 724943) B724943
theorem B647135 : Blo 428775 647135 := bstep (se 1 (by rfl) ⟨485351, by rfl⟩ : syracuseStep 647135 = 970703) B970703
theorem B1663111 : Blo 428775 1663111 := bstep (se 1 (by rfl) ⟨1247333, by rfl⟩ : syracuseStep 1663111 = 2494667) B2494667
theorem B647387 : Blo 428775 647387 := bstep (se 1 (by rfl) ⟨485540, by rfl⟩ : syracuseStep 647387 = 971081) B971081
theorem B647399 : Blo 428775 647399 := bstep (se 1 (by rfl) ⟨485549, by rfl⟩ : syracuseStep 647399 = 971099) B971099
theorem B647561 : Blo 428775 647561 := bstep (se 2 (by rfl) ⟨242835, by rfl⟩ : syracuseStep 647561 = 485671) B485671
theorem B161014169 : Blo 428775 161014169 := bstep (se 2 (by rfl) ⟨60380313, by rfl⟩ : syracuseStep 161014169 = 120760627) B120760627
theorem B1630651 : Blo 428775 1630651 := bstep (se 1 (by rfl) ⟨1222988, by rfl⟩ : syracuseStep 1630651 = 2445977) B2445977
theorem B647657 : Blo 428775 647657 := bstep (se 2 (by rfl) ⟨242871, by rfl⟩ : syracuseStep 647657 = 485743) B485743
theorem B483943 : Blo 428775 483943 := bstep (se 1 (by rfl) ⟨362957, by rfl⟩ : syracuseStep 483943 = 725915) B725915
theorem B647783 : Blo 428775 647783 := bstep (se 1 (by rfl) ⟨485837, by rfl⟩ : syracuseStep 647783 = 971675) B971675
theorem B647915 : Blo 428775 647915 := bstep (se 1 (by rfl) ⟨485936, by rfl⟩ : syracuseStep 647915 = 971873) B971873
theorem B647945 : Blo 428775 647945 := bstep (se 2 (by rfl) ⟨242979, by rfl⟩ : syracuseStep 647945 = 485959) B485959
theorem B648047 : Blo 428775 648047 := bstep (se 1 (by rfl) ⟨486035, by rfl⟩ : syracuseStep 648047 = 972071) B972071
theorem B11035601 : Blo 428775 11035601 := bstep (se 2 (by rfl) ⟨4138350, by rfl⟩ : syracuseStep 11035601 = 8276701) B8276701
theorem B648299 : Blo 428775 648299 := bstep (se 1 (by rfl) ⟨486224, by rfl⟩ : syracuseStep 648299 = 972449) B972449
theorem B648539 : Blo 428775 648539 := bstep (se 1 (by rfl) ⟨486404, by rfl⟩ : syracuseStep 648539 = 972809) B972809
theorem B3302849 : Blo 428775 3302849 := bstep (se 2 (by rfl) ⟨1238568, by rfl⟩ : syracuseStep 3302849 = 2477137) B2477137
theorem B1467919 : Blo 428775 1467919 := bstep (se 1 (by rfl) ⟨1100939, by rfl⟩ : syracuseStep 1467919 = 2201879) B2201879
theorem B1304147 : Blo 428775 1304147 := bstep (se 1 (by rfl) ⟨978110, by rfl⟩ : syracuseStep 1304147 = 1956221) B1956221
theorem B648815 : Blo 428775 648815 := bstep (se 1 (by rfl) ⟨486611, by rfl⟩ : syracuseStep 648815 = 973223) B973223
theorem B550567 : Blo 428775 550567 := bstep (se 1 (by rfl) ⟨412925, by rfl⟩ : syracuseStep 550567 = 825851) B825851
theorem B648887 : Blo 428775 648887 := bstep (se 1 (by rfl) ⟨486665, by rfl⟩ : syracuseStep 648887 = 973331) B973331
theorem B648923 : Blo 428775 648923 := bstep (se 1 (by rfl) ⟨486692, by rfl⟩ : syracuseStep 648923 = 973385) B973385
theorem B649097 : Blo 428775 649097 := bstep (se 2 (by rfl) ⟨243411, by rfl⟩ : syracuseStep 649097 = 486823) B486823
theorem B1305119 : Blo 428775 1305119 := bstep (se 1 (by rfl) ⟨978839, by rfl⟩ : syracuseStep 1305119 = 1957679) B1957679
theorem B3108377 : Blo 428775 3108377 := bstep (se 2 (by rfl) ⟨1165641, by rfl⟩ : syracuseStep 3108377 = 2331283) B2331283
theorem B2453267 : Blo 428775 2453267 := bstep (se 1 (by rfl) ⟨1839950, by rfl⟩ : syracuseStep 2453267 = 3679901) B3679901
theorem B1570079 : Blo 428775 1570079 := bstep (se 1 (by rfl) ⟨1177559, by rfl⟩ : syracuseStep 1570079 = 2355119) B2355119
theorem B31782203 : Blo 428775 31782203 := bstep (se 1 (by rfl) ⟨23836652, by rfl⟩ : syracuseStep 31782203 = 47673305) B47673305
theorem B2454907 : Blo 428775 2454907 := bstep (se 1 (by rfl) ⟨1841180, by rfl⟩ : syracuseStep 2454907 = 3682361) B3682361
theorem B816959 : Blo 428775 816959 := bstep (se 1 (by rfl) ⟨612719, by rfl⟩ : syracuseStep 816959 = 1225439) B1225439
theorem B2455433 : Blo 428775 2455433 := bstep (se 2 (by rfl) ⟨920787, by rfl⟩ : syracuseStep 2455433 = 1841575) B1841575
theorem B1243279 : Blo 428775 1243279 := bstep (se 1 (by rfl) ⟨932459, by rfl⟩ : syracuseStep 1243279 = 1864919) B1864919
theorem B2128403 : Blo 428775 2128403 := bstep (se 1 (by rfl) ⟨1596302, by rfl⟩ : syracuseStep 2128403 = 3192605) B3192605
theorem B2751367 : Blo 428775 2751367 := bstep (se 1 (by rfl) ⟨2063525, by rfl⟩ : syracuseStep 2751367 = 4127051) B4127051
theorem B1244527 : Blo 428775 1244527 := bstep (se 1 (by rfl) ⟨933395, by rfl⟩ : syracuseStep 1244527 = 1866791) B1866791
theorem B818599 : Blo 428775 818599 := bstep (se 1 (by rfl) ⟨613949, by rfl⟩ : syracuseStep 818599 = 1227899) B1227899
theorem B687791 : Blo 428775 687791 := bstep (se 1 (by rfl) ⟨515843, by rfl⟩ : syracuseStep 687791 = 1031687) B1031687
theorem B1507513 : Blo 428775 1507513 := bstep (se 2 (by rfl) ⟨565317, by rfl⟩ : syracuseStep 1507513 = 1130635) B1130635
theorem B1868143 : Blo 428775 1868143 := bstep (se 1 (by rfl) ⟨1401107, by rfl⟩ : syracuseStep 1868143 = 2802215) B2802215
theorem B2065007 : Blo 428775 2065007 := bstep (se 1 (by rfl) ⟨1548755, by rfl⟩ : syracuseStep 2065007 = 3097511) B3097511
theorem B8389331 : Blo 428775 8389331 := bstep (se 1 (by rfl) ⟨6291998, by rfl⟩ : syracuseStep 8389331 = 12583997) B12583997
theorem B1377503 : Blo 428775 1377503 := bstep (se 1 (by rfl) ⟨1033127, by rfl⟩ : syracuseStep 1377503 = 2066255) B2066255
theorem B820459 : Blo 428775 820459 := bstep (se 1 (by rfl) ⟨615344, by rfl⟩ : syracuseStep 820459 = 1230689) B1230689
theorem B689771 : Blo 428775 689771 := bstep (se 1 (by rfl) ⟨517328, by rfl⟩ : syracuseStep 689771 = 1034657) B1034657
theorem B3278555 : Blo 428775 3278555 := bstep (se 1 (by rfl) ⟨2458916, by rfl⟩ : syracuseStep 3278555 = 4917833) B4917833
theorem B2623375 : Blo 428775 2623375 := bstep (se 1 (by rfl) ⟨1967531, by rfl⟩ : syracuseStep 2623375 = 3935063) B3935063
theorem B919583 : Blo 428775 919583 := bstep (se 1 (by rfl) ⟨689687, by rfl⟩ : syracuseStep 919583 = 1379375) B1379375
theorem B821279 : Blo 428775 821279 := bstep (se 1 (by rfl) ⟨615959, by rfl⟩ : syracuseStep 821279 = 1231919) B1231919
theorem B1837217 : Blo 428775 1837217 := bstep (se 2 (by rfl) ⟨688956, by rfl⟩ : syracuseStep 1837217 = 1377913) B1377913
theorem B657791 : Blo 428775 657791 := bstep (se 1 (by rfl) ⟨493343, by rfl⟩ : syracuseStep 657791 = 986687) B986687
theorem B1640843 : Blo 428775 1640843 := bstep (se 1 (by rfl) ⟨1230632, by rfl⟩ : syracuseStep 1640843 = 2461265) B2461265
theorem B723559 : Blo 428775 723559 := bstep (se 1 (by rfl) ⟨542669, by rfl⟩ : syracuseStep 723559 = 1085339) B1085339
theorem B429023 : Blo 428775 429023 := bstep (se 1 (by rfl) ⟨321767, by rfl⟩ : syracuseStep 429023 = 643535) B643535
theorem B429051 : Blo 428775 429051 := bstep (se 1 (by rfl) ⟨321788, by rfl⟩ : syracuseStep 429051 = 643577) B643577
theorem B429119 : Blo 428775 429119 := bstep (se 1 (by rfl) ⟨321839, by rfl⟩ : syracuseStep 429119 = 643679) B643679
theorem B724315 : Blo 428775 724315 := bstep (se 1 (by rfl) ⟨543236, by rfl⟩ : syracuseStep 724315 = 1086473) B1086473
theorem B1838447 : Blo 428775 1838447 := bstep (se 1 (by rfl) ⟨1378835, by rfl⟩ : syracuseStep 1838447 = 2757671) B2757671
theorem B429439 : Blo 428775 429439 := bstep (se 1 (by rfl) ⟨322079, by rfl⟩ : syracuseStep 429439 = 644159) B644159
theorem B429467 : Blo 428775 429467 := bstep (se 1 (by rfl) ⟨322100, by rfl⟩ : syracuseStep 429467 = 644201) B644201
theorem B429535 : Blo 428775 429535 := bstep (se 1 (by rfl) ⟨322151, by rfl⟩ : syracuseStep 429535 = 644303) B644303
theorem B429671 : Blo 428775 429671 := bstep (se 1 (by rfl) ⟨322253, by rfl⟩ : syracuseStep 429671 = 644507) B644507
theorem B133107313 : Blo 428775 133107313 := bstep (se 2 (by rfl) ⟨49915242, by rfl⟩ : syracuseStep 133107313 = 99830485) B99830485
theorem B3280499 : Blo 428775 3280499 := bstep (se 1 (by rfl) ⟨2460374, by rfl⟩ : syracuseStep 3280499 = 4920749) B4920749
theorem B429819 : Blo 428775 429819 := bstep (se 1 (by rfl) ⟨322364, by rfl⟩ : syracuseStep 429819 = 644729) B644729
theorem B429887 : Blo 428775 429887 := bstep (se 1 (by rfl) ⟨322415, by rfl⟩ : syracuseStep 429887 = 644831) B644831
theorem B429951 : Blo 428775 429951 := bstep (se 1 (by rfl) ⟨322463, by rfl⟩ : syracuseStep 429951 = 644927) B644927
theorem B430063 : Blo 428775 430063 := bstep (se 1 (by rfl) ⟨322547, by rfl⟩ : syracuseStep 430063 = 645095) B645095
theorem B430075 : Blo 428775 430075 := bstep (se 1 (by rfl) ⟨322556, by rfl⟩ : syracuseStep 430075 = 645113) B645113
theorem B430143 : Blo 428775 430143 := bstep (se 1 (by rfl) ⟨322607, by rfl⟩ : syracuseStep 430143 = 645215) B645215
theorem B430183 : Blo 428775 430183 := bstep (se 1 (by rfl) ⟨322637, by rfl⟩ : syracuseStep 430183 = 645275) B645275
theorem B430207 : Blo 428775 430207 := bstep (se 1 (by rfl) ⟨322655, by rfl⟩ : syracuseStep 430207 = 645311) B645311
theorem B430235 : Blo 428775 430235 := bstep (se 1 (by rfl) ⟨322676, by rfl⟩ : syracuseStep 430235 = 645353) B645353
theorem B3477725 : Blo 428775 3477725 := bstep (se 3 (by rfl) ⟨652073, by rfl⟩ : syracuseStep 3477725 = 1304147) B1304147
theorem B8261939 : Blo 428775 8261939 := bstep (se 1 (by rfl) ⟨6196454, by rfl⟩ : syracuseStep 8261939 = 12392909) B12392909
theorem B430439 : Blo 428775 430439 := bstep (se 1 (by rfl) ⟨322829, by rfl⟩ : syracuseStep 430439 = 645659) B645659
theorem B7868825 : Blo 428775 7868825 := bstep (se 2 (by rfl) ⟨2950809, by rfl⟩ : syracuseStep 7868825 = 5901619) B5901619
theorem B430491 : Blo 428775 430491 := bstep (se 1 (by rfl) ⟨322868, by rfl⟩ : syracuseStep 430491 = 645737) B645737
theorem B922043 : Blo 428775 922043 := bstep (se 1 (by rfl) ⟨691532, by rfl⟩ : syracuseStep 922043 = 1383065) B1383065
theorem B8425957 : Blo 428775 8425957 := bstep (se 4 (by rfl) ⟨789933, by rfl⟩ : syracuseStep 8425957 = 1579867) B1579867
theorem B1086007 : Blo 428775 1086007 := bstep (se 1 (by rfl) ⟨814505, by rfl⟩ : syracuseStep 1086007 = 1629011) B1629011
theorem B430843 : Blo 428775 430843 := bstep (se 1 (by rfl) ⟨323132, by rfl⟩ : syracuseStep 430843 = 646265) B646265
theorem B430911 : Blo 428775 430911 := bstep (se 1 (by rfl) ⟨323183, by rfl⟩ : syracuseStep 430911 = 646367) B646367
theorem B430939 : Blo 428775 430939 := bstep (se 1 (by rfl) ⟨323204, by rfl⟩ : syracuseStep 430939 = 646409) B646409
theorem B693083 : Blo 428775 693083 := bstep (se 1 (by rfl) ⟨519812, by rfl⟩ : syracuseStep 693083 = 1039625) B1039625
theorem B431007 : Blo 428775 431007 := bstep (se 1 (by rfl) ⟨323255, by rfl⟩ : syracuseStep 431007 = 646511) B646511
theorem B431087 : Blo 428775 431087 := bstep (se 1 (by rfl) ⟨323315, by rfl⟩ : syracuseStep 431087 = 646631) B646631
theorem B922607 : Blo 428775 922607 := bstep (se 1 (by rfl) ⟨691955, by rfl⟩ : syracuseStep 922607 = 1383911) B1383911
theorem B431175 : Blo 428775 431175 := bstep (se 1 (by rfl) ⟨323381, by rfl⟩ : syracuseStep 431175 = 646763) B646763
theorem B431259 : Blo 428775 431259 := bstep (se 1 (by rfl) ⟨323444, by rfl⟩ : syracuseStep 431259 = 646889) B646889
theorem B431355 : Blo 428775 431355 := bstep (se 1 (by rfl) ⟨323516, by rfl⟩ : syracuseStep 431355 = 647033) B647033
theorem B726313 : Blo 428775 726313 := bstep (se 2 (by rfl) ⟨272367, by rfl⟩ : syracuseStep 726313 = 544735) B544735
theorem B431423 : Blo 428775 431423 := bstep (se 1 (by rfl) ⟨323567, by rfl⟩ : syracuseStep 431423 = 647135) B647135
theorem B431591 : Blo 428775 431591 := bstep (se 1 (by rfl) ⟨323693, by rfl⟩ : syracuseStep 431591 = 647387) B647387
theorem B431599 : Blo 428775 431599 := bstep (se 1 (by rfl) ⟨323699, by rfl⟩ : syracuseStep 431599 = 647399) B647399
theorem B431707 : Blo 428775 431707 := bstep (se 1 (by rfl) ⟨323780, by rfl⟩ : syracuseStep 431707 = 647561) B647561
theorem B431771 : Blo 428775 431771 := bstep (se 1 (by rfl) ⟨323828, by rfl⟩ : syracuseStep 431771 = 647657) B647657
theorem B431855 : Blo 428775 431855 := bstep (se 1 (by rfl) ⟨323891, by rfl⟩ : syracuseStep 431855 = 647783) B647783
theorem B431943 : Blo 428775 431943 := bstep (se 1 (by rfl) ⟨323957, by rfl⟩ : syracuseStep 431943 = 647915) B647915
theorem B431963 : Blo 428775 431963 := bstep (se 1 (by rfl) ⟨323972, by rfl⟩ : syracuseStep 431963 = 647945) B647945
theorem B726907 : Blo 428775 726907 := bstep (se 1 (by rfl) ⟨545180, by rfl⟩ : syracuseStep 726907 = 1090361) B1090361
theorem B5248891 : Blo 428775 5248891 := bstep (se 1 (by rfl) ⟨3936668, by rfl⟩ : syracuseStep 5248891 = 7873337) B7873337
theorem B432031 : Blo 428775 432031 := bstep (se 1 (by rfl) ⟨324023, by rfl⟩ : syracuseStep 432031 = 648047) B648047
theorem B7837721 : Blo 428775 7837721 := bstep (se 2 (by rfl) ⟨2939145, by rfl⟩ : syracuseStep 7837721 = 5878291) B5878291
theorem B432199 : Blo 428775 432199 := bstep (se 1 (by rfl) ⟨324149, by rfl⟩ : syracuseStep 432199 = 648299) B648299
theorem B4135049 : Blo 428775 4135049 := bstep (se 2 (by rfl) ⟨1550643, by rfl⟩ : syracuseStep 4135049 = 3101287) B3101287
theorem B727177 : Blo 428775 727177 := bstep (se 2 (by rfl) ⟨272691, by rfl⟩ : syracuseStep 727177 = 545383) B545383
theorem B432359 : Blo 428775 432359 := bstep (se 1 (by rfl) ⟨324269, by rfl⟩ : syracuseStep 432359 = 648539) B648539
theorem B2201899 : Blo 428775 2201899 := bstep (se 1 (by rfl) ⟨1651424, by rfl⟩ : syracuseStep 2201899 = 3302849) B3302849
theorem B432543 : Blo 428775 432543 := bstep (se 1 (by rfl) ⟨324407, by rfl⟩ : syracuseStep 432543 = 648815) B648815
theorem B3676589 : Blo 428775 3676589 := bstep (se 3 (by rfl) ⟨689360, by rfl⟩ : syracuseStep 3676589 = 1378721) B1378721
theorem B432591 : Blo 428775 432591 := bstep (se 1 (by rfl) ⟨324443, by rfl⟩ : syracuseStep 432591 = 648887) B648887
theorem B432615 : Blo 428775 432615 := bstep (se 1 (by rfl) ⟨324461, by rfl⟩ : syracuseStep 432615 = 648923) B648923
theorem B432731 : Blo 428775 432731 := bstep (se 1 (by rfl) ⟨324548, by rfl⟩ : syracuseStep 432731 = 649097) B649097
theorem B5675741 : Blo 428775 5675741 := bstep (se 3 (by rfl) ⟨1064201, by rfl⟩ : syracuseStep 5675741 = 2128403) B2128403
theorem B3480317 : Blo 428775 3480317 := bstep (se 3 (by rfl) ⟨652559, by rfl⟩ : syracuseStep 3480317 = 1305119) B1305119
theorem B727879 : Blo 428775 727879 := bstep (se 1 (by rfl) ⟨545909, by rfl⟩ : syracuseStep 727879 = 1091819) B1091819
theorem B2072137 : Blo 428775 2072137 := bstep (se 2 (by rfl) ⟨777051, by rfl⟩ : syracuseStep 2072137 = 1554103) B1554103
theorem B728743 : Blo 428775 728743 := bstep (se 1 (by rfl) ⟨546557, by rfl⟩ : syracuseStep 728743 = 1093115) B1093115
theorem B2072251 : Blo 428775 2072251 := bstep (se 1 (by rfl) ⟨1554188, by rfl⟩ : syracuseStep 2072251 = 3108377) B3108377
theorem B2760439 : Blo 428775 2760439 := bstep (se 1 (by rfl) ⟨2070329, by rfl⟩ : syracuseStep 2760439 = 4140659) B4140659
theorem B1384577 : Blo 428775 1384577 := bstep (se 2 (by rfl) ⟨519216, by rfl⟩ : syracuseStep 1384577 = 1038433) B1038433
theorem B9904841 : Blo 428775 9904841 := bstep (se 2 (by rfl) ⟨3714315, by rfl⟩ : syracuseStep 9904841 = 7428631) B7428631
theorem B729911 : Blo 428775 729911 := bstep (se 1 (by rfl) ⟨547433, by rfl⟩ : syracuseStep 729911 = 1094867) B1094867
theorem B3941419 : Blo 428775 3941419 := bstep (se 1 (by rfl) ⟨2956064, by rfl⟩ : syracuseStep 3941419 = 5912129) B5912129
theorem B32188265 : Blo 428775 32188265 := bstep (se 2 (by rfl) ⟨12070599, by rfl⟩ : syracuseStep 32188265 = 24141199) B24141199
theorem B1091465 : Blo 428775 1091465 := bstep (se 2 (by rfl) ⟨409299, by rfl⟩ : syracuseStep 1091465 = 818599) B818599
theorem B1452059 : Blo 428775 1452059 := bstep (se 1 (by rfl) ⟨1089044, by rfl⟩ : syracuseStep 1452059 = 2178089) B2178089
theorem B1550441 : Blo 428775 1550441 := bstep (se 2 (by rfl) ⟨581415, by rfl⟩ : syracuseStep 1550441 = 1162831) B1162831
theorem B1452221 : Blo 428775 1452221 := bstep (se 3 (by rfl) ⟨272291, by rfl⟩ : syracuseStep 1452221 = 544583) B544583
theorem B5319431 : Blo 428775 5319431 := bstep (se 1 (by rfl) ⟨3989573, by rfl⟩ : syracuseStep 5319431 = 7979147) B7979147
theorem B1846223 : Blo 428775 1846223 := bstep (se 1 (by rfl) ⟨1384667, by rfl⟩ : syracuseStep 1846223 = 2769335) B2769335
theorem B1092649 : Blo 428775 1092649 := bstep (se 2 (by rfl) ⟨409743, by rfl⟩ : syracuseStep 1092649 = 819487) B819487
theorem B4140197 : Blo 428775 4140197 := bstep (se 4 (by rfl) ⟨388143, by rfl⟩ : syracuseStep 4140197 = 776287) B776287
theorem B2174201 : Blo 428775 2174201 := bstep (se 2 (by rfl) ⟨815325, by rfl⟩ : syracuseStep 2174201 = 1630651) B1630651
theorem B1846547 : Blo 428775 1846547 := bstep (se 1 (by rfl) ⟨1384910, by rfl⟩ : syracuseStep 1846547 = 2769821) B2769821
theorem B2174363 : Blo 428775 2174363 := bstep (se 1 (by rfl) ⟨1630772, by rfl⟩ : syracuseStep 2174363 = 3261545) B3261545
theorem B5222033 : Blo 428775 5222033 := bstep (se 2 (by rfl) ⟨1958262, by rfl⟩ : syracuseStep 5222033 = 3916525) B3916525
theorem B16494353 : Blo 428775 16494353 := bstep (se 2 (by rfl) ⟨6185382, by rfl⟩ : syracuseStep 16494353 = 12370765) B12370765
theorem B1093439 : Blo 428775 1093439 := bstep (se 1 (by rfl) ⟨820079, by rfl⟩ : syracuseStep 1093439 = 1640159) B1640159
theorem B1453949 : Blo 428775 1453949 := bstep (se 3 (by rfl) ⟨272615, by rfl⟩ : syracuseStep 1453949 = 545231) B545231
theorem B1454219 : Blo 428775 1454219 := bstep (se 1 (by rfl) ⟨1090664, by rfl⟩ : syracuseStep 1454219 = 2181329) B2181329
theorem B1094087 : Blo 428775 1094087 := bstep (se 1 (by rfl) ⟨820565, by rfl⟩ : syracuseStep 1094087 = 1641131) B1641131
theorem B2077559 : Blo 428775 2077559 := bstep (se 1 (by rfl) ⟨1558169, by rfl⟩ : syracuseStep 2077559 = 3116339) B3116339
theorem B734089 : Blo 428775 734089 := bstep (se 2 (by rfl) ⟨275283, by rfl⟩ : syracuseStep 734089 = 550567) B550567
theorem B15774695 : Blo 428775 15774695 := bstep (se 1 (by rfl) ⟨11831021, by rfl⟩ : syracuseStep 15774695 = 23662043) B23662043
theorem B1160443 : Blo 428775 1160443 := bstep (se 1 (by rfl) ⟨870332, by rfl⟩ : syracuseStep 1160443 = 1740665) B1740665
theorem B1455731 : Blo 428775 1455731 := bstep (se 1 (by rfl) ⟨1091798, by rfl⟩ : syracuseStep 1455731 = 2183597) B2183597
theorem B1652395 : Blo 428775 1652395 := bstep (se 1 (by rfl) ⟨1239296, by rfl⟩ : syracuseStep 1652395 = 2478593) B2478593
theorem B2209451 : Blo 428775 2209451 := bstep (se 1 (by rfl) ⟨1657088, by rfl⟩ : syracuseStep 2209451 = 3314177) B3314177
theorem B1455839 : Blo 428775 1455839 := bstep (se 1 (by rfl) ⟨1091879, by rfl⟩ : syracuseStep 1455839 = 2183759) B2183759
theorem B1456001 : Blo 428775 1456001 := bstep (se 2 (by rfl) ⟨546000, by rfl⟩ : syracuseStep 1456001 = 1092001) B1092001
theorem B6961153 : Blo 428775 6961153 := bstep (se 2 (by rfl) ⟨2610432, by rfl⟩ : syracuseStep 6961153 = 5220865) B5220865
theorem B964799 : Blo 428775 964799 := bstep (se 1 (by rfl) ⟨723599, by rfl⟩ : syracuseStep 964799 = 1447199) B1447199
theorem B1456541 : Blo 428775 1456541 := bstep (se 3 (by rfl) ⟨273101, by rfl⟩ : syracuseStep 1456541 = 546203) B546203
theorem B1456811 : Blo 428775 1456811 := bstep (se 1 (by rfl) ⟨1092608, by rfl⟩ : syracuseStep 1456811 = 2185217) B2185217
theorem B1457243 : Blo 428775 1457243 := bstep (se 1 (by rfl) ⟨1092932, by rfl⟩ : syracuseStep 1457243 = 2185865) B2185865
theorem B4209779 : Blo 428775 4209779 := bstep (se 1 (by rfl) ⟨3157334, by rfl⟩ : syracuseStep 4209779 = 6314669) B6314669
theorem B1457351 : Blo 428775 1457351 := bstep (se 1 (by rfl) ⟨1093013, by rfl⟩ : syracuseStep 1457351 = 2186027) B2186027
theorem B1031399 : Blo 428775 1031399 := bstep (se 1 (by rfl) ⟨773549, by rfl⟩ : syracuseStep 1031399 = 1547099) B1547099
theorem B933289 : Blo 428775 933289 := bstep (se 2 (by rfl) ⟨349983, by rfl⟩ : syracuseStep 933289 = 699967) B699967
theorem B966059 : Blo 428775 966059 := bstep (se 1 (by rfl) ⟨724544, by rfl⟩ : syracuseStep 966059 = 1449089) B1449089
theorem B966095 : Blo 428775 966095 := bstep (se 1 (by rfl) ⟨724571, by rfl⟩ : syracuseStep 966095 = 1449143) B1449143
theorem B966599 : Blo 428775 966599 := bstep (se 1 (by rfl) ⟨724949, by rfl⟩ : syracuseStep 966599 = 1449899) B1449899
theorem B1753069 : Blo 428775 1753069 := bstep (se 3 (by rfl) ⟨328700, by rfl⟩ : syracuseStep 1753069 = 657401) B657401
theorem B6209783 : Blo 428775 6209783 := bstep (se 1 (by rfl) ⟨4657337, by rfl⟩ : syracuseStep 6209783 = 9314675) B9314675
theorem B966905 : Blo 428775 966905 := bstep (se 2 (by rfl) ⟨362589, by rfl⟩ : syracuseStep 966905 = 725179) B725179
theorem B966959 : Blo 428775 966959 := bstep (se 1 (by rfl) ⟨725219, by rfl⟩ : syracuseStep 966959 = 1450439) B1450439
theorem B2998781 : Blo 428775 2998781 := bstep (se 3 (by rfl) ⟨562271, by rfl⟩ : syracuseStep 2998781 = 1124543) B1124543
theorem B967175 : Blo 428775 967175 := bstep (se 1 (by rfl) ⟨725381, by rfl⟩ : syracuseStep 967175 = 1450763) B1450763
theorem B7357067 : Blo 428775 7357067 := bstep (se 1 (by rfl) ⟨5517800, by rfl⟩ : syracuseStep 7357067 = 11035601) B11035601
theorem B967355 : Blo 428775 967355 := bstep (se 1 (by rfl) ⟨725516, by rfl⟩ : syracuseStep 967355 = 1451033) B1451033
theorem B967787 : Blo 428775 967787 := bstep (se 1 (by rfl) ⟨725840, by rfl⟩ : syracuseStep 967787 = 1451681) B1451681
theorem B968255 : Blo 428775 968255 := bstep (se 1 (by rfl) ⟨726191, by rfl⟩ : syracuseStep 968255 = 1452383) B1452383
theorem B968363 : Blo 428775 968363 := bstep (se 1 (by rfl) ⟨726272, by rfl⟩ : syracuseStep 968363 = 1452545) B1452545
theorem B6637477 : Blo 428775 6637477 := bstep (se 4 (by rfl) ⟨622263, by rfl⟩ : syracuseStep 6637477 = 1244527) B1244527
theorem B968687 : Blo 428775 968687 := bstep (se 1 (by rfl) ⟨726515, by rfl⟩ : syracuseStep 968687 = 1453031) B1453031
theorem B968903 : Blo 428775 968903 := bstep (se 1 (by rfl) ⟨726677, by rfl⟩ : syracuseStep 968903 = 1453355) B1453355
theorem B969083 : Blo 428775 969083 := bstep (se 1 (by rfl) ⟨726812, by rfl⟩ : syracuseStep 969083 = 1453625) B1453625
theorem B3263003 : Blo 428775 3263003 := bstep (se 1 (by rfl) ⟨2447252, by rfl⟩ : syracuseStep 3263003 = 4894505) B4894505
theorem B1231463 : Blo 428775 1231463 := bstep (se 1 (by rfl) ⟨923597, by rfl⟩ : syracuseStep 1231463 = 1847195) B1847195
theorem B969353 : Blo 428775 969353 := bstep (se 2 (by rfl) ⟨363507, by rfl⟩ : syracuseStep 969353 = 727015) B727015
theorem B1657705 : Blo 428775 1657705 := bstep (se 2 (by rfl) ⟨621639, by rfl⟩ : syracuseStep 1657705 = 1243279) B1243279
theorem B969641 : Blo 428775 969641 := bstep (se 2 (by rfl) ⟨363615, by rfl⟩ : syracuseStep 969641 = 727231) B727231
theorem B21188135 : Blo 428775 21188135 := bstep (se 1 (by rfl) ⟨15891101, by rfl⟩ : syracuseStep 21188135 = 31782203) B31782203
theorem B970343 : Blo 428775 970343 := bstep (se 1 (by rfl) ⟨727757, by rfl⟩ : syracuseStep 970343 = 1455515) B1455515
theorem B544639 : Blo 428775 544639 := bstep (se 1 (by rfl) ⟨408479, by rfl⟩ : syracuseStep 544639 = 816959) B816959
theorem B970847 : Blo 428775 970847 := bstep (se 1 (by rfl) ⟨728135, by rfl⟩ : syracuseStep 970847 = 1456271) B1456271
theorem B643175 : Blo 428775 643175 := bstep (se 1 (by rfl) ⟨482381, by rfl⟩ : syracuseStep 643175 = 964763) B964763
theorem B774299 : Blo 428775 774299 := bstep (se 1 (by rfl) ⟨580724, by rfl⟩ : syracuseStep 774299 = 1161449) B1161449
theorem B643247 : Blo 428775 643247 := bstep (se 1 (by rfl) ⟨482435, by rfl⟩ : syracuseStep 643247 = 964871) B964871
theorem B643451 : Blo 428775 643451 := bstep (se 1 (by rfl) ⟨482588, by rfl⟩ : syracuseStep 643451 = 965177) B965177
theorem B643721 : Blo 428775 643721 := bstep (se 2 (by rfl) ⟨241395, by rfl⟩ : syracuseStep 643721 = 482791) B482791
theorem B971603 : Blo 428775 971603 := bstep (se 1 (by rfl) ⟨728702, by rfl⟩ : syracuseStep 971603 = 1457405) B1457405
theorem B643931 : Blo 428775 643931 := bstep (se 1 (by rfl) ⟨482948, by rfl⟩ : syracuseStep 643931 = 965897) B965897
theorem B7361441 : Blo 428775 7361441 := bstep (se 2 (by rfl) ⟨2760540, by rfl⟩ : syracuseStep 7361441 = 5521081) B5521081
theorem B644393 : Blo 428775 644393 := bstep (se 2 (by rfl) ⟨241647, by rfl⟩ : syracuseStep 644393 = 483295) B483295
theorem B972143 : Blo 428775 972143 := bstep (se 1 (by rfl) ⟨729107, by rfl⟩ : syracuseStep 972143 = 1458215) B1458215
theorem B644591 : Blo 428775 644591 := bstep (se 1 (by rfl) ⟨483443, by rfl⟩ : syracuseStep 644591 = 966887) B966887
theorem B972575 : Blo 428775 972575 := bstep (se 1 (by rfl) ⟨729431, by rfl⟩ : syracuseStep 972575 = 1458863) B1458863
theorem B1038203 : Blo 428775 1038203 := bstep (se 1 (by rfl) ⟨778652, by rfl⟩ : syracuseStep 1038203 = 1557305) B1557305
theorem B644987 : Blo 428775 644987 := bstep (se 1 (by rfl) ⟨483740, by rfl⟩ : syracuseStep 644987 = 967481) B967481
theorem B1857437 : Blo 428775 1857437 := bstep (se 3 (by rfl) ⟨348269, by rfl⟩ : syracuseStep 1857437 = 696539) B696539
theorem B645023 : Blo 428775 645023 := bstep (se 1 (by rfl) ⟨483767, by rfl⟩ : syracuseStep 645023 = 967535) B967535
theorem B972791 : Blo 428775 972791 := bstep (se 1 (by rfl) ⟨729593, by rfl⟩ : syracuseStep 972791 = 1459187) B1459187
theorem B8869925 : Blo 428775 8869925 := bstep (se 4 (by rfl) ⟨831555, by rfl⟩ : syracuseStep 8869925 = 1663111) B1663111
theorem B1169447 : Blo 428775 1169447 := bstep (se 1 (by rfl) ⟨877085, by rfl⟩ : syracuseStep 1169447 = 1754171) B1754171
theorem B645257 : Blo 428775 645257 := bstep (se 2 (by rfl) ⟨241971, by rfl⟩ : syracuseStep 645257 = 483943) B483943
theorem B645407 : Blo 428775 645407 := bstep (se 1 (by rfl) ⟨484055, by rfl⟩ : syracuseStep 645407 = 968111) B968111
theorem B973151 : Blo 428775 973151 := bstep (se 1 (by rfl) ⟨729863, by rfl⟩ : syracuseStep 973151 = 1459727) B1459727
theorem B3103073 : Blo 428775 3103073 := bstep (se 2 (by rfl) ⟨1163652, by rfl⟩ : syracuseStep 3103073 = 2327305) B2327305
theorem B1628525 : Blo 428775 1628525 := bstep (se 3 (by rfl) ⟨305348, by rfl⟩ : syracuseStep 1628525 = 610697) B610697
theorem B547231 : Blo 428775 547231 := bstep (se 1 (by rfl) ⟨410423, by rfl⟩ : syracuseStep 547231 = 820847) B820847
theorem B2447891 : Blo 428775 2447891 := bstep (se 1 (by rfl) ⟨1835918, by rfl⟩ : syracuseStep 2447891 = 3671837) B3671837
theorem B4413971 : Blo 428775 4413971 := bstep (se 1 (by rfl) ⟨3310478, by rfl⟩ : syracuseStep 4413971 = 6620957) B6620957
theorem B645959 : Blo 428775 645959 := bstep (se 1 (by rfl) ⟨484469, by rfl⟩ : syracuseStep 645959 = 968939) B968939
theorem B973691 : Blo 428775 973691 := bstep (se 1 (by rfl) ⟨730268, by rfl⟩ : syracuseStep 973691 = 1460537) B1460537
theorem B482395 : Blo 428775 482395 := bstep (se 1 (by rfl) ⟨361796, by rfl⟩ : syracuseStep 482395 = 723593) B723593
theorem B1957225 : Blo 428775 1957225 := bstep (se 2 (by rfl) ⟨733959, by rfl⟩ : syracuseStep 1957225 = 1467919) B1467919
theorem B4677097 : Blo 428775 4677097 := bstep (se 2 (by rfl) ⟨1753911, by rfl⟩ : syracuseStep 4677097 = 3507823) B3507823
theorem B646823 : Blo 428775 646823 := bstep (se 1 (by rfl) ⟨485117, by rfl⟩ : syracuseStep 646823 = 970235) B970235
theorem B1629983 : Blo 428775 1629983 := bstep (se 1 (by rfl) ⟨1222487, by rfl⟩ : syracuseStep 1629983 = 2444975) B2444975
theorem B646943 : Blo 428775 646943 := bstep (se 1 (by rfl) ⟨485207, by rfl⟩ : syracuseStep 646943 = 970415) B970415
theorem B516007 : Blo 428775 516007 := bstep (se 1 (by rfl) ⟨387005, by rfl⟩ : syracuseStep 516007 = 774011) B774011
theorem B647375 : Blo 428775 647375 := bstep (se 1 (by rfl) ⟨485531, by rfl⟩ : syracuseStep 647375 = 971063) B971063
theorem B483583 : Blo 428775 483583 := bstep (se 1 (by rfl) ⟨362687, by rfl⟩ : syracuseStep 483583 = 725375) B725375
theorem B647423 : Blo 428775 647423 := bstep (se 1 (by rfl) ⟨485567, by rfl⟩ : syracuseStep 647423 = 971135) B971135
theorem B483871 : Blo 428775 483871 := bstep (se 1 (by rfl) ⟨362903, by rfl⟩ : syracuseStep 483871 = 725807) B725807
theorem B2351783 : Blo 428775 2351783 := bstep (se 1 (by rfl) ⟨1763837, by rfl⟩ : syracuseStep 2351783 = 3527675) B3527675
theorem B1630955 : Blo 428775 1630955 := bstep (se 1 (by rfl) ⟨1223216, by rfl⟩ : syracuseStep 1630955 = 2446433) B2446433
theorem B4121401 : Blo 428775 4121401 := bstep (se 2 (by rfl) ⟨1545525, by rfl⟩ : syracuseStep 4121401 = 3091051) B3091051
theorem B648239 : Blo 428775 648239 := bstep (se 1 (by rfl) ⟨486179, by rfl⟩ : syracuseStep 648239 = 972359) B972359
theorem B484519 : Blo 428775 484519 := bstep (se 1 (by rfl) ⟨363389, by rfl⟩ : syracuseStep 484519 = 726779) B726779
theorem B648359 : Blo 428775 648359 := bstep (se 1 (by rfl) ⟨486269, by rfl⟩ : syracuseStep 648359 = 972539) B972539
theorem B648731 : Blo 428775 648731 := bstep (se 1 (by rfl) ⟨486548, by rfl⟩ : syracuseStep 648731 = 973097) B973097
theorem B1894013 : Blo 428775 1894013 := bstep (se 3 (by rfl) ⟨355127, by rfl⟩ : syracuseStep 1894013 = 710255) B710255
theorem B1631897 : Blo 428775 1631897 := bstep (se 2 (by rfl) ⟨611961, by rfl⟩ : syracuseStep 1631897 = 1223923) B1223923
theorem B649115 : Blo 428775 649115 := bstep (se 1 (by rfl) ⟨486836, by rfl⟩ : syracuseStep 649115 = 973673) B973673
theorem B485311 : Blo 428775 485311 := bstep (se 1 (by rfl) ⟨363983, by rfl⟩ : syracuseStep 485311 = 727967) B727967
theorem B649151 : Blo 428775 649151 := bstep (se 1 (by rfl) ⟨486863, by rfl⟩ : syracuseStep 649151 = 973727) B973727
theorem B4909085 : Blo 428775 4909085 := bstep (se 3 (by rfl) ⟨920453, by rfl⟩ : syracuseStep 4909085 = 1840907) B1840907
theorem B1108091 : Blo 428775 1108091 := bstep (se 1 (by rfl) ⟨831068, by rfl⟩ : syracuseStep 1108091 = 1662137) B1662137
theorem B485599 : Blo 428775 485599 := bstep (se 1 (by rfl) ⟨364199, by rfl⟩ : syracuseStep 485599 = 728399) B728399
theorem B107342779 : Blo 428775 107342779 := bstep (se 1 (by rfl) ⟨80507084, by rfl⟩ : syracuseStep 107342779 = 161014169) B161014169
theorem B486463 : Blo 428775 486463 := bstep (se 1 (by rfl) ⟨364847, by rfl⟩ : syracuseStep 486463 = 729695) B729695
theorem B2453975 : Blo 428775 2453975 := bstep (se 1 (by rfl) ⟨1840481, by rfl⟩ : syracuseStep 2453975 = 3680963) B3680963
theorem B3273209 : Blo 428775 3273209 := bstep (se 2 (by rfl) ⟨1227453, by rfl⟩ : syracuseStep 3273209 = 2454907) B2454907
theorem B2061065 : Blo 428775 2061065 := bstep (se 2 (by rfl) ⟨772899, by rfl⟩ : syracuseStep 2061065 = 1545799) B1545799
theorem B816169 : Blo 428775 816169 := bstep (se 2 (by rfl) ⟨306063, by rfl⟩ : syracuseStep 816169 = 612127) B612127
theorem B1635511 : Blo 428775 1635511 := bstep (se 1 (by rfl) ⟨1226633, by rfl⟩ : syracuseStep 1635511 = 2453267) B2453267
theorem B1046719 : Blo 428775 1046719 := bstep (se 1 (by rfl) ⟨785039, by rfl⟩ : syracuseStep 1046719 = 1570079) B1570079
theorem B2062547 : Blo 428775 2062547 := bstep (se 1 (by rfl) ⟨1546910, by rfl⟩ : syracuseStep 2062547 = 3093821) B3093821
theorem B3668489 : Blo 428775 3668489 := bstep (se 2 (by rfl) ⟨1375683, by rfl⟩ : syracuseStep 3668489 = 2751367) B2751367
theorem B2652763 : Blo 428775 2652763 := bstep (se 1 (by rfl) ⟨1989572, by rfl⟩ : syracuseStep 2652763 = 3979145) B3979145
theorem B1636955 : Blo 428775 1636955 := bstep (se 1 (by rfl) ⟨1227716, by rfl⟩ : syracuseStep 1636955 = 2455433) B2455433
theorem B1636969 : Blo 428775 1636969 := bstep (se 2 (by rfl) ⟨613863, by rfl⟩ : syracuseStep 1636969 = 1227727) B1227727
theorem B2325449 : Blo 428775 2325449 := bstep (se 2 (by rfl) ⟨872043, by rfl⟩ : syracuseStep 2325449 = 1744087) B1744087
theorem B1834109 : Blo 428775 1834109 := bstep (se 3 (by rfl) ⟨343895, by rfl⟩ : syracuseStep 1834109 = 687791) B687791
theorem B884287 : Blo 428775 884287 := bstep (se 1 (by rfl) ⟨663215, by rfl⟩ : syracuseStep 884287 = 1326431) B1326431
theorem B1999187 : Blo 428775 1999187 := bstep (se 1 (by rfl) ⟨1499390, by rfl⟩ : syracuseStep 1999187 = 2998781) B2998781
theorem B1376671 : Blo 428775 1376671 := bstep (se 1 (by rfl) ⟨1032503, by rfl⟩ : syracuseStep 1376671 = 2065007) B2065007
theorem B2490857 : Blo 428775 2490857 := bstep (se 2 (by rfl) ⟨934071, by rfl⟩ : syracuseStep 2490857 = 1868143) B1868143
theorem B918335 : Blo 428775 918335 := bstep (se 1 (by rfl) ⟨688751, by rfl⟩ : syracuseStep 918335 = 1377503) B1377503
theorem B459847 : Blo 428775 459847 := bstep (se 1 (by rfl) ⟨344885, by rfl⟩ : syracuseStep 459847 = 689771) B689771
theorem B2458781 : Blo 428775 2458781 := bstep (se 3 (by rfl) ⟨461021, by rfl⟩ : syracuseStep 2458781 = 922043) B922043
theorem B14125423 : Blo 428775 14125423 := bstep (se 1 (by rfl) ⟨10594067, by rfl⟩ : syracuseStep 14125423 = 21188135) B21188135
theorem B8849969 : Blo 428775 8849969 := bstep (se 2 (by rfl) ⟨3318738, by rfl⟩ : syracuseStep 8849969 = 6637477) B6637477
theorem B428783 : Blo 428775 428783 := bstep (se 1 (by rfl) ⟨321587, by rfl⟩ : syracuseStep 428783 = 643175) B643175
theorem B428831 : Blo 428775 428831 := bstep (se 1 (by rfl) ⟨321623, by rfl⟩ : syracuseStep 428831 = 643247) B643247
theorem B5507959 : Blo 428775 5507959 := bstep (se 1 (by rfl) ⟨4130969, by rfl⟩ : syracuseStep 5507959 = 8261939) B8261939
theorem B428967 : Blo 428775 428967 := bstep (se 1 (by rfl) ⟨321725, by rfl⟩ : syracuseStep 428967 = 643451) B643451
theorem B5245883 : Blo 428775 5245883 := bstep (se 1 (by rfl) ⟨3934412, by rfl⟩ : syracuseStep 5245883 = 7868825) B7868825
theorem B429147 : Blo 428775 429147 := bstep (se 1 (by rfl) ⟨321860, by rfl⟩ : syracuseStep 429147 = 643721) B643721
theorem B429287 : Blo 428775 429287 := bstep (se 1 (by rfl) ⟨321965, by rfl⟩ : syracuseStep 429287 = 643931) B643931
theorem B429595 : Blo 428775 429595 := bstep (se 1 (by rfl) ⟨322196, by rfl⟩ : syracuseStep 429595 = 644393) B644393
theorem B429727 : Blo 428775 429727 := bstep (se 1 (by rfl) ⟨322295, by rfl⟩ : syracuseStep 429727 = 644591) B644591
theorem B429991 : Blo 428775 429991 := bstep (se 1 (by rfl) ⟨322493, by rfl⟩ : syracuseStep 429991 = 644987) B644987
theorem B692135 : Blo 428775 692135 := bstep (se 1 (by rfl) ⟨519101, by rfl⟩ : syracuseStep 692135 = 1038203) B1038203
theorem B430015 : Blo 428775 430015 := bstep (se 1 (by rfl) ⟨322511, by rfl⟩ : syracuseStep 430015 = 645023) B645023
theorem B430171 : Blo 428775 430171 := bstep (se 1 (by rfl) ⟨322628, by rfl⟩ : syracuseStep 430171 = 645257) B645257
theorem B2756699 : Blo 428775 2756699 := bstep (se 1 (by rfl) ⟨2067524, by rfl⟩ : syracuseStep 2756699 = 4135049) B4135049
theorem B430271 : Blo 428775 430271 := bstep (se 1 (by rfl) ⟨322703, by rfl⟩ : syracuseStep 430271 = 645407) B645407
theorem B2068715 : Blo 428775 2068715 := bstep (se 1 (by rfl) ⟨1551536, by rfl⟩ : syracuseStep 2068715 = 3103073) B3103073
theorem B1085683 : Blo 428775 1085683 := bstep (se 1 (by rfl) ⟨814262, by rfl⟩ : syracuseStep 1085683 = 1628525) B1628525
theorem B430639 : Blo 428775 430639 := bstep (se 1 (by rfl) ⟨322979, by rfl⟩ : syracuseStep 430639 = 645959) B645959
theorem B177476417 : Blo 428775 177476417 := bstep (se 2 (by rfl) ⟨66553656, by rfl⟩ : syracuseStep 177476417 = 133107313) B133107313
theorem B431215 : Blo 428775 431215 := bstep (se 1 (by rfl) ⟨323411, by rfl⟩ : syracuseStep 431215 = 646823) B646823
theorem B726185 : Blo 428775 726185 := bstep (se 2 (by rfl) ⟨272319, by rfl⟩ : syracuseStep 726185 = 544639) B544639
theorem B1086655 : Blo 428775 1086655 := bstep (se 1 (by rfl) ⟨814991, by rfl⟩ : syracuseStep 1086655 = 1629983) B1629983
theorem B431295 : Blo 428775 431295 := bstep (se 1 (by rfl) ⟨323471, by rfl⟩ : syracuseStep 431295 = 646943) B646943
theorem B923051 : Blo 428775 923051 := bstep (se 1 (by rfl) ⟨692288, by rfl⟩ : syracuseStep 923051 = 1384577) B1384577
theorem B431583 : Blo 428775 431583 := bstep (se 1 (by rfl) ⟨323687, by rfl⟩ : syracuseStep 431583 = 647375) B647375
theorem B431615 : Blo 428775 431615 := bstep (se 1 (by rfl) ⟨323711, by rfl⟩ : syracuseStep 431615 = 647423) B647423
theorem B4134509 : Blo 428775 4134509 := bstep (se 3 (by rfl) ⟨775220, by rfl⟩ : syracuseStep 4134509 = 1550441) B1550441
theorem B2954909 : Blo 428775 2954909 := bstep (se 3 (by rfl) ⟨554045, by rfl⟩ : syracuseStep 2954909 = 1108091) B1108091
theorem B1087303 : Blo 428775 1087303 := bstep (se 1 (by rfl) ⟨815477, by rfl⟩ : syracuseStep 1087303 = 1630955) B1630955
theorem B432159 : Blo 428775 432159 := bstep (se 1 (by rfl) ⟨324119, by rfl⟩ : syracuseStep 432159 = 648239) B648239
theorem B1448009 : Blo 428775 1448009 := bstep (se 2 (by rfl) ⟨543003, by rfl⟩ : syracuseStep 1448009 = 1086007) B1086007
theorem B432239 : Blo 428775 432239 := bstep (se 1 (by rfl) ⟨324179, by rfl⟩ : syracuseStep 432239 = 648359) B648359
theorem B432487 : Blo 428775 432487 := bstep (se 1 (by rfl) ⟨324365, by rfl⟩ : syracuseStep 432487 = 648731) B648731
theorem B1087931 : Blo 428775 1087931 := bstep (se 1 (by rfl) ⟨815948, by rfl⟩ : syracuseStep 1087931 = 1631897) B1631897
theorem B727643 : Blo 428775 727643 := bstep (se 1 (by rfl) ⟨545732, by rfl⟩ : syracuseStep 727643 = 1091465) B1091465
theorem B432743 : Blo 428775 432743 := bstep (se 1 (by rfl) ⟨324557, by rfl⟩ : syracuseStep 432743 = 649115) B649115
theorem B432767 : Blo 428775 432767 := bstep (se 1 (by rfl) ⟨324575, by rfl⟩ : syracuseStep 432767 = 649151) B649151
theorem B11770589 : Blo 428775 11770589 := bstep (se 3 (by rfl) ⟨2206985, by rfl⟩ : syracuseStep 11770589 = 4413971) B4413971
theorem B1088225 : Blo 428775 1088225 := bstep (se 2 (by rfl) ⟨408084, by rfl⟩ : syracuseStep 1088225 = 816169) B816169
theorem B3283901 : Blo 428775 3283901 := bstep (se 3 (by rfl) ⟨615731, by rfl⟩ : syracuseStep 3283901 = 1231463) B1231463
theorem B1547257 : Blo 428775 1547257 := bstep (se 2 (by rfl) ⟨580221, by rfl⟩ : syracuseStep 1547257 = 1160443) B1160443
theorem B3546287 : Blo 428775 3546287 := bstep (se 1 (by rfl) ⟨2659715, by rfl⟩ : syracuseStep 3546287 = 5319431) B5319431
theorem B2760131 : Blo 428775 2760131 := bstep (se 1 (by rfl) ⟨2070098, by rfl⟩ : syracuseStep 2760131 = 4140197) B4140197
theorem B1449467 : Blo 428775 1449467 := bstep (se 1 (by rfl) ⟨1087100, by rfl⟩ : syracuseStep 1449467 = 2174201) B2174201
theorem B2203193 : Blo 428775 2203193 := bstep (se 2 (by rfl) ⟨826197, by rfl⟩ : syracuseStep 2203193 = 1652395) B1652395
theorem B1449575 : Blo 428775 1449575 := bstep (se 1 (by rfl) ⟨1087181, by rfl⟩ : syracuseStep 1449575 = 2174363) B2174363
theorem B3481355 : Blo 428775 3481355 := bstep (se 1 (by rfl) ⟨2611016, by rfl⟩ : syracuseStep 3481355 = 5222033) B5222033
theorem B728959 : Blo 428775 728959 := bstep (se 1 (by rfl) ⟨546719, by rfl⟩ : syracuseStep 728959 = 1093439) B1093439
theorem B9281537 : Blo 428775 9281537 := bstep (se 2 (by rfl) ⟨3480576, by rfl⟩ : syracuseStep 9281537 = 6961153) B6961153
theorem B729391 : Blo 428775 729391 := bstep (se 1 (by rfl) ⟨547043, by rfl⟩ : syracuseStep 729391 = 1094087) B1094087
theorem B729641 : Blo 428775 729641 := bstep (se 2 (by rfl) ⟨273615, by rfl⟩ : syracuseStep 729641 = 547231) B547231
theorem B1385039 : Blo 428775 1385039 := bstep (se 1 (by rfl) ⟨1038779, by rfl⟩ : syracuseStep 1385039 = 2077559) B2077559
theorem B1091303 : Blo 428775 1091303 := bstep (se 1 (by rfl) ⟨818477, by rfl⟩ : syracuseStep 1091303 = 1636955) B1636955
theorem B1550299 : Blo 428775 1550299 := bstep (se 1 (by rfl) ⟨1162724, by rfl⟩ : syracuseStep 1550299 = 2325449) B2325449
theorem B6236129 : Blo 428775 6236129 := bstep (se 2 (by rfl) ⟨2338548, by rfl⟩ : syracuseStep 6236129 = 4677097) B4677097
theorem B1222739 : Blo 428775 1222739 := bstep (se 1 (by rfl) ⟨917054, by rfl⟩ : syracuseStep 1222739 = 1834109) B1834109
theorem B2762849 : Blo 428775 2762849 := bstep (se 2 (by rfl) ⟨1036068, by rfl⟩ : syracuseStep 2762849 = 2072137) B2072137
theorem B2763001 : Blo 428775 2763001 := bstep (se 2 (by rfl) ⟨1036125, by rfl⟩ : syracuseStep 2763001 = 2072251) B2072251
theorem B3680585 : Blo 428775 3680585 := bstep (se 2 (by rfl) ⟨1380219, by rfl⟩ : syracuseStep 3680585 = 2760439) B2760439
theorem B2337425 : Blo 428775 2337425 := bstep (se 2 (by rfl) ⟨876534, by rfl⟩ : syracuseStep 2337425 = 1753069) B1753069
theorem B4139855 : Blo 428775 4139855 := bstep (se 1 (by rfl) ⟨3104891, by rfl⟩ : syracuseStep 4139855 = 6209783) B6209783
theorem B2010017 : Blo 428775 2010017 := bstep (se 2 (by rfl) ⟨753756, by rfl⟩ : syracuseStep 2010017 = 1507513) B1507513
theorem B5255225 : Blo 428775 5255225 := bstep (se 2 (by rfl) ⟨1970709, by rfl⟩ : syracuseStep 5255225 = 3941419) B3941419
theorem B1224811 : Blo 428775 1224811 := bstep (se 1 (by rfl) ⟨918608, by rfl⟩ : syracuseStep 1224811 = 1837217) B1837217
theorem B438527 : Blo 428775 438527 := bstep (se 1 (by rfl) ⟨328895, by rfl⟩ : syracuseStep 438527 = 657791) B657791
theorem B1093895 : Blo 428775 1093895 := bstep (se 1 (by rfl) ⟨820421, by rfl⟩ : syracuseStep 1093895 = 1640843) B1640843
theorem B1093945 : Blo 428775 1093945 := bstep (se 2 (by rfl) ⟨410229, by rfl⟩ : syracuseStep 1093945 = 820459) B820459
theorem B2175335 : Blo 428775 2175335 := bstep (se 1 (by rfl) ⟨1631501, by rfl⟩ : syracuseStep 2175335 = 3263003) B3263003
theorem B1848221 : Blo 428775 1848221 := bstep (se 3 (by rfl) ⟨346541, by rfl⟩ : syracuseStep 1848221 = 693083) B693083
theorem B1225631 : Blo 428775 1225631 := bstep (se 1 (by rfl) ⟨919223, by rfl⟩ : syracuseStep 1225631 = 1838447) B1838447
theorem B964745 : Blo 428775 964745 := bstep (se 2 (by rfl) ⟨361779, by rfl⟩ : syracuseStep 964745 = 723559) B723559
theorem B2210273 : Blo 428775 2210273 := bstep (se 2 (by rfl) ⟨828852, by rfl⟩ : syracuseStep 2210273 = 1657705) B1657705
theorem B5225147 : Blo 428775 5225147 := bstep (se 1 (by rfl) ⟨3918860, by rfl⟩ : syracuseStep 5225147 = 7837721) B7837721
theorem B5913283 : Blo 428775 5913283 := bstep (se 1 (by rfl) ⟨4434962, by rfl⟩ : syracuseStep 5913283 = 8869925) B8869925
theorem B1456865 : Blo 428775 1456865 := bstep (se 2 (by rfl) ⟨546324, by rfl⟩ : syracuseStep 1456865 = 1092649) B1092649
theorem B965753 : Blo 428775 965753 := bstep (se 2 (by rfl) ⟨362157, by rfl⟩ : syracuseStep 965753 = 724315) B724315
theorem B3783827 : Blo 428775 3783827 := bstep (se 1 (by rfl) ⟨2837870, by rfl⟩ : syracuseStep 3783827 = 5675741) B5675741
theorem B6603227 : Blo 428775 6603227 := bstep (se 1 (by rfl) ⟨4952420, by rfl⟩ : syracuseStep 6603227 = 9904841) B9904841
theorem B1262675 : Blo 428775 1262675 := bstep (se 1 (by rfl) ⟨947006, by rfl⟩ : syracuseStep 1262675 = 1894013) B1894013
theorem B968039 : Blo 428775 968039 := bstep (se 1 (by rfl) ⟨726029, by rfl⟩ : syracuseStep 968039 = 1452059) B1452059
theorem B968147 : Blo 428775 968147 := bstep (se 1 (by rfl) ⟨726110, by rfl⟩ : syracuseStep 968147 = 1452221) B1452221
theorem B2180681 : Blo 428775 2180681 := bstep (se 2 (by rfl) ⟨817755, by rfl⟩ : syracuseStep 2180681 = 1635511) B1635511
theorem B968417 : Blo 428775 968417 := bstep (se 2 (by rfl) ⟨363156, by rfl⟩ : syracuseStep 968417 = 726313) B726313
theorem B1230815 : Blo 428775 1230815 := bstep (se 1 (by rfl) ⟨923111, by rfl⟩ : syracuseStep 1230815 = 1846223) B1846223
theorem B1231031 : Blo 428775 1231031 := bstep (se 1 (by rfl) ⟨923273, by rfl⟩ : syracuseStep 1231031 = 1846547) B1846547
theorem B969209 : Blo 428775 969209 := bstep (se 2 (by rfl) ⟨363453, by rfl⟩ : syracuseStep 969209 = 726907) B726907
theorem B6998521 : Blo 428775 6998521 := bstep (se 2 (by rfl) ⟨2624445, by rfl⟩ : syracuseStep 6998521 = 5248891) B5248891
theorem B10996235 : Blo 428775 10996235 := bstep (se 1 (by rfl) ⟨8247176, by rfl⟩ : syracuseStep 10996235 = 16494353) B16494353
theorem B969299 : Blo 428775 969299 := bstep (se 1 (by rfl) ⟨726974, by rfl⟩ : syracuseStep 969299 = 1453949) B1453949
theorem B969479 : Blo 428775 969479 := bstep (se 1 (by rfl) ⟨727109, by rfl⟩ : syracuseStep 969479 = 1454219) B1454219
theorem B969569 : Blo 428775 969569 := bstep (se 2 (by rfl) ⟨363588, by rfl⟩ : syracuseStep 969569 = 727177) B727177
theorem B1395625 : Blo 428775 1395625 := bstep (se 2 (by rfl) ⟨523359, by rfl⟩ : syracuseStep 1395625 = 1046719) B1046719
theorem B11226077 : Blo 428775 11226077 := bstep (se 3 (by rfl) ⟨2104889, by rfl⟩ : syracuseStep 11226077 = 4209779) B4209779
theorem B2182139 : Blo 428775 2182139 := bstep (se 1 (by rfl) ⟨1636604, by rfl⟩ : syracuseStep 2182139 = 3273209) B3273209
theorem B2935865 : Blo 428775 2935865 := bstep (se 2 (by rfl) ⟨1100949, by rfl⟩ : syracuseStep 2935865 = 2201899) B2201899
theorem B2182625 : Blo 428775 2182625 := bstep (se 2 (by rfl) ⟨818484, by rfl⟩ : syracuseStep 2182625 = 1636969) B1636969
theorem B970487 : Blo 428775 970487 := bstep (se 1 (by rfl) ⟨727865, by rfl⟩ : syracuseStep 970487 = 1455731) B1455731
theorem B970505 : Blo 428775 970505 := bstep (se 2 (by rfl) ⟨363939, by rfl⟩ : syracuseStep 970505 = 727879) B727879
theorem B970559 : Blo 428775 970559 := bstep (se 1 (by rfl) ⟨727919, by rfl⟩ : syracuseStep 970559 = 1455839) B1455839
theorem B970667 : Blo 428775 970667 := bstep (se 1 (by rfl) ⟨728000, by rfl⟩ : syracuseStep 970667 = 1456001) B1456001
theorem B643193 : Blo 428775 643193 := bstep (se 2 (by rfl) ⟨241197, by rfl⟩ : syracuseStep 643193 = 482395) B482395
theorem B643199 : Blo 428775 643199 := bstep (se 1 (by rfl) ⟨482399, by rfl⟩ : syracuseStep 643199 = 964799) B964799
theorem B971027 : Blo 428775 971027 := bstep (se 1 (by rfl) ⟨728270, by rfl⟩ : syracuseStep 971027 = 1456541) B1456541
theorem B2445659 : Blo 428775 2445659 := bstep (se 1 (by rfl) ⟨1834244, by rfl⟩ : syracuseStep 2445659 = 3668489) B3668489
theorem B971207 : Blo 428775 971207 := bstep (se 1 (by rfl) ⟨728405, by rfl⟩ : syracuseStep 971207 = 1456811) B1456811
theorem B2609633 : Blo 428775 2609633 := bstep (se 2 (by rfl) ⟨978612, by rfl⟩ : syracuseStep 2609633 = 1957225) B1957225
theorem B971495 : Blo 428775 971495 := bstep (se 1 (by rfl) ⟨728621, by rfl⟩ : syracuseStep 971495 = 1457243) B1457243
theorem B971567 : Blo 428775 971567 := bstep (se 1 (by rfl) ⟨728675, by rfl⟩ : syracuseStep 971567 = 1457351) B1457351
theorem B971657 : Blo 428775 971657 := bstep (se 2 (by rfl) ⟨364371, by rfl⟩ : syracuseStep 971657 = 728743) B728743
theorem B644039 : Blo 428775 644039 := bstep (se 1 (by rfl) ⟨483029, by rfl⟩ : syracuseStep 644039 = 966059) B966059
theorem B644063 : Blo 428775 644063 := bstep (se 1 (by rfl) ⟨483047, by rfl⟩ : syracuseStep 644063 = 966095) B966095
theorem B644399 : Blo 428775 644399 := bstep (se 1 (by rfl) ⟨483299, by rfl⟩ : syracuseStep 644399 = 966599) B966599
theorem B644603 : Blo 428775 644603 := bstep (se 1 (by rfl) ⟨483452, by rfl⟩ : syracuseStep 644603 = 966905) B966905
theorem B644639 : Blo 428775 644639 := bstep (se 1 (by rfl) ⟨483479, by rfl⟩ : syracuseStep 644639 = 966959) B966959
theorem B644777 : Blo 428775 644777 := bstep (se 2 (by rfl) ⟨241791, by rfl⟩ : syracuseStep 644777 = 483583) B483583
theorem B644783 : Blo 428775 644783 := bstep (se 1 (by rfl) ⟨483587, by rfl⟩ : syracuseStep 644783 = 967175) B967175
theorem B12474101 : Blo 428775 12474101 := bstep (se 5 (by rfl) ⟨584723, by rfl⟩ : syracuseStep 12474101 = 1169447) B1169447
theorem B4904711 : Blo 428775 4904711 := bstep (se 1 (by rfl) ⟨3678533, by rfl⟩ : syracuseStep 4904711 = 7357067) B7357067
theorem B644903 : Blo 428775 644903 := bstep (se 1 (by rfl) ⟨483677, by rfl⟩ : syracuseStep 644903 = 967355) B967355
theorem B5592887 : Blo 428775 5592887 := bstep (se 1 (by rfl) ⟨4194665, by rfl⟩ : syracuseStep 5592887 = 8389331) B8389331
theorem B645161 : Blo 428775 645161 := bstep (se 2 (by rfl) ⟨241935, by rfl⟩ : syracuseStep 645161 = 483871) B483871
theorem B645191 : Blo 428775 645191 := bstep (se 1 (by rfl) ⟨483893, by rfl⟩ : syracuseStep 645191 = 967787) B967787
theorem B645503 : Blo 428775 645503 := bstep (se 1 (by rfl) ⟨484127, by rfl⟩ : syracuseStep 645503 = 968255) B968255
theorem B5495201 : Blo 428775 5495201 := bstep (se 2 (by rfl) ⟨2060700, by rfl⟩ : syracuseStep 5495201 = 4121401) B4121401
theorem B645575 : Blo 428775 645575 := bstep (se 1 (by rfl) ⟨484181, by rfl⟩ : syracuseStep 645575 = 968363) B968363
theorem B2185703 : Blo 428775 2185703 := bstep (se 1 (by rfl) ⟨1639277, by rfl⟩ : syracuseStep 2185703 = 3278555) B3278555
theorem B645791 : Blo 428775 645791 := bstep (se 1 (by rfl) ⟨484343, by rfl⟩ : syracuseStep 645791 = 968687) B968687
theorem B613055 : Blo 428775 613055 := bstep (se 1 (by rfl) ⟨459791, by rfl⟩ : syracuseStep 613055 = 919583) B919583
theorem B645935 : Blo 428775 645935 := bstep (se 1 (by rfl) ⟨484451, by rfl⟩ : syracuseStep 645935 = 968903) B968903
theorem B646025 : Blo 428775 646025 := bstep (se 2 (by rfl) ⟨242259, by rfl⟩ : syracuseStep 646025 = 484519) B484519
theorem B646055 : Blo 428775 646055 := bstep (se 1 (by rfl) ⟨484541, by rfl⟩ : syracuseStep 646055 = 969083) B969083
theorem B646235 : Blo 428775 646235 := bstep (se 1 (by rfl) ⟨484676, by rfl⟩ : syracuseStep 646235 = 969353) B969353
theorem B646427 : Blo 428775 646427 := bstep (se 1 (by rfl) ⟨484820, by rfl⟩ : syracuseStep 646427 = 969641) B969641
theorem B5496173 : Blo 428775 5496173 := bstep (se 3 (by rfl) ⟨1030532, by rfl⟩ : syracuseStep 5496173 = 2061065) B2061065
theorem B646895 : Blo 428775 646895 := bstep (se 1 (by rfl) ⟨485171, by rfl⟩ : syracuseStep 646895 = 970343) B970343
theorem B2186999 : Blo 428775 2186999 := bstep (se 1 (by rfl) ⟨1640249, by rfl⟩ : syracuseStep 2186999 = 3280499) B3280499
theorem B3497833 : Blo 428775 3497833 := bstep (se 2 (by rfl) ⟨1311687, by rfl⟩ : syracuseStep 3497833 = 2623375) B2623375
theorem B647081 : Blo 428775 647081 := bstep (se 2 (by rfl) ⟨242655, by rfl⟩ : syracuseStep 647081 = 485311) B485311
theorem B647231 : Blo 428775 647231 := bstep (se 1 (by rfl) ⟨485423, by rfl⟩ : syracuseStep 647231 = 970847) B970847
theorem B516199 : Blo 428775 516199 := bstep (se 1 (by rfl) ⟨387149, by rfl⟩ : syracuseStep 516199 = 774299) B774299
theorem B2318483 : Blo 428775 2318483 := bstep (se 1 (by rfl) ⟨1738862, by rfl⟩ : syracuseStep 2318483 = 3477725) B3477725
theorem B647465 : Blo 428775 647465 := bstep (se 2 (by rfl) ⟨242799, by rfl⟩ : syracuseStep 647465 = 485599) B485599
theorem B647735 : Blo 428775 647735 := bstep (se 1 (by rfl) ⟨485801, by rfl⟩ : syracuseStep 647735 = 971603) B971603
theorem B4907627 : Blo 428775 4907627 := bstep (se 1 (by rfl) ⟨3680720, by rfl⟩ : syracuseStep 4907627 = 7361441) B7361441
theorem B615071 : Blo 428775 615071 := bstep (se 1 (by rfl) ⟨461303, by rfl⟩ : syracuseStep 615071 = 922607) B922607
theorem B648095 : Blo 428775 648095 := bstep (se 1 (by rfl) ⟨486071, by rfl⟩ : syracuseStep 648095 = 972143) B972143
theorem B648383 : Blo 428775 648383 := bstep (se 1 (by rfl) ⟨486287, by rfl⟩ : syracuseStep 648383 = 972575) B972575
theorem B143123705 : Blo 428775 143123705 := bstep (se 2 (by rfl) ⟨53671389, by rfl⟩ : syracuseStep 143123705 = 107342779) B107342779
theorem B1238291 : Blo 428775 1238291 := bstep (se 1 (by rfl) ⟨928718, by rfl⟩ : syracuseStep 1238291 = 1857437) B1857437
theorem B648527 : Blo 428775 648527 := bstep (se 1 (by rfl) ⟨486395, by rfl⟩ : syracuseStep 648527 = 972791) B972791
theorem B648617 : Blo 428775 648617 := bstep (se 2 (by rfl) ⟨243231, by rfl⟩ : syracuseStep 648617 = 486463) B486463
theorem B648767 : Blo 428775 648767 := bstep (se 1 (by rfl) ⟨486575, by rfl⟩ : syracuseStep 648767 = 973151) B973151
theorem B2451059 : Blo 428775 2451059 := bstep (se 1 (by rfl) ⟨1838294, by rfl⟩ : syracuseStep 2451059 = 3676589) B3676589
theorem B1631927 : Blo 428775 1631927 := bstep (se 1 (by rfl) ⟨1223945, by rfl⟩ : syracuseStep 1631927 = 2447891) B2447891
theorem B5891869 : Blo 428775 5891869 := bstep (se 3 (by rfl) ⟨1104725, by rfl⟩ : syracuseStep 5891869 = 2209451) B2209451
theorem B2320211 : Blo 428775 2320211 := bstep (se 1 (by rfl) ⟨1740158, by rfl⟩ : syracuseStep 2320211 = 3480317) B3480317
theorem B649127 : Blo 428775 649127 := bstep (se 1 (by rfl) ⟨486845, by rfl⟩ : syracuseStep 649127 = 973691) B973691
theorem B2190077 : Blo 428775 2190077 := bstep (se 3 (by rfl) ⟨410639, by rfl⟩ : syracuseStep 2190077 = 821279) B821279
theorem B1567855 : Blo 428775 1567855 := bstep (se 1 (by rfl) ⟨1175891, by rfl⟩ : syracuseStep 1567855 = 2351783) B2351783
theorem B486607 : Blo 428775 486607 := bstep (se 1 (by rfl) ⟨364955, by rfl⟩ : syracuseStep 486607 = 729911) B729911
theorem B11234609 : Blo 428775 11234609 := bstep (se 2 (by rfl) ⟨4212978, by rfl⟩ : syracuseStep 11234609 = 8425957) B8425957
theorem B978785 : Blo 428775 978785 := bstep (se 2 (by rfl) ⟨367044, by rfl⟩ : syracuseStep 978785 = 734089) B734089
theorem B21458843 : Blo 428775 21458843 := bstep (se 1 (by rfl) ⟨16094132, by rfl⟩ : syracuseStep 21458843 = 32188265) B32188265
theorem B3272723 : Blo 428775 3272723 := bstep (se 1 (by rfl) ⟨2454542, by rfl⟩ : syracuseStep 3272723 = 4909085) B4909085
theorem B4977541 : Blo 428775 4977541 := bstep (se 4 (by rfl) ⟨466644, by rfl⟩ : syracuseStep 4977541 = 933289) B933289
theorem B1635983 : Blo 428775 1635983 := bstep (se 1 (by rfl) ⟨1226987, by rfl⟩ : syracuseStep 1635983 = 2453975) B2453975
theorem B10516463 : Blo 428775 10516463 := bstep (se 1 (by rfl) ⟨7887347, by rfl⟩ : syracuseStep 10516463 = 15774695) B15774695
theorem B3537017 : Blo 428775 3537017 := bstep (se 2 (by rfl) ⟨1326381, by rfl⟩ : syracuseStep 3537017 = 2652763) B2652763
theorem B1375031 : Blo 428775 1375031 := bstep (se 1 (by rfl) ⟨1031273, by rfl⟩ : syracuseStep 1375031 = 2062547) B2062547
theorem B1179049 : Blo 428775 1179049 := bstep (se 2 (by rfl) ⟨442143, by rfl⟩ : syracuseStep 1179049 = 884287) B884287
theorem B687599 : Blo 428775 687599 := bstep (se 1 (by rfl) ⟨515699, by rfl⟩ : syracuseStep 687599 = 1031399) B1031399
theorem B688009 : Blo 428775 688009 := bstep (se 2 (by rfl) ⟨258003, by rfl⟩ : syracuseStep 688009 = 516007) B516007
theorem B688265 : Blo 428775 688265 := bstep (se 2 (by rfl) ⟨258099, by rfl⟩ : syracuseStep 688265 = 516199) B516199
theorem B1835561 : Blo 428775 1835561 := bstep (se 2 (by rfl) ⟨688335, by rfl⟩ : syracuseStep 1835561 = 1376671) B1376671
theorem B1639187 : Blo 428775 1639187 := bstep (se 1 (by rfl) ⟨1229390, by rfl⟩ : syracuseStep 1639187 = 2458781) B2458781
theorem B820543 : Blo 428775 820543 := bstep (se 1 (by rfl) ⟨615407, by rfl⟩ : syracuseStep 820543 = 1230815) B1230815
theorem B820687 : Blo 428775 820687 := bstep (se 1 (by rfl) ⟨615515, by rfl⟩ : syracuseStep 820687 = 1231031) B1231031
theorem B5899979 : Blo 428775 5899979 := bstep (se 1 (by rfl) ⟨4424984, by rfl⟩ : syracuseStep 5899979 = 8849969) B8849969
theorem B1640189 : Blo 428775 1640189 := bstep (se 3 (by rfl) ⟨307535, by rfl⟩ : syracuseStep 1640189 = 615071) B615071
theorem B461423 : Blo 428775 461423 := bstep (se 1 (by rfl) ⟨346067, by rfl⟩ : syracuseStep 461423 = 692135) B692135
theorem B2067065 : Blo 428775 2067065 := bstep (se 2 (by rfl) ⟨775149, by rfl⟩ : syracuseStep 2067065 = 1550299) B1550299
theorem B1837799 : Blo 428775 1837799 := bstep (se 1 (by rfl) ⟨1378349, by rfl⟩ : syracuseStep 1837799 = 2756699) B2756699
theorem B428795 : Blo 428775 428795 := bstep (se 1 (by rfl) ⟨321596, by rfl⟩ : syracuseStep 428795 = 643193) B643193
theorem B428799 : Blo 428775 428799 := bstep (se 1 (by rfl) ⟨321599, by rfl⟩ : syracuseStep 428799 = 643199) B643199
theorem B1379143 : Blo 428775 1379143 := bstep (se 1 (by rfl) ⟨1034357, by rfl⟩ : syracuseStep 1379143 = 2068715) B2068715
theorem B1739755 : Blo 428775 1739755 := bstep (se 1 (by rfl) ⟨1304816, by rfl⟩ : syracuseStep 1739755 = 2609633) B2609633
theorem B429359 : Blo 428775 429359 := bstep (se 1 (by rfl) ⟨322019, by rfl⟩ : syracuseStep 429359 = 644039) B644039
theorem B429375 : Blo 428775 429375 := bstep (se 1 (by rfl) ⟨322031, by rfl⟩ : syracuseStep 429375 = 644063) B644063
theorem B429599 : Blo 428775 429599 := bstep (se 1 (by rfl) ⟨322199, by rfl⟩ : syracuseStep 429599 = 644399) B644399
theorem B429735 : Blo 428775 429735 := bstep (se 1 (by rfl) ⟨322301, by rfl⟩ : syracuseStep 429735 = 644603) B644603
theorem B429759 : Blo 428775 429759 := bstep (se 1 (by rfl) ⟨322319, by rfl⟩ : syracuseStep 429759 = 644639) B644639
theorem B2756339 : Blo 428775 2756339 := bstep (se 1 (by rfl) ⟨2067254, by rfl⟩ : syracuseStep 2756339 = 4134509) B4134509
theorem B1969939 : Blo 428775 1969939 := bstep (se 1 (by rfl) ⟨1477454, by rfl⟩ : syracuseStep 1969939 = 2954909) B2954909
theorem B429851 : Blo 428775 429851 := bstep (se 1 (by rfl) ⟨322388, by rfl⟩ : syracuseStep 429851 = 644777) B644777
theorem B429855 : Blo 428775 429855 := bstep (se 1 (by rfl) ⟨322391, by rfl⟩ : syracuseStep 429855 = 644783) B644783
theorem B7343945 : Blo 428775 7343945 := bstep (se 2 (by rfl) ⟨2753979, by rfl⟩ : syracuseStep 7343945 = 5507959) B5507959
theorem B429935 : Blo 428775 429935 := bstep (se 1 (by rfl) ⟨322451, by rfl⟩ : syracuseStep 429935 = 644903) B644903
theorem B430107 : Blo 428775 430107 := bstep (se 1 (by rfl) ⟨322580, by rfl⟩ : syracuseStep 430107 = 645161) B645161
theorem B430127 : Blo 428775 430127 := bstep (se 1 (by rfl) ⟨322595, by rfl⟩ : syracuseStep 430127 = 645191) B645191
theorem B430335 : Blo 428775 430335 := bstep (se 1 (by rfl) ⟨322751, by rfl⟩ : syracuseStep 430335 = 645503) B645503
theorem B725287 : Blo 428775 725287 := bstep (se 1 (by rfl) ⟨543965, by rfl⟩ : syracuseStep 725287 = 1087931) B1087931
theorem B430383 : Blo 428775 430383 := bstep (se 1 (by rfl) ⟨322787, by rfl⟩ : syracuseStep 430383 = 645575) B645575
theorem B430527 : Blo 428775 430527 := bstep (se 1 (by rfl) ⟨322895, by rfl⟩ : syracuseStep 430527 = 645791) B645791
theorem B725483 : Blo 428775 725483 := bstep (se 1 (by rfl) ⟨544112, by rfl⟩ : syracuseStep 725483 = 1088225) B1088225
theorem B430623 : Blo 428775 430623 := bstep (se 1 (by rfl) ⟨322967, by rfl⟩ : syracuseStep 430623 = 645935) B645935
theorem B430683 : Blo 428775 430683 := bstep (se 1 (by rfl) ⟨323012, by rfl⟩ : syracuseStep 430683 = 646025) B646025
theorem B430703 : Blo 428775 430703 := bstep (se 1 (by rfl) ⟨323027, by rfl⟩ : syracuseStep 430703 = 646055) B646055
theorem B26546885 : Blo 428775 26546885 := bstep (se 4 (by rfl) ⟨2488770, by rfl⟩ : syracuseStep 26546885 = 4977541) B4977541
theorem B430823 : Blo 428775 430823 := bstep (se 1 (by rfl) ⟨323117, by rfl⟩ : syracuseStep 430823 = 646235) B646235
theorem B2364191 : Blo 428775 2364191 := bstep (se 1 (by rfl) ⟨1773143, by rfl⟩ : syracuseStep 2364191 = 3546287) B3546287
theorem B430951 : Blo 428775 430951 := bstep (se 1 (by rfl) ⟨323213, by rfl⟩ : syracuseStep 430951 = 646427) B646427
theorem B1840087 : Blo 428775 1840087 := bstep (se 1 (by rfl) ⟨1380065, by rfl⟩ : syracuseStep 1840087 = 2760131) B2760131
theorem B431263 : Blo 428775 431263 := bstep (se 1 (by rfl) ⟨323447, by rfl⟩ : syracuseStep 431263 = 646895) B646895
theorem B431387 : Blo 428775 431387 := bstep (se 1 (by rfl) ⟨323540, by rfl⟩ : syracuseStep 431387 = 647081) B647081
theorem B431487 : Blo 428775 431487 := bstep (se 1 (by rfl) ⟨323615, by rfl⟩ : syracuseStep 431487 = 647231) B647231
theorem B1545655 : Blo 428775 1545655 := bstep (se 1 (by rfl) ⟨1159241, by rfl⟩ : syracuseStep 1545655 = 2318483) B2318483
theorem B431643 : Blo 428775 431643 := bstep (se 1 (by rfl) ⟨323732, by rfl⟩ : syracuseStep 431643 = 647465) B647465
theorem B1447577 : Blo 428775 1447577 := bstep (se 2 (by rfl) ⟨542841, by rfl⟩ : syracuseStep 1447577 = 1085683) B1085683
theorem B431823 : Blo 428775 431823 := bstep (se 1 (by rfl) ⟨323867, by rfl⟩ : syracuseStep 431823 = 647735) B647735
theorem B923359 : Blo 428775 923359 := bstep (se 1 (by rfl) ⟨692519, by rfl⟩ : syracuseStep 923359 = 1385039) B1385039
theorem B432063 : Blo 428775 432063 := bstep (se 1 (by rfl) ⟨324047, by rfl⟩ : syracuseStep 432063 = 648095) B648095
theorem B432255 : Blo 428775 432255 := bstep (se 1 (by rfl) ⟨324191, by rfl⟩ : syracuseStep 432255 = 648383) B648383
theorem B825527 : Blo 428775 825527 := bstep (se 1 (by rfl) ⟨619145, by rfl⟩ : syracuseStep 825527 = 1238291) B1238291
theorem B432351 : Blo 428775 432351 := bstep (se 1 (by rfl) ⟨324263, by rfl⟩ : syracuseStep 432351 = 648527) B648527
theorem B432411 : Blo 428775 432411 := bstep (se 1 (by rfl) ⟨324308, by rfl⟩ : syracuseStep 432411 = 648617) B648617
theorem B432511 : Blo 428775 432511 := bstep (se 1 (by rfl) ⟨324383, by rfl⟩ : syracuseStep 432511 = 648767) B648767
theorem B1087951 : Blo 428775 1087951 := bstep (se 1 (by rfl) ⟨815963, by rfl⟩ : syracuseStep 1087951 = 1631927) B1631927
theorem B727535 : Blo 428775 727535 := bstep (se 1 (by rfl) ⟨545651, by rfl⟩ : syracuseStep 727535 = 1091303) B1091303
theorem B432751 : Blo 428775 432751 := bstep (se 1 (by rfl) ⟨324563, by rfl⟩ : syracuseStep 432751 = 649127) B649127
theorem B1841899 : Blo 428775 1841899 := bstep (se 1 (by rfl) ⟨1381424, by rfl⟩ : syracuseStep 1841899 = 2762849) B2762849
theorem B1448873 : Blo 428775 1448873 := bstep (se 2 (by rfl) ⟨543327, by rfl⟩ : syracuseStep 1448873 = 1086655) B1086655
theorem B2759903 : Blo 428775 2759903 := bstep (se 1 (by rfl) ⟨2069927, by rfl⟩ : syracuseStep 2759903 = 4139855) B4139855
theorem B1449737 : Blo 428775 1449737 := bstep (se 2 (by rfl) ⟨543651, by rfl⟩ : syracuseStep 1449737 = 1087303) B1087303
theorem B729263 : Blo 428775 729263 := bstep (se 1 (by rfl) ⟨546947, by rfl⟩ : syracuseStep 729263 = 1093895) B1093895
theorem B1450223 : Blo 428775 1450223 := bstep (se 1 (by rfl) ⟨1087667, by rfl⟩ : syracuseStep 1450223 = 2175335) B2175335
theorem B1090655 : Blo 428775 1090655 := bstep (se 1 (by rfl) ⟨817991, by rfl⟩ : syracuseStep 1090655 = 1635983) B1635983
theorem B3483431 : Blo 428775 3483431 := bstep (se 1 (by rfl) ⟨2612573, by rfl⟩ : syracuseStep 3483431 = 5225147) B5225147
theorem B18655109 : Blo 428775 18655109 := bstep (se 4 (by rfl) ⟨1748916, by rfl⟩ : syracuseStep 18655109 = 3497833) B3497833
theorem B4402151 : Blo 428775 4402151 := bstep (se 1 (by rfl) ⟨3301613, by rfl⟩ : syracuseStep 4402151 = 6603227) B6603227
theorem B1453787 : Blo 428775 1453787 := bstep (se 1 (by rfl) ⟨1090340, by rfl⟩ : syracuseStep 1453787 = 2180681) B2180681
theorem B7484051 : Blo 428775 7484051 := bstep (se 1 (by rfl) ⟨5613038, by rfl⟩ : syracuseStep 7484051 = 11226077) B11226077
theorem B1454759 : Blo 428775 1454759 := bstep (se 1 (by rfl) ⟨1091069, by rfl⟩ : syracuseStep 1454759 = 2182139) B2182139
theorem B1455083 : Blo 428775 1455083 := bstep (se 1 (by rfl) ⟨1091312, by rfl⟩ : syracuseStep 1455083 = 2182625) B2182625
theorem B3684001 : Blo 428775 3684001 := bstep (se 2 (by rfl) ⟨1381500, by rfl⟩ : syracuseStep 3684001 = 2763001) B2763001
theorem B965339 : Blo 428775 965339 := bstep (se 1 (by rfl) ⟨724004, by rfl⟩ : syracuseStep 965339 = 1448009) B1448009
theorem B1457135 : Blo 428775 1457135 := bstep (se 1 (by rfl) ⟨1092851, by rfl⟩ : syracuseStep 1457135 = 2185703) B2185703
theorem B7847059 : Blo 428775 7847059 := bstep (se 1 (by rfl) ⟨5885294, by rfl⟩ : syracuseStep 7847059 = 11770589) B11770589
theorem B966311 : Blo 428775 966311 := bstep (se 1 (by rfl) ⟨724733, by rfl⟩ : syracuseStep 966311 = 1449467) B1449467
theorem B966383 : Blo 428775 966383 := bstep (se 1 (by rfl) ⟨724787, by rfl⟩ : syracuseStep 966383 = 1449575) B1449575
theorem B1457999 : Blo 428775 1457999 := bstep (se 1 (by rfl) ⟨1093499, by rfl⟩ : syracuseStep 1457999 = 2186999) B2186999
theorem B1458593 : Blo 428775 1458593 := bstep (se 2 (by rfl) ⟨546972, by rfl⟩ : syracuseStep 1458593 = 1093945) B1093945
theorem B1558283 : Blo 428775 1558283 := bstep (se 1 (by rfl) ⟨1168712, by rfl⟩ : syracuseStep 1558283 = 2337425) B2337425
theorem B1460051 : Blo 428775 1460051 := bstep (se 1 (by rfl) ⟨1095038, by rfl⟩ : syracuseStep 1460051 = 2190077) B2190077
theorem B7489739 : Blo 428775 7489739 := bstep (se 1 (by rfl) ⟨5617304, by rfl⟩ : syracuseStep 7489739 = 11234609) B11234609
theorem B14305895 : Blo 428775 14305895 := bstep (se 1 (by rfl) ⟨10729421, by rfl⟩ : syracuseStep 14305895 = 21458843) B21458843
theorem B2181815 : Blo 428775 2181815 := bstep (se 1 (by rfl) ⟨1636361, by rfl⟩ : syracuseStep 2181815 = 3272723) B3272723
theorem B1232147 : Blo 428775 1232147 := bstep (se 1 (by rfl) ⟨924110, by rfl⟩ : syracuseStep 1232147 = 1848221) B1848221
theorem B7884377 : Blo 428775 7884377 := bstep (se 2 (by rfl) ⟨2956641, by rfl⟩ : syracuseStep 7884377 = 5913283) B5913283
theorem B10440373 : Blo 428775 10440373 := bstep (se 5 (by rfl) ⟨489392, by rfl⟩ : syracuseStep 10440373 = 978785) B978785
theorem B643163 : Blo 428775 643163 := bstep (se 1 (by rfl) ⟨482372, by rfl⟩ : syracuseStep 643163 = 964745) B964745
theorem B971243 : Blo 428775 971243 := bstep (se 1 (by rfl) ⟨728432, by rfl⟩ : syracuseStep 971243 = 1456865) B1456865
theorem B643835 : Blo 428775 643835 := bstep (se 1 (by rfl) ⟨482876, by rfl⟩ : syracuseStep 643835 = 965753) B965753
theorem B971945 : Blo 428775 971945 := bstep (se 2 (by rfl) ⟨364479, by rfl⟩ : syracuseStep 971945 = 728959) B728959
theorem B1332791 : Blo 428775 1332791 := bstep (se 1 (by rfl) ⟨999593, by rfl⟩ : syracuseStep 1332791 = 1999187) B1999187
theorem B1660571 : Blo 428775 1660571 := bstep (se 1 (by rfl) ⟨1245428, by rfl⟩ : syracuseStep 1660571 = 2490857) B2490857
theorem B972521 : Blo 428775 972521 := bstep (se 2 (by rfl) ⟨364695, by rfl⟩ : syracuseStep 972521 = 729391) B729391
theorem B1169405 : Blo 428775 1169405 := bstep (se 3 (by rfl) ⟨219263, by rfl⟩ : syracuseStep 1169405 = 438527) B438527
theorem B645359 : Blo 428775 645359 := bstep (se 1 (by rfl) ⟨484019, by rfl⟩ : syracuseStep 645359 = 968039) B968039
theorem B645431 : Blo 428775 645431 := bstep (se 1 (by rfl) ⟨484073, by rfl⟩ : syracuseStep 645431 = 968147) B968147
theorem B645611 : Blo 428775 645611 := bstep (se 1 (by rfl) ⟨484208, by rfl⟩ : syracuseStep 645611 = 968417) B968417
theorem B646139 : Blo 428775 646139 := bstep (se 1 (by rfl) ⟨484604, by rfl⟩ : syracuseStep 646139 = 969209) B969209
theorem B7330823 : Blo 428775 7330823 := bstep (se 1 (by rfl) ⟨5498117, by rfl⟩ : syracuseStep 7330823 = 10996235) B10996235
theorem B646199 : Blo 428775 646199 := bstep (se 1 (by rfl) ⟨484649, by rfl⟩ : syracuseStep 646199 = 969299) B969299
theorem B646319 : Blo 428775 646319 := bstep (se 1 (by rfl) ⟨484739, by rfl⟩ : syracuseStep 646319 = 969479) B969479
theorem B646379 : Blo 428775 646379 := bstep (se 1 (by rfl) ⟨484784, by rfl⟩ : syracuseStep 646379 = 969569) B969569
theorem B3497255 : Blo 428775 3497255 := bstep (se 1 (by rfl) ⟨2622941, by rfl⟩ : syracuseStep 3497255 = 5245883) B5245883
theorem B1957243 : Blo 428775 1957243 := bstep (se 1 (by rfl) ⟨1467932, by rfl⟩ : syracuseStep 1957243 = 2935865) B2935865
theorem B2448893 : Blo 428775 2448893 := bstep (se 3 (by rfl) ⟨459167, by rfl⟩ : syracuseStep 2448893 = 918335) B918335
theorem B7855825 : Blo 428775 7855825 := bstep (se 2 (by rfl) ⟨2945934, by rfl⟩ : syracuseStep 7855825 = 5891869) B5891869
theorem B3268349 : Blo 428775 3268349 := bstep (se 3 (by rfl) ⟨612815, by rfl⟩ : syracuseStep 3268349 = 1225631) B1225631
theorem B646991 : Blo 428775 646991 := bstep (se 1 (by rfl) ⟨485243, by rfl⟩ : syracuseStep 646991 = 970487) B970487
theorem B647003 : Blo 428775 647003 := bstep (se 1 (by rfl) ⟨485252, by rfl⟩ : syracuseStep 647003 = 970505) B970505
theorem B647039 : Blo 428775 647039 := bstep (se 1 (by rfl) ⟨485279, by rfl⟩ : syracuseStep 647039 = 970559) B970559
theorem B647111 : Blo 428775 647111 := bstep (se 1 (by rfl) ⟨485333, by rfl⟩ : syracuseStep 647111 = 970667) B970667
theorem B647351 : Blo 428775 647351 := bstep (se 1 (by rfl) ⟨485513, by rfl⟩ : syracuseStep 647351 = 971027) B971027
theorem B3367133 : Blo 428775 3367133 := bstep (se 3 (by rfl) ⟨631337, by rfl⟩ : syracuseStep 3367133 = 1262675) B1262675
theorem B1630439 : Blo 428775 1630439 := bstep (se 1 (by rfl) ⟨1222829, by rfl⟩ : syracuseStep 1630439 = 2445659) B2445659
theorem B647471 : Blo 428775 647471 := bstep (se 1 (by rfl) ⟨485603, by rfl⟩ : syracuseStep 647471 = 971207) B971207
theorem B18833897 : Blo 428775 18833897 := bstep (se 2 (by rfl) ⟨7062711, by rfl⟩ : syracuseStep 18833897 = 14125423) B14125423
theorem B647663 : Blo 428775 647663 := bstep (se 1 (by rfl) ⟨485747, by rfl⟩ : syracuseStep 647663 = 971495) B971495
theorem B647711 : Blo 428775 647711 := bstep (se 1 (by rfl) ⟨485783, by rfl⟩ : syracuseStep 647711 = 971567) B971567
theorem B118317611 : Blo 428775 118317611 := bstep (se 1 (by rfl) ⟨88738208, by rfl⟩ : syracuseStep 118317611 = 177476417) B177476417
theorem B647771 : Blo 428775 647771 := bstep (se 1 (by rfl) ⟨485828, by rfl⟩ : syracuseStep 647771 = 971657) B971657
theorem B9331361 : Blo 428775 9331361 := bstep (se 2 (by rfl) ⟨3499260, by rfl⟩ : syracuseStep 9331361 = 6998521) B6998521
theorem B484123 : Blo 428775 484123 := bstep (se 1 (by rfl) ⟨363092, by rfl⟩ : syracuseStep 484123 = 726185) B726185
theorem B615367 : Blo 428775 615367 := bstep (se 1 (by rfl) ⟨461525, by rfl⟩ : syracuseStep 615367 = 923051) B923051
theorem B8316067 : Blo 428775 8316067 := bstep (se 1 (by rfl) ⟨6237050, by rfl⟩ : syracuseStep 8316067 = 12474101) B12474101
theorem B3269807 : Blo 428775 3269807 := bstep (se 1 (by rfl) ⟨2452355, by rfl⟩ : syracuseStep 3269807 = 4904711) B4904711
theorem B3728591 : Blo 428775 3728591 := bstep (se 1 (by rfl) ⟨2796443, by rfl⟩ : syracuseStep 3728591 = 5592887) B5592887
theorem B1860833 : Blo 428775 1860833 := bstep (se 2 (by rfl) ⟨697812, by rfl⟩ : syracuseStep 1860833 = 1395625) B1395625
theorem B2090473 : Blo 428775 2090473 := bstep (se 2 (by rfl) ⟨783927, by rfl⟩ : syracuseStep 2090473 = 1567855) B1567855
theorem B648809 : Blo 428775 648809 := bstep (se 2 (by rfl) ⟨243303, by rfl⟩ : syracuseStep 648809 = 486607) B486607
theorem B3663467 : Blo 428775 3663467 := bstep (se 1 (by rfl) ⟨2747600, by rfl⟩ : syracuseStep 3663467 = 5495201) B5495201
theorem B485095 : Blo 428775 485095 := bstep (se 1 (by rfl) ⟨363821, by rfl⟩ : syracuseStep 485095 = 727643) B727643
theorem B2189267 : Blo 428775 2189267 := bstep (se 1 (by rfl) ⟨1641950, by rfl⟩ : syracuseStep 2189267 = 3283901) B3283901
theorem B6187229 : Blo 428775 6187229 := bstep (se 3 (by rfl) ⟨1160105, by rfl⟩ : syracuseStep 6187229 = 2320211) B2320211
theorem B3664115 : Blo 428775 3664115 := bstep (se 1 (by rfl) ⟨2748086, by rfl⟩ : syracuseStep 3664115 = 5496173) B5496173
theorem B1468795 : Blo 428775 1468795 := bstep (se 1 (by rfl) ⟨1101596, by rfl⟩ : syracuseStep 1468795 = 2203193) B2203193
theorem B2320903 : Blo 428775 2320903 := bstep (se 1 (by rfl) ⟨1740677, by rfl⟩ : syracuseStep 2320903 = 3481355) B3481355
theorem B6187691 : Blo 428775 6187691 := bstep (se 1 (by rfl) ⟨4640768, by rfl⟩ : syracuseStep 6187691 = 9281537) B9281537
theorem B1633081 : Blo 428775 1633081 := bstep (se 2 (by rfl) ⟨612405, by rfl⟩ : syracuseStep 1633081 = 1224811) B1224811
theorem B486427 : Blo 428775 486427 := bstep (se 1 (by rfl) ⟨364820, by rfl⟩ : syracuseStep 486427 = 729641) B729641
theorem B2452517 : Blo 428775 2452517 := bstep (se 4 (by rfl) ⟨229923, by rfl⟩ : syracuseStep 2452517 = 459847) B459847
theorem B3271751 : Blo 428775 3271751 := bstep (se 1 (by rfl) ⟨2453813, by rfl⟩ : syracuseStep 3271751 = 4907627) B4907627
theorem B95415803 : Blo 428775 95415803 := bstep (se 1 (by rfl) ⟨71561852, by rfl⟩ : syracuseStep 95415803 = 143123705) B143123705
theorem B1634039 : Blo 428775 1634039 := bstep (se 1 (by rfl) ⟨1225529, by rfl⟩ : syracuseStep 1634039 = 2451059) B2451059
theorem B4157419 : Blo 428775 4157419 := bstep (se 1 (by rfl) ⟨3118064, by rfl⟩ : syracuseStep 4157419 = 6236129) B6236129
theorem B815159 : Blo 428775 815159 := bstep (se 1 (by rfl) ⟨611369, by rfl⟩ : syracuseStep 815159 = 1222739) B1222739
theorem B2453723 : Blo 428775 2453723 := bstep (se 1 (by rfl) ⟨1840292, by rfl⟩ : syracuseStep 2453723 = 3680585) B3680585
theorem B1634813 : Blo 428775 1634813 := bstep (se 3 (by rfl) ⟨306527, by rfl⟩ : syracuseStep 1634813 = 613055) B613055
theorem B1340011 : Blo 428775 1340011 := bstep (se 1 (by rfl) ⟨1005008, by rfl⟩ : syracuseStep 1340011 = 2010017) B2010017
theorem B3503483 : Blo 428775 3503483 := bstep (se 1 (by rfl) ⟨2627612, by rfl⟩ : syracuseStep 3503483 = 5255225) B5255225
theorem B7010975 : Blo 428775 7010975 := bstep (se 1 (by rfl) ⟨5258231, by rfl⟩ : syracuseStep 7010975 = 10516463) B10516463
theorem B2063009 : Blo 428775 2063009 := bstep (se 2 (by rfl) ⟨773628, by rfl⟩ : syracuseStep 2063009 = 1547257) B1547257
theorem B2358011 : Blo 428775 2358011 := bstep (se 1 (by rfl) ⟨1768508, by rfl⟩ : syracuseStep 2358011 = 3537017) B3537017
theorem B1473515 : Blo 428775 1473515 := bstep (se 1 (by rfl) ⟨1105136, by rfl⟩ : syracuseStep 1473515 = 2210273) B2210273
theorem B916687 : Blo 428775 916687 := bstep (se 1 (by rfl) ⟨687515, by rfl⟩ : syracuseStep 916687 = 1375031) B1375031
theorem B1572065 : Blo 428775 1572065 := bstep (se 2 (by rfl) ⟨589524, by rfl⟩ : syracuseStep 1572065 = 1179049) B1179049
theorem B2522551 : Blo 428775 2522551 := bstep (se 1 (by rfl) ⟨1891913, by rfl⟩ : syracuseStep 2522551 = 3783827) B3783827
theorem B458399 : Blo 428775 458399 := bstep (se 1 (by rfl) ⟨343799, by rfl⟩ : syracuseStep 458399 = 687599) B687599
theorem B917345 : Blo 428775 917345 := bstep (se 2 (by rfl) ⟨344004, by rfl⟩ : syracuseStep 917345 = 688009) B688009
theorem B458843 : Blo 428775 458843 := bstep (se 1 (by rfl) ⟨344132, by rfl⟩ : syracuseStep 458843 = 688265) B688265
theorem B3933319 : Blo 428775 3933319 := bstep (se 1 (by rfl) ⟨2949989, by rfl⟩ : syracuseStep 3933319 = 5899979) B5899979
theorem B9537263 : Blo 428775 9537263 := bstep (se 1 (by rfl) ⟨7152947, by rfl⟩ : syracuseStep 9537263 = 14305895) B14305895
theorem B1378043 : Blo 428775 1378043 := bstep (se 1 (by rfl) ⟨1033532, by rfl⟩ : syracuseStep 1378043 = 2067065) B2067065
theorem B821431 : Blo 428775 821431 := bstep (se 1 (by rfl) ⟨616073, by rfl⟩ : syracuseStep 821431 = 1232147) B1232147
theorem B1837559 : Blo 428775 1837559 := bstep (se 1 (by rfl) ⟨1378169, by rfl⟩ : syracuseStep 1837559 = 2756339) B2756339
theorem B428775 : Blo 428775 428775 := bstep (se 1 (by rfl) ⟨321581, by rfl⟩ : syracuseStep 428775 = 643163) B643163
theorem B17697923 : Blo 428775 17697923 := bstep (se 1 (by rfl) ⟨13273442, by rfl⟩ : syracuseStep 17697923 = 26546885) B26546885
theorem B429223 : Blo 428775 429223 := bstep (se 1 (by rfl) ⟨321917, by rfl⟩ : syracuseStep 429223 = 643835) B643835
theorem B1576127 : Blo 428775 1576127 := bstep (se 1 (by rfl) ⟨1182095, by rfl⟩ : syracuseStep 1576127 = 2364191) B2364191
theorem B888527 : Blo 428775 888527 := bstep (se 1 (by rfl) ⟨666395, by rfl⟩ : syracuseStep 888527 = 1332791) B1332791
theorem B1838857 : Blo 428775 1838857 := bstep (se 2 (by rfl) ⟨689571, by rfl⟩ : syracuseStep 1838857 = 1379143) B1379143
theorem B430239 : Blo 428775 430239 := bstep (se 1 (by rfl) ⟨322679, by rfl⟩ : syracuseStep 430239 = 645359) B645359
theorem B430287 : Blo 428775 430287 := bstep (se 1 (by rfl) ⟨322715, by rfl⟩ : syracuseStep 430287 = 645431) B645431
theorem B430407 : Blo 428775 430407 := bstep (se 1 (by rfl) ⟨322805, by rfl⟩ : syracuseStep 430407 = 645611) B645611
theorem B430759 : Blo 428775 430759 := bstep (se 1 (by rfl) ⟨323069, by rfl⟩ : syracuseStep 430759 = 646139) B646139
theorem B4887215 : Blo 428775 4887215 := bstep (se 1 (by rfl) ⟨3665411, by rfl⟩ : syracuseStep 4887215 = 7330823) B7330823
theorem B430799 : Blo 428775 430799 := bstep (se 1 (by rfl) ⟨323099, by rfl⟩ : syracuseStep 430799 = 646199) B646199
theorem B430879 : Blo 428775 430879 := bstep (se 1 (by rfl) ⟨323159, by rfl⟩ : syracuseStep 430879 = 646319) B646319
theorem B1839935 : Blo 428775 1839935 := bstep (se 1 (by rfl) ⟨1379951, by rfl⟩ : syracuseStep 1839935 = 2759903) B2759903
theorem B430919 : Blo 428775 430919 := bstep (se 1 (by rfl) ⟨323189, by rfl⟩ : syracuseStep 430919 = 646379) B646379
theorem B2331503 : Blo 428775 2331503 := bstep (se 1 (by rfl) ⟨1748627, by rfl⟩ : syracuseStep 2331503 = 3497255) B3497255
theorem B3281957 : Blo 428775 3281957 := bstep (se 4 (by rfl) ⟨307683, by rfl⟩ : syracuseStep 3281957 = 615367) B615367
theorem B431327 : Blo 428775 431327 := bstep (se 1 (by rfl) ⟨323495, by rfl⟩ : syracuseStep 431327 = 646991) B646991
theorem B431335 : Blo 428775 431335 := bstep (se 1 (by rfl) ⟨323501, by rfl⟩ : syracuseStep 431335 = 647003) B647003
theorem B431359 : Blo 428775 431359 := bstep (se 1 (by rfl) ⟨323519, by rfl⟩ : syracuseStep 431359 = 647039) B647039
theorem B431407 : Blo 428775 431407 := bstep (se 1 (by rfl) ⟨323555, by rfl⟩ : syracuseStep 431407 = 647111) B647111
theorem B5543225 : Blo 428775 5543225 := bstep (se 2 (by rfl) ⟨2078709, by rfl⟩ : syracuseStep 5543225 = 4157419) B4157419
theorem B431567 : Blo 428775 431567 := bstep (se 1 (by rfl) ⟨323675, by rfl⟩ : syracuseStep 431567 = 647351) B647351
theorem B1086959 : Blo 428775 1086959 := bstep (se 1 (by rfl) ⟨815219, by rfl⟩ : syracuseStep 1086959 = 1630439) B1630439
theorem B431647 : Blo 428775 431647 := bstep (se 1 (by rfl) ⟨323735, by rfl⟩ : syracuseStep 431647 = 647471) B647471
theorem B12555931 : Blo 428775 12555931 := bstep (se 1 (by rfl) ⟨9416948, by rfl⟩ : syracuseStep 12555931 = 18833897) B18833897
theorem B431775 : Blo 428775 431775 := bstep (se 1 (by rfl) ⟨323831, by rfl⟩ : syracuseStep 431775 = 647663) B647663
theorem B431807 : Blo 428775 431807 := bstep (se 1 (by rfl) ⟨323855, by rfl⟩ : syracuseStep 431807 = 647711) B647711
theorem B78878407 : Blo 428775 78878407 := bstep (se 1 (by rfl) ⟨59158805, by rfl⟩ : syracuseStep 78878407 = 118317611) B118317611
theorem B431847 : Blo 428775 431847 := bstep (se 1 (by rfl) ⟨323885, by rfl⟩ : syracuseStep 431847 = 647771) B647771
theorem B727103 : Blo 428775 727103 := bstep (se 1 (by rfl) ⟨545327, by rfl⟩ : syracuseStep 727103 = 1090655) B1090655
theorem B432539 : Blo 428775 432539 := bstep (se 1 (by rfl) ⟨324404, by rfl⟩ : syracuseStep 432539 = 648809) B648809
theorem B63610535 : Blo 428775 63610535 := bstep (se 1 (by rfl) ⟨47707901, by rfl⟩ : syracuseStep 63610535 = 95415803) B95415803
theorem B1089359 : Blo 428775 1089359 := bstep (se 1 (by rfl) ⟨817019, by rfl⟩ : syracuseStep 1089359 = 1634039) B1634039
theorem B1089875 : Blo 428775 1089875 := bstep (se 1 (by rfl) ⟨817406, by rfl⟩ : syracuseStep 1089875 = 1634813) B1634813
theorem B4989367 : Blo 428775 4989367 := bstep (se 1 (by rfl) ⟨3742025, by rfl⟩ : syracuseStep 4989367 = 7484051) B7484051
theorem B1450601 : Blo 428775 1450601 := bstep (se 2 (by rfl) ⟨543975, by rfl⟩ : syracuseStep 1450601 = 1087951) B1087951
theorem B2335655 : Blo 428775 2335655 := bstep (se 1 (by rfl) ⟨1751741, by rfl⟩ : syracuseStep 2335655 = 3503483) B3503483
theorem B10462745 : Blo 428775 10462745 := bstep (se 2 (by rfl) ⟨3923529, by rfl⟩ : syracuseStep 10462745 = 7847059) B7847059
theorem B1222249 : Blo 428775 1222249 := bstep (se 2 (by rfl) ⟨458343, by rfl⟩ : syracuseStep 1222249 = 916687) B916687
theorem B1222397 : Blo 428775 1222397 := bstep (se 3 (by rfl) ⟨229199, by rfl⟩ : syracuseStep 1222397 = 458399) B458399
theorem B1223707 : Blo 428775 1223707 := bstep (se 1 (by rfl) ⟨917780, by rfl⟩ : syracuseStep 1223707 = 1835561) B1835561
theorem B1092791 : Blo 428775 1092791 := bstep (se 1 (by rfl) ⟨819593, by rfl⟩ : syracuseStep 1092791 = 1639187) B1639187
theorem B1093459 : Blo 428775 1093459 := bstep (se 1 (by rfl) ⟨820094, by rfl⟩ : syracuseStep 1093459 = 1640189) B1640189
theorem B4993159 : Blo 428775 4993159 := bstep (se 1 (by rfl) ⟨3744869, by rfl⟩ : syracuseStep 4993159 = 7489739) B7489739
theorem B11088089 : Blo 428775 11088089 := bstep (se 2 (by rfl) ⟨4158033, by rfl⟩ : syracuseStep 11088089 = 8316067) B8316067
theorem B1094057 : Blo 428775 1094057 := bstep (se 2 (by rfl) ⟨410271, by rfl⟩ : syracuseStep 1094057 = 820543) B820543
theorem B1454543 : Blo 428775 1454543 := bstep (se 1 (by rfl) ⟨1090907, by rfl⟩ : syracuseStep 1454543 = 2181815) B2181815
theorem B1225199 : Blo 428775 1225199 := bstep (se 1 (by rfl) ⟨918899, by rfl⟩ : syracuseStep 1225199 = 1837799) B1837799
theorem B1094249 : Blo 428775 1094249 := bstep (se 2 (by rfl) ⟨410343, by rfl⟩ : syracuseStep 1094249 = 820687) B820687
theorem B5256251 : Blo 428775 5256251 := bstep (se 1 (by rfl) ⟨3942188, by rfl⟩ : syracuseStep 5256251 = 7884377) B7884377
theorem B4895963 : Blo 428775 4895963 := bstep (se 1 (by rfl) ⟨3671972, by rfl⟩ : syracuseStep 4895963 = 7343945) B7343945
theorem B4962221 : Blo 428775 4962221 := bstep (se 3 (by rfl) ⟨930416, by rfl⟩ : syracuseStep 4962221 = 1860833) B1860833
theorem B3094537 : Blo 428775 3094537 := bstep (se 2 (by rfl) ⟨1160451, by rfl⟩ : syracuseStep 3094537 = 2320903) B2320903
theorem B2177441 : Blo 428775 2177441 := bstep (se 2 (by rfl) ⟨816540, by rfl⟩ : syracuseStep 2177441 = 1633081) B1633081
theorem B965051 : Blo 428775 965051 := bstep (se 1 (by rfl) ⟨723788, by rfl⟩ : syracuseStep 965051 = 1447577) B1447577
theorem B965915 : Blo 428775 965915 := bstep (se 1 (by rfl) ⟨724436, by rfl⟩ : syracuseStep 965915 = 1448873) B1448873
theorem B2178899 : Blo 428775 2178899 := bstep (se 1 (by rfl) ⟨1634174, by rfl⟩ : syracuseStep 2178899 = 3268349) B3268349
theorem B966491 : Blo 428775 966491 := bstep (se 1 (by rfl) ⟨724868, by rfl⟩ : syracuseStep 966491 = 1449737) B1449737
theorem B2244755 : Blo 428775 2244755 := bstep (se 1 (by rfl) ⟨1683566, by rfl⟩ : syracuseStep 2244755 = 3367133) B3367133
theorem B966815 : Blo 428775 966815 := bstep (se 1 (by rfl) ⟨725111, by rfl⟩ : syracuseStep 966815 = 1450223) B1450223
theorem B967049 : Blo 428775 967049 := bstep (se 2 (by rfl) ⟨362643, by rfl⟩ : syracuseStep 967049 = 725287) B725287
theorem B2179871 : Blo 428775 2179871 := bstep (se 1 (by rfl) ⟨1634903, by rfl⟩ : syracuseStep 2179871 = 3269807) B3269807
theorem B1786681 : Blo 428775 1786681 := bstep (se 2 (by rfl) ⟨670005, by rfl⟩ : syracuseStep 1786681 = 1340011) B1340011
theorem B2442311 : Blo 428775 2442311 := bstep (se 1 (by rfl) ⟨1831733, by rfl⟩ : syracuseStep 2442311 = 3663467) B3663467
theorem B12436739 : Blo 428775 12436739 := bstep (se 1 (by rfl) ⟨9327554, by rfl⟩ : syracuseStep 12436739 = 18655109) B18655109
theorem B1459511 : Blo 428775 1459511 := bstep (se 1 (by rfl) ⟨1094633, by rfl⟩ : syracuseStep 1459511 = 2189267) B2189267
theorem B2442743 : Blo 428775 2442743 := bstep (se 1 (by rfl) ⟨1832057, by rfl⟩ : syracuseStep 2442743 = 3664115) B3664115
theorem B1230461 : Blo 428775 1230461 := bstep (se 3 (by rfl) ⟨230711, by rfl⟩ : syracuseStep 1230461 = 461423) B461423
theorem B18695933 : Blo 428775 18695933 := bstep (se 3 (by rfl) ⟨3505487, by rfl⟩ : syracuseStep 18695933 = 7010975) B7010975
theorem B2934767 : Blo 428775 2934767 := bstep (se 1 (by rfl) ⟨2201075, by rfl⟩ : syracuseStep 2934767 = 4402151) B4402151
theorem B2181167 : Blo 428775 2181167 := bstep (se 1 (by rfl) ⟨1635875, by rfl⟩ : syracuseStep 2181167 = 3271751) B3271751
theorem B1231145 : Blo 428775 1231145 := bstep (se 2 (by rfl) ⟨461679, by rfl⟩ : syracuseStep 1231145 = 923359) B923359
theorem B969191 : Blo 428775 969191 := bstep (se 1 (by rfl) ⟨726893, by rfl⟩ : syracuseStep 969191 = 1453787) B1453787
theorem B543439 : Blo 428775 543439 := bstep (se 1 (by rfl) ⟨407579, by rfl⟩ : syracuseStep 543439 = 815159) B815159
theorem B969839 : Blo 428775 969839 := bstep (se 1 (by rfl) ⟨727379, by rfl⟩ : syracuseStep 969839 = 1454759) B1454759
theorem B970055 : Blo 428775 970055 := bstep (se 1 (by rfl) ⟨727541, by rfl⟩ : syracuseStep 970055 = 1455083) B1455083
theorem B10506341 : Blo 428775 10506341 := bstep (se 4 (by rfl) ⟨984969, by rfl⟩ : syracuseStep 10506341 = 1969939) B1969939
theorem B643559 : Blo 428775 643559 := bstep (se 1 (by rfl) ⟨482669, by rfl⟩ : syracuseStep 643559 = 965339) B965339
theorem B2609657 : Blo 428775 2609657 := bstep (se 2 (by rfl) ⟨978621, by rfl⟩ : syracuseStep 2609657 = 1957243) B1957243
theorem B3363401 : Blo 428775 3363401 := bstep (se 2 (by rfl) ⟨1261275, by rfl⟩ : syracuseStep 3363401 = 2522551) B2522551
theorem B971423 : Blo 428775 971423 := bstep (se 1 (by rfl) ⟨728567, by rfl⟩ : syracuseStep 971423 = 1457135) B1457135
theorem B10474433 : Blo 428775 10474433 := bstep (se 2 (by rfl) ⟨3927912, by rfl⟩ : syracuseStep 10474433 = 7855825) B7855825
theorem B644207 : Blo 428775 644207 := bstep (se 1 (by rfl) ⟨483155, by rfl⟩ : syracuseStep 644207 = 966311) B966311
theorem B644255 : Blo 428775 644255 := bstep (se 1 (by rfl) ⟨483191, by rfl⟩ : syracuseStep 644255 = 966383) B966383
theorem B971999 : Blo 428775 971999 := bstep (se 1 (by rfl) ⟨728999, by rfl⟩ : syracuseStep 971999 = 1457999) B1457999
theorem B611563 : Blo 428775 611563 := bstep (se 1 (by rfl) ⟨458672, by rfl⟩ : syracuseStep 611563 = 917345) B917345
theorem B972395 : Blo 428775 972395 := bstep (se 1 (by rfl) ⟨729296, by rfl⟩ : syracuseStep 972395 = 1458593) B1458593
theorem B645497 : Blo 428775 645497 := bstep (se 2 (by rfl) ⟨242061, by rfl⟩ : syracuseStep 645497 = 484123) B484123
theorem B973367 : Blo 428775 973367 := bstep (se 1 (by rfl) ⟨730025, by rfl⟩ : syracuseStep 973367 = 1460051) B1460051
theorem B646793 : Blo 428775 646793 := bstep (se 2 (by rfl) ⟨242547, by rfl⟩ : syracuseStep 646793 = 485095) B485095
theorem B483655 : Blo 428775 483655 := bstep (se 1 (by rfl) ⟨362741, by rfl⟩ : syracuseStep 483655 = 725483) B725483
theorem B647495 : Blo 428775 647495 := bstep (se 1 (by rfl) ⟨485621, by rfl⟩ : syracuseStep 647495 = 971243) B971243
theorem B1958393 : Blo 428775 1958393 := bstep (se 2 (by rfl) ⟨734397, by rfl⟩ : syracuseStep 1958393 = 1468795) B1468795
theorem B647963 : Blo 428775 647963 := bstep (se 1 (by rfl) ⟨485972, by rfl⟩ : syracuseStep 647963 = 971945) B971945
theorem B1107047 : Blo 428775 1107047 := bstep (se 1 (by rfl) ⟨830285, by rfl⟩ : syracuseStep 1107047 = 1660571) B1660571
theorem B648347 : Blo 428775 648347 := bstep (se 1 (by rfl) ⟨486260, by rfl⟩ : syracuseStep 648347 = 972521) B972521
theorem B2319673 : Blo 428775 2319673 := bstep (se 2 (by rfl) ⟨869877, by rfl⟩ : syracuseStep 2319673 = 1739755) B1739755
theorem B779603 : Blo 428775 779603 := bstep (se 1 (by rfl) ⟨584702, by rfl⟩ : syracuseStep 779603 = 1169405) B1169405
theorem B648569 : Blo 428775 648569 := bstep (se 2 (by rfl) ⟨243213, by rfl⟩ : syracuseStep 648569 = 486427) B486427
theorem B550351 : Blo 428775 550351 := bstep (se 1 (by rfl) ⟨412763, by rfl⟩ : syracuseStep 550351 = 825527) B825527
theorem B485023 : Blo 428775 485023 := bstep (se 1 (by rfl) ⟨363767, by rfl⟩ : syracuseStep 485023 = 727535) B727535
theorem B4155421 : Blo 428775 4155421 := bstep (se 3 (by rfl) ⟨779141, by rfl⟩ : syracuseStep 4155421 = 1558283) B1558283
theorem B13920497 : Blo 428775 13920497 := bstep (se 2 (by rfl) ⟨5220186, by rfl⟩ : syracuseStep 13920497 = 10440373) B10440373
theorem B1632595 : Blo 428775 1632595 := bstep (se 1 (by rfl) ⟨1224446, by rfl⟩ : syracuseStep 1632595 = 2448893) B2448893
theorem B486175 : Blo 428775 486175 := bstep (se 1 (by rfl) ⟨364631, by rfl⟩ : syracuseStep 486175 = 729263) B729263
theorem B6220907 : Blo 428775 6220907 := bstep (se 1 (by rfl) ⟨4665680, by rfl⟩ : syracuseStep 6220907 = 9331361) B9331361
theorem B2485727 : Blo 428775 2485727 := bstep (se 1 (by rfl) ⟨1864295, by rfl⟩ : syracuseStep 2485727 = 3728591) B3728591
theorem B2322287 : Blo 428775 2322287 := bstep (se 1 (by rfl) ⟨1741715, by rfl⟩ : syracuseStep 2322287 = 3483431) B3483431
theorem B2453449 : Blo 428775 2453449 := bstep (se 2 (by rfl) ⟨920043, by rfl⟩ : syracuseStep 2453449 = 1840087) B1840087
theorem B4124819 : Blo 428775 4124819 := bstep (se 1 (by rfl) ⟨3093614, by rfl⟩ : syracuseStep 4124819 = 6187229) B6187229
theorem B4125127 : Blo 428775 4125127 := bstep (se 1 (by rfl) ⟨3093845, by rfl⟩ : syracuseStep 4125127 = 6187691) B6187691
theorem B2060873 : Blo 428775 2060873 := bstep (se 2 (by rfl) ⟨772827, by rfl⟩ : syracuseStep 2060873 = 1545655) B1545655
theorem B6288029 : Blo 428775 6288029 := bstep (se 3 (by rfl) ⟨1179005, by rfl⟩ : syracuseStep 6288029 = 2358011) B2358011
theorem B1635011 : Blo 428775 1635011 := bstep (se 1 (by rfl) ⟨1226258, by rfl⟩ : syracuseStep 1635011 = 2452517) B2452517
theorem B4912001 : Blo 428775 4912001 := bstep (se 2 (by rfl) ⟨1842000, by rfl⟩ : syracuseStep 4912001 = 3684001) B3684001
theorem B1635815 : Blo 428775 1635815 := bstep (se 1 (by rfl) ⟨1226861, by rfl⟩ : syracuseStep 1635815 = 2453723) B2453723
theorem B2455865 : Blo 428775 2455865 := bstep (se 2 (by rfl) ⟨920949, by rfl⟩ : syracuseStep 2455865 = 1841899) B1841899
theorem B1375339 : Blo 428775 1375339 := bstep (se 1 (by rfl) ⟨1031504, by rfl⟩ : syracuseStep 1375339 = 2063009) B2063009
theorem B982343 : Blo 428775 982343 := bstep (se 1 (by rfl) ⟨736757, by rfl⟩ : syracuseStep 982343 = 1473515) B1473515
theorem B1048043 : Blo 428775 1048043 := bstep (se 1 (by rfl) ⟨786032, by rfl⟩ : syracuseStep 1048043 = 1572065) B1572065
theorem B44596757 : Blo 428775 44596757 := bstep (se 6 (by rfl) ⟨1045236, by rfl⟩ : syracuseStep 44596757 = 2090473) B2090473
theorem B6652489 : Blo 428775 6652489 := bstep (se 2 (by rfl) ⟨2494683, by rfl⟩ : syracuseStep 6652489 = 4989367) B4989367
theorem B8291159 : Blo 428775 8291159 := bstep (se 1 (by rfl) ⟨6218369, by rfl⟩ : syracuseStep 8291159 = 12436739) B12436739
theorem B820307 : Blo 428775 820307 := bstep (se 1 (by rfl) ⟨615230, by rfl⟩ : syracuseStep 820307 = 1230461) B1230461
theorem B6358175 : Blo 428775 6358175 := bstep (se 1 (by rfl) ⟨4768631, by rfl⟩ : syracuseStep 6358175 = 9537263) B9537263
theorem B918695 : Blo 428775 918695 := bstep (se 1 (by rfl) ⟨689021, by rfl⟩ : syracuseStep 918695 = 1378043) B1378043
theorem B5244425 : Blo 428775 5244425 := bstep (se 2 (by rfl) ⟨1966659, by rfl⟩ : syracuseStep 5244425 = 3933319) B3933319
theorem B820763 : Blo 428775 820763 := bstep (se 1 (by rfl) ⟨615572, by rfl⟩ : syracuseStep 820763 = 1231145) B1231145
theorem B11798615 : Blo 428775 11798615 := bstep (se 1 (by rfl) ⟨8848961, by rfl⟩ : syracuseStep 11798615 = 17697923) B17697923
theorem B1050751 : Blo 428775 1050751 := bstep (se 1 (by rfl) ⟨788063, by rfl⟩ : syracuseStep 1050751 = 1576127) B1576127
theorem B592351 : Blo 428775 592351 := bstep (se 1 (by rfl) ⟨444263, by rfl⟩ : syracuseStep 592351 = 888527) B888527
theorem B5540561 : Blo 428775 5540561 := bstep (se 2 (by rfl) ⟨2077710, by rfl⟩ : syracuseStep 5540561 = 4155421) B4155421
theorem B429039 : Blo 428775 429039 := bstep (se 1 (by rfl) ⟨321779, by rfl⟩ : syracuseStep 429039 = 643559) B643559
theorem B1739771 : Blo 428775 1739771 := bstep (se 1 (by rfl) ⟨1304828, by rfl⟩ : syracuseStep 1739771 = 2609657) B2609657
theorem B6982955 : Blo 428775 6982955 := bstep (se 1 (by rfl) ⟨5237216, by rfl⟩ : syracuseStep 6982955 = 10474433) B10474433
theorem B429471 : Blo 428775 429471 := bstep (se 1 (by rfl) ⟨322103, by rfl⟩ : syracuseStep 429471 = 644207) B644207
theorem B429503 : Blo 428775 429503 := bstep (se 1 (by rfl) ⟨322127, by rfl⟩ : syracuseStep 429503 = 644255) B644255
theorem B724585 : Blo 428775 724585 := bstep (se 2 (by rfl) ⟨271719, by rfl⟩ : syracuseStep 724585 = 543439) B543439
theorem B724639 : Blo 428775 724639 := bstep (se 1 (by rfl) ⟨543479, by rfl⟩ : syracuseStep 724639 = 1086959) B1086959
theorem B430331 : Blo 428775 430331 := bstep (se 1 (by rfl) ⟨322748, by rfl⟩ : syracuseStep 430331 = 645497) B645497
theorem B431195 : Blo 428775 431195 := bstep (se 1 (by rfl) ⟨323396, by rfl⟩ : syracuseStep 431195 = 646793) B646793
theorem B42407023 : Blo 428775 42407023 := bstep (se 1 (by rfl) ⟨31805267, by rfl⟩ : syracuseStep 42407023 = 63610535) B63610535
theorem B726239 : Blo 428775 726239 := bstep (se 1 (by rfl) ⟨544679, by rfl⟩ : syracuseStep 726239 = 1089359) B1089359
theorem B6657545 : Blo 428775 6657545 := bstep (se 2 (by rfl) ⟨2496579, by rfl⟩ : syracuseStep 6657545 = 4993159) B4993159
theorem B431663 : Blo 428775 431663 := bstep (se 1 (by rfl) ⟨323747, by rfl⟩ : syracuseStep 431663 = 647495) B647495
theorem B726583 : Blo 428775 726583 := bstep (se 1 (by rfl) ⟨544937, by rfl⟩ : syracuseStep 726583 = 1089875) B1089875
theorem B431975 : Blo 428775 431975 := bstep (se 1 (by rfl) ⟨323981, by rfl⟩ : syracuseStep 431975 = 647963) B647963
theorem B432231 : Blo 428775 432231 := bstep (se 1 (by rfl) ⟨324173, by rfl⟩ : syracuseStep 432231 = 648347) B648347
theorem B432379 : Blo 428775 432379 := bstep (se 1 (by rfl) ⟨324284, by rfl⟩ : syracuseStep 432379 = 648569) B648569
theorem B9280331 : Blo 428775 9280331 := bstep (se 1 (by rfl) ⟨6960248, by rfl⟩ : syracuseStep 9280331 = 13920497) B13920497
theorem B728527 : Blo 428775 728527 := bstep (se 1 (by rfl) ⟨546395, by rfl⟩ : syracuseStep 728527 = 1092791) B1092791
theorem B1548191 : Blo 428775 1548191 := bstep (se 1 (by rfl) ⟨1161143, by rfl⟩ : syracuseStep 1548191 = 2322287) B2322287
theorem B729371 : Blo 428775 729371 := bstep (se 1 (by rfl) ⟨547028, by rfl⟩ : syracuseStep 729371 = 1094057) B1094057
theorem B729499 : Blo 428775 729499 := bstep (se 1 (by rfl) ⟨547124, by rfl⟩ : syracuseStep 729499 = 1094249) B1094249
theorem B1090007 : Blo 428775 1090007 := bstep (se 1 (by rfl) ⟨817505, by rfl⟩ : syracuseStep 1090007 = 1635011) B1635011
theorem B1090543 : Blo 428775 1090543 := bstep (se 1 (by rfl) ⟨817907, by rfl⟩ : syracuseStep 1090543 = 1635815) B1635815
theorem B2794781 : Blo 428775 2794781 := bstep (se 3 (by rfl) ⟨524021, by rfl⟩ : syracuseStep 2794781 = 1048043) B1048043
theorem B1451627 : Blo 428775 1451627 := bstep (se 1 (by rfl) ⟨1088720, by rfl⟩ : syracuseStep 1451627 = 2177441) B2177441
theorem B29731171 : Blo 428775 29731171 := bstep (se 1 (by rfl) ⟨22298378, by rfl⟩ : syracuseStep 29731171 = 44596757) B44596757
theorem B1452599 : Blo 428775 1452599 := bstep (se 1 (by rfl) ⟨1089449, by rfl⟩ : syracuseStep 1452599 = 2178899) B2178899
theorem B1223581 : Blo 428775 1223581 := bstep (se 3 (by rfl) ⟨229421, by rfl⟩ : syracuseStep 1223581 = 458843) B458843
theorem B1453247 : Blo 428775 1453247 := bstep (se 1 (by rfl) ⟨1089935, by rfl⟩ : syracuseStep 1453247 = 2179871) B2179871
theorem B12463955 : Blo 428775 12463955 := bstep (se 1 (by rfl) ⟨9347966, by rfl⟩ : syracuseStep 12463955 = 18695933) B18695933
theorem B1454111 : Blo 428775 1454111 := bstep (se 1 (by rfl) ⟨1090583, by rfl⟩ : syracuseStep 1454111 = 2181167) B2181167
theorem B1225039 : Blo 428775 1225039 := bstep (se 1 (by rfl) ⟨918779, by rfl⟩ : syracuseStep 1225039 = 1837559) B1837559
theorem B3092897 : Blo 428775 3092897 := bstep (se 2 (by rfl) ⟨1159836, by rfl⟩ : syracuseStep 3092897 = 2319673) B2319673
theorem B1095241 : Blo 428775 1095241 := bstep (se 2 (by rfl) ⟨410715, by rfl⟩ : syracuseStep 1095241 = 821431) B821431
theorem B2176793 : Blo 428775 2176793 := bstep (se 2 (by rfl) ⟨816297, by rfl⟩ : syracuseStep 2176793 = 1632595) B1632595
theorem B3258143 : Blo 428775 3258143 := bstep (se 1 (by rfl) ⟨2443607, by rfl⟩ : syracuseStep 3258143 = 4887215) B4887215
theorem B1226623 : Blo 428775 1226623 := bstep (se 1 (by rfl) ⟨919967, by rfl⟩ : syracuseStep 1226623 = 1839935) B1839935
theorem B1554335 : Blo 428775 1554335 := bstep (se 1 (by rfl) ⟨1165751, by rfl⟩ : syracuseStep 1554335 = 2331503) B2331503
theorem B2078941 : Blo 428775 2078941 := bstep (se 3 (by rfl) ⟨389801, by rfl⟩ : syracuseStep 2078941 = 779603) B779603
theorem B1457945 : Blo 428775 1457945 := bstep (se 2 (by rfl) ⟨546729, by rfl⟩ : syracuseStep 1457945 = 1093459) B1093459
theorem B967067 : Blo 428775 967067 := bstep (se 1 (by rfl) ⟨725300, by rfl⟩ : syracuseStep 967067 = 1450601) B1450601
theorem B1557103 : Blo 428775 1557103 := bstep (se 1 (by rfl) ⟨1167827, by rfl⟩ : syracuseStep 1557103 = 2335655) B2335655
theorem B738031 : Blo 428775 738031 := bstep (se 1 (by rfl) ⟨553523, by rfl⟩ : syracuseStep 738031 = 1107047) B1107047
theorem B4147271 : Blo 428775 4147271 := bstep (se 1 (by rfl) ⟨3110453, by rfl⟩ : syracuseStep 4147271 = 6220907) B6220907
theorem B105171209 : Blo 428775 105171209 := bstep (se 2 (by rfl) ⟨39439203, by rfl⟩ : syracuseStep 105171209 = 78878407) B78878407
theorem B1657151 : Blo 428775 1657151 := bstep (se 1 (by rfl) ⟨1242863, by rfl⟩ : syracuseStep 1657151 = 2485727) B2485727
theorem B2935205 : Blo 428775 2935205 := bstep (se 4 (by rfl) ⟨275175, by rfl⟩ : syracuseStep 2935205 = 550351) B550351
theorem B7392059 : Blo 428775 7392059 := bstep (se 1 (by rfl) ⟨5544044, by rfl⟩ : syracuseStep 7392059 = 11088089) B11088089
theorem B969695 : Blo 428775 969695 := bstep (se 1 (by rfl) ⟨727271, by rfl⟩ : syracuseStep 969695 = 1454543) B1454543
theorem B3263975 : Blo 428775 3263975 := bstep (se 1 (by rfl) ⟨2447981, by rfl⟩ : syracuseStep 3263975 = 4895963) B4895963
theorem B643367 : Blo 428775 643367 := bstep (se 1 (by rfl) ⟨482525, by rfl⟩ : syracuseStep 643367 = 965051) B965051
theorem B643943 : Blo 428775 643943 := bstep (se 1 (by rfl) ⟨482957, by rfl⟩ : syracuseStep 643943 = 965915) B965915
theorem B644327 : Blo 428775 644327 := bstep (se 1 (by rfl) ⟨483245, by rfl⟩ : syracuseStep 644327 = 966491) B966491
theorem B1496503 : Blo 428775 1496503 := bstep (se 1 (by rfl) ⟨1122377, by rfl⟩ : syracuseStep 1496503 = 2244755) B2244755
theorem B644543 : Blo 428775 644543 := bstep (se 1 (by rfl) ⟨483407, by rfl⟩ : syracuseStep 644543 = 966815) B966815
theorem B644699 : Blo 428775 644699 := bstep (se 1 (by rfl) ⟨483524, by rfl⟩ : syracuseStep 644699 = 967049) B967049
theorem B644873 : Blo 428775 644873 := bstep (se 2 (by rfl) ⟨241827, by rfl⟩ : syracuseStep 644873 = 483655) B483655
theorem B1628207 : Blo 428775 1628207 := bstep (se 1 (by rfl) ⟨1221155, by rfl⟩ : syracuseStep 1628207 = 2442311) B2442311
theorem B973007 : Blo 428775 973007 := bstep (se 1 (by rfl) ⟨729755, by rfl⟩ : syracuseStep 973007 = 1459511) B1459511
theorem B1628495 : Blo 428775 1628495 := bstep (se 1 (by rfl) ⟨1221371, by rfl⟩ : syracuseStep 1628495 = 2442743) B2442743
theorem B1956511 : Blo 428775 1956511 := bstep (se 1 (by rfl) ⟨1467383, by rfl⟩ : syracuseStep 1956511 = 2934767) B2934767
theorem B8969069 : Blo 428775 8969069 := bstep (se 3 (by rfl) ⟨1681700, by rfl⟩ : syracuseStep 8969069 = 3363401) B3363401
theorem B646127 : Blo 428775 646127 := bstep (se 1 (by rfl) ⟨484595, by rfl⟩ : syracuseStep 646127 = 969191) B969191
theorem B646559 : Blo 428775 646559 := bstep (se 1 (by rfl) ⟨484919, by rfl⟩ : syracuseStep 646559 = 969839) B969839
theorem B1629665 : Blo 428775 1629665 := bstep (se 2 (by rfl) ⟨611124, by rfl⟩ : syracuseStep 1629665 = 1222249) B1222249
theorem B646697 : Blo 428775 646697 := bstep (se 2 (by rfl) ⟨242511, by rfl⟩ : syracuseStep 646697 = 485023) B485023
theorem B646703 : Blo 428775 646703 := bstep (se 1 (by rfl) ⟨485027, by rfl⟩ : syracuseStep 646703 = 970055) B970055
theorem B7004227 : Blo 428775 7004227 := bstep (se 1 (by rfl) ⟨5253170, by rfl⟩ : syracuseStep 7004227 = 10506341) B10506341
theorem B647615 : Blo 428775 647615 := bstep (se 1 (by rfl) ⟨485711, by rfl⟩ : syracuseStep 647615 = 971423) B971423
theorem B2187971 : Blo 428775 2187971 := bstep (se 1 (by rfl) ⟨1640978, by rfl⟩ : syracuseStep 2187971 = 3281957) B3281957
theorem B647999 : Blo 428775 647999 := bstep (se 1 (by rfl) ⟨485999, by rfl⟩ : syracuseStep 647999 = 971999) B971999
theorem B3695483 : Blo 428775 3695483 := bstep (se 1 (by rfl) ⟨2771612, by rfl⟩ : syracuseStep 3695483 = 5543225) B5543225
theorem B648233 : Blo 428775 648233 := bstep (se 2 (by rfl) ⟨243087, by rfl⟩ : syracuseStep 648233 = 486175) B486175
theorem B648263 : Blo 428775 648263 := bstep (se 1 (by rfl) ⟨486197, by rfl⟩ : syracuseStep 648263 = 972395) B972395
theorem B1631609 : Blo 428775 1631609 := bstep (se 2 (by rfl) ⟨611853, by rfl⟩ : syracuseStep 1631609 = 1223707) B1223707
theorem B484735 : Blo 428775 484735 := bstep (se 1 (by rfl) ⟨363551, by rfl⟩ : syracuseStep 484735 = 727103) B727103
theorem B9528965 : Blo 428775 9528965 := bstep (se 4 (by rfl) ⟨893340, by rfl⟩ : syracuseStep 9528965 = 1786681) B1786681
theorem B648911 : Blo 428775 648911 := bstep (se 1 (by rfl) ⟨486683, by rfl⟩ : syracuseStep 648911 = 973367) B973367
theorem B2451809 : Blo 428775 2451809 := bstep (se 2 (by rfl) ⟨919428, by rfl⟩ : syracuseStep 2451809 = 1838857) B1838857
theorem B3271265 : Blo 428775 3271265 := bstep (se 2 (by rfl) ⟨1226724, by rfl⟩ : syracuseStep 3271265 = 2453449) B2453449
theorem B1305595 : Blo 428775 1305595 := bstep (se 1 (by rfl) ⟨979196, by rfl⟩ : syracuseStep 1305595 = 1958393) B1958393
theorem B5500169 : Blo 428775 5500169 := bstep (se 2 (by rfl) ⟨2062563, by rfl⟩ : syracuseStep 5500169 = 4125127) B4125127
theorem B6975163 : Blo 428775 6975163 := bstep (se 1 (by rfl) ⟨5231372, by rfl⟩ : syracuseStep 6975163 = 10462745) B10462745
theorem B814931 : Blo 428775 814931 := bstep (se 1 (by rfl) ⟨611198, by rfl⟩ : syracuseStep 814931 = 1222397) B1222397
theorem B815417 : Blo 428775 815417 := bstep (se 2 (by rfl) ⟨305781, by rfl⟩ : syracuseStep 815417 = 611563) B611563
theorem B16741241 : Blo 428775 16741241 := bstep (se 2 (by rfl) ⟨6277965, by rfl⟩ : syracuseStep 16741241 = 12555931) B12555931
theorem B4126049 : Blo 428775 4126049 := bstep (se 2 (by rfl) ⟨1547268, by rfl⟩ : syracuseStep 4126049 = 3094537) B3094537
theorem B2749879 : Blo 428775 2749879 := bstep (se 1 (by rfl) ⟨2062409, by rfl⟩ : syracuseStep 2749879 = 4124819) B4124819
theorem B816799 : Blo 428775 816799 := bstep (se 1 (by rfl) ⟨612599, by rfl⟩ : syracuseStep 816799 = 1225199) B1225199
theorem B1373915 : Blo 428775 1373915 := bstep (se 1 (by rfl) ⟨1030436, by rfl⟩ : syracuseStep 1373915 = 2060873) B2060873
theorem B4192019 : Blo 428775 4192019 := bstep (se 1 (by rfl) ⟨3144014, by rfl⟩ : syracuseStep 4192019 = 6288029) B6288029
theorem B3274667 : Blo 428775 3274667 := bstep (se 1 (by rfl) ⟨2456000, by rfl⟩ : syracuseStep 3274667 = 4912001) B4912001
theorem B3504167 : Blo 428775 3504167 := bstep (se 1 (by rfl) ⟨2628125, by rfl⟩ : syracuseStep 3504167 = 5256251) B5256251
theorem B3308147 : Blo 428775 3308147 := bstep (se 1 (by rfl) ⟨2481110, by rfl⟩ : syracuseStep 3308147 = 4962221) B4962221
theorem B1833785 : Blo 428775 1833785 := bstep (se 2 (by rfl) ⟨687669, by rfl⟩ : syracuseStep 1833785 = 1375339) B1375339
theorem B1637243 : Blo 428775 1637243 := bstep (se 1 (by rfl) ⟨1227932, by rfl⟩ : syracuseStep 1637243 = 2455865) B2455865
theorem B654895 : Blo 428775 654895 := bstep (se 1 (by rfl) ⟨491171, by rfl⟩ : syracuseStep 654895 = 982343) B982343
theorem B9338969 : Blo 428775 9338969 := bstep (se 2 (by rfl) ⟨3502113, by rfl⟩ : syracuseStep 9338969 = 7004227) B7004227
theorem B984041 : Blo 428775 984041 := bstep (se 2 (by rfl) ⟨369015, by rfl⟩ : syracuseStep 984041 = 738031) B738031
theorem B7865743 : Blo 428775 7865743 := bstep (se 1 (by rfl) ⟨5899307, by rfl⟩ : syracuseStep 7865743 = 11798615) B11798615
theorem B4655303 : Blo 428775 4655303 := bstep (se 1 (by rfl) ⟨3491477, by rfl⟩ : syracuseStep 4655303 = 6982955) B6982955
theorem B428911 : Blo 428775 428911 := bstep (se 1 (by rfl) ⟨321683, by rfl⟩ : syracuseStep 428911 = 643367) B643367
theorem B429295 : Blo 428775 429295 := bstep (se 1 (by rfl) ⟨321971, by rfl⟩ : syracuseStep 429295 = 643943) B643943
theorem B429551 : Blo 428775 429551 := bstep (se 1 (by rfl) ⟨322163, by rfl⟩ : syracuseStep 429551 = 644327) B644327
theorem B429695 : Blo 428775 429695 := bstep (se 1 (by rfl) ⟨322271, by rfl⟩ : syracuseStep 429695 = 644543) B644543
theorem B429799 : Blo 428775 429799 := bstep (se 1 (by rfl) ⟨322349, by rfl⟩ : syracuseStep 429799 = 644699) B644699
theorem B429915 : Blo 428775 429915 := bstep (se 1 (by rfl) ⟨322436, by rfl⟩ : syracuseStep 429915 = 644873) B644873
theorem B1740793 : Blo 428775 1740793 := bstep (se 2 (by rfl) ⟨652797, by rfl⟩ : syracuseStep 1740793 = 1305595) B1305595
theorem B1085471 : Blo 428775 1085471 := bstep (se 1 (by rfl) ⟨814103, by rfl⟩ : syracuseStep 1085471 = 1628207) B1628207
theorem B1085663 : Blo 428775 1085663 := bstep (se 1 (by rfl) ⟨814247, by rfl⟩ : syracuseStep 1085663 = 1628495) B1628495
theorem B430751 : Blo 428775 430751 := bstep (se 1 (by rfl) ⟨323063, by rfl⟩ : syracuseStep 430751 = 646127) B646127
theorem B431039 : Blo 428775 431039 := bstep (se 1 (by rfl) ⟨323279, by rfl⟩ : syracuseStep 431039 = 646559) B646559
theorem B1086443 : Blo 428775 1086443 := bstep (se 1 (by rfl) ⟨814832, by rfl⟩ : syracuseStep 1086443 = 1629665) B1629665
theorem B431131 : Blo 428775 431131 := bstep (se 1 (by rfl) ⟨323348, by rfl⟩ : syracuseStep 431131 = 646697) B646697
theorem B431135 : Blo 428775 431135 := bstep (se 1 (by rfl) ⟨323351, by rfl⟩ : syracuseStep 431135 = 646703) B646703
theorem B431743 : Blo 428775 431743 := bstep (se 1 (by rfl) ⟨323807, by rfl⟩ : syracuseStep 431743 = 647615) B647615
theorem B726671 : Blo 428775 726671 := bstep (se 1 (by rfl) ⟨545003, by rfl⟩ : syracuseStep 726671 = 1090007) B1090007
theorem B431999 : Blo 428775 431999 := bstep (se 1 (by rfl) ⟨323999, by rfl⟩ : syracuseStep 431999 = 647999) B647999
theorem B2463655 : Blo 428775 2463655 := bstep (se 1 (by rfl) ⟨1847741, by rfl⟩ : syracuseStep 2463655 = 3695483) B3695483
theorem B432155 : Blo 428775 432155 := bstep (se 1 (by rfl) ⟨324116, by rfl⟩ : syracuseStep 432155 = 648233) B648233
theorem B432175 : Blo 428775 432175 := bstep (se 1 (by rfl) ⟨324131, by rfl⟩ : syracuseStep 432175 = 648263) B648263
theorem B1087739 : Blo 428775 1087739 := bstep (se 1 (by rfl) ⟨815804, by rfl⟩ : syracuseStep 1087739 = 1631609) B1631609
theorem B432607 : Blo 428775 432607 := bstep (se 1 (by rfl) ⟨324455, by rfl⟩ : syracuseStep 432607 = 648911) B648911
theorem B1089065 : Blo 428775 1089065 := bstep (se 2 (by rfl) ⟨408399, by rfl⟩ : syracuseStep 1089065 = 816799) B816799
theorem B37200869 : Blo 428775 37200869 := bstep (se 4 (by rfl) ⟨3487581, by rfl⟩ : syracuseStep 37200869 = 6975163) B6975163
theorem B2794679 : Blo 428775 2794679 := bstep (se 1 (by rfl) ⟨2096009, by rfl⟩ : syracuseStep 2794679 = 4192019) B4192019
theorem B1451195 : Blo 428775 1451195 := bstep (se 1 (by rfl) ⟨1088396, by rfl⟩ : syracuseStep 1451195 = 2176793) B2176793
theorem B2172095 : Blo 428775 2172095 := bstep (se 1 (by rfl) ⟨1629071, by rfl⟩ : syracuseStep 2172095 = 3258143) B3258143
theorem B2336111 : Blo 428775 2336111 := bstep (se 1 (by rfl) ⟨1752083, by rfl⟩ : syracuseStep 2336111 = 3504167) B3504167
theorem B2205431 : Blo 428775 2205431 := bstep (se 1 (by rfl) ⟨1654073, by rfl⟩ : syracuseStep 2205431 = 3308147) B3308147
theorem B1222523 : Blo 428775 1222523 := bstep (se 1 (by rfl) ⟨916892, by rfl⟩ : syracuseStep 1222523 = 1833785) B1833785
theorem B1091495 : Blo 428775 1091495 := bstep (se 1 (by rfl) ⟨818621, by rfl⟩ : syracuseStep 1091495 = 1637243) B1637243
theorem B4238783 : Blo 428775 4238783 := bstep (se 1 (by rfl) ⟨3179087, by rfl⟩ : syracuseStep 4238783 = 6358175) B6358175
theorem B2076137 : Blo 428775 2076137 := bstep (se 2 (by rfl) ⟨778551, by rfl⟩ : syracuseStep 2076137 = 1557103) B1557103
theorem B1454057 : Blo 428775 1454057 := bstep (se 2 (by rfl) ⟨545271, by rfl⟩ : syracuseStep 1454057 = 1090543) B1090543
theorem B2764847 : Blo 428775 2764847 := bstep (se 1 (by rfl) ⟨2073635, by rfl⟩ : syracuseStep 2764847 = 4147271) B4147271
theorem B4928039 : Blo 428775 4928039 := bstep (se 1 (by rfl) ⟨3696029, by rfl⟩ : syracuseStep 4928039 = 7392059) B7392059
theorem B1159847 : Blo 428775 1159847 := bstep (se 1 (by rfl) ⟨869885, by rfl⟩ : syracuseStep 1159847 = 1739771) B1739771
theorem B2175983 : Blo 428775 2175983 := bstep (se 1 (by rfl) ⟨1631987, by rfl⟩ : syracuseStep 2175983 = 3263975) B3263975
theorem B3159205 : Blo 428775 3159205 := bstep (se 4 (by rfl) ⟨296175, by rfl⟩ : syracuseStep 3159205 = 592351) B592351
theorem B7452749 : Blo 428775 7452749 := bstep (se 3 (by rfl) ⟨1397390, by rfl⟩ : syracuseStep 7452749 = 2794781) B2794781
theorem B4438363 : Blo 428775 4438363 := bstep (se 1 (by rfl) ⟨3328772, by rfl⟩ : syracuseStep 4438363 = 6657545) B6657545
theorem B5979379 : Blo 428775 5979379 := bstep (se 1 (by rfl) ⟨4484534, by rfl⟩ : syracuseStep 5979379 = 8969069) B8969069
theorem B966113 : Blo 428775 966113 := bstep (se 2 (by rfl) ⟨362292, by rfl⟩ : syracuseStep 966113 = 724585) B724585
theorem B966185 : Blo 428775 966185 := bstep (se 2 (by rfl) ⟨362319, by rfl⟩ : syracuseStep 966185 = 724639) B724639
theorem B1458647 : Blo 428775 1458647 := bstep (se 1 (by rfl) ⟨1093985, by rfl⟩ : syracuseStep 1458647 = 2187971) B2187971
theorem B967751 : Blo 428775 967751 := bstep (se 1 (by rfl) ⟨725813, by rfl⟩ : syracuseStep 967751 = 1451627) B1451627
theorem B56542697 : Blo 428775 56542697 := bstep (se 2 (by rfl) ⟨21203511, by rfl⟩ : syracuseStep 56542697 = 42407023) B42407023
theorem B968399 : Blo 428775 968399 := bstep (se 1 (by rfl) ⟨726299, by rfl⟩ : syracuseStep 968399 = 1452599) B1452599
theorem B2180843 : Blo 428775 2180843 := bstep (se 1 (by rfl) ⟨1635632, by rfl⟩ : syracuseStep 2180843 = 3271265) B3271265
theorem B968777 : Blo 428775 968777 := bstep (se 2 (by rfl) ⟨363291, by rfl⟩ : syracuseStep 968777 = 726583) B726583
theorem B1460321 : Blo 428775 1460321 := bstep (se 2 (by rfl) ⟨547620, by rfl⟩ : syracuseStep 1460321 = 1095241) B1095241
theorem B968831 : Blo 428775 968831 := bstep (se 1 (by rfl) ⟨726623, by rfl⟩ : syracuseStep 968831 = 1453247) B1453247
theorem B543287 : Blo 428775 543287 := bstep (se 1 (by rfl) ⟨407465, by rfl⟩ : syracuseStep 543287 = 814931) B814931
theorem B8309303 : Blo 428775 8309303 := bstep (se 1 (by rfl) ⟨6231977, by rfl⟩ : syracuseStep 8309303 = 12463955) B12463955
theorem B969407 : Blo 428775 969407 := bstep (se 1 (by rfl) ⟨727055, by rfl⟩ : syracuseStep 969407 = 1454111) B1454111
theorem B543611 : Blo 428775 543611 := bstep (se 1 (by rfl) ⟨407708, by rfl⟩ : syracuseStep 543611 = 815417) B815417
theorem B3492773 : Blo 428775 3492773 := bstep (se 4 (by rfl) ⟨327447, by rfl⟩ : syracuseStep 3492773 = 654895) B654895
theorem B2771921 : Blo 428775 2771921 := bstep (se 2 (by rfl) ⟨1039470, by rfl⟩ : syracuseStep 2771921 = 2078941) B2078941
theorem B11160827 : Blo 428775 11160827 := bstep (se 1 (by rfl) ⟨8370620, by rfl⟩ : syracuseStep 11160827 = 16741241) B16741241
theorem B2608681 : Blo 428775 2608681 := bstep (se 2 (by rfl) ⟨978255, by rfl⟩ : syracuseStep 2608681 = 1956511) B1956511
theorem B1036223 : Blo 428775 1036223 := bstep (se 1 (by rfl) ⟨777167, by rfl⟩ : syracuseStep 1036223 = 1554335) B1554335
theorem B2183111 : Blo 428775 2183111 := bstep (se 1 (by rfl) ⟨1637333, by rfl⟩ : syracuseStep 2183111 = 3274667) B3274667
theorem B971369 : Blo 428775 971369 := bstep (se 2 (by rfl) ⟨364263, by rfl⟩ : syracuseStep 971369 = 728527) B728527
theorem B971963 : Blo 428775 971963 := bstep (se 1 (by rfl) ⟨728972, by rfl⟩ : syracuseStep 971963 = 1457945) B1457945
theorem B644711 : Blo 428775 644711 := bstep (se 1 (by rfl) ⟨483533, by rfl⟩ : syracuseStep 644711 = 967067) B967067
theorem B972665 : Blo 428775 972665 := bstep (se 2 (by rfl) ⟨364749, by rfl⟩ : syracuseStep 972665 = 729499) B729499
theorem B5527439 : Blo 428775 5527439 := bstep (se 1 (by rfl) ⟨4145579, by rfl⟩ : syracuseStep 5527439 = 8291159) B8291159
theorem B8869985 : Blo 428775 8869985 := bstep (se 2 (by rfl) ⟨3326244, by rfl⟩ : syracuseStep 8869985 = 6652489) B6652489
theorem B612463 : Blo 428775 612463 := bstep (se 1 (by rfl) ⟨459347, by rfl⟩ : syracuseStep 612463 = 918695) B918695
theorem B3496283 : Blo 428775 3496283 := bstep (se 1 (by rfl) ⟨2622212, by rfl⟩ : syracuseStep 3496283 = 5244425) B5244425
theorem B547175 : Blo 428775 547175 := bstep (se 1 (by rfl) ⟨410381, by rfl⟩ : syracuseStep 547175 = 820763) B820763
theorem B70114139 : Blo 428775 70114139 := bstep (se 1 (by rfl) ⟨52585604, by rfl⟩ : syracuseStep 70114139 = 105171209) B105171209
theorem B1104767 : Blo 428775 1104767 := bstep (se 1 (by rfl) ⟨828575, by rfl⟩ : syracuseStep 1104767 = 1657151) B1657151
theorem B1956803 : Blo 428775 1956803 := bstep (se 1 (by rfl) ⟨1467602, by rfl⟩ : syracuseStep 1956803 = 2935205) B2935205
theorem B3693707 : Blo 428775 3693707 := bstep (se 1 (by rfl) ⟨2770280, by rfl⟩ : syracuseStep 3693707 = 5540561) B5540561
theorem B646313 : Blo 428775 646313 := bstep (se 2 (by rfl) ⟨242367, by rfl⟩ : syracuseStep 646313 = 484735) B484735
theorem B646463 : Blo 428775 646463 := bstep (se 1 (by rfl) ⟨484847, by rfl⟩ : syracuseStep 646463 = 969695) B969695
theorem B1401001 : Blo 428775 1401001 := bstep (se 2 (by rfl) ⟨525375, by rfl⟩ : syracuseStep 1401001 = 1050751) B1050751
theorem B2187485 : Blo 428775 2187485 := bstep (se 3 (by rfl) ⟨410153, by rfl⟩ : syracuseStep 2187485 = 820307) B820307
theorem B39641561 : Blo 428775 39641561 := bstep (se 2 (by rfl) ⟨14865585, by rfl⟩ : syracuseStep 39641561 = 29731171) B29731171
theorem B484159 : Blo 428775 484159 := bstep (se 1 (by rfl) ⟨363119, by rfl⟩ : syracuseStep 484159 = 726239) B726239
theorem B1631441 : Blo 428775 1631441 := bstep (se 2 (by rfl) ⟨611790, by rfl⟩ : syracuseStep 1631441 = 1223581) B1223581
theorem B648671 : Blo 428775 648671 := bstep (se 1 (by rfl) ⟨486503, by rfl⟩ : syracuseStep 648671 = 973007) B973007
theorem B6186887 : Blo 428775 6186887 := bstep (se 1 (by rfl) ⟨4640165, by rfl⟩ : syracuseStep 6186887 = 9280331) B9280331
theorem B486247 : Blo 428775 486247 := bstep (se 1 (by rfl) ⟨364685, by rfl⟩ : syracuseStep 486247 = 729371) B729371
theorem B1633385 : Blo 428775 1633385 := bstep (se 2 (by rfl) ⟨612519, by rfl⟩ : syracuseStep 1633385 = 1225039) B1225039
theorem B6352643 : Blo 428775 6352643 := bstep (se 1 (by rfl) ⟨4764482, by rfl⟩ : syracuseStep 6352643 = 9528965) B9528965
theorem B1634539 : Blo 428775 1634539 := bstep (se 1 (by rfl) ⟨1225904, by rfl⟩ : syracuseStep 1634539 = 2451809) B2451809
theorem B3666505 : Blo 428775 3666505 := bstep (se 2 (by rfl) ⟨1374939, by rfl⟩ : syracuseStep 3666505 = 2749879) B2749879
theorem B1995337 : Blo 428775 1995337 := bstep (se 2 (by rfl) ⟨748251, by rfl⟩ : syracuseStep 1995337 = 1496503) B1496503
theorem B3666779 : Blo 428775 3666779 := bstep (se 1 (by rfl) ⟨2750084, by rfl⟩ : syracuseStep 3666779 = 5500169) B5500169
theorem B1635497 : Blo 428775 1635497 := bstep (se 2 (by rfl) ⟨613311, by rfl⟩ : syracuseStep 1635497 = 1226623) B1226623
theorem B2061931 : Blo 428775 2061931 := bstep (se 1 (by rfl) ⟨1546448, by rfl⟩ : syracuseStep 2061931 = 3092897) B3092897
theorem B2750699 : Blo 428775 2750699 := bstep (se 1 (by rfl) ⟨2063024, by rfl⟩ : syracuseStep 2750699 = 4126049) B4126049
theorem B915943 : Blo 428775 915943 := bstep (se 1 (by rfl) ⟨686957, by rfl⟩ : syracuseStep 915943 = 1373915) B1373915
theorem B4128509 : Blo 428775 4128509 := bstep (se 3 (by rfl) ⟨774095, by rfl⟩ : syracuseStep 4128509 = 1548191) B1548191
theorem B6225979 : Blo 428775 6225979 := bstep (se 1 (by rfl) ⟨4669484, by rfl⟩ : syracuseStep 6225979 = 9338969) B9338969
theorem B656027 : Blo 428775 656027 := bstep (se 1 (by rfl) ⟨492020, by rfl⟩ : syracuseStep 656027 = 984041) B984041
theorem B5539535 : Blo 428775 5539535 := bstep (se 1 (by rfl) ⟨4154651, by rfl⟩ : syracuseStep 5539535 = 8309303) B8309303
theorem B10487657 : Blo 428775 10487657 := bstep (se 2 (by rfl) ⟨3932871, by rfl⟩ : syracuseStep 10487657 = 7865743) B7865743
theorem B2328515 : Blo 428775 2328515 := bstep (se 1 (by rfl) ⟨1746386, by rfl⟩ : syracuseStep 2328515 = 3492773) B3492773
theorem B7440551 : Blo 428775 7440551 := bstep (se 1 (by rfl) ⟨5580413, by rfl⟩ : syracuseStep 7440551 = 11160827) B11160827
theorem B690815 : Blo 428775 690815 := bstep (se 1 (by rfl) ⟨518111, by rfl⟩ : syracuseStep 690815 = 1036223) B1036223
theorem B723647 : Blo 428775 723647 := bstep (se 1 (by rfl) ⟨542735, by rfl⟩ : syracuseStep 723647 = 1085471) B1085471
theorem B723775 : Blo 428775 723775 := bstep (se 1 (by rfl) ⟨542831, by rfl⟩ : syracuseStep 723775 = 1085663) B1085663
theorem B724295 : Blo 428775 724295 := bstep (se 1 (by rfl) ⟨543221, by rfl⟩ : syracuseStep 724295 = 1086443) B1086443
theorem B29888021 : Blo 428775 29888021 := bstep (se 6 (by rfl) ⟨700500, by rfl⟩ : syracuseStep 29888021 = 1401001) B1401001
theorem B429807 : Blo 428775 429807 := bstep (se 1 (by rfl) ⟨322355, by rfl⟩ : syracuseStep 429807 = 644711) B644711
theorem B725159 : Blo 428775 725159 := bstep (se 1 (by rfl) ⟨543869, by rfl⟩ : syracuseStep 725159 = 1087739) B1087739
theorem B2330855 : Blo 428775 2330855 := bstep (se 1 (by rfl) ⟨1748141, by rfl⟩ : syracuseStep 2330855 = 3496283) B3496283
theorem B3478241 : Blo 428775 3478241 := bstep (se 2 (by rfl) ⟨1304340, by rfl⟩ : syracuseStep 3478241 = 2608681) B2608681
theorem B2462471 : Blo 428775 2462471 := bstep (se 1 (by rfl) ⟨1846853, by rfl⟩ : syracuseStep 2462471 = 3693707) B3693707
theorem B430875 : Blo 428775 430875 := bstep (se 1 (by rfl) ⟨323156, by rfl⟩ : syracuseStep 430875 = 646313) B646313
theorem B430975 : Blo 428775 430975 := bstep (se 1 (by rfl) ⟨323231, by rfl⟩ : syracuseStep 430975 = 646463) B646463
theorem B726043 : Blo 428775 726043 := bstep (se 1 (by rfl) ⟨544532, by rfl⟩ : syracuseStep 726043 = 1089065) B1089065
theorem B4888673 : Blo 428775 4888673 := bstep (se 2 (by rfl) ⟨1833252, by rfl⟩ : syracuseStep 4888673 = 3666505) B3666505
theorem B2660449 : Blo 428775 2660449 := bstep (se 2 (by rfl) ⟨997668, by rfl⟩ : syracuseStep 2660449 = 1995337) B1995337
theorem B1448063 : Blo 428775 1448063 := bstep (se 1 (by rfl) ⟨1086047, by rfl⟩ : syracuseStep 1448063 = 2172095) B2172095
theorem B1087627 : Blo 428775 1087627 := bstep (se 1 (by rfl) ⟨815720, by rfl⟩ : syracuseStep 1087627 = 1631441) B1631441
theorem B16849093 : Blo 428775 16849093 := bstep (se 4 (by rfl) ⟨1579602, by rfl⟩ : syracuseStep 16849093 = 3159205) B3159205
theorem B432447 : Blo 428775 432447 := bstep (se 1 (by rfl) ⟨324335, by rfl⟩ : syracuseStep 432447 = 648671) B648671
theorem B727663 : Blo 428775 727663 := bstep (se 1 (by rfl) ⟨545747, by rfl⟩ : syracuseStep 727663 = 1091495) B1091495
theorem B1448765 : Blo 428775 1448765 := bstep (se 3 (by rfl) ⟨271643, by rfl⟩ : syracuseStep 1448765 = 543287) B543287
theorem B1088923 : Blo 428775 1088923 := bstep (se 1 (by rfl) ⟨816692, by rfl⟩ : syracuseStep 1088923 = 1633385) B1633385
theorem B2825855 : Blo 428775 2825855 := bstep (se 1 (by rfl) ⟨2119391, by rfl⟩ : syracuseStep 2825855 = 4238783) B4238783
theorem B1384091 : Blo 428775 1384091 := bstep (se 1 (by rfl) ⟨1038068, by rfl⟩ : syracuseStep 1384091 = 2076137) B2076137
theorem B1449629 : Blo 428775 1449629 := bstep (se 3 (by rfl) ⟨271805, by rfl⟩ : syracuseStep 1449629 = 543611) B543611
theorem B4235095 : Blo 428775 4235095 := bstep (se 1 (by rfl) ⟨3176321, by rfl⟩ : syracuseStep 4235095 = 6352643) B6352643
theorem B5218141 : Blo 428775 5218141 := bstep (se 3 (by rfl) ⟨978401, by rfl⟩ : syracuseStep 5218141 = 1956803) B1956803
theorem B3284873 : Blo 428775 3284873 := bstep (se 2 (by rfl) ⟨1231827, by rfl⟩ : syracuseStep 3284873 = 2463655) B2463655
theorem B1843231 : Blo 428775 1843231 := bstep (se 1 (by rfl) ⟨1382423, by rfl⟩ : syracuseStep 1843231 = 2764847) B2764847
theorem B3285359 : Blo 428775 3285359 := bstep (se 1 (by rfl) ⟨2464019, by rfl⟩ : syracuseStep 3285359 = 4928039) B4928039
theorem B1221257 : Blo 428775 1221257 := bstep (se 2 (by rfl) ⟨457971, by rfl⟩ : syracuseStep 1221257 = 915943) B915943
theorem B1450655 : Blo 428775 1450655 := bstep (se 1 (by rfl) ⟨1087991, by rfl⟩ : syracuseStep 1450655 = 2175983) B2175983
theorem B1090331 : Blo 428775 1090331 := bstep (se 1 (by rfl) ⟨817748, by rfl⟩ : syracuseStep 1090331 = 1635497) B1635497
theorem B7972505 : Blo 428775 7972505 := bstep (se 2 (by rfl) ⟨2989689, by rfl⟩ : syracuseStep 7972505 = 5979379) B5979379
theorem B37695131 : Blo 428775 37695131 := bstep (se 1 (by rfl) ⟨28271348, by rfl⟩ : syracuseStep 37695131 = 56542697) B56542697
theorem B1453895 : Blo 428775 1453895 := bstep (se 1 (by rfl) ⟨1090421, by rfl⟩ : syracuseStep 1453895 = 2180843) B2180843
theorem B1847947 : Blo 428775 1847947 := bstep (se 1 (by rfl) ⟨1385960, by rfl⟩ : syracuseStep 1847947 = 2771921) B2771921
theorem B1455407 : Blo 428775 1455407 := bstep (se 1 (by rfl) ⟨1091555, by rfl⟩ : syracuseStep 1455407 = 2183111) B2183111
theorem B3684959 : Blo 428775 3684959 := bstep (se 1 (by rfl) ⟨2763719, by rfl⟩ : syracuseStep 3684959 = 5527439) B5527439
theorem B5913323 : Blo 428775 5913323 := bstep (se 1 (by rfl) ⟨4434992, by rfl⟩ : syracuseStep 5913323 = 8869985) B8869985
theorem B46742759 : Blo 428775 46742759 := bstep (se 1 (by rfl) ⟨35057069, by rfl⟩ : syracuseStep 46742759 = 70114139) B70114139
theorem B736511 : Blo 428775 736511 := bstep (se 1 (by rfl) ⟨552383, by rfl⟩ : syracuseStep 736511 = 1104767) B1104767
theorem B1458323 : Blo 428775 1458323 := bstep (se 1 (by rfl) ⟨1093742, by rfl⟩ : syracuseStep 1458323 = 2187485) B2187485
theorem B2179385 : Blo 428775 2179385 := bstep (se 2 (by rfl) ⟨817269, by rfl⟩ : syracuseStep 2179385 = 1634539) B1634539
theorem B26427707 : Blo 428775 26427707 := bstep (se 1 (by rfl) ⟨19820780, by rfl⟩ : syracuseStep 26427707 = 39641561) B39641561
theorem B967463 : Blo 428775 967463 := bstep (se 1 (by rfl) ⟨725597, by rfl⟩ : syracuseStep 967463 = 1451195) B1451195
theorem B1557407 : Blo 428775 1557407 := bstep (se 1 (by rfl) ⟨1168055, by rfl⟩ : syracuseStep 1557407 = 2336111) B2336111
theorem B1459133 : Blo 428775 1459133 := bstep (se 3 (by rfl) ⟨273587, by rfl⟩ : syracuseStep 1459133 = 547175) B547175
theorem B969371 : Blo 428775 969371 := bstep (se 1 (by rfl) ⟨727028, by rfl⟩ : syracuseStep 969371 = 1454057) B1454057
theorem B773231 : Blo 428775 773231 := bstep (se 1 (by rfl) ⟨579923, by rfl⟩ : syracuseStep 773231 = 1159847) B1159847
theorem B5917817 : Blo 428775 5917817 := bstep (se 2 (by rfl) ⟨2219181, by rfl⟩ : syracuseStep 5917817 = 4438363) B4438363
theorem B2444519 : Blo 428775 2444519 := bstep (se 1 (by rfl) ⟨1833389, by rfl⟩ : syracuseStep 2444519 = 3666779) B3666779
theorem B4968499 : Blo 428775 4968499 := bstep (se 1 (by rfl) ⟨3726374, by rfl⟩ : syracuseStep 4968499 = 7452749) B7452749
theorem B644075 : Blo 428775 644075 := bstep (se 1 (by rfl) ⟨483056, by rfl⟩ : syracuseStep 644075 = 966113) B966113
theorem B644123 : Blo 428775 644123 := bstep (se 1 (by rfl) ⟨483092, by rfl⟩ : syracuseStep 644123 = 966185) B966185
theorem B972431 : Blo 428775 972431 := bstep (se 1 (by rfl) ⟨729323, by rfl⟩ : syracuseStep 972431 = 1458647) B1458647
theorem B645167 : Blo 428775 645167 := bstep (se 1 (by rfl) ⟨483875, by rfl⟩ : syracuseStep 645167 = 967751) B967751
theorem B645545 : Blo 428775 645545 := bstep (se 2 (by rfl) ⟨242079, by rfl⟩ : syracuseStep 645545 = 484159) B484159
theorem B645599 : Blo 428775 645599 := bstep (se 1 (by rfl) ⟨484199, by rfl⟩ : syracuseStep 645599 = 968399) B968399
theorem B645851 : Blo 428775 645851 := bstep (se 1 (by rfl) ⟨484388, by rfl⟩ : syracuseStep 645851 = 968777) B968777
theorem B973547 : Blo 428775 973547 := bstep (se 1 (by rfl) ⟨730160, by rfl⟩ : syracuseStep 973547 = 1460321) B1460321
theorem B645887 : Blo 428775 645887 := bstep (se 1 (by rfl) ⟨484415, by rfl⟩ : syracuseStep 645887 = 968831) B968831
theorem B3103535 : Blo 428775 3103535 := bstep (se 1 (by rfl) ⟨2327651, by rfl⟩ : syracuseStep 3103535 = 4655303) B4655303
theorem B646271 : Blo 428775 646271 := bstep (se 1 (by rfl) ⟨484703, by rfl⟩ : syracuseStep 646271 = 969407) B969407
theorem B647579 : Blo 428775 647579 := bstep (se 1 (by rfl) ⟨485684, by rfl⟩ : syracuseStep 647579 = 971369) B971369
theorem B647975 : Blo 428775 647975 := bstep (se 1 (by rfl) ⟨485981, by rfl⟩ : syracuseStep 647975 = 971963) B971963
theorem B484447 : Blo 428775 484447 := bstep (se 1 (by rfl) ⟨363335, by rfl⟩ : syracuseStep 484447 = 726671) B726671
theorem B648329 : Blo 428775 648329 := bstep (se 2 (by rfl) ⟨243123, by rfl⟩ : syracuseStep 648329 = 486247) B486247
theorem B648443 : Blo 428775 648443 := bstep (se 1 (by rfl) ⟨486332, by rfl⟩ : syracuseStep 648443 = 972665) B972665
theorem B2321057 : Blo 428775 2321057 := bstep (se 2 (by rfl) ⟨870396, by rfl⟩ : syracuseStep 2321057 = 1740793) B1740793
theorem B7335197 : Blo 428775 7335197 := bstep (se 3 (by rfl) ⟨1375349, by rfl⟩ : syracuseStep 7335197 = 2750699) B2750699
theorem B24800579 : Blo 428775 24800579 := bstep (se 1 (by rfl) ⟨18600434, by rfl⟩ : syracuseStep 24800579 = 37200869) B37200869
theorem B1863119 : Blo 428775 1863119 := bstep (se 1 (by rfl) ⟨1397339, by rfl⟩ : syracuseStep 1863119 = 2794679) B2794679
theorem B1470287 : Blo 428775 1470287 := bstep (se 1 (by rfl) ⟨1102715, by rfl⟩ : syracuseStep 1470287 = 2205431) B2205431
theorem B815015 : Blo 428775 815015 := bstep (se 1 (by rfl) ⟨611261, by rfl⟩ : syracuseStep 815015 = 1222523) B1222523
theorem B4124591 : Blo 428775 4124591 := bstep (se 1 (by rfl) ⟨3093443, by rfl⟩ : syracuseStep 4124591 = 6186887) B6186887
theorem B2749241 : Blo 428775 2749241 := bstep (se 2 (by rfl) ⟨1030965, by rfl⟩ : syracuseStep 2749241 = 2061931) B2061931
theorem B816617 : Blo 428775 816617 := bstep (se 2 (by rfl) ⟨306231, by rfl⟩ : syracuseStep 816617 = 612463) B612463
theorem B11009357 : Blo 428775 11009357 := bstep (se 3 (by rfl) ⟨2064254, by rfl⟩ : syracuseStep 11009357 = 4128509) B4128509
theorem B2457641 : Blo 428775 2457641 := bstep (se 2 (by rfl) ⟨921615, by rfl⟩ : syracuseStep 2457641 = 1843231) B1843231
theorem B9275309 : Blo 428775 9275309 := bstep (se 3 (by rfl) ⟨1739120, by rfl⟩ : syracuseStep 9275309 = 3478241) B3478241
theorem B19925347 : Blo 428775 19925347 := bstep (se 1 (by rfl) ⟨14944010, by rfl⟩ : syracuseStep 19925347 = 29888021) B29888021
theorem B1641647 : Blo 428775 1641647 := bstep (se 1 (by rfl) ⟨1231235, by rfl⟩ : syracuseStep 1641647 = 2462471) B2462471
theorem B429383 : Blo 428775 429383 := bstep (se 1 (by rfl) ⟨322037, by rfl⟩ : syracuseStep 429383 = 644075) B644075
theorem B429415 : Blo 428775 429415 := bstep (se 1 (by rfl) ⟨322061, by rfl⟩ : syracuseStep 429415 = 644123) B644123
theorem B430111 : Blo 428775 430111 := bstep (se 1 (by rfl) ⟨322583, by rfl⟩ : syracuseStep 430111 = 645167) B645167
theorem B430363 : Blo 428775 430363 := bstep (se 1 (by rfl) ⟨322772, by rfl⟩ : syracuseStep 430363 = 645545) B645545
theorem B430399 : Blo 428775 430399 := bstep (se 1 (by rfl) ⟨322799, by rfl⟩ : syracuseStep 430399 = 645599) B645599
theorem B430567 : Blo 428775 430567 := bstep (se 1 (by rfl) ⟨322925, by rfl⟩ : syracuseStep 430567 = 645851) B645851
theorem B430591 : Blo 428775 430591 := bstep (se 1 (by rfl) ⟨322943, by rfl⟩ : syracuseStep 430591 = 645887) B645887
theorem B2069023 : Blo 428775 2069023 := bstep (se 1 (by rfl) ⟨1551767, by rfl⟩ : syracuseStep 2069023 = 3103535) B3103535
theorem B430847 : Blo 428775 430847 := bstep (se 1 (by rfl) ⟨323135, by rfl⟩ : syracuseStep 430847 = 646271) B646271
theorem B922727 : Blo 428775 922727 := bstep (se 1 (by rfl) ⟨692045, by rfl⟩ : syracuseStep 922727 = 1384091) B1384091
theorem B6624665 : Blo 428775 6624665 := bstep (se 2 (by rfl) ⟨2484249, by rfl⟩ : syracuseStep 6624665 = 4968499) B4968499
theorem B431719 : Blo 428775 431719 := bstep (se 1 (by rfl) ⟨323789, by rfl⟩ : syracuseStep 431719 = 647579) B647579
theorem B726887 : Blo 428775 726887 := bstep (se 1 (by rfl) ⟨545165, by rfl⟩ : syracuseStep 726887 = 1090331) B1090331
theorem B431983 : Blo 428775 431983 := bstep (se 1 (by rfl) ⟨323987, by rfl⟩ : syracuseStep 431983 = 647975) B647975
theorem B432219 : Blo 428775 432219 := bstep (se 1 (by rfl) ⟨324164, by rfl⟩ : syracuseStep 432219 = 648329) B648329
theorem B432295 : Blo 428775 432295 := bstep (se 1 (by rfl) ⟨324221, by rfl⟩ : syracuseStep 432295 = 648443) B648443
theorem B2463929 : Blo 428775 2463929 := bstep (se 2 (by rfl) ⟨923973, by rfl⟩ : syracuseStep 2463929 = 1847947) B1847947
theorem B5315003 : Blo 428775 5315003 := bstep (se 1 (by rfl) ⟨3986252, by rfl⟩ : syracuseStep 5315003 = 7972505) B7972505
theorem B1842173 : Blo 428775 1842173 := bstep (se 3 (by rfl) ⟨345407, by rfl⟩ : syracuseStep 1842173 = 690815) B690815
theorem B1547371 : Blo 428775 1547371 := bstep (se 1 (by rfl) ⟨1160528, by rfl⟩ : syracuseStep 1547371 = 2321057) B2321057
theorem B4890131 : Blo 428775 4890131 := bstep (se 1 (by rfl) ⟨3667598, by rfl⟩ : syracuseStep 4890131 = 7335197) B7335197
theorem B3547265 : Blo 428775 3547265 := bstep (se 2 (by rfl) ⟨1330224, by rfl⟩ : syracuseStep 3547265 = 2660449) B2660449
theorem B1450169 : Blo 428775 1450169 := bstep (se 2 (by rfl) ⟨543813, by rfl⟩ : syracuseStep 1450169 = 1087627) B1087627
theorem B3942215 : Blo 428775 3942215 := bstep (se 1 (by rfl) ⟨2956661, by rfl⟩ : syracuseStep 3942215 = 5913323) B5913323
theorem B1451897 : Blo 428775 1451897 := bstep (se 2 (by rfl) ⟨544461, by rfl⟩ : syracuseStep 1451897 = 1088923) B1088923
theorem B5646793 : Blo 428775 5646793 := bstep (se 2 (by rfl) ⟨2117547, by rfl⟩ : syracuseStep 5646793 = 4235095) B4235095
theorem B6957521 : Blo 428775 6957521 := bstep (se 2 (by rfl) ⟨2609070, by rfl⟩ : syracuseStep 6957521 = 5218141) B5218141
theorem B8301305 : Blo 428775 8301305 := bstep (se 2 (by rfl) ⟨3112989, by rfl⟩ : syracuseStep 8301305 = 6225979) B6225979
theorem B1452923 : Blo 428775 1452923 := bstep (se 1 (by rfl) ⟨1089692, by rfl⟩ : syracuseStep 1452923 = 2179385) B2179385
theorem B437351 : Blo 428775 437351 := bstep (se 1 (by rfl) ⟨328013, by rfl⟩ : syracuseStep 437351 = 656027) B656027
theorem B6991771 : Blo 428775 6991771 := bstep (se 1 (by rfl) ⟨5243828, by rfl⟩ : syracuseStep 6991771 = 10487657) B10487657
theorem B1552343 : Blo 428775 1552343 := bstep (se 1 (by rfl) ⟨1164257, by rfl⟩ : syracuseStep 1552343 = 2328515) B2328515
theorem B4960367 : Blo 428775 4960367 := bstep (se 1 (by rfl) ⟨3720275, by rfl⟩ : syracuseStep 4960367 = 7440551) B7440551
theorem B3256685 : Blo 428775 3256685 := bstep (se 3 (by rfl) ⟨610628, by rfl⟩ : syracuseStep 3256685 = 1221257) B1221257
theorem B1553903 : Blo 428775 1553903 := bstep (se 1 (by rfl) ⟨1165427, by rfl⟩ : syracuseStep 1553903 = 2330855) B2330855
theorem B965033 : Blo 428775 965033 := bstep (se 2 (by rfl) ⟨361887, by rfl⟩ : syracuseStep 965033 = 723775) B723775
theorem B3259115 : Blo 428775 3259115 := bstep (se 1 (by rfl) ⟨2444336, by rfl⟩ : syracuseStep 3259115 = 4888673) B4888673
theorem B965375 : Blo 428775 965375 := bstep (se 1 (by rfl) ⟨724031, by rfl⟩ : syracuseStep 965375 = 1448063) B1448063
theorem B965843 : Blo 428775 965843 := bstep (se 1 (by rfl) ⟨724382, by rfl⟩ : syracuseStep 965843 = 1448765) B1448765
theorem B1883903 : Blo 428775 1883903 := bstep (se 1 (by rfl) ⟨1412927, by rfl⟩ : syracuseStep 1883903 = 2825855) B2825855
theorem B966419 : Blo 428775 966419 := bstep (se 1 (by rfl) ⟨724814, by rfl⟩ : syracuseStep 966419 = 1449629) B1449629
theorem B967103 : Blo 428775 967103 := bstep (se 1 (by rfl) ⟨725327, by rfl⟩ : syracuseStep 967103 = 1450655) B1450655
theorem B968057 : Blo 428775 968057 := bstep (se 2 (by rfl) ⟨363021, by rfl⟩ : syracuseStep 968057 = 726043) B726043
theorem B16533719 : Blo 428775 16533719 := bstep (se 1 (by rfl) ⟨12400289, by rfl⟩ : syracuseStep 16533719 = 24800579) B24800579
theorem B969263 : Blo 428775 969263 := bstep (se 1 (by rfl) ⟨726947, by rfl⟩ : syracuseStep 969263 = 1453895) B1453895
theorem B543343 : Blo 428775 543343 := bstep (se 1 (by rfl) ⟨407507, by rfl⟩ : syracuseStep 543343 = 815015) B815015
theorem B22465457 : Blo 428775 22465457 := bstep (se 2 (by rfl) ⟨8424546, by rfl⟩ : syracuseStep 22465457 = 16849093) B16849093
theorem B15780845 : Blo 428775 15780845 := bstep (se 3 (by rfl) ⟨2958908, by rfl⟩ : syracuseStep 15780845 = 5917817) B5917817
theorem B970217 : Blo 428775 970217 := bstep (se 2 (by rfl) ⟨363831, by rfl⟩ : syracuseStep 970217 = 727663) B727663
theorem B970271 : Blo 428775 970271 := bstep (se 1 (by rfl) ⟨727703, by rfl⟩ : syracuseStep 970271 = 1455407) B1455407
theorem B544411 : Blo 428775 544411 := bstep (se 1 (by rfl) ⟨408308, by rfl⟩ : syracuseStep 544411 = 816617) B816617
theorem B4968317 : Blo 428775 4968317 := bstep (se 3 (by rfl) ⟨931559, by rfl⟩ : syracuseStep 4968317 = 1863119) B1863119
theorem B972215 : Blo 428775 972215 := bstep (se 1 (by rfl) ⟨729161, by rfl⟩ : syracuseStep 972215 = 1458323) B1458323
theorem B17618471 : Blo 428775 17618471 := bstep (se 1 (by rfl) ⟨13213853, by rfl⟩ : syracuseStep 17618471 = 26427707) B26427707
theorem B644975 : Blo 428775 644975 := bstep (se 1 (by rfl) ⟨483731, by rfl⟩ : syracuseStep 644975 = 967463) B967463
theorem B1038271 : Blo 428775 1038271 := bstep (se 1 (by rfl) ⟨778703, by rfl⟩ : syracuseStep 1038271 = 1557407) B1557407
theorem B972755 : Blo 428775 972755 := bstep (se 1 (by rfl) ⟨729566, by rfl⟩ : syracuseStep 972755 = 1459133) B1459133
theorem B3693023 : Blo 428775 3693023 := bstep (se 1 (by rfl) ⟨2769767, by rfl⟩ : syracuseStep 3693023 = 5539535) B5539535
theorem B645929 : Blo 428775 645929 := bstep (se 2 (by rfl) ⟨242223, by rfl⟩ : syracuseStep 645929 = 484447) B484447
theorem B646247 : Blo 428775 646247 := bstep (se 1 (by rfl) ⟨484685, by rfl⟩ : syracuseStep 646247 = 969371) B969371
theorem B482431 : Blo 428775 482431 := bstep (se 1 (by rfl) ⟨361823, by rfl⟩ : syracuseStep 482431 = 723647) B723647
theorem B1629679 : Blo 428775 1629679 := bstep (se 1 (by rfl) ⟨1222259, by rfl⟩ : syracuseStep 1629679 = 2444519) B2444519
theorem B482863 : Blo 428775 482863 := bstep (se 1 (by rfl) ⟨362147, by rfl⟩ : syracuseStep 482863 = 724295) B724295
theorem B483439 : Blo 428775 483439 := bstep (se 1 (by rfl) ⟨362579, by rfl⟩ : syracuseStep 483439 = 725159) B725159
theorem B648287 : Blo 428775 648287 := bstep (se 1 (by rfl) ⟨486215, by rfl⟩ : syracuseStep 648287 = 972431) B972431
theorem B649031 : Blo 428775 649031 := bstep (se 1 (by rfl) ⟨486773, by rfl⟩ : syracuseStep 649031 = 973547) B973547
theorem B2189915 : Blo 428775 2189915 := bstep (se 1 (by rfl) ⟨1642436, by rfl⟩ : syracuseStep 2189915 = 3284873) B3284873
theorem B2190239 : Blo 428775 2190239 := bstep (se 1 (by rfl) ⟨1642679, by rfl⟩ : syracuseStep 2190239 = 3285359) B3285359
theorem B25130087 : Blo 428775 25130087 := bstep (se 1 (by rfl) ⟨18847565, by rfl⟩ : syracuseStep 25130087 = 37695131) B37695131
theorem B980191 : Blo 428775 980191 := bstep (se 1 (by rfl) ⟨735143, by rfl⟩ : syracuseStep 980191 = 1470287) B1470287
theorem B2749727 : Blo 428775 2749727 := bstep (se 1 (by rfl) ⟨2062295, by rfl⟩ : syracuseStep 2749727 = 4124591) B4124591
theorem B2061949 : Blo 428775 2061949 := bstep (se 3 (by rfl) ⟨386615, by rfl⟩ : syracuseStep 2061949 = 773231) B773231
theorem B1832827 : Blo 428775 1832827 := bstep (se 1 (by rfl) ⟨1374620, by rfl⟩ : syracuseStep 1832827 = 2749241) B2749241
theorem B1964029 : Blo 428775 1964029 := bstep (se 3 (by rfl) ⟨368255, by rfl⟩ : syracuseStep 1964029 = 736511) B736511
theorem B2456639 : Blo 428775 2456639 := bstep (se 1 (by rfl) ⟨1842479, by rfl⟩ : syracuseStep 2456639 = 3684959) B3684959
theorem B31161839 : Blo 428775 31161839 := bstep (se 1 (by rfl) ⟨23371379, by rfl⟩ : syracuseStep 31161839 = 46742759) B46742759
theorem B7339571 : Blo 428775 7339571 := bstep (se 1 (by rfl) ⟨5504678, by rfl⟩ : syracuseStep 7339571 = 11009357) B11009357
theorem B1638427 : Blo 428775 1638427 := bstep (se 1 (by rfl) ⟨1228820, by rfl⟩ : syracuseStep 1638427 = 2457641) B2457641
theorem B14976971 : Blo 428775 14976971 := bstep (se 1 (by rfl) ⟨11232728, by rfl⟩ : syracuseStep 14976971 = 22465457) B22465457
theorem B10520563 : Blo 428775 10520563 := bstep (se 1 (by rfl) ⟨7890422, by rfl⟩ : syracuseStep 10520563 = 15780845) B15780845
theorem B724457 : Blo 428775 724457 := bstep (se 2 (by rfl) ⟨271671, by rfl⟩ : syracuseStep 724457 = 543343) B543343
theorem B429983 : Blo 428775 429983 := bstep (se 1 (by rfl) ⟨322487, by rfl⟩ : syracuseStep 429983 = 644975) B644975
theorem B1642619 : Blo 428775 1642619 := bstep (se 1 (by rfl) ⟨1231964, by rfl⟩ : syracuseStep 1642619 = 2463929) B2463929
theorem B3543335 : Blo 428775 3543335 := bstep (se 1 (by rfl) ⟨2657501, by rfl⟩ : syracuseStep 3543335 = 5315003) B5315003
theorem B2462015 : Blo 428775 2462015 := bstep (se 1 (by rfl) ⟨1846511, by rfl⟩ : syracuseStep 2462015 = 3693023) B3693023
theorem B430619 : Blo 428775 430619 := bstep (se 1 (by rfl) ⟨322964, by rfl⟩ : syracuseStep 430619 = 645929) B645929
theorem B430831 : Blo 428775 430831 := bstep (se 1 (by rfl) ⟨323123, by rfl⟩ : syracuseStep 430831 = 646247) B646247
theorem B725881 : Blo 428775 725881 := bstep (se 2 (by rfl) ⟨272205, by rfl⟩ : syracuseStep 725881 = 544411) B544411
theorem B2758697 : Blo 428775 2758697 := bstep (se 2 (by rfl) ⟨1034511, by rfl⟩ : syracuseStep 2758697 = 2069023) B2069023
theorem B432191 : Blo 428775 432191 := bstep (se 1 (by rfl) ⟨324143, by rfl⟩ : syracuseStep 432191 = 648287) B648287
theorem B2628143 : Blo 428775 2628143 := bstep (se 1 (by rfl) ⟨1971107, by rfl⟩ : syracuseStep 2628143 = 3942215) B3942215
theorem B432687 : Blo 428775 432687 := bstep (se 1 (by rfl) ⟨324515, by rfl⟩ : syracuseStep 432687 = 649031) B649031
theorem B1384361 : Blo 428775 1384361 := bstep (se 2 (by rfl) ⟨519135, by rfl⟩ : syracuseStep 1384361 = 1038271) B1038271
theorem B2171123 : Blo 428775 2171123 := bstep (se 1 (by rfl) ⟨1628342, by rfl⟩ : syracuseStep 2171123 = 3256685) B3256685
theorem B16753391 : Blo 428775 16753391 := bstep (se 1 (by rfl) ⟨12565043, by rfl⟩ : syracuseStep 16753391 = 25130087) B25130087
theorem B2172743 : Blo 428775 2172743 := bstep (se 1 (by rfl) ⟨1629557, by rfl⟩ : syracuseStep 2172743 = 3259115) B3259115
theorem B2172905 : Blo 428775 2172905 := bstep (se 2 (by rfl) ⟨814839, by rfl⟩ : syracuseStep 2172905 = 1629679) B1629679
theorem B5023741 : Blo 428775 5023741 := bstep (se 3 (by rfl) ⟨941951, by rfl⟩ : syracuseStep 5023741 = 1883903) B1883903
theorem B13248845 : Blo 428775 13248845 := bstep (se 3 (by rfl) ⟨2484158, by rfl⟩ : syracuseStep 13248845 = 4968317) B4968317
theorem B4893047 : Blo 428775 4893047 := bstep (se 1 (by rfl) ⟨3669785, by rfl⟩ : syracuseStep 4893047 = 7339571) B7339571
theorem B4139581 : Blo 428775 4139581 := bstep (se 3 (by rfl) ⟨776171, by rfl⟩ : syracuseStep 4139581 = 1552343) B1552343
theorem B4665077 : Blo 428775 4665077 := bstep (se 5 (by rfl) ⟨218675, by rfl⟩ : syracuseStep 4665077 = 437351) B437351
theorem B11022479 : Blo 428775 11022479 := bstep (se 1 (by rfl) ⟨8266859, by rfl⟩ : syracuseStep 11022479 = 16533719) B16533719
theorem B1094431 : Blo 428775 1094431 := bstep (se 1 (by rfl) ⟨820823, by rfl⟩ : syracuseStep 1094431 = 1641647) B1641647
theorem B11745647 : Blo 428775 11745647 := bstep (se 1 (by rfl) ⟨8809235, by rfl⟩ : syracuseStep 11745647 = 17618471) B17618471
theorem B1228115 : Blo 428775 1228115 := bstep (se 1 (by rfl) ⟨921086, by rfl⟩ : syracuseStep 1228115 = 1842173) B1842173
theorem B3260087 : Blo 428775 3260087 := bstep (se 1 (by rfl) ⟨2445065, by rfl⟩ : syracuseStep 3260087 = 4890131) B4890131
theorem B9322361 : Blo 428775 9322361 := bstep (se 2 (by rfl) ⟨3495885, by rfl⟩ : syracuseStep 9322361 = 6991771) B6991771
theorem B966779 : Blo 428775 966779 := bstep (se 1 (by rfl) ⟨725084, by rfl⟩ : syracuseStep 966779 = 1450169) B1450169
theorem B967931 : Blo 428775 967931 := bstep (se 1 (by rfl) ⟨725948, by rfl⟩ : syracuseStep 967931 = 1451897) B1451897
theorem B4638347 : Blo 428775 4638347 := bstep (se 1 (by rfl) ⟨3478760, by rfl⟩ : syracuseStep 4638347 = 6957521) B6957521
theorem B1459943 : Blo 428775 1459943 := bstep (se 1 (by rfl) ⟨1094957, by rfl⟩ : syracuseStep 1459943 = 2189915) B2189915
theorem B968615 : Blo 428775 968615 := bstep (se 1 (by rfl) ⟨726461, by rfl⟩ : syracuseStep 968615 = 1452923) B1452923
theorem B1460159 : Blo 428775 1460159 := bstep (se 1 (by rfl) ⟨1095119, by rfl⟩ : syracuseStep 1460159 = 2190239) B2190239
theorem B2443769 : Blo 428775 2443769 := bstep (se 2 (by rfl) ⟨916413, by rfl⟩ : syracuseStep 2443769 = 1832827) B1832827
theorem B1035935 : Blo 428775 1035935 := bstep (se 1 (by rfl) ⟨776951, by rfl⟩ : syracuseStep 1035935 = 1553903) B1553903
theorem B643241 : Blo 428775 643241 := bstep (se 2 (by rfl) ⟨241215, by rfl⟩ : syracuseStep 643241 = 482431) B482431
theorem B643355 : Blo 428775 643355 := bstep (se 1 (by rfl) ⟨482516, by rfl⟩ : syracuseStep 643355 = 965033) B965033
theorem B643583 : Blo 428775 643583 := bstep (se 1 (by rfl) ⟨482687, by rfl⟩ : syracuseStep 643583 = 965375) B965375
theorem B643817 : Blo 428775 643817 := bstep (se 2 (by rfl) ⟨241431, by rfl⟩ : syracuseStep 643817 = 482863) B482863
theorem B643895 : Blo 428775 643895 := bstep (se 1 (by rfl) ⟨482921, by rfl⟩ : syracuseStep 643895 = 965843) B965843
theorem B644279 : Blo 428775 644279 := bstep (se 1 (by rfl) ⟨483209, by rfl⟩ : syracuseStep 644279 = 966419) B966419
theorem B644585 : Blo 428775 644585 := bstep (se 2 (by rfl) ⟨241719, by rfl⟩ : syracuseStep 644585 = 483439) B483439
theorem B644735 : Blo 428775 644735 := bstep (se 1 (by rfl) ⟨483551, by rfl⟩ : syracuseStep 644735 = 967103) B967103
theorem B645371 : Blo 428775 645371 := bstep (se 1 (by rfl) ⟨484028, by rfl⟩ : syracuseStep 645371 = 968057) B968057
theorem B6183539 : Blo 428775 6183539 := bstep (se 1 (by rfl) ⟨4637654, by rfl⟩ : syracuseStep 6183539 = 9275309) B9275309
theorem B37837493 : Blo 428775 37837493 := bstep (se 5 (by rfl) ⟨1773632, by rfl⟩ : syracuseStep 37837493 = 3547265) B3547265
theorem B646175 : Blo 428775 646175 := bstep (se 1 (by rfl) ⟨484631, by rfl⟩ : syracuseStep 646175 = 969263) B969263
theorem B646811 : Blo 428775 646811 := bstep (se 1 (by rfl) ⟨485108, by rfl⟩ : syracuseStep 646811 = 970217) B970217
theorem B646847 : Blo 428775 646847 := bstep (se 1 (by rfl) ⟨485135, by rfl⟩ : syracuseStep 646847 = 970271) B970271
theorem B26567129 : Blo 428775 26567129 := bstep (se 2 (by rfl) ⟨9962673, by rfl⟩ : syracuseStep 26567129 = 19925347) B19925347
theorem B7529057 : Blo 428775 7529057 := bstep (se 2 (by rfl) ⟨2823396, by rfl⟩ : syracuseStep 7529057 = 5646793) B5646793
theorem B615151 : Blo 428775 615151 := bstep (se 1 (by rfl) ⟨461363, by rfl⟩ : syracuseStep 615151 = 922727) B922727
theorem B4416443 : Blo 428775 4416443 := bstep (se 1 (by rfl) ⟨3312332, by rfl⟩ : syracuseStep 4416443 = 6624665) B6624665
theorem B648143 : Blo 428775 648143 := bstep (se 1 (by rfl) ⟨486107, by rfl⟩ : syracuseStep 648143 = 972215) B972215
theorem B484591 : Blo 428775 484591 := bstep (se 1 (by rfl) ⟨363443, by rfl⟩ : syracuseStep 484591 = 726887) B726887
theorem B648503 : Blo 428775 648503 := bstep (se 1 (by rfl) ⟨486377, by rfl⟩ : syracuseStep 648503 = 972755) B972755
theorem B1306921 : Blo 428775 1306921 := bstep (se 2 (by rfl) ⟨490095, by rfl⟩ : syracuseStep 1306921 = 980191) B980191
theorem B5534203 : Blo 428775 5534203 := bstep (se 1 (by rfl) ⟨4150652, by rfl⟩ : syracuseStep 5534203 = 8301305) B8301305
theorem B2749265 : Blo 428775 2749265 := bstep (se 2 (by rfl) ⟨1030974, by rfl⟩ : syracuseStep 2749265 = 2061949) B2061949
theorem B2618705 : Blo 428775 2618705 := bstep (se 2 (by rfl) ⟨982014, by rfl⟩ : syracuseStep 2618705 = 1964029) B1964029
theorem B3306911 : Blo 428775 3306911 := bstep (se 1 (by rfl) ⟨2480183, by rfl⟩ : syracuseStep 3306911 = 4960367) B4960367
theorem B1833151 : Blo 428775 1833151 := bstep (se 1 (by rfl) ⟨1374863, by rfl⟩ : syracuseStep 1833151 = 2749727) B2749727
theorem B83098237 : Blo 428775 83098237 := bstep (se 3 (by rfl) ⟨15580919, by rfl⟩ : syracuseStep 83098237 = 31161839) B31161839
theorem B2063161 : Blo 428775 2063161 := bstep (se 2 (by rfl) ⟨773685, by rfl⟩ : syracuseStep 2063161 = 1547371) B1547371
theorem B1637759 : Blo 428775 1637759 := bstep (se 1 (by rfl) ⟨1228319, by rfl⟩ : syracuseStep 1637759 = 2456639) B2456639
theorem B820201 : Blo 428775 820201 := bstep (se 2 (by rfl) ⟨307575, by rfl⟩ : syracuseStep 820201 = 615151) B615151
theorem B690623 : Blo 428775 690623 := bstep (se 1 (by rfl) ⟨517967, by rfl⟩ : syracuseStep 690623 = 1035935) B1035935
theorem B14027417 : Blo 428775 14027417 := bstep (se 2 (by rfl) ⟨5260281, by rfl⟩ : syracuseStep 14027417 = 10520563) B10520563
theorem B428827 : Blo 428775 428827 := bstep (se 1 (by rfl) ⟨321620, by rfl⟩ : syracuseStep 428827 = 643241) B643241
theorem B428903 : Blo 428775 428903 := bstep (se 1 (by rfl) ⟨321677, by rfl⟩ : syracuseStep 428903 = 643355) B643355
theorem B2362223 : Blo 428775 2362223 := bstep (se 1 (by rfl) ⟨1771667, by rfl⟩ : syracuseStep 2362223 = 3543335) B3543335
theorem B1641343 : Blo 428775 1641343 := bstep (se 1 (by rfl) ⟨1231007, by rfl⟩ : syracuseStep 1641343 = 2462015) B2462015
theorem B429055 : Blo 428775 429055 := bstep (se 1 (by rfl) ⟨321791, by rfl⟩ : syracuseStep 429055 = 643583) B643583
theorem B429211 : Blo 428775 429211 := bstep (se 1 (by rfl) ⟨321908, by rfl⟩ : syracuseStep 429211 = 643817) B643817
theorem B429263 : Blo 428775 429263 := bstep (se 1 (by rfl) ⟨321947, by rfl⟩ : syracuseStep 429263 = 643895) B643895
theorem B429519 : Blo 428775 429519 := bstep (se 1 (by rfl) ⟨322139, by rfl⟩ : syracuseStep 429519 = 644279) B644279
theorem B429723 : Blo 428775 429723 := bstep (se 1 (by rfl) ⟨322292, by rfl⟩ : syracuseStep 429723 = 644585) B644585
theorem B8818429 : Blo 428775 8818429 := bstep (se 3 (by rfl) ⟨1653455, by rfl⟩ : syracuseStep 8818429 = 3306911) B3306911
theorem B429823 : Blo 428775 429823 := bstep (se 1 (by rfl) ⟨322367, by rfl⟩ : syracuseStep 429823 = 644735) B644735
theorem B1839131 : Blo 428775 1839131 := bstep (se 1 (by rfl) ⟨1379348, by rfl⟩ : syracuseStep 1839131 = 2758697) B2758697
theorem B430247 : Blo 428775 430247 := bstep (se 1 (by rfl) ⟨322685, by rfl⟩ : syracuseStep 430247 = 645371) B645371
theorem B430783 : Blo 428775 430783 := bstep (se 1 (by rfl) ⟨323087, by rfl⟩ : syracuseStep 430783 = 646175) B646175
theorem B431207 : Blo 428775 431207 := bstep (se 1 (by rfl) ⟨323405, by rfl⟩ : syracuseStep 431207 = 646811) B646811
theorem B431231 : Blo 428775 431231 := bstep (se 1 (by rfl) ⟨323423, by rfl⟩ : syracuseStep 431231 = 646847) B646847
theorem B922907 : Blo 428775 922907 := bstep (se 1 (by rfl) ⟨692180, by rfl⟩ : syracuseStep 922907 = 1384361) B1384361
theorem B1447415 : Blo 428775 1447415 := bstep (se 1 (by rfl) ⟨1085561, by rfl⟩ : syracuseStep 1447415 = 2171123) B2171123
theorem B1742561 : Blo 428775 1742561 := bstep (se 2 (by rfl) ⟨653460, by rfl⟩ : syracuseStep 1742561 = 1306921) B1306921
theorem B5019371 : Blo 428775 5019371 := bstep (se 1 (by rfl) ⟨3764528, by rfl⟩ : syracuseStep 5019371 = 7529057) B7529057
theorem B432095 : Blo 428775 432095 := bstep (se 1 (by rfl) ⟨324071, by rfl⟩ : syracuseStep 432095 = 648143) B648143
theorem B7378937 : Blo 428775 7378937 := bstep (se 2 (by rfl) ⟨2767101, by rfl⟩ : syracuseStep 7378937 = 5534203) B5534203
theorem B432335 : Blo 428775 432335 := bstep (se 1 (by rfl) ⟨324251, by rfl⟩ : syracuseStep 432335 = 648503) B648503
theorem B1448495 : Blo 428775 1448495 := bstep (se 1 (by rfl) ⟨1086371, by rfl⟩ : syracuseStep 1448495 = 2172743) B2172743
theorem B1448603 : Blo 428775 1448603 := bstep (se 1 (by rfl) ⟨1086452, by rfl⟩ : syracuseStep 1448603 = 2172905) B2172905
theorem B7348319 : Blo 428775 7348319 := bstep (se 1 (by rfl) ⟨5511239, by rfl⟩ : syracuseStep 7348319 = 11022479) B11022479
theorem B110797649 : Blo 428775 110797649 := bstep (se 2 (by rfl) ⟨41549118, by rfl⟩ : syracuseStep 110797649 = 83098237) B83098237
theorem B1745803 : Blo 428775 1745803 := bstep (se 1 (by rfl) ⟨1309352, by rfl⟩ : syracuseStep 1745803 = 2618705) B2618705
theorem B1091839 : Blo 428775 1091839 := bstep (se 1 (by rfl) ⟨818879, by rfl⟩ : syracuseStep 1091839 = 1637759) B1637759
theorem B2173391 : Blo 428775 2173391 := bstep (se 1 (by rfl) ⟨1630043, by rfl⟩ : syracuseStep 2173391 = 3260087) B3260087
theorem B3092231 : Blo 428775 3092231 := bstep (se 1 (by rfl) ⟨2319173, by rfl⟩ : syracuseStep 3092231 = 4638347) B4638347
theorem B6698321 : Blo 428775 6698321 := bstep (se 2 (by rfl) ⟨2511870, by rfl⟩ : syracuseStep 6698321 = 5023741) B5023741
theorem B1095079 : Blo 428775 1095079 := bstep (se 1 (by rfl) ⟨821309, by rfl⟩ : syracuseStep 1095079 = 1642619) B1642619
theorem B5519441 : Blo 428775 5519441 := bstep (se 2 (by rfl) ⟨2069790, by rfl⟩ : syracuseStep 5519441 = 4139581) B4139581
theorem B1752095 : Blo 428775 1752095 := bstep (se 1 (by rfl) ⟨1314071, by rfl⟩ : syracuseStep 1752095 = 2628143) B2628143
theorem B17711419 : Blo 428775 17711419 := bstep (se 1 (by rfl) ⟨13283564, by rfl⟩ : syracuseStep 17711419 = 26567129) B26567129
theorem B1459241 : Blo 428775 1459241 := bstep (se 2 (by rfl) ⟨547215, by rfl⟩ : syracuseStep 1459241 = 1094431) B1094431
theorem B967841 : Blo 428775 967841 := bstep (se 2 (by rfl) ⟨362940, by rfl⟩ : syracuseStep 967841 = 725881) B725881
theorem B8832563 : Blo 428775 8832563 := bstep (se 1 (by rfl) ⟨6624422, by rfl⟩ : syracuseStep 8832563 = 13248845) B13248845
theorem B3262031 : Blo 428775 3262031 := bstep (se 1 (by rfl) ⟨2446523, by rfl⟩ : syracuseStep 3262031 = 4893047) B4893047
theorem B2444201 : Blo 428775 2444201 := bstep (se 2 (by rfl) ⟨916575, by rfl⟩ : syracuseStep 2444201 = 1833151) B1833151
theorem B6214907 : Blo 428775 6214907 := bstep (se 1 (by rfl) ⟨4661180, by rfl⟩ : syracuseStep 6214907 = 9322361) B9322361
theorem B2184569 : Blo 428775 2184569 := bstep (se 2 (by rfl) ⟨819213, by rfl⟩ : syracuseStep 2184569 = 1638427) B1638427
theorem B644519 : Blo 428775 644519 := bstep (se 1 (by rfl) ⟨483389, by rfl⟩ : syracuseStep 644519 = 966779) B966779
theorem B645287 : Blo 428775 645287 := bstep (se 1 (by rfl) ⟨483965, by rfl⟩ : syracuseStep 645287 = 967931) B967931
theorem B973295 : Blo 428775 973295 := bstep (se 1 (by rfl) ⟨729971, by rfl⟩ : syracuseStep 973295 = 1459943) B1459943
theorem B645743 : Blo 428775 645743 := bstep (se 1 (by rfl) ⟨484307, by rfl⟩ : syracuseStep 645743 = 968615) B968615
theorem B973439 : Blo 428775 973439 := bstep (se 1 (by rfl) ⟨730079, by rfl⟩ : syracuseStep 973439 = 1460159) B1460159
theorem B9984647 : Blo 428775 9984647 := bstep (se 1 (by rfl) ⟨7488485, by rfl⟩ : syracuseStep 9984647 = 14976971) B14976971
theorem B646121 : Blo 428775 646121 := bstep (se 2 (by rfl) ⟨242295, by rfl⟩ : syracuseStep 646121 = 484591) B484591
theorem B1629179 : Blo 428775 1629179 := bstep (se 1 (by rfl) ⟨1221884, by rfl⟩ : syracuseStep 1629179 = 2443769) B2443769
theorem B482971 : Blo 428775 482971 := bstep (se 1 (by rfl) ⟨362228, by rfl⟩ : syracuseStep 482971 = 724457) B724457
theorem B4122359 : Blo 428775 4122359 := bstep (se 1 (by rfl) ⟨3091769, by rfl⟩ : syracuseStep 4122359 = 6183539) B6183539
theorem B25224995 : Blo 428775 25224995 := bstep (se 1 (by rfl) ⟨18918746, by rfl⟩ : syracuseStep 25224995 = 37837493) B37837493
theorem B11168927 : Blo 428775 11168927 := bstep (se 1 (by rfl) ⟨8376695, by rfl⟩ : syracuseStep 11168927 = 16753391) B16753391
theorem B2944295 : Blo 428775 2944295 := bstep (se 1 (by rfl) ⟨2208221, by rfl⟩ : syracuseStep 2944295 = 4416443) B4416443
theorem B3110051 : Blo 428775 3110051 := bstep (se 1 (by rfl) ⟨2332538, by rfl⟩ : syracuseStep 3110051 = 4665077) B4665077
theorem B1832843 : Blo 428775 1832843 := bstep (se 1 (by rfl) ⟨1374632, by rfl⟩ : syracuseStep 1832843 = 2749265) B2749265
theorem B2750881 : Blo 428775 2750881 := bstep (se 2 (by rfl) ⟨1031580, by rfl⟩ : syracuseStep 2750881 = 2063161) B2063161
theorem B7830431 : Blo 428775 7830431 := bstep (se 1 (by rfl) ⟨5872823, by rfl⟩ : syracuseStep 7830431 = 11745647) B11745647
theorem B818743 : Blo 428775 818743 := bstep (se 1 (by rfl) ⟨614057, by rfl⟩ : syracuseStep 818743 = 1228115) B1228115
theorem B460415 : Blo 428775 460415 := bstep (se 1 (by rfl) ⟨345311, by rfl⟩ : syracuseStep 460415 = 690623) B690623
theorem B1574815 : Blo 428775 1574815 := bstep (se 1 (by rfl) ⟨1181111, by rfl⟩ : syracuseStep 1574815 = 2362223) B2362223
theorem B429679 : Blo 428775 429679 := bstep (se 1 (by rfl) ⟨322259, by rfl⟩ : syracuseStep 429679 = 644519) B644519
theorem B3346247 : Blo 428775 3346247 := bstep (se 1 (by rfl) ⟨2509685, by rfl⟩ : syracuseStep 3346247 = 5019371) B5019371
theorem B4919291 : Blo 428775 4919291 := bstep (se 1 (by rfl) ⟨3689468, by rfl⟩ : syracuseStep 4919291 = 7378937) B7378937
theorem B430191 : Blo 428775 430191 := bstep (se 1 (by rfl) ⟨322643, by rfl⟩ : syracuseStep 430191 = 645287) B645287
theorem B430495 : Blo 428775 430495 := bstep (se 1 (by rfl) ⟨322871, by rfl⟩ : syracuseStep 430495 = 645743) B645743
theorem B6656431 : Blo 428775 6656431 := bstep (se 1 (by rfl) ⟨4992323, by rfl⟩ : syracuseStep 6656431 = 9984647) B9984647
theorem B430747 : Blo 428775 430747 := bstep (se 1 (by rfl) ⟨323060, by rfl⟩ : syracuseStep 430747 = 646121) B646121
theorem B1086119 : Blo 428775 1086119 := bstep (se 1 (by rfl) ⟨814589, by rfl⟩ : syracuseStep 1086119 = 1629179) B1629179
theorem B9310949 : Blo 428775 9310949 := bstep (se 4 (by rfl) ⟨872901, by rfl⟩ : syracuseStep 9310949 = 1745803) B1745803
theorem B73865099 : Blo 428775 73865099 := bstep (se 1 (by rfl) ⟨55398824, by rfl⟩ : syracuseStep 73865099 = 110797649) B110797649
theorem B16816663 : Blo 428775 16816663 := bstep (se 1 (by rfl) ⟨12612497, by rfl⟩ : syracuseStep 16816663 = 25224995) B25224995
theorem B1448927 : Blo 428775 1448927 := bstep (se 1 (by rfl) ⟨1086695, by rfl⟩ : syracuseStep 1448927 = 2173391) B2173391
theorem B7445951 : Blo 428775 7445951 := bstep (se 1 (by rfl) ⟨5584463, by rfl⟩ : syracuseStep 7445951 = 11168927) B11168927
theorem B2073367 : Blo 428775 2073367 := bstep (se 1 (by rfl) ⟨1555025, by rfl⟩ : syracuseStep 2073367 = 3110051) B3110051
theorem B4465547 : Blo 428775 4465547 := bstep (se 1 (by rfl) ⟨3349160, by rfl⟩ : syracuseStep 4465547 = 6698321) B6698321
theorem B1221895 : Blo 428775 1221895 := bstep (se 1 (by rfl) ⟨916421, by rfl⟩ : syracuseStep 1221895 = 1832843) B1832843
theorem B3679627 : Blo 428775 3679627 := bstep (se 1 (by rfl) ⟨2759720, by rfl⟩ : syracuseStep 3679627 = 5519441) B5519441
theorem B5220287 : Blo 428775 5220287 := bstep (se 1 (by rfl) ⟨3915215, by rfl⟩ : syracuseStep 5220287 = 7830431) B7830431
theorem B1091657 : Blo 428775 1091657 := bstep (se 2 (by rfl) ⟨409371, by rfl⟩ : syracuseStep 1091657 = 818743) B818743
theorem B2174687 : Blo 428775 2174687 := bstep (se 1 (by rfl) ⟨1631015, by rfl⟩ : syracuseStep 2174687 = 3262031) B3262031
theorem B1093601 : Blo 428775 1093601 := bstep (se 2 (by rfl) ⟨410100, by rfl⟩ : syracuseStep 1093601 = 820201) B820201
theorem B9351611 : Blo 428775 9351611 := bstep (se 1 (by rfl) ⟨7013708, by rfl⟩ : syracuseStep 9351611 = 14027417) B14027417
theorem B1226087 : Blo 428775 1226087 := bstep (se 1 (by rfl) ⟨919565, by rfl⟩ : syracuseStep 1226087 = 1839131) B1839131
theorem B1455785 : Blo 428775 1455785 := bstep (se 2 (by rfl) ⟨545919, by rfl⟩ : syracuseStep 1455785 = 1091839) B1091839
theorem B1456379 : Blo 428775 1456379 := bstep (se 1 (by rfl) ⟨1092284, by rfl⟩ : syracuseStep 1456379 = 2184569) B2184569
theorem B964943 : Blo 428775 964943 := bstep (se 1 (by rfl) ⟨723707, by rfl⟩ : syracuseStep 964943 = 1447415) B1447415
theorem B1161707 : Blo 428775 1161707 := bstep (se 1 (by rfl) ⟨871280, by rfl⟩ : syracuseStep 1161707 = 1742561) B1742561
theorem B965663 : Blo 428775 965663 := bstep (se 1 (by rfl) ⟨724247, by rfl⟩ : syracuseStep 965663 = 1448495) B1448495
theorem B965735 : Blo 428775 965735 := bstep (se 1 (by rfl) ⟨724301, by rfl⟩ : syracuseStep 965735 = 1448603) B1448603
theorem B4898879 : Blo 428775 4898879 := bstep (se 1 (by rfl) ⟨3674159, by rfl⟩ : syracuseStep 4898879 = 7348319) B7348319
theorem B1460105 : Blo 428775 1460105 := bstep (se 2 (by rfl) ⟨547539, by rfl⟩ : syracuseStep 1460105 = 1095079) B1095079
theorem B1168063 : Blo 428775 1168063 := bstep (se 1 (by rfl) ⟨876047, by rfl⟩ : syracuseStep 1168063 = 1752095) B1752095
theorem B643961 : Blo 428775 643961 := bstep (se 2 (by rfl) ⟨241485, by rfl⟩ : syracuseStep 643961 = 482971) B482971
theorem B23615225 : Blo 428775 23615225 := bstep (se 2 (by rfl) ⟨8855709, by rfl⟩ : syracuseStep 23615225 = 17711419) B17711419
theorem B972827 : Blo 428775 972827 := bstep (se 1 (by rfl) ⟨729620, by rfl⟩ : syracuseStep 972827 = 1459241) B1459241
theorem B645227 : Blo 428775 645227 := bstep (se 1 (by rfl) ⟨483920, by rfl⟩ : syracuseStep 645227 = 967841) B967841
theorem B5888375 : Blo 428775 5888375 := bstep (se 1 (by rfl) ⟨4416281, by rfl⟩ : syracuseStep 5888375 = 8832563) B8832563
theorem B1629467 : Blo 428775 1629467 := bstep (se 1 (by rfl) ⟨1222100, by rfl⟩ : syracuseStep 1629467 = 2444201) B2444201
theorem B16573085 : Blo 428775 16573085 := bstep (se 3 (by rfl) ⟨3107453, by rfl⟩ : syracuseStep 16573085 = 6214907) B6214907
theorem B615271 : Blo 428775 615271 := bstep (se 1 (by rfl) ⟨461453, by rfl⟩ : syracuseStep 615271 = 922907) B922907
theorem B2188457 : Blo 428775 2188457 := bstep (se 2 (by rfl) ⟨820671, by rfl⟩ : syracuseStep 2188457 = 1641343) B1641343
theorem B648863 : Blo 428775 648863 := bstep (se 1 (by rfl) ⟨486647, by rfl⟩ : syracuseStep 648863 = 973295) B973295
theorem B648959 : Blo 428775 648959 := bstep (se 1 (by rfl) ⟨486719, by rfl⟩ : syracuseStep 648959 = 973439) B973439
theorem B11757905 : Blo 428775 11757905 := bstep (se 2 (by rfl) ⟨4409214, by rfl⟩ : syracuseStep 11757905 = 8818429) B8818429
theorem B2748239 : Blo 428775 2748239 := bstep (se 1 (by rfl) ⟨2061179, by rfl⟩ : syracuseStep 2748239 = 4122359) B4122359
theorem B1962863 : Blo 428775 1962863 := bstep (se 1 (by rfl) ⟨1472147, by rfl⟩ : syracuseStep 1962863 = 2944295) B2944295
theorem B2061487 : Blo 428775 2061487 := bstep (se 1 (by rfl) ⟨1546115, by rfl⟩ : syracuseStep 2061487 = 3092231) B3092231
theorem B3667841 : Blo 428775 3667841 := bstep (se 2 (by rfl) ⟨1375440, by rfl⟩ : syracuseStep 3667841 = 2750881) B2750881
theorem B820361 : Blo 428775 820361 := bstep (se 2 (by rfl) ⟨307635, by rfl⟩ : syracuseStep 820361 = 615271) B615271
theorem B2099753 : Blo 428775 2099753 := bstep (se 2 (by rfl) ⟨787407, by rfl⟩ : syracuseStep 2099753 = 1574815) B1574815
theorem B2230831 : Blo 428775 2230831 := bstep (se 1 (by rfl) ⟨1673123, by rfl⟩ : syracuseStep 2230831 = 3346247) B3346247
theorem B3279527 : Blo 428775 3279527 := bstep (se 1 (by rfl) ⟨2459645, by rfl⟩ : syracuseStep 3279527 = 4919291) B4919291
theorem B89688869 : Blo 428775 89688869 := bstep (se 4 (by rfl) ⟨8408331, by rfl⟩ : syracuseStep 89688869 = 16816663) B16816663
theorem B724079 : Blo 428775 724079 := bstep (se 1 (by rfl) ⟨543059, by rfl⟩ : syracuseStep 724079 = 1086119) B1086119
theorem B429307 : Blo 428775 429307 := bstep (se 1 (by rfl) ⟨321980, by rfl⟩ : syracuseStep 429307 = 643961) B643961
theorem B430151 : Blo 428775 430151 := bstep (se 1 (by rfl) ⟨322613, by rfl⟩ : syracuseStep 430151 = 645227) B645227
theorem B1086311 : Blo 428775 1086311 := bstep (se 1 (by rfl) ⟨814733, by rfl⟩ : syracuseStep 1086311 = 1629467) B1629467
theorem B11048723 : Blo 428775 11048723 := bstep (se 1 (by rfl) ⟨8286542, by rfl⟩ : syracuseStep 11048723 = 16573085) B16573085
theorem B432575 : Blo 428775 432575 := bstep (se 1 (by rfl) ⟨324431, by rfl⟩ : syracuseStep 432575 = 648863) B648863
theorem B432639 : Blo 428775 432639 := bstep (se 1 (by rfl) ⟨324479, by rfl⟩ : syracuseStep 432639 = 648959) B648959
theorem B3480191 : Blo 428775 3480191 := bstep (se 1 (by rfl) ⟨2610143, by rfl⟩ : syracuseStep 3480191 = 5220287) B5220287
theorem B727771 : Blo 428775 727771 := bstep (se 1 (by rfl) ⟨545828, by rfl⟩ : syracuseStep 727771 = 1091657) B1091657
theorem B7838603 : Blo 428775 7838603 := bstep (se 1 (by rfl) ⟨5878952, by rfl⟩ : syracuseStep 7838603 = 11757905) B11757905
theorem B1449791 : Blo 428775 1449791 := bstep (se 1 (by rfl) ⟨1087343, by rfl⟩ : syracuseStep 1449791 = 2174687) B2174687
theorem B729067 : Blo 428775 729067 := bstep (se 1 (by rfl) ⟨546800, by rfl⟩ : syracuseStep 729067 = 1093601) B1093601
theorem B6234407 : Blo 428775 6234407 := bstep (se 1 (by rfl) ⟨4675805, by rfl⟩ : syracuseStep 6234407 = 9351611) B9351611
theorem B2764489 : Blo 428775 2764489 := bstep (se 2 (by rfl) ⟨1036683, by rfl⟩ : syracuseStep 2764489 = 2073367) B2073367
theorem B6207299 : Blo 428775 6207299 := bstep (se 1 (by rfl) ⟨4655474, by rfl⟩ : syracuseStep 6207299 = 9310949) B9310949
theorem B15743483 : Blo 428775 15743483 := bstep (se 1 (by rfl) ⟨11807612, by rfl⟩ : syracuseStep 15743483 = 23615225) B23615225
theorem B24918677 : Blo 428775 24918677 := bstep (se 6 (by rfl) ⟨584031, by rfl⟩ : syracuseStep 24918677 = 1168063) B1168063
theorem B1227773 : Blo 428775 1227773 := bstep (se 3 (by rfl) ⟨230207, by rfl⟩ : syracuseStep 1227773 = 460415) B460415
theorem B965951 : Blo 428775 965951 := bstep (se 1 (by rfl) ⟨724463, by rfl⟩ : syracuseStep 965951 = 1448927) B1448927
theorem B4963967 : Blo 428775 4963967 := bstep (se 1 (by rfl) ⟨3722975, by rfl⟩ : syracuseStep 4963967 = 7445951) B7445951
theorem B1458971 : Blo 428775 1458971 := bstep (se 1 (by rfl) ⟨1094228, by rfl⟩ : syracuseStep 1458971 = 2188457) B2188457
theorem B3097885 : Blo 428775 3097885 := bstep (se 3 (by rfl) ⟨580853, by rfl⟩ : syracuseStep 3097885 = 1161707) B1161707
theorem B970523 : Blo 428775 970523 := bstep (se 1 (by rfl) ⟨727892, by rfl⟩ : syracuseStep 970523 = 1455785) B1455785
theorem B2445227 : Blo 428775 2445227 := bstep (se 1 (by rfl) ⟨1833920, by rfl⟩ : syracuseStep 2445227 = 3667841) B3667841
theorem B970919 : Blo 428775 970919 := bstep (se 1 (by rfl) ⟨728189, by rfl⟩ : syracuseStep 970919 = 1456379) B1456379
theorem B643295 : Blo 428775 643295 := bstep (se 1 (by rfl) ⟨482471, by rfl⟩ : syracuseStep 643295 = 964943) B964943
theorem B643775 : Blo 428775 643775 := bstep (se 1 (by rfl) ⟨482831, by rfl⟩ : syracuseStep 643775 = 965663) B965663
theorem B643823 : Blo 428775 643823 := bstep (se 1 (by rfl) ⟨482867, by rfl⟩ : syracuseStep 643823 = 965735) B965735
theorem B3265919 : Blo 428775 3265919 := bstep (se 1 (by rfl) ⟨2449439, by rfl⟩ : syracuseStep 3265919 = 4898879) B4898879
theorem B973403 : Blo 428775 973403 := bstep (se 1 (by rfl) ⟨730052, by rfl⟩ : syracuseStep 973403 = 1460105) B1460105
theorem B1629193 : Blo 428775 1629193 := bstep (se 2 (by rfl) ⟨610947, by rfl⟩ : syracuseStep 1629193 = 1221895) B1221895
theorem B4906169 : Blo 428775 4906169 := bstep (se 2 (by rfl) ⟨1839813, by rfl⟩ : syracuseStep 4906169 = 3679627) B3679627
theorem B49243399 : Blo 428775 49243399 := bstep (se 1 (by rfl) ⟨36932549, by rfl⟩ : syracuseStep 49243399 = 73865099) B73865099
theorem B648551 : Blo 428775 648551 := bstep (se 1 (by rfl) ⟨486413, by rfl⟩ : syracuseStep 648551 = 972827) B972827
theorem B3925583 : Blo 428775 3925583 := bstep (se 1 (by rfl) ⟨2944187, by rfl⟩ : syracuseStep 3925583 = 5888375) B5888375
theorem B8875241 : Blo 428775 8875241 := bstep (se 2 (by rfl) ⟨3328215, by rfl⟩ : syracuseStep 8875241 = 6656431) B6656431
theorem B2977031 : Blo 428775 2977031 := bstep (se 1 (by rfl) ⟨2232773, by rfl⟩ : syracuseStep 2977031 = 4465547) B4465547
theorem B2748649 : Blo 428775 2748649 := bstep (se 2 (by rfl) ⟨1030743, by rfl⟩ : syracuseStep 2748649 = 2061487) B2061487
theorem B1832159 : Blo 428775 1832159 := bstep (se 1 (by rfl) ⟨1374119, by rfl⟩ : syracuseStep 1832159 = 2748239) B2748239
theorem B1308575 : Blo 428775 1308575 := bstep (se 1 (by rfl) ⟨981431, by rfl⟩ : syracuseStep 1308575 = 1962863) B1962863
theorem B817391 : Blo 428775 817391 := bstep (se 1 (by rfl) ⟨613043, by rfl⟩ : syracuseStep 817391 = 1226087) B1226087
theorem B4130513 : Blo 428775 4130513 := bstep (se 2 (by rfl) ⟨1548942, by rfl⟩ : syracuseStep 4130513 = 3097885) B3097885
theorem B428863 : Blo 428775 428863 := bstep (se 1 (by rfl) ⟨321647, by rfl⟩ : syracuseStep 428863 = 643295) B643295
theorem B429183 : Blo 428775 429183 := bstep (se 1 (by rfl) ⟨321887, by rfl⟩ : syracuseStep 429183 = 643775) B643775
theorem B429215 : Blo 428775 429215 := bstep (se 1 (by rfl) ⟨321911, by rfl⟩ : syracuseStep 429215 = 643823) B643823
theorem B724207 : Blo 428775 724207 := bstep (se 1 (by rfl) ⟨543155, by rfl⟩ : syracuseStep 724207 = 1086311) B1086311
theorem B4885757 : Blo 428775 4885757 := bstep (se 3 (by rfl) ⟨916079, by rfl⟩ : syracuseStep 4885757 = 1832159) B1832159
theorem B432367 : Blo 428775 432367 := bstep (se 1 (by rfl) ⟨324275, by rfl⟩ : syracuseStep 432367 = 648551) B648551
theorem B7938749 : Blo 428775 7938749 := bstep (se 3 (by rfl) ⟨1488515, by rfl⟩ : syracuseStep 7938749 = 2977031) B2977031
theorem B4138199 : Blo 428775 4138199 := bstep (se 1 (by rfl) ⟨3103649, by rfl⟩ : syracuseStep 4138199 = 6207299) B6207299
theorem B2172257 : Blo 428775 2172257 := bstep (se 2 (by rfl) ⟨814596, by rfl⟩ : syracuseStep 2172257 = 1629193) B1629193
theorem B10495655 : Blo 428775 10495655 := bstep (se 1 (by rfl) ⟨7871741, by rfl⟩ : syracuseStep 10495655 = 15743483) B15743483
theorem B2177279 : Blo 428775 2177279 := bstep (se 1 (by rfl) ⟨1632959, by rfl⟩ : syracuseStep 2177279 = 3265919) B3265919
theorem B5225735 : Blo 428775 5225735 := bstep (se 1 (by rfl) ⟨3919301, by rfl⟩ : syracuseStep 5225735 = 7838603) B7838603
theorem B3685985 : Blo 428775 3685985 := bstep (se 2 (by rfl) ⟨1382244, by rfl⟩ : syracuseStep 3685985 = 2764489) B2764489
theorem B966527 : Blo 428775 966527 := bstep (se 1 (by rfl) ⟨724895, by rfl⟩ : syracuseStep 966527 = 1449791) B1449791
theorem B1050525845 : Blo 428775 1050525845 := bstep (se 6 (by rfl) ⟨24621699, by rfl⟩ : syracuseStep 1050525845 = 49243399) B49243399
theorem B2179709 : Blo 428775 2179709 := bstep (se 3 (by rfl) ⟨408695, by rfl⟩ : syracuseStep 2179709 = 817391) B817391
theorem B5916827 : Blo 428775 5916827 := bstep (se 1 (by rfl) ⟨4437620, by rfl⟩ : syracuseStep 5916827 = 8875241) B8875241
theorem B970361 : Blo 428775 970361 := bstep (se 2 (by rfl) ⟨363885, by rfl⟩ : syracuseStep 970361 = 727771) B727771
theorem B872383 : Blo 428775 872383 := bstep (se 1 (by rfl) ⟨654287, by rfl⟩ : syracuseStep 872383 = 1308575) B1308575
theorem B643967 : Blo 428775 643967 := bstep (se 1 (by rfl) ⟨482975, by rfl⟩ : syracuseStep 643967 = 965951) B965951
theorem B972089 : Blo 428775 972089 := bstep (se 2 (by rfl) ⟨364533, by rfl⟩ : syracuseStep 972089 = 729067) B729067
theorem B972647 : Blo 428775 972647 := bstep (se 1 (by rfl) ⟨729485, by rfl⟩ : syracuseStep 972647 = 1458971) B1458971
theorem B546907 : Blo 428775 546907 := bstep (se 1 (by rfl) ⟨410180, by rfl⟩ : syracuseStep 546907 = 820361) B820361
theorem B1399835 : Blo 428775 1399835 := bstep (se 1 (by rfl) ⟨1049876, by rfl⟩ : syracuseStep 1399835 = 2099753) B2099753
theorem B2186351 : Blo 428775 2186351 := bstep (se 1 (by rfl) ⟨1639763, by rfl⟩ : syracuseStep 2186351 = 3279527) B3279527
theorem B59792579 : Blo 428775 59792579 := bstep (se 1 (by rfl) ⟨44844434, by rfl⟩ : syracuseStep 59792579 = 89688869) B89688869
theorem B482719 : Blo 428775 482719 := bstep (se 1 (by rfl) ⟨362039, by rfl⟩ : syracuseStep 482719 = 724079) B724079
theorem B647015 : Blo 428775 647015 := bstep (se 1 (by rfl) ⟨485261, by rfl⟩ : syracuseStep 647015 = 970523) B970523
theorem B1630151 : Blo 428775 1630151 := bstep (se 1 (by rfl) ⟨1222613, by rfl⟩ : syracuseStep 1630151 = 2445227) B2445227
theorem B647279 : Blo 428775 647279 := bstep (se 1 (by rfl) ⟨485459, by rfl⟩ : syracuseStep 647279 = 970919) B970919
theorem B2974441 : Blo 428775 2974441 := bstep (se 2 (by rfl) ⟨1115415, by rfl⟩ : syracuseStep 2974441 = 2230831) B2230831
theorem B7365815 : Blo 428775 7365815 := bstep (se 1 (by rfl) ⟨5524361, by rfl⟩ : syracuseStep 7365815 = 11048723) B11048723
theorem B648935 : Blo 428775 648935 := bstep (se 1 (by rfl) ⟨486701, by rfl⟩ : syracuseStep 648935 = 973403) B973403
theorem B2320127 : Blo 428775 2320127 := bstep (se 1 (by rfl) ⟨1740095, by rfl⟩ : syracuseStep 2320127 = 3480191) B3480191
theorem B3270779 : Blo 428775 3270779 := bstep (se 1 (by rfl) ⟨2453084, by rfl⟩ : syracuseStep 3270779 = 4906169) B4906169
theorem B4156271 : Blo 428775 4156271 := bstep (se 1 (by rfl) ⟨3117203, by rfl⟩ : syracuseStep 4156271 = 6234407) B6234407
theorem B3664865 : Blo 428775 3664865 := bstep (se 2 (by rfl) ⟨1374324, by rfl⟩ : syracuseStep 3664865 = 2748649) B2748649
theorem B2617055 : Blo 428775 2617055 := bstep (se 1 (by rfl) ⟨1962791, by rfl⟩ : syracuseStep 2617055 = 3925583) B3925583
theorem B16612451 : Blo 428775 16612451 := bstep (se 1 (by rfl) ⟨12459338, by rfl⟩ : syracuseStep 16612451 = 24918677) B24918677
theorem B818515 : Blo 428775 818515 := bstep (se 1 (by rfl) ⟨613886, by rfl⟩ : syracuseStep 818515 = 1227773) B1227773
theorem B3309311 : Blo 428775 3309311 := bstep (se 1 (by rfl) ⟨2481983, by rfl⟩ : syracuseStep 3309311 = 4963967) B4963967
theorem B700350563 : Blo 428775 700350563 := bstep (se 1 (by rfl) ⟨525262922, by rfl⟩ : syracuseStep 700350563 = 1050525845) B1050525845
theorem B3965921 : Blo 428775 3965921 := bstep (se 2 (by rfl) ⟨1487220, by rfl⟩ : syracuseStep 3965921 = 2974441) B2974441
theorem B2753675 : Blo 428775 2753675 := bstep (se 1 (by rfl) ⟨2065256, by rfl⟩ : syracuseStep 2753675 = 4130513) B4130513
theorem B429311 : Blo 428775 429311 := bstep (se 1 (by rfl) ⟨321983, by rfl⟩ : syracuseStep 429311 = 643967) B643967
theorem B431343 : Blo 428775 431343 := bstep (se 1 (by rfl) ⟨323507, by rfl⟩ : syracuseStep 431343 = 647015) B647015
theorem B1086767 : Blo 428775 1086767 := bstep (se 1 (by rfl) ⟨815075, by rfl⟩ : syracuseStep 1086767 = 1630151) B1630151
theorem B431519 : Blo 428775 431519 := bstep (se 1 (by rfl) ⟨323639, by rfl⟩ : syracuseStep 431519 = 647279) B647279
theorem B2758799 : Blo 428775 2758799 := bstep (se 1 (by rfl) ⟨2069099, by rfl⟩ : syracuseStep 2758799 = 4138199) B4138199
theorem B1448171 : Blo 428775 1448171 := bstep (se 1 (by rfl) ⟨1086128, by rfl⟩ : syracuseStep 1448171 = 2172257) B2172257
theorem B432623 : Blo 428775 432623 := bstep (se 1 (by rfl) ⟨324467, by rfl⟩ : syracuseStep 432623 = 648935) B648935
theorem B1546751 : Blo 428775 1546751 := bstep (se 1 (by rfl) ⟨1160063, by rfl⟩ : syracuseStep 1546751 = 2320127) B2320127
theorem B1744703 : Blo 428775 1744703 := bstep (se 1 (by rfl) ⟨1308527, by rfl⟩ : syracuseStep 1744703 = 2617055) B2617055
theorem B729209 : Blo 428775 729209 := bstep (se 2 (by rfl) ⟨273453, by rfl⟩ : syracuseStep 729209 = 546907) B546907
theorem B1451519 : Blo 428775 1451519 := bstep (se 1 (by rfl) ⟨1088639, by rfl⟩ : syracuseStep 1451519 = 2177279) B2177279
theorem B1091353 : Blo 428775 1091353 := bstep (se 2 (by rfl) ⟨409257, by rfl⟩ : syracuseStep 1091353 = 818515) B818515
theorem B3483823 : Blo 428775 3483823 := bstep (se 1 (by rfl) ⟨2612867, by rfl⟩ : syracuseStep 3483823 = 5225735) B5225735
theorem B2206207 : Blo 428775 2206207 := bstep (se 1 (by rfl) ⟨1654655, by rfl⟩ : syracuseStep 2206207 = 3309311) B3309311
theorem B1453139 : Blo 428775 1453139 := bstep (se 1 (by rfl) ⟨1089854, by rfl⟩ : syracuseStep 1453139 = 2179709) B2179709
theorem B3944551 : Blo 428775 3944551 := bstep (se 1 (by rfl) ⟨2958413, by rfl⟩ : syracuseStep 3944551 = 5916827) B5916827
theorem B3257171 : Blo 428775 3257171 := bstep (se 1 (by rfl) ⟨2442878, by rfl⟩ : syracuseStep 3257171 = 4885757) B4885757
theorem B965609 : Blo 428775 965609 := bstep (se 2 (by rfl) ⟨362103, by rfl⟩ : syracuseStep 965609 = 724207) B724207
theorem B933223 : Blo 428775 933223 := bstep (se 1 (by rfl) ⟨699917, by rfl⟩ : syracuseStep 933223 = 1399835) B1399835
theorem B1457567 : Blo 428775 1457567 := bstep (se 1 (by rfl) ⟨1093175, by rfl⟩ : syracuseStep 1457567 = 2186351) B2186351
theorem B39861719 : Blo 428775 39861719 := bstep (se 1 (by rfl) ⟨29896289, by rfl⟩ : syracuseStep 39861719 = 59792579) B59792579
theorem B1163177 : Blo 428775 1163177 := bstep (se 2 (by rfl) ⟨436191, by rfl⟩ : syracuseStep 1163177 = 872383) B872383
theorem B5292499 : Blo 428775 5292499 := bstep (se 1 (by rfl) ⟨3969374, by rfl⟩ : syracuseStep 5292499 = 7938749) B7938749
theorem B6997103 : Blo 428775 6997103 := bstep (se 1 (by rfl) ⟨5247827, by rfl⟩ : syracuseStep 6997103 = 10495655) B10495655
theorem B2180519 : Blo 428775 2180519 := bstep (se 1 (by rfl) ⟨1635389, by rfl⟩ : syracuseStep 2180519 = 3270779) B3270779
theorem B2770847 : Blo 428775 2770847 := bstep (se 1 (by rfl) ⟨2078135, by rfl⟩ : syracuseStep 2770847 = 4156271) B4156271
theorem B2443243 : Blo 428775 2443243 := bstep (se 1 (by rfl) ⟨1832432, by rfl⟩ : syracuseStep 2443243 = 3664865) B3664865
theorem B643625 : Blo 428775 643625 := bstep (se 2 (by rfl) ⟨241359, by rfl⟩ : syracuseStep 643625 = 482719) B482719
theorem B644351 : Blo 428775 644351 := bstep (se 1 (by rfl) ⟨483263, by rfl⟩ : syracuseStep 644351 = 966527) B966527
theorem B646907 : Blo 428775 646907 := bstep (se 1 (by rfl) ⟨485180, by rfl⟩ : syracuseStep 646907 = 970361) B970361
theorem B648059 : Blo 428775 648059 := bstep (se 1 (by rfl) ⟨486044, by rfl⟩ : syracuseStep 648059 = 972089) B972089
theorem B648431 : Blo 428775 648431 := bstep (se 1 (by rfl) ⟨486323, by rfl⟩ : syracuseStep 648431 = 972647) B972647
theorem B4910543 : Blo 428775 4910543 := bstep (se 1 (by rfl) ⟨3682907, by rfl⟩ : syracuseStep 4910543 = 7365815) B7365815
theorem B11074967 : Blo 428775 11074967 := bstep (se 1 (by rfl) ⟨8306225, by rfl⟩ : syracuseStep 11074967 = 16612451) B16612451
theorem B2457323 : Blo 428775 2457323 := bstep (se 1 (by rfl) ⟨1842992, by rfl⟩ : syracuseStep 2457323 = 3685985) B3685985
theorem B1835783 : Blo 428775 1835783 := bstep (se 1 (by rfl) ⟨1376837, by rfl⟩ : syracuseStep 1835783 = 2753675) B2753675
theorem B11766437 : Blo 428775 11766437 := bstep (se 4 (by rfl) ⟨1103103, by rfl⟩ : syracuseStep 11766437 = 2206207) B2206207
theorem B429083 : Blo 428775 429083 := bstep (se 1 (by rfl) ⟨321812, by rfl⟩ : syracuseStep 429083 = 643625) B643625
theorem B429567 : Blo 428775 429567 := bstep (se 1 (by rfl) ⟨322175, by rfl⟩ : syracuseStep 429567 = 644351) B644351
theorem B724511 : Blo 428775 724511 := bstep (se 1 (by rfl) ⟨543383, by rfl⟩ : syracuseStep 724511 = 1086767) B1086767
theorem B1839199 : Blo 428775 1839199 := bstep (se 1 (by rfl) ⟨1379399, by rfl⟩ : syracuseStep 1839199 = 2758799) B2758799
theorem B431271 : Blo 428775 431271 := bstep (se 1 (by rfl) ⟨323453, by rfl⟩ : syracuseStep 431271 = 646907) B646907
theorem B432039 : Blo 428775 432039 := bstep (se 1 (by rfl) ⟨324029, by rfl⟩ : syracuseStep 432039 = 648059) B648059
theorem B432287 : Blo 428775 432287 := bstep (se 1 (by rfl) ⟨324215, by rfl⟩ : syracuseStep 432287 = 648431) B648431
theorem B2171447 : Blo 428775 2171447 := bstep (se 1 (by rfl) ⟨1628585, by rfl⟩ : syracuseStep 2171447 = 3257171) B3257171
theorem B7383311 : Blo 428775 7383311 := bstep (se 1 (by rfl) ⟨5537483, by rfl⟩ : syracuseStep 7383311 = 11074967) B11074967
theorem B7056665 : Blo 428775 7056665 := bstep (se 2 (by rfl) ⟨2646249, by rfl⟩ : syracuseStep 7056665 = 5292499) B5292499
theorem B4664735 : Blo 428775 4664735 := bstep (se 1 (by rfl) ⟨3498551, by rfl⟩ : syracuseStep 4664735 = 6997103) B6997103
theorem B1453679 : Blo 428775 1453679 := bstep (se 1 (by rfl) ⟨1090259, by rfl⟩ : syracuseStep 1453679 = 2180519) B2180519
theorem B1847231 : Blo 428775 1847231 := bstep (se 1 (by rfl) ⟨1385423, by rfl⟩ : syracuseStep 1847231 = 2770847) B2770847
theorem B1455137 : Blo 428775 1455137 := bstep (se 2 (by rfl) ⟨545676, by rfl⟩ : syracuseStep 1455137 = 1091353) B1091353
theorem B3257657 : Blo 428775 3257657 := bstep (se 2 (by rfl) ⟨1221621, by rfl⟩ : syracuseStep 3257657 = 2443243) B2443243
theorem B965447 : Blo 428775 965447 := bstep (se 1 (by rfl) ⟨724085, by rfl⟩ : syracuseStep 965447 = 1448171) B1448171
theorem B1031167 : Blo 428775 1031167 := bstep (se 1 (by rfl) ⟨773375, by rfl⟩ : syracuseStep 1031167 = 1546751) B1546751
theorem B1163135 : Blo 428775 1163135 := bstep (se 1 (by rfl) ⟨872351, by rfl⟩ : syracuseStep 1163135 = 1744703) B1744703
theorem B5259401 : Blo 428775 5259401 := bstep (se 2 (by rfl) ⟨1972275, by rfl⟩ : syracuseStep 5259401 = 3944551) B3944551
theorem B967679 : Blo 428775 967679 := bstep (se 1 (by rfl) ⟨725759, by rfl⟩ : syracuseStep 967679 = 1451519) B1451519
theorem B968759 : Blo 428775 968759 := bstep (se 1 (by rfl) ⟨726569, by rfl⟩ : syracuseStep 968759 = 1453139) B1453139
theorem B643739 : Blo 428775 643739 := bstep (se 1 (by rfl) ⟨482804, by rfl⟩ : syracuseStep 643739 = 965609) B965609
theorem B971711 : Blo 428775 971711 := bstep (se 1 (by rfl) ⟨728783, by rfl⟩ : syracuseStep 971711 = 1457567) B1457567
theorem B775451 : Blo 428775 775451 := bstep (se 1 (by rfl) ⟨581588, by rfl⟩ : syracuseStep 775451 = 1163177) B1163177
theorem B466900375 : Blo 428775 466900375 := bstep (se 1 (by rfl) ⟨350175281, by rfl⟩ : syracuseStep 466900375 = 700350563) B700350563
theorem B2643947 : Blo 428775 2643947 := bstep (se 1 (by rfl) ⟨1982960, by rfl⟩ : syracuseStep 2643947 = 3965921) B3965921
theorem B4645097 : Blo 428775 4645097 := bstep (se 2 (by rfl) ⟨1741911, by rfl⟩ : syracuseStep 4645097 = 3483823) B3483823
theorem B486139 : Blo 428775 486139 := bstep (se 1 (by rfl) ⟨364604, by rfl⟩ : syracuseStep 486139 = 729209) B729209
theorem B3273695 : Blo 428775 3273695 := bstep (se 1 (by rfl) ⟨2455271, by rfl⟩ : syracuseStep 3273695 = 4910543) B4910543
theorem B1244297 : Blo 428775 1244297 := bstep (se 2 (by rfl) ⟨466611, by rfl⟩ : syracuseStep 1244297 = 933223) B933223
theorem B26574479 : Blo 428775 26574479 := bstep (se 1 (by rfl) ⟨19930859, by rfl⟩ : syracuseStep 26574479 = 39861719) B39861719
theorem B1638215 : Blo 428775 1638215 := bstep (se 1 (by rfl) ⟨1228661, by rfl⟩ : syracuseStep 1638215 = 2457323) B2457323
theorem B3506267 : Blo 428775 3506267 := bstep (se 1 (by rfl) ⟨2629700, by rfl⟩ : syracuseStep 3506267 = 5259401) B5259401
theorem B429159 : Blo 428775 429159 := bstep (se 1 (by rfl) ⟨321869, by rfl⟩ : syracuseStep 429159 = 643739) B643739
theorem B2067869 : Blo 428775 2067869 := bstep (se 3 (by rfl) ⟨387725, by rfl⟩ : syracuseStep 2067869 = 775451) B775451
theorem B1447631 : Blo 428775 1447631 := bstep (se 1 (by rfl) ⟨1085723, by rfl⟩ : syracuseStep 1447631 = 2171447) B2171447
theorem B4922207 : Blo 428775 4922207 := bstep (se 1 (by rfl) ⟨3691655, by rfl⟩ : syracuseStep 4922207 = 7383311) B7383311
theorem B622533833 : Blo 428775 622533833 := bstep (se 2 (by rfl) ⟨233450187, by rfl⟩ : syracuseStep 622533833 = 466900375) B466900375
theorem B2171771 : Blo 428775 2171771 := bstep (se 1 (by rfl) ⟨1628828, by rfl⟩ : syracuseStep 2171771 = 3257657) B3257657
theorem B829531 : Blo 428775 829531 := bstep (se 1 (by rfl) ⟨622148, by rfl⟩ : syracuseStep 829531 = 1244297) B1244297
theorem B1092143 : Blo 428775 1092143 := bstep (se 1 (by rfl) ⟨819107, by rfl⟩ : syracuseStep 1092143 = 1638215) B1638215
theorem B1223855 : Blo 428775 1223855 := bstep (se 1 (by rfl) ⟨917891, by rfl⟩ : syracuseStep 1223855 = 1835783) B1835783
theorem B7844291 : Blo 428775 7844291 := bstep (se 1 (by rfl) ⟨5883218, by rfl⟩ : syracuseStep 7844291 = 11766437) B11766437
theorem B3096731 : Blo 428775 3096731 := bstep (se 1 (by rfl) ⟨2322548, by rfl⟩ : syracuseStep 3096731 = 4645097) B4645097
theorem B4704443 : Blo 428775 4704443 := bstep (se 1 (by rfl) ⟨3528332, by rfl⟩ : syracuseStep 4704443 = 7056665) B7056665
theorem B969119 : Blo 428775 969119 := bstep (se 1 (by rfl) ⟨726839, by rfl⟩ : syracuseStep 969119 = 1453679) B1453679
theorem B1231487 : Blo 428775 1231487 := bstep (se 1 (by rfl) ⟨923615, by rfl⟩ : syracuseStep 1231487 = 1847231) B1847231
theorem B2182463 : Blo 428775 2182463 := bstep (se 1 (by rfl) ⟨1636847, by rfl⟩ : syracuseStep 2182463 = 3273695) B3273695
theorem B970091 : Blo 428775 970091 := bstep (se 1 (by rfl) ⟨727568, by rfl⟩ : syracuseStep 970091 = 1455137) B1455137
theorem B643631 : Blo 428775 643631 := bstep (se 1 (by rfl) ⟨482723, by rfl⟩ : syracuseStep 643631 = 965447) B965447
theorem B17716319 : Blo 428775 17716319 := bstep (se 1 (by rfl) ⟨13287239, by rfl⟩ : syracuseStep 17716319 = 26574479) B26574479
theorem B775423 : Blo 428775 775423 := bstep (se 1 (by rfl) ⟨581567, by rfl⟩ : syracuseStep 775423 = 1163135) B1163135
theorem B645119 : Blo 428775 645119 := bstep (se 1 (by rfl) ⟨483839, by rfl⟩ : syracuseStep 645119 = 967679) B967679
theorem B645839 : Blo 428775 645839 := bstep (se 1 (by rfl) ⟨484379, by rfl⟩ : syracuseStep 645839 = 968759) B968759
theorem B483007 : Blo 428775 483007 := bstep (se 1 (by rfl) ⟨362255, by rfl⟩ : syracuseStep 483007 = 724511) B724511
theorem B647807 : Blo 428775 647807 := bstep (se 1 (by rfl) ⟨485855, by rfl⟩ : syracuseStep 647807 = 971711) B971711
theorem B648185 : Blo 428775 648185 := bstep (se 2 (by rfl) ⟨243069, by rfl⟩ : syracuseStep 648185 = 486139) B486139
theorem B1762631 : Blo 428775 1762631 := bstep (se 1 (by rfl) ⟨1321973, by rfl⟩ : syracuseStep 1762631 = 2643947) B2643947
theorem B2452265 : Blo 428775 2452265 := bstep (se 2 (by rfl) ⟨919599, by rfl⟩ : syracuseStep 2452265 = 1839199) B1839199
theorem B3109823 : Blo 428775 3109823 := bstep (se 1 (by rfl) ⟨2332367, by rfl⟩ : syracuseStep 3109823 = 4664735) B4664735
theorem B1374889 : Blo 428775 1374889 := bstep (se 2 (by rfl) ⟨515583, by rfl⟩ : syracuseStep 1374889 = 1031167) B1031167
theorem B2064487 : Blo 428775 2064487 := bstep (se 1 (by rfl) ⟨1548365, by rfl⟩ : syracuseStep 2064487 = 3096731) B3096731
theorem B4424165 : Blo 428775 4424165 := bstep (se 4 (by rfl) ⟨414765, by rfl⟩ : syracuseStep 4424165 = 829531) B829531
theorem B820991 : Blo 428775 820991 := bstep (se 1 (by rfl) ⟨615743, by rfl⟩ : syracuseStep 820991 = 1231487) B1231487
theorem B429087 : Blo 428775 429087 := bstep (se 1 (by rfl) ⟨321815, by rfl⟩ : syracuseStep 429087 = 643631) B643631
theorem B430079 : Blo 428775 430079 := bstep (se 1 (by rfl) ⟨322559, by rfl⟩ : syracuseStep 430079 = 645119) B645119
theorem B430559 : Blo 428775 430559 := bstep (se 1 (by rfl) ⟨322919, by rfl⟩ : syracuseStep 430559 = 645839) B645839
theorem B3281471 : Blo 428775 3281471 := bstep (se 1 (by rfl) ⟨2461103, by rfl⟩ : syracuseStep 3281471 = 4922207) B4922207
theorem B431871 : Blo 428775 431871 := bstep (se 1 (by rfl) ⟨323903, by rfl⟩ : syracuseStep 431871 = 647807) B647807
theorem B1447847 : Blo 428775 1447847 := bstep (se 1 (by rfl) ⟨1085885, by rfl⟩ : syracuseStep 1447847 = 2171771) B2171771
theorem B432123 : Blo 428775 432123 := bstep (se 1 (by rfl) ⟨324092, by rfl⟩ : syracuseStep 432123 = 648185) B648185
theorem B728095 : Blo 428775 728095 := bstep (se 1 (by rfl) ⟨546071, by rfl⟩ : syracuseStep 728095 = 1092143) B1092143
theorem B2073215 : Blo 428775 2073215 := bstep (se 1 (by rfl) ⟨1554911, by rfl⟩ : syracuseStep 2073215 = 3109823) B3109823
theorem B5514317 : Blo 428775 5514317 := bstep (se 3 (by rfl) ⟨1033934, by rfl⟩ : syracuseStep 5514317 = 2067869) B2067869
theorem B2337511 : Blo 428775 2337511 := bstep (se 1 (by rfl) ⟨1753133, by rfl⟩ : syracuseStep 2337511 = 3506267) B3506267
theorem B1454975 : Blo 428775 1454975 := bstep (se 1 (by rfl) ⟨1091231, by rfl⟩ : syracuseStep 1454975 = 2182463) B2182463
theorem B11810879 : Blo 428775 11810879 := bstep (se 1 (by rfl) ⟨8858159, by rfl⟩ : syracuseStep 11810879 = 17716319) B17716319
theorem B965087 : Blo 428775 965087 := bstep (se 1 (by rfl) ⟨723815, by rfl⟩ : syracuseStep 965087 = 1447631) B1447631
theorem B415022555 : Blo 428775 415022555 := bstep (se 1 (by rfl) ⟨311266916, by rfl⟩ : syracuseStep 415022555 = 622533833) B622533833
theorem B1033897 : Blo 428775 1033897 := bstep (se 2 (by rfl) ⟨387711, by rfl⟩ : syracuseStep 1033897 = 775423) B775423
theorem B5229527 : Blo 428775 5229527 := bstep (se 1 (by rfl) ⟨3922145, by rfl⟩ : syracuseStep 5229527 = 7844291) B7844291
theorem B644009 : Blo 428775 644009 := bstep (se 2 (by rfl) ⟨241503, by rfl⟩ : syracuseStep 644009 = 483007) B483007
theorem B3136295 : Blo 428775 3136295 := bstep (se 1 (by rfl) ⟨2352221, by rfl⟩ : syracuseStep 3136295 = 4704443) B4704443
theorem B646079 : Blo 428775 646079 := bstep (se 1 (by rfl) ⟨484559, by rfl⟩ : syracuseStep 646079 = 969119) B969119
theorem B646727 : Blo 428775 646727 := bstep (se 1 (by rfl) ⟨485045, by rfl⟩ : syracuseStep 646727 = 970091) B970091
theorem B1175087 : Blo 428775 1175087 := bstep (se 1 (by rfl) ⟨881315, by rfl⟩ : syracuseStep 1175087 = 1762631) B1762631
theorem B1634843 : Blo 428775 1634843 := bstep (se 1 (by rfl) ⟨1226132, by rfl⟩ : syracuseStep 1634843 = 2452265) B2452265
theorem B815903 : Blo 428775 815903 := bstep (se 1 (by rfl) ⟨611927, by rfl⟩ : syracuseStep 815903 = 1223855) B1223855
theorem B1833185 : Blo 428775 1833185 := bstep (se 2 (by rfl) ⟨687444, by rfl⟩ : syracuseStep 1833185 = 1374889) B1374889
theorem B2752649 : Blo 428775 2752649 := bstep (se 2 (by rfl) ⟨1032243, by rfl⟩ : syracuseStep 2752649 = 2064487) B2064487
theorem B2949443 : Blo 428775 2949443 := bstep (se 1 (by rfl) ⟨2212082, by rfl⟩ : syracuseStep 2949443 = 4424165) B4424165
theorem B1378529 : Blo 428775 1378529 := bstep (se 2 (by rfl) ⟨516948, by rfl⟩ : syracuseStep 1378529 = 1033897) B1033897
theorem B429339 : Blo 428775 429339 := bstep (se 1 (by rfl) ⟨322004, by rfl⟩ : syracuseStep 429339 = 644009) B644009
theorem B3116681 : Blo 428775 3116681 := bstep (se 2 (by rfl) ⟨1168755, by rfl⟩ : syracuseStep 3116681 = 2337511) B2337511
theorem B430719 : Blo 428775 430719 := bstep (se 1 (by rfl) ⟨323039, by rfl⟩ : syracuseStep 430719 = 646079) B646079
theorem B431151 : Blo 428775 431151 := bstep (se 1 (by rfl) ⟨323363, by rfl⟩ : syracuseStep 431151 = 646727) B646727
theorem B1382143 : Blo 428775 1382143 := bstep (se 1 (by rfl) ⟨1036607, by rfl⟩ : syracuseStep 1382143 = 2073215) B2073215
theorem B3676211 : Blo 428775 3676211 := bstep (se 1 (by rfl) ⟨2757158, by rfl⟩ : syracuseStep 3676211 = 5514317) B5514317
theorem B1089895 : Blo 428775 1089895 := bstep (se 1 (by rfl) ⟨817421, by rfl⟩ : syracuseStep 1089895 = 1634843) B1634843
theorem B7873919 : Blo 428775 7873919 := bstep (se 1 (by rfl) ⟨5905439, by rfl⟩ : syracuseStep 7873919 = 11810879) B11810879
theorem B1222123 : Blo 428775 1222123 := bstep (se 1 (by rfl) ⟨916592, by rfl⟩ : syracuseStep 1222123 = 1833185) B1833185
theorem B965231 : Blo 428775 965231 := bstep (se 1 (by rfl) ⟨723923, by rfl⟩ : syracuseStep 965231 = 1447847) B1447847
theorem B13945405 : Blo 428775 13945405 := bstep (se 3 (by rfl) ⟨2614763, by rfl⟩ : syracuseStep 13945405 = 5229527) B5229527
theorem B543935 : Blo 428775 543935 := bstep (se 1 (by rfl) ⟨407951, by rfl⟩ : syracuseStep 543935 = 815903) B815903
theorem B969983 : Blo 428775 969983 := bstep (se 1 (by rfl) ⟨727487, by rfl⟩ : syracuseStep 969983 = 1454975) B1454975
theorem B970793 : Blo 428775 970793 := bstep (se 2 (by rfl) ⟨364047, by rfl⟩ : syracuseStep 970793 = 728095) B728095
theorem B643391 : Blo 428775 643391 := bstep (se 1 (by rfl) ⟨482543, by rfl⟩ : syracuseStep 643391 = 965087) B965087
theorem B276681703 : Blo 428775 276681703 := bstep (se 1 (by rfl) ⟨207511277, by rfl⟩ : syracuseStep 276681703 = 415022555) B415022555
theorem B547327 : Blo 428775 547327 := bstep (se 1 (by rfl) ⟨410495, by rfl⟩ : syracuseStep 547327 = 820991) B820991
theorem B2187647 : Blo 428775 2187647 := bstep (se 1 (by rfl) ⟨1640735, by rfl⟩ : syracuseStep 2187647 = 3281471) B3281471
theorem B2090863 : Blo 428775 2090863 := bstep (se 1 (by rfl) ⟨1568147, by rfl⟩ : syracuseStep 2090863 = 3136295) B3136295
theorem B783391 : Blo 428775 783391 := bstep (se 1 (by rfl) ⟨587543, by rfl⟩ : syracuseStep 783391 = 1175087) B1175087
theorem B1835099 : Blo 428775 1835099 := bstep (se 1 (by rfl) ⟨1376324, by rfl⟩ : syracuseStep 1835099 = 2752649) B2752649
theorem B1966295 : Blo 428775 1966295 := bstep (se 1 (by rfl) ⟨1474721, by rfl⟩ : syracuseStep 1966295 = 2949443) B2949443
theorem B919019 : Blo 428775 919019 := bstep (se 1 (by rfl) ⟨689264, by rfl⟩ : syracuseStep 919019 = 1378529) B1378529
theorem B428927 : Blo 428775 428927 := bstep (se 1 (by rfl) ⟨321695, by rfl⟩ : syracuseStep 428927 = 643391) B643391
theorem B5249279 : Blo 428775 5249279 := bstep (se 1 (by rfl) ⟨3936959, by rfl⟩ : syracuseStep 5249279 = 7873919) B7873919
theorem B368908937 : Blo 428775 368908937 := bstep (se 2 (by rfl) ⟨138340851, by rfl⟩ : syracuseStep 368908937 = 276681703) B276681703
theorem B1842857 : Blo 428775 1842857 := bstep (se 2 (by rfl) ⟨691071, by rfl⟩ : syracuseStep 1842857 = 1382143) B1382143
theorem B1450493 : Blo 428775 1450493 := bstep (se 3 (by rfl) ⟨271967, by rfl⟩ : syracuseStep 1450493 = 543935) B543935
theorem B729769 : Blo 428775 729769 := bstep (se 2 (by rfl) ⟨273663, by rfl⟩ : syracuseStep 729769 = 547327) B547327
theorem B11151269 : Blo 428775 11151269 := bstep (se 4 (by rfl) ⟨1045431, by rfl⟩ : syracuseStep 11151269 = 2090863) B2090863
theorem B1453193 : Blo 428775 1453193 := bstep (se 2 (by rfl) ⟨544947, by rfl⟩ : syracuseStep 1453193 = 1089895) B1089895
theorem B2077787 : Blo 428775 2077787 := bstep (se 1 (by rfl) ⟨1558340, by rfl⟩ : syracuseStep 2077787 = 3116681) B3116681
theorem B18593873 : Blo 428775 18593873 := bstep (se 2 (by rfl) ⟨6972702, by rfl⟩ : syracuseStep 18593873 = 13945405) B13945405
theorem B1458431 : Blo 428775 1458431 := bstep (se 1 (by rfl) ⟨1093823, by rfl⟩ : syracuseStep 1458431 = 2187647) B2187647
theorem B643487 : Blo 428775 643487 := bstep (se 1 (by rfl) ⟨482615, by rfl⟩ : syracuseStep 643487 = 965231) B965231
theorem B1629497 : Blo 428775 1629497 := bstep (se 2 (by rfl) ⟨611061, by rfl⟩ : syracuseStep 1629497 = 1222123) B1222123
theorem B646655 : Blo 428775 646655 := bstep (se 1 (by rfl) ⟨484991, by rfl⟩ : syracuseStep 646655 = 969983) B969983
theorem B647195 : Blo 428775 647195 := bstep (se 1 (by rfl) ⟨485396, by rfl⟩ : syracuseStep 647195 = 970793) B970793
theorem B2450807 : Blo 428775 2450807 := bstep (se 1 (by rfl) ⟨1838105, by rfl⟩ : syracuseStep 2450807 = 3676211) B3676211
theorem B1044521 : Blo 428775 1044521 := bstep (se 2 (by rfl) ⟨391695, by rfl⟩ : syracuseStep 1044521 = 783391) B783391
theorem B1310863 : Blo 428775 1310863 := bstep (se 1 (by rfl) ⟨983147, by rfl⟩ : syracuseStep 1310863 = 1966295) B1966295
theorem B428991 : Blo 428775 428991 := bstep (se 1 (by rfl) ⟨321743, by rfl⟩ : syracuseStep 428991 = 643487) B643487
theorem B1086331 : Blo 428775 1086331 := bstep (se 1 (by rfl) ⟨814748, by rfl⟩ : syracuseStep 1086331 = 1629497) B1629497
theorem B431103 : Blo 428775 431103 := bstep (se 1 (by rfl) ⟨323327, by rfl⟩ : syracuseStep 431103 = 646655) B646655
theorem B431463 : Blo 428775 431463 := bstep (se 1 (by rfl) ⟨323597, by rfl⟩ : syracuseStep 431463 = 647195) B647195
theorem B696347 : Blo 428775 696347 := bstep (se 1 (by rfl) ⟨522260, by rfl⟩ : syracuseStep 696347 = 1044521) B1044521
theorem B1385191 : Blo 428775 1385191 := bstep (se 1 (by rfl) ⟨1038893, by rfl⟩ : syracuseStep 1385191 = 2077787) B2077787
theorem B12395915 : Blo 428775 12395915 := bstep (se 1 (by rfl) ⟨9296936, by rfl⟩ : syracuseStep 12395915 = 18593873) B18593873
theorem B1223399 : Blo 428775 1223399 := bstep (se 1 (by rfl) ⟨917549, by rfl⟩ : syracuseStep 1223399 = 1835099) B1835099
theorem B245939291 : Blo 428775 245939291 := bstep (se 1 (by rfl) ⟨184454468, by rfl⟩ : syracuseStep 245939291 = 368908937) B368908937
theorem B1228571 : Blo 428775 1228571 := bstep (se 1 (by rfl) ⟨921428, by rfl⟩ : syracuseStep 1228571 = 1842857) B1842857
theorem B966995 : Blo 428775 966995 := bstep (se 1 (by rfl) ⟨725246, by rfl⟩ : syracuseStep 966995 = 1450493) B1450493
theorem B968795 : Blo 428775 968795 := bstep (se 1 (by rfl) ⟨726596, by rfl⟩ : syracuseStep 968795 = 1453193) B1453193
theorem B972287 : Blo 428775 972287 := bstep (se 1 (by rfl) ⟨729215, by rfl⟩ : syracuseStep 972287 = 1458431) B1458431
theorem B973025 : Blo 428775 973025 := bstep (se 2 (by rfl) ⟨364884, by rfl⟩ : syracuseStep 973025 = 729769) B729769
theorem B612679 : Blo 428775 612679 := bstep (se 1 (by rfl) ⟨459509, by rfl⟩ : syracuseStep 612679 = 919019) B919019
theorem B3499519 : Blo 428775 3499519 := bstep (se 1 (by rfl) ⟨2624639, by rfl⟩ : syracuseStep 3499519 = 5249279) B5249279
theorem B1633871 : Blo 428775 1633871 := bstep (se 1 (by rfl) ⟨1225403, by rfl⟩ : syracuseStep 1633871 = 2450807) B2450807
theorem B7434179 : Blo 428775 7434179 := bstep (se 1 (by rfl) ⟨5575634, by rfl⟩ : syracuseStep 7434179 = 11151269) B11151269
theorem B464231 : Blo 428775 464231 := bstep (se 1 (by rfl) ⟨348173, by rfl⟩ : syracuseStep 464231 = 696347) B696347
theorem B8263943 : Blo 428775 8263943 := bstep (se 1 (by rfl) ⟨6197957, by rfl⟩ : syracuseStep 8263943 = 12395915) B12395915
theorem B1448441 : Blo 428775 1448441 := bstep (se 2 (by rfl) ⟨543165, by rfl⟩ : syracuseStep 1448441 = 1086331) B1086331
theorem B1089247 : Blo 428775 1089247 := bstep (se 1 (by rfl) ⟨816935, by rfl⟩ : syracuseStep 1089247 = 1633871) B1633871
theorem B4956119 : Blo 428775 4956119 := bstep (se 1 (by rfl) ⟨3717089, by rfl⟩ : syracuseStep 4956119 = 7434179) B7434179
theorem B1747817 : Blo 428775 1747817 := bstep (se 2 (by rfl) ⟨655431, by rfl⟩ : syracuseStep 1747817 = 1310863) B1310863
theorem B4666025 : Blo 428775 4666025 := bstep (se 2 (by rfl) ⟨1749759, by rfl⟩ : syracuseStep 4666025 = 3499519) B3499519
theorem B7387685 : Blo 428775 7387685 := bstep (se 4 (by rfl) ⟨692595, by rfl⟩ : syracuseStep 7387685 = 1385191) B1385191
theorem B163959527 : Blo 428775 163959527 := bstep (se 1 (by rfl) ⟨122969645, by rfl⟩ : syracuseStep 163959527 = 245939291) B245939291
theorem B644663 : Blo 428775 644663 := bstep (se 1 (by rfl) ⟨483497, by rfl⟩ : syracuseStep 644663 = 966995) B966995
theorem B645863 : Blo 428775 645863 := bstep (se 1 (by rfl) ⟨484397, by rfl⟩ : syracuseStep 645863 = 968795) B968795
theorem B648191 : Blo 428775 648191 := bstep (se 1 (by rfl) ⟨486143, by rfl⟩ : syracuseStep 648191 = 972287) B972287
theorem B648683 : Blo 428775 648683 := bstep (se 1 (by rfl) ⟨486512, by rfl⟩ : syracuseStep 648683 = 973025) B973025
theorem B815599 : Blo 428775 815599 := bstep (se 1 (by rfl) ⟨611699, by rfl⟩ : syracuseStep 815599 = 1223399) B1223399
theorem B816905 : Blo 428775 816905 := bstep (se 2 (by rfl) ⟨306339, by rfl⟩ : syracuseStep 816905 = 612679) B612679
theorem B819047 : Blo 428775 819047 := bstep (se 1 (by rfl) ⟨614285, by rfl⟩ : syracuseStep 819047 = 1228571) B1228571
theorem B429775 : Blo 428775 429775 := bstep (se 1 (by rfl) ⟨322331, by rfl⟩ : syracuseStep 429775 = 644663) B644663
theorem B5509295 : Blo 428775 5509295 := bstep (se 1 (by rfl) ⟨4131971, by rfl⟩ : syracuseStep 5509295 = 8263943) B8263943
theorem B430575 : Blo 428775 430575 := bstep (se 1 (by rfl) ⟨322931, by rfl⟩ : syracuseStep 430575 = 645863) B645863
theorem B1087465 : Blo 428775 1087465 := bstep (se 2 (by rfl) ⟨407799, by rfl⟩ : syracuseStep 1087465 = 815599) B815599
theorem B432127 : Blo 428775 432127 := bstep (se 1 (by rfl) ⟨324095, by rfl⟩ : syracuseStep 432127 = 648191) B648191
theorem B432455 : Blo 428775 432455 := bstep (se 1 (by rfl) ⟨324341, by rfl⟩ : syracuseStep 432455 = 648683) B648683
theorem B4925123 : Blo 428775 4925123 := bstep (se 1 (by rfl) ⟨3693842, by rfl⟩ : syracuseStep 4925123 = 7387685) B7387685
theorem B1452329 : Blo 428775 1452329 := bstep (se 2 (by rfl) ⟨544623, by rfl⟩ : syracuseStep 1452329 = 1089247) B1089247
theorem B965627 : Blo 428775 965627 := bstep (se 1 (by rfl) ⟨724220, by rfl⟩ : syracuseStep 965627 = 1448441) B1448441
theorem B2178413 : Blo 428775 2178413 := bstep (se 3 (by rfl) ⟨408452, by rfl⟩ : syracuseStep 2178413 = 816905) B816905
theorem B1165211 : Blo 428775 1165211 := bstep (se 1 (by rfl) ⟨873908, by rfl⟩ : syracuseStep 1165211 = 1747817) B1747817
theorem B546031 : Blo 428775 546031 := bstep (se 1 (by rfl) ⟨409523, by rfl⟩ : syracuseStep 546031 = 819047) B819047
theorem B12442733 : Blo 428775 12442733 := bstep (se 3 (by rfl) ⟨2333012, by rfl⟩ : syracuseStep 12442733 = 4666025) B4666025
theorem B109306351 : Blo 428775 109306351 := bstep (se 1 (by rfl) ⟨81979763, by rfl⟩ : syracuseStep 109306351 = 163959527) B163959527
theorem B1237949 : Blo 428775 1237949 := bstep (se 3 (by rfl) ⟨232115, by rfl⟩ : syracuseStep 1237949 = 464231) B464231
theorem B3304079 : Blo 428775 3304079 := bstep (se 1 (by rfl) ⟨2478059, by rfl⟩ : syracuseStep 3304079 = 4956119) B4956119
theorem B3672863 : Blo 428775 3672863 := bstep (se 1 (by rfl) ⟨2754647, by rfl⟩ : syracuseStep 3672863 = 5509295) B5509295
theorem B8295155 : Blo 428775 8295155 := bstep (se 1 (by rfl) ⟨6221366, by rfl⟩ : syracuseStep 8295155 = 12442733) B12442733
theorem B825299 : Blo 428775 825299 := bstep (se 1 (by rfl) ⟨618974, by rfl⟩ : syracuseStep 825299 = 1237949) B1237949
theorem B3283415 : Blo 428775 3283415 := bstep (se 1 (by rfl) ⟨2462561, by rfl⟩ : syracuseStep 3283415 = 4925123) B4925123
theorem B728041 : Blo 428775 728041 := bstep (se 2 (by rfl) ⟨273015, by rfl⟩ : syracuseStep 728041 = 546031) B546031
theorem B2202719 : Blo 428775 2202719 := bstep (se 1 (by rfl) ⟨1652039, by rfl⟩ : syracuseStep 2202719 = 3304079) B3304079
theorem B1449953 : Blo 428775 1449953 := bstep (se 2 (by rfl) ⟨543732, by rfl⟩ : syracuseStep 1449953 = 1087465) B1087465
theorem B1452275 : Blo 428775 1452275 := bstep (se 1 (by rfl) ⟨1089206, by rfl⟩ : syracuseStep 1452275 = 2178413) B2178413
theorem B968219 : Blo 428775 968219 := bstep (se 1 (by rfl) ⟨726164, by rfl⟩ : syracuseStep 968219 = 1452329) B1452329
theorem B643751 : Blo 428775 643751 := bstep (se 1 (by rfl) ⟨482813, by rfl⟩ : syracuseStep 643751 = 965627) B965627
theorem B145741801 : Blo 428775 145741801 := bstep (se 2 (by rfl) ⟨54653175, by rfl⟩ : syracuseStep 145741801 = 109306351) B109306351
theorem B776807 : Blo 428775 776807 := bstep (se 1 (by rfl) ⟨582605, by rfl⟩ : syracuseStep 776807 = 1165211) B1165211
theorem B429167 : Blo 428775 429167 := bstep (se 1 (by rfl) ⟨321875, by rfl⟩ : syracuseStep 429167 = 643751) B643751
theorem B194322401 : Blo 428775 194322401 := bstep (se 2 (by rfl) ⟨72870900, by rfl⟩ : syracuseStep 194322401 = 145741801) B145741801
theorem B5873917 : Blo 428775 5873917 := bstep (se 3 (by rfl) ⟨1101359, by rfl⟩ : syracuseStep 5873917 = 2202719) B2202719
theorem B966635 : Blo 428775 966635 := bstep (se 1 (by rfl) ⟨724976, by rfl⟩ : syracuseStep 966635 = 1449953) B1449953
theorem B968183 : Blo 428775 968183 := bstep (se 1 (by rfl) ⟨726137, by rfl⟩ : syracuseStep 968183 = 1452275) B1452275
theorem B970721 : Blo 428775 970721 := bstep (se 2 (by rfl) ⟨364020, by rfl⟩ : syracuseStep 970721 = 728041) B728041
theorem B645479 : Blo 428775 645479 := bstep (se 1 (by rfl) ⟨484109, by rfl⟩ : syracuseStep 645479 = 968219) B968219
theorem B2448575 : Blo 428775 2448575 := bstep (se 1 (by rfl) ⟨1836431, by rfl⟩ : syracuseStep 2448575 = 3672863) B3672863
theorem B5530103 : Blo 428775 5530103 := bstep (se 1 (by rfl) ⟨4147577, by rfl⟩ : syracuseStep 5530103 = 8295155) B8295155
theorem B550199 : Blo 428775 550199 := bstep (se 1 (by rfl) ⟨412649, by rfl⟩ : syracuseStep 550199 = 825299) B825299
theorem B2188943 : Blo 428775 2188943 := bstep (se 1 (by rfl) ⟨1641707, by rfl⟩ : syracuseStep 2188943 = 3283415) B3283415
theorem B517871 : Blo 428775 517871 := bstep (se 1 (by rfl) ⟨388403, by rfl⟩ : syracuseStep 517871 = 776807) B776807
theorem B7831889 : Blo 428775 7831889 := bstep (se 2 (by rfl) ⟨2936958, by rfl⟩ : syracuseStep 7831889 = 5873917) B5873917
theorem B430319 : Blo 428775 430319 := bstep (se 1 (by rfl) ⟨322739, by rfl⟩ : syracuseStep 430319 = 645479) B645479
theorem B1380989 : Blo 428775 1380989 := bstep (se 3 (by rfl) ⟨258935, by rfl⟩ : syracuseStep 1380989 = 517871) B517871
theorem B129548267 : Blo 428775 129548267 := bstep (se 1 (by rfl) ⟨97161200, by rfl⟩ : syracuseStep 129548267 = 194322401) B194322401
theorem B3686735 : Blo 428775 3686735 := bstep (se 1 (by rfl) ⟨2765051, by rfl⟩ : syracuseStep 3686735 = 5530103) B5530103
theorem B1459295 : Blo 428775 1459295 := bstep (se 1 (by rfl) ⟨1094471, by rfl⟩ : syracuseStep 1459295 = 2188943) B2188943
theorem B644423 : Blo 428775 644423 := bstep (se 1 (by rfl) ⟨483317, by rfl⟩ : syracuseStep 644423 = 966635) B966635
theorem B645455 : Blo 428775 645455 := bstep (se 1 (by rfl) ⟨484091, by rfl⟩ : syracuseStep 645455 = 968183) B968183
theorem B647147 : Blo 428775 647147 := bstep (se 1 (by rfl) ⟨485360, by rfl⟩ : syracuseStep 647147 = 970721) B970721
theorem B1467197 : Blo 428775 1467197 := bstep (se 3 (by rfl) ⟨275099, by rfl⟩ : syracuseStep 1467197 = 550199) B550199
theorem B1632383 : Blo 428775 1632383 := bstep (se 1 (by rfl) ⟨1224287, by rfl⟩ : syracuseStep 1632383 = 2448575) B2448575
theorem B2457823 : Blo 428775 2457823 := bstep (se 1 (by rfl) ⟨1843367, by rfl⟩ : syracuseStep 2457823 = 3686735) B3686735
theorem B920659 : Blo 428775 920659 := bstep (se 1 (by rfl) ⟨690494, by rfl⟩ : syracuseStep 920659 = 1380989) B1380989
theorem B429615 : Blo 428775 429615 := bstep (se 1 (by rfl) ⟨322211, by rfl⟩ : syracuseStep 429615 = 644423) B644423
theorem B430303 : Blo 428775 430303 := bstep (se 1 (by rfl) ⟨322727, by rfl⟩ : syracuseStep 430303 = 645455) B645455
theorem B431431 : Blo 428775 431431 := bstep (se 1 (by rfl) ⟨323573, by rfl⟩ : syracuseStep 431431 = 647147) B647147
theorem B1088255 : Blo 428775 1088255 := bstep (se 1 (by rfl) ⟨816191, by rfl⟩ : syracuseStep 1088255 = 1632383) B1632383
theorem B5221259 : Blo 428775 5221259 := bstep (se 1 (by rfl) ⟨3915944, by rfl⟩ : syracuseStep 5221259 = 7831889) B7831889
theorem B86365511 : Blo 428775 86365511 := bstep (se 1 (by rfl) ⟨64774133, by rfl⟩ : syracuseStep 86365511 = 129548267) B129548267
theorem B972863 : Blo 428775 972863 := bstep (se 1 (by rfl) ⟨729647, by rfl⟩ : syracuseStep 972863 = 1459295) B1459295
theorem B978131 : Blo 428775 978131 := bstep (se 1 (by rfl) ⟨733598, by rfl⟩ : syracuseStep 978131 = 1467197) B1467197
theorem B3277097 : Blo 428775 3277097 := bstep (se 2 (by rfl) ⟨1228911, by rfl⟩ : syracuseStep 3277097 = 2457823) B2457823
theorem B57577007 : Blo 428775 57577007 := bstep (se 1 (by rfl) ⟨43182755, by rfl⟩ : syracuseStep 57577007 = 86365511) B86365511
theorem B725503 : Blo 428775 725503 := bstep (se 1 (by rfl) ⟨544127, by rfl⟩ : syracuseStep 725503 = 1088255) B1088255
theorem B3480839 : Blo 428775 3480839 := bstep (se 1 (by rfl) ⟨2610629, by rfl⟩ : syracuseStep 3480839 = 5221259) B5221259
theorem B1227545 : Blo 428775 1227545 := bstep (se 2 (by rfl) ⟨460329, by rfl⟩ : syracuseStep 1227545 = 920659) B920659
theorem B648575 : Blo 428775 648575 := bstep (se 1 (by rfl) ⟨486431, by rfl⟩ : syracuseStep 648575 = 972863) B972863
theorem B652087 : Blo 428775 652087 := bstep (se 1 (by rfl) ⟨489065, by rfl⟩ : syracuseStep 652087 = 978131) B978131
theorem B432383 : Blo 428775 432383 := bstep (se 1 (by rfl) ⟨324287, by rfl⟩ : syracuseStep 432383 = 648575) B648575
theorem B38384671 : Blo 428775 38384671 := bstep (se 1 (by rfl) ⟨28788503, by rfl⟩ : syracuseStep 38384671 = 57577007) B57577007
theorem B967337 : Blo 428775 967337 := bstep (se 2 (by rfl) ⟨362751, by rfl⟩ : syracuseStep 967337 = 725503) B725503
theorem B869449 : Blo 428775 869449 := bstep (se 2 (by rfl) ⟨326043, by rfl⟩ : syracuseStep 869449 = 652087) B652087
theorem B2184731 : Blo 428775 2184731 := bstep (se 1 (by rfl) ⟨1638548, by rfl⟩ : syracuseStep 2184731 = 3277097) B3277097
theorem B2320559 : Blo 428775 2320559 := bstep (se 1 (by rfl) ⟨1740419, by rfl⟩ : syracuseStep 2320559 = 3480839) B3480839
theorem B818363 : Blo 428775 818363 := bstep (se 1 (by rfl) ⟨613772, by rfl⟩ : syracuseStep 818363 = 1227545) B1227545
theorem B1547039 : Blo 428775 1547039 := bstep (se 1 (by rfl) ⟨1160279, by rfl⟩ : syracuseStep 1547039 = 2320559) B2320559
theorem B1159265 : Blo 428775 1159265 := bstep (se 2 (by rfl) ⟨434724, by rfl⟩ : syracuseStep 1159265 = 869449) B869449
theorem B1456487 : Blo 428775 1456487 := bstep (se 1 (by rfl) ⟨1092365, by rfl⟩ : syracuseStep 1456487 = 2184731) B2184731
theorem B2182301 : Blo 428775 2182301 := bstep (se 3 (by rfl) ⟨409181, by rfl⟩ : syracuseStep 2182301 = 818363) B818363
theorem B644891 : Blo 428775 644891 := bstep (se 1 (by rfl) ⟨483668, by rfl⟩ : syracuseStep 644891 = 967337) B967337
theorem B51179561 : Blo 428775 51179561 := bstep (se 2 (by rfl) ⟨19192335, by rfl⟩ : syracuseStep 51179561 = 38384671) B38384671
theorem B429927 : Blo 428775 429927 := bstep (se 1 (by rfl) ⟨322445, by rfl⟩ : syracuseStep 429927 = 644891) B644891
theorem B34119707 : Blo 428775 34119707 := bstep (se 1 (by rfl) ⟨25589780, by rfl⟩ : syracuseStep 34119707 = 51179561) B51179561
theorem B1454867 : Blo 428775 1454867 := bstep (se 1 (by rfl) ⟨1091150, by rfl⟩ : syracuseStep 1454867 = 2182301) B2182301
theorem B1031359 : Blo 428775 1031359 := bstep (se 1 (by rfl) ⟨773519, by rfl⟩ : syracuseStep 1031359 = 1547039) B1547039
theorem B772843 : Blo 428775 772843 := bstep (se 1 (by rfl) ⟨579632, by rfl⟩ : syracuseStep 772843 = 1159265) B1159265
theorem B970991 : Blo 428775 970991 := bstep (se 1 (by rfl) ⟨728243, by rfl⟩ : syracuseStep 970991 = 1456487) B1456487
theorem B1030457 : Blo 428775 1030457 := bstep (se 2 (by rfl) ⟨386421, by rfl⟩ : syracuseStep 1030457 = 772843) B772843
theorem B969911 : Blo 428775 969911 := bstep (se 1 (by rfl) ⟨727433, by rfl⟩ : syracuseStep 969911 = 1454867) B1454867
theorem B90985885 : Blo 428775 90985885 := bstep (se 3 (by rfl) ⟨17059853, by rfl⟩ : syracuseStep 90985885 = 34119707) B34119707
theorem B647327 : Blo 428775 647327 := bstep (se 1 (by rfl) ⟨485495, by rfl⟩ : syracuseStep 647327 = 970991) B970991
theorem B1375145 : Blo 428775 1375145 := bstep (se 2 (by rfl) ⟨515679, by rfl⟩ : syracuseStep 1375145 = 1031359) B1031359
theorem B431551 : Blo 428775 431551 := bstep (se 1 (by rfl) ⟨323663, by rfl⟩ : syracuseStep 431551 = 647327) B647327
theorem B646607 : Blo 428775 646607 := bstep (se 1 (by rfl) ⟨484955, by rfl⟩ : syracuseStep 646607 = 969911) B969911
theorem B485258053 : Blo 428775 485258053 := bstep (se 4 (by rfl) ⟨45492942, by rfl⟩ : syracuseStep 485258053 = 90985885) B90985885
theorem B686971 : Blo 428775 686971 := bstep (se 1 (by rfl) ⟨515228, by rfl⟩ : syracuseStep 686971 = 1030457) B1030457
theorem B916763 : Blo 428775 916763 := bstep (se 1 (by rfl) ⟨687572, by rfl⟩ : syracuseStep 916763 = 1375145) B1375145
theorem B431071 : Blo 428775 431071 := bstep (se 1 (by rfl) ⟨323303, by rfl⟩ : syracuseStep 431071 = 646607) B646607
theorem B647010737 : Blo 428775 647010737 := bstep (se 2 (by rfl) ⟨242629026, by rfl⟩ : syracuseStep 647010737 = 485258053) B485258053
theorem B2444701 : Blo 428775 2444701 := bstep (se 3 (by rfl) ⟨458381, by rfl⟩ : syracuseStep 2444701 = 916763) B916763
theorem B915961 : Blo 428775 915961 := bstep (se 2 (by rfl) ⟨343485, by rfl⟩ : syracuseStep 915961 = 686971) B686971
theorem B1221281 : Blo 428775 1221281 := bstep (se 2 (by rfl) ⟨457980, by rfl⟩ : syracuseStep 1221281 = 915961) B915961
theorem B431340491 : Blo 428775 431340491 := bstep (se 1 (by rfl) ⟨323505368, by rfl⟩ : syracuseStep 431340491 = 647010737) B647010737
theorem B3259601 : Blo 428775 3259601 := bstep (se 2 (by rfl) ⟨1222350, by rfl⟩ : syracuseStep 3259601 = 2444701) B2444701
theorem B2173067 : Blo 428775 2173067 := bstep (se 1 (by rfl) ⟨1629800, by rfl⟩ : syracuseStep 2173067 = 3259601) B3259601
theorem B287560327 : Blo 428775 287560327 := bstep (se 1 (by rfl) ⟨215670245, by rfl⟩ : syracuseStep 287560327 = 431340491) B431340491
theorem B814187 : Blo 428775 814187 := bstep (se 1 (by rfl) ⟨610640, by rfl⟩ : syracuseStep 814187 = 1221281) B1221281
theorem B1448711 : Blo 428775 1448711 := bstep (se 1 (by rfl) ⟨1086533, by rfl⟩ : syracuseStep 1448711 = 2173067) B2173067
theorem B542791 : Blo 428775 542791 := bstep (se 1 (by rfl) ⟨407093, by rfl⟩ : syracuseStep 542791 = 814187) B814187
theorem B383413769 : Blo 428775 383413769 := bstep (se 2 (by rfl) ⟨143780163, by rfl⟩ : syracuseStep 383413769 = 287560327) B287560327
theorem B723721 : Blo 428775 723721 := bstep (se 2 (by rfl) ⟨271395, by rfl⟩ : syracuseStep 723721 = 542791) B542791
theorem B965807 : Blo 428775 965807 := bstep (se 1 (by rfl) ⟨724355, by rfl⟩ : syracuseStep 965807 = 1448711) B1448711
theorem B255609179 : Blo 428775 255609179 := bstep (se 1 (by rfl) ⟨191706884, by rfl⟩ : syracuseStep 255609179 = 383413769) B383413769
theorem B170406119 : Blo 428775 170406119 := bstep (se 1 (by rfl) ⟨127804589, by rfl⟩ : syracuseStep 170406119 = 255609179) B255609179
theorem B964961 : Blo 428775 964961 := bstep (se 2 (by rfl) ⟨361860, by rfl⟩ : syracuseStep 964961 = 723721) B723721
theorem B643871 : Blo 428775 643871 := bstep (se 1 (by rfl) ⟨482903, by rfl⟩ : syracuseStep 643871 = 965807) B965807
theorem B429247 : Blo 428775 429247 := bstep (se 1 (by rfl) ⟨321935, by rfl⟩ : syracuseStep 429247 = 643871) B643871
theorem B643307 : Blo 428775 643307 := bstep (se 1 (by rfl) ⟨482480, by rfl⟩ : syracuseStep 643307 = 964961) B964961
theorem B454416317 : Blo 428775 454416317 := bstep (se 3 (by rfl) ⟨85203059, by rfl⟩ : syracuseStep 454416317 = 170406119) B170406119
theorem B428871 : Blo 428775 428871 := bstep (se 1 (by rfl) ⟨321653, by rfl⟩ : syracuseStep 428871 = 643307) B643307
theorem B302944211 : Blo 428775 302944211 := bstep (se 1 (by rfl) ⟨227208158, by rfl⟩ : syracuseStep 302944211 = 454416317) B454416317
theorem B201962807 : Blo 428775 201962807 := bstep (se 1 (by rfl) ⟨151472105, by rfl⟩ : syracuseStep 201962807 = 302944211) B302944211
theorem B134641871 : Blo 428775 134641871 := bstep (se 1 (by rfl) ⟨100981403, by rfl⟩ : syracuseStep 134641871 = 201962807) B201962807
theorem B89761247 : Blo 428775 89761247 := bstep (se 1 (by rfl) ⟨67320935, by rfl⟩ : syracuseStep 89761247 = 134641871) B134641871
theorem B59840831 : Blo 428775 59840831 := bstep (se 1 (by rfl) ⟨44880623, by rfl⟩ : syracuseStep 59840831 = 89761247) B89761247
theorem B39893887 : Blo 428775 39893887 := bstep (se 1 (by rfl) ⟨29920415, by rfl⟩ : syracuseStep 39893887 = 59840831) B59840831
theorem B53191849 : Blo 428775 53191849 := bstep (se 2 (by rfl) ⟨19946943, by rfl⟩ : syracuseStep 53191849 = 39893887) B39893887
theorem B70922465 : Blo 428775 70922465 := bstep (se 2 (by rfl) ⟨26595924, by rfl⟩ : syracuseStep 70922465 = 53191849) B53191849
theorem B47281643 : Blo 428775 47281643 := bstep (se 1 (by rfl) ⟨35461232, by rfl⟩ : syracuseStep 47281643 = 70922465) B70922465
theorem B31521095 : Blo 428775 31521095 := bstep (se 1 (by rfl) ⟨23640821, by rfl⟩ : syracuseStep 31521095 = 47281643) B47281643
theorem B21014063 : Blo 428775 21014063 := bstep (se 1 (by rfl) ⟨15760547, by rfl⟩ : syracuseStep 21014063 = 31521095) B31521095
theorem B14009375 : Blo 428775 14009375 := bstep (se 1 (by rfl) ⟨10507031, by rfl⟩ : syracuseStep 14009375 = 21014063) B21014063
theorem B9339583 : Blo 428775 9339583 := bstep (se 1 (by rfl) ⟨7004687, by rfl⟩ : syracuseStep 9339583 = 14009375) B14009375
theorem B12452777 : Blo 428775 12452777 := bstep (se 2 (by rfl) ⟨4669791, by rfl⟩ : syracuseStep 12452777 = 9339583) B9339583
theorem B8301851 : Blo 428775 8301851 := bstep (se 1 (by rfl) ⟨6226388, by rfl⟩ : syracuseStep 8301851 = 12452777) B12452777
theorem B5534567 : Blo 428775 5534567 := bstep (se 1 (by rfl) ⟨4150925, by rfl⟩ : syracuseStep 5534567 = 8301851) B8301851
theorem B3689711 : Blo 428775 3689711 := bstep (se 1 (by rfl) ⟨2767283, by rfl⟩ : syracuseStep 3689711 = 5534567) B5534567
theorem B2459807 : Blo 428775 2459807 := bstep (se 1 (by rfl) ⟨1844855, by rfl⟩ : syracuseStep 2459807 = 3689711) B3689711
theorem B1639871 : Blo 428775 1639871 := bstep (se 1 (by rfl) ⟨1229903, by rfl⟩ : syracuseStep 1639871 = 2459807) B2459807
theorem B1093247 : Blo 428775 1093247 := bstep (se 1 (by rfl) ⟨819935, by rfl⟩ : syracuseStep 1093247 = 1639871) B1639871
theorem B728831 : Blo 428775 728831 := bstep (se 1 (by rfl) ⟨546623, by rfl⟩ : syracuseStep 728831 = 1093247) B1093247
theorem B485887 : Blo 428775 485887 := bstep (se 1 (by rfl) ⟨364415, by rfl⟩ : syracuseStep 485887 = 728831) B728831
theorem B647849 : Blo 428775 647849 := bstep (se 2 (by rfl) ⟨242943, by rfl⟩ : syracuseStep 647849 = 485887) B485887
theorem B431899 : Blo 428775 431899 := bstep (se 1 (by rfl) ⟨323924, by rfl⟩ : syracuseStep 431899 = 647849) B647849

theorem C0 (j : ℕ) (h1 : 107193 ≤ j) (h2 : j ≤ 107892) : Blo 428775 (4 * j + 3) := by
  interval_cases j
  · exact B428775
  · exact B428779
  · exact B428783
  · exact B428787
  · exact B428791
  · exact B428795
  · exact B428799
  · exact B428803
  · exact B428807
  · exact B428811
  · exact B428815
  · exact B428819
  · exact B428823
  · exact B428827
  · exact B428831
  · exact B428835
  · exact B428839
  · exact B428843
  · exact B428847
  · exact B428851
  · exact B428855
  · exact B428859
  · exact B428863
  · exact B428867
  · exact B428871
  · exact B428875
  · exact B428879
  · exact B428883
  · exact B428887
  · exact B428891
  · exact B428895
  · exact B428899
  · exact B428903
  · exact B428907
  · exact B428911
  · exact B428915
  · exact B428919
  · exact B428923
  · exact B428927
  · exact B428931
  · exact B428935
  · exact B428939
  · exact B428943
  · exact B428947
  · exact B428951
  · exact B428955
  · exact B428959
  · exact B428963
  · exact B428967
  · exact B428971
  · exact B428975
  · exact B428979
  · exact B428983
  · exact B428987
  · exact B428991
  · exact B428995
  · exact B428999
  · exact B429003
  · exact B429007
  · exact B429011
  · exact B429015
  · exact B429019
  · exact B429023
  · exact B429027
  · exact B429031
  · exact B429035
  · exact B429039
  · exact B429043
  · exact B429047
  · exact B429051
  · exact B429055
  · exact B429059
  · exact B429063
  · exact B429067
  · exact B429071
  · exact B429075
  · exact B429079
  · exact B429083
  · exact B429087
  · exact B429091
  · exact B429095
  · exact B429099
  · exact B429103
  · exact B429107
  · exact B429111
  · exact B429115
  · exact B429119
  · exact B429123
  · exact B429127
  · exact B429131
  · exact B429135
  · exact B429139
  · exact B429143
  · exact B429147
  · exact B429151
  · exact B429155
  · exact B429159
  · exact B429163
  · exact B429167
  · exact B429171
  · exact B429175
  · exact B429179
  · exact B429183
  · exact B429187
  · exact B429191
  · exact B429195
  · exact B429199
  · exact B429203
  · exact B429207
  · exact B429211
  · exact B429215
  · exact B429219
  · exact B429223
  · exact B429227
  · exact B429231
  · exact B429235
  · exact B429239
  · exact B429243
  · exact B429247
  · exact B429251
  · exact B429255
  · exact B429259
  · exact B429263
  · exact B429267
  · exact B429271
  · exact B429275
  · exact B429279
  · exact B429283
  · exact B429287
  · exact B429291
  · exact B429295
  · exact B429299
  · exact B429303
  · exact B429307
  · exact B429311
  · exact B429315
  · exact B429319
  · exact B429323
  · exact B429327
  · exact B429331
  · exact B429335
  · exact B429339
  · exact B429343
  · exact B429347
  · exact B429351
  · exact B429355
  · exact B429359
  · exact B429363
  · exact B429367
  · exact B429371
  · exact B429375
  · exact B429379
  · exact B429383
  · exact B429387
  · exact B429391
  · exact B429395
  · exact B429399
  · exact B429403
  · exact B429407
  · exact B429411
  · exact B429415
  · exact B429419
  · exact B429423
  · exact B429427
  · exact B429431
  · exact B429435
  · exact B429439
  · exact B429443
  · exact B429447
  · exact B429451
  · exact B429455
  · exact B429459
  · exact B429463
  · exact B429467
  · exact B429471
  · exact B429475
  · exact B429479
  · exact B429483
  · exact B429487
  · exact B429491
  · exact B429495
  · exact B429499
  · exact B429503
  · exact B429507
  · exact B429511
  · exact B429515
  · exact B429519
  · exact B429523
  · exact B429527
  · exact B429531
  · exact B429535
  · exact B429539
  · exact B429543
  · exact B429547
  · exact B429551
  · exact B429555
  · exact B429559
  · exact B429563
  · exact B429567
  · exact B429571
  · exact B429575
  · exact B429579
  · exact B429583
  · exact B429587
  · exact B429591
  · exact B429595
  · exact B429599
  · exact B429603
  · exact B429607
  · exact B429611
  · exact B429615
  · exact B429619
  · exact B429623
  · exact B429627
  · exact B429631
  · exact B429635
  · exact B429639
  · exact B429643
  · exact B429647
  · exact B429651
  · exact B429655
  · exact B429659
  · exact B429663
  · exact B429667
  · exact B429671
  · exact B429675
  · exact B429679
  · exact B429683
  · exact B429687
  · exact B429691
  · exact B429695
  · exact B429699
  · exact B429703
  · exact B429707
  · exact B429711
  · exact B429715
  · exact B429719
  · exact B429723
  · exact B429727
  · exact B429731
  · exact B429735
  · exact B429739
  · exact B429743
  · exact B429747
  · exact B429751
  · exact B429755
  · exact B429759
  · exact B429763
  · exact B429767
  · exact B429771
  · exact B429775
  · exact B429779
  · exact B429783
  · exact B429787
  · exact B429791
  · exact B429795
  · exact B429799
  · exact B429803
  · exact B429807
  · exact B429811
  · exact B429815
  · exact B429819
  · exact B429823
  · exact B429827
  · exact B429831
  · exact B429835
  · exact B429839
  · exact B429843
  · exact B429847
  · exact B429851
  · exact B429855
  · exact B429859
  · exact B429863
  · exact B429867
  · exact B429871
  · exact B429875
  · exact B429879
  · exact B429883
  · exact B429887
  · exact B429891
  · exact B429895
  · exact B429899
  · exact B429903
  · exact B429907
  · exact B429911
  · exact B429915
  · exact B429919
  · exact B429923
  · exact B429927
  · exact B429931
  · exact B429935
  · exact B429939
  · exact B429943
  · exact B429947
  · exact B429951
  · exact B429955
  · exact B429959
  · exact B429963
  · exact B429967
  · exact B429971
  · exact B429975
  · exact B429979
  · exact B429983
  · exact B429987
  · exact B429991
  · exact B429995
  · exact B429999
  · exact B430003
  · exact B430007
  · exact B430011
  · exact B430015
  · exact B430019
  · exact B430023
  · exact B430027
  · exact B430031
  · exact B430035
  · exact B430039
  · exact B430043
  · exact B430047
  · exact B430051
  · exact B430055
  · exact B430059
  · exact B430063
  · exact B430067
  · exact B430071
  · exact B430075
  · exact B430079
  · exact B430083
  · exact B430087
  · exact B430091
  · exact B430095
  · exact B430099
  · exact B430103
  · exact B430107
  · exact B430111
  · exact B430115
  · exact B430119
  · exact B430123
  · exact B430127
  · exact B430131
  · exact B430135
  · exact B430139
  · exact B430143
  · exact B430147
  · exact B430151
  · exact B430155
  · exact B430159
  · exact B430163
  · exact B430167
  · exact B430171
  · exact B430175
  · exact B430179
  · exact B430183
  · exact B430187
  · exact B430191
  · exact B430195
  · exact B430199
  · exact B430203
  · exact B430207
  · exact B430211
  · exact B430215
  · exact B430219
  · exact B430223
  · exact B430227
  · exact B430231
  · exact B430235
  · exact B430239
  · exact B430243
  · exact B430247
  · exact B430251
  · exact B430255
  · exact B430259
  · exact B430263
  · exact B430267
  · exact B430271
  · exact B430275
  · exact B430279
  · exact B430283
  · exact B430287
  · exact B430291
  · exact B430295
  · exact B430299
  · exact B430303
  · exact B430307
  · exact B430311
  · exact B430315
  · exact B430319
  · exact B430323
  · exact B430327
  · exact B430331
  · exact B430335
  · exact B430339
  · exact B430343
  · exact B430347
  · exact B430351
  · exact B430355
  · exact B430359
  · exact B430363
  · exact B430367
  · exact B430371
  · exact B430375
  · exact B430379
  · exact B430383
  · exact B430387
  · exact B430391
  · exact B430395
  · exact B430399
  · exact B430403
  · exact B430407
  · exact B430411
  · exact B430415
  · exact B430419
  · exact B430423
  · exact B430427
  · exact B430431
  · exact B430435
  · exact B430439
  · exact B430443
  · exact B430447
  · exact B430451
  · exact B430455
  · exact B430459
  · exact B430463
  · exact B430467
  · exact B430471
  · exact B430475
  · exact B430479
  · exact B430483
  · exact B430487
  · exact B430491
  · exact B430495
  · exact B430499
  · exact B430503
  · exact B430507
  · exact B430511
  · exact B430515
  · exact B430519
  · exact B430523
  · exact B430527
  · exact B430531
  · exact B430535
  · exact B430539
  · exact B430543
  · exact B430547
  · exact B430551
  · exact B430555
  · exact B430559
  · exact B430563
  · exact B430567
  · exact B430571
  · exact B430575
  · exact B430579
  · exact B430583
  · exact B430587
  · exact B430591
  · exact B430595
  · exact B430599
  · exact B430603
  · exact B430607
  · exact B430611
  · exact B430615
  · exact B430619
  · exact B430623
  · exact B430627
  · exact B430631
  · exact B430635
  · exact B430639
  · exact B430643
  · exact B430647
  · exact B430651
  · exact B430655
  · exact B430659
  · exact B430663
  · exact B430667
  · exact B430671
  · exact B430675
  · exact B430679
  · exact B430683
  · exact B430687
  · exact B430691
  · exact B430695
  · exact B430699
  · exact B430703
  · exact B430707
  · exact B430711
  · exact B430715
  · exact B430719
  · exact B430723
  · exact B430727
  · exact B430731
  · exact B430735
  · exact B430739
  · exact B430743
  · exact B430747
  · exact B430751
  · exact B430755
  · exact B430759
  · exact B430763
  · exact B430767
  · exact B430771
  · exact B430775
  · exact B430779
  · exact B430783
  · exact B430787
  · exact B430791
  · exact B430795
  · exact B430799
  · exact B430803
  · exact B430807
  · exact B430811
  · exact B430815
  · exact B430819
  · exact B430823
  · exact B430827
  · exact B430831
  · exact B430835
  · exact B430839
  · exact B430843
  · exact B430847
  · exact B430851
  · exact B430855
  · exact B430859
  · exact B430863
  · exact B430867
  · exact B430871
  · exact B430875
  · exact B430879
  · exact B430883
  · exact B430887
  · exact B430891
  · exact B430895
  · exact B430899
  · exact B430903
  · exact B430907
  · exact B430911
  · exact B430915
  · exact B430919
  · exact B430923
  · exact B430927
  · exact B430931
  · exact B430935
  · exact B430939
  · exact B430943
  · exact B430947
  · exact B430951
  · exact B430955
  · exact B430959
  · exact B430963
  · exact B430967
  · exact B430971
  · exact B430975
  · exact B430979
  · exact B430983
  · exact B430987
  · exact B430991
  · exact B430995
  · exact B430999
  · exact B431003
  · exact B431007
  · exact B431011
  · exact B431015
  · exact B431019
  · exact B431023
  · exact B431027
  · exact B431031
  · exact B431035
  · exact B431039
  · exact B431043
  · exact B431047
  · exact B431051
  · exact B431055
  · exact B431059
  · exact B431063
  · exact B431067
  · exact B431071
  · exact B431075
  · exact B431079
  · exact B431083
  · exact B431087
  · exact B431091
  · exact B431095
  · exact B431099
  · exact B431103
  · exact B431107
  · exact B431111
  · exact B431115
  · exact B431119
  · exact B431123
  · exact B431127
  · exact B431131
  · exact B431135
  · exact B431139
  · exact B431143
  · exact B431147
  · exact B431151
  · exact B431155
  · exact B431159
  · exact B431163
  · exact B431167
  · exact B431171
  · exact B431175
  · exact B431179
  · exact B431183
  · exact B431187
  · exact B431191
  · exact B431195
  · exact B431199
  · exact B431203
  · exact B431207
  · exact B431211
  · exact B431215
  · exact B431219
  · exact B431223
  · exact B431227
  · exact B431231
  · exact B431235
  · exact B431239
  · exact B431243
  · exact B431247
  · exact B431251
  · exact B431255
  · exact B431259
  · exact B431263
  · exact B431267
  · exact B431271
  · exact B431275
  · exact B431279
  · exact B431283
  · exact B431287
  · exact B431291
  · exact B431295
  · exact B431299
  · exact B431303
  · exact B431307
  · exact B431311
  · exact B431315
  · exact B431319
  · exact B431323
  · exact B431327
  · exact B431331
  · exact B431335
  · exact B431339
  · exact B431343
  · exact B431347
  · exact B431351
  · exact B431355
  · exact B431359
  · exact B431363
  · exact B431367
  · exact B431371
  · exact B431375
  · exact B431379
  · exact B431383
  · exact B431387
  · exact B431391
  · exact B431395
  · exact B431399
  · exact B431403
  · exact B431407
  · exact B431411
  · exact B431415
  · exact B431419
  · exact B431423
  · exact B431427
  · exact B431431
  · exact B431435
  · exact B431439
  · exact B431443
  · exact B431447
  · exact B431451
  · exact B431455
  · exact B431459
  · exact B431463
  · exact B431467
  · exact B431471
  · exact B431475
  · exact B431479
  · exact B431483
  · exact B431487
  · exact B431491
  · exact B431495
  · exact B431499
  · exact B431503
  · exact B431507
  · exact B431511
  · exact B431515
  · exact B431519
  · exact B431523
  · exact B431527
  · exact B431531
  · exact B431535
  · exact B431539
  · exact B431543
  · exact B431547
  · exact B431551
  · exact B431555
  · exact B431559
  · exact B431563
  · exact B431567
  · exact B431571

theorem C1 (j : ℕ) (h1 : 107893 ≤ j) (h2 : j ≤ 108193) : Blo 428775 (4 * j + 3) := by
  interval_cases j
  · exact B431575
  · exact B431579
  · exact B431583
  · exact B431587
  · exact B431591
  · exact B431595
  · exact B431599
  · exact B431603
  · exact B431607
  · exact B431611
  · exact B431615
  · exact B431619
  · exact B431623
  · exact B431627
  · exact B431631
  · exact B431635
  · exact B431639
  · exact B431643
  · exact B431647
  · exact B431651
  · exact B431655
  · exact B431659
  · exact B431663
  · exact B431667
  · exact B431671
  · exact B431675
  · exact B431679
  · exact B431683
  · exact B431687
  · exact B431691
  · exact B431695
  · exact B431699
  · exact B431703
  · exact B431707
  · exact B431711
  · exact B431715
  · exact B431719
  · exact B431723
  · exact B431727
  · exact B431731
  · exact B431735
  · exact B431739
  · exact B431743
  · exact B431747
  · exact B431751
  · exact B431755
  · exact B431759
  · exact B431763
  · exact B431767
  · exact B431771
  · exact B431775
  · exact B431779
  · exact B431783
  · exact B431787
  · exact B431791
  · exact B431795
  · exact B431799
  · exact B431803
  · exact B431807
  · exact B431811
  · exact B431815
  · exact B431819
  · exact B431823
  · exact B431827
  · exact B431831
  · exact B431835
  · exact B431839
  · exact B431843
  · exact B431847
  · exact B431851
  · exact B431855
  · exact B431859
  · exact B431863
  · exact B431867
  · exact B431871
  · exact B431875
  · exact B431879
  · exact B431883
  · exact B431887
  · exact B431891
  · exact B431895
  · exact B431899
  · exact B431903
  · exact B431907
  · exact B431911
  · exact B431915
  · exact B431919
  · exact B431923
  · exact B431927
  · exact B431931
  · exact B431935
  · exact B431939
  · exact B431943
  · exact B431947
  · exact B431951
  · exact B431955
  · exact B431959
  · exact B431963
  · exact B431967
  · exact B431971
  · exact B431975
  · exact B431979
  · exact B431983
  · exact B431987
  · exact B431991
  · exact B431995
  · exact B431999
  · exact B432003
  · exact B432007
  · exact B432011
  · exact B432015
  · exact B432019
  · exact B432023
  · exact B432027
  · exact B432031
  · exact B432035
  · exact B432039
  · exact B432043
  · exact B432047
  · exact B432051
  · exact B432055
  · exact B432059
  · exact B432063
  · exact B432067
  · exact B432071
  · exact B432075
  · exact B432079
  · exact B432083
  · exact B432087
  · exact B432091
  · exact B432095
  · exact B432099
  · exact B432103
  · exact B432107
  · exact B432111
  · exact B432115
  · exact B432119
  · exact B432123
  · exact B432127
  · exact B432131
  · exact B432135
  · exact B432139
  · exact B432143
  · exact B432147
  · exact B432151
  · exact B432155
  · exact B432159
  · exact B432163
  · exact B432167
  · exact B432171
  · exact B432175
  · exact B432179
  · exact B432183
  · exact B432187
  · exact B432191
  · exact B432195
  · exact B432199
  · exact B432203
  · exact B432207
  · exact B432211
  · exact B432215
  · exact B432219
  · exact B432223
  · exact B432227
  · exact B432231
  · exact B432235
  · exact B432239
  · exact B432243
  · exact B432247
  · exact B432251
  · exact B432255
  · exact B432259
  · exact B432263
  · exact B432267
  · exact B432271
  · exact B432275
  · exact B432279
  · exact B432283
  · exact B432287
  · exact B432291
  · exact B432295
  · exact B432299
  · exact B432303
  · exact B432307
  · exact B432311
  · exact B432315
  · exact B432319
  · exact B432323
  · exact B432327
  · exact B432331
  · exact B432335
  · exact B432339
  · exact B432343
  · exact B432347
  · exact B432351
  · exact B432355
  · exact B432359
  · exact B432363
  · exact B432367
  · exact B432371
  · exact B432375
  · exact B432379
  · exact B432383
  · exact B432387
  · exact B432391
  · exact B432395
  · exact B432399
  · exact B432403
  · exact B432407
  · exact B432411
  · exact B432415
  · exact B432419
  · exact B432423
  · exact B432427
  · exact B432431
  · exact B432435
  · exact B432439
  · exact B432443
  · exact B432447
  · exact B432451
  · exact B432455
  · exact B432459
  · exact B432463
  · exact B432467
  · exact B432471
  · exact B432475
  · exact B432479
  · exact B432483
  · exact B432487
  · exact B432491
  · exact B432495
  · exact B432499
  · exact B432503
  · exact B432507
  · exact B432511
  · exact B432515
  · exact B432519
  · exact B432523
  · exact B432527
  · exact B432531
  · exact B432535
  · exact B432539
  · exact B432543
  · exact B432547
  · exact B432551
  · exact B432555
  · exact B432559
  · exact B432563
  · exact B432567
  · exact B432571
  · exact B432575
  · exact B432579
  · exact B432583
  · exact B432587
  · exact B432591
  · exact B432595
  · exact B432599
  · exact B432603
  · exact B432607
  · exact B432611
  · exact B432615
  · exact B432619
  · exact B432623
  · exact B432627
  · exact B432631
  · exact B432635
  · exact B432639
  · exact B432643
  · exact B432647
  · exact B432651
  · exact B432655
  · exact B432659
  · exact B432663
  · exact B432667
  · exact B432671
  · exact B432675
  · exact B432679
  · exact B432683
  · exact B432687
  · exact B432691
  · exact B432695
  · exact B432699
  · exact B432703
  · exact B432707
  · exact B432711
  · exact B432715
  · exact B432719
  · exact B432723
  · exact B432727
  · exact B432731
  · exact B432735
  · exact B432739
  · exact B432743
  · exact B432747
  · exact B432751
  · exact B432755
  · exact B432759
  · exact B432763
  · exact B432767
  · exact B432771
  · exact B432775

theorem solution (m : ℕ) (hlo : 428775 ≤ m) (hhi : m ≤ 432775) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 107193 ≤ j := by omega
    have hj2 : j ≤ 108193 := by omega
    have hb : Blo 428775 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 107893 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
