-- Prove2me | solution 1 for syracuse_descends_range_519798_523798
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:48:25.708596+00:00
-- url     : https://prove2.me/submissions/b74c6d5d-b443-41d0-b262-df6d97f751c4

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


theorem B557113 : Blo 519798 557113 := bbase (se 2 (by rfl) ⟨208917, by rfl⟩ : syracuseStep 557113 = 417835) (by norm_num)
theorem B557237 : Blo 519798 557237 := bbase (se 5 (by rfl) ⟨26120, by rfl⟩ : syracuseStep 557237 = 52241) (by norm_num)
theorem B2228485 : Blo 519798 2228485 := bbase (se 4 (by rfl) ⟨208920, by rfl⟩ : syracuseStep 2228485 = 417841) (by norm_num)
theorem B1802549 : Blo 519798 1802549 := bbase (se 5 (by rfl) ⟨84494, by rfl⟩ : syracuseStep 1802549 = 168989) (by norm_num)
theorem B557489 : Blo 519798 557489 := bbase (se 2 (by rfl) ⟨209058, by rfl⟩ : syracuseStep 557489 = 418117) (by norm_num)
theorem B1671749 : Blo 519798 1671749 := bbase (se 4 (by rfl) ⟨156726, by rfl⟩ : syracuseStep 1671749 = 313453) (by norm_num)
theorem B3801941 : Blo 519798 3801941 := bbase (se 9 (by rfl) ⟨11138, by rfl⟩ : syracuseStep 3801941 = 22277) (by norm_num)
theorem B557933 : Blo 519798 557933 := bbase (se 3 (by rfl) ⟨104612, by rfl⟩ : syracuseStep 557933 = 209225) (by norm_num)
theorem B1115021 : Blo 519798 1115021 := bbase (se 3 (by rfl) ⟨209066, by rfl⟩ : syracuseStep 1115021 = 418133) (by norm_num)
theorem B2229221 : Blo 519798 2229221 := bbase (se 4 (by rfl) ⟨208989, by rfl⟩ : syracuseStep 2229221 = 417979) (by norm_num)
theorem B10322965 : Blo 519798 10322965 := bbase (se 6 (by rfl) ⟨241944, by rfl⟩ : syracuseStep 10322965 = 483889) (by norm_num)
theorem B1115165 : Blo 519798 1115165 := bbase (se 3 (by rfl) ⟨209093, by rfl⟩ : syracuseStep 1115165 = 418187) (by norm_num)
theorem B558181 : Blo 519798 558181 := bbase (se 4 (by rfl) ⟨52329, by rfl⟩ : syracuseStep 558181 = 104659) (by norm_num)
theorem B5014709 : Blo 519798 5014709 := bbase (se 5 (by rfl) ⟨235064, by rfl⟩ : syracuseStep 5014709 = 470129) (by norm_num)
theorem B1901909 : Blo 519798 1901909 := bbase (se 12 (by rfl) ⟨696, by rfl⟩ : syracuseStep 1901909 = 1393) (by norm_num)
theorem B1115525 : Blo 519798 1115525 := bbase (se 4 (by rfl) ⟨104580, by rfl⟩ : syracuseStep 1115525 = 209161) (by norm_num)
theorem B1672645 : Blo 519798 1672645 := bbase (se 4 (by rfl) ⟨156810, by rfl⟩ : syracuseStep 1672645 = 313621) (by norm_num)
theorem B3179989 : Blo 519798 3179989 := bbase (se 7 (by rfl) ⟨37265, by rfl⟩ : syracuseStep 3179989 = 74531) (by norm_num)
theorem B558625 : Blo 519798 558625 := bbase (se 2 (by rfl) ⟨209484, by rfl⟩ : syracuseStep 558625 = 418969) (by norm_num)
theorem B558685 : Blo 519798 558685 := bbase (se 3 (by rfl) ⟨104753, by rfl⟩ : syracuseStep 558685 = 209507) (by norm_num)
theorem B1410821 : Blo 519798 1410821 := bbase (se 4 (by rfl) ⟨132264, by rfl⟩ : syracuseStep 1410821 = 264529) (by norm_num)
theorem B1673045 : Blo 519798 1673045 := bbase (se 9 (by rfl) ⟨4901, by rfl⟩ : syracuseStep 1673045 = 9803) (by norm_num)
theorem B559001 : Blo 519798 559001 := bbase (se 2 (by rfl) ⟨209625, by rfl⟩ : syracuseStep 559001 = 419251) (by norm_num)
theorem B1411253 : Blo 519798 1411253 := bbase (se 5 (by rfl) ⟨66152, by rfl⟩ : syracuseStep 1411253 = 132305) (by norm_num)
theorem B1116413 : Blo 519798 1116413 := bbase (se 3 (by rfl) ⟨209327, by rfl⟩ : syracuseStep 1116413 = 418655) (by norm_num)
theorem B8063381 : Blo 519798 8063381 := bbase (se 6 (by rfl) ⟨188985, by rfl⟩ : syracuseStep 8063381 = 377971) (by norm_num)
theorem B657877 : Blo 519798 657877 := bbase (se 7 (by rfl) ⟨7709, by rfl⟩ : syracuseStep 657877 = 15419) (by norm_num)
theorem B1116661 : Blo 519798 1116661 := bbase (se 5 (by rfl) ⟨52343, by rfl⟩ : syracuseStep 1116661 = 104687) (by norm_num)
theorem B657973 : Blo 519798 657973 := bbase (se 5 (by rfl) ⟨30842, by rfl⟩ : syracuseStep 657973 = 61685) (by norm_num)
theorem B625205 : Blo 519798 625205 := bbase (se 5 (by rfl) ⟨29306, by rfl⟩ : syracuseStep 625205 = 58613) (by norm_num)
theorem B526933 : Blo 519798 526933 := bbase (se 8 (by rfl) ⟨3087, by rfl⟩ : syracuseStep 526933 = 6175) (by norm_num)
theorem B625277 : Blo 519798 625277 := bbase (se 3 (by rfl) ⟨117239, by rfl⟩ : syracuseStep 625277 = 234479) (by norm_num)
theorem B4459157 : Blo 519798 4459157 := bbase (se 6 (by rfl) ⟨104511, by rfl⟩ : syracuseStep 4459157 = 209023) (by norm_num)
theorem B3148469 : Blo 519798 3148469 := bbase (se 5 (by rfl) ⟨147584, by rfl⟩ : syracuseStep 3148469 = 295169) (by norm_num)
theorem B658145 : Blo 519798 658145 := bbase (se 2 (by rfl) ⟨246804, by rfl⟩ : syracuseStep 658145 = 493609) (by norm_num)
theorem B658201 : Blo 519798 658201 := bbase (se 2 (by rfl) ⟨246825, by rfl⟩ : syracuseStep 658201 = 493651) (by norm_num)
theorem B1543013 : Blo 519798 1543013 := bbase (se 4 (by rfl) ⟨144657, by rfl⟩ : syracuseStep 1543013 = 289315) (by norm_num)
theorem B658297 : Blo 519798 658297 := bbase (se 2 (by rfl) ⟨246861, by rfl⟩ : syracuseStep 658297 = 493723) (by norm_num)
theorem B625585 : Blo 519798 625585 := bbase (se 2 (by rfl) ⟨234594, by rfl⟩ : syracuseStep 625585 = 469189) (by norm_num)
theorem B1117165 : Blo 519798 1117165 := bbase (se 3 (by rfl) ⟨209468, by rfl⟩ : syracuseStep 1117165 = 418937) (by norm_num)
theorem B658469 : Blo 519798 658469 := bbase (se 4 (by rfl) ⟨61731, by rfl⟩ : syracuseStep 658469 = 123463) (by norm_num)
theorem B2821205 : Blo 519798 2821205 := bbase (se 8 (by rfl) ⟨16530, by rfl⟩ : syracuseStep 2821205 = 33061) (by norm_num)
theorem B625753 : Blo 519798 625753 := bbase (se 2 (by rfl) ⟨234657, by rfl⟩ : syracuseStep 625753 = 469315) (by norm_num)
theorem B658525 : Blo 519798 658525 := bbase (se 3 (by rfl) ⟨123473, by rfl⟩ : syracuseStep 658525 = 246947) (by norm_num)
theorem B625801 : Blo 519798 625801 := bbase (se 2 (by rfl) ⟨234675, by rfl⟩ : syracuseStep 625801 = 469351) (by norm_num)
theorem B658621 : Blo 519798 658621 := bbase (se 3 (by rfl) ⟨123491, by rfl⟩ : syracuseStep 658621 = 246983) (by norm_num)
theorem B625897 : Blo 519798 625897 := bbase (se 2 (by rfl) ⟨234711, by rfl⟩ : syracuseStep 625897 = 469423) (by norm_num)
theorem B658793 : Blo 519798 658793 := bbase (se 2 (by rfl) ⟨247047, by rfl⟩ : syracuseStep 658793 = 494095) (by norm_num)
theorem B658849 : Blo 519798 658849 := bbase (se 2 (by rfl) ⟨247068, by rfl⟩ : syracuseStep 658849 = 494137) (by norm_num)
theorem B2035109 : Blo 519798 2035109 := bbase (se 4 (by rfl) ⟨190791, by rfl⟩ : syracuseStep 2035109 = 381583) (by norm_num)
theorem B658945 : Blo 519798 658945 := bbase (se 2 (by rfl) ⟨247104, by rfl⟩ : syracuseStep 658945 = 494209) (by norm_num)
theorem B659117 : Blo 519798 659117 := bbase (se 3 (by rfl) ⟨123584, by rfl⟩ : syracuseStep 659117 = 247169) (by norm_num)
theorem B659173 : Blo 519798 659173 := bbase (se 4 (by rfl) ⟨61797, by rfl⟩ : syracuseStep 659173 = 123595) (by norm_num)
theorem B626473 : Blo 519798 626473 := bbase (se 2 (by rfl) ⟨234927, by rfl⟩ : syracuseStep 626473 = 469855) (by norm_num)
theorem B659269 : Blo 519798 659269 := bbase (se 4 (by rfl) ⟨61806, by rfl⟩ : syracuseStep 659269 = 123613) (by norm_num)
theorem B1118053 : Blo 519798 1118053 := bbase (se 4 (by rfl) ⟨104817, by rfl⟩ : syracuseStep 1118053 = 209635) (by norm_num)
theorem B987005 : Blo 519798 987005 := bbase (se 3 (by rfl) ⟨185063, by rfl⟩ : syracuseStep 987005 = 370127) (by norm_num)
theorem B659441 : Blo 519798 659441 := bbase (se 2 (by rfl) ⟨247290, by rfl⟩ : syracuseStep 659441 = 494581) (by norm_num)
theorem B987157 : Blo 519798 987157 := bbase (se 6 (by rfl) ⟨23136, by rfl⟩ : syracuseStep 987157 = 46273) (by norm_num)
theorem B659497 : Blo 519798 659497 := bbase (se 2 (by rfl) ⟨247311, by rfl⟩ : syracuseStep 659497 = 494623) (by norm_num)
theorem B528433 : Blo 519798 528433 := bbase (se 2 (by rfl) ⟨198162, by rfl⟩ : syracuseStep 528433 = 396325) (by norm_num)
theorem B659593 : Blo 519798 659593 := bbase (se 2 (by rfl) ⟨247347, by rfl⟩ : syracuseStep 659593 = 494695) (by norm_num)
theorem B3772565 : Blo 519798 3772565 := bbase (se 6 (by rfl) ⟨88419, by rfl⟩ : syracuseStep 3772565 = 176839) (by norm_num)
theorem B790717 : Blo 519798 790717 := bbase (se 3 (by rfl) ⟨148259, by rfl⟩ : syracuseStep 790717 = 296519) (by norm_num)
theorem B2232517 : Blo 519798 2232517 := bbase (se 4 (by rfl) ⟨209298, by rfl⟩ : syracuseStep 2232517 = 418597) (by norm_num)
theorem B790789 : Blo 519798 790789 := bbase (se 4 (by rfl) ⟨74136, by rfl⟩ : syracuseStep 790789 = 148273) (by norm_num)
theorem B659765 : Blo 519798 659765 := bbase (se 5 (by rfl) ⟨30926, by rfl⟩ : syracuseStep 659765 = 61853) (by norm_num)
theorem B987461 : Blo 519798 987461 := bbase (se 4 (by rfl) ⟨92574, by rfl⟩ : syracuseStep 987461 = 185149) (by norm_num)
theorem B1118549 : Blo 519798 1118549 := bbase (se 10 (by rfl) ⟨1638, by rfl⟩ : syracuseStep 1118549 = 3277) (by norm_num)
theorem B659821 : Blo 519798 659821 := bbase (se 3 (by rfl) ⟨123716, by rfl⟩ : syracuseStep 659821 = 247433) (by norm_num)
theorem B528749 : Blo 519798 528749 := bbase (se 3 (by rfl) ⟨99140, by rfl⟩ : syracuseStep 528749 = 198281) (by norm_num)
theorem B1249661 : Blo 519798 1249661 := bbase (se 3 (by rfl) ⟨234311, by rfl⟩ : syracuseStep 1249661 = 468623) (by norm_num)
theorem B1249717 : Blo 519798 1249717 := bbase (se 5 (by rfl) ⟨58580, by rfl⟩ : syracuseStep 1249717 = 117161) (by norm_num)
theorem B659917 : Blo 519798 659917 := bbase (se 3 (by rfl) ⟨123734, by rfl⟩ : syracuseStep 659917 = 247469) (by norm_num)
theorem B594497 : Blo 519798 594497 := bbase (se 2 (by rfl) ⟨222936, by rfl⟩ : syracuseStep 594497 = 445873) (by norm_num)
theorem B660089 : Blo 519798 660089 := bbase (se 2 (by rfl) ⟨247533, by rfl⟩ : syracuseStep 660089 = 495067) (by norm_num)
theorem B660145 : Blo 519798 660145 := bbase (se 2 (by rfl) ⟨247554, by rfl⟩ : syracuseStep 660145 = 495109) (by norm_num)
theorem B594625 : Blo 519798 594625 := bbase (se 2 (by rfl) ⟨222984, by rfl⟩ : syracuseStep 594625 = 445969) (by norm_num)
theorem B3773141 : Blo 519798 3773141 := bbase (se 7 (by rfl) ⟨44216, by rfl⟩ : syracuseStep 3773141 = 88433) (by norm_num)
theorem B3347189 : Blo 519798 3347189 := bbase (se 5 (by rfl) ⟨156899, by rfl⟩ : syracuseStep 3347189 = 313799) (by norm_num)
theorem B660241 : Blo 519798 660241 := bbase (se 2 (by rfl) ⟨247590, by rfl⟩ : syracuseStep 660241 = 495181) (by norm_num)
theorem B627473 : Blo 519798 627473 := bbase (se 2 (by rfl) ⟨235302, by rfl⟩ : syracuseStep 627473 = 470605) (by norm_num)
theorem B1250093 : Blo 519798 1250093 := bbase (se 3 (by rfl) ⟨234392, by rfl⟩ : syracuseStep 1250093 = 468785) (by norm_num)
theorem B627521 : Blo 519798 627521 := bbase (se 2 (by rfl) ⟨235320, by rfl⟩ : syracuseStep 627521 = 470641) (by norm_num)
theorem B529301 : Blo 519798 529301 := bbase (se 6 (by rfl) ⟨12405, by rfl⟩ : syracuseStep 529301 = 24811) (by norm_num)
theorem B660413 : Blo 519798 660413 := bbase (se 3 (by rfl) ⟨123827, by rfl⟩ : syracuseStep 660413 = 247655) (by norm_num)
theorem B660469 : Blo 519798 660469 := bbase (se 5 (by rfl) ⟨30959, by rfl⟩ : syracuseStep 660469 = 61919) (by norm_num)
theorem B1250333 : Blo 519798 1250333 := bbase (se 3 (by rfl) ⟨234437, by rfl⟩ : syracuseStep 1250333 = 468875) (by norm_num)
theorem B1315885 : Blo 519798 1315885 := bbase (se 3 (by rfl) ⟨246728, by rfl⟩ : syracuseStep 1315885 = 493457) (by norm_num)
theorem B988213 : Blo 519798 988213 := bbase (se 5 (by rfl) ⟨46322, by rfl⟩ : syracuseStep 988213 = 92645) (by norm_num)
theorem B660565 : Blo 519798 660565 := bbase (se 8 (by rfl) ⟨3870, by rfl⟩ : syracuseStep 660565 = 7741) (by norm_num)
theorem B3970133 : Blo 519798 3970133 := bbase (se 8 (by rfl) ⟨23262, by rfl⟩ : syracuseStep 3970133 = 46525) (by norm_num)
theorem B791677 : Blo 519798 791677 := bbase (se 3 (by rfl) ⟨148439, by rfl⟩ : syracuseStep 791677 = 296879) (by norm_num)
theorem B1315997 : Blo 519798 1315997 := bbase (se 3 (by rfl) ⟨246749, by rfl⟩ : syracuseStep 1315997 = 493499) (by norm_num)
theorem B988357 : Blo 519798 988357 := bbase (se 4 (by rfl) ⟨92658, by rfl⟩ : syracuseStep 988357 = 185317) (by norm_num)
theorem B529625 : Blo 519798 529625 := bbase (se 2 (by rfl) ⟨198609, by rfl⟩ : syracuseStep 529625 = 397219) (by norm_num)
theorem B660737 : Blo 519798 660737 := bbase (se 2 (by rfl) ⟨247776, by rfl⟩ : syracuseStep 660737 = 495553) (by norm_num)
theorem B660793 : Blo 519798 660793 := bbase (se 2 (by rfl) ⟨247797, by rfl⟩ : syracuseStep 660793 = 495595) (by norm_num)
theorem B1316189 : Blo 519798 1316189 := bbase (se 3 (by rfl) ⟨246785, by rfl⟩ : syracuseStep 1316189 = 493571) (by norm_num)
theorem B988517 : Blo 519798 988517 := bbase (se 4 (by rfl) ⟨92673, by rfl⟩ : syracuseStep 988517 = 185347) (by norm_num)
theorem B628069 : Blo 519798 628069 := bbase (se 4 (by rfl) ⟨58881, by rfl⟩ : syracuseStep 628069 = 117763) (by norm_num)
theorem B660889 : Blo 519798 660889 := bbase (se 2 (by rfl) ⟨247833, by rfl⟩ : syracuseStep 660889 = 495667) (by norm_num)
theorem B1054117 : Blo 519798 1054117 := bbase (se 4 (by rfl) ⟨98823, by rfl⟩ : syracuseStep 1054117 = 197647) (by norm_num)
theorem B988661 : Blo 519798 988661 := bbase (se 5 (by rfl) ⟨46343, by rfl⟩ : syracuseStep 988661 = 92687) (by norm_num)
theorem B1676837 : Blo 519798 1676837 := bbase (se 4 (by rfl) ⟨157203, by rfl⟩ : syracuseStep 1676837 = 314407) (by norm_num)
theorem B661061 : Blo 519798 661061 := bbase (se 4 (by rfl) ⟨61974, by rfl⟩ : syracuseStep 661061 = 123949) (by norm_num)
theorem B1873525 : Blo 519798 1873525 := bbase (se 5 (by rfl) ⟨87821, by rfl⟩ : syracuseStep 1873525 = 175643) (by norm_num)
theorem B661117 : Blo 519798 661117 := bbase (se 3 (by rfl) ⟨123959, by rfl⟩ : syracuseStep 661117 = 247919) (by norm_num)
theorem B1316533 : Blo 519798 1316533 := bbase (se 5 (by rfl) ⟨61712, by rfl⟩ : syracuseStep 1316533 = 123425) (by norm_num)
theorem B661213 : Blo 519798 661213 := bbase (se 3 (by rfl) ⟨123977, by rfl⟩ : syracuseStep 661213 = 247955) (by norm_num)
theorem B988949 : Blo 519798 988949 := bbase (se 6 (by rfl) ⟨23178, by rfl⟩ : syracuseStep 988949 = 46357) (by norm_num)
theorem B530209 : Blo 519798 530209 := bbase (se 2 (by rfl) ⟨198828, by rfl⟩ : syracuseStep 530209 = 397657) (by norm_num)
theorem B1316645 : Blo 519798 1316645 := bbase (se 4 (by rfl) ⟨123435, by rfl⟩ : syracuseStep 1316645 = 246871) (by norm_num)
theorem B890677 : Blo 519798 890677 := bbase (se 5 (by rfl) ⟨41750, by rfl⟩ : syracuseStep 890677 = 83501) (by norm_num)
theorem B628549 : Blo 519798 628549 := bbase (se 4 (by rfl) ⟨58926, by rfl⟩ : syracuseStep 628549 = 117853) (by norm_num)
theorem B661385 : Blo 519798 661385 := bbase (se 2 (by rfl) ⟨248019, by rfl⟩ : syracuseStep 661385 = 496039) (by norm_num)
theorem B1054637 : Blo 519798 1054637 := bbase (se 3 (by rfl) ⟨197744, by rfl⟩ : syracuseStep 1054637 = 395489) (by norm_num)
theorem B989101 : Blo 519798 989101 := bbase (se 3 (by rfl) ⟨185456, by rfl⟩ : syracuseStep 989101 = 370913) (by norm_num)
theorem B661441 : Blo 519798 661441 := bbase (se 2 (by rfl) ⟨248040, by rfl⟩ : syracuseStep 661441 = 496081) (by norm_num)
theorem B1316837 : Blo 519798 1316837 := bbase (se 4 (by rfl) ⟨123453, by rfl⟩ : syracuseStep 1316837 = 246907) (by norm_num)
theorem B661537 : Blo 519798 661537 := bbase (se 2 (by rfl) ⟨248076, by rfl⟩ : syracuseStep 661537 = 496153) (by norm_num)
theorem B1480805 : Blo 519798 1480805 := bbase (se 4 (by rfl) ⟨138825, by rfl⟩ : syracuseStep 1480805 = 277651) (by norm_num)
theorem B530533 : Blo 519798 530533 := bbase (se 4 (by rfl) ⟨49737, by rfl⟩ : syracuseStep 530533 = 99475) (by norm_num)
theorem B661709 : Blo 519798 661709 := bbase (se 3 (by rfl) ⟨124070, by rfl⟩ : syracuseStep 661709 = 248141) (by norm_num)
theorem B989405 : Blo 519798 989405 := bbase (se 3 (by rfl) ⟨185513, by rfl⟩ : syracuseStep 989405 = 371027) (by norm_num)
theorem B661765 : Blo 519798 661765 := bbase (se 4 (by rfl) ⟨62040, by rfl⟩ : syracuseStep 661765 = 124081) (by norm_num)
theorem B792845 : Blo 519798 792845 := bbase (se 3 (by rfl) ⟨148658, by rfl⟩ : syracuseStep 792845 = 297317) (by norm_num)
theorem B1317181 : Blo 519798 1317181 := bbase (se 3 (by rfl) ⟨246971, by rfl⟩ : syracuseStep 1317181 = 493943) (by norm_num)
theorem B661861 : Blo 519798 661861 := bbase (se 4 (by rfl) ⟨62049, by rfl⟩ : syracuseStep 661861 = 124099) (by norm_num)
theorem B530825 : Blo 519798 530825 := bbase (se 2 (by rfl) ⟨199059, by rfl⟩ : syracuseStep 530825 = 398119) (by norm_num)
theorem B1317293 : Blo 519798 1317293 := bbase (se 3 (by rfl) ⟨246992, by rfl⟩ : syracuseStep 1317293 = 493985) (by norm_num)
theorem B1055197 : Blo 519798 1055197 := bbase (se 3 (by rfl) ⟨197849, by rfl⟩ : syracuseStep 1055197 = 395699) (by norm_num)
theorem B662033 : Blo 519798 662033 := bbase (se 2 (by rfl) ⟨248262, by rfl⟩ : syracuseStep 662033 = 496525) (by norm_num)
theorem B1481237 : Blo 519798 1481237 := bbase (se 6 (by rfl) ⟨34716, by rfl⟩ : syracuseStep 1481237 = 69433) (by norm_num)
theorem B662089 : Blo 519798 662089 := bbase (se 2 (by rfl) ⟨248283, by rfl⟩ : syracuseStep 662089 = 496567) (by norm_num)
theorem B563801 : Blo 519798 563801 := bbase (se 2 (by rfl) ⟨211425, by rfl⟩ : syracuseStep 563801 = 422851) (by norm_num)
theorem B1677925 : Blo 519798 1677925 := bbase (se 4 (by rfl) ⟨157305, by rfl⟩ : syracuseStep 1677925 = 314611) (by norm_num)
theorem B1317485 : Blo 519798 1317485 := bbase (se 3 (by rfl) ⟨247028, by rfl⟩ : syracuseStep 1317485 = 494057) (by norm_num)
theorem B662185 : Blo 519798 662185 := bbase (se 2 (by rfl) ⟨248319, by rfl⟩ : syracuseStep 662185 = 496639) (by norm_num)
theorem B662357 : Blo 519798 662357 := bbase (se 9 (by rfl) ⟨1940, by rfl⟩ : syracuseStep 662357 = 3881) (by norm_num)
theorem B662413 : Blo 519798 662413 := bbase (se 3 (by rfl) ⟨124202, by rfl⟩ : syracuseStep 662413 = 248405) (by norm_num)
theorem B1317829 : Blo 519798 1317829 := bbase (se 4 (by rfl) ⟨123546, by rfl⟩ : syracuseStep 1317829 = 247093) (by norm_num)
theorem B990157 : Blo 519798 990157 := bbase (se 3 (by rfl) ⟨185654, by rfl⟩ : syracuseStep 990157 = 371309) (by norm_num)
theorem B662509 : Blo 519798 662509 := bbase (se 3 (by rfl) ⟨124220, by rfl⟩ : syracuseStep 662509 = 248441) (by norm_num)
theorem B1874981 : Blo 519798 1874981 := bbase (se 4 (by rfl) ⟨175779, by rfl⟩ : syracuseStep 1874981 = 351559) (by norm_num)
theorem B1317941 : Blo 519798 1317941 := bbase (se 5 (by rfl) ⟨61778, by rfl⟩ : syracuseStep 1317941 = 123557) (by norm_num)
theorem B990301 : Blo 519798 990301 := bbase (se 3 (by rfl) ⟨185681, by rfl⟩ : syracuseStep 990301 = 371363) (by norm_num)
theorem B1055845 : Blo 519798 1055845 := bbase (se 4 (by rfl) ⟨98985, by rfl⟩ : syracuseStep 1055845 = 197971) (by norm_num)
theorem B2235509 : Blo 519798 2235509 := bbase (se 5 (by rfl) ⟨104789, by rfl⟩ : syracuseStep 2235509 = 209579) (by norm_num)
theorem B662681 : Blo 519798 662681 := bbase (se 2 (by rfl) ⟨248505, by rfl⟩ : syracuseStep 662681 = 497011) (by norm_num)
theorem B2170037 : Blo 519798 2170037 := bbase (se 5 (by rfl) ⟨101720, by rfl⟩ : syracuseStep 2170037 = 203441) (by norm_num)
theorem B662737 : Blo 519798 662737 := bbase (se 2 (by rfl) ⟨248526, by rfl⟩ : syracuseStep 662737 = 497053) (by norm_num)
theorem B1318133 : Blo 519798 1318133 := bbase (se 5 (by rfl) ⟨61787, by rfl⟩ : syracuseStep 1318133 = 123575) (by norm_num)
theorem B990461 : Blo 519798 990461 := bbase (se 3 (by rfl) ⟨185711, by rfl⟩ : syracuseStep 990461 = 371423) (by norm_num)
theorem B1481989 : Blo 519798 1481989 := bbase (se 4 (by rfl) ⟨138936, by rfl⟩ : syracuseStep 1481989 = 277873) (by norm_num)
theorem B662833 : Blo 519798 662833 := bbase (se 2 (by rfl) ⟨248562, by rfl⟩ : syracuseStep 662833 = 497125) (by norm_num)
theorem B990605 : Blo 519798 990605 := bbase (se 3 (by rfl) ⟨185738, by rfl⟩ : syracuseStep 990605 = 371477) (by norm_num)
theorem B564689 : Blo 519798 564689 := bbase (se 2 (by rfl) ⟨211758, by rfl⟩ : syracuseStep 564689 = 423517) (by norm_num)
theorem B1875413 : Blo 519798 1875413 := bbase (se 7 (by rfl) ⟨21977, by rfl⟩ : syracuseStep 1875413 = 43955) (by norm_num)
theorem B1318477 : Blo 519798 1318477 := bbase (se 3 (by rfl) ⟨247214, by rfl⟩ : syracuseStep 1318477 = 494429) (by norm_num)
theorem B794189 : Blo 519798 794189 := bbase (se 3 (by rfl) ⟨148910, by rfl⟩ : syracuseStep 794189 = 297821) (by norm_num)
theorem B2203301 : Blo 519798 2203301 := bbase (se 4 (by rfl) ⟨206559, by rfl⟩ : syracuseStep 2203301 = 413119) (by norm_num)
theorem B990893 : Blo 519798 990893 := bbase (se 3 (by rfl) ⟨185792, by rfl⟩ : syracuseStep 990893 = 371585) (by norm_num)
theorem B564913 : Blo 519798 564913 := bbase (se 2 (by rfl) ⟨211842, by rfl⟩ : syracuseStep 564913 = 423685) (by norm_num)
theorem B1318589 : Blo 519798 1318589 := bbase (se 3 (by rfl) ⟨247235, by rfl⟩ : syracuseStep 1318589 = 494471) (by norm_num)
theorem B794413 : Blo 519798 794413 := bbase (se 3 (by rfl) ⟨148952, by rfl⟩ : syracuseStep 794413 = 297905) (by norm_num)
theorem B991045 : Blo 519798 991045 := bbase (se 4 (by rfl) ⟨92910, by rfl⟩ : syracuseStep 991045 = 185821) (by norm_num)
theorem B1318781 : Blo 519798 1318781 := bbase (se 3 (by rfl) ⟨247271, by rfl⟩ : syracuseStep 1318781 = 494543) (by norm_num)
theorem B2236517 : Blo 519798 2236517 := bbase (se 4 (by rfl) ⟨209673, by rfl⟩ : syracuseStep 2236517 = 419347) (by norm_num)
theorem B1253485 : Blo 519798 1253485 := bbase (se 3 (by rfl) ⟨235028, by rfl⟩ : syracuseStep 1253485 = 470057) (by norm_num)
theorem B991349 : Blo 519798 991349 := bbase (se 5 (by rfl) ⟨46469, by rfl⟩ : syracuseStep 991349 = 92939) (by norm_num)
theorem B1319125 : Blo 519798 1319125 := bbase (se 7 (by rfl) ⟨15458, by rfl⟩ : syracuseStep 1319125 = 30917) (by norm_num)
theorem B10035413 : Blo 519798 10035413 := bbase (se 7 (by rfl) ⟨117602, by rfl⟩ : syracuseStep 10035413 = 235205) (by norm_num)
theorem B1057045 : Blo 519798 1057045 := bbase (se 6 (by rfl) ⟨24774, by rfl⟩ : syracuseStep 1057045 = 49549) (by norm_num)
theorem B1319237 : Blo 519798 1319237 := bbase (se 4 (by rfl) ⟨123678, by rfl⟩ : syracuseStep 1319237 = 247357) (by norm_num)
theorem B1974725 : Blo 519798 1974725 := bbase (se 4 (by rfl) ⟨185130, by rfl⟩ : syracuseStep 1974725 = 370261) (by norm_num)
theorem B1876421 : Blo 519798 1876421 := bbase (se 4 (by rfl) ⟨175914, by rfl⟩ : syracuseStep 1876421 = 351829) (by norm_num)
theorem B1319429 : Blo 519798 1319429 := bbase (se 4 (by rfl) ⟨123696, by rfl⟩ : syracuseStep 1319429 = 247393) (by norm_num)
theorem B1975013 : Blo 519798 1975013 := bbase (se 4 (by rfl) ⟨185157, by rfl⟩ : syracuseStep 1975013 = 370315) (by norm_num)
theorem B1319773 : Blo 519798 1319773 := bbase (se 3 (by rfl) ⟨247457, by rfl⟩ : syracuseStep 1319773 = 494915) (by norm_num)
theorem B992101 : Blo 519798 992101 := bbase (se 4 (by rfl) ⟨93009, by rfl⟩ : syracuseStep 992101 = 186019) (by norm_num)
theorem B1057693 : Blo 519798 1057693 := bbase (se 3 (by rfl) ⟨198317, by rfl⟩ : syracuseStep 1057693 = 396635) (by norm_num)
theorem B1319885 : Blo 519798 1319885 := bbase (se 3 (by rfl) ⟨247478, by rfl⟩ : syracuseStep 1319885 = 494957) (by norm_num)
theorem B992245 : Blo 519798 992245 := bbase (se 5 (by rfl) ⟨46511, by rfl⟩ : syracuseStep 992245 = 93023) (by norm_num)
theorem B1320077 : Blo 519798 1320077 := bbase (se 3 (by rfl) ⟨247514, by rfl⟩ : syracuseStep 1320077 = 495029) (by norm_num)
theorem B992405 : Blo 519798 992405 := bbase (se 6 (by rfl) ⟨23259, by rfl⟩ : syracuseStep 992405 = 46519) (by norm_num)
theorem B992549 : Blo 519798 992549 := bbase (se 4 (by rfl) ⟨93051, by rfl⟩ : syracuseStep 992549 = 186103) (by norm_num)
theorem B1254869 : Blo 519798 1254869 := bbase (se 7 (by rfl) ⟨14705, by rfl⟩ : syracuseStep 1254869 = 29411) (by norm_num)
theorem B1058269 : Blo 519798 1058269 := bbase (se 3 (by rfl) ⟨198425, by rfl⟩ : syracuseStep 1058269 = 396851) (by norm_num)
theorem B1320421 : Blo 519798 1320421 := bbase (se 4 (by rfl) ⟨123789, by rfl⟩ : syracuseStep 1320421 = 247579) (by norm_num)
theorem B992837 : Blo 519798 992837 := bbase (se 4 (by rfl) ⟨93078, by rfl⟩ : syracuseStep 992837 = 186157) (by norm_num)
theorem B1320533 : Blo 519798 1320533 := bbase (se 8 (by rfl) ⟨7737, by rfl⟩ : syracuseStep 1320533 = 15475) (by norm_num)
theorem B1255061 : Blo 519798 1255061 := bbase (se 6 (by rfl) ⟨29415, by rfl⟩ : syracuseStep 1255061 = 58831) (by norm_num)
theorem B992989 : Blo 519798 992989 := bbase (se 3 (by rfl) ⟨186185, by rfl⟩ : syracuseStep 992989 = 372371) (by norm_num)
theorem B1320725 : Blo 519798 1320725 := bbase (se 6 (by rfl) ⟨30954, by rfl⟩ : syracuseStep 1320725 = 61909) (by norm_num)
theorem B894797 : Blo 519798 894797 := bbase (se 3 (by rfl) ⟨167774, by rfl⟩ : syracuseStep 894797 = 335549) (by norm_num)
theorem B1976197 : Blo 519798 1976197 := bbase (se 4 (by rfl) ⟨185268, by rfl⟩ : syracuseStep 1976197 = 370537) (by norm_num)
theorem B993293 : Blo 519798 993293 := bbase (se 3 (by rfl) ⟨186242, by rfl⟩ : syracuseStep 993293 = 372485) (by norm_num)
theorem B1484837 : Blo 519798 1484837 := bbase (se 4 (by rfl) ⟨139203, by rfl⟩ : syracuseStep 1484837 = 278407) (by norm_num)
theorem B1321069 : Blo 519798 1321069 := bbase (se 3 (by rfl) ⟨247700, by rfl⟩ : syracuseStep 1321069 = 495401) (by norm_num)
theorem B1976501 : Blo 519798 1976501 := bbase (se 5 (by rfl) ⟨92648, by rfl⟩ : syracuseStep 1976501 = 185297) (by norm_num)
theorem B1321181 : Blo 519798 1321181 := bbase (se 3 (by rfl) ⟨247721, by rfl⟩ : syracuseStep 1321181 = 495443) (by norm_num)
theorem B3352853 : Blo 519798 3352853 := bbase (se 6 (by rfl) ⟨78582, by rfl⟩ : syracuseStep 3352853 = 157165) (by norm_num)
theorem B1321373 : Blo 519798 1321373 := bbase (se 3 (by rfl) ⟨247757, by rfl⟩ : syracuseStep 1321373 = 495515) (by norm_num)
theorem B1583525 : Blo 519798 1583525 := bbase (se 4 (by rfl) ⟨148455, by rfl⟩ : syracuseStep 1583525 = 296911) (by norm_num)
theorem B4467221 : Blo 519798 4467221 := bbase (se 6 (by rfl) ⟨104700, by rfl⟩ : syracuseStep 4467221 = 209401) (by norm_num)
theorem B2894453 : Blo 519798 2894453 := bbase (se 5 (by rfl) ⟨135677, by rfl⟩ : syracuseStep 2894453 = 271355) (by norm_num)
theorem B1321717 : Blo 519798 1321717 := bbase (se 5 (by rfl) ⟨61955, by rfl⟩ : syracuseStep 1321717 = 123911) (by norm_num)
theorem B994045 : Blo 519798 994045 := bbase (se 3 (by rfl) ⟨186383, by rfl⟩ : syracuseStep 994045 = 372767) (by norm_num)
theorem B1321829 : Blo 519798 1321829 := bbase (se 4 (by rfl) ⟨123921, by rfl⟩ : syracuseStep 1321829 = 247843) (by norm_num)
theorem B994189 : Blo 519798 994189 := bbase (se 3 (by rfl) ⟨186410, by rfl⟩ : syracuseStep 994189 = 372821) (by norm_num)
theorem B2632661 : Blo 519798 2632661 := bbase (se 7 (by rfl) ⟨30851, by rfl⟩ : syracuseStep 2632661 = 61703) (by norm_num)
theorem B1322021 : Blo 519798 1322021 := bbase (se 4 (by rfl) ⟨123939, by rfl⟩ : syracuseStep 1322021 = 247879) (by norm_num)
theorem B994349 : Blo 519798 994349 := bbase (se 3 (by rfl) ⟨186440, by rfl⟩ : syracuseStep 994349 = 372881) (by norm_num)
theorem B1256629 : Blo 519798 1256629 := bbase (se 5 (by rfl) ⟨58904, by rfl⟩ : syracuseStep 1256629 = 117809) (by norm_num)
theorem B1486021 : Blo 519798 1486021 := bbase (se 4 (by rfl) ⟨139314, by rfl⟩ : syracuseStep 1486021 = 278629) (by norm_num)
theorem B1486181 : Blo 519798 1486181 := bbase (se 4 (by rfl) ⟨139329, by rfl⟩ : syracuseStep 1486181 = 278659) (by norm_num)
theorem B1322365 : Blo 519798 1322365 := bbase (se 3 (by rfl) ⟨247943, by rfl⟩ : syracuseStep 1322365 = 495887) (by norm_num)
theorem B1191365 : Blo 519798 1191365 := bbase (se 4 (by rfl) ⟨111690, by rfl⟩ : syracuseStep 1191365 = 223381) (by norm_num)
theorem B1322477 : Blo 519798 1322477 := bbase (se 3 (by rfl) ⟨247964, by rfl⟩ : syracuseStep 1322477 = 495929) (by norm_num)
theorem B1486421 : Blo 519798 1486421 := bbase (se 8 (by rfl) ⟨8709, by rfl⟩ : syracuseStep 1486421 = 17419) (by norm_num)
theorem B1322669 : Blo 519798 1322669 := bbase (se 3 (by rfl) ⟨248000, by rfl⟩ : syracuseStep 1322669 = 496001) (by norm_num)
theorem B1486613 : Blo 519798 1486613 := bbase (se 6 (by rfl) ⟨34842, by rfl⟩ : syracuseStep 1486613 = 69685) (by norm_num)
theorem B1257245 : Blo 519798 1257245 := bbase (se 3 (by rfl) ⟨235733, by rfl⟩ : syracuseStep 1257245 = 471467) (by norm_num)
theorem B3387253 : Blo 519798 3387253 := bbase (se 5 (by rfl) ⟨158777, by rfl⟩ : syracuseStep 3387253 = 317555) (by norm_num)
theorem B1323013 : Blo 519798 1323013 := bbase (se 4 (by rfl) ⟨124032, by rfl⟩ : syracuseStep 1323013 = 248065) (by norm_num)
theorem B1323125 : Blo 519798 1323125 := bbase (se 5 (by rfl) ⟨62021, by rfl⟩ : syracuseStep 1323125 = 124043) (by norm_num)
theorem B1159373 : Blo 519798 1159373 := bbase (se 3 (by rfl) ⟨217382, by rfl⟩ : syracuseStep 1159373 = 434765) (by norm_num)
theorem B2633957 : Blo 519798 2633957 := bbase (se 4 (by rfl) ⟨246933, by rfl⟩ : syracuseStep 2633957 = 493867) (by norm_num)
theorem B1978613 : Blo 519798 1978613 := bbase (se 5 (by rfl) ⟨92747, by rfl⟩ : syracuseStep 1978613 = 185495) (by norm_num)
theorem B635149 : Blo 519798 635149 := bbase (se 3 (by rfl) ⟨119090, by rfl⟩ : syracuseStep 635149 = 238181) (by norm_num)
theorem B1323317 : Blo 519798 1323317 := bbase (se 5 (by rfl) ⟨62030, by rfl⟩ : syracuseStep 1323317 = 124061) (by norm_num)
theorem B1782229 : Blo 519798 1782229 := bbase (se 7 (by rfl) ⟨20885, by rfl⟩ : syracuseStep 1782229 = 41771) (by norm_num)
theorem B1978901 : Blo 519798 1978901 := bbase (se 6 (by rfl) ⟨46380, by rfl⟩ : syracuseStep 1978901 = 92761) (by norm_num)
theorem B1258021 : Blo 519798 1258021 := bbase (se 4 (by rfl) ⟨117939, by rfl⟩ : syracuseStep 1258021 = 235879) (by norm_num)
theorem B1323661 : Blo 519798 1323661 := bbase (se 3 (by rfl) ⟨248186, by rfl⟩ : syracuseStep 1323661 = 496373) (by norm_num)
theorem B1585909 : Blo 519798 1585909 := bbase (se 5 (by rfl) ⟨74339, by rfl⟩ : syracuseStep 1585909 = 148679) (by norm_num)
theorem B1487605 : Blo 519798 1487605 := bbase (se 5 (by rfl) ⟨69731, by rfl⟩ : syracuseStep 1487605 = 139463) (by norm_num)
theorem B1323773 : Blo 519798 1323773 := bbase (se 3 (by rfl) ⟨248207, by rfl⟩ : syracuseStep 1323773 = 496415) (by norm_num)
theorem B537377 : Blo 519798 537377 := bbase (se 2 (by rfl) ⟨201516, by rfl⟩ : syracuseStep 537377 = 403033) (by norm_num)
theorem B1323965 : Blo 519798 1323965 := bbase (se 3 (by rfl) ⟨248243, by rfl⟩ : syracuseStep 1323965 = 496487) (by norm_num)
theorem B537625 : Blo 519798 537625 := bbase (se 2 (by rfl) ⟨201609, by rfl⟩ : syracuseStep 537625 = 403219) (by norm_num)
theorem B668701 : Blo 519798 668701 := bbase (se 3 (by rfl) ⟨125381, by rfl⟩ : syracuseStep 668701 = 250763) (by norm_num)
theorem B2503781 : Blo 519798 2503781 := bbase (se 4 (by rfl) ⟨234729, by rfl⟩ : syracuseStep 2503781 = 469459) (by norm_num)
theorem B4568309 : Blo 519798 4568309 := bbase (se 5 (by rfl) ⟨214139, by rfl⟩ : syracuseStep 4568309 = 428279) (by norm_num)
theorem B1324309 : Blo 519798 1324309 := bbase (se 6 (by rfl) ⟨31038, by rfl⟩ : syracuseStep 1324309 = 62077) (by norm_num)
theorem B5354869 : Blo 519798 5354869 := bbase (se 5 (by rfl) ⟨251009, by rfl⟩ : syracuseStep 5354869 = 502019) (by norm_num)
theorem B1324421 : Blo 519798 1324421 := bbase (se 4 (by rfl) ⟨124164, by rfl⟩ : syracuseStep 1324421 = 248329) (by norm_num)
theorem B2635253 : Blo 519798 2635253 := bbase (se 5 (by rfl) ⟨123527, by rfl⟩ : syracuseStep 2635253 = 247055) (by norm_num)
theorem B1324613 : Blo 519798 1324613 := bbase (se 4 (by rfl) ⟨124182, by rfl⟩ : syracuseStep 1324613 = 248365) (by norm_num)
theorem B1980085 : Blo 519798 1980085 := bbase (se 5 (by rfl) ⟨92816, by rfl⟩ : syracuseStep 1980085 = 185633) (by norm_num)
theorem B2668261 : Blo 519798 2668261 := bbase (se 4 (by rfl) ⟨250149, by rfl⟩ : syracuseStep 2668261 = 500299) (by norm_num)
theorem B1193773 : Blo 519798 1193773 := bbase (se 3 (by rfl) ⟨223832, by rfl⟩ : syracuseStep 1193773 = 447665) (by norm_num)
theorem B1488709 : Blo 519798 1488709 := bbase (se 4 (by rfl) ⟨139566, by rfl⟩ : syracuseStep 1488709 = 279133) (by norm_num)
theorem B1718101 : Blo 519798 1718101 := bbase (se 9 (by rfl) ⟨5033, by rfl⟩ : syracuseStep 1718101 = 10067) (by norm_num)
theorem B1324957 : Blo 519798 1324957 := bbase (se 3 (by rfl) ⟨248429, by rfl⟩ : syracuseStep 1324957 = 496859) (by norm_num)
theorem B1980389 : Blo 519798 1980389 := bbase (se 4 (by rfl) ⟨185661, by rfl⟩ : syracuseStep 1980389 = 371323) (by norm_num)
theorem B1325069 : Blo 519798 1325069 := bbase (se 3 (by rfl) ⟨248450, by rfl⟩ : syracuseStep 1325069 = 496901) (by norm_num)
theorem B833581 : Blo 519798 833581 := bbase (se 3 (by rfl) ⟨156296, by rfl⟩ : syracuseStep 833581 = 312593) (by norm_num)
theorem B1587317 : Blo 519798 1587317 := bbase (se 5 (by rfl) ⟨74405, by rfl⟩ : syracuseStep 1587317 = 148811) (by norm_num)
theorem B702589 : Blo 519798 702589 := bbase (se 3 (by rfl) ⟨131735, by rfl⟩ : syracuseStep 702589 = 263471) (by norm_num)
theorem B1325261 : Blo 519798 1325261 := bbase (se 3 (by rfl) ⟨248486, by rfl⟩ : syracuseStep 1325261 = 496973) (by norm_num)
theorem B702685 : Blo 519798 702685 := bbase (se 3 (by rfl) ⟨131753, by rfl⟩ : syracuseStep 702685 = 263507) (by norm_num)
theorem B3750421 : Blo 519798 3750421 := bbase (se 6 (by rfl) ⟨87900, by rfl⟩ : syracuseStep 3750421 = 175801) (by norm_num)
theorem B1325605 : Blo 519798 1325605 := bbase (se 4 (by rfl) ⟨124275, by rfl⟩ : syracuseStep 1325605 = 248551) (by norm_num)
theorem B1325717 : Blo 519798 1325717 := bbase (se 6 (by rfl) ⟨31071, by rfl⟩ : syracuseStep 1325717 = 62143) (by norm_num)
theorem B670441 : Blo 519798 670441 := bbase (se 2 (by rfl) ⟨251415, by rfl⟩ : syracuseStep 670441 = 502831) (by norm_num)
theorem B2636549 : Blo 519798 2636549 := bbase (se 4 (by rfl) ⟨247176, by rfl⟩ : syracuseStep 2636549 = 494353) (by norm_num)
theorem B1882997 : Blo 519798 1882997 := bbase (se 5 (by rfl) ⟨88265, by rfl⟩ : syracuseStep 1882997 = 176531) (by norm_num)
theorem B670933 : Blo 519798 670933 := bbase (se 7 (by rfl) ⟨7862, by rfl⟩ : syracuseStep 670933 = 15725) (by norm_num)
theorem B1490213 : Blo 519798 1490213 := bbase (se 4 (by rfl) ⟨139707, by rfl⟩ : syracuseStep 1490213 = 279415) (by norm_num)
theorem B834965 : Blo 519798 834965 := bbase (se 6 (by rfl) ⟨19569, by rfl⟩ : syracuseStep 834965 = 39139) (by norm_num)
theorem B1883573 : Blo 519798 1883573 := bbase (se 5 (by rfl) ⟨88292, by rfl⟩ : syracuseStep 1883573 = 176585) (by norm_num)
theorem B4996565 : Blo 519798 4996565 := bbase (se 7 (by rfl) ⟨58553, by rfl⟩ : syracuseStep 4996565 = 117107) (by norm_num)
theorem B835157 : Blo 519798 835157 := bbase (se 8 (by rfl) ⟨4893, by rfl⟩ : syracuseStep 835157 = 9787) (by norm_num)
theorem B671657 : Blo 519798 671657 := bbase (se 2 (by rfl) ⟨251871, by rfl⟩ : syracuseStep 671657 = 503743) (by norm_num)
theorem B3162037 : Blo 519798 3162037 := bbase (se 5 (by rfl) ⟨148220, by rfl⟩ : syracuseStep 3162037 = 296441) (by norm_num)
theorem B2637845 : Blo 519798 2637845 := bbase (se 6 (by rfl) ⟨61824, by rfl⟩ : syracuseStep 2637845 = 123649) (by norm_num)
theorem B1982501 : Blo 519798 1982501 := bbase (se 4 (by rfl) ⟨185859, by rfl⟩ : syracuseStep 1982501 = 371719) (by norm_num)
theorem B2113685 : Blo 519798 2113685 := bbase (se 6 (by rfl) ⟨49539, by rfl⟩ : syracuseStep 2113685 = 99079) (by norm_num)
theorem B2113829 : Blo 519798 2113829 := bbase (se 4 (by rfl) ⟨198171, by rfl⟩ : syracuseStep 2113829 = 396343) (by norm_num)
theorem B1589557 : Blo 519798 1589557 := bbase (se 5 (by rfl) ⟨74510, by rfl⟩ : syracuseStep 1589557 = 149021) (by norm_num)
theorem B1982789 : Blo 519798 1982789 := bbase (se 4 (by rfl) ⟨185886, by rfl⟩ : syracuseStep 1982789 = 371773) (by norm_num)
theorem B1720709 : Blo 519798 1720709 := bbase (se 4 (by rfl) ⟨161316, by rfl⟩ : syracuseStep 1720709 = 322633) (by norm_num)
theorem B1884725 : Blo 519798 1884725 := bbase (se 5 (by rfl) ⟨88346, by rfl⟩ : syracuseStep 1884725 = 176693) (by norm_num)
theorem B1688197 : Blo 519798 1688197 := bbase (se 4 (by rfl) ⟨158268, by rfl⟩ : syracuseStep 1688197 = 316537) (by norm_num)
theorem B2966165 : Blo 519798 2966165 := bbase (se 6 (by rfl) ⟨69519, by rfl⟩ : syracuseStep 2966165 = 139039) (by norm_num)
theorem B836477 : Blo 519798 836477 := bbase (se 3 (by rfl) ⟨156839, by rfl⟩ : syracuseStep 836477 = 313679) (by norm_num)
theorem B836573 : Blo 519798 836573 := bbase (se 3 (by rfl) ⟨156857, by rfl⟩ : syracuseStep 836573 = 313715) (by norm_num)
theorem B836605 : Blo 519798 836605 := bbase (se 3 (by rfl) ⟨156863, by rfl⟩ : syracuseStep 836605 = 313727) (by norm_num)
theorem B541777 : Blo 519798 541777 := bbase (se 2 (by rfl) ⟨203166, by rfl⟩ : syracuseStep 541777 = 406333) (by norm_num)
theorem B1688741 : Blo 519798 1688741 := bbase (se 4 (by rfl) ⟨158319, by rfl⟩ : syracuseStep 1688741 = 316639) (by norm_num)
theorem B1754405 : Blo 519798 1754405 := bbase (se 4 (by rfl) ⟨164475, by rfl⟩ : syracuseStep 1754405 = 328951) (by norm_num)
theorem B2639141 : Blo 519798 2639141 := bbase (se 4 (by rfl) ⟨247419, by rfl⟩ : syracuseStep 2639141 = 494839) (by norm_num)
theorem B1983973 : Blo 519798 1983973 := bbase (se 4 (by rfl) ⟨185997, by rfl⟩ : syracuseStep 1983973 = 371995) (by norm_num)
theorem B1590821 : Blo 519798 1590821 := bbase (se 4 (by rfl) ⟨149139, by rfl⟩ : syracuseStep 1590821 = 298279) (by norm_num)
theorem B706205 : Blo 519798 706205 := bbase (se 3 (by rfl) ⟨132413, by rfl⟩ : syracuseStep 706205 = 264827) (by norm_num)
theorem B4245173 : Blo 519798 4245173 := bbase (se 5 (by rfl) ⟨198992, by rfl⟩ : syracuseStep 4245173 = 397985) (by norm_num)
theorem B706253 : Blo 519798 706253 := bbase (se 3 (by rfl) ⟨132422, by rfl⟩ : syracuseStep 706253 = 264845) (by norm_num)
theorem B1754837 : Blo 519798 1754837 := bbase (se 7 (by rfl) ⟨20564, by rfl⟩ : syracuseStep 1754837 = 41129) (by norm_num)
theorem B1984277 : Blo 519798 1984277 := bbase (se 6 (by rfl) ⟨46506, by rfl⟩ : syracuseStep 1984277 = 93013) (by norm_num)
theorem B4245301 : Blo 519798 4245301 := bbase (se 5 (by rfl) ⟨198998, by rfl⟩ : syracuseStep 4245301 = 397997) (by norm_num)
theorem B1755269 : Blo 519798 1755269 := bbase (se 4 (by rfl) ⟨164556, by rfl⟩ : syracuseStep 1755269 = 329113) (by norm_num)
theorem B706837 : Blo 519798 706837 := bbase (se 6 (by rfl) ⟨16566, by rfl⟩ : syracuseStep 706837 = 33133) (by norm_num)
theorem B1886485 : Blo 519798 1886485 := bbase (se 6 (by rfl) ⟨44214, by rfl⟩ : syracuseStep 1886485 = 88429) (by norm_num)
theorem B838117 : Blo 519798 838117 := bbase (se 4 (by rfl) ⟨78573, by rfl⟩ : syracuseStep 838117 = 157147) (by norm_num)
theorem B1001981 : Blo 519798 1001981 := bbase (se 3 (by rfl) ⟨187871, by rfl⟩ : syracuseStep 1001981 = 375743) (by norm_num)
theorem B5032469 : Blo 519798 5032469 := bbase (se 6 (by rfl) ⟨117948, by rfl⟩ : syracuseStep 5032469 = 235897) (by norm_num)
theorem B1755701 : Blo 519798 1755701 := bbase (se 5 (by rfl) ⟨82298, by rfl⟩ : syracuseStep 1755701 = 164597) (by norm_num)
theorem B2640437 : Blo 519798 2640437 := bbase (se 5 (by rfl) ⟨123770, by rfl⟩ : syracuseStep 2640437 = 247541) (by norm_num)
theorem B2116165 : Blo 519798 2116165 := bbase (se 4 (by rfl) ⟨198390, by rfl⟩ : syracuseStep 2116165 = 396781) (by norm_num)
theorem B1886789 : Blo 519798 1886789 := bbase (se 4 (by rfl) ⟨176886, by rfl⟩ : syracuseStep 1886789 = 353773) (by norm_num)
theorem B904133 : Blo 519798 904133 := bbase (se 4 (by rfl) ⟨84762, by rfl⟩ : syracuseStep 904133 = 169525) (by norm_num)
theorem B1756133 : Blo 519798 1756133 := bbase (se 4 (by rfl) ⟨164637, by rfl⟩ : syracuseStep 1756133 = 329275) (by norm_num)
theorem B937109 : Blo 519798 937109 := bbase (se 6 (by rfl) ⟨21963, by rfl⟩ : syracuseStep 937109 = 43927) (by norm_num)
theorem B838829 : Blo 519798 838829 := bbase (se 3 (by rfl) ⟨157280, by rfl⟩ : syracuseStep 838829 = 314561) (by norm_num)
theorem B1756565 : Blo 519798 1756565 := bbase (se 6 (by rfl) ⟨41169, by rfl⟩ : syracuseStep 1756565 = 82339) (by norm_num)
theorem B10833301 : Blo 519798 10833301 := bbase (se 6 (by rfl) ⟨253905, by rfl⟩ : syracuseStep 10833301 = 507811) (by norm_num)
theorem B642853 : Blo 519798 642853 := bbase (se 4 (by rfl) ⟨60267, by rfl⟩ : syracuseStep 642853 = 120535) (by norm_num)
theorem B1756997 : Blo 519798 1756997 := bbase (se 4 (by rfl) ⟨164718, by rfl⟩ : syracuseStep 1756997 = 329437) (by norm_num)
theorem B2641733 : Blo 519798 2641733 := bbase (se 4 (by rfl) ⟨247662, by rfl⟩ : syracuseStep 2641733 = 495325) (by norm_num)
theorem B1986389 : Blo 519798 1986389 := bbase (se 9 (by rfl) ⟨5819, by rfl⟩ : syracuseStep 1986389 = 11639) (by norm_num)
theorem B741325 : Blo 519798 741325 := bbase (se 3 (by rfl) ⟨138998, by rfl⟩ : syracuseStep 741325 = 277997) (by norm_num)
theorem B6770645 : Blo 519798 6770645 := bbase (se 7 (by rfl) ⟨79343, by rfl⟩ : syracuseStep 6770645 = 158687) (by norm_num)
theorem B1986677 : Blo 519798 1986677 := bbase (se 5 (by rfl) ⟨93125, by rfl⟩ : syracuseStep 1986677 = 186251) (by norm_num)
theorem B1757429 : Blo 519798 1757429 := bbase (se 5 (by rfl) ⟨82379, by rfl⟩ : syracuseStep 1757429 = 164759) (by norm_num)
theorem B938413 : Blo 519798 938413 := bbase (se 3 (by rfl) ⟨175952, by rfl⟩ : syracuseStep 938413 = 351905) (by norm_num)
theorem B741917 : Blo 519798 741917 := bbase (se 3 (by rfl) ⟨139109, by rfl⟩ : syracuseStep 741917 = 278219) (by norm_num)
theorem B741997 : Blo 519798 741997 := bbase (se 3 (by rfl) ⟨139124, by rfl⟩ : syracuseStep 741997 = 278249) (by norm_num)
theorem B1757861 : Blo 519798 1757861 := bbase (se 4 (by rfl) ⟨164799, by rfl⟩ : syracuseStep 1757861 = 329599) (by norm_num)
theorem B742117 : Blo 519798 742117 := bbase (se 4 (by rfl) ⟨69573, by rfl⟩ : syracuseStep 742117 = 139147) (by norm_num)
theorem B742213 : Blo 519798 742213 := bbase (se 4 (by rfl) ⟨69582, by rfl⟩ : syracuseStep 742213 = 139165) (by norm_num)
theorem B7131989 : Blo 519798 7131989 := bbase (se 9 (by rfl) ⟨20894, by rfl⟩ : syracuseStep 7131989 = 41789) (by norm_num)
theorem B4445077 : Blo 519798 4445077 := bbase (se 6 (by rfl) ⟨104181, by rfl⟩ : syracuseStep 4445077 = 208363) (by norm_num)
theorem B1758293 : Blo 519798 1758293 := bbase (se 8 (by rfl) ⟨10302, by rfl⟩ : syracuseStep 1758293 = 20605) (by norm_num)
theorem B2643029 : Blo 519798 2643029 := bbase (se 8 (by rfl) ⟨15486, by rfl⟩ : syracuseStep 2643029 = 30973) (by norm_num)
theorem B939133 : Blo 519798 939133 := bbase (se 3 (by rfl) ⟨176087, by rfl⟩ : syracuseStep 939133 = 352175) (by norm_num)
theorem B1987861 : Blo 519798 1987861 := bbase (se 6 (by rfl) ⟨46590, by rfl⟩ : syracuseStep 1987861 = 93181) (by norm_num)
theorem B742709 : Blo 519798 742709 := bbase (se 5 (by rfl) ⟨34814, by rfl⟩ : syracuseStep 742709 = 69629) (by norm_num)
theorem B906653 : Blo 519798 906653 := bbase (se 3 (by rfl) ⟨169997, by rfl⟩ : syracuseStep 906653 = 339995) (by norm_num)
theorem B1758725 : Blo 519798 1758725 := bbase (se 4 (by rfl) ⟨164880, by rfl⟩ : syracuseStep 1758725 = 329761) (by norm_num)
theorem B1988165 : Blo 519798 1988165 := bbase (se 4 (by rfl) ⟨186390, by rfl⟩ : syracuseStep 1988165 = 372781) (by norm_num)
theorem B743261 : Blo 519798 743261 := bbase (se 3 (by rfl) ⟨139361, by rfl⟩ : syracuseStep 743261 = 278723) (by norm_num)
theorem B3954581 : Blo 519798 3954581 := bbase (se 6 (by rfl) ⟨92685, by rfl⟩ : syracuseStep 3954581 = 185371) (by norm_num)
theorem B939941 : Blo 519798 939941 := bbase (se 4 (by rfl) ⟨88119, by rfl⟩ : syracuseStep 939941 = 176239) (by norm_num)
theorem B1759157 : Blo 519798 1759157 := bbase (se 5 (by rfl) ⟨82460, by rfl⟩ : syracuseStep 1759157 = 164921) (by norm_num)
theorem B2512853 : Blo 519798 2512853 := bbase (se 7 (by rfl) ⟨29447, by rfl⟩ : syracuseStep 2512853 = 58895) (by norm_num)
theorem B2414645 : Blo 519798 2414645 := bbase (se 5 (by rfl) ⟨113186, by rfl⟩ : syracuseStep 2414645 = 226373) (by norm_num)
theorem B1169549 : Blo 519798 1169549 := bbase (se 3 (by rfl) ⟨219290, by rfl⟩ : syracuseStep 1169549 = 438581) (by norm_num)
theorem B2513045 : Blo 519798 2513045 := bbase (se 6 (by rfl) ⟨58899, by rfl⟩ : syracuseStep 2513045 = 117799) (by norm_num)
theorem B1169621 : Blo 519798 1169621 := bbase (se 7 (by rfl) ⟨13706, by rfl⟩ : syracuseStep 1169621 = 27413) (by norm_num)
theorem B1169693 : Blo 519798 1169693 := bbase (se 3 (by rfl) ⟨219317, by rfl⟩ : syracuseStep 1169693 = 438635) (by norm_num)
theorem B1169765 : Blo 519798 1169765 := bbase (se 4 (by rfl) ⟨109665, by rfl⟩ : syracuseStep 1169765 = 219331) (by norm_num)
theorem B1759589 : Blo 519798 1759589 := bbase (se 4 (by rfl) ⟨164961, by rfl⟩ : syracuseStep 1759589 = 329923) (by norm_num)
theorem B2644325 : Blo 519798 2644325 := bbase (se 4 (by rfl) ⟨247905, by rfl⟩ : syracuseStep 2644325 = 495811) (by norm_num)
theorem B1169837 : Blo 519798 1169837 := bbase (se 3 (by rfl) ⟨219344, by rfl⟩ : syracuseStep 1169837 = 438689) (by norm_num)
theorem B1169909 : Blo 519798 1169909 := bbase (se 5 (by rfl) ⟨54839, by rfl⟩ : syracuseStep 1169909 = 109679) (by norm_num)
theorem B2513429 : Blo 519798 2513429 := bbase (se 6 (by rfl) ⟨58908, by rfl⟩ : syracuseStep 2513429 = 117817) (by norm_num)
theorem B1169981 : Blo 519798 1169981 := bbase (se 3 (by rfl) ⟨219371, by rfl⟩ : syracuseStep 1169981 = 438743) (by norm_num)
theorem B744013 : Blo 519798 744013 := bbase (se 3 (by rfl) ⟨139502, by rfl⟩ : syracuseStep 744013 = 279005) (by norm_num)
theorem B1170053 : Blo 519798 1170053 := bbase (se 4 (by rfl) ⟨109692, by rfl⟩ : syracuseStep 1170053 = 219385) (by norm_num)
theorem B1170125 : Blo 519798 1170125 := bbase (se 3 (by rfl) ⟨219398, by rfl⟩ : syracuseStep 1170125 = 438797) (by norm_num)
theorem B1170197 : Blo 519798 1170197 := bbase (se 6 (by rfl) ⟨27426, by rfl⟩ : syracuseStep 1170197 = 54853) (by norm_num)
theorem B1760021 : Blo 519798 1760021 := bbase (se 6 (by rfl) ⟨41250, by rfl⟩ : syracuseStep 1760021 = 82501) (by norm_num)
theorem B1334045 : Blo 519798 1334045 := bbase (se 3 (by rfl) ⟨250133, by rfl⟩ : syracuseStep 1334045 = 500267) (by norm_num)
theorem B4447061 : Blo 519798 4447061 := bbase (se 9 (by rfl) ⟨13028, by rfl⟩ : syracuseStep 4447061 = 26057) (by norm_num)
theorem B32168789 : Blo 519798 32168789 := bbase (se 9 (by rfl) ⟨94244, by rfl⟩ : syracuseStep 32168789 = 188489) (by norm_num)
theorem B1170269 : Blo 519798 1170269 := bbase (se 3 (by rfl) ⟨219425, by rfl⟩ : syracuseStep 1170269 = 438851) (by norm_num)
theorem B1170341 : Blo 519798 1170341 := bbase (se 4 (by rfl) ⟨109719, by rfl⟩ : syracuseStep 1170341 = 219439) (by norm_num)
theorem B1006501 : Blo 519798 1006501 := bbase (se 4 (by rfl) ⟨94359, by rfl⟩ : syracuseStep 1006501 = 188719) (by norm_num)
theorem B1170413 : Blo 519798 1170413 := bbase (se 3 (by rfl) ⟨219452, by rfl⟩ : syracuseStep 1170413 = 438905) (by norm_num)
theorem B1170485 : Blo 519798 1170485 := bbase (se 5 (by rfl) ⟨54866, by rfl⟩ : syracuseStep 1170485 = 109733) (by norm_num)
theorem B1170557 : Blo 519798 1170557 := bbase (se 3 (by rfl) ⟨219479, by rfl⟩ : syracuseStep 1170557 = 438959) (by norm_num)
theorem B5364917 : Blo 519798 5364917 := bbase (se 5 (by rfl) ⟨251480, by rfl⟩ : syracuseStep 5364917 = 502961) (by norm_num)
theorem B1170629 : Blo 519798 1170629 := bbase (se 4 (by rfl) ⟨109746, by rfl⟩ : syracuseStep 1170629 = 219493) (by norm_num)
theorem B1760453 : Blo 519798 1760453 := bbase (se 4 (by rfl) ⟨165042, by rfl⟩ : syracuseStep 1760453 = 330085) (by norm_num)
theorem B1170701 : Blo 519798 1170701 := bbase (se 3 (by rfl) ⟨219506, by rfl⟩ : syracuseStep 1170701 = 439013) (by norm_num)
theorem B1170773 : Blo 519798 1170773 := bbase (se 11 (by rfl) ⟨857, by rfl⟩ : syracuseStep 1170773 = 1715) (by norm_num)
theorem B96722261 : Blo 519798 96722261 := bbase (se 11 (by rfl) ⟨70841, by rfl⟩ : syracuseStep 96722261 = 141683) (by norm_num)
theorem B744805 : Blo 519798 744805 := bbase (se 4 (by rfl) ⟨69825, by rfl⟩ : syracuseStep 744805 = 139651) (by norm_num)
theorem B1170845 : Blo 519798 1170845 := bbase (se 3 (by rfl) ⟨219533, by rfl⟩ : syracuseStep 1170845 = 439067) (by norm_num)
theorem B1170917 : Blo 519798 1170917 := bbase (se 4 (by rfl) ⟨109773, by rfl⟩ : syracuseStep 1170917 = 219547) (by norm_num)
theorem B941549 : Blo 519798 941549 := bbase (se 3 (by rfl) ⟨176540, by rfl⟩ : syracuseStep 941549 = 353081) (by norm_num)
theorem B1170989 : Blo 519798 1170989 := bbase (se 3 (by rfl) ⟨219560, by rfl⟩ : syracuseStep 1170989 = 439121) (by norm_num)
theorem B1171061 : Blo 519798 1171061 := bbase (se 5 (by rfl) ⟨54893, by rfl⟩ : syracuseStep 1171061 = 109787) (by norm_num)
theorem B1760885 : Blo 519798 1760885 := bbase (se 5 (by rfl) ⟨82541, by rfl⟩ : syracuseStep 1760885 = 165083) (by norm_num)
theorem B2645621 : Blo 519798 2645621 := bbase (se 5 (by rfl) ⟨124013, by rfl⟩ : syracuseStep 2645621 = 248027) (by norm_num)
theorem B2088629 : Blo 519798 2088629 := bbase (se 5 (by rfl) ⟨97904, by rfl⟩ : syracuseStep 2088629 = 195809) (by norm_num)
theorem B745141 : Blo 519798 745141 := bbase (se 5 (by rfl) ⟨34928, by rfl⟩ : syracuseStep 745141 = 69857) (by norm_num)
theorem B1171133 : Blo 519798 1171133 := bbase (se 3 (by rfl) ⟨219587, by rfl⟩ : syracuseStep 1171133 = 439175) (by norm_num)
theorem B6676181 : Blo 519798 6676181 := bbase (se 7 (by rfl) ⟨78236, by rfl⟩ : syracuseStep 6676181 = 156473) (by norm_num)
theorem B679657 : Blo 519798 679657 := bbase (se 2 (by rfl) ⟨254871, by rfl⟩ : syracuseStep 679657 = 509743) (by norm_num)
theorem B1171205 : Blo 519798 1171205 := bbase (se 4 (by rfl) ⟨109800, by rfl⟩ : syracuseStep 1171205 = 219601) (by norm_num)
theorem B1171277 : Blo 519798 1171277 := bbase (se 3 (by rfl) ⟨219614, by rfl⟩ : syracuseStep 1171277 = 439229) (by norm_num)
theorem B745357 : Blo 519798 745357 := bbase (se 3 (by rfl) ⟨139754, by rfl⟩ : syracuseStep 745357 = 279509) (by norm_num)
theorem B1171349 : Blo 519798 1171349 := bbase (se 6 (by rfl) ⟨27453, by rfl⟩ : syracuseStep 1171349 = 54907) (by norm_num)
theorem B581537 : Blo 519798 581537 := bbase (se 2 (by rfl) ⟨218076, by rfl⟩ : syracuseStep 581537 = 436153) (by norm_num)
theorem B1171421 : Blo 519798 1171421 := bbase (se 3 (by rfl) ⟨219641, by rfl⟩ : syracuseStep 1171421 = 439283) (by norm_num)
theorem B1171493 : Blo 519798 1171493 := bbase (se 4 (by rfl) ⟨109827, by rfl⟩ : syracuseStep 1171493 = 219655) (by norm_num)
theorem B1761317 : Blo 519798 1761317 := bbase (se 4 (by rfl) ⟨165123, by rfl⟩ : syracuseStep 1761317 = 330247) (by norm_num)
theorem B1171565 : Blo 519798 1171565 := bbase (se 3 (by rfl) ⟨219668, by rfl⟩ : syracuseStep 1171565 = 439337) (by norm_num)
theorem B942205 : Blo 519798 942205 := bbase (se 3 (by rfl) ⟨176663, by rfl⟩ : syracuseStep 942205 = 353327) (by norm_num)
theorem B1171637 : Blo 519798 1171637 := bbase (se 5 (by rfl) ⟨54920, by rfl⟩ : syracuseStep 1171637 = 109841) (by norm_num)
theorem B1171709 : Blo 519798 1171709 := bbase (se 3 (by rfl) ⟨219695, by rfl⟩ : syracuseStep 1171709 = 439391) (by norm_num)
theorem B745733 : Blo 519798 745733 := bbase (se 4 (by rfl) ⟨69912, by rfl⟩ : syracuseStep 745733 = 139825) (by norm_num)
theorem B1171781 : Blo 519798 1171781 := bbase (se 4 (by rfl) ⟨109854, by rfl⟩ : syracuseStep 1171781 = 219709) (by norm_num)
theorem B1171853 : Blo 519798 1171853 := bbase (se 3 (by rfl) ⟨219722, by rfl⟩ : syracuseStep 1171853 = 439445) (by norm_num)
theorem B1171925 : Blo 519798 1171925 := bbase (se 7 (by rfl) ⟨13733, by rfl⟩ : syracuseStep 1171925 = 27467) (by norm_num)
theorem B1761749 : Blo 519798 1761749 := bbase (se 7 (by rfl) ⟨20645, by rfl⟩ : syracuseStep 1761749 = 41291) (by norm_num)
theorem B2974229 : Blo 519798 2974229 := bbase (se 6 (by rfl) ⟨69708, by rfl⟩ : syracuseStep 2974229 = 139417) (by norm_num)
theorem B1171997 : Blo 519798 1171997 := bbase (se 3 (by rfl) ⟨219749, by rfl⟩ : syracuseStep 1171997 = 439499) (by norm_num)
theorem B2253349 : Blo 519798 2253349 := bbase (se 4 (by rfl) ⟨211251, by rfl⟩ : syracuseStep 2253349 = 422503) (by norm_num)
theorem B1172069 : Blo 519798 1172069 := bbase (se 4 (by rfl) ⟨109881, by rfl⟩ : syracuseStep 1172069 = 219763) (by norm_num)
theorem B877189 : Blo 519798 877189 := bbase (se 4 (by rfl) ⟨82236, by rfl⟩ : syracuseStep 877189 = 164473) (by norm_num)
theorem B1172141 : Blo 519798 1172141 := bbase (se 3 (by rfl) ⟨219776, by rfl⟩ : syracuseStep 1172141 = 439553) (by norm_num)
theorem B877277 : Blo 519798 877277 := bbase (se 3 (by rfl) ⟨164489, by rfl⟩ : syracuseStep 877277 = 328979) (by norm_num)
theorem B1172213 : Blo 519798 1172213 := bbase (se 5 (by rfl) ⟨54947, by rfl⟩ : syracuseStep 1172213 = 109895) (by norm_num)
theorem B2286341 : Blo 519798 2286341 := bbase (se 4 (by rfl) ⟨214344, by rfl⟩ : syracuseStep 2286341 = 428689) (by norm_num)
theorem B1172285 : Blo 519798 1172285 := bbase (se 3 (by rfl) ⟨219803, by rfl⟩ : syracuseStep 1172285 = 439607) (by norm_num)
theorem B877405 : Blo 519798 877405 := bbase (se 3 (by rfl) ⟨164513, by rfl⟩ : syracuseStep 877405 = 329027) (by norm_num)
theorem B1172357 : Blo 519798 1172357 := bbase (se 4 (by rfl) ⟨109908, by rfl⟩ : syracuseStep 1172357 = 219817) (by norm_num)
theorem B1762181 : Blo 519798 1762181 := bbase (se 4 (by rfl) ⟨165204, by rfl⟩ : syracuseStep 1762181 = 330409) (by norm_num)
theorem B2646917 : Blo 519798 2646917 := bbase (se 4 (by rfl) ⟨248148, by rfl⟩ : syracuseStep 2646917 = 496297) (by norm_num)
theorem B942997 : Blo 519798 942997 := bbase (se 6 (by rfl) ⟨22101, by rfl⟩ : syracuseStep 942997 = 44203) (by norm_num)
theorem B877493 : Blo 519798 877493 := bbase (se 5 (by rfl) ⟨41132, by rfl⟩ : syracuseStep 877493 = 82265) (by norm_num)
theorem B3335093 : Blo 519798 3335093 := bbase (se 5 (by rfl) ⟨156332, by rfl⟩ : syracuseStep 3335093 = 312665) (by norm_num)
theorem B1172429 : Blo 519798 1172429 := bbase (se 3 (by rfl) ⟨219830, by rfl⟩ : syracuseStep 1172429 = 439661) (by norm_num)
theorem B1172501 : Blo 519798 1172501 := bbase (se 6 (by rfl) ⟨27480, by rfl⟩ : syracuseStep 1172501 = 54961) (by norm_num)
theorem B877621 : Blo 519798 877621 := bbase (se 5 (by rfl) ⟨41138, by rfl⟩ : syracuseStep 877621 = 82277) (by norm_num)
theorem B1172573 : Blo 519798 1172573 := bbase (se 3 (by rfl) ⟨219857, by rfl⟩ : syracuseStep 1172573 = 439715) (by norm_num)
theorem B877709 : Blo 519798 877709 := bbase (se 3 (by rfl) ⟨164570, by rfl⟩ : syracuseStep 877709 = 329141) (by norm_num)
theorem B1172645 : Blo 519798 1172645 := bbase (se 4 (by rfl) ⟨109935, by rfl⟩ : syracuseStep 1172645 = 219871) (by norm_num)
theorem B1172717 : Blo 519798 1172717 := bbase (se 3 (by rfl) ⟨219884, by rfl⟩ : syracuseStep 1172717 = 439769) (by norm_num)
theorem B877837 : Blo 519798 877837 := bbase (se 3 (by rfl) ⟨164594, by rfl⟩ : syracuseStep 877837 = 329189) (by norm_num)
theorem B1172789 : Blo 519798 1172789 := bbase (se 5 (by rfl) ⟨54974, by rfl⟩ : syracuseStep 1172789 = 109949) (by norm_num)
theorem B1762613 : Blo 519798 1762613 := bbase (se 5 (by rfl) ⟨82622, by rfl⟩ : syracuseStep 1762613 = 165245) (by norm_num)
theorem B877925 : Blo 519798 877925 := bbase (se 4 (by rfl) ⟨82305, by rfl⟩ : syracuseStep 877925 = 164611) (by norm_num)
theorem B1172861 : Blo 519798 1172861 := bbase (se 3 (by rfl) ⟨219911, by rfl⟩ : syracuseStep 1172861 = 439823) (by norm_num)
theorem B2221445 : Blo 519798 2221445 := bbase (se 4 (by rfl) ⟨208260, by rfl⟩ : syracuseStep 2221445 = 416521) (by norm_num)
theorem B779717 : Blo 519798 779717 := bbase (se 4 (by rfl) ⟨73098, by rfl⟩ : syracuseStep 779717 = 146197) (by norm_num)
theorem B1172933 : Blo 519798 1172933 := bbase (se 4 (by rfl) ⟨109962, by rfl⟩ : syracuseStep 1172933 = 219925) (by norm_num)
theorem B779741 : Blo 519798 779741 := bbase (se 3 (by rfl) ⟨146201, by rfl⟩ : syracuseStep 779741 = 292403) (by norm_num)
theorem B878053 : Blo 519798 878053 := bbase (se 4 (by rfl) ⟨82317, by rfl⟩ : syracuseStep 878053 = 164635) (by norm_num)
theorem B779765 : Blo 519798 779765 := bbase (se 5 (by rfl) ⟨36551, by rfl⟩ : syracuseStep 779765 = 73103) (by norm_num)
theorem B779789 : Blo 519798 779789 := bbase (se 3 (by rfl) ⟨146210, by rfl⟩ : syracuseStep 779789 = 292421) (by norm_num)
theorem B1173005 : Blo 519798 1173005 := bbase (se 3 (by rfl) ⟨219938, by rfl⟩ : syracuseStep 1173005 = 439877) (by norm_num)
theorem B779813 : Blo 519798 779813 := bbase (se 4 (by rfl) ⟨73107, by rfl⟩ : syracuseStep 779813 = 146215) (by norm_num)
theorem B779837 : Blo 519798 779837 := bbase (se 3 (by rfl) ⟨146219, by rfl⟩ : syracuseStep 779837 = 292439) (by norm_num)
theorem B878141 : Blo 519798 878141 := bbase (se 3 (by rfl) ⟨164651, by rfl⟩ : syracuseStep 878141 = 329303) (by norm_num)
theorem B779861 : Blo 519798 779861 := bbase (se 8 (by rfl) ⟨4569, by rfl⟩ : syracuseStep 779861 = 9139) (by norm_num)
theorem B1173077 : Blo 519798 1173077 := bbase (se 8 (by rfl) ⟨6873, by rfl⟩ : syracuseStep 1173077 = 13747) (by norm_num)
theorem B779885 : Blo 519798 779885 := bbase (se 3 (by rfl) ⟨146228, by rfl⟩ : syracuseStep 779885 = 292457) (by norm_num)
theorem B779909 : Blo 519798 779909 := bbase (se 4 (by rfl) ⟨73116, by rfl⟩ : syracuseStep 779909 = 146233) (by norm_num)
theorem B779933 : Blo 519798 779933 := bbase (se 3 (by rfl) ⟨146237, by rfl⟩ : syracuseStep 779933 = 292475) (by norm_num)
theorem B1173149 : Blo 519798 1173149 := bbase (se 3 (by rfl) ⟨219965, by rfl⟩ : syracuseStep 1173149 = 439931) (by norm_num)
theorem B2123429 : Blo 519798 2123429 := bbase (se 4 (by rfl) ⟨199071, by rfl⟩ : syracuseStep 2123429 = 398143) (by norm_num)
theorem B779957 : Blo 519798 779957 := bbase (se 5 (by rfl) ⟨36560, by rfl⟩ : syracuseStep 779957 = 73121) (by norm_num)
theorem B2975413 : Blo 519798 2975413 := bbase (se 5 (by rfl) ⟨139472, by rfl⟩ : syracuseStep 2975413 = 278945) (by norm_num)
theorem B878269 : Blo 519798 878269 := bbase (se 3 (by rfl) ⟨164675, by rfl⟩ : syracuseStep 878269 = 329351) (by norm_num)
theorem B943805 : Blo 519798 943805 := bbase (se 3 (by rfl) ⟨176963, by rfl⟩ : syracuseStep 943805 = 353927) (by norm_num)
theorem B779981 : Blo 519798 779981 := bbase (se 3 (by rfl) ⟨146246, by rfl⟩ : syracuseStep 779981 = 292493) (by norm_num)
theorem B780005 : Blo 519798 780005 := bbase (se 4 (by rfl) ⟨73125, by rfl⟩ : syracuseStep 780005 = 146251) (by norm_num)
theorem B1173221 : Blo 519798 1173221 := bbase (se 4 (by rfl) ⟨109989, by rfl⟩ : syracuseStep 1173221 = 219979) (by norm_num)
theorem B1763045 : Blo 519798 1763045 := bbase (se 4 (by rfl) ⟨165285, by rfl⟩ : syracuseStep 1763045 = 330571) (by norm_num)
theorem B780029 : Blo 519798 780029 := bbase (se 3 (by rfl) ⟨146255, by rfl⟩ : syracuseStep 780029 = 292511) (by norm_num)
theorem B780053 : Blo 519798 780053 := bbase (se 6 (by rfl) ⟨18282, by rfl⟩ : syracuseStep 780053 = 36565) (by norm_num)
theorem B878357 : Blo 519798 878357 := bbase (se 6 (by rfl) ⟨20586, by rfl⟩ : syracuseStep 878357 = 41173) (by norm_num)
theorem B780077 : Blo 519798 780077 := bbase (se 3 (by rfl) ⟨146264, by rfl⟩ : syracuseStep 780077 = 292529) (by norm_num)
theorem B1173293 : Blo 519798 1173293 := bbase (se 3 (by rfl) ⟨219992, by rfl⟩ : syracuseStep 1173293 = 439985) (by norm_num)
theorem B780101 : Blo 519798 780101 := bbase (se 4 (by rfl) ⟨73134, by rfl⟩ : syracuseStep 780101 = 146269) (by norm_num)
theorem B780125 : Blo 519798 780125 := bbase (se 3 (by rfl) ⟨146273, by rfl⟩ : syracuseStep 780125 = 292547) (by norm_num)
theorem B780149 : Blo 519798 780149 := bbase (se 5 (by rfl) ⟨36569, by rfl⟩ : syracuseStep 780149 = 73139) (by norm_num)
theorem B1173365 : Blo 519798 1173365 := bbase (se 5 (by rfl) ⟨55001, by rfl⟩ : syracuseStep 1173365 = 110003) (by norm_num)
theorem B780173 : Blo 519798 780173 := bbase (se 3 (by rfl) ⟨146282, by rfl⟩ : syracuseStep 780173 = 292565) (by norm_num)
theorem B878485 : Blo 519798 878485 := bbase (se 6 (by rfl) ⟨20589, by rfl⟩ : syracuseStep 878485 = 41179) (by norm_num)
theorem B780197 : Blo 519798 780197 := bbase (se 4 (by rfl) ⟨73143, by rfl⟩ : syracuseStep 780197 = 146287) (by norm_num)
theorem B780221 : Blo 519798 780221 := bbase (se 3 (by rfl) ⟨146291, by rfl⟩ : syracuseStep 780221 = 292583) (by norm_num)
theorem B1173437 : Blo 519798 1173437 := bbase (se 3 (by rfl) ⟨220019, by rfl⟩ : syracuseStep 1173437 = 440039) (by norm_num)
theorem B780245 : Blo 519798 780245 := bbase (se 7 (by rfl) ⟨9143, by rfl⟩ : syracuseStep 780245 = 18287) (by norm_num)
theorem B780269 : Blo 519798 780269 := bbase (se 3 (by rfl) ⟨146300, by rfl⟩ : syracuseStep 780269 = 292601) (by norm_num)
theorem B878573 : Blo 519798 878573 := bbase (se 3 (by rfl) ⟨164732, by rfl⟩ : syracuseStep 878573 = 329465) (by norm_num)
theorem B780293 : Blo 519798 780293 := bbase (se 4 (by rfl) ⟨73152, by rfl⟩ : syracuseStep 780293 = 146305) (by norm_num)
theorem B1173509 : Blo 519798 1173509 := bbase (se 4 (by rfl) ⟨110016, by rfl⟩ : syracuseStep 1173509 = 220033) (by norm_num)
theorem B780317 : Blo 519798 780317 := bbase (se 3 (by rfl) ⟨146309, by rfl⟩ : syracuseStep 780317 = 292619) (by norm_num)
theorem B780341 : Blo 519798 780341 := bbase (se 5 (by rfl) ⟨36578, by rfl⟩ : syracuseStep 780341 = 73157) (by norm_num)
theorem B780365 : Blo 519798 780365 := bbase (se 3 (by rfl) ⟨146318, by rfl⟩ : syracuseStep 780365 = 292637) (by norm_num)
theorem B1173581 : Blo 519798 1173581 := bbase (se 3 (by rfl) ⟨220046, by rfl⟩ : syracuseStep 1173581 = 440093) (by norm_num)
theorem B780389 : Blo 519798 780389 := bbase (se 4 (by rfl) ⟨73161, by rfl⟩ : syracuseStep 780389 = 146323) (by norm_num)
theorem B878701 : Blo 519798 878701 := bbase (se 3 (by rfl) ⟨164756, by rfl⟩ : syracuseStep 878701 = 329513) (by norm_num)
theorem B780413 : Blo 519798 780413 := bbase (se 3 (by rfl) ⟨146327, by rfl⟩ : syracuseStep 780413 = 292655) (by norm_num)
theorem B780437 : Blo 519798 780437 := bbase (se 6 (by rfl) ⟨18291, by rfl⟩ : syracuseStep 780437 = 36583) (by norm_num)
theorem B1173653 : Blo 519798 1173653 := bbase (se 6 (by rfl) ⟨27507, by rfl⟩ : syracuseStep 1173653 = 55015) (by norm_num)
theorem B1763477 : Blo 519798 1763477 := bbase (se 6 (by rfl) ⟨41331, by rfl⟩ : syracuseStep 1763477 = 82663) (by norm_num)
theorem B2648213 : Blo 519798 2648213 := bbase (se 6 (by rfl) ⟨62067, by rfl⟩ : syracuseStep 2648213 = 124135) (by norm_num)
theorem B780461 : Blo 519798 780461 := bbase (se 3 (by rfl) ⟨146336, by rfl⟩ : syracuseStep 780461 = 292673) (by norm_num)
theorem B780485 : Blo 519798 780485 := bbase (se 4 (by rfl) ⟨73170, by rfl⟩ : syracuseStep 780485 = 146341) (by norm_num)
theorem B878789 : Blo 519798 878789 := bbase (se 4 (by rfl) ⟨82386, by rfl⟩ : syracuseStep 878789 = 164773) (by norm_num)
theorem B780509 : Blo 519798 780509 := bbase (se 3 (by rfl) ⟨146345, by rfl⟩ : syracuseStep 780509 = 292691) (by norm_num)
theorem B1173725 : Blo 519798 1173725 := bbase (se 3 (by rfl) ⟨220073, by rfl⟩ : syracuseStep 1173725 = 440147) (by norm_num)
theorem B780533 : Blo 519798 780533 := bbase (se 5 (by rfl) ⟨36587, by rfl⟩ : syracuseStep 780533 = 73175) (by norm_num)
theorem B780557 : Blo 519798 780557 := bbase (se 3 (by rfl) ⟨146354, by rfl⟩ : syracuseStep 780557 = 292709) (by norm_num)
theorem B780581 : Blo 519798 780581 := bbase (se 4 (by rfl) ⟨73179, by rfl⟩ : syracuseStep 780581 = 146359) (by norm_num)
theorem B1173797 : Blo 519798 1173797 := bbase (se 4 (by rfl) ⟨110043, by rfl⟩ : syracuseStep 1173797 = 220087) (by norm_num)
theorem B780605 : Blo 519798 780605 := bbase (se 3 (by rfl) ⟨146363, by rfl⟩ : syracuseStep 780605 = 292727) (by norm_num)
theorem B878917 : Blo 519798 878917 := bbase (se 4 (by rfl) ⟨82398, by rfl⟩ : syracuseStep 878917 = 164797) (by norm_num)
theorem B780629 : Blo 519798 780629 := bbase (se 10 (by rfl) ⟨1143, by rfl⟩ : syracuseStep 780629 = 2287) (by norm_num)
theorem B2222437 : Blo 519798 2222437 := bbase (se 4 (by rfl) ⟨208353, by rfl⟩ : syracuseStep 2222437 = 416707) (by norm_num)
theorem B780653 : Blo 519798 780653 := bbase (se 3 (by rfl) ⟨146372, by rfl⟩ : syracuseStep 780653 = 292745) (by norm_num)
theorem B1173869 : Blo 519798 1173869 := bbase (se 3 (by rfl) ⟨220100, by rfl⟩ : syracuseStep 1173869 = 440201) (by norm_num)
theorem B780677 : Blo 519798 780677 := bbase (se 4 (by rfl) ⟨73188, by rfl⟩ : syracuseStep 780677 = 146377) (by norm_num)
theorem B1337741 : Blo 519798 1337741 := bbase (se 3 (by rfl) ⟨250826, by rfl⟩ : syracuseStep 1337741 = 501653) (by norm_num)
theorem B780701 : Blo 519798 780701 := bbase (se 3 (by rfl) ⟨146381, by rfl⟩ : syracuseStep 780701 = 292763) (by norm_num)
theorem B879005 : Blo 519798 879005 := bbase (se 3 (by rfl) ⟨164813, by rfl⟩ : syracuseStep 879005 = 329627) (by norm_num)
theorem B780725 : Blo 519798 780725 := bbase (se 5 (by rfl) ⟨36596, by rfl⟩ : syracuseStep 780725 = 73193) (by norm_num)
theorem B1173941 : Blo 519798 1173941 := bbase (se 5 (by rfl) ⟨55028, by rfl⟩ : syracuseStep 1173941 = 110057) (by norm_num)
theorem B780749 : Blo 519798 780749 := bbase (se 3 (by rfl) ⟨146390, by rfl⟩ : syracuseStep 780749 = 292781) (by norm_num)
theorem B780773 : Blo 519798 780773 := bbase (se 4 (by rfl) ⟨73197, by rfl⟩ : syracuseStep 780773 = 146395) (by norm_num)
theorem B780797 : Blo 519798 780797 := bbase (se 3 (by rfl) ⟨146399, by rfl⟩ : syracuseStep 780797 = 292799) (by norm_num)
theorem B1174013 : Blo 519798 1174013 := bbase (se 3 (by rfl) ⟨220127, by rfl⟩ : syracuseStep 1174013 = 440255) (by norm_num)
theorem B780821 : Blo 519798 780821 := bbase (se 6 (by rfl) ⟨18300, by rfl⟩ : syracuseStep 780821 = 36601) (by norm_num)
theorem B879133 : Blo 519798 879133 := bbase (se 3 (by rfl) ⟨164837, by rfl⟩ : syracuseStep 879133 = 329675) (by norm_num)
theorem B780845 : Blo 519798 780845 := bbase (se 3 (by rfl) ⟨146408, by rfl⟩ : syracuseStep 780845 = 292817) (by norm_num)
theorem B780869 : Blo 519798 780869 := bbase (se 4 (by rfl) ⟨73206, by rfl⟩ : syracuseStep 780869 = 146413) (by norm_num)
theorem B1174085 : Blo 519798 1174085 := bbase (se 4 (by rfl) ⟨110070, by rfl⟩ : syracuseStep 1174085 = 220141) (by norm_num)
theorem B1763909 : Blo 519798 1763909 := bbase (se 4 (by rfl) ⟨165366, by rfl⟩ : syracuseStep 1763909 = 330733) (by norm_num)
theorem B780893 : Blo 519798 780893 := bbase (se 3 (by rfl) ⟨146417, by rfl⟩ : syracuseStep 780893 = 292835) (by norm_num)
theorem B780917 : Blo 519798 780917 := bbase (se 5 (by rfl) ⟨36605, by rfl⟩ : syracuseStep 780917 = 73211) (by norm_num)
theorem B879221 : Blo 519798 879221 := bbase (se 5 (by rfl) ⟨41213, by rfl⟩ : syracuseStep 879221 = 82427) (by norm_num)
theorem B780941 : Blo 519798 780941 := bbase (se 3 (by rfl) ⟨146426, by rfl⟩ : syracuseStep 780941 = 292853) (by norm_num)
theorem B1174157 : Blo 519798 1174157 := bbase (se 3 (by rfl) ⟨220154, by rfl⟩ : syracuseStep 1174157 = 440309) (by norm_num)
theorem B780965 : Blo 519798 780965 := bbase (se 4 (by rfl) ⟨73215, by rfl⟩ : syracuseStep 780965 = 146431) (by norm_num)
theorem B780989 : Blo 519798 780989 := bbase (se 3 (by rfl) ⟨146435, by rfl⟩ : syracuseStep 780989 = 292871) (by norm_num)
theorem B781013 : Blo 519798 781013 := bbase (se 7 (by rfl) ⟨9152, by rfl⟩ : syracuseStep 781013 = 18305) (by norm_num)
theorem B1174229 : Blo 519798 1174229 := bbase (se 7 (by rfl) ⟨13760, by rfl⟩ : syracuseStep 1174229 = 27521) (by norm_num)
theorem B781037 : Blo 519798 781037 := bbase (se 3 (by rfl) ⟨146444, by rfl⟩ : syracuseStep 781037 = 292889) (by norm_num)
theorem B879349 : Blo 519798 879349 := bbase (se 5 (by rfl) ⟨41219, by rfl⟩ : syracuseStep 879349 = 82439) (by norm_num)
theorem B781061 : Blo 519798 781061 := bbase (se 4 (by rfl) ⟨73224, by rfl⟩ : syracuseStep 781061 = 146449) (by norm_num)
theorem B781085 : Blo 519798 781085 := bbase (se 3 (by rfl) ⟨146453, by rfl⟩ : syracuseStep 781085 = 292907) (by norm_num)
theorem B1174301 : Blo 519798 1174301 := bbase (se 3 (by rfl) ⟨220181, by rfl⟩ : syracuseStep 1174301 = 440363) (by norm_num)
theorem B781109 : Blo 519798 781109 := bbase (se 5 (by rfl) ⟨36614, by rfl⟩ : syracuseStep 781109 = 73229) (by norm_num)
theorem B781133 : Blo 519798 781133 := bbase (se 3 (by rfl) ⟨146462, by rfl⟩ : syracuseStep 781133 = 292925) (by norm_num)
theorem B879437 : Blo 519798 879437 := bbase (se 3 (by rfl) ⟨164894, by rfl⟩ : syracuseStep 879437 = 329789) (by norm_num)
theorem B781157 : Blo 519798 781157 := bbase (se 4 (by rfl) ⟨73233, by rfl⟩ : syracuseStep 781157 = 146467) (by norm_num)
theorem B1174373 : Blo 519798 1174373 := bbase (se 4 (by rfl) ⟨110097, by rfl⟩ : syracuseStep 1174373 = 220195) (by norm_num)
theorem B781181 : Blo 519798 781181 := bbase (se 3 (by rfl) ⟨146471, by rfl⟩ : syracuseStep 781181 = 292943) (by norm_num)
theorem B781205 : Blo 519798 781205 := bbase (se 6 (by rfl) ⟨18309, by rfl⟩ : syracuseStep 781205 = 36619) (by norm_num)
theorem B781229 : Blo 519798 781229 := bbase (se 3 (by rfl) ⟨146480, by rfl⟩ : syracuseStep 781229 = 292961) (by norm_num)
theorem B1174445 : Blo 519798 1174445 := bbase (se 3 (by rfl) ⟨220208, by rfl⟩ : syracuseStep 1174445 = 440417) (by norm_num)
theorem B781253 : Blo 519798 781253 := bbase (se 4 (by rfl) ⟨73242, by rfl⟩ : syracuseStep 781253 = 146485) (by norm_num)
theorem B879565 : Blo 519798 879565 := bbase (se 3 (by rfl) ⟨164918, by rfl⟩ : syracuseStep 879565 = 329837) (by norm_num)
theorem B781277 : Blo 519798 781277 := bbase (se 3 (by rfl) ⟨146489, by rfl⟩ : syracuseStep 781277 = 292979) (by norm_num)
theorem B781301 : Blo 519798 781301 := bbase (se 5 (by rfl) ⟨36623, by rfl⟩ : syracuseStep 781301 = 73247) (by norm_num)
theorem B1174517 : Blo 519798 1174517 := bbase (se 5 (by rfl) ⟨55055, by rfl⟩ : syracuseStep 1174517 = 110111) (by norm_num)
theorem B1764341 : Blo 519798 1764341 := bbase (se 5 (by rfl) ⟨82703, by rfl⟩ : syracuseStep 1764341 = 165407) (by norm_num)
theorem B781325 : Blo 519798 781325 := bbase (se 3 (by rfl) ⟨146498, by rfl⟩ : syracuseStep 781325 = 292997) (by norm_num)
theorem B781349 : Blo 519798 781349 := bbase (se 4 (by rfl) ⟨73251, by rfl⟩ : syracuseStep 781349 = 146503) (by norm_num)
theorem B879653 : Blo 519798 879653 := bbase (se 4 (by rfl) ⟨82467, by rfl⟩ : syracuseStep 879653 = 164935) (by norm_num)
theorem B781373 : Blo 519798 781373 := bbase (se 3 (by rfl) ⟨146507, by rfl⟩ : syracuseStep 781373 = 293015) (by norm_num)
theorem B1174589 : Blo 519798 1174589 := bbase (se 3 (by rfl) ⟨220235, by rfl⟩ : syracuseStep 1174589 = 440471) (by norm_num)
theorem B781397 : Blo 519798 781397 := bbase (se 8 (by rfl) ⟨4578, by rfl⟩ : syracuseStep 781397 = 9157) (by norm_num)
theorem B584797 : Blo 519798 584797 := bbase (se 3 (by rfl) ⟨109649, by rfl⟩ : syracuseStep 584797 = 219299) (by norm_num)
theorem B781421 : Blo 519798 781421 := bbase (se 3 (by rfl) ⟨146516, by rfl⟩ : syracuseStep 781421 = 293033) (by norm_num)
theorem B584833 : Blo 519798 584833 := bbase (se 2 (by rfl) ⟨219312, by rfl⟩ : syracuseStep 584833 = 438625) (by norm_num)
theorem B781445 : Blo 519798 781445 := bbase (se 4 (by rfl) ⟨73260, by rfl⟩ : syracuseStep 781445 = 146521) (by norm_num)
theorem B1174661 : Blo 519798 1174661 := bbase (se 4 (by rfl) ⟨110124, by rfl⟩ : syracuseStep 1174661 = 220249) (by norm_num)
theorem B781469 : Blo 519798 781469 := bbase (se 3 (by rfl) ⟨146525, by rfl⟩ : syracuseStep 781469 = 293051) (by norm_num)
theorem B584869 : Blo 519798 584869 := bbase (se 4 (by rfl) ⟨54831, by rfl⟩ : syracuseStep 584869 = 109663) (by norm_num)
theorem B879781 : Blo 519798 879781 := bbase (se 4 (by rfl) ⟨82479, by rfl⟩ : syracuseStep 879781 = 164959) (by norm_num)
theorem B781493 : Blo 519798 781493 := bbase (se 5 (by rfl) ⟨36632, by rfl⟩ : syracuseStep 781493 = 73265) (by norm_num)
theorem B584905 : Blo 519798 584905 := bbase (se 2 (by rfl) ⟨219339, by rfl⟩ : syracuseStep 584905 = 438679) (by norm_num)
theorem B781517 : Blo 519798 781517 := bbase (se 3 (by rfl) ⟨146534, by rfl⟩ : syracuseStep 781517 = 293069) (by norm_num)
theorem B1174733 : Blo 519798 1174733 := bbase (se 3 (by rfl) ⟨220262, by rfl⟩ : syracuseStep 1174733 = 440525) (by norm_num)
theorem B781541 : Blo 519798 781541 := bbase (se 4 (by rfl) ⟨73269, by rfl⟩ : syracuseStep 781541 = 146539) (by norm_num)
theorem B584941 : Blo 519798 584941 := bbase (se 3 (by rfl) ⟨109676, by rfl⟩ : syracuseStep 584941 = 219353) (by norm_num)
theorem B781565 : Blo 519798 781565 := bbase (se 3 (by rfl) ⟨146543, by rfl⟩ : syracuseStep 781565 = 293087) (by norm_num)
theorem B879869 : Blo 519798 879869 := bbase (se 3 (by rfl) ⟨164975, by rfl⟩ : syracuseStep 879869 = 329951) (by norm_num)
theorem B584977 : Blo 519798 584977 := bbase (se 2 (by rfl) ⟨219366, by rfl⟩ : syracuseStep 584977 = 438733) (by norm_num)
theorem B781589 : Blo 519798 781589 := bbase (se 6 (by rfl) ⟨18318, by rfl⟩ : syracuseStep 781589 = 36637) (by norm_num)
theorem B1174805 : Blo 519798 1174805 := bbase (se 6 (by rfl) ⟨27534, by rfl⟩ : syracuseStep 1174805 = 55069) (by norm_num)
theorem B781613 : Blo 519798 781613 := bbase (se 3 (by rfl) ⟨146552, by rfl⟩ : syracuseStep 781613 = 293105) (by norm_num)
theorem B585013 : Blo 519798 585013 := bbase (se 5 (by rfl) ⟨27422, by rfl⟩ : syracuseStep 585013 = 54845) (by norm_num)
theorem B781637 : Blo 519798 781637 := bbase (se 4 (by rfl) ⟨73278, by rfl⟩ : syracuseStep 781637 = 146557) (by norm_num)
theorem B585049 : Blo 519798 585049 := bbase (se 2 (by rfl) ⟨219393, by rfl⟩ : syracuseStep 585049 = 438787) (by norm_num)
theorem B781661 : Blo 519798 781661 := bbase (se 3 (by rfl) ⟨146561, by rfl⟩ : syracuseStep 781661 = 293123) (by norm_num)
theorem B1174877 : Blo 519798 1174877 := bbase (se 3 (by rfl) ⟨220289, by rfl⟩ : syracuseStep 1174877 = 440579) (by norm_num)
theorem B781685 : Blo 519798 781685 := bbase (se 5 (by rfl) ⟨36641, by rfl⟩ : syracuseStep 781685 = 73283) (by norm_num)
theorem B585085 : Blo 519798 585085 := bbase (se 3 (by rfl) ⟨109703, by rfl⟩ : syracuseStep 585085 = 219407) (by norm_num)
theorem B879997 : Blo 519798 879997 := bbase (se 3 (by rfl) ⟨164999, by rfl⟩ : syracuseStep 879997 = 329999) (by norm_num)
theorem B781709 : Blo 519798 781709 := bbase (se 3 (by rfl) ⟨146570, by rfl⟩ : syracuseStep 781709 = 293141) (by norm_num)
theorem B585121 : Blo 519798 585121 := bbase (se 2 (by rfl) ⟨219420, by rfl⟩ : syracuseStep 585121 = 438841) (by norm_num)
theorem B781733 : Blo 519798 781733 := bbase (se 4 (by rfl) ⟨73287, by rfl⟩ : syracuseStep 781733 = 146575) (by norm_num)
theorem B1174949 : Blo 519798 1174949 := bbase (se 4 (by rfl) ⟨110151, by rfl⟩ : syracuseStep 1174949 = 220303) (by norm_num)
theorem B1764773 : Blo 519798 1764773 := bbase (se 4 (by rfl) ⟨165447, by rfl⟩ : syracuseStep 1764773 = 330895) (by norm_num)
theorem B2649509 : Blo 519798 2649509 := bbase (se 4 (by rfl) ⟨248391, by rfl⟩ : syracuseStep 2649509 = 496783) (by norm_num)
theorem B781757 : Blo 519798 781757 := bbase (se 3 (by rfl) ⟨146579, by rfl⟩ : syracuseStep 781757 = 293159) (by norm_num)
theorem B585157 : Blo 519798 585157 := bbase (se 4 (by rfl) ⟨54858, by rfl⟩ : syracuseStep 585157 = 109717) (by norm_num)
theorem B781781 : Blo 519798 781781 := bbase (se 7 (by rfl) ⟨9161, by rfl⟩ : syracuseStep 781781 = 18323) (by norm_num)
theorem B880085 : Blo 519798 880085 := bbase (se 7 (by rfl) ⟨10313, by rfl⟩ : syracuseStep 880085 = 20627) (by norm_num)
theorem B585193 : Blo 519798 585193 := bbase (se 2 (by rfl) ⟨219447, by rfl⟩ : syracuseStep 585193 = 438895) (by norm_num)
theorem B781805 : Blo 519798 781805 := bbase (se 3 (by rfl) ⟨146588, by rfl⟩ : syracuseStep 781805 = 293177) (by norm_num)
theorem B1175021 : Blo 519798 1175021 := bbase (se 3 (by rfl) ⟨220316, by rfl⟩ : syracuseStep 1175021 = 440633) (by norm_num)
theorem B781829 : Blo 519798 781829 := bbase (se 4 (by rfl) ⟨73296, by rfl⟩ : syracuseStep 781829 = 146593) (by norm_num)
theorem B585229 : Blo 519798 585229 := bbase (se 3 (by rfl) ⟨109730, by rfl⟩ : syracuseStep 585229 = 219461) (by norm_num)
theorem B781853 : Blo 519798 781853 := bbase (se 3 (by rfl) ⟨146597, by rfl⟩ : syracuseStep 781853 = 293195) (by norm_num)
theorem B1666597 : Blo 519798 1666597 := bbase (se 4 (by rfl) ⟨156243, by rfl⟩ : syracuseStep 1666597 = 312487) (by norm_num)
theorem B585265 : Blo 519798 585265 := bbase (se 2 (by rfl) ⟨219474, by rfl⟩ : syracuseStep 585265 = 438949) (by norm_num)
theorem B781877 : Blo 519798 781877 := bbase (se 5 (by rfl) ⟨36650, by rfl⟩ : syracuseStep 781877 = 73301) (by norm_num)
theorem B1175093 : Blo 519798 1175093 := bbase (se 5 (by rfl) ⟨55082, by rfl⟩ : syracuseStep 1175093 = 110165) (by norm_num)
theorem B781901 : Blo 519798 781901 := bbase (se 3 (by rfl) ⟨146606, by rfl⟩ : syracuseStep 781901 = 293213) (by norm_num)
theorem B585301 : Blo 519798 585301 := bbase (se 8 (by rfl) ⟨3429, by rfl⟩ : syracuseStep 585301 = 6859) (by norm_num)
theorem B880213 : Blo 519798 880213 := bbase (se 8 (by rfl) ⟨5157, by rfl⟩ : syracuseStep 880213 = 10315) (by norm_num)
theorem B781925 : Blo 519798 781925 := bbase (se 4 (by rfl) ⟨73305, by rfl⟩ : syracuseStep 781925 = 146611) (by norm_num)
theorem B2977397 : Blo 519798 2977397 := bbase (se 5 (by rfl) ⟨139565, by rfl⟩ : syracuseStep 2977397 = 279131) (by norm_num)
theorem B585337 : Blo 519798 585337 := bbase (se 2 (by rfl) ⟨219501, by rfl⟩ : syracuseStep 585337 = 439003) (by norm_num)
theorem B781949 : Blo 519798 781949 := bbase (se 3 (by rfl) ⟨146615, by rfl⟩ : syracuseStep 781949 = 293231) (by norm_num)
theorem B1175165 : Blo 519798 1175165 := bbase (se 3 (by rfl) ⟨220343, by rfl⟩ : syracuseStep 1175165 = 440687) (by norm_num)
theorem B781973 : Blo 519798 781973 := bbase (se 6 (by rfl) ⟨18327, by rfl⟩ : syracuseStep 781973 = 36655) (by norm_num)
theorem B585373 : Blo 519798 585373 := bbase (se 3 (by rfl) ⟨109757, by rfl⟩ : syracuseStep 585373 = 219515) (by norm_num)
theorem B781997 : Blo 519798 781997 := bbase (se 3 (by rfl) ⟨146624, by rfl⟩ : syracuseStep 781997 = 293249) (by norm_num)
theorem B880301 : Blo 519798 880301 := bbase (se 3 (by rfl) ⟨165056, by rfl⟩ : syracuseStep 880301 = 330113) (by norm_num)
theorem B585409 : Blo 519798 585409 := bbase (se 2 (by rfl) ⟨219528, by rfl⟩ : syracuseStep 585409 = 439057) (by norm_num)
theorem B782021 : Blo 519798 782021 := bbase (se 4 (by rfl) ⟨73314, by rfl⟩ : syracuseStep 782021 = 146629) (by norm_num)
theorem B1175237 : Blo 519798 1175237 := bbase (se 4 (by rfl) ⟨110178, by rfl⟩ : syracuseStep 1175237 = 220357) (by norm_num)
theorem B782045 : Blo 519798 782045 := bbase (se 3 (by rfl) ⟨146633, by rfl⟩ : syracuseStep 782045 = 293267) (by norm_num)
theorem B585445 : Blo 519798 585445 := bbase (se 4 (by rfl) ⟨54885, by rfl⟩ : syracuseStep 585445 = 109771) (by norm_num)
theorem B782069 : Blo 519798 782069 := bbase (se 5 (by rfl) ⟨36659, by rfl⟩ : syracuseStep 782069 = 73319) (by norm_num)
theorem B585481 : Blo 519798 585481 := bbase (se 2 (by rfl) ⟨219555, by rfl⟩ : syracuseStep 585481 = 439111) (by norm_num)
theorem B782093 : Blo 519798 782093 := bbase (se 3 (by rfl) ⟨146642, by rfl⟩ : syracuseStep 782093 = 293285) (by norm_num)
theorem B1175309 : Blo 519798 1175309 := bbase (se 3 (by rfl) ⟨220370, by rfl⟩ : syracuseStep 1175309 = 440741) (by norm_num)
theorem B782117 : Blo 519798 782117 := bbase (se 4 (by rfl) ⟨73323, by rfl⟩ : syracuseStep 782117 = 146647) (by norm_num)
theorem B585517 : Blo 519798 585517 := bbase (se 3 (by rfl) ⟨109784, by rfl⟩ : syracuseStep 585517 = 219569) (by norm_num)
theorem B880429 : Blo 519798 880429 := bbase (se 3 (by rfl) ⟨165080, by rfl⟩ : syracuseStep 880429 = 330161) (by norm_num)
theorem B782141 : Blo 519798 782141 := bbase (se 3 (by rfl) ⟨146651, by rfl⟩ : syracuseStep 782141 = 293303) (by norm_num)
theorem B585553 : Blo 519798 585553 := bbase (se 2 (by rfl) ⟨219582, by rfl⟩ : syracuseStep 585553 = 439165) (by norm_num)
theorem B782165 : Blo 519798 782165 := bbase (se 9 (by rfl) ⟨2291, by rfl⟩ : syracuseStep 782165 = 4583) (by norm_num)
theorem B1175381 : Blo 519798 1175381 := bbase (se 9 (by rfl) ⟨3443, by rfl⟩ : syracuseStep 1175381 = 6887) (by norm_num)
theorem B1765205 : Blo 519798 1765205 := bbase (se 9 (by rfl) ⟨5171, by rfl⟩ : syracuseStep 1765205 = 10343) (by norm_num)
theorem B782189 : Blo 519798 782189 := bbase (se 3 (by rfl) ⟨146660, by rfl⟩ : syracuseStep 782189 = 293321) (by norm_num)
theorem B585589 : Blo 519798 585589 := bbase (se 5 (by rfl) ⟨27449, by rfl⟩ : syracuseStep 585589 = 54899) (by norm_num)
theorem B782213 : Blo 519798 782213 := bbase (se 4 (by rfl) ⟨73332, by rfl⟩ : syracuseStep 782213 = 146665) (by norm_num)
theorem B880517 : Blo 519798 880517 := bbase (se 4 (by rfl) ⟨82548, by rfl⟩ : syracuseStep 880517 = 165097) (by norm_num)
theorem B585625 : Blo 519798 585625 := bbase (se 2 (by rfl) ⟨219609, by rfl⟩ : syracuseStep 585625 = 439219) (by norm_num)
theorem B782237 : Blo 519798 782237 := bbase (se 3 (by rfl) ⟨146669, by rfl⟩ : syracuseStep 782237 = 293339) (by norm_num)
theorem B1175453 : Blo 519798 1175453 := bbase (se 3 (by rfl) ⟨220397, by rfl⟩ : syracuseStep 1175453 = 440795) (by norm_num)
theorem B782261 : Blo 519798 782261 := bbase (se 5 (by rfl) ⟨36668, by rfl⟩ : syracuseStep 782261 = 73337) (by norm_num)
theorem B585661 : Blo 519798 585661 := bbase (se 3 (by rfl) ⟨109811, by rfl⟩ : syracuseStep 585661 = 219623) (by norm_num)
theorem B782285 : Blo 519798 782285 := bbase (se 3 (by rfl) ⟨146678, by rfl⟩ : syracuseStep 782285 = 293357) (by norm_num)
theorem B585697 : Blo 519798 585697 := bbase (se 2 (by rfl) ⟨219636, by rfl⟩ : syracuseStep 585697 = 439273) (by norm_num)
theorem B782309 : Blo 519798 782309 := bbase (se 4 (by rfl) ⟨73341, by rfl⟩ : syracuseStep 782309 = 146683) (by norm_num)
theorem B1175525 : Blo 519798 1175525 := bbase (se 4 (by rfl) ⟨110205, by rfl⟩ : syracuseStep 1175525 = 220411) (by norm_num)
theorem B782333 : Blo 519798 782333 := bbase (se 3 (by rfl) ⟨146687, by rfl⟩ : syracuseStep 782333 = 293375) (by norm_num)
theorem B585733 : Blo 519798 585733 := bbase (se 4 (by rfl) ⟨54912, by rfl⟩ : syracuseStep 585733 = 109825) (by norm_num)
theorem B880645 : Blo 519798 880645 := bbase (se 4 (by rfl) ⟨82560, by rfl⟩ : syracuseStep 880645 = 165121) (by norm_num)
theorem B782357 : Blo 519798 782357 := bbase (se 6 (by rfl) ⟨18336, by rfl⟩ : syracuseStep 782357 = 36673) (by norm_num)
theorem B585769 : Blo 519798 585769 := bbase (se 2 (by rfl) ⟨219663, by rfl⟩ : syracuseStep 585769 = 439327) (by norm_num)
theorem B782381 : Blo 519798 782381 := bbase (se 3 (by rfl) ⟨146696, by rfl⟩ : syracuseStep 782381 = 293393) (by norm_num)
theorem B1175597 : Blo 519798 1175597 := bbase (se 3 (by rfl) ⟨220424, by rfl⟩ : syracuseStep 1175597 = 440849) (by norm_num)
theorem B782405 : Blo 519798 782405 := bbase (se 4 (by rfl) ⟨73350, by rfl⟩ : syracuseStep 782405 = 146701) (by norm_num)
theorem B585805 : Blo 519798 585805 := bbase (se 3 (by rfl) ⟨109838, by rfl⟩ : syracuseStep 585805 = 219677) (by norm_num)
theorem B782429 : Blo 519798 782429 := bbase (se 3 (by rfl) ⟨146705, by rfl⟩ : syracuseStep 782429 = 293411) (by norm_num)
theorem B880733 : Blo 519798 880733 := bbase (se 3 (by rfl) ⟨165137, by rfl⟩ : syracuseStep 880733 = 330275) (by norm_num)
theorem B585841 : Blo 519798 585841 := bbase (se 2 (by rfl) ⟨219690, by rfl⟩ : syracuseStep 585841 = 439381) (by norm_num)
theorem B782453 : Blo 519798 782453 := bbase (se 5 (by rfl) ⟨36677, by rfl⟩ : syracuseStep 782453 = 73355) (by norm_num)
theorem B1175669 : Blo 519798 1175669 := bbase (se 5 (by rfl) ⟨55109, by rfl⟩ : syracuseStep 1175669 = 110219) (by norm_num)
theorem B782477 : Blo 519798 782477 := bbase (se 3 (by rfl) ⟨146714, by rfl⟩ : syracuseStep 782477 = 293429) (by norm_num)
theorem B585877 : Blo 519798 585877 := bbase (se 6 (by rfl) ⟨13731, by rfl⟩ : syracuseStep 585877 = 27463) (by norm_num)
theorem B782501 : Blo 519798 782501 := bbase (se 4 (by rfl) ⟨73359, by rfl⟩ : syracuseStep 782501 = 146719) (by norm_num)
theorem B585913 : Blo 519798 585913 := bbase (se 2 (by rfl) ⟨219717, by rfl⟩ : syracuseStep 585913 = 439435) (by norm_num)
theorem B782525 : Blo 519798 782525 := bbase (se 3 (by rfl) ⟨146723, by rfl⟩ : syracuseStep 782525 = 293447) (by norm_num)
theorem B1175741 : Blo 519798 1175741 := bbase (se 3 (by rfl) ⟨220451, by rfl⟩ : syracuseStep 1175741 = 440903) (by norm_num)
theorem B782549 : Blo 519798 782549 := bbase (se 7 (by rfl) ⟨9170, by rfl⟩ : syracuseStep 782549 = 18341) (by norm_num)
theorem B585949 : Blo 519798 585949 := bbase (se 3 (by rfl) ⟨109865, by rfl⟩ : syracuseStep 585949 = 219731) (by norm_num)
theorem B880861 : Blo 519798 880861 := bbase (se 3 (by rfl) ⟨165161, by rfl⟩ : syracuseStep 880861 = 330323) (by norm_num)
theorem B782573 : Blo 519798 782573 := bbase (se 3 (by rfl) ⟨146732, by rfl⟩ : syracuseStep 782573 = 293465) (by norm_num)
theorem B585985 : Blo 519798 585985 := bbase (se 2 (by rfl) ⟨219744, by rfl⟩ : syracuseStep 585985 = 439489) (by norm_num)
theorem B782597 : Blo 519798 782597 := bbase (se 4 (by rfl) ⟨73368, by rfl⟩ : syracuseStep 782597 = 146737) (by norm_num)
theorem B1175813 : Blo 519798 1175813 := bbase (se 4 (by rfl) ⟨110232, by rfl⟩ : syracuseStep 1175813 = 220465) (by norm_num)
theorem B1765637 : Blo 519798 1765637 := bbase (se 4 (by rfl) ⟨165528, by rfl⟩ : syracuseStep 1765637 = 331057) (by norm_num)
theorem B782621 : Blo 519798 782621 := bbase (se 3 (by rfl) ⟨146741, by rfl⟩ : syracuseStep 782621 = 293483) (by norm_num)
theorem B586021 : Blo 519798 586021 := bbase (se 4 (by rfl) ⟨54939, by rfl⟩ : syracuseStep 586021 = 109879) (by norm_num)
theorem B782645 : Blo 519798 782645 := bbase (se 5 (by rfl) ⟨36686, by rfl⟩ : syracuseStep 782645 = 73373) (by norm_num)
theorem B880949 : Blo 519798 880949 := bbase (se 5 (by rfl) ⟨41294, by rfl⟩ : syracuseStep 880949 = 82589) (by norm_num)
theorem B586057 : Blo 519798 586057 := bbase (se 2 (by rfl) ⟨219771, by rfl⟩ : syracuseStep 586057 = 439543) (by norm_num)
theorem B782669 : Blo 519798 782669 := bbase (se 3 (by rfl) ⟨146750, by rfl⟩ : syracuseStep 782669 = 293501) (by norm_num)
theorem B1175885 : Blo 519798 1175885 := bbase (se 3 (by rfl) ⟨220478, by rfl⟩ : syracuseStep 1175885 = 440957) (by norm_num)
theorem B1339733 : Blo 519798 1339733 := bbase (se 10 (by rfl) ⟨1962, by rfl⟩ : syracuseStep 1339733 = 3925) (by norm_num)
theorem B782693 : Blo 519798 782693 := bbase (se 4 (by rfl) ⟨73377, by rfl⟩ : syracuseStep 782693 = 146755) (by norm_num)
theorem B586093 : Blo 519798 586093 := bbase (se 3 (by rfl) ⟨109892, by rfl⟩ : syracuseStep 586093 = 219785) (by norm_num)
theorem B782717 : Blo 519798 782717 := bbase (se 3 (by rfl) ⟨146759, by rfl⟩ : syracuseStep 782717 = 293519) (by norm_num)
theorem B586129 : Blo 519798 586129 := bbase (se 2 (by rfl) ⟨219798, by rfl⟩ : syracuseStep 586129 = 439597) (by norm_num)
theorem B782741 : Blo 519798 782741 := bbase (se 6 (by rfl) ⟨18345, by rfl⟩ : syracuseStep 782741 = 36691) (by norm_num)
theorem B1175957 : Blo 519798 1175957 := bbase (se 6 (by rfl) ⟨27561, by rfl⟩ : syracuseStep 1175957 = 55123) (by norm_num)
theorem B782765 : Blo 519798 782765 := bbase (se 3 (by rfl) ⟨146768, by rfl⟩ : syracuseStep 782765 = 293537) (by norm_num)
theorem B586165 : Blo 519798 586165 := bbase (se 5 (by rfl) ⟨27476, by rfl⟩ : syracuseStep 586165 = 54953) (by norm_num)
theorem B881077 : Blo 519798 881077 := bbase (se 5 (by rfl) ⟨41300, by rfl⟩ : syracuseStep 881077 = 82601) (by norm_num)
theorem B782789 : Blo 519798 782789 := bbase (se 4 (by rfl) ⟨73386, by rfl⟩ : syracuseStep 782789 = 146773) (by norm_num)
theorem B586201 : Blo 519798 586201 := bbase (se 2 (by rfl) ⟨219825, by rfl⟩ : syracuseStep 586201 = 439651) (by norm_num)
theorem B782813 : Blo 519798 782813 := bbase (se 3 (by rfl) ⟨146777, by rfl⟩ : syracuseStep 782813 = 293555) (by norm_num)
theorem B1176029 : Blo 519798 1176029 := bbase (se 3 (by rfl) ⟨220505, by rfl⟩ : syracuseStep 1176029 = 441011) (by norm_num)
theorem B782837 : Blo 519798 782837 := bbase (se 5 (by rfl) ⟨36695, by rfl⟩ : syracuseStep 782837 = 73391) (by norm_num)
theorem B586237 : Blo 519798 586237 := bbase (se 3 (by rfl) ⟨109919, by rfl⟩ : syracuseStep 586237 = 219839) (by norm_num)
theorem B782861 : Blo 519798 782861 := bbase (se 3 (by rfl) ⟨146786, by rfl⟩ : syracuseStep 782861 = 293573) (by norm_num)
theorem B881165 : Blo 519798 881165 := bbase (se 3 (by rfl) ⟨165218, by rfl⟩ : syracuseStep 881165 = 330437) (by norm_num)
theorem B586273 : Blo 519798 586273 := bbase (se 2 (by rfl) ⟨219852, by rfl⟩ : syracuseStep 586273 = 439705) (by norm_num)
theorem B782885 : Blo 519798 782885 := bbase (se 4 (by rfl) ⟨73395, by rfl⟩ : syracuseStep 782885 = 146791) (by norm_num)
theorem B1176101 : Blo 519798 1176101 := bbase (se 4 (by rfl) ⟨110259, by rfl⟩ : syracuseStep 1176101 = 220519) (by norm_num)
theorem B1274405 : Blo 519798 1274405 := bbase (se 4 (by rfl) ⟨119475, by rfl⟩ : syracuseStep 1274405 = 238951) (by norm_num)
theorem B782909 : Blo 519798 782909 := bbase (se 3 (by rfl) ⟨146795, by rfl⟩ : syracuseStep 782909 = 293591) (by norm_num)
theorem B586309 : Blo 519798 586309 := bbase (se 4 (by rfl) ⟨54966, by rfl⟩ : syracuseStep 586309 = 109933) (by norm_num)
theorem B782933 : Blo 519798 782933 := bbase (se 8 (by rfl) ⟨4587, by rfl⟩ : syracuseStep 782933 = 9175) (by norm_num)
theorem B586345 : Blo 519798 586345 := bbase (se 2 (by rfl) ⟨219879, by rfl⟩ : syracuseStep 586345 = 439759) (by norm_num)
theorem B782957 : Blo 519798 782957 := bbase (se 3 (by rfl) ⟨146804, by rfl⟩ : syracuseStep 782957 = 293609) (by norm_num)
theorem B1176173 : Blo 519798 1176173 := bbase (se 3 (by rfl) ⟨220532, by rfl⟩ : syracuseStep 1176173 = 441065) (by norm_num)
theorem B782981 : Blo 519798 782981 := bbase (se 4 (by rfl) ⟨73404, by rfl⟩ : syracuseStep 782981 = 146809) (by norm_num)
theorem B586381 : Blo 519798 586381 := bbase (se 3 (by rfl) ⟨109946, by rfl⟩ : syracuseStep 586381 = 219893) (by norm_num)
theorem B881293 : Blo 519798 881293 := bbase (se 3 (by rfl) ⟨165242, by rfl⟩ : syracuseStep 881293 = 330485) (by norm_num)
theorem B783005 : Blo 519798 783005 := bbase (se 3 (by rfl) ⟨146813, by rfl⟩ : syracuseStep 783005 = 293627) (by norm_num)
theorem B586417 : Blo 519798 586417 := bbase (se 2 (by rfl) ⟨219906, by rfl⟩ : syracuseStep 586417 = 439813) (by norm_num)
theorem B783029 : Blo 519798 783029 := bbase (se 5 (by rfl) ⟨36704, by rfl⟩ : syracuseStep 783029 = 73409) (by norm_num)
theorem B1176245 : Blo 519798 1176245 := bbase (se 5 (by rfl) ⟨55136, by rfl⟩ : syracuseStep 1176245 = 110273) (by norm_num)
theorem B1766069 : Blo 519798 1766069 := bbase (se 5 (by rfl) ⟨82784, by rfl⟩ : syracuseStep 1766069 = 165569) (by norm_num)
theorem B2650805 : Blo 519798 2650805 := bbase (se 5 (by rfl) ⟨124256, by rfl⟩ : syracuseStep 2650805 = 248513) (by norm_num)
theorem B783053 : Blo 519798 783053 := bbase (se 3 (by rfl) ⟨146822, by rfl⟩ : syracuseStep 783053 = 293645) (by norm_num)
theorem B586453 : Blo 519798 586453 := bbase (se 7 (by rfl) ⟨6872, by rfl⟩ : syracuseStep 586453 = 13745) (by norm_num)
theorem B783077 : Blo 519798 783077 := bbase (se 4 (by rfl) ⟨73413, by rfl⟩ : syracuseStep 783077 = 146827) (by norm_num)
theorem B881381 : Blo 519798 881381 := bbase (se 4 (by rfl) ⟨82629, by rfl⟩ : syracuseStep 881381 = 165259) (by norm_num)
theorem B586489 : Blo 519798 586489 := bbase (se 2 (by rfl) ⟨219933, by rfl⟩ : syracuseStep 586489 = 439867) (by norm_num)
theorem B783101 : Blo 519798 783101 := bbase (se 3 (by rfl) ⟨146831, by rfl⟩ : syracuseStep 783101 = 293663) (by norm_num)
theorem B1176317 : Blo 519798 1176317 := bbase (se 3 (by rfl) ⟨220559, by rfl⟩ : syracuseStep 1176317 = 441119) (by norm_num)
theorem B4223765 : Blo 519798 4223765 := bbase (se 6 (by rfl) ⟨98994, by rfl⟩ : syracuseStep 4223765 = 197989) (by norm_num)
theorem B783125 : Blo 519798 783125 := bbase (se 6 (by rfl) ⟨18354, by rfl⟩ : syracuseStep 783125 = 36709) (by norm_num)
theorem B586525 : Blo 519798 586525 := bbase (se 3 (by rfl) ⟨109973, by rfl⟩ : syracuseStep 586525 = 219947) (by norm_num)
theorem B783149 : Blo 519798 783149 := bbase (se 3 (by rfl) ⟨146840, by rfl⟩ : syracuseStep 783149 = 293681) (by norm_num)
theorem B586561 : Blo 519798 586561 := bbase (se 2 (by rfl) ⟨219960, by rfl⟩ : syracuseStep 586561 = 439921) (by norm_num)
theorem B783173 : Blo 519798 783173 := bbase (se 4 (by rfl) ⟨73422, by rfl⟩ : syracuseStep 783173 = 146845) (by norm_num)
theorem B1176389 : Blo 519798 1176389 := bbase (se 4 (by rfl) ⟨110286, by rfl⟩ : syracuseStep 1176389 = 220573) (by norm_num)
theorem B783197 : Blo 519798 783197 := bbase (se 3 (by rfl) ⟨146849, by rfl⟩ : syracuseStep 783197 = 293699) (by norm_num)
theorem B586597 : Blo 519798 586597 := bbase (se 4 (by rfl) ⟨54993, by rfl⟩ : syracuseStep 586597 = 109987) (by norm_num)
theorem B881509 : Blo 519798 881509 := bbase (se 4 (by rfl) ⟨82641, by rfl⟩ : syracuseStep 881509 = 165283) (by norm_num)
theorem B783221 : Blo 519798 783221 := bbase (se 5 (by rfl) ⟨36713, by rfl⟩ : syracuseStep 783221 = 73427) (by norm_num)
theorem B586633 : Blo 519798 586633 := bbase (se 2 (by rfl) ⟨219987, by rfl⟩ : syracuseStep 586633 = 439975) (by norm_num)
theorem B783245 : Blo 519798 783245 := bbase (se 3 (by rfl) ⟨146858, by rfl⟩ : syracuseStep 783245 = 293717) (by norm_num)
theorem B1176461 : Blo 519798 1176461 := bbase (se 3 (by rfl) ⟨220586, by rfl⟩ : syracuseStep 1176461 = 441173) (by norm_num)
theorem B783269 : Blo 519798 783269 := bbase (se 4 (by rfl) ⟨73431, by rfl⟩ : syracuseStep 783269 = 146863) (by norm_num)
theorem B586669 : Blo 519798 586669 := bbase (se 3 (by rfl) ⟨110000, by rfl⟩ : syracuseStep 586669 = 220001) (by norm_num)
theorem B783293 : Blo 519798 783293 := bbase (se 3 (by rfl) ⟨146867, by rfl⟩ : syracuseStep 783293 = 293735) (by norm_num)
theorem B881597 : Blo 519798 881597 := bbase (se 3 (by rfl) ⟨165299, by rfl⟩ : syracuseStep 881597 = 330599) (by norm_num)
theorem B1110989 : Blo 519798 1110989 := bbase (se 3 (by rfl) ⟨208310, by rfl⟩ : syracuseStep 1110989 = 416621) (by norm_num)
theorem B586705 : Blo 519798 586705 := bbase (se 2 (by rfl) ⟨220014, by rfl⟩ : syracuseStep 586705 = 440029) (by norm_num)
theorem B783317 : Blo 519798 783317 := bbase (se 7 (by rfl) ⟨9179, by rfl⟩ : syracuseStep 783317 = 18359) (by norm_num)
theorem B1176533 : Blo 519798 1176533 := bbase (se 7 (by rfl) ⟨13787, by rfl⟩ : syracuseStep 1176533 = 27575) (by norm_num)
theorem B783341 : Blo 519798 783341 := bbase (se 3 (by rfl) ⟨146876, by rfl⟩ : syracuseStep 783341 = 293753) (by norm_num)
theorem B586741 : Blo 519798 586741 := bbase (se 5 (by rfl) ⟨27503, by rfl⟩ : syracuseStep 586741 = 55007) (by norm_num)
theorem B783365 : Blo 519798 783365 := bbase (se 4 (by rfl) ⟨73440, by rfl⟩ : syracuseStep 783365 = 146881) (by norm_num)
theorem B586777 : Blo 519798 586777 := bbase (se 2 (by rfl) ⟨220041, by rfl⟩ : syracuseStep 586777 = 440083) (by norm_num)
theorem B783389 : Blo 519798 783389 := bbase (se 3 (by rfl) ⟨146885, by rfl⟩ : syracuseStep 783389 = 293771) (by norm_num)
theorem B1176605 : Blo 519798 1176605 := bbase (se 3 (by rfl) ⟨220613, by rfl⟩ : syracuseStep 1176605 = 441227) (by norm_num)
theorem B783413 : Blo 519798 783413 := bbase (se 5 (by rfl) ⟨36722, by rfl⟩ : syracuseStep 783413 = 73445) (by norm_num)
theorem B586813 : Blo 519798 586813 := bbase (se 3 (by rfl) ⟨110027, by rfl⟩ : syracuseStep 586813 = 220055) (by norm_num)
theorem B881725 : Blo 519798 881725 := bbase (se 3 (by rfl) ⟨165323, by rfl⟩ : syracuseStep 881725 = 330647) (by norm_num)
theorem B783437 : Blo 519798 783437 := bbase (se 3 (by rfl) ⟨146894, by rfl⟩ : syracuseStep 783437 = 293789) (by norm_num)
theorem B1111133 : Blo 519798 1111133 := bbase (se 3 (by rfl) ⟨208337, by rfl⟩ : syracuseStep 1111133 = 416675) (by norm_num)
theorem B586849 : Blo 519798 586849 := bbase (se 2 (by rfl) ⟨220068, by rfl⟩ : syracuseStep 586849 = 440137) (by norm_num)
theorem B783461 : Blo 519798 783461 := bbase (se 4 (by rfl) ⟨73449, by rfl⟩ : syracuseStep 783461 = 146899) (by norm_num)
theorem B1176677 : Blo 519798 1176677 := bbase (se 4 (by rfl) ⟨110313, by rfl⟩ : syracuseStep 1176677 = 220627) (by norm_num)
theorem B1766501 : Blo 519798 1766501 := bbase (se 4 (by rfl) ⟨165609, by rfl⟩ : syracuseStep 1766501 = 331219) (by norm_num)
theorem B783485 : Blo 519798 783485 := bbase (se 3 (by rfl) ⟨146903, by rfl⟩ : syracuseStep 783485 = 293807) (by norm_num)
theorem B586885 : Blo 519798 586885 := bbase (se 4 (by rfl) ⟨55020, by rfl⟩ : syracuseStep 586885 = 110041) (by norm_num)
theorem B783509 : Blo 519798 783509 := bbase (se 6 (by rfl) ⟨18363, by rfl⟩ : syracuseStep 783509 = 36727) (by norm_num)
theorem B881813 : Blo 519798 881813 := bbase (se 6 (by rfl) ⟨20667, by rfl⟩ : syracuseStep 881813 = 41335) (by norm_num)
theorem B586921 : Blo 519798 586921 := bbase (se 2 (by rfl) ⟨220095, by rfl⟩ : syracuseStep 586921 = 440191) (by norm_num)
theorem B783533 : Blo 519798 783533 := bbase (se 3 (by rfl) ⟨146912, by rfl⟩ : syracuseStep 783533 = 293825) (by norm_num)
theorem B1176749 : Blo 519798 1176749 := bbase (se 3 (by rfl) ⟨220640, by rfl⟩ : syracuseStep 1176749 = 441281) (by norm_num)
theorem B783557 : Blo 519798 783557 := bbase (se 4 (by rfl) ⟨73458, by rfl⟩ : syracuseStep 783557 = 146917) (by norm_num)
theorem B586957 : Blo 519798 586957 := bbase (se 3 (by rfl) ⟨110054, by rfl⟩ : syracuseStep 586957 = 220109) (by norm_num)
theorem B783581 : Blo 519798 783581 := bbase (se 3 (by rfl) ⟨146921, by rfl⟩ : syracuseStep 783581 = 293843) (by norm_num)
theorem B586993 : Blo 519798 586993 := bbase (se 2 (by rfl) ⟨220122, by rfl⟩ : syracuseStep 586993 = 440245) (by norm_num)
theorem B783605 : Blo 519798 783605 := bbase (se 5 (by rfl) ⟨36731, by rfl⟩ : syracuseStep 783605 = 73463) (by norm_num)
theorem B1176821 : Blo 519798 1176821 := bbase (se 5 (by rfl) ⟨55163, by rfl⟩ : syracuseStep 1176821 = 110327) (by norm_num)
theorem B783629 : Blo 519798 783629 := bbase (se 3 (by rfl) ⟨146930, by rfl⟩ : syracuseStep 783629 = 293861) (by norm_num)
theorem B587029 : Blo 519798 587029 := bbase (se 6 (by rfl) ⟨13758, by rfl⟩ : syracuseStep 587029 = 27517) (by norm_num)
theorem B881941 : Blo 519798 881941 := bbase (se 6 (by rfl) ⟨20670, by rfl⟩ : syracuseStep 881941 = 41341) (by norm_num)
theorem B783653 : Blo 519798 783653 := bbase (se 4 (by rfl) ⟨73467, by rfl⟩ : syracuseStep 783653 = 146935) (by norm_num)
theorem B587065 : Blo 519798 587065 := bbase (se 2 (by rfl) ⟨220149, by rfl⟩ : syracuseStep 587065 = 440299) (by norm_num)
theorem B783677 : Blo 519798 783677 := bbase (se 3 (by rfl) ⟨146939, by rfl⟩ : syracuseStep 783677 = 293879) (by norm_num)
theorem B1176893 : Blo 519798 1176893 := bbase (se 3 (by rfl) ⟨220667, by rfl⟩ : syracuseStep 1176893 = 441335) (by norm_num)
theorem B783701 : Blo 519798 783701 := bbase (se 13 (by rfl) ⟨143, by rfl⟩ : syracuseStep 783701 = 287) (by norm_num)
theorem B587101 : Blo 519798 587101 := bbase (se 3 (by rfl) ⟨110081, by rfl⟩ : syracuseStep 587101 = 220163) (by norm_num)
theorem B783725 : Blo 519798 783725 := bbase (se 3 (by rfl) ⟨146948, by rfl⟩ : syracuseStep 783725 = 293897) (by norm_num)
theorem B882029 : Blo 519798 882029 := bbase (se 3 (by rfl) ⟨165380, by rfl⟩ : syracuseStep 882029 = 330761) (by norm_num)
theorem B587137 : Blo 519798 587137 := bbase (se 2 (by rfl) ⟨220176, by rfl⟩ : syracuseStep 587137 = 440353) (by norm_num)
theorem B783749 : Blo 519798 783749 := bbase (se 4 (by rfl) ⟨73476, by rfl⟩ : syracuseStep 783749 = 146953) (by norm_num)
theorem B1176965 : Blo 519798 1176965 := bbase (se 4 (by rfl) ⟨110340, by rfl⟩ : syracuseStep 1176965 = 220681) (by norm_num)
theorem B783773 : Blo 519798 783773 := bbase (se 3 (by rfl) ⟨146957, by rfl⟩ : syracuseStep 783773 = 293915) (by norm_num)
theorem B587173 : Blo 519798 587173 := bbase (se 4 (by rfl) ⟨55047, by rfl⟩ : syracuseStep 587173 = 110095) (by norm_num)
theorem B783797 : Blo 519798 783797 := bbase (se 5 (by rfl) ⟨36740, by rfl⟩ : syracuseStep 783797 = 73481) (by norm_num)
theorem B587209 : Blo 519798 587209 := bbase (se 2 (by rfl) ⟨220203, by rfl⟩ : syracuseStep 587209 = 440407) (by norm_num)
theorem B783821 : Blo 519798 783821 := bbase (se 3 (by rfl) ⟨146966, by rfl⟩ : syracuseStep 783821 = 293933) (by norm_num)
theorem B1177037 : Blo 519798 1177037 := bbase (se 3 (by rfl) ⟨220694, by rfl⟩ : syracuseStep 1177037 = 441389) (by norm_num)
theorem B783845 : Blo 519798 783845 := bbase (se 4 (by rfl) ⟨73485, by rfl⟩ : syracuseStep 783845 = 146971) (by norm_num)
theorem B587245 : Blo 519798 587245 := bbase (se 3 (by rfl) ⟨110108, by rfl⟩ : syracuseStep 587245 = 220217) (by norm_num)
theorem B882157 : Blo 519798 882157 := bbase (se 3 (by rfl) ⟨165404, by rfl⟩ : syracuseStep 882157 = 330809) (by norm_num)
theorem B3962357 : Blo 519798 3962357 := bbase (se 5 (by rfl) ⟨185735, by rfl⟩ : syracuseStep 3962357 = 371471) (by norm_num)
theorem B783869 : Blo 519798 783869 := bbase (se 3 (by rfl) ⟨146975, by rfl⟩ : syracuseStep 783869 = 293951) (by norm_num)
theorem B587281 : Blo 519798 587281 := bbase (se 2 (by rfl) ⟨220230, by rfl⟩ : syracuseStep 587281 = 440461) (by norm_num)
theorem B783893 : Blo 519798 783893 := bbase (se 6 (by rfl) ⟨18372, by rfl⟩ : syracuseStep 783893 = 36745) (by norm_num)
theorem B1177109 : Blo 519798 1177109 := bbase (se 6 (by rfl) ⟨27588, by rfl⟩ : syracuseStep 1177109 = 55177) (by norm_num)
theorem B1766933 : Blo 519798 1766933 := bbase (se 6 (by rfl) ⟨41412, by rfl⟩ : syracuseStep 1766933 = 82825) (by norm_num)
theorem B751141 : Blo 519798 751141 := bbase (se 4 (by rfl) ⟨70419, by rfl⟩ : syracuseStep 751141 = 140839) (by norm_num)
theorem B783917 : Blo 519798 783917 := bbase (se 3 (by rfl) ⟨146984, by rfl⟩ : syracuseStep 783917 = 293969) (by norm_num)
theorem B587317 : Blo 519798 587317 := bbase (se 5 (by rfl) ⟨27530, by rfl⟩ : syracuseStep 587317 = 55061) (by norm_num)
theorem B783941 : Blo 519798 783941 := bbase (se 4 (by rfl) ⟨73494, by rfl⟩ : syracuseStep 783941 = 146989) (by norm_num)
theorem B882245 : Blo 519798 882245 := bbase (se 4 (by rfl) ⟨82710, by rfl⟩ : syracuseStep 882245 = 165421) (by norm_num)
theorem B587353 : Blo 519798 587353 := bbase (se 2 (by rfl) ⟨220257, by rfl⟩ : syracuseStep 587353 = 440515) (by norm_num)
theorem B783965 : Blo 519798 783965 := bbase (se 3 (by rfl) ⟨146993, by rfl⟩ : syracuseStep 783965 = 293987) (by norm_num)
theorem B1177181 : Blo 519798 1177181 := bbase (se 3 (by rfl) ⟨220721, by rfl⟩ : syracuseStep 1177181 = 441443) (by norm_num)
theorem B783989 : Blo 519798 783989 := bbase (se 5 (by rfl) ⟨36749, by rfl⟩ : syracuseStep 783989 = 73499) (by norm_num)
theorem B587389 : Blo 519798 587389 := bbase (se 3 (by rfl) ⟨110135, by rfl⟩ : syracuseStep 587389 = 220271) (by norm_num)
theorem B784013 : Blo 519798 784013 := bbase (se 3 (by rfl) ⟨147002, by rfl⟩ : syracuseStep 784013 = 294005) (by norm_num)
theorem B587425 : Blo 519798 587425 := bbase (se 2 (by rfl) ⟨220284, by rfl⟩ : syracuseStep 587425 = 440569) (by norm_num)
theorem B784037 : Blo 519798 784037 := bbase (se 4 (by rfl) ⟨73503, by rfl⟩ : syracuseStep 784037 = 147007) (by norm_num)
theorem B1177253 : Blo 519798 1177253 := bbase (se 4 (by rfl) ⟨110367, by rfl⟩ : syracuseStep 1177253 = 220735) (by norm_num)
theorem B2815669 : Blo 519798 2815669 := bbase (se 5 (by rfl) ⟨131984, by rfl⟩ : syracuseStep 2815669 = 263969) (by norm_num)
theorem B784061 : Blo 519798 784061 := bbase (se 3 (by rfl) ⟨147011, by rfl⟩ : syracuseStep 784061 = 294023) (by norm_num)
theorem B587461 : Blo 519798 587461 := bbase (se 4 (by rfl) ⟨55074, by rfl⟩ : syracuseStep 587461 = 110149) (by norm_num)
theorem B882373 : Blo 519798 882373 := bbase (se 4 (by rfl) ⟨82722, by rfl⟩ : syracuseStep 882373 = 165445) (by norm_num)
theorem B784085 : Blo 519798 784085 := bbase (se 7 (by rfl) ⟨9188, by rfl⟩ : syracuseStep 784085 = 18377) (by norm_num)
theorem B587497 : Blo 519798 587497 := bbase (se 2 (by rfl) ⟨220311, by rfl⟩ : syracuseStep 587497 = 440623) (by norm_num)
theorem B784109 : Blo 519798 784109 := bbase (se 3 (by rfl) ⟨147020, by rfl⟩ : syracuseStep 784109 = 294041) (by norm_num)
theorem B1177325 : Blo 519798 1177325 := bbase (se 3 (by rfl) ⟨220748, by rfl⟩ : syracuseStep 1177325 = 441497) (by norm_num)
theorem B784133 : Blo 519798 784133 := bbase (se 4 (by rfl) ⟨73512, by rfl⟩ : syracuseStep 784133 = 147025) (by norm_num)
theorem B587533 : Blo 519798 587533 := bbase (se 3 (by rfl) ⟨110162, by rfl⟩ : syracuseStep 587533 = 220325) (by norm_num)
theorem B2979605 : Blo 519798 2979605 := bbase (se 6 (by rfl) ⟨69834, by rfl⟩ : syracuseStep 2979605 = 139669) (by norm_num)
theorem B784157 : Blo 519798 784157 := bbase (se 3 (by rfl) ⟨147029, by rfl⟩ : syracuseStep 784157 = 294059) (by norm_num)
theorem B882461 : Blo 519798 882461 := bbase (se 3 (by rfl) ⟨165461, by rfl⟩ : syracuseStep 882461 = 330923) (by norm_num)
theorem B849709 : Blo 519798 849709 := bbase (se 3 (by rfl) ⟨159320, by rfl⟩ : syracuseStep 849709 = 318641) (by norm_num)
theorem B587569 : Blo 519798 587569 := bbase (se 2 (by rfl) ⟨220338, by rfl⟩ : syracuseStep 587569 = 440677) (by norm_num)
theorem B784181 : Blo 519798 784181 := bbase (se 5 (by rfl) ⟨36758, by rfl⟩ : syracuseStep 784181 = 73517) (by norm_num)
theorem B1177397 : Blo 519798 1177397 := bbase (se 5 (by rfl) ⟨55190, by rfl⟩ : syracuseStep 1177397 = 110381) (by norm_num)
theorem B1111877 : Blo 519798 1111877 := bbase (se 4 (by rfl) ⟨104238, by rfl⟩ : syracuseStep 1111877 = 208477) (by norm_num)
theorem B784205 : Blo 519798 784205 := bbase (se 3 (by rfl) ⟨147038, by rfl⟩ : syracuseStep 784205 = 294077) (by norm_num)
theorem B587605 : Blo 519798 587605 := bbase (se 9 (by rfl) ⟨1721, by rfl⟩ : syracuseStep 587605 = 3443) (by norm_num)
theorem B784229 : Blo 519798 784229 := bbase (se 4 (by rfl) ⟨73521, by rfl⟩ : syracuseStep 784229 = 147043) (by norm_num)
theorem B849773 : Blo 519798 849773 := bbase (se 3 (by rfl) ⟨159332, by rfl⟩ : syracuseStep 849773 = 318665) (by norm_num)
theorem B587641 : Blo 519798 587641 := bbase (se 2 (by rfl) ⟨220365, by rfl⟩ : syracuseStep 587641 = 440731) (by norm_num)
theorem B784253 : Blo 519798 784253 := bbase (se 3 (by rfl) ⟨147047, by rfl⟩ : syracuseStep 784253 = 294095) (by norm_num)
theorem B1177469 : Blo 519798 1177469 := bbase (se 3 (by rfl) ⟨220775, by rfl⟩ : syracuseStep 1177469 = 441551) (by norm_num)
theorem B784277 : Blo 519798 784277 := bbase (se 6 (by rfl) ⟨18381, by rfl⟩ : syracuseStep 784277 = 36763) (by norm_num)
theorem B587677 : Blo 519798 587677 := bbase (se 3 (by rfl) ⟨110189, by rfl⟩ : syracuseStep 587677 = 220379) (by norm_num)
theorem B882589 : Blo 519798 882589 := bbase (se 3 (by rfl) ⟨165485, by rfl⟩ : syracuseStep 882589 = 330971) (by norm_num)
theorem B784301 : Blo 519798 784301 := bbase (se 3 (by rfl) ⟨147056, by rfl⟩ : syracuseStep 784301 = 294113) (by norm_num)
theorem B587713 : Blo 519798 587713 := bbase (se 2 (by rfl) ⟨220392, by rfl⟩ : syracuseStep 587713 = 440785) (by norm_num)
theorem B784325 : Blo 519798 784325 := bbase (se 4 (by rfl) ⟨73530, by rfl⟩ : syracuseStep 784325 = 147061) (by norm_num)
theorem B1177541 : Blo 519798 1177541 := bbase (se 4 (by rfl) ⟨110394, by rfl⟩ : syracuseStep 1177541 = 220789) (by norm_num)
theorem B1767365 : Blo 519798 1767365 := bbase (se 4 (by rfl) ⟨165690, by rfl⟩ : syracuseStep 1767365 = 331381) (by norm_num)
theorem B784349 : Blo 519798 784349 := bbase (se 3 (by rfl) ⟨147065, by rfl⟩ : syracuseStep 784349 = 294131) (by norm_num)
theorem B587749 : Blo 519798 587749 := bbase (se 4 (by rfl) ⟨55101, by rfl⟩ : syracuseStep 587749 = 110203) (by norm_num)
theorem B784373 : Blo 519798 784373 := bbase (se 5 (by rfl) ⟨36767, by rfl⟩ : syracuseStep 784373 = 73535) (by norm_num)
theorem B882677 : Blo 519798 882677 := bbase (se 5 (by rfl) ⟨41375, by rfl⟩ : syracuseStep 882677 = 82751) (by norm_num)
theorem B587785 : Blo 519798 587785 := bbase (se 2 (by rfl) ⟨220419, by rfl⟩ : syracuseStep 587785 = 440839) (by norm_num)
theorem B784397 : Blo 519798 784397 := bbase (se 3 (by rfl) ⟨147074, by rfl⟩ : syracuseStep 784397 = 294149) (by norm_num)
theorem B1177613 : Blo 519798 1177613 := bbase (se 3 (by rfl) ⟨220802, by rfl⟩ : syracuseStep 1177613 = 441605) (by norm_num)
theorem B1505317 : Blo 519798 1505317 := bbase (se 4 (by rfl) ⟨141123, by rfl⟩ : syracuseStep 1505317 = 282247) (by norm_num)
theorem B784421 : Blo 519798 784421 := bbase (se 4 (by rfl) ⟨73539, by rfl⟩ : syracuseStep 784421 = 147079) (by norm_num)
theorem B587821 : Blo 519798 587821 := bbase (se 3 (by rfl) ⟨110216, by rfl⟩ : syracuseStep 587821 = 220433) (by norm_num)
theorem B784445 : Blo 519798 784445 := bbase (se 3 (by rfl) ⟨147083, by rfl⟩ : syracuseStep 784445 = 294167) (by norm_num)
theorem B587857 : Blo 519798 587857 := bbase (se 2 (by rfl) ⟨220446, by rfl⟩ : syracuseStep 587857 = 440893) (by norm_num)
theorem B784469 : Blo 519798 784469 := bbase (se 8 (by rfl) ⟨4596, by rfl⟩ : syracuseStep 784469 = 9193) (by norm_num)
theorem B1177685 : Blo 519798 1177685 := bbase (se 8 (by rfl) ⟨6900, by rfl⟩ : syracuseStep 1177685 = 13801) (by norm_num)
theorem B784493 : Blo 519798 784493 := bbase (se 3 (by rfl) ⟨147092, by rfl⟩ : syracuseStep 784493 = 294185) (by norm_num)
theorem B587893 : Blo 519798 587893 := bbase (se 5 (by rfl) ⟨27557, by rfl⟩ : syracuseStep 587893 = 55115) (by norm_num)
theorem B882805 : Blo 519798 882805 := bbase (se 5 (by rfl) ⟨41381, by rfl⟩ : syracuseStep 882805 = 82763) (by norm_num)
theorem B784517 : Blo 519798 784517 := bbase (se 4 (by rfl) ⟨73548, by rfl⟩ : syracuseStep 784517 = 147097) (by norm_num)
theorem B9664661 : Blo 519798 9664661 := bbase (se 6 (by rfl) ⟨226515, by rfl⟩ : syracuseStep 9664661 = 453031) (by norm_num)
theorem B587929 : Blo 519798 587929 := bbase (se 2 (by rfl) ⟨220473, by rfl⟩ : syracuseStep 587929 = 440947) (by norm_num)
theorem B784541 : Blo 519798 784541 := bbase (se 3 (by rfl) ⟨147101, by rfl⟩ : syracuseStep 784541 = 294203) (by norm_num)
theorem B1177757 : Blo 519798 1177757 := bbase (se 3 (by rfl) ⟨220829, by rfl⟩ : syracuseStep 1177757 = 441659) (by norm_num)
theorem B784565 : Blo 519798 784565 := bbase (se 5 (by rfl) ⟨36776, by rfl⟩ : syracuseStep 784565 = 73553) (by norm_num)
theorem B587965 : Blo 519798 587965 := bbase (se 3 (by rfl) ⟨110243, by rfl⟩ : syracuseStep 587965 = 220487) (by norm_num)
theorem B784589 : Blo 519798 784589 := bbase (se 3 (by rfl) ⟨147110, by rfl⟩ : syracuseStep 784589 = 294221) (by norm_num)
theorem B882893 : Blo 519798 882893 := bbase (se 3 (by rfl) ⟨165542, by rfl⟩ : syracuseStep 882893 = 331085) (by norm_num)
theorem B555221 : Blo 519798 555221 := bbase (se 7 (by rfl) ⟨6506, by rfl⟩ : syracuseStep 555221 = 13013) (by norm_num)
theorem B588001 : Blo 519798 588001 := bbase (se 2 (by rfl) ⟨220500, by rfl⟩ : syracuseStep 588001 = 441001) (by norm_num)
theorem B784613 : Blo 519798 784613 := bbase (se 4 (by rfl) ⟨73557, by rfl⟩ : syracuseStep 784613 = 147115) (by norm_num)
theorem B1177829 : Blo 519798 1177829 := bbase (se 4 (by rfl) ⟨110421, by rfl⟩ : syracuseStep 1177829 = 220843) (by norm_num)
theorem B784637 : Blo 519798 784637 := bbase (se 3 (by rfl) ⟨147119, by rfl⟩ : syracuseStep 784637 = 294239) (by norm_num)
theorem B588037 : Blo 519798 588037 := bbase (se 4 (by rfl) ⟨55128, by rfl⟩ : syracuseStep 588037 = 110257) (by norm_num)
theorem B784661 : Blo 519798 784661 := bbase (se 6 (by rfl) ⟨18390, by rfl⟩ : syracuseStep 784661 = 36781) (by norm_num)
theorem B555293 : Blo 519798 555293 := bbase (se 3 (by rfl) ⟨104117, by rfl⟩ : syracuseStep 555293 = 208235) (by norm_num)
theorem B588073 : Blo 519798 588073 := bbase (se 2 (by rfl) ⟨220527, by rfl⟩ : syracuseStep 588073 = 441055) (by norm_num)
theorem B784685 : Blo 519798 784685 := bbase (se 3 (by rfl) ⟨147128, by rfl⟩ : syracuseStep 784685 = 294257) (by norm_num)
theorem B1177901 : Blo 519798 1177901 := bbase (se 3 (by rfl) ⟨220856, by rfl⟩ : syracuseStep 1177901 = 441713) (by norm_num)
theorem B784709 : Blo 519798 784709 := bbase (se 4 (by rfl) ⟨73566, by rfl⟩ : syracuseStep 784709 = 147133) (by norm_num)
theorem B588109 : Blo 519798 588109 := bbase (se 3 (by rfl) ⟨110270, by rfl⟩ : syracuseStep 588109 = 220541) (by norm_num)
theorem B883021 : Blo 519798 883021 := bbase (se 3 (by rfl) ⟨165566, by rfl⟩ : syracuseStep 883021 = 331133) (by norm_num)
theorem B784733 : Blo 519798 784733 := bbase (se 3 (by rfl) ⟨147137, by rfl⟩ : syracuseStep 784733 = 294275) (by norm_num)
theorem B588145 : Blo 519798 588145 := bbase (se 2 (by rfl) ⟨220554, by rfl⟩ : syracuseStep 588145 = 441109) (by norm_num)
theorem B784757 : Blo 519798 784757 := bbase (se 5 (by rfl) ⟨36785, by rfl⟩ : syracuseStep 784757 = 73571) (by norm_num)
theorem B1177973 : Blo 519798 1177973 := bbase (se 5 (by rfl) ⟨55217, by rfl⟩ : syracuseStep 1177973 = 110435) (by norm_num)
theorem B1767797 : Blo 519798 1767797 := bbase (se 5 (by rfl) ⟨82865, by rfl⟩ : syracuseStep 1767797 = 165731) (by norm_num)
theorem B784781 : Blo 519798 784781 := bbase (se 3 (by rfl) ⟨147146, by rfl⟩ : syracuseStep 784781 = 294293) (by norm_num)
theorem B588181 : Blo 519798 588181 := bbase (se 6 (by rfl) ⟨13785, by rfl⟩ : syracuseStep 588181 = 27571) (by norm_num)
theorem B784805 : Blo 519798 784805 := bbase (se 4 (by rfl) ⟨73575, by rfl⟩ : syracuseStep 784805 = 147151) (by norm_num)
theorem B883109 : Blo 519798 883109 := bbase (se 4 (by rfl) ⟨82791, by rfl⟩ : syracuseStep 883109 = 165583) (by norm_num)
theorem B588217 : Blo 519798 588217 := bbase (se 2 (by rfl) ⟨220581, by rfl⟩ : syracuseStep 588217 = 441163) (by norm_num)
theorem B784829 : Blo 519798 784829 := bbase (se 3 (by rfl) ⟨147155, by rfl⟩ : syracuseStep 784829 = 294311) (by norm_num)
theorem B1178045 : Blo 519798 1178045 := bbase (se 3 (by rfl) ⟨220883, by rfl⟩ : syracuseStep 1178045 = 441767) (by norm_num)
theorem B784853 : Blo 519798 784853 := bbase (se 7 (by rfl) ⟨9197, by rfl⟩ : syracuseStep 784853 = 18395) (by norm_num)
theorem B555481 : Blo 519798 555481 := bbase (se 2 (by rfl) ⟨208305, by rfl⟩ : syracuseStep 555481 = 416611) (by norm_num)
theorem B588253 : Blo 519798 588253 := bbase (se 3 (by rfl) ⟨110297, by rfl⟩ : syracuseStep 588253 = 220595) (by norm_num)
theorem B784877 : Blo 519798 784877 := bbase (se 3 (by rfl) ⟨147164, by rfl⟩ : syracuseStep 784877 = 294329) (by norm_num)
theorem B588289 : Blo 519798 588289 := bbase (se 2 (by rfl) ⟨220608, by rfl⟩ : syracuseStep 588289 = 441217) (by norm_num)
theorem B784901 : Blo 519798 784901 := bbase (se 4 (by rfl) ⟨73584, by rfl⟩ : syracuseStep 784901 = 147169) (by norm_num)
theorem B1178117 : Blo 519798 1178117 := bbase (se 4 (by rfl) ⟨110448, by rfl⟩ : syracuseStep 1178117 = 220897) (by norm_num)
theorem B784925 : Blo 519798 784925 := bbase (se 3 (by rfl) ⟨147173, by rfl⟩ : syracuseStep 784925 = 294347) (by norm_num)
theorem B588325 : Blo 519798 588325 := bbase (se 4 (by rfl) ⟨55155, by rfl⟩ : syracuseStep 588325 = 110311) (by norm_num)
theorem B883237 : Blo 519798 883237 := bbase (se 4 (by rfl) ⟨82803, by rfl⟩ : syracuseStep 883237 = 165607) (by norm_num)
theorem B1112629 : Blo 519798 1112629 := bbase (se 5 (by rfl) ⟨52154, by rfl⟩ : syracuseStep 1112629 = 104309) (by norm_num)
theorem B784949 : Blo 519798 784949 := bbase (se 5 (by rfl) ⟨36794, by rfl⟩ : syracuseStep 784949 = 73589) (by norm_num)
theorem B588361 : Blo 519798 588361 := bbase (se 2 (by rfl) ⟨220635, by rfl⟩ : syracuseStep 588361 = 441271) (by norm_num)
theorem B784973 : Blo 519798 784973 := bbase (se 3 (by rfl) ⟨147182, by rfl⟩ : syracuseStep 784973 = 294365) (by norm_num)
theorem B1178189 : Blo 519798 1178189 := bbase (se 3 (by rfl) ⟨220910, by rfl⟩ : syracuseStep 1178189 = 441821) (by norm_num)
theorem B784997 : Blo 519798 784997 := bbase (se 4 (by rfl) ⟨73593, by rfl⟩ : syracuseStep 784997 = 147187) (by norm_num)
theorem B588397 : Blo 519798 588397 := bbase (se 3 (by rfl) ⟨110324, by rfl⟩ : syracuseStep 588397 = 220649) (by norm_num)
theorem B785021 : Blo 519798 785021 := bbase (se 3 (by rfl) ⟨147191, by rfl⟩ : syracuseStep 785021 = 294383) (by norm_num)
theorem B883325 : Blo 519798 883325 := bbase (se 3 (by rfl) ⟨165623, by rfl⟩ : syracuseStep 883325 = 331247) (by norm_num)
theorem B555665 : Blo 519798 555665 := bbase (se 2 (by rfl) ⟨208374, by rfl⟩ : syracuseStep 555665 = 416749) (by norm_num)
theorem B588433 : Blo 519798 588433 := bbase (se 2 (by rfl) ⟨220662, by rfl⟩ : syracuseStep 588433 = 441325) (by norm_num)
theorem B785045 : Blo 519798 785045 := bbase (se 6 (by rfl) ⟨18399, by rfl⟩ : syracuseStep 785045 = 36799) (by norm_num)
theorem B1178261 : Blo 519798 1178261 := bbase (se 6 (by rfl) ⟨27615, by rfl⟩ : syracuseStep 1178261 = 55231) (by norm_num)
theorem B785069 : Blo 519798 785069 := bbase (se 3 (by rfl) ⟨147200, by rfl⟩ : syracuseStep 785069 = 294401) (by norm_num)
theorem B588469 : Blo 519798 588469 := bbase (se 5 (by rfl) ⟨27584, by rfl⟩ : syracuseStep 588469 = 55169) (by norm_num)
theorem B1112773 : Blo 519798 1112773 := bbase (se 4 (by rfl) ⟨104322, by rfl⟩ : syracuseStep 1112773 = 208645) (by norm_num)
theorem B785093 : Blo 519798 785093 := bbase (se 4 (by rfl) ⟨73602, by rfl⟩ : syracuseStep 785093 = 147205) (by norm_num)
theorem B5929685 : Blo 519798 5929685 := bbase (se 7 (by rfl) ⟨69488, by rfl⟩ : syracuseStep 5929685 = 138977) (by norm_num)
theorem B588505 : Blo 519798 588505 := bbase (se 2 (by rfl) ⟨220689, by rfl⟩ : syracuseStep 588505 = 441379) (by norm_num)
theorem B785117 : Blo 519798 785117 := bbase (se 3 (by rfl) ⟨147209, by rfl⟩ : syracuseStep 785117 = 294419) (by norm_num)
theorem B1178333 : Blo 519798 1178333 := bbase (se 3 (by rfl) ⟨220937, by rfl⟩ : syracuseStep 1178333 = 441875) (by norm_num)
theorem B785141 : Blo 519798 785141 := bbase (se 5 (by rfl) ⟨36803, by rfl⟩ : syracuseStep 785141 = 73607) (by norm_num)
theorem B588541 : Blo 519798 588541 := bbase (se 3 (by rfl) ⟨110351, by rfl⟩ : syracuseStep 588541 = 220703) (by norm_num)
theorem B883453 : Blo 519798 883453 := bbase (se 3 (by rfl) ⟨165647, by rfl⟩ : syracuseStep 883453 = 331295) (by norm_num)
theorem B785165 : Blo 519798 785165 := bbase (se 3 (by rfl) ⟨147218, by rfl⟩ : syracuseStep 785165 = 294437) (by norm_num)
theorem B588577 : Blo 519798 588577 := bbase (se 2 (by rfl) ⟨220716, by rfl⟩ : syracuseStep 588577 = 441433) (by norm_num)
theorem B785189 : Blo 519798 785189 := bbase (se 4 (by rfl) ⟨73611, by rfl⟩ : syracuseStep 785189 = 147223) (by norm_num)
theorem B1178405 : Blo 519798 1178405 := bbase (se 4 (by rfl) ⟨110475, by rfl⟩ : syracuseStep 1178405 = 220951) (by norm_num)
theorem B785213 : Blo 519798 785213 := bbase (se 3 (by rfl) ⟨147227, by rfl⟩ : syracuseStep 785213 = 294455) (by norm_num)
theorem B588613 : Blo 519798 588613 := bbase (se 4 (by rfl) ⟨55182, by rfl⟩ : syracuseStep 588613 = 110365) (by norm_num)
theorem B1604437 : Blo 519798 1604437 := bbase (se 9 (by rfl) ⟨4700, by rfl⟩ : syracuseStep 1604437 = 9401) (by norm_num)
theorem B785237 : Blo 519798 785237 := bbase (se 9 (by rfl) ⟨2300, by rfl⟩ : syracuseStep 785237 = 4601) (by norm_num)
theorem B883541 : Blo 519798 883541 := bbase (se 9 (by rfl) ⟨2588, by rfl⟩ : syracuseStep 883541 = 5177) (by norm_num)
theorem B588649 : Blo 519798 588649 := bbase (se 2 (by rfl) ⟨220743, by rfl⟩ : syracuseStep 588649 = 441487) (by norm_num)
theorem B785261 : Blo 519798 785261 := bbase (se 3 (by rfl) ⟨147236, by rfl⟩ : syracuseStep 785261 = 294473) (by norm_num)
theorem B1178477 : Blo 519798 1178477 := bbase (se 3 (by rfl) ⟨220964, by rfl⟩ : syracuseStep 1178477 = 441929) (by norm_num)
theorem B785285 : Blo 519798 785285 := bbase (se 4 (by rfl) ⟨73620, by rfl⟩ : syracuseStep 785285 = 147241) (by norm_num)
theorem B588685 : Blo 519798 588685 := bbase (se 3 (by rfl) ⟨110378, by rfl⟩ : syracuseStep 588685 = 220757) (by norm_num)
theorem B785309 : Blo 519798 785309 := bbase (se 3 (by rfl) ⟨147245, by rfl⟩ : syracuseStep 785309 = 294491) (by norm_num)
theorem B588721 : Blo 519798 588721 := bbase (se 2 (by rfl) ⟨220770, by rfl⟩ : syracuseStep 588721 = 441541) (by norm_num)
theorem B785333 : Blo 519798 785333 := bbase (se 5 (by rfl) ⟨36812, by rfl⟩ : syracuseStep 785333 = 73625) (by norm_num)
theorem B785357 : Blo 519798 785357 := bbase (se 3 (by rfl) ⟨147254, by rfl⟩ : syracuseStep 785357 = 294509) (by norm_num)
theorem B588757 : Blo 519798 588757 := bbase (se 7 (by rfl) ⟨6899, by rfl⟩ : syracuseStep 588757 = 13799) (by norm_num)
theorem B883669 : Blo 519798 883669 := bbase (se 7 (by rfl) ⟨10355, by rfl⟩ : syracuseStep 883669 = 20711) (by norm_num)
theorem B785381 : Blo 519798 785381 := bbase (se 4 (by rfl) ⟨73629, by rfl⟩ : syracuseStep 785381 = 147259) (by norm_num)
theorem B3177461 : Blo 519798 3177461 := bbase (se 5 (by rfl) ⟨148943, by rfl⟩ : syracuseStep 3177461 = 297887) (by norm_num)
theorem B588793 : Blo 519798 588793 := bbase (se 2 (by rfl) ⟨220797, by rfl⟩ : syracuseStep 588793 = 441595) (by norm_num)
theorem B785405 : Blo 519798 785405 := bbase (se 3 (by rfl) ⟨147263, by rfl⟩ : syracuseStep 785405 = 294527) (by norm_num)
theorem B785429 : Blo 519798 785429 := bbase (se 6 (by rfl) ⟨18408, by rfl⟩ : syracuseStep 785429 = 36817) (by norm_num)
theorem B588829 : Blo 519798 588829 := bbase (se 3 (by rfl) ⟨110405, by rfl⟩ : syracuseStep 588829 = 220811) (by norm_num)
theorem B785453 : Blo 519798 785453 := bbase (se 3 (by rfl) ⟨147272, by rfl⟩ : syracuseStep 785453 = 294545) (by norm_num)
theorem B883757 : Blo 519798 883757 := bbase (se 3 (by rfl) ⟨165704, by rfl⟩ : syracuseStep 883757 = 331409) (by norm_num)
theorem B1113149 : Blo 519798 1113149 := bbase (se 3 (by rfl) ⟨208715, by rfl⟩ : syracuseStep 1113149 = 417431) (by norm_num)
theorem B588865 : Blo 519798 588865 := bbase (se 2 (by rfl) ⟨220824, by rfl⟩ : syracuseStep 588865 = 441649) (by norm_num)
theorem B785477 : Blo 519798 785477 := bbase (se 4 (by rfl) ⟨73638, by rfl⟩ : syracuseStep 785477 = 147277) (by norm_num)
theorem B785501 : Blo 519798 785501 := bbase (se 3 (by rfl) ⟨147281, by rfl⟩ : syracuseStep 785501 = 294563) (by norm_num)
theorem B588901 : Blo 519798 588901 := bbase (se 4 (by rfl) ⟨55209, by rfl⟩ : syracuseStep 588901 = 110419) (by norm_num)
theorem B1408117 : Blo 519798 1408117 := bbase (se 5 (by rfl) ⟨66005, by rfl⟩ : syracuseStep 1408117 = 132011) (by norm_num)
theorem B785525 : Blo 519798 785525 := bbase (se 5 (by rfl) ⟨36821, by rfl⟩ : syracuseStep 785525 = 73643) (by norm_num)
theorem B588937 : Blo 519798 588937 := bbase (se 2 (by rfl) ⟨220851, by rfl⟩ : syracuseStep 588937 = 441703) (by norm_num)
theorem B785549 : Blo 519798 785549 := bbase (se 3 (by rfl) ⟨147290, by rfl⟩ : syracuseStep 785549 = 294581) (by norm_num)
theorem B785573 : Blo 519798 785573 := bbase (se 4 (by rfl) ⟨73647, by rfl⟩ : syracuseStep 785573 = 147295) (by norm_num)
theorem B588973 : Blo 519798 588973 := bbase (se 3 (by rfl) ⟨110432, by rfl⟩ : syracuseStep 588973 = 220865) (by norm_num)
theorem B883885 : Blo 519798 883885 := bbase (se 3 (by rfl) ⟨165728, by rfl⟩ : syracuseStep 883885 = 331457) (by norm_num)
theorem B785597 : Blo 519798 785597 := bbase (se 3 (by rfl) ⟨147299, by rfl⟩ : syracuseStep 785597 = 294599) (by norm_num)
theorem B589009 : Blo 519798 589009 := bbase (se 2 (by rfl) ⟨220878, by rfl⟩ : syracuseStep 589009 = 441757) (by norm_num)
theorem B785621 : Blo 519798 785621 := bbase (se 7 (by rfl) ⟨9206, by rfl⟩ : syracuseStep 785621 = 18413) (by norm_num)
theorem B785645 : Blo 519798 785645 := bbase (se 3 (by rfl) ⟨147308, by rfl⟩ : syracuseStep 785645 = 294617) (by norm_num)
theorem B2227445 : Blo 519798 2227445 := bbase (se 5 (by rfl) ⟨104411, by rfl⟩ : syracuseStep 2227445 = 208823) (by norm_num)
theorem B589045 : Blo 519798 589045 := bbase (se 5 (by rfl) ⟨27611, by rfl⟩ : syracuseStep 589045 = 55223) (by norm_num)
theorem B785669 : Blo 519798 785669 := bbase (se 4 (by rfl) ⟨73656, by rfl⟩ : syracuseStep 785669 = 147313) (by norm_num)
theorem B589081 : Blo 519798 589081 := bbase (se 2 (by rfl) ⟨220905, by rfl⟩ : syracuseStep 589081 = 441811) (by norm_num)
theorem B785693 : Blo 519798 785693 := bbase (se 3 (by rfl) ⟨147317, by rfl⟩ : syracuseStep 785693 = 294635) (by norm_num)
theorem B589117 : Blo 519798 589117 := bbase (se 3 (by rfl) ⟨110459, by rfl⟩ : syracuseStep 589117 = 220919) (by norm_num)
theorem B589153 : Blo 519798 589153 := bbase (se 2 (by rfl) ⟨220932, by rfl⟩ : syracuseStep 589153 = 441865) (by norm_num)
theorem B556417 : Blo 519798 556417 := bbase (se 2 (by rfl) ⟨208656, by rfl⟩ : syracuseStep 556417 = 417313) (by norm_num)
theorem B589189 : Blo 519798 589189 := bbase (se 4 (by rfl) ⟨55236, by rfl⟩ : syracuseStep 589189 = 110473) (by norm_num)
theorem B589225 : Blo 519798 589225 := bbase (se 2 (by rfl) ⟨220959, by rfl⟩ : syracuseStep 589225 = 441919) (by norm_num)
theorem B1113517 : Blo 519798 1113517 := bbase (se 3 (by rfl) ⟨208784, by rfl⟩ : syracuseStep 1113517 = 417569) (by norm_num)
theorem B556489 : Blo 519798 556489 := bbase (se 2 (by rfl) ⟨208683, by rfl⟩ : syracuseStep 556489 = 417367) (by norm_num)
theorem B589261 : Blo 519798 589261 := bbase (se 3 (by rfl) ⟨110486, by rfl⟩ : syracuseStep 589261 = 220973) (by norm_num)
theorem B2227733 : Blo 519798 2227733 := bbase (se 6 (by rfl) ⟨52212, by rfl⟩ : syracuseStep 2227733 = 104425) (by norm_num)
theorem B556669 : Blo 519798 556669 := bbase (se 3 (by rfl) ⟨104375, by rfl⟩ : syracuseStep 556669 = 208751) (by norm_num)
theorem B1409123 : Blo 519798 1409123 := bstep (se 1 (by rfl) ⟨1056842, by rfl⟩ : syracuseStep 1409123 = 2113685) B2113685
theorem B1671313 : Blo 519798 1671313 := bstep (se 2 (by rfl) ⟨626742, by rfl⟩ : syracuseStep 1671313 = 1253485) B1253485
theorem B1409219 : Blo 519798 1409219 := bstep (se 1 (by rfl) ⟨1056914, by rfl⟩ : syracuseStep 1409219 = 2113829) B2113829
theorem B1147139 : Blo 519798 1147139 := bstep (se 1 (by rfl) ⟨860354, by rfl⟩ : syracuseStep 1147139 = 1720709) B1720709
theorem B2818309 : Blo 519798 2818309 := bstep (se 4 (by rfl) ⟨264216, by rfl⟩ : syracuseStep 2818309 = 528433) B528433
theorem B1409393 : Blo 519798 1409393 := bstep (se 2 (by rfl) ⟨528522, by rfl⟩ : syracuseStep 1409393 = 1057045) B1057045
theorem B1114499 : Blo 519798 1114499 := bstep (se 1 (by rfl) ⟨835874, by rfl⟩ : syracuseStep 1114499 = 1671749) B1671749
theorem B557651 : Blo 519798 557651 := bstep (se 1 (by rfl) ⟨418238, by rfl⟩ : syracuseStep 557651 = 836477) B836477
theorem B3343139 : Blo 519798 3343139 := bstep (se 1 (by rfl) ⟨2507354, by rfl⟩ : syracuseStep 3343139 = 5014709) B5014709
theorem B1410257 : Blo 519798 1410257 := bstep (se 2 (by rfl) ⟨528846, by rfl⟩ : syracuseStep 1410257 = 1057693) B1057693
theorem B1115363 : Blo 519798 1115363 := bstep (se 1 (by rfl) ⟨836522, by rfl⟩ : syracuseStep 1115363 = 1673045) B1673045
theorem B1115473 : Blo 519798 1115473 := bstep (se 2 (by rfl) ⟨418302, by rfl⟩ : syracuseStep 1115473 = 836605) B836605
theorem B13763953 : Blo 519798 13763953 := bstep (se 2 (by rfl) ⟨5161482, by rfl⟩ : syracuseStep 13763953 = 10322965) B10322965
theorem B722369 : Blo 519798 722369 := bstep (se 2 (by rfl) ⟨270888, by rfl⟩ : syracuseStep 722369 = 541777) B541777
theorem B5375587 : Blo 519798 5375587 := bstep (se 1 (by rfl) ⟨4031690, by rfl⟩ : syracuseStep 5375587 = 8063381) B8063381
theorem B2098979 : Blo 519798 2098979 := bstep (se 1 (by rfl) ⟨1574234, by rfl⟩ : syracuseStep 2098979 = 3148469) B3148469
theorem B2230193 : Blo 519798 2230193 := bstep (se 2 (by rfl) ⟨836322, by rfl⟩ : syracuseStep 2230193 = 1672645) B1672645
theorem B1411025 : Blo 519798 1411025 := bstep (se 2 (by rfl) ⟨529134, by rfl⟩ : syracuseStep 1411025 = 1058269) B1058269
theorem B1673261 : Blo 519798 1673261 := bstep (se 3 (by rfl) ⟨313736, by rfl⟩ : syracuseStep 1673261 = 627473) B627473
theorem B559219 : Blo 519798 559219 := bstep (se 1 (by rfl) ⟨419414, by rfl⟩ : syracuseStep 559219 = 838829) B838829
theorem B1673389 : Blo 519798 1673389 := bstep (se 3 (by rfl) ⟨313760, by rfl⟩ : syracuseStep 1673389 = 627521) B627521
theorem B3967217 : Blo 519798 3967217 := bstep (se 2 (by rfl) ⟨1487706, by rfl⟩ : syracuseStep 3967217 = 2975413) B2975413
theorem B1411469 : Blo 519798 1411469 := bstep (se 3 (by rfl) ⟨264650, by rfl⟩ : syracuseStep 1411469 = 529301) B529301
theorem B2230861 : Blo 519798 2230861 := bstep (se 3 (by rfl) ⟨418286, by rfl⟩ : syracuseStep 2230861 = 836573) B836573
theorem B658307 : Blo 519798 658307 := bstep (se 1 (by rfl) ⟨493730, by rfl⟩ : syracuseStep 658307 = 987461) B987461
theorem B2231459 : Blo 519798 2231459 := bstep (se 1 (by rfl) ⟨1673594, by rfl⟩ : syracuseStep 2231459 = 3347189) B3347189
theorem B4754659 : Blo 519798 4754659 := bstep (se 1 (by rfl) ⟨3565994, by rfl⟩ : syracuseStep 4754659 = 7131989) B7131989
theorem B1412333 : Blo 519798 1412333 := bstep (se 3 (by rfl) ⟨264812, by rfl⟩ : syracuseStep 1412333 = 529625) B529625
theorem B1117489 : Blo 519798 1117489 := bstep (se 2 (by rfl) ⟨419058, by rfl⟩ : syracuseStep 1117489 = 838117) B838117
theorem B2821553 : Blo 519798 2821553 := bstep (se 2 (by rfl) ⟨1058082, by rfl⟩ : syracuseStep 2821553 = 2116165) B2116165
theorem B659011 : Blo 519798 659011 := bstep (se 1 (by rfl) ⟨494258, by rfl⟩ : syracuseStep 659011 = 988517) B988517
theorem B659107 : Blo 519798 659107 := bstep (se 1 (by rfl) ⟨494330, by rfl⟩ : syracuseStep 659107 = 988661) B988661
theorem B1117891 : Blo 519798 1117891 := bstep (se 1 (by rfl) ⟨838418, by rfl⟩ : syracuseStep 1117891 = 1676837) B1676837
theorem B5639989 : Blo 519798 5639989 := bstep (se 5 (by rfl) ⟨264374, by rfl⟩ : syracuseStep 5639989 = 528749) B528749
theorem B626627 : Blo 519798 626627 := bstep (se 1 (by rfl) ⟨469970, by rfl⟩ : syracuseStep 626627 = 939941) B939941
theorem B1675235 : Blo 519798 1675235 := bstep (se 1 (by rfl) ⟨1256426, by rfl⟩ : syracuseStep 1675235 = 2512853) B2512853
theorem B1609763 : Blo 519798 1609763 := bstep (se 1 (by rfl) ⟨1207322, by rfl⟩ : syracuseStep 1609763 = 2414645) B2414645
theorem B987203 : Blo 519798 987203 := bstep (se 1 (by rfl) ⟨740402, by rfl⟩ : syracuseStep 987203 = 1480805) B1480805
theorem B1675363 : Blo 519798 1675363 := bstep (se 1 (by rfl) ⟨1256522, by rfl⟩ : syracuseStep 1675363 = 2513045) B2513045
theorem B659603 : Blo 519798 659603 := bstep (se 1 (by rfl) ⟨494702, by rfl⟩ : syracuseStep 659603 = 989405) B989405
theorem B528563 : Blo 519798 528563 := bstep (se 1 (by rfl) ⟨396422, by rfl⟩ : syracuseStep 528563 = 792845) B792845
theorem B1675505 : Blo 519798 1675505 := bstep (se 2 (by rfl) ⟨628314, by rfl⟩ : syracuseStep 1675505 = 1256629) B1256629
theorem B987491 : Blo 519798 987491 := bstep (se 1 (by rfl) ⟨740618, by rfl⟩ : syracuseStep 987491 = 1481237) B1481237
theorem B1675619 : Blo 519798 1675619 := bstep (se 1 (by rfl) ⟨1256714, by rfl⟩ : syracuseStep 1675619 = 2513429) B2513429
theorem B3346829 : Blo 519798 3346829 := bstep (se 3 (by rfl) ⟨627530, by rfl⟩ : syracuseStep 3346829 = 1255061) B1255061
theorem B8556997 : Blo 519798 8556997 := bstep (se 4 (by rfl) ⟨802218, by rfl⟩ : syracuseStep 8556997 = 1604437) B1604437
theorem B889363 : Blo 519798 889363 := bstep (se 1 (by rfl) ⟨667022, by rfl⟩ : syracuseStep 889363 = 1334045) B1334045
theorem B1249987 : Blo 519798 1249987 := bstep (se 1 (by rfl) ⟨937490, by rfl⟩ : syracuseStep 1249987 = 1874981) B1874981
theorem B3576611 : Blo 519798 3576611 := bstep (se 1 (by rfl) ⟨2682458, by rfl⟩ : syracuseStep 3576611 = 5364917) B5364917
theorem B660307 : Blo 519798 660307 := bstep (se 1 (by rfl) ⟨495230, by rfl⟩ : syracuseStep 660307 = 990461) B990461
theorem B660403 : Blo 519798 660403 := bstep (se 1 (by rfl) ⟨495302, by rfl⟩ : syracuseStep 660403 = 990605) B990605
theorem B2266061 : Blo 519798 2266061 := bstep (se 3 (by rfl) ⟨424886, by rfl⟩ : syracuseStep 2266061 = 849773) B849773
theorem B857137 : Blo 519798 857137 := bstep (se 2 (by rfl) ⟨321426, by rfl⟩ : syracuseStep 857137 = 642853) B642853
theorem B529459 : Blo 519798 529459 := bstep (se 1 (by rfl) ⟨397094, by rfl⟩ : syracuseStep 529459 = 794189) B794189
theorem B988433 : Blo 519798 988433 := bstep (se 2 (by rfl) ⟨370662, by rfl⟩ : syracuseStep 988433 = 741325) B741325
theorem B1316209 : Blo 519798 1316209 := bstep (se 2 (by rfl) ⟨493578, by rfl⟩ : syracuseStep 1316209 = 987157) B987157
theorem B660899 : Blo 519798 660899 := bstep (se 1 (by rfl) ⟨495674, by rfl⟩ : syracuseStep 660899 = 991349) B991349
theorem B6690275 : Blo 519798 6690275 := bstep (se 1 (by rfl) ⟨5017706, by rfl⟩ : syracuseStep 6690275 = 10035413) B10035413
theorem B1054289 : Blo 519798 1054289 := bstep (se 2 (by rfl) ⟨395358, by rfl⟩ : syracuseStep 1054289 = 790717) B790717
theorem B1316483 : Blo 519798 1316483 := bstep (se 1 (by rfl) ⟨987362, by rfl⟩ : syracuseStep 1316483 = 1974725) B1974725
theorem B1250947 : Blo 519798 1250947 := bstep (se 1 (by rfl) ⟨938210, by rfl⟩ : syracuseStep 1250947 = 1876421) B1876421
theorem B4232845 : Blo 519798 4232845 := bstep (se 3 (by rfl) ⟨793658, by rfl⟩ : syracuseStep 4232845 = 1587317) B1587317
theorem B1054385 : Blo 519798 1054385 := bstep (se 2 (by rfl) ⟨395394, by rfl⟩ : syracuseStep 1054385 = 790789) B790789
theorem B1316675 : Blo 519798 1316675 := bstep (se 1 (by rfl) ⟨987506, by rfl⟩ : syracuseStep 1316675 = 1975013) B1975013
theorem B1480589 : Blo 519798 1480589 := bstep (se 3 (by rfl) ⟨277610, by rfl⟩ : syracuseStep 1480589 = 555221) B555221
theorem B1251217 : Blo 519798 1251217 := bstep (se 2 (by rfl) ⟨469206, by rfl⟩ : syracuseStep 1251217 = 938413) B938413
theorem B1677361 : Blo 519798 1677361 := bstep (se 2 (by rfl) ⟨629010, by rfl⟩ : syracuseStep 1677361 = 1258021) B1258021
theorem B1480781 : Blo 519798 1480781 := bstep (se 3 (by rfl) ⟨277646, by rfl⟩ : syracuseStep 1480781 = 555293) B555293
theorem B661603 : Blo 519798 661603 := bstep (se 1 (by rfl) ⟨496202, by rfl⟩ : syracuseStep 661603 = 992405) B992405
theorem B989329 : Blo 519798 989329 := bstep (se 2 (by rfl) ⟨370998, by rfl⟩ : syracuseStep 989329 = 741997) B741997
theorem B661699 : Blo 519798 661699 := bstep (se 1 (by rfl) ⟨496274, by rfl⟩ : syracuseStep 661699 = 992549) B992549
theorem B792833 : Blo 519798 792833 := bstep (se 2 (by rfl) ⟨297312, by rfl⟩ : syracuseStep 792833 = 594625) B594625
theorem B989489 : Blo 519798 989489 := bstep (se 2 (by rfl) ⟨371058, by rfl⟩ : syracuseStep 989489 = 742117) B742117
theorem B3578309 : Blo 519798 3578309 := bstep (se 4 (by rfl) ⟨335466, by rfl⟩ : syracuseStep 3578309 = 670933) B670933
theorem B629203 : Blo 519798 629203 := bstep (se 1 (by rfl) ⟨471902, by rfl⟩ : syracuseStep 629203 = 943805) B943805
theorem B596531 : Blo 519798 596531 := bstep (se 1 (by rfl) ⟨447398, by rfl⟩ : syracuseStep 596531 = 894797) B894797
theorem B662195 : Blo 519798 662195 := bstep (se 1 (by rfl) ⟨496646, by rfl⟩ : syracuseStep 662195 = 993293) B993293
theorem B989891 : Blo 519798 989891 := bstep (se 1 (by rfl) ⟨742418, by rfl⟩ : syracuseStep 989891 = 1484837) B1484837
theorem B1317617 : Blo 519798 1317617 := bstep (se 2 (by rfl) ⟨494106, by rfl⟩ : syracuseStep 1317617 = 988213) B988213
theorem B1317667 : Blo 519798 1317667 := bstep (se 1 (by rfl) ⟨988250, by rfl⟩ : syracuseStep 1317667 = 1976501) B1976501
theorem B2235235 : Blo 519798 2235235 := bstep (se 1 (by rfl) ⟨1676426, by rfl⟩ : syracuseStep 2235235 = 3352853) B3352853
theorem B1317809 : Blo 519798 1317809 := bstep (se 2 (by rfl) ⟨494178, by rfl⟩ : syracuseStep 1317809 = 988357) B988357
theorem B891827 : Blo 519798 891827 := bstep (se 1 (by rfl) ⟨668870, by rfl⟩ : syracuseStep 891827 = 1337741) B1337741
theorem B1055683 : Blo 519798 1055683 := bstep (se 1 (by rfl) ⟨791762, by rfl⟩ : syracuseStep 1055683 = 1583525) B1583525
theorem B1481773 : Blo 519798 1481773 := bstep (se 3 (by rfl) ⟨277832, by rfl⟩ : syracuseStep 1481773 = 555665) B555665
theorem B662899 : Blo 519798 662899 := bstep (se 1 (by rfl) ⟨497174, by rfl⟩ : syracuseStep 662899 = 994349) B994349
theorem B2498033 : Blo 519798 2498033 := bstep (se 2 (by rfl) ⟨936762, by rfl⟩ : syracuseStep 2498033 = 1873525) B1873525
theorem B990787 : Blo 519798 990787 := bstep (se 1 (by rfl) ⟨743090, by rfl⟩ : syracuseStep 990787 = 1486181) B1486181
theorem B794243 : Blo 519798 794243 := bstep (se 1 (by rfl) ⟨595682, by rfl⟩ : syracuseStep 794243 = 1191365) B1191365
theorem B990947 : Blo 519798 990947 := bstep (se 1 (by rfl) ⟨743210, by rfl⟩ : syracuseStep 990947 = 1486421) B1486421
theorem B1187569 : Blo 519798 1187569 := bstep (se 2 (by rfl) ⟨445338, by rfl⟩ : syracuseStep 1187569 = 890677) B890677
theorem B1318801 : Blo 519798 1318801 := bstep (se 2 (by rfl) ⟨494550, by rfl⟩ : syracuseStep 1318801 = 989101) B989101
theorem B2007089 : Blo 519798 2007089 := bstep (se 2 (by rfl) ⟨752658, by rfl⟩ : syracuseStep 2007089 = 1505317) B1505317
theorem B1319075 : Blo 519798 1319075 := bstep (se 1 (by rfl) ⟨989306, by rfl⟩ : syracuseStep 1319075 = 1978613) B1978613
theorem B893155 : Blo 519798 893155 := bstep (se 1 (by rfl) ⟨669866, by rfl⟩ : syracuseStep 893155 = 1339733) B1339733
theorem B1319267 : Blo 519798 1319267 := bstep (se 1 (by rfl) ⟨989450, by rfl⟩ : syracuseStep 1319267 = 1978901) B1978901
theorem B2498957 : Blo 519798 2498957 := bstep (se 3 (by rfl) ⟨468554, by rfl⟩ : syracuseStep 2498957 = 937109) B937109
theorem B1483505 : Blo 519798 1483505 := bstep (se 2 (by rfl) ⟨556314, by rfl⟩ : syracuseStep 1483505 = 1112629) B1112629
theorem B992017 : Blo 519798 992017 := bstep (se 2 (by rfl) ⟨372006, by rfl⟩ : syracuseStep 992017 = 744013) B744013
theorem B2237233 : Blo 519798 2237233 := bstep (se 2 (by rfl) ⟨838962, by rfl⟩ : syracuseStep 2237233 = 1677925) B1677925
theorem B307635029 : Blo 519798 307635029 := bstep (se 9 (by rfl) ⟨901274, by rfl⟩ : syracuseStep 307635029 = 1802549) B1802549
theorem B1483697 : Blo 519798 1483697 := bstep (se 2 (by rfl) ⟨556386, by rfl⟩ : syracuseStep 1483697 = 1112773) B1112773
theorem B893921 : Blo 519798 893921 := bstep (se 2 (by rfl) ⟨335220, by rfl⟩ : syracuseStep 893921 = 670441) B670441
theorem B1320209 : Blo 519798 1320209 := bstep (se 2 (by rfl) ⟨495078, by rfl⟩ : syracuseStep 1320209 = 990157) B990157
theorem B1320259 : Blo 519798 1320259 := bstep (se 1 (by rfl) ⟨990194, by rfl⟩ : syracuseStep 1320259 = 1980389) B1980389
theorem B1320401 : Blo 519798 1320401 := bstep (se 2 (by rfl) ⟨495150, by rfl⟩ : syracuseStep 1320401 = 990301) B990301
theorem B1877489 : Blo 519798 1877489 := bstep (se 2 (by rfl) ⟨704058, by rfl⟩ : syracuseStep 1877489 = 1408117) B1408117
theorem B2827781 : Blo 519798 2827781 := bstep (se 4 (by rfl) ⟨265104, by rfl⟩ : syracuseStep 2827781 = 530209) B530209
theorem B4236869 : Blo 519798 4236869 := bstep (se 4 (by rfl) ⟨397206, by rfl⟩ : syracuseStep 4236869 = 794413) B794413
theorem B4531781 : Blo 519798 4531781 := bstep (se 4 (by rfl) ⟨424854, by rfl⟩ : syracuseStep 4531781 = 849709) B849709
theorem B1975985 : Blo 519798 1975985 := bstep (se 2 (by rfl) ⟨740994, by rfl⟩ : syracuseStep 1975985 = 1481989) B1481989
theorem B3352261 : Blo 519798 3352261 := bstep (se 4 (by rfl) ⟨314274, by rfl⟩ : syracuseStep 3352261 = 628549) B628549
theorem B993073 : Blo 519798 993073 := bstep (se 2 (by rfl) ⟨372402, by rfl⟩ : syracuseStep 993073 = 744805) B744805
theorem B1484689 : Blo 519798 1484689 := bstep (se 2 (by rfl) ⟨556758, by rfl⟩ : syracuseStep 1484689 = 1113517) B1113517
theorem B1255331 : Blo 519798 1255331 := bstep (se 1 (by rfl) ⟨941498, by rfl⟩ : syracuseStep 1255331 = 1882997) B1882997
theorem B1484963 : Blo 519798 1484963 := bstep (se 1 (by rfl) ⟨1113722, by rfl⟩ : syracuseStep 1484963 = 2227445) B2227445
theorem B993475 : Blo 519798 993475 := bstep (se 1 (by rfl) ⟨745106, by rfl⟩ : syracuseStep 993475 = 1490213) B1490213
theorem B993521 : Blo 519798 993521 := bstep (se 2 (by rfl) ⟨372570, by rfl⟩ : syracuseStep 993521 = 745141) B745141
theorem B1255715 : Blo 519798 1255715 := bstep (se 1 (by rfl) ⟨941786, by rfl⟩ : syracuseStep 1255715 = 1883573) B1883573
theorem B2632013 : Blo 519798 2632013 := bstep (se 3 (by rfl) ⟨493502, by rfl⟩ : syracuseStep 2632013 = 987005) B987005
theorem B1485155 : Blo 519798 1485155 := bstep (se 1 (by rfl) ⟨1113866, by rfl⟩ : syracuseStep 1485155 = 2227733) B2227733
theorem B1550765 : Blo 519798 1550765 := bstep (se 3 (by rfl) ⟨290768, by rfl⟩ : syracuseStep 1550765 = 581537) B581537
theorem B1321393 : Blo 519798 1321393 := bstep (se 2 (by rfl) ⟨495522, by rfl⟩ : syracuseStep 1321393 = 991045) B991045
theorem B993809 : Blo 519798 993809 := bstep (se 2 (by rfl) ⟨372678, by rfl⟩ : syracuseStep 993809 = 745357) B745357
theorem B1321667 : Blo 519798 1321667 := bstep (se 1 (by rfl) ⟨991250, by rfl⟩ : syracuseStep 1321667 = 1982501) B1982501
theorem B1256273 : Blo 519798 1256273 := bstep (se 2 (by rfl) ⟨471102, by rfl⟩ : syracuseStep 1256273 = 942205) B942205
theorem B1321859 : Blo 519798 1321859 := bstep (se 1 (by rfl) ⟨991394, by rfl⟩ : syracuseStep 1321859 = 1982789) B1982789
theorem B1256483 : Blo 519798 1256483 := bstep (se 1 (by rfl) ⟨942362, by rfl⟩ : syracuseStep 1256483 = 1884725) B1884725
theorem B1977443 : Blo 519798 1977443 := bstep (se 1 (by rfl) ⟨1483082, by rfl⟩ : syracuseStep 1977443 = 2966165) B2966165
theorem B1485965 : Blo 519798 1485965 := bstep (se 3 (by rfl) ⟨278618, by rfl⟩ : syracuseStep 1485965 = 557237) B557237
theorem B2829509 : Blo 519798 2829509 := bstep (se 4 (by rfl) ⟨265266, by rfl⟩ : syracuseStep 2829509 = 530533) B530533
theorem B2534627 : Blo 519798 2534627 := bstep (se 1 (by rfl) ⟨1900970, by rfl⟩ : syracuseStep 2534627 = 3801941) B3801941
theorem B1486147 : Blo 519798 1486147 := bstep (se 1 (by rfl) ⟨1114610, by rfl⟩ : syracuseStep 1486147 = 2229221) B2229221
theorem B1125827 : Blo 519798 1125827 := bstep (se 1 (by rfl) ⟨844370, by rfl⟩ : syracuseStep 1125827 = 1688741) B1688741
theorem B1060547 : Blo 519798 1060547 := bstep (se 1 (by rfl) ⟨795410, by rfl⟩ : syracuseStep 1060547 = 1590821) B1590821
theorem B2830115 : Blo 519798 2830115 := bstep (se 1 (by rfl) ⟨2122586, by rfl⟩ : syracuseStep 2830115 = 4245173) B4245173
theorem B1486637 : Blo 519798 1486637 := bstep (se 3 (by rfl) ⟨278744, by rfl⟩ : syracuseStep 1486637 = 557489) B557489
theorem B1322801 : Blo 519798 1322801 := bstep (se 2 (by rfl) ⟨496050, by rfl⟩ : syracuseStep 1322801 = 992101) B992101
theorem B3747653 : Blo 519798 3747653 := bstep (se 4 (by rfl) ⟨351342, by rfl⟩ : syracuseStep 3747653 = 702685) B702685
theorem B1322851 : Blo 519798 1322851 := bstep (se 1 (by rfl) ⟨992138, by rfl⟩ : syracuseStep 1322851 = 1984277) B1984277
theorem B1257329 : Blo 519798 1257329 := bstep (se 2 (by rfl) ⟨471498, by rfl⟩ : syracuseStep 1257329 = 942997) B942997
theorem B1322993 : Blo 519798 1322993 := bstep (se 2 (by rfl) ⟨496122, by rfl⟩ : syracuseStep 1322993 = 992245) B992245
theorem B1978445 : Blo 519798 1978445 := bstep (se 3 (by rfl) ⟨370958, by rfl⟩ : syracuseStep 1978445 = 741917) B741917
theorem B1585325 : Blo 519798 1585325 := bstep (se 3 (by rfl) ⟨297248, by rfl⟩ : syracuseStep 1585325 = 594497) B594497
theorem B3354979 : Blo 519798 3354979 := bstep (se 1 (by rfl) ⟨2516234, by rfl⟩ : syracuseStep 3354979 = 5032469) B5032469
theorem B1257859 : Blo 519798 1257859 := bstep (se 1 (by rfl) ⟨943394, by rfl⟩ : syracuseStep 1257859 = 1886789) B1886789
theorem B1028675 : Blo 519798 1028675 := bstep (se 1 (by rfl) ⟨771506, by rfl⟩ : syracuseStep 1028675 = 1543013) B1543013
theorem B4239985 : Blo 519798 4239985 := bstep (se 2 (by rfl) ⟨1589994, by rfl⟩ : syracuseStep 4239985 = 3179989) B3179989
theorem B1880803 : Blo 519798 1880803 := bstep (se 1 (by rfl) ⟨1410602, by rfl⟩ : syracuseStep 1880803 = 2821205) B2821205
theorem B1487821 : Blo 519798 1487821 := bstep (se 3 (by rfl) ⟨278966, by rfl⟩ : syracuseStep 1487821 = 557933) B557933
theorem B1323985 : Blo 519798 1323985 := bstep (se 2 (by rfl) ⟨496494, by rfl⟩ : syracuseStep 1323985 = 992989) B992989
theorem B2962565 : Blo 519798 2962565 := bstep (se 4 (by rfl) ⟨277740, by rfl⟩ : syracuseStep 2962565 = 555481) B555481
theorem B2634929 : Blo 519798 2634929 := bstep (se 2 (by rfl) ⟨988098, by rfl⟩ : syracuseStep 2634929 = 1976197) B1976197
theorem B1324259 : Blo 519798 1324259 := bstep (se 1 (by rfl) ⟨993194, by rfl⟩ : syracuseStep 1324259 = 1986389) B1986389
theorem B1324451 : Blo 519798 1324451 := bstep (se 1 (by rfl) ⟨993338, by rfl⟩ : syracuseStep 1324451 = 1986677) B1986677
theorem B833107 : Blo 519798 833107 := bstep (se 1 (by rfl) ⟨624830, by rfl⟩ : syracuseStep 833107 = 1249661) B1249661
theorem B2963249 : Blo 519798 2963249 := bstep (se 2 (by rfl) ⟨1111218, by rfl⟩ : syracuseStep 2963249 = 2222437) B2222437
theorem B1488881 : Blo 519798 1488881 := bstep (se 2 (by rfl) ⟨558330, by rfl⟩ : syracuseStep 1488881 = 1116661) B1116661
theorem B833555 : Blo 519798 833555 := bstep (se 1 (by rfl) ⟨625166, by rfl⟩ : syracuseStep 833555 = 1250333) B1250333
theorem B702577 : Blo 519798 702577 := bstep (se 2 (by rfl) ⟨263466, by rfl⟩ : syracuseStep 702577 = 526933) B526933
theorem B1980557 : Blo 519798 1980557 := bstep (se 3 (by rfl) ⟨371354, by rfl⟩ : syracuseStep 1980557 = 742709) B742709
theorem B604435 : Blo 519798 604435 := bstep (se 1 (by rfl) ⟨453326, by rfl⟩ : syracuseStep 604435 = 906653) B906653
theorem B1325393 : Blo 519798 1325393 := bstep (se 2 (by rfl) ⟨497022, by rfl⟩ : syracuseStep 1325393 = 994045) B994045
theorem B1325443 : Blo 519798 1325443 := bstep (se 1 (by rfl) ⟨994082, by rfl⟩ : syracuseStep 1325443 = 1988165) B1988165
theorem B1325585 : Blo 519798 1325585 := bstep (se 2 (by rfl) ⟨497094, by rfl⟩ : syracuseStep 1325585 = 994189) B994189
theorem B834113 : Blo 519798 834113 := bstep (se 2 (by rfl) ⟨312792, by rfl⟩ : syracuseStep 834113 = 625585) B625585
theorem B2636387 : Blo 519798 2636387 := bstep (se 1 (by rfl) ⟨1977290, by rfl⟩ : syracuseStep 2636387 = 3954581) B3954581
theorem B703091 : Blo 519798 703091 := bstep (se 1 (by rfl) ⟨527318, by rfl⟩ : syracuseStep 703091 = 1054637) B1054637
theorem B1489553 : Blo 519798 1489553 := bstep (se 2 (by rfl) ⟨558582, by rfl⟩ : syracuseStep 1489553 = 1117165) B1117165
theorem B834337 : Blo 519798 834337 := bstep (se 2 (by rfl) ⟨312876, by rfl⟩ : syracuseStep 834337 = 625753) B625753
theorem B834401 : Blo 519798 834401 := bstep (se 2 (by rfl) ⟨312900, by rfl⟩ : syracuseStep 834401 = 625801) B625801
theorem B1981361 : Blo 519798 1981361 := bstep (se 2 (by rfl) ⟨743010, by rfl⟩ : syracuseStep 1981361 = 1486021) B1486021
theorem B834529 : Blo 519798 834529 := bstep (se 2 (by rfl) ⟨312948, by rfl⟩ : syracuseStep 834529 = 625897) B625897
theorem B1883213 : Blo 519798 1883213 := bstep (se 3 (by rfl) ⟨353102, by rfl⟩ : syracuseStep 1883213 = 706205) B706205
theorem B1883341 : Blo 519798 1883341 := bstep (se 3 (by rfl) ⟨353126, by rfl⟩ : syracuseStep 1883341 = 706253) B706253
theorem B2964707 : Blo 519798 2964707 := bstep (se 1 (by rfl) ⟨2223530, by rfl⟩ : syracuseStep 2964707 = 4447061) B4447061
theorem B21445859 : Blo 519798 21445859 := bstep (se 1 (by rfl) ⟨16084394, by rfl⟩ : syracuseStep 21445859 = 32168789) B32168789
theorem B2637197 : Blo 519798 2637197 := bstep (se 3 (by rfl) ⟨494474, by rfl⟩ : syracuseStep 2637197 = 988949) B988949
theorem B1490339 : Blo 519798 1490339 := bstep (se 1 (by rfl) ⟨1117754, by rfl⟩ : syracuseStep 1490339 = 2235509) B2235509
theorem B1982029 : Blo 519798 1982029 := bstep (se 3 (by rfl) ⟨371630, by rfl⟩ : syracuseStep 1982029 = 743261) B743261
theorem B1490669 : Blo 519798 1490669 := bstep (se 3 (by rfl) ⟨279500, by rfl⟩ : syracuseStep 1490669 = 559001) B559001
theorem B1392419 : Blo 519798 1392419 := bstep (se 1 (by rfl) ⟨1044314, by rfl⟩ : syracuseStep 1392419 = 2088629) B2088629
theorem B1490737 : Blo 519798 1490737 := bstep (se 2 (by rfl) ⟨559026, by rfl⟩ : syracuseStep 1490737 = 1118053) B1118053
theorem B1491011 : Blo 519798 1491011 := bstep (se 1 (by rfl) ⟨1118258, by rfl⟩ : syracuseStep 1491011 = 2236517) B2236517
theorem B1982819 : Blo 519798 1982819 := bstep (se 1 (by rfl) ⟨1487114, by rfl⟩ : syracuseStep 1982819 = 2974229) B2974229
theorem B1524227 : Blo 519798 1524227 := bstep (se 1 (by rfl) ⟨1143170, by rfl⟩ : syracuseStep 1524227 = 2286341) B2286341
theorem B2376305 : Blo 519798 2376305 := bstep (se 2 (by rfl) ⟨891114, by rfl⟩ : syracuseStep 2376305 = 1782229) B1782229
theorem B836579 : Blo 519798 836579 := bstep (se 1 (by rfl) ⟨627434, by rfl⟩ : syracuseStep 836579 = 1254869) B1254869
theorem B2114545 : Blo 519798 2114545 := bstep (se 2 (by rfl) ⟨792954, by rfl⟩ : syracuseStep 2114545 = 1585909) B1585909
theorem B1983473 : Blo 519798 1983473 := bstep (se 2 (by rfl) ⟨743802, by rfl⟩ : syracuseStep 1983473 = 1487605) B1487605
theorem B2671949 : Blo 519798 2671949 := bstep (se 3 (by rfl) ⟨500990, by rfl⟩ : syracuseStep 2671949 = 1001981) B1001981
theorem B1754513 : Blo 519798 1754513 := bstep (se 2 (by rfl) ⟨657942, by rfl⟩ : syracuseStep 1754513 = 1315885) B1315885
theorem B837425 : Blo 519798 837425 := bstep (se 2 (by rfl) ⟨314034, by rfl⟩ : syracuseStep 837425 = 628069) B628069
theorem B1755053 : Blo 519798 1755053 := bstep (se 3 (by rfl) ⟨329072, by rfl⟩ : syracuseStep 1755053 = 658145) B658145
theorem B1755107 : Blo 519798 1755107 := bstep (se 1 (by rfl) ⟨1316330, by rfl⟩ : syracuseStep 1755107 = 2632661) B2632661
theorem B1001521 : Blo 519798 1001521 := bstep (se 2 (by rfl) ⟨375570, by rfl⟩ : syracuseStep 1001521 = 751141) B751141
theorem B5621957 : Blo 519798 5621957 := bstep (se 4 (by rfl) ⟨527058, by rfl⟩ : syracuseStep 5621957 = 1054117) B1054117
theorem B1755377 : Blo 519798 1755377 := bstep (se 2 (by rfl) ⟨658266, by rfl⟩ : syracuseStep 1755377 = 1316533) B1316533
theorem B3754225 : Blo 519798 3754225 := bstep (se 2 (by rfl) ⟨1407834, by rfl⟩ : syracuseStep 3754225 = 2815669) B2815669
theorem B2640113 : Blo 519798 2640113 := bstep (se 2 (by rfl) ⟨990042, by rfl⟩ : syracuseStep 2640113 = 1980085) B1980085
theorem B3557681 : Blo 519798 3557681 := bstep (se 2 (by rfl) ⟨1334130, by rfl⟩ : syracuseStep 3557681 = 2668261) B2668261
theorem B2967941 : Blo 519798 2967941 := bstep (se 4 (by rfl) ⟨278244, by rfl⟩ : syracuseStep 2967941 = 556489) B556489
theorem B1591697 : Blo 519798 1591697 := bstep (se 2 (by rfl) ⟨596886, by rfl⟩ : syracuseStep 1591697 = 1193773) B1193773
theorem B1984931 : Blo 519798 1984931 := bstep (se 1 (by rfl) ⟨1488698, by rfl⟩ : syracuseStep 1984931 = 2977397) B2977397
theorem B1984945 : Blo 519798 1984945 := bstep (se 2 (by rfl) ⟨744354, by rfl⟩ : syracuseStep 1984945 = 1488709) B1488709
theorem B2411021 : Blo 519798 2411021 := bstep (se 3 (by rfl) ⟨452066, by rfl⟩ : syracuseStep 2411021 = 904133) B904133
theorem B838163 : Blo 519798 838163 := bstep (se 1 (by rfl) ⟨628622, by rfl⟩ : syracuseStep 838163 = 1257245) B1257245
theorem B1755917 : Blo 519798 1755917 := bstep (se 3 (by rfl) ⟨329234, by rfl⟩ : syracuseStep 1755917 = 658469) B658469
theorem B772915 : Blo 519798 772915 := bstep (se 1 (by rfl) ⟨579686, by rfl⟩ : syracuseStep 772915 = 1159373) B1159373
theorem B1755971 : Blo 519798 1755971 := bstep (se 1 (by rfl) ⟨1316978, by rfl⟩ : syracuseStep 1755971 = 2633957) B2633957
theorem B2968397 : Blo 519798 2968397 := bstep (se 3 (by rfl) ⟨556574, by rfl⟩ : syracuseStep 2968397 = 1113149) B1113149
theorem B936785 : Blo 519798 936785 := bstep (se 2 (by rfl) ⟨351294, by rfl⟩ : syracuseStep 936785 = 702589) B702589
theorem B1756241 : Blo 519798 1756241 := bstep (se 2 (by rfl) ⟨658590, by rfl⟩ : syracuseStep 1756241 = 1317181) B1317181
theorem B5786765 : Blo 519798 5786765 := bstep (se 3 (by rfl) ⟨1085018, by rfl⟩ : syracuseStep 5786765 = 2170037) B2170037
theorem B740659 : Blo 519798 740659 := bstep (se 1 (by rfl) ⟨555494, by rfl⟩ : syracuseStep 740659 = 1110989) B1110989
theorem B5000561 : Blo 519798 5000561 := bstep (se 2 (by rfl) ⟨1875210, by rfl⟩ : syracuseStep 5000561 = 3750421) B3750421
theorem B740755 : Blo 519798 740755 := bstep (se 1 (by rfl) ⟨555566, by rfl⟩ : syracuseStep 740755 = 1111133) B1111133
theorem B1756781 : Blo 519798 1756781 := bstep (se 3 (by rfl) ⟨329396, by rfl⟩ : syracuseStep 1756781 = 658793) B658793
theorem B1756835 : Blo 519798 1756835 := bstep (se 1 (by rfl) ⟨1317626, by rfl⟩ : syracuseStep 1756835 = 2635253) B2635253
theorem B2641571 : Blo 519798 2641571 := bstep (se 1 (by rfl) ⟨1981178, by rfl⟩ : syracuseStep 2641571 = 3962357) B3962357
theorem B5426957 : Blo 519798 5426957 := bstep (se 3 (by rfl) ⟨1017554, by rfl⟩ : syracuseStep 5426957 = 2035109) B2035109
theorem B1986403 : Blo 519798 1986403 := bstep (se 1 (by rfl) ⟨1489802, by rfl⟩ : syracuseStep 1986403 = 2979605) B2979605
theorem B741251 : Blo 519798 741251 := bstep (se 1 (by rfl) ⟨555938, by rfl⟩ : syracuseStep 741251 = 1111877) B1111877
theorem B5001101 : Blo 519798 5001101 := bstep (se 3 (by rfl) ⟨937706, by rfl⟩ : syracuseStep 5001101 = 1875413) B1875413
theorem B1757105 : Blo 519798 1757105 := bstep (se 2 (by rfl) ⟨658914, by rfl⟩ : syracuseStep 1757105 = 1317829) B1317829
theorem B2510797 : Blo 519798 2510797 := bstep (se 3 (by rfl) ⟨470774, by rfl⟩ : syracuseStep 2510797 = 941549) B941549
theorem B6443107 : Blo 519798 6443107 := bstep (se 1 (by rfl) ⟨4832330, by rfl⟩ : syracuseStep 6443107 = 9664661) B9664661
theorem B1757645 : Blo 519798 1757645 := bstep (se 3 (by rfl) ⟨329558, by rfl⟩ : syracuseStep 1757645 = 659117) B659117
theorem B2642381 : Blo 519798 2642381 := bstep (se 3 (by rfl) ⟨495446, by rfl⟩ : syracuseStep 2642381 = 990893) B990893
theorem B3953123 : Blo 519798 3953123 := bstep (se 1 (by rfl) ⟨2964842, by rfl⟩ : syracuseStep 3953123 = 5929685) B5929685
theorem B741889 : Blo 519798 741889 := bstep (se 2 (by rfl) ⟨278208, by rfl⟩ : syracuseStep 741889 = 556417) B556417
theorem B1757699 : Blo 519798 1757699 := bstep (se 1 (by rfl) ⟨1318274, by rfl⟩ : syracuseStep 1757699 = 2636549) B2636549
theorem B2118307 : Blo 519798 2118307 := bstep (se 1 (by rfl) ⟨1588730, by rfl⟩ : syracuseStep 2118307 = 3177461) B3177461
theorem B1757969 : Blo 519798 1757969 := bstep (se 2 (by rfl) ⟨659238, by rfl⟩ : syracuseStep 1757969 = 1318477) B1318477
theorem B742225 : Blo 519798 742225 := bstep (se 2 (by rfl) ⟨278334, by rfl⟩ : syracuseStep 742225 = 556669) B556669
theorem B906209 : Blo 519798 906209 := bstep (se 2 (by rfl) ⟨339828, by rfl⟩ : syracuseStep 906209 = 679657) B679657
theorem B3331043 : Blo 519798 3331043 := bstep (se 1 (by rfl) ⟨2498282, by rfl⟩ : syracuseStep 3331043 = 4996565) B4996565
theorem B1791085 : Blo 519798 1791085 := bstep (se 3 (by rfl) ⟨335828, by rfl⟩ : syracuseStep 1791085 = 671657) B671657
theorem B4216049 : Blo 519798 4216049 := bstep (se 2 (by rfl) ⟨1581018, by rfl⟩ : syracuseStep 4216049 = 3162037) B3162037
theorem B1758509 : Blo 519798 1758509 := bstep (se 3 (by rfl) ⟨329720, by rfl⟩ : syracuseStep 1758509 = 659441) B659441
theorem B1758563 : Blo 519798 1758563 := bstep (se 1 (by rfl) ⟨1318922, by rfl⟩ : syracuseStep 1758563 = 2637845) B2637845
theorem B742817 : Blo 519798 742817 := bstep (se 2 (by rfl) ⟨278556, by rfl⟩ : syracuseStep 742817 = 557113) B557113
theorem B1758833 : Blo 519798 1758833 := bstep (se 2 (by rfl) ⟨659562, by rfl⟩ : syracuseStep 1758833 = 1319125) B1319125
theorem B2971313 : Blo 519798 2971313 := bstep (se 2 (by rfl) ⟨1114242, by rfl⟩ : syracuseStep 2971313 = 2228485) B2228485
theorem B2119409 : Blo 519798 2119409 := bstep (se 2 (by rfl) ⟨794778, by rfl⟩ : syracuseStep 2119409 = 1589557) B1589557
theorem B743347 : Blo 519798 743347 := bstep (se 1 (by rfl) ⟨557510, by rfl⟩ : syracuseStep 743347 = 1115021) B1115021
theorem B1988621 : Blo 519798 1988621 := bstep (se 3 (by rfl) ⟨372866, by rfl⟩ : syracuseStep 1988621 = 745733) B745733
theorem B3004465 : Blo 519798 3004465 := bstep (se 2 (by rfl) ⟨1126674, by rfl⟩ : syracuseStep 3004465 = 2253349) B2253349
theorem B1759373 : Blo 519798 1759373 := bstep (se 3 (by rfl) ⟨329882, by rfl⟩ : syracuseStep 1759373 = 659765) B659765
theorem B1169585 : Blo 519798 1169585 := bstep (se 2 (by rfl) ⟨438594, by rfl⟩ : syracuseStep 1169585 = 877189) B877189
theorem B2250929 : Blo 519798 2250929 := bstep (se 2 (by rfl) ⟨844098, by rfl⟩ : syracuseStep 2250929 = 1688197) B1688197
theorem B1169603 : Blo 519798 1169603 := bstep (se 1 (by rfl) ⟨877202, by rfl⟩ : syracuseStep 1169603 = 1754405) B1754405
theorem B1759427 : Blo 519798 1759427 := bstep (se 1 (by rfl) ⟨1319570, by rfl⟩ : syracuseStep 1759427 = 2639141) B2639141
theorem B1267939 : Blo 519798 1267939 := bstep (se 1 (by rfl) ⟨950954, by rfl⟩ : syracuseStep 1267939 = 1901909) B1901909
theorem B743683 : Blo 519798 743683 := bstep (se 1 (by rfl) ⟨557762, by rfl⟩ : syracuseStep 743683 = 1115525) B1115525
theorem B1169873 : Blo 519798 1169873 := bstep (se 2 (by rfl) ⟨438702, by rfl⟩ : syracuseStep 1169873 = 877405) B877405
theorem B1759697 : Blo 519798 1759697 := bstep (se 2 (by rfl) ⟨659886, by rfl⟩ : syracuseStep 1759697 = 1319773) B1319773
theorem B1169891 : Blo 519798 1169891 := bstep (se 1 (by rfl) ⟨877418, by rfl⟩ : syracuseStep 1169891 = 1754837) B1754837
theorem B940547 : Blo 519798 940547 := bstep (se 1 (by rfl) ⟨705410, by rfl⟩ : syracuseStep 940547 = 1410821) B1410821
theorem B1170161 : Blo 519798 1170161 := bstep (se 2 (by rfl) ⟨438810, by rfl⟩ : syracuseStep 1170161 = 877621) B877621
theorem B1170179 : Blo 519798 1170179 := bstep (se 1 (by rfl) ⟨877634, by rfl⟩ : syracuseStep 1170179 = 1755269) B1755269
theorem B940835 : Blo 519798 940835 := bstep (se 1 (by rfl) ⟨705626, by rfl⟩ : syracuseStep 940835 = 1411253) B1411253
theorem B744241 : Blo 519798 744241 := bstep (se 2 (by rfl) ⟨279090, by rfl⟩ : syracuseStep 744241 = 558181) B558181
theorem B744275 : Blo 519798 744275 := bstep (se 1 (by rfl) ⟨558206, by rfl⟩ : syracuseStep 744275 = 1116413) B1116413
theorem B1760237 : Blo 519798 1760237 := bstep (se 3 (by rfl) ⟨330044, by rfl⟩ : syracuseStep 1760237 = 660089) B660089
theorem B1170449 : Blo 519798 1170449 := bstep (se 2 (by rfl) ⟨438918, by rfl⟩ : syracuseStep 1170449 = 877837) B877837
theorem B1170467 : Blo 519798 1170467 := bstep (se 1 (by rfl) ⟨877850, by rfl⟩ : syracuseStep 1170467 = 1755701) B1755701
theorem B1760291 : Blo 519798 1760291 := bstep (se 1 (by rfl) ⟨1320218, by rfl⟩ : syracuseStep 1760291 = 2640437) B2640437
theorem B2972771 : Blo 519798 2972771 := bstep (se 1 (by rfl) ⟨2229578, by rfl⟩ : syracuseStep 2972771 = 4459157) B4459157
theorem B1170737 : Blo 519798 1170737 := bstep (se 2 (by rfl) ⟨439026, by rfl⟩ : syracuseStep 1170737 = 878053) B878053
theorem B1760561 : Blo 519798 1760561 := bstep (se 2 (by rfl) ⟨660210, by rfl⟩ : syracuseStep 1760561 = 1320421) B1320421
theorem B2645297 : Blo 519798 2645297 := bstep (se 2 (by rfl) ⟨991986, by rfl⟩ : syracuseStep 2645297 = 1983973) B1983973
theorem B1170755 : Blo 519798 1170755 := bstep (se 1 (by rfl) ⟨878066, by rfl⟩ : syracuseStep 1170755 = 1756133) B1756133
theorem B744833 : Blo 519798 744833 := bstep (se 2 (by rfl) ⟨279312, by rfl⟩ : syracuseStep 744833 = 558625) B558625
theorem B3333581 : Blo 519798 3333581 := bstep (se 3 (by rfl) ⟨625046, by rfl⟩ : syracuseStep 3333581 = 1250093) B1250093
theorem B744913 : Blo 519798 744913 := bstep (se 2 (by rfl) ⟨279342, by rfl⟩ : syracuseStep 744913 = 558685) B558685
theorem B1171025 : Blo 519798 1171025 := bstep (se 2 (by rfl) ⟨439134, by rfl⟩ : syracuseStep 1171025 = 878269) B878269
theorem B1171043 : Blo 519798 1171043 := bstep (se 1 (by rfl) ⟨878282, by rfl⟩ : syracuseStep 1171043 = 1756565) B1756565
theorem B5660401 : Blo 519798 5660401 := bstep (se 2 (by rfl) ⟨2122650, by rfl⟩ : syracuseStep 5660401 = 4245301) B4245301
theorem B1761101 : Blo 519798 1761101 := bstep (se 3 (by rfl) ⟨330206, by rfl⟩ : syracuseStep 1761101 = 660413) B660413
theorem B1171313 : Blo 519798 1171313 := bstep (se 2 (by rfl) ⟨439242, by rfl⟩ : syracuseStep 1171313 = 878485) B878485
theorem B1171331 : Blo 519798 1171331 := bstep (se 1 (by rfl) ⟨878498, by rfl⟩ : syracuseStep 1171331 = 1756997) B1756997
theorem B1761155 : Blo 519798 1761155 := bstep (se 1 (by rfl) ⟨1320866, by rfl⟩ : syracuseStep 1761155 = 2641733) B2641733
theorem B4513763 : Blo 519798 4513763 := bstep (se 1 (by rfl) ⟨3385322, by rfl⟩ : syracuseStep 4513763 = 6770645) B6770645
theorem B2973773 : Blo 519798 2973773 := bstep (se 3 (by rfl) ⟨557582, by rfl⟩ : syracuseStep 2973773 = 1115165) B1115165
theorem B2515043 : Blo 519798 2515043 := bstep (se 1 (by rfl) ⟨1886282, by rfl⟩ : syracuseStep 2515043 = 3772565) B3772565
theorem B1171601 : Blo 519798 1171601 := bstep (se 2 (by rfl) ⟨439350, by rfl⟩ : syracuseStep 1171601 = 878701) B878701
theorem B1761425 : Blo 519798 1761425 := bstep (se 2 (by rfl) ⟨660534, by rfl⟩ : syracuseStep 1761425 = 1321069) B1321069
theorem B1171619 : Blo 519798 1171619 := bstep (se 1 (by rfl) ⟨878714, by rfl⟩ : syracuseStep 1171619 = 1757429) B1757429
theorem B745699 : Blo 519798 745699 := bstep (se 1 (by rfl) ⟨559274, by rfl⟩ : syracuseStep 745699 = 1118549) B1118549
theorem B942449 : Blo 519798 942449 := bstep (se 2 (by rfl) ⟨353418, by rfl⟩ : syracuseStep 942449 = 706837) B706837
theorem B2515313 : Blo 519798 2515313 := bstep (se 2 (by rfl) ⟨943242, by rfl⟩ : syracuseStep 2515313 = 1886485) B1886485
theorem B1171889 : Blo 519798 1171889 := bstep (se 2 (by rfl) ⟨439458, by rfl⟩ : syracuseStep 1171889 = 878917) B878917
theorem B1171907 : Blo 519798 1171907 := bstep (se 1 (by rfl) ⟨878930, by rfl⟩ : syracuseStep 1171907 = 1757861) B1757861
theorem B2515427 : Blo 519798 2515427 := bstep (se 1 (by rfl) ⟨1886570, by rfl⟩ : syracuseStep 2515427 = 3773141) B3773141
theorem B877169 : Blo 519798 877169 := bstep (se 2 (by rfl) ⟨328938, by rfl⟩ : syracuseStep 877169 = 657877) B657877
theorem B1761965 : Blo 519798 1761965 := bstep (se 3 (by rfl) ⟨330368, by rfl⟩ : syracuseStep 1761965 = 660737) B660737
theorem B1172177 : Blo 519798 1172177 := bstep (se 2 (by rfl) ⟨439566, by rfl⟩ : syracuseStep 1172177 = 879133) B879133
theorem B1172195 : Blo 519798 1172195 := bstep (se 1 (by rfl) ⟨879146, by rfl⟩ : syracuseStep 1172195 = 1758293) B1758293
theorem B1762019 : Blo 519798 1762019 := bstep (se 1 (by rfl) ⟨1321514, by rfl⟩ : syracuseStep 1762019 = 2643029) B2643029
theorem B2646755 : Blo 519798 2646755 := bstep (se 1 (by rfl) ⟨1985066, by rfl⟩ : syracuseStep 2646755 = 3970133) B3970133
theorem B877297 : Blo 519798 877297 := bstep (se 2 (by rfl) ⟨328986, by rfl⟩ : syracuseStep 877297 = 657973) B657973
theorem B877331 : Blo 519798 877331 := bstep (se 1 (by rfl) ⟨657998, by rfl⟩ : syracuseStep 877331 = 1315997) B1315997
theorem B877459 : Blo 519798 877459 := bstep (se 1 (by rfl) ⟨658094, by rfl⟩ : syracuseStep 877459 = 1316189) B1316189
theorem B1172465 : Blo 519798 1172465 := bstep (se 2 (by rfl) ⟨439674, by rfl⟩ : syracuseStep 1172465 = 879349) B879349
theorem B1762289 : Blo 519798 1762289 := bstep (se 2 (by rfl) ⟨660858, by rfl⟩ : syracuseStep 1762289 = 1321717) B1321717
theorem B1172483 : Blo 519798 1172483 := bstep (se 1 (by rfl) ⟨879362, by rfl⟩ : syracuseStep 1172483 = 1758725) B1758725
theorem B5923853 : Blo 519798 5923853 := bstep (se 3 (by rfl) ⟨1110722, by rfl⟩ : syracuseStep 5923853 = 2221445) B2221445
theorem B877601 : Blo 519798 877601 := bstep (se 2 (by rfl) ⟨329100, by rfl⟩ : syracuseStep 877601 = 658201) B658201
theorem B877729 : Blo 519798 877729 := bstep (se 2 (by rfl) ⟨329148, by rfl⟩ : syracuseStep 877729 = 658297) B658297
theorem B877763 : Blo 519798 877763 := bstep (se 1 (by rfl) ⟨658322, by rfl⟩ : syracuseStep 877763 = 1316645) B1316645
theorem B1172753 : Blo 519798 1172753 := bstep (se 2 (by rfl) ⟨439782, by rfl⟩ : syracuseStep 1172753 = 879565) B879565
theorem B1172771 : Blo 519798 1172771 := bstep (se 1 (by rfl) ⟨879578, by rfl⟩ : syracuseStep 1172771 = 1759157) B1759157
theorem B877891 : Blo 519798 877891 := bstep (se 1 (by rfl) ⟨658418, by rfl⟩ : syracuseStep 877891 = 1316837) B1316837
theorem B779699 : Blo 519798 779699 := bstep (se 1 (by rfl) ⟨584774, by rfl⟩ : syracuseStep 779699 = 1169549) B1169549
theorem B5662133 : Blo 519798 5662133 := bstep (se 5 (by rfl) ⟨265412, by rfl⟩ : syracuseStep 5662133 = 530825) B530825
theorem B779729 : Blo 519798 779729 := bstep (se 2 (by rfl) ⟨292398, by rfl⟩ : syracuseStep 779729 = 584797) B584797
theorem B878033 : Blo 519798 878033 := bstep (se 2 (by rfl) ⟨329262, by rfl⟩ : syracuseStep 878033 = 658525) B658525
theorem B779747 : Blo 519798 779747 := bstep (se 1 (by rfl) ⟨584810, by rfl⟩ : syracuseStep 779747 = 1169621) B1169621
theorem B779777 : Blo 519798 779777 := bstep (se 2 (by rfl) ⟨292416, by rfl⟩ : syracuseStep 779777 = 584833) B584833
theorem B1762829 : Blo 519798 1762829 := bstep (se 3 (by rfl) ⟨330530, by rfl⟩ : syracuseStep 1762829 = 661061) B661061
theorem B2647565 : Blo 519798 2647565 := bstep (se 3 (by rfl) ⟨496418, by rfl⟩ : syracuseStep 2647565 = 992837) B992837
theorem B779795 : Blo 519798 779795 := bstep (se 1 (by rfl) ⟨584846, by rfl⟩ : syracuseStep 779795 = 1169693) B1169693
theorem B779825 : Blo 519798 779825 := bstep (se 2 (by rfl) ⟨292434, by rfl⟩ : syracuseStep 779825 = 584869) B584869
theorem B1173041 : Blo 519798 1173041 := bstep (se 2 (by rfl) ⟨439890, by rfl⟩ : syracuseStep 1173041 = 879781) B879781
theorem B779843 : Blo 519798 779843 := bstep (se 1 (by rfl) ⟨584882, by rfl⟩ : syracuseStep 779843 = 1169765) B1169765
theorem B1173059 : Blo 519798 1173059 := bstep (se 1 (by rfl) ⟨879794, by rfl⟩ : syracuseStep 1173059 = 1759589) B1759589
theorem B1762883 : Blo 519798 1762883 := bstep (se 1 (by rfl) ⟨1322162, by rfl⟩ : syracuseStep 1762883 = 2644325) B2644325
theorem B878161 : Blo 519798 878161 := bstep (se 2 (by rfl) ⟨329310, by rfl⟩ : syracuseStep 878161 = 658621) B658621
theorem B779873 : Blo 519798 779873 := bstep (se 2 (by rfl) ⟨292452, by rfl⟩ : syracuseStep 779873 = 584905) B584905
theorem B779891 : Blo 519798 779891 := bstep (se 1 (by rfl) ⟨584918, by rfl⟩ : syracuseStep 779891 = 1169837) B1169837
theorem B878195 : Blo 519798 878195 := bstep (se 1 (by rfl) ⟨658646, by rfl⟩ : syracuseStep 878195 = 1317293) B1317293
theorem B779921 : Blo 519798 779921 := bstep (se 2 (by rfl) ⟨292470, by rfl⟩ : syracuseStep 779921 = 584941) B584941
theorem B779939 : Blo 519798 779939 := bstep (se 1 (by rfl) ⟨584954, by rfl⟩ : syracuseStep 779939 = 1169909) B1169909
theorem B779969 : Blo 519798 779969 := bstep (se 2 (by rfl) ⟨292488, by rfl⟩ : syracuseStep 779969 = 584977) B584977
theorem B3958469 : Blo 519798 3958469 := bstep (se 4 (by rfl) ⟨371106, by rfl⟩ : syracuseStep 3958469 = 742213) B742213
theorem B779987 : Blo 519798 779987 := bstep (se 1 (by rfl) ⟨584990, by rfl⟩ : syracuseStep 779987 = 1169981) B1169981
theorem B780017 : Blo 519798 780017 := bstep (se 2 (by rfl) ⟨292506, by rfl⟩ : syracuseStep 780017 = 585013) B585013
theorem B878323 : Blo 519798 878323 := bstep (se 1 (by rfl) ⟨658742, by rfl⟩ : syracuseStep 878323 = 1317485) B1317485
theorem B780035 : Blo 519798 780035 := bstep (se 1 (by rfl) ⟨585026, by rfl⟩ : syracuseStep 780035 = 1170053) B1170053
theorem B5662477 : Blo 519798 5662477 := bstep (se 3 (by rfl) ⟨1061714, by rfl⟩ : syracuseStep 5662477 = 2123429) B2123429
theorem B780065 : Blo 519798 780065 := bstep (se 2 (by rfl) ⟨292524, by rfl⟩ : syracuseStep 780065 = 585049) B585049
theorem B780083 : Blo 519798 780083 := bstep (se 1 (by rfl) ⟨585062, by rfl⟩ : syracuseStep 780083 = 1170125) B1170125
theorem B780113 : Blo 519798 780113 := bstep (se 2 (by rfl) ⟨292542, by rfl⟩ : syracuseStep 780113 = 585085) B585085
theorem B1173329 : Blo 519798 1173329 := bstep (se 2 (by rfl) ⟨439998, by rfl⟩ : syracuseStep 1173329 = 879997) B879997
theorem B1763153 : Blo 519798 1763153 := bstep (se 2 (by rfl) ⟨661182, by rfl⟩ : syracuseStep 1763153 = 1322365) B1322365
theorem B780131 : Blo 519798 780131 := bstep (se 1 (by rfl) ⟨585098, by rfl⟩ : syracuseStep 780131 = 1170197) B1170197
theorem B1173347 : Blo 519798 1173347 := bstep (se 1 (by rfl) ⟨880010, by rfl⟩ : syracuseStep 1173347 = 1760021) B1760021
theorem B14444401 : Blo 519798 14444401 := bstep (se 2 (by rfl) ⟨5416650, by rfl⟩ : syracuseStep 14444401 = 10833301) B10833301
theorem B780161 : Blo 519798 780161 := bstep (se 2 (by rfl) ⟨292560, by rfl⟩ : syracuseStep 780161 = 585121) B585121
theorem B878465 : Blo 519798 878465 := bstep (se 2 (by rfl) ⟨329424, by rfl⟩ : syracuseStep 878465 = 658849) B658849
theorem B780179 : Blo 519798 780179 := bstep (se 1 (by rfl) ⟨585134, by rfl⟩ : syracuseStep 780179 = 1170269) B1170269
theorem B780209 : Blo 519798 780209 := bstep (se 2 (by rfl) ⟨292578, by rfl⟩ : syracuseStep 780209 = 585157) B585157
theorem B780227 : Blo 519798 780227 := bstep (se 1 (by rfl) ⟨585170, by rfl⟩ : syracuseStep 780227 = 1170341) B1170341
theorem B780257 : Blo 519798 780257 := bstep (se 2 (by rfl) ⟨292596, by rfl⟩ : syracuseStep 780257 = 585193) B585193
theorem B780275 : Blo 519798 780275 := bstep (se 1 (by rfl) ⟨585206, by rfl⟩ : syracuseStep 780275 = 1170413) B1170413
theorem B878593 : Blo 519798 878593 := bstep (se 2 (by rfl) ⟨329472, by rfl⟩ : syracuseStep 878593 = 658945) B658945
theorem B780305 : Blo 519798 780305 := bstep (se 2 (by rfl) ⟨292614, by rfl⟩ : syracuseStep 780305 = 585229) B585229
theorem B780323 : Blo 519798 780323 := bstep (se 1 (by rfl) ⟨585242, by rfl⟩ : syracuseStep 780323 = 1170485) B1170485
theorem B878627 : Blo 519798 878627 := bstep (se 1 (by rfl) ⟨658970, by rfl⟩ : syracuseStep 878627 = 1317941) B1317941
theorem B2222129 : Blo 519798 2222129 := bstep (se 2 (by rfl) ⟨833298, by rfl⟩ : syracuseStep 2222129 = 1666597) B1666597
theorem B780353 : Blo 519798 780353 := bstep (se 2 (by rfl) ⟨292632, by rfl⟩ : syracuseStep 780353 = 585265) B585265
theorem B780371 : Blo 519798 780371 := bstep (se 1 (by rfl) ⟨585278, by rfl⟩ : syracuseStep 780371 = 1170557) B1170557
theorem B780401 : Blo 519798 780401 := bstep (se 2 (by rfl) ⟨292650, by rfl⟩ : syracuseStep 780401 = 585301) B585301
theorem B1173617 : Blo 519798 1173617 := bstep (se 2 (by rfl) ⟨440106, by rfl⟩ : syracuseStep 1173617 = 880213) B880213
theorem B780419 : Blo 519798 780419 := bstep (se 1 (by rfl) ⟨585314, by rfl⟩ : syracuseStep 780419 = 1170629) B1170629
theorem B1173635 : Blo 519798 1173635 := bstep (se 1 (by rfl) ⟨880226, by rfl⟩ : syracuseStep 1173635 = 1760453) B1760453
theorem B780449 : Blo 519798 780449 := bstep (se 2 (by rfl) ⟨292668, by rfl⟩ : syracuseStep 780449 = 585337) B585337
theorem B878755 : Blo 519798 878755 := bstep (se 1 (by rfl) ⟨659066, by rfl⟩ : syracuseStep 878755 = 1318133) B1318133
theorem B780467 : Blo 519798 780467 := bstep (se 1 (by rfl) ⟨585350, by rfl⟩ : syracuseStep 780467 = 1170701) B1170701
theorem B780497 : Blo 519798 780497 := bstep (se 2 (by rfl) ⟨292686, by rfl⟩ : syracuseStep 780497 = 585373) B585373
theorem B780515 : Blo 519798 780515 := bstep (se 1 (by rfl) ⟨585386, by rfl⟩ : syracuseStep 780515 = 1170773) B1170773
theorem B64481507 : Blo 519798 64481507 := bstep (se 1 (by rfl) ⟨48361130, by rfl⟩ : syracuseStep 64481507 = 96722261) B96722261
theorem B780545 : Blo 519798 780545 := bstep (se 2 (by rfl) ⟨292704, by rfl⟩ : syracuseStep 780545 = 585409) B585409
theorem B780563 : Blo 519798 780563 := bstep (se 1 (by rfl) ⟨585422, by rfl⟩ : syracuseStep 780563 = 1170845) B1170845
theorem B780593 : Blo 519798 780593 := bstep (se 2 (by rfl) ⟨292722, by rfl⟩ : syracuseStep 780593 = 585445) B585445
theorem B878897 : Blo 519798 878897 := bstep (se 2 (by rfl) ⟨329586, by rfl⟩ : syracuseStep 878897 = 659173) B659173
theorem B780611 : Blo 519798 780611 := bstep (se 1 (by rfl) ⟨585458, by rfl⟩ : syracuseStep 780611 = 1170917) B1170917
theorem B780641 : Blo 519798 780641 := bstep (se 2 (by rfl) ⟨292740, by rfl⟩ : syracuseStep 780641 = 585481) B585481
theorem B1763693 : Blo 519798 1763693 := bstep (se 3 (by rfl) ⟨330692, by rfl⟩ : syracuseStep 1763693 = 661385) B661385
theorem B780659 : Blo 519798 780659 := bstep (se 1 (by rfl) ⟨585494, by rfl⟩ : syracuseStep 780659 = 1170989) B1170989
theorem B780689 : Blo 519798 780689 := bstep (se 2 (by rfl) ⟨292758, by rfl⟩ : syracuseStep 780689 = 585517) B585517
theorem B1173905 : Blo 519798 1173905 := bstep (se 2 (by rfl) ⟨440214, by rfl⟩ : syracuseStep 1173905 = 880429) B880429
theorem B780707 : Blo 519798 780707 := bstep (se 1 (by rfl) ⟨585530, by rfl⟩ : syracuseStep 780707 = 1171061) B1171061
theorem B1173923 : Blo 519798 1173923 := bstep (se 1 (by rfl) ⟨880442, by rfl⟩ : syracuseStep 1173923 = 1760885) B1760885
theorem B1763747 : Blo 519798 1763747 := bstep (se 1 (by rfl) ⟨1322810, by rfl⟩ : syracuseStep 1763747 = 2645621) B2645621
theorem B879025 : Blo 519798 879025 := bstep (se 2 (by rfl) ⟨329634, by rfl⟩ : syracuseStep 879025 = 659269) B659269
theorem B780737 : Blo 519798 780737 := bstep (se 2 (by rfl) ⟨292776, by rfl⟩ : syracuseStep 780737 = 585553) B585553
theorem B1468867 : Blo 519798 1468867 := bstep (se 1 (by rfl) ⟨1101650, by rfl⟩ : syracuseStep 1468867 = 2203301) B2203301
theorem B780755 : Blo 519798 780755 := bstep (se 1 (by rfl) ⟨585566, by rfl⟩ : syracuseStep 780755 = 1171133) B1171133
theorem B879059 : Blo 519798 879059 := bstep (se 1 (by rfl) ⟨659294, by rfl⟩ : syracuseStep 879059 = 1318589) B1318589
theorem B4450787 : Blo 519798 4450787 := bstep (se 1 (by rfl) ⟨3338090, by rfl⟩ : syracuseStep 4450787 = 6676181) B6676181
theorem B780785 : Blo 519798 780785 := bstep (se 2 (by rfl) ⟨292794, by rfl⟩ : syracuseStep 780785 = 585589) B585589
theorem B4516337 : Blo 519798 4516337 := bstep (se 2 (by rfl) ⟨1693626, by rfl⟩ : syracuseStep 4516337 = 3387253) B3387253
theorem B780803 : Blo 519798 780803 := bstep (se 1 (by rfl) ⟨585602, by rfl⟩ : syracuseStep 780803 = 1171205) B1171205
theorem B780833 : Blo 519798 780833 := bstep (se 2 (by rfl) ⟨292812, by rfl⟩ : syracuseStep 780833 = 585625) B585625
theorem B780851 : Blo 519798 780851 := bstep (se 1 (by rfl) ⟨585638, by rfl⟩ : syracuseStep 780851 = 1171277) B1171277
theorem B780881 : Blo 519798 780881 := bstep (se 2 (by rfl) ⟨292830, by rfl⟩ : syracuseStep 780881 = 585661) B585661
theorem B879187 : Blo 519798 879187 := bstep (se 1 (by rfl) ⟨659390, by rfl⟩ : syracuseStep 879187 = 1318781) B1318781
theorem B780899 : Blo 519798 780899 := bstep (se 1 (by rfl) ⟨585674, by rfl⟩ : syracuseStep 780899 = 1171349) B1171349
theorem B780929 : Blo 519798 780929 := bstep (se 2 (by rfl) ⟨292848, by rfl⟩ : syracuseStep 780929 = 585697) B585697
theorem B780947 : Blo 519798 780947 := bstep (se 1 (by rfl) ⟨585710, by rfl⟩ : syracuseStep 780947 = 1171421) B1171421
theorem B780977 : Blo 519798 780977 := bstep (se 2 (by rfl) ⟨292866, by rfl⟩ : syracuseStep 780977 = 585733) B585733
theorem B1174193 : Blo 519798 1174193 := bstep (se 2 (by rfl) ⟨440322, by rfl⟩ : syracuseStep 1174193 = 880645) B880645
theorem B1764017 : Blo 519798 1764017 := bstep (se 2 (by rfl) ⟨661506, by rfl⟩ : syracuseStep 1764017 = 1323013) B1323013
theorem B780995 : Blo 519798 780995 := bstep (se 1 (by rfl) ⟨585746, by rfl⟩ : syracuseStep 780995 = 1171493) B1171493
theorem B1174211 : Blo 519798 1174211 := bstep (se 1 (by rfl) ⟨880658, by rfl⟩ : syracuseStep 1174211 = 1761317) B1761317
theorem B781025 : Blo 519798 781025 := bstep (se 2 (by rfl) ⟨292884, by rfl⟩ : syracuseStep 781025 = 585769) B585769
theorem B879329 : Blo 519798 879329 := bstep (se 2 (by rfl) ⟨329748, by rfl⟩ : syracuseStep 879329 = 659497) B659497
theorem B781043 : Blo 519798 781043 := bstep (se 1 (by rfl) ⟨585782, by rfl⟩ : syracuseStep 781043 = 1171565) B1171565
theorem B781073 : Blo 519798 781073 := bstep (se 2 (by rfl) ⟨292902, by rfl⟩ : syracuseStep 781073 = 585805) B585805
theorem B781091 : Blo 519798 781091 := bstep (se 1 (by rfl) ⟨585818, by rfl⟩ : syracuseStep 781091 = 1171637) B1171637
theorem B781121 : Blo 519798 781121 := bstep (se 2 (by rfl) ⟨292920, by rfl⟩ : syracuseStep 781121 = 585841) B585841
theorem B3566405 : Blo 519798 3566405 := bstep (se 4 (by rfl) ⟨334350, by rfl⟩ : syracuseStep 3566405 = 668701) B668701
theorem B781139 : Blo 519798 781139 := bstep (se 1 (by rfl) ⟨585854, by rfl⟩ : syracuseStep 781139 = 1171709) B1171709
theorem B879457 : Blo 519798 879457 := bstep (se 2 (by rfl) ⟨329796, by rfl⟩ : syracuseStep 879457 = 659593) B659593
theorem B781169 : Blo 519798 781169 := bstep (se 2 (by rfl) ⟨292938, by rfl⟩ : syracuseStep 781169 = 585877) B585877
theorem B781187 : Blo 519798 781187 := bstep (se 1 (by rfl) ⟨585890, by rfl⟩ : syracuseStep 781187 = 1171781) B1171781
theorem B879491 : Blo 519798 879491 := bstep (se 1 (by rfl) ⟨659618, by rfl⟩ : syracuseStep 879491 = 1319237) B1319237
theorem B781217 : Blo 519798 781217 := bstep (se 2 (by rfl) ⟨292956, by rfl⟩ : syracuseStep 781217 = 585913) B585913
theorem B2976689 : Blo 519798 2976689 := bstep (se 2 (by rfl) ⟨1116258, by rfl⟩ : syracuseStep 2976689 = 2232517) B2232517
theorem B781235 : Blo 519798 781235 := bstep (se 1 (by rfl) ⟨585926, by rfl⟩ : syracuseStep 781235 = 1171853) B1171853
theorem B781265 : Blo 519798 781265 := bstep (se 2 (by rfl) ⟨292974, by rfl⟩ : syracuseStep 781265 = 585949) B585949
theorem B1174481 : Blo 519798 1174481 := bstep (se 2 (by rfl) ⟨440430, by rfl⟩ : syracuseStep 1174481 = 880861) B880861
theorem B781283 : Blo 519798 781283 := bstep (se 1 (by rfl) ⟨585962, by rfl⟩ : syracuseStep 781283 = 1171925) B1171925
theorem B1174499 : Blo 519798 1174499 := bstep (se 1 (by rfl) ⟨880874, by rfl⟩ : syracuseStep 1174499 = 1761749) B1761749
theorem B781313 : Blo 519798 781313 := bstep (se 2 (by rfl) ⟨292992, by rfl⟩ : syracuseStep 781313 = 585985) B585985
theorem B879619 : Blo 519798 879619 := bstep (se 1 (by rfl) ⟨659714, by rfl⟩ : syracuseStep 879619 = 1319429) B1319429
theorem B846865 : Blo 519798 846865 := bstep (se 2 (by rfl) ⟨317574, by rfl⟩ : syracuseStep 846865 = 635149) B635149
theorem B781331 : Blo 519798 781331 := bstep (se 1 (by rfl) ⟨585998, by rfl⟩ : syracuseStep 781331 = 1171997) B1171997
theorem B781361 : Blo 519798 781361 := bstep (se 2 (by rfl) ⟨293010, by rfl⟩ : syracuseStep 781361 = 586021) B586021
theorem B13593653 : Blo 519798 13593653 := bstep (se 5 (by rfl) ⟨637202, by rfl⟩ : syracuseStep 13593653 = 1274405) B1274405
theorem B781379 : Blo 519798 781379 := bstep (se 1 (by rfl) ⟨586034, by rfl⟩ : syracuseStep 781379 = 1172069) B1172069
theorem B781409 : Blo 519798 781409 := bstep (se 2 (by rfl) ⟨293028, by rfl⟩ : syracuseStep 781409 = 586057) B586057
theorem B781427 : Blo 519798 781427 := bstep (se 1 (by rfl) ⟨586070, by rfl⟩ : syracuseStep 781427 = 1172141) B1172141
theorem B781457 : Blo 519798 781457 := bstep (se 2 (by rfl) ⟨293046, by rfl⟩ : syracuseStep 781457 = 586093) B586093
theorem B879761 : Blo 519798 879761 := bstep (se 2 (by rfl) ⟨329910, by rfl⟩ : syracuseStep 879761 = 659821) B659821
theorem B584851 : Blo 519798 584851 := bstep (se 1 (by rfl) ⟨438638, by rfl⟩ : syracuseStep 584851 = 877277) B877277
theorem B781475 : Blo 519798 781475 := bstep (se 1 (by rfl) ⟨586106, by rfl⟩ : syracuseStep 781475 = 1172213) B1172213
theorem B781505 : Blo 519798 781505 := bstep (se 2 (by rfl) ⟨293064, by rfl⟩ : syracuseStep 781505 = 586129) B586129
theorem B1764557 : Blo 519798 1764557 := bstep (se 3 (by rfl) ⟨330854, by rfl⟩ : syracuseStep 1764557 = 661709) B661709
theorem B781523 : Blo 519798 781523 := bstep (se 1 (by rfl) ⟨586142, by rfl⟩ : syracuseStep 781523 = 1172285) B1172285
theorem B1666289 : Blo 519798 1666289 := bstep (se 2 (by rfl) ⟨624858, by rfl⟩ : syracuseStep 1666289 = 1249717) B1249717
theorem B781553 : Blo 519798 781553 := bstep (se 2 (by rfl) ⟨293082, by rfl⟩ : syracuseStep 781553 = 586165) B586165
theorem B1174769 : Blo 519798 1174769 := bstep (se 2 (by rfl) ⟨440538, by rfl⟩ : syracuseStep 1174769 = 881077) B881077
theorem B781571 : Blo 519798 781571 := bstep (se 1 (by rfl) ⟨586178, by rfl⟩ : syracuseStep 781571 = 1172357) B1172357
theorem B1174787 : Blo 519798 1174787 := bstep (se 1 (by rfl) ⟨881090, by rfl⟩ : syracuseStep 1174787 = 1762181) B1762181
theorem B1764611 : Blo 519798 1764611 := bstep (se 1 (by rfl) ⟨1323458, by rfl⟩ : syracuseStep 1764611 = 2646917) B2646917
theorem B879889 : Blo 519798 879889 := bstep (se 2 (by rfl) ⟨329958, by rfl⟩ : syracuseStep 879889 = 659917) B659917
theorem B781601 : Blo 519798 781601 := bstep (se 2 (by rfl) ⟨293100, by rfl⟩ : syracuseStep 781601 = 586201) B586201
theorem B584995 : Blo 519798 584995 := bstep (se 1 (by rfl) ⟨438746, by rfl⟩ : syracuseStep 584995 = 877493) B877493
theorem B2223395 : Blo 519798 2223395 := bstep (se 1 (by rfl) ⟨1667546, by rfl⟩ : syracuseStep 2223395 = 3335093) B3335093
theorem B781619 : Blo 519798 781619 := bstep (se 1 (by rfl) ⟨586214, by rfl⟩ : syracuseStep 781619 = 1172429) B1172429
theorem B879923 : Blo 519798 879923 := bstep (se 1 (by rfl) ⟨659942, by rfl⟩ : syracuseStep 879923 = 1319885) B1319885
theorem B4222277 : Blo 519798 4222277 := bstep (se 4 (by rfl) ⟨395838, by rfl⟩ : syracuseStep 4222277 = 791677) B791677
theorem B5008709 : Blo 519798 5008709 := bstep (se 4 (by rfl) ⟨469566, by rfl⟩ : syracuseStep 5008709 = 939133) B939133
theorem B781649 : Blo 519798 781649 := bstep (se 2 (by rfl) ⟨293118, by rfl⟩ : syracuseStep 781649 = 586237) B586237
theorem B781667 : Blo 519798 781667 := bstep (se 1 (by rfl) ⟨586250, by rfl⟩ : syracuseStep 781667 = 1172501) B1172501
theorem B781697 : Blo 519798 781697 := bstep (se 2 (by rfl) ⟨293136, by rfl⟩ : syracuseStep 781697 = 586273) B586273
theorem B781715 : Blo 519798 781715 := bstep (se 1 (by rfl) ⟨586286, by rfl⟩ : syracuseStep 781715 = 1172573) B1172573
theorem B781745 : Blo 519798 781745 := bstep (se 2 (by rfl) ⟨293154, by rfl⟩ : syracuseStep 781745 = 586309) B586309
theorem B585139 : Blo 519798 585139 := bstep (se 1 (by rfl) ⟨438854, by rfl⟩ : syracuseStep 585139 = 877709) B877709
theorem B880051 : Blo 519798 880051 := bstep (se 1 (by rfl) ⟨660038, by rfl⟩ : syracuseStep 880051 = 1320077) B1320077
theorem B781763 : Blo 519798 781763 := bstep (se 1 (by rfl) ⟨586322, by rfl⟩ : syracuseStep 781763 = 1172645) B1172645
theorem B781793 : Blo 519798 781793 := bstep (se 2 (by rfl) ⟨293172, by rfl⟩ : syracuseStep 781793 = 586345) B586345
theorem B781811 : Blo 519798 781811 := bstep (se 1 (by rfl) ⟨586358, by rfl⟩ : syracuseStep 781811 = 1172717) B1172717
theorem B781841 : Blo 519798 781841 := bstep (se 2 (by rfl) ⟨293190, by rfl⟩ : syracuseStep 781841 = 586381) B586381
theorem B1175057 : Blo 519798 1175057 := bstep (se 2 (by rfl) ⟨440646, by rfl⟩ : syracuseStep 1175057 = 881293) B881293
theorem B1764881 : Blo 519798 1764881 := bstep (se 2 (by rfl) ⟨661830, by rfl⟩ : syracuseStep 1764881 = 1323661) B1323661
theorem B781859 : Blo 519798 781859 := bstep (se 1 (by rfl) ⟨586394, by rfl⟩ : syracuseStep 781859 = 1172789) B1172789
theorem B1175075 : Blo 519798 1175075 := bstep (se 1 (by rfl) ⟨881306, by rfl⟩ : syracuseStep 1175075 = 1762613) B1762613
theorem B781889 : Blo 519798 781889 := bstep (se 2 (by rfl) ⟨293208, by rfl⟩ : syracuseStep 781889 = 586417) B586417
theorem B880193 : Blo 519798 880193 := bstep (se 2 (by rfl) ⟨330072, by rfl⟩ : syracuseStep 880193 = 660145) B660145
theorem B585283 : Blo 519798 585283 := bstep (se 1 (by rfl) ⟨438962, by rfl⟩ : syracuseStep 585283 = 877925) B877925
theorem B781907 : Blo 519798 781907 := bstep (se 1 (by rfl) ⟨586430, by rfl⟩ : syracuseStep 781907 = 1172861) B1172861
theorem B781937 : Blo 519798 781937 := bstep (se 2 (by rfl) ⟨293226, by rfl⟩ : syracuseStep 781937 = 586453) B586453
theorem B519811 : Blo 519798 519811 := bstep (se 1 (by rfl) ⟨389858, by rfl⟩ : syracuseStep 519811 = 779717) B779717
theorem B781955 : Blo 519798 781955 := bstep (se 1 (by rfl) ⟨586466, by rfl⟩ : syracuseStep 781955 = 1172933) B1172933
theorem B519827 : Blo 519798 519827 := bstep (se 1 (by rfl) ⟨389870, by rfl⟩ : syracuseStep 519827 = 779741) B779741
theorem B781985 : Blo 519798 781985 := bstep (se 2 (by rfl) ⟨293244, by rfl⟩ : syracuseStep 781985 = 586489) B586489
theorem B519843 : Blo 519798 519843 := bstep (se 1 (by rfl) ⟨389882, by rfl⟩ : syracuseStep 519843 = 779765) B779765
theorem B519859 : Blo 519798 519859 := bstep (se 1 (by rfl) ⟨389894, by rfl⟩ : syracuseStep 519859 = 779789) B779789
theorem B782003 : Blo 519798 782003 := bstep (se 1 (by rfl) ⟨586502, by rfl⟩ : syracuseStep 782003 = 1173005) B1173005
theorem B880321 : Blo 519798 880321 := bstep (se 2 (by rfl) ⟨330120, by rfl⟩ : syracuseStep 880321 = 660241) B660241
theorem B519875 : Blo 519798 519875 := bstep (se 1 (by rfl) ⟨389906, by rfl⟩ : syracuseStep 519875 = 779813) B779813
theorem B782033 : Blo 519798 782033 := bstep (se 2 (by rfl) ⟨293262, by rfl⟩ : syracuseStep 782033 = 586525) B586525
theorem B585427 : Blo 519798 585427 := bstep (se 1 (by rfl) ⟨439070, by rfl⟩ : syracuseStep 585427 = 878141) B878141
theorem B519891 : Blo 519798 519891 := bstep (se 1 (by rfl) ⟨389918, by rfl⟩ : syracuseStep 519891 = 779837) B779837
theorem B519907 : Blo 519798 519907 := bstep (se 1 (by rfl) ⟨389930, by rfl⟩ : syracuseStep 519907 = 779861) B779861
theorem B782051 : Blo 519798 782051 := bstep (se 1 (by rfl) ⟨586538, by rfl⟩ : syracuseStep 782051 = 1173077) B1173077
theorem B880355 : Blo 519798 880355 := bstep (se 1 (by rfl) ⟨660266, by rfl⟩ : syracuseStep 880355 = 1320533) B1320533
theorem B519923 : Blo 519798 519923 := bstep (se 1 (by rfl) ⟨389942, by rfl⟩ : syracuseStep 519923 = 779885) B779885
theorem B782081 : Blo 519798 782081 := bstep (se 2 (by rfl) ⟨293280, by rfl⟩ : syracuseStep 782081 = 586561) B586561
theorem B519939 : Blo 519798 519939 := bstep (se 1 (by rfl) ⟨389954, by rfl⟩ : syracuseStep 519939 = 779909) B779909
theorem B519955 : Blo 519798 519955 := bstep (se 1 (by rfl) ⟨389966, by rfl⟩ : syracuseStep 519955 = 779933) B779933
theorem B782099 : Blo 519798 782099 := bstep (se 1 (by rfl) ⟨586574, by rfl⟩ : syracuseStep 782099 = 1173149) B1173149
theorem B519971 : Blo 519798 519971 := bstep (se 1 (by rfl) ⟨389978, by rfl⟩ : syracuseStep 519971 = 779957) B779957
theorem B782129 : Blo 519798 782129 := bstep (se 2 (by rfl) ⟨293298, by rfl⟩ : syracuseStep 782129 = 586597) B586597
theorem B1175345 : Blo 519798 1175345 := bstep (se 2 (by rfl) ⟨440754, by rfl⟩ : syracuseStep 1175345 = 881509) B881509
theorem B519987 : Blo 519798 519987 := bstep (se 1 (by rfl) ⟨389990, by rfl⟩ : syracuseStep 519987 = 779981) B779981
theorem B520003 : Blo 519798 520003 := bstep (se 1 (by rfl) ⟨390002, by rfl⟩ : syracuseStep 520003 = 780005) B780005
theorem B782147 : Blo 519798 782147 := bstep (se 1 (by rfl) ⟨586610, by rfl⟩ : syracuseStep 782147 = 1173221) B1173221
theorem B1175363 : Blo 519798 1175363 := bstep (se 1 (by rfl) ⟨881522, by rfl⟩ : syracuseStep 1175363 = 1763045) B1763045
theorem B520019 : Blo 519798 520019 := bstep (se 1 (by rfl) ⟨390014, by rfl⟩ : syracuseStep 520019 = 780029) B780029
theorem B782177 : Blo 519798 782177 := bstep (se 2 (by rfl) ⟨293316, by rfl⟩ : syracuseStep 782177 = 586633) B586633
theorem B520035 : Blo 519798 520035 := bstep (se 1 (by rfl) ⟨390026, by rfl⟩ : syracuseStep 520035 = 780053) B780053
theorem B585571 : Blo 519798 585571 := bstep (se 1 (by rfl) ⟨439178, by rfl⟩ : syracuseStep 585571 = 878357) B878357
theorem B880483 : Blo 519798 880483 := bstep (se 1 (by rfl) ⟨660362, by rfl⟩ : syracuseStep 880483 = 1320725) B1320725
theorem B5926769 : Blo 519798 5926769 := bstep (se 2 (by rfl) ⟨2222538, by rfl⟩ : syracuseStep 5926769 = 4445077) B4445077
theorem B520051 : Blo 519798 520051 := bstep (se 1 (by rfl) ⟨390038, by rfl⟩ : syracuseStep 520051 = 780077) B780077
theorem B782195 : Blo 519798 782195 := bstep (se 1 (by rfl) ⟨586646, by rfl⟩ : syracuseStep 782195 = 1173293) B1173293
theorem B520067 : Blo 519798 520067 := bstep (se 1 (by rfl) ⟨390050, by rfl⟩ : syracuseStep 520067 = 780101) B780101
theorem B782225 : Blo 519798 782225 := bstep (se 2 (by rfl) ⟨293334, by rfl⟩ : syracuseStep 782225 = 586669) B586669
theorem B520083 : Blo 519798 520083 := bstep (se 1 (by rfl) ⟨390062, by rfl⟩ : syracuseStep 520083 = 780125) B780125
theorem B520099 : Blo 519798 520099 := bstep (se 1 (by rfl) ⟨390074, by rfl⟩ : syracuseStep 520099 = 780149) B780149
theorem B782243 : Blo 519798 782243 := bstep (se 1 (by rfl) ⟨586682, by rfl⟩ : syracuseStep 782243 = 1173365) B1173365
theorem B520115 : Blo 519798 520115 := bstep (se 1 (by rfl) ⟨390086, by rfl⟩ : syracuseStep 520115 = 780173) B780173
theorem B782273 : Blo 519798 782273 := bstep (se 2 (by rfl) ⟨293352, by rfl⟩ : syracuseStep 782273 = 586705) B586705
theorem B520131 : Blo 519798 520131 := bstep (se 1 (by rfl) ⟨390098, by rfl⟩ : syracuseStep 520131 = 780197) B780197
theorem B520147 : Blo 519798 520147 := bstep (se 1 (by rfl) ⟨390110, by rfl⟩ : syracuseStep 520147 = 780221) B780221
theorem B782291 : Blo 519798 782291 := bstep (se 1 (by rfl) ⟨586718, by rfl⟩ : syracuseStep 782291 = 1173437) B1173437
theorem B520163 : Blo 519798 520163 := bstep (se 1 (by rfl) ⟨390122, by rfl⟩ : syracuseStep 520163 = 780245) B780245
theorem B782321 : Blo 519798 782321 := bstep (se 2 (by rfl) ⟨293370, by rfl⟩ : syracuseStep 782321 = 586741) B586741
theorem B880625 : Blo 519798 880625 := bstep (se 2 (by rfl) ⟨330234, by rfl⟩ : syracuseStep 880625 = 660469) B660469
theorem B520179 : Blo 519798 520179 := bstep (se 1 (by rfl) ⟨390134, by rfl⟩ : syracuseStep 520179 = 780269) B780269
theorem B585715 : Blo 519798 585715 := bstep (se 1 (by rfl) ⟨439286, by rfl⟩ : syracuseStep 585715 = 878573) B878573
theorem B520195 : Blo 519798 520195 := bstep (se 1 (by rfl) ⟨390146, by rfl⟩ : syracuseStep 520195 = 780293) B780293
theorem B782339 : Blo 519798 782339 := bstep (se 1 (by rfl) ⟨586754, by rfl⟩ : syracuseStep 782339 = 1173509) B1173509
theorem B520211 : Blo 519798 520211 := bstep (se 1 (by rfl) ⟨390158, by rfl⟩ : syracuseStep 520211 = 780317) B780317
theorem B782369 : Blo 519798 782369 := bstep (se 2 (by rfl) ⟨293388, by rfl⟩ : syracuseStep 782369 = 586777) B586777
theorem B716833 : Blo 519798 716833 := bstep (se 2 (by rfl) ⟨268812, by rfl⟩ : syracuseStep 716833 = 537625) B537625
theorem B520227 : Blo 519798 520227 := bstep (se 1 (by rfl) ⟨390170, by rfl⟩ : syracuseStep 520227 = 780341) B780341
theorem B1765421 : Blo 519798 1765421 := bstep (se 3 (by rfl) ⟨331016, by rfl⟩ : syracuseStep 1765421 = 662033) B662033
theorem B520243 : Blo 519798 520243 := bstep (se 1 (by rfl) ⟨390182, by rfl⟩ : syracuseStep 520243 = 780365) B780365
theorem B782387 : Blo 519798 782387 := bstep (se 1 (by rfl) ⟨586790, by rfl⟩ : syracuseStep 782387 = 1173581) B1173581
theorem B520259 : Blo 519798 520259 := bstep (se 1 (by rfl) ⟨390194, by rfl⟩ : syracuseStep 520259 = 780389) B780389
theorem B782417 : Blo 519798 782417 := bstep (se 2 (by rfl) ⟨293406, by rfl⟩ : syracuseStep 782417 = 586813) B586813
theorem B1175633 : Blo 519798 1175633 := bstep (se 2 (by rfl) ⟨440862, by rfl⟩ : syracuseStep 1175633 = 881725) B881725
theorem B520275 : Blo 519798 520275 := bstep (se 1 (by rfl) ⟨390206, by rfl⟩ : syracuseStep 520275 = 780413) B780413
theorem B520291 : Blo 519798 520291 := bstep (se 1 (by rfl) ⟨390218, by rfl⟩ : syracuseStep 520291 = 780437) B780437
theorem B782435 : Blo 519798 782435 := bstep (se 1 (by rfl) ⟨586826, by rfl⟩ : syracuseStep 782435 = 1173653) B1173653
theorem B1175651 : Blo 519798 1175651 := bstep (se 1 (by rfl) ⟨881738, by rfl⟩ : syracuseStep 1175651 = 1763477) B1763477
theorem B1765475 : Blo 519798 1765475 := bstep (se 1 (by rfl) ⟨1324106, by rfl⟩ : syracuseStep 1765475 = 2648213) B2648213
theorem B880753 : Blo 519798 880753 := bstep (se 2 (by rfl) ⟨330282, by rfl⟩ : syracuseStep 880753 = 660565) B660565
theorem B520307 : Blo 519798 520307 := bstep (se 1 (by rfl) ⟨390230, by rfl⟩ : syracuseStep 520307 = 780461) B780461
theorem B782465 : Blo 519798 782465 := bstep (se 2 (by rfl) ⟨293424, by rfl⟩ : syracuseStep 782465 = 586849) B586849
theorem B520323 : Blo 519798 520323 := bstep (se 1 (by rfl) ⟨390242, by rfl⟩ : syracuseStep 520323 = 780485) B780485
theorem B585859 : Blo 519798 585859 := bstep (se 1 (by rfl) ⟨439394, by rfl⟩ : syracuseStep 585859 = 878789) B878789
theorem B1667213 : Blo 519798 1667213 := bstep (se 3 (by rfl) ⟨312602, by rfl⟩ : syracuseStep 1667213 = 625205) B625205
theorem B520339 : Blo 519798 520339 := bstep (se 1 (by rfl) ⟨390254, by rfl⟩ : syracuseStep 520339 = 780509) B780509
theorem B782483 : Blo 519798 782483 := bstep (se 1 (by rfl) ⟨586862, by rfl⟩ : syracuseStep 782483 = 1173725) B1173725
theorem B880787 : Blo 519798 880787 := bstep (se 1 (by rfl) ⟨660590, by rfl⟩ : syracuseStep 880787 = 1321181) B1321181
theorem B520355 : Blo 519798 520355 := bstep (se 1 (by rfl) ⟨390266, by rfl⟩ : syracuseStep 520355 = 780533) B780533
theorem B782513 : Blo 519798 782513 := bstep (se 2 (by rfl) ⟨293442, by rfl⟩ : syracuseStep 782513 = 586885) B586885
theorem B520371 : Blo 519798 520371 := bstep (se 1 (by rfl) ⟨390278, by rfl⟩ : syracuseStep 520371 = 780557) B780557
theorem B520387 : Blo 519798 520387 := bstep (se 1 (by rfl) ⟨390290, by rfl⟩ : syracuseStep 520387 = 780581) B780581
theorem B782531 : Blo 519798 782531 := bstep (se 1 (by rfl) ⟨586898, by rfl⟩ : syracuseStep 782531 = 1173797) B1173797
theorem B520403 : Blo 519798 520403 := bstep (se 1 (by rfl) ⟨390302, by rfl⟩ : syracuseStep 520403 = 780605) B780605
theorem B782561 : Blo 519798 782561 := bstep (se 2 (by rfl) ⟨293460, by rfl⟩ : syracuseStep 782561 = 586921) B586921
theorem B520419 : Blo 519798 520419 := bstep (se 1 (by rfl) ⟨390314, by rfl⟩ : syracuseStep 520419 = 780629) B780629
theorem B1503469 : Blo 519798 1503469 := bstep (se 3 (by rfl) ⟨281900, by rfl⟩ : syracuseStep 1503469 = 563801) B563801
theorem B520435 : Blo 519798 520435 := bstep (se 1 (by rfl) ⟨390326, by rfl⟩ : syracuseStep 520435 = 780653) B780653
theorem B782579 : Blo 519798 782579 := bstep (se 1 (by rfl) ⟨586934, by rfl⟩ : syracuseStep 782579 = 1173869) B1173869
theorem B520451 : Blo 519798 520451 := bstep (se 1 (by rfl) ⟨390338, by rfl⟩ : syracuseStep 520451 = 780677) B780677
theorem B782609 : Blo 519798 782609 := bstep (se 2 (by rfl) ⟨293478, by rfl⟩ : syracuseStep 782609 = 586957) B586957
theorem B520467 : Blo 519798 520467 := bstep (se 1 (by rfl) ⟨390350, by rfl⟩ : syracuseStep 520467 = 780701) B780701
theorem B586003 : Blo 519798 586003 := bstep (se 1 (by rfl) ⟨439502, by rfl⟩ : syracuseStep 586003 = 879005) B879005
theorem B880915 : Blo 519798 880915 := bstep (se 1 (by rfl) ⟨660686, by rfl⟩ : syracuseStep 880915 = 1321373) B1321373
theorem B520483 : Blo 519798 520483 := bstep (se 1 (by rfl) ⟨390362, by rfl⟩ : syracuseStep 520483 = 780725) B780725
theorem B782627 : Blo 519798 782627 := bstep (se 1 (by rfl) ⟨586970, by rfl⟩ : syracuseStep 782627 = 1173941) B1173941
theorem B520499 : Blo 519798 520499 := bstep (se 1 (by rfl) ⟨390374, by rfl⟩ : syracuseStep 520499 = 780749) B780749
theorem B782657 : Blo 519798 782657 := bstep (se 2 (by rfl) ⟨293496, by rfl⟩ : syracuseStep 782657 = 586993) B586993
theorem B520515 : Blo 519798 520515 := bstep (se 1 (by rfl) ⟨390386, by rfl⟩ : syracuseStep 520515 = 780773) B780773
theorem B1667405 : Blo 519798 1667405 := bstep (se 3 (by rfl) ⟨312638, by rfl⟩ : syracuseStep 1667405 = 625277) B625277
theorem B520531 : Blo 519798 520531 := bstep (se 1 (by rfl) ⟨390398, by rfl⟩ : syracuseStep 520531 = 780797) B780797
theorem B782675 : Blo 519798 782675 := bstep (se 1 (by rfl) ⟨587006, by rfl⟩ : syracuseStep 782675 = 1174013) B1174013
theorem B520547 : Blo 519798 520547 := bstep (se 1 (by rfl) ⟨390410, by rfl⟩ : syracuseStep 520547 = 780821) B780821
theorem B2978147 : Blo 519798 2978147 := bstep (se 1 (by rfl) ⟨2233610, by rfl⟩ : syracuseStep 2978147 = 4467221) B4467221
theorem B782705 : Blo 519798 782705 := bstep (se 2 (by rfl) ⟨293514, by rfl⟩ : syracuseStep 782705 = 587029) B587029
theorem B1175921 : Blo 519798 1175921 := bstep (se 2 (by rfl) ⟨440970, by rfl⟩ : syracuseStep 1175921 = 881941) B881941
theorem B520563 : Blo 519798 520563 := bstep (se 1 (by rfl) ⟨390422, by rfl⟩ : syracuseStep 520563 = 780845) B780845
theorem B1765745 : Blo 519798 1765745 := bstep (se 2 (by rfl) ⟨662154, by rfl⟩ : syracuseStep 1765745 = 1324309) B1324309
theorem B2650481 : Blo 519798 2650481 := bstep (se 2 (by rfl) ⟨993930, by rfl⟩ : syracuseStep 2650481 = 1987861) B1987861
theorem B520579 : Blo 519798 520579 := bstep (se 1 (by rfl) ⟨390434, by rfl⟩ : syracuseStep 520579 = 780869) B780869
theorem B782723 : Blo 519798 782723 := bstep (se 1 (by rfl) ⟨587042, by rfl⟩ : syracuseStep 782723 = 1174085) B1174085
theorem B1175939 : Blo 519798 1175939 := bstep (se 1 (by rfl) ⟨881954, by rfl⟩ : syracuseStep 1175939 = 1763909) B1763909
theorem B520595 : Blo 519798 520595 := bstep (se 1 (by rfl) ⟨390446, by rfl⟩ : syracuseStep 520595 = 780893) B780893
theorem B782753 : Blo 519798 782753 := bstep (se 2 (by rfl) ⟨293532, by rfl⟩ : syracuseStep 782753 = 587065) B587065
theorem B881057 : Blo 519798 881057 := bstep (se 2 (by rfl) ⟨330396, by rfl⟩ : syracuseStep 881057 = 660793) B660793
theorem B520611 : Blo 519798 520611 := bstep (se 1 (by rfl) ⟨390458, by rfl⟩ : syracuseStep 520611 = 780917) B780917
theorem B586147 : Blo 519798 586147 := bstep (se 1 (by rfl) ⟨439610, by rfl⟩ : syracuseStep 586147 = 879221) B879221
theorem B1929635 : Blo 519798 1929635 := bstep (se 1 (by rfl) ⟨1447226, by rfl⟩ : syracuseStep 1929635 = 2894453) B2894453
theorem B520627 : Blo 519798 520627 := bstep (se 1 (by rfl) ⟨390470, by rfl⟩ : syracuseStep 520627 = 780941) B780941
theorem B782771 : Blo 519798 782771 := bstep (se 1 (by rfl) ⟨587078, by rfl⟩ : syracuseStep 782771 = 1174157) B1174157
theorem B520643 : Blo 519798 520643 := bstep (se 1 (by rfl) ⟨390482, by rfl⟩ : syracuseStep 520643 = 780965) B780965
theorem B782801 : Blo 519798 782801 := bstep (se 2 (by rfl) ⟨293550, by rfl⟩ : syracuseStep 782801 = 587101) B587101
theorem B520659 : Blo 519798 520659 := bstep (se 1 (by rfl) ⟨390494, by rfl⟩ : syracuseStep 520659 = 780989) B780989
theorem B520675 : Blo 519798 520675 := bstep (se 1 (by rfl) ⟨390506, by rfl⟩ : syracuseStep 520675 = 781013) B781013
theorem B782819 : Blo 519798 782819 := bstep (se 1 (by rfl) ⟨587114, by rfl⟩ : syracuseStep 782819 = 1174229) B1174229
theorem B7139825 : Blo 519798 7139825 := bstep (se 2 (by rfl) ⟨2677434, by rfl⟩ : syracuseStep 7139825 = 5354869) B5354869
theorem B520691 : Blo 519798 520691 := bstep (se 1 (by rfl) ⟨390518, by rfl⟩ : syracuseStep 520691 = 781037) B781037
theorem B782849 : Blo 519798 782849 := bstep (se 2 (by rfl) ⟨293568, by rfl⟩ : syracuseStep 782849 = 587137) B587137
theorem B520707 : Blo 519798 520707 := bstep (se 1 (by rfl) ⟨390530, by rfl⟩ : syracuseStep 520707 = 781061) B781061
theorem B520723 : Blo 519798 520723 := bstep (se 1 (by rfl) ⟨390542, by rfl⟩ : syracuseStep 520723 = 781085) B781085
theorem B782867 : Blo 519798 782867 := bstep (se 1 (by rfl) ⟨587150, by rfl⟩ : syracuseStep 782867 = 1174301) B1174301
theorem B881185 : Blo 519798 881185 := bstep (se 2 (by rfl) ⟨330444, by rfl⟩ : syracuseStep 881185 = 660889) B660889
theorem B520739 : Blo 519798 520739 := bstep (se 1 (by rfl) ⟨390554, by rfl⟩ : syracuseStep 520739 = 781109) B781109
theorem B782897 : Blo 519798 782897 := bstep (se 2 (by rfl) ⟨293586, by rfl⟩ : syracuseStep 782897 = 587173) B587173
theorem B520755 : Blo 519798 520755 := bstep (se 1 (by rfl) ⟨390566, by rfl⟩ : syracuseStep 520755 = 781133) B781133
theorem B586291 : Blo 519798 586291 := bstep (se 1 (by rfl) ⟨439718, by rfl⟩ : syracuseStep 586291 = 879437) B879437
theorem B520771 : Blo 519798 520771 := bstep (se 1 (by rfl) ⟨390578, by rfl⟩ : syracuseStep 520771 = 781157) B781157
theorem B782915 : Blo 519798 782915 := bstep (se 1 (by rfl) ⟨587186, by rfl⟩ : syracuseStep 782915 = 1174373) B1174373
theorem B881219 : Blo 519798 881219 := bstep (se 1 (by rfl) ⟨660914, by rfl⟩ : syracuseStep 881219 = 1321829) B1321829
theorem B520787 : Blo 519798 520787 := bstep (se 1 (by rfl) ⟨390590, by rfl⟩ : syracuseStep 520787 = 781181) B781181
theorem B782945 : Blo 519798 782945 := bstep (se 2 (by rfl) ⟨293604, by rfl⟩ : syracuseStep 782945 = 587209) B587209
theorem B520803 : Blo 519798 520803 := bstep (se 1 (by rfl) ⟨390602, by rfl⟩ : syracuseStep 520803 = 781205) B781205
theorem B520819 : Blo 519798 520819 := bstep (se 1 (by rfl) ⟨390614, by rfl⟩ : syracuseStep 520819 = 781229) B781229
theorem B782963 : Blo 519798 782963 := bstep (se 1 (by rfl) ⟨587222, by rfl⟩ : syracuseStep 782963 = 1174445) B1174445
theorem B520835 : Blo 519798 520835 := bstep (se 1 (by rfl) ⟨390626, by rfl⟩ : syracuseStep 520835 = 781253) B781253
theorem B782993 : Blo 519798 782993 := bstep (se 2 (by rfl) ⟨293622, by rfl⟩ : syracuseStep 782993 = 587245) B587245
theorem B1176209 : Blo 519798 1176209 := bstep (se 2 (by rfl) ⟨441078, by rfl⟩ : syracuseStep 1176209 = 882157) B882157
theorem B520851 : Blo 519798 520851 := bstep (se 1 (by rfl) ⟨390638, by rfl⟩ : syracuseStep 520851 = 781277) B781277
theorem B1176227 : Blo 519798 1176227 := bstep (se 1 (by rfl) ⟨882170, by rfl⟩ : syracuseStep 1176227 = 1764341) B1764341
theorem B520867 : Blo 519798 520867 := bstep (se 1 (by rfl) ⟨390650, by rfl⟩ : syracuseStep 520867 = 781301) B781301
theorem B783011 : Blo 519798 783011 := bstep (se 1 (by rfl) ⟨587258, by rfl⟩ : syracuseStep 783011 = 1174517) B1174517
theorem B520883 : Blo 519798 520883 := bstep (se 1 (by rfl) ⟨390662, by rfl⟩ : syracuseStep 520883 = 781325) B781325
theorem B783041 : Blo 519798 783041 := bstep (se 2 (by rfl) ⟨293640, by rfl⟩ : syracuseStep 783041 = 587281) B587281
theorem B520899 : Blo 519798 520899 := bstep (se 1 (by rfl) ⟨390674, by rfl⟩ : syracuseStep 520899 = 781349) B781349
theorem B586435 : Blo 519798 586435 := bstep (se 1 (by rfl) ⟨439826, by rfl⟩ : syracuseStep 586435 = 879653) B879653
theorem B881347 : Blo 519798 881347 := bstep (se 1 (by rfl) ⟨661010, by rfl⟩ : syracuseStep 881347 = 1322021) B1322021
theorem B520915 : Blo 519798 520915 := bstep (se 1 (by rfl) ⟨390686, by rfl⟩ : syracuseStep 520915 = 781373) B781373
theorem B783059 : Blo 519798 783059 := bstep (se 1 (by rfl) ⟨587294, by rfl⟩ : syracuseStep 783059 = 1174589) B1174589
theorem B520931 : Blo 519798 520931 := bstep (se 1 (by rfl) ⟨390698, by rfl⟩ : syracuseStep 520931 = 781397) B781397
theorem B783089 : Blo 519798 783089 := bstep (se 2 (by rfl) ⟨293658, by rfl⟩ : syracuseStep 783089 = 587317) B587317
theorem B520947 : Blo 519798 520947 := bstep (se 1 (by rfl) ⟨390710, by rfl⟩ : syracuseStep 520947 = 781421) B781421
theorem B520963 : Blo 519798 520963 := bstep (se 1 (by rfl) ⟨390722, by rfl⟩ : syracuseStep 520963 = 781445) B781445
theorem B783107 : Blo 519798 783107 := bstep (se 1 (by rfl) ⟨587330, by rfl⟩ : syracuseStep 783107 = 1174661) B1174661
theorem B520979 : Blo 519798 520979 := bstep (se 1 (by rfl) ⟨390734, by rfl⟩ : syracuseStep 520979 = 781469) B781469
theorem B783137 : Blo 519798 783137 := bstep (se 2 (by rfl) ⟨293676, by rfl⟩ : syracuseStep 783137 = 587353) B587353
theorem B520995 : Blo 519798 520995 := bstep (se 1 (by rfl) ⟨390746, by rfl⟩ : syracuseStep 520995 = 781493) B781493
theorem B521011 : Blo 519798 521011 := bstep (se 1 (by rfl) ⟨390758, by rfl⟩ : syracuseStep 521011 = 781517) B781517
theorem B783155 : Blo 519798 783155 := bstep (se 1 (by rfl) ⟨587366, by rfl⟩ : syracuseStep 783155 = 1174733) B1174733
theorem B521027 : Blo 519798 521027 := bstep (se 1 (by rfl) ⟨390770, by rfl⟩ : syracuseStep 521027 = 781541) B781541
theorem B783185 : Blo 519798 783185 := bstep (se 2 (by rfl) ⟨293694, by rfl⟩ : syracuseStep 783185 = 587389) B587389
theorem B881489 : Blo 519798 881489 := bstep (se 2 (by rfl) ⟨330558, by rfl⟩ : syracuseStep 881489 = 661117) B661117
theorem B521043 : Blo 519798 521043 := bstep (se 1 (by rfl) ⟨390782, by rfl⟩ : syracuseStep 521043 = 781565) B781565
theorem B586579 : Blo 519798 586579 := bstep (se 1 (by rfl) ⟨439934, by rfl⟩ : syracuseStep 586579 = 879869) B879869
theorem B521059 : Blo 519798 521059 := bstep (se 1 (by rfl) ⟨390794, by rfl⟩ : syracuseStep 521059 = 781589) B781589
theorem B783203 : Blo 519798 783203 := bstep (se 1 (by rfl) ⟨587402, by rfl⟩ : syracuseStep 783203 = 1174805) B1174805
theorem B521075 : Blo 519798 521075 := bstep (se 1 (by rfl) ⟨390806, by rfl⟩ : syracuseStep 521075 = 781613) B781613
theorem B783233 : Blo 519798 783233 := bstep (se 2 (by rfl) ⟨293712, by rfl⟩ : syracuseStep 783233 = 587425) B587425
theorem B521091 : Blo 519798 521091 := bstep (se 1 (by rfl) ⟨390818, by rfl⟩ : syracuseStep 521091 = 781637) B781637
theorem B1766285 : Blo 519798 1766285 := bstep (se 3 (by rfl) ⟨331178, by rfl⟩ : syracuseStep 1766285 = 662357) B662357
theorem B521107 : Blo 519798 521107 := bstep (se 1 (by rfl) ⟨390830, by rfl⟩ : syracuseStep 521107 = 781661) B781661
theorem B783251 : Blo 519798 783251 := bstep (se 1 (by rfl) ⟨587438, by rfl⟩ : syracuseStep 783251 = 1174877) B1174877
theorem B521123 : Blo 519798 521123 := bstep (se 1 (by rfl) ⟨390842, by rfl⟩ : syracuseStep 521123 = 781685) B781685
theorem B783281 : Blo 519798 783281 := bstep (se 2 (by rfl) ⟨293730, by rfl⟩ : syracuseStep 783281 = 587461) B587461
theorem B1176497 : Blo 519798 1176497 := bstep (se 2 (by rfl) ⟨441186, by rfl⟩ : syracuseStep 1176497 = 882373) B882373
theorem B521139 : Blo 519798 521139 := bstep (se 1 (by rfl) ⟨390854, by rfl⟩ : syracuseStep 521139 = 781709) B781709
theorem B521155 : Blo 519798 521155 := bstep (se 1 (by rfl) ⟨390866, by rfl⟩ : syracuseStep 521155 = 781733) B781733
theorem B783299 : Blo 519798 783299 := bstep (se 1 (by rfl) ⟨587474, by rfl⟩ : syracuseStep 783299 = 1174949) B1174949
theorem B1176515 : Blo 519798 1176515 := bstep (se 1 (by rfl) ⟨882386, by rfl⟩ : syracuseStep 1176515 = 1764773) B1764773
theorem B1766339 : Blo 519798 1766339 := bstep (se 1 (by rfl) ⟨1324754, by rfl⟩ : syracuseStep 1766339 = 2649509) B2649509
theorem B881617 : Blo 519798 881617 := bstep (se 2 (by rfl) ⟨330606, by rfl⟩ : syracuseStep 881617 = 661213) B661213
theorem B521171 : Blo 519798 521171 := bstep (se 1 (by rfl) ⟨390878, by rfl⟩ : syracuseStep 521171 = 781757) B781757
theorem B783329 : Blo 519798 783329 := bstep (se 2 (by rfl) ⟨293748, by rfl⟩ : syracuseStep 783329 = 587497) B587497
theorem B521187 : Blo 519798 521187 := bstep (se 1 (by rfl) ⟨390890, by rfl⟩ : syracuseStep 521187 = 781781) B781781
theorem B586723 : Blo 519798 586723 := bstep (se 1 (by rfl) ⟨440042, by rfl⟩ : syracuseStep 586723 = 880085) B880085
theorem B521203 : Blo 519798 521203 := bstep (se 1 (by rfl) ⟨390902, by rfl⟩ : syracuseStep 521203 = 781805) B781805
theorem B783347 : Blo 519798 783347 := bstep (se 1 (by rfl) ⟨587510, by rfl⟩ : syracuseStep 783347 = 1175021) B1175021
theorem B881651 : Blo 519798 881651 := bstep (se 1 (by rfl) ⟨661238, by rfl⟩ : syracuseStep 881651 = 1322477) B1322477
theorem B521219 : Blo 519798 521219 := bstep (se 1 (by rfl) ⟨390914, by rfl⟩ : syracuseStep 521219 = 781829) B781829
theorem B783377 : Blo 519798 783377 := bstep (se 2 (by rfl) ⟨293766, by rfl⟩ : syracuseStep 783377 = 587533) B587533
theorem B521235 : Blo 519798 521235 := bstep (se 1 (by rfl) ⟨390926, by rfl⟩ : syracuseStep 521235 = 781853) B781853
theorem B521251 : Blo 519798 521251 := bstep (se 1 (by rfl) ⟨390938, by rfl⟩ : syracuseStep 521251 = 781877) B781877
theorem B783395 : Blo 519798 783395 := bstep (se 1 (by rfl) ⟨587546, by rfl⟩ : syracuseStep 783395 = 1175093) B1175093
theorem B521267 : Blo 519798 521267 := bstep (se 1 (by rfl) ⟨390950, by rfl⟩ : syracuseStep 521267 = 781901) B781901
theorem B783425 : Blo 519798 783425 := bstep (se 2 (by rfl) ⟨293784, by rfl⟩ : syracuseStep 783425 = 587569) B587569
theorem B521283 : Blo 519798 521283 := bstep (se 1 (by rfl) ⟨390962, by rfl⟩ : syracuseStep 521283 = 781925) B781925
theorem B521299 : Blo 519798 521299 := bstep (se 1 (by rfl) ⟨390974, by rfl⟩ : syracuseStep 521299 = 781949) B781949
theorem B783443 : Blo 519798 783443 := bstep (se 1 (by rfl) ⟨587582, by rfl⟩ : syracuseStep 783443 = 1175165) B1175165
theorem B521315 : Blo 519798 521315 := bstep (se 1 (by rfl) ⟨390986, by rfl⟩ : syracuseStep 521315 = 781973) B781973
theorem B2290801 : Blo 519798 2290801 := bstep (se 2 (by rfl) ⟨859050, by rfl⟩ : syracuseStep 2290801 = 1718101) B1718101
theorem B783473 : Blo 519798 783473 := bstep (se 2 (by rfl) ⟨293802, by rfl⟩ : syracuseStep 783473 = 587605) B587605
theorem B521331 : Blo 519798 521331 := bstep (se 1 (by rfl) ⟨390998, by rfl⟩ : syracuseStep 521331 = 781997) B781997
theorem B586867 : Blo 519798 586867 := bstep (se 1 (by rfl) ⟨440150, by rfl⟩ : syracuseStep 586867 = 880301) B880301
theorem B881779 : Blo 519798 881779 := bstep (se 1 (by rfl) ⟨661334, by rfl⟩ : syracuseStep 881779 = 1322669) B1322669
theorem B521347 : Blo 519798 521347 := bstep (se 1 (by rfl) ⟨391010, by rfl⟩ : syracuseStep 521347 = 782021) B782021
theorem B783491 : Blo 519798 783491 := bstep (se 1 (by rfl) ⟨587618, by rfl⟩ : syracuseStep 783491 = 1175237) B1175237
theorem B521363 : Blo 519798 521363 := bstep (se 1 (by rfl) ⟨391022, by rfl⟩ : syracuseStep 521363 = 782045) B782045
theorem B783521 : Blo 519798 783521 := bstep (se 2 (by rfl) ⟨293820, by rfl⟩ : syracuseStep 783521 = 587641) B587641
theorem B521379 : Blo 519798 521379 := bstep (se 1 (by rfl) ⟨391034, by rfl⟩ : syracuseStep 521379 = 782069) B782069
theorem B521395 : Blo 519798 521395 := bstep (se 1 (by rfl) ⟨391046, by rfl⟩ : syracuseStep 521395 = 782093) B782093
theorem B783539 : Blo 519798 783539 := bstep (se 1 (by rfl) ⟨587654, by rfl⟩ : syracuseStep 783539 = 1175309) B1175309
theorem B521411 : Blo 519798 521411 := bstep (se 1 (by rfl) ⟨391058, by rfl⟩ : syracuseStep 521411 = 782117) B782117
theorem B783569 : Blo 519798 783569 := bstep (se 2 (by rfl) ⟨293838, by rfl⟩ : syracuseStep 783569 = 587677) B587677
theorem B1176785 : Blo 519798 1176785 := bstep (se 2 (by rfl) ⟨441294, by rfl⟩ : syracuseStep 1176785 = 882589) B882589
theorem B521427 : Blo 519798 521427 := bstep (se 1 (by rfl) ⟨391070, by rfl⟩ : syracuseStep 521427 = 782141) B782141
theorem B1766609 : Blo 519798 1766609 := bstep (se 2 (by rfl) ⟨662478, by rfl⟩ : syracuseStep 1766609 = 1324957) B1324957
theorem B521443 : Blo 519798 521443 := bstep (se 1 (by rfl) ⟨391082, by rfl⟩ : syracuseStep 521443 = 782165) B782165
theorem B783587 : Blo 519798 783587 := bstep (se 1 (by rfl) ⟨587690, by rfl⟩ : syracuseStep 783587 = 1175381) B1175381
theorem B1176803 : Blo 519798 1176803 := bstep (se 1 (by rfl) ⟨882602, by rfl⟩ : syracuseStep 1176803 = 1765205) B1765205
theorem B521459 : Blo 519798 521459 := bstep (se 1 (by rfl) ⟨391094, by rfl⟩ : syracuseStep 521459 = 782189) B782189
theorem B783617 : Blo 519798 783617 := bstep (se 2 (by rfl) ⟨293856, by rfl⟩ : syracuseStep 783617 = 587713) B587713
theorem B881921 : Blo 519798 881921 := bstep (se 2 (by rfl) ⟨330720, by rfl⟩ : syracuseStep 881921 = 661441) B661441
theorem B521475 : Blo 519798 521475 := bstep (se 1 (by rfl) ⟨391106, by rfl⟩ : syracuseStep 521475 = 782213) B782213
theorem B587011 : Blo 519798 587011 := bstep (se 1 (by rfl) ⟨440258, by rfl⟩ : syracuseStep 587011 = 880517) B880517
theorem B521491 : Blo 519798 521491 := bstep (se 1 (by rfl) ⟨391118, by rfl⟩ : syracuseStep 521491 = 782237) B782237
theorem B783635 : Blo 519798 783635 := bstep (se 1 (by rfl) ⟨587726, by rfl⟩ : syracuseStep 783635 = 1175453) B1175453
theorem B521507 : Blo 519798 521507 := bstep (se 1 (by rfl) ⟨391130, by rfl⟩ : syracuseStep 521507 = 782261) B782261
theorem B783665 : Blo 519798 783665 := bstep (se 2 (by rfl) ⟨293874, by rfl⟩ : syracuseStep 783665 = 587749) B587749
theorem B521523 : Blo 519798 521523 := bstep (se 1 (by rfl) ⟨391142, by rfl⟩ : syracuseStep 521523 = 782285) B782285
theorem B521539 : Blo 519798 521539 := bstep (se 1 (by rfl) ⟨391154, by rfl⟩ : syracuseStep 521539 = 782309) B782309
theorem B783683 : Blo 519798 783683 := bstep (se 1 (by rfl) ⟨587762, by rfl⟩ : syracuseStep 783683 = 1175525) B1175525
theorem B521555 : Blo 519798 521555 := bstep (se 1 (by rfl) ⟨391166, by rfl⟩ : syracuseStep 521555 = 782333) B782333
theorem B783713 : Blo 519798 783713 := bstep (se 2 (by rfl) ⟨293892, by rfl⟩ : syracuseStep 783713 = 587785) B587785
theorem B521571 : Blo 519798 521571 := bstep (se 1 (by rfl) ⟨391178, by rfl⟩ : syracuseStep 521571 = 782357) B782357
theorem B521587 : Blo 519798 521587 := bstep (se 1 (by rfl) ⟨391190, by rfl⟩ : syracuseStep 521587 = 782381) B782381
theorem B783731 : Blo 519798 783731 := bstep (se 1 (by rfl) ⟨587798, by rfl⟩ : syracuseStep 783731 = 1175597) B1175597
theorem B882049 : Blo 519798 882049 := bstep (se 2 (by rfl) ⟨330768, by rfl⟩ : syracuseStep 882049 = 661537) B661537
theorem B521603 : Blo 519798 521603 := bstep (se 1 (by rfl) ⟨391202, by rfl⟩ : syracuseStep 521603 = 782405) B782405
theorem B1111441 : Blo 519798 1111441 := bstep (se 2 (by rfl) ⟨416790, by rfl⟩ : syracuseStep 1111441 = 833581) B833581
theorem B783761 : Blo 519798 783761 := bstep (se 2 (by rfl) ⟨293910, by rfl⟩ : syracuseStep 783761 = 587821) B587821
theorem B521619 : Blo 519798 521619 := bstep (se 1 (by rfl) ⟨391214, by rfl⟩ : syracuseStep 521619 = 782429) B782429
theorem B587155 : Blo 519798 587155 := bstep (se 1 (by rfl) ⟨440366, by rfl⟩ : syracuseStep 587155 = 880733) B880733
theorem B521635 : Blo 519798 521635 := bstep (se 1 (by rfl) ⟨391226, by rfl⟩ : syracuseStep 521635 = 782453) B782453
theorem B783779 : Blo 519798 783779 := bstep (se 1 (by rfl) ⟨587834, by rfl⟩ : syracuseStep 783779 = 1175669) B1175669
theorem B882083 : Blo 519798 882083 := bstep (se 1 (by rfl) ⟨661562, by rfl⟩ : syracuseStep 882083 = 1323125) B1323125
theorem B521651 : Blo 519798 521651 := bstep (se 1 (by rfl) ⟨391238, by rfl⟩ : syracuseStep 521651 = 782477) B782477
theorem B783809 : Blo 519798 783809 := bstep (se 2 (by rfl) ⟨293928, by rfl⟩ : syracuseStep 783809 = 587857) B587857
theorem B521667 : Blo 519798 521667 := bstep (se 1 (by rfl) ⟨391250, by rfl⟩ : syracuseStep 521667 = 782501) B782501
theorem B521683 : Blo 519798 521683 := bstep (se 1 (by rfl) ⟨391262, by rfl⟩ : syracuseStep 521683 = 782525) B782525
theorem B783827 : Blo 519798 783827 := bstep (se 1 (by rfl) ⟨587870, by rfl⟩ : syracuseStep 783827 = 1175741) B1175741
theorem B521699 : Blo 519798 521699 := bstep (se 1 (by rfl) ⟨391274, by rfl⟩ : syracuseStep 521699 = 782549) B782549
theorem B783857 : Blo 519798 783857 := bstep (se 2 (by rfl) ⟨293946, by rfl⟩ : syracuseStep 783857 = 587893) B587893
theorem B1177073 : Blo 519798 1177073 := bstep (se 2 (by rfl) ⟨441402, by rfl⟩ : syracuseStep 1177073 = 882805) B882805
theorem B521715 : Blo 519798 521715 := bstep (se 1 (by rfl) ⟨391286, by rfl⟩ : syracuseStep 521715 = 782573) B782573
theorem B521731 : Blo 519798 521731 := bstep (se 1 (by rfl) ⟨391298, by rfl⟩ : syracuseStep 521731 = 782597) B782597
theorem B783875 : Blo 519798 783875 := bstep (se 1 (by rfl) ⟨587906, by rfl⟩ : syracuseStep 783875 = 1175813) B1175813
theorem B1177091 : Blo 519798 1177091 := bstep (se 1 (by rfl) ⟨882818, by rfl⟩ : syracuseStep 1177091 = 1765637) B1765637
theorem B521747 : Blo 519798 521747 := bstep (se 1 (by rfl) ⟨391310, by rfl⟩ : syracuseStep 521747 = 782621) B782621
theorem B783905 : Blo 519798 783905 := bstep (se 2 (by rfl) ⟨293964, by rfl⟩ : syracuseStep 783905 = 587929) B587929
theorem B521763 : Blo 519798 521763 := bstep (se 1 (by rfl) ⟨391322, by rfl⟩ : syracuseStep 521763 = 782645) B782645
theorem B587299 : Blo 519798 587299 := bstep (se 1 (by rfl) ⟨440474, by rfl⟩ : syracuseStep 587299 = 880949) B880949
theorem B882211 : Blo 519798 882211 := bstep (se 1 (by rfl) ⟨661658, by rfl⟩ : syracuseStep 882211 = 1323317) B1323317
theorem B521779 : Blo 519798 521779 := bstep (se 1 (by rfl) ⟨391334, by rfl⟩ : syracuseStep 521779 = 782669) B782669
theorem B783923 : Blo 519798 783923 := bstep (se 1 (by rfl) ⟨587942, by rfl⟩ : syracuseStep 783923 = 1175885) B1175885
theorem B521795 : Blo 519798 521795 := bstep (se 1 (by rfl) ⟨391346, by rfl⟩ : syracuseStep 521795 = 782693) B782693
theorem B783953 : Blo 519798 783953 := bstep (se 2 (by rfl) ⟨293982, by rfl⟩ : syracuseStep 783953 = 587965) B587965
theorem B521811 : Blo 519798 521811 := bstep (se 1 (by rfl) ⟨391358, by rfl⟩ : syracuseStep 521811 = 782717) B782717
theorem B521827 : Blo 519798 521827 := bstep (se 1 (by rfl) ⟨391370, by rfl⟩ : syracuseStep 521827 = 782741) B782741
theorem B783971 : Blo 519798 783971 := bstep (se 1 (by rfl) ⟨587978, by rfl⟩ : syracuseStep 783971 = 1175957) B1175957
theorem B521843 : Blo 519798 521843 := bstep (se 1 (by rfl) ⟨391382, by rfl⟩ : syracuseStep 521843 = 782765) B782765
theorem B784001 : Blo 519798 784001 := bstep (se 2 (by rfl) ⟨294000, by rfl⟩ : syracuseStep 784001 = 588001) B588001
theorem B521859 : Blo 519798 521859 := bstep (se 1 (by rfl) ⟨391394, by rfl⟩ : syracuseStep 521859 = 782789) B782789
theorem B521875 : Blo 519798 521875 := bstep (se 1 (by rfl) ⟨391406, by rfl⟩ : syracuseStep 521875 = 782813) B782813
theorem B784019 : Blo 519798 784019 := bstep (se 1 (by rfl) ⟨588014, by rfl⟩ : syracuseStep 784019 = 1176029) B1176029
theorem B521891 : Blo 519798 521891 := bstep (se 1 (by rfl) ⟨391418, by rfl⟩ : syracuseStep 521891 = 782837) B782837
theorem B784049 : Blo 519798 784049 := bstep (se 2 (by rfl) ⟨294018, by rfl⟩ : syracuseStep 784049 = 588037) B588037
theorem B882353 : Blo 519798 882353 := bstep (se 2 (by rfl) ⟨330882, by rfl⟩ : syracuseStep 882353 = 661765) B661765
theorem B521907 : Blo 519798 521907 := bstep (se 1 (by rfl) ⟨391430, by rfl⟩ : syracuseStep 521907 = 782861) B782861
theorem B587443 : Blo 519798 587443 := bstep (se 1 (by rfl) ⟨440582, by rfl⟩ : syracuseStep 587443 = 881165) B881165
theorem B5732021 : Blo 519798 5732021 := bstep (se 5 (by rfl) ⟨268688, by rfl⟩ : syracuseStep 5732021 = 537377) B537377
theorem B521923 : Blo 519798 521923 := bstep (se 1 (by rfl) ⟨391442, by rfl⟩ : syracuseStep 521923 = 782885) B782885
theorem B784067 : Blo 519798 784067 := bstep (se 1 (by rfl) ⟨588050, by rfl⟩ : syracuseStep 784067 = 1176101) B1176101
theorem B521939 : Blo 519798 521939 := bstep (se 1 (by rfl) ⟨391454, by rfl⟩ : syracuseStep 521939 = 782909) B782909
theorem B784097 : Blo 519798 784097 := bstep (se 2 (by rfl) ⟨294036, by rfl⟩ : syracuseStep 784097 = 588073) B588073
theorem B521955 : Blo 519798 521955 := bstep (se 1 (by rfl) ⟨391466, by rfl⟩ : syracuseStep 521955 = 782933) B782933
theorem B1767149 : Blo 519798 1767149 := bstep (se 3 (by rfl) ⟨331340, by rfl⟩ : syracuseStep 1767149 = 662681) B662681
theorem B521971 : Blo 519798 521971 := bstep (se 1 (by rfl) ⟨391478, by rfl⟩ : syracuseStep 521971 = 782957) B782957
theorem B784115 : Blo 519798 784115 := bstep (se 1 (by rfl) ⟨588086, by rfl⟩ : syracuseStep 784115 = 1176173) B1176173
theorem B521987 : Blo 519798 521987 := bstep (se 1 (by rfl) ⟨391490, by rfl⟩ : syracuseStep 521987 = 782981) B782981
theorem B784145 : Blo 519798 784145 := bstep (se 2 (by rfl) ⟨294054, by rfl⟩ : syracuseStep 784145 = 588109) B588109
theorem B1177361 : Blo 519798 1177361 := bstep (se 2 (by rfl) ⟨441510, by rfl⟩ : syracuseStep 1177361 = 883021) B883021
theorem B522003 : Blo 519798 522003 := bstep (se 1 (by rfl) ⟨391502, by rfl⟩ : syracuseStep 522003 = 783005) B783005
theorem B522019 : Blo 519798 522019 := bstep (se 1 (by rfl) ⟨391514, by rfl⟩ : syracuseStep 522019 = 783029) B783029
theorem B784163 : Blo 519798 784163 := bstep (se 1 (by rfl) ⟨588122, by rfl⟩ : syracuseStep 784163 = 1176245) B1176245
theorem B1177379 : Blo 519798 1177379 := bstep (se 1 (by rfl) ⟨883034, by rfl⟩ : syracuseStep 1177379 = 1766069) B1766069
theorem B1767203 : Blo 519798 1767203 := bstep (se 1 (by rfl) ⟨1325402, by rfl⟩ : syracuseStep 1767203 = 2650805) B2650805
theorem B882481 : Blo 519798 882481 := bstep (se 2 (by rfl) ⟨330930, by rfl⟩ : syracuseStep 882481 = 661861) B661861
theorem B522035 : Blo 519798 522035 := bstep (se 1 (by rfl) ⟨391526, by rfl⟩ : syracuseStep 522035 = 783053) B783053
theorem B784193 : Blo 519798 784193 := bstep (se 2 (by rfl) ⟨294072, by rfl⟩ : syracuseStep 784193 = 588145) B588145
theorem B522051 : Blo 519798 522051 := bstep (se 1 (by rfl) ⟨391538, by rfl⟩ : syracuseStep 522051 = 783077) B783077
theorem B587587 : Blo 519798 587587 := bstep (se 1 (by rfl) ⟨440690, by rfl⟩ : syracuseStep 587587 = 881381) B881381
theorem B882515 : Blo 519798 882515 := bstep (se 1 (by rfl) ⟨661886, by rfl⟩ : syracuseStep 882515 = 1323773) B1323773
theorem B784211 : Blo 519798 784211 := bstep (se 1 (by rfl) ⟨588158, by rfl⟩ : syracuseStep 784211 = 1176317) B1176317
theorem B522067 : Blo 519798 522067 := bstep (se 1 (by rfl) ⟨391550, by rfl⟩ : syracuseStep 522067 = 783101) B783101
theorem B2815843 : Blo 519798 2815843 := bstep (se 1 (by rfl) ⟨2111882, by rfl⟩ : syracuseStep 2815843 = 4223765) B4223765
theorem B522083 : Blo 519798 522083 := bstep (se 1 (by rfl) ⟨391562, by rfl⟩ : syracuseStep 522083 = 783125) B783125
theorem B784241 : Blo 519798 784241 := bstep (se 2 (by rfl) ⟨294090, by rfl⟩ : syracuseStep 784241 = 588181) B588181
theorem B522099 : Blo 519798 522099 := bstep (se 1 (by rfl) ⟨391574, by rfl⟩ : syracuseStep 522099 = 783149) B783149
theorem B522115 : Blo 519798 522115 := bstep (se 1 (by rfl) ⟨391586, by rfl⟩ : syracuseStep 522115 = 783173) B783173
theorem B784259 : Blo 519798 784259 := bstep (se 1 (by rfl) ⟨588194, by rfl⟩ : syracuseStep 784259 = 1176389) B1176389
theorem B522131 : Blo 519798 522131 := bstep (se 1 (by rfl) ⟨391598, by rfl⟩ : syracuseStep 522131 = 783197) B783197
theorem B784289 : Blo 519798 784289 := bstep (se 2 (by rfl) ⟨294108, by rfl⟩ : syracuseStep 784289 = 588217) B588217
theorem B522147 : Blo 519798 522147 := bstep (se 1 (by rfl) ⟨391610, by rfl⟩ : syracuseStep 522147 = 783221) B783221
theorem B522163 : Blo 519798 522163 := bstep (se 1 (by rfl) ⟨391622, by rfl⟩ : syracuseStep 522163 = 783245) B783245
theorem B784307 : Blo 519798 784307 := bstep (se 1 (by rfl) ⟨588230, by rfl⟩ : syracuseStep 784307 = 1176461) B1176461
theorem B522179 : Blo 519798 522179 := bstep (se 1 (by rfl) ⟨391634, by rfl⟩ : syracuseStep 522179 = 783269) B783269
theorem B1406929 : Blo 519798 1406929 := bstep (se 2 (by rfl) ⟨527598, by rfl⟩ : syracuseStep 1406929 = 1055197) B1055197
theorem B784337 : Blo 519798 784337 := bstep (se 2 (by rfl) ⟨294126, by rfl⟩ : syracuseStep 784337 = 588253) B588253
theorem B522195 : Blo 519798 522195 := bstep (se 1 (by rfl) ⟨391646, by rfl⟩ : syracuseStep 522195 = 783293) B783293
theorem B587731 : Blo 519798 587731 := bstep (se 1 (by rfl) ⟨440798, by rfl⟩ : syracuseStep 587731 = 881597) B881597
theorem B882643 : Blo 519798 882643 := bstep (se 1 (by rfl) ⟨661982, by rfl⟩ : syracuseStep 882643 = 1323965) B1323965
theorem B522211 : Blo 519798 522211 := bstep (se 1 (by rfl) ⟨391658, by rfl⟩ : syracuseStep 522211 = 783317) B783317
theorem B784355 : Blo 519798 784355 := bstep (se 1 (by rfl) ⟨588266, by rfl⟩ : syracuseStep 784355 = 1176533) B1176533
theorem B522227 : Blo 519798 522227 := bstep (se 1 (by rfl) ⟨391670, by rfl⟩ : syracuseStep 522227 = 783341) B783341
theorem B784385 : Blo 519798 784385 := bstep (se 2 (by rfl) ⟨294144, by rfl⟩ : syracuseStep 784385 = 588289) B588289
theorem B522243 : Blo 519798 522243 := bstep (se 1 (by rfl) ⟨391682, by rfl⟩ : syracuseStep 522243 = 783365) B783365
theorem B522259 : Blo 519798 522259 := bstep (se 1 (by rfl) ⟨391694, by rfl⟩ : syracuseStep 522259 = 783389) B783389
theorem B784403 : Blo 519798 784403 := bstep (se 1 (by rfl) ⟨588302, by rfl⟩ : syracuseStep 784403 = 1176605) B1176605
theorem B522275 : Blo 519798 522275 := bstep (se 1 (by rfl) ⟨391706, by rfl⟩ : syracuseStep 522275 = 783413) B783413
theorem B784433 : Blo 519798 784433 := bstep (se 2 (by rfl) ⟨294162, by rfl⟩ : syracuseStep 784433 = 588325) B588325
theorem B1177649 : Blo 519798 1177649 := bstep (se 2 (by rfl) ⟨441618, by rfl⟩ : syracuseStep 1177649 = 883237) B883237
theorem B522291 : Blo 519798 522291 := bstep (se 1 (by rfl) ⟨391718, by rfl⟩ : syracuseStep 522291 = 783437) B783437
theorem B1767473 : Blo 519798 1767473 := bstep (se 2 (by rfl) ⟨662802, by rfl⟩ : syracuseStep 1767473 = 1325605) B1325605
theorem B1669187 : Blo 519798 1669187 := bstep (se 1 (by rfl) ⟨1251890, by rfl⟩ : syracuseStep 1669187 = 2503781) B2503781
theorem B522307 : Blo 519798 522307 := bstep (se 1 (by rfl) ⟨391730, by rfl⟩ : syracuseStep 522307 = 783461) B783461
theorem B784451 : Blo 519798 784451 := bstep (se 1 (by rfl) ⟨588338, by rfl⟩ : syracuseStep 784451 = 1176677) B1176677
theorem B1177667 : Blo 519798 1177667 := bstep (se 1 (by rfl) ⟨883250, by rfl⟩ : syracuseStep 1177667 = 1766501) B1766501
theorem B522323 : Blo 519798 522323 := bstep (se 1 (by rfl) ⟨391742, by rfl⟩ : syracuseStep 522323 = 783485) B783485
theorem B784481 : Blo 519798 784481 := bstep (se 2 (by rfl) ⟨294180, by rfl⟩ : syracuseStep 784481 = 588361) B588361
theorem B882785 : Blo 519798 882785 := bstep (se 2 (by rfl) ⟨331044, by rfl⟩ : syracuseStep 882785 = 662089) B662089
theorem B522339 : Blo 519798 522339 := bstep (se 1 (by rfl) ⟨391754, by rfl⟩ : syracuseStep 522339 = 783509) B783509
theorem B587875 : Blo 519798 587875 := bstep (se 1 (by rfl) ⟨440906, by rfl⟩ : syracuseStep 587875 = 881813) B881813
theorem B522355 : Blo 519798 522355 := bstep (se 1 (by rfl) ⟨391766, by rfl⟩ : syracuseStep 522355 = 783533) B783533
theorem B784499 : Blo 519798 784499 := bstep (se 1 (by rfl) ⟨588374, by rfl⟩ : syracuseStep 784499 = 1176749) B1176749
theorem B522371 : Blo 519798 522371 := bstep (se 1 (by rfl) ⟨391778, by rfl⟩ : syracuseStep 522371 = 783557) B783557
theorem B784529 : Blo 519798 784529 := bstep (se 2 (by rfl) ⟨294198, by rfl⟩ : syracuseStep 784529 = 588397) B588397
theorem B522387 : Blo 519798 522387 := bstep (se 1 (by rfl) ⟨391790, by rfl⟩ : syracuseStep 522387 = 783581) B783581
theorem B3045539 : Blo 519798 3045539 := bstep (se 1 (by rfl) ⟨2284154, by rfl⟩ : syracuseStep 3045539 = 4568309) B4568309
theorem B522403 : Blo 519798 522403 := bstep (se 1 (by rfl) ⟨391802, by rfl⟩ : syracuseStep 522403 = 783605) B783605
theorem B784547 : Blo 519798 784547 := bstep (se 1 (by rfl) ⟨588410, by rfl⟩ : syracuseStep 784547 = 1176821) B1176821
theorem B522419 : Blo 519798 522419 := bstep (se 1 (by rfl) ⟨391814, by rfl⟩ : syracuseStep 522419 = 783629) B783629
theorem B784577 : Blo 519798 784577 := bstep (se 2 (by rfl) ⟨294216, by rfl⟩ : syracuseStep 784577 = 588433) B588433
theorem B522435 : Blo 519798 522435 := bstep (se 1 (by rfl) ⟨391826, by rfl⟩ : syracuseStep 522435 = 783653) B783653
theorem B522451 : Blo 519798 522451 := bstep (se 1 (by rfl) ⟨391838, by rfl⟩ : syracuseStep 522451 = 783677) B783677
theorem B784595 : Blo 519798 784595 := bstep (se 1 (by rfl) ⟨588446, by rfl⟩ : syracuseStep 784595 = 1176893) B1176893
theorem B522467 : Blo 519798 522467 := bstep (se 1 (by rfl) ⟨391850, by rfl⟩ : syracuseStep 522467 = 783701) B783701
theorem B882913 : Blo 519798 882913 := bstep (se 2 (by rfl) ⟨331092, by rfl⟩ : syracuseStep 882913 = 662185) B662185
theorem B784625 : Blo 519798 784625 := bstep (se 2 (by rfl) ⟨294234, by rfl⟩ : syracuseStep 784625 = 588469) B588469
theorem B522483 : Blo 519798 522483 := bstep (se 1 (by rfl) ⟨391862, by rfl⟩ : syracuseStep 522483 = 783725) B783725
theorem B588019 : Blo 519798 588019 := bstep (se 1 (by rfl) ⟨441014, by rfl⟩ : syracuseStep 588019 = 882029) B882029
theorem B522499 : Blo 519798 522499 := bstep (se 1 (by rfl) ⟨391874, by rfl⟩ : syracuseStep 522499 = 783749) B783749
theorem B784643 : Blo 519798 784643 := bstep (se 1 (by rfl) ⟨588482, by rfl⟩ : syracuseStep 784643 = 1176965) B1176965
theorem B3012869 : Blo 519798 3012869 := bstep (se 4 (by rfl) ⟨282456, by rfl⟩ : syracuseStep 3012869 = 564913) B564913
theorem B882947 : Blo 519798 882947 := bstep (se 1 (by rfl) ⟨662210, by rfl⟩ : syracuseStep 882947 = 1324421) B1324421
theorem B522515 : Blo 519798 522515 := bstep (se 1 (by rfl) ⟨391886, by rfl⟩ : syracuseStep 522515 = 783773) B783773
theorem B784673 : Blo 519798 784673 := bstep (se 2 (by rfl) ⟨294252, by rfl⟩ : syracuseStep 784673 = 588505) B588505
theorem B522531 : Blo 519798 522531 := bstep (se 1 (by rfl) ⟨391898, by rfl⟩ : syracuseStep 522531 = 783797) B783797
theorem B522547 : Blo 519798 522547 := bstep (se 1 (by rfl) ⟨391910, by rfl⟩ : syracuseStep 522547 = 783821) B783821
theorem B784691 : Blo 519798 784691 := bstep (se 1 (by rfl) ⟨588518, by rfl⟩ : syracuseStep 784691 = 1177037) B1177037
theorem B522563 : Blo 519798 522563 := bstep (se 1 (by rfl) ⟨391922, by rfl⟩ : syracuseStep 522563 = 783845) B783845
theorem B784721 : Blo 519798 784721 := bstep (se 2 (by rfl) ⟨294270, by rfl⟩ : syracuseStep 784721 = 588541) B588541
theorem B1177937 : Blo 519798 1177937 := bstep (se 2 (by rfl) ⟨441726, by rfl⟩ : syracuseStep 1177937 = 883453) B883453
theorem B522579 : Blo 519798 522579 := bstep (se 1 (by rfl) ⟨391934, by rfl⟩ : syracuseStep 522579 = 783869) B783869
theorem B522595 : Blo 519798 522595 := bstep (se 1 (by rfl) ⟨391946, by rfl⟩ : syracuseStep 522595 = 783893) B783893
theorem B784739 : Blo 519798 784739 := bstep (se 1 (by rfl) ⟨588554, by rfl⟩ : syracuseStep 784739 = 1177109) B1177109
theorem B1177955 : Blo 519798 1177955 := bstep (se 1 (by rfl) ⟨883466, by rfl⟩ : syracuseStep 1177955 = 1766933) B1766933
theorem B522611 : Blo 519798 522611 := bstep (se 1 (by rfl) ⟨391958, by rfl⟩ : syracuseStep 522611 = 783917) B783917
theorem B784769 : Blo 519798 784769 := bstep (se 2 (by rfl) ⟨294288, by rfl⟩ : syracuseStep 784769 = 588577) B588577
theorem B522627 : Blo 519798 522627 := bstep (se 1 (by rfl) ⟨391970, by rfl⟩ : syracuseStep 522627 = 783941) B783941
theorem B588163 : Blo 519798 588163 := bstep (se 1 (by rfl) ⟨441122, by rfl⟩ : syracuseStep 588163 = 882245) B882245
theorem B883075 : Blo 519798 883075 := bstep (se 1 (by rfl) ⟨662306, by rfl⟩ : syracuseStep 883075 = 1324613) B1324613
theorem B522643 : Blo 519798 522643 := bstep (se 1 (by rfl) ⟨391982, by rfl⟩ : syracuseStep 522643 = 783965) B783965
theorem B784787 : Blo 519798 784787 := bstep (se 1 (by rfl) ⟨588590, by rfl⟩ : syracuseStep 784787 = 1177181) B1177181
theorem B522659 : Blo 519798 522659 := bstep (se 1 (by rfl) ⟨391994, by rfl⟩ : syracuseStep 522659 = 783989) B783989
theorem B784817 : Blo 519798 784817 := bstep (se 2 (by rfl) ⟨294306, by rfl⟩ : syracuseStep 784817 = 588613) B588613
theorem B522675 : Blo 519798 522675 := bstep (se 1 (by rfl) ⟨392006, by rfl⟩ : syracuseStep 522675 = 784013) B784013
theorem B522691 : Blo 519798 522691 := bstep (se 1 (by rfl) ⟨392018, by rfl⟩ : syracuseStep 522691 = 784037) B784037
theorem B784835 : Blo 519798 784835 := bstep (se 1 (by rfl) ⟨588626, by rfl⟩ : syracuseStep 784835 = 1177253) B1177253
theorem B522707 : Blo 519798 522707 := bstep (se 1 (by rfl) ⟨392030, by rfl⟩ : syracuseStep 522707 = 784061) B784061
theorem B784865 : Blo 519798 784865 := bstep (se 2 (by rfl) ⟨294324, by rfl⟩ : syracuseStep 784865 = 588649) B588649
theorem B522723 : Blo 519798 522723 := bstep (se 1 (by rfl) ⟨392042, by rfl⟩ : syracuseStep 522723 = 784085) B784085
theorem B522739 : Blo 519798 522739 := bstep (se 1 (by rfl) ⟨392054, by rfl⟩ : syracuseStep 522739 = 784109) B784109
theorem B784883 : Blo 519798 784883 := bstep (se 1 (by rfl) ⟨588662, by rfl⟩ : syracuseStep 784883 = 1177325) B1177325
theorem B522755 : Blo 519798 522755 := bstep (se 1 (by rfl) ⟨392066, by rfl⟩ : syracuseStep 522755 = 784133) B784133
theorem B784913 : Blo 519798 784913 := bstep (se 2 (by rfl) ⟨294342, by rfl⟩ : syracuseStep 784913 = 588685) B588685
theorem B883217 : Blo 519798 883217 := bstep (se 2 (by rfl) ⟨331206, by rfl⟩ : syracuseStep 883217 = 662413) B662413
theorem B522771 : Blo 519798 522771 := bstep (se 1 (by rfl) ⟨392078, by rfl⟩ : syracuseStep 522771 = 784157) B784157
theorem B588307 : Blo 519798 588307 := bstep (se 1 (by rfl) ⟨441230, by rfl⟩ : syracuseStep 588307 = 882461) B882461
theorem B522787 : Blo 519798 522787 := bstep (se 1 (by rfl) ⟨392090, by rfl⟩ : syracuseStep 522787 = 784181) B784181
theorem B784931 : Blo 519798 784931 := bstep (se 1 (by rfl) ⟨588698, by rfl⟩ : syracuseStep 784931 = 1177397) B1177397
theorem B1505837 : Blo 519798 1505837 := bstep (se 3 (by rfl) ⟨282344, by rfl⟩ : syracuseStep 1505837 = 564689) B564689
theorem B1342001 : Blo 519798 1342001 := bstep (se 2 (by rfl) ⟨503250, by rfl⟩ : syracuseStep 1342001 = 1006501) B1006501
theorem B522803 : Blo 519798 522803 := bstep (se 1 (by rfl) ⟨392102, by rfl⟩ : syracuseStep 522803 = 784205) B784205
theorem B784961 : Blo 519798 784961 := bstep (se 2 (by rfl) ⟨294360, by rfl⟩ : syracuseStep 784961 = 588721) B588721
theorem B522819 : Blo 519798 522819 := bstep (se 1 (by rfl) ⟨392114, by rfl⟩ : syracuseStep 522819 = 784229) B784229
theorem B522835 : Blo 519798 522835 := bstep (se 1 (by rfl) ⟨392126, by rfl⟩ : syracuseStep 522835 = 784253) B784253
theorem B784979 : Blo 519798 784979 := bstep (se 1 (by rfl) ⟨588734, by rfl⟩ : syracuseStep 784979 = 1177469) B1177469
theorem B522851 : Blo 519798 522851 := bstep (se 1 (by rfl) ⟨392138, by rfl⟩ : syracuseStep 522851 = 784277) B784277
theorem B785009 : Blo 519798 785009 := bstep (se 2 (by rfl) ⟨294378, by rfl⟩ : syracuseStep 785009 = 588757) B588757
theorem B1178225 : Blo 519798 1178225 := bstep (se 2 (by rfl) ⟨441834, by rfl⟩ : syracuseStep 1178225 = 883669) B883669
theorem B522867 : Blo 519798 522867 := bstep (se 1 (by rfl) ⟨392150, by rfl⟩ : syracuseStep 522867 = 784301) B784301
theorem B522883 : Blo 519798 522883 := bstep (se 1 (by rfl) ⟨392162, by rfl⟩ : syracuseStep 522883 = 784325) B784325
theorem B785027 : Blo 519798 785027 := bstep (se 1 (by rfl) ⟨588770, by rfl⟩ : syracuseStep 785027 = 1177541) B1177541
theorem B1178243 : Blo 519798 1178243 := bstep (se 1 (by rfl) ⟨883682, by rfl⟩ : syracuseStep 1178243 = 1767365) B1767365
theorem B522899 : Blo 519798 522899 := bstep (se 1 (by rfl) ⟨392174, by rfl⟩ : syracuseStep 522899 = 784349) B784349
theorem B883345 : Blo 519798 883345 := bstep (se 2 (by rfl) ⟨331254, by rfl⟩ : syracuseStep 883345 = 662509) B662509
theorem B785057 : Blo 519798 785057 := bstep (se 2 (by rfl) ⟨294396, by rfl⟩ : syracuseStep 785057 = 588793) B588793
theorem B522915 : Blo 519798 522915 := bstep (se 1 (by rfl) ⟨392186, by rfl⟩ : syracuseStep 522915 = 784373) B784373
theorem B588451 : Blo 519798 588451 := bstep (se 1 (by rfl) ⟨441338, by rfl⟩ : syracuseStep 588451 = 882677) B882677
theorem B522931 : Blo 519798 522931 := bstep (se 1 (by rfl) ⟨392198, by rfl⟩ : syracuseStep 522931 = 784397) B784397
theorem B785075 : Blo 519798 785075 := bstep (se 1 (by rfl) ⟨588806, by rfl⟩ : syracuseStep 785075 = 1177613) B1177613
theorem B883379 : Blo 519798 883379 := bstep (se 1 (by rfl) ⟨662534, by rfl⟩ : syracuseStep 883379 = 1325069) B1325069
theorem B522947 : Blo 519798 522947 := bstep (se 1 (by rfl) ⟨392210, by rfl⟩ : syracuseStep 522947 = 784421) B784421
theorem B785105 : Blo 519798 785105 := bstep (se 2 (by rfl) ⟨294414, by rfl⟩ : syracuseStep 785105 = 588829) B588829
theorem B522963 : Blo 519798 522963 := bstep (se 1 (by rfl) ⟨392222, by rfl⟩ : syracuseStep 522963 = 784445) B784445
theorem B522979 : Blo 519798 522979 := bstep (se 1 (by rfl) ⟨392234, by rfl⟩ : syracuseStep 522979 = 784469) B784469
theorem B785123 : Blo 519798 785123 := bstep (se 1 (by rfl) ⟨588842, by rfl⟩ : syracuseStep 785123 = 1177685) B1177685
theorem B522995 : Blo 519798 522995 := bstep (se 1 (by rfl) ⟨392246, by rfl⟩ : syracuseStep 522995 = 784493) B784493
theorem B785153 : Blo 519798 785153 := bstep (se 2 (by rfl) ⟨294432, by rfl⟩ : syracuseStep 785153 = 588865) B588865
theorem B523011 : Blo 519798 523011 := bstep (se 1 (by rfl) ⟨392258, by rfl⟩ : syracuseStep 523011 = 784517) B784517
theorem B523027 : Blo 519798 523027 := bstep (se 1 (by rfl) ⟨392270, by rfl⟩ : syracuseStep 523027 = 784541) B784541
theorem B785171 : Blo 519798 785171 := bstep (se 1 (by rfl) ⟨588878, by rfl⟩ : syracuseStep 785171 = 1177757) B1177757
theorem B523043 : Blo 519798 523043 := bstep (se 1 (by rfl) ⟨392282, by rfl⟩ : syracuseStep 523043 = 784565) B784565
theorem B1407793 : Blo 519798 1407793 := bstep (se 2 (by rfl) ⟨527922, by rfl⟩ : syracuseStep 1407793 = 1055845) B1055845
theorem B785201 : Blo 519798 785201 := bstep (se 2 (by rfl) ⟨294450, by rfl⟩ : syracuseStep 785201 = 588901) B588901
theorem B523059 : Blo 519798 523059 := bstep (se 1 (by rfl) ⟨392294, by rfl⟩ : syracuseStep 523059 = 784589) B784589
theorem B588595 : Blo 519798 588595 := bstep (se 1 (by rfl) ⟨441446, by rfl⟩ : syracuseStep 588595 = 882893) B882893
theorem B883507 : Blo 519798 883507 := bstep (se 1 (by rfl) ⟨662630, by rfl⟩ : syracuseStep 883507 = 1325261) B1325261
theorem B523075 : Blo 519798 523075 := bstep (se 1 (by rfl) ⟨392306, by rfl⟩ : syracuseStep 523075 = 784613) B784613
theorem B785219 : Blo 519798 785219 := bstep (se 1 (by rfl) ⟨588914, by rfl⟩ : syracuseStep 785219 = 1177829) B1177829
theorem B523091 : Blo 519798 523091 := bstep (se 1 (by rfl) ⟨392318, by rfl⟩ : syracuseStep 523091 = 784637) B784637
theorem B785249 : Blo 519798 785249 := bstep (se 2 (by rfl) ⟨294468, by rfl⟩ : syracuseStep 785249 = 588937) B588937
theorem B523107 : Blo 519798 523107 := bstep (se 1 (by rfl) ⟨392330, by rfl⟩ : syracuseStep 523107 = 784661) B784661
theorem B523123 : Blo 519798 523123 := bstep (se 1 (by rfl) ⟨392342, by rfl⟩ : syracuseStep 523123 = 784685) B784685
theorem B785267 : Blo 519798 785267 := bstep (se 1 (by rfl) ⟨588950, by rfl⟩ : syracuseStep 785267 = 1177901) B1177901
theorem B523139 : Blo 519798 523139 := bstep (se 1 (by rfl) ⟨392354, by rfl⟩ : syracuseStep 523139 = 784709) B784709
theorem B3341189 : Blo 519798 3341189 := bstep (se 4 (by rfl) ⟨313236, by rfl⟩ : syracuseStep 3341189 = 626473) B626473
theorem B2227085 : Blo 519798 2227085 := bstep (se 3 (by rfl) ⟨417578, by rfl⟩ : syracuseStep 2227085 = 835157) B835157
theorem B785297 : Blo 519798 785297 := bstep (se 2 (by rfl) ⟨294486, by rfl⟩ : syracuseStep 785297 = 588973) B588973
theorem B1178513 : Blo 519798 1178513 := bstep (se 2 (by rfl) ⟨441942, by rfl⟩ : syracuseStep 1178513 = 883885) B883885
theorem B523155 : Blo 519798 523155 := bstep (se 1 (by rfl) ⟨392366, by rfl⟩ : syracuseStep 523155 = 784733) B784733
theorem B523171 : Blo 519798 523171 := bstep (se 1 (by rfl) ⟨392378, by rfl⟩ : syracuseStep 523171 = 784757) B784757
theorem B785315 : Blo 519798 785315 := bstep (se 1 (by rfl) ⟨588986, by rfl⟩ : syracuseStep 785315 = 1177973) B1177973
theorem B1178531 : Blo 519798 1178531 := bstep (se 1 (by rfl) ⟨883898, by rfl⟩ : syracuseStep 1178531 = 1767797) B1767797
theorem B523187 : Blo 519798 523187 := bstep (se 1 (by rfl) ⟨392390, by rfl⟩ : syracuseStep 523187 = 784781) B784781
theorem B785345 : Blo 519798 785345 := bstep (se 2 (by rfl) ⟨294504, by rfl⟩ : syracuseStep 785345 = 589009) B589009
theorem B883649 : Blo 519798 883649 := bstep (se 2 (by rfl) ⟨331368, by rfl⟩ : syracuseStep 883649 = 662737) B662737
theorem B523203 : Blo 519798 523203 := bstep (se 1 (by rfl) ⟨392402, by rfl⟩ : syracuseStep 523203 = 784805) B784805
theorem B588739 : Blo 519798 588739 := bstep (se 1 (by rfl) ⟨441554, by rfl⟩ : syracuseStep 588739 = 883109) B883109
theorem B523219 : Blo 519798 523219 := bstep (se 1 (by rfl) ⟨392414, by rfl⟩ : syracuseStep 523219 = 784829) B784829
theorem B785363 : Blo 519798 785363 := bstep (se 1 (by rfl) ⟨589022, by rfl⟩ : syracuseStep 785363 = 1178045) B1178045
theorem B523235 : Blo 519798 523235 := bstep (se 1 (by rfl) ⟨392426, by rfl⟩ : syracuseStep 523235 = 784853) B784853
theorem B785393 : Blo 519798 785393 := bstep (se 2 (by rfl) ⟨294522, by rfl⟩ : syracuseStep 785393 = 589045) B589045
theorem B523251 : Blo 519798 523251 := bstep (se 1 (by rfl) ⟨392438, by rfl⟩ : syracuseStep 523251 = 784877) B784877
theorem B523267 : Blo 519798 523267 := bstep (se 1 (by rfl) ⟨392450, by rfl⟩ : syracuseStep 523267 = 784901) B784901
theorem B785411 : Blo 519798 785411 := bstep (se 1 (by rfl) ⟨589058, by rfl⟩ : syracuseStep 785411 = 1178117) B1178117
theorem B523283 : Blo 519798 523283 := bstep (se 1 (by rfl) ⟨392462, by rfl⟩ : syracuseStep 523283 = 784925) B784925
theorem B785441 : Blo 519798 785441 := bstep (se 2 (by rfl) ⟨294540, by rfl⟩ : syracuseStep 785441 = 589081) B589081
theorem B523299 : Blo 519798 523299 := bstep (se 1 (by rfl) ⟨392474, by rfl⟩ : syracuseStep 523299 = 784949) B784949
theorem B523315 : Blo 519798 523315 := bstep (se 1 (by rfl) ⟨392486, by rfl⟩ : syracuseStep 523315 = 784973) B784973
theorem B785459 : Blo 519798 785459 := bstep (se 1 (by rfl) ⟨589094, by rfl⟩ : syracuseStep 785459 = 1178189) B1178189
theorem B883777 : Blo 519798 883777 := bstep (se 2 (by rfl) ⟨331416, by rfl⟩ : syracuseStep 883777 = 662833) B662833
theorem B523331 : Blo 519798 523331 := bstep (se 1 (by rfl) ⟨392498, by rfl⟩ : syracuseStep 523331 = 784997) B784997
theorem B785489 : Blo 519798 785489 := bstep (se 2 (by rfl) ⟨294558, by rfl⟩ : syracuseStep 785489 = 589117) B589117
theorem B523347 : Blo 519798 523347 := bstep (se 1 (by rfl) ⟨392510, by rfl⟩ : syracuseStep 523347 = 785021) B785021
theorem B588883 : Blo 519798 588883 := bstep (se 1 (by rfl) ⟨441662, by rfl⟩ : syracuseStep 588883 = 883325) B883325
theorem B523363 : Blo 519798 523363 := bstep (se 1 (by rfl) ⟨392522, by rfl⟩ : syracuseStep 523363 = 785045) B785045
theorem B785507 : Blo 519798 785507 := bstep (se 1 (by rfl) ⟨589130, by rfl⟩ : syracuseStep 785507 = 1178261) B1178261
theorem B883811 : Blo 519798 883811 := bstep (se 1 (by rfl) ⟨662858, by rfl⟩ : syracuseStep 883811 = 1325717) B1325717
theorem B523379 : Blo 519798 523379 := bstep (se 1 (by rfl) ⟨392534, by rfl⟩ : syracuseStep 523379 = 785069) B785069
theorem B785537 : Blo 519798 785537 := bstep (se 2 (by rfl) ⟨294576, by rfl⟩ : syracuseStep 785537 = 589153) B589153
theorem B523395 : Blo 519798 523395 := bstep (se 1 (by rfl) ⟨392546, by rfl⟩ : syracuseStep 523395 = 785093) B785093
theorem B523411 : Blo 519798 523411 := bstep (se 1 (by rfl) ⟨392558, by rfl⟩ : syracuseStep 523411 = 785117) B785117
theorem B785555 : Blo 519798 785555 := bstep (se 1 (by rfl) ⟨589166, by rfl⟩ : syracuseStep 785555 = 1178333) B1178333
theorem B523427 : Blo 519798 523427 := bstep (se 1 (by rfl) ⟨392570, by rfl⟩ : syracuseStep 523427 = 785141) B785141
theorem B785585 : Blo 519798 785585 := bstep (se 2 (by rfl) ⟨294594, by rfl⟩ : syracuseStep 785585 = 589189) B589189
theorem B523443 : Blo 519798 523443 := bstep (se 1 (by rfl) ⟨392582, by rfl⟩ : syracuseStep 523443 = 785165) B785165
theorem B523459 : Blo 519798 523459 := bstep (se 1 (by rfl) ⟨392594, by rfl⟩ : syracuseStep 523459 = 785189) B785189
theorem B785603 : Blo 519798 785603 := bstep (se 1 (by rfl) ⟨589202, by rfl⟩ : syracuseStep 785603 = 1178405) B1178405
theorem B523475 : Blo 519798 523475 := bstep (se 1 (by rfl) ⟨392606, by rfl⟩ : syracuseStep 523475 = 785213) B785213
theorem B785633 : Blo 519798 785633 := bstep (se 2 (by rfl) ⟨294612, by rfl⟩ : syracuseStep 785633 = 589225) B589225
theorem B523491 : Blo 519798 523491 := bstep (se 1 (by rfl) ⟨392618, by rfl⟩ : syracuseStep 523491 = 785237) B785237
theorem B589027 : Blo 519798 589027 := bstep (se 1 (by rfl) ⟨441770, by rfl⟩ : syracuseStep 589027 = 883541) B883541
theorem B523507 : Blo 519798 523507 := bstep (se 1 (by rfl) ⟨392630, by rfl⟩ : syracuseStep 523507 = 785261) B785261
theorem B785651 : Blo 519798 785651 := bstep (se 1 (by rfl) ⟨589238, by rfl⟩ : syracuseStep 785651 = 1178477) B1178477
theorem B523523 : Blo 519798 523523 := bstep (se 1 (by rfl) ⟨392642, by rfl⟩ : syracuseStep 523523 = 785285) B785285
theorem B785681 : Blo 519798 785681 := bstep (se 2 (by rfl) ⟨294630, by rfl⟩ : syracuseStep 785681 = 589261) B589261
theorem B523539 : Blo 519798 523539 := bstep (se 1 (by rfl) ⟨392654, by rfl⟩ : syracuseStep 523539 = 785309) B785309
theorem B523555 : Blo 519798 523555 := bstep (se 1 (by rfl) ⟨392666, by rfl⟩ : syracuseStep 523555 = 785333) B785333
theorem B523571 : Blo 519798 523571 := bstep (se 1 (by rfl) ⟨392678, by rfl⟩ : syracuseStep 523571 = 785357) B785357
theorem B523587 : Blo 519798 523587 := bstep (se 1 (by rfl) ⟨392690, by rfl⟩ : syracuseStep 523587 = 785381) B785381
theorem B523603 : Blo 519798 523603 := bstep (se 1 (by rfl) ⟨392702, by rfl⟩ : syracuseStep 523603 = 785405) B785405
theorem B523619 : Blo 519798 523619 := bstep (se 1 (by rfl) ⟨392714, by rfl⟩ : syracuseStep 523619 = 785429) B785429
theorem B523635 : Blo 519798 523635 := bstep (se 1 (by rfl) ⟨392726, by rfl⟩ : syracuseStep 523635 = 785453) B785453
theorem B589171 : Blo 519798 589171 := bstep (se 1 (by rfl) ⟨441878, by rfl⟩ : syracuseStep 589171 = 883757) B883757
theorem B523651 : Blo 519798 523651 := bstep (se 1 (by rfl) ⟨392738, by rfl⟩ : syracuseStep 523651 = 785477) B785477
theorem B3964301 : Blo 519798 3964301 := bstep (se 3 (by rfl) ⟨743306, by rfl⟩ : syracuseStep 3964301 = 1486613) B1486613
theorem B523667 : Blo 519798 523667 := bstep (se 1 (by rfl) ⟨392750, by rfl⟩ : syracuseStep 523667 = 785501) B785501
theorem B523683 : Blo 519798 523683 := bstep (se 1 (by rfl) ⟨392762, by rfl⟩ : syracuseStep 523683 = 785525) B785525
theorem B523699 : Blo 519798 523699 := bstep (se 1 (by rfl) ⟨392774, by rfl⟩ : syracuseStep 523699 = 785549) B785549
theorem B523715 : Blo 519798 523715 := bstep (se 1 (by rfl) ⟨392786, by rfl⟩ : syracuseStep 523715 = 785573) B785573
theorem B523731 : Blo 519798 523731 := bstep (se 1 (by rfl) ⟨392798, by rfl⟩ : syracuseStep 523731 = 785597) B785597
theorem B523747 : Blo 519798 523747 := bstep (se 1 (by rfl) ⟨392810, by rfl⟩ : syracuseStep 523747 = 785621) B785621
theorem B523763 : Blo 519798 523763 := bstep (se 1 (by rfl) ⟨392822, by rfl⟩ : syracuseStep 523763 = 785645) B785645
theorem B523779 : Blo 519798 523779 := bstep (se 1 (by rfl) ⟨392834, by rfl⟩ : syracuseStep 523779 = 785669) B785669
theorem B523795 : Blo 519798 523795 := bstep (se 1 (by rfl) ⟨392846, by rfl⟩ : syracuseStep 523795 = 785693) B785693
theorem B556643 : Blo 519798 556643 := bstep (se 1 (by rfl) ⟨417482, by rfl⟩ : syracuseStep 556643 = 834965) B834965
theorem B2228417 : Blo 519798 2228417 := bstep (se 2 (by rfl) ⟨835656, by rfl⟩ : syracuseStep 2228417 = 1671313) B1671313
theorem B17170805 : Blo 519798 17170805 := bstep (se 5 (by rfl) ⟨804881, by rfl⟩ : syracuseStep 17170805 = 1609763) B1609763
theorem B1409501 : Blo 519798 1409501 := bstep (se 3 (by rfl) ⟨264281, by rfl⟩ : syracuseStep 1409501 = 528563) B528563
theorem B2228759 : Blo 519798 2228759 := bstep (se 1 (by rfl) ⟨1671569, by rfl⟩ : syracuseStep 2228759 = 3343139) B3343139
theorem B2982977 : Blo 519798 2982977 := bstep (se 2 (by rfl) ⟨1118616, by rfl⟩ : syracuseStep 2982977 = 2237233) B2237233
theorem B2819393 : Blo 519798 2819393 := bstep (se 2 (by rfl) ⟨1057272, by rfl⟩ : syracuseStep 2819393 = 2114545) B2114545
theorem B1115507 : Blo 519798 1115507 := bstep (se 1 (by rfl) ⟨836630, by rfl⟩ : syracuseStep 1115507 = 1673261) B1673261
theorem B1607347 : Blo 519798 1607347 := bstep (se 1 (by rfl) ⟨1205510, by rfl⟩ : syracuseStep 1607347 = 2411021) B2411021
theorem B558775 : Blo 519798 558775 := bstep (se 1 (by rfl) ⟨419081, by rfl⟩ : syracuseStep 558775 = 838163) B838163
theorem B18351937 : Blo 519798 18351937 := bstep (se 2 (by rfl) ⟨6881976, by rfl⟩ : syracuseStep 18351937 = 13763953) B13763953
theorem B624523 : Blo 519798 624523 := bstep (se 1 (by rfl) ⟨468392, by rfl⟩ : syracuseStep 624523 = 936785) B936785
theorem B2230877 : Blo 519798 2230877 := bstep (se 3 (by rfl) ⟨418289, by rfl⟩ : syracuseStep 2230877 = 836579) B836579
theorem B1116823 : Blo 519798 1116823 := bstep (se 1 (by rfl) ⟨837617, by rfl⟩ : syracuseStep 1116823 = 1675235) B1675235
theorem B658135 : Blo 519798 658135 := bstep (se 1 (by rfl) ⟨493601, by rfl⟩ : syracuseStep 658135 = 987203) B987203
theorem B1117003 : Blo 519798 1117003 := bstep (se 1 (by rfl) ⟨837752, by rfl⟩ : syracuseStep 1117003 = 1675505) B1675505
theorem B2231185 : Blo 519798 2231185 := bstep (se 2 (by rfl) ⟨836694, by rfl⟩ : syracuseStep 2231185 = 1673389) B1673389
theorem B1117079 : Blo 519798 1117079 := bstep (se 1 (by rfl) ⟨837809, by rfl⟩ : syracuseStep 1117079 = 1675619) B1675619
theorem B2231219 : Blo 519798 2231219 := bstep (se 1 (by rfl) ⟨1673414, by rfl⟩ : syracuseStep 2231219 = 3346829) B3346829
theorem B658955 : Blo 519798 658955 := bstep (se 1 (by rfl) ⟨494216, by rfl⟩ : syracuseStep 658955 = 988433) B988433
theorem B4460183 : Blo 519798 4460183 := bstep (se 1 (by rfl) ⟨3345137, by rfl⟩ : syracuseStep 4460183 = 6690275) B6690275
theorem B1412939 : Blo 519798 1412939 := bstep (se 1 (by rfl) ⟨1059704, by rfl⟩ : syracuseStep 1412939 = 2119409) B2119409
theorem B10030949 : Blo 519798 10030949 := bstep (se 4 (by rfl) ⟨940401, by rfl⟩ : syracuseStep 10030949 = 1880803) B1880803
theorem B987059 : Blo 519798 987059 := bstep (se 1 (by rfl) ⟨740294, by rfl⟩ : syracuseStep 987059 = 1480589) B1480589
theorem B659659 : Blo 519798 659659 := bstep (se 1 (by rfl) ⟨494744, by rfl⟩ : syracuseStep 659659 = 989489) B989489
theorem B627031 : Blo 519798 627031 := bstep (se 1 (by rfl) ⟨470273, by rfl⟩ : syracuseStep 627031 = 940547) B940547
theorem B987545 : Blo 519798 987545 := bstep (se 2 (by rfl) ⟨370329, by rfl⟩ : syracuseStep 987545 = 740659) B740659
theorem B659927 : Blo 519798 659927 := bstep (se 1 (by rfl) ⟨494945, by rfl⟩ : syracuseStep 659927 = 989891) B989891
theorem B594551 : Blo 519798 594551 := bstep (se 1 (by rfl) ⟨445913, by rfl⟩ : syracuseStep 594551 = 891827) B891827
theorem B2233133 : Blo 519798 2233133 := bstep (se 3 (by rfl) ⟨418712, by rfl⟩ : syracuseStep 2233133 = 837425) B837425
theorem B660631 : Blo 519798 660631 := bstep (se 1 (by rfl) ⟨495473, by rfl⟩ : syracuseStep 660631 = 990947) B990947
theorem B3347729 : Blo 519798 3347729 := bstep (se 2 (by rfl) ⟨1255398, by rfl⟩ : syracuseStep 3347729 = 2510797) B2510797
theorem B16258421 : Blo 519798 16258421 := bstep (se 5 (by rfl) ⟨762113, by rfl⟩ : syracuseStep 16258421 = 1524227) B1524227
theorem B1676695 : Blo 519798 1676695 := bstep (se 1 (by rfl) ⟨1257521, by rfl⟩ : syracuseStep 1676695 = 2515043) B2515043
theorem B2233817 : Blo 519798 2233817 := bstep (se 2 (by rfl) ⟨837681, by rfl⟩ : syracuseStep 2233817 = 1675363) B1675363
theorem B1676875 : Blo 519798 1676875 := bstep (se 1 (by rfl) ⟨1257656, by rfl⟩ : syracuseStep 1676875 = 2515313) B2515313
theorem B2004625 : Blo 519798 2004625 := bstep (se 2 (by rfl) ⟨751734, by rfl⟩ : syracuseStep 2004625 = 1503469) B1503469
theorem B1676951 : Blo 519798 1676951 := bstep (se 1 (by rfl) ⟨1257713, by rfl⟩ : syracuseStep 1676951 = 2515427) B2515427
theorem B989003 : Blo 519798 989003 := bstep (se 1 (by rfl) ⟨741752, by rfl⟩ : syracuseStep 989003 = 1483505) B1483505
theorem B1677145 : Blo 519798 1677145 := bstep (se 2 (by rfl) ⟨628929, by rfl⟩ : syracuseStep 1677145 = 1257859) B1257859
theorem B11409329 : Blo 519798 11409329 := bstep (se 2 (by rfl) ⟨4278498, by rfl⟩ : syracuseStep 11409329 = 8556997) B8556997
theorem B989185 : Blo 519798 989185 := bstep (se 2 (by rfl) ⟨370944, by rfl⟩ : syracuseStep 989185 = 741889) B741889
theorem B8034317 : Blo 519798 8034317 := bstep (se 3 (by rfl) ⟨1506434, by rfl⟩ : syracuseStep 8034317 = 3012869) B3012869
theorem B1185817 : Blo 519798 1185817 := bstep (se 2 (by rfl) ⟨444681, by rfl⟩ : syracuseStep 1185817 = 889363) B889363
theorem B2824409 : Blo 519798 2824409 := bstep (se 2 (by rfl) ⟨1059153, by rfl⟩ : syracuseStep 2824409 = 2118307) B2118307
theorem B3774755 : Blo 519798 3774755 := bstep (se 1 (by rfl) ⟨2831066, by rfl⟩ : syracuseStep 3774755 = 5662133) B5662133
theorem B1251659 : Blo 519798 1251659 := bstep (se 1 (by rfl) ⟨938744, by rfl⟩ : syracuseStep 1251659 = 1877489) B1877489
theorem B2824579 : Blo 519798 2824579 := bstep (se 1 (by rfl) ⟨2118434, by rfl⟩ : syracuseStep 2824579 = 4236869) B4236869
theorem B3021187 : Blo 519798 3021187 := bstep (se 1 (by rfl) ⟨2265890, by rfl⟩ : syracuseStep 3021187 = 4531781) B4531781
theorem B989633 : Blo 519798 989633 := bstep (se 2 (by rfl) ⟨371112, by rfl⟩ : syracuseStep 989633 = 742225) B742225
theorem B1317323 : Blo 519798 1317323 := bstep (se 1 (by rfl) ⟨987992, by rfl⟩ : syracuseStep 1317323 = 1975985) B1975985
theorem B4135373 : Blo 519798 4135373 := bstep (se 3 (by rfl) ⟨775382, by rfl⟩ : syracuseStep 4135373 = 1550765) B1550765
theorem B1481419 : Blo 519798 1481419 := bstep (se 1 (by rfl) ⟨1111064, by rfl⟩ : syracuseStep 1481419 = 2222129) B2222129
theorem B989975 : Blo 519798 989975 := bstep (se 1 (by rfl) ⟨742481, by rfl⟩ : syracuseStep 989975 = 1484963) B1484963
theorem B3054401 : Blo 519798 3054401 := bstep (se 2 (by rfl) ⟨1145400, by rfl⟩ : syracuseStep 3054401 = 2290801) B2290801
theorem B662347 : Blo 519798 662347 := bstep (se 1 (by rfl) ⟨496760, by rfl⟩ : syracuseStep 662347 = 993521) B993521
theorem B1874909 : Blo 519798 1874909 := bstep (se 3 (by rfl) ⟨351545, by rfl⟩ : syracuseStep 1874909 = 703091) B703091
theorem B1481921 : Blo 519798 1481921 := bstep (se 2 (by rfl) ⟨555720, by rfl⟩ : syracuseStep 1481921 = 1111441) B1111441
theorem B1318295 : Blo 519798 1318295 := bstep (se 1 (by rfl) ⟨988721, by rfl⟩ : syracuseStep 1318295 = 1977443) B1977443
theorem B990643 : Blo 519798 990643 := bstep (se 1 (by rfl) ⟨742982, by rfl⟩ : syracuseStep 990643 = 1485965) B1485965
theorem B5643793 : Blo 519798 5643793 := bstep (se 2 (by rfl) ⟨2116422, by rfl⟩ : syracuseStep 5643793 = 4232845) B4232845
theorem B1482263 : Blo 519798 1482263 := bstep (se 1 (by rfl) ⟨1111697, by rfl⟩ : syracuseStep 1482263 = 2223395) B2223395
theorem B991091 : Blo 519798 991091 := bstep (se 1 (by rfl) ⟨743318, by rfl⟩ : syracuseStep 991091 = 1486637) B1486637
theorem B2498435 : Blo 519798 2498435 := bstep (se 1 (by rfl) ⟨1873826, by rfl⟩ : syracuseStep 2498435 = 3747653) B3747653
theorem B991129 : Blo 519798 991129 := bstep (se 2 (by rfl) ⟨371673, by rfl⟩ : syracuseStep 991129 = 743347) B743347
theorem B1875905 : Blo 519798 1875905 := bstep (se 2 (by rfl) ⟨703464, by rfl⟩ : syracuseStep 1875905 = 1406929) B1406929
theorem B1318963 : Blo 519798 1318963 := bstep (se 1 (by rfl) ⟨989222, by rfl⟩ : syracuseStep 1318963 = 1978445) B1978445
theorem B4005953 : Blo 519798 4005953 := bstep (se 2 (by rfl) ⟨1502232, by rfl⟩ : syracuseStep 4005953 = 3004465) B3004465
theorem B2236481 : Blo 519798 2236481 := bstep (se 2 (by rfl) ⟨838680, by rfl⟩ : syracuseStep 2236481 = 1677361) B1677361
theorem B3350621 : Blo 519798 3350621 := bstep (se 3 (by rfl) ⟨628241, by rfl⟩ : syracuseStep 3350621 = 1256483) B1256483
theorem B1056883 : Blo 519798 1056883 := bstep (se 1 (by rfl) ⟨792662, by rfl⟩ : syracuseStep 1056883 = 1585325) B1585325
theorem B1319105 : Blo 519798 1319105 := bstep (se 2 (by rfl) ⟨494664, by rfl⟩ : syracuseStep 1319105 = 989329) B989329
theorem B1286423 : Blo 519798 1286423 := bstep (se 1 (by rfl) ⟨964817, by rfl⟩ : syracuseStep 1286423 = 1929635) B1929635
theorem B4759883 : Blo 519798 4759883 := bstep (se 1 (by rfl) ⟨3569912, by rfl⟩ : syracuseStep 4759883 = 7139825) B7139825
theorem B991577 : Blo 519798 991577 := bstep (se 2 (by rfl) ⟨371841, by rfl⟩ : syracuseStep 991577 = 743683) B743683
theorem B1975043 : Blo 519798 1975043 := bstep (se 1 (by rfl) ⟨1481282, by rfl⟩ : syracuseStep 1975043 = 2962565) B2962565
theorem B1877057 : Blo 519798 1877057 := bstep (se 2 (by rfl) ⟨703896, by rfl⟩ : syracuseStep 1877057 = 1407793) B1407793
theorem B992321 : Blo 519798 992321 := bstep (se 2 (by rfl) ⟨372120, by rfl⟩ : syracuseStep 992321 = 744241) B744241
theorem B1975499 : Blo 519798 1975499 := bstep (se 1 (by rfl) ⟨1481624, by rfl⟩ : syracuseStep 1975499 = 2963249) B2963249
theorem B992587 : Blo 519798 992587 := bstep (se 1 (by rfl) ⟨744440, by rfl⟩ : syracuseStep 992587 = 1488881) B1488881
theorem B1975697 : Blo 519798 1975697 := bstep (se 2 (by rfl) ⟨740886, by rfl⟩ : syracuseStep 1975697 = 1481773) B1481773
theorem B1320371 : Blo 519798 1320371 := bstep (se 1 (by rfl) ⟨990278, by rfl⟩ : syracuseStep 1320371 = 1980557) B1980557
theorem B1484381 : Blo 519798 1484381 := bstep (se 3 (by rfl) ⟨278321, by rfl⟩ : syracuseStep 1484381 = 556643) B556643
theorem B894667 : Blo 519798 894667 := bstep (se 1 (by rfl) ⟨671000, by rfl⟩ : syracuseStep 894667 = 1342001) B1342001
theorem B993035 : Blo 519798 993035 := bstep (se 1 (by rfl) ⟨744776, by rfl⟩ : syracuseStep 993035 = 1489553) B1489553
theorem B2828125 : Blo 519798 2828125 := bstep (se 3 (by rfl) ⟨530273, by rfl⟩ : syracuseStep 2828125 = 1060547) B1060547
theorem B1484723 : Blo 519798 1484723 := bstep (se 1 (by rfl) ⟨1113542, by rfl⟩ : syracuseStep 1484723 = 2227085) B2227085
theorem B993217 : Blo 519798 993217 := bstep (se 2 (by rfl) ⟨372456, by rfl⟩ : syracuseStep 993217 = 744913) B744913
theorem B1320907 : Blo 519798 1320907 := bstep (se 1 (by rfl) ⟨990680, by rfl⟩ : syracuseStep 1320907 = 1981361) B1981361
theorem B1255475 : Blo 519798 1255475 := bstep (se 1 (by rfl) ⟨941606, by rfl⟩ : syracuseStep 1255475 = 1883213) B1883213
theorem B1321049 : Blo 519798 1321049 := bstep (se 2 (by rfl) ⟨495393, by rfl⟩ : syracuseStep 1321049 = 990787) B990787
theorem B1976471 : Blo 519798 1976471 := bstep (se 1 (by rfl) ⟨1482353, by rfl⟩ : syracuseStep 1976471 = 2964707) B2964707
theorem B14297239 : Blo 519798 14297239 := bstep (se 1 (by rfl) ⟨10722929, by rfl⟩ : syracuseStep 14297239 = 21445859) B21445859
theorem B15050933 : Blo 519798 15050933 := bstep (se 5 (by rfl) ⟨705512, by rfl⟩ : syracuseStep 15050933 = 1411025) B1411025
theorem B993559 : Blo 519798 993559 := bstep (se 1 (by rfl) ⟨745169, by rfl⟩ : syracuseStep 993559 = 1490339) B1490339
theorem B3352877 : Blo 519798 3352877 := bstep (se 3 (by rfl) ⟨628664, by rfl⟩ : syracuseStep 3352877 = 1257329) B1257329
theorem B1583425 : Blo 519798 1583425 := bstep (se 2 (by rfl) ⟨593784, by rfl⟩ : syracuseStep 1583425 = 1187569) B1187569
theorem B7547201 : Blo 519798 7547201 := bstep (se 2 (by rfl) ⟨2830200, by rfl⟩ : syracuseStep 7547201 = 5660401) B5660401
theorem B1976669 : Blo 519798 1976669 := bstep (se 3 (by rfl) ⟨370625, by rfl⟩ : syracuseStep 1976669 = 741251) B741251
theorem B993779 : Blo 519798 993779 := bstep (se 1 (by rfl) ⟨745334, by rfl⟩ : syracuseStep 993779 = 1490669) B1490669
theorem B928279 : Blo 519798 928279 := bstep (se 1 (by rfl) ⟨696209, by rfl⟩ : syracuseStep 928279 = 1392419) B1392419
theorem B12036701 : Blo 519798 12036701 := bstep (se 3 (by rfl) ⟨2256881, by rfl⟩ : syracuseStep 12036701 = 4513763) B4513763
theorem B994007 : Blo 519798 994007 := bstep (se 1 (by rfl) ⟨745505, by rfl⟩ : syracuseStep 994007 = 1491011) B1491011
theorem B764759 : Blo 519798 764759 := bstep (se 1 (by rfl) ⟨573569, by rfl⟩ : syracuseStep 764759 = 1147139) B1147139
theorem B1321879 : Blo 519798 1321879 := bstep (se 1 (by rfl) ⟨991409, by rfl⟩ : syracuseStep 1321879 = 1982819) B1982819
theorem B1190873 : Blo 519798 1190873 := bstep (se 2 (by rfl) ⟨446577, by rfl⟩ : syracuseStep 1190873 = 893155) B893155
theorem B994265 : Blo 519798 994265 := bstep (se 2 (by rfl) ⟨372849, by rfl⟩ : syracuseStep 994265 = 745699) B745699
theorem B1584203 : Blo 519798 1584203 := bstep (se 1 (by rfl) ⟨1188152, by rfl⟩ : syracuseStep 1584203 = 2376305) B2376305
theorem B1322315 : Blo 519798 1322315 := bstep (se 1 (by rfl) ⟨991736, by rfl⟩ : syracuseStep 1322315 = 1983473) B1983473
theorem B1781299 : Blo 519798 1781299 := bstep (se 1 (by rfl) ⟨1335974, by rfl⟩ : syracuseStep 1781299 = 2671949) B2671949
theorem B2633309 : Blo 519798 2633309 := bstep (se 3 (by rfl) ⟨493745, by rfl⟩ : syracuseStep 2633309 = 987491) B987491
theorem B1322689 : Blo 519798 1322689 := bstep (se 2 (by rfl) ⟨496008, by rfl⟩ : syracuseStep 1322689 = 992017) B992017
theorem B6762341 : Blo 519798 6762341 := bstep (se 4 (by rfl) ⟨633969, by rfl⟩ : syracuseStep 6762341 = 1267939) B1267939
theorem B3747971 : Blo 519798 3747971 := bstep (se 1 (by rfl) ⟨2810978, by rfl⟩ : syracuseStep 3747971 = 5621957) B5621957
theorem B2371787 : Blo 519798 2371787 := bstep (se 1 (by rfl) ⟨1778840, by rfl⟩ : syracuseStep 2371787 = 3557681) B3557681
theorem B1487069 : Blo 519798 1487069 := bstep (se 3 (by rfl) ⟨278825, by rfl⟩ : syracuseStep 1487069 = 557651) B557651
theorem B1978627 : Blo 519798 1978627 := bstep (se 1 (by rfl) ⟨1483970, by rfl⟩ : syracuseStep 1978627 = 2967941) B2967941
theorem B1061131 : Blo 519798 1061131 := bstep (se 1 (by rfl) ⟨795848, by rfl⟩ : syracuseStep 1061131 = 1591697) B1591697
theorem B1323287 : Blo 519798 1323287 := bstep (se 1 (by rfl) ⟨992465, by rfl⟩ : syracuseStep 1323287 = 1984931) B1984931
theorem B1487297 : Blo 519798 1487297 := bstep (se 2 (by rfl) ⟨557736, by rfl⟩ : syracuseStep 1487297 = 1115473) B1115473
theorem B1978931 : Blo 519798 1978931 := bstep (se 1 (by rfl) ⟨1484198, by rfl⟩ : syracuseStep 1978931 = 2968397) B2968397
theorem B1487639 : Blo 519798 1487639 := bstep (se 1 (by rfl) ⟨1115729, by rfl⟩ : syracuseStep 1487639 = 2231459) B2231459
theorem B4469681 : Blo 519798 4469681 := bstep (se 2 (by rfl) ⟨1676130, by rfl⟩ : syracuseStep 4469681 = 3352261) B3352261
theorem B1881035 : Blo 519798 1881035 := bstep (se 1 (by rfl) ⟨1410776, by rfl⟩ : syracuseStep 1881035 = 2821553) B2821553
theorem B7549969 : Blo 519798 7549969 := bstep (se 2 (by rfl) ⟨2831238, by rfl⟩ : syracuseStep 7549969 = 5662477) B5662477
theorem B1324097 : Blo 519798 1324097 := bstep (se 2 (by rfl) ⟨496536, by rfl⟩ : syracuseStep 1324097 = 993073) B993073
theorem B1979585 : Blo 519798 1979585 := bstep (se 2 (by rfl) ⟨742344, by rfl⟩ : syracuseStep 1979585 = 1484689) B1484689
theorem B1324633 : Blo 519798 1324633 := bstep (se 2 (by rfl) ⟨496737, by rfl⟩ : syracuseStep 1324633 = 993475) B993475
theorem B2635415 : Blo 519798 2635415 := bstep (se 1 (by rfl) ⟨1976561, by rfl⟩ : syracuseStep 2635415 = 3953123) B3953123
theorem B604139 : Blo 519798 604139 := bstep (se 1 (by rfl) ⟨453104, by rfl⟩ : syracuseStep 604139 = 906209) B906209
theorem B702859 : Blo 519798 702859 := bstep (se 1 (by rfl) ⟨527144, by rfl⟩ : syracuseStep 702859 = 1054289) B1054289
theorem B1030553 : Blo 519798 1030553 := bstep (se 2 (by rfl) ⟨386457, by rfl⟩ : syracuseStep 1030553 = 772915) B772915
theorem B1980845 : Blo 519798 1980845 := bstep (se 3 (by rfl) ⟨371408, by rfl⟩ : syracuseStep 1980845 = 742817) B742817
theorem B702923 : Blo 519798 702923 := bstep (se 1 (by rfl) ⟨527192, by rfl⟩ : syracuseStep 702923 = 1054385) B1054385
theorem B1980875 : Blo 519798 1980875 := bstep (se 1 (by rfl) ⟨1485656, by rfl⟩ : syracuseStep 1980875 = 2971313) B2971313
theorem B1325747 : Blo 519798 1325747 := bstep (se 1 (by rfl) ⟨994310, by rfl⟩ : syracuseStep 1325747 = 1988621) B1988621
theorem B1129153 : Blo 519798 1129153 := bstep (se 2 (by rfl) ⟨423432, by rfl⟩ : syracuseStep 1129153 = 846865) B846865
theorem B6339545 : Blo 519798 6339545 := bstep (se 2 (by rfl) ⟨2377329, by rfl⟩ : syracuseStep 6339545 = 4754659) B4754659
theorem B1489985 : Blo 519798 1489985 := bstep (se 2 (by rfl) ⟨558744, by rfl⟩ : syracuseStep 1489985 = 1117489) B1117489
theorem B1981529 : Blo 519798 1981529 := bstep (se 2 (by rfl) ⟨743073, by rfl⟩ : syracuseStep 1981529 = 1486147) B1486147
theorem B1981847 : Blo 519798 1981847 := bstep (se 1 (by rfl) ⟨1486385, by rfl⟩ : syracuseStep 1981847 = 2972771) B2972771
theorem B1490521 : Blo 519798 1490521 := bstep (se 2 (by rfl) ⟨558945, by rfl⟩ : syracuseStep 1490521 = 1117891) B1117891
theorem B7519985 : Blo 519798 7519985 := bstep (se 2 (by rfl) ⟨2819994, by rfl⟩ : syracuseStep 7519985 = 5639989) B5639989
theorem B5947181 : Blo 519798 5947181 := bstep (se 3 (by rfl) ⟨1115096, by rfl⟩ : syracuseStep 5947181 = 2230193) B2230193
theorem B1982515 : Blo 519798 1982515 := bstep (se 1 (by rfl) ⟨1486886, by rfl⟩ : syracuseStep 1982515 = 2973773) B2973773
theorem B3948749 : Blo 519798 3948749 := bstep (se 3 (by rfl) ⟨740390, by rfl⟩ : syracuseStep 3948749 = 1480781) B1480781
theorem B4473305 : Blo 519798 4473305 := bstep (se 2 (by rfl) ⟨1677489, by rfl⟩ : syracuseStep 4473305 = 3354979) B3354979
theorem B2114221 : Blo 519798 2114221 := bstep (se 3 (by rfl) ⟨396416, by rfl⟩ : syracuseStep 2114221 = 792833) B792833
theorem B3949235 : Blo 519798 3949235 := bstep (se 1 (by rfl) ⟨2961926, by rfl⟩ : syracuseStep 3949235 = 5923853) B5923853
theorem B5653313 : Blo 519798 5653313 := bstep (se 2 (by rfl) ⟨2119992, by rfl⟩ : syracuseStep 5653313 = 4239985) B4239985
theorem B1885187 : Blo 519798 1885187 := bstep (se 1 (by rfl) ⟨1413890, by rfl⟩ : syracuseStep 1885187 = 2827781) B2827781
theorem B2638979 : Blo 519798 2638979 := bstep (se 1 (by rfl) ⟨1979234, by rfl⟩ : syracuseStep 2638979 = 3958469) B3958469
theorem B1983761 : Blo 519798 1983761 := bstep (se 2 (by rfl) ⟨743910, by rfl⟩ : syracuseStep 1983761 = 1487821) B1487821
theorem B836887 : Blo 519798 836887 := bstep (se 1 (by rfl) ⟨627665, by rfl⟩ : syracuseStep 836887 = 1255331) B1255331
theorem B4015565 : Blo 519798 4015565 := bstep (se 3 (by rfl) ⟨752918, by rfl⟩ : syracuseStep 4015565 = 1505837) B1505837
theorem B1590749 : Blo 519798 1590749 := bstep (se 3 (by rfl) ⟨298265, by rfl⟩ : syracuseStep 1590749 = 596531) B596531
theorem B837143 : Blo 519798 837143 := bstep (se 1 (by rfl) ⟨627857, by rfl⟩ : syracuseStep 837143 = 1255715) B1255715
theorem B1754675 : Blo 519798 1754675 := bstep (se 1 (by rfl) ⟨1316006, by rfl⟩ : syracuseStep 1754675 = 2632013) B2632013
theorem B2967191 : Blo 519798 2967191 := bstep (se 1 (by rfl) ⟨2225393, by rfl⟩ : syracuseStep 2967191 = 4450787) B4450787
theorem B1754945 : Blo 519798 1754945 := bstep (se 2 (by rfl) ⟨658104, by rfl⟩ : syracuseStep 1754945 = 1316209) B1316209
theorem B2377603 : Blo 519798 2377603 := bstep (se 1 (by rfl) ⟨1783202, by rfl⟩ : syracuseStep 2377603 = 3566405) B3566405
theorem B837515 : Blo 519798 837515 := bstep (se 1 (by rfl) ⟨628136, by rfl⟩ : syracuseStep 837515 = 1256273) B1256273
theorem B1984459 : Blo 519798 1984459 := bstep (se 1 (by rfl) ⟨1488344, by rfl⟩ : syracuseStep 1984459 = 2976689) B2976689
theorem B9062435 : Blo 519798 9062435 := bstep (se 1 (by rfl) ⟨6796826, by rfl⟩ : syracuseStep 9062435 = 13593653) B13593653
theorem B2508893 : Blo 519798 2508893 := bstep (se 3 (by rfl) ⟨470417, by rfl⟩ : syracuseStep 2508893 = 940835) B940835
theorem B3950693 : Blo 519798 3950693 := bstep (se 4 (by rfl) ⟨370377, by rfl⟩ : syracuseStep 3950693 = 740755) B740755
theorem B1886339 : Blo 519798 1886339 := bstep (se 1 (by rfl) ⟨1414754, by rfl⟩ : syracuseStep 1886339 = 2829509) B2829509
theorem B1689751 : Blo 519798 1689751 := bstep (se 1 (by rfl) ⟨1267313, by rfl⟩ : syracuseStep 1689751 = 2534627) B2534627
theorem B1984733 : Blo 519798 1984733 := bstep (se 3 (by rfl) ⟨372137, by rfl⟩ : syracuseStep 1984733 = 744275) B744275
theorem B1755485 : Blo 519798 1755485 := bstep (se 3 (by rfl) ⟨329153, by rfl⟩ : syracuseStep 1755485 = 658307) B658307
theorem B3754457 : Blo 519798 3754457 := bstep (se 2 (by rfl) ⟨1407921, by rfl⟩ : syracuseStep 3754457 = 2815843) B2815843
theorem B1886743 : Blo 519798 1886743 := bstep (se 1 (by rfl) ⟨1415057, by rfl⟩ : syracuseStep 1886743 = 2830115) B2830115
theorem B3951179 : Blo 519798 3951179 := bstep (se 1 (by rfl) ⟨2963384, by rfl⟩ : syracuseStep 3951179 = 5926769) B5926769
theorem B936769 : Blo 519798 936769 := bstep (se 2 (by rfl) ⟨351288, by rfl⟩ : syracuseStep 936769 = 702577) B702577
theorem B1985431 : Blo 519798 1985431 := bstep (se 1 (by rfl) ⟨1489073, by rfl⟩ : syracuseStep 1985431 = 2978147) B2978147
theorem B805913 : Blo 519798 805913 := bstep (se 2 (by rfl) ⟨302217, by rfl⟩ : syracuseStep 805913 = 604435) B604435
theorem B838937 : Blo 519798 838937 := bstep (se 2 (by rfl) ⟨314601, by rfl⟩ : syracuseStep 838937 = 629203) B629203
theorem B4443437 : Blo 519798 4443437 := bstep (se 3 (by rfl) ⟨833144, by rfl⟩ : syracuseStep 4443437 = 1666289) B1666289
theorem B6671717 : Blo 519798 6671717 := bstep (se 4 (by rfl) ⟨625473, by rfl⟩ : syracuseStep 6671717 = 1250947) B1250947
theorem B1756619 : Blo 519798 1756619 := bstep (se 1 (by rfl) ⟨1317464, by rfl⟩ : syracuseStep 1756619 = 2634929) B2634929
theorem B1986221 : Blo 519798 1986221 := bstep (se 3 (by rfl) ⟨372416, by rfl⟩ : syracuseStep 1986221 = 744833) B744833
theorem B1756889 : Blo 519798 1756889 := bstep (se 2 (by rfl) ⟨658833, by rfl⟩ : syracuseStep 1756889 = 1317667) B1317667
theorem B3821347 : Blo 519798 3821347 := bstep (se 1 (by rfl) ⟨2866010, by rfl⟩ : syracuseStep 3821347 = 5732021) B5732021
theorem B2511121 : Blo 519798 2511121 := bstep (se 2 (by rfl) ⟨941670, by rfl⟩ : syracuseStep 2511121 = 1883341) B1883341
theorem B2117981 : Blo 519798 2117981 := bstep (se 3 (by rfl) ⟨397121, by rfl⟩ : syracuseStep 2117981 = 794243) B794243
theorem B1757591 : Blo 519798 1757591 := bstep (se 1 (by rfl) ⟨1318193, by rfl⟩ : syracuseStep 1757591 = 2636387) B2636387
theorem B14471885 : Blo 519798 14471885 := bstep (se 3 (by rfl) ⟨2713478, by rfl⟩ : syracuseStep 14471885 = 5426957) B5426957
theorem B2642705 : Blo 519798 2642705 := bstep (se 2 (by rfl) ⟨991014, by rfl⟩ : syracuseStep 2642705 = 1982029) B1982029
theorem B24171317 : Blo 519798 24171317 := bstep (se 5 (by rfl) ⟨1133030, by rfl⟩ : syracuseStep 24171317 = 2266061) B2266061
theorem B1758131 : Blo 519798 1758131 := bstep (se 1 (by rfl) ⟨1318598, by rfl⟩ : syracuseStep 1758131 = 2637197) B2637197
theorem B2642867 : Blo 519798 2642867 := bstep (se 1 (by rfl) ⟨1982150, by rfl⟩ : syracuseStep 2642867 = 3964301) B3964301
theorem B1987649 : Blo 519798 1987649 := bstep (se 2 (by rfl) ⟨745368, by rfl⟩ : syracuseStep 1987649 = 1490737) B1490737
theorem B1758401 : Blo 519798 1758401 := bstep (se 2 (by rfl) ⟨659400, by rfl⟩ : syracuseStep 1758401 = 1318801) B1318801
theorem B939479 : Blo 519798 939479 := bstep (se 1 (by rfl) ⟨704609, by rfl⟩ : syracuseStep 939479 = 1409219) B1409219
theorem B3823109 : Blo 519798 3823109 := bstep (se 4 (by rfl) ⟨358416, by rfl⟩ : syracuseStep 3823109 = 716833) B716833
theorem B939595 : Blo 519798 939595 := bstep (se 1 (by rfl) ⟨704696, by rfl⟩ : syracuseStep 939595 = 1409393) B1409393
theorem B3757661 : Blo 519798 3757661 := bstep (se 3 (by rfl) ⟨704561, by rfl⟩ : syracuseStep 3757661 = 1409123) B1409123
theorem B3757745 : Blo 519798 3757745 := bstep (se 2 (by rfl) ⟨1409154, by rfl⟩ : syracuseStep 3757745 = 2818309) B2818309
theorem B1758941 : Blo 519798 1758941 := bstep (se 3 (by rfl) ⟨329801, by rfl⟩ : syracuseStep 1758941 = 659603) B659603
theorem B34363237 : Blo 519798 34363237 := bstep (se 4 (by rfl) ⟨3221553, by rfl⟩ : syracuseStep 34363237 = 6443107) B6443107
theorem B940171 : Blo 519798 940171 := bstep (se 1 (by rfl) ⟨705128, by rfl⟩ : syracuseStep 940171 = 1410257) B1410257
theorem B743575 : Blo 519798 743575 := bstep (se 1 (by rfl) ⟨557681, by rfl⟩ : syracuseStep 743575 = 1115363) B1115363
theorem B4446413 : Blo 519798 4446413 := bstep (se 3 (by rfl) ⟨833702, by rfl⟩ : syracuseStep 4446413 = 1667405) B1667405
theorem B1169675 : Blo 519798 1169675 := bstep (se 1 (by rfl) ⟨877256, by rfl⟩ : syracuseStep 1169675 = 1754513) B1754513
theorem B2513197 : Blo 519798 2513197 := bstep (se 3 (by rfl) ⟨471224, by rfl⟩ : syracuseStep 2513197 = 942449) B942449
theorem B1169729 : Blo 519798 1169729 := bstep (se 2 (by rfl) ⟨438648, by rfl⟩ : syracuseStep 1169729 = 877297) B877297
theorem B2971997 : Blo 519798 2971997 := bstep (se 3 (by rfl) ⟨557249, by rfl⟩ : syracuseStep 2971997 = 1114499) B1114499
theorem B11295125 : Blo 519798 11295125 := bstep (se 6 (by rfl) ⟨264729, by rfl⟩ : syracuseStep 11295125 = 529459) B529459
theorem B1399319 : Blo 519798 1399319 := bstep (se 1 (by rfl) ⟨1049489, by rfl⟩ : syracuseStep 1399319 = 2098979) B2098979
theorem B1169945 : Blo 519798 1169945 := bstep (se 2 (by rfl) ⟨438729, by rfl⟩ : syracuseStep 1169945 = 877459) B877459
theorem B1170035 : Blo 519798 1170035 := bstep (se 1 (by rfl) ⟨877526, by rfl⟩ : syracuseStep 1170035 = 1755053) B1755053
theorem B1170071 : Blo 519798 1170071 := bstep (se 1 (by rfl) ⟨877553, by rfl⟩ : syracuseStep 1170071 = 1755107) B1755107
theorem B1170251 : Blo 519798 1170251 := bstep (se 1 (by rfl) ⟨877688, by rfl⟩ : syracuseStep 1170251 = 1755377) B1755377
theorem B1760075 : Blo 519798 1760075 := bstep (se 1 (by rfl) ⟨1320056, by rfl⟩ : syracuseStep 1760075 = 2640113) B2640113
theorem B2644811 : Blo 519798 2644811 := bstep (se 1 (by rfl) ⟨1983608, by rfl⟩ : syracuseStep 2644811 = 3967217) B3967217
theorem B1170305 : Blo 519798 1170305 := bstep (se 2 (by rfl) ⟨438864, by rfl⟩ : syracuseStep 1170305 = 877729) B877729
theorem B940979 : Blo 519798 940979 := bstep (se 1 (by rfl) ⟨705734, by rfl⟩ : syracuseStep 940979 = 1411469) B1411469
theorem B1170521 : Blo 519798 1170521 := bstep (se 2 (by rfl) ⟨438945, by rfl⟩ : syracuseStep 1170521 = 877891) B877891
theorem B1760345 : Blo 519798 1760345 := bstep (se 2 (by rfl) ⟨660129, by rfl⟩ : syracuseStep 1760345 = 1320259) B1320259
theorem B1170611 : Blo 519798 1170611 := bstep (se 1 (by rfl) ⟨877958, by rfl⟩ : syracuseStep 1170611 = 1755917) B1755917
theorem B1170647 : Blo 519798 1170647 := bstep (se 1 (by rfl) ⟨877985, by rfl⟩ : syracuseStep 1170647 = 1755971) B1755971
theorem B1170827 : Blo 519798 1170827 := bstep (se 1 (by rfl) ⟨878120, by rfl⟩ : syracuseStep 1170827 = 1756241) B1756241
theorem B3857843 : Blo 519798 3857843 := bstep (se 1 (by rfl) ⟨2893382, by rfl⟩ : syracuseStep 3857843 = 5786765) B5786765
theorem B1170881 : Blo 519798 1170881 := bstep (se 2 (by rfl) ⟨439080, by rfl⟩ : syracuseStep 1170881 = 878161) B878161
theorem B7167449 : Blo 519798 7167449 := bstep (se 2 (by rfl) ⟨2687793, by rfl⟩ : syracuseStep 7167449 = 5375587) B5375587
theorem B941555 : Blo 519798 941555 := bstep (se 1 (by rfl) ⟨706166, by rfl⟩ : syracuseStep 941555 = 1412333) B1412333
theorem B3333707 : Blo 519798 3333707 := bstep (se 1 (by rfl) ⟨2500280, by rfl⟩ : syracuseStep 3333707 = 5000561) B5000561
theorem B1171097 : Blo 519798 1171097 := bstep (se 2 (by rfl) ⟨439161, by rfl⟩ : syracuseStep 1171097 = 878323) B878323
theorem B1171187 : Blo 519798 1171187 := bstep (se 1 (by rfl) ⟨878390, by rfl⟩ : syracuseStep 1171187 = 1756781) B1756781
theorem B1171223 : Blo 519798 1171223 := bstep (se 1 (by rfl) ⟨878417, by rfl⟩ : syracuseStep 1171223 = 1756835) B1756835
theorem B1761047 : Blo 519798 1761047 := bstep (se 1 (by rfl) ⟨1320785, by rfl⟩ : syracuseStep 1761047 = 2641571) B2641571
theorem B3956525 : Blo 519798 3956525 := bstep (se 3 (by rfl) ⟨741848, by rfl⟩ : syracuseStep 3956525 = 1483697) B1483697
theorem B19259201 : Blo 519798 19259201 := bstep (se 2 (by rfl) ⟨7222200, by rfl⟩ : syracuseStep 19259201 = 14444401) B14444401
theorem B2383789 : Blo 519798 2383789 := bstep (se 3 (by rfl) ⟨446960, by rfl⟩ : syracuseStep 2383789 = 893921) B893921
theorem B3334067 : Blo 519798 3334067 := bstep (se 1 (by rfl) ⟨2500550, by rfl⟩ : syracuseStep 3334067 = 5001101) B5001101
theorem B1171403 : Blo 519798 1171403 := bstep (se 1 (by rfl) ⟨878552, by rfl⟩ : syracuseStep 1171403 = 1757105) B1757105
theorem B1171457 : Blo 519798 1171457 := bstep (se 2 (by rfl) ⟨439296, by rfl⟩ : syracuseStep 1171457 = 878593) B878593
theorem B1335361 : Blo 519798 1335361 := bstep (se 2 (by rfl) ⟨500760, by rfl⟩ : syracuseStep 1335361 = 1001521) B1001521
theorem B745625 : Blo 519798 745625 := bstep (se 2 (by rfl) ⟨279609, by rfl⟩ : syracuseStep 745625 = 559219) B559219
theorem B1171673 : Blo 519798 1171673 := bstep (se 2 (by rfl) ⟨439377, by rfl⟩ : syracuseStep 1171673 = 878755) B878755
theorem B1171763 : Blo 519798 1171763 := bstep (se 1 (by rfl) ⟨878822, by rfl⟩ : syracuseStep 1171763 = 1757645) B1757645
theorem B1761587 : Blo 519798 1761587 := bstep (se 1 (by rfl) ⟨1321190, by rfl⟩ : syracuseStep 1761587 = 2642381) B2642381
theorem B5005633 : Blo 519798 5005633 := bstep (se 2 (by rfl) ⟨1877112, by rfl⟩ : syracuseStep 5005633 = 3754225) B3754225
theorem B1171799 : Blo 519798 1171799 := bstep (se 1 (by rfl) ⟨878849, by rfl⟩ : syracuseStep 1171799 = 1757699) B1757699
theorem B1171979 : Blo 519798 1171979 := bstep (se 1 (by rfl) ⟨878984, by rfl⟩ : syracuseStep 1171979 = 1757969) B1757969
theorem B2384407 : Blo 519798 2384407 := bstep (se 1 (by rfl) ⟨1788305, by rfl⟩ : syracuseStep 2384407 = 3576611) B3576611
theorem B1172033 : Blo 519798 1172033 := bstep (se 2 (by rfl) ⟨439512, by rfl⟩ : syracuseStep 1172033 = 879025) B879025
theorem B1761857 : Blo 519798 1761857 := bstep (se 2 (by rfl) ⟨660696, by rfl⟩ : syracuseStep 1761857 = 1321393) B1321393
theorem B2646593 : Blo 519798 2646593 := bstep (se 2 (by rfl) ⟨992472, by rfl⟩ : syracuseStep 2646593 = 1984945) B1984945
theorem B1958489 : Blo 519798 1958489 := bstep (se 2 (by rfl) ⟨734433, by rfl⟩ : syracuseStep 1958489 = 1468867) B1468867
theorem B2220695 : Blo 519798 2220695 := bstep (se 1 (by rfl) ⟨1665521, by rfl⟩ : syracuseStep 2220695 = 3331043) B3331043
theorem B2974481 : Blo 519798 2974481 := bstep (se 2 (by rfl) ⟨1115430, by rfl⟩ : syracuseStep 2974481 = 2230861) B2230861
theorem B1172249 : Blo 519798 1172249 := bstep (se 2 (by rfl) ⟨439593, by rfl⟩ : syracuseStep 1172249 = 879187) B879187
theorem B2810699 : Blo 519798 2810699 := bstep (se 1 (by rfl) ⟨2108024, by rfl⟩ : syracuseStep 2810699 = 4216049) B4216049
theorem B1172339 : Blo 519798 1172339 := bstep (se 1 (by rfl) ⟨879254, by rfl⟩ : syracuseStep 1172339 = 1758509) B1758509
theorem B1172375 : Blo 519798 1172375 := bstep (se 1 (by rfl) ⟨879281, by rfl⟩ : syracuseStep 1172375 = 1758563) B1758563
theorem B1172555 : Blo 519798 1172555 := bstep (se 1 (by rfl) ⟨879416, by rfl⟩ : syracuseStep 1172555 = 1758833) B1758833
theorem B877655 : Blo 519798 877655 := bstep (se 1 (by rfl) ⟨658241, by rfl⟩ : syracuseStep 877655 = 1316483) B1316483
theorem B1762397 : Blo 519798 1762397 := bstep (se 3 (by rfl) ⟨330449, by rfl⟩ : syracuseStep 1762397 = 660899) B660899
theorem B1172609 : Blo 519798 1172609 := bstep (se 2 (by rfl) ⟨439728, by rfl⟩ : syracuseStep 1172609 = 879457) B879457
theorem B1926317 : Blo 519798 1926317 := bstep (se 3 (by rfl) ⟨361184, by rfl⟩ : syracuseStep 1926317 = 722369) B722369
theorem B877783 : Blo 519798 877783 := bstep (se 1 (by rfl) ⟨658337, by rfl⟩ : syracuseStep 877783 = 1316675) B1316675
theorem B1172825 : Blo 519798 1172825 := bstep (se 2 (by rfl) ⟨439809, by rfl⟩ : syracuseStep 1172825 = 879619) B879619
theorem B1172915 : Blo 519798 1172915 := bstep (se 1 (by rfl) ⟨879686, by rfl⟩ : syracuseStep 1172915 = 1759373) B1759373
theorem B779723 : Blo 519798 779723 := bstep (se 1 (by rfl) ⟨584792, by rfl⟩ : syracuseStep 779723 = 1169585) B1169585
theorem B1500619 : Blo 519798 1500619 := bstep (se 1 (by rfl) ⟨1125464, by rfl⟩ : syracuseStep 1500619 = 2250929) B2250929
theorem B779735 : Blo 519798 779735 := bstep (se 1 (by rfl) ⟨584801, by rfl⟩ : syracuseStep 779735 = 1169603) B1169603
theorem B1172951 : Blo 519798 1172951 := bstep (se 1 (by rfl) ⟨879713, by rfl⟩ : syracuseStep 1172951 = 1759427) B1759427
theorem B779801 : Blo 519798 779801 := bstep (se 2 (by rfl) ⟨292425, by rfl⟩ : syracuseStep 779801 = 584851) B584851
theorem B2385539 : Blo 519798 2385539 := bstep (se 1 (by rfl) ⟨1789154, by rfl⟩ : syracuseStep 2385539 = 3578309) B3578309
theorem B779915 : Blo 519798 779915 := bstep (se 1 (by rfl) ⟨584936, by rfl⟩ : syracuseStep 779915 = 1169873) B1169873
theorem B1173131 : Blo 519798 1173131 := bstep (se 1 (by rfl) ⟨879848, by rfl⟩ : syracuseStep 1173131 = 1759697) B1759697
theorem B779927 : Blo 519798 779927 := bstep (se 1 (by rfl) ⟨584945, by rfl⟩ : syracuseStep 779927 = 1169891) B1169891
theorem B1173185 : Blo 519798 1173185 := bstep (se 2 (by rfl) ⟨439944, by rfl⟩ : syracuseStep 1173185 = 879889) B879889
theorem B779993 : Blo 519798 779993 := bstep (se 2 (by rfl) ⟨292497, by rfl⟩ : syracuseStep 779993 = 584995) B584995
theorem B780107 : Blo 519798 780107 := bstep (se 1 (by rfl) ⟨585080, by rfl⟩ : syracuseStep 780107 = 1170161) B1170161
theorem B878411 : Blo 519798 878411 := bstep (se 1 (by rfl) ⟨658808, by rfl⟩ : syracuseStep 878411 = 1317617) B1317617
theorem B780119 : Blo 519798 780119 := bstep (se 1 (by rfl) ⟨585089, by rfl⟩ : syracuseStep 780119 = 1170179) B1170179
theorem B780185 : Blo 519798 780185 := bstep (se 2 (by rfl) ⟨292569, by rfl⟩ : syracuseStep 780185 = 585139) B585139
theorem B1173401 : Blo 519798 1173401 := bstep (se 2 (by rfl) ⟨440025, by rfl⟩ : syracuseStep 1173401 = 880051) B880051
theorem B878539 : Blo 519798 878539 := bstep (se 1 (by rfl) ⟨658904, by rfl⟩ : syracuseStep 878539 = 1317809) B1317809
theorem B1173491 : Blo 519798 1173491 := bstep (se 1 (by rfl) ⟨880118, by rfl⟩ : syracuseStep 1173491 = 1760237) B1760237
theorem B780299 : Blo 519798 780299 := bstep (se 1 (by rfl) ⟨585224, by rfl⟩ : syracuseStep 780299 = 1170449) B1170449
theorem B780311 : Blo 519798 780311 := bstep (se 1 (by rfl) ⟨585233, by rfl⟩ : syracuseStep 780311 = 1170467) B1170467
theorem B1173527 : Blo 519798 1173527 := bstep (se 1 (by rfl) ⟨880145, by rfl⟩ : syracuseStep 1173527 = 1760291) B1760291
theorem B780377 : Blo 519798 780377 := bstep (se 2 (by rfl) ⟨292641, by rfl⟩ : syracuseStep 780377 = 585283) B585283
theorem B878681 : Blo 519798 878681 := bstep (se 2 (by rfl) ⟨329505, by rfl⟩ : syracuseStep 878681 = 659011) B659011
theorem B780491 : Blo 519798 780491 := bstep (se 1 (by rfl) ⟨585368, by rfl⟩ : syracuseStep 780491 = 1170737) B1170737
theorem B1173707 : Blo 519798 1173707 := bstep (se 1 (by rfl) ⟨880280, by rfl⟩ : syracuseStep 1173707 = 1760561) B1760561
theorem B1763531 : Blo 519798 1763531 := bstep (se 1 (by rfl) ⟨1322648, by rfl⟩ : syracuseStep 1763531 = 2645297) B2645297
theorem B780503 : Blo 519798 780503 := bstep (se 1 (by rfl) ⟨585377, by rfl⟩ : syracuseStep 780503 = 1170755) B1170755
theorem B878809 : Blo 519798 878809 := bstep (se 2 (by rfl) ⟨329553, by rfl⟩ : syracuseStep 878809 = 659107) B659107
theorem B1173761 : Blo 519798 1173761 := bstep (se 2 (by rfl) ⟨440160, by rfl⟩ : syracuseStep 1173761 = 880321) B880321
theorem B780569 : Blo 519798 780569 := bstep (se 2 (by rfl) ⟨292713, by rfl⟩ : syracuseStep 780569 = 585427) B585427
theorem B2222387 : Blo 519798 2222387 := bstep (se 1 (by rfl) ⟨1666790, by rfl⟩ : syracuseStep 2222387 = 3333581) B3333581
theorem B1665355 : Blo 519798 1665355 := bstep (se 1 (by rfl) ⟨1249016, by rfl⟩ : syracuseStep 1665355 = 2498033) B2498033
theorem B780683 : Blo 519798 780683 := bstep (se 1 (by rfl) ⟨585512, by rfl⟩ : syracuseStep 780683 = 1171025) B1171025
theorem B780695 : Blo 519798 780695 := bstep (se 1 (by rfl) ⟨585521, by rfl⟩ : syracuseStep 780695 = 1171043) B1171043
theorem B780761 : Blo 519798 780761 := bstep (se 2 (by rfl) ⟨292785, by rfl⟩ : syracuseStep 780761 = 585571) B585571
theorem B1173977 : Blo 519798 1173977 := bstep (se 2 (by rfl) ⟨440241, by rfl⟩ : syracuseStep 1173977 = 880483) B880483
theorem B1763801 : Blo 519798 1763801 := bstep (se 2 (by rfl) ⟨661425, by rfl⟩ : syracuseStep 1763801 = 1322851) B1322851
theorem B2648537 : Blo 519798 2648537 := bstep (se 2 (by rfl) ⟨993201, by rfl⟩ : syracuseStep 2648537 = 1986403) B1986403
theorem B1174067 : Blo 519798 1174067 := bstep (se 1 (by rfl) ⟨880550, by rfl⟩ : syracuseStep 1174067 = 1761101) B1761101
theorem B780875 : Blo 519798 780875 := bstep (se 1 (by rfl) ⟨585656, by rfl⟩ : syracuseStep 780875 = 1171313) B1171313
theorem B780887 : Blo 519798 780887 := bstep (se 1 (by rfl) ⟨585665, by rfl⟩ : syracuseStep 780887 = 1171331) B1171331
theorem B1174103 : Blo 519798 1174103 := bstep (se 1 (by rfl) ⟨880577, by rfl⟩ : syracuseStep 1174103 = 1761155) B1761155
theorem B780953 : Blo 519798 780953 := bstep (se 2 (by rfl) ⟨292857, by rfl⟩ : syracuseStep 780953 = 585715) B585715
theorem B1338059 : Blo 519798 1338059 := bstep (se 1 (by rfl) ⟨1003544, by rfl⟩ : syracuseStep 1338059 = 2007089) B2007089
theorem B781067 : Blo 519798 781067 := bstep (se 1 (by rfl) ⟨585800, by rfl⟩ : syracuseStep 781067 = 1171601) B1171601
theorem B1174283 : Blo 519798 1174283 := bstep (se 1 (by rfl) ⟨880712, by rfl⟩ : syracuseStep 1174283 = 1761425) B1761425
theorem B781079 : Blo 519798 781079 := bstep (se 1 (by rfl) ⟨585809, by rfl⟩ : syracuseStep 781079 = 1171619) B1171619
theorem B879383 : Blo 519798 879383 := bstep (se 1 (by rfl) ⟨659537, by rfl⟩ : syracuseStep 879383 = 1319075) B1319075
theorem B1174337 : Blo 519798 1174337 := bstep (se 2 (by rfl) ⟨440376, by rfl⟩ : syracuseStep 1174337 = 880753) B880753
theorem B781145 : Blo 519798 781145 := bstep (se 2 (by rfl) ⟨292929, by rfl⟩ : syracuseStep 781145 = 585859) B585859
theorem B879511 : Blo 519798 879511 := bstep (se 1 (by rfl) ⟨659633, by rfl⟩ : syracuseStep 879511 = 1319267) B1319267
theorem B1665971 : Blo 519798 1665971 := bstep (se 1 (by rfl) ⟨1249478, by rfl⟩ : syracuseStep 1665971 = 2498957) B2498957
theorem B781259 : Blo 519798 781259 := bstep (se 1 (by rfl) ⟨585944, by rfl⟩ : syracuseStep 781259 = 1171889) B1171889
theorem B781271 : Blo 519798 781271 := bstep (se 1 (by rfl) ⟨585953, by rfl⟩ : syracuseStep 781271 = 1171907) B1171907
theorem B781337 : Blo 519798 781337 := bstep (se 2 (by rfl) ⟨293001, by rfl⟩ : syracuseStep 781337 = 586003) B586003
theorem B1174553 : Blo 519798 1174553 := bstep (se 2 (by rfl) ⟨440457, by rfl⟩ : syracuseStep 1174553 = 880915) B880915
theorem B584779 : Blo 519798 584779 := bstep (se 1 (by rfl) ⟨438584, by rfl⟩ : syracuseStep 584779 = 877169) B877169
theorem B1174643 : Blo 519798 1174643 := bstep (se 1 (by rfl) ⟨880982, by rfl⟩ : syracuseStep 1174643 = 1761965) B1761965
theorem B781451 : Blo 519798 781451 := bstep (se 1 (by rfl) ⟨586088, by rfl⟩ : syracuseStep 781451 = 1172177) B1172177
theorem B781463 : Blo 519798 781463 := bstep (se 1 (by rfl) ⟨586097, by rfl⟩ : syracuseStep 781463 = 1172195) B1172195
theorem B1174679 : Blo 519798 1174679 := bstep (se 1 (by rfl) ⟨881009, by rfl⟩ : syracuseStep 1174679 = 1762019) B1762019
theorem B1764503 : Blo 519798 1764503 := bstep (se 1 (by rfl) ⟨1323377, by rfl⟩ : syracuseStep 1764503 = 2646755) B2646755
theorem B584887 : Blo 519798 584887 := bstep (se 1 (by rfl) ⟨438665, by rfl⟩ : syracuseStep 584887 = 877331) B877331
theorem B781529 : Blo 519798 781529 := bstep (se 2 (by rfl) ⟨293073, by rfl⟩ : syracuseStep 781529 = 586147) B586147
theorem B205090019 : Blo 519798 205090019 := bstep (se 1 (by rfl) ⟨153817514, by rfl⟩ : syracuseStep 205090019 = 307635029) B307635029
theorem B781643 : Blo 519798 781643 := bstep (se 1 (by rfl) ⟨586232, by rfl⟩ : syracuseStep 781643 = 1172465) B1172465
theorem B1174859 : Blo 519798 1174859 := bstep (se 1 (by rfl) ⟨881144, by rfl⟩ : syracuseStep 1174859 = 1762289) B1762289
theorem B781655 : Blo 519798 781655 := bstep (se 1 (by rfl) ⟨586241, by rfl⟩ : syracuseStep 781655 = 1172483) B1172483
theorem B585067 : Blo 519798 585067 := bstep (se 1 (by rfl) ⟨438800, by rfl⟩ : syracuseStep 585067 = 877601) B877601
theorem B1174913 : Blo 519798 1174913 := bstep (se 2 (by rfl) ⟨440592, by rfl⟩ : syracuseStep 1174913 = 881185) B881185
theorem B781721 : Blo 519798 781721 := bstep (se 2 (by rfl) ⟨293145, by rfl⟩ : syracuseStep 781721 = 586291) B586291
theorem B585175 : Blo 519798 585175 := bstep (se 1 (by rfl) ⟨438881, by rfl⟩ : syracuseStep 585175 = 877763) B877763
theorem B781835 : Blo 519798 781835 := bstep (se 1 (by rfl) ⟨586376, by rfl⟩ : syracuseStep 781835 = 1172753) B1172753
theorem B880139 : Blo 519798 880139 := bstep (se 1 (by rfl) ⟨660104, by rfl⟩ : syracuseStep 880139 = 1320209) B1320209
theorem B781847 : Blo 519798 781847 := bstep (se 1 (by rfl) ⟨586385, by rfl⟩ : syracuseStep 781847 = 1172771) B1172771
theorem B1666649 : Blo 519798 1666649 := bstep (se 2 (by rfl) ⟨624993, by rfl⟩ : syracuseStep 1666649 = 1249987) B1249987
theorem B781913 : Blo 519798 781913 := bstep (se 2 (by rfl) ⟨293217, by rfl⟩ : syracuseStep 781913 = 586435) B586435
theorem B1175129 : Blo 519798 1175129 := bstep (se 2 (by rfl) ⟨440673, by rfl⟩ : syracuseStep 1175129 = 881347) B881347
theorem B3960413 : Blo 519798 3960413 := bstep (se 3 (by rfl) ⟨742577, by rfl⟩ : syracuseStep 3960413 = 1485155) B1485155
theorem B519799 : Blo 519798 519799 := bstep (se 1 (by rfl) ⟨389849, by rfl⟩ : syracuseStep 519799 = 779699) B779699
theorem B519819 : Blo 519798 519819 := bstep (se 1 (by rfl) ⟨389864, by rfl⟩ : syracuseStep 519819 = 779729) B779729
theorem B585355 : Blo 519798 585355 := bstep (se 1 (by rfl) ⟨439016, by rfl⟩ : syracuseStep 585355 = 878033) B878033
theorem B880267 : Blo 519798 880267 := bstep (se 1 (by rfl) ⟨660200, by rfl⟩ : syracuseStep 880267 = 1320401) B1320401
theorem B519831 : Blo 519798 519831 := bstep (se 1 (by rfl) ⟨389873, by rfl⟩ : syracuseStep 519831 = 779747) B779747
theorem B519851 : Blo 519798 519851 := bstep (se 1 (by rfl) ⟨389888, by rfl⟩ : syracuseStep 519851 = 779777) B779777
theorem B1175219 : Blo 519798 1175219 := bstep (se 1 (by rfl) ⟨881414, by rfl⟩ : syracuseStep 1175219 = 1762829) B1762829
theorem B1765043 : Blo 519798 1765043 := bstep (se 1 (by rfl) ⟨1323782, by rfl⟩ : syracuseStep 1765043 = 2647565) B2647565
theorem B519863 : Blo 519798 519863 := bstep (se 1 (by rfl) ⟨389897, by rfl⟩ : syracuseStep 519863 = 779795) B779795
theorem B519883 : Blo 519798 519883 := bstep (se 1 (by rfl) ⟨389912, by rfl⟩ : syracuseStep 519883 = 779825) B779825
theorem B782027 : Blo 519798 782027 := bstep (se 1 (by rfl) ⟨586520, by rfl⟩ : syracuseStep 782027 = 1173041) B1173041
theorem B519895 : Blo 519798 519895 := bstep (se 1 (by rfl) ⟨389921, by rfl⟩ : syracuseStep 519895 = 779843) B779843
theorem B782039 : Blo 519798 782039 := bstep (se 1 (by rfl) ⟨586529, by rfl⟩ : syracuseStep 782039 = 1173059) B1173059
theorem B1175255 : Blo 519798 1175255 := bstep (se 1 (by rfl) ⟨881441, by rfl⟩ : syracuseStep 1175255 = 1762883) B1762883
theorem B519915 : Blo 519798 519915 := bstep (se 1 (by rfl) ⟨389936, by rfl⟩ : syracuseStep 519915 = 779873) B779873
theorem B519927 : Blo 519798 519927 := bstep (se 1 (by rfl) ⟨389945, by rfl⟩ : syracuseStep 519927 = 779891) B779891
theorem B585463 : Blo 519798 585463 := bstep (se 1 (by rfl) ⟨439097, by rfl⟩ : syracuseStep 585463 = 878195) B878195
theorem B519947 : Blo 519798 519947 := bstep (se 1 (by rfl) ⟨389960, by rfl⟩ : syracuseStep 519947 = 779921) B779921
theorem B519959 : Blo 519798 519959 := bstep (se 1 (by rfl) ⟨389969, by rfl⟩ : syracuseStep 519959 = 779939) B779939
theorem B782105 : Blo 519798 782105 := bstep (se 2 (by rfl) ⟨293289, by rfl⟩ : syracuseStep 782105 = 586579) B586579
theorem B880409 : Blo 519798 880409 := bstep (se 2 (by rfl) ⟨330153, by rfl⟩ : syracuseStep 880409 = 660307) B660307
theorem B519979 : Blo 519798 519979 := bstep (se 1 (by rfl) ⟨389984, by rfl⟩ : syracuseStep 519979 = 779969) B779969
theorem B519991 : Blo 519798 519991 := bstep (se 1 (by rfl) ⟨389993, by rfl⟩ : syracuseStep 519991 = 779987) B779987
theorem B520011 : Blo 519798 520011 := bstep (se 1 (by rfl) ⟨390008, by rfl⟩ : syracuseStep 520011 = 780017) B780017
theorem B520023 : Blo 519798 520023 := bstep (se 1 (by rfl) ⟨390017, by rfl⟩ : syracuseStep 520023 = 780035) B780035
theorem B520043 : Blo 519798 520043 := bstep (se 1 (by rfl) ⟨390032, by rfl⟩ : syracuseStep 520043 = 780065) B780065
theorem B520055 : Blo 519798 520055 := bstep (se 1 (by rfl) ⟨390041, by rfl⟩ : syracuseStep 520055 = 780083) B780083
theorem B520075 : Blo 519798 520075 := bstep (se 1 (by rfl) ⟨390056, by rfl⟩ : syracuseStep 520075 = 780113) B780113
theorem B782219 : Blo 519798 782219 := bstep (se 1 (by rfl) ⟨586664, by rfl⟩ : syracuseStep 782219 = 1173329) B1173329
theorem B1175435 : Blo 519798 1175435 := bstep (se 1 (by rfl) ⟨881576, by rfl⟩ : syracuseStep 1175435 = 1763153) B1763153
theorem B520087 : Blo 519798 520087 := bstep (se 1 (by rfl) ⟨390065, by rfl⟩ : syracuseStep 520087 = 780131) B780131
theorem B782231 : Blo 519798 782231 := bstep (se 1 (by rfl) ⟨586673, by rfl⟩ : syracuseStep 782231 = 1173347) B1173347
theorem B880537 : Blo 519798 880537 := bstep (se 2 (by rfl) ⟨330201, by rfl⟩ : syracuseStep 880537 = 660403) B660403
theorem B585643 : Blo 519798 585643 := bstep (se 1 (by rfl) ⟨439232, by rfl⟩ : syracuseStep 585643 = 878465) B878465
theorem B520107 : Blo 519798 520107 := bstep (se 1 (by rfl) ⟨390080, by rfl⟩ : syracuseStep 520107 = 780161) B780161
theorem B520119 : Blo 519798 520119 := bstep (se 1 (by rfl) ⟨390089, by rfl⟩ : syracuseStep 520119 = 780179) B780179
theorem B1175489 : Blo 519798 1175489 := bstep (se 2 (by rfl) ⟨440808, by rfl⟩ : syracuseStep 1175489 = 881617) B881617
theorem B1765313 : Blo 519798 1765313 := bstep (se 2 (by rfl) ⟨661992, by rfl⟩ : syracuseStep 1765313 = 1323985) B1323985
theorem B520139 : Blo 519798 520139 := bstep (se 1 (by rfl) ⟨390104, by rfl⟩ : syracuseStep 520139 = 780209) B780209
theorem B520151 : Blo 519798 520151 := bstep (se 1 (by rfl) ⟨390113, by rfl⟩ : syracuseStep 520151 = 780227) B780227
theorem B782297 : Blo 519798 782297 := bstep (se 2 (by rfl) ⟨293361, by rfl⟩ : syracuseStep 782297 = 586723) B586723
theorem B520171 : Blo 519798 520171 := bstep (se 1 (by rfl) ⟨390128, by rfl⟩ : syracuseStep 520171 = 780257) B780257
theorem B520183 : Blo 519798 520183 := bstep (se 1 (by rfl) ⟨390137, by rfl⟩ : syracuseStep 520183 = 780275) B780275
theorem B520203 : Blo 519798 520203 := bstep (se 1 (by rfl) ⟨390152, by rfl⟩ : syracuseStep 520203 = 780305) B780305
theorem B520215 : Blo 519798 520215 := bstep (se 1 (by rfl) ⟨390161, by rfl⟩ : syracuseStep 520215 = 780323) B780323
theorem B585751 : Blo 519798 585751 := bstep (se 1 (by rfl) ⟨439313, by rfl⟩ : syracuseStep 585751 = 878627) B878627
theorem B520235 : Blo 519798 520235 := bstep (se 1 (by rfl) ⟨390176, by rfl⟩ : syracuseStep 520235 = 780353) B780353
theorem B2650157 : Blo 519798 2650157 := bstep (se 3 (by rfl) ⟨496904, by rfl⟩ : syracuseStep 2650157 = 993809) B993809
theorem B520247 : Blo 519798 520247 := bstep (se 1 (by rfl) ⟨390185, by rfl⟩ : syracuseStep 520247 = 780371) B780371
theorem B1142849 : Blo 519798 1142849 := bstep (se 2 (by rfl) ⟨428568, by rfl⟩ : syracuseStep 1142849 = 857137) B857137
theorem B520267 : Blo 519798 520267 := bstep (se 1 (by rfl) ⟨390200, by rfl⟩ : syracuseStep 520267 = 780401) B780401
theorem B782411 : Blo 519798 782411 := bstep (se 1 (by rfl) ⟨586808, by rfl⟩ : syracuseStep 782411 = 1173617) B1173617
theorem B520279 : Blo 519798 520279 := bstep (se 1 (by rfl) ⟨390209, by rfl⟩ : syracuseStep 520279 = 780419) B780419
theorem B782423 : Blo 519798 782423 := bstep (se 1 (by rfl) ⟨586817, by rfl⟩ : syracuseStep 782423 = 1173635) B1173635
theorem B520299 : Blo 519798 520299 := bstep (se 1 (by rfl) ⟨390224, by rfl⟩ : syracuseStep 520299 = 780449) B780449
theorem B520311 : Blo 519798 520311 := bstep (se 1 (by rfl) ⟨390233, by rfl⟩ : syracuseStep 520311 = 780467) B780467
theorem B520331 : Blo 519798 520331 := bstep (se 1 (by rfl) ⟨390248, by rfl⟩ : syracuseStep 520331 = 780497) B780497
theorem B2388113 : Blo 519798 2388113 := bstep (se 2 (by rfl) ⟨895542, by rfl⟩ : syracuseStep 2388113 = 1791085) B1791085
theorem B520343 : Blo 519798 520343 := bstep (se 1 (by rfl) ⟨390257, by rfl⟩ : syracuseStep 520343 = 780515) B780515
theorem B42987671 : Blo 519798 42987671 := bstep (se 1 (by rfl) ⟨32240753, by rfl⟩ : syracuseStep 42987671 = 64481507) B64481507
theorem B782489 : Blo 519798 782489 := bstep (se 2 (by rfl) ⟨293433, by rfl⟩ : syracuseStep 782489 = 586867) B586867
theorem B1175705 : Blo 519798 1175705 := bstep (se 2 (by rfl) ⟨440889, by rfl⟩ : syracuseStep 1175705 = 881779) B881779
theorem B520363 : Blo 519798 520363 := bstep (se 1 (by rfl) ⟨390272, by rfl⟩ : syracuseStep 520363 = 780545) B780545
theorem B520375 : Blo 519798 520375 := bstep (se 1 (by rfl) ⟨390281, by rfl⟩ : syracuseStep 520375 = 780563) B780563
theorem B520395 : Blo 519798 520395 := bstep (se 1 (by rfl) ⟨390296, by rfl⟩ : syracuseStep 520395 = 780593) B780593
theorem B585931 : Blo 519798 585931 := bstep (se 1 (by rfl) ⟨439448, by rfl⟩ : syracuseStep 585931 = 878897) B878897
theorem B520407 : Blo 519798 520407 := bstep (se 1 (by rfl) ⟨390305, by rfl⟩ : syracuseStep 520407 = 780611) B780611
theorem B520427 : Blo 519798 520427 := bstep (se 1 (by rfl) ⟨390320, by rfl⟩ : syracuseStep 520427 = 780641) B780641
theorem B1175795 : Blo 519798 1175795 := bstep (se 1 (by rfl) ⟨881846, by rfl⟩ : syracuseStep 1175795 = 1763693) B1763693
theorem B520439 : Blo 519798 520439 := bstep (se 1 (by rfl) ⟨390329, by rfl⟩ : syracuseStep 520439 = 780659) B780659
theorem B520459 : Blo 519798 520459 := bstep (se 1 (by rfl) ⟨390344, by rfl⟩ : syracuseStep 520459 = 780689) B780689
theorem B782603 : Blo 519798 782603 := bstep (se 1 (by rfl) ⟨586952, by rfl⟩ : syracuseStep 782603 = 1173905) B1173905
theorem B520471 : Blo 519798 520471 := bstep (se 1 (by rfl) ⟨390353, by rfl⟩ : syracuseStep 520471 = 780707) B780707
theorem B782615 : Blo 519798 782615 := bstep (se 1 (by rfl) ⟨586961, by rfl⟩ : syracuseStep 782615 = 1173923) B1173923
theorem B1175831 : Blo 519798 1175831 := bstep (se 1 (by rfl) ⟨881873, by rfl⟩ : syracuseStep 1175831 = 1763747) B1763747
theorem B520491 : Blo 519798 520491 := bstep (se 1 (by rfl) ⟨390368, by rfl⟩ : syracuseStep 520491 = 780737) B780737
theorem B520503 : Blo 519798 520503 := bstep (se 1 (by rfl) ⟨390377, by rfl⟩ : syracuseStep 520503 = 780755) B780755
theorem B586039 : Blo 519798 586039 := bstep (se 1 (by rfl) ⟨439529, by rfl⟩ : syracuseStep 586039 = 879059) B879059
theorem B520523 : Blo 519798 520523 := bstep (se 1 (by rfl) ⟨390392, by rfl⟩ : syracuseStep 520523 = 780785) B780785
theorem B3010891 : Blo 519798 3010891 := bstep (se 1 (by rfl) ⟨2258168, by rfl⟩ : syracuseStep 3010891 = 4516337) B4516337
theorem B520535 : Blo 519798 520535 := bstep (se 1 (by rfl) ⟨390401, by rfl⟩ : syracuseStep 520535 = 780803) B780803
theorem B782681 : Blo 519798 782681 := bstep (se 2 (by rfl) ⟨293505, by rfl⟩ : syracuseStep 782681 = 587011) B587011
theorem B520555 : Blo 519798 520555 := bstep (se 1 (by rfl) ⟨390416, by rfl⟩ : syracuseStep 520555 = 780833) B780833
theorem B520567 : Blo 519798 520567 := bstep (se 1 (by rfl) ⟨390425, by rfl⟩ : syracuseStep 520567 = 780851) B780851
theorem B520587 : Blo 519798 520587 := bstep (se 1 (by rfl) ⟨390440, by rfl⟩ : syracuseStep 520587 = 780881) B780881
theorem B520599 : Blo 519798 520599 := bstep (se 1 (by rfl) ⟨390449, by rfl⟩ : syracuseStep 520599 = 780899) B780899
theorem B520619 : Blo 519798 520619 := bstep (se 1 (by rfl) ⟨390464, by rfl⟩ : syracuseStep 520619 = 780929) B780929
theorem B520631 : Blo 519798 520631 := bstep (se 1 (by rfl) ⟨390473, by rfl⟩ : syracuseStep 520631 = 780947) B780947
theorem B520651 : Blo 519798 520651 := bstep (se 1 (by rfl) ⟨390488, by rfl⟩ : syracuseStep 520651 = 780977) B780977
theorem B782795 : Blo 519798 782795 := bstep (se 1 (by rfl) ⟨587096, by rfl⟩ : syracuseStep 782795 = 1174193) B1174193
theorem B1176011 : Blo 519798 1176011 := bstep (se 1 (by rfl) ⟨882008, by rfl⟩ : syracuseStep 1176011 = 1764017) B1764017
theorem B520663 : Blo 519798 520663 := bstep (se 1 (by rfl) ⟨390497, by rfl⟩ : syracuseStep 520663 = 780995) B780995
theorem B782807 : Blo 519798 782807 := bstep (se 1 (by rfl) ⟨587105, by rfl⟩ : syracuseStep 782807 = 1174211) B1174211
theorem B881111 : Blo 519798 881111 := bstep (se 1 (by rfl) ⟨660833, by rfl⟩ : syracuseStep 881111 = 1321667) B1321667
theorem B1765853 : Blo 519798 1765853 := bstep (se 3 (by rfl) ⟨331097, by rfl⟩ : syracuseStep 1765853 = 662195) B662195
theorem B520683 : Blo 519798 520683 := bstep (se 1 (by rfl) ⟨390512, by rfl⟩ : syracuseStep 520683 = 781025) B781025
theorem B586219 : Blo 519798 586219 := bstep (se 1 (by rfl) ⟨439664, by rfl⟩ : syracuseStep 586219 = 879329) B879329
theorem B520695 : Blo 519798 520695 := bstep (se 1 (by rfl) ⟨390521, by rfl⟩ : syracuseStep 520695 = 781043) B781043
theorem B1176065 : Blo 519798 1176065 := bstep (se 2 (by rfl) ⟨441024, by rfl⟩ : syracuseStep 1176065 = 882049) B882049
theorem B520715 : Blo 519798 520715 := bstep (se 1 (by rfl) ⟨390536, by rfl⟩ : syracuseStep 520715 = 781073) B781073
theorem B520727 : Blo 519798 520727 := bstep (se 1 (by rfl) ⟨390545, by rfl⟩ : syracuseStep 520727 = 781091) B781091
theorem B782873 : Blo 519798 782873 := bstep (se 2 (by rfl) ⟨293577, by rfl⟩ : syracuseStep 782873 = 587155) B587155
theorem B520747 : Blo 519798 520747 := bstep (se 1 (by rfl) ⟨390560, by rfl⟩ : syracuseStep 520747 = 781121) B781121
theorem B520759 : Blo 519798 520759 := bstep (se 1 (by rfl) ⟨390569, by rfl⟩ : syracuseStep 520759 = 781139) B781139
theorem B520779 : Blo 519798 520779 := bstep (se 1 (by rfl) ⟨390584, by rfl⟩ : syracuseStep 520779 = 781169) B781169
theorem B520791 : Blo 519798 520791 := bstep (se 1 (by rfl) ⟨390593, by rfl⟩ : syracuseStep 520791 = 781187) B781187
theorem B586327 : Blo 519798 586327 := bstep (se 1 (by rfl) ⟨439745, by rfl⟩ : syracuseStep 586327 = 879491) B879491
theorem B881239 : Blo 519798 881239 := bstep (se 1 (by rfl) ⟨660929, by rfl⟩ : syracuseStep 881239 = 1321859) B1321859
theorem B520811 : Blo 519798 520811 := bstep (se 1 (by rfl) ⟨390608, by rfl⟩ : syracuseStep 520811 = 781217) B781217
theorem B520823 : Blo 519798 520823 := bstep (se 1 (by rfl) ⟨390617, by rfl⟩ : syracuseStep 520823 = 781235) B781235
theorem B520843 : Blo 519798 520843 := bstep (se 1 (by rfl) ⟨390632, by rfl⟩ : syracuseStep 520843 = 781265) B781265
theorem B782987 : Blo 519798 782987 := bstep (se 1 (by rfl) ⟨587240, by rfl⟩ : syracuseStep 782987 = 1174481) B1174481
theorem B520855 : Blo 519798 520855 := bstep (se 1 (by rfl) ⟨390641, by rfl⟩ : syracuseStep 520855 = 781283) B781283
theorem B782999 : Blo 519798 782999 := bstep (se 1 (by rfl) ⟨587249, by rfl⟩ : syracuseStep 782999 = 1174499) B1174499
theorem B520875 : Blo 519798 520875 := bstep (se 1 (by rfl) ⟨390656, by rfl⟩ : syracuseStep 520875 = 781313) B781313
theorem B520887 : Blo 519798 520887 := bstep (se 1 (by rfl) ⟨390665, by rfl⟩ : syracuseStep 520887 = 781331) B781331
theorem B520907 : Blo 519798 520907 := bstep (se 1 (by rfl) ⟨390680, by rfl⟩ : syracuseStep 520907 = 781361) B781361
theorem B520919 : Blo 519798 520919 := bstep (se 1 (by rfl) ⟨390689, by rfl⟩ : syracuseStep 520919 = 781379) B781379
theorem B783065 : Blo 519798 783065 := bstep (se 2 (by rfl) ⟨293649, by rfl⟩ : syracuseStep 783065 = 587299) B587299
theorem B1176281 : Blo 519798 1176281 := bstep (se 2 (by rfl) ⟨441105, by rfl⟩ : syracuseStep 1176281 = 882211) B882211
theorem B520939 : Blo 519798 520939 := bstep (se 1 (by rfl) ⟨390704, by rfl⟩ : syracuseStep 520939 = 781409) B781409
theorem B520951 : Blo 519798 520951 := bstep (se 1 (by rfl) ⟨390713, by rfl⟩ : syracuseStep 520951 = 781427) B781427
theorem B520971 : Blo 519798 520971 := bstep (se 1 (by rfl) ⟨390728, by rfl⟩ : syracuseStep 520971 = 781457) B781457
theorem B586507 : Blo 519798 586507 := bstep (se 1 (by rfl) ⟨439880, by rfl⟩ : syracuseStep 586507 = 879761) B879761
theorem B520983 : Blo 519798 520983 := bstep (se 1 (by rfl) ⟨390737, by rfl⟩ : syracuseStep 520983 = 781475) B781475
theorem B1110809 : Blo 519798 1110809 := bstep (se 2 (by rfl) ⟨416553, by rfl⟩ : syracuseStep 1110809 = 833107) B833107
theorem B521003 : Blo 519798 521003 := bstep (se 1 (by rfl) ⟨390752, by rfl⟩ : syracuseStep 521003 = 781505) B781505
theorem B1176371 : Blo 519798 1176371 := bstep (se 1 (by rfl) ⟨882278, by rfl⟩ : syracuseStep 1176371 = 1764557) B1764557
theorem B521015 : Blo 519798 521015 := bstep (se 1 (by rfl) ⟨390761, by rfl⟩ : syracuseStep 521015 = 781523) B781523
theorem B521035 : Blo 519798 521035 := bstep (se 1 (by rfl) ⟨390776, by rfl⟩ : syracuseStep 521035 = 781553) B781553
theorem B783179 : Blo 519798 783179 := bstep (se 1 (by rfl) ⟨587384, by rfl⟩ : syracuseStep 783179 = 1174769) B1174769
theorem B521047 : Blo 519798 521047 := bstep (se 1 (by rfl) ⟨390785, by rfl⟩ : syracuseStep 521047 = 781571) B781571
theorem B783191 : Blo 519798 783191 := bstep (se 1 (by rfl) ⟨587393, by rfl⟩ : syracuseStep 783191 = 1174787) B1174787
theorem B1176407 : Blo 519798 1176407 := bstep (se 1 (by rfl) ⟨882305, by rfl⟩ : syracuseStep 1176407 = 1764611) B1764611
theorem B521067 : Blo 519798 521067 := bstep (se 1 (by rfl) ⟨390800, by rfl⟩ : syracuseStep 521067 = 781601) B781601
theorem B521079 : Blo 519798 521079 := bstep (se 1 (by rfl) ⟨390809, by rfl⟩ : syracuseStep 521079 = 781619) B781619
theorem B586615 : Blo 519798 586615 := bstep (se 1 (by rfl) ⟨439961, by rfl⟩ : syracuseStep 586615 = 879923) B879923
theorem B2814851 : Blo 519798 2814851 := bstep (se 1 (by rfl) ⟨2111138, by rfl⟩ : syracuseStep 2814851 = 4222277) B4222277
theorem B3339139 : Blo 519798 3339139 := bstep (se 1 (by rfl) ⟨2504354, by rfl⟩ : syracuseStep 3339139 = 5008709) B5008709
theorem B521099 : Blo 519798 521099 := bstep (se 1 (by rfl) ⟨390824, by rfl⟩ : syracuseStep 521099 = 781649) B781649
theorem B521111 : Blo 519798 521111 := bstep (se 1 (by rfl) ⟨390833, by rfl⟩ : syracuseStep 521111 = 781667) B781667
theorem B783257 : Blo 519798 783257 := bstep (se 2 (by rfl) ⟨293721, by rfl⟩ : syracuseStep 783257 = 587443) B587443
theorem B521131 : Blo 519798 521131 := bstep (se 1 (by rfl) ⟨390848, by rfl⟩ : syracuseStep 521131 = 781697) B781697
theorem B2225069 : Blo 519798 2225069 := bstep (se 3 (by rfl) ⟨417200, by rfl⟩ : syracuseStep 2225069 = 834401) B834401
theorem B521143 : Blo 519798 521143 := bstep (se 1 (by rfl) ⟨390857, by rfl⟩ : syracuseStep 521143 = 781715) B781715
theorem B521163 : Blo 519798 521163 := bstep (se 1 (by rfl) ⟨390872, by rfl⟩ : syracuseStep 521163 = 781745) B781745
theorem B750551 : Blo 519798 750551 := bstep (se 1 (by rfl) ⟨562913, by rfl⟩ : syracuseStep 750551 = 1125827) B1125827
theorem B521175 : Blo 519798 521175 := bstep (se 1 (by rfl) ⟨390881, by rfl⟩ : syracuseStep 521175 = 781763) B781763
theorem B521195 : Blo 519798 521195 := bstep (se 1 (by rfl) ⟨390896, by rfl⟩ : syracuseStep 521195 = 781793) B781793
theorem B521207 : Blo 519798 521207 := bstep (se 1 (by rfl) ⟨390905, by rfl⟩ : syracuseStep 521207 = 781811) B781811
theorem B1176587 : Blo 519798 1176587 := bstep (se 1 (by rfl) ⟨882440, by rfl⟩ : syracuseStep 1176587 = 1764881) B1764881
theorem B521227 : Blo 519798 521227 := bstep (se 1 (by rfl) ⟨390920, by rfl⟩ : syracuseStep 521227 = 781841) B781841
theorem B783371 : Blo 519798 783371 := bstep (se 1 (by rfl) ⟨587528, by rfl⟩ : syracuseStep 783371 = 1175057) B1175057
theorem B8909837 : Blo 519798 8909837 := bstep (se 3 (by rfl) ⟨1670594, by rfl⟩ : syracuseStep 8909837 = 3341189) B3341189
theorem B521239 : Blo 519798 521239 := bstep (se 1 (by rfl) ⟨390929, by rfl⟩ : syracuseStep 521239 = 781859) B781859
theorem B783383 : Blo 519798 783383 := bstep (se 1 (by rfl) ⟨587537, by rfl⟩ : syracuseStep 783383 = 1175075) B1175075
theorem B521259 : Blo 519798 521259 := bstep (se 1 (by rfl) ⟨390944, by rfl⟩ : syracuseStep 521259 = 781889) B781889
theorem B586795 : Blo 519798 586795 := bstep (se 1 (by rfl) ⟨440096, by rfl⟩ : syracuseStep 586795 = 880193) B880193
theorem B521271 : Blo 519798 521271 := bstep (se 1 (by rfl) ⟨390953, by rfl⟩ : syracuseStep 521271 = 781907) B781907
theorem B1176641 : Blo 519798 1176641 := bstep (se 2 (by rfl) ⟨441240, by rfl⟩ : syracuseStep 1176641 = 882481) B882481
theorem B521291 : Blo 519798 521291 := bstep (se 1 (by rfl) ⟨390968, by rfl⟩ : syracuseStep 521291 = 781937) B781937
theorem B521303 : Blo 519798 521303 := bstep (se 1 (by rfl) ⟨390977, by rfl⟩ : syracuseStep 521303 = 781955) B781955
theorem B783449 : Blo 519798 783449 := bstep (se 2 (by rfl) ⟨293793, by rfl⟩ : syracuseStep 783449 = 587587) B587587
theorem B521323 : Blo 519798 521323 := bstep (se 1 (by rfl) ⟨390992, by rfl⟩ : syracuseStep 521323 = 781985) B781985
theorem B521335 : Blo 519798 521335 := bstep (se 1 (by rfl) ⟨391001, by rfl⟩ : syracuseStep 521335 = 782003) B782003
theorem B521355 : Blo 519798 521355 := bstep (se 1 (by rfl) ⟨391016, by rfl⟩ : syracuseStep 521355 = 782033) B782033
theorem B521367 : Blo 519798 521367 := bstep (se 1 (by rfl) ⟨391025, by rfl⟩ : syracuseStep 521367 = 782051) B782051
theorem B586903 : Blo 519798 586903 := bstep (se 1 (by rfl) ⟨440177, by rfl⟩ : syracuseStep 586903 = 880355) B880355
theorem B521387 : Blo 519798 521387 := bstep (se 1 (by rfl) ⟨391040, by rfl⟩ : syracuseStep 521387 = 782081) B782081
theorem B521399 : Blo 519798 521399 := bstep (se 1 (by rfl) ⟨391049, by rfl⟩ : syracuseStep 521399 = 782099) B782099
theorem B1668289 : Blo 519798 1668289 := bstep (se 2 (by rfl) ⟨625608, by rfl⟩ : syracuseStep 1668289 = 1251217) B1251217
theorem B521419 : Blo 519798 521419 := bstep (se 1 (by rfl) ⟨391064, by rfl⟩ : syracuseStep 521419 = 782129) B782129
theorem B783563 : Blo 519798 783563 := bstep (se 1 (by rfl) ⟨587672, by rfl⟩ : syracuseStep 783563 = 1175345) B1175345
theorem B881867 : Blo 519798 881867 := bstep (se 1 (by rfl) ⟨661400, by rfl⟩ : syracuseStep 881867 = 1322801) B1322801
theorem B521431 : Blo 519798 521431 := bstep (se 1 (by rfl) ⟨391073, by rfl⟩ : syracuseStep 521431 = 782147) B782147
theorem B783575 : Blo 519798 783575 := bstep (se 1 (by rfl) ⟨587681, by rfl⟩ : syracuseStep 783575 = 1175363) B1175363
theorem B521451 : Blo 519798 521451 := bstep (se 1 (by rfl) ⟨391088, by rfl⟩ : syracuseStep 521451 = 782177) B782177
theorem B521463 : Blo 519798 521463 := bstep (se 1 (by rfl) ⟨391097, by rfl⟩ : syracuseStep 521463 = 782195) B782195
theorem B521483 : Blo 519798 521483 := bstep (se 1 (by rfl) ⟨391112, by rfl⟩ : syracuseStep 521483 = 782225) B782225
theorem B521495 : Blo 519798 521495 := bstep (se 1 (by rfl) ⟨391121, by rfl⟩ : syracuseStep 521495 = 782243) B782243
theorem B783641 : Blo 519798 783641 := bstep (se 2 (by rfl) ⟨293865, by rfl⟩ : syracuseStep 783641 = 587731) B587731
theorem B1176857 : Blo 519798 1176857 := bstep (se 2 (by rfl) ⟨441321, by rfl⟩ : syracuseStep 1176857 = 882643) B882643
theorem B521515 : Blo 519798 521515 := bstep (se 1 (by rfl) ⟨391136, by rfl⟩ : syracuseStep 521515 = 782273) B782273
theorem B521527 : Blo 519798 521527 := bstep (se 1 (by rfl) ⟨391145, by rfl⟩ : syracuseStep 521527 = 782291) B782291
theorem B521547 : Blo 519798 521547 := bstep (se 1 (by rfl) ⟨391160, by rfl⟩ : syracuseStep 521547 = 782321) B782321
theorem B587083 : Blo 519798 587083 := bstep (se 1 (by rfl) ⟨440312, by rfl⟩ : syracuseStep 587083 = 880625) B880625
theorem B881995 : Blo 519798 881995 := bstep (se 1 (by rfl) ⟨661496, by rfl⟩ : syracuseStep 881995 = 1322993) B1322993
theorem B521559 : Blo 519798 521559 := bstep (se 1 (by rfl) ⟨391169, by rfl⟩ : syracuseStep 521559 = 782339) B782339
theorem B521579 : Blo 519798 521579 := bstep (se 1 (by rfl) ⟨391184, by rfl⟩ : syracuseStep 521579 = 782369) B782369
theorem B1176947 : Blo 519798 1176947 := bstep (se 1 (by rfl) ⟨882710, by rfl⟩ : syracuseStep 1176947 = 1765421) B1765421
theorem B521591 : Blo 519798 521591 := bstep (se 1 (by rfl) ⟨391193, by rfl⟩ : syracuseStep 521591 = 782387) B782387
theorem B521611 : Blo 519798 521611 := bstep (se 1 (by rfl) ⟨391208, by rfl⟩ : syracuseStep 521611 = 782417) B782417
theorem B783755 : Blo 519798 783755 := bstep (se 1 (by rfl) ⟨587816, by rfl⟩ : syracuseStep 783755 = 1175633) B1175633
theorem B521623 : Blo 519798 521623 := bstep (se 1 (by rfl) ⟨391217, by rfl⟩ : syracuseStep 521623 = 782435) B782435
theorem B783767 : Blo 519798 783767 := bstep (se 1 (by rfl) ⟨587825, by rfl⟩ : syracuseStep 783767 = 1175651) B1175651
theorem B1176983 : Blo 519798 1176983 := bstep (se 1 (by rfl) ⟨882737, by rfl⟩ : syracuseStep 1176983 = 1765475) B1765475
theorem B521643 : Blo 519798 521643 := bstep (se 1 (by rfl) ⟨391232, by rfl⟩ : syracuseStep 521643 = 782465) B782465
theorem B1111475 : Blo 519798 1111475 := bstep (se 1 (by rfl) ⟨833606, by rfl⟩ : syracuseStep 1111475 = 1667213) B1667213
theorem B521655 : Blo 519798 521655 := bstep (se 1 (by rfl) ⟨391241, by rfl⟩ : syracuseStep 521655 = 782483) B782483
theorem B587191 : Blo 519798 587191 := bstep (se 1 (by rfl) ⟨440393, by rfl⟩ : syracuseStep 587191 = 880787) B880787
theorem B521675 : Blo 519798 521675 := bstep (se 1 (by rfl) ⟨391256, by rfl⟩ : syracuseStep 521675 = 782513) B782513
theorem B521687 : Blo 519798 521687 := bstep (se 1 (by rfl) ⟨391265, by rfl⟩ : syracuseStep 521687 = 782531) B782531
theorem B783833 : Blo 519798 783833 := bstep (se 2 (by rfl) ⟨293937, by rfl⟩ : syracuseStep 783833 = 587875) B587875
theorem B882137 : Blo 519798 882137 := bstep (se 2 (by rfl) ⟨330801, by rfl⟩ : syracuseStep 882137 = 661603) B661603
theorem B521707 : Blo 519798 521707 := bstep (se 1 (by rfl) ⟨391280, by rfl⟩ : syracuseStep 521707 = 782561) B782561
theorem B521719 : Blo 519798 521719 := bstep (se 1 (by rfl) ⟨391289, by rfl⟩ : syracuseStep 521719 = 782579) B782579
theorem B521739 : Blo 519798 521739 := bstep (se 1 (by rfl) ⟨391304, by rfl⟩ : syracuseStep 521739 = 782609) B782609
theorem B521751 : Blo 519798 521751 := bstep (se 1 (by rfl) ⟨391313, by rfl⟩ : syracuseStep 521751 = 782627) B782627
theorem B521771 : Blo 519798 521771 := bstep (se 1 (by rfl) ⟨391328, by rfl⟩ : syracuseStep 521771 = 782657) B782657
theorem B521783 : Blo 519798 521783 := bstep (se 1 (by rfl) ⟨391337, by rfl⟩ : syracuseStep 521783 = 782675) B782675
theorem B521803 : Blo 519798 521803 := bstep (se 1 (by rfl) ⟨391352, by rfl⟩ : syracuseStep 521803 = 782705) B782705
theorem B783947 : Blo 519798 783947 := bstep (se 1 (by rfl) ⟨587960, by rfl⟩ : syracuseStep 783947 = 1175921) B1175921
theorem B1177163 : Blo 519798 1177163 := bstep (se 1 (by rfl) ⟨882872, by rfl⟩ : syracuseStep 1177163 = 1765745) B1765745
theorem B1766987 : Blo 519798 1766987 := bstep (se 1 (by rfl) ⟨1325240, by rfl⟩ : syracuseStep 1766987 = 2650481) B2650481
theorem B521815 : Blo 519798 521815 := bstep (se 1 (by rfl) ⟨391361, by rfl⟩ : syracuseStep 521815 = 782723) B782723
theorem B783959 : Blo 519798 783959 := bstep (se 1 (by rfl) ⟨587969, by rfl⟩ : syracuseStep 783959 = 1175939) B1175939
theorem B882265 : Blo 519798 882265 := bstep (se 2 (by rfl) ⟨330849, by rfl⟩ : syracuseStep 882265 = 661699) B661699
theorem B521835 : Blo 519798 521835 := bstep (se 1 (by rfl) ⟨391376, by rfl⟩ : syracuseStep 521835 = 782753) B782753
theorem B587371 : Blo 519798 587371 := bstep (se 1 (by rfl) ⟨440528, by rfl⟩ : syracuseStep 587371 = 881057) B881057
theorem B521847 : Blo 519798 521847 := bstep (se 1 (by rfl) ⟨391385, by rfl⟩ : syracuseStep 521847 = 782771) B782771
theorem B1177217 : Blo 519798 1177217 := bstep (se 2 (by rfl) ⟨441456, by rfl⟩ : syracuseStep 1177217 = 882913) B882913
theorem B521867 : Blo 519798 521867 := bstep (se 1 (by rfl) ⟨391400, by rfl⟩ : syracuseStep 521867 = 782801) B782801
theorem B521879 : Blo 519798 521879 := bstep (se 1 (by rfl) ⟨391409, by rfl⟩ : syracuseStep 521879 = 782819) B782819
theorem B784025 : Blo 519798 784025 := bstep (se 2 (by rfl) ⟨294009, by rfl⟩ : syracuseStep 784025 = 588019) B588019
theorem B521899 : Blo 519798 521899 := bstep (se 1 (by rfl) ⟨391424, by rfl⟩ : syracuseStep 521899 = 782849) B782849
theorem B521911 : Blo 519798 521911 := bstep (se 1 (by rfl) ⟨391433, by rfl⟩ : syracuseStep 521911 = 782867) B782867
theorem B521931 : Blo 519798 521931 := bstep (se 1 (by rfl) ⟨391448, by rfl⟩ : syracuseStep 521931 = 782897) B782897
theorem B685783 : Blo 519798 685783 := bstep (se 1 (by rfl) ⟨514337, by rfl⟩ : syracuseStep 685783 = 1028675) B1028675
theorem B521943 : Blo 519798 521943 := bstep (se 1 (by rfl) ⟨391457, by rfl⟩ : syracuseStep 521943 = 782915) B782915
theorem B587479 : Blo 519798 587479 := bstep (se 1 (by rfl) ⟨440609, by rfl⟩ : syracuseStep 587479 = 881219) B881219
theorem B521963 : Blo 519798 521963 := bstep (se 1 (by rfl) ⟨391472, by rfl⟩ : syracuseStep 521963 = 782945) B782945
theorem B521975 : Blo 519798 521975 := bstep (se 1 (by rfl) ⟨391481, by rfl⟩ : syracuseStep 521975 = 782963) B782963
theorem B521995 : Blo 519798 521995 := bstep (se 1 (by rfl) ⟨391496, by rfl⟩ : syracuseStep 521995 = 782993) B782993
theorem B784139 : Blo 519798 784139 := bstep (se 1 (by rfl) ⟨588104, by rfl⟩ : syracuseStep 784139 = 1176209) B1176209
theorem B522007 : Blo 519798 522007 := bstep (se 1 (by rfl) ⟨391505, by rfl⟩ : syracuseStep 522007 = 783011) B783011
theorem B784151 : Blo 519798 784151 := bstep (se 1 (by rfl) ⟨588113, by rfl⟩ : syracuseStep 784151 = 1176227) B1176227
theorem B522027 : Blo 519798 522027 := bstep (se 1 (by rfl) ⟨391520, by rfl⟩ : syracuseStep 522027 = 783041) B783041
theorem B522039 : Blo 519798 522039 := bstep (se 1 (by rfl) ⟨391529, by rfl⟩ : syracuseStep 522039 = 783059) B783059
theorem B522059 : Blo 519798 522059 := bstep (se 1 (by rfl) ⟨391544, by rfl⟩ : syracuseStep 522059 = 783089) B783089
theorem B522071 : Blo 519798 522071 := bstep (se 1 (by rfl) ⟨391553, by rfl⟩ : syracuseStep 522071 = 783107) B783107
theorem B784217 : Blo 519798 784217 := bstep (se 2 (by rfl) ⟨294081, by rfl⟩ : syracuseStep 784217 = 588163) B588163
theorem B1177433 : Blo 519798 1177433 := bstep (se 2 (by rfl) ⟨441537, by rfl⟩ : syracuseStep 1177433 = 883075) B883075
theorem B1767257 : Blo 519798 1767257 := bstep (se 2 (by rfl) ⟨662721, by rfl⟩ : syracuseStep 1767257 = 1325443) B1325443
theorem B522091 : Blo 519798 522091 := bstep (se 1 (by rfl) ⟨391568, by rfl⟩ : syracuseStep 522091 = 783137) B783137
theorem B522103 : Blo 519798 522103 := bstep (se 1 (by rfl) ⟨391577, by rfl⟩ : syracuseStep 522103 = 783155) B783155
theorem B522123 : Blo 519798 522123 := bstep (se 1 (by rfl) ⟨391592, by rfl⟩ : syracuseStep 522123 = 783185) B783185
theorem B587659 : Blo 519798 587659 := bstep (se 1 (by rfl) ⟨440744, by rfl⟩ : syracuseStep 587659 = 881489) B881489
theorem B522135 : Blo 519798 522135 := bstep (se 1 (by rfl) ⟨391601, by rfl⟩ : syracuseStep 522135 = 783203) B783203
theorem B522155 : Blo 519798 522155 := bstep (se 1 (by rfl) ⟨391616, by rfl⟩ : syracuseStep 522155 = 783233) B783233
theorem B1177523 : Blo 519798 1177523 := bstep (se 1 (by rfl) ⟨883142, by rfl⟩ : syracuseStep 1177523 = 1766285) B1766285
theorem B522167 : Blo 519798 522167 := bstep (se 1 (by rfl) ⟨391625, by rfl⟩ : syracuseStep 522167 = 783251) B783251
theorem B522187 : Blo 519798 522187 := bstep (se 1 (by rfl) ⟨391640, by rfl⟩ : syracuseStep 522187 = 783281) B783281
theorem B784331 : Blo 519798 784331 := bstep (se 1 (by rfl) ⟨588248, by rfl⟩ : syracuseStep 784331 = 1176497) B1176497
theorem B522199 : Blo 519798 522199 := bstep (se 1 (by rfl) ⟨391649, by rfl⟩ : syracuseStep 522199 = 783299) B783299
theorem B784343 : Blo 519798 784343 := bstep (se 1 (by rfl) ⟨588257, by rfl⟩ : syracuseStep 784343 = 1176515) B1176515
theorem B1177559 : Blo 519798 1177559 := bstep (se 1 (by rfl) ⟨883169, by rfl⟩ : syracuseStep 1177559 = 1766339) B1766339
theorem B522219 : Blo 519798 522219 := bstep (se 1 (by rfl) ⟨391664, by rfl⟩ : syracuseStep 522219 = 783329) B783329
theorem B522231 : Blo 519798 522231 := bstep (se 1 (by rfl) ⟨391673, by rfl⟩ : syracuseStep 522231 = 783347) B783347
theorem B587767 : Blo 519798 587767 := bstep (se 1 (by rfl) ⟨440825, by rfl⟩ : syracuseStep 587767 = 881651) B881651
theorem B522251 : Blo 519798 522251 := bstep (se 1 (by rfl) ⟨391688, by rfl⟩ : syracuseStep 522251 = 783377) B783377
theorem B522263 : Blo 519798 522263 := bstep (se 1 (by rfl) ⟨391697, by rfl⟩ : syracuseStep 522263 = 783395) B783395
theorem B784409 : Blo 519798 784409 := bstep (se 2 (by rfl) ⟨294153, by rfl⟩ : syracuseStep 784409 = 588307) B588307
theorem B522283 : Blo 519798 522283 := bstep (se 1 (by rfl) ⟨391712, by rfl⟩ : syracuseStep 522283 = 783425) B783425
theorem B522295 : Blo 519798 522295 := bstep (se 1 (by rfl) ⟨391721, by rfl⟩ : syracuseStep 522295 = 783443) B783443
theorem B522315 : Blo 519798 522315 := bstep (se 1 (by rfl) ⟨391736, by rfl⟩ : syracuseStep 522315 = 783473) B783473
theorem B522327 : Blo 519798 522327 := bstep (se 1 (by rfl) ⟨391745, by rfl⟩ : syracuseStep 522327 = 783491) B783491
theorem B522347 : Blo 519798 522347 := bstep (se 1 (by rfl) ⟨391760, by rfl⟩ : syracuseStep 522347 = 783521) B783521
theorem B522359 : Blo 519798 522359 := bstep (se 1 (by rfl) ⟨391769, by rfl⟩ : syracuseStep 522359 = 783539) B783539
theorem B522379 : Blo 519798 522379 := bstep (se 1 (by rfl) ⟨391784, by rfl⟩ : syracuseStep 522379 = 783569) B783569
theorem B784523 : Blo 519798 784523 := bstep (se 1 (by rfl) ⟨588392, by rfl⟩ : syracuseStep 784523 = 1176785) B1176785
theorem B1177739 : Blo 519798 1177739 := bstep (se 1 (by rfl) ⟨883304, by rfl⟩ : syracuseStep 1177739 = 1766609) B1766609
theorem B522391 : Blo 519798 522391 := bstep (se 1 (by rfl) ⟨391793, by rfl⟩ : syracuseStep 522391 = 783587) B783587
theorem B784535 : Blo 519798 784535 := bstep (se 1 (by rfl) ⟨588401, by rfl⟩ : syracuseStep 784535 = 1176803) B1176803
theorem B882839 : Blo 519798 882839 := bstep (se 1 (by rfl) ⟨662129, by rfl⟩ : syracuseStep 882839 = 1324259) B1324259
theorem B522411 : Blo 519798 522411 := bstep (se 1 (by rfl) ⟨391808, by rfl⟩ : syracuseStep 522411 = 783617) B783617
theorem B587947 : Blo 519798 587947 := bstep (se 1 (by rfl) ⟨440960, by rfl⟩ : syracuseStep 587947 = 881921) B881921
theorem B522423 : Blo 519798 522423 := bstep (se 1 (by rfl) ⟨391817, by rfl⟩ : syracuseStep 522423 = 783635) B783635
theorem B1177793 : Blo 519798 1177793 := bstep (se 2 (by rfl) ⟨441672, by rfl⟩ : syracuseStep 1177793 = 883345) B883345
theorem B522443 : Blo 519798 522443 := bstep (se 1 (by rfl) ⟨391832, by rfl⟩ : syracuseStep 522443 = 783665) B783665
theorem B522455 : Blo 519798 522455 := bstep (se 1 (by rfl) ⟨391841, by rfl⟩ : syracuseStep 522455 = 783683) B783683
theorem B784601 : Blo 519798 784601 := bstep (se 2 (by rfl) ⟨294225, by rfl⟩ : syracuseStep 784601 = 588451) B588451
theorem B522475 : Blo 519798 522475 := bstep (se 1 (by rfl) ⟨391856, by rfl⟩ : syracuseStep 522475 = 783713) B783713
theorem B522487 : Blo 519798 522487 := bstep (se 1 (by rfl) ⟨391865, by rfl⟩ : syracuseStep 522487 = 783731) B783731
theorem B522507 : Blo 519798 522507 := bstep (se 1 (by rfl) ⟨391880, by rfl⟩ : syracuseStep 522507 = 783761) B783761
theorem B522519 : Blo 519798 522519 := bstep (se 1 (by rfl) ⟨391889, by rfl⟩ : syracuseStep 522519 = 783779) B783779
theorem B588055 : Blo 519798 588055 := bstep (se 1 (by rfl) ⟨441041, by rfl⟩ : syracuseStep 588055 = 882083) B882083
theorem B882967 : Blo 519798 882967 := bstep (se 1 (by rfl) ⟨662225, by rfl⟩ : syracuseStep 882967 = 1324451) B1324451
theorem B522539 : Blo 519798 522539 := bstep (se 1 (by rfl) ⟨391904, by rfl⟩ : syracuseStep 522539 = 783809) B783809
theorem B522551 : Blo 519798 522551 := bstep (se 1 (by rfl) ⟨391913, by rfl⟩ : syracuseStep 522551 = 783827) B783827
theorem B522571 : Blo 519798 522571 := bstep (se 1 (by rfl) ⟨391928, by rfl⟩ : syracuseStep 522571 = 783857) B783857
theorem B784715 : Blo 519798 784715 := bstep (se 1 (by rfl) ⟨588536, by rfl⟩ : syracuseStep 784715 = 1177073) B1177073
theorem B522583 : Blo 519798 522583 := bstep (se 1 (by rfl) ⟨391937, by rfl⟩ : syracuseStep 522583 = 783875) B783875
theorem B784727 : Blo 519798 784727 := bstep (se 1 (by rfl) ⟨588545, by rfl⟩ : syracuseStep 784727 = 1177091) B1177091
theorem B522603 : Blo 519798 522603 := bstep (se 1 (by rfl) ⟨391952, by rfl⟩ : syracuseStep 522603 = 783905) B783905
theorem B522615 : Blo 519798 522615 := bstep (se 1 (by rfl) ⟨391961, by rfl⟩ : syracuseStep 522615 = 783923) B783923
theorem B1112449 : Blo 519798 1112449 := bstep (se 2 (by rfl) ⟨417168, by rfl⟩ : syracuseStep 1112449 = 834337) B834337
theorem B522635 : Blo 519798 522635 := bstep (se 1 (by rfl) ⟨391976, by rfl⟩ : syracuseStep 522635 = 783953) B783953
theorem B522647 : Blo 519798 522647 := bstep (se 1 (by rfl) ⟨391985, by rfl⟩ : syracuseStep 522647 = 783971) B783971
theorem B784793 : Blo 519798 784793 := bstep (se 2 (by rfl) ⟨294297, by rfl⟩ : syracuseStep 784793 = 588595) B588595
theorem B1178009 : Blo 519798 1178009 := bstep (se 2 (by rfl) ⟨441753, by rfl⟩ : syracuseStep 1178009 = 883507) B883507
theorem B522667 : Blo 519798 522667 := bstep (se 1 (by rfl) ⟨392000, by rfl⟩ : syracuseStep 522667 = 784001) B784001
theorem B522679 : Blo 519798 522679 := bstep (se 1 (by rfl) ⟨392009, by rfl⟩ : syracuseStep 522679 = 784019) B784019
theorem B588235 : Blo 519798 588235 := bstep (se 1 (by rfl) ⟨441176, by rfl⟩ : syracuseStep 588235 = 882353) B882353
theorem B522699 : Blo 519798 522699 := bstep (se 1 (by rfl) ⟨392024, by rfl⟩ : syracuseStep 522699 = 784049) B784049
theorem B522711 : Blo 519798 522711 := bstep (se 1 (by rfl) ⟨392033, by rfl⟩ : syracuseStep 522711 = 784067) B784067
theorem B2980313 : Blo 519798 2980313 := bstep (se 2 (by rfl) ⟨1117617, by rfl⟩ : syracuseStep 2980313 = 2235235) B2235235
theorem B522731 : Blo 519798 522731 := bstep (se 1 (by rfl) ⟨392048, by rfl⟩ : syracuseStep 522731 = 784097) B784097
theorem B1178099 : Blo 519798 1178099 := bstep (se 1 (by rfl) ⟨883574, by rfl⟩ : syracuseStep 1178099 = 1767149) B1767149
theorem B522743 : Blo 519798 522743 := bstep (se 1 (by rfl) ⟨392057, by rfl⟩ : syracuseStep 522743 = 784115) B784115
theorem B522763 : Blo 519798 522763 := bstep (se 1 (by rfl) ⟨392072, by rfl⟩ : syracuseStep 522763 = 784145) B784145
theorem B784907 : Blo 519798 784907 := bstep (se 1 (by rfl) ⟨588680, by rfl⟩ : syracuseStep 784907 = 1177361) B1177361
theorem B522775 : Blo 519798 522775 := bstep (se 1 (by rfl) ⟨392081, by rfl⟩ : syracuseStep 522775 = 784163) B784163
theorem B784919 : Blo 519798 784919 := bstep (se 1 (by rfl) ⟨588689, by rfl⟩ : syracuseStep 784919 = 1177379) B1177379
theorem B1178135 : Blo 519798 1178135 := bstep (se 1 (by rfl) ⟨883601, by rfl⟩ : syracuseStep 1178135 = 1767203) B1767203
theorem B522795 : Blo 519798 522795 := bstep (se 1 (by rfl) ⟨392096, by rfl⟩ : syracuseStep 522795 = 784193) B784193
theorem B522807 : Blo 519798 522807 := bstep (se 1 (by rfl) ⟨392105, by rfl⟩ : syracuseStep 522807 = 784211) B784211
theorem B588343 : Blo 519798 588343 := bstep (se 1 (by rfl) ⟨441257, by rfl⟩ : syracuseStep 588343 = 882515) B882515
theorem B522827 : Blo 519798 522827 := bstep (se 1 (by rfl) ⟨392120, by rfl⟩ : syracuseStep 522827 = 784241) B784241
theorem B522839 : Blo 519798 522839 := bstep (se 1 (by rfl) ⟨392129, by rfl⟩ : syracuseStep 522839 = 784259) B784259
theorem B1407577 : Blo 519798 1407577 := bstep (se 2 (by rfl) ⟨527841, by rfl⟩ : syracuseStep 1407577 = 1055683) B1055683
theorem B784985 : Blo 519798 784985 := bstep (se 2 (by rfl) ⟨294369, by rfl⟩ : syracuseStep 784985 = 588739) B588739
theorem B522859 : Blo 519798 522859 := bstep (se 1 (by rfl) ⟨392144, by rfl⟩ : syracuseStep 522859 = 784289) B784289
theorem B522871 : Blo 519798 522871 := bstep (se 1 (by rfl) ⟨392153, by rfl⟩ : syracuseStep 522871 = 784307) B784307
theorem B1112705 : Blo 519798 1112705 := bstep (se 2 (by rfl) ⟨417264, by rfl⟩ : syracuseStep 1112705 = 834529) B834529
theorem B522891 : Blo 519798 522891 := bstep (se 1 (by rfl) ⟨392168, by rfl⟩ : syracuseStep 522891 = 784337) B784337
theorem B522903 : Blo 519798 522903 := bstep (se 1 (by rfl) ⟨392177, by rfl⟩ : syracuseStep 522903 = 784355) B784355
theorem B522923 : Blo 519798 522923 := bstep (se 1 (by rfl) ⟨392192, by rfl⟩ : syracuseStep 522923 = 784385) B784385
theorem B555703 : Blo 519798 555703 := bstep (se 1 (by rfl) ⟨416777, by rfl⟩ : syracuseStep 555703 = 833555) B833555
theorem B522935 : Blo 519798 522935 := bstep (se 1 (by rfl) ⟨392201, by rfl⟩ : syracuseStep 522935 = 784403) B784403
theorem B522955 : Blo 519798 522955 := bstep (se 1 (by rfl) ⟨392216, by rfl⟩ : syracuseStep 522955 = 784433) B784433
theorem B785099 : Blo 519798 785099 := bstep (se 1 (by rfl) ⟨588824, by rfl⟩ : syracuseStep 785099 = 1177649) B1177649
theorem B1178315 : Blo 519798 1178315 := bstep (se 1 (by rfl) ⟨883736, by rfl⟩ : syracuseStep 1178315 = 1767473) B1767473
theorem B1112791 : Blo 519798 1112791 := bstep (se 1 (by rfl) ⟨834593, by rfl⟩ : syracuseStep 1112791 = 1669187) B1669187
theorem B522967 : Blo 519798 522967 := bstep (se 1 (by rfl) ⟨392225, by rfl⟩ : syracuseStep 522967 = 784451) B784451
theorem B785111 : Blo 519798 785111 := bstep (se 1 (by rfl) ⟨588833, by rfl⟩ : syracuseStep 785111 = 1177667) B1177667
theorem B522987 : Blo 519798 522987 := bstep (se 1 (by rfl) ⟨392240, by rfl⟩ : syracuseStep 522987 = 784481) B784481
theorem B588523 : Blo 519798 588523 := bstep (se 1 (by rfl) ⟨441392, by rfl⟩ : syracuseStep 588523 = 882785) B882785
theorem B522999 : Blo 519798 522999 := bstep (se 1 (by rfl) ⟨392249, by rfl⟩ : syracuseStep 522999 = 784499) B784499
theorem B1178369 : Blo 519798 1178369 := bstep (se 2 (by rfl) ⟨441888, by rfl⟩ : syracuseStep 1178369 = 883777) B883777
theorem B523019 : Blo 519798 523019 := bstep (se 1 (by rfl) ⟨392264, by rfl⟩ : syracuseStep 523019 = 784529) B784529
theorem B2030359 : Blo 519798 2030359 := bstep (se 1 (by rfl) ⟨1522769, by rfl⟩ : syracuseStep 2030359 = 3045539) B3045539
theorem B523031 : Blo 519798 523031 := bstep (se 1 (by rfl) ⟨392273, by rfl⟩ : syracuseStep 523031 = 784547) B784547
theorem B785177 : Blo 519798 785177 := bstep (se 2 (by rfl) ⟨294441, by rfl⟩ : syracuseStep 785177 = 588883) B588883
theorem B523051 : Blo 519798 523051 := bstep (se 1 (by rfl) ⟨392288, by rfl⟩ : syracuseStep 523051 = 784577) B784577
theorem B523063 : Blo 519798 523063 := bstep (se 1 (by rfl) ⟨392297, by rfl⟩ : syracuseStep 523063 = 784595) B784595
theorem B523083 : Blo 519798 523083 := bstep (se 1 (by rfl) ⟨392312, by rfl⟩ : syracuseStep 523083 = 784625) B784625
theorem B523095 : Blo 519798 523095 := bstep (se 1 (by rfl) ⟨392321, by rfl⟩ : syracuseStep 523095 = 784643) B784643
theorem B588631 : Blo 519798 588631 := bstep (se 1 (by rfl) ⟨441473, by rfl⟩ : syracuseStep 588631 = 882947) B882947
theorem B523115 : Blo 519798 523115 := bstep (se 1 (by rfl) ⟨392336, by rfl⟩ : syracuseStep 523115 = 784673) B784673
theorem B523127 : Blo 519798 523127 := bstep (se 1 (by rfl) ⟨392345, by rfl⟩ : syracuseStep 523127 = 784691) B784691
theorem B523147 : Blo 519798 523147 := bstep (se 1 (by rfl) ⟨392360, by rfl⟩ : syracuseStep 523147 = 784721) B784721
theorem B785291 : Blo 519798 785291 := bstep (se 1 (by rfl) ⟨588968, by rfl⟩ : syracuseStep 785291 = 1177937) B1177937
theorem B883595 : Blo 519798 883595 := bstep (se 1 (by rfl) ⟨662696, by rfl⟩ : syracuseStep 883595 = 1325393) B1325393
theorem B523159 : Blo 519798 523159 := bstep (se 1 (by rfl) ⟨392369, by rfl⟩ : syracuseStep 523159 = 784739) B784739
theorem B785303 : Blo 519798 785303 := bstep (se 1 (by rfl) ⟨588977, by rfl⟩ : syracuseStep 785303 = 1177955) B1177955
theorem B523179 : Blo 519798 523179 := bstep (se 1 (by rfl) ⟨392384, by rfl⟩ : syracuseStep 523179 = 784769) B784769
theorem B523191 : Blo 519798 523191 := bstep (se 1 (by rfl) ⟨392393, by rfl⟩ : syracuseStep 523191 = 784787) B784787
theorem B523211 : Blo 519798 523211 := bstep (se 1 (by rfl) ⟨392408, by rfl⟩ : syracuseStep 523211 = 784817) B784817
theorem B523223 : Blo 519798 523223 := bstep (se 1 (by rfl) ⟨392417, by rfl⟩ : syracuseStep 523223 = 784835) B784835
theorem B785369 : Blo 519798 785369 := bstep (se 2 (by rfl) ⟨294513, by rfl⟩ : syracuseStep 785369 = 589027) B589027
theorem B523243 : Blo 519798 523243 := bstep (se 1 (by rfl) ⟨392432, by rfl⟩ : syracuseStep 523243 = 784865) B784865
theorem B523255 : Blo 519798 523255 := bstep (se 1 (by rfl) ⟨392441, by rfl⟩ : syracuseStep 523255 = 784883) B784883
theorem B523275 : Blo 519798 523275 := bstep (se 1 (by rfl) ⟨392456, by rfl⟩ : syracuseStep 523275 = 784913) B784913
theorem B588811 : Blo 519798 588811 := bstep (se 1 (by rfl) ⟨441608, by rfl⟩ : syracuseStep 588811 = 883217) B883217
theorem B883723 : Blo 519798 883723 := bstep (se 1 (by rfl) ⟨662792, by rfl⟩ : syracuseStep 883723 = 1325585) B1325585
theorem B523287 : Blo 519798 523287 := bstep (se 1 (by rfl) ⟨392465, by rfl⟩ : syracuseStep 523287 = 784931) B784931
theorem B556075 : Blo 519798 556075 := bstep (se 1 (by rfl) ⟨417056, by rfl⟩ : syracuseStep 556075 = 834113) B834113
theorem B523307 : Blo 519798 523307 := bstep (se 1 (by rfl) ⟨392480, by rfl⟩ : syracuseStep 523307 = 784961) B784961
theorem B523319 : Blo 519798 523319 := bstep (se 1 (by rfl) ⟨392489, by rfl⟩ : syracuseStep 523319 = 784979) B784979
theorem B523339 : Blo 519798 523339 := bstep (se 1 (by rfl) ⟨392504, by rfl⟩ : syracuseStep 523339 = 785009) B785009
theorem B785483 : Blo 519798 785483 := bstep (se 1 (by rfl) ⟨589112, by rfl⟩ : syracuseStep 785483 = 1178225) B1178225
theorem B523351 : Blo 519798 523351 := bstep (se 1 (by rfl) ⟨392513, by rfl⟩ : syracuseStep 523351 = 785027) B785027
theorem B785495 : Blo 519798 785495 := bstep (se 1 (by rfl) ⟨589121, by rfl⟩ : syracuseStep 785495 = 1178243) B1178243
theorem B523371 : Blo 519798 523371 := bstep (se 1 (by rfl) ⟨392528, by rfl⟩ : syracuseStep 523371 = 785057) B785057
theorem B523383 : Blo 519798 523383 := bstep (se 1 (by rfl) ⟨392537, by rfl⟩ : syracuseStep 523383 = 785075) B785075
theorem B588919 : Blo 519798 588919 := bstep (se 1 (by rfl) ⟨441689, by rfl⟩ : syracuseStep 588919 = 883379) B883379
theorem B523403 : Blo 519798 523403 := bstep (se 1 (by rfl) ⟨392552, by rfl⟩ : syracuseStep 523403 = 785105) B785105
theorem B523415 : Blo 519798 523415 := bstep (se 1 (by rfl) ⟨392561, by rfl⟩ : syracuseStep 523415 = 785123) B785123
theorem B785561 : Blo 519798 785561 := bstep (se 2 (by rfl) ⟨294585, by rfl⟩ : syracuseStep 785561 = 589171) B589171
theorem B883865 : Blo 519798 883865 := bstep (se 2 (by rfl) ⟨331449, by rfl⟩ : syracuseStep 883865 = 662899) B662899
theorem B523435 : Blo 519798 523435 := bstep (se 1 (by rfl) ⟨392576, by rfl⟩ : syracuseStep 523435 = 785153) B785153
theorem B523447 : Blo 519798 523447 := bstep (se 1 (by rfl) ⟨392585, by rfl⟩ : syracuseStep 523447 = 785171) B785171
theorem B523467 : Blo 519798 523467 := bstep (se 1 (by rfl) ⟨392600, by rfl⟩ : syracuseStep 523467 = 785201) B785201
theorem B523479 : Blo 519798 523479 := bstep (se 1 (by rfl) ⟨392609, by rfl⟩ : syracuseStep 523479 = 785219) B785219
theorem B523499 : Blo 519798 523499 := bstep (se 1 (by rfl) ⟨392624, by rfl⟩ : syracuseStep 523499 = 785249) B785249
theorem B523511 : Blo 519798 523511 := bstep (se 1 (by rfl) ⟨392633, by rfl⟩ : syracuseStep 523511 = 785267) B785267
theorem B523531 : Blo 519798 523531 := bstep (se 1 (by rfl) ⟨392648, by rfl⟩ : syracuseStep 523531 = 785297) B785297
theorem B785675 : Blo 519798 785675 := bstep (se 1 (by rfl) ⟨589256, by rfl⟩ : syracuseStep 785675 = 1178513) B1178513
theorem B523543 : Blo 519798 523543 := bstep (se 1 (by rfl) ⟨392657, by rfl⟩ : syracuseStep 523543 = 785315) B785315
theorem B785687 : Blo 519798 785687 := bstep (se 1 (by rfl) ⟨589265, by rfl⟩ : syracuseStep 785687 = 1178531) B1178531
theorem B523563 : Blo 519798 523563 := bstep (se 1 (by rfl) ⟨392672, by rfl⟩ : syracuseStep 523563 = 785345) B785345
theorem B589099 : Blo 519798 589099 := bstep (se 1 (by rfl) ⟨441824, by rfl⟩ : syracuseStep 589099 = 883649) B883649
theorem B523575 : Blo 519798 523575 := bstep (se 1 (by rfl) ⟨392681, by rfl⟩ : syracuseStep 523575 = 785363) B785363
theorem B523595 : Blo 519798 523595 := bstep (se 1 (by rfl) ⟨392696, by rfl⟩ : syracuseStep 523595 = 785393) B785393
theorem B523607 : Blo 519798 523607 := bstep (se 1 (by rfl) ⟨392705, by rfl⟩ : syracuseStep 523607 = 785411) B785411
theorem B523627 : Blo 519798 523627 := bstep (se 1 (by rfl) ⟨392720, by rfl⟩ : syracuseStep 523627 = 785441) B785441
theorem B523639 : Blo 519798 523639 := bstep (se 1 (by rfl) ⟨392729, by rfl⟩ : syracuseStep 523639 = 785459) B785459
theorem B523659 : Blo 519798 523659 := bstep (se 1 (by rfl) ⟨392744, by rfl⟩ : syracuseStep 523659 = 785489) B785489
theorem B523671 : Blo 519798 523671 := bstep (se 1 (by rfl) ⟨392753, by rfl⟩ : syracuseStep 523671 = 785507) B785507
theorem B589207 : Blo 519798 589207 := bstep (se 1 (by rfl) ⟨441905, by rfl⟩ : syracuseStep 589207 = 883811) B883811
theorem B523691 : Blo 519798 523691 := bstep (se 1 (by rfl) ⟨392768, by rfl⟩ : syracuseStep 523691 = 785537) B785537
theorem B523703 : Blo 519798 523703 := bstep (se 1 (by rfl) ⟨392777, by rfl⟩ : syracuseStep 523703 = 785555) B785555
theorem B523723 : Blo 519798 523723 := bstep (se 1 (by rfl) ⟨392792, by rfl⟩ : syracuseStep 523723 = 785585) B785585
theorem B523735 : Blo 519798 523735 := bstep (se 1 (by rfl) ⟨392801, by rfl⟩ : syracuseStep 523735 = 785603) B785603
theorem B523755 : Blo 519798 523755 := bstep (se 1 (by rfl) ⟨392816, by rfl⟩ : syracuseStep 523755 = 785633) B785633
theorem B523767 : Blo 519798 523767 := bstep (se 1 (by rfl) ⟨392825, by rfl⟩ : syracuseStep 523767 = 785651) B785651
theorem B523787 : Blo 519798 523787 := bstep (se 1 (by rfl) ⟨392840, by rfl⟩ : syracuseStep 523787 = 785681) B785681
theorem B1671005 : Blo 519798 1671005 := bstep (se 3 (by rfl) ⟨313313, by rfl⟩ : syracuseStep 1671005 = 626627) B626627
theorem B1409177 : Blo 519798 1409177 := bstep (se 2 (by rfl) ⟨528441, by rfl⟩ : syracuseStep 1409177 = 1056883) B1056883
theorem B2982203 : Blo 519798 2982203 := bstep (se 1 (by rfl) ⟨2236652, by rfl⟩ : syracuseStep 2982203 = 4473305) B4473305
theorem B9994589 : Blo 519798 9994589 := bstep (se 3 (by rfl) ⟨1873985, by rfl⟩ : syracuseStep 9994589 = 3747971) B3747971
theorem B3768875 : Blo 519798 3768875 := bstep (se 1 (by rfl) ⟨2826656, by rfl⟩ : syracuseStep 3768875 = 5653313) B5653313
theorem B9012005 : Blo 519798 9012005 := bstep (se 4 (by rfl) ⟨844875, by rfl⟩ : syracuseStep 9012005 = 1689751) B1689751
theorem B76251941 : Blo 519798 76251941 := bstep (se 4 (by rfl) ⟨7148619, by rfl⟩ : syracuseStep 76251941 = 14297239) B14297239
theorem B2818961 : Blo 519798 2818961 := bstep (se 2 (by rfl) ⟨1057110, by rfl⟩ : syracuseStep 2818961 = 2114221) B2114221
theorem B54887381 : Blo 519798 54887381 := bstep (se 7 (by rfl) ⟨643211, by rfl⟩ : syracuseStep 54887381 = 1286423) B1286423
theorem B558095 : Blo 519798 558095 := bstep (se 1 (by rfl) ⟨418571, by rfl⟩ : syracuseStep 558095 = 837143) B837143
theorem B558343 : Blo 519798 558343 := bstep (se 1 (by rfl) ⟨418757, by rfl⟩ : syracuseStep 558343 = 837515) B837515
theorem B1672595 : Blo 519798 1672595 := bstep (se 1 (by rfl) ⟨1254446, by rfl⟩ : syracuseStep 1672595 = 2508893) B2508893
theorem B1115849 : Blo 519798 1115849 := bstep (se 2 (by rfl) ⟨418443, by rfl⟩ : syracuseStep 1115849 = 836887) B836887
theorem B3344165 : Blo 519798 3344165 := bstep (se 4 (by rfl) ⟨313515, by rfl⟩ : syracuseStep 3344165 = 627031) B627031
theorem B2000825 : Blo 519798 2000825 := bstep (se 2 (by rfl) ⟨750309, by rfl⟩ : syracuseStep 2000825 = 1500619) B1500619
theorem B3770833 : Blo 519798 3770833 := bstep (se 2 (by rfl) ⟨1414062, by rfl⟩ : syracuseStep 3770833 = 2828125) B2828125
theorem B2001469 : Blo 519798 2001469 := bstep (se 3 (by rfl) ⟨375275, by rfl⟩ : syracuseStep 2001469 = 750551) B750551
theorem B6687299 : Blo 519798 6687299 := bstep (se 1 (by rfl) ⟨5015474, by rfl⟩ : syracuseStep 6687299 = 10030949) B10030949
theorem B658039 : Blo 519798 658039 := bstep (se 1 (by rfl) ⟨493529, by rfl⟩ : syracuseStep 658039 = 987059) B987059
theorem B4950821 : Blo 519798 4950821 := bstep (se 4 (by rfl) ⟨464139, by rfl⟩ : syracuseStep 4950821 = 928279) B928279
theorem B12716837 : Blo 519798 12716837 := bstep (se 4 (by rfl) ⟨1192203, by rfl⟩ : syracuseStep 12716837 = 2384407) B2384407
theorem B10062629 : Blo 519798 10062629 := bstep (se 4 (by rfl) ⟨943371, by rfl⟩ : syracuseStep 10062629 = 1886743) B1886743
theorem B1411987 : Blo 519798 1411987 := bstep (se 1 (by rfl) ⟨1058990, by rfl⟩ : syracuseStep 1411987 = 2117981) B2117981
theorem B658363 : Blo 519798 658363 := bstep (se 1 (by rfl) ⟨493772, by rfl⟩ : syracuseStep 658363 = 987545) B987545
theorem B2231819 : Blo 519798 2231819 := bstep (se 1 (by rfl) ⟨1673864, by rfl⟩ : syracuseStep 2231819 = 3347729) B3347729
theorem B1249025 : Blo 519798 1249025 := bstep (se 2 (by rfl) ⟨468384, by rfl⟩ : syracuseStep 1249025 = 936769) B936769
theorem B1117967 : Blo 519798 1117967 := bstep (se 1 (by rfl) ⟨838475, by rfl⟩ : syracuseStep 1117967 = 1676951) B1676951
theorem B659335 : Blo 519798 659335 := bstep (se 1 (by rfl) ⟨494501, by rfl⟩ : syracuseStep 659335 = 989003) B989003
theorem B7606219 : Blo 519798 7606219 := bstep (se 1 (by rfl) ⟨5704664, by rfl⟩ : syracuseStep 7606219 = 11409329) B11409329
theorem B659755 : Blo 519798 659755 := bstep (se 1 (by rfl) ⟨494816, by rfl⟩ : syracuseStep 659755 = 989633) B989633
theorem B2756915 : Blo 519798 2756915 := bstep (se 1 (by rfl) ⟨2067686, by rfl⟩ : syracuseStep 2756915 = 4135373) B4135373
theorem B659983 : Blo 519798 659983 := bstep (se 1 (by rfl) ⟨494987, by rfl⟩ : syracuseStep 659983 = 989975) B989975
theorem B2036267 : Blo 519798 2036267 := bstep (se 1 (by rfl) ⟨1527200, by rfl⟩ : syracuseStep 2036267 = 3054401) B3054401
theorem B627319 : Blo 519798 627319 := bstep (se 1 (by rfl) ⟨470489, by rfl⟩ : syracuseStep 627319 = 940979) B940979
theorem B1249939 : Blo 519798 1249939 := bstep (se 1 (by rfl) ⟨937454, by rfl⟩ : syracuseStep 1249939 = 1874909) B1874909
theorem B987947 : Blo 519798 987947 := bstep (se 1 (by rfl) ⟨740960, by rfl⟩ : syracuseStep 987947 = 1481921) B1481921
theorem B988175 : Blo 519798 988175 := bstep (se 1 (by rfl) ⟨741131, by rfl⟩ : syracuseStep 988175 = 1482263) B1482263
theorem B660727 : Blo 519798 660727 := bstep (se 1 (by rfl) ⟨495545, by rfl⟩ : syracuseStep 660727 = 991091) B991091
theorem B1611037 : Blo 519798 1611037 := bstep (se 3 (by rfl) ⟨302069, by rfl⟩ : syracuseStep 1611037 = 604139) B604139
theorem B1250603 : Blo 519798 1250603 := bstep (se 1 (by rfl) ⟨937952, by rfl⟩ : syracuseStep 1250603 = 1875905) B1875905
theorem B2233747 : Blo 519798 2233747 := bstep (se 1 (by rfl) ⟨1675310, by rfl⟩ : syracuseStep 2233747 = 3350621) B3350621
theorem B661051 : Blo 519798 661051 := bstep (se 1 (by rfl) ⟨495788, by rfl⟩ : syracuseStep 661051 = 991577) B991577
theorem B1414841 : Blo 519798 1414841 := bstep (se 2 (by rfl) ⟨530565, by rfl⟩ : syracuseStep 1414841 = 1061131) B1061131
theorem B3348161 : Blo 519798 3348161 := bstep (se 2 (by rfl) ⟨1255560, by rfl⟩ : syracuseStep 3348161 = 2511121) B2511121
theorem B1480463 : Blo 519798 1480463 := bstep (se 1 (by rfl) ⟨1110347, by rfl⟩ : syracuseStep 1480463 = 2220695) B2220695
theorem B1316695 : Blo 519798 1316695 := bstep (se 1 (by rfl) ⟨987521, by rfl⟩ : syracuseStep 1316695 = 1975043) B1975043
theorem B1873799 : Blo 519798 1873799 := bstep (se 1 (by rfl) ⟨1405349, by rfl⟩ : syracuseStep 1873799 = 2810699) B2810699
theorem B1251371 : Blo 519798 1251371 := bstep (se 1 (by rfl) ⟨938528, by rfl⟩ : syracuseStep 1251371 = 1877057) B1877057
theorem B661547 : Blo 519798 661547 := bstep (se 1 (by rfl) ⟨496160, by rfl⟩ : syracuseStep 661547 = 992321) B992321
theorem B1284211 : Blo 519798 1284211 := bstep (se 1 (by rfl) ⟨963158, by rfl⟩ : syracuseStep 1284211 = 1926317) B1926317
theorem B1316999 : Blo 519798 1316999 := bstep (se 1 (by rfl) ⟨987749, by rfl⟩ : syracuseStep 1316999 = 1975499) B1975499
theorem B1317131 : Blo 519798 1317131 := bstep (se 1 (by rfl) ⟨987848, by rfl⟩ : syracuseStep 1317131 = 1975697) B1975697
theorem B989587 : Blo 519798 989587 := bstep (se 1 (by rfl) ⟨742190, by rfl⟩ : syracuseStep 989587 = 1484381) B1484381
theorem B662023 : Blo 519798 662023 := bstep (se 1 (by rfl) ⟨496517, by rfl⟩ : syracuseStep 662023 = 993035) B993035
theorem B1874461 : Blo 519798 1874461 := bstep (se 3 (by rfl) ⟨351461, by rfl⟩ : syracuseStep 1874461 = 702923) B702923
theorem B989815 : Blo 519798 989815 := bstep (se 1 (by rfl) ⟨742361, by rfl⟩ : syracuseStep 989815 = 1484723) B1484723
theorem B10066625 : Blo 519798 10066625 := bstep (se 2 (by rfl) ⟨3774984, by rfl⟩ : syracuseStep 10066625 = 7549969) B7549969
theorem B1317647 : Blo 519798 1317647 := bstep (se 1 (by rfl) ⟨988235, by rfl⟩ : syracuseStep 1317647 = 1976471) B1976471
theorem B10033955 : Blo 519798 10033955 := bstep (se 1 (by rfl) ⟨7525466, by rfl⟩ : syracuseStep 10033955 = 15050933) B15050933
theorem B2235251 : Blo 519798 2235251 := bstep (se 1 (by rfl) ⟨1676438, by rfl⟩ : syracuseStep 2235251 = 3352877) B3352877
theorem B1481591 : Blo 519798 1481591 := bstep (se 1 (by rfl) ⟨1111193, by rfl⟩ : syracuseStep 1481591 = 2222387) B2222387
theorem B1317779 : Blo 519798 1317779 := bstep (se 1 (by rfl) ⟨988334, by rfl⟩ : syracuseStep 1317779 = 1976669) B1976669
theorem B662519 : Blo 519798 662519 := bstep (se 1 (by rfl) ⟨496889, by rfl⟩ : syracuseStep 662519 = 993779) B993779
theorem B662671 : Blo 519798 662671 := bstep (se 1 (by rfl) ⟨497003, by rfl⟩ : syracuseStep 662671 = 994007) B994007
theorem B2235593 : Blo 519798 2235593 := bstep (se 2 (by rfl) ⟨838347, by rfl⟩ : syracuseStep 2235593 = 1676695) B1676695
theorem B662843 : Blo 519798 662843 := bstep (se 1 (by rfl) ⟨497132, by rfl⟩ : syracuseStep 662843 = 994265) B994265
theorem B1252793 : Blo 519798 1252793 := bstep (se 2 (by rfl) ⟨469797, by rfl⟩ : syracuseStep 1252793 = 939595) B939595
theorem B2235833 : Blo 519798 2235833 := bstep (se 2 (by rfl) ⟨838437, by rfl⟩ : syracuseStep 2235833 = 1676875) B1676875
theorem B2039357 : Blo 519798 2039357 := bstep (se 3 (by rfl) ⟨382379, by rfl⟩ : syracuseStep 2039357 = 764759) B764759
theorem B2236193 : Blo 519798 2236193 := bstep (se 2 (by rfl) ⟨838572, by rfl⟩ : syracuseStep 2236193 = 1677145) B1677145
theorem B45817649 : Blo 519798 45817649 := bstep (se 2 (by rfl) ⟨17181618, by rfl⟩ : syracuseStep 45817649 = 34363237) B34363237
theorem B1318913 : Blo 519798 1318913 := bstep (se 2 (by rfl) ⟨494592, by rfl⟩ : syracuseStep 1318913 = 989185) B989185
theorem B1581089 : Blo 519798 1581089 := bstep (se 2 (by rfl) ⟨592908, by rfl⟩ : syracuseStep 1581089 = 1185817) B1185817
theorem B761899 : Blo 519798 761899 := bstep (se 1 (by rfl) ⟨571424, by rfl⟩ : syracuseStep 761899 = 1142849) B1142849
theorem B1581191 : Blo 519798 1581191 := bstep (se 1 (by rfl) ⟨1185893, by rfl⟩ : syracuseStep 1581191 = 2371787) B2371787
theorem B991379 : Blo 519798 991379 := bstep (se 1 (by rfl) ⟨743534, by rfl⟩ : syracuseStep 991379 = 1487069) B1487069
theorem B1253561 : Blo 519798 1253561 := bstep (se 2 (by rfl) ⟨470085, by rfl⟩ : syracuseStep 1253561 = 940171) B940171
theorem B991433 : Blo 519798 991433 := bstep (se 2 (by rfl) ⟨371787, by rfl⟩ : syracuseStep 991433 = 743575) B743575
theorem B991531 : Blo 519798 991531 := bstep (se 1 (by rfl) ⟨743648, by rfl⟩ : syracuseStep 991531 = 1487297) B1487297
theorem B1319287 : Blo 519798 1319287 := bstep (se 1 (by rfl) ⟨989465, by rfl⟩ : syracuseStep 1319287 = 1978931) B1978931
theorem B3350929 : Blo 519798 3350929 := bstep (se 2 (by rfl) ⟨1256598, by rfl⟩ : syracuseStep 3350929 = 2513197) B2513197
theorem B1483265 : Blo 519798 1483265 := bstep (se 2 (by rfl) ⟨556224, by rfl⟩ : syracuseStep 1483265 = 1112449) B1112449
theorem B991759 : Blo 519798 991759 := bstep (se 1 (by rfl) ⟨743819, by rfl⟩ : syracuseStep 991759 = 1487639) B1487639
theorem B1876567 : Blo 519798 1876567 := bstep (se 1 (by rfl) ⟨1407425, by rfl⟩ : syracuseStep 1876567 = 2814851) B2814851
theorem B1483379 : Blo 519798 1483379 := bstep (se 1 (by rfl) ⟨1112534, by rfl⟩ : syracuseStep 1483379 = 2225069) B2225069
theorem B1254023 : Blo 519798 1254023 := bstep (se 1 (by rfl) ⟨940517, by rfl⟩ : syracuseStep 1254023 = 1881035) B1881035
theorem B5939891 : Blo 519798 5939891 := bstep (se 1 (by rfl) ⟨4454918, by rfl⟩ : syracuseStep 5939891 = 8909837) B8909837
theorem B2237165 : Blo 519798 2237165 := bstep (se 3 (by rfl) ⟨419468, by rfl⟩ : syracuseStep 2237165 = 838937) B838937
theorem B1876769 : Blo 519798 1876769 := bstep (se 2 (by rfl) ⟨703788, by rfl⟩ : syracuseStep 1876769 = 1407577) B1407577
theorem B1319723 : Blo 519798 1319723 := bstep (se 1 (by rfl) ⟨989792, by rfl⟩ : syracuseStep 1319723 = 1979585) B1979585
theorem B1975225 : Blo 519798 1975225 := bstep (se 2 (by rfl) ⟨740709, by rfl⟩ : syracuseStep 1975225 = 1481419) B1481419
theorem B1483721 : Blo 519798 1483721 := bstep (se 2 (by rfl) ⟨556395, by rfl⟩ : syracuseStep 1483721 = 1112791) B1112791
theorem B1320563 : Blo 519798 1320563 := bstep (se 1 (by rfl) ⟨990422, by rfl⟩ : syracuseStep 1320563 = 1980845) B1980845
theorem B1320583 : Blo 519798 1320583 := bstep (se 1 (by rfl) ⟨990437, by rfl⟩ : syracuseStep 1320583 = 1980875) B1980875
theorem B1320857 : Blo 519798 1320857 := bstep (se 2 (by rfl) ⟨495321, by rfl⟩ : syracuseStep 1320857 = 990643) B990643
theorem B993323 : Blo 519798 993323 := bstep (se 1 (by rfl) ⟨744992, by rfl⟩ : syracuseStep 993323 = 1489985) B1489985
theorem B1321019 : Blo 519798 1321019 := bstep (se 1 (by rfl) ⟨990764, by rfl⟩ : syracuseStep 1321019 = 1981529) B1981529
theorem B1321231 : Blo 519798 1321231 := bstep (se 1 (by rfl) ⟨990923, by rfl⟩ : syracuseStep 1321231 = 1981847) B1981847
theorem B1321505 : Blo 519798 1321505 := bstep (se 2 (by rfl) ⟨495564, by rfl⟩ : syracuseStep 1321505 = 991129) B991129
theorem B1780481 : Blo 519798 1780481 := bstep (se 2 (by rfl) ⟨667680, by rfl⟩ : syracuseStep 1780481 = 1335361) B1335361
theorem B1485611 : Blo 519798 1485611 := bstep (se 1 (by rfl) ⟨1114208, by rfl⟩ : syracuseStep 1485611 = 2228417) B2228417
theorem B2632499 : Blo 519798 2632499 := bstep (se 1 (by rfl) ⟨1974374, by rfl⟩ : syracuseStep 2632499 = 3948749) B3948749
theorem B11447203 : Blo 519798 11447203 := bstep (se 1 (by rfl) ⟨8585402, by rfl⟩ : syracuseStep 11447203 = 17170805) B17170805
theorem B1485839 : Blo 519798 1485839 := bstep (se 1 (by rfl) ⟨1114379, by rfl⟩ : syracuseStep 1485839 = 2228759) B2228759
theorem B2632823 : Blo 519798 2632823 := bstep (se 1 (by rfl) ⟨1974617, by rfl⟩ : syracuseStep 2632823 = 3949235) B3949235
theorem B1256791 : Blo 519798 1256791 := bstep (se 1 (by rfl) ⟨942593, by rfl⟩ : syracuseStep 1256791 = 1885187) B1885187
theorem B1322507 : Blo 519798 1322507 := bstep (se 1 (by rfl) ⟨991880, by rfl⟩ : syracuseStep 1322507 = 1983761) B1983761
theorem B1879595 : Blo 519798 1879595 := bstep (se 1 (by rfl) ⟨1409696, by rfl⟩ : syracuseStep 1879595 = 2819393) B2819393
theorem B1060499 : Blo 519798 1060499 := bstep (se 1 (by rfl) ⟨795374, by rfl⟩ : syracuseStep 1060499 = 1590749) B1590749
theorem B1978127 : Blo 519798 1978127 := bstep (se 1 (by rfl) ⟨1483595, by rfl⟩ : syracuseStep 1978127 = 2967191) B2967191
theorem B6041623 : Blo 519798 6041623 := bstep (se 1 (by rfl) ⟨4531217, by rfl⟩ : syracuseStep 6041623 = 9062435) B9062435
theorem B2633795 : Blo 519798 2633795 := bstep (se 1 (by rfl) ⟨1975346, by rfl⟩ : syracuseStep 2633795 = 3950693) B3950693
theorem B1323155 : Blo 519798 1323155 := bstep (se 1 (by rfl) ⟨992366, by rfl⟩ : syracuseStep 1323155 = 1984733) B1984733
theorem B2502971 : Blo 519798 2502971 := bstep (se 1 (by rfl) ⟨1877228, by rfl⟩ : syracuseStep 2502971 = 3754457) B3754457
theorem B1585469 : Blo 519798 1585469 := bstep (se 3 (by rfl) ⟨297275, by rfl⟩ : syracuseStep 1585469 = 594551) B594551
theorem B2634119 : Blo 519798 2634119 := bstep (se 1 (by rfl) ⟨1975589, by rfl⟩ : syracuseStep 2634119 = 3951179) B3951179
theorem B1487251 : Blo 519798 1487251 := bstep (se 1 (by rfl) ⟨1115438, by rfl⟩ : syracuseStep 1487251 = 2230877) B2230877
theorem B1323449 : Blo 519798 1323449 := bstep (se 2 (by rfl) ⟨496293, by rfl⟩ : syracuseStep 1323449 = 992587) B992587
theorem B1487479 : Blo 519798 1487479 := bstep (se 1 (by rfl) ⟨1115609, by rfl⟩ : syracuseStep 1487479 = 2231219) B2231219
theorem B537275 : Blo 519798 537275 := bstep (se 1 (by rfl) ⟨402956, by rfl⟩ : syracuseStep 537275 = 805913) B805913
theorem B2962291 : Blo 519798 2962291 := bstep (se 1 (by rfl) ⟨2221718, by rfl⟩ : syracuseStep 2962291 = 4443437) B4443437
theorem B1192889 : Blo 519798 1192889 := bstep (se 2 (by rfl) ⟨447333, by rfl⟩ : syracuseStep 1192889 = 894667) B894667
theorem B1324147 : Blo 519798 1324147 := bstep (se 1 (by rfl) ⟨993110, by rfl⟩ : syracuseStep 1324147 = 1986221) B1986221
theorem B832697 : Blo 519798 832697 := bstep (se 2 (by rfl) ⟨312261, by rfl⟩ : syracuseStep 832697 = 624523) B624523
theorem B1324289 : Blo 519798 1324289 := bstep (se 2 (by rfl) ⟨496608, by rfl⟩ : syracuseStep 1324289 = 993217) B993217
theorem B1324745 : Blo 519798 1324745 := bstep (se 2 (by rfl) ⟨496779, by rfl⟩ : syracuseStep 1324745 = 993559) B993559
theorem B2111233 : Blo 519798 2111233 := bstep (se 2 (by rfl) ⟨791712, by rfl⟩ : syracuseStep 2111233 = 1583425) B1583425
theorem B9647923 : Blo 519798 9647923 := bstep (se 1 (by rfl) ⟨7235942, by rfl⟩ : syracuseStep 9647923 = 14471885) B14471885
theorem B1488755 : Blo 519798 1488755 := bstep (se 1 (by rfl) ⟨1116566, by rfl⟩ : syracuseStep 1488755 = 2233133) B2233133
theorem B1325099 : Blo 519798 1325099 := bstep (se 1 (by rfl) ⟨993824, by rfl⟩ : syracuseStep 1325099 = 1987649) B1987649
theorem B1489097 : Blo 519798 1489097 := bstep (se 2 (by rfl) ⟨558411, by rfl⟩ : syracuseStep 1489097 = 1116823) B1116823
theorem B2963749 : Blo 519798 2963749 := bstep (se 4 (by rfl) ⟨277851, by rfl⟩ : syracuseStep 2963749 = 555703) B555703
theorem B1489211 : Blo 519798 1489211 := bstep (se 1 (by rfl) ⟨1116908, by rfl⟩ : syracuseStep 1489211 = 2233817) B2233817
theorem B2505107 : Blo 519798 2505107 := bstep (se 1 (by rfl) ⟨1878830, by rfl⟩ : syracuseStep 2505107 = 3757661) B3757661
theorem B1489337 : Blo 519798 1489337 := bstep (se 2 (by rfl) ⟨558501, by rfl⟩ : syracuseStep 1489337 = 1117003) B1117003
theorem B2505163 : Blo 519798 2505163 := bstep (se 1 (by rfl) ⟨1878872, by rfl⟩ : syracuseStep 2505163 = 3757745) B3757745
theorem B2505277 : Blo 519798 2505277 := bstep (se 3 (by rfl) ⟨469739, by rfl⟩ : syracuseStep 2505277 = 939479) B939479
theorem B5356211 : Blo 519798 5356211 := bstep (se 1 (by rfl) ⟨4017158, by rfl⟩ : syracuseStep 5356211 = 8034317) B8034317
theorem B2964275 : Blo 519798 2964275 := bstep (se 1 (by rfl) ⟨2223206, by rfl⟩ : syracuseStep 2964275 = 4446413) B4446413
theorem B1882939 : Blo 519798 1882939 := bstep (se 1 (by rfl) ⟨1412204, by rfl⟩ : syracuseStep 1882939 = 2824409) B2824409
theorem B1981331 : Blo 519798 1981331 := bstep (se 1 (by rfl) ⟨1485998, by rfl⟩ : syracuseStep 1981331 = 2971997) B2971997
theorem B932879 : Blo 519798 932879 := bstep (se 1 (by rfl) ⟨699659, by rfl⟩ : syracuseStep 932879 = 1399319) B1399319
theorem B2375065 : Blo 519798 2375065 := bstep (se 2 (by rfl) ⟨890649, by rfl⟩ : syracuseStep 2375065 = 1781299) B1781299
theorem B2571895 : Blo 519798 2571895 := bstep (se 1 (by rfl) ⟨1928921, by rfl⟩ : syracuseStep 2571895 = 3857843) B3857843
theorem B2637683 : Blo 519798 2637683 := bstep (se 1 (by rfl) ⟨1978262, by rfl⟩ : syracuseStep 2637683 = 3956525) B3956525
theorem B2670635 : Blo 519798 2670635 := bstep (se 1 (by rfl) ⟨2002976, by rfl⟩ : syracuseStep 2670635 = 4005953) B4005953
theorem B1490987 : Blo 519798 1490987 := bstep (se 1 (by rfl) ⟨1118240, by rfl⟩ : syracuseStep 1490987 = 2236481) B2236481
theorem B2965733 : Blo 519798 2965733 := bstep (se 4 (by rfl) ⟨278037, by rfl⟩ : syracuseStep 2965733 = 556075) B556075
theorem B2638169 : Blo 519798 2638169 := bstep (se 2 (by rfl) ⟨989313, by rfl⟩ : syracuseStep 2638169 = 1978627) B1978627
theorem B5030237 : Blo 519798 5030237 := bstep (se 3 (by rfl) ⟨943169, by rfl⟩ : syracuseStep 5030237 = 1886339) B1886339
theorem B4014521 : Blo 519798 4014521 := bstep (se 2 (by rfl) ⟨1505445, by rfl⟩ : syracuseStep 4014521 = 3010891) B3010891
theorem B1982987 : Blo 519798 1982987 := bstep (se 1 (by rfl) ⟨1487240, by rfl⟩ : syracuseStep 1982987 = 2974481) B2974481
theorem B1590359 : Blo 519798 1590359 := bstep (se 1 (by rfl) ⟨1192769, by rfl⟩ : syracuseStep 1590359 = 2385539) B2385539
theorem B836983 : Blo 519798 836983 := bstep (se 1 (by rfl) ⟨627737, by rfl⟩ : syracuseStep 836983 = 1255475) B1255475
theorem B5031467 : Blo 519798 5031467 := bstep (se 1 (by rfl) ⟨3773600, by rfl⟩ : syracuseStep 5031467 = 7547201) B7547201
theorem B32097869 : Blo 519798 32097869 := bstep (se 3 (by rfl) ⟨6018350, by rfl⟩ : syracuseStep 32097869 = 12036701) B12036701
theorem B136726679 : Blo 519798 136726679 := bstep (se 1 (by rfl) ⟨102545009, by rfl⟩ : syracuseStep 136726679 = 205090019) B205090019
theorem B2672833 : Blo 519798 2672833 := bstep (se 2 (by rfl) ⟨1002312, by rfl⟩ : syracuseStep 2672833 = 2004625) B2004625
theorem B1755539 : Blo 519798 1755539 := bstep (se 1 (by rfl) ⟨1316654, by rfl⟩ : syracuseStep 1755539 = 2633309) B2633309
theorem B2640275 : Blo 519798 2640275 := bstep (se 1 (by rfl) ⟨1980206, by rfl⟩ : syracuseStep 2640275 = 3960413) B3960413
theorem B4508227 : Blo 519798 4508227 := bstep (se 1 (by rfl) ⟨3381170, by rfl⟩ : syracuseStep 4508227 = 6762341) B6762341
theorem B1592075 : Blo 519798 1592075 := bstep (se 1 (by rfl) ⟨1194056, by rfl⟩ : syracuseStep 1592075 = 2388113) B2388113
theorem B28658447 : Blo 519798 28658447 := bstep (se 1 (by rfl) ⟨21493835, by rfl⟩ : syracuseStep 28658447 = 42987671) B42987671
theorem B937145 : Blo 519798 937145 := bstep (se 2 (by rfl) ⟨351429, by rfl⟩ : syracuseStep 937145 = 702859) B702859
theorem B740539 : Blo 519798 740539 := bstep (se 1 (by rfl) ⟨555404, by rfl⟩ : syracuseStep 740539 = 1110809) B1110809
theorem B8572517 : Blo 519798 8572517 := bstep (se 4 (by rfl) ⟨803673, by rfl⟩ : syracuseStep 8572517 = 1607347) B1607347
theorem B740983 : Blo 519798 740983 := bstep (se 1 (by rfl) ⟨555737, by rfl⟩ : syracuseStep 740983 = 1111475) B1111475
theorem B2707145 : Blo 519798 2707145 := bstep (se 2 (by rfl) ⟨1015179, by rfl⟩ : syracuseStep 2707145 = 2030359) B2030359
theorem B1756943 : Blo 519798 1756943 := bstep (se 1 (by rfl) ⟨1317707, by rfl⟩ : syracuseStep 1756943 = 2635415) B2635415
theorem B2510813 : Blo 519798 2510813 := bstep (se 3 (by rfl) ⟨470777, by rfl⟩ : syracuseStep 2510813 = 941555) B941555
theorem B1757213 : Blo 519798 1757213 := bstep (se 3 (by rfl) ⟨329477, by rfl⟩ : syracuseStep 1757213 = 658955) B658955
theorem B1986875 : Blo 519798 1986875 := bstep (se 1 (by rfl) ⟨1490156, by rfl⟩ : syracuseStep 1986875 = 2980313) B2980313
theorem B741803 : Blo 519798 741803 := bstep (se 1 (by rfl) ⟨556352, by rfl⟩ : syracuseStep 741803 = 1112705) B1112705
theorem B7525057 : Blo 519798 7525057 := bstep (se 2 (by rfl) ⟨2821896, by rfl⟩ : syracuseStep 7525057 = 5643793) B5643793
theorem B1987361 : Blo 519798 1987361 := bstep (se 2 (by rfl) ⟨745260, by rfl⟩ : syracuseStep 1987361 = 1490521) B1490521
theorem B1758617 : Blo 519798 1758617 := bstep (se 2 (by rfl) ⟨659481, by rfl⟩ : syracuseStep 1758617 = 1318963) B1318963
theorem B2643353 : Blo 519798 2643353 := bstep (se 2 (by rfl) ⟨991257, by rfl⟩ : syracuseStep 2643353 = 1982515) B1982515
theorem B1988333 : Blo 519798 1988333 := bstep (se 3 (by rfl) ⟨372812, by rfl⟩ : syracuseStep 1988333 = 745625) B745625
theorem B6674177 : Blo 519798 6674177 := bstep (se 2 (by rfl) ⟨2502816, by rfl⟩ : syracuseStep 6674177 = 5005633) B5005633
theorem B1988651 : Blo 519798 1988651 := bstep (se 1 (by rfl) ⟨1491488, by rfl⟩ : syracuseStep 1988651 = 2982977) B2982977
theorem B1759319 : Blo 519798 1759319 := bstep (se 1 (by rfl) ⟨1319489, by rfl⟩ : syracuseStep 1759319 = 2638979) B2638979
theorem B16898165 : Blo 519798 16898165 := bstep (se 5 (by rfl) ⟨792101, by rfl⟩ : syracuseStep 16898165 = 1584203) B1584203
theorem B743671 : Blo 519798 743671 := bstep (se 1 (by rfl) ⟨557753, by rfl⟩ : syracuseStep 743671 = 1115507) B1115507
theorem B2677043 : Blo 519798 2677043 := bstep (se 1 (by rfl) ⟨2007782, by rfl⟩ : syracuseStep 2677043 = 4015565) B4015565
theorem B1169783 : Blo 519798 1169783 := bstep (se 1 (by rfl) ⟨877337, by rfl⟩ : syracuseStep 1169783 = 1754675) B1754675
theorem B1169963 : Blo 519798 1169963 := bstep (se 1 (by rfl) ⟨877472, by rfl⟩ : syracuseStep 1169963 = 1754945) B1754945
theorem B1759805 : Blo 519798 1759805 := bstep (se 3 (by rfl) ⟨329963, by rfl⟩ : syracuseStep 1759805 = 659927) B659927
theorem B3758669 : Blo 519798 3758669 := bstep (se 3 (by rfl) ⟨704750, by rfl⟩ : syracuseStep 3758669 = 1409501) B1409501
theorem B1170323 : Blo 519798 1170323 := bstep (se 1 (by rfl) ⟨877742, by rfl⟩ : syracuseStep 1170323 = 1755485) B1755485
theorem B1170377 : Blo 519798 1170377 := bstep (se 2 (by rfl) ⟨438891, by rfl⟩ : syracuseStep 1170377 = 877783) B877783
theorem B744719 : Blo 519798 744719 := bstep (se 1 (by rfl) ⟨558539, by rfl⟩ : syracuseStep 744719 = 1117079) B1117079
theorem B4447811 : Blo 519798 4447811 := bstep (se 1 (by rfl) ⟨3335858, by rfl⟩ : syracuseStep 4447811 = 6671717) B6671717
theorem B745033 : Blo 519798 745033 := bstep (se 2 (by rfl) ⟨279387, by rfl⟩ : syracuseStep 745033 = 558775) B558775
theorem B1171079 : Blo 519798 1171079 := bstep (se 1 (by rfl) ⟨878309, by rfl⟩ : syracuseStep 1171079 = 1756619) B1756619
theorem B2973455 : Blo 519798 2973455 := bstep (se 1 (by rfl) ⟨2230091, by rfl⟩ : syracuseStep 2973455 = 4460183) B4460183
theorem B1171259 : Blo 519798 1171259 := bstep (se 1 (by rfl) ⟨878444, by rfl⟩ : syracuseStep 1171259 = 1756889) B1756889
theorem B3170137 : Blo 519798 3170137 := bstep (se 2 (by rfl) ⟨1188801, by rfl⟩ : syracuseStep 3170137 = 2377603) B2377603
theorem B941959 : Blo 519798 941959 := bstep (se 1 (by rfl) ⟨706469, by rfl⟩ : syracuseStep 941959 = 1412939) B1412939
theorem B1171385 : Blo 519798 1171385 := bstep (se 2 (by rfl) ⟨439269, by rfl⟩ : syracuseStep 1171385 = 878539) B878539
theorem B1761209 : Blo 519798 1761209 := bstep (se 2 (by rfl) ⟨660453, by rfl⟩ : syracuseStep 1761209 = 1320907) B1320907
theorem B2645945 : Blo 519798 2645945 := bstep (se 2 (by rfl) ⟨992229, by rfl⟩ : syracuseStep 2645945 = 1984459) B1984459
theorem B1171727 : Blo 519798 1171727 := bstep (se 1 (by rfl) ⟨878795, by rfl⟩ : syracuseStep 1171727 = 1757591) B1757591
theorem B1171745 : Blo 519798 1171745 := bstep (se 2 (by rfl) ⟨439404, by rfl⟩ : syracuseStep 1171745 = 878809) B878809
theorem B2220473 : Blo 519798 2220473 := bstep (se 2 (by rfl) ⟨832677, by rfl⟩ : syracuseStep 2220473 = 1665355) B1665355
theorem B1761803 : Blo 519798 1761803 := bstep (se 1 (by rfl) ⟨1321352, by rfl⟩ : syracuseStep 1761803 = 2642705) B2642705
theorem B16114211 : Blo 519798 16114211 := bstep (se 1 (by rfl) ⟨12085658, by rfl⟩ : syracuseStep 16114211 = 24171317) B24171317
theorem B1172087 : Blo 519798 1172087 := bstep (se 1 (by rfl) ⟨879065, by rfl⟩ : syracuseStep 1172087 = 1758131) B1758131
theorem B1761911 : Blo 519798 1761911 := bstep (se 1 (by rfl) ⟨1321433, by rfl⟩ : syracuseStep 1761911 = 2642867) B2642867
theorem B1172267 : Blo 519798 1172267 := bstep (se 1 (by rfl) ⟨879200, by rfl⟩ : syracuseStep 1172267 = 1758401) B1758401
theorem B10838947 : Blo 519798 10838947 := bstep (se 1 (by rfl) ⟨8129210, by rfl⟩ : syracuseStep 10838947 = 16258421) B16258421
theorem B877513 : Blo 519798 877513 := bstep (se 2 (by rfl) ⟨329067, by rfl⟩ : syracuseStep 877513 = 658135) B658135
theorem B2548739 : Blo 519798 2548739 := bstep (se 1 (by rfl) ⟨1911554, by rfl⟩ : syracuseStep 2548739 = 3823109) B3823109
theorem B1172627 : Blo 519798 1172627 := bstep (se 1 (by rfl) ⟨879470, by rfl⟩ : syracuseStep 1172627 = 1758941) B1758941
theorem B2974913 : Blo 519798 2974913 := bstep (se 2 (by rfl) ⟨1115592, by rfl⟩ : syracuseStep 2974913 = 2231185) B2231185
theorem B1172681 : Blo 519798 1172681 := bstep (se 2 (by rfl) ⟨439755, by rfl⟩ : syracuseStep 1172681 = 879511) B879511
theorem B1762505 : Blo 519798 1762505 := bstep (se 2 (by rfl) ⟨660939, by rfl⟩ : syracuseStep 1762505 = 1321879) B1321879
theorem B2647241 : Blo 519798 2647241 := bstep (se 2 (by rfl) ⟨992715, by rfl⟩ : syracuseStep 2647241 = 1985431) B1985431
theorem B779705 : Blo 519798 779705 := bstep (se 2 (by rfl) ⟨292389, by rfl⟩ : syracuseStep 779705 = 584779) B584779
theorem B779783 : Blo 519798 779783 := bstep (se 1 (by rfl) ⟨584837, by rfl⟩ : syracuseStep 779783 = 1169675) B1169675
theorem B2516503 : Blo 519798 2516503 := bstep (se 1 (by rfl) ⟨1887377, by rfl⟩ : syracuseStep 2516503 = 3774755) B3774755
theorem B779819 : Blo 519798 779819 := bstep (se 1 (by rfl) ⟨584864, by rfl⟩ : syracuseStep 779819 = 1169729) B1169729
theorem B779849 : Blo 519798 779849 := bstep (se 2 (by rfl) ⟨292443, by rfl⟩ : syracuseStep 779849 = 584887) B584887
theorem B7530083 : Blo 519798 7530083 := bstep (se 1 (by rfl) ⟨5647562, by rfl⟩ : syracuseStep 7530083 = 11295125) B11295125
theorem B878215 : Blo 519798 878215 := bstep (se 1 (by rfl) ⟨658661, by rfl⟩ : syracuseStep 878215 = 1317323) B1317323
theorem B779963 : Blo 519798 779963 := bstep (se 1 (by rfl) ⟨584972, by rfl⟩ : syracuseStep 779963 = 1169945) B1169945
theorem B780023 : Blo 519798 780023 := bstep (se 1 (by rfl) ⟨585017, by rfl⟩ : syracuseStep 780023 = 1170035) B1170035
theorem B780047 : Blo 519798 780047 := bstep (se 1 (by rfl) ⟨585035, by rfl⟩ : syracuseStep 780047 = 1170071) B1170071
theorem B780089 : Blo 519798 780089 := bstep (se 2 (by rfl) ⟨292533, by rfl⟩ : syracuseStep 780089 = 585067) B585067
theorem B780167 : Blo 519798 780167 := bstep (se 1 (by rfl) ⟨585125, by rfl⟩ : syracuseStep 780167 = 1170251) B1170251
theorem B1173383 : Blo 519798 1173383 := bstep (se 1 (by rfl) ⟨880037, by rfl⟩ : syracuseStep 1173383 = 1760075) B1760075
theorem B1763207 : Blo 519798 1763207 := bstep (se 1 (by rfl) ⟨1322405, by rfl⟩ : syracuseStep 1763207 = 2644811) B2644811
theorem B780203 : Blo 519798 780203 := bstep (se 1 (by rfl) ⟨585152, by rfl⟩ : syracuseStep 780203 = 1170305) B1170305
theorem B780233 : Blo 519798 780233 := bstep (se 2 (by rfl) ⟨292587, by rfl⟩ : syracuseStep 780233 = 585175) B585175
theorem B780347 : Blo 519798 780347 := bstep (se 1 (by rfl) ⟨585260, by rfl⟩ : syracuseStep 780347 = 1170521) B1170521
theorem B1173563 : Blo 519798 1173563 := bstep (se 1 (by rfl) ⟨880172, by rfl⟩ : syracuseStep 1173563 = 1760345) B1760345
theorem B780407 : Blo 519798 780407 := bstep (se 1 (by rfl) ⟨585305, by rfl⟩ : syracuseStep 780407 = 1170611) B1170611
theorem B780431 : Blo 519798 780431 := bstep (se 1 (by rfl) ⟨585323, by rfl⟩ : syracuseStep 780431 = 1170647) B1170647
theorem B780473 : Blo 519798 780473 := bstep (se 2 (by rfl) ⟨292677, by rfl⟩ : syracuseStep 780473 = 585355) B585355
theorem B1173689 : Blo 519798 1173689 := bstep (se 2 (by rfl) ⟨440133, by rfl⟩ : syracuseStep 1173689 = 880267) B880267
theorem B1763585 : Blo 519798 1763585 := bstep (se 2 (by rfl) ⟨661344, by rfl⟩ : syracuseStep 1763585 = 1322689) B1322689
theorem B780551 : Blo 519798 780551 := bstep (se 1 (by rfl) ⟨585413, by rfl⟩ : syracuseStep 780551 = 1170827) B1170827
theorem B878863 : Blo 519798 878863 := bstep (se 1 (by rfl) ⟨659147, by rfl⟩ : syracuseStep 878863 = 1318295) B1318295
theorem B780587 : Blo 519798 780587 := bstep (se 1 (by rfl) ⟨585440, by rfl⟩ : syracuseStep 780587 = 1170881) B1170881
theorem B4778299 : Blo 519798 4778299 := bstep (se 1 (by rfl) ⟨3583724, by rfl⟩ : syracuseStep 4778299 = 7167449) B7167449
theorem B780617 : Blo 519798 780617 := bstep (se 2 (by rfl) ⟨292731, by rfl⟩ : syracuseStep 780617 = 585463) B585463
theorem B2222471 : Blo 519798 2222471 := bstep (se 1 (by rfl) ⟨1666853, by rfl⟩ : syracuseStep 2222471 = 3333707) B3333707
theorem B780731 : Blo 519798 780731 := bstep (se 1 (by rfl) ⟨585548, by rfl⟩ : syracuseStep 780731 = 1171097) B1171097
theorem B780791 : Blo 519798 780791 := bstep (se 1 (by rfl) ⟨585593, by rfl⟩ : syracuseStep 780791 = 1171187) B1171187
theorem B780815 : Blo 519798 780815 := bstep (se 1 (by rfl) ⟨585611, by rfl⟩ : syracuseStep 780815 = 1171223) B1171223
theorem B1174031 : Blo 519798 1174031 := bstep (se 1 (by rfl) ⟨880523, by rfl⟩ : syracuseStep 1174031 = 1761047) B1761047
theorem B1174049 : Blo 519798 1174049 := bstep (se 2 (by rfl) ⟨440268, by rfl⟩ : syracuseStep 1174049 = 880537) B880537
theorem B12839467 : Blo 519798 12839467 := bstep (se 1 (by rfl) ⟨9629600, by rfl⟩ : syracuseStep 12839467 = 19259201) B19259201
theorem B780857 : Blo 519798 780857 := bstep (se 2 (by rfl) ⟨292821, by rfl⟩ : syracuseStep 780857 = 585643) B585643
theorem B1665623 : Blo 519798 1665623 := bstep (se 1 (by rfl) ⟨1249217, by rfl⟩ : syracuseStep 1665623 = 2498435) B2498435
theorem B2222711 : Blo 519798 2222711 := bstep (se 1 (by rfl) ⟨1667033, by rfl⟩ : syracuseStep 2222711 = 3334067) B3334067
theorem B780935 : Blo 519798 780935 := bstep (se 1 (by rfl) ⟨585701, by rfl⟩ : syracuseStep 780935 = 1171403) B1171403
theorem B780971 : Blo 519798 780971 := bstep (se 1 (by rfl) ⟨585728, by rfl⟩ : syracuseStep 780971 = 1171457) B1171457
theorem B781001 : Blo 519798 781001 := bstep (se 2 (by rfl) ⟨292875, by rfl⟩ : syracuseStep 781001 = 585751) B585751
theorem B879403 : Blo 519798 879403 := bstep (se 1 (by rfl) ⟨659552, by rfl⟩ : syracuseStep 879403 = 1319105) B1319105
theorem B781115 : Blo 519798 781115 := bstep (se 1 (by rfl) ⟨585836, by rfl⟩ : syracuseStep 781115 = 1171673) B1171673
theorem B781175 : Blo 519798 781175 := bstep (se 1 (by rfl) ⟨585881, by rfl⟩ : syracuseStep 781175 = 1171763) B1171763
theorem B1174391 : Blo 519798 1174391 := bstep (se 1 (by rfl) ⟨880793, by rfl⟩ : syracuseStep 1174391 = 1761587) B1761587
theorem B3173255 : Blo 519798 3173255 := bstep (se 1 (by rfl) ⟨2379941, by rfl⟩ : syracuseStep 3173255 = 4759883) B4759883
theorem B781199 : Blo 519798 781199 := bstep (se 1 (by rfl) ⟨585899, by rfl⟩ : syracuseStep 781199 = 1171799) B1171799
theorem B781241 : Blo 519798 781241 := bstep (se 2 (by rfl) ⟨292965, by rfl⟩ : syracuseStep 781241 = 585931) B585931
theorem B879545 : Blo 519798 879545 := bstep (se 2 (by rfl) ⟨329829, by rfl⟩ : syracuseStep 879545 = 659659) B659659
theorem B781319 : Blo 519798 781319 := bstep (se 1 (by rfl) ⟨585989, by rfl⟩ : syracuseStep 781319 = 1171979) B1171979
theorem B781355 : Blo 519798 781355 := bstep (se 1 (by rfl) ⟨586016, by rfl⟩ : syracuseStep 781355 = 1172033) B1172033
theorem B1174571 : Blo 519798 1174571 := bstep (se 1 (by rfl) ⟨880928, by rfl⟩ : syracuseStep 1174571 = 1761857) B1761857
theorem B1764395 : Blo 519798 1764395 := bstep (se 1 (by rfl) ⟨1323296, by rfl⟩ : syracuseStep 1764395 = 2646593) B2646593
theorem B1305659 : Blo 519798 1305659 := bstep (se 1 (by rfl) ⟨979244, by rfl⟩ : syracuseStep 1305659 = 1958489) B1958489
theorem B781385 : Blo 519798 781385 := bstep (se 2 (by rfl) ⟨293019, by rfl⟩ : syracuseStep 781385 = 586039) B586039
theorem B781499 : Blo 519798 781499 := bstep (se 1 (by rfl) ⟨586124, by rfl⟩ : syracuseStep 781499 = 1172249) B1172249
theorem B781559 : Blo 519798 781559 := bstep (se 1 (by rfl) ⟨586169, by rfl⟩ : syracuseStep 781559 = 1172339) B1172339
theorem B781583 : Blo 519798 781583 := bstep (se 1 (by rfl) ⟨586187, by rfl⟩ : syracuseStep 781583 = 1172375) B1172375
theorem B781625 : Blo 519798 781625 := bstep (se 2 (by rfl) ⟨293109, by rfl⟩ : syracuseStep 781625 = 586219) B586219
theorem B781703 : Blo 519798 781703 := bstep (se 1 (by rfl) ⟨586277, by rfl⟩ : syracuseStep 781703 = 1172555) B1172555
theorem B585103 : Blo 519798 585103 := bstep (se 1 (by rfl) ⟨438827, by rfl⟩ : syracuseStep 585103 = 877655) B877655
theorem B1174931 : Blo 519798 1174931 := bstep (se 1 (by rfl) ⟨881198, by rfl⟩ : syracuseStep 1174931 = 1762397) B1762397
theorem B781739 : Blo 519798 781739 := bstep (se 1 (by rfl) ⟨586304, by rfl⟩ : syracuseStep 781739 = 1172609) B1172609
theorem B781769 : Blo 519798 781769 := bstep (se 2 (by rfl) ⟨293163, by rfl⟩ : syracuseStep 781769 = 586327) B586327
theorem B1174985 : Blo 519798 1174985 := bstep (se 2 (by rfl) ⟨440619, by rfl⟩ : syracuseStep 1174985 = 881239) B881239
theorem B3337757 : Blo 519798 3337757 := bstep (se 3 (by rfl) ⟨625829, by rfl⟩ : syracuseStep 3337757 = 1251659) B1251659
theorem B781883 : Blo 519798 781883 := bstep (se 1 (by rfl) ⟨586412, by rfl⟩ : syracuseStep 781883 = 1172825) B1172825
theorem B781943 : Blo 519798 781943 := bstep (se 1 (by rfl) ⟨586457, by rfl⟩ : syracuseStep 781943 = 1172915) B1172915
theorem B880247 : Blo 519798 880247 := bstep (se 1 (by rfl) ⟨660185, by rfl⟩ : syracuseStep 880247 = 1320371) B1320371
theorem B519815 : Blo 519798 519815 := bstep (se 1 (by rfl) ⟨389861, by rfl⟩ : syracuseStep 519815 = 779723) B779723
theorem B519823 : Blo 519798 519823 := bstep (se 1 (by rfl) ⟨389867, by rfl⟩ : syracuseStep 519823 = 779735) B779735
theorem B781967 : Blo 519798 781967 := bstep (se 1 (by rfl) ⟨586475, by rfl⟩ : syracuseStep 781967 = 1172951) B1172951
theorem B782009 : Blo 519798 782009 := bstep (se 2 (by rfl) ⟨293253, by rfl⟩ : syracuseStep 782009 = 586507) B586507
theorem B519867 : Blo 519798 519867 := bstep (se 1 (by rfl) ⟨389900, by rfl⟩ : syracuseStep 519867 = 779801) B779801
theorem B519943 : Blo 519798 519943 := bstep (se 1 (by rfl) ⟨389957, by rfl⟩ : syracuseStep 519943 = 779915) B779915
theorem B782087 : Blo 519798 782087 := bstep (se 1 (by rfl) ⟨586565, by rfl⟩ : syracuseStep 782087 = 1173131) B1173131
theorem B519951 : Blo 519798 519951 := bstep (se 1 (by rfl) ⟨389963, by rfl⟩ : syracuseStep 519951 = 779927) B779927
theorem B782123 : Blo 519798 782123 := bstep (se 1 (by rfl) ⟨586592, by rfl⟩ : syracuseStep 782123 = 1173185) B1173185
theorem B519995 : Blo 519798 519995 := bstep (se 1 (by rfl) ⟨389996, by rfl⟩ : syracuseStep 519995 = 779993) B779993
theorem B782153 : Blo 519798 782153 := bstep (se 2 (by rfl) ⟨293307, by rfl⟩ : syracuseStep 782153 = 586615) B586615
theorem B4452185 : Blo 519798 4452185 := bstep (se 2 (by rfl) ⟨1669569, by rfl⟩ : syracuseStep 4452185 = 3339139) B3339139
theorem B585607 : Blo 519798 585607 := bstep (se 1 (by rfl) ⟨439205, by rfl⟩ : syracuseStep 585607 = 878411) B878411
theorem B520071 : Blo 519798 520071 := bstep (se 1 (by rfl) ⟨390053, by rfl⟩ : syracuseStep 520071 = 780107) B780107
theorem B520079 : Blo 519798 520079 := bstep (se 1 (by rfl) ⟨390059, by rfl⟩ : syracuseStep 520079 = 780119) B780119
theorem B520123 : Blo 519798 520123 := bstep (se 1 (by rfl) ⟨390092, by rfl⟩ : syracuseStep 520123 = 780185) B780185
theorem B782267 : Blo 519798 782267 := bstep (se 1 (by rfl) ⟨586700, by rfl⟩ : syracuseStep 782267 = 1173401) B1173401
theorem B782327 : Blo 519798 782327 := bstep (se 1 (by rfl) ⟨586745, by rfl⟩ : syracuseStep 782327 = 1173491) B1173491
theorem B520199 : Blo 519798 520199 := bstep (se 1 (by rfl) ⟨390149, by rfl⟩ : syracuseStep 520199 = 780299) B780299
theorem B520207 : Blo 519798 520207 := bstep (se 1 (by rfl) ⟨390155, by rfl⟩ : syracuseStep 520207 = 780311) B780311
theorem B782351 : Blo 519798 782351 := bstep (se 1 (by rfl) ⟨586763, by rfl⟩ : syracuseStep 782351 = 1173527) B1173527
theorem B782393 : Blo 519798 782393 := bstep (se 2 (by rfl) ⟨293397, by rfl⟩ : syracuseStep 782393 = 586795) B586795
theorem B520251 : Blo 519798 520251 := bstep (se 1 (by rfl) ⟨390188, by rfl⟩ : syracuseStep 520251 = 780377) B780377
theorem B585787 : Blo 519798 585787 := bstep (se 1 (by rfl) ⟨439340, by rfl⟩ : syracuseStep 585787 = 878681) B878681
theorem B880699 : Blo 519798 880699 := bstep (se 1 (by rfl) ⟨660524, by rfl⟩ : syracuseStep 880699 = 1321049) B1321049
theorem B1175687 : Blo 519798 1175687 := bstep (se 1 (by rfl) ⟨881765, by rfl⟩ : syracuseStep 1175687 = 1763531) B1763531
theorem B520327 : Blo 519798 520327 := bstep (se 1 (by rfl) ⟨390245, by rfl⟩ : syracuseStep 520327 = 780491) B780491
theorem B782471 : Blo 519798 782471 := bstep (se 1 (by rfl) ⟨586853, by rfl⟩ : syracuseStep 782471 = 1173707) B1173707
theorem B520335 : Blo 519798 520335 := bstep (se 1 (by rfl) ⟨390251, by rfl⟩ : syracuseStep 520335 = 780503) B780503
theorem B782507 : Blo 519798 782507 := bstep (se 1 (by rfl) ⟨586880, by rfl⟩ : syracuseStep 782507 = 1173761) B1173761
theorem B520379 : Blo 519798 520379 := bstep (se 1 (by rfl) ⟨390284, by rfl⟩ : syracuseStep 520379 = 780569) B780569
theorem B782537 : Blo 519798 782537 := bstep (se 2 (by rfl) ⟨293451, by rfl⟩ : syracuseStep 782537 = 586903) B586903
theorem B880841 : Blo 519798 880841 := bstep (se 2 (by rfl) ⟨330315, by rfl⟩ : syracuseStep 880841 = 660631) B660631
theorem B2224385 : Blo 519798 2224385 := bstep (se 2 (by rfl) ⟨834144, by rfl⟩ : syracuseStep 2224385 = 1668289) B1668289
theorem B520455 : Blo 519798 520455 := bstep (se 1 (by rfl) ⟨390341, by rfl⟩ : syracuseStep 520455 = 780683) B780683
theorem B520463 : Blo 519798 520463 := bstep (se 1 (by rfl) ⟨390347, by rfl⟩ : syracuseStep 520463 = 780695) B780695
theorem B520507 : Blo 519798 520507 := bstep (se 1 (by rfl) ⟨390380, by rfl⟩ : syracuseStep 520507 = 780761) B780761
theorem B782651 : Blo 519798 782651 := bstep (se 1 (by rfl) ⟨586988, by rfl⟩ : syracuseStep 782651 = 1173977) B1173977
theorem B1175867 : Blo 519798 1175867 := bstep (se 1 (by rfl) ⟨881900, by rfl⟩ : syracuseStep 1175867 = 1763801) B1763801
theorem B1765691 : Blo 519798 1765691 := bstep (se 1 (by rfl) ⟨1324268, by rfl⟩ : syracuseStep 1765691 = 2648537) B2648537
theorem B782711 : Blo 519798 782711 := bstep (se 1 (by rfl) ⟨587033, by rfl⟩ : syracuseStep 782711 = 1174067) B1174067
theorem B520583 : Blo 519798 520583 := bstep (se 1 (by rfl) ⟨390437, by rfl⟩ : syracuseStep 520583 = 780875) B780875
theorem B520591 : Blo 519798 520591 := bstep (se 1 (by rfl) ⟨390443, by rfl⟩ : syracuseStep 520591 = 780887) B780887
theorem B782735 : Blo 519798 782735 := bstep (se 1 (by rfl) ⟨587051, by rfl⟩ : syracuseStep 782735 = 1174103) B1174103
theorem B782777 : Blo 519798 782777 := bstep (se 2 (by rfl) ⟨293541, by rfl⟩ : syracuseStep 782777 = 587083) B587083
theorem B1175993 : Blo 519798 1175993 := bstep (se 2 (by rfl) ⟨440997, by rfl⟩ : syracuseStep 1175993 = 881995) B881995
theorem B520635 : Blo 519798 520635 := bstep (se 1 (by rfl) ⟨390476, by rfl⟩ : syracuseStep 520635 = 780953) B780953
theorem B520711 : Blo 519798 520711 := bstep (se 1 (by rfl) ⟨390533, by rfl⟩ : syracuseStep 520711 = 781067) B781067
theorem B782855 : Blo 519798 782855 := bstep (se 1 (by rfl) ⟨587141, by rfl⟩ : syracuseStep 782855 = 1174283) B1174283
theorem B520719 : Blo 519798 520719 := bstep (se 1 (by rfl) ⟨390539, by rfl⟩ : syracuseStep 520719 = 781079) B781079
theorem B586255 : Blo 519798 586255 := bstep (se 1 (by rfl) ⟨439691, by rfl⟩ : syracuseStep 586255 = 879383) B879383
theorem B3568157 : Blo 519798 3568157 := bstep (se 3 (by rfl) ⟨669029, by rfl⟩ : syracuseStep 3568157 = 1338059) B1338059
theorem B782891 : Blo 519798 782891 := bstep (se 1 (by rfl) ⟨587168, by rfl⟩ : syracuseStep 782891 = 1174337) B1174337
theorem B520763 : Blo 519798 520763 := bstep (se 1 (by rfl) ⟨390572, by rfl⟩ : syracuseStep 520763 = 781145) B781145
theorem B782921 : Blo 519798 782921 := bstep (se 2 (by rfl) ⟨293595, by rfl⟩ : syracuseStep 782921 = 587191) B587191
theorem B1110647 : Blo 519798 1110647 := bstep (se 1 (by rfl) ⟨832985, by rfl⟩ : syracuseStep 1110647 = 1665971) B1665971
theorem B520839 : Blo 519798 520839 := bstep (se 1 (by rfl) ⟨390629, by rfl⟩ : syracuseStep 520839 = 781259) B781259
theorem B520847 : Blo 519798 520847 := bstep (se 1 (by rfl) ⟨390635, by rfl⟩ : syracuseStep 520847 = 781271) B781271
theorem B520891 : Blo 519798 520891 := bstep (se 1 (by rfl) ⟨390668, by rfl⟩ : syracuseStep 520891 = 781337) B781337
theorem B783035 : Blo 519798 783035 := bstep (se 1 (by rfl) ⟨587276, by rfl⟩ : syracuseStep 783035 = 1174553) B1174553
theorem B783095 : Blo 519798 783095 := bstep (se 1 (by rfl) ⟨587321, by rfl⟩ : syracuseStep 783095 = 1174643) B1174643
theorem B520967 : Blo 519798 520967 := bstep (se 1 (by rfl) ⟨390725, by rfl⟩ : syracuseStep 520967 = 781451) B781451
theorem B1176335 : Blo 519798 1176335 := bstep (se 1 (by rfl) ⟨882251, by rfl⟩ : syracuseStep 1176335 = 1764503) B1764503
theorem B520975 : Blo 519798 520975 := bstep (se 1 (by rfl) ⟨390731, by rfl⟩ : syracuseStep 520975 = 781463) B781463
theorem B783119 : Blo 519798 783119 := bstep (se 1 (by rfl) ⟨587339, by rfl⟩ : syracuseStep 783119 = 1174679) B1174679
theorem B1176353 : Blo 519798 1176353 := bstep (se 2 (by rfl) ⟨441132, by rfl⟩ : syracuseStep 1176353 = 882265) B882265
theorem B1766177 : Blo 519798 1766177 := bstep (se 2 (by rfl) ⟨662316, by rfl⟩ : syracuseStep 1766177 = 1324633) B1324633
theorem B783161 : Blo 519798 783161 := bstep (se 2 (by rfl) ⟨293685, by rfl⟩ : syracuseStep 783161 = 587371) B587371
theorem B521019 : Blo 519798 521019 := bstep (se 1 (by rfl) ⟨390764, by rfl⟩ : syracuseStep 521019 = 781529) B781529
theorem B521095 : Blo 519798 521095 := bstep (se 1 (by rfl) ⟨390821, by rfl⟩ : syracuseStep 521095 = 781643) B781643
theorem B783239 : Blo 519798 783239 := bstep (se 1 (by rfl) ⟨587429, by rfl⟩ : syracuseStep 783239 = 1174859) B1174859
theorem B881543 : Blo 519798 881543 := bstep (se 1 (by rfl) ⟨661157, by rfl⟩ : syracuseStep 881543 = 1322315) B1322315
theorem B521103 : Blo 519798 521103 := bstep (se 1 (by rfl) ⟨390827, by rfl⟩ : syracuseStep 521103 = 781655) B781655
theorem B783275 : Blo 519798 783275 := bstep (se 1 (by rfl) ⟨587456, by rfl⟩ : syracuseStep 783275 = 1174913) B1174913
theorem B521147 : Blo 519798 521147 := bstep (se 1 (by rfl) ⟨390860, by rfl⟩ : syracuseStep 521147 = 781721) B781721
theorem B914377 : Blo 519798 914377 := bstep (se 2 (by rfl) ⟨342891, by rfl⟩ : syracuseStep 914377 = 685783) B685783
theorem B783305 : Blo 519798 783305 := bstep (se 2 (by rfl) ⟨293739, by rfl⟩ : syracuseStep 783305 = 587479) B587479
theorem B521223 : Blo 519798 521223 := bstep (se 1 (by rfl) ⟨390917, by rfl⟩ : syracuseStep 521223 = 781835) B781835
theorem B586759 : Blo 519798 586759 := bstep (se 1 (by rfl) ⟨440069, by rfl⟩ : syracuseStep 586759 = 880139) B880139
theorem B521231 : Blo 519798 521231 := bstep (se 1 (by rfl) ⟨390923, by rfl⟩ : syracuseStep 521231 = 781847) B781847
theorem B1111099 : Blo 519798 1111099 := bstep (se 1 (by rfl) ⟨833324, by rfl⟩ : syracuseStep 1111099 = 1666649) B1666649
theorem B521275 : Blo 519798 521275 := bstep (se 1 (by rfl) ⟨390956, by rfl⟩ : syracuseStep 521275 = 781913) B781913
theorem B783419 : Blo 519798 783419 := bstep (se 1 (by rfl) ⟨587564, by rfl⟩ : syracuseStep 783419 = 1175129) B1175129
theorem B783479 : Blo 519798 783479 := bstep (se 1 (by rfl) ⟨587609, by rfl⟩ : syracuseStep 783479 = 1175219) B1175219
theorem B1176695 : Blo 519798 1176695 := bstep (se 1 (by rfl) ⟨882521, by rfl⟩ : syracuseStep 1176695 = 1765043) B1765043
theorem B521351 : Blo 519798 521351 := bstep (se 1 (by rfl) ⟨391013, by rfl⟩ : syracuseStep 521351 = 782027) B782027
theorem B521359 : Blo 519798 521359 := bstep (se 1 (by rfl) ⟨391019, by rfl⟩ : syracuseStep 521359 = 782039) B782039
theorem B783503 : Blo 519798 783503 := bstep (se 1 (by rfl) ⟨587627, by rfl⟩ : syracuseStep 783503 = 1175255) B1175255
theorem B783545 : Blo 519798 783545 := bstep (se 2 (by rfl) ⟨293829, by rfl⟩ : syracuseStep 783545 = 587659) B587659
theorem B521403 : Blo 519798 521403 := bstep (se 1 (by rfl) ⟨391052, by rfl⟩ : syracuseStep 521403 = 782105) B782105
theorem B586939 : Blo 519798 586939 := bstep (se 1 (by rfl) ⟨440204, by rfl⟩ : syracuseStep 586939 = 880409) B880409
theorem B3175661 : Blo 519798 3175661 := bstep (se 3 (by rfl) ⟨595436, by rfl⟩ : syracuseStep 3175661 = 1190873) B1190873
theorem B521479 : Blo 519798 521479 := bstep (se 1 (by rfl) ⟨391109, by rfl⟩ : syracuseStep 521479 = 782219) B782219
theorem B783623 : Blo 519798 783623 := bstep (se 1 (by rfl) ⟨587717, by rfl⟩ : syracuseStep 783623 = 1175435) B1175435
theorem B521487 : Blo 519798 521487 := bstep (se 1 (by rfl) ⟨391115, by rfl⟩ : syracuseStep 521487 = 782231) B782231
theorem B783659 : Blo 519798 783659 := bstep (se 1 (by rfl) ⟨587744, by rfl⟩ : syracuseStep 783659 = 1175489) B1175489
theorem B1176875 : Blo 519798 1176875 := bstep (se 1 (by rfl) ⟨882656, by rfl⟩ : syracuseStep 1176875 = 1765313) B1765313
theorem B521531 : Blo 519798 521531 := bstep (se 1 (by rfl) ⟨391148, by rfl⟩ : syracuseStep 521531 = 782297) B782297
theorem B783689 : Blo 519798 783689 := bstep (se 2 (by rfl) ⟨293883, by rfl⟩ : syracuseStep 783689 = 587767) B587767
theorem B1766771 : Blo 519798 1766771 := bstep (se 1 (by rfl) ⟨1325078, by rfl⟩ : syracuseStep 1766771 = 2650157) B2650157
theorem B521607 : Blo 519798 521607 := bstep (se 1 (by rfl) ⟨391205, by rfl⟩ : syracuseStep 521607 = 782411) B782411
theorem B521615 : Blo 519798 521615 := bstep (se 1 (by rfl) ⟨391211, by rfl⟩ : syracuseStep 521615 = 782423) B782423
theorem B521659 : Blo 519798 521659 := bstep (se 1 (by rfl) ⟨391244, by rfl⟩ : syracuseStep 521659 = 782489) B782489
theorem B783803 : Blo 519798 783803 := bstep (se 1 (by rfl) ⟨587852, by rfl⟩ : syracuseStep 783803 = 1175705) B1175705
theorem B783863 : Blo 519798 783863 := bstep (se 1 (by rfl) ⟨587897, by rfl⟩ : syracuseStep 783863 = 1175795) B1175795
theorem B521735 : Blo 519798 521735 := bstep (se 1 (by rfl) ⟨391301, by rfl⟩ : syracuseStep 521735 = 782603) B782603
theorem B521743 : Blo 519798 521743 := bstep (se 1 (by rfl) ⟨391307, by rfl⟩ : syracuseStep 521743 = 782615) B782615
theorem B783887 : Blo 519798 783887 := bstep (se 1 (by rfl) ⟨587915, by rfl⟩ : syracuseStep 783887 = 1175831) B1175831
theorem B882191 : Blo 519798 882191 := bstep (se 1 (by rfl) ⟨661643, by rfl⟩ : syracuseStep 882191 = 1323287) B1323287
theorem B783929 : Blo 519798 783929 := bstep (se 2 (by rfl) ⟨293973, by rfl⟩ : syracuseStep 783929 = 587947) B587947
theorem B521787 : Blo 519798 521787 := bstep (se 1 (by rfl) ⟨391340, by rfl⟩ : syracuseStep 521787 = 782681) B782681
theorem B521863 : Blo 519798 521863 := bstep (se 1 (by rfl) ⟨391397, by rfl⟩ : syracuseStep 521863 = 782795) B782795
theorem B784007 : Blo 519798 784007 := bstep (se 1 (by rfl) ⟨588005, by rfl⟩ : syracuseStep 784007 = 1176011) B1176011
theorem B521871 : Blo 519798 521871 := bstep (se 1 (by rfl) ⟨391403, by rfl⟩ : syracuseStep 521871 = 782807) B782807
theorem B587407 : Blo 519798 587407 := bstep (se 1 (by rfl) ⟨440555, by rfl⟩ : syracuseStep 587407 = 881111) B881111
theorem B1177235 : Blo 519798 1177235 := bstep (se 1 (by rfl) ⟨882926, by rfl⟩ : syracuseStep 1177235 = 1765853) B1765853
theorem B784043 : Blo 519798 784043 := bstep (se 1 (by rfl) ⟨588032, by rfl⟩ : syracuseStep 784043 = 1176065) B1176065
theorem B521915 : Blo 519798 521915 := bstep (se 1 (by rfl) ⟨391436, by rfl⟩ : syracuseStep 521915 = 782873) B782873
theorem B784073 : Blo 519798 784073 := bstep (se 2 (by rfl) ⟨294027, by rfl⟩ : syracuseStep 784073 = 588055) B588055
theorem B1177289 : Blo 519798 1177289 := bstep (se 2 (by rfl) ⟨441483, by rfl⟩ : syracuseStep 1177289 = 882967) B882967
theorem B521991 : Blo 519798 521991 := bstep (se 1 (by rfl) ⟨391493, by rfl⟩ : syracuseStep 521991 = 782987) B782987
theorem B521999 : Blo 519798 521999 := bstep (se 1 (by rfl) ⟨391499, by rfl⟩ : syracuseStep 521999 = 782999) B782999
theorem B522043 : Blo 519798 522043 := bstep (se 1 (by rfl) ⟨391532, by rfl⟩ : syracuseStep 522043 = 783065) B783065
theorem B784187 : Blo 519798 784187 := bstep (se 1 (by rfl) ⟨588140, by rfl⟩ : syracuseStep 784187 = 1176281) B1176281
theorem B3766105 : Blo 519798 3766105 := bstep (se 2 (by rfl) ⟨1412289, by rfl⟩ : syracuseStep 3766105 = 2824579) B2824579
theorem B4028249 : Blo 519798 4028249 := bstep (se 2 (by rfl) ⟨1510593, by rfl⟩ : syracuseStep 4028249 = 3021187) B3021187
theorem B784247 : Blo 519798 784247 := bstep (se 1 (by rfl) ⟨588185, by rfl⟩ : syracuseStep 784247 = 1176371) B1176371
theorem B522119 : Blo 519798 522119 := bstep (se 1 (by rfl) ⟨391589, by rfl⟩ : syracuseStep 522119 = 783179) B783179
theorem B522127 : Blo 519798 522127 := bstep (se 1 (by rfl) ⟨391595, by rfl⟩ : syracuseStep 522127 = 783191) B783191
theorem B784271 : Blo 519798 784271 := bstep (se 1 (by rfl) ⟨588203, by rfl⟩ : syracuseStep 784271 = 1176407) B1176407
theorem B784313 : Blo 519798 784313 := bstep (se 2 (by rfl) ⟨294117, by rfl⟩ : syracuseStep 784313 = 588235) B588235
theorem B522171 : Blo 519798 522171 := bstep (se 1 (by rfl) ⟨391628, by rfl⟩ : syracuseStep 522171 = 783257) B783257
theorem B2979787 : Blo 519798 2979787 := bstep (se 1 (by rfl) ⟨2234840, by rfl⟩ : syracuseStep 2979787 = 4469681) B4469681
theorem B522247 : Blo 519798 522247 := bstep (se 1 (by rfl) ⟨391685, by rfl⟩ : syracuseStep 522247 = 783371) B783371
theorem B784391 : Blo 519798 784391 := bstep (se 1 (by rfl) ⟨588293, by rfl⟩ : syracuseStep 784391 = 1176587) B1176587
theorem B522255 : Blo 519798 522255 := bstep (se 1 (by rfl) ⟨391691, by rfl⟩ : syracuseStep 522255 = 783383) B783383
theorem B882731 : Blo 519798 882731 := bstep (se 1 (by rfl) ⟨662048, by rfl⟩ : syracuseStep 882731 = 1324097) B1324097
theorem B784427 : Blo 519798 784427 := bstep (se 1 (by rfl) ⟨588320, by rfl⟩ : syracuseStep 784427 = 1176641) B1176641
theorem B522299 : Blo 519798 522299 := bstep (se 1 (by rfl) ⟨391724, by rfl⟩ : syracuseStep 522299 = 783449) B783449
theorem B784457 : Blo 519798 784457 := bstep (se 2 (by rfl) ⟨294171, by rfl⟩ : syracuseStep 784457 = 588343) B588343
theorem B522375 : Blo 519798 522375 := bstep (se 1 (by rfl) ⟨391781, by rfl⟩ : syracuseStep 522375 = 783563) B783563
theorem B587911 : Blo 519798 587911 := bstep (se 1 (by rfl) ⟨440933, by rfl⟩ : syracuseStep 587911 = 881867) B881867
theorem B522383 : Blo 519798 522383 := bstep (se 1 (by rfl) ⟨391787, by rfl⟩ : syracuseStep 522383 = 783575) B783575
theorem B522427 : Blo 519798 522427 := bstep (se 1 (by rfl) ⟨391820, by rfl⟩ : syracuseStep 522427 = 783641) B783641
theorem B784571 : Blo 519798 784571 := bstep (se 1 (by rfl) ⟨588428, by rfl⟩ : syracuseStep 784571 = 1176857) B1176857
theorem B784631 : Blo 519798 784631 := bstep (se 1 (by rfl) ⟨588473, by rfl⟩ : syracuseStep 784631 = 1176947) B1176947
theorem B1505537 : Blo 519798 1505537 := bstep (se 2 (by rfl) ⟨564576, by rfl⟩ : syracuseStep 1505537 = 1129153) B1129153
theorem B522503 : Blo 519798 522503 := bstep (se 1 (by rfl) ⟨391877, by rfl⟩ : syracuseStep 522503 = 783755) B783755
theorem B522511 : Blo 519798 522511 := bstep (se 1 (by rfl) ⟨391883, by rfl⟩ : syracuseStep 522511 = 783767) B783767
theorem B784655 : Blo 519798 784655 := bstep (se 1 (by rfl) ⟨588491, by rfl⟩ : syracuseStep 784655 = 1176983) B1176983
theorem B784697 : Blo 519798 784697 := bstep (se 2 (by rfl) ⟨294261, by rfl⟩ : syracuseStep 784697 = 588523) B588523
theorem B522555 : Blo 519798 522555 := bstep (se 1 (by rfl) ⟨391916, by rfl⟩ : syracuseStep 522555 = 783833) B783833
theorem B588091 : Blo 519798 588091 := bstep (se 1 (by rfl) ⟨441068, by rfl⟩ : syracuseStep 588091 = 882137) B882137
theorem B522631 : Blo 519798 522631 := bstep (se 1 (by rfl) ⟨391973, by rfl⟩ : syracuseStep 522631 = 783947) B783947
theorem B784775 : Blo 519798 784775 := bstep (se 1 (by rfl) ⟨588581, by rfl⟩ : syracuseStep 784775 = 1177163) B1177163
theorem B1177991 : Blo 519798 1177991 := bstep (se 1 (by rfl) ⟨883493, by rfl⟩ : syracuseStep 1177991 = 1766987) B1766987
theorem B522639 : Blo 519798 522639 := bstep (se 1 (by rfl) ⟨391979, by rfl⟩ : syracuseStep 522639 = 783959) B783959
theorem B784811 : Blo 519798 784811 := bstep (se 1 (by rfl) ⟨588608, by rfl⟩ : syracuseStep 784811 = 1177217) B1177217
theorem B883129 : Blo 519798 883129 := bstep (se 2 (by rfl) ⟨331173, by rfl⟩ : syracuseStep 883129 = 662347) B662347
theorem B522683 : Blo 519798 522683 := bstep (se 1 (by rfl) ⟨392012, by rfl⟩ : syracuseStep 522683 = 784025) B784025
theorem B784841 : Blo 519798 784841 := bstep (se 2 (by rfl) ⟨294315, by rfl⟩ : syracuseStep 784841 = 588631) B588631
theorem B522759 : Blo 519798 522759 := bstep (se 1 (by rfl) ⟨392069, by rfl⟩ : syracuseStep 522759 = 784139) B784139
theorem B522767 : Blo 519798 522767 := bstep (se 1 (by rfl) ⟨392075, by rfl⟩ : syracuseStep 522767 = 784151) B784151
theorem B522811 : Blo 519798 522811 := bstep (se 1 (by rfl) ⟨392108, by rfl⟩ : syracuseStep 522811 = 784217) B784217
theorem B784955 : Blo 519798 784955 := bstep (se 1 (by rfl) ⟨588716, by rfl⟩ : syracuseStep 784955 = 1177433) B1177433
theorem B1178171 : Blo 519798 1178171 := bstep (se 1 (by rfl) ⟨883628, by rfl⟩ : syracuseStep 1178171 = 1767257) B1767257
theorem B785015 : Blo 519798 785015 := bstep (se 1 (by rfl) ⟨588761, by rfl⟩ : syracuseStep 785015 = 1177523) B1177523
theorem B522887 : Blo 519798 522887 := bstep (se 1 (by rfl) ⟨392165, by rfl⟩ : syracuseStep 522887 = 784331) B784331
theorem B522895 : Blo 519798 522895 := bstep (se 1 (by rfl) ⟨392171, by rfl⟩ : syracuseStep 522895 = 784343) B784343
theorem B785039 : Blo 519798 785039 := bstep (se 1 (by rfl) ⟨588779, by rfl⟩ : syracuseStep 785039 = 1177559) B1177559
theorem B785081 : Blo 519798 785081 := bstep (se 2 (by rfl) ⟨294405, by rfl⟩ : syracuseStep 785081 = 588811) B588811
theorem B1178297 : Blo 519798 1178297 := bstep (se 2 (by rfl) ⟨441861, by rfl⟩ : syracuseStep 1178297 = 883723) B883723
theorem B522939 : Blo 519798 522939 := bstep (se 1 (by rfl) ⟨392204, by rfl⟩ : syracuseStep 522939 = 784409) B784409
theorem B523015 : Blo 519798 523015 := bstep (se 1 (by rfl) ⟨392261, by rfl⟩ : syracuseStep 523015 = 784523) B784523
theorem B785159 : Blo 519798 785159 := bstep (se 1 (by rfl) ⟨588869, by rfl⟩ : syracuseStep 785159 = 1177739) B1177739
theorem B523023 : Blo 519798 523023 := bstep (se 1 (by rfl) ⟨392267, by rfl⟩ : syracuseStep 523023 = 784535) B784535
theorem B588559 : Blo 519798 588559 := bstep (se 1 (by rfl) ⟨441419, by rfl⟩ : syracuseStep 588559 = 882839) B882839
theorem B785195 : Blo 519798 785195 := bstep (se 1 (by rfl) ⟨588896, by rfl⟩ : syracuseStep 785195 = 1177793) B1177793
theorem B523067 : Blo 519798 523067 := bstep (se 1 (by rfl) ⟨392300, by rfl⟩ : syracuseStep 523067 = 784601) B784601
theorem B785225 : Blo 519798 785225 := bstep (se 2 (by rfl) ⟨294459, by rfl⟩ : syracuseStep 785225 = 588919) B588919
theorem B20380517 : Blo 519798 20380517 := bstep (se 4 (by rfl) ⟨1910673, by rfl⟩ : syracuseStep 20380517 = 3821347) B3821347
theorem B523143 : Blo 519798 523143 := bstep (se 1 (by rfl) ⟨392357, by rfl⟩ : syracuseStep 523143 = 784715) B784715
theorem B523151 : Blo 519798 523151 := bstep (se 1 (by rfl) ⟨392363, by rfl⟩ : syracuseStep 523151 = 784727) B784727
theorem B687035 : Blo 519798 687035 := bstep (se 1 (by rfl) ⟨515276, by rfl⟩ : syracuseStep 687035 = 1030553) B1030553
theorem B523195 : Blo 519798 523195 := bstep (se 1 (by rfl) ⟨392396, by rfl⟩ : syracuseStep 523195 = 784793) B784793
theorem B785339 : Blo 519798 785339 := bstep (se 1 (by rfl) ⟨589004, by rfl⟩ : syracuseStep 785339 = 1178009) B1178009
theorem B785399 : Blo 519798 785399 := bstep (se 1 (by rfl) ⟨589049, by rfl⟩ : syracuseStep 785399 = 1178099) B1178099
theorem B97876997 : Blo 519798 97876997 := bstep (se 4 (by rfl) ⟨9175968, by rfl⟩ : syracuseStep 97876997 = 18351937) B18351937
theorem B523271 : Blo 519798 523271 := bstep (se 1 (by rfl) ⟨392453, by rfl⟩ : syracuseStep 523271 = 784907) B784907
theorem B523279 : Blo 519798 523279 := bstep (se 1 (by rfl) ⟨392459, by rfl⟩ : syracuseStep 523279 = 784919) B784919
theorem B785423 : Blo 519798 785423 := bstep (se 1 (by rfl) ⟨589067, by rfl⟩ : syracuseStep 785423 = 1178135) B1178135
theorem B785465 : Blo 519798 785465 := bstep (se 2 (by rfl) ⟨294549, by rfl⟩ : syracuseStep 785465 = 589099) B589099
theorem B523323 : Blo 519798 523323 := bstep (se 1 (by rfl) ⟨392492, by rfl⟩ : syracuseStep 523323 = 784985) B784985
theorem B883831 : Blo 519798 883831 := bstep (se 1 (by rfl) ⟨662873, by rfl⟩ : syracuseStep 883831 = 1325747) B1325747
theorem B523399 : Blo 519798 523399 := bstep (se 1 (by rfl) ⟨392549, by rfl⟩ : syracuseStep 523399 = 785099) B785099
theorem B785543 : Blo 519798 785543 := bstep (se 1 (by rfl) ⟨589157, by rfl⟩ : syracuseStep 785543 = 1178315) B1178315
theorem B523407 : Blo 519798 523407 := bstep (se 1 (by rfl) ⟨392555, by rfl⟩ : syracuseStep 523407 = 785111) B785111
theorem B785579 : Blo 519798 785579 := bstep (se 1 (by rfl) ⟨589184, by rfl⟩ : syracuseStep 785579 = 1178369) B1178369
theorem B523451 : Blo 519798 523451 := bstep (se 1 (by rfl) ⟨392588, by rfl⟩ : syracuseStep 523451 = 785177) B785177
theorem B785609 : Blo 519798 785609 := bstep (se 2 (by rfl) ⟨294603, by rfl⟩ : syracuseStep 785609 = 589207) B589207
theorem B523527 : Blo 519798 523527 := bstep (se 1 (by rfl) ⟨392645, by rfl⟩ : syracuseStep 523527 = 785291) B785291
theorem B589063 : Blo 519798 589063 := bstep (se 1 (by rfl) ⟨441797, by rfl⟩ : syracuseStep 589063 = 883595) B883595
theorem B523535 : Blo 519798 523535 := bstep (se 1 (by rfl) ⟨392651, by rfl⟩ : syracuseStep 523535 = 785303) B785303
theorem B4226363 : Blo 519798 4226363 := bstep (se 1 (by rfl) ⟨3169772, by rfl⟩ : syracuseStep 4226363 = 6339545) B6339545
theorem B523579 : Blo 519798 523579 := bstep (se 1 (by rfl) ⟨392684, by rfl⟩ : syracuseStep 523579 = 785369) B785369
theorem B523655 : Blo 519798 523655 := bstep (se 1 (by rfl) ⟨392741, by rfl⟩ : syracuseStep 523655 = 785483) B785483
theorem B523663 : Blo 519798 523663 := bstep (se 1 (by rfl) ⟨392747, by rfl⟩ : syracuseStep 523663 = 785495) B785495
theorem B523707 : Blo 519798 523707 := bstep (se 1 (by rfl) ⟨392780, by rfl⟩ : syracuseStep 523707 = 785561) B785561
theorem B589243 : Blo 519798 589243 := bstep (se 1 (by rfl) ⟨441932, by rfl⟩ : syracuseStep 589243 = 883865) B883865
theorem B523783 : Blo 519798 523783 := bstep (se 1 (by rfl) ⟨392837, by rfl⟩ : syracuseStep 523783 = 785675) B785675
theorem B523791 : Blo 519798 523791 := bstep (se 1 (by rfl) ⟨392843, by rfl⟩ : syracuseStep 523791 = 785687) B785687
theorem B5013323 : Blo 519798 5013323 := bstep (se 1 (by rfl) ⟨3759992, by rfl⟩ : syracuseStep 5013323 = 7519985) B7519985
theorem B3964787 : Blo 519798 3964787 := bstep (se 1 (by rfl) ⟨2973590, by rfl⟩ : syracuseStep 3964787 = 5947181) B5947181
theorem B3178385 : Blo 519798 3178385 := bstep (se 2 (by rfl) ⟨1191894, by rfl⟩ : syracuseStep 3178385 = 2383789) B2383789
theorem B1114003 : Blo 519798 1114003 := bstep (se 1 (by rfl) ⟨835502, by rfl⟩ : syracuseStep 1114003 = 1671005) B1671005
theorem B1015865 : Blo 519798 1015865 := bstep (se 2 (by rfl) ⟨380949, by rfl⟩ : syracuseStep 1015865 = 761899) B761899
theorem B1115063 : Blo 519798 1115063 := bstep (se 1 (by rfl) ⟨836297, by rfl⟩ : syracuseStep 1115063 = 1672595) B1672595
theorem B21398579 : Blo 519798 21398579 := bstep (se 1 (by rfl) ⟨16048934, by rfl⟩ : syracuseStep 21398579 = 32097869) B32097869
theorem B2229443 : Blo 519798 2229443 := bstep (se 1 (by rfl) ⟨1672082, by rfl⟩ : syracuseStep 2229443 = 3344165) B3344165
theorem B14451929 : Blo 519798 14451929 := bstep (se 2 (by rfl) ⟨5419473, by rfl⟩ : syracuseStep 14451929 = 10838947) B10838947
theorem B3966245 : Blo 519798 3966245 := bstep (se 4 (by rfl) ⟨371835, by rfl⟩ : syracuseStep 3966245 = 743671) B743671
theorem B4458199 : Blo 519798 4458199 := bstep (se 1 (by rfl) ⟨3343649, by rfl⟩ : syracuseStep 4458199 = 6687299) B6687299
theorem B19105631 : Blo 519798 19105631 := bstep (se 1 (by rfl) ⟨14329223, by rfl⟩ : syracuseStep 19105631 = 28658447) B28658447
theorem B13371317 : Blo 519798 13371317 := bstep (se 5 (by rfl) ⟨626780, by rfl⟩ : syracuseStep 13371317 = 1253561) B1253561
theorem B624763 : Blo 519798 624763 := bstep (se 1 (by rfl) ⟨468572, by rfl⟩ : syracuseStep 624763 = 937145) B937145
theorem B1804763 : Blo 519798 1804763 := bstep (se 1 (by rfl) ⟨1353572, by rfl⟩ : syracuseStep 1804763 = 2707145) B2707145
theorem B1673875 : Blo 519798 1673875 := bstep (se 1 (by rfl) ⟨1255406, by rfl⟩ : syracuseStep 1673875 = 2510813) B2510813
theorem B658631 : Blo 519798 658631 := bstep (se 1 (by rfl) ⟨493973, by rfl⟩ : syracuseStep 658631 = 987947) B987947
theorem B658783 : Blo 519798 658783 := bstep (se 1 (by rfl) ⟨494087, by rfl⟩ : syracuseStep 658783 = 988175) B988175
theorem B2232107 : Blo 519798 2232107 := bstep (se 1 (by rfl) ⟨1674080, by rfl⟩ : syracuseStep 2232107 = 3348161) B3348161
theorem B986975 : Blo 519798 986975 := bstep (se 1 (by rfl) ⟨740231, by rfl⟩ : syracuseStep 986975 = 1480463) B1480463
theorem B1249199 : Blo 519798 1249199 := bstep (se 1 (by rfl) ⟨936899, by rfl⟩ : syracuseStep 1249199 = 1873799) B1873799
theorem B987385 : Blo 519798 987385 := bstep (se 2 (by rfl) ⟨370269, by rfl⟩ : syracuseStep 987385 = 740539) B740539
theorem B1675721 : Blo 519798 1675721 := bstep (se 2 (by rfl) ⟨628395, by rfl⟩ : syracuseStep 1675721 = 1256791) B1256791
theorem B3772909 : Blo 519798 3772909 := bstep (se 3 (by rfl) ⟨707420, by rfl⟩ : syracuseStep 3772909 = 1414841) B1414841
theorem B6689303 : Blo 519798 6689303 := bstep (se 1 (by rfl) ⟨5016977, by rfl⟩ : syracuseStep 6689303 = 10033955) B10033955
theorem B987727 : Blo 519798 987727 := bstep (se 1 (by rfl) ⟨740795, by rfl⟩ : syracuseStep 987727 = 1481591) B1481591
theorem B987977 : Blo 519798 987977 := bstep (se 2 (by rfl) ⟨370491, by rfl⟩ : syracuseStep 987977 = 740983) B740983
theorem B30545099 : Blo 519798 30545099 := bstep (se 1 (by rfl) ⟨22908824, by rfl⟩ : syracuseStep 30545099 = 45817649) B45817649
theorem B1054127 : Blo 519798 1054127 := bstep (se 1 (by rfl) ⟨790595, by rfl⟩ : syracuseStep 1054127 = 1581191) B1581191
theorem B660955 : Blo 519798 660955 := bstep (se 1 (by rfl) ⟨495716, by rfl⟩ : syracuseStep 660955 = 991433) B991433
theorem B1480315 : Blo 519798 1480315 := bstep (se 1 (by rfl) ⟨1110236, by rfl⟩ : syracuseStep 1480315 = 2220473) B2220473
theorem B988843 : Blo 519798 988843 := bstep (se 1 (by rfl) ⟨741632, by rfl⟩ : syracuseStep 988843 = 1483265) B1483265
theorem B988919 : Blo 519798 988919 := bstep (se 1 (by rfl) ⟨741689, by rfl⟩ : syracuseStep 988919 = 1483379) B1483379
theorem B1251179 : Blo 519798 1251179 := bstep (se 1 (by rfl) ⟨938384, by rfl⟩ : syracuseStep 1251179 = 1876769) B1876769
theorem B989147 : Blo 519798 989147 := bstep (se 1 (by rfl) ⟨741860, by rfl⟩ : syracuseStep 989147 = 1483721) B1483721
theorem B10033409 : Blo 519798 10033409 := bstep (se 2 (by rfl) ⟨3762528, by rfl⟩ : syracuseStep 10033409 = 7525057) B7525057
theorem B5020055 : Blo 519798 5020055 := bstep (se 1 (by rfl) ⟨3765041, by rfl⟩ : syracuseStep 5020055 = 7530083) B7530083
theorem B1219169 : Blo 519798 1219169 := bstep (se 2 (by rfl) ⟨457188, by rfl⟩ : syracuseStep 1219169 = 914377) B914377
theorem B1481465 : Blo 519798 1481465 := bstep (se 2 (by rfl) ⟨555549, by rfl⟩ : syracuseStep 1481465 = 1111099) B1111099
theorem B1481647 : Blo 519798 1481647 := bstep (se 1 (by rfl) ⟨1111235, by rfl⟩ : syracuseStep 1481647 = 2222471) B2222471
theorem B1481807 : Blo 519798 1481807 := bstep (se 1 (by rfl) ⟨1111355, by rfl⟩ : syracuseStep 1481807 = 2222711) B2222711
theorem B1186987 : Blo 519798 1186987 := bstep (se 1 (by rfl) ⟨890240, by rfl⟩ : syracuseStep 1186987 = 1780481) B1780481
theorem B990407 : Blo 519798 990407 := bstep (se 1 (by rfl) ⟨742805, by rfl⟩ : syracuseStep 990407 = 1485611) B1485611
theorem B4463909 : Blo 519798 4463909 := bstep (se 4 (by rfl) ⟨418491, by rfl⟩ : syracuseStep 4463909 = 836983) B836983
theorem B990559 : Blo 519798 990559 := bstep (se 1 (by rfl) ⟨742919, by rfl⟩ : syracuseStep 990559 = 1485839) B1485839
theorem B1253063 : Blo 519798 1253063 := bstep (se 1 (by rfl) ⟨939797, by rfl⟩ : syracuseStep 1253063 = 1879595) B1879595
theorem B5021473 : Blo 519798 5021473 := bstep (se 2 (by rfl) ⟨1883052, by rfl⟩ : syracuseStep 5021473 = 3766105) B3766105
theorem B1318751 : Blo 519798 1318751 := bstep (se 1 (by rfl) ⟨989063, by rfl⟩ : syracuseStep 1318751 = 1978127) B1978127
theorem B3973049 : Blo 519798 3973049 := bstep (se 2 (by rfl) ⟨1489893, by rfl⟩ : syracuseStep 3973049 = 2979787) B2979787
theorem B1712281 : Blo 519798 1712281 := bstep (se 2 (by rfl) ⟨642105, by rfl⟩ : syracuseStep 1712281 = 1284211) B1284211
theorem B1482923 : Blo 519798 1482923 := bstep (se 1 (by rfl) ⟨1112192, by rfl⟩ : syracuseStep 1482923 = 2224385) B2224385
theorem B1056979 : Blo 519798 1056979 := bstep (se 1 (by rfl) ⟨792734, by rfl⟩ : syracuseStep 1056979 = 1585469) B1585469
theorem B1319449 : Blo 519798 1319449 := bstep (se 2 (by rfl) ⟨494793, by rfl⟩ : syracuseStep 1319449 = 989587) B989587
theorem B795259 : Blo 519798 795259 := bstep (se 1 (by rfl) ⟨596444, by rfl⟩ : syracuseStep 795259 = 1192889) B1192889
theorem B2499281 : Blo 519798 2499281 := bstep (se 2 (by rfl) ⟨937230, by rfl⟩ : syracuseStep 2499281 = 1874461) B1874461
theorem B1319753 : Blo 519798 1319753 := bstep (se 2 (by rfl) ⟨494907, by rfl⟩ : syracuseStep 1319753 = 989815) B989815
theorem B992503 : Blo 519798 992503 := bstep (se 1 (by rfl) ⟨744377, by rfl⟩ : syracuseStep 992503 = 1488755) B1488755
theorem B992731 : Blo 519798 992731 := bstep (se 1 (by rfl) ⟨744548, by rfl⟩ : syracuseStep 992731 = 1489097) B1489097
theorem B992807 : Blo 519798 992807 := bstep (se 1 (by rfl) ⟨744605, by rfl⟩ : syracuseStep 992807 = 1489211) B1489211
theorem B992891 : Blo 519798 992891 := bstep (se 1 (by rfl) ⟨744668, by rfl⟩ : syracuseStep 992891 = 1489337) B1489337
theorem B2827997 : Blo 519798 2827997 := bstep (se 3 (by rfl) ⟨530249, by rfl⟩ : syracuseStep 2827997 = 1060499) B1060499
theorem B117253973 : Blo 519798 117253973 := bstep (se 9 (by rfl) ⟨343517, by rfl⟩ : syracuseStep 117253973 = 687035) B687035
theorem B1976183 : Blo 519798 1976183 := bstep (se 1 (by rfl) ⟨1482137, by rfl⟩ : syracuseStep 1976183 = 2964275) B2964275
theorem B1320887 : Blo 519798 1320887 := bstep (se 1 (by rfl) ⟨990665, by rfl⟩ : syracuseStep 1320887 = 1981331) B1981331
theorem B65251331 : Blo 519798 65251331 := bstep (se 1 (by rfl) ⟨48938498, by rfl⟩ : syracuseStep 65251331 = 97876997) B97876997
theorem B5023781 : Blo 519798 5023781 := bstep (se 4 (by rfl) ⟨470979, by rfl⟩ : syracuseStep 5023781 = 941959) B941959
theorem B993377 : Blo 519798 993377 := bstep (se 2 (by rfl) ⟨372516, by rfl⟩ : syracuseStep 993377 = 745033) B745033
theorem B5941349 : Blo 519798 5941349 := bstep (se 4 (by rfl) ⟨557001, by rfl⟩ : syracuseStep 5941349 = 1114003) B1114003
theorem B1780423 : Blo 519798 1780423 := bstep (se 1 (by rfl) ⟨1335317, by rfl⟩ : syracuseStep 1780423 = 2670635) B2670635
theorem B3975965 : Blo 519798 3975965 := bstep (se 3 (by rfl) ⟨745493, by rfl⟩ : syracuseStep 3975965 = 1490987) B1490987
theorem B1977155 : Blo 519798 1977155 := bstep (se 1 (by rfl) ⟨1482866, by rfl⟩ : syracuseStep 1977155 = 2965733) B2965733
theorem B6663059 : Blo 519798 6663059 := bstep (se 1 (by rfl) ⟨4997294, by rfl⟩ : syracuseStep 6663059 = 9994589) B9994589
theorem B3353491 : Blo 519798 3353491 := bstep (se 1 (by rfl) ⟨2515118, by rfl⟩ : syracuseStep 3353491 = 5030237) B5030237
theorem B1321991 : Blo 519798 1321991 := bstep (se 1 (by rfl) ⟨991493, by rfl⟩ : syracuseStep 1321991 = 1982987) B1982987
theorem B1322041 : Blo 519798 1322041 := bstep (se 2 (by rfl) ⟨495765, by rfl⟩ : syracuseStep 1322041 = 991531) B991531
theorem B4467905 : Blo 519798 4467905 := bstep (se 2 (by rfl) ⟨1675464, by rfl⟩ : syracuseStep 4467905 = 3350929) B3350929
theorem B6008003 : Blo 519798 6008003 := bstep (se 1 (by rfl) ⟨4506002, by rfl⟩ : syracuseStep 6008003 = 9012005) B9012005
theorem B50834627 : Blo 519798 50834627 := bstep (se 1 (by rfl) ⟨38125970, by rfl⟩ : syracuseStep 50834627 = 76251941) B76251941
theorem B1879307 : Blo 519798 1879307 := bstep (se 1 (by rfl) ⟨1409480, by rfl⟩ : syracuseStep 1879307 = 2818961) B2818961
theorem B1322345 : Blo 519798 1322345 := bstep (se 2 (by rfl) ⟨495879, by rfl⟩ : syracuseStep 1322345 = 991759) B991759
theorem B2502089 : Blo 519798 2502089 := bstep (se 2 (by rfl) ⟨938283, by rfl⟩ : syracuseStep 2502089 = 1876567) B1876567
theorem B3354311 : Blo 519798 3354311 := bstep (se 1 (by rfl) ⟨2515733, by rfl⟩ : syracuseStep 3354311 = 5031467) B5031467
theorem B1978141 : Blo 519798 1978141 := bstep (se 3 (by rfl) ⟨370901, by rfl⟩ : syracuseStep 1978141 = 741803) B741803
theorem B2633633 : Blo 519798 2633633 := bstep (se 2 (by rfl) ⟨987612, by rfl⟩ : syracuseStep 2633633 = 1975225) B1975225
theorem B3355337 : Blo 519798 3355337 := bstep (se 2 (by rfl) ⟨1258251, by rfl⟩ : syracuseStep 3355337 = 2516503) B2516503
theorem B1487879 : Blo 519798 1487879 := bstep (se 1 (by rfl) ⟨1115909, by rfl⟩ : syracuseStep 1487879 = 2231819) B2231819
theorem B5715011 : Blo 519798 5715011 := bstep (se 1 (by rfl) ⟨4286258, by rfl⟩ : syracuseStep 5715011 = 8572517) B8572517
theorem B1324583 : Blo 519798 1324583 := bstep (se 1 (by rfl) ⟨993437, by rfl⟩ : syracuseStep 1324583 = 1986875) B1986875
theorem B1357511 : Blo 519798 1357511 := bstep (se 1 (by rfl) ⟨1018133, by rfl⟩ : syracuseStep 1357511 = 2036267) B2036267
theorem B6371065 : Blo 519798 6371065 := bstep (se 2 (by rfl) ⟨2389149, by rfl⟩ : syracuseStep 6371065 = 4778299) B4778299
theorem B1324907 : Blo 519798 1324907 := bstep (se 1 (by rfl) ⟨993680, by rfl⟩ : syracuseStep 1324907 = 1987361) B1987361
theorem B29407093 : Blo 519798 29407093 := bstep (se 5 (by rfl) ⟨1378457, by rfl⟩ : syracuseStep 29407093 = 2756915) B2756915
theorem B5027777 : Blo 519798 5027777 := bstep (se 2 (by rfl) ⟨1885416, by rfl⟩ : syracuseStep 5027777 = 3770833) B3770833
theorem B17119289 : Blo 519798 17119289 := bstep (se 2 (by rfl) ⟨6419733, by rfl⟩ : syracuseStep 17119289 = 12839467) B12839467
theorem B2668625 : Blo 519798 2668625 := bstep (se 2 (by rfl) ⟨1000734, by rfl⟩ : syracuseStep 2668625 = 2001469) B2001469
theorem B6010969 : Blo 519798 6010969 := bstep (se 2 (by rfl) ⟨2254113, by rfl⟩ : syracuseStep 6010969 = 4508227) B4508227
theorem B833735 : Blo 519798 833735 := bstep (se 1 (by rfl) ⟨625301, by rfl⟩ : syracuseStep 833735 = 1250603) B1250603
theorem B1325555 : Blo 519798 1325555 := bstep (se 1 (by rfl) ⟨994166, by rfl⟩ : syracuseStep 1325555 = 1988333) B1988333
theorem B1882649 : Blo 519798 1882649 := bstep (se 2 (by rfl) ⟨705993, by rfl⟩ : syracuseStep 1882649 = 1411987) B1411987
theorem B834247 : Blo 519798 834247 := bstep (se 1 (by rfl) ⟨625685, by rfl⟩ : syracuseStep 834247 = 1251371) B1251371
theorem B1325767 : Blo 519798 1325767 := bstep (se 1 (by rfl) ⟨994325, by rfl⟩ : syracuseStep 1325767 = 1988651) B1988651
theorem B1784695 : Blo 519798 1784695 := bstep (se 1 (by rfl) ⟨1338521, by rfl⟩ : syracuseStep 1784695 = 2677043) B2677043
theorem B2505779 : Blo 519798 2505779 := bstep (se 1 (by rfl) ⟨1879334, by rfl⟩ : syracuseStep 2505779 = 3758669) B3758669
theorem B1490167 : Blo 519798 1490167 := bstep (se 1 (by rfl) ⟨1117625, by rfl⟩ : syracuseStep 1490167 = 2235251) B2235251
theorem B1490395 : Blo 519798 1490395 := bstep (se 1 (by rfl) ⟨1117796, by rfl⟩ : syracuseStep 1490395 = 2235593) B2235593
theorem B835195 : Blo 519798 835195 := bstep (se 1 (by rfl) ⟨626396, by rfl⟩ : syracuseStep 835195 = 1252793) B1252793
theorem B1490555 : Blo 519798 1490555 := bstep (se 1 (by rfl) ⟨1117916, by rfl⟩ : syracuseStep 1490555 = 2235833) B2235833
theorem B2965207 : Blo 519798 2965207 := bstep (se 1 (by rfl) ⟨2223905, by rfl⟩ : syracuseStep 2965207 = 4447811) B4447811
theorem B1982303 : Blo 519798 1982303 := bstep (se 1 (by rfl) ⟨1486727, by rfl⟩ : syracuseStep 1982303 = 2973455) B2973455
theorem B1490795 : Blo 519798 1490795 := bstep (se 1 (by rfl) ⟨1118096, by rfl⟩ : syracuseStep 1490795 = 2236193) B2236193
theorem B10141625 : Blo 519798 10141625 := bstep (se 2 (by rfl) ⟨3803109, by rfl⟩ : syracuseStep 10141625 = 7606219) B7606219
theorem B836015 : Blo 519798 836015 := bstep (se 1 (by rfl) ⟨627011, by rfl⟩ : syracuseStep 836015 = 1254023) B1254023
theorem B1491443 : Blo 519798 1491443 := bstep (se 1 (by rfl) ⟨1118582, by rfl⟩ : syracuseStep 1491443 = 2237165) B2237165
theorem B1983001 : Blo 519798 1983001 := bstep (se 2 (by rfl) ⟨743625, by rfl⟩ : syracuseStep 1983001 = 1487251) B1487251
theorem B1983275 : Blo 519798 1983275 := bstep (se 1 (by rfl) ⟨1487456, by rfl⟩ : syracuseStep 1983275 = 2974913) B2974913
theorem B836425 : Blo 519798 836425 := bstep (se 2 (by rfl) ⟨313659, by rfl⟩ : syracuseStep 836425 = 627319) B627319
theorem B1983305 : Blo 519798 1983305 := bstep (se 2 (by rfl) ⟨743739, by rfl⟩ : syracuseStep 1983305 = 1487479) B1487479
theorem B3949721 : Blo 519798 3949721 := bstep (se 2 (by rfl) ⟨1481145, by rfl⟩ : syracuseStep 3949721 = 2962291) B2962291
theorem B4441661 : Blo 519798 4441661 := bstep (se 3 (by rfl) ⟨832811, by rfl⟩ : syracuseStep 4441661 = 1665623) B1665623
theorem B2148049 : Blo 519798 2148049 := bstep (se 2 (by rfl) ⟨805518, by rfl⟩ : syracuseStep 2148049 = 1611037) B1611037
theorem B1754999 : Blo 519798 1754999 := bstep (se 1 (by rfl) ⟨1316249, by rfl⟩ : syracuseStep 1754999 = 2632499) B2632499
theorem B2115503 : Blo 519798 2115503 := bstep (se 1 (by rfl) ⟨1586627, by rfl⟩ : syracuseStep 2115503 = 3173255) B3173255
theorem B4245533 : Blo 519798 4245533 := bstep (se 3 (by rfl) ⟨796037, by rfl⟩ : syracuseStep 4245533 = 1592075) B1592075
theorem B870439 : Blo 519798 870439 := bstep (se 1 (by rfl) ⟨652829, by rfl⟩ : syracuseStep 870439 = 1305659) B1305659
theorem B1755215 : Blo 519798 1755215 := bstep (se 1 (by rfl) ⟨1316411, by rfl⟩ : syracuseStep 1755215 = 2632823) B2632823
theorem B12667013 : Blo 519798 12667013 := bstep (se 4 (by rfl) ⟨1187532, by rfl⟩ : syracuseStep 12667013 = 2375065) B2375065
theorem B12863897 : Blo 519798 12863897 := bstep (se 2 (by rfl) ⟨4823961, by rfl⟩ : syracuseStep 12863897 = 9647923) B9647923
theorem B1755593 : Blo 519798 1755593 := bstep (se 2 (by rfl) ⟨658347, by rfl⟩ : syracuseStep 1755593 = 1316695) B1316695
theorem B2968123 : Blo 519798 2968123 := bstep (se 1 (by rfl) ⟨2226092, by rfl⟩ : syracuseStep 2968123 = 4452185) B4452185
theorem B1755863 : Blo 519798 1755863 := bstep (se 1 (by rfl) ⟨1316897, by rfl⟩ : syracuseStep 1755863 = 2633795) B2633795
theorem B1756079 : Blo 519798 1756079 := bstep (se 1 (by rfl) ⟨1317059, by rfl⟩ : syracuseStep 1756079 = 2634119) B2634119
theorem B2378771 : Blo 519798 2378771 := bstep (se 1 (by rfl) ⟨1784078, by rfl⟩ : syracuseStep 2378771 = 3568157) B3568157
theorem B3951665 : Blo 519798 3951665 := bstep (se 2 (by rfl) ⟨1481874, by rfl⟩ : syracuseStep 3951665 = 2963749) B2963749
theorem B740431 : Blo 519798 740431 := bstep (se 1 (by rfl) ⟨555323, by rfl⟩ : syracuseStep 740431 = 1110647) B1110647
theorem B13716773 : Blo 519798 13716773 := bstep (se 4 (by rfl) ⟨1285947, by rfl⟩ : syracuseStep 13716773 = 2571895) B2571895
theorem B1985917 : Blo 519798 1985917 := bstep (se 3 (by rfl) ⟨372359, by rfl⟩ : syracuseStep 1985917 = 744719) B744719
theorem B2117107 : Blo 519798 2117107 := bstep (se 1 (by rfl) ⟨1587830, by rfl⟩ : syracuseStep 2117107 = 3175661) B3175661
theorem B2510585 : Blo 519798 2510585 := bstep (se 2 (by rfl) ⟨941469, by rfl⟩ : syracuseStep 2510585 = 1882939) B1882939
theorem B1003691 : Blo 519798 1003691 := bstep (se 1 (by rfl) ⟨752768, by rfl⟩ : syracuseStep 1003691 = 1505537) B1505537
theorem B13587011 : Blo 519798 13587011 := bstep (se 1 (by rfl) ⟨10190258, by rfl⟩ : syracuseStep 13587011 = 20380517) B20380517
theorem B3330733 : Blo 519798 3330733 := bstep (se 3 (by rfl) ⟨624512, by rfl⟩ : syracuseStep 3330733 = 1249025) B1249025
theorem B1758455 : Blo 519798 1758455 := bstep (se 1 (by rfl) ⟨1318841, by rfl⟩ : syracuseStep 1758455 = 2637683) B2637683
theorem B2643191 : Blo 519798 2643191 := bstep (se 1 (by rfl) ⟨1982393, by rfl⟩ : syracuseStep 2643191 = 3964787) B3964787
theorem B2118923 : Blo 519798 2118923 := bstep (se 1 (by rfl) ⟨1589192, by rfl⟩ : syracuseStep 2118923 = 3178385) B3178385
theorem B939451 : Blo 519798 939451 := bstep (se 1 (by rfl) ⟨704588, by rfl⟩ : syracuseStep 939451 = 1409177) B1409177
theorem B5953013 : Blo 519798 5953013 := bstep (se 5 (by rfl) ⟨279047, by rfl⟩ : syracuseStep 5953013 = 558095) B558095
theorem B1988135 : Blo 519798 1988135 := bstep (se 1 (by rfl) ⟨1491101, by rfl⟩ : syracuseStep 1988135 = 2982203) B2982203
theorem B1758779 : Blo 519798 1758779 := bstep (se 1 (by rfl) ⟨1319084, by rfl⟩ : syracuseStep 1758779 = 2638169) B2638169
theorem B2676347 : Blo 519798 2676347 := bstep (se 1 (by rfl) ⟨2007260, by rfl⟩ : syracuseStep 2676347 = 4014521) B4014521
theorem B16864949 : Blo 519798 16864949 := bstep (se 5 (by rfl) ⟨790544, by rfl⟩ : syracuseStep 16864949 = 1581089) B1581089
theorem B2512583 : Blo 519798 2512583 := bstep (se 1 (by rfl) ⟨1884437, by rfl⟩ : syracuseStep 2512583 = 3768875) B3768875
theorem B2643677 : Blo 519798 2643677 := bstep (se 3 (by rfl) ⟨495689, by rfl⟩ : syracuseStep 2643677 = 991379) B991379
theorem B1759049 : Blo 519798 1759049 := bstep (se 2 (by rfl) ⟨659643, by rfl⟩ : syracuseStep 1759049 = 1319287) B1319287
theorem B36591587 : Blo 519798 36591587 := bstep (se 1 (by rfl) ⟨27443690, by rfl⟩ : syracuseStep 36591587 = 54887381) B54887381
theorem B16963829 : Blo 519798 16963829 := bstep (se 5 (by rfl) ⟨795179, by rfl⟩ : syracuseStep 16963829 = 1590359) B1590359
theorem B743899 : Blo 519798 743899 := bstep (se 1 (by rfl) ⟨557924, by rfl⟩ : syracuseStep 743899 = 1115849) B1115849
theorem B1170017 : Blo 519798 1170017 := bstep (se 2 (by rfl) ⟨438756, by rfl⟩ : syracuseStep 1170017 = 877513) B877513
theorem B1333883 : Blo 519798 1333883 := bstep (se 1 (by rfl) ⟨1000412, by rfl⟩ : syracuseStep 1333883 = 2000825) B2000825
theorem B91151119 : Blo 519798 91151119 := bstep (se 1 (by rfl) ⟨68363339, by rfl⟩ : syracuseStep 91151119 = 136726679) B136726679
theorem B1170359 : Blo 519798 1170359 := bstep (se 1 (by rfl) ⟨877769, by rfl⟩ : syracuseStep 1170359 = 1755539) B1755539
theorem B1760183 : Blo 519798 1760183 := bstep (se 1 (by rfl) ⟨1320137, by rfl⟩ : syracuseStep 1760183 = 2640275) B2640275
theorem B1432733 : Blo 519798 1432733 := bstep (se 3 (by rfl) ⟨268637, by rfl⟩ : syracuseStep 1432733 = 537275) B537275
theorem B8477891 : Blo 519798 8477891 := bstep (se 1 (by rfl) ⟨6358418, by rfl⟩ : syracuseStep 8477891 = 12716837) B12716837
theorem B6708419 : Blo 519798 6708419 := bstep (se 1 (by rfl) ⟨5031314, by rfl⟩ : syracuseStep 6708419 = 10062629) B10062629
theorem B1170953 : Blo 519798 1170953 := bstep (se 2 (by rfl) ⟨439107, by rfl⟩ : syracuseStep 1170953 = 878215) B878215
theorem B1760777 : Blo 519798 1760777 := bstep (se 2 (by rfl) ⟨660291, by rfl⟩ : syracuseStep 1760777 = 1320583) B1320583
theorem B1171295 : Blo 519798 1171295 := bstep (se 1 (by rfl) ⟨878471, by rfl⟩ : syracuseStep 1171295 = 1756943) B1756943
theorem B1171475 : Blo 519798 1171475 := bstep (se 1 (by rfl) ⟨878606, by rfl⟩ : syracuseStep 1171475 = 1757213) B1757213
theorem B3563777 : Blo 519798 3563777 := bstep (se 2 (by rfl) ⟨1336416, by rfl⟩ : syracuseStep 3563777 = 2672833) B2672833
theorem B1171817 : Blo 519798 1171817 := bstep (se 2 (by rfl) ⟨439431, by rfl⟩ : syracuseStep 1171817 = 878863) B878863
theorem B1761641 : Blo 519798 1761641 := bstep (se 2 (by rfl) ⟨660615, by rfl⟩ : syracuseStep 1761641 = 1321231) B1321231
theorem B877385 : Blo 519798 877385 := bstep (se 2 (by rfl) ⟨329019, by rfl⟩ : syracuseStep 877385 = 658039) B658039
theorem B1172411 : Blo 519798 1172411 := bstep (se 1 (by rfl) ⟨879308, by rfl⟩ : syracuseStep 1172411 = 1758617) B1758617
theorem B1762235 : Blo 519798 1762235 := bstep (se 1 (by rfl) ⟨1321676, by rfl⟩ : syracuseStep 1762235 = 2643353) B2643353
theorem B1172537 : Blo 519798 1172537 := bstep (se 2 (by rfl) ⟨439701, by rfl⟩ : syracuseStep 1172537 = 879403) B879403
theorem B4449451 : Blo 519798 4449451 := bstep (se 1 (by rfl) ⟨3337088, by rfl⟩ : syracuseStep 4449451 = 6674177) B6674177
theorem B15262937 : Blo 519798 15262937 := bstep (se 2 (by rfl) ⟨5723601, by rfl⟩ : syracuseStep 15262937 = 11447203) B11447203
theorem B877817 : Blo 519798 877817 := bstep (se 2 (by rfl) ⟨329181, by rfl⟩ : syracuseStep 877817 = 658363) B658363
theorem B1172879 : Blo 519798 1172879 := bstep (se 1 (by rfl) ⟨879659, by rfl⟩ : syracuseStep 1172879 = 1759319) B1759319
theorem B11265443 : Blo 519798 11265443 := bstep (se 1 (by rfl) ⟨8449082, by rfl⟩ : syracuseStep 11265443 = 16898165) B16898165
theorem B877999 : Blo 519798 877999 := bstep (se 1 (by rfl) ⟨658499, by rfl⟩ : syracuseStep 877999 = 1316999) B1316999
theorem B878087 : Blo 519798 878087 := bstep (se 1 (by rfl) ⟨658565, by rfl⟩ : syracuseStep 878087 = 1317131) B1317131
theorem B779855 : Blo 519798 779855 := bstep (se 1 (by rfl) ⟨584891, by rfl⟩ : syracuseStep 779855 = 1169783) B1169783
theorem B779975 : Blo 519798 779975 := bstep (se 1 (by rfl) ⟨584981, by rfl⟩ : syracuseStep 779975 = 1169963) B1169963
theorem B1173203 : Blo 519798 1173203 := bstep (se 1 (by rfl) ⟨879902, by rfl⟩ : syracuseStep 1173203 = 1759805) B1759805
theorem B6711083 : Blo 519798 6711083 := bstep (se 1 (by rfl) ⟨5033312, by rfl⟩ : syracuseStep 6711083 = 10066625) B10066625
theorem B878431 : Blo 519798 878431 := bstep (se 1 (by rfl) ⟨658823, by rfl⟩ : syracuseStep 878431 = 1317647) B1317647
theorem B780137 : Blo 519798 780137 := bstep (se 2 (by rfl) ⟨292551, by rfl⟩ : syracuseStep 780137 = 585103) B585103
theorem B878519 : Blo 519798 878519 := bstep (se 1 (by rfl) ⟨658889, by rfl⟩ : syracuseStep 878519 = 1317779) B1317779
theorem B780215 : Blo 519798 780215 := bstep (se 1 (by rfl) ⟨585161, by rfl⟩ : syracuseStep 780215 = 1170323) B1170323
theorem B780251 : Blo 519798 780251 := bstep (se 1 (by rfl) ⟨585188, by rfl⟩ : syracuseStep 780251 = 1170377) B1170377
theorem B10741997 : Blo 519798 10741997 := bstep (se 3 (by rfl) ⟨2014124, by rfl⟩ : syracuseStep 10741997 = 4028249) B4028249
theorem B780719 : Blo 519798 780719 := bstep (se 1 (by rfl) ⟨585539, by rfl⟩ : syracuseStep 780719 = 1171079) B1171079
theorem B780809 : Blo 519798 780809 := bstep (se 2 (by rfl) ⟨292803, by rfl⟩ : syracuseStep 780809 = 585607) B585607
theorem B879113 : Blo 519798 879113 := bstep (se 2 (by rfl) ⟨329667, by rfl⟩ : syracuseStep 879113 = 659335) B659335
theorem B780839 : Blo 519798 780839 := bstep (se 1 (by rfl) ⟨585629, by rfl⟩ : syracuseStep 780839 = 1171259) B1171259
theorem B780923 : Blo 519798 780923 := bstep (se 1 (by rfl) ⟨585692, by rfl⟩ : syracuseStep 780923 = 1171385) B1171385
theorem B1174139 : Blo 519798 1174139 := bstep (se 1 (by rfl) ⟨880604, by rfl⟩ : syracuseStep 1174139 = 1761209) B1761209
theorem B1763963 : Blo 519798 1763963 := bstep (se 1 (by rfl) ⟨1322972, by rfl⟩ : syracuseStep 1763963 = 2645945) B2645945
theorem B879275 : Blo 519798 879275 := bstep (se 1 (by rfl) ⟨659456, by rfl⟩ : syracuseStep 879275 = 1318913) B1318913
theorem B8055497 : Blo 519798 8055497 := bstep (se 2 (by rfl) ⟨3020811, by rfl⟩ : syracuseStep 8055497 = 6041623) B6041623
theorem B781049 : Blo 519798 781049 := bstep (se 2 (by rfl) ⟨292893, by rfl⟩ : syracuseStep 781049 = 585787) B585787
theorem B1174265 : Blo 519798 1174265 := bstep (se 2 (by rfl) ⟨440349, by rfl⟩ : syracuseStep 1174265 = 880699) B880699
theorem B1764125 : Blo 519798 1764125 := bstep (se 3 (by rfl) ⟨330773, by rfl⟩ : syracuseStep 1764125 = 661547) B661547
theorem B2648861 : Blo 519798 2648861 := bstep (se 3 (by rfl) ⟨496661, by rfl⟩ : syracuseStep 2648861 = 993323) B993323
theorem B781151 : Blo 519798 781151 := bstep (se 1 (by rfl) ⟨585863, by rfl⟩ : syracuseStep 781151 = 1171727) B1171727
theorem B781163 : Blo 519798 781163 := bstep (se 1 (by rfl) ⟨585872, by rfl⟩ : syracuseStep 781163 = 1171745) B1171745
theorem B1174535 : Blo 519798 1174535 := bstep (se 1 (by rfl) ⟨880901, by rfl⟩ : syracuseStep 1174535 = 1761803) B1761803
theorem B10742807 : Blo 519798 10742807 := bstep (se 1 (by rfl) ⟨8057105, by rfl⟩ : syracuseStep 10742807 = 16114211) B16114211
theorem B879673 : Blo 519798 879673 := bstep (se 2 (by rfl) ⟨329877, by rfl⟩ : syracuseStep 879673 = 659755) B659755
theorem B781391 : Blo 519798 781391 := bstep (se 1 (by rfl) ⟨586043, by rfl⟩ : syracuseStep 781391 = 1172087) B1172087
theorem B1174607 : Blo 519798 1174607 := bstep (se 1 (by rfl) ⟨880955, by rfl⟩ : syracuseStep 1174607 = 1761911) B1761911
theorem B3959927 : Blo 519798 3959927 := bstep (se 1 (by rfl) ⟨2969945, by rfl⟩ : syracuseStep 3959927 = 5939891) B5939891
theorem B781511 : Blo 519798 781511 := bstep (se 1 (by rfl) ⟨586133, by rfl⟩ : syracuseStep 781511 = 1172267) B1172267
theorem B879815 : Blo 519798 879815 := bstep (se 1 (by rfl) ⟨659861, by rfl⟩ : syracuseStep 879815 = 1319723) B1319723
theorem B1699159 : Blo 519798 1699159 := bstep (se 1 (by rfl) ⟨1274369, by rfl⟩ : syracuseStep 1699159 = 2548739) B2548739
theorem B781673 : Blo 519798 781673 := bstep (se 2 (by rfl) ⟨293127, by rfl⟩ : syracuseStep 781673 = 586255) B586255
theorem B879977 : Blo 519798 879977 := bstep (se 2 (by rfl) ⟨329991, by rfl⟩ : syracuseStep 879977 = 659983) B659983
theorem B781751 : Blo 519798 781751 := bstep (se 1 (by rfl) ⟨586313, by rfl⟩ : syracuseStep 781751 = 1172627) B1172627
theorem B781787 : Blo 519798 781787 := bstep (se 1 (by rfl) ⟨586340, by rfl⟩ : syracuseStep 781787 = 1172681) B1172681
theorem B1175003 : Blo 519798 1175003 := bstep (se 1 (by rfl) ⟨881252, by rfl⟩ : syracuseStep 1175003 = 1762505) B1762505
theorem B1764827 : Blo 519798 1764827 := bstep (se 1 (by rfl) ⟨1323620, by rfl⟩ : syracuseStep 1764827 = 2647241) B2647241
theorem B1666585 : Blo 519798 1666585 := bstep (se 2 (by rfl) ⟨624969, by rfl⟩ : syracuseStep 1666585 = 1249939) B1249939
theorem B519803 : Blo 519798 519803 := bstep (se 1 (by rfl) ⟨389852, by rfl⟩ : syracuseStep 519803 = 779705) B779705
theorem B519855 : Blo 519798 519855 := bstep (se 1 (by rfl) ⟨389891, by rfl⟩ : syracuseStep 519855 = 779783) B779783
theorem B519879 : Blo 519798 519879 := bstep (se 1 (by rfl) ⟨389909, by rfl⟩ : syracuseStep 519879 = 779819) B779819
theorem B519899 : Blo 519798 519899 := bstep (se 1 (by rfl) ⟨389924, by rfl⟩ : syracuseStep 519899 = 779849) B779849
theorem B880375 : Blo 519798 880375 := bstep (se 1 (by rfl) ⟨660281, by rfl⟩ : syracuseStep 880375 = 1320563) B1320563
theorem B519975 : Blo 519798 519975 := bstep (se 1 (by rfl) ⟨389981, by rfl⟩ : syracuseStep 519975 = 779963) B779963
theorem B520015 : Blo 519798 520015 := bstep (se 1 (by rfl) ⟨390011, by rfl⟩ : syracuseStep 520015 = 780023) B780023
theorem B520031 : Blo 519798 520031 := bstep (se 1 (by rfl) ⟨390023, by rfl⟩ : syracuseStep 520031 = 780047) B780047
theorem B520059 : Blo 519798 520059 := bstep (se 1 (by rfl) ⟨390044, by rfl⟩ : syracuseStep 520059 = 780089) B780089
theorem B520111 : Blo 519798 520111 := bstep (se 1 (by rfl) ⟨390083, by rfl⟩ : syracuseStep 520111 = 780167) B780167
theorem B782255 : Blo 519798 782255 := bstep (se 1 (by rfl) ⟨586691, by rfl⟩ : syracuseStep 782255 = 1173383) B1173383
theorem B1175471 : Blo 519798 1175471 := bstep (se 1 (by rfl) ⟨881603, by rfl⟩ : syracuseStep 1175471 = 1763207) B1763207
theorem B880571 : Blo 519798 880571 := bstep (se 1 (by rfl) ⟨660428, by rfl⟩ : syracuseStep 880571 = 1320857) B1320857
theorem B520135 : Blo 519798 520135 := bstep (se 1 (by rfl) ⟨390101, by rfl⟩ : syracuseStep 520135 = 780203) B780203
theorem B520155 : Blo 519798 520155 := bstep (se 1 (by rfl) ⟨390116, by rfl⟩ : syracuseStep 520155 = 780233) B780233
theorem B782345 : Blo 519798 782345 := bstep (se 2 (by rfl) ⟨293379, by rfl⟩ : syracuseStep 782345 = 586759) B586759
theorem B2977829 : Blo 519798 2977829 := bstep (se 4 (by rfl) ⟨279171, by rfl⟩ : syracuseStep 2977829 = 558343) B558343
theorem B520231 : Blo 519798 520231 := bstep (se 1 (by rfl) ⟨390173, by rfl⟩ : syracuseStep 520231 = 780347) B780347
theorem B782375 : Blo 519798 782375 := bstep (se 1 (by rfl) ⟨586781, by rfl⟩ : syracuseStep 782375 = 1173563) B1173563
theorem B880679 : Blo 519798 880679 := bstep (se 1 (by rfl) ⟨660509, by rfl⟩ : syracuseStep 880679 = 1321019) B1321019
theorem B520271 : Blo 519798 520271 := bstep (se 1 (by rfl) ⟨390203, by rfl⟩ : syracuseStep 520271 = 780407) B780407
theorem B520287 : Blo 519798 520287 := bstep (se 1 (by rfl) ⟨390215, by rfl⟩ : syracuseStep 520287 = 780431) B780431
theorem B520315 : Blo 519798 520315 := bstep (se 1 (by rfl) ⟨390236, by rfl⟩ : syracuseStep 520315 = 780473) B780473
theorem B782459 : Blo 519798 782459 := bstep (se 1 (by rfl) ⟨586844, by rfl⟩ : syracuseStep 782459 = 1173689) B1173689
theorem B1765529 : Blo 519798 1765529 := bstep (se 2 (by rfl) ⟨662073, by rfl⟩ : syracuseStep 1765529 = 1324147) B1324147
theorem B1175723 : Blo 519798 1175723 := bstep (se 1 (by rfl) ⟨881792, by rfl⟩ : syracuseStep 1175723 = 1763585) B1763585
theorem B520367 : Blo 519798 520367 := bstep (se 1 (by rfl) ⟨390275, by rfl⟩ : syracuseStep 520367 = 780551) B780551
theorem B520391 : Blo 519798 520391 := bstep (se 1 (by rfl) ⟨390293, by rfl⟩ : syracuseStep 520391 = 780587) B780587
theorem B520411 : Blo 519798 520411 := bstep (se 1 (by rfl) ⟨390308, by rfl⟩ : syracuseStep 520411 = 780617) B780617
theorem B782585 : Blo 519798 782585 := bstep (se 2 (by rfl) ⟨293469, by rfl⟩ : syracuseStep 782585 = 586939) B586939
theorem B520487 : Blo 519798 520487 := bstep (se 1 (by rfl) ⟨390365, by rfl⟩ : syracuseStep 520487 = 780731) B780731
theorem B880969 : Blo 519798 880969 := bstep (se 2 (by rfl) ⟨330363, by rfl⟩ : syracuseStep 880969 = 660727) B660727
theorem B520527 : Blo 519798 520527 := bstep (se 1 (by rfl) ⟨390395, by rfl⟩ : syracuseStep 520527 = 780791) B780791
theorem B520543 : Blo 519798 520543 := bstep (se 1 (by rfl) ⟨390407, by rfl⟩ : syracuseStep 520543 = 780815) B780815
theorem B782687 : Blo 519798 782687 := bstep (se 1 (by rfl) ⟨587015, by rfl⟩ : syracuseStep 782687 = 1174031) B1174031
theorem B782699 : Blo 519798 782699 := bstep (se 1 (by rfl) ⟨587024, by rfl⟩ : syracuseStep 782699 = 1174049) B1174049
theorem B881003 : Blo 519798 881003 := bstep (se 1 (by rfl) ⟨660752, by rfl⟩ : syracuseStep 881003 = 1321505) B1321505
theorem B520571 : Blo 519798 520571 := bstep (se 1 (by rfl) ⟨390428, by rfl⟩ : syracuseStep 520571 = 780857) B780857
theorem B520623 : Blo 519798 520623 := bstep (se 1 (by rfl) ⟨390467, by rfl⟩ : syracuseStep 520623 = 780935) B780935
theorem B520647 : Blo 519798 520647 := bstep (se 1 (by rfl) ⟨390485, by rfl⟩ : syracuseStep 520647 = 780971) B780971
theorem B520667 : Blo 519798 520667 := bstep (se 1 (by rfl) ⟨390500, by rfl⟩ : syracuseStep 520667 = 781001) B781001
theorem B14283229 : Blo 519798 14283229 := bstep (se 3 (by rfl) ⟨2678105, by rfl⟩ : syracuseStep 14283229 = 5356211) B5356211
theorem B2978329 : Blo 519798 2978329 := bstep (se 2 (by rfl) ⟨1116873, by rfl⟩ : syracuseStep 2978329 = 2233747) B2233747
theorem B520743 : Blo 519798 520743 := bstep (se 1 (by rfl) ⟨390557, by rfl⟩ : syracuseStep 520743 = 781115) B781115
theorem B520783 : Blo 519798 520783 := bstep (se 1 (by rfl) ⟨390587, by rfl⟩ : syracuseStep 520783 = 781175) B781175
theorem B782927 : Blo 519798 782927 := bstep (se 1 (by rfl) ⟨587195, by rfl⟩ : syracuseStep 782927 = 1174391) B1174391
theorem B520799 : Blo 519798 520799 := bstep (se 1 (by rfl) ⟨390599, by rfl⟩ : syracuseStep 520799 = 781199) B781199
theorem B520827 : Blo 519798 520827 := bstep (se 1 (by rfl) ⟨390620, by rfl⟩ : syracuseStep 520827 = 781241) B781241
theorem B586363 : Blo 519798 586363 := bstep (se 1 (by rfl) ⟨439772, by rfl⟩ : syracuseStep 586363 = 879545) B879545
theorem B520879 : Blo 519798 520879 := bstep (se 1 (by rfl) ⟨390659, by rfl⟩ : syracuseStep 520879 = 781319) B781319
theorem B1176263 : Blo 519798 1176263 := bstep (se 1 (by rfl) ⟨882197, by rfl⟩ : syracuseStep 1176263 = 1764395) B1764395
theorem B520903 : Blo 519798 520903 := bstep (se 1 (by rfl) ⟨390677, by rfl⟩ : syracuseStep 520903 = 781355) B781355
theorem B783047 : Blo 519798 783047 := bstep (se 1 (by rfl) ⟨587285, by rfl⟩ : syracuseStep 783047 = 1174571) B1174571
theorem B520923 : Blo 519798 520923 := bstep (se 1 (by rfl) ⟨390692, by rfl⟩ : syracuseStep 520923 = 781385) B781385
theorem B881401 : Blo 519798 881401 := bstep (se 2 (by rfl) ⟨330525, by rfl⟩ : syracuseStep 881401 = 661051) B661051
theorem B13202189 : Blo 519798 13202189 := bstep (se 3 (by rfl) ⟨2475410, by rfl⟩ : syracuseStep 13202189 = 4950821) B4950821
theorem B520999 : Blo 519798 520999 := bstep (se 1 (by rfl) ⟨390749, by rfl⟩ : syracuseStep 520999 = 781499) B781499
theorem B521039 : Blo 519798 521039 := bstep (se 1 (by rfl) ⟨390779, by rfl⟩ : syracuseStep 521039 = 781559) B781559
theorem B521055 : Blo 519798 521055 := bstep (se 1 (by rfl) ⟨390791, by rfl⟩ : syracuseStep 521055 = 781583) B781583
theorem B783209 : Blo 519798 783209 := bstep (se 2 (by rfl) ⟨293703, by rfl⟩ : syracuseStep 783209 = 587407) B587407
theorem B521083 : Blo 519798 521083 := bstep (se 1 (by rfl) ⟨390812, by rfl⟩ : syracuseStep 521083 = 781625) B781625
theorem B521135 : Blo 519798 521135 := bstep (se 1 (by rfl) ⟨390851, by rfl⟩ : syracuseStep 521135 = 781703) B781703
theorem B783287 : Blo 519798 783287 := bstep (se 1 (by rfl) ⟨587465, by rfl⟩ : syracuseStep 783287 = 1174931) B1174931
theorem B521159 : Blo 519798 521159 := bstep (se 1 (by rfl) ⟨390869, by rfl⟩ : syracuseStep 521159 = 781739) B781739
theorem B521179 : Blo 519798 521179 := bstep (se 1 (by rfl) ⟨390884, by rfl⟩ : syracuseStep 521179 = 781769) B781769
theorem B783323 : Blo 519798 783323 := bstep (se 1 (by rfl) ⟨587492, by rfl⟩ : syracuseStep 783323 = 1174985) B1174985
theorem B2814977 : Blo 519798 2814977 := bstep (se 2 (by rfl) ⟨1055616, by rfl⟩ : syracuseStep 2814977 = 2111233) B2111233
theorem B881671 : Blo 519798 881671 := bstep (se 1 (by rfl) ⟨661253, by rfl⟩ : syracuseStep 881671 = 1322507) B1322507
theorem B2225171 : Blo 519798 2225171 := bstep (se 1 (by rfl) ⟨1668878, by rfl⟩ : syracuseStep 2225171 = 3337757) B3337757
theorem B521255 : Blo 519798 521255 := bstep (se 1 (by rfl) ⟨390941, by rfl⟩ : syracuseStep 521255 = 781883) B781883
theorem B521295 : Blo 519798 521295 := bstep (se 1 (by rfl) ⟨390971, by rfl⟩ : syracuseStep 521295 = 781943) B781943
theorem B586831 : Blo 519798 586831 := bstep (se 1 (by rfl) ⟨440123, by rfl⟩ : syracuseStep 586831 = 880247) B880247
theorem B521311 : Blo 519798 521311 := bstep (se 1 (by rfl) ⟨390983, by rfl⟩ : syracuseStep 521311 = 781967) B781967
theorem B521339 : Blo 519798 521339 := bstep (se 1 (by rfl) ⟨391004, by rfl⟩ : syracuseStep 521339 = 782009) B782009
theorem B521391 : Blo 519798 521391 := bstep (se 1 (by rfl) ⟨391043, by rfl⟩ : syracuseStep 521391 = 782087) B782087
theorem B521415 : Blo 519798 521415 := bstep (se 1 (by rfl) ⟨391061, by rfl⟩ : syracuseStep 521415 = 782123) B782123
theorem B521435 : Blo 519798 521435 := bstep (se 1 (by rfl) ⟨391076, by rfl⟩ : syracuseStep 521435 = 782153) B782153
theorem B521511 : Blo 519798 521511 := bstep (se 1 (by rfl) ⟨391133, by rfl⟩ : syracuseStep 521511 = 782267) B782267
theorem B1766717 : Blo 519798 1766717 := bstep (se 3 (by rfl) ⟨331259, by rfl⟩ : syracuseStep 1766717 = 662519) B662519
theorem B521551 : Blo 519798 521551 := bstep (se 1 (by rfl) ⟨391163, by rfl⟩ : syracuseStep 521551 = 782327) B782327
theorem B521567 : Blo 519798 521567 := bstep (se 1 (by rfl) ⟨391175, by rfl⟩ : syracuseStep 521567 = 782351) B782351
theorem B521595 : Blo 519798 521595 := bstep (se 1 (by rfl) ⟨391196, by rfl⟩ : syracuseStep 521595 = 782393) B782393
theorem B521647 : Blo 519798 521647 := bstep (se 1 (by rfl) ⟨391235, by rfl⟩ : syracuseStep 521647 = 782471) B782471
theorem B783791 : Blo 519798 783791 := bstep (se 1 (by rfl) ⟨587843, by rfl⟩ : syracuseStep 783791 = 1175687) B1175687
theorem B882103 : Blo 519798 882103 := bstep (se 1 (by rfl) ⟨661577, by rfl⟩ : syracuseStep 882103 = 1323155) B1323155
theorem B521671 : Blo 519798 521671 := bstep (se 1 (by rfl) ⟨391253, by rfl⟩ : syracuseStep 521671 = 782507) B782507
theorem B521691 : Blo 519798 521691 := bstep (se 1 (by rfl) ⟨391268, by rfl⟩ : syracuseStep 521691 = 782537) B782537
theorem B587227 : Blo 519798 587227 := bstep (se 1 (by rfl) ⟨440420, by rfl⟩ : syracuseStep 587227 = 880841) B880841
theorem B783881 : Blo 519798 783881 := bstep (se 2 (by rfl) ⟨293955, by rfl⟩ : syracuseStep 783881 = 587911) B587911
theorem B1668647 : Blo 519798 1668647 := bstep (se 1 (by rfl) ⟨1251485, by rfl⟩ : syracuseStep 1668647 = 2502971) B2502971
theorem B521767 : Blo 519798 521767 := bstep (se 1 (by rfl) ⟨391325, by rfl⟩ : syracuseStep 521767 = 782651) B782651
theorem B783911 : Blo 519798 783911 := bstep (se 1 (by rfl) ⟨587933, by rfl⟩ : syracuseStep 783911 = 1175867) B1175867
theorem B1177127 : Blo 519798 1177127 := bstep (se 1 (by rfl) ⟨882845, by rfl⟩ : syracuseStep 1177127 = 1765691) B1765691
theorem B521807 : Blo 519798 521807 := bstep (se 1 (by rfl) ⟨391355, by rfl⟩ : syracuseStep 521807 = 782711) B782711
theorem B521823 : Blo 519798 521823 := bstep (se 1 (by rfl) ⟨391367, by rfl⟩ : syracuseStep 521823 = 782735) B782735
theorem B521851 : Blo 519798 521851 := bstep (se 1 (by rfl) ⟨391388, by rfl⟩ : syracuseStep 521851 = 782777) B782777
theorem B783995 : Blo 519798 783995 := bstep (se 1 (by rfl) ⟨587996, by rfl⟩ : syracuseStep 783995 = 1175993) B1175993
theorem B882299 : Blo 519798 882299 := bstep (se 1 (by rfl) ⟨661724, by rfl⟩ : syracuseStep 882299 = 1323449) B1323449
theorem B521903 : Blo 519798 521903 := bstep (se 1 (by rfl) ⟨391427, by rfl⟩ : syracuseStep 521903 = 782855) B782855
theorem B521927 : Blo 519798 521927 := bstep (se 1 (by rfl) ⟨391445, by rfl⟩ : syracuseStep 521927 = 782891) B782891
theorem B521947 : Blo 519798 521947 := bstep (se 1 (by rfl) ⟨391460, by rfl⟩ : syracuseStep 521947 = 782921) B782921
theorem B784121 : Blo 519798 784121 := bstep (se 2 (by rfl) ⟨294045, by rfl⟩ : syracuseStep 784121 = 588091) B588091
theorem B522023 : Blo 519798 522023 := bstep (se 1 (by rfl) ⟨391517, by rfl⟩ : syracuseStep 522023 = 783035) B783035
theorem B522063 : Blo 519798 522063 := bstep (se 1 (by rfl) ⟨391547, by rfl⟩ : syracuseStep 522063 = 783095) B783095
theorem B522079 : Blo 519798 522079 := bstep (se 1 (by rfl) ⟨391559, by rfl⟩ : syracuseStep 522079 = 783119) B783119
theorem B784223 : Blo 519798 784223 := bstep (se 1 (by rfl) ⟨588167, by rfl⟩ : syracuseStep 784223 = 1176335) B1176335
theorem B784235 : Blo 519798 784235 := bstep (se 1 (by rfl) ⟨588176, by rfl⟩ : syracuseStep 784235 = 1176353) B1176353
theorem B1177451 : Blo 519798 1177451 := bstep (se 1 (by rfl) ⟨883088, by rfl⟩ : syracuseStep 1177451 = 1766177) B1766177
theorem B522107 : Blo 519798 522107 := bstep (se 1 (by rfl) ⟨391580, by rfl⟩ : syracuseStep 522107 = 783161) B783161
theorem B1177505 : Blo 519798 1177505 := bstep (se 2 (by rfl) ⟨441564, by rfl⟩ : syracuseStep 1177505 = 883129) B883129
theorem B522159 : Blo 519798 522159 := bstep (se 1 (by rfl) ⟨391619, by rfl⟩ : syracuseStep 522159 = 783239) B783239
theorem B587695 : Blo 519798 587695 := bstep (se 1 (by rfl) ⟨440771, by rfl⟩ : syracuseStep 587695 = 881543) B881543
theorem B3340217 : Blo 519798 3340217 := bstep (se 2 (by rfl) ⟨1252581, by rfl⟩ : syracuseStep 3340217 = 2505163) B2505163
theorem B522183 : Blo 519798 522183 := bstep (se 1 (by rfl) ⟨391637, by rfl⟩ : syracuseStep 522183 = 783275) B783275
theorem B522203 : Blo 519798 522203 := bstep (se 1 (by rfl) ⟨391652, by rfl⟩ : syracuseStep 522203 = 783305) B783305
theorem B882697 : Blo 519798 882697 := bstep (se 2 (by rfl) ⟨331011, by rfl⟩ : syracuseStep 882697 = 662023) B662023
theorem B522279 : Blo 519798 522279 := bstep (se 1 (by rfl) ⟨391709, by rfl⟩ : syracuseStep 522279 = 783419) B783419
theorem B522319 : Blo 519798 522319 := bstep (se 1 (by rfl) ⟨391739, by rfl⟩ : syracuseStep 522319 = 783479) B783479
theorem B784463 : Blo 519798 784463 := bstep (se 1 (by rfl) ⟨588347, by rfl⟩ : syracuseStep 784463 = 1176695) B1176695
theorem B3340369 : Blo 519798 3340369 := bstep (se 2 (by rfl) ⟨1252638, by rfl⟩ : syracuseStep 3340369 = 2505277) B2505277
theorem B522335 : Blo 519798 522335 := bstep (se 1 (by rfl) ⟨391751, by rfl⟩ : syracuseStep 522335 = 783503) B783503
theorem B555131 : Blo 519798 555131 := bstep (se 1 (by rfl) ⟨416348, by rfl⟩ : syracuseStep 555131 = 832697) B832697
theorem B522363 : Blo 519798 522363 := bstep (se 1 (by rfl) ⟨391772, by rfl⟩ : syracuseStep 522363 = 783545) B783545
theorem B1767581 : Blo 519798 1767581 := bstep (se 3 (by rfl) ⟨331421, by rfl⟩ : syracuseStep 1767581 = 662843) B662843
theorem B882859 : Blo 519798 882859 := bstep (se 1 (by rfl) ⟨662144, by rfl⟩ : syracuseStep 882859 = 1324289) B1324289
theorem B522415 : Blo 519798 522415 := bstep (se 1 (by rfl) ⟨391811, by rfl⟩ : syracuseStep 522415 = 783623) B783623
theorem B522439 : Blo 519798 522439 := bstep (se 1 (by rfl) ⟨391829, by rfl⟩ : syracuseStep 522439 = 783659) B783659
theorem B784583 : Blo 519798 784583 := bstep (se 1 (by rfl) ⟨588437, by rfl⟩ : syracuseStep 784583 = 1176875) B1176875
theorem B522459 : Blo 519798 522459 := bstep (se 1 (by rfl) ⟨391844, by rfl⟩ : syracuseStep 522459 = 783689) B783689
theorem B1177847 : Blo 519798 1177847 := bstep (se 1 (by rfl) ⟨883385, by rfl⟩ : syracuseStep 1177847 = 1766771) B1766771
theorem B522535 : Blo 519798 522535 := bstep (se 1 (by rfl) ⟨391901, by rfl⟩ : syracuseStep 522535 = 783803) B783803
theorem B522575 : Blo 519798 522575 := bstep (se 1 (by rfl) ⟨391931, by rfl⟩ : syracuseStep 522575 = 783863) B783863
theorem B522591 : Blo 519798 522591 := bstep (se 1 (by rfl) ⟨391943, by rfl⟩ : syracuseStep 522591 = 783887) B783887
theorem B588127 : Blo 519798 588127 := bstep (se 1 (by rfl) ⟨441095, by rfl⟩ : syracuseStep 588127 = 882191) B882191
theorem B784745 : Blo 519798 784745 := bstep (se 2 (by rfl) ⟨294279, by rfl⟩ : syracuseStep 784745 = 588559) B588559
theorem B522619 : Blo 519798 522619 := bstep (se 1 (by rfl) ⟨391964, by rfl⟩ : syracuseStep 522619 = 783929) B783929
theorem B522671 : Blo 519798 522671 := bstep (se 1 (by rfl) ⟨392003, by rfl⟩ : syracuseStep 522671 = 784007) B784007
theorem B784823 : Blo 519798 784823 := bstep (se 1 (by rfl) ⟨588617, by rfl⟩ : syracuseStep 784823 = 1177235) B1177235
theorem B522695 : Blo 519798 522695 := bstep (se 1 (by rfl) ⟨392021, by rfl⟩ : syracuseStep 522695 = 784043) B784043
theorem B522715 : Blo 519798 522715 := bstep (se 1 (by rfl) ⟨392036, by rfl⟩ : syracuseStep 522715 = 784073) B784073
theorem B784859 : Blo 519798 784859 := bstep (se 1 (by rfl) ⟨588644, by rfl⟩ : syracuseStep 784859 = 1177289) B1177289
theorem B883163 : Blo 519798 883163 := bstep (se 1 (by rfl) ⟨662372, by rfl⟩ : syracuseStep 883163 = 1324745) B1324745
theorem B522791 : Blo 519798 522791 := bstep (se 1 (by rfl) ⟨392093, by rfl⟩ : syracuseStep 522791 = 784187) B784187
theorem B522831 : Blo 519798 522831 := bstep (se 1 (by rfl) ⟨392123, by rfl⟩ : syracuseStep 522831 = 784247) B784247
theorem B522847 : Blo 519798 522847 := bstep (se 1 (by rfl) ⟨392135, by rfl⟩ : syracuseStep 522847 = 784271) B784271
theorem B522875 : Blo 519798 522875 := bstep (se 1 (by rfl) ⟨392156, by rfl⟩ : syracuseStep 522875 = 784313) B784313
theorem B522927 : Blo 519798 522927 := bstep (se 1 (by rfl) ⟨392195, by rfl⟩ : syracuseStep 522927 = 784391) B784391
theorem B522951 : Blo 519798 522951 := bstep (se 1 (by rfl) ⟨392213, by rfl⟩ : syracuseStep 522951 = 784427) B784427
theorem B588487 : Blo 519798 588487 := bstep (se 1 (by rfl) ⟨441365, by rfl⟩ : syracuseStep 588487 = 882731) B882731
theorem B883399 : Blo 519798 883399 := bstep (se 1 (by rfl) ⟨662549, by rfl⟩ : syracuseStep 883399 = 1325099) B1325099
theorem B522971 : Blo 519798 522971 := bstep (se 1 (by rfl) ⟨392228, by rfl⟩ : syracuseStep 522971 = 784457) B784457
theorem B523047 : Blo 519798 523047 := bstep (se 1 (by rfl) ⟨392285, by rfl⟩ : syracuseStep 523047 = 784571) B784571
theorem B1178441 : Blo 519798 1178441 := bstep (se 2 (by rfl) ⟨441915, by rfl⟩ : syracuseStep 1178441 = 883831) B883831
theorem B5438285 : Blo 519798 5438285 := bstep (se 3 (by rfl) ⟨1019678, by rfl⟩ : syracuseStep 5438285 = 2039357) B2039357
theorem B523087 : Blo 519798 523087 := bstep (se 1 (by rfl) ⟨392315, by rfl⟩ : syracuseStep 523087 = 784631) B784631
theorem B523103 : Blo 519798 523103 := bstep (se 1 (by rfl) ⟨392327, by rfl⟩ : syracuseStep 523103 = 784655) B784655
theorem B883561 : Blo 519798 883561 := bstep (se 2 (by rfl) ⟨331335, by rfl⟩ : syracuseStep 883561 = 662671) B662671
theorem B523131 : Blo 519798 523131 := bstep (se 1 (by rfl) ⟨392348, by rfl⟩ : syracuseStep 523131 = 784697) B784697
theorem B523183 : Blo 519798 523183 := bstep (se 1 (by rfl) ⟨392387, by rfl⟩ : syracuseStep 523183 = 784775) B784775
theorem B785327 : Blo 519798 785327 := bstep (se 1 (by rfl) ⟨588995, by rfl⟩ : syracuseStep 785327 = 1177991) B1177991
theorem B1670071 : Blo 519798 1670071 := bstep (se 1 (by rfl) ⟨1252553, by rfl⟩ : syracuseStep 1670071 = 2505107) B2505107
theorem B523207 : Blo 519798 523207 := bstep (se 1 (by rfl) ⟨392405, by rfl⟩ : syracuseStep 523207 = 784811) B784811
theorem B523227 : Blo 519798 523227 := bstep (se 1 (by rfl) ⟨392420, by rfl⟩ : syracuseStep 523227 = 784841) B784841
theorem B785417 : Blo 519798 785417 := bstep (se 2 (by rfl) ⟨294531, by rfl⟩ : syracuseStep 785417 = 589063) B589063
theorem B523303 : Blo 519798 523303 := bstep (se 1 (by rfl) ⟨392477, by rfl⟩ : syracuseStep 523303 = 784955) B784955
theorem B785447 : Blo 519798 785447 := bstep (se 1 (by rfl) ⟨589085, by rfl⟩ : syracuseStep 785447 = 1178171) B1178171
theorem B523343 : Blo 519798 523343 := bstep (se 1 (by rfl) ⟨392507, by rfl⟩ : syracuseStep 523343 = 785015) B785015
theorem B523359 : Blo 519798 523359 := bstep (se 1 (by rfl) ⟨392519, by rfl⟩ : syracuseStep 523359 = 785039) B785039
theorem B523387 : Blo 519798 523387 := bstep (se 1 (by rfl) ⟨392540, by rfl⟩ : syracuseStep 523387 = 785081) B785081
theorem B785531 : Blo 519798 785531 := bstep (se 1 (by rfl) ⟨589148, by rfl⟩ : syracuseStep 785531 = 1178297) B1178297
theorem B523439 : Blo 519798 523439 := bstep (se 1 (by rfl) ⟨392579, by rfl⟩ : syracuseStep 523439 = 785159) B785159
theorem B523463 : Blo 519798 523463 := bstep (se 1 (by rfl) ⟨392597, by rfl⟩ : syracuseStep 523463 = 785195) B785195
theorem B523483 : Blo 519798 523483 := bstep (se 1 (by rfl) ⟨392612, by rfl⟩ : syracuseStep 523483 = 785225) B785225
theorem B785657 : Blo 519798 785657 := bstep (se 2 (by rfl) ⟨294621, by rfl⟩ : syracuseStep 785657 = 589243) B589243
theorem B523559 : Blo 519798 523559 := bstep (se 1 (by rfl) ⟨392669, by rfl⟩ : syracuseStep 523559 = 785339) B785339
theorem B523599 : Blo 519798 523599 := bstep (se 1 (by rfl) ⟨392699, by rfl⟩ : syracuseStep 523599 = 785399) B785399
theorem B523615 : Blo 519798 523615 := bstep (se 1 (by rfl) ⟨392711, by rfl⟩ : syracuseStep 523615 = 785423) B785423
theorem B621919 : Blo 519798 621919 := bstep (se 1 (by rfl) ⟨466439, by rfl⟩ : syracuseStep 621919 = 932879) B932879
theorem B523643 : Blo 519798 523643 := bstep (se 1 (by rfl) ⟨392732, by rfl⟩ : syracuseStep 523643 = 785465) B785465
theorem B2981245 : Blo 519798 2981245 := bstep (se 3 (by rfl) ⟨558983, by rfl⟩ : syracuseStep 2981245 = 1117967) B1117967
theorem B523695 : Blo 519798 523695 := bstep (se 1 (by rfl) ⟨392771, by rfl⟩ : syracuseStep 523695 = 785543) B785543
theorem B523719 : Blo 519798 523719 := bstep (se 1 (by rfl) ⟨392789, by rfl⟩ : syracuseStep 523719 = 785579) B785579
theorem B523739 : Blo 519798 523739 := bstep (se 1 (by rfl) ⟨392804, by rfl⟩ : syracuseStep 523739 = 785609) B785609
theorem B2817575 : Blo 519798 2817575 := bstep (se 1 (by rfl) ⟨2113181, by rfl⟩ : syracuseStep 2817575 = 4226363) B4226363
theorem B4226849 : Blo 519798 4226849 := bstep (se 2 (by rfl) ⟨1585068, by rfl⟩ : syracuseStep 4226849 = 3170137) B3170137
theorem B3342215 : Blo 519798 3342215 := bstep (se 1 (by rfl) ⟨2506661, by rfl⟩ : syracuseStep 3342215 = 5013323) B5013323
theorem B9503405 : Blo 519798 9503405 := bstep (se 3 (by rfl) ⟨1781888, by rfl⟩ : syracuseStep 9503405 = 3563777) B3563777
theorem B9634619 : Blo 519798 9634619 := bstep (se 1 (by rfl) ⟨7225964, by rfl⟩ : syracuseStep 9634619 = 14451929) B14451929
theorem B5637221 : Blo 519798 5637221 := bstep (se 4 (by rfl) ⟨528489, by rfl⟩ : syracuseStep 5637221 = 1056979) B1056979
theorem B2229373 : Blo 519798 2229373 := bstep (se 3 (by rfl) ⟨418007, by rfl⟩ : syracuseStep 2229373 = 836015) B836015
theorem B1410335 : Blo 519798 1410335 := bstep (se 1 (by rfl) ⟨1057751, by rfl⟩ : syracuseStep 1410335 = 2115503) B2115503
theorem B8914211 : Blo 519798 8914211 := bstep (se 1 (by rfl) ⟨6685658, by rfl⟩ : syracuseStep 8914211 = 13371317) B13371317
theorem B5932601 : Blo 519798 5932601 := bstep (se 2 (by rfl) ⟨2224725, by rfl⟩ : syracuseStep 5932601 = 4449451) B4449451
theorem B9144515 : Blo 519798 9144515 := bstep (se 1 (by rfl) ⟨6858386, by rfl⟩ : syracuseStep 9144515 = 13716773) B13716773
theorem B1673723 : Blo 519798 1673723 := bstep (se 1 (by rfl) ⟨1255292, by rfl⟩ : syracuseStep 1673723 = 2510585) B2510585
theorem B657983 : Blo 519798 657983 := bstep (se 1 (by rfl) ⟨493487, by rfl⟩ : syracuseStep 657983 = 986975) B986975
theorem B1117147 : Blo 519798 1117147 := bstep (se 1 (by rfl) ⟨837860, by rfl⟩ : syracuseStep 1117147 = 1675721) B1675721
theorem B4459535 : Blo 519798 4459535 := bstep (se 1 (by rfl) ⟨3344651, by rfl⟩ : syracuseStep 4459535 = 6689303) B6689303
theorem B1412615 : Blo 519798 1412615 := bstep (se 1 (by rfl) ⟨1059461, by rfl⟩ : syracuseStep 1412615 = 2118923) B2118923
theorem B3968675 : Blo 519798 3968675 := bstep (se 1 (by rfl) ⟨2976506, by rfl⟩ : syracuseStep 3968675 = 5953013) B5953013
theorem B11243299 : Blo 519798 11243299 := bstep (se 1 (by rfl) ⟨8432474, by rfl⟩ : syracuseStep 11243299 = 16864949) B16864949
theorem B1675055 : Blo 519798 1675055 := bstep (se 1 (by rfl) ⟨1256291, by rfl⟩ : syracuseStep 1675055 = 2512583) B2512583
theorem B659279 : Blo 519798 659279 := bstep (se 1 (by rfl) ⟨494459, by rfl⟩ : syracuseStep 659279 = 988919) B988919
theorem B659431 : Blo 519798 659431 := bstep (se 1 (by rfl) ⟨494573, by rfl⟩ : syracuseStep 659431 = 989147) B989147
theorem B987241 : Blo 519798 987241 := bstep (se 2 (by rfl) ⟨370215, by rfl⟩ : syracuseStep 987241 = 740431) B740431
theorem B11309219 : Blo 519798 11309219 := bstep (se 1 (by rfl) ⟨8481914, by rfl⟩ : syracuseStep 11309219 = 16963829) B16963829
theorem B6688939 : Blo 519798 6688939 := bstep (se 1 (by rfl) ⟨5016704, by rfl⟩ : syracuseStep 6688939 = 10033409) B10033409
theorem B3346703 : Blo 519798 3346703 := bstep (se 1 (by rfl) ⟨2510027, by rfl⟩ : syracuseStep 3346703 = 5020055) B5020055
theorem B4460933 : Blo 519798 4460933 := bstep (se 4 (by rfl) ⟨418212, by rfl⟩ : syracuseStep 4460933 = 836425) B836425
theorem B889255 : Blo 519798 889255 := bstep (se 1 (by rfl) ⟨666941, by rfl⟩ : syracuseStep 889255 = 1333883) B1333883
theorem B2265545 : Blo 519798 2265545 := bstep (se 2 (by rfl) ⟨849579, by rfl⟩ : syracuseStep 2265545 = 1699159) B1699159
theorem B987643 : Blo 519798 987643 := bstep (se 1 (by rfl) ⟨740732, by rfl⟩ : syracuseStep 987643 = 1481465) B1481465
theorem B2822809 : Blo 519798 2822809 := bstep (se 2 (by rfl) ⟨1058553, by rfl⟩ : syracuseStep 2822809 = 2117107) B2117107
theorem B987871 : Blo 519798 987871 := bstep (se 1 (by rfl) ⟨740903, by rfl⟩ : syracuseStep 987871 = 1481807) B1481807
theorem B988615 : Blo 519798 988615 := bstep (se 1 (by rfl) ⟨741461, by rfl⟩ : syracuseStep 988615 = 1482923) B1482923
theorem B1480349 : Blo 519798 1480349 := bstep (se 3 (by rfl) ⟨277565, by rfl⟩ : syracuseStep 1480349 = 555131) B555131
theorem B1316513 : Blo 519798 1316513 := bstep (se 2 (by rfl) ⟨493692, by rfl⟩ : syracuseStep 1316513 = 987385) B987385
theorem B19044305 : Blo 519798 19044305 := bstep (se 2 (by rfl) ⟨7141614, by rfl⟩ : syracuseStep 19044305 = 14283229) B14283229
theorem B3971105 : Blo 519798 3971105 := bstep (se 2 (by rfl) ⟨1489164, by rfl⟩ : syracuseStep 3971105 = 2978329) B2978329
theorem B1316969 : Blo 519798 1316969 := bstep (se 2 (by rfl) ⟨493863, by rfl⟩ : syracuseStep 1316969 = 987727) B987727
theorem B7510295 : Blo 519798 7510295 := bstep (se 1 (by rfl) ⟨5632721, by rfl⟩ : syracuseStep 7510295 = 11265443) B11265443
theorem B661871 : Blo 519798 661871 := bstep (se 1 (by rfl) ⟨496403, by rfl⟩ : syracuseStep 661871 = 992807) B992807
theorem B661927 : Blo 519798 661927 := bstep (se 1 (by rfl) ⟨496445, by rfl⟩ : syracuseStep 661927 = 992891) B992891
theorem B1317455 : Blo 519798 1317455 := bstep (se 1 (by rfl) ⟨988091, by rfl⟩ : syracuseStep 1317455 = 1976183) B1976183
theorem B3349187 : Blo 519798 3349187 := bstep (se 1 (by rfl) ⟨2511890, by rfl⟩ : syracuseStep 3349187 = 5023781) B5023781
theorem B662251 : Blo 519798 662251 := bstep (se 1 (by rfl) ⟨496688, by rfl⟩ : syracuseStep 662251 = 993377) B993377
theorem B3251117 : Blo 519798 3251117 := bstep (se 3 (by rfl) ⟨609584, by rfl⟩ : syracuseStep 3251117 = 1219169) B1219169
theorem B1318103 : Blo 519798 1318103 := bstep (se 1 (by rfl) ⟨988577, by rfl⟩ : syracuseStep 1318103 = 1977155) B1977155
theorem B1252601 : Blo 519798 1252601 := bstep (se 2 (by rfl) ⟨469725, by rfl⟩ : syracuseStep 1252601 = 939451) B939451
theorem B4005335 : Blo 519798 4005335 := bstep (se 1 (by rfl) ⟨3004001, by rfl⟩ : syracuseStep 4005335 = 6008003) B6008003
theorem B33889751 : Blo 519798 33889751 := bstep (se 1 (by rfl) ⟨25417313, by rfl⟩ : syracuseStep 33889751 = 50834627) B50834627
theorem B1973753 : Blo 519798 1973753 := bstep (se 2 (by rfl) ⟨740157, by rfl⟩ : syracuseStep 1973753 = 1480315) B1480315
theorem B1252871 : Blo 519798 1252871 := bstep (se 1 (by rfl) ⟨939653, by rfl⟩ : syracuseStep 1252871 = 1879307) B1879307
theorem B1318457 : Blo 519798 1318457 := bstep (se 2 (by rfl) ⟨494421, by rfl⟩ : syracuseStep 1318457 = 988843) B988843
theorem B8494753 : Blo 519798 8494753 := bstep (se 2 (by rfl) ⟨3185532, by rfl⟩ : syracuseStep 8494753 = 6371065) B6371065
theorem B627351317 : Blo 519798 627351317 := bstep (se 6 (by rfl) ⟨14703546, by rfl⟩ : syracuseStep 627351317 = 29407093) B29407093
theorem B2236891 : Blo 519798 2236891 := bstep (se 1 (by rfl) ⟨1677668, by rfl⟩ : syracuseStep 2236891 = 3355337) B3355337
theorem B991865 : Blo 519798 991865 := bstep (se 2 (by rfl) ⟨371949, by rfl⟩ : syracuseStep 991865 = 743899) B743899
theorem B1876651 : Blo 519798 1876651 := bstep (se 1 (by rfl) ⟨1407488, by rfl⟩ : syracuseStep 1876651 = 2814977) B2814977
theorem B991919 : Blo 519798 991919 := bstep (se 1 (by rfl) ⟨743939, by rfl⟩ : syracuseStep 991919 = 1487879) B1487879
theorem B1483447 : Blo 519798 1483447 := bstep (se 1 (by rfl) ⟨1112585, by rfl⟩ : syracuseStep 1483447 = 2225171) B2225171
theorem B3810007 : Blo 519798 3810007 := bstep (se 1 (by rfl) ⟨2857505, by rfl⟩ : syracuseStep 3810007 = 5715011) B5715011
theorem B1975529 : Blo 519798 1975529 := bstep (se 2 (by rfl) ⟨740823, by rfl⟩ : syracuseStep 1975529 = 1481647) B1481647
theorem B3351851 : Blo 519798 3351851 := bstep (se 1 (by rfl) ⟨2513888, by rfl⟩ : syracuseStep 3351851 = 5027777) B5027777
theorem B11412859 : Blo 519798 11412859 := bstep (se 1 (by rfl) ⟨8559644, by rfl⟩ : syracuseStep 11412859 = 17119289) B17119289
theorem B1779083 : Blo 519798 1779083 := bstep (se 1 (by rfl) ⟨1334312, by rfl⟩ : syracuseStep 1779083 = 2668625) B2668625
theorem B1582649 : Blo 519798 1582649 := bstep (se 2 (by rfl) ⟨593493, by rfl⟩ : syracuseStep 1582649 = 1186987) B1186987
theorem B1255099 : Blo 519798 1255099 := bstep (se 1 (by rfl) ⟨941324, by rfl⟩ : syracuseStep 1255099 = 1882649) B1882649
theorem B1320745 : Blo 519798 1320745 := bstep (se 2 (by rfl) ⟨495279, by rfl⟩ : syracuseStep 1320745 = 990559) B990559
theorem B829225 : Blo 519798 829225 := bstep (se 2 (by rfl) ⟨310959, by rfl⟩ : syracuseStep 829225 = 621919) B621919
theorem B3974993 : Blo 519798 3974993 := bstep (se 2 (by rfl) ⟨1490622, by rfl⟩ : syracuseStep 3974993 = 2981245) B2981245
theorem B1878383 : Blo 519798 1878383 := bstep (se 1 (by rfl) ⟨1408787, by rfl⟩ : syracuseStep 1878383 = 2817575) B2817575
theorem B6695297 : Blo 519798 6695297 := bstep (se 2 (by rfl) ⟨2510736, by rfl⟩ : syracuseStep 6695297 = 5021473) B5021473
theorem B993703 : Blo 519798 993703 := bstep (se 1 (by rfl) ⟨745277, by rfl⟩ : syracuseStep 993703 = 1490555) B1490555
theorem B1321535 : Blo 519798 1321535 := bstep (se 1 (by rfl) ⟨991151, by rfl⟩ : syracuseStep 1321535 = 1982303) B1982303
theorem B993863 : Blo 519798 993863 := bstep (se 1 (by rfl) ⟨745397, by rfl⟩ : syracuseStep 993863 = 1490795) B1490795
theorem B6761083 : Blo 519798 6761083 := bstep (se 1 (by rfl) ⟨5070812, by rfl⟩ : syracuseStep 6761083 = 10141625) B10141625
theorem B994295 : Blo 519798 994295 := bstep (se 1 (by rfl) ⟨745721, by rfl⟩ : syracuseStep 994295 = 1491443) B1491443
theorem B1322183 : Blo 519798 1322183 := bstep (se 1 (by rfl) ⟨991637, by rfl⟩ : syracuseStep 1322183 = 1983275) B1983275
theorem B1322203 : Blo 519798 1322203 := bstep (se 1 (by rfl) ⟨991652, by rfl⟩ : syracuseStep 1322203 = 1983305) B1983305
theorem B14265719 : Blo 519798 14265719 := bstep (se 1 (by rfl) ⟨10699289, by rfl⟩ : syracuseStep 14265719 = 21398579) B21398579
theorem B2633147 : Blo 519798 2633147 := bstep (se 1 (by rfl) ⟨1974860, by rfl⟩ : syracuseStep 2633147 = 3949721) B3949721
theorem B1486295 : Blo 519798 1486295 := bstep (se 1 (by rfl) ⟨1114721, by rfl⟩ : syracuseStep 1486295 = 2229443) B2229443
theorem B1060345 : Blo 519798 1060345 := bstep (se 2 (by rfl) ⟨397629, by rfl⟩ : syracuseStep 1060345 = 795259) B795259
theorem B2961107 : Blo 519798 2961107 := bstep (se 1 (by rfl) ⟨2220830, by rfl⟩ : syracuseStep 2961107 = 4441661) B4441661
theorem B2830355 : Blo 519798 2830355 := bstep (se 1 (by rfl) ⟨2122766, by rfl⟩ : syracuseStep 2830355 = 4245533) B4245533
theorem B1323337 : Blo 519798 1323337 := bstep (se 2 (by rfl) ⟨496251, by rfl⟩ : syracuseStep 1323337 = 992503) B992503
theorem B1323641 : Blo 519798 1323641 := bstep (se 2 (by rfl) ⟨496365, by rfl⟩ : syracuseStep 1323641 = 992731) B992731
theorem B1585847 : Blo 519798 1585847 := bstep (se 1 (by rfl) ⟨1189385, by rfl⟩ : syracuseStep 1585847 = 2378771) B2378771
theorem B2634443 : Blo 519798 2634443 := bstep (se 1 (by rfl) ⟨1975832, by rfl⟩ : syracuseStep 2634443 = 3951665) B3951665
theorem B2634605 : Blo 519798 2634605 := bstep (se 3 (by rfl) ⟨493988, by rfl⟩ : syracuseStep 2634605 = 987977) B987977
theorem B2864065 : Blo 519798 2864065 := bstep (se 2 (by rfl) ⟨1074024, by rfl⟩ : syracuseStep 2864065 = 2148049) B2148049
theorem B5944265 : Blo 519798 5944265 := bstep (se 2 (by rfl) ⟨2229099, by rfl⟩ : syracuseStep 5944265 = 4458199) B4458199
theorem B1488071 : Blo 519798 1488071 := bstep (se 1 (by rfl) ⟨1116053, by rfl⟩ : syracuseStep 1488071 = 2232107) B2232107
theorem B832799 : Blo 519798 832799 := bstep (se 1 (by rfl) ⟨624599, by rfl⟩ : syracuseStep 832799 = 1249199) B1249199
theorem B1160585 : Blo 519798 1160585 := bstep (se 2 (by rfl) ⟨435219, by rfl⟩ : syracuseStep 1160585 = 870439) B870439
theorem B833017 : Blo 519798 833017 := bstep (se 2 (by rfl) ⟨312381, by rfl⟩ : syracuseStep 833017 = 624763) B624763
theorem B9058007 : Blo 519798 9058007 := bstep (se 1 (by rfl) ⟨6793505, by rfl⟩ : syracuseStep 9058007 = 13587011) B13587011
theorem B8927333 : Blo 519798 8927333 := bstep (se 4 (by rfl) ⟨836937, by rfl⟩ : syracuseStep 8927333 = 1673875) B1673875
theorem B20363399 : Blo 519798 20363399 := bstep (se 1 (by rfl) ⟨15272549, by rfl⟩ : syracuseStep 20363399 = 30545099) B30545099
theorem B702751 : Blo 519798 702751 := bstep (se 1 (by rfl) ⟨527063, by rfl⟩ : syracuseStep 702751 = 1054127) B1054127
theorem B1325423 : Blo 519798 1325423 := bstep (se 1 (by rfl) ⟨994067, by rfl⟩ : syracuseStep 1325423 = 1988135) B1988135
theorem B1784231 : Blo 519798 1784231 := bstep (se 1 (by rfl) ⟨1338173, by rfl⟩ : syracuseStep 1784231 = 2676347) B2676347
theorem B4471321 : Blo 519798 4471321 := bstep (se 2 (by rfl) ⟨1676745, by rfl⟩ : syracuseStep 4471321 = 3353491) B3353491
theorem B834119 : Blo 519798 834119 := bstep (se 1 (by rfl) ⟨625589, by rfl⟩ : syracuseStep 834119 = 1251179) B1251179
theorem B24394391 : Blo 519798 24394391 := bstep (se 1 (by rfl) ⟨18295793, by rfl⟩ : syracuseStep 24394391 = 36591587) B36591587
theorem B5651927 : Blo 519798 5651927 := bstep (se 1 (by rfl) ⟨4238945, by rfl⟩ : syracuseStep 5651927 = 8477891) B8477891
theorem B4472279 : Blo 519798 4472279 := bstep (se 1 (by rfl) ⟨3354209, by rfl⟩ : syracuseStep 4472279 = 6708419) B6708419
theorem B2637521 : Blo 519798 2637521 := bstep (se 2 (by rfl) ⟨989070, by rfl⟩ : syracuseStep 2637521 = 1978141) B1978141
theorem B835375 : Blo 519798 835375 := bstep (se 1 (by rfl) ⟨626531, by rfl⟩ : syracuseStep 835375 = 1253063) B1253063
theorem B5030545 : Blo 519798 5030545 := bstep (se 2 (by rfl) ⟨1886454, by rfl⟩ : syracuseStep 5030545 = 3772909) B3772909
theorem B10175291 : Blo 519798 10175291 := bstep (se 1 (by rfl) ⟨7631468, by rfl⟩ : syracuseStep 10175291 = 15262937) B15262937
theorem B4440977 : Blo 519798 4440977 := bstep (se 2 (by rfl) ⟨1665366, by rfl⟩ : syracuseStep 4440977 = 3330733) B3330733
theorem B1885331 : Blo 519798 1885331 := bstep (se 1 (by rfl) ⟨1413998, by rfl⟩ : syracuseStep 1885331 = 2827997) B2827997
theorem B4474055 : Blo 519798 4474055 := bstep (se 1 (by rfl) ⟨3355541, by rfl⟩ : syracuseStep 4474055 = 6711083) B6711083
theorem B78169315 : Blo 519798 78169315 := bstep (se 1 (by rfl) ⟨58626986, by rfl⟩ : syracuseStep 78169315 = 117253973) B117253973
theorem B43500887 : Blo 519798 43500887 := bstep (se 1 (by rfl) ⟨32625665, by rfl⟩ : syracuseStep 43500887 = 65251331) B65251331
theorem B7161331 : Blo 519798 7161331 := bstep (se 1 (by rfl) ⟨5370998, by rfl⟩ : syracuseStep 7161331 = 10741997) B10741997
theorem B21481325 : Blo 519798 21481325 := bstep (se 3 (by rfl) ⟨4027748, by rfl⟩ : syracuseStep 21481325 = 8055497) B8055497
theorem B4442039 : Blo 519798 4442039 := bstep (se 1 (by rfl) ⟨3331529, by rfl⟩ : syracuseStep 4442039 = 6663059) B6663059
theorem B7161871 : Blo 519798 7161871 := bstep (se 1 (by rfl) ⟨5371403, by rfl⟩ : syracuseStep 7161871 = 10742807) B10742807
theorem B2639951 : Blo 519798 2639951 := bstep (se 1 (by rfl) ⟨1979963, by rfl⟩ : syracuseStep 2639951 = 3959927) B3959927
theorem B1755755 : Blo 519798 1755755 := bstep (se 1 (by rfl) ⟨1316816, by rfl⟩ : syracuseStep 1755755 = 2633633) B2633633
theorem B1985219 : Blo 519798 1985219 := bstep (se 1 (by rfl) ⟨1488914, by rfl⟩ : syracuseStep 1985219 = 2977829) B2977829
theorem B8014625 : Blo 519798 8014625 := bstep (se 2 (by rfl) ⟨3005484, by rfl⟩ : syracuseStep 8014625 = 6010969) B6010969
theorem B3820621 : Blo 519798 3820621 := bstep (se 3 (by rfl) ⟨716366, by rfl⟩ : syracuseStep 3820621 = 1432733) B1432733
theorem B8801459 : Blo 519798 8801459 := bstep (se 1 (by rfl) ⟨6601094, by rfl⟩ : syracuseStep 8801459 = 13202189) B13202189
theorem B1756349 : Blo 519798 1756349 := bstep (se 3 (by rfl) ⟨329315, by rfl⟩ : syracuseStep 1756349 = 658631) B658631
theorem B2641085 : Blo 519798 2641085 := bstep (se 3 (by rfl) ⟨495203, by rfl⟩ : syracuseStep 2641085 = 990407) B990407
theorem B2379593 : Blo 519798 2379593 := bstep (se 2 (by rfl) ⟨892347, by rfl⟩ : syracuseStep 2379593 = 1784695) B1784695
theorem B1986889 : Blo 519798 1986889 := bstep (se 2 (by rfl) ⟨745083, by rfl⟩ : syracuseStep 1986889 = 1490167) B1490167
theorem B3625523 : Blo 519798 3625523 := bstep (se 1 (by rfl) ⟨2719142, by rfl⟩ : syracuseStep 3625523 = 5438285) B5438285
theorem B1987193 : Blo 519798 1987193 := bstep (se 2 (by rfl) ⟨745197, by rfl⟩ : syracuseStep 1987193 = 1490395) B1490395
theorem B3953609 : Blo 519798 3953609 := bstep (se 2 (by rfl) ⟨1482603, by rfl⟩ : syracuseStep 3953609 = 2965207) B2965207
theorem B677243 : Blo 519798 677243 := bstep (se 1 (by rfl) ⟨507932, by rfl⟩ : syracuseStep 677243 = 1015865) B1015865
theorem B2283041 : Blo 519798 2283041 := bstep (se 2 (by rfl) ⟨856140, by rfl⟩ : syracuseStep 2283041 = 1712281) B1712281
theorem B2676509 : Blo 519798 2676509 := bstep (se 3 (by rfl) ⟨501845, by rfl⟩ : syracuseStep 2676509 = 1003691) B1003691
theorem B743375 : Blo 519798 743375 := bstep (se 1 (by rfl) ⟨557531, by rfl⟩ : syracuseStep 743375 = 1115063) B1115063
theorem B1759265 : Blo 519798 1759265 := bstep (se 2 (by rfl) ⟨659724, by rfl⟩ : syracuseStep 1759265 = 1319449) B1319449
theorem B2644001 : Blo 519798 2644001 := bstep (se 2 (by rfl) ⟨991500, by rfl⟩ : syracuseStep 2644001 = 1983001) B1983001
theorem B2644163 : Blo 519798 2644163 := bstep (se 1 (by rfl) ⟨1983122, by rfl⟩ : syracuseStep 2644163 = 3966245) B3966245
theorem B12737087 : Blo 519798 12737087 := bstep (se 1 (by rfl) ⟨9552815, by rfl⟩ : syracuseStep 12737087 = 19105631) B19105631
theorem B1169999 : Blo 519798 1169999 := bstep (se 1 (by rfl) ⟨877499, by rfl⟩ : syracuseStep 1169999 = 1754999) B1754999
theorem B1170143 : Blo 519798 1170143 := bstep (se 1 (by rfl) ⟨877607, by rfl⟩ : syracuseStep 1170143 = 1755215) B1755215
theorem B8444675 : Blo 519798 8444675 := bstep (se 1 (by rfl) ⟨6333506, by rfl⟩ : syracuseStep 8444675 = 12667013) B12667013
theorem B8575931 : Blo 519798 8575931 := bstep (se 1 (by rfl) ⟨6431948, by rfl⟩ : syracuseStep 8575931 = 12863897) B12863897
theorem B1170395 : Blo 519798 1170395 := bstep (se 1 (by rfl) ⟨877796, by rfl⟩ : syracuseStep 1170395 = 1755593) B1755593
theorem B1203175 : Blo 519798 1203175 := bstep (se 1 (by rfl) ⟨902381, by rfl⟩ : syracuseStep 1203175 = 1804763) B1804763
theorem B1170575 : Blo 519798 1170575 := bstep (se 1 (by rfl) ⟨877931, by rfl⟩ : syracuseStep 1170575 = 1755863) B1755863
theorem B1170665 : Blo 519798 1170665 := bstep (se 2 (by rfl) ⟨438999, by rfl⟩ : syracuseStep 1170665 = 877999) B877999
theorem B1170719 : Blo 519798 1170719 := bstep (se 1 (by rfl) ⟨878039, by rfl⟩ : syracuseStep 1170719 = 1756079) B1756079
theorem B1171241 : Blo 519798 1171241 := bstep (se 2 (by rfl) ⟨439215, by rfl⟩ : syracuseStep 1171241 = 878431) B878431
theorem B3957497 : Blo 519798 3957497 := bstep (se 2 (by rfl) ⟨1484061, by rfl⟩ : syracuseStep 3957497 = 2968123) B2968123
theorem B1172303 : Blo 519798 1172303 := bstep (se 1 (by rfl) ⟨879227, by rfl⟩ : syracuseStep 1172303 = 1758455) B1758455
theorem B1762127 : Blo 519798 1762127 := bstep (se 1 (by rfl) ⟨1321595, by rfl⟩ : syracuseStep 1762127 = 2643191) B2643191
theorem B9495589 : Blo 519798 9495589 := bstep (se 4 (by rfl) ⟨890211, by rfl⟩ : syracuseStep 9495589 = 1780423) B1780423
theorem B1172519 : Blo 519798 1172519 := bstep (se 1 (by rfl) ⟨879389, by rfl⟩ : syracuseStep 1172519 = 1758779) B1758779
theorem B1762451 : Blo 519798 1762451 := bstep (se 1 (by rfl) ⟨1321838, by rfl⟩ : syracuseStep 1762451 = 2643677) B2643677
theorem B1172699 : Blo 519798 1172699 := bstep (se 1 (by rfl) ⟨879524, by rfl⟩ : syracuseStep 1172699 = 1759049) B1759049
theorem B1172897 : Blo 519798 1172897 := bstep (se 2 (by rfl) ⟨439836, by rfl⟩ : syracuseStep 1172897 = 879673) B879673
theorem B1762721 : Blo 519798 1762721 := bstep (se 2 (by rfl) ⟨661020, by rfl⟩ : syracuseStep 1762721 = 1322041) B1322041
theorem B4449725 : Blo 519798 4449725 := bstep (se 3 (by rfl) ⟨834323, by rfl⟩ : syracuseStep 4449725 = 1668647) B1668647
theorem B780011 : Blo 519798 780011 := bstep (se 1 (by rfl) ⟨585008, by rfl⟩ : syracuseStep 780011 = 1170017) B1170017
theorem B878377 : Blo 519798 878377 := bstep (se 2 (by rfl) ⟨329391, by rfl⟩ : syracuseStep 878377 = 658783) B658783
theorem B2647889 : Blo 519798 2647889 := bstep (se 2 (by rfl) ⟨992958, by rfl⟩ : syracuseStep 2647889 = 1985917) B1985917
theorem B780239 : Blo 519798 780239 := bstep (se 1 (by rfl) ⟨585179, by rfl⟩ : syracuseStep 780239 = 1170359) B1170359
theorem B1173455 : Blo 519798 1173455 := bstep (se 1 (by rfl) ⟨880091, by rfl⟩ : syracuseStep 1173455 = 1760183) B1760183
theorem B2222113 : Blo 519798 2222113 := bstep (se 2 (by rfl) ⟨833292, by rfl⟩ : syracuseStep 2222113 = 1666585) B1666585
theorem B2975939 : Blo 519798 2975939 := bstep (se 1 (by rfl) ⟨2231954, by rfl⟩ : syracuseStep 2975939 = 4463909) B4463909
theorem B1173833 : Blo 519798 1173833 := bstep (se 2 (by rfl) ⟨440187, by rfl⟩ : syracuseStep 1173833 = 880375) B880375
theorem B780635 : Blo 519798 780635 := bstep (se 1 (by rfl) ⟨585476, by rfl⟩ : syracuseStep 780635 = 1170953) B1170953
theorem B1173851 : Blo 519798 1173851 := bstep (se 1 (by rfl) ⟨880388, by rfl⟩ : syracuseStep 1173851 = 1760777) B1760777
theorem B780863 : Blo 519798 780863 := bstep (se 1 (by rfl) ⟨585647, by rfl⟩ : syracuseStep 780863 = 1171295) B1171295
theorem B879167 : Blo 519798 879167 := bstep (se 1 (by rfl) ⟨659375, by rfl⟩ : syracuseStep 879167 = 1318751) B1318751
theorem B2648699 : Blo 519798 2648699 := bstep (se 1 (by rfl) ⟨1986524, by rfl⟩ : syracuseStep 2648699 = 3973049) B3973049
theorem B780983 : Blo 519798 780983 := bstep (se 1 (by rfl) ⟨585737, by rfl⟩ : syracuseStep 780983 = 1171475) B1171475
theorem B781211 : Blo 519798 781211 := bstep (se 1 (by rfl) ⟨585908, by rfl⟩ : syracuseStep 781211 = 1171817) B1171817
theorem B1174427 : Blo 519798 1174427 := bstep (se 1 (by rfl) ⟨880820, by rfl⟩ : syracuseStep 1174427 = 1761641) B1761641
theorem B1174625 : Blo 519798 1174625 := bstep (se 2 (by rfl) ⟨440484, by rfl⟩ : syracuseStep 1174625 = 880969) B880969
theorem B1666187 : Blo 519798 1666187 := bstep (se 1 (by rfl) ⟨1249640, by rfl⟩ : syracuseStep 1666187 = 2499281) B2499281
theorem B584923 : Blo 519798 584923 := bstep (se 1 (by rfl) ⟨438692, by rfl⟩ : syracuseStep 584923 = 877385) B877385
theorem B879835 : Blo 519798 879835 := bstep (se 1 (by rfl) ⟨659876, by rfl⟩ : syracuseStep 879835 = 1319753) B1319753
theorem B781607 : Blo 519798 781607 := bstep (se 1 (by rfl) ⟨586205, by rfl⟩ : syracuseStep 781607 = 1172411) B1172411
theorem B1174823 : Blo 519798 1174823 := bstep (se 1 (by rfl) ⟨881117, by rfl⟩ : syracuseStep 1174823 = 1762235) B1762235
theorem B781691 : Blo 519798 781691 := bstep (se 1 (by rfl) ⟨586268, by rfl⟩ : syracuseStep 781691 = 1172537) B1172537
theorem B781817 : Blo 519798 781817 := bstep (se 2 (by rfl) ⟨293181, by rfl⟩ : syracuseStep 781817 = 586363) B586363
theorem B585211 : Blo 519798 585211 := bstep (se 1 (by rfl) ⟨438908, by rfl⟩ : syracuseStep 585211 = 877817) B877817
theorem B781919 : Blo 519798 781919 := bstep (se 1 (by rfl) ⟨586439, by rfl⟩ : syracuseStep 781919 = 1172879) B1172879
theorem B1175201 : Blo 519798 1175201 := bstep (se 2 (by rfl) ⟨440700, by rfl⟩ : syracuseStep 1175201 = 881401) B881401
theorem B585391 : Blo 519798 585391 := bstep (se 1 (by rfl) ⟨439043, by rfl⟩ : syracuseStep 585391 = 878087) B878087
theorem B519903 : Blo 519798 519903 := bstep (se 1 (by rfl) ⟨389927, by rfl⟩ : syracuseStep 519903 = 779855) B779855
theorem B519983 : Blo 519798 519983 := bstep (se 1 (by rfl) ⟨389987, by rfl⟩ : syracuseStep 519983 = 779975) B779975
theorem B782135 : Blo 519798 782135 := bstep (se 1 (by rfl) ⟨586601, by rfl⟩ : syracuseStep 782135 = 1173203) B1173203
theorem B520091 : Blo 519798 520091 := bstep (se 1 (by rfl) ⟨390068, by rfl⟩ : syracuseStep 520091 = 780137) B780137
theorem B520143 : Blo 519798 520143 := bstep (se 1 (by rfl) ⟨390107, by rfl⟩ : syracuseStep 520143 = 780215) B780215
theorem B585679 : Blo 519798 585679 := bstep (se 1 (by rfl) ⟨439259, by rfl⟩ : syracuseStep 585679 = 878519) B878519
theorem B880591 : Blo 519798 880591 := bstep (se 1 (by rfl) ⟨660443, by rfl⟩ : syracuseStep 880591 = 1320887) B1320887
theorem B520167 : Blo 519798 520167 := bstep (se 1 (by rfl) ⟨390125, by rfl⟩ : syracuseStep 520167 = 780251) B780251
theorem B1175561 : Blo 519798 1175561 := bstep (se 2 (by rfl) ⟨440835, by rfl⟩ : syracuseStep 1175561 = 881671) B881671
theorem B3960899 : Blo 519798 3960899 := bstep (se 1 (by rfl) ⟨2970674, by rfl⟩ : syracuseStep 3960899 = 5941349) B5941349
theorem B782441 : Blo 519798 782441 := bstep (se 2 (by rfl) ⟨293415, by rfl⟩ : syracuseStep 782441 = 586831) B586831
theorem B520479 : Blo 519798 520479 := bstep (se 1 (by rfl) ⟨390359, by rfl⟩ : syracuseStep 520479 = 780719) B780719
theorem B520539 : Blo 519798 520539 := bstep (se 1 (by rfl) ⟨390404, by rfl⟩ : syracuseStep 520539 = 780809) B780809
theorem B586075 : Blo 519798 586075 := bstep (se 1 (by rfl) ⟨439556, by rfl⟩ : syracuseStep 586075 = 879113) B879113
theorem B520559 : Blo 519798 520559 := bstep (se 1 (by rfl) ⟨390419, by rfl⟩ : syracuseStep 520559 = 780839) B780839
theorem B520615 : Blo 519798 520615 := bstep (se 1 (by rfl) ⟨390461, by rfl⟩ : syracuseStep 520615 = 780923) B780923
theorem B782759 : Blo 519798 782759 := bstep (se 1 (by rfl) ⟨587069, by rfl⟩ : syracuseStep 782759 = 1174139) B1174139
theorem B1175975 : Blo 519798 1175975 := bstep (se 1 (by rfl) ⟨881981, by rfl⟩ : syracuseStep 1175975 = 1763963) B1763963
theorem B586183 : Blo 519798 586183 := bstep (se 1 (by rfl) ⟨439637, by rfl⟩ : syracuseStep 586183 = 879275) B879275
theorem B520699 : Blo 519798 520699 := bstep (se 1 (by rfl) ⟨390524, by rfl⟩ : syracuseStep 520699 = 781049) B781049
theorem B782843 : Blo 519798 782843 := bstep (se 1 (by rfl) ⟨587132, by rfl⟩ : syracuseStep 782843 = 1174265) B1174265
theorem B1176083 : Blo 519798 1176083 := bstep (se 1 (by rfl) ⟨882062, by rfl⟩ : syracuseStep 1176083 = 1764125) B1764125
theorem B1765907 : Blo 519798 1765907 := bstep (se 1 (by rfl) ⟨1324430, by rfl⟩ : syracuseStep 1765907 = 2648861) B2648861
theorem B2650643 : Blo 519798 2650643 := bstep (se 1 (by rfl) ⟨1987982, by rfl⟩ : syracuseStep 2650643 = 3975965) B3975965
theorem B520767 : Blo 519798 520767 := bstep (se 1 (by rfl) ⟨390575, by rfl⟩ : syracuseStep 520767 = 781151) B781151
theorem B520775 : Blo 519798 520775 := bstep (se 1 (by rfl) ⟨390581, by rfl⟩ : syracuseStep 520775 = 781163) B781163
theorem B1176137 : Blo 519798 1176137 := bstep (se 2 (by rfl) ⟨441051, by rfl⟩ : syracuseStep 1176137 = 882103) B882103
theorem B782969 : Blo 519798 782969 := bstep (se 2 (by rfl) ⟨293613, by rfl⟩ : syracuseStep 782969 = 587227) B587227
theorem B881273 : Blo 519798 881273 := bstep (se 2 (by rfl) ⟨330477, by rfl⟩ : syracuseStep 881273 = 660955) B660955
theorem B783023 : Blo 519798 783023 := bstep (se 1 (by rfl) ⟨587267, by rfl⟩ : syracuseStep 783023 = 1174535) B1174535
theorem B881327 : Blo 519798 881327 := bstep (se 1 (by rfl) ⟨660995, by rfl⟩ : syracuseStep 881327 = 1321991) B1321991
theorem B520927 : Blo 519798 520927 := bstep (se 1 (by rfl) ⟨390695, by rfl⟩ : syracuseStep 520927 = 781391) B781391
theorem B783071 : Blo 519798 783071 := bstep (se 1 (by rfl) ⟨587303, by rfl⟩ : syracuseStep 783071 = 1174607) B1174607
theorem B14480117 : Blo 519798 14480117 := bstep (se 5 (by rfl) ⟨678755, by rfl⟩ : syracuseStep 14480117 = 1357511) B1357511
theorem B2978603 : Blo 519798 2978603 := bstep (se 1 (by rfl) ⟨2233952, by rfl⟩ : syracuseStep 2978603 = 4467905) B4467905
theorem B521007 : Blo 519798 521007 := bstep (se 1 (by rfl) ⟨390755, by rfl⟩ : syracuseStep 521007 = 781511) B781511
theorem B586543 : Blo 519798 586543 := bstep (se 1 (by rfl) ⟨439907, by rfl⟩ : syracuseStep 586543 = 879815) B879815
theorem B521115 : Blo 519798 521115 := bstep (se 1 (by rfl) ⟨390836, by rfl⟩ : syracuseStep 521115 = 781673) B781673
theorem B586651 : Blo 519798 586651 := bstep (se 1 (by rfl) ⟨439988, by rfl⟩ : syracuseStep 586651 = 879977) B879977
theorem B881563 : Blo 519798 881563 := bstep (se 1 (by rfl) ⟨661172, by rfl⟩ : syracuseStep 881563 = 1322345) B1322345
theorem B521167 : Blo 519798 521167 := bstep (se 1 (by rfl) ⟨390875, by rfl⟩ : syracuseStep 521167 = 781751) B781751
theorem B1668059 : Blo 519798 1668059 := bstep (se 1 (by rfl) ⟨1251044, by rfl⟩ : syracuseStep 1668059 = 2502089) B2502089
theorem B521191 : Blo 519798 521191 := bstep (se 1 (by rfl) ⟨390893, by rfl⟩ : syracuseStep 521191 = 781787) B781787
theorem B783335 : Blo 519798 783335 := bstep (se 1 (by rfl) ⟨587501, by rfl⟩ : syracuseStep 783335 = 1175003) B1175003
theorem B1176551 : Blo 519798 1176551 := bstep (se 1 (by rfl) ⟨882413, by rfl⟩ : syracuseStep 1176551 = 1764827) B1764827
theorem B783593 : Blo 519798 783593 := bstep (se 2 (by rfl) ⟨293847, by rfl⟩ : syracuseStep 783593 = 587695) B587695
theorem B521503 : Blo 519798 521503 := bstep (se 1 (by rfl) ⟨391127, by rfl⟩ : syracuseStep 521503 = 782255) B782255
theorem B783647 : Blo 519798 783647 := bstep (se 1 (by rfl) ⟨587735, by rfl⟩ : syracuseStep 783647 = 1175471) B1175471
theorem B587047 : Blo 519798 587047 := bstep (se 1 (by rfl) ⟨440285, by rfl⟩ : syracuseStep 587047 = 880571) B880571
theorem B521563 : Blo 519798 521563 := bstep (se 1 (by rfl) ⟨391172, by rfl⟩ : syracuseStep 521563 = 782345) B782345
theorem B1176929 : Blo 519798 1176929 := bstep (se 2 (by rfl) ⟨441348, by rfl⟩ : syracuseStep 1176929 = 882697) B882697
theorem B521583 : Blo 519798 521583 := bstep (se 1 (by rfl) ⟨391187, by rfl⟩ : syracuseStep 521583 = 782375) B782375
theorem B587119 : Blo 519798 587119 := bstep (se 1 (by rfl) ⟨440339, by rfl⟩ : syracuseStep 587119 = 880679) B880679
theorem B521639 : Blo 519798 521639 := bstep (se 1 (by rfl) ⟨391229, by rfl⟩ : syracuseStep 521639 = 782459) B782459
theorem B1177019 : Blo 519798 1177019 := bstep (se 1 (by rfl) ⟨882764, by rfl⟩ : syracuseStep 1177019 = 1765529) B1765529
theorem B4453825 : Blo 519798 4453825 := bstep (se 2 (by rfl) ⟨1670184, by rfl⟩ : syracuseStep 4453825 = 3340369) B3340369
theorem B783815 : Blo 519798 783815 := bstep (se 1 (by rfl) ⟨587861, by rfl⟩ : syracuseStep 783815 = 1175723) B1175723
theorem B521723 : Blo 519798 521723 := bstep (se 1 (by rfl) ⟨391292, by rfl⟩ : syracuseStep 521723 = 782585) B782585
theorem B1177145 : Blo 519798 1177145 := bstep (se 2 (by rfl) ⟨441429, by rfl⟩ : syracuseStep 1177145 = 882859) B882859
theorem B521791 : Blo 519798 521791 := bstep (se 1 (by rfl) ⟨391343, by rfl⟩ : syracuseStep 521791 = 782687) B782687
theorem B521799 : Blo 519798 521799 := bstep (se 1 (by rfl) ⟨391349, by rfl⟩ : syracuseStep 521799 = 782699) B782699
theorem B587335 : Blo 519798 587335 := bstep (se 1 (by rfl) ⟨440501, by rfl⟩ : syracuseStep 587335 = 881003) B881003
theorem B521951 : Blo 519798 521951 := bstep (se 1 (by rfl) ⟨391463, by rfl⟩ : syracuseStep 521951 = 782927) B782927
theorem B784169 : Blo 519798 784169 := bstep (se 2 (by rfl) ⟨294063, by rfl⟩ : syracuseStep 784169 = 588127) B588127
theorem B522031 : Blo 519798 522031 := bstep (se 1 (by rfl) ⟨391523, by rfl⟩ : syracuseStep 522031 = 783047) B783047
theorem B784175 : Blo 519798 784175 := bstep (se 1 (by rfl) ⟨588131, by rfl⟩ : syracuseStep 784175 = 1176263) B1176263
theorem B522139 : Blo 519798 522139 := bstep (se 1 (by rfl) ⟨391604, by rfl⟩ : syracuseStep 522139 = 783209) B783209
theorem B522191 : Blo 519798 522191 := bstep (se 1 (by rfl) ⟨391643, by rfl⟩ : syracuseStep 522191 = 783287) B783287
theorem B522215 : Blo 519798 522215 := bstep (se 1 (by rfl) ⟨391661, by rfl⟩ : syracuseStep 522215 = 783323) B783323
theorem B1177811 : Blo 519798 1177811 := bstep (se 1 (by rfl) ⟨883358, by rfl⟩ : syracuseStep 1177811 = 1766717) B1766717
theorem B1112329 : Blo 519798 1112329 := bstep (se 2 (by rfl) ⟨417123, by rfl⟩ : syracuseStep 1112329 = 834247) B834247
theorem B784649 : Blo 519798 784649 := bstep (se 2 (by rfl) ⟨294243, by rfl⟩ : syracuseStep 784649 = 588487) B588487
theorem B1177865 : Blo 519798 1177865 := bstep (se 2 (by rfl) ⟨441699, by rfl⟩ : syracuseStep 1177865 = 883399) B883399
theorem B1767689 : Blo 519798 1767689 := bstep (se 2 (by rfl) ⟨662883, by rfl⟩ : syracuseStep 1767689 = 1325767) B1325767
theorem B522527 : Blo 519798 522527 := bstep (se 1 (by rfl) ⟨391895, by rfl⟩ : syracuseStep 522527 = 783791) B783791
theorem B522587 : Blo 519798 522587 := bstep (se 1 (by rfl) ⟨391940, by rfl⟩ : syracuseStep 522587 = 783881) B783881
theorem B121534825 : Blo 519798 121534825 := bstep (se 2 (by rfl) ⟨45575559, by rfl⟩ : syracuseStep 121534825 = 91151119) B91151119
theorem B522607 : Blo 519798 522607 := bstep (se 1 (by rfl) ⟨391955, by rfl⟩ : syracuseStep 522607 = 783911) B783911
theorem B784751 : Blo 519798 784751 := bstep (se 1 (by rfl) ⟨588563, by rfl⟩ : syracuseStep 784751 = 1177127) B1177127
theorem B883055 : Blo 519798 883055 := bstep (se 1 (by rfl) ⟨662291, by rfl⟩ : syracuseStep 883055 = 1324583) B1324583
theorem B522663 : Blo 519798 522663 := bstep (se 1 (by rfl) ⟨391997, by rfl⟩ : syracuseStep 522663 = 783995) B783995
theorem B588199 : Blo 519798 588199 := bstep (se 1 (by rfl) ⟨441149, by rfl⟩ : syracuseStep 588199 = 882299) B882299
theorem B1178081 : Blo 519798 1178081 := bstep (se 2 (by rfl) ⟨441780, by rfl⟩ : syracuseStep 1178081 = 883561) B883561
theorem B522747 : Blo 519798 522747 := bstep (se 1 (by rfl) ⟨392060, by rfl⟩ : syracuseStep 522747 = 784121) B784121
theorem B522815 : Blo 519798 522815 := bstep (se 1 (by rfl) ⟨392111, by rfl⟩ : syracuseStep 522815 = 784223) B784223
theorem B522823 : Blo 519798 522823 := bstep (se 1 (by rfl) ⟨392117, by rfl⟩ : syracuseStep 522823 = 784235) B784235
theorem B784967 : Blo 519798 784967 := bstep (se 1 (by rfl) ⟨588725, by rfl⟩ : syracuseStep 784967 = 1177451) B1177451
theorem B2226761 : Blo 519798 2226761 := bstep (se 2 (by rfl) ⟨835035, by rfl⟩ : syracuseStep 2226761 = 1670071) B1670071
theorem B883271 : Blo 519798 883271 := bstep (se 1 (by rfl) ⟨662453, by rfl⟩ : syracuseStep 883271 = 1324907) B1324907
theorem B785003 : Blo 519798 785003 := bstep (se 1 (by rfl) ⟨588752, by rfl⟩ : syracuseStep 785003 = 1177505) B1177505
theorem B2226811 : Blo 519798 2226811 := bstep (se 1 (by rfl) ⟨1670108, by rfl⟩ : syracuseStep 2226811 = 3340217) B3340217
theorem B522975 : Blo 519798 522975 := bstep (se 1 (by rfl) ⟨392231, by rfl⟩ : syracuseStep 522975 = 784463) B784463
theorem B1178387 : Blo 519798 1178387 := bstep (se 1 (by rfl) ⟨883790, by rfl⟩ : syracuseStep 1178387 = 1767581) B1767581
theorem B555823 : Blo 519798 555823 := bstep (se 1 (by rfl) ⟨416867, by rfl⟩ : syracuseStep 555823 = 833735) B833735
theorem B523055 : Blo 519798 523055 := bstep (se 1 (by rfl) ⟨392291, by rfl⟩ : syracuseStep 523055 = 784583) B784583
theorem B785231 : Blo 519798 785231 := bstep (se 1 (by rfl) ⟨588923, by rfl⟩ : syracuseStep 785231 = 1177847) B1177847
theorem B523163 : Blo 519798 523163 := bstep (se 1 (by rfl) ⟨392372, by rfl⟩ : syracuseStep 523163 = 784745) B784745
theorem B523215 : Blo 519798 523215 := bstep (se 1 (by rfl) ⟨392411, by rfl⟩ : syracuseStep 523215 = 784823) B784823
theorem B523239 : Blo 519798 523239 := bstep (se 1 (by rfl) ⟨392429, by rfl⟩ : syracuseStep 523239 = 784859) B784859
theorem B588775 : Blo 519798 588775 := bstep (se 1 (by rfl) ⟨441581, by rfl⟩ : syracuseStep 588775 = 883163) B883163
theorem B883703 : Blo 519798 883703 := bstep (se 1 (by rfl) ⟨662777, by rfl⟩ : syracuseStep 883703 = 1325555) B1325555
theorem B8944829 : Blo 519798 8944829 := bstep (se 3 (by rfl) ⟨1677155, by rfl⟩ : syracuseStep 8944829 = 3354311) B3354311
theorem B785627 : Blo 519798 785627 := bstep (se 1 (by rfl) ⟨589220, by rfl⟩ : syracuseStep 785627 = 1178441) B1178441
theorem B523551 : Blo 519798 523551 := bstep (se 1 (by rfl) ⟨392663, by rfl⟩ : syracuseStep 523551 = 785327) B785327
theorem B523611 : Blo 519798 523611 := bstep (se 1 (by rfl) ⟨392708, by rfl⟩ : syracuseStep 523611 = 785417) B785417
theorem B523631 : Blo 519798 523631 := bstep (se 1 (by rfl) ⟨392723, by rfl⟩ : syracuseStep 523631 = 785447) B785447
theorem B1670519 : Blo 519798 1670519 := bstep (se 1 (by rfl) ⟨1252889, by rfl⟩ : syracuseStep 1670519 = 2505779) B2505779
theorem B523687 : Blo 519798 523687 := bstep (se 1 (by rfl) ⟨392765, by rfl⟩ : syracuseStep 523687 = 785531) B785531
theorem B1113593 : Blo 519798 1113593 := bstep (se 2 (by rfl) ⟨417597, by rfl⟩ : syracuseStep 1113593 = 835195) B835195
theorem B523771 : Blo 519798 523771 := bstep (se 1 (by rfl) ⟨392828, by rfl⟩ : syracuseStep 523771 = 785657) B785657
theorem B2817899 : Blo 519798 2817899 := bstep (se 1 (by rfl) ⟨2113424, by rfl⟩ : syracuseStep 2817899 = 4226849) B4226849
theorem B2228143 : Blo 519798 2228143 := bstep (se 1 (by rfl) ⟨1671107, by rfl⟩ : syracuseStep 2228143 = 3342215) B3342215
theorem B6423079 : Blo 519798 6423079 := bstep (se 1 (by rfl) ⟨4817309, by rfl⟩ : syracuseStep 6423079 = 9634619) B9634619
theorem B6783527 : Blo 519798 6783527 := bstep (se 1 (by rfl) ⟨5087645, by rfl⟩ : syracuseStep 6783527 = 10175291) B10175291
theorem B2982521 : Blo 519798 2982521 := bstep (se 2 (by rfl) ⟨1118445, by rfl⟩ : syracuseStep 2982521 = 2236891) B2236891
theorem B2982703 : Blo 519798 2982703 := bstep (se 1 (by rfl) ⟨2237027, by rfl⟩ : syracuseStep 2982703 = 4474055) B4474055
theorem B29000591 : Blo 519798 29000591 := bstep (se 1 (by rfl) ⟨21750443, by rfl⟩ : syracuseStep 29000591 = 43500887) B43500887
theorem B5080009 : Blo 519798 5080009 := bstep (se 2 (by rfl) ⟨1905003, by rfl⟩ : syracuseStep 5080009 = 3810007) B3810007
theorem B14320883 : Blo 519798 14320883 := bstep (se 1 (by rfl) ⟨10740662, by rfl⟩ : syracuseStep 14320883 = 21481325) B21481325
theorem B6096343 : Blo 519798 6096343 := bstep (se 1 (by rfl) ⟨4572257, by rfl⟩ : syracuseStep 6096343 = 9144515) B9144515
theorem B1115815 : Blo 519798 1115815 := bstep (se 1 (by rfl) ⟨836861, by rfl⟩ : syracuseStep 1115815 = 1673723) B1673723
theorem B5343083 : Blo 519798 5343083 := bstep (se 1 (by rfl) ⟨4007312, by rfl⟩ : syracuseStep 5343083 = 8014625) B8014625
theorem B5867639 : Blo 519798 5867639 := bstep (se 1 (by rfl) ⟨4400729, by rfl⟩ : syracuseStep 5867639 = 8801459) B8801459
theorem B1673465 : Blo 519798 1673465 := bstep (se 2 (by rfl) ⟨627549, by rfl⟩ : syracuseStep 1673465 = 1255099) B1255099
theorem B1116703 : Blo 519798 1116703 := bstep (se 1 (by rfl) ⟨837527, by rfl⟩ : syracuseStep 1116703 = 1675055) B1675055
theorem B7539479 : Blo 519798 7539479 := bstep (se 1 (by rfl) ⟨5654609, by rfl⟩ : syracuseStep 7539479 = 11309219) B11309219
theorem B2231135 : Blo 519798 2231135 := bstep (se 1 (by rfl) ⟨1673351, by rfl⟩ : syracuseStep 2231135 = 3346703) B3346703
theorem B1510363 : Blo 519798 1510363 := bstep (se 1 (by rfl) ⟨1132772, by rfl⟩ : syracuseStep 1510363 = 2265545) B2265545
theorem B3968189 : Blo 519798 3968189 := bstep (se 3 (by rfl) ⟨744035, by rfl⟩ : syracuseStep 3968189 = 1488071) B1488071
theorem B9014777 : Blo 519798 9014777 := bstep (se 2 (by rfl) ⟨3380541, by rfl⟩ : syracuseStep 9014777 = 6761083) B6761083
theorem B1805981 : Blo 519798 1805981 := bstep (se 3 (by rfl) ⟨338621, by rfl⟩ : syracuseStep 1805981 = 677243) B677243
theorem B986899 : Blo 519798 986899 := bstep (se 1 (by rfl) ⟨740174, by rfl⟩ : syracuseStep 986899 = 1480349) B1480349
theorem B8491391 : Blo 519798 8491391 := bstep (se 1 (by rfl) ⟨6368543, by rfl⟩ : syracuseStep 8491391 = 12737087) B12737087
theorem B2232791 : Blo 519798 2232791 := bstep (se 1 (by rfl) ⟨1674593, by rfl⟩ : syracuseStep 2232791 = 3349187) B3349187
theorem B24154685 : Blo 519798 24154685 := bstep (se 3 (by rfl) ⟨4529003, by rfl⟩ : syracuseStep 24154685 = 9058007) B9058007
theorem B1413793 : Blo 519798 1413793 := bstep (se 2 (by rfl) ⟨530172, by rfl⟩ : syracuseStep 1413793 = 1060345) B1060345
theorem B1315835 : Blo 519798 1315835 := bstep (se 1 (by rfl) ⟨986876, by rfl⟩ : syracuseStep 1315835 = 1973753) B1973753
theorem B1316321 : Blo 519798 1316321 := bstep (se 2 (by rfl) ⟨493620, by rfl⟩ : syracuseStep 1316321 = 987241) B987241
theorem B8918585 : Blo 519798 8918585 := bstep (se 2 (by rfl) ⟨3344469, by rfl⟩ : syracuseStep 8918585 = 6688939) B6688939
theorem B661279 : Blo 519798 661279 := bstep (se 1 (by rfl) ⟨495959, by rfl⟩ : syracuseStep 661279 = 991919) B991919
theorem B1185673 : Blo 519798 1185673 := bstep (se 2 (by rfl) ⟨444627, by rfl⟩ : syracuseStep 1185673 = 889255) B889255
theorem B1316857 : Blo 519798 1316857 := bstep (se 2 (by rfl) ⟨493821, by rfl⟩ : syracuseStep 1316857 = 987643) B987643
theorem B1317019 : Blo 519798 1317019 := bstep (se 1 (by rfl) ⟨987764, by rfl⟩ : syracuseStep 1317019 = 1975529) B1975529
theorem B2234567 : Blo 519798 2234567 := bstep (se 1 (by rfl) ⟨1675925, by rfl⟩ : syracuseStep 2234567 = 3351851) B3351851
theorem B1186055 : Blo 519798 1186055 := bstep (se 1 (by rfl) ⟨889541, by rfl⟩ : syracuseStep 1186055 = 1779083) B1779083
theorem B1317161 : Blo 519798 1317161 := bstep (se 2 (by rfl) ⟨493935, by rfl⟩ : syracuseStep 1317161 = 987871) B987871
theorem B1055099 : Blo 519798 1055099 := bstep (se 1 (by rfl) ⟨791324, by rfl⟩ : syracuseStep 1055099 = 1582649) B1582649
theorem B1252255 : Blo 519798 1252255 := bstep (se 1 (by rfl) ⟨939191, by rfl⟩ : syracuseStep 1252255 = 1878383) B1878383
theorem B4463531 : Blo 519798 4463531 := bstep (se 1 (by rfl) ⟨3347648, by rfl⟩ : syracuseStep 4463531 = 6695297) B6695297
theorem B662575 : Blo 519798 662575 := bstep (se 1 (by rfl) ⟨496931, by rfl⟩ : syracuseStep 662575 = 993863) B993863
theorem B5938433 : Blo 519798 5938433 := bstep (se 2 (by rfl) ⟨2226912, by rfl⟩ : syracuseStep 5938433 = 4453825) B4453825
theorem B1318153 : Blo 519798 1318153 := bstep (se 2 (by rfl) ⟨494307, by rfl⟩ : syracuseStep 1318153 = 988615) B988615
theorem B9510479 : Blo 519798 9510479 := bstep (se 1 (by rfl) ⟨7132859, by rfl⟩ : syracuseStep 9510479 = 14265719) B14265719
theorem B990863 : Blo 519798 990863 := bstep (se 1 (by rfl) ⟨743147, by rfl⟩ : syracuseStep 990863 = 1486295) B1486295
theorem B1974071 : Blo 519798 1974071 := bstep (se 1 (by rfl) ⟨1480553, by rfl⟩ : syracuseStep 1974071 = 2961107) B2961107
theorem B1483105 : Blo 519798 1483105 := bstep (se 2 (by rfl) ⟨556164, by rfl⟩ : syracuseStep 1483105 = 1112329) B1112329
theorem B1057231 : Blo 519798 1057231 := bstep (se 1 (by rfl) ⟨792923, by rfl⟩ : syracuseStep 1057231 = 1585847) B1585847
theorem B162046433 : Blo 519798 162046433 := bstep (se 2 (by rfl) ⟨60767412, by rfl⟩ : syracuseStep 162046433 = 121534825) B121534825
theorem B13575599 : Blo 519798 13575599 := bstep (se 1 (by rfl) ⟨10181699, by rfl⟩ : syracuseStep 13575599 = 20363399) B20363399
theorem B1189487 : Blo 519798 1189487 := bstep (se 1 (by rfl) ⟨892115, by rfl⟩ : syracuseStep 1189487 = 1784231) B1784231
theorem B1484507 : Blo 519798 1484507 := bstep (se 1 (by rfl) ⟨1113380, by rfl⟩ : syracuseStep 1484507 = 2226761) B2226761
theorem B16262927 : Blo 519798 16262927 := bstep (se 1 (by rfl) ⟨12197195, by rfl⟩ : syracuseStep 16262927 = 24394391) B24394391
theorem B1878599 : Blo 519798 1878599 := bstep (se 1 (by rfl) ⟨1408949, by rfl⟩ : syracuseStep 1878599 = 2817899) B2817899
theorem B6335603 : Blo 519798 6335603 := bstep (se 1 (by rfl) ⟨4751702, by rfl⟩ : syracuseStep 6335603 = 9503405) B9503405
theorem B2960651 : Blo 519798 2960651 := bstep (se 1 (by rfl) ⟨2220488, by rfl⟩ : syracuseStep 2960651 = 4440977) B4440977
theorem B1256887 : Blo 519798 1256887 := bstep (se 1 (by rfl) ⟨942665, by rfl⟩ : syracuseStep 1256887 = 1885331) B1885331
theorem B5942807 : Blo 519798 5942807 := bstep (se 1 (by rfl) ⟨4457105, by rfl⟩ : syracuseStep 5942807 = 8914211) B8914211
theorem B1977929 : Blo 519798 1977929 := bstep (se 2 (by rfl) ⟨741723, by rfl⟩ : syracuseStep 1977929 = 1483447) B1483447
theorem B2961359 : Blo 519798 2961359 := bstep (se 1 (by rfl) ⟨2221019, by rfl⟩ : syracuseStep 2961359 = 4442039) B4442039
theorem B12660785 : Blo 519798 12660785 := bstep (se 2 (by rfl) ⟨4747794, by rfl⟩ : syracuseStep 12660785 = 9495589) B9495589
theorem B1323479 : Blo 519798 1323479 := bstep (se 1 (by rfl) ⟨992609, by rfl⟩ : syracuseStep 1323479 = 1985219) B1985219
theorem B15217145 : Blo 519798 15217145 := bstep (se 2 (by rfl) ⟨5706429, by rfl⟩ : syracuseStep 15217145 = 11412859) B11412859
theorem B9548441 : Blo 519798 9548441 := bstep (se 2 (by rfl) ⟨3580665, by rfl⟩ : syracuseStep 9548441 = 7161331) B7161331
theorem B1586395 : Blo 519798 1586395 := bstep (se 1 (by rfl) ⟨1189796, by rfl⟩ : syracuseStep 1586395 = 2379593) B2379593
theorem B9549161 : Blo 519798 9549161 := bstep (se 2 (by rfl) ⟨3580935, by rfl⟩ : syracuseStep 9549161 = 7161871) B7161871
theorem B2962817 : Blo 519798 2962817 := bstep (se 2 (by rfl) ⟨1111056, by rfl⟩ : syracuseStep 2962817 = 2222113) B2222113
theorem B1324795 : Blo 519798 1324795 := bstep (se 1 (by rfl) ⟨993596, by rfl⟩ : syracuseStep 1324795 = 1987193) B1987193
theorem B1324937 : Blo 519798 1324937 := bstep (se 2 (by rfl) ⟨496851, by rfl⟩ : syracuseStep 1324937 = 993703) B993703
theorem B2635739 : Blo 519798 2635739 := bstep (se 1 (by rfl) ⟨1976804, by rfl⟩ : syracuseStep 2635739 = 3953609) B3953609
theorem B10008805 : Blo 519798 10008805 := bstep (se 4 (by rfl) ⟨938325, by rfl⟩ : syracuseStep 10008805 = 1876651) B1876651
theorem B1522027 : Blo 519798 1522027 := bstep (se 1 (by rfl) ⟨1141520, by rfl⟩ : syracuseStep 1522027 = 2283041) B2283041
theorem B1784339 : Blo 519798 1784339 := bstep (se 1 (by rfl) ⟨1338254, by rfl⟩ : syracuseStep 1784339 = 2676509) B2676509
theorem B1489529 : Blo 519798 1489529 := bstep (se 2 (by rfl) ⟨558573, by rfl⟩ : syracuseStep 1489529 = 1117147) B1117147
theorem B12696203 : Blo 519798 12696203 := bstep (se 1 (by rfl) ⟨9522152, by rfl⟩ : syracuseStep 12696203 = 19044305) B19044305
theorem B5094161 : Blo 519798 5094161 := bstep (se 2 (by rfl) ⟨1910310, by rfl⟩ : syracuseStep 5094161 = 3820621) B3820621
theorem B5717287 : Blo 519798 5717287 := bstep (se 1 (by rfl) ⟨4287965, by rfl⟩ : syracuseStep 5717287 = 8575931) B8575931
theorem B835067 : Blo 519798 835067 := bstep (se 1 (by rfl) ⟨626300, by rfl⟩ : syracuseStep 835067 = 1252601) B1252601
theorem B22593167 : Blo 519798 22593167 := bstep (se 1 (by rfl) ⟨16944875, by rfl⟩ : syracuseStep 22593167 = 33889751) B33889751
theorem B835247 : Blo 519798 835247 := bstep (se 1 (by rfl) ⟨626435, by rfl⟩ : syracuseStep 835247 = 1252871) B1252871
theorem B14991065 : Blo 519798 14991065 := bstep (se 2 (by rfl) ⟨5621649, by rfl⟩ : syracuseStep 14991065 = 11243299) B11243299
theorem B418234211 : Blo 519798 418234211 := bstep (se 1 (by rfl) ⟨313675658, by rfl⟩ : syracuseStep 418234211 = 627351317) B627351317
theorem B1982333 : Blo 519798 1982333 := bstep (se 3 (by rfl) ⟨371687, by rfl⟩ : syracuseStep 1982333 = 743375) B743375
theorem B2638331 : Blo 519798 2638331 := bstep (se 1 (by rfl) ⟨1978748, by rfl⟩ : syracuseStep 2638331 = 3957497) B3957497
theorem B2966483 : Blo 519798 2966483 := bstep (se 1 (by rfl) ⟨2224862, by rfl⟩ : syracuseStep 2966483 = 4449725) B4449725
theorem B3818753 : Blo 519798 3818753 := bstep (se 2 (by rfl) ⟨1432032, by rfl⟩ : syracuseStep 3818753 = 2864065) B2864065
theorem B1983959 : Blo 519798 1983959 := bstep (se 1 (by rfl) ⟨1487969, by rfl⟩ : syracuseStep 1983959 = 2975939) B2975939
theorem B1754621 : Blo 519798 1754621 := bstep (se 3 (by rfl) ⟨328991, by rfl⟩ : syracuseStep 1754621 = 657983) B657983
theorem B1755431 : Blo 519798 1755431 := bstep (se 1 (by rfl) ⟨1316573, by rfl⟩ : syracuseStep 1755431 = 2633147) B2633147
theorem B8669645 : Blo 519798 8669645 := bstep (se 3 (by rfl) ⟨1625558, by rfl⟩ : syracuseStep 8669645 = 3251117) B3251117
theorem B1886903 : Blo 519798 1886903 := bstep (se 1 (by rfl) ⟨1415177, by rfl⟩ : syracuseStep 1886903 = 2830355) B2830355
theorem B2640599 : Blo 519798 2640599 := bstep (se 1 (by rfl) ⟨1980449, by rfl⟩ : syracuseStep 2640599 = 3960899) B3960899
theorem B937001 : Blo 519798 937001 := bstep (se 2 (by rfl) ⟨351375, by rfl⟩ : syracuseStep 937001 = 702751) B702751
theorem B1756295 : Blo 519798 1756295 := bstep (se 1 (by rfl) ⟨1317221, by rfl⟩ : syracuseStep 1756295 = 2634443) B2634443
theorem B9653411 : Blo 519798 9653411 := bstep (se 1 (by rfl) ⟨7240058, by rfl⟩ : syracuseStep 9653411 = 14480117) B14480117
theorem B1985735 : Blo 519798 1985735 := bstep (se 1 (by rfl) ⟨1489301, by rfl⟩ : syracuseStep 1985735 = 2978603) B2978603
theorem B1756403 : Blo 519798 1756403 := bstep (se 1 (by rfl) ⟨1317302, by rfl⟩ : syracuseStep 1756403 = 2634605) B2634605
theorem B2969081 : Blo 519798 2969081 := bstep (se 2 (by rfl) ⟨1113405, by rfl⟩ : syracuseStep 2969081 = 2226811) B2226811
theorem B773723 : Blo 519798 773723 := bstep (se 1 (by rfl) ⟨580292, by rfl⟩ : syracuseStep 773723 = 1160585) B1160585
theorem B741097 : Blo 519798 741097 := bstep (se 2 (by rfl) ⟨277911, by rfl⟩ : syracuseStep 741097 = 555823) B555823
theorem B2969581 : Blo 519798 2969581 := bstep (se 3 (by rfl) ⟨556796, by rfl⟩ : syracuseStep 2969581 = 1113593) B1113593
theorem B5951555 : Blo 519798 5951555 := bstep (se 1 (by rfl) ⟨4463666, by rfl⟩ : syracuseStep 5951555 = 8927333) B8927333
theorem B1758077 : Blo 519798 1758077 := bstep (se 3 (by rfl) ⟨329639, by rfl⟩ : syracuseStep 1758077 = 659279) B659279
theorem B11326337 : Blo 519798 11326337 := bstep (se 2 (by rfl) ⟨4247376, by rfl⟩ : syracuseStep 11326337 = 8494753) B8494753
theorem B1758347 : Blo 519798 1758347 := bstep (se 1 (by rfl) ⟨1318760, by rfl⟩ : syracuseStep 1758347 = 2637521) B2637521
theorem B2970857 : Blo 519798 2970857 := bstep (se 2 (by rfl) ⟨1114071, by rfl⟩ : syracuseStep 2970857 = 2228143) B2228143
theorem B3758147 : Blo 519798 3758147 := bstep (se 1 (by rfl) ⟨2818610, by rfl⟩ : syracuseStep 3758147 = 5637221) B5637221
theorem B940223 : Blo 519798 940223 := bstep (se 1 (by rfl) ⟨705167, by rfl⟩ : syracuseStep 940223 = 1410335) B1410335
theorem B6707393 : Blo 519798 6707393 := bstep (se 2 (by rfl) ⟨2515272, by rfl⟩ : syracuseStep 6707393 = 5030545) B5030545
theorem B3955067 : Blo 519798 3955067 := bstep (se 1 (by rfl) ⟨2966300, by rfl⟩ : syracuseStep 3955067 = 5932601) B5932601
theorem B1759967 : Blo 519798 1759967 := bstep (se 1 (by rfl) ⟨1319975, by rfl⟩ : syracuseStep 1759967 = 2639951) B2639951
theorem B2972497 : Blo 519798 2972497 := bstep (se 2 (by rfl) ⟨1114686, by rfl⟩ : syracuseStep 2972497 = 2229373) B2229373
theorem B104225753 : Blo 519798 104225753 := bstep (se 2 (by rfl) ⟨39084657, by rfl⟩ : syracuseStep 104225753 = 78169315) B78169315
theorem B2644973 : Blo 519798 2644973 := bstep (se 3 (by rfl) ⟨495932, by rfl⟩ : syracuseStep 2644973 = 991865) B991865
theorem B1170503 : Blo 519798 1170503 := bstep (se 1 (by rfl) ⟨877877, by rfl⟩ : syracuseStep 1170503 = 1755755) B1755755
theorem B2973023 : Blo 519798 2973023 := bstep (se 1 (by rfl) ⟨2229767, by rfl⟩ : syracuseStep 2973023 = 4459535) B4459535
theorem B1170899 : Blo 519798 1170899 := bstep (se 1 (by rfl) ⟨878174, by rfl⟩ : syracuseStep 1170899 = 1756349) B1756349
theorem B1760723 : Blo 519798 1760723 := bstep (se 1 (by rfl) ⟨1320542, by rfl⟩ : syracuseStep 1760723 = 2641085) B2641085
theorem B941743 : Blo 519798 941743 := bstep (se 1 (by rfl) ⟨706307, by rfl⟩ : syracuseStep 941743 = 1412615) B1412615
theorem B1171169 : Blo 519798 1171169 := bstep (se 2 (by rfl) ⟨439188, by rfl⟩ : syracuseStep 1171169 = 878377) B878377
theorem B1760993 : Blo 519798 1760993 := bstep (se 2 (by rfl) ⟨660372, by rfl⟩ : syracuseStep 1760993 = 1320745) B1320745
theorem B1105633 : Blo 519798 1105633 := bstep (se 2 (by rfl) ⟨414612, by rfl⟩ : syracuseStep 1105633 = 829225) B829225
theorem B2645783 : Blo 519798 2645783 := bstep (se 1 (by rfl) ⟨1984337, by rfl⟩ : syracuseStep 2645783 = 3968675) B3968675
theorem B2973955 : Blo 519798 2973955 := bstep (se 1 (by rfl) ⟨2230466, by rfl⟩ : syracuseStep 2973955 = 4460933) B4460933
theorem B2417015 : Blo 519798 2417015 := bstep (se 1 (by rfl) ⟨1812761, by rfl⟩ : syracuseStep 2417015 = 3625523) B3625523
theorem B2220797 : Blo 519798 2220797 := bstep (se 3 (by rfl) ⟨416399, by rfl⟩ : syracuseStep 2220797 = 832799) B832799
theorem B877675 : Blo 519798 877675 := bstep (se 1 (by rfl) ⟨658256, by rfl⟩ : syracuseStep 877675 = 1316513) B1316513
theorem B1172843 : Blo 519798 1172843 := bstep (se 1 (by rfl) ⟨879632, by rfl⟩ : syracuseStep 1172843 = 1759265) B1759265
theorem B1762667 : Blo 519798 1762667 := bstep (se 1 (by rfl) ⟨1322000, by rfl⟩ : syracuseStep 1762667 = 2644001) B2644001
theorem B2647403 : Blo 519798 2647403 := bstep (se 1 (by rfl) ⟨1985552, by rfl⟩ : syracuseStep 2647403 = 3971105) B3971105
theorem B877979 : Blo 519798 877979 := bstep (se 1 (by rfl) ⟨658484, by rfl⟩ : syracuseStep 877979 = 1316969) B1316969
theorem B1762775 : Blo 519798 1762775 := bstep (se 1 (by rfl) ⟨1322081, by rfl⟩ : syracuseStep 1762775 = 2644163) B2644163
theorem B5006863 : Blo 519798 5006863 := bstep (se 1 (by rfl) ⟨3755147, by rfl⟩ : syracuseStep 5006863 = 7510295) B7510295
theorem B779897 : Blo 519798 779897 := bstep (se 2 (by rfl) ⟨292461, by rfl⟩ : syracuseStep 779897 = 584923) B584923
theorem B1173113 : Blo 519798 1173113 := bstep (se 2 (by rfl) ⟨439917, by rfl⟩ : syracuseStep 1173113 = 879835) B879835
theorem B1762937 : Blo 519798 1762937 := bstep (se 2 (by rfl) ⟨661101, by rfl⟩ : syracuseStep 1762937 = 1322203) B1322203
theorem B779999 : Blo 519798 779999 := bstep (se 1 (by rfl) ⟨584999, by rfl⟩ : syracuseStep 779999 = 1169999) B1169999
theorem B878303 : Blo 519798 878303 := bstep (se 1 (by rfl) ⟨658727, by rfl⟩ : syracuseStep 878303 = 1317455) B1317455
theorem B780095 : Blo 519798 780095 := bstep (se 1 (by rfl) ⟨585071, by rfl⟩ : syracuseStep 780095 = 1170143) B1170143
theorem B5629783 : Blo 519798 5629783 := bstep (se 1 (by rfl) ⟨4222337, by rfl⟩ : syracuseStep 5629783 = 8444675) B8444675
theorem B780263 : Blo 519798 780263 := bstep (se 1 (by rfl) ⟨585197, by rfl⟩ : syracuseStep 780263 = 1170395) B1170395
theorem B780281 : Blo 519798 780281 := bstep (se 2 (by rfl) ⟨292605, by rfl⟩ : syracuseStep 780281 = 585211) B585211
theorem B780383 : Blo 519798 780383 := bstep (se 1 (by rfl) ⟨585287, by rfl⟩ : syracuseStep 780383 = 1170575) B1170575
theorem B878735 : Blo 519798 878735 := bstep (se 1 (by rfl) ⟨659051, by rfl⟩ : syracuseStep 878735 = 1318103) B1318103
theorem B780443 : Blo 519798 780443 := bstep (se 1 (by rfl) ⟨585332, by rfl⟩ : syracuseStep 780443 = 1170665) B1170665
theorem B780479 : Blo 519798 780479 := bstep (se 1 (by rfl) ⟨585359, by rfl⟩ : syracuseStep 780479 = 1170719) B1170719
theorem B780521 : Blo 519798 780521 := bstep (se 2 (by rfl) ⟨292695, by rfl⟩ : syracuseStep 780521 = 585391) B585391
theorem B878971 : Blo 519798 878971 := bstep (se 1 (by rfl) ⟨659228, by rfl⟩ : syracuseStep 878971 = 1318457) B1318457
theorem B780827 : Blo 519798 780827 := bstep (se 1 (by rfl) ⟨585620, by rfl⟩ : syracuseStep 780827 = 1171241) B1171241
theorem B780905 : Blo 519798 780905 := bstep (se 2 (by rfl) ⟨292839, by rfl⟩ : syracuseStep 780905 = 585679) B585679
theorem B1174121 : Blo 519798 1174121 := bstep (se 2 (by rfl) ⟨440295, by rfl⟩ : syracuseStep 1174121 = 880591) B880591
theorem B879241 : Blo 519798 879241 := bstep (se 2 (by rfl) ⟨329715, by rfl⟩ : syracuseStep 879241 = 659431) B659431
theorem B1764449 : Blo 519798 1764449 := bstep (se 2 (by rfl) ⟨661668, by rfl⟩ : syracuseStep 1764449 = 1323337) B1323337
theorem B2649185 : Blo 519798 2649185 := bstep (se 2 (by rfl) ⟨993444, by rfl⟩ : syracuseStep 2649185 = 1986889) B1986889
theorem B781433 : Blo 519798 781433 := bstep (se 2 (by rfl) ⟨293037, by rfl⟩ : syracuseStep 781433 = 586075) B586075
theorem B781535 : Blo 519798 781535 := bstep (se 1 (by rfl) ⟨586151, by rfl⟩ : syracuseStep 781535 = 1172303) B1172303
theorem B1174751 : Blo 519798 1174751 := bstep (se 1 (by rfl) ⟨881063, by rfl⟩ : syracuseStep 1174751 = 1762127) B1762127
theorem B781577 : Blo 519798 781577 := bstep (se 2 (by rfl) ⟨293091, by rfl⟩ : syracuseStep 781577 = 586183) B586183
theorem B781679 : Blo 519798 781679 := bstep (se 1 (by rfl) ⟨586259, by rfl⟩ : syracuseStep 781679 = 1172519) B1172519
theorem B1174967 : Blo 519798 1174967 := bstep (se 1 (by rfl) ⟨881225, by rfl⟩ : syracuseStep 1174967 = 1762451) B1762451
theorem B781799 : Blo 519798 781799 := bstep (se 1 (by rfl) ⟨586349, by rfl⟩ : syracuseStep 781799 = 1172699) B1172699
theorem B3763745 : Blo 519798 3763745 := bstep (se 2 (by rfl) ⟨1411404, by rfl⟩ : syracuseStep 3763745 = 2822809) B2822809
theorem B781931 : Blo 519798 781931 := bstep (se 1 (by rfl) ⟨586448, by rfl⟩ : syracuseStep 781931 = 1172897) B1172897
theorem B1175147 : Blo 519798 1175147 := bstep (se 1 (by rfl) ⟨881360, by rfl⟩ : syracuseStep 1175147 = 1762721) B1762721
theorem B1764989 : Blo 519798 1764989 := bstep (se 3 (by rfl) ⟨330935, by rfl⟩ : syracuseStep 1764989 = 661871) B661871
theorem B782057 : Blo 519798 782057 := bstep (se 2 (by rfl) ⟨293271, by rfl⟩ : syracuseStep 782057 = 586543) B586543
theorem B520007 : Blo 519798 520007 := bstep (se 1 (by rfl) ⟨390005, by rfl⟩ : syracuseStep 520007 = 780011) B780011
theorem B782201 : Blo 519798 782201 := bstep (se 2 (by rfl) ⟨293325, by rfl⟩ : syracuseStep 782201 = 586651) B586651
theorem B1175417 : Blo 519798 1175417 := bstep (se 2 (by rfl) ⟨440781, by rfl⟩ : syracuseStep 1175417 = 881563) B881563
theorem B1765259 : Blo 519798 1765259 := bstep (se 1 (by rfl) ⟨1323944, by rfl⟩ : syracuseStep 1765259 = 2647889) B2647889
theorem B2649995 : Blo 519798 2649995 := bstep (se 1 (by rfl) ⟨1987496, by rfl⟩ : syracuseStep 2649995 = 3974993) B3974993
theorem B520159 : Blo 519798 520159 := bstep (se 1 (by rfl) ⟨390119, by rfl⟩ : syracuseStep 520159 = 780239) B780239
theorem B782303 : Blo 519798 782303 := bstep (se 1 (by rfl) ⟨586727, by rfl⟩ : syracuseStep 782303 = 1173455) B1173455
theorem B782555 : Blo 519798 782555 := bstep (se 1 (by rfl) ⟨586916, by rfl⟩ : syracuseStep 782555 = 1173833) B1173833
theorem B520423 : Blo 519798 520423 := bstep (se 1 (by rfl) ⟨390317, by rfl⟩ : syracuseStep 520423 = 780635) B780635
theorem B782567 : Blo 519798 782567 := bstep (se 1 (by rfl) ⟨586925, by rfl⟩ : syracuseStep 782567 = 1173851) B1173851
theorem B520575 : Blo 519798 520575 := bstep (se 1 (by rfl) ⟨390431, by rfl⟩ : syracuseStep 520575 = 780863) B780863
theorem B586111 : Blo 519798 586111 := bstep (se 1 (by rfl) ⟨439583, by rfl⟩ : syracuseStep 586111 = 879167) B879167
theorem B881023 : Blo 519798 881023 := bstep (se 1 (by rfl) ⟨660767, by rfl⟩ : syracuseStep 881023 = 1321535) B1321535
theorem B782729 : Blo 519798 782729 := bstep (se 2 (by rfl) ⟨293523, by rfl⟩ : syracuseStep 782729 = 587047) B587047
theorem B1765799 : Blo 519798 1765799 := bstep (se 1 (by rfl) ⟨1324349, by rfl⟩ : syracuseStep 1765799 = 2648699) B2648699
theorem B520655 : Blo 519798 520655 := bstep (se 1 (by rfl) ⟨390491, by rfl⟩ : syracuseStep 520655 = 780983) B780983
theorem B782825 : Blo 519798 782825 := bstep (se 2 (by rfl) ⟨293559, by rfl⟩ : syracuseStep 782825 = 587119) B587119
theorem B520807 : Blo 519798 520807 := bstep (se 1 (by rfl) ⟨390605, by rfl⟩ : syracuseStep 520807 = 781211) B781211
theorem B782951 : Blo 519798 782951 := bstep (se 1 (by rfl) ⟨587213, by rfl⟩ : syracuseStep 782951 = 1174427) B1174427
theorem B1110689 : Blo 519798 1110689 := bstep (se 2 (by rfl) ⟨416508, by rfl⟩ : syracuseStep 1110689 = 833017) B833017
theorem B783083 : Blo 519798 783083 := bstep (se 1 (by rfl) ⟨587312, by rfl⟩ : syracuseStep 783083 = 1174625) B1174625
theorem B1110791 : Blo 519798 1110791 := bstep (se 1 (by rfl) ⟨833093, by rfl⟩ : syracuseStep 1110791 = 1666187) B1666187
theorem B783113 : Blo 519798 783113 := bstep (se 2 (by rfl) ⟨293667, by rfl⟩ : syracuseStep 783113 = 587335) B587335
theorem B881455 : Blo 519798 881455 := bstep (se 1 (by rfl) ⟨661091, by rfl⟩ : syracuseStep 881455 = 1322183) B1322183
theorem B521071 : Blo 519798 521071 := bstep (se 1 (by rfl) ⟨390803, by rfl⟩ : syracuseStep 521071 = 781607) B781607
theorem B783215 : Blo 519798 783215 := bstep (se 1 (by rfl) ⟨587411, by rfl⟩ : syracuseStep 783215 = 1174823) B1174823
theorem B521127 : Blo 519798 521127 := bstep (se 1 (by rfl) ⟨390845, by rfl⟩ : syracuseStep 521127 = 781691) B781691
theorem B521211 : Blo 519798 521211 := bstep (se 1 (by rfl) ⟨390908, by rfl⟩ : syracuseStep 521211 = 781817) B781817
theorem B521279 : Blo 519798 521279 := bstep (se 1 (by rfl) ⟨390959, by rfl⟩ : syracuseStep 521279 = 781919) B781919
theorem B783467 : Blo 519798 783467 := bstep (se 1 (by rfl) ⟨587600, by rfl⟩ : syracuseStep 783467 = 1175201) B1175201
theorem B521423 : Blo 519798 521423 := bstep (se 1 (by rfl) ⟨391067, by rfl⟩ : syracuseStep 521423 = 782135) B782135
theorem B2651453 : Blo 519798 2651453 := bstep (se 3 (by rfl) ⟨497147, by rfl⟩ : syracuseStep 2651453 = 994295) B994295
theorem B783707 : Blo 519798 783707 := bstep (se 1 (by rfl) ⟨587780, by rfl⟩ : syracuseStep 783707 = 1175561) B1175561
theorem B521627 : Blo 519798 521627 := bstep (se 1 (by rfl) ⟨391220, by rfl⟩ : syracuseStep 521627 = 782441) B782441
theorem B521839 : Blo 519798 521839 := bstep (se 1 (by rfl) ⟨391379, by rfl⟩ : syracuseStep 521839 = 782759) B782759
theorem B783983 : Blo 519798 783983 := bstep (se 1 (by rfl) ⟨587987, by rfl⟩ : syracuseStep 783983 = 1175975) B1175975
theorem B521895 : Blo 519798 521895 := bstep (se 1 (by rfl) ⟨391421, by rfl⟩ : syracuseStep 521895 = 782843) B782843
theorem B784055 : Blo 519798 784055 := bstep (se 1 (by rfl) ⟨588041, by rfl⟩ : syracuseStep 784055 = 1176083) B1176083
theorem B1177271 : Blo 519798 1177271 := bstep (se 1 (by rfl) ⟨882953, by rfl⟩ : syracuseStep 1177271 = 1765907) B1765907
theorem B1767095 : Blo 519798 1767095 := bstep (se 1 (by rfl) ⟨1325321, by rfl⟩ : syracuseStep 1767095 = 2650643) B2650643
theorem B784091 : Blo 519798 784091 := bstep (se 1 (by rfl) ⟨588068, by rfl⟩ : syracuseStep 784091 = 1176137) B1176137
theorem B521979 : Blo 519798 521979 := bstep (se 1 (by rfl) ⟨391484, by rfl⟩ : syracuseStep 521979 = 782969) B782969
theorem B587515 : Blo 519798 587515 := bstep (se 1 (by rfl) ⟨440636, by rfl⟩ : syracuseStep 587515 = 881273) B881273
theorem B882427 : Blo 519798 882427 := bstep (se 1 (by rfl) ⟨661820, by rfl⟩ : syracuseStep 882427 = 1323641) B1323641
theorem B522015 : Blo 519798 522015 := bstep (se 1 (by rfl) ⟨391511, by rfl⟩ : syracuseStep 522015 = 783023) B783023
theorem B587551 : Blo 519798 587551 := bstep (se 1 (by rfl) ⟨440663, by rfl⟩ : syracuseStep 587551 = 881327) B881327
theorem B522047 : Blo 519798 522047 := bstep (se 1 (by rfl) ⟨391535, by rfl⟩ : syracuseStep 522047 = 783071) B783071
theorem B784265 : Blo 519798 784265 := bstep (se 2 (by rfl) ⟨294099, by rfl⟩ : syracuseStep 784265 = 588199) B588199
theorem B882569 : Blo 519798 882569 := bstep (se 2 (by rfl) ⟨330963, by rfl⟩ : syracuseStep 882569 = 661927) B661927
theorem B3962843 : Blo 519798 3962843 := bstep (se 1 (by rfl) ⟨2972132, by rfl⟩ : syracuseStep 3962843 = 5944265) B5944265
theorem B1112039 : Blo 519798 1112039 := bstep (se 1 (by rfl) ⟨834029, by rfl⟩ : syracuseStep 1112039 = 1668059) B1668059
theorem B522223 : Blo 519798 522223 := bstep (se 1 (by rfl) ⟨391667, by rfl⟩ : syracuseStep 522223 = 783335) B783335
theorem B784367 : Blo 519798 784367 := bstep (se 1 (by rfl) ⟨588275, by rfl⟩ : syracuseStep 784367 = 1176551) B1176551
theorem B5961761 : Blo 519798 5961761 := bstep (se 2 (by rfl) ⟨2235660, by rfl⟩ : syracuseStep 5961761 = 4471321) B4471321
theorem B522395 : Blo 519798 522395 := bstep (se 1 (by rfl) ⟨391796, by rfl⟩ : syracuseStep 522395 = 783593) B783593
theorem B522431 : Blo 519798 522431 := bstep (se 1 (by rfl) ⟨391823, by rfl⟩ : syracuseStep 522431 = 783647) B783647
theorem B784619 : Blo 519798 784619 := bstep (se 1 (by rfl) ⟨588464, by rfl⟩ : syracuseStep 784619 = 1176929) B1176929
theorem B784679 : Blo 519798 784679 := bstep (se 1 (by rfl) ⟨588509, by rfl⟩ : syracuseStep 784679 = 1177019) B1177019
theorem B522543 : Blo 519798 522543 := bstep (se 1 (by rfl) ⟨391907, by rfl⟩ : syracuseStep 522543 = 783815) B783815
theorem B883001 : Blo 519798 883001 := bstep (se 2 (by rfl) ⟨331125, by rfl⟩ : syracuseStep 883001 = 662251) B662251
theorem B784763 : Blo 519798 784763 := bstep (se 1 (by rfl) ⟨588572, by rfl⟩ : syracuseStep 784763 = 1177145) B1177145
theorem B522779 : Blo 519798 522779 := bstep (se 1 (by rfl) ⟨392084, by rfl⟩ : syracuseStep 522779 = 784169) B784169
theorem B522783 : Blo 519798 522783 := bstep (se 1 (by rfl) ⟨392087, by rfl⟩ : syracuseStep 522783 = 784175) B784175
theorem B10680893 : Blo 519798 10680893 := bstep (se 3 (by rfl) ⟨2002667, by rfl⟩ : syracuseStep 10680893 = 4005335) B4005335
theorem B1604233 : Blo 519798 1604233 := bstep (se 2 (by rfl) ⟨601587, by rfl⟩ : syracuseStep 1604233 = 1203175) B1203175
theorem B785033 : Blo 519798 785033 := bstep (se 2 (by rfl) ⟨294387, by rfl⟩ : syracuseStep 785033 = 588775) B588775
theorem B785207 : Blo 519798 785207 := bstep (se 1 (by rfl) ⟨588905, by rfl⟩ : syracuseStep 785207 = 1177811) B1177811
theorem B523099 : Blo 519798 523099 := bstep (se 1 (by rfl) ⟨392324, by rfl⟩ : syracuseStep 523099 = 784649) B784649
theorem B785243 : Blo 519798 785243 := bstep (se 1 (by rfl) ⟨588932, by rfl⟩ : syracuseStep 785243 = 1177865) B1177865
theorem B1178459 : Blo 519798 1178459 := bstep (se 1 (by rfl) ⟨883844, by rfl⟩ : syracuseStep 1178459 = 1767689) B1767689
theorem B523167 : Blo 519798 523167 := bstep (se 1 (by rfl) ⟨392375, by rfl⟩ : syracuseStep 523167 = 784751) B784751
theorem B588703 : Blo 519798 588703 := bstep (se 1 (by rfl) ⟨441527, by rfl⟩ : syracuseStep 588703 = 883055) B883055
theorem B883615 : Blo 519798 883615 := bstep (se 1 (by rfl) ⟨662711, by rfl⟩ : syracuseStep 883615 = 1325423) B1325423
theorem B785387 : Blo 519798 785387 := bstep (se 1 (by rfl) ⟨589040, by rfl⟩ : syracuseStep 785387 = 1178081) B1178081
theorem B556079 : Blo 519798 556079 := bstep (se 1 (by rfl) ⟨417059, by rfl⟩ : syracuseStep 556079 = 834119) B834119
theorem B523311 : Blo 519798 523311 := bstep (se 1 (by rfl) ⟨392483, by rfl⟩ : syracuseStep 523311 = 784967) B784967
theorem B588847 : Blo 519798 588847 := bstep (se 1 (by rfl) ⟨441635, by rfl⟩ : syracuseStep 588847 = 883271) B883271
theorem B523335 : Blo 519798 523335 := bstep (se 1 (by rfl) ⟨392501, by rfl⟩ : syracuseStep 523335 = 785003) B785003
theorem B785591 : Blo 519798 785591 := bstep (se 1 (by rfl) ⟨589193, by rfl⟩ : syracuseStep 785591 = 1178387) B1178387
theorem B523487 : Blo 519798 523487 := bstep (se 1 (by rfl) ⟨392615, by rfl⟩ : syracuseStep 523487 = 785231) B785231
theorem B589135 : Blo 519798 589135 := bstep (se 1 (by rfl) ⟨441851, by rfl⟩ : syracuseStep 589135 = 883703) B883703
theorem B5963219 : Blo 519798 5963219 := bstep (se 1 (by rfl) ⟨4472414, by rfl⟩ : syracuseStep 5963219 = 8944829) B8944829
theorem B523751 : Blo 519798 523751 := bstep (se 1 (by rfl) ⟨392813, by rfl⟩ : syracuseStep 523751 = 785627) B785627
theorem B1113679 : Blo 519798 1113679 := bstep (se 1 (by rfl) ⟨835259, by rfl⟩ : syracuseStep 1113679 = 1670519) B1670519
theorem B3767951 : Blo 519798 3767951 := bstep (se 1 (by rfl) ⟨2825963, by rfl⟩ : syracuseStep 3767951 = 5651927) B5651927
theorem B2981519 : Blo 519798 2981519 := bstep (se 1 (by rfl) ⟨2236139, by rfl⟩ : syracuseStep 2981519 = 4472279) B4472279
theorem B1113833 : Blo 519798 1113833 := bstep (se 2 (by rfl) ⟨417687, by rfl⟩ : syracuseStep 1113833 = 835375) B835375
theorem B3965273 : Blo 519798 3965273 := bstep (se 2 (by rfl) ⟨1486977, by rfl⟩ : syracuseStep 3965273 = 2973955) B2973955
theorem B19333727 : Blo 519798 19333727 := bstep (se 1 (by rfl) ⟨14500295, by rfl⟩ : syracuseStep 19333727 = 29000591) B29000591
theorem B18089405 : Blo 519798 18089405 := bstep (se 3 (by rfl) ⟨3391763, by rfl⟩ : syracuseStep 18089405 = 6783527) B6783527
theorem B8128457 : Blo 519798 8128457 := bstep (se 2 (by rfl) ⟨3048171, by rfl⟩ : syracuseStep 8128457 = 6096343) B6096343
theorem B624667 : Blo 519798 624667 := bstep (se 1 (by rfl) ⟨468500, by rfl⟩ : syracuseStep 624667 = 937001) B937001
theorem B5638565 : Blo 519798 5638565 := bstep (se 4 (by rfl) ⟨528615, by rfl⟩ : syracuseStep 5638565 = 1057231) B1057231
theorem B7506377 : Blo 519798 7506377 := bstep (se 2 (by rfl) ⟨2814891, by rfl⟩ : syracuseStep 7506377 = 5629783) B5629783
theorem B3967703 : Blo 519798 3967703 := bstep (se 1 (by rfl) ⟨2975777, by rfl⟩ : syracuseStep 3967703 = 5951555) B5951555
theorem B7540229 : Blo 519798 7540229 := bstep (se 4 (by rfl) ⟨706896, by rfl⟩ : syracuseStep 7540229 = 1413793) B1413793
theorem B626815 : Blo 519798 626815 := bstep (se 1 (by rfl) ⟨470111, by rfl⟩ : syracuseStep 626815 = 940223) B940223
theorem B790703 : Blo 519798 790703 := bstep (se 1 (by rfl) ⟨593027, by rfl⟩ : syracuseStep 790703 = 1186055) B1186055
theorem B988129 : Blo 519798 988129 := bstep (se 2 (by rfl) ⟨370548, by rfl⟩ : syracuseStep 988129 = 741097) B741097
theorem B1315865 : Blo 519798 1315865 := bstep (se 2 (by rfl) ⟨493449, by rfl⟩ : syracuseStep 1315865 = 986899) B986899
theorem B660575 : Blo 519798 660575 := bstep (se 1 (by rfl) ⟨495431, by rfl⟩ : syracuseStep 660575 = 990863) B990863
theorem B1316047 : Blo 519798 1316047 := bstep (se 1 (by rfl) ⟨987035, by rfl⟩ : syracuseStep 1316047 = 1974071) B1974071
theorem B1611343 : Blo 519798 1611343 := bstep (se 1 (by rfl) ⟨1208507, by rfl⟩ : syracuseStep 1611343 = 2417015) B2417015
theorem B1480531 : Blo 519798 1480531 := bstep (se 1 (by rfl) ⟨1110398, by rfl⟩ : syracuseStep 1480531 = 2220797) B2220797
theorem B4462573 : Blo 519798 4462573 := bstep (se 3 (by rfl) ⟨836732, by rfl⟩ : syracuseStep 4462573 = 1673465) B1673465
theorem B9050399 : Blo 519798 9050399 := bstep (se 1 (by rfl) ⟨6787799, by rfl⟩ : syracuseStep 9050399 = 13575599) B13575599
theorem B792991 : Blo 519798 792991 := bstep (se 1 (by rfl) ⟨594743, by rfl⟩ : syracuseStep 792991 = 1189487) B1189487
theorem B8460773 : Blo 519798 8460773 := bstep (se 4 (by rfl) ⟨793197, by rfl⟩ : syracuseStep 8460773 = 1586395) B1586395
theorem B989671 : Blo 519798 989671 := bstep (se 1 (by rfl) ⟨742253, by rfl⟩ : syracuseStep 989671 = 1484507) B1484507
theorem B3972077 : Blo 519798 3972077 := bstep (se 3 (by rfl) ⟨744764, by rfl⟩ : syracuseStep 3972077 = 1489529) B1489529
theorem B1973767 : Blo 519798 1973767 := bstep (se 1 (by rfl) ⟨1480325, by rfl⟩ : syracuseStep 1973767 = 2960651) B2960651
theorem B1318619 : Blo 519798 1318619 := bstep (se 1 (by rfl) ⟨988964, by rfl⟩ : syracuseStep 1318619 = 1977929) B1977929
theorem B1580897 : Blo 519798 1580897 := bstep (se 2 (by rfl) ⟨592836, by rfl⟩ : syracuseStep 1580897 = 1185673) B1185673
theorem B1974239 : Blo 519798 1974239 := bstep (se 1 (by rfl) ⟨1480679, by rfl⟩ : syracuseStep 1974239 = 2961359) B2961359
theorem B1482877 : Blo 519798 1482877 := bstep (se 3 (by rfl) ⟨278039, by rfl⟩ : syracuseStep 1482877 = 556079) B556079
theorem B13345073 : Blo 519798 13345073 := bstep (se 2 (by rfl) ⟨5004402, by rfl⟩ : syracuseStep 13345073 = 10008805) B10008805
theorem B6365627 : Blo 519798 6365627 := bstep (se 1 (by rfl) ⟨4774220, by rfl⟩ : syracuseStep 6365627 = 9548441) B9548441
theorem B2138977 : Blo 519798 2138977 := bstep (se 2 (by rfl) ⟨802116, by rfl⟩ : syracuseStep 2138977 = 1604233) B1604233
theorem B6366107 : Blo 519798 6366107 := bstep (se 1 (by rfl) ⟨4774580, by rfl⟩ : syracuseStep 6366107 = 9549161) B9549161
theorem B1975211 : Blo 519798 1975211 := bstep (se 1 (by rfl) ⟨1481408, by rfl⟩ : syracuseStep 1975211 = 2962817) B2962817
theorem B3974507 : Blo 519798 3974507 := bstep (se 1 (by rfl) ⟨2980880, by rfl⟩ : syracuseStep 3974507 = 5961761) B5961761
theorem B1189559 : Blo 519798 1189559 := bstep (se 1 (by rfl) ⟨892169, by rfl⟩ : syracuseStep 1189559 = 1784339) B1784339
theorem B7120595 : Blo 519798 7120595 := bstep (se 1 (by rfl) ⟨5340446, by rfl⟩ : syracuseStep 7120595 = 10680893) B10680893
theorem B8464135 : Blo 519798 8464135 := bstep (se 1 (by rfl) ⟨6348101, by rfl⟩ : syracuseStep 8464135 = 12696203) B12696203
theorem B1484905 : Blo 519798 1484905 := bstep (se 2 (by rfl) ⟨556839, by rfl⟩ : syracuseStep 1484905 = 1113679) B1113679
theorem B1255657 : Blo 519798 1255657 := bstep (se 2 (by rfl) ⟨470871, by rfl⟩ : syracuseStep 1255657 = 941743) B941743
theorem B3975479 : Blo 519798 3975479 := bstep (se 1 (by rfl) ⟨2981609, by rfl⟩ : syracuseStep 3975479 = 5963219) B5963219
theorem B1321555 : Blo 519798 1321555 := bstep (se 1 (by rfl) ⟨991166, by rfl⟩ : syracuseStep 1321555 = 1982333) B1982333
theorem B1977473 : Blo 519798 1977473 := bstep (se 2 (by rfl) ⟨741552, by rfl⟩ : syracuseStep 1977473 = 1483105) B1483105
theorem B1977655 : Blo 519798 1977655 := bstep (se 1 (by rfl) ⟨1483241, by rfl⟩ : syracuseStep 1977655 = 2966483) B2966483
theorem B8564105 : Blo 519798 8564105 := bstep (se 2 (by rfl) ⟨3211539, by rfl⟩ : syracuseStep 8564105 = 6423079) B6423079
theorem B9547255 : Blo 519798 9547255 := bstep (se 1 (by rfl) ⟨7160441, by rfl⟩ : syracuseStep 9547255 = 14320883) B14320883
theorem B1322639 : Blo 519798 1322639 := bstep (se 1 (by rfl) ⟨991979, by rfl⟩ : syracuseStep 1322639 = 1983959) B1983959
theorem B3976937 : Blo 519798 3976937 := bstep (se 2 (by rfl) ⟨1491351, by rfl⟩ : syracuseStep 3976937 = 2982703) B2982703
theorem B3911759 : Blo 519798 3911759 := bstep (se 1 (by rfl) ⟨2933819, by rfl⟩ : syracuseStep 3911759 = 5867639) B5867639
theorem B5779763 : Blo 519798 5779763 := bstep (se 1 (by rfl) ⟨4334822, by rfl⟩ : syracuseStep 5779763 = 8669645) B8669645
theorem B1257935 : Blo 519798 1257935 := bstep (se 1 (by rfl) ⟨943451, by rfl⟩ : syracuseStep 1257935 = 1886903) B1886903
theorem B5026319 : Blo 519798 5026319 := bstep (se 1 (by rfl) ⟨3769739, by rfl⟩ : syracuseStep 5026319 = 7539479) B7539479
theorem B1487423 : Blo 519798 1487423 := bstep (se 1 (by rfl) ⟨1115567, by rfl⟩ : syracuseStep 1487423 = 2231135) B2231135
theorem B2962109 : Blo 519798 2962109 := bstep (se 3 (by rfl) ⟨555395, by rfl⟩ : syracuseStep 2962109 = 1110791) B1110791
theorem B6435607 : Blo 519798 6435607 := bstep (se 1 (by rfl) ⟨4826705, by rfl⟩ : syracuseStep 6435607 = 9653411) B9653411
theorem B1323823 : Blo 519798 1323823 := bstep (se 1 (by rfl) ⟨992867, by rfl⟩ : syracuseStep 1323823 = 1985735) B1985735
theorem B1487753 : Blo 519798 1487753 := bstep (se 2 (by rfl) ⟨557907, by rfl⟩ : syracuseStep 1487753 = 1115815) B1115815
theorem B6009851 : Blo 519798 6009851 := bstep (se 1 (by rfl) ⟨4507388, by rfl⟩ : syracuseStep 6009851 = 9014777) B9014777
theorem B1979387 : Blo 519798 1979387 := bstep (se 1 (by rfl) ⟨1484540, by rfl⟩ : syracuseStep 1979387 = 2969081) B2969081
theorem B1488527 : Blo 519798 1488527 := bstep (se 1 (by rfl) ⟨1116395, by rfl⟩ : syracuseStep 1488527 = 2232791) B2232791
theorem B16103123 : Blo 519798 16103123 := bstep (se 1 (by rfl) ⟨12077342, by rfl⟩ : syracuseStep 16103123 = 24154685) B24154685
theorem B7550891 : Blo 519798 7550891 := bstep (se 1 (by rfl) ⟨5663168, by rfl⟩ : syracuseStep 7550891 = 11326337) B11326337
theorem B1488937 : Blo 519798 1488937 := bstep (se 2 (by rfl) ⟨558351, by rfl⟩ : syracuseStep 1488937 = 1116703) B1116703
theorem B1980571 : Blo 519798 1980571 := bstep (se 1 (by rfl) ⟨1485428, by rfl⟩ : syracuseStep 1980571 = 2970857) B2970857
theorem B5945723 : Blo 519798 5945723 := bstep (se 1 (by rfl) ⟨4459292, by rfl⟩ : syracuseStep 5945723 = 8918585) B8918585
theorem B2013817 : Blo 519798 2013817 := bstep (se 2 (by rfl) ⟨755181, by rfl⟩ : syracuseStep 2013817 = 1510363) B1510363
theorem B2505431 : Blo 519798 2505431 := bstep (se 1 (by rfl) ⟨1879073, by rfl⟩ : syracuseStep 2505431 = 3758147) B3758147
theorem B4471595 : Blo 519798 4471595 := bstep (se 1 (by rfl) ⟨3353696, by rfl⟩ : syracuseStep 4471595 = 6707393) B6707393
theorem B703399 : Blo 519798 703399 := bstep (se 1 (by rfl) ⟨527549, by rfl⟩ : syracuseStep 703399 = 1055099) B1055099
theorem B2636711 : Blo 519798 2636711 := bstep (se 1 (by rfl) ⟨1977533, by rfl⟩ : syracuseStep 2636711 = 3955067) B3955067
theorem B69483835 : Blo 519798 69483835 := bstep (se 1 (by rfl) ⟨52112876, by rfl⟩ : syracuseStep 69483835 = 104225753) B104225753
theorem B1982015 : Blo 519798 1982015 := bstep (se 1 (by rfl) ⟨1486511, by rfl⟩ : syracuseStep 1982015 = 2973023) B2973023
theorem B6340319 : Blo 519798 6340319 := bstep (se 1 (by rfl) ⟨4755239, by rfl⟩ : syracuseStep 6340319 = 9510479) B9510479
theorem B30492197 : Blo 519798 30492197 := bstep (se 4 (by rfl) ⟨2858643, by rfl⟩ : syracuseStep 30492197 = 5717287) B5717287
theorem B6703397 : Blo 519798 6703397 := bstep (se 4 (by rfl) ⟨628443, by rfl⟩ : syracuseStep 6703397 = 1256887) B1256887
theorem B2509163 : Blo 519798 2509163 := bstep (se 1 (by rfl) ⟨1881872, by rfl⟩ : syracuseStep 2509163 = 3763745) B3763745
theorem B1755809 : Blo 519798 1755809 := bstep (se 2 (by rfl) ⟨658428, by rfl⟩ : syracuseStep 1755809 = 1316857) B1316857
theorem B8440523 : Blo 519798 8440523 := bstep (se 1 (by rfl) ⟨6330392, by rfl⟩ : syracuseStep 8440523 = 12660785) B12660785
theorem B1756025 : Blo 519798 1756025 := bstep (se 2 (by rfl) ⟨658509, by rfl⟩ : syracuseStep 1756025 = 1317019) B1317019
theorem B10144763 : Blo 519798 10144763 := bstep (se 1 (by rfl) ⟨7608572, by rfl⟩ : syracuseStep 10144763 = 15217145) B15217145
theorem B740459 : Blo 519798 740459 := bstep (se 1 (by rfl) ⟨555344, by rfl⟩ : syracuseStep 740459 = 1110689) B1110689
theorem B1757159 : Blo 519798 1757159 := bstep (se 1 (by rfl) ⟨1317869, by rfl⟩ : syracuseStep 1757159 = 2635739) B2635739
theorem B2641895 : Blo 519798 2641895 := bstep (se 1 (by rfl) ⟨1981421, by rfl⟩ : syracuseStep 2641895 = 3962843) B3962843
theorem B741359 : Blo 519798 741359 := bstep (se 1 (by rfl) ⟨556019, by rfl⟩ : syracuseStep 741359 = 1112039) B1112039
theorem B1757537 : Blo 519798 1757537 := bstep (se 2 (by rfl) ⟨659076, by rfl⟩ : syracuseStep 1757537 = 1318153) B1318153
theorem B3396107 : Blo 519798 3396107 := bstep (se 1 (by rfl) ⟨2547080, by rfl⟩ : syracuseStep 3396107 = 5094161) B5094161
theorem B15062111 : Blo 519798 15062111 := bstep (se 1 (by rfl) ⟨11296583, by rfl⟩ : syracuseStep 15062111 = 22593167) B22593167
theorem B2511967 : Blo 519798 2511967 := bstep (se 1 (by rfl) ⟨1883975, by rfl⟩ : syracuseStep 2511967 = 3767951) B3767951
theorem B1987679 : Blo 519798 1987679 := bstep (se 1 (by rfl) ⟨1490759, by rfl⟩ : syracuseStep 1987679 = 2981519) B2981519
theorem B742555 : Blo 519798 742555 := bstep (se 1 (by rfl) ⟨556916, by rfl⟩ : syracuseStep 742555 = 1113833) B1113833
theorem B1758887 : Blo 519798 1758887 := bstep (se 1 (by rfl) ⟨1319165, by rfl⟩ : syracuseStep 1758887 = 2638331) B2638331
theorem B1988347 : Blo 519798 1988347 := bstep (se 1 (by rfl) ⟨1491260, by rfl⟩ : syracuseStep 1988347 = 2982521) B2982521
theorem B2545835 : Blo 519798 2545835 := bstep (se 1 (by rfl) ⟨1909376, by rfl⟩ : syracuseStep 2545835 = 3818753) B3818753
theorem B1169747 : Blo 519798 1169747 := bstep (se 1 (by rfl) ⟨877310, by rfl⟩ : syracuseStep 1169747 = 1754621) B1754621
theorem B3562055 : Blo 519798 3562055 := bstep (se 1 (by rfl) ⟨2671541, by rfl⟩ : syracuseStep 3562055 = 5343083) B5343083
theorem B6773345 : Blo 519798 6773345 := bstep (se 2 (by rfl) ⟨2540004, by rfl⟩ : syracuseStep 6773345 = 5080009) B5080009
theorem B1170233 : Blo 519798 1170233 := bstep (se 2 (by rfl) ⟨438837, by rfl⟩ : syracuseStep 1170233 = 877675) B877675
theorem B1170287 : Blo 519798 1170287 := bstep (se 1 (by rfl) ⟨877715, by rfl⟩ : syracuseStep 1170287 = 1755431) B1755431
theorem B1760399 : Blo 519798 1760399 := bstep (se 1 (by rfl) ⟨1320299, by rfl⟩ : syracuseStep 1760399 = 2640599) B2640599
theorem B6675817 : Blo 519798 6675817 := bstep (se 2 (by rfl) ⟨2503431, by rfl⟩ : syracuseStep 6675817 = 5006863) B5006863
theorem B1170863 : Blo 519798 1170863 := bstep (se 1 (by rfl) ⟨878147, by rfl⟩ : syracuseStep 1170863 = 1756295) B1756295
theorem B2645459 : Blo 519798 2645459 := bstep (se 1 (by rfl) ⟨1984094, by rfl⟩ : syracuseStep 2645459 = 3968189) B3968189
theorem B1170935 : Blo 519798 1170935 := bstep (se 1 (by rfl) ⟨878201, by rfl⟩ : syracuseStep 1170935 = 1756403) B1756403
theorem B5660927 : Blo 519798 5660927 := bstep (se 1 (by rfl) ⟨4245695, by rfl⟩ : syracuseStep 5660927 = 8491391) B8491391
theorem B1171961 : Blo 519798 1171961 := bstep (se 2 (by rfl) ⟨439485, by rfl⟩ : syracuseStep 1171961 = 878971) B878971
theorem B1172051 : Blo 519798 1172051 := bstep (se 1 (by rfl) ⟨879038, by rfl⟩ : syracuseStep 1172051 = 1758077) B1758077
theorem B877223 : Blo 519798 877223 := bstep (se 1 (by rfl) ⟨657917, by rfl⟩ : syracuseStep 877223 = 1315835) B1315835
theorem B1172231 : Blo 519798 1172231 := bstep (se 1 (by rfl) ⟨879173, by rfl⟩ : syracuseStep 1172231 = 1758347) B1758347
theorem B1172321 : Blo 519798 1172321 := bstep (se 2 (by rfl) ⟨439620, by rfl⟩ : syracuseStep 1172321 = 879241) B879241
theorem B877547 : Blo 519798 877547 := bstep (se 1 (by rfl) ⟨658160, by rfl⟩ : syracuseStep 877547 = 1316321) B1316321
theorem B878107 : Blo 519798 878107 := bstep (se 1 (by rfl) ⟨658580, by rfl⟩ : syracuseStep 878107 = 1317161) B1317161
theorem B1173311 : Blo 519798 1173311 := bstep (se 1 (by rfl) ⟨879983, by rfl⟩ : syracuseStep 1173311 = 1759967) B1759967
theorem B2975687 : Blo 519798 2975687 := bstep (se 1 (by rfl) ⟨2231765, by rfl⟩ : syracuseStep 2975687 = 4463531) B4463531
theorem B1763315 : Blo 519798 1763315 := bstep (se 1 (by rfl) ⟨1322486, by rfl⟩ : syracuseStep 1763315 = 2644973) B2644973
theorem B780335 : Blo 519798 780335 := bstep (se 1 (by rfl) ⟨585251, by rfl⟩ : syracuseStep 780335 = 1170503) B1170503
theorem B3958955 : Blo 519798 3958955 := bstep (se 1 (by rfl) ⟨2969216, by rfl⟩ : syracuseStep 3958955 = 5938433) B5938433
theorem B780599 : Blo 519798 780599 := bstep (se 1 (by rfl) ⟨585449, by rfl⟩ : syracuseStep 780599 = 1170899) B1170899
theorem B1173815 : Blo 519798 1173815 := bstep (se 1 (by rfl) ⟨880361, by rfl⟩ : syracuseStep 1173815 = 1760723) B1760723
theorem B780779 : Blo 519798 780779 := bstep (se 1 (by rfl) ⟨585584, by rfl⟩ : syracuseStep 780779 = 1171169) B1171169
theorem B1173995 : Blo 519798 1173995 := bstep (se 1 (by rfl) ⟨880496, by rfl⟩ : syracuseStep 1173995 = 1760993) B1760993
theorem B1763855 : Blo 519798 1763855 := bstep (se 1 (by rfl) ⟨1322891, by rfl⟩ : syracuseStep 1763855 = 2645783) B2645783
theorem B3959441 : Blo 519798 3959441 := bstep (se 2 (by rfl) ⟨1484790, by rfl⟩ : syracuseStep 3959441 = 2969581) B2969581
theorem B108030955 : Blo 519798 108030955 := bstep (se 1 (by rfl) ⟨81023216, by rfl⟩ : syracuseStep 108030955 = 162046433) B162046433
theorem B781481 : Blo 519798 781481 := bstep (se 2 (by rfl) ⟨293055, by rfl⟩ : syracuseStep 781481 = 586111) B586111
theorem B1174697 : Blo 519798 1174697 := bstep (se 2 (by rfl) ⟨440511, by rfl⟩ : syracuseStep 1174697 = 881023) B881023
theorem B5958845 : Blo 519798 5958845 := bstep (se 3 (by rfl) ⟨1117283, by rfl⟩ : syracuseStep 5958845 = 2234567) B2234567
theorem B781895 : Blo 519798 781895 := bstep (se 1 (by rfl) ⟨586421, by rfl⟩ : syracuseStep 781895 = 1172843) B1172843
theorem B1175111 : Blo 519798 1175111 := bstep (se 1 (by rfl) ⟨881333, by rfl⟩ : syracuseStep 1175111 = 1762667) B1762667
theorem B1764935 : Blo 519798 1764935 := bstep (se 1 (by rfl) ⟨1323701, by rfl⟩ : syracuseStep 1764935 = 2647403) B2647403
theorem B585319 : Blo 519798 585319 := bstep (se 1 (by rfl) ⟨438989, by rfl⟩ : syracuseStep 585319 = 877979) B877979
theorem B1175183 : Blo 519798 1175183 := bstep (se 1 (by rfl) ⟨881387, by rfl⟩ : syracuseStep 1175183 = 1762775) B1762775
theorem B1175273 : Blo 519798 1175273 := bstep (se 2 (by rfl) ⟨440727, by rfl⟩ : syracuseStep 1175273 = 881455) B881455
theorem B519931 : Blo 519798 519931 := bstep (se 1 (by rfl) ⟨389948, by rfl⟩ : syracuseStep 519931 = 779897) B779897
theorem B782075 : Blo 519798 782075 := bstep (se 1 (by rfl) ⟨586556, by rfl⟩ : syracuseStep 782075 = 1173113) B1173113
theorem B1175291 : Blo 519798 1175291 := bstep (se 1 (by rfl) ⟨881468, by rfl⟩ : syracuseStep 1175291 = 1762937) B1762937
theorem B519999 : Blo 519798 519999 := bstep (se 1 (by rfl) ⟨389999, by rfl⟩ : syracuseStep 519999 = 779999) B779999
theorem B585535 : Blo 519798 585535 := bstep (se 1 (by rfl) ⟨439151, by rfl⟩ : syracuseStep 585535 = 878303) B878303
theorem B10841951 : Blo 519798 10841951 := bstep (se 1 (by rfl) ⟨8131463, by rfl⟩ : syracuseStep 10841951 = 16262927) B16262927
theorem B520063 : Blo 519798 520063 := bstep (se 1 (by rfl) ⟨390047, by rfl⟩ : syracuseStep 520063 = 780095) B780095
theorem B520175 : Blo 519798 520175 := bstep (se 1 (by rfl) ⟨390131, by rfl⟩ : syracuseStep 520175 = 780263) B780263
theorem B520187 : Blo 519798 520187 := bstep (se 1 (by rfl) ⟨390140, by rfl⟩ : syracuseStep 520187 = 780281) B780281
theorem B520255 : Blo 519798 520255 := bstep (se 1 (by rfl) ⟨390191, by rfl⟩ : syracuseStep 520255 = 780383) B780383
theorem B585823 : Blo 519798 585823 := bstep (se 1 (by rfl) ⟨439367, by rfl⟩ : syracuseStep 585823 = 878735) B878735
theorem B520295 : Blo 519798 520295 := bstep (se 1 (by rfl) ⟨390221, by rfl⟩ : syracuseStep 520295 = 780443) B780443
theorem B520319 : Blo 519798 520319 := bstep (se 1 (by rfl) ⟨390239, by rfl⟩ : syracuseStep 520319 = 780479) B780479
theorem B520347 : Blo 519798 520347 := bstep (se 1 (by rfl) ⟨390260, by rfl⟩ : syracuseStep 520347 = 780521) B780521
theorem B5009597 : Blo 519798 5009597 := bstep (se 3 (by rfl) ⟨939299, by rfl⟩ : syracuseStep 5009597 = 1878599) B1878599
theorem B520551 : Blo 519798 520551 := bstep (se 1 (by rfl) ⟨390413, by rfl⟩ : syracuseStep 520551 = 780827) B780827
theorem B520603 : Blo 519798 520603 := bstep (se 1 (by rfl) ⟨390452, by rfl⟩ : syracuseStep 520603 = 780905) B780905
theorem B782747 : Blo 519798 782747 := bstep (se 1 (by rfl) ⟨587060, by rfl⟩ : syracuseStep 782747 = 1174121) B1174121
theorem B1176299 : Blo 519798 1176299 := bstep (se 1 (by rfl) ⟨882224, by rfl⟩ : syracuseStep 1176299 = 1764449) B1764449
theorem B1766123 : Blo 519798 1766123 := bstep (se 1 (by rfl) ⟨1324592, by rfl⟩ : syracuseStep 1766123 = 2649185) B2649185
theorem B4223735 : Blo 519798 4223735 := bstep (se 1 (by rfl) ⟨3167801, by rfl⟩ : syracuseStep 4223735 = 6335603) B6335603
theorem B520955 : Blo 519798 520955 := bstep (se 1 (by rfl) ⟨390716, by rfl⟩ : syracuseStep 520955 = 781433) B781433
theorem B521023 : Blo 519798 521023 := bstep (se 1 (by rfl) ⟨390767, by rfl⟩ : syracuseStep 521023 = 781535) B781535
theorem B783167 : Blo 519798 783167 := bstep (se 1 (by rfl) ⟨587375, by rfl⟩ : syracuseStep 783167 = 1174751) B1174751
theorem B521051 : Blo 519798 521051 := bstep (se 1 (by rfl) ⟨390788, by rfl⟩ : syracuseStep 521051 = 781577) B781577
theorem B521119 : Blo 519798 521119 := bstep (se 1 (by rfl) ⟨390839, by rfl⟩ : syracuseStep 521119 = 781679) B781679
theorem B783311 : Blo 519798 783311 := bstep (se 1 (by rfl) ⟨587483, by rfl⟩ : syracuseStep 783311 = 1174967) B1174967
theorem B521199 : Blo 519798 521199 := bstep (se 1 (by rfl) ⟨390899, by rfl⟩ : syracuseStep 521199 = 781799) B781799
theorem B783353 : Blo 519798 783353 := bstep (se 2 (by rfl) ⟨293757, by rfl⟩ : syracuseStep 783353 = 587515) B587515
theorem B1176569 : Blo 519798 1176569 := bstep (se 2 (by rfl) ⟨441213, by rfl⟩ : syracuseStep 1176569 = 882427) B882427
theorem B1766393 : Blo 519798 1766393 := bstep (se 2 (by rfl) ⟨662397, by rfl⟩ : syracuseStep 1766393 = 1324795) B1324795
theorem B3961871 : Blo 519798 3961871 := bstep (se 1 (by rfl) ⟨2971403, by rfl⟩ : syracuseStep 3961871 = 5942807) B5942807
theorem B783401 : Blo 519798 783401 := bstep (se 2 (by rfl) ⟨293775, by rfl⟩ : syracuseStep 783401 = 587551) B587551
theorem B881705 : Blo 519798 881705 := bstep (se 2 (by rfl) ⟨330639, by rfl⟩ : syracuseStep 881705 = 661279) B661279
theorem B521287 : Blo 519798 521287 := bstep (se 1 (by rfl) ⟨390965, by rfl⟩ : syracuseStep 521287 = 781931) B781931
theorem B783431 : Blo 519798 783431 := bstep (se 1 (by rfl) ⟨587573, by rfl⟩ : syracuseStep 783431 = 1175147) B1175147
theorem B1176659 : Blo 519798 1176659 := bstep (se 1 (by rfl) ⟨882494, by rfl⟩ : syracuseStep 1176659 = 1764989) B1764989
theorem B521371 : Blo 519798 521371 := bstep (se 1 (by rfl) ⟨391028, by rfl⟩ : syracuseStep 521371 = 782057) B782057
theorem B521467 : Blo 519798 521467 := bstep (se 1 (by rfl) ⟨391100, by rfl⟩ : syracuseStep 521467 = 782201) B782201
theorem B783611 : Blo 519798 783611 := bstep (se 1 (by rfl) ⟨587708, by rfl⟩ : syracuseStep 783611 = 1175417) B1175417
theorem B1176839 : Blo 519798 1176839 := bstep (se 1 (by rfl) ⟨882629, by rfl⟩ : syracuseStep 1176839 = 1765259) B1765259
theorem B1766663 : Blo 519798 1766663 := bstep (se 1 (by rfl) ⟨1324997, by rfl⟩ : syracuseStep 1766663 = 2649995) B2649995
theorem B521535 : Blo 519798 521535 := bstep (se 1 (by rfl) ⟨391151, by rfl⟩ : syracuseStep 521535 = 782303) B782303
theorem B521703 : Blo 519798 521703 := bstep (se 1 (by rfl) ⟨391277, by rfl⟩ : syracuseStep 521703 = 782555) B782555
theorem B521711 : Blo 519798 521711 := bstep (se 1 (by rfl) ⟨391283, by rfl⟩ : syracuseStep 521711 = 782567) B782567
theorem B521819 : Blo 519798 521819 := bstep (se 1 (by rfl) ⟨391364, by rfl⟩ : syracuseStep 521819 = 782729) B782729
theorem B1177199 : Blo 519798 1177199 := bstep (se 1 (by rfl) ⟨882899, by rfl⟩ : syracuseStep 1177199 = 1765799) B1765799
theorem B882319 : Blo 519798 882319 := bstep (se 1 (by rfl) ⟨661739, by rfl⟩ : syracuseStep 882319 = 1323479) B1323479
theorem B521883 : Blo 519798 521883 := bstep (se 1 (by rfl) ⟨391412, by rfl⟩ : syracuseStep 521883 = 782825) B782825
theorem B521967 : Blo 519798 521967 := bstep (se 1 (by rfl) ⟨391475, by rfl⟩ : syracuseStep 521967 = 782951) B782951
theorem B2029369 : Blo 519798 2029369 := bstep (se 2 (by rfl) ⟨761013, by rfl⟩ : syracuseStep 2029369 = 1522027) B1522027
theorem B522055 : Blo 519798 522055 := bstep (se 1 (by rfl) ⟨391541, by rfl⟩ : syracuseStep 522055 = 783083) B783083
theorem B522075 : Blo 519798 522075 := bstep (se 1 (by rfl) ⟨391556, by rfl⟩ : syracuseStep 522075 = 783113) B783113
theorem B522143 : Blo 519798 522143 := bstep (se 1 (by rfl) ⟨391607, by rfl⟩ : syracuseStep 522143 = 783215) B783215
theorem B522311 : Blo 519798 522311 := bstep (se 1 (by rfl) ⟨391733, by rfl⟩ : syracuseStep 522311 = 783467) B783467
theorem B1767635 : Blo 519798 1767635 := bstep (se 1 (by rfl) ⟨1325726, by rfl⟩ : syracuseStep 1767635 = 2651453) B2651453
theorem B522471 : Blo 519798 522471 := bstep (se 1 (by rfl) ⟨391853, by rfl⟩ : syracuseStep 522471 = 783707) B783707
theorem B522655 : Blo 519798 522655 := bstep (se 1 (by rfl) ⟨391991, by rfl⟩ : syracuseStep 522655 = 783983) B783983
theorem B3963329 : Blo 519798 3963329 := bstep (se 2 (by rfl) ⟨1486248, by rfl⟩ : syracuseStep 3963329 = 2972497) B2972497
theorem B522703 : Blo 519798 522703 := bstep (se 1 (by rfl) ⟨392027, by rfl⟩ : syracuseStep 522703 = 784055) B784055
theorem B784847 : Blo 519798 784847 := bstep (se 1 (by rfl) ⟨588635, by rfl⟩ : syracuseStep 784847 = 1177271) B1177271
theorem B1178063 : Blo 519798 1178063 := bstep (se 1 (by rfl) ⟨883547, by rfl⟩ : syracuseStep 1178063 = 1767095) B1767095
theorem B522727 : Blo 519798 522727 := bstep (se 1 (by rfl) ⟨392045, by rfl⟩ : syracuseStep 522727 = 784091) B784091
theorem B5896709 : Blo 519798 5896709 := bstep (se 4 (by rfl) ⟨552816, by rfl⟩ : syracuseStep 5896709 = 1105633) B1105633
theorem B1669673 : Blo 519798 1669673 := bstep (se 2 (by rfl) ⟨626127, by rfl⟩ : syracuseStep 1669673 = 1252255) B1252255
theorem B784937 : Blo 519798 784937 := bstep (se 2 (by rfl) ⟨294351, by rfl⟩ : syracuseStep 784937 = 588703) B588703
theorem B1178153 : Blo 519798 1178153 := bstep (se 2 (by rfl) ⟨441807, by rfl⟩ : syracuseStep 1178153 = 883615) B883615
theorem B522843 : Blo 519798 522843 := bstep (se 1 (by rfl) ⟨392132, by rfl⟩ : syracuseStep 522843 = 784265) B784265
theorem B588379 : Blo 519798 588379 := bstep (se 1 (by rfl) ⟨441284, by rfl⟩ : syracuseStep 588379 = 882569) B882569
theorem B883291 : Blo 519798 883291 := bstep (se 1 (by rfl) ⟨662468, by rfl⟩ : syracuseStep 883291 = 1324937) B1324937
theorem B2226845 : Blo 519798 2226845 := bstep (se 3 (by rfl) ⟨417533, by rfl⟩ : syracuseStep 2226845 = 835067) B835067
theorem B522911 : Blo 519798 522911 := bstep (se 1 (by rfl) ⟨392183, by rfl⟩ : syracuseStep 522911 = 784367) B784367
theorem B785129 : Blo 519798 785129 := bstep (se 2 (by rfl) ⟨294423, by rfl⟩ : syracuseStep 785129 = 588847) B588847
theorem B883433 : Blo 519798 883433 := bstep (se 2 (by rfl) ⟨331287, by rfl⟩ : syracuseStep 883433 = 662575) B662575
theorem B523079 : Blo 519798 523079 := bstep (se 1 (by rfl) ⟨392309, by rfl⟩ : syracuseStep 523079 = 784619) B784619
theorem B523119 : Blo 519798 523119 := bstep (se 1 (by rfl) ⟨392339, by rfl⟩ : syracuseStep 523119 = 784679) B784679
theorem B588667 : Blo 519798 588667 := bstep (se 1 (by rfl) ⟨441500, by rfl⟩ : syracuseStep 588667 = 883001) B883001
theorem B2063261 : Blo 519798 2063261 := bstep (se 3 (by rfl) ⟨386861, by rfl⟩ : syracuseStep 2063261 = 773723) B773723
theorem B523175 : Blo 519798 523175 := bstep (se 1 (by rfl) ⟨392381, by rfl⟩ : syracuseStep 523175 = 784763) B784763
theorem B4815949 : Blo 519798 4815949 := bstep (se 3 (by rfl) ⟨902990, by rfl⟩ : syracuseStep 4815949 = 1805981) B1805981
theorem B523355 : Blo 519798 523355 := bstep (se 1 (by rfl) ⟨392516, by rfl⟩ : syracuseStep 523355 = 785033) B785033
theorem B785513 : Blo 519798 785513 := bstep (se 2 (by rfl) ⟨294567, by rfl⟩ : syracuseStep 785513 = 589135) B589135
theorem B523471 : Blo 519798 523471 := bstep (se 1 (by rfl) ⟨392603, by rfl⟩ : syracuseStep 523471 = 785207) B785207
theorem B523495 : Blo 519798 523495 := bstep (se 1 (by rfl) ⟨392621, by rfl⟩ : syracuseStep 523495 = 785243) B785243
theorem B785639 : Blo 519798 785639 := bstep (se 1 (by rfl) ⟨589229, by rfl⟩ : syracuseStep 785639 = 1178459) B1178459
theorem B523591 : Blo 519798 523591 := bstep (se 1 (by rfl) ⟨392693, by rfl⟩ : syracuseStep 523591 = 785387) B785387
theorem B523727 : Blo 519798 523727 := bstep (se 1 (by rfl) ⟨392795, by rfl⟩ : syracuseStep 523727 = 785591) B785591
theorem B556831 : Blo 519798 556831 := bstep (se 1 (by rfl) ⟨417623, by rfl⟩ : syracuseStep 556831 = 835247) B835247
theorem B9994043 : Blo 519798 9994043 := bstep (se 1 (by rfl) ⟨7495532, by rfl⟩ : syracuseStep 9994043 = 14991065) B14991065
theorem B278822807 : Blo 519798 278822807 := bstep (se 1 (by rfl) ⟨209117105, by rfl⟩ : syracuseStep 278822807 = 418234211) B418234211
theorem B12059603 : Blo 519798 12059603 := bstep (se 1 (by rfl) ⟨9044702, by rfl⟩ : syracuseStep 12059603 = 18089405) B18089405
theorem B2851969 : Blo 519798 2851969 := bstep (se 2 (by rfl) ⟨1069488, by rfl⟩ : syracuseStep 2851969 = 2138977) B2138977
theorem B1672775 : Blo 519798 1672775 := bstep (se 1 (by rfl) ⟨1254581, by rfl⟩ : syracuseStep 1672775 = 2509163) B2509163
theorem B1674209 : Blo 519798 1674209 := bstep (se 2 (by rfl) ⟨627828, by rfl⟩ : syracuseStep 1674209 = 1255657) B1255657
theorem B6033599 : Blo 519798 6033599 := bstep (se 1 (by rfl) ⟨4525199, by rfl⟩ : syracuseStep 6033599 = 9050399) B9050399
theorem B5640515 : Blo 519798 5640515 := bstep (se 1 (by rfl) ⟨4230386, by rfl⟩ : syracuseStep 5640515 = 8460773) B8460773
theorem B1053931 : Blo 519798 1053931 := bstep (se 1 (by rfl) ⟨790448, by rfl⟩ : syracuseStep 1053931 = 1580897) B1580897
theorem B1316159 : Blo 519798 1316159 := bstep (se 1 (by rfl) ⟨987119, by rfl⟩ : syracuseStep 1316159 = 1974239) B1974239
theorem B3773951 : Blo 519798 3773951 := bstep (se 1 (by rfl) ⟨2830463, by rfl⟩ : syracuseStep 3773951 = 5660927) B5660927
theorem B6788893 : Blo 519798 6788893 := bstep (se 3 (by rfl) ⟨1272917, by rfl⟩ : syracuseStep 6788893 = 2545835) B2545835
theorem B1316807 : Blo 519798 1316807 := bstep (se 1 (by rfl) ⟨987605, by rfl⟩ : syracuseStep 1316807 = 1975211) B1975211
theorem B793039 : Blo 519798 793039 := bstep (se 1 (by rfl) ⟨594779, by rfl⟩ : syracuseStep 793039 = 1189559) B1189559
theorem B1317505 : Blo 519798 1317505 := bstep (se 2 (by rfl) ⟨494064, by rfl⟩ : syracuseStep 1317505 = 988129) B988129
theorem B3349289 : Blo 519798 3349289 := bstep (se 2 (by rfl) ⟨1255983, by rfl⟩ : syracuseStep 3349289 = 2511967) B2511967
theorem B990073 : Blo 519798 990073 := bstep (se 2 (by rfl) ⟨371277, by rfl⟩ : syracuseStep 990073 = 742555) B742555
theorem B370580453 : Blo 519798 370580453 := bstep (se 4 (by rfl) ⟨34741917, by rfl⟩ : syracuseStep 370580453 = 69483835) B69483835
theorem B1318315 : Blo 519798 1318315 := bstep (se 1 (by rfl) ⟨988736, by rfl⟩ : syracuseStep 1318315 = 1977473) B1977473
theorem B3972563 : Blo 519798 3972563 := bstep (se 1 (by rfl) ⟨2979422, by rfl⟩ : syracuseStep 3972563 = 5958845) B5958845
theorem B5709403 : Blo 519798 5709403 := bstep (se 1 (by rfl) ⟨4282052, by rfl⟩ : syracuseStep 5709403 = 8564105) B8564105
theorem B1974041 : Blo 519798 1974041 := bstep (se 2 (by rfl) ⟨740265, by rfl⟩ : syracuseStep 1974041 = 1480531) B1480531
theorem B1974557 : Blo 519798 1974557 := bstep (se 3 (by rfl) ⟨370229, by rfl⟩ : syracuseStep 1974557 = 740459) B740459
theorem B3350879 : Blo 519798 3350879 := bstep (se 1 (by rfl) ⟨2513159, by rfl⟩ : syracuseStep 3350879 = 5026319) B5026319
theorem B991615 : Blo 519798 991615 := bstep (se 1 (by rfl) ⟨743711, by rfl⟩ : syracuseStep 991615 = 1487423) B1487423
theorem B1974739 : Blo 519798 1974739 := bstep (se 1 (by rfl) ⟨1481054, by rfl⟩ : syracuseStep 1974739 = 2962109) B2962109
theorem B1057321 : Blo 519798 1057321 := bstep (se 2 (by rfl) ⟨396495, by rfl⟩ : syracuseStep 1057321 = 792991) B792991
theorem B991835 : Blo 519798 991835 := bstep (se 1 (by rfl) ⟨743876, by rfl⟩ : syracuseStep 991835 = 1487753) B1487753
theorem B1319561 : Blo 519798 1319561 := bstep (se 2 (by rfl) ⟨494835, by rfl⟩ : syracuseStep 1319561 = 989671) B989671
theorem B4006567 : Blo 519798 4006567 := bstep (se 1 (by rfl) ⟨3004925, by rfl⟩ : syracuseStep 4006567 = 6009851) B6009851
theorem B1319591 : Blo 519798 1319591 := bstep (se 1 (by rfl) ⟨989693, by rfl⟩ : syracuseStep 1319591 = 1979387) B1979387
theorem B992351 : Blo 519798 992351 := bstep (se 1 (by rfl) ⟨744263, by rfl⟩ : syracuseStep 992351 = 1488527) B1488527
theorem B1484563 : Blo 519798 1484563 := bstep (se 1 (by rfl) ⟨1113422, by rfl⟩ : syracuseStep 1484563 = 2226845) B2226845
theorem B2631689 : Blo 519798 2631689 := bstep (se 2 (by rfl) ⟨986883, by rfl⟩ : syracuseStep 2631689 = 1973767) B1973767
theorem B1321343 : Blo 519798 1321343 := bstep (se 1 (by rfl) ⟨991007, by rfl⟩ : syracuseStep 1321343 = 1982015) B1982015
theorem B6662695 : Blo 519798 6662695 := bstep (se 1 (by rfl) ⟨4997021, by rfl⟩ : syracuseStep 6662695 = 9994043) B9994043
theorem B1976957 : Blo 519798 1976957 := bstep (se 3 (by rfl) ⟨370679, by rfl⟩ : syracuseStep 1976957 = 741359) B741359
theorem B1977169 : Blo 519798 1977169 := bstep (se 2 (by rfl) ⟨741438, by rfl⟩ : syracuseStep 1977169 = 1482877) B1482877
theorem B12889151 : Blo 519798 12889151 := bstep (se 1 (by rfl) ⟨9666863, by rfl⟩ : syracuseStep 12889151 = 19333727) B19333727
theorem B20328131 : Blo 519798 20328131 := bstep (se 1 (by rfl) ⟨15246098, by rfl⟩ : syracuseStep 20328131 = 30492197) B30492197
theorem B3354493 : Blo 519798 3354493 := bstep (se 3 (by rfl) ⟨628967, by rfl⟩ : syracuseStep 3354493 = 1257935) B1257935
theorem B5418971 : Blo 519798 5418971 := bstep (se 1 (by rfl) ⟨4064228, by rfl⟩ : syracuseStep 5418971 = 8128457) B8128457
theorem B9056285 : Blo 519798 9056285 := bstep (se 3 (by rfl) ⟨1698053, by rfl⟩ : syracuseStep 9056285 = 3396107) B3396107
theorem B4468931 : Blo 519798 4468931 := bstep (se 1 (by rfl) ⟨3351698, by rfl⟩ : syracuseStep 4468931 = 6703397) B6703397
theorem B6763175 : Blo 519798 6763175 := bstep (se 1 (by rfl) ⟨5072381, by rfl⟩ : syracuseStep 6763175 = 10144763) B10144763
theorem B5026819 : Blo 519798 5026819 := bstep (se 1 (by rfl) ⟨3770114, by rfl⟩ : syracuseStep 5026819 = 7540229) B7540229
theorem B11285513 : Blo 519798 11285513 := bstep (se 2 (by rfl) ⟨4232067, by rfl⟩ : syracuseStep 11285513 = 8464135) B8464135
theorem B832889 : Blo 519798 832889 := bstep (se 2 (by rfl) ⟨312333, by rfl⟩ : syracuseStep 832889 = 624667) B624667
theorem B1979873 : Blo 519798 1979873 := bstep (se 2 (by rfl) ⟨742452, by rfl⟩ : syracuseStep 1979873 = 1484905) B1484905
theorem B10041407 : Blo 519798 10041407 := bstep (se 1 (by rfl) ⟨7531055, by rfl⟩ : syracuseStep 10041407 = 15062111) B15062111
theorem B1325119 : Blo 519798 1325119 := bstep (se 1 (by rfl) ⟨993839, by rfl⟩ : syracuseStep 1325119 = 1987679) B1987679
theorem B2374703 : Blo 519798 2374703 := bstep (se 1 (by rfl) ⟨1781027, by rfl⟩ : syracuseStep 2374703 = 3562055) B3562055
theorem B2636873 : Blo 519798 2636873 := bstep (se 2 (by rfl) ⟨988827, by rfl⟩ : syracuseStep 2636873 = 1977655) B1977655
theorem B18988253 : Blo 519798 18988253 := bstep (se 3 (by rfl) ⟨3560297, by rfl⟩ : syracuseStep 18988253 = 7120595) B7120595
theorem B12729673 : Blo 519798 12729673 := bstep (se 2 (by rfl) ⟨4773627, by rfl⟩ : syracuseStep 12729673 = 9547255) B9547255
theorem B835753 : Blo 519798 835753 := bstep (se 2 (by rfl) ⟨313407, by rfl⟩ : syracuseStep 835753 = 626815) B626815
theorem B8896715 : Blo 519798 8896715 := bstep (se 1 (by rfl) ⟨6672536, by rfl⟩ : syracuseStep 8896715 = 13345073) B13345073
theorem B4243751 : Blo 519798 4243751 := bstep (se 1 (by rfl) ⟨3182813, by rfl⟩ : syracuseStep 4243751 = 6365627) B6365627
theorem B4244071 : Blo 519798 4244071 := bstep (se 1 (by rfl) ⟨3183053, by rfl⟩ : syracuseStep 4244071 = 6366107) B6366107
theorem B1983791 : Blo 519798 1983791 := bstep (se 1 (by rfl) ⟨1487843, by rfl⟩ : syracuseStep 1983791 = 2975687) B2975687
theorem B2639303 : Blo 519798 2639303 := bstep (se 1 (by rfl) ⟨1979477, by rfl⟩ : syracuseStep 2639303 = 3958955) B3958955
theorem B1754729 : Blo 519798 1754729 := bstep (se 2 (by rfl) ⟨658023, by rfl⟩ : syracuseStep 1754729 = 1316047) B1316047
theorem B2639627 : Blo 519798 2639627 := bstep (se 1 (by rfl) ⟨1979720, by rfl⟩ : syracuseStep 2639627 = 3959441) B3959441
theorem B33736661 : Blo 519798 33736661 := bstep (se 7 (by rfl) ⟨395351, by rfl⟩ : syracuseStep 33736661 = 790703) B790703
theorem B2148457 : Blo 519798 2148457 := bstep (se 2 (by rfl) ⟨805671, by rfl⟩ : syracuseStep 2148457 = 1611343) B1611343
theorem B2705825 : Blo 519798 2705825 := bstep (se 2 (by rfl) ⟨1014684, by rfl⟩ : syracuseStep 2705825 = 2029369) B2029369
theorem B7227967 : Blo 519798 7227967 := bstep (se 1 (by rfl) ⟨5420975, by rfl⟩ : syracuseStep 7227967 = 10841951) B10841951
theorem B5950097 : Blo 519798 5950097 := bstep (se 2 (by rfl) ⟨2231286, by rfl⟩ : syracuseStep 5950097 = 4462573) B4462573
theorem B2607839 : Blo 519798 2607839 := bstep (se 1 (by rfl) ⟨1955879, by rfl⟩ : syracuseStep 2607839 = 3911759) B3911759
theorem B1985249 : Blo 519798 1985249 := bstep (se 2 (by rfl) ⟨744468, by rfl⟩ : syracuseStep 1985249 = 1488937) B1488937
theorem B3853175 : Blo 519798 3853175 := bstep (se 1 (by rfl) ⟨2889881, by rfl⟩ : syracuseStep 3853175 = 5779763) B5779763
theorem B2640761 : Blo 519798 2640761 := bstep (se 2 (by rfl) ⟨990285, by rfl⟩ : syracuseStep 2640761 = 1980571) B1980571
theorem B2641247 : Blo 519798 2641247 := bstep (se 1 (by rfl) ⟨1980935, by rfl⟩ : syracuseStep 2641247 = 3961871) B3961871
theorem B10735415 : Blo 519798 10735415 := bstep (se 1 (by rfl) ⟨8051561, by rfl⟩ : syracuseStep 10735415 = 16103123) B16103123
theorem B937865 : Blo 519798 937865 := bstep (se 2 (by rfl) ⟨351699, by rfl⟩ : syracuseStep 937865 = 703399) B703399
theorem B5033927 : Blo 519798 5033927 := bstep (se 1 (by rfl) ⟨3775445, by rfl⟩ : syracuseStep 5033927 = 7550891) B7550891
theorem B2642219 : Blo 519798 2642219 := bstep (se 1 (by rfl) ⟨1981664, by rfl⟩ : syracuseStep 2642219 = 3963329) B3963329
theorem B8901089 : Blo 519798 8901089 := bstep (se 2 (by rfl) ⟨3337908, by rfl⟩ : syracuseStep 8901089 = 6675817) B6675817
theorem B1757807 : Blo 519798 1757807 := bstep (se 1 (by rfl) ⟨1318355, by rfl⟩ : syracuseStep 1757807 = 2636711) B2636711
theorem B742441 : Blo 519798 742441 := bstep (se 2 (by rfl) ⟨278415, by rfl⟩ : syracuseStep 742441 = 556831) B556831
theorem B185881871 : Blo 519798 185881871 := bstep (se 1 (by rfl) ⟨139411403, by rfl⟩ : syracuseStep 185881871 = 278822807) B278822807
theorem B2643515 : Blo 519798 2643515 := bstep (se 1 (by rfl) ⟨1982636, by rfl⟩ : syracuseStep 2643515 = 3965273) B3965273
theorem B3759043 : Blo 519798 3759043 := bstep (se 1 (by rfl) ⟨2819282, by rfl⟩ : syracuseStep 3759043 = 5638565) B5638565
theorem B5004251 : Blo 519798 5004251 := bstep (se 1 (by rfl) ⟨3753188, by rfl⟩ : syracuseStep 5004251 = 7506377) B7506377
theorem B1170539 : Blo 519798 1170539 := bstep (se 1 (by rfl) ⟨877904, by rfl⟩ : syracuseStep 1170539 = 1755809) B1755809
theorem B5627015 : Blo 519798 5627015 := bstep (se 1 (by rfl) ⟨4220261, by rfl⟩ : syracuseStep 5627015 = 8440523) B8440523
theorem B2645135 : Blo 519798 2645135 := bstep (se 1 (by rfl) ⟨1983851, by rfl⟩ : syracuseStep 2645135 = 3967703) B3967703
theorem B1170683 : Blo 519798 1170683 := bstep (se 1 (by rfl) ⟨878012, by rfl⟩ : syracuseStep 1170683 = 1756025) B1756025
theorem B1170809 : Blo 519798 1170809 := bstep (se 2 (by rfl) ⟨439053, by rfl⟩ : syracuseStep 1170809 = 878107) B878107
theorem B1171439 : Blo 519798 1171439 := bstep (se 1 (by rfl) ⟨878579, by rfl⟩ : syracuseStep 1171439 = 1757159) B1757159
theorem B1761263 : Blo 519798 1761263 := bstep (se 1 (by rfl) ⟨1320947, by rfl⟩ : syracuseStep 1761263 = 2641895) B2641895
theorem B1171691 : Blo 519798 1171691 := bstep (se 1 (by rfl) ⟨878768, by rfl⟩ : syracuseStep 1171691 = 1757537) B1757537
theorem B1761533 : Blo 519798 1761533 := bstep (se 3 (by rfl) ⟨330287, by rfl⟩ : syracuseStep 1761533 = 660575) B660575
theorem B877243 : Blo 519798 877243 := bstep (se 1 (by rfl) ⟨657932, by rfl⟩ : syracuseStep 877243 = 1315865) B1315865
theorem B1762073 : Blo 519798 1762073 := bstep (se 2 (by rfl) ⟨660777, by rfl⟩ : syracuseStep 1762073 = 1321555) B1321555
theorem B1172591 : Blo 519798 1172591 := bstep (se 1 (by rfl) ⟨879443, by rfl⟩ : syracuseStep 1172591 = 1758887) B1758887
theorem B144041273 : Blo 519798 144041273 := bstep (se 2 (by rfl) ⟨54015477, by rfl⟩ : syracuseStep 144041273 = 108030955) B108030955
theorem B779831 : Blo 519798 779831 := bstep (se 1 (by rfl) ⟨584873, by rfl⟩ : syracuseStep 779831 = 1169747) B1169747
theorem B4515563 : Blo 519798 4515563 := bstep (se 1 (by rfl) ⟨3386672, by rfl⟩ : syracuseStep 4515563 = 6773345) B6773345
theorem B780155 : Blo 519798 780155 := bstep (se 1 (by rfl) ⟨585116, by rfl⟩ : syracuseStep 780155 = 1170233) B1170233
theorem B780191 : Blo 519798 780191 := bstep (se 1 (by rfl) ⟨585143, by rfl⟩ : syracuseStep 780191 = 1170287) B1170287
theorem B2648051 : Blo 519798 2648051 := bstep (se 1 (by rfl) ⟨1986038, by rfl⟩ : syracuseStep 2648051 = 3972077) B3972077
theorem B1173599 : Blo 519798 1173599 := bstep (se 1 (by rfl) ⟨880199, by rfl⟩ : syracuseStep 1173599 = 1760399) B1760399
theorem B780425 : Blo 519798 780425 := bstep (se 2 (by rfl) ⟨292659, by rfl⟩ : syracuseStep 780425 = 585319) B585319
theorem B780575 : Blo 519798 780575 := bstep (se 1 (by rfl) ⟨585431, by rfl⟩ : syracuseStep 780575 = 1170863) B1170863
theorem B1763639 : Blo 519798 1763639 := bstep (se 1 (by rfl) ⟨1322729, by rfl⟩ : syracuseStep 1763639 = 2645459) B2645459
theorem B780623 : Blo 519798 780623 := bstep (se 1 (by rfl) ⟨585467, by rfl⟩ : syracuseStep 780623 = 1170935) B1170935
theorem B780713 : Blo 519798 780713 := bstep (se 2 (by rfl) ⟨292767, by rfl⟩ : syracuseStep 780713 = 585535) B585535
theorem B879079 : Blo 519798 879079 := bstep (se 1 (by rfl) ⟨659309, by rfl⟩ : syracuseStep 879079 = 1318619) B1318619
theorem B781097 : Blo 519798 781097 := bstep (se 2 (by rfl) ⟨292911, by rfl⟩ : syracuseStep 781097 = 585823) B585823
theorem B781307 : Blo 519798 781307 := bstep (se 1 (by rfl) ⟨585980, by rfl⟩ : syracuseStep 781307 = 1171961) B1171961
theorem B781367 : Blo 519798 781367 := bstep (se 1 (by rfl) ⟨586025, by rfl⟩ : syracuseStep 781367 = 1172051) B1172051
theorem B584815 : Blo 519798 584815 := bstep (se 1 (by rfl) ⟨438611, by rfl⟩ : syracuseStep 584815 = 877223) B877223
theorem B781487 : Blo 519798 781487 := bstep (se 1 (by rfl) ⟨586115, by rfl⟩ : syracuseStep 781487 = 1172231) B1172231
theorem B781547 : Blo 519798 781547 := bstep (se 1 (by rfl) ⟨586160, by rfl⟩ : syracuseStep 781547 = 1172321) B1172321
theorem B585031 : Blo 519798 585031 := bstep (se 1 (by rfl) ⟨438773, by rfl⟩ : syracuseStep 585031 = 877547) B877547
theorem B2649671 : Blo 519798 2649671 := bstep (se 1 (by rfl) ⟨1987253, by rfl⟩ : syracuseStep 2649671 = 3974507) B3974507
theorem B8580809 : Blo 519798 8580809 := bstep (se 2 (by rfl) ⟨3217803, by rfl⟩ : syracuseStep 8580809 = 6435607) B6435607
theorem B1765097 : Blo 519798 1765097 := bstep (se 2 (by rfl) ⟨661911, by rfl⟩ : syracuseStep 1765097 = 1323823) B1323823
theorem B782207 : Blo 519798 782207 := bstep (se 1 (by rfl) ⟨586655, by rfl⟩ : syracuseStep 782207 = 1173311) B1173311
theorem B1175543 : Blo 519798 1175543 := bstep (se 1 (by rfl) ⟨881657, by rfl⟩ : syracuseStep 1175543 = 1763315) B1763315
theorem B520223 : Blo 519798 520223 := bstep (se 1 (by rfl) ⟨390167, by rfl⟩ : syracuseStep 520223 = 780335) B780335
theorem B520399 : Blo 519798 520399 := bstep (se 1 (by rfl) ⟨390299, by rfl⟩ : syracuseStep 520399 = 780599) B780599
theorem B782543 : Blo 519798 782543 := bstep (se 1 (by rfl) ⟨586907, by rfl⟩ : syracuseStep 782543 = 1173815) B1173815
theorem B2650319 : Blo 519798 2650319 := bstep (se 1 (by rfl) ⟨1987739, by rfl⟩ : syracuseStep 2650319 = 3975479) B3975479
theorem B520519 : Blo 519798 520519 := bstep (se 1 (by rfl) ⟨390389, by rfl⟩ : syracuseStep 520519 = 780779) B780779
theorem B782663 : Blo 519798 782663 := bstep (se 1 (by rfl) ⟨586997, by rfl⟩ : syracuseStep 782663 = 1173995) B1173995
theorem B1175903 : Blo 519798 1175903 := bstep (se 1 (by rfl) ⟨881927, by rfl⟩ : syracuseStep 1175903 = 1763855) B1763855
theorem B6681149 : Blo 519798 6681149 := bstep (se 3 (by rfl) ⟨1252715, by rfl⟩ : syracuseStep 6681149 = 2505431) B2505431
theorem B520987 : Blo 519798 520987 := bstep (se 1 (by rfl) ⟨390740, by rfl⟩ : syracuseStep 520987 = 781481) B781481
theorem B783131 : Blo 519798 783131 := bstep (se 1 (by rfl) ⟨587348, by rfl⟩ : syracuseStep 783131 = 1174697) B1174697
theorem B1176425 : Blo 519798 1176425 := bstep (se 2 (by rfl) ⟨441159, by rfl⟩ : syracuseStep 1176425 = 882319) B882319
theorem B2651129 : Blo 519798 2651129 := bstep (se 2 (by rfl) ⟨994173, by rfl⟩ : syracuseStep 2651129 = 1988347) B1988347
theorem B521263 : Blo 519798 521263 := bstep (se 1 (by rfl) ⟨390947, by rfl⟩ : syracuseStep 521263 = 781895) B781895
theorem B783407 : Blo 519798 783407 := bstep (se 1 (by rfl) ⟨587555, by rfl⟩ : syracuseStep 783407 = 1175111) B1175111
theorem B1176623 : Blo 519798 1176623 := bstep (se 1 (by rfl) ⟨882467, by rfl⟩ : syracuseStep 1176623 = 1764935) B1764935
theorem B881759 : Blo 519798 881759 := bstep (se 1 (by rfl) ⟨661319, by rfl⟩ : syracuseStep 881759 = 1322639) B1322639
theorem B783455 : Blo 519798 783455 := bstep (se 1 (by rfl) ⟨587591, by rfl⟩ : syracuseStep 783455 = 1175183) B1175183
theorem B783515 : Blo 519798 783515 := bstep (se 1 (by rfl) ⟨587636, by rfl⟩ : syracuseStep 783515 = 1175273) B1175273
theorem B2651291 : Blo 519798 2651291 := bstep (se 1 (by rfl) ⟨1988468, by rfl⟩ : syracuseStep 2651291 = 3976937) B3976937
theorem B521383 : Blo 519798 521383 := bstep (se 1 (by rfl) ⟨391037, by rfl⟩ : syracuseStep 521383 = 782075) B782075
theorem B783527 : Blo 519798 783527 := bstep (se 1 (by rfl) ⟨587645, by rfl⟩ : syracuseStep 783527 = 1175291) B1175291
theorem B3339731 : Blo 519798 3339731 := bstep (se 1 (by rfl) ⟨2504798, by rfl⟩ : syracuseStep 3339731 = 5009597) B5009597
theorem B521831 : Blo 519798 521831 := bstep (se 1 (by rfl) ⟨391373, by rfl⟩ : syracuseStep 521831 = 782747) B782747
theorem B784199 : Blo 519798 784199 := bstep (se 1 (by rfl) ⟨588149, by rfl⟩ : syracuseStep 784199 = 1176299) B1176299
theorem B1177415 : Blo 519798 1177415 := bstep (se 1 (by rfl) ⟨883061, by rfl⟩ : syracuseStep 1177415 = 1766123) B1766123
theorem B2815823 : Blo 519798 2815823 := bstep (se 1 (by rfl) ⟨2111867, by rfl⟩ : syracuseStep 2815823 = 4223735) B4223735
theorem B522111 : Blo 519798 522111 := bstep (se 1 (by rfl) ⟨391583, by rfl⟩ : syracuseStep 522111 = 783167) B783167
theorem B522207 : Blo 519798 522207 := bstep (se 1 (by rfl) ⟨391655, by rfl⟩ : syracuseStep 522207 = 783311) B783311
theorem B522235 : Blo 519798 522235 := bstep (se 1 (by rfl) ⟨391676, by rfl⟩ : syracuseStep 522235 = 783353) B783353
theorem B784379 : Blo 519798 784379 := bstep (se 1 (by rfl) ⟨588284, by rfl⟩ : syracuseStep 784379 = 1176569) B1176569
theorem B1177595 : Blo 519798 1177595 := bstep (se 1 (by rfl) ⟨883196, by rfl⟩ : syracuseStep 1177595 = 1766393) B1766393
theorem B522267 : Blo 519798 522267 := bstep (se 1 (by rfl) ⟨391700, by rfl⟩ : syracuseStep 522267 = 783401) B783401
theorem B587803 : Blo 519798 587803 := bstep (se 1 (by rfl) ⟨440852, by rfl⟩ : syracuseStep 587803 = 881705) B881705
theorem B522287 : Blo 519798 522287 := bstep (se 1 (by rfl) ⟨391715, by rfl⟩ : syracuseStep 522287 = 783431) B783431
theorem B784439 : Blo 519798 784439 := bstep (se 1 (by rfl) ⟨588329, by rfl⟩ : syracuseStep 784439 = 1176659) B1176659
theorem B784505 : Blo 519798 784505 := bstep (se 2 (by rfl) ⟨294189, by rfl⟩ : syracuseStep 784505 = 588379) B588379
theorem B1177721 : Blo 519798 1177721 := bstep (se 2 (by rfl) ⟨441645, by rfl⟩ : syracuseStep 1177721 = 883291) B883291
theorem B2685089 : Blo 519798 2685089 := bstep (se 2 (by rfl) ⟨1006908, by rfl⟩ : syracuseStep 2685089 = 2013817) B2013817
theorem B522407 : Blo 519798 522407 := bstep (se 1 (by rfl) ⟨391805, by rfl⟩ : syracuseStep 522407 = 783611) B783611
theorem B784559 : Blo 519798 784559 := bstep (se 1 (by rfl) ⟨588419, by rfl⟩ : syracuseStep 784559 = 1176839) B1176839
theorem B1177775 : Blo 519798 1177775 := bstep (se 1 (by rfl) ⟨883331, by rfl⟩ : syracuseStep 1177775 = 1766663) B1766663
theorem B784799 : Blo 519798 784799 := bstep (se 1 (by rfl) ⟨588599, by rfl⟩ : syracuseStep 784799 = 1177199) B1177199
theorem B784889 : Blo 519798 784889 := bstep (se 2 (by rfl) ⟨294333, by rfl⟩ : syracuseStep 784889 = 588667) B588667
theorem B6421265 : Blo 519798 6421265 := bstep (se 2 (by rfl) ⟨2407974, by rfl⟩ : syracuseStep 6421265 = 4815949) B4815949
theorem B1178423 : Blo 519798 1178423 := bstep (se 1 (by rfl) ⟨883817, by rfl⟩ : syracuseStep 1178423 = 1767635) B1767635
theorem B3963815 : Blo 519798 3963815 := bstep (se 1 (by rfl) ⟨2972861, by rfl⟩ : syracuseStep 3963815 = 5945723) B5945723
theorem B523231 : Blo 519798 523231 := bstep (se 1 (by rfl) ⟨392423, by rfl⟩ : syracuseStep 523231 = 784847) B784847
theorem B785375 : Blo 519798 785375 := bstep (se 1 (by rfl) ⟨589031, by rfl⟩ : syracuseStep 785375 = 1178063) B1178063
theorem B3931139 : Blo 519798 3931139 := bstep (se 1 (by rfl) ⟨2948354, by rfl⟩ : syracuseStep 3931139 = 5896709) B5896709
theorem B1113115 : Blo 519798 1113115 := bstep (se 1 (by rfl) ⟨834836, by rfl⟩ : syracuseStep 1113115 = 1669673) B1669673
theorem B523291 : Blo 519798 523291 := bstep (se 1 (by rfl) ⟨392468, by rfl⟩ : syracuseStep 523291 = 784937) B784937
theorem B785435 : Blo 519798 785435 := bstep (se 1 (by rfl) ⟨589076, by rfl⟩ : syracuseStep 785435 = 1178153) B1178153
theorem B523419 : Blo 519798 523419 := bstep (se 1 (by rfl) ⟨392564, by rfl⟩ : syracuseStep 523419 = 785129) B785129
theorem B588955 : Blo 519798 588955 := bstep (se 1 (by rfl) ⟨441716, by rfl⟩ : syracuseStep 588955 = 883433) B883433
theorem B2981063 : Blo 519798 2981063 := bstep (se 1 (by rfl) ⟨2235797, by rfl⟩ : syracuseStep 2981063 = 4471595) B4471595
theorem B1375507 : Blo 519798 1375507 := bstep (se 1 (by rfl) ⟨1031630, by rfl⟩ : syracuseStep 1375507 = 2063261) B2063261
theorem B523675 : Blo 519798 523675 := bstep (se 1 (by rfl) ⟨392756, by rfl⟩ : syracuseStep 523675 = 785513) B785513
theorem B523759 : Blo 519798 523759 := bstep (se 1 (by rfl) ⟨392819, by rfl⟩ : syracuseStep 523759 = 785639) B785639
theorem B4226879 : Blo 519798 4226879 := bstep (se 1 (by rfl) ⟨3170159, by rfl⟩ : syracuseStep 4226879 = 6340319) B6340319
theorem B5931143 : Blo 519798 5931143 := bstep (se 1 (by rfl) ⟨4448357, by rfl⟩ : syracuseStep 5931143 = 8896715) B8896715
theorem B1114337 : Blo 519798 1114337 := bstep (se 2 (by rfl) ⟨417876, by rfl⟩ : syracuseStep 1114337 = 835753) B835753
theorem B1409761 : Blo 519798 1409761 := bstep (se 2 (by rfl) ⟨528660, by rfl⟩ : syracuseStep 1409761 = 1057321) B1057321
theorem B1115183 : Blo 519798 1115183 := bstep (se 1 (by rfl) ⟨836387, by rfl⟩ : syracuseStep 1115183 = 1672775) B1672775
theorem B3802625 : Blo 519798 3802625 := bstep (se 2 (by rfl) ⟨1425984, by rfl⟩ : syracuseStep 3802625 = 2851969) B2851969
theorem B1803883 : Blo 519798 1803883 := bstep (se 1 (by rfl) ⟨1352912, by rfl⟩ : syracuseStep 1803883 = 2705825) B2705825
theorem B3966731 : Blo 519798 3966731 := bstep (se 1 (by rfl) ⟨2975048, by rfl⟩ : syracuseStep 3966731 = 5950097) B5950097
theorem B1738559 : Blo 519798 1738559 := bstep (se 1 (by rfl) ⟨1303919, by rfl⟩ : syracuseStep 1738559 = 2607839) B2607839
theorem B625243 : Blo 519798 625243 := bstep (se 1 (by rfl) ⟨468932, by rfl⟩ : syracuseStep 625243 = 937865) B937865
theorem B5934059 : Blo 519798 5934059 := bstep (se 1 (by rfl) ⟨4450544, by rfl⟩ : syracuseStep 5934059 = 8901089) B8901089
theorem B8883593 : Blo 519798 8883593 := bstep (se 2 (by rfl) ⟨3331347, by rfl⟩ : syracuseStep 8883593 = 6662695) B6662695
theorem B9637289 : Blo 519798 9637289 := bstep (se 2 (by rfl) ⟨3613983, by rfl⟩ : syracuseStep 9637289 = 7227967) B7227967
theorem B21368357 : Blo 519798 21368357 := bstep (se 4 (by rfl) ⟨2003283, by rfl⟩ : syracuseStep 21368357 = 4006567) B4006567
theorem B2232859 : Blo 519798 2232859 := bstep (se 1 (by rfl) ⟨1674644, by rfl⟩ : syracuseStep 2232859 = 3349289) B3349289
theorem B7508861 : Blo 519798 7508861 := bstep (se 3 (by rfl) ⟨1407911, by rfl⟩ : syracuseStep 7508861 = 2815823) B2815823
theorem B1316027 : Blo 519798 1316027 := bstep (se 1 (by rfl) ⟨987020, by rfl⟩ : syracuseStep 1316027 = 1974041) B1974041
theorem B1316371 : Blo 519798 1316371 := bstep (se 1 (by rfl) ⟨987278, by rfl⟩ : syracuseStep 1316371 = 1974557) B1974557
theorem B2233919 : Blo 519798 2233919 := bstep (se 1 (by rfl) ⟨1675439, by rfl⟩ : syracuseStep 2233919 = 3350879) B3350879
theorem B661223 : Blo 519798 661223 := bstep (se 1 (by rfl) ⟨495917, by rfl⟩ : syracuseStep 661223 = 991835) B991835
theorem B989921 : Blo 519798 989921 := bstep (se 2 (by rfl) ⟨371220, by rfl⟩ : syracuseStep 989921 = 742441) B742441
theorem B1317971 : Blo 519798 1317971 := bstep (se 1 (by rfl) ⟨988478, by rfl⟩ : syracuseStep 1317971 = 1976957) B1976957
theorem B8592767 : Blo 519798 8592767 := bstep (se 1 (by rfl) ⟨6444575, by rfl⟩ : syracuseStep 8592767 = 12889151) B12889151
theorem B9051857 : Blo 519798 9051857 := bstep (se 2 (by rfl) ⟨3394446, by rfl⟩ : syracuseStep 9051857 = 6788893) B6788893
theorem B4464557 : Blo 519798 4464557 := bstep (se 3 (by rfl) ⟨837104, by rfl⟩ : syracuseStep 4464557 = 1674209) B1674209
theorem B3612647 : Blo 519798 3612647 := bstep (se 1 (by rfl) ⟨2709485, by rfl⟩ : syracuseStep 3612647 = 5418971) B5418971
theorem B6037523 : Blo 519798 6037523 := bstep (se 1 (by rfl) ⟨4528142, by rfl⟩ : syracuseStep 6037523 = 9056285) B9056285
theorem B1057385 : Blo 519798 1057385 := bstep (se 2 (by rfl) ⟨396519, by rfl⟩ : syracuseStep 1057385 = 793039) B793039
theorem B1319915 : Blo 519798 1319915 := bstep (se 1 (by rfl) ⟨989936, by rfl⟩ : syracuseStep 1319915 = 1979873) B1979873
theorem B1320097 : Blo 519798 1320097 := bstep (se 2 (by rfl) ⟨495036, by rfl⟩ : syracuseStep 1320097 = 990073) B990073
theorem B41100533 : Blo 519798 41100533 := bstep (se 5 (by rfl) ⟨1926587, by rfl⟩ : syracuseStep 41100533 = 3853175) B3853175
theorem B1484153 : Blo 519798 1484153 := bstep (se 2 (by rfl) ⟨556557, by rfl⟩ : syracuseStep 1484153 = 1113115) B1113115
theorem B6694271 : Blo 519798 6694271 := bstep (se 1 (by rfl) ⟨5020703, by rfl⟩ : syracuseStep 6694271 = 10041407) B10041407
theorem B54208349 : Blo 519798 54208349 := bstep (se 3 (by rfl) ⟨10164065, by rfl⟩ : syracuseStep 54208349 = 20328131) B20328131
theorem B1583135 : Blo 519798 1583135 := bstep (se 1 (by rfl) ⟨1187351, by rfl⟩ : syracuseStep 1583135 = 2374703) B2374703
theorem B7612537 : Blo 519798 7612537 := bstep (se 2 (by rfl) ⟨2854701, by rfl⟩ : syracuseStep 7612537 = 5709403) B5709403
theorem B12658835 : Blo 519798 12658835 := bstep (se 1 (by rfl) ⟨9494126, by rfl⟩ : syracuseStep 12658835 = 18988253) B18988253
theorem B2829167 : Blo 519798 2829167 := bstep (se 1 (by rfl) ⟨2121875, by rfl⟩ : syracuseStep 2829167 = 4243751) B4243751
theorem B1322153 : Blo 519798 1322153 := bstep (se 2 (by rfl) ⟨495807, by rfl⟩ : syracuseStep 1322153 = 991615) B991615
theorem B2632985 : Blo 519798 2632985 := bstep (se 2 (by rfl) ⟨987369, by rfl⟩ : syracuseStep 2632985 = 1974739) B1974739
theorem B8039735 : Blo 519798 8039735 := bstep (se 1 (by rfl) ⟨6029801, by rfl⟩ : syracuseStep 8039735 = 12059603) B12059603
theorem B1322527 : Blo 519798 1322527 := bstep (se 1 (by rfl) ⟨991895, by rfl⟩ : syracuseStep 1322527 = 1983791) B1983791
theorem B22491107 : Blo 519798 22491107 := bstep (se 1 (by rfl) ⟨16868330, by rfl⟩ : syracuseStep 22491107 = 33736661) B33736661
theorem B1323499 : Blo 519798 1323499 := bstep (se 1 (by rfl) ⟨992624, by rfl⟩ : syracuseStep 1323499 = 1985249) B1985249
theorem B1979417 : Blo 519798 1979417 := bstep (se 2 (by rfl) ⟨742281, by rfl⟩ : syracuseStep 1979417 = 1484563) B1484563
theorem B7156943 : Blo 519798 7156943 := bstep (se 1 (by rfl) ⟨5367707, by rfl⟩ : syracuseStep 7156943 = 10735415) B10735415
theorem B2864609 : Blo 519798 2864609 := bstep (se 2 (by rfl) ⟨1074228, by rfl⟩ : syracuseStep 2864609 = 2148457) B2148457
theorem B2636225 : Blo 519798 2636225 := bstep (se 2 (by rfl) ⟨988584, by rfl⟩ : syracuseStep 2636225 = 1977169) B1977169
theorem B247053635 : Blo 519798 247053635 := bstep (se 1 (by rfl) ⟨185290226, by rfl⟩ : syracuseStep 247053635 = 370580453) B370580453
theorem B3751343 : Blo 519798 3751343 := bstep (se 1 (by rfl) ⟨2813507, by rfl⟩ : syracuseStep 3751343 = 5627015) B5627015
theorem B4472657 : Blo 519798 4472657 := bstep (se 2 (by rfl) ⟨1677246, by rfl⟩ : syracuseStep 4472657 = 3354493) B3354493
theorem B7160237 : Blo 519798 7160237 := bstep (se 3 (by rfl) ⟨1342544, by rfl⟩ : syracuseStep 7160237 = 2685089) B2685089
theorem B96027515 : Blo 519798 96027515 := bstep (se 1 (by rfl) ⟨72020636, by rfl⟩ : syracuseStep 96027515 = 144041273) B144041273
theorem B6702425 : Blo 519798 6702425 := bstep (se 2 (by rfl) ⟨2513409, by rfl⟩ : syracuseStep 6702425 = 5026819) B5026819
theorem B1754459 : Blo 519798 1754459 := bstep (se 1 (by rfl) ⟨1315844, by rfl⟩ : syracuseStep 1754459 = 2631689) B2631689
theorem B5720539 : Blo 519798 5720539 := bstep (se 1 (by rfl) ⟨4290404, by rfl⟩ : syracuseStep 5720539 = 8580809) B8580809
theorem B4508783 : Blo 519798 4508783 := bstep (se 1 (by rfl) ⟨3381587, by rfl⟩ : syracuseStep 4508783 = 6763175) B6763175
theorem B7523675 : Blo 519798 7523675 := bstep (se 1 (by rfl) ⟨5642756, by rfl⟩ : syracuseStep 7523675 = 11285513) B11285513
theorem B1756673 : Blo 519798 1756673 := bstep (se 2 (by rfl) ⟨658752, by rfl⟩ : syracuseStep 1756673 = 1317505) B1317505
theorem B4280843 : Blo 519798 4280843 := bstep (se 1 (by rfl) ⟨3210632, by rfl⟩ : syracuseStep 4280843 = 6421265) B6421265
theorem B1757753 : Blo 519798 1757753 := bstep (se 2 (by rfl) ⟨659157, by rfl⟩ : syracuseStep 1757753 = 1318315) B1318315
theorem B2642543 : Blo 519798 2642543 := bstep (se 1 (by rfl) ⟨1981907, by rfl⟩ : syracuseStep 2642543 = 3963815) B3963815
theorem B1757915 : Blo 519798 1757915 := bstep (se 1 (by rfl) ⟨1318436, by rfl⟩ : syracuseStep 1757915 = 2636873) B2636873
theorem B1987375 : Blo 519798 1987375 := bstep (se 1 (by rfl) ⟨1490531, by rfl⟩ : syracuseStep 1987375 = 2981063) B2981063
theorem B13423805 : Blo 519798 13423805 := bstep (se 3 (by rfl) ⟨2516963, by rfl⟩ : syracuseStep 13423805 = 5033927) B5033927
theorem B5658761 : Blo 519798 5658761 := bstep (se 2 (by rfl) ⟨2122035, by rfl⟩ : syracuseStep 5658761 = 4244071) B4244071
theorem B1169657 : Blo 519798 1169657 := bstep (se 2 (by rfl) ⟨438621, by rfl⟩ : syracuseStep 1169657 = 877243) B877243
theorem B1759535 : Blo 519798 1759535 := bstep (se 1 (by rfl) ⟨1319651, by rfl⟩ : syracuseStep 1759535 = 2639303) B2639303
theorem B1169819 : Blo 519798 1169819 := bstep (se 1 (by rfl) ⟨877364, by rfl⟩ : syracuseStep 1169819 = 1754729) B1754729
theorem B1759751 : Blo 519798 1759751 := bstep (se 1 (by rfl) ⟨1319813, by rfl⟩ : syracuseStep 1759751 = 2639627) B2639627
theorem B1760507 : Blo 519798 1760507 := bstep (se 1 (by rfl) ⟨1320380, by rfl⟩ : syracuseStep 1760507 = 2640761) B2640761
theorem B1760831 : Blo 519798 1760831 := bstep (se 1 (by rfl) ⟨1320623, by rfl⟩ : syracuseStep 1760831 = 2641247) B2641247
theorem B4022399 : Blo 519798 4022399 := bstep (se 1 (by rfl) ⟨3016799, by rfl⟩ : syracuseStep 4022399 = 6033599) B6033599
theorem B1761479 : Blo 519798 1761479 := bstep (se 1 (by rfl) ⟨1321109, by rfl⟩ : syracuseStep 1761479 = 2642219) B2642219
theorem B3760343 : Blo 519798 3760343 := bstep (se 1 (by rfl) ⟨2820257, by rfl⟩ : syracuseStep 3760343 = 5640515) B5640515
theorem B2646269 : Blo 519798 2646269 := bstep (se 3 (by rfl) ⟨496175, by rfl⟩ : syracuseStep 2646269 = 992351) B992351
theorem B1171871 : Blo 519798 1171871 := bstep (se 1 (by rfl) ⟨878903, by rfl⟩ : syracuseStep 1171871 = 1757807) B1757807
theorem B1172105 : Blo 519798 1172105 := bstep (se 2 (by rfl) ⟨439539, by rfl⟩ : syracuseStep 1172105 = 879079) B879079
theorem B123921247 : Blo 519798 123921247 := bstep (se 1 (by rfl) ⟨92940935, by rfl⟩ : syracuseStep 123921247 = 185881871) B185881871
theorem B877439 : Blo 519798 877439 := bstep (se 1 (by rfl) ⟨658079, by rfl⟩ : syracuseStep 877439 = 1316159) B1316159
theorem B2515967 : Blo 519798 2515967 := bstep (se 1 (by rfl) ⟨1886975, by rfl⟩ : syracuseStep 2515967 = 3773951) B3773951
theorem B1762343 : Blo 519798 1762343 := bstep (se 1 (by rfl) ⟨1321757, by rfl⟩ : syracuseStep 1762343 = 2643515) B2643515
theorem B877871 : Blo 519798 877871 := bstep (se 1 (by rfl) ⟨658403, by rfl⟩ : syracuseStep 877871 = 1316807) B1316807
theorem B779753 : Blo 519798 779753 := bstep (se 2 (by rfl) ⟨292407, by rfl⟩ : syracuseStep 779753 = 584815) B584815
theorem B780041 : Blo 519798 780041 := bstep (se 2 (by rfl) ⟨292515, by rfl⟩ : syracuseStep 780041 = 585031) B585031
theorem B3336167 : Blo 519798 3336167 := bstep (se 1 (by rfl) ⟨2502125, by rfl⟩ : syracuseStep 3336167 = 5004251) B5004251
theorem B780359 : Blo 519798 780359 := bstep (se 1 (by rfl) ⟨585269, by rfl⟩ : syracuseStep 780359 = 1170539) B1170539
theorem B1763423 : Blo 519798 1763423 := bstep (se 1 (by rfl) ⟨1322567, by rfl⟩ : syracuseStep 1763423 = 2645135) B2645135
theorem B780455 : Blo 519798 780455 := bstep (se 1 (by rfl) ⟨585341, by rfl⟩ : syracuseStep 780455 = 1170683) B1170683
theorem B780539 : Blo 519798 780539 := bstep (se 1 (by rfl) ⟨585404, by rfl⟩ : syracuseStep 780539 = 1170809) B1170809
theorem B2648375 : Blo 519798 2648375 := bstep (se 1 (by rfl) ⟨1986281, by rfl⟩ : syracuseStep 2648375 = 3972563) B3972563
theorem B780959 : Blo 519798 780959 := bstep (se 1 (by rfl) ⟨585719, by rfl⟩ : syracuseStep 780959 = 1171439) B1171439
theorem B1174175 : Blo 519798 1174175 := bstep (se 1 (by rfl) ⟨880631, by rfl⟩ : syracuseStep 1174175 = 1761263) B1761263
theorem B781127 : Blo 519798 781127 := bstep (se 1 (by rfl) ⟨585845, by rfl⟩ : syracuseStep 781127 = 1171691) B1171691
theorem B1174355 : Blo 519798 1174355 := bstep (se 1 (by rfl) ⟨880766, by rfl⟩ : syracuseStep 1174355 = 1761533) B1761533
theorem B879707 : Blo 519798 879707 := bstep (se 1 (by rfl) ⟨659780, by rfl⟩ : syracuseStep 879707 = 1319561) B1319561
theorem B879727 : Blo 519798 879727 := bstep (se 1 (by rfl) ⟨659795, by rfl⟩ : syracuseStep 879727 = 1319591) B1319591
theorem B1174715 : Blo 519798 1174715 := bstep (se 1 (by rfl) ⟨881036, by rfl⟩ : syracuseStep 1174715 = 1762073) B1762073
theorem B781727 : Blo 519798 781727 := bstep (se 1 (by rfl) ⟨586295, by rfl⟩ : syracuseStep 781727 = 1172591) B1172591
theorem B519887 : Blo 519798 519887 := bstep (se 1 (by rfl) ⟨389915, by rfl⟩ : syracuseStep 519887 = 779831) B779831
theorem B3010375 : Blo 519798 3010375 := bstep (se 1 (by rfl) ⟨2257781, by rfl⟩ : syracuseStep 3010375 = 4515563) B4515563
theorem B520103 : Blo 519798 520103 := bstep (se 1 (by rfl) ⟨390077, by rfl⟩ : syracuseStep 520103 = 780155) B780155
theorem B520127 : Blo 519798 520127 := bstep (se 1 (by rfl) ⟨390095, by rfl⟩ : syracuseStep 520127 = 780191) B780191
theorem B1765367 : Blo 519798 1765367 := bstep (se 1 (by rfl) ⟨1324025, by rfl⟩ : syracuseStep 1765367 = 2648051) B2648051
theorem B782399 : Blo 519798 782399 := bstep (se 1 (by rfl) ⟨586799, by rfl⟩ : syracuseStep 782399 = 1173599) B1173599
theorem B520283 : Blo 519798 520283 := bstep (se 1 (by rfl) ⟨390212, by rfl⟩ : syracuseStep 520283 = 780425) B780425
theorem B7336037 : Blo 519798 7336037 := bstep (se 4 (by rfl) ⟨687753, by rfl⟩ : syracuseStep 7336037 = 1375507) B1375507
theorem B520383 : Blo 519798 520383 := bstep (se 1 (by rfl) ⟨390287, by rfl⟩ : syracuseStep 520383 = 780575) B780575
theorem B1175759 : Blo 519798 1175759 := bstep (se 1 (by rfl) ⟨881819, by rfl⟩ : syracuseStep 1175759 = 1763639) B1763639
theorem B520415 : Blo 519798 520415 := bstep (se 1 (by rfl) ⟨390311, by rfl⟩ : syracuseStep 520415 = 780623) B780623
theorem B880895 : Blo 519798 880895 := bstep (se 1 (by rfl) ⟨660671, by rfl⟩ : syracuseStep 880895 = 1321343) B1321343
theorem B520475 : Blo 519798 520475 := bstep (se 1 (by rfl) ⟨390356, by rfl⟩ : syracuseStep 520475 = 780713) B780713
theorem B1405241 : Blo 519798 1405241 := bstep (se 2 (by rfl) ⟨526965, by rfl⟩ : syracuseStep 1405241 = 1053931) B1053931
theorem B520731 : Blo 519798 520731 := bstep (se 1 (by rfl) ⟨390548, by rfl⟩ : syracuseStep 520731 = 781097) B781097
theorem B520871 : Blo 519798 520871 := bstep (se 1 (by rfl) ⟨390653, by rfl⟩ : syracuseStep 520871 = 781307) B781307
theorem B520911 : Blo 519798 520911 := bstep (se 1 (by rfl) ⟨390683, by rfl⟩ : syracuseStep 520911 = 781367) B781367
theorem B520991 : Blo 519798 520991 := bstep (se 1 (by rfl) ⟨390743, by rfl⟩ : syracuseStep 520991 = 781487) B781487
theorem B521031 : Blo 519798 521031 := bstep (se 1 (by rfl) ⟨390773, by rfl⟩ : syracuseStep 521031 = 781547) B781547
theorem B1766447 : Blo 519798 1766447 := bstep (se 1 (by rfl) ⟨1324835, by rfl⟩ : syracuseStep 1766447 = 2649671) B2649671
theorem B1176731 : Blo 519798 1176731 := bstep (se 1 (by rfl) ⟨882548, by rfl⟩ : syracuseStep 1176731 = 1765097) B1765097
theorem B521471 : Blo 519798 521471 := bstep (se 1 (by rfl) ⟨391103, by rfl⟩ : syracuseStep 521471 = 782207) B782207
theorem B783695 : Blo 519798 783695 := bstep (se 1 (by rfl) ⟨587771, by rfl⟩ : syracuseStep 783695 = 1175543) B1175543
theorem B783737 : Blo 519798 783737 := bstep (se 2 (by rfl) ⟨293901, by rfl⟩ : syracuseStep 783737 = 587803) B587803
theorem B1766825 : Blo 519798 1766825 := bstep (se 2 (by rfl) ⟨662559, by rfl⟩ : syracuseStep 1766825 = 1325119) B1325119
theorem B2979287 : Blo 519798 2979287 := bstep (se 1 (by rfl) ⟨2234465, by rfl⟩ : syracuseStep 2979287 = 4468931) B4468931
theorem B521695 : Blo 519798 521695 := bstep (se 1 (by rfl) ⟨391271, by rfl⟩ : syracuseStep 521695 = 782543) B782543
theorem B1766879 : Blo 519798 1766879 := bstep (se 1 (by rfl) ⟨1325159, by rfl⟩ : syracuseStep 1766879 = 2650319) B2650319
theorem B521775 : Blo 519798 521775 := bstep (se 1 (by rfl) ⟨391331, by rfl⟩ : syracuseStep 521775 = 782663) B782663
theorem B783935 : Blo 519798 783935 := bstep (se 1 (by rfl) ⟨587951, by rfl⟩ : syracuseStep 783935 = 1175903) B1175903
theorem B4454099 : Blo 519798 4454099 := bstep (se 1 (by rfl) ⟨3340574, by rfl⟩ : syracuseStep 4454099 = 6681149) B6681149
theorem B522087 : Blo 519798 522087 := bstep (se 1 (by rfl) ⟨391565, by rfl⟩ : syracuseStep 522087 = 783131) B783131
theorem B784283 : Blo 519798 784283 := bstep (se 1 (by rfl) ⟨588212, by rfl⟩ : syracuseStep 784283 = 1176425) B1176425
theorem B1767419 : Blo 519798 1767419 := bstep (se 1 (by rfl) ⟨1325564, by rfl⟩ : syracuseStep 1767419 = 2651129) B2651129
theorem B522271 : Blo 519798 522271 := bstep (se 1 (by rfl) ⟨391703, by rfl⟩ : syracuseStep 522271 = 783407) B783407
theorem B784415 : Blo 519798 784415 := bstep (se 1 (by rfl) ⟨588311, by rfl⟩ : syracuseStep 784415 = 1176623) B1176623
theorem B522303 : Blo 519798 522303 := bstep (se 1 (by rfl) ⟨391727, by rfl⟩ : syracuseStep 522303 = 783455) B783455
theorem B587839 : Blo 519798 587839 := bstep (se 1 (by rfl) ⟨440879, by rfl⟩ : syracuseStep 587839 = 881759) B881759
theorem B522343 : Blo 519798 522343 := bstep (se 1 (by rfl) ⟨391757, by rfl⟩ : syracuseStep 522343 = 783515) B783515
theorem B1767527 : Blo 519798 1767527 := bstep (se 1 (by rfl) ⟨1325645, by rfl⟩ : syracuseStep 1767527 = 2651291) B2651291
theorem B522351 : Blo 519798 522351 := bstep (se 1 (by rfl) ⟨391763, by rfl⟩ : syracuseStep 522351 = 783527) B783527
theorem B555259 : Blo 519798 555259 := bstep (se 1 (by rfl) ⟨416444, by rfl⟩ : syracuseStep 555259 = 832889) B832889
theorem B2226487 : Blo 519798 2226487 := bstep (se 1 (by rfl) ⟨1669865, by rfl⟩ : syracuseStep 2226487 = 3339731) B3339731
theorem B522799 : Blo 519798 522799 := bstep (se 1 (by rfl) ⟨392099, by rfl⟩ : syracuseStep 522799 = 784199) B784199
theorem B784943 : Blo 519798 784943 := bstep (se 1 (by rfl) ⟨588707, by rfl⟩ : syracuseStep 784943 = 1177415) B1177415
theorem B5012057 : Blo 519798 5012057 := bstep (se 2 (by rfl) ⟨1879521, by rfl⟩ : syracuseStep 5012057 = 3759043) B3759043
theorem B522919 : Blo 519798 522919 := bstep (se 1 (by rfl) ⟨392189, by rfl⟩ : syracuseStep 522919 = 784379) B784379
theorem B785063 : Blo 519798 785063 := bstep (se 1 (by rfl) ⟨588797, by rfl⟩ : syracuseStep 785063 = 1177595) B1177595
theorem B522959 : Blo 519798 522959 := bstep (se 1 (by rfl) ⟨392219, by rfl⟩ : syracuseStep 522959 = 784439) B784439
theorem B523003 : Blo 519798 523003 := bstep (se 1 (by rfl) ⟨392252, by rfl⟩ : syracuseStep 523003 = 784505) B784505
theorem B785147 : Blo 519798 785147 := bstep (se 1 (by rfl) ⟨588860, by rfl⟩ : syracuseStep 785147 = 1177721) B1177721
theorem B523039 : Blo 519798 523039 := bstep (se 1 (by rfl) ⟨392279, by rfl⟩ : syracuseStep 523039 = 784559) B784559
theorem B785183 : Blo 519798 785183 := bstep (se 1 (by rfl) ⟨588887, by rfl⟩ : syracuseStep 785183 = 1177775) B1177775
theorem B785273 : Blo 519798 785273 := bstep (se 2 (by rfl) ⟨294477, by rfl⟩ : syracuseStep 785273 = 588955) B588955
theorem B523199 : Blo 519798 523199 := bstep (se 1 (by rfl) ⟨392399, by rfl⟩ : syracuseStep 523199 = 784799) B784799
theorem B523259 : Blo 519798 523259 := bstep (se 1 (by rfl) ⟨392444, by rfl⟩ : syracuseStep 523259 = 784889) B784889
theorem B16972897 : Blo 519798 16972897 := bstep (se 2 (by rfl) ⟨6364836, by rfl⟩ : syracuseStep 16972897 = 12729673) B12729673
theorem B785615 : Blo 519798 785615 := bstep (se 1 (by rfl) ⟨589211, by rfl⟩ : syracuseStep 785615 = 1178423) B1178423
theorem B523583 : Blo 519798 523583 := bstep (se 1 (by rfl) ⟨392687, by rfl⟩ : syracuseStep 523583 = 785375) B785375
theorem B2620759 : Blo 519798 2620759 := bstep (se 1 (by rfl) ⟨1965569, by rfl⟩ : syracuseStep 2620759 = 3931139) B3931139
theorem B523623 : Blo 519798 523623 := bstep (se 1 (by rfl) ⟨392717, by rfl⟩ : syracuseStep 523623 = 785435) B785435
theorem B2817919 : Blo 519798 2817919 := bstep (se 1 (by rfl) ⟨2113439, by rfl⟩ : syracuseStep 2817919 = 4226879) B4226879
theorem B2819693 : Blo 519798 2819693 := bstep (se 3 (by rfl) ⟨528692, by rfl⟩ : syracuseStep 2819693 = 1057385) B1057385
theorem B5015783 : Blo 519798 5015783 := bstep (se 1 (by rfl) ⟨3761837, by rfl⟩ : syracuseStep 5015783 = 7523675) B7523675
theorem B6424859 : Blo 519798 6424859 := bstep (se 1 (by rfl) ⟨4818644, by rfl⟩ : syracuseStep 6424859 = 9637289) B9637289
theorem B2853895 : Blo 519798 2853895 := bstep (se 1 (by rfl) ⟨2140421, by rfl⟩ : syracuseStep 2853895 = 4280843) B4280843
theorem B8949203 : Blo 519798 8949203 := bstep (se 1 (by rfl) ⟨6711902, by rfl⟩ : syracuseStep 8949203 = 13423805) B13423805
theorem B3772507 : Blo 519798 3772507 := bstep (se 1 (by rfl) ⟨2829380, by rfl⟩ : syracuseStep 3772507 = 5658761) B5658761
theorem B6034571 : Blo 519798 6034571 := bstep (se 1 (by rfl) ⟨4525928, by rfl⟩ : syracuseStep 6034571 = 9051857) B9051857
theorem B1677311 : Blo 519798 1677311 := bstep (se 1 (by rfl) ⟨1257983, by rfl⟩ : syracuseStep 1677311 = 2515967) B2515967
theorem B27400355 : Blo 519798 27400355 := bstep (se 1 (by rfl) ⟨20550266, by rfl⟩ : syracuseStep 27400355 = 41100533) B41100533
theorem B989435 : Blo 519798 989435 := bstep (se 1 (by rfl) ⟨742076, by rfl⟩ : syracuseStep 989435 = 1484153) B1484153
theorem B4462847 : Blo 519798 4462847 := bstep (se 1 (by rfl) ⟨3347135, by rfl⟩ : syracuseStep 4462847 = 6694271) B6694271
theorem B1055423 : Blo 519798 1055423 := bstep (se 1 (by rfl) ⟨791567, by rfl⟩ : syracuseStep 1055423 = 1583135) B1583135
theorem B4890691 : Blo 519798 4890691 := bstep (se 1 (by rfl) ⟨3668018, by rfl⟩ : syracuseStep 4890691 = 7336037) B7336037
theorem B1319611 : Blo 519798 1319611 := bstep (se 1 (by rfl) ⟨989708, by rfl⟩ : syracuseStep 1319611 = 1979417) B1979417
theorem B1909739 : Blo 519798 1909739 := bstep (se 1 (by rfl) ⟨1432304, by rfl⟩ : syracuseStep 1909739 = 2864609) B2864609
theorem B164702423 : Blo 519798 164702423 := bstep (se 1 (by rfl) ⟨123526817, by rfl⟩ : syracuseStep 164702423 = 247053635) B247053635
theorem B2500895 : Blo 519798 2500895 := bstep (se 1 (by rfl) ⟨1875671, by rfl⟩ : syracuseStep 2500895 = 3751343) B3751343
theorem B4468283 : Blo 519798 4468283 := bstep (se 1 (by rfl) ⟨3351212, by rfl⟩ : syracuseStep 4468283 = 6702425) B6702425
theorem B1879681 : Blo 519798 1879681 := bstep (se 2 (by rfl) ⟨704880, by rfl⟩ : syracuseStep 1879681 = 1409761) B1409761
theorem B2535083 : Blo 519798 2535083 := bstep (se 1 (by rfl) ⟨1901312, by rfl⟩ : syracuseStep 2535083 = 3802625) B3802625
theorem B165228329 : Blo 519798 165228329 := bstep (se 2 (by rfl) ⟨61960623, by rfl⟩ : syracuseStep 165228329 = 123921247) B123921247
theorem B1159039 : Blo 519798 1159039 := bstep (se 1 (by rfl) ⟨869279, by rfl⟩ : syracuseStep 1159039 = 1738559) B1738559
theorem B2405177 : Blo 519798 2405177 := bstep (se 2 (by rfl) ⟨901941, by rfl⟩ : syracuseStep 2405177 = 1803883) B1803883
theorem B833657 : Blo 519798 833657 := bstep (se 2 (by rfl) ⟨312621, by rfl⟩ : syracuseStep 833657 = 625243) B625243
theorem B1489279 : Blo 519798 1489279 := bstep (se 1 (by rfl) ⟨1116959, by rfl⟩ : syracuseStep 1489279 = 2233919) B2233919
theorem B2506895 : Blo 519798 2506895 := bstep (se 1 (by rfl) ⟨1880171, by rfl⟩ : syracuseStep 2506895 = 3760343) B3760343
theorem B8439223 : Blo 519798 8439223 := bstep (se 1 (by rfl) ⟨6329417, by rfl⟩ : syracuseStep 8439223 = 12658835) B12658835
theorem B1886111 : Blo 519798 1886111 := bstep (se 1 (by rfl) ⟨1414583, by rfl⟩ : syracuseStep 1886111 = 2829167) B2829167
theorem B2639789 : Blo 519798 2639789 := bstep (se 3 (by rfl) ⟨494960, by rfl⟩ : syracuseStep 2639789 = 989921) B989921
theorem B1755161 : Blo 519798 1755161 := bstep (se 2 (by rfl) ⟨658185, by rfl⟩ : syracuseStep 1755161 = 1316371) B1316371
theorem B1755323 : Blo 519798 1755323 := bstep (se 1 (by rfl) ⟨1316492, by rfl⟩ : syracuseStep 1755323 = 2632985) B2632985
theorem B5359823 : Blo 519798 5359823 := bstep (se 1 (by rfl) ⟨4019867, by rfl⟩ : syracuseStep 5359823 = 8039735) B8039735
theorem B14994071 : Blo 519798 14994071 := bstep (se 1 (by rfl) ⟨11245553, by rfl⟩ : syracuseStep 14994071 = 22491107) B22491107
theorem B936827 : Blo 519798 936827 := bstep (se 1 (by rfl) ⟨702620, by rfl⟩ : syracuseStep 936827 = 1405241) B1405241
theorem B740345 : Blo 519798 740345 := bstep (se 2 (by rfl) ⟨277629, by rfl⟩ : syracuseStep 740345 = 555259) B555259
theorem B2968649 : Blo 519798 2968649 := bstep (se 2 (by rfl) ⟨1113243, by rfl⟩ : syracuseStep 2968649 = 2226487) B2226487
theorem B4771295 : Blo 519798 4771295 := bstep (se 1 (by rfl) ⟨3578471, by rfl⟩ : syracuseStep 4771295 = 7156943) B7156943
theorem B1986191 : Blo 519798 1986191 := bstep (se 1 (by rfl) ⟨1489643, by rfl⟩ : syracuseStep 1986191 = 2979287) B2979287
theorem B2969399 : Blo 519798 2969399 := bstep (se 1 (by rfl) ⟨2227049, by rfl⟩ : syracuseStep 2969399 = 4454099) B4454099
theorem B22630529 : Blo 519798 22630529 := bstep (se 2 (by rfl) ⟨8486448, by rfl⟩ : syracuseStep 22630529 = 16972897) B16972897
theorem B1757483 : Blo 519798 1757483 := bstep (se 1 (by rfl) ⟨1318112, by rfl⟩ : syracuseStep 1757483 = 2636225) B2636225
theorem B3494345 : Blo 519798 3494345 := bstep (se 2 (by rfl) ⟨1310379, by rfl⟩ : syracuseStep 3494345 = 2620759) B2620759
theorem B3757225 : Blo 519798 3757225 := bstep (se 2 (by rfl) ⟨1408959, by rfl⟩ : syracuseStep 3757225 = 2817919) B2817919
theorem B3954095 : Blo 519798 3954095 := bstep (se 1 (by rfl) ⟨2965571, by rfl⟩ : syracuseStep 3954095 = 5931143) B5931143
theorem B4773491 : Blo 519798 4773491 := bstep (se 1 (by rfl) ⟨3580118, by rfl⟩ : syracuseStep 4773491 = 7160237) B7160237
theorem B64018343 : Blo 519798 64018343 := bstep (se 1 (by rfl) ⟨48013757, by rfl⟩ : syracuseStep 64018343 = 96027515) B96027515
theorem B2971565 : Blo 519798 2971565 := bstep (se 3 (by rfl) ⟨557168, by rfl⟩ : syracuseStep 2971565 = 1114337) B1114337
theorem B743455 : Blo 519798 743455 := bstep (se 1 (by rfl) ⟨557591, by rfl⟩ : syracuseStep 743455 = 1115183) B1115183
theorem B1169639 : Blo 519798 1169639 := bstep (se 1 (by rfl) ⟨877229, by rfl⟩ : syracuseStep 1169639 = 1754459) B1754459
theorem B2644487 : Blo 519798 2644487 := bstep (se 1 (by rfl) ⟨1983365, by rfl⟩ : syracuseStep 2644487 = 3966731) B3966731
theorem B1760129 : Blo 519798 1760129 := bstep (se 2 (by rfl) ⟨660048, by rfl⟩ : syracuseStep 1760129 = 1320097) B1320097
theorem B3956039 : Blo 519798 3956039 := bstep (se 1 (by rfl) ⟨2967029, by rfl⟩ : syracuseStep 3956039 = 5934059) B5934059
theorem B3005855 : Blo 519798 3005855 := bstep (se 1 (by rfl) ⟨2254391, by rfl⟩ : syracuseStep 3005855 = 4508783) B4508783
theorem B5922395 : Blo 519798 5922395 := bstep (se 1 (by rfl) ⟨4441796, by rfl⟩ : syracuseStep 5922395 = 8883593) B8883593
theorem B1171115 : Blo 519798 1171115 := bstep (se 1 (by rfl) ⟨878336, by rfl⟩ : syracuseStep 1171115 = 1756673) B1756673
theorem B14245571 : Blo 519798 14245571 := bstep (se 1 (by rfl) ⟨10684178, by rfl⟩ : syracuseStep 14245571 = 21368357) B21368357
theorem B10150049 : Blo 519798 10150049 := bstep (se 2 (by rfl) ⟨3806268, by rfl⟩ : syracuseStep 10150049 = 7612537) B7612537
theorem B1171835 : Blo 519798 1171835 := bstep (se 1 (by rfl) ⟨878876, by rfl⟩ : syracuseStep 1171835 = 1757753) B1757753
theorem B1761695 : Blo 519798 1761695 := bstep (se 1 (by rfl) ⟨1321271, by rfl⟩ : syracuseStep 1761695 = 2642543) B2642543
theorem B1171943 : Blo 519798 1171943 := bstep (se 1 (by rfl) ⟨878957, by rfl⟩ : syracuseStep 1171943 = 1757915) B1757915
theorem B5005907 : Blo 519798 5005907 := bstep (se 1 (by rfl) ⟨3754430, by rfl⟩ : syracuseStep 5005907 = 7508861) B7508861
theorem B7627385 : Blo 519798 7627385 := bstep (se 2 (by rfl) ⟨2860269, by rfl⟩ : syracuseStep 7627385 = 5720539) B5720539
theorem B877351 : Blo 519798 877351 := bstep (se 1 (by rfl) ⟨658013, by rfl⟩ : syracuseStep 877351 = 1316027) B1316027
theorem B1172969 : Blo 519798 1172969 := bstep (se 2 (by rfl) ⟨439863, by rfl⟩ : syracuseStep 1172969 = 879727) B879727
theorem B779771 : Blo 519798 779771 := bstep (se 1 (by rfl) ⟨584828, by rfl⟩ : syracuseStep 779771 = 1169657) B1169657
theorem B1173023 : Blo 519798 1173023 := bstep (se 1 (by rfl) ⟨879767, by rfl⟩ : syracuseStep 1173023 = 1759535) B1759535
theorem B779879 : Blo 519798 779879 := bstep (se 1 (by rfl) ⟨584909, by rfl⟩ : syracuseStep 779879 = 1169819) B1169819
theorem B1173167 : Blo 519798 1173167 := bstep (se 1 (by rfl) ⟨879875, by rfl⟩ : syracuseStep 1173167 = 1759751) B1759751
theorem B1763261 : Blo 519798 1763261 := bstep (se 3 (by rfl) ⟨330611, by rfl⟩ : syracuseStep 1763261 = 661223) B661223
theorem B1763369 : Blo 519798 1763369 := bstep (se 2 (by rfl) ⟨661263, by rfl⟩ : syracuseStep 1763369 = 1322527) B1322527
theorem B878647 : Blo 519798 878647 := bstep (se 1 (by rfl) ⟨658985, by rfl⟩ : syracuseStep 878647 = 1317971) B1317971
theorem B1173671 : Blo 519798 1173671 := bstep (se 1 (by rfl) ⟨880253, by rfl⟩ : syracuseStep 1173671 = 1760507) B1760507
theorem B5728511 : Blo 519798 5728511 := bstep (se 1 (by rfl) ⟨4296383, by rfl⟩ : syracuseStep 5728511 = 8592767) B8592767
theorem B1173887 : Blo 519798 1173887 := bstep (se 1 (by rfl) ⟨880415, by rfl⟩ : syracuseStep 1173887 = 1760831) B1760831
theorem B2976371 : Blo 519798 2976371 := bstep (se 1 (by rfl) ⟨2232278, by rfl⟩ : syracuseStep 2976371 = 4464557) B4464557
theorem B4025015 : Blo 519798 4025015 := bstep (se 1 (by rfl) ⟨3018761, by rfl⟩ : syracuseStep 4025015 = 6037523) B6037523
theorem B2681599 : Blo 519798 2681599 := bstep (se 1 (by rfl) ⟨2011199, by rfl⟩ : syracuseStep 2681599 = 4022399) B4022399
theorem B1174319 : Blo 519798 1174319 := bstep (se 1 (by rfl) ⟨880739, by rfl⟩ : syracuseStep 1174319 = 1761479) B1761479
theorem B1764179 : Blo 519798 1764179 := bstep (se 1 (by rfl) ⟨1323134, by rfl⟩ : syracuseStep 1764179 = 2646269) B2646269
theorem B781247 : Blo 519798 781247 := bstep (se 1 (by rfl) ⟨585935, by rfl⟩ : syracuseStep 781247 = 1171871) B1171871
theorem B781403 : Blo 519798 781403 := bstep (se 1 (by rfl) ⟨586052, by rfl⟩ : syracuseStep 781403 = 1172105) B1172105
theorem B584959 : Blo 519798 584959 := bstep (se 1 (by rfl) ⟨438719, by rfl⟩ : syracuseStep 584959 = 877439) B877439
theorem B1764665 : Blo 519798 1764665 := bstep (se 2 (by rfl) ⟨661749, by rfl⟩ : syracuseStep 1764665 = 1323499) B1323499
theorem B879943 : Blo 519798 879943 := bstep (se 1 (by rfl) ⟨659957, by rfl⟩ : syracuseStep 879943 = 1319915) B1319915
theorem B1174895 : Blo 519798 1174895 := bstep (se 1 (by rfl) ⟨881171, by rfl⟩ : syracuseStep 1174895 = 1762343) B1762343
theorem B2977145 : Blo 519798 2977145 := bstep (se 2 (by rfl) ⟨1116429, by rfl⟩ : syracuseStep 2977145 = 2232859) B2232859
theorem B585247 : Blo 519798 585247 := bstep (se 1 (by rfl) ⟨438935, by rfl⟩ : syracuseStep 585247 = 877871) B877871
theorem B519835 : Blo 519798 519835 := bstep (se 1 (by rfl) ⟨389876, by rfl⟩ : syracuseStep 519835 = 779753) B779753
theorem B2649833 : Blo 519798 2649833 := bstep (se 2 (by rfl) ⟨993687, by rfl⟩ : syracuseStep 2649833 = 1987375) B1987375
theorem B520027 : Blo 519798 520027 := bstep (se 1 (by rfl) ⟨390020, by rfl⟩ : syracuseStep 520027 = 780041) B780041
theorem B36138899 : Blo 519798 36138899 := bstep (se 1 (by rfl) ⟨27104174, by rfl⟩ : syracuseStep 36138899 = 54208349) B54208349
theorem B2224111 : Blo 519798 2224111 := bstep (se 1 (by rfl) ⟨1668083, by rfl⟩ : syracuseStep 2224111 = 3336167) B3336167
theorem B520239 : Blo 519798 520239 := bstep (se 1 (by rfl) ⟨390179, by rfl⟩ : syracuseStep 520239 = 780359) B780359
theorem B1175615 : Blo 519798 1175615 := bstep (se 1 (by rfl) ⟨881711, by rfl⟩ : syracuseStep 1175615 = 1763423) B1763423
theorem B520303 : Blo 519798 520303 := bstep (se 1 (by rfl) ⟨390227, by rfl⟩ : syracuseStep 520303 = 780455) B780455
theorem B520359 : Blo 519798 520359 := bstep (se 1 (by rfl) ⟨390269, by rfl⟩ : syracuseStep 520359 = 780539) B780539
theorem B1765583 : Blo 519798 1765583 := bstep (se 1 (by rfl) ⟨1324187, by rfl⟩ : syracuseStep 1765583 = 2648375) B2648375
theorem B520639 : Blo 519798 520639 := bstep (se 1 (by rfl) ⟨390479, by rfl⟩ : syracuseStep 520639 = 780959) B780959
theorem B782783 : Blo 519798 782783 := bstep (se 1 (by rfl) ⟨587087, by rfl⟩ : syracuseStep 782783 = 1174175) B1174175
theorem B520751 : Blo 519798 520751 := bstep (se 1 (by rfl) ⟨390563, by rfl⟩ : syracuseStep 520751 = 781127) B781127
theorem B782903 : Blo 519798 782903 := bstep (se 1 (by rfl) ⟨587177, by rfl⟩ : syracuseStep 782903 = 1174355) B1174355
theorem B586471 : Blo 519798 586471 := bstep (se 1 (by rfl) ⟨439853, by rfl⟩ : syracuseStep 586471 = 879707) B879707
theorem B881435 : Blo 519798 881435 := bstep (se 1 (by rfl) ⟨661076, by rfl⟩ : syracuseStep 881435 = 1322153) B1322153
theorem B783143 : Blo 519798 783143 := bstep (se 1 (by rfl) ⟨587357, by rfl⟩ : syracuseStep 783143 = 1174715) B1174715
theorem B521151 : Blo 519798 521151 := bstep (se 1 (by rfl) ⟨390863, by rfl⟩ : syracuseStep 521151 = 781727) B781727
theorem B1176911 : Blo 519798 1176911 := bstep (se 1 (by rfl) ⟨882683, by rfl⟩ : syracuseStep 1176911 = 1765367) B1765367
theorem B521599 : Blo 519798 521599 := bstep (se 1 (by rfl) ⟨391199, by rfl⟩ : syracuseStep 521599 = 782399) B782399
theorem B783785 : Blo 519798 783785 := bstep (se 2 (by rfl) ⟨293919, by rfl⟩ : syracuseStep 783785 = 587839) B587839
theorem B783839 : Blo 519798 783839 := bstep (se 1 (by rfl) ⟨587879, by rfl⟩ : syracuseStep 783839 = 1175759) B1175759
theorem B587263 : Blo 519798 587263 := bstep (se 1 (by rfl) ⟨440447, by rfl⟩ : syracuseStep 587263 = 880895) B880895
theorem B1177631 : Blo 519798 1177631 := bstep (se 1 (by rfl) ⟨883223, by rfl⟩ : syracuseStep 1177631 = 1766447) B1766447
theorem B784487 : Blo 519798 784487 := bstep (se 1 (by rfl) ⟨588365, by rfl⟩ : syracuseStep 784487 = 1176731) B1176731
theorem B522463 : Blo 519798 522463 := bstep (se 1 (by rfl) ⟨391847, by rfl⟩ : syracuseStep 522463 = 783695) B783695
theorem B522491 : Blo 519798 522491 := bstep (se 1 (by rfl) ⟨391868, by rfl⟩ : syracuseStep 522491 = 783737) B783737
theorem B1177883 : Blo 519798 1177883 := bstep (se 1 (by rfl) ⟨883412, by rfl⟩ : syracuseStep 1177883 = 1766825) B1766825
theorem B1177919 : Blo 519798 1177919 := bstep (se 1 (by rfl) ⟨883439, by rfl⟩ : syracuseStep 1177919 = 1766879) B1766879
theorem B522623 : Blo 519798 522623 := bstep (se 1 (by rfl) ⟨391967, by rfl⟩ : syracuseStep 522623 = 783935) B783935
theorem B522855 : Blo 519798 522855 := bstep (se 1 (by rfl) ⟨392141, by rfl⟩ : syracuseStep 522855 = 784283) B784283
theorem B1178279 : Blo 519798 1178279 := bstep (se 1 (by rfl) ⟨883709, by rfl⟩ : syracuseStep 1178279 = 1767419) B1767419
theorem B522943 : Blo 519798 522943 := bstep (se 1 (by rfl) ⟨392207, by rfl⟩ : syracuseStep 522943 = 784415) B784415
theorem B1178351 : Blo 519798 1178351 := bstep (se 1 (by rfl) ⟨883763, by rfl⟩ : syracuseStep 1178351 = 1767527) B1767527
theorem B523295 : Blo 519798 523295 := bstep (se 1 (by rfl) ⟨392471, by rfl⟩ : syracuseStep 523295 = 784943) B784943
theorem B16055333 : Blo 519798 16055333 := bstep (se 4 (by rfl) ⟨1505187, by rfl⟩ : syracuseStep 16055333 = 3010375) B3010375
theorem B3341371 : Blo 519798 3341371 := bstep (se 1 (by rfl) ⟨2506028, by rfl⟩ : syracuseStep 3341371 = 5012057) B5012057
theorem B523375 : Blo 519798 523375 := bstep (se 1 (by rfl) ⟨392531, by rfl⟩ : syracuseStep 523375 = 785063) B785063
theorem B523431 : Blo 519798 523431 := bstep (se 1 (by rfl) ⟨392573, by rfl⟩ : syracuseStep 523431 = 785147) B785147
theorem B523455 : Blo 519798 523455 := bstep (se 1 (by rfl) ⟨392591, by rfl⟩ : syracuseStep 523455 = 785183) B785183
theorem B523515 : Blo 519798 523515 := bstep (se 1 (by rfl) ⟨392636, by rfl⟩ : syracuseStep 523515 = 785273) B785273
theorem B523743 : Blo 519798 523743 := bstep (se 1 (by rfl) ⟨392807, by rfl⟩ : syracuseStep 523743 = 785615) B785615
theorem B2981771 : Blo 519798 2981771 := bstep (se 1 (by rfl) ⟨2236328, by rfl⟩ : syracuseStep 2981771 = 4472657) B4472657
theorem B9633725 : Blo 519798 9633725 := bstep (se 3 (by rfl) ⟨1806323, by rfl⟩ : syracuseStep 9633725 = 3612647) B3612647
theorem B1671263 : Blo 519798 1671263 := bstep (se 1 (by rfl) ⟨1253447, by rfl⟩ : syracuseStep 1671263 = 2506895) B2506895
theorem B26083685 : Blo 519798 26083685 := bstep (se 4 (by rfl) ⟨2445345, by rfl⟩ : syracuseStep 26083685 = 4890691) B4890691
theorem B3573215 : Blo 519798 3573215 := bstep (se 1 (by rfl) ⟨2679911, by rfl⟩ : syracuseStep 3573215 = 5359823) B5359823
theorem B3343855 : Blo 519798 3343855 := bstep (se 1 (by rfl) ⟨2507891, by rfl⟩ : syracuseStep 3343855 = 5015783) B5015783
theorem B9996047 : Blo 519798 9996047 := bstep (se 1 (by rfl) ⟨7497035, by rfl⟩ : syracuseStep 9996047 = 14994071) B14994071
theorem B624551 : Blo 519798 624551 := bstep (se 1 (by rfl) ⟨468413, by rfl⟩ : syracuseStep 624551 = 936827) B936827
theorem B5966135 : Blo 519798 5966135 := bstep (se 1 (by rfl) ⟨4474601, by rfl⟩ : syracuseStep 5966135 = 8949203) B8949203
theorem B3180863 : Blo 519798 3180863 := bstep (se 1 (by rfl) ⟨2385647, by rfl⟩ : syracuseStep 3180863 = 4771295) B4771295
theorem B3575465 : Blo 519798 3575465 := bstep (se 2 (by rfl) ⟨1340799, by rfl⟩ : syracuseStep 3575465 = 2681599) B2681599
theorem B3182327 : Blo 519798 3182327 := bstep (se 1 (by rfl) ⟨2386745, by rfl⟩ : syracuseStep 3182327 = 4773491) B4773491
theorem B1118207 : Blo 519798 1118207 := bstep (se 1 (by rfl) ⟨838655, by rfl⟩ : syracuseStep 1118207 = 1677311) B1677311
theorem B3805193 : Blo 519798 3805193 := bstep (se 2 (by rfl) ⟨1426947, by rfl⟩ : syracuseStep 3805193 = 2853895) B2853895
theorem B2003903 : Blo 519798 2003903 := bstep (se 1 (by rfl) ⟨1502927, by rfl⟩ : syracuseStep 2003903 = 3005855) B3005855
theorem B1974253 : Blo 519798 1974253 := bstep (se 3 (by rfl) ⟨370172, by rfl⟩ : syracuseStep 1974253 = 740345) B740345
theorem B991273 : Blo 519798 991273 := bstep (se 2 (by rfl) ⟨371727, by rfl⟩ : syracuseStep 991273 = 743455) B743455
theorem B37988189 : Blo 519798 37988189 := bstep (se 3 (by rfl) ⟨7122785, by rfl⟩ : syracuseStep 37988189 = 14245571) B14245571
theorem B1879795 : Blo 519798 1879795 := bstep (se 1 (by rfl) ⟨1409846, by rfl⟩ : syracuseStep 1879795 = 2819693) B2819693
theorem B9318253 : Blo 519798 9318253 := bstep (se 3 (by rfl) ⟨1747172, by rfl⟩ : syracuseStep 9318253 = 3494345) B3494345
theorem B8892341 : Blo 519798 8892341 := bstep (se 5 (by rfl) ⟨416828, by rfl⟩ : syracuseStep 8892341 = 833657) B833657
theorem B1257407 : Blo 519798 1257407 := bstep (se 1 (by rfl) ⟨943055, by rfl⟩ : syracuseStep 1257407 = 1886111) B1886111
theorem B11252297 : Blo 519798 11252297 := bstep (se 2 (by rfl) ⟨4219611, by rfl⟩ : syracuseStep 11252297 = 8439223) B8439223
theorem B1979099 : Blo 519798 1979099 := bstep (se 1 (by rfl) ⟨1484324, by rfl⟩ : syracuseStep 1979099 = 2968649) B2968649
theorem B1324127 : Blo 519798 1324127 := bstep (se 1 (by rfl) ⟨993095, by rfl⟩ : syracuseStep 1324127 = 1986191) B1986191
theorem B1979599 : Blo 519798 1979599 := bstep (se 1 (by rfl) ⟨1484699, by rfl⟩ : syracuseStep 1979599 = 2969399) B2969399
theorem B15087019 : Blo 519798 15087019 := bstep (se 1 (by rfl) ⟨11315264, by rfl⟩ : syracuseStep 15087019 = 22630529) B22630529
theorem B2636063 : Blo 519798 2636063 := bstep (se 1 (by rfl) ⟨1977047, by rfl⟩ : syracuseStep 2636063 = 3954095) B3954095
theorem B42678895 : Blo 519798 42678895 := bstep (se 1 (by rfl) ⟨32009171, by rfl⟩ : syracuseStep 42678895 = 64018343) B64018343
theorem B1981043 : Blo 519798 1981043 := bstep (se 1 (by rfl) ⟨1485782, by rfl⟩ : syracuseStep 1981043 = 2971565) B2971565
theorem B18266903 : Blo 519798 18266903 := bstep (se 1 (by rfl) ⟨13700177, by rfl⟩ : syracuseStep 18266903 = 27400355) B27400355
theorem B703615 : Blo 519798 703615 := bstep (se 1 (by rfl) ⟨527711, by rfl⟩ : syracuseStep 703615 = 1055423) B1055423
theorem B2506241 : Blo 519798 2506241 := bstep (se 2 (by rfl) ⟨939840, by rfl⟩ : syracuseStep 2506241 = 1879681) B1879681
theorem B2637359 : Blo 519798 2637359 := bstep (se 1 (by rfl) ⟨1978019, by rfl⟩ : syracuseStep 2637359 = 3956039) B3956039
theorem B3948263 : Blo 519798 3948263 := bstep (se 1 (by rfl) ⟨2961197, by rfl⟩ : syracuseStep 3948263 = 5922395) B5922395
theorem B2965481 : Blo 519798 2965481 := bstep (se 2 (by rfl) ⟨1112055, by rfl⟩ : syracuseStep 2965481 = 2224111) B2224111
theorem B6766699 : Blo 519798 6766699 := bstep (se 1 (by rfl) ⟨5075024, by rfl⟩ : syracuseStep 6766699 = 10150049) B10150049
theorem B5030009 : Blo 519798 5030009 := bstep (se 2 (by rfl) ⟨1886253, by rfl⟩ : syracuseStep 5030009 = 3772507) B3772507
theorem B2638493 : Blo 519798 2638493 := bstep (se 3 (by rfl) ⟨494717, by rfl⟩ : syracuseStep 2638493 = 989435) B989435
theorem B6669053 : Blo 519798 6669053 := bstep (se 3 (by rfl) ⟨1250447, by rfl⟩ : syracuseStep 6669053 = 2500895) B2500895
theorem B3819007 : Blo 519798 3819007 := bstep (se 1 (by rfl) ⟨2864255, by rfl⟩ : syracuseStep 3819007 = 5728511) B5728511
theorem B1984247 : Blo 519798 1984247 := bstep (se 1 (by rfl) ⟨1488185, by rfl⟩ : syracuseStep 1984247 = 2976371) B2976371
theorem B1984763 : Blo 519798 1984763 := bstep (se 1 (by rfl) ⟨1488572, by rfl⟩ : syracuseStep 1984763 = 2977145) B2977145
theorem B1690055 : Blo 519798 1690055 := bstep (se 1 (by rfl) ⟨1267541, by rfl⟩ : syracuseStep 1690055 = 2535083) B2535083
theorem B110152219 : Blo 519798 110152219 := bstep (se 1 (by rfl) ⟨82614164, by rfl⟩ : syracuseStep 110152219 = 165228329) B165228329
theorem B1985705 : Blo 519798 1985705 := bstep (se 2 (by rfl) ⟨744639, by rfl⟩ : syracuseStep 1985705 = 1489279) B1489279
theorem B6181541 : Blo 519798 6181541 := bstep (se 4 (by rfl) ⟨579519, by rfl⟩ : syracuseStep 6181541 = 1159039) B1159039
theorem B10703555 : Blo 519798 10703555 := bstep (se 1 (by rfl) ⟨8027666, by rfl⟩ : syracuseStep 10703555 = 16055333) B16055333
theorem B1987847 : Blo 519798 1987847 := bstep (se 1 (by rfl) ⟨1490885, by rfl⟩ : syracuseStep 1987847 = 2981771) B2981771
theorem B1759481 : Blo 519798 1759481 := bstep (se 2 (by rfl) ⟨659805, by rfl⟩ : syracuseStep 1759481 = 1319611) B1319611
theorem B1169801 : Blo 519798 1169801 := bstep (se 2 (by rfl) ⟨438675, by rfl⟩ : syracuseStep 1169801 = 877351) B877351
theorem B1759859 : Blo 519798 1759859 := bstep (se 1 (by rfl) ⟨1319894, by rfl⟩ : syracuseStep 1759859 = 2639789) B2639789
theorem B1170107 : Blo 519798 1170107 := bstep (se 1 (by rfl) ⟨877580, by rfl⟩ : syracuseStep 1170107 = 1755161) B1755161
theorem B1170215 : Blo 519798 1170215 := bstep (se 1 (by rfl) ⟨877661, by rfl⟩ : syracuseStep 1170215 = 1755323) B1755323
theorem B4283239 : Blo 519798 4283239 := bstep (se 1 (by rfl) ⟨3212429, by rfl⟩ : syracuseStep 4283239 = 6424859) B6424859
theorem B20339693 : Blo 519798 20339693 := bstep (se 3 (by rfl) ⟨3813692, by rfl⟩ : syracuseStep 20339693 = 7627385) B7627385
theorem B1171529 : Blo 519798 1171529 := bstep (se 2 (by rfl) ⟨439323, by rfl⟩ : syracuseStep 1171529 = 878647) B878647
theorem B1171655 : Blo 519798 1171655 := bstep (se 1 (by rfl) ⟨878741, by rfl⟩ : syracuseStep 1171655 = 1757483) B1757483
theorem B4023047 : Blo 519798 4023047 := bstep (se 1 (by rfl) ⟨3017285, by rfl⟩ : syracuseStep 4023047 = 6034571) B6034571
theorem B779759 : Blo 519798 779759 := bstep (se 1 (by rfl) ⟨584819, by rfl⟩ : syracuseStep 779759 = 1169639) B1169639
theorem B2975231 : Blo 519798 2975231 := bstep (se 1 (by rfl) ⟨2231423, by rfl⟩ : syracuseStep 2975231 = 4462847) B4462847
theorem B779945 : Blo 519798 779945 := bstep (se 2 (by rfl) ⟨292479, by rfl⟩ : syracuseStep 779945 = 584959) B584959
theorem B1762991 : Blo 519798 1762991 := bstep (se 1 (by rfl) ⟨1322243, by rfl⟩ : syracuseStep 1762991 = 2644487) B2644487
theorem B1173257 : Blo 519798 1173257 := bstep (se 2 (by rfl) ⟨439971, by rfl⟩ : syracuseStep 1173257 = 879943) B879943
theorem B1173419 : Blo 519798 1173419 := bstep (se 1 (by rfl) ⟨880064, by rfl⟩ : syracuseStep 1173419 = 1760129) B1760129
theorem B780329 : Blo 519798 780329 := bstep (se 2 (by rfl) ⟨292623, by rfl⟩ : syracuseStep 780329 = 585247) B585247
theorem B780743 : Blo 519798 780743 := bstep (se 1 (by rfl) ⟨585557, by rfl⟩ : syracuseStep 780743 = 1171115) B1171115
theorem B781223 : Blo 519798 781223 := bstep (se 1 (by rfl) ⟨585917, by rfl⟩ : syracuseStep 781223 = 1171835) B1171835
theorem B1174463 : Blo 519798 1174463 := bstep (se 1 (by rfl) ⟨880847, by rfl⟩ : syracuseStep 1174463 = 1761695) B1761695
theorem B781295 : Blo 519798 781295 := bstep (se 1 (by rfl) ⟨585971, by rfl⟩ : syracuseStep 781295 = 1171943) B1171943
theorem B3337271 : Blo 519798 3337271 := bstep (se 1 (by rfl) ⟨2502953, by rfl⟩ : syracuseStep 3337271 = 5005907) B5005907
theorem B1273159 : Blo 519798 1273159 := bstep (se 1 (by rfl) ⟨954869, by rfl⟩ : syracuseStep 1273159 = 1909739) B1909739
theorem B781961 : Blo 519798 781961 := bstep (se 2 (by rfl) ⟨293235, by rfl⟩ : syracuseStep 781961 = 586471) B586471
theorem B781979 : Blo 519798 781979 := bstep (se 1 (by rfl) ⟨586484, by rfl⟩ : syracuseStep 781979 = 1172969) B1172969
theorem B519847 : Blo 519798 519847 := bstep (se 1 (by rfl) ⟨389885, by rfl⟩ : syracuseStep 519847 = 779771) B779771
theorem B782015 : Blo 519798 782015 := bstep (se 1 (by rfl) ⟨586511, by rfl⟩ : syracuseStep 782015 = 1173023) B1173023
theorem B519919 : Blo 519798 519919 := bstep (se 1 (by rfl) ⟨389939, by rfl⟩ : syracuseStep 519919 = 779879) B779879
theorem B782111 : Blo 519798 782111 := bstep (se 1 (by rfl) ⟨586583, by rfl⟩ : syracuseStep 782111 = 1173167) B1173167
theorem B1175507 : Blo 519798 1175507 := bstep (se 1 (by rfl) ⟨881630, by rfl⟩ : syracuseStep 1175507 = 1763261) B1763261
theorem B1175579 : Blo 519798 1175579 := bstep (se 1 (by rfl) ⟨881684, by rfl⟩ : syracuseStep 1175579 = 1763369) B1763369
theorem B782447 : Blo 519798 782447 := bstep (se 1 (by rfl) ⟨586835, by rfl⟩ : syracuseStep 782447 = 1173671) B1173671
theorem B109801615 : Blo 519798 109801615 := bstep (se 1 (by rfl) ⟨82351211, by rfl⟩ : syracuseStep 109801615 = 164702423) B164702423
theorem B5009633 : Blo 519798 5009633 := bstep (se 2 (by rfl) ⟨1878612, by rfl⟩ : syracuseStep 5009633 = 3757225) B3757225
theorem B782591 : Blo 519798 782591 := bstep (se 1 (by rfl) ⟨586943, by rfl⟩ : syracuseStep 782591 = 1173887) B1173887
theorem B2683343 : Blo 519798 2683343 := bstep (se 1 (by rfl) ⟨2012507, by rfl⟩ : syracuseStep 2683343 = 4025015) B4025015
theorem B782879 : Blo 519798 782879 := bstep (se 1 (by rfl) ⟨587159, by rfl⟩ : syracuseStep 782879 = 1174319) B1174319
theorem B1176119 : Blo 519798 1176119 := bstep (se 1 (by rfl) ⟨882089, by rfl⟩ : syracuseStep 1176119 = 1764179) B1764179
theorem B520831 : Blo 519798 520831 := bstep (se 1 (by rfl) ⟨390623, by rfl⟩ : syracuseStep 520831 = 781247) B781247
theorem B783017 : Blo 519798 783017 := bstep (se 2 (by rfl) ⟨293631, by rfl⟩ : syracuseStep 783017 = 587263) B587263
theorem B520935 : Blo 519798 520935 := bstep (se 1 (by rfl) ⟨390701, by rfl⟩ : syracuseStep 520935 = 781403) B781403
theorem B1176443 : Blo 519798 1176443 := bstep (se 1 (by rfl) ⟨882332, by rfl⟩ : syracuseStep 1176443 = 1764665) B1764665
theorem B783263 : Blo 519798 783263 := bstep (se 1 (by rfl) ⟨587447, by rfl⟩ : syracuseStep 783263 = 1174895) B1174895
theorem B2978855 : Blo 519798 2978855 := bstep (se 1 (by rfl) ⟨2234141, by rfl⟩ : syracuseStep 2978855 = 4468283) B4468283
theorem B1766555 : Blo 519798 1766555 := bstep (se 1 (by rfl) ⟨1324916, by rfl⟩ : syracuseStep 1766555 = 2649833) B2649833
theorem B783743 : Blo 519798 783743 := bstep (se 1 (by rfl) ⟨587807, by rfl⟩ : syracuseStep 783743 = 1175615) B1175615
theorem B1177055 : Blo 519798 1177055 := bstep (se 1 (by rfl) ⟨882791, by rfl⟩ : syracuseStep 1177055 = 1765583) B1765583
theorem B521855 : Blo 519798 521855 := bstep (se 1 (by rfl) ⟨391391, by rfl⟩ : syracuseStep 521855 = 782783) B782783
theorem B521935 : Blo 519798 521935 := bstep (se 1 (by rfl) ⟨391451, by rfl⟩ : syracuseStep 521935 = 782903) B782903
theorem B587623 : Blo 519798 587623 := bstep (se 1 (by rfl) ⟨440717, by rfl⟩ : syracuseStep 587623 = 881435) B881435
theorem B522095 : Blo 519798 522095 := bstep (se 1 (by rfl) ⟨391571, by rfl⟩ : syracuseStep 522095 = 783143) B783143
theorem B1603451 : Blo 519798 1603451 := bstep (se 1 (by rfl) ⟨1202588, by rfl⟩ : syracuseStep 1603451 = 2405177) B2405177
theorem B784607 : Blo 519798 784607 := bstep (se 1 (by rfl) ⟨588455, by rfl⟩ : syracuseStep 784607 = 1176911) B1176911
theorem B522523 : Blo 519798 522523 := bstep (se 1 (by rfl) ⟨391892, by rfl⟩ : syracuseStep 522523 = 783785) B783785
theorem B522559 : Blo 519798 522559 := bstep (se 1 (by rfl) ⟨391919, by rfl⟩ : syracuseStep 522559 = 783839) B783839
theorem B785087 : Blo 519798 785087 := bstep (se 1 (by rfl) ⟨588815, by rfl⟩ : syracuseStep 785087 = 1177631) B1177631
theorem B522991 : Blo 519798 522991 := bstep (se 1 (by rfl) ⟨392243, by rfl⟩ : syracuseStep 522991 = 784487) B784487
theorem B4455161 : Blo 519798 4455161 := bstep (se 2 (by rfl) ⟨1670685, by rfl⟩ : syracuseStep 4455161 = 3341371) B3341371
theorem B785255 : Blo 519798 785255 := bstep (se 1 (by rfl) ⟨588941, by rfl⟩ : syracuseStep 785255 = 1177883) B1177883
theorem B785279 : Blo 519798 785279 := bstep (se 1 (by rfl) ⟨588959, by rfl⟩ : syracuseStep 785279 = 1177919) B1177919
theorem B785519 : Blo 519798 785519 := bstep (se 1 (by rfl) ⟨589139, by rfl⟩ : syracuseStep 785519 = 1178279) B1178279
theorem B785567 : Blo 519798 785567 := bstep (se 1 (by rfl) ⟨589175, by rfl⟩ : syracuseStep 785567 = 1178351) B1178351
theorem B96370397 : Blo 519798 96370397 := bstep (se 3 (by rfl) ⟨18069449, by rfl⟩ : syracuseStep 96370397 = 36138899) B36138899
theorem B6422483 : Blo 519798 6422483 := bstep (se 1 (by rfl) ⟨4816862, by rfl⟩ : syracuseStep 6422483 = 9633725) B9633725
theorem B1114175 : Blo 519798 1114175 := bstep (se 1 (by rfl) ⟨835631, by rfl⟩ : syracuseStep 1114175 = 1671263) B1671263
theorem B4458473 : Blo 519798 4458473 := bstep (se 2 (by rfl) ⟨1671927, by rfl⟩ : syracuseStep 4458473 = 3343855) B3343855
theorem B146869625 : Blo 519798 146869625 := bstep (se 2 (by rfl) ⟨55076109, by rfl⟩ : syracuseStep 146869625 = 110152219) B110152219
theorem B12424337 : Blo 519798 12424337 := bstep (se 2 (by rfl) ⟨4659126, by rfl⟩ : syracuseStep 12424337 = 9318253) B9318253
theorem B1319399 : Blo 519798 1319399 := bstep (se 1 (by rfl) ⟨989549, by rfl⟩ : syracuseStep 1319399 = 1979099) B1979099
theorem B5710985 : Blo 519798 5710985 := bstep (se 2 (by rfl) ⟨2141619, by rfl⟩ : syracuseStep 5710985 = 4283239) B4283239
theorem B1320695 : Blo 519798 1320695 := bstep (se 1 (by rfl) ⟨990521, by rfl⟩ : syracuseStep 1320695 = 1981043) B1981043
theorem B2632175 : Blo 519798 2632175 := bstep (se 1 (by rfl) ⟨1974131, by rfl⟩ : syracuseStep 2632175 = 3948263) B3948263
theorem B2632337 : Blo 519798 2632337 := bstep (se 2 (by rfl) ⟨987126, by rfl⟩ : syracuseStep 2632337 = 1974253) B1974253
theorem B1976987 : Blo 519798 1976987 := bstep (se 1 (by rfl) ⟨1482740, by rfl⟩ : syracuseStep 1976987 = 2965481) B2965481
theorem B1321697 : Blo 519798 1321697 := bstep (se 2 (by rfl) ⟨495636, by rfl⟩ : syracuseStep 1321697 = 991273) B991273
theorem B3353339 : Blo 519798 3353339 := bstep (se 1 (by rfl) ⟨2515004, by rfl⟩ : syracuseStep 3353339 = 5030009) B5030009
theorem B9022265 : Blo 519798 9022265 := bstep (se 2 (by rfl) ⟨3383349, by rfl⟩ : syracuseStep 9022265 = 6766699) B6766699
theorem B1322831 : Blo 519798 1322831 := bstep (se 1 (by rfl) ⟨992123, by rfl⟩ : syracuseStep 1322831 = 1984247) B1984247
theorem B6664031 : Blo 519798 6664031 := bstep (se 1 (by rfl) ⟨4998023, by rfl⟩ : syracuseStep 6664031 = 9996047) B9996047
theorem B1323175 : Blo 519798 1323175 := bstep (se 1 (by rfl) ⟨992381, by rfl⟩ : syracuseStep 1323175 = 1984763) B1984763
theorem B3977423 : Blo 519798 3977423 := bstep (se 1 (by rfl) ⟨2983067, by rfl⟩ : syracuseStep 3977423 = 5966135) B5966135
theorem B1126703 : Blo 519798 1126703 := bstep (se 1 (by rfl) ⟨845027, by rfl⟩ : syracuseStep 1126703 = 1690055) B1690055
theorem B10728125 : Blo 519798 10728125 := bstep (se 3 (by rfl) ⟨2011523, by rfl⟩ : syracuseStep 10728125 = 4023047) B4023047
theorem B1323803 : Blo 519798 1323803 := bstep (se 1 (by rfl) ⟨992852, by rfl⟩ : syracuseStep 1323803 = 1985705) B1985705
theorem B2536795 : Blo 519798 2536795 := bstep (se 1 (by rfl) ⟨1902596, by rfl⟩ : syracuseStep 2536795 = 3805193) B3805193
theorem B1325231 : Blo 519798 1325231 := bstep (se 1 (by rfl) ⟨993923, by rfl⟩ : syracuseStep 1325231 = 1987847) B1987847
theorem B2506393 : Blo 519798 2506393 := bstep (se 2 (by rfl) ⟨939897, by rfl⟩ : syracuseStep 2506393 = 1879795) B1879795
theorem B1983487 : Blo 519798 1983487 := bstep (se 1 (by rfl) ⟨1487615, by rfl⟩ : syracuseStep 1983487 = 2975231) B2975231
theorem B2639465 : Blo 519798 2639465 := bstep (se 2 (by rfl) ⟨989799, by rfl⟩ : syracuseStep 2639465 = 1979599) B1979599
theorem B838271 : Blo 519798 838271 := bstep (se 1 (by rfl) ⟨628703, by rfl⟩ : syracuseStep 838271 = 1257407) B1257407
theorem B20368037 : Blo 519798 20368037 := bstep (se 4 (by rfl) ⟨1909503, by rfl⟩ : syracuseStep 20368037 = 3819007) B3819007
theorem B1788895 : Blo 519798 1788895 := bstep (se 1 (by rfl) ⟨1341671, by rfl⟩ : syracuseStep 1788895 = 2683343) B2683343
theorem B1985903 : Blo 519798 1985903 := bstep (se 1 (by rfl) ⟨1489427, by rfl⟩ : syracuseStep 1985903 = 2978855) B2978855
theorem B56905193 : Blo 519798 56905193 := bstep (se 2 (by rfl) ⟨21339447, by rfl⟩ : syracuseStep 56905193 = 42678895) B42678895
theorem B1068967 : Blo 519798 1068967 := bstep (se 1 (by rfl) ⟨801725, by rfl⟩ : syracuseStep 1068967 = 1603451) B1603451
theorem B938153 : Blo 519798 938153 := bstep (se 2 (by rfl) ⟨351807, by rfl⟩ : syracuseStep 938153 = 703615) B703615
theorem B1757375 : Blo 519798 1757375 := bstep (se 1 (by rfl) ⟨1318031, by rfl⟩ : syracuseStep 1757375 = 2636063) B2636063
theorem B2970107 : Blo 519798 2970107 := bstep (se 1 (by rfl) ⟨2227580, by rfl⟩ : syracuseStep 2970107 = 4455161) B4455161
theorem B12177935 : Blo 519798 12177935 := bstep (se 1 (by rfl) ⟨9133451, by rfl⟩ : syracuseStep 12177935 = 18266903) B18266903
theorem B1758239 : Blo 519798 1758239 := bstep (se 1 (by rfl) ⟨1318679, by rfl⟩ : syracuseStep 1758239 = 2637359) B2637359
theorem B64246931 : Blo 519798 64246931 := bstep (se 1 (by rfl) ⟨48185198, by rfl⟩ : syracuseStep 64246931 = 96370397) B96370397
theorem B4281655 : Blo 519798 4281655 := bstep (se 1 (by rfl) ⟨3211241, by rfl⟩ : syracuseStep 4281655 = 6422483) B6422483
theorem B1758995 : Blo 519798 1758995 := bstep (se 1 (by rfl) ⟨1319246, by rfl⟩ : syracuseStep 1758995 = 2638493) B2638493
theorem B4446035 : Blo 519798 4446035 := bstep (se 1 (by rfl) ⟨3334526, by rfl⟩ : syracuseStep 4446035 = 6669053) B6669053
theorem B69556493 : Blo 519798 69556493 := bstep (se 3 (by rfl) ⟨13041842, by rfl⟩ : syracuseStep 69556493 = 26083685) B26083685
theorem B2382143 : Blo 519798 2382143 := bstep (se 1 (by rfl) ⟨1786607, by rfl⟩ : syracuseStep 2382143 = 3573215) B3573215
theorem B2120575 : Blo 519798 2120575 := bstep (se 1 (by rfl) ⟨1590431, by rfl⟩ : syracuseStep 2120575 = 3180863) B3180863
theorem B2383643 : Blo 519798 2383643 := bstep (se 1 (by rfl) ⟨1787732, by rfl⟩ : syracuseStep 2383643 = 3575465) B3575465
theorem B2121551 : Blo 519798 2121551 := bstep (se 1 (by rfl) ⟨1591163, by rfl⟩ : syracuseStep 2121551 = 3182327) B3182327
theorem B745471 : Blo 519798 745471 := bstep (se 1 (by rfl) ⟨559103, by rfl⟩ : syracuseStep 745471 = 1118207) B1118207
theorem B4121027 : Blo 519798 4121027 := bstep (se 1 (by rfl) ⟨3090770, by rfl⟩ : syracuseStep 4121027 = 6181541) B6181541
theorem B7135703 : Blo 519798 7135703 := bstep (se 1 (by rfl) ⟨5351777, by rfl⟩ : syracuseStep 7135703 = 10703555) B10703555
theorem B1335935 : Blo 519798 1335935 := bstep (se 1 (by rfl) ⟨1001951, by rfl⟩ : syracuseStep 1335935 = 2003903) B2003903
theorem B1172987 : Blo 519798 1172987 := bstep (se 1 (by rfl) ⟨879740, by rfl⟩ : syracuseStep 1172987 = 1759481) B1759481
theorem B779867 : Blo 519798 779867 := bstep (se 1 (by rfl) ⟨584900, by rfl⟩ : syracuseStep 779867 = 1169801) B1169801
theorem B1173239 : Blo 519798 1173239 := bstep (se 1 (by rfl) ⟨879929, by rfl⟩ : syracuseStep 1173239 = 1759859) B1759859
theorem B1697545 : Blo 519798 1697545 := bstep (se 2 (by rfl) ⟨636579, by rfl⟩ : syracuseStep 1697545 = 1273159) B1273159
theorem B780071 : Blo 519798 780071 := bstep (se 1 (by rfl) ⟨585053, by rfl⟩ : syracuseStep 780071 = 1170107) B1170107
theorem B780143 : Blo 519798 780143 := bstep (se 1 (by rfl) ⟨585107, by rfl⟩ : syracuseStep 780143 = 1170215) B1170215
theorem B13559795 : Blo 519798 13559795 := bstep (se 1 (by rfl) ⟨10169846, by rfl⟩ : syracuseStep 13559795 = 20339693) B20339693
theorem B1665469 : Blo 519798 1665469 := bstep (se 3 (by rfl) ⟨312275, by rfl⟩ : syracuseStep 1665469 = 624551) B624551
theorem B781019 : Blo 519798 781019 := bstep (se 1 (by rfl) ⟨585764, by rfl⟩ : syracuseStep 781019 = 1171529) B1171529
theorem B781103 : Blo 519798 781103 := bstep (se 1 (by rfl) ⟨585827, by rfl⟩ : syracuseStep 781103 = 1171655) B1171655
theorem B146402153 : Blo 519798 146402153 := bstep (se 2 (by rfl) ⟨54900807, by rfl⟩ : syracuseStep 146402153 = 109801615) B109801615
theorem B519839 : Blo 519798 519839 := bstep (se 1 (by rfl) ⟨389879, by rfl⟩ : syracuseStep 519839 = 779759) B779759
theorem B519963 : Blo 519798 519963 := bstep (se 1 (by rfl) ⟨389972, by rfl⟩ : syracuseStep 519963 = 779945) B779945
theorem B1175327 : Blo 519798 1175327 := bstep (se 1 (by rfl) ⟨881495, by rfl⟩ : syracuseStep 1175327 = 1762991) B1762991
theorem B782171 : Blo 519798 782171 := bstep (se 1 (by rfl) ⟨586628, by rfl⟩ : syracuseStep 782171 = 1173257) B1173257
theorem B25325459 : Blo 519798 25325459 := bstep (se 1 (by rfl) ⟨18994094, by rfl⟩ : syracuseStep 25325459 = 37988189) B37988189
theorem B782279 : Blo 519798 782279 := bstep (se 1 (by rfl) ⟨586709, by rfl⟩ : syracuseStep 782279 = 1173419) B1173419
theorem B520219 : Blo 519798 520219 := bstep (se 1 (by rfl) ⟨390164, by rfl⟩ : syracuseStep 520219 = 780329) B780329
theorem B520495 : Blo 519798 520495 := bstep (se 1 (by rfl) ⟨390371, by rfl⟩ : syracuseStep 520495 = 780743) B780743
theorem B20116025 : Blo 519798 20116025 := bstep (se 2 (by rfl) ⟨7543509, by rfl⟩ : syracuseStep 20116025 = 15087019) B15087019
theorem B520815 : Blo 519798 520815 := bstep (se 1 (by rfl) ⟨390611, by rfl⟩ : syracuseStep 520815 = 781223) B781223
theorem B782975 : Blo 519798 782975 := bstep (se 1 (by rfl) ⟨587231, by rfl⟩ : syracuseStep 782975 = 1174463) B1174463
theorem B520863 : Blo 519798 520863 := bstep (se 1 (by rfl) ⟨390647, by rfl⟩ : syracuseStep 520863 = 781295) B781295
theorem B2224847 : Blo 519798 2224847 := bstep (se 1 (by rfl) ⟨1668635, by rfl⟩ : syracuseStep 2224847 = 3337271) B3337271
theorem B521307 : Blo 519798 521307 := bstep (se 1 (by rfl) ⟨390980, by rfl⟩ : syracuseStep 521307 = 781961) B781961
theorem B521319 : Blo 519798 521319 := bstep (se 1 (by rfl) ⟨390989, by rfl⟩ : syracuseStep 521319 = 781979) B781979
theorem B521343 : Blo 519798 521343 := bstep (se 1 (by rfl) ⟨391007, by rfl⟩ : syracuseStep 521343 = 782015) B782015
theorem B783497 : Blo 519798 783497 := bstep (se 2 (by rfl) ⟨293811, by rfl⟩ : syracuseStep 783497 = 587623) B587623
theorem B521407 : Blo 519798 521407 := bstep (se 1 (by rfl) ⟨391055, by rfl⟩ : syracuseStep 521407 = 782111) B782111
theorem B5928227 : Blo 519798 5928227 := bstep (se 1 (by rfl) ⟨4446170, by rfl⟩ : syracuseStep 5928227 = 8892341) B8892341
theorem B783671 : Blo 519798 783671 := bstep (se 1 (by rfl) ⟨587753, by rfl⟩ : syracuseStep 783671 = 1175507) B1175507
theorem B783719 : Blo 519798 783719 := bstep (se 1 (by rfl) ⟨587789, by rfl⟩ : syracuseStep 783719 = 1175579) B1175579
theorem B521631 : Blo 519798 521631 := bstep (se 1 (by rfl) ⟨391223, by rfl⟩ : syracuseStep 521631 = 782447) B782447
theorem B3339755 : Blo 519798 3339755 := bstep (se 1 (by rfl) ⟨2504816, by rfl⟩ : syracuseStep 3339755 = 5009633) B5009633
theorem B521727 : Blo 519798 521727 := bstep (se 1 (by rfl) ⟨391295, by rfl⟩ : syracuseStep 521727 = 782591) B782591
theorem B521919 : Blo 519798 521919 := bstep (se 1 (by rfl) ⟨391439, by rfl⟩ : syracuseStep 521919 = 782879) B782879
theorem B784079 : Blo 519798 784079 := bstep (se 1 (by rfl) ⟨588059, by rfl⟩ : syracuseStep 784079 = 1176119) B1176119
theorem B7501531 : Blo 519798 7501531 := bstep (se 1 (by rfl) ⟨5626148, by rfl⟩ : syracuseStep 7501531 = 11252297) B11252297
theorem B522011 : Blo 519798 522011 := bstep (se 1 (by rfl) ⟨391508, by rfl⟩ : syracuseStep 522011 = 783017) B783017
theorem B784295 : Blo 519798 784295 := bstep (se 1 (by rfl) ⟨588221, by rfl⟩ : syracuseStep 784295 = 1176443) B1176443
theorem B522175 : Blo 519798 522175 := bstep (se 1 (by rfl) ⟨391631, by rfl⟩ : syracuseStep 522175 = 783263) B783263
theorem B882751 : Blo 519798 882751 := bstep (se 1 (by rfl) ⟨662063, by rfl⟩ : syracuseStep 882751 = 1324127) B1324127
theorem B1177703 : Blo 519798 1177703 := bstep (se 1 (by rfl) ⟨883277, by rfl⟩ : syracuseStep 1177703 = 1766555) B1766555
theorem B522495 : Blo 519798 522495 := bstep (se 1 (by rfl) ⟨391871, by rfl⟩ : syracuseStep 522495 = 783743) B783743
theorem B784703 : Blo 519798 784703 := bstep (se 1 (by rfl) ⟨588527, by rfl⟩ : syracuseStep 784703 = 1177055) B1177055
theorem B523071 : Blo 519798 523071 := bstep (se 1 (by rfl) ⟨392303, by rfl⟩ : syracuseStep 523071 = 784607) B784607
theorem B523391 : Blo 519798 523391 := bstep (se 1 (by rfl) ⟨392543, by rfl⟩ : syracuseStep 523391 = 785087) B785087
theorem B523503 : Blo 519798 523503 := bstep (se 1 (by rfl) ⟨392627, by rfl⟩ : syracuseStep 523503 = 785255) B785255
theorem B523519 : Blo 519798 523519 := bstep (se 1 (by rfl) ⟨392639, by rfl⟩ : syracuseStep 523519 = 785279) B785279
theorem B523679 : Blo 519798 523679 := bstep (se 1 (by rfl) ⟨392759, by rfl⟩ : syracuseStep 523679 = 785519) B785519
theorem B523711 : Blo 519798 523711 := bstep (se 1 (by rfl) ⟨392783, by rfl⟩ : syracuseStep 523711 = 785567) B785567
theorem B1670827 : Blo 519798 1670827 := bstep (se 1 (by rfl) ⟨1253120, by rfl⟩ : syracuseStep 1670827 = 2506241) B2506241
theorem B558847 : Blo 519798 558847 := bstep (se 1 (by rfl) ⟨419135, by rfl⟩ : syracuseStep 558847 = 838271) B838271
theorem B97913083 : Blo 519798 97913083 := bstep (se 1 (by rfl) ⟨73434812, by rfl⟩ : syracuseStep 97913083 = 146869625) B146869625
theorem B2263393 : Blo 519798 2263393 := bstep (se 2 (by rfl) ⟨848772, by rfl⟩ : syracuseStep 2263393 = 1697545) B1697545
theorem B42831287 : Blo 519798 42831287 := bstep (se 1 (by rfl) ⟨32123465, by rfl⟩ : syracuseStep 42831287 = 64246931) B64246931
theorem B9540773 : Blo 519798 9540773 := bstep (se 4 (by rfl) ⟨894447, by rfl⟩ : syracuseStep 9540773 = 1788895) B1788895
theorem B1414367 : Blo 519798 1414367 := bstep (se 1 (by rfl) ⟨1060775, by rfl⟩ : syracuseStep 1414367 = 2121551) B2121551
theorem B4757135 : Blo 519798 4757135 := bstep (se 1 (by rfl) ⟨3567851, by rfl⟩ : syracuseStep 4757135 = 7135703) B7135703
theorem B890623 : Blo 519798 890623 := bstep (se 1 (by rfl) ⟨667967, by rfl⟩ : syracuseStep 890623 = 1335935) B1335935
theorem B3807323 : Blo 519798 3807323 := bstep (se 1 (by rfl) ⟨2855492, by rfl⟩ : syracuseStep 3807323 = 5710985) B5710985
theorem B5708873 : Blo 519798 5708873 := bstep (se 2 (by rfl) ⟨2140827, by rfl⟩ : syracuseStep 5708873 = 4281655) B4281655
theorem B1317991 : Blo 519798 1317991 := bstep (se 1 (by rfl) ⟨988493, by rfl⟩ : syracuseStep 1317991 = 1976987) B1976987
theorem B3382393 : Blo 519798 3382393 := bstep (se 2 (by rfl) ⟨1268397, by rfl⟩ : syracuseStep 3382393 = 2536795) B2536795
theorem B2235559 : Blo 519798 2235559 := bstep (se 1 (by rfl) ⟨1676669, by rfl⟩ : syracuseStep 2235559 = 3353339) B3353339
theorem B10002041 : Blo 519798 10002041 := bstep (se 2 (by rfl) ⟨3750765, by rfl⟩ : syracuseStep 10002041 = 7501531) B7501531
theorem B16883639 : Blo 519798 16883639 := bstep (se 1 (by rfl) ⟨12662729, by rfl⟩ : syracuseStep 16883639 = 25325459) B25325459
theorem B13410683 : Blo 519798 13410683 := bstep (se 1 (by rfl) ⟨10058012, by rfl⟩ : syracuseStep 13410683 = 20116025) B20116025
theorem B7152083 : Blo 519798 7152083 := bstep (se 1 (by rfl) ⟨5364062, by rfl⟩ : syracuseStep 7152083 = 10728125) B10728125
theorem B1483231 : Blo 519798 1483231 := bstep (se 1 (by rfl) ⟨1112423, by rfl⟩ : syracuseStep 1483231 = 2224847) B2224847
theorem B2827433 : Blo 519798 2827433 := bstep (se 2 (by rfl) ⟨1060287, by rfl⟩ : syracuseStep 2827433 = 2120575) B2120575
theorem B993961 : Blo 519798 993961 := bstep (se 2 (by rfl) ⟨372735, by rfl⟩ : syracuseStep 993961 = 745471) B745471
theorem B2501741 : Blo 519798 2501741 := bstep (se 3 (by rfl) ⟨469076, by rfl⟩ : syracuseStep 2501741 = 938153) B938153
theorem B13578691 : Blo 519798 13578691 := bstep (se 1 (by rfl) ⟨10184018, by rfl⟩ : syracuseStep 13578691 = 20368037) B20368037
theorem B1323935 : Blo 519798 1323935 := bstep (se 1 (by rfl) ⟨992951, by rfl⟩ : syracuseStep 1323935 = 1985903) B1985903
theorem B1980071 : Blo 519798 1980071 := bstep (se 1 (by rfl) ⟨1485053, by rfl⟩ : syracuseStep 1980071 = 2970107) B2970107
theorem B2964023 : Blo 519798 2964023 := bstep (se 1 (by rfl) ⟨2223017, by rfl⟩ : syracuseStep 2964023 = 4446035) B4446035
theorem B1589095 : Blo 519798 1589095 := bstep (se 1 (by rfl) ⟨1191821, by rfl⟩ : syracuseStep 1589095 = 2383643) B2383643
theorem B1425289 : Blo 519798 1425289 := bstep (se 2 (by rfl) ⟨534483, by rfl⟩ : syracuseStep 1425289 = 1068967) B1068967
theorem B185483981 : Blo 519798 185483981 := bstep (se 3 (by rfl) ⟨34778246, by rfl⟩ : syracuseStep 185483981 = 69556493) B69556493
theorem B1754783 : Blo 519798 1754783 := bstep (se 1 (by rfl) ⟨1316087, by rfl⟩ : syracuseStep 1754783 = 2632175) B2632175
theorem B1754891 : Blo 519798 1754891 := bstep (se 1 (by rfl) ⟨1316168, by rfl⟩ : syracuseStep 1754891 = 2632337) B2632337
theorem B6014843 : Blo 519798 6014843 := bstep (se 1 (by rfl) ⟨4511132, by rfl⟩ : syracuseStep 6014843 = 9022265) B9022265
theorem B97601435 : Blo 519798 97601435 := bstep (se 1 (by rfl) ⟨73201076, by rfl⟩ : syracuseStep 97601435 = 146402153) B146402153
theorem B4442687 : Blo 519798 4442687 := bstep (se 1 (by rfl) ⟨3332015, by rfl⟩ : syracuseStep 4442687 = 6664031) B6664031
theorem B3952151 : Blo 519798 3952151 := bstep (se 1 (by rfl) ⟨2964113, by rfl⟩ : syracuseStep 3952151 = 5928227) B5928227
theorem B742783 : Blo 519798 742783 := bstep (se 1 (by rfl) ⟨557087, by rfl⟩ : syracuseStep 742783 = 1114175) B1114175
theorem B1759643 : Blo 519798 1759643 := bstep (se 1 (by rfl) ⟨1319732, by rfl⟩ : syracuseStep 1759643 = 2639465) B2639465
theorem B2972315 : Blo 519798 2972315 := bstep (se 1 (by rfl) ⟨2229236, by rfl⟩ : syracuseStep 2972315 = 4458473) B4458473
theorem B2644649 : Blo 519798 2644649 := bstep (se 2 (by rfl) ⟨991743, by rfl⟩ : syracuseStep 2644649 = 1983487) B1983487
theorem B37936795 : Blo 519798 37936795 := bstep (se 1 (by rfl) ⟨28452596, by rfl⟩ : syracuseStep 37936795 = 56905193) B56905193
theorem B1171583 : Blo 519798 1171583 := bstep (se 1 (by rfl) ⟨878687, by rfl⟩ : syracuseStep 1171583 = 1757375) B1757375
theorem B8118623 : Blo 519798 8118623 := bstep (se 1 (by rfl) ⟨6088967, by rfl⟩ : syracuseStep 8118623 = 12177935) B12177935
theorem B2220625 : Blo 519798 2220625 := bstep (se 2 (by rfl) ⟨832734, by rfl⟩ : syracuseStep 2220625 = 1665469) B1665469
theorem B1172159 : Blo 519798 1172159 := bstep (se 1 (by rfl) ⟨879119, by rfl⟩ : syracuseStep 1172159 = 1758239) B1758239
theorem B8282891 : Blo 519798 8282891 := bstep (se 1 (by rfl) ⟨6212168, by rfl⟩ : syracuseStep 8282891 = 12424337) B12424337
theorem B1172663 : Blo 519798 1172663 := bstep (se 1 (by rfl) ⟨879497, by rfl⟩ : syracuseStep 1172663 = 1758995) B1758995
theorem B1764233 : Blo 519798 1764233 := bstep (se 2 (by rfl) ⟨661587, by rfl⟩ : syracuseStep 1764233 = 1323175) B1323175
theorem B2747351 : Blo 519798 2747351 := bstep (se 1 (by rfl) ⟨2060513, by rfl⟩ : syracuseStep 2747351 = 4121027) B4121027
theorem B879599 : Blo 519798 879599 := bstep (se 1 (by rfl) ⟨659699, by rfl⟩ : syracuseStep 879599 = 1319399) B1319399
theorem B6352381 : Blo 519798 6352381 := bstep (se 3 (by rfl) ⟨1191071, by rfl⟩ : syracuseStep 6352381 = 2382143) B2382143
theorem B781991 : Blo 519798 781991 := bstep (se 1 (by rfl) ⟨586493, by rfl⟩ : syracuseStep 781991 = 1172987) B1172987
theorem B519911 : Blo 519798 519911 := bstep (se 1 (by rfl) ⟨389933, by rfl⟩ : syracuseStep 519911 = 779867) B779867
theorem B782159 : Blo 519798 782159 := bstep (se 1 (by rfl) ⟨586619, by rfl⟩ : syracuseStep 782159 = 1173239) B1173239
theorem B880463 : Blo 519798 880463 := bstep (se 1 (by rfl) ⟨660347, by rfl⟩ : syracuseStep 880463 = 1320695) B1320695
theorem B520047 : Blo 519798 520047 := bstep (se 1 (by rfl) ⟨390035, by rfl⟩ : syracuseStep 520047 = 780071) B780071
theorem B520095 : Blo 519798 520095 := bstep (se 1 (by rfl) ⟨390071, by rfl⟩ : syracuseStep 520095 = 780143) B780143
theorem B9039863 : Blo 519798 9039863 := bstep (se 1 (by rfl) ⟨6779897, by rfl⟩ : syracuseStep 9039863 = 13559795) B13559795
theorem B520679 : Blo 519798 520679 := bstep (se 1 (by rfl) ⟨390509, by rfl⟩ : syracuseStep 520679 = 781019) B781019
theorem B881131 : Blo 519798 881131 := bstep (se 1 (by rfl) ⟨660848, by rfl⟩ : syracuseStep 881131 = 1321697) B1321697
theorem B520735 : Blo 519798 520735 := bstep (se 1 (by rfl) ⟨390551, by rfl⟩ : syracuseStep 520735 = 781103) B781103
theorem B783551 : Blo 519798 783551 := bstep (se 1 (by rfl) ⟨587663, by rfl⟩ : syracuseStep 783551 = 1175327) B1175327
theorem B881887 : Blo 519798 881887 := bstep (se 1 (by rfl) ⟨661415, by rfl⟩ : syracuseStep 881887 = 1322831) B1322831
theorem B521447 : Blo 519798 521447 := bstep (se 1 (by rfl) ⟨391085, by rfl⟩ : syracuseStep 521447 = 782171) B782171
theorem B521519 : Blo 519798 521519 := bstep (se 1 (by rfl) ⟨391139, by rfl⟩ : syracuseStep 521519 = 782279) B782279
theorem B1177001 : Blo 519798 1177001 := bstep (se 2 (by rfl) ⟨441375, by rfl⟩ : syracuseStep 1177001 = 882751) B882751
theorem B2651615 : Blo 519798 2651615 := bstep (se 1 (by rfl) ⟨1988711, by rfl⟩ : syracuseStep 2651615 = 3977423) B3977423
theorem B751135 : Blo 519798 751135 := bstep (se 1 (by rfl) ⟨563351, by rfl⟩ : syracuseStep 751135 = 1126703) B1126703
theorem B521983 : Blo 519798 521983 := bstep (se 1 (by rfl) ⟨391487, by rfl⟩ : syracuseStep 521983 = 782975) B782975
theorem B882535 : Blo 519798 882535 := bstep (se 1 (by rfl) ⟨661901, by rfl⟩ : syracuseStep 882535 = 1323803) B1323803
theorem B522331 : Blo 519798 522331 := bstep (se 1 (by rfl) ⟨391748, by rfl⟩ : syracuseStep 522331 = 783497) B783497
theorem B522447 : Blo 519798 522447 := bstep (se 1 (by rfl) ⟨391835, by rfl⟩ : syracuseStep 522447 = 783671) B783671
theorem B522479 : Blo 519798 522479 := bstep (se 1 (by rfl) ⟨391859, by rfl⟩ : syracuseStep 522479 = 783719) B783719
theorem B2226503 : Blo 519798 2226503 := bstep (se 1 (by rfl) ⟨1669877, by rfl⟩ : syracuseStep 2226503 = 3339755) B3339755
theorem B522719 : Blo 519798 522719 := bstep (se 1 (by rfl) ⟨392039, by rfl⟩ : syracuseStep 522719 = 784079) B784079
theorem B522863 : Blo 519798 522863 := bstep (se 1 (by rfl) ⟨392147, by rfl⟩ : syracuseStep 522863 = 784295) B784295
theorem B785135 : Blo 519798 785135 := bstep (se 1 (by rfl) ⟨588851, by rfl⟩ : syracuseStep 785135 = 1177703) B1177703
theorem B883487 : Blo 519798 883487 := bstep (se 1 (by rfl) ⟨662615, by rfl⟩ : syracuseStep 883487 = 1325231) B1325231
theorem B523135 : Blo 519798 523135 := bstep (se 1 (by rfl) ⟨392351, by rfl⟩ : syracuseStep 523135 = 784703) B784703
theorem B3341857 : Blo 519798 3341857 := bstep (se 2 (by rfl) ⟨1253196, by rfl⟩ : syracuseStep 3341857 = 2506393) B2506393
theorem B2227769 : Blo 519798 2227769 := bstep (se 2 (by rfl) ⟨835413, by rfl⟩ : syracuseStep 2227769 = 1670827) B1670827
theorem B22087709 : Blo 519798 22087709 := bstep (se 3 (by rfl) ⟨4141445, by rfl⟩ : syracuseStep 22087709 = 8282891) B8282891
theorem B130550777 : Blo 519798 130550777 := bstep (se 2 (by rfl) ⟨48956541, by rfl⟩ : syracuseStep 130550777 = 97913083) B97913083
theorem B3017857 : Blo 519798 3017857 := bstep (se 2 (by rfl) ⟨1131696, by rfl⟩ : syracuseStep 3017857 = 2263393) B2263393
theorem B6360515 : Blo 519798 6360515 := bstep (se 1 (by rfl) ⟨4770386, by rfl⟩ : syracuseStep 6360515 = 9540773) B9540773
theorem B3805915 : Blo 519798 3805915 := bstep (se 1 (by rfl) ⟨2854436, by rfl⟩ : syracuseStep 3805915 = 5708873) B5708873
theorem B5412415 : Blo 519798 5412415 := bstep (se 1 (by rfl) ⟨4059311, by rfl⟩ : syracuseStep 5412415 = 8118623) B8118623
theorem B990377 : Blo 519798 990377 := bstep (se 2 (by rfl) ⟨371391, by rfl⟩ : syracuseStep 990377 = 742783) B742783
theorem B1187497 : Blo 519798 1187497 := bstep (se 2 (by rfl) ⟨445311, by rfl⟩ : syracuseStep 1187497 = 890623) B890623
theorem B1320047 : Blo 519798 1320047 := bstep (se 1 (by rfl) ⟨990035, by rfl⟩ : syracuseStep 1320047 = 1980071) B1980071
theorem B1484335 : Blo 519798 1484335 := bstep (se 1 (by rfl) ⟨1113251, by rfl⟩ : syracuseStep 1484335 = 2226503) B2226503
theorem B1976015 : Blo 519798 1976015 := bstep (se 1 (by rfl) ⟨1482011, by rfl⟩ : syracuseStep 1976015 = 2964023) B2964023
theorem B1485179 : Blo 519798 1485179 := bstep (se 1 (by rfl) ⟨1113884, by rfl⟩ : syracuseStep 1485179 = 2227769) B2227769
theorem B1977641 : Blo 519798 1977641 := bstep (se 2 (by rfl) ⟨741615, by rfl⟩ : syracuseStep 1977641 = 1483231) B1483231
theorem B2960833 : Blo 519798 2960833 := bstep (se 2 (by rfl) ⟨1110312, by rfl⟩ : syracuseStep 2960833 = 2220625) B2220625
theorem B4009895 : Blo 519798 4009895 := bstep (se 1 (by rfl) ⟨3007421, by rfl⟩ : syracuseStep 4009895 = 6014843) B6014843
theorem B2961791 : Blo 519798 2961791 := bstep (se 1 (by rfl) ⟨2221343, by rfl⟩ : syracuseStep 2961791 = 4442687) B4442687
theorem B28554191 : Blo 519798 28554191 := bstep (se 1 (by rfl) ⟨21415643, by rfl⟩ : syracuseStep 28554191 = 42831287) B42831287
theorem B2634767 : Blo 519798 2634767 := bstep (se 1 (by rfl) ⟨1976075, by rfl⟩ : syracuseStep 2634767 = 3952151) B3952151
theorem B1325281 : Blo 519798 1325281 := bstep (se 2 (by rfl) ⟨496980, by rfl⟩ : syracuseStep 1325281 = 993961) B993961
theorem B2538215 : Blo 519798 2538215 := bstep (se 1 (by rfl) ⟨1903661, by rfl⟩ : syracuseStep 2538215 = 3807323) B3807323
theorem B1981543 : Blo 519798 1981543 := bstep (se 1 (by rfl) ⟨1486157, by rfl⟩ : syracuseStep 1981543 = 2972315) B2972315
theorem B8469841 : Blo 519798 8469841 := bstep (se 2 (by rfl) ⟨3176190, by rfl⟩ : syracuseStep 8469841 = 6352381) B6352381
theorem B6668027 : Blo 519798 6668027 := bstep (se 1 (by rfl) ⟨5001020, by rfl⟩ : syracuseStep 6668027 = 10002041) B10002041
theorem B11255759 : Blo 519798 11255759 := bstep (se 1 (by rfl) ⟨8441819, by rfl⟩ : syracuseStep 11255759 = 16883639) B16883639
theorem B4768055 : Blo 519798 4768055 := bstep (se 1 (by rfl) ⟨3576041, by rfl⟩ : syracuseStep 4768055 = 7152083) B7152083
theorem B18104921 : Blo 519798 18104921 := bstep (se 2 (by rfl) ⟨6789345, by rfl⟩ : syracuseStep 18104921 = 13578691) B13578691
theorem B1884955 : Blo 519798 1884955 := bstep (se 1 (by rfl) ⟨1413716, by rfl⟩ : syracuseStep 1884955 = 2827433) B2827433
theorem B50742773 : Blo 519798 50742773 := bstep (se 5 (by rfl) ⟨2378567, by rfl⟩ : syracuseStep 50742773 = 4757135) B4757135
theorem B1001513 : Blo 519798 1001513 := bstep (se 2 (by rfl) ⟨375567, by rfl⟩ : syracuseStep 1001513 = 751135) B751135
theorem B1757321 : Blo 519798 1757321 := bstep (se 2 (by rfl) ⟨658995, by rfl⟩ : syracuseStep 1757321 = 1317991) B1317991
theorem B4509857 : Blo 519798 4509857 := bstep (se 2 (by rfl) ⟨1691196, by rfl⟩ : syracuseStep 4509857 = 3382393) B3382393
theorem B50582393 : Blo 519798 50582393 := bstep (se 2 (by rfl) ⟨18968397, by rfl⟩ : syracuseStep 50582393 = 37936795) B37936795
theorem B2118793 : Blo 519798 2118793 := bstep (se 2 (by rfl) ⟨794547, by rfl⟩ : syracuseStep 2118793 = 1589095) B1589095
theorem B123655987 : Blo 519798 123655987 := bstep (se 1 (by rfl) ⟨92741990, by rfl⟩ : syracuseStep 123655987 = 185483981) B185483981
theorem B1169855 : Blo 519798 1169855 := bstep (se 1 (by rfl) ⟨877391, by rfl⟩ : syracuseStep 1169855 = 1754783) B1754783
theorem B1169927 : Blo 519798 1169927 := bstep (se 1 (by rfl) ⟨877445, by rfl⟩ : syracuseStep 1169927 = 1754891) B1754891
theorem B65067623 : Blo 519798 65067623 := bstep (se 1 (by rfl) ⟨48800717, by rfl⟩ : syracuseStep 65067623 = 97601435) B97601435
theorem B745129 : Blo 519798 745129 := bstep (se 2 (by rfl) ⟨279423, by rfl⟩ : syracuseStep 745129 = 558847) B558847
theorem B942911 : Blo 519798 942911 := bstep (se 1 (by rfl) ⟨707183, by rfl⟩ : syracuseStep 942911 = 1414367) B1414367
theorem B1173095 : Blo 519798 1173095 := bstep (se 1 (by rfl) ⟨879821, by rfl⟩ : syracuseStep 1173095 = 1759643) B1759643
theorem B1763099 : Blo 519798 1763099 := bstep (se 1 (by rfl) ⟨1322324, by rfl⟩ : syracuseStep 1763099 = 2644649) B2644649
theorem B781055 : Blo 519798 781055 := bstep (se 1 (by rfl) ⟨585791, by rfl⟩ : syracuseStep 781055 = 1171583) B1171583
theorem B8940455 : Blo 519798 8940455 := bstep (se 1 (by rfl) ⟨6705341, by rfl⟩ : syracuseStep 8940455 = 13410683) B13410683
theorem B781439 : Blo 519798 781439 := bstep (se 1 (by rfl) ⟨586079, by rfl⟩ : syracuseStep 781439 = 1172159) B1172159
theorem B1174841 : Blo 519798 1174841 := bstep (se 2 (by rfl) ⟨440565, by rfl⟩ : syracuseStep 1174841 = 881131) B881131
theorem B781775 : Blo 519798 781775 := bstep (se 1 (by rfl) ⟨586331, by rfl⟩ : syracuseStep 781775 = 1172663) B1172663
theorem B1175849 : Blo 519798 1175849 := bstep (se 2 (by rfl) ⟨440943, by rfl⟩ : syracuseStep 1175849 = 881887) B881887
theorem B1176155 : Blo 519798 1176155 := bstep (se 1 (by rfl) ⟨882116, by rfl⟩ : syracuseStep 1176155 = 1764233) B1764233
theorem B1831567 : Blo 519798 1831567 := bstep (se 1 (by rfl) ⟨1373675, by rfl⟩ : syracuseStep 1831567 = 2747351) B2747351
theorem B586399 : Blo 519798 586399 := bstep (se 1 (by rfl) ⟨439799, by rfl⟩ : syracuseStep 586399 = 879599) B879599
theorem B1667827 : Blo 519798 1667827 := bstep (se 1 (by rfl) ⟨1250870, by rfl⟩ : syracuseStep 1667827 = 2501741) B2501741
theorem B521327 : Blo 519798 521327 := bstep (se 1 (by rfl) ⟨390995, by rfl⟩ : syracuseStep 521327 = 781991) B781991
theorem B1176713 : Blo 519798 1176713 := bstep (se 2 (by rfl) ⟨441267, by rfl⟩ : syracuseStep 1176713 = 882535) B882535
theorem B521439 : Blo 519798 521439 := bstep (se 1 (by rfl) ⟨391079, by rfl⟩ : syracuseStep 521439 = 782159) B782159
theorem B586975 : Blo 519798 586975 := bstep (se 1 (by rfl) ⟨440231, by rfl⟩ : syracuseStep 586975 = 880463) B880463
theorem B6026575 : Blo 519798 6026575 := bstep (se 1 (by rfl) ⟨4519931, by rfl⟩ : syracuseStep 6026575 = 9039863) B9039863
theorem B882623 : Blo 519798 882623 := bstep (se 1 (by rfl) ⟨661967, by rfl⟩ : syracuseStep 882623 = 1323935) B1323935
theorem B522367 : Blo 519798 522367 := bstep (se 1 (by rfl) ⟨391775, by rfl⟩ : syracuseStep 522367 = 783551) B783551
theorem B784667 : Blo 519798 784667 := bstep (se 1 (by rfl) ⟨588500, by rfl⟩ : syracuseStep 784667 = 1177001) B1177001
theorem B1767743 : Blo 519798 1767743 := bstep (se 1 (by rfl) ⟨1325807, by rfl⟩ : syracuseStep 1767743 = 2651615) B2651615
theorem B2980745 : Blo 519798 2980745 := bstep (se 2 (by rfl) ⟨1117779, by rfl⟩ : syracuseStep 2980745 = 2235559) B2235559
theorem B523423 : Blo 519798 523423 := bstep (se 1 (by rfl) ⟨392567, by rfl⟩ : syracuseStep 523423 = 785135) B785135
theorem B588991 : Blo 519798 588991 := bstep (se 1 (by rfl) ⟨441743, by rfl⟩ : syracuseStep 588991 = 883487) B883487
theorem B4455809 : Blo 519798 4455809 := bstep (se 2 (by rfl) ⟨1670928, by rfl⟩ : syracuseStep 4455809 = 3341857) B3341857
theorem B1900385 : Blo 519798 1900385 := bstep (se 2 (by rfl) ⟨712644, by rfl⟩ : syracuseStep 1900385 = 1425289) B1425289
theorem B3178703 : Blo 519798 3178703 := bstep (se 1 (by rfl) ⟨2384027, by rfl⟩ : syracuseStep 3178703 = 4768055) B4768055
theorem B235602229 : Blo 519798 235602229 := bstep (se 5 (by rfl) ⟨11043854, by rfl⟩ : syracuseStep 235602229 = 22087709) B22087709
theorem B87033851 : Blo 519798 87033851 := bstep (se 1 (by rfl) ⟨65275388, by rfl⟩ : syracuseStep 87033851 = 130550777) B130550777
theorem B33721595 : Blo 519798 33721595 := bstep (se 1 (by rfl) ⟨25291196, by rfl⟩ : syracuseStep 33721595 = 50582393) B50582393
theorem B660251 : Blo 519798 660251 := bstep (se 1 (by rfl) ⟨495188, by rfl⟩ : syracuseStep 660251 = 990377) B990377
theorem B628607 : Blo 519798 628607 := bstep (se 1 (by rfl) ⟨471455, by rfl⟩ : syracuseStep 628607 = 942911) B942911
theorem B1317343 : Blo 519798 1317343 := bstep (se 1 (by rfl) ⟨988007, by rfl⟩ : syracuseStep 1317343 = 1976015) B1976015
theorem B2825057 : Blo 519798 2825057 := bstep (se 2 (by rfl) ⟨1059396, by rfl⟩ : syracuseStep 2825057 = 2118793) B2118793
theorem B990119 : Blo 519798 990119 := bstep (se 1 (by rfl) ⟨742589, by rfl⟩ : syracuseStep 990119 = 1485179) B1485179
theorem B8035433 : Blo 519798 8035433 := bstep (se 2 (by rfl) ⟨3013287, by rfl⟩ : syracuseStep 8035433 = 6026575) B6026575
theorem B7216553 : Blo 519798 7216553 := bstep (se 2 (by rfl) ⟨2706207, by rfl⟩ : syracuseStep 7216553 = 5412415) B5412415
theorem B1318427 : Blo 519798 1318427 := bstep (se 1 (by rfl) ⟨988820, by rfl⟩ : syracuseStep 1318427 = 1977641) B1977641
theorem B1974527 : Blo 519798 1974527 := bstep (se 1 (by rfl) ⟨1480895, by rfl⟩ : syracuseStep 1974527 = 2961791) B2961791
theorem B3974021 : Blo 519798 3974021 := bstep (se 4 (by rfl) ⟨372564, by rfl⟩ : syracuseStep 3974021 = 745129) B745129
theorem B1583329 : Blo 519798 1583329 := bstep (se 2 (by rfl) ⟨593748, by rfl⟩ : syracuseStep 1583329 = 1187497) B1187497
theorem B12069947 : Blo 519798 12069947 := bstep (se 1 (by rfl) ⟨9052460, by rfl⟩ : syracuseStep 12069947 = 18104921) B18104921
theorem B33828515 : Blo 519798 33828515 := bstep (se 1 (by rfl) ⟨25371386, by rfl⟩ : syracuseStep 33828515 = 50742773) B50742773
theorem B667675 : Blo 519798 667675 := bstep (se 1 (by rfl) ⟨500756, by rfl⟩ : syracuseStep 667675 = 1001513) B1001513
theorem B1979113 : Blo 519798 1979113 := bstep (se 2 (by rfl) ⟨742167, by rfl⟩ : syracuseStep 1979113 = 1484335) B1484335
theorem B4240343 : Blo 519798 4240343 := bstep (se 1 (by rfl) ⟨3180257, by rfl⟩ : syracuseStep 4240343 = 6360515) B6360515
theorem B3947777 : Blo 519798 3947777 := bstep (se 2 (by rfl) ⟨1480416, by rfl⟩ : syracuseStep 3947777 = 2960833) B2960833
theorem B2442089 : Blo 519798 2442089 := bstep (se 2 (by rfl) ⟨915783, by rfl⟩ : syracuseStep 2442089 = 1831567) B1831567
theorem B164874649 : Blo 519798 164874649 := bstep (se 2 (by rfl) ⟨61827993, by rfl⟩ : syracuseStep 164874649 = 123655987) B123655987
theorem B2673263 : Blo 519798 2673263 := bstep (se 1 (by rfl) ⟨2004947, by rfl⟩ : syracuseStep 2673263 = 4009895) B4009895
theorem B1756511 : Blo 519798 1756511 := bstep (se 1 (by rfl) ⟨1317383, by rfl⟩ : syracuseStep 1756511 = 2634767) B2634767
theorem B2642057 : Blo 519798 2642057 := bstep (se 2 (by rfl) ⟨990771, by rfl⟩ : syracuseStep 2642057 = 1981543) B1981543
theorem B11293121 : Blo 519798 11293121 := bstep (se 2 (by rfl) ⟨4234920, by rfl⟩ : syracuseStep 11293121 = 8469841) B8469841
theorem B1692143 : Blo 519798 1692143 := bstep (se 1 (by rfl) ⟨1269107, by rfl⟩ : syracuseStep 1692143 = 2538215) B2538215
theorem B1987163 : Blo 519798 1987163 := bstep (se 1 (by rfl) ⟨1490372, by rfl⟩ : syracuseStep 1987163 = 2980745) B2980745
theorem B2970539 : Blo 519798 2970539 := bstep (se 1 (by rfl) ⟨2227904, by rfl⟩ : syracuseStep 2970539 = 4455809) B4455809
theorem B4445351 : Blo 519798 4445351 := bstep (se 1 (by rfl) ⟨3334013, by rfl⟩ : syracuseStep 4445351 = 6668027) B6668027
theorem B1266923 : Blo 519798 1266923 := bstep (se 1 (by rfl) ⟨950192, by rfl⟩ : syracuseStep 1266923 = 1900385) B1900385
theorem B2513273 : Blo 519798 2513273 := bstep (se 2 (by rfl) ⟨942477, by rfl⟩ : syracuseStep 2513273 = 1884955) B1884955
theorem B1171547 : Blo 519798 1171547 := bstep (se 1 (by rfl) ⟨878660, by rfl⟩ : syracuseStep 1171547 = 1757321) B1757321
theorem B3006571 : Blo 519798 3006571 := bstep (se 1 (by rfl) ⟨2254928, by rfl⟩ : syracuseStep 3006571 = 4509857) B4509857
theorem B4023809 : Blo 519798 4023809 := bstep (se 2 (by rfl) ⟨1508928, by rfl⟩ : syracuseStep 4023809 = 3017857) B3017857
theorem B779903 : Blo 519798 779903 := bstep (se 1 (by rfl) ⟨584927, by rfl⟩ : syracuseStep 779903 = 1169855) B1169855
theorem B779951 : Blo 519798 779951 := bstep (se 1 (by rfl) ⟨584963, by rfl⟩ : syracuseStep 779951 = 1169927) B1169927
theorem B43378415 : Blo 519798 43378415 := bstep (se 1 (by rfl) ⟨32533811, by rfl⟩ : syracuseStep 43378415 = 65067623) B65067623
theorem B880031 : Blo 519798 880031 := bstep (se 1 (by rfl) ⟨660023, by rfl⟩ : syracuseStep 880031 = 1320047) B1320047
theorem B781865 : Blo 519798 781865 := bstep (se 2 (by rfl) ⟨293199, by rfl⟩ : syracuseStep 781865 = 586399) B586399
theorem B5074553 : Blo 519798 5074553 := bstep (se 2 (by rfl) ⟨1902957, by rfl⟩ : syracuseStep 5074553 = 3805915) B3805915
theorem B2223769 : Blo 519798 2223769 := bstep (se 2 (by rfl) ⟨833913, by rfl⟩ : syracuseStep 2223769 = 1667827) B1667827
theorem B782063 : Blo 519798 782063 := bstep (se 1 (by rfl) ⟨586547, by rfl⟩ : syracuseStep 782063 = 1173095) B1173095
theorem B1175399 : Blo 519798 1175399 := bstep (se 1 (by rfl) ⟨881549, by rfl⟩ : syracuseStep 1175399 = 1763099) B1763099
theorem B782633 : Blo 519798 782633 := bstep (se 2 (by rfl) ⟨293487, by rfl⟩ : syracuseStep 782633 = 586975) B586975
theorem B520703 : Blo 519798 520703 := bstep (se 1 (by rfl) ⟨390527, by rfl⟩ : syracuseStep 520703 = 781055) B781055
theorem B5960303 : Blo 519798 5960303 := bstep (se 1 (by rfl) ⟨4470227, by rfl⟩ : syracuseStep 5960303 = 8940455) B8940455
theorem B520959 : Blo 519798 520959 := bstep (se 1 (by rfl) ⟨390719, by rfl⟩ : syracuseStep 520959 = 781439) B781439
theorem B783227 : Blo 519798 783227 := bstep (se 1 (by rfl) ⟨587420, by rfl⟩ : syracuseStep 783227 = 1174841) B1174841
theorem B521183 : Blo 519798 521183 := bstep (se 1 (by rfl) ⟨390887, by rfl⟩ : syracuseStep 521183 = 781775) B781775
theorem B783899 : Blo 519798 783899 := bstep (se 1 (by rfl) ⟨587924, by rfl⟩ : syracuseStep 783899 = 1175849) B1175849
theorem B1767041 : Blo 519798 1767041 := bstep (se 2 (by rfl) ⟨662640, by rfl⟩ : syracuseStep 1767041 = 1325281) B1325281
theorem B784103 : Blo 519798 784103 := bstep (se 1 (by rfl) ⟨588077, by rfl⟩ : syracuseStep 784103 = 1176155) B1176155
theorem B19036127 : Blo 519798 19036127 := bstep (se 1 (by rfl) ⟨14277095, by rfl⟩ : syracuseStep 19036127 = 28554191) B28554191
theorem B784475 : Blo 519798 784475 := bstep (se 1 (by rfl) ⟨588356, by rfl⟩ : syracuseStep 784475 = 1176713) B1176713
theorem B588415 : Blo 519798 588415 := bstep (se 1 (by rfl) ⟨441311, by rfl⟩ : syracuseStep 588415 = 882623) B882623
theorem B523111 : Blo 519798 523111 := bstep (se 1 (by rfl) ⟨392333, by rfl⟩ : syracuseStep 523111 = 784667) B784667
theorem B1178495 : Blo 519798 1178495 := bstep (se 1 (by rfl) ⟨883871, by rfl⟩ : syracuseStep 1178495 = 1767743) B1767743
theorem B785321 : Blo 519798 785321 := bstep (se 2 (by rfl) ⟨294495, by rfl⟩ : syracuseStep 785321 = 588991) B588991
theorem B7503839 : Blo 519798 7503839 := bstep (se 1 (by rfl) ⟨5627879, by rfl⟩ : syracuseStep 7503839 = 11255759) B11255759
theorem B30114989 : Blo 519798 30114989 := bstep (se 3 (by rfl) ⟨5646560, by rfl⟩ : syracuseStep 30114989 = 11293121) B11293121
theorem B22481063 : Blo 519798 22481063 := bstep (se 1 (by rfl) ⟨16860797, by rfl⟩ : syracuseStep 22481063 = 33721595) B33721595
theorem B3378461 : Blo 519798 3378461 := bstep (se 3 (by rfl) ⟨633461, by rfl⟩ : syracuseStep 3378461 = 1266923) B1266923
theorem B660079 : Blo 519798 660079 := bstep (se 1 (by rfl) ⟨495059, by rfl⟩ : syracuseStep 660079 = 990119) B990119
theorem B1676285 : Blo 519798 1676285 := bstep (se 3 (by rfl) ⟨314303, by rfl⟩ : syracuseStep 1676285 = 628607) B628607
theorem B890233 : Blo 519798 890233 := bstep (se 2 (by rfl) ⟨333837, by rfl⟩ : syracuseStep 890233 = 667675) B667675
theorem B1316351 : Blo 519798 1316351 := bstep (se 1 (by rfl) ⟨987263, by rfl⟩ : syracuseStep 1316351 = 1974527) B1974527
theorem B3383035 : Blo 519798 3383035 := bstep (se 1 (by rfl) ⟨2537276, by rfl⟩ : syracuseStep 3383035 = 5074553) B5074553
theorem B22552343 : Blo 519798 22552343 := bstep (se 1 (by rfl) ⟨16914257, by rfl⟩ : syracuseStep 22552343 = 33828515) B33828515
theorem B3973535 : Blo 519798 3973535 := bstep (se 1 (by rfl) ⟨2980151, by rfl⟩ : syracuseStep 3973535 = 5960303) B5960303
theorem B2826895 : Blo 519798 2826895 := bstep (se 1 (by rfl) ⟨2120171, by rfl⟩ : syracuseStep 2826895 = 4240343) B4240343
theorem B12690751 : Blo 519798 12690751 := bstep (se 1 (by rfl) ⟨9518063, by rfl⟩ : syracuseStep 12690751 = 19036127) B19036127
theorem B2631851 : Blo 519798 2631851 := bstep (se 1 (by rfl) ⟨1973888, by rfl⟩ : syracuseStep 2631851 = 3947777) B3947777
theorem B4008761 : Blo 519798 4008761 := bstep (se 2 (by rfl) ⟨1503285, by rfl⟩ : syracuseStep 4008761 = 3006571) B3006571
theorem B1782175 : Blo 519798 1782175 := bstep (se 1 (by rfl) ⟨1336631, by rfl⟩ : syracuseStep 1782175 = 2673263) B2673263
theorem B2111105 : Blo 519798 2111105 := bstep (se 2 (by rfl) ⟨791664, by rfl⟩ : syracuseStep 2111105 = 1583329) B1583329
theorem B1128095 : Blo 519798 1128095 := bstep (se 1 (by rfl) ⟨846071, by rfl⟩ : syracuseStep 1128095 = 1692143) B1692143
theorem B1324775 : Blo 519798 1324775 := bstep (se 1 (by rfl) ⟨993581, by rfl⟩ : syracuseStep 1324775 = 1987163) B1987163
theorem B1980359 : Blo 519798 1980359 := bstep (se 1 (by rfl) ⟨1485269, by rfl⟩ : syracuseStep 1980359 = 2970539) B2970539
theorem B2963567 : Blo 519798 2963567 := bstep (se 1 (by rfl) ⟨2222675, by rfl⟩ : syracuseStep 2963567 = 4445351) B4445351
theorem B5356955 : Blo 519798 5356955 := bstep (se 1 (by rfl) ⟨4017716, by rfl⟩ : syracuseStep 5356955 = 8035433) B8035433
theorem B2965025 : Blo 519798 2965025 := bstep (se 2 (by rfl) ⟨1111884, by rfl⟩ : syracuseStep 2965025 = 2223769) B2223769
theorem B2638817 : Blo 519798 2638817 := bstep (se 2 (by rfl) ⟨989556, by rfl⟩ : syracuseStep 2638817 = 1979113) B1979113
theorem B6702061 : Blo 519798 6702061 := bstep (se 3 (by rfl) ⟨1256636, by rfl⟩ : syracuseStep 6702061 = 2513273) B2513273
theorem B28918943 : Blo 519798 28918943 := bstep (se 1 (by rfl) ⟨21689207, by rfl⟩ : syracuseStep 28918943 = 43378415) B43378415
theorem B8046631 : Blo 519798 8046631 := bstep (se 1 (by rfl) ⟨6034973, by rfl⟩ : syracuseStep 8046631 = 12069947) B12069947
theorem B1756457 : Blo 519798 1756457 := bstep (se 2 (by rfl) ⟨658671, by rfl⟩ : syracuseStep 1756457 = 1317343) B1317343
theorem B5002559 : Blo 519798 5002559 := bstep (se 1 (by rfl) ⟨3751919, by rfl⟩ : syracuseStep 5002559 = 7503839) B7503839
theorem B2119135 : Blo 519798 2119135 := bstep (se 1 (by rfl) ⟨1589351, by rfl⟩ : syracuseStep 2119135 = 3178703) B3178703
theorem B314136305 : Blo 519798 314136305 := bstep (se 2 (by rfl) ⟨117801114, by rfl⟩ : syracuseStep 314136305 = 235602229) B235602229
theorem B1628059 : Blo 519798 1628059 := bstep (se 1 (by rfl) ⟨1221044, by rfl⟩ : syracuseStep 1628059 = 2442089) B2442089
theorem B58022567 : Blo 519798 58022567 := bstep (se 1 (by rfl) ⟨43516925, by rfl⟩ : syracuseStep 58022567 = 87033851) B87033851
theorem B1760669 : Blo 519798 1760669 := bstep (se 3 (by rfl) ⟨330125, by rfl⟩ : syracuseStep 1760669 = 660251) B660251
theorem B1171007 : Blo 519798 1171007 := bstep (se 1 (by rfl) ⟨878255, by rfl⟩ : syracuseStep 1171007 = 1756511) B1756511
theorem B1761371 : Blo 519798 1761371 := bstep (se 1 (by rfl) ⟨1321028, by rfl⟩ : syracuseStep 1761371 = 2642057) B2642057
theorem B219832865 : Blo 519798 219832865 := bstep (se 2 (by rfl) ⟨82437324, by rfl⟩ : syracuseStep 219832865 = 164874649) B164874649
theorem B4811035 : Blo 519798 4811035 := bstep (se 1 (by rfl) ⟨3608276, by rfl⟩ : syracuseStep 4811035 = 7216553) B7216553
theorem B878951 : Blo 519798 878951 := bstep (se 1 (by rfl) ⟨659213, by rfl⟩ : syracuseStep 878951 = 1318427) B1318427
theorem B781031 : Blo 519798 781031 := bstep (se 1 (by rfl) ⟨585773, by rfl⟩ : syracuseStep 781031 = 1171547) B1171547
theorem B2649347 : Blo 519798 2649347 := bstep (se 1 (by rfl) ⟨1987010, by rfl⟩ : syracuseStep 2649347 = 3974021) B3974021
theorem B2682539 : Blo 519798 2682539 := bstep (se 1 (by rfl) ⟨2011904, by rfl⟩ : syracuseStep 2682539 = 4023809) B4023809
theorem B519935 : Blo 519798 519935 := bstep (se 1 (by rfl) ⟨389951, by rfl⟩ : syracuseStep 519935 = 779903) B779903
theorem B519967 : Blo 519798 519967 := bstep (se 1 (by rfl) ⟨389975, by rfl⟩ : syracuseStep 519967 = 779951) B779951
theorem B7533485 : Blo 519798 7533485 := bstep (se 3 (by rfl) ⟨1412528, by rfl⟩ : syracuseStep 7533485 = 2825057) B2825057
theorem B586687 : Blo 519798 586687 := bstep (se 1 (by rfl) ⟨440015, by rfl⟩ : syracuseStep 586687 = 880031) B880031
theorem B521243 : Blo 519798 521243 := bstep (se 1 (by rfl) ⟨390932, by rfl⟩ : syracuseStep 521243 = 781865) B781865
theorem B521375 : Blo 519798 521375 := bstep (se 1 (by rfl) ⟨391031, by rfl⟩ : syracuseStep 521375 = 782063) B782063
theorem B783599 : Blo 519798 783599 := bstep (se 1 (by rfl) ⟨587699, by rfl⟩ : syracuseStep 783599 = 1175399) B1175399
theorem B521755 : Blo 519798 521755 := bstep (se 1 (by rfl) ⟨391316, by rfl⟩ : syracuseStep 521755 = 782633) B782633
theorem B522151 : Blo 519798 522151 := bstep (se 1 (by rfl) ⟨391613, by rfl⟩ : syracuseStep 522151 = 783227) B783227
theorem B784553 : Blo 519798 784553 := bstep (se 2 (by rfl) ⟨294207, by rfl⟩ : syracuseStep 784553 = 588415) B588415
theorem B522599 : Blo 519798 522599 := bstep (se 1 (by rfl) ⟨391949, by rfl⟩ : syracuseStep 522599 = 783899) B783899
theorem B1178027 : Blo 519798 1178027 := bstep (se 1 (by rfl) ⟨883520, by rfl⟩ : syracuseStep 1178027 = 1767041) B1767041
theorem B522735 : Blo 519798 522735 := bstep (se 1 (by rfl) ⟨392051, by rfl⟩ : syracuseStep 522735 = 784103) B784103
theorem B522983 : Blo 519798 522983 := bstep (se 1 (by rfl) ⟨392237, by rfl⟩ : syracuseStep 522983 = 784475) B784475
theorem B785663 : Blo 519798 785663 := bstep (se 1 (by rfl) ⟨589247, by rfl⟩ : syracuseStep 785663 = 1178495) B1178495
theorem B523547 : Blo 519798 523547 := bstep (se 1 (by rfl) ⟨392660, by rfl⟩ : syracuseStep 523547 = 785321) B785321
theorem B3769193 : Blo 519798 3769193 := bstep (se 2 (by rfl) ⟨1413447, by rfl⟩ : syracuseStep 3769193 = 2826895) B2826895
theorem B1117523 : Blo 519798 1117523 := bstep (se 1 (by rfl) ⟨838142, by rfl⟩ : syracuseStep 1117523 = 1676285) B1676285
theorem B209424203 : Blo 519798 209424203 := bstep (se 1 (by rfl) ⟨157068152, by rfl⟩ : syracuseStep 209424203 = 314136305) B314136305
theorem B2825513 : Blo 519798 2825513 := bstep (se 2 (by rfl) ⟨1059567, by rfl⟩ : syracuseStep 2825513 = 2119135) B2119135
theorem B2170745 : Blo 519798 2170745 := bstep (se 2 (by rfl) ⟨814029, by rfl⟩ : syracuseStep 2170745 = 1628059) B1628059
theorem B5022323 : Blo 519798 5022323 := bstep (se 1 (by rfl) ⟨3766742, by rfl⟩ : syracuseStep 5022323 = 7533485) B7533485
theorem B1320239 : Blo 519798 1320239 := bstep (se 1 (by rfl) ⟨990179, by rfl⟩ : syracuseStep 1320239 = 1980359) B1980359
theorem B1975711 : Blo 519798 1975711 := bstep (se 1 (by rfl) ⟨1481783, by rfl⟩ : syracuseStep 1975711 = 2963567) B2963567
theorem B1976683 : Blo 519798 1976683 := bstep (se 1 (by rfl) ⟨1482512, by rfl⟩ : syracuseStep 1976683 = 2965025) B2965025
theorem B19279295 : Blo 519798 19279295 := bstep (se 1 (by rfl) ⟨14459471, by rfl⟩ : syracuseStep 19279295 = 28918943) B28918943
theorem B14987375 : Blo 519798 14987375 := bstep (se 1 (by rfl) ⟨11240531, by rfl⟩ : syracuseStep 14987375 = 22481063) B22481063
theorem B16921001 : Blo 519798 16921001 := bstep (se 2 (by rfl) ⟨6345375, by rfl⟩ : syracuseStep 16921001 = 12690751) B12690751
theorem B38681711 : Blo 519798 38681711 := bstep (se 1 (by rfl) ⟨29011283, by rfl⟩ : syracuseStep 38681711 = 58022567) B58022567
theorem B146555243 : Blo 519798 146555243 := bstep (se 1 (by rfl) ⟨109916432, by rfl⟩ : syracuseStep 146555243 = 219832865) B219832865
theorem B2376233 : Blo 519798 2376233 := bstep (se 2 (by rfl) ⟨891087, by rfl⟩ : syracuseStep 2376233 = 1782175) B1782175
theorem B1754567 : Blo 519798 1754567 := bstep (se 1 (by rfl) ⟨1315925, by rfl⟩ : syracuseStep 1754567 = 2631851) B2631851
theorem B2672507 : Blo 519798 2672507 := bstep (se 1 (by rfl) ⟨2004380, by rfl⟩ : syracuseStep 2672507 = 4008761) B4008761
theorem B1788359 : Blo 519798 1788359 := bstep (se 1 (by rfl) ⟨1341269, by rfl⟩ : syracuseStep 1788359 = 2682539) B2682539
theorem B18042853 : Blo 519798 18042853 := bstep (se 4 (by rfl) ⟨1691517, by rfl⟩ : syracuseStep 18042853 = 3383035) B3383035
theorem B42915365 : Blo 519798 42915365 := bstep (se 4 (by rfl) ⟨4023315, by rfl⟩ : syracuseStep 42915365 = 8046631) B8046631
theorem B1759211 : Blo 519798 1759211 := bstep (se 1 (by rfl) ⟨1319408, by rfl⟩ : syracuseStep 1759211 = 2638817) B2638817
theorem B20076659 : Blo 519798 20076659 := bstep (se 1 (by rfl) ⟨15057494, by rfl⟩ : syracuseStep 20076659 = 30114989) B30114989
theorem B8936081 : Blo 519798 8936081 := bstep (se 2 (by rfl) ⟨3351030, by rfl⟩ : syracuseStep 8936081 = 6702061) B6702061
theorem B1170971 : Blo 519798 1170971 := bstep (se 1 (by rfl) ⟨878228, by rfl⟩ : syracuseStep 1170971 = 1756457) B1756457
theorem B36036917 : Blo 519798 36036917 := bstep (se 5 (by rfl) ⟨1689230, by rfl⟩ : syracuseStep 36036917 = 3378461) B3378461
theorem B6414713 : Blo 519798 6414713 := bstep (se 2 (by rfl) ⟨2405517, by rfl⟩ : syracuseStep 6414713 = 4811035) B4811035
theorem B3335039 : Blo 519798 3335039 := bstep (se 1 (by rfl) ⟨2501279, by rfl⟩ : syracuseStep 3335039 = 5002559) B5002559
theorem B877567 : Blo 519798 877567 := bstep (se 1 (by rfl) ⟨658175, by rfl⟩ : syracuseStep 877567 = 1316351) B1316351
theorem B1173779 : Blo 519798 1173779 := bstep (se 1 (by rfl) ⟨880334, by rfl⟩ : syracuseStep 1173779 = 1760669) B1760669
theorem B780671 : Blo 519798 780671 := bstep (se 1 (by rfl) ⟨585503, by rfl⟩ : syracuseStep 780671 = 1171007) B1171007
theorem B15034895 : Blo 519798 15034895 := bstep (se 1 (by rfl) ⟨11276171, by rfl⟩ : syracuseStep 15034895 = 22552343) B22552343
theorem B1174247 : Blo 519798 1174247 := bstep (se 1 (by rfl) ⟨880685, by rfl⟩ : syracuseStep 1174247 = 1761371) B1761371
theorem B2649023 : Blo 519798 2649023 := bstep (se 1 (by rfl) ⟨1986767, by rfl⟩ : syracuseStep 2649023 = 3973535) B3973535
theorem B880105 : Blo 519798 880105 := bstep (se 2 (by rfl) ⟨330039, by rfl⟩ : syracuseStep 880105 = 660079) B660079
theorem B782249 : Blo 519798 782249 := bstep (se 2 (by rfl) ⟨293343, by rfl⟩ : syracuseStep 782249 = 586687) B586687
theorem B585967 : Blo 519798 585967 := bstep (se 1 (by rfl) ⟨439475, by rfl⟩ : syracuseStep 585967 = 878951) B878951
theorem B520687 : Blo 519798 520687 := bstep (se 1 (by rfl) ⟨390515, by rfl⟩ : syracuseStep 520687 = 781031) B781031
theorem B4747909 : Blo 519798 4747909 := bstep (se 4 (by rfl) ⟨445116, by rfl⟩ : syracuseStep 4747909 = 890233) B890233
theorem B1766231 : Blo 519798 1766231 := bstep (se 1 (by rfl) ⟨1324673, by rfl⟩ : syracuseStep 1766231 = 2649347) B2649347
theorem B522399 : Blo 519798 522399 := bstep (se 1 (by rfl) ⟨391799, by rfl⟩ : syracuseStep 522399 = 783599) B783599
theorem B1407403 : Blo 519798 1407403 := bstep (se 1 (by rfl) ⟨1055552, by rfl⟩ : syracuseStep 1407403 = 2111105) B2111105
theorem B752063 : Blo 519798 752063 := bstep (se 1 (by rfl) ⟨564047, by rfl⟩ : syracuseStep 752063 = 1128095) B1128095
theorem B883183 : Blo 519798 883183 := bstep (se 1 (by rfl) ⟨662387, by rfl⟩ : syracuseStep 883183 = 1324775) B1324775
theorem B523035 : Blo 519798 523035 := bstep (se 1 (by rfl) ⟨392276, by rfl⟩ : syracuseStep 523035 = 784553) B784553
theorem B785351 : Blo 519798 785351 := bstep (se 1 (by rfl) ⟨589013, by rfl⟩ : syracuseStep 785351 = 1178027) B1178027
theorem B523775 : Blo 519798 523775 := bstep (se 1 (by rfl) ⟨392831, by rfl⟩ : syracuseStep 523775 = 785663) B785663
theorem B3571303 : Blo 519798 3571303 := bstep (se 1 (by rfl) ⟨2678477, by rfl⟩ : syracuseStep 3571303 = 5356955) B5356955
theorem B28610243 : Blo 519798 28610243 := bstep (se 1 (by rfl) ⟨21457682, by rfl⟩ : syracuseStep 28610243 = 42915365) B42915365
theorem B1447163 : Blo 519798 1447163 := bstep (se 1 (by rfl) ⟨1085372, by rfl⟩ : syracuseStep 1447163 = 2170745) B2170745
theorem B24057137 : Blo 519798 24057137 := bstep (se 2 (by rfl) ⟨9021426, by rfl⟩ : syracuseStep 24057137 = 18042853) B18042853
theorem B24024611 : Blo 519798 24024611 := bstep (se 1 (by rfl) ⟨18018458, by rfl⟩ : syracuseStep 24024611 = 36036917) B36036917
theorem B3348215 : Blo 519798 3348215 := bstep (se 1 (by rfl) ⟨2511161, by rfl⟩ : syracuseStep 3348215 = 5022323) B5022323
theorem B6330545 : Blo 519798 6330545 := bstep (se 2 (by rfl) ⟨2373954, by rfl⟩ : syracuseStep 6330545 = 4747909) B4747909
theorem B2005501 : Blo 519798 2005501 := bstep (se 3 (by rfl) ⟨376031, by rfl⟩ : syracuseStep 2005501 = 752063) B752063
theorem B12852863 : Blo 519798 12852863 := bstep (se 1 (by rfl) ⟨9639647, by rfl⟩ : syracuseStep 12852863 = 19279295) B19279295
theorem B11280667 : Blo 519798 11280667 := bstep (se 1 (by rfl) ⟨8460500, by rfl⟩ : syracuseStep 11280667 = 16921001) B16921001
theorem B1876537 : Blo 519798 1876537 := bstep (se 2 (by rfl) ⟨703701, by rfl⟩ : syracuseStep 1876537 = 1407403) B1407403
theorem B4761737 : Blo 519798 4761737 := bstep (se 2 (by rfl) ⟨1785651, by rfl⟩ : syracuseStep 4761737 = 3571303) B3571303
theorem B1584155 : Blo 519798 1584155 := bstep (se 1 (by rfl) ⟨1188116, by rfl⟩ : syracuseStep 1584155 = 2376233) B2376233
theorem B1781671 : Blo 519798 1781671 := bstep (se 1 (by rfl) ⟨1336253, by rfl⟩ : syracuseStep 1781671 = 2672507) B2672507
theorem B2634281 : Blo 519798 2634281 := bstep (se 2 (by rfl) ⟨987855, by rfl⟩ : syracuseStep 2634281 = 1975711) B1975711
theorem B2635577 : Blo 519798 2635577 := bstep (se 2 (by rfl) ⟨988341, by rfl⟩ : syracuseStep 2635577 = 1976683) B1976683
theorem B13384439 : Blo 519798 13384439 := bstep (se 1 (by rfl) ⟨10038329, by rfl⟩ : syracuseStep 13384439 = 20076659) B20076659
theorem B1883675 : Blo 519798 1883675 := bstep (se 1 (by rfl) ⟨1412756, by rfl⟩ : syracuseStep 1883675 = 2825513) B2825513
theorem B4276475 : Blo 519798 4276475 := bstep (se 1 (by rfl) ⟨3207356, by rfl⟩ : syracuseStep 4276475 = 6414713) B6414713
theorem B4768957 : Blo 519798 4768957 := bstep (se 3 (by rfl) ⟨894179, by rfl⟩ : syracuseStep 4768957 = 1788359) B1788359
theorem B97703495 : Blo 519798 97703495 := bstep (se 1 (by rfl) ⟨73277621, by rfl⟩ : syracuseStep 97703495 = 146555243) B146555243
theorem B2512795 : Blo 519798 2512795 := bstep (se 1 (by rfl) ⟨1884596, by rfl⟩ : syracuseStep 2512795 = 3769193) B3769193
theorem B1169711 : Blo 519798 1169711 := bstep (se 1 (by rfl) ⟨877283, by rfl⟩ : syracuseStep 1169711 = 1754567) B1754567
theorem B1170089 : Blo 519798 1170089 := bstep (se 2 (by rfl) ⟨438783, by rfl⟩ : syracuseStep 1170089 = 877567) B877567
theorem B139616135 : Blo 519798 139616135 := bstep (se 1 (by rfl) ⟨104712101, by rfl⟩ : syracuseStep 139616135 = 209424203) B209424203
theorem B1172807 : Blo 519798 1172807 := bstep (se 1 (by rfl) ⟨879605, by rfl⟩ : syracuseStep 1172807 = 1759211) B1759211
theorem B5957387 : Blo 519798 5957387 := bstep (se 1 (by rfl) ⟨4468040, by rfl⟩ : syracuseStep 5957387 = 8936081) B8936081
theorem B1173473 : Blo 519798 1173473 := bstep (se 2 (by rfl) ⟨440052, by rfl⟩ : syracuseStep 1173473 = 880105) B880105
theorem B780647 : Blo 519798 780647 := bstep (se 1 (by rfl) ⟨585485, by rfl⟩ : syracuseStep 780647 = 1170971) B1170971
theorem B781289 : Blo 519798 781289 := bstep (se 2 (by rfl) ⟨292983, by rfl⟩ : syracuseStep 781289 = 585967) B585967
theorem B2223359 : Blo 519798 2223359 := bstep (se 1 (by rfl) ⟨1667519, by rfl⟩ : syracuseStep 2223359 = 3335039) B3335039
theorem B880159 : Blo 519798 880159 := bstep (se 1 (by rfl) ⟨660119, by rfl⟩ : syracuseStep 880159 = 1320239) B1320239
theorem B782519 : Blo 519798 782519 := bstep (se 1 (by rfl) ⟨586889, by rfl⟩ : syracuseStep 782519 = 1173779) B1173779
theorem B520447 : Blo 519798 520447 := bstep (se 1 (by rfl) ⟨390335, by rfl⟩ : syracuseStep 520447 = 780671) B780671
theorem B10023263 : Blo 519798 10023263 := bstep (se 1 (by rfl) ⟨7517447, by rfl⟩ : syracuseStep 10023263 = 15034895) B15034895
theorem B782831 : Blo 519798 782831 := bstep (se 1 (by rfl) ⟨587123, by rfl⟩ : syracuseStep 782831 = 1174247) B1174247
theorem B1766015 : Blo 519798 1766015 := bstep (se 1 (by rfl) ⟨1324511, by rfl⟩ : syracuseStep 1766015 = 2649023) B2649023
theorem B521499 : Blo 519798 521499 := bstep (se 1 (by rfl) ⟨391124, by rfl⟩ : syracuseStep 521499 = 782249) B782249
theorem B9991583 : Blo 519798 9991583 := bstep (se 1 (by rfl) ⟨7493687, by rfl⟩ : syracuseStep 9991583 = 14987375) B14987375
theorem B1177487 : Blo 519798 1177487 := bstep (se 1 (by rfl) ⟨883115, by rfl⟩ : syracuseStep 1177487 = 1766231) B1766231
theorem B1177577 : Blo 519798 1177577 := bstep (se 2 (by rfl) ⟨441591, by rfl⟩ : syracuseStep 1177577 = 883183) B883183
theorem B2980061 : Blo 519798 2980061 := bstep (se 3 (by rfl) ⟨558761, by rfl⟩ : syracuseStep 2980061 = 1117523) B1117523
theorem B523567 : Blo 519798 523567 := bstep (se 1 (by rfl) ⟨392675, by rfl⟩ : syracuseStep 523567 = 785351) B785351
theorem B25787807 : Blo 519798 25787807 := bstep (se 1 (by rfl) ⟨19340855, by rfl⟩ : syracuseStep 25787807 = 38681711) B38681711
theorem B2850983 : Blo 519798 2850983 := bstep (se 1 (by rfl) ⟨2138237, by rfl⟩ : syracuseStep 2850983 = 4276475) B4276475
theorem B15040889 : Blo 519798 15040889 := bstep (se 2 (by rfl) ⟨5640333, by rfl⟩ : syracuseStep 15040889 = 11280667) B11280667
theorem B6358609 : Blo 519798 6358609 := bstep (se 2 (by rfl) ⟨2384478, by rfl⟩ : syracuseStep 6358609 = 4768957) B4768957
theorem B19073495 : Blo 519798 19073495 := bstep (se 1 (by rfl) ⟨14305121, by rfl⟩ : syracuseStep 19073495 = 28610243) B28610243
theorem B2232143 : Blo 519798 2232143 := bstep (se 1 (by rfl) ⟨1674107, by rfl⟩ : syracuseStep 2232143 = 3348215) B3348215
theorem B64065629 : Blo 519798 64065629 := bstep (se 3 (by rfl) ⟨12012305, by rfl⟩ : syracuseStep 64065629 = 24024611) B24024611
theorem B3971591 : Blo 519798 3971591 := bstep (se 1 (by rfl) ⟨2978693, by rfl⟩ : syracuseStep 3971591 = 5957387) B5957387
theorem B1482239 : Blo 519798 1482239 := bstep (se 1 (by rfl) ⟨1111679, by rfl⟩ : syracuseStep 1482239 = 2223359) B2223359
theorem B3350393 : Blo 519798 3350393 := bstep (se 2 (by rfl) ⟨1256397, by rfl⟩ : syracuseStep 3350393 = 2512795) B2512795
theorem B6661055 : Blo 519798 6661055 := bstep (se 1 (by rfl) ⟨4995791, by rfl⟩ : syracuseStep 6661055 = 9991583) B9991583
theorem B8922959 : Blo 519798 8922959 := bstep (se 1 (by rfl) ⟨6692219, by rfl⟩ : syracuseStep 8922959 = 13384439) B13384439
theorem B1255783 : Blo 519798 1255783 := bstep (se 1 (by rfl) ⟨941837, by rfl⟩ : syracuseStep 1255783 = 1883675) B1883675
theorem B2502049 : Blo 519798 2502049 := bstep (se 2 (by rfl) ⟨938268, by rfl⟩ : syracuseStep 2502049 = 1876537) B1876537
theorem B964775 : Blo 519798 964775 := bstep (se 1 (by rfl) ⟨723581, by rfl⟩ : syracuseStep 964775 = 1447163) B1447163
theorem B16038091 : Blo 519798 16038091 := bstep (se 1 (by rfl) ⟨12028568, by rfl⟩ : syracuseStep 16038091 = 24057137) B24057137
theorem B8568575 : Blo 519798 8568575 := bstep (se 1 (by rfl) ⟨6426431, by rfl⟩ : syracuseStep 8568575 = 12852863) B12852863
theorem B2375561 : Blo 519798 2375561 := bstep (se 2 (by rfl) ⟨890835, by rfl⟩ : syracuseStep 2375561 = 1781671) B1781671
theorem B93077423 : Blo 519798 93077423 := bstep (se 1 (by rfl) ⟨69808067, by rfl⟩ : syracuseStep 93077423 = 139616135) B139616135
theorem B1756187 : Blo 519798 1756187 := bstep (se 1 (by rfl) ⟨1317140, by rfl⟩ : syracuseStep 1756187 = 2634281) B2634281
theorem B2674001 : Blo 519798 2674001 := bstep (se 2 (by rfl) ⟨1002750, by rfl⟩ : syracuseStep 2674001 = 2005501) B2005501
theorem B1757051 : Blo 519798 1757051 := bstep (se 1 (by rfl) ⟨1317788, by rfl⟩ : syracuseStep 1757051 = 2635577) B2635577
theorem B1986707 : Blo 519798 1986707 := bstep (se 1 (by rfl) ⟨1490030, by rfl⟩ : syracuseStep 1986707 = 2980061) B2980061
theorem B17191871 : Blo 519798 17191871 := bstep (se 1 (by rfl) ⟨12893903, by rfl⟩ : syracuseStep 17191871 = 25787807) B25787807
theorem B65135663 : Blo 519798 65135663 := bstep (se 1 (by rfl) ⟨48851747, by rfl⟩ : syracuseStep 65135663 = 97703495) B97703495
theorem B4220363 : Blo 519798 4220363 := bstep (se 1 (by rfl) ⟨3165272, by rfl⟩ : syracuseStep 4220363 = 6330545) B6330545
theorem B779807 : Blo 519798 779807 := bstep (se 1 (by rfl) ⟨584855, by rfl⟩ : syracuseStep 779807 = 1169711) B1169711
theorem B780059 : Blo 519798 780059 := bstep (se 1 (by rfl) ⟨585044, by rfl⟩ : syracuseStep 780059 = 1170089) B1170089
theorem B1173545 : Blo 519798 1173545 := bstep (se 2 (by rfl) ⟨440079, by rfl⟩ : syracuseStep 1173545 = 880159) B880159
theorem B781871 : Blo 519798 781871 := bstep (se 1 (by rfl) ⟨586403, by rfl⟩ : syracuseStep 781871 = 1172807) B1172807
theorem B782315 : Blo 519798 782315 := bstep (se 1 (by rfl) ⟨586736, by rfl⟩ : syracuseStep 782315 = 1173473) B1173473
theorem B3174491 : Blo 519798 3174491 := bstep (se 1 (by rfl) ⟨2380868, by rfl⟩ : syracuseStep 3174491 = 4761737) B4761737
theorem B520431 : Blo 519798 520431 := bstep (se 1 (by rfl) ⟨390323, by rfl⟩ : syracuseStep 520431 = 780647) B780647
theorem B520859 : Blo 519798 520859 := bstep (se 1 (by rfl) ⟨390644, by rfl⟩ : syracuseStep 520859 = 781289) B781289
theorem B4224413 : Blo 519798 4224413 := bstep (se 3 (by rfl) ⟨792077, by rfl⟩ : syracuseStep 4224413 = 1584155) B1584155
theorem B521679 : Blo 519798 521679 := bstep (se 1 (by rfl) ⟨391259, by rfl⟩ : syracuseStep 521679 = 782519) B782519
theorem B6682175 : Blo 519798 6682175 := bstep (se 1 (by rfl) ⟨5011631, by rfl⟩ : syracuseStep 6682175 = 10023263) B10023263
theorem B521887 : Blo 519798 521887 := bstep (se 1 (by rfl) ⟨391415, by rfl⟩ : syracuseStep 521887 = 782831) B782831
theorem B1177343 : Blo 519798 1177343 := bstep (se 1 (by rfl) ⟨883007, by rfl⟩ : syracuseStep 1177343 = 1766015) B1766015
theorem B784991 : Blo 519798 784991 := bstep (se 1 (by rfl) ⟨588743, by rfl⟩ : syracuseStep 784991 = 1177487) B1177487
theorem B785051 : Blo 519798 785051 := bstep (se 1 (by rfl) ⟨588788, by rfl⟩ : syracuseStep 785051 = 1177577) B1177577
theorem B1900655 : Blo 519798 1900655 := bstep (se 1 (by rfl) ⟨1425491, by rfl⟩ : syracuseStep 1900655 = 2850983) B2850983
theorem B10027259 : Blo 519798 10027259 := bstep (se 1 (by rfl) ⟨7520444, by rfl⟩ : syracuseStep 10027259 = 15040889) B15040889
theorem B12715663 : Blo 519798 12715663 := bstep (se 1 (by rfl) ⟨9536747, by rfl⟩ : syracuseStep 12715663 = 19073495) B19073495
theorem B1674377 : Blo 519798 1674377 := bstep (se 2 (by rfl) ⟨627891, by rfl⟩ : syracuseStep 1674377 = 1255783) B1255783
theorem B2233595 : Blo 519798 2233595 := bstep (se 1 (by rfl) ⟨1675196, by rfl⟩ : syracuseStep 2233595 = 3350393) B3350393
theorem B43423775 : Blo 519798 43423775 := bstep (se 1 (by rfl) ⟨32567831, by rfl⟩ : syracuseStep 43423775 = 65135663) B65135663
theorem B5712383 : Blo 519798 5712383 := bstep (se 1 (by rfl) ⟨4284287, by rfl⟩ : syracuseStep 5712383 = 8568575) B8568575
theorem B1583707 : Blo 519798 1583707 := bstep (se 1 (by rfl) ⟨1187780, by rfl⟩ : syracuseStep 1583707 = 2375561) B2375561
theorem B8465309 : Blo 519798 8465309 := bstep (se 3 (by rfl) ⟨1587245, by rfl⟩ : syracuseStep 8465309 = 3174491) B3174491
theorem B1782667 : Blo 519798 1782667 := bstep (se 1 (by rfl) ⟨1337000, by rfl⟩ : syracuseStep 1782667 = 2674001) B2674001
theorem B1488095 : Blo 519798 1488095 := bstep (se 1 (by rfl) ⟨1116071, by rfl⟩ : syracuseStep 1488095 = 2232143) B2232143
theorem B42710419 : Blo 519798 42710419 := bstep (se 1 (by rfl) ⟨32032814, by rfl⟩ : syracuseStep 42710419 = 64065629) B64065629
theorem B1324471 : Blo 519798 1324471 := bstep (se 1 (by rfl) ⟨993353, by rfl⟩ : syracuseStep 1324471 = 1986707) B1986707
theorem B11254301 : Blo 519798 11254301 := bstep (se 3 (by rfl) ⟨2110181, by rfl⟩ : syracuseStep 11254301 = 4220363) B4220363
theorem B4440703 : Blo 519798 4440703 := bstep (se 1 (by rfl) ⟨3330527, by rfl⟩ : syracuseStep 4440703 = 6661055) B6661055
theorem B5948639 : Blo 519798 5948639 := bstep (se 1 (by rfl) ⟨4461479, by rfl⟩ : syracuseStep 5948639 = 8922959) B8922959
theorem B21384121 : Blo 519798 21384121 := bstep (se 2 (by rfl) ⟨8019045, by rfl⟩ : syracuseStep 21384121 = 16038091) B16038091
theorem B3952637 : Blo 519798 3952637 := bstep (se 3 (by rfl) ⟨741119, by rfl⟩ : syracuseStep 3952637 = 1482239) B1482239
theorem B643183 : Blo 519798 643183 := bstep (se 1 (by rfl) ⟨482387, by rfl⟩ : syracuseStep 643183 = 964775) B964775
theorem B62051615 : Blo 519798 62051615 := bstep (se 1 (by rfl) ⟨46538711, by rfl⟩ : syracuseStep 62051615 = 93077423) B93077423
theorem B1170791 : Blo 519798 1170791 := bstep (se 1 (by rfl) ⟨878093, by rfl⟩ : syracuseStep 1170791 = 1756187) B1756187
theorem B8478145 : Blo 519798 8478145 := bstep (se 2 (by rfl) ⟨3179304, by rfl⟩ : syracuseStep 8478145 = 6358609) B6358609
theorem B1171367 : Blo 519798 1171367 := bstep (se 1 (by rfl) ⟨878525, by rfl⟩ : syracuseStep 1171367 = 1757051) B1757051
theorem B11461247 : Blo 519798 11461247 := bstep (se 1 (by rfl) ⟨8595935, by rfl⟩ : syracuseStep 11461247 = 17191871) B17191871
theorem B11265101 : Blo 519798 11265101 := bstep (se 3 (by rfl) ⟨2112206, by rfl⟩ : syracuseStep 11265101 = 4224413) B4224413
theorem B2647727 : Blo 519798 2647727 := bstep (se 1 (by rfl) ⟨1985795, by rfl⟩ : syracuseStep 2647727 = 3971591) B3971591
theorem B3336065 : Blo 519798 3336065 := bstep (se 2 (by rfl) ⟨1251024, by rfl⟩ : syracuseStep 3336065 = 2502049) B2502049
theorem B519871 : Blo 519798 519871 := bstep (se 1 (by rfl) ⟨389903, by rfl⟩ : syracuseStep 519871 = 779807) B779807
theorem B520039 : Blo 519798 520039 := bstep (se 1 (by rfl) ⟨390029, by rfl⟩ : syracuseStep 520039 = 780059) B780059
theorem B782363 : Blo 519798 782363 := bstep (se 1 (by rfl) ⟨586772, by rfl⟩ : syracuseStep 782363 = 1173545) B1173545
theorem B521247 : Blo 519798 521247 := bstep (se 1 (by rfl) ⟨390935, by rfl⟩ : syracuseStep 521247 = 781871) B781871
theorem B521543 : Blo 519798 521543 := bstep (se 1 (by rfl) ⟨391157, by rfl⟩ : syracuseStep 521543 = 782315) B782315
theorem B4454783 : Blo 519798 4454783 := bstep (se 1 (by rfl) ⟨3341087, by rfl⟩ : syracuseStep 4454783 = 6682175) B6682175
theorem B784895 : Blo 519798 784895 := bstep (se 1 (by rfl) ⟨588671, by rfl⟩ : syracuseStep 784895 = 1177343) B1177343
theorem B523327 : Blo 519798 523327 := bstep (se 1 (by rfl) ⟨392495, by rfl⟩ : syracuseStep 523327 = 784991) B784991
theorem B523367 : Blo 519798 523367 := bstep (se 1 (by rfl) ⟨392525, by rfl⟩ : syracuseStep 523367 = 785051) B785051
theorem B6684839 : Blo 519798 6684839 := bstep (se 1 (by rfl) ⟨5013629, by rfl⟩ : syracuseStep 6684839 = 10027259) B10027259
theorem B3965759 : Blo 519798 3965759 := bstep (se 1 (by rfl) ⟨2974319, by rfl⟩ : syracuseStep 3965759 = 5948639) B5948639
theorem B1116251 : Blo 519798 1116251 := bstep (se 1 (by rfl) ⟨837188, by rfl⟩ : syracuseStep 1116251 = 1674377) B1674377
theorem B28512161 : Blo 519798 28512161 := bstep (se 2 (by rfl) ⟨10692060, by rfl⟩ : syracuseStep 28512161 = 21384121) B21384121
theorem B9507557 : Blo 519798 9507557 := bstep (se 4 (by rfl) ⟨891333, by rfl⟩ : syracuseStep 9507557 = 1782667) B1782667
theorem B7640831 : Blo 519798 7640831 := bstep (se 1 (by rfl) ⟨5730623, by rfl⟩ : syracuseStep 7640831 = 11461247) B11461247
theorem B7510067 : Blo 519798 7510067 := bstep (se 1 (by rfl) ⟨5632550, by rfl⟩ : syracuseStep 7510067 = 11265101) B11265101
theorem B3808255 : Blo 519798 3808255 := bstep (se 1 (by rfl) ⟨2856191, by rfl⟩ : syracuseStep 3808255 = 5712383) B5712383
theorem B5643539 : Blo 519798 5643539 := bstep (se 1 (by rfl) ⟨4232654, by rfl⟩ : syracuseStep 5643539 = 8465309) B8465309
theorem B992063 : Blo 519798 992063 := bstep (se 1 (by rfl) ⟨744047, by rfl⟩ : syracuseStep 992063 = 1488095) B1488095
theorem B16954217 : Blo 519798 16954217 := bstep (se 2 (by rfl) ⟨6357831, by rfl⟩ : syracuseStep 16954217 = 12715663) B12715663
theorem B2635091 : Blo 519798 2635091 := bstep (se 1 (by rfl) ⟨1976318, by rfl⟩ : syracuseStep 2635091 = 3952637) B3952637
theorem B2111609 : Blo 519798 2111609 := bstep (se 2 (by rfl) ⟨791853, by rfl⟩ : syracuseStep 2111609 = 1583707) B1583707
theorem B1489063 : Blo 519798 1489063 := bstep (se 1 (by rfl) ⟨1116797, by rfl⟩ : syracuseStep 1489063 = 2233595) B2233595
theorem B41367743 : Blo 519798 41367743 := bstep (se 1 (by rfl) ⟨31025807, by rfl⟩ : syracuseStep 41367743 = 62051615) B62051615
theorem B28949183 : Blo 519798 28949183 := bstep (se 1 (by rfl) ⟨21711887, by rfl⟩ : syracuseStep 28949183 = 43423775) B43423775
theorem B2969855 : Blo 519798 2969855 := bstep (se 1 (by rfl) ⟨2227391, by rfl⟩ : syracuseStep 2969855 = 4454783) B4454783
theorem B1267103 : Blo 519798 1267103 := bstep (se 1 (by rfl) ⟨950327, by rfl⟩ : syracuseStep 1267103 = 1900655) B1900655
theorem B5920937 : Blo 519798 5920937 := bstep (se 2 (by rfl) ⟨2220351, by rfl⟩ : syracuseStep 5920937 = 4440703) B4440703
theorem B13721237 : Blo 519798 13721237 := bstep (se 6 (by rfl) ⟨321591, by rfl⟩ : syracuseStep 13721237 = 643183) B643183
theorem B780527 : Blo 519798 780527 := bstep (se 1 (by rfl) ⟨585395, by rfl⟩ : syracuseStep 780527 = 1170791) B1170791
theorem B780911 : Blo 519798 780911 := bstep (se 1 (by rfl) ⟨585683, by rfl⟩ : syracuseStep 780911 = 1171367) B1171367
theorem B1765151 : Blo 519798 1765151 := bstep (se 1 (by rfl) ⟨1323863, by rfl⟩ : syracuseStep 1765151 = 2647727) B2647727
theorem B2224043 : Blo 519798 2224043 := bstep (se 1 (by rfl) ⟨1668032, by rfl⟩ : syracuseStep 2224043 = 3336065) B3336065
theorem B56947225 : Blo 519798 56947225 := bstep (se 2 (by rfl) ⟨21355209, by rfl⟩ : syracuseStep 56947225 = 42710419) B42710419
theorem B1765961 : Blo 519798 1765961 := bstep (se 2 (by rfl) ⟨662235, by rfl⟩ : syracuseStep 1765961 = 1324471) B1324471
theorem B521575 : Blo 519798 521575 := bstep (se 1 (by rfl) ⟨391181, by rfl⟩ : syracuseStep 521575 = 782363) B782363
theorem B523263 : Blo 519798 523263 := bstep (se 1 (by rfl) ⟨392447, by rfl⟩ : syracuseStep 523263 = 784895) B784895
theorem B7502867 : Blo 519798 7502867 := bstep (se 1 (by rfl) ⟨5627150, by rfl⟩ : syracuseStep 7502867 = 11254301) B11254301
theorem B11304193 : Blo 519798 11304193 := bstep (se 2 (by rfl) ⟨4239072, by rfl⟩ : syracuseStep 11304193 = 8478145) B8478145
theorem B4456559 : Blo 519798 4456559 := bstep (se 1 (by rfl) ⟨3342419, by rfl⟩ : syracuseStep 4456559 = 6684839) B6684839
theorem B19008107 : Blo 519798 19008107 := bstep (se 1 (by rfl) ⟨14256080, by rfl⟩ : syracuseStep 19008107 = 28512161) B28512161
theorem B9147491 : Blo 519798 9147491 := bstep (se 1 (by rfl) ⟨6860618, by rfl⟩ : syracuseStep 9147491 = 13721237) B13721237
theorem B661375 : Blo 519798 661375 := bstep (se 1 (by rfl) ⟨496031, by rfl⟩ : syracuseStep 661375 = 992063) B992063
theorem B75929633 : Blo 519798 75929633 := bstep (se 2 (by rfl) ⟨28473612, by rfl⟩ : syracuseStep 75929633 = 56947225) B56947225
theorem B1482695 : Blo 519798 1482695 := bstep (se 1 (by rfl) ⟨1112021, by rfl⟩ : syracuseStep 1482695 = 2224043) B2224043
theorem B1979903 : Blo 519798 1979903 := bstep (se 1 (by rfl) ⟨1484927, by rfl⟩ : syracuseStep 1979903 = 2969855) B2969855
theorem B6338371 : Blo 519798 6338371 := bstep (se 1 (by rfl) ⟨4753778, by rfl⟩ : syracuseStep 6338371 = 9507557) B9507557
theorem B3947291 : Blo 519798 3947291 := bstep (se 1 (by rfl) ⟨2960468, by rfl⟩ : syracuseStep 3947291 = 5920937) B5920937
theorem B1985417 : Blo 519798 1985417 := bstep (se 2 (by rfl) ⟨744531, by rfl⟩ : syracuseStep 1985417 = 1489063) B1489063
theorem B1756727 : Blo 519798 1756727 := bstep (se 1 (by rfl) ⟨1317545, by rfl⟩ : syracuseStep 1756727 = 2635091) B2635091
theorem B27578495 : Blo 519798 27578495 := bstep (se 1 (by rfl) ⟨20683871, by rfl⟩ : syracuseStep 27578495 = 41367743) B41367743
theorem B5001911 : Blo 519798 5001911 := bstep (se 1 (by rfl) ⟨3751433, by rfl⟩ : syracuseStep 5001911 = 7502867) B7502867
theorem B2643839 : Blo 519798 2643839 := bstep (se 1 (by rfl) ⟨1982879, by rfl⟩ : syracuseStep 2643839 = 3965759) B3965759
theorem B744167 : Blo 519798 744167 := bstep (se 1 (by rfl) ⟨558125, by rfl⟩ : syracuseStep 744167 = 1116251) B1116251
theorem B844735 : Blo 519798 844735 := bstep (se 1 (by rfl) ⟨633551, by rfl⟩ : syracuseStep 844735 = 1267103) B1267103
theorem B5006711 : Blo 519798 5006711 := bstep (se 1 (by rfl) ⟨3755033, by rfl⟩ : syracuseStep 5006711 = 7510067) B7510067
theorem B20375549 : Blo 519798 20375549 := bstep (se 3 (by rfl) ⟨3820415, by rfl⟩ : syracuseStep 20375549 = 7640831) B7640831
theorem B3762359 : Blo 519798 3762359 := bstep (se 1 (by rfl) ⟨2821769, by rfl⟩ : syracuseStep 3762359 = 5643539) B5643539
theorem B5630957 : Blo 519798 5630957 := bstep (se 3 (by rfl) ⟨1055804, by rfl⟩ : syracuseStep 5630957 = 2111609) B2111609
theorem B520351 : Blo 519798 520351 := bstep (se 1 (by rfl) ⟨390263, by rfl⟩ : syracuseStep 520351 = 780527) B780527
theorem B520607 : Blo 519798 520607 := bstep (se 1 (by rfl) ⟨390455, by rfl⟩ : syracuseStep 520607 = 780911) B780911
theorem B1176767 : Blo 519798 1176767 := bstep (se 1 (by rfl) ⟨882575, by rfl⟩ : syracuseStep 1176767 = 1765151) B1765151
theorem B1177307 : Blo 519798 1177307 := bstep (se 1 (by rfl) ⟨882980, by rfl⟩ : syracuseStep 1177307 = 1765961) B1765961
theorem B11302811 : Blo 519798 11302811 := bstep (se 1 (by rfl) ⟨8477108, by rfl⟩ : syracuseStep 11302811 = 16954217) B16954217
theorem B5077673 : Blo 519798 5077673 := bstep (se 2 (by rfl) ⟨1904127, by rfl⟩ : syracuseStep 5077673 = 3808255) B3808255
theorem B15072257 : Blo 519798 15072257 := bstep (se 2 (by rfl) ⟨5652096, by rfl⟩ : syracuseStep 15072257 = 11304193) B11304193
theorem B19299455 : Blo 519798 19299455 := bstep (se 1 (by rfl) ⟨14474591, by rfl⟩ : syracuseStep 19299455 = 28949183) B28949183
theorem B18385663 : Blo 519798 18385663 := bstep (se 1 (by rfl) ⟨13789247, by rfl⟩ : syracuseStep 18385663 = 27578495) B27578495
theorem B6098327 : Blo 519798 6098327 := bstep (se 1 (by rfl) ⟨4573745, by rfl⟩ : syracuseStep 6098327 = 9147491) B9147491
theorem B988463 : Blo 519798 988463 := bstep (se 1 (by rfl) ⟨741347, by rfl⟩ : syracuseStep 988463 = 1482695) B1482695
theorem B1319935 : Blo 519798 1319935 := bstep (se 1 (by rfl) ⟨989951, by rfl⟩ : syracuseStep 1319935 = 1979903) B1979903
theorem B3385115 : Blo 519798 3385115 := bstep (se 1 (by rfl) ⟨2538836, by rfl⟩ : syracuseStep 3385115 = 5077673) B5077673
theorem B2631527 : Blo 519798 2631527 := bstep (se 1 (by rfl) ⟨1973645, by rfl⟩ : syracuseStep 2631527 = 3947291) B3947291
theorem B1126313 : Blo 519798 1126313 := bstep (se 2 (by rfl) ⟨422367, by rfl⟩ : syracuseStep 1126313 = 844735) B844735
theorem B1323611 : Blo 519798 1323611 := bstep (se 1 (by rfl) ⟨992708, by rfl⟩ : syracuseStep 1323611 = 1985417) B1985417
theorem B13583699 : Blo 519798 13583699 := bstep (se 1 (by rfl) ⟨10187774, by rfl⟩ : syracuseStep 13583699 = 20375549) B20375549
theorem B2508239 : Blo 519798 2508239 := bstep (se 1 (by rfl) ⟨1881179, by rfl⟩ : syracuseStep 2508239 = 3762359) B3762359
theorem B1984445 : Blo 519798 1984445 := bstep (se 3 (by rfl) ⟨372083, by rfl⟩ : syracuseStep 1984445 = 744167) B744167
theorem B3753971 : Blo 519798 3753971 := bstep (se 1 (by rfl) ⟨2815478, by rfl⟩ : syracuseStep 3753971 = 5630957) B5630957
theorem B10048171 : Blo 519798 10048171 := bstep (se 1 (by rfl) ⟨7536128, by rfl⟩ : syracuseStep 10048171 = 15072257) B15072257
theorem B12866303 : Blo 519798 12866303 := bstep (se 1 (by rfl) ⟨9649727, by rfl⟩ : syracuseStep 12866303 = 19299455) B19299455
theorem B2971039 : Blo 519798 2971039 := bstep (se 1 (by rfl) ⟨2228279, by rfl⟩ : syracuseStep 2971039 = 4456559) B4456559
theorem B12672071 : Blo 519798 12672071 := bstep (se 1 (by rfl) ⟨9504053, by rfl⟩ : syracuseStep 12672071 = 19008107) B19008107
theorem B1171151 : Blo 519798 1171151 := bstep (se 1 (by rfl) ⟨878363, by rfl⟩ : syracuseStep 1171151 = 1756727) B1756727
theorem B3334607 : Blo 519798 3334607 := bstep (se 1 (by rfl) ⟨2500955, by rfl⟩ : syracuseStep 3334607 = 5001911) B5001911
theorem B1762559 : Blo 519798 1762559 := bstep (se 1 (by rfl) ⟨1321919, by rfl⟩ : syracuseStep 1762559 = 2643839) B2643839
theorem B50619755 : Blo 519798 50619755 := bstep (se 1 (by rfl) ⟨37964816, by rfl⟩ : syracuseStep 50619755 = 75929633) B75929633
theorem B3337807 : Blo 519798 3337807 := bstep (se 1 (by rfl) ⟨2503355, by rfl⟩ : syracuseStep 3337807 = 5006711) B5006711
theorem B8451161 : Blo 519798 8451161 := bstep (se 2 (by rfl) ⟨3169185, by rfl⟩ : syracuseStep 8451161 = 6338371) B6338371
theorem B881833 : Blo 519798 881833 := bstep (se 2 (by rfl) ⟨330687, by rfl⟩ : syracuseStep 881833 = 661375) B661375
theorem B784511 : Blo 519798 784511 := bstep (se 1 (by rfl) ⟨588383, by rfl⟩ : syracuseStep 784511 = 1176767) B1176767
theorem B784871 : Blo 519798 784871 := bstep (se 1 (by rfl) ⟨588653, by rfl⟩ : syracuseStep 784871 = 1177307) B1177307
theorem B7535207 : Blo 519798 7535207 := bstep (se 1 (by rfl) ⟨5651405, by rfl⟩ : syracuseStep 7535207 = 11302811) B11302811
theorem B1672159 : Blo 519798 1672159 := bstep (se 1 (by rfl) ⟨1254119, by rfl⟩ : syracuseStep 1672159 = 2508239) B2508239
theorem B4065551 : Blo 519798 4065551 := bstep (se 1 (by rfl) ⟨3049163, by rfl⟩ : syracuseStep 4065551 = 6098327) B6098327
theorem B24514217 : Blo 519798 24514217 := bstep (se 2 (by rfl) ⟨9192831, by rfl⟩ : syracuseStep 24514217 = 18385663) B18385663
theorem B5023471 : Blo 519798 5023471 := bstep (se 1 (by rfl) ⟨3767603, by rfl⟩ : syracuseStep 5023471 = 7535207) B7535207
theorem B9055799 : Blo 519798 9055799 := bstep (se 1 (by rfl) ⟨6791849, by rfl⟩ : syracuseStep 9055799 = 13583699) B13583699
theorem B1322963 : Blo 519798 1322963 := bstep (se 1 (by rfl) ⟨992222, by rfl⟩ : syracuseStep 1322963 = 1984445) B1984445
theorem B2502647 : Blo 519798 2502647 := bstep (se 1 (by rfl) ⟨1876985, by rfl⟩ : syracuseStep 2502647 = 3753971) B3753971
theorem B2635901 : Blo 519798 2635901 := bstep (se 3 (by rfl) ⟨494231, by rfl⟩ : syracuseStep 2635901 = 988463) B988463
theorem B1754351 : Blo 519798 1754351 := bstep (se 1 (by rfl) ⟨1315763, by rfl⟩ : syracuseStep 1754351 = 2631527) B2631527
theorem B1759913 : Blo 519798 1759913 := bstep (se 2 (by rfl) ⟨659967, by rfl⟩ : syracuseStep 1759913 = 1319935) B1319935
theorem B8577535 : Blo 519798 8577535 := bstep (se 1 (by rfl) ⟨6433151, by rfl⟩ : syracuseStep 8577535 = 12866303) B12866303
theorem B8448047 : Blo 519798 8448047 := bstep (se 1 (by rfl) ⟨6336035, by rfl⟩ : syracuseStep 8448047 = 12672071) B12672071
theorem B4450409 : Blo 519798 4450409 := bstep (se 2 (by rfl) ⟨1668903, by rfl⟩ : syracuseStep 4450409 = 3337807) B3337807
theorem B780767 : Blo 519798 780767 := bstep (se 1 (by rfl) ⟨585575, by rfl⟩ : syracuseStep 780767 = 1171151) B1171151
theorem B2223071 : Blo 519798 2223071 := bstep (se 1 (by rfl) ⟨1667303, by rfl⟩ : syracuseStep 2223071 = 3334607) B3334607
theorem B1175039 : Blo 519798 1175039 := bstep (se 1 (by rfl) ⟨881279, by rfl⟩ : syracuseStep 1175039 = 1762559) B1762559
theorem B13397561 : Blo 519798 13397561 := bstep (se 2 (by rfl) ⟨5024085, by rfl⟩ : syracuseStep 13397561 = 10048171) B10048171
theorem B33746503 : Blo 519798 33746503 := bstep (se 1 (by rfl) ⟨25309877, by rfl⟩ : syracuseStep 33746503 = 50619755) B50619755
theorem B2256743 : Blo 519798 2256743 := bstep (se 1 (by rfl) ⟨1692557, by rfl⟩ : syracuseStep 2256743 = 3385115) B3385115
theorem B1175777 : Blo 519798 1175777 := bstep (se 2 (by rfl) ⟨440916, by rfl⟩ : syracuseStep 1175777 = 881833) B881833
theorem B3961385 : Blo 519798 3961385 := bstep (se 2 (by rfl) ⟨1485519, by rfl⟩ : syracuseStep 3961385 = 2971039) B2971039
theorem B750875 : Blo 519798 750875 := bstep (se 1 (by rfl) ⟨563156, by rfl⟩ : syracuseStep 750875 = 1126313) B1126313
theorem B882407 : Blo 519798 882407 := bstep (se 1 (by rfl) ⟨661805, by rfl⟩ : syracuseStep 882407 = 1323611) B1323611
theorem B5634107 : Blo 519798 5634107 := bstep (se 1 (by rfl) ⟨4225580, by rfl⟩ : syracuseStep 5634107 = 8451161) B8451161
theorem B523007 : Blo 519798 523007 := bstep (se 1 (by rfl) ⟨392255, by rfl⟩ : syracuseStep 523007 = 784511) B784511
theorem B523247 : Blo 519798 523247 := bstep (se 1 (by rfl) ⟨392435, by rfl⟩ : syracuseStep 523247 = 784871) B784871
theorem B11436713 : Blo 519798 11436713 := bstep (se 2 (by rfl) ⟨4288767, by rfl⟩ : syracuseStep 11436713 = 8577535) B8577535
theorem B2229545 : Blo 519798 2229545 := bstep (se 2 (by rfl) ⟨836079, by rfl⟩ : syracuseStep 2229545 = 1672159) B1672159
theorem B2002333 : Blo 519798 2002333 := bstep (se 3 (by rfl) ⟨375437, by rfl⟩ : syracuseStep 2002333 = 750875) B750875
theorem B44995337 : Blo 519798 44995337 := bstep (se 2 (by rfl) ⟨16873251, by rfl⟩ : syracuseStep 44995337 = 33746503) B33746503
theorem B1482047 : Blo 519798 1482047 := bstep (se 1 (by rfl) ⟨1111535, by rfl⟩ : syracuseStep 1482047 = 2223071) B2223071
theorem B6037199 : Blo 519798 6037199 := bstep (se 1 (by rfl) ⟨4527899, by rfl⟩ : syracuseStep 6037199 = 9055799) B9055799
theorem B6697961 : Blo 519798 6697961 := bstep (se 2 (by rfl) ⟨2511735, by rfl⟩ : syracuseStep 6697961 = 5023471) B5023471
theorem B2966939 : Blo 519798 2966939 := bstep (se 1 (by rfl) ⟨2225204, by rfl⟩ : syracuseStep 2966939 = 4450409) B4450409
theorem B8931707 : Blo 519798 8931707 := bstep (se 1 (by rfl) ⟨6698780, by rfl⟩ : syracuseStep 8931707 = 13397561) B13397561
theorem B2640923 : Blo 519798 2640923 := bstep (se 1 (by rfl) ⟨1980692, by rfl⟩ : syracuseStep 2640923 = 3961385) B3961385
theorem B3756071 : Blo 519798 3756071 := bstep (se 1 (by rfl) ⟨2817053, by rfl⟩ : syracuseStep 3756071 = 5634107) B5634107
theorem B1757267 : Blo 519798 1757267 := bstep (se 1 (by rfl) ⟨1317950, by rfl⟩ : syracuseStep 1757267 = 2635901) B2635901
theorem B1169567 : Blo 519798 1169567 := bstep (se 1 (by rfl) ⟨877175, by rfl⟩ : syracuseStep 1169567 = 1754351) B1754351
theorem B2710367 : Blo 519798 2710367 := bstep (se 1 (by rfl) ⟨2032775, by rfl⟩ : syracuseStep 2710367 = 4065551) B4065551
theorem B16342811 : Blo 519798 16342811 := bstep (se 1 (by rfl) ⟨12257108, by rfl⟩ : syracuseStep 16342811 = 24514217) B24514217
theorem B1173275 : Blo 519798 1173275 := bstep (se 1 (by rfl) ⟨879956, by rfl⟩ : syracuseStep 1173275 = 1759913) B1759913
theorem B5632031 : Blo 519798 5632031 := bstep (se 1 (by rfl) ⟨4224023, by rfl⟩ : syracuseStep 5632031 = 8448047) B8448047
theorem B520511 : Blo 519798 520511 := bstep (se 1 (by rfl) ⟨390383, by rfl⟩ : syracuseStep 520511 = 780767) B780767
theorem B783359 : Blo 519798 783359 := bstep (se 1 (by rfl) ⟨587519, by rfl⟩ : syracuseStep 783359 = 1175039) B1175039
theorem B1504495 : Blo 519798 1504495 := bstep (se 1 (by rfl) ⟨1128371, by rfl⟩ : syracuseStep 1504495 = 2256743) B2256743
theorem B881975 : Blo 519798 881975 := bstep (se 1 (by rfl) ⟨661481, by rfl⟩ : syracuseStep 881975 = 1322963) B1322963
theorem B1668431 : Blo 519798 1668431 := bstep (se 1 (by rfl) ⟨1251323, by rfl⟩ : syracuseStep 1668431 = 2502647) B2502647
theorem B783851 : Blo 519798 783851 := bstep (se 1 (by rfl) ⟨587888, by rfl⟩ : syracuseStep 783851 = 1175777) B1175777
theorem B588271 : Blo 519798 588271 := bstep (se 1 (by rfl) ⟨441203, by rfl⟩ : syracuseStep 588271 = 882407) B882407
theorem B1806911 : Blo 519798 1806911 := bstep (se 1 (by rfl) ⟨1355183, by rfl⟩ : syracuseStep 1806911 = 2710367) B2710367
theorem B988031 : Blo 519798 988031 := bstep (se 1 (by rfl) ⟨741023, by rfl⟩ : syracuseStep 988031 = 1482047) B1482047
theorem B2005993 : Blo 519798 2005993 := bstep (se 2 (by rfl) ⟨752247, by rfl⟩ : syracuseStep 2005993 = 1504495) B1504495
theorem B4465307 : Blo 519798 4465307 := bstep (se 1 (by rfl) ⟨3348980, by rfl⟩ : syracuseStep 4465307 = 6697961) B6697961
theorem B1486363 : Blo 519798 1486363 := bstep (se 1 (by rfl) ⟨1114772, by rfl⟩ : syracuseStep 1486363 = 2229545) B2229545
theorem B1977959 : Blo 519798 1977959 := bstep (se 1 (by rfl) ⟨1483469, by rfl⟩ : syracuseStep 1977959 = 2966939) B2966939
theorem B2504047 : Blo 519798 2504047 := bstep (se 1 (by rfl) ⟨1878035, by rfl⟩ : syracuseStep 2504047 = 3756071) B3756071
theorem B29996891 : Blo 519798 29996891 := bstep (se 1 (by rfl) ⟨22497668, by rfl⟩ : syracuseStep 29996891 = 44995337) B44995337
theorem B2669777 : Blo 519798 2669777 := bstep (se 2 (by rfl) ⟨1001166, by rfl⟩ : syracuseStep 2669777 = 2002333) B2002333
theorem B10895207 : Blo 519798 10895207 := bstep (se 1 (by rfl) ⟨8171405, by rfl⟩ : syracuseStep 10895207 = 16342811) B16342811
theorem B3754687 : Blo 519798 3754687 := bstep (se 1 (by rfl) ⟨2816015, by rfl⟩ : syracuseStep 3754687 = 5632031) B5632031
theorem B7624475 : Blo 519798 7624475 := bstep (se 1 (by rfl) ⟨5718356, by rfl⟩ : syracuseStep 7624475 = 11436713) B11436713
theorem B5954471 : Blo 519798 5954471 := bstep (se 1 (by rfl) ⟨4465853, by rfl⟩ : syracuseStep 5954471 = 8931707) B8931707
theorem B1760615 : Blo 519798 1760615 := bstep (se 1 (by rfl) ⟨1320461, by rfl⟩ : syracuseStep 1760615 = 2640923) B2640923
theorem B1171511 : Blo 519798 1171511 := bstep (se 1 (by rfl) ⟨878633, by rfl⟩ : syracuseStep 1171511 = 1757267) B1757267
theorem B779711 : Blo 519798 779711 := bstep (se 1 (by rfl) ⟨584783, by rfl⟩ : syracuseStep 779711 = 1169567) B1169567
theorem B4024799 : Blo 519798 4024799 := bstep (se 1 (by rfl) ⟨3018599, by rfl⟩ : syracuseStep 4024799 = 6037199) B6037199
theorem B782183 : Blo 519798 782183 := bstep (se 1 (by rfl) ⟨586637, by rfl⟩ : syracuseStep 782183 = 1173275) B1173275
theorem B784361 : Blo 519798 784361 := bstep (se 2 (by rfl) ⟨294135, by rfl⟩ : syracuseStep 784361 = 588271) B588271
theorem B522239 : Blo 519798 522239 := bstep (se 1 (by rfl) ⟨391679, by rfl⟩ : syracuseStep 522239 = 783359) B783359
theorem B587983 : Blo 519798 587983 := bstep (se 1 (by rfl) ⟨440987, by rfl⟩ : syracuseStep 587983 = 881975) B881975
theorem B1112287 : Blo 519798 1112287 := bstep (se 1 (by rfl) ⟨834215, by rfl⟩ : syracuseStep 1112287 = 1668431) B1668431
theorem B522567 : Blo 519798 522567 := bstep (se 1 (by rfl) ⟨391925, by rfl⟩ : syracuseStep 522567 = 783851) B783851
theorem B658687 : Blo 519798 658687 := bstep (se 1 (by rfl) ⟨494015, by rfl⟩ : syracuseStep 658687 = 988031) B988031
theorem B5082983 : Blo 519798 5082983 := bstep (se 1 (by rfl) ⟨3812237, by rfl⟩ : syracuseStep 5082983 = 7624475) B7624475
theorem B3969647 : Blo 519798 3969647 := bstep (se 1 (by rfl) ⟨2977235, by rfl⟩ : syracuseStep 3969647 = 5954471) B5954471
theorem B1318639 : Blo 519798 1318639 := bstep (se 1 (by rfl) ⟨988979, by rfl⟩ : syracuseStep 1318639 = 1977959) B1977959
theorem B1483049 : Blo 519798 1483049 := bstep (se 2 (by rfl) ⟨556143, by rfl⟩ : syracuseStep 1483049 = 1112287) B1112287
theorem B19997927 : Blo 519798 19997927 := bstep (se 1 (by rfl) ⟨14998445, by rfl⟩ : syracuseStep 19997927 = 29996891) B29996891
theorem B1779851 : Blo 519798 1779851 := bstep (se 1 (by rfl) ⟨1334888, by rfl⟩ : syracuseStep 1779851 = 2669777) B2669777
theorem B1981817 : Blo 519798 1981817 := bstep (se 2 (by rfl) ⟨743181, by rfl⟩ : syracuseStep 1981817 = 1486363) B1486363
theorem B2674657 : Blo 519798 2674657 := bstep (se 2 (by rfl) ⟨1002996, by rfl⟩ : syracuseStep 2674657 = 2005993) B2005993
theorem B29053885 : Blo 519798 29053885 := bstep (se 3 (by rfl) ⟨5447603, by rfl⟩ : syracuseStep 29053885 = 10895207) B10895207
theorem B1204607 : Blo 519798 1204607 := bstep (se 1 (by rfl) ⟨903455, by rfl⟩ : syracuseStep 1204607 = 1806911) B1806911
theorem B5006249 : Blo 519798 5006249 := bstep (se 2 (by rfl) ⟨1877343, by rfl⟩ : syracuseStep 5006249 = 3754687) B3754687
theorem B1173743 : Blo 519798 1173743 := bstep (se 1 (by rfl) ⟨880307, by rfl⟩ : syracuseStep 1173743 = 1760615) B1760615
theorem B781007 : Blo 519798 781007 := bstep (se 1 (by rfl) ⟨585755, by rfl⟩ : syracuseStep 781007 = 1171511) B1171511
theorem B2976871 : Blo 519798 2976871 := bstep (se 1 (by rfl) ⟨2232653, by rfl⟩ : syracuseStep 2976871 = 4465307) B4465307
theorem B519807 : Blo 519798 519807 := bstep (se 1 (by rfl) ⟨389855, by rfl⟩ : syracuseStep 519807 = 779711) B779711
theorem B2683199 : Blo 519798 2683199 := bstep (se 1 (by rfl) ⟨2012399, by rfl⟩ : syracuseStep 2683199 = 4024799) B4024799
theorem B3338729 : Blo 519798 3338729 := bstep (se 2 (by rfl) ⟨1252023, by rfl⟩ : syracuseStep 3338729 = 2504047) B2504047
theorem B521455 : Blo 519798 521455 := bstep (se 1 (by rfl) ⟨391091, by rfl⟩ : syracuseStep 521455 = 782183) B782183
theorem B783977 : Blo 519798 783977 := bstep (se 2 (by rfl) ⟨293991, by rfl⟩ : syracuseStep 783977 = 587983) B587983
theorem B522907 : Blo 519798 522907 := bstep (se 1 (by rfl) ⟨392180, by rfl⟩ : syracuseStep 522907 = 784361) B784361
theorem B3969161 : Blo 519798 3969161 := bstep (se 2 (by rfl) ⟨1488435, by rfl⟩ : syracuseStep 3969161 = 2976871) B2976871
theorem B988699 : Blo 519798 988699 := bstep (se 1 (by rfl) ⟨741524, by rfl⟩ : syracuseStep 988699 = 1483049) B1483049
theorem B38738513 : Blo 519798 38738513 := bstep (se 2 (by rfl) ⟨14526942, by rfl⟩ : syracuseStep 38738513 = 29053885) B29053885
theorem B1321211 : Blo 519798 1321211 := bstep (se 1 (by rfl) ⟨990908, by rfl⟩ : syracuseStep 1321211 = 1981817) B1981817
theorem B3388655 : Blo 519798 3388655 := bstep (se 1 (by rfl) ⟨2541491, by rfl⟩ : syracuseStep 3388655 = 5082983) B5082983
theorem B803071 : Blo 519798 803071 := bstep (se 1 (by rfl) ⟨602303, by rfl⟩ : syracuseStep 803071 = 1204607) B1204607
theorem B1788799 : Blo 519798 1788799 := bstep (se 1 (by rfl) ⟨1341599, by rfl⟩ : syracuseStep 1788799 = 2683199) B2683199
theorem B1758185 : Blo 519798 1758185 := bstep (se 2 (by rfl) ⟨659319, by rfl⟩ : syracuseStep 1758185 = 1318639) B1318639
theorem B2646431 : Blo 519798 2646431 := bstep (se 1 (by rfl) ⟨1984823, by rfl⟩ : syracuseStep 2646431 = 3969647) B3969647
theorem B878249 : Blo 519798 878249 := bstep (se 2 (by rfl) ⟨329343, by rfl⟩ : syracuseStep 878249 = 658687) B658687
theorem B3566209 : Blo 519798 3566209 := bstep (se 2 (by rfl) ⟨1337328, by rfl⟩ : syracuseStep 3566209 = 2674657) B2674657
theorem B4746269 : Blo 519798 4746269 := bstep (se 3 (by rfl) ⟨889925, by rfl⟩ : syracuseStep 4746269 = 1779851) B1779851
theorem B3337499 : Blo 519798 3337499 := bstep (se 1 (by rfl) ⟨2503124, by rfl⟩ : syracuseStep 3337499 = 5006249) B5006249
theorem B13331951 : Blo 519798 13331951 := bstep (se 1 (by rfl) ⟨9998963, by rfl⟩ : syracuseStep 13331951 = 19997927) B19997927
theorem B782495 : Blo 519798 782495 := bstep (se 1 (by rfl) ⟨586871, by rfl⟩ : syracuseStep 782495 = 1173743) B1173743
theorem B520671 : Blo 519798 520671 := bstep (se 1 (by rfl) ⟨390503, by rfl⟩ : syracuseStep 520671 = 781007) B781007
theorem B2225819 : Blo 519798 2225819 := bstep (se 1 (by rfl) ⟨1669364, by rfl⟩ : syracuseStep 2225819 = 3338729) B3338729
theorem B522651 : Blo 519798 522651 := bstep (se 1 (by rfl) ⟨391988, by rfl⟩ : syracuseStep 522651 = 783977) B783977
theorem B4754945 : Blo 519798 4754945 := bstep (se 2 (by rfl) ⟨1783104, by rfl⟩ : syracuseStep 4754945 = 3566209) B3566209
theorem B25825675 : Blo 519798 25825675 := bstep (se 1 (by rfl) ⟨19369256, by rfl⟩ : syracuseStep 25825675 = 38738513) B38738513
theorem B5935517 : Blo 519798 5935517 := bstep (se 3 (by rfl) ⟨1112909, by rfl⟩ : syracuseStep 5935517 = 2225819) B2225819
theorem B1318265 : Blo 519798 1318265 := bstep (se 2 (by rfl) ⟨494349, by rfl⟩ : syracuseStep 1318265 = 988699) B988699
theorem B8887967 : Blo 519798 8887967 := bstep (se 1 (by rfl) ⟨6665975, by rfl⟩ : syracuseStep 8887967 = 13331951) B13331951
theorem B3164179 : Blo 519798 3164179 := bstep (se 1 (by rfl) ⟨2373134, by rfl⟩ : syracuseStep 3164179 = 4746269) B4746269
theorem B1070761 : Blo 519798 1070761 := bstep (se 2 (by rfl) ⟨401535, by rfl⟩ : syracuseStep 1070761 = 803071) B803071
theorem B2646107 : Blo 519798 2646107 := bstep (se 1 (by rfl) ⟨1984580, by rfl⟩ : syracuseStep 2646107 = 3969161) B3969161
theorem B1172123 : Blo 519798 1172123 := bstep (se 1 (by rfl) ⟨879092, by rfl⟩ : syracuseStep 1172123 = 1758185) B1758185
theorem B2385065 : Blo 519798 2385065 := bstep (se 2 (by rfl) ⟨894399, by rfl⟩ : syracuseStep 2385065 = 1788799) B1788799
theorem B1764287 : Blo 519798 1764287 := bstep (se 1 (by rfl) ⟨1323215, by rfl⟩ : syracuseStep 1764287 = 2646431) B2646431
theorem B585499 : Blo 519798 585499 := bstep (se 1 (by rfl) ⟨439124, by rfl⟩ : syracuseStep 585499 = 878249) B878249
theorem B880807 : Blo 519798 880807 := bstep (se 1 (by rfl) ⟨660605, by rfl⟩ : syracuseStep 880807 = 1321211) B1321211
theorem B2224999 : Blo 519798 2224999 := bstep (se 1 (by rfl) ⟨1668749, by rfl⟩ : syracuseStep 2224999 = 3337499) B3337499
theorem B521663 : Blo 519798 521663 := bstep (se 1 (by rfl) ⟨391247, by rfl⟩ : syracuseStep 521663 = 782495) B782495
theorem B2259103 : Blo 519798 2259103 := bstep (se 1 (by rfl) ⟨1694327, by rfl⟩ : syracuseStep 2259103 = 3388655) B3388655
theorem B1590043 : Blo 519798 1590043 := bstep (se 1 (by rfl) ⟨1192532, by rfl⟩ : syracuseStep 1590043 = 2385065) B2385065
theorem B2966665 : Blo 519798 2966665 := bstep (se 2 (by rfl) ⟨1112499, by rfl⟩ : syracuseStep 2966665 = 2224999) B2224999
theorem B1427681 : Blo 519798 1427681 := bstep (se 2 (by rfl) ⟨535380, by rfl⟩ : syracuseStep 1427681 = 1070761) B1070761
theorem B3169963 : Blo 519798 3169963 := bstep (se 1 (by rfl) ⟨2377472, by rfl⟩ : syracuseStep 3169963 = 4754945) B4754945
theorem B4218905 : Blo 519798 4218905 := bstep (se 2 (by rfl) ⟨1582089, by rfl⟩ : syracuseStep 4218905 = 3164179) B3164179
theorem B3957011 : Blo 519798 3957011 := bstep (se 1 (by rfl) ⟨2967758, by rfl⟩ : syracuseStep 3957011 = 5935517) B5935517
theorem B878843 : Blo 519798 878843 := bstep (se 1 (by rfl) ⟨659132, by rfl⟩ : syracuseStep 878843 = 1318265) B1318265
theorem B780665 : Blo 519798 780665 := bstep (se 2 (by rfl) ⟨292749, by rfl⟩ : syracuseStep 780665 = 585499) B585499
theorem B5925311 : Blo 519798 5925311 := bstep (se 1 (by rfl) ⟨4443983, by rfl⟩ : syracuseStep 5925311 = 8887967) B8887967
theorem B1764071 : Blo 519798 1764071 := bstep (se 1 (by rfl) ⟨1323053, by rfl⟩ : syracuseStep 1764071 = 2646107) B2646107
theorem B1174409 : Blo 519798 1174409 := bstep (se 2 (by rfl) ⟨440403, by rfl⟩ : syracuseStep 1174409 = 880807) B880807
theorem B781415 : Blo 519798 781415 := bstep (se 1 (by rfl) ⟨586061, by rfl⟩ : syracuseStep 781415 = 1172123) B1172123
theorem B34434233 : Blo 519798 34434233 := bstep (se 2 (by rfl) ⟨12912837, by rfl⟩ : syracuseStep 34434233 = 25825675) B25825675
theorem B1176191 : Blo 519798 1176191 := bstep (se 1 (by rfl) ⟨882143, by rfl⟩ : syracuseStep 1176191 = 1764287) B1764287
theorem B3012137 : Blo 519798 3012137 := bstep (se 2 (by rfl) ⟨1129551, by rfl⟩ : syracuseStep 3012137 = 2259103) B2259103
theorem B951787 : Blo 519798 951787 := bstep (se 1 (by rfl) ⟨713840, by rfl⟩ : syracuseStep 951787 = 1427681) B1427681
theorem B2008091 : Blo 519798 2008091 := bstep (se 1 (by rfl) ⟨1506068, by rfl⟩ : syracuseStep 2008091 = 3012137) B3012137
theorem B2638007 : Blo 519798 2638007 := bstep (se 1 (by rfl) ⟨1978505, by rfl⟩ : syracuseStep 2638007 = 3957011) B3957011
theorem B3950207 : Blo 519798 3950207 := bstep (se 1 (by rfl) ⟨2962655, by rfl⟩ : syracuseStep 3950207 = 5925311) B5925311
theorem B22956155 : Blo 519798 22956155 := bstep (se 1 (by rfl) ⟨17217116, by rfl⟩ : syracuseStep 22956155 = 34434233) B34434233
theorem B2120057 : Blo 519798 2120057 := bstep (se 2 (by rfl) ⟨795021, by rfl⟩ : syracuseStep 2120057 = 1590043) B1590043
theorem B3955553 : Blo 519798 3955553 := bstep (se 2 (by rfl) ⟨1483332, by rfl⟩ : syracuseStep 3955553 = 2966665) B2966665
theorem B2812603 : Blo 519798 2812603 := bstep (se 1 (by rfl) ⟨2109452, by rfl⟩ : syracuseStep 2812603 = 4218905) B4218905
theorem B585895 : Blo 519798 585895 := bstep (se 1 (by rfl) ⟨439421, by rfl⟩ : syracuseStep 585895 = 878843) B878843
theorem B520443 : Blo 519798 520443 := bstep (se 1 (by rfl) ⟨390332, by rfl⟩ : syracuseStep 520443 = 780665) B780665
theorem B1176047 : Blo 519798 1176047 := bstep (se 1 (by rfl) ⟨882035, by rfl⟩ : syracuseStep 1176047 = 1764071) B1764071
theorem B782939 : Blo 519798 782939 := bstep (se 1 (by rfl) ⟨587204, by rfl⟩ : syracuseStep 782939 = 1174409) B1174409
theorem B520943 : Blo 519798 520943 := bstep (se 1 (by rfl) ⟨390707, by rfl⟩ : syracuseStep 520943 = 781415) B781415
theorem B784127 : Blo 519798 784127 := bstep (se 1 (by rfl) ⟨588095, by rfl⟩ : syracuseStep 784127 = 1176191) B1176191
theorem B4226617 : Blo 519798 4226617 := bstep (se 2 (by rfl) ⟨1584981, by rfl⟩ : syracuseStep 4226617 = 3169963) B3169963
theorem B15304103 : Blo 519798 15304103 := bstep (se 1 (by rfl) ⟨11478077, by rfl⟩ : syracuseStep 15304103 = 22956155) B22956155
theorem B1413371 : Blo 519798 1413371 := bstep (se 1 (by rfl) ⟨1060028, by rfl⟩ : syracuseStep 1413371 = 2120057) B2120057
theorem B2633471 : Blo 519798 2633471 := bstep (se 1 (by rfl) ⟨1975103, by rfl⟩ : syracuseStep 2633471 = 3950207) B3950207
theorem B3750137 : Blo 519798 3750137 := bstep (se 2 (by rfl) ⟨1406301, by rfl⟩ : syracuseStep 3750137 = 2812603) B2812603
theorem B2637035 : Blo 519798 2637035 := bstep (se 1 (by rfl) ⟨1977776, by rfl⟩ : syracuseStep 2637035 = 3955553) B3955553
theorem B1758671 : Blo 519798 1758671 := bstep (se 1 (by rfl) ⟨1319003, by rfl⟩ : syracuseStep 1758671 = 2638007) B2638007
theorem B1269049 : Blo 519798 1269049 := bstep (se 2 (by rfl) ⟨475893, by rfl⟩ : syracuseStep 1269049 = 951787) B951787
theorem B781193 : Blo 519798 781193 := bstep (se 2 (by rfl) ⟨292947, by rfl⟩ : syracuseStep 781193 = 585895) B585895
theorem B1338727 : Blo 519798 1338727 := bstep (se 1 (by rfl) ⟨1004045, by rfl⟩ : syracuseStep 1338727 = 2008091) B2008091
theorem B784031 : Blo 519798 784031 := bstep (se 1 (by rfl) ⟨588023, by rfl⟩ : syracuseStep 784031 = 1176047) B1176047
theorem B521959 : Blo 519798 521959 := bstep (se 1 (by rfl) ⟨391469, by rfl⟩ : syracuseStep 521959 = 782939) B782939
theorem B522751 : Blo 519798 522751 := bstep (se 1 (by rfl) ⟨392063, by rfl⟩ : syracuseStep 522751 = 784127) B784127
theorem B5635489 : Blo 519798 5635489 := bstep (se 2 (by rfl) ⟨2113308, by rfl⟩ : syracuseStep 5635489 = 4226617) B4226617
theorem B2500091 : Blo 519798 2500091 := bstep (se 1 (by rfl) ⟨1875068, by rfl⟩ : syracuseStep 2500091 = 3750137) B3750137
theorem B7513985 : Blo 519798 7513985 := bstep (se 2 (by rfl) ⟨2817744, by rfl⟩ : syracuseStep 7513985 = 5635489) B5635489
theorem B10202735 : Blo 519798 10202735 := bstep (se 1 (by rfl) ⟨7652051, by rfl⟩ : syracuseStep 10202735 = 15304103) B15304103
theorem B1784969 : Blo 519798 1784969 := bstep (se 2 (by rfl) ⟨669363, by rfl⟩ : syracuseStep 1784969 = 1338727) B1338727
theorem B1755647 : Blo 519798 1755647 := bstep (se 1 (by rfl) ⟨1316735, by rfl⟩ : syracuseStep 1755647 = 2633471) B2633471
theorem B1692065 : Blo 519798 1692065 := bstep (se 2 (by rfl) ⟨634524, by rfl⟩ : syracuseStep 1692065 = 1269049) B1269049
theorem B1758023 : Blo 519798 1758023 := bstep (se 1 (by rfl) ⟨1318517, by rfl⟩ : syracuseStep 1758023 = 2637035) B2637035
theorem B942247 : Blo 519798 942247 := bstep (se 1 (by rfl) ⟨706685, by rfl⟩ : syracuseStep 942247 = 1413371) B1413371
theorem B1172447 : Blo 519798 1172447 := bstep (se 1 (by rfl) ⟨879335, by rfl⟩ : syracuseStep 1172447 = 1758671) B1758671
theorem B520795 : Blo 519798 520795 := bstep (se 1 (by rfl) ⟨390596, by rfl⟩ : syracuseStep 520795 = 781193) B781193
theorem B522687 : Blo 519798 522687 := bstep (se 1 (by rfl) ⟨392015, by rfl⟩ : syracuseStep 522687 = 784031) B784031
theorem B1189979 : Blo 519798 1189979 := bstep (se 1 (by rfl) ⟨892484, by rfl⟩ : syracuseStep 1189979 = 1784969) B1784969
theorem B1256329 : Blo 519798 1256329 := bstep (se 2 (by rfl) ⟨471123, by rfl⟩ : syracuseStep 1256329 = 942247) B942247
theorem B1128043 : Blo 519798 1128043 := bstep (se 1 (by rfl) ⟨846032, by rfl⟩ : syracuseStep 1128043 = 1692065) B1692065
theorem B20037293 : Blo 519798 20037293 := bstep (se 3 (by rfl) ⟨3756992, by rfl⟩ : syracuseStep 20037293 = 7513985) B7513985
theorem B6801823 : Blo 519798 6801823 := bstep (se 1 (by rfl) ⟨5101367, by rfl⟩ : syracuseStep 6801823 = 10202735) B10202735
theorem B1170431 : Blo 519798 1170431 := bstep (se 1 (by rfl) ⟨877823, by rfl⟩ : syracuseStep 1170431 = 1755647) B1755647
theorem B1172015 : Blo 519798 1172015 := bstep (se 1 (by rfl) ⟨879011, by rfl⟩ : syracuseStep 1172015 = 1758023) B1758023
theorem B781631 : Blo 519798 781631 := bstep (se 1 (by rfl) ⟨586223, by rfl⟩ : syracuseStep 781631 = 1172447) B1172447
theorem B1666727 : Blo 519798 1666727 := bstep (se 1 (by rfl) ⟨1250045, by rfl⟩ : syracuseStep 1666727 = 2500091) B2500091
theorem B793319 : Blo 519798 793319 := bstep (se 1 (by rfl) ⟨594989, by rfl⟩ : syracuseStep 793319 = 1189979) B1189979
theorem B6700421 : Blo 519798 6700421 := bstep (se 4 (by rfl) ⟨628164, by rfl⟩ : syracuseStep 6700421 = 1256329) B1256329
theorem B13358195 : Blo 519798 13358195 := bstep (se 1 (by rfl) ⟨10018646, by rfl⟩ : syracuseStep 13358195 = 20037293) B20037293
theorem B9069097 : Blo 519798 9069097 := bstep (se 2 (by rfl) ⟨3400911, by rfl⟩ : syracuseStep 9069097 = 6801823) B6801823
theorem B780287 : Blo 519798 780287 := bstep (se 1 (by rfl) ⟨585215, by rfl⟩ : syracuseStep 780287 = 1170431) B1170431
theorem B781343 : Blo 519798 781343 := bstep (se 1 (by rfl) ⟨586007, by rfl⟩ : syracuseStep 781343 = 1172015) B1172015
theorem B1504057 : Blo 519798 1504057 := bstep (se 2 (by rfl) ⟨564021, by rfl⟩ : syracuseStep 1504057 = 1128043) B1128043
theorem B521087 : Blo 519798 521087 := bstep (se 1 (by rfl) ⟨390815, by rfl⟩ : syracuseStep 521087 = 781631) B781631
theorem B1111151 : Blo 519798 1111151 := bstep (se 1 (by rfl) ⟨833363, by rfl⟩ : syracuseStep 1111151 = 1666727) B1666727
theorem B12092129 : Blo 519798 12092129 := bstep (se 2 (by rfl) ⟨4534548, by rfl⟩ : syracuseStep 12092129 = 9069097) B9069097
theorem B2005409 : Blo 519798 2005409 := bstep (se 2 (by rfl) ⟨752028, by rfl⟩ : syracuseStep 2005409 = 1504057) B1504057
theorem B4466947 : Blo 519798 4466947 := bstep (se 1 (by rfl) ⟨3350210, by rfl⟩ : syracuseStep 4466947 = 6700421) B6700421
theorem B2115517 : Blo 519798 2115517 := bstep (se 3 (by rfl) ⟨396659, by rfl⟩ : syracuseStep 2115517 = 793319) B793319
theorem B740767 : Blo 519798 740767 := bstep (se 1 (by rfl) ⟨555575, by rfl⟩ : syracuseStep 740767 = 1111151) B1111151
theorem B8905463 : Blo 519798 8905463 := bstep (se 1 (by rfl) ⟨6679097, by rfl⟩ : syracuseStep 8905463 = 13358195) B13358195
theorem B520191 : Blo 519798 520191 := bstep (se 1 (by rfl) ⟨390143, by rfl⟩ : syracuseStep 520191 = 780287) B780287
theorem B520895 : Blo 519798 520895 := bstep (se 1 (by rfl) ⟨390671, by rfl⟩ : syracuseStep 520895 = 781343) B781343
theorem B8061419 : Blo 519798 8061419 := bstep (se 1 (by rfl) ⟨6046064, by rfl⟩ : syracuseStep 8061419 = 12092129) B12092129
theorem B2820689 : Blo 519798 2820689 := bstep (se 2 (by rfl) ⟨1057758, by rfl⟩ : syracuseStep 2820689 = 2115517) B2115517
theorem B987689 : Blo 519798 987689 := bstep (se 2 (by rfl) ⟨370383, by rfl⟩ : syracuseStep 987689 = 740767) B740767
theorem B5936975 : Blo 519798 5936975 := bstep (se 1 (by rfl) ⟨4452731, by rfl⟩ : syracuseStep 5936975 = 8905463) B8905463
theorem B5347757 : Blo 519798 5347757 := bstep (se 3 (by rfl) ⟨1002704, by rfl⟩ : syracuseStep 5347757 = 2005409) B2005409
theorem B5955929 : Blo 519798 5955929 := bstep (se 2 (by rfl) ⟨2233473, by rfl⟩ : syracuseStep 5955929 = 4466947) B4466947
theorem B5374279 : Blo 519798 5374279 := bstep (se 1 (by rfl) ⟨4030709, by rfl⟩ : syracuseStep 5374279 = 8061419) B8061419
theorem B658459 : Blo 519798 658459 := bstep (se 1 (by rfl) ⟨493844, by rfl⟩ : syracuseStep 658459 = 987689) B987689
theorem B3970619 : Blo 519798 3970619 := bstep (se 1 (by rfl) ⟨2977964, by rfl⟩ : syracuseStep 3970619 = 5955929) B5955929
theorem B1880459 : Blo 519798 1880459 := bstep (se 1 (by rfl) ⟨1410344, by rfl⟩ : syracuseStep 1880459 = 2820689) B2820689
theorem B3957983 : Blo 519798 3957983 := bstep (se 1 (by rfl) ⟨2968487, by rfl⟩ : syracuseStep 3957983 = 5936975) B5936975
theorem B3565171 : Blo 519798 3565171 := bstep (se 1 (by rfl) ⟨2673878, by rfl⟩ : syracuseStep 3565171 = 5347757) B5347757
theorem B4753561 : Blo 519798 4753561 := bstep (se 2 (by rfl) ⟨1782585, by rfl⟩ : syracuseStep 4753561 = 3565171) B3565171
theorem B1253639 : Blo 519798 1253639 := bstep (se 1 (by rfl) ⟨940229, by rfl⟩ : syracuseStep 1253639 = 1880459) B1880459
theorem B2638655 : Blo 519798 2638655 := bstep (se 1 (by rfl) ⟨1978991, by rfl⟩ : syracuseStep 2638655 = 3957983) B3957983
theorem B7165705 : Blo 519798 7165705 := bstep (se 2 (by rfl) ⟨2687139, by rfl⟩ : syracuseStep 7165705 = 5374279) B5374279
theorem B2647079 : Blo 519798 2647079 := bstep (se 1 (by rfl) ⟨1985309, by rfl⟩ : syracuseStep 2647079 = 3970619) B3970619
theorem B877945 : Blo 519798 877945 := bstep (se 2 (by rfl) ⟨329229, by rfl⟩ : syracuseStep 877945 = 658459) B658459
theorem B6338081 : Blo 519798 6338081 := bstep (se 2 (by rfl) ⟨2376780, by rfl⟩ : syracuseStep 6338081 = 4753561) B4753561
theorem B835759 : Blo 519798 835759 := bstep (se 1 (by rfl) ⟨626819, by rfl⟩ : syracuseStep 835759 = 1253639) B1253639
theorem B9554273 : Blo 519798 9554273 := bstep (se 2 (by rfl) ⟨3582852, by rfl⟩ : syracuseStep 9554273 = 7165705) B7165705
theorem B1759103 : Blo 519798 1759103 := bstep (se 1 (by rfl) ⟨1319327, by rfl⟩ : syracuseStep 1759103 = 2638655) B2638655
theorem B1170593 : Blo 519798 1170593 := bstep (se 2 (by rfl) ⟨438972, by rfl⟩ : syracuseStep 1170593 = 877945) B877945
theorem B1764719 : Blo 519798 1764719 := bstep (se 1 (by rfl) ⟨1323539, by rfl⟩ : syracuseStep 1764719 = 2647079) B2647079
theorem B1114345 : Blo 519798 1114345 := bstep (se 2 (by rfl) ⟨417879, by rfl⟩ : syracuseStep 1114345 = 835759) B835759
theorem B6369515 : Blo 519798 6369515 := bstep (se 1 (by rfl) ⟨4777136, by rfl⟩ : syracuseStep 6369515 = 9554273) B9554273
theorem B1172735 : Blo 519798 1172735 := bstep (se 1 (by rfl) ⟨879551, by rfl⟩ : syracuseStep 1172735 = 1759103) B1759103
theorem B780395 : Blo 519798 780395 := bstep (se 1 (by rfl) ⟨585296, by rfl⟩ : syracuseStep 780395 = 1170593) B1170593
theorem B1176479 : Blo 519798 1176479 := bstep (se 1 (by rfl) ⟨882359, by rfl⟩ : syracuseStep 1176479 = 1764719) B1764719
theorem B4225387 : Blo 519798 4225387 := bstep (se 1 (by rfl) ⟨3169040, by rfl⟩ : syracuseStep 4225387 = 6338081) B6338081
theorem B1485793 : Blo 519798 1485793 := bstep (se 2 (by rfl) ⟨557172, by rfl⟩ : syracuseStep 1485793 = 1114345) B1114345
theorem B4246343 : Blo 519798 4246343 := bstep (se 1 (by rfl) ⟨3184757, by rfl⟩ : syracuseStep 4246343 = 6369515) B6369515
theorem B781823 : Blo 519798 781823 := bstep (se 1 (by rfl) ⟨586367, by rfl⟩ : syracuseStep 781823 = 1172735) B1172735
theorem B520263 : Blo 519798 520263 := bstep (se 1 (by rfl) ⟨390197, by rfl⟩ : syracuseStep 520263 = 780395) B780395
theorem B5633849 : Blo 519798 5633849 := bstep (se 2 (by rfl) ⟨2112693, by rfl⟩ : syracuseStep 5633849 = 4225387) B4225387
theorem B784319 : Blo 519798 784319 := bstep (se 1 (by rfl) ⟨588239, by rfl⟩ : syracuseStep 784319 = 1176479) B1176479
theorem B2830895 : Blo 519798 2830895 := bstep (se 1 (by rfl) ⟨2123171, by rfl⟩ : syracuseStep 2830895 = 4246343) B4246343
theorem B1981057 : Blo 519798 1981057 := bstep (se 2 (by rfl) ⟨742896, by rfl⟩ : syracuseStep 1981057 = 1485793) B1485793
theorem B3755899 : Blo 519798 3755899 := bstep (se 1 (by rfl) ⟨2816924, by rfl⟩ : syracuseStep 3755899 = 5633849) B5633849
theorem B521215 : Blo 519798 521215 := bstep (se 1 (by rfl) ⟨390911, by rfl⟩ : syracuseStep 521215 = 781823) B781823
theorem B522879 : Blo 519798 522879 := bstep (se 1 (by rfl) ⟨392159, by rfl⟩ : syracuseStep 522879 = 784319) B784319
theorem B1887263 : Blo 519798 1887263 := bstep (se 1 (by rfl) ⟨1415447, by rfl⟩ : syracuseStep 1887263 = 2830895) B2830895
theorem B2641409 : Blo 519798 2641409 := bstep (se 2 (by rfl) ⟨990528, by rfl⟩ : syracuseStep 2641409 = 1981057) B1981057
theorem B5007865 : Blo 519798 5007865 := bstep (se 2 (by rfl) ⟨1877949, by rfl⟩ : syracuseStep 5007865 = 3755899) B3755899
theorem B1258175 : Blo 519798 1258175 := bstep (se 1 (by rfl) ⟨943631, by rfl⟩ : syracuseStep 1258175 = 1887263) B1887263
theorem B1760939 : Blo 519798 1760939 := bstep (se 1 (by rfl) ⟨1320704, by rfl⟩ : syracuseStep 1760939 = 2641409) B2641409
theorem B6677153 : Blo 519798 6677153 := bstep (se 2 (by rfl) ⟨2503932, by rfl⟩ : syracuseStep 6677153 = 5007865) B5007865
theorem B838783 : Blo 519798 838783 := bstep (se 1 (by rfl) ⟨629087, by rfl⟩ : syracuseStep 838783 = 1258175) B1258175
theorem B1173959 : Blo 519798 1173959 := bstep (se 1 (by rfl) ⟨880469, by rfl⟩ : syracuseStep 1173959 = 1760939) B1760939
theorem B4451435 : Blo 519798 4451435 := bstep (se 1 (by rfl) ⟨3338576, by rfl⟩ : syracuseStep 4451435 = 6677153) B6677153
theorem B1118377 : Blo 519798 1118377 := bstep (se 2 (by rfl) ⟨419391, by rfl⟩ : syracuseStep 1118377 = 838783) B838783
theorem B2967623 : Blo 519798 2967623 := bstep (se 1 (by rfl) ⟨2225717, by rfl⟩ : syracuseStep 2967623 = 4451435) B4451435
theorem B782639 : Blo 519798 782639 := bstep (se 1 (by rfl) ⟨586979, by rfl⟩ : syracuseStep 782639 = 1173959) B1173959
theorem B5964677 : Blo 519798 5964677 := bstep (se 4 (by rfl) ⟨559188, by rfl⟩ : syracuseStep 5964677 = 1118377) B1118377
theorem B1978415 : Blo 519798 1978415 := bstep (se 1 (by rfl) ⟨1483811, by rfl⟩ : syracuseStep 1978415 = 2967623) B2967623
theorem B521759 : Blo 519798 521759 := bstep (se 1 (by rfl) ⟨391319, by rfl⟩ : syracuseStep 521759 = 782639) B782639
theorem B1318943 : Blo 519798 1318943 := bstep (se 1 (by rfl) ⟨989207, by rfl⟩ : syracuseStep 1318943 = 1978415) B1978415
theorem B3976451 : Blo 519798 3976451 := bstep (se 1 (by rfl) ⟨2982338, by rfl⟩ : syracuseStep 3976451 = 5964677) B5964677
theorem B879295 : Blo 519798 879295 := bstep (se 1 (by rfl) ⟨659471, by rfl⟩ : syracuseStep 879295 = 1318943) B1318943
theorem B2650967 : Blo 519798 2650967 := bstep (se 1 (by rfl) ⟨1988225, by rfl⟩ : syracuseStep 2650967 = 3976451) B3976451
theorem B1172393 : Blo 519798 1172393 := bstep (se 2 (by rfl) ⟨439647, by rfl⟩ : syracuseStep 1172393 = 879295) B879295
theorem B1767311 : Blo 519798 1767311 := bstep (se 1 (by rfl) ⟨1325483, by rfl⟩ : syracuseStep 1767311 = 2650967) B2650967
theorem B781595 : Blo 519798 781595 := bstep (se 1 (by rfl) ⟨586196, by rfl⟩ : syracuseStep 781595 = 1172393) B1172393
theorem B1178207 : Blo 519798 1178207 := bstep (se 1 (by rfl) ⟨883655, by rfl⟩ : syracuseStep 1178207 = 1767311) B1767311
theorem B521063 : Blo 519798 521063 := bstep (se 1 (by rfl) ⟨390797, by rfl⟩ : syracuseStep 521063 = 781595) B781595
theorem B785471 : Blo 519798 785471 := bstep (se 1 (by rfl) ⟨589103, by rfl⟩ : syracuseStep 785471 = 1178207) B1178207
theorem B523647 : Blo 519798 523647 := bstep (se 1 (by rfl) ⟨392735, by rfl⟩ : syracuseStep 523647 = 785471) B785471

theorem C0 (j : ℕ) (h1 : 129949 ≤ j) (h2 : j ≤ 130648) : Blo 519798 (4 * j + 3) := by
  interval_cases j
  · exact B519799
  · exact B519803
  · exact B519807
  · exact B519811
  · exact B519815
  · exact B519819
  · exact B519823
  · exact B519827
  · exact B519831
  · exact B519835
  · exact B519839
  · exact B519843
  · exact B519847
  · exact B519851
  · exact B519855
  · exact B519859
  · exact B519863
  · exact B519867
  · exact B519871
  · exact B519875
  · exact B519879
  · exact B519883
  · exact B519887
  · exact B519891
  · exact B519895
  · exact B519899
  · exact B519903
  · exact B519907
  · exact B519911
  · exact B519915
  · exact B519919
  · exact B519923
  · exact B519927
  · exact B519931
  · exact B519935
  · exact B519939
  · exact B519943
  · exact B519947
  · exact B519951
  · exact B519955
  · exact B519959
  · exact B519963
  · exact B519967
  · exact B519971
  · exact B519975
  · exact B519979
  · exact B519983
  · exact B519987
  · exact B519991
  · exact B519995
  · exact B519999
  · exact B520003
  · exact B520007
  · exact B520011
  · exact B520015
  · exact B520019
  · exact B520023
  · exact B520027
  · exact B520031
  · exact B520035
  · exact B520039
  · exact B520043
  · exact B520047
  · exact B520051
  · exact B520055
  · exact B520059
  · exact B520063
  · exact B520067
  · exact B520071
  · exact B520075
  · exact B520079
  · exact B520083
  · exact B520087
  · exact B520091
  · exact B520095
  · exact B520099
  · exact B520103
  · exact B520107
  · exact B520111
  · exact B520115
  · exact B520119
  · exact B520123
  · exact B520127
  · exact B520131
  · exact B520135
  · exact B520139
  · exact B520143
  · exact B520147
  · exact B520151
  · exact B520155
  · exact B520159
  · exact B520163
  · exact B520167
  · exact B520171
  · exact B520175
  · exact B520179
  · exact B520183
  · exact B520187
  · exact B520191
  · exact B520195
  · exact B520199
  · exact B520203
  · exact B520207
  · exact B520211
  · exact B520215
  · exact B520219
  · exact B520223
  · exact B520227
  · exact B520231
  · exact B520235
  · exact B520239
  · exact B520243
  · exact B520247
  · exact B520251
  · exact B520255
  · exact B520259
  · exact B520263
  · exact B520267
  · exact B520271
  · exact B520275
  · exact B520279
  · exact B520283
  · exact B520287
  · exact B520291
  · exact B520295
  · exact B520299
  · exact B520303
  · exact B520307
  · exact B520311
  · exact B520315
  · exact B520319
  · exact B520323
  · exact B520327
  · exact B520331
  · exact B520335
  · exact B520339
  · exact B520343
  · exact B520347
  · exact B520351
  · exact B520355
  · exact B520359
  · exact B520363
  · exact B520367
  · exact B520371
  · exact B520375
  · exact B520379
  · exact B520383
  · exact B520387
  · exact B520391
  · exact B520395
  · exact B520399
  · exact B520403
  · exact B520407
  · exact B520411
  · exact B520415
  · exact B520419
  · exact B520423
  · exact B520427
  · exact B520431
  · exact B520435
  · exact B520439
  · exact B520443
  · exact B520447
  · exact B520451
  · exact B520455
  · exact B520459
  · exact B520463
  · exact B520467
  · exact B520471
  · exact B520475
  · exact B520479
  · exact B520483
  · exact B520487
  · exact B520491
  · exact B520495
  · exact B520499
  · exact B520503
  · exact B520507
  · exact B520511
  · exact B520515
  · exact B520519
  · exact B520523
  · exact B520527
  · exact B520531
  · exact B520535
  · exact B520539
  · exact B520543
  · exact B520547
  · exact B520551
  · exact B520555
  · exact B520559
  · exact B520563
  · exact B520567
  · exact B520571
  · exact B520575
  · exact B520579
  · exact B520583
  · exact B520587
  · exact B520591
  · exact B520595
  · exact B520599
  · exact B520603
  · exact B520607
  · exact B520611
  · exact B520615
  · exact B520619
  · exact B520623
  · exact B520627
  · exact B520631
  · exact B520635
  · exact B520639
  · exact B520643
  · exact B520647
  · exact B520651
  · exact B520655
  · exact B520659
  · exact B520663
  · exact B520667
  · exact B520671
  · exact B520675
  · exact B520679
  · exact B520683
  · exact B520687
  · exact B520691
  · exact B520695
  · exact B520699
  · exact B520703
  · exact B520707
  · exact B520711
  · exact B520715
  · exact B520719
  · exact B520723
  · exact B520727
  · exact B520731
  · exact B520735
  · exact B520739
  · exact B520743
  · exact B520747
  · exact B520751
  · exact B520755
  · exact B520759
  · exact B520763
  · exact B520767
  · exact B520771
  · exact B520775
  · exact B520779
  · exact B520783
  · exact B520787
  · exact B520791
  · exact B520795
  · exact B520799
  · exact B520803
  · exact B520807
  · exact B520811
  · exact B520815
  · exact B520819
  · exact B520823
  · exact B520827
  · exact B520831
  · exact B520835
  · exact B520839
  · exact B520843
  · exact B520847
  · exact B520851
  · exact B520855
  · exact B520859
  · exact B520863
  · exact B520867
  · exact B520871
  · exact B520875
  · exact B520879
  · exact B520883
  · exact B520887
  · exact B520891
  · exact B520895
  · exact B520899
  · exact B520903
  · exact B520907
  · exact B520911
  · exact B520915
  · exact B520919
  · exact B520923
  · exact B520927
  · exact B520931
  · exact B520935
  · exact B520939
  · exact B520943
  · exact B520947
  · exact B520951
  · exact B520955
  · exact B520959
  · exact B520963
  · exact B520967
  · exact B520971
  · exact B520975
  · exact B520979
  · exact B520983
  · exact B520987
  · exact B520991
  · exact B520995
  · exact B520999
  · exact B521003
  · exact B521007
  · exact B521011
  · exact B521015
  · exact B521019
  · exact B521023
  · exact B521027
  · exact B521031
  · exact B521035
  · exact B521039
  · exact B521043
  · exact B521047
  · exact B521051
  · exact B521055
  · exact B521059
  · exact B521063
  · exact B521067
  · exact B521071
  · exact B521075
  · exact B521079
  · exact B521083
  · exact B521087
  · exact B521091
  · exact B521095
  · exact B521099
  · exact B521103
  · exact B521107
  · exact B521111
  · exact B521115
  · exact B521119
  · exact B521123
  · exact B521127
  · exact B521131
  · exact B521135
  · exact B521139
  · exact B521143
  · exact B521147
  · exact B521151
  · exact B521155
  · exact B521159
  · exact B521163
  · exact B521167
  · exact B521171
  · exact B521175
  · exact B521179
  · exact B521183
  · exact B521187
  · exact B521191
  · exact B521195
  · exact B521199
  · exact B521203
  · exact B521207
  · exact B521211
  · exact B521215
  · exact B521219
  · exact B521223
  · exact B521227
  · exact B521231
  · exact B521235
  · exact B521239
  · exact B521243
  · exact B521247
  · exact B521251
  · exact B521255
  · exact B521259
  · exact B521263
  · exact B521267
  · exact B521271
  · exact B521275
  · exact B521279
  · exact B521283
  · exact B521287
  · exact B521291
  · exact B521295
  · exact B521299
  · exact B521303
  · exact B521307
  · exact B521311
  · exact B521315
  · exact B521319
  · exact B521323
  · exact B521327
  · exact B521331
  · exact B521335
  · exact B521339
  · exact B521343
  · exact B521347
  · exact B521351
  · exact B521355
  · exact B521359
  · exact B521363
  · exact B521367
  · exact B521371
  · exact B521375
  · exact B521379
  · exact B521383
  · exact B521387
  · exact B521391
  · exact B521395
  · exact B521399
  · exact B521403
  · exact B521407
  · exact B521411
  · exact B521415
  · exact B521419
  · exact B521423
  · exact B521427
  · exact B521431
  · exact B521435
  · exact B521439
  · exact B521443
  · exact B521447
  · exact B521451
  · exact B521455
  · exact B521459
  · exact B521463
  · exact B521467
  · exact B521471
  · exact B521475
  · exact B521479
  · exact B521483
  · exact B521487
  · exact B521491
  · exact B521495
  · exact B521499
  · exact B521503
  · exact B521507
  · exact B521511
  · exact B521515
  · exact B521519
  · exact B521523
  · exact B521527
  · exact B521531
  · exact B521535
  · exact B521539
  · exact B521543
  · exact B521547
  · exact B521551
  · exact B521555
  · exact B521559
  · exact B521563
  · exact B521567
  · exact B521571
  · exact B521575
  · exact B521579
  · exact B521583
  · exact B521587
  · exact B521591
  · exact B521595
  · exact B521599
  · exact B521603
  · exact B521607
  · exact B521611
  · exact B521615
  · exact B521619
  · exact B521623
  · exact B521627
  · exact B521631
  · exact B521635
  · exact B521639
  · exact B521643
  · exact B521647
  · exact B521651
  · exact B521655
  · exact B521659
  · exact B521663
  · exact B521667
  · exact B521671
  · exact B521675
  · exact B521679
  · exact B521683
  · exact B521687
  · exact B521691
  · exact B521695
  · exact B521699
  · exact B521703
  · exact B521707
  · exact B521711
  · exact B521715
  · exact B521719
  · exact B521723
  · exact B521727
  · exact B521731
  · exact B521735
  · exact B521739
  · exact B521743
  · exact B521747
  · exact B521751
  · exact B521755
  · exact B521759
  · exact B521763
  · exact B521767
  · exact B521771
  · exact B521775
  · exact B521779
  · exact B521783
  · exact B521787
  · exact B521791
  · exact B521795
  · exact B521799
  · exact B521803
  · exact B521807
  · exact B521811
  · exact B521815
  · exact B521819
  · exact B521823
  · exact B521827
  · exact B521831
  · exact B521835
  · exact B521839
  · exact B521843
  · exact B521847
  · exact B521851
  · exact B521855
  · exact B521859
  · exact B521863
  · exact B521867
  · exact B521871
  · exact B521875
  · exact B521879
  · exact B521883
  · exact B521887
  · exact B521891
  · exact B521895
  · exact B521899
  · exact B521903
  · exact B521907
  · exact B521911
  · exact B521915
  · exact B521919
  · exact B521923
  · exact B521927
  · exact B521931
  · exact B521935
  · exact B521939
  · exact B521943
  · exact B521947
  · exact B521951
  · exact B521955
  · exact B521959
  · exact B521963
  · exact B521967
  · exact B521971
  · exact B521975
  · exact B521979
  · exact B521983
  · exact B521987
  · exact B521991
  · exact B521995
  · exact B521999
  · exact B522003
  · exact B522007
  · exact B522011
  · exact B522015
  · exact B522019
  · exact B522023
  · exact B522027
  · exact B522031
  · exact B522035
  · exact B522039
  · exact B522043
  · exact B522047
  · exact B522051
  · exact B522055
  · exact B522059
  · exact B522063
  · exact B522067
  · exact B522071
  · exact B522075
  · exact B522079
  · exact B522083
  · exact B522087
  · exact B522091
  · exact B522095
  · exact B522099
  · exact B522103
  · exact B522107
  · exact B522111
  · exact B522115
  · exact B522119
  · exact B522123
  · exact B522127
  · exact B522131
  · exact B522135
  · exact B522139
  · exact B522143
  · exact B522147
  · exact B522151
  · exact B522155
  · exact B522159
  · exact B522163
  · exact B522167
  · exact B522171
  · exact B522175
  · exact B522179
  · exact B522183
  · exact B522187
  · exact B522191
  · exact B522195
  · exact B522199
  · exact B522203
  · exact B522207
  · exact B522211
  · exact B522215
  · exact B522219
  · exact B522223
  · exact B522227
  · exact B522231
  · exact B522235
  · exact B522239
  · exact B522243
  · exact B522247
  · exact B522251
  · exact B522255
  · exact B522259
  · exact B522263
  · exact B522267
  · exact B522271
  · exact B522275
  · exact B522279
  · exact B522283
  · exact B522287
  · exact B522291
  · exact B522295
  · exact B522299
  · exact B522303
  · exact B522307
  · exact B522311
  · exact B522315
  · exact B522319
  · exact B522323
  · exact B522327
  · exact B522331
  · exact B522335
  · exact B522339
  · exact B522343
  · exact B522347
  · exact B522351
  · exact B522355
  · exact B522359
  · exact B522363
  · exact B522367
  · exact B522371
  · exact B522375
  · exact B522379
  · exact B522383
  · exact B522387
  · exact B522391
  · exact B522395
  · exact B522399
  · exact B522403
  · exact B522407
  · exact B522411
  · exact B522415
  · exact B522419
  · exact B522423
  · exact B522427
  · exact B522431
  · exact B522435
  · exact B522439
  · exact B522443
  · exact B522447
  · exact B522451
  · exact B522455
  · exact B522459
  · exact B522463
  · exact B522467
  · exact B522471
  · exact B522475
  · exact B522479
  · exact B522483
  · exact B522487
  · exact B522491
  · exact B522495
  · exact B522499
  · exact B522503
  · exact B522507
  · exact B522511
  · exact B522515
  · exact B522519
  · exact B522523
  · exact B522527
  · exact B522531
  · exact B522535
  · exact B522539
  · exact B522543
  · exact B522547
  · exact B522551
  · exact B522555
  · exact B522559
  · exact B522563
  · exact B522567
  · exact B522571
  · exact B522575
  · exact B522579
  · exact B522583
  · exact B522587
  · exact B522591
  · exact B522595

theorem C1 (j : ℕ) (h1 : 130649 ≤ j) (h2 : j ≤ 130948) : Blo 519798 (4 * j + 3) := by
  interval_cases j
  · exact B522599
  · exact B522603
  · exact B522607
  · exact B522611
  · exact B522615
  · exact B522619
  · exact B522623
  · exact B522627
  · exact B522631
  · exact B522635
  · exact B522639
  · exact B522643
  · exact B522647
  · exact B522651
  · exact B522655
  · exact B522659
  · exact B522663
  · exact B522667
  · exact B522671
  · exact B522675
  · exact B522679
  · exact B522683
  · exact B522687
  · exact B522691
  · exact B522695
  · exact B522699
  · exact B522703
  · exact B522707
  · exact B522711
  · exact B522715
  · exact B522719
  · exact B522723
  · exact B522727
  · exact B522731
  · exact B522735
  · exact B522739
  · exact B522743
  · exact B522747
  · exact B522751
  · exact B522755
  · exact B522759
  · exact B522763
  · exact B522767
  · exact B522771
  · exact B522775
  · exact B522779
  · exact B522783
  · exact B522787
  · exact B522791
  · exact B522795
  · exact B522799
  · exact B522803
  · exact B522807
  · exact B522811
  · exact B522815
  · exact B522819
  · exact B522823
  · exact B522827
  · exact B522831
  · exact B522835
  · exact B522839
  · exact B522843
  · exact B522847
  · exact B522851
  · exact B522855
  · exact B522859
  · exact B522863
  · exact B522867
  · exact B522871
  · exact B522875
  · exact B522879
  · exact B522883
  · exact B522887
  · exact B522891
  · exact B522895
  · exact B522899
  · exact B522903
  · exact B522907
  · exact B522911
  · exact B522915
  · exact B522919
  · exact B522923
  · exact B522927
  · exact B522931
  · exact B522935
  · exact B522939
  · exact B522943
  · exact B522947
  · exact B522951
  · exact B522955
  · exact B522959
  · exact B522963
  · exact B522967
  · exact B522971
  · exact B522975
  · exact B522979
  · exact B522983
  · exact B522987
  · exact B522991
  · exact B522995
  · exact B522999
  · exact B523003
  · exact B523007
  · exact B523011
  · exact B523015
  · exact B523019
  · exact B523023
  · exact B523027
  · exact B523031
  · exact B523035
  · exact B523039
  · exact B523043
  · exact B523047
  · exact B523051
  · exact B523055
  · exact B523059
  · exact B523063
  · exact B523067
  · exact B523071
  · exact B523075
  · exact B523079
  · exact B523083
  · exact B523087
  · exact B523091
  · exact B523095
  · exact B523099
  · exact B523103
  · exact B523107
  · exact B523111
  · exact B523115
  · exact B523119
  · exact B523123
  · exact B523127
  · exact B523131
  · exact B523135
  · exact B523139
  · exact B523143
  · exact B523147
  · exact B523151
  · exact B523155
  · exact B523159
  · exact B523163
  · exact B523167
  · exact B523171
  · exact B523175
  · exact B523179
  · exact B523183
  · exact B523187
  · exact B523191
  · exact B523195
  · exact B523199
  · exact B523203
  · exact B523207
  · exact B523211
  · exact B523215
  · exact B523219
  · exact B523223
  · exact B523227
  · exact B523231
  · exact B523235
  · exact B523239
  · exact B523243
  · exact B523247
  · exact B523251
  · exact B523255
  · exact B523259
  · exact B523263
  · exact B523267
  · exact B523271
  · exact B523275
  · exact B523279
  · exact B523283
  · exact B523287
  · exact B523291
  · exact B523295
  · exact B523299
  · exact B523303
  · exact B523307
  · exact B523311
  · exact B523315
  · exact B523319
  · exact B523323
  · exact B523327
  · exact B523331
  · exact B523335
  · exact B523339
  · exact B523343
  · exact B523347
  · exact B523351
  · exact B523355
  · exact B523359
  · exact B523363
  · exact B523367
  · exact B523371
  · exact B523375
  · exact B523379
  · exact B523383
  · exact B523387
  · exact B523391
  · exact B523395
  · exact B523399
  · exact B523403
  · exact B523407
  · exact B523411
  · exact B523415
  · exact B523419
  · exact B523423
  · exact B523427
  · exact B523431
  · exact B523435
  · exact B523439
  · exact B523443
  · exact B523447
  · exact B523451
  · exact B523455
  · exact B523459
  · exact B523463
  · exact B523467
  · exact B523471
  · exact B523475
  · exact B523479
  · exact B523483
  · exact B523487
  · exact B523491
  · exact B523495
  · exact B523499
  · exact B523503
  · exact B523507
  · exact B523511
  · exact B523515
  · exact B523519
  · exact B523523
  · exact B523527
  · exact B523531
  · exact B523535
  · exact B523539
  · exact B523543
  · exact B523547
  · exact B523551
  · exact B523555
  · exact B523559
  · exact B523563
  · exact B523567
  · exact B523571
  · exact B523575
  · exact B523579
  · exact B523583
  · exact B523587
  · exact B523591
  · exact B523595
  · exact B523599
  · exact B523603
  · exact B523607
  · exact B523611
  · exact B523615
  · exact B523619
  · exact B523623
  · exact B523627
  · exact B523631
  · exact B523635
  · exact B523639
  · exact B523643
  · exact B523647
  · exact B523651
  · exact B523655
  · exact B523659
  · exact B523663
  · exact B523667
  · exact B523671
  · exact B523675
  · exact B523679
  · exact B523683
  · exact B523687
  · exact B523691
  · exact B523695
  · exact B523699
  · exact B523703
  · exact B523707
  · exact B523711
  · exact B523715
  · exact B523719
  · exact B523723
  · exact B523727
  · exact B523731
  · exact B523735
  · exact B523739
  · exact B523743
  · exact B523747
  · exact B523751
  · exact B523755
  · exact B523759
  · exact B523763
  · exact B523767
  · exact B523771
  · exact B523775
  · exact B523779
  · exact B523783
  · exact B523787
  · exact B523791
  · exact B523795

theorem solution (m : ℕ) (hlo : 519798 ≤ m) (hhi : m ≤ 523798) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 129949 ≤ j := by omega
    have hj2 : j ≤ 130948 := by omega
    have hb : Blo 519798 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 130649 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
