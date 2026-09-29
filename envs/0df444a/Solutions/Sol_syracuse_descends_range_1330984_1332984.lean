-- Prove2me | solution 1 for syracuse_descends_range_1330984_1332984
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:12:40.762382+00:00
-- url     : https://prove2.me/submissions/fea0a4f3-4571-4922-88ba-b6f2b202011d

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


theorem B2998277 : Blo 1330984 2998277 := bbase (se 4 (by rfl) ⟨281088, by rfl⟩ : syracuseStep 2998277 = 562177) (by norm_num)
theorem B1998869 : Blo 1330984 1998869 := bbase (se 6 (by rfl) ⟨46848, by rfl⟩ : syracuseStep 1998869 = 93697) (by norm_num)
theorem B1499161 : Blo 1330984 1499161 := bbase (se 2 (by rfl) ⟨562185, by rfl⟩ : syracuseStep 1499161 = 1124371) (by norm_num)
theorem B2400301 : Blo 1330984 2400301 := bbase (se 3 (by rfl) ⟨450056, by rfl⟩ : syracuseStep 2400301 = 900113) (by norm_num)
theorem B1998893 : Blo 1330984 1998893 := bbase (se 3 (by rfl) ⟨374792, by rfl⟩ : syracuseStep 1998893 = 749585) (by norm_num)
theorem B3039277 : Blo 1330984 3039277 := bbase (se 3 (by rfl) ⟨569864, by rfl⟩ : syracuseStep 3039277 = 1139729) (by norm_num)
theorem B1499197 : Blo 1330984 1499197 := bbase (se 3 (by rfl) ⟨281099, by rfl⟩ : syracuseStep 1499197 = 562199) (by norm_num)
theorem B1998917 : Blo 1330984 1998917 := bbase (se 4 (by rfl) ⟨187398, by rfl⟩ : syracuseStep 1998917 = 374797) (by norm_num)
theorem B2998349 : Blo 1330984 2998349 := bbase (se 3 (by rfl) ⟨562190, by rfl⟩ : syracuseStep 2998349 = 1124381) (by norm_num)
theorem B1998941 : Blo 1330984 1998941 := bbase (se 3 (by rfl) ⟨374801, by rfl⟩ : syracuseStep 1998941 = 749603) (by norm_num)
theorem B1499233 : Blo 1330984 1499233 := bbase (se 2 (by rfl) ⟨562212, by rfl⟩ : syracuseStep 1499233 = 1124425) (by norm_num)
theorem B7684213 : Blo 1330984 7684213 := bbase (se 5 (by rfl) ⟨360197, by rfl⟩ : syracuseStep 7684213 = 720395) (by norm_num)
theorem B1998965 : Blo 1330984 1998965 := bbase (se 5 (by rfl) ⟨93701, by rfl⟩ : syracuseStep 1998965 = 187403) (by norm_num)
theorem B1499269 : Blo 1330984 1499269 := bbase (se 4 (by rfl) ⟨140556, by rfl⟩ : syracuseStep 1499269 = 281113) (by norm_num)
theorem B1998989 : Blo 1330984 1998989 := bbase (se 3 (by rfl) ⟨374810, by rfl⟩ : syracuseStep 1998989 = 749621) (by norm_num)
theorem B2998421 : Blo 1330984 2998421 := bbase (se 6 (by rfl) ⟨70275, by rfl⟩ : syracuseStep 2998421 = 140551) (by norm_num)
theorem B1999013 : Blo 1330984 1999013 := bbase (se 4 (by rfl) ⟨187407, by rfl⟩ : syracuseStep 1999013 = 374815) (by norm_num)
theorem B1499305 : Blo 1330984 1499305 := bbase (se 2 (by rfl) ⟨562239, by rfl⟩ : syracuseStep 1499305 = 1124479) (by norm_num)
theorem B1999037 : Blo 1330984 1999037 := bbase (se 3 (by rfl) ⟨374819, by rfl⟩ : syracuseStep 1999037 = 749639) (by norm_num)
theorem B4497605 : Blo 1330984 4497605 := bbase (se 4 (by rfl) ⟨421650, by rfl⟩ : syracuseStep 4497605 = 843301) (by norm_num)
theorem B1499341 : Blo 1330984 1499341 := bbase (se 3 (by rfl) ⟨281126, by rfl⟩ : syracuseStep 1499341 = 562253) (by norm_num)
theorem B1999061 : Blo 1330984 1999061 := bbase (se 7 (by rfl) ⟨23426, by rfl⟩ : syracuseStep 1999061 = 46853) (by norm_num)
theorem B2998493 : Blo 1330984 2998493 := bbase (se 3 (by rfl) ⟨562217, by rfl⟩ : syracuseStep 2998493 = 1124435) (by norm_num)
theorem B3039461 : Blo 1330984 3039461 := bbase (se 4 (by rfl) ⟨284949, by rfl⟩ : syracuseStep 3039461 = 569899) (by norm_num)
theorem B1999085 : Blo 1330984 1999085 := bbase (se 3 (by rfl) ⟨374828, by rfl⟩ : syracuseStep 1999085 = 749657) (by norm_num)
theorem B1499377 : Blo 1330984 1499377 := bbase (se 2 (by rfl) ⟨562266, by rfl⟩ : syracuseStep 1499377 = 1124533) (by norm_num)
theorem B3465461 : Blo 1330984 3465461 := bbase (se 5 (by rfl) ⟨162443, by rfl⟩ : syracuseStep 3465461 = 324887) (by norm_num)
theorem B6742277 : Blo 1330984 6742277 := bbase (se 4 (by rfl) ⟨632088, by rfl⟩ : syracuseStep 6742277 = 1264177) (by norm_num)
theorem B1999109 : Blo 1330984 1999109 := bbase (se 4 (by rfl) ⟨187416, by rfl⟩ : syracuseStep 1999109 = 374833) (by norm_num)
theorem B1499413 : Blo 1330984 1499413 := bbase (se 6 (by rfl) ⟨35142, by rfl⟩ : syracuseStep 1499413 = 70285) (by norm_num)
theorem B1999133 : Blo 1330984 1999133 := bbase (se 3 (by rfl) ⟨374837, by rfl⟩ : syracuseStep 1999133 = 749675) (by norm_num)
theorem B2998565 : Blo 1330984 2998565 := bbase (se 4 (by rfl) ⟨281115, by rfl⟩ : syracuseStep 2998565 = 562231) (by norm_num)
theorem B1999157 : Blo 1330984 1999157 := bbase (se 5 (by rfl) ⟨93710, by rfl⟩ : syracuseStep 1999157 = 187421) (by norm_num)
theorem B1499449 : Blo 1330984 1499449 := bbase (se 2 (by rfl) ⟨562293, by rfl⟩ : syracuseStep 1499449 = 1124587) (by norm_num)
theorem B2433349 : Blo 1330984 2433349 := bbase (se 4 (by rfl) ⟨228126, by rfl⟩ : syracuseStep 2433349 = 456253) (by norm_num)
theorem B1999181 : Blo 1330984 1999181 := bbase (se 3 (by rfl) ⟨374846, by rfl⟩ : syracuseStep 1999181 = 749693) (by norm_num)
theorem B1499485 : Blo 1330984 1499485 := bbase (se 3 (by rfl) ⟨281153, by rfl⟩ : syracuseStep 1499485 = 562307) (by norm_num)
theorem B1999205 : Blo 1330984 1999205 := bbase (se 4 (by rfl) ⟨187425, by rfl⟩ : syracuseStep 1999205 = 374851) (by norm_num)
theorem B2998637 : Blo 1330984 2998637 := bbase (se 3 (by rfl) ⟨562244, by rfl⟩ : syracuseStep 2998637 = 1124489) (by norm_num)
theorem B1999229 : Blo 1330984 1999229 := bbase (se 3 (by rfl) ⟨374855, by rfl⟩ : syracuseStep 1999229 = 749711) (by norm_num)
theorem B1499521 : Blo 1330984 1499521 := bbase (se 2 (by rfl) ⟨562320, by rfl⟩ : syracuseStep 1499521 = 1124641) (by norm_num)
theorem B5685653 : Blo 1330984 5685653 := bbase (se 6 (by rfl) ⟨133257, by rfl⟩ : syracuseStep 5685653 = 266515) (by norm_num)
theorem B17064341 : Blo 1330984 17064341 := bbase (se 6 (by rfl) ⟨399945, by rfl⟩ : syracuseStep 17064341 = 799891) (by norm_num)
theorem B1999253 : Blo 1330984 1999253 := bbase (se 6 (by rfl) ⟨46857, by rfl⟩ : syracuseStep 1999253 = 93715) (by norm_num)
theorem B1499557 : Blo 1330984 1499557 := bbase (se 4 (by rfl) ⟨140583, by rfl⟩ : syracuseStep 1499557 = 281167) (by norm_num)
theorem B1999277 : Blo 1330984 1999277 := bbase (se 3 (by rfl) ⟨374864, by rfl⟩ : syracuseStep 1999277 = 749729) (by norm_num)
theorem B2998709 : Blo 1330984 2998709 := bbase (se 5 (by rfl) ⟨140564, by rfl⟩ : syracuseStep 2998709 = 281129) (by norm_num)
theorem B1999301 : Blo 1330984 1999301 := bbase (se 4 (by rfl) ⟨187434, by rfl⟩ : syracuseStep 1999301 = 374869) (by norm_num)
theorem B1499593 : Blo 1330984 1499593 := bbase (se 2 (by rfl) ⟨562347, by rfl⟩ : syracuseStep 1499593 = 1124695) (by norm_num)
theorem B2843093 : Blo 1330984 2843093 := bbase (se 7 (by rfl) ⟨33317, by rfl⟩ : syracuseStep 2843093 = 66635) (by norm_num)
theorem B1999325 : Blo 1330984 1999325 := bbase (se 3 (by rfl) ⟨374873, by rfl⟩ : syracuseStep 1999325 = 749747) (by norm_num)
theorem B1999349 : Blo 1330984 1999349 := bbase (se 5 (by rfl) ⟨93719, by rfl⟩ : syracuseStep 1999349 = 187439) (by norm_num)
theorem B2998781 : Blo 1330984 2998781 := bbase (se 3 (by rfl) ⟨562271, by rfl⟩ : syracuseStep 2998781 = 1124543) (by norm_num)
theorem B1999373 : Blo 1330984 1999373 := bbase (se 3 (by rfl) ⟨374882, by rfl⟩ : syracuseStep 1999373 = 749765) (by norm_num)
theorem B2433557 : Blo 1330984 2433557 := bbase (se 6 (by rfl) ⟨57036, by rfl⟩ : syracuseStep 2433557 = 114073) (by norm_num)
theorem B1999397 : Blo 1330984 1999397 := bbase (se 4 (by rfl) ⟨187443, by rfl⟩ : syracuseStep 1999397 = 374887) (by norm_num)
theorem B1999421 : Blo 1330984 1999421 := bbase (se 3 (by rfl) ⟨374891, by rfl⟩ : syracuseStep 1999421 = 749783) (by norm_num)
theorem B2998853 : Blo 1330984 2998853 := bbase (se 4 (by rfl) ⟨281142, by rfl⟩ : syracuseStep 2998853 = 562285) (by norm_num)
theorem B14410325 : Blo 1330984 14410325 := bbase (se 8 (by rfl) ⟨84435, by rfl⟩ : syracuseStep 14410325 = 168871) (by norm_num)
theorem B1999445 : Blo 1330984 1999445 := bbase (se 8 (by rfl) ⟨11715, by rfl⟩ : syracuseStep 1999445 = 23431) (by norm_num)
theorem B2843237 : Blo 1330984 2843237 := bbase (se 4 (by rfl) ⟨266553, by rfl⟩ : syracuseStep 2843237 = 533107) (by norm_num)
theorem B1999469 : Blo 1330984 1999469 := bbase (se 3 (by rfl) ⟨374900, by rfl⟩ : syracuseStep 1999469 = 749801) (by norm_num)
theorem B4498037 : Blo 1330984 4498037 := bbase (se 5 (by rfl) ⟨210845, by rfl⟩ : syracuseStep 4498037 = 421691) (by norm_num)
theorem B2998925 : Blo 1330984 2998925 := bbase (se 3 (by rfl) ⟨562298, by rfl⟩ : syracuseStep 2998925 = 1124597) (by norm_num)
theorem B2433701 : Blo 1330984 2433701 := bbase (se 4 (by rfl) ⟨228159, by rfl⟩ : syracuseStep 2433701 = 456319) (by norm_num)
theorem B11387573 : Blo 1330984 11387573 := bbase (se 5 (by rfl) ⟨533792, by rfl⟩ : syracuseStep 11387573 = 1067585) (by norm_num)
theorem B2998997 : Blo 1330984 2998997 := bbase (se 7 (by rfl) ⟨35144, by rfl⟩ : syracuseStep 2998997 = 70289) (by norm_num)
theorem B2999069 : Blo 1330984 2999069 := bbase (se 3 (by rfl) ⟨562325, by rfl⟩ : syracuseStep 2999069 = 1124651) (by norm_num)
theorem B1622857 : Blo 1330984 1622857 := bbase (se 2 (by rfl) ⟨608571, by rfl⟩ : syracuseStep 1622857 = 1217143) (by norm_num)
theorem B4809557 : Blo 1330984 4809557 := bbase (se 9 (by rfl) ⟨14090, by rfl⟩ : syracuseStep 4809557 = 28181) (by norm_num)
theorem B2999141 : Blo 1330984 2999141 := bbase (se 4 (by rfl) ⟨281169, by rfl⟩ : syracuseStep 2999141 = 562339) (by norm_num)
theorem B2999213 : Blo 1330984 2999213 := bbase (se 3 (by rfl) ⟨562352, by rfl⟩ : syracuseStep 2999213 = 1124705) (by norm_num)
theorem B5055493 : Blo 1330984 5055493 := bbase (se 4 (by rfl) ⟨473952, by rfl⟩ : syracuseStep 5055493 = 947905) (by norm_num)
theorem B3417125 : Blo 1330984 3417125 := bbase (se 4 (by rfl) ⟨320355, by rfl⟩ : syracuseStep 3417125 = 640711) (by norm_num)
theorem B4498469 : Blo 1330984 4498469 := bbase (se 4 (by rfl) ⟨421731, by rfl⟩ : syracuseStep 4498469 = 843463) (by norm_num)
theorem B2278541 : Blo 1330984 2278541 := bbase (se 3 (by rfl) ⟨427226, by rfl⟩ : syracuseStep 2278541 = 854453) (by norm_num)
theorem B5055797 : Blo 1330984 5055797 := bbase (se 5 (by rfl) ⟨236990, by rfl⟩ : syracuseStep 5055797 = 473981) (by norm_num)
theorem B2843981 : Blo 1330984 2843981 := bbase (se 3 (by rfl) ⟨533246, by rfl⟩ : syracuseStep 2843981 = 1066493) (by norm_num)
theorem B5686645 : Blo 1330984 5686645 := bbase (se 5 (by rfl) ⟨266561, by rfl⟩ : syracuseStep 5686645 = 533123) (by norm_num)
theorem B3794309 : Blo 1330984 3794309 := bbase (se 4 (by rfl) ⟨355716, by rfl⟩ : syracuseStep 3794309 = 711433) (by norm_num)
theorem B4105637 : Blo 1330984 4105637 := bbase (se 4 (by rfl) ⟨384903, by rfl⟩ : syracuseStep 4105637 = 769807) (by norm_num)
theorem B2246069 : Blo 1330984 2246069 := bbase (se 5 (by rfl) ⟨105284, by rfl⟩ : syracuseStep 2246069 = 210569) (by norm_num)
theorem B6743573 : Blo 1330984 6743573 := bbase (se 6 (by rfl) ⟨158052, by rfl⟩ : syracuseStep 6743573 = 316105) (by norm_num)
theorem B2885149 : Blo 1330984 2885149 := bbase (se 3 (by rfl) ⟨540965, by rfl⟩ : syracuseStep 2885149 = 1081931) (by norm_num)
theorem B2246197 : Blo 1330984 2246197 := bbase (se 5 (by rfl) ⟨105290, by rfl⟩ : syracuseStep 2246197 = 210581) (by norm_num)
theorem B2246285 : Blo 1330984 2246285 := bbase (se 3 (by rfl) ⟨421178, by rfl⟩ : syracuseStep 2246285 = 842357) (by norm_num)
theorem B19195541 : Blo 1330984 19195541 := bbase (se 6 (by rfl) ⟨449895, by rfl⟩ : syracuseStep 19195541 = 899791) (by norm_num)
theorem B6080197 : Blo 1330984 6080197 := bbase (se 4 (by rfl) ⟨570018, by rfl⟩ : syracuseStep 6080197 = 1140037) (by norm_num)
theorem B2246413 : Blo 1330984 2246413 := bbase (se 3 (by rfl) ⟨421202, by rfl⟩ : syracuseStep 2246413 = 842405) (by norm_num)
theorem B2246501 : Blo 1330984 2246501 := bbase (se 4 (by rfl) ⟨210609, by rfl⟩ : syracuseStep 2246501 = 421219) (by norm_num)
theorem B9594773 : Blo 1330984 9594773 := bbase (se 6 (by rfl) ⟨224877, by rfl⟩ : syracuseStep 9594773 = 449755) (by norm_num)
theorem B9734069 : Blo 1330984 9734069 := bbase (se 5 (by rfl) ⟨456284, by rfl⟩ : syracuseStep 9734069 = 912569) (by norm_num)
theorem B2246629 : Blo 1330984 2246629 := bbase (se 4 (by rfl) ⟨210621, by rfl⟩ : syracuseStep 2246629 = 421243) (by norm_num)
theorem B4556837 : Blo 1330984 4556837 := bbase (se 4 (by rfl) ⟨427203, by rfl⟩ : syracuseStep 4556837 = 854407) (by norm_num)
theorem B2246717 : Blo 1330984 2246717 := bbase (se 3 (by rfl) ⟨421259, by rfl⟩ : syracuseStep 2246717 = 842519) (by norm_num)
theorem B2844733 : Blo 1330984 2844733 := bbase (se 3 (by rfl) ⟨533387, by rfl⟩ : syracuseStep 2844733 = 1066775) (by norm_num)
theorem B2246845 : Blo 1330984 2246845 := bbase (se 3 (by rfl) ⟨421283, by rfl⟩ : syracuseStep 2246845 = 842567) (by norm_num)
theorem B2844877 : Blo 1330984 2844877 := bbase (se 3 (by rfl) ⟨533414, by rfl⟩ : syracuseStep 2844877 = 1066829) (by norm_num)
theorem B2246933 : Blo 1330984 2246933 := bbase (se 6 (by rfl) ⟨52662, by rfl⟩ : syracuseStep 2246933 = 105325) (by norm_num)
theorem B2247061 : Blo 1330984 2247061 := bbase (se 6 (by rfl) ⟨52665, by rfl⟩ : syracuseStep 2247061 = 105331) (by norm_num)
theorem B1599917 : Blo 1330984 1599917 := bbase (se 3 (by rfl) ⟨299984, by rfl⟩ : syracuseStep 1599917 = 599969) (by norm_num)
theorem B3369397 : Blo 1330984 3369397 := bbase (se 5 (by rfl) ⟨157940, by rfl⟩ : syracuseStep 3369397 = 315881) (by norm_num)
theorem B2247149 : Blo 1330984 2247149 := bbase (se 3 (by rfl) ⟨421340, by rfl⟩ : syracuseStep 2247149 = 842681) (by norm_num)
theorem B3369509 : Blo 1330984 3369509 := bbase (se 4 (by rfl) ⟨315891, by rfl⟩ : syracuseStep 3369509 = 631783) (by norm_num)
theorem B3795493 : Blo 1330984 3795493 := bbase (se 4 (by rfl) ⟨355827, by rfl⟩ : syracuseStep 3795493 = 711655) (by norm_num)
theorem B2845253 : Blo 1330984 2845253 := bbase (se 4 (by rfl) ⟨266742, by rfl⟩ : syracuseStep 2845253 = 533485) (by norm_num)
theorem B2247277 : Blo 1330984 2247277 := bbase (se 3 (by rfl) ⟨421364, by rfl⟩ : syracuseStep 2247277 = 842729) (by norm_num)
theorem B2247365 : Blo 1330984 2247365 := bbase (se 4 (by rfl) ⟨210690, by rfl⟩ : syracuseStep 2247365 = 421381) (by norm_num)
theorem B3795653 : Blo 1330984 3795653 := bbase (se 4 (by rfl) ⟨355842, by rfl⟩ : syracuseStep 3795653 = 711685) (by norm_num)
theorem B3369701 : Blo 1330984 3369701 := bbase (se 4 (by rfl) ⟨315909, by rfl⟩ : syracuseStep 3369701 = 631819) (by norm_num)
theorem B6744869 : Blo 1330984 6744869 := bbase (se 4 (by rfl) ⟨632331, by rfl⟩ : syracuseStep 6744869 = 1264663) (by norm_num)
theorem B2247493 : Blo 1330984 2247493 := bbase (se 4 (by rfl) ⟨210702, by rfl⟩ : syracuseStep 2247493 = 421405) (by norm_num)
theorem B2132813 : Blo 1330984 2132813 := bbase (se 3 (by rfl) ⟨399902, by rfl⟩ : syracuseStep 2132813 = 799805) (by norm_num)
theorem B2247581 : Blo 1330984 2247581 := bbase (se 3 (by rfl) ⟨421421, by rfl⟩ : syracuseStep 2247581 = 842843) (by norm_num)
theorem B11373493 : Blo 1330984 11373493 := bbase (se 5 (by rfl) ⟨533132, by rfl⟩ : syracuseStep 11373493 = 1066265) (by norm_num)
theorem B2845621 : Blo 1330984 2845621 := bbase (se 5 (by rfl) ⟨133388, by rfl⟩ : syracuseStep 2845621 = 266777) (by norm_num)
theorem B2247709 : Blo 1330984 2247709 := bbase (se 3 (by rfl) ⟨421445, by rfl⟩ : syracuseStep 2247709 = 842891) (by norm_num)
theorem B3370045 : Blo 1330984 3370045 := bbase (se 3 (by rfl) ⟨631883, by rfl⟩ : syracuseStep 3370045 = 1263767) (by norm_num)
theorem B1600609 : Blo 1330984 1600609 := bbase (se 2 (by rfl) ⟨600228, by rfl⟩ : syracuseStep 1600609 = 1200457) (by norm_num)
theorem B2247797 : Blo 1330984 2247797 := bbase (se 5 (by rfl) ⟨105365, by rfl⟩ : syracuseStep 2247797 = 210731) (by norm_num)
theorem B4492421 : Blo 1330984 4492421 := bbase (se 4 (by rfl) ⟨421164, by rfl⟩ : syracuseStep 4492421 = 842329) (by norm_num)
theorem B3370157 : Blo 1330984 3370157 := bbase (se 3 (by rfl) ⟨631904, by rfl⟩ : syracuseStep 3370157 = 1263809) (by norm_num)
theorem B1600705 : Blo 1330984 1600705 := bbase (se 2 (by rfl) ⟨600264, by rfl⟩ : syracuseStep 1600705 = 1200529) (by norm_num)
theorem B2133197 : Blo 1330984 2133197 := bbase (se 3 (by rfl) ⟨399974, by rfl⟩ : syracuseStep 2133197 = 799949) (by norm_num)
theorem B1518809 : Blo 1330984 1518809 := bbase (se 2 (by rfl) ⟨569553, by rfl⟩ : syracuseStep 1518809 = 1139107) (by norm_num)
theorem B2247925 : Blo 1330984 2247925 := bbase (se 5 (by rfl) ⟨105371, by rfl⟩ : syracuseStep 2247925 = 210743) (by norm_num)
theorem B2133325 : Blo 1330984 2133325 := bbase (se 3 (by rfl) ⟨399998, by rfl⟩ : syracuseStep 2133325 = 799997) (by norm_num)
theorem B2248013 : Blo 1330984 2248013 := bbase (se 3 (by rfl) ⟨421502, by rfl⟩ : syracuseStep 2248013 = 843005) (by norm_num)
theorem B3370349 : Blo 1330984 3370349 := bbase (se 3 (by rfl) ⟨631940, by rfl⟩ : syracuseStep 3370349 = 1263881) (by norm_num)
theorem B5057909 : Blo 1330984 5057909 := bbase (se 5 (by rfl) ⟨237089, by rfl⟩ : syracuseStep 5057909 = 474179) (by norm_num)
theorem B2248141 : Blo 1330984 2248141 := bbase (se 3 (by rfl) ⟨421526, by rfl⟩ : syracuseStep 2248141 = 843053) (by norm_num)
theorem B2248229 : Blo 1330984 2248229 := bbase (se 4 (by rfl) ⟨210771, by rfl⟩ : syracuseStep 2248229 = 421543) (by norm_num)
theorem B4492853 : Blo 1330984 4492853 := bbase (se 5 (by rfl) ⟨210602, by rfl⟩ : syracuseStep 4492853 = 421205) (by norm_num)
theorem B1601089 : Blo 1330984 1601089 := bbase (se 2 (by rfl) ⟨600408, by rfl⟩ : syracuseStep 1601089 = 1200817) (by norm_num)
theorem B2526805 : Blo 1330984 2526805 := bbase (se 8 (by rfl) ⟨14805, by rfl⟩ : syracuseStep 2526805 = 29611) (by norm_num)
theorem B3198565 : Blo 1330984 3198565 := bbase (se 4 (by rfl) ⟨299865, by rfl⟩ : syracuseStep 3198565 = 599731) (by norm_num)
theorem B1896061 : Blo 1330984 1896061 := bbase (se 3 (by rfl) ⟨355511, by rfl⟩ : syracuseStep 1896061 = 711023) (by norm_num)
theorem B5058197 : Blo 1330984 5058197 := bbase (se 6 (by rfl) ⟨118551, by rfl⟩ : syracuseStep 5058197 = 237103) (by norm_num)
theorem B2248357 : Blo 1330984 2248357 := bbase (se 4 (by rfl) ⟨210783, by rfl⟩ : syracuseStep 2248357 = 421567) (by norm_num)
theorem B3370693 : Blo 1330984 3370693 := bbase (se 4 (by rfl) ⟨316002, by rfl⟩ : syracuseStep 3370693 = 632005) (by norm_num)
theorem B10120949 : Blo 1330984 10120949 := bbase (se 5 (by rfl) ⟨474419, by rfl⟩ : syracuseStep 10120949 = 948839) (by norm_num)
theorem B2248445 : Blo 1330984 2248445 := bbase (se 3 (by rfl) ⟨421583, by rfl⟩ : syracuseStep 2248445 = 843167) (by norm_num)
theorem B1519393 : Blo 1330984 1519393 := bbase (se 2 (by rfl) ⟨569772, by rfl⟩ : syracuseStep 1519393 = 1139545) (by norm_num)
theorem B3370805 : Blo 1330984 3370805 := bbase (se 5 (by rfl) ⟨158006, by rfl⟩ : syracuseStep 3370805 = 316013) (by norm_num)
theorem B2248573 : Blo 1330984 2248573 := bbase (se 3 (by rfl) ⟨421607, by rfl⟩ : syracuseStep 2248573 = 843215) (by norm_num)
theorem B2527109 : Blo 1330984 2527109 := bbase (se 4 (by rfl) ⟨236916, by rfl⟩ : syracuseStep 2527109 = 473833) (by norm_num)
theorem B2248661 : Blo 1330984 2248661 := bbase (se 7 (by rfl) ⟨26351, by rfl⟩ : syracuseStep 2248661 = 52703) (by norm_num)
theorem B4493285 : Blo 1330984 4493285 := bbase (se 4 (by rfl) ⟨421245, by rfl⟩ : syracuseStep 4493285 = 842491) (by norm_num)
theorem B3370997 : Blo 1330984 3370997 := bbase (se 5 (by rfl) ⟨158015, by rfl⟩ : syracuseStep 3370997 = 316031) (by norm_num)
theorem B3198989 : Blo 1330984 3198989 := bbase (se 3 (by rfl) ⟨599810, by rfl⟩ : syracuseStep 3198989 = 1199621) (by norm_num)
theorem B1421345 : Blo 1330984 1421345 := bbase (se 2 (by rfl) ⟨533004, by rfl⟩ : syracuseStep 1421345 = 1066009) (by norm_num)
theorem B6746165 : Blo 1330984 6746165 := bbase (se 5 (by rfl) ⟨316226, by rfl⟩ : syracuseStep 6746165 = 632453) (by norm_num)
theorem B15167573 : Blo 1330984 15167573 := bbase (se 8 (by rfl) ⟨88872, by rfl⟩ : syracuseStep 15167573 = 177745) (by norm_num)
theorem B2248789 : Blo 1330984 2248789 := bbase (se 8 (by rfl) ⟨13176, by rfl⟩ : syracuseStep 2248789 = 26353) (by norm_num)
theorem B10113173 : Blo 1330984 10113173 := bbase (se 6 (by rfl) ⟨237027, by rfl⟩ : syracuseStep 10113173 = 474055) (by norm_num)
theorem B2248877 : Blo 1330984 2248877 := bbase (se 3 (by rfl) ⟨421664, by rfl⟩ : syracuseStep 2248877 = 843329) (by norm_num)
theorem B1519817 : Blo 1330984 1519817 := bbase (se 2 (by rfl) ⟨569931, by rfl⟩ : syracuseStep 1519817 = 1139863) (by norm_num)
theorem B1896653 : Blo 1330984 1896653 := bbase (se 3 (by rfl) ⟨355622, by rfl⟩ : syracuseStep 1896653 = 711245) (by norm_num)
theorem B1421533 : Blo 1330984 1421533 := bbase (se 3 (by rfl) ⟨266537, by rfl⟩ : syracuseStep 1421533 = 533075) (by norm_num)
theorem B1896733 : Blo 1330984 1896733 := bbase (se 3 (by rfl) ⟨355637, by rfl⟩ : syracuseStep 1896733 = 711275) (by norm_num)
theorem B6402341 : Blo 1330984 6402341 := bbase (se 4 (by rfl) ⟨600219, by rfl⟩ : syracuseStep 6402341 = 1200439) (by norm_num)
theorem B3199277 : Blo 1330984 3199277 := bbase (se 3 (by rfl) ⟨599864, by rfl⟩ : syracuseStep 3199277 = 1199729) (by norm_num)
theorem B2249005 : Blo 1330984 2249005 := bbase (se 3 (by rfl) ⟨421688, by rfl⟩ : syracuseStep 2249005 = 843377) (by norm_num)
theorem B2134325 : Blo 1330984 2134325 := bbase (se 5 (by rfl) ⟨100046, by rfl⟩ : syracuseStep 2134325 = 200093) (by norm_num)
theorem B5402933 : Blo 1330984 5402933 := bbase (se 5 (by rfl) ⟨253262, by rfl⟩ : syracuseStep 5402933 = 506525) (by norm_num)
theorem B8106293 : Blo 1330984 8106293 := bbase (se 5 (by rfl) ⟨379982, by rfl⟩ : syracuseStep 8106293 = 759965) (by norm_num)
theorem B3371341 : Blo 1330984 3371341 := bbase (se 3 (by rfl) ⟨632126, by rfl⟩ : syracuseStep 3371341 = 1264253) (by norm_num)
theorem B2249093 : Blo 1330984 2249093 := bbase (se 4 (by rfl) ⟨210852, by rfl⟩ : syracuseStep 2249093 = 421705) (by norm_num)
theorem B1421717 : Blo 1330984 1421717 := bbase (se 6 (by rfl) ⟨33321, by rfl⟩ : syracuseStep 1421717 = 66643) (by norm_num)
theorem B4493717 : Blo 1330984 4493717 := bbase (se 6 (by rfl) ⟨105321, by rfl⟩ : syracuseStep 4493717 = 210643) (by norm_num)
theorem B1896853 : Blo 1330984 1896853 := bbase (se 6 (by rfl) ⟨44457, by rfl⟩ : syracuseStep 1896853 = 88915) (by norm_num)
theorem B2134453 : Blo 1330984 2134453 := bbase (se 5 (by rfl) ⟨100052, by rfl⟩ : syracuseStep 2134453 = 200105) (by norm_num)
theorem B5403061 : Blo 1330984 5403061 := bbase (se 5 (by rfl) ⟨253268, by rfl⟩ : syracuseStep 5403061 = 506537) (by norm_num)
theorem B3371453 : Blo 1330984 3371453 := bbase (se 3 (by rfl) ⟨632147, by rfl⟩ : syracuseStep 3371453 = 1264295) (by norm_num)
theorem B6738389 : Blo 1330984 6738389 := bbase (se 7 (by rfl) ⟨78965, by rfl⟩ : syracuseStep 6738389 = 157931) (by norm_num)
theorem B1896949 : Blo 1330984 1896949 := bbase (se 5 (by rfl) ⟨88919, by rfl⟩ : syracuseStep 1896949 = 177839) (by norm_num)
theorem B2249221 : Blo 1330984 2249221 := bbase (se 4 (by rfl) ⟨210864, by rfl⟩ : syracuseStep 2249221 = 421729) (by norm_num)
theorem B2699821 : Blo 1330984 2699821 := bbase (se 3 (by rfl) ⟨506216, by rfl⟩ : syracuseStep 2699821 = 1012433) (by norm_num)
theorem B2994749 : Blo 1330984 2994749 := bbase (se 3 (by rfl) ⟨561515, by rfl⟩ : syracuseStep 2994749 = 1123031) (by norm_num)
theorem B1708609 : Blo 1330984 1708609 := bbase (se 2 (by rfl) ⟨640728, by rfl⟩ : syracuseStep 1708609 = 1281457) (by norm_num)
theorem B2249309 : Blo 1330984 2249309 := bbase (se 3 (by rfl) ⟨421745, by rfl⟩ : syracuseStep 2249309 = 843491) (by norm_num)
theorem B2527861 : Blo 1330984 2527861 := bbase (se 5 (by rfl) ⟨118493, by rfl⟩ : syracuseStep 2527861 = 236987) (by norm_num)
theorem B3371645 : Blo 1330984 3371645 := bbase (se 3 (by rfl) ⟨632183, by rfl⟩ : syracuseStep 3371645 = 1264367) (by norm_num)
theorem B2994821 : Blo 1330984 2994821 := bbase (se 4 (by rfl) ⟨280764, by rfl⟩ : syracuseStep 2994821 = 561529) (by norm_num)
theorem B2994893 : Blo 1330984 2994893 := bbase (se 3 (by rfl) ⟨561542, by rfl⟩ : syracuseStep 2994893 = 1123085) (by norm_num)
theorem B2528005 : Blo 1330984 2528005 := bbase (se 4 (by rfl) ⟨237000, by rfl⟩ : syracuseStep 2528005 = 474001) (by norm_num)
theorem B2994965 : Blo 1330984 2994965 := bbase (se 6 (by rfl) ⟨70194, by rfl⟩ : syracuseStep 2994965 = 140389) (by norm_num)
theorem B4264741 : Blo 1330984 4264741 := bbase (se 4 (by rfl) ⟨399819, by rfl⟩ : syracuseStep 4264741 = 799639) (by norm_num)
theorem B5059381 : Blo 1330984 5059381 := bbase (se 5 (by rfl) ⟨237158, by rfl⟩ : syracuseStep 5059381 = 474317) (by norm_num)
theorem B2134837 : Blo 1330984 2134837 := bbase (se 5 (by rfl) ⟨100070, by rfl⟩ : syracuseStep 2134837 = 200141) (by norm_num)
theorem B4494149 : Blo 1330984 4494149 := bbase (se 4 (by rfl) ⟨421326, by rfl⟩ : syracuseStep 4494149 = 842653) (by norm_num)
theorem B19452757 : Blo 1330984 19452757 := bbase (se 9 (by rfl) ⟨56990, by rfl⟩ : syracuseStep 19452757 = 113981) (by norm_num)
theorem B2995037 : Blo 1330984 2995037 := bbase (se 3 (by rfl) ⟨561569, by rfl⟩ : syracuseStep 2995037 = 1123139) (by norm_num)
theorem B4264805 : Blo 1330984 4264805 := bbase (se 4 (by rfl) ⟨399825, by rfl⟩ : syracuseStep 4264805 = 799651) (by norm_num)
theorem B11375477 : Blo 1330984 11375477 := bbase (se 5 (by rfl) ⟨533225, by rfl⟩ : syracuseStep 11375477 = 1066451) (by norm_num)
theorem B2995109 : Blo 1330984 2995109 := bbase (se 4 (by rfl) ⟨280791, by rfl⟩ : syracuseStep 2995109 = 561583) (by norm_num)
theorem B2528165 : Blo 1330984 2528165 := bbase (se 4 (by rfl) ⟨237015, by rfl⟩ : syracuseStep 2528165 = 474031) (by norm_num)
theorem B6157237 : Blo 1330984 6157237 := bbase (se 5 (by rfl) ⟨288620, by rfl⟩ : syracuseStep 6157237 = 577241) (by norm_num)
theorem B3601349 : Blo 1330984 3601349 := bbase (se 4 (by rfl) ⟨337626, by rfl⟩ : syracuseStep 3601349 = 675253) (by norm_num)
theorem B6403013 : Blo 1330984 6403013 := bbase (se 4 (by rfl) ⟨600282, by rfl⟩ : syracuseStep 6403013 = 1200565) (by norm_num)
theorem B3371989 : Blo 1330984 3371989 := bbase (se 7 (by rfl) ⟨39515, by rfl⟩ : syracuseStep 3371989 = 79031) (by norm_num)
theorem B1897445 : Blo 1330984 1897445 := bbase (se 4 (by rfl) ⟨177885, by rfl⟩ : syracuseStep 1897445 = 355771) (by norm_num)
theorem B2995181 : Blo 1330984 2995181 := bbase (se 3 (by rfl) ⟨561596, by rfl⟩ : syracuseStep 2995181 = 1123193) (by norm_num)
theorem B1998845 : Blo 1330984 1998845 := bbase (se 3 (by rfl) ⟨374783, by rfl⟩ : syracuseStep 1998845 = 749567) (by norm_num)
theorem B2995253 : Blo 1330984 2995253 := bbase (se 5 (by rfl) ⟨140402, by rfl⟩ : syracuseStep 2995253 = 280805) (by norm_num)
theorem B2528309 : Blo 1330984 2528309 := bbase (se 5 (by rfl) ⟨118514, by rfl⟩ : syracuseStep 2528309 = 237029) (by norm_num)
theorem B2135093 : Blo 1330984 2135093 := bbase (se 5 (by rfl) ⟨100082, by rfl⟩ : syracuseStep 2135093 = 200165) (by norm_num)
theorem B3372101 : Blo 1330984 3372101 := bbase (se 4 (by rfl) ⟨316134, by rfl⟩ : syracuseStep 3372101 = 632269) (by norm_num)
theorem B1684577 : Blo 1330984 1684577 := bbase (se 2 (by rfl) ⟨631716, by rfl⟩ : syracuseStep 1684577 = 1263433) (by norm_num)
theorem B5059685 : Blo 1330984 5059685 := bbase (se 4 (by rfl) ⟨474345, by rfl⟩ : syracuseStep 5059685 = 948691) (by norm_num)
theorem B2995325 : Blo 1330984 2995325 := bbase (se 3 (by rfl) ⟨561623, by rfl⟩ : syracuseStep 2995325 = 1123247) (by norm_num)
theorem B1422469 : Blo 1330984 1422469 := bbase (se 4 (by rfl) ⟨133356, by rfl⟩ : syracuseStep 1422469 = 266713) (by norm_num)
theorem B1684633 : Blo 1330984 1684633 := bbase (se 2 (by rfl) ⟨631737, by rfl⟩ : syracuseStep 1684633 = 1263475) (by norm_num)
theorem B2995397 : Blo 1330984 2995397 := bbase (se 4 (by rfl) ⟨280818, by rfl⟩ : syracuseStep 2995397 = 561637) (by norm_num)
theorem B1422541 : Blo 1330984 1422541 := bbase (se 3 (by rfl) ⟨266726, by rfl⟩ : syracuseStep 1422541 = 533453) (by norm_num)
theorem B4494581 : Blo 1330984 4494581 := bbase (se 5 (by rfl) ⟨210683, by rfl⟩ : syracuseStep 4494581 = 421367) (by norm_num)
theorem B1684729 : Blo 1330984 1684729 := bbase (se 2 (by rfl) ⟨631773, by rfl⟩ : syracuseStep 1684729 = 1263547) (by norm_num)
theorem B2700541 : Blo 1330984 2700541 := bbase (se 3 (by rfl) ⟨506351, by rfl⟩ : syracuseStep 2700541 = 1012703) (by norm_num)
theorem B3372293 : Blo 1330984 3372293 := bbase (se 4 (by rfl) ⟨316152, by rfl⟩ : syracuseStep 3372293 = 632305) (by norm_num)
theorem B2995469 : Blo 1330984 2995469 := bbase (se 3 (by rfl) ⟨561650, by rfl⟩ : syracuseStep 2995469 = 1123301) (by norm_num)
theorem B1799453 : Blo 1330984 1799453 := bbase (se 3 (by rfl) ⟨337397, by rfl⟩ : syracuseStep 1799453 = 674795) (by norm_num)
theorem B6747461 : Blo 1330984 6747461 := bbase (se 4 (by rfl) ⟨632574, by rfl⟩ : syracuseStep 6747461 = 1265149) (by norm_num)
theorem B2995541 : Blo 1330984 2995541 := bbase (se 13 (by rfl) ⟨548, by rfl⟩ : syracuseStep 2995541 = 1097) (by norm_num)
theorem B2528597 : Blo 1330984 2528597 := bbase (se 14 (by rfl) ⟨231, by rfl⟩ : syracuseStep 2528597 = 463) (by norm_num)
theorem B1709429 : Blo 1330984 1709429 := bbase (se 5 (by rfl) ⟨80129, by rfl⟩ : syracuseStep 1709429 = 160259) (by norm_num)
theorem B1422721 : Blo 1330984 1422721 := bbase (se 2 (by rfl) ⟨533520, by rfl⟩ : syracuseStep 1422721 = 1067041) (by norm_num)
theorem B2995613 : Blo 1330984 2995613 := bbase (se 3 (by rfl) ⟨561677, by rfl⟩ : syracuseStep 2995613 = 1123355) (by norm_num)
theorem B1684901 : Blo 1330984 1684901 := bbase (se 4 (by rfl) ⟨157959, by rfl⟩ : syracuseStep 1684901 = 315919) (by norm_num)
theorem B3790277 : Blo 1330984 3790277 := bbase (se 4 (by rfl) ⟨355338, by rfl⟩ : syracuseStep 3790277 = 710677) (by norm_num)
theorem B1684957 : Blo 1330984 1684957 := bbase (se 3 (by rfl) ⟨315929, by rfl⟩ : syracuseStep 1684957 = 631859) (by norm_num)
theorem B2995685 : Blo 1330984 2995685 := bbase (se 4 (by rfl) ⟨280845, by rfl⟩ : syracuseStep 2995685 = 561691) (by norm_num)
theorem B2528749 : Blo 1330984 2528749 := bbase (se 3 (by rfl) ⟨474140, by rfl⟩ : syracuseStep 2528749 = 948281) (by norm_num)
theorem B2995757 : Blo 1330984 2995757 := bbase (se 3 (by rfl) ⟨561704, by rfl⟩ : syracuseStep 2995757 = 1123409) (by norm_num)
theorem B1685053 : Blo 1330984 1685053 := bbase (se 3 (by rfl) ⟨315947, by rfl⟩ : syracuseStep 1685053 = 631895) (by norm_num)
theorem B3372637 : Blo 1330984 3372637 := bbase (se 3 (by rfl) ⟨632369, by rfl⟩ : syracuseStep 3372637 = 1264739) (by norm_num)
theorem B2995829 : Blo 1330984 2995829 := bbase (se 5 (by rfl) ⟨140429, by rfl⟩ : syracuseStep 2995829 = 280859) (by norm_num)
theorem B4495013 : Blo 1330984 4495013 := bbase (se 4 (by rfl) ⟨421407, by rfl⟩ : syracuseStep 4495013 = 842815) (by norm_num)
theorem B5404325 : Blo 1330984 5404325 := bbase (se 4 (by rfl) ⟨506655, by rfl⟩ : syracuseStep 5404325 = 1013311) (by norm_num)
theorem B2995901 : Blo 1330984 2995901 := bbase (se 3 (by rfl) ⟨561731, by rfl⟩ : syracuseStep 2995901 = 1123463) (by norm_num)
theorem B1996493 : Blo 1330984 1996493 := bbase (se 3 (by rfl) ⟨374342, by rfl⟩ : syracuseStep 1996493 = 748685) (by norm_num)
theorem B3372749 : Blo 1330984 3372749 := bbase (se 3 (by rfl) ⟨632390, by rfl⟩ : syracuseStep 3372749 = 1264781) (by norm_num)
theorem B1996517 : Blo 1330984 1996517 := bbase (se 4 (by rfl) ⟨187173, by rfl⟩ : syracuseStep 1996517 = 374347) (by norm_num)
theorem B6739685 : Blo 1330984 6739685 := bbase (se 4 (by rfl) ⟨631845, by rfl⟩ : syracuseStep 6739685 = 1263691) (by norm_num)
theorem B1685225 : Blo 1330984 1685225 := bbase (se 2 (by rfl) ⟨631959, by rfl⟩ : syracuseStep 1685225 = 1263919) (by norm_num)
theorem B1996541 : Blo 1330984 1996541 := bbase (se 3 (by rfl) ⟨374351, by rfl⟩ : syracuseStep 1996541 = 748703) (by norm_num)
theorem B2995973 : Blo 1330984 2995973 := bbase (se 4 (by rfl) ⟨280872, by rfl⟩ : syracuseStep 2995973 = 561745) (by norm_num)
theorem B1996565 : Blo 1330984 1996565 := bbase (se 6 (by rfl) ⟨46794, by rfl⟩ : syracuseStep 1996565 = 93589) (by norm_num)
theorem B2529053 : Blo 1330984 2529053 := bbase (se 3 (by rfl) ⟨474197, by rfl⟩ : syracuseStep 2529053 = 948395) (by norm_num)
theorem B1685281 : Blo 1330984 1685281 := bbase (se 2 (by rfl) ⟨631980, by rfl⟩ : syracuseStep 1685281 = 1263961) (by norm_num)
theorem B1996589 : Blo 1330984 1996589 := bbase (se 3 (by rfl) ⟨374360, by rfl⟩ : syracuseStep 1996589 = 748721) (by norm_num)
theorem B1423165 : Blo 1330984 1423165 := bbase (se 3 (by rfl) ⟨266843, by rfl⟩ : syracuseStep 1423165 = 533687) (by norm_num)
theorem B1996613 : Blo 1330984 1996613 := bbase (se 4 (by rfl) ⟨187182, by rfl⟩ : syracuseStep 1996613 = 374365) (by norm_num)
theorem B2561861 : Blo 1330984 2561861 := bbase (se 4 (by rfl) ⟨240174, by rfl⟩ : syracuseStep 2561861 = 480349) (by norm_num)
theorem B2996045 : Blo 1330984 2996045 := bbase (se 3 (by rfl) ⟨561758, by rfl⟩ : syracuseStep 2996045 = 1123517) (by norm_num)
theorem B1996637 : Blo 1330984 1996637 := bbase (se 3 (by rfl) ⟨374369, by rfl⟩ : syracuseStep 1996637 = 748739) (by norm_num)
theorem B1996661 : Blo 1330984 1996661 := bbase (se 5 (by rfl) ⟨93593, by rfl⟩ : syracuseStep 1996661 = 187187) (by norm_num)
theorem B3790709 : Blo 1330984 3790709 := bbase (se 5 (by rfl) ⟨177689, by rfl⟩ : syracuseStep 3790709 = 355379) (by norm_num)
theorem B1685377 : Blo 1330984 1685377 := bbase (se 2 (by rfl) ⟨632016, by rfl⟩ : syracuseStep 1685377 = 1264033) (by norm_num)
theorem B1996685 : Blo 1330984 1996685 := bbase (se 3 (by rfl) ⟨374378, by rfl⟩ : syracuseStep 1996685 = 748757) (by norm_num)
theorem B3372941 : Blo 1330984 3372941 := bbase (se 3 (by rfl) ⟨632426, by rfl⟩ : syracuseStep 3372941 = 1264853) (by norm_num)
theorem B2996117 : Blo 1330984 2996117 := bbase (se 6 (by rfl) ⟨70221, by rfl⟩ : syracuseStep 2996117 = 140443) (by norm_num)
theorem B1349533 : Blo 1330984 1349533 := bbase (se 3 (by rfl) ⟨253037, by rfl⟩ : syracuseStep 1349533 = 506075) (by norm_num)
theorem B1996709 : Blo 1330984 1996709 := bbase (se 4 (by rfl) ⟨187191, by rfl⟩ : syracuseStep 1996709 = 374383) (by norm_num)
theorem B1800101 : Blo 1330984 1800101 := bbase (se 4 (by rfl) ⟨168759, by rfl⟩ : syracuseStep 1800101 = 337519) (by norm_num)
theorem B1423289 : Blo 1330984 1423289 := bbase (se 2 (by rfl) ⟨533733, by rfl⟩ : syracuseStep 1423289 = 1067467) (by norm_num)
theorem B1996733 : Blo 1330984 1996733 := bbase (se 3 (by rfl) ⟨374387, by rfl⟩ : syracuseStep 1996733 = 748775) (by norm_num)
theorem B2561989 : Blo 1330984 2561989 := bbase (se 4 (by rfl) ⟨240186, by rfl⟩ : syracuseStep 2561989 = 480373) (by norm_num)
theorem B1996757 : Blo 1330984 1996757 := bbase (se 7 (by rfl) ⟨23399, by rfl⟩ : syracuseStep 1996757 = 46799) (by norm_num)
theorem B2996189 : Blo 1330984 2996189 := bbase (se 3 (by rfl) ⟨561785, by rfl⟩ : syracuseStep 2996189 = 1123571) (by norm_num)
theorem B1996781 : Blo 1330984 1996781 := bbase (se 3 (by rfl) ⟨374396, by rfl⟩ : syracuseStep 1996781 = 748793) (by norm_num)
theorem B1996805 : Blo 1330984 1996805 := bbase (se 4 (by rfl) ⟨187200, by rfl⟩ : syracuseStep 1996805 = 374401) (by norm_num)
theorem B1996829 : Blo 1330984 1996829 := bbase (se 3 (by rfl) ⟨374405, by rfl⟩ : syracuseStep 1996829 = 748811) (by norm_num)
theorem B2996261 : Blo 1330984 2996261 := bbase (se 4 (by rfl) ⟨280899, by rfl⟩ : syracuseStep 2996261 = 561799) (by norm_num)
theorem B1685549 : Blo 1330984 1685549 := bbase (se 3 (by rfl) ⟨316040, by rfl⟩ : syracuseStep 1685549 = 632081) (by norm_num)
theorem B1996853 : Blo 1330984 1996853 := bbase (se 5 (by rfl) ⟨93602, by rfl⟩ : syracuseStep 1996853 = 187205) (by norm_num)
theorem B8534069 : Blo 1330984 8534069 := bbase (se 5 (by rfl) ⟨400034, by rfl⟩ : syracuseStep 8534069 = 800069) (by norm_num)
theorem B1996877 : Blo 1330984 1996877 := bbase (se 3 (by rfl) ⟨374414, by rfl⟩ : syracuseStep 1996877 = 748829) (by norm_num)
theorem B1923149 : Blo 1330984 1923149 := bbase (se 3 (by rfl) ⟨360590, by rfl⟩ : syracuseStep 1923149 = 721181) (by norm_num)
theorem B4495445 : Blo 1330984 4495445 := bbase (se 8 (by rfl) ⟨26340, by rfl⟩ : syracuseStep 4495445 = 52681) (by norm_num)
theorem B1996901 : Blo 1330984 1996901 := bbase (se 4 (by rfl) ⟨187209, by rfl⟩ : syracuseStep 1996901 = 374419) (by norm_num)
theorem B1685605 : Blo 1330984 1685605 := bbase (se 4 (by rfl) ⟨158025, by rfl⟩ : syracuseStep 1685605 = 316051) (by norm_num)
theorem B2996333 : Blo 1330984 2996333 := bbase (se 3 (by rfl) ⟨561812, by rfl⟩ : syracuseStep 2996333 = 1123625) (by norm_num)
theorem B1996925 : Blo 1330984 1996925 := bbase (se 3 (by rfl) ⟨374423, by rfl⟩ : syracuseStep 1996925 = 748847) (by norm_num)
theorem B2562173 : Blo 1330984 2562173 := bbase (se 3 (by rfl) ⟨480407, by rfl⟩ : syracuseStep 2562173 = 960815) (by norm_num)
theorem B4798597 : Blo 1330984 4798597 := bbase (se 4 (by rfl) ⟨449868, by rfl⟩ : syracuseStep 4798597 = 899737) (by norm_num)
theorem B1996949 : Blo 1330984 1996949 := bbase (se 6 (by rfl) ⟨46803, by rfl⟩ : syracuseStep 1996949 = 93607) (by norm_num)
theorem B1996973 : Blo 1330984 1996973 := bbase (se 3 (by rfl) ⟨374432, by rfl⟩ : syracuseStep 1996973 = 748865) (by norm_num)
theorem B2996405 : Blo 1330984 2996405 := bbase (se 5 (by rfl) ⟨140456, by rfl⟩ : syracuseStep 2996405 = 280913) (by norm_num)
theorem B1996997 : Blo 1330984 1996997 := bbase (se 4 (by rfl) ⟨187218, by rfl⟩ : syracuseStep 1996997 = 374437) (by norm_num)
theorem B1685701 : Blo 1330984 1685701 := bbase (se 4 (by rfl) ⟨158034, by rfl⟩ : syracuseStep 1685701 = 316069) (by norm_num)
theorem B1349849 : Blo 1330984 1349849 := bbase (se 2 (by rfl) ⟨506193, by rfl⟩ : syracuseStep 1349849 = 1012387) (by norm_num)
theorem B1997021 : Blo 1330984 1997021 := bbase (se 3 (by rfl) ⟨374441, by rfl⟩ : syracuseStep 1997021 = 748883) (by norm_num)
theorem B6830309 : Blo 1330984 6830309 := bbase (se 4 (by rfl) ⟨640341, by rfl⟩ : syracuseStep 6830309 = 1280683) (by norm_num)
theorem B3373285 : Blo 1330984 3373285 := bbase (se 4 (by rfl) ⟨316245, by rfl⟩ : syracuseStep 3373285 = 632491) (by norm_num)
theorem B1997045 : Blo 1330984 1997045 := bbase (se 5 (by rfl) ⟨93611, by rfl⟩ : syracuseStep 1997045 = 187223) (by norm_num)
theorem B1349881 : Blo 1330984 1349881 := bbase (se 2 (by rfl) ⟨506205, by rfl⟩ : syracuseStep 1349881 = 1012411) (by norm_num)
theorem B2996477 : Blo 1330984 2996477 := bbase (se 3 (by rfl) ⟨561839, by rfl⟩ : syracuseStep 2996477 = 1123679) (by norm_num)
theorem B5691653 : Blo 1330984 5691653 := bbase (se 4 (by rfl) ⟨533592, by rfl⟩ : syracuseStep 5691653 = 1067185) (by norm_num)
theorem B1997069 : Blo 1330984 1997069 := bbase (se 3 (by rfl) ⟨374450, by rfl⟩ : syracuseStep 1997069 = 748901) (by norm_num)
theorem B1497361 : Blo 1330984 1497361 := bbase (se 2 (by rfl) ⟨561510, by rfl⟩ : syracuseStep 1497361 = 1123021) (by norm_num)
theorem B1997093 : Blo 1330984 1997093 := bbase (se 4 (by rfl) ⟨187227, by rfl⟩ : syracuseStep 1997093 = 374455) (by norm_num)
theorem B4798757 : Blo 1330984 4798757 := bbase (se 4 (by rfl) ⟨449883, by rfl⟩ : syracuseStep 4798757 = 899767) (by norm_num)
theorem B1497397 : Blo 1330984 1497397 := bbase (se 5 (by rfl) ⟨70190, by rfl⟩ : syracuseStep 1497397 = 140381) (by norm_num)
theorem B1997117 : Blo 1330984 1997117 := bbase (se 3 (by rfl) ⟨374459, by rfl⟩ : syracuseStep 1997117 = 748919) (by norm_num)
theorem B2996549 : Blo 1330984 2996549 := bbase (se 4 (by rfl) ⟨280926, by rfl⟩ : syracuseStep 2996549 = 561853) (by norm_num)
theorem B1997141 : Blo 1330984 1997141 := bbase (se 10 (by rfl) ⟨2925, by rfl⟩ : syracuseStep 1997141 = 5851) (by norm_num)
theorem B3373397 : Blo 1330984 3373397 := bbase (se 10 (by rfl) ⟨4941, by rfl⟩ : syracuseStep 3373397 = 9883) (by norm_num)
theorem B1497433 : Blo 1330984 1497433 := bbase (se 2 (by rfl) ⟨561537, by rfl⟩ : syracuseStep 1497433 = 1123075) (by norm_num)
theorem B1997165 : Blo 1330984 1997165 := bbase (se 3 (by rfl) ⟨374468, by rfl⟩ : syracuseStep 1997165 = 748937) (by norm_num)
theorem B1685873 : Blo 1330984 1685873 := bbase (se 2 (by rfl) ⟨632202, by rfl⟩ : syracuseStep 1685873 = 1264405) (by norm_num)
theorem B1497469 : Blo 1330984 1497469 := bbase (se 3 (by rfl) ⟨280775, by rfl⟩ : syracuseStep 1497469 = 561551) (by norm_num)
theorem B1997189 : Blo 1330984 1997189 := bbase (se 4 (by rfl) ⟨187236, by rfl⟩ : syracuseStep 1997189 = 374473) (by norm_num)
theorem B2996621 : Blo 1330984 2996621 := bbase (se 3 (by rfl) ⟨561866, by rfl⟩ : syracuseStep 2996621 = 1123733) (by norm_num)
theorem B1997213 : Blo 1330984 1997213 := bbase (se 3 (by rfl) ⟨374477, by rfl⟩ : syracuseStep 1997213 = 748955) (by norm_num)
theorem B1497505 : Blo 1330984 1497505 := bbase (se 2 (by rfl) ⟨561564, by rfl⟩ : syracuseStep 1497505 = 1123129) (by norm_num)
theorem B1685929 : Blo 1330984 1685929 := bbase (se 2 (by rfl) ⟨632223, by rfl⟩ : syracuseStep 1685929 = 1264447) (by norm_num)
theorem B1997237 : Blo 1330984 1997237 := bbase (se 5 (by rfl) ⟨93620, by rfl⟩ : syracuseStep 1997237 = 187241) (by norm_num)
theorem B1497541 : Blo 1330984 1497541 := bbase (se 4 (by rfl) ⟨140394, by rfl⟩ : syracuseStep 1497541 = 280789) (by norm_num)
theorem B5126597 : Blo 1330984 5126597 := bbase (se 4 (by rfl) ⟨480618, by rfl⟩ : syracuseStep 5126597 = 961237) (by norm_num)
theorem B1997261 : Blo 1330984 1997261 := bbase (se 3 (by rfl) ⟨374486, by rfl⟩ : syracuseStep 1997261 = 748973) (by norm_num)
theorem B2996693 : Blo 1330984 2996693 := bbase (se 7 (by rfl) ⟨35117, by rfl⟩ : syracuseStep 2996693 = 70235) (by norm_num)
theorem B1997285 : Blo 1330984 1997285 := bbase (se 4 (by rfl) ⟨187245, by rfl⟩ : syracuseStep 1997285 = 374491) (by norm_num)
theorem B1497577 : Blo 1330984 1497577 := bbase (se 2 (by rfl) ⟨561591, by rfl⟩ : syracuseStep 1497577 = 1123183) (by norm_num)
theorem B2398709 : Blo 1330984 2398709 := bbase (se 5 (by rfl) ⟨112439, by rfl⟩ : syracuseStep 2398709 = 224879) (by norm_num)
theorem B1997309 : Blo 1330984 1997309 := bbase (se 3 (by rfl) ⟨374495, by rfl⟩ : syracuseStep 1997309 = 748991) (by norm_num)
theorem B4495877 : Blo 1330984 4495877 := bbase (se 4 (by rfl) ⟨421488, by rfl⟩ : syracuseStep 4495877 = 842977) (by norm_num)
theorem B1686025 : Blo 1330984 1686025 := bbase (se 2 (by rfl) ⟨632259, by rfl⟩ : syracuseStep 1686025 = 1264519) (by norm_num)
theorem B1497613 : Blo 1330984 1497613 := bbase (se 3 (by rfl) ⟨280802, by rfl⟩ : syracuseStep 1497613 = 561605) (by norm_num)
theorem B3037709 : Blo 1330984 3037709 := bbase (se 3 (by rfl) ⟨569570, by rfl⟩ : syracuseStep 3037709 = 1139141) (by norm_num)
theorem B2529805 : Blo 1330984 2529805 := bbase (se 3 (by rfl) ⟨474338, by rfl⟩ : syracuseStep 2529805 = 948677) (by norm_num)
theorem B1997333 : Blo 1330984 1997333 := bbase (se 6 (by rfl) ⟨46812, by rfl⟩ : syracuseStep 1997333 = 93625) (by norm_num)
theorem B3373589 : Blo 1330984 3373589 := bbase (se 6 (by rfl) ⟨79068, by rfl⟩ : syracuseStep 3373589 = 158137) (by norm_num)
theorem B2996765 : Blo 1330984 2996765 := bbase (se 3 (by rfl) ⟨561893, by rfl⟩ : syracuseStep 2996765 = 1123787) (by norm_num)
theorem B2341405 : Blo 1330984 2341405 := bbase (se 3 (by rfl) ⟨439013, by rfl⟩ : syracuseStep 2341405 = 878027) (by norm_num)
theorem B5691941 : Blo 1330984 5691941 := bbase (se 4 (by rfl) ⟨533619, by rfl⟩ : syracuseStep 5691941 = 1067239) (by norm_num)
theorem B1997357 : Blo 1330984 1997357 := bbase (se 3 (by rfl) ⟨374504, by rfl⟩ : syracuseStep 1997357 = 749009) (by norm_num)
theorem B1497649 : Blo 1330984 1497649 := bbase (se 2 (by rfl) ⟨561618, by rfl⟩ : syracuseStep 1497649 = 1123237) (by norm_num)
theorem B1997381 : Blo 1330984 1997381 := bbase (se 4 (by rfl) ⟨187254, by rfl⟩ : syracuseStep 1997381 = 374509) (by norm_num)
theorem B1497685 : Blo 1330984 1497685 := bbase (se 8 (by rfl) ⟨8775, by rfl⟩ : syracuseStep 1497685 = 17551) (by norm_num)
theorem B1997405 : Blo 1330984 1997405 := bbase (se 3 (by rfl) ⟨374513, by rfl⟩ : syracuseStep 1997405 = 749027) (by norm_num)
theorem B3791461 : Blo 1330984 3791461 := bbase (se 4 (by rfl) ⟨355449, by rfl⟩ : syracuseStep 3791461 = 710899) (by norm_num)
theorem B2996837 : Blo 1330984 2996837 := bbase (se 4 (by rfl) ⟨280953, by rfl⟩ : syracuseStep 2996837 = 561907) (by norm_num)
theorem B1997429 : Blo 1330984 1997429 := bbase (se 5 (by rfl) ⟨93629, by rfl⟩ : syracuseStep 1997429 = 187259) (by norm_num)
theorem B1497721 : Blo 1330984 1497721 := bbase (se 2 (by rfl) ⟨561645, by rfl⟩ : syracuseStep 1497721 = 1123291) (by norm_num)
theorem B1997453 : Blo 1330984 1997453 := bbase (se 3 (by rfl) ⟨374522, by rfl⟩ : syracuseStep 1997453 = 749045) (by norm_num)
theorem B1497757 : Blo 1330984 1497757 := bbase (se 3 (by rfl) ⟨280829, by rfl⟩ : syracuseStep 1497757 = 561659) (by norm_num)
theorem B2529949 : Blo 1330984 2529949 := bbase (se 3 (by rfl) ⟨474365, by rfl⟩ : syracuseStep 2529949 = 948731) (by norm_num)
theorem B1997477 : Blo 1330984 1997477 := bbase (se 4 (by rfl) ⟨187263, by rfl⟩ : syracuseStep 1997477 = 374527) (by norm_num)
theorem B2996909 : Blo 1330984 2996909 := bbase (se 3 (by rfl) ⟨561920, by rfl⟩ : syracuseStep 2996909 = 1123841) (by norm_num)
theorem B1686197 : Blo 1330984 1686197 := bbase (se 5 (by rfl) ⟨79040, by rfl⟩ : syracuseStep 1686197 = 158081) (by norm_num)
theorem B1997501 : Blo 1330984 1997501 := bbase (se 3 (by rfl) ⟨374531, by rfl⟩ : syracuseStep 1997501 = 749063) (by norm_num)
theorem B1497793 : Blo 1330984 1497793 := bbase (se 2 (by rfl) ⟨561672, by rfl⟩ : syracuseStep 1497793 = 1123345) (by norm_num)
theorem B1997525 : Blo 1330984 1997525 := bbase (se 7 (by rfl) ⟨23408, by rfl⟩ : syracuseStep 1997525 = 46817) (by norm_num)
theorem B6830821 : Blo 1330984 6830821 := bbase (se 4 (by rfl) ⟨640389, by rfl⟩ : syracuseStep 6830821 = 1280779) (by norm_num)
theorem B1497829 : Blo 1330984 1497829 := bbase (se 4 (by rfl) ⟨140421, by rfl⟩ : syracuseStep 1497829 = 280843) (by norm_num)
theorem B1997549 : Blo 1330984 1997549 := bbase (se 3 (by rfl) ⟨374540, by rfl⟩ : syracuseStep 1997549 = 749081) (by norm_num)
theorem B1686253 : Blo 1330984 1686253 := bbase (se 3 (by rfl) ⟨316172, by rfl⟩ : syracuseStep 1686253 = 632345) (by norm_num)
theorem B2996981 : Blo 1330984 2996981 := bbase (se 5 (by rfl) ⟨140483, by rfl⟩ : syracuseStep 2996981 = 280967) (by norm_num)
theorem B1997573 : Blo 1330984 1997573 := bbase (se 4 (by rfl) ⟨187272, by rfl⟩ : syracuseStep 1997573 = 374545) (by norm_num)
theorem B1497865 : Blo 1330984 1497865 := bbase (se 2 (by rfl) ⟨561699, by rfl⟩ : syracuseStep 1497865 = 1123399) (by norm_num)
theorem B2398997 : Blo 1330984 2398997 := bbase (se 6 (by rfl) ⟨56226, by rfl⟩ : syracuseStep 2398997 = 112453) (by norm_num)
theorem B1997597 : Blo 1330984 1997597 := bbase (se 3 (by rfl) ⟨374549, by rfl⟩ : syracuseStep 1997597 = 749099) (by norm_num)
theorem B1350433 : Blo 1330984 1350433 := bbase (se 2 (by rfl) ⟨506412, by rfl⟩ : syracuseStep 1350433 = 1012825) (by norm_num)
theorem B1497901 : Blo 1330984 1497901 := bbase (se 3 (by rfl) ⟨280856, by rfl⟩ : syracuseStep 1497901 = 561713) (by norm_num)
theorem B1997621 : Blo 1330984 1997621 := bbase (se 5 (by rfl) ⟨93638, by rfl⟩ : syracuseStep 1997621 = 187277) (by norm_num)
theorem B2997053 : Blo 1330984 2997053 := bbase (se 3 (by rfl) ⟨561947, by rfl⟩ : syracuseStep 2997053 = 1123895) (by norm_num)
theorem B2530109 : Blo 1330984 2530109 := bbase (se 3 (by rfl) ⟨474395, by rfl⟩ : syracuseStep 2530109 = 948791) (by norm_num)
theorem B1997645 : Blo 1330984 1997645 := bbase (se 3 (by rfl) ⟨374558, by rfl⟩ : syracuseStep 1997645 = 749117) (by norm_num)
theorem B1686349 : Blo 1330984 1686349 := bbase (se 3 (by rfl) ⟨316190, by rfl⟩ : syracuseStep 1686349 = 632381) (by norm_num)
theorem B1497937 : Blo 1330984 1497937 := bbase (se 2 (by rfl) ⟨561726, by rfl⟩ : syracuseStep 1497937 = 1123453) (by norm_num)
theorem B1997669 : Blo 1330984 1997669 := bbase (se 4 (by rfl) ⟨187281, by rfl⟩ : syracuseStep 1997669 = 374563) (by norm_num)
theorem B3373933 : Blo 1330984 3373933 := bbase (se 3 (by rfl) ⟨632612, by rfl⟩ : syracuseStep 3373933 = 1265225) (by norm_num)
theorem B1497973 : Blo 1330984 1497973 := bbase (se 5 (by rfl) ⟨70217, by rfl⟩ : syracuseStep 1497973 = 140435) (by norm_num)
theorem B1997693 : Blo 1330984 1997693 := bbase (se 3 (by rfl) ⟨374567, by rfl⟩ : syracuseStep 1997693 = 749135) (by norm_num)
theorem B2997125 : Blo 1330984 2997125 := bbase (se 4 (by rfl) ⟨280980, by rfl⟩ : syracuseStep 2997125 = 561961) (by norm_num)
theorem B1825669 : Blo 1330984 1825669 := bbase (se 4 (by rfl) ⟨171156, by rfl⟩ : syracuseStep 1825669 = 342313) (by norm_num)
theorem B1997717 : Blo 1330984 1997717 := bbase (se 6 (by rfl) ⟨46821, by rfl⟩ : syracuseStep 1997717 = 93643) (by norm_num)
theorem B1498009 : Blo 1330984 1498009 := bbase (se 2 (by rfl) ⟨561753, by rfl⟩ : syracuseStep 1498009 = 1123507) (by norm_num)
theorem B1997741 : Blo 1330984 1997741 := bbase (se 3 (by rfl) ⟨374576, by rfl⟩ : syracuseStep 1997741 = 749153) (by norm_num)
theorem B4496309 : Blo 1330984 4496309 := bbase (se 5 (by rfl) ⟨210764, by rfl⟩ : syracuseStep 4496309 = 421529) (by norm_num)
theorem B2702261 : Blo 1330984 2702261 := bbase (se 5 (by rfl) ⟨126668, by rfl⟩ : syracuseStep 2702261 = 253337) (by norm_num)
theorem B1498045 : Blo 1330984 1498045 := bbase (se 3 (by rfl) ⟨280883, by rfl⟩ : syracuseStep 1498045 = 561767) (by norm_num)
theorem B1997765 : Blo 1330984 1997765 := bbase (se 4 (by rfl) ⟨187290, by rfl⟩ : syracuseStep 1997765 = 374581) (by norm_num)
theorem B2997197 : Blo 1330984 2997197 := bbase (se 3 (by rfl) ⟨561974, by rfl⟩ : syracuseStep 2997197 = 1123949) (by norm_num)
theorem B2530253 : Blo 1330984 2530253 := bbase (se 3 (by rfl) ⟨474422, by rfl⟩ : syracuseStep 2530253 = 948845) (by norm_num)
theorem B1997789 : Blo 1330984 1997789 := bbase (se 3 (by rfl) ⟨374585, by rfl⟩ : syracuseStep 1997789 = 749171) (by norm_num)
theorem B3374045 : Blo 1330984 3374045 := bbase (se 3 (by rfl) ⟨632633, by rfl⟩ : syracuseStep 3374045 = 1265267) (by norm_num)
theorem B1498081 : Blo 1330984 1498081 := bbase (se 2 (by rfl) ⟨561780, by rfl⟩ : syracuseStep 1498081 = 1123561) (by norm_num)
theorem B2399213 : Blo 1330984 2399213 := bbase (se 3 (by rfl) ⟨449852, by rfl⟩ : syracuseStep 2399213 = 899705) (by norm_num)
theorem B6740981 : Blo 1330984 6740981 := bbase (se 5 (by rfl) ⟨315983, by rfl⟩ : syracuseStep 6740981 = 631967) (by norm_num)
theorem B1997813 : Blo 1330984 1997813 := bbase (se 5 (by rfl) ⟨93647, by rfl⟩ : syracuseStep 1997813 = 187295) (by norm_num)
theorem B1686521 : Blo 1330984 1686521 := bbase (se 2 (by rfl) ⟨632445, by rfl⟩ : syracuseStep 1686521 = 1264891) (by norm_num)
theorem B1498117 : Blo 1330984 1498117 := bbase (se 4 (by rfl) ⟨140448, by rfl⟩ : syracuseStep 1498117 = 280897) (by norm_num)
theorem B1997837 : Blo 1330984 1997837 := bbase (se 3 (by rfl) ⟨374594, by rfl⟩ : syracuseStep 1997837 = 749189) (by norm_num)
theorem B2997269 : Blo 1330984 2997269 := bbase (se 6 (by rfl) ⟨70248, by rfl⟩ : syracuseStep 2997269 = 140497) (by norm_num)
theorem B1997861 : Blo 1330984 1997861 := bbase (se 4 (by rfl) ⟨187299, by rfl⟩ : syracuseStep 1997861 = 374599) (by norm_num)
theorem B1498153 : Blo 1330984 1498153 := bbase (se 2 (by rfl) ⟨561807, by rfl⟩ : syracuseStep 1498153 = 1123615) (by norm_num)
theorem B1686577 : Blo 1330984 1686577 := bbase (se 2 (by rfl) ⟨632466, by rfl⟩ : syracuseStep 1686577 = 1264933) (by norm_num)
theorem B1997885 : Blo 1330984 1997885 := bbase (se 3 (by rfl) ⟨374603, by rfl⟩ : syracuseStep 1997885 = 749207) (by norm_num)
theorem B1498189 : Blo 1330984 1498189 := bbase (se 3 (by rfl) ⟨280910, by rfl⟩ : syracuseStep 1498189 = 561821) (by norm_num)
theorem B1997909 : Blo 1330984 1997909 := bbase (se 8 (by rfl) ⟨11706, by rfl⟩ : syracuseStep 1997909 = 23413) (by norm_num)
theorem B2997341 : Blo 1330984 2997341 := bbase (se 3 (by rfl) ⟨562001, by rfl⟩ : syracuseStep 2997341 = 1124003) (by norm_num)
theorem B1997933 : Blo 1330984 1997933 := bbase (se 3 (by rfl) ⟨374612, by rfl⟩ : syracuseStep 1997933 = 749225) (by norm_num)
theorem B1498225 : Blo 1330984 1498225 := bbase (se 2 (by rfl) ⟨561834, by rfl⟩ : syracuseStep 1498225 = 1123669) (by norm_num)
theorem B1997957 : Blo 1330984 1997957 := bbase (se 4 (by rfl) ⟨187308, by rfl⟩ : syracuseStep 1997957 = 374617) (by norm_num)
theorem B1686673 : Blo 1330984 1686673 := bbase (se 2 (by rfl) ⟨632502, by rfl⟩ : syracuseStep 1686673 = 1265005) (by norm_num)
theorem B12795029 : Blo 1330984 12795029 := bbase (se 6 (by rfl) ⟨299883, by rfl⟩ : syracuseStep 12795029 = 599767) (by norm_num)
theorem B1498261 : Blo 1330984 1498261 := bbase (se 6 (by rfl) ⟨35115, by rfl⟩ : syracuseStep 1498261 = 70231) (by norm_num)
theorem B1997981 : Blo 1330984 1997981 := bbase (se 3 (by rfl) ⟨374621, by rfl⟩ : syracuseStep 1997981 = 749243) (by norm_num)
theorem B2161829 : Blo 1330984 2161829 := bbase (se 4 (by rfl) ⟨202671, by rfl⟩ : syracuseStep 2161829 = 405343) (by norm_num)
theorem B2997413 : Blo 1330984 2997413 := bbase (se 4 (by rfl) ⟨281007, by rfl⟩ : syracuseStep 2997413 = 562015) (by norm_num)
theorem B1998005 : Blo 1330984 1998005 := bbase (se 5 (by rfl) ⟨93656, by rfl⟩ : syracuseStep 1998005 = 187313) (by norm_num)
theorem B1498297 : Blo 1330984 1498297 := bbase (se 2 (by rfl) ⟨561861, by rfl⟩ : syracuseStep 1498297 = 1123723) (by norm_num)
theorem B1998029 : Blo 1330984 1998029 := bbase (se 3 (by rfl) ⟨374630, by rfl⟩ : syracuseStep 1998029 = 749261) (by norm_num)
theorem B1498333 : Blo 1330984 1498333 := bbase (se 3 (by rfl) ⟨280937, by rfl⟩ : syracuseStep 1498333 = 561875) (by norm_num)
theorem B1998053 : Blo 1330984 1998053 := bbase (se 4 (by rfl) ⟨187317, by rfl⟩ : syracuseStep 1998053 = 374635) (by norm_num)
theorem B2997485 : Blo 1330984 2997485 := bbase (se 3 (by rfl) ⟨562028, by rfl⟩ : syracuseStep 2997485 = 1124057) (by norm_num)
theorem B2530541 : Blo 1330984 2530541 := bbase (se 3 (by rfl) ⟨474476, by rfl⟩ : syracuseStep 2530541 = 948953) (by norm_num)
theorem B1998077 : Blo 1330984 1998077 := bbase (se 3 (by rfl) ⟨374639, by rfl⟩ : syracuseStep 1998077 = 749279) (by norm_num)
theorem B1498369 : Blo 1330984 1498369 := bbase (se 2 (by rfl) ⟨561888, by rfl⟩ : syracuseStep 1498369 = 1123777) (by norm_num)
theorem B1998101 : Blo 1330984 1998101 := bbase (se 6 (by rfl) ⟨46830, by rfl⟩ : syracuseStep 1998101 = 93661) (by norm_num)
theorem B5692693 : Blo 1330984 5692693 := bbase (se 6 (by rfl) ⟨133422, by rfl⟩ : syracuseStep 5692693 = 266845) (by norm_num)
theorem B1498405 : Blo 1330984 1498405 := bbase (se 4 (by rfl) ⟨140475, by rfl⟩ : syracuseStep 1498405 = 280951) (by norm_num)
theorem B1998125 : Blo 1330984 1998125 := bbase (se 3 (by rfl) ⟨374648, by rfl⟩ : syracuseStep 1998125 = 749297) (by norm_num)
theorem B2997557 : Blo 1330984 2997557 := bbase (se 5 (by rfl) ⟨140510, by rfl⟩ : syracuseStep 2997557 = 281021) (by norm_num)
theorem B1686845 : Blo 1330984 1686845 := bbase (se 3 (by rfl) ⟨316283, by rfl⟩ : syracuseStep 1686845 = 632567) (by norm_num)
theorem B1998149 : Blo 1330984 1998149 := bbase (se 4 (by rfl) ⟨187326, by rfl⟩ : syracuseStep 1998149 = 374653) (by norm_num)
theorem B1498441 : Blo 1330984 1498441 := bbase (se 2 (by rfl) ⟨561915, by rfl⟩ : syracuseStep 1498441 = 1123831) (by norm_num)
theorem B7585109 : Blo 1330984 7585109 := bbase (se 11 (by rfl) ⟨5555, by rfl⟩ : syracuseStep 7585109 = 11111) (by norm_num)
theorem B1998173 : Blo 1330984 1998173 := bbase (se 3 (by rfl) ⟨374657, by rfl⟩ : syracuseStep 1998173 = 749315) (by norm_num)
theorem B4496741 : Blo 1330984 4496741 := bbase (se 4 (by rfl) ⟨421569, by rfl⟩ : syracuseStep 4496741 = 843139) (by norm_num)
theorem B1498477 : Blo 1330984 1498477 := bbase (se 3 (by rfl) ⟨280964, by rfl⟩ : syracuseStep 1498477 = 561929) (by norm_num)
theorem B1998197 : Blo 1330984 1998197 := bbase (se 5 (by rfl) ⟨93665, by rfl⟩ : syracuseStep 1998197 = 187331) (by norm_num)
theorem B1686901 : Blo 1330984 1686901 := bbase (se 5 (by rfl) ⟨79073, by rfl⟩ : syracuseStep 1686901 = 158147) (by norm_num)
theorem B2997629 : Blo 1330984 2997629 := bbase (se 3 (by rfl) ⟨562055, by rfl⟩ : syracuseStep 2997629 = 1124111) (by norm_num)
theorem B3202429 : Blo 1330984 3202429 := bbase (se 3 (by rfl) ⟨600455, by rfl⟩ : syracuseStep 3202429 = 1200911) (by norm_num)
theorem B1998221 : Blo 1330984 1998221 := bbase (se 3 (by rfl) ⟨374666, by rfl⟩ : syracuseStep 1998221 = 749333) (by norm_num)
theorem B1498513 : Blo 1330984 1498513 := bbase (se 2 (by rfl) ⟨561942, by rfl⟩ : syracuseStep 1498513 = 1123885) (by norm_num)
theorem B1998245 : Blo 1330984 1998245 := bbase (se 4 (by rfl) ⟨187335, by rfl⟩ : syracuseStep 1998245 = 374671) (by norm_num)
theorem B2162093 : Blo 1330984 2162093 := bbase (se 3 (by rfl) ⟨405392, by rfl⟩ : syracuseStep 2162093 = 810785) (by norm_num)
theorem B2276789 : Blo 1330984 2276789 := bbase (se 5 (by rfl) ⟨106724, by rfl⟩ : syracuseStep 2276789 = 213449) (by norm_num)
theorem B1498549 : Blo 1330984 1498549 := bbase (se 5 (by rfl) ⟨70244, by rfl⟩ : syracuseStep 1498549 = 140489) (by norm_num)
theorem B1998269 : Blo 1330984 1998269 := bbase (se 3 (by rfl) ⟨374675, by rfl⟩ : syracuseStep 1998269 = 749351) (by norm_num)
theorem B2997701 : Blo 1330984 2997701 := bbase (se 4 (by rfl) ⟨281034, by rfl⟩ : syracuseStep 2997701 = 562069) (by norm_num)
theorem B1998293 : Blo 1330984 1998293 := bbase (se 7 (by rfl) ⟨23417, by rfl⟩ : syracuseStep 1998293 = 46835) (by norm_num)
theorem B1686997 : Blo 1330984 1686997 := bbase (se 7 (by rfl) ⟨19769, by rfl⟩ : syracuseStep 1686997 = 39539) (by norm_num)
theorem B1498585 : Blo 1330984 1498585 := bbase (se 2 (by rfl) ⟨561969, by rfl⟩ : syracuseStep 1498585 = 1123939) (by norm_num)
theorem B1998317 : Blo 1330984 1998317 := bbase (se 3 (by rfl) ⟨374684, by rfl⟩ : syracuseStep 1998317 = 749369) (by norm_num)
theorem B1498621 : Blo 1330984 1498621 := bbase (se 3 (by rfl) ⟨280991, by rfl⟩ : syracuseStep 1498621 = 561983) (by norm_num)
theorem B1998341 : Blo 1330984 1998341 := bbase (se 4 (by rfl) ⟨187344, by rfl⟩ : syracuseStep 1998341 = 374689) (by norm_num)
theorem B2997773 : Blo 1330984 2997773 := bbase (se 3 (by rfl) ⟨562082, by rfl⟩ : syracuseStep 2997773 = 1124165) (by norm_num)
theorem B1998365 : Blo 1330984 1998365 := bbase (se 3 (by rfl) ⟨374693, by rfl⟩ : syracuseStep 1998365 = 749387) (by norm_num)
theorem B1498657 : Blo 1330984 1498657 := bbase (se 2 (by rfl) ⟨561996, by rfl⟩ : syracuseStep 1498657 = 1123993) (by norm_num)
theorem B1998389 : Blo 1330984 1998389 := bbase (se 5 (by rfl) ⟨93674, by rfl⟩ : syracuseStep 1998389 = 187349) (by norm_num)
theorem B5054021 : Blo 1330984 5054021 := bbase (se 4 (by rfl) ⟨473814, by rfl⟩ : syracuseStep 5054021 = 947629) (by norm_num)
theorem B1498693 : Blo 1330984 1498693 := bbase (se 4 (by rfl) ⟨140502, by rfl⟩ : syracuseStep 1498693 = 281005) (by norm_num)
theorem B1998413 : Blo 1330984 1998413 := bbase (se 3 (by rfl) ⟨374702, by rfl⟩ : syracuseStep 1998413 = 749405) (by norm_num)
theorem B2997845 : Blo 1330984 2997845 := bbase (se 8 (by rfl) ⟨17565, by rfl⟩ : syracuseStep 2997845 = 35131) (by norm_num)
theorem B1998437 : Blo 1330984 1998437 := bbase (se 4 (by rfl) ⟨187353, by rfl⟩ : syracuseStep 1998437 = 374707) (by norm_num)
theorem B1498729 : Blo 1330984 1498729 := bbase (se 2 (by rfl) ⟨562023, by rfl⟩ : syracuseStep 1498729 = 1124047) (by norm_num)
theorem B1998461 : Blo 1330984 1998461 := bbase (se 3 (by rfl) ⟨374711, by rfl⟩ : syracuseStep 1998461 = 749423) (by norm_num)
theorem B1498765 : Blo 1330984 1498765 := bbase (se 3 (by rfl) ⟨281018, by rfl⟩ : syracuseStep 1498765 = 562037) (by norm_num)
theorem B1998485 : Blo 1330984 1998485 := bbase (se 6 (by rfl) ⟨46839, by rfl⟩ : syracuseStep 1998485 = 93679) (by norm_num)
theorem B25960085 : Blo 1330984 25960085 := bbase (se 6 (by rfl) ⟨608439, by rfl⟩ : syracuseStep 25960085 = 1216879) (by norm_num)
theorem B2997917 : Blo 1330984 2997917 := bbase (se 3 (by rfl) ⟨562109, by rfl⟩ : syracuseStep 2997917 = 1124219) (by norm_num)
theorem B1998509 : Blo 1330984 1998509 := bbase (se 3 (by rfl) ⟨374720, by rfl⟩ : syracuseStep 1998509 = 749441) (by norm_num)
theorem B1498801 : Blo 1330984 1498801 := bbase (se 2 (by rfl) ⟨562050, by rfl⟩ : syracuseStep 1498801 = 1124101) (by norm_num)
theorem B1998533 : Blo 1330984 1998533 := bbase (se 4 (by rfl) ⟨187362, by rfl⟩ : syracuseStep 1998533 = 374725) (by norm_num)
theorem B1498837 : Blo 1330984 1498837 := bbase (se 7 (by rfl) ⟨17564, by rfl⟩ : syracuseStep 1498837 = 35129) (by norm_num)
theorem B1998557 : Blo 1330984 1998557 := bbase (se 3 (by rfl) ⟨374729, by rfl⟩ : syracuseStep 1998557 = 749459) (by norm_num)
theorem B2997989 : Blo 1330984 2997989 := bbase (se 4 (by rfl) ⟨281061, by rfl⟩ : syracuseStep 2997989 = 562123) (by norm_num)
theorem B1998581 : Blo 1330984 1998581 := bbase (se 5 (by rfl) ⟨93683, by rfl⟩ : syracuseStep 1998581 = 187367) (by norm_num)
theorem B1498873 : Blo 1330984 1498873 := bbase (se 2 (by rfl) ⟨562077, by rfl⟩ : syracuseStep 1498873 = 1124155) (by norm_num)
theorem B1998605 : Blo 1330984 1998605 := bbase (se 3 (by rfl) ⟨374738, by rfl⟩ : syracuseStep 1998605 = 749477) (by norm_num)
theorem B4497173 : Blo 1330984 4497173 := bbase (se 6 (by rfl) ⟨105402, by rfl⟩ : syracuseStep 4497173 = 210805) (by norm_num)
theorem B1498909 : Blo 1330984 1498909 := bbase (se 3 (by rfl) ⟨281045, by rfl⟩ : syracuseStep 1498909 = 562091) (by norm_num)
theorem B1998629 : Blo 1330984 1998629 := bbase (se 4 (by rfl) ⟨187371, by rfl⟩ : syracuseStep 1998629 = 374743) (by norm_num)
theorem B2998061 : Blo 1330984 2998061 := bbase (se 3 (by rfl) ⟨562136, by rfl⟩ : syracuseStep 2998061 = 1124273) (by norm_num)
theorem B4267829 : Blo 1330984 4267829 := bbase (se 5 (by rfl) ⟨200054, by rfl⟩ : syracuseStep 4267829 = 400109) (by norm_num)
theorem B1998653 : Blo 1330984 1998653 := bbase (se 3 (by rfl) ⟨374747, by rfl⟩ : syracuseStep 1998653 = 749495) (by norm_num)
theorem B1498945 : Blo 1330984 1498945 := bbase (se 2 (by rfl) ⟨562104, by rfl⟩ : syracuseStep 1498945 = 1124209) (by norm_num)
theorem B2400077 : Blo 1330984 2400077 := bbase (se 3 (by rfl) ⟨450014, by rfl⟩ : syracuseStep 2400077 = 900029) (by norm_num)
theorem B1998677 : Blo 1330984 1998677 := bbase (se 9 (by rfl) ⟨5855, by rfl⟩ : syracuseStep 1998677 = 11711) (by norm_num)
theorem B5054309 : Blo 1330984 5054309 := bbase (se 4 (by rfl) ⟨473841, by rfl⟩ : syracuseStep 5054309 = 947683) (by norm_num)
theorem B1498981 : Blo 1330984 1498981 := bbase (se 4 (by rfl) ⟨140529, by rfl⟩ : syracuseStep 1498981 = 281059) (by norm_num)
theorem B1998701 : Blo 1330984 1998701 := bbase (se 3 (by rfl) ⟨374756, by rfl⟩ : syracuseStep 1998701 = 749513) (by norm_num)
theorem B2998133 : Blo 1330984 2998133 := bbase (se 5 (by rfl) ⟨140537, by rfl⟩ : syracuseStep 2998133 = 281075) (by norm_num)
theorem B1441669 : Blo 1330984 1441669 := bbase (se 4 (by rfl) ⟨135156, by rfl⟩ : syracuseStep 1441669 = 270313) (by norm_num)
theorem B1998725 : Blo 1330984 1998725 := bbase (se 4 (by rfl) ⟨187380, by rfl⟩ : syracuseStep 1998725 = 374761) (by norm_num)
theorem B1499017 : Blo 1330984 1499017 := bbase (se 2 (by rfl) ⟨562131, by rfl⟩ : syracuseStep 1499017 = 1124263) (by norm_num)
theorem B1998749 : Blo 1330984 1998749 := bbase (se 3 (by rfl) ⟨374765, by rfl⟩ : syracuseStep 1998749 = 749531) (by norm_num)
theorem B1499053 : Blo 1330984 1499053 := bbase (se 3 (by rfl) ⟨281072, by rfl⟩ : syracuseStep 1499053 = 562145) (by norm_num)
theorem B1998773 : Blo 1330984 1998773 := bbase (se 5 (by rfl) ⟨93692, by rfl⟩ : syracuseStep 1998773 = 187385) (by norm_num)
theorem B2998205 : Blo 1330984 2998205 := bbase (se 3 (by rfl) ⟨562163, by rfl⟩ : syracuseStep 2998205 = 1124327) (by norm_num)
theorem B5767109 : Blo 1330984 5767109 := bbase (se 4 (by rfl) ⟨540666, by rfl⟩ : syracuseStep 5767109 = 1081333) (by norm_num)
theorem B1998797 : Blo 1330984 1998797 := bbase (se 3 (by rfl) ⟨374774, by rfl⟩ : syracuseStep 1998797 = 749549) (by norm_num)
theorem B1499089 : Blo 1330984 1499089 := bbase (se 2 (by rfl) ⟨562158, by rfl⟩ : syracuseStep 1499089 = 1124317) (by norm_num)
theorem B1998821 : Blo 1330984 1998821 := bbase (se 4 (by rfl) ⟨187389, by rfl⟩ : syracuseStep 1998821 = 374779) (by norm_num)
theorem B1499125 : Blo 1330984 1499125 := bbase (se 5 (by rfl) ⟨70271, by rfl⟩ : syracuseStep 1499125 = 140543) (by norm_num)
theorem B5693429 : Blo 1330984 5693429 := bbase (se 5 (by rfl) ⟨266879, by rfl⟩ : syracuseStep 5693429 = 533759) (by norm_num)
theorem B1998851 : Blo 1330984 1998851 := bstep (se 1 (by rfl) ⟨1499138, by rfl⟩ : syracuseStep 1998851 = 2998277) B2998277
theorem B1998881 : Blo 1330984 1998881 := bstep (se 2 (by rfl) ⟨749580, by rfl⟩ : syracuseStep 1998881 = 1499161) B1499161
theorem B4497443 : Blo 1330984 4497443 := bstep (se 1 (by rfl) ⟨3373082, by rfl⟩ : syracuseStep 4497443 = 6746165) B6746165
theorem B1998899 : Blo 1330984 1998899 := bstep (se 1 (by rfl) ⟨1499174, by rfl⟩ : syracuseStep 1998899 = 2998349) B2998349
theorem B3792977 : Blo 1330984 3792977 := bstep (se 2 (by rfl) ⟨1422366, by rfl⟩ : syracuseStep 3792977 = 2844733) B2844733
theorem B1998929 : Blo 1330984 1998929 := bstep (se 2 (by rfl) ⟨749598, by rfl⟩ : syracuseStep 1998929 = 1499197) B1499197
theorem B6742115 : Blo 1330984 6742115 := bstep (se 1 (by rfl) ⟨5056586, by rfl⟩ : syracuseStep 6742115 = 10113173) B10113173
theorem B1998947 : Blo 1330984 1998947 := bstep (se 1 (by rfl) ⟨1499210, by rfl⟩ : syracuseStep 1998947 = 2998421) B2998421
theorem B2998385 : Blo 1330984 2998385 := bstep (se 2 (by rfl) ⟨1124394, by rfl⟩ : syracuseStep 2998385 = 2248789) B2248789
theorem B1499251 : Blo 1330984 1499251 := bstep (se 1 (by rfl) ⟨1124438, by rfl⟩ : syracuseStep 1499251 = 2248877) B2248877
theorem B1998977 : Blo 1330984 1998977 := bstep (se 2 (by rfl) ⟨749616, by rfl⟩ : syracuseStep 1998977 = 1499233) B1499233
theorem B2998403 : Blo 1330984 2998403 := bstep (se 1 (by rfl) ⟨2248802, by rfl⟩ : syracuseStep 2998403 = 4497605) B4497605
theorem B5693581 : Blo 1330984 5693581 := bstep (se 3 (by rfl) ⟨1067546, by rfl⟩ : syracuseStep 5693581 = 2135093) B2135093
theorem B1998995 : Blo 1330984 1998995 := bstep (se 1 (by rfl) ⟨1499246, by rfl⟩ : syracuseStep 1998995 = 2998493) B2998493
theorem B6398129 : Blo 1330984 6398129 := bstep (se 2 (by rfl) ⟨2399298, by rfl⟩ : syracuseStep 6398129 = 4798597) B4798597
theorem B1999025 : Blo 1330984 1999025 := bstep (se 2 (by rfl) ⟨749634, by rfl⟩ : syracuseStep 1999025 = 1499269) B1499269
theorem B4268227 : Blo 1330984 4268227 := bstep (se 1 (by rfl) ⟨3201170, by rfl⟩ : syracuseStep 4268227 = 6402341) B6402341
theorem B1999043 : Blo 1330984 1999043 := bstep (se 1 (by rfl) ⟨1499282, by rfl⟩ : syracuseStep 1999043 = 2998565) B2998565
theorem B5128397 : Blo 1330984 5128397 := bstep (se 3 (by rfl) ⟨961574, by rfl⟩ : syracuseStep 5128397 = 1923149) B1923149
theorem B1999073 : Blo 1330984 1999073 := bstep (se 2 (by rfl) ⟨749652, by rfl⟩ : syracuseStep 1999073 = 1499305) B1499305
theorem B1999091 : Blo 1330984 1999091 := bstep (se 1 (by rfl) ⟨1499318, by rfl⟩ : syracuseStep 1999091 = 2998637) B2998637
theorem B1499395 : Blo 1330984 1499395 := bstep (se 1 (by rfl) ⟨1124546, by rfl⟩ : syracuseStep 1499395 = 2249093) B2249093
theorem B3793169 : Blo 1330984 3793169 := bstep (se 2 (by rfl) ⟨1422438, by rfl⟩ : syracuseStep 3793169 = 2844877) B2844877
theorem B1999121 : Blo 1330984 1999121 := bstep (se 2 (by rfl) ⟨749670, by rfl⟩ : syracuseStep 1999121 = 1499341) B1499341
theorem B1999139 : Blo 1330984 1999139 := bstep (se 1 (by rfl) ⟨1499354, by rfl⟩ : syracuseStep 1999139 = 2998709) B2998709
theorem B4497713 : Blo 1330984 4497713 := bstep (se 2 (by rfl) ⟨1686642, by rfl⟩ : syracuseStep 4497713 = 3373285) B3373285
theorem B1999169 : Blo 1330984 1999169 := bstep (se 2 (by rfl) ⟨749688, by rfl⟩ : syracuseStep 1999169 = 1499377) B1499377
theorem B1999187 : Blo 1330984 1999187 := bstep (se 1 (by rfl) ⟨1499390, by rfl⟩ : syracuseStep 1999187 = 2998781) B2998781
theorem B1622371 : Blo 1330984 1622371 := bstep (se 1 (by rfl) ⟨1216778, by rfl⟩ : syracuseStep 1622371 = 2433557) B2433557
theorem B1999217 : Blo 1330984 1999217 := bstep (se 2 (by rfl) ⟨749706, by rfl⟩ : syracuseStep 1999217 = 1499413) B1499413
theorem B1999235 : Blo 1330984 1999235 := bstep (se 1 (by rfl) ⟨1499426, by rfl⟩ : syracuseStep 1999235 = 2998853) B2998853
theorem B2998673 : Blo 1330984 2998673 := bstep (se 2 (by rfl) ⟨1124502, by rfl⟩ : syracuseStep 2998673 = 2249005) B2249005
theorem B1499539 : Blo 1330984 1499539 := bstep (se 1 (by rfl) ⟨1124654, by rfl⟩ : syracuseStep 1499539 = 2249309) B2249309
theorem B1999265 : Blo 1330984 1999265 := bstep (se 2 (by rfl) ⟨749724, by rfl⟩ : syracuseStep 1999265 = 1499449) B1499449
theorem B2998691 : Blo 1330984 2998691 := bstep (se 1 (by rfl) ⟨2249018, by rfl⟩ : syracuseStep 2998691 = 4498037) B4498037
theorem B3244465 : Blo 1330984 3244465 := bstep (se 2 (by rfl) ⟨1216674, by rfl⟩ : syracuseStep 3244465 = 2433349) B2433349
theorem B1999283 : Blo 1330984 1999283 := bstep (se 1 (by rfl) ⟨1499462, by rfl⟩ : syracuseStep 1999283 = 2998925) B2998925
theorem B1622467 : Blo 1330984 1622467 := bstep (se 1 (by rfl) ⟨1216850, by rfl⟩ : syracuseStep 1622467 = 2433701) B2433701
theorem B1999313 : Blo 1330984 1999313 := bstep (se 2 (by rfl) ⟨749742, by rfl⟩ : syracuseStep 1999313 = 1499485) B1499485
theorem B1999331 : Blo 1330984 1999331 := bstep (se 1 (by rfl) ⟨1499498, by rfl⟩ : syracuseStep 1999331 = 2998997) B2998997
theorem B1999361 : Blo 1330984 1999361 := bstep (se 2 (by rfl) ⟨749760, by rfl⟩ : syracuseStep 1999361 = 1499521) B1499521
theorem B1999379 : Blo 1330984 1999379 := bstep (se 1 (by rfl) ⟨1499534, by rfl⟩ : syracuseStep 1999379 = 2999069) B2999069
theorem B1999409 : Blo 1330984 1999409 := bstep (se 2 (by rfl) ⟨749778, by rfl⟩ : syracuseStep 1999409 = 1499557) B1499557
theorem B2843203 : Blo 1330984 2843203 := bstep (se 1 (by rfl) ⟨2132402, by rfl⟩ : syracuseStep 2843203 = 4264805) B4264805
theorem B1999427 : Blo 1330984 1999427 := bstep (se 1 (by rfl) ⟨1499570, by rfl⟩ : syracuseStep 1999427 = 2999141) B2999141
theorem B1999457 : Blo 1330984 1999457 := bstep (se 2 (by rfl) ⟨749796, by rfl⟩ : syracuseStep 1999457 = 1499593) B1499593
theorem B1999475 : Blo 1330984 1999475 := bstep (se 1 (by rfl) ⟨1499606, by rfl⟩ : syracuseStep 1999475 = 2999213) B2999213
theorem B2400899 : Blo 1330984 2400899 := bstep (se 1 (by rfl) ⟨1800674, by rfl⟩ : syracuseStep 2400899 = 3601349) B3601349
theorem B4268675 : Blo 1330984 4268675 := bstep (se 1 (by rfl) ⟨3201506, by rfl⟩ : syracuseStep 4268675 = 6403013) B6403013
theorem B9241229 : Blo 1330984 9241229 := bstep (se 3 (by rfl) ⟨1732730, by rfl⟩ : syracuseStep 9241229 = 3465461) B3465461
theorem B2998961 : Blo 1330984 2998961 := bstep (se 2 (by rfl) ⟨1124610, by rfl⟩ : syracuseStep 2998961 = 2249221) B2249221
theorem B2998979 : Blo 1330984 2998979 := bstep (se 1 (by rfl) ⟨2249234, by rfl⟩ : syracuseStep 2998979 = 4498469) B4498469
theorem B2278145 : Blo 1330984 2278145 := bstep (se 2 (by rfl) ⟨854304, by rfl⟩ : syracuseStep 2278145 = 1708609) B1708609
theorem B5055281 : Blo 1330984 5055281 := bstep (se 2 (by rfl) ⟨1895730, by rfl⟩ : syracuseStep 5055281 = 3791461) B3791461
theorem B4498253 : Blo 1330984 4498253 := bstep (se 3 (by rfl) ⟨843422, by rfl⟩ : syracuseStep 4498253 = 1686845) B1686845
theorem B4498307 : Blo 1330984 4498307 := bstep (se 1 (by rfl) ⟨3373730, by rfl⟩ : syracuseStep 4498307 = 6747461) B6747461
theorem B6742925 : Blo 1330984 6742925 := bstep (se 3 (by rfl) ⟨1264298, by rfl⟩ : syracuseStep 6742925 = 2528597) B2528597
theorem B2737091 : Blo 1330984 2737091 := bstep (se 1 (by rfl) ⟨2052818, by rfl⟩ : syracuseStep 2737091 = 4105637) B4105637
theorem B5686321 : Blo 1330984 5686321 := bstep (se 2 (by rfl) ⟨2132370, by rfl⟩ : syracuseStep 5686321 = 4264741) B4264741
theorem B7586885 : Blo 1330984 7586885 := bstep (se 4 (by rfl) ⟨711270, by rfl⟩ : syracuseStep 7586885 = 1422541) B1422541
theorem B2163809 : Blo 1330984 2163809 := bstep (se 2 (by rfl) ⟨811428, by rfl⟩ : syracuseStep 2163809 = 1622857) B1622857
theorem B12797027 : Blo 1330984 12797027 := bstep (se 1 (by rfl) ⟨9597770, by rfl⟩ : syracuseStep 12797027 = 19195541) B19195541
theorem B25937009 : Blo 1330984 25937009 := bstep (se 2 (by rfl) ⟨9726378, by rfl⟩ : syracuseStep 25937009 = 19452757) B19452757
theorem B6071437 : Blo 1330984 6071437 := bstep (se 3 (by rfl) ⟨1138394, by rfl⟩ : syracuseStep 6071437 = 2276789) B2276789
theorem B4498577 : Blo 1330984 4498577 := bstep (se 2 (by rfl) ⟨1686966, by rfl⟩ : syracuseStep 4498577 = 3373933) B3373933
theorem B15164657 : Blo 1330984 15164657 := bstep (se 2 (by rfl) ⟨5686746, by rfl⟩ : syracuseStep 15164657 = 11373493) B11373493
theorem B8209649 : Blo 1330984 8209649 := bstep (se 2 (by rfl) ⟨3078618, by rfl⟩ : syracuseStep 8209649 = 6157237) B6157237
theorem B3794161 : Blo 1330984 3794161 := bstep (se 2 (by rfl) ⟨1422810, by rfl⟩ : syracuseStep 3794161 = 2845621) B2845621
theorem B6489379 : Blo 1330984 6489379 := bstep (se 1 (by rfl) ⟨4867034, by rfl⟩ : syracuseStep 6489379 = 9734069) B9734069
theorem B27329845 : Blo 1330984 27329845 := bstep (se 5 (by rfl) ⟨1281086, by rfl⟩ : syracuseStep 27329845 = 2562173) B2562173
theorem B3794435 : Blo 1330984 3794435 := bstep (se 1 (by rfl) ⟨2845826, by rfl⟩ : syracuseStep 3794435 = 5691653) B5691653
theorem B7587341 : Blo 1330984 7587341 := bstep (se 3 (by rfl) ⟨1422626, by rfl⟩ : syracuseStep 7587341 = 2845253) B2845253
theorem B2246177 : Blo 1330984 2246177 := bstep (se 2 (by rfl) ⟨842316, by rfl⟩ : syracuseStep 2246177 = 1684633) B1684633
theorem B3417731 : Blo 1330984 3417731 := bstep (se 1 (by rfl) ⟨2563298, by rfl⟩ : syracuseStep 3417731 = 5126597) B5126597
theorem B2246305 : Blo 1330984 2246305 := bstep (se 2 (by rfl) ⟨842364, by rfl⟩ : syracuseStep 2246305 = 1684729) B1684729
theorem B1599139 : Blo 1330984 1599139 := bstep (se 1 (by rfl) ⟨1199354, by rfl⟩ : syracuseStep 1599139 = 2398709) B2398709
theorem B2246339 : Blo 1330984 2246339 := bstep (se 1 (by rfl) ⟨1684754, by rfl⟩ : syracuseStep 2246339 = 3369509) B3369509
theorem B3794627 : Blo 1330984 3794627 := bstep (se 1 (by rfl) ⟨2845970, by rfl⟩ : syracuseStep 3794627 = 5691941) B5691941
theorem B14411533 : Blo 1330984 14411533 := bstep (se 3 (by rfl) ⟨2702162, by rfl⟩ : syracuseStep 14411533 = 5404325) B5404325
theorem B2844433 : Blo 1330984 2844433 := bstep (se 2 (by rfl) ⟨1066662, by rfl⟩ : syracuseStep 2844433 = 2133325) B2133325
theorem B23062325 : Blo 1330984 23062325 := bstep (se 5 (by rfl) ⟨1081046, by rfl⟩ : syracuseStep 23062325 = 2162093) B2162093
theorem B2246467 : Blo 1330984 2246467 := bstep (se 1 (by rfl) ⟨1684850, by rfl⟩ : syracuseStep 2246467 = 3369701) B3369701
theorem B4269905 : Blo 1330984 4269905 := bstep (se 2 (by rfl) ⟨1601214, by rfl⟩ : syracuseStep 4269905 = 3202429) B3202429
theorem B2246609 : Blo 1330984 2246609 := bstep (se 2 (by rfl) ⟨842478, by rfl⟩ : syracuseStep 2246609 = 1684957) B1684957
theorem B1599475 : Blo 1330984 1599475 := bstep (se 1 (by rfl) ⟨1199606, by rfl⟩ : syracuseStep 1599475 = 2399213) B2399213
theorem B2246737 : Blo 1330984 2246737 := bstep (se 2 (by rfl) ⟨842526, by rfl⟩ : syracuseStep 2246737 = 1685053) B1685053
theorem B8530019 : Blo 1330984 8530019 := bstep (se 1 (by rfl) ⟨6397514, by rfl⟩ : syracuseStep 8530019 = 12795029) B12795029
theorem B3369073 : Blo 1330984 3369073 := bstep (se 2 (by rfl) ⟨1263402, by rfl⟩ : syracuseStep 3369073 = 2526805) B2526805
theorem B2246771 : Blo 1330984 2246771 := bstep (se 1 (by rfl) ⟨1685078, by rfl⟩ : syracuseStep 2246771 = 3370157) B3370157
theorem B6400205 : Blo 1330984 6400205 := bstep (se 3 (by rfl) ⟨1200038, by rfl⟩ : syracuseStep 6400205 = 2400077) B2400077
theorem B5056739 : Blo 1330984 5056739 := bstep (se 1 (by rfl) ⟨3792554, by rfl⟩ : syracuseStep 5056739 = 7585109) B7585109
theorem B2246899 : Blo 1330984 2246899 := bstep (se 1 (by rfl) ⟨1685174, by rfl⟩ : syracuseStep 2246899 = 3370349) B3370349
theorem B2247041 : Blo 1330984 2247041 := bstep (se 2 (by rfl) ⟨842640, by rfl⟩ : syracuseStep 2247041 = 1685281) B1685281
theorem B2025857 : Blo 1330984 2025857 := bstep (se 2 (by rfl) ⟨759696, by rfl⟩ : syracuseStep 2025857 = 1519393) B1519393
theorem B3369347 : Blo 1330984 3369347 := bstep (se 1 (by rfl) ⟨2527010, by rfl⟩ : syracuseStep 3369347 = 5054021) B5054021
theorem B3795437 : Blo 1330984 3795437 := bstep (se 3 (by rfl) ⟨711644, by rfl⟩ : syracuseStep 3795437 = 1423289) B1423289
theorem B2247169 : Blo 1330984 2247169 := bstep (se 2 (by rfl) ⟨842688, by rfl⟩ : syracuseStep 2247169 = 1685377) B1685377
theorem B2247203 : Blo 1330984 2247203 := bstep (se 1 (by rfl) ⟨1685402, by rfl⟩ : syracuseStep 2247203 = 3370805) B3370805
theorem B2845219 : Blo 1330984 2845219 := bstep (se 1 (by rfl) ⟨2133914, by rfl⟩ : syracuseStep 2845219 = 4267829) B4267829
theorem B3369539 : Blo 1330984 3369539 := bstep (se 1 (by rfl) ⟨2527154, by rfl⟩ : syracuseStep 3369539 = 5054309) B5054309
theorem B3844739 : Blo 1330984 3844739 := bstep (se 1 (by rfl) ⟨2883554, by rfl⟩ : syracuseStep 3844739 = 5767109) B5767109
theorem B2247331 : Blo 1330984 2247331 := bstep (se 1 (by rfl) ⟨1685498, by rfl⟩ : syracuseStep 2247331 = 3370997) B3370997
theorem B3795619 : Blo 1330984 3795619 := bstep (se 1 (by rfl) ⟨2846714, by rfl⟩ : syracuseStep 3795619 = 5693429) B5693429
theorem B2132659 : Blo 1330984 2132659 := bstep (se 1 (by rfl) ⟨1599494, by rfl⟩ : syracuseStep 2132659 = 3198989) B3198989
theorem B10111715 : Blo 1330984 10111715 := bstep (se 1 (by rfl) ⟨7583786, by rfl⟩ : syracuseStep 10111715 = 15167573) B15167573
theorem B9112333 : Blo 1330984 9112333 := bstep (se 3 (by rfl) ⟨1708562, by rfl⟩ : syracuseStep 9112333 = 3417125) B3417125
theorem B12151565 : Blo 1330984 12151565 := bstep (se 3 (by rfl) ⟨2278418, by rfl⟩ : syracuseStep 12151565 = 4556837) B4556837
theorem B2247473 : Blo 1330984 2247473 := bstep (se 2 (by rfl) ⟨842802, by rfl⟩ : syracuseStep 2247473 = 1685605) B1685605
theorem B2026307 : Blo 1330984 2026307 := bstep (se 1 (by rfl) ⟨1519730, by rfl⟩ : syracuseStep 2026307 = 3039461) B3039461
theorem B12487493 : Blo 1330984 12487493 := bstep (se 4 (by rfl) ⟨1170702, by rfl⟩ : syracuseStep 12487493 = 2341405) B2341405
theorem B4492205 : Blo 1330984 4492205 := bstep (se 3 (by rfl) ⟨842288, by rfl⟩ : syracuseStep 4492205 = 1684577) B1684577
theorem B2247601 : Blo 1330984 2247601 := bstep (se 2 (by rfl) ⟨842850, by rfl⟩ : syracuseStep 2247601 = 1685701) B1685701
theorem B2247635 : Blo 1330984 2247635 := bstep (se 1 (by rfl) ⟨1685726, by rfl⟩ : syracuseStep 2247635 = 3371453) B3371453
theorem B4492259 : Blo 1330984 4492259 := bstep (se 1 (by rfl) ⟨3369194, by rfl⟩ : syracuseStep 4492259 = 6738389) B6738389
theorem B1895395 : Blo 1330984 1895395 := bstep (se 1 (by rfl) ⟨1421546, by rfl⟩ : syracuseStep 1895395 = 2843093) B2843093
theorem B1895491 : Blo 1330984 1895491 := bstep (se 1 (by rfl) ⟨1421618, by rfl⟩ : syracuseStep 1895491 = 2843237) B2843237
theorem B2247763 : Blo 1330984 2247763 := bstep (se 1 (by rfl) ⟨1685822, by rfl⟩ : syracuseStep 2247763 = 3371645) B3371645
theorem B5057741 : Blo 1330984 5057741 := bstep (se 3 (by rfl) ⟨948326, by rfl⟩ : syracuseStep 5057741 = 1896653) B1896653
theorem B2247905 : Blo 1330984 2247905 := bstep (se 2 (by rfl) ⟨842964, by rfl⟩ : syracuseStep 2247905 = 1685929) B1685929
theorem B3599597 : Blo 1330984 3599597 := bstep (se 3 (by rfl) ⟨674924, by rfl⟩ : syracuseStep 3599597 = 1349849) B1349849
theorem B4050157 : Blo 1330984 4050157 := bstep (se 3 (by rfl) ⟨759404, by rfl⟩ : syracuseStep 4050157 = 1518809) B1518809
theorem B4492529 : Blo 1330984 4492529 := bstep (se 2 (by rfl) ⟨1684698, by rfl⟩ : syracuseStep 4492529 = 3369397) B3369397
theorem B2845937 : Blo 1330984 2845937 := bstep (se 2 (by rfl) ⟨1067226, by rfl⟩ : syracuseStep 2845937 = 2134453) B2134453
theorem B7204081 : Blo 1330984 7204081 := bstep (se 2 (by rfl) ⟨2701530, by rfl⟩ : syracuseStep 7204081 = 5403061) B5403061
theorem B2248033 : Blo 1330984 2248033 := bstep (se 2 (by rfl) ⟨843012, by rfl⟩ : syracuseStep 2248033 = 1686025) B1686025
theorem B2248067 : Blo 1330984 2248067 := bstep (se 1 (by rfl) ⟨1686050, by rfl⟩ : syracuseStep 2248067 = 3372101) B3372101
theorem B3599761 : Blo 1330984 3599761 := bstep (se 2 (by rfl) ⟨1349910, by rfl⟩ : syracuseStep 3599761 = 2699821) B2699821
theorem B8531405 : Blo 1330984 8531405 := bstep (se 3 (by rfl) ⟨1599638, by rfl⟩ : syracuseStep 8531405 = 3199277) B3199277
theorem B3370481 : Blo 1330984 3370481 := bstep (se 2 (by rfl) ⟨1263930, by rfl⟩ : syracuseStep 3370481 = 2527861) B2527861
theorem B2248195 : Blo 1330984 2248195 := bstep (se 1 (by rfl) ⟨1686146, by rfl⟩ : syracuseStep 2248195 = 3372293) B3372293
theorem B3370531 : Blo 1330984 3370531 := bstep (se 1 (by rfl) ⟨2527898, by rfl⟩ : syracuseStep 3370531 = 5055797) B5055797
theorem B1895987 : Blo 1330984 1895987 := bstep (se 1 (by rfl) ⟨1421990, by rfl⟩ : syracuseStep 1895987 = 2843981) B2843981
theorem B2526851 : Blo 1330984 2526851 := bstep (se 1 (by rfl) ⟨1895138, by rfl⟩ : syracuseStep 2526851 = 3790277) B3790277
theorem B2248337 : Blo 1330984 2248337 := bstep (se 2 (by rfl) ⟨843126, by rfl⟩ : syracuseStep 2248337 = 1686253) B1686253
theorem B3370673 : Blo 1330984 3370673 := bstep (se 2 (by rfl) ⟨1264002, by rfl⟩ : syracuseStep 3370673 = 2528005) B2528005
theorem B6745841 : Blo 1330984 6745841 := bstep (se 2 (by rfl) ⟨2529690, by rfl⟩ : syracuseStep 6745841 = 5059381) B5059381
theorem B2846449 : Blo 1330984 2846449 := bstep (se 2 (by rfl) ⟨1067418, by rfl⟩ : syracuseStep 2846449 = 2134837) B2134837
theorem B4493069 : Blo 1330984 4493069 := bstep (se 3 (by rfl) ⟨842450, by rfl⟩ : syracuseStep 4493069 = 1684901) B1684901
theorem B2248465 : Blo 1330984 2248465 := bstep (se 2 (by rfl) ⟨843174, by rfl⟩ : syracuseStep 2248465 = 1686349) B1686349
theorem B1330995 : Blo 1330984 1330995 := bstep (se 1 (by rfl) ⟨998246, by rfl⟩ : syracuseStep 1330995 = 1996493) B1996493
theorem B2248499 : Blo 1330984 2248499 := bstep (se 1 (by rfl) ⟨1686374, by rfl⟩ : syracuseStep 2248499 = 3372749) B3372749
theorem B1331011 : Blo 1330984 1331011 := bstep (se 1 (by rfl) ⟨998258, by rfl⟩ : syracuseStep 1331011 = 1996517) B1996517
theorem B4493123 : Blo 1330984 4493123 := bstep (se 1 (by rfl) ⟨3369842, by rfl⟩ : syracuseStep 4493123 = 6739685) B6739685
theorem B7581509 : Blo 1330984 7581509 := bstep (se 4 (by rfl) ⟨710766, by rfl⟩ : syracuseStep 7581509 = 1421533) B1421533
theorem B1331027 : Blo 1330984 1331027 := bstep (se 1 (by rfl) ⟨998270, by rfl⟩ : syracuseStep 1331027 = 1996541) B1996541
theorem B1331043 : Blo 1330984 1331043 := bstep (se 1 (by rfl) ⟨998282, by rfl⟩ : syracuseStep 1331043 = 1996565) B1996565
theorem B1331059 : Blo 1330984 1331059 := bstep (se 1 (by rfl) ⟨998294, by rfl⟩ : syracuseStep 1331059 = 1996589) B1996589
theorem B1331075 : Blo 1330984 1331075 := bstep (se 1 (by rfl) ⟨998306, by rfl⟩ : syracuseStep 1331075 = 1996613) B1996613
theorem B1707907 : Blo 1330984 1707907 := bstep (se 1 (by rfl) ⟨1280930, by rfl⟩ : syracuseStep 1707907 = 2561861) B2561861
theorem B1331091 : Blo 1330984 1331091 := bstep (se 1 (by rfl) ⟨998318, by rfl⟩ : syracuseStep 1331091 = 1996637) B1996637
theorem B1331107 : Blo 1330984 1331107 := bstep (se 1 (by rfl) ⟨998330, by rfl⟩ : syracuseStep 1331107 = 1996661) B1996661
theorem B2527139 : Blo 1330984 2527139 := bstep (se 1 (by rfl) ⟨1895354, by rfl⟩ : syracuseStep 2527139 = 3790709) B3790709
theorem B1331123 : Blo 1330984 1331123 := bstep (se 1 (by rfl) ⟨998342, by rfl⟩ : syracuseStep 1331123 = 1996685) B1996685
theorem B2248627 : Blo 1330984 2248627 := bstep (se 1 (by rfl) ⟨1686470, by rfl⟩ : syracuseStep 2248627 = 3372941) B3372941
theorem B1331139 : Blo 1330984 1331139 := bstep (se 1 (by rfl) ⟨998354, by rfl⟩ : syracuseStep 1331139 = 1996709) B1996709
theorem B1331155 : Blo 1330984 1331155 := bstep (se 1 (by rfl) ⟨998366, by rfl⟩ : syracuseStep 1331155 = 1996733) B1996733
theorem B1331171 : Blo 1330984 1331171 := bstep (se 1 (by rfl) ⟨998378, by rfl⟩ : syracuseStep 1331171 = 1996757) B1996757
theorem B1331187 : Blo 1330984 1331187 := bstep (se 1 (by rfl) ⟨998390, by rfl⟩ : syracuseStep 1331187 = 1996781) B1996781
theorem B1331203 : Blo 1330984 1331203 := bstep (se 1 (by rfl) ⟨998402, by rfl⟩ : syracuseStep 1331203 = 1996805) B1996805
theorem B1331219 : Blo 1330984 1331219 := bstep (se 1 (by rfl) ⟨998414, by rfl⟩ : syracuseStep 1331219 = 1996829) B1996829
theorem B34156565 : Blo 1330984 34156565 := bstep (se 6 (by rfl) ⟨800544, by rfl⟩ : syracuseStep 34156565 = 1601089) B1601089
theorem B1331235 : Blo 1330984 1331235 := bstep (se 1 (by rfl) ⟨998426, by rfl⟩ : syracuseStep 1331235 = 1996853) B1996853
theorem B5689379 : Blo 1330984 5689379 := bstep (se 1 (by rfl) ⟨4267034, by rfl⟩ : syracuseStep 5689379 = 8534069) B8534069
theorem B1331251 : Blo 1330984 1331251 := bstep (se 1 (by rfl) ⟨998438, by rfl⟩ : syracuseStep 1331251 = 1996877) B1996877
theorem B2248769 : Blo 1330984 2248769 := bstep (se 2 (by rfl) ⟨843288, by rfl⟩ : syracuseStep 2248769 = 1686577) B1686577
theorem B1331267 : Blo 1330984 1331267 := bstep (se 1 (by rfl) ⟨998450, by rfl⟩ : syracuseStep 1331267 = 1996901) B1996901
theorem B4493393 : Blo 1330984 4493393 := bstep (se 2 (by rfl) ⟨1685022, by rfl⟩ : syracuseStep 4493393 = 3370045) B3370045
theorem B1331283 : Blo 1330984 1331283 := bstep (se 1 (by rfl) ⟨998462, by rfl⟩ : syracuseStep 1331283 = 1996925) B1996925
theorem B1331299 : Blo 1330984 1331299 := bstep (se 1 (by rfl) ⟨998474, by rfl⟩ : syracuseStep 1331299 = 1996949) B1996949
theorem B1331315 : Blo 1330984 1331315 := bstep (se 1 (by rfl) ⟨998486, by rfl⟩ : syracuseStep 1331315 = 1996973) B1996973
theorem B2134145 : Blo 1330984 2134145 := bstep (se 2 (by rfl) ⟨800304, by rfl⟩ : syracuseStep 2134145 = 1600609) B1600609
theorem B1331331 : Blo 1330984 1331331 := bstep (se 1 (by rfl) ⟨998498, by rfl⟩ : syracuseStep 1331331 = 1996997) B1996997
theorem B1331347 : Blo 1330984 1331347 := bstep (se 1 (by rfl) ⟨998510, by rfl⟩ : syracuseStep 1331347 = 1997021) B1997021
theorem B1331363 : Blo 1330984 1331363 := bstep (se 1 (by rfl) ⟨998522, by rfl⟩ : syracuseStep 1331363 = 1997045) B1997045
theorem B1896625 : Blo 1330984 1896625 := bstep (se 2 (by rfl) ⟨711234, by rfl⟩ : syracuseStep 1896625 = 1422469) B1422469
theorem B1331379 : Blo 1330984 1331379 := bstep (se 1 (by rfl) ⟨998534, by rfl⟩ : syracuseStep 1331379 = 1997069) B1997069
theorem B2248897 : Blo 1330984 2248897 := bstep (se 2 (by rfl) ⟨843336, by rfl⟩ : syracuseStep 2248897 = 1686673) B1686673
theorem B1331395 : Blo 1330984 1331395 := bstep (se 1 (by rfl) ⟨998546, by rfl⟩ : syracuseStep 1331395 = 1997093) B1997093
theorem B3199171 : Blo 1330984 3199171 := bstep (se 1 (by rfl) ⟨2399378, by rfl⟩ : syracuseStep 3199171 = 4798757) B4798757
theorem B1331411 : Blo 1330984 1331411 := bstep (se 1 (by rfl) ⟨998558, by rfl⟩ : syracuseStep 1331411 = 1997117) B1997117
theorem B1331427 : Blo 1330984 1331427 := bstep (se 1 (by rfl) ⟨998570, by rfl⟩ : syracuseStep 1331427 = 1997141) B1997141
theorem B2248931 : Blo 1330984 2248931 := bstep (se 1 (by rfl) ⟨1686698, by rfl⟩ : syracuseStep 2248931 = 3373397) B3373397
theorem B1331443 : Blo 1330984 1331443 := bstep (se 1 (by rfl) ⟨998582, by rfl⟩ : syracuseStep 1331443 = 1997165) B1997165
theorem B2134273 : Blo 1330984 2134273 := bstep (se 2 (by rfl) ⟨800352, by rfl⟩ : syracuseStep 2134273 = 1600705) B1600705
theorem B1331459 : Blo 1330984 1331459 := bstep (se 1 (by rfl) ⟨998594, by rfl⟩ : syracuseStep 1331459 = 1997189) B1997189
theorem B1331475 : Blo 1330984 1331475 := bstep (se 1 (by rfl) ⟨998606, by rfl⟩ : syracuseStep 1331475 = 1997213) B1997213
theorem B1331491 : Blo 1330984 1331491 := bstep (se 1 (by rfl) ⟨998618, by rfl⟩ : syracuseStep 1331491 = 1997237) B1997237
theorem B1331507 : Blo 1330984 1331507 := bstep (se 1 (by rfl) ⟨998630, by rfl⟩ : syracuseStep 1331507 = 1997261) B1997261
theorem B1331523 : Blo 1330984 1331523 := bstep (se 1 (by rfl) ⟨998642, by rfl⟩ : syracuseStep 1331523 = 1997285) B1997285
theorem B3600721 : Blo 1330984 3600721 := bstep (se 2 (by rfl) ⟨1350270, by rfl⟩ : syracuseStep 3600721 = 2700541) B2700541
theorem B1331539 : Blo 1330984 1331539 := bstep (se 1 (by rfl) ⟨998654, by rfl⟩ : syracuseStep 1331539 = 1997309) B1997309
theorem B1331555 : Blo 1330984 1331555 := bstep (se 1 (by rfl) ⟨998666, by rfl⟩ : syracuseStep 1331555 = 1997333) B1997333
theorem B2249059 : Blo 1330984 2249059 := bstep (se 1 (by rfl) ⟨1686794, by rfl⟩ : syracuseStep 2249059 = 3373589) B3373589
theorem B7590257 : Blo 1330984 7590257 := bstep (se 2 (by rfl) ⟨2846346, by rfl⟩ : syracuseStep 7590257 = 5692693) B5692693
theorem B1331571 : Blo 1330984 1331571 := bstep (se 1 (by rfl) ⟨998678, by rfl⟩ : syracuseStep 1331571 = 1997357) B1997357
theorem B1331587 : Blo 1330984 1331587 := bstep (se 1 (by rfl) ⟨998690, by rfl⟩ : syracuseStep 1331587 = 1997381) B1997381
theorem B1331603 : Blo 1330984 1331603 := bstep (se 1 (by rfl) ⟨998702, by rfl⟩ : syracuseStep 1331603 = 1997405) B1997405
theorem B1331619 : Blo 1330984 1331619 := bstep (se 1 (by rfl) ⟨998714, by rfl⟩ : syracuseStep 1331619 = 1997429) B1997429
theorem B1331635 : Blo 1330984 1331635 := bstep (se 1 (by rfl) ⟨998726, by rfl⟩ : syracuseStep 1331635 = 1997453) B1997453
theorem B1331651 : Blo 1330984 1331651 := bstep (se 1 (by rfl) ⟨998738, by rfl⟩ : syracuseStep 1331651 = 1997477) B1997477
theorem B1331667 : Blo 1330984 1331667 := bstep (se 1 (by rfl) ⟨998750, by rfl⟩ : syracuseStep 1331667 = 1997501) B1997501
theorem B1331683 : Blo 1330984 1331683 := bstep (se 1 (by rfl) ⟨998762, by rfl⟩ : syracuseStep 1331683 = 1997525) B1997525
theorem B7582193 : Blo 1330984 7582193 := bstep (se 2 (by rfl) ⟨2843322, by rfl⟩ : syracuseStep 7582193 = 5686645) B5686645
theorem B2249201 : Blo 1330984 2249201 := bstep (se 2 (by rfl) ⟨843450, by rfl⟩ : syracuseStep 2249201 = 1686901) B1686901
theorem B1331699 : Blo 1330984 1331699 := bstep (se 1 (by rfl) ⟨998774, by rfl⟩ : syracuseStep 1331699 = 1997549) B1997549
theorem B1896961 : Blo 1330984 1896961 := bstep (se 2 (by rfl) ⟨711360, by rfl⟩ : syracuseStep 1896961 = 1422721) B1422721
theorem B1331715 : Blo 1330984 1331715 := bstep (se 1 (by rfl) ⟨998786, by rfl⟩ : syracuseStep 1331715 = 1997573) B1997573
theorem B1331731 : Blo 1330984 1331731 := bstep (se 1 (by rfl) ⟨998798, by rfl⟩ : syracuseStep 1331731 = 1997597) B1997597
theorem B1331747 : Blo 1330984 1331747 := bstep (se 1 (by rfl) ⟨998810, by rfl⟩ : syracuseStep 1331747 = 1997621) B1997621
theorem B1421875 : Blo 1330984 1421875 := bstep (se 1 (by rfl) ⟨1066406, by rfl⟩ : syracuseStep 1421875 = 2132813) B2132813
theorem B1331763 : Blo 1330984 1331763 := bstep (se 1 (by rfl) ⟨998822, by rfl⟩ : syracuseStep 1331763 = 1997645) B1997645
theorem B1331779 : Blo 1330984 1331779 := bstep (se 1 (by rfl) ⟨998834, by rfl⟩ : syracuseStep 1331779 = 1997669) B1997669
theorem B1331795 : Blo 1330984 1331795 := bstep (se 1 (by rfl) ⟨998846, by rfl⟩ : syracuseStep 1331795 = 1997693) B1997693
theorem B1331811 : Blo 1330984 1331811 := bstep (se 1 (by rfl) ⟨998858, by rfl⟩ : syracuseStep 1331811 = 1997717) B1997717
theorem B4493933 : Blo 1330984 4493933 := bstep (se 3 (by rfl) ⟨842612, by rfl⟩ : syracuseStep 4493933 = 1685225) B1685225
theorem B2249329 : Blo 1330984 2249329 := bstep (se 2 (by rfl) ⟨843498, by rfl⟩ : syracuseStep 2249329 = 1686997) B1686997
theorem B1331827 : Blo 1330984 1331827 := bstep (se 1 (by rfl) ⟨998870, by rfl⟩ : syracuseStep 1331827 = 1997741) B1997741
theorem B1331843 : Blo 1330984 1331843 := bstep (se 1 (by rfl) ⟨998882, by rfl⟩ : syracuseStep 1331843 = 1997765) B1997765
theorem B3371665 : Blo 1330984 3371665 := bstep (se 2 (by rfl) ⟨1264374, by rfl⟩ : syracuseStep 3371665 = 2528749) B2528749
theorem B1331859 : Blo 1330984 1331859 := bstep (se 1 (by rfl) ⟨998894, by rfl⟩ : syracuseStep 1331859 = 1997789) B1997789
theorem B2249363 : Blo 1330984 2249363 := bstep (se 1 (by rfl) ⟨1687022, by rfl⟩ : syracuseStep 2249363 = 3374045) B3374045
theorem B4493987 : Blo 1330984 4493987 := bstep (se 1 (by rfl) ⟨3370490, by rfl⟩ : syracuseStep 4493987 = 6740981) B6740981
theorem B1331875 : Blo 1330984 1331875 := bstep (se 1 (by rfl) ⟨998906, by rfl⟩ : syracuseStep 1331875 = 1997813) B1997813
theorem B1331891 : Blo 1330984 1331891 := bstep (se 1 (by rfl) ⟨998918, by rfl⟩ : syracuseStep 1331891 = 1997837) B1997837
theorem B1331907 : Blo 1330984 1331907 := bstep (se 1 (by rfl) ⟨998930, by rfl⟩ : syracuseStep 1331907 = 1997861) B1997861
theorem B9736901 : Blo 1330984 9736901 := bstep (se 4 (by rfl) ⟨912834, by rfl⟩ : syracuseStep 9736901 = 1825669) B1825669
theorem B3846865 : Blo 1330984 3846865 := bstep (se 2 (by rfl) ⟨1442574, by rfl⟩ : syracuseStep 3846865 = 2885149) B2885149
theorem B1331923 : Blo 1330984 1331923 := bstep (se 1 (by rfl) ⟨998942, by rfl⟩ : syracuseStep 1331923 = 1997885) B1997885
theorem B1331939 : Blo 1330984 1331939 := bstep (se 1 (by rfl) ⟨998954, by rfl⟩ : syracuseStep 1331939 = 1997909) B1997909
theorem B2994929 : Blo 1330984 2994929 := bstep (se 2 (by rfl) ⟨1123098, by rfl⟩ : syracuseStep 2994929 = 2246197) B2246197
theorem B1331955 : Blo 1330984 1331955 := bstep (se 1 (by rfl) ⟨998966, by rfl⟩ : syracuseStep 1331955 = 1997933) B1997933
theorem B2994947 : Blo 1330984 2994947 := bstep (se 1 (by rfl) ⟨2246210, by rfl⟩ : syracuseStep 2994947 = 4492421) B4492421
theorem B1331971 : Blo 1330984 1331971 := bstep (se 1 (by rfl) ⟨998978, by rfl⟩ : syracuseStep 1331971 = 1997957) B1997957
theorem B1331987 : Blo 1330984 1331987 := bstep (se 1 (by rfl) ⟨998990, by rfl⟩ : syracuseStep 1331987 = 1997981) B1997981
theorem B1332003 : Blo 1330984 1332003 := bstep (se 1 (by rfl) ⟨999002, by rfl⟩ : syracuseStep 1332003 = 1998005) B1998005
theorem B4264753 : Blo 1330984 4264753 := bstep (se 2 (by rfl) ⟨1599282, by rfl⟩ : syracuseStep 4264753 = 3198565) B3198565
theorem B1422131 : Blo 1330984 1422131 := bstep (se 1 (by rfl) ⟨1066598, by rfl⟩ : syracuseStep 1422131 = 2133197) B2133197
theorem B1332019 : Blo 1330984 1332019 := bstep (se 1 (by rfl) ⟨999014, by rfl⟩ : syracuseStep 1332019 = 1998029) B1998029
theorem B1332035 : Blo 1330984 1332035 := bstep (se 1 (by rfl) ⟨999026, by rfl⟩ : syracuseStep 1332035 = 1998053) B1998053
theorem B2528081 : Blo 1330984 2528081 := bstep (se 2 (by rfl) ⟨948030, by rfl⟩ : syracuseStep 2528081 = 1896061) B1896061
theorem B1332051 : Blo 1330984 1332051 := bstep (se 1 (by rfl) ⟨999038, by rfl⟩ : syracuseStep 1332051 = 1998077) B1998077
theorem B1332067 : Blo 1330984 1332067 := bstep (se 1 (by rfl) ⟨999050, by rfl⟩ : syracuseStep 1332067 = 1998101) B1998101
theorem B1332083 : Blo 1330984 1332083 := bstep (se 1 (by rfl) ⟨999062, by rfl⟩ : syracuseStep 1332083 = 1998125) B1998125
theorem B1332099 : Blo 1330984 1332099 := bstep (se 1 (by rfl) ⟨999074, by rfl⟩ : syracuseStep 1332099 = 1998149) B1998149
theorem B12825485 : Blo 1330984 12825485 := bstep (se 3 (by rfl) ⟨2404778, by rfl⟩ : syracuseStep 12825485 = 4809557) B4809557
theorem B1332115 : Blo 1330984 1332115 := bstep (se 1 (by rfl) ⟨999086, by rfl⟩ : syracuseStep 1332115 = 1998173) B1998173
theorem B3371939 : Blo 1330984 3371939 := bstep (se 1 (by rfl) ⟨2528954, by rfl⟩ : syracuseStep 3371939 = 5057909) B5057909
theorem B1332131 : Blo 1330984 1332131 := bstep (se 1 (by rfl) ⟨999098, by rfl⟩ : syracuseStep 1332131 = 1998197) B1998197
theorem B4494257 : Blo 1330984 4494257 := bstep (se 2 (by rfl) ⟨1685346, by rfl⟩ : syracuseStep 4494257 = 3370693) B3370693
theorem B8106929 : Blo 1330984 8106929 := bstep (se 2 (by rfl) ⟨3040098, by rfl⟩ : syracuseStep 8106929 = 6080197) B6080197
theorem B1332147 : Blo 1330984 1332147 := bstep (se 1 (by rfl) ⟨999110, by rfl⟩ : syracuseStep 1332147 = 1998221) B1998221
theorem B1332163 : Blo 1330984 1332163 := bstep (se 1 (by rfl) ⟨999122, by rfl⟩ : syracuseStep 1332163 = 1998245) B1998245
theorem B1332179 : Blo 1330984 1332179 := bstep (se 1 (by rfl) ⟨999134, by rfl⟩ : syracuseStep 1332179 = 1998269) B1998269
theorem B1332195 : Blo 1330984 1332195 := bstep (se 1 (by rfl) ⟨999146, by rfl⟩ : syracuseStep 1332195 = 1998293) B1998293
theorem B1332211 : Blo 1330984 1332211 := bstep (se 1 (by rfl) ⟨999158, by rfl⟩ : syracuseStep 1332211 = 1998317) B1998317
theorem B1332227 : Blo 1330984 1332227 := bstep (se 1 (by rfl) ⟨999170, by rfl⟩ : syracuseStep 1332227 = 1998341) B1998341
theorem B2995217 : Blo 1330984 2995217 := bstep (se 2 (by rfl) ⟨1123206, by rfl⟩ : syracuseStep 2995217 = 2246413) B2246413
theorem B1332243 : Blo 1330984 1332243 := bstep (se 1 (by rfl) ⟨999182, by rfl⟩ : syracuseStep 1332243 = 1998365) B1998365
theorem B2995235 : Blo 1330984 2995235 := bstep (se 1 (by rfl) ⟨2246426, by rfl⟩ : syracuseStep 2995235 = 4492853) B4492853
theorem B1332259 : Blo 1330984 1332259 := bstep (se 1 (by rfl) ⟨999194, by rfl⟩ : syracuseStep 1332259 = 1998389) B1998389
theorem B1332275 : Blo 1330984 1332275 := bstep (se 1 (by rfl) ⟨999206, by rfl⟩ : syracuseStep 1332275 = 1998413) B1998413
theorem B1332291 : Blo 1330984 1332291 := bstep (se 1 (by rfl) ⟨999218, by rfl⟩ : syracuseStep 1332291 = 1998437) B1998437
theorem B1897553 : Blo 1330984 1897553 := bstep (se 2 (by rfl) ⟨711582, by rfl⟩ : syracuseStep 1897553 = 1423165) B1423165
theorem B1332307 : Blo 1330984 1332307 := bstep (se 1 (by rfl) ⟨999230, by rfl⟩ : syracuseStep 1332307 = 1998461) B1998461
theorem B3372131 : Blo 1330984 3372131 := bstep (se 1 (by rfl) ⟨2529098, by rfl⟩ : syracuseStep 3372131 = 5058197) B5058197
theorem B1332323 : Blo 1330984 1332323 := bstep (se 1 (by rfl) ⟨999242, by rfl⟩ : syracuseStep 1332323 = 1998485) B1998485
theorem B17306723 : Blo 1330984 17306723 := bstep (se 1 (by rfl) ⟨12980042, by rfl⟩ : syracuseStep 17306723 = 25960085) B25960085
theorem B1332339 : Blo 1330984 1332339 := bstep (se 1 (by rfl) ⟨999254, by rfl⟩ : syracuseStep 1332339 = 1998509) B1998509
theorem B1332355 : Blo 1330984 1332355 := bstep (se 1 (by rfl) ⟨999266, by rfl⟩ : syracuseStep 1332355 = 1998533) B1998533
theorem B7206029 : Blo 1330984 7206029 := bstep (se 3 (by rfl) ⟨1351130, by rfl⟩ : syracuseStep 7206029 = 2702261) B2702261
theorem B1332371 : Blo 1330984 1332371 := bstep (se 1 (by rfl) ⟨999278, by rfl⟩ : syracuseStep 1332371 = 1998557) B1998557
theorem B1332387 : Blo 1330984 1332387 := bstep (se 1 (by rfl) ⟨999290, by rfl⟩ : syracuseStep 1332387 = 1998581) B1998581
theorem B6747299 : Blo 1330984 6747299 := bstep (se 1 (by rfl) ⟨5060474, by rfl⟩ : syracuseStep 6747299 = 10120949) B10120949
theorem B1922225 : Blo 1330984 1922225 := bstep (se 2 (by rfl) ⟨720834, by rfl⟩ : syracuseStep 1922225 = 1441669) B1441669
theorem B1332403 : Blo 1330984 1332403 := bstep (se 1 (by rfl) ⟨999302, by rfl⟩ : syracuseStep 1332403 = 1998605) B1998605
theorem B1332419 : Blo 1330984 1332419 := bstep (se 1 (by rfl) ⟨999314, by rfl⟩ : syracuseStep 1332419 = 1998629) B1998629
theorem B1799377 : Blo 1330984 1799377 := bstep (se 2 (by rfl) ⟨674766, by rfl⟩ : syracuseStep 1799377 = 1349533) B1349533
theorem B1332435 : Blo 1330984 1332435 := bstep (se 1 (by rfl) ⟨999326, by rfl⟩ : syracuseStep 1332435 = 1998653) B1998653
theorem B1332451 : Blo 1330984 1332451 := bstep (se 1 (by rfl) ⟨999338, by rfl⟩ : syracuseStep 1332451 = 1998677) B1998677
theorem B1332467 : Blo 1330984 1332467 := bstep (se 1 (by rfl) ⟨999350, by rfl⟩ : syracuseStep 1332467 = 1998701) B1998701
theorem B1684739 : Blo 1330984 1684739 := bstep (se 1 (by rfl) ⟨1263554, by rfl⟩ : syracuseStep 1684739 = 2527109) B2527109
theorem B1332483 : Blo 1330984 1332483 := bstep (se 1 (by rfl) ⟨999362, by rfl⟩ : syracuseStep 1332483 = 1998725) B1998725
theorem B5059853 : Blo 1330984 5059853 := bstep (se 3 (by rfl) ⟨948722, by rfl⟩ : syracuseStep 5059853 = 1897445) B1897445
theorem B1332499 : Blo 1330984 1332499 := bstep (se 1 (by rfl) ⟨999374, by rfl⟩ : syracuseStep 1332499 = 1998749) B1998749
theorem B1332515 : Blo 1330984 1332515 := bstep (se 1 (by rfl) ⟨999386, by rfl⟩ : syracuseStep 1332515 = 1998773) B1998773
theorem B2995505 : Blo 1330984 2995505 := bstep (se 2 (by rfl) ⟨1123314, by rfl⟩ : syracuseStep 2995505 = 2246629) B2246629
theorem B1332531 : Blo 1330984 1332531 := bstep (se 1 (by rfl) ⟨999398, by rfl⟩ : syracuseStep 1332531 = 1998797) B1998797
theorem B2995523 : Blo 1330984 2995523 := bstep (se 1 (by rfl) ⟨2246642, by rfl⟩ : syracuseStep 2995523 = 4493285) B4493285
theorem B1332547 : Blo 1330984 1332547 := bstep (se 1 (by rfl) ⟨999410, by rfl⟩ : syracuseStep 1332547 = 1998821) B1998821
theorem B1332563 : Blo 1330984 1332563 := bstep (se 1 (by rfl) ⟨999422, by rfl⟩ : syracuseStep 1332563 = 1998845) B1998845
theorem B1332579 : Blo 1330984 1332579 := bstep (se 1 (by rfl) ⟨999434, by rfl⟩ : syracuseStep 1332579 = 1998869) B1998869
theorem B1332595 : Blo 1330984 1332595 := bstep (se 1 (by rfl) ⟨999446, by rfl⟩ : syracuseStep 1332595 = 1998893) B1998893
theorem B1332611 : Blo 1330984 1332611 := bstep (se 1 (by rfl) ⟨999458, by rfl⟩ : syracuseStep 1332611 = 1998917) B1998917
theorem B3200401 : Blo 1330984 3200401 := bstep (se 2 (by rfl) ⟨1200150, by rfl⟩ : syracuseStep 3200401 = 2400301) B2400301
theorem B4052369 : Blo 1330984 4052369 := bstep (se 2 (by rfl) ⟨1519638, by rfl⟩ : syracuseStep 4052369 = 3039277) B3039277
theorem B1332627 : Blo 1330984 1332627 := bstep (se 1 (by rfl) ⟨999470, by rfl⟩ : syracuseStep 1332627 = 1998941) B1998941
theorem B1332643 : Blo 1330984 1332643 := bstep (se 1 (by rfl) ⟨999482, by rfl⟩ : syracuseStep 1332643 = 1998965) B1998965
theorem B3790253 : Blo 1330984 3790253 := bstep (se 3 (by rfl) ⟨710672, by rfl⟩ : syracuseStep 3790253 = 1421345) B1421345
theorem B1332659 : Blo 1330984 1332659 := bstep (se 1 (by rfl) ⟨999494, by rfl⟩ : syracuseStep 1332659 = 1998989) B1998989
theorem B1332675 : Blo 1330984 1332675 := bstep (se 1 (by rfl) ⟨999506, by rfl⟩ : syracuseStep 1332675 = 1999013) B1999013
theorem B4494797 : Blo 1330984 4494797 := bstep (se 3 (by rfl) ⟨842774, by rfl⟩ : syracuseStep 4494797 = 1685549) B1685549
theorem B1332691 : Blo 1330984 1332691 := bstep (se 1 (by rfl) ⟨999518, by rfl⟩ : syracuseStep 1332691 = 1999037) B1999037
theorem B1332707 : Blo 1330984 1332707 := bstep (se 1 (by rfl) ⟨999530, by rfl⟩ : syracuseStep 1332707 = 1999061) B1999061
theorem B10245617 : Blo 1330984 10245617 := bstep (se 2 (by rfl) ⟨3842106, by rfl⟩ : syracuseStep 10245617 = 7684213) B7684213
theorem B1332723 : Blo 1330984 1332723 := bstep (se 1 (by rfl) ⟨999542, by rfl⟩ : syracuseStep 1332723 = 1999085) B1999085
theorem B4494851 : Blo 1330984 4494851 := bstep (se 1 (by rfl) ⟨3371138, by rfl⟩ : syracuseStep 4494851 = 6742277) B6742277
theorem B1332739 : Blo 1330984 1332739 := bstep (se 1 (by rfl) ⟨999554, by rfl⟩ : syracuseStep 1332739 = 1999109) B1999109
theorem B1332755 : Blo 1330984 1332755 := bstep (se 1 (by rfl) ⟨999566, by rfl⟩ : syracuseStep 1332755 = 1999133) B1999133
theorem B1422883 : Blo 1330984 1422883 := bstep (se 1 (by rfl) ⟨1067162, by rfl⟩ : syracuseStep 1422883 = 2134325) B2134325
theorem B3601955 : Blo 1330984 3601955 := bstep (se 1 (by rfl) ⟨2701466, by rfl⟩ : syracuseStep 3601955 = 5402933) B5402933
theorem B1332771 : Blo 1330984 1332771 := bstep (se 1 (by rfl) ⟨999578, by rfl⟩ : syracuseStep 1332771 = 1999157) B1999157
theorem B5404195 : Blo 1330984 5404195 := bstep (se 1 (by rfl) ⟨4053146, by rfl⟩ : syracuseStep 5404195 = 8106293) B8106293
theorem B1332787 : Blo 1330984 1332787 := bstep (se 1 (by rfl) ⟨999590, by rfl⟩ : syracuseStep 1332787 = 1999181) B1999181
theorem B1332803 : Blo 1330984 1332803 := bstep (se 1 (by rfl) ⟨999602, by rfl⟩ : syracuseStep 1332803 = 1999205) B1999205
theorem B2995793 : Blo 1330984 2995793 := bstep (se 2 (by rfl) ⟨1123422, by rfl⟩ : syracuseStep 2995793 = 2246845) B2246845
theorem B1332819 : Blo 1330984 1332819 := bstep (se 1 (by rfl) ⟨999614, by rfl⟩ : syracuseStep 1332819 = 1999229) B1999229
theorem B2995811 : Blo 1330984 2995811 := bstep (se 1 (by rfl) ⟨2246858, by rfl⟩ : syracuseStep 2995811 = 4493717) B4493717
theorem B11376227 : Blo 1330984 11376227 := bstep (se 1 (by rfl) ⟨8532170, by rfl⟩ : syracuseStep 11376227 = 17064341) B17064341
theorem B1332835 : Blo 1330984 1332835 := bstep (se 1 (by rfl) ⟨999626, by rfl⟩ : syracuseStep 1332835 = 1999253) B1999253
theorem B1332851 : Blo 1330984 1332851 := bstep (se 1 (by rfl) ⟨999638, by rfl⟩ : syracuseStep 1332851 = 1999277) B1999277
theorem B1332867 : Blo 1330984 1332867 := bstep (se 1 (by rfl) ⟨999650, by rfl⟩ : syracuseStep 1332867 = 1999301) B1999301
theorem B1332883 : Blo 1330984 1332883 := bstep (se 1 (by rfl) ⟨999662, by rfl⟩ : syracuseStep 1332883 = 1999325) B1999325
theorem B1332899 : Blo 1330984 1332899 := bstep (se 1 (by rfl) ⟨999674, by rfl⟩ : syracuseStep 1332899 = 1999349) B1999349
theorem B1332915 : Blo 1330984 1332915 := bstep (se 1 (by rfl) ⟨999686, by rfl⟩ : syracuseStep 1332915 = 1999373) B1999373
theorem B1996481 : Blo 1330984 1996481 := bstep (se 2 (by rfl) ⟨748680, by rfl⟩ : syracuseStep 1996481 = 1497361) B1497361
theorem B1332931 : Blo 1330984 1332931 := bstep (se 1 (by rfl) ⟨999698, by rfl⟩ : syracuseStep 1332931 = 1999397) B1999397
theorem B6076109 : Blo 1330984 6076109 := bstep (se 3 (by rfl) ⟨1139270, by rfl⟩ : syracuseStep 6076109 = 2278541) B2278541
theorem B2528977 : Blo 1330984 2528977 := bstep (se 2 (by rfl) ⟨948366, by rfl⟩ : syracuseStep 2528977 = 1896733) B1896733
theorem B1996499 : Blo 1330984 1996499 := bstep (se 1 (by rfl) ⟨1497374, by rfl⟩ : syracuseStep 1996499 = 2994749) B2994749
theorem B1332947 : Blo 1330984 1332947 := bstep (se 1 (by rfl) ⟨999710, by rfl⟩ : syracuseStep 1332947 = 1999421) B1999421
theorem B9606883 : Blo 1330984 9606883 := bstep (se 1 (by rfl) ⟨7205162, by rfl⟩ : syracuseStep 9606883 = 14410325) B14410325
theorem B1332963 : Blo 1330984 1332963 := bstep (se 1 (by rfl) ⟨999722, by rfl⟩ : syracuseStep 1332963 = 1999445) B1999445
theorem B1996529 : Blo 1330984 1996529 := bstep (se 2 (by rfl) ⟨748698, by rfl⟩ : syracuseStep 1996529 = 1497397) B1497397
theorem B1332979 : Blo 1330984 1332979 := bstep (se 1 (by rfl) ⟨999734, by rfl⟩ : syracuseStep 1332979 = 1999469) B1999469
theorem B1996547 : Blo 1330984 1996547 := bstep (se 1 (by rfl) ⟨1497410, by rfl⟩ : syracuseStep 1996547 = 2994821) B2994821
theorem B5764877 : Blo 1330984 5764877 := bstep (se 3 (by rfl) ⟨1080914, by rfl⟩ : syracuseStep 5764877 = 2161829) B2161829
theorem B4495121 : Blo 1330984 4495121 := bstep (se 2 (by rfl) ⟨1685670, by rfl⟩ : syracuseStep 4495121 = 3371341) B3371341
theorem B1996577 : Blo 1330984 1996577 := bstep (se 2 (by rfl) ⟨748716, by rfl⟩ : syracuseStep 1996577 = 1497433) B1497433
theorem B7591715 : Blo 1330984 7591715 := bstep (se 1 (by rfl) ⟨5693786, by rfl⟩ : syracuseStep 7591715 = 11387573) B11387573
theorem B1996595 : Blo 1330984 1996595 := bstep (se 1 (by rfl) ⟨1497446, by rfl⟩ : syracuseStep 1996595 = 2994893) B2994893
theorem B1996625 : Blo 1330984 1996625 := bstep (se 2 (by rfl) ⟨748734, by rfl⟩ : syracuseStep 1996625 = 1497469) B1497469
theorem B1996643 : Blo 1330984 1996643 := bstep (se 1 (by rfl) ⟨1497482, by rfl⟩ : syracuseStep 1996643 = 2994965) B2994965
theorem B4052845 : Blo 1330984 4052845 := bstep (se 3 (by rfl) ⟨759908, by rfl⟩ : syracuseStep 4052845 = 1519817) B1519817
theorem B2996081 : Blo 1330984 2996081 := bstep (se 2 (by rfl) ⟨1123530, by rfl⟩ : syracuseStep 2996081 = 2247061) B2247061
theorem B2529137 : Blo 1330984 2529137 := bstep (se 2 (by rfl) ⟨948426, by rfl⟩ : syracuseStep 2529137 = 1896853) B1896853
theorem B1996673 : Blo 1330984 1996673 := bstep (se 2 (by rfl) ⟨748752, by rfl⟩ : syracuseStep 1996673 = 1497505) B1497505
theorem B2996099 : Blo 1330984 2996099 := bstep (se 1 (by rfl) ⟨2247074, by rfl⟩ : syracuseStep 2996099 = 4494149) B4494149
theorem B1996691 : Blo 1330984 1996691 := bstep (se 1 (by rfl) ⟨1497518, by rfl⟩ : syracuseStep 1996691 = 2995037) B2995037
theorem B7583651 : Blo 1330984 7583651 := bstep (se 1 (by rfl) ⟨5687738, by rfl⟩ : syracuseStep 7583651 = 11375477) B11375477
theorem B1996721 : Blo 1330984 1996721 := bstep (se 2 (by rfl) ⟨748770, by rfl⟩ : syracuseStep 1996721 = 1497541) B1497541
theorem B1996739 : Blo 1330984 1996739 := bstep (se 1 (by rfl) ⟨1497554, by rfl⟩ : syracuseStep 1996739 = 2995109) B2995109
theorem B1685443 : Blo 1330984 1685443 := bstep (se 1 (by rfl) ⟨1264082, by rfl⟩ : syracuseStep 1685443 = 2528165) B2528165
theorem B6748109 : Blo 1330984 6748109 := bstep (se 3 (by rfl) ⟨1265270, by rfl⟩ : syracuseStep 6748109 = 2530541) B2530541
theorem B1996769 : Blo 1330984 1996769 := bstep (se 2 (by rfl) ⟨748788, by rfl⟩ : syracuseStep 1996769 = 1497577) B1497577
theorem B1996787 : Blo 1330984 1996787 := bstep (se 1 (by rfl) ⟨1497590, by rfl⟩ : syracuseStep 1996787 = 2995181) B2995181
theorem B1996817 : Blo 1330984 1996817 := bstep (se 2 (by rfl) ⟨748806, by rfl⟩ : syracuseStep 1996817 = 1497613) B1497613
theorem B3373073 : Blo 1330984 3373073 := bstep (se 2 (by rfl) ⟨1264902, by rfl⟩ : syracuseStep 3373073 = 2529805) B2529805
theorem B1996835 : Blo 1330984 1996835 := bstep (se 1 (by rfl) ⟨1497626, by rfl⟩ : syracuseStep 1996835 = 2995253) B2995253
theorem B1685539 : Blo 1330984 1685539 := bstep (se 1 (by rfl) ⟨1264154, by rfl⟩ : syracuseStep 1685539 = 2528309) B2528309
theorem B5060657 : Blo 1330984 5060657 := bstep (se 2 (by rfl) ⟨1897746, by rfl⟩ : syracuseStep 5060657 = 3795493) B3795493
theorem B1996865 : Blo 1330984 1996865 := bstep (se 2 (by rfl) ⟨748824, by rfl⟩ : syracuseStep 1996865 = 1497649) B1497649
theorem B3373123 : Blo 1330984 3373123 := bstep (se 1 (by rfl) ⟨2529842, by rfl⟩ : syracuseStep 3373123 = 5059685) B5059685
theorem B4798541 : Blo 1330984 4798541 := bstep (se 3 (by rfl) ⟨899726, by rfl⟩ : syracuseStep 4798541 = 1799453) B1799453
theorem B1996883 : Blo 1330984 1996883 := bstep (se 1 (by rfl) ⟨1497662, by rfl⟩ : syracuseStep 1996883 = 2995325) B2995325
theorem B1996913 : Blo 1330984 1996913 := bstep (se 2 (by rfl) ⟨748842, by rfl⟩ : syracuseStep 1996913 = 1497685) B1497685
theorem B1996931 : Blo 1330984 1996931 := bstep (se 1 (by rfl) ⟨1497698, by rfl⟩ : syracuseStep 1996931 = 2995397) B2995397
theorem B2996369 : Blo 1330984 2996369 := bstep (se 2 (by rfl) ⟨1123638, by rfl⟩ : syracuseStep 2996369 = 2247277) B2247277
theorem B1996961 : Blo 1330984 1996961 := bstep (se 2 (by rfl) ⟨748860, by rfl⟩ : syracuseStep 1996961 = 1497721) B1497721
theorem B2996387 : Blo 1330984 2996387 := bstep (se 1 (by rfl) ⟨2247290, by rfl⟩ : syracuseStep 2996387 = 4494581) B4494581
theorem B1996979 : Blo 1330984 1996979 := bstep (se 1 (by rfl) ⟨1497734, by rfl⟩ : syracuseStep 1996979 = 2995469) B2995469
theorem B1997009 : Blo 1330984 1997009 := bstep (se 2 (by rfl) ⟨748878, by rfl⟩ : syracuseStep 1997009 = 1497757) B1497757
theorem B3373265 : Blo 1330984 3373265 := bstep (se 2 (by rfl) ⟨1264974, by rfl⟩ : syracuseStep 3373265 = 2529949) B2529949
theorem B1997027 : Blo 1330984 1997027 := bstep (se 1 (by rfl) ⟨1497770, by rfl⟩ : syracuseStep 1997027 = 2995541) B2995541
theorem B1997057 : Blo 1330984 1997057 := bstep (se 2 (by rfl) ⟨748896, by rfl⟩ : syracuseStep 1997057 = 1497793) B1497793
theorem B2529539 : Blo 1330984 2529539 := bstep (se 1 (by rfl) ⟨1897154, by rfl⟩ : syracuseStep 2529539 = 3794309) B3794309
theorem B1997075 : Blo 1330984 1997075 := bstep (se 1 (by rfl) ⟨1497806, by rfl⟩ : syracuseStep 1997075 = 2995613) B2995613
theorem B1497379 : Blo 1330984 1497379 := bstep (se 1 (by rfl) ⟨1123034, by rfl⟩ : syracuseStep 1497379 = 2246069) B2246069
theorem B4495661 : Blo 1330984 4495661 := bstep (se 3 (by rfl) ⟨842936, by rfl⟩ : syracuseStep 4495661 = 1685873) B1685873
theorem B9107761 : Blo 1330984 9107761 := bstep (se 2 (by rfl) ⟨3415410, by rfl⟩ : syracuseStep 9107761 = 6830821) B6830821
theorem B1997105 : Blo 1330984 1997105 := bstep (se 2 (by rfl) ⟨748914, by rfl⟩ : syracuseStep 1997105 = 1497829) B1497829
theorem B1997123 : Blo 1330984 1997123 := bstep (se 1 (by rfl) ⟨1497842, by rfl⟩ : syracuseStep 1997123 = 2995685) B2995685
theorem B1997153 : Blo 1330984 1997153 := bstep (se 2 (by rfl) ⟨748932, by rfl⟩ : syracuseStep 1997153 = 1497865) B1497865
theorem B4495715 : Blo 1330984 4495715 := bstep (se 1 (by rfl) ⟨3371786, by rfl⟩ : syracuseStep 4495715 = 6743573) B6743573
theorem B1997171 : Blo 1330984 1997171 := bstep (se 1 (by rfl) ⟨1497878, by rfl⟩ : syracuseStep 1997171 = 2995757) B2995757
theorem B1800577 : Blo 1330984 1800577 := bstep (se 2 (by rfl) ⟨675216, by rfl⟩ : syracuseStep 1800577 = 1350433) B1350433
theorem B15161741 : Blo 1330984 15161741 := bstep (se 3 (by rfl) ⟨2842826, by rfl⟩ : syracuseStep 15161741 = 5685653) B5685653
theorem B3791245 : Blo 1330984 3791245 := bstep (se 3 (by rfl) ⟨710858, by rfl⟩ : syracuseStep 3791245 = 1421717) B1421717
theorem B1997201 : Blo 1330984 1997201 := bstep (se 2 (by rfl) ⟨748950, by rfl⟩ : syracuseStep 1997201 = 1497901) B1497901
theorem B1997219 : Blo 1330984 1997219 := bstep (se 1 (by rfl) ⟨1497914, by rfl⟩ : syracuseStep 1997219 = 2995829) B2995829
theorem B2996657 : Blo 1330984 2996657 := bstep (se 2 (by rfl) ⟨1123746, by rfl⟩ : syracuseStep 2996657 = 2247493) B2247493
theorem B1497523 : Blo 1330984 1497523 := bstep (se 1 (by rfl) ⟨1123142, by rfl⟩ : syracuseStep 1497523 = 2246285) B2246285
theorem B1997249 : Blo 1330984 1997249 := bstep (se 2 (by rfl) ⟨748968, by rfl⟩ : syracuseStep 1997249 = 1497937) B1497937
theorem B2996675 : Blo 1330984 2996675 := bstep (se 1 (by rfl) ⟨2247506, by rfl⟩ : syracuseStep 2996675 = 4495013) B4495013
theorem B4266445 : Blo 1330984 4266445 := bstep (se 3 (by rfl) ⟨799958, by rfl⟩ : syracuseStep 4266445 = 1599917) B1599917
theorem B1997267 : Blo 1330984 1997267 := bstep (se 1 (by rfl) ⟨1497950, by rfl⟩ : syracuseStep 1997267 = 2995901) B2995901
theorem B1997297 : Blo 1330984 1997297 := bstep (se 2 (by rfl) ⟨748986, by rfl⟩ : syracuseStep 1997297 = 1497973) B1497973
theorem B1997315 : Blo 1330984 1997315 := bstep (se 1 (by rfl) ⟨1497986, by rfl⟩ : syracuseStep 1997315 = 2995973) B2995973
theorem B1686035 : Blo 1330984 1686035 := bstep (se 1 (by rfl) ⟨1264526, by rfl⟩ : syracuseStep 1686035 = 2529053) B2529053
theorem B1997345 : Blo 1330984 1997345 := bstep (se 2 (by rfl) ⟨749004, by rfl⟩ : syracuseStep 1997345 = 1498009) B1498009
theorem B1997363 : Blo 1330984 1997363 := bstep (se 1 (by rfl) ⟨1498022, by rfl⟩ : syracuseStep 1997363 = 2996045) B2996045
theorem B18233909 : Blo 1330984 18233909 := bstep (se 5 (by rfl) ⟨854714, by rfl⟩ : syracuseStep 18233909 = 1709429) B1709429
theorem B1497667 : Blo 1330984 1497667 := bstep (se 1 (by rfl) ⟨1123250, by rfl⟩ : syracuseStep 1497667 = 2246501) B2246501
theorem B1997393 : Blo 1330984 1997393 := bstep (se 2 (by rfl) ⟨749022, by rfl⟩ : syracuseStep 1997393 = 1498045) B1498045
theorem B6396515 : Blo 1330984 6396515 := bstep (se 1 (by rfl) ⟨4797386, by rfl⟩ : syracuseStep 6396515 = 9594773) B9594773
theorem B1997411 : Blo 1330984 1997411 := bstep (se 1 (by rfl) ⟨1498058, by rfl⟩ : syracuseStep 1997411 = 2996117) B2996117
theorem B4495985 : Blo 1330984 4495985 := bstep (se 2 (by rfl) ⟨1685994, by rfl⟩ : syracuseStep 4495985 = 3371989) B3371989
theorem B1997441 : Blo 1330984 1997441 := bstep (se 2 (by rfl) ⟨749040, by rfl⟩ : syracuseStep 1997441 = 1498081) B1498081
theorem B7199365 : Blo 1330984 7199365 := bstep (se 4 (by rfl) ⟨674940, by rfl⟩ : syracuseStep 7199365 = 1349881) B1349881
theorem B1997459 : Blo 1330984 1997459 := bstep (se 1 (by rfl) ⟨1498094, by rfl⟩ : syracuseStep 1997459 = 2996189) B2996189
theorem B6740657 : Blo 1330984 6740657 := bstep (se 2 (by rfl) ⟨2527746, by rfl⟩ : syracuseStep 6740657 = 5055493) B5055493
theorem B1997489 : Blo 1330984 1997489 := bstep (se 2 (by rfl) ⟨749058, by rfl⟩ : syracuseStep 1997489 = 1498117) B1498117
theorem B1997507 : Blo 1330984 1997507 := bstep (se 1 (by rfl) ⟨1498130, by rfl⟩ : syracuseStep 1997507 = 2996261) B2996261
theorem B8100557 : Blo 1330984 8100557 := bstep (se 3 (by rfl) ⟨1518854, by rfl⟩ : syracuseStep 8100557 = 3037709) B3037709
theorem B2996945 : Blo 1330984 2996945 := bstep (se 2 (by rfl) ⟨1123854, by rfl⟩ : syracuseStep 2996945 = 2247709) B2247709
theorem B1497811 : Blo 1330984 1497811 := bstep (se 1 (by rfl) ⟨1123358, by rfl⟩ : syracuseStep 1497811 = 2246717) B2246717
theorem B1997537 : Blo 1330984 1997537 := bstep (se 2 (by rfl) ⟨749076, by rfl⟩ : syracuseStep 1997537 = 1498153) B1498153
theorem B2996963 : Blo 1330984 2996963 := bstep (se 1 (by rfl) ⟨2247722, by rfl⟩ : syracuseStep 2996963 = 4495445) B4495445
theorem B1997555 : Blo 1330984 1997555 := bstep (se 1 (by rfl) ⟨1498166, by rfl⟩ : syracuseStep 1997555 = 2996333) B2996333
theorem B1997585 : Blo 1330984 1997585 := bstep (se 2 (by rfl) ⟨749094, by rfl⟩ : syracuseStep 1997585 = 1498189) B1498189
theorem B1997603 : Blo 1330984 1997603 := bstep (se 1 (by rfl) ⟨1498202, by rfl⟩ : syracuseStep 1997603 = 2996405) B2996405
theorem B1997633 : Blo 1330984 1997633 := bstep (se 2 (by rfl) ⟨749112, by rfl⟩ : syracuseStep 1997633 = 1498225) B1498225
theorem B4553539 : Blo 1330984 4553539 := bstep (se 1 (by rfl) ⟨3415154, by rfl⟩ : syracuseStep 4553539 = 6830309) B6830309
theorem B1997651 : Blo 1330984 1997651 := bstep (se 1 (by rfl) ⟨1498238, by rfl⟩ : syracuseStep 1997651 = 2996477) B2996477
theorem B1497955 : Blo 1330984 1497955 := bstep (se 1 (by rfl) ⟨1123466, by rfl⟩ : syracuseStep 1497955 = 2246933) B2246933
theorem B1997681 : Blo 1330984 1997681 := bstep (se 2 (by rfl) ⟨749130, by rfl⟩ : syracuseStep 1997681 = 1498261) B1498261
theorem B1997699 : Blo 1330984 1997699 := bstep (se 1 (by rfl) ⟨1498274, by rfl⟩ : syracuseStep 1997699 = 2996549) B2996549
theorem B1997729 : Blo 1330984 1997729 := bstep (se 2 (by rfl) ⟨749148, by rfl⟩ : syracuseStep 1997729 = 1498297) B1498297
theorem B1997747 : Blo 1330984 1997747 := bstep (se 1 (by rfl) ⟨1498310, by rfl⟩ : syracuseStep 1997747 = 2996621) B2996621
theorem B1997777 : Blo 1330984 1997777 := bstep (se 2 (by rfl) ⟨749166, by rfl⟩ : syracuseStep 1997777 = 1498333) B1498333
theorem B1997795 : Blo 1330984 1997795 := bstep (se 1 (by rfl) ⟨1498346, by rfl⟩ : syracuseStep 1997795 = 2996693) B2996693
theorem B2997233 : Blo 1330984 2997233 := bstep (se 2 (by rfl) ⟨1123962, by rfl⟩ : syracuseStep 2997233 = 2247925) B2247925
theorem B1498099 : Blo 1330984 1498099 := bstep (se 1 (by rfl) ⟨1123574, by rfl⟩ : syracuseStep 1498099 = 2247149) B2247149
theorem B1997825 : Blo 1330984 1997825 := bstep (se 2 (by rfl) ⟨749184, by rfl⟩ : syracuseStep 1997825 = 1498369) B1498369
theorem B2997251 : Blo 1330984 2997251 := bstep (se 1 (by rfl) ⟨2247938, by rfl⟩ : syracuseStep 2997251 = 4495877) B4495877
theorem B1997843 : Blo 1330984 1997843 := bstep (se 1 (by rfl) ⟨1498382, by rfl⟩ : syracuseStep 1997843 = 2996765) B2996765
theorem B1997873 : Blo 1330984 1997873 := bstep (se 2 (by rfl) ⟨749202, by rfl⟩ : syracuseStep 1997873 = 1498405) B1498405
theorem B1997891 : Blo 1330984 1997891 := bstep (se 1 (by rfl) ⟨1498418, by rfl⟩ : syracuseStep 1997891 = 2996837) B2996837
theorem B1997921 : Blo 1330984 1997921 := bstep (se 2 (by rfl) ⟨749220, by rfl⟩ : syracuseStep 1997921 = 1498441) B1498441
theorem B1997939 : Blo 1330984 1997939 := bstep (se 1 (by rfl) ⟨1498454, by rfl⟩ : syracuseStep 1997939 = 2996909) B2996909
theorem B1498243 : Blo 1330984 1498243 := bstep (se 1 (by rfl) ⟨1123682, by rfl⟩ : syracuseStep 1498243 = 2247365) B2247365
theorem B2530435 : Blo 1330984 2530435 := bstep (se 1 (by rfl) ⟨1897826, by rfl⟩ : syracuseStep 2530435 = 3795653) B3795653
theorem B4496525 : Blo 1330984 4496525 := bstep (se 3 (by rfl) ⟨843098, by rfl⟩ : syracuseStep 4496525 = 1686197) B1686197
theorem B1997969 : Blo 1330984 1997969 := bstep (se 2 (by rfl) ⟨749238, by rfl⟩ : syracuseStep 1997969 = 1498477) B1498477
theorem B1997987 : Blo 1330984 1997987 := bstep (se 1 (by rfl) ⟨1498490, by rfl⟩ : syracuseStep 1997987 = 2996981) B2996981
theorem B1998017 : Blo 1330984 1998017 := bstep (se 2 (by rfl) ⟨749256, by rfl⟩ : syracuseStep 1998017 = 1498513) B1498513
theorem B4496579 : Blo 1330984 4496579 := bstep (se 1 (by rfl) ⟨3372434, by rfl⟩ : syracuseStep 4496579 = 6744869) B6744869
theorem B1998035 : Blo 1330984 1998035 := bstep (se 1 (by rfl) ⟨1498526, by rfl⟩ : syracuseStep 1998035 = 2997053) B2997053
theorem B1686739 : Blo 1330984 1686739 := bstep (se 1 (by rfl) ⟨1265054, by rfl⟩ : syracuseStep 1686739 = 2530109) B2530109
theorem B1998065 : Blo 1330984 1998065 := bstep (se 2 (by rfl) ⟨749274, by rfl⟩ : syracuseStep 1998065 = 1498549) B1498549
theorem B1998083 : Blo 1330984 1998083 := bstep (se 1 (by rfl) ⟨1498562, by rfl⟩ : syracuseStep 1998083 = 2997125) B2997125
theorem B2997521 : Blo 1330984 2997521 := bstep (se 2 (by rfl) ⟨1124070, by rfl⟩ : syracuseStep 2997521 = 2248141) B2248141
theorem B1498387 : Blo 1330984 1498387 := bstep (se 1 (by rfl) ⟨1123790, by rfl⟩ : syracuseStep 1498387 = 2247581) B2247581
theorem B1998113 : Blo 1330984 1998113 := bstep (se 2 (by rfl) ⟨749292, by rfl⟩ : syracuseStep 1998113 = 1498585) B1498585
theorem B2997539 : Blo 1330984 2997539 := bstep (se 1 (by rfl) ⟨2248154, by rfl⟩ : syracuseStep 2997539 = 4496309) B4496309
theorem B1998131 : Blo 1330984 1998131 := bstep (se 1 (by rfl) ⟨1498598, by rfl⟩ : syracuseStep 1998131 = 2997197) B2997197
theorem B1686835 : Blo 1330984 1686835 := bstep (se 1 (by rfl) ⟨1265126, by rfl⟩ : syracuseStep 1686835 = 2530253) B2530253
theorem B1998161 : Blo 1330984 1998161 := bstep (se 2 (by rfl) ⟨749310, by rfl⟩ : syracuseStep 1998161 = 1498621) B1498621
theorem B1998179 : Blo 1330984 1998179 := bstep (se 1 (by rfl) ⟨1498634, by rfl⟩ : syracuseStep 1998179 = 2997269) B2997269
theorem B1998209 : Blo 1330984 1998209 := bstep (se 2 (by rfl) ⟨749328, by rfl⟩ : syracuseStep 1998209 = 1498657) B1498657
theorem B6397325 : Blo 1330984 6397325 := bstep (se 3 (by rfl) ⟨1199498, by rfl⟩ : syracuseStep 6397325 = 2398997) B2398997
theorem B1998227 : Blo 1330984 1998227 := bstep (se 1 (by rfl) ⟨1498670, by rfl⟩ : syracuseStep 1998227 = 2997341) B2997341
theorem B1498531 : Blo 1330984 1498531 := bstep (se 1 (by rfl) ⟨1123898, by rfl⟩ : syracuseStep 1498531 = 2247797) B2247797
theorem B1998257 : Blo 1330984 1998257 := bstep (se 2 (by rfl) ⟨749346, by rfl⟩ : syracuseStep 1998257 = 1498693) B1498693
theorem B1998275 : Blo 1330984 1998275 := bstep (se 1 (by rfl) ⟨1498706, by rfl⟩ : syracuseStep 1998275 = 2997413) B2997413
theorem B4496849 : Blo 1330984 4496849 := bstep (se 2 (by rfl) ⟨1686318, by rfl⟩ : syracuseStep 4496849 = 3372637) B3372637
theorem B1998305 : Blo 1330984 1998305 := bstep (se 2 (by rfl) ⟨749364, by rfl⟩ : syracuseStep 1998305 = 1498729) B1498729
theorem B1998323 : Blo 1330984 1998323 := bstep (se 1 (by rfl) ⟨1498742, by rfl⟩ : syracuseStep 1998323 = 2997485) B2997485
theorem B1998353 : Blo 1330984 1998353 := bstep (se 2 (by rfl) ⟨749382, by rfl⟩ : syracuseStep 1998353 = 1498765) B1498765
theorem B1998371 : Blo 1330984 1998371 := bstep (se 1 (by rfl) ⟨1498778, by rfl⟩ : syracuseStep 1998371 = 2997557) B2997557
theorem B2997809 : Blo 1330984 2997809 := bstep (se 2 (by rfl) ⟨1124178, by rfl⟩ : syracuseStep 2997809 = 2248357) B2248357
theorem B1498675 : Blo 1330984 1498675 := bstep (se 1 (by rfl) ⟨1124006, by rfl⟩ : syracuseStep 1498675 = 2248013) B2248013
theorem B1998401 : Blo 1330984 1998401 := bstep (se 2 (by rfl) ⟨749400, by rfl⟩ : syracuseStep 1998401 = 1498801) B1498801
theorem B2997827 : Blo 1330984 2997827 := bstep (se 1 (by rfl) ⟨2248370, by rfl⟩ : syracuseStep 2997827 = 4496741) B4496741
theorem B1998419 : Blo 1330984 1998419 := bstep (se 1 (by rfl) ⟨1498814, by rfl⟩ : syracuseStep 1998419 = 2997629) B2997629
theorem B1998449 : Blo 1330984 1998449 := bstep (se 2 (by rfl) ⟨749418, by rfl⟩ : syracuseStep 1998449 = 1498837) B1498837
theorem B1998467 : Blo 1330984 1998467 := bstep (se 1 (by rfl) ⟨1498850, by rfl⟩ : syracuseStep 1998467 = 2997701) B2997701
theorem B1998497 : Blo 1330984 1998497 := bstep (se 2 (by rfl) ⟨749436, by rfl⟩ : syracuseStep 1998497 = 1498873) B1498873
theorem B1998515 : Blo 1330984 1998515 := bstep (se 1 (by rfl) ⟨1498886, by rfl⟩ : syracuseStep 1998515 = 2997773) B2997773
theorem B1498819 : Blo 1330984 1498819 := bstep (se 1 (by rfl) ⟨1124114, by rfl⟩ : syracuseStep 1498819 = 2248229) B2248229
theorem B1998545 : Blo 1330984 1998545 := bstep (se 2 (by rfl) ⟨749454, by rfl⟩ : syracuseStep 1998545 = 1498909) B1498909
theorem B1998563 : Blo 1330984 1998563 := bstep (se 1 (by rfl) ⟨1498922, by rfl⟩ : syracuseStep 1998563 = 2997845) B2997845
theorem B1998593 : Blo 1330984 1998593 := bstep (se 2 (by rfl) ⟨749472, by rfl⟩ : syracuseStep 1998593 = 1498945) B1498945
theorem B4800269 : Blo 1330984 4800269 := bstep (se 3 (by rfl) ⟨900050, by rfl⟩ : syracuseStep 4800269 = 1800101) B1800101
theorem B1998611 : Blo 1330984 1998611 := bstep (se 1 (by rfl) ⟨1498958, by rfl⟩ : syracuseStep 1998611 = 2997917) B2997917
theorem B1998641 : Blo 1330984 1998641 := bstep (se 2 (by rfl) ⟨749490, by rfl⟩ : syracuseStep 1998641 = 1498981) B1498981
theorem B1998659 : Blo 1330984 1998659 := bstep (se 1 (by rfl) ⟨1498994, by rfl⟩ : syracuseStep 1998659 = 2997989) B2997989
theorem B2998097 : Blo 1330984 2998097 := bstep (se 2 (by rfl) ⟨1124286, by rfl⟩ : syracuseStep 2998097 = 2248573) B2248573
theorem B1498963 : Blo 1330984 1498963 := bstep (se 1 (by rfl) ⟨1124222, by rfl⟩ : syracuseStep 1498963 = 2248445) B2248445
theorem B1998689 : Blo 1330984 1998689 := bstep (se 2 (by rfl) ⟨749508, by rfl⟩ : syracuseStep 1998689 = 1499017) B1499017
theorem B2998115 : Blo 1330984 2998115 := bstep (se 1 (by rfl) ⟨2248586, by rfl⟩ : syracuseStep 2998115 = 4497173) B4497173
theorem B1998707 : Blo 1330984 1998707 := bstep (se 1 (by rfl) ⟨1499030, by rfl⟩ : syracuseStep 1998707 = 2998061) B2998061
theorem B1998737 : Blo 1330984 1998737 := bstep (se 2 (by rfl) ⟨749526, by rfl⟩ : syracuseStep 1998737 = 1499053) B1499053
theorem B1998755 : Blo 1330984 1998755 := bstep (se 1 (by rfl) ⟨1499066, by rfl⟩ : syracuseStep 1998755 = 2998133) B2998133
theorem B3415985 : Blo 1330984 3415985 := bstep (se 2 (by rfl) ⟨1280994, by rfl⟩ : syracuseStep 3415985 = 2561989) B2561989
theorem B1998785 : Blo 1330984 1998785 := bstep (se 2 (by rfl) ⟨749544, by rfl⟩ : syracuseStep 1998785 = 1499089) B1499089
theorem B10117061 : Blo 1330984 10117061 := bstep (se 4 (by rfl) ⟨948474, by rfl⟩ : syracuseStep 10117061 = 1896949) B1896949
theorem B1998803 : Blo 1330984 1998803 := bstep (se 1 (by rfl) ⟨1499102, by rfl⟩ : syracuseStep 1998803 = 2998205) B2998205
theorem B1499107 : Blo 1330984 1499107 := bstep (se 1 (by rfl) ⟨1124330, by rfl⟩ : syracuseStep 1499107 = 2248661) B2248661
theorem B4497389 : Blo 1330984 4497389 := bstep (se 3 (by rfl) ⟨843260, by rfl⟩ : syracuseStep 4497389 = 1686521) B1686521
theorem B1998833 : Blo 1330984 1998833 := bstep (se 2 (by rfl) ⟨749562, by rfl⟩ : syracuseStep 1998833 = 1499125) B1499125
theorem B3792919 : Blo 1330984 3792919 := bstep (se 1 (by rfl) ⟨2844689, by rfl⟩ : syracuseStep 3792919 = 5689379) B5689379
theorem B2998295 : Blo 1330984 2998295 := bstep (se 1 (by rfl) ⟨2248721, by rfl⟩ : syracuseStep 2998295 = 4497443) B4497443
theorem B1499179 : Blo 1330984 1499179 := bstep (se 1 (by rfl) ⟨1124384, by rfl⟩ : syracuseStep 1499179 = 2248769) B2248769
theorem B1998923 : Blo 1330984 1998923 := bstep (se 1 (by rfl) ⟨1499192, by rfl⟩ : syracuseStep 1998923 = 2998385) B2998385
theorem B1998935 : Blo 1330984 1998935 := bstep (se 1 (by rfl) ⟨1499201, by rfl⟩ : syracuseStep 1998935 = 2998403) B2998403
theorem B4497497 : Blo 1330984 4497497 := bstep (se 2 (by rfl) ⟨1686561, by rfl⟩ : syracuseStep 4497497 = 3373123) B3373123
theorem B1499287 : Blo 1330984 1499287 := bstep (se 1 (by rfl) ⟨1124465, by rfl⟩ : syracuseStep 1499287 = 2248931) B2248931
theorem B1999001 : Blo 1330984 1999001 := bstep (se 2 (by rfl) ⟨749625, by rfl⟩ : syracuseStep 1999001 = 1499251) B1499251
theorem B2998475 : Blo 1330984 2998475 := bstep (se 1 (by rfl) ⟨2248856, by rfl⟩ : syracuseStep 2998475 = 4497713) B4497713
theorem B2998529 : Blo 1330984 2998529 := bstep (se 2 (by rfl) ⟨1124448, by rfl⟩ : syracuseStep 2998529 = 2248897) B2248897
theorem B1999115 : Blo 1330984 1999115 := bstep (se 1 (by rfl) ⟨1499336, by rfl⟩ : syracuseStep 1999115 = 2998673) B2998673
theorem B1999127 : Blo 1330984 1999127 := bstep (se 1 (by rfl) ⟨1499345, by rfl⟩ : syracuseStep 1999127 = 2998691) B2998691
theorem B5054795 : Blo 1330984 5054795 := bstep (se 1 (by rfl) ⟨3791096, by rfl⟩ : syracuseStep 5054795 = 7582193) B7582193
theorem B1499467 : Blo 1330984 1499467 := bstep (se 1 (by rfl) ⟨1124600, by rfl⟩ : syracuseStep 1499467 = 2249201) B2249201
theorem B1999193 : Blo 1330984 1999193 := bstep (se 2 (by rfl) ⟨749697, by rfl⟩ : syracuseStep 1999193 = 1499395) B1499395
theorem B10109285 : Blo 1330984 10109285 := bstep (se 4 (by rfl) ⟨947745, by rfl⟩ : syracuseStep 10109285 = 1895491) B1895491
theorem B1499575 : Blo 1330984 1499575 := bstep (se 1 (by rfl) ⟨1124681, by rfl⟩ : syracuseStep 1499575 = 2249363) B2249363
theorem B4800961 : Blo 1330984 4800961 := bstep (se 2 (by rfl) ⟨1800360, by rfl⟩ : syracuseStep 4800961 = 3600721) B3600721
theorem B1999307 : Blo 1330984 1999307 := bstep (se 1 (by rfl) ⟨1499480, by rfl⟩ : syracuseStep 1999307 = 2998961) B2998961
theorem B1999319 : Blo 1330984 1999319 := bstep (se 1 (by rfl) ⟨1499489, by rfl⟩ : syracuseStep 1999319 = 2998979) B2998979
theorem B2163161 : Blo 1330984 2163161 := bstep (se 2 (by rfl) ⟨811185, by rfl⟩ : syracuseStep 2163161 = 1622371) B1622371
theorem B2998745 : Blo 1330984 2998745 := bstep (se 2 (by rfl) ⟨1124529, by rfl⟩ : syracuseStep 2998745 = 2249059) B2249059
theorem B2400769 : Blo 1330984 2400769 := bstep (se 2 (by rfl) ⟨900288, by rfl⟩ : syracuseStep 2400769 = 1800577) B1800577
theorem B5054993 : Blo 1330984 5054993 := bstep (se 2 (by rfl) ⟨1895622, by rfl⟩ : syracuseStep 5054993 = 3791245) B3791245
theorem B1999385 : Blo 1330984 1999385 := bstep (se 2 (by rfl) ⟨749769, by rfl⟩ : syracuseStep 1999385 = 1499539) B1499539
theorem B2998835 : Blo 1330984 2998835 := bstep (se 1 (by rfl) ⟨2249126, by rfl⟩ : syracuseStep 2998835 = 4498253) B4498253
theorem B245998133 : Blo 1330984 245998133 := bstep (se 5 (by rfl) ⟨11531162, by rfl⟩ : syracuseStep 245998133 = 23062325) B23062325
theorem B4325953 : Blo 1330984 4325953 := bstep (se 2 (by rfl) ⟨1622232, by rfl⟩ : syracuseStep 4325953 = 3244465) B3244465
theorem B2998871 : Blo 1330984 2998871 := bstep (se 1 (by rfl) ⟨2249153, by rfl⟩ : syracuseStep 2998871 = 4498307) B4498307
theorem B2163289 : Blo 1330984 2163289 := bstep (se 2 (by rfl) ⟨811233, by rfl⟩ : syracuseStep 2163289 = 1622467) B1622467
theorem B3793625 : Blo 1330984 3793625 := bstep (se 2 (by rfl) ⟨1422609, by rfl⟩ : syracuseStep 3793625 = 2845219) B2845219
theorem B1442539 : Blo 1330984 1442539 := bstep (se 1 (by rfl) ⟨1081904, by rfl⟩ : syracuseStep 1442539 = 2163809) B2163809
theorem B2999051 : Blo 1330984 2999051 := bstep (se 1 (by rfl) ⟨2249288, by rfl⟩ : syracuseStep 2999051 = 4498577) B4498577
theorem B4498199 : Blo 1330984 4498199 := bstep (se 1 (by rfl) ⟨3373649, by rfl⟩ : syracuseStep 4498199 = 6747299) B6747299
theorem B2999105 : Blo 1330984 2999105 := bstep (se 2 (by rfl) ⟨1124664, by rfl⟩ : syracuseStep 2999105 = 2249329) B2249329
theorem B10109771 : Blo 1330984 10109771 := bstep (se 1 (by rfl) ⟨7582328, by rfl⟩ : syracuseStep 10109771 = 15164657) B15164657
theorem B5473099 : Blo 1330984 5473099 := bstep (se 1 (by rfl) ⟨4104824, by rfl⟩ : syracuseStep 5473099 = 8209649) B8209649
theorem B2843545 : Blo 1330984 2843545 := bstep (se 2 (by rfl) ⟨1066329, by rfl⟩ : syracuseStep 2843545 = 2132659) B2132659
theorem B5129153 : Blo 1330984 5129153 := bstep (se 2 (by rfl) ⟨1923432, by rfl⟩ : syracuseStep 5129153 = 3846865) B3846865
theorem B12149777 : Blo 1330984 12149777 := bstep (se 2 (by rfl) ⟨4556166, by rfl⟩ : syracuseStep 12149777 = 9112333) B9112333
theorem B10806317 : Blo 1330984 10806317 := bstep (se 3 (by rfl) ⟨2026184, by rfl⟩ : syracuseStep 10806317 = 4052369) B4052369
theorem B5686337 : Blo 1330984 5686337 := bstep (se 2 (by rfl) ⟨2132376, by rfl⟩ : syracuseStep 5686337 = 4264753) B4264753
theorem B2278487 : Blo 1330984 2278487 := bstep (se 1 (by rfl) ⟨1708865, by rfl⟩ : syracuseStep 2278487 = 3417731) B3417731
theorem B3843251 : Blo 1330984 3843251 := bstep (se 1 (by rfl) ⟨2882438, by rfl⟩ : syracuseStep 3843251 = 5764877) B5764877
theorem B5055767 : Blo 1330984 5055767 := bstep (se 1 (by rfl) ⟨3791825, by rfl⟩ : syracuseStep 5055767 = 7583651) B7583651
theorem B4498739 : Blo 1330984 4498739 := bstep (se 1 (by rfl) ⟨3374054, by rfl⟩ : syracuseStep 4498739 = 6748109) B6748109
theorem B5686679 : Blo 1330984 5686679 := bstep (se 1 (by rfl) ⟨4265009, by rfl⟩ : syracuseStep 5686679 = 8530019) B8530019
theorem B5055965 : Blo 1330984 5055965 := bstep (se 3 (by rfl) ⟨947993, by rfl⟩ : syracuseStep 5055965 = 1895987) B1895987
theorem B8095249 : Blo 1330984 8095249 := bstep (se 2 (by rfl) ⟨3035718, by rfl⟩ : syracuseStep 8095249 = 6071437) B6071437
theorem B2246231 : Blo 1330984 2246231 := bstep (se 1 (by rfl) ⟨1684673, by rfl⟩ : syracuseStep 2246231 = 3369347) B3369347
theorem B5400209 : Blo 1330984 5400209 := bstep (se 2 (by rfl) ⟨2025078, by rfl⟩ : syracuseStep 5400209 = 4050157) B4050157
theorem B24643277 : Blo 1330984 24643277 := bstep (se 3 (by rfl) ⟨4620614, by rfl⟩ : syracuseStep 24643277 = 9241229) B9241229
theorem B2246359 : Blo 1330984 2246359 := bstep (se 1 (by rfl) ⟨1684769, by rfl⟩ : syracuseStep 2246359 = 3369539) B3369539
theorem B8652505 : Blo 1330984 8652505 := bstep (se 2 (by rfl) ⟨3244689, by rfl⟩ : syracuseStep 8652505 = 6489379) B6489379
theorem B36439793 : Blo 1330984 36439793 := bstep (se 2 (by rfl) ⟨13664922, by rfl⟩ : syracuseStep 36439793 = 27329845) B27329845
theorem B5400371 : Blo 1330984 5400371 := bstep (se 1 (by rfl) ⟨4050278, by rfl⟩ : syracuseStep 5400371 = 8100557) B8100557
theorem B10119005 : Blo 1330984 10119005 := bstep (se 3 (by rfl) ⟨1897313, by rfl⟩ : syracuseStep 10119005 = 3794627) B3794627
theorem B8324995 : Blo 1330984 8324995 := bstep (se 1 (by rfl) ⟨6243746, by rfl⟩ : syracuseStep 8324995 = 12487493) B12487493
theorem B2132185 : Blo 1330984 2132185 := bstep (se 2 (by rfl) ⟨799569, by rfl⟩ : syracuseStep 2132185 = 1599139) B1599139
theorem B5687603 : Blo 1330984 5687603 := bstep (se 1 (by rfl) ⟨4265702, by rfl⟩ : syracuseStep 5687603 = 8531405) B8531405
theorem B3795265 : Blo 1330984 3795265 := bstep (se 2 (by rfl) ⟨1423224, by rfl⟩ : syracuseStep 3795265 = 2846449) B2846449
theorem B2246987 : Blo 1330984 2246987 := bstep (se 1 (by rfl) ⟨1685240, by rfl⟩ : syracuseStep 2246987 = 3370481) B3370481
theorem B2247115 : Blo 1330984 2247115 := bstep (se 1 (by rfl) ⟨1685336, by rfl⟩ : syracuseStep 2247115 = 3370673) B3370673
theorem B2247257 : Blo 1330984 2247257 := bstep (se 2 (by rfl) ⟨842721, by rfl⟩ : syracuseStep 2247257 = 1685443) B1685443
theorem B6744707 : Blo 1330984 6744707 := bstep (se 1 (by rfl) ⟨5058530, by rfl⟩ : syracuseStep 6744707 = 10117061) B10117061
theorem B2132633 : Blo 1330984 2132633 := bstep (se 2 (by rfl) ⟨799737, by rfl⟩ : syracuseStep 2132633 = 1599475) B1599475
theorem B2247385 : Blo 1330984 2247385 := bstep (se 2 (by rfl) ⟨842769, by rfl⟩ : syracuseStep 2247385 = 1685539) B1685539
theorem B3418931 : Blo 1330984 3418931 := bstep (se 1 (by rfl) ⟨2564198, by rfl⟩ : syracuseStep 3418931 = 5128397) B5128397
theorem B4492097 : Blo 1330984 4492097 := bstep (se 2 (by rfl) ⟨1684536, by rfl⟩ : syracuseStep 4492097 = 3369073) B3369073
theorem B2845697 : Blo 1330984 2845697 := bstep (se 2 (by rfl) ⟨1067136, by rfl⟩ : syracuseStep 2845697 = 2134273) B2134273
theorem B12143681 : Blo 1330984 12143681 := bstep (se 2 (by rfl) ⟨4553880, by rfl⟩ : syracuseStep 12143681 = 9107761) B9107761
theorem B2845783 : Blo 1330984 2845783 := bstep (se 1 (by rfl) ⟨2134337, by rfl⟩ : syracuseStep 2845783 = 4268675) B4268675
theorem B6491267 : Blo 1330984 6491267 := bstep (se 1 (by rfl) ⟨4868450, by rfl⟩ : syracuseStep 6491267 = 9736901) B9736901
theorem B1518763 : Blo 1330984 1518763 := bstep (se 1 (by rfl) ⟨1139072, by rfl⟩ : syracuseStep 1518763 = 2278145) B2278145
theorem B3370187 : Blo 1330984 3370187 := bstep (se 1 (by rfl) ⟨2527640, by rfl⟩ : syracuseStep 3370187 = 5055281) B5055281
theorem B5688593 : Blo 1330984 5688593 := bstep (se 2 (by rfl) ⟨2133222, by rfl⟩ : syracuseStep 5688593 = 4266445) B4266445
theorem B2247959 : Blo 1330984 2247959 := bstep (se 1 (by rfl) ⟨1685969, by rfl⟩ : syracuseStep 2247959 = 3371939) B3371939
theorem B4492637 : Blo 1330984 4492637 := bstep (se 3 (by rfl) ⟨842369, by rfl⟩ : syracuseStep 4492637 = 1684739) B1684739
theorem B5057923 : Blo 1330984 5057923 := bstep (se 1 (by rfl) ⟨3793442, by rfl⟩ : syracuseStep 5057923 = 7586885) B7586885
theorem B8531351 : Blo 1330984 8531351 := bstep (se 1 (by rfl) ⟨6398513, by rfl⟩ : syracuseStep 8531351 = 12797027) B12797027
theorem B2248087 : Blo 1330984 2248087 := bstep (se 1 (by rfl) ⟨1686065, by rfl⟩ : syracuseStep 2248087 = 3372131) B3372131
theorem B1895833 : Blo 1330984 1895833 := bstep (se 2 (by rfl) ⟨710937, by rfl⟩ : syracuseStep 1895833 = 1421875) B1421875
theorem B11537815 : Blo 1330984 11537815 := bstep (se 1 (by rfl) ⟨8653361, by rfl⟩ : syracuseStep 11537815 = 17306723) B17306723
theorem B4804019 : Blo 1330984 4804019 := bstep (se 1 (by rfl) ⟨3603014, by rfl⟩ : syracuseStep 4804019 = 7206029) B7206029
theorem B5402285 : Blo 1330984 5402285 := bstep (se 3 (by rfl) ⟨1012928, by rfl⟩ : syracuseStep 5402285 = 2025857) B2025857
theorem B5058227 : Blo 1330984 5058227 := bstep (se 1 (by rfl) ⟨3793670, by rfl⟩ : syracuseStep 5058227 = 7587341) B7587341
theorem B9596677 : Blo 1330984 9596677 := bstep (se 4 (by rfl) ⟨899688, by rfl⟩ : syracuseStep 9596677 = 1799377) B1799377
theorem B1330987 : Blo 1330984 1330987 := bstep (se 1 (by rfl) ⟨998240, by rfl⟩ : syracuseStep 1330987 = 1996481) B1996481
theorem B4050739 : Blo 1330984 4050739 := bstep (se 1 (by rfl) ⟨3038054, by rfl⟩ : syracuseStep 4050739 = 6076109) B6076109
theorem B1330999 : Blo 1330984 1330999 := bstep (se 1 (by rfl) ⟨998249, by rfl⟩ : syracuseStep 1330999 = 1996499) B1996499
theorem B1331019 : Blo 1330984 1331019 := bstep (se 1 (by rfl) ⟨998264, by rfl⟩ : syracuseStep 1331019 = 1996529) B1996529
theorem B1331031 : Blo 1330984 1331031 := bstep (se 1 (by rfl) ⟨998273, by rfl⟩ : syracuseStep 1331031 = 1996547) B1996547
theorem B1331051 : Blo 1330984 1331051 := bstep (se 1 (by rfl) ⟨998288, by rfl⟩ : syracuseStep 1331051 = 1996577) B1996577
theorem B1331063 : Blo 1330984 1331063 := bstep (se 1 (by rfl) ⟨998297, by rfl⟩ : syracuseStep 1331063 = 1996595) B1996595
theorem B1331083 : Blo 1330984 1331083 := bstep (se 1 (by rfl) ⟨998312, by rfl⟩ : syracuseStep 1331083 = 1996625) B1996625
theorem B2846603 : Blo 1330984 2846603 := bstep (se 1 (by rfl) ⟨2134952, by rfl⟩ : syracuseStep 2846603 = 4269905) B4269905
theorem B1331095 : Blo 1330984 1331095 := bstep (se 1 (by rfl) ⟨998321, by rfl⟩ : syracuseStep 1331095 = 1996643) B1996643
theorem B1331115 : Blo 1330984 1331115 := bstep (se 1 (by rfl) ⟨998336, by rfl⟩ : syracuseStep 1331115 = 1996673) B1996673
theorem B1331127 : Blo 1330984 1331127 := bstep (se 1 (by rfl) ⟨998345, by rfl⟩ : syracuseStep 1331127 = 1996691) B1996691
theorem B1331147 : Blo 1330984 1331147 := bstep (se 1 (by rfl) ⟨998360, by rfl⟩ : syracuseStep 1331147 = 1996721) B1996721
theorem B1331159 : Blo 1330984 1331159 := bstep (se 1 (by rfl) ⟨998369, by rfl⟩ : syracuseStep 1331159 = 1996739) B1996739
theorem B2527193 : Blo 1330984 2527193 := bstep (se 2 (by rfl) ⟨947697, by rfl⟩ : syracuseStep 2527193 = 1895395) B1895395
theorem B1331179 : Blo 1330984 1331179 := bstep (se 1 (by rfl) ⟨998384, by rfl⟩ : syracuseStep 1331179 = 1996769) B1996769
theorem B1331191 : Blo 1330984 1331191 := bstep (se 1 (by rfl) ⟨998393, by rfl⟩ : syracuseStep 1331191 = 1996787) B1996787
theorem B1331211 : Blo 1330984 1331211 := bstep (se 1 (by rfl) ⟨998408, by rfl⟩ : syracuseStep 1331211 = 1996817) B1996817
theorem B2248715 : Blo 1330984 2248715 := bstep (se 1 (by rfl) ⟨1686536, by rfl⟩ : syracuseStep 2248715 = 3373073) B3373073
theorem B1331223 : Blo 1330984 1331223 := bstep (se 1 (by rfl) ⟨998417, by rfl⟩ : syracuseStep 1331223 = 1996835) B1996835
theorem B1331243 : Blo 1330984 1331243 := bstep (se 1 (by rfl) ⟨998432, by rfl⟩ : syracuseStep 1331243 = 1996865) B1996865
theorem B3199027 : Blo 1330984 3199027 := bstep (se 1 (by rfl) ⟨2399270, by rfl⟩ : syracuseStep 3199027 = 4798541) B4798541
theorem B1331255 : Blo 1330984 1331255 := bstep (se 1 (by rfl) ⟨998441, by rfl⟩ : syracuseStep 1331255 = 1996883) B1996883
theorem B7581761 : Blo 1330984 7581761 := bstep (se 2 (by rfl) ⟨2843160, by rfl⟩ : syracuseStep 7581761 = 5686321) B5686321
theorem B1331275 : Blo 1330984 1331275 := bstep (se 1 (by rfl) ⟨998456, by rfl⟩ : syracuseStep 1331275 = 1996913) B1996913
theorem B1331287 : Blo 1330984 1331287 := bstep (se 1 (by rfl) ⟨998465, by rfl⟩ : syracuseStep 1331287 = 1996931) B1996931
theorem B9605213 : Blo 1330984 9605213 := bstep (se 3 (by rfl) ⟨1800977, by rfl⟩ : syracuseStep 9605213 = 3601955) B3601955
theorem B1331307 : Blo 1330984 1331307 := bstep (se 1 (by rfl) ⟨998480, by rfl⟩ : syracuseStep 1331307 = 1996961) B1996961
theorem B1331319 : Blo 1330984 1331319 := bstep (se 1 (by rfl) ⟨998489, by rfl⟩ : syracuseStep 1331319 = 1996979) B1996979
theorem B1331339 : Blo 1330984 1331339 := bstep (se 1 (by rfl) ⟨998504, by rfl⟩ : syracuseStep 1331339 = 1997009) B1997009
theorem B2248843 : Blo 1330984 2248843 := bstep (se 1 (by rfl) ⟨1686632, by rfl⟩ : syracuseStep 2248843 = 3373265) B3373265
theorem B1331351 : Blo 1330984 1331351 := bstep (se 1 (by rfl) ⟨998513, by rfl⟩ : syracuseStep 1331351 = 1997027) B1997027
theorem B3371159 : Blo 1330984 3371159 := bstep (se 1 (by rfl) ⟨2528369, by rfl⟩ : syracuseStep 3371159 = 5056739) B5056739
theorem B1331371 : Blo 1330984 1331371 := bstep (se 1 (by rfl) ⟨998528, by rfl⟩ : syracuseStep 1331371 = 1997057) B1997057
theorem B1331383 : Blo 1330984 1331383 := bstep (se 1 (by rfl) ⟨998537, by rfl⟩ : syracuseStep 1331383 = 1997075) B1997075
theorem B1331403 : Blo 1330984 1331403 := bstep (se 1 (by rfl) ⟨998552, by rfl⟩ : syracuseStep 1331403 = 1997105) B1997105
theorem B1331415 : Blo 1330984 1331415 := bstep (se 1 (by rfl) ⟨998561, by rfl⟩ : syracuseStep 1331415 = 1997123) B1997123
theorem B1331435 : Blo 1330984 1331435 := bstep (se 1 (by rfl) ⟨998576, by rfl⟩ : syracuseStep 1331435 = 1997153) B1997153
theorem B1331447 : Blo 1330984 1331447 := bstep (se 1 (by rfl) ⟨998585, by rfl⟩ : syracuseStep 1331447 = 1997171) B1997171
theorem B1331467 : Blo 1330984 1331467 := bstep (se 1 (by rfl) ⟨998600, by rfl⟩ : syracuseStep 1331467 = 1997201) B1997201
theorem B1331479 : Blo 1330984 1331479 := bstep (se 1 (by rfl) ⟨998609, by rfl⟩ : syracuseStep 1331479 = 1997219) B1997219
theorem B2248985 : Blo 1330984 2248985 := bstep (se 2 (by rfl) ⟨843369, by rfl⟩ : syracuseStep 2248985 = 1686739) B1686739
theorem B1331499 : Blo 1330984 1331499 := bstep (se 1 (by rfl) ⟨998624, by rfl⟩ : syracuseStep 1331499 = 1997249) B1997249
theorem B1331511 : Blo 1330984 1331511 := bstep (se 1 (by rfl) ⟨998633, by rfl⟩ : syracuseStep 1331511 = 1997267) B1997267
theorem B5058881 : Blo 1330984 5058881 := bstep (se 2 (by rfl) ⟨1897080, by rfl⟩ : syracuseStep 5058881 = 3794161) B3794161
theorem B9605441 : Blo 1330984 9605441 := bstep (se 2 (by rfl) ⟨3602040, by rfl⟩ : syracuseStep 9605441 = 7204081) B7204081
theorem B1331531 : Blo 1330984 1331531 := bstep (se 1 (by rfl) ⟨998648, by rfl⟩ : syracuseStep 1331531 = 1997297) B1997297
theorem B1331543 : Blo 1330984 1331543 := bstep (se 1 (by rfl) ⟨998657, by rfl⟩ : syracuseStep 1331543 = 1997315) B1997315
theorem B6402397 : Blo 1330984 6402397 := bstep (se 3 (by rfl) ⟨1200449, by rfl⟩ : syracuseStep 6402397 = 2400899) B2400899
theorem B24285541 : Blo 1330984 24285541 := bstep (se 4 (by rfl) ⟨2276769, by rfl⟩ : syracuseStep 24285541 = 4553539) B4553539
theorem B1331563 : Blo 1330984 1331563 := bstep (se 1 (by rfl) ⟨998672, by rfl⟩ : syracuseStep 1331563 = 1997345) B1997345
theorem B1331575 : Blo 1330984 1331575 := bstep (se 1 (by rfl) ⟨998681, by rfl⟩ : syracuseStep 1331575 = 1997363) B1997363
theorem B1331595 : Blo 1330984 1331595 := bstep (se 1 (by rfl) ⟨998696, by rfl⟩ : syracuseStep 1331595 = 1997393) B1997393
theorem B4264343 : Blo 1330984 4264343 := bstep (se 1 (by rfl) ⟨3198257, by rfl⟩ : syracuseStep 4264343 = 6396515) B6396515
theorem B1331607 : Blo 1330984 1331607 := bstep (se 1 (by rfl) ⟨998705, by rfl⟩ : syracuseStep 1331607 = 1997411) B1997411
theorem B2249113 : Blo 1330984 2249113 := bstep (se 2 (by rfl) ⟨843417, by rfl⟩ : syracuseStep 2249113 = 1686835) B1686835
theorem B1331627 : Blo 1330984 1331627 := bstep (se 1 (by rfl) ⟨998720, by rfl⟩ : syracuseStep 1331627 = 1997441) B1997441
theorem B1331639 : Blo 1330984 1331639 := bstep (se 1 (by rfl) ⟨998729, by rfl⟩ : syracuseStep 1331639 = 1997459) B1997459
theorem B4493771 : Blo 1330984 4493771 := bstep (se 1 (by rfl) ⟨3370328, by rfl⟩ : syracuseStep 4493771 = 6740657) B6740657
theorem B1331659 : Blo 1330984 1331659 := bstep (se 1 (by rfl) ⟨998744, by rfl⟩ : syracuseStep 1331659 = 1997489) B1997489
theorem B1331671 : Blo 1330984 1331671 := bstep (se 1 (by rfl) ⟨998753, by rfl⟩ : syracuseStep 1331671 = 1997507) B1997507
theorem B1331691 : Blo 1330984 1331691 := bstep (se 1 (by rfl) ⟨998768, by rfl⟩ : syracuseStep 1331691 = 1997537) B1997537
theorem B1331703 : Blo 1330984 1331703 := bstep (se 1 (by rfl) ⟨998777, by rfl⟩ : syracuseStep 1331703 = 1997555) B1997555
theorem B1331723 : Blo 1330984 1331723 := bstep (se 1 (by rfl) ⟨998792, by rfl⟩ : syracuseStep 1331723 = 1997585) B1997585
theorem B1331735 : Blo 1330984 1331735 := bstep (se 1 (by rfl) ⟨998801, by rfl⟩ : syracuseStep 1331735 = 1997603) B1997603
theorem B1331755 : Blo 1330984 1331755 := bstep (se 1 (by rfl) ⟨998816, by rfl⟩ : syracuseStep 1331755 = 1997633) B1997633
theorem B1331767 : Blo 1330984 1331767 := bstep (se 1 (by rfl) ⟨998825, by rfl⟩ : syracuseStep 1331767 = 1997651) B1997651
theorem B1331787 : Blo 1330984 1331787 := bstep (se 1 (by rfl) ⟨998840, by rfl⟩ : syracuseStep 1331787 = 1997681) B1997681
theorem B1331799 : Blo 1330984 1331799 := bstep (se 1 (by rfl) ⟨998849, by rfl⟩ : syracuseStep 1331799 = 1997699) B1997699
theorem B1331819 : Blo 1330984 1331819 := bstep (se 1 (by rfl) ⟨998864, by rfl⟩ : syracuseStep 1331819 = 1997729) B1997729
theorem B2994803 : Blo 1330984 2994803 := bstep (se 1 (by rfl) ⟨2246102, by rfl⟩ : syracuseStep 2994803 = 4492205) B4492205
theorem B1331831 : Blo 1330984 1331831 := bstep (se 1 (by rfl) ⟨998873, by rfl⟩ : syracuseStep 1331831 = 1997747) B1997747
theorem B1331851 : Blo 1330984 1331851 := bstep (se 1 (by rfl) ⟨998888, by rfl⟩ : syracuseStep 1331851 = 1997777) B1997777
theorem B2994839 : Blo 1330984 2994839 := bstep (se 1 (by rfl) ⟨2246129, by rfl⟩ : syracuseStep 2994839 = 4492259) B4492259
theorem B1331863 : Blo 1330984 1331863 := bstep (se 1 (by rfl) ⟨998897, by rfl⟩ : syracuseStep 1331863 = 1997795) B1997795
theorem B1331883 : Blo 1330984 1331883 := bstep (se 1 (by rfl) ⟨998912, by rfl⟩ : syracuseStep 1331883 = 1997825) B1997825
theorem B1331895 : Blo 1330984 1331895 := bstep (se 1 (by rfl) ⟨998921, by rfl⟩ : syracuseStep 1331895 = 1997843) B1997843
theorem B1331915 : Blo 1330984 1331915 := bstep (se 1 (by rfl) ⟨998936, by rfl⟩ : syracuseStep 1331915 = 1997873) B1997873
theorem B12800717 : Blo 1330984 12800717 := bstep (se 3 (by rfl) ⟨2400134, by rfl⟩ : syracuseStep 12800717 = 4800269) B4800269
theorem B1331927 : Blo 1330984 1331927 := bstep (se 1 (by rfl) ⟨998945, by rfl⟩ : syracuseStep 1331927 = 1997891) B1997891
theorem B4494041 : Blo 1330984 4494041 := bstep (se 2 (by rfl) ⟨1685265, by rfl⟩ : syracuseStep 4494041 = 3370531) B3370531
theorem B1897177 : Blo 1330984 1897177 := bstep (se 2 (by rfl) ⟨711441, by rfl⟩ : syracuseStep 1897177 = 1422883) B1422883
theorem B7205593 : Blo 1330984 7205593 := bstep (se 2 (by rfl) ⟨2702097, by rfl⟩ : syracuseStep 7205593 = 5404195) B5404195
theorem B1331947 : Blo 1330984 1331947 := bstep (se 1 (by rfl) ⟨998960, by rfl⟩ : syracuseStep 1331947 = 1997921) B1997921
theorem B1331959 : Blo 1330984 1331959 := bstep (se 1 (by rfl) ⟨998969, by rfl⟩ : syracuseStep 1331959 = 1997939) B1997939
theorem B17068805 : Blo 1330984 17068805 := bstep (se 4 (by rfl) ⟨1600200, by rfl⟩ : syracuseStep 17068805 = 3200401) B3200401
theorem B1331979 : Blo 1330984 1331979 := bstep (se 1 (by rfl) ⟨998984, by rfl⟩ : syracuseStep 1331979 = 1997969) B1997969
theorem B1331991 : Blo 1330984 1331991 := bstep (se 1 (by rfl) ⟨998993, by rfl⟩ : syracuseStep 1331991 = 1997987) B1997987
theorem B1332011 : Blo 1330984 1332011 := bstep (se 1 (by rfl) ⟨999008, by rfl⟩ : syracuseStep 1332011 = 1998017) B1998017
theorem B3371827 : Blo 1330984 3371827 := bstep (se 1 (by rfl) ⟨2528870, by rfl⟩ : syracuseStep 3371827 = 5057741) B5057741
theorem B1332023 : Blo 1330984 1332023 := bstep (se 1 (by rfl) ⟨999017, by rfl⟩ : syracuseStep 1332023 = 1998035) B1998035
theorem B2995019 : Blo 1330984 2995019 := bstep (se 1 (by rfl) ⟨2246264, by rfl⟩ : syracuseStep 2995019 = 4492529) B4492529
theorem B1332043 : Blo 1330984 1332043 := bstep (se 1 (by rfl) ⟨999032, by rfl⟩ : syracuseStep 1332043 = 1998065) B1998065
theorem B1897291 : Blo 1330984 1897291 := bstep (se 1 (by rfl) ⟨1422968, by rfl⟩ : syracuseStep 1897291 = 2845937) B2845937
theorem B1332055 : Blo 1330984 1332055 := bstep (se 1 (by rfl) ⟨999041, by rfl⟩ : syracuseStep 1332055 = 1998083) B1998083
theorem B5403485 : Blo 1330984 5403485 := bstep (se 3 (by rfl) ⟨1013153, by rfl⟩ : syracuseStep 5403485 = 2026307) B2026307
theorem B1332075 : Blo 1330984 1332075 := bstep (se 1 (by rfl) ⟨999056, by rfl⟩ : syracuseStep 1332075 = 1998113) B1998113
theorem B1332087 : Blo 1330984 1332087 := bstep (se 1 (by rfl) ⟨999065, by rfl⟩ : syracuseStep 1332087 = 1998131) B1998131
theorem B2995073 : Blo 1330984 2995073 := bstep (se 2 (by rfl) ⟨1123152, by rfl⟩ : syracuseStep 2995073 = 2246305) B2246305
theorem B1332107 : Blo 1330984 1332107 := bstep (se 1 (by rfl) ⟨999080, by rfl⟩ : syracuseStep 1332107 = 1998161) B1998161
theorem B1332119 : Blo 1330984 1332119 := bstep (se 1 (by rfl) ⟨999089, by rfl⟩ : syracuseStep 1332119 = 1998179) B1998179
theorem B1332139 : Blo 1330984 1332139 := bstep (se 1 (by rfl) ⟨999104, by rfl⟩ : syracuseStep 1332139 = 1998209) B1998209
theorem B4264883 : Blo 1330984 4264883 := bstep (se 1 (by rfl) ⟨3198662, by rfl⟩ : syracuseStep 4264883 = 6397325) B6397325
theorem B1332151 : Blo 1330984 1332151 := bstep (se 1 (by rfl) ⟨999113, by rfl⟩ : syracuseStep 1332151 = 1998227) B1998227
theorem B3371969 : Blo 1330984 3371969 := bstep (se 2 (by rfl) ⟨1264488, by rfl⟩ : syracuseStep 3371969 = 2528977) B2528977
theorem B1332171 : Blo 1330984 1332171 := bstep (se 1 (by rfl) ⟨999128, by rfl⟩ : syracuseStep 1332171 = 1998257) B1998257
theorem B1332183 : Blo 1330984 1332183 := bstep (se 1 (by rfl) ⟨999137, by rfl⟩ : syracuseStep 1332183 = 1998275) B1998275
theorem B12809177 : Blo 1330984 12809177 := bstep (se 2 (by rfl) ⟨4803441, by rfl⟩ : syracuseStep 12809177 = 9606883) B9606883
theorem B1332203 : Blo 1330984 1332203 := bstep (se 1 (by rfl) ⟨999152, by rfl⟩ : syracuseStep 1332203 = 1998305) B1998305
theorem B1332215 : Blo 1330984 1332215 := bstep (se 1 (by rfl) ⟨999161, by rfl⟩ : syracuseStep 1332215 = 1998323) B1998323
theorem B1332235 : Blo 1330984 1332235 := bstep (se 1 (by rfl) ⟨999176, by rfl⟩ : syracuseStep 1332235 = 1998353) B1998353
theorem B19215377 : Blo 1330984 19215377 := bstep (se 2 (by rfl) ⟨7205766, by rfl⟩ : syracuseStep 19215377 = 14411533) B14411533
theorem B1332247 : Blo 1330984 1332247 := bstep (se 1 (by rfl) ⟨999185, by rfl⟩ : syracuseStep 1332247 = 1998371) B1998371
theorem B1332267 : Blo 1330984 1332267 := bstep (se 1 (by rfl) ⟨999200, by rfl⟩ : syracuseStep 1332267 = 1998401) B1998401
theorem B1332279 : Blo 1330984 1332279 := bstep (se 1 (by rfl) ⟨999209, by rfl⟩ : syracuseStep 1332279 = 1998419) B1998419
theorem B1332299 : Blo 1330984 1332299 := bstep (se 1 (by rfl) ⟨999224, by rfl⟩ : syracuseStep 1332299 = 1998449) B1998449
theorem B1684567 : Blo 1330984 1684567 := bstep (se 1 (by rfl) ⟨1263425, by rfl⟩ : syracuseStep 1684567 = 2526851) B2526851
theorem B1332311 : Blo 1330984 1332311 := bstep (se 1 (by rfl) ⟨999233, by rfl⟩ : syracuseStep 1332311 = 1998467) B1998467
theorem B2995289 : Blo 1330984 2995289 := bstep (se 2 (by rfl) ⟨1123233, by rfl⟩ : syracuseStep 2995289 = 2246467) B2246467
theorem B6739037 : Blo 1330984 6739037 := bstep (se 3 (by rfl) ⟨1263569, by rfl⟩ : syracuseStep 6739037 = 2527139) B2527139
theorem B1332331 : Blo 1330984 1332331 := bstep (se 1 (by rfl) ⟨999248, by rfl⟩ : syracuseStep 1332331 = 1998497) B1998497
theorem B1332343 : Blo 1330984 1332343 := bstep (se 1 (by rfl) ⟨999257, by rfl⟩ : syracuseStep 1332343 = 1998515) B1998515
theorem B1332363 : Blo 1330984 1332363 := bstep (se 1 (by rfl) ⟨999272, by rfl⟩ : syracuseStep 1332363 = 1998545) B1998545
theorem B5403793 : Blo 1330984 5403793 := bstep (se 2 (by rfl) ⟨2026422, by rfl⟩ : syracuseStep 5403793 = 4052845) B4052845
theorem B1332375 : Blo 1330984 1332375 := bstep (se 1 (by rfl) ⟨999281, by rfl⟩ : syracuseStep 1332375 = 1998563) B1998563
theorem B1332395 : Blo 1330984 1332395 := bstep (se 1 (by rfl) ⟨999296, by rfl⟩ : syracuseStep 1332395 = 1998593) B1998593
theorem B2995379 : Blo 1330984 2995379 := bstep (se 1 (by rfl) ⟨2246534, by rfl⟩ : syracuseStep 2995379 = 4493069) B4493069
theorem B1332407 : Blo 1330984 1332407 := bstep (se 1 (by rfl) ⟨999305, by rfl⟩ : syracuseStep 1332407 = 1998611) B1998611
theorem B1332427 : Blo 1330984 1332427 := bstep (se 1 (by rfl) ⟨999320, by rfl⟩ : syracuseStep 1332427 = 1998641) B1998641
theorem B2995415 : Blo 1330984 2995415 := bstep (se 1 (by rfl) ⟨2246561, by rfl⟩ : syracuseStep 2995415 = 4493123) B4493123
theorem B1332439 : Blo 1330984 1332439 := bstep (se 1 (by rfl) ⟨999329, by rfl⟩ : syracuseStep 1332439 = 1998659) B1998659
theorem B1332459 : Blo 1330984 1332459 := bstep (se 1 (by rfl) ⟨999344, by rfl⟩ : syracuseStep 1332459 = 1998689) B1998689
theorem B1332471 : Blo 1330984 1332471 := bstep (se 1 (by rfl) ⟨999353, by rfl⟩ : syracuseStep 1332471 = 1998707) B1998707
theorem B1332491 : Blo 1330984 1332491 := bstep (se 1 (by rfl) ⟨999368, by rfl⟩ : syracuseStep 1332491 = 1998737) B1998737
theorem B1332503 : Blo 1330984 1332503 := bstep (se 1 (by rfl) ⟨999377, by rfl⟩ : syracuseStep 1332503 = 1998755) B1998755
theorem B1332523 : Blo 1330984 1332523 := bstep (se 1 (by rfl) ⟨999392, by rfl⟩ : syracuseStep 1332523 = 1998785) B1998785
theorem B1332535 : Blo 1330984 1332535 := bstep (se 1 (by rfl) ⟨999401, by rfl⟩ : syracuseStep 1332535 = 1998803) B1998803
theorem B1332555 : Blo 1330984 1332555 := bstep (se 1 (by rfl) ⟨999416, by rfl⟩ : syracuseStep 1332555 = 1998833) B1998833
theorem B1332567 : Blo 1330984 1332567 := bstep (se 1 (by rfl) ⟨999425, by rfl⟩ : syracuseStep 1332567 = 1998851) B1998851
theorem B22771043 : Blo 1330984 22771043 := bstep (se 1 (by rfl) ⟨17078282, by rfl⟩ : syracuseStep 22771043 = 34156565) B34156565
theorem B1332587 : Blo 1330984 1332587 := bstep (se 1 (by rfl) ⟨999440, by rfl⟩ : syracuseStep 1332587 = 1998881) B1998881
theorem B1332599 : Blo 1330984 1332599 := bstep (se 1 (by rfl) ⟨999449, by rfl⟩ : syracuseStep 1332599 = 1998899) B1998899
theorem B2995595 : Blo 1330984 2995595 := bstep (se 1 (by rfl) ⟨2246696, by rfl⟩ : syracuseStep 2995595 = 4493393) B4493393
theorem B2528651 : Blo 1330984 2528651 := bstep (se 1 (by rfl) ⟨1896488, by rfl⟩ : syracuseStep 2528651 = 3792977) B3792977
theorem B1332619 : Blo 1330984 1332619 := bstep (se 1 (by rfl) ⟨999464, by rfl⟩ : syracuseStep 1332619 = 1998929) B1998929
theorem B4494743 : Blo 1330984 4494743 := bstep (se 1 (by rfl) ⟨3371057, by rfl⟩ : syracuseStep 4494743 = 6742115) B6742115
theorem B1332631 : Blo 1330984 1332631 := bstep (se 1 (by rfl) ⟨999473, by rfl⟩ : syracuseStep 1332631 = 1998947) B1998947
theorem B1332651 : Blo 1330984 1332651 := bstep (se 1 (by rfl) ⟨999488, by rfl⟩ : syracuseStep 1332651 = 1998977) B1998977
theorem B1332663 : Blo 1330984 1332663 := bstep (se 1 (by rfl) ⟨999497, by rfl⟩ : syracuseStep 1332663 = 1998995) B1998995
theorem B2995649 : Blo 1330984 2995649 := bstep (se 2 (by rfl) ⟨1123368, by rfl⟩ : syracuseStep 2995649 = 2246737) B2246737
theorem B1332683 : Blo 1330984 1332683 := bstep (se 1 (by rfl) ⟨999512, by rfl⟩ : syracuseStep 1332683 = 1999025) B1999025
theorem B1332695 : Blo 1330984 1332695 := bstep (se 1 (by rfl) ⟨999521, by rfl⟩ : syracuseStep 1332695 = 1999043) B1999043
theorem B1332715 : Blo 1330984 1332715 := bstep (se 1 (by rfl) ⟨999536, by rfl⟩ : syracuseStep 1332715 = 1999073) B1999073
theorem B1332727 : Blo 1330984 1332727 := bstep (se 1 (by rfl) ⟨999545, by rfl⟩ : syracuseStep 1332727 = 1999091) B1999091
theorem B1332747 : Blo 1330984 1332747 := bstep (se 1 (by rfl) ⟨999560, by rfl⟩ : syracuseStep 1332747 = 1999121) B1999121
theorem B7591441 : Blo 1330984 7591441 := bstep (se 2 (by rfl) ⟨2846790, by rfl⟩ : syracuseStep 7591441 = 5693581) B5693581
theorem B1332759 : Blo 1330984 1332759 := bstep (se 1 (by rfl) ⟨999569, by rfl⟩ : syracuseStep 1332759 = 1999139) B1999139
theorem B5060141 : Blo 1330984 5060141 := bstep (se 3 (by rfl) ⟨948776, by rfl⟩ : syracuseStep 5060141 = 1897553) B1897553
theorem B1332779 : Blo 1330984 1332779 := bstep (se 1 (by rfl) ⟨999584, by rfl⟩ : syracuseStep 1332779 = 1999169) B1999169
theorem B1332791 : Blo 1330984 1332791 := bstep (se 1 (by rfl) ⟨999593, by rfl⟩ : syracuseStep 1332791 = 1999187) B1999187
theorem B2528833 : Blo 1330984 2528833 := bstep (se 2 (by rfl) ⟨948312, by rfl⟩ : syracuseStep 2528833 = 1896625) B1896625
theorem B5060171 : Blo 1330984 5060171 := bstep (se 1 (by rfl) ⟨3795128, by rfl⟩ : syracuseStep 5060171 = 7590257) B7590257
theorem B1332811 : Blo 1330984 1332811 := bstep (se 1 (by rfl) ⟨999608, by rfl⟩ : syracuseStep 1332811 = 1999217) B1999217
theorem B1332823 : Blo 1330984 1332823 := bstep (se 1 (by rfl) ⟨999617, by rfl⟩ : syracuseStep 1332823 = 1999235) B1999235
theorem B4265561 : Blo 1330984 4265561 := bstep (se 2 (by rfl) ⟨1599585, by rfl⟩ : syracuseStep 4265561 = 3199171) B3199171
theorem B5690969 : Blo 1330984 5690969 := bstep (se 2 (by rfl) ⟨2134113, by rfl⟩ : syracuseStep 5690969 = 4268227) B4268227
theorem B1332843 : Blo 1330984 1332843 := bstep (se 1 (by rfl) ⟨999632, by rfl⟩ : syracuseStep 1332843 = 1999265) B1999265
theorem B1332855 : Blo 1330984 1332855 := bstep (se 1 (by rfl) ⟨999641, by rfl⟩ : syracuseStep 1332855 = 1999283) B1999283
theorem B1332875 : Blo 1330984 1332875 := bstep (se 1 (by rfl) ⟨999656, by rfl⟩ : syracuseStep 1332875 = 1999313) B1999313
theorem B1332887 : Blo 1330984 1332887 := bstep (se 1 (by rfl) ⟨999665, by rfl⟩ : syracuseStep 1332887 = 1999331) B1999331
theorem B2995865 : Blo 1330984 2995865 := bstep (se 2 (by rfl) ⟨1123449, by rfl⟩ : syracuseStep 2995865 = 2246899) B2246899
theorem B1332907 : Blo 1330984 1332907 := bstep (se 1 (by rfl) ⟨999680, by rfl⟩ : syracuseStep 1332907 = 1999361) B1999361
theorem B5691053 : Blo 1330984 5691053 := bstep (se 3 (by rfl) ⟨1067072, by rfl⟩ : syracuseStep 5691053 = 2134145) B2134145
theorem B1332919 : Blo 1330984 1332919 := bstep (se 1 (by rfl) ⟨999689, by rfl⟩ : syracuseStep 1332919 = 1999379) B1999379
theorem B1332939 : Blo 1330984 1332939 := bstep (se 1 (by rfl) ⟨999704, by rfl⟩ : syracuseStep 1332939 = 1999409) B1999409
theorem B1332951 : Blo 1330984 1332951 := bstep (se 1 (by rfl) ⟨999713, by rfl⟩ : syracuseStep 1332951 = 1999427) B1999427
theorem B1996505 : Blo 1330984 1996505 := bstep (se 2 (by rfl) ⟨748689, by rfl⟩ : syracuseStep 1996505 = 1497379) B1497379
theorem B1332971 : Blo 1330984 1332971 := bstep (se 1 (by rfl) ⟨999728, by rfl⟩ : syracuseStep 1332971 = 1999457) B1999457
theorem B2995955 : Blo 1330984 2995955 := bstep (se 1 (by rfl) ⟨2246966, by rfl⟩ : syracuseStep 2995955 = 4493933) B4493933
theorem B1332983 : Blo 1330984 1332983 := bstep (se 1 (by rfl) ⟨999737, by rfl⟩ : syracuseStep 1332983 = 1999475) B1999475
theorem B2995991 : Blo 1330984 2995991 := bstep (se 1 (by rfl) ⟨2246993, by rfl⟩ : syracuseStep 2995991 = 4493987) B4493987
theorem B17061677 : Blo 1330984 17061677 := bstep (se 3 (by rfl) ⟨3199064, by rfl⟩ : syracuseStep 17061677 = 6398129) B6398129
theorem B5125933 : Blo 1330984 5125933 := bstep (se 3 (by rfl) ⟨961112, by rfl⟩ : syracuseStep 5125933 = 1922225) B1922225
theorem B1996619 : Blo 1330984 1996619 := bstep (se 1 (by rfl) ⟨1497464, by rfl⟩ : syracuseStep 1996619 = 2994929) B2994929
theorem B1996631 : Blo 1330984 1996631 := bstep (se 1 (by rfl) ⟨1497473, by rfl⟩ : syracuseStep 1996631 = 2994947) B2994947
theorem B1685387 : Blo 1330984 1685387 := bstep (se 1 (by rfl) ⟨1264040, by rfl⟩ : syracuseStep 1685387 = 2528081) B2528081
theorem B1996697 : Blo 1330984 1996697 := bstep (se 2 (by rfl) ⟨748761, by rfl⟩ : syracuseStep 1996697 = 1497523) B1497523
theorem B8550323 : Blo 1330984 8550323 := bstep (se 1 (by rfl) ⟨6412742, by rfl⟩ : syracuseStep 8550323 = 12825485) B12825485
theorem B4495283 : Blo 1330984 4495283 := bstep (se 1 (by rfl) ⟨3371462, by rfl⟩ : syracuseStep 4495283 = 6742925) B6742925
theorem B2996171 : Blo 1330984 2996171 := bstep (se 1 (by rfl) ⟨2247128, by rfl⟩ : syracuseStep 2996171 = 4494257) B4494257
theorem B5404619 : Blo 1330984 5404619 := bstep (se 1 (by rfl) ⟨4053464, by rfl⟩ : syracuseStep 5404619 = 8106929) B8106929
theorem B9598925 : Blo 1330984 9598925 := bstep (se 3 (by rfl) ⟨1799798, by rfl⟩ : syracuseStep 9598925 = 3599597) B3599597
theorem B2996225 : Blo 1330984 2996225 := bstep (se 2 (by rfl) ⟨1123584, by rfl⟩ : syracuseStep 2996225 = 2247169) B2247169
theorem B2529281 : Blo 1330984 2529281 := bstep (se 2 (by rfl) ⟨948480, by rfl⟩ : syracuseStep 2529281 = 1896961) B1896961
theorem B1996811 : Blo 1330984 1996811 := bstep (se 1 (by rfl) ⟨1497608, by rfl⟩ : syracuseStep 1996811 = 2995217) B2995217
theorem B1996823 : Blo 1330984 1996823 := bstep (se 1 (by rfl) ⟨1497617, by rfl⟩ : syracuseStep 1996823 = 2995235) B2995235
theorem B10115117 : Blo 1330984 10115117 := bstep (se 3 (by rfl) ⟨1896584, by rfl⟩ : syracuseStep 10115117 = 3793169) B3793169
theorem B17291339 : Blo 1330984 17291339 := bstep (se 1 (by rfl) ⟨12968504, by rfl⟩ : syracuseStep 17291339 = 25937009) B25937009
theorem B3790937 : Blo 1330984 3790937 := bstep (se 2 (by rfl) ⟨1421601, by rfl⟩ : syracuseStep 3790937 = 2843203) B2843203
theorem B1996889 : Blo 1330984 1996889 := bstep (se 2 (by rfl) ⟨748833, by rfl⟩ : syracuseStep 1996889 = 1497667) B1497667
theorem B9599153 : Blo 1330984 9599153 := bstep (se 2 (by rfl) ⟨3599682, by rfl⟩ : syracuseStep 9599153 = 7199365) B7199365
theorem B3373235 : Blo 1330984 3373235 := bstep (se 1 (by rfl) ⟨2529926, by rfl⟩ : syracuseStep 3373235 = 5059853) B5059853
theorem B4495553 : Blo 1330984 4495553 := bstep (se 2 (by rfl) ⟨1685832, by rfl⟩ : syracuseStep 4495553 = 3371665) B3371665
theorem B1997003 : Blo 1330984 1997003 := bstep (se 1 (by rfl) ⟨1497752, by rfl⟩ : syracuseStep 1997003 = 2995505) B2995505
theorem B1997015 : Blo 1330984 1997015 := bstep (se 1 (by rfl) ⟨1497761, by rfl⟩ : syracuseStep 1997015 = 2995523) B2995523
theorem B2996441 : Blo 1330984 2996441 := bstep (se 2 (by rfl) ⟨1123665, by rfl⟩ : syracuseStep 2996441 = 2247331) B2247331
theorem B5060825 : Blo 1330984 5060825 := bstep (se 2 (by rfl) ⟨1897809, by rfl⟩ : syracuseStep 5060825 = 3795619) B3795619
theorem B1997081 : Blo 1330984 1997081 := bstep (se 2 (by rfl) ⟨748905, by rfl⟩ : syracuseStep 1997081 = 1497811) B1497811
theorem B2996531 : Blo 1330984 2996531 := bstep (se 1 (by rfl) ⟨2247398, by rfl⟩ : syracuseStep 2996531 = 4494797) B4494797
theorem B6830411 : Blo 1330984 6830411 := bstep (se 1 (by rfl) ⟨5122808, by rfl⟩ : syracuseStep 6830411 = 10245617) B10245617
theorem B2996567 : Blo 1330984 2996567 := bstep (se 1 (by rfl) ⟨2247425, by rfl⟩ : syracuseStep 2996567 = 4494851) B4494851
theorem B2529623 : Blo 1330984 2529623 := bstep (se 1 (by rfl) ⟨1897217, by rfl⟩ : syracuseStep 2529623 = 3794435) B3794435
theorem B1497451 : Blo 1330984 1497451 := bstep (se 1 (by rfl) ⟨1123088, by rfl⟩ : syracuseStep 1497451 = 2246177) B2246177
theorem B1997195 : Blo 1330984 1997195 := bstep (se 1 (by rfl) ⟨1497896, by rfl⟩ : syracuseStep 1997195 = 2995793) B2995793
theorem B1997207 : Blo 1330984 1997207 := bstep (se 1 (by rfl) ⟨1497905, by rfl⟩ : syracuseStep 1997207 = 2995811) B2995811
theorem B7584151 : Blo 1330984 7584151 := bstep (se 1 (by rfl) ⟨5688113, by rfl⟩ : syracuseStep 7584151 = 11376227) B11376227
theorem B10107341 : Blo 1330984 10107341 := bstep (se 3 (by rfl) ⟨1895126, by rfl⟩ : syracuseStep 10107341 = 3790253) B3790253
theorem B1497559 : Blo 1330984 1497559 := bstep (se 1 (by rfl) ⟨1123169, by rfl⟩ : syracuseStep 1497559 = 2246339) B2246339
theorem B1997273 : Blo 1330984 1997273 := bstep (se 2 (by rfl) ⟨748977, by rfl⟩ : syracuseStep 1997273 = 1497955) B1497955
theorem B2996747 : Blo 1330984 2996747 := bstep (se 1 (by rfl) ⟨2247560, by rfl⟩ : syracuseStep 2996747 = 4495121) B4495121
theorem B5061143 : Blo 1330984 5061143 := bstep (se 1 (by rfl) ⟨3795857, by rfl⟩ : syracuseStep 5061143 = 7591715) B7591715
theorem B2996801 : Blo 1330984 2996801 := bstep (se 2 (by rfl) ⟨1123800, by rfl⟩ : syracuseStep 2996801 = 2247601) B2247601
theorem B1997387 : Blo 1330984 1997387 := bstep (se 1 (by rfl) ⟨1498040, by rfl⟩ : syracuseStep 1997387 = 2996081) B2996081
theorem B1686091 : Blo 1330984 1686091 := bstep (se 1 (by rfl) ⟨1264568, by rfl⟩ : syracuseStep 1686091 = 2529137) B2529137
theorem B1997399 : Blo 1330984 1997399 := bstep (se 1 (by rfl) ⟨1498049, by rfl⟩ : syracuseStep 1997399 = 2996099) B2996099
theorem B1497739 : Blo 1330984 1497739 := bstep (se 1 (by rfl) ⟨1123304, by rfl⟩ : syracuseStep 1497739 = 2246609) B2246609
theorem B1997465 : Blo 1330984 1997465 := bstep (se 2 (by rfl) ⟨749049, by rfl⟩ : syracuseStep 1997465 = 1498099) B1498099
theorem B3373771 : Blo 1330984 3373771 := bstep (se 1 (by rfl) ⟨2530328, by rfl⟩ : syracuseStep 3373771 = 5060657) B5060657
theorem B4496093 : Blo 1330984 4496093 := bstep (se 3 (by rfl) ⟨843017, by rfl⟩ : syracuseStep 4496093 = 1686035) B1686035
theorem B1497847 : Blo 1330984 1497847 := bstep (se 1 (by rfl) ⟨1123385, by rfl⟩ : syracuseStep 1497847 = 2246771) B2246771
theorem B1997579 : Blo 1330984 1997579 := bstep (se 1 (by rfl) ⟨1498184, by rfl⟩ : syracuseStep 1997579 = 2996369) B2996369
theorem B1997591 : Blo 1330984 1997591 := bstep (se 1 (by rfl) ⟨1498193, by rfl⟩ : syracuseStep 1997591 = 2996387) B2996387
theorem B2997017 : Blo 1330984 2997017 := bstep (se 2 (by rfl) ⟨1123881, by rfl⟩ : syracuseStep 2997017 = 2247763) B2247763
theorem B4266803 : Blo 1330984 4266803 := bstep (se 1 (by rfl) ⟨3200102, by rfl⟩ : syracuseStep 4266803 = 6400205) B6400205
theorem B1686359 : Blo 1330984 1686359 := bstep (se 1 (by rfl) ⟨1264769, by rfl⟩ : syracuseStep 1686359 = 2529539) B2529539
theorem B1997657 : Blo 1330984 1997657 := bstep (se 2 (by rfl) ⟨749121, by rfl⟩ : syracuseStep 1997657 = 1498243) B1498243
theorem B3373913 : Blo 1330984 3373913 := bstep (se 2 (by rfl) ⟨1265217, by rfl⟩ : syracuseStep 3373913 = 2530435) B2530435
theorem B2997107 : Blo 1330984 2997107 := bstep (se 1 (by rfl) ⟨2247830, by rfl⟩ : syracuseStep 2997107 = 4495661) B4495661
theorem B2997143 : Blo 1330984 2997143 := bstep (se 1 (by rfl) ⟨2247857, by rfl⟩ : syracuseStep 2997143 = 4495715) B4495715
theorem B1498027 : Blo 1330984 1498027 := bstep (se 1 (by rfl) ⟨1123520, by rfl⟩ : syracuseStep 1498027 = 2247041) B2247041
theorem B10107827 : Blo 1330984 10107827 := bstep (se 1 (by rfl) ⟨7580870, by rfl⟩ : syracuseStep 10107827 = 15161741) B15161741
theorem B1997771 : Blo 1330984 1997771 := bstep (se 1 (by rfl) ⟨1498328, by rfl⟩ : syracuseStep 1997771 = 2996657) B2996657
theorem B1997783 : Blo 1330984 1997783 := bstep (se 1 (by rfl) ⟨1498337, by rfl⟩ : syracuseStep 1997783 = 2996675) B2996675
theorem B2530291 : Blo 1330984 2530291 := bstep (se 1 (by rfl) ⟨1897718, by rfl⟩ : syracuseStep 2530291 = 3795437) B3795437
theorem B1498135 : Blo 1330984 1498135 := bstep (se 1 (by rfl) ⟨1123601, by rfl⟩ : syracuseStep 1498135 = 2247203) B2247203
theorem B1997849 : Blo 1330984 1997849 := bstep (se 2 (by rfl) ⟨749193, by rfl⟩ : syracuseStep 1997849 = 1498387) B1498387
theorem B12155939 : Blo 1330984 12155939 := bstep (se 1 (by rfl) ⟨9116954, by rfl⟩ : syracuseStep 12155939 = 18233909) B18233909
theorem B2997323 : Blo 1330984 2997323 := bstep (se 1 (by rfl) ⟨2247992, by rfl⟩ : syracuseStep 2997323 = 4495985) B4495985
theorem B2563159 : Blo 1330984 2563159 := bstep (se 1 (by rfl) ⟨1922369, by rfl⟩ : syracuseStep 2563159 = 3844739) B3844739
theorem B2997377 : Blo 1330984 2997377 := bstep (se 2 (by rfl) ⟨1124016, by rfl⟩ : syracuseStep 2997377 = 2248033) B2248033
theorem B1997963 : Blo 1330984 1997963 := bstep (se 1 (by rfl) ⟨1498472, by rfl⟩ : syracuseStep 1997963 = 2996945) B2996945
theorem B6741143 : Blo 1330984 6741143 := bstep (se 1 (by rfl) ⟨5055857, by rfl⟩ : syracuseStep 6741143 = 10111715) B10111715
theorem B1997975 : Blo 1330984 1997975 := bstep (se 1 (by rfl) ⟨1498481, by rfl⟩ : syracuseStep 1997975 = 2996963) B2996963
theorem B8101043 : Blo 1330984 8101043 := bstep (se 1 (by rfl) ⟨6075782, by rfl⟩ : syracuseStep 8101043 = 12151565) B12151565
theorem B4799681 : Blo 1330984 4799681 := bstep (se 2 (by rfl) ⟨1799880, by rfl⟩ : syracuseStep 4799681 = 3599761) B3599761
theorem B1498315 : Blo 1330984 1498315 := bstep (se 1 (by rfl) ⟨1123736, by rfl⟩ : syracuseStep 1498315 = 2247473) B2247473
theorem B1998041 : Blo 1330984 1998041 := bstep (se 2 (by rfl) ⟨749265, by rfl⟩ : syracuseStep 1998041 = 1498531) B1498531
theorem B1498423 : Blo 1330984 1498423 := bstep (se 1 (by rfl) ⟨1123817, by rfl⟩ : syracuseStep 1498423 = 2247635) B2247635
theorem B1998155 : Blo 1330984 1998155 := bstep (se 1 (by rfl) ⟨1498616, by rfl⟩ : syracuseStep 1998155 = 2997233) B2997233
theorem B1998167 : Blo 1330984 1998167 := bstep (se 1 (by rfl) ⟨1498625, by rfl⟩ : syracuseStep 1998167 = 2997251) B2997251
theorem B2997593 : Blo 1330984 2997593 := bstep (se 2 (by rfl) ⟨1124097, by rfl⟩ : syracuseStep 2997593 = 2248195) B2248195
theorem B1998233 : Blo 1330984 1998233 := bstep (se 2 (by rfl) ⟨749337, by rfl⟩ : syracuseStep 1998233 = 1498675) B1498675
theorem B2997683 : Blo 1330984 2997683 := bstep (se 1 (by rfl) ⟨2248262, by rfl⟩ : syracuseStep 2997683 = 4496525) B4496525
theorem B2997719 : Blo 1330984 2997719 := bstep (se 1 (by rfl) ⟨2248289, by rfl⟩ : syracuseStep 2997719 = 4496579) B4496579
theorem B3792349 : Blo 1330984 3792349 := bstep (se 3 (by rfl) ⟨711065, by rfl⟩ : syracuseStep 3792349 = 1422131) B1422131
theorem B1498603 : Blo 1330984 1498603 := bstep (se 1 (by rfl) ⟨1123952, by rfl⟩ : syracuseStep 1498603 = 2247905) B2247905
theorem B1998347 : Blo 1330984 1998347 := bstep (se 1 (by rfl) ⟨1498760, by rfl⟩ : syracuseStep 1998347 = 2997521) B2997521
theorem B1998359 : Blo 1330984 1998359 := bstep (se 1 (by rfl) ⟨1498769, by rfl⟩ : syracuseStep 1998359 = 2997539) B2997539
theorem B1498711 : Blo 1330984 1498711 := bstep (se 1 (by rfl) ⟨1124033, by rfl⟩ : syracuseStep 1498711 = 2248067) B2248067
theorem B1998425 : Blo 1330984 1998425 := bstep (se 2 (by rfl) ⟨749409, by rfl⟩ : syracuseStep 1998425 = 1498819) B1498819
theorem B2997899 : Blo 1330984 2997899 := bstep (se 1 (by rfl) ⟨2248424, by rfl⟩ : syracuseStep 2997899 = 4496849) B4496849
theorem B3792577 : Blo 1330984 3792577 := bstep (se 2 (by rfl) ⟨1422216, by rfl⟩ : syracuseStep 3792577 = 2844433) B2844433
theorem B2997953 : Blo 1330984 2997953 := bstep (se 2 (by rfl) ⟨1124232, by rfl⟩ : syracuseStep 2997953 = 2248465) B2248465
theorem B1998539 : Blo 1330984 1998539 := bstep (se 1 (by rfl) ⟨1498904, by rfl⟩ : syracuseStep 1998539 = 2997809) B2997809
theorem B1998551 : Blo 1330984 1998551 := bstep (se 1 (by rfl) ⟨1498913, by rfl⟩ : syracuseStep 1998551 = 2997827) B2997827
theorem B1498891 : Blo 1330984 1498891 := bstep (se 1 (by rfl) ⟨1124168, by rfl⟩ : syracuseStep 1498891 = 2248337) B2248337
theorem B1998617 : Blo 1330984 1998617 := bstep (se 2 (by rfl) ⟨749481, by rfl⟩ : syracuseStep 1998617 = 1498963) B1498963
theorem B4497227 : Blo 1330984 4497227 := bstep (se 1 (by rfl) ⟨3372920, by rfl⟩ : syracuseStep 4497227 = 6745841) B6745841
theorem B2277209 : Blo 1330984 2277209 := bstep (se 2 (by rfl) ⟨853953, by rfl⟩ : syracuseStep 2277209 = 1707907) B1707907
theorem B7298909 : Blo 1330984 7298909 := bstep (se 3 (by rfl) ⟨1368545, by rfl⟩ : syracuseStep 7298909 = 2737091) B2737091
theorem B1498999 : Blo 1330984 1498999 := bstep (se 1 (by rfl) ⟨1124249, by rfl⟩ : syracuseStep 1498999 = 2248499) B2248499
theorem B5054339 : Blo 1330984 5054339 := bstep (se 1 (by rfl) ⟨3790754, by rfl⟩ : syracuseStep 5054339 = 7581509) B7581509
theorem B1998731 : Blo 1330984 1998731 := bstep (se 1 (by rfl) ⟨1499048, by rfl⟩ : syracuseStep 1998731 = 2998097) B2998097
theorem B1998743 : Blo 1330984 1998743 := bstep (se 1 (by rfl) ⟨1499057, by rfl⟩ : syracuseStep 1998743 = 2998115) B2998115
theorem B2998169 : Blo 1330984 2998169 := bstep (se 2 (by rfl) ⟨1124313, by rfl⟩ : syracuseStep 2998169 = 2248627) B2248627
theorem B2277323 : Blo 1330984 2277323 := bstep (se 1 (by rfl) ⟨1707992, by rfl⟩ : syracuseStep 2277323 = 3415985) B3415985
theorem B1998809 : Blo 1330984 1998809 := bstep (se 2 (by rfl) ⟨749553, by rfl⟩ : syracuseStep 1998809 = 1499107) B1499107
theorem B2998259 : Blo 1330984 2998259 := bstep (se 1 (by rfl) ⟨2248694, by rfl⟩ : syracuseStep 2998259 = 4497389) B4497389
theorem B12804101 : Blo 1330984 12804101 := bstep (se 4 (by rfl) ⟨1200384, by rfl⟩ : syracuseStep 12804101 = 2400769) B2400769
theorem B1499143 : Blo 1330984 1499143 := bstep (se 1 (by rfl) ⟨1124357, by rfl⟩ : syracuseStep 1499143 = 2248715) B2248715
theorem B1998863 : Blo 1330984 1998863 := bstep (se 1 (by rfl) ⟨1499147, by rfl⟩ : syracuseStep 1998863 = 2998295) B2998295
theorem B5054507 : Blo 1330984 5054507 := bstep (se 1 (by rfl) ⟨3790880, by rfl⟩ : syracuseStep 5054507 = 7581761) B7581761
theorem B1998905 : Blo 1330984 1998905 := bstep (se 2 (by rfl) ⟨749589, by rfl⟩ : syracuseStep 1998905 = 1499179) B1499179
theorem B2998331 : Blo 1330984 2998331 := bstep (se 1 (by rfl) ⟨2248748, by rfl⟩ : syracuseStep 2998331 = 4497497) B4497497
theorem B1998983 : Blo 1330984 1998983 := bstep (se 1 (by rfl) ⟨1499237, by rfl⟩ : syracuseStep 1998983 = 2998475) B2998475
theorem B1999019 : Blo 1330984 1999019 := bstep (se 1 (by rfl) ⟨1499264, by rfl⟩ : syracuseStep 1999019 = 2998529) B2998529
theorem B2998457 : Blo 1330984 2998457 := bstep (se 2 (by rfl) ⟨1124421, by rfl⟩ : syracuseStep 2998457 = 2248843) B2248843
theorem B1499323 : Blo 1330984 1499323 := bstep (se 1 (by rfl) ⟨1124492, by rfl⟩ : syracuseStep 1499323 = 2248985) B2248985
theorem B1999049 : Blo 1330984 1999049 := bstep (se 2 (by rfl) ⟨749643, by rfl⟩ : syracuseStep 1999049 = 1499287) B1499287
theorem B2842895 : Blo 1330984 2842895 := bstep (se 1 (by rfl) ⟨2132171, by rfl⟩ : syracuseStep 2842895 = 4264343) B4264343
theorem B2842913 : Blo 1330984 2842913 := bstep (se 2 (by rfl) ⟨1066092, by rfl⟩ : syracuseStep 2842913 = 2132185) B2132185
theorem B1442107 : Blo 1330984 1442107 := bstep (se 1 (by rfl) ⟨1081580, by rfl⟩ : syracuseStep 1442107 = 2163161) B2163161
theorem B1999163 : Blo 1330984 1999163 := bstep (se 1 (by rfl) ⟨1499372, by rfl⟩ : syracuseStep 1999163 = 2998745) B2998745
theorem B1999223 : Blo 1330984 1999223 := bstep (se 1 (by rfl) ⟨1499417, by rfl⟩ : syracuseStep 1999223 = 2998835) B2998835
theorem B1999247 : Blo 1330984 1999247 := bstep (se 1 (by rfl) ⟨1499435, by rfl⟩ : syracuseStep 1999247 = 2998871) B2998871
theorem B1999289 : Blo 1330984 1999289 := bstep (se 2 (by rfl) ⟨749733, by rfl⟩ : syracuseStep 1999289 = 1499467) B1499467
theorem B8536529 : Blo 1330984 8536529 := bstep (se 2 (by rfl) ⟨3201198, by rfl⟩ : syracuseStep 8536529 = 6402397) B6402397
theorem B11379203 : Blo 1330984 11379203 := bstep (se 1 (by rfl) ⟨8534402, by rfl⟩ : syracuseStep 11379203 = 17068805) B17068805
theorem B1999367 : Blo 1330984 1999367 := bstep (se 1 (by rfl) ⟨1499525, by rfl⟩ : syracuseStep 1999367 = 2999051) B2999051
theorem B2998799 : Blo 1330984 2998799 := bstep (se 1 (by rfl) ⟨2249099, by rfl⟩ : syracuseStep 2998799 = 4498199) B4498199
theorem B2998817 : Blo 1330984 2998817 := bstep (se 2 (by rfl) ⟨1124556, by rfl⟩ : syracuseStep 2998817 = 2249113) B2249113
theorem B1999403 : Blo 1330984 1999403 := bstep (se 1 (by rfl) ⟨1499552, by rfl⟩ : syracuseStep 1999403 = 2999105) B2999105
theorem B1999433 : Blo 1330984 1999433 := bstep (se 2 (by rfl) ⟨749787, by rfl⟩ : syracuseStep 1999433 = 1499575) B1499575
theorem B2843255 : Blo 1330984 2843255 := bstep (se 1 (by rfl) ⟨2132441, by rfl⟩ : syracuseStep 2843255 = 4264883) B4264883
theorem B5767937 : Blo 1330984 5767937 := bstep (se 2 (by rfl) ⟨2162976, by rfl⟩ : syracuseStep 5767937 = 4325953) B4325953
theorem B2884385 : Blo 1330984 2884385 := bstep (se 2 (by rfl) ⟨1081644, by rfl⟩ : syracuseStep 2884385 = 2163289) B2163289
theorem B2999159 : Blo 1330984 2999159 := bstep (se 1 (by rfl) ⟨2249369, by rfl⟩ : syracuseStep 2999159 = 4498739) B4498739
theorem B15180695 : Blo 1330984 15180695 := bstep (se 1 (by rfl) ⟨11385521, by rfl⟩ : syracuseStep 15180695 = 22771043) B22771043
theorem B4498361 : Blo 1330984 4498361 := bstep (se 2 (by rfl) ⟨1686885, by rfl⟩ : syracuseStep 4498361 = 3373771) B3373771
theorem B3793979 : Blo 1330984 3793979 := bstep (se 1 (by rfl) ⟨2845484, by rfl⟩ : syracuseStep 3793979 = 5690969) B5690969
theorem B3794035 : Blo 1330984 3794035 := bstep (se 1 (by rfl) ⟨2845526, by rfl⟩ : syracuseStep 3794035 = 5691053) B5691053
theorem B7693541 : Blo 1330984 7693541 := bstep (se 4 (by rfl) ⟨721269, by rfl⟩ : syracuseStep 7693541 = 1442539) B1442539
theorem B6399283 : Blo 1330984 6399283 := bstep (se 1 (by rfl) ⟨4799462, by rfl⟩ : syracuseStep 6399283 = 9598925) B9598925
theorem B6743411 : Blo 1330984 6743411 := bstep (se 1 (by rfl) ⟨5057558, by rfl⟩ : syracuseStep 6743411 = 10115117) B10115117
theorem B11527559 : Blo 1330984 11527559 := bstep (se 1 (by rfl) ⟨8645669, by rfl⟩ : syracuseStep 11527559 = 17291339) B17291339
theorem B2246089 : Blo 1330984 2246089 := bstep (se 2 (by rfl) ⟨842283, by rfl⟩ : syracuseStep 2246089 = 1684567) B1684567
theorem B3417545 : Blo 1330984 3417545 := bstep (se 2 (by rfl) ⟨1281579, by rfl⟩ : syracuseStep 3417545 = 2563159) B2563159
theorem B3794377 : Blo 1330984 3794377 := bstep (se 2 (by rfl) ⟨1422891, by rfl⟩ : syracuseStep 3794377 = 2845783) B2845783
theorem B2025017 : Blo 1330984 2025017 := bstep (se 2 (by rfl) ⟨759381, by rfl⟩ : syracuseStep 2025017 = 1518763) B1518763
theorem B6743897 : Blo 1330984 6743897 := bstep (se 2 (by rfl) ⟨2528961, by rfl⟩ : syracuseStep 6743897 = 5057923) B5057923
theorem B2279287 : Blo 1330984 2279287 := bstep (se 1 (by rfl) ⟨1709465, by rfl⟩ : syracuseStep 2279287 = 3418931) B3418931
theorem B5056465 : Blo 1330984 5056465 := bstep (se 2 (by rfl) ⟨1896174, by rfl⟩ : syracuseStep 5056465 = 3792349) B3792349
theorem B8103959 : Blo 1330984 8103959 := bstep (se 1 (by rfl) ⟨6077969, by rfl⟩ : syracuseStep 8103959 = 12155939) B12155939
theorem B8095787 : Blo 1330984 8095787 := bstep (se 1 (by rfl) ⟨6071840, by rfl⟩ : syracuseStep 8095787 = 12143681) B12143681
theorem B4327511 : Blo 1330984 4327511 := bstep (se 1 (by rfl) ⟨3245633, by rfl⟩ : syracuseStep 4327511 = 6491267) B6491267
theorem B5400695 : Blo 1330984 5400695 := bstep (se 1 (by rfl) ⟨4050521, by rfl⟩ : syracuseStep 5400695 = 8101043) B8101043
theorem B2246791 : Blo 1330984 2246791 := bstep (se 1 (by rfl) ⟨1685093, by rfl⟩ : syracuseStep 2246791 = 3370187) B3370187
theorem B5056769 : Blo 1330984 5056769 := bstep (se 2 (by rfl) ⟨1896288, by rfl⟩ : syracuseStep 5056769 = 3792577) B3792577
theorem B5687567 : Blo 1330984 5687567 := bstep (se 1 (by rfl) ⟨4265675, by rfl⟩ : syracuseStep 5687567 = 8531351) B8531351
theorem B11536673 : Blo 1330984 11536673 := bstep (se 2 (by rfl) ⟨4326252, by rfl⟩ : syracuseStep 11536673 = 8652505) B8652505
theorem B6834577 : Blo 1330984 6834577 := bstep (se 2 (by rfl) ⟨2562966, by rfl⟩ : syracuseStep 6834577 = 5125933) B5125933
theorem B5400985 : Blo 1330984 5400985 := bstep (se 2 (by rfl) ⟨2025369, by rfl⟩ : syracuseStep 5400985 = 4050739) B4050739
theorem B1518139 : Blo 1330984 1518139 := bstep (se 1 (by rfl) ⟨1138604, by rfl⟩ : syracuseStep 1518139 = 2277209) B2277209
theorem B3369559 : Blo 1330984 3369559 := bstep (se 1 (by rfl) ⟨2527169, by rfl⟩ : syracuseStep 3369559 = 5054339) B5054339
theorem B1518215 : Blo 1330984 1518215 := bstep (se 1 (by rfl) ⟨1138661, by rfl⟩ : syracuseStep 1518215 = 2277323) B2277323
theorem B7588525 : Blo 1330984 7588525 := bstep (se 3 (by rfl) ⟨1422848, by rfl⟩ : syracuseStep 7588525 = 2845697) B2845697
theorem B5057225 : Blo 1330984 5057225 := bstep (se 2 (by rfl) ⟨1896459, by rfl⟩ : syracuseStep 5057225 = 3792919) B3792919
theorem B2247439 : Blo 1330984 2247439 := bstep (se 1 (by rfl) ⟨1685579, by rfl⟩ : syracuseStep 2247439 = 3371159) B3371159
theorem B3369863 : Blo 1330984 3369863 := bstep (se 1 (by rfl) ⟨2527397, by rfl⟩ : syracuseStep 3369863 = 5054795) B5054795
theorem B3369995 : Blo 1330984 3369995 := bstep (se 1 (by rfl) ⟨2527496, by rfl⟩ : syracuseStep 3369995 = 5054993) B5054993
theorem B163998755 : Blo 1330984 163998755 := bstep (se 1 (by rfl) ⟨122999066, by rfl⟩ : syracuseStep 163998755 = 245998133) B245998133
theorem B10112201 : Blo 1330984 10112201 := bstep (se 2 (by rfl) ⟨3792075, by rfl⟩ : syracuseStep 10112201 = 7584151) B7584151
theorem B6401281 : Blo 1330984 6401281 := bstep (se 2 (by rfl) ⟨2400480, by rfl⟩ : syracuseStep 6401281 = 4800961) B4800961
theorem B2247979 : Blo 1330984 2247979 := bstep (se 1 (by rfl) ⟨1685984, by rfl⟩ : syracuseStep 2247979 = 3371969) B3371969
theorem B3419435 : Blo 1330984 3419435 := bstep (se 1 (by rfl) ⟨2564576, by rfl⟩ : syracuseStep 3419435 = 5129153) B5129153
theorem B8539451 : Blo 1330984 8539451 := bstep (se 1 (by rfl) ⟨6404588, by rfl⟩ : syracuseStep 8539451 = 12809177) B12809177
theorem B7204211 : Blo 1330984 7204211 := bstep (se 1 (by rfl) ⟨5403158, by rfl⟩ : syracuseStep 7204211 = 10806317) B10806317
theorem B4492691 : Blo 1330984 4492691 := bstep (se 1 (by rfl) ⟨3369518, by rfl⟩ : syracuseStep 4492691 = 6739037) B6739037
theorem B2248121 : Blo 1330984 2248121 := bstep (se 2 (by rfl) ⟨843045, by rfl⟩ : syracuseStep 2248121 = 1686091) B1686091
theorem B3370511 : Blo 1330984 3370511 := bstep (se 1 (by rfl) ⟨2527883, by rfl⟩ : syracuseStep 3370511 = 5055767) B5055767
theorem B18214429 : Blo 1330984 18214429 := bstep (se 3 (by rfl) ⟨3415205, by rfl⟩ : syracuseStep 18214429 = 6830411) B6830411
theorem B3370643 : Blo 1330984 3370643 := bstep (se 1 (by rfl) ⟨2527982, by rfl⟩ : syracuseStep 3370643 = 5055965) B5055965
theorem B3600139 : Blo 1330984 3600139 := bstep (se 1 (by rfl) ⟨2700104, by rfl⟩ : syracuseStep 3600139 = 5400209) B5400209
theorem B16428851 : Blo 1330984 16428851 := bstep (se 1 (by rfl) ⟨12321638, by rfl⟩ : syracuseStep 16428851 = 24643277) B24643277
theorem B1331003 : Blo 1330984 1331003 := bstep (se 1 (by rfl) ⟨998252, by rfl⟩ : syracuseStep 1331003 = 1996505) B1996505
theorem B24293195 : Blo 1330984 24293195 := bstep (se 1 (by rfl) ⟨18219896, by rfl⟩ : syracuseStep 24293195 = 36439793) B36439793
theorem B11374451 : Blo 1330984 11374451 := bstep (se 1 (by rfl) ⟨8530838, by rfl⟩ : syracuseStep 11374451 = 17061677) B17061677
theorem B3600247 : Blo 1330984 3600247 := bstep (se 1 (by rfl) ⟨2700185, by rfl⟩ : syracuseStep 3600247 = 5400371) B5400371
theorem B1331079 : Blo 1330984 1331079 := bstep (se 1 (by rfl) ⟨998309, by rfl⟩ : syracuseStep 1331079 = 1996619) B1996619
theorem B1331087 : Blo 1330984 1331087 := bstep (se 1 (by rfl) ⟨998315, by rfl⟩ : syracuseStep 1331087 = 1996631) B1996631
theorem B6746003 : Blo 1330984 6746003 := bstep (se 1 (by rfl) ⟨5059502, by rfl⟩ : syracuseStep 6746003 = 10119005) B10119005
theorem B1331131 : Blo 1330984 1331131 := bstep (se 1 (by rfl) ⟨998348, by rfl⟩ : syracuseStep 1331131 = 1996697) B1996697
theorem B1331207 : Blo 1330984 1331207 := bstep (se 1 (by rfl) ⟨998405, by rfl⟩ : syracuseStep 1331207 = 1996811) B1996811
theorem B1331215 : Blo 1330984 1331215 := bstep (se 1 (by rfl) ⟨998411, by rfl⟩ : syracuseStep 1331215 = 1996823) B1996823
theorem B2527291 : Blo 1330984 2527291 := bstep (se 1 (by rfl) ⟨1895468, by rfl⟩ : syracuseStep 2527291 = 3790937) B3790937
theorem B1331259 : Blo 1330984 1331259 := bstep (se 1 (by rfl) ⟨998444, by rfl⟩ : syracuseStep 1331259 = 1996889) B1996889
theorem B2248823 : Blo 1330984 2248823 := bstep (se 1 (by rfl) ⟨1686617, by rfl⟩ : syracuseStep 2248823 = 3373235) B3373235
theorem B1331335 : Blo 1330984 1331335 := bstep (se 1 (by rfl) ⟨998501, by rfl⟩ : syracuseStep 1331335 = 1997003) B1997003
theorem B1331343 : Blo 1330984 1331343 := bstep (se 1 (by rfl) ⟨998507, by rfl⟩ : syracuseStep 1331343 = 1997015) B1997015
theorem B1331387 : Blo 1330984 1331387 := bstep (se 1 (by rfl) ⟨998540, by rfl⟩ : syracuseStep 1331387 = 1997081) B1997081
theorem B7205057 : Blo 1330984 7205057 := bstep (se 2 (by rfl) ⟨2701896, by rfl⟩ : syracuseStep 7205057 = 5403793) B5403793
theorem B11374829 : Blo 1330984 11374829 := bstep (se 3 (by rfl) ⟨2132780, by rfl⟩ : syracuseStep 11374829 = 4265561) B4265561
theorem B1331463 : Blo 1330984 1331463 := bstep (se 1 (by rfl) ⟨998597, by rfl⟩ : syracuseStep 1331463 = 1997195) B1997195
theorem B1331471 : Blo 1330984 1331471 := bstep (se 1 (by rfl) ⟨998603, by rfl⟩ : syracuseStep 1331471 = 1997207) B1997207
theorem B6738227 : Blo 1330984 6738227 := bstep (se 1 (by rfl) ⟨5053670, by rfl⟩ : syracuseStep 6738227 = 10107341) B10107341
theorem B1331515 : Blo 1330984 1331515 := bstep (se 1 (by rfl) ⟨998636, by rfl⟩ : syracuseStep 1331515 = 1997273) B1997273
theorem B1331591 : Blo 1330984 1331591 := bstep (se 1 (by rfl) ⟨998693, by rfl⟩ : syracuseStep 1331591 = 1997387) B1997387
theorem B1331599 : Blo 1330984 1331599 := bstep (se 1 (by rfl) ⟨998699, by rfl⟩ : syracuseStep 1331599 = 1997399) B1997399
theorem B1421755 : Blo 1330984 1421755 := bstep (se 1 (by rfl) ⟨1066316, by rfl⟩ : syracuseStep 1421755 = 2132633) B2132633
theorem B1331643 : Blo 1330984 1331643 := bstep (se 1 (by rfl) ⟨998732, by rfl⟩ : syracuseStep 1331643 = 1997465) B1997465
theorem B1331719 : Blo 1330984 1331719 := bstep (se 1 (by rfl) ⟨998789, by rfl⟩ : syracuseStep 1331719 = 1997579) B1997579
theorem B1331727 : Blo 1330984 1331727 := bstep (se 1 (by rfl) ⟨998795, by rfl⟩ : syracuseStep 1331727 = 1997591) B1997591
theorem B2527777 : Blo 1330984 2527777 := bstep (se 2 (by rfl) ⟨947916, by rfl⟩ : syracuseStep 2527777 = 1895833) B1895833
theorem B2994731 : Blo 1330984 2994731 := bstep (se 1 (by rfl) ⟨2246048, by rfl⟩ : syracuseStep 2994731 = 4492097) B4492097
theorem B1331771 : Blo 1330984 1331771 := bstep (se 1 (by rfl) ⟨998828, by rfl⟩ : syracuseStep 1331771 = 1997657) B1997657
theorem B2249275 : Blo 1330984 2249275 := bstep (se 1 (by rfl) ⟨1686956, by rfl⟩ : syracuseStep 2249275 = 3373913) B3373913
theorem B6738551 : Blo 1330984 6738551 := bstep (se 1 (by rfl) ⟨5053913, by rfl⟩ : syracuseStep 6738551 = 10107827) B10107827
theorem B1331847 : Blo 1330984 1331847 := bstep (se 1 (by rfl) ⟨998885, by rfl⟩ : syracuseStep 1331847 = 1997771) B1997771
theorem B1331855 : Blo 1330984 1331855 := bstep (se 1 (by rfl) ⟨998891, by rfl⟩ : syracuseStep 1331855 = 1997783) B1997783
theorem B1331899 : Blo 1330984 1331899 := bstep (se 1 (by rfl) ⟨998924, by rfl⟩ : syracuseStep 1331899 = 1997849) B1997849
theorem B10793665 : Blo 1330984 10793665 := bstep (se 2 (by rfl) ⟨4047624, by rfl⟩ : syracuseStep 10793665 = 8095249) B8095249
theorem B10121921 : Blo 1330984 10121921 := bstep (se 2 (by rfl) ⟨3795720, by rfl⟩ : syracuseStep 10121921 = 7591441) B7591441
theorem B3371777 : Blo 1330984 3371777 := bstep (se 2 (by rfl) ⟨1264416, by rfl⟩ : syracuseStep 3371777 = 2528833) B2528833
theorem B1331975 : Blo 1330984 1331975 := bstep (se 1 (by rfl) ⟨998981, by rfl⟩ : syracuseStep 1331975 = 1997963) B1997963
theorem B4494095 : Blo 1330984 4494095 := bstep (se 1 (by rfl) ⟨3370571, by rfl⟩ : syracuseStep 4494095 = 6741143) B6741143
theorem B1331983 : Blo 1330984 1331983 := bstep (se 1 (by rfl) ⟨998987, by rfl⟩ : syracuseStep 1331983 = 1997975) B1997975
theorem B3199787 : Blo 1330984 3199787 := bstep (se 1 (by rfl) ⟨2399840, by rfl⟩ : syracuseStep 3199787 = 4799681) B4799681
theorem B1332027 : Blo 1330984 1332027 := bstep (se 1 (by rfl) ⟨999020, by rfl⟩ : syracuseStep 1332027 = 1998041) B1998041
theorem B1332103 : Blo 1330984 1332103 := bstep (se 1 (by rfl) ⟨999077, by rfl⟩ : syracuseStep 1332103 = 1998155) B1998155
theorem B1332111 : Blo 1330984 1332111 := bstep (se 1 (by rfl) ⟨999083, by rfl⟩ : syracuseStep 1332111 = 1998167) B1998167
theorem B2995091 : Blo 1330984 2995091 := bstep (se 1 (by rfl) ⟨2246318, by rfl⟩ : syracuseStep 2995091 = 4492637) B4492637
theorem B1332155 : Blo 1330984 1332155 := bstep (se 1 (by rfl) ⟨999116, by rfl⟩ : syracuseStep 1332155 = 1998233) B1998233
theorem B2995145 : Blo 1330984 2995145 := bstep (se 2 (by rfl) ⟨1123179, by rfl⟩ : syracuseStep 2995145 = 2246359) B2246359
theorem B1332231 : Blo 1330984 1332231 := bstep (se 1 (by rfl) ⟨999173, by rfl⟩ : syracuseStep 1332231 = 1998347) B1998347
theorem B1332239 : Blo 1330984 1332239 := bstep (se 1 (by rfl) ⟨999179, by rfl⟩ : syracuseStep 1332239 = 1998359) B1998359
theorem B4494365 : Blo 1330984 4494365 := bstep (se 3 (by rfl) ⟨842693, by rfl⟩ : syracuseStep 4494365 = 1685387) B1685387
theorem B7590941 : Blo 1330984 7590941 := bstep (se 3 (by rfl) ⟨1423301, by rfl⟩ : syracuseStep 7590941 = 2846603) B2846603
theorem B1332283 : Blo 1330984 1332283 := bstep (se 1 (by rfl) ⟨999212, by rfl⟩ : syracuseStep 1332283 = 1998425) B1998425
theorem B3601523 : Blo 1330984 3601523 := bstep (se 1 (by rfl) ⟨2701142, by rfl⟩ : syracuseStep 3601523 = 5402285) B5402285
theorem B3372151 : Blo 1330984 3372151 := bstep (se 1 (by rfl) ⟨2529113, by rfl⟩ : syracuseStep 3372151 = 5058227) B5058227
theorem B1332359 : Blo 1330984 1332359 := bstep (se 1 (by rfl) ⟨999269, by rfl⟩ : syracuseStep 1332359 = 1998539) B1998539
theorem B1332367 : Blo 1330984 1332367 := bstep (se 1 (by rfl) ⟨999275, by rfl⟩ : syracuseStep 1332367 = 1998551) B1998551
theorem B1332411 : Blo 1330984 1332411 := bstep (se 1 (by rfl) ⟨999308, by rfl⟩ : syracuseStep 1332411 = 1998617) B1998617
theorem B1332487 : Blo 1330984 1332487 := bstep (se 1 (by rfl) ⟨999365, by rfl⟩ : syracuseStep 1332487 = 1998731) B1998731
theorem B1332495 : Blo 1330984 1332495 := bstep (se 1 (by rfl) ⟨999371, by rfl⟩ : syracuseStep 1332495 = 1998743) B1998743
theorem B1684795 : Blo 1330984 1684795 := bstep (se 1 (by rfl) ⟨1263596, by rfl⟩ : syracuseStep 1684795 = 2527193) B2527193
theorem B1332539 : Blo 1330984 1332539 := bstep (se 1 (by rfl) ⟨999404, by rfl⟩ : syracuseStep 1332539 = 1998809) B1998809
theorem B1332615 : Blo 1330984 1332615 := bstep (se 1 (by rfl) ⟨999461, by rfl⟩ : syracuseStep 1332615 = 1998923) B1998923
theorem B1332623 : Blo 1330984 1332623 := bstep (se 1 (by rfl) ⟨999467, by rfl⟩ : syracuseStep 1332623 = 1998935) B1998935
theorem B6403475 : Blo 1330984 6403475 := bstep (se 1 (by rfl) ⟨4802606, by rfl⟩ : syracuseStep 6403475 = 9605213) B9605213
theorem B4265369 : Blo 1330984 4265369 := bstep (se 2 (by rfl) ⟨1599513, by rfl⟩ : syracuseStep 4265369 = 3199027) B3199027
theorem B1332667 : Blo 1330984 1332667 := bstep (se 1 (by rfl) ⟨999500, by rfl⟩ : syracuseStep 1332667 = 1999001) B1999001
theorem B1332743 : Blo 1330984 1332743 := bstep (se 1 (by rfl) ⟨999557, by rfl⟩ : syracuseStep 1332743 = 1999115) B1999115
theorem B1332751 : Blo 1330984 1332751 := bstep (se 1 (by rfl) ⟨999563, by rfl⟩ : syracuseStep 1332751 = 1999127) B1999127
theorem B3372587 : Blo 1330984 3372587 := bstep (se 1 (by rfl) ⟨2529440, by rfl⟩ : syracuseStep 3372587 = 5058881) B5058881
theorem B6403627 : Blo 1330984 6403627 := bstep (se 1 (by rfl) ⟨4802720, by rfl⟩ : syracuseStep 6403627 = 9605441) B9605441
theorem B1332795 : Blo 1330984 1332795 := bstep (se 1 (by rfl) ⟨999596, by rfl⟩ : syracuseStep 1332795 = 1999193) B1999193
theorem B6075965 : Blo 1330984 6075965 := bstep (se 3 (by rfl) ⟨1139243, by rfl⟩ : syracuseStep 6075965 = 2278487) B2278487
theorem B6739523 : Blo 1330984 6739523 := bstep (se 1 (by rfl) ⟨5054642, by rfl⟩ : syracuseStep 6739523 = 10109285) B10109285
theorem B2995847 : Blo 1330984 2995847 := bstep (se 1 (by rfl) ⟨2246885, by rfl⟩ : syracuseStep 2995847 = 4493771) B4493771
theorem B1332871 : Blo 1330984 1332871 := bstep (se 1 (by rfl) ⟨999653, by rfl⟩ : syracuseStep 1332871 = 1999307) B1999307
theorem B1332879 : Blo 1330984 1332879 := bstep (se 1 (by rfl) ⟨999659, by rfl⟩ : syracuseStep 1332879 = 1999319) B1999319
theorem B1332923 : Blo 1330984 1332923 := bstep (se 1 (by rfl) ⟨999692, by rfl⟩ : syracuseStep 1332923 = 1999385) B1999385
theorem B1996535 : Blo 1330984 1996535 := bstep (se 1 (by rfl) ⟨1497401, by rfl⟩ : syracuseStep 1996535 = 2994803) B2994803
theorem B5060353 : Blo 1330984 5060353 := bstep (se 2 (by rfl) ⟨1897632, by rfl⟩ : syracuseStep 5060353 = 3795265) B3795265
theorem B1996559 : Blo 1330984 1996559 := bstep (se 1 (by rfl) ⟨1497419, by rfl⟩ : syracuseStep 1996559 = 2994839) B2994839
theorem B25597741 : Blo 1330984 25597741 := bstep (se 3 (by rfl) ⟨4799576, by rfl⟩ : syracuseStep 25597741 = 9599153) B9599153
theorem B32380721 : Blo 1330984 32380721 := bstep (se 2 (by rfl) ⟨12142770, by rfl⟩ : syracuseStep 32380721 = 24285541) B24285541
theorem B8533811 : Blo 1330984 8533811 := bstep (se 1 (by rfl) ⟨6400358, by rfl⟩ : syracuseStep 8533811 = 12800717) B12800717
theorem B1996601 : Blo 1330984 1996601 := bstep (se 2 (by rfl) ⟨748725, by rfl⟩ : syracuseStep 1996601 = 1497451) B1497451
theorem B2996027 : Blo 1330984 2996027 := bstep (se 1 (by rfl) ⟨2247020, by rfl⟩ : syracuseStep 2996027 = 4494041) B4494041
theorem B2529083 : Blo 1330984 2529083 := bstep (se 1 (by rfl) ⟨1896812, by rfl⟩ : syracuseStep 2529083 = 3793625) B3793625
theorem B1996679 : Blo 1330984 1996679 := bstep (se 1 (by rfl) ⟨1497509, by rfl⟩ : syracuseStep 1996679 = 2995019) B2995019
theorem B6739847 : Blo 1330984 6739847 := bstep (se 1 (by rfl) ⟨5054885, by rfl⟩ : syracuseStep 6739847 = 10109771) B10109771
theorem B3602323 : Blo 1330984 3602323 := bstep (se 1 (by rfl) ⟨2701742, by rfl⟩ : syracuseStep 3602323 = 5403485) B5403485
theorem B1996715 : Blo 1330984 1996715 := bstep (se 1 (by rfl) ⟨1497536, by rfl⟩ : syracuseStep 1996715 = 2995073) B2995073
theorem B2996153 : Blo 1330984 2996153 := bstep (se 2 (by rfl) ⟨1123557, by rfl⟩ : syracuseStep 2996153 = 2247115) B2247115
theorem B1996745 : Blo 1330984 1996745 := bstep (se 2 (by rfl) ⟨748779, by rfl⟩ : syracuseStep 1996745 = 1497559) B1497559
theorem B8099851 : Blo 1330984 8099851 := bstep (se 1 (by rfl) ⟨6074888, by rfl⟩ : syracuseStep 8099851 = 12149777) B12149777
theorem B12810251 : Blo 1330984 12810251 := bstep (se 1 (by rfl) ⟨9607688, by rfl⟩ : syracuseStep 12810251 = 19215377) B19215377
theorem B3790891 : Blo 1330984 3790891 := bstep (se 1 (by rfl) ⟨2843168, by rfl⟩ : syracuseStep 3790891 = 5686337) B5686337
theorem B1996859 : Blo 1330984 1996859 := bstep (se 1 (by rfl) ⟨1497644, by rfl⟩ : syracuseStep 1996859 = 2995289) B2995289
theorem B1996919 : Blo 1330984 1996919 := bstep (se 1 (by rfl) ⟨1497689, by rfl⟩ : syracuseStep 1996919 = 2995379) B2995379
theorem B2562167 : Blo 1330984 2562167 := bstep (se 1 (by rfl) ⟨1921625, by rfl⟩ : syracuseStep 2562167 = 3843251) B3843251
theorem B1996943 : Blo 1330984 1996943 := bstep (se 1 (by rfl) ⟨1497707, by rfl⟩ : syracuseStep 1996943 = 2995415) B2995415
theorem B1996985 : Blo 1330984 1996985 := bstep (se 2 (by rfl) ⟨748869, by rfl⟩ : syracuseStep 1996985 = 1497739) B1497739
theorem B1997063 : Blo 1330984 1997063 := bstep (se 1 (by rfl) ⟨1497797, by rfl⟩ : syracuseStep 1997063 = 2995595) B2995595
theorem B1685767 : Blo 1330984 1685767 := bstep (se 1 (by rfl) ⟨1264325, by rfl⟩ : syracuseStep 1685767 = 2528651) B2528651
theorem B3791119 : Blo 1330984 3791119 := bstep (se 1 (by rfl) ⟨2843339, by rfl⟩ : syracuseStep 3791119 = 5686679) B5686679
theorem B2996495 : Blo 1330984 2996495 := bstep (se 1 (by rfl) ⟨2247371, by rfl⟩ : syracuseStep 2996495 = 4494743) B4494743
theorem B2996513 : Blo 1330984 2996513 := bstep (se 2 (by rfl) ⟨1123692, by rfl⟩ : syracuseStep 2996513 = 2247385) B2247385
theorem B2529569 : Blo 1330984 2529569 := bstep (se 2 (by rfl) ⟨948588, by rfl⟩ : syracuseStep 2529569 = 1897177) B1897177
theorem B9607457 : Blo 1330984 9607457 := bstep (se 2 (by rfl) ⟨3602796, by rfl⟩ : syracuseStep 9607457 = 7205593) B7205593
theorem B1997099 : Blo 1330984 1997099 := bstep (se 1 (by rfl) ⟨1497824, by rfl⟩ : syracuseStep 1997099 = 2995649) B2995649
theorem B1997129 : Blo 1330984 1997129 := bstep (se 2 (by rfl) ⟨748923, by rfl⟩ : syracuseStep 1997129 = 1497847) B1497847
theorem B3373427 : Blo 1330984 3373427 := bstep (se 1 (by rfl) ⟨2530070, by rfl⟩ : syracuseStep 3373427 = 5060141) B5060141
theorem B3373447 : Blo 1330984 3373447 := bstep (se 1 (by rfl) ⟨2530085, by rfl⟩ : syracuseStep 3373447 = 5060171) B5060171
theorem B1497487 : Blo 1330984 1497487 := bstep (se 1 (by rfl) ⟨1123115, by rfl⟩ : syracuseStep 1497487 = 2246231) B2246231
theorem B4495769 : Blo 1330984 4495769 := bstep (se 2 (by rfl) ⟨1685913, by rfl⟩ : syracuseStep 4495769 = 3371827) B3371827
theorem B7297465 : Blo 1330984 7297465 := bstep (se 2 (by rfl) ⟨2736549, by rfl⟩ : syracuseStep 7297465 = 5473099) B5473099
theorem B2529721 : Blo 1330984 2529721 := bstep (se 2 (by rfl) ⟨948645, by rfl⟩ : syracuseStep 2529721 = 1897291) B1897291
theorem B1997243 : Blo 1330984 1997243 := bstep (se 1 (by rfl) ⟨1497932, by rfl⟩ : syracuseStep 1997243 = 2995865) B2995865
theorem B1997303 : Blo 1330984 1997303 := bstep (se 1 (by rfl) ⟨1497977, by rfl⟩ : syracuseStep 1997303 = 2995955) B2995955
theorem B1997327 : Blo 1330984 1997327 := bstep (se 1 (by rfl) ⟨1497995, by rfl⟩ : syracuseStep 1997327 = 2995991) B2995991
theorem B3791393 : Blo 1330984 3791393 := bstep (se 2 (by rfl) ⟨1421772, by rfl⟩ : syracuseStep 3791393 = 2843545) B2843545
theorem B1997369 : Blo 1330984 1997369 := bstep (se 2 (by rfl) ⟨749013, by rfl⟩ : syracuseStep 1997369 = 1498027) B1498027
theorem B5700215 : Blo 1330984 5700215 := bstep (se 1 (by rfl) ⟨4275161, by rfl⟩ : syracuseStep 5700215 = 8550323) B8550323
theorem B2996855 : Blo 1330984 2996855 := bstep (se 1 (by rfl) ⟨2247641, by rfl⟩ : syracuseStep 2996855 = 4495283) B4495283
theorem B1997447 : Blo 1330984 1997447 := bstep (se 1 (by rfl) ⟨1498085, by rfl⟩ : syracuseStep 1997447 = 2996171) B2996171
theorem B3603079 : Blo 1330984 3603079 := bstep (se 1 (by rfl) ⟨2702309, by rfl⟩ : syracuseStep 3603079 = 5404619) B5404619
theorem B3373721 : Blo 1330984 3373721 := bstep (se 2 (by rfl) ⟨1265145, by rfl⟩ : syracuseStep 3373721 = 2530291) B2530291
theorem B1997483 : Blo 1330984 1997483 := bstep (se 1 (by rfl) ⟨1498112, by rfl⟩ : syracuseStep 1997483 = 2996225) B2996225
theorem B1686187 : Blo 1330984 1686187 := bstep (se 1 (by rfl) ⟨1264640, by rfl⟩ : syracuseStep 1686187 = 2529281) B2529281
theorem B1997513 : Blo 1330984 1997513 := bstep (se 2 (by rfl) ⟨749067, by rfl⟩ : syracuseStep 1997513 = 1498135) B1498135
theorem B2997035 : Blo 1330984 2997035 := bstep (se 1 (by rfl) ⟨2247776, by rfl⟩ : syracuseStep 2997035 = 4495553) B4495553
theorem B1997627 : Blo 1330984 1997627 := bstep (se 1 (by rfl) ⟨1498220, by rfl⟩ : syracuseStep 1997627 = 2996441) B2996441
theorem B3373883 : Blo 1330984 3373883 := bstep (se 1 (by rfl) ⟨2530412, by rfl⟩ : syracuseStep 3373883 = 5060825) B5060825
theorem B3791735 : Blo 1330984 3791735 := bstep (se 1 (by rfl) ⟨2843801, by rfl⟩ : syracuseStep 3791735 = 5687603) B5687603
theorem B1997687 : Blo 1330984 1997687 := bstep (se 1 (by rfl) ⟨1498265, by rfl⟩ : syracuseStep 1997687 = 2996531) B2996531
theorem B1497991 : Blo 1330984 1497991 := bstep (se 1 (by rfl) ⟨1123493, by rfl⟩ : syracuseStep 1497991 = 2246987) B2246987
theorem B1997711 : Blo 1330984 1997711 := bstep (se 1 (by rfl) ⟨1498283, by rfl⟩ : syracuseStep 1997711 = 2996567) B2996567
theorem B1686415 : Blo 1330984 1686415 := bstep (se 1 (by rfl) ⟨1264811, by rfl⟩ : syracuseStep 1686415 = 2529623) B2529623
theorem B1997753 : Blo 1330984 1997753 := bstep (se 2 (by rfl) ⟨749157, by rfl⟩ : syracuseStep 1997753 = 1498315) B1498315
theorem B1997831 : Blo 1330984 1997831 := bstep (se 1 (by rfl) ⟨1498373, by rfl⟩ : syracuseStep 1997831 = 2996747) B2996747
theorem B3374095 : Blo 1330984 3374095 := bstep (se 1 (by rfl) ⟨2530571, by rfl⟩ : syracuseStep 3374095 = 5061143) B5061143
theorem B1997867 : Blo 1330984 1997867 := bstep (se 1 (by rfl) ⟨1498400, by rfl⟩ : syracuseStep 1997867 = 2996801) B2996801
theorem B1498171 : Blo 1330984 1498171 := bstep (se 1 (by rfl) ⟨1123628, by rfl⟩ : syracuseStep 1498171 = 2247257) B2247257
theorem B1997897 : Blo 1330984 1997897 := bstep (se 2 (by rfl) ⟨749211, by rfl⟩ : syracuseStep 1997897 = 1498423) B1498423
theorem B4496471 : Blo 1330984 4496471 := bstep (se 1 (by rfl) ⟨3372353, by rfl⟩ : syracuseStep 4496471 = 6744707) B6744707
theorem B2997395 : Blo 1330984 2997395 := bstep (se 1 (by rfl) ⟨2248046, by rfl⟩ : syracuseStep 2997395 = 4496093) B4496093
theorem B1998011 : Blo 1330984 1998011 := bstep (se 1 (by rfl) ⟨1498508, by rfl⟩ : syracuseStep 1998011 = 2997017) B2997017
theorem B2997449 : Blo 1330984 2997449 := bstep (se 2 (by rfl) ⟨1124043, by rfl⟩ : syracuseStep 2997449 = 2248087) B2248087
theorem B15383753 : Blo 1330984 15383753 := bstep (se 2 (by rfl) ⟨5768907, by rfl⟩ : syracuseStep 15383753 = 11537815) B11537815
theorem B1998071 : Blo 1330984 1998071 := bstep (se 1 (by rfl) ⟨1498553, by rfl⟩ : syracuseStep 1998071 = 2997107) B2997107
theorem B1998095 : Blo 1330984 1998095 := bstep (se 1 (by rfl) ⟨1498571, by rfl⟩ : syracuseStep 1998095 = 2997143) B2997143
theorem B1998137 : Blo 1330984 1998137 := bstep (se 2 (by rfl) ⟨749301, by rfl⟩ : syracuseStep 1998137 = 1498603) B1498603
theorem B1998215 : Blo 1330984 1998215 := bstep (se 1 (by rfl) ⟨1498661, by rfl⟩ : syracuseStep 1998215 = 2997323) B2997323
theorem B1998251 : Blo 1330984 1998251 := bstep (se 1 (by rfl) ⟨1498688, by rfl⟩ : syracuseStep 1998251 = 2997377) B2997377
theorem B1998281 : Blo 1330984 1998281 := bstep (se 2 (by rfl) ⟨749355, by rfl⟩ : syracuseStep 1998281 = 1498711) B1498711
theorem B11378141 : Blo 1330984 11378141 := bstep (se 3 (by rfl) ⟨2133401, by rfl⟩ : syracuseStep 11378141 = 4266803) B4266803
theorem B3792395 : Blo 1330984 3792395 := bstep (se 1 (by rfl) ⟨2844296, by rfl⟩ : syracuseStep 3792395 = 5688593) B5688593
theorem B1498639 : Blo 1330984 1498639 := bstep (se 1 (by rfl) ⟨1123979, by rfl⟩ : syracuseStep 1498639 = 2247959) B2247959
theorem B1998395 : Blo 1330984 1998395 := bstep (se 1 (by rfl) ⟨1498796, by rfl⟩ : syracuseStep 1998395 = 2997593) B2997593
theorem B4496957 : Blo 1330984 4496957 := bstep (se 3 (by rfl) ⟨843179, by rfl⟩ : syracuseStep 4496957 = 1686359) B1686359
theorem B1998455 : Blo 1330984 1998455 := bstep (se 1 (by rfl) ⟨1498841, by rfl⟩ : syracuseStep 1998455 = 2997683) B2997683
theorem B3202679 : Blo 1330984 3202679 := bstep (se 1 (by rfl) ⟨2402009, by rfl⟩ : syracuseStep 3202679 = 4804019) B4804019
theorem B1998479 : Blo 1330984 1998479 := bstep (se 1 (by rfl) ⟨1498859, by rfl⟩ : syracuseStep 1998479 = 2997719) B2997719
theorem B12795569 : Blo 1330984 12795569 := bstep (se 2 (by rfl) ⟨4798338, by rfl⟩ : syracuseStep 12795569 = 9596677) B9596677
theorem B1998521 : Blo 1330984 1998521 := bstep (se 2 (by rfl) ⟨749445, by rfl⟩ : syracuseStep 1998521 = 1498891) B1498891
theorem B1998599 : Blo 1330984 1998599 := bstep (se 1 (by rfl) ⟨1498949, by rfl⟩ : syracuseStep 1998599 = 2997899) B2997899
theorem B1998635 : Blo 1330984 1998635 := bstep (se 1 (by rfl) ⟨1498976, by rfl⟩ : syracuseStep 1998635 = 2997953) B2997953
theorem B1998665 : Blo 1330984 1998665 := bstep (se 2 (by rfl) ⟨749499, by rfl⟩ : syracuseStep 1998665 = 1498999) B1498999
theorem B11099993 : Blo 1330984 11099993 := bstep (se 2 (by rfl) ⟨4162497, by rfl⟩ : syracuseStep 11099993 = 8324995) B8324995
theorem B2998151 : Blo 1330984 2998151 := bstep (se 1 (by rfl) ⟨2248613, by rfl⟩ : syracuseStep 2998151 = 4497227) B4497227
theorem B4865939 : Blo 1330984 4865939 := bstep (se 1 (by rfl) ⟨3649454, by rfl⟩ : syracuseStep 4865939 = 7298909) B7298909
theorem B1998779 : Blo 1330984 1998779 := bstep (se 1 (by rfl) ⟨1499084, by rfl⟩ : syracuseStep 1998779 = 2998169) B2998169
theorem B1998839 : Blo 1330984 1998839 := bstep (se 1 (by rfl) ⟨1499129, by rfl⟩ : syracuseStep 1998839 = 2998259) B2998259
theorem B8536067 : Blo 1330984 8536067 := bstep (se 1 (by rfl) ⟨6402050, by rfl⟩ : syracuseStep 8536067 = 12804101) B12804101
theorem B1998857 : Blo 1330984 1998857 := bstep (se 2 (by rfl) ⟨749571, by rfl⟩ : syracuseStep 1998857 = 1499143) B1499143
theorem B1998887 : Blo 1330984 1998887 := bstep (se 1 (by rfl) ⟨1499165, by rfl⟩ : syracuseStep 1998887 = 2998331) B2998331
theorem B5054521 : Blo 1330984 5054521 := bstep (se 2 (by rfl) ⟨1895445, by rfl⟩ : syracuseStep 5054521 = 3790891) B3790891
theorem B1499215 : Blo 1330984 1499215 := bstep (se 1 (by rfl) ⟨1124411, by rfl⟩ : syracuseStep 1499215 = 2248823) B2248823
theorem B1998971 : Blo 1330984 1998971 := bstep (se 1 (by rfl) ⟨1499228, by rfl⟩ : syracuseStep 1998971 = 2998457) B2998457
theorem B1999097 : Blo 1330984 1999097 := bstep (se 2 (by rfl) ⟨749661, by rfl⟩ : syracuseStep 1999097 = 1499323) B1499323
theorem B7586135 : Blo 1330984 7586135 := bstep (se 1 (by rfl) ⟨5689601, by rfl⟩ : syracuseStep 7586135 = 11379203) B11379203
theorem B1999199 : Blo 1330984 1999199 := bstep (se 1 (by rfl) ⟨1499399, by rfl⟩ : syracuseStep 1999199 = 2998799) B2998799
theorem B5054825 : Blo 1330984 5054825 := bstep (se 2 (by rfl) ⟨1895559, by rfl⟩ : syracuseStep 5054825 = 3791119) B3791119
theorem B1999211 : Blo 1330984 1999211 := bstep (se 1 (by rfl) ⟨1499408, by rfl⟩ : syracuseStep 1999211 = 2998817) B2998817
theorem B4497929 : Blo 1330984 4497929 := bstep (se 2 (by rfl) ⟨1686723, by rfl⟩ : syracuseStep 4497929 = 3373447) B3373447
theorem B7201313 : Blo 1330984 7201313 := bstep (se 2 (by rfl) ⟨2700492, by rfl⟩ : syracuseStep 7201313 = 5400985) B5400985
theorem B1999439 : Blo 1330984 1999439 := bstep (se 1 (by rfl) ⟨1499579, by rfl⟩ : syracuseStep 1999439 = 2999159) B2999159
theorem B2998907 : Blo 1330984 2998907 := bstep (se 1 (by rfl) ⟨2249180, by rfl⟩ : syracuseStep 2998907 = 4498361) B4498361
theorem B2401015 : Blo 1330984 2401015 := bstep (se 1 (by rfl) ⟨1800761, by rfl⟩ : syracuseStep 2401015 = 3601523) B3601523
theorem B2024185 : Blo 1330984 2024185 := bstep (se 2 (by rfl) ⟨759069, by rfl⟩ : syracuseStep 2024185 = 1518139) B1518139
theorem B2999033 : Blo 1330984 2999033 := bstep (se 2 (by rfl) ⟨1124637, by rfl⟩ : syracuseStep 2999033 = 2249275) B2249275
theorem B9118493 : Blo 1330984 9118493 := bstep (se 3 (by rfl) ⟨1709717, by rfl⟩ : syracuseStep 9118493 = 3419435) B3419435
theorem B5129027 : Blo 1330984 5129027 := bstep (se 1 (by rfl) ⟨3846770, by rfl⟩ : syracuseStep 5129027 = 7693541) B7693541
theorem B10118033 : Blo 1330984 10118033 := bstep (se 2 (by rfl) ⟨3794262, by rfl⟩ : syracuseStep 10118033 = 7588525) B7588525
theorem B7685039 : Blo 1330984 7685039 := bstep (se 1 (by rfl) ⟨5763779, by rfl⟩ : syracuseStep 7685039 = 11527559) B11527559
theorem B4268983 : Blo 1330984 4268983 := bstep (se 1 (by rfl) ⟨3201737, by rfl⟩ : syracuseStep 4268983 = 6403475) B6403475
theorem B2843579 : Blo 1330984 2843579 := bstep (se 1 (by rfl) ⟨2132684, by rfl⟩ : syracuseStep 2843579 = 4265369) B4265369
theorem B2278363 : Blo 1330984 2278363 := bstep (se 1 (by rfl) ⟨1708772, by rfl⟩ : syracuseStep 2278363 = 3417545) B3417545
theorem B57566213 : Blo 1330984 57566213 := bstep (se 4 (by rfl) ⟨5396832, by rfl⟩ : syracuseStep 57566213 = 10793665) B10793665
theorem B21587147 : Blo 1330984 21587147 := bstep (se 1 (by rfl) ⟨16190360, by rfl⟩ : syracuseStep 21587147 = 32380721) B32380721
theorem B4498793 : Blo 1330984 4498793 := bstep (se 2 (by rfl) ⟨1687047, by rfl⟩ : syracuseStep 4498793 = 3374095) B3374095
theorem B4048573 : Blo 1330984 4048573 := bstep (se 3 (by rfl) ⟨759107, by rfl⟩ : syracuseStep 4048573 = 1518215) B1518215
theorem B2246393 : Blo 1330984 2246393 := bstep (se 2 (by rfl) ⟨842397, by rfl⟩ : syracuseStep 2246393 = 1684795) B1684795
theorem B2246575 : Blo 1330984 2246575 := bstep (se 1 (by rfl) ⟨1684931, by rfl⟩ : syracuseStep 2246575 = 3369863) B3369863
theorem B2246663 : Blo 1330984 2246663 := bstep (se 1 (by rfl) ⟨1684997, by rfl⟩ : syracuseStep 2246663 = 3369995) B3369995
theorem B109332503 : Blo 1330984 109332503 := bstep (se 1 (by rfl) ⟨81999377, by rfl⟩ : syracuseStep 109332503 = 163998755) B163998755
theorem B8538169 : Blo 1330984 8538169 := bstep (se 2 (by rfl) ⟨3201813, by rfl⟩ : syracuseStep 8538169 = 6403627) B6403627
theorem B6744221 : Blo 1330984 6744221 := bstep (se 3 (by rfl) ⟨1264541, by rfl⟩ : syracuseStep 6744221 = 2529083) B2529083
theorem B29599981 : Blo 1330984 29599981 := bstep (se 3 (by rfl) ⟨5549996, by rfl⟩ : syracuseStep 29599981 = 11099993) B11099993
theorem B4802807 : Blo 1330984 4802807 := bstep (se 1 (by rfl) ⟨3602105, by rfl⟩ : syracuseStep 4802807 = 7204211) B7204211
theorem B2247007 : Blo 1330984 2247007 := bstep (se 1 (by rfl) ⟨1685255, by rfl⟩ : syracuseStep 2247007 = 3370511) B3370511
theorem B34130321 : Blo 1330984 34130321 := bstep (se 2 (by rfl) ⟨12798870, by rfl⟩ : syracuseStep 34130321 = 25597741) B25597741
theorem B2247095 : Blo 1330984 2247095 := bstep (se 1 (by rfl) ⟨1685321, by rfl⟩ : syracuseStep 2247095 = 3370643) B3370643
theorem B8530379 : Blo 1330984 8530379 := bstep (se 1 (by rfl) ⟨6397784, by rfl⟩ : syracuseStep 8530379 = 12795569) B12795569
theorem B4803097 : Blo 1330984 4803097 := bstep (se 2 (by rfl) ⟨1801161, by rfl⟩ : syracuseStep 4803097 = 3602323) B3602323
theorem B10799801 : Blo 1330984 10799801 := bstep (se 2 (by rfl) ⟨4049925, by rfl⟩ : syracuseStep 10799801 = 8099851) B8099851
theorem B3369671 : Blo 1330984 3369671 := bstep (se 1 (by rfl) ⟨2527253, by rfl⟩ : syracuseStep 3369671 = 5054507) B5054507
theorem B3369721 : Blo 1330984 3369721 := bstep (se 2 (by rfl) ⟨1263645, by rfl⟩ : syracuseStep 3369721 = 2527291) B2527291
theorem B4803371 : Blo 1330984 4803371 := bstep (se 1 (by rfl) ⟨3602528, by rfl⟩ : syracuseStep 4803371 = 7205057) B7205057
theorem B1895275 : Blo 1330984 1895275 := bstep (se 1 (by rfl) ⟨1421456, by rfl⟩ : syracuseStep 1895275 = 2842913) B2842913
theorem B4492151 : Blo 1330984 4492151 := bstep (se 1 (by rfl) ⟨3369113, by rfl⟩ : syracuseStep 4492151 = 6738227) B6738227
theorem B2247689 : Blo 1330984 2247689 := bstep (se 2 (by rfl) ⟨842883, by rfl⟩ : syracuseStep 2247689 = 1685767) B1685767
theorem B4492367 : Blo 1330984 4492367 := bstep (se 1 (by rfl) ⟨3369275, by rfl⟩ : syracuseStep 4492367 = 6738551) B6738551
theorem B1895503 : Blo 1330984 1895503 := bstep (se 1 (by rfl) ⟨1421627, by rfl⟩ : syracuseStep 1895503 = 2843255) B2843255
theorem B2247851 : Blo 1330984 2247851 := bstep (se 1 (by rfl) ⟨1685888, by rfl⟩ : syracuseStep 2247851 = 3371777) B3371777
theorem B3845291 : Blo 1330984 3845291 := bstep (se 1 (by rfl) ⟨2883968, by rfl⟩ : syracuseStep 3845291 = 5767937) B5767937
theorem B9112769 : Blo 1330984 9112769 := bstep (se 2 (by rfl) ⟨3417288, by rfl⟩ : syracuseStep 9112769 = 6834577) B6834577
theorem B2133191 : Blo 1330984 2133191 := bstep (se 1 (by rfl) ⟨1599893, by rfl⟩ : syracuseStep 2133191 = 3199787) B3199787
theorem B10120463 : Blo 1330984 10120463 := bstep (se 1 (by rfl) ⟨7590347, by rfl⟩ : syracuseStep 10120463 = 15180695) B15180695
theorem B7581053 : Blo 1330984 7581053 := bstep (se 3 (by rfl) ⟨1421447, by rfl⟩ : syracuseStep 7581053 = 2842895) B2842895
theorem B3370369 : Blo 1330984 3370369 := bstep (se 2 (by rfl) ⟨1263888, by rfl⟩ : syracuseStep 3370369 = 2527777) B2527777
theorem B30764461 : Blo 1330984 30764461 := bstep (se 3 (by rfl) ⟨5768336, by rfl⟩ : syracuseStep 30764461 = 11536673) B11536673
theorem B6745517 : Blo 1330984 6745517 := bstep (se 3 (by rfl) ⟨1264784, by rfl⟩ : syracuseStep 6745517 = 2529569) B2529569
theorem B25619885 : Blo 1330984 25619885 := bstep (se 3 (by rfl) ⟨4803728, by rfl⟩ : syracuseStep 25619885 = 9607457) B9607457
theorem B4492745 : Blo 1330984 4492745 := bstep (se 2 (by rfl) ⟨1684779, by rfl⟩ : syracuseStep 4492745 = 3369559) B3369559
theorem B4804105 : Blo 1330984 4804105 := bstep (se 2 (by rfl) ⟨1801539, by rfl⟩ : syracuseStep 4804105 = 3603079) B3603079
theorem B2248249 : Blo 1330984 2248249 := bstep (se 2 (by rfl) ⟨843093, by rfl⟩ : syracuseStep 2248249 = 1686187) B1686187
theorem B2248391 : Blo 1330984 2248391 := bstep (se 1 (by rfl) ⟨1686293, by rfl⟩ : syracuseStep 2248391 = 3372587) B3372587
theorem B4050643 : Blo 1330984 4050643 := bstep (se 1 (by rfl) ⟨3037982, by rfl⟩ : syracuseStep 4050643 = 6075965) B6075965
theorem B4493015 : Blo 1330984 4493015 := bstep (se 1 (by rfl) ⟨3369761, by rfl⟩ : syracuseStep 4493015 = 6739523) B6739523
theorem B1331023 : Blo 1330984 1331023 := bstep (se 1 (by rfl) ⟨998267, by rfl⟩ : syracuseStep 1331023 = 1996535) B1996535
theorem B1331039 : Blo 1330984 1331039 := bstep (se 1 (by rfl) ⟨998279, by rfl⟩ : syracuseStep 1331039 = 1996559) B1996559
theorem B2248553 : Blo 1330984 2248553 := bstep (se 2 (by rfl) ⟨843207, by rfl⟩ : syracuseStep 2248553 = 1686415) B1686415
theorem B5689207 : Blo 1330984 5689207 := bstep (se 1 (by rfl) ⟨4266905, by rfl⟩ : syracuseStep 5689207 = 8533811) B8533811
theorem B1331067 : Blo 1330984 1331067 := bstep (se 1 (by rfl) ⟨998300, by rfl⟩ : syracuseStep 1331067 = 1996601) B1996601
theorem B1331119 : Blo 1330984 1331119 := bstep (se 1 (by rfl) ⟨998339, by rfl⟩ : syracuseStep 1331119 = 1996679) B1996679
theorem B4493231 : Blo 1330984 4493231 := bstep (se 1 (by rfl) ⟨3369923, by rfl⟩ : syracuseStep 4493231 = 6739847) B6739847
theorem B1331143 : Blo 1330984 1331143 := bstep (se 1 (by rfl) ⟨998357, by rfl⟩ : syracuseStep 1331143 = 1996715) B1996715
theorem B1331163 : Blo 1330984 1331163 := bstep (se 1 (by rfl) ⟨998372, by rfl⟩ : syracuseStep 1331163 = 1996745) B1996745
theorem B8540167 : Blo 1330984 8540167 := bstep (se 1 (by rfl) ⟨6405125, by rfl⟩ : syracuseStep 8540167 = 12810251) B12810251
theorem B5402639 : Blo 1330984 5402639 := bstep (se 1 (by rfl) ⟨4051979, by rfl⟩ : syracuseStep 5402639 = 8103959) B8103959
theorem B1331239 : Blo 1330984 1331239 := bstep (se 1 (by rfl) ⟨998429, by rfl⟩ : syracuseStep 1331239 = 1996859) B1996859
theorem B1331279 : Blo 1330984 1331279 := bstep (se 1 (by rfl) ⟨998459, by rfl⟩ : syracuseStep 1331279 = 1996919) B1996919
theorem B1708111 : Blo 1330984 1708111 := bstep (se 1 (by rfl) ⟨1281083, by rfl⟩ : syracuseStep 1708111 = 2562167) B2562167
theorem B3600463 : Blo 1330984 3600463 := bstep (se 1 (by rfl) ⟨2700347, by rfl⟩ : syracuseStep 3600463 = 5400695) B5400695
theorem B1331295 : Blo 1330984 1331295 := bstep (se 1 (by rfl) ⟨998471, by rfl⟩ : syracuseStep 1331295 = 1996943) B1996943
theorem B1331323 : Blo 1330984 1331323 := bstep (se 1 (by rfl) ⟨998492, by rfl⟩ : syracuseStep 1331323 = 1996985) B1996985
theorem B5058713 : Blo 1330984 5058713 := bstep (se 2 (by rfl) ⟨1897017, by rfl⟩ : syracuseStep 5058713 = 3794035) B3794035
theorem B3371179 : Blo 1330984 3371179 := bstep (se 1 (by rfl) ⟨2528384, by rfl⟩ : syracuseStep 3371179 = 5056769) B5056769
theorem B1331375 : Blo 1330984 1331375 := bstep (se 1 (by rfl) ⟨998531, by rfl⟩ : syracuseStep 1331375 = 1997063) B1997063
theorem B1331399 : Blo 1330984 1331399 := bstep (se 1 (by rfl) ⟨998549, by rfl⟩ : syracuseStep 1331399 = 1997099) B1997099
theorem B1331419 : Blo 1330984 1331419 := bstep (se 1 (by rfl) ⟨998564, by rfl⟩ : syracuseStep 1331419 = 1997129) B1997129
theorem B2248951 : Blo 1330984 2248951 := bstep (se 1 (by rfl) ⟨1686713, by rfl⟩ : syracuseStep 2248951 = 3373427) B3373427
theorem B1331495 : Blo 1330984 1331495 := bstep (se 1 (by rfl) ⟨998621, by rfl⟩ : syracuseStep 1331495 = 1997243) B1997243
theorem B8540477 : Blo 1330984 8540477 := bstep (se 3 (by rfl) ⟨1601339, by rfl⟩ : syracuseStep 8540477 = 3202679) B3202679
theorem B1331535 : Blo 1330984 1331535 := bstep (se 1 (by rfl) ⟨998651, by rfl⟩ : syracuseStep 1331535 = 1997303) B1997303
theorem B1331551 : Blo 1330984 1331551 := bstep (se 1 (by rfl) ⟨998663, by rfl⟩ : syracuseStep 1331551 = 1997327) B1997327
theorem B2527595 : Blo 1330984 2527595 := bstep (se 1 (by rfl) ⟨1895696, by rfl⟩ : syracuseStep 2527595 = 3791393) B3791393
theorem B1331579 : Blo 1330984 1331579 := bstep (se 1 (by rfl) ⟨998684, by rfl⟩ : syracuseStep 1331579 = 1997369) B1997369
theorem B8532377 : Blo 1330984 8532377 := bstep (se 2 (by rfl) ⟨3199641, by rfl⟩ : syracuseStep 8532377 = 6399283) B6399283
theorem B1331631 : Blo 1330984 1331631 := bstep (se 1 (by rfl) ⟨998723, by rfl⟩ : syracuseStep 1331631 = 1997447) B1997447
theorem B2249147 : Blo 1330984 2249147 := bstep (se 1 (by rfl) ⟨1686860, by rfl⟩ : syracuseStep 2249147 = 3373721) B3373721
theorem B1331655 : Blo 1330984 1331655 := bstep (se 1 (by rfl) ⟨998741, by rfl⟩ : syracuseStep 1331655 = 1997483) B1997483
theorem B1331675 : Blo 1330984 1331675 := bstep (se 1 (by rfl) ⟨998756, by rfl⟩ : syracuseStep 1331675 = 1997513) B1997513
theorem B3371483 : Blo 1330984 3371483 := bstep (se 1 (by rfl) ⟨2528612, by rfl⟩ : syracuseStep 3371483 = 5057225) B5057225
theorem B1331751 : Blo 1330984 1331751 := bstep (se 1 (by rfl) ⟨998813, by rfl⟩ : syracuseStep 1331751 = 1997627) B1997627
theorem B2249255 : Blo 1330984 2249255 := bstep (se 1 (by rfl) ⟨1686941, by rfl⟩ : syracuseStep 2249255 = 3373883) B3373883
theorem B2527823 : Blo 1330984 2527823 := bstep (se 1 (by rfl) ⟨1895867, by rfl⟩ : syracuseStep 2527823 = 3791735) B3791735
theorem B1331791 : Blo 1330984 1331791 := bstep (se 1 (by rfl) ⟨998843, by rfl⟩ : syracuseStep 1331791 = 1997687) B1997687
theorem B1331807 : Blo 1330984 1331807 := bstep (se 1 (by rfl) ⟨998855, by rfl⟩ : syracuseStep 1331807 = 1997711) B1997711
theorem B2994785 : Blo 1330984 2994785 := bstep (se 2 (by rfl) ⟨1123044, by rfl⟩ : syracuseStep 2994785 = 2246089) B2246089
theorem B5059169 : Blo 1330984 5059169 := bstep (se 2 (by rfl) ⟨1897188, by rfl⟩ : syracuseStep 5059169 = 3794377) B3794377
theorem B1331835 : Blo 1330984 1331835 := bstep (se 1 (by rfl) ⟨998876, by rfl⟩ : syracuseStep 1331835 = 1997753) B1997753
theorem B1331887 : Blo 1330984 1331887 := bstep (se 1 (by rfl) ⟨998915, by rfl⟩ : syracuseStep 1331887 = 1997831) B1997831
theorem B1331911 : Blo 1330984 1331911 := bstep (se 1 (by rfl) ⟨998933, by rfl⟩ : syracuseStep 1331911 = 1997867) B1997867
theorem B24285905 : Blo 1330984 24285905 := bstep (se 2 (by rfl) ⟨9107214, by rfl⟩ : syracuseStep 24285905 = 18214429) B18214429
theorem B1331931 : Blo 1330984 1331931 := bstep (se 1 (by rfl) ⟨998948, by rfl⟩ : syracuseStep 1331931 = 1997897) B1997897
theorem B1332007 : Blo 1330984 1332007 := bstep (se 1 (by rfl) ⟨999005, by rfl⟩ : syracuseStep 1332007 = 1998011) B1998011
theorem B1332047 : Blo 1330984 1332047 := bstep (se 1 (by rfl) ⟨999035, by rfl⟩ : syracuseStep 1332047 = 1998071) B1998071
theorem B1332063 : Blo 1330984 1332063 := bstep (se 1 (by rfl) ⟨999047, by rfl⟩ : syracuseStep 1332063 = 1998095) B1998095
theorem B1332091 : Blo 1330984 1332091 := bstep (se 1 (by rfl) ⟨999068, by rfl⟩ : syracuseStep 1332091 = 1998137) B1998137
theorem B1332143 : Blo 1330984 1332143 := bstep (se 1 (by rfl) ⟨999107, by rfl⟩ : syracuseStep 1332143 = 1998215) B1998215
theorem B2995127 : Blo 1330984 2995127 := bstep (se 1 (by rfl) ⟨2246345, by rfl⟩ : syracuseStep 2995127 = 4492691) B4492691
theorem B1332167 : Blo 1330984 1332167 := bstep (se 1 (by rfl) ⟨999125, by rfl⟩ : syracuseStep 1332167 = 1998251) B1998251
theorem B1332187 : Blo 1330984 1332187 := bstep (se 1 (by rfl) ⟨999140, by rfl⟩ : syracuseStep 1332187 = 1998281) B1998281
theorem B7582693 : Blo 1330984 7582693 := bstep (se 4 (by rfl) ⟨710877, by rfl⟩ : syracuseStep 7582693 = 1421755) B1421755
theorem B6747137 : Blo 1330984 6747137 := bstep (se 2 (by rfl) ⟨2530176, by rfl⟩ : syracuseStep 6747137 = 5060353) B5060353
theorem B2528263 : Blo 1330984 2528263 := bstep (se 1 (by rfl) ⟨1896197, by rfl⟩ : syracuseStep 2528263 = 3792395) B3792395
theorem B1332263 : Blo 1330984 1332263 := bstep (se 1 (by rfl) ⟨999197, by rfl⟩ : syracuseStep 1332263 = 1998395) B1998395
theorem B1332303 : Blo 1330984 1332303 := bstep (se 1 (by rfl) ⟨999227, by rfl⟩ : syracuseStep 1332303 = 1998455) B1998455
theorem B1332319 : Blo 1330984 1332319 := bstep (se 1 (by rfl) ⟨999239, by rfl⟩ : syracuseStep 1332319 = 1998479) B1998479
theorem B1332347 : Blo 1330984 1332347 := bstep (se 1 (by rfl) ⟨999260, by rfl⟩ : syracuseStep 1332347 = 1998521) B1998521
theorem B1332399 : Blo 1330984 1332399 := bstep (se 1 (by rfl) ⟨999299, by rfl⟩ : syracuseStep 1332399 = 1998599) B1998599
theorem B1332423 : Blo 1330984 1332423 := bstep (se 1 (by rfl) ⟨999317, by rfl⟩ : syracuseStep 1332423 = 1998635) B1998635
theorem B1332443 : Blo 1330984 1332443 := bstep (se 1 (by rfl) ⟨999332, by rfl⟩ : syracuseStep 1332443 = 1998665) B1998665
theorem B7582967 : Blo 1330984 7582967 := bstep (se 1 (by rfl) ⟨5687225, by rfl⟩ : syracuseStep 7582967 = 11374451) B11374451
theorem B1332519 : Blo 1330984 1332519 := bstep (se 1 (by rfl) ⟨999389, by rfl⟩ : syracuseStep 1332519 = 1998779) B1998779
theorem B1332559 : Blo 1330984 1332559 := bstep (se 1 (by rfl) ⟨999419, by rfl⟩ : syracuseStep 1332559 = 1998839) B1998839
theorem B1332575 : Blo 1330984 1332575 := bstep (se 1 (by rfl) ⟨999431, by rfl⟩ : syracuseStep 1332575 = 1998863) B1998863
theorem B1332603 : Blo 1330984 1332603 := bstep (se 1 (by rfl) ⟨999452, by rfl⟩ : syracuseStep 1332603 = 1998905) B1998905
theorem B1332655 : Blo 1330984 1332655 := bstep (se 1 (by rfl) ⟨999491, by rfl⟩ : syracuseStep 1332655 = 1998983) B1998983
theorem B1332679 : Blo 1330984 1332679 := bstep (se 1 (by rfl) ⟨999509, by rfl⟩ : syracuseStep 1332679 = 1999019) B1999019
theorem B1332699 : Blo 1330984 1332699 := bstep (se 1 (by rfl) ⟨999524, by rfl⟩ : syracuseStep 1332699 = 1999049) B1999049
theorem B7583219 : Blo 1330984 7583219 := bstep (se 1 (by rfl) ⟨5687414, by rfl⟩ : syracuseStep 7583219 = 11374829) B11374829
theorem B2995721 : Blo 1330984 2995721 := bstep (se 2 (by rfl) ⟨1123395, by rfl⟩ : syracuseStep 2995721 = 2246791) B2246791
theorem B1332775 : Blo 1330984 1332775 := bstep (se 1 (by rfl) ⟨999581, by rfl⟩ : syracuseStep 1332775 = 1999163) B1999163
theorem B1332815 : Blo 1330984 1332815 := bstep (se 1 (by rfl) ⟨999611, by rfl⟩ : syracuseStep 1332815 = 1999223) B1999223
theorem B1332831 : Blo 1330984 1332831 := bstep (se 1 (by rfl) ⟨999623, by rfl⟩ : syracuseStep 1332831 = 1999247) B1999247
theorem B1332859 : Blo 1330984 1332859 := bstep (se 1 (by rfl) ⟨999644, by rfl⟩ : syracuseStep 1332859 = 1999289) B1999289
theorem B5691019 : Blo 1330984 5691019 := bstep (se 1 (by rfl) ⟨4268264, by rfl⟩ : syracuseStep 5691019 = 8536529) B8536529
theorem B1332911 : Blo 1330984 1332911 := bstep (se 1 (by rfl) ⟨999683, by rfl⟩ : syracuseStep 1332911 = 1999367) B1999367
theorem B1996487 : Blo 1330984 1996487 := bstep (se 1 (by rfl) ⟨1497365, by rfl⟩ : syracuseStep 1996487 = 2994731) B2994731
theorem B1332935 : Blo 1330984 1332935 := bstep (se 1 (by rfl) ⟨999701, by rfl⟩ : syracuseStep 1332935 = 1999403) B1999403
theorem B1332955 : Blo 1330984 1332955 := bstep (se 1 (by rfl) ⟨999716, by rfl⟩ : syracuseStep 1332955 = 1999433) B1999433
theorem B1922809 : Blo 1330984 1922809 := bstep (se 2 (by rfl) ⟨721053, by rfl⟩ : syracuseStep 1922809 = 1442107) B1442107
theorem B6747947 : Blo 1330984 6747947 := bstep (se 1 (by rfl) ⟨5060960, by rfl⟩ : syracuseStep 6747947 = 10121921) B10121921
theorem B2996063 : Blo 1330984 2996063 := bstep (se 1 (by rfl) ⟨2247047, by rfl⟩ : syracuseStep 2996063 = 4494095) B4494095
theorem B1996649 : Blo 1330984 1996649 := bstep (se 2 (by rfl) ⟨748743, by rfl⟩ : syracuseStep 1996649 = 1497487) B1497487
theorem B1922923 : Blo 1330984 1922923 := bstep (se 1 (by rfl) ⟨1442192, by rfl⟩ : syracuseStep 1922923 = 2884385) B2884385
theorem B9729953 : Blo 1330984 9729953 := bstep (se 2 (by rfl) ⟨3648732, by rfl⟩ : syracuseStep 9729953 = 7297465) B7297465
theorem B3372961 : Blo 1330984 3372961 := bstep (se 2 (by rfl) ⟨1264860, by rfl⟩ : syracuseStep 3372961 = 2529721) B2529721
theorem B1996727 : Blo 1330984 1996727 := bstep (se 1 (by rfl) ⟨1497545, by rfl⟩ : syracuseStep 1996727 = 2995091) B2995091
theorem B1996763 : Blo 1330984 1996763 := bstep (se 1 (by rfl) ⟨1497572, by rfl⟩ : syracuseStep 1996763 = 2995145) B2995145
theorem B2996243 : Blo 1330984 2996243 := bstep (se 1 (by rfl) ⟨2247182, by rfl⟩ : syracuseStep 2996243 = 4494365) B4494365
theorem B5060627 : Blo 1330984 5060627 := bstep (se 1 (by rfl) ⟨3795470, by rfl⟩ : syracuseStep 5060627 = 7590941) B7590941
theorem B2529319 : Blo 1330984 2529319 := bstep (se 1 (by rfl) ⟨1896989, by rfl⟩ : syracuseStep 2529319 = 3793979) B3793979
theorem B46160117 : Blo 1330984 46160117 := bstep (se 5 (by rfl) ⟨2163755, by rfl⟩ : syracuseStep 46160117 = 4327511) B4327511
theorem B4495607 : Blo 1330984 4495607 := bstep (se 1 (by rfl) ⟨3371705, by rfl⟩ : syracuseStep 4495607 = 6743411) B6743411
theorem B2996585 : Blo 1330984 2996585 := bstep (se 2 (by rfl) ⟨1123719, by rfl⟩ : syracuseStep 2996585 = 2247439) B2247439
theorem B1350011 : Blo 1330984 1350011 := bstep (se 1 (by rfl) ⟨1012508, by rfl⟩ : syracuseStep 1350011 = 2025017) B2025017
theorem B1997231 : Blo 1330984 1997231 := bstep (se 1 (by rfl) ⟨1497923, by rfl⟩ : syracuseStep 1997231 = 2995847) B2995847
theorem B1997321 : Blo 1330984 1997321 := bstep (se 2 (by rfl) ⟨748995, by rfl⟩ : syracuseStep 1997321 = 1497991) B1497991
theorem B1997351 : Blo 1330984 1997351 := bstep (se 1 (by rfl) ⟨1498013, by rfl⟩ : syracuseStep 1997351 = 2996027) B2996027
theorem B4495931 : Blo 1330984 4495931 := bstep (se 1 (by rfl) ⟨3371948, by rfl⟩ : syracuseStep 4495931 = 6743897) B6743897
theorem B1997435 : Blo 1330984 1997435 := bstep (se 1 (by rfl) ⟨1498076, by rfl⟩ : syracuseStep 1997435 = 2996153) B2996153
theorem B5397191 : Blo 1330984 5397191 := bstep (se 1 (by rfl) ⟨4047893, by rfl⟩ : syracuseStep 5397191 = 8095787) B8095787
theorem B1997561 : Blo 1330984 1997561 := bstep (se 2 (by rfl) ⟨749085, by rfl⟩ : syracuseStep 1997561 = 1498171) B1498171
theorem B4496201 : Blo 1330984 4496201 := bstep (se 2 (by rfl) ⟨1686075, by rfl⟩ : syracuseStep 4496201 = 3372151) B3372151
theorem B3791711 : Blo 1330984 3791711 := bstep (se 1 (by rfl) ⟨2843783, by rfl⟩ : syracuseStep 3791711 = 5687567) B5687567
theorem B1997663 : Blo 1330984 1997663 := bstep (se 1 (by rfl) ⟨1498247, by rfl⟩ : syracuseStep 1997663 = 2996495) B2996495
theorem B1997675 : Blo 1330984 1997675 := bstep (se 1 (by rfl) ⟨1498256, by rfl⟩ : syracuseStep 1997675 = 2996513) B2996513
theorem B2997179 : Blo 1330984 2997179 := bstep (se 1 (by rfl) ⟨2247884, by rfl⟩ : syracuseStep 2997179 = 4495769) B4495769
theorem B8535041 : Blo 1330984 8535041 := bstep (se 2 (by rfl) ⟨3200640, by rfl⟩ : syracuseStep 8535041 = 6401281) B6401281
theorem B2997305 : Blo 1330984 2997305 := bstep (se 2 (by rfl) ⟨1123989, by rfl⟩ : syracuseStep 2997305 = 2247979) B2247979
theorem B3800143 : Blo 1330984 3800143 := bstep (se 1 (by rfl) ⟨2850107, by rfl⟩ : syracuseStep 3800143 = 5700215) B5700215
theorem B1997903 : Blo 1330984 1997903 := bstep (se 1 (by rfl) ⟨1498427, by rfl⟩ : syracuseStep 1997903 = 2996855) B2996855
theorem B1998023 : Blo 1330984 1998023 := bstep (se 1 (by rfl) ⟨1498517, by rfl⟩ : syracuseStep 1998023 = 2997035) B2997035
theorem B1998185 : Blo 1330984 1998185 := bstep (se 2 (by rfl) ⟨749319, by rfl⟩ : syracuseStep 1998185 = 1498639) B1498639
theorem B2997647 : Blo 1330984 2997647 := bstep (se 1 (by rfl) ⟨2248235, by rfl⟩ : syracuseStep 2997647 = 4496471) B4496471
theorem B1998263 : Blo 1330984 1998263 := bstep (se 1 (by rfl) ⟨1498697, by rfl⟩ : syracuseStep 1998263 = 2997395) B2997395
theorem B6741467 : Blo 1330984 6741467 := bstep (se 1 (by rfl) ⟨5056100, by rfl⟩ : syracuseStep 6741467 = 10112201) B10112201
theorem B1998299 : Blo 1330984 1998299 := bstep (se 1 (by rfl) ⟨1498724, by rfl⟩ : syracuseStep 1998299 = 2997449) B2997449
theorem B10255835 : Blo 1330984 10255835 := bstep (se 1 (by rfl) ⟨7691876, by rfl⟩ : syracuseStep 10255835 = 15383753) B15383753
theorem B5692967 : Blo 1330984 5692967 := bstep (se 1 (by rfl) ⟨4269725, by rfl⟩ : syracuseStep 5692967 = 8539451) B8539451
theorem B1498747 : Blo 1330984 1498747 := bstep (se 1 (by rfl) ⟨1124060, by rfl⟩ : syracuseStep 1498747 = 2248121) B2248121
theorem B7585427 : Blo 1330984 7585427 := bstep (se 1 (by rfl) ⟨5689070, by rfl⟩ : syracuseStep 7585427 = 11378141) B11378141
theorem B4800185 : Blo 1330984 4800185 := bstep (se 2 (by rfl) ⟨1800069, by rfl⟩ : syracuseStep 4800185 = 3600139) B3600139
theorem B2997971 : Blo 1330984 2997971 := bstep (se 1 (by rfl) ⟨2248478, by rfl⟩ : syracuseStep 2997971 = 4496957) B4496957
theorem B4800329 : Blo 1330984 4800329 := bstep (se 2 (by rfl) ⟨1800123, by rfl⟩ : syracuseStep 4800329 = 3600247) B3600247
theorem B3039049 : Blo 1330984 3039049 := bstep (se 2 (by rfl) ⟨1139643, by rfl⟩ : syracuseStep 3039049 = 2279287) B2279287
theorem B10952567 : Blo 1330984 10952567 := bstep (se 1 (by rfl) ⟨8214425, by rfl⟩ : syracuseStep 10952567 = 16428851) B16428851
theorem B16195463 : Blo 1330984 16195463 := bstep (se 1 (by rfl) ⟨12146597, by rfl⟩ : syracuseStep 16195463 = 24293195) B24293195
theorem B1998767 : Blo 1330984 1998767 := bstep (se 1 (by rfl) ⟨1499075, by rfl⟩ : syracuseStep 1998767 = 2998151) B2998151
theorem B3243959 : Blo 1330984 3243959 := bstep (se 1 (by rfl) ⟨2432969, by rfl⟩ : syracuseStep 3243959 = 4865939) B4865939
theorem B4497335 : Blo 1330984 4497335 := bstep (se 1 (by rfl) ⟨3373001, by rfl⟩ : syracuseStep 4497335 = 6746003) B6746003
theorem B6741953 : Blo 1330984 6741953 := bstep (se 2 (by rfl) ⟨2528232, by rfl⟩ : syracuseStep 6741953 = 5056465) B5056465
theorem B11386889 : Blo 1330984 11386889 := bstep (se 2 (by rfl) ⟨4270083, by rfl⟩ : syracuseStep 11386889 = 8540167) B8540167
theorem B2277481 : Blo 1330984 2277481 := bstep (se 2 (by rfl) ⟨854055, by rfl⟩ : syracuseStep 2277481 = 1708111) B1708111
theorem B4800617 : Blo 1330984 4800617 := bstep (se 2 (by rfl) ⟨1800231, by rfl⟩ : syracuseStep 4800617 = 3600463) B3600463
theorem B1998953 : Blo 1330984 1998953 := bstep (se 2 (by rfl) ⟨749607, by rfl⟩ : syracuseStep 1998953 = 1499215) B1499215
theorem B5693651 : Blo 1330984 5693651 := bstep (se 1 (by rfl) ⟨4270238, by rfl⟩ : syracuseStep 5693651 = 8540477) B8540477
theorem B1499431 : Blo 1330984 1499431 := bstep (se 1 (by rfl) ⟨1124573, by rfl⟩ : syracuseStep 1499431 = 2249147) B2249147
theorem B2998601 : Blo 1330984 2998601 := bstep (se 2 (by rfl) ⟨1124475, by rfl⟩ : syracuseStep 2998601 = 2248951) B2248951
theorem B2998619 : Blo 1330984 2998619 := bstep (se 1 (by rfl) ⟨2248964, by rfl⟩ : syracuseStep 2998619 = 4497929) B4497929
theorem B4800875 : Blo 1330984 4800875 := bstep (se 1 (by rfl) ⟨3600656, by rfl⟩ : syracuseStep 4800875 = 7201313) B7201313
theorem B1499503 : Blo 1330984 1499503 := bstep (se 1 (by rfl) ⟨1124627, by rfl⟩ : syracuseStep 1499503 = 2249255) B2249255
theorem B1999271 : Blo 1330984 1999271 := bstep (se 1 (by rfl) ⟨1499453, by rfl⟩ : syracuseStep 1999271 = 2998907) B2998907
theorem B1999355 : Blo 1330984 1999355 := bstep (se 1 (by rfl) ⟨1499516, by rfl⟩ : syracuseStep 1999355 = 2999033) B2999033
theorem B6078995 : Blo 1330984 6078995 := bstep (se 1 (by rfl) ⟨4559246, by rfl⟩ : syracuseStep 6078995 = 9118493) B9118493
theorem B4498091 : Blo 1330984 4498091 := bstep (se 1 (by rfl) ⟨3373568, by rfl⟩ : syracuseStep 4498091 = 6747137) B6747137
theorem B5055311 : Blo 1330984 5055311 := bstep (se 1 (by rfl) ⟨3791483, by rfl⟩ : syracuseStep 5055311 = 7582967) B7582967
theorem B2999195 : Blo 1330984 2999195 := bstep (se 1 (by rfl) ⟨2249396, by rfl⟩ : syracuseStep 2999195 = 4498793) B4498793
theorem B5055479 : Blo 1330984 5055479 := bstep (se 1 (by rfl) ⟨3791609, by rfl⟩ : syracuseStep 5055479 = 7583219) B7583219
theorem B4498631 : Blo 1330984 4498631 := bstep (se 1 (by rfl) ⟨3373973, by rfl⟩ : syracuseStep 4498631 = 6747947) B6747947
theorem B10110257 : Blo 1330984 10110257 := bstep (se 2 (by rfl) ⟨3791346, by rfl⟩ : syracuseStep 10110257 = 7582693) B7582693
theorem B5686919 : Blo 1330984 5686919 := bstep (se 1 (by rfl) ⟨4265189, by rfl⟩ : syracuseStep 5686919 = 8530379) B8530379
theorem B3598127 : Blo 1330984 3598127 := bstep (se 1 (by rfl) ⟨2698595, by rfl⟩ : syracuseStep 3598127 = 5397191) B5397191
theorem B2246447 : Blo 1330984 2246447 := bstep (se 1 (by rfl) ⟨1684835, by rfl⟩ : syracuseStep 2246447 = 3369671) B3369671
theorem B41019281 : Blo 1330984 41019281 := bstep (se 2 (by rfl) ⟨15382230, by rfl⟩ : syracuseStep 41019281 = 30764461) B30764461
theorem B7588025 : Blo 1330984 7588025 := bstep (se 2 (by rfl) ⟨2845509, by rfl⟩ : syracuseStep 7588025 = 5691019) B5691019
theorem B10111229 : Blo 1330984 10111229 := bstep (se 3 (by rfl) ⟨1895855, by rfl⟩ : syracuseStep 10111229 = 3791711) B3791711
theorem B5400857 : Blo 1330984 5400857 := bstep (se 2 (by rfl) ⟨2025321, by rfl⟩ : syracuseStep 5400857 = 4050643) B4050643
theorem B3795311 : Blo 1330984 3795311 := bstep (se 1 (by rfl) ⟨2846483, by rfl⟩ : syracuseStep 3795311 = 5692967) B5692967
theorem B5056951 : Blo 1330984 5056951 := bstep (se 1 (by rfl) ⟨3792713, by rfl⟩ : syracuseStep 5056951 = 7585427) B7585427
theorem B7301711 : Blo 1330984 7301711 := bstep (se 1 (by rfl) ⟨5476283, by rfl⟩ : syracuseStep 7301711 = 10952567) B10952567
theorem B5057423 : Blo 1330984 5057423 := bstep (se 1 (by rfl) ⟨3793067, by rfl⟩ : syracuseStep 5057423 = 7586135) B7586135
theorem B3369883 : Blo 1330984 3369883 := bstep (se 1 (by rfl) ⟨2527412, by rfl⟩ : syracuseStep 3369883 = 5054825) B5054825
theorem B5688251 : Blo 1330984 5688251 := bstep (se 1 (by rfl) ⟨4266188, by rfl⟩ : syracuseStep 5688251 = 8532377) B8532377
theorem B2247655 : Blo 1330984 2247655 := bstep (se 1 (by rfl) ⟨1685741, by rfl⟩ : syracuseStep 2247655 = 3371483) B3371483
theorem B16190603 : Blo 1330984 16190603 := bstep (se 1 (by rfl) ⟨12142952, by rfl⟩ : syracuseStep 16190603 = 24285905) B24285905
theorem B3419351 : Blo 1330984 3419351 := bstep (se 1 (by rfl) ⟨2564513, by rfl⟩ : syracuseStep 3419351 = 5129027) B5129027
theorem B6745355 : Blo 1330984 6745355 := bstep (se 1 (by rfl) ⟨5059016, by rfl⟩ : syracuseStep 6745355 = 10118033) B10118033
theorem B5123359 : Blo 1330984 5123359 := bstep (se 1 (by rfl) ⟨3842519, by rfl⟩ : syracuseStep 5123359 = 7685039) B7685039
theorem B1895719 : Blo 1330984 1895719 := bstep (se 1 (by rfl) ⟨1421789, by rfl⟩ : syracuseStep 1895719 = 2843579) B2843579
theorem B3600029 : Blo 1330984 3600029 := bstep (se 3 (by rfl) ⟨675005, by rfl⟩ : syracuseStep 3600029 = 1350011) B1350011
theorem B4492961 : Blo 1330984 4492961 := bstep (se 2 (by rfl) ⟨1684860, by rfl⟩ : syracuseStep 4492961 = 3369721) B3369721
theorem B2698913 : Blo 1330984 2698913 := bstep (se 2 (by rfl) ⟨1012092, by rfl⟩ : syracuseStep 2698913 = 2024185) B2024185
theorem B1330991 : Blo 1330984 1330991 := bstep (se 1 (by rfl) ⟨998243, by rfl⟩ : syracuseStep 1330991 = 1996487) B1996487
theorem B2527033 : Blo 1330984 2527033 := bstep (se 2 (by rfl) ⟨947637, by rfl⟩ : syracuseStep 2527033 = 1895275) B1895275
theorem B1331099 : Blo 1330984 1331099 := bstep (se 1 (by rfl) ⟨998324, by rfl⟩ : syracuseStep 1331099 = 1996649) B1996649
theorem B1331151 : Blo 1330984 1331151 := bstep (se 1 (by rfl) ⟨998363, by rfl⟩ : syracuseStep 1331151 = 1996727) B1996727
theorem B1331175 : Blo 1330984 1331175 := bstep (se 1 (by rfl) ⟨998381, by rfl⟩ : syracuseStep 1331175 = 1996763) B1996763
theorem B3371017 : Blo 1330984 3371017 := bstep (se 2 (by rfl) ⟨1264131, by rfl⟩ : syracuseStep 3371017 = 2528263) B2528263
theorem B72888335 : Blo 1330984 72888335 := bstep (se 1 (by rfl) ⟨54666251, by rfl⟩ : syracuseStep 72888335 = 109332503) B109332503
theorem B2527337 : Blo 1330984 2527337 := bstep (se 2 (by rfl) ⟨947751, by rfl⟩ : syracuseStep 2527337 = 1895503) B1895503
theorem B5066857 : Blo 1330984 5066857 := bstep (se 2 (by rfl) ⟨1900071, by rfl⟩ : syracuseStep 5066857 = 3800143) B3800143
theorem B30773411 : Blo 1330984 30773411 := bstep (se 1 (by rfl) ⟨23080058, by rfl⟩ : syracuseStep 30773411 = 46160117) B46160117
theorem B22753547 : Blo 1330984 22753547 := bstep (se 1 (by rfl) ⟨17065160, by rfl⟩ : syracuseStep 22753547 = 34130321) B34130321
theorem B1331487 : Blo 1330984 1331487 := bstep (se 1 (by rfl) ⟨998615, by rfl⟩ : syracuseStep 1331487 = 1997231) B1997231
theorem B1331547 : Blo 1330984 1331547 := bstep (se 1 (by rfl) ⟨998660, by rfl⟩ : syracuseStep 1331547 = 1997321) B1997321
theorem B1331567 : Blo 1330984 1331567 := bstep (se 1 (by rfl) ⟨998675, by rfl⟩ : syracuseStep 1331567 = 1997351) B1997351
theorem B16208261 : Blo 1330984 16208261 := bstep (se 4 (by rfl) ⟨1519524, by rfl⟩ : syracuseStep 16208261 = 3039049) B3039049
theorem B1331623 : Blo 1330984 1331623 := bstep (se 1 (by rfl) ⟨998717, by rfl⟩ : syracuseStep 1331623 = 1997435) B1997435
theorem B1331707 : Blo 1330984 1331707 := bstep (se 1 (by rfl) ⟨998780, by rfl⟩ : syracuseStep 1331707 = 1997561) B1997561
theorem B4493825 : Blo 1330984 4493825 := bstep (se 2 (by rfl) ⟨1685184, by rfl⟩ : syracuseStep 4493825 = 3370369) B3370369
theorem B1331775 : Blo 1330984 1331775 := bstep (se 1 (by rfl) ⟨998831, by rfl⟩ : syracuseStep 1331775 = 1997663) B1997663
theorem B1331783 : Blo 1330984 1331783 := bstep (se 1 (by rfl) ⟨998837, by rfl⟩ : syracuseStep 1331783 = 1997675) B1997675
theorem B2994767 : Blo 1330984 2994767 := bstep (se 1 (by rfl) ⟨2246075, by rfl⟩ : syracuseStep 2994767 = 4492151) B4492151
theorem B5690027 : Blo 1330984 5690027 := bstep (se 1 (by rfl) ⟨4267520, by rfl⟩ : syracuseStep 5690027 = 8535041) B8535041
theorem B2994911 : Blo 1330984 2994911 := bstep (se 1 (by rfl) ⟨2246183, by rfl⟩ : syracuseStep 2994911 = 4492367) B4492367
theorem B1331935 : Blo 1330984 1331935 := bstep (se 1 (by rfl) ⟨998951, by rfl⟩ : syracuseStep 1331935 = 1997903) B1997903
theorem B6075179 : Blo 1330984 6075179 := bstep (se 1 (by rfl) ⟨4556384, by rfl⟩ : syracuseStep 6075179 = 9112769) B9112769
theorem B1422127 : Blo 1330984 1422127 := bstep (se 1 (by rfl) ⟨1066595, by rfl⟩ : syracuseStep 1422127 = 2133191) B2133191
theorem B1332015 : Blo 1330984 1332015 := bstep (se 1 (by rfl) ⟨999011, by rfl⟩ : syracuseStep 1332015 = 1998023) B1998023
theorem B6746975 : Blo 1330984 6746975 := bstep (se 1 (by rfl) ⟨5060231, by rfl⟩ : syracuseStep 6746975 = 10120463) B10120463
theorem B1332123 : Blo 1330984 1332123 := bstep (se 1 (by rfl) ⟨999092, by rfl⟩ : syracuseStep 1332123 = 1998185) B1998185
theorem B1332175 : Blo 1330984 1332175 := bstep (se 1 (by rfl) ⟨999131, by rfl⟩ : syracuseStep 1332175 = 1998263) B1998263
theorem B2995163 : Blo 1330984 2995163 := bstep (se 1 (by rfl) ⟨2246372, by rfl⟩ : syracuseStep 2995163 = 4492745) B4492745
theorem B4494311 : Blo 1330984 4494311 := bstep (se 1 (by rfl) ⟨3370733, by rfl⟩ : syracuseStep 4494311 = 6741467) B6741467
theorem B1332199 : Blo 1330984 1332199 := bstep (se 1 (by rfl) ⟨999149, by rfl⟩ : syracuseStep 1332199 = 1998299) B1998299
theorem B6837223 : Blo 1330984 6837223 := bstep (se 1 (by rfl) ⟨5127917, by rfl⟩ : syracuseStep 6837223 = 10255835) B10255835
theorem B3200123 : Blo 1330984 3200123 := bstep (se 1 (by rfl) ⟨2400092, by rfl⟩ : syracuseStep 3200123 = 4800185) B4800185
theorem B2995343 : Blo 1330984 2995343 := bstep (se 1 (by rfl) ⟨2246507, by rfl⟩ : syracuseStep 2995343 = 4493015) B4493015
theorem B3200219 : Blo 1330984 3200219 := bstep (se 1 (by rfl) ⟨2400164, by rfl⟩ : syracuseStep 3200219 = 4800329) B4800329
theorem B2995433 : Blo 1330984 2995433 := bstep (se 2 (by rfl) ⟨1123287, by rfl⟩ : syracuseStep 2995433 = 2246575) B2246575
theorem B2995487 : Blo 1330984 2995487 := bstep (se 1 (by rfl) ⟨2246615, by rfl⟩ : syracuseStep 2995487 = 4493231) B4493231
theorem B1332511 : Blo 1330984 1332511 := bstep (se 1 (by rfl) ⟨999383, by rfl⟩ : syracuseStep 1332511 = 1998767) B1998767
theorem B4494635 : Blo 1330984 4494635 := bstep (se 1 (by rfl) ⟨3370976, by rfl⟩ : syracuseStep 4494635 = 6741953) B6741953
theorem B5690711 : Blo 1330984 5690711 := bstep (se 1 (by rfl) ⟨4268033, by rfl⟩ : syracuseStep 5690711 = 8536067) B8536067
theorem B1332571 : Blo 1330984 1332571 := bstep (se 1 (by rfl) ⟨999428, by rfl⟩ : syracuseStep 1332571 = 1998857) B1998857
theorem B3601759 : Blo 1330984 3601759 := bstep (se 1 (by rfl) ⟨2701319, by rfl⟩ : syracuseStep 3601759 = 5402639) B5402639
theorem B1332591 : Blo 1330984 1332591 := bstep (se 1 (by rfl) ⟨999443, by rfl⟩ : syracuseStep 1332591 = 1998887) B1998887
theorem B3372425 : Blo 1330984 3372425 := bstep (se 2 (by rfl) ⟨1264659, by rfl⟩ : syracuseStep 3372425 = 2529319) B2529319
theorem B6739361 : Blo 1330984 6739361 := bstep (se 2 (by rfl) ⟨2527260, by rfl⟩ : syracuseStep 6739361 = 5054521) B5054521
theorem B11384225 : Blo 1330984 11384225 := bstep (se 2 (by rfl) ⟨4269084, by rfl⟩ : syracuseStep 11384225 = 8538169) B8538169
theorem B1332647 : Blo 1330984 1332647 := bstep (se 1 (by rfl) ⟨999485, by rfl⟩ : syracuseStep 1332647 = 1998971) B1998971
theorem B3372475 : Blo 1330984 3372475 := bstep (se 1 (by rfl) ⟨2529356, by rfl⟩ : syracuseStep 3372475 = 5058713) B5058713
theorem B1332731 : Blo 1330984 1332731 := bstep (se 1 (by rfl) ⟨999548, by rfl⟩ : syracuseStep 1332731 = 1999097) B1999097
theorem B4494905 : Blo 1330984 4494905 := bstep (se 2 (by rfl) ⟨1685589, by rfl⟩ : syracuseStep 4494905 = 3371179) B3371179
theorem B1332799 : Blo 1330984 1332799 := bstep (se 1 (by rfl) ⟨999599, by rfl⟩ : syracuseStep 1332799 = 1999199) B1999199
theorem B1685063 : Blo 1330984 1685063 := bstep (se 1 (by rfl) ⟨1263797, by rfl⟩ : syracuseStep 1685063 = 2527595) B2527595
theorem B1332807 : Blo 1330984 1332807 := bstep (se 1 (by rfl) ⟨999605, by rfl⟩ : syracuseStep 1332807 = 1999211) B1999211
theorem B1685215 : Blo 1330984 1685215 := bstep (se 1 (by rfl) ⟨1263911, by rfl⟩ : syracuseStep 1685215 = 2527823) B2527823
theorem B1332959 : Blo 1330984 1332959 := bstep (se 1 (by rfl) ⟨999719, by rfl⟩ : syracuseStep 1332959 = 1999439) B1999439
theorem B1996523 : Blo 1330984 1996523 := bstep (se 1 (by rfl) ⟨1497392, by rfl⟩ : syracuseStep 1996523 = 2994785) B2994785
theorem B3372779 : Blo 1330984 3372779 := bstep (se 1 (by rfl) ⟨2529584, by rfl⟩ : syracuseStep 3372779 = 5059169) B5059169
theorem B10254109 : Blo 1330984 10254109 := bstep (se 3 (by rfl) ⟨1922645, by rfl⟩ : syracuseStep 10254109 = 3845291) B3845291
theorem B2996009 : Blo 1330984 2996009 := bstep (se 2 (by rfl) ⟨1123503, by rfl⟩ : syracuseStep 2996009 = 2247007) B2247007
theorem B1996751 : Blo 1330984 1996751 := bstep (se 1 (by rfl) ⟨1497563, by rfl⟩ : syracuseStep 1996751 = 2995127) B2995127
theorem B38377475 : Blo 1330984 38377475 := bstep (se 1 (by rfl) ⟨28783106, by rfl⟩ : syracuseStep 38377475 = 57566213) B57566213
theorem B6404129 : Blo 1330984 6404129 := bstep (se 2 (by rfl) ⟨2401548, by rfl⟩ : syracuseStep 6404129 = 4803097) B4803097
theorem B14391431 : Blo 1330984 14391431 := bstep (se 1 (by rfl) ⟨10793573, by rfl⟩ : syracuseStep 14391431 = 21587147) B21587147
theorem B3201353 : Blo 1330984 3201353 := bstep (se 2 (by rfl) ⟨1200507, by rfl⟩ : syracuseStep 3201353 = 2401015) B2401015
theorem B1997147 : Blo 1330984 1997147 := bstep (se 1 (by rfl) ⟨1497860, by rfl⟩ : syracuseStep 1997147 = 2995721) B2995721
theorem B1497595 : Blo 1330984 1497595 := bstep (se 1 (by rfl) ⟨1123196, by rfl⟩ : syracuseStep 1497595 = 2246393) B2246393
theorem B1997375 : Blo 1330984 1997375 := bstep (se 1 (by rfl) ⟨1498031, by rfl⟩ : syracuseStep 1997375 = 2996063) B2996063
theorem B157866565 : Blo 1330984 157866565 := bstep (se 4 (by rfl) ⟨14799990, by rfl⟩ : syracuseStep 157866565 = 29599981) B29599981
theorem B5691977 : Blo 1330984 5691977 := bstep (se 2 (by rfl) ⟨2134491, by rfl⟩ : syracuseStep 5691977 = 4268983) B4268983
theorem B6486635 : Blo 1330984 6486635 := bstep (se 1 (by rfl) ⟨4864976, by rfl⟩ : syracuseStep 6486635 = 9729953) B9729953
theorem B3037817 : Blo 1330984 3037817 := bstep (se 2 (by rfl) ⟨1139181, by rfl⟩ : syracuseStep 3037817 = 2278363) B2278363
theorem B1497775 : Blo 1330984 1497775 := bstep (se 1 (by rfl) ⟨1123331, by rfl⟩ : syracuseStep 1497775 = 2246663) B2246663
theorem B1997495 : Blo 1330984 1997495 := bstep (se 1 (by rfl) ⟨1498121, by rfl⟩ : syracuseStep 1997495 = 2996243) B2996243
theorem B3373751 : Blo 1330984 3373751 := bstep (se 1 (by rfl) ⟨2530313, by rfl⟩ : syracuseStep 3373751 = 5060627) B5060627
theorem B4496147 : Blo 1330984 4496147 := bstep (se 1 (by rfl) ⟨3372110, by rfl⟩ : syracuseStep 4496147 = 6744221) B6744221
theorem B2997071 : Blo 1330984 2997071 := bstep (se 1 (by rfl) ⟨2247803, by rfl⟩ : syracuseStep 2997071 = 4495607) B4495607
theorem B3201871 : Blo 1330984 3201871 := bstep (se 1 (by rfl) ⟨2401403, by rfl⟩ : syracuseStep 3201871 = 4802807) B4802807
theorem B1997723 : Blo 1330984 1997723 := bstep (se 1 (by rfl) ⟨1498292, by rfl⟩ : syracuseStep 1997723 = 2996585) B2996585
theorem B1498063 : Blo 1330984 1498063 := bstep (se 1 (by rfl) ⟨1123547, by rfl⟩ : syracuseStep 1498063 = 2247095) B2247095
theorem B2997287 : Blo 1330984 2997287 := bstep (se 1 (by rfl) ⟨2247965, by rfl⟩ : syracuseStep 2997287 = 4495931) B4495931
theorem B7199867 : Blo 1330984 7199867 := bstep (se 1 (by rfl) ⟨5399900, by rfl⟩ : syracuseStep 7199867 = 10799801) B10799801
theorem B3202247 : Blo 1330984 3202247 := bstep (se 1 (by rfl) ⟨2401685, by rfl⟩ : syracuseStep 3202247 = 4803371) B4803371
theorem B2997467 : Blo 1330984 2997467 := bstep (se 1 (by rfl) ⟨2248100, by rfl⟩ : syracuseStep 2997467 = 4496201) B4496201
theorem B1998119 : Blo 1330984 1998119 := bstep (se 1 (by rfl) ⟨1498589, by rfl⟩ : syracuseStep 1998119 = 2997179) B2997179
theorem B1498459 : Blo 1330984 1498459 := bstep (se 1 (by rfl) ⟨1123844, by rfl⟩ : syracuseStep 1498459 = 2247689) B2247689
theorem B6405473 : Blo 1330984 6405473 := bstep (se 2 (by rfl) ⟨2402052, by rfl⟩ : syracuseStep 6405473 = 4804105) B4804105
theorem B1998203 : Blo 1330984 1998203 := bstep (se 1 (by rfl) ⟨1498652, by rfl⟩ : syracuseStep 1998203 = 2997305) B2997305
theorem B2997665 : Blo 1330984 2997665 := bstep (se 2 (by rfl) ⟨1124124, by rfl⟩ : syracuseStep 2997665 = 2248249) B2248249
theorem B1498567 : Blo 1330984 1498567 := bstep (se 1 (by rfl) ⟨1123925, by rfl⟩ : syracuseStep 1498567 = 2247851) B2247851
theorem B1998329 : Blo 1330984 1998329 := bstep (se 2 (by rfl) ⟨749373, by rfl⟩ : syracuseStep 1998329 = 1498747) B1498747
theorem B5398097 : Blo 1330984 5398097 := bstep (se 2 (by rfl) ⟨2024286, by rfl⟩ : syracuseStep 5398097 = 4048573) B4048573
theorem B5054035 : Blo 1330984 5054035 := bstep (se 1 (by rfl) ⟨3790526, by rfl⟩ : syracuseStep 5054035 = 7581053) B7581053
theorem B1998431 : Blo 1330984 1998431 := bstep (se 1 (by rfl) ⟨1498823, by rfl⟩ : syracuseStep 1998431 = 2997647) B2997647
theorem B4497011 : Blo 1330984 4497011 := bstep (se 1 (by rfl) ⟨3372758, by rfl⟩ : syracuseStep 4497011 = 6745517) B6745517
theorem B17079923 : Blo 1330984 17079923 := bstep (se 1 (by rfl) ⟨12809942, by rfl⟩ : syracuseStep 17079923 = 25619885) B25619885
theorem B2563745 : Blo 1330984 2563745 := bstep (se 2 (by rfl) ⟨961404, by rfl⟩ : syracuseStep 2563745 = 1922809) B1922809
theorem B1498927 : Blo 1330984 1498927 := bstep (se 1 (by rfl) ⟨1124195, by rfl⟩ : syracuseStep 1498927 = 2248391) B2248391
theorem B1998647 : Blo 1330984 1998647 := bstep (se 1 (by rfl) ⟨1498985, by rfl⟩ : syracuseStep 1998647 = 2997971) B2997971
theorem B2563897 : Blo 1330984 2563897 := bstep (se 2 (by rfl) ⟨961461, by rfl⟩ : syracuseStep 2563897 = 1922923) B1922923
theorem B7585609 : Blo 1330984 7585609 := bstep (se 2 (by rfl) ⟨2844603, by rfl⟩ : syracuseStep 7585609 = 5689207) B5689207
theorem B4497281 : Blo 1330984 4497281 := bstep (se 2 (by rfl) ⟨1686480, by rfl⟩ : syracuseStep 4497281 = 3372961) B3372961
theorem B1499035 : Blo 1330984 1499035 := bstep (se 1 (by rfl) ⟨1124276, by rfl⟩ : syracuseStep 1499035 = 2248553) B2248553
theorem B10796975 : Blo 1330984 10796975 := bstep (se 1 (by rfl) ⟨8097731, by rfl⟩ : syracuseStep 10796975 = 16195463) B16195463
theorem B2162639 : Blo 1330984 2162639 := bstep (se 1 (by rfl) ⟨1621979, by rfl⟩ : syracuseStep 2162639 = 3243959) B3243959
theorem B2998223 : Blo 1330984 2998223 := bstep (se 1 (by rfl) ⟨2248667, by rfl⟩ : syracuseStep 2998223 = 4497335) B4497335
theorem B1999067 : Blo 1330984 1999067 := bstep (se 1 (by rfl) ⟨1499300, by rfl⟩ : syracuseStep 1999067 = 2998601) B2998601
theorem B1999079 : Blo 1330984 1999079 := bstep (se 1 (by rfl) ⟨1499309, by rfl⟩ : syracuseStep 1999079 = 2998619) B2998619
theorem B10805507 : Blo 1330984 10805507 := bstep (se 1 (by rfl) ⟨8104130, by rfl⟩ : syracuseStep 10805507 = 16208261) B16208261
theorem B1999241 : Blo 1330984 1999241 := bstep (se 2 (by rfl) ⟨749715, by rfl⟩ : syracuseStep 1999241 = 1499431) B1499431
theorem B2998727 : Blo 1330984 2998727 := bstep (se 1 (by rfl) ⟨2249045, by rfl⟩ : syracuseStep 2998727 = 4498091) B4498091
theorem B1999337 : Blo 1330984 1999337 := bstep (se 2 (by rfl) ⟨749751, by rfl⟩ : syracuseStep 1999337 = 1499503) B1499503
theorem B4497983 : Blo 1330984 4497983 := bstep (se 1 (by rfl) ⟨3373487, by rfl⟩ : syracuseStep 4497983 = 6746975) B6746975
theorem B6742601 : Blo 1330984 6742601 := bstep (se 2 (by rfl) ⟨2528475, by rfl⟩ : syracuseStep 6742601 = 5056951) B5056951
theorem B1999463 : Blo 1330984 1999463 := bstep (se 1 (by rfl) ⟨1499597, by rfl⟩ : syracuseStep 1999463 = 2999195) B2999195
theorem B14402285 : Blo 1330984 14402285 := bstep (se 3 (by rfl) ⟨2700428, by rfl⟩ : syracuseStep 14402285 = 5400857) B5400857
theorem B2999087 : Blo 1330984 2999087 := bstep (se 1 (by rfl) ⟨2249315, by rfl⟩ : syracuseStep 2999087 = 4498631) B4498631
theorem B3793807 : Blo 1330984 3793807 := bstep (se 1 (by rfl) ⟨2845355, by rfl⟩ : syracuseStep 3793807 = 5690711) B5690711
theorem B4269161 : Blo 1330984 4269161 := bstep (se 2 (by rfl) ⟨1600935, by rfl⟩ : syracuseStep 4269161 = 3201871) B3201871
theorem B2134831 : Blo 1330984 2134831 := bstep (se 1 (by rfl) ⟨1601123, by rfl⟩ : syracuseStep 2134831 = 3202247) B3202247
theorem B27346187 : Blo 1330984 27346187 := bstep (se 1 (by rfl) ⟨20509640, by rfl⟩ : syracuseStep 27346187 = 41019281) B41019281
theorem B25584983 : Blo 1330984 25584983 := bstep (se 1 (by rfl) ⟨19188737, by rfl⟩ : syracuseStep 25584983 = 38377475) B38377475
theorem B4269419 : Blo 1330984 4269419 := bstep (se 1 (by rfl) ⟨3202064, by rfl⟩ : syracuseStep 4269419 = 6404129) B6404129
theorem B9594287 : Blo 1330984 9594287 := bstep (se 1 (by rfl) ⟨7195715, by rfl⟩ : syracuseStep 9594287 = 14391431) B14391431
theorem B14394925 : Blo 1330984 14394925 := bstep (se 3 (by rfl) ⟨2699048, by rfl⟩ : syracuseStep 14394925 = 5398097) B5398097
theorem B3794651 : Blo 1330984 3794651 := bstep (se 1 (by rfl) ⟨2845988, by rfl⟩ : syracuseStep 3794651 = 5691977) B5691977
theorem B4867807 : Blo 1330984 4867807 := bstep (se 1 (by rfl) ⟨3650855, by rfl⟩ : syracuseStep 4867807 = 7301711) B7301711
theorem B2025211 : Blo 1330984 2025211 := bstep (se 1 (by rfl) ⟨1518908, by rfl⟩ : syracuseStep 2025211 = 3037817) B3037817
theorem B15173405 : Blo 1330984 15173405 := bstep (se 3 (by rfl) ⟨2845013, by rfl⟩ : syracuseStep 15173405 = 5690027) B5690027
theorem B4802345 : Blo 1330984 4802345 := bstep (se 2 (by rfl) ⟨1800879, by rfl⟩ : syracuseStep 4802345 = 3601759) B3601759
theorem B2279567 : Blo 1330984 2279567 := bstep (se 1 (by rfl) ⟨1709675, by rfl⟩ : syracuseStep 2279567 = 3419351) B3419351
theorem B4270315 : Blo 1330984 4270315 := bstep (se 1 (by rfl) ⟨3202736, by rfl⟩ : syracuseStep 4270315 = 6405473) B6405473
theorem B2246953 : Blo 1330984 2246953 := bstep (se 2 (by rfl) ⟨842607, by rfl⟩ : syracuseStep 2246953 = 1685215) B1685215
theorem B3369377 : Blo 1330984 3369377 := bstep (se 2 (by rfl) ⟨1263516, by rfl⟩ : syracuseStep 3369377 = 2527033) B2527033
theorem B3418529 : Blo 1330984 3418529 := bstep (se 2 (by rfl) ⟨1281948, by rfl⟩ : syracuseStep 3418529 = 2563897) B2563897
theorem B20515607 : Blo 1330984 20515607 := bstep (se 1 (by rfl) ⟨15386705, by rfl⟩ : syracuseStep 20515607 = 30773411) B30773411
theorem B3795767 : Blo 1330984 3795767 := bstep (se 1 (by rfl) ⟨2846825, by rfl⟩ : syracuseStep 3795767 = 5693651) B5693651
theorem B4050119 : Blo 1330984 4050119 := bstep (se 1 (by rfl) ⟨3037589, by rfl⟩ : syracuseStep 4050119 = 6075179) B6075179
theorem B3370207 : Blo 1330984 3370207 := bstep (se 1 (by rfl) ⟨2527655, by rfl⟩ : syracuseStep 3370207 = 5055311) B5055311
theorem B3370319 : Blo 1330984 3370319 := bstep (se 1 (by rfl) ⟨2527739, by rfl⟩ : syracuseStep 3370319 = 5055479) B5055479
theorem B2133415 : Blo 1330984 2133415 := bstep (se 1 (by rfl) ⟨1600061, by rfl⟩ : syracuseStep 2133415 = 3200123) B3200123
theorem B210488753 : Blo 1330984 210488753 := bstep (se 2 (by rfl) ⟨78933282, by rfl⟩ : syracuseStep 210488753 = 157866565) B157866565
theorem B2133479 : Blo 1330984 2133479 := bstep (se 1 (by rfl) ⟨1600109, by rfl⟩ : syracuseStep 2133479 = 3200219) B3200219
theorem B2248283 : Blo 1330984 2248283 := bstep (se 1 (by rfl) ⟨1686212, by rfl⟩ : syracuseStep 2248283 = 3372425) B3372425
theorem B4492907 : Blo 1330984 4492907 := bstep (se 1 (by rfl) ⟨3369680, by rfl⟩ : syracuseStep 4492907 = 6739361) B6739361
theorem B7589483 : Blo 1330984 7589483 := bstep (se 1 (by rfl) ⟨5692112, by rfl⟩ : syracuseStep 7589483 = 11384225) B11384225
theorem B1331015 : Blo 1330984 1331015 := bstep (se 1 (by rfl) ⟨998261, by rfl⟩ : syracuseStep 1331015 = 1996523) B1996523
theorem B2248519 : Blo 1330984 2248519 := bstep (se 1 (by rfl) ⟨1686389, by rfl⟩ : syracuseStep 2248519 = 3372779) B3372779
theorem B4493177 : Blo 1330984 4493177 := bstep (se 2 (by rfl) ⟨1684941, by rfl⟩ : syracuseStep 4493177 = 3369883) B3369883
theorem B1331167 : Blo 1330984 1331167 := bstep (se 1 (by rfl) ⟨998375, by rfl⟩ : syracuseStep 1331167 = 1996751) B1996751
theorem B5058683 : Blo 1330984 5058683 := bstep (se 1 (by rfl) ⟨3794012, by rfl⟩ : syracuseStep 5058683 = 7588025) B7588025
theorem B4493501 : Blo 1330984 4493501 := bstep (se 3 (by rfl) ⟨842531, by rfl⟩ : syracuseStep 4493501 = 1685063) B1685063
theorem B2134235 : Blo 1330984 2134235 := bstep (se 1 (by rfl) ⟨1600676, by rfl⟩ : syracuseStep 2134235 = 3201353) B3201353
theorem B1331431 : Blo 1330984 1331431 := bstep (se 1 (by rfl) ⟨998573, by rfl⟩ : syracuseStep 1331431 = 1997147) B1997147
theorem B1331583 : Blo 1330984 1331583 := bstep (se 1 (by rfl) ⟨998687, by rfl⟩ : syracuseStep 1331583 = 1997375) B1997375
theorem B2527625 : Blo 1330984 2527625 := bstep (se 2 (by rfl) ⟨947859, by rfl⟩ : syracuseStep 2527625 = 1895719) B1895719
theorem B6836653 : Blo 1330984 6836653 := bstep (se 3 (by rfl) ⟨1281872, by rfl⟩ : syracuseStep 6836653 = 2563745) B2563745
theorem B1331663 : Blo 1330984 1331663 := bstep (se 1 (by rfl) ⟨998747, by rfl⟩ : syracuseStep 1331663 = 1997495) B1997495
theorem B2249167 : Blo 1330984 2249167 := bstep (se 1 (by rfl) ⟨1686875, by rfl⟩ : syracuseStep 2249167 = 3373751) B3373751
theorem B3371615 : Blo 1330984 3371615 := bstep (se 1 (by rfl) ⟨2528711, by rfl⟩ : syracuseStep 3371615 = 5057423) B5057423
theorem B1331815 : Blo 1330984 1331815 := bstep (se 1 (by rfl) ⟨998861, by rfl⟩ : syracuseStep 1331815 = 1997723) B1997723
theorem B10793735 : Blo 1330984 10793735 := bstep (se 1 (by rfl) ⟨8095301, by rfl⟩ : syracuseStep 10793735 = 16190603) B16190603
theorem B6738713 : Blo 1330984 6738713 := bstep (se 2 (by rfl) ⟨2527017, by rfl⟩ : syracuseStep 6738713 = 5054035) B5054035
theorem B1332079 : Blo 1330984 1332079 := bstep (se 1 (by rfl) ⟨999059, by rfl⟩ : syracuseStep 1332079 = 1998119) B1998119
theorem B1332135 : Blo 1330984 1332135 := bstep (se 1 (by rfl) ⟨999101, by rfl⟩ : syracuseStep 1332135 = 1998203) B1998203
theorem B1332219 : Blo 1330984 1332219 := bstep (se 1 (by rfl) ⟨999164, by rfl⟩ : syracuseStep 1332219 = 1998329) B1998329
theorem B1332287 : Blo 1330984 1332287 := bstep (se 1 (by rfl) ⟨999215, by rfl⟩ : syracuseStep 1332287 = 1998431) B1998431
theorem B10114145 : Blo 1330984 10114145 := bstep (se 2 (by rfl) ⟨3792804, by rfl⟩ : syracuseStep 10114145 = 7585609) B7585609
theorem B2995307 : Blo 1330984 2995307 := bstep (se 1 (by rfl) ⟨2246480, by rfl⟩ : syracuseStep 2995307 = 4492961) B4492961
theorem B1799275 : Blo 1330984 1799275 := bstep (se 1 (by rfl) ⟨1349456, by rfl⟩ : syracuseStep 1799275 = 2698913) B2698913
theorem B1332431 : Blo 1330984 1332431 := bstep (se 1 (by rfl) ⟨999323, by rfl⟩ : syracuseStep 1332431 = 1998647) B1998647
theorem B7197983 : Blo 1330984 7197983 := bstep (se 1 (by rfl) ⟨5398487, by rfl⟩ : syracuseStep 7197983 = 10796975) B10796975
theorem B7591259 : Blo 1330984 7591259 := bstep (se 1 (by rfl) ⟨5693444, by rfl⟩ : syracuseStep 7591259 = 11386889) B11386889
theorem B48592223 : Blo 1330984 48592223 := bstep (se 1 (by rfl) ⟨36444167, by rfl⟩ : syracuseStep 48592223 = 72888335) B72888335
theorem B4494689 : Blo 1330984 4494689 := bstep (se 2 (by rfl) ⟨1685508, by rfl⟩ : syracuseStep 4494689 = 3371017) B3371017
theorem B1684891 : Blo 1330984 1684891 := bstep (se 1 (by rfl) ⟨1263668, by rfl⟩ : syracuseStep 1684891 = 2527337) B2527337
theorem B3200411 : Blo 1330984 3200411 := bstep (se 1 (by rfl) ⟨2400308, by rfl⟩ : syracuseStep 3200411 = 4800617) B4800617
theorem B1332635 : Blo 1330984 1332635 := bstep (se 1 (by rfl) ⟨999476, by rfl⟩ : syracuseStep 1332635 = 1998953) B1998953
theorem B3036641 : Blo 1330984 3036641 := bstep (se 2 (by rfl) ⟨1138740, by rfl⟩ : syracuseStep 3036641 = 2277481) B2277481
theorem B6755809 : Blo 1330984 6755809 := bstep (se 2 (by rfl) ⟨2533428, by rfl⟩ : syracuseStep 6755809 = 5066857) B5066857
theorem B15169031 : Blo 1330984 15169031 := bstep (se 1 (by rfl) ⟨11376773, by rfl⟩ : syracuseStep 15169031 = 22753547) B22753547
theorem B1332847 : Blo 1330984 1332847 := bstep (se 1 (by rfl) ⟨999635, by rfl⟩ : syracuseStep 1332847 = 1999271) B1999271
theorem B1332903 : Blo 1330984 1332903 := bstep (se 1 (by rfl) ⟨999677, by rfl⟩ : syracuseStep 1332903 = 1999355) B1999355
theorem B2995883 : Blo 1330984 2995883 := bstep (se 1 (by rfl) ⟨2246912, by rfl⟩ : syracuseStep 2995883 = 4493825) B4493825
theorem B4052663 : Blo 1330984 4052663 := bstep (se 1 (by rfl) ⟨3039497, by rfl⟩ : syracuseStep 4052663 = 6078995) B6078995
theorem B1996511 : Blo 1330984 1996511 := bstep (se 1 (by rfl) ⟨1497383, by rfl⟩ : syracuseStep 1996511 = 2994767) B2994767
theorem B1996607 : Blo 1330984 1996607 := bstep (se 1 (by rfl) ⟨1497455, by rfl⟩ : syracuseStep 1996607 = 2994911) B2994911
theorem B1996775 : Blo 1330984 1996775 := bstep (se 1 (by rfl) ⟨1497581, by rfl⟩ : syracuseStep 1996775 = 2995163) B2995163
theorem B2996207 : Blo 1330984 2996207 := bstep (se 1 (by rfl) ⟨2247155, by rfl⟩ : syracuseStep 2996207 = 4494311) B4494311
theorem B1996793 : Blo 1330984 1996793 := bstep (se 2 (by rfl) ⟨748797, by rfl⟩ : syracuseStep 1996793 = 1497595) B1497595
theorem B1996895 : Blo 1330984 1996895 := bstep (se 1 (by rfl) ⟨1497671, by rfl⟩ : syracuseStep 1996895 = 2995343) B2995343
theorem B1996955 : Blo 1330984 1996955 := bstep (se 1 (by rfl) ⟨1497716, by rfl⟩ : syracuseStep 1996955 = 2995433) B2995433
theorem B1996991 : Blo 1330984 1996991 := bstep (se 1 (by rfl) ⟨1497743, by rfl⟩ : syracuseStep 1996991 = 2995487) B2995487
theorem B2996423 : Blo 1330984 2996423 := bstep (se 1 (by rfl) ⟨2247317, by rfl⟩ : syracuseStep 2996423 = 4494635) B4494635
theorem B6740171 : Blo 1330984 6740171 := bstep (se 1 (by rfl) ⟨5055128, by rfl⟩ : syracuseStep 6740171 = 10110257) B10110257
theorem B1997033 : Blo 1330984 1997033 := bstep (se 2 (by rfl) ⟨748887, by rfl⟩ : syracuseStep 1997033 = 1497775) B1497775
theorem B12802333 : Blo 1330984 12802333 := bstep (se 3 (by rfl) ⟨2400437, by rfl⟩ : syracuseStep 12802333 = 4800875) B4800875
theorem B2996603 : Blo 1330984 2996603 := bstep (se 1 (by rfl) ⟨2247452, by rfl⟩ : syracuseStep 2996603 = 4494905) B4494905
theorem B3791279 : Blo 1330984 3791279 := bstep (se 1 (by rfl) ⟨2843459, by rfl⟩ : syracuseStep 3791279 = 5686919) B5686919
theorem B1997339 : Blo 1330984 1997339 := bstep (se 1 (by rfl) ⟨1498004, by rfl⟩ : syracuseStep 1997339 = 2996009) B2996009
theorem B2398751 : Blo 1330984 2398751 := bstep (se 1 (by rfl) ⟨1799063, by rfl⟩ : syracuseStep 2398751 = 3598127) B3598127
theorem B1497631 : Blo 1330984 1497631 := bstep (se 1 (by rfl) ⟨1123223, by rfl⟩ : syracuseStep 1497631 = 2246447) B2246447
theorem B1997417 : Blo 1330984 1997417 := bstep (se 2 (by rfl) ⟨749031, by rfl⟩ : syracuseStep 1997417 = 1498063) B1498063
theorem B2996873 : Blo 1330984 2996873 := bstep (se 2 (by rfl) ⟨1123827, by rfl⟩ : syracuseStep 2996873 = 2247655) B2247655
theorem B9116297 : Blo 1330984 9116297 := bstep (se 2 (by rfl) ⟨3418611, by rfl⟩ : syracuseStep 9116297 = 6837223) B6837223
theorem B6740819 : Blo 1330984 6740819 := bstep (se 1 (by rfl) ⟨5055614, by rfl⟩ : syracuseStep 6740819 = 10111229) B10111229
theorem B2530207 : Blo 1330984 2530207 := bstep (se 1 (by rfl) ⟨1897655, by rfl⟩ : syracuseStep 2530207 = 3795311) B3795311
theorem B7584677 : Blo 1330984 7584677 := bstep (se 4 (by rfl) ⟨711063, by rfl⟩ : syracuseStep 7584677 = 1422127) B1422127
theorem B6831145 : Blo 1330984 6831145 := bstep (se 2 (by rfl) ⟨2561679, by rfl⟩ : syracuseStep 6831145 = 5123359) B5123359
theorem B4324423 : Blo 1330984 4324423 := bstep (se 1 (by rfl) ⟨3243317, by rfl⟩ : syracuseStep 4324423 = 6486635) B6486635
theorem B1997945 : Blo 1330984 1997945 := bstep (se 2 (by rfl) ⟨749229, by rfl⟩ : syracuseStep 1997945 = 1498459) B1498459
theorem B2997431 : Blo 1330984 2997431 := bstep (se 1 (by rfl) ⟨2248073, by rfl⟩ : syracuseStep 2997431 = 4496147) B4496147
theorem B1998047 : Blo 1330984 1998047 := bstep (se 1 (by rfl) ⟨1498535, by rfl⟩ : syracuseStep 1998047 = 2997071) B2997071
theorem B4496633 : Blo 1330984 4496633 := bstep (se 2 (by rfl) ⟨1686237, by rfl⟩ : syracuseStep 4496633 = 3372475) B3372475
theorem B1998089 : Blo 1330984 1998089 := bstep (se 2 (by rfl) ⟨749283, by rfl⟩ : syracuseStep 1998089 = 1498567) B1498567
theorem B3792167 : Blo 1330984 3792167 := bstep (se 1 (by rfl) ⟨2844125, by rfl⟩ : syracuseStep 3792167 = 5688251) B5688251
theorem B1998191 : Blo 1330984 1998191 := bstep (se 1 (by rfl) ⟨1498643, by rfl⟩ : syracuseStep 1998191 = 2997287) B2997287
theorem B4799911 : Blo 1330984 4799911 := bstep (se 1 (by rfl) ⟨3599933, by rfl⟩ : syracuseStep 4799911 = 7199867) B7199867
theorem B1998311 : Blo 1330984 1998311 := bstep (se 1 (by rfl) ⟨1498733, by rfl⟩ : syracuseStep 1998311 = 2997467) B2997467
theorem B4496903 : Blo 1330984 4496903 := bstep (se 1 (by rfl) ⟨3372677, by rfl⟩ : syracuseStep 4496903 = 6745355) B6745355
theorem B1998443 : Blo 1330984 1998443 := bstep (se 1 (by rfl) ⟨1498832, by rfl⟩ : syracuseStep 1998443 = 2997665) B2997665
theorem B13672145 : Blo 1330984 13672145 := bstep (se 2 (by rfl) ⟨5127054, by rfl⟩ : syracuseStep 13672145 = 10254109) B10254109
theorem B1998569 : Blo 1330984 1998569 := bstep (se 2 (by rfl) ⟨749463, by rfl⟩ : syracuseStep 1998569 = 1498927) B1498927
theorem B2998007 : Blo 1330984 2998007 := bstep (se 1 (by rfl) ⟨2248505, by rfl⟩ : syracuseStep 2998007 = 4497011) B4497011
theorem B11386615 : Blo 1330984 11386615 := bstep (se 1 (by rfl) ⟨8539961, by rfl⟩ : syracuseStep 11386615 = 17079923) B17079923
theorem B2400019 : Blo 1330984 2400019 := bstep (se 1 (by rfl) ⟨1800014, by rfl⟩ : syracuseStep 2400019 = 3600029) B3600029
theorem B1998713 : Blo 1330984 1998713 := bstep (se 2 (by rfl) ⟨749517, by rfl⟩ : syracuseStep 1998713 = 1499035) B1499035
theorem B5767037 : Blo 1330984 5767037 := bstep (se 3 (by rfl) ⟨1081319, by rfl⟩ : syracuseStep 5767037 = 2162639) B2162639
theorem B2998187 : Blo 1330984 2998187 := bstep (se 1 (by rfl) ⟨2248640, by rfl⟩ : syracuseStep 2998187 = 4497281) B4497281
theorem B1998815 : Blo 1330984 1998815 := bstep (se 1 (by rfl) ⟨1499111, by rfl⟩ : syracuseStep 1998815 = 2998223) B2998223
theorem B1999151 : Blo 1330984 1999151 := bstep (se 1 (by rfl) ⟨1499363, by rfl⟩ : syracuseStep 1999151 = 2998727) B2998727
theorem B5693753 : Blo 1330984 5693753 := bstep (se 2 (by rfl) ⟨2135157, by rfl⟩ : syracuseStep 5693753 = 4270315) B4270315
theorem B2998655 : Blo 1330984 2998655 := bstep (se 1 (by rfl) ⟨2248991, by rfl⟩ : syracuseStep 2998655 = 4497983) B4497983
theorem B9601523 : Blo 1330984 9601523 := bstep (se 1 (by rfl) ⟨7201142, by rfl⟩ : syracuseStep 9601523 = 14402285) B14402285
theorem B1999391 : Blo 1330984 1999391 := bstep (se 1 (by rfl) ⟨1499543, by rfl⟩ : syracuseStep 1999391 = 2999087) B2999087
theorem B2998889 : Blo 1330984 2998889 := bstep (se 2 (by rfl) ⟨1124583, by rfl⟩ : syracuseStep 2998889 = 2249167) B2249167
theorem B6742763 : Blo 1330984 6742763 := bstep (se 1 (by rfl) ⟨5057072, by rfl⟩ : syracuseStep 6742763 = 10114145) B10114145
theorem B17056655 : Blo 1330984 17056655 := bstep (se 1 (by rfl) ⟨12792491, by rfl⟩ : syracuseStep 17056655 = 25584983) B25584983
theorem B2246251 : Blo 1330984 2246251 := bstep (se 1 (by rfl) ⟨1684688, by rfl⟩ : syracuseStep 2246251 = 3369377) B3369377
theorem B1599167 : Blo 1330984 1599167 := bstep (se 1 (by rfl) ⟨1199375, by rfl⟩ : syracuseStep 1599167 = 2398751) B2398751
theorem B2246521 : Blo 1330984 2246521 := bstep (se 2 (by rfl) ⟨842445, by rfl⟩ : syracuseStep 2246521 = 1684891) B1684891
theorem B6399881 : Blo 1330984 6399881 := bstep (se 2 (by rfl) ⟨2399955, by rfl⟩ : syracuseStep 6399881 = 4799911) B4799911
theorem B2844553 : Blo 1330984 2844553 := bstep (se 2 (by rfl) ⟨1066707, by rfl⟩ : syracuseStep 2844553 = 2133415) B2133415
theorem B5056451 : Blo 1330984 5056451 := bstep (se 1 (by rfl) ⟨3792338, by rfl⟩ : syracuseStep 5056451 = 7584677) B7584677
theorem B2246879 : Blo 1330984 2246879 := bstep (se 1 (by rfl) ⟨1685159, by rfl⟩ : syracuseStep 2246879 = 3370319) B3370319
theorem B6490409 : Blo 1330984 6490409 := bstep (se 2 (by rfl) ⟨2433903, by rfl⟩ : syracuseStep 6490409 = 4867807) B4867807
theorem B15182153 : Blo 1330984 15182153 := bstep (se 2 (by rfl) ⟨5693307, by rfl⟩ : syracuseStep 15182153 = 11386615) B11386615
theorem B3844691 : Blo 1330984 3844691 := bstep (se 1 (by rfl) ⟨2883518, by rfl⟩ : syracuseStep 3844691 = 5767037) B5767037
theorem B7203671 : Blo 1330984 7203671 := bstep (se 1 (by rfl) ⟨5402753, by rfl⟩ : syracuseStep 7203671 = 10805507) B10805507
theorem B36432773 : Blo 1330984 36432773 := bstep (se 4 (by rfl) ⟨3415572, by rfl⟩ : syracuseStep 36432773 = 6831145) B6831145
theorem B2247743 : Blo 1330984 2247743 := bstep (se 1 (by rfl) ⟨1685807, by rfl⟩ : syracuseStep 2247743 = 3371615) B3371615
theorem B7195823 : Blo 1330984 7195823 := bstep (se 1 (by rfl) ⟨5396867, by rfl⟩ : syracuseStep 7195823 = 10793735) B10793735
theorem B4492475 : Blo 1330984 4492475 := bstep (se 1 (by rfl) ⟨3369356, by rfl⟩ : syracuseStep 4492475 = 6738713) B6738713
theorem B10800317 : Blo 1330984 10800317 := bstep (se 3 (by rfl) ⟨2025059, by rfl⟩ : syracuseStep 10800317 = 4050119) B4050119
theorem B2846107 : Blo 1330984 2846107 := bstep (se 1 (by rfl) ⟨2134580, by rfl⟩ : syracuseStep 2846107 = 4269161) B4269161
theorem B18230791 : Blo 1330984 18230791 := bstep (se 1 (by rfl) ⟨13673093, by rfl⟩ : syracuseStep 18230791 = 27346187) B27346187
theorem B32394815 : Blo 1330984 32394815 := bstep (se 1 (by rfl) ⟨24296111, by rfl⟩ : syracuseStep 32394815 = 48592223) B48592223
theorem B2846279 : Blo 1330984 2846279 := bstep (se 1 (by rfl) ⟨2134709, by rfl⟩ : syracuseStep 2846279 = 4269419) B4269419
theorem B2133607 : Blo 1330984 2133607 := bstep (se 1 (by rfl) ⟨1600205, by rfl⟩ : syracuseStep 2133607 = 3200411) B3200411
theorem B10112687 : Blo 1330984 10112687 := bstep (se 1 (by rfl) ⟨7584515, by rfl⟩ : syracuseStep 10112687 = 15169031) B15169031
theorem B2846441 : Blo 1330984 2846441 := bstep (se 2 (by rfl) ⟨1067415, by rfl⟩ : syracuseStep 2846441 = 2134831) B2134831
theorem B561303341 : Blo 1330984 561303341 := bstep (se 3 (by rfl) ⟨105244376, by rfl⟩ : syracuseStep 561303341 = 210488753) B210488753
theorem B1331007 : Blo 1330984 1331007 := bstep (se 1 (by rfl) ⟨998255, by rfl⟩ : syracuseStep 1331007 = 1996511) B1996511
theorem B5058409 : Blo 1330984 5058409 := bstep (se 2 (by rfl) ⟨1896903, by rfl⟩ : syracuseStep 5058409 = 3793807) B3793807
theorem B1331071 : Blo 1330984 1331071 := bstep (se 1 (by rfl) ⟨998303, by rfl⟩ : syracuseStep 1331071 = 1996607) B1996607
theorem B5689277 : Blo 1330984 5689277 := bstep (se 3 (by rfl) ⟨1066739, by rfl⟩ : syracuseStep 5689277 = 2133479) B2133479
theorem B1331183 : Blo 1330984 1331183 := bstep (se 1 (by rfl) ⟨998387, by rfl⟩ : syracuseStep 1331183 = 1996775) B1996775
theorem B1331195 : Blo 1330984 1331195 := bstep (se 1 (by rfl) ⟨998396, by rfl⟩ : syracuseStep 1331195 = 1996793) B1996793
theorem B1331263 : Blo 1330984 1331263 := bstep (se 1 (by rfl) ⟨998447, by rfl⟩ : syracuseStep 1331263 = 1996895) B1996895
theorem B1519711 : Blo 1330984 1519711 := bstep (se 1 (by rfl) ⟨1139783, by rfl⟩ : syracuseStep 1519711 = 2279567) B2279567
theorem B12800101 : Blo 1330984 12800101 := bstep (se 4 (by rfl) ⟨1200009, by rfl⟩ : syracuseStep 12800101 = 2400019) B2400019
theorem B1331303 : Blo 1330984 1331303 := bstep (se 1 (by rfl) ⟨998477, by rfl⟩ : syracuseStep 1331303 = 1996955) B1996955
theorem B1331327 : Blo 1330984 1331327 := bstep (se 1 (by rfl) ⟨998495, by rfl⟩ : syracuseStep 1331327 = 1996991) B1996991
theorem B4493447 : Blo 1330984 4493447 := bstep (se 1 (by rfl) ⟨3370085, by rfl⟩ : syracuseStep 4493447 = 6740171) B6740171
theorem B1331355 : Blo 1330984 1331355 := bstep (se 1 (by rfl) ⟨998516, by rfl⟩ : syracuseStep 1331355 = 1997033) B1997033
theorem B2527519 : Blo 1330984 2527519 := bstep (se 1 (by rfl) ⟨1895639, by rfl⟩ : syracuseStep 2527519 = 3791279) B3791279
theorem B4493609 : Blo 1330984 4493609 := bstep (se 2 (by rfl) ⟨1685103, by rfl⟩ : syracuseStep 4493609 = 3370207) B3370207
theorem B1331559 : Blo 1330984 1331559 := bstep (se 1 (by rfl) ⟨998669, by rfl⟩ : syracuseStep 1331559 = 1997339) B1997339
theorem B1331611 : Blo 1330984 1331611 := bstep (se 1 (by rfl) ⟨998708, by rfl⟩ : syracuseStep 1331611 = 1997417) B1997417
theorem B13677071 : Blo 1330984 13677071 := bstep (se 1 (by rfl) ⟨10257803, by rfl⟩ : syracuseStep 13677071 = 20515607) B20515607
theorem B4493879 : Blo 1330984 4493879 := bstep (se 1 (by rfl) ⟨3370409, by rfl⟩ : syracuseStep 4493879 = 6740819) B6740819
theorem B9007745 : Blo 1330984 9007745 := bstep (se 2 (by rfl) ⟨3377904, by rfl⟩ : syracuseStep 9007745 = 6755809) B6755809
theorem B1331963 : Blo 1330984 1331963 := bstep (se 1 (by rfl) ⟨998972, by rfl⟩ : syracuseStep 1331963 = 1997945) B1997945
theorem B1332031 : Blo 1330984 1332031 := bstep (se 1 (by rfl) ⟨999023, by rfl⟩ : syracuseStep 1332031 = 1998047) B1998047
theorem B1332059 : Blo 1330984 1332059 := bstep (se 1 (by rfl) ⟨999044, by rfl⟩ : syracuseStep 1332059 = 1998089) B1998089
theorem B2528111 : Blo 1330984 2528111 := bstep (se 1 (by rfl) ⟨1896083, by rfl⟩ : syracuseStep 2528111 = 3792167) B3792167
theorem B1332127 : Blo 1330984 1332127 := bstep (se 1 (by rfl) ⟨999095, by rfl⟩ : syracuseStep 1332127 = 1998191) B1998191
theorem B1332207 : Blo 1330984 1332207 := bstep (se 1 (by rfl) ⟨999155, by rfl⟩ : syracuseStep 1332207 = 1998311) B1998311
theorem B2700281 : Blo 1330984 2700281 := bstep (se 2 (by rfl) ⟨1012605, by rfl⟩ : syracuseStep 2700281 = 2025211) B2025211
theorem B2995271 : Blo 1330984 2995271 := bstep (se 1 (by rfl) ⟨2246453, by rfl⟩ : syracuseStep 2995271 = 4492907) B4492907
theorem B1332295 : Blo 1330984 1332295 := bstep (se 1 (by rfl) ⟨999221, by rfl⟩ : syracuseStep 1332295 = 1998443) B1998443
theorem B5059655 : Blo 1330984 5059655 := bstep (se 1 (by rfl) ⟨3794741, by rfl⟩ : syracuseStep 5059655 = 7589483) B7589483
theorem B9114763 : Blo 1330984 9114763 := bstep (se 1 (by rfl) ⟨6836072, by rfl⟩ : syracuseStep 9114763 = 13672145) B13672145
theorem B1332379 : Blo 1330984 1332379 := bstep (se 1 (by rfl) ⟨999284, by rfl⟩ : syracuseStep 1332379 = 1998569) B1998569
theorem B2995451 : Blo 1330984 2995451 := bstep (se 1 (by rfl) ⟨2246588, by rfl⟩ : syracuseStep 2995451 = 4493177) B4493177
theorem B1332475 : Blo 1330984 1332475 := bstep (se 1 (by rfl) ⟨999356, by rfl⟩ : syracuseStep 1332475 = 1998713) B1998713
theorem B1332543 : Blo 1330984 1332543 := bstep (se 1 (by rfl) ⟨999407, by rfl⟩ : syracuseStep 1332543 = 1998815) B1998815
theorem B3372455 : Blo 1330984 3372455 := bstep (se 1 (by rfl) ⟨2529341, by rfl⟩ : syracuseStep 3372455 = 5058683) B5058683
theorem B2995667 : Blo 1330984 2995667 := bstep (se 1 (by rfl) ⟨2246750, by rfl⟩ : syracuseStep 2995667 = 4493501) B4493501
theorem B1332711 : Blo 1330984 1332711 := bstep (se 1 (by rfl) ⟨999533, by rfl⟩ : syracuseStep 1332711 = 1999067) B1999067
theorem B1332719 : Blo 1330984 1332719 := bstep (se 1 (by rfl) ⟨999539, by rfl⟩ : syracuseStep 1332719 = 1999079) B1999079
theorem B1332827 : Blo 1330984 1332827 := bstep (se 1 (by rfl) ⟨999620, by rfl⟩ : syracuseStep 1332827 = 1999241) B1999241
theorem B1332891 : Blo 1330984 1332891 := bstep (se 1 (by rfl) ⟨999668, by rfl⟩ : syracuseStep 1332891 = 1999337) B1999337
theorem B17069777 : Blo 1330984 17069777 := bstep (se 2 (by rfl) ⟨6401166, by rfl⟩ : syracuseStep 17069777 = 12802333) B12802333
theorem B4495067 : Blo 1330984 4495067 := bstep (se 1 (by rfl) ⟨3371300, by rfl⟩ : syracuseStep 4495067 = 6742601) B6742601
theorem B2995937 : Blo 1330984 2995937 := bstep (se 2 (by rfl) ⟨1123476, by rfl⟩ : syracuseStep 2995937 = 2246953) B2246953
theorem B1332975 : Blo 1330984 1332975 := bstep (se 1 (by rfl) ⟨999731, by rfl⟩ : syracuseStep 1332975 = 1999463) B1999463
theorem B9115537 : Blo 1330984 9115537 := bstep (se 2 (by rfl) ⟨3418326, by rfl⟩ : syracuseStep 9115537 = 6836653) B6836653
theorem B5691293 : Blo 1330984 5691293 := bstep (se 3 (by rfl) ⟨1067117, by rfl⟩ : syracuseStep 5691293 = 2134235) B2134235
theorem B1996841 : Blo 1330984 1996841 := bstep (se 2 (by rfl) ⟨748815, by rfl⟩ : syracuseStep 1996841 = 1497631) B1497631
theorem B1996871 : Blo 1330984 1996871 := bstep (se 1 (by rfl) ⟨1497653, by rfl⟩ : syracuseStep 1996871 = 2995307) B2995307
theorem B4798655 : Blo 1330984 4798655 := bstep (se 1 (by rfl) ⟨3598991, by rfl⟩ : syracuseStep 4798655 = 7197983) B7197983
theorem B5060839 : Blo 1330984 5060839 := bstep (se 1 (by rfl) ⟨3795629, by rfl⟩ : syracuseStep 5060839 = 7591259) B7591259
theorem B2996459 : Blo 1330984 2996459 := bstep (se 1 (by rfl) ⟨2247344, by rfl⟩ : syracuseStep 2996459 = 4494689) B4494689
theorem B6396191 : Blo 1330984 6396191 := bstep (se 1 (by rfl) ⟨4797143, by rfl⟩ : syracuseStep 6396191 = 9594287) B9594287
theorem B6740333 : Blo 1330984 6740333 := bstep (se 3 (by rfl) ⟨1263812, by rfl⟩ : syracuseStep 6740333 = 2527625) B2527625
theorem B9116077 : Blo 1330984 9116077 := bstep (se 3 (by rfl) ⟨1709264, by rfl⟩ : syracuseStep 9116077 = 3418529) B3418529
theorem B1997255 : Blo 1330984 1997255 := bstep (se 1 (by rfl) ⟨1497941, by rfl⟩ : syracuseStep 1997255 = 2995883) B2995883
theorem B2701775 : Blo 1330984 2701775 := bstep (se 1 (by rfl) ⟨2026331, by rfl⟩ : syracuseStep 2701775 = 4052663) B4052663
theorem B2529767 : Blo 1330984 2529767 := bstep (se 1 (by rfl) ⟨1897325, by rfl⟩ : syracuseStep 2529767 = 3794651) B3794651
theorem B10115603 : Blo 1330984 10115603 := bstep (se 1 (by rfl) ⟨7586702, by rfl⟩ : syracuseStep 10115603 = 15173405) B15173405
theorem B3201563 : Blo 1330984 3201563 := bstep (se 1 (by rfl) ⟨2401172, by rfl⟩ : syracuseStep 3201563 = 4802345) B4802345
theorem B3373609 : Blo 1330984 3373609 := bstep (se 2 (by rfl) ⟨1265103, by rfl⟩ : syracuseStep 3373609 = 2530207) B2530207
theorem B1997471 : Blo 1330984 1997471 := bstep (se 1 (by rfl) ⟨1498103, by rfl⟩ : syracuseStep 1997471 = 2996207) B2996207
theorem B5765897 : Blo 1330984 5765897 := bstep (se 2 (by rfl) ⟨2162211, by rfl⟩ : syracuseStep 5765897 = 4324423) B4324423
theorem B1997615 : Blo 1330984 1997615 := bstep (se 1 (by rfl) ⟨1498211, by rfl⟩ : syracuseStep 1997615 = 2996423) B2996423
theorem B2399033 : Blo 1330984 2399033 := bstep (se 2 (by rfl) ⟨899637, by rfl⟩ : syracuseStep 2399033 = 1799275) B1799275
theorem B1997735 : Blo 1330984 1997735 := bstep (se 1 (by rfl) ⟨1498301, by rfl⟩ : syracuseStep 1997735 = 2996603) B2996603
theorem B1997915 : Blo 1330984 1997915 := bstep (se 1 (by rfl) ⟨1498436, by rfl⟩ : syracuseStep 1997915 = 2996873) B2996873
theorem B6077531 : Blo 1330984 6077531 := bstep (se 1 (by rfl) ⟨4558148, by rfl⟩ : syracuseStep 6077531 = 9116297) B9116297
theorem B2530511 : Blo 1330984 2530511 := bstep (se 1 (by rfl) ⟨1897883, by rfl⟩ : syracuseStep 2530511 = 3795767) B3795767
theorem B19193233 : Blo 1330984 19193233 := bstep (se 2 (by rfl) ⟨7197462, by rfl⟩ : syracuseStep 19193233 = 14394925) B14394925
theorem B1998287 : Blo 1330984 1998287 := bstep (se 1 (by rfl) ⟨1498715, by rfl⟩ : syracuseStep 1998287 = 2997431) B2997431
theorem B2997755 : Blo 1330984 2997755 := bstep (se 1 (by rfl) ⟨2248316, by rfl⟩ : syracuseStep 2997755 = 4496633) B4496633
theorem B2997935 : Blo 1330984 2997935 := bstep (se 1 (by rfl) ⟨2248451, by rfl⟩ : syracuseStep 2997935 = 4496903) B4496903
theorem B32390837 : Blo 1330984 32390837 := bstep (se 5 (by rfl) ⟨1518320, by rfl⟩ : syracuseStep 32390837 = 3036641) B3036641
theorem B1498855 : Blo 1330984 1498855 := bstep (se 1 (by rfl) ⟨1124141, by rfl⟩ : syracuseStep 1498855 = 2248283) B2248283
theorem B2998025 : Blo 1330984 2998025 := bstep (se 2 (by rfl) ⟨1124259, by rfl⟩ : syracuseStep 2998025 = 2248519) B2248519
theorem B1998671 : Blo 1330984 1998671 := bstep (se 1 (by rfl) ⟨1499003, by rfl⟩ : syracuseStep 1998671 = 2998007) B2998007
theorem B1998791 : Blo 1330984 1998791 := bstep (se 1 (by rfl) ⟨1499093, by rfl⟩ : syracuseStep 1998791 = 2998187) B2998187
theorem B1999103 : Blo 1330984 1999103 := bstep (se 1 (by rfl) ⟨1499327, by rfl⟩ : syracuseStep 1999103 = 2998655) B2998655
theorem B1999259 : Blo 1330984 1999259 := bstep (se 1 (by rfl) ⟨1499444, by rfl⟩ : syracuseStep 1999259 = 2998889) B2998889
theorem B11371103 : Blo 1330984 11371103 := bstep (se 1 (by rfl) ⟨8528327, by rfl⟩ : syracuseStep 11371103 = 17056655) B17056655
theorem B4498145 : Blo 1330984 4498145 := bstep (se 2 (by rfl) ⟨1686804, by rfl⟩ : syracuseStep 4498145 = 3373609) B3373609
theorem B11379851 : Blo 1330984 11379851 := bstep (se 1 (by rfl) ⟨8534888, by rfl⟩ : syracuseStep 11379851 = 17069777) B17069777
theorem B3794195 : Blo 1330984 3794195 := bstep (se 1 (by rfl) ⟨2845646, by rfl⟩ : syracuseStep 3794195 = 5691293) B5691293
theorem B36472189 : Blo 1330984 36472189 := bstep (se 3 (by rfl) ⟨6838535, by rfl⟩ : syracuseStep 36472189 = 13677071) B13677071
theorem B8537501 : Blo 1330984 8537501 := bstep (se 3 (by rfl) ⟨1600781, by rfl⟩ : syracuseStep 8537501 = 3201563) B3201563
theorem B24020653 : Blo 1330984 24020653 := bstep (se 3 (by rfl) ⟨4503872, by rfl⟩ : syracuseStep 24020653 = 9007745) B9007745
theorem B6743735 : Blo 1330984 6743735 := bstep (se 1 (by rfl) ⟨5057801, by rfl⟩ : syracuseStep 6743735 = 10115603) B10115603
theorem B3843931 : Blo 1330984 3843931 := bstep (se 1 (by rfl) ⟨2882948, by rfl⟩ : syracuseStep 3843931 = 5765897) B5765897
theorem B1599355 : Blo 1330984 1599355 := bstep (se 1 (by rfl) ⟨1199516, by rfl⟩ : syracuseStep 1599355 = 2399033) B2399033
theorem B4802447 : Blo 1330984 4802447 := bstep (se 1 (by rfl) ⟨3601835, by rfl⟩ : syracuseStep 4802447 = 7203671) B7203671
theorem B24307721 : Blo 1330984 24307721 := bstep (se 2 (by rfl) ⟨9115395, by rfl⟩ : syracuseStep 24307721 = 18230791) B18230791
theorem B2844809 : Blo 1330984 2844809 := bstep (se 2 (by rfl) ⟨1066803, by rfl⟩ : syracuseStep 2844809 = 2133607) B2133607
theorem B21596543 : Blo 1330984 21596543 := bstep (se 1 (by rfl) ⟨16197407, by rfl⟩ : syracuseStep 21596543 = 32394815) B32394815
theorem B6744545 : Blo 1330984 6744545 := bstep (se 2 (by rfl) ⟨2529204, by rfl⟩ : syracuseStep 6744545 = 5058409) B5058409
theorem B17066801 : Blo 1330984 17066801 := bstep (se 2 (by rfl) ⟨6400050, by rfl⟩ : syracuseStep 17066801 = 12800101) B12800101
theorem B3795835 : Blo 1330984 3795835 := bstep (se 1 (by rfl) ⟨2846876, by rfl⟩ : syracuseStep 3795835 = 5693753) B5693753
theorem B16206749 : Blo 1330984 16206749 := bstep (se 3 (by rfl) ⟨3038765, by rfl⟩ : syracuseStep 16206749 = 6077531) B6077531
theorem B6401015 : Blo 1330984 6401015 := bstep (se 1 (by rfl) ⟨4800761, by rfl⟩ : syracuseStep 6401015 = 9601523) B9601523
theorem B3370025 : Blo 1330984 3370025 := bstep (se 2 (by rfl) ⟨1263759, by rfl⟩ : syracuseStep 3370025 = 2527519) B2527519
theorem B8105125 : Blo 1330984 8105125 := bstep (se 4 (by rfl) ⟨759855, by rfl⟩ : syracuseStep 8105125 = 1519711) B1519711
theorem B2248303 : Blo 1330984 2248303 := bstep (se 1 (by rfl) ⟨1686227, by rfl⟩ : syracuseStep 2248303 = 3372455) B3372455
theorem B3370967 : Blo 1330984 3370967 := bstep (se 1 (by rfl) ⟨2528225, by rfl⟩ : syracuseStep 3370967 = 5056451) B5056451
theorem B1331227 : Blo 1330984 1331227 := bstep (se 1 (by rfl) ⟨998420, by rfl⟩ : syracuseStep 1331227 = 1996841) B1996841
theorem B1331247 : Blo 1330984 1331247 := bstep (se 1 (by rfl) ⟨998435, by rfl⟩ : syracuseStep 1331247 = 1996871) B1996871
theorem B3199103 : Blo 1330984 3199103 := bstep (se 1 (by rfl) ⟨2399327, by rfl⟩ : syracuseStep 3199103 = 4798655) B4798655
theorem B12153017 : Blo 1330984 12153017 := bstep (se 2 (by rfl) ⟨4557381, by rfl⟩ : syracuseStep 12153017 = 9114763) B9114763
theorem B4264127 : Blo 1330984 4264127 := bstep (se 1 (by rfl) ⟨3198095, by rfl⟩ : syracuseStep 4264127 = 6396191) B6396191
theorem B10121435 : Blo 1330984 10121435 := bstep (se 1 (by rfl) ⟨7591076, by rfl⟩ : syracuseStep 10121435 = 15182153) B15182153
theorem B4493555 : Blo 1330984 4493555 := bstep (se 1 (by rfl) ⟨3370166, by rfl⟩ : syracuseStep 4493555 = 6740333) B6740333
theorem B1331503 : Blo 1330984 1331503 := bstep (se 1 (by rfl) ⟨998627, by rfl⟩ : syracuseStep 1331503 = 1997255) B1997255
theorem B1331647 : Blo 1330984 1331647 := bstep (se 1 (by rfl) ⟨998735, by rfl⟩ : syracuseStep 1331647 = 1997471) B1997471
theorem B4264445 : Blo 1330984 4264445 := bstep (se 3 (by rfl) ⟨799583, by rfl⟩ : syracuseStep 4264445 = 1599167) B1599167
theorem B1331743 : Blo 1330984 1331743 := bstep (se 1 (by rfl) ⟨998807, by rfl⟩ : syracuseStep 1331743 = 1997615) B1997615
theorem B7590509 : Blo 1330984 7590509 := bstep (se 3 (by rfl) ⟨1423220, by rfl⟩ : syracuseStep 7590509 = 2846441) B2846441
theorem B1331823 : Blo 1330984 1331823 := bstep (se 1 (by rfl) ⟨998867, by rfl⟩ : syracuseStep 1331823 = 1997735) B1997735
theorem B1331943 : Blo 1330984 1331943 := bstep (se 1 (by rfl) ⟨998957, by rfl⟩ : syracuseStep 1331943 = 1997915) B1997915
theorem B4797215 : Blo 1330984 4797215 := bstep (se 1 (by rfl) ⟨3597911, by rfl⟩ : syracuseStep 4797215 = 7195823) B7195823
theorem B2994983 : Blo 1330984 2994983 := bstep (se 1 (by rfl) ⟨2246237, by rfl⟩ : syracuseStep 2994983 = 4492475) B4492475
theorem B2995001 : Blo 1330984 2995001 := bstep (se 2 (by rfl) ⟨1123125, by rfl⟩ : syracuseStep 2995001 = 2246251) B2246251
theorem B1332191 : Blo 1330984 1332191 := bstep (se 1 (by rfl) ⟨999143, by rfl⟩ : syracuseStep 1332191 = 1998287) B1998287
theorem B1897519 : Blo 1330984 1897519 := bstep (se 1 (by rfl) ⟨1423139, by rfl⟩ : syracuseStep 1897519 = 2846279) B2846279
theorem B2995361 : Blo 1330984 2995361 := bstep (se 2 (by rfl) ⟨1123260, by rfl⟩ : syracuseStep 2995361 = 2246521) B2246521
theorem B12154049 : Blo 1330984 12154049 := bstep (se 2 (by rfl) ⟨4557768, by rfl⟩ : syracuseStep 12154049 = 9115537) B9115537
theorem B1332447 : Blo 1330984 1332447 := bstep (se 1 (by rfl) ⟨999335, by rfl⟩ : syracuseStep 1332447 = 1998671) B1998671
theorem B1332527 : Blo 1330984 1332527 := bstep (se 1 (by rfl) ⟨999395, by rfl⟩ : syracuseStep 1332527 = 1998791) B1998791
theorem B2995631 : Blo 1330984 2995631 := bstep (se 1 (by rfl) ⟨2246723, by rfl⟩ : syracuseStep 2995631 = 4493447) B4493447
theorem B2995739 : Blo 1330984 2995739 := bstep (se 1 (by rfl) ⟨2246804, by rfl⟩ : syracuseStep 2995739 = 4493609) B4493609
theorem B1332767 : Blo 1330984 1332767 := bstep (se 1 (by rfl) ⟨999575, by rfl⟩ : syracuseStep 1332767 = 1999151) B1999151
theorem B6747785 : Blo 1330984 6747785 := bstep (se 2 (by rfl) ⟨2530419, by rfl⟩ : syracuseStep 6747785 = 5060839) B5060839
theorem B1332927 : Blo 1330984 1332927 := bstep (se 1 (by rfl) ⟨999695, by rfl⟩ : syracuseStep 1332927 = 1999391) B1999391
theorem B2995919 : Blo 1330984 2995919 := bstep (se 1 (by rfl) ⟨2246939, by rfl⟩ : syracuseStep 2995919 = 4493879) B4493879
theorem B4495175 : Blo 1330984 4495175 := bstep (se 1 (by rfl) ⟨3371381, by rfl⟩ : syracuseStep 4495175 = 6742763) B6742763
theorem B28800845 : Blo 1330984 28800845 := bstep (se 3 (by rfl) ⟨5400158, by rfl⟩ : syracuseStep 28800845 = 10800317) B10800317
theorem B12154769 : Blo 1330984 12154769 := bstep (se 2 (by rfl) ⟨4558038, by rfl⟩ : syracuseStep 12154769 = 9116077) B9116077
theorem B1996847 : Blo 1330984 1996847 := bstep (se 1 (by rfl) ⟨1497635, by rfl⟩ : syracuseStep 1996847 = 2995271) B2995271
theorem B3373103 : Blo 1330984 3373103 := bstep (se 1 (by rfl) ⟨2529827, by rfl⟩ : syracuseStep 3373103 = 5059655) B5059655
theorem B17307757 : Blo 1330984 17307757 := bstep (se 3 (by rfl) ⟨3245204, by rfl⟩ : syracuseStep 17307757 = 6490409) B6490409
theorem B1996967 : Blo 1330984 1996967 := bstep (se 1 (by rfl) ⟨1497725, by rfl⟩ : syracuseStep 1996967 = 2995451) B2995451
theorem B1997111 : Blo 1330984 1997111 := bstep (se 1 (by rfl) ⟨1497833, by rfl⟩ : syracuseStep 1997111 = 2995667) B2995667
theorem B2996711 : Blo 1330984 2996711 := bstep (se 1 (by rfl) ⟨2247533, by rfl⟩ : syracuseStep 2996711 = 4495067) B4495067
theorem B1997291 : Blo 1330984 1997291 := bstep (se 1 (by rfl) ⟨1497968, by rfl⟩ : syracuseStep 1997291 = 2995937) B2995937
theorem B4266587 : Blo 1330984 4266587 := bstep (se 1 (by rfl) ⟨3199940, by rfl⟩ : syracuseStep 4266587 = 6399881) B6399881
theorem B1497919 : Blo 1330984 1497919 := bstep (se 1 (by rfl) ⟨1123439, by rfl⟩ : syracuseStep 1497919 = 2246879) B2246879
theorem B1997639 : Blo 1330984 1997639 := bstep (se 1 (by rfl) ⟨1498229, by rfl⟩ : syracuseStep 1997639 = 2996459) B2996459
theorem B1801183 : Blo 1330984 1801183 := bstep (se 1 (by rfl) ⟨1350887, by rfl⟩ : syracuseStep 1801183 = 2701775) B2701775
theorem B1686511 : Blo 1330984 1686511 := bstep (se 1 (by rfl) ⟨1264883, by rfl⟩ : syracuseStep 1686511 = 2529767) B2529767
theorem B2563127 : Blo 1330984 2563127 := bstep (se 1 (by rfl) ⟨1922345, by rfl⟩ : syracuseStep 2563127 = 3844691) B3844691
theorem B25590977 : Blo 1330984 25590977 := bstep (se 2 (by rfl) ⟨9596616, by rfl⟩ : syracuseStep 25590977 = 19193233) B19193233
theorem B24288515 : Blo 1330984 24288515 := bstep (se 1 (by rfl) ⟨18216386, by rfl⟩ : syracuseStep 24288515 = 36432773) B36432773
theorem B1498495 : Blo 1330984 1498495 := bstep (se 1 (by rfl) ⟨1123871, by rfl⟩ : syracuseStep 1498495 = 2247743) B2247743
theorem B1687007 : Blo 1330984 1687007 := bstep (se 1 (by rfl) ⟨1265255, by rfl⟩ : syracuseStep 1687007 = 2530511) B2530511
theorem B15179237 : Blo 1330984 15179237 := bstep (se 4 (by rfl) ⟨1423053, by rfl⟩ : syracuseStep 15179237 = 2846107) B2846107
theorem B6741629 : Blo 1330984 6741629 := bstep (se 3 (by rfl) ⟨1264055, by rfl⟩ : syracuseStep 6741629 = 2528111) B2528111
theorem B1998473 : Blo 1330984 1998473 := bstep (se 2 (by rfl) ⟨749427, by rfl⟩ : syracuseStep 1998473 = 1498855) B1498855
theorem B1998503 : Blo 1330984 1998503 := bstep (se 1 (by rfl) ⟨1498877, by rfl⟩ : syracuseStep 1998503 = 2997755) B2997755
theorem B6741791 : Blo 1330984 6741791 := bstep (se 1 (by rfl) ⟨5056343, by rfl⟩ : syracuseStep 6741791 = 10112687) B10112687
theorem B1998623 : Blo 1330984 1998623 := bstep (se 1 (by rfl) ⟨1498967, by rfl⟩ : syracuseStep 1998623 = 2997935) B2997935
theorem B21593891 : Blo 1330984 21593891 := bstep (se 1 (by rfl) ⟨16195418, by rfl⟩ : syracuseStep 21593891 = 32390837) B32390837
theorem B1998683 : Blo 1330984 1998683 := bstep (se 1 (by rfl) ⟨1499012, by rfl⟩ : syracuseStep 1998683 = 2998025) B2998025
theorem B3792737 : Blo 1330984 3792737 := bstep (se 2 (by rfl) ⟨1422276, by rfl⟩ : syracuseStep 3792737 = 2844553) B2844553
theorem B374202227 : Blo 1330984 374202227 := bstep (se 1 (by rfl) ⟨280651670, by rfl⟩ : syracuseStep 374202227 = 561303341) B561303341
theorem B3792851 : Blo 1330984 3792851 := bstep (se 1 (by rfl) ⟨2844638, by rfl⟩ : syracuseStep 3792851 = 5689277) B5689277
theorem B7200749 : Blo 1330984 7200749 := bstep (se 3 (by rfl) ⟨1350140, by rfl⟩ : syracuseStep 7200749 = 2700281) B2700281
theorem B2842751 : Blo 1330984 2842751 := bstep (se 1 (by rfl) ⟨2132063, by rfl⟩ : syracuseStep 2842751 = 4264127) B4264127
theorem B23077009 : Blo 1330984 23077009 := bstep (se 2 (by rfl) ⟨8653878, by rfl⟩ : syracuseStep 23077009 = 17307757) B17307757
theorem B2998763 : Blo 1330984 2998763 := bstep (se 1 (by rfl) ⟨2249072, by rfl⟩ : syracuseStep 2998763 = 4498145) B4498145
theorem B32408045 : Blo 1330984 32408045 := bstep (se 3 (by rfl) ⟨6076508, by rfl⟩ : syracuseStep 32408045 = 12153017) B12153017
theorem B7586567 : Blo 1330984 7586567 := bstep (se 1 (by rfl) ⟨5689925, by rfl⟩ : syracuseStep 7586567 = 11379851) B11379851
theorem B8102699 : Blo 1330984 8102699 := bstep (se 1 (by rfl) ⟨6077024, by rfl⟩ : syracuseStep 8102699 = 12154049) B12154049
theorem B22766669 : Blo 1330984 22766669 := bstep (se 3 (by rfl) ⟨4268750, by rfl⟩ : syracuseStep 22766669 = 8537501) B8537501
theorem B4498523 : Blo 1330984 4498523 := bstep (se 1 (by rfl) ⟨3373892, by rfl⟩ : syracuseStep 4498523 = 6747785) B6747785
theorem B4498685 : Blo 1330984 4498685 := bstep (se 3 (by rfl) ⟨843503, by rfl⟩ : syracuseStep 4498685 = 1687007) B1687007
theorem B8103179 : Blo 1330984 8103179 := bstep (se 1 (by rfl) ⟨6077384, by rfl⟩ : syracuseStep 8103179 = 12154769) B12154769
theorem B2401577 : Blo 1330984 2401577 := bstep (se 2 (by rfl) ⟨900591, by rfl⟩ : syracuseStep 2401577 = 1801183) B1801183
theorem B11371853 : Blo 1330984 11371853 := bstep (se 3 (by rfl) ⟨2132222, by rfl⟩ : syracuseStep 11371853 = 4264445) B4264445
theorem B16205147 : Blo 1330984 16205147 := bstep (se 1 (by rfl) ⟨12153860, by rfl⟩ : syracuseStep 16205147 = 24307721) B24307721
theorem B10806833 : Blo 1330984 10806833 := bstep (se 2 (by rfl) ⟨4052562, by rfl⟩ : syracuseStep 10806833 = 8105125) B8105125
theorem B2844391 : Blo 1330984 2844391 := bstep (se 1 (by rfl) ⟨2133293, by rfl⟩ : syracuseStep 2844391 = 4266587) B4266587
theorem B48629585 : Blo 1330984 48629585 := bstep (se 2 (by rfl) ⟨18236094, by rfl⟩ : syracuseStep 48629585 = 36472189) B36472189
theorem B8529893 : Blo 1330984 8529893 := bstep (se 4 (by rfl) ⟨799677, by rfl⟩ : syracuseStep 8529893 = 1599355) B1599355
theorem B2246683 : Blo 1330984 2246683 := bstep (se 1 (by rfl) ⟨1685012, by rfl⟩ : syracuseStep 2246683 = 3370025) B3370025
theorem B10119491 : Blo 1330984 10119491 := bstep (se 1 (by rfl) ⟨7589618, by rfl⟩ : syracuseStep 10119491 = 15179237) B15179237
theorem B12806525 : Blo 1330984 12806525 := bstep (se 3 (by rfl) ⟨2401223, by rfl⟩ : syracuseStep 12806525 = 4802447) B4802447
theorem B14395927 : Blo 1330984 14395927 := bstep (se 1 (by rfl) ⟨10796945, by rfl⟩ : syracuseStep 14395927 = 21593891) B21593891
theorem B2247311 : Blo 1330984 2247311 := bstep (se 1 (by rfl) ⟨1685483, by rfl⟩ : syracuseStep 2247311 = 3370967) B3370967
theorem B2132735 : Blo 1330984 2132735 := bstep (se 1 (by rfl) ⟨1599551, by rfl⟩ : syracuseStep 2132735 = 3199103) B3199103
theorem B7580735 : Blo 1330984 7580735 := bstep (se 1 (by rfl) ⟨5685551, by rfl⟩ : syracuseStep 7580735 = 11371103) B11371103
theorem B3198143 : Blo 1330984 3198143 := bstep (se 1 (by rfl) ⟨2398607, by rfl⟩ : syracuseStep 3198143 = 4797215) B4797215
theorem B27340021 : Blo 1330984 27340021 := bstep (se 5 (by rfl) ⟨1281563, by rfl⟩ : syracuseStep 27340021 = 2563127) B2563127
theorem B2248681 : Blo 1330984 2248681 := bstep (se 2 (by rfl) ⟨843255, by rfl⟩ : syracuseStep 2248681 = 1686511) B1686511
theorem B1331231 : Blo 1330984 1331231 := bstep (se 1 (by rfl) ⟨998423, by rfl⟩ : syracuseStep 1331231 = 1996847) B1996847
theorem B2248735 : Blo 1330984 2248735 := bstep (se 1 (by rfl) ⟨1686551, by rfl⟩ : syracuseStep 2248735 = 3373103) B3373103
theorem B1896539 : Blo 1330984 1896539 := bstep (se 1 (by rfl) ⟨1422404, by rfl⟩ : syracuseStep 1896539 = 2844809) B2844809
theorem B1331311 : Blo 1330984 1331311 := bstep (se 1 (by rfl) ⟨998483, by rfl⟩ : syracuseStep 1331311 = 1996967) B1996967
theorem B1331407 : Blo 1330984 1331407 := bstep (se 1 (by rfl) ⟨998555, by rfl⟩ : syracuseStep 1331407 = 1997111) B1997111
theorem B14397695 : Blo 1330984 14397695 := bstep (se 1 (by rfl) ⟨10798271, by rfl⟩ : syracuseStep 14397695 = 21596543) B21596543
theorem B1331527 : Blo 1330984 1331527 := bstep (se 1 (by rfl) ⟨998645, by rfl⟩ : syracuseStep 1331527 = 1997291) B1997291
theorem B1331759 : Blo 1330984 1331759 := bstep (se 1 (by rfl) ⟨998819, by rfl⟩ : syracuseStep 1331759 = 1997639) B1997639
theorem B17060651 : Blo 1330984 17060651 := bstep (se 1 (by rfl) ⟨12795488, by rfl⟩ : syracuseStep 17060651 = 25590977) B25590977
theorem B16192343 : Blo 1330984 16192343 := bstep (se 1 (by rfl) ⟨12144257, by rfl⟩ : syracuseStep 16192343 = 24288515) B24288515
theorem B32027537 : Blo 1330984 32027537 := bstep (se 2 (by rfl) ⟨12010326, by rfl⟩ : syracuseStep 32027537 = 24020653) B24020653
theorem B997872605 : Blo 1330984 997872605 := bstep (se 3 (by rfl) ⟨187101113, by rfl⟩ : syracuseStep 997872605 = 374202227) B374202227
theorem B4494419 : Blo 1330984 4494419 := bstep (se 1 (by rfl) ⟨3370814, by rfl⟩ : syracuseStep 4494419 = 6741629) B6741629
theorem B1332315 : Blo 1330984 1332315 := bstep (se 1 (by rfl) ⟨999236, by rfl⟩ : syracuseStep 1332315 = 1998473) B1998473
theorem B1332335 : Blo 1330984 1332335 := bstep (se 1 (by rfl) ⟨999251, by rfl⟩ : syracuseStep 1332335 = 1998503) B1998503
theorem B5125241 : Blo 1330984 5125241 := bstep (se 2 (by rfl) ⟨1921965, by rfl⟩ : syracuseStep 5125241 = 3843931) B3843931
theorem B4494527 : Blo 1330984 4494527 := bstep (se 1 (by rfl) ⟨3370895, by rfl⟩ : syracuseStep 4494527 = 6741791) B6741791
theorem B1332415 : Blo 1330984 1332415 := bstep (se 1 (by rfl) ⟨999311, by rfl⟩ : syracuseStep 1332415 = 1998623) B1998623
theorem B1332455 : Blo 1330984 1332455 := bstep (se 1 (by rfl) ⟨999341, by rfl⟩ : syracuseStep 1332455 = 1998683) B1998683
theorem B2528491 : Blo 1330984 2528491 := bstep (se 1 (by rfl) ⟨1896368, by rfl⟩ : syracuseStep 2528491 = 3792737) B3792737
theorem B2528567 : Blo 1330984 2528567 := bstep (se 1 (by rfl) ⟨1896425, by rfl⟩ : syracuseStep 2528567 = 3792851) B3792851
theorem B6747623 : Blo 1330984 6747623 := bstep (se 1 (by rfl) ⟨5060717, by rfl⟩ : syracuseStep 6747623 = 10121435) B10121435
theorem B2995703 : Blo 1330984 2995703 := bstep (se 1 (by rfl) ⟨2246777, by rfl⟩ : syracuseStep 2995703 = 4493555) B4493555
theorem B1332735 : Blo 1330984 1332735 := bstep (se 1 (by rfl) ⟨999551, by rfl⟩ : syracuseStep 1332735 = 1999103) B1999103
theorem B1332839 : Blo 1330984 1332839 := bstep (se 1 (by rfl) ⟨999629, by rfl⟩ : syracuseStep 1332839 = 1999259) B1999259
theorem B5060339 : Blo 1330984 5060339 := bstep (se 1 (by rfl) ⟨3795254, by rfl⟩ : syracuseStep 5060339 = 7590509) B7590509
theorem B1996655 : Blo 1330984 1996655 := bstep (se 1 (by rfl) ⟨1497491, by rfl⟩ : syracuseStep 1996655 = 2994983) B2994983
theorem B1996667 : Blo 1330984 1996667 := bstep (se 1 (by rfl) ⟨1497500, by rfl⟩ : syracuseStep 1996667 = 2995001) B2995001
theorem B1996907 : Blo 1330984 1996907 := bstep (se 1 (by rfl) ⟨1497680, by rfl⟩ : syracuseStep 1996907 = 2995361) B2995361
theorem B2529463 : Blo 1330984 2529463 := bstep (se 1 (by rfl) ⟨1897097, by rfl⟩ : syracuseStep 2529463 = 3794195) B3794195
theorem B1997087 : Blo 1330984 1997087 := bstep (se 1 (by rfl) ⟨1497815, by rfl⟩ : syracuseStep 1997087 = 2995631) B2995631
theorem B1997159 : Blo 1330984 1997159 := bstep (se 1 (by rfl) ⟨1497869, by rfl⟩ : syracuseStep 1997159 = 2995739) B2995739
theorem B1997225 : Blo 1330984 1997225 := bstep (se 2 (by rfl) ⟨748959, by rfl⟩ : syracuseStep 1997225 = 1497919) B1497919
theorem B4495823 : Blo 1330984 4495823 := bstep (se 1 (by rfl) ⟨3371867, by rfl⟩ : syracuseStep 4495823 = 6743735) B6743735
theorem B1997279 : Blo 1330984 1997279 := bstep (se 1 (by rfl) ⟨1497959, by rfl⟩ : syracuseStep 1997279 = 2995919) B2995919
theorem B5061113 : Blo 1330984 5061113 := bstep (se 2 (by rfl) ⟨1897917, by rfl⟩ : syracuseStep 5061113 = 3795835) B3795835
theorem B2996783 : Blo 1330984 2996783 := bstep (se 1 (by rfl) ⟨2247587, by rfl⟩ : syracuseStep 2996783 = 4495175) B4495175
theorem B19200563 : Blo 1330984 19200563 := bstep (se 1 (by rfl) ⟨14400422, by rfl⟩ : syracuseStep 19200563 = 28800845) B28800845
theorem B2530025 : Blo 1330984 2530025 := bstep (se 2 (by rfl) ⟨948759, by rfl⟩ : syracuseStep 2530025 = 1897519) B1897519
theorem B4496363 : Blo 1330984 4496363 := bstep (se 1 (by rfl) ⟨3372272, by rfl⟩ : syracuseStep 4496363 = 6744545) B6744545
theorem B1997807 : Blo 1330984 1997807 := bstep (se 1 (by rfl) ⟨1498355, by rfl⟩ : syracuseStep 1997807 = 2996711) B2996711
theorem B1997993 : Blo 1330984 1997993 := bstep (se 2 (by rfl) ⟨749247, by rfl⟩ : syracuseStep 1997993 = 1498495) B1498495
theorem B11377867 : Blo 1330984 11377867 := bstep (se 1 (by rfl) ⟨8533400, by rfl⟩ : syracuseStep 11377867 = 17066801) B17066801
theorem B10804499 : Blo 1330984 10804499 := bstep (se 1 (by rfl) ⟨8103374, by rfl⟩ : syracuseStep 10804499 = 16206749) B16206749
theorem B4267343 : Blo 1330984 4267343 := bstep (se 1 (by rfl) ⟨3200507, by rfl⟩ : syracuseStep 4267343 = 6401015) B6401015
theorem B2997737 : Blo 1330984 2997737 := bstep (se 2 (by rfl) ⟨1124151, by rfl⟩ : syracuseStep 2997737 = 2248303) B2248303
theorem B19201997 : Blo 1330984 19201997 := bstep (se 3 (by rfl) ⟨3600374, by rfl⟩ : syracuseStep 19201997 = 7200749) B7200749
theorem B2998313 : Blo 1330984 2998313 := bstep (se 2 (by rfl) ⟨1124367, by rfl⟩ : syracuseStep 2998313 = 2248735) B2248735
theorem B30769345 : Blo 1330984 30769345 := bstep (se 2 (by rfl) ⟨11538504, by rfl⟩ : syracuseStep 30769345 = 23077009) B23077009
theorem B1999175 : Blo 1330984 1999175 := bstep (se 1 (by rfl) ⟨1499381, by rfl⟩ : syracuseStep 1999175 = 2998763) B2998763
theorem B665248403 : Blo 1330984 665248403 := bstep (se 1 (by rfl) ⟨498936302, by rfl⟩ : syracuseStep 665248403 = 997872605) B997872605
theorem B19194569 : Blo 1330984 19194569 := bstep (se 2 (by rfl) ⟨7197963, by rfl⟩ : syracuseStep 19194569 = 14395927) B14395927
theorem B2999015 : Blo 1330984 2999015 := bstep (se 1 (by rfl) ⟨2249261, by rfl⟩ : syracuseStep 2999015 = 4498523) B4498523
theorem B3416827 : Blo 1330984 3416827 := bstep (se 1 (by rfl) ⟨2562620, by rfl⟩ : syracuseStep 3416827 = 5125241) B5125241
theorem B2999123 : Blo 1330984 2999123 := bstep (se 1 (by rfl) ⟨2249342, by rfl⟩ : syracuseStep 2999123 = 4498685) B4498685
theorem B4498415 : Blo 1330984 4498415 := bstep (se 1 (by rfl) ⟨3373811, by rfl⟩ : syracuseStep 4498415 = 6747623) B6747623
theorem B5686595 : Blo 1330984 5686595 := bstep (se 1 (by rfl) ⟨4264946, by rfl⟩ : syracuseStep 5686595 = 8529893) B8529893
theorem B8537683 : Blo 1330984 8537683 := bstep (se 1 (by rfl) ⟨6403262, by rfl⟩ : syracuseStep 8537683 = 12806525) B12806525
theorem B2132095 : Blo 1330984 2132095 := bstep (se 1 (by rfl) ⟨1599071, by rfl⟩ : syracuseStep 2132095 = 3198143) B3198143
theorem B7202999 : Blo 1330984 7202999 := bstep (se 1 (by rfl) ⟨5402249, by rfl⟩ : syracuseStep 7202999 = 10804499) B10804499
theorem B2844895 : Blo 1330984 2844895 := bstep (se 1 (by rfl) ⟨2133671, by rfl⟩ : syracuseStep 2844895 = 4267343) B4267343
theorem B1895167 : Blo 1330984 1895167 := bstep (se 1 (by rfl) ⟨1421375, by rfl⟩ : syracuseStep 1895167 = 2842751) B2842751
theorem B5057437 : Blo 1330984 5057437 := bstep (se 3 (by rfl) ⟨948269, by rfl⟩ : syracuseStep 5057437 = 1896539) B1896539
theorem B21605363 : Blo 1330984 21605363 := bstep (se 1 (by rfl) ⟨16204022, by rfl⟩ : syracuseStep 21605363 = 32408045) B32408045
theorem B5057711 : Blo 1330984 5057711 := bstep (se 1 (by rfl) ⟨3793283, by rfl⟩ : syracuseStep 5057711 = 7586567) B7586567
theorem B11373767 : Blo 1330984 11373767 := bstep (se 1 (by rfl) ⟨8530325, by rfl⟩ : syracuseStep 11373767 = 17060651) B17060651
theorem B5401799 : Blo 1330984 5401799 := bstep (se 1 (by rfl) ⟨4051349, by rfl⟩ : syracuseStep 5401799 = 8102699) B8102699
theorem B21351691 : Blo 1330984 21351691 := bstep (se 1 (by rfl) ⟨16013768, by rfl⟩ : syracuseStep 21351691 = 32027537) B32027537
theorem B1601051 : Blo 1330984 1601051 := bstep (se 1 (by rfl) ⟨1200788, by rfl⟩ : syracuseStep 1601051 = 2401577) B2401577
theorem B7581235 : Blo 1330984 7581235 := bstep (se 1 (by rfl) ⟨5685926, by rfl⟩ : syracuseStep 7581235 = 11371853) B11371853
theorem B7204555 : Blo 1330984 7204555 := bstep (se 1 (by rfl) ⟨5403416, by rfl⟩ : syracuseStep 7204555 = 10806833) B10806833
theorem B32419723 : Blo 1330984 32419723 := bstep (se 1 (by rfl) ⟨24314792, by rfl⟩ : syracuseStep 32419723 = 48629585) B48629585
theorem B1331103 : Blo 1330984 1331103 := bstep (se 1 (by rfl) ⟨998327, by rfl⟩ : syracuseStep 1331103 = 1996655) B1996655
theorem B1331111 : Blo 1330984 1331111 := bstep (se 1 (by rfl) ⟨998333, by rfl⟩ : syracuseStep 1331111 = 1996667) B1996667
theorem B1331271 : Blo 1330984 1331271 := bstep (se 1 (by rfl) ⟨998453, by rfl⟩ : syracuseStep 1331271 = 1996907) B1996907
theorem B1331391 : Blo 1330984 1331391 := bstep (se 1 (by rfl) ⟨998543, by rfl⟩ : syracuseStep 1331391 = 1997087) B1997087
theorem B6746327 : Blo 1330984 6746327 := bstep (se 1 (by rfl) ⟨5059745, by rfl⟩ : syracuseStep 6746327 = 10119491) B10119491
theorem B1331439 : Blo 1330984 1331439 := bstep (se 1 (by rfl) ⟨998579, by rfl⟩ : syracuseStep 1331439 = 1997159) B1997159
theorem B1331483 : Blo 1330984 1331483 := bstep (se 1 (by rfl) ⟨998612, by rfl⟩ : syracuseStep 1331483 = 1997225) B1997225
theorem B3371321 : Blo 1330984 3371321 := bstep (se 2 (by rfl) ⟨1264245, by rfl⟩ : syracuseStep 3371321 = 2528491) B2528491
theorem B1331519 : Blo 1330984 1331519 := bstep (se 1 (by rfl) ⟨998639, by rfl⟩ : syracuseStep 1331519 = 1997279) B1997279
theorem B12800375 : Blo 1330984 12800375 := bstep (se 1 (by rfl) ⟨9600281, by rfl⟩ : syracuseStep 12800375 = 19200563) B19200563
theorem B1331871 : Blo 1330984 1331871 := bstep (se 1 (by rfl) ⟨998903, by rfl⟩ : syracuseStep 1331871 = 1997807) B1997807
theorem B1331995 : Blo 1330984 1331995 := bstep (se 1 (by rfl) ⟨998996, by rfl⟩ : syracuseStep 1331995 = 1997993) B1997993
theorem B12801331 : Blo 1330984 12801331 := bstep (se 1 (by rfl) ⟨9600998, by rfl⟩ : syracuseStep 12801331 = 19201997) B19201997
theorem B2995577 : Blo 1330984 2995577 := bstep (se 2 (by rfl) ⟨1123341, by rfl⟩ : syracuseStep 2995577 = 2246683) B2246683
theorem B9598463 : Blo 1330984 9598463 := bstep (se 1 (by rfl) ⟨7198847, by rfl⟩ : syracuseStep 9598463 = 14397695) B14397695
theorem B3372617 : Blo 1330984 3372617 := bstep (se 2 (by rfl) ⟨1264731, by rfl⟩ : syracuseStep 3372617 = 2529463) B2529463
theorem B21608477 : Blo 1330984 21608477 := bstep (se 3 (by rfl) ⟨4051589, by rfl⟩ : syracuseStep 21608477 = 8103179) B8103179
theorem B15177779 : Blo 1330984 15177779 := bstep (se 1 (by rfl) ⟨11383334, by rfl⟩ : syracuseStep 15177779 = 22766669) B22766669
theorem B2996279 : Blo 1330984 2996279 := bstep (se 1 (by rfl) ⟨2247209, by rfl⟩ : syracuseStep 2996279 = 4494419) B4494419
theorem B2996351 : Blo 1330984 2996351 := bstep (se 1 (by rfl) ⟨2247263, by rfl⟩ : syracuseStep 2996351 = 4494527) B4494527
theorem B1685711 : Blo 1330984 1685711 := bstep (se 1 (by rfl) ⟨1264283, by rfl⟩ : syracuseStep 1685711 = 2528567) B2528567
theorem B10803431 : Blo 1330984 10803431 := bstep (se 1 (by rfl) ⟨8102573, by rfl⟩ : syracuseStep 10803431 = 16205147) B16205147
theorem B1997135 : Blo 1330984 1997135 := bstep (se 1 (by rfl) ⟨1497851, by rfl⟩ : syracuseStep 1997135 = 2995703) B2995703
theorem B3373559 : Blo 1330984 3373559 := bstep (se 1 (by rfl) ⟨2530169, by rfl⟩ : syracuseStep 3373559 = 5060339) B5060339
theorem B15170489 : Blo 1330984 15170489 := bstep (se 2 (by rfl) ⟨5688933, by rfl⟩ : syracuseStep 15170489 = 11377867) B11377867
theorem B2997215 : Blo 1330984 2997215 := bstep (se 1 (by rfl) ⟨2247911, by rfl⟩ : syracuseStep 2997215 = 4495823) B4495823
theorem B36453361 : Blo 1330984 36453361 := bstep (se 2 (by rfl) ⟨13670010, by rfl⟩ : syracuseStep 36453361 = 27340021) B27340021
theorem B3374075 : Blo 1330984 3374075 := bstep (se 1 (by rfl) ⟨2530556, by rfl⟩ : syracuseStep 3374075 = 5061113) B5061113
theorem B1997855 : Blo 1330984 1997855 := bstep (se 1 (by rfl) ⟨1498391, by rfl⟩ : syracuseStep 1997855 = 2996783) B2996783
theorem B1498207 : Blo 1330984 1498207 := bstep (se 1 (by rfl) ⟨1123655, by rfl⟩ : syracuseStep 1498207 = 2247311) B2247311
theorem B1686683 : Blo 1330984 1686683 := bstep (se 1 (by rfl) ⟨1265012, by rfl⟩ : syracuseStep 1686683 = 2530025) B2530025
theorem B2997575 : Blo 1330984 2997575 := bstep (se 1 (by rfl) ⟨2248181, by rfl⟩ : syracuseStep 2997575 = 4496363) B4496363
theorem B5053823 : Blo 1330984 5053823 := bstep (se 1 (by rfl) ⟨3790367, by rfl⟩ : syracuseStep 5053823 = 7580735) B7580735
theorem B43179581 : Blo 1330984 43179581 := bstep (se 3 (by rfl) ⟨8096171, by rfl⟩ : syracuseStep 43179581 = 16192343) B16192343
theorem B3792521 : Blo 1330984 3792521 := bstep (se 2 (by rfl) ⟨1422195, by rfl⟩ : syracuseStep 3792521 = 2844391) B2844391
theorem B1998491 : Blo 1330984 1998491 := bstep (se 1 (by rfl) ⟨1498868, by rfl⟩ : syracuseStep 1998491 = 2997737) B2997737
theorem B2998241 : Blo 1330984 2998241 := bstep (se 2 (by rfl) ⟨1124340, by rfl⟩ : syracuseStep 2998241 = 2248681) B2248681
theorem B22749173 : Blo 1330984 22749173 := bstep (se 5 (by rfl) ⟨1066367, by rfl⟩ : syracuseStep 22749173 = 2132735) B2132735
theorem B1998875 : Blo 1330984 1998875 := bstep (se 1 (by rfl) ⟨1499156, by rfl⟩ : syracuseStep 1998875 = 2998313) B2998313
theorem B4497551 : Blo 1330984 4497551 := bstep (se 1 (by rfl) ⟨3373163, by rfl⟩ : syracuseStep 4497551 = 6746327) B6746327
theorem B2842793 : Blo 1330984 2842793 := bstep (se 2 (by rfl) ⟨1066047, by rfl⟩ : syracuseStep 2842793 = 2132095) B2132095
theorem B41025793 : Blo 1330984 41025793 := bstep (se 2 (by rfl) ⟨15384672, by rfl⟩ : syracuseStep 41025793 = 30769345) B30769345
theorem B3793193 : Blo 1330984 3793193 := bstep (se 2 (by rfl) ⟨1422447, by rfl⟩ : syracuseStep 3793193 = 2844895) B2844895
theorem B4497821 : Blo 1330984 4497821 := bstep (se 3 (by rfl) ⟨843341, by rfl⟩ : syracuseStep 4497821 = 1686683) B1686683
theorem B443498935 : Blo 1330984 443498935 := bstep (se 1 (by rfl) ⟨332624201, by rfl⟩ : syracuseStep 443498935 = 665248403) B665248403
theorem B12796379 : Blo 1330984 12796379 := bstep (se 1 (by rfl) ⟨9597284, by rfl⟩ : syracuseStep 12796379 = 19194569) B19194569
theorem B1999343 : Blo 1330984 1999343 := bstep (se 1 (by rfl) ⟨1499507, by rfl⟩ : syracuseStep 1999343 = 2999015) B2999015
theorem B1999415 : Blo 1330984 1999415 := bstep (se 1 (by rfl) ⟨1499561, by rfl⟩ : syracuseStep 1999415 = 2999123) B2999123
theorem B2998943 : Blo 1330984 2998943 := bstep (se 1 (by rfl) ⟨2249207, by rfl⟩ : syracuseStep 2998943 = 4498415) B4498415
theorem B4555769 : Blo 1330984 4555769 := bstep (se 2 (by rfl) ⟨1708413, by rfl⟩ : syracuseStep 4555769 = 3416827) B3416827
theorem B6398975 : Blo 1330984 6398975 := bstep (se 1 (by rfl) ⟨4799231, by rfl⟩ : syracuseStep 6398975 = 9598463) B9598463
theorem B6743249 : Blo 1330984 6743249 := bstep (se 2 (by rfl) ⟨2528718, by rfl⟩ : syracuseStep 6743249 = 5057437) B5057437
theorem B48604481 : Blo 1330984 48604481 := bstep (se 2 (by rfl) ⟨18226680, by rfl⟩ : syracuseStep 48604481 = 36453361) B36453361
theorem B10118519 : Blo 1330984 10118519 := bstep (se 1 (by rfl) ⟨7588889, by rfl⟩ : syracuseStep 10118519 = 15177779) B15177779
theorem B4269469 : Blo 1330984 4269469 := bstep (se 3 (by rfl) ⟨800525, by rfl⟩ : syracuseStep 4269469 = 1601051) B1601051
theorem B4801999 : Blo 1330984 4801999 := bstep (se 1 (by rfl) ⟨3601499, by rfl⟩ : syracuseStep 4801999 = 7202999) B7202999
theorem B7202287 : Blo 1330984 7202287 := bstep (se 1 (by rfl) ⟨5401715, by rfl⟩ : syracuseStep 7202287 = 10803431) B10803431
theorem B28468921 : Blo 1330984 28468921 := bstep (se 2 (by rfl) ⟨10675845, by rfl⟩ : syracuseStep 28468921 = 21351691) B21351691
theorem B14403575 : Blo 1330984 14403575 := bstep (se 1 (by rfl) ⟨10802681, by rfl⟩ : syracuseStep 14403575 = 21605363) B21605363
theorem B3369215 : Blo 1330984 3369215 := bstep (se 1 (by rfl) ⟨2526911, by rfl⟩ : syracuseStep 3369215 = 5053823) B5053823
theorem B15166115 : Blo 1330984 15166115 := bstep (se 1 (by rfl) ⟨11374586, by rfl⟩ : syracuseStep 15166115 = 22749173) B22749173
theorem B2247547 : Blo 1330984 2247547 := bstep (se 1 (by rfl) ⟨1685660, by rfl⟩ : syracuseStep 2247547 = 3371321) B3371321
theorem B2526889 : Blo 1330984 2526889 := bstep (se 2 (by rfl) ⟨947583, by rfl⟩ : syracuseStep 2526889 = 1895167) B1895167
theorem B2248411 : Blo 1330984 2248411 := bstep (se 1 (by rfl) ⟨1686308, by rfl⟩ : syracuseStep 2248411 = 3372617) B3372617
theorem B38424293 : Blo 1330984 38424293 := bstep (se 4 (by rfl) ⟨3602277, by rfl⟩ : syracuseStep 38424293 = 7204555) B7204555
theorem B14405651 : Blo 1330984 14405651 := bstep (se 1 (by rfl) ⟨10804238, by rfl⟩ : syracuseStep 14405651 = 21608477) B21608477
theorem B1331423 : Blo 1330984 1331423 := bstep (se 1 (by rfl) ⟨998567, by rfl⟩ : syracuseStep 1331423 = 1997135) B1997135
theorem B2249039 : Blo 1330984 2249039 := bstep (se 1 (by rfl) ⟨1686779, by rfl⟩ : syracuseStep 2249039 = 3373559) B3373559
theorem B17068441 : Blo 1330984 17068441 := bstep (se 2 (by rfl) ⟨6400665, by rfl⟩ : syracuseStep 17068441 = 12801331) B12801331
theorem B10113659 : Blo 1330984 10113659 := bstep (se 1 (by rfl) ⟨7585244, by rfl⟩ : syracuseStep 10113659 = 15170489) B15170489
theorem B2249383 : Blo 1330984 2249383 := bstep (se 1 (by rfl) ⟨1687037, by rfl⟩ : syracuseStep 2249383 = 3374075) B3374075
theorem B1331903 : Blo 1330984 1331903 := bstep (se 1 (by rfl) ⟨998927, by rfl⟩ : syracuseStep 1331903 = 1997855) B1997855
theorem B11383577 : Blo 1330984 11383577 := bstep (se 2 (by rfl) ⟨4268841, by rfl⟩ : syracuseStep 11383577 = 8537683) B8537683
theorem B3371807 : Blo 1330984 3371807 := bstep (se 1 (by rfl) ⟨2528855, by rfl⟩ : syracuseStep 3371807 = 5057711) B5057711
theorem B7582511 : Blo 1330984 7582511 := bstep (se 1 (by rfl) ⟨5686883, by rfl⟩ : syracuseStep 7582511 = 11373767) B11373767
theorem B3601199 : Blo 1330984 3601199 := bstep (se 1 (by rfl) ⟨2700899, by rfl⟩ : syracuseStep 3601199 = 5401799) B5401799
theorem B2528347 : Blo 1330984 2528347 := bstep (se 1 (by rfl) ⟨1896260, by rfl⟩ : syracuseStep 2528347 = 3792521) B3792521
theorem B1332327 : Blo 1330984 1332327 := bstep (se 1 (by rfl) ⟨999245, by rfl⟩ : syracuseStep 1332327 = 1998491) B1998491
theorem B43226297 : Blo 1330984 43226297 := bstep (se 2 (by rfl) ⟨16209861, by rfl⟩ : syracuseStep 43226297 = 32419723) B32419723
theorem B1332783 : Blo 1330984 1332783 := bstep (se 1 (by rfl) ⟨999587, by rfl⟩ : syracuseStep 1332783 = 1999175) B1999175
theorem B8533583 : Blo 1330984 8533583 := bstep (se 1 (by rfl) ⟨6400187, by rfl⟩ : syracuseStep 8533583 = 12800375) B12800375
theorem B4495229 : Blo 1330984 4495229 := bstep (se 3 (by rfl) ⟨842855, by rfl⟩ : syracuseStep 4495229 = 1685711) B1685711
theorem B3791063 : Blo 1330984 3791063 := bstep (se 1 (by rfl) ⟨2843297, by rfl⟩ : syracuseStep 3791063 = 5686595) B5686595
theorem B1997051 : Blo 1330984 1997051 := bstep (se 1 (by rfl) ⟨1497788, by rfl⟩ : syracuseStep 1997051 = 2995577) B2995577
theorem B1997519 : Blo 1330984 1997519 := bstep (se 1 (by rfl) ⟨1498139, by rfl⟩ : syracuseStep 1997519 = 2996279) B2996279
theorem B1997567 : Blo 1330984 1997567 := bstep (se 1 (by rfl) ⟨1498175, by rfl⟩ : syracuseStep 1997567 = 2996351) B2996351
theorem B1997609 : Blo 1330984 1997609 := bstep (se 2 (by rfl) ⟨749103, by rfl⟩ : syracuseStep 1997609 = 1498207) B1498207
theorem B115145549 : Blo 1330984 115145549 := bstep (se 3 (by rfl) ⟨21589790, by rfl⟩ : syracuseStep 115145549 = 43179581) B43179581
theorem B1998143 : Blo 1330984 1998143 := bstep (se 1 (by rfl) ⟨1498607, by rfl⟩ : syracuseStep 1998143 = 2997215) B2997215
theorem B10108313 : Blo 1330984 10108313 := bstep (se 2 (by rfl) ⟨3790617, by rfl⟩ : syracuseStep 10108313 = 7581235) B7581235
theorem B1998383 : Blo 1330984 1998383 := bstep (se 1 (by rfl) ⟨1498787, by rfl⟩ : syracuseStep 1998383 = 2997575) B2997575
theorem B1998827 : Blo 1330984 1998827 := bstep (se 1 (by rfl) ⟨1499120, by rfl⟩ : syracuseStep 1998827 = 2998241) B2998241
theorem B2998367 : Blo 1330984 2998367 := bstep (se 1 (by rfl) ⟨2248775, by rfl⟩ : syracuseStep 2998367 = 4497551) B4497551
theorem B1499359 : Blo 1330984 1499359 := bstep (se 1 (by rfl) ⟨1124519, by rfl⟩ : syracuseStep 1499359 = 2249039) B2249039
theorem B2998547 : Blo 1330984 2998547 := bstep (se 1 (by rfl) ⟨2248910, by rfl⟩ : syracuseStep 2998547 = 4497821) B4497821
theorem B6742439 : Blo 1330984 6742439 := bstep (se 1 (by rfl) ⟨5056829, by rfl⟩ : syracuseStep 6742439 = 10113659) B10113659
theorem B1999295 : Blo 1330984 1999295 := bstep (se 1 (by rfl) ⟨1499471, by rfl⟩ : syracuseStep 1999295 = 2998943) B2998943
theorem B5055007 : Blo 1330984 5055007 := bstep (se 1 (by rfl) ⟨3791255, by rfl⟩ : syracuseStep 5055007 = 7582511) B7582511
theorem B2400799 : Blo 1330984 2400799 := bstep (se 1 (by rfl) ⟨1800599, by rfl⟩ : syracuseStep 2400799 = 3601199) B3601199
theorem B22757921 : Blo 1330984 22757921 := bstep (se 2 (by rfl) ⟨8534220, by rfl⟩ : syracuseStep 22757921 = 17068441) B17068441
theorem B591331913 : Blo 1330984 591331913 := bstep (se 2 (by rfl) ⟨221749467, by rfl⟩ : syracuseStep 591331913 = 443498935) B443498935
theorem B2999177 : Blo 1330984 2999177 := bstep (se 2 (by rfl) ⟨1124691, by rfl⟩ : syracuseStep 2999177 = 2249383) B2249383
theorem B9602383 : Blo 1330984 9602383 := bstep (se 1 (by rfl) ⟨7201787, by rfl⟩ : syracuseStep 9602383 = 14403575) B14403575
theorem B2246143 : Blo 1330984 2246143 := bstep (se 1 (by rfl) ⟨1684607, by rfl⟩ : syracuseStep 2246143 = 3369215) B3369215
theorem B10110743 : Blo 1330984 10110743 := bstep (se 1 (by rfl) ⟨7583057, by rfl⟩ : syracuseStep 10110743 = 15166115) B15166115
theorem B9603049 : Blo 1330984 9603049 := bstep (se 2 (by rfl) ⟨3601143, by rfl⟩ : syracuseStep 9603049 = 7202287) B7202287
theorem B3369185 : Blo 1330984 3369185 := bstep (se 2 (by rfl) ⟨1263444, by rfl⟩ : syracuseStep 3369185 = 2526889) B2526889
theorem B9603767 : Blo 1330984 9603767 := bstep (se 1 (by rfl) ⟨7202825, by rfl⟩ : syracuseStep 9603767 = 14405651) B14405651
theorem B1895195 : Blo 1330984 1895195 := bstep (se 1 (by rfl) ⟨1421396, by rfl⟩ : syracuseStep 1895195 = 2842793) B2842793
theorem B8530919 : Blo 1330984 8530919 := bstep (se 1 (by rfl) ⟨6398189, by rfl⟩ : syracuseStep 8530919 = 12796379) B12796379
theorem B54701057 : Blo 1330984 54701057 := bstep (se 2 (by rfl) ⟨20512896, by rfl⟩ : syracuseStep 54701057 = 41025793) B41025793
theorem B7589051 : Blo 1330984 7589051 := bstep (se 1 (by rfl) ⟨5691788, by rfl⟩ : syracuseStep 7589051 = 11383577) B11383577
theorem B2247871 : Blo 1330984 2247871 := bstep (se 1 (by rfl) ⟨1685903, by rfl⟩ : syracuseStep 2247871 = 3371807) B3371807
theorem B32402987 : Blo 1330984 32402987 := bstep (se 1 (by rfl) ⟨24302240, by rfl⟩ : syracuseStep 32402987 = 48604481) B48604481
theorem B6745679 : Blo 1330984 6745679 := bstep (se 1 (by rfl) ⟨5059259, by rfl⟩ : syracuseStep 6745679 = 10118519) B10118519
theorem B5689055 : Blo 1330984 5689055 := bstep (se 1 (by rfl) ⟨4266791, by rfl⟩ : syracuseStep 5689055 = 8533583) B8533583
theorem B3371129 : Blo 1330984 3371129 := bstep (se 2 (by rfl) ⟨1264173, by rfl⟩ : syracuseStep 3371129 = 2528347) B2528347
theorem B2527375 : Blo 1330984 2527375 := bstep (se 1 (by rfl) ⟨1895531, by rfl⟩ : syracuseStep 2527375 = 3791063) B3791063
theorem B1331367 : Blo 1330984 1331367 := bstep (se 1 (by rfl) ⟨998525, by rfl⟩ : syracuseStep 1331367 = 1997051) B1997051
theorem B1331679 : Blo 1330984 1331679 := bstep (se 1 (by rfl) ⟨998759, by rfl⟩ : syracuseStep 1331679 = 1997519) B1997519
theorem B1331711 : Blo 1330984 1331711 := bstep (se 1 (by rfl) ⟨998783, by rfl⟩ : syracuseStep 1331711 = 1997567) B1997567
theorem B1331739 : Blo 1330984 1331739 := bstep (se 1 (by rfl) ⟨998804, by rfl⟩ : syracuseStep 1331739 = 1997609) B1997609
theorem B76763699 : Blo 1330984 76763699 := bstep (se 1 (by rfl) ⟨57572774, by rfl⟩ : syracuseStep 76763699 = 115145549) B115145549
theorem B6402665 : Blo 1330984 6402665 := bstep (se 2 (by rfl) ⟨2400999, by rfl⟩ : syracuseStep 6402665 = 4801999) B4801999
theorem B1332095 : Blo 1330984 1332095 := bstep (se 1 (by rfl) ⟨999071, by rfl⟩ : syracuseStep 1332095 = 1998143) B1998143
theorem B37958561 : Blo 1330984 37958561 := bstep (se 2 (by rfl) ⟨14234460, by rfl⟩ : syracuseStep 37958561 = 28468921) B28468921
theorem B6738875 : Blo 1330984 6738875 := bstep (se 1 (by rfl) ⟨5054156, by rfl⟩ : syracuseStep 6738875 = 10108313) B10108313
theorem B1332255 : Blo 1330984 1332255 := bstep (se 1 (by rfl) ⟨999191, by rfl⟩ : syracuseStep 1332255 = 1998383) B1998383
theorem B1332551 : Blo 1330984 1332551 := bstep (se 1 (by rfl) ⟨999413, by rfl⟩ : syracuseStep 1332551 = 1998827) B1998827
theorem B1332583 : Blo 1330984 1332583 := bstep (se 1 (by rfl) ⟨999437, by rfl⟩ : syracuseStep 1332583 = 1998875) B1998875
theorem B2528795 : Blo 1330984 2528795 := bstep (se 1 (by rfl) ⟨1896596, by rfl⟩ : syracuseStep 2528795 = 3793193) B3793193
theorem B1332895 : Blo 1330984 1332895 := bstep (se 1 (by rfl) ⟨999671, by rfl⟩ : syracuseStep 1332895 = 1999343) B1999343
theorem B1332943 : Blo 1330984 1332943 := bstep (se 1 (by rfl) ⟨999707, by rfl⟩ : syracuseStep 1332943 = 1999415) B1999415
theorem B4265983 : Blo 1330984 4265983 := bstep (se 1 (by rfl) ⟨3199487, by rfl⟩ : syracuseStep 4265983 = 6398975) B6398975
theorem B28817531 : Blo 1330984 28817531 := bstep (se 1 (by rfl) ⟨21613148, by rfl⟩ : syracuseStep 28817531 = 43226297) B43226297
theorem B4495499 : Blo 1330984 4495499 := bstep (se 1 (by rfl) ⟨3371624, by rfl⟩ : syracuseStep 4495499 = 6743249) B6743249
theorem B2996729 : Blo 1330984 2996729 := bstep (se 2 (by rfl) ⟨1123773, by rfl⟩ : syracuseStep 2996729 = 2247547) B2247547
theorem B2996819 : Blo 1330984 2996819 := bstep (se 1 (by rfl) ⟨2247614, by rfl⟩ : syracuseStep 2996819 = 4495229) B4495229
theorem B5692625 : Blo 1330984 5692625 := bstep (se 2 (by rfl) ⟨2134734, by rfl⟩ : syracuseStep 5692625 = 4269469) B4269469
theorem B2997881 : Blo 1330984 2997881 := bstep (se 2 (by rfl) ⟨1124205, by rfl⟩ : syracuseStep 2997881 = 2248411) B2248411
theorem B25616195 : Blo 1330984 25616195 := bstep (se 1 (by rfl) ⟨19212146, by rfl⟩ : syracuseStep 25616195 = 38424293) B38424293
theorem B12148717 : Blo 1330984 12148717 := bstep (se 3 (by rfl) ⟨2277884, by rfl⟩ : syracuseStep 12148717 = 4555769) B4555769
theorem B1998911 : Blo 1330984 1998911 := bstep (se 1 (by rfl) ⟨1499183, by rfl⟩ : syracuseStep 1998911 = 2998367) B2998367
theorem B1999031 : Blo 1330984 1999031 := bstep (se 1 (by rfl) ⟨1499273, by rfl⟩ : syracuseStep 1999031 = 2998547) B2998547
theorem B1999145 : Blo 1330984 1999145 := bstep (se 2 (by rfl) ⟨749679, by rfl⟩ : syracuseStep 1999145 = 1499359) B1499359
theorem B15171947 : Blo 1330984 15171947 := bstep (se 1 (by rfl) ⟨11378960, by rfl⟩ : syracuseStep 15171947 = 22757921) B22757921
theorem B51175799 : Blo 1330984 51175799 := bstep (se 1 (by rfl) ⟨38381849, by rfl⟩ : syracuseStep 51175799 = 76763699) B76763699
theorem B1999451 : Blo 1330984 1999451 := bstep (se 1 (by rfl) ⟨1499588, by rfl⟩ : syracuseStep 1999451 = 2999177) B2999177
theorem B25305707 : Blo 1330984 25305707 := bstep (se 1 (by rfl) ⟨18979280, by rfl⟩ : syracuseStep 25305707 = 37958561) B37958561
theorem B19211687 : Blo 1330984 19211687 := bstep (se 1 (by rfl) ⟨14408765, by rfl⟩ : syracuseStep 19211687 = 28817531) B28817531
theorem B2246123 : Blo 1330984 2246123 := bstep (se 1 (by rfl) ⟨1684592, by rfl⟩ : syracuseStep 2246123 = 3369185) B3369185
theorem B17073773 : Blo 1330984 17073773 := bstep (se 3 (by rfl) ⟨3201332, by rfl⟩ : syracuseStep 17073773 = 6402665) B6402665
theorem B5687279 : Blo 1330984 5687279 := bstep (se 1 (by rfl) ⟨4265459, by rfl⟩ : syracuseStep 5687279 = 8530919) B8530919
theorem B3795083 : Blo 1330984 3795083 := bstep (se 1 (by rfl) ⟨2846312, by rfl⟩ : syracuseStep 3795083 = 5692625) B5692625
theorem B16198289 : Blo 1330984 16198289 := bstep (se 2 (by rfl) ⟨6074358, by rfl⟩ : syracuseStep 16198289 = 12148717) B12148717
theorem B5687977 : Blo 1330984 5687977 := bstep (se 2 (by rfl) ⟨2132991, by rfl⟩ : syracuseStep 5687977 = 4265983) B4265983
theorem B2247419 : Blo 1330984 2247419 := bstep (se 1 (by rfl) ⟨1685564, by rfl⟩ : syracuseStep 2247419 = 3371129) B3371129
theorem B3369833 : Blo 1330984 3369833 := bstep (se 2 (by rfl) ⟨1263687, by rfl⟩ : syracuseStep 3369833 = 2527375) B2527375
theorem B4492583 : Blo 1330984 4492583 := bstep (se 1 (by rfl) ⟨3369437, by rfl⟩ : syracuseStep 4492583 = 6738875) B6738875
theorem B6402511 : Blo 1330984 6402511 := bstep (se 1 (by rfl) ⟨4801883, by rfl⟩ : syracuseStep 6402511 = 9603767) B9603767
theorem B2994857 : Blo 1330984 2994857 := bstep (se 2 (by rfl) ⟨1123071, by rfl⟩ : syracuseStep 2994857 = 2246143) B2246143
theorem B36467371 : Blo 1330984 36467371 := bstep (se 1 (by rfl) ⟨27350528, by rfl⟩ : syracuseStep 36467371 = 54701057) B54701057
theorem B5059367 : Blo 1330984 5059367 := bstep (se 1 (by rfl) ⟨3794525, by rfl⟩ : syracuseStep 5059367 = 7589051) B7589051
theorem B17077463 : Blo 1330984 17077463 := bstep (se 1 (by rfl) ⟨12808097, by rfl⟩ : syracuseStep 17077463 = 25616195) B25616195
theorem B4494959 : Blo 1330984 4494959 := bstep (se 1 (by rfl) ⟨3371219, by rfl⟩ : syracuseStep 4494959 = 6742439) B6742439
theorem B1332863 : Blo 1330984 1332863 := bstep (se 1 (by rfl) ⟨999647, by rfl⟩ : syracuseStep 1332863 = 1999295) B1999295
theorem B394221275 : Blo 1330984 394221275 := bstep (se 1 (by rfl) ⟨295665956, by rfl⟩ : syracuseStep 394221275 = 591331913) B591331913
theorem B6740009 : Blo 1330984 6740009 := bstep (se 2 (by rfl) ⟨2527503, by rfl⟩ : syracuseStep 6740009 = 5055007) B5055007
theorem B3201065 : Blo 1330984 3201065 := bstep (se 2 (by rfl) ⟨1200399, by rfl⟩ : syracuseStep 3201065 = 2400799) B2400799
theorem B1685863 : Blo 1330984 1685863 := bstep (se 1 (by rfl) ⟨1264397, by rfl⟩ : syracuseStep 1685863 = 2528795) B2528795
theorem B6740495 : Blo 1330984 6740495 := bstep (se 1 (by rfl) ⟨5055371, by rfl⟩ : syracuseStep 6740495 = 10110743) B10110743
theorem B2996999 : Blo 1330984 2996999 := bstep (se 1 (by rfl) ⟨2247749, by rfl⟩ : syracuseStep 2996999 = 4495499) B4495499
theorem B2997161 : Blo 1330984 2997161 := bstep (se 2 (by rfl) ⟨1123935, by rfl⟩ : syracuseStep 2997161 = 2247871) B2247871
theorem B1997819 : Blo 1330984 1997819 := bstep (se 1 (by rfl) ⟨1498364, by rfl⟩ : syracuseStep 1997819 = 2996729) B2996729
theorem B1997879 : Blo 1330984 1997879 := bstep (se 1 (by rfl) ⟨1498409, by rfl⟩ : syracuseStep 1997879 = 2996819) B2996819
theorem B12803177 : Blo 1330984 12803177 := bstep (se 2 (by rfl) ⟨4801191, by rfl⟩ : syracuseStep 12803177 = 9602383) B9602383
theorem B5053853 : Blo 1330984 5053853 := bstep (se 3 (by rfl) ⟨947597, by rfl⟩ : syracuseStep 5053853 = 1895195) B1895195
theorem B21601991 : Blo 1330984 21601991 := bstep (se 1 (by rfl) ⟨16201493, by rfl⟩ : syracuseStep 21601991 = 32402987) B32402987
theorem B4497119 : Blo 1330984 4497119 := bstep (se 1 (by rfl) ⟨3372839, by rfl⟩ : syracuseStep 4497119 = 6745679) B6745679
theorem B1998587 : Blo 1330984 1998587 := bstep (se 1 (by rfl) ⟨1498940, by rfl⟩ : syracuseStep 1998587 = 2997881) B2997881
theorem B3792703 : Blo 1330984 3792703 := bstep (se 1 (by rfl) ⟨2844527, by rfl⟩ : syracuseStep 3792703 = 5689055) B5689055
theorem B12804065 : Blo 1330984 12804065 := bstep (se 2 (by rfl) ⟨4801524, by rfl⟩ : syracuseStep 12804065 = 9603049) B9603049
theorem B8536681 : Blo 1330984 8536681 := bstep (se 2 (by rfl) ⟨3201255, by rfl⟩ : syracuseStep 8536681 = 6402511) B6402511
theorem B10798859 : Blo 1330984 10798859 := bstep (se 1 (by rfl) ⟨8099144, by rfl⟩ : syracuseStep 10798859 = 16198289) B16198289
theorem B2246555 : Blo 1330984 2246555 := bstep (se 1 (by rfl) ⟨1684916, by rfl⟩ : syracuseStep 2246555 = 3369833) B3369833
theorem B3369235 : Blo 1330984 3369235 := bstep (se 1 (by rfl) ⟨2526926, by rfl⟩ : syracuseStep 3369235 = 5053853) B5053853
theorem B5056937 : Blo 1330984 5056937 := bstep (se 2 (by rfl) ⟨1896351, by rfl⟩ : syracuseStep 5056937 = 3792703) B3792703
theorem B2247817 : Blo 1330984 2247817 := bstep (se 2 (by rfl) ⟨842931, by rfl⟩ : syracuseStep 2247817 = 1685863) B1685863
theorem B48623161 : Blo 1330984 48623161 := bstep (se 2 (by rfl) ⟨18233685, by rfl⟩ : syracuseStep 48623161 = 36467371) B36467371
theorem B12807791 : Blo 1330984 12807791 := bstep (se 1 (by rfl) ⟨9605843, by rfl⟩ : syracuseStep 12807791 = 19211687) B19211687
theorem B11382515 : Blo 1330984 11382515 := bstep (se 1 (by rfl) ⟨8536886, by rfl⟩ : syracuseStep 11382515 = 17073773) B17073773
theorem B4493339 : Blo 1330984 4493339 := bstep (se 1 (by rfl) ⟨3370004, by rfl⟩ : syracuseStep 4493339 = 6740009) B6740009
theorem B2134043 : Blo 1330984 2134043 := bstep (se 1 (by rfl) ⟨1600532, by rfl⟩ : syracuseStep 2134043 = 3201065) B3201065
theorem B67481885 : Blo 1330984 67481885 := bstep (se 3 (by rfl) ⟨12652853, by rfl⟩ : syracuseStep 67481885 = 25305707) B25305707
theorem B4493663 : Blo 1330984 4493663 := bstep (se 1 (by rfl) ⟨3370247, by rfl⟩ : syracuseStep 4493663 = 6740495) B6740495
theorem B1331879 : Blo 1330984 1331879 := bstep (se 1 (by rfl) ⟨998909, by rfl⟩ : syracuseStep 1331879 = 1997819) B1997819
theorem B1331919 : Blo 1330984 1331919 := bstep (se 1 (by rfl) ⟨998939, by rfl⟩ : syracuseStep 1331919 = 1997879) B1997879
theorem B2995055 : Blo 1330984 2995055 := bstep (se 1 (by rfl) ⟨2246291, by rfl⟩ : syracuseStep 2995055 = 4492583) B4492583
theorem B1332391 : Blo 1330984 1332391 := bstep (se 1 (by rfl) ⟨999293, by rfl⟩ : syracuseStep 1332391 = 1998587) B1998587
theorem B1332607 : Blo 1330984 1332607 := bstep (se 1 (by rfl) ⟨999455, by rfl⟩ : syracuseStep 1332607 = 1998911) B1998911
theorem B1332687 : Blo 1330984 1332687 := bstep (se 1 (by rfl) ⟨999515, by rfl⟩ : syracuseStep 1332687 = 1999031) B1999031
theorem B1332763 : Blo 1330984 1332763 := bstep (se 1 (by rfl) ⟨999572, by rfl⟩ : syracuseStep 1332763 = 1999145) B1999145
theorem B10114631 : Blo 1330984 10114631 := bstep (se 1 (by rfl) ⟨7585973, by rfl⟩ : syracuseStep 10114631 = 15171947) B15171947
theorem B34117199 : Blo 1330984 34117199 := bstep (se 1 (by rfl) ⟨25587899, by rfl⟩ : syracuseStep 34117199 = 51175799) B51175799
theorem B1332967 : Blo 1330984 1332967 := bstep (se 1 (by rfl) ⟨999725, by rfl⟩ : syracuseStep 1332967 = 1999451) B1999451
theorem B1996571 : Blo 1330984 1996571 := bstep (se 1 (by rfl) ⟨1497428, by rfl⟩ : syracuseStep 1996571 = 2994857) B2994857
theorem B3372911 : Blo 1330984 3372911 := bstep (se 1 (by rfl) ⟨2529683, by rfl⟩ : syracuseStep 3372911 = 5059367) B5059367
theorem B11384975 : Blo 1330984 11384975 := bstep (se 1 (by rfl) ⟨8538731, by rfl⟩ : syracuseStep 11384975 = 17077463) B17077463
theorem B7583969 : Blo 1330984 7583969 := bstep (se 2 (by rfl) ⟨2843988, by rfl⟩ : syracuseStep 7583969 = 5687977) B5687977
theorem B1497415 : Blo 1330984 1497415 := bstep (se 1 (by rfl) ⟨1123061, by rfl⟩ : syracuseStep 1497415 = 2246123) B2246123
theorem B2996639 : Blo 1330984 2996639 := bstep (se 1 (by rfl) ⟨2247479, by rfl⟩ : syracuseStep 2996639 = 4494959) B4494959
theorem B262814183 : Blo 1330984 262814183 := bstep (se 1 (by rfl) ⟨197110637, by rfl⟩ : syracuseStep 262814183 = 394221275) B394221275
theorem B3791519 : Blo 1330984 3791519 := bstep (se 1 (by rfl) ⟨2843639, by rfl⟩ : syracuseStep 3791519 = 5687279) B5687279
theorem B2530055 : Blo 1330984 2530055 := bstep (se 1 (by rfl) ⟨1897541, by rfl⟩ : syracuseStep 2530055 = 3795083) B3795083
theorem B1498279 : Blo 1330984 1498279 := bstep (se 1 (by rfl) ⟨1123709, by rfl⟩ : syracuseStep 1498279 = 2247419) B2247419
theorem B1997999 : Blo 1330984 1997999 := bstep (se 1 (by rfl) ⟨1498499, by rfl⟩ : syracuseStep 1997999 = 2996999) B2996999
theorem B1998107 : Blo 1330984 1998107 := bstep (se 1 (by rfl) ⟨1498580, by rfl⟩ : syracuseStep 1998107 = 2997161) B2997161
theorem B8535451 : Blo 1330984 8535451 := bstep (se 1 (by rfl) ⟨6401588, by rfl⟩ : syracuseStep 8535451 = 12803177) B12803177
theorem B14401327 : Blo 1330984 14401327 := bstep (se 1 (by rfl) ⟨10800995, by rfl⟩ : syracuseStep 14401327 = 21601991) B21601991
theorem B2998079 : Blo 1330984 2998079 := bstep (se 1 (by rfl) ⟨2248559, by rfl⟩ : syracuseStep 2998079 = 4497119) B4497119
theorem B8536043 : Blo 1330984 8536043 := bstep (se 1 (by rfl) ⟨6402032, by rfl⟩ : syracuseStep 8536043 = 12804065) B12804065
theorem B6743087 : Blo 1330984 6743087 := bstep (se 1 (by rfl) ⟨5057315, by rfl⟩ : syracuseStep 6743087 = 10114631) B10114631
theorem B5055979 : Blo 1330984 5055979 := bstep (se 1 (by rfl) ⟨3791984, by rfl⟩ : syracuseStep 5055979 = 7583969) B7583969
theorem B11380601 : Blo 1330984 11380601 := bstep (se 2 (by rfl) ⟨4267725, by rfl⟩ : syracuseStep 11380601 = 8535451) B8535451
theorem B8538527 : Blo 1330984 8538527 := bstep (se 1 (by rfl) ⟨6403895, by rfl⟩ : syracuseStep 8538527 = 12807791) B12807791
theorem B7588343 : Blo 1330984 7588343 := bstep (se 1 (by rfl) ⟨5691257, by rfl⟩ : syracuseStep 7588343 = 11382515) B11382515
theorem B4492313 : Blo 1330984 4492313 := bstep (se 2 (by rfl) ⟨1684617, by rfl⟩ : syracuseStep 4492313 = 3369235) B3369235
theorem B11382241 : Blo 1330984 11382241 := bstep (se 2 (by rfl) ⟨4268340, by rfl⟩ : syracuseStep 11382241 = 8536681) B8536681
theorem B22744799 : Blo 1330984 22744799 := bstep (se 1 (by rfl) ⟨17058599, by rfl⟩ : syracuseStep 22744799 = 34117199) B34117199
theorem B1331047 : Blo 1330984 1331047 := bstep (se 1 (by rfl) ⟨998285, by rfl⟩ : syracuseStep 1331047 = 1996571) B1996571
theorem B2248607 : Blo 1330984 2248607 := bstep (se 1 (by rfl) ⟨1686455, by rfl⟩ : syracuseStep 2248607 = 3372911) B3372911
theorem B7589983 : Blo 1330984 7589983 := bstep (se 1 (by rfl) ⟨5692487, by rfl⟩ : syracuseStep 7589983 = 11384975) B11384975
theorem B3371291 : Blo 1330984 3371291 := bstep (se 1 (by rfl) ⟨2528468, by rfl⟩ : syracuseStep 3371291 = 5056937) B5056937
theorem B2527679 : Blo 1330984 2527679 := bstep (se 1 (by rfl) ⟨1895759, by rfl⟩ : syracuseStep 2527679 = 3791519) B3791519
theorem B6746813 : Blo 1330984 6746813 := bstep (se 3 (by rfl) ⟨1265027, by rfl⟩ : syracuseStep 6746813 = 2530055) B2530055
theorem B1331999 : Blo 1330984 1331999 := bstep (se 1 (by rfl) ⟨998999, by rfl⟩ : syracuseStep 1331999 = 1997999) B1997999
theorem B1332071 : Blo 1330984 1332071 := bstep (se 1 (by rfl) ⟨999053, by rfl⟩ : syracuseStep 1332071 = 1998107) B1998107
theorem B5690695 : Blo 1330984 5690695 := bstep (se 1 (by rfl) ⟨4268021, by rfl⟩ : syracuseStep 5690695 = 8536043) B8536043
theorem B2995559 : Blo 1330984 2995559 := bstep (se 1 (by rfl) ⟨2246669, by rfl⟩ : syracuseStep 2995559 = 4493339) B4493339
theorem B1422695 : Blo 1330984 1422695 := bstep (se 1 (by rfl) ⟨1067021, by rfl⟩ : syracuseStep 1422695 = 2134043) B2134043
theorem B44987923 : Blo 1330984 44987923 := bstep (se 1 (by rfl) ⟨33740942, by rfl⟩ : syracuseStep 44987923 = 67481885) B67481885
theorem B2995775 : Blo 1330984 2995775 := bstep (se 1 (by rfl) ⟨2246831, by rfl⟩ : syracuseStep 2995775 = 4493663) B4493663
theorem B1996553 : Blo 1330984 1996553 := bstep (se 2 (by rfl) ⟨748707, by rfl⟩ : syracuseStep 1996553 = 1497415) B1497415
theorem B1996703 : Blo 1330984 1996703 := bstep (se 1 (by rfl) ⟨1497527, by rfl⟩ : syracuseStep 1996703 = 2995055) B2995055
theorem B7199239 : Blo 1330984 7199239 := bstep (se 1 (by rfl) ⟨5399429, by rfl⟩ : syracuseStep 7199239 = 10798859) B10798859
theorem B1497703 : Blo 1330984 1497703 := bstep (se 1 (by rfl) ⟨1123277, by rfl⟩ : syracuseStep 1497703 = 2246555) B2246555
theorem B2997089 : Blo 1330984 2997089 := bstep (se 2 (by rfl) ⟨1123908, by rfl⟩ : syracuseStep 2997089 = 2247817) B2247817
theorem B1997705 : Blo 1330984 1997705 := bstep (se 2 (by rfl) ⟨749139, by rfl⟩ : syracuseStep 1997705 = 1498279) B1498279
theorem B1997759 : Blo 1330984 1997759 := bstep (se 1 (by rfl) ⟨1498319, by rfl⟩ : syracuseStep 1997759 = 2996639) B2996639
theorem B175209455 : Blo 1330984 175209455 := bstep (se 1 (by rfl) ⟨131407091, by rfl⟩ : syracuseStep 175209455 = 262814183) B262814183
theorem B64830881 : Blo 1330984 64830881 := bstep (se 2 (by rfl) ⟨24311580, by rfl⟩ : syracuseStep 64830881 = 48623161) B48623161
theorem B19201769 : Blo 1330984 19201769 := bstep (se 2 (by rfl) ⟨7200663, by rfl⟩ : syracuseStep 19201769 = 14401327) B14401327
theorem B1998719 : Blo 1330984 1998719 := bstep (se 1 (by rfl) ⟨1499039, by rfl⟩ : syracuseStep 1998719 = 2998079) B2998079
theorem B4497875 : Blo 1330984 4497875 := bstep (se 1 (by rfl) ⟨3373406, by rfl⟩ : syracuseStep 4497875 = 6746813) B6746813
theorem B3793853 : Blo 1330984 3793853 := bstep (se 3 (by rfl) ⟨711347, by rfl⟩ : syracuseStep 3793853 = 1422695) B1422695
theorem B7587067 : Blo 1330984 7587067 := bstep (se 1 (by rfl) ⟨5690300, by rfl⟩ : syracuseStep 7587067 = 11380601) B11380601
theorem B7587593 : Blo 1330984 7587593 := bstep (se 2 (by rfl) ⟨2845347, by rfl⟩ : syracuseStep 7587593 = 5690695) B5690695
theorem B59983897 : Blo 1330984 59983897 := bstep (se 2 (by rfl) ⟨22493961, by rfl⟩ : syracuseStep 59983897 = 44987923) B44987923
theorem B10119977 : Blo 1330984 10119977 := bstep (se 2 (by rfl) ⟨3794991, by rfl⟩ : syracuseStep 10119977 = 7589983) B7589983
theorem B2247527 : Blo 1330984 2247527 := bstep (se 1 (by rfl) ⟨1685645, by rfl⟩ : syracuseStep 2247527 = 3371291) B3371291
theorem B1331035 : Blo 1330984 1331035 := bstep (se 1 (by rfl) ⟨998276, by rfl⟩ : syracuseStep 1331035 = 1996553) B1996553
theorem B1331135 : Blo 1330984 1331135 := bstep (se 1 (by rfl) ⟨998351, by rfl⟩ : syracuseStep 1331135 = 1996703) B1996703
theorem B5058895 : Blo 1330984 5058895 := bstep (se 1 (by rfl) ⟨3794171, by rfl⟩ : syracuseStep 5058895 = 7588343) B7588343
theorem B1331803 : Blo 1330984 1331803 := bstep (se 1 (by rfl) ⟨998852, by rfl⟩ : syracuseStep 1331803 = 1997705) B1997705
theorem B1331839 : Blo 1330984 1331839 := bstep (se 1 (by rfl) ⟨998879, by rfl⟩ : syracuseStep 1331839 = 1997759) B1997759
theorem B15176321 : Blo 1330984 15176321 := bstep (se 2 (by rfl) ⟨5691120, by rfl⟩ : syracuseStep 15176321 = 11382241) B11382241
theorem B116806303 : Blo 1330984 116806303 := bstep (se 1 (by rfl) ⟨87604727, by rfl⟩ : syracuseStep 116806303 = 175209455) B175209455
theorem B2994875 : Blo 1330984 2994875 := bstep (se 1 (by rfl) ⟨2246156, by rfl⟩ : syracuseStep 2994875 = 4492313) B4492313
theorem B12801179 : Blo 1330984 12801179 := bstep (se 1 (by rfl) ⟨9600884, by rfl⟩ : syracuseStep 12801179 = 19201769) B19201769
theorem B1332479 : Blo 1330984 1332479 := bstep (se 1 (by rfl) ⟨999359, by rfl⟩ : syracuseStep 1332479 = 1998719) B1998719
theorem B1685119 : Blo 1330984 1685119 := bstep (se 1 (by rfl) ⟨1263839, by rfl⟩ : syracuseStep 1685119 = 2527679) B2527679
theorem B9598985 : Blo 1330984 9598985 := bstep (se 2 (by rfl) ⟨3599619, by rfl⟩ : syracuseStep 9598985 = 7199239) B7199239
theorem B4495391 : Blo 1330984 4495391 := bstep (se 1 (by rfl) ⟨3371543, by rfl⟩ : syracuseStep 4495391 = 6743087) B6743087
theorem B1996937 : Blo 1330984 1996937 := bstep (se 2 (by rfl) ⟨748851, by rfl⟩ : syracuseStep 1996937 = 1497703) B1497703
theorem B1997039 : Blo 1330984 1997039 := bstep (se 1 (by rfl) ⟨1497779, by rfl⟩ : syracuseStep 1997039 = 2995559) B2995559
theorem B1997183 : Blo 1330984 1997183 := bstep (se 1 (by rfl) ⟨1497887, by rfl⟩ : syracuseStep 1997183 = 2995775) B2995775
theorem B5692351 : Blo 1330984 5692351 := bstep (se 1 (by rfl) ⟨4269263, by rfl⟩ : syracuseStep 5692351 = 8538527) B8538527
theorem B1998059 : Blo 1330984 1998059 := bstep (se 1 (by rfl) ⟨1498544, by rfl⟩ : syracuseStep 1998059 = 2997089) B2997089
theorem B6741305 : Blo 1330984 6741305 := bstep (se 2 (by rfl) ⟨2527989, by rfl⟩ : syracuseStep 6741305 = 5055979) B5055979
theorem B43220587 : Blo 1330984 43220587 := bstep (se 1 (by rfl) ⟨32415440, by rfl⟩ : syracuseStep 43220587 = 64830881) B64830881
theorem B15163199 : Blo 1330984 15163199 := bstep (se 1 (by rfl) ⟨11372399, by rfl⟩ : syracuseStep 15163199 = 22744799) B22744799
theorem B1499071 : Blo 1330984 1499071 := bstep (se 1 (by rfl) ⟨1124303, by rfl⟩ : syracuseStep 1499071 = 2248607) B2248607
theorem B79978529 : Blo 1330984 79978529 := bstep (se 2 (by rfl) ⟨29991948, by rfl⟩ : syracuseStep 79978529 = 59983897) B59983897
theorem B2998583 : Blo 1330984 2998583 := bstep (se 1 (by rfl) ⟨2248937, by rfl⟩ : syracuseStep 2998583 = 4497875) B4497875
theorem B10117547 : Blo 1330984 10117547 := bstep (se 1 (by rfl) ⟨7588160, by rfl⟩ : syracuseStep 10117547 = 15176321) B15176321
theorem B6399323 : Blo 1330984 6399323 := bstep (se 1 (by rfl) ⟨4799492, by rfl⟩ : syracuseStep 6399323 = 9598985) B9598985
theorem B2246825 : Blo 1330984 2246825 := bstep (se 2 (by rfl) ⟨842559, by rfl⟩ : syracuseStep 2246825 = 1685119) B1685119
theorem B6745193 : Blo 1330984 6745193 := bstep (se 2 (by rfl) ⟨2529447, by rfl⟩ : syracuseStep 6745193 = 5058895) B5058895
theorem B5058395 : Blo 1330984 5058395 := bstep (se 1 (by rfl) ⟨3793796, by rfl⟩ : syracuseStep 5058395 = 7587593) B7587593
theorem B7589801 : Blo 1330984 7589801 := bstep (se 2 (by rfl) ⟨2846175, by rfl⟩ : syracuseStep 7589801 = 5692351) B5692351
theorem B1331291 : Blo 1330984 1331291 := bstep (se 1 (by rfl) ⟨998468, by rfl⟩ : syracuseStep 1331291 = 1996937) B1996937
theorem B1331359 : Blo 1330984 1331359 := bstep (se 1 (by rfl) ⟨998519, by rfl⟩ : syracuseStep 1331359 = 1997039) B1997039
theorem B1331455 : Blo 1330984 1331455 := bstep (se 1 (by rfl) ⟨998591, by rfl⟩ : syracuseStep 1331455 = 1997183) B1997183
theorem B6746651 : Blo 1330984 6746651 := bstep (se 1 (by rfl) ⟨5059988, by rfl⟩ : syracuseStep 6746651 = 10119977) B10119977
theorem B57627449 : Blo 1330984 57627449 := bstep (se 2 (by rfl) ⟨21610293, by rfl⟩ : syracuseStep 57627449 = 43220587) B43220587
theorem B1332039 : Blo 1330984 1332039 := bstep (se 1 (by rfl) ⟨999029, by rfl⟩ : syracuseStep 1332039 = 1998059) B1998059
theorem B4494203 : Blo 1330984 4494203 := bstep (se 1 (by rfl) ⟨3370652, by rfl⟩ : syracuseStep 4494203 = 6741305) B6741305
theorem B1996583 : Blo 1330984 1996583 := bstep (se 1 (by rfl) ⟨1497437, by rfl⟩ : syracuseStep 1996583 = 2994875) B2994875
theorem B2529235 : Blo 1330984 2529235 := bstep (se 1 (by rfl) ⟨1896926, by rfl⟩ : syracuseStep 2529235 = 3793853) B3793853
theorem B8534119 : Blo 1330984 8534119 := bstep (se 1 (by rfl) ⟨6400589, by rfl⟩ : syracuseStep 8534119 = 12801179) B12801179
theorem B622966949 : Blo 1330984 622966949 := bstep (se 4 (by rfl) ⟨58403151, by rfl⟩ : syracuseStep 622966949 = 116806303) B116806303
theorem B2996927 : Blo 1330984 2996927 := bstep (se 1 (by rfl) ⟨2247695, by rfl⟩ : syracuseStep 2996927 = 4495391) B4495391
theorem B10116089 : Blo 1330984 10116089 := bstep (se 2 (by rfl) ⟨3793533, by rfl⟩ : syracuseStep 10116089 = 7587067) B7587067
theorem B1498351 : Blo 1330984 1498351 := bstep (se 1 (by rfl) ⟨1123763, by rfl⟩ : syracuseStep 1498351 = 2247527) B2247527
theorem B10108799 : Blo 1330984 10108799 := bstep (se 1 (by rfl) ⟨7581599, by rfl⟩ : syracuseStep 10108799 = 15163199) B15163199
theorem B1998761 : Blo 1330984 1998761 := bstep (se 2 (by rfl) ⟨749535, by rfl⟩ : syracuseStep 1998761 = 1499071) B1499071
theorem B11378825 : Blo 1330984 11378825 := bstep (se 2 (by rfl) ⟨4267059, by rfl⟩ : syracuseStep 11378825 = 8534119) B8534119
theorem B1999055 : Blo 1330984 1999055 := bstep (se 1 (by rfl) ⟨1499291, by rfl⟩ : syracuseStep 1999055 = 2998583) B2998583
theorem B4497767 : Blo 1330984 4497767 := bstep (se 1 (by rfl) ⟨3373325, by rfl⟩ : syracuseStep 4497767 = 6746651) B6746651
theorem B415311299 : Blo 1330984 415311299 := bstep (se 1 (by rfl) ⟨311483474, by rfl⟩ : syracuseStep 415311299 = 622966949) B622966949
theorem B6744059 : Blo 1330984 6744059 := bstep (se 1 (by rfl) ⟨5058044, by rfl⟩ : syracuseStep 6744059 = 10116089) B10116089
theorem B6745031 : Blo 1330984 6745031 := bstep (se 1 (by rfl) ⟨5058773, by rfl⟩ : syracuseStep 6745031 = 10117547) B10117547
theorem B1331055 : Blo 1330984 1331055 := bstep (se 1 (by rfl) ⟨998291, by rfl⟩ : syracuseStep 1331055 = 1996583) B1996583
theorem B3372263 : Blo 1330984 3372263 := bstep (se 1 (by rfl) ⟨2529197, by rfl⟩ : syracuseStep 3372263 = 5058395) B5058395
theorem B6739199 : Blo 1330984 6739199 := bstep (se 1 (by rfl) ⟨5054399, by rfl⟩ : syracuseStep 6739199 = 10108799) B10108799
theorem B3372313 : Blo 1330984 3372313 := bstep (se 2 (by rfl) ⟨1264617, by rfl⟩ : syracuseStep 3372313 = 2529235) B2529235
theorem B1332507 : Blo 1330984 1332507 := bstep (se 1 (by rfl) ⟨999380, by rfl⟩ : syracuseStep 1332507 = 1998761) B1998761
theorem B5059867 : Blo 1330984 5059867 := bstep (se 1 (by rfl) ⟨3794900, by rfl⟩ : syracuseStep 5059867 = 7589801) B7589801
theorem B53319019 : Blo 1330984 53319019 := bstep (se 1 (by rfl) ⟨39989264, by rfl⟩ : syracuseStep 53319019 = 79978529) B79978529
theorem B38418299 : Blo 1330984 38418299 := bstep (se 1 (by rfl) ⟨28813724, by rfl⟩ : syracuseStep 38418299 = 57627449) B57627449
theorem B2996135 : Blo 1330984 2996135 := bstep (se 1 (by rfl) ⟨2247101, by rfl⟩ : syracuseStep 2996135 = 4494203) B4494203
theorem B4266215 : Blo 1330984 4266215 := bstep (se 1 (by rfl) ⟨3199661, by rfl⟩ : syracuseStep 4266215 = 6399323) B6399323
theorem B1497883 : Blo 1330984 1497883 := bstep (se 1 (by rfl) ⟨1123412, by rfl⟩ : syracuseStep 1497883 = 2246825) B2246825
theorem B1997801 : Blo 1330984 1997801 := bstep (se 2 (by rfl) ⟨749175, by rfl⟩ : syracuseStep 1997801 = 1498351) B1498351
theorem B1997951 : Blo 1330984 1997951 := bstep (se 1 (by rfl) ⟨1498463, by rfl⟩ : syracuseStep 1997951 = 2996927) B2996927
theorem B4496795 : Blo 1330984 4496795 := bstep (se 1 (by rfl) ⟨3372596, by rfl⟩ : syracuseStep 4496795 = 6745193) B6745193
theorem B7585883 : Blo 1330984 7585883 := bstep (se 1 (by rfl) ⟨5689412, by rfl⟩ : syracuseStep 7585883 = 11378825) B11378825
theorem B2998511 : Blo 1330984 2998511 := bstep (se 1 (by rfl) ⟨2248883, by rfl⟩ : syracuseStep 2998511 = 4497767) B4497767
theorem B276874199 : Blo 1330984 276874199 := bstep (se 1 (by rfl) ⟨207655649, by rfl⟩ : syracuseStep 276874199 = 415311299) B415311299
theorem B2844143 : Blo 1330984 2844143 := bstep (se 1 (by rfl) ⟨2133107, by rfl⟩ : syracuseStep 2844143 = 4266215) B4266215
theorem B71092025 : Blo 1330984 71092025 := bstep (se 2 (by rfl) ⟨26659509, by rfl⟩ : syracuseStep 71092025 = 53319019) B53319019
theorem B2248175 : Blo 1330984 2248175 := bstep (se 1 (by rfl) ⟨1686131, by rfl⟩ : syracuseStep 2248175 = 3372263) B3372263
theorem B4492799 : Blo 1330984 4492799 := bstep (se 1 (by rfl) ⟨3369599, by rfl⟩ : syracuseStep 4492799 = 6739199) B6739199
theorem B25612199 : Blo 1330984 25612199 := bstep (se 1 (by rfl) ⟨19209149, by rfl⟩ : syracuseStep 25612199 = 38418299) B38418299
theorem B6746489 : Blo 1330984 6746489 := bstep (se 2 (by rfl) ⟨2529933, by rfl⟩ : syracuseStep 6746489 = 5059867) B5059867
theorem B1331867 : Blo 1330984 1331867 := bstep (se 1 (by rfl) ⟨998900, by rfl⟩ : syracuseStep 1331867 = 1997801) B1997801
theorem B1331967 : Blo 1330984 1331967 := bstep (se 1 (by rfl) ⟨998975, by rfl⟩ : syracuseStep 1331967 = 1997951) B1997951
theorem B1332703 : Blo 1330984 1332703 := bstep (se 1 (by rfl) ⟨999527, by rfl⟩ : syracuseStep 1332703 = 1999055) B1999055
theorem B1997177 : Blo 1330984 1997177 := bstep (se 2 (by rfl) ⟨748941, by rfl⟩ : syracuseStep 1997177 = 1497883) B1497883
theorem B1997423 : Blo 1330984 1997423 := bstep (se 1 (by rfl) ⟨1498067, by rfl⟩ : syracuseStep 1997423 = 2996135) B2996135
theorem B4496039 : Blo 1330984 4496039 := bstep (se 1 (by rfl) ⟨3372029, by rfl⟩ : syracuseStep 4496039 = 6744059) B6744059
theorem B4496417 : Blo 1330984 4496417 := bstep (se 2 (by rfl) ⟨1686156, by rfl⟩ : syracuseStep 4496417 = 3372313) B3372313
theorem B4496687 : Blo 1330984 4496687 := bstep (se 1 (by rfl) ⟨3372515, by rfl⟩ : syracuseStep 4496687 = 6745031) B6745031
theorem B2997863 : Blo 1330984 2997863 := bstep (se 1 (by rfl) ⟨2248397, by rfl⟩ : syracuseStep 2997863 = 4496795) B4496795
theorem B1999007 : Blo 1330984 1999007 := bstep (se 1 (by rfl) ⟨1499255, by rfl⟩ : syracuseStep 1999007 = 2998511) B2998511
theorem B4497659 : Blo 1330984 4497659 := bstep (se 1 (by rfl) ⟨3373244, by rfl⟩ : syracuseStep 4497659 = 6746489) B6746489
theorem B184582799 : Blo 1330984 184582799 := bstep (se 1 (by rfl) ⟨138437099, by rfl⟩ : syracuseStep 184582799 = 276874199) B276874199
theorem B17074799 : Blo 1330984 17074799 := bstep (se 1 (by rfl) ⟨12806099, by rfl⟩ : syracuseStep 17074799 = 25612199) B25612199
theorem B5057255 : Blo 1330984 5057255 := bstep (se 1 (by rfl) ⟨3792941, by rfl⟩ : syracuseStep 5057255 = 7585883) B7585883
theorem B1896095 : Blo 1330984 1896095 := bstep (se 1 (by rfl) ⟨1422071, by rfl⟩ : syracuseStep 1896095 = 2844143) B2844143
theorem B47394683 : Blo 1330984 47394683 := bstep (se 1 (by rfl) ⟨35546012, by rfl⟩ : syracuseStep 47394683 = 71092025) B71092025
theorem B1331451 : Blo 1330984 1331451 := bstep (se 1 (by rfl) ⟨998588, by rfl⟩ : syracuseStep 1331451 = 1997177) B1997177
theorem B1331615 : Blo 1330984 1331615 := bstep (se 1 (by rfl) ⟨998711, by rfl⟩ : syracuseStep 1331615 = 1997423) B1997423
theorem B2995199 : Blo 1330984 2995199 := bstep (se 1 (by rfl) ⟨2246399, by rfl⟩ : syracuseStep 2995199 = 4492799) B4492799
theorem B2997359 : Blo 1330984 2997359 := bstep (se 1 (by rfl) ⟨2248019, by rfl⟩ : syracuseStep 2997359 = 4496039) B4496039
theorem B2997611 : Blo 1330984 2997611 := bstep (se 1 (by rfl) ⟨2248208, by rfl⟩ : syracuseStep 2997611 = 4496417) B4496417
theorem B2997791 : Blo 1330984 2997791 := bstep (se 1 (by rfl) ⟨2248343, by rfl⟩ : syracuseStep 2997791 = 4496687) B4496687
theorem B1498783 : Blo 1330984 1498783 := bstep (se 1 (by rfl) ⟨1124087, by rfl⟩ : syracuseStep 1498783 = 2248175) B2248175
theorem B1998575 : Blo 1330984 1998575 := bstep (se 1 (by rfl) ⟨1498931, by rfl⟩ : syracuseStep 1998575 = 2997863) B2997863
theorem B2998439 : Blo 1330984 2998439 := bstep (se 1 (by rfl) ⟨2248829, by rfl⟩ : syracuseStep 2998439 = 4497659) B4497659
theorem B5056253 : Blo 1330984 5056253 := bstep (se 3 (by rfl) ⟨948047, by rfl⟩ : syracuseStep 5056253 = 1896095) B1896095
theorem B123055199 : Blo 1330984 123055199 := bstep (se 1 (by rfl) ⟨92291399, by rfl⟩ : syracuseStep 123055199 = 184582799) B184582799
theorem B11383199 : Blo 1330984 11383199 := bstep (se 1 (by rfl) ⟨8537399, by rfl⟩ : syracuseStep 11383199 = 17074799) B17074799
theorem B3371503 : Blo 1330984 3371503 := bstep (se 1 (by rfl) ⟨2528627, by rfl⟩ : syracuseStep 3371503 = 5057255) B5057255
theorem B1332383 : Blo 1330984 1332383 := bstep (se 1 (by rfl) ⟨999287, by rfl⟩ : syracuseStep 1332383 = 1998575) B1998575
theorem B1332671 : Blo 1330984 1332671 := bstep (se 1 (by rfl) ⟨999503, by rfl⟩ : syracuseStep 1332671 = 1999007) B1999007
theorem B1996799 : Blo 1330984 1996799 := bstep (se 1 (by rfl) ⟨1497599, by rfl⟩ : syracuseStep 1996799 = 2995199) B2995199
theorem B1998239 : Blo 1330984 1998239 := bstep (se 1 (by rfl) ⟨1498679, by rfl⟩ : syracuseStep 1998239 = 2997359) B2997359
theorem B1998377 : Blo 1330984 1998377 := bstep (se 2 (by rfl) ⟨749391, by rfl⟩ : syracuseStep 1998377 = 1498783) B1498783
theorem B1998407 : Blo 1330984 1998407 := bstep (se 1 (by rfl) ⟨1498805, by rfl⟩ : syracuseStep 1998407 = 2997611) B2997611
theorem B1998527 : Blo 1330984 1998527 := bstep (se 1 (by rfl) ⟨1498895, by rfl⟩ : syracuseStep 1998527 = 2997791) B2997791
theorem B31596455 : Blo 1330984 31596455 := bstep (se 1 (by rfl) ⟨23697341, by rfl⟩ : syracuseStep 31596455 = 47394683) B47394683
theorem B1998959 : Blo 1330984 1998959 := bstep (se 1 (by rfl) ⟨1499219, by rfl⟩ : syracuseStep 1998959 = 2998439) B2998439
theorem B82036799 : Blo 1330984 82036799 := bstep (se 1 (by rfl) ⟨61527599, by rfl⟩ : syracuseStep 82036799 = 123055199) B123055199
theorem B21064303 : Blo 1330984 21064303 := bstep (se 1 (by rfl) ⟨15798227, by rfl⟩ : syracuseStep 21064303 = 31596455) B31596455
theorem B7588799 : Blo 1330984 7588799 := bstep (se 1 (by rfl) ⟨5691599, by rfl⟩ : syracuseStep 7588799 = 11383199) B11383199
theorem B3370835 : Blo 1330984 3370835 := bstep (se 1 (by rfl) ⟨2528126, by rfl⟩ : syracuseStep 3370835 = 5056253) B5056253
theorem B1331199 : Blo 1330984 1331199 := bstep (se 1 (by rfl) ⟨998399, by rfl⟩ : syracuseStep 1331199 = 1996799) B1996799
theorem B1332159 : Blo 1330984 1332159 := bstep (se 1 (by rfl) ⟨999119, by rfl⟩ : syracuseStep 1332159 = 1998239) B1998239
theorem B1332251 : Blo 1330984 1332251 := bstep (se 1 (by rfl) ⟨999188, by rfl⟩ : syracuseStep 1332251 = 1998377) B1998377
theorem B1332271 : Blo 1330984 1332271 := bstep (se 1 (by rfl) ⟨999203, by rfl⟩ : syracuseStep 1332271 = 1998407) B1998407
theorem B1332351 : Blo 1330984 1332351 := bstep (se 1 (by rfl) ⟨999263, by rfl⟩ : syracuseStep 1332351 = 1998527) B1998527
theorem B4495337 : Blo 1330984 4495337 := bstep (se 2 (by rfl) ⟨1685751, by rfl⟩ : syracuseStep 4495337 = 3371503) B3371503
theorem B54691199 : Blo 1330984 54691199 := bstep (se 1 (by rfl) ⟨41018399, by rfl⟩ : syracuseStep 54691199 = 82036799) B82036799
theorem B2247223 : Blo 1330984 2247223 := bstep (se 1 (by rfl) ⟨1685417, by rfl⟩ : syracuseStep 2247223 = 3370835) B3370835
theorem B28085737 : Blo 1330984 28085737 := bstep (se 2 (by rfl) ⟨10532151, by rfl⟩ : syracuseStep 28085737 = 21064303) B21064303
theorem B5059199 : Blo 1330984 5059199 := bstep (se 1 (by rfl) ⟨3794399, by rfl⟩ : syracuseStep 5059199 = 7588799) B7588799
theorem B1332639 : Blo 1330984 1332639 := bstep (se 1 (by rfl) ⟨999479, by rfl⟩ : syracuseStep 1332639 = 1998959) B1998959
theorem B2996891 : Blo 1330984 2996891 := bstep (se 1 (by rfl) ⟨2247668, by rfl⟩ : syracuseStep 2996891 = 4495337) B4495337
theorem B37447649 : Blo 1330984 37447649 := bstep (se 2 (by rfl) ⟨14042868, by rfl⟩ : syracuseStep 37447649 = 28085737) B28085737
theorem B3372799 : Blo 1330984 3372799 := bstep (se 1 (by rfl) ⟨2529599, by rfl⟩ : syracuseStep 3372799 = 5059199) B5059199
theorem B2996297 : Blo 1330984 2996297 := bstep (se 2 (by rfl) ⟨1123611, by rfl⟩ : syracuseStep 2996297 = 2247223) B2247223
theorem B36460799 : Blo 1330984 36460799 := bstep (se 1 (by rfl) ⟨27345599, by rfl⟩ : syracuseStep 36460799 = 54691199) B54691199
theorem B1997927 : Blo 1330984 1997927 := bstep (se 1 (by rfl) ⟨1498445, by rfl⟩ : syracuseStep 1997927 = 2996891) B2996891
theorem B24307199 : Blo 1330984 24307199 := bstep (se 1 (by rfl) ⟨18230399, by rfl⟩ : syracuseStep 24307199 = 36460799) B36460799
theorem B24965099 : Blo 1330984 24965099 := bstep (se 1 (by rfl) ⟨18723824, by rfl⟩ : syracuseStep 24965099 = 37447649) B37447649
theorem B1331951 : Blo 1330984 1331951 := bstep (se 1 (by rfl) ⟨998963, by rfl⟩ : syracuseStep 1331951 = 1997927) B1997927
theorem B1997531 : Blo 1330984 1997531 := bstep (se 1 (by rfl) ⟨1498148, by rfl⟩ : syracuseStep 1997531 = 2996297) B2996297
theorem B4497065 : Blo 1330984 4497065 := bstep (se 2 (by rfl) ⟨1686399, by rfl⟩ : syracuseStep 4497065 = 3372799) B3372799
theorem B16204799 : Blo 1330984 16204799 := bstep (se 1 (by rfl) ⟨12153599, by rfl⟩ : syracuseStep 16204799 = 24307199) B24307199
theorem B1331687 : Blo 1330984 1331687 := bstep (se 1 (by rfl) ⟨998765, by rfl⟩ : syracuseStep 1331687 = 1997531) B1997531
theorem B16643399 : Blo 1330984 16643399 := bstep (se 1 (by rfl) ⟨12482549, by rfl⟩ : syracuseStep 16643399 = 24965099) B24965099
theorem B2998043 : Blo 1330984 2998043 := bstep (se 1 (by rfl) ⟨2248532, by rfl⟩ : syracuseStep 2998043 = 4497065) B4497065
theorem B177529589 : Blo 1330984 177529589 := bstep (se 5 (by rfl) ⟨8321699, by rfl⟩ : syracuseStep 177529589 = 16643399) B16643399
theorem B1998695 : Blo 1330984 1998695 := bstep (se 1 (by rfl) ⟨1499021, by rfl⟩ : syracuseStep 1998695 = 2998043) B2998043
theorem B43212797 : Blo 1330984 43212797 := bstep (se 3 (by rfl) ⟨8102399, by rfl⟩ : syracuseStep 43212797 = 16204799) B16204799
theorem B118353059 : Blo 1330984 118353059 := bstep (se 1 (by rfl) ⟨88764794, by rfl⟩ : syracuseStep 118353059 = 177529589) B177529589
theorem B1332463 : Blo 1330984 1332463 := bstep (se 1 (by rfl) ⟨999347, by rfl⟩ : syracuseStep 1332463 = 1998695) B1998695
theorem B28808531 : Blo 1330984 28808531 := bstep (se 1 (by rfl) ⟨21606398, by rfl⟩ : syracuseStep 28808531 = 43212797) B43212797
theorem B19205687 : Blo 1330984 19205687 := bstep (se 1 (by rfl) ⟨14404265, by rfl⟩ : syracuseStep 19205687 = 28808531) B28808531
theorem B78902039 : Blo 1330984 78902039 := bstep (se 1 (by rfl) ⟨59176529, by rfl⟩ : syracuseStep 78902039 = 118353059) B118353059
theorem B52601359 : Blo 1330984 52601359 := bstep (se 1 (by rfl) ⟨39451019, by rfl⟩ : syracuseStep 52601359 = 78902039) B78902039
theorem B51215165 : Blo 1330984 51215165 := bstep (se 3 (by rfl) ⟨9602843, by rfl⟩ : syracuseStep 51215165 = 19205687) B19205687
theorem B70135145 : Blo 1330984 70135145 := bstep (se 2 (by rfl) ⟨26300679, by rfl⟩ : syracuseStep 70135145 = 52601359) B52601359
theorem B34143443 : Blo 1330984 34143443 := bstep (se 1 (by rfl) ⟨25607582, by rfl⟩ : syracuseStep 34143443 = 51215165) B51215165
theorem B22762295 : Blo 1330984 22762295 := bstep (se 1 (by rfl) ⟨17071721, by rfl⟩ : syracuseStep 22762295 = 34143443) B34143443
theorem B46756763 : Blo 1330984 46756763 := bstep (se 1 (by rfl) ⟨35067572, by rfl⟩ : syracuseStep 46756763 = 70135145) B70135145
theorem B31171175 : Blo 1330984 31171175 := bstep (se 1 (by rfl) ⟨23378381, by rfl⟩ : syracuseStep 31171175 = 46756763) B46756763
theorem B15174863 : Blo 1330984 15174863 := bstep (se 1 (by rfl) ⟨11381147, by rfl⟩ : syracuseStep 15174863 = 22762295) B22762295
theorem B20780783 : Blo 1330984 20780783 := bstep (se 1 (by rfl) ⟨15585587, by rfl⟩ : syracuseStep 20780783 = 31171175) B31171175
theorem B10116575 : Blo 1330984 10116575 := bstep (se 1 (by rfl) ⟨7587431, by rfl⟩ : syracuseStep 10116575 = 15174863) B15174863
theorem B13853855 : Blo 1330984 13853855 := bstep (se 1 (by rfl) ⟨10390391, by rfl⟩ : syracuseStep 13853855 = 20780783) B20780783
theorem B6744383 : Blo 1330984 6744383 := bstep (se 1 (by rfl) ⟨5058287, by rfl⟩ : syracuseStep 6744383 = 10116575) B10116575
theorem B9235903 : Blo 1330984 9235903 := bstep (se 1 (by rfl) ⟨6926927, by rfl⟩ : syracuseStep 9235903 = 13853855) B13853855
theorem B4496255 : Blo 1330984 4496255 := bstep (se 1 (by rfl) ⟨3372191, by rfl⟩ : syracuseStep 4496255 = 6744383) B6744383
theorem B12314537 : Blo 1330984 12314537 := bstep (se 2 (by rfl) ⟨4617951, by rfl⟩ : syracuseStep 12314537 = 9235903) B9235903
theorem B2997503 : Blo 1330984 2997503 := bstep (se 1 (by rfl) ⟨2248127, by rfl⟩ : syracuseStep 2997503 = 4496255) B4496255
theorem B8209691 : Blo 1330984 8209691 := bstep (se 1 (by rfl) ⟨6157268, by rfl⟩ : syracuseStep 8209691 = 12314537) B12314537
theorem B1998335 : Blo 1330984 1998335 := bstep (se 1 (by rfl) ⟨1498751, by rfl⟩ : syracuseStep 1998335 = 2997503) B2997503
theorem B5473127 : Blo 1330984 5473127 := bstep (se 1 (by rfl) ⟨4104845, by rfl⟩ : syracuseStep 5473127 = 8209691) B8209691
theorem B1332223 : Blo 1330984 1332223 := bstep (se 1 (by rfl) ⟨999167, by rfl⟩ : syracuseStep 1332223 = 1998335) B1998335
theorem B14595005 : Blo 1330984 14595005 := bstep (se 3 (by rfl) ⟨2736563, by rfl⟩ : syracuseStep 14595005 = 5473127) B5473127
theorem B38920013 : Blo 1330984 38920013 := bstep (se 3 (by rfl) ⟨7297502, by rfl⟩ : syracuseStep 38920013 = 14595005) B14595005
theorem B25946675 : Blo 1330984 25946675 := bstep (se 1 (by rfl) ⟨19460006, by rfl⟩ : syracuseStep 25946675 = 38920013) B38920013
theorem B17297783 : Blo 1330984 17297783 := bstep (se 1 (by rfl) ⟨12973337, by rfl⟩ : syracuseStep 17297783 = 25946675) B25946675
theorem B11531855 : Blo 1330984 11531855 := bstep (se 1 (by rfl) ⟨8648891, by rfl⟩ : syracuseStep 11531855 = 17297783) B17297783
theorem B7687903 : Blo 1330984 7687903 := bstep (se 1 (by rfl) ⟨5765927, by rfl⟩ : syracuseStep 7687903 = 11531855) B11531855
theorem B164008597 : Blo 1330984 164008597 := bstep (se 6 (by rfl) ⟨3843951, by rfl⟩ : syracuseStep 164008597 = 7687903) B7687903
theorem B218678129 : Blo 1330984 218678129 := bstep (se 2 (by rfl) ⟨82004298, by rfl⟩ : syracuseStep 218678129 = 164008597) B164008597
theorem B145785419 : Blo 1330984 145785419 := bstep (se 1 (by rfl) ⟨109339064, by rfl⟩ : syracuseStep 145785419 = 218678129) B218678129
theorem B97190279 : Blo 1330984 97190279 := bstep (se 1 (by rfl) ⟨72892709, by rfl⟩ : syracuseStep 97190279 = 145785419) B145785419
theorem B64793519 : Blo 1330984 64793519 := bstep (se 1 (by rfl) ⟨48595139, by rfl⟩ : syracuseStep 64793519 = 97190279) B97190279
theorem B43195679 : Blo 1330984 43195679 := bstep (se 1 (by rfl) ⟨32396759, by rfl⟩ : syracuseStep 43195679 = 64793519) B64793519
theorem B28797119 : Blo 1330984 28797119 := bstep (se 1 (by rfl) ⟨21597839, by rfl⟩ : syracuseStep 28797119 = 43195679) B43195679
theorem B19198079 : Blo 1330984 19198079 := bstep (se 1 (by rfl) ⟨14398559, by rfl⟩ : syracuseStep 19198079 = 28797119) B28797119
theorem B12798719 : Blo 1330984 12798719 := bstep (se 1 (by rfl) ⟨9599039, by rfl⟩ : syracuseStep 12798719 = 19198079) B19198079
theorem B8532479 : Blo 1330984 8532479 := bstep (se 1 (by rfl) ⟨6399359, by rfl⟩ : syracuseStep 8532479 = 12798719) B12798719
theorem B5688319 : Blo 1330984 5688319 := bstep (se 1 (by rfl) ⟨4266239, by rfl⟩ : syracuseStep 5688319 = 8532479) B8532479
theorem B7584425 : Blo 1330984 7584425 := bstep (se 2 (by rfl) ⟨2844159, by rfl⟩ : syracuseStep 7584425 = 5688319) B5688319
theorem B5056283 : Blo 1330984 5056283 := bstep (se 1 (by rfl) ⟨3792212, by rfl⟩ : syracuseStep 5056283 = 7584425) B7584425
theorem B3370855 : Blo 1330984 3370855 := bstep (se 1 (by rfl) ⟨2528141, by rfl⟩ : syracuseStep 3370855 = 5056283) B5056283
theorem B4494473 : Blo 1330984 4494473 := bstep (se 2 (by rfl) ⟨1685427, by rfl⟩ : syracuseStep 4494473 = 3370855) B3370855
theorem B2996315 : Blo 1330984 2996315 := bstep (se 1 (by rfl) ⟨2247236, by rfl⟩ : syracuseStep 2996315 = 4494473) B4494473
theorem B1997543 : Blo 1330984 1997543 := bstep (se 1 (by rfl) ⟨1498157, by rfl⟩ : syracuseStep 1997543 = 2996315) B2996315
theorem B1331695 : Blo 1330984 1331695 := bstep (se 1 (by rfl) ⟨998771, by rfl⟩ : syracuseStep 1331695 = 1997543) B1997543

theorem C0 (j : ℕ) (h1 : 332746 ≤ j) (h2 : j ≤ 333245) : Blo 1330984 (4 * j + 3) := by
  interval_cases j
  · exact B1330987
  · exact B1330991
  · exact B1330995
  · exact B1330999
  · exact B1331003
  · exact B1331007
  · exact B1331011
  · exact B1331015
  · exact B1331019
  · exact B1331023
  · exact B1331027
  · exact B1331031
  · exact B1331035
  · exact B1331039
  · exact B1331043
  · exact B1331047
  · exact B1331051
  · exact B1331055
  · exact B1331059
  · exact B1331063
  · exact B1331067
  · exact B1331071
  · exact B1331075
  · exact B1331079
  · exact B1331083
  · exact B1331087
  · exact B1331091
  · exact B1331095
  · exact B1331099
  · exact B1331103
  · exact B1331107
  · exact B1331111
  · exact B1331115
  · exact B1331119
  · exact B1331123
  · exact B1331127
  · exact B1331131
  · exact B1331135
  · exact B1331139
  · exact B1331143
  · exact B1331147
  · exact B1331151
  · exact B1331155
  · exact B1331159
  · exact B1331163
  · exact B1331167
  · exact B1331171
  · exact B1331175
  · exact B1331179
  · exact B1331183
  · exact B1331187
  · exact B1331191
  · exact B1331195
  · exact B1331199
  · exact B1331203
  · exact B1331207
  · exact B1331211
  · exact B1331215
  · exact B1331219
  · exact B1331223
  · exact B1331227
  · exact B1331231
  · exact B1331235
  · exact B1331239
  · exact B1331243
  · exact B1331247
  · exact B1331251
  · exact B1331255
  · exact B1331259
  · exact B1331263
  · exact B1331267
  · exact B1331271
  · exact B1331275
  · exact B1331279
  · exact B1331283
  · exact B1331287
  · exact B1331291
  · exact B1331295
  · exact B1331299
  · exact B1331303
  · exact B1331307
  · exact B1331311
  · exact B1331315
  · exact B1331319
  · exact B1331323
  · exact B1331327
  · exact B1331331
  · exact B1331335
  · exact B1331339
  · exact B1331343
  · exact B1331347
  · exact B1331351
  · exact B1331355
  · exact B1331359
  · exact B1331363
  · exact B1331367
  · exact B1331371
  · exact B1331375
  · exact B1331379
  · exact B1331383
  · exact B1331387
  · exact B1331391
  · exact B1331395
  · exact B1331399
  · exact B1331403
  · exact B1331407
  · exact B1331411
  · exact B1331415
  · exact B1331419
  · exact B1331423
  · exact B1331427
  · exact B1331431
  · exact B1331435
  · exact B1331439
  · exact B1331443
  · exact B1331447
  · exact B1331451
  · exact B1331455
  · exact B1331459
  · exact B1331463
  · exact B1331467
  · exact B1331471
  · exact B1331475
  · exact B1331479
  · exact B1331483
  · exact B1331487
  · exact B1331491
  · exact B1331495
  · exact B1331499
  · exact B1331503
  · exact B1331507
  · exact B1331511
  · exact B1331515
  · exact B1331519
  · exact B1331523
  · exact B1331527
  · exact B1331531
  · exact B1331535
  · exact B1331539
  · exact B1331543
  · exact B1331547
  · exact B1331551
  · exact B1331555
  · exact B1331559
  · exact B1331563
  · exact B1331567
  · exact B1331571
  · exact B1331575
  · exact B1331579
  · exact B1331583
  · exact B1331587
  · exact B1331591
  · exact B1331595
  · exact B1331599
  · exact B1331603
  · exact B1331607
  · exact B1331611
  · exact B1331615
  · exact B1331619
  · exact B1331623
  · exact B1331627
  · exact B1331631
  · exact B1331635
  · exact B1331639
  · exact B1331643
  · exact B1331647
  · exact B1331651
  · exact B1331655
  · exact B1331659
  · exact B1331663
  · exact B1331667
  · exact B1331671
  · exact B1331675
  · exact B1331679
  · exact B1331683
  · exact B1331687
  · exact B1331691
  · exact B1331695
  · exact B1331699
  · exact B1331703
  · exact B1331707
  · exact B1331711
  · exact B1331715
  · exact B1331719
  · exact B1331723
  · exact B1331727
  · exact B1331731
  · exact B1331735
  · exact B1331739
  · exact B1331743
  · exact B1331747
  · exact B1331751
  · exact B1331755
  · exact B1331759
  · exact B1331763
  · exact B1331767
  · exact B1331771
  · exact B1331775
  · exact B1331779
  · exact B1331783
  · exact B1331787
  · exact B1331791
  · exact B1331795
  · exact B1331799
  · exact B1331803
  · exact B1331807
  · exact B1331811
  · exact B1331815
  · exact B1331819
  · exact B1331823
  · exact B1331827
  · exact B1331831
  · exact B1331835
  · exact B1331839
  · exact B1331843
  · exact B1331847
  · exact B1331851
  · exact B1331855
  · exact B1331859
  · exact B1331863
  · exact B1331867
  · exact B1331871
  · exact B1331875
  · exact B1331879
  · exact B1331883
  · exact B1331887
  · exact B1331891
  · exact B1331895
  · exact B1331899
  · exact B1331903
  · exact B1331907
  · exact B1331911
  · exact B1331915
  · exact B1331919
  · exact B1331923
  · exact B1331927
  · exact B1331931
  · exact B1331935
  · exact B1331939
  · exact B1331943
  · exact B1331947
  · exact B1331951
  · exact B1331955
  · exact B1331959
  · exact B1331963
  · exact B1331967
  · exact B1331971
  · exact B1331975
  · exact B1331979
  · exact B1331983
  · exact B1331987
  · exact B1331991
  · exact B1331995
  · exact B1331999
  · exact B1332003
  · exact B1332007
  · exact B1332011
  · exact B1332015
  · exact B1332019
  · exact B1332023
  · exact B1332027
  · exact B1332031
  · exact B1332035
  · exact B1332039
  · exact B1332043
  · exact B1332047
  · exact B1332051
  · exact B1332055
  · exact B1332059
  · exact B1332063
  · exact B1332067
  · exact B1332071
  · exact B1332075
  · exact B1332079
  · exact B1332083
  · exact B1332087
  · exact B1332091
  · exact B1332095
  · exact B1332099
  · exact B1332103
  · exact B1332107
  · exact B1332111
  · exact B1332115
  · exact B1332119
  · exact B1332123
  · exact B1332127
  · exact B1332131
  · exact B1332135
  · exact B1332139
  · exact B1332143
  · exact B1332147
  · exact B1332151
  · exact B1332155
  · exact B1332159
  · exact B1332163
  · exact B1332167
  · exact B1332171
  · exact B1332175
  · exact B1332179
  · exact B1332183
  · exact B1332187
  · exact B1332191
  · exact B1332195
  · exact B1332199
  · exact B1332203
  · exact B1332207
  · exact B1332211
  · exact B1332215
  · exact B1332219
  · exact B1332223
  · exact B1332227
  · exact B1332231
  · exact B1332235
  · exact B1332239
  · exact B1332243
  · exact B1332247
  · exact B1332251
  · exact B1332255
  · exact B1332259
  · exact B1332263
  · exact B1332267
  · exact B1332271
  · exact B1332275
  · exact B1332279
  · exact B1332283
  · exact B1332287
  · exact B1332291
  · exact B1332295
  · exact B1332299
  · exact B1332303
  · exact B1332307
  · exact B1332311
  · exact B1332315
  · exact B1332319
  · exact B1332323
  · exact B1332327
  · exact B1332331
  · exact B1332335
  · exact B1332339
  · exact B1332343
  · exact B1332347
  · exact B1332351
  · exact B1332355
  · exact B1332359
  · exact B1332363
  · exact B1332367
  · exact B1332371
  · exact B1332375
  · exact B1332379
  · exact B1332383
  · exact B1332387
  · exact B1332391
  · exact B1332395
  · exact B1332399
  · exact B1332403
  · exact B1332407
  · exact B1332411
  · exact B1332415
  · exact B1332419
  · exact B1332423
  · exact B1332427
  · exact B1332431
  · exact B1332435
  · exact B1332439
  · exact B1332443
  · exact B1332447
  · exact B1332451
  · exact B1332455
  · exact B1332459
  · exact B1332463
  · exact B1332467
  · exact B1332471
  · exact B1332475
  · exact B1332479
  · exact B1332483
  · exact B1332487
  · exact B1332491
  · exact B1332495
  · exact B1332499
  · exact B1332503
  · exact B1332507
  · exact B1332511
  · exact B1332515
  · exact B1332519
  · exact B1332523
  · exact B1332527
  · exact B1332531
  · exact B1332535
  · exact B1332539
  · exact B1332543
  · exact B1332547
  · exact B1332551
  · exact B1332555
  · exact B1332559
  · exact B1332563
  · exact B1332567
  · exact B1332571
  · exact B1332575
  · exact B1332579
  · exact B1332583
  · exact B1332587
  · exact B1332591
  · exact B1332595
  · exact B1332599
  · exact B1332603
  · exact B1332607
  · exact B1332611
  · exact B1332615
  · exact B1332619
  · exact B1332623
  · exact B1332627
  · exact B1332631
  · exact B1332635
  · exact B1332639
  · exact B1332643
  · exact B1332647
  · exact B1332651
  · exact B1332655
  · exact B1332659
  · exact B1332663
  · exact B1332667
  · exact B1332671
  · exact B1332675
  · exact B1332679
  · exact B1332683
  · exact B1332687
  · exact B1332691
  · exact B1332695
  · exact B1332699
  · exact B1332703
  · exact B1332707
  · exact B1332711
  · exact B1332715
  · exact B1332719
  · exact B1332723
  · exact B1332727
  · exact B1332731
  · exact B1332735
  · exact B1332739
  · exact B1332743
  · exact B1332747
  · exact B1332751
  · exact B1332755
  · exact B1332759
  · exact B1332763
  · exact B1332767
  · exact B1332771
  · exact B1332775
  · exact B1332779
  · exact B1332783
  · exact B1332787
  · exact B1332791
  · exact B1332795
  · exact B1332799
  · exact B1332803
  · exact B1332807
  · exact B1332811
  · exact B1332815
  · exact B1332819
  · exact B1332823
  · exact B1332827
  · exact B1332831
  · exact B1332835
  · exact B1332839
  · exact B1332843
  · exact B1332847
  · exact B1332851
  · exact B1332855
  · exact B1332859
  · exact B1332863
  · exact B1332867
  · exact B1332871
  · exact B1332875
  · exact B1332879
  · exact B1332883
  · exact B1332887
  · exact B1332891
  · exact B1332895
  · exact B1332899
  · exact B1332903
  · exact B1332907
  · exact B1332911
  · exact B1332915
  · exact B1332919
  · exact B1332923
  · exact B1332927
  · exact B1332931
  · exact B1332935
  · exact B1332939
  · exact B1332943
  · exact B1332947
  · exact B1332951
  · exact B1332955
  · exact B1332959
  · exact B1332963
  · exact B1332967
  · exact B1332971
  · exact B1332975
  · exact B1332979
  · exact B1332983

theorem solution (m : ℕ) (hlo : 1330984 ≤ m) (hhi : m ≤ 1332984) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 332746 ≤ j := by omega
    have hj2 : j ≤ 333245 := by omega
    have hb : Blo 1330984 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
